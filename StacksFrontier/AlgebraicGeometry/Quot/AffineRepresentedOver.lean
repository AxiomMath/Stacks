module

public import StacksFrontier.AlgebraicGeometry.Quot.AffineAlgebraicSpaceOverCofilteredLimit
public import StacksFrontier.AlgebraicGeometry.Quot.SpacePointsOverBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PresentationSizeBounds
public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPushforward

/-!
# Functors on the test schemes over a scheme represented by bounded affine schemes

Let `Z` be a scheme of the site.  A functor `R` on the test schemes over `Z` is *represented by an
affine scheme of size at most `κ`* when it is isomorphic to the universe lift of the functor of
points over `Z` of an affine object `W` of the site with a morphism `W ⟶ Z`, of size at most `κ`.
This file proves that the condition is stable under cofiltered limits and under passage to
subfunctors, with explicit bounds on the size of the representing scheme:

* a cofiltered limit, indexed by a category `I` with `#I` and `κ` below the cutoff of the site, of
  functors represented by affine schemes of size at most `κ` is represented by an affine scheme of
  size at most `max ℵ₀ (#I * κ)` (Stacks 01YW, Stacks 000P);
* a subfunctor of a functor represented by an affine scheme of size at most `κ`, which is itself
  an algebraic space affine over `Z`, is represented by an affine scheme of size at most
  `2 ^ 2 ^ κ` (the bound on the source of a monomorphism).

## References

* [Stacks Project, Tag 01YW](https://stacks.math.columbia.edu/tag/01YW)
* [Stacks Project, Tag 000P](https://stacks.math.columbia.edu/tag/000P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A functor on the test schemes over `Z` represented by an affine scheme of size at most
`κ`.** -/
def IsAffineRepresentedOver (Z : BigFppfOver B S hS) (κ : Cardinal.{u})
    (R : (SchemesOver ((schemeSpaceFunctor B S hS).obj Z))ᵒᵖ ⥤ Type (u + 1)) : Prop :=
  ∃ (W : BigFppfOver B S hS) (w : W ⟶ Z), IsAffine ((BigFppfOver.toScheme B S hS).obj W) ∧
    ((BigFppfOver.toScheme B S hS).obj W).size ≤ κ ∧
      Nonempty (spacePointsOver ((schemeSpaceFunctor B S hS).map w) ⋙ uliftFunctor.{u + 1, u} ≅ R)

namespace IsAffineRepresentedOver

variable {Z : BigFppfOver B S hS} {κ : Cardinal.{u}}
  {R R' : (SchemesOver ((schemeSpaceFunctor B S hS).obj Z))ᵒᵖ ⥤ Type (u + 1)}

/-- Being represented by an affine scheme of size at most `κ` is invariant under isomorphism of
functors. -/
theorem of_iso (e : R ≅ R') (h : IsAffineRepresentedOver Z κ R) :
    IsAffineRepresentedOver Z κ R' := by
  obtain ⟨W, w, hW, hs, ⟨ψ⟩⟩ := h
  exact ⟨W, w, hW, hs, ⟨ψ ≪≫ e⟩⟩

/-- A functor represented by an affine scheme of size at most `κ` is represented by an affine
scheme of size at most any `κ' ≥ κ`. -/
theorem mono {κ' : Cardinal.{u}} (hκ : κ ≤ κ') (h : IsAffineRepresentedOver Z κ R) :
    IsAffineRepresentedOver Z κ' R := by
  obtain ⟨W, w, hW, hs, hψ⟩ := h
  exact ⟨W, w, hW, hs.trans hκ, hψ⟩

/-- **An algebraic space affine and of finite presentation over an affine scheme `Z` is an affine
scheme of size at most that of `Z`** (Stacks 04T7). -/
theorem of_isAffineFinitePresentation (hZ : IsAffine ((BigFppfOver.toScheme B S hS).obj Z))
    (h : IsAffineFinitePresentationAlgebraicSpaceOver ((schemeSpaceFunctor B S hS).obj Z) R) :
    IsAffineRepresentedOver Z ((BigFppfOver.toScheme B S hS).obj Z).size R := by
  obtain ⟨W, w, hw, hwfp, ψ⟩ := h.exists_scheme
  have hW : IsAffine ((BigFppfOver.toScheme B S hS).obj W) :=
    isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map w)
  exact ⟨W, w, hW,
    Scheme.size_le_of_locallyOfFiniteType_of_quasiCompact ((BigFppfOver.toScheme B S hS).map w), ψ⟩

/-- A functor represented by an affine scheme over an affine scheme `Z` is an algebraic space
affine over `Z`. -/
theorem isAffineAlgebraicSpaceOver (hZ : IsAffine ((BigFppfOver.toScheme B S hS).obj Z))
    (h : IsAffineRepresentedOver Z κ R) :
    IsAffineAlgebraicSpaceOver ((schemeSpaceFunctor B S hS).obj Z) R := by
  obtain ⟨W, w, hW, -, hψ⟩ := h
  exact ⟨(schemeSpaceFunctor B S hS).obj W, (schemeSpaceFunctor B S hS).map w,
    isAffineHom_yoneda_map B S hS w, hψ⟩

end IsAffineRepresentedOver

/-! ### The functor of points of a limit -/

section LimitPoints

variable (Z : BigFppfOver B S hS) {I : Type u} [Category.{u} I] [IsConnected I]
  (V : I ⥤ BigFppfOver B S hS) (w : ∀ i, V.obj i ⟶ Z)
  (hw : ∀ {i j : I} (φ : i ⟶ j), V.map φ ≫ w j = w i)

/-- The structure morphisms of a system of schemes over `Z`, as a morphism of the represented
presheaves to the constant system at `Z`. -/
def systemStructure : V ⋙ yoneda ⟶ (Functor.const I).obj
    ((schemeSpaceFunctor B S hS).obj Z).1 where
  app i := yoneda.map (w i)
  naturality i j φ := by
    change yoneda.map (V.map φ) ≫ yoneda.map (w j) = yoneda.map (w i) ≫ 𝟙 _
    rw [← Functor.map_comp, hw, Category.comp_id]

variable {cV : Cone V} (hcV : IsLimit cV) (i₀ : I)

omit [IsConnected I] in
include hcV in
/-- The presheaf limit of the represented system is an algebraic space: it is represented by the
limit in the site. -/
theorem isAlgebraicSpace_limit_yoneda :
    IsAlgebraicSpace B S hS (limit (V ⋙ yoneda)) :=
  (isAlgebraicSpace_yoneda B S hS cV.pt).of_iso
    ((isLimitOfPreserves yoneda hcV).conePointUniqueUpToIso (limit.isLimit (V ⋙ yoneda)))

include hcV in
/-- **The points over `Z` of the limit of a system of schemes over `Z` are the limit of the
points.** -/
def limitPointsIso :
    spacePointsOver ((schemeSpaceFunctor B S hS).map (cV.π.app i₀ ≫ w i₀)) ≅
      spacePointsOver (limitStructureMorphism B S hS (V ⋙ yoneda) (systemStructure Z V w hw)
        (isAlgebraicSpace_limit_yoneda V hcV) i₀) :=
  spacePointsOverIsoOfIso
    (ObjectProperty.isoMk _
      ((isLimitOfPreserves yoneda hcV).conePointUniqueUpToIso (limit.isLimit (V ⋙ yoneda))))
    (ObjectProperty.hom_ext _ (by
      change ((isLimitOfPreserves yoneda hcV).conePointUniqueUpToIso
          (limit.isLimit (V ⋙ yoneda))).hom ≫ limit.π (V ⋙ yoneda) i₀ ≫ yoneda.map (w i₀) =
        yoneda.map (cV.π.app i₀ ≫ w i₀)
      have h₁ : ((isLimitOfPreserves yoneda hcV).conePointUniqueUpToIso
          (limit.isLimit (V ⋙ yoneda))).hom ≫ limit.π (V ⋙ yoneda) i₀ = yoneda.map (cV.π.app i₀) :=
        IsLimit.conePointUniqueUpToIso_hom_comp _ _ i₀
      rw [← Category.assoc, h₁, Functor.map_comp]))

end LimitPoints

/-! ### The system of representing schemes -/

section RepresentedSystem

variable (Z : BigFppfOver B S hS) {I : Type u} [Category.{u} I]
  (R : I ⥤ ((SchemesOver ((schemeSpaceFunctor B S hS).obj Z))ᵒᵖ ⥤ Type (u + 1)))
  (W : I → BigFppfOver B S hS) (w : ∀ i, W i ⟶ Z)
  (ψ : ∀ i, spacePointsOver ((schemeSpaceFunctor B S hS).map (w i)) ⋙ uliftFunctor.{u + 1, u} ≅
    R.obj i)

/-- The functor viewing a scheme of the site as an algebraic space is fully faithful. -/
def fullyFaithfulSchemeSpaceFunctor : (schemeSpaceFunctor B S hS).FullyFaithful where
  preimage f := yoneda.preimage f.hom
  map_preimage f := ObjectProperty.hom_ext _ (Functor.map_preimage yoneda f.hom)
  preimage_map f := yoneda.preimage_map f

/-- A functor to the algebraic spaces whose values are schemes, lifted to the schemes. -/
def liftToSchemes (F : I ⥤ AlgebraicSpaces B S hS)
    (e : ∀ i, (schemeSpaceFunctor B S hS).obj (W i) ≅ F.obj i) : I ⥤ BigFppfOver B S hS where
  obj := W
  map φ := fullyFaithfulSchemeSpaceFunctor.preimage ((e _).hom ≫ F.map φ ≫ (e _).inv)
  map_id i := fullyFaithfulSchemeSpaceFunctor.map_injective (by simp)
  map_comp φ φ' := fullyFaithfulSchemeSpaceFunctor.map_injective (by simp)

/-- The image of a transition morphism of `liftToSchemes W F e` as a morphism of algebraic spaces
is the transition morphism of `F` conjugated by `e`. -/
theorem schemeSpaceFunctor_map_liftToSchemes_map (F : I ⥤ AlgebraicSpaces B S hS)
    (e : ∀ i, (schemeSpaceFunctor B S hS).obj (W i) ≅ F.obj i) {i j : I} (φ : i ⟶ j) :
    (schemeSpaceFunctor B S hS).map ((liftToSchemes W F e).map φ) =
      (e _).hom ≫ F.map φ ≫ (e _).inv :=
  fullyFaithfulSchemeSpaceFunctor.map_preimage _

/-- **The system of representing schemes of a system of functors on the test schemes over `Z`,
each represented by a scheme over `Z`.** -/
def representedSystem : I ⥤ BigFppfOver B S hS :=
  liftToSchemes W (dataSystem R (fun i => (schemeSpaceFunctor B S hS).obj (W i))
    (fun i => (schemeSpaceFunctor B S hS).map (w i)) ψ) (fun _ => Iso.refl _)

/-- The value of `representedSystem Z R W w ψ` at `i` is `W i`. -/
@[simp]
theorem representedSystem_obj (i : I) : (representedSystem Z R W w ψ).obj i = W i := rfl

/-- The image of a transition morphism of `representedSystem Z R W w ψ` as a morphism of algebraic
spaces is the transition morphism `dataTransition` of the system `R`. -/
theorem schemeSpaceFunctor_map_representedSystem_map {i j : I} (φ : i ⟶ j) :
    (schemeSpaceFunctor B S hS).map ((representedSystem Z R W w ψ).map φ) =
      dataTransition R (fun i => (schemeSpaceFunctor B S hS).obj (W i))
        (fun i => (schemeSpaceFunctor B S hS).map (w i)) ψ φ :=
  (schemeSpaceFunctor_map_liftToSchemes_map W _ _ φ).trans
    ((Category.id_comp _).trans (Category.comp_id _))

/-- The transition morphisms of `representedSystem Z R W w ψ` commute with the structure morphisms
`w i` to `Z`. -/
theorem representedSystem_map_comp {i j : I} (φ : i ⟶ j) :
    (representedSystem Z R W w ψ).map φ ≫ w j = w i :=
  fullyFaithfulSchemeSpaceFunctor.map_injective (((schemeSpaceFunctor B S hS).map_comp _ _).trans
    ((congrArg (· ≫ (schemeSpaceFunctor B S hS).map (w j))
      (schemeSpaceFunctor_map_representedSystem_map Z R W w ψ φ)).trans
      (dataTransition_comp R _ _ ψ φ)))

/-- The system of functors of points over `Z` of the representing schemes is the given system. -/
def representedSystemPointsIso :
    spacePointsSystem B S hS (representedSystem Z R W w ψ ⋙ yoneda)
        (systemStructure Z (representedSystem Z R W w ψ) w
          (representedSystem_map_comp Z R W w ψ))
        (fun i => isAlgebraicSpace_yoneda B S hS (W i)) ⋙
      (Functor.whiskeringRight _ (Type u) (Type (u + 1))).obj uliftFunctor.{u + 1, u} ≅ R :=
  NatIso.ofComponents (fun i => ψ i) fun {i j} φ => by
    have h := whiskerRight_spacePointsOverMap_dataTransition R
      (fun i => (schemeSpaceFunctor B S hS).obj (W i))
      (fun i => (schemeSpaceFunctor B S hS).map (w i)) ψ φ
    refine Eq.trans ?_ h
    exact congrArg (fun k => Functor.whiskerRight k uliftFunctor.{u + 1, u} ≫ (ψ j).hom)
      (spacePointsOverMap_congr (systemTransition_comp_projection B S hS _ _ _ φ)
        (dataTransition_comp R _ _ ψ φ)
        (schemeSpaceFunctor_map_representedSystem_map Z R W w ψ φ))

variable [IsCofiltered I]

/-- **A limit of the system of representing schemes represents the limit of the system of
functors.** -/
theorem nonempty_limit_representation {cV : Cone (representedSystem Z R W w ψ)} (hcV : IsLimit cV)
    (c : Cone R) (hc : IsLimit c) (i₀ : I) :
    Nonempty (spacePointsOver ((schemeSpaceFunctor B S hS).map (cV.π.app i₀ ≫ w i₀)) ⋙
      uliftFunctor.{u + 1, u} ≅ c.pt) := by
  have : IsConnected I := IsCofiltered.isConnected I
  let V := representedSystem Z R W w ψ
  let D := V ⋙ yoneda
  let τ := systemStructure Z V w (representedSystem_map_comp Z R W w ψ)
  have hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i) := fun i => isAlgebraicSpace_yoneda B S hS (W i)
  have hlim := isAlgebraicSpace_limit_yoneda V hcV
  have h₁ := isLimitOfPreserves ((Functor.whiskeringRight _ (Type u) (Type (u + 1))).obj
    uliftFunctor.{u + 1, u}) (isLimit_spacePointsLimitCone B S hS D τ hD hlim i₀)
  have h₂ := (IsLimit.postcomposeHomEquiv (representedSystemPointsIso Z R W w ψ) _).symm h₁
  exact ⟨Functor.isoWhiskerRight (limitPointsIso Z V w (representedSystem_map_comp Z R W w ψ)
    hcV i₀) _ ≪≫ h₂.conePointUniqueUpToIso hc⟩

end RepresentedSystem

/-! ### Stability under limits -/

section Limits

variable {Z : BigFppfOver B S hS} {I : Type u} [Category.{u} I] [IsCofiltered I]
  (R : I ⥤ ((SchemesOver ((schemeSpaceFunctor B S hS).obj Z))ᵒᵖ ⥤ Type (u + 1)))

/-- **A cofiltered limit, over an index smaller than the cutoff, of functors represented by
affine schemes of size at most `κ < cutoff` is represented by an affine scheme of size at most
`max ℵ₀ (#I * κ)`.** -/
theorem IsAffineRepresentedOver.of_isLimit_of_bounded {κ : Cardinal.{u}}
    (h : ∀ i, IsAffineRepresentedOver Z κ (R.obj i)) (hI : max #I κ < B.cutoff) (c : Cone R)
    (hc : IsLimit c) : IsAffineRepresentedOver Z (max ℵ₀ (#I * κ)) c.pt := by
  choose W w hW hs ψ using h
  obtain ⟨ψ'⟩ : Nonempty (∀ i, spacePointsOver ((schemeSpaceFunctor B S hS).map (w i)) ⋙
      uliftFunctor.{u + 1, u} ≅ R.obj i) := ⟨fun i => (ψ i).some⟩
  have hI' : #I < B.cutoff := (le_max_left _ _).trans_lt hI
  have hκ : κ < B.cutoff := (le_max_right _ _).trans_lt hI
  have hs' : ∀ j, ((representedSystem Z R W w ψ' ⋙ BigFppfOver.toScheme B S hS).obj j).size ≤ κ :=
    fun j => by rw [Functor.comp_obj, representedSystem_obj]; exact hs j
  have := BigFppfOver.hasLimit_of_isAffine_of_size_le _ hW hI' hκ hs'
  have := BigFppfOver.preservesLimit_toScheme_of_size_le _ hW hI' hκ hs'
  obtain ⟨i₀⟩ := IsCofiltered.nonempty (C := I)
  have hlimS := isLimitOfPreserves (BigFppfOver.toScheme B S hS)
    (limit.isLimit (representedSystem Z R W w ψ'))
  have haff : ∀ j, IsAffine ((representedSystem Z R W w ψ' ⋙
      BigFppfOver.toScheme B S hS).obj j) := hW
  have h1 : IsAffine ((BigFppfOver.toScheme B S hS).obj (limit (representedSystem Z R W w ψ'))) :=
    Scheme.isAffine_of_isLimit _ hlimS
  have h2 := Scheme.size_le_of_isLimit_of_isAffine
    (representedSystem Z R W w ψ' ⋙ BigFppfOver.toScheme B S hS) haff hs' hlimS
  rw [Functor.mapCone_pt, limit.cone_x] at h2
  have h3 := nonempty_limit_representation Z R W w ψ' (limit.isLimit _) c hc i₀
  exact ⟨_, _, h1, h2, h3⟩

end Limits

/-! ### Subfunctors of represented functors -/

section Injective

/-- **The morphism of algebraic spaces attached to an injective morphism of functors of points
over `Y` is a monomorphism of presheaves.** -/
theorem mono_hom_spacePointsOverInv {Y H H' : AlgebraicSpaces B S hS} {p : H ⟶ Y} {p' : H' ⟶ Y}
    (β : spacePointsOver p ⟶ spacePointsOver p') (hβ : ∀ T, Function.Injective (β.app T)) :
    Mono (spacePointsOverInv β).hom := by
  refine (NatTrans.mono_iff_mono_app _).2 fun V => (mono_iff_injective _).2 fun x y hxy => ?_
  have hp : p.hom.app V x = p.hom.app V y := by
    rw [← spacePointsOverInv_comp β]
    exact congrArg (p'.hom.app V) hxy
  let T := pointTest p V.unop x
  let x' : spacePointsOverObj p T := pointTestSection p V.unop x
  let y' : spacePointsOverObj p T := ⟨y, hp.symm.trans (testPoint_pointTest p V.unop x).symm⟩
  have h₁ : (β.app (Opposite.op T) x').1 = (β.app (Opposite.op T) y').1 :=
    (spacePointsOverInvApp_eq β x').symm.trans (hxy.trans (spacePointsOverInvApp_eq β y'))
  exact congrArg Subtype.val (hβ _ (Subtype.ext h₁))

variable {Z : BigFppfOver B S hS} (hZ : IsAffine ((BigFppfOver.toScheme B S hS).obj Z))
  {R R₀ : (SchemesOver ((schemeSpaceFunctor B S hS).obj Z))ᵒᵖ ⥤ Type (u + 1)}

include hZ in
/-- **A subfunctor of a functor represented by an affine scheme of size at most `κ`, which is
itself an algebraic space affine over `Z`, is represented by an affine scheme of size at most
`2 ^ 2 ^ κ`**: its representing scheme is a subobject of the given one. -/
theorem IsAffineRepresentedOver.of_injective {κ : Cardinal.{u}}
    (h : IsAffineAlgebraicSpaceOver ((schemeSpaceFunctor B S hS).obj Z) R)
    (h₀ : IsAffineRepresentedOver Z κ R₀) (α : R ⟶ R₀)
    (hα : ∀ T, Function.Injective (α.app T)) :
    IsAffineRepresentedOver Z ((2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ κ) R := by
  obtain ⟨H, p, hp, ⟨c⟩⟩ := h
  obtain ⟨W₀, w₀, -, hs₀, ⟨c₀⟩⟩ := h₀
  obtain ⟨W', e, P, he, hP⟩ := exists_representing_over_of_isAffineHom B S hS H.2 p.hom hp
  have hW' : IsAffine ((BigFppfOver.toScheme B S hS).obj W') :=
    isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map P)
  let eS : (schemeSpaceFunctor B S hS).obj W' ≅ H :=
    { hom := ObjectProperty.homMk e.inv
      inv := ObjectProperty.homMk e.hom
      hom_inv_id := ObjectProperty.hom_ext _ e.inv_hom_id
      inv_hom_id := ObjectProperty.hom_ext _ e.hom_inv_id }
  let ψ : spacePointsOver ((schemeSpaceFunctor B S hS).map P) ⋙ uliftFunctor.{u + 1, u} ≅ R :=
    Functor.isoWhiskerRight (spacePointsOverIsoOfIso eS (p := (schemeSpaceFunctor B S hS).map P)
      (p' := p) (ObjectProperty.hom_ext _ he)) _ ≪≫ c
  let β := stripUlift (ψ.hom ≫ α ≫ c₀.inv)
  have hβ : ∀ T, Function.Injective (β.app T) := fun T a b hab =>
    congrArg ULift.down ((mono_iff_injective (ψ.hom.app T)).1 inferInstance
      (hα T ((mono_iff_injective (c₀.inv.app T)).1 inferInstance (congrArg ULift.up hab))))
  have hm := mono_hom_spacePointsOverInv β hβ
  have hm₀ : Mono (yoneda.preimage (spacePointsOverInv β).hom) :=
    (yoneda (C := BigFppfOver B S hS)).mono_of_mono_map
      ((Functor.map_preimage yoneda (spacePointsOverInv β).hom).symm ▸ hm)
  have _ : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    comp_preservesLimitsOfShape _ _
  have hsize := Scheme.size_le_of_mono
    ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (spacePointsOverInv β).hom))
  refine ⟨W', P, hW', hsize.trans (max_le ?_ ?_), ⟨ψ⟩⟩
  · exact power_le_power_left two_ne_zero ((Scheme.mk_le_two_pow_size _).trans
      (power_le_power_left two_ne_zero hs₀))
  · exact hs₀.trans ((cantor κ).le.trans (cantor _).le)

end Injective

end AlgebraicGeometry.Space

end
