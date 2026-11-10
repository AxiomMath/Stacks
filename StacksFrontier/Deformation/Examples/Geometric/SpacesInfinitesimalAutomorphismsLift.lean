module

public import StacksFrontier.Deformation.Examples.Geometric.SpacesSpecialFibreThickening
public import StacksFrontier.Deformation.Examples.Geometric.SpacesInfinitesimalAutomorphismsLiftTorsorTop
public import StacksFrontier.AlgebraicGeometry.Spaces.DeformationLiftCartesianTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleComposition

/-!
# Infinitesimal automorphisms of a deformation of an algebraic space as lifts

Let `X` be an algebraic space over the field `k`, `x₀` a point of its deformation category over
`k` and `i : x₀ ⟶ xε` a pushforward of `x₀` to an object `Aε` of `𝒞_Λ` with a dual-number
coordinate.  Write `X'` for the total space of `xε`, `G ⊆ X'` for its special fibre (the inverse
image of `Spec k ⊂ Spec Aε`, a first order thickening) and `π : X' ⟶ X` for the retraction
given by `i` (the total space of `x₀` is `X` itself, through its special-fibre map).

The fibre automorphisms `a` of `xε` are the self-maps of `X'` over `Spec Aε` fixing `X`, and
`a ↦ a ≫ π` identifies them with the *lifts* of `π|_G` over `Spec k`: the morphisms `X' ⟶ X`
over `Spec k` which agree with `π` on `G`.  Those lifts are a torsor under
`Hom(π|_G^*Ω_{X/k}, 𝒞_{G/X'})` ([Stacks Project, Tag 061D]); the resulting bijection of the
automorphism group with that group turns composition into addition.

## Main definitions

* `Deformation.Examples.spaceRetraction`: `π : X' ⟶ X`.
* `Deformation.Examples.spaceRetractionSpecial`: the restriction `e₀` of `π` to `G`.
* `Deformation.Examples.spaceAutEquivLifts`: fibre automorphisms are lifts.
* `Deformation.Examples.spaceAutMulEquivHom`: the fibre automorphism group is the additive group
  `Hom(e₀^*Ω_{X/k}, 𝒞_{G/X'})`.

## References

* [Stacks Project, Tag 061D](https://stacks.math.columbia.edu/tag/061D)
* [Stacks Project, Tag 0CK7](https://stacks.math.columbia.edu/tag/0CK7)
* [Stacks Project, Tag 0E41](https://stacks.math.columbia.edu/tag/0E41)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Space

universe u

namespace Deformation.Examples

variable {Λ : Type u} {k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable (B : BigFppfSite.{u}) (hΛ : B.Contains (Spec (.of Λ)))
variable (hSpec : ∀ A : ArtinianLocalAlgCat.{u, u, u} Λ k, B.Contains (Spec (.of A)))
variable (X : (BigFppfOver B (Spec (.of Λ)) hΛ)ᵒᵖ ⥤ Type u)
  (hX : IsAlgebraicSpace B (Spec (.of Λ)) hΛ X)
  (toK : X ⟶ yoneda.obj (spaceBaseOver B hΛ hSpec (residueFieldBase Λ k)))

/-- `X` as an algebraic space over `Spec Λ`. -/
abbrev spaceOf : AlgebraicSpaces B (Spec (.of Λ)) hΛ := ⟨X, hX⟩

/-- The structure morphism `X ⟶ Spec k`, as a morphism of algebraic spaces. -/
abbrev spaceStructureMap :
    spaceOf B hΛ X hX ⟶ schemeSpace (spaceBaseOver B hΛ hSpec (residueFieldBase Λ k)) :=
  ObjectProperty.homMk toK

variable {Aε : ArtinianLocalAlgCat.{u, u, u} Λ k}
  {x₀ : (spaceDeformationProjection B hΛ hSpec X hX toK).Fiber
    (residueFieldObject.{u, u, u} Λ k)}
  {xε : (spaceDeformationProjection B hΛ hSpec X hX toK).Fiber Aε}
  (i : x₀.1 ⟶ xε.1)

/-- The structure arrow of a point lies over a morphism to the residue field; its square is
cartesian. -/
theorem spaceSpecialMap_isPullback (y : Over (spaceSpecialFiber B hΛ hSpec X hX toK)) :
    IsPullback (spaceSpecialMap B hΛ hSpec X hX toK y) toK y.left.toBase
      (yoneda.map (spaceBaseOverMap B hΛ hSpec y.hom.base)) :=
  y.hom.cartesian

/-- **The retraction `π : X' ⟶ X`** of the total space of `xε` onto `X`: the space component of
`i` followed by the inverse of the special-fibre map of `x₀`. -/
def spaceRetraction :
    spaceTotalSpace B hΛ hSpec xε.1.left ⟶ spaceOf B hΛ X hX :=
  haveI := isIso_spaceSpecialMap_of_residueFieldObject B hΛ hSpec X hX toK x₀
  ObjectProperty.homMk (i.left.map ≫ inv (spaceSpecialMap B hΛ hSpec X hX toK x₀.1))

/-- `π` is a retraction of the special-fibre map of `xε`. -/
theorem spaceSpecialMap_comp_spaceRetraction :
    spaceSpecialMap B hΛ hSpec X hX toK xε.1 ≫ (spaceRetraction B hΛ hSpec X hX toK i).hom =
      𝟙 X := by
  have := isIso_spaceSpecialMap_of_residueFieldObject B hΛ hSpec X hX toK x₀
  change spaceSpecialMap B hΛ hSpec X hX toK xε.1 ≫ i.left.map ≫
    inv (spaceSpecialMap B hΛ hSpec X hX toK x₀.1) = 𝟙 X
  rw [← Category.assoc, spaceSpecialMap_comp B hΛ hSpec X hX toK i, IsIso.hom_inv_id]

/-- The structure arrow of a point over the residue-field object lies over an isomorphism of
spectra. -/
theorem isIso_yoneda_map_spaceBaseOverMap_residue :
    IsIso (yoneda.map (spaceBaseOverMap B hΛ hSpec x₀.1.hom.base)) := by
  have hs : IsTerminal (residueFieldObject.{u, u, u} Λ k) :=
    ArtinianLocalAlgCat.isTerminal_of_maximalIdeal_eq_bot _
      (IsLocalRing.maximalIdeal_eq_bot (R := ULift.{u} k))
  have hx : IsTerminal x₀.1.left.base := by
    rwa [show x₀.1.left.base = residueFieldObject.{u, u, u} Λ k from x₀.2]
  have hb : IsIso x₀.1.hom.base := isIso_of_isTerminal hx isTerminal_residueFieldBase _
  have : IsIso (spaceBaseOverMap B hΛ hSpec x₀.1.hom.base) :=
    ⟨⟨spaceBaseOverMap B hΛ hSpec (inv x₀.1.hom.base), by
      rw [← spaceBaseOverMap_comp, IsIso.inv_hom_id, spaceBaseOverMap_id], by
      rw [← spaceBaseOverMap_comp, IsIso.hom_inv_id, spaceBaseOverMap_id]⟩⟩
  exact Functor.map_isIso _ _

/-- **`π` lies over `Spec Aε ⟶ Spec k`**: after the isomorphism of spectra of the structure
arrow of `x₀`, `π ≫ (X ⟶ Spec k)` is the structure morphism of `X'` followed by the morphism of
spectra of `i`. -/
theorem spaceRetraction_comp_toK :
    (spaceRetraction B hΛ hSpec X hX toK i).hom ≫ toK ≫
        yoneda.map (spaceBaseOverMap B hΛ hSpec x₀.1.hom.base) =
      xε.1.left.toBase ≫ yoneda.map (spaceBaseOverMap B hΛ hSpec i.left.base) := by
  have := isIso_spaceSpecialMap_of_residueFieldObject B hΛ hSpec X hX toK x₀
  change (i.left.map ≫ inv (spaceSpecialMap B hΛ hSpec X hX toK x₀.1)) ≫ toK ≫ _ = _
  rw [← (spaceSpecialMap_isPullback B hΛ hSpec X hX toK x₀.1).w, Category.assoc,
    IsIso.inv_hom_id_assoc]
  exact i.left.cartesian.w

/-- A self-map of `X'` over `Spec Aε` does not change `π` over `Spec k`. -/
theorem comp_spaceRetraction_comp_toK (c : xε.1.left.space ⟶ xε.1.left.space)
    (hc : c ≫ xε.1.left.toBase = xε.1.left.toBase) :
    c ≫ (spaceRetraction B hΛ hSpec X hX toK i).hom ≫ toK =
      (spaceRetraction B hΛ hSpec X hX toK i).hom ≫ toK := by
  have := isIso_yoneda_map_spaceBaseOverMap_residue B hΛ hSpec X hX toK (x₀ := x₀)
  have h := spaceRetraction_comp_toK B hΛ hSpec X hX toK i
  refine (cancel_mono (yoneda.map (spaceBaseOverMap B hΛ hSpec x₀.1.hom.base))).1 ?_
  exact (Category.assoc _ _ _).trans ((congrArg (c ≫ ·) ((Category.assoc _ _ _).trans h)).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hc).trans
      (h.symm.trans (Category.assoc _ _ _).symm))))

/-- Maps into the total space of `xε` are determined by their composites with `π` and with the
structure morphism: the space component of `i` is cartesian and the special-fibre map of `x₀` is
invertible. -/
theorem spaceTotal_hom_ext {T : (BigFppfOver B (Spec (.of Λ)) hΛ)ᵒᵖ ⥤ Type u}
    {m m' : T ⟶ xε.1.left.space}
    (h₁ : m ≫ (spaceRetraction B hΛ hSpec X hX toK i).hom =
      m' ≫ (spaceRetraction B hΛ hSpec X hX toK i).hom)
    (h₂ : m ≫ xε.1.left.toBase = m' ≫ xε.1.left.toBase) : m = m' := by
  have := isIso_spaceSpecialMap_of_residueFieldObject B hΛ hSpec X hX toK x₀
  refine i.left.cartesian.hom_ext ?_ h₂
  simpa [spaceRetraction] using congrArg (· ≫ spaceSpecialMap B hΛ hSpec X hX toK x₀.1) h₁

/-! ### The special fibre -/

/-- The morphism `xε.base ⟶ k` underlying the structure arrow of `xε`. -/
abbrev spacePointResidue (y : Over (spaceSpecialFiber B hΛ hSpec X hX toK)) :
    y.left.base ⟶ residueFieldBase Λ k :=
  y.hom.base

/-- The closed immersion `Spec k ⟶ Spec A` underlying the structure arrow of a point is a
monomorphism of presheaves. -/
theorem mono_yoneda_map_spaceBaseOverMap (y : Over (spaceSpecialFiber B hΛ hSpec X hX toK)) :
    Mono (yoneda.map (spaceBaseOverMap B hΛ hSpec y.hom.base)) := by
  have hm : Mono ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map
      (spaceBaseOverMap B hΛ hSpec y.hom.base)) := by
    rw [toScheme_map_spaceBaseOverMap]
    have := IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom y.hom.base.hom.toRingHom)
      (surjective_of_hom_residueFieldBase y.hom.base)
    infer_instance
  have : Mono (spaceBaseOverMap B hΛ hSpec y.hom.base) :=
    (BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).mono_of_mono_map hm
  infer_instance

/-- The special fibre `G ⊆ X'` of the total space of a point. -/
abbrev spacePointSpecial (y : Over (spaceSpecialFiber B hΛ hSpec X hX toK)) :
    ClosedSubspaces B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec y.left).1 :=
  spaceSpecialSubspace B hΛ hSpec y.left y.hom.base

/-- The corestriction of a monomorphism of presheaves to its range is an isomorphism. -/
theorem isIso_toRange_of_mono {F F' : (BigFppfOver B (Spec (.of Λ)) hΛ)ᵒᵖ ⥤ Type u}
    (p : F' ⟶ F) (_ : Mono p) : IsIso (Subfunctor.toRange p) :=
  inferInstance

/-- The projection of the special fibre to `Spec k`. -/
def spacePointSpecialToK (y : Over (spaceSpecialFiber B hΛ hSpec X hX toK)) :
    (spacePointSpecial B hΛ hSpec X hX toK y).1.toFunctor ⟶
      yoneda.obj (spaceBaseOver B hΛ hSpec (residueFieldBase Λ k)) :=
  (spaceBaseSpecialSubspace B hΛ hSpec y.hom.base).1.fromPreimage y.left.toBase ≫
    @inv _ _ _ _ (Subfunctor.toRange (yoneda.map (spaceBaseOverMap B hΛ hSpec y.hom.base)))
      (isIso_toRange_of_mono B hΛ _ (mono_yoneda_map_spaceBaseOverMap B hΛ hSpec X hX toK y))

/-- The inclusion of the special fibre `G` followed by the structure morphism of the total space
is `spacePointSpecialToK` followed by the closed immersion `Spec k ⟶ Spec A`. -/
theorem spacePointSpecial_ι_comp_toBase (y : Over (spaceSpecialFiber B hΛ hSpec X hX toK)) :
    (spacePointSpecial B hΛ hSpec X hX toK y).1.ι ≫ y.left.toBase =
      spacePointSpecialToK B hΛ hSpec X hX toK y ≫
        yoneda.map (spaceBaseOverMap B hΛ hSpec y.hom.base) := by
  have ht := isIso_toRange_of_mono B hΛ _ (mono_yoneda_map_spaceBaseOverMap B hΛ hSpec X hX toK y)
  have h1 := Subfunctor.fromPreimage_ι (spaceBaseSpecialSubspace B hΛ hSpec y.hom.base).1
    y.left.toBase
  have h2 := @IsIso.inv_hom_id _ _ _ _ _ ht
  have h3 := Subfunctor.toRange_ι (yoneda.map (spaceBaseOverMap B hΛ hSpec y.hom.base))
  change _ = ((spaceBaseSpecialSubspace B hΛ hSpec y.hom.base).1.fromPreimage y.left.toBase ≫
    @inv _ _ _ _ (Subfunctor.toRange (yoneda.map (spaceBaseOverMap B hΛ hSpec y.hom.base))) ht) ≫
      yoneda.map (spaceBaseOverMap B hΛ hSpec y.hom.base)
  refine h1.symm.trans ?_
  refine Eq.trans ?_ (congrArg (_ ≫ ·) h3)
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine Eq.trans ?_ (congrArg (_ ≫ ·) (Category.assoc _ _ _))
  exact congrArg (_ ≫ ·) ((congrArg (· ≫ _) h2).trans (Category.id_comp _)).symm

/-- **The special fibre is `X`**: the morphism `G ⟶ X` through the cartesian square of the
structure arrow. -/
def spacePointSpecialToX (y : Over (spaceSpecialFiber B hΛ hSpec X hX toK)) :
    (spacePointSpecial B hΛ hSpec X hX toK y).1.toFunctor ⟶ X :=
  (spaceSpecialMap_isPullback B hΛ hSpec X hX toK y).lift _ _
    (spacePointSpecial_ι_comp_toBase B hΛ hSpec X hX toK y)

/-- The map `G ⟶ X` followed by the special-fibre map is the inclusion of the special fibre. -/
theorem spacePointSpecialToX_comp (y : Over (spaceSpecialFiber B hΛ hSpec X hX toK)) :
    spacePointSpecialToX B hΛ hSpec X hX toK y ≫ spaceSpecialMap B hΛ hSpec X hX toK y =
      (spacePointSpecial B hΛ hSpec X hX toK y).1.ι :=
  (spaceSpecialMap_isPullback B hΛ hSpec X hX toK y).lift_fst _ _ _

/-- The special-fibre map lands in the special fibre. -/
def spaceSpecialMapToSpecial (y : Over (spaceSpecialFiber B hΛ hSpec X hX toK)) :
    X ⟶ (spacePointSpecial B hΛ hSpec X hX toK y).1.toFunctor :=
  Subfunctor.lift (spaceSpecialMap B hΛ hSpec X hX toK y) (by
    rintro U _ ⟨x, rfl⟩
    exact ⟨toK.app U x,
      (congrArg (fun m => m.app U x) (spaceSpecialMap_isPullback B hΛ hSpec X hX toK y).w).symm⟩)

/-- The special-fibre map into the special fibre, followed by the inclusion of the special fibre,
is the special-fibre map. -/
theorem spaceSpecialMapToSpecial_ι (y : Over (spaceSpecialFiber B hΛ hSpec X hX toK)) :
    spaceSpecialMapToSpecial B hΛ hSpec X hX toK y ≫
        (spacePointSpecial B hΛ hSpec X hX toK y).1.ι =
      spaceSpecialMap B hΛ hSpec X hX toK y :=
  rfl

/-- A self-map of `X'` fixing the special-fibre map restricts to the identity of `G`. -/
theorem spacePointSpecial_ι_comp_of_fixes (y : Over (spaceSpecialFiber B hΛ hSpec X hX toK))
    (c : y.left.space ⟶ y.left.space)
    (hc : spaceSpecialMap B hΛ hSpec X hX toK y ≫ c = spaceSpecialMap B hΛ hSpec X hX toK y) :
    (spacePointSpecial B hΛ hSpec X hX toK y).1.ι ≫ c =
      (spacePointSpecial B hΛ hSpec X hX toK y).1.ι := by
  rw [← spacePointSpecialToX_comp, Category.assoc, hc]

/-- The restriction of `π` to the special fibre of `xε`, as a morphism to the top closed
subspace of `X`. -/
def spaceRetractionSpecial :
    (⟨(spacePointSpecial B hΛ hSpec X hX toK xε.1).1.toFunctor,
        (spacePointSpecial B hΛ hSpec X hX toK xε.1).2.1⟩ : AlgebraicSpaces B (Spec (.of Λ)) hΛ) ⟶
      (⟨(topSubspace B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)).1.toFunctor,
        (topSubspace B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)).2.1⟩ :
          AlgebraicSpaces B (Spec (.of Λ)) hΛ) :=
  ObjectProperty.homMk (Subfunctor.lift
    ((spacePointSpecial B hΛ hSpec X hX toK xε.1).1.ι ≫
      (spaceRetraction B hΛ hSpec X hX toK i).hom) le_top)

/-- The inclusion of the special fibre followed by `π` is the restriction `e₀` of `π` followed by
the inclusion of the top closed subspace of `X`. -/
theorem spaceRetractionSpecial_spec :
    subspaceInclusion B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec xε.1.left)
        (spacePointSpecial B hΛ hSpec X hX toK xε.1) ≫ spaceRetraction B hΛ hSpec X hX toK i =
      spaceRetractionSpecial B hΛ hSpec X hX toK i ≫
        subspaceInclusion B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
          (topSubspace B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)) :=
  rfl

/-- The special fibre of `xε` is a first order thickening of its total space. -/
theorem isFirstOrderThickening_spacePointSpecial
    {g : residueFieldObject.{u, u, u} Λ k ⟶ Aε} {e : Aε ⟶ residueFieldObject.{u, u, u} Λ k}
    (hpair : IsCanonicalDualNumberPair g e) :
    IsFirstOrderThickening B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec xε.1.left)
      (spacePointSpecial B hΛ hSpec X hX toK xε.1).1 := by
  refine isFirstOrderThickening_spaceSpecialSubspace B hΛ hSpec _ _ ?_
  rw [show xε.1.left.base = Aε from xε.2]
  exact maximalIdeal_sq_eq_bot_of_isCanonicalDualNumberPair hpair

/-! ### Self-maps over the base act trivially on the conormal module -/

section Conormal

attribute [local irreducible] modulePullback

variable (P : FlatAlgebraicSpaceFamily B hΛ hSpec) (f : P.base ⟶ residueFieldBase Λ k)

/-- The special fibre of a family, as an algebraic space. -/
abbrev spaceSpecialSpace : AlgebraicSpaces B (Spec (.of Λ)) hΛ :=
  ⟨(spaceSpecialSubspace B hΛ hSpec P f).1.toFunctor, (spaceSpecialSubspace B hΛ hSpec P f).2.1⟩

/-- The square of the special fibre over `Spec k ⊂ Spec A`. -/
theorem spaceSpecialSubspace_square :
    subspaceInclusion B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec P)
        (spaceSpecialSubspace B hΛ hSpec P f) ≫ spaceTotalToBase B hΛ hSpec P =
      preimageProjection B (Spec (.of Λ)) hΛ (spaceTotalToBase B hΛ hSpec P)
          (spaceBaseSpecialSubspace B hΛ hSpec f) ≫
        subspaceInclusion B (Spec (.of Λ)) hΛ (schemeSpace (spaceBaseOver B hΛ hSpec P.base))
          (spaceBaseSpecialSubspace B hΛ hSpec f) :=
  conormalEtaleRestrictionSquare B (Spec (.of Λ)) hΛ (spaceTotalToBase B hΛ hSpec P)
    (spaceBaseSpecialSubspace B hΛ hSpec f)

/-- The conormal map of the square of the special fibre over `Spec k ⊂ Spec A`, pulled back
along the identity, is an epimorphism ([Stacks Project, Tag 04CQ], surjectivity). -/
theorem epi_modulePullback_id_conormalMap_spaceSpecialSubspace :
    Epi ((modulePullback B (Spec (.of Λ)) hΛ
      (𝟙 (⟨(preimageSubspace B (Spec (.of Λ)) hΛ (spaceTotalToBase B hΛ hSpec P)
          (spaceBaseSpecialSubspace B hΛ hSpec f)).1.toFunctor,
        (preimageSubspace B (Spec (.of Λ)) hΛ (spaceTotalToBase B hΛ hSpec P)
          (spaceBaseSpecialSubspace B hΛ hSpec f)).2.1⟩ : AlgebraicSpaces B (Spec (.of Λ)) hΛ))).map
      (conormalMap B (Spec (.of Λ)) hΛ (preimageSubspace B (Spec (.of Λ)) hΛ
          (spaceTotalToBase B hΛ hSpec P) (spaceBaseSpecialSubspace B hΛ hSpec f))
        (spaceBaseSpecialSubspace B hΛ hSpec f) (spaceTotalToBase B hΛ hSpec P)
        (preimageProjection B (Spec (.of Λ)) hΛ (spaceTotalToBase B hΛ hSpec P)
          (spaceBaseSpecialSubspace B hΛ hSpec f))
        (conormalEtaleRestrictionSquare B (Spec (.of Λ)) hΛ (spaceTotalToBase B hΛ hSpec P)
          (spaceBaseSpecialSubspace B hΛ hSpec f)))) :=
  epi_modulePullback_conormalMap B (Spec (.of Λ)) hΛ (spaceTotalToBase B hΛ hSpec P)
    (spaceBaseSpecialSubspace B hΛ hSpec f) _

/-- The conormal map of a self-map of the total space over `Spec A` fixing the special fibre,
composed with the conormal map of the square over `Spec k ⊂ Spec A`, is the conormal map of that
square ([Stacks Project, Tag 04G2]). -/
theorem conormalMap_spaceSpecialSubspace_comp
    (c : spaceTotalSpace B hΛ hSpec P ⟶ spaceTotalSpace B hΛ hSpec P)
    (hcb : c ≫ spaceTotalToBase B hΛ hSpec P = spaceTotalToBase B hΛ hSpec P)
    (ha : subspaceInclusion B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec P)
        (preimageSubspace B (Spec (.of Λ)) hΛ (spaceTotalToBase B hΛ hSpec P)
          (spaceBaseSpecialSubspace B hΛ hSpec f)) ≫ c =
      𝟙 (⟨(preimageSubspace B (Spec (.of Λ)) hΛ (spaceTotalToBase B hΛ hSpec P)
          (spaceBaseSpecialSubspace B hΛ hSpec f)).1.toFunctor,
        (preimageSubspace B (Spec (.of Λ)) hΛ (spaceTotalToBase B hΛ hSpec P)
          (spaceBaseSpecialSubspace B hΛ hSpec f)).2.1⟩ : AlgebraicSpaces B (Spec (.of Λ)) hΛ) ≫
            subspaceInclusion B (Spec (.of Λ)) hΛ
        (spaceTotalSpace B hΛ hSpec P) (preimageSubspace B (Spec (.of Λ)) hΛ
          (spaceTotalToBase B hΛ hSpec P)
          (spaceBaseSpecialSubspace B hΛ hSpec f)))
    (hsq'' : subspaceInclusion B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec P)
        (preimageSubspace B (Spec (.of Λ)) hΛ (spaceTotalToBase B hΛ hSpec P)
          (spaceBaseSpecialSubspace B hΛ hSpec f)) ≫ c ≫ spaceTotalToBase B hΛ hSpec P =
      (𝟙 (⟨(preimageSubspace B (Spec (.of Λ)) hΛ (spaceTotalToBase B hΛ hSpec P)
          (spaceBaseSpecialSubspace B hΛ hSpec f)).1.toFunctor,
        (preimageSubspace B (Spec (.of Λ)) hΛ (spaceTotalToBase B hΛ hSpec P)
          (spaceBaseSpecialSubspace B hΛ hSpec f)).2.1⟩ : AlgebraicSpaces B (Spec (.of Λ)) hΛ) ≫
            preimageProjection B (Spec (.of Λ)) hΛ
          (spaceTotalToBase B hΛ hSpec P) (spaceBaseSpecialSubspace B hΛ hSpec f)) ≫
        subspaceInclusion B (Spec (.of Λ)) hΛ (schemeSpace (spaceBaseOver B hΛ hSpec P.base))
          (spaceBaseSpecialSubspace B hΛ hSpec f))
    (hsq₀ : subspaceInclusion B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec P)
        (preimageSubspace B (Spec (.of Λ)) hΛ (spaceTotalToBase B hΛ hSpec P)
          (spaceBaseSpecialSubspace B hΛ hSpec f)) ≫ spaceTotalToBase B hΛ hSpec P =
      (𝟙 (⟨(preimageSubspace B (Spec (.of Λ)) hΛ (spaceTotalToBase B hΛ hSpec P)
          (spaceBaseSpecialSubspace B hΛ hSpec f)).1.toFunctor,
        (preimageSubspace B (Spec (.of Λ)) hΛ (spaceTotalToBase B hΛ hSpec P)
          (spaceBaseSpecialSubspace B hΛ hSpec f)).2.1⟩ : AlgebraicSpaces B (Spec (.of Λ)) hΛ) ≫
            preimageProjection B (Spec (.of Λ)) hΛ
          (spaceTotalToBase B hΛ hSpec P) (spaceBaseSpecialSubspace B hΛ hSpec f)) ≫
        subspaceInclusion B (Spec (.of Λ)) hΛ (schemeSpace (spaceBaseOver B hΛ hSpec P.base))
          (spaceBaseSpecialSubspace B hΛ hSpec f)) :
    conormalMap B (Spec (.of Λ)) hΛ (preimageSubspace B (Spec (.of Λ)) hΛ
      (spaceTotalToBase B hΛ hSpec P)
          (spaceBaseSpecialSubspace B hΛ hSpec f))
        (spaceBaseSpecialSubspace B hΛ hSpec f) (spaceTotalToBase B hΛ hSpec P)
        (𝟙 (⟨(preimageSubspace B (Spec (.of Λ)) hΛ (spaceTotalToBase B hΛ hSpec P)
          (spaceBaseSpecialSubspace B hΛ hSpec f)).1.toFunctor,
        (preimageSubspace B (Spec (.of Λ)) hΛ (spaceTotalToBase B hΛ hSpec P)
          (spaceBaseSpecialSubspace B hΛ hSpec f)).2.1⟩ : AlgebraicSpaces B (Spec (.of Λ)) hΛ) ≫
            preimageProjection B (Spec (.of Λ)) hΛ
          (spaceTotalToBase B hΛ hSpec P) (spaceBaseSpecialSubspace B hΛ hSpec f)) hsq₀ =
      (modulePullbackCompIso B (Spec (.of Λ)) hΛ (𝟙 (⟨(preimageSubspace B (Spec (.of Λ)) hΛ
        (spaceTotalToBase B hΛ hSpec P)
          (spaceBaseSpecialSubspace B hΛ hSpec f)).1.toFunctor,
        (preimageSubspace B (Spec (.of Λ)) hΛ (spaceTotalToBase B hΛ hSpec P)
          (spaceBaseSpecialSubspace B hΛ hSpec f)).2.1⟩ : AlgebraicSpaces B (Spec (.of Λ)) hΛ))
          (preimageProjection B (Spec (.of Λ)) hΛ (spaceTotalToBase B hΛ hSpec P)
            (spaceBaseSpecialSubspace B hΛ hSpec f))).inv.app
          (conormalModule B (Spec (.of Λ)) hΛ (schemeSpace (spaceBaseOver B hΛ hSpec P.base))
            (spaceBaseSpecialSubspace B hΛ hSpec f)) ≫
        (modulePullback B (Spec (.of Λ)) hΛ (𝟙 (⟨(preimageSubspace B (Spec (.of Λ)) hΛ
          (spaceTotalToBase B hΛ hSpec P)
          (spaceBaseSpecialSubspace B hΛ hSpec f)).1.toFunctor,
        (preimageSubspace B (Spec (.of Λ)) hΛ (spaceTotalToBase B hΛ hSpec P)
          (spaceBaseSpecialSubspace B hΛ hSpec f)).2.1⟩ : AlgebraicSpaces B (Spec (.of Λ)) hΛ))).map
          (conormalMap B (Spec (.of Λ)) hΛ (preimageSubspace B (Spec (.of Λ)) hΛ
            (spaceTotalToBase B hΛ hSpec P)
          (spaceBaseSpecialSubspace B hΛ hSpec f))
            (spaceBaseSpecialSubspace B hΛ hSpec f) (spaceTotalToBase B hΛ hSpec P)
            (preimageProjection B (Spec (.of Λ)) hΛ (spaceTotalToBase B hΛ hSpec P)
              (spaceBaseSpecialSubspace B hΛ hSpec f))
            (conormalEtaleRestrictionSquare B (Spec (.of Λ)) hΛ (spaceTotalToBase B hΛ hSpec P)
          (spaceBaseSpecialSubspace B hΛ hSpec f))) ≫
        conormalMap B (Spec (.of Λ)) hΛ (preimageSubspace B (Spec (.of Λ)) hΛ
          (spaceTotalToBase B hΛ hSpec P)
          (spaceBaseSpecialSubspace B hΛ hSpec f))
          (preimageSubspace B (Spec (.of Λ)) hΛ (spaceTotalToBase B hΛ hSpec P)
          (spaceBaseSpecialSubspace B hΛ hSpec f)) c (𝟙 (⟨(preimageSubspace B (Spec (.of Λ)) hΛ
            (spaceTotalToBase B hΛ hSpec P)
          (spaceBaseSpecialSubspace B hΛ hSpec f)).1.toFunctor,
        (preimageSubspace B (Spec (.of Λ)) hΛ (spaceTotalToBase B hΛ hSpec P)
          (spaceBaseSpecialSubspace B hΛ hSpec f)).2.1⟩ : AlgebraicSpaces B (Spec (.of Λ)) hΛ))
            ha :=
  (conormalMap_congr_upper B (Spec (.of Λ)) hΛ (preimageSubspace B (Spec (.of Λ)) hΛ
    (spaceTotalToBase B hΛ hSpec P)
          (spaceBaseSpecialSubspace B hΛ hSpec f))
      (spaceBaseSpecialSubspace B hΛ hSpec f) hcb.symm _ hsq₀ hsq'').trans
    (conormalMap_comp B (Spec (.of Λ)) hΛ c (spaceTotalToBase B hΛ hSpec P)
      (preimageSubspace B (Spec (.of Λ)) hΛ (spaceTotalToBase B hΛ hSpec P)
          (spaceBaseSpecialSubspace B hΛ hSpec f)) (preimageSubspace B (Spec (.of Λ)) hΛ
            (spaceTotalToBase B hΛ hSpec P)
          (spaceBaseSpecialSubspace B hΛ hSpec f))
      (spaceBaseSpecialSubspace B hΛ hSpec f) (𝟙 (⟨(preimageSubspace B (Spec (.of Λ)) hΛ
        (spaceTotalToBase B hΛ hSpec P)
          (spaceBaseSpecialSubspace B hΛ hSpec f)).1.toFunctor,
        (preimageSubspace B (Spec (.of Λ)) hΛ (spaceTotalToBase B hΛ hSpec P)
          (spaceBaseSpecialSubspace B hΛ hSpec f)).2.1⟩ : AlgebraicSpaces B (Spec (.of Λ)) hΛ))
      (preimageProjection B (Spec (.of Λ)) hΛ (spaceTotalToBase B hΛ hSpec P)
        (spaceBaseSpecialSubspace B hΛ hSpec f)) ha
      (conormalEtaleRestrictionSquare B (Spec (.of Λ)) hΛ (spaceTotalToBase B hΛ hSpec P)
          (spaceBaseSpecialSubspace B hΛ hSpec f)) hsq'')

/-- **A self-map of the total space over `Spec A` restricting to the identity of the special
fibre has the conormal map of the identity** ([Stacks Project, Tag 0CK7]): the special fibre is
the inverse image of `Spec k ⊂ Spec A`, the map of conormal modules of that cartesian square is
surjective, and both conormal maps composed with it are the conormal map of the square, by the
composition law of [Stacks Project, Tag 04G2]. -/
theorem conormalMap_preimageSpecial_eq_id
    (c : spaceTotalSpace B hΛ hSpec P ⟶ spaceTotalSpace B hΛ hSpec P)
    (hcb : c ≫ spaceTotalToBase B hΛ hSpec P = spaceTotalToBase B hΛ hSpec P)
    (ha : subspaceInclusion B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec P)
        (preimageSubspace B (Spec (.of Λ)) hΛ (spaceTotalToBase B hΛ hSpec P)
          (spaceBaseSpecialSubspace B hΛ hSpec f)) ≫ c =
      𝟙 (⟨(preimageSubspace B (Spec (.of Λ)) hΛ (spaceTotalToBase B hΛ hSpec P)
          (spaceBaseSpecialSubspace B hΛ hSpec f)).1.toFunctor,
        (preimageSubspace B (Spec (.of Λ)) hΛ (spaceTotalToBase B hΛ hSpec P)
          (spaceBaseSpecialSubspace B hΛ hSpec f)).2.1⟩ : AlgebraicSpaces B (Spec (.of Λ)) hΛ) ≫
            subspaceInclusion B (Spec (.of Λ)) hΛ
        (spaceTotalSpace B hΛ hSpec P) (preimageSubspace B (Spec (.of Λ)) hΛ
          (spaceTotalToBase B hΛ hSpec P)
          (spaceBaseSpecialSubspace B hΛ hSpec f)))
    (hid : subspaceInclusion B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec P)
        (preimageSubspace B (Spec (.of Λ)) hΛ (spaceTotalToBase B hΛ hSpec P)
          (spaceBaseSpecialSubspace B hΛ hSpec f)) ≫ 𝟙 _ =
      𝟙 (⟨(preimageSubspace B (Spec (.of Λ)) hΛ (spaceTotalToBase B hΛ hSpec P)
          (spaceBaseSpecialSubspace B hΛ hSpec f)).1.toFunctor,
        (preimageSubspace B (Spec (.of Λ)) hΛ (spaceTotalToBase B hΛ hSpec P)
          (spaceBaseSpecialSubspace B hΛ hSpec f)).2.1⟩ : AlgebraicSpaces B (Spec (.of Λ)) hΛ) ≫
            subspaceInclusion B (Spec (.of Λ)) hΛ
        (spaceTotalSpace B hΛ hSpec P) (preimageSubspace B (Spec (.of Λ)) hΛ
          (spaceTotalToBase B hΛ hSpec P)
          (spaceBaseSpecialSubspace B hΛ hSpec f))) :
    conormalMap B (Spec (.of Λ)) hΛ (preimageSubspace B (Spec (.of Λ)) hΛ
      (spaceTotalToBase B hΛ hSpec P)
          (spaceBaseSpecialSubspace B hΛ hSpec f))
        (preimageSubspace B (Spec (.of Λ)) hΛ (spaceTotalToBase B hΛ hSpec P)
          (spaceBaseSpecialSubspace B hΛ hSpec f)) c (𝟙 (⟨(preimageSubspace B (Spec (.of Λ)) hΛ
            (spaceTotalToBase B hΛ hSpec P)
          (spaceBaseSpecialSubspace B hΛ hSpec f)).1.toFunctor,
        (preimageSubspace B (Spec (.of Λ)) hΛ (spaceTotalToBase B hΛ hSpec P)
          (spaceBaseSpecialSubspace B hΛ hSpec f)).2.1⟩ : AlgebraicSpaces B (Spec (.of Λ)) hΛ)) ha =
      conormalMap B (Spec (.of Λ)) hΛ (preimageSubspace B (Spec (.of Λ)) hΛ
        (spaceTotalToBase B hΛ hSpec P)
          (spaceBaseSpecialSubspace B hΛ hSpec f))
        (preimageSubspace B (Spec (.of Λ)) hΛ (spaceTotalToBase B hΛ hSpec P)
          (spaceBaseSpecialSubspace B hΛ hSpec f)) (𝟙 _) (𝟙 (⟨(preimageSubspace B (Spec (.of Λ)) hΛ
            (spaceTotalToBase B hΛ hSpec P)
          (spaceBaseSpecialSubspace B hΛ hSpec f)).1.toFunctor,
        (preimageSubspace B (Spec (.of Λ)) hΛ (spaceTotalToBase B hΛ hSpec P)
          (spaceBaseSpecialSubspace B hΛ hSpec f)).2.1⟩ : AlgebraicSpaces B (Spec (.of Λ)) hΛ))
            hid := by
  have hsq₀ := conormalEtaleRestrictionSquare B (Spec (.of Λ)) hΛ (spaceTotalToBase B hΛ hSpec P)
    (spaceBaseSpecialSubspace B hΛ hSpec f)
  have h1 := conormalMap_spaceSpecialSubspace_comp B hΛ hSpec P f c hcb ha (by rwa [hcb]) hsq₀
  have h2 := conormalMap_spaceSpecialSubspace_comp B hΛ hSpec P f (𝟙 _) (Category.id_comp _) hid
    (by rwa [Category.id_comp]) hsq₀
  exact cancel_iso_inv_epi_left
    ((modulePullbackCompIso B (Spec (.of Λ)) hΛ (𝟙 (⟨(preimageSubspace B (Spec (.of Λ)) hΛ
      (spaceTotalToBase B hΛ hSpec P)
          (spaceBaseSpecialSubspace B hΛ hSpec f)).1.toFunctor,
        (preimageSubspace B (Spec (.of Λ)) hΛ (spaceTotalToBase B hΛ hSpec P)
          (spaceBaseSpecialSubspace B hΛ hSpec f)).2.1⟩ : AlgebraicSpaces B (Spec (.of Λ)) hΛ))
      (preimageProjection B (Spec (.of Λ)) hΛ (spaceTotalToBase B hΛ hSpec P)
        (spaceBaseSpecialSubspace B hΛ hSpec f))).app
      (conormalModule B (Spec (.of Λ)) hΛ (schemeSpace (spaceBaseOver B hΛ hSpec P.base))
        (spaceBaseSpecialSubspace B hΛ hSpec f))) _
    (epi_modulePullback_id_conormalMap_spaceSpecialSubspace B hΛ hSpec P f) _ _ (h1.symm.trans h2)


/-- **A self-map of the total space over `Spec A` restricting to the identity of the special
fibre has the conormal map of the identity** ([Stacks Project, Tag 0CK7]), at the spelling
`Deformation.Examples.spaceSpecialSubspace` of the special fibre. -/
theorem conormalMap_spaceSpecialSubspace_eq_id
    (c : spaceTotalSpace B hΛ hSpec P ⟶ spaceTotalSpace B hΛ hSpec P)
    (hcb : c ≫ spaceTotalToBase B hΛ hSpec P = spaceTotalToBase B hΛ hSpec P)
    (ha : subspaceInclusion B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec P)
        (spaceSpecialSubspace B hΛ hSpec P f) ≫ c =
      𝟙 _ ≫ subspaceInclusion B (Spec (.of Λ)) hΛ
        (spaceTotalSpace B hΛ hSpec P) (spaceSpecialSubspace B hΛ hSpec P f))
    (hid : subspaceInclusion B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec P)
        (spaceSpecialSubspace B hΛ hSpec P f) ≫ 𝟙 _ =
      𝟙 _ ≫ subspaceInclusion B (Spec (.of Λ)) hΛ
        (spaceTotalSpace B hΛ hSpec P) (spaceSpecialSubspace B hΛ hSpec P f)) :
    conormalMap B (Spec (.of Λ)) hΛ (spaceSpecialSubspace B hΛ hSpec P f)
        (spaceSpecialSubspace B hΛ hSpec P f) c (𝟙 _) ha =
      conormalMap B (Spec (.of Λ)) hΛ (spaceSpecialSubspace B hΛ hSpec P f)
        (spaceSpecialSubspace B hΛ hSpec P f) (𝟙 _) (𝟙 _) hid :=
  conormalMap_preimageSpecial_eq_id B hΛ hSpec P f c hcb ha hid

end Conormal

end Deformation.Examples

end
