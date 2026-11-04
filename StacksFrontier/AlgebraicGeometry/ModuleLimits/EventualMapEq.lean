module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.MorphismLimit
public import StacksFrontier.AlgebraicGeometry.EventualLimitProperties.Basic
public import StacksFrontier.AlgebraicGeometry.PullbackInvertible.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Eventual equality of morphisms of finitely presented modules through a cofiltered limit

Let `D` be a cofiltered diagram of schemes with affine transition morphisms, let `c` be a limit
cone on it and let `ψ₁, ψ₂ : F ⟶ G` be two morphisms of sheaves of modules of finite
presentation on a quasi-compact stage `D.obj i`.  If the pullbacks of `ψ₁` and `ψ₂` to `c.pt`
agree, then already their pullbacks to some stage `D.obj j` over `i` agree.  This is part (3)
of Tag 01ZR.

## Main results

* `Stacks.AlgebraicGeometry.ModuleLimits.exists_pullback_map_eq_of_isLimit`: the statement
  above, for a cofiltered diagram with affine transition morphisms whose morphisms live in the
  universe of the schemes; only the stage carrying the two morphisms is quasi-compact.
* `Stacks.AlgebraicGeometry.ModuleLimits.exists_pullback_map_eq_of_isLimit'`: the same with the
  index morphism universe unrestricted, so at the universe shape
  `{I : Type u} [Category.{v} I] (D : I ⥤ Scheme.{u})` and with no smallness hypothesis.
* `Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_restrict_cover`: two morphisms of sheaves of
  modules on a scheme are equal as soon as their restrictions to the members of an open covering
  are equal.
* `Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_restrict`: the restriction of a
  module of finite presentation to an open subscheme is of finite presentation.

## References

* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
* [Stacks Project, Tag 05N7](https://stacks.math.columbia.edu/tag/05N7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe v u

namespace Stacks.AlgebraicGeometry.ModuleLimits

open Scheme.Modules

/-! ### Transporting an equality of images along a natural isomorphism -/

/-- If two parallel morphisms have equal images under a functor, they have equal images under
any isomorphic functor. -/
theorem map_eq_of_natIso {C₁ C₂ : Type*} [Category C₁] [Category C₂] {P Q : C₁ ⥤ C₂}
    (α : P ≅ Q) {A B : C₁} {f g : A ⟶ B} (h : P.map f = P.map g) : Q.map f = Q.map g := by
  rw [← cancel_epi (α.hom.app A), ← α.hom.naturality f, ← α.hom.naturality g, h]

/-- An equality of pullbacks of two morphisms along `g` persists after precomposing `g` with an
arbitrary morphism. -/
theorem pullback_map_eq_of_precomp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {M N : Z.Modules} {χ₁ χ₂ : M ⟶ N}
    (h : (Scheme.Modules.pullback g).map χ₁ = (Scheme.Modules.pullback g).map χ₂) :
    (Scheme.Modules.pullback (f ≫ g)).map χ₁ = (Scheme.Modules.pullback (f ≫ g)).map χ₂ :=
  map_eq_of_natIso (Scheme.Modules.pullbackComp f g)
    (show (Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback f).map χ₁ = _ by
      dsimp only [Functor.comp_map]; rw [h])

/-! ### Restriction to an open subscheme -/

/-- The restriction of a sheaf of modules of finite presentation to an open subscheme is of
finite presentation. -/
theorem isFinitePresentation_restrict {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (F : Y.Modules) [F.IsFinitePresentation] :
    (Scheme.Modules.restrict F f).IsFinitePresentation :=
  let g : X.toRingedSpace ⟶ Y.toRingedSpace := f.toLRSHom.toShHom
  (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback f).app F).symm
    (@Stacks.SheafOfModules.modulePullback_isFinitePresentation _ _ g F ‹_›)

/-- Restriction of sections along an inclusion of opens commutes with a morphism of sheaves of
modules, elementwise. -/
theorem Hom_app_presheaf_map {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N) {U V : X.Opens}
    (hV : V ≤ U) (m : Γ(M, U)) :
    N.presheaf.map (homOfLE hV).op (φ.app U m) =
      φ.app V (M.presheaf.map (homOfLE hV).op m) := by
  simpa using (congrArg (fun k => (ConcreteCategory.hom k) m)
    (φ.mapPresheaf.naturality (homOfLE hV).op)).symm

/-- The image of an open contained in `W` under the inclusion of `W` is that open. -/
theorem image_preimage_of_le {X : Scheme.{u}} {W V : X.Opens} (h : V ≤ W) :
    W.ι ''ᵁ (W.ι ⁻¹ᵁ V) = V := by
  ext x
  simp only [Scheme.Hom.coe_image, TopologicalSpace.Opens.map_coe, Set.mem_image,
    Set.mem_preimage, SetLike.mem_coe]
  exact ⟨fun ⟨y, hy, hyx⟩ => hyx ▸ hy, fun hx => ⟨⟨x, h hx⟩, hx, rfl⟩⟩

/-- Two morphisms of sheaves of modules on a scheme are equal as soon as their restrictions to
the members of an open covering agree. -/
theorem hom_ext_of_restrict_cover {X : Scheme.{u}} {M N : X.Modules} {φ ψ : M ⟶ N}
    {ι : Type*} (W : ι → X.Opens) (hW : ∀ x : X, ∃ a, x ∈ W a)
    (h : ∀ a, (Scheme.Modules.restrictFunctor (W a).ι).map φ =
      (Scheme.Modules.restrictFunctor (W a).ι).map ψ) : φ = ψ := by
  have key : ∀ (a : ι) (V : X.Opens), V ≤ W a → φ.app V = ψ.app V := fun a V hV ↦ by
    have h₁ : φ.app ((W a).ι ''ᵁ ((W a).ι ⁻¹ᵁ V)) = ψ.app ((W a).ι ''ᵁ ((W a).ι ⁻¹ᵁ V)) :=
      congrArg (fun k => Scheme.Modules.Hom.app k ((W a).ι ⁻¹ᵁ V)) (h a)
    rwa [image_preimage_of_le hV] at h₁
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  ext m
  refine N.isSheaf.section_ext (U := op U) fun x hx ↦ ?_
  obtain ⟨a, ha⟩ := hW x
  refine ⟨U ⊓ W a, inf_le_left, ⟨hx, ha⟩, ?_⟩
  rw [Hom_app_presheaf_map φ inf_le_left m, Hom_app_presheaf_map ψ inf_le_left m,
    key a (U ⊓ W a) inf_le_right]

/-- Equality of the pullbacks of two morphisms along `f` can be tested after restricting to the
preimage of an open, as equality of pullbacks of the restrictions. -/
private theorem restrict_pullback_map_eq_iff {X Y : Scheme.{u}} (f : X ⟶ Y) {U U' : Y.Opens}
    (hU : U ≤ U') {F G : Y.Modules} (ψ₁ ψ₂ : F ⟶ G) :
    (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map ((Scheme.Modules.pullback f).map ψ₁) =
        (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map ((Scheme.Modules.pullback f).map ψ₂) ↔
      (Scheme.Modules.pullback (f.resLE U' (f ⁻¹ᵁ U) (Scheme.Hom.preimage_mono _ hU))).map
          ((Scheme.Modules.restrictFunctor U'.ι).map ψ₁) =
        (Scheme.Modules.pullback (f.resLE U' (f ⁻¹ᵁ U) (Scheme.Hom.preimage_mono _ hU))).map
          ((Scheme.Modules.restrictFunctor U'.ι).map ψ₂) :=
  ⟨map_eq_of_natIso (Stacks.Modules.restrictPullbackIso f _),
    map_eq_of_natIso (Stacks.Modules.restrictPullbackIso f _).symm⟩

/-! ### Tag 01ZR (3) in the general case -/

section

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
  [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] (c : Cone D)

/-- If the pullbacks of `ψ₁` and `ψ₂` to the limit agree, then for an affine open `V` of the
stage `D.obj i` there is an index over `i` from which on the pullbacks of the restrictions of
`ψ₁` and `ψ₂` to the preimage of `V` agree. -/
private theorem exists_over_pullback_restrict_map_eq (hc : IsLimit c) (i : I)
    {V : (D.obj i).Opens} (hV : IsAffineOpen V)
    (F G : (D.obj i).Modules) [F.IsFinitePresentation] [G.IsFinitePresentation]
    (ψ₁ ψ₂ : F ⟶ G)
    (h : (Scheme.Modules.pullback (c.π.app i)).map ψ₁ =
      (Scheme.Modules.pullback (c.π.app i)).map ψ₂) :
    ∃ j : Over i, ∀ (k : Over i), (k ⟶ j) →
      (Scheme.Modules.pullback ((EventualLimit.preimageDiagram D i V).map
          (Over.homMk k.hom (by simp) : k ⟶ Over.mk (𝟙 i)))).map
          ((Scheme.Modules.restrictFunctor (D.map (𝟙 i) ⁻¹ᵁ V).ι).map ψ₁) =
      (Scheme.Modules.pullback ((EventualLimit.preimageDiagram D i V).map
          (Over.homMk k.hom (by simp) : k ⟶ Over.mk (𝟙 i)))).map
          ((Scheme.Modules.restrictFunctor (D.map (𝟙 i) ⁻¹ᵁ V).ι).map ψ₂) := by
  have haff : ∀ k : Over i, IsAffine ((EventualLimit.preimageDiagram D i V).obj k) :=
    EventualLimit.isAffine_preimageDiagram_obj D i hV
  have hdl : IsLimit (EventualLimit.preimageCone D c i V) :=
    EventualLimit.isLimitPreimageCone D c hc i V
  have hVW : V ≤ D.map (𝟙 i) ⁻¹ᵁ V := by simp
  have hFfp : ((Scheme.Modules.restrictFunctor (D.map (𝟙 i) ⁻¹ᵁ V).ι).obj
      F).IsFinitePresentation := isFinitePresentation_restrict _ F
  have hGfp : ((Scheme.Modules.restrictFunctor (D.map (𝟙 i) ⁻¹ᵁ V).ι).obj
      G).IsFinitePresentation := isFinitePresentation_restrict _ G
  have hres : (Scheme.Modules.pullback
        ((EventualLimit.preimageCone D c i V).π.app (Over.mk (𝟙 i)))).map
        ((Scheme.Modules.restrictFunctor (D.map (𝟙 i) ⁻¹ᵁ V).ι).map ψ₁) =
      (Scheme.Modules.pullback
        ((EventualLimit.preimageCone D c i V).π.app (Over.mk (𝟙 i)))).map
        ((Scheme.Modules.restrictFunctor (D.map (𝟙 i) ⁻¹ᵁ V).ι).map ψ₂) := by
    exact (restrict_pullback_map_eq_iff (c.π.app i) hVW ψ₁ ψ₂).1 (by rw [h])
  obtain ⟨j, e, hje⟩ := @exists_pullback_map_eq_of_isAffine' _ _ _
    (EventualLimit.preimageDiagram D i V) (EventualLimit.preimageCone D c i V) haff hdl
    (Over.mk (𝟙 i)) _ _ hFfp hGfp _ _ hres
  refine ⟨j, fun k m => ?_⟩
  have hcomp : (m ≫ e) = (Over.homMk k.hom (by simp) : k ⟶ Over.mk (𝟙 i)) :=
    Over.OverMorphism.ext (by simpa using Over.w (m ≫ e))
  rw [← hcomp, Functor.map_comp]
  exact pullback_map_eq_of_precomp _ _ hje

/-- Let `c` be a limit cone on a cofiltered diagram `D` of
schemes with affine transition morphisms and let `ψ₁, ψ₂ : F ⟶ G` be morphisms of sheaves of
modules of finite presentation on a quasi-compact stage `D.obj i`.  If the pullbacks of `ψ₁` and
`ψ₂` to `c.pt` agree, then their pullbacks to `D.obj j` agree for some `j` over `i`. -/
@[stacks 01ZR "eventual_equality"]
theorem exists_pullback_map_eq_of_isLimit (hc : IsLimit c) (i : I) [CompactSpace (D.obj i)]
    (F G : (D.obj i).Modules) [F.IsFinitePresentation] [G.IsFinitePresentation]
    (ψ₁ ψ₂ : F ⟶ G)
    (h : (Scheme.Modules.pullback (c.π.app i)).map ψ₁ =
      (Scheme.Modules.pullback (c.π.app i)).map ψ₂) :
    ∃ (j : I) (e : j ⟶ i),
      (Scheme.Modules.pullback (D.map e)).map ψ₁ =
        (Scheme.Modules.pullback (D.map e)).map ψ₂ := by
  classical
  let 𝒰 := (D.obj i).affineCover.finiteSubcover
  let V : 𝒰.I₀ → (D.obj i).Opens := fun a => (𝒰.f a).opensRange
  have hVa : ∀ a, IsAffineOpen (V a) := fun a => isAffineOpen_opensRange _
  have hcov : ∀ x : D.obj i, ∃ a, x ∈ V a := fun x =>
    𝒰.isOpenCover_opensRange.exists_mem x
  choose jj hjj using fun a =>
    exists_over_pullback_restrict_map_eq D c hc i (hVa a) F G ψ₁ ψ₂ h
  obtain ⟨k, hk⟩ := IsCofiltered.inf_objs_exists (Finset.image jj Finset.univ)
  have hkm : ∀ a, k ⟶ jj a := fun a =>
    (hk (Finset.mem_image_of_mem _ (Finset.mem_univ a))).some
  refine ⟨k.left, k.hom, ?_⟩
  refine hom_ext_of_restrict_cover (fun a => D.map k.hom ⁻¹ᵁ V a) (fun x => ?_) (fun a => ?_)
  · exact hcov ((D.map k.hom).base x)
  · exact (restrict_pullback_map_eq_iff (D.map k.hom) (by simp) ψ₁ ψ₂).2 (hjj a k (hkm a))

end

/-! ### The index morphism universe -/

section IndexHomUniverse

open CategoryTheory.Functor CategoryTheory.Functor.FullImage

variable {I : Type u} [Category.{v} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
  [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] (c : Cone D)

include c in
/-- For a cofiltered diagram of schemes with affine transition morphisms, indexed by a category
whose morphisms live in any universe, two morphisms of sheaves of modules of finite presentation
on a quasi-compact stage whose pullbacks to the limit agree already have equal pullbacks to a
later stage. -/
theorem exists_pullback_map_eq_of_isLimit' (hc : IsLimit c) (i : I) [CompactSpace (D.obj i)]
    (F G : (D.obj i).Modules) [F.IsFinitePresentation] [G.IsFinitePresentation]
    (ψ₁ ψ₂ : F ⟶ G)
    (h : (Scheme.Modules.pullback (c.π.app i)).map ψ₁ =
      (Scheme.Modules.pullback (c.π.app i)).map ψ₂) :
    ∃ (j : I) (e : j ⟶ i),
      (Scheme.Modules.pullback (D.map e)).map ψ₁ =
        (Scheme.Modules.pullback (D.map e)).map ψ₂ := by
  obtain ⟨j, gm, hj⟩ :=
    @exists_pullback_map_eq_of_isLimit (FullImage D) _ _ (ι D) _ (cone D c) (isLimitCone D hc)
      ⟨i⟩ ‹_› F G ‹_› ‹_› ψ₁ ψ₂ h
  refine ⟨j.as, hom D gm, ?_⟩
  rwa [map_hom D gm]

end IndexHomUniverse

end Stacks.AlgebraicGeometry.ModuleLimits

end
