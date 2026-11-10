module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictHenselizationBoundedIndex
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictHenselizationConeBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.RelativelyPureModules
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.SpecStalkAffineNhdsSystem

/-!
# An impurity over the strict henselization descends to an étale neighbourhood

In Situation 0CV6, let `a : V ⟶ Y` be an étale chart of the target, `v̄` a geometric point of `V`
and `Y^{sh} = Spec 𝒪_{V, v̄}^{sh}` the strict henselization, realized as a test scheme `T` of the
site together with its canonical morphism to `V`. An impurity of `F` above `y` with test scheme
`T` over `Y` gives an impurity whose structure morphism is étale, and hence one whose structure
morphism is quasi-finite at its specialized point. This is the implication (1) ⟹ (3) of
Stacks 0CVB, and with (3) ⟹ (4) its implication (1) ⟹ (4).

## Main results

* `AlgebraicGeometry.Space.exists_affineLimitPresentation_strictHenselization`: the test scheme
  `T` is the limit, inside the site, of a bounded system of affine étale neighbourhoods of `v̄`,
  each étale over `Y`.
* `AlgebraicGeometry.Space.exists_isImpurity_isEtale_of_isImpurity_strictHenselization`:
  (1) ⟹ (3) for a given realization of the strict henselization.
* `AlgebraicGeometry.Space.exists_isImpurity_isQuasiFiniteAt_of_isImpurity_strictHenselization`:
  (1) ⟹ (4) for a given realization. The registration of Stacks 0CVB, on the strict
  henselization built from `(Y, ȳ)`, is in
  `StacksFrontier/AlgebraicGeometry/Spaces/Flat/StrictHenselizationConditions.lean`.

## Implementation notes

The source writes `Y^{sh} = lim V` over the affine étale neighbourhoods of `ȳ` and applies
Stacks 0CV9. Inside the size-bounded site the limit-descent route needs a cardinality clause,
`AlgebraicGeometry.Space.SiteLimitBound`. The source's own bookkeeping, by the cofinality of the
cutoff, is not available for this system, and its transition morphisms are not monomorphisms.
What it does satisfy is the third package of that clause: the bounded family
`AlgebraicGeometry.EtaleNeighborhoodBounded` of the module
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictHenselizationBoundedIndex`
has fewer members than the cutoff, its morphism types and its stages are bounded by one cardinal
below the cutoff, and it is initial among the étale neighbourhoods, so the strict henselization
is still its limit.

The realization of `Y^{sh}` is given as in the statement of Stacks 0CVB: a test scheme `T`,
a morphism `ψ : T ⟶ V` of the site, and an isomorphism of the scheme underlying `T` with
`AlgebraicGeometry.strictHenselization` under which `ψ` is
`AlgebraicGeometry.strictHenselizationToBase`. The field of the geometric point is asked to be
small for the site, as it is for the geometric point a geometric point of `Y` induces on a chart.

## References

* [Stacks Project, Tag 0CVB](https://stacks.math.columbia.edu/tag/0CVB)
* [Stacks Project, Tag 0CV9](https://stacks.math.columbia.edu/tag/0CV9)
* [Stacks Project, Tag 04HX](https://stacks.math.columbia.edu/tag/04HX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- For a strong prelimit cardinal `κ > ℵ₀`, a power of two cardinals below `κ` is below `κ`. -/
theorem power_lt_of_isStrongPrelimit {κ a b : Cardinal.{u}} (hκ : ℵ₀ < κ)
    (hsl : κ.IsStrongPrelimit) (ha : a < κ) (hb : b < κ) : a ^ b < κ :=
  calc a ^ b ≤ (2 ^ a) ^ b := Cardinal.power_le_power_right (Cardinal.cantor a).le
    _ = 2 ^ (a * b) := Cardinal.power_mul.symm
    _ < κ := hsl (Cardinal.mul_lt_of_lt hκ.le ha hb)

/-- The structure morphism of the source of a morphism of the site factors through it. -/
private theorem inclusion_map_hom_eq_toScheme_map_comp {T T' : BigFppfOver B S hS} (ψ : T ⟶ T') :
    B.inclusion.map T.hom = (BigFppfOver.toScheme B S hS).map ψ ≫ B.inclusion.map T'.hom :=
  (congrArg B.inclusion.map (Over.w ψ)).symm.trans (B.inclusion.map_comp _ _)

section System

variable (V : BigFppfOver B S hS) (E : BigEtaleSite.{u})
  (hV : E.Contains ((BigFppfOver.toScheme B S hS).obj V))
  (v : _root_.AlgebraicGeometry.GeometricPoint ((BigFppfOver.toScheme B S hS).obj V))
  {R : CommRingCat.{u}} (ι₀ : Spec R ⟶ (BigFppfOver.toScheme B S hS).obj V)
  [_root_.AlgebraicGeometry.IsOpenImmersion ι₀]

/-- The diagram of schemes of the bounded family of affine étale neighbourhoods of `v`. -/
abbrev shSchemeDiagram : EtaleNeighborhoodBounded E hV v ι₀ ⥤ Scheme.{u} :=
  etaleNeighborhoodBoundedFunctor E hV v ι₀ ⋙ etaleNeighborhoodDiagram E _ hV v

/-- The structure morphism of a member of the bounded family to the chart. -/
abbrev shSchemeProj (j : EtaleNeighborhoodBounded E hV v ι₀) :
    (shSchemeDiagram V E hV v ι₀).obj j ⟶ (BigFppfOver.toScheme B S hS).obj V :=
  E.inclusion.map ((etaleNeighborhoodBoundedFunctor E hV v ι₀).obj j).1.obj.hom

/-- The structure morphisms to the chart are compatible with the transition morphisms. -/
theorem shSchemeDiagram_map_comp_proj {j j' : EtaleNeighborhoodBounded E hV v ι₀}
    (f : j ⟶ j') :
    (shSchemeDiagram V E hV v ι₀).map f ≫ shSchemeProj V E hV v ι₀ j' =
      shSchemeProj V E hV v ι₀ j :=
  (E.inclusion.map_comp _ _).symm.trans (congrArg E.inclusion.map (Over.w
    ((_root_.AlgebraicGeometry.SmallEtale.inclusion E _ hV).map
      ((etaleNeighborhoodBoundedFunctor E hV v ι₀).map f).1)))

/-- A member of the bounded family lies in the big fppf site. -/
theorem contains_shSchemeDiagram_obj (j : EtaleNeighborhoodBounded E hV v ι₀) :
    B.Contains ((shSchemeDiagram V E hV v ι₀).obj j) :=
  (size_spec_boundedPresRing_le ι₀ j.1.1).trans_lt V.left.property

/-- A member of the bounded family, as an object of the site. -/
abbrev shStage (j : EtaleNeighborhoodBounded E hV v ι₀) : BigFppfOver B S hS :=
  BigFppfOver.mk B S hS (contains_shSchemeDiagram_obj V E hV v ι₀ j)
    (shSchemeProj V E hV v ι₀ j ≫ B.inclusion.map V.hom)

/-- The scheme underlying a member of the bounded family, read as an object of the site. -/
theorem toScheme_obj_shStage (j : EtaleNeighborhoodBounded E hV v ι₀) :
    (BigFppfOver.toScheme B S hS).obj (shStage V E hV v ι₀ j) =
      (shSchemeDiagram V E hV v ι₀).obj j := rfl

/-- A transition morphism of the bounded family, read on the objects of the site. -/
abbrev shStageSchemeMap {j j' : EtaleNeighborhoodBounded E hV v ι₀} (f : j ⟶ j') :
    (BigFppfOver.toScheme B S hS).obj (shStage V E hV v ι₀ j) ⟶
      (BigFppfOver.toScheme B S hS).obj (shStage V E hV v ι₀ j') :=
  show (shSchemeDiagram V E hV v ι₀).obj j ⟶ (shSchemeDiagram V E hV v ι₀).obj j' from
    (shSchemeDiagram V E hV v ι₀).map f

/-- The structure morphism of a member of the bounded family to the chart, read on the object
of the site. -/
abbrev shStageSchemeProj (j : EtaleNeighborhoodBounded E hV v ι₀) :
    (BigFppfOver.toScheme B S hS).obj (shStage V E hV v ι₀ j) ⟶
      (BigFppfOver.toScheme B S hS).obj V :=
  show (shSchemeDiagram V E hV v ι₀).obj j ⟶ (BigFppfOver.toScheme B S hS).obj V from
    shSchemeProj V E hV v ι₀ j

/-- **The bounded family of affine étale neighbourhoods of `v`, as a system of the site.** -/
def shStageFunctor : EtaleNeighborhoodBounded E hV v ι₀ ⥤ BigFppfOver B S hS where
  obj j := shStage V E hV v ι₀ j
  map f := siteHomMk B S hS (shStageSchemeMap V E hV v ι₀ f) (by
    change (shSchemeDiagram V E hV v ι₀).map f ≫ (shSchemeProj V E hV v ι₀ _ ≫
      B.inclusion.map V.hom) = shSchemeProj V E hV v ι₀ _ ≫ B.inclusion.map V.hom
    rw [← Category.assoc, shSchemeDiagram_map_comp_proj])
  map_id j := hom_ext_toScheme B S hS ((shSchemeDiagram V E hV v ι₀).map_id j)
  map_comp f g := hom_ext_toScheme B S hS ((shSchemeDiagram V E hV v ι₀).map_comp f g)

/-- The morphism of schemes underlying a transition morphism of the system. -/
theorem toScheme_map_shStageFunctor_map {j j' : EtaleNeighborhoodBounded E hV v ι₀}
    (f : j ⟶ j') :
    (BigFppfOver.toScheme B S hS).map ((shStageFunctor V E hV v ι₀).map f) =
      shStageSchemeMap V E hV v ι₀ f := rfl

/-- The morphism of a stage of the system to the chart. -/
def shStageHom (j : EtaleNeighborhoodBounded E hV v ι₀) :
    (shStageFunctor V E hV v ι₀).obj j ⟶ V :=
  siteHomMk B S hS (shStageSchemeProj V E hV v ι₀ j) rfl

/-- The morphism of schemes underlying the morphism of a stage to the chart. -/
theorem toScheme_map_shStageHom (j : EtaleNeighborhoodBounded E hV v ι₀) :
    (BigFppfOver.toScheme B S hS).map (shStageHom V E hV v ι₀ j) =
      shStageSchemeProj V E hV v ι₀ j := rfl

/-- The morphisms of the stages of the system to the chart commute with the transition
morphisms. -/
theorem shStageFunctor_map_comp_shStageHom {j j' : EtaleNeighborhoodBounded E hV v ι₀}
    (f : j ⟶ j') :
    (shStageFunctor V E hV v ι₀).map f ≫ shStageHom V E hV v ι₀ j' =
      shStageHom V E hV v ι₀ j :=
  hom_ext_toScheme B S hS (((BigFppfOver.toScheme B S hS).map_comp _ _).trans
    (shSchemeDiagram_map_comp_proj V E hV v ι₀ f))

/-- The morphism of a stage to the chart is étale. -/
theorem etale_toScheme_map_shStageHom (j : EtaleNeighborhoodBounded E hV v ι₀) :
    Etale ((BigFppfOver.toScheme B S hS).map (shStageHom V E hV v ι₀ j)) :=
  show Etale (shSchemeProj V E hV v ι₀ j) from
    ((etaleNeighborhoodBoundedFunctor E hV v ι₀).obj j).1.property

example : (strictHenselizationBoundedCone E hV v ι₀).pt =
    _root_.AlgebraicGeometry.strictHenselization E _ hV v := rfl

/-- For a realization `e` of the strict henselization over `ψ`, the legs of the cone followed by
the structure morphisms are `ψ`. -/
private theorem strictHenselizationBoundedCone_π_app_comp_shSchemeProj {T : BigFppfOver B S hS}
    (ψ : T ⟶ V)
    (e : (BigFppfOver.toScheme B S hS).obj T ≅ (strictHenselizationBoundedCone E hV v ι₀).pt)
    (he : (BigFppfOver.toScheme B S hS).map ψ =
      e.hom ≫ _root_.AlgebraicGeometry.strictHenselizationToBase E _ hV v)
    (j : EtaleNeighborhoodBounded E hV v ι₀) :
    e.hom ≫ (strictHenselizationBoundedCone E hV v ι₀).π.app j ≫ shSchemeProj V E hV v ι₀ j =
      (BigFppfOver.toScheme B S hS).map ψ := by
  have h1 : (strictHenselizationBoundedCone E hV v ι₀).π.app j ≫ shSchemeProj V E hV v ι₀ j =
      strictHenselizationConeToBase E _ hV v :=
    strictHenselizationCone_π_comp_hom E _ hV v _
  refine (congrArg (e.hom ≫ ·) h1).trans ?_
  rw [strictHenselizationConeToBase_eq, he]

/-- The structure morphism of a realization of the strict henselization factors through each leg
of the cone and the structure morphism of the stage. -/
private theorem inclusion_map_hom_eq_cone_leg_comp {T : BigFppfOver B S hS} (ψ : T ⟶ V)
    (e : (BigFppfOver.toScheme B S hS).obj T ≅ (strictHenselizationBoundedCone E hV v ι₀).pt)
    (he : (BigFppfOver.toScheme B S hS).map ψ =
      e.hom ≫ _root_.AlgebraicGeometry.strictHenselizationToBase E _ hV v)
    (j : EtaleNeighborhoodBounded E hV v ι₀) :
    B.inclusion.map T.hom = (e.hom ≫ (strictHenselizationBoundedCone E hV v ι₀).π.app j) ≫
      (shSchemeProj V E hV v ι₀ j ≫ B.inclusion.map V.hom) := by
  rw [inclusion_map_hom_eq_toScheme_map_comp ψ,
    ← strictHenselizationBoundedCone_π_app_comp_shSchemeProj V E hV v ι₀ ψ e he j]
  simp only [Category.assoc]

/-- The morphisms from a realization of the strict henselization to the stages of the system. -/
private def shStageConeProj {T : BigFppfOver B S hS} (ψ : T ⟶ V)
    (e : (BigFppfOver.toScheme B S hS).obj T ≅ (strictHenselizationBoundedCone E hV v ι₀).pt)
    (he : (BigFppfOver.toScheme B S hS).map ψ =
      e.hom ≫ _root_.AlgebraicGeometry.strictHenselizationToBase E _ hV v)
    (j : EtaleNeighborhoodBounded E hV v ι₀) : T ⟶ (shStageFunctor V E hV v ι₀).obj j :=
  siteHomMk B S hS (show (BigFppfOver.toScheme B S hS).obj T ⟶
    (shSchemeDiagram V E hV v ι₀).obj j from
      e.hom ≫ (strictHenselizationBoundedCone E hV v ι₀).π.app j) (by
    exact (inclusion_map_hom_eq_cone_leg_comp V E hV v ι₀ ψ e he j).symm)

/-- The morphisms from a realization of the strict henselization to the stages lie over `ψ`. -/
private theorem shStageConeProj_comp_shStageHom {T : BigFppfOver B S hS} (ψ : T ⟶ V)
    (e : (BigFppfOver.toScheme B S hS).obj T ≅ (strictHenselizationBoundedCone E hV v ι₀).pt)
    (he : (BigFppfOver.toScheme B S hS).map ψ =
      e.hom ≫ _root_.AlgebraicGeometry.strictHenselizationToBase E _ hV v)
    (j : EtaleNeighborhoodBounded E hV v ι₀) :
    shStageConeProj V E hV v ι₀ ψ e he j ≫ shStageHom V E hV v ι₀ j = ψ :=
  hom_ext_toScheme B S hS (((BigFppfOver.toScheme B S hS).map_comp _ _).trans
    ((Category.assoc _ _ _).trans
      (strictHenselizationBoundedCone_π_app_comp_shSchemeProj V E hV v ι₀ ψ e he j)))

/-- The morphisms from a realization of the strict henselization to the stages commute with the
transition morphisms. -/
private theorem shStageConeProj_comp_map {T : BigFppfOver B S hS} (ψ : T ⟶ V)
    (e : (BigFppfOver.toScheme B S hS).obj T ≅ (strictHenselizationBoundedCone E hV v ι₀).pt)
    (he : (BigFppfOver.toScheme B S hS).map ψ =
      e.hom ≫ _root_.AlgebraicGeometry.strictHenselizationToBase E _ hV v)
    {i j : EtaleNeighborhoodBounded E hV v ι₀} (f : i ⟶ j) :
    shStageConeProj V E hV v ι₀ ψ e he i ≫ (shStageFunctor V E hV v ι₀).map f =
      shStageConeProj V E hV v ι₀ ψ e he j :=
  hom_ext_toScheme B S hS (((BigFppfOver.toScheme B S hS).map_comp _ _).trans
    ((Category.assoc _ _ _).trans
      (congrArg (e.hom ≫ ·) ((strictHenselizationBoundedCone E hV v ι₀).w f))))

/-- The cone over the system given by a realization of the strict henselization. -/
private def shStageCone {T : BigFppfOver B S hS} (ψ : T ⟶ V)
    (e : (BigFppfOver.toScheme B S hS).obj T ≅ (strictHenselizationBoundedCone E hV v ι₀).pt)
    (he : (BigFppfOver.toScheme B S hS).map ψ =
      e.hom ≫ _root_.AlgebraicGeometry.strictHenselizationToBase E _ hV v) :
    Cone (shStageFunctor V E hV v ι₀) where
  pt := T
  π :=
    { app := shStageConeProj V E hV v ι₀ ψ e he
      naturality := fun _ _ f ↦
        (Category.id_comp _).trans (shStageConeProj_comp_map V E hV v ι₀ ψ e he f).symm }

/-- **A realization of the strict henselization is the limit of the system inside the site.** -/
private def shStageConeIsLimit {T : BigFppfOver B S hS} (ψ : T ⟶ V)
    (e : (BigFppfOver.toScheme B S hS).obj T ≅ (strictHenselizationBoundedCone E hV v ι₀).pt)
    (he : (BigFppfOver.toScheme B S hS).map ψ =
      e.hom ≫ _root_.AlgebraicGeometry.strictHenselizationToBase E _ hV v)
    (s₀ : v.source ⟶ Spec R) (hs₀ : s₀ ≫ ι₀ = v.hom) :
    IsLimit (shStageCone V E hV v ι₀ ψ e he) := by
  have := isCofiltered_etaleNeighborhoodBounded E hV s₀ hs₀
  refine IsLimit.ofExistsUnique fun s ↦ ?_
  obtain ⟨j₀⟩ := IsCofiltered.nonempty (C := EtaleNeighborhoodBounded E hV v ι₀)
  have hL : IsLimit ((strictHenselizationBoundedCone E hV v ι₀).extend e.hom) :=
    IsLimit.extendIso (s := strictHenselizationBoundedCone E hV v ι₀) e.hom
      (strictHenselizationBoundedConeIsLimit E hV s₀ hs₀)
  let c' : Cone (shSchemeDiagram V E hV v ι₀) :=
    { pt := (BigFppfOver.toScheme B S hS).obj s.pt
      π :=
        { app := fun j ↦ show (BigFppfOver.toScheme B S hS).obj s.pt ⟶
            (shSchemeDiagram V E hV v ι₀).obj j from (BigFppfOver.toScheme B S hS).map (s.π.app j)
          naturality := fun i j f ↦ (Category.id_comp _).trans
            ((congrArg (BigFppfOver.toScheme B S hS).map (s.w f)).symm.trans
              ((BigFppfOver.toScheme B S hS).map_comp _ _)) } }
  have h1 : ∀ j, hL.lift c' ≫ e.hom ≫ (strictHenselizationBoundedCone E hV v ι₀).π.app j =
      (BigFppfOver.toScheme B S hS).map (s.π.app j) :=
    fun j ↦ hL.fac c' j
  have hover : hL.lift c' ≫ B.inclusion.map T.hom = B.inclusion.map s.pt.hom := by
    rw [inclusion_map_hom_eq_cone_leg_comp V E hV v ι₀ ψ e he j₀]
    simp only [Category.assoc]
    rw [reassoc_of% (h1 j₀)]
    exact (inclusion_map_hom_eq_toScheme_map_comp (s.π.app j₀)).symm
  refine ⟨siteHomMk B S hS (hL.lift c') hover, fun j ↦ hom_ext_toScheme B S hS ?_,
    fun l' hl' ↦ hom_ext_toScheme B S hS ?_⟩
  · exact ((BigFppfOver.toScheme B S hS).map_comp _ _).trans (h1 j)
  · refine hL.hom_ext fun j ↦ ?_
    change (BigFppfOver.toScheme B S hS).map l' ≫ e.hom ≫
        (strictHenselizationBoundedCone E hV v ι₀).π.app j =
      hL.lift c' ≫ e.hom ≫ (strictHenselizationBoundedCone E hV v ι₀).π.app j
    rw [h1 j, ← hl' j, Functor.map_comp]
    rfl

end System

/-- Every geometric point of a scheme factors through an affine open. -/
theorem exists_affine_open_geometricPoint {X : Scheme.{u}}
    (v : _root_.AlgebraicGeometry.GeometricPoint X) :
    ∃ (R : CommRingCat.{u}) (ι₀ : Spec R ⟶ X) (_ : _root_.AlgebraicGeometry.IsOpenImmersion ι₀)
      (s₀ : v.source ⟶ Spec R), s₀ ≫ ι₀ = v.hom := by
  obtain ⟨R, ι₀, hι₀, hmem, -⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (x := v.hom (default : v.source)) (U := ⊤) trivial
  have hrange : Set.range v.hom ⊆ Set.range ι₀ := by
    rintro _ ⟨b, rfl⟩
    rwa [Subsingleton.elim b default]
  exact ⟨R, ι₀, hι₀, IsOpenImmersion.lift ι₀ v.hom hrange, IsOpenImmersion.lift_fac _ _ _⟩

/-- The ring of an affine open of an object of the site is below the cutoff. -/
private theorem max_aleph0_mk_lt_cutoff (V : BigFppfOver B S hS) {R : CommRingCat.{u}}
    (ι₀ : Spec R ⟶ (BigFppfOver.toScheme B S hS).obj V)
    [_root_.AlgebraicGeometry.IsOpenImmersion ι₀] : max ℵ₀ #R < B.cutoff := by
  have hRle : max ℵ₀ #R ≤ ((BigFppfOver.toScheme B S hS).obj V).size := by
    rw [← Scheme.size_Spec]
    exact Scheme.size_le_of_isOpenImmersion ι₀
  exact hRle.trans_lt V.left.property

/-- **The bounded family of affine étale neighbourhoods of a geometric point of an object of the
site has fewer members than the cutoff**, provided the field of the point is small for the
site. -/
theorem mk_etaleNeighborhoodBounded_lt (V : BigFppfOver B S hS) (E : BigEtaleSite.{u})
    (hV : E.Contains ((BigFppfOver.toScheme B S hS).obj V))
    (v : _root_.AlgebraicGeometry.GeometricPoint ((BigFppfOver.toScheme B S hS).obj V))
    (hv : B.Contains (Spec (.of v.residueField))) {R : CommRingCat.{u}}
    (ι₀ : Spec R ⟶ (BigFppfOver.toScheme B S hS).obj V)
    [_root_.AlgebraicGeometry.IsOpenImmersion ι₀] :
    #(EtaleNeighborhoodBounded E hV v ι₀) < B.cutoff := by
  have hm := max_aleph0_mk_lt_cutoff V ι₀
  have hk : #v.residueField < B.cutoff :=
    ((le_max_right _ _).trans (Scheme.size_Spec (.of v.residueField)).ge).trans_lt hv
  exact (mk_etaleNeighborhoodBoundedIndex_le v ι₀).trans_lt
    (Cardinal.mul_lt_of_lt B.aleph0_lt_cutoff.le (B.cutoff_isStrongPrelimit hm)
      (power_lt_of_isStrongPrelimit B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit hk hm))

/-- The bounded family of affine étale neighbourhoods of a geometric point, as a system of the
site, satisfies the third package of the cardinality clause. -/
private theorem siteLimitBound_shStageFunctor (V : BigFppfOver B S hS) (E : BigEtaleSite.{u})
    (hV : E.Contains ((BigFppfOver.toScheme B S hS).obj V))
    (v : _root_.AlgebraicGeometry.GeometricPoint ((BigFppfOver.toScheme B S hS).obj V))
    (hv : B.Contains (Spec (.of v.residueField))) {R : CommRingCat.{u}}
    (ι₀ : Spec R ⟶ (BigFppfOver.toScheme B S hS).obj V)
    [_root_.AlgebraicGeometry.IsOpenImmersion ι₀] :
    SiteLimitBound (shStageFunctor V E hV v ι₀) :=
  Or.inr (Or.inr ⟨mk_etaleNeighborhoodBounded_lt V E hV v hv ι₀, _,
    power_lt_of_isStrongPrelimit B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
      (max_aleph0_mk_lt_cutoff V ι₀) (max_aleph0_mk_lt_cutoff V ι₀),
    mk_hom_etaleNeighborhoodBounded_le E hV v ι₀,
    _, V.left.property, fun j ↦ size_spec_boundedPresRing_le ι₀ j.1.1⟩)

/-- **The strict henselization of an object of the site at a geometric point lies in the site**,
provided the field of the point does: it is the limit of the bounded family of affine étale
neighbourhoods, which has fewer members than the cutoff, all of size at most that of the
object. -/
theorem contains_strictHenselization (V : BigFppfOver B S hS) (E : BigEtaleSite.{u})
    (hV : E.Contains ((BigFppfOver.toScheme B S hS).obj V))
    (v : _root_.AlgebraicGeometry.GeometricPoint ((BigFppfOver.toScheme B S hS).obj V))
    (hv : B.Contains (Spec (.of v.residueField))) :
    B.Contains (_root_.AlgebraicGeometry.strictHenselization E _ hV v) := by
  obtain ⟨R, ι₀, hι₀, s₀, hs₀⟩ := exists_affine_open_geometricPoint v
  have := isCofiltered_etaleNeighborhoodBounded E hV s₀ hs₀
  have hpt : (strictHenselizationBoundedCone E hV v ι₀).pt =
      _root_.AlgebraicGeometry.strictHenselization E _ hV v := rfl
  rw [BigFppfSite.Contains, ← hpt]
  exact Scheme.size_lt_of_isLimit_of_isAffine_of_size_le B.aleph0_lt_cutoff
    (shSchemeDiagram V E hV v ι₀)
    (fun j ↦ inferInstanceAs (IsAffine (Spec (boundedPresRing j.1.1))))
    (mk_etaleNeighborhoodBounded_lt V E hV v hv ι₀) V.left.property
    (fun j ↦ size_spec_boundedPresRing_le ι₀ j.1.1)
    (strictHenselizationBoundedConeIsLimit E hV s₀ hs₀)

/-- **The strict henselization of an étale chart is the limit, inside the site, of a bounded
system of affine étale neighbourhoods, each étale over the target.** Let `D` be an impurity
diagram whose test scheme `T` is the strict henselization of a chart `a : V ⟶ Y` at a geometric
point `v`, in the sense that the scheme underlying `T` is identified with
`AlgebraicGeometry.strictHenselization` and `D.g` is the canonical morphism followed by `a`. Then
`D` carries an affine limit presentation, by the third package of
`AlgebraicGeometry.Space.SiteLimitBound`, each of whose structure morphisms to `Y` is a morphism
of the site étale over `V` followed by `a`. -/
theorem exists_affineLimitPresentation_strictHenselization
    {P : PrePureSituation.{u, u} B S hS} (D : ImpurityDiagram P)
    (V : BigFppfOver B S hS) (a : yoneda.obj V ⟶ P.Y) (E : BigEtaleSite.{u})
    (hV : E.Contains ((BigFppfOver.toScheme B S hS).obj V))
    (v : _root_.AlgebraicGeometry.GeometricPoint ((BigFppfOver.toScheme B S hS).obj V))
    (hv : B.Contains (Spec (.of v.residueField)))
    (ψ : D.T ⟶ V)
    (e : (BigFppfOver.toScheme B S hS).obj D.T ≅
      _root_.AlgebraicGeometry.strictHenselization E _ hV v)
    (he : (BigFppfOver.toScheme B S hS).map ψ =
      e.hom ≫ _root_.AlgebraicGeometry.strictHenselizationToBase E _ hV v)
    (hg : D.g = yoneda.map ψ ≫ a) :
    ∃ A : AffineLimitPresentation D, ∀ i, ∃ h : A.stage.obj i ⟶ V,
      A.base i = yoneda.map h ≫ a ∧ Etale ((BigFppfOver.toScheme B S hS).map h) := by
  classical
  -- an affine open of the chart through which the geometric point factors
  obtain ⟨R, ι₀, hι₀, s₀, hs₀⟩ := exists_affine_open_geometricPoint v
  have := isCofiltered_etaleNeighborhoodBounded E hV s₀ hs₀
  -- `e`, with its target read as the vertex of the cone: this is what keeps the unifier from
  -- unfolding the vertex when the cone is extended along it
  let e' : (BigFppfOver.toScheme B S hS).obj D.T ≅ (strictHenselizationBoundedCone E hV v ι₀).pt :=
    e
  have he' : (BigFppfOver.toScheme B S hS).map ψ =
      e'.hom ≫ _root_.AlgebraicGeometry.strictHenselizationToBase E _ hV v := he
  have ht := shStageConeIsLimit V E hV v ι₀ ψ e' he' s₀ hs₀
  refine ⟨{ J := EtaleNeighborhoodBounded E hV v ι₀
            stage := shStageFunctor V E hV v ι₀
            bound := siteLimitBound_shStageFunctor V E hV v hv ι₀
            isAffine := fun j ↦ inferInstanceAs (IsAffine (Spec (boundedPresRing j.1.1)))
            proj := shStageConeProj V E hV v ι₀ ψ e' he'
            proj_comp := shStageConeProj_comp_map V E hV v ι₀ ψ e' he'
            base := fun j ↦ yoneda.map (shStageHom V E hV v ι₀ j) ≫ a
            base_comp := fun f ↦ by
              rw [← Category.assoc, ← Functor.map_comp, shStageFunctor_map_comp_shStageHom]
            proj_base := fun j ↦ by
              rw [← Category.assoc, ← Functor.map_comp, shStageConeProj_comp_shStageHom, hg]
            isLimit := fun W m hm ↦ (isLimitOfPreserves yoneda ht).existsUnique
              { pt := W
                π :=
                  { app := m
                    naturality := fun _ _ f ↦ (Category.id_comp _).trans (hm f).symm } } },
    fun i ↦ ⟨shStageHom V E hV v ι₀ i, rfl, etale_toScheme_map_shStageHom V E hV v ι₀ i⟩⟩

/-- **The implication (1) ⟹ (3) of Stacks 0CVB, for a given realization of the strict
henselization.** Let `a : V ⟶ Y` be an étale chart of the target and `T` a test
scheme realizing the strict henselization `Spec 𝒪_{V, v}^{sh}` of the chart at a geometric point
`v`, over `Y` through the canonical morphism. An impurity of `F` above `y` with test scheme `T`
gives an impurity whose structure morphism is étale.

The source writes `Y^{sh} = lim V` over the affine étale neighbourhoods of the geometric point
and applies Stacks 0CV9. Here the limit is taken over the bounded family
`AlgebraicGeometry.EtaleNeighborhoodBounded`, presented by
`AlgebraicGeometry.Space.exists_affineLimitPresentation_strictHenselization`; every stage is étale
over `V`, hence over `Y`. -/
theorem exists_isImpurity_isEtale_of_isImpurity_strictHenselization
    {P : PrePureSituation.{u, u} B S hS} (D : ImpurityDiagram P)
    (V : BigFppfOver B S hS) (a : yoneda.obj V ⟶ P.Y) (ha : IsEtale B S hS a)
    (E : BigEtaleSite.{u}) (hV : E.Contains ((BigFppfOver.toScheme B S hS).obj V))
    (v : _root_.AlgebraicGeometry.GeometricPoint ((BigFppfOver.toScheme B S hS).obj V))
    (hv : B.Contains (Spec (.of v.residueField)))
    (ψ : D.T ⟶ V)
    (e : (BigFppfOver.toScheme B S hS).obj D.T ≅
      _root_.AlgebraicGeometry.strictHenselization E _ hV v)
    (he : (BigFppfOver.toScheme B S hS).map ψ =
      e.hom ≫ _root_.AlgebraicGeometry.strictHenselizationToBase E _ hV v)
    (hg : D.g = yoneda.map ψ ≫ a) (hD : D.IsImpurity) :
    ∃ D' : ImpurityDiagram P, IsEtale B S hS D'.g ∧ D'.IsImpurity := by
  obtain ⟨A, hA⟩ := exists_affineLimitPresentation_strictHenselization D V a E hV v hv ψ e he hg
  obtain ⟨i, hi⟩ := A.exists_isImpurity_stageDiagram hD
  obtain ⟨h, hb, het⟩ := hA i
  refine ⟨A.stageDiagram i, ?_, hi⟩
  rw [AffineLimitPresentation.stageDiagram_g, hb]
  exact isEtale_comp B S hS
    (isEtale_of_presheaf_etale B S hS ((presheaf_yoneda_map_etale_iff B S hS h).2 het)) ha

/-- **The implication (1) ⟹ (4) of Stacks 0CVB, for a given realization of the strict
henselization.** An impurity of `F` above `y` over the strict henselization of an étale chart,
realized as a test scheme, gives an impurity whose structure morphism is quasi-finite at its
specialized point: the implication (1) ⟹ (3) of
`AlgebraicGeometry.Space.exists_isImpurity_isEtale_of_isImpurity_strictHenselization`, followed
by (3) ⟹ (4),
`AlgebraicGeometry.Space.exists_isImpurity_isQuasiFiniteAt_of_exists_isImpurity_isEtale`. -/
theorem exists_isImpurity_isQuasiFiniteAt_of_isImpurity_strictHenselization
    {P : PrePureSituation.{u, u} B S hS} (D : ImpurityDiagram P)
    (V : BigFppfOver B S hS) (a : yoneda.obj V ⟶ P.Y) (ha : IsEtale B S hS a)
    (E : BigEtaleSite.{u}) (hV : E.Contains ((BigFppfOver.toScheme B S hS).obj V))
    (v : _root_.AlgebraicGeometry.GeometricPoint ((BigFppfOver.toScheme B S hS).obj V))
    (hv : B.Contains (Spec (.of v.residueField)))
    (ψ : D.T ⟶ V)
    (e : (BigFppfOver.toScheme B S hS).obj D.T ≅
      _root_.AlgebraicGeometry.strictHenselization E _ hV v)
    (he : (BigFppfOver.toScheme B S hS).map ψ =
      e.hom ≫ _root_.AlgebraicGeometry.strictHenselizationToBase E _ hV v)
    (hg : D.g = yoneda.map ψ ≫ a) (hD : D.IsImpurity) :
    ∃ D' : ImpurityDiagram P, IsQuasiFiniteAt B S hS D'.g D'.t ∧ D'.IsImpurity :=
  exists_isImpurity_isQuasiFiniteAt_of_exists_isImpurity_isEtale P
    (exists_isImpurity_isEtale_of_isImpurity_strictHenselization D V a ha E hV v hv ψ e he hg
      hD)

end AlgebraicGeometry.Space

end
