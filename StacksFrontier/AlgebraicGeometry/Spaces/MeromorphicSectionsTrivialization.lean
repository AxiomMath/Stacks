module

public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicFunctionsLocalUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionTrivialChart
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicValueOfSection
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyBijective

/-!
# The sheaf of meromorphic sections of a module trivialised at the codimension-zero points

Let `X` be an algebraic space over a scheme `S` of a big fppf site `B` satisfying conditions (a),
(b) and (c) of Stacks 0ENA and let `M` be an **invertible** `𝒪_X`-module together with a
trivialisation of `j_η^*M` at every point `η` of codimension `0`.  This file proves
`𝒦_X ≅ 𝒦_X(M)` as sheaves of `𝒦_X`-modules — the statement the construction of a regular
meromorphic section of Stacks 0EPQ consumes.

The morphism is the one the **meromorphic value** of
`StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicValueOfSection` transposes to.  The sheaf of
meromorphic sections is the sheafification of the sectionwise extension of scalars
`𝒦_X ⊗_{𝒪_X} M`, and the meromorphic value, being a morphism of `𝒪_X`-modules `M ⟶ 𝒦_X`,
transposes along the change-of-rings adjunction of Stacks 03CU to a morphism of presheaves of
`𝒦_X`-modules `𝒦_X ⊗_{𝒪_X} M ⟶ 𝒦_X`, `a ⊗ m ↦ a · v(m)`.

That morphism is **locally bijective**.  Over a chart `U` carrying a free generator `g` of `M`
the map `a ↦ a ⊗ g` is a bijection of `𝒦_X(U)` onto the sections of `𝒦_X ⊗_{𝒪_X} M`, so the
morphism is, up to that bijection, multiplication by `v(g)`; and `v(g)` is a unit over a covering
sieve, because multiplication by it is injective over every chart below
(`…injective_mul_meromorphicValue`) and a meromorphic function which multiplies injectively is
locally a unit (`AlgebraicGeometry.Space.exists_sieve_isUnit_of_injective_mul`).  The charts
carrying such a generator cover every chart, by Stacks 0B8Q for the small étale site.

A locally bijective morphism out of a presheaf into a sheaf identifies that sheaf with the
sheafification, which is
`Stacks.SheafOfModules.isIso_of_fac_of_isLocallyBijective`; so the transpose of the morphism
across the sheafification is an isomorphism `𝒦_X(M) ≅ 𝒦_X`.

## Main definitions

* `…meromorphicValueCounit` is the morphism of presheaves of `𝒦_X`-modules
  `𝒦_X ⊗_{𝒪_X} M ⟶ 𝒦_X`.
* `…meromorphicValueCounitSieve` is the sieve of charts over which it, and every restriction of
  it, is bijective on sections.

## Main results

* `…bijective_meromorphicValueCounit_app`: bijectivity over a chart with a free generator whose
  meromorphic value is a unit.
* `…meromorphicValueCounitSieve_mem`: the sieve is covering.
* `…isLocallyInjective_uliftMap_meromorphicValueCounit` and
  `…isLocallySurjective_uliftMap_meromorphicValueCounit`: the universe lift of the transpose,
  which is the morphism out of the presheaf that `𝒦_X(M)` sheafifies, is locally bijective.
* `…nonempty_uliftUnit_iso_meromorphicSectionSheaf`: **`𝒦_X ≅ 𝒦_X(M)`.**

## Implementation notes

The sieve quantifies over the charts *below* a member, not only over the member, so that it is
downward closed: bijectivity of the sections map over one chart says nothing about the charts
below it, while the covering family produced from local freeness does come with the stronger
property.

## References

* [Stacks Project, Tag 0ENA](https://stacks.math.columbia.edu/tag/0ENA)
* [Stacks Project, Tag 0EN5](https://stacks.math.columbia.edu/tag/0EN5)
* [Stacks Project, Tag 0EPQ](https://stacks.math.columbia.edu/tag/0EPQ)
* [Stacks Project, Tag 0B8Q](https://stacks.math.columbia.edu/tag/0B8Q)
* [Stacks Project, Tag 03CU](https://stacks.math.columbia.edu/tag/03CU)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

namespace CodimensionZeroPresentation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
    (P : CodimensionZeroPresentation B S hS X.1) (M : Modules.{u, u} B S hS X.1 X.2)
    (τ : (η : CodimensionZeroPoints B S hS X.1) → P.genericPointPullback η.2 M ≅
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS (P.specStalkSpace η.2).1 (P.specStalkSpace η.2).2).O))
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1)

/-! ### The transpose of the meromorphic value -/

/-- **The transpose of the meromorphic value**: the morphism of presheaves of `𝒦_X`-modules
`𝒦_X ⊗_{𝒪_X} M ⟶ 𝒦_X` sending `a ⊗ m` to `a · v(m)`. -/
noncomputable def meromorphicValueCounit :
    (Stacks.PresheafOfModules.ChangeOfRings.changeOfRings
        (toMeromorphicFunctionSheaf B S hS X.1 X.2).hom).obj M.val ⟶
      PresheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS X.1 X.2).O).obj :=
  Stacks.PresheafOfModules.ChangeOfRings.counitHom _ (P.meromorphicValueHom M τ hwa hfin)

/-- **The transpose is bijective over a chart carrying a free generator whose meromorphic value
is a unit.**  Over such a chart `a ↦ a ⊗ g` is a bijection onto the sections of
`𝒦_X ⊗_{𝒪_X} M`, and the transpose composed with it is multiplication by the value of `g`. -/
theorem bijective_meromorphicValueCounit_app (U : SmallEtale B S hS X.1)
    (g : M.val.obj (op U))
    (hg : Function.Bijective fun r : chartRing B S hS X.1 X.2 U ↦ r • g)
    (hu : IsUnit (P.meromorphicValue M τ hwa hfin U g)) :
    Function.Bijective ((P.meromorphicValueCounit M τ hwa hfin).app (op U)) := by
  let := ((toMeromorphicFunctionSheaf B S hS X.1 X.2).hom.app (op U)).hom.toAlgebra
  let : Module ((structureSheaf B S hS X.1 X.2).obj.obj (op U)) (M.val.obj (op U)) :=
    inferInstanceAs (Module (chartRing B S hS X.1 X.2 U) (M.val.obj (op U)))
  have hT : Function.Bijective
      fun a : (meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op U) ↦
        a ⊗ₜ[(structureSheaf B S hS X.1 X.2).obj.obj (op U)] g :=
    Stacks.bijective_tmul_of_bijective_smul g hg
  have h1 : Function.Bijective
      fun r : (meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op U) ↦
        r • (1 : (meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op U)) :=
    ⟨fun a b h => by simpa only [smul_eq_mul, mul_one] using h,
      fun c => ⟨c, by simp only [smul_eq_mul, mul_one]⟩⟩
  have hmul := Stacks.bijective_smul_of_isUnit_smul hu
    (show P.meromorphicValue M τ hwa hfin U g =
      P.meromorphicValue M τ hwa hfin U g •
        (1 : (meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op U)) by
      rw [smul_eq_mul, mul_one]) h1
  have hcomp : (fun y => ((P.meromorphicValueCounit M τ hwa hfin).app (op U)).hom y) ∘
        (fun a : (meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op U) ↦
          a ⊗ₜ[(structureSheaf B S hS X.1 X.2).obj.obj (op U)] g) =
      fun r : (meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op U) ↦
        r • P.meromorphicValue M τ hwa hfin U g := by
    funext a
    exact Stacks.PresheafOfModules.ChangeOfRings.counitApp_tmul _
      (P.meromorphicValueHom M τ hwa hfin) (op U) a g
  exact (hT.of_comp_iff _).mp (Eq.mpr (congrArg Function.Bijective hcomp) hmul)

/-! ### The covering sieve of bijectivity -/

/-- **The sieve of charts over which the transpose of the meromorphic value, and each of its
restrictions, is bijective on sections.** -/
def meromorphicValueCounitSieve (U : SmallEtale B S hS X.1) : Sieve U where
  arrows W _ := ∀ (W' : SmallEtale B S hS X.1) (_ : W' ⟶ W),
    Function.Bijective ((P.meromorphicValueCounit M τ hwa hfin).app (op W'))
  downward_closed hk j W'' h := hk W'' (h ≫ j)

include hwa hfin in
/-- **The sieve of bijectivity is covering.**  Over a chart on which `M` has a compatible family
of free generators, the meromorphic value of the generator multiplies injectively over every
chart below, hence is a unit over a covering sieve, and over each member the transpose is
bijective; and the charts carrying such a family cover every chart. -/
theorem meromorphicValueCounitSieve_mem
    (hM : AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property M)
    (U : SmallEtale B S hS X.1) :
    P.meromorphicValueCounitSieve M τ hwa hfin U ∈ SmallEtale.topology B S hS X.1 U := by
  obtain ⟨I, V₀, α, hcov, hgen⟩ :=
    exists_generator_cover_smul_of_isInvertible B S hS X M hM U
  refine (SmallEtale.topology B S hS X.1).transitive hcov _ ?_
  rintro Q k ⟨Q', p, q, ⟨i⟩, rfl⟩
  obtain ⟨e, hecompat, hebij⟩ := hgen i
  have hveq : ∀ (W : SmallEtale B S hS X.1) (j : W ⟶ Q),
      ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.map j.op).hom
          (P.meromorphicValue M τ hwa hfin Q (e Q p)) =
        P.meromorphicValue M τ hwa hfin W (e W (j ≫ p)) := fun W j =>
    (P.meromorphicValue_map M τ hwa hfin j (e Q p)).symm.trans
      (congrArg (P.meromorphicValue M τ hwa hfin W) (hecompat Q W p j))
  have hinj : ∀ (W : SmallEtale B S hS X.1) (j : W ⟶ Q), Function.Injective
      fun z : (meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op W) ↦
        z * ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.map j.op).hom
          (P.meromorphicValue M τ hwa hfin Q (e Q p)) := by
    intro W j
    rw [hveq W j]
    exact P.injective_mul_meromorphicValue M τ hwa hfin hM (V₀ i) e hecompat hebij W (j ≫ p)
  obtain ⟨T, hT, hunit⟩ := exists_sieve_isUnit_of_injective_mul B S hS X.1 X.2 Q
    (P.meromorphicValue M τ hwa hfin Q (e Q p)) hinj
  refine (SmallEtale.topology B S hS X.1).superset_covering ?_ hT
  intro W j hj W' h
  refine P.bijective_meromorphicValueCounit_app M τ hwa hfin W' (e W' ((h ≫ j) ≫ p))
    (hebij W' ((h ≫ j) ≫ p)) ?_
  exact (hveq W' (h ≫ j)) ▸ hunit (h ≫ j) (T.downward_closed hj h)

/-! ### The isomorphism `𝒦_X ≅ 𝒦_X(M)` -/

/-- Bijectivity of the sections map of the transpose is unaffected by the universe lift. -/
theorem bijective_uliftMap_meromorphicValueCounit_app (W : SmallEtale B S hS X.1)
    (h : Function.Bijective ((P.meromorphicValueCounit M τ hwa hfin).app (op W))) :
    Function.Bijective (PresheafOfModules.Hom.app (PresheafOfModules.uliftMap.{_, _, _, _, u + 1}
      (P.meromorphicValueCounit M τ hwa hfin)) (op W)) := by
  refine ⟨fun a b hab => ULift.ext (h.injective (congrArg ULift.down hab)), fun c => ?_⟩
  obtain ⟨t, ht⟩ := h.surjective c.down
  exact ⟨ULift.up t, ULift.ext ht⟩

include hwa hfin in
/-- **The universe lift of the transpose of the meromorphic value is locally injective.** -/
theorem isLocallyInjective_uliftMap_meromorphicValueCounit
    (hM : AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property M) :
    Presheaf.IsLocallyInjective (SmallEtale.topology B S hS X.1)
      ((PresheafOfModules.toPresheaf _).map (PresheafOfModules.uliftMap.{_, _, _, _, u + 1}
        (P.meromorphicValueCounit M τ hwa hfin))) := by
  constructor
  intro Z a b hab
  refine (SmallEtale.topology B S hS X.1).superset_covering ?_
    (P.meromorphicValueCounitSieve_mem M τ hwa hfin hM Z.unop)
  intro W k hk
  refine (P.bijective_uliftMap_meromorphicValueCounit_app M τ hwa hfin W (hk W (𝟙 W))).injective ?_
  refine Eq.trans (PresheafOfModules.naturality_apply
    (PresheafOfModules.uliftMap.{_, _, _, _, u + 1}
      (P.meromorphicValueCounit M τ hwa hfin)) k.op a) ?_
  refine Eq.trans ?_ (PresheafOfModules.naturality_apply
    (PresheafOfModules.uliftMap.{_, _, _, _, u + 1}
      (P.meromorphicValueCounit M τ hwa hfin)) k.op b).symm
  exact congrArg
    (fun w : (PresheafOfModules.uliftObj.{_, _, _, _, u + 1} (PresheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS X.1 X.2).O).obj)).obj
          Z ↦
      ((PresheafOfModules.uliftObj.{_, _, _, _, u + 1} (PresheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS X.1 X.2).O).obj)).map
          k.op).hom w) hab

include hwa hfin in
/-- **The universe lift of the transpose of the meromorphic value is locally surjective.** -/
theorem isLocallySurjective_uliftMap_meromorphicValueCounit
    (hM : AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property M) :
    Presheaf.IsLocallySurjective (SmallEtale.topology B S hS X.1)
      ((PresheafOfModules.toPresheaf _).map (PresheafOfModules.uliftMap.{_, _, _, _, u + 1}
        (P.meromorphicValueCounit M τ hwa hfin))) := by
  constructor
  intro U s
  refine (SmallEtale.topology B S hS X.1).superset_covering ?_
    (P.meromorphicValueCounitSieve_mem M τ hwa hfin hM U)
  intro W k hk
  exact (P.bijective_uliftMap_meromorphicValueCounit_app M τ hwa hfin W (hk W (𝟙 W))).surjective _

include P τ hwa hfin in
/-- **`𝒦_X ≅ 𝒦_X(M)` for a module trivialised at the codimension-zero points.**  The sheaf of
meromorphic sections is the sheafification of `𝒦_X ⊗_{𝒪_X} M`, which receives the locally
bijective transpose of the meromorphic value into the sheaf `𝒦_X`; a sheaf receiving a locally
bijective morphism from a presheaf is its sheafification. -/
theorem nonempty_uliftUnit_iso_meromorphicSectionSheaf
    (hM : AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property M) :
    Nonempty (SheafOfModules.uliftObj.{_, _, _, _, u + 1}
        (SheafOfModules.unit
          (Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS X.1 X.2).O)) ≅
      meromorphicSectionSheaf.{u, u} B S hS X.1 X.2 M) := by
  let : HasWeakSheafify (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1} :=
    moduleHasWeakSheafify.{u, u} B S hS X.1
  let : (SmallEtale.topology B S hS X.1).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    moduleWEqualsLocallyBijective.{u, u} B S hS X.1
  let : Presheaf.IsLocallyInjective (SmallEtale.topology B S hS X.1)
      (CategoryTheory.toSheafify (SmallEtale.topology B S hS X.1)
        (meromorphicSectionPresheaf.{u, u} B S hS X.1 X.2 M).presheaf) :=
    ((SmallEtale.topology B S hS X.1).W_toSheafify
      (meromorphicSectionPresheaf.{u, u} B S hS X.1 X.2 M).presheaf).isLocallyInjective
  let : Presheaf.IsLocallySurjective (SmallEtale.topology B S hS X.1)
      (CategoryTheory.toSheafify (SmallEtale.topology B S hS X.1)
        (meromorphicSectionPresheaf.{u, u} B S hS X.1 X.2 M).presheaf) :=
    ((SmallEtale.topology B S hS X.1).W_toSheafify
      (meromorphicSectionPresheaf.{u, u} B S hS X.1 X.2 M).presheaf).isLocallySurjective
  have hti : PresheafOfModules.IsLocallyInjective (meromorphicRingedSite B S hS X.1 X.2).J
      (PresheafOfModules.toSheafify
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS X.1 X.2).O).obj)
        (CategoryTheory.toSheafify (SmallEtale.topology B S hS X.1)
          (meromorphicSectionPresheaf.{u, u} B S hS X.1 X.2 M).presheaf)) := inferInstance
  have hts : PresheafOfModules.IsLocallySurjective (meromorphicRingedSite B S hS X.1 X.2).J
      (PresheafOfModules.toSheafify
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS X.1 X.2).O).obj)
        (CategoryTheory.toSheafify (SmallEtale.topology B S hS X.1)
          (meromorphicSectionPresheaf.{u, u} B S hS X.1 X.2 M).presheaf)) := inferInstance
  have hli : PresheafOfModules.IsLocallyInjective (meromorphicRingedSite B S hS X.1 X.2).J
      (PresheafOfModules.uliftMap.{_, _, _, _, u + 1}
        (P.meromorphicValueCounit M τ hwa hfin)) :=
    P.isLocallyInjective_uliftMap_meromorphicValueCounit M τ hwa hfin hM
  have hls : PresheafOfModules.IsLocallySurjective (meromorphicRingedSite B S hS X.1 X.2).J
      (PresheafOfModules.uliftMap.{_, _, _, _, u + 1}
        (P.meromorphicValueCounit M τ hwa hfin)) :=
    P.isLocallySurjective_uliftMap_meromorphicValueCounit M τ hwa hfin hM
  set h := (PresheafOfModules.sheafificationHomEquiv
    (P := meromorphicSectionPresheaf.{u, u} B S hS X.1 X.2 M)
    (F := SheafOfModules.uliftObj.{_, _, _, _, u + 1}
      (SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS X.1 X.2).O)))
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS X.1 X.2).O).obj)).symm
      (PresheafOfModules.uliftMap.{_, _, _, _, u + 1}
        (P.meromorphicValueCounit M τ hwa hfin)) with hh
  have : IsIso h :=
    @Stacks.SheafOfModules.isIso_of_fac_of_isLocallyBijective _ _ _ _ _ _ _
      (PresheafOfModules.toSheafify
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS X.1 X.2).O).obj)
        (CategoryTheory.toSheafify (SmallEtale.topology B S hS X.1)
          (meromorphicSectionPresheaf.{u, u} B S hS X.1 X.2 M).presheaf))
      (PresheafOfModules.uliftMap.{_, _, _, _, u + 1}
        (P.meromorphicValueCounit M τ hwa hfin)) h
      (by rw [hh]; exact (PresheafOfModules.sheafificationHomEquiv _).apply_symm_apply _)
      hti hts hli hls
  exact ⟨(asIso h).symm⟩

end CodimensionZeroPresentation

end AlgebraicGeometry.Space

end
