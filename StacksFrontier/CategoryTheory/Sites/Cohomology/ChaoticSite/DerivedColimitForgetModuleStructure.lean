module

public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitByPointResolutionAbelian
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitOfComplexesByPointResolution
public import StacksFrontier.Homology.DerivedIndexing.Extend
public import StacksFrontier.RingTheory.Dualizing.DerivedHomBaseChange.Conservative

/-!
# Derived lower shriek and forgetting the module structure, on a site with a point resolution

Let `C` be a small category with the chaotic topology, `B` a ring, and `U_•` a cosimplicial
object of `C` which is a point resolution. This file compares the two derived lower shrieks
available to a `B̲`-module — the one with values in `D(B)` and the one with values in `D(Ab)`
applied to the underlying diagram of abelian groups:

`forget(Lπ_!^{B}(ℱ)) ≅ Lπ_!^{Ab}(forget ℱ)` in `D(Ab)`, naturally in `ℱ`.

In general this comparison is only a natural transformation, and not an isomorphism: that is the
content of [Stacks, Tag 07AE], formalized for a general morphism of sites in
`StacksFrontier/CategoryTheory/Sites/Cohomology/LowerShriek/ForgetComparison.lean`. What makes it an
isomorphism here is the point resolution. Both sides are computed by the extended Moore complex
of the evaluation on `U_•` — `Stacks.ChaoticSite.ModuleValued.mooreCochainNatIsoDerivedColimit`
and `Stacks.ChaoticSite.AbelianValued.mooreCochainNatIsoDerivedColimit`, the two derived forms of
[Stacks, Tag 08Q9] — and that complex is manifestly compatible with forgetting the module
structure, since forming the alternating sum of the faces commutes with an additive functor.

## Why the universal property does not give this

The composite `Lπ_!^{B} ⋙ forget` is a left derived functor of `colim ⋙ forget` for free, by the
absoluteness of Stacks 0794
(`Stacks.CategoryHomology.isLeftDerivedFunctor_comp_of_enoughProjectives`), so the canonical
comparison exists with no hypothesis at all. Its invertibility is equivalent to the *other*
composite, `forget ⋙ Lπ_!^{Ab}`, being a left derived functor of the same functor, and that is
not formal: it would require the diagramwise forgetful functor to carry projective diagrams of
`B`-modules to `colim`-acyclic diagrams of abelian groups. It does not carry them to projective
ones — a projective `B`-module need not be projective over `ℤ`, as `B = ZMod 2` shows — so the
route that discharges every other acyclicity hypothesis in this library, namely that a bounded
above acyclic complex of projectives is K-projective and hence zero in the homotopy category, is
unavailable. The missing input would be the bounded above dual of [Stacks, Tag 05T8], which
`StacksFrontier/Algebra/Homology/DerivedCategory/AcyclicObjects.lean` explicitly declines to state.
The point resolution replaces that input.

## No variance is fixed

Nothing below prefers one direction of the comparison to the other. The final statement is an
`IsIso ↔ IsIso` between a morphism of `D(B)` and its image in `D(Ab)`, so it composes equally
well with a unit and with a counit: a consumer holding the derived unit of [Stacks, Tag 08QJ]
and wanting the counit demanded by a triangle identity may apply it to either, in either
direction, without an inverse having to be threaded through.

## Main definitions

* `Stacks.ChaoticSite.forgetModuleDiagrams`: forgetting the module structure of a diagram of
  `B`-modules on `Cᵒᵖ`.
* `Stacks.ChaoticSite.mooreCochainComplexCompForgetNatIso`: the extended Moore complex of the
  underlying diagram of abelian groups is the extended Moore complex of the diagram of modules,
  read degreewise in abelian groups.
* `Stacks.ChaoticSite.derivedColimitCompForgetNatIso`: **the comparison** — the image in `D(Ab)`
  of `Lπ_!^{B}(ℱ)` and `Lπ_!^{Ab}(forget ℱ)` agree, as an isomorphism of functors.

## Main results

* `Stacks.ChaoticSite.ModuleValued.isIso_totalDerivedColimit_single_map_iff`: derived lower
  shriek in `D(B)` inverts a morphism of `B̲`-modules exactly when the induced morphism of
  extended Moore complexes is a quasi-isomorphism. This is the module-coefficient twin of
  `Stacks.ChaoticSite.AbelianValued.isIso_totalDerivedColimit_single_map_iff`.
* `Stacks.ChaoticSite.isIso_totalDerivedColimit_single_map_forget_iff`: **the statement a
  consumer uses** — a morphism of `B̲`-modules is inverted by `Lπ_!` in `D(B)` exactly when the
  underlying morphism of abelian diagrams is inverted by `Lπ_!` in `D(Ab)`.

## Implementation notes

The last result needs two inputs, not one. The natural isomorphism identifies the *image* in
`D(Ab)` of the morphism of `D(B)` with the morphism of `D(Ab)` that a consumer has in hand; what
turns an identification of images into a statement about the morphism of `D(B)` itself is the
conservativity of `forget₂ (ModuleCat B) AddCommGrpCat` on derived categories, which is
`CategoryTheory.Functor.reflectsIsomorphisms_mapDerivedCategory` and needs no hypothesis beyond
exactness and reflection of isomorphisms by the functor itself.

**A universe constraint on that conservativity instance.** Instance search for
`CategoryTheory.Functor.reflectsIsomorphisms_mapDerivedCategory` at
`forget₂ (ModuleCat.{v} B) AddCommGrpCat.{v}` with `B : Type w` and `v`, `w` independent fails,
with `stuck at solving universe constraint … PreservesColimits (forget₂ (ModuleCat B)
AddCommGrpCat)`: Mathlib's colimit-preservation instances for that forgetful functor are stated
at `ModuleCat.{max w w'} R`, and the mixed shape does not unify with them. It resolves at
`ModuleCat.{max v w} B` and at the `ModuleCat.{u} B`, `B : Type u` used throughout this file.

## References

* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
* [Stacks Project, Tag 08PF](https://stacks.math.columbia.edu/tag/08PF)
* [Stacks Project, Tag 07AE](https://stacks.math.columbia.edu/tag/07AE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open Stacks.CategoryHomology

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.ChaoticSite

variable {C : Type u} [SmallCategory C] {B : Type u} [Ring B] (U : CosimplicialObject C)

/-! ### The module-coefficient criterion -/

namespace ModuleValued

/-- **Derived lower shriek in `D(B)` inverts a morphism of `B̲`-modules exactly when the induced
morphism of extended Moore complexes is a quasi-isomorphism.** This is the naturality square of
`Stacks.ChaoticSite.ModuleValued.mooreCochainNatIsoDerivedColimit` at `a`, read through the
characterisation of the isomorphisms in the derived category, and it is the module-coefficient
twin of `Stacks.ChaoticSite.AbelianValued.isIso_totalDerivedColimit_single_map_iff`. -/
theorem isIso_totalDerivedColimit_single_map_iff (hU : IsPointResolution U)
    {F G : Cᵒᵖ ⥤ ModuleCat.{u} B} (a : F ⟶ G) :
    IsIso ((totalDerivedColimit C (ModuleCat.{u} B)).map (DerivedCategory.Q.map
        ((HomologicalComplex.single (Cᵒᵖ ⥤ ModuleCat.{u} B)
          (ComplexShape.up ℤ) 0).map a))) ↔
      QuasiIso ((mooreCochainComplex U).map a) := by
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
  exact (NatIso.isIso_map_iff (mooreCochainNatIsoDerivedColimit U hU) a).symm

end ModuleValued

/-! ### Forgetting the module structure of a diagram -/

/-- Forgetting the module structure of a diagram of `B`-modules on `Cᵒᵖ`, that is, of a
`B̲`-module on the chaotic site. -/
abbrev forgetModuleDiagrams :
    (Cᵒᵖ ⥤ ModuleCat.{u} B) ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  (Functor.whiskeringRight Cᵒᵖ (ModuleCat.{u} B) AddCommGrpCat.{u}).obj
    (ModuleValued.forgetModules (B := B))

/-- **The Moore complex of the underlying diagram of abelian groups is the Moore complex of the
diagram of modules, read degreewise in abelian groups**, as an equality of functors. This is the
functorial form of `Stacks.ChaoticSite.cosimplicialMooreComplex_comp_forgetModules`: forming the
alternating sum of the faces commutes with an additive functor
(`AlgebraicTopology.map_alternatingFaceMapComplex`). -/
theorem forgetModuleDiagrams_comp_cosimplicialMooreComplex :
    forgetModuleDiagrams (B := B) ⋙ cosimplicialMooreComplex U =
      ModuleValued.moduleCosimplicialMooreComplex U ⋙
        (ModuleValued.forgetModules (B := B)).mapHomologicalComplex (ComplexShape.down ℕ) := by
  rw [show ModuleValued.moduleCosimplicialMooreComplex (B := B) U ⋙
      (ModuleValued.forgetModules (B := B)).mapHomologicalComplex (ComplexShape.down ℕ) =
      (Functor.whiskeringLeft SimplexCategoryᵒᵖ Cᵒᵖ (ModuleCat.{u} B)).obj U.op ⋙
        (alternatingFaceMapComplex (ModuleCat.{u} B) ⋙
          (ModuleValued.forgetModules (B := B)).mapHomologicalComplex
            (ComplexShape.down ℕ)) from rfl,
    AlgebraicTopology.map_alternatingFaceMapComplex (ModuleValued.forgetModules (B := B))]
  rfl

/-- **The extended Moore complex of the underlying diagram of abelian groups is the extended
Moore complex of the diagram of modules, read degreewise in abelian groups.** Extension by zero
along an embedding of complex shapes does not commute with an additive functor on the nose — the
image of a zero object is only *a* zero object — so this is an isomorphism and not an equality,
in contrast to `Stacks.ChaoticSite.forgetModuleDiagrams_comp_cosimplicialMooreComplex`. -/
def mooreCochainComplexCompForgetNatIso :
    forgetModuleDiagrams (B := B) ⋙ AbelianValued.mooreCochainComplex U ≅
      ModuleValued.mooreCochainComplex U ⋙
        (ModuleValued.forgetModules (B := B)).mapHomologicalComplex (ComplexShape.up ℤ) :=
  Functor.isoWhiskerRight (eqToIso (forgetModuleDiagrams_comp_cosimplicialMooreComplex U))
      ((ComplexShape.embeddingUpIntLE (0 : ℤ)).extendFunctor AddCommGrpCat.{u}) ≪≫
    Functor.isoWhiskerLeft (ModuleValued.moduleCosimplicialMooreComplex U)
      (Stacks.DerivedIndexing.mapExtendNatIsoSymm (ModuleValued.forgetModules (B := B))
        (ComplexShape.embeddingUpIntLE (0 : ℤ))).symm

/-! ### The comparison -/

/-- **Derived lower shriek commutes with forgetting the module structure, on a site admitting a
point resolution.** For a cosimplicial object `U_•` of `C` which is a point resolution,

`forget(Lπ_!^{B}(ℱ)) ≅ Lπ_!^{Ab}(forget ℱ)` in `D(Ab)`,

naturally in the diagram `ℱ` of `B`-modules placed in cohomological degree zero. Both sides are
the extended Moore complex of the evaluation on `U_•`, by the two derived forms of
[Stacks, Tag 08Q9], and that complex does not see the module structure. -/
def derivedColimitCompForgetNatIso (hU : IsPointResolution U) :
    HomologicalComplex.single (Cᵒᵖ ⥤ ModuleCat.{u} B) (ComplexShape.up ℤ) 0 ⋙
        DerivedCategory.Q ⋙ totalDerivedColimit C (ModuleCat.{u} B) ⋙
          (ModuleValued.forgetModules (B := B)).mapDerivedCategory ≅
      forgetModuleDiagrams (B := B) ⋙
        HomologicalComplex.single (Cᵒᵖ ⥤ AddCommGrpCat.{u}) (ComplexShape.up ℤ) 0 ⋙
          DerivedCategory.Q ⋙ totalDerivedColimit C AddCommGrpCat.{u} :=
  Functor.isoWhiskerRight (ModuleValued.mooreCochainNatIsoDerivedColimit U hU).symm
      (ModuleValued.forgetModules (B := B)).mapDerivedCategory ≪≫
    Functor.isoWhiskerLeft (ModuleValued.mooreCochainComplex U)
      (ModuleValued.forgetModules (B := B)).mapDerivedCategoryFactors ≪≫
    Functor.isoWhiskerRight (mooreCochainComplexCompForgetNatIso U).symm DerivedCategory.Q ≪≫
    Functor.isoWhiskerLeft (forgetModuleDiagrams (B := B))
      (AbelianValued.mooreCochainNatIsoDerivedColimit U hU)

/-- **A morphism of `B̲`-modules is inverted by derived lower shriek in `D(B)` exactly when the
underlying morphism of diagrams of abelian groups is inverted by derived lower shriek in
`D(Ab)`.** This is the statement that lets a result proved in `D(Ab)` — for instance the change
of coefficients of [Stacks, Tag 08QJ] — be read at module coefficients.

It is an equivalence, not an implication, and it mentions no comparison map of its own, so it
imposes no direction on the morphism `a`: it applies to a unit and to a counit alike.

The forward direction is the functoriality of derived lower shriek through the identification
`Stacks.ChaoticSite.derivedColimitCompForgetNatIso`; the backward direction is that one
identification together with the conservativity of `forget₂ (ModuleCat B) AddCommGrpCat` on
derived categories. -/
theorem isIso_totalDerivedColimit_single_map_forget_iff (hU : IsPointResolution U)
    {F G : Cᵒᵖ ⥤ ModuleCat.{u} B} (a : F ⟶ G) :
    IsIso ((totalDerivedColimit C (ModuleCat.{u} B)).map (DerivedCategory.Q.map
        ((HomologicalComplex.single (Cᵒᵖ ⥤ ModuleCat.{u} B)
          (ComplexShape.up ℤ) 0).map a))) ↔
      IsIso ((totalDerivedColimit C AddCommGrpCat.{u}).map (DerivedCategory.Q.map
        ((HomologicalComplex.single (Cᵒᵖ ⥤ AddCommGrpCat.{u}) (ComplexShape.up ℤ) 0).map
          ((forgetModuleDiagrams (B := B)).map a)))) := by
  have h := NatIso.isIso_map_iff (derivedColimitCompForgetNatIso U hU) a
  simp only [Functor.comp_map] at h
  rw [← h]
  exact ⟨fun _ => inferInstance,
    fun _ => isIso_of_reflects_iso _ (ModuleValued.forgetModules (B := B)).mapDerivedCategory⟩

end Stacks.ChaoticSite

end
