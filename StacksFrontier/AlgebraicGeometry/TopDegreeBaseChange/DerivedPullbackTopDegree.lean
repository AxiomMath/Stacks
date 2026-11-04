module

public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncGELTSingle
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TopDegreeComparison
public import StacksFrontier.Homology.HomComplex.RHom
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Triangulated
public import
  StacksFrontier.Topology.Sheaves.Cohomology.KFlatAndDerivedPullback.ResolvingDatumUnconditional
public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.TensorProduct
public import
  StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ClosedSubsetPullbackRightExact
import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.DerivedPullback
import StacksCore.Tactic.EgaSgaAttribute

open AlgebraicGeometry.RingedSpace.KFlatDerivedPullback

/-!
# The top cohomology of a derived pullback is the pullback of the top cohomology

[Stacks, Tag 0EX3] argues for its conclusion (c) that, `Rf'_* F'` having no cohomology above the
degree `d`,

> `H^d(Lh^* Rf'_* F') = h^* R^d f'_* F'`.

`Stacks.TopDegreeComparison` isolates the homological half of that step: a *right t-exact*
triangulated functor of derived categories computes the degree-`d` cohomology of its argument
from the degree-`d` truncation alone. It carries right t-exactness as an explicit hypothesis,
because no declaration in this development established it for any functor.

This file supplies it for the derived pullback of sheaves of modules along a morphism of ringed
spaces, identifies the remaining single-complex term `H^d(Lf^*(M[-d]))` with the ordinary
pullback `f^* M`, and composes the three into the displayed step.

## Main results

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.isLE_derivedPullback_obj`: `Lf^*` is right
  t-exact — it carries `D^{≤a}(𝒪_Y)` to `D^{≤a}(𝒪_X)`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.truncGEIsoSingleHomology`: for `K` with no
  cohomology above `d`, the truncation `τ^{≥d} K` is `H^d(K)` placed in degree `d`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedPullbackTopDegreeIso`: the top cohomology
  of `Lf^* K` is that of `Lf^*` of any model of `τ^{≥d} K`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedPullbackTopDegreeIsoSingle`: the two
  combined — `H^d(Lf^* K) ≅ H^d(Lf^*(H^d(K)[-d]))` for `K` with no cohomology above `d`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.mapTopHomologyIso`: a right-exact additive functor
  commutes with the top cohomology of a strictly bounded-above complex, and
  `isIso_homologyMap_map_of_isStrictlyLE` is the consequence used below — such a functor carries a
  degree-`d` homology isomorphism between strictly bounded-above complexes to one.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange`'s
  `isIso_homologyFunctor_map_derivedPullbackComparison_app`: the canonical comparison
  `Lf^*(Q P) ⟶ Q(f^* P)` is invertible on degree-`d` cohomology for **every** complex `P` with
  zero terms above `d` — not only for a K-flat one.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.homologyDerivedPullbackSingleIso`:
  `H^d(Lf^*(M[-d])) ≅ f^* M` for a single module `M`, **as the canonical map**
  `homologyDerivedPullbackSingleMap`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedPullbackTopDegreeIsoPullback`: the step the
  source displays, `H^d(Lf^* K) ≅ f^* H^d(K)` for `K` with no cohomology above `d`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.topDirectImagePullbackIso_of_isLE`: the same at the
  scheme-level spelling of the 0EX3 situation.

## Implementation notes

*Right t-exactness.* The proof is the one the source's `D^{≤a}` argument uses: an object of
`D^{≤a}(𝒪_Y)` is represented by a K-flat complex with zero terms above `a`
(`Stacks.DerivedTensor.RingedSite.exists_kFlat_isStrictlyLE_representative`), a K-flat complex
computes `Lf^*` (`Stacks.Cohomology.derivedPullbackIsoPullbackOfKFlat`), and degreewise pullback
is additive, so it keeps the terms zero above `a`.

*Two spellings of the category of `𝒪_Y`-modules.*
  `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y` and
`SheafOfModules.{u} (structureSheafRing Y)` are `rfl`-equal, as
`StacksDraft.KFlat.ringSheaf_eq` records, but their typeclass instances are different terms and
synthesis does not cross between them. `isLE_derivedPullback_obj` is therefore stated at the
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules` spelling, which is the one the K-flat
  representative comes in, and takes its
`IsLE` hypothesis as an **explicit argument** rather than as an instance binder: as an instance
binder it is not synthesizable at the other spelling, which is where
`Stacks.TopDegreeComparison.topDegreeIso` consumes it.

*`truncGEIsoSingleHomology` belongs upstream.* It is generic homological algebra about the
canonical t-structure and not about schemes, and it is one step from
`DerivedCategory.truncGELTIsoHomologyFunctorCompSingleFunctor`: for `K` with no cohomology above
`d` the inclusion `τ^{<d+1} K ⟶ K` is invertible, so `τ^{≥d} K` is `τ^{≥d} τ^{<d+1} K`. It is
recorded here because it is this tag that needs it; it should move to
`StacksFrontier/Algebra/Homology/DerivedCategory/TruncGELTSingle.lean` when that file is next
touched.

*The single-complex term, and why it is the canonical map.* `H^d(Lf^*(M[-d])) ≅ f^* M` is proved
by the source's own route and not by any general nonsense. The map is
`homologyDerivedPullbackSingleMap`, built from
  `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison` exactly
as Tag 0EX3's own degree-zero `derivedToOrdinaryPullback` is; `derivedToOrdinaryPullbackSingle`
is that construction in degree `d`. Its invertibility on `H^d` is
`isIso_homologyFunctor_map_derivedPullbackComparison_app`, whose proof is the source's: choose a
termwise-surjective quasi-isomorphism `s : F ⟶ P` with `F` K-flat and `F` again zero above `d`
(`CochainComplex.exists_quasiIso_prop`, Stacks 05T7), where the comparison *is* invertible
(`Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat`); the
naturality square of
the comparison at `s` then reduces the claim to `H^d(f^* s)`, and that is an isomorphism because
`f^*` preserves the cokernel of the last differential, being a left adjoint. That last step is
`isIso_homologyMap_map_of_isStrictlyLE`, the `IsIso` form of `mapTopHomologyIso`, stated for an
arbitrary additive functor preserving finite colimits; both are generic homological algebra and
belong upstream beside `truncGEIsoSingleHomology`. Right exactness of `f^*` is **not** re-derived
here: `RingedSpaceModuleAdjunction.preservesFiniteColimits_modulePullback` already has it
unconditionally, and three files in the tree still carry it as a hypothesis it need not be.

*The comparison is invertible on `H^d` for every strictly bounded-above complex.* That is
strictly more than
`Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat`, which
needs `P` K-flat, and it is what makes the single complex — which is not K-flat — reachable at
all.

*Spelling.* Everything below is stated at the `SheafOfModules.{u} (structureSheafRing _)`
spelling, which is the one
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison`,
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pullbackOnHomotopy` and
`RingedSpaceModuleAdjunction.modulePullback` are stated at. The K-flat machinery of
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback` uses
`SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf _.sheaf)`, which is `rfl`-equal and
*not* syntactically equal, and `rw` sees the difference: a goal mixing the two does not match
`Functor.map_comp`, because the `Category` instance of the composition is a different term from
the one the functor's `map` expects. `exists_kFlat_isStrictlyLE_resolution` is therefore stated at
the `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules` spelling, where its
`[IsStrictlyLE]` instance binder is synthesizable, and the crossing happens once, in argument
position.

*No `@[stacks 0EX3]` attribute.* The tag asserts conclusions (a), (b) and (c) about a
`Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation`. Conclusion (a) **is** proved, as
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.isZero_rightDerivedPlus_pushforward_baseChange`
(`BaseChangeVanishing.lean`), which carries `@[stacks 0EX3 "(a)"]`. Conclusion (b) **is**
proved as well, over a base carrying no hypothesis and as exactly the statement about a canonical
map of sheaves on `Y'` that the tag makes: `isIso_higherDirectImageTensorMap` and
`topDirectImageTensorComparison` in `TensorComparisonBase.lean`, which carry
`@[stacks 0EX3 "(b)"]`. Conclusion (c) is proved too:
`…TopDegreeBaseChange.isIso_topDirectImageBaseChangeMap` (`BaseChangeTopDegreeConclusion.lean`),
which carries `@[stacks 0EX3 "(c)"]`.

**The `IsLE` hypothesis is discharged.** It is
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.isLE_derivedPushforward_baseChange`
(`DerivedModelCrossing.lean`), and the statement's `topDirectImagePullbackIso` is
`topDirectImagePullbackIso` in that same module, unconditional.

Conclusion (a) is a statement about `Functor.rightDerivedPlus` of
`Scheme.Modules.pushforward`, the homology of the derived functor on the *bounded below* derived
category `D⁺`, while the `IsLE` hypothesis is about
  `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward`, the
*unbounded* total right derived functor computed by K-injective resolutions, so (a) does not
supply `IsLE` directly and a crossing between the two models is needed.

The **functor-level** natural isomorphism `G.rightDerivedFunctorPlus ⋙ Plus.ι ≅ Plus.ι ⋙ H`
exists only as `private def rightDerivedPlusCompIso`
(`StacksFrontier/Homology/Tor/DerivedExtensionScalars.lean:1515`), under the
`backward.isDefEq.respectTransparency false` option, but it is not needed. `IsLE` is
a *proposition about one object*, so only the two functors' **values at one object** are needed,
and the object-level comparison is
`Stacks.Perfect.CechAugmentation.nonempty_obj_iso_rightDerivedFunctorPlus` —
a **public** theorem, in a file carrying no such option at all, whose single hypothesis is
exactly
  `isIso_derivedPushforwardUnit_app_of_isKInjective`. Its `Nonempty` wrapper
is no obstacle for the same reason the object level suffices: the conclusion transported is a
`Prop`. So the only input of the first declaration of the statement is one public lemma, in its
object-level form.

(c) asks in addition for the characterization of the comparison on cycle classes, and **that
characterization is available**: it is
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.topDirectImagePullbackIso_cycles`
(`TopDegreePullbackIdentity.lean`), with the cycle-free form
`topDirectImagePullbackIso_cycles_iff` (`TopDegreePullbackCycles.lean`). The two declarations
of the statement of Tag `0BDL` are both present in the library, generalized:
its comparison on cycles is `Stacks.MapHomologyCycles.mapCycles`
(`MapHomologyCycles.lean`), the comparison `G(Z^i K) ⟶ Z^i(G K)` that any additive functor
supplies, and its comparison of homology through a representative is
`homologyPullbackRepresentativeComparison` (`TopDegreePullbackCycles.lean`), which keeps the
statement's geometric name and is `Stacks.RepresentativeHomology.comparisonOfRepresentative` at the
derived-pullback counit. So the cycle-class description costs nothing further here.

(c) itself applies conclusion (b) — the companion statement — in the source's proof, so it is not
reachable from (a) and this comparison alone.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open RingedSpaceModuleAdjunction

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

universe u

open DerivedCategory

attribute [local instance] HasDerivedCategory.standard

section Truncation

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

/-- **An object with no cohomology above `d` has `H^d` for its `≥ d` truncation.** For such a
`K` the inclusion `τ^{<d+1} K ⟶ K` is invertible, so `τ^{≥d} K` is `τ^{≥d} τ^{<d+1} K`, which is
`H^d(K)` placed in degree `d` by
`DerivedCategory.truncGELTIsoHomologyFunctorCompSingleFunctor`. -/
@[sga "4 XVIII 2.14.2" "more general"]
def truncGEIsoSingleHomology (K : DerivedCategory C) (d : ℤ)
    (hK : TStructure.t.IsLE K d) :
    (TStructure.t.truncGE d).obj K ≅ (singleFunctor C d).obj ((homologyFunctor C d).obj K) :=
  have : IsIso ((TStructure.t.truncLTι (d + 1)).app K) :=
    (TStructure.t.isLE_iff_isIso_truncLTι_app d (d + 1) rfl K).1 hK
  ((TStructure.t.truncGE d).mapIso
      (asIso ((TStructure.t.truncLTι (d + 1)).app K))).symm ≪≫
    (truncGELTIsoHomologyFunctorCompSingleFunctor d).app K

end Truncation

section RightExact

variable {A : Type*} [Category A] [Abelian A] {B : Type*} [Category B] [Abelian B]

/-- **Opcycles commute with a functor preserving finite colimits.** In degree `j` the opcycles are
the cokernel of the differential into `j`, by `HomologicalComplex.opcyclesIsCokernel`, and a
functor preserving finite colimits carries that cokernel cofork to a cokernel cofork for the
image differential. -/
def mapOpcyclesIso (G : A ⥤ B) [G.Additive] [PreservesFiniteColimits G]
    (K : CochainComplex A ℤ) (i j : ℤ) (hij : (ComplexShape.up ℤ).prev j = i) :
    ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).opcycles j ≅ G.obj (K.opcycles j) :=
  IsColimit.coconePointUniqueUpToIso
    (((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).opcyclesIsCokernel i j hij)
    (isColimitCoforkMapOfIsColimit' G (K.d_pOpcycles i j) (K.opcyclesIsCokernel i j hij))

/-- **A right-exact additive functor commutes with the top cohomology of a strictly
bounded-above complex.** For `K` with zero terms above `d` the differential out of degree `d`
vanishes, so `H^d(K)` is the opcycles in degree `d` — the cokernel of the last differential — and
likewise for `G K`, whose terms above `d` are again zero. The two cokernels correspond by
`mapOpcyclesIso`.

The hypothesis `K.IsStrictlyLE d` is an **explicit argument**: at the two `rfl`-equal spellings of
the category of modules on a ringed space it is not synthesizable as an instance binder, which
puts the crossing in instance search instead of in the unifier. -/
def mapTopHomologyIso (G : A ⥤ B) [G.Additive] [PreservesFiniteColimits G]
    (K : CochainComplex A ℤ) (d : ℤ) (hK : K.IsStrictlyLE d) :
    ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homology d ≅ G.obj (K.homology d) :=
  have := hK
  have hz : IsZero (K.X (d + 1)) := K.isZero_of_isStrictlyLE d (d + 1) (by lia)
  have hd : K.d d (d + 1) = 0 := hz.eq_of_tgt _ _
  ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).isoHomologyι d (d + 1) (by simp)
      (by simpa using congrArg G.map hd) ≪≫
    mapOpcyclesIso G K (d - 1) d (by simp) ≪≫
    (G.mapIso (K.isoHomologyι d (d + 1) (by simp) hd)).symm

/-- An additive functor carries a complex with zero terms above `d` to one. -/
private theorem isStrictlyLE_map_obj (G : A ⥤ B) [G.Additive] (K : CochainComplex A ℤ) (d : ℤ)
    (hK : K.IsStrictlyLE d) :
    CochainComplex.IsStrictlyLE ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) d := by
  have := hK
  rw [CochainComplex.isStrictlyLE_iff]
  exact fun i hi => Functor.map_isZero _ (K.isZero_of_isStrictlyLE d i hi)

/-- For a complex with zero terms above `d`, `homologyι` in degree `d` is invertible. -/
private theorem isIso_homologyι_of_isStrictlyLE (K : CochainComplex B ℤ) (d : ℤ)
    (hK : K.IsStrictlyLE d) : IsIso (K.homologyι d) := by
  have := hK
  exact K.isIso_homologyι d (d + 1) (by simp)
    ((K.isZero_of_isStrictlyLE d (d + 1) (by lia)).eq_of_tgt _ _)

variable (G : A ⥤ B) [G.Additive] [PreservesFiniteColimits G]

/-- `mapOpcyclesIso` is the comparison characterized by its composite with the projection to the
opcycles, which is what makes it canonical and usable. -/
theorem pOpcycles_comp_mapOpcyclesIso_hom (K : CochainComplex A ℤ) (i j : ℤ)
    (hij : (ComplexShape.up ℤ).prev j = i) :
    ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).pOpcycles j ≫
        (mapOpcyclesIso G K i j hij).hom = G.map (K.pOpcycles j) := by
  have h := IsColimit.comp_coconePointUniqueUpToIso_hom
    (((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).opcyclesIsCokernel i j hij)
    (isColimitCoforkMapOfIsColimit' G (K.d_pOpcycles i j) (K.opcyclesIsCokernel i j hij))
    WalkingParallelPair.one
  simpa [mapOpcyclesIso, Cofork.π] using h

/-- **`mapOpcyclesIso` is natural in the complex.** Both sides are determined by their composite
with the projection to the opcycles, which is an epimorphism. -/
theorem mapOpcyclesIso_hom_naturality {K L : CochainComplex A ℤ} (φ : K ⟶ L) (i j : ℤ)
    (hij : (ComplexShape.up ℤ).prev j = i) :
    HomologicalComplex.opcyclesMap ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) j ≫
        (mapOpcyclesIso G L i j hij).hom =
      (mapOpcyclesIso G K i j hij).hom ≫ G.map (HomologicalComplex.opcyclesMap φ j) := by
  rw [← cancel_epi (((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).pOpcycles j)]
  rw [HomologicalComplex.p_opcyclesMap_assoc, pOpcycles_comp_mapOpcyclesIso_hom,
    ← Category.assoc, pOpcycles_comp_mapOpcyclesIso_hom, ← G.map_comp,
    HomologicalComplex.p_opcyclesMap]
  simp

/-- For complexes with zero terms above `d`, a degree-`d` homology isomorphism is the same thing as
an isomorphism of the opcycles in degree `d`: both sides are the cokernel of the last differential,
identified by `HomologicalComplex.homologyι`. -/
theorem isIso_opcyclesMap_of_isStrictlyLE {K L : CochainComplex A ℤ} (φ : K ⟶ L) (d : ℤ)
    (hK : K.IsStrictlyLE d) (hL : L.IsStrictlyLE d)
    (h : IsIso (HomologicalComplex.homologyMap φ d)) :
    IsIso (HomologicalComplex.opcyclesMap φ d) := by
  have := isIso_homologyι_of_isStrictlyLE K d hK
  have := isIso_homologyι_of_isStrictlyLE L d hL
  have : IsIso (K.homologyι d ≫ HomologicalComplex.opcyclesMap φ d) := by
    rw [← HomologicalComplex.homologyι_naturality]
    infer_instance
  exact IsIso.of_isIso_comp_left (K.homologyι d) _

/-- **A right-exact additive functor carries a degree-`d` homology isomorphism between strictly
bounded-above complexes to one.** This is the `IsIso` form of `mapTopHomologyIso`, obtained from
`mapOpcyclesIso_hom_naturality` through `isIso_opcyclesMap_of_isStrictlyLE`. -/
theorem isIso_homologyMap_map_of_isStrictlyLE {K L : CochainComplex A ℤ} (φ : K ⟶ L) (d : ℤ)
    (hK : K.IsStrictlyLE d) (hL : L.IsStrictlyLE d)
    (h : IsIso (HomologicalComplex.homologyMap φ d)) :
    IsIso (HomologicalComplex.homologyMap
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) d) := by
  have := isIso_homologyι_of_isStrictlyLE _ d (isStrictlyLE_map_obj G K d hK)
  have h3 := isIso_opcyclesMap_of_isStrictlyLE φ d hK hL h
  have h4 : IsIso (HomologicalComplex.opcyclesMap
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) d) := by
    have key : HomologicalComplex.opcyclesMap
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) d =
        (mapOpcyclesIso G K (d - 1) d (by simp)).hom ≫
          G.map (HomologicalComplex.opcyclesMap φ d) ≫
            (mapOpcyclesIso G L (d - 1) d (by simp)).inv := by
      rw [← Category.assoc, Iso.eq_comp_inv]
      exact mapOpcyclesIso_hom_naturality G φ (d - 1) d (by simp)
    rw [key]
    infer_instance
  have := isIso_homologyι_of_isStrictlyLE _ d (isStrictlyLE_map_obj G L d hL)
  have key : HomologicalComplex.homologyMap
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) d =
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homologyι d ≫
        HomologicalComplex.opcyclesMap
            ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) d ≫
          inv (((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj L).homologyι d) := by
    rw [← Category.assoc, IsIso.eq_comp_inv]
    exact HomologicalComplex.homologyι_naturality _ _
  rw [key]
  infer_instance

end RightExact

section DerivedGeneric

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

/-- A degree-`d` homology isomorphism of complexes becomes one after `Q` and `H^d`, without being
an isomorphism in the derived category.

Not to be confused with `Stacks08CQ.isIso_homologyFunctor_map_Q_map`, which carries the same
*name* and a different statement: it
assumes `QuasiIso` — invertibility in every degree — and concludes in every degree, and its proof
is that `Q` inverts a quasi-isomorphism outright. Here only degree `d` is assumed, which is all a
single complex supplies, so that proof does not apply. Hence the suffix. -/
theorem isIso_homologyFunctor_map_Q_map_of_isIso_homologyMap {K L : CochainComplex C ℤ}
    (ψ : K ⟶ L) (d : ℤ) (h : IsIso (HomologicalComplex.homologyMap ψ d)) :
    IsIso ((homologyFunctor C d).map (Q.map ψ)) := by
  have h1 : IsIso ((homologyFunctorFactors C d).hom.app K) :=
    ((homologyFunctorFactors C d).app K).isIso_hom
  have h2 : IsIso ((homologyFunctorFactors C d).hom.app L) :=
    ((homologyFunctorFactors C d).app L).isIso_hom
  have h3 : IsIso ((homologyFunctor C d).map (Q.map ψ) ≫
      (homologyFunctorFactors C d).hom.app L) := by
    rw [homologyFunctorFactors_hom_naturality ψ d]
    exact (asIso ((homologyFunctorFactors C d).hom.app K) ≪≫ @asIso _ _ _ _ _ h).isIso_hom
  exact IsIso.of_isIso_comp_right _ ((homologyFunctorFactors C d).hom.app L)

/-- The same through the homotopy category, which is the shape
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pullbackOnHomotopy` produces. -/
theorem isIso_homologyFunctor_map_Qh_map_quotient_map_of_isIso_homologyMap
    {K L : CochainComplex C ℤ} (ψ : K ⟶ L) (d : ℤ)
    (h : IsIso (HomologicalComplex.homologyMap ψ d)) :
    IsIso ((homologyFunctor C d).map
      (Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map ψ))) := by
  have h0 := isIso_homologyFunctor_map_Q_map_of_isIso_homologyMap ψ d h
  have h1 : IsIso ((quotientCompQhIso C).hom.app K) :=
    ((quotientCompQhIso C).app K).isIso_hom
  have h2 : IsIso ((quotientCompQhIso C).hom.app L) :=
    ((quotientCompQhIso C).app L).isIso_hom
  have h3 : IsIso ((homologyFunctor C d).map
      (Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map ψ) ≫
        (quotientCompQhIso C).hom.app L)) := by
    rw [quotientCompQhIso_hom_naturality ψ, Functor.map_comp]
    infer_instance
  rw [Functor.map_comp] at h3
  exact IsIso.of_isIso_comp_right _
    ((homologyFunctor C d).map ((quotientCompQhIso C).hom.app L))

/-- **`Qh` inverts the class of a quasi-isomorphism of complexes**, with `QuasiIso` as an
**explicit argument**. The content is the root-level instance
`isIso_Qh_map_quotient_map_of_quasiIso` (`StacksFrontier/Homology/HomComplex/RHom.lean:233`) and is
not re-derived here; what this adds is the binder. As an instance binder `QuasiIso` does not fire
at the `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules` spelling, which is the one
  `exists_kFlat_isStrictlyLE_resolution`
produces its map in, so the crossing has to happen in argument position. -/
theorem isIso_Qh_map_quotient_map {K L : CochainComplex C ℤ} (ψ : K ⟶ L) (h : QuasiIso ψ) :
    IsIso (Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map ψ)) :=
  have := h
  inferInstance

/-- **`H^d` of a module placed in degree `d` is the module.** -/
def homologySingleIso (N : C) (d : ℤ) :
    (homologyFunctor C d).obj ((singleFunctor C d).obj N) ≅ N :=
  (homologyFunctorFactors C d).app ((CochainComplex.singleFunctor C d).obj N) ≪≫
    HomologicalComplex.singleObjHomologySelfIso _ _ _

end DerivedGeneric

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **The derived pullback is right t-exact.** If `K` has no cohomology above `a`, neither has
`Lf^* K`.

`K` is represented by a K-flat complex `F` with zero terms above `a`; `Lf^*` is computed on a
K-flat complex by degreewise pullback, and degreewise pullback is additive, so `f^* F` again has
zero terms above `a`. -/
theorem isLE_derivedPullback_obj
    (K : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)) (a : ℤ) (hK
      : K.IsLE a) :
    ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).obj K).IsLE a := by
  have := hK
  obtain ⟨F, hF, hFLE, ⟨e⟩⟩ :=
    Stacks.DerivedTensor.RingedSite.exists_kFlat_isStrictlyLE_representative Y.sheaf K a
  have := hFLE
  have hQ : (DerivedCategory.Q.obj (((modulePullback f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj F)).IsLE a := by
    rw [DerivedCategory.isLE_Q_obj_iff]
    have := isStrictlyLE_map_obj (modulePullback f) F a hFLE
    infer_instance
  exact DerivedCategory.TStructure.t.isLE_of_iso
    ((Stacks.Cohomology.derivedPullbackIsoPullbackOfKFlat f F hF).symm ≪≫
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).mapIso e) a

/-- **The top cohomology of `Lf^* K` is read off any model of `τ^{≥d} K`.** This is
`Stacks.TopDegreeComparison.topDegreeIso` at `L = Lf^*`, whose right t-exactness hypothesis is
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.isLE_derivedPullback_obj`. -/
def derivedPullbackTopDegreeIso
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) (d : ℤ)
    {K₀ : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))}
    (e : (TStructure.t.truncGE d).obj K ≅ K₀) :
    (homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) d).obj
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).obj K) ≅
      (homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) d).obj
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).obj K₀) :=
  Stacks.TopDegreeComparison.topDegreeIso
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
    (fun Z n hZ => isLE_derivedPullback_obj f Z n hZ) K d e

/-- **The step [Stacks, Tag 0EX3] quotes**, at the spelling this development states the derived
pullback in: for `K` with no cohomology above `d`, the degree-`d` cohomology of `Lf^* K` is the
degree-`d` cohomology of `Lf^*` applied to `H^d(K)` placed in degree `d`.

Composed with `homologyDerivedPullbackSingleIso`, which identifies `H^d(Lf^*(M[-d]))` with
`f^* M`, this is the tag's `H^d(Lf^* K) = f^* H^d(K)`; see
`derivedPullbackTopDegreeIsoPullback`. -/
def derivedPullbackTopDegreeIsoSingle
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) (d : ℤ)
    (hK : TStructure.t.IsLE K d) :
    (homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) d).obj
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).obj K) ≅
      (homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) d).obj
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).obj
          ((singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) d).obj
            ((homologyFunctor (SheafOfModules.{u} (structureSheafRing Y)) d).obj K))) :=
  derivedPullbackTopDegreeIso f K d (truncGEIsoSingleHomology K d hK)

/-- **A K-flat resolution with the same cohomological bound.** Stacks 05T7
(`CochainComplex.exists_quasiIso_prop`) applied to the flat modules, with Stacks 06YS'
consequence that a bounded-above complex of flat modules is K-flat.

Stated at the `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules` spelling, which is
where the `[IsStrictlyLE]` instance binder of 05T7 is synthesizable; consumers at the
`SheafOfModules.{u} (structureSheafRing _)` spelling cross it in argument position. -/
theorem exists_kFlat_isStrictlyLE_resolution
    (P : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) (d : ℤ)
      (hP : P.IsStrictlyLE d) :
    ∃ (F : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) (s : F ⟶
      P),
      AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y F ∧ F.IsStrictlyLE d ∧ QuasiIso s
        := by
  have := hP
  obtain ⟨F, s, -, hs, hFflat, hFLE⟩ := (CochainComplex.exists_quasiIso_prop
    (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.flatProperty Y)
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.exists_flat_epi Y) d).1 P
  exact ⟨F, s, AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.kFlat_of_boundedAbove_of_flat Y F
    ⟨d, hFLE⟩ hFflat, hFLE, hs⟩

/-- **The comparison `Lf^*(Q P) ⟶ Q(f^* P)` is invertible on degree-`d` cohomology for every
complex `P` with zero terms above `d`.**
`Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat` gives this
for `P` K-flat; the point here is that no flatness is needed once one looks only at the top
cohomology, and that is what makes the single complex reachable.

Take a quasi-isomorphism `s : F ⟶ P` with `F` K-flat and again zero above `d`. The naturality
square of `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison` at the
  class of `s` has an isomorphism for its
left-hand vertical (`Qh` inverts `s`) and for its top edge (`F` is K-flat), so the claim for `P`
becomes the claim that `H^d(f^* s)` is an isomorphism — and it is, because `f^*` preserves the
cokernel of the last differential of a complex with zero terms above `d`. -/
theorem isIso_homologyFunctor_map_derivedPullbackComparison_app
    (P : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ) (d : ℤ)
    (hP : P.IsStrictlyLE d) :
    IsIso ((homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) d).map
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison f).app
        ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing Y))
          (ComplexShape.up ℤ)).obj P))) := by
  obtain ⟨F, s, hF, hFLE, hs⟩ := exists_kFlat_isStrictlyLE_resolution P d hP
  have hcompF :=
    Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat f F hF
  have hmap : IsIso (HomologicalComplex.homologyMap
      (((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).map s) d) := by
    have := RingedSpaceModuleAdjunction.preservesFiniteColimits_modulePullback f
    exact isIso_homologyMap_map_of_isStrictlyLE (modulePullback f) s d hFLE hP
      ((quasiIsoAt_iff_isIso_homologyMap s d).1 (hs.quasiIsoAt d))
  have hψ : IsIso ((homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) d).map
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pullbackOnHomotopy f).map
        ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing Y))
          (ComplexShape.up ℤ)).map s))) :=
    isIso_homologyFunctor_map_Qh_map_quotient_map_of_isIso_homologyMap
      (((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).map s) d hmap
  have hQs := isIso_Qh_map_quotient_map s hs
  have hLs : IsIso ((homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) d).map
      ((DerivedCategory.Qh ⋙ Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        f).map
        ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing Y))
          (ComplexShape.up ℤ)).map s))) :=
    ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f ⋙
      homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) d).mapIso
        (@asIso _ _ _ _ _ hQs)).isIso_hom
  have nat := (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison
    f).naturality
      ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing Y))
        (ComplexShape.up ℤ)).map s)
  have hRHS : IsIso ((homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) d).map
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison f).app
          ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing Y))
            (ComplexShape.up ℤ)).obj F) ≫
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pullbackOnHomotopy f).map
          ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing Y))
            (ComplexShape.up ℤ)).map s))) := by
    rw [Functor.map_comp]
    exact (@asIso _ _ _ _ _
        (((homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) d).mapIso
          (@asIso _ _ _ _ _ hcompF)).isIso_hom) ≪≫ @asIso _ _ _ _ _ hψ).isIso_hom
  rw [← nat, Functor.map_comp] at hRHS
  exact IsIso.of_isIso_comp_left
    ((homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) d).map
      ((DerivedCategory.Qh ⋙ Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        f).map
        ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing Y))
          (ComplexShape.up ℤ)).map s))) _

/-- **The canonical map `Lf^*(M[-d]) ⟶ (f^* M)[-d]`.** This is Tag 0EX3's own
`derivedToOrdinaryPullback`, which the statement writes in degree zero, in degree `d`: the derived-pullback
comparison of `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison` at the
  single complex on `M`, read through
the identifications of the single functors with their homotopy-category and derived-category
forms. -/
def derivedToOrdinaryPullbackSingle (M : SheafOfModules.{u} (structureSheafRing Y)) (d : ℤ) :
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).obj
        ((singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) d).obj M) ⟶
      (singleFunctor (SheafOfModules.{u} (structureSheafRing X)) d).obj
        ((modulePullback f).obj M) :=
  (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).map
      ((singleFunctorIsoCompQh (SheafOfModules.{u} (structureSheafRing Y)) d).hom.app M) ≫
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison f).app
      ((HomotopyCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) d).obj M) ≫
    DerivedCategory.Qh.map
      ((Functor.mapHomotopyCategorySingleFunctor (modulePullback f) d).hom.app M) ≫
    (singleFunctorIsoCompQh (SheafOfModules.{u} (structureSheafRing X)) d).inv.app
      ((modulePullback f).obj M)

/-- **The canonical map `H^d(Lf^*(M[-d])) ⟶ f^* M`**: `derivedToOrdinaryPullbackSingle` on
degree-`d` cohomology, followed by `homologySingleIso`. -/
def homologyDerivedPullbackSingleMap
    (M : SheafOfModules.{u} (structureSheafRing Y)) (d : ℤ) :
    (homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) d).obj
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).obj
          ((singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) d).obj M)) ⟶
      (modulePullback f).obj M :=
  (homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) d).map
      (derivedToOrdinaryPullbackSingle f M d) ≫
    (homologySingleIso ((modulePullback f).obj M) d).hom

/-- **`H^d(Lf^*(M[-d])) = f^* M`**, the identification [Stacks, Tag 0EX3] uses silently when it
writes `H^d(Lh^* Rf'_* F') = h^* R^d f'_* F'`.

Three of the four factors of `derivedToOrdinaryPullbackSingle` are components of natural
isomorphisms; the fourth is the derived-pullback comparison at the single complex, which
`isIso_homologyFunctor_map_derivedPullbackComparison_app` inverts on degree-`d` cohomology because
the single complex has zero terms above `d`. -/
theorem isIso_homologyDerivedPullbackSingleMap
    (M : SheafOfModules.{u} (structureSheafRing Y)) (d : ℤ) :
    IsIso (homologyDerivedPullbackSingleMap f M d) := by
  have hcomp : IsIso ((homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) d).map
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison f).app
        ((HomotopyCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) d).obj M))) :=
    isIso_homologyFunctor_map_derivedPullbackComparison_app f
      ((CochainComplex.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) d).obj M) d
      inferInstance
  rw [homologyDerivedPullbackSingleMap, derivedToOrdinaryPullbackSingle,
    Functor.map_comp, Functor.map_comp, Functor.map_comp]
  infer_instance

/-- **`H^d(Lf^*(M[-d])) ≅ f^* M`**, the canonical map
`homologyDerivedPullbackSingleMap` made an isomorphism. -/
def homologyDerivedPullbackSingleIso (M : SheafOfModules.{u} (structureSheafRing Y)) (d : ℤ) :
    (homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) d).obj
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).obj
          ((singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) d).obj M)) ≅
      (modulePullback f).obj M :=
  @asIso _ _ _ _ _ (isIso_homologyDerivedPullbackSingleMap f M d)

/-- **The step [Stacks, Tag 0EX3] displays.** For `K` with no cohomology above `d`, the top
cohomology of the derived pullback is the ordinary pullback of the top cohomology:

> `H^d(Lf^* K) = f^* H^d(K)`.

This is `derivedPullbackTopDegreeIsoSingle` followed by
`homologyDerivedPullbackSingleIso`. -/
def derivedPullbackTopDegreeIsoPullback
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) (d : ℤ)
    (hK : TStructure.t.IsLE K d) :
    (homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) d).obj
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).obj K) ≅
      (modulePullback f).obj
        ((homologyFunctor (SheafOfModules.{u} (structureSheafRing Y)) d).obj K) :=
  derivedPullbackTopDegreeIsoSingle f K d hK ≪≫ homologyDerivedPullbackSingleIso f _ d

/-- **Pullback of the top higher direct image, at the scheme-level spelling of the 0EX3
situation.** This is the `topDirectImagePullbackIso` of the statement `0EX3__top_direct_image_base_change`
with **one hypothesis the statement does not have**: that `Rf'_*(F'[0])` has no cohomology above
`d`. The statement derives that from conclusion (a) of the tag; here it is assumed, so the
declaration does not carry the statement's name and carries no tag.

Conclusion (a) does not supply `hLE` by itself — (a) is about `Functor.rightDerivedPlus`, the
homology of the derived functor on `D⁺`, while `hLE` is about the unbounded
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward` — but the comparison of
  those two models at one object is
available, so `hLE` **is** discharged:
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.isLE_derivedPushforward_baseChange`
(`DerivedModelCrossing.lean`). The unconditional form of this declaration therefore exists, as
`topDirectImagePullbackIso` in that module; it is kept separate from this one only because this
module cannot import it without a cycle.

`AlgebraicGeometry.Scheme.Modules.pullback h` and
`RingedSpaceModuleAdjunction.modulePullback h.toLRSHom.toShHom` are the same functor by `rfl`, as
are the two spellings of the category of modules, so no transport appears here. -/
def topDirectImagePullbackIso_of_isLE
    (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})
    (F' : S.X'.Modules) [F'.IsQuasicoherent]
    {Y'' : Scheme.{u}} (h : Y'' ⟶ S.Y')
    (hLE : TStructure.t.IsLE
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
        S.f'.toLRSHom.toShHom).obj
        ((singleFunctor S.X'.Modules 0).obj F')) (S.d : ℤ)) :
    (Scheme.Modules.pullback h).obj
      ((homologyFunctor S.Y'.Modules (S.d : ℤ)).obj
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
          S.f'.toLRSHom.toShHom).obj
          ((singleFunctor S.X'.Modules 0).obj F'))) ≅
      (homologyFunctor Y''.Modules (S.d : ℤ)).obj
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback h.toLRSHom.toShHom).obj
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
            S.f'.toLRSHom.toShHom).obj
            ((singleFunctor S.X'.Modules 0).obj F'))) :=
  (derivedPullbackTopDegreeIsoPullback h.toLRSHom.toShHom _ (S.d : ℤ) hLE).symm

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
