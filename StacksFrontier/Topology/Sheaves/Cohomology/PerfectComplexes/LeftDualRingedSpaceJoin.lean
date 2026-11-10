module

public import StacksFrontier.AlgebraicGeometry.RingedSpace.FlatKFlatResolution
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.LeftDualOnARingedSpace
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.Defs
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.LeftDualDirectSummand

/-!
# The ringed-site and ringed-space readings of Stacks 0FPD are the same reading

Stacks 0FPD has two conclusions for an object `M` of `D(O_X)` with a left dual: **(a)** `M` is
perfect, and **(b)** the left dual is the one constructed in Example 0FPC. The two are proved in
two different idioms, and a carrier for the whole tag has to state both at once:

* **(b)** is proved in
  `StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.LeftDualOnARingedSpace`
  over a sheaf of rings `Rc` on a topological space, with the pairing taken in
  `AlgebraicGeometry.RingedSite.derivedMonoidalStructure (Stacks.SheafOfModules.ringedSite Rc)`,
  the ringed-*site* spelling of Stacks 0FPB;
* **(a)**, whose chain-level steps are
  `StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.LeftDualLocalCoevaluation` and
  `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoproductLocalFiniteSum`, has to be proved for a
  ringed space `X` with the pairing in
  `Stacks.Cohomology.MonoidalDerived.derivedCategoryMonoidalCategory X`, because the perfectness
  machinery it ends at — Tag 08CM, Tag 08CP, Tag 08CQ, Tag 08CR, Tag 08CS — is stated for a
  ringed space at a general universe, while the ringed-site perfectness of Tag 08G5 is pinned to
  `RingedSite.{u, u, 0}` and Tags 08G7 and 08GA to `RingedSite.{0, 0, 0}`.

Whether the two monoidal structures are the same was not recorded anywhere, and it is the whole
question of whether a single declaration can state both conclusions. **They are the same, on the
nose:** `derivedCategoryMonoidalCategory_eq_ringedSite` below is `rfl`. So conclusion (b) is
available verbatim for a pairing in the ringed-space structure, which is
`isIso_derivedDualToLeftDual_ringedSpace` and `whiskerRight_derivedDualToLeftDual_ringedSpace`
below, and nothing stands between the two halves of the tag but conclusion (a) itself.

The identification needs the derived category to be the **standard** model: the ringed-site
declarations fix the derived-category hom universe at `u + 1` through
`CategoryTheory.HasDerivedCategory.standard`, which is in force in every file of the duality
cluster, whereas the ringed-space perfectness statements leave it free. At a free hom universe
`d` the two structures are not even of the same type — the elaborator reports
`MonoidalCategory.{u + 1, u + 1} … but is expected to have type MonoidalCategory.{d, u + 1} …` —
so the join is a statement about the standard model and is stated here as such.

## The K-flatness bridge

Stacks 06YF, `AlgebraicGeometry.RingedSpace.exists_isKFlat_isFlat_quasiIso_epi`, produces a
K-flat resolution with flat terms in the predicate `Stacks.SheafOfModules.IsKFlat`, while the
monoidal cluster — and therefore the comparison of the derived tensor product with the total
tensor complex that
`Stacks.Cohomology.LeftDualPerfect.exists_local_complexMap_coevaluation` consumes — uses
`Stacks.SheafOfModules.DerivedMonoidal.KFlat`. No lemma related the two. They are **definitionally
the same predicate**: both say that tensoring with the complex carries acyclic complexes to
acyclic complexes, one through `Stacks.SheafOfModules.Tensor.tensorComplex` and the other through
`CochainComplex.KFlatBifunctor.KFlat` at `Stacks.SheafOfModules.Tensor.sheafTensor`, and those are
one term. `isKFlat_iff_kFlat` below is `Iff.rfl`, and `exists_kFlat_quasiIso_epi` is Stacks 06YF
in the spelling the coevaluation step needs — which closes the only binder of that step whose
inhabitant was not yet named. Stacks 06YF's further clause, that the terms of the resolution are
flat, is *not* restated: `SheafOfModules.IsFlat` leaves its ring sheaf implicit, and solving it
against the `Mod` spelling asks the elaborator to unify `Stacks.SheafOfModules.Tensor.ringSheaf`
with `commRingSheafToRingSheaf` applied to a metavariable, which it will not do. A consumer that
needs flat terms — the inclusion `Tot(K ⊗ N) ⊆ Tot(M ⊗ N)` of the next step does — applies Stacks
06YF directly, in its own spelling.

## Main results

* `Stacks.Cohomology.LeftDualPerfect.isKFlat_iff_kFlat`: the two K-flatness predicates agree.
* `Stacks.Cohomology.LeftDualPerfect.exists_kFlat_quasiIso_epi`: **Stacks 06YF** in the `KFlat`
  spelling — every complex of `O_X`-modules receives a degreewise epimorphic quasi-isomorphism
  from a K-flat complex.
* `Stacks.Cohomology.LeftDualPerfect.derivedCategoryMonoidalCategory_eq_ringedSite`: **the join.**
  The monoidal structure of Stacks 0FPB on `D(O_X)` for a ringed space is the ringed-site
  structure at the site of opens of `X`, by `rfl`.
* `Stacks.Cohomology.LeftDualPerfect.derivedDualIsoLeftDual_ringedSpace` and
  `Stacks.Cohomology.LeftDualPerfect.leftDualIsoDerivedDual_ringedSpace`: **conclusion (b) of
  Stacks 0FPD, read for a pairing in the ringed-space monoidal structure** — the identification
  `M^∨ ≅ N` and its inverse. This is the form a whole-tag carrier would use.

**One measurement a reader needs.** The join being `rfl` does *not* make the two spellings
interchangeable for instance *retrieval*. A pairing of type
`@CategoryTheory.ExactPairing _ _ (derivedCategoryMonoidalCategory X) M N`, seated by `letI`, is
not found for a goal `@CategoryTheory.ExactPairing _ _ (RingedSite.derivedMonoidalStructure
(ringedSite X.sheaf)) M N`: the monoidal structure is an instance argument of `ExactPairing`, and
synthesis does not unfold `derivedCategoryMonoidalCategory` to see that the two agree. So a
statement of (b) at the ringed space must not mention `ε_`, `▷` or
`AlgebraicGeometry.RingedSite.derivedDualToLeftDual`, all of which take the pairing as an
instance; it must be stated in the instance-free form `M^∨ ≅ N`, where the pairing is passed
explicitly and the crossing is a single definitional unification at the application. The
evaluation compatibility that pins the identification down —
`Stacks.SheafOfModules.whiskerRight_derivedDualToLeftDualMonoidal` — is therefore left in the
ringed-site spelling where it is proved; it is about the same morphism, by the join.

Nothing below is a clause of a tag; these are re-readings of conclusion (b) in a second idiom.
The whole tag is stated, for one pairing, by
`Stacks.Cohomology.LeftDualPerfect.isPerfect_and_isIso_derivedDualToLeftDual` of
`StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.LeftDualIsPerfect`.

## References

* [Stacks Project, Tag 0FPD](https://stacks.math.columbia.edu/tag/0FPD)
* [Stacks Project, Tag 0FPV](https://stacks.math.columbia.edu/tag/0FPV)
* [Stacks Project, Tag 0FPC](https://stacks.math.columbia.edu/tag/0FPC)
* [Stacks Project, Tag 0FPB](https://stacks.math.columbia.edu/tag/0FPB)
* [Stacks Project, Tag 0FFP](https://stacks.math.columbia.edu/tag/0FFP)
* [Stacks Project, Tag 06YF](https://stacks.math.columbia.edu/tag/06YF)
* [Stacks Project, Tag 08CM](https://stacks.math.columbia.edu/tag/08CM)
* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry TopologicalSpace
open Stacks.SheafOfModules.DerivedMonoidal Stacks.Cohomology.MonoidalDerived

universe u

namespace Stacks.Cohomology.LeftDualPerfect

/-! ### The K-flatness bridge -/

section KFlatBridge

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The two K-flatness predicates of this development agree.**
`Stacks.SheafOfModules.IsKFlat`, which Stacks 06YF produces, and
`Stacks.SheafOfModules.DerivedMonoidal.KFlat`, which the monoidal cluster consumes, are the same
predicate: both say that tensoring with the complex preserves acyclicity, one spelled through
`Stacks.SheafOfModules.Tensor.tensorComplex` and the other through
`CochainComplex.KFlatBifunctor.KFlat` at `Stacks.SheafOfModules.Tensor.sheafTensor`, and those
are one term. -/
theorem isKFlat_iff_kFlat (K : CochainComplex (Mod R) ℤ) :
    Stacks.SheafOfModules.IsKFlat R K ↔ KFlat R K :=
  Iff.rfl

end KFlatBridge

/-! ### Stacks 06YF in the spelling the coevaluation step needs -/

section Resolution

variable (X : RingedSpace.{u, u})

/-- `⊗_{O_X}` is additive in its first variable, pinned by hand because the library instance ties
the sections universe to the site universes as `max u v`, which instance synthesis cannot solve
against the diagonal `u` of this cluster while those universes are still metavariables. This is
the pinning of `StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.LeftDualOnARingedSpace` read
at a ringed space. -/
local instance additiveSheafTensorSpace :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).Additive :=
  Stacks.SheafOfModules.Tensor.sheafTensor_additive
    (J := Opens.grothendieckTopology X.carrier) X.sheaf

/-- `ℱ ⊗_{O_X} -` is additive, pinned for the same reason. -/
local instance additiveSheafTensorObjSpace (M : Mod X.sheaf) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj M).Additive :=
  Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive
    (J := Opens.grothendieckTopology X.carrier) X.sheaf M

/-- The total complexes of the tensor double complexes exist, pinned for the same reason. -/
local instance hasMapBifunctorSpace (K₁ K₂ : CochainComplex (Mod X.sheaf) ℤ) :
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf) (ComplexShape.up ℤ) :=
  Stacks.SheafOfModules.Tensor.hasMapBifunctor_sheafTensor
    (J := Opens.grothendieckTopology X.carrier) X.sheaf K₁ K₂

/-- **Stacks 06YF in the `KFlat` spelling.** Every complex of `O_X`-modules on a ringed space
receives a quasi-isomorphism, epimorphic in every degree, from a complex that is K-flat for
`Stacks.SheafOfModules.DerivedMonoidal.KFlat` and whose terms are flat.

This is `AlgebraicGeometry.RingedSpace.exists_isKFlat_isFlat_quasiIso_epi` read through
`isKFlat_iff_kFlat`. It is what names the inhabitant of the K-flatness binders of
`Stacks.Cohomology.LeftDualPerfect.exists_local_complexMap_coevaluation`: that step needs a
K-flat representative of each of the two objects, and needs the terms of the second one flat,
which is exactly what Stacks 06YF supplies. -/
theorem exists_kFlat_quasiIso_epi (G : CochainComplex (Mod X.sheaf) ℤ) :
    ∃ (K : CochainComplex (Mod X.sheaf) ℤ) (s : K ⟶ G),
      KFlat X.sheaf K ∧ QuasiIso s ∧ ∀ i : ℤ, Epi (s.f i) := by
  obtain ⟨K, s, hK, -, hqi, hepi⟩ :=
    AlgebraicGeometry.RingedSpace.exists_isKFlat_isFlat_quasiIso_epi X G
  exact ⟨K, s, hK, hqi, hepi⟩

end Resolution

/-! ### The join -/

section Join

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSpace.{u, u})

/-- **The join of the two readings of Stacks 0FPB.** The monoidal structure on `D(O_X)` that the
ringed-space statements of this development use is, on the nose, the ringed-site structure at the
site of opens of `X` that the ringed-site statements use.

This is what makes a single declaration able to state both conclusions of Stacks 0FPD: conclusion
(a) must be proved in the ringed-space idiom, because the perfectness machinery of Tags 08CM to
08CS is universe-general only there, while conclusion (b) is proved in the ringed-site idiom. The
derived category is the standard model, which is what fixes the hom universe on both sides. -/
theorem derivedCategoryMonoidalCategory_eq_ringedSite :
    derivedCategoryMonoidalCategory X =
      AlgebraicGeometry.RingedSite.derivedMonoidalStructure
        (Stacks.SheafOfModules.ringedSite X.sheaf) :=
  rfl

variable (M N : DerivedModules X.sheaf)

/-- **Conclusion (b) of Stacks 0FPD, read for a pairing in the ringed-space monoidal structure of
Stacks 0FPB.** If `N` is a left dual of `M` in `D(O_X)` then the dual object
`M^∨ = RSheafHom(M, O_X)` of Example 0FPC is isomorphic to `N`, by the morphism that the pairing
matches with the evaluation of Example 0FPC.

This is `Stacks.SheafOfModules.derivedDualIsoLeftDual` with the pairing taken in
`derivedCategoryMonoidalCategory X` rather than in the ringed-site structure, the two being the
same by `derivedCategoryMonoidalCategory_eq_ringedSite`. The conclusion mentions no monoidal
structure at all, which is what lets the crossing be a single definitional unification at the
application; see the module docstring for why a form mentioning `ε_` or `▷` would not elaborate.

It carries no tag; the whole tag is
`Stacks.Cohomology.LeftDualPerfect.isPerfect_and_isIso_derivedDualToLeftDual`. -/
def derivedDualIsoLeftDual_ringedSpace
    (pair : letI := derivedCategoryMonoidalCategory X; ExactPairing M N) :
    Stacks.SheafOfModules.derivedDual X.sheaf M ≅ N :=
  Stacks.SheafOfModules.derivedDualIsoLeftDual X.sheaf M N pair

/-- **Conclusion (b) of Stacks 0FPD in the direction the source states it**, read for a pairing in
the ringed-space monoidal structure: a left dual `N` of `M` in `D(O_X)` is the dual object
`M^∨ = RSheafHom(M, O_X)` of Example 0FPC. -/
def leftDualIsoDerivedDual_ringedSpace
    (pair : letI := derivedCategoryMonoidalCategory X; ExactPairing M N) :
    N ≅ Stacks.SheafOfModules.derivedDual X.sheaf M :=
  (derivedDualIsoLeftDual_ringedSpace X M N pair).symm

end Join

end Stacks.Cohomology.LeftDualPerfect

end
