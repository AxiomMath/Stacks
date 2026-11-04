module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherentCohomologyUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentImpliesCartesian
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteCoherenceCokernels
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteCoherenceFiniteFamilies
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 08IK: the cohomology of a pseudo-coherent complex on a Noetherian algebraic space

Let `S` be a scheme, let `F` be a Noetherian algebraic space over `S` and let `E` be an object
of `D_QCoh(𝒪_F)`.  Stacks 08IK asserts, for every `m ∈ ℤ`, the equivalence of

1. `Hⁱ(E)` is coherent for `i ≥ m` and zero for `i ≫ 0`, and
2. `E` is `m`-pseudo-coherent,

and deduces that `E` is pseudo-coherent exactly when it is an object of `D⁻_Coh(𝒪_F)`.

**This file proves the coherence clause of (1) from (2), for every `m` and in every degree
`i ≥ m`, and nothing else of the tag.**  The vanishing clause of (1) and the implication
(1) ⇒ (2) are not available in this development; see "What is not proved here" below, which
names the missing substrate.

## Main results

* `AlgebraicGeometry.Space.isCoherentOnSite_homology_of_isPseudoCoherentFrom`: an
  `m`-pseudo-coherent object of `D(𝒪_F)` over a *locally* Noetherian algebraic space has
  coherent `Hⁱ` in every degree `i ≥ m` whose `Hⁱ` is quasi-coherent.  This is the content; the
  three statements below are its specializations to the hypotheses of the source.
* `AlgebraicGeometry.Space.isCoherentOnSite_homology_of_isPseudoCoherentFrom_of_lt`: in the
  degrees `i > m` the quasi-coherence hypothesis is not needed at all, being Stacks 08JL.
* `AlgebraicGeometry.Space.isCoherentOnSite_homology_of_isPseudoCoherentFrom_of_isNoetherian`:
  the same under the Noetherianity hypothesis of Stacks 08IK — **the coherence clause of
  Stacks 08IK (1), derived from (2)**.
* `AlgebraicGeometry.Space.isCoherentOnSite_homology_of_isPseudoCoherent_of_isNoetherian`: a
  pseudo-coherent object of `D(𝒪_F)` over a Noetherian algebraic space has coherent cohomology
  in every degree — **the coherence half of the final statement of Stacks 08IK**, the half of
  "`E` lies in `D⁻_Coh(𝒪_F)`" that does not mention boundedness.  Here no quasi-coherence
  hypothesis is needed: it is supplied by Stacks 08JL.
* `Stacks.SheafOfModules.isCoherentOnSite_free_of_unit`,
  `Stacks.SheafOfModules.isCoherentOnSite_of_isDirectSummandOfFiniteFree`,
  `Stacks.SheafOfModules.isCoherentOnSite_homology_of_terms` and
  `Stacks.SheafOfModules.isCoherentOnSite_homology_of_isStrictlyPerfect`: on an arbitrary ringed
  site whose structure sheaf is coherent, a finite free module is coherent, a direct summand of
  a finite free module is coherent, and the cohomology of a complex with coherent terms — in
  particular of a strictly perfect complex — is coherent.

## How the coherence clause is proved

The argument is the source's reduction to the affine case run on the slices of the small étale
site, exactly as `AlgebraicGeometry.Space.isQuasicoherentOnSite_homology_of_isPseudoCoherentFrom`
runs the proof of Stacks 08JL there, and it needs no comparison with the Zariski site of a chart.

Pseudo-coherence of a representative complex `K` gives, over every object `U` of the site, a
covering on whose members `K` is approximated above degree `m` by a strictly perfect complex `P`
of modules on the slice, with `Hⁱ(P) ⟶ Hⁱ(K)|_V` an isomorphism for `i > m` and an epimorphism
for `i = m`; in particular it is an **epimorphism for every `i ≥ m`**, which is the only thing
used below, and is why the two cases `i = m` and `i > m` are not separated.

Over a locally Noetherian algebraic space the structure sheaf is coherent
(`AlgebraicGeometry.Space.isCoherent_structureSheaf`, Stacks 07UB), hence so is its restriction
to every slice, coherence being hereditary on a site
(`Stacks.SheafOfModules.isCoherentOnSite_over`).  A finite free module on the slice is a finite
coproduct of copies of that restriction, so it is coherent by the direct sum clause of
Stacks 01BY (3); a direct summand of a finite free module is a subsheaf of finite type of one,
so it is coherent by the subsheaf clause Stacks 01BY (1); and the cohomology of a complex of
coherent modules is coherent by the kernel and cokernel clauses of Stacks 01BY (3).  So `Hⁱ(P)`
is coherent, and `Hⁱ(K)|_V` is of finite type, being the target of an epimorphism out of it.
Finite type is local on the site, so `Hⁱ(K)` is of finite type.

Finite type is not coherence, and the step from one to the other is where Noetherianity is used
a second time: a quasi-coherent module of finite type on a locally Noetherian algebraic space is
coherent, which is `AlgebraicGeometry.Space.isCoherentOnSite_of_isCartesian_of_isLocallyNoetherian`
(the finite-type half of Stacks 07UB) together with the unconditional
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isQuasicoherentOnSite` (Descent,
Proposition 03DX (2)) which supplies its base change hypothesis.  This is the one place where
quasi-coherence of `Hⁱ(E)` enters, and it is the hypothesis `E ∈ D_QCoh(𝒪_F)` of the source.

In degrees `i > m` the quasi-coherence of `Hⁱ(E)` is not an extra assumption at all: it is
Stacks 08JL, carried by
`AlgebraicGeometry.Space.isQuasicoherentOnSite_homology_of_isPseudoCoherentFrom_unconditional`.
It is genuinely needed in degree `i = m`, where the approximation yields only an epimorphism
onto `Hᵐ(E)` and quasi-coherence is not known to be closed under quotients — that is a clause of
Stacks 03M1, which this development does not have.

## What is not proved here

**The vanishing clause of (1), `Hⁱ(E) = 0` for `i ≫ 0`, is not proved, in either direction.**
Over a ringed space it is `AlgebraicGeometry.isBoundedAbove_of_isPseudoCoherentFrom`, whose
proof takes a strictly perfect model on an open neighbourhood of each *point*, reads off the
degree above which its terms vanish, and extracts a finite subcover by compactness of the
underlying topological space.  Neither half of that has an analogue here.  Pseudo-coherence on a
ringed site is indexed by objects and covering sieves, not by points and opens, and the one
statement relating `AlgebraicGeometry.RingedSite.IsPseudoCoherentFrom` to
`AlgebraicGeometry.RingedSpace.IsPseudoCoherentFrom` —
`AlgebraicGeometry.RingedSpace.PseudoCoherence.isPseudoCoherentFrom_ringedSite` — is for the
site of *opens* of a ringed space, where the site is a lattice of opens and the comparison of
local models is Mathlib's `TopologicalSpace.Opens.sheafOfModulesEquivOver`; the small étale site
of an algebraic space is not of that form, so nothing here applies to it; and quasi-compactness of
an algebraic space, `AlgebraicGeometry.Space.IsQuasiCompactSpace`, is not known in this development
to give a covering family of the small étale site indexed by a finite type — the one
finite-refinement statement available,
`AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_refinement`, requires the object being
covered to be affine, and its own documentation records that the objects of the small étale site
include infinite disjoint unions of affine charts over which no covering has a finite refinement.

**The implication (1) ⇒ (2) is not proved.**  Its scheme-level counterpart,
`AlgebraicGeometry.isPseudoCoherentFrom_iff_coherent_homology` (Stacks 08E8), is built from
`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_isLE_homology` and
`AlgebraicGeometry.isPseudoCoherentFrom_singleFunctor_zero_of_isCoherent`, and neither has a
ringed-site form: there is no statement anywhere in this development that a coherent module
placed in a single degree is pseudo-coherent on a ringed site, which is the arithmetic heart of
that implication (it asks for arbitrarily long finite free resolutions of a coherent module,
étale-locally).  For the same reason the "in particular" of the tag is available only in the
direction proved here, and only in its coherence half.

## Implementation notes

The module universe is the universe `u` of the structure rings, as in Stacks 08FT and in
`StacksFrontier/AlgebraicGeometry/Spaces/PseudoCoherentCohomology.lean`: the strictly perfect local
models are built from the structure sheaf.  It is also the universe at which the cokernel clause
of Stacks 01BY (3) on a site, `Stacks.SheafOfModules.isCoherentOnSite_cokernel`, is available,
and the universe at which Descent, Proposition 03DX (2) is available for the small étale site.

The locality step is `Stacks.SheafOfModules.isFiniteType_of_over`, whose index type is free,
applied to the family of all arrows of all the coverings supplied by pseudo-coherence; that
presieve-flattening is the same device as in
`StacksFrontier/AlgebraicGeometry/Spaces/PseudoCoherentCohomology.lean`.

The generic lemmas of the first section take coherence of the structure sheaf as an explicit
hypothesis rather than an instance, because the only source of it for the small étale site of an
algebraic space is the instance `AlgebraicGeometry.Space.isCoherent_structureSheaf`, which is
stated for the site itself and is transported to the slices by a theorem rather than found by
synthesis.

## References

* [Stacks Project, Tag 08IK](https://stacks.math.columbia.edu/tag/08IK)
* [Stacks Project, Tag 08E8](https://stacks.math.columbia.edu/tag/08E8)
* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
* [Stacks Project, Tag 08JL](https://stacks.math.columbia.edu/tag/08JL)
* [Stacks Project, Tag 07UB](https://stacks.math.columbia.edu/tag/07UB)
* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03EA](https://stacks.math.columbia.edu/tag/03EA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.SheafOfModules

universe u v w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The `R`-modules whose sections live in the universe of the sections of `R` form an abelian
category.

The content is `SheafOfModules.instAbelian`, Mathlib's abelian structure on the sheaves of
modules over a sheaf of rings.  It is named, and given a raised priority, for the reason
recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/PseudoCoherentCohomologyUnconditional.lean`:
`Stacks.Cohomology.SiteModules.moduleSheavesAbelian` answers the same goal with the module
universe left as the join of the universes of the site, the rings and a free one, and a search
reaching it first ends in a universe constraint with no solution rather than in a failure it can
recover from. -/
noncomputable local instance (priority := high) modules_abelian :
    Abelian (SheafOfModules.{w} R) :=
  SheafOfModules.instAbelian R

/-- **A finite free module on a ringed site with coherent structure sheaf is coherent.**  It is
a finite coproduct of copies of the structure sheaf, and coherence is closed under finite
coproducts by the direct sum clause of Stacks 01BY (3). -/
theorem isCoherentOnSite_free_of_unit
    (hR : SheafOfModules.IsCoherentOnSite (SheafOfModules.unit R)) (n : ℕ) :
    SheafOfModules.IsCoherentOnSite (SheafOfModules.free (R := R) (ULift.{w} (Fin n))) :=
  isCoherentOnSite_sigma (fun _ : ULift.{w} (Fin n) ↦ SheafOfModules.unit R) fun _ ↦ hR

/-- **A direct summand of a finite free module on a ringed site with coherent structure sheaf is
coherent.**  A retraction `i : M ⟶ 𝒪^{⊕n}`, `r : 𝒪^{⊕n} ⟶ M` with `i ≫ r = 𝟙` makes `i` a
monomorphism and `r` an epimorphism; the first exhibits `M` as a subsheaf of a coherent sheaf
and the second makes it of finite type, so the subsheaf clause Stacks 01BY (1) applies. -/
theorem isCoherentOnSite_of_isDirectSummandOfFiniteFree
    (hR : SheafOfModules.IsCoherentOnSite (SheafOfModules.unit R))
    {M : SheafOfModules.{w} R} (hM : IsDirectSummandOfFiniteFree R M) :
    SheafOfModules.IsCoherentOnSite M := by
  obtain ⟨n, i, r, hir⟩ := (isDirectSummandOfFiniteFree_iff_free R M).1 hM
  have hfree := isCoherentOnSite_free_of_unit hR n
  have : IsSplitMono i := ⟨⟨r, hir⟩⟩
  have : IsSplitEpi r := ⟨⟨i, hir⟩⟩
  exact isCoherentOnSite_of_mono i hfree
    (isFiniteType_of_locallySurjective r.val (exists_cover_preimage_of_epi r) hfree.isFiniteType)

/-- **The cohomology of a cochain complex of coherent modules on a ringed site is coherent.**
The cocycles in degree `i` are the kernel of the `i`-th differential and the cohomology is the
cokernel of the map into them from degree `i - 1`, so this is the kernel clause and then the
cokernel clause of Stacks 01BY (3). -/
theorem isCoherentOnSite_homology_of_terms (P : CochainComplex (SheafOfModules.{w} R) ℤ)
    (hP : ∀ j : ℤ, SheafOfModules.IsCoherentOnSite (P.X j)) (i : ℤ) :
    SheafOfModules.IsCoherentOnSite (P.homology i) := by
  have hcyc : SheafOfModules.IsCoherentOnSite (P.cycles i) :=
    isCoherentOnSite_of_iso
      (IsLimit.conePointUniqueUpToIso (kernelIsKernel (P.d i (i + 1)))
        (P.cyclesIsKernel i (i + 1) (by simp)))
      (isCoherentOnSite_kernel (hP i) (hP (i + 1)) (P.d i (i + 1)))
  exact isCoherentOnSite_of_iso
    (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel (P.toCycles (i - 1) i))
      (P.homologyIsCokernel (i - 1) i (by simp)))
    (isCoherentOnSite_cokernel (P.toCycles (i - 1) i) (hP (i - 1)) hcyc)

/-- **The cohomology of a strictly perfect complex on a ringed site with coherent structure
sheaf is coherent.**  Its terms are direct summands of finite free modules, hence coherent, and
`Stacks.SheafOfModules.isCoherentOnSite_homology_of_terms` applies. -/
theorem isCoherentOnSite_homology_of_isStrictlyPerfect
    (hR : SheafOfModules.IsCoherentOnSite (SheafOfModules.unit R))
    (P : CochainComplex (SheafOfModules.{w} R) ℤ) (hP : IsStrictlyPerfect R P) (i : ℤ) :
    SheafOfModules.IsCoherentOnSite (P.homology i) :=
  isCoherentOnSite_homology_of_terms P
    (fun j ↦ isCoherentOnSite_of_isDirectSummandOfFiniteFree hR (hP.termDirectSummand j)) i

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- The `𝒪_F`-modules on a slice of the small étale site, with sections in the universe of the
schemes, form an abelian category.

This is the slice counterpart of `AlgebraicGeometry.Space.modules_abelian`, named and given a
raised priority for the same reason: left to synthesis the goal is answered by an instance whose
module universe is the join of the universes of the site, the rings and a free one, which is
never the universe `u` of the schemes. -/
noncomputable local instance (priority := high) modules_over_abelian
    (V : (smallEtaleRingedSite B S hS F hF).C) :
    Abelian (SheafOfModules.{u}
      (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).over V)) :=
  SheafOfModules.instAbelian _

/-- **The structure sheaf of a locally Noetherian algebraic space is coherent on every slice of
its small étale site.**  Coherence of the structure sheaf itself is Stacks 07UB,
`AlgebraicGeometry.Space.isCoherent_structureSheaf`, and coherence on a site is hereditary for
restriction to a slice, `Stacks.SheafOfModules.isCoherentOnSite_over`; the restriction of the
structure sheaf to a slice is the structure sheaf of the slice on the nose. -/
theorem isCoherentOnSite_unit_over
    [Fact (HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} ↦ IsLocallyNoetherian V))]
    (V : (smallEtaleRingedSite B S hS F hF).C) :
    SheafOfModules.IsCoherentOnSite
      (SheafOfModules.unit
        (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).over V)) :=
  Stacks.SheafOfModules.isCoherentOnSite_over
    (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)))
    (isCoherent_structureSheaf B S hS F hF).toIsCoherentOnSite V

/-- **The cohomology of an `m`-pseudo-coherent object of `D(𝒪_F)` is of finite type above `m`.**

Over every object of the small étale site, pseudo-coherence supplies a covering on whose members
`Hⁱ(E)` receives an epimorphism from `Hⁱ(P)` with `P` strictly perfect on the slice — an
isomorphism when `i > m` and an epimorphism when `i = m`.  On a locally Noetherian algebraic
space `Hⁱ(P)` is coherent, hence of finite type, and finite type passes along an epimorphism and
is local on the site. -/
theorem isFiniteType_homology_of_isPseudoCoherentFrom
    [Fact (HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} ↦ IsLocallyNoetherian V))]
    (E : DerivedCategory (Modules.{u, u} B S hS F hF)) (m i : ℤ)
    (hE : (smallEtaleRingedSite B S hS F hF).IsPseudoCoherentFrom E m) (hi : m ≤ i) :
    PresheafOfModules.IsFiniteType (smallEtaleRingedSite B S hS F hF).J
      ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS F hF) i).obj E).val := by
  classical
  set Y := smallEtaleRingedSite B S hS F hF with hY
  obtain ⟨K, hK, ⟨e⟩⟩ := hE
  choose T hT happrox using hK
  -- The arrows of all the coverings, as a family of objects of the site.
  set A := Σ U : Y.C, Σ V : Y.C, {f : V ⟶ U // T U f} with hA
  set Z : A → Y.C := fun a ↦ a.2.1 with hZ
  have hcover : Y.J.CoversTop Z := by
    intro W
    refine Y.J.superset_covering ?_ (hT W)
    rintro P g ⟨V, h, f, hf, rfl⟩
    exact ⟨⟨W, V, f, hf⟩, ⟨h⟩⟩
  have hft : PresheafOfModules.IsFiniteType Y.J (K.homology i).val := by
    refine Stacks.SheafOfModules.isFiniteType_of_over (K.homology i) Z hcover fun a ↦ ?_
    obtain ⟨P, hP, α, hiso, hepi⟩ := happrox a.1 a.2.2.1 a.2.2.2
    have hhom : (SheafOfModules.overFunctor
        ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (Z a)).PreservesHomology := by
      have : PreservesFiniteLimits (SheafOfModules.overFunctor.{u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (Z a)) :=
        SheafOfModules.preservesFiniteLimits_overFunctor _ _
      have : (SheafOfModules.overFunctor.{u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (Z a)).PreservesEpimorphisms :=
        Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesEpimorphisms (Z a)
      exact Functor.preservesHomology_of_preservesEpis_and_kernels _
    have hepi' : Epi (HomologicalComplex.homologyMap α i) := by
      rcases eq_or_lt_of_le hi with h | h
      · exact h ▸ hepi
      · have := hiso i h
        infer_instance
    refine Stacks.SheafOfModules.presheaf_isFiniteType_of_iso
      ((SheafOfModules.forget _).mapIso ((K.sc i).mapHomologyIso
        (SheafOfModules.overFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (Z a)))) ?_
    exact Stacks.SheafOfModules.isFiniteType_of_locallySurjective
      (HomologicalComplex.homologyMap α i).val
      (Stacks.SheafOfModules.exists_cover_preimage_of_epi (HomologicalComplex.homologyMap α i))
      (Stacks.SheafOfModules.isCoherentOnSite_homology_of_isStrictlyPerfect
        (isCoherentOnSite_unit_over B S hS F hF (Z a)) P hP i).isFiniteType
  exact Stacks.SheafOfModules.presheaf_isFiniteType_of_iso
    ((SheafOfModules.forget ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).mapIso
      ((DerivedCategory.homologyFunctorFactors _ i).symm.app K ≪≫
        (DerivedCategory.homologyFunctor _ i).mapIso e)) hft

/-- **The coherence clause of Stacks 08IK (1), derived from (2), over a locally Noetherian
algebraic space.**  Let `F` be a locally Noetherian algebraic space over `S`, let `E` be an
object of `D(𝒪_F)` which is `m`-pseudo-coherent and let `i ≥ m` be a degree in which `Hⁱ(E)` is
quasi-coherent.  Then `Hⁱ(E)` is a coherent `𝒪_F`-module.

The quasi-coherence hypothesis is the hypothesis `E ∈ D_QCoh(𝒪_F)` of the source, read in the
single degree in which it is used.  For `i > m` it is automatic, being Stacks 08JL; see
`AlgebraicGeometry.Space.isQuasicoherentOnSite_homology_of_isPseudoCoherentFrom_unconditional`.

Local Noetherianity rather than Noetherianity is enough, which is a generalization of the
source; the statement under the source's own hypothesis is
`AlgebraicGeometry.Space.isCoherentOnSite_homology_of_isPseudoCoherentFrom_of_isNoetherian`. -/
theorem isCoherentOnSite_homology_of_isPseudoCoherentFrom
    (hN : HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} ↦ IsLocallyNoetherian V))
    (E : DerivedCategory (Modules.{u, u} B S hS F hF)) (m i : ℤ)
    (hE : (smallEtaleRingedSite B S hS F hF).IsPseudoCoherentFrom E m) (hi : m ≤ i)
    (hqc : ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS F hF) i).obj E).IsQuasicoherentOnSite) :
    SheafOfModules.IsCoherentOnSite
      ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS F hF) i).obj E) := by
  have := Fact.mk hN
  exact isCoherentOnSite_of_isCartesian_of_isLocallyNoetherian B S hS F hF _
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF _ hqc)
    (isFiniteType_homology_of_isPseudoCoherentFrom B S hS F hF E m i hE hi)

/-- **Above the approximation degree the quasi-coherence hypothesis is not needed.**  Let `F` be
a locally Noetherian algebraic space over `S` and let `E` be an `m`-pseudo-coherent object of
`D(𝒪_F)`.  Then `Hⁱ(E)` is coherent for every `i > m`, with no hypothesis on `E` beyond
pseudo-coherence: quasi-coherence of `Hⁱ(E)` in those degrees is Stacks 08JL.

The hypothesis `E ∈ D_QCoh(𝒪_F)` of Stacks 08IK is therefore used in exactly one degree, `i = m`,
where the local approximation gives only an epimorphism onto `Hᵐ(E)`. -/
theorem isCoherentOnSite_homology_of_isPseudoCoherentFrom_of_lt
    (hN : HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} ↦ IsLocallyNoetherian V))
    (E : DerivedCategory (Modules.{u, u} B S hS F hF)) (m i : ℤ)
    (hE : (smallEtaleRingedSite B S hS F hF).IsPseudoCoherentFrom E m) (hi : m < i) :
    SheafOfModules.IsCoherentOnSite
      ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS F hF) i).obj E) :=
  isCoherentOnSite_homology_of_isPseudoCoherentFrom B S hS F hF hN E m i hE hi.le
    (isQuasicoherentOnSite_homology_of_isPseudoCoherentFrom_unconditional
      B S hS F hF E m i hE hi)

/-- **Stacks 08IK, the coherence clause of (1) derived from (2).**  Let `S` be a scheme, let `F`
be a Noetherian algebraic space over `S` and let `E` be an object of `D_QCoh(𝒪_F)`.  If `E` is
`m`-pseudo-coherent then `Hⁱ(E)` is coherent for every `i ≥ m`.

The remaining clause of (1), that `Hⁱ(E)` vanishes for `i ≫ 0`, and the converse implication
(1) ⇒ (2) are not proved in this development; the module documentation names the missing
substrate for each.

Only local Noetherianity of `F` is used, which is the third component of Stacks 03EA; the
quasi-compactness and quasi-separatedness components are not.  The underlying statement with
that hypothesis alone is
`AlgebraicGeometry.Space.isCoherentOnSite_homology_of_isPseudoCoherentFrom`.

The quasi-coherence hypothesis is the hypothesis `E ∈ D_QCoh(𝒪_F)` of the source, read in the
single degree in which it is used, and it is needed only in the degree `i = m`:
`AlgebraicGeometry.Space.isCoherentOnSite_homology_of_isPseudoCoherentFrom_of_lt` is the same
conclusion for `i > m` with no hypothesis on `E` beyond pseudo-coherence. -/
@[stacks 08IK "(2) gives the coherence clause of (1)"]
theorem isCoherentOnSite_homology_of_isPseudoCoherentFrom_of_isNoetherian
    (hZ : B.Contains (⊤_ Scheme.{u})) (hFN : IsNoetherian B S hS hZ F)
    (E : DerivedCategory (Modules.{u, u} B S hS F hF)) (m i : ℤ)
    (hE : (smallEtaleRingedSite B S hS F hF).IsPseudoCoherentFrom E m) (hi : m ≤ i)
    (hqc : ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS F hF) i).obj E).IsQuasicoherentOnSite) :
    SheafOfModules.IsCoherentOnSite
      ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS F hF) i).obj E) :=
  isCoherentOnSite_homology_of_isPseudoCoherentFrom B S hS F hF hFN.2.2 E m i hE hi hqc

/-- **Stacks 08IK, the coherence half of the final statement.**  Let `S` be a scheme, let `F` be
a Noetherian algebraic space over `S` and let `E` be a pseudo-coherent object of `D(𝒪_F)`.  Then
`Hⁱ(E)` is a coherent `𝒪_F`-module in every degree.

This is the half of "`E` is an object of `D⁻_Coh(𝒪_F)`" that does not mention boundedness; the
boundedness half is not proved here, and neither is the converse.  No quasi-coherence hypothesis
is needed: a pseudo-coherent object lies in `D_QCoh(𝒪_F)` by Stacks 08JL,
`AlgebraicGeometry.Space.derivedCategoryB_of_isPseudoCoherent_unconditional`. -/
@[stacks 08IK "pseudo-coherent gives coherent cohomology"]
theorem isCoherentOnSite_homology_of_isPseudoCoherent_of_isNoetherian
    (hZ : B.Contains (⊤_ Scheme.{u})) (hFN : IsNoetherian B S hS hZ F)
    (E : DerivedCategory (Modules.{u, u} B S hS F hF))
    (hE : (smallEtaleRingedSite B S hS F hF).IsPseudoCoherent E) (i : ℤ) :
    SheafOfModules.IsCoherentOnSite
      ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS F hF) i).obj E) := by
  obtain ⟨K, hK, ⟨e⟩⟩ := hE
  exact isCoherentOnSite_homology_of_isPseudoCoherentFrom_of_isNoetherian B S hS F hF hZ hFN E
    i i ⟨K, hK i, ⟨e⟩⟩ le_rfl
    (derivedCategoryB_of_isPseudoCoherent_unconditional B S hS F hF E ⟨K, hK, ⟨e⟩⟩ i)

end AlgebraicGeometry.Space

end
