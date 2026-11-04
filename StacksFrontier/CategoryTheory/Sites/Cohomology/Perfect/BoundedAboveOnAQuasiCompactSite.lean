module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.IntervalDescent
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.FiniteSubfamily
import StacksCore.Tactic.StacksAttribute

/-!
# A perfect object on a quasi-compact site is bounded above

Let `(C, O)` be a ringed site whose terminal object is quasi-compact in the sense of
[Stacks, Tag 090H], and let `E` be a perfect object of `D(O)`. Then `E` is bounded above: there
is an integer `b` with `H^n(E) = 0` for every `n > b`.

Perfectness is a *local* condition — every object of the site is covered by objects over which
`E` has a strictly perfect model — and a strictly perfect complex is bounded, so `E` is locally
bounded above. What quasi-compactness of the terminal object adds is that finitely many members
of the covering already cover, so that the finitely many local bounds are dominated by a single
integer; vanishing of a cohomology sheaf is then checked on that covering.

## Main results

* `AlgebraicGeometry.RingedSite.exists_coversTop_isStrictlyPerfect_uniformBound`: over a
  quasi-compact terminal object, a perfect complex has a *finite* covering family on each
  member of which it has a strictly perfect model, all of them vanishing above one and the same
  degree.
* `AlgebraicGeometry.RingedSite.exists_isLE_of_isPerfect`: a perfect object of `D(O)` is bounded
  above.

## Implementation notes

**This file is deliberately untagged.** The statement is the quasi-compact global form of the
boundedness of a perfect complex. The two tags the Stacks project attaches to that circle of
ideas, 0BCJ and 08E8, are already registered in this repository for different cases — 0BCJ by
`StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.LocalRingStalks` and 08E8 by
`StacksFrontier.AlgebraicGeometry.PseudoCoherent.Noetherian.CoherentHomology`, the latter being the
Noetherian global form — and whether the quasi-compact case belongs under either attribute is a
scoping question for those tags, not one to settle by adding a second registration. That the
case proved here was genuinely absent is recorded in the repository
itself: the implementation notes of
`StacksFrontier/AlgebraicGeometry/Duality/DetectingBoundedness.lean`, lines 95-105, name the local
form and the Noetherian global form and state that "the quasi-compactness patch from the former
to a global bound over a merely quasi-compact quasi-separated `X` is not carried out anywhere",
which is why the `@[stacks 0GEM]` statement there carries `hP : P.IsLE nP` as a hypothesis.

**The shape of the argument** is the one
`Stacks.SheafOfModules.DerivedTensorProduct.hasFiniteTorDimension_of_locallyHasFiniteTorDimension`
uses for Tor amplitude: cut the covering down with
`CategoryTheory.GrothendieckTopology.exists_finite_ofArrows_mem_of_isQuasiCompactObject`, take a
single bound dominating the finitely many local ones, turn the covering sieve on the terminal
object into a family covering the final object with
`CategoryTheory.GrothendieckTopology.coversTop_iff_of_isTerminal`, and descend the vanishing
along `Stacks.SheafOfModules.isZero_of_coversTop`. Restriction to a slice is exact, so it
commutes with cohomology by
`StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso`; the restricted object is
computed by the strictly perfect model, which has no terms, hence no cohomology, above its
bound.

**Boundedness is read off the terms, not the cohomology, of the local model.** The `bounded`
field of `IsStrictlyPerfect` says that only finitely many terms are nonzero, so the set of
degrees in which the model is nonzero is bounded above; a complex with a zero term in degree `n`
has zero homology in degree `n`, by `CategoryTheory.ShortComplex.isZero_homology_of_isZero_X₂`.

## References

* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
* [Stacks Project, Tag 08FL](https://stacks.math.columbia.edu/tag/08FL)
* [Stacks Project, Tag 090H](https://stacks.math.columbia.edu/tag/090H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u d

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u})
variable [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{u}]
variable [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{u}]
variable [HasSheafify X.J AddCommGrpCat.{u}]
variable [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **A perfect complex over a quasi-compact terminal object has one bound on a finite
covering.** If the terminal object `U` is quasi-compact, a perfect complex `E` admits finitely
many objects `V i`, whose arrows to `U` generate a covering sieve, carrying strictly perfect
models of `E|_{V i}` all of whose terms vanish in degrees above one and the same integer.

The covering perfectness supplies at `U` is cut down to finitely many arrows, which
quasi-compactness permits, and the finitely many degrees above which the chosen models vanish
are dominated by a single one. -/
theorem exists_coversTop_isStrictlyPerfect_uniformBound
    (U : X.C) (hU : IsTerminal U) (hqc : X.J.IsQuasiCompactObject U)
    (E : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hE : X.IsPerfectComplex E) :
    ∃ (ι : Type u) (_ : Finite ι) (V : ι → X.C) (b : ℤ), X.J.CoversTop V ∧
      ∀ i, ∃ P : CochainComplex
          (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (V i))) ℤ,
        IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (V i)) P ∧
          (∀ n : ℤ, b < n → IsZero (P.X n)) ∧
          ∃ q : P ⟶ X.restrictComplex E (V i), QuasiIso q := by
  classical
  obtain ⟨S, hScov, hmodels⟩ := hE U
  obtain ⟨ι, hιfin, V, f, hfS, hcov⟩ :=
    GrothendieckTopology.exists_finite_ofArrows_mem_of_isQuasiCompactObject hqc S hScov
  have : Finite ι := hιfin
  choose P hP q hq using fun i : ι => hmodels (f i) (hfS i)
  have hlocal : ∀ i : ι, ∃ b : ℤ, ∀ n : ℤ, b < n → IsZero ((P i).X n) := by
    intro i
    obtain ⟨b, hb⟩ := (hP i).bounded.bddAbove
    refine ⟨b, fun n hn => ?_⟩
    by_contra hz
    exact absurd (hb (show n ∈ {j : ℤ | ¬ IsZero ((P i).X j)} from hz)) (by omega)
  choose b hb using hlocal
  obtain ⟨b₀, hb₀⟩ := (Set.finite_range b).bddAbove
  refine ⟨ι, hιfin, V, b₀,
    (X.J.coversTop_iff_of_isTerminal U hU V).2 ((Sieve.ofArrows_eq_ofObjects hU V f) ▸ hcov),
    fun i => ⟨P i, hP i, fun n hn => hb i n ?_, q i, hq i⟩⟩
  exact lt_of_le_of_lt (hb₀ (Set.mem_range_self i)) hn

variable [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
variable [∀ U : X.C, HasDerivedCategory.{d}
  (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))]

/-- **A perfect object of `D(O)` on a quasi-compact site is bounded above.** If the terminal
object of the site is quasi-compact in the sense of [Stacks, Tag 090H] and `E` is a perfect
object of `D(O)`, then `E` lies in cohomological degrees `≤ b` for some integer `b`.

Finitely many members of the covering supplied by perfectness already cover, by quasi-compactness,
and over each of them a strictly perfect model computes `E` and vanishes above one common degree
`b`. Above `b` the cohomology sheaves of `E` therefore restrict to zero on a family covering the
final object, so they vanish. -/
theorem exists_isLE_of_isPerfect
    (U : X.C) (hU : IsTerminal U) (hqc : X.J.IsQuasiCompactObject U)
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hE : X.IsPerfect E) : ∃ b : ℤ, E.IsLE b := by
  obtain ⟨Ecpx, hEcpx, ⟨e⟩⟩ := hE
  obtain ⟨ι, -, V, b, hcov, hmodels⟩ :=
    exists_coversTop_isStrictlyPerfect_uniformBound X U hU hqc Ecpx hEcpx
  refine ⟨b, ?_⟩
  rw [DerivedCategory.isLE_iff]
  intro n hn
  refine Stacks.SheafOfModules.isZero_of_coversTop hcov _ fun i => ?_
  obtain ⟨P, -, hPzero, q, hq⟩ := hmodels i
  set G := SheafOfModules.overFunctor.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O) (V i) with hG
  have hQq : IsIso (DerivedCategory.Q.map q) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso
      (C := SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (V i))) q).2 hq
  have hiso : G.mapDerivedCategory.obj E ≅ DerivedCategory.Q.obj P :=
    G.mapDerivedCategory.mapIso e.symm ≪≫ G.mapDerivedCategoryFactors.app Ecpx ≪≫
      (asIso (DerivedCategory.Q.map q)).symm
  have hPhom : IsZero ((DerivedCategory.homologyFunctor _ n).obj (DerivedCategory.Q.obj P)) :=
    IsZero.of_iso
      (ShortComplex.isZero_homology_of_isZero_X₂ (P.sc n) (by simpa using hPzero n hn))
      ((DerivedCategory.homologyFunctorFactors _ n).app P)
  exact (hPhom.of_iso ((DerivedCategory.homologyFunctor _ n).mapIso hiso)).of_iso
    ((StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso G n).app E).symm

end AlgebraicGeometry.RingedSite

end
