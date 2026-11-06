module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionExists
public import StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZeroSubcomplexOnASite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.DerivedExistence
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorsOnDerivedCategories

/-!
# A bounded above representative whose terms are presented as sums of extensions by zero

Let `(C, O)` be a ringed site and let `K` be a complex of `O`-modules with `H^i(K) = 0` for
`i > b`. Then `K` receives a quasi-isomorphism from a complex `P` with `P^i = 0` for `i > b`
each of whose terms is a direct sum of extensions by zero `j_{U!}O_U` of the structure sheaves
of the slice sites; those terms are flat, so `P` is a bounded above complex of flat modules.

This is the representative the span subcomplex of a site consumes.
`Stacks.Sites.ExtensionByZeroSpan.exists_sieve_subcomplex` does not ask that the terms of its
complex *be isomorphic to* such a sum; it asks for the sum **as a presentation**, a family
`ιP n α : j_{U(n,α)!}O_{U(n,α)} ⟶ P^n` exhibited as a colimit cofan, because the marked
generators it spans are indexed by that family and the sections it lifts are read off those
components. What is produced here is therefore the cofan together with its colimit property,
not the existence of an isomorphism with a coproduct.

## Main results

* `Stacks.SheafOfModules.exists_isColimit_cofanExtUnit`: a module which is a direct sum of
  extensions by zero carries a colimit cofan of extensions by zero, at the `extUnit` spelling
  of the span subcomplex.
* `Stacks.SheafOfModules.exists_sumExtensionByZeroRepresentative_of_isLE`: the representative,
  with the cofan presentation of each of its terms, its bound, and flatness of its terms.

## Implementation notes

**Why the two spellings of `j_{U!}O_U` need no comparison.**
`Stacks.Cohomology.DerivedLowerShriek.extensionByZeroUnit` is written with
`SheafOfModules.pullback (𝟙 (R.over U))` and `Stacks.Sites.ExtensionByZeroSpan.extUnit` with
`SheafOfModules.extensionByZero R U`, whose body is that same pullback; the two terms are
definitionally equal, so the coproduct of one family is the coproduct of the other and the
cofan transports along the isomorphism the class asserts with no bridging morphism. For the
same reason `Stacks.Cohomology.DerivedLowerShriek.IsSumOfExtensionByZeroUnits` and
`Stacks.SheafOfModules.IsSumOfExtensionByZeroStructureSheaves` are the same predicate, which is
what lets the flatness of the terms be cited from the latter and the resolution be run against
the former — the one of the two which is an `ObjectProperty` carrying the hypotheses
Stacks 05T7 asks of a resolving class.

**The class, not the ladder.** [Stacks, Tag 077J]
(`Stacks.SheafOfModules.exists_resolutionByDirectSumsExtensionsByZero`) resolves an *arbitrary*
complex by a sequential ladder whose colimit is the resolution, and its terms are sums of
extensions by zero only rung by rung, so no term of the resolution itself carries a
presentation. For a bounded above object no ladder is needed: Stacks 05T7 (2) applied to the
class of such sums gives a single bounded above resolution outright.

Nothing below is a clause of a tag; this is a step of the proof of [Stacks, Tag 0FPV], so no
`@[stacks …]` attribute is attached.

## References

* [Stacks Project, Tag 05T7](https://stacks.math.columbia.edu/tag/05T7)
* [Stacks Project, Tag 03EW](https://stacks.math.columbia.edu/tag/03EW)
* [Stacks Project, Tag 03EV](https://stacks.math.columbia.edu/tag/03EV)
* [Stacks Project, Tag 077J](https://stacks.math.columbia.edu/tag/077J)
* [Stacks Project, Tag 0FPV](https://stacks.math.columbia.edu/tag/0FPV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

variable (X : AlgebraicGeometry.RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The resolving class: direct sums of extensions by zero of the structure sheaves of the
slices of the site, read at the ring sheaf of a ringed site. It contains a zero object and
every module is a quotient of one of its members, which is what Stacks 05T7 asks of it. -/
private abbrev sumExtClass :
    ObjectProperty (_root_.SheafOfModules.{u} (Tensor.ringSheaf X.O)) :=
  Stacks.Cohomology.DerivedLowerShriek.IsSumOfExtensionByZeroUnits (Tensor.ringSheaf X.O)

/-- A member of the resolving class is a direct sum of extensions by zero in the sense of
`Stacks.SheafOfModules.IsSumOfExtensionByZeroStructureSheaves`: the two predicates are the same,
the spellings `SheafOfModules.pullback (𝟙 (R.over U))` and `SheafOfModules.extensionByZero R U`
of `j_{U!}O_U` being definitionally equal. -/
private theorem isSumOfExtensionByZeroStructureSheaves_of_sumExtClass
    {M : _root_.SheafOfModules.{u} (Tensor.ringSheaf X.O)} (hM : sumExtClass X M) :
    IsSumOfExtensionByZeroStructureSheaves X M := hM

/-- **A direct sum of extensions by zero, presented as a colimit cofan.** The class asserts an
isomorphism with a coproduct of extensions by zero; the span subcomplex of a site consumes
instead the family of morphisms into the module together with its colimit property, which is
what this produces. -/
theorem exists_isColimit_cofanExtUnit
    {M : _root_.SheafOfModules.{u} (Tensor.ringSheaf X.O)}
    (hM : IsSumOfExtensionByZeroStructureSheaves X M) :
    ∃ (I : Type u) (U : I → X.C)
      (ιM : ∀ α, Stacks.Sites.ExtensionByZeroSpan.extUnit (Tensor.ringSheaf X.O) (U α) ⟶ M),
      Nonempty (IsColimit (Cofan.mk M ιM)) := by
  obtain ⟨I, U, ⟨e⟩⟩ := hM
  refine ⟨I, U, fun α => Sigma.ι
    (fun α : I => Stacks.Sites.ExtensionByZeroSpan.extUnit (Tensor.ringSheaf X.O) (U α)) α ≫
      e.hom, ⟨?_⟩⟩
  exact (coproductIsCoproduct
      (fun α : I =>
        Stacks.Sites.ExtensionByZeroSpan.extUnit (Tensor.ringSheaf X.O) (U α))).ofIsoColimit
    (Cocone.ext e (fun α => rfl))

/-- **A bounded above representative whose terms are presented as sums of extensions by zero.**
A complex of `O`-modules with no cohomology above `b` receives a quasi-isomorphism from a
complex vanishing in every degree above `b` each of whose terms is presented as a colimit cofan
of extensions by zero `j_{U!}O_U` of the structure sheaves of the slices; those terms are flat.

This is Stacks 05T7 (2) at the class of direct sums of extensions by zero, with the
presentation of each term retained rather than only its isomorphism class, together with
Stacks 03EV and 05NG for the flatness. -/
theorem exists_sumExtensionByZeroRepresentative_of_isLE
    (K : CochainComplex (_root_.SheafOfModules.{u} (Tensor.ringSheaf X.O)) ℤ) (b : ℤ)
    [K.IsLE b] :
    ∃ (P : CochainComplex (_root_.SheafOfModules.{u} (Tensor.ringSheaf X.O)) ℤ) (f : P ⟶ K)
      (_ : QuasiIso f) (I : ℤ → Type u) (U : ∀ n, I n → X.C)
      (ιP : ∀ n α, Stacks.Sites.ExtensionByZeroSpan.extUnit
        (Tensor.ringSheaf X.O) (U n α) ⟶ P.X n),
      (∀ n, Nonempty (IsColimit (Cofan.mk (P.X n) (ιP n)))) ∧ P.IsStrictlyLE b ∧
        ∀ n, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O) (P.X n) := by
  classical
  obtain ⟨P, f, hf, hPsum, hPLE⟩ :=
    (CochainComplex.exists_quasiIso_prop (sumExtClass X)
      (fun M => Stacks.Cohomology.DerivedLowerShriek.exists_epi_isSumOfExtensionByZeroUnits
        (Tensor.ringSheaf X.O) M) b).2 K
  have hsum : ∀ n, IsSumOfExtensionByZeroStructureSheaves X (P.X n) := fun n =>
    isSumOfExtensionByZeroStructureSheaves_of_sumExtClass X (hPsum n)
  choose I U ιP hcol using fun n => exists_isColimit_cofanExtUnit X (hsum n)
  exact ⟨P, f, hf, I, U, ιP, hcol, hPLE,
    fun n => isFlat_of_isSumOfExtensionByZeroStructureSheaves X (hsum n)⟩

end Stacks.SheafOfModules

end
