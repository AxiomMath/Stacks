module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.BoundedAbove
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Slice.RestrictionBoundedBelow
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.IntervalDescent
import StacksCore.Tactic.StacksAttribute

/-!
# `m`-pseudo-coherent plus finite coverings puts an object in `D⁻`

Let `(C, O)` be a ringed site and let `E` be a complex of `O`-modules.  If a family of objects
covering the final object carries, on each member, a degree above which the cohomology of `E|_V`
vanishes, then the cohomology of `E` itself vanishes above a single degree: the maximum of the
members' degrees, which exists because the family is finite.  Together with
`StacksFrontier/CategoryTheory/Sites/Cohomology/PseudoCoherent/BoundedAbove.lean`, which produces
those per-member degrees out of the strictly perfect approximations that `m`-pseudo-coherence
provides, this is the **boundedness step** of Stacks 08HE (2) ⇒ (1): the induction on `n - m`
starts from `E` in `D⁻(O)`, and `n` is the top nonvanishing degree the bound supplies.

## The derived-category model is a parameter

The two statements below that mention `D(O)` take `HasDerivedCategory` as a hypothesis rather
than using `CategoryTheory.HasDerivedCategory.standard`.  The localization model is visible in
their *statements*, so a consumer that has its own model — the small étale site of a scheme is
one — cannot substitute it afterwards; and elaborating the standard model at a site whose objects
live a universe above its sections is prohibitively slow.

## Why the two halves are separate

The per-member half is universe-polymorphic in the module sections and asks nothing of the site.
The descent half uses `Stacks.SheafOfModules.isZero_of_coversTop`, which is stated for modules
whose sections live in the universe of the ring's sections, and asks for a family covering the
*final* object — `CategoryTheory.GrothendieckTopology.CoversTop` — which is the shape in which
locality of vanishing is available in this development.  A covering sieve on an object becomes
such a family through `CategoryTheory.GrothendieckTopology.coversTop_iff_of_isTerminal` when the
object is terminal, which is the case the induction starts from.

No naturality is needed and none is available: the library has no natural isomorphism between
the homology of a restricted complex and the restriction of its homology, and
`CategoryTheory.ShortComplex.mapHomologyIso` at the exact `SheafOfModules.overFunctor` is enough
objectwise.  This is the same device by which
`AlgebraicGeometry.RingedSite.isZero_homology_restrictComplex` and
`AlgebraicGeometry.RingedSite.isGE_Q_obj_restrictComplex` are proved; this file is their
converse, in that it runs the comparison from the slices back to the site.

## Main results

* `AlgebraicGeometry.RingedSite.exists_isZero_homology_of_coversTop`: **the descent of the
  bound** — per-member bounds on a finite covering family give a bound for `E`.
* `AlgebraicGeometry.RingedSite.exists_isLE_Q_obj_of_coversTop`: the same read as
  `E ∈ D⁻(O)`.
* `AlgebraicGeometry.RingedSite.exists_isLE_Q_obj_of_isPseudoCoherentComplexFrom`: **the
  boundedness step**, from `m`-pseudo-coherence and the hypothesis that a covering presieve of
  the starting object admits a finite subfamily still covering the final object.

## References

* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
* [Stacks Project, Tag 08HE](https://stacks.math.columbia.edu/tag/08HE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe t u v w d

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, v, w})
  [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{w}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]

omit [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})] in
/-- **A cohomological upper bound descends from a finite covering family.**  If each member of a
finite family of objects covering the final object carries a degree above which the cohomology of
`E|_V` vanishes, then the cohomology of `E` vanishes above the maximum of those degrees.

Above that maximum the cohomology sheaf `HʲE` restricts to zero on every member, because the
homology of the restricted complex is the restriction of the homology
(`CategoryTheory.ShortComplex.mapHomologyIso` at the exact `SheafOfModules.overFunctor`), and a
sheaf of modules vanishing on a family covering the final object is zero
(`Stacks.SheafOfModules.isZero_of_coversTop`). -/
public theorem exists_isZero_homology_of_coversTop
    (E : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    {ι : Type t} [Finite ι] (V : ι → X.C) (hV : X.J.CoversTop V)
    (hb : ∀ i : ι, ∃ b : ℤ, ∀ j : ℤ, b < j →
      IsZero ((X.restrictComplex E (V i)).homology j)) :
    ∃ b : ℤ, ∀ j : ℤ, b < j → IsZero (E.homology j) := by
  choose c hc using hb
  obtain ⟨b, hbd⟩ := (Set.finite_range c).bddAbove
  refine ⟨b, fun j hj => Stacks.SheafOfModules.isZero_of_coversTop hV _ fun i => ?_⟩
  have hph : (SheafOfModules.overFunctor.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (V i)).PreservesHomology :=
    Stacks.SheafOfModules.preservesHomology_overFunctor
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (V i)
  exact IsZero.of_iso (hc i j (lt_of_le_of_lt (hbd (Set.mem_range_self i)) hj))
    (((E.sc j).mapHomologyIso (SheafOfModules.overFunctor.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (V i))).symm)

variable [HasDerivedCategory.{d} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

omit [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})] in
/-- **The same bound, read in the derived category**: the image of `E` in `D(O)` is `≤ b` for
some `b`, that is, `E` lies in `D⁻(O)`.  The cohomology of `DerivedCategory.Q.obj E` is the
cohomology of `E` by `DerivedCategory.homologyFunctorFactors`. -/
public theorem exists_isLE_Q_obj_of_coversTop
    (E : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    {ι : Type t} [Finite ι] (V : ι → X.C) (hV : X.J.CoversTop V)
    (hb : ∀ i : ι, ∃ b : ℤ, ∀ j : ℤ, b < j →
      IsZero ((X.restrictComplex E (V i)).homology j)) :
    ∃ b : ℤ, (DerivedCategory.Q.obj E).IsLE b := by
  obtain ⟨b, hbz⟩ := X.exists_isZero_homology_of_coversTop E V hV hb
  exact ⟨b, (DerivedCategory.isLE_iff _ b).2 fun j hj => IsZero.of_iso (hbz j hj)
    ((DerivedCategory.homologyFunctorFactors
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) j).app E)⟩

omit [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})] in
/-- **The boundedness step of Stacks 08HE (2) ⇒ (1).**  An `m`-pseudo-coherent complex lies in
`D⁻(O)`, provided the covering presieve that witnesses `m`-pseudo-coherence at some object admits
a **finite** subfamily which still covers the final object of the site.

That proviso is the finite-refinement hypothesis, and it is where finiteness of coverings enters:
on the small affine étale site of a scheme it is supplied by
`Stacks.Sites.exists_finite_flat_refinement` at
`AlgebraicGeometry.SmallAffineEtale.precoverage`, whose coverings are finite, together with
`CategoryTheory.GrothendieckTopology.coversTop_iff_of_isTerminal`.  It is left as a hypothesis
rather than built in because the Zariski site of a non-quasi-compact scheme does not have it, and
the conclusion is false there. -/
public theorem exists_isLE_Q_obj_of_isPseudoCoherentComplexFrom
    (E : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) (k : ℤ)
    (hE : X.IsPseudoCoherentComplexFrom E k) (T : X.C)
    (hrefine : ∀ S : Presieve T, Sieve.generate S ∈ X.J T →
      ∃ (ι : Type t) (_ : Finite ι) (V : ι → X.C) (f : ∀ i, V i ⟶ T),
        (∀ i, S (f i)) ∧ X.J.CoversTop V) :
    ∃ b : ℤ, (DerivedCategory.Q.obj E).IsLE b := by
  obtain ⟨S, hS, hmem⟩ :=
    X.exists_isZero_homology_restrictComplex_of_isPseudoCoherentComplexFrom E k hE T
  obtain ⟨ι, hι, V, f, hf, hV⟩ := hrefine S hS
  exact X.exists_isLE_Q_obj_of_coversTop E V hV fun i => hmem (f i) (hf i)

end AlgebraicGeometry.RingedSite

end
