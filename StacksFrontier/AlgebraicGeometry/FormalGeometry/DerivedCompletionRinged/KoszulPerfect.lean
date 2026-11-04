module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulDerivedCompletion
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.InvertibleObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.LocalNature

/-!
# The Koszul complexes of a finite family of global sections are perfect

Let `(𝒞, 𝒪)` be a ringed site and let `f_1, …, f_r` be global sections of `𝒪`. The Koszul
complex `K(𝒪, f_1^{n+1}, …, f_r^{n+1})` of
`AlgebraicGeometry.RingedSite.koszulPowerComplex` is, in the grading of [Stacks, Tag 0913] in
which it is compared with the extended alternating Čech complex, the complex whose degree-`p`
term is the product of copies of `𝒪` indexed by the subsets of `{1, …, r}` of cardinality `p`.
Each such term is a *finite free* `𝒪`-module and the complex is concentrated in degrees
`0, …, r`, so the complex is strictly perfect in the sense of [Stacks, Tag 08FL] and the object
it represents in `D(𝒪)` is perfect in the sense of [Stacks, Tag 08G5].

This is what the hypothesis of [Stacks, Tag 08JJ] asks of the Koszul complexes when
[Stacks, Tag 0A0A] is applied to them in the proof of [Stacks, Tag 0A0E].

## Main results

* `AlgebraicGeometry.RingedSite.isDirectSummandOfFiniteFree_koszulPowerComplex_X`: every term of
  the Koszul complex is a direct summand of a finite free `𝒪`-module — in fact finite free, the
  retraction below being an isomorphism.
* `AlgebraicGeometry.RingedSite.isStrictlyPerfect_koszulPowerComplex`: **the Koszul complex is
  strictly perfect** ([Stacks, Tag 08FL]).
* `AlgebraicGeometry.RingedSite.isPerfectComplex_koszulPowerComplex` and
  `AlgebraicGeometry.RingedSite.isPerfect_koszulPowerComplex`: **the Koszul complex is a perfect
  complex, and the object it represents in `D(𝒪)` is perfect** ([Stacks, Tag 08G5]).

## Implementation notes

The degree-`p` term is the categorical product `∏_{|S| = p} 𝒪` over the index type
`CategoryTheory.AlternatingCech.Idx r p` of subsets of `Fin r` of cardinality `p`, which is a
finite type in `Type 0`. A finite product in a preadditive category with finite products is a
finite biproduct, and reindexing it along `Fintype.equivFin` turns it into the direct sum of
`Fintype.card (Idx r p)` copies of the structure sheaf; that direct sum is a finite free module
by `isDirectSummandOfFiniteFree_of_retract_biproduct` of
`AlgebraicGeometry.RingedSite.InvertibleDerived`, which is the form in which the library
records "a retract of a finite direct sum of copies of `𝒪` is a direct summand of a finite
free `𝒪`-module". No second notion of finite freeness is introduced: the finite free modules
are the `SheafOfModules.free (ULift (Fin n))` of [Stacks, Tag 08FL].

Perfectness of the object of `D(𝒪)` is read off the *global* strict perfectness through
`AlgebraicGeometry.RingedSite.InvertibleDerived.isPerfectComplex_of_strictlyPerfectSieve`: the
sieve of arrows over whose source the restriction of the complex is strictly perfect is the
whole sieve, because restriction to a slice of the site is exact and carries the structure sheaf
to the structure sheaf, so it preserves strict perfectness
(`Stacks.SheafOfModules.isStrictlyPerfect_mapHomologicalComplex`).

The universes are the diagonal `RingedSite.{u, u, u}` with coefficient universe `u`, as
everywhere in this directory.

## References

* [Stacks Project, Tag 08FL](https://stacks.math.columbia.edu/tag/08FL)
* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
* [Stacks Project, Tag 0913](https://stacks.math.columbia.edu/tag/0913)
* [Stacks Project, Tag 0A0E](https://stacks.math.columbia.edu/tag/0A0E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u d

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u}) {r : ℕ}
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

attribute [local instance] hasFiniteBiproducts_sheafOfModules

/-- **The degree-`p` term of the Koszul complex is a finite free `𝒪`-module.** It is the
product of copies of `𝒪` indexed by the subsets of `{1, …, r}` of cardinality `p`, a finite
index type; a finite product is a finite biproduct, and reindexing the index type by
`Fin (Fintype.card _)` presents it as a finite direct sum of copies of the structure sheaf. -/
theorem isDirectSummandOfFiniteFree_koszulPowerComplex_X (n : ℕ) (p : ℤ) :
    IsDirectSummandOfFiniteFree (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      ((koszulPowerComplex X f n).X p) := by
  classical
  refine InvertibleDerived.isDirectSummandOfFiniteFree_of_retract_biproduct
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
    (n := Fintype.card (AlternatingCech.Idx r p)) (Retract.ofIso ?_)
  exact (biproduct.isoProduct fun _ : AlternatingCech.Idx r p =>
        SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).symm ≪≫
    biproduct.reindex (Fintype.equivFin (AlternatingCech.Idx r p))
      (fun _ : Fin (Fintype.card (AlternatingCech.Idx r p)) =>
        SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- **The Koszul complex is strictly perfect** ([Stacks, Tag 08FL]): it is concentrated in
degrees `0, …, r` and each of its terms is a finite free `𝒪`-module. -/
theorem isStrictlyPerfect_koszulPowerComplex (n : ℕ) :
    IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (koszulPowerComplex X f n) where
  bounded := (Set.finite_Icc (0 : ℤ) r).subset fun p hp => by
    simp only [Set.mem_ofPred_eq] at hp
    refine Set.mem_Icc.mpr ⟨?_, ?_⟩
    · by_contra h
      exact hp (isZero_koszulPowerComplex_X_of_neg X f n (by omega))
    · by_contra h
      exact hp (isZero_koszulPowerComplex_X_of_lt X f n (by omega))
  termDirectSummand p := isDirectSummandOfFiniteFree_koszulPowerComplex_X X f n p

variable [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The Koszul complex is a perfect complex** ([Stacks, Tag 08G5]). It is globally strictly
perfect, and restriction to a slice of the site preserves strict perfectness, so the sieve of
arrows over whose source its restriction is strictly perfect is the whole sieve of every
object. -/
theorem isPerfectComplex_koszulPowerComplex (n : ℕ) :
    X.IsPerfectComplex (koszulPowerComplex X f n) := by
  refine InvertibleDerived.isPerfectComplex_of_strictlyPerfectSieve _ fun U => ?_
  refine X.J.superset_covering (fun V g _ => ?_) (X.J.top_mem U)
  have : PreservesFiniteColimits
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V) :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits V
  exact Stacks.SheafOfModules.isStrictlyPerfect_mapHomologicalComplex _
    (Stacks.SheafOfModules.overFunctorUnitIso (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V)
    (isStrictlyPerfect_koszulPowerComplex X f n)

/-- **The object of `D(𝒪)` represented by the Koszul complex is perfect** ([Stacks, Tag 08G5]).
This is the hypothesis under which [Stacks, Tag 08JJ] identifies `K ⊗^𝐋_𝒪 K_n^∨` with
`R𝑆heafHom_𝒪(K_n, K)`, and so the hypothesis under which [Stacks, Tag 0A0A] applies to the
Koszul system of [Stacks, Tag 0A0E]. -/
theorem isPerfect_koszulPowerComplex
    [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
    (n : ℕ) : X.IsPerfect (DerivedCategory.Q.obj (koszulPowerComplex X f n)) :=
  ⟨koszulPowerComplex X f n, isPerfectComplex_koszulPowerComplex X f n, ⟨Iso.refl _⟩⟩

end AlgebraicGeometry.RingedSite

end
