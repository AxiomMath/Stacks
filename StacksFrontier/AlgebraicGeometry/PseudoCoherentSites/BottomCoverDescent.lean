module

public import StacksFrontier.Algebra.Homology.CoverOfTheLowestTerm
public import StacksFrontier.AlgebraicGeometry.PseudoCoherentSites.TruncatingApproximationsGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.PseudoCoherentObjects

/-!
# Pseudo-coherence from an approximation whose lowest term is only finitely generated

Let `(C, O)` be a ringed site, let `E` be a complex of `O`-modules and let `n` be an integer.
Suppose that locally — over the members of a covering family of every object of `C` — the
complex `E` receives a map

`α : 𝒦 ⟶ E|_V`

from a bounded complex `𝒦` which

* vanishes in the degrees below `n`,
* is a direct summand of a finite free `O|_V`-module in every degree above `n`,
* carries in degree `n` a module which is merely a quotient of a direct summand of a finite free
  `O|_V`-module — there is an epimorphism `q : 𝒜 ⟶ 𝒦^n` with `𝒜` such a summand,

and which is an isomorphism on cohomology in the degrees above `n` and an epimorphism on
cohomology in degree `n`. Then `E` is `n`-pseudo-coherent.

The point is the degree-`n` term: `𝒦` itself is *not* strictly perfect, so it is not an
approximation in the sense of Stacks 08FT part (1), and this is exactly the situation the
inductive step of the source's proof of the first assertion of Stacks 0FPV leaves one in. There
the complex `𝒦` is assembled from the finitely many sections `fᵢ` and `d(fᵢ)` below the degree
reached so far and from a strictly perfect complex above it; over a general site its degree-`n`
term is finitely generated and nothing more, because the restriction of an extension by zero
`j_{V!}O_V` to the slice over `V` is free on the *arrows* into `V` rather than on one generator
(the unit `O_V ⟶ (j_{V!}O_V)|_V` is invertible only for a subterminal `V`, by
`Stacks.SheafOfModules.ExtensionByZero.isIso_extensionByZeroAdjunction_unit`). The source's own
route consumes exactly that: "a surjection `O^{⊕r} ⟶ 𝒦^{n}` then gives the required complex".

Replacing the degree-`n` term of `𝒦` by `𝒜` along `q` is
`HomologicalComplex.bottomCover` of `StacksFrontier.Algebra.Homology.CoverOfTheLowestTerm`. The
result is strictly perfect, and its morphism to `𝒦` is an isomorphism on cohomology above `n`
and an epimorphism in degree `n`, so composing with `α` keeps both halves of the approximation
condition.

## Main results

* `AlgebraicGeometry.RingedSite.isStrictlyPerfect_bottomCover`: the complex with its degree-`n`
  term replaced by a direct summand of a finite free module is strictly perfect.
* `AlgebraicGeometry.RingedSite.exists_isStrictlyPerfect_approximation_of_bottomCover`: an
  approximation in degrees `≥ n` whose source is strictly perfect away from degree `n` and only
  finitely covered there yields a genuinely strictly perfect approximation in degrees `≥ n`.
* `AlgebraicGeometry.RingedSite.isPseudoCoherentComplexFrom_of_local_bottomCover` and
  `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_Q_of_local_bottomCover`: the local form,
  for a complex and for the object of `D(O)` it represents.

## Implementation notes

Nothing is weakened and nothing is assumed about `E`: the three statements are the defining
condition of `AlgebraicGeometry.RingedSite.IsPseudoCoherentComplexFrom` with the strict
perfection of the approximating complex relaxed in the single degree `n` to the existence of an
epimorphism onto its degree-`n` term from a direct summand of a finite free module. The
boundedness of `𝒦` is carried as the hypothesis
`{i | ¬ IsZero (𝒦.X i)}.Finite` rather than as a pair of bounds, which is the form
`IsStrictlyPerfect` itself uses.

The degree-`n` cohomology is where the replacement is only an epimorphism, and that is enough:
`HomologicalComplex.epi_homologyMap_of_epi_f` needs no hypothesis in the degree below. In the
degrees above `n` the replacement is invertible on cohomology even though it is only an
epimorphism in degree `n`, by `HomologicalComplex.isIso_homologyMap_of_epi_f`. Both are in
`StacksFrontier.Algebra.Homology.HomologyOfADegreewiseEpi`.

The universes are free: `RingedSite.{u, v, w}` with the sections of the modules in the ring
universe `w`, as for the rest of this directory.

## References

* [Stacks Project, Tag 08FL](https://stacks.math.columbia.edu/tag/08FL)
* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
* [Stacks Project, Tag 0FPV](https://stacks.math.columbia.edu/tag/0FPV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w d

namespace AlgebraicGeometry.RingedSite

section Modules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **A complex which is a direct summand of a finite free module in every degree but one, and
whose remaining term has been replaced by such a summand, is strictly perfect.** -/
theorem isStrictlyPerfect_bottomCover {K : CochainComplex (SheafOfModules.{w} R) ℤ} {n : ℤ}
    (hd : ∀ i : ℤ, (ComplexShape.up ℤ).Rel i n → K.d i n = 0)
    {A : SheafOfModules.{w} R} (q : A ⟶ K.X n) (hA : IsDirectSummandOfFiniteFree R A)
    (hbdd : {i : ℤ | ¬ IsZero (K.X i)}.Finite)
    (hterm : ∀ i : ℤ, i ≠ n → IsDirectSummandOfFiniteFree R (K.X i)) :
    IsStrictlyPerfect R (K.bottomCover n hd q) where
  bounded := by
    refine (hbdd.union (Set.finite_singleton n)).subset fun i hi => ?_
    simp only [Set.mem_ofPred_eq] at hi
    by_cases hin : i = n
    · exact Or.inr (by simpa only [Set.mem_singleton_iff] using hin)
    · exact Or.inl (fun hz => hi ((hz.of_iso (K.bottomCoverXIsoOfNe n hd q i hin))))
  termDirectSummand i := by
    by_cases hin : i = n
    · exact IsDirectSummandOfFiniteFree.of_iso R
        ((K.bottomCover n hd q).XIsoOfEq hin ≪≫ K.bottomCoverXIsoSelf n hd q) hA
    · exact IsDirectSummandOfFiniteFree.of_iso R (K.bottomCoverXIsoOfNe n hd q i hin)
        (hterm i hin)

/-- **A cover of the lowest term turns an approximation into a strictly perfect one.** Let
`α : K ⟶ G` be a morphism of complexes of `O`-modules which is an isomorphism on cohomology in
the degrees above `n` and an epimorphism in degree `n`. If `K` is bounded, vanishes below `n`,
is a direct summand of a finite free `O`-module in every degree above `n`, and admits an
epimorphism `q : A ⟶ K^n` from such a summand `A`, then `G` admits an approximation in degrees
`≥ n` by a complex that is genuinely strictly perfect.

The approximating complex is `K` with its degree-`n` term replaced by `A` along `q`, and the
approximating morphism is the composite of the resulting morphism to `K` with `α`. -/
theorem exists_isStrictlyPerfect_approximation_of_bottomCover
    {K G : CochainComplex (SheafOfModules.{w} R) ℤ} (n : ℤ)
    (hzero : ∀ i : ℤ, i < n → IsZero (K.X i))
    (hbdd : {i : ℤ | ¬ IsZero (K.X i)}.Finite)
    (hterm : ∀ i : ℤ, n < i → IsDirectSummandOfFiniteFree R (K.X i))
    {A : SheafOfModules.{w} R} (hA : IsDirectSummandOfFiniteFree R A)
    (q : A ⟶ K.X n) (hq : Epi q) (α : K ⟶ G)
    (hiso : ∀ j : ℤ, n < j → IsIso (HomologicalComplex.homologyMap α j))
    (hepi : Epi (HomologicalComplex.homologyMap α n)) :
    ∃ P : CochainComplex (SheafOfModules.{w} R) ℤ, IsStrictlyPerfect R P ∧
      ∃ β : P ⟶ G, (∀ j : ℤ, n < j → IsIso (HomologicalComplex.homologyMap β j)) ∧
        Epi (HomologicalComplex.homologyMap β n) := by
  have := hq
  have hd : ∀ i : ℤ, (ComplexShape.up ℤ).Rel i n → K.d i n = 0 := fun i hi =>
    (hzero i (by simp only [ComplexShape.up_Rel] at hi; omega)).eq_of_src _ _
  have hterm' : ∀ i : ℤ, i ≠ n → IsDirectSummandOfFiniteFree R (K.X i) := by
    intro i hi
    rcases lt_trichotomy i n with h | h | h
    · exact IsDirectSummandOfFiniteFree.of_isZero_general R (hzero i h)
    · exact absurd h hi
    · exact hterm i h
  refine ⟨K.bottomCover n hd q,
    isStrictlyPerfect_bottomCover R hd q hA hbdd hterm',
    K.bottomCoverι n hd q ≫ α, fun j hj => ?_, ?_⟩
  · rw [HomologicalComplex.homologyMap_comp]
    have := HomologicalComplex.isIso_homologyMap_bottomCoverι K n hd q j (by omega)
      (by simp only [CochainComplex.next]; omega)
    have := hiso j hj
    infer_instance
  · rw [HomologicalComplex.homologyMap_comp]
    have := HomologicalComplex.epi_homologyMap_bottomCoverι K n hd q n
      (by simp only [CochainComplex.next]; omega)
    exact epi_comp _ _

end Modules

section Site

variable (X : RingedSite.{u, v, w})
variable [HasSheafify X.J AddCommGrpCat.{w}]
variable [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
variable [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

omit [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **A complex of `O`-modules which locally admits an approximation in degrees `≥ n` whose
source is strictly perfect away from degree `n`, bounded, zero below `n`, and finitely covered in
degree `n`, is `n`-pseudo-coherent.**

This is the descent step of the source's proof of the first assertion of Stacks 0FPV: the
complex produced by the inductive construction is finitely generated in its lowest degree and
not a direct summand of a finite free module there, and a surjection onto that term from such a
summand turns it into a strictly perfect approximation. -/
theorem isPseudoCoherentComplexFrom_of_local_bottomCover
    (E : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) (n : ℤ)
    (h : ∀ U : X.C, ∃ S : Presieve U, Sieve.generate S ∈ X.J U ∧
      ∀ ⦃V : X.C⦄ (f : V ⟶ U), S f →
        ∃ K : CochainComplex
            (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ,
          (∀ i : ℤ, i < n → IsZero (K.X i)) ∧
          {i : ℤ | ¬ IsZero (K.X i)}.Finite ∧
          (∀ i : ℤ, n < i →
            IsDirectSummandOfFiniteFree ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)
              (K.X i)) ∧
          (∃ A : SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V),
            IsDirectSummandOfFiniteFree ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V) A ∧
              ∃ q : A ⟶ K.X n, Epi q) ∧
          ∃ α : K ⟶ X.restrictComplex E V,
            (∀ j : ℤ, n < j → IsIso (HomologicalComplex.homologyMap α j)) ∧
            Epi (HomologicalComplex.homologyMap α n)) :
    X.IsPseudoCoherentComplexFrom E n := by
  intro U
  obtain ⟨S, hS, hdata⟩ := h U
  refine ⟨S, hS, fun V f hf => ?_⟩
  obtain ⟨K, hzero, hbdd, hterm, ⟨A, hA, q, hq⟩, α, hiso, hepi⟩ := hdata f hf
  exact exists_isStrictlyPerfect_approximation_of_bottomCover
    ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V) n hzero hbdd hterm hA q hq α hiso hepi

/-- The object of `D(O)` represented by a complex as in
`AlgebraicGeometry.RingedSite.isPseudoCoherentComplexFrom_of_local_bottomCover` is
`n`-pseudo-coherent: that complex is itself a representative. -/
theorem isPseudoCoherentFrom_Q_of_local_bottomCover
    [HasDerivedCategory.{d} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
    (E : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) (n : ℤ)
    (h : ∀ U : X.C, ∃ S : Presieve U, Sieve.generate S ∈ X.J U ∧
      ∀ ⦃V : X.C⦄ (f : V ⟶ U), S f →
        ∃ K : CochainComplex
            (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ,
          (∀ i : ℤ, i < n → IsZero (K.X i)) ∧
          {i : ℤ | ¬ IsZero (K.X i)}.Finite ∧
          (∀ i : ℤ, n < i →
            IsDirectSummandOfFiniteFree ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)
              (K.X i)) ∧
          (∃ A : SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V),
            IsDirectSummandOfFiniteFree ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V) A ∧
              ∃ q : A ⟶ K.X n, Epi q) ∧
          ∃ α : K ⟶ X.restrictComplex E V,
            (∀ j : ℤ, n < j → IsIso (HomologicalComplex.homologyMap α j)) ∧
            Epi (HomologicalComplex.homologyMap α n)) :
    X.IsPseudoCoherentFrom (DerivedCategory.Q.obj E) n :=
  ⟨E, isPseudoCoherentComplexFrom_of_local_bottomCover X E n h, ⟨Iso.refl _⟩⟩

end Site

end AlgebraicGeometry.RingedSite

end
