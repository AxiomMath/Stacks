module

public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Homology.CochainComplexOpposite
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.Data.Int.Interval
public import StacksCore.Algebra.Homology.TotalComplex
public import StacksFrontier.Algebra.Homology.HomotopyCategory.Minus
public import StacksFrontier.Algebra.Homology.Resolution.InjectiveResolution
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Hom bicomplex of two cochain complexes

Let `C` be an abelian category, and let `K` and `I` be `ℤ`-graded cochain complexes of `C`.
Applying the additive bifunctor `(X, Y) ↦ Hom_C(X, Y)` to `K` and `I` — with `K` placed in the
contravariant slot via the opposite complex, so that the degree `p` term of the first argument is
`K⁻ᵖ` — produces the bicomplex of abelian groups whose `(p, q)` term is `Hom_C(K⁻ᵖ, Iᑫ)`.

When `K` is bounded above and `I` is bounded below, only finitely many terms of this bicomplex
are nonzero on each diagonal `p + q = n`: boundedness above of `K` bounds `p` from below and
boundedness below of `I` bounds `p` from above along the diagonal. Finite diagonals are exactly
what the existence of the total complex requires when only finite coproducts are available, so
the total complex `⊕_{p + q = n} Hom_C(K⁻ᵖ, Iᑫ)` exists.

This is the bicomplex used to build the two spectral sequences converging to `Ext`
[Stacks 07AA], where `I` is taken to be an injective resolution of a single module; for that
use, `CochainComplex.injectiveResolutionSingle` provides the resolution.

## Main definitions

* `CochainComplex.homBicomplex`: the bicomplex `(p, q) ↦ Hom_C(K⁻ᵖ, Iᑫ)`.
* `CochainComplex.homBicomplexTotal`: its total complex, for `K` bounded above and `I` bounded
  below.
* `CochainComplex.injectiveResolutionSingle`: an injective resolution, as a resolution of a
  cochain complex, of an object placed in degree `0`.

## Main results

* `CochainComplex.homBicomplex_finite_diagonals`: each diagonal of the Hom bicomplex has only
  finitely many nonzero terms, for `K` bounded above and `I` bounded below.
* `CochainComplex.isZero_homBicomplex_X_X_of_isZero_left` and
  `CochainComplex.isZero_homBicomplex_X_X_of_isZero_right`: a term of the Hom bicomplex vanishes
  as soon as either of the two terms it is built from does.

## Implementation notes

The bicomplex carries no `@[stacks]` attribute. [Stacks 07AA] is the pair of spectral sequences
converging to `Ext`, which is not proved here; what is proved here is the boundedness
bookkeeping that the construction of those spectral sequences rests on, together with the
existence of the resolution they are built from. Tagging either declaration with 07AA would
claim the spectral sequences.

The two boundedness hypotheses are the object properties `CochainComplex.minus` (bounded above)
and `CochainComplex.plus` (bounded below), each an existential over a bound rather than a bound
carried as data, matching [Stacks 013H]. For an injective resolution the second is already
available as the field `CochainComplex.InjectiveResolution.boundedBelow`, so the diagonals of
`homBicomplex K R.cocomplex` are finite by
`homBicomplex_finite_diagonals K _ hK R.boundedBelow n`.

The group-valued bifunctor is `CategoryTheory.preadditiveCoyoneda`, whose values lie in
`AddCommGrpCat.{v}` for `Category.{v} C`; `v` is therefore free and is merely carried by the
statements, never computed from them, so no `max` constraint arises. The contravariant slot is
filled through `CochainComplex.opEquivalence`, which reindexes by negation, so the degree `p`
term of the first argument is `op (K.X (-p))` — this identification and the identification of
the `(p, q)` term of the bicomplex with the corresponding `preadditiveCoyoneda` value are both
`rfl`, which is why the two vanishing lemmas are terms rather than rewrites.

`injectiveResolutionSingle` chooses a resolution with `Exists.choose`; the resolution of an
object is not unique, and no statement here depends on which one is taken.

## References

* [Stacks, Tag 013H](https://stacks.math.columbia.edu/tag/013H)
* [Stacks, Tag 013K](https://stacks.math.columbia.edu/tag/013K)
* [Stacks, Tag 07AA](https://stacks.math.columbia.edu/tag/07AA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The Hom bicomplex of two cochain complexes `K` and `I` of an abelian category: the bicomplex
of abelian groups whose `(p, q)` term is `Hom_C(K⁻ᵖ, Iᑫ)`, obtained by applying the additive
bifunctor `Hom_C(-, -)` to the opposite complex of `K` and to `I`. -/
public noncomputable def homBicomplex (K I : CochainComplex C ℤ) :
    HomologicalComplex₂ AddCommGrpCat (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (((preadditiveCoyoneda (C := C)).mapBifunctorHomologicalComplex
    (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj
    ((CochainComplex.opEquivalence C).functor.obj (op K))).obj I

/-- The `(p, q)` term of the Hom bicomplex vanishes when the term `K⁻ᵖ` of the first complex
does. -/
public lemma isZero_homBicomplex_X_X_of_isZero_left (K I : CochainComplex C ℤ) (p q : ℤ)
    (h : IsZero (K.X (-p))) : IsZero (((homBicomplex K I).X p).X q) :=
  ((preadditiveCoyoneda.map_isZero h.op).obj (I.X q) :
    IsZero ((preadditiveCoyoneda.obj (op (K.X (-p)))).obj (I.X q)))

/-- The `(p, q)` term of the Hom bicomplex vanishes when the term `Iᑫ` of the second complex
does. -/
public lemma isZero_homBicomplex_X_X_of_isZero_right (K I : CochainComplex C ℤ) (p q : ℤ)
    (h : IsZero (I.X q)) : IsZero (((homBicomplex K I).X p).X q) :=
  ((preadditiveCoyoneda.obj (op (K.X (-p)))).map_isZero h :
    IsZero ((preadditiveCoyoneda.obj (op (K.X (-p)))).obj (I.X q)))

/-- Each diagonal of the Hom bicomplex of a bounded above complex `K` and a bounded below
complex `I` has only finitely many nonzero terms: a bound `Kⁱ = 0` for `i > a` forces `p ≥ -a`
and a bound `Iⁱ = 0` for `i < b` forces `p ≤ n - b` on the diagonal `p + q = n`. -/
public theorem homBicomplex_finite_diagonals (K I : CochainComplex C ℤ)
    (hK : CochainComplex.minus C K) (hI : CochainComplex.plus C I) (n : ℤ) :
    {pq : ℤ × ℤ |
      ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) pq = n ∧
      ¬ IsZero (((homBicomplex K I).X pq.1).X pq.2)}.Finite := by
  obtain ⟨a, ha⟩ := (CochainComplex.minus_iff K).1 hK
  obtain ⟨b, hb⟩ := (CochainComplex.plus_iff C I).1 hI
  refine Set.Finite.subset ((Set.finite_Icc (-a) (n - b)).image (fun p : ℤ => (p, n - p))) ?_
  rintro ⟨p, q⟩ ⟨hsum, hne⟩
  have hsum' : p + q = n := hsum
  obtain rfl : q = n - p := by omega
  refine ⟨p, ⟨?_, ?_⟩, rfl⟩
  · by_contra hlt
    exact hne (isZero_homBicomplex_X_X_of_isZero_left K I p _
      (CochainComplex.isZero_of_isStrictlyLE K a (-p) (by omega)))
  · by_contra hgt
    exact hne (isZero_homBicomplex_X_X_of_isZero_right K I p _
      (CochainComplex.isZero_of_isStrictlyGE I b (n - p) (by omega)))

/-- The total complex of the Hom bicomplex of a bounded above complex `K` and a bounded below
complex `I`: in degree `n` it is `⊕_{p + q = n} Hom_C(K⁻ᵖ, Iᑫ)`, which exists because the
diagonals are finite. -/
@[ega "0 11.3.1" "special case"]
public noncomputable def homBicomplexTotal (K I : CochainComplex C ℤ)
    (hK : CochainComplex.minus C K) (hI : CochainComplex.plus C I) :
    CochainComplex AddCommGrpCat ℤ := by
  letI : (homBicomplex K I).HasTotal (ComplexShape.up ℤ) :=
    HomologicalComplex₂.hasTotal_of_finite (homBicomplex K I) (ComplexShape.up ℤ)
      (homBicomplex_finite_diagonals K I hK hI)
  exact (homBicomplex K I).total (ComplexShape.up ℤ)

/-- An injective resolution of an object `F` of an abelian category with enough injectives,
regarded as an injective resolution of the cochain complex `F` placed in degree `0`. -/
public noncomputable def injectiveResolutionSingle [EnoughInjectives C] (F : C) :
    CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor C 0).obj F) :=
  (CochainComplex.exists_injectiveResolution_isStrictlyGE 0
    ((CochainComplex.singleFunctor C 0).obj F)).choose

end CochainComplex
