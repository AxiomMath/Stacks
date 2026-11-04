module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.SingleHomology
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantExtensions
public import StacksCore.Tactic.StacksAttribute

/-!
# Complexes with locally constant cohomology sheaves

Let `(C, J)` be a site and `Λ` a Noetherian commutative ring. Stacks Tag 094G asserts that an
object `K` of `D^b(C, Λ)` whose cohomology sheaves are locally constant sheaves of `Λ`-modules of
finite type is, locally on the site, represented by a bounded complex of locally constant sheaves
of `Λ`-modules of finite type.

This file states that conclusion and proves the base case of the induction by which Tag 094G
proves it: the case of an object with at most one nonzero cohomology sheaf. Such a `K` is the
single complex on the sheaf `H^n(K)`, and over a covering family trivializing that sheaf the
restricted single complex has a locally constant term of finite type in degree `n` and zero
terms elsewhere.

## Main definitions

* `Stacks.ConstantSheaf.IsRepresentedByLocallyConstantComplex`: an object of the derived category
  of sheaves of `Λ`-modules is isomorphic to `Q` of a complex concentrated in degrees `[a, b]`
  all of whose terms are locally constant of finite type.

## Main results

* `Stacks.ConstantSheaf.isFiniteTypeLocallyConstantModuleSheaf_of_constant`: a sheaf isomorphic
  to the constant sheaf on a finitely generated module is locally constant of finite type.
* `Stacks.ConstantSheaf.isFiniteTypeLocallyConstantModuleSheaf_overPullback_of_isConstantFGOver`:
  on the slice site over a trivializing object, the restriction of a sheaf is locally constant of
  finite type.
* `Stacks.ConstantSheaf.isRepresentedByLocallyConstantComplex_single`: the class of the single
  complex on a locally constant sheaf of finite type is represented by that complex.
* `Stacks.ConstantSheaf.exists_cover_isRepresentedByLocallyConstantComplex`: **Tag 094G for an
  object with at most one nonzero cohomology sheaf.**

## Implementation notes

The conclusion is stated over an *arbitrary* object `U` of the site rather than over a final
object, which is how the source phrases it; the version over a final object is the special case.
This is the form taken by every neighbouring result (Tags 093Q, 093S, 093U), and no finality
hypothesis is used.

The restriction `K|_{U_i}` is the functor induced on derived categories by restriction of sheaves
to the slice site, `(J.overPullback _ (V i)).mapDerivedCategory`. Restriction to a slice site is
additive and preserves finite limits and finite colimits, so the induced functor on derived
categories exists with no hypotheses beyond those already carried, and it carries the single
complex on a sheaf to the single complex on the restricted sheaf
(`CategoryTheory.Functor.mapDerivedCategorySingleFunctor`).

The module universe is `max u v w` throughout, as for the predicate of Tag 093U: at that universe
all sheafification hypotheses are automatic and the universe is unchanged by slicing, so the
statement on the slice site `C/V` is the statement of the same shape at the same module universe.

The hypothesis `[IsNoetherianRing Λ]` of Tag 094G is carried in the variable block, to match the
chain of results this belongs to, but it is `omit`ted: Noetherianity enters Tag 094G only through
the weak Serre property of Tag 093U, which is used in the induction step and not in the case
proved here.

## What is not proved

Only the case of **at most one nonzero cohomology sheaf** is proved. The induction of Tag 094G on
the length `b - a` of the interval containing the nonzero cohomology sheaves is not carried out,
so nothing is proved for two or more nonzero cohomology sheaves, and no part of the induction
step is formalized.

The induction step of the source refines the covering so that `H^b(K)` is a constant sheaf `M̲`,
chooses a surjection `Λ^{⊕n} → M` from a finite free module, refines once more so that the `n`
generators lift to `H^b(U_i, K)`, and uses the resulting map `Λ^{⊕n}̲[-b] → K` — surjective on
`H^b` — as the first map of a distinguished triangle whose third term has one fewer nonzero
cohomology sheaf (locally constant of finite type by Tag 093U) and to which the induction
hypothesis applies; the last differential of the resulting complex is read off from Tag 093S.
Two ingredients of that argument are unavailable here.

* The finite free module `Λ^{⊕n}` is not an object of `ModuleCat.{max u v w} Λ`: a finite free
  `Λ`-module has `Λ` itself as a summand, and `Λ : Type r` lives at a universe unrelated to
  `max u v w`. The same obstruction is recorded for Tag 093U in
  `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantExtensions`, where it is
  circumvented by constructing the extension inside the sections of the middle term. No such
  substitute is available here, because what the argument uses about `Λ^{⊕n}` is freeness, that
  is, that a map out of it is exactly a family of sections.
* Lifting the generators to `H^b(U_i, K)` is the statement that the cohomology of a bounded
  complex on a site is computed locally, which is not among the inputs this file has.

## References

* [Stacks Project, Tag 094G](https://stacks.math.columbia.edu/tag/094G)
* [Stacks Project, Tag 093U](https://stacks.math.columbia.edu/tag/093U)
* [Stacks Project, Tag 093S](https://stacks.math.columbia.edu/tag/093S)
* [Stacks Project, Tag 093Q](https://stacks.math.columbia.edu/tag/093Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u w r

namespace Stacks.ConstantSheaf

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]

omit [IsNoetherianRing Λ]

/-! ### Constant sheaves are locally constant -/

/-- A sheaf of `Λ`-modules isomorphic to the constant sheaf on a finitely generated module is
locally constant of finite type: the identity of any object is already a trivializing covering
family, since the constant sheaf restricts to the constant sheaf on a slice site. -/
theorem isFiniteTypeLocallyConstantModuleSheaf_of_constant
    {F : Sheaf J (ModuleCat.{max u v w} Λ)} {E : ModuleCat.{max u v w} Λ}
    (hE : ModuleCat.isFG Λ E)
    (e : (constantSheaf J (ModuleCat.{max u v w} Λ)).obj E ≅ F) :
    IsFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J Λ F := by
  intro U
  refine ⟨PUnit.{max u v + 1}, fun _ => U, fun _ => 𝟙 U, ?_, fun _ => ?_⟩
  · have h : Sieve.ofArrows (fun _ : PUnit.{max u v + 1} => U) (fun _ => 𝟙 U) = ⊤ :=
      Sieve.id_mem_iff_eq_top.mp (Sieve.ofArrows_mk _ _ PUnit.unit)
    rw [h]
    exact J.top_mem U
  · exact ⟨E, hE, ⟨(overPullbackConstantSheafIso J (ModuleCat.{max u v w} Λ) U).app E ≪≫
      (J.overPullback (ModuleCat.{max u v w} Λ) U).mapIso e⟩⟩

/-- Over an object `V` trivializing `F`, the restriction of `F` to the slice site `C/V` is a
locally constant sheaf of finite type for the localized topology. The module universe `max u v w`
is unchanged by slicing, so this is the same condition at the same universe. -/
theorem isFiniteTypeLocallyConstantModuleSheaf_overPullback_of_isConstantFGOver
    {V : C} {F : Sheaf J (ModuleCat.{max u v w} Λ)} (h : IsConstantFGOver J Λ V F) :
    IsFiniteTypeLocallyConstantModuleSheaf.{v, max u v, w} (J.over V) Λ
      ((J.overPullback (ModuleCat.{max u v w} Λ) V).obj F) := by
  obtain ⟨E, hE, ⟨φ⟩⟩ := h
  exact isFiniteTypeLocallyConstantModuleSheaf_of_constant (J.over V) Λ hE φ

/-! ### Representability by a complex of locally constant sheaves -/

/-- **Represented by a complex of locally constant sheaves of finite type.** An object `X` of the
derived category of sheaves of `Λ`-modules is isomorphic to `Q` of a cochain complex which is
zero outside the degrees `[a, b]` and all of whose terms are locally constant of finite type.
This is the conclusion of Stacks Tag 094G at one member of the covering family. -/
def IsRepresentedByLocallyConstantComplex (a b : ℤ)
    (X : DerivedCategory (Sheaf J (ModuleCat.{max u v w} Λ))) : Prop :=
  ∃ L : CochainComplex (Sheaf J (ModuleCat.{max u v w} Λ)) ℤ,
    L.IsStrictlyGE a ∧ L.IsStrictlyLE b ∧
      (∀ i : ℤ, IsFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J Λ (L.X i)) ∧
      Nonempty (X ≅ DerivedCategory.Q.obj L)

variable {J Λ}

/-- Representability by a complex of locally constant sheaves of finite type depends only on the
isomorphism class in the derived category. -/
theorem IsRepresentedByLocallyConstantComplex.of_iso {a b : ℤ}
    {X Y : DerivedCategory (Sheaf J (ModuleCat.{max u v w} Λ))}
    (h : IsRepresentedByLocallyConstantComplex.{v, u, w} J Λ a b X) (e : Y ≅ X) :
    IsRepresentedByLocallyConstantComplex.{v, u, w} J Λ a b Y := by
  obtain ⟨L, hGE, hLE, hterm, ⟨eL⟩⟩ := h
  exact ⟨L, hGE, hLE, hterm, ⟨e ≪≫ eL⟩⟩

variable (J Λ)

/-- The single complex on a locally constant sheaf of finite type `F`, placed in degree `n`,
represents the class of `F[-n]` in the derived category: its term in degree `n` is `F` and its
other terms are zero, and the zero sheaf is locally constant of finite type. -/
theorem isRepresentedByLocallyConstantComplex_single (n : ℤ)
    {F : Sheaf J (ModuleCat.{max u v w} Λ)}
    (hF : IsFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J Λ F) :
    IsRepresentedByLocallyConstantComplex.{v, u, w} J Λ n n
      ((DerivedCategory.singleFunctor (Sheaf J (ModuleCat.{max u v w} Λ)) n).obj F) := by
  refine ⟨(HomologicalComplex.single (Sheaf J (ModuleCat.{max u v w} Λ))
    (ComplexShape.up ℤ) n).obj F, inferInstance, inferInstance, fun j => ?_, ⟨Iso.refl _⟩⟩
  by_cases hj : j = n
  · subst hj
    exact ObjectProperty.prop_of_iso _
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) j F).symm hF
  · exact ObjectProperty.prop_of_iso _
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) n F j hj).isoZero.symm
      (isFiniteTypeLocallyConstantModuleSheaf_zero J Λ)

/-! ### Tag 094G for one nonzero cohomology sheaf -/

/-- **Stacks Tag 094G, the case of at most one nonzero cohomology sheaf.** Let `K` be an object of
the derived category of sheaves of `Λ`-modules whose cohomology is concentrated in a single
degree `n` and whose cohomology sheaves are locally constant of finite type. Then every object
`U` of the site has a covering family `V i ⟶ U` such that the restriction of `K` to each slice
site `C/V i` is represented by a complex of locally constant sheaves of `Λ`-modules of finite
type, concentrated in degree `n`. -/
@[stacks 094G "the case of at most one nonzero cohomology sheaf"]
theorem exists_cover_isRepresentedByLocallyConstantComplex (n : ℤ) (U : C)
    (K : DerivedCategory (Sheaf J (ModuleCat.{max u v w} Λ)))
    [K.IsGE n] [K.IsLE n]
    (hK : ∀ i : ℤ, IsFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J Λ
      ((DerivedCategory.homologyFunctor _ i).obj K)) :
    ∃ (I : Type (max u v)) (V : I → C) (f : ∀ i, V i ⟶ U),
      Sieve.ofArrows V f ∈ J U ∧ ∀ i : I,
        IsRepresentedByLocallyConstantComplex.{v, max u v, w} (J.over (V i)) Λ n n
          ((J.overPullback (ModuleCat.{max u v w} Λ) (V i)).mapDerivedCategory.obj K) := by
  obtain ⟨Y, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE K n
  have hY : IsFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J Λ Y :=
    ObjectProperty.prop_of_iso _
      ((DerivedCategory.homologyFunctor _ n).mapIso e ≪≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso _ n).app Y) (hK n)
  obtain ⟨I, V, f, hcov, hloc⟩ := hY U
  refine ⟨I, V, f, hcov, fun i => ?_⟩
  let G : Sheaf J (ModuleCat.{max u v w} Λ) ⥤ Sheaf (J.over (V i)) (ModuleCat.{max u v w} Λ) :=
    J.overPullback (ModuleCat.{max u v w} Λ) (V i)
  have hres : IsFiniteTypeLocallyConstantModuleSheaf.{v, max u v, w} (J.over (V i)) Λ (G.obj Y) :=
    isFiniteTypeLocallyConstantModuleSheaf_overPullback_of_isConstantFGOver J Λ (hloc i)
  exact (isRepresentedByLocallyConstantComplex_single (J.over (V i)) Λ n hres).of_iso
    (G.mapDerivedCategory.mapIso e ≪≫ (G.mapDerivedCategorySingleFunctor n).app Y)

end Stacks.ConstantSheaf

end
