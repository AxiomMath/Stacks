module

public import Mathlib.Algebra.Homology.DerivedCategory.Plus
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.CategoryTheory.Localization.CalculusOfFractions.Fractions
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Constructor
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorsOnDerivedCategories
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Right and left acyclic objects for an additive functor

This file collects the formalizations of [Stacks, Tag 0157], [Stacks, Tag 05T8], [Stacks, Tag
05T9].

## References

* [Stacks, Tag 0157](https://stacks.math.columbia.edu/tag/0157)
* [Stacks, Tag 05T8](https://stacks.math.columbia.edu/tag/05T8)
* [Stacks, Tag 05T9](https://stacks.math.columbia.edu/tag/05T9)
-/

section

/-!
# Right acyclic objects for an additive functor

Let `F : C ⥤ D` be an additive functor between abelian categories. It induces a functor
`K⁺(C) ⥤ D⁺(D)`, whose *right derived functor* `RF : D⁺(C) ⥤ D⁺(D)` is the left Kan extension of
that functor along the localization `Qh : K⁺(C) ⥤ D⁺(C)` at the quasi-isomorphisms `Qis⁺(C)`. The
unit `α : F ⟶ Qh ⋙ RF` of that Kan extension has, at an object `X` of `K⁺(C)`, the leg
`α_X : F(X) ⟶ RF(Qh(X))`, the canonical map, and `X` *computes* `RF` when `α_X` is an isomorphism.

An object `A` of `C` is *right acyclic for `F`* when the complex `A[0]`, with `A` placed in
degree zero, computes `RF`.

## Main definitions

* `CategoryTheory.Functor.rightAcyclic F`: the objects of `C` that are right acyclic for `F`, as
  an `ObjectProperty C`.

## Main results

* `CategoryTheory.Functor.rightAcyclic_isClosedUnderIsomorphisms`: right acyclicity is invariant
  under isomorphism, which is what lets the property be carried across the degreewise
  isomorphisms of a truncation of a complex.

## Implementation notes

* This is part (3) of the source definition. Its part (1) names the right derived functors `RF`,
  which are `Functor.totalRightDerived`, and its part (2) names the left derived functors `LF`.
* Part (1) names two right derived functors of `F`: one of `F : K(C) ⥤ D(D)` relative to `Qis(C)`,
  and one of `F : K⁺(C) ⥤ D⁺(D)` relative to `Qis⁺(C)`. They are defined at, and are computed by,
  the same bounded below objects, `A[0]` among them, so the condition is stated for the second. The
  multiplicative system is the source's in both cases — `Qis(C)` resp. `Qis⁺(C)`, never the
  quasi-isomorphisms of the target.
* Part (4), left acyclicity, is this property for the opposite functor `F.op : Cᵒᵖ ⥤ Dᵒᵖ` at
  `Aᵒᵖ`, since passing to opposite categories exchanges `K⁻(C)` with `K⁺(Cᵒᵖ)` and `LF` with
  `R(F.op)`; it is not restated here.
* `HasRightDerivedFunctor` says that `RF` is everywhere defined, and it holds when `C` has enough
  injectives. The source lets `RF` be a partial functor and asks in addition that it be defined at
  `A[0]`, a distinction that is invisible in the everywhere defined case assumed here. Under
  `[EnoughInjectives C]`, which supplies that instance, `RF` and `α` are
  `Functor.rightDerivedFunctorPlus` and `Functor.rightDerivedFunctorPlusUnit` by definition, so
  `F.rightAcyclic A` is definitionally
  `IsIso (F.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.singleFunctor C 0).obj A))`
  and a proof of either is a proof of the other.

## References

* [Stacks, Tag 0157](https://stacks.math.columbia.edu/tag/0157)
-/

@[expose] public section

universe w w' v v' u u'

namespace CategoryTheory.Functor

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [Abelian C] [Abelian D] [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D]

/-- An object `A` of an abelian category `C` is **right acyclic** for an additive functor
`F : C ⥤ D` to an abelian category, or **acyclic for `RF`**, if the complex `A[0]` with `A` in
degree zero computes the right derived functor `RF` of `F : K⁺(C) ⥤ D⁺(D)`, that is, if the
canonical map `α_{A[0]} : F(A[0]) ⟶ RF(Qh(A[0]))`, the unit of `RF` at `A[0]`, is an
isomorphism. -/
@[stacks 0157 "part (3); the `RF` of part (1) is `Functor.totalRightDerived`", sga "4 XVII 1.2.3"
  "(ii)", sga "4 V 0.4"]
public def rightAcyclic (F : C ⥤ D) [F.Additive]
    [(F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso C)] : ObjectProperty C := fun A ↦
  IsIso (((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
    DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C)).app
    ((HomotopyCategory.Plus.singleFunctor C 0).obj A))

/-- **Right acyclicity is invariant under isomorphism.** Isomorphic objects give isomorphic
objects of `K⁺(C)` when placed in degree zero, and the unit of the right derived functor is
natural, so it is invertible at one exactly when it is at the other. -/
public instance rightAcyclic_isClosedUnderIsomorphisms (F : C ⥤ D) [F.Additive]
    [(F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso C)] :
    (F.rightAcyclic).IsClosedUnderIsomorphisms where
  of_iso e hA :=
    (NatTrans.isIso_app_iff_of_iso _ ((HomotopyCategory.Plus.singleFunctor C 0).mapIso e)).1 hA

end CategoryTheory.Functor

end

end

section

/-!
# A class of objects computing a right derived functor

Let `F : A ⥤ B` be an additive functor between abelian categories. Let `I` be a class of
objects of `A` such that

* every object of `A` is a subobject of an object satisfying `I`, and
* for every short exact sequence `0 ⟶ P ⟶ Q ⟶ R ⟶ 0` of `A` with `P` and `Q` satisfying `I`, the
  object `R` satisfies `I` too and `0 ⟶ F P ⟶ F Q ⟶ F R ⟶ 0` is again short exact.

Then every object satisfying `I` is right acyclic for `F`, i.e. computes `RF`. For `I` the
injective objects of a category with enough injectives this is the classical statement that
injective objects are acyclic; the point of the lemma is that a class of `F`-adapted objects,
such as the flasque sheaves for sheaf cohomology, does just as well.

## Main results

* `CategoryTheory.Functor.hasPointwiseRightDerivedFunctor_and_le_rightAcyclic`: Stacks 05T8,
  including existence of the pointwise right derived functor.
* `CategoryTheory.Functor.le_rightAcyclic`: Stacks 05T8 for an already given right derived
  functor.

## Implementation notes

The class `I ⊂ Ob(A)` of the source is a `CategoryTheory.ObjectProperty A`, i.e. a predicate on
objects, and "every object of `I` is acyclic for `RF`" is the inequality `I ≤ F.rightAcyclic` of
object properties (Stacks 0157), which unfolds to `∀ X, I X → F.rightAcyclic X`. "Every object of
`A` is a subobject of an element of `I`" is spelled, as in Stacks 05T6, as the existence for each
`X` of a monomorphism from `X` into an object satisfying `I`; Mathlib has no name for this
hypothesis. A short exact sequence `0 ⟶ P ⟶ Q ⟶ R ⟶ 0` is a `CategoryTheory.ShortComplex A`
which is `ShortComplex.ShortExact`, and exactness of `0 ⟶ F P ⟶ F Q ⟶ F R ⟶ 0` is
`ShortExact` for its image `S.map F` under `F` (an additive functor preserves zero morphisms, so
the image short complex is defined).

The source's hypothesis (2) is a single condition with a conjunction of two conclusions, and is
stated that way rather than split in two, because the intended instances (`I` the injective, or
the flasque, or the `F`-acyclic objects) verify the two together and because the source's own
proof uses both halves at every application.

The source does not assume that a zero object satisfies `I`: as its footnote observes, this
follows from the hypotheses, since (1) makes `I` nonempty and (2) applied to
`0 ⟶ P ⟶ P ⟶ 0 ⟶ 0` puts a zero object in `I`. It is therefore not assumed here either, even
though the route through Stacks 05T6 needs it.

The source lets `RF` be a partially defined functor and concludes both that it is defined at
objects of `I` and that its comparison there is invertible. The bounded below complexes all of
whose terms satisfy `I` form a right derivability structure for the quasi-isomorphisms of
`K⁺(A)` (every complex has such a resolution by Stacks 05T6, and `K⁺(A)` has a calculus of left
fractions), and this derivability structure derives `F`: a quasi-isomorphism between two such
complexes is sent to a quasi-isomorphism. The latter is the source's computation for an acyclic
complex with terms in `I`, applied after factoring the quasi-isomorphism through a degreewise
monomorphic one into a resolution of `cone(𝟙) ⊞ L`, which avoids asking `I` to be closed under
direct sums. Hence `RF` exists pointwise on all of `K⁺(A)`, and its unit is invertible on every
complex with terms in `I`, in particular on `A[0]` for `A` in `I`, whichever right derived functor
is chosen.

Faithfulness. (1) Every hypothesis is used by the conclusion: `hI₁` is what makes the
`I`-resolutions cofinal among the bounded below resolutions of `A[0]`, and `hI₂` is what makes
`F` of such a resolution exact; the conclusion fails without `hI₂` (take `I` the class of all
objects, which satisfies `hI₁` with `i = 𝟙 X`, and an `F` that is not exact), and without `hI₁`
there is no reason for a bounded below resolution of `A[0]` to be refinable inside `I`, which is
the only route the source's proof has to the unit. (2) The ambient data are the source's: one
additive functor `F : A ⥤ B` between abelian categories, one class `I` of objects of `A`, and the
derived functor taken along the localization of `K⁺(A)` at the quasi-isomorphisms of `A`, not of
`B`. (3) The canonical map is pinned, not merely asserted to exist: `F.rightAcyclic A` is
invertibility of the leg `F(A[0]) ⟶ RF(A[0])` of the unit of the right derived functor, by the
definition imported from Stacks 0157. (4) Non-degenerate: for `A` with enough injectives and `I`
the injective objects, `hI₁` is `EnoughInjectives.presentation` and `hI₂` holds because a short
exact sequence whose first two terms are injective splits, so the statement then asserts the
classical acyclicity of injective objects; and for an exact `F`, the class `I = ⊤` satisfies both
hypotheses, so the hypotheses do not force `I` to be small.

## References

* [StacksProject 05T8](https://stacks.math.columbia.edu/tag/05T8)
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Functor

universe w w' v v' u u'

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [Abelian C] [Abelian D]

section


open HomologicalComplex ZeroObject

namespace RightAcyclicCriterion

/-- The short exact sequence `Y ⟶ Y ⟶ Z` puts every zero object in `I`. -/
public lemma zero_mem (F : C ⥤ D) [F.Additive] (I : ObjectProperty C)
    (hI₁ : ∀ X : C, ∃ (Y : C) (_ : I Y) (i : X ⟶ Y), Mono i)
    (hI₂ : ∀ S : ShortComplex C, S.ShortExact → I S.X₁ → I S.X₂ →
      I S.X₃ ∧ (S.map F).ShortExact) {Z : C} (hZ : IsZero Z) : I Z := by
  obtain ⟨Y, hY, i, hi⟩ := hI₁ Z
  exact (hI₂ (ShortComplex.mk (𝟙 Y) (0 : Y ⟶ Z) (by simp))
    { exact := (ShortComplex.exact_iff_epi _ rfl).2 inferInstance
      epi_g := hZ.epi _ } hY hY).1

/-- In an acyclic complex the differential surjects onto the next cycles. -/
private lemma epi_toCycles (K : CochainComplex C ℤ) (hK : K.Acyclic) {m n : ℤ} (h : m + 1 = n) :
    Epi (K.toCycles m n) := by
  subst h
  have h : Epi (K.toCycles ((ComplexShape.up ℤ).prev (m + 1)) (m + 1)) :=
    (hK (m + 1)).epi_toCycles
  rwa [show (ComplexShape.up ℤ).prev (m + 1) = m by simp] at h

/-- The short exact sequences used to induct on the cycles of an acyclic complex. -/
private lemma cycles_shortExact (K : CochainComplex C ℤ) (hK : K.Acyclic) (n : ℤ) :
    (ShortComplex.mk (K.iCycles n) (K.toCycles n (n + 1))
      (by simp [← cancel_mono (K.iCycles (n + 1))])).ShortExact := by
  have := epi_toCycles K hK (rfl : n + 1 = n + 1)
  refine { exact := ?_ }
  let S := ShortComplex.mk (K.iCycles n) (K.d n (n + 1)) (K.iCycles_d _ _)
  let φ : ShortComplex.mk (K.iCycles n) (K.toCycles n (n + 1))
      (by simp [← cancel_mono (K.iCycles (n + 1))]) ⟶ S :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := K.iCycles (n + 1)
      comm₂₃ := by simp [S] }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2
    (ShortComplex.exact_of_f_is_kernel S (K.cyclesIsKernel n (n + 1) (by simp)))

/-- Starting below the bound, the cycles belong to `I`, and their short exact sequences
remain exact after applying `F`. -/
private lemma map_acyclic (F : C ⥤ D) [F.Additive] (I : ObjectProperty C)
    (hI₀ : ∀ {Z : C}, IsZero Z → I Z)
    (hI₂ : ∀ S : ShortComplex C, S.ShortExact → I S.X₁ → I S.X₂ →
      I S.X₃ ∧ (S.map F).ShortExact)
    (K : CochainComplex C ℤ) (a : ℤ) [K.IsStrictlyGE a]
    (hK : K.Acyclic) (hIK : ∀ n, I (K.X n)) :
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic := by
  have hcycles : ∀ n, I (K.cycles n) := by
    intro n
    by_cases hn : n < a
    · exact hI₀ ((K.isZero_of_isStrictlyGE a n hn).of_mono (K.iCycles n))
    · have hbase : I (K.cycles a) := by
        have := epi_toCycles K hK (show a - 1 + 1 = a by omega)
        exact hI₀ ((K.isZero_of_isStrictlyGE a (a - 1) (by omega)).of_epi (K.toCycles (a - 1) a))
      exact Int.leInduction hbase (fun n hn ih ↦
        (hI₂ _ (cycles_shortExact K hK n) ih (hIK n)).1) n (by omega)
  have hmap (n : ℤ) := (hI₂ _ (cycles_shortExact K hK n) (hcycles n) (hIK n)).2
  intro n
  rw [HomologicalComplex.exactAt_iff' _ (n - 1) n (n + 1) (by simp) (by simp)]
  have hprev := hmap (n - 1)
  have hnext := hmap (n + 1)
  have : Epi (F.map (K.toCycles (n - 1) n)) := by
    have e : n - 1 + 1 = n := by omega
    have hp := hprev.epi_g
    dsimp only [ShortComplex.map_g] at hp
    rwa [e] at hp
  have : Mono (F.map (K.iCycles (n + 1))) := hnext.mono_f
  let S := ShortComplex.mk (F.map (K.d (n - 1) n)) (F.map (K.toCycles n (n + 1)))
    (by rw [← F.map_comp, K.d_toCycles, F.map_zero])
  let φ : S ⟶
      (ShortComplex.mk (K.iCycles n) (K.toCycles n (n + 1))
        (by simp [← cancel_mono (K.iCycles (n + 1))])).map F :=
    { τ₁ := F.map (K.toCycles (n - 1) n)
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by simp [S, ← F.map_comp]
      comm₂₃ := by simp [S] }
  let S' := ShortComplex.mk (F.map (K.d (n - 1) n)) (F.map (K.d n (n + 1)))
    (by rw [← F.map_comp, K.d_comp_d, F.map_zero])
  let ψ : S ⟶ S' :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := F.map (K.iCycles (n + 1))
      comm₁₂ := by simp [S, S']
      comm₂₃ := by simp [S, S', ← F.map_comp] }
  dsimp only [HomologicalComplex.sc', Functor.mapHomologicalComplex_obj_d,
    Functor.mapHomologicalComplex_obj_X]
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono ψ).1
    ((ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 (hmap n).exact)

/-- A monomorphic quasi-isomorphism between complexes of `I` has an acyclic cokernel
whose terms belong to `I`. Applying `F` preserves its short exact sequence. -/
private lemma map_mono_quasiIso (F : C ⥤ D) [F.Additive] (I : ObjectProperty C)
    (hI₀ : ∀ {Z : C}, IsZero Z → I Z)
    (hI₂ : ∀ S : ShortComplex C, S.ShortExact → I S.X₁ → I S.X₂ →
      I S.X₃ ∧ (S.map F).ShortExact)
    {K L : CochainComplex C ℤ} (f : K ⟶ L) [Mono f] [QuasiIso f]
    (hL : CochainComplex.plus C L) (hIK : ∀ n, I (K.X n)) (hIL : ∀ n, I (L.X n)) :
    QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f) := by
  let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel f }
  have he (n : ℤ) := hS.map_of_exact (eval C (ComplexShape.up ℤ) n)
  have hp (n : ℤ) := hI₂ _ (he n) (hIK n) (hIL n)
  have hmap : (S.map (F.mapHomologicalComplex (ComplexShape.up ℤ))).ShortExact :=
    shortExact_of_degreewise_shortExact _ fun n ↦ (hp n).2
  obtain ⟨a, ha⟩ := hL
  have hc : (cokernel f).IsStrictlyGE a := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro n hn
    exact IsZero.of_epi ((cokernel.π f).f n) (L.isZero_of_isStrictlyGE a n hn)
  have hac := map_acyclic F I hI₀ hI₂ (cokernel f) a (hS.acyclic_X₃ inferInstance)
    (fun n ↦ (hp n).1)
  constructor
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have : Mono (homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f) n) :=
    (hmap.homology_exact₁ (n - 1) n (by simp)).mono_g
      ((hac (n - 1)).isZero_homology.eq_of_src _ _)
  have : Epi (homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f) n) :=
    (hmap.homology_exact₂ n).epi_f ((hac n).isZero_homology.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-- Adding the contractible cone of an identity does not change the homotopy type. -/
private noncomputable def coneBiprodHomotopyEquiv (K L : CochainComplex C ℤ) :
    HomotopyEquiv (CochainComplex.mappingCone (𝟙 K) ⊞ L) L where
  hom := biprod.snd
  inv := biprod.inr
  homotopyHomInvId := by
    let h₀ := CochainComplex.mappingCone.homotopyToZeroOfId K
    let h₁ := (h₀.compRight
      (biprod.inl : _ ⟶ CochainComplex.mappingCone (𝟙 K) ⊞ L)).compLeft
        (biprod.fst : CochainComplex.mappingCone (𝟙 K) ⊞ L ⟶ _)
    let h₂ := Homotopy.add h₁ (Homotopy.refl (biprod.snd ≫ biprod.inr))
    exact (Homotopy.ofEq (by simp)).trans (h₂.symm.trans (Homotopy.ofEq (by simp)))
  homotopyInvHomId := Homotopy.ofEq (by simp)

/-- Factor through a direct sum with a contractible cone and resolve that sum by `I`.
The resulting comparison maps are monomorphic quasi-isomorphisms. This avoids requiring
that `I` itself be closed under direct sums. -/
public lemma map_quasiIso (F : C ⥤ D) [F.Additive] (I : ObjectProperty C)
    (hI₁ : ∀ X : C, ∃ (Y : C) (_ : I Y) (i : X ⟶ Y), Mono i)
    (hI₂ : ∀ S : ShortComplex C, S.ShortExact → I S.X₁ → I S.X₂ →
      I S.X₃ ∧ (S.map F).ShortExact)
    {K L : CochainComplex C ℤ} (f : K ⟶ L) [QuasiIso f]
    (hK : CochainComplex.plus C K) (hL : CochainComplex.plus C L)
    (hIK : ∀ n, I (K.X n)) (hIL : ∀ n, I (L.X n)) :
    QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f) := by
  have hI₀ : ∀ {Z : C}, IsZero Z → I Z := zero_mem F I hI₁ hI₂
  have : I.ContainsZero := ⟨0, isZero_zero C, hI₀ (isZero_zero C)⟩
  let M := CochainComplex.mappingCone (𝟙 K) ⊞ L
  let e := coneBiprodHomotopyEquiv K L
  let i : K ⟶ M := biprod.lift (CochainComplex.mappingCone.inr (𝟙 K)) f
  have fac : i ≫ e.hom = f := biprod.lift_snd _ _
  have : Mono (CochainComplex.mappingCone.inr (𝟙 K)) := by
    apply HomologicalComplex.mono_of_mono_f
    intro n
    have : IsSplitMono ((CochainComplex.mappingCone.inr (𝟙 K)).f n) :=
      IsSplitMono.mk' { retraction := (CochainComplex.mappingCone.snd (𝟙 K)).v n n (by omega),
                         id := CochainComplex.mappingCone.inr_f_snd_v (𝟙 K) n }
    infer_instance
  have : Mono i := by dsimp [i]; infer_instance
  have : QuasiIso i := by
    rw [← quasiIso_iff_comp_right i e.hom, fac]
    infer_instance
  have hM : CochainComplex.plus C M := by
    obtain ⟨a, ha⟩ := hK
    obtain ⟨b, hb⟩ := hL
    have hc := CochainComplex.isStrictlyGE_mappingCone (𝟙 K) a a (min (a - 1) b)
      (by omega) (by omega)
    have hl := L.isStrictlyGE_of_ge (min (a - 1) b) b (by omega)
    refine ⟨min (a - 1) b, ?_⟩
    rw [CochainComplex.isStrictlyGE_iff]
    intro n hn
    exact IsZero.of_iso
      ((biprod_isZero_iff _ _).2
        ⟨(CochainComplex.mappingCone (𝟙 K)).isZero_of_isStrictlyGE _ n hn,
          L.isZero_of_isStrictlyGE _ n hn⟩) ((eval C (ComplexShape.up ℤ) n).mapBiprod _ _)
  obtain ⟨a, ha⟩ := hM
  obtain ⟨N, r, hr, hIN, hmr, hn⟩ := CochainComplex.exists_quasiIso_prop_isStrictlyGE I hI₁ a M
  have : Mono r := HomologicalComplex.mono_of_mono_f r (hmr ha)
  have hir := map_mono_quasiIso F I hI₀ hI₂ (i ≫ r) ⟨a, hn⟩ hIK hIN
  have : Mono e.inv := by dsimp [e, coneBiprodHomotopyEquiv]; infer_instance
  have hjr := map_mono_quasiIso F I hI₀ hI₂ (e.inv ≫ r) ⟨a, hn⟩ hIL hIN
  let G := F.mapHomologicalComplex (ComplexShape.up ℤ)
  have : QuasiIso (G.map e.inv) := (F.mapHomotopyEquiv e).quasiIso_inv
  have : QuasiIso (G.map e.hom) := (F.mapHomotopyEquiv e).quasiIso_hom
  have : QuasiIso (G.map e.inv ≫ G.map r) := by
    rw [← G.map_comp]
    exact hjr
  have : QuasiIso (G.map r) := quasiIso_of_comp_left (G.map e.inv) (G.map r)
  have : QuasiIso (G.map i ≫ G.map r) := by
    rw [← G.map_comp]
    exact hir
  have : QuasiIso (G.map i) := quasiIso_of_comp_right (G.map i) (G.map r)
  rw [← fac, G.map_comp]
  exact quasiIso_comp _ _

section Localization
variable {A B : Type*} [Category* A] [Category* B]

/-- A fully faithful inclusion with enough right resolutions induces an equivalence
after localization. Fractions and their equality relations can be resolved in the subcategory. -/
@[sga "4½ Etat_0 4.2.3" "more general"]
public lemma localizedEquivalence_of_rightResolutions
    {W₁ : MorphismProperty A} {W₂ : MorphismProperty B}
    (Φ : LocalizerMorphism W₁ W₂) [Φ.IsInduced] [Φ.functor.Full] [Φ.functor.Faithful]
    [W₁.HasLeftCalculusOfFractions] [W₂.HasLeftCalculusOfFractions]
    [Φ.HasRightResolutions] : Φ.IsLocalizedEquivalence := by
  let L₁ := W₁.Q
  let L₂ := W₂.Q
  let G := Φ.localizedFunctor L₁ L₂
  have e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ G := CatCommSq.iso Φ.functor L₁ L₂ G
  have N : ∀ {X Y : A} (h : X ⟶ Y),
      e.hom.app X ≫ G.map (L₁.map h) = L₂.map (Φ.functor.map h) ≫ e.hom.app Y :=
    fun h ↦ (e.hom.naturality h).symm
  have hsat : ∀ {X Y : A} (h : X ⟶ Y), W₂ (Φ.functor.map h) → W₁ h := by
    intro X Y h hh
    rw [← Φ.inverseImage_eq]
    exact hh
  have : L₁.EssSurj := Localization.essSurj L₁ W₁
  have : G.EssSurj := by
    have h := Φ.essSurj_of_hasRightResolutions L₂
    refine ⟨fun Y ↦ ?_⟩
    obtain ⟨X, ⟨i⟩⟩ := h.mem_essImage Y
    exact ⟨L₁.obj X, ⟨(e.app X).symm ≪≫ i⟩⟩
  have : G.Full := by
    refine G.full_of_comp_essSurj L₁ (fun X Y φ ↦ ?_)
    obtain ⟨ψ, hψ⟩ := Localization.exists_leftFraction L₂ W₂
      (e.hom.app X ≫ φ ≫ e.inv.app Y)
    let ρ : Φ.RightResolution ψ.Y' := Classical.arbitrary _
    let g : W₁.LeftFraction X Y :=
      { Y' := ρ.X₁
        f := Φ.functor.preimage (ψ.f ≫ ρ.w)
        s := Φ.functor.preimage (ψ.s ≫ ρ.w)
        hs := hsat _ (by simpa using W₂.comp_mem _ _ ψ.hs ρ.hw) }
    have hφ : e.hom.app X ≫ φ = ψ.map L₂ (Localization.inverts _ _) ≫ e.hom.app Y := by
      rw [← hψ]
      simp
    refine ⟨g.map L₁ (Localization.inverts _ _), ?_⟩
    have := Localization.inverts L₁ W₁ _ g.hs
    rw [← cancel_mono (G.map (L₁.map g.s)), ← G.map_comp,
      MorphismProperty.LeftFraction.map_comp_map_s,
      ← cancel_epi (e.hom.app X), N, ← Category.assoc, hφ,
      Category.assoc, N, ← Category.assoc]
    congr 1
    simp [g]
  have : G.Faithful := by
    refine Functor.faithful_of_comp_of_hasLeftCalculusOfFractions L₁ W₁ G
      (fun X Y f g hfg ↦ ?_)
    have h2 : L₂.map (Φ.functor.map f) = L₂.map (Φ.functor.map g) := by
      rw [← cancel_mono (e.hom.app Y), ← N, ← N, hfg]
    rw [MorphismProperty.map_eq_iff_postcomp L₂ W₂] at h2
    obtain ⟨Z, s, hsW, fac⟩ := h2
    let ρ : Φ.RightResolution Z := Classical.arbitrary _
    let t : Y ⟶ ρ.X₁ := Φ.functor.preimage (s ≫ ρ.w)
    have ht : W₁ t := hsat _ (by simpa [t] using W₂.comp_mem _ _ hsW ρ.hw)
    have := Localization.inverts L₁ W₁ _ ht
    rw [← cancel_mono (L₁.map t), ← L₁.map_comp, ← L₁.map_comp]
    congr 1
    apply Φ.functor.map_injective
    simp [t, ← Category.assoc, fac]
  have : G.IsEquivalence := { }
  exact LocalizerMorphism.IsLocalizedEquivalence.mk' Φ L₁ L₂ G

/-- The inclusion of a class of objects `P`, as a localizer morphism from the morphisms of `P`
which belong to `W` to `W`. -/
public abbrev inclusionLocalizerMorphism (W : MorphismProperty A) (P : ObjectProperty A) :
    LocalizerMorphism (W.inverseImage P.ι) W where
  functor := P.ι
  map _ _ _ h := h

/-- Enough right resolutions in a full subcategory give a right derivability structure:
Ore squares provide connected resolution categories and resolutions of arrows. -/
private lemma rightDerivability_of_resolutions (W : MorphismProperty A)
    [W.HasLeftCalculusOfFractions] (P : ObjectProperty A)
    (hP : ∀ X, ∃ (Y : A) (_ : P Y) (r : X ⟶ Y), W r) :
    (inclusionLocalizerMorphism W P).IsRightDerivabilityStructure := by
  let Φ := inclusionLocalizerMorphism W P
  have hres : Φ.HasRightResolutions := by
    intro X
    obtain ⟨Y, hY, r, hr⟩ := hP X
    exact ⟨{ X₁ := ⟨Y, hY⟩, w := r, hw := hr }⟩
  have key : ∀ {X' X Y : A} (s : X' ⟶ X) (hs : W s) (f : X' ⟶ Y),
      ∃ (Z : A) (_ : P Z) (a : X ⟶ Z) (b : Y ⟶ Z), W b ∧ f ≫ b = s ≫ a := by
    intro X' X Y s hs f
    obtain ⟨q, hq⟩ := (MorphismProperty.RightFraction.mk s hs f).exists_leftFraction
    dsimp only at hq
    obtain ⟨Z, hZ, r, hr⟩ := hP q.Y'
    exact ⟨Z, hZ, q.f ≫ r, q.s ≫ r, W.comp_mem _ _ q.hs hr, by simp [reassoc_of% hq]⟩
  have : (W.inverseImage P.ι).HasLeftCalculusOfFractions := by
    constructor
    · intro X Y φ
      obtain ⟨Z, hZ, a, b, hb, hab⟩ := key φ.s.hom φ.hs φ.f.hom
      exact ⟨{ Y' := ⟨Z, hZ⟩, f := ObjectProperty.homMk a, s := ObjectProperty.homMk b, hs := hb },
        ObjectProperty.hom_ext _ hab⟩
    · intro X' X Y f g s hs h
      obtain ⟨Z, t, ht, hfg⟩ := MorphismProperty.HasLeftCalculusOfFractions.ext
        f.hom g.hom s.hom hs (congrArg (fun t ↦ t.hom) h)
      obtain ⟨Z', hZ', r, hr⟩ := hP Z
      exact ⟨⟨Z', hZ'⟩, ObjectProperty.homMk (t ≫ r), W.comp_mem _ _ ht hr,
        ObjectProperty.hom_ext _ (by simp [reassoc_of% hfg])⟩
  have : Φ.IsInduced := ⟨rfl⟩
  have : Φ.IsLocalizedEquivalence := localizedEquivalence_of_rightResolutions Φ
  have : ∀ X, IsConnected (Φ.RightResolution X) := by
    intro X
    apply zigzag_isConnected
    intro R S
    obtain ⟨Z, hZ, c, d, hd, hcd⟩ := key R.w R.hw S.w
    let T : Φ.RightResolution X := { X₁ := ⟨Z, hZ⟩, w := S.w ≫ d, hw := W.comp_mem _ _ S.hw hd }
    let a : R ⟶ T := { f := ObjectProperty.homMk c, comm := by simp [Φ, T, hcd] }
    let b : S ⟶ T := { f := ObjectProperty.homMk d, comm := by simp [Φ, T] }
    exact (Zigzag.of_hom a).trans (Zigzag.of_inv b)
  have : Φ.arrow.HasRightResolutions := by
    intro g
    obtain ⟨X, hX, r, hr⟩ := hP g.left
    obtain ⟨Y, hY, a, b, hb, hab⟩ := key r hr g.hom
    exact ⟨{
      X₁ := Arrow.mk (ObjectProperty.homMk a : (⟨X, hX⟩ : P.FullSubcategory) ⟶ ⟨Y, hY⟩)
      w := Arrow.homMk r b (by simp [Φ, Functor.mapArrow, hab])
      hw := ⟨hr, hb⟩ }⟩
  exact LocalizerMorphism.IsRightDerivabilityStructure.mk' Φ

end Localization

/-- The bounded below complexes all of whose terms satisfy `I`, as objects of `K⁺(C)`. -/
public abbrev termwise (I : ObjectProperty C) : ObjectProperty (HomotopyCategory.Plus C) :=
  fun X ↦ ∀ n, I (X.obj.as.X n)

/-- A morphism of `K⁺(C)` between complexes with terms in `I` which is a quasi-isomorphism is
sent by `F` to a quasi-isomorphism. -/
private lemma mapHomotopyCategoryPlus_map_mem_quasiIso (F : C ⥤ D) [F.Additive]
    (I : ObjectProperty C) (hI₁ : ∀ X : C, ∃ (Y : C) (_ : I Y) (i : X ⟶ Y), Mono i)
    (hI₂ : ∀ S : ShortComplex C, S.ShortExact → I S.X₁ → I S.X₂ →
      I S.X₃ ∧ (S.map F).ShortExact)
    {X Y : HomotopyCategory.Plus C} (hX : termwise I X) (hY : termwise I Y) (f : X ⟶ Y)
    (hf : HomotopyCategory.Plus.quasiIso C f) :
    HomotopyCategory.Plus.quasiIso D (F.mapHomotopyCategoryPlus.map f) := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.Plus.quotient_obj_surjective X
  obtain ⟨L, rfl⟩ := HomotopyCategory.Plus.quotient_obj_surjective Y
  obtain ⟨g, rfl⟩ := (HomotopyCategory.Plus.quotient C).map_surjective f
  rw [HomotopyCategory.Plus.quasiIso_iff, HomotopyCategory.Plus.quotient_map_hom] at hf
  have hg : QuasiIso g.hom := (HomotopyCategory.quotient_map_mem_quasiIso_iff g.hom).1 hf
  rw [HomotopyCategory.Plus.quasiIso_iff]
  dsimp only [Functor.mapHomotopyCategoryPlus, ObjectProperty.lift_map, ObjectProperty.homMk_hom,
    Functor.comp_map, ObjectProperty.ι_map, HomotopyCategory.Plus.quotient_map_hom]
  exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).2
    (map_quasiIso F I hI₁ hI₂ g.hom K.property L.property hX hY)

/-- The complex `A[0]` has all its terms in `I` as soon as `A` does and `I` contains the zero
objects. -/
private lemma termwise_singleFunctor (I : ObjectProperty C) (hI₀ : ∀ {Z : C}, IsZero Z → I Z)
    {A : C} (hA : I A) : termwise I ((HomotopyCategory.Plus.singleFunctor C 0).obj A) := by
  have e : ((HomotopyCategory.Plus.singleFunctor C 0).obj A).obj.as =
      (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj A := rfl
  intro n
  rw [e]
  by_cases hn : n = 0
  · subst n
    rwa [HomologicalComplex.single_obj_X_self]
  · exact hI₀ (HomologicalComplex.isZero_single_obj_X _ _ A n hn)

end RightAcyclicCriterion

open RightAcyclicCriterion

variable [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D]

omit [HasDerivedCategory C] in
/-- Under the adapted-class hypotheses of Stacks 05T8, the full subcategory of bounded
below complexes with terms in `I` is a right derivability structure, and it derives the
functor induced by `F` with values in `D⁺(D)`. -/
public lemma isRightDerivabilityStructure_and_derives_of_adapted
    (F : C ⥤ D) [F.Additive] (I : ObjectProperty C)
    (hI₁ : ∀ X : C, ∃ (Y : C) (_ : I Y) (i : X ⟶ Y), Mono i)
    (hI₂ : ∀ S : ShortComplex C, S.ShortExact → I S.X₁ → I S.X₂ →
      I S.X₃ ∧ (S.map F).ShortExact) :
    (inclusionLocalizerMorphism (HomotopyCategory.Plus.quasiIso C)
        (termwise I)).IsRightDerivabilityStructure ∧
      (inclusionLocalizerMorphism (HomotopyCategory.Plus.quasiIso C) (termwise I)).Derives
        (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh) := by
  have hI₀ : ∀ {Z : C}, IsZero Z → I Z := zero_mem F I hI₁ hI₂
  have : I.ContainsZero := ⟨0, isZero_zero C, hI₀ (isZero_zero C)⟩
  have : (HomotopyCategory.Plus.quasiIso C).HasLeftCalculusOfFractions := by
    rw [HomotopyCategory.Plus.quasiIso_eq_subcategoryAcyclic_trW]
    infer_instance
  refine ⟨rightDerivability_of_resolutions _ _ (fun X ↦ ?_), fun X Y f hf ↦ ?_⟩
  · obtain ⟨a, ha⟩ := (HomotopyCategory.plus_quotient_obj_iff X.obj.as).1 X.property
    obtain ⟨N, r, hr, hIN, _, hn⟩ :=
      CochainComplex.exists_quasiIso_prop_isStrictlyGE I hI₁ a X.obj.as
    refine ⟨⟨(HomotopyCategory.quotient C _).obj N,
      (HomotopyCategory.plus_quotient_obj_iff N).2 ⟨a, hn⟩⟩, hIN,
      ObjectProperty.homMk ((HomotopyCategory.quotient C _).map r), ?_⟩
    rw [HomotopyCategory.Plus.quasiIso_iff]
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff r).2 hr
  · rw [Functor.comp_map, Functor.comp_map, ObjectProperty.ι_map]
    exact Localization.inverts _ (HomotopyCategory.Plus.quasiIso D) _
      (mapHomotopyCategoryPlus_map_mem_quasiIso F I hI₁ hI₂ X.property Y.property f.hom hf)

/-- **Stacks 05T8.** Let `F : C ⥤ D` be an additive functor between abelian categories and let
`I` be a class of objects of `C` such that every object of `C` is a subobject of an object
satisfying `I`, and such that for every short exact sequence `0 ⟶ P ⟶ Q ⟶ R ⟶ 0` with `P` and
`Q` satisfying `I` the object `R` satisfies `I` and `0 ⟶ F P ⟶ F Q ⟶ F R ⟶ 0` is short exact.
Then the pointwise right derived functor exists on `K⁺(C)`, and every object satisfying `I`
is acyclic for it. -/
@[stacks 05T8 "The right derived functor `RF` is defined everywhere on `K⁺(C)`, and every
  object of `I` is acyclic for it.",
  sga "4 V 0.4" "M acyclic for u",
  sga "4½ Etat_0 4.2.3.2" "SES-stable σ, + case"]
public theorem hasPointwiseRightDerivedFunctor_and_le_rightAcyclic
    (F : C ⥤ D) [F.Additive] (I : ObjectProperty C)
    (hI₁ : ∀ X : C, ∃ (Y : C) (_ : I Y) (i : X ⟶ Y), Mono i)
    (hI₂ : ∀ S : ShortComplex C, S.ShortExact → I S.X₁ → I S.X₂ →
      I S.X₃ ∧ (S.map F).ShortExact) :
    ∃ h : (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).HasPointwiseRightDerivedFunctor
        (HomotopyCategory.Plus.quasiIso C),
      letI := h
      I ≤ F.rightAcyclic := by
  obtain ⟨hΦ, hderive⟩ := isRightDerivabilityStructure_and_derives_of_adapted F I hI₁ hI₂
  have h := hderive.hasPointwiseRightDerivedFunctor
  refine ⟨h, fun A hA ↦ ?_⟩
  exact hderive.isIso_of_isRightDerivedFunctor _
    ⟨_, termwise_singleFunctor I (zero_mem F I hI₁ hI₂) hA⟩

/-- **Stacks 05T8.** Let `F : C ⥤ D` be an additive functor between abelian categories whose
right derived functor `RF : D⁺(C) ⥤ D⁺(D)` exists, and let `I` be a class of objects of `C` such
that every object of `C` is a subobject of an object satisfying `I`, and such that for every short
exact sequence `0 ⟶ P ⟶ Q ⟶ R ⟶ 0` with `P` and `Q` satisfying `I` the object `R` satisfies `I`
and `0 ⟶ F P ⟶ F Q ⟶ F R ⟶ 0` is short exact. Then every object satisfying `I` is acyclic for
`RF`. -/
@[stacks 05T8, sga "4 V 0.4" "M acyclic for u", sga "4½ Etat_0 4.2.3.2" "σ right f-acyclic"]
public theorem le_rightAcyclic (F : C ⥤ D) [F.Additive]
    [(F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso C)] (I : ObjectProperty C)
    (hI₁ : ∀ X : C, ∃ (Y : C) (_ : I Y) (i : X ⟶ Y), Mono i)
    (hI₂ : ∀ S : ShortComplex C, S.ShortExact → I S.X₁ → I S.X₂ →
      I S.X₃ ∧ (S.map F).ShortExact) :
    I ≤ F.rightAcyclic := by
  obtain ⟨hΦ, hderive⟩ := isRightDerivabilityStructure_and_derives_of_adapted F I hI₁ hI₂
  exact fun A hA ↦ hderive.isIso_of_isRightDerivedFunctor _
    ⟨_, termwise_singleFunctor I (zero_mem F I hI₁ hI₂) hA⟩

end

end CategoryTheory.Functor

end

end

section

/-!
# A class of objects computing a left derived functor

Let `F : C ⥤ D` be an additive functor between abelian categories, with left derived functor
`LF : D⁻(C) ⥤ D⁻(D)`. Let `P` be a class of objects of `C` such that

* every object of `C` is a quotient of an object satisfying `P`, and
* for every short exact sequence `0 ⟶ P ⟶ Q ⟶ R ⟶ 0` of `C` with `Q` and `R` satisfying `P`, the
  object `P` satisfies `P` too and `0 ⟶ F P ⟶ F Q ⟶ F R ⟶ 0` is again short exact.

Then every object satisfying `P` is left acyclic for `F`, i.e. computes `LF`. For `P` the
projective objects of a category with enough projectives this is the classical statement that
projective objects are acyclic; the point of the lemma is that a class of `F`-adapted objects,
such as the flat modules for the derived tensor product, does just as well.

This is the dual of the statement that a class of `F`-adapted objects computing `RF` consists of
right acyclic objects ([Stacks, Tag 05T8]), and is proved from it by reading it in the opposite
categories, applied to `F.op : Cᵒᵖ ⥤ Dᵒᵖ` and the class `Pᵒᵖ`. Dualizing the hypotheses is what
the lemmas below do: an epimorphism `Y ⟶ X` out of an object satisfying `P` is a monomorphism
`Xᵒᵖ ⟶ Yᵒᵖ` into an object satisfying `Pᵒᵖ`, and a short exact sequence of `Cᵒᵖ` with its first
two terms in `Pᵒᵖ` is the opposite of a short exact sequence of `C` with its last two terms in
`P`, whose image under `F` is short exact exactly when the image of the original one under `F.op`
is.

## Main results

* `CategoryTheory.Functor.le_rightAcyclic_op`: Stacks 05T9.

## Implementation notes

The class `P ⊂ Ob(C)` of the source is a `CategoryTheory.ObjectProperty C`, i.e. a predicate on
objects, and "every object of `C` is a quotient of an element of `P`" is spelled, as in
[Stacks, Tag 05T7], as the existence for each `X` of an epimorphism onto `X` out of an object
satisfying `P`; Mathlib has no name for this hypothesis. A short exact sequence
`0 ⟶ P ⟶ Q ⟶ R ⟶ 0` is a `CategoryTheory.ShortComplex C` which is `ShortComplex.ShortExact`, and
exactness of `0 ⟶ F P ⟶ F Q ⟶ F R ⟶ 0` is `ShortExact` for its image `S.map F` (an additive
functor preserves zero morphisms, so the image short complex is defined).

Left acyclicity is not a separate notion here: as recorded in [Stacks, Tag 0157], an object `A` of
`C` is acyclic for `LF` exactly when `Aᵒᵖ` is acyclic for `R(Fᵒᵖ)`, because passing to opposite
categories exchanges `K⁻(C)` with `K⁺(Cᵒᵖ)` and `LF` with `R(Fᵒᵖ)`; Mathlib's derived functor API
(`Functor.mapHomotopyCategoryPlus`, `DerivedCategory.Plus.Qh`, `Functor.totalRightDerived`) is
available for `K⁺` only. So "every object of `P` is acyclic for `LF`" is the inequality
`P.op ≤ F.op.rightAcyclic` of object properties of `Cᵒᵖ`, which unfolds to
`∀ X : C, P X → F.op.rightAcyclic (op X)`.

The source's hypothesis (2) is a single condition with a conjunction of two conclusions, and is
stated that way rather than split in two, because the intended instances (`P` the projective, or
the flat, or the `F`-acyclic objects) verify the two together and because the source's own proof
uses both halves at every application. The source does not assume that a zero object satisfies
`P`: this follows from the hypotheses, since (1) makes `P` nonempty and (2) applied to
`0 ⟶ 0 ⟶ Q ⟶ Q ⟶ 0` puts a zero object in `P`. It is therefore not assumed here either, even
though the route through [Stacks, Tag 05T7] needs it.

The source lets `LF` be a partially defined functor and concludes acyclicity of the objects of `P`
at which it is then automatically defined; here `LF` is assumed everywhere defined on `D⁻(C)` —
that is, `R(Fᵒᵖ)` is assumed everywhere defined on `D⁺(Cᵒᵖ)` (`HasRightDerivedFunctor`) — which is
what makes the unit whose invertibility is acyclicity available at all. This holds in the intended
applications, in particular whenever `C` has enough projectives.

The image `S.map F.op` of a short complex `S` of `Cᵒᵖ` under `F.op` is definitionally the opposite
of the image `S.unop.map F` of `S.unop` under `F`, so `mapOp_op` below, which records this, is
proved by `rfl`; it is stated because a proof that rewrites with it reads as the mathematics
rather than as an unfolding.

## References

* [Stacks project, Tag 05T9](https://stacks.math.columbia.edu/tag/05T9)
* [Stacks project, Tag 05T8](https://stacks.math.columbia.edu/tag/05T8)
-/

@[expose] public section

open CategoryTheory Limits Opposite

namespace CategoryTheory

universe w w' v v' u u'

section

variable {C : Type u} [Category.{v} C]

/-- If every object of `C` is a quotient of an object satisfying `P`, then every object of `Cᵒᵖ`
is a subobject of an object satisfying `Pᵒᵖ`. -/
private lemma exists_mono_op (P : ObjectProperty C)
    (hP : ∀ X : C, ∃ (Y : C) (_ : P Y) (p : Y ⟶ X), Epi p) (X : Cᵒᵖ) :
    ∃ (Y : Cᵒᵖ) (_ : P.op Y) (i : X ⟶ Y), Mono i := by
  obtain ⟨Y, hY, p, hp⟩ := hP X.unop
  exact ⟨op Y, hY, p.op, inferInstance⟩

end

section

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [Abelian C] [Abelian D]

/-- The image under `F.op` of a short complex of `Cᵒᵖ` is the opposite of the image under `F` of
its opposite short complex. -/
private lemma mapOp_op (F : C ⥤ D) [F.Additive] (S : ShortComplex Cᵒᵖ) :
    S.map F.op = (S.unop.map F).op :=
  rfl

/-- If for every short exact sequence of `C` whose last two terms satisfy `P` the first one does
too and the image under `F` is short exact, then for every short exact sequence of `Cᵒᵖ` whose
first two terms satisfy `Pᵒᵖ` the last one does too and the image under `F.op` is short exact. -/
private lemma shortExact_map_op (F : C ⥤ D) [F.Additive] (P : ObjectProperty C)
    (hP : ∀ S : ShortComplex C, S.ShortExact → P S.X₂ → P S.X₃ →
      P S.X₁ ∧ (S.map F).ShortExact)
    (S : ShortComplex Cᵒᵖ) (hS : S.ShortExact) (h₁ : P.op S.X₁) (h₂ : P.op S.X₂) :
    P.op S.X₃ ∧ (S.map F.op).ShortExact := by
  obtain ⟨h, hmap⟩ := hP S.unop hS.unop h₂ h₁
  exact ⟨h, (mapOp_op F S).symm ▸ hmap.op⟩

end

namespace Functor

/-- **Stacks 05T9.** Let `F : C ⥤ D` be an additive functor between abelian categories and let
`P` be a class of objects of `C` such that every object of `C` is a quotient of an object
satisfying `P`, and such that for every short exact sequence `0 ⟶ P ⟶ Q ⟶ R ⟶ 0` with `Q` and
`R` satisfying `P` the object `P` satisfies `P` and `0 ⟶ F P ⟶ F Q ⟶ F R ⟶ 0` is short exact.
Then every object satisfying `P` is acyclic for the left derived functor `LF` of `F`, i.e. its
opposite is acyclic for the right derived functor of `F.op`. -/
@[stacks 05T9, sga "4 XVII 1.2.6", sga "4½ Etat_0 4.2.3.2" "σ left f-acyclic"]
public theorem le_rightAcyclic_op {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
    [Abelian C] [Abelian D] [HasDerivedCategory.{w} Cᵒᵖ] [HasDerivedCategory.{w'} Dᵒᵖ]
    (F : C ⥤ D) [F.Additive]
    [(F.op.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso Cᵒᵖ)] (P : ObjectProperty C)
    (hP₁ : ∀ X : C, ∃ (Y : C) (_ : P Y) (p : Y ⟶ X), Epi p)
    (hP₂ : ∀ S : ShortComplex C, S.ShortExact → P S.X₂ → P S.X₃ →
      P S.X₁ ∧ (S.map F).ShortExact) :
    P.op ≤ F.op.rightAcyclic :=
  F.op.le_rightAcyclic P.op (exists_mono_op P hP₁) (shortExact_map_op F P hP₂)

end Functor

end CategoryTheory

end

end
