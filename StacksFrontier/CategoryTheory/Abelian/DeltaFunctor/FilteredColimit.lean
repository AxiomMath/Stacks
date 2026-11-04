module

public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import StacksCore.CategoryTheory.Abelian.DeltaFunctor.Basic

/-! # A δ-functor commuting with colimits in degree zero commutes with them in every degree

Let `D` be a cohomological δ-functor (`CategoryTheory.DeltaFunctor`, Stacks 010Q) from a
Grothendieck abelian category `A` to an abelian category `B`, and let `I` be a shape for which
colimits in both `A` and `B` exist and are exact.  This file proves that the comparison map
`colimᵢ Dⁿ(Gᵢ) ⟶ Dⁿ(colimᵢ Gᵢ)` is an isomorphism for every `n` and every diagram `G : I ⥤ A`,
given

* the same statement in degree `0`, for every diagram, and
* the vanishing of `Dⁿ⁺¹` on the colimit of a diagram of injective objects.

This is the inductive engine of the proof of Stacks 01FF (sheaf cohomology over a quasi-compact
open commutes with filtered colimits), with the two inputs of that proof abstracted into the two
hypotheses above: for `D = H^•(U, -)` the first is Stacks 009F and the second is the vanishing
claim that Stacks obtains from Stacks 01EW and Stacks 01EP.  The induction itself, the
functorial injective embedding of a diagram and the comparison of the two long exact sequences
are all carried out here, once and for all.

## Main results

* `exists_mono_pointwise_injective`: Stacks 079H for *diagrams*.  Every diagram `G : I ⥤ A` in a
  Grothendieck abelian category admits a pointwise monomorphism into a diagram whose values are
  injective objects.  This is the diagram form of Stacks 01DI used in the proof of Stacks 01FF,
  and it is obtained from Mathlib's functorial factorization of a morphism as a monomorphism
  followed by a morphism with the right lifting property against monomorphisms, transported to
  the functor category.
* `ShortComplex.exact_of_exact_evaluation`: a short complex of diagrams is exact as soon as it
  is pointwise exact.
* `DeltaFunctor.deltaNat`, `DeltaFunctor.topδ₁`, `DeltaFunctor.topδ₂`: the levelwise long exact
  sequences of a diagram of short exact sequences, assembled into short complexes of diagrams.
* `DeltaFunctor.ladder₁`, `DeltaFunctor.ladder₂`: the two comparison ladders from the colimit of
  the levelwise long exact sequences to the long exact sequence of the colimit, whose vertical
  maps are the comparison morphisms `Limits.colimit.post`.
* `DeltaFunctor.isIso_colimit_post_of_isIso_zero`: the conclusion.

## Design

The levelwise connecting morphisms `δ` assemble into a natural transformation of diagrams
(`DeltaFunctor.deltaNat`) precisely because `δ` is natural in the short exact sequence, applied
to the morphism of short exact sequences `ShortComplex.mapNatTrans` induced by a morphism of the
index category.  The same naturality, applied instead to the colimit cocone inclusions
`Limits.colim.ι`, is what makes the squares of `DeltaFunctor.ladder₁` and
`DeltaFunctor.ladder₂` involving `δ` commute; the remaining squares are
`Limits.colimit.map_post`.

Once both ladders exist, no diagram chase is needed.  Injectivity of the degree-`n + 1`
comparison map is Mathlib's four lemma `ShortComplex.mono_of_epi_of_epi_of_mono` applied to
`ladder₁`, and surjectivity is immediate from the commuting square of `ladder₂`: the composite
along the bottom is epi because the connecting morphism of the colimit sequence is (its target
`Dⁿ⁺¹` of the colimit of injectives vanishes), so the composite along the top is epi, hence so
is its second factor.  The exactness of the top rows is the exactness of `I`-colimits in `B`
applied to the pointwise exact short complexes of diagrams.

## References

* [Stacks Project, Tag 01FF](https://stacks.math.columbia.edu/tag/01FF)
* [Stacks Project, Tag 079H](https://stacks.math.columbia.edu/tag/079H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty ZeroObject

universe v₁ u₁ v₂ u₂ v₃ u₃ w

namespace CategoryTheory

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B]
  {I : Type u₃} [Category.{v₃} I]

/-! ### Generalities on diagrams -/

/-- **Stacks 079H for diagrams.** Every diagram `G : I ⥤ A` in a Grothendieck abelian category
admits a morphism into a diagram with injective values which is a monomorphism at every index.

Mathlib factors any morphism of `A` functorially as a monomorphism followed by a morphism with
the right lifting property against all monomorphisms, and a functorial factorization extends
pointwise to any functor category.  Factoring `G ⟶ 0` in `I ⥤ A` therefore gives a pointwise
monomorphism `G ⟶ E` with each `E.obj i ⟶ 0` having that right lifting property, which is
exactly injectivity of `E.obj i`. -/
theorem exists_mono_pointwise_injective [IsGrothendieckAbelian.{w} A] (G : I ⥤ A) :
    ∃ (E : I ⥤ A) (α : G ⟶ E), (∀ i, Mono (α.app i)) ∧ ∀ i, Injective (E.obj i) := by
  let fac := (functorialFactorizationData ((monomorphisms A).functorCategory I)
    ((monomorphisms A).rlp.functorCategory I)).factorizationData (0 : G ⟶ 0)
  refine ⟨fac.Z, fac.i, fun i => fac.hi i, fun i => ?_⟩
  exact (injective_iff_rlp_monomorphisms_of_isZero (fac.p.app i)
    ((isZero_zero (I ⥤ A)).obj i)).2 (fac.hp i)

/-- A diagram all of whose values are zero objects is a zero object. -/
theorem Functor.isZero_of_isZero_obj (X : I ⥤ B) (h : ∀ i, IsZero (X.obj i)) : IsZero X := by
  refine (IsZero.iff_id_eq_zero _).2 ?_
  ext i
  exact (IsZero.iff_id_eq_zero _).1 (h i)

/-- Whether the comparison morphism `colimᵢ H(Kᵢ) ⟶ H(colimᵢ Kᵢ)` is an isomorphism depends
only on the isomorphism class of `H`. -/
theorem Limits.isIso_colimit_post_of_natIso {C' : Type*} [Category* C'] {D' : Type*}
    [Category* D'] {J : Type*} [Category* J] (K : J ⥤ C') {H H' : C' ⥤ D'} (e : H ≅ H')
    [HasColimit K] [HasColimit (K ⋙ H)] [HasColimit (K ⋙ H')] [IsIso (colimit.post K H')] :
    IsIso (colimit.post K H) :=
  have : PreservesColimit K H' := preservesColimit_of_isIso_post H' K
  have : PreservesColimit K H := preservesColimit_of_natIso K e.symm
  inferInstance

/-- A short complex of diagrams is exact as soon as it is exact at every index: homology in a
functor category is computed pointwise, because evaluation is exact. -/
theorem ShortComplex.exact_of_exact_evaluation (T : ShortComplex (I ⥤ B))
    (h : ∀ i, (T.map ((evaluation I B).obj i)).Exact) : T.Exact := by
  rw [ShortComplex.exact_iff_isZero_homology]
  refine Functor.isZero_of_isZero_obj _ fun i => ?_
  have h1 := h i
  rw [ShortComplex.exact_iff_isZero_homology] at h1
  exact h1.of_iso (T.mapHomologyIso ((evaluation I B).obj i)).symm

namespace DeltaFunctor

/-! ### The levelwise long exact sequences of a diagram of short exact sequences -/

variable (D : DeltaFunctor A B) (S : ShortComplex (I ⥤ A))
  (hS : ∀ i, (S.map ((evaluation I A).obj i)).ShortExact)

/-- The connecting morphisms `δ : Dⁿ(X₃ᵢ) ⟶ Dⁿ⁺¹(X₁ᵢ)` of the levelwise short exact sequences,
assembled into a natural transformation of diagrams.  Naturality is the naturality of `δ` in the
short exact sequence, applied to the morphism of levelwise short exact sequences induced by a
morphism of the index category. -/
def deltaNat (n : ℕ) : S.X₃ ⋙ D.functor n ⟶ S.X₁ ⋙ D.functor (n + 1) where
  app i := D.δ (hS i) n
  naturality i j f := D.δ_naturality (hS i) (hS j) (S.mapNatTrans ((evaluation I A).map f)) n

/-- The short complex of diagrams whose value at `i` is the three-term stretch
`Dⁿ(X₂ᵢ) → Dⁿ(X₃ᵢ) → Dⁿ⁺¹(X₁ᵢ)` of the long exact sequence, i.e. `DeltaFunctor.scδ₁`. -/
def topδ₁ (n : ℕ) : ShortComplex (I ⥤ B) :=
  ShortComplex.mk (Functor.whiskerRight S.g (D.functor n)) (deltaNat D S hS n)
    (by ext i; exact D.map_g_δ (hS i) n)

/-- The short complex of diagrams whose value at `i` is the three-term stretch
`Dⁿ(X₃ᵢ) → Dⁿ⁺¹(X₁ᵢ) → Dⁿ⁺¹(X₂ᵢ)` of the long exact sequence, i.e. `DeltaFunctor.scδ₂`. -/
def topδ₂ (n : ℕ) : ShortComplex (I ⥤ B) :=
  ShortComplex.mk (deltaNat D S hS n) (Functor.whiskerRight S.f (D.functor (n + 1)))
    (by ext i; exact D.δ_map_f (hS i) n)

/-- `DeltaFunctor.topδ₁` evaluates to `DeltaFunctor.scδ₁` of the short exact sequence at `i`. -/
theorem topδ₁_map_eval (n : ℕ) (i : I) :
    (topδ₁ D S hS n).map ((evaluation I B).obj i) = D.scδ₁ (hS i) n := rfl

/-- `DeltaFunctor.topδ₂` evaluates to `DeltaFunctor.scδ₂` of the short exact sequence at `i`. -/
theorem topδ₂_map_eval (n : ℕ) (i : I) :
    (topδ₂ D S hS n).map ((evaluation I B).obj i) = D.scδ₂ (hS i) n := rfl

/-! ### The comparison ladders -/

variable [HasColimitsOfShape I A] [HasColimitsOfShape I B]

/-- The comparison ladder from the colimit of the levelwise stretches
`Dⁿ(X₂) → Dⁿ(X₃) → Dⁿ⁺¹(X₁)` to the corresponding stretch for the colimit short exact
sequence.  Its vertical maps are the comparison morphisms `Limits.colimit.post`. -/
def ladder₁ (hScol : (S.map colim).ShortExact) (n : ℕ) :
    (topδ₁ D S hS n).map colim ⟶ D.scδ₁ hScol n where
  τ₁ := colimit.post S.X₂ (D.functor n)
  τ₂ := colimit.post S.X₃ (D.functor n)
  τ₃ := colimit.post S.X₁ (D.functor (n + 1))
  comm₁₂ := colimit.map_post (α := S.g) (D.functor n)
  comm₂₃ := by
    dsimp only [topδ₁, ShortComplex.map_X₂, ShortComplex.map_g]
    refine colimit.hom_ext fun i => ?_
    have h := D.δ_naturality (hS i) hScol (S.mapNatTrans (colim.ι i)) n
    simp only [colimit.ι_post_assoc, colimit.ι_map_assoc, colimit.ι_post]
    exact h

/-- The comparison ladder from the colimit of the levelwise stretches
`Dⁿ(X₃) → Dⁿ⁺¹(X₁) → Dⁿ⁺¹(X₂)` to the corresponding stretch for the colimit short exact
sequence. -/
def ladder₂ (hScol : (S.map colim).ShortExact) (n : ℕ) :
    (topδ₂ D S hS n).map colim ⟶ D.scδ₂ hScol n where
  τ₁ := colimit.post S.X₃ (D.functor n)
  τ₂ := colimit.post S.X₁ (D.functor (n + 1))
  τ₃ := colimit.post S.X₂ (D.functor (n + 1))
  comm₁₂ := by
    dsimp only [topδ₂, ShortComplex.map_X₁, ShortComplex.map_f]
    refine colimit.hom_ext fun i => ?_
    have h := D.δ_naturality (hS i) hScol (S.mapNatTrans (colim.ι i)) n
    simp only [colimit.ι_post_assoc, colimit.ι_map_assoc, colimit.ι_post]
    exact h
  comm₂₃ := colimit.map_post (α := S.f) (D.functor (n + 1))

/-! ### The induction -/

variable [IsGrothendieckAbelian.{w} A] [HasExactColimitsOfShape I A]
  [HasExactColimitsOfShape I B]

/-- **The inductive engine of Stacks 01FF.** Let `D` be a cohomological δ-functor from a
Grothendieck abelian category `A` to an abelian category `B`, and let `I` be a shape for which
colimits in `A` and in `B` exist and are exact.  If the comparison morphism
`colimᵢ D⁰(Gᵢ) ⟶ D⁰(colimᵢ Gᵢ)` is an isomorphism for every diagram `G : I ⥤ A`, if `Dⁿ⁺¹`
kills injective objects, and if `Dⁿ⁺¹` kills the colimit of every diagram of injective objects,
then `colimᵢ Dⁿ(Gᵢ) ⟶ Dⁿ(colimᵢ Gᵢ)` is an isomorphism in every degree `n`.

The proof is the induction on the degree of Stacks 01FF.  At the inductive step, embed `G`
pointwise into a diagram `E` of injectives (`exists_mono_pointwise_injective`) and let
`0 → G → E → Q → 0` be the resulting short exact sequence of diagrams.  Its levelwise and its
colimit long exact sequences are compared by `DeltaFunctor.ladder₁` and
`DeltaFunctor.ladder₂`; the inductive hypothesis makes the comparison an isomorphism at `E` and
at `Q` in degree `n`, the hypotheses on injectives make the terms at `E` in degree `n + 1`
vanish on both rows, and the four lemma then forces the comparison at `G` in degree `n + 1` to
be an isomorphism. -/
theorem isIso_colimit_post_of_isIso_zero
    (h0 : ∀ G : I ⥤ A, IsIso (colimit.post G (D.functor 0)))
    (hinj : ∀ X : A, Injective X → ∀ n : ℕ, IsZero ((D.functor (n + 1)).obj X))
    (hvan : ∀ E : I ⥤ A, (∀ i, Injective (E.obj i)) → ∀ n : ℕ,
      IsZero ((D.functor (n + 1)).obj (colimit E)))
    (q : ℕ) (G : I ⥤ A) : IsIso (colimit.post G (D.functor q)) := by
  suffices h : ∀ (q : ℕ) (G : I ⥤ A), IsIso (colimit.post G (D.functor q)) from h q G
  clear G q
  intro q
  induction q with
  | zero => exact h0
  | succ n ih =>
    intro G
    obtain ⟨E, α, hmono, hEinj⟩ := exists_mono_pointwise_injective (I := I) (A := A) G
    have hα : Mono α := by
      have : ∀ i, Mono (α.app i) := hmono
      exact NatTrans.mono_of_mono_app α
    let S : ShortComplex (I ⥤ A) := ShortComplex.cokernelSequence α
    have hSE : S.ShortExact :=
      { exact := ShortComplex.cokernelSequence_exact α
        mono_f := hα
        epi_g := inferInstance }
    have hS : ∀ i, (S.map ((evaluation I A).obj i)).ShortExact := fun i => hSE.map_of_exact _
    have hScol : (S.map colim).ShortExact := hSE.map_of_exact _
    -- `Dⁿ⁺¹` kills the system of injectives, levelwise and after taking the colimit.
    have hzTop : IsZero (colimit (S.X₂ ⋙ D.functor (n + 1))) :=
      Functor.map_isZero colim
        (Functor.isZero_of_isZero_obj _ fun i => hinj (S.X₂.obj i) (hEinj i) n)
    have hzBot : IsZero ((D.functor (n + 1)).obj (colimit S.X₂)) := hvan S.X₂ hEinj n
    -- The top row is exact, because `I`-colimits in `B` are.
    have hex₂ : ((topδ₂ D S hS n).map colim).Exact :=
      (ShortComplex.exact_of_exact_evaluation _ fun i => D.scδ₂_exact (hS i) n).map colim
    have hEpiTop : Epi (colim.map (deltaNat D S hS n)) := by
      rw [ShortComplex.exact_iff_epi _ (hzTop.eq_of_tgt _ 0)] at hex₂
      exact hex₂
    have hEpiδ : Epi (D.δ hScol n) := D.epi_δ_of_map_f_eq_zero hScol n (hzBot.eq_of_tgt _ 0)
    have hI₂ := ih S.X₂
    have hI₃ := ih S.X₃
    have hEpi₁ : Epi (colimit.post S.X₂ (D.functor n)) := inferInstance
    have hMono₂ : Mono (colimit.post S.X₃ (D.functor n)) := inferInstance
    have hEpi₂ : Epi (colimit.post S.X₃ (D.functor n)) := inferInstance
    have hmono3 : Mono (colimit.post G (D.functor (n + 1))) :=
      ShortComplex.mono_of_epi_of_epi_of_mono (ladder₁ D S hS hScol n)
        (D.scδ₁_exact hScol n) hEpiTop hEpi₁ hMono₂
    have hsq : colimit.post S.X₃ (D.functor n) ≫ D.δ hScol n =
        colim.map (deltaNat D S hS n) ≫ colimit.post G (D.functor (n + 1)) :=
      (ladder₂ D S hS hScol n).comm₁₂
    have hepi3 : Epi (colimit.post G (D.functor (n + 1))) := by
      have hcomp : Epi (colim.map (deltaNat D S hS n) ≫ colimit.post G (D.functor (n + 1))) := by
        rw [← hsq]
        exact epi_comp' hEpi₂ hEpiδ
      exact epi_of_epi (colim.map (deltaNat D S hS n)) _
    exact isIso_of_mono_of_epi _

end DeltaFunctor

end CategoryTheory

end
