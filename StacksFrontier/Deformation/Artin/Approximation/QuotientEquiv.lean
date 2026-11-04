module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.RingTheory.Localization.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.SpecField
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.LimitPreservingOnObjects
public import StacksFrontier.CategoryTheory.Sites.Gerbe.Equivalence
public import StacksFrontier.RingTheory.AdicCompletion.PolynomialSurjection
public import StacksFrontier.RingTheory.Algebra.DirectLimit.FinitePresentation
public import StacksFrontier.RingTheory.ArtinRees.AssociatedGraded
public import StacksFrontier.RingTheory.ArtinRees.Constant
public import StacksFrontier.RingTheory.Etale.AssociatedGraded
public import StacksFrontier.RingTheory.Filtration.AssociatedGraded
public import StacksFrontier.RingTheory.GRing.Defs
public import StacksFrontier.RingTheory.GRing.EssFiniteType
public import StacksFrontier.RingTheory.Noetherian.ArtinRees
public import StacksFrontier.RingTheory.Smoothing.ApproximationGRing
import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# Approximation of an object over a complete local ring

This is the first of four parts of `StacksFrontier.Deformation.Artin.Approximation`: it
contains the site abbreviations and the quotient, truncation and graded-ring equivalences;
the later parts are `TruncationIso`, `Descent` and `FiniteType`.

An object of a category fibred in groupoids lying over a Noetherian complete local ring
can be approximated by one lying over a finite type algebra, preserving a specified
infinitesimal neighbourhood and the associated graded algebra of the maximal-ideal
filtration.

## Main definitions

* `Deformation.Artin.Approximation.baseFiberedCategory` and
  `Deformation.Artin.Approximation.structureMorphism` present the canonical projection to
  the site in the form used by limit preservation.

## Main results

* `Deformation.Artin.Approximation.exists_finiteType_approximation` gives the finite type
  approximation, its compatible object and its graded-algebra isomorphism: clauses (1)-(6)
  of Stacks 07XB.

## Implementation notes

The chosen big fppf site has a size cutoff, so membership witnesses for the spectra
of the complete ring and its truncation are explicit. Membership of the finite type
algebra and its truncation is included in the output. Limit preservation is taken for
index categories with objects and morphisms in the ring universe, so it applies to the
finite-presentation approximation diagram.

Clause (6), the isomorphism of graded `k`-algebras `Gr_{m_R}(R) ≅ Gr_{m_A}(A)`, is stated
as a ring isomorphism of the associated graded rings that preserves the homogeneous
summands and that agrees in degree zero with the truncation isomorphism of clause (4);
together these say that it is an isomorphism of graded algebras over the residue field.

The proof is split into independently elaborated steps rather than written as one block:
`exists_descent_of_limitPreserving` runs the direct system and the limit-preservation
descent, `exists_truncation_equiv_of_approximating_generators` produces the truncation
isomorphism from the approximating generators, `exists_artinRees_denominator_eq` fixes the
Artin-Rees precision the approximation must be asked for, and
`exists_gradedRingEquiv_of_approximation` assembles clause (6) over abstract data.

The proof of the tag invokes Artin approximation over a G-ring, Stacks 07QZ, whose own
proof goes through Popescu's theorem, Stacks 07GC. Both are proved in this library, so the
result is unconditional: `exists_etale_solution_approximating` repackages
`Stacks.Smoothing.exists_localEtaleSolution_of_isGRing` in the shape the proof consumes.

## References

* [Stacks Project, Tag 07XB](https://stacks.math.columbia.edu/tag/07XB)
* [Stacks Project, Tag 07QZ](https://stacks.math.columbia.edu/tag/07QZ)
* [Stacks Project, Tag 07GC](https://stacks.math.columbia.edu/tag/07GC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing AssociatedGraded

namespace Deformation.Artin.Approximation

universe u v w


theorem specMap_comp_three_eq_of_ringHom
    {A B C D E : Type u}
    [CommRing A] [CommRing B] [CommRing C] [CommRing D] [CommRing E]
    (f : C →+* D) (g : B →+* C) (h : A →+* B)
    (f' : E →+* D) (g' : A →+* E)
    (heq : f.comp (g.comp h) = f'.comp g') :
    Spec.map (CommRingCat.ofHom f) ≫
        Spec.map (CommRingCat.ofHom g) ≫
        Spec.map (CommRingCat.ofHom h) =
      Spec.map (CommRingCat.ofHom f') ≫
        Spec.map (CommRingCat.ofHom g') := by
  simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp, heq]

/-- The big fppf site of `S` inside the chosen site `B`, abbreviated. -/
public abbrev Site (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) := AlgebraicGeometry.BigFppfOver B S hS

/-- The category of schemes in the site, viewed as fibred in groupoids over itself. -/
public def baseFiberedCategory (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (Site B S hS) :=
  CatFiberedInGroupoids.mk (BasedCategory.ofFunctor (𝟭 (Site B S hS)))
    Functor.isFiberedInGroupoids_id

/-- The structure morphism of a fibred category, as a morphism to the identity
fibred category of the site. -/
public def structureMorphism (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (Site B S hS)) :
    𝒳 ⟶ baseFiberedCategory B S hS :=
  (CatFiberedInGroupoids.homEquivBasedFunctor 𝒳 (baseFiberedCategory B S hS)).symm
    { toFunctor := 𝒳.val.p
      w := by cat_disch }

/-- Every element lies in the zeroth step of the `I`-adic filtration, which is all of `M`.
Naming this keeps the membership side conditions of the degree-zero statements from being
discharged by `simp` inside a large local context. -/
theorem mem_power_zero {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (I : Ideal A) (m : M) : m ∈ power (M := M) I 0 := by
  simp

/-- The geometric square produced by a commuting square of ring maps over an affine chart
of the base: if `fA` and `fR` factor through the chart `k` by `αA` and `αR`, and the
truncation map `ψ` makes the ring square commute, then the corresponding square of
morphisms of schemes commutes. -/
theorem specMap_truncation_square {S : Scheme.{u}}
    {Lam A R QA QR : Type u} [CommRing Lam] [CommRing A] [CommRing R] [CommRing QA]
    [CommRing QR] (k : Spec (.of Lam) ⟶ S)
    (αA : Lam →+* A) (qA : A →+* QA) (αR : Lam →+* R) (qR : R →+* QR) (ψ : QA →+* QR)
    (fA : Spec (.of A) ⟶ S) (fR : Spec (.of R) ⟶ S)
    (hfA : Spec.map (CommRingCat.ofHom αA) ≫ k = fA)
    (hfR : Spec.map (CommRingCat.ofHom αR) ≫ k = fR)
    (heq : ψ.comp (qA.comp αA) = qR.comp αR) :
    Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom qA) ≫ fA =
      Spec.map (CommRingCat.ofHom qR) ≫ fR := by
  subst hfA
  subst hfR
  rw [← Category.assoc (Spec.map (CommRingCat.ofHom qA)),
    ← Category.assoc (Spec.map (CommRingCat.ofHom ψ)),
    ← Category.assoc (Spec.map (CommRingCat.ofHom qR)),
    specMap_comp_three_eq_of_ringHom ψ qA αA qR αR heq]

/-- If two finite lists of relations agree modulo an ideal, then after adjoining that
ideal they generate the same ideal. This is the ring-theoretic bridge used to identify
the finite infinitesimal neighborhoods in the approximation construction. -/
private theorem span_range_sup_eq_of_sub_mem
    {A : Type u} [CommRing A] {r : ℕ} (I : Ideal A)
    (b b' : Fin r → A)
    (h : ∀ i, b i - b' i ∈ I) :
    Ideal.span (Set.range b) ⊔ I = Ideal.span (Set.range b') ⊔ I := by
  have key : ∀ b b' : Fin r → A, (∀ i, b i - b' i ∈ I) →
      Ideal.span (Set.range b) ⊔ I ≤ Ideal.span (Set.range b') ⊔ I := by
    intro b b' h
    refine sup_le ?_ le_sup_right
    rw [Ideal.span_le]
    rintro x ⟨i, rfl⟩
    have hbi : b i = (b i - b' i) + b' i := by ring
    rw [hbi]
    exact add_mem (Ideal.mem_sup_right (h i))
      (Ideal.mem_sup_left (Ideal.subset_span ⟨i, rfl⟩))
  exact le_antisymm (key b b' h)
    (key b' b fun i => by simpa only [neg_sub] using I.neg_mem (h i))

/-- The quotient rings by two relation ideals have canonically isomorphic truncations
when their displayed generators agree modulo the truncating ideal. -/
private noncomputable def quotientEquivOfRelationsCongruent
    {A : Type u} [CommRing A] {r : ℕ} (I : Ideal A)
    (b b' : Fin r → A) (h : ∀ i, b i - b' i ∈ I) :
    (A ⧸ (Ideal.span (Set.range b) ⊔ I)) ≃+*
    (A ⧸ (Ideal.span (Set.range b') ⊔ I)) :=
  Ideal.quotEquivOfEq (span_range_sup_eq_of_sub_mem I b b' h)

/-- This quotient equivalence sends a class to the class of the same representative. -/
private theorem quotientEquivOfRelationsCongruent_mk
    {A : Type u} [CommRing A] {r : ℕ} (I : Ideal A)
    (b b' : Fin r → A) (h : ∀ i, b i - b' i ∈ I) (x : A) :
    quotientEquivOfRelationsCongruent I b b' h
      (Ideal.Quotient.mk (Ideal.span (Set.range b) ⊔ I) x) =
        Ideal.Quotient.mk (Ideal.span (Set.range b') ⊔ I) x :=
  Ideal.quotEquivOfEq_mk _ x

/-- The relation equivalence commutes with the quotient maps from the ambient ring.
This is the ring-hom form of the representative calculation above and is convenient
when turning the comparison into a morphism of affine schemes. -/
private theorem quotientEquivOfRelationsCongruent_comp_mk
    {A : Type u} [CommRing A] {r : ℕ} (I : Ideal A)
    (b b' : Fin r → A) (h : ∀ i, b i - b' i ∈ I) :
    (quotientEquivOfRelationsCongruent I b b' h).toRingHom.comp
        (Ideal.Quotient.mk (Ideal.span (Set.range b) ⊔ I)) =
      Ideal.Quotient.mk (Ideal.span (Set.range b') ⊔ I) := by
  ext x
  exact quotientEquivOfRelationsCongruent_mk I b b' h x

/-- The inverse comparison also keeps the same representatives. -/
private theorem quotientEquivOfRelationsCongruent_symm_mk
    {A : Type u} [CommRing A] {r : ℕ} (I : Ideal A)
    (b b' : Fin r → A) (h : ∀ i, b i - b' i ∈ I) (x : A) :
    (quotientEquivOfRelationsCongruent I b b' h).symm
      (Ideal.Quotient.mk (Ideal.span (Set.range b') ⊔ I) x) =
        Ideal.Quotient.mk (Ideal.span (Set.range b) ⊔ I) x := by
  apply (quotientEquivOfRelationsCongruent I b b' h).injective
  rw [RingEquiv.apply_symm_apply]
  exact quotientEquivOfRelationsCongruent_mk I b b' h x

/-- The inverse relation comparison also commutes with the quotient maps. This is
the ring-hom equality underlying the reverse affine-scheme comparison. -/
private theorem quotientEquivOfRelationsCongruent_symm_comp_mk
    {A : Type u} [CommRing A] {r : ℕ} (I : Ideal A)
    (b b' : Fin r → A) (h : ∀ i, b i - b' i ∈ I) :
    ((quotientEquivOfRelationsCongruent I b b' h).symm).toRingHom.comp
        (Ideal.Quotient.mk (Ideal.span (Set.range b') ⊔ I)) =
      Ideal.Quotient.mk (Ideal.span (Set.range b) ⊔ I) := by
  ext x
  exact quotientEquivOfRelationsCongruent_symm_mk I b b' h x

/-- On affine spectra, the inverse relation comparison followed by the quotient
closed immersion is the original quotient closed immersion. -/
private theorem quotientEquivOfRelationsCongruent_specMap_comp
    {A : Type u} [CommRing A] {r : ℕ} (I : Ideal A)
    (b b' : Fin r → A) (h : ∀ i, b i - b' i ∈ I) :
    Spec.map (CommRingCat.ofHom
        (quotientEquivOfRelationsCongruent I b b' h).symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range b') ⊔ I))) =
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range b) ⊔ I))) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1

/-- On affine spectra, the relation comparison followed by the other quotient
closed immersion is the original quotient closed immersion. This is the forward
comparison corresponding to `quotientEquivOfRelationsCongruent_specMap_comp`. -/
private theorem quotientEquivOfRelationsCongruent_specMap_comp_symm
    {A : Type u} [CommRing A] {r : ℕ} (I : Ideal A)
    (b b' : Fin r → A) (h : ∀ i, b i - b' i ∈ I) :
    Spec.map (CommRingCat.ofHom
        (quotientEquivOfRelationsCongruent I b b' h).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range b) ⊔ I))) =
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range b') ⊔ I))) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1

/-- A vector in a finite product whose coordinates lie in an ideal belongs to
the ideal filtration of that product. -/
private theorem mem_ideal_smul_top_pi
    {A : Type u} [CommRing A] {ι : Type v} [Fintype ι]
    (I : Ideal A) (x : ι → A) (hx : ∀ i, x i ∈ I) :
    x ∈ I • (⊤ : Submodule A (ι → A)) := by
  classical
  rw [← Finset.univ_sum_single x]
  apply Submodule.sum_mem
  intro i hi
  have hs : Pi.single i (x i) = (x i) • Pi.single i (1 : A) := by
    ext j
    by_cases hij : i = j <;> simp [hij]
  rw [hs]
  exact Submodule.smul_mem_smul (hx i) (Submodule.mem_top)

/-- An étale algebra with the same residue field has the same finite local
neighborhoods as its base. -/
private noncomputable def etaleTruncEquiv
    {T D : Type u} [CommRing T] [IsLocalRing T] [CommRing D]
    [Algebra T D] [Algebra.Etale T D]
    (mD : Ideal D) [mD.IsMaximal]
    (hcomp : Ideal.comap (algebraMap T D) mD = maximalIdeal T)
    (hres : Function.Bijective
      (Ideal.ResidueField.map (maximalIdeal T) mD (algebraMap T D) hcomp.symm))
    (n : ℕ) (hn : 1 ≤ n) :
    (T ⧸ (maximalIdeal T) ^ n) ≃+* (D ⧸ mD ^ n) := by
  let f : T →+* D := algebraMap T D
  have hsurj : Function.Surjective ((Ideal.Quotient.mk mD).comp f) := by
    intro y
    obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨z, hz⟩ := hres.2 (algebraMap D mD.ResidueField d)
    obtain ⟨t, rfl⟩ :=
      (maximalIdeal T).algebraMap_residueField_surjective z
    refine ⟨t, ?_⟩
    change Ideal.Quotient.mk mD (f t) = Ideal.Quotient.mk mD d
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem (f t) d).2
    have hmem : d - f t ∈ mD := by
      apply Ideal.algebraMap_residueField_eq_zero.mp
      have heq : algebraMap D mD.ResidueField (f t) =
          algebraMap D mD.ResidueField d := by
        rw [← Ideal.ResidueField.map_algebraMap
          (maximalIdeal T) mD f hcomp.symm t]
        exact hz
      simpa only [map_sub, sub_eq_zero] using heq.symm
    simpa only [neg_sub] using mD.neg_mem hmem
  have hI : FormallyEtaleH1D.Iideal f mD = maximalIdeal T := by
    ext t
    simp only [FormallyEtaleH1D.Iideal, RingHom.mem_ker,
      RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_comap, ← hcomp]
    rfl
  have hform : RingHom.FormallyEtale f :=
    RingHom.formallyEtale_algebraMap.mpr Algebra.Etale.formallyEtale
  let e : (T ⧸ FormallyEtaleH1D.Iideal f mD ^ n) ≃+*
      (D ⧸ mD ^ n) :=
    RingEquiv.ofBijective (FormallyEtaleH1D.quotMap f mD n)
      (FormallyEtaleH1D.quotMap_bijective f mD hform hsurj n hn)
  exact (Ideal.quotEquivOfEq (by rw [hI])).trans e

private theorem etaleTruncEquiv_mk
    {T D : Type u} [CommRing T] [IsLocalRing T] [CommRing D]
    [Algebra T D] [Algebra.Etale T D]
    (mD : Ideal D) [mD.IsMaximal]
    (hcomp : Ideal.comap (algebraMap T D) mD = maximalIdeal T)
    (hres : Function.Bijective
      (Ideal.ResidueField.map (maximalIdeal T) mD (algebraMap T D) hcomp.symm))
    (n : ℕ) (hn : 1 ≤ n) (t : T) :
    etaleTruncEquiv mD hcomp hres n hn
        (Ideal.Quotient.mk ((maximalIdeal T) ^ n) t) =
      Ideal.Quotient.mk (mD ^ n) (algebraMap T D t) := by
  simp only [etaleTruncEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  change FormallyEtaleH1D.quotMap (algebraMap T D) mD n
      (Ideal.Quotient.mk _ t) = _
  rw [FormallyEtaleH1D.quotMap, Ideal.quotientMap_mk]

private theorem completion_eval_ker
    (T : Type u) [CommRing T] [IsLocalRing T] [IsNoetherianRing T]
    (n : ℕ) :
    RingHom.ker (AdicCompletion.evalₐ (maximalIdeal T) n).toRingHom =
      maximalIdeal (AdicCompletion (maximalIdeal T) T) ^ n := by
  rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow]
  ext x
  rw [RingHom.mem_ker]
  change AdicCompletion.evalₐ (maximalIdeal T) n x = 0 ↔ _
  rw [← Submodule.restrictScalars_mem T, ← Ideal.smul_top_eq_map,
    AdicCompletion.pow_smul_top_eq_ker_eval
      (maximalIdeal T).fg_of_isNoetherianRing]
  have heq : maximalIdeal T ^ n * ⊤ = maximalIdeal T ^ n := by simp
  have hinj : Function.Injective (Ideal.Quotient.factor (le_of_eq heq)) := by
    simpa [RingHom.injective_iff_ker_eq_bot, Ideal.Quotient.factor_ker] using
      Ideal.map_mk_eq_bot_of_le (le_of_eq heq.symm)
  simpa [← AdicCompletion.factor_eval_eq_evalₐ] using map_eq_zero_iff _ hinj

/-- The completion has the same quotient by each power of the maximal ideal. -/
private noncomputable def completionTruncEquiv
    (T : Type u) [CommRing T] [IsLocalRing T] [IsNoetherianRing T]
    (n : ℕ) :
    (AdicCompletion (maximalIdeal T) T ⧸
        maximalIdeal (AdicCompletion (maximalIdeal T) T) ^ n) ≃+*
      (T ⧸ maximalIdeal T ^ n) :=
  (Ideal.quotEquivOfEq (completion_eval_ker T n).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (AdicCompletion.surjective_evalₐ _ n))

private theorem completionTruncEquiv_mk
    (T : Type u) [CommRing T] [IsLocalRing T] [IsNoetherianRing T]
    (n : ℕ) (t : T) :
    completionTruncEquiv T n
        (Ideal.Quotient.mk _ (algebraMap T (AdicCompletion (maximalIdeal T) T) t)) =
      Ideal.Quotient.mk _ t := by
  change completionTruncEquiv T n
      (Ideal.Quotient.mk _ (AdicCompletion.of (maximalIdeal T) T t)) = _
  simp only [completionTruncEquiv, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]
  change AdicCompletion.evalₐ _ n (AdicCompletion.of _ T t) = _
  exact AdicCompletion.evalₐ_of _ n t

/-- Quotienting by two ideals in succession agrees with quotienting by their
sum. The formula is useful for transporting a relation ideal across a finite
neighborhood equivalence. -/
private noncomputable def quotientSupEquiv
    {A : Type u} [CommRing A] (I J : Ideal A) :
    (A ⧸ (I ⊔ J)) ≃+*
      ((A ⧸ J) ⧸ Ideal.map (Ideal.Quotient.mk J) I) := by
  let f : A →+* ((A ⧸ J) ⧸ Ideal.map (Ideal.Quotient.mk J) I) :=
    (Ideal.Quotient.mk (Ideal.map (Ideal.Quotient.mk J) I)).comp
      (Ideal.Quotient.mk J)
  have hf : Function.Surjective f :=
    Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective
  have hker : RingHom.ker f = I ⊔ J := by
    calc
      RingHom.ker f = Ideal.comap (Ideal.Quotient.mk J)
          (Ideal.map (Ideal.Quotient.mk J) I) := by
            change Ideal.comap (Ideal.Quotient.mk J)
              (RingHom.ker (Ideal.Quotient.mk
                (Ideal.map (Ideal.Quotient.mk J) I))) = _
            rw [Ideal.mk_ker]
      _ = J ⊔ I := by
        rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
          ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
        exact sup_comm I J
      _ = I ⊔ J := sup_comm J I
  exact (Ideal.quotEquivOfEq hker.symm).trans
    (f.quotientKerEquivOfSurjective hf)

private theorem quotientSupEquiv_mk
    {A : Type u} [CommRing A] (I J : Ideal A) (x : A) :
    quotientSupEquiv I J (Ideal.Quotient.mk (I ⊔ J) x) =
      Ideal.Quotient.mk (Ideal.map (Ideal.Quotient.mk J) I)
        (Ideal.Quotient.mk J x) := by
  simp only [quotientSupEquiv, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]
  rfl

/-- The Artin-Rees bound makes nearby images agree modulo the next filtration step. -/
private theorem range_inf_power_le
    {A : Type u} [CommRing A] (I : Ideal A) {M : Type v} {N : Type w}
    [AddCommGroup M] [AddCommGroup N] [Module A M] [Module A N]
    (g g' : M →ₗ[A] N) (c n : ℕ) (hg : IsArtinReesConstant I g c)
    (hgg' : CongruentModPow I g g' (c + 1)) :
    LinearMap.range g ⊓ power (M := N) I n ≤
      power (M := N) I (n + 1) ⊔ LinearMap.range g' := by
  intro b hb
  obtain ⟨⟨a, rfl⟩, hpow⟩ := hb
  have hdiff : ∀ (s : ℕ) (a : M), a ∈ power (M := M) I s →
      (g - g') a ∈ power (M := N) I (s + c + 1) := by
    intro s a ha
    unfold CongruentModPow at hgg'
    refine Submodule.smul_induction_on ha ?_ ?_
    · intro r hr m _
      rw [map_smul]
      have h := Submodule.smul_mem_smul hr (hgg' ⟨m, rfl⟩)
      simpa [power, smul_smul, ← pow_add, add_assoc] using h
    · intro y z hy hz
      simpa only [map_add] using Submodule.add_mem _ hy hz
  by_cases hn : n ≤ c
  · have hd : (g - g') a ∈ power (M := N) I (c + 1) := by
      unfold CongruentModPow at hgg'
      exact hgg' ⟨a, rfl⟩
    have hd' : (g - g') a ∈ power (M := N) I (n + 1) :=
      Submodule.smul_mono (Ideal.pow_le_pow_right (by omega)) le_rfl hd
    apply Submodule.mem_sup.mpr
    refine ⟨(g - g') a, hd', g' a, ⟨a, rfl⟩, ?_⟩
    simp
  · have hnc : c ≤ n := by omega
    obtain ⟨a', ha', hga'⟩ := hg.mem_map hnc hpow
    apply Submodule.mem_sup.mpr
    refine ⟨(g - g') a', ?_, g' a', ⟨a', rfl⟩, ?_⟩
    · have hd := hdiff (n - c) a' ha'
      simpa [Nat.sub_add_cancel hnc, add_assoc] using hd
    · simp only [LinearMap.sub_apply]
      rw [hga']
      abel

/-- Nearby maps with a common Artin-Rees bound have equal graded-piece denominators. -/
private theorem presentation_denominator_eq
    {A : Type u} [CommRing A] (I : Ideal A) {M : Type v} {N : Type w}
    [AddCommGroup M] [AddCommGroup N] [Module A M] [Module A N]
    (g g' : M →ₗ[A] N) (c n : ℕ)
    (hg : IsArtinReesConstant I g c) (hg' : IsArtinReesConstant I g' c)
    (hgg' : CongruentModPow I g g' (c + 1)) :
    (power (M := N) I (n + 1) ⊔ LinearMap.range g).comap (power I n).subtype =
      (power (M := N) I (n + 1) ⊔ LinearMap.range g').comap (power I n).subtype := by
  have key : ∀ g g' : M →ₗ[A] N, IsArtinReesConstant I g c → CongruentModPow I g g' (c + 1) →
      (power (M := N) I (n + 1) ⊔ LinearMap.range g).comap (power I n).subtype ≤
        (power (M := N) I (n + 1) ⊔ LinearMap.range g').comap (power I n).subtype := by
    intro g g' hg hgg' z hz
    change (z : N) ∈ power (M := N) I (n + 1) ⊔ LinearMap.range g at hz
    obtain ⟨p, hp, r, hr, eq⟩ := Submodule.mem_sup.mp hz
    change p + r = (z : N) at eq
    have hrn : r ∈ LinearMap.range g ⊓ power (M := N) I n := by
      refine ⟨hr, ?_⟩
      have h := Submodule.sub_mem (power (M := N) I n) z.property
        (power_succ_le I n hp)
      have hre : r = (z : N) - p := by rw [← eq]; abel
      rwa [hre]
    have := range_inf_power_le I g g' c n hg hgg' hrn
    change (z : N) ∈ power (M := N) I (n + 1) ⊔ LinearMap.range g'
    rw [← eq]
    exact Submodule.add_mem _ (Submodule.mem_sup_left hp) this
  exact le_antisymm (key g g' hg hgg') (key g' g hg' hgg'.symm)

/-- The image of an element of the `n`-th power lies in the `n`-th power of the image ideal. -/
private theorem mk_mem_power_map
    {A : Type*} [CommRing A] (I K : Ideal A) (n : ℕ) (z : power (M := A) I n) :
    Ideal.Quotient.mk K (z : A) ∈ power (M := A ⧸ K) (Ideal.map (Ideal.Quotient.mk K) I) n := by
  rw [ring_power_eq, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ (by simpa [ring_power_eq] using z.property)

private def ringPieceRep
    {A : Type*} [CommRing A] (I K : Ideal A) (n : ℕ)
    (z : power (M := A) I n) :
    piece (M := A ⧸ K) (Ideal.map (Ideal.Quotient.mk K) I) n :=
  mk (Ideal.map (Ideal.Quotient.mk K) I) n ⟨Ideal.Quotient.mk K z, mk_mem_power_map I K n z⟩

private noncomputable def ringPiecePresentation
    {A : Type*} [CommRing A] (I K : Ideal A) (n : ℕ) :
    ((power (M := A) I n) ⧸
        (power (M := A) I (n + 1) ⊔ (K : Submodule A A)).comap
          (power I n).subtype) ≃ₗ[A]
      piece (M := A ⧸ K) (Ideal.map (Ideal.Quotient.mk K) I) n := by
  let P := power (M := A) I n
  let Q := A ⧸ K
  let J : Ideal Q := Ideal.map (Ideal.Quotient.mk K) I
  let V := power (M := Q) J n
  have hpow (j : ℕ) : power (M := Q) J j =
      (Ideal.map (Ideal.Quotient.mk K) (I ^ j) : Submodule Q Q) := by
    rw [ring_power_eq, ← Ideal.map_pow]
  let φ : P →ₗ[A] V := {
    toFun := fun z => ⟨Ideal.Quotient.mk K z, mk_mem_power_map I K n z⟩
    map_add' := fun x y => Subtype.ext (by simp)
    map_smul' := fun a x => Subtype.ext (by
      simp only [SetLike.val_smul, smul_eq_mul, map_mul]
      rfl) }
  let F : P →ₗ[A] piece (M := Q) J n :=
    (((power (M := Q) J (n + 1)).comap V.subtype).mkQ.restrictScalars A).comp φ
  have hsurjφ : Function.Surjective φ := by
    intro q
    have hq : (q : Q) ∈ Ideal.map (Ideal.Quotient.mk K) (I ^ n) := by
      rw [← hpow n]
      exact q.property
    obtain ⟨z, hz, eq⟩ :=
      (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk K)
        Ideal.Quotient.mk_surjective).mp hq
    refine ⟨⟨z, by simpa [P, ring_power_eq] using hz⟩, Subtype.ext ?_⟩
    simpa [φ] using eq
  have hsurjF : Function.Surjective F := by
    intro q
    induction q using Quotient.inductionOn with
    | _ q =>
      obtain ⟨z, rfl⟩ := hsurjφ q
      exact ⟨z, rfl⟩
  have hker : LinearMap.ker F =
      (power (M := A) I (n + 1) ⊔ (K : Submodule A A)).comap P.subtype := by
    ext z
    simp only [LinearMap.mem_ker, Submodule.mem_comap]
    change ((power (M := Q) J (n + 1)).comap V.subtype).mkQ (φ z) = 0 ↔
      (z : A) ∈ power (M := A) I (n + 1) ⊔ (K : Submodule A A)
    simp only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_comap]
    change (Ideal.Quotient.mk K (z : A) ∈ power (M := Q) J (n + 1)) ↔
      (z : A) ∈ power (M := A) I (n + 1) ⊔ (K : Submodule A A)
    rw [hpow (n + 1), ring_power_eq]
    change (z : A) ∈ Ideal.comap (Ideal.Quotient.mk K)
        (Ideal.map (Ideal.Quotient.mk K) (I ^ (n + 1))) ↔
      (z : A) ∈ (I ^ (n + 1) : Ideal A) ⊔ K
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_comm]
  exact (Submodule.quotEquivOfEq _ _ hker.symm).trans
    (F.quotKerEquivOfSurjective hsurjF)

private theorem ringPiecePresentation_mk
    {A : Type*} [CommRing A] (I K : Ideal A) (n : ℕ)
    (z : power (M := A) I n) :
    ringPiecePresentation I K n (Submodule.Quotient.mk z) =
      ringPieceRep I K n z := by
  simp [ringPiecePresentation]
  congr 1

private noncomputable def ringPieceEquiv
    {A : Type*} [CommRing A] (I J K : Ideal A) (n : ℕ)
    (h : (power (M := A) I (n + 1) ⊔ (J : Submodule A A)).comap
        (power I n).subtype =
      (power (M := A) I (n + 1) ⊔ (K : Submodule A A)).comap
        (power I n).subtype) :
    piece (M := A ⧸ J) (Ideal.map (Ideal.Quotient.mk J) I) n ≃ₗ[A]
      piece (M := A ⧸ K) (Ideal.map (Ideal.Quotient.mk K) I) n :=
  (ringPiecePresentation I J n).symm |>.trans <|
    (Submodule.quotEquivOfEq _ _ h).trans (ringPiecePresentation I K n)

private theorem ringPieceEquiv_mk
    {A : Type*} [CommRing A] (I J K : Ideal A) (n : ℕ)
    (h : (power (M := A) I (n + 1) ⊔ (J : Submodule A A)).comap
        (power I n).subtype =
      (power (M := A) I (n + 1) ⊔ (K : Submodule A A)).comap
        (power I n).subtype)
    (z : power (M := A) I n) :
    ringPieceEquiv I J K n h (ringPieceRep I J n z) = ringPieceRep I K n z := by
  have hJ := ringPiecePresentation_mk I J n z
  have hK := ringPiecePresentation_mk I K n z
  have hinv : (ringPiecePresentation I J n).symm (ringPieceRep I J n z) =
      Submodule.Quotient.mk z :=
    (ringPiecePresentation I J n).symm_apply_eq.mpr hJ
  simp only [ringPieceEquiv, LinearEquiv.trans_apply]
  rw [hinv, Submodule.quotEquivOfEq_mk]
  exact hK

private theorem ringPiece_exists_rep
    {A : Type*} [CommRing A] (I K : Ideal A) (n : ℕ)
    (x : piece (M := A ⧸ K) (Ideal.map (Ideal.Quotient.mk K) I) n) :
    ∃ z : power (M := A) I n,
      x = ringPieceRep I K n z := by
  obtain ⟨y, rfl⟩ := (ringPiecePresentation I K n).surjective x
  induction y using Quotient.inductionOn with
  | _ z =>
    exact ⟨z, (ringPiecePresentation_mk I K n z).symm⟩

private theorem ringPieceRep_mul
    {A : Type*} [CommRing A] (I K : Ideal A) (i j : ℕ)
    (z : power (M := A) I i) (w : power (M := A) I j) :
    let zw : power (M := A) I (i + j) :=
      ⟨(z : A) * (w : A), by
        simpa only [smul_eq_mul] using smul_mem_power I z.property w.property⟩
    DirectSum.of _ i (ringPieceRep I K i z) *
        DirectSum.of _ j (ringPieceRep I K j w) =
      DirectSum.of _ (i + j) (ringPieceRep I K (i + j) zw) := by
  intro zw
  rw [of_mul_of]
  congr 1

private noncomputable def ringGradedEquivOfDenomEq
    {A : Type*} [CommRing A] (I J K : Ideal A)
    (hden : ∀ n,
      (power (M := A) I (n + 1) ⊔ (J : Submodule A A)).comap
        (power I n).subtype =
      (power (M := A) I (n + 1) ⊔ (K : Submodule A A)).comap
        (power I n).subtype) :
    gradedRing (Ideal.map (Ideal.Quotient.mk J) I) ≃+*
      gradedRing (Ideal.map (Ideal.Quotient.mk K) I) := by
  let IJ : Ideal (A ⧸ J) := Ideal.map (Ideal.Quotient.mk J) I
  let IK : Ideal (A ⧸ K) := Ideal.map (Ideal.Quotient.mk K) I
  let ePiece (n : ℕ) : piece (M := A ⧸ J) IJ n ≃ₗ[A]
      piece (M := A ⧸ K) IK n := ringPieceEquiv I J K n (hden n)
  let eAdd : gradedRing IJ ≃+ gradedRing IK :=
    DirectSum.congrAddEquiv (fun n => (ePiece n).toAddEquiv)
  have heAddRep (n : ℕ) (z : power (M := A) I n) :
      eAdd (DirectSum.of _ n (ringPieceRep I J n z)) =
        DirectSum.of _ n (ringPieceRep I K n z) := by
    change (DirectSum.map fun n => (ePiece n).toAddMonoidHom)
      (DirectSum.of _ n (ringPieceRep I J n z)) = _
    rw [DirectSum.map_of]
    congr 1
    exact ringPieceEquiv_mk I J K n (hden n) z
  let f : gradedRing IJ →+* gradedRing IK :=
    { toFun := eAdd
      map_zero' := eAdd.map_zero
      map_add' := eAdd.map_add
      map_one' := by
        let z : power (M := A) I 0 := ⟨1, mem_power_zero _ _⟩
        change eAdd (DirectSum.of _ 0 (ringPieceRep I J 0 z)) =
          DirectSum.of _ 0 (ringPieceRep I K 0 z)
        exact heAddRep 0 z
      map_mul' := by
        intro x y
        induction x using DirectSum.induction_on with
        | zero => simp
        | add x x' hx hx' =>
          simpa only [add_mul, map_add] using congrArg₂ (· + ·) hx hx'
        | of i a =>
          induction y using DirectSum.induction_on with
          | zero => simp
          | add y y' hy hy' =>
            simpa only [mul_add, map_add] using congrArg₂ (· + ·) hy hy'
          | of j b =>
            obtain ⟨z, rfl⟩ := ringPiece_exists_rep I J i a
            obtain ⟨w, rfl⟩ := ringPiece_exists_rep I J j b
            change eAdd (DirectSum.of _ i (ringPieceRep I J i z) *
                DirectSum.of _ j (ringPieceRep I J j w)) =
              eAdd (DirectSum.of _ i (ringPieceRep I J i z)) *
                eAdd (DirectSum.of _ j (ringPieceRep I J j w))
            rw [ringPieceRep_mul I J i j z w, heAddRep,
              heAddRep, heAddRep, ringPieceRep_mul I K i j z w] }
  exact RingEquiv.ofBijective f (by change Function.Bijective eAdd; exact eAdd.bijective)

end Deformation.Artin.Approximation
