module

public import StacksFrontier.Homology.PseudoCoherent.Relative.Composition
public import StacksFrontier.Homology.RelativelyPerfect.FlatComplex
public import StacksFrontier.RingTheory.Dualizing.RelativeComposition
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.DerivedTensor
import all StacksFrontier.Homology.RelativelyPerfect.Tensor
import all StacksFrontier.RingTheory.Dualizing.UpperShriek.DerivedTensor
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Transitivity of relative perfection

Let `R → A → B` be flat ring maps of finite presentation.  If `KA` is perfect relative to `R` in
`D(A)` ([stacks 0DHS]) and `KB` is perfect relative to `A` in `D(B)`, then `KA ⊗ᴸ_A KB` is
perfect relative to `R` in `D(B)`.  That is
`Dualizing.isRelativelyPerfect_derivedTensorProductOver`, and it is clause (1) of [stacks 0E2C]
for the composite — the first antecedent of [stacks 0E2H] as that tag is organised in
`StacksFrontier.RingTheory.Dualizing.RelativeCompositionTag`.

The statement does not occur in the source: §15.85 has only [stacks 0DHU] (perfect tensor
relatively perfect, over a *fixed* base) and [stacks 0DHW] (base change of the base ring), and
the source's proof of [stacks 0E2H] never needs transitivity because it reads clause (1) off an
identification with `(ψ ∘ φ)^!(R)`, which this library cannot assemble.  So it is proved here
directly.

## The argument

[stacks 0DHV], `PseudoCoherence.isRelativelyPerfect_iff_exists_bounded_flat_finitePresentation`,
is an equivalence, so both hypotheses and the conclusion are statements about *bounded* complexes
with prescribed termwise properties.  Choose by it a bounded complex `P` of `A`-modules, flat over
`R` and finitely presented over `A`, representing `KA`, and a bounded complex `N` of `B`-modules,
flat over `A` and finitely presented over `B`, representing `KB`.  Three things then have to be
checked of the total tensor complex of `P` and `N`.

* **It computes the derived tensor product.**  `Dualizing.derivedTensorProductOver (algebraMap A B)
  KB` is a total left derived functor whose counit is invertible on the complexes that are K-flat
  over `A`, and `P` is *not* one of those: its terms are flat over `R`, not over `A`.  What saves
  the computation is the fixed factor: `N` is bounded with `A`-flat terms, so its restriction of
  scalars to `A` is K-flat over `A` by [stacks 064K], and therefore the direct tensor-total
  functor already inverts quasi-isomorphisms — its underlying complex of `A`-modules is a total
  tensor product with that K-flat complex, and restriction of scalars reflects
  quasi-isomorphisms.  A left derived functor of a functor inverting the weak equivalences has
  invertible counit, so the counit is invertible at *every* complex.  This is
  `Dualizing.isIso_alphaF_of_kFlat_restrictScalars`.
* **It is bounded.**  Read off the underlying complex of `A`-modules again: that is the total
  tensor product of two bounded complexes, which `PseudoCoherence.tensorLeftLarge_isStrictlyLE`
  and `PseudoCoherence.tensorLeftLarge_isStrictlyGE` bound, and restriction of scalars neither
  creates nor destroys a zero module.
* **Its terms are flat over `R` and finitely presented over `B`.**  Flatness is again a statement
  about the underlying complex of `A`-modules, so it is
  `PseudoCoherence.tensorLeftLarge_flat_restrictScalars`, whose termwise content is
  `Dualizing.flat_tensorProduct`.  Finite presentation is a statement over `B`, so it is read off
  the change-of-rings comparison `(P ⊗_A N)^i = ⨁ (B ⊗_A P^p) ⊗_B N^q`; each summand is
  `N^q ⊗_A P^p` by cancellation of the base change, finitely presented over `B` by
  `Dualizing.finitePresentation_tensorProduct`, and the coproduct runs over the antidiagonal with
  all but finitely many summands zero, which `finitePresentation_coproduct_of_isZero` reduces to
  a finite direct sum.

## Main results

* `Dualizing.isIso_alphaF_of_kFlat_restrictScalars` — the chain-level comparison: a derived
  tensor product along a ring map is computed by the ordinary one whenever the fixed factor is
  K-flat over the source ring.
* `Dualizing.isRelativelyPerfect_of_iso` — relative perfection depends only on the isomorphism
  class of the object.
* `Dualizing.isRelativelyPerfect_derivedTensorProductOver` — **transitivity of relative
  perfection.**

## References

* [Stacks Project, Tag 0DHS](https://stacks.math.columbia.edu/tag/0DHS)
* [Stacks Project, Tag 0DHV](https://stacks.math.columbia.edu/tag/0DHV)
* [Stacks Project, Tag 064K](https://stacks.math.columbia.edu/tag/064K)
* [Stacks Project, Tag 0E2C](https://stacks.math.columbia.edu/tag/0E2C)
* [Stacks Project, Tag 0E2H](https://stacks.math.columbia.edu/tag/0E2H)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct
open CochainComplex CochainComplex.DerivedTensor

-- `StacksFrontier.RingTheory.Dualizing.UpperShriek.DerivedTensor` now reaches
-- `StacksFrontier.Homology.DerivedCategory.LocallySmall`, whose global `HasDerivedCategory`
-- instances have the ambient morphism universe rather than its successor; the priority keeps
-- the standard model, which is the one every statement here is about.
attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Dualizing

noncomputable section

/-! ### The chain-level comparison -/

/-- If the fixed right-hand factor is K-flat after restriction of scalars, then the direct
tensor-total functor already inverts quasi-isomorphisms, so the counit of its left derived
functor is invertible at *every* complex, not only at the K-flat ones. -/
theorem isIso_alphaF_of_kFlat_restrictScalars {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (N : CochainComplex (ModuleCat.{u} B) ℤ)
    (T : DerivedTensorChangeOfRings.{u, u, u} f N)
    (hN : CochainComplex.KFlat.{u, u} ((restrictScalarsLarge.{u, u, u} f).obj N)) :
    IsIso T.alphaF := by
  refine Functor.isIso_of_isLeftDerivedFunctor_of_inverts T.F T.alphaF
    (W := HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)) ?_
  intro X Y g hg
  have hgq : QuasiIso g := hg
  show IsIso (DerivedCategory.Q.map (T.directTensor.map g))
  rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
  rw [← quasiIso_restrictScalarsLarge_map_iff.{u, u, u} f (T.directTensor.map g)]
  have hsq := T.directTensorUnderlying.hom.naturality g
  have hr : QuasiIso ((tensorRightLarge.{u, u} ((restrictScalarsLarge.{u, u, u} f).obj N)).map g) :=
    CochainComplex.DerivedTensor.quasiIso_tright_map.{u, u} _ hN g
  have h1 : QuasiIso ((restrictScalarsLarge.{u, u, u} f).map (T.directTensor.map g) ≫
      T.directTensorUnderlying.hom.app Y) := by
    rw [show (restrictScalarsLarge.{u, u, u} f).map (T.directTensor.map g) =
        (T.directTensor ⋙ restrictScalarsLarge.{u, u, u} f).map g from rfl, hsq]
    exact quasiIso_comp (hφ := quasiIso_of_isIso _) (hφ' := hr) _ _
  exact (quasiIso_iff_comp_right (hφ' := quasiIso_of_isIso (T.directTensorUnderlying.hom.app Y))
    _ _).1 h1

/-! ### Finite presentation of a term of a total tensor complex -/

section Coproduct

variable {B : Type u} [CommRing B] {ι : Type}

/-- A coproduct of modules all but finitely many of which vanish is the coproduct of the
finitely many that may not. -/
private def coprodIsoOfIsZero (F : ι → ModuleCat.{u} B) [HasCoproduct F]
    (s : Finset ι) (hs : ∀ j, j ∉ s → IsZero (F j)) :
    (∐ fun j : {j : ι // j ∈ s} => F j.1) ≅ (∐ F : ModuleCat.{u} B) := by
  classical
  refine
    { hom := Sigma.desc fun j => Sigma.ι F j.1
      inv := Sigma.desc fun j =>
        if h : j ∈ s then Sigma.ι (fun k : {j : ι // j ∈ s} => F k.1) ⟨j, h⟩ else 0
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply Sigma.hom_ext
    intro j
    simp only [Sigma.ι_desc_assoc, Sigma.ι_desc, Category.comp_id]
    rw [dif_pos j.2]
  · apply Sigma.hom_ext
    intro j
    simp only [Sigma.ι_desc_assoc, Category.comp_id]
    by_cases h : j ∈ s
    · rw [dif_pos h, Sigma.ι_desc]
    · rw [dif_neg h]
      exact (hs j h).eq_of_src _ _

/-- A coproduct of finitely presented modules all but finitely many of which vanish is finitely
presented. -/
private lemma finitePresentation_coproduct_of_isZero (F : ι → ModuleCat.{u} B) [HasCoproduct F]
    [∀ j, Module.FinitePresentation B (F j)] (s : Finset ι)
    (hs : ∀ j, j ∉ s → IsZero (F j)) :
    Module.FinitePresentation B (∐ F : ModuleCat.{u} B) := by
  classical
  let G : {j : ι // j ∈ s} → ModuleCat.{u} B := fun j => F j.1
  have hG : Module.FinitePresentation B (∐ G : ModuleCat.{u} B) := by
    have : Module.FinitePresentation B (∀ j : {j : ι // j ∈ s}, (G j : Type u)) :=
      Module.FinitePresentation.pi _
    exact Module.FinitePresentation.of_equiv
      (((ModuleCat.coprodIsoDirectSum G).toLinearEquiv.trans
        (DirectSum.linearEquivFunOnFintype B {j : ι // j ∈ s}
          fun j => (G j : Type u))).symm)
  exact Module.FinitePresentation.of_equiv (coprodIsoOfIsZero F s hs).toLinearEquiv

end Coproduct

/-- The terms of a total tensor product of two bounded above complexes are finitely presented
as soon as the termwise tensor products are: in each degree only finitely many bidegrees
contribute. -/
private lemma tensorLeftLarge_finitePresentation {B : Type u} [CommRing B]
    (E X : CochainComplex (ModuleCat.{u} B) ℤ) (a b : ℤ)
    [E.IsStrictlyLE a] [X.IsStrictlyLE b]
    (hEX : ∀ p q : ℤ, Module.FinitePresentation B (TensorProduct B (E.X p) (X.X q)))
    (i : ℤ) :
    Module.FinitePresentation B (((CochainComplex.tensorLeftLarge.{u, u} E).obj X).X i) := by
  classical
  let _ := ModuleCat.liftedModuleMonoidalStruct.{u, u} (R := B)
  let _ := ModuleCat.liftedModuleMonoidal.{u, u} (R := B)
  let F : {pq : ℤ × ℤ // pq.1 + pq.2 = i} → ModuleCat.{u} B :=
    fun pq => E.X pq.1.1 ⊗ X.X pq.1.2
  have hF : ∀ j, Module.FinitePresentation B (F j) := fun j => hEX j.1.1 j.1.2
  show Module.FinitePresentation B (∐ F : ModuleCat.{u} B)
  let s : Finset {pq : ℤ × ℤ // pq.1 + pq.2 = i} :=
    (Finset.Icc (i - b) a).map
      ⟨fun p => ⟨(p, i - p), by omega⟩, fun p q h => by exact congrArg (fun z => z.1.1) h⟩
  apply finitePresentation_coproduct_of_isZero F s
  intro j hj
  have hj' : ¬(i - b ≤ j.1.1 ∧ j.1.1 ≤ a) := by
    intro h
    apply hj
    apply Finset.mem_map.mpr
    refine ⟨j.1.1, Finset.mem_Icc.mpr h, ?_⟩
    apply Subtype.ext
    exact Prod.ext rfl (show i - j.1.1 = j.1.2 from by have := j.2; omega)
  by_cases hp : a < j.1.1
  · exact (tensorRight _).map_isZero (E.isZero_of_isStrictlyLE a _ hp)
  · exact (tensorLeft _).map_isZero (X.isZero_of_isStrictlyLE b _ (by have := j.2; omega))

/-! ### Transitivity -/

/-- A complex whose terms vanish wherever those of a bounded above complex do is bounded above. -/
private lemma isStrictlyLE_of_isZero_imp {A B : Type u} [CommRing A] [CommRing B]
    (K : CochainComplex (ModuleCat.{u} A) ℤ) {L : CochainComplex (ModuleCat.{u} B) ℤ} (n : ℤ)
    [K.IsStrictlyLE n] (h : ∀ i, IsZero (K.X i) → IsZero (L.X i)) : L.IsStrictlyLE n :=
  (CochainComplex.isStrictlyLE_iff L n).mpr fun i hi => h i (K.isZero_of_isStrictlyLE n i hi)

/-- A complex whose terms vanish wherever those of a bounded below complex do is bounded below. -/
private lemma isStrictlyGE_of_isZero_imp {A B : Type u} [CommRing A] [CommRing B]
    (K : CochainComplex (ModuleCat.{u} A) ℤ) {L : CochainComplex (ModuleCat.{u} B) ℤ} (n : ℤ)
    [K.IsStrictlyGE n] (h : ∀ i, IsZero (K.X i) → IsZero (L.X i)) : L.IsStrictlyGE n :=
  (CochainComplex.isStrictlyGE_iff L n).mpr fun i hi => h i (K.isZero_of_isStrictlyGE n i hi)

/-- Relative perfection depends only on the isomorphism class of the object in `D(A)`: it is
read off a bounded representative with terms flat over the base and finitely presented over `A`,
which [stacks 0DHV] produces from either side. -/
theorem isRelativelyPerfect_of_iso {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] [Algebra.FinitePresentation R A]
    (derivedTensor : DerivedCategory (ModuleCat.{u} R) ⥤
        DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R))
    (comparison : ∀ M : ModuleCat.{u} R,
      DerivedCategory.Q ⋙ derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) ⟶
        (StacksDraft.TorAmplitude.tensorModuleRight M).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (isLeftDerived : ∀ M : ModuleCat.{u} R,
      (derivedTensor.flip.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)).IsLeftDerivedFunctor
        (comparison M)
        (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)))
    {K K' : DerivedCategory (ModuleCat.{u} A)} (e : K ≅ K')
    (h : PseudoCoherence.IsRelativelyPerfect.{u, u, u} derivedTensor comparison isLeftDerived K) :
    PseudoCoherence.IsRelativelyPerfect.{u, u, u} derivedTensor comparison isLeftDerived K' := by
  obtain ⟨P, a, b, h1, h2, h3, h4, ⟨eP⟩⟩ :=
    (PseudoCoherence.isRelativelyPerfect_iff_exists_bounded_flat_finitePresentation.{u, u, u}
      derivedTensor comparison isLeftDerived K).1 h
  exact (PseudoCoherence.isRelativelyPerfect_iff_exists_bounded_flat_finitePresentation.{u, u, u}
    derivedTensor comparison isLeftDerived K').2 ⟨P, a, b, h1, h2, h3, h4, ⟨e.symm ≪≫ eP⟩⟩

section Transitivity

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
  [Module.Flat R A] [Module.Flat A B]
  [Algebra.FinitePresentation R A] [Algebra.FinitePresentation A B]

/-- **Transitivity of relative perfection.**  Let `R → A → B` be flat ring maps of finite
presentation, let `KA` be perfect relative to `R` in `D(A)` and `KB` perfect relative to `A` in
`D(B)`.  Then `KA ⊗ᴸ_A KB`, that is the value at `KA` of
`Dualizing.derivedTensorProductOver (algebraMap A B) KB`, is perfect relative to `R` in `D(B)`.

This is clause (1) of [stacks 0E2C] for the composite.  It carries nothing: see the module
documentation for the three steps, and in particular for why the models chosen by [stacks 0DHV]
compute the derived tensor product even though neither of them is K-flat over `A`. -/
@[sga "6 IV 3.3.2" "(f), special case"]
theorem isRelativelyPerfect_derivedTensorProductOver
    (KA : DerivedCategory (ModuleCat.{u} A)) (KB : DerivedCategory (ModuleCat.{u} B))
    (hKA : PseudoCoherence.IsRelativelyPerfect.{u, u, u}
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor
      (StacksDraft.TorAmplitude.canonicalTensorComparison R)
      (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived R) KA)
    (hKB : PseudoCoherence.IsRelativelyPerfect.{u, u, u}
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).tensor
      (StacksDraft.TorAmplitude.canonicalTensorComparison A)
      (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived A) KB) :
    letI : Module.Flat R B := Module.Flat.trans R A B
    letI : Algebra.FinitePresentation R B := Algebra.FinitePresentation.trans R A B
    PseudoCoherence.IsRelativelyPerfect.{u, u, u}
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor
      (StacksDraft.TorAmplitude.canonicalTensorComparison R)
      (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived R)
      ((derivedTensorProductOver.{u, u} (algebraMap A B) KB).obj KA) := by
  let : Module.Flat R B := Module.Flat.trans R A B
  let : Algebra.FinitePresentation R B := Algebra.FinitePresentation.trans R A B
  obtain ⟨P, a, b, hPGE, hPLE, hPflat, hPfp, ⟨eP⟩⟩ :=
    (PseudoCoherence.isRelativelyPerfect_iff_exists_bounded_flat_finitePresentation.{u, u, u}
      _ _ _ KA).1 hKA
  obtain ⟨N, c, d, hNGE, hNLE, hNflat, hNfp, ⟨eN⟩⟩ :=
    (PseudoCoherence.isRelativelyPerfect_iff_exists_bounded_flat_finitePresentation.{u, u, u}
      _ _ _ KB).1 hKB
  -- The restriction of the chosen model of `KB` to `A`: bounded with `A`-flat terms, hence
  -- K-flat over `A`.
  let NA := (CochainComplex.restrictScalarsLarge.{u, u, u} (algebraMap A B)).obj N
  have : NA.IsStrictlyLE d :=
    isStrictlyLE_of_isZero_imp N d fun _ => (ModuleCat.restrictScalars (algebraMap A B)).map_isZero
  have : NA.IsStrictlyGE c :=
    isStrictlyGE_of_isZero_imp N c fun _ => (ModuleCat.restrictScalars (algebraMap A B)).map_isZero
  have hNAflat : ∀ n : ℤ, Module.Flat A (NA.X n) := hNflat
  have hNkflat : CochainComplex.KFlat.{u, u} NA :=
    PseudoCoherence.kFlat_of_isStrictlyLE_flat.{u, u} NA d hNAflat
  let T := canonicalDerivedTensorChangeOfRings.{u, u, u} (algebraMap A B) N
  have halpha : IsIso T.alphaF :=
    isIso_alphaF_of_kFlat_restrictScalars (algebraMap A B) N T hNkflat
  -- The total tensor complex, and its identification with the derived tensor product.
  let Tot := T.directTensor.obj P
  obtain ⟨i1⟩ := derivedTensorProductOver_congr.{u, u} (algebraMap A B) KB
    (DerivedCategory.Q.obj N) eN
  obtain ⟨i2⟩ := derivedTensorRepresentativeIso.{u, u} (algebraMap A B) N
  have eobj : (derivedTensorProductOver.{u, u} (algebraMap A B) KB).obj KA ≅
      DerivedCategory.Q.obj Tot :=
    i1.app KA ≪≫ (i2.app KA).symm ≪≫ T.F.mapIso eP ≪≫ asIso (T.alphaF.app P)
  -- The underlying complex of `A`-modules of the total complex.
  have eA : (CochainComplex.restrictScalarsLarge.{u, u, u} (algebraMap A B)).obj Tot ≅
      (CochainComplex.tensorLeftLarge.{u, u} NA).obj P :=
    T.directTensorUnderlying.app P ≪≫
      (CochainComplex.DerivedTensor.tensorFlipIso.{u, u} NA P).symm
  have hzero : ∀ i : ℤ, IsZero (((CochainComplex.tensorLeftLarge.{u, u} NA).obj P).X i) →
      IsZero (Tot.X i) := by
    intro i h
    refine ModuleCat.isZero_iff_subsingleton.mpr ?_
    have h2 : IsZero (((CochainComplex.restrictScalarsLarge.{u, u, u}
        (algebraMap A B)).obj Tot).X i) :=
      h.of_iso ((HomologicalComplex.eval (ModuleCat.{u} A) (ComplexShape.up ℤ) i).mapIso eA)
    have h3 := ModuleCat.isZero_iff_subsingleton.mp h2
    exact h3
  have := PseudoCoherence.tensorLeftLarge_isStrictlyLE.{u, u} NA P d b
  have := PseudoCoherence.tensorLeftLarge_isStrictlyGE.{u, u} NA P c a
  refine (PseudoCoherence.isRelativelyPerfect_iff_exists_bounded_flat_finitePresentation.{u, u, u}
    _ _ _ _).2 ⟨Tot, c + a, d + b, ?_, ?_, ?_, ?_, ⟨eobj⟩⟩
  · exact isStrictlyGE_of_isZero_imp _ _ hzero
  · exact isStrictlyLE_of_isZero_imp _ _ hzero
  · intro i
    have h0 : Module.Flat R ((ModuleCat.restrictScalars (algebraMap R A)).obj
        ((HomologicalComplex.eval (ModuleCat.{u} A) (ComplexShape.up ℤ) i).obj
          ((CochainComplex.tensorLeftLarge.{u, u} NA).obj P))) :=
      PseudoCoherence.tensorLeftLarge_flat_restrictScalars.{u, u, u} NA P hNAflat hPflat i
    have e3 : (ModuleCat.restrictScalars (algebraMap R B)).obj (Tot.X i) ≅
        (ModuleCat.restrictScalars (algebraMap R A)).obj
          ((ModuleCat.restrictScalars (algebraMap A B)).obj (Tot.X i)) :=
      ModuleCat.restrictScalarsComp'App (algebraMap R A) (algebraMap A B) (algebraMap R B)
        (IsScalarTower.algebraMap_eq R A B) (Tot.X i)
    exact Module.Flat.of_linearEquiv
      (e3 ≪≫ (ModuleCat.restrictScalars (algebraMap R A)).mapIso
        ((HomologicalComplex.eval (ModuleCat.{u} A) (ComplexShape.up ℤ) i).mapIso
          eA)).toLinearEquiv
  · intro i
    let P' := (CochainComplex.extendScalarsLarge.{u, u, u} (algebraMap A B)).obj P
    have : P'.IsStrictlyLE b :=
      isStrictlyLE_of_isZero_imp P b fun _ => (ModuleCat.extendScalars (algebraMap A B)).map_isZero
    have hterm : ∀ p q : ℤ,
        Module.FinitePresentation B (TensorProduct B (N.X p) (P'.X q)) := by
      intro p q
      let : Module A (N.X p) :=
        ((ModuleCat.restrictScalars (algebraMap A B)).obj (N.X p)).isModule
      have : IsScalarTower A B (N.X p) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
      have : Module.FinitePresentation A (P.X q) := hPfp q
      have : Module.FinitePresentation B (N.X p) := hNfp p
      have e5 : TensorProduct B (N.X p) (P'.X q) ≃ₗ[B]
          TensorProduct B (N.X p) (TensorProduct A B (P.X q)) :=
        TensorProduct.congr (LinearEquiv.refl B (N.X p))
          (PseudoCoherence.extendScalarsAlgebraMapObjIso (P.X q)).toLinearEquiv
      have e6 : TensorProduct B (N.X p) (TensorProduct A B (P.X q)) ≃ₗ[B]
          TensorProduct A (N.X p) (P.X q) :=
        TensorProduct.AlgebraTensorModule.cancelBaseChange A B B (N.X p) (P.X q)
      have : Module.FinitePresentation B (TensorProduct A (N.X p) (P.X q)) :=
        finitePresentation_tensorProduct A B (P.X q) (N.X p)
      exact Module.FinitePresentation.of_equiv (e5.trans e6).symm
    have hfp : Module.FinitePresentation B
        ((HomologicalComplex.eval (ModuleCat.{u} B) (ComplexShape.up ℤ) i).obj
          ((CochainComplex.tensorLeftLarge.{u, u} N).obj P')) :=
      tensorLeftLarge_finitePresentation N P' d b hterm i
    exact Module.FinitePresentation.of_equiv
      ((HomologicalComplex.eval (ModuleCat.{u} B) (ComplexShape.up ℤ) i).mapIso
        (T.directTensorComparison.app P ≪≫
          (CochainComplex.DerivedTensor.tensorFlipIso.{u, u} N P').symm)).symm.toLinearEquiv

end Transitivity

end

end Dualizing

end
