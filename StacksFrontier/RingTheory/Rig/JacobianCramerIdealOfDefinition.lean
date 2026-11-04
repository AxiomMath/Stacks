module

public import StacksFrontier.RingTheory.Rig.JacobianCramerCriterion
public import StacksFrontier.RingTheory.Rig.RigEtaleLifting
public import StacksFrontier.RingTheory.Rig.RigEtaleLocality
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AdicQuotientSystemOfCompleteLocal
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleClosedImmersion

/-!
# Artin's Jacobian and Cramer condition for a map of `WAdm^{Noeth}`

Let `φ : A → C` be a continuous homomorphism of Noetherian adic topological rings which is adic
and topologically of finite type, so that for every ideal of definition `I` of `A` the ring `C`
is an object of the category of Stacks 0AL4 over `(A, I)`, with completed polynomial
presentations `C = A⟨x₁, …, x_r⟩ / J` (Stacks 0AJP). Artin's condition (i) of
[ArtinII, Definition 1.7] asks that the Jacobian ideal and the Cramer ideal of `C` over `A`
each contain an ideal of definition of `C`. This file shows, through Stacks 0AJY, that this
condition is rig-étaleness of `φ` (Stacks 0GCV), whether it is asked for every ideal of
definition, every presentation and every finite generating family of `J`, or only for one of
each.

## Main definitions

* `RingHom.JacobianCramerContainIdealOfDefinition`: for every ideal of definition `I` of `A`,
  every completed polynomial presentation of `C` over `(A, I)` and every finite family
  generating its ideal `J`, the Jacobian ideal and the Cramer ideal each contain an ideal of
  definition of `C`.
* `RingHom.JacobianCramerContainIdealOfDefinitionForSome`: the same for some ideal of
  definition, some presentation and some generating family.

## Main results

* `RingHom.isRigEtale_tfae_jacobianCramer`: for `φ` adic and topologically of finite type,
  rig-étaleness and the two forms of Artin's condition are equivalent.

## References

* [Stacks Project, Tag 0AJU](https://stacks.math.columbia.edu/tag/0AJU)
* [Stacks Project, Tag 0AJY](https://stacks.math.columbia.edu/tag/0AJY)
* [Stacks Project, Tag 0GCV](https://stacks.math.columbia.edu/tag/0GCV)
* [Stacks Project, Tag 0GDL](https://stacks.math.columbia.edu/tag/0GDL)
-/

@[expose] public noncomputable section

namespace RingHom

universe u

variable {A C : Type u}
  [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [IsNoetherianRing A]
  [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
    [IsNoetherianRing C]

/-- Artin's condition (i), asked of every presentation: for every ideal of definition `I` of
`A` over which `C` is an object of the category of Stacks 0AL4, every completed polynomial
presentation `C = A⟨x₁, …, x_r⟩ / J` over `(A, I)` and every finite family `f₁, …, f_t`
generating `J`, the Jacobian ideal and the Cramer ideal of `C` over `A` each contain an ideal of
definition of `C`. -/
abbrev JacobianCramerContainIdealOfDefinition (φ : A →+* C) : Prop :=
  ∀ (hft : Rig.FiniteTypeAdicAlgebraForEveryIdeal φ) (I : Ideal A)
    (hI : TopologicalRing.IsIdealOfDefinition I)
    (P : Rig.CompletedPolynomialPresentation I (Rig.adicFiniteTypeAlgebra φ hft I hI)) (t : ℕ)
    (f : Fin t → P.completedPolynomialRing), P.ker = Ideal.span (Set.range f) →
      (∃ J : Ideal C, TopologicalRing.IsIdealOfDefinition J ∧
          J ≤ Rig.completedJacobianIdeal (Rig.adicFiniteTypeAlgebra φ hft I hI) P f) ∧
        ∃ J : Ideal C, TopologicalRing.IsIdealOfDefinition J ∧
          J ≤ Rig.completedCramerIdeal (Rig.adicFiniteTypeAlgebra φ hft I hI) P

/-- Artin's condition (i), asked of one presentation: `C` is an object of the category of
Stacks 0AL4 over every ideal of definition of `A`, and for some ideal of definition `I` of `A`,
some completed polynomial presentation `C = A⟨x₁, …, x_r⟩ / J` over `(A, I)` and some finite
family `f₁, …, f_t` generating `J`, the Jacobian ideal and the Cramer ideal of `C` over `A` each
contain an ideal of definition of `C`. -/
abbrev JacobianCramerContainIdealOfDefinitionForSome (φ : A →+* C) : Prop :=
  ∃ (hft : Rig.FiniteTypeAdicAlgebraForEveryIdeal φ) (I : Ideal A)
    (hI : TopologicalRing.IsIdealOfDefinition I)
    (P : Rig.CompletedPolynomialPresentation I (Rig.adicFiniteTypeAlgebra φ hft I hI)) (t : ℕ)
    (f : Fin t → P.completedPolynomialRing), P.ker = Ideal.span (Set.range f) ∧
      (∃ J : Ideal C, TopologicalRing.IsIdealOfDefinition J ∧
          J ≤ Rig.completedJacobianIdeal (Rig.adicFiniteTypeAlgebra φ hft I hI) P f) ∧
        ∃ J : Ideal C, TopologicalRing.IsIdealOfDefinition J ∧
          J ≤ Rig.completedCramerIdeal (Rig.adicFiniteTypeAlgebra φ hft I hI) P

omit [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A] [IsNoetherianRing A] in
/-- In a ring carrying the `IC`-adic topology, an ideal contains an ideal of definition exactly
when it contains a power of `IC`: the powers of `IC` from the first on are ideals of definition,
and every ideal of definition is open, so contains a power of `IC`. -/
theorem exists_isIdealOfDefinition_le_iff_exists_pow_le {φ : A →+* C} {I : Ideal A}
    (hadic : _root_.IsAdic (I.map φ)) (K : Ideal C) :
    (∃ J : Ideal C, TopologicalRing.IsIdealOfDefinition J ∧ J ≤ K) ↔
      ∃ c : ℕ, I.map φ ^ c ≤ K := by
  constructor
  · rintro ⟨J, hJ, hJK⟩
    obtain ⟨n, hn⟩ := AlgebraicGeometry.FormalSpace.exists_pow_le_of_isOpen hadic hJ.1
    exact ⟨n, hn.trans hJK⟩
  · rintro ⟨c, hc⟩
    exact ⟨I.map φ ^ (c + 1), AlgebraicGeometry.FormalSpace.isIdealOfDefinition_pow_succ hadic c,
      (Ideal.pow_le_pow_right (Nat.le_succ c)).trans hc⟩

/-- For one ideal of definition `I`, one presentation and one generating family, the Jacobian
and the Cramer ideal each contain an ideal of definition of `C` exactly when the object of
Stacks 0AL4 cut out by `I` is rig-étale: by Stacks 0AJY this is the statement that each contains
a power of `IC`, and the powers of `IC` are cofinal among the ideals of definition of `C`,
which carries the `IC`-adic topology. -/
theorem exists_isIdealOfDefinition_le_jacobian_cramer_iff (φ : A →+* C)
    (hft : Rig.FiniteTypeAdicAlgebraForEveryIdeal φ) (I : Ideal A)
    (hI : TopologicalRing.IsIdealOfDefinition I)
    (P : Rig.CompletedPolynomialPresentation I (Rig.adicFiniteTypeAlgebra φ hft I hI)) {t : ℕ}
    (f : Fin t → P.completedPolynomialRing) (hf : P.ker = Ideal.span (Set.range f)) :
    ((∃ J : Ideal C, TopologicalRing.IsIdealOfDefinition J ∧
        J ≤ Rig.completedJacobianIdeal (Rig.adicFiniteTypeAlgebra φ hft I hI) P f) ∧
      ∃ J : Ideal C, TopologicalRing.IsIdealOfDefinition J ∧
        J ≤ Rig.completedCramerIdeal (Rig.adicFiniteTypeAlgebra φ hft I hI) P) ↔
      Rig.IsRigEtale (Rig.adicFiniteTypeAlgebra φ hft I hI) := by
  have hadic : _root_.IsAdic (I.map φ) := (hft I hI).1
  rw [Rig.isRigEtale_iff_exists_pow_le_completedJacobianIdeal_and_completedCramerIdeal _ P f hf]
  simp only [Ideal.map_pow]
  exact and_congr (exists_isIdealOfDefinition_le_iff_exists_pow_le hadic _)
    (exists_isIdealOfDefinition_le_iff_exists_pow_le hadic _)

/-- **Artin's condition (i) is rig-étaleness**, for a continuous homomorphism `φ : A → C` of
Noetherian adic topological rings which is adic and topologically of finite type, so that `C`
is an object of the category of Stacks 0AL4 over every ideal of definition of `A`. The
following are equivalent:

1. `φ` is rig-étale (Stacks 0GCV);
2. for every ideal of definition `I` of `A`, every completed polynomial presentation
   `C = A⟨x₁, …, x_r⟩ / J` over `(A, I)` and every finite family generating `J`, the Jacobian
   ideal and the Cramer ideal of `C` over `A` each contain an ideal of definition of `C`;
3. the same holds for some ideal of definition, some presentation and some generating family.

This is Stacks 0AJY at each ideal of definition, together with Stacks 0GCU, which makes
rig-étaleness over one ideal of definition rig-étaleness over all of them. -/
theorem isRigEtale_tfae_jacobianCramer (φ : A →+* C) (hφ : Continuous φ)
    (hA : TopologicalRing.IsAdic A) (hC : TopologicalRing.IsAdic C)
    (hft : Rig.FiniteTypeAdicAlgebraForEveryIdeal φ) :
    List.TFAE [RingHom.IsRigEtale φ, JacobianCramerContainIdealOfDefinition φ,
      JacobianCramerContainIdealOfDefinitionForSome φ] := by
  tfae_have 1 → 2 := by
    intro h hft' I hI P t f hf
    obtain ⟨hc, hfin, hre⟩ := h.forall_idealOfDefinition hφ hA hC I hI
    have heq : Rig.adicFiniteTypeAlgebra φ hft' I hI =
        (let : Algebra A C := φ.toAlgebra
         let : Algebra.FiniteType (A ⧸ I) (C ⧸ I.map (algebraMap A C)) := hfin
         Rig.AdicFiniteTypeAlgebra.of (I := I) C hc) := by
      apply CategoryTheory.ObjectProperty.FullSubcategory.ext
      rfl
    refine (exists_isIdealOfDefinition_le_jacobian_cramer_iff φ hft' I hI P f hf).mpr ?_
    rw [heq]
    exact hre
  tfae_have 2 → 3 := by
    intro h
    obtain ⟨I, hI, -⟩ := hA.1
    obtain ⟨P⟩ := Rig.nonempty_completedPolynomialPresentation (Ideal.fg_of_isNoetherianRing I)
      (Rig.adicFiniteTypeAlgebra φ hft I hI)
    obtain ⟨t, f, hf⟩ :=
      Submodule.fg_iff_exists_fin_generating_family.mp (Ideal.fg_of_isNoetherianRing P.ker)
    exact ⟨hft, I, hI, P, t, f, hf.symm, h hft I hI P t f hf.symm⟩
  tfae_have 3 → 1 := by
    rintro ⟨hft', I, hI, P, t, f, hf, hJ⟩
    exact RingHom.isRigEtale_of_isRigEtaleOver hft' I hI
      (Rig.isRigEtaleOver_of_isRigEtale φ hft' I hI
        ((exists_isIdealOfDefinition_le_jacobian_cramer_iff φ hft' I hI P f hf).mp hJ))
  tfae_finish

end RingHom

end
