module

public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.SequentialProIsomorphism
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.ProIsomorphismInterleaving
public import StacksFrontier.Homology.DerivedComplete.DerivedHomCompletionTorSequence
public import StacksFrontier.RingTheory.Module.AdicSystem.PseudoCoherentHomology

@[expose] public noncomputable section

/-!
# The adic tower comparison on cohomology is a pro-isomorphism

Let `I` be an ideal of a Noetherian ring `A`. For a complex `P` of finite `A`-modules the tower
of cohomology modules of the degreewise reductions, `n ↦ H^i(P/Iⁿ⁺¹P)`, is compared with the
adic quotient tower of the cohomology, `n ↦ H^i(P)/Iⁿ⁺¹H^i(P)`. Neither map is an isomorphism
at a fixed level, but the comparison is an isomorphism of inverse systems up to a shift of the
index: the two towers are pro-isomorphic, with one uniform shift serving every level. For a
pseudo-coherent object `K` of `D(A)` the same holds with the derived reductions
`K ⊗^𝐋_A A/Iⁿ⁺¹` in place of the degreewise ones.

The mathematical content is Artin--Rees, applied to the cycles and the boundaries of the complex
inside its terms; this is what both the Noetherian hypothesis and the finiteness of the terms
are for. The statement is false for a non-Noetherian base, and false without finiteness: with no
uniform Artin--Rees bound there is no uniform shift, and a tower whose level `i` needs shift
`≥ n + i` is not pro-isomorphic to anything.

## Main definitions

* `InverseSequence.ProIso.reindexSuccessorOp` reindexes a pro-isomorphism along the shift
  `n ↦ n + 1` of the index, which is what matches the two indexing conventions in play: the
  Artin--Rees comparison of [Stacks, Tag 0EGU] is stated at the exponents `Iⁿ`, while the
  derived tower `NoetherianAdicCompletion.idealPowerQuotientSystem` runs over the positive
  powers `Iⁿ⁺¹`.
* `Stacks.AdicTowerCohomology.adicQuotientSystemMapIso` transports the adic quotient tower of a
  module along an isomorphism of modules.
* `Stacks.AdicTowerCohomology.adicQuotientSystemIsoOfQuotientTransition` recognises a tower of
  quotients `n ↦ H/IⁿH` whose transitions are compatible with the quotient maps as the adic
  quotient tower.

## Main results

* `Stacks.AdicTowerCohomology.nonempty_proIso_concreteReductionHomologySystem_adicQuotientSystem`:
  the pro-isomorphism in the concrete presentation of both towers, for a complex of finite
  modules.
* `Stacks.AdicTowerCohomology.nonempty_proIso_reductionHomology_adicQuotientSystem`: the same at
  the categorical homology of the degreewise reductions. Nothing is assumed of the complex
  beyond finiteness of its terms.
* `Stacks.AdicTowerCohomology.nonempty_proIso_derivedReductionHomology_adicQuotientSystem`: the
  statement for a pseudo-coherent object of `D(A)` and its derived reductions, which is the form
  a consumer of the tower `n ↦ K ⊗^𝐋_A A/Iⁿ⁺¹` wants.

## Implementation notes

Pro-isomorphism is the repository's explicit up-to-refinement structure `InverseSequence.ProIso`
and, as everywhere it is used, the conclusions are `Nonempty (ProIso _ _)`: the refinement data
is not canonical.

The Artin--Rees input is [Stacks, Tag 0EGU], already available for a three-term complex of
finite modules; one degree of a complex is such a three-term complex, so the work here is to
identify the two towers appearing in that tag with the towers of this file — on the one side the
homology of the derived reductions of a pseudo-coherent object, on the other the adic quotient
tower of its cohomology — and to reconcile the two index conventions.

No new mathematics about derived reductions is developed: the identification of the derived
reductions of a pseudo-coherent object with the degreewise reductions of a bounded-above
finite-free representative, and the concrete presentation of their homology, are taken from
`StacksFrontier.RingTheory.Module.AdicSystem.PseudoCoherentHomology`.

## References

* [Stacks Project, Tag 0EGU](https://stacks.math.columbia.edu/tag/0EGU)
* [Stacks Project, Tag 0A06](https://stacks.math.columbia.edu/tag/0A06)
-/

open CategoryTheory CategoryTheory.Limits Opposite InverseSequence

universe u

namespace InverseSequence.ProIso

open Stacks.AdicSystem.DerivedReductionProIso (successorOp)

variable {D : Type*} [Category D]

/-- The transition maps of the index shift `n ↦ n + 1` of an inverse system are the transition
maps of the system itself, between the shifted indices. -/
theorem tr_successorOp (X : ℕᵒᵖ ⥤ D) {n m : ℕ} (h : n ≤ m) :
    tr (successorOp ⋙ X) h = tr X (Nat.add_le_add_right h 1) := by
  show X.map (successorOp.map (homOfLE h).op) = X.map (homOfLE _).op
  exact congrArg X.map (Subsingleton.elim _ _)

/-- **A pro-isomorphism may be reindexed by the shift `n ↦ n + 1`.** Both systems are
reindexed along the same cofinal shift, so the reindexed comparison maps are the original ones
composed with one transition map. -/
def reindexSuccessorOp {X Y : ℕᵒᵖ ⥤ D} (a : ProIso X Y) :
    ProIso (successorOp ⋙ X) (successorOp ⋙ Y) where
  α m := a.α (m + 1)
  β m := a.β (m + 1)
  αmono _ _ h := a.αmono (Nat.add_le_add_right h 1)
  βmono _ _ h := a.βmono (Nat.add_le_add_right h 1)
  αle m := (Nat.le_succ m).trans (a.αle (m + 1))
  βle m := (Nat.le_succ m).trans (a.βle (m + 1))
  φ m := tr X (Nat.le_succ (a.α (m + 1))) ≫ a.φ (m + 1)
  ψ m := tr Y (Nat.le_succ (a.β (m + 1))) ≫ a.ψ (m + 1)
  φnat {m m'} h := by
    rw [tr_successorOp, tr_successorOp]
    calc tr X (Nat.add_le_add_right (a.αmono (Nat.add_le_add_right h 1)) 1) ≫
          tr X (Nat.le_succ (a.α (m + 1))) ≫ a.φ (m + 1)
        = tr X ((Nat.le_succ (a.α (m + 1))).trans
            (Nat.add_le_add_right (a.αmono (Nat.add_le_add_right h 1)) 1)) ≫
            a.φ (m + 1) := by
          rw [← Category.assoc, tr_trans]
      _ = (tr X (Nat.le_succ (a.α (m' + 1))) ≫
            tr X (a.αmono (Nat.add_le_add_right h 1))) ≫ a.φ (m + 1) := by
          rw [tr_trans]
      _ = tr X (Nat.le_succ (a.α (m' + 1))) ≫
            tr X (a.αmono (Nat.add_le_add_right h 1)) ≫ a.φ (m + 1) := Category.assoc _ _ _
      _ = tr X (Nat.le_succ (a.α (m' + 1))) ≫
            a.φ (m' + 1) ≫ tr Y (Nat.add_le_add_right h 1) := by
          rw [a.φnat (Nat.add_le_add_right h 1)]
      _ = _ := (Category.assoc _ _ _).symm
  ψnat {m m'} h := by
    rw [tr_successorOp, tr_successorOp]
    calc tr Y (Nat.add_le_add_right (a.βmono (Nat.add_le_add_right h 1)) 1) ≫
          tr Y (Nat.le_succ (a.β (m + 1))) ≫ a.ψ (m + 1)
        = tr Y ((Nat.le_succ (a.β (m + 1))).trans
            (Nat.add_le_add_right (a.βmono (Nat.add_le_add_right h 1)) 1)) ≫
            a.ψ (m + 1) := by
          rw [← Category.assoc, tr_trans]
      _ = (tr Y (Nat.le_succ (a.β (m' + 1))) ≫
            tr Y (a.βmono (Nat.add_le_add_right h 1))) ≫ a.ψ (m + 1) := by
          rw [tr_trans]
      _ = tr Y (Nat.le_succ (a.β (m' + 1))) ≫
            tr Y (a.βmono (Nat.add_le_add_right h 1)) ≫ a.ψ (m + 1) := Category.assoc _ _ _
      _ = tr Y (Nat.le_succ (a.β (m' + 1))) ≫
            a.ψ (m' + 1) ≫ tr X (Nat.add_le_add_right h 1) := by
          rw [a.ψnat (Nat.add_le_add_right h 1)]
      _ = _ := (Category.assoc _ _ _).symm
  ψφ m := by
    rw [tr_successorOp]
    calc (tr X (Nat.le_succ (a.α (a.β (m + 1) + 1))) ≫ a.φ (a.β (m + 1) + 1)) ≫
          tr Y (Nat.le_succ (a.β (m + 1))) ≫ a.ψ (m + 1)
        = tr X (Nat.le_succ (a.α (a.β (m + 1) + 1))) ≫
            (a.φ (a.β (m + 1) + 1) ≫ tr Y (Nat.le_succ (a.β (m + 1)))) ≫
              a.ψ (m + 1) := by simp only [Category.assoc]
      _ = tr X (Nat.le_succ (a.α (a.β (m + 1) + 1))) ≫
            (tr X (a.αmono (Nat.le_succ (a.β (m + 1)))) ≫ a.φ (a.β (m + 1))) ≫
              a.ψ (m + 1) := by
          rw [a.φnat (Nat.le_succ (a.β (m + 1)))]
      _ = (tr X (Nat.le_succ (a.α (a.β (m + 1) + 1))) ≫
            tr X (a.αmono (Nat.le_succ (a.β (m + 1))))) ≫
              a.φ (a.β (m + 1)) ≫ a.ψ (m + 1) := by simp only [Category.assoc]
      _ = tr X ((a.αmono (Nat.le_succ (a.β (m + 1)))).trans
            (Nat.le_succ (a.α (a.β (m + 1) + 1)))) ≫
              tr X ((a.βle (m + 1)).trans (a.αle (a.β (m + 1)))) := by
          rw [tr_trans, a.ψφ (m + 1)]
      _ = _ := tr_trans _ _ _
  φψ m := by
    rw [tr_successorOp]
    calc (tr Y (Nat.le_succ (a.β (a.α (m + 1) + 1))) ≫ a.ψ (a.α (m + 1) + 1)) ≫
          tr X (Nat.le_succ (a.α (m + 1))) ≫ a.φ (m + 1)
        = tr Y (Nat.le_succ (a.β (a.α (m + 1) + 1))) ≫
            (a.ψ (a.α (m + 1) + 1) ≫ tr X (Nat.le_succ (a.α (m + 1)))) ≫
              a.φ (m + 1) := by simp only [Category.assoc]
      _ = tr Y (Nat.le_succ (a.β (a.α (m + 1) + 1))) ≫
            (tr Y (a.βmono (Nat.le_succ (a.α (m + 1)))) ≫ a.ψ (a.α (m + 1))) ≫
              a.φ (m + 1) := by
          rw [a.ψnat (Nat.le_succ (a.α (m + 1)))]
      _ = (tr Y (Nat.le_succ (a.β (a.α (m + 1) + 1))) ≫
            tr Y (a.βmono (Nat.le_succ (a.α (m + 1))))) ≫
              a.ψ (a.α (m + 1)) ≫ a.φ (m + 1) := by simp only [Category.assoc]
      _ = tr Y ((a.βmono (Nat.le_succ (a.α (m + 1)))).trans
            (Nat.le_succ (a.β (a.α (m + 1) + 1)))) ≫
              tr Y ((a.αle (m + 1)).trans (a.βle (a.α (m + 1)))) := by
          rw [tr_trans, a.φψ (m + 1)]
      _ = _ := tr_trans _ _ _

end InverseSequence.ProIso

namespace Stacks.AdicTowerCohomology

open Stacks.AdicSystem.DerivedReductionProIso (successorOp)

variable {A : Type u} [CommRing A]

/-! ### Transport of the adic quotient tower along an isomorphism of modules -/

/-- The adic quotient tower `n ↦ M/Iⁿ⁺¹M` transported along an isomorphism `M ≅ N`. -/
def adicQuotientSystemMapIso (I : Ideal A) {M N : ModuleCat.{u} A} (e : M ≅ N) :
    AdicCompletionTor.adicQuotientSystem I M ≅ AdicCompletionTor.adicQuotientSystem I N := by
  have hmap : ∀ k : ℕ, Submodule.map (e.toLinearEquiv : M →ₗ[A] N)
      (I ^ k • (⊤ : Submodule A M)) = I ^ k • (⊤ : Submodule A N) := by
    intro k
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]
  refine NatIso.ofComponents (fun n =>
    (Submodule.Quotient.equiv _ _ e.toLinearEquiv (hmap (n.unop + 1))).toModuleIso) ?_
  intro n m f
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
  rfl

/-! ### The quotient tower of `0EGU` is the adic quotient tower -/

/-- Any family of transition maps on the tower `n ↦ H/IⁿH` that is compatible with the quotient
maps assembles to the adic quotient tower, after the shift `n ↦ n + 1`. -/
def adicQuotientSystemIsoOfQuotientTransition (I : Ideal A) (H : Type u) [AddCommGroup H]
    [Module A H]
    (quotTransition : ∀ n : ℕ, (H ⧸ I ^ (n + 1) • (⊤ : Submodule A H)) →ₗ[A]
      (H ⧸ I ^ n • (⊤ : Submodule A H)))
    (hq : ∀ (n : ℕ) (x : H),
      quotTransition n (Submodule.Quotient.mk x) = Submodule.Quotient.mk x) :
    successorOp ⋙ Functor.ofOpSequence
        (X := fun n => ModuleCat.of A (H ⧸ I ^ n • (⊤ : Submodule A H)))
        (fun n => ModuleCat.ofHom (quotTransition n)) ≅
      AdicCompletionTor.adicQuotientSystem I (ModuleCat.of A H) := by
  have key : ∀ (k l : ℕ) (hkl : l ≤ k),
      (Functor.ofOpSequence
          (X := fun n => ModuleCat.of A (H ⧸ I ^ n • (⊤ : Submodule A H)))
          (fun n => ModuleCat.ofHom (quotTransition n))).map (homOfLE hkl).op =
        ModuleCat.ofHom (AdicCompletion.transitionMap I (ModuleCat.of A H) hkl) := by
    refine NoetherianAdicCompletion.ofOpSequence_map_eq _
      (fun k l hkl => ModuleCat.ofHom (AdicCompletion.transitionMap I
        (ModuleCat.of A H) hkl)) ?_ ?_
    · intro n
      refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
      rfl
    · intro k l hkl
      refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
      simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
        ModuleCat.hom_ofHom]
      exact (congrArg (AdicCompletion.transitionMap I (ModuleCat.of A H) hkl) (hq k x)).symm
  refine NatIso.ofComponents (fun n => Iso.refl _) (fun {n m} f => ?_)
  have h : m.unop ≤ n.unop := leOfHom f.unop
  have hf : f = (homOfLE h).op := Subsingleton.elim _ _
  subst hf
  refine (Category.comp_id _).trans (Eq.trans ?_ (Category.id_comp _).symm)
  exact key (n.unop + 1) (m.unop + 1) (Nat.add_le_add_right h 1)

/-! ### The pro-isomorphism at the concrete presentation of the homology -/

open Stacks.AdicSystem.DerivedReductionProIso (concreteHomologyIdealTransition
  reductionCyclesMapOfIdealLE)
open Stacks.PseudoCoherent.AdicCompletion (degreewiseReductionHomologySystem)

/-- **Artin--Rees for a complex of finite modules, as a pro-isomorphism of towers.** For a
complex `P` of finite modules over a Noetherian ring, the tower `n ↦ H^i(P/Iⁿ⁺¹P)` of homology
modules of the degreewise reductions is pro-isomorphic to the adic quotient tower
`n ↦ H^i(P)/Iⁿ⁺¹H^i(P)` of its homology, in the concrete presentation of both. -/
theorem nonempty_proIso_concreteReductionHomologySystem_adicQuotientSystem
    [IsNoetherianRing A] (I : Ideal A) (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (hP : ∀ n, Module.Finite A (P.X n)) (i : ℤ) :
    Nonempty (ProIso (successorOp ⋙ degreewiseReductionHomologySystem I P i)
      (AdicCompletionTor.adicQuotientSystem I (ModuleCat.of A
        (LinearMap.ker (P.sc i).g.hom ⧸
          (LinearMap.range (P.sc i).f.hom).comap
            (LinearMap.ker (P.sc i).g.hom).subtype)))) := by
  have : Module.Finite A (P.sc i).X₁ := hP _
  have : Module.Finite A (P.sc i).X₂ := hP _
  have : Module.Finite A (P.sc i).X₃ := hP _
  obtain ⟨toLevel, transition, quotTransition, fromQuotient, hh⟩ :=
    Stacks.AdicSystem.ArtinReesHomology.exists_uniform_adic_homology_comparison I
      (P.sc i).f.hom (P.sc i).g.hom (congrArg ModuleCat.Hom.hom (P.sc i).zero)
  have ht : transition = fun n => concreteHomologyIdealTransition
      (Ideal.pow_le_pow_right (Nat.le_succ n) : I ^ (n + 1) ≤ I ^ n)
      (P.sc i).f (P.sc i).g (P.sc i).zero := by
    funext n
    refine LinearMap.ext fun x => ?_
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
    exact hh.2.1 n x (reductionCyclesMapOfIdealLE
      (Ideal.pow_le_pow_right (Nat.le_succ n)) (P.sc i).g x) rfl
  have hq := hh.2.2.1
  obtain ⟨c, hc, back, hb⟩ := hh.2.2.2.2.2
  obtain ⟨a⟩ := hb.2.2.1
  subst ht
  exact ⟨CategoryTheory.Pro.proIsoTrans a.reindexSuccessorOp
    (InverseSequence.ProIso.ofNatIso
      (adicQuotientSystemIsoOfQuotientTransition I _ quotTransition hq))⟩

/-! ### The pro-isomorphism of the derived adic tower on cohomology -/

open Stacks.PseudoCoherent.AdicCompletion (degreewiseReductionSystem
  derivedReductionSystemIsoDegreewise degreewiseReductionHomologySystemIso)

/-- The concrete presentation of the homology of `P` in degree `i` is its categorical homology. -/
private def concreteHomologyIso (P : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ) :=
  (Submodule.quotEquivOfEq _ _
      (LinearMap.range_codRestrict _ _ (P.sc i).moduleCat_zero_apply).symm).toModuleIso ≪≫
    (P.sc i).moduleCatHomologyIso.symm

/-- **The adic tower comparison on the cohomology of a complex of finite modules is a
pro-isomorphism.** For a complex `P` of finite modules over a Noetherian ring `A` and an ideal
`I ⊆ A`, the tower `n ↦ H^i(P/Iⁿ⁺¹P)` is pro-isomorphic to `n ↦ H^i(P)/Iⁿ⁺¹H^i(P)`. No
flatness is assumed: this is the degreewise-reduction form, from which the derived form below
follows for a K-flat representative. -/
theorem nonempty_proIso_reductionHomology_adicQuotientSystem
    [IsNoetherianRing A] (I : Ideal A) (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (hP : ∀ n, Module.Finite A (P.X n)) (i : ℤ) :
    Nonempty (ProIso
      (degreewiseReductionSystem I P ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (ComplexShape.up ℤ) i)
      (AdicCompletionTor.adicQuotientSystem I
        ((HomologicalComplex.homologyFunctor (ModuleCat.{u} A)
          (ComplexShape.up ℤ) i).obj P))) := by
  obtain ⟨a⟩ := nonempty_proIso_concreteReductionHomologySystem_adicQuotientSystem I P hP i
  exact ⟨CategoryTheory.Pro.proIsoTrans
    (InverseSequence.ProIso.ofNatIso (degreewiseReductionHomologySystemIso I P i).symm)
    (CategoryTheory.Pro.proIsoTrans a
      (InverseSequence.ProIso.ofNatIso
        (adicQuotientSystemMapIso I (concreteHomologyIso P i))))⟩

attribute [local instance] HasDerivedCategory.standard

/-- **The adic tower comparison on cohomology is a pro-isomorphism over a Noetherian base.**
Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `K` a pseudo-coherent object of `D(A)`.
Then for every `i` the tower of cohomology modules of the derived reductions,
`n ↦ H^i(K ⊗^𝐋_A A/Iⁿ⁺¹)`, is pro-isomorphic to the adic quotient tower of the cohomology,
`n ↦ H^i(K)/Iⁿ⁺¹H^i(K)`. The content is Artin--Rees, which is where the Noetherian hypothesis
and the finiteness of the terms of a pseudo-coherent representative are used. -/
theorem nonempty_proIso_derivedReductionHomology_adicQuotientSystem
    [IsNoetherianRing A] (I : Ideal A) (K : DerivedCategory (ModuleCat.{u} A))
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) (i : ℤ) :
    Nonempty (ProIso
      ((NoetherianAdicCompletion.idealPowerQuotientSystem I ⋙ T.tensor.obj K) ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{u} A) i)
      (AdicCompletionTor.adicQuotientSystem I
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K))) := by
  obtain ⟨P, hP, ⟨e⟩⟩ := hK
  obtain ⟨b, hb⟩ := hP.upperBound
  have : P.IsStrictlyLE b := hb
  have : ∀ n, Module.Flat A (P.X n) := fun n => by
    have : Module.Free A (P.X n) := (hP.finiteFree n).2
    infer_instance
  have hflat : P.KFlat := CochainComplex.KFlat.kFlat_of_flat P b
  -- The tower of derived reductions of `K` is the tower of degreewise reductions of `P`,
  -- and its homology is the concrete homology of those reductions.
  let g : (NoetherianAdicCompletion.idealPowerQuotientSystem I ⋙ T.tensor.obj K) ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} A) i ≅
      successorOp ⋙ degreewiseReductionHomologySystem I P i :=
    Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft (NoetherianAdicCompletion.idealPowerQuotientSystem I)
          (T.tensor.mapIso e)).symm
        (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i) ≪≫
      Functor.isoWhiskerRight (derivedReductionSystemIsoDegreewise I T P hflat)
        (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i) ≪≫
      Functor.isoWhiskerLeft (degreewiseReductionSystem I P)
        (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) i) ≪≫
      (degreewiseReductionHomologySystemIso I P i).symm
  -- The concrete homology of `P` in degree `i` is `H^i(K)`.
  let q := concreteHomologyIso P i ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) i).symm.app P ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapIso e
  obtain ⟨a⟩ := nonempty_proIso_concreteReductionHomologySystem_adicQuotientSystem I P
    (fun n => (hP.finiteFree n).1) i
  exact ⟨CategoryTheory.Pro.proIsoTrans (InverseSequence.ProIso.ofNatIso g)
    (CategoryTheory.Pro.proIsoTrans a
      (InverseSequence.ProIso.ofNatIso (adicQuotientSystemMapIso I q)))⟩

end Stacks.AdicTowerCohomology

end
