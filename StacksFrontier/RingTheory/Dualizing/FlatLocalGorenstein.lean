module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import StacksFrontier.Homology.Ext.DerivedCoyoneda
public import StacksFrontier.Homology.HomComplex.DerivedAdjunction
public import StacksFrontier.Homology.PseudoCoherent.HomFlat
public import StacksFrontier.RingTheory.Dualizing.Complex
public import StacksFrontier.RingTheory.Dualizing.ResidueFieldShift
public import StacksFrontier.RingTheory.Dualizing.Gorenstein
public import StacksFrontier.RingTheory.Dualizing.TrivialDuality
public import StacksFrontier.RingTheory.Dualizing.TrivialDualityRing.Ext

/-!
# Gorenstein rings under flat local homomorphisms

For a flat local homomorphism `A → B` of Noetherian local rings, the target is Gorenstein
exactly when the source and the closed fibre `B ⧸ m_A B` are Gorenstein.

## Main results

* `Dualizing.isGorensteinLocalRing_iff_of_flat`: for a flat local homomorphism of Noetherian
  local rings, the target is Gorenstein if and only if the source and the closed fibre are.
* `Dualizing.isGorensteinLocalRing_of_ringEquiv`: a Noetherian local ring isomorphic to a
  Gorenstein local ring is Gorenstein.

## References

* [Stacks Project, Tag 0BJL](https://stacks.math.columbia.edu/tag/0BJL)
-/

@[expose] public section

namespace Dualizing

open IsLocalRing
open CategoryTheory
open scoped TensorProduct

universe uA uB uW

attribute [local instance] HasDerivedCategory.standard in
private noncomputable def derivedExtAdjunctionEquiv {A : Type uA} {B : Type uB}
    [CommRing A] [CommRing B] (q : A →+* B)
    (X : DerivedCategory (ModuleCat.{max uA uB uW} B))
    (Y : DerivedCategory (ModuleCat.{max uA uB uW} A)) (i : ℤ) :
    DerivedCategory.Ext
        ((ModuleCat.restrictScalars.{max uA uB uW} q).mapDerivedCategory.obj X) Y i ≃
      DerivedCategory.Ext X
      ((derivedHom.{uA, max uB uW, uB} q).obj Y) i := by
  let R := ModuleCat.restrictScalars.{max uA uB uW} q
  let G := derivedHom.{uA, max uB uW, uB} q
  letI : Limits.PreservesFiniteLimits R := by
    constructor
    intro J _ _
    constructor
    intro F
    infer_instance
  letI : Limits.PreservesFiniteColimits R := by
    constructor
    intro J _ _
    constructor
    intro F
    infer_instance
  letI : R.mapDerivedCategory.CommShift ℤ := inferInstance
  let adj := Classical.choice
    (restrictScalarsDerived_adj_derivedHom.{uA, max uB uW, uB} q)
  letI : G.CommShift ℤ := adj.rightAdjointCommShift ℤ
  letI : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
  exact (adj.homEquiv X (Y⟦i⟧)).trans
    (Iso.homCongr (Iso.refl X) ((G.commShiftIso i).app Y))

/-! ### Transporting the residue-field criterion to a common module universe -/

attribute [local instance] HasDerivedCategory.standard

private noncomputable def derivedExtUliftEquiv {R : Type uA} [CommRing R]
    (M N : ModuleCat.{uA} R) (n : ℕ) :
    DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{uA} R) 0).obj M)
        ((DerivedCategory.singleFunctor (ModuleCat.{uA} R) 0).obj N) n ≃
      DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{max uA uB} R) 0).obj
          ((ModuleCat.uliftFunctor.{uB} R).obj M))
        ((DerivedCategory.singleFunctor (ModuleCat.{max uA uB} R) 0).obj
          ((ModuleCat.uliftFunctor.{uB} R).obj N)) n := by
  let F := ModuleCat.uliftFunctor.{uB, uA} R
  let e := Equiv.ofBijective (F.mapExtAddHom M N n)
    (Functor.mapExt_bijective_of_preservesProjectiveObjects F M N n)
  exact (Abelian.Ext.homEquiv.symm).trans (e.trans Abelian.Ext.homEquiv)

private lemma residueExtVanish_iff_ulift (R : Type uA) [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] :
    (∃ b : ℤ, ∀ i : ℤ, b < i →
      Subsingleton (DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{uA} R) 0).obj
          (ModuleCat.of R (Shrink.{uA} (R ⧸ maximalIdeal R))))
        ((DerivedCategory.singleFunctor (ModuleCat.{uA} R) 0).obj
          (ModuleCat.of R R)) i)) ↔
    (∃ b : ℤ, ∀ i : ℤ, b < i →
      Subsingleton (DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{max uA uB} R) 0).obj
          ((ModuleCat.uliftFunctor.{uB} R).obj
            (ModuleCat.of R (Shrink.{uA} (R ⧸ maximalIdeal R)))))
        ((DerivedCategory.singleFunctor (ModuleCat.{max uA uB} R) 0).obj
          ((ModuleCat.uliftFunctor.{uB} R).obj (ModuleCat.of R R))) i)) := by
  have key : ∀ i : ℤ, 0 ≤ i →
      (Subsingleton (DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{uA} R) 0).obj
          (ModuleCat.of R (Shrink.{uA} (R ⧸ maximalIdeal R))))
        ((DerivedCategory.singleFunctor (ModuleCat.{uA} R) 0).obj
          (ModuleCat.of R R)) i) ↔
      Subsingleton (DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{max uA uB} R) 0).obj
          ((ModuleCat.uliftFunctor.{uB} R).obj
            (ModuleCat.of R (Shrink.{uA} (R ⧸ maximalIdeal R)))))
        ((DerivedCategory.singleFunctor (ModuleCat.{max uA uB} R) 0).obj
          ((ModuleCat.uliftFunctor.{uB} R).obj (ModuleCat.of R R))) i)) := by
    intro i hi
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hi
    exact (derivedExtUliftEquiv (ModuleCat.of R (Shrink.{uA} (R ⧸ maximalIdeal R)))
      (ModuleCat.of R R) n).subsingleton_congr
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨max b 0, fun i hi => (key i (by omega)).mp (hb i (by omega))⟩
  · rintro ⟨b, hb⟩
    exact ⟨max b 0, fun i hi => (key i (by omega)).mpr (hb i (by omega))⟩

private theorem isGorensteinLocalRing_iff_residueField_ext_vanishing_ulift
    (R : Type uA) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] :
    IsGorensteinLocalRing R ↔
      ∃ b : ℤ, ∀ i : ℤ, b < i →
        Subsingleton (DerivedCategory.Ext
          ((DerivedCategory.singleFunctor (ModuleCat.{max uA uB} R) 0).obj
            ((ModuleCat.uliftFunctor.{uB} R).obj
              (ModuleCat.of R (Shrink.{uA} (R ⧸ maximalIdeal R)))))
          ((DerivedCategory.singleFunctor (ModuleCat.{max uA uB} R) 0).obj
            ((ModuleCat.uliftFunctor.{uB} R).obj (ModuleCat.of R R))) i) :=
  (isGorensteinLocalRing_iff_residueField_ext_vanishing R).trans (residueExtVanish_iff_ulift R)

universe uR uS uM

private lemma flatExtBaseChangeLinearEquiv
    {R : Type uA} {S : Type uB} [CommRing R] [CommRing S]
    [Algebra R S] [Module.Flat R S] [IsNoetherianRing R]
    (M : Type uA) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (N : Type uA) [AddCommGroup N] [Module R N] (i : ℕ) :
    Nonempty
      ((S ⊗[R] (Abelian.Ext
        (ModuleCat.of R (ULift.{max uA uB} M))
        (ModuleCat.of R (ULift.{max uA uB} N)) i)) ≃ₗ[S]
       Abelian.Ext
        (ModuleCat.of S (ULift.{max uA uB} (S ⊗[R] M)))
        (ModuleCat.of S (ULift.{max uA uB} (S ⊗[R] N))) i) := by
  classical
  let RM := ModuleCat.of R (ULift.{max uA uB} M)
  let RN := ModuleCat.of R (ULift.{max uA uB} N)
  let SM := ModuleCat.of S (ULift.{max uA uB} (S ⊗[R] M))
  let SN := ModuleCat.of S (ULift.{max uA uB} (S ⊗[R] N))
  have hBase := StacksDraft.PseudoCoherence.baseChange_ext_bijective_of_pseudoCoherent
    R S M N
  dsimp only at hBase
  obtain ⟨η, t, hη, ht, htuniq, hall⟩ := hBase
  obtain ⟨β, hcomm, hβuniq, hβsmul, hβzero, hβfin, hβpc, hβbij⟩ := hall i
  have hβ : Function.Bijective β := hβbij ‹IsNoetherianRing R› ‹Module.Finite R M›
  let f : (S ⊗[R] Abelian.Ext RM RN i) →+ (Abelian.Ext SM SN i) :=
    β.comp (TensorProduct.comm R S (Abelian.Ext RM RN i)).toAddMonoidHom
  let g : (S ⊗[R] Abelian.Ext RM RN i) →ₗ[S] (Abelian.Ext SM SN i) :=
    { __ := f
      map_smul' := by
        intro r z
        change f (r • z) = r • f z
        induction z using TensorProduct.inductionOn with
        | tmul s e =>
            simpa [f, TensorProduct.smul_tmul'] using hβsmul e s r
        | add x y hx hy => simp only [smul_add, map_add, hx, hy] }
  exact ⟨LinearEquiv.ofBijective g
    (hβ.comp (TensorProduct.comm R S (Abelian.Ext RM RN i)).bijective)⟩

private lemma flatExtVanish_iff_of_faithfullyFlat
    {A : Type uA} {B : Type uB} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [Algebra A B]
    [Module.FaithfullyFlat A B]
    (M : Type uA) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (N : Type uA) [AddCommGroup N] [Module A N] (i : ℕ) :
    Subsingleton (Abelian.Ext
      (ModuleCat.of B (ULift.{max uB uA} (B ⊗[A] M)))
      (ModuleCat.of B (ULift.{max uB uA} (B ⊗[A] N))) i) ↔
    Subsingleton (Abelian.Ext
      (ModuleCat.of A (ULift.{max uB uA} M))
      (ModuleCat.of A (ULift.{max uB uA} N)) i) := by
  obtain ⟨e⟩ := flatExtBaseChangeLinearEquiv (R := A) (S := B) M N i
  exact e.toEquiv.subsingleton_congr.symm.trans
    (Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right A B)

private theorem finiteInjectiveDimension_map
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [Limits.PreservesFiniteLimits F]
    [Limits.PreservesFiniteColimits F] [F.PreservesInjectiveObjects]
    {K : DerivedCategory C}
    (hK : StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension K) :
    StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension (F.mapDerivedCategory.obj K) := by
  obtain ⟨a, b, I, hIa, hIb, hI, ⟨e⟩⟩ := hK
  let J : CochainComplex D ℤ := (F.mapHomologicalComplex (.up ℤ)).obj I
  have : J.IsStrictlyGE a := inferInstance
  have : J.IsStrictlyLE b := inferInstance
  refine ⟨a, b, J, inferInstance, inferInstance, ?_, ?_⟩
  · exact fun i => F.injective_obj_of_injective (hI i)
  · exact ⟨F.mapDerivedCategory.mapIso e ≪≫ F.mapDerivedCategoryFactors.app I⟩

private theorem highExt_vanish_of_isGorenstein
    {R : Type uA} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (hR : IsGorensteinLocalRing R) :
    ∃ b : ℤ, ∀ (M : ModuleCat.{max uB uA} R) (i : ℤ), b < i →
      Subsingleton (DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{max uB uA} R) 0).obj M)
        ((DerivedCategory.singleFunctor (ModuleCat.{max uB uA} R) 0).obj
          ((ModuleCat.uliftFunctor.{uB} R).obj (ModuleCat.of R R))) i) := by
  let F := ModuleCat.uliftFunctor.{uB, uA} R
  obtain ⟨a, b, I, hIa, hIb, hI, ⟨e⟩⟩ :=
    finiteInjectiveDimension_map F hR.finiteInjectiveDimension
  have hK : StacksDraft.InjectiveDimension.HasInjectiveAmplitude
      ((DerivedCategory.singleFunctor (ModuleCat.{max uB uA} R) 0).obj
        (F.obj (ModuleCat.of R R))) a b :=
    ⟨I, hIa, hIb, hI, ⟨((F.mapDerivedCategorySingleFunctor 0).app _).symm ≪≫ e⟩⟩
  exact ⟨b, fun M i hi =>
    (StacksDraft.InjectiveDimension.hasInjectiveAmplitude_iff_ext_vanishing_iff_quotient_vanishing
      _ a b).1.mp hK M i (Or.inr hi)⟩

private theorem isGorensteinLocalRing_of_faithfullyFlat
    {A : Type uA} {B : Type uB} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsLocalRing A] [IsLocalRing B]
    [Algebra A B] [Module.FaithfullyFlat A B]
    (hB : IsGorensteinLocalRing B) :
    IsGorensteinLocalRing A := by
  classical
  apply (isGorensteinLocalRing_iff_residueField_ext_vanishing_ulift.{uA,
    max uA uB} A).mpr
  obtain ⟨b, hb⟩ := highExt_vanish_of_isGorenstein.{uB, max uA uB} hB
  refine ⟨max b 0, fun i hi => ?_⟩
  have hi0 : 0 ≤ i := by omega
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hi0
  let M := Shrink.{uA} (A ⧸ maximalIdeal A)
  let SM := ModuleCat.of B (ULift.{max uA uB} (B ⊗[A] M))
  let SN := ModuleCat.of B (ULift.{max uA uB} (B ⊗[A] A))
  let BN := (ModuleCat.uliftFunctor.{max uA uB} B).obj (ModuleCat.of B B)
  let e : SN ≅ BN :=
    ((ULift.moduleEquiv : SN ≃ₗ[B] (B ⊗[A] A)).trans
      ((TensorProduct.AlgebraTensorModule.rid A B B).trans ULift.moduleEquiv.symm)).toModuleIso
  have hBN := hb SM n (by omega)
  have hSN : Subsingleton (Abelian.Ext SM SN n) :=
    (Abelian.Ext.homEquiv.trans
      (Iso.homCongr (Iso.refl _)
        ((shiftFunctor _ (n : ℤ)).mapIso
          ((DerivedCategory.singleFunctor _ 0).mapIso e)))).injective.subsingleton
  have hA := (flatExtVanish_iff_of_faithfullyFlat (A := A) (B := B) M A n).mp hSN
  exact (Abelian.Ext.homEquiv.subsingleton_congr).mp hA

private noncomputable def derivedHomHomologyLinearEquivExt
    {R S : Type uA} [CommRing R] [CommRing S] (q : R →+* S)
    (K : DerivedCategory (ModuleCat.{max uB uA} R)) (i : ℤ) :
    ((ModuleCat.restrictScalars q).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{max uB uA} S) i).obj
        ((derivedHom.{uA, uB} q).obj K))) ≃ₗ[R]
      DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{max uB uA} R) 0).obj
          ((ModuleCat.restrictScalars q).obj (ModuleCat.of S (ULift.{uB} S)))) K i :=
  (derivedCoextendScalarsHomologyLinearEquivExt q
    (derivedHom.{uA, uB} q)
    ((coextendScalarsToDerivedCategory q).totalRightDerivedUnit
      DerivedCategory.Qh (HomotopyCategory.quasiIso (ModuleCat.{max uB uA} R)
        (.up ℤ)))).linearEquiv K i

private lemma negative_ext_subsingleton
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (M N : C) (i : ℤ) (hi : i < 0) :
    Subsingleton (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor C 0).obj M)
      ((DerivedCategory.singleFunctor C 0).obj N) i) := by
  let e := ((DerivedCategory.singleFunctors C).shiftIso i (-i) 0 (by omega)).app N
  refine subsingleton_of_forall_eq 0 (fun f => ?_)
  apply (cancel_mono e.hom).mp
  rw [Limits.zero_comp]
  exact DerivedCategory.TStructure.t.zero (f ≫ e.hom) 0 (-i) (by omega)

private theorem residueField_ext_one_degree
    (R : Type uA) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (hR : IsGorensteinLocalRing R) :
    let k := ModuleCat.of (ResidueField R) (ULift.{0} (ResidueField R))
    let kR := (ModuleCat.restrictScalars (residue R)).obj k
    let K := (DerivedCategory.singleFunctor (ModuleCat.{uA} R) 0).obj (ModuleCat.of R R)
    ∃ d : ℤ,
      Nonempty ((DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{uA} R) 0).obj kR) K d) ≃ₗ[R] kR) ∧
      ∀ i : ℤ, i ≠ d → Subsingleton (DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{uA} R) 0).obj kR) K i) := by
  classical
  dsimp only
  let k := ModuleCat.of (ResidueField R) (ULift.{0} (ResidueField R))
  let K := (DerivedCategory.singleFunctor (ModuleCat.{uA} R) 0).obj (ModuleCat.of R R)
  let D := (derivedHom.{uA, 0} (residue R)).obj K
  let S := (DerivedCategory.singleFunctor (ModuleCat.{uA} (ResidueField R)) 0).obj k
  let H := DerivedCategory.homologyFunctor (ModuleCat.{uA} (ResidueField R))
  let F := ModuleCat.restrictScalars.{uA} (residue R)
  obtain ⟨n, ⟨e⟩⟩ := derivedHom_localResidueField_iso_shift.{uA, 0} K hR
  let eH : (H (-n)).obj D ≅ k :=
    (H (-n)).mapIso e ≪≫ ((H 0).shiftIso n (-n) 0 (add_neg_cancel n)).app S ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app k
  refine ⟨-n, ⟨(derivedHomHomologyLinearEquivExt.{uA, 0} (residue R) K (-n)).symm.trans
    (F.mapIso eH).toLinearEquiv⟩, ?_⟩
  intro i hi
  let eHi : (H i).obj D ≅ (H (n + i)).obj S :=
    (H i).mapIso e ≪≫ ((H 0).shiftIso n i (n + i) rfl).app S
  have hz : Limits.IsZero ((H (n + i)).obj S) := by
    rcases lt_or_gt_of_ne (show n + i ≠ 0 by omega) with h | h
    · exact S.isZero_of_isGE 0 _ h
    · exact S.isZero_of_isLE 0 _ h
  exact (((derivedHomHomologyLinearEquivExt.{uA, 0} (residue R) K i).toEquiv).subsingleton_congr).mp
      (ModuleCat.isZero_iff_subsingleton.mp (F.map_isZero (hz.of_iso eHi)))

private noncomputable def residueFieldBaseChangeLinearEquiv
    (R : Type uA) (S : Type uB) [CommRing R] [CommRing S]
    [IsLocalRing R] [Algebra R S] :
    (S ⊗[R] ((ModuleCat.restrictScalars (residue R)).obj
      (ModuleCat.of (ResidueField R) (ULift.{0} (ResidueField R))))) ≃ₗ[S]
      (S ⧸ (maximalIdeal R).map (algebraMap R S)) :=
  (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S S)
    (ULift.moduleEquiv : ((ModuleCat.restrictScalars (residue R)).obj
      (ModuleCat.of (ResidueField R) (ULift.{0} (ResidueField R)))) ≃ₗ[R]
        (ResidueField R))).trans
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S (maximalIdeal R)).symm.toLinearEquiv

private theorem residueField_ext_baseChange_one_degree
    (R : Type uA) (S : Type uB) [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsLocalRing R] [Algebra R S] [Module.Flat R S]
    (hR : IsGorensteinLocalRing R) :
    let k := (ModuleCat.restrictScalars (residue R)).obj
      (ModuleCat.of (ResidueField R) (ULift.{0} (ResidueField R)))
    ∃ d : ℤ, 0 ≤ d ∧ ∀ n : ℕ,
      let E := Abelian.Ext
        (ModuleCat.of S (ULift.{max uA uB} (S ⊗[R] k)))
        (ModuleCat.of S (ULift.{max uA uB} (S ⊗[R] R))) n
      (↑n = d → Nonempty (E ≃ₗ[S]
        (S ⧸ (maximalIdeal R).map (algebraMap R S)))) ∧
      (↑n ≠ d → Subsingleton E) := by
  classical
  dsimp only
  let k := (ModuleCat.restrictScalars (residue R)).obj
    (ModuleCat.of (ResidueField R) (ULift.{0} (ResidueField R)))
  have hk : Module.Finite R k := by
    change Module.Finite R (ULift.{0} (ResidueField R))
    infer_instance
  let F := ModuleCat.uliftFunctor.{max uA uB, uA} R
  obtain ⟨d, ⟨ed⟩, hd⟩ := residueField_ext_one_degree R hR
  have hd0 : 0 ≤ d := by
    by_contra h
    have hz := negative_ext_subsingleton k (ModuleCat.of R R) d (by omega)
    have hz' : Subsingleton k := ed.symm.injective.subsingleton
    exact (zero_ne_one : (0 : ResidueField R) ≠ 1)
      (congrArg ULift.down (hz'.elim (ULift.up 0) (ULift.up 1)))
  refine ⟨d, hd0, fun n => ?_⟩
  let eLift := (LinearEquiv.ofBijective
    (F.mapExtLinearMap R k (ModuleCat.of R R) n)
    (Functor.mapExt_bijective_of_preservesProjectiveObjects F k (ModuleCat.of R R) n)).symm
  let e := eLift.trans (Abelian.Ext.homLinearEquiv (R := R))
  obtain ⟨eBase⟩ := flatExtBaseChangeLinearEquiv (R := R) (S := S) k R n
  constructor
  · intro hn
    subst hn
    exact ⟨eBase.symm.trans
      ((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S S) (e.trans ed)).trans
        (residueFieldBaseChangeLinearEquiv R S))⟩
  · intro hn
    have hsmall := hd n hn
    have hlarge := e.injective.subsingleton
    have htensor : Subsingleton (S ⊗[R] Abelian.Ext (F.obj k) (F.obj (ModuleCat.of R R)) n) :=
      inferInstance
    exact eBase.toEquiv.subsingleton_congr.mp htensor

private noncomputable def quotientModuleIsoOfRestrictScalars
    {R : Type uA} [CommRing R] (I : Ideal R)
    (M N : ModuleCat.{max uB uA} (R ⧸ I))
    (e : ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj M) ≃ₗ[R]
      ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj N)) : M ≅ N := by
  let f : M ≃ₗ[R ⧸ I] N :=
    { __ := e.toAddEquiv
      map_smul' := by
        intro a m
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
        exact e.map_smul r m }
  exact f.toModuleIso

private noncomputable def closedFibreExtLinearEquiv
    (R : Type uA) (S : Type uB) [CommRing R] [CommRing S]
    [IsLocalRing R] [Algebra R S] (n : ℕ) :
    let F := S ⧸ (maximalIdeal R).map (algebraMap R S)
    let q := Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R S))
    let k := (ModuleCat.restrictScalars (residue R)).obj
      (ModuleCat.of (ResidueField R) (ULift.{0} (ResidueField R)))
    DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{max uA uB} S) 0).obj
        ((ModuleCat.restrictScalars q).obj (ModuleCat.of F (ULift.{max uA uB} F))))
      ((DerivedCategory.singleFunctor (ModuleCat.{max uA uB} S) 0).obj
        (ModuleCat.of S (ULift.{max uA uB} S))) n ≃ₗ[S]
      Abelian.Ext
        (ModuleCat.of S (ULift.{max uA uB} (S ⊗[R] k)))
        (ModuleCat.of S (ULift.{max uA uB} (S ⊗[R] R))) n := by
  dsimp only
  let F := S ⧸ (maximalIdeal R).map (algebraMap R S)
  let q := Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R S))
  let k := (ModuleCat.restrictScalars (residue R)).obj
    (ModuleCat.of (ResidueField R) (ULift.{0} (ResidueField R)))
  let eM : ModuleCat.of S (ULift.{max uA uB} (S ⊗[R] k)) ≅
      (ModuleCat.restrictScalars q).obj (ModuleCat.of F (ULift.{max uA uB} F)) :=
    ((ULift.moduleEquiv : ULift.{max uA uB} (S ⊗[R] k) ≃ₗ[S] (S ⊗[R] k)).trans
      ((residueFieldBaseChangeLinearEquiv R S).trans ULift.moduleEquiv.symm)).toModuleIso
  let eN : ModuleCat.of S (ULift.{max uA uB} (S ⊗[R] R)) ≅
      ModuleCat.of S (ULift.{max uA uB} S) :=
    ((ULift.moduleEquiv : ULift.{max uA uB} (S ⊗[R] R) ≃ₗ[S] (S ⊗[R] R)).trans
      ((TensorProduct.AlgebraTensorModule.rid R S S).trans ULift.moduleEquiv.symm)).toModuleIso
  exact (Linear.homCongr S
    ((DerivedCategory.singleFunctor _ 0).mapIso eM.symm)
    ((shiftFunctor _ (n : ℤ)).mapIso ((DerivedCategory.singleFunctor _ 0).mapIso eN.symm))).trans
      Abelian.Ext.homLinearEquiv.symm

private theorem derivedHom_closedFibre_iso_single
    (R : Type uA) (S : Type uB) [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsLocalRing R] [Algebra R S] [Module.Flat R S]
    (hR : IsGorensteinLocalRing R) :
    let F := S ⧸ (maximalIdeal R).map (algebraMap R S)
    let q := Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R S))
    ∃ d : ℤ, Nonempty
      ((derivedHom.{uB, max uA uB} q).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{max uA uB} S) 0).obj
          (ModuleCat.of S (ULift.{max uA uB} S))) ≅
        (DerivedCategory.singleFunctor (ModuleCat.{max uA uB} F) d).obj
          (ModuleCat.of F (ULift.{max uA uB} F))) := by
  classical
  dsimp only
  let I := (maximalIdeal R).map (algebraMap R S)
  let F := S ⧸ I
  let q := Ideal.Quotient.mk I
  let T := ModuleCat.restrictScalars.{max uA uB} q
  let K := (DerivedCategory.singleFunctor (ModuleCat.{max uA uB} S) 0).obj
    (ModuleCat.of S (ULift.{max uA uB} S))
  let D := (derivedHom.{uB, max uA uB} q).obj K
  let H := DerivedCategory.homologyFunctor (ModuleCat.{max uA uB} F)
  let U := ModuleCat.of F (ULift.{max uA uB} F)
  obtain ⟨d, hd0, hd⟩ := residueField_ext_baseChange_one_degree R S hR
  let c (i : ℤ) := derivedHomHomologyLinearEquivExt.{uB, max uA uB} q K i
  have hzero (i : ℤ) (hi : i ≠ d) : Limits.IsZero ((H i).obj D) := by
    apply ModuleCat.isZero_iff_subsingleton.mpr
    change Subsingleton (T.obj ((H i).obj D))
    by_cases hi0 : 0 ≤ i
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hi0
      have hz := (hd n).2 hi
      exact ((c n).trans (closedFibreExtLinearEquiv R S n)).injective.subsingleton
    · have hz := negative_ext_subsingleton (T.obj U)
        (ModuleCat.of S (ULift.{max uA uB} S)) i (by omega)
      exact (c i).injective.subsingleton
  have hGE : D.IsGE d := (DerivedCategory.isGE_iff D d).mpr
    (fun i hi => hzero i (by omega))
  have hLE : D.IsLE d := (DerivedCategory.isLE_iff D d).mpr
    (fun i hi => hzero i (by omega))
  have eH : Nonempty ((H d).obj D ≅ U) := by
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hd0
    obtain ⟨e⟩ := (hd n).1 rfl
    let e' : T.obj ((H (n : ℤ)).obj D) ≃ₗ[S] T.obj U :=
      ((c n).trans (closedFibreExtLinearEquiv R S n)).trans
        (e.trans ULift.moduleEquiv.symm)
    exact ⟨quotientModuleIsoOfRestrictScalars I _ _ e'⟩
  obtain ⟨eH⟩ := eH
  obtain ⟨W, ⟨eW⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE D d
  let eWH : (H d).obj D ≅ W := (H d).mapIso eW ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso _ d).app W
  exact ⟨d, ⟨eW ≪≫ (DerivedCategory.singleFunctor _ d).mapIso (eWH.symm ≪≫ eH)⟩⟩

private noncomputable def closedFibreDerivedExtEquiv
    {R : Type uA} [CommRing R] (I : Ideal R) (d : ℤ)
    (e : (derivedHom.{uA, uB} (Ideal.Quotient.mk I)).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{max uB uA} R) 0).obj
          (ModuleCat.of R (ULift.{uB} R))) ≅
        (DerivedCategory.singleFunctor (ModuleCat.{max uB uA} (R ⧸ I)) d).obj
          (ModuleCat.of (R ⧸ I) (ULift.{uB} (R ⧸ I))))
    (M : ModuleCat.{max uB uA} (R ⧸ I)) (i : ℤ) :
    DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{max uB uA} R) 0).obj
        ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj M))
      ((DerivedCategory.singleFunctor (ModuleCat.{max uB uA} R) 0).obj
        (ModuleCat.of R (ULift.{uB} R))) i ≃
    DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{max uB uA} (R ⧸ I)) 0).obj M)
      ((DerivedCategory.singleFunctor (ModuleCat.{max uB uA} (R ⧸ I)) 0).obj
        (ModuleCat.of (R ⧸ I) (ULift.{uB} (R ⧸ I)))) (i - d) := by
  let q := Ideal.Quotient.mk I
  let T := ModuleCat.restrictScalars.{max uB uA} q
  let K := (DerivedCategory.singleFunctor (ModuleCat.{max uB uA} R) 0).obj
    (ModuleCat.of R (ULift.{uB} R))
  let U := ModuleCat.of (R ⧸ I) (ULift.{uB} (R ⧸ I))
  let X := (DerivedCategory.singleFunctor (ModuleCat.{max uB uA} (R ⧸ I)) 0).obj M
  let Y := (DerivedCategory.singleFunctor (ModuleCat.{max uB uA} (R ⧸ I)) 0).obj U
  let eD : (derivedHom.{uA, uB} q).obj K ≅ Y⟦-d⟧ :=
    e ≪≫ (((DerivedCategory.singleFunctors (ModuleCat.{max uB uA} (R ⧸ I))).shiftIso
      (-d) d 0 (by omega)).app U).symm
  let eShift := (shiftFunctor _ i).mapIso eD ≪≫
    ((shiftFunctorAdd' _ (-d) i (i - d) (by omega)).app Y).symm
  exact (Iso.homCongr ((T.mapDerivedCategorySingleFunctor 0).app M).symm (Iso.refl _)).trans
    ((derivedExtAdjunctionEquiv.{uA, uA, uB} q X K i).trans
      (Iso.homCongr (Iso.refl X) eShift))

private theorem isGorensteinLocalRing_iff_quotient_of_derivedHom_iso_single
    {R : Type uA} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (I : Ideal R) [IsLocalRing (R ⧸ I)]
    (d : ℤ)
    (e : (derivedHom.{uA, uB} (Ideal.Quotient.mk I)).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{max uB uA} R) 0).obj
          (ModuleCat.of R (ULift.{uB} R))) ≅
        (DerivedCategory.singleFunctor (ModuleCat.{max uB uA} (R ⧸ I)) d).obj
          (ModuleCat.of (R ⧸ I) (ULift.{uB} (R ⧸ I)))) :
    IsGorensteinLocalRing R ↔ IsGorensteinLocalRing (R ⧸ I) := by
  classical
  let F := R ⧸ I
  let q := Ideal.Quotient.mk I
  let T := ModuleCat.restrictScalars.{max uB uA} q
  constructor
  · intro hR
    apply (isGorensteinLocalRing_iff_residueField_ext_vanishing_ulift.{uA, uB} F).mpr
    obtain ⟨b, hb⟩ := highExt_vanish_of_isGorenstein.{uA, uB} hR
    refine ⟨b - d, fun i hi => ?_⟩
    let M := (ModuleCat.uliftFunctor.{uB} F).obj
      (ModuleCat.of F (Shrink.{uA} (F ⧸ maximalIdeal F)))
    have hz := hb (T.obj M) (i + d) (by omega)
    have hz' := ((closedFibreDerivedExtEquiv I d e M (i + d)).subsingleton_congr).mp hz
    change Subsingleton (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{max uB uA} F) 0).obj M)
      ((DerivedCategory.singleFunctor (ModuleCat.{max uB uA} F) 0).obj
        (ModuleCat.of F (ULift.{uB} F))) i)
    simpa only [add_sub_cancel_right] using hz'
  · intro hF
    apply (isGorensteinLocalRing_iff_residueField_ext_vanishing_ulift.{uA, uB} R).mpr
    obtain ⟨b, hb⟩ := highExt_vanish_of_isGorenstein.{uA, uB} hF
    have hI : I ≤ maximalIdeal R := le_maximalIdeal
      (Ideal.Quotient.nontrivial_iff.mp inferInstance)
    let g : F →+* ResidueField R := Ideal.Quotient.lift I (residue R)
      (fun x hx => (residue_eq_zero_iff x).mpr (hI hx))
    let M : ModuleCat.{max uB uA} F := (ModuleCat.restrictScalars g).obj
      (ModuleCat.of (ResidueField R) (ULift.{uB} (ResidueField R)))
    let kR := (ModuleCat.uliftFunctor.{uB} R).obj
      (ModuleCat.of R (Shrink.{uA} (R ⧸ maximalIdeal R)))
    let ek : kR ≅ T.obj M :=
      ((ULift.moduleEquiv : kR ≃ₗ[R] Shrink.{uA} (R ⧸ maximalIdeal R)).trans
        ((Shrink.linearEquiv R (R ⧸ maximalIdeal R)).trans ULift.moduleEquiv.symm)).toModuleIso
    refine ⟨b + d, fun i hi => ?_⟩
    have hz := hb M (i - d) (by omega)
    have hz' := ((closedFibreDerivedExtEquiv I d e M i).subsingleton_congr).mpr hz
    exact ((Iso.homCongr ((DerivedCategory.singleFunctor _ 0).mapIso ek)
        (Iso.refl _)).subsingleton_congr).mpr hz'

universe u v

/-- For a flat local homomorphism of Noetherian local rings, the target is Gorenstein if and only
if the source and the closed fibre are Gorenstein. -/
@[stacks 0BJL]
public theorem isGorensteinLocalRing_iff_of_flat
    (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsLocalRing A] [IsLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Flat A B] :
    let I := (maximalIdeal A).map (algebraMap A B)
    let _ : Nontrivial (B ⧸ I) :=
      Ideal.Quotient.nontrivial_iff.mpr
        (IsLocalRing.map_maximalIdeal_lt_top (algebraMap A B)).ne
    let _ : IsLocalHom (Ideal.Quotient.mk I) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    let _ : IsLocalRing (B ⧸ I) :=
      IsLocalRing.of_surjective _ Ideal.Quotient.mk_surjective
    IsGorensteinLocalRing B ↔
      (IsGorensteinLocalRing A ∧
        IsGorensteinLocalRing (B ⧸ I)) := by
  intro I hnontrivial hlocalhom hlocal
  have : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  suffices hfibre : IsGorensteinLocalRing A →
      (IsGorensteinLocalRing B ↔
        IsGorensteinLocalRing
          (B ⧸ (maximalIdeal A).map (algebraMap A B))) by
    refine ⟨fun hB => ?_, fun ⟨hA, hF⟩ => (hfibre hA).mpr hF⟩
    have hA := isGorensteinLocalRing_of_faithfullyFlat (A := A) hB
    exact ⟨hA, (hfibre hA).mp hB⟩
  intro hA
  obtain ⟨d, ⟨e⟩⟩ := derivedHom_closedFibre_iso_single A B hA
  exact isGorensteinLocalRing_iff_quotient_of_derivedHom_iso_single I d e

/-- A Noetherian local ring isomorphic to a Gorenstein local ring, possibly in another universe,
is Gorenstein. -/
public theorem isGorensteinLocalRing_of_ringEquiv
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsNoetherianRing S] [IsLocalRing R] [IsLocalRing S]
    (e : R ≃+* S) (hS : IsGorensteinLocalRing S) : IsGorensteinLocalRing R := by
  let := e.toRingHom.toAlgebra
  let : IsLocalHom (algebraMap R S) :=
    IsLocalHom.of_surjective _ e.surjective
  let : Module.Flat R S := RingHom.Flat.of_bijective e.bijective
  exact ((isGorensteinLocalRing_iff_of_flat R S).mp hS).1

end Dualizing

end
