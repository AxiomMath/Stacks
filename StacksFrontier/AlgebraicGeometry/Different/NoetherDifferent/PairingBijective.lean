module

public import Mathlib.RingTheory.Etale.QuasiFinite
public import Mathlib.RingTheory.LocalProperties.Basic
public import Mathlib.RingTheory.Smooth.Flat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Discriminant.FactorizationRefinement
public import StacksFrontier.AlgebraicGeometry.Discriminant.NoetherPairingFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Discriminant.TargetLocalization
public import StacksFrontier.AlgebraicGeometry.Different.DualizingModulesQuasi.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Different.NoetherDifferent.PairingFiniteProjective
public import StacksFrontier.RingTheory.Different.PairingBaseChange

/-!
# The Noether pairing of a flat quasi-finite algebra is perfect

For a flat quasi-finite homomorphism of Noetherian rings, the canonical pairing identifies the
annihilator of the diagonal ideal with the dual of the relative dualizing module.

The statement is local on the target and stable under flat base change of the source, so it
reduces to the case of an algebra which is finite projective over its base, where the pairing is
plain contraction. The reduction uses the étale local structure of a quasi-finite algebra: after
an étale base change and an away localization of the target, the algebra becomes finite over the
new base.

## Main definitions

* `Stacks.Discriminant.specMap_ulift_isOpenImmersion_localizationAway`: an away localization
  induces an open immersion on spectra.
* `Stacks.Discriminant.diagonalAnnihilatorScalarExtension` is the map on diagonal annihilators
  induced by a flat base change of the source, as a map of modules over the target.
* `Stacks.Discriminant.noetherPairingEquiv` is the linear equivalence induced by the pairing.

## Main results

* `Stacks.Discriminant.diagonalAnnihilatorScalarExtension_isBaseChange`: the diagonal
  annihilator commutes with flat base change of the source.
* `Stacks.Discriminant.noetherPairing_flip_bijective`: **Stacks Project, Tag 0BVS**, the map
  induced by the canonical pairing is bijective.

## Implementation notes

Both reductions are instances of
`Stacks.Discriminant.pairing_flip_baseChange_bijective_iff`, which needs the two sides of the
pairing to be base changes of one another. On the dualizing side this is Tag 0BT3; on the
annihilator side it is `diagonalAnnihilatorScalarExtension_isBaseChange` for a base change of
the source and `Stacks.Discriminant.diagonalAnnihilatorTargetEquiv` for a localization of the
target.

## References

* [Stacks Project, Tag 0BVS](https://stacks.math.columbia.edu/tag/0BVS)
-/

@[expose] public section

open scoped TensorProduct
open AlgebraicGeometry CategoryTheory

namespace Stacks.Discriminant

universe u v w x

attribute [local instance] algebraDualModule

/-- An away localization induces an open immersion on spectra, after lifting both rings to a
common universe. -/
theorem specMap_ulift_isOpenImmersion_localizationAway {B Bg : Type v}
    [CommRing B] [CommRing Bg] [Algebra B Bg] (g : B) [IsLocalization.Away g Bg] :
    IsOpenImmersion (Spec.map
      (CommRingCat.ofHom (RingHom.ulift.{v, v} (algebraMap B Bg)))) := by
  let uB : ULift.{v} B ≃+* B := ULift.ringEquiv
  let uC : ULift.{v} Bg ≃+* Bg := ULift.ringEquiv
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B Bg))) :=
    IsOpenImmersion.of_isLocalization g
  have : IsIso (CommRingCat.ofHom uB.toRingHom) := uB.toCommRingCatIso.isIso_hom
  have : IsIso (CommRingCat.ofHom uC.symm.toRingHom) := uC.symm.toCommRingCatIso.isIso_hom
  have heq : RingHom.ulift.{v, v} (algebraMap B Bg) =
      uC.symm.toRingHom.comp ((algebraMap B Bg).comp uB.toRingHom) := by
    ext x
    rfl
  rw [heq, CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_comp, Spec.map_comp]
  infer_instance

/-- Multiplying an element of the diagonal annihilator by a tensor is multiplying it by the
image of that tensor under the multiplication map. -/
private lemma mul_mem_diagonalAnnihilator
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (z : B ⊗[A] B) (j : ↑(diagonalAnnihilator A B)) :
    z * j.1 = (Algebra.TensorProduct.lmul' A z) • j.1 := by
  let d := z - (Algebra.TensorProduct.lmul' A z) ⊗ₜ[A] (1 : B)
  have hd : d ∈ RingHom.ker (Algebra.TensorProduct.lmul' A).toRingHom := by
    show (Algebra.TensorProduct.lmul' A) d = 0
    simp [d]
  have hz := Submodule.mem_annihilator.mp j.2 d hd
  have h : z * j.1 = ((Algebra.TensorProduct.lmul' A z) ⊗ₜ[A] (1 : B)) * j.1 := by
    apply sub_eq_zero.mp
    simpa [d, mul_sub, sub_mul, mul_comm] using hz
  rw [h]
  induction j.1 using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [mul_add, smul_add, hx, hy]
  | tmul b c => simp [TensorProduct.smul_tmul', smul_eq_mul]

section DiagonalBaseChange

variable (A : Type u) (B : Type v) (S : Type w)
  [CommRing A] [CommRing B] [CommRing S] [Algebra A B] [Algebra A S]
  [Algebra.FiniteType A B] [Module.Flat A S]

/-- The map on diagonal annihilators induced by a flat base change of the source, as a map of
modules over the target. -/
def diagonalAnnihilatorScalarExtension :
    letI : Algebra B (S ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
    ↑(diagonalAnnihilator A B) →ₗ[B] ↑(diagonalAnnihilator S (S ⊗[A] B)) := by
  letI : Algebra B (S ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  refine
    { toFun := diagonalAnnihilatorFlatBaseChange A B S
      map_add' := fun x y => Subtype.ext (map_add (envelopingBaseChange A B S) x.1 y.1)
      map_smul' := fun b j => Subtype.ext ?_ }
  change envelopingBaseChange A B S (b • j.1) =
    (algebraMap B (S ⊗[A] B) b) • envelopingBaseChange A B S j.1
  induction j.1 using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [smul_add, hx, hy]
  | tmul x y =>
      have hb : b • (x ⊗ₜ[A] y) = (b * x) ⊗ₜ[A] y := rfl
      rw [hb, envelopingBaseChange_tmul, envelopingBaseChange_tmul,
        TensorProduct.smul_tmul']
      congr 1
      simp [Algebra.TensorProduct.right_algebraMap_apply,
        Algebra.TensorProduct.tmul_mul_tmul]

omit [Algebra.FiniteType A B] [Module.Flat A S] in
/-- The scalar extension of the enveloping algebra along a flat base change of the source. -/
noncomputable def envelopingScalarExtensionEquiv :
    S ⊗[A] (B ⊗[A] B) ≃ₐ[S] ((S ⊗[A] B) ⊗[S] (S ⊗[A] B)) :=
  (Algebra.TensorProduct.assoc A A S S B B).symm.trans
    (Algebra.TensorProduct.cancelBaseChange A S S (S ⊗[A] B) B).symm

omit [Algebra.FiniteType A B] [Module.Flat A S] in
/-- The scalar extension of the enveloping algebra on a pure tensor. -/
lemma envelopingScalarExtensionEquiv_tmul (s : S) (z : B ⊗[A] B) :
    envelopingScalarExtensionEquiv A B S (s ⊗ₜ[A] z) =
      s • envelopingBaseChange A B S z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [TensorProduct.tmul_add, hx, hy, smul_add]
  | tmul b c =>
      rw [envelopingBaseChange_tmul]
      simp [envelopingScalarExtensionEquiv, Algebra.TensorProduct.assoc_symm_tmul,
        Algebra.TensorProduct.cancelBaseChange_symm_tmul, TensorProduct.smul_tmul']

/-- The diagonal annihilator commutes with a flat base change of the source. -/
theorem diagonalAnnihilatorScalarExtension_isBaseChange :
    letI : Algebra B (S ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
    IsBaseChange (S ⊗[A] B) (diagonalAnnihilatorScalarExtension A B S) := by
  let _ : Algebra B (S ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  let J := diagonalAnnihilator A B
  let f := LinearMap.liftBaseChange (S ⊗[A] B) (diagonalAnnihilatorScalarExtension A B S)
  let e := Algebra.IsPushout.cancelBaseChange A S B (S ⊗[A] B) ↑J
  let t := envelopingScalarExtensionEquiv A B S
  have he (s : S) (j : ↑J) :
      (f (e.symm (s ⊗ₜ[A] j))).1 =
        t ((J.subtype.restrictScalars A).lTensor S (s ⊗ₜ[A] j)) := by
    simp only [e, f, Algebra.IsPushout.cancelBaseChange_symm_tmul,
      envelopingScalarExtensionEquiv_tmul, t, LinearMap.liftBaseChange_tmul,
      diagonalAnnihilatorScalarExtension, LinearMap.lTensor_tmul,
      LinearMap.coe_restrictScalars, Submodule.subtype_apply]
    exact IsScalarTower.algebraMap_smul (S ⊗[A] B) s _
  have hz0 : e.symm 0 = 0 := map_zero e.symm
  have hzadd : ∀ x y, e.symm (x + y) = e.symm x + e.symm y := fun x y => map_add e.symm x y
  have ht0 : t 0 = 0 := map_zero t
  have htadd : ∀ x y, t (x + y) = t x + t y := fun x y => map_add t x y
  have he' (z : S ⊗[A] ↑J) :
      (f (e.symm z)).1 = t ((J.subtype.restrictScalars A).lTensor S z) := by
    induction z using TensorProduct.induction_on with
    | zero => rw [hz0, map_zero, ZeroMemClass.coe_zero, map_zero, ht0]
    | tmul s j => exact he s j
    | add x y hx hy =>
        rw [hzadd, map_add, AddMemClass.coe_add, hx, hy, map_add, htadd]
  have hinj : Function.Injective f := by
    intro x y hxy
    apply e.injective
    apply Module.Flat.lTensor_preserves_injective_linearMap
      (M := S) (J.subtype.restrictScalars A) Subtype.val_injective
    apply t.injective
    rw [← he', ← he', e.symm_apply_apply, e.symm_apply_apply]
    exact congrArg Subtype.val hxy
  have hsurj : Function.Surjective f := by
    intro j
    have hj : j.1 ∈ J.map (envelopingBaseChange A B S) := by
      rw [map_diagonalAnnihilator_eq]
      exact j.2
    have hr : ∀ z ∈ J.map (envelopingBaseChange A B S), ∃ x, (f x).1 = z := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
          obtain ⟨j, hj, rfl⟩ := hz
          exact ⟨1 ⊗ₜ[B] ⟨j, hj⟩, by
            simp [f, diagonalAnnihilatorScalarExtension, diagonalAnnihilatorFlatBaseChange]⟩
      | zero => exact ⟨0, by simp⟩
      | add x y hx hy ihx ihy =>
          obtain ⟨a, rfl⟩ := ihx
          obtain ⟨b, rfl⟩ := ihy
          exact ⟨a + b, by simp⟩
      | smul r z hz ih =>
          obtain ⟨x, rfl⟩ := ih
          exact ⟨(Algebra.TensorProduct.lmul' S r) • x, by
            simpa using (mul_mem_diagonalAnnihilator r (f x)).symm⟩
    obtain ⟨x, hx⟩ := hr j.1 hj
    exact ⟨x, Subtype.ext hx⟩
  exact IsBaseChange.of_equiv (LinearEquiv.ofBijective f ⟨hinj, hsurj⟩) fun j =>
    (LinearMap.liftBaseChange_tmul (S ⊗[A] B)
      (diagonalAnnihilatorScalarExtension A B S) 1 j).trans (one_smul _ _)

end DiagonalBaseChange

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- The dualizing module of a finite open factorization is finitely presented over the target. -/
private theorem dualizingModule_finitePresentation
    [IsNoetherianRing A] [IsNoetherianRing B] [Algebra.FiniteType A B]
    (F : FiniteOpenFactorization.{u, v, w} A B) :
    Module.FinitePresentation B (dualizingModule F) := by
  have : Module.Finite B (dualizingModule F) := dualizingModule_finite F
  exact Module.finitePresentation_of_finite B _

/-- The base change `S ⊗[A] B` of a flat `A`-algebra `S` is flat over `B`, for the right algebra
structure. -/
private theorem flat_tensor_rightAlgebra (A : Type u) (B : Type v) (S : Type*)
    [CommRing A] [CommRing B] [CommRing S] [Algebra A B] [Algebra A S] [Module.Flat A S] :
    letI : Algebra B (S ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
    Module.Flat B (S ⊗[A] B) := by
  let _ : Algebra B (S ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  let e : (S ⊗[A] B) ≃ₐ[B] B ⊗[A] S :=
    AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm A S B).toRingEquiv) (by
      intro b
      simp [Algebra.TensorProduct.right_algebraMap_apply])
  exact Module.Flat.of_linearEquiv e.toLinearEquiv

/-- The map induced by the canonical pairing becomes bijective after a flat base change of the
source exactly when the pairing of the base-changed algebra induces a bijection. -/
theorem noetherPairing_flip_baseChange_bijective_iff
    [IsNoetherianRing A] [IsNoetherianRing B] [Algebra.FiniteType A B]
    (F : FiniteOpenFactorization.{u, v, w} A B)
    (S : Type*) [CommRing S] [Algebra A S] [Module.Flat A S] :
    letI : Algebra B (S ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
    Function.Bijective ((noetherPairing F).flip.baseChange (S ⊗[A] B)) ↔
      Function.Bijective (noetherPairing (FiniteOpenFactorization.baseChange F S)).flip := by
  let _ : Algebra B (S ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  let F' := FiniteOpenFactorization.baseChange F S
  let _ : Module B (dualizingModule F') := Module.compHom _ (algebraMap B (S ⊗[A] B))
  let _ : IsScalarTower B (S ⊗[A] B) (dualizingModule F') :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  have : Module.Flat B (S ⊗[A] B) := flat_tensor_rightAlgebra A B S
  have := dualizingModule_finitePresentation F
  exact pairing_flip_baseChange_bijective_iff (noetherPairing F) (noetherPairing F')
    (dualizingModule.baseChange F S) (diagonalAnnihilatorScalarExtension A B S)
    (dualizingModule_isBaseChange_of_flat F S)
    (diagonalAnnihilatorScalarExtension_isBaseChange A B S) fun ω j =>
      noetherPairing_baseChange S F ω j

/-- The map induced by the canonical pairing becomes bijective after an away localization of the
target exactly when the pairing of the localized algebra induces a bijection. -/
theorem noetherPairing_flip_baseChange_bijective_iff_away
    [IsNoetherianRing A] [IsNoetherianRing B]
    [Algebra.QuasiFinite A B] [Algebra.FiniteType A B]
    (g : B) (F : FiniteOpenFactorization.{u, v, x} A B) :
    letI : Algebra A (Localization.Away g) := inferInstance
    letI : IsScalarTower A B (Localization.Away g) := IsScalarTower.of_algebraMap_eq' rfl
    Function.Bijective ((noetherPairing F).flip.baseChange (Localization.Away g)) ↔
      Function.Bijective
        (noetherPairing (locFact (Bg := Localization.Away g) g F)).flip := by
  let C := Localization.Away g
  let _ : Algebra A C := inferInstance
  let _ : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq' rfl
  let G := locFact (Bg := C) g F
  let _ : Module B (dualizingModule G) := Module.compHom _ (algebraMap B C)
  let _ : IsScalarTower B C (dualizingModule G) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let localizationMap : dualizingModule F →ₗ[B] C ⊗[B] dualizingModule F :=
    TensorProduct.mk B C _ 1
  let eω := localizedModule_dualizingModule_equiv g F G
    localizationMap (inferInstance : IsLocalizedModule (Submonoid.powers g) localizationMap)
  let i : dualizingModule F →ₗ[B] dualizingModule G :=
    (eω.toLinearMap.restrictScalars B).comp localizationMap
  have hi : IsBaseChange C i := IsBaseChange.of_equiv eω fun _ => rfl
  have hopen := specMap_ulift_isOpenImmersion_localizationAway (B := B) (Bg := C) g
  let eJC := diagonalAnnihilatorTargetEquiv A B C hopen
  let jmap : ↑(diagonalAnnihilator A B) →ₗ[B] ↑(diagonalAnnihilator A C) :=
    (eJC.toLinearMap.restrictScalars B).comp
      (TensorProduct.mk B C ↑(diagonalAnnihilator A B) 1)
  have hjmap : IsBaseChange C jmap := IsBaseChange.of_equiv eJC fun _ => rfl
  have := dualizingModule_finitePresentation F
  refine pairing_flip_baseChange_bijective_iff
    (noetherPairing F) (noetherPairing G) i jmap hi hjmap fun ω j₀ => ?_
  let eJ := diagonalAnnihilatorBaseChangeEquiv F
  have headd : ∀ z t, eJ (z + t) = eJ z + eJ t := fun z t => eJ.map_add z t
  induction ω using dualizingModule.induction_on generalizing j₀ with
  | zero => simp
  | add ω η hω hη => simp [hω, hη]
  | tmul f y₀ =>
      obtain ⟨z, rfl⟩ := eJ.surjective j₀
      induction z using TensorProduct.inductionOn with
      | add z t hz ht => rw [headd, map_add, map_add, map_add, map_add, hz, ht]
      | tmul y j' =>
          have hi' : i (dualizingModule.tmul F f y₀) =
              dualizingModule.tmul G f (algebraMap B C y₀) := by
            have h := localizedModule_dualizingModule_equiv_tmul g F G localizationMap
              (inferInstance : IsLocalizedModule (Submonoid.powers g) localizationMap)
              (AlgEquiv.refl : G.middle ≃ₐ[A] F.middle) (fun _ => rfl) f y₀
            show eω (localizationMap (dualizingModule.tmul F f y₀)) = _
            convert h using 1
            congr 1
          have hF : (eJ (y ⊗ₜ[F.middle] j') : B ⊗[A] B) =
              diagonalAnnihilatorBaseChange A F.middle B (y ⊗ₜ[F.middle] j') := rfl
          have hJ : (jmap (eJ (y ⊗ₜ[F.middle] j')) : C ⊗[A] C) =
              diagonalAnnihilatorBaseChange A F.middle C
                ((algebraMap B C y) ⊗ₜ[F.middle] j') := by
            show diagonalAnnihilatorBaseChange A B C
              (1 ⊗ₜ[B] eJ (y ⊗ₜ[F.middle] j')) = _
            simp only [diagonalAnnihilatorBaseChange,
              TensorProduct.AlgebraTensorModule.lift_tmul,
              LinearMap.toSpanSingleton_apply, one_smul]
            show Algebra.TensorProduct.map (IsScalarTower.toAlgHom A B C)
              (IsScalarTower.toAlgHom A B C) (eJ (y ⊗ₜ[F.middle] j') : B ⊗[A] B) = _
            rw [hF]
            simp only [diagonalAnnihilatorBaseChange,
              TensorProduct.AlgebraTensorModule.lift_tmul,
              LinearMap.toSpanSingleton_apply]
            have hcomp : ∀ z : F.middle ⊗[A] F.middle,
                Algebra.TensorProduct.map (IsScalarTower.toAlgHom A B C)
                    (IsScalarTower.toAlgHom A B C)
                  (y • Algebra.TensorProduct.map (IsScalarTower.toAlgHom A F.middle B)
                    (IsScalarTower.toAlgHom A F.middle B) z) =
                  algebraMap B C y • Algebra.TensorProduct.map
                    (IsScalarTower.toAlgHom A F.middle C)
                    (IsScalarTower.toAlgHom A F.middle C) z := by
              intro z
              induction z using TensorProduct.induction_on with
              | zero => simp
              | add z t hz ht => simpa only [map_add, smul_add] using congrArg₂ (· + ·) hz ht
              | tmul a b =>
                  simp [Algebra.TensorProduct.map_tmul, Algebra.smul_def]
                  rfl
            exact hcomp j'.1
          rw [hi', noetherPairing_apply_of_eq_baseChange G f
            (algebraMap B C y₀) (algebraMap B C y) j' _ hJ,
            noetherPairing_apply_of_eq_baseChange F f y₀ y j' _ hF]
          simp [G, locFact, map_mul]
          rfl

/-- **Stacks Project, Tag 0BVS.** For a flat quasi-finite homomorphism of Noetherian rings the
canonical pairing induces a bijection from the annihilator of the diagonal ideal to the dual of
the relative dualizing module. -/
@[stacks 0BVS]
theorem noetherPairing_flip_bijective
    [IsNoetherianRing A] [IsNoetherianRing B]
    [Module.Flat A B] [Algebra.QuasiFinite A B]
    (F : FiniteOpenFactorization.{u, v, w} A B) :
    Function.Bijective (noetherPairing F).flip := by
  apply bijective_of_localized_maximal
  intro q hq
  let p : Ideal A := q.comap (algebraMap A B)
  have : p.IsPrime := Ideal.IsPrime.comap (algebraMap A B)
  have : q.LiesOver p := ⟨rfl⟩
  have : Algebra.FiniteType A B := finiteType_of_finiteOpenFactorization F
  obtain ⟨S, instS, algS, etaleS, P, hP, hPp, e, he, Q, hQ, hQP,
      hQq, heQ, hres, hfinite, hunique⟩ :=
    Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq p q
  have : Algebra.FiniteType A S := inferInstance
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing A S
  have : Module.Flat A S := Algebra.Smooth.flat A S
  have hbranch := noetherPairing_flip_bijective_selfFactorization_baseChange_away
    (A := A) (B := B) e hfinite
  let _ : Algebra B (S ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  have : Module.Flat B (S ⊗[A] B) := flat_tensor_rightAlgebra A B S
  have : Q.LiesOver q := ⟨hQq.symm⟩
  let C := Localization.Away e
  let QC : Ideal C := Q.map (algebraMap (S ⊗[A] B) C)
  have hdis : Disjoint (Submonoid.powers e : Set (S ⊗[A] B)) (Q : Set (S ⊗[A] B)) := by
    rwa [Ideal.disjoint_powers_iff_notMem_of_isPrime]
  have : QC.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint
    (Submonoid.powers e) C Q inferInstance hdis
  have : QC.LiesOver Q :=
    IsLocalization.liesOver_map_of_isPrime_disjoint (Submonoid.powers e) C hdis
  have : QC.LiesOver q := Ideal.LiesOver.trans _ Q _
  have : Module.Flat B C := Module.Flat.trans B (S ⊗[A] B) C
  apply localizedMap_bijective_of_flat_baseChange (noetherPairing F).flip q QC
  let F' := FiniteOpenFactorization.baseChange F S
  let _ : Module B (dualizingModule F') := Module.compHom _ (algebraMap B (S ⊗[A] B))
  let _ : IsScalarTower B (S ⊗[A] B) (dualizingModule F') :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  have := dualizingModule_finitePresentation F
  have hbase :
      Function.Bijective ((noetherPairing F).flip.baseChange C) ↔
        Function.Bijective ((noetherPairing F').flip.baseChange C) :=
    pairing_flip_iteratedBaseChange_bijective_iff
      (noetherPairing F) (noetherPairing F')
      (dualizingModule.baseChange F S) (diagonalAnnihilatorScalarExtension A B S)
      (dualizingModule_isBaseChange_of_flat F S)
      (diagonalAnnihilatorScalarExtension_isBaseChange A B S) fun ω j =>
        noetherPairing_baseChange S F ω j
  have : Algebra.FiniteType S (S ⊗[A] B) := inferInstance
  have : IsNoetherianRing (S ⊗[A] B) := Algebra.FiniteType.isNoetherianRing S (S ⊗[A] B)
  have : Algebra.QuasiFinite S (S ⊗[A] B) := inferInstance
  have : Module.Flat S (S ⊗[A] B) := Module.Flat.baseChange A S B
  exact hbase.mpr ((noetherPairing_flip_baseChange_bijective_iff_away e F').mpr
    (noetherPairing_flip_bijective_of_factorization _ (selfFactorization S C) hbranch))

/-- The linear equivalence induced by the canonical pairing of a flat quasi-finite homomorphism
of Noetherian rings. -/
noncomputable def noetherPairingEquiv
    [IsNoetherianRing A] [IsNoetherianRing B]
    [Module.Flat A B] [Algebra.QuasiFinite A B]
    (F : FiniteOpenFactorization.{u, v, w} A B) :
    ↑(diagonalAnnihilator A B) ≃ₗ[B] (dualizingModule F →ₗ[B] B) :=
  LinearEquiv.ofBijective (noetherPairing F).flip (noetherPairing_flip_bijective F)

end Stacks.Discriminant

end
