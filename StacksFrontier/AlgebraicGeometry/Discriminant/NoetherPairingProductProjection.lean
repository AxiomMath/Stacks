module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Discriminant.NoetherPairingNaturality
public import StacksFrontier.AlgebraicGeometry.Discriminant.NoetherPairingProduct
public import StacksFrontier.AlgebraicGeometry.Discriminant.ProductFactorization

/-!
# The canonical pairing and the two projections of a product

Let `A` be a Noetherian ring and let `B` and `C` be quasi-finite Noetherian `A`-algebras. The
relative dualizing module of `A → B × C` is the product of the relative dualizing modules of
`A → B` and of `A → C`, and the diagonal annihilator of `B × C` projects to the diagonal
annihilators of `B` and of `C`. This file proves that the canonical pairing of Tag 0BVP is
compatible with these two projections.

## Main definitions

* `Stacks.Discriminant.diagonalAnnihilatorCongr` transports the diagonal annihilator along an
  algebra equivalence.

## Main results

* `Stacks.Discriminant.noetherPairing_prod_fst` and
  `Stacks.Discriminant.noetherPairing_prod_snd`: the canonical pairing commutes with the
  projections to the two factors.

## Implementation notes

The compatibility is first proved for a finite-open factorization whose intermediate algebra is
presented as the product of the two chosen intermediate algebras, where both the product
equivalence of dualizing modules and the decomposition of the diagonal annihilator are given on
pure tensors. The general case follows from independence of the factorization, in the form of
`Stacks.Discriminant.noetherPairing_naturality` for the pairing and of
`Stacks.Discriminant.dualizingModuleProdEquiv_naturality` for the product equivalence, applied to
the product of the two chosen factorizations.

As in Tag 0BT5 the presentation of the intermediate algebra is an algebra equivalence from the
product of the two chosen intermediate algebras rather than an equality, so an element of the
diagonal annihilator of the intermediate algebra is transported along it before being projected.

## References

* [Stacks Project, Tag 0BVR](https://stacks.math.columbia.edu/tag/0BVR)
-/

@[expose] public section

open scoped TensorProduct

namespace Stacks.Discriminant

universe u v w x y z

attribute [local instance] algebraDualModule

/-- An algebra equivalence carries the diagonal annihilator to the diagonal annihilator. -/
def diagonalAnnihilatorCongr
    {A : Type u} {C : Type v} {D : Type w}
    [CommRing A] [CommRing C] [CommRing D] [Algebra A C] [Algebra A D]
    (e : C ≃ₐ[A] D) (j : ↑(diagonalAnnihilator A C)) :
    ↑(diagonalAnnihilator A D) :=
  ⟨Algebra.TensorProduct.map e.toAlgHom e.toAlgHom j.1, by
    apply mem_diagonalAnnihilator_of_mul_tmul_sub_eq_zero
    intro d
    have hmem : (1 : C) ⊗ₜ[A] e.symm d - e.symm d ⊗ₜ[A] (1 : C) ∈
        RingHom.ker (Algebra.TensorProduct.lmul' (R := A) (S := C)).toRingHom := by
      rw [RingHom.mem_ker]
      change (Algebra.TensorProduct.lmul' A) _ = 0
      simp [Algebra.TensorProduct.lmul'_apply_tmul]
    have h0 : j.1 * ((1 : C) ⊗ₜ[A] e.symm d - e.symm d ⊗ₜ[A] (1 : C)) = 0 := by
      simpa only [smul_eq_mul] using (Submodule.mem_annihilator.mp j.2) _ hmem
    have hmap := congrArg (Algebra.TensorProduct.map e.toAlgHom e.toAlgHom) h0
    rw [map_mul, map_zero, map_sub] at hmap
    simpa only [Algebra.TensorProduct.map_tmul, map_one, AlgEquiv.coe_toAlgHom,
      AlgEquiv.apply_symm_apply] using hmap⟩

/-- Transport of the diagonal annihilator along an algebra equivalence is additive. -/
lemma diagonalAnnihilatorCongr_add
    {A : Type u} {C : Type v} {D : Type w}
    [CommRing A] [CommRing C] [CommRing D] [Algebra A C] [Algebra A D]
    (e : C ≃ₐ[A] D) (j k : ↑(diagonalAnnihilator A C)) :
    diagonalAnnihilatorCongr e (j + k) =
      diagonalAnnihilatorCongr e j + diagonalAnnihilatorCongr e k := by
  apply Subtype.ext
  simp [diagonalAnnihilatorCongr]

/-- Transport of the diagonal annihilator along an algebra equivalence kills zero. -/
lemma diagonalAnnihilatorCongr_zero
    {A : Type u} {C : Type v} {D : Type w}
    [CommRing A] [CommRing C] [CommRing D] [Algebra A C] [Algebra A D]
    (e : C ≃ₐ[A] D) :
    diagonalAnnihilatorCongr e 0 = 0 := by
  apply Subtype.ext
  simp [diagonalAnnihilatorCongr]

/-- Contracting the transport along `e.symm` of an element of the diagonal annihilator against
`f ∘ e` is `e.symm` of its contraction against `f`. -/
private theorem tensorContract_diagonalAnnihilatorCongr_symm
    {A : Type u} {C : Type v} {D : Type w}
    [CommRing A] [CommRing C] [CommRing D] [Algebra A C] [Algebra A D]
    (e : C ≃ₐ[A] D) (f : Module.Dual A D) (j : ↑(diagonalAnnihilator A D)) :
    tensorContract A C (f.comp e.toLinearMap) (diagonalAnnihilatorCongr e.symm j).1 =
      e.symm (tensorContract A D f j.1) := by
  change tensorContract A C (f.comp e.toLinearMap)
    (Algebra.TensorProduct.map e.symm.toAlgHom e.symm.toAlgHom j.1) = _
  rw [tensorContract_map, show (f.comp e.toLinearMap).comp
    (e.symm.toAlgHom : D →ₐ[A] C).toLinearMap = f from by
      ext u
      exact congrArg f (e.apply_symm_apply u)]
  rfl

/-- The diagonal annihilator of the target is the image of a surjective linear map from the base
change of the diagonal annihilator of the intermediate algebra. -/
private theorem exists_surjective_diagonalAnnihilatorBaseChange
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (F : FiniteOpenFactorization.{u, v, x} A B) :
    ∃ ψJ : B ⊗[F.middle] (↑(diagonalAnnihilator A F.middle)) →ₗ[B]
        (↑(diagonalAnnihilator A B)),
      (∀ t, (ψJ t).1 = diagonalAnnihilatorBaseChange A F.middle B t) ∧
        Function.Surjective ψJ := by
  have hopen := specMap_ulift_isOpenImmersion (algebraMap F.middle B)
    F.isOpenEmbedding_comap F.awayMap_bijective
  have hRange := range_diagonalAnnihilatorBaseChange A F.middle B hopen
  refine ⟨(diagonalAnnihilatorBaseChange A F.middle B).codRestrict
    ((diagonalAnnihilator A B).restrictScalars B) (fun t => ?_), fun t => rfl, fun j₀ => ?_⟩
  · rw [← hRange]
    exact ⟨t, rfl⟩
  · obtain ⟨t, ht⟩ := (show j₀.1 ∈ LinearMap.range (diagonalAnnihilatorBaseChange A F.middle B)
      by rw [hRange]; exact j₀.2)
    exact ⟨t, Subtype.ext ht⟩

/-- The pairing commutes with the projection to the first factor, for a finite-open factorization
whose intermediate algebra is presented as the product of the two chosen ones. -/
private theorem noetherPairing_product_fst
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
    [Algebra.QuasiFinite A B] [Algebra.QuasiFinite A C]
    (F : FiniteOpenFactorization.{u, max v w, x} A (B × C))
    (FB : FiniteOpenFactorization.{u, v, y} A B)
    (FC : FiniteOpenFactorization.{u, w, z} A C)
    (e : (FB.middle × FC.middle) ≃ₐ[A] F.middle)
    (hcompat : ∀ p : FB.middle × FC.middle,
      algebraMap F.middle (B × C) (e p) =
        (algebraMap FB.middle B p.1, algebraMap FC.middle C p.2))
    (ω : dualizingModule F) (j : ↑(diagonalAnnihilator A (B × C))) :
    noetherPairing FB ((dualizingModuleProdEquiv F FB FC ω).1)
        (diagonalAnnihilatorProdFst A B C j) =
      (noetherPairing F ω j).1 := by
  classical
  obtain ⟨ψJ, hψJ, hsurj⟩ := exists_surjective_diagonalAnnihilatorBaseChange F
  induction ω using dualizingModule.induction_on with
  | add ω₁ ω₂ h₁ h₂ =>
      rw [map_add (dualizingModuleProdEquiv F FB FC)]
      simp only [Prod.fst_add, map_add, LinearMap.add_apply, h₁, h₂]
  | tmul f x =>
      obtain ⟨b, c⟩ := x
      have hprod := dualizingModuleProdEquiv_tmul F FB FC e hcompat f b c
      rw [hprod]
      obtain ⟨t, rfl⟩ := hsurj j
      induction t using TensorProduct.inductionOn with
      | add t₁ t₂ h₁ h₂ =>
          rw [map_add ψJ, diagonalAnnihilatorProdFst_add, map_add, map_add, Prod.fst_add,
            h₁, h₂]
      | tmul y j' =>
          have hkey : ∀ a : F.middle,
              (algebraMap F.middle (B × C) a).1 = algebraMap FB.middle B (e.symm a).1 := by
            intro a
            have h := congrArg Prod.fst (hcompat (e.symm a))
            rwa [e.apply_symm_apply] at h
          have hjP : (ψJ (y ⊗ₜ[F.middle] j')).1 =
              diagonalAnnihilatorBaseChange A F.middle (B × C) (y ⊗ₜ[F.middle] j') := hψJ _
          have hjB : (diagonalAnnihilatorProdFst A B C (ψJ (y ⊗ₜ[F.middle] j'))).1 =
              diagonalAnnihilatorBaseChange A FB.middle B
                (y.1 ⊗ₜ[FB.middle] diagonalAnnihilatorProdFst A FB.middle FC.middle
                  (diagonalAnnihilatorCongr e.symm j')) := by
            have hz : ∀ t : F.middle ⊗[A] F.middle,
                Algebra.TensorProduct.map (AlgHom.fst A B C) (AlgHom.fst A B C)
                    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A F.middle (B × C))
                      (IsScalarTower.toAlgHom A F.middle (B × C)) t) =
                  Algebra.TensorProduct.map (IsScalarTower.toAlgHom A FB.middle B)
                      (IsScalarTower.toAlgHom A FB.middle B)
                    (Algebra.TensorProduct.map (AlgHom.fst A FB.middle FC.middle)
                      (AlgHom.fst A FB.middle FC.middle)
                      (Algebra.TensorProduct.map e.symm.toAlgHom e.symm.toAlgHom t)) := by
              intro t
              induction t using TensorProduct.inductionOn with
              | tmul a d =>
                  simp only [Algebra.TensorProduct.map_tmul]
                  change (algebraMap F.middle (B × C) a).1 ⊗ₜ[A]
                      (algebraMap F.middle (B × C) d).1 =
                    algebraMap FB.middle B (e.symm a).1 ⊗ₜ[A] algebraMap FB.middle B (e.symm d).1
                  rw [hkey a, hkey d]
              | add t₁ t₂ h₁ h₂ => simp only [map_add, h₁, h₂]
            change Algebra.TensorProduct.map (AlgHom.fst A B C) (AlgHom.fst A B C)
              (ψJ (y ⊗ₜ[F.middle] j')).1 = _
            rw [hjP, diagonalAnnihilatorBaseChange_tmul_eq,
              diagonalAnnihilatorBaseChange_tmul_eq, map_mul,
              Algebra.TensorProduct.map_tmul, map_one]
            change (y.1 ⊗ₜ[A] (1 : B)) * _ = (y.1 ⊗ₜ[A] (1 : B)) * _
            congr 1
            exact hz j'.1
          rw [noetherPairing_apply_of_eq_baseChange FB
              (f.comp (e.toLinearMap.comp (LinearMap.inl A FB.middle FC.middle))) b y.1
              (diagonalAnnihilatorProdFst A FB.middle FC.middle
                (diagonalAnnihilatorCongr e.symm j')) _ hjB,
            noetherPairing_apply_of_eq_baseChange F f (b, c) y j' _ hjP]
          have hcontract : tensorContract A FB.middle
                (f.comp (e.toLinearMap.comp (LinearMap.inl A FB.middle FC.middle)))
                (diagonalAnnihilatorProdFst A FB.middle FC.middle
                  (diagonalAnnihilatorCongr e.symm j')).1 =
              (tensorContract A (FB.middle × FC.middle) (f.comp e.toLinearMap)
                (diagonalAnnihilatorCongr e.symm j').1).1 :=
            tensorContract_fst_prod (f.comp e.toLinearMap)
              (diagonalAnnihilatorCongr e.symm j')
          rw [hcontract, tensorContract_diagonalAnnihilatorCongr_symm e f j', Prod.fst_mul,
            Prod.fst_mul, hkey]

/-- The pairing commutes with the projection to the second factor, for a finite-open
factorization whose intermediate algebra is presented as the product of the two chosen ones. -/
private theorem noetherPairing_product_snd
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
    [Algebra.QuasiFinite A B] [Algebra.QuasiFinite A C]
    (F : FiniteOpenFactorization.{u, max v w, x} A (B × C))
    (FB : FiniteOpenFactorization.{u, v, y} A B)
    (FC : FiniteOpenFactorization.{u, w, z} A C)
    (e : (FB.middle × FC.middle) ≃ₐ[A] F.middle)
    (hcompat : ∀ p : FB.middle × FC.middle,
      algebraMap F.middle (B × C) (e p) =
        (algebraMap FB.middle B p.1, algebraMap FC.middle C p.2))
    (ω : dualizingModule F) (j : ↑(diagonalAnnihilator A (B × C))) :
    noetherPairing FC ((dualizingModuleProdEquiv F FB FC ω).2)
        (diagonalAnnihilatorProdSnd A B C j) =
      (noetherPairing F ω j).2 := by
  classical
  obtain ⟨ψJ, hψJ, hsurj⟩ := exists_surjective_diagonalAnnihilatorBaseChange F
  induction ω using dualizingModule.induction_on with
  | add ω₁ ω₂ h₁ h₂ =>
      rw [map_add (dualizingModuleProdEquiv F FB FC)]
      simp only [Prod.snd_add, map_add, LinearMap.add_apply, h₁, h₂]
  | tmul f x =>
      obtain ⟨b, c⟩ := x
      have hprod := dualizingModuleProdEquiv_tmul F FB FC e hcompat f b c
      rw [hprod]
      obtain ⟨t, rfl⟩ := hsurj j
      induction t using TensorProduct.inductionOn with
      | add t₁ t₂ h₁ h₂ =>
          rw [map_add ψJ, diagonalAnnihilatorProdSnd_add, map_add, map_add, Prod.snd_add,
            h₁, h₂]
      | tmul y j' =>
          have hkey : ∀ a : F.middle,
              (algebraMap F.middle (B × C) a).2 = algebraMap FC.middle C (e.symm a).2 := by
            intro a
            have h := congrArg Prod.snd (hcompat (e.symm a))
            rwa [e.apply_symm_apply] at h
          have hjP : (ψJ (y ⊗ₜ[F.middle] j')).1 =
              diagonalAnnihilatorBaseChange A F.middle (B × C) (y ⊗ₜ[F.middle] j') := hψJ _
          have hjC : (diagonalAnnihilatorProdSnd A B C (ψJ (y ⊗ₜ[F.middle] j'))).1 =
              diagonalAnnihilatorBaseChange A FC.middle C
                (y.2 ⊗ₜ[FC.middle] diagonalAnnihilatorProdSnd A FB.middle FC.middle
                  (diagonalAnnihilatorCongr e.symm j')) := by
            have hz : ∀ t : F.middle ⊗[A] F.middle,
                Algebra.TensorProduct.map (AlgHom.snd A B C) (AlgHom.snd A B C)
                    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A F.middle (B × C))
                      (IsScalarTower.toAlgHom A F.middle (B × C)) t) =
                  Algebra.TensorProduct.map (IsScalarTower.toAlgHom A FC.middle C)
                      (IsScalarTower.toAlgHom A FC.middle C)
                    (Algebra.TensorProduct.map (AlgHom.snd A FB.middle FC.middle)
                      (AlgHom.snd A FB.middle FC.middle)
                      (Algebra.TensorProduct.map e.symm.toAlgHom e.symm.toAlgHom t)) := by
              intro t
              induction t using TensorProduct.inductionOn with
              | tmul a d =>
                  simp only [Algebra.TensorProduct.map_tmul]
                  change (algebraMap F.middle (B × C) a).2 ⊗ₜ[A]
                      (algebraMap F.middle (B × C) d).2 =
                    algebraMap FC.middle C (e.symm a).2 ⊗ₜ[A] algebraMap FC.middle C (e.symm d).2
                  rw [hkey a, hkey d]
              | add t₁ t₂ h₁ h₂ => simp only [map_add, h₁, h₂]
            change Algebra.TensorProduct.map (AlgHom.snd A B C) (AlgHom.snd A B C)
              (ψJ (y ⊗ₜ[F.middle] j')).1 = _
            rw [hjP, diagonalAnnihilatorBaseChange_tmul_eq,
              diagonalAnnihilatorBaseChange_tmul_eq, map_mul,
              Algebra.TensorProduct.map_tmul, map_one]
            change (y.2 ⊗ₜ[A] (1 : C)) * _ = (y.2 ⊗ₜ[A] (1 : C)) * _
            congr 1
            exact hz j'.1
          rw [noetherPairing_apply_of_eq_baseChange FC
              (f.comp (e.toLinearMap.comp (LinearMap.inr A FB.middle FC.middle))) c y.2
              (diagonalAnnihilatorProdSnd A FB.middle FC.middle
                (diagonalAnnihilatorCongr e.symm j')) _ hjC,
            noetherPairing_apply_of_eq_baseChange F f (b, c) y j' _ hjP]
          have hcontract : tensorContract A FC.middle
                (f.comp (e.toLinearMap.comp (LinearMap.inr A FB.middle FC.middle)))
                (diagonalAnnihilatorProdSnd A FB.middle FC.middle
                  (diagonalAnnihilatorCongr e.symm j')).1 =
              (tensorContract A (FB.middle × FC.middle) (f.comp e.toLinearMap)
                (diagonalAnnihilatorCongr e.symm j').1).2 :=
            tensorContract_snd_prod (f.comp e.toLinearMap)
              (diagonalAnnihilatorCongr e.symm j')
          rw [hcontract, tensorContract_diagonalAnnihilatorCongr_symm e f j', Prod.snd_mul,
            Prod.snd_mul, hkey]

/-- **Stacks Project, Tag 0BVR (product projection).** The canonical pairing between the relative
dualizing module and the diagonal annihilator commutes with the projection to the first factor of
a product. -/
@[stacks 0BVR "product_projection"]
theorem noetherPairing_prod_fst
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
    [Algebra.QuasiFinite A B] [Algebra.QuasiFinite A C]
    (F : FiniteOpenFactorization.{u, max v w, x} A (B × C))
    (FB : FiniteOpenFactorization.{u, v, y} A B)
    (FC : FiniteOpenFactorization.{u, w, z} A C)
    (ω : dualizingModule F) (j : ↑(diagonalAnnihilator A (B × C))) :
    noetherPairing FB ((dualizingModuleProdEquiv F FB FC ω).1)
        (diagonalAnnihilatorProdFst A B C j) =
      (noetherPairing F ω j).1 := by
  have hfst := congrArg Prod.fst (dualizingModuleProdEquiv_naturality F
    (productFiniteOpenFactorization FB FC) FB FB FC FC ω)
  rw [dualizingModuleEquiv_refl FB, LinearEquiv.refl_apply] at hfst
  calc noetherPairing FB ((dualizingModuleProdEquiv F FB FC ω).1)
        (diagonalAnnihilatorProdFst A B C j)
      = noetherPairing FB ((dualizingModuleProdEquiv (productFiniteOpenFactorization FB FC)
          FB FC (dualizingModuleEquiv F (productFiniteOpenFactorization FB FC) ω)).1)
          (diagonalAnnihilatorProdFst A B C j) := by rw [hfst]
    _ = (noetherPairing (productFiniteOpenFactorization FB FC)
          (dualizingModuleEquiv F (productFiniteOpenFactorization FB FC) ω) j).1 :=
        noetherPairing_product_fst (productFiniteOpenFactorization FB FC) FB FC
          AlgEquiv.refl (fun _ => rfl) _ j
    _ = (noetherPairing F ω j).1 :=
        congrArg Prod.fst (noetherPairing_naturality F (productFiniteOpenFactorization FB FC) ω j)

/-- **Stacks Project, Tag 0BVR (product projection).** The canonical pairing between the relative
dualizing module and the diagonal annihilator commutes with the projection to the second factor
of a product. -/
@[stacks 0BVR "product_projection"]
theorem noetherPairing_prod_snd
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
    [Algebra.QuasiFinite A B] [Algebra.QuasiFinite A C]
    (F : FiniteOpenFactorization.{u, max v w, x} A (B × C))
    (FB : FiniteOpenFactorization.{u, v, y} A B)
    (FC : FiniteOpenFactorization.{u, w, z} A C)
    (ω : dualizingModule F) (j : ↑(diagonalAnnihilator A (B × C))) :
    noetherPairing FC ((dualizingModuleProdEquiv F FB FC ω).2)
        (diagonalAnnihilatorProdSnd A B C j) =
      (noetherPairing F ω j).2 := by
  have hsnd := congrArg Prod.snd (dualizingModuleProdEquiv_naturality F
    (productFiniteOpenFactorization FB FC) FB FB FC FC ω)
  rw [dualizingModuleEquiv_refl FC, LinearEquiv.refl_apply] at hsnd
  calc noetherPairing FC ((dualizingModuleProdEquiv F FB FC ω).2)
        (diagonalAnnihilatorProdSnd A B C j)
      = noetherPairing FC ((dualizingModuleProdEquiv (productFiniteOpenFactorization FB FC)
          FB FC (dualizingModuleEquiv F (productFiniteOpenFactorization FB FC) ω)).2)
          (diagonalAnnihilatorProdSnd A B C j) := by rw [hsnd]
    _ = (noetherPairing (productFiniteOpenFactorization FB FC)
          (dualizingModuleEquiv F (productFiniteOpenFactorization FB FC) ω) j).2 :=
        noetherPairing_product_snd (productFiniteOpenFactorization FB FC) FB FC
          AlgEquiv.refl (fun _ => rfl) _ j
    _ = (noetherPairing F ω j).2 :=
        congrArg Prod.snd (noetherPairing_naturality F (productFiniteOpenFactorization FB FC) ω j)

end Stacks.Discriminant
