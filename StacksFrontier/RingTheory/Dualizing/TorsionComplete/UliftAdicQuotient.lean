module

public import StacksFrontier.AlgebraicGeometry.ProEtale.ExtensionByZero.AdicSheaves
public import StacksFrontier.Homology.DerivedComplete.NoetherianCompleteIdealPowers

/-!
# The adic quotient tower over the ring in the module universe

A module `M` over a ring `A` becomes a module over `ULift A` under the universe lift
`AdicKoszul.moduleUniverseLift`, and an ideal `I` of `A` becomes the ideal
`I.comap ULift.ringEquiv` of `ULift A`. This file transports the tower of adic quotients
`M / IⁿM` across that lift: the tower formed over `ULift A` by the lifted module and the
contracted ideal is naturally isomorphic to the lift of the original tower, compatibly with
the quotient maps out of `M`. Finite generation of the ideal and finiteness of the module are
carried across as well.

## Main results

* `Dualizing.fg_comap_uliftRingEquiv` — contracting an ideal along the universe-lift ring
  equivalence preserves finite generation.
* `Dualizing.finite_moduleUniverseLift_obj` — the universe lift of a finite module is finite.
* `Dualizing.uliftAdicQuotientModuleSystemIso` — the natural isomorphism of adic quotient
  towers.
* `Dualizing.map_mkQ_comp_uliftAdicQuotientModuleSystemIso` — that isomorphism carries the
  lift of the quotient map `M ↠ M/IⁿM` to the quotient map of the lifted module.

## Implementation notes

The comparison is built from the inverse direction. The lift of `M ↠ M/IⁿM` is a surjection of
`ULift A`-modules whose kernel is exactly the submodule cut out by the contracted ideal, so it
factors through the quotient of the lifted module as an isomorphism, and the isomorphism of
towers is the inverse of the resulting natural transformation. The compatibility with the
quotient maps is then obtained by cancelling that isomorphism, which reduces it to
`Submodule.liftQ_mkQ`.

No transfer of `IsNoetherianRing` to `ULift` appears here: instance search already produces
`IsNoetherianRing (ULift A)` from `IsNoetherianRing A`.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace Dualizing

/-- Contracting an ideal along the universe-lift ring equivalence is the pushforward along the
inverse equivalence. -/
private theorem comap_uliftRingEquiv_eq_map (A : Type u) [CommRing A] (I : Ideal A) :
    I.comap (ULift.ringEquiv.{u, u} (R := A)).toRingHom =
      Ideal.map (ULift.ringEquiv.{u, u} (R := A)).symm.toRingHom I := by
  rw [RingEquiv.toRingHom_eq_coe, RingEquiv.toRingHom_eq_coe, Ideal.map_comap_of_equiv,
    RingEquiv.symm_symm, Ideal.comap_coe]

/-- Contraction along the universe-lift ring equivalence commutes with powers. -/
private theorem comap_uliftRingEquiv_pow (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) :
    (I.comap (ULift.ringEquiv.{u, u} (R := A)).toRingHom) ^ n =
      (I ^ n).comap (ULift.ringEquiv.{u, u} (R := A)).toRingHom := by
  rw [comap_uliftRingEquiv_eq_map, comap_uliftRingEquiv_eq_map, Ideal.map_pow]

/-- A finitely generated ideal stays finitely generated when contracted along the universe-lift
ring equivalence of its ring. -/
theorem fg_comap_uliftRingEquiv (A : Type u) [CommRing A] {I : Ideal A} (hI : I.FG) :
    (I.comap (ULift.ringEquiv.{u, u} (R := A)).toRingHom).FG := by
  obtain ⟨r, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hI
  rw [NoetherianAdicCompletion.comap_uliftRingEquiv_eq_span f I hf]
  exact Submodule.fg_span (Set.finite_range _)

/-- An element of a module, read as an element of its universe lift over the lifted ring. This
is `ULift.up`, but with the target written as the carrier of the lifted module, which is what
the `ULift A`-module structure is attached to. -/
private def uliftElt (A : Type u) [CommRing A] (M : ModuleCat.{u} A) (y : (M : Type u)) :
    ((AdicKoszul.moduleUniverseLift.{u, u} A).obj M : Type u) := ULift.up y

/-- The universe lift of a finite module is finite over the lifted ring. -/
instance finite_moduleUniverseLift_obj (A : Type u) [CommRing A] (M : ModuleCat.{u} A)
    [Module.Finite A M] :
    Module.Finite (ULift.{u} A) ((AdicKoszul.moduleUniverseLift.{u, u} A).obj M) := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := (M : Type u))
  refine ⟨⟨s.image (uliftElt A M), ?_⟩⟩
  refine top_unique fun x _ ↦ ?_
  have hx : x.down ∈ Submodule.span A (s : Set (M : Type u)) := hs ▸ Submodule.mem_top
  have key : ∀ y : (M : Type u), y ∈ Submodule.span A (s : Set (M : Type u)) →
      uliftElt A M y ∈ Submodule.span (ULift.{u} A)
        ((s.image (uliftElt A M) : Finset _) : Set _) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      exact Submodule.subset_span
        (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_coe.1 hz)))
    | zero =>
      have h0 : uliftElt A M 0 = 0 := rfl
      rw [h0]
      exact Submodule.zero_mem _
    | add z w _ _ hz hw =>
      have hadd : uliftElt A M (z + w) = uliftElt A M z + uliftElt A M w := rfl
      rw [hadd]
      exact Submodule.add_mem _ hz hw
    | smul a z _ hz =>
      have hsmul : uliftElt A M (a • z) = (ULift.up a : ULift.{u} A) • uliftElt A M z := rfl
      rw [hsmul]
      exact Submodule.smul_mem _ _ hz
  exact key x.down hx

/-- The submodule cut out by a power of the contracted ideal consists exactly of the lifts of
the elements cut out by the corresponding power of the original ideal. -/
private theorem mem_comap_pow_smul_top (A : Type u) [CommRing A] (I : Ideal A)
    (M : ModuleCat.{u} A) (n : ℕ)
    (x : ((AdicKoszul.moduleUniverseLift.{u, u} A).obj M : Type u)) :
    x ∈ (I.comap (ULift.ringEquiv.{u, u} (R := A)).toRingHom) ^ n •
        (⊤ : Submodule (ULift.{u} A)
          ((AdicKoszul.moduleUniverseLift.{u, u} A).obj M : Type u)) ↔
      x.down ∈ I ^ n • (⊤ : Submodule A (M : Type u)) := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro b hb y _
      rw [comap_uliftRingEquiv_pow] at hb
      have hb' : b.down ∈ I ^ n := hb
      change b.down • y.down ∈ I ^ n • (⊤ : Submodule A (M : Type u))
      exact Submodule.smul_mem_smul hb' Submodule.mem_top
    · intro y z hy hz
      change y.down + z.down ∈ I ^ n • (⊤ : Submodule A (M : Type u))
      exact Submodule.add_mem _ hy hz
  · intro hx
    have key : ∀ y : (M : Type u), y ∈ I ^ n • (⊤ : Submodule A (M : Type u)) →
        uliftElt A M y ∈ (I.comap (ULift.ringEquiv.{u, u} (R := A)).toRingHom) ^ n •
          (⊤ : Submodule (ULift.{u} A)
            ((AdicKoszul.moduleUniverseLift.{u, u} A).obj M : Type u)) := by
      intro y hy
      refine Submodule.smul_induction_on hy ?_ ?_
      · intro a ha m _
        have ha' : (ULift.up a : ULift.{u} A) ∈
            (I.comap (ULift.ringEquiv.{u, u} (R := A)).toRingHom) ^ n := by
          rw [comap_uliftRingEquiv_pow]; exact ha
        have hsmul : uliftElt A M (a • m) =
          (ULift.up a : ULift.{u} A) • uliftElt A M m := rfl
        rw [hsmul]
        exact Submodule.smul_mem_smul ha' Submodule.mem_top
      · intro y z hy hz
        have hadd : uliftElt A M (y + z) = uliftElt A M y + uliftElt A M z := rfl
        rw [hadd]
        exact Submodule.add_mem _ hy hz
    exact key x.down hx

/-- The universe lift of the quotient map `M ↠ M/IⁿM`, viewed as a map onto the `n`-th term of
the lifted adic quotient tower. -/
private def uliftQuotientSurjection (A : Type u) [CommRing A] (I : Ideal A)
    (M : ModuleCat.{u} A) (n : ℕ) :
    (AdicKoszul.moduleUniverseLift.{u, u} A).obj M ⟶
      (AlgebraicGeometry.ProEtale.adicQuotientModuleSystem A I M ⋙
        AdicKoszul.moduleUniverseLift.{u, u} A).obj ⟨n⟩ :=
  (AdicKoszul.moduleUniverseLift.{u, u} A).map
    (ModuleCat.ofHom (I ^ n • (⊤ : Submodule A (M : Type u))).mkQ)

/-- The quotient map of the lifted module onto the `n`-th term of its own adic quotient tower,
with the target written as that term of the tower. -/
private def uliftTowerMkQ (A : Type u) [CommRing A] (I : Ideal A) (M : ModuleCat.{u} A)
    (n : ℕ) :
    (AdicKoszul.moduleUniverseLift.{u, u} A).obj M ⟶
      (AlgebraicGeometry.ProEtale.adicQuotientModuleSystem (ULift.{u} A)
        (I.comap (ULift.ringEquiv.{u, u} (R := A)).toRingHom)
        ((AdicKoszul.moduleUniverseLift.{u, u} A).obj M)).obj ⟨n⟩ :=
  ModuleCat.ofHom ((I.comap (ULift.ringEquiv.{u, u} (R := A)).toRingHom) ^ n •
    (⊤ : Submodule (ULift.{u} A)
      ((AdicKoszul.moduleUniverseLift.{u, u} A).obj M : Type u))).mkQ

private theorem ker_uliftQuotientSurjection (A : Type u) [CommRing A] (I : Ideal A)
    (M : ModuleCat.{u} A) (n : ℕ) :
    LinearMap.ker (uliftQuotientSurjection A I M n).hom =
      (I.comap (ULift.ringEquiv.{u, u} (R := A)).toRingHom) ^ n •
        (⊤ : Submodule (ULift.{u} A)
          ((AdicKoszul.moduleUniverseLift.{u, u} A).obj M : Type u)) := by
  ext x
  rw [LinearMap.mem_ker, mem_comap_pow_smul_top]
  constructor
  · intro h
    exact (Submodule.Quotient.mk_eq_zero _).1 (congrArg ULift.down h)
  · intro h
    exact congrArg ULift.up ((Submodule.Quotient.mk_eq_zero _).2 h)

/-- The comparison map from the `n`-th term of the adic quotient tower of the lifted module to
the lift of the `n`-th term of the original tower, obtained by factoring the lifted quotient
map through its kernel. -/
private def uliftAdicQuotientInvMap (A : Type u) [CommRing A] (I : Ideal A)
    (M : ModuleCat.{u} A) (n : ℕ) :
    (AlgebraicGeometry.ProEtale.adicQuotientModuleSystem (ULift.{u} A)
        (I.comap (ULift.ringEquiv.{u, u} (R := A)).toRingHom)
        ((AdicKoszul.moduleUniverseLift.{u, u} A).obj M)).obj ⟨n⟩ ⟶
      (AlgebraicGeometry.ProEtale.adicQuotientModuleSystem A I M ⋙
        AdicKoszul.moduleUniverseLift.{u, u} A).obj ⟨n⟩ :=
  ModuleCat.ofHom (Submodule.liftQ _ (uliftQuotientSurjection A I M n).hom
    (le_of_eq (ker_uliftQuotientSurjection A I M n).symm))

private instance isIso_uliftAdicQuotientInvMap (A : Type u) [CommRing A] (I : Ideal A)
    (M : ModuleCat.{u} A) (n : ℕ) : IsIso (uliftAdicQuotientInvMap A I M n) := by
  refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨?_, ?_⟩
  · refine LinearMap.ker_eq_bot.1 ?_
    exact Submodule.ker_liftQ_eq_bot _ _ _ (le_of_eq (ker_uliftQuotientSurjection A I M n))
  · intro y
    obtain ⟨m, hm⟩ := Submodule.Quotient.mk_surjective
      (I ^ n • (⊤ : Submodule A (M : Type u))) y.down
    exact ⟨Submodule.Quotient.mk (uliftElt A M m), congrArg ULift.up hm⟩

private theorem uliftAdicQuotientInvMap_transition (A : Type u) [CommRing A] (I : Ideal A)
    (M : ModuleCat.{u} A) (n : ℕ) :
    ModuleCat.ofHom (AdicCompletion.transitionMap
          (I.comap (ULift.ringEquiv.{u, u} (R := A)).toRingHom)
          ((AdicKoszul.moduleUniverseLift.{u, u} A).obj M : Type u) (Nat.le_succ n)) ≫
        uliftAdicQuotientInvMap A I M n =
      uliftAdicQuotientInvMap A I M (n + 1) ≫
        (AdicKoszul.moduleUniverseLift.{u, u} A).map
          (ModuleCat.ofHom (AdicCompletion.transitionMap I (M : Type u) (Nat.le_succ n))) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro q
  induction q using Quotient.inductionOn with
  | _ x => rfl

/-- The comparison of towers, in the direction out of the tower of the lifted module. -/
private def uliftAdicQuotientInvNatTrans (A : Type u) [CommRing A] (I : Ideal A)
    (M : ModuleCat.{u} A) :
    AlgebraicGeometry.ProEtale.adicQuotientModuleSystem (ULift.{u} A)
        (I.comap (ULift.ringEquiv.{u, u} (R := A)).toRingHom)
        ((AdicKoszul.moduleUniverseLift.{u, u} A).obj M) ⟶
      AlgebraicGeometry.ProEtale.adicQuotientModuleSystem A I M ⋙
        AdicKoszul.moduleUniverseLift.{u, u} A :=
  NatTrans.ofOpSequence (fun n ↦ uliftAdicQuotientInvMap A I M n) (by
    intro n
    erw [Functor.ofOpSequence_map_homOfLE_succ, Functor.comp_map,
      Functor.ofOpSequence_map_homOfLE_succ]
    exact uliftAdicQuotientInvMap_transition A I M n)

private instance isIso_uliftAdicQuotientInvNatTrans_app (A : Type u) [CommRing A] (I : Ideal A)
    (M : ModuleCat.{u} A) (n : ℕᵒᵖ) :
    IsIso ((uliftAdicQuotientInvNatTrans A I M).app n) :=
  isIso_uliftAdicQuotientInvMap A I M n.unop

private instance isIso_uliftAdicQuotientInvNatTrans (A : Type u) [CommRing A] (I : Ideal A)
    (M : ModuleCat.{u} A) : IsIso (uliftAdicQuotientInvNatTrans A I M) :=
  NatIso.isIso_of_isIso_app (uliftAdicQuotientInvNatTrans A I M)

/-- The universe lift of the adic quotient tower of `M` is the adic quotient tower of the
lifted module over the contracted ideal. -/
@[no_expose]
def uliftAdicQuotientModuleSystemIso (A : Type u) [CommRing A] (I : Ideal A)
    (M : ModuleCat.{u} A) :
    AlgebraicGeometry.ProEtale.adicQuotientModuleSystem A I M ⋙
        AdicKoszul.moduleUniverseLift.{u, u} A ≅
      AlgebraicGeometry.ProEtale.adicQuotientModuleSystem (ULift.{u} A)
        (I.comap (ULift.ringEquiv.{u, u} (R := A)).toRingHom)
        ((AdicKoszul.moduleUniverseLift.{u, u} A).obj M) :=
  (asIso (uliftAdicQuotientInvNatTrans A I M)).symm

/-- The comparison of towers carries the universe lift of the quotient map `M ↠ M/IⁿM` to the
quotient map of the lifted module by the corresponding power of the contracted ideal. -/
theorem map_mkQ_comp_uliftAdicQuotientModuleSystemIso (A : Type u) [CommRing A] (I : Ideal A)
    (M : ModuleCat.{u} A) (n : ℕ) :
    (AdicKoszul.moduleUniverseLift.{u, u} A).map
          (ModuleCat.ofHom (I ^ n • (⊤ : Submodule A (M : Type u))).mkQ) ≫
        (uliftAdicQuotientModuleSystemIso A I M).hom.app ⟨n⟩ =
      ModuleCat.ofHom ((I.comap (ULift.ringEquiv.{u, u} (R := A)).toRingHom) ^ n •
        (⊤ : Submodule (ULift.{u} A)
          (((AdicKoszul.moduleUniverseLift.{u, u} A).obj M : Type u)))).mkQ := by
  have happ : (uliftAdicQuotientModuleSystemIso A I M).inv.app (⟨n⟩ : ℕᵒᵖ) =
      uliftAdicQuotientInvMap A I M n := rfl
  have hcancel := (uliftAdicQuotientModuleSystemIso A I M).hom_inv_id_app (⟨n⟩ : ℕᵒᵖ)
  rw [happ] at hcancel
  change uliftQuotientSurjection A I M n ≫
      (uliftAdicQuotientModuleSystemIso A I M).hom.app (⟨n⟩ : ℕᵒᵖ) = uliftTowerMkQ A I M n
  rw [← cancel_mono (uliftAdicQuotientInvMap A I M n), Category.assoc, hcancel,
    Category.comp_id]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

end Dualizing

end
