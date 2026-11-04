module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.DeducingFullyFaithfulness.DerivedTensorResidueFieldSkyscraper
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalkPseudoCoherent
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsRingIso
public import StacksFrontier.Topology.Sheaves.Modules.StalkSkyscraperAdjunction
public import StacksFrontier.AlgebraicGeometry.Modules.StalkRingComparison
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.StalkwiseIsomorphism
public import StacksFrontier.AlgebraicGeometry.DevissageNoetherian.Support
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaClosedEmbeddingUnconditional
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Detecting zero perfect complexes by maps into residue-field skyscrapers

Let `X` be a Noetherian scheme and `K` a perfect object of `D(𝒪_X)`. If
`Hom(K, 𝒪_x[i]) = 0` for every closed point `x` and every `i ∈ ℤ`, where `𝒪_x` is the skyscraper
sheaf at `x` with value `κ(x)`, then `K = 0`. This is the global consequence of
[Stacks, Tag 0G03] part (4) that the criterion [Stacks, Tag 0G24] consumes (its hypothesis (3)).

The proof: the stalk functor at `x` is left adjoint to the skyscraper functor at `x`, both exact,
so `Hom(K, 𝒪_x[i]) = Hom(K_x, κ(x)[i])` in `D(𝒪_{X,x})`. The derived stalk `K_x` is
pseudo-coherent, so bounded above with finite cohomology; if it is nonzero its top cohomology
module is a nonzero finite module over the local ring `𝒪_{X,x}`, which has a nonzero map to
`κ(x)` by Nakayama's lemma, and that map gives a nonzero morphism `K_x ⟶ κ(x)[-t]`. Hence every
cohomology sheaf of `K` has zero stalk at every closed point; a nonzero coherent sheaf on a
quasi-compact scheme has a closed point in its support, so `K = 0`.

## Main results

* `Stacks.AlgebraicGeometry.DerivedVarieties.Orlov.isZero_of_forall_hom_shift_residueField`:
  over a local ring, a bounded above complex with finite cohomology admitting no nonzero map to
  any shift of the residue field is zero.
* `Stacks.AlgebraicGeometry.DerivedVarieties.Orlov.homPointSheafShiftEquiv`:
  `Hom(K, 𝒪_x[i]) ≃ Hom(K_x, κ(x)[i])`.
* `Stacks.AlgebraicGeometry.DerivedVarieties.Orlov.isZero_of_forall_hom_pointSheaf_shift`: the
  global detection statement above.

## References

* [Stacks Project, Tag 0G03](https://stacks.math.columbia.edu/tag/0G03)
* [Stacks Project, Tag 0G24](https://stacks.math.columbia.edu/tag/0G24)
* [Stacks Project, Tag 0GWZ](https://stacks.math.columbia.edu/tag/0GWZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.DerivedVarieties.Orlov

attribute [local instance 100000] HasDerivedCategory.standard

/-- A bounded above complex with some nonzero cohomology in degree `> b` has a top nonzero
cohomology degree `t > b`, and lies in degrees `≤ t`. -/
private theorem exists_isLE_not_isZero_homology {A : Type u} [CommRing A]
    (P : DerivedCategory (ModuleCat.{u} A)) (b : ℤ)
    (hbdd : ∃ c : ℤ, ∀ i : ℤ, c < i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj P))
    (hne : ∃ n : ℤ, b < n ∧
      ¬ IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj P)) :
    ∃ t : ℤ, b < t ∧ ¬ IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) t).obj P) ∧
      P.IsLE t := by
  classical
  obtain ⟨c, hc⟩ := hbdd
  obtain ⟨t, ⟨htb, ht⟩, htop⟩ := Int.exists_greatest_of_bdd (P := fun n => b < n ∧
      ¬ IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj P))
    ⟨c, fun n hn => not_lt.mp fun hlt => hn.2 (hc n hlt)⟩ hne
  refine ⟨t, htb, ht, ?_⟩
  rw [DerivedCategory.isLE_iff]
  intro j hj
  by_contra hnz
  have := htop j ⟨by omega, hnz⟩
  omega

/-! ### Local algebra -/

section Local

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- **A nonzero finite module over a local ring maps nontrivially to the residue field**
`κ = A_𝔪 / 𝔪A_𝔪`, by Nakayama's lemma. -/
@[ega "IV 2.5.5.4" "more general"]
theorem exists_linearMap_residueField_ne_zero (M : Type u) [AddCommGroup M] [Module A M]
    [Module.Finite A M] [Nontrivial M] :
    ∃ f : M →ₗ[A] (IsLocalRing.maximalIdeal A).ResidueField, f ≠ 0 := by
  have : Nontrivial (TensorProduct A (IsLocalRing.ResidueField A) M) :=
    not_subsingleton_iff_nontrivial.mp fun h =>
      not_nontrivial_iff_subsingleton.mpr ((IsLocalRing.subsingleton_tensorProduct (R := A)).mp h)
        inferInstance
  obtain ⟨z, hz⟩ := exists_ne (0 : TensorProduct A (IsLocalRing.ResidueField A) M)
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual (IsLocalRing.ResidueField A)
      (TensorProduct A (IsLocalRing.ResidueField A) M), φ z ≠ 0 := by
    by_contra! h
    exact hz ((Module.forall_dual_apply_eq_zero_iff (IsLocalRing.ResidueField A) z).mp h)
  let ι : IsLocalRing.ResidueField A →ₗ[A] (IsLocalRing.maximalIdeal A).ResidueField :=
    (IsScalarTower.toAlgHom A (A ⧸ IsLocalRing.maximalIdeal A)
      (IsLocalRing.maximalIdeal A).ResidueField).toLinearMap
  have hι : Function.Injective ι :=
    (IsLocalRing.maximalIdeal A).bijective_algebraMap_quotient_residueField.1
  refine ⟨ι.comp ((φ.restrictScalars A).comp
    (TensorProduct.mk A (IsLocalRing.ResidueField A) M 1)), fun hμ => hφ ?_⟩
  have hμ' :
      (φ.restrictScalars A).comp (TensorProduct.mk A (IsLocalRing.ResidueField A) M 1) = 0 := by
    ext m
    exact hι (by simpa using congrArg (fun f => f m) hμ)
  have hzero : ∀ y : TensorProduct A (IsLocalRing.ResidueField A) M, φ y = 0 := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a m =>
        have hm := congrArg (fun f : M →ₗ[A] IsLocalRing.ResidueField A => f m) hμ'
        simp only [LinearMap.coe_comp, Function.comp_apply, TensorProduct.mk_apply,
          LinearMap.coe_restrictScalars, LinearMap.zero_apply] at hm
        rw [← mul_one a, ← smul_eq_mul, ← TensorProduct.smul_tmul', map_smul, hm, smul_zero]
    | add y y' hy hy' => rw [map_add, hy, hy', add_zero]
  exact hzero z

variable (A)

/-- The residue field `κ = A_𝔪 / 𝔪A_𝔪` of a local ring, as an object of `Mod_A`. -/
abbrev residueFieldObj : ModuleCat.{u} A := residueFieldModuleCat (IsLocalRing.maximalIdeal A)

variable {A}

/-- **A complex in degrees `≤ t` over a local ring whose `H^t` is a nonzero finite module has a
nonzero map to `N[-t]`, for any module `N` containing the residue field**: compose
`P ⟶ τ_{≥ t}P = H^t(P)[-t]` with a nonzero map `H^t(P) ⟶ κ ⊆ N` (Nakayama). -/
theorem exists_hom_shift_ne_zero_of_isLE (P : DerivedCategory (ModuleCat.{u} A)) (t : ℤ)
    (hLE : P.IsLE t) (ht : ¬ IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) t).obj P))
    (hfin : Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) t).obj P))
    (N : ModuleCat.{u} A) (j : residueFieldObj A ⟶ N) (hj : Function.Injective j.hom) :
    ¬ Subsingleton (P ⟶ ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N)⟦-t⟧) := by
  intro hsub
  let H := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) t).obj P
  have : Nontrivial H :=
    not_subsingleton_iff_nontrivial.mp fun _ => ht (ModuleCat.isZero_of_subsingleton _)
  obtain ⟨f₀, hf₀⟩ := exists_linearMap_residueField_ne_zero (A := A) H
  let f : H →ₗ[A] N := j.hom ∘ₗ f₀
  have hf : f ≠ 0 := fun h0 =>
    hf₀ (LinearMap.ext fun m => hj ((LinearMap.congr_fun h0 m).trans j.hom.map_zero.symm))
  -- The truncation `P ⟶ τ_{≥ t} P ≅ M[-t]`, an isomorphism on `H^t`.
  let tS := DerivedCategory.TStructure.t (C := ModuleCat.{u} A)
  let V := (tS.truncGE t).obj P
  have : tS.IsGE V t := by dsimp [V]; infer_instance
  have : tS.IsLE V t := by dsimp [V]; infer_instance
  obtain ⟨M, ⟨eV⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE V t
  let HF := DerivedCategory.homologyFunctor (ModuleCat.{u} A) t
  let π : P ⟶ V := (tS.truncGEπ t).app P
  have : IsIso (HF.map π) := DerivedCategory.isIso_homologyFunctor_map_truncGEπ t t le_rfl P
  let ε := DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} A) t
  let α : H ≅ M := asIso (HF.map π) ≪≫ HF.mapIso eV ≪≫ ε.app M
  let fH : H ⟶ N := ModuleCat.ofHom f
  let f' : M ⟶ N := α.inv ≫ fH
  let g : P ⟶ (DerivedCategory.singleFunctor (ModuleCat.{u} A) t).obj (N) :=
    π ≫ eV.hom ≫ (DerivedCategory.singleFunctor (ModuleCat.{u} A) t).map f'
  have hg : HF.map g ≫ ε.hom.app (N) = fH := by
    have hnat := ε.hom.naturality f'
    simp only [Functor.comp_map, Functor.id_map] at hnat
    simp only [g, Functor.map_comp, Category.assoc]
    change HF.map π ≫ HF.map eV.hom ≫ (HF.map ((DerivedCategory.singleFunctor _ t).map f') ≫
      ε.hom.app (N)) = _
    rw [hnat]
    simp only [f', α, Iso.trans_inv, asIso_inv, Functor.mapIso_inv, Iso.app_inv, Category.assoc,
      Iso.hom_inv_id_app_assoc]
    rw [← Functor.map_comp_assoc HF eV.hom eV.inv, eV.hom_inv_id]
    simp
  have hg0 : g ≠ 0 := fun h0 => by
    rw [h0, Functor.map_zero, Limits.zero_comp] at hg
    exact hf (congrArg ModuleCat.Hom.hom hg).symm
  let eS : ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (N))⟦-t⟧ ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) t).obj (N) :=
    ((DerivedCategory.singleFunctors (ModuleCat.{u} A)).shiftIso (-t) t 0 (by omega)).app _
  exact hg0 (by simpa using congrArg (· ≫ eS.hom) (hsub.elim (g ≫ eS.inv) 0))

/-- **A bounded above complex with finite cohomology over a local ring which admits no nonzero
map to any shift of a module `N` containing the residue field is zero.** -/
theorem isZero_of_forall_hom_shift_of_injective (P : DerivedCategory (ModuleCat.{u} A))
    (N : ModuleCat.{u} A) (j : residueFieldObj A ⟶ N) (hj : Function.Injective j.hom)
    (hbdd : ∃ b : ℤ, ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj P))
    (hfin : ∀ i : ℤ, Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj P))
    (h : ∀ i : ℤ, Subsingleton
      (P ⟶ ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N)⟦i⟧)) :
    IsZero P := by
  apply DerivedCategory.isZero_of_forall_isZero_homology
  by_contra hne
  push Not at hne
  obtain ⟨n, hn⟩ := hne
  obtain ⟨t, -, ht, hLE⟩ := exists_isLE_not_isZero_homology P (n - 1) hbdd ⟨n, by omega, hn⟩
  exact exists_hom_shift_ne_zero_of_isLE P t hLE ht (hfin t) N j hj (h (-t))

/-- **Amplitude over a local ring, tested against the residue field**: a bounded above complex
with finite cohomology lies in degrees `≤ b` as soon as it has no nonzero map to `κ[-i]` for any
`i > b`. -/
theorem isLE_of_forall_hom_shift_residueField (P : DerivedCategory (ModuleCat.{u} A)) (b : ℤ)
    (hbdd : ∃ c : ℤ, ∀ i : ℤ, c < i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj P))
    (hfin : ∀ i : ℤ, Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj P))
    (h : ∀ i : ℤ, b < i → Subsingleton
      (P ⟶ ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (residueFieldObj A))⟦-i⟧)) :
    P.IsLE b := by
  rw [DerivedCategory.isLE_iff]
  by_contra hne
  push Not at hne
  obtain ⟨t, htb, ht, hLE⟩ := exists_isLE_not_isZero_homology P b hbdd hne
  exact exists_hom_shift_ne_zero_of_isLE P t hLE ht (hfin t) _ (𝟙 _) Function.injective_id
    (h t htb)

/-- **A bounded above complex with finite cohomology over a local ring which admits no nonzero
map to any shift of the residue field is zero.** -/
theorem isZero_of_forall_hom_shift_residueField (P : DerivedCategory (ModuleCat.{u} A))
    (hbdd : ∃ b : ℤ, ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj P))
    (hfin : ∀ i : ℤ, Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj P))
    (h : ∀ i : ℤ, Subsingleton
      (P ⟶ ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (residueFieldObj A))⟦i⟧)) :
    IsZero P :=
  isZero_of_forall_hom_shift_of_injective P _ (𝟙 _) Function.injective_id hbdd hfin h

end Local

/-! ### Maps into residue-field skyscrapers -/

section Global

variable (X : Scheme.{u}) (x : X)

/-- The skyscraper sheaf `𝒪_x` at `x` with value `κ(x)`, placed in degree `0` of `D(𝒪_X)`. -/
abbrev pointSheaf : DerivedCategory X.Modules :=
  (DerivedCategory.singleFunctor X.Modules 0).obj (residueFieldSkyscraperSheaf X x)

/-- The derived stalk functor `D(𝒪_X) ⥤ D(𝒪_{X,x})`. -/
abbrev derivedStalk :
    DerivedCategory X.Modules ⥤
      DerivedCategory (ModuleCat.{u} (ToType (StacksDraft.StalkRingComparison.stalkRing X x))) :=
  (SheafOfModules.stalkFunctor X.ringCatSheaf x).mapDerivedCategory

/-- `𝒪_x[i]` is the derived skyscraper of `κ(x)[i]`. -/
def pointSheafShiftIso (i : ℤ) :
    (pointSheaf X x)⟦i⟧ ≅ (SheafOfModules.skyscraperFunctor X.ringCatSheaf x).mapDerivedCategory.obj
      (((DerivedCategory.singleFunctor _ 0).obj (residueFieldStalkModule X x))⟦i⟧) :=
  (shiftFunctor _ i).mapIso
      (((SheafOfModules.skyscraperFunctor X.ringCatSheaf x).mapDerivedCategorySingleFunctor 0).app
        (residueFieldStalkModule X x)).symm ≪≫
    (((SheafOfModules.skyscraperFunctor X.ringCatSheaf x).mapDerivedCategory.commShiftIso i).app
      _).symm

/-- **Maps into `𝒪_x[i]` are maps out of the derived stalk into `κ(x)[i]`**: the stalk functor
at `x` is left adjoint to the skyscraper functor at `x`, and both are exact. -/
def homPointSheafShiftEquiv (K : DerivedCategory X.Modules) (i : ℤ) :
    (K ⟶ (pointSheaf X x)⟦i⟧) ≃
      ((derivedStalk X x).obj K ⟶
        ((DerivedCategory.singleFunctor _ 0).obj (residueFieldStalkModule X x))⟦i⟧) :=
  (Iso.homCongr (Iso.refl K) (pointSheafShiftIso X x i)).trans
    ((StacksDraft.DerivedRingIso.mapDerivedCategoryAdjunction
      (SheafOfModules.stalkSkyscraperAdjunction X.ringCatSheaf x)).homEquiv _ _).symm

/-- **A perfect complex orthogonal to all shifts of `𝒪_x` has zero derived stalk at `x`.** -/
theorem isZero_derivedStalk_of_forall_hom_pointSheaf_shift [IsNoetherian X]
    (K : DerivedCategory X.Modules) (hK : RingedSpace.IsPerfect (X := X.toRingedSpace) K)
    (h : ∀ i : ℤ, Subsingleton (K ⟶ (pointSheaf X x)⟦i⟧)) :
    IsZero ((derivedStalk X x).obj K) := by
  have hpc := @Stacks.AlgebraicGeometry.DerivedStalk.isPseudoCoherent_derivedStalk_of_isPerfect
    X inferInstance x (StacksDraft.StalkRingComparison.isNoetherianRing_stalkRing X x) K hK
  obtain ⟨hbdd, hfin⟩ :=
    (@StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology
      (ToType (StacksDraft.StalkRingComparison.stalkRing X x)) _
      (StacksDraft.StalkRingComparison.isNoetherianRing_stalkRing X x) _
      ((derivedStalk X x).obj K) 0 (ToType (StacksDraft.StalkRingComparison.stalkRing X x))
      _ _).2.1.1 hpc
  exact isZero_of_forall_hom_shift_residueField _ hbdd hfin
    (fun i => (homPointSheafShiftEquiv X x K i).symm.injective.subsingleton)

/-- **A perfect complex on a Noetherian scheme is zero as soon as all its derived stalks at closed
points are.** Each cohomology sheaf is of finite type, so its support is closed; a nonempty
closed subset of a quasi-compact scheme contains a closed point. -/
theorem isZero_of_forall_isClosed_isZero_derivedStalk [IsNoetherian X]
    (K : DerivedCategory X.Modules) (hK : RingedSpace.IsPerfect (X := X.toRingedSpace) K)
    (h : ∀ x : X, IsClosed ({x} : Set X) → IsZero ((derivedStalk X x).obj K)) :
    IsZero K := by
  have hbc := Stacks.AlgebraicGeometry.PerfectCohomology.isBoundedCoherent_of_isPerfect X K hK
  have hstalk : ∀ (i : ℤ) (y : X), IsZero ((SheafOfModules.stalkFunctor X.ringCatSheaf y).obj
      ((DerivedCategory.homologyFunctor X.Modules i).obj K)) := by
    intro i y
    let H := (DerivedCategory.homologyFunctor X.Modules i).obj K
    have : H.IsFiniteType := (hbc.2 i).isFiniteType
    have hclosed : IsClosed (SheafOfModules.supp H) :=
      Stacks.AlgebraicGeometry.DevissageNoetherian.isClosed_supp X.sheaf H
    have hzero : ∀ z : X, IsClosed ({z} : Set X) →
        IsZero ((SheafOfModules.stalkFunctor X.ringCatSheaf z).obj H) := fun z hz =>
      ((Functor.map_isZero (DerivedCategory.homologyFunctor _ i) (h z hz)).of_iso
        (((SheafOfModules.stalkFunctor X.ringCatSheaf z).mapDerivedCategoryHomologyIso i).app
          K).symm)
    have key : ∀ z : X, z ∈ SheafOfModules.supp H ↔
        ¬ IsZero ((SheafOfModules.stalkFunctor X.ringCatSheaf z).obj H) := by
      intro z
      refine (SheafOfModules.mem_supp_iff_nontrivial_stalk (R := X.ringCatSheaf) H z).trans ?_
      refine Iff.trans ?_ (not_congr (SheafOfModules.isZero_stalkFunctor_obj_iff
        X.ringCatSheaf z H).symm)
      rw [AddCommGrpCat.isZero_iff_subsingleton, not_subsingleton_iff_nontrivial]
    by_contra hy
    have hyS : y ∈ SheafOfModules.supp H := (key y).2 hy
    obtain ⟨z, hz, hzclosed⟩ := (isClosed_closure (s := ({y} : Set X))).exists_closed_singleton
      ⟨y, subset_closure rfl⟩
    have hzS : z ∈ SheafOfModules.supp H :=
      (closure_minimal (Set.singleton_subset_iff.2 hyS) hclosed) hz
    exact (key z).1 hzS (hzero z hzclosed)
  have : IsIso (0 : K ⟶ K) :=
    Stacks.Cohomology.StalkwiseIso.isIso_of_forall_stalk_isIso X.ringCatSheaf _ fun i y =>
      ⟨0, (hstalk i y).eq_of_src _ _, (hstalk i y).eq_of_src _ _⟩
  exact IsZero.of_mono_zero K K

/-- **[Stacks, Tag 0G03] part (4), globally**: a perfect complex `K` on a Noetherian scheme with
`Hom(K, 𝒪_x[i]) = 0` for every closed point `x` and every `i ∈ ℤ` is zero. -/
theorem isZero_of_forall_hom_pointSheaf_shift [IsNoetherian X]
    (K : DerivedCategory X.Modules) (hK : RingedSpace.IsPerfect (X := X.toRingedSpace) K)
    (h : ∀ x : X, IsClosed ({x} : Set X) → ∀ i : ℤ, Subsingleton (K ⟶ (pointSheaf X x)⟦i⟧)) :
    IsZero K :=
  isZero_of_forall_isClosed_isZero_derivedStalk X K hK fun x hx =>
    isZero_derivedStalk_of_forall_hom_pointSheaf_shift X x K hK (h x hx)

end Global

end Stacks.AlgebraicGeometry.DerivedVarieties.Orlov

end
