module

public import StacksCore.LinearAlgebra.Matrix.CommSemiring
public import StacksFrontier.RingTheory.Tor.AlmostFlatResolution
public import StacksFrontier.RingTheory.Tor.Balancing
public import StacksFrontier.RingTheory.Tor.Flatness
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.RingTheory.Flat.TorCriterion.Tor1Vanishing
import all StacksFrontier.RingTheory.Flat.TorCriterion.Tor1Vanishing

/-!
# Flatness criteria through the vanishing of `Tor₁`

Let `R` be a commutative ring, `I ⊆ R` an ideal and `M` an `R`-module such that `M/IM` is flat over
`R/I` and `Tor₁^R(R/I, M) = 0`. Then `Tor₁^R(N, M) = 0` for every `R`-module `N` annihilated by a
power of `I`, the module `M/IⁿM` is flat over `R/Iⁿ` for every `n ≥ 1`, and `M` is flat over `R`
if `I` is nilpotent.

## Main results

* `tor1_vanishes_of_annihilated`: `Tor₁^R(N, M) = 0` for every `N` annihilated by a power of `I`.
* `flat_quotient_pow`: `M/IⁿM` is flat over `R/Iⁿ` for every `n ≥ 1`.
* `flat_of_nilpotent`: `M` is flat over `R` when `I` is nilpotent.
* `flat_of_tor1_quotient_vanishes`: `M` is flat if `Tor₁^R(R/J, M) = 0` for every ideal `J`.

## References

* [Stacks Project, Tag 051C](https://stacks.math.columbia.edu/tag/051C)
-/

@[expose] public section

open CategoryTheory TensorProduct

universe u

section FlatBridge

variable {R : Type u} [CommRing R]
variable {M : Type u} [AddCommGroup M] [Module R M]

end FlatBridge

/-! ## Flatness of `M ⧸ J M` over `R ⧸ J` -/

section BaseChangeFlat

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {M : Type u} [AddCommGroup M] [Module R M]

set_option backward.isDefEq.respectTransparency false in
open Tor1VanishesAux CategoryTheory.Limits in
/-- If, for a projective resolution `Pr` of `M`, the map induced on degree-`0` homology by
`P ↪ Fr` after tensoring with `Pr` is a monomorphism, then `rTensor M P.subtype` is injective. -/
theorem Stacks.Flatness.TorCriterion.rTensor_subtype_injective_of_tor0_homologyMap_mono
    {Fr : Type u} [AddCommGroup Fr] [Module R Fr] (P : Submodule R Fr)
    (Pr : ProjectiveResolution (ModuleCat.of R M))
    (hmono : Mono (HomologicalComplex.homologyMap ((shortCx P).map (torPhi Pr.complex)).f 0)) :
    Function.Injective (LinearMap.rTensor M P.subtype) := by
  set S := (shortCx P).map (torPhi Pr.complex) with hSdef
  have hsq : HomologicalComplex.opcyclesMap S.f 0 ≫ (cokerIso Pr (ModuleCat.of R Fr)).hom
      = (cokerIso Pr (ModuleCat.of R P)).hom ≫ ModuleCat.ofHom (LinearMap.rTensor M P.subtype) := by
    have hepi : Epi (S.X₁.pOpcycles 0) := inferInstance
    rw [← cancel_epi (S.X₁.pOpcycles 0)]
    have hPF : S.X₁.pOpcycles 0 ≫ HomologicalComplex.opcyclesMap S.f 0
        = S.f.f 0 ≫ S.X₂.pOpcycles 0 := HomologicalComplex.p_opcyclesMap S.f 0
    have hcfr : S.X₂.pOpcycles 0 ≫ (cokerIso Pr (ModuleCat.of R Fr)).hom = augX Pr (ModuleCat.of R
        Fr) :=
      pOpcycles_cokerIso Pr (ModuleCat.of R Fr)
    have hcp : S.X₁.pOpcycles 0 ≫ (cokerIso Pr (ModuleCat.of R P)).hom = augX Pr (ModuleCat.of R P)
        :=
      pOpcycles_cokerIso Pr (ModuleCat.of R P)
    calc S.X₁.pOpcycles 0 ≫ HomologicalComplex.opcyclesMap S.f 0 ≫
          (cokerIso Pr (ModuleCat.of R Fr)).hom
        = (S.X₁.pOpcycles 0 ≫ HomologicalComplex.opcyclesMap S.f 0) ≫
          (cokerIso Pr (ModuleCat.of R Fr)).hom := by
          rw [Category.assoc]
      _ = S.f.f 0 ≫ (S.X₂.pOpcycles 0 ≫ (cokerIso Pr (ModuleCat.of R Fr)).hom) := by
          rw [hPF, Category.assoc]
      _ = S.f.f 0 ≫ augX Pr (ModuleCat.of R Fr) := by rw [hcfr]
      _ = augX Pr (ModuleCat.of R P) ≫ ModuleCat.ofHom (LinearMap.rTensor M P.subtype) :=
          augX_naturality P Pr
      _ = (S.X₁.pOpcycles 0 ≫ (cokerIso Pr (ModuleCat.of R P)).hom) ≫
          ModuleCat.ofHom (LinearMap.rTensor M P.subtype) := by
          rw [hcp]
      _ = S.X₁.pOpcycles 0 ≫ (cokerIso Pr (ModuleCat.of R P)).hom ≫
          ModuleCat.ofHom (LinearMap.rTensor M P.subtype) := by
          rw [Category.assoc]
  have hn : (ComplexShape.down ℕ).next 0 = 0 := by
    apply ComplexShape.next_eq_self; intro h; simp [ComplexShape.down] at h
  have hiso1 : IsIso (S.X₁.homologyι 0) := by
    have hd : S.X₁.d 0 0 = 0 := S.X₁.shape 0 0 (by simp [ComplexShape.down])
    rw [← S.X₁.isoHomologyι_hom 0 0 hn hd]; infer_instance
  have hiso2 : IsIso (S.X₂.homologyι 0) := by
    have hd : S.X₂.d 0 0 = 0 := S.X₂.shape 0 0 (by simp [ComplexShape.down])
    rw [← S.X₂.isoHomologyι_hom 0 0 hn hd]; infer_instance
  have hnat := HomologicalComplex.homologyι_naturality S.f 0
  have heq : HomologicalComplex.homologyMap S.f 0
      = S.X₁.homologyι 0 ≫ HomologicalComplex.opcyclesMap S.f 0 ≫ inv (S.X₂.homologyι 0) := by
    rw [← Category.assoc, ← hnat, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have := hmono
  have hmono_op : Mono (HomologicalComplex.opcyclesMap S.f 0) := by
    have : Mono (S.X₁.homologyι 0 ≫ HomologicalComplex.opcyclesMap S.f 0) :=
      mono_of_mono_fac (show (S.X₁.homologyι 0 ≫ HomologicalComplex.opcyclesMap S.f 0) ≫
        inv (S.X₂.homologyι 0) = HomologicalComplex.homologyMap S.f 0 by rw [heq, Category.assoc])
    exact (mono_comp_iff_of_isIso (S.X₁.homologyι 0) _).mp this
  have hrt_mono : Mono (ModuleCat.ofHom (LinearMap.rTensor M P.subtype)) := by
    have : Mono ((cokerIso Pr (ModuleCat.of R P)).hom ≫
        ModuleCat.ofHom (LinearMap.rTensor M P.subtype)) := by
      rw [← hsq]
      exact mono_comp _ _
    exact (mono_comp_iff_of_isIso _ _).mp this
  exact (ModuleCat.mono_iff_injective (ModuleCat.ofHom (LinearMap.rTensor M P.subtype))).mp hrt_mono

open Tor1VanishesAux CategoryTheory.Limits in
/-- If `Tor₁^R(Fr ⧸ P, M) = 0`, then `rTensor M P.subtype : P ⊗_R M → Fr ⊗_R M` is injective. -/
public theorem rTensor_subtype_injective_of_tor1_vanishes
    {Fr : Type u} [AddCommGroup Fr] [Module R Fr] (P : Submodule R Fr)
    (hQ : Tor1Vanishes R (Fr ⧸ P) M) :
    Function.Injective (LinearMap.rTensor M P.subtype) := by
  let Pr : ProjectiveResolution (ModuleCat.of R M) := ProjectiveResolution.of (ModuleCat.of R M)
  set S := (shortCx P).map (torPhi Pr.complex) with hSdef
  have hS : S.ShortExact := mappedSES_shortExact P Pr
  have hrel : (ComplexShape.down ℕ).Rel 1 0 := by simp [ComplexShape.down]
  have hX3 : Limits.IsZero (S.X₃.homology 1) :=
    Limits.IsZero.of_iso hQ (torIsoHomology Pr (Fr ⧸ P)).symm
  have hδ0 : hS.δ 1 0 hrel = 0 := hX3.eq_of_src _ _
  have e1 := hS.homology_exact₁ 1 0 hrel
  have hmono : Mono (HomologicalComplex.homologyMap S.f 0) := e1.mono_g hδ0
  exact Stacks.Flatness.TorCriterion.rTensor_subtype_injective_of_tor0_homologyMap_mono P Pr hmono

/-- For `R ⧸ J`-modules `X, Y` and an `R ⧸ J`-linear map `f : X → Y`, if
`rTensor M (f.restrictScalars R)` is injective then so is `rTensor ((R ⧸ J) ⊗_R M) f`. -/
private theorem rTensor_restrictScalars_injective'
    (J : Ideal R)
    {X Y : Type u} [AddCommGroup X] [Module R X] [Module (R ⧸ J) X] [IsScalarTower R (R ⧸ J) X]
    [AddCommGroup Y] [Module R Y] [Module (R ⧸ J) Y] [IsScalarTower R (R ⧸ J) Y]
    (f : X →ₗ[R ⧸ J] Y)
    (hfM : Function.Injective (LinearMap.rTensor M (f.restrictScalars R))) :
    Function.Injective (LinearMap.rTensor ((R⧸J) ⊗[R] M) f) := by
  let eX := TensorProduct.AlgebraTensorModule.cancelBaseChange R (R⧸J) (R⧸J) X M
  let eY := TensorProduct.AlgebraTensorModule.cancelBaseChange R (R⧸J) (R⧸J) Y M
  have hnat : ∀ t : X ⊗[R⧸J] ((R⧸J) ⊗[R] M),
      (LinearMap.rTensor M (f.restrictScalars R)) (eX t)
        = eY ((LinearMap.rTensor ((R⧸J) ⊗[R] M) f) t) := by
    intro t
    induction t with
    | zero => simp
    | tmul x m' =>
        induction m' with
        | zero => simp
        | tmul a m =>
            show (LinearMap.rTensor M (f.restrictScalars R)) (eX (x ⊗ₜ[R⧸J] (a ⊗ₜ[R] m)))
              = eY ((LinearMap.rTensor ((R⧸J) ⊗[R] M) f) (x ⊗ₜ[R⧸J] (a ⊗ₜ[R] m)))
            rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
            rw [LinearMap.rTensor_tmul, LinearMap.rTensor_tmul]
            simp only [LinearMap.restrictScalars_apply, map_smul]
            rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
        | add a b ha hb => simp only [TensorProduct.tmul_add, map_add, ha, hb]
    | add a b ha hb => simp only [map_add, ha, hb]
  intro u v huv
  apply eX.injective
  apply hfM
  rw [hnat, hnat, huv]

/-- If `Tor₁^R(N, M) = 0` for every `R`-module `N` annihilated by the ideal `J`, then `M ⧸ JM` is
flat over `R ⧸ J`. -/
@[ega "0 6.1.1" "Implication c) ⇒ a)",
  sga "1 IV 5.2" "(i), special case",
  sga "1 IV 5.3" "(iii)",
  sga "1 IV 5.4"]
theorem flat_quotient_of_tor1_vanishes
    {J : Ideal R}
    (hKill : ∀ N : Type u, ∀ _ : AddCommGroup N, ∀ _ : Module R N,
        J • (⊤ : Submodule R N) = ⊥ → Tor1Vanishes R N M) :
    Module.Flat (R ⧸ J) (M ⧸ (J • (⊤ : Submodule R M))) := by
  have hflat : Module.Flat (R ⧸ J) ((R ⧸ J) ⊗[R] M) := by
    rw [Module.Flat.iff_rTensor_injective']
    intro K
    apply rTensor_restrictScalars_injective' J K.subtype
    set P : Submodule R (R ⧸ J) := K.restrictScalars R with hPdef
    show Function.Injective (LinearMap.rTensor M (P.subtype))
    have hkill : J • (⊤ : Submodule R ((R ⧸ J) ⧸ P)) = ⊥ := by
      rw [eq_bot_iff, Submodule.smul_le]
      intro r hr x _
      rw [Submodule.mem_bot]
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective P x
      rw [← Submodule.Quotient.mk_smul]
      have : r • z = 0 := by
        obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
        rw [show r • (Ideal.Quotient.mk J w) = (Ideal.Quotient.mk J r) * (Ideal.Quotient.mk J w) by
          rw [← map_mul]; rfl]
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr, zero_mul]
      rw [this, Submodule.Quotient.mk_zero]
    have hQ : Tor1Vanishes R ((R ⧸ J) ⧸ P) M := hKill ((R ⧸ J) ⧸ P) _ _ hkill
    exact rTensor_subtype_injective_of_tor1_vanishes P hQ
  exact Module.Flat.of_linearEquiv (quotTensorRIEquiv J).symm

end BaseChangeFlat

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {M : Type u} [AddCommGroup M] [Module R M]

/-- If `Tor₁^R(R/J, M) = 0` for every ideal `J ⊆ R`, then `M` is flat over `R`. -/
@[ega "0 6.1.1" "more general",
  sga "1 IV 5.2" "B = A: (i) ⇒ (ii)",
  sga "4 XVII 4.1.9" "special case",
  sga "6 I 5.1.1" "special case"]
theorem flat_of_tor1_quotient_vanishes
    (h : ∀ J : Ideal R, Tor1Vanishes R (R ⧸ J) M) :
    Module.Flat R M := by
  rw [Module.Flat.iff_rTensor_injective']
  intro J
  exact rTensor_subtype_injective_of_tor1_vanishes (R := R) (M := M) (Fr := R) J (h J)

/-- If `M/IM` is flat over `R/I` and `Tor₁^R(R/I, M) = 0`, then `Tor₁^R(N, M) = 0` for every
`R`-module `N` annihilated by `Iᵐ` for some `m`. -/
@[stacks 051C "(2)",
  sga "1 IV 5.3" "=> (iii)",
  sga "1 IV 5.2" "(ii) ⇒ (i), special case",
  sga "3 VIB 12.7" "partial"]
theorem tor1_vanishes_of_annihilated
    (H1 : Module.Flat (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))))
    (H2 : Tor1Vanishes R (R ⧸ I) M)
    (N : Type u) [AddCommGroup N] [Module R N]
    (m : ℕ) (hN : (I ^ m) • (⊤ : Submodule R N) = ⊥) :
    Tor1Vanishes R N M := by
  induction m generalizing N with
  | zero =>
    rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul] at hN
    have : Subsingleton N := ⟨fun a b => by
      have ha : a ∈ (⊤ : Submodule R N) := Submodule.mem_top
      have hb : b ∈ (⊤ : Submodule R N) := Submodule.mem_top
      rw [hN, Submodule.mem_bot] at ha hb
      rw [ha, hb]⟩
    exact tor1_isZero_of_subsingleton N
  | succ k ih =>
    set P : Submodule R N := I • (⊤ : Submodule R N) with hPdef
    have hkP : I ^ k • P = ⊥ := by
      rw [hPdef, smul_smul, ← pow_succ]
      exact hN
    have hPtop : (I ^ k) • (⊤ : Submodule R P) = ⊥ := by
      have hmap : ((I ^ k) • (⊤ : Submodule R P)).map P.subtype = I ^ k • P := by
        rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype]
      have hinj : Function.Injective (Submodule.map P.subtype) :=
        Submodule.map_injective_of_injective Subtype.coe_injective
      apply hinj
      rw [Submodule.map_bot, hmap, hkP]
    have ha : Tor1Vanishes R P M := ih P hPtop
    have hQkill : I • (⊤ : Submodule R (N ⧸ P)) = ⊥ := by
      have hmap : I • (⊤ : Submodule R (N ⧸ P)) = (I • (⊤ : Submodule R N)).map P.mkQ := by
        rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
      rw [hmap, ← hPdef, Submodule.mkQ_map_self]
    have hb : Tor1Vanishes R (N ⧸ P) M := tor1_vanishes_of_smul_eq_bot I H1 H2 (N ⧸ P) hQkill
    exact tor1_vanishes_of_submodule N P ha hb

/-- If `M/IM` is flat over `R/I` and `Tor₁^R(R/I, M) = 0`, then for every `n ≥ 1` the
`R/Iⁿ`-module `M/IⁿM` is flat over `R/Iⁿ`. -/
@[stacks 051C "(1)",
  ega "0 10.2.1" "(b) ⇒ (d)",
  ega "0 10.2.2" "b ⇒ d",
  sga "1 IV 5.5" "more general",
  sga "1 IV 5.6" "(ii)⇒(iv)",
  sga "3 VIB 12.7" "more general"]
theorem flat_quotient_pow
    (H1 : Module.Flat (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))))
    (H2 : Tor1Vanishes R (R ⧸ I) M) :
    ∀ n : ℕ, 1 ≤ n →
      Module.Flat (R ⧸ I ^ n) (M ⧸ ((I ^ n) • (⊤ : Submodule R M))) := by
  intro n hn
  exact flat_quotient_of_tor1_vanishes
    (fun N _ _ hN => tor1_vanishes_of_annihilated I H1 H2 N n hN)

/-- If `M/IM` is flat over `R/I`, `Tor₁^R(R/I, M) = 0` and `I` is nilpotent, then `M` is flat
over `R`. -/
@[stacks 051C "in particular",
  sga "1 IV 5.5" "(ii) => (i)",
  ega "0 10.2.1" "(b)⇒(a), 𝔍 nilpotent",
  ega "0 10.1.3" "(i)",
  ega "0 10.2.2" "special case",
  ega "IV 11.2.5" "special case",
  ega "IV 11.3.12" "b⇒a when J is nilpotent", sga "1 IV 5.6" "(ii)⇒(i), special case"]
theorem flat_of_nilpotent
    (H1 : Module.Flat (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))))
    (H2 : Tor1Vanishes R (R ⧸ I) M)
    (hI : ∃ n : ℕ, 1 ≤ n ∧ I ^ n = ⊥) :
    Module.Flat R M := by
  obtain ⟨n, _, hn⟩ := hI
  apply flat_of_tor1_quotient_vanishes
  intro J
  apply tor1_vanishes_of_annihilated I H1 H2 (R ⧸ J) n
  rw [hn]
  simp
