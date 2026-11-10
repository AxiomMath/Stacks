module

public import StacksFrontier.RingTheory.SpreadingOut.FlatIdeal
public import StacksFrontier.RingTheory.SpreadingOut.QuotientSystem
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The local criterion for flatness for local maps essentially of finite presentation

Let `R → S` be a local homomorphism of local rings which is essentially of finite presentation,
let `I ≠ R` be an ideal of `R` and let `M` be an `S`-module of finite presentation, viewed as an
`R`-module. If `I ⊗_R M → R ⊗_R M` is injective — the form Remark 00M6 gives the vanishing of
`Tor_1^R(R/I, M)` — and `M/IM` is flat over `R/I`, then `M` is flat over `R`.

## Main results

* `Module.Flat.of_rTensor_subtype_injective_of_flat_quotient_of_essentiallyOfFinitePresentation`:
  the local criterion for flatness for a local map essentially of finite presentation, as above.

## Implementation notes

By 00QX the datum `R → S`, `M` is a filtered colimit of data `A λ → B λ`, `N λ` over Noetherian
local rings with `N λ` finite. `Module.Flat.exists_ge_flat_quotient_of_isColimit` says that the
quotient system is flat at cofinally many stages, which is the hypothesis of
`Module.Flat.exists_ge_flat_of_isColimit_of_rTensor_subtype_injective`; that lemma makes `N λ`
itself flat over `A λ` at cofinally many stages, and
`Module.Flat.of_isColimit_of_forall_exists_ge_flat` turns cofinal flatness into flatness over the
colimit. That argument needs `R`, `S` and `M` in a single universe, because 00QX produces a system
indexed by a type in that universe and functors to `CommRingCat` and `AddCommGrpCat` there.

The statement has them in three independent universes. They are lifted into `Type (max u v w)`
with `ULift`, and the hypotheses carried across:

* flatness, and finite presentation, transport along a ring isomorphism by transitivity — the
  target is a flat, resp. finitely presented, module over the source through the isomorphism —
  which is `flat_of_ringEquiv` and `Module.FinitePresentation.trans`;
* the essential finite presentation of `R → S` transports by re-presenting the intermediate
  finitely presented algebra in the lifted universe;
* the quotient flatness transports by `flat_quotient_of_equiv`: the two quotients `M'/I'M'` and
  `M/IM` correspond under the isomorphism, `I'` being the inverse image of `I`;
* the `Tor` hypothesis transports by `sum_tmul_eq_zero_of_equiv`. This is the one step that is not
  formal, because a tensor product over `R'` is not a tensor product over `R`: instead the
  vanishing of `∑ₖ pₖ ⊗ xₖ` in `I ⊗_R M` is replaced by the finitary certificate of
  `Ideal.exists_tmul_vanishing_certificate`, which is a finite family of elements and equations
  and so carries across the isomorphism elementwise, and the transported certificate gives the
  vanishing on the other side by `Ideal.sum_tmul_eq_zero_of_vanishing_certificate`.

## References

* [Stacks Project, Tag 0471](https://stacks.math.columbia.edu/tag/0471)
-/

@[expose] public section

universe u v w x y

open CategoryTheory Limits
open scoped TensorProduct

namespace Stacks.Flatness.EssFPLocalCriterion

/-- The local criterion for flatness for a local map `R → S` essentially of finite presentation and
an `S`-module `M` of finite presentation, with `R`, `S` and `M` in a single universe and the
injectivity of `I ⊗_R M → M` stated elementwise. -/
@[sga "3 VIB 12.7" "Local, special case"]
private theorem solution_aux {R S M : Type u} [CommRing R] [CommRing S] [IsLocalRing R]
    [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)] [AddCommGroup M] [Module R M]
    [Module S M] [IsScalarTower R S M] [Module.FinitePresentation S M]
    (hS : (algebraMap R S).EssentiallyOfFinitePresentation) (I : Ideal R) (hI : I ≠ ⊤)
    (hTor : ∀ {n : ℕ} (p : Fin n → ↥I) (u : Fin n → M),
      (∑ k, HSMul.hSMul (α := R) (β := M) (p k : R) (u k) = 0) →
      ∑ k, (p k) ⊗ₜ[R] (u k) = (0 : ↥I ⊗[R] M))
    (hflat : Module.Flat (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M)))) :
    Module.Flat R M := by
  obtain ⟨Λ, instPre, instNe, instDir, A, B, φ, N, mod, hsmul, ρ, σ, ν, hRc, hSc, hMc,
      hφ, hν, hAlocal, hBlocal, hφlocal, hρlocal, hAft, hφft, hNfin, hBloc, hNbc⟩ :=
    RingHom.EssentiallyOfFinitePresentation.exists_isColimit_essFiniteType_module (M := M) hS
  have hAmaplocal : ∀ ⦃k l : Λ⦄ (h : k ⟶ l), IsLocalHom (A.map h).hom := by
    intro k l h
    have hc : (ρ.app l).hom.comp (A.map h).hom = (ρ.app k).hom := by ext a; simp
    have : IsLocalHom ((ρ.app l).hom.comp (A.map h).hom) := by rw [hc]; exact hρlocal k
    exact isLocalHom_of_comp (A.map h).hom (ρ.app l).hom
  have hQflat := Module.Flat.exists_ge_flat_quotient_of_isColimit mod hsmul hRc hSc hMc hφ hν
    hAlocal hBlocal hφlocal hAmaplocal hAft hφft hNfin hBloc hNbc I hI hflat
  have hflat' := Module.Flat.exists_ge_flat_of_isColimit_of_rTensor_subtype_injective mod hsmul
    hRc hMc hφ hν hAlocal hBlocal hφlocal hAft hφft hNfin hBloc hNbc I hI hTor hQflat
  have hnat : ∀ ⦃k l : Λ⦄ (h : k ⟶ l) (x : ↑(A.obj k)),
      (φ.app l ((A.map h) x) : ↑(B.obj l)) = B.map h ((φ.app k) x) := by
    intro k l h x
    simp
  let modA : ∀ k : Λ, Module ↑(A.obj k) ↑(N.obj k) :=
    fun k => Module.compHom _ (φ.app k).hom
  have hsmulA : ∀ ⦃k l : Λ⦄ (h : k ⟶ l) (x : ↑(A.obj k)) (m : ↑(N.obj k)),
      N.map h (x • m) = A.map h x • N.map h m := by
    intro k l h x m
    change N.map h ((φ.app k x) • m) = (φ.app l (A.map h x)) • N.map h m
    rw [hsmul h ((φ.app k) x) m, hnat h x]
  have hνA : ∀ (k : Λ) (x : ↑(A.obj k)) (m : ↑(N.obj k)),
      (ν.app k (x • m) : M) = HSMul.hSMul (α := R) (β := M) (ρ.app k x) (ν.app k m) := by
    intro k x m
    change (ν.app k ((φ.app k x) • m) : M) = _
    rw [hν k ((φ.app k) x) m]
    have h2 : (σ.app k (φ.app k x) : S) = algebraMap R S (ρ.app k x) := by
      simpa using ConcreteCategory.congr_hom (hφ k) x
    rw [h2, algebraMap_smul]
  exact Module.Flat.of_isColimit_of_forall_exists_ge_flat modA hsmulA hRc hMc hνA hflat'

/-! ### Universe reduction -/

/-- Let `e : R₁ ≃+* R₂` be a ring isomorphism and let `φ : X ≃+ Y` be an additive isomorphism which
is semilinear over `e`, that is `φ (r • x) = e r • φ x`. If `Y` is flat over `R₂` then `X` is flat
over `R₁`. -/
theorem flat_of_ringEquiv_of_addEquiv {R₁ R₂ X Y : Type*} [CommRing R₁] [CommRing R₂]
    [AddCommGroup X] [AddCommGroup Y] [Module R₁ X] [Module R₂ Y] [Module.Flat R₂ Y]
    (e : R₁ ≃+* R₂) (φ : X ≃+ Y) (hφ : ∀ (r : R₁) (x : X), φ (r • x) = e r • φ x) :
    Module.Flat R₁ X := by
  let algR₁R₂ : Algebra R₁ R₂ := e.toRingHom.toAlgebra
  let modR₁Y : Module R₁ Y := Module.compHom Y (e : R₁ →+* R₂)
  have hsmul : ∀ (r : R₁) (y : Y), r • y = e r • y := fun _ _ => rfl
  have : IsScalarTower R₁ R₂ Y := IsScalarTower.of_algebraMap_smul hsmul
  have : Module.Flat R₁ R₂ :=
    Module.Flat.of_linearEquiv
      ({ toFun := e.symm
         map_add' := fun x y => map_add _ _ _
         map_smul' := fun a y => by
           change e.symm ((e a * y : R₂)) = a * e.symm y
           rw [map_mul, e.symm_apply_apply]
         invFun := e
         left_inv := fun x => e.apply_symm_apply x
         right_inv := fun y => e.symm_apply_apply y } : R₂ ≃ₗ[R₁] R₁)
  have : Module.Flat R₁ Y := Module.Flat.trans R₁ R₂ Y
  exact Module.Flat.of_linearEquiv (φ.toLinearEquiv (R := R₁) fun r x => by rw [hφ, hsmul])

/-- Let `e : R₁ ≃+* R₂` be a ring isomorphism and let `X` be a module over both rings with
`r • x = e r • x`. If `X` is flat over `R₂` then `X` is flat over `R₁`. -/
theorem flat_of_ringEquiv {R₁ R₂ : Type*} [CommRing R₁] [CommRing R₂] (e : R₁ ≃+* R₂)
    {X : Type*} [AddCommGroup X] [Module R₁ X] [Module R₂ X]
    (hcompat : ∀ (r : R₁) (x : X), r • x = e r • x) [Module.Flat R₂ X] : Module.Flat R₁ X :=
  flat_of_ringEquiv_of_addEquiv (X := X) (Y := X) e (AddEquiv.refl X) hcompat

/-- Let `eR : R' ≃+* R` be a ring isomorphism and `eM : M' ≃+ M` an additive isomorphism which is
semilinear over `eR`, and let `I` be an ideal of `R` with inverse image `I'` in `R'`. If `M/IM` is
flat over `R/I`, then `M'/I'M'` is flat over `R'/I'`. -/
private lemma flat_quotient_of_equiv {R : Type u} {M : Type w} {R' : Type x} {M' : Type y}
    [CommRing R] [AddCommGroup M] [Module R M] [CommRing R'] [AddCommGroup M'] [Module R' M']
    (eR : R' ≃+* R) (eM : M' ≃+ M)
    (hcompat : ∀ (a : R') (m : M'), eM (a • m) = eR a • eM m)
    (I : Ideal R) (hflat : Module.Flat (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M)))) :
    Module.Flat (R' ⧸ I.comap (eR : R' →+* R))
      (M' ⧸ ((I.comap (eR : R' →+* R)) • (⊤ : Submodule R' M'))) := by
  set I' : Ideal R' := I.comap (eR : R' →+* R) with hI'def
  have hmapI : I = I'.map (eR : R' →+* R) := (Ideal.map_comap_of_surjective _ eR.surjective I).symm
  let ebar : (R' ⧸ I') ≃+* (R ⧸ I) := Ideal.quotientEquiv I' I eR hmapI
  have ip1 : RingHomInvPair (eR : R' →+* R) (eR.symm : R →+* R') := RingHomInvPair.of_ringEquiv eR
  have ip2 : RingHomInvPair (eR.symm : R →+* R') (eR : R' →+* R) := RingHomInvPair.symm _ _
  have hsurj : RingHomSurjective (eR : R' →+* R) := ⟨eR.surjective⟩
  let eMs : M' ≃ₛₗ[(eR : R' →+* R)] M :=
    { toFun := eM
      map_add' := fun x y => map_add eM x y
      map_smul' := hcompat
      invFun := eM.symm
      left_inv := fun x => eM.symm_apply_apply x
      right_inv := fun y => eM.apply_symm_apply y }
  have hsub : Submodule.map (eMs : M' →ₛₗ[(eR : R' →+* R)] M) (I' • (⊤ : Submodule R' M'))
      = I • (⊤ : Submodule R M) := by
    refine le_antisymm ?_ ?_
    · rw [Submodule.map_le_iff_le_comap]
      refine Submodule.smul_le.2 fun a ha m _ => ?_
      rw [Submodule.mem_comap]
      change eM (a • m) ∈ I • (⊤ : Submodule R M)
      rw [hcompat]
      exact Submodule.smul_mem_smul (Ideal.mem_comap.mp ha) Submodule.mem_top
    · refine Submodule.smul_le.2 fun a ha m _ => ?_
      refine Submodule.mem_map.2 ⟨(eR.symm a) • (eM.symm m), ?_, ?_⟩
      · refine Submodule.smul_mem_smul (Ideal.mem_comap.mpr ?_) Submodule.mem_top
        simpa using ha
      · change eM ((eR.symm a) • (eM.symm m)) = a • m
        rw [hcompat, eR.apply_symm_apply, eM.apply_symm_apply]
  let e1 := Submodule.Quotient.equiv (I' • (⊤ : Submodule R' M')) (I • (⊤ : Submodule R M)) eMs hsub
  refine flat_of_ringEquiv_of_addEquiv ebar e1.toAddEquiv fun r z => ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective (I' • (⊤ : Submodule R' M')) z
  exact congrArg Submodule.Quotient.mk (hcompat a m)

/-- Let `eR : R' ≃+* R` be a ring isomorphism and `eM : M' ≃+ M` an additive isomorphism which is
semilinear over `eR`, and let `I` be an ideal of `R` with inverse image `I'` in `R'`. If
`I ⊗_R M → M` is injective, then for `pₖ ∈ I'` and `uₖ ∈ M'` with `∑ₖ pₖ uₖ = 0`, the element
`∑ₖ pₖ ⊗ uₖ` of `I' ⊗_{R'} M'` vanishes. -/
private lemma sum_tmul_eq_zero_of_equiv {R : Type u} {M : Type w} {R' : Type x} {M' : Type y}
    [CommRing R] [AddCommGroup M] [Module R M] [CommRing R'] [AddCommGroup M'] [Module R' M']
    (eR : R' ≃+* R) (eM : M' ≃+ M)
    (hcompat : ∀ (a : R') (m : M'), eM (a • m) = eR a • eM m)
    (I : Ideal R) (hTor : Function.Injective (I.subtype.rTensor M))
    {n : ℕ} (p : Fin n → ↥(I.comap (eR : R' →+* R))) (u : Fin n → M')
    (hrel : ∑ k, HSMul.hSMul (α := R') (β := M') (p k : R') (u k) = 0) :
    ∑ k, (p k) ⊗ₜ[R'] (u k) = (0 : ↥(I.comap (eR : R' →+* R)) ⊗[R'] M') := by
  have hmem : ∀ k, eR (p k : R') ∈ I := fun k => Ideal.mem_comap.mp (p k).2
  have hrelR : ∑ k, HSMul.hSMul (α := R) (β := M) (eR (p k : R')) (eM (u k)) = 0 := by
    have hsum : eM (∑ k, HSMul.hSMul (α := R') (β := M') (p k : R') (u k))
        = ∑ k, HSMul.hSMul (α := R) (β := M) (eR (p k : R')) (eM (u k)) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun k _ => hcompat _ _
    rw [← hsum, hrel, map_zero]
  have hz : ∑ k, (⟨eR (p k : R'), hmem k⟩ : ↥I) ⊗ₜ[R] (eM (u k)) = (0 : ↥I ⊗[R] M) := by
    refine hTor ?_
    rw [map_zero, map_sum]
    refine (TensorProduct.lid R M).injective ?_
    rw [map_zero, map_sum]
    simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, Submodule.coe_subtype]
    exact hrelR
  obtain ⟨n', m, g, hg, Y, c, d, h1, h2, h3⟩ :=
    Ideal.exists_tmul_vanishing_certificate I (fun k => eR (p k : R')) hmem
      (fun k => eM (u k)) hz
  have hgmem : ∀ b, eR.symm (g b) ∈ I.comap (eR : R' →+* R) := fun b =>
    Ideal.mem_comap.mpr (by simpa using hg b)
  refine Ideal.sum_tmul_eq_zero_of_vanishing_certificate (I.comap (eR : R' →+* R)) p u
    (fun b => ⟨eR.symm (g b), hgmem b⟩) (fun l => eM.symm (Y l))
    (fun k l => eR.symm (c k l)) (fun b l => eR.symm (d b l)) ?_ ?_ ?_
  · intro k
    refine eM.injective ?_
    rw [map_sum, h1 k]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hcompat, eR.apply_symm_apply, eM.apply_symm_apply]
  · intro b
    refine eM.injective ?_
    rw [map_sum, map_zero, ← h2 b]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hcompat, eR.apply_symm_apply, eM.apply_symm_apply]
  · intro l
    refine eR.injective ?_
    rw [map_zero, map_add, map_sum, map_sum, ← h3 l]
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun k _ => ?_)
      (Finset.sum_congr rfl fun b _ => ?_) <;> simp only [smul_eq_mul, map_mul, eR.apply_symm_apply]

/-- The local criterion for flatness for a local map `R → S` essentially of finite presentation and
an `S`-module `M` of finite presentation, with `R`, `S` and `M` in independent universes. -/
private theorem solution {R : Type u} (S : Type v) (M : Type w) [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)] [AddCommGroup M]
    [Module R M] [Module S M] [IsScalarTower R S M] [Module.FinitePresentation S M]
    (hS : (algebraMap R S).EssentiallyOfFinitePresentation) (I : Ideal R) (hI : I ≠ ⊤)
    (hTor : Function.Injective (I.subtype.rTensor M))
    (hflat : Module.Flat (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M)))) :
    Module.Flat R M := by
  let eR : ULift.{max v w} R ≃+* R := ULift.ringEquiv
  let eS : ULift.{max u w} S ≃+* S := ULift.ringEquiv
  let eM : ULift.{max u v} M ≃ₗ[R] M := ULift.moduleEquiv
  let algR'S' : Algebra (ULift.{max v w} R) (ULift.{max u w} S) :=
    ULift.algebra' R (ULift.{max u w} S)
  let algS'S : Algebra (ULift.{max u w} S) S := ULift.algebra' S S
  let algR'R : Algebra (ULift.{max v w} R) R := ULift.algebra' R R
  have hlocR' : IsLocalRing (ULift.{max v w} R) := eR.symm.isLocalRing
  have hlocS' : IsLocalRing (ULift.{max u w} S) := eS.symm.isLocalRing
  have hlochom : IsLocalHom (algebraMap (ULift.{max v w} R) (ULift.{max u w} S)) := by
    have h0 : (eS : ULift.{max u w} S →+* S).comp
        (algebraMap (ULift.{max v w} R) (ULift.{max u w} S)) =
        (algebraMap R S).comp (eR : ULift.{max v w} R →+* R) := rfl
    have : IsLocalHom ((eS : ULift.{max u w} S →+* S).comp
        (algebraMap (ULift.{max v w} R) (ULift.{max u w} S))) := by
      rw [h0]; exact RingHom.isLocalHom_comp _ _
    exact isLocalHom_of_comp _ (eS : ULift.{max u w} S →+* S)
  have htowS'S : IsScalarTower (ULift.{max u w} S) S (ULift.{max u v} M) :=
    ⟨fun x y z => by ext; exact mul_smul x.down y z.down⟩
  have hfpS'S : Module.FinitePresentation (ULift.{max u w} S) S := by
    refine Module.FinitePresentation.of_equiv
      (M := ULift.{max u w} S) (N := S) (R := ULift.{max u w} S) ?_
    exact { eS with map_smul' := fun _ _ => rfl }
  have hfpSM' : Module.FinitePresentation S (ULift.{max u v} M) :=
    Module.FinitePresentation.of_equiv (ULift.moduleEquiv (R := S)).symm
  have hfp : Module.FinitePresentation (ULift.{max u w} S) (ULift.{max u v} M) :=
    Module.FinitePresentation.trans (ULift.{max u w} S) (ULift.{max u v} M) S
  have htow : IsScalarTower (ULift.{max v w} R) (ULift.{max u w} S) (ULift.{max u v} M) :=
    ⟨fun x y z => by ext; exact smul_assoc x.down y.down z.down⟩
  set I' : Ideal (ULift.{max v w} R) := I.comap (eR : ULift.{max v w} R →+* R) with hI'def
  have hI' : I' ≠ ⊤ := by
    intro htop
    refine hI (Ideal.eq_top_iff_one I |>.2 ?_)
    have h1 : (1 : ULift.{max v w} R) ∈ I' := by rw [htop]; exact Submodule.mem_top
    have := Ideal.mem_comap.mp h1
    rwa [map_one] at this
  have hTor' : ∀ {n : ℕ} (p : Fin n → ↥I') (u : Fin n → ULift.{max u v} M),
      (∑ k, HSMul.hSMul (α := ULift.{max v w} R) (β := ULift.{max u v} M) (p k : ULift.{max v w} R)
        (u k) = 0) →
      ∑ k, (p k) ⊗ₜ[ULift.{max v w} R] (u k)
        = (0 : ↥I' ⊗[ULift.{max v w} R] ULift.{max u v} M) :=
    fun p u hrel => sum_tmul_eq_zero_of_equiv eR eM.toAddEquiv (fun _ _ => rfl) I hTor p u hrel
  have hflat' : Module.Flat (ULift.{max v w} R ⧸ I')
      (ULift.{max u v} M ⧸ (I' • (⊤ : Submodule (ULift.{max v w} R) (ULift.{max u v} M)))) :=
    flat_quotient_of_equiv eR eM.toAddEquiv (fun _ _ => rfl) I hflat
  have hS' :
      (algebraMap (ULift.{max v w} R) (ULift.{max u w} S)).EssentiallyOfFinitePresentation := by
    let algRS : Algebra R S := (algebraMap R S).toAlgebra
    obtain ⟨A, instA, instRA, instAS, instTow, instFP, T, instLoc⟩ := hS
    let eA : ULift.{max u v w} A ≃+* A := ULift.ringEquiv
    let algR'A' : Algebra (ULift.{max v w} R) (ULift.{max u v w} A) :=
      ULift.algebra' R (ULift.{max u v w} A)
    let algA'S' : Algebra (ULift.{max u v w} A) (ULift.{max u w} S) :=
      ULift.algebra' A (ULift.{max u w} S)
    let algR'S'' : Algebra (ULift.{max v w} R) (ULift.{max u w} S) :=
      (algebraMap (ULift.{max v w} R) (ULift.{max u w} S)).toAlgebra
    have hftRR : Algebra.FiniteType R R := Module.Finite.finiteType R
    have hftRR' : Algebra.FiniteType R (ULift.{max v w} R) :=
      Algebra.FiniteType.of_surjective (Algebra.ofId R (ULift.{max v w} R))
        (fun x => ⟨x.down, rfl⟩)
    have hfpRA' : Algebra.FinitePresentation R (ULift.{max u v w} A) :=
      Algebra.FinitePresentation.equiv (ULift.algEquiv (R := R) (A := A)).symm
    have htowRR'A' : IsScalarTower R (ULift.{max v w} R) (ULift.{max u v w} A) :=
      ⟨fun x y z => by ext; exact mul_smul x y.down z.down⟩
    have hfpR'A' : Algebra.FinitePresentation (ULift.{max v w} R) (ULift.{max u v w} A) :=
      Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R
        (ULift.{max v w} R) (ULift.{max u v w} A)
    have hker : RingHom.ker (eS.symm : S →+* ULift.{max u w} S) = ⊥ :=
      (RingHom.injective_iff_ker_eq_bot _).mp eS.symm.injective
    have hlocA' : IsLocalization
        (Submonoid.map (eA.symm : A →+* ULift.{max u v w} A) T) (ULift.{max u w} S) :=
      IsLocalization.of_surjective T S (eA.symm : A →+* ULift.{max u v w} A) eA.symm.surjective
        (eS.symm : S →+* ULift.{max u w} S) eS.symm.surjective rfl (by rw [hker]; exact bot_le)
    refine ⟨ULift.{max u v w} A, inferInstance, algR'A', algA'S', ?_, hfpR'A',
      Submonoid.map (eA.symm : A →+* ULift.{max u v w} A) T, hlocA'⟩
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    ext
    exact IsScalarTower.algebraMap_apply R A S x.down
  have hgoal : Module.Flat (ULift.{max v w} R) (ULift.{max u v} M) :=
    solution_aux (S := ULift.{max u w} S) (M := ULift.{max u v} M) hS' I' hI' hTor' hflat'
  have hRR' : Module.Flat R (ULift.{max v w} R) := Module.Flat.of_linearEquiv ULift.moduleEquiv
  have htowRR' : IsScalarTower R (ULift.{max v w} R) (ULift.{max u v} M) :=
    ⟨fun x y z => by ext; exact mul_smul x y.down z.down⟩
  have : Module.Flat R (ULift.{max u v} M) :=
    Module.Flat.trans R (ULift.{max v w} R) (ULift.{max u v} M)
  exact Module.Flat.of_linearEquiv eM.symm

end Stacks.Flatness.EssFPLocalCriterion

/-! ### The local criterion -/

namespace Module.Flat

/-- The local criterion for flatness for local maps essentially of finite presentation.
Let `R → S` be a local homomorphism of local rings with `S` essentially of finite presentation over
`R`, let `I ≠ R` be an ideal of `R` and let `M` be an `S`-module of finite presentation. If
`Tor₁^R(R/I, M) = 0` and `M/IM` is flat over `R/I`, then `M` is flat over `R`.

Here the Tor hypothesis appears in the form of Remark 00M6, as the injectivity of
`I ⊗_R M → R ⊗_R M`, and `M/IM` is `M ⧸ I • ⊤` with its canonical `R ⧸ I`-module structure. No ring
is assumed Noetherian; the Noetherian variant is 00ML. -/
@[stacks 0471 "The hypothesis `Tor_1^R(M, R/I) = 0` is stated in the form Remark 00M6 identifies it
with, the injectivity of `I ⊗_R M → R ⊗_R M`, as in the Noetherian sibling 00ML; this is the form
the source's proof produces and the form 00ML consumes, and unlike `Tor_1` it puts `R` and `M` in
no common universe. Hypothesis (1) is `RingHom.EssentiallyOfFinitePresentation` (Definition
00QM (2)), Mathlib having no such predicate. See the module docstring.",
  ega "IV 11.3.12" "b⇒a, b⇒a for arbitrary A", sga "1 IV 5.6" "(ii)⇒(i), special case"]
public theorem of_rTensor_subtype_injective_of_flat_quotient_of_essentiallyOfFinitePresentation
    {R : Type u} (S : Type v) (M : Type w) [CommRing R] [CommRing S] [IsLocalRing R]
    [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)] [AddCommGroup M] [Module R M]
    [Module S M] [IsScalarTower R S M] [Module.FinitePresentation S M]
    (hS : (algebraMap R S).EssentiallyOfFinitePresentation) (I : Ideal R) (hI : I ≠ ⊤)
    (hTor : Function.Injective (I.subtype.rTensor M))
    (hflat : Module.Flat (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M)))) :
    Module.Flat R M :=
  Stacks.Flatness.EssFPLocalCriterion.solution S M hS I hI hTor hflat

end Module.Flat
