module

public import StacksFrontier.Algebra.Module.StablyFree
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Quotient.Pi
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.RingTheory.Nakayama

/-!
# Lifting a finite stably free module through a quotient

Let `I` be an ideal of a commutative ring `R` every element of whose coset `1 + I` is a unit, so
that `I` lies in the Jacobson radical of `R`. Every finite stably free `R / I`-module is then the
reduction modulo `I` of a finite stably free `R`-module.

## Main results

* `exists_isStablyFree_lift`: a finite stably free `R / I`-module `E` admits a finite stably free
  `R`-module `M` together with an `R / I`-linear isomorphism `M / IM ≃ E`.

## Implementation notes

This is the conceptual form of the substrate of Stacks Project tag 0BC5. It carries
no `@[stacks]` attribute: tag 0BC5 is carried elsewhere in the library.

Stable freeness is Mathlib's `Module.IsStablyFree`, so a witness is a finite free complement
making a direct sum free. The lift is produced from such a complement: a presentation of `E` as a
direct summand of a finite free `R / I`-module is given by an idempotent matrix over `R / I`, which
is lifted to an idempotent matrix over `R` because `I` is contained in the Jacobson radical, and
the image of the lifted idempotent is the required module. The quotient `M / IM` is the submodule
`I • ⊤` quotient, and the asserted isomorphism is `R / I`-linear, not merely `R`-linear.

The module universes of `E` and of the lift are kept independent: `E : Type v` over `R : Type u`,
with the lift produced in `ModuleCat.{max u v} R`, since the construction passes through free
modules on a basis index of `E`.

## References

* [Stacks Project, Tag 0BC5](https://stacks.math.columbia.edu/tag/0BC5)
-/

@[expose] public section

universe u v

private theorem ideal_le_jacobson_bot {R : Type u} [CommRing R] (I : Ideal R)
    (hI : ∀ x : R, x ∈ I → IsUnit (1 + x)) : I ≤ Ideal.jacobson (⊥ : Ideal R) := by
  intro x hx
  rw [Ideal.mem_jacobson_bot]
  intro y
  have hxy : x * y ∈ I := I.mul_mem_right y hx
  simpa [mul_comm, add_comm] using hI (x * y) hxy

private theorem isUnit_of_mod_quotient_id {R : Type u} [CommRing R] (I : Ideal R)
    (hI : ∀ x : R, x ∈ I → IsUnit (1 + x)) {κ : Type v} [Finite κ]
    (f : (κ → R) →ₗ[R] (κ → R))
    (hf : ∀ x i, Ideal.Quotient.mk I (f x i) = Ideal.Quotient.mk I (x i)) :
    IsUnit f := by
  classical
  let := Fintype.ofFinite κ
  let b := Pi.basisFun R κ
  have hm : (LinearMap.toMatrix b b f).map (Ideal.Quotient.mk I) = 1 := by
    ext i j
    simp only [Matrix.map_apply, LinearMap.toMatrix_apply, Matrix.one_apply]
    rw [Pi.basisFun_repr, hf, Pi.basisFun_apply]
    by_cases hij : i = j <;> simp [hij]
  have hd : Ideal.Quotient.mk I (LinearMap.det f) = 1 := by
    calc
      Ideal.Quotient.mk I (LinearMap.det f) =
          Matrix.det ((Ideal.Quotient.mk I).mapMatrix (LinearMap.toMatrix b b f)) := by
        rw [← LinearMap.det_toMatrix b f, RingHom.map_det]
      _ = 1 := by
        show ((LinearMap.toMatrix b b f).map (Ideal.Quotient.mk I)).det = 1
        rw [hm, Matrix.det_one]
  have hx : LinearMap.det f - 1 ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simp [map_sub, hd]
  have hdet : IsUnit (LinearMap.det f) := by
    simpa [sub_add_cancel] using hI (LinearMap.det f - 1) hx
  exact (LinearMap.isUnit_iff_isUnit_det f).2 hdet

/-- A finite stably free module over `R ⧸ I` lifts to a finite stably free `R`-module when every
`1 + x` with `x ∈ I` is a unit: there is a finite stably free `M` with `M / IM ≅ E`. -/
theorem exists_isStablyFree_lift
    {R : Type u} [CommRing R] (I : Ideal R)
    (hI : ∀ x : R, x ∈ I → IsUnit (1 + x))
    {E : Type v} [AddCommGroup E] [Module (R ⧸ I) E]
    [Module.Finite (R ⧸ I) E] [Module.IsStablyFree (R ⧸ I) E] :
    ∃ M : ModuleCat.{max u v} R,
      Module.Finite R M ∧ Module.IsStablyFree R M ∧
        Nonempty ((M ⧸ (I • (⊤ : Submodule R M))) ≃ₗ[R ⧸ I] E) := by
  classical
  let q := R ⧸ I
  obtain ⟨N, hNadd, hNmod, hNfin, hNfree, hFfree⟩ :=
    Module.IsStablyFree.exist_free_prod q E
  let : AddCommGroup N := hNadd
  let : Module q N := hNmod
  have : Module.Finite q N := hNfin
  have : Module.Free q N := hNfree
  let F := E × N
  let : AddCommGroup F := inferInstance
  let : Module q F := inferInstance
  have : Module.Finite q F := inferInstance
  have : Module.Free q F := hFfree
  let bF := Module.Free.chooseBasis q F
  let bN := Module.Free.chooseBasis q N
  let ι := Module.Free.ChooseBasisIndex q F
  let κ := Module.Free.ChooseBasisIndex q N
  let : Fintype ι := inferInstance
  let : Fintype κ := inferInstance
  let qMapF := Module.quotientPiMap I (ι := ι)
  let qMapN := Module.quotientPiMap I (ι := κ)
  let pQ : (ι → q) →ₗ[q] (κ → q) :=
    bN.equivFun.toLinearMap.comp <|
      (LinearMap.snd q E N).comp bF.equivFun.symm.toLinearMap
  let jQ : (κ → q) →ₗ[q] (ι → q) :=
    bF.equivFun.toLinearMap.comp <|
      (LinearMap.inr q E N).comp bN.equivFun.symm.toLinearMap
  let pR : (ι → q) →ₗ[R] (κ → q) := pQ.restrictScalars R
  let jR : (κ → q) →ₗ[R] (ι → q) := jQ.restrictScalars R
  have hpj : pQ.comp jQ = LinearMap.id := by
    apply LinearMap.ext
    intro x
    show bN.equivFun (LinearMap.snd q E N
      (bF.equivFun.symm (bF.equivFun (LinearMap.inr q E N (bN.equivFun.symm x))))) = x
    rw [bF.equivFun.symm_apply_apply]
    simp only [LinearMap.snd_apply, LinearMap.inr_apply]
    exact bN.equivFun.apply_symm_apply x
  have hpjR : pR.comp jR = LinearMap.id := LinearMap.ext fun x => LinearMap.congr_fun hpj x
  have : Module.Projective R (ι → R) := inferInstance
  have : Module.Projective R (κ → R) := inferInstance
  obtain ⟨φ, hφ⟩ := Module.projective_lifting_property qMapN
    (pR.comp qMapF) (Module.quotientPiMap_surjective I (ι := κ))
  obtain ⟨ψ, hψ⟩ := Module.projective_lifting_property qMapF
    (jR.comp qMapN) (Module.quotientPiMap_surjective I (ι := ι))
  let h : (κ → R) →ₗ[R] (κ → R) := φ.comp ψ
  have hcomp : qMapN.comp h = qMapN := by
    apply LinearMap.ext
    intro x
    show qMapN (φ (ψ x)) = qMapN x
    calc
      qMapN (φ (ψ x)) = pR (qMapF (ψ x)) := congrArg (fun f => f (ψ x)) hφ
      _ = pR (jR (qMapN x)) := congrArg pR (congrArg (fun f => f x) hψ)
      _ = qMapN x := congrArg (fun f => f (qMapN x)) hpjR
  have hmod : ∀ x i, Ideal.Quotient.mk I (h x i) = Ideal.Quotient.mk I (x i) := by
    intro x i
    have hx := congrArg (fun f => f x) hcomp
    have hi := congrArg (fun y => y i) hx
    simpa [h, qMapN, Module.quotientPiMap] using hi
  obtain ⟨u, hu⟩ := isUnit_of_mod_quotient_id I hI h hmod
  let hInv : (κ → R) →ₗ[R] (κ → R) := ↑(u⁻¹)
  have hhInv : h.comp hInv = LinearMap.id := by
    calc
      h.comp hInv = (↑u : Module.End R (κ → R)) * ↑(u⁻¹) := by
        rw [← hu]
        rfl
      _ = 1 := by simp
      _ = LinearMap.id := rfl
  let ψ' : (κ → R) →ₗ[R] (ι → R) := ψ.comp hInv
  have hsplit : φ.comp ψ' = LinearMap.id := by
    calc
      φ.comp ψ' = φ.comp (ψ.comp hInv) := rfl
      _ = (φ.comp ψ).comp hInv := by rw [LinearMap.comp_assoc]
      _ = LinearMap.id := by simpa [h] using hhInv
  have hsection : ∀ y, φ (ψ' y) = y := fun y => by simpa using LinearMap.congr_fun hsplit y
  let P := LinearMap.ker φ
  let liftKer : (ι → R) →ₗ[R] P :=
    { toFun := fun x => ⟨x - ψ' (φ x), by
        show φ (x - ψ' (φ x)) = 0
        rw [map_sub, hsection]
        simp
      ⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        show x + y - ψ' (φ (x + y)) = (x - ψ' (φ x)) + (y - ψ' (φ y))
        rw [map_add, map_add]
        abel
      map_smul' := by
        intro r x
        apply Subtype.ext
        show r • x - ψ' (φ (r • x)) = r • (x - ψ' (φ x))
        rw [map_smul, map_smul]
        rw [smul_sub] }
  have hliftKer_val : ∀ p : P, liftKer p.val = p := fun p => by
    apply Subtype.ext
    show p.val - ψ' (φ p.val) = p.val
    rw [p.property]
    simp
  have hsurjLiftKer : Function.Surjective liftKer := fun p => ⟨p.val, hliftKer_val p⟩
  let g : (ι → R) →ₗ[R] P × (κ → R) := LinearMap.prod liftKer φ
  let f : (P × (κ → R)) →ₗ[R] (ι → R) :=
    (Submodule.subtype P).comp (LinearMap.fst R P (κ → R)) +
      ψ'.comp (LinearMap.snd R P (κ → R))
  have hfg : ∀ z, g (f z) = z := by
    intro z
    apply Prod.ext
    · apply Subtype.ext
      show z.1.val + ψ' z.2 - ψ' (φ (z.1.val + ψ' z.2)) = z.1.val
      rw [map_add, z.1.property, zero_add, hsection]
      simp
    · show φ (z.1.val + ψ' z.2) = z.2
      rw [map_add, z.1.property, zero_add, hsection]
  have hgf : ∀ x, f (g x) = x := by
    intro x
    show (liftKer x).val + ψ' (φ x) = x
    simp [liftKer, sub_add_cancel]
  let eSplit : (P × (κ → R)) ≃ₗ[R] (ι → R) :=
    LinearEquiv.ofBijective f
      ⟨fun x y hxy => by simpa only [hfg] using congrArg g hxy, fun x => ⟨g x, hgf x⟩⟩
  have hfinP : Module.Finite R P := Module.Finite.of_surjective liftKer hsurjLiftKer
  have : Module.Free R (P × (κ → R)) := Module.Free.of_equiv eSplit.symm
  have hstableP : Module.IsStablyFree R P :=
    Module.IsStablyFree.of_free_prod R P (κ → R)
  let fP : P →ₛₗ[Ideal.Quotient.mk I] E :=
    { toFun := fun x => (bF.equivFun.symm (qMapF x.val)).1
      map_add' := by
        intro x y
        show (bF.equivFun.symm (qMapF (x.val + y.val))).1 =
          (bF.equivFun.symm (qMapF x.val)).1 + (bF.equivFun.symm (qMapF y.val)).1
        rw [map_add, map_add]
        rfl
      map_smul' := by
        intro r x
        show (bF.equivFun.symm (qMapF (r • x.val))).1 =
          Ideal.Quotient.mk I r • (bF.equivFun.symm (qMapF x.val)).1
        rw [qMapF.map_smul]
        show (bF.equivFun.symm
          ((Ideal.Quotient.mk I r) • qMapF x.val)).1 = _
        rw [bF.equivFun.symm.map_smulₛₗ]
        rfl }
  let J : Submodule R P := I • (⊤ : Submodule R P)
  have hJle : J ≤ fP.ker := by
    rw [Submodule.smul_le]
    intro r hr x hx
    show fP (r • x) = 0
    rw [fP.map_smulₛₗ]
    have hrq : Ideal.Quotient.mk I r = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hr
    simp [hrq]
  have hmapLiftKer :
      (I • (⊤ : Submodule R (ι → R))).map liftKer = J := by
    rw [Submodule.map_smul'', Submodule.map_top,
      LinearMap.range_eq_top.mpr hsurjLiftKer]
  have hkerRev : fP.ker ≤ J := by
    intro x hx
    have hxphi : φ x.val = 0 := x.property
    have hvp : pQ (qMapF x.val) = 0 := by
      have hh := congrArg (fun L => L x.val) hφ
      have hz : qMapN (φ x.val) = 0 := by rw [hxphi]; simp
      exact hh.symm.trans hz
    let w : E × N := bF.equivFun.symm (qMapF x.val)
    have hwE : w.1 = 0 := hx
    have hwN : w.2 = 0 := by
      have hn : bN.equivFun w.2 = 0 := by
        show bN.equivFun ((LinearMap.snd q E N) (bF.equivFun.symm (qMapF x.val))) = 0
        exact hvp
      apply bN.equivFun.injective
      simpa using hn
    have hqzero : qMapF x.val = 0 := by
      apply bF.equivFun.symm.injective
      have hw : w = 0 := by
        ext <;> assumption
      show w = bF.equivFun.symm 0
      simpa using hw
    have hcoords : ∀ i, x.val i ∈ I := by
      intro i
      have hi := congrArg (fun y : ι → q => y i) hqzero
      change Ideal.Quotient.mk I (x.val i) = 0 at hi
      exact Ideal.Quotient.eq_zero_iff_mem.mp hi
    have hxAmbient : x.val ∈ I • (⊤ : Submodule R (ι → R)) := by
      rw [Module.ideal_smul_top_pi]
      exact fun i _ => hcoords i
    rw [← hmapLiftKer, ← hliftKer_val x]
    exact Submodule.mem_map_of_mem hxAmbient
  have hker : fP.ker = J := le_antisymm hkerRev hJle
  have hqInv : ∀ z, qMapN (hInv z) = qMapN z := by
    intro z
    calc
      qMapN (hInv z) = qMapN (h (hInv z)) := (congrArg (fun L => L (hInv z)) hcomp).symm
      _ = qMapN z := by
        have hh := congrArg (fun L => L z) hhInv
        simpa using congrArg qMapN hh
  have hqψ' : ∀ z, qMapF (ψ' z) = jR (qMapN z) := by
    intro z
    calc
      qMapF (ψ' z) = qMapF (ψ (hInv z)) := rfl
      _ = jR (qMapN (hInv z)) := congrArg (fun L => L (hInv z)) hψ
      _ = jR (qMapN z) := by rw [hqInv z]
  have hsurj : Function.Surjective fP := by
    intro e
    let v : ι → q := bF.equivFun (e, 0)
    obtain ⟨x, hx⟩ := Module.quotientPiMap_surjective I v
    have hpv : pQ v = 0 := by
      simp [pQ, v]
    have hqφ : qMapN (φ x) = 0 := by
      calc
        qMapN (φ x) = pR (qMapF x) := congrArg (fun L => L x) hφ
        _ = pQ v := by rw [hx]; rfl
        _ = 0 := hpv
    have hqcorr : qMapF (ψ' (φ x)) = 0 := by
      rw [hqψ' (φ x), hqφ]
      simp
    refine ⟨liftKer x, ?_⟩
    show (bF.equivFun.symm (qMapF (liftKer x).val)).1 = e
    have hqLift : qMapF (liftKer x).val = v := by
      show qMapF (x - ψ' (φ x)) = v
      rw [map_sub, hqcorr, sub_zero, hx]
    rw [hqLift]
    simp [v]
  have hquotP : Nonempty ((P ⧸ J) ≃ₗ[R ⧸ I] E) := by
    let fbarSem := J.liftQ fP hJle
    let fbar : (P ⧸ J) →ₗ[R ⧸ I] E :=
      { toFun := fbarSem
        map_add' := fbarSem.map_add
        map_smul' := by
          intro a x
          obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
          exact fbarSem.map_smulₛₗ r x }
    have hkerBar : fbarSem.ker = ⊥ :=
      Submodule.ker_liftQ_eq_bot J fP hJle (le_of_eq hker)
    have hinj : Function.Injective fbar := by
      intro x y hxy
      have hx : x - y ∈ fbarSem.ker := by
        show fbarSem (x - y) = 0
        change fbarSem x = fbarSem y at hxy
        rw [map_sub, hxy, sub_self]
      have hbot : x - y ∈ (⊥ : Submodule R (P ⧸ J)) := hkerBar ▸ hx
      exact sub_eq_zero.mp (by simpa using hbot)
    have hsurjbar : Function.Surjective fbar := by
      intro e
      obtain ⟨x, hx⟩ := hsurj e
      refine ⟨J.mkQ x, ?_⟩
      show J.liftQ fP hJle (Submodule.Quotient.mk x) = e
      rw [Submodule.liftQ_apply]
      exact hx
    exact ⟨LinearEquiv.ofBijective fbar ⟨hinj, hsurjbar⟩⟩
  have : Module.Finite R P := hfinP
  let M : ModuleCat.{max u v} R := ModuleCat.of R P
  have hquot : Nonempty ((M ⧸ (I • (⊤ : Submodule R M))) ≃ₗ[R ⧸ I] E) := by
    simpa [M, J] using hquotP
  exact ⟨M, hfinP, hstableP, hquot⟩

end
