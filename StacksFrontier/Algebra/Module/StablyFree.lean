module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Quotient.Pi
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.RingTheory.Nakayama
public import StacksCore.RingTheory.Jacobson.Ideal

/-!
# Stably free modules

Two modules over a ring are *stably isomorphic* if they become isomorphic after adding a finite
free summand to each, and a module is *stably free* if it is stably isomorphic to a free module.
Stable freeness itself is Mathlib's `Module.IsStablyFree`, which is phrased as the existence of a
finite free module `N` with `M × N` free; the first result below identifies that with the source
definition.

This file collects the elementary theory of stable freeness: its behaviour on the terms of a
short exact sequence, and the fact that stably free modules lift along an ideal contained in the
Jacobson radical.

## Main definitions

* `Module.IsStablyIso`: two modules become isomorphic after adding finite free summands.

## Main results

* `Module.isStablyFree_iff_exists_isStablyIso`: `Module.IsStablyFree` agrees with the source
  definition, namely stable isomorphy to a free module.
* `Module.IsStablyFree.prod` and `Module.IsStablyFree.of_prod_left`: stable freeness is stable
  under products and is inherited by a complementary factor.
* `Module.isStablyFree_two_out_of_three`: in a short exact sequence of finite modules with
  projective quotient, stable freeness of two of the terms gives it for the third.
* `Module.exists_isStablyFree_lift`: over an ideal contained in the Jacobson radical, every
  finite stably free module on the quotient is the reduction of a finite stably free module.

## Implementation notes

A finite free summand is spelled `Fin n → R`, and an arbitrary free module — needed to state
stable isomorphy to a *free* module without fixing a universe — is packaged as an object of
`ModuleCat R`. A short exact sequence `0 → P' → P → P'' → 0` is given by two linear maps together
with injectivity of the first, exactness at the middle term, and surjectivity of the second. The
reduction of a module `M` along an ideal `I` is `M ⧸ I • ⊤` with its `R ⧸ I`-module structure.

Projectivity of the outer terms is not assumed in `Module.isStablyFree_two_out_of_three`: a
stably free module is projective, so only the quotient, whose projectivity splits the sequence,
needs the hypothesis.

## References

* [Stacks Project, Tag 0BC3](https://stacks.math.columbia.edu/tag/0BC3)
* [Stacks Project, Tag 0BC4](https://stacks.math.columbia.edu/tag/0BC4)
* [Stacks Project, Tag 0BC5](https://stacks.math.columbia.edu/tag/0BC5)
-/

universe u v w x

@[expose] public section

namespace Module

/-- Two modules are *stably isomorphic* if adding finite free summands to each gives isomorphic
modules. -/
@[stacks 0BC3 "(1)"]
def IsStablyIso (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type*) [AddCommGroup N] [Module R N] : Prop :=
  ∃ m n : ℕ, Nonempty ((M × (Fin m → R)) ≃ₗ[R] (N × (Fin n → R)))

/-- A module is stably free precisely when it is stably isomorphic to a free module. This
identifies Mathlib's `Module.IsStablyFree` with the source definition. -/
@[stacks 0BC3 "(2)"]
theorem isStablyFree_iff_exists_isStablyIso (R : Type u) [Ring R]
    (M : Type v) [AddCommGroup M] [Module R M] :
    IsStablyFree R M ↔ ∃ F : ModuleCat.{max u v} R, Module.Free R F ∧ IsStablyIso R M F := by
  constructor
  · intro hM
    let : IsStablyFree R M := hM
    obtain ⟨N, hNadd, hNmodule, hNfinite, hNfree, hprod⟩ := IsStablyFree.exist_free_prod R M
    let : AddCommGroup N := hNadd
    let : Module R N := hNmodule
    let : Module.Finite R N := hNfinite
    let : Module.Free R N := hNfree
    refine ⟨ModuleCat.of R (M × N), hprod, ?_⟩
    by_cases hR : Nontrivial R
    · let : Nontrivial R := hR
      let : _root_.Finite (Module.Free.ChooseBasisIndex R N) :=
        Module.Finite.finite_basis (Module.Free.chooseBasis R N)
      let : Fintype (Module.Free.ChooseBasisIndex R N) := Fintype.ofFinite _
      let b := (Module.Free.chooseBasis R N).reindex
        (Fintype.equivFin (Module.Free.ChooseBasisIndex R N))
      exact ⟨Fintype.card (Module.Free.ChooseBasisIndex R N), 0,
        ⟨((LinearEquiv.refl R M).prodCongr b.equivFun.symm).trans LinearEquiv.prodUnique.symm⟩⟩
    · let : Subsingleton R := not_nontrivial_iff_subsingleton.mp hR
      let : Subsingleton N := Module.subsingleton R N
      exact ⟨0, 0, ⟨((LinearEquiv.refl R M).prodCongr
        (LinearEquiv.ofSubsingleton (Fin 0 → R) N)).trans LinearEquiv.prodUnique.symm⟩⟩
  · rintro ⟨F, hF, m, n, ⟨e⟩⟩
    let : Module.Free R F := hF
    have : Module.Free R (F × (Fin n → R)) := inferInstance
    have : Module.Free R (M × (Fin m → R)) := Module.Free.of_equiv e.symm
    exact IsStablyFree.of_free_prod R M (Fin m → R)

/-- A module is stably free if its product with a finite free module is isomorphic to a free
module. -/
private theorem isStablyFree_of_prod_equiv {R : Type u} [Ring R] {M : Type v} [AddCommGroup M]
    [Module R M] {A : Type w} [AddCommGroup A] [Module R A] [Module.Finite R A] [Module.Free R A]
    {F : Type x} [AddCommGroup F] [Module R F] [Module.Free R F] (e : (M × A) ≃ₗ[R] F) :
    IsStablyFree R M :=
  have : Module.Free R (M × A) := Module.Free.of_equiv e.symm
  IsStablyFree.of_free_prod R M A

/-- A product of two stably free modules is stably free. -/
theorem IsStablyFree.prod {R : Type u} [Ring R]
    {M : Type v} [AddCommGroup M] [Module R M] {N : Type w} [AddCommGroup N] [Module R N]
    (hM : IsStablyFree R M) (hN : IsStablyFree R N) : IsStablyFree R (M × N) := by
  let := hM
  let := hN
  obtain ⟨A, _, _, _, _, _⟩ := IsStablyFree.exist_free_prod R M
  obtain ⟨B, _, _, _, _, _⟩ := IsStablyFree.exist_free_prod R N
  let e : ((M × N) × (A × B)) ≃ₗ[R] ((M × A) × (N × B)) :=
    (LinearEquiv.prodAssoc R (M × N) A B).symm.trans <|
      ((LinearEquiv.prodAssoc R M N A).prodCongr (LinearEquiv.refl R B)).trans <|
        ((LinearEquiv.prodCongr (LinearEquiv.refl R M)
          (LinearEquiv.prodComm R N A)).prodCongr (LinearEquiv.refl R B)).trans <|
          (LinearEquiv.prodAssoc R M A N).symm.prodCongr (LinearEquiv.refl R B) |>.trans <|
            LinearEquiv.prodAssoc R (M × A) N B
  exact isStablyFree_of_prod_equiv e

/-- If a product and its left factor are stably free, so is the right factor. -/
theorem IsStablyFree.of_prod_left {R : Type u} [Ring R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    {N : Type w} [AddCommGroup N] [Module R N]
    (hM : IsStablyFree R M) (hMN : IsStablyFree R (M × N)) : IsStablyFree R N := by
  let := hM
  let := hMN
  obtain ⟨A, _, _, _, _, _⟩ := IsStablyFree.exist_free_prod R M
  obtain ⟨B, _, _, _, _, _⟩ := IsStablyFree.exist_free_prod R (M × N)
  let e : (N × ((M × A) × B)) ≃ₗ[R] (((M × N) × B) × A) :=
    (LinearEquiv.prodAssoc R N (M × A) B).symm.trans <|
      ((LinearEquiv.prodComm R N (M × A)).prodCongr (LinearEquiv.refl R B)).trans <|
        ((LinearEquiv.prodAssoc R M A N).prodCongr (LinearEquiv.refl R B)).trans <|
          (LinearEquiv.prodCongr (LinearEquiv.refl R M)
            (LinearEquiv.prodComm R A N)).prodCongr (LinearEquiv.refl R B) |>.trans <|
            ((LinearEquiv.prodAssoc R M N A).symm.prodCongr (LinearEquiv.refl R B)).trans <|
              (LinearEquiv.prodAssoc R (M × N) A B).trans <|
                (LinearEquiv.prodCongr (LinearEquiv.refl R (M × N))
                  (LinearEquiv.prodComm R A B)).trans <|
                  (LinearEquiv.prodAssoc R (M × N) B A).symm
  exact isStablyFree_of_prod_equiv e

/-- In a short exact sequence of finite modules with projective quotient, if any two of the three
terms are stably free, then so is the third. -/
@[stacks 0BC4]
theorem isStablyFree_two_out_of_three {R : Type u} [Ring R]
    {P' : Type v} [AddCommGroup P'] [Module R P'] [Module.Finite R P']
    {P : Type w} [AddCommGroup P] [Module R P] [Module.Finite R P]
    {P'' : Type x} [AddCommGroup P''] [Module R P''] [Module.Finite R P''] [Module.Projective R P'']
    (f : P' →ₗ[R] P) (g : P →ₗ[R] P'')
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g) :
    ((IsStablyFree R P' ∧ IsStablyFree R P) → IsStablyFree R P'') ∧
      ((IsStablyFree R P' ∧ IsStablyFree R P'') → IsStablyFree R P) ∧
      ((IsStablyFree R P ∧ IsStablyFree R P'') → IsStablyFree R P') := by
  obtain ⟨l, hl⟩ := Module.projective_lifting_property g LinearMap.id hg
  obtain ⟨e, -, -⟩ := ((Function.Exact.split_tfae' hfg).out 1 3 rfl rfl).mp ⟨hf, l, hl⟩
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨hP', hP⟩
    exact hP'.of_prod_left (hP.equiv e)
  · rintro ⟨hP', hP''⟩
    exact (hP'.prod hP'').equiv e.symm
  · rintro ⟨hP, hP''⟩
    exact hP''.of_prod_left ((hP.equiv e).equiv (LinearEquiv.prodComm R P' P''))

section Lift

variable {R : Type u} [CommRing R]

/-- An endomorphism of a finite free module that reduces to the identity modulo an ideal all of
whose `1 + x` are units has unit determinant, hence is invertible. -/
private theorem isUnit_of_reduction_eq_id (I : Ideal R) (hI : ∀ x ∈ I, IsUnit (1 + x))
    {κ : Type v} [Fintype κ] [DecidableEq κ] (f : (κ → R) →ₗ[R] (κ → R))
    (hf : ∀ x i, Ideal.Quotient.mk I (f x i) = Ideal.Quotient.mk I (x i)) : IsUnit f := by
  classical
  let b := Pi.basisFun R κ
  have hm : (LinearMap.toMatrix b b f).map (Ideal.Quotient.mk I) = 1 := by
    ext i j
    simp only [Matrix.map_apply, LinearMap.toMatrix_apply, Matrix.one_apply]
    rw [Pi.basisFun_repr, hf, Pi.basisFun_apply]
    by_cases hij : i = j <;> simp [hij]
  have hd : Ideal.Quotient.mk I (LinearMap.det f) = 1 := by
    rw [← LinearMap.det_toMatrix b f, RingHom.map_det]
    show ((LinearMap.toMatrix b b f).map (Ideal.Quotient.mk I)).det = 1
    rw [hm, Matrix.det_one]
  have hx : LinearMap.det f - 1 ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simp [map_sub, hd]
  exact (LinearMap.isUnit_iff_isUnit_det f).2
    (by simpa [sub_add_cancel] using hI (LinearMap.det f - 1) hx)

/-- Coordinatewise reduction `Rᶥ → (R ⧸ I)ᶥ`, as a map of `R`-modules. -/
public def quotientPiMap (I : Ideal R) {ι : Type v} : (ι → R) →ₗ[R] (ι → R ⧸ I) where
  toFun x i := Ideal.Quotient.mk I (x i)
  map_add' x y := by ext i; simp
  map_smul' r x := by
    ext i
    change Ideal.Quotient.mk I (r * x i) =
      Ideal.Quotient.mk I r * Ideal.Quotient.mk I (x i)
    exact (Ideal.Quotient.mk I).map_mul r (x i)

/-- Coordinatewise reduction `Rᶥ → (R ⧸ I)ᶥ` is surjective. -/
public theorem quotientPiMap_surjective (I : Ideal R) {ι : Type v} :
    Function.Surjective (quotientPiMap I (ι := ι)) := by
  classical
  intro y
  choose x hx using fun i => Ideal.Quotient.mk_surjective (y i)
  exact ⟨x, funext hx⟩

/-- On a finite free module, `I • ⊤` is the submodule of tuples with all coordinates in `I`. -/
public theorem ideal_smul_top_pi (I : Ideal R) {ι : Type v} [Fintype ι] [DecidableEq ι] :
    I • (⊤ : Submodule R (ι → R)) =
      Submodule.pi Set.univ (fun _ : ι => (I : Submodule R R)) := by
  classical
  ext x
  constructor
  · intro hx i _
    have hproj : Function.Surjective (LinearMap.proj i : (ι → R) →ₗ[R] R) :=
      fun y => ⟨fun _ => y, rfl⟩
    have hmap : (I • (⊤ : Submodule R (ι → R))).map (LinearMap.proj i) = I := by
      rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hproj]
      simp
    have hm : (LinearMap.proj i) x ∈ (I • (⊤ : Submodule R (ι → R))).map
        (LinearMap.proj i) := Submodule.mem_map_of_mem hx
    simpa [LinearMap.proj_apply] using hmap ▸ hm
  · intro hx
    have hx' : ∀ i, x i ∈ I := fun i => (Submodule.mem_pi.mp hx) i (Set.mem_univ i)
    have hsum : x = ∑ i, x i • (Pi.single i (1 : R)) := by
      calc
        x = ∑ i, Pi.single i (x i) := (LinearMap.sum_single_apply (fun _ : ι => R) x).symm
        _ = ∑ i, x i • (Pi.single i (1 : R)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          ext j
          by_cases hij : i = j <;> simp [hij]
    rw [hsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hx' i) (by simp)

/-- Let `I` be an ideal of `R` such that every element of `1 + I` is a unit, in other words `I` is
contained in the Jacobson radical. Then every finite stably free `R ⧸ I`-module `E` is the
reduction modulo `I` of a finite stably free `R`-module. -/
@[stacks 0BC5]
theorem exists_isStablyFree_lift (I : Ideal R) (hI : ∀ x ∈ I, IsUnit (1 + x))
    {E : Type v} [AddCommGroup E] [Module (R ⧸ I) E] [Module.Finite (R ⧸ I) E]
    [IsStablyFree (R ⧸ I) E] :
    ∃ M : ModuleCat.{max u v} R, Module.Finite R M ∧ IsStablyFree R M ∧
      Nonempty ((M ⧸ (I • (⊤ : Submodule R M))) ≃ₗ[R ⧸ I] E) := by
  classical
  let q := R ⧸ I
  obtain ⟨N, hNadd, hNmod, hNfin, hNfree, hFfree⟩ := IsStablyFree.exist_free_prod q E
  let : AddCommGroup N := hNadd
  let : Module q N := hNmod
  let : Module.Finite q N := hNfin
  let : Module.Free q N := hNfree
  let F := E × N
  let : Module.Free q F := hFfree
  let bF := Module.Free.chooseBasis q F
  let bN := Module.Free.chooseBasis q N
  let ι := Module.Free.ChooseBasisIndex q F
  let κ := Module.Free.ChooseBasisIndex q N
  let : Fintype ι := inferInstance
  let : Fintype κ := inferInstance
  let qMapF := quotientPiMap I (ι := ι)
  let qMapN := quotientPiMap I (ι := κ)
  let pQ : (ι → q) →ₗ[q] (κ → q) :=
    bN.equivFun.toLinearMap.comp <|
      (LinearMap.snd q E N).comp bF.equivFun.symm.toLinearMap
  let jQ : (κ → q) →ₗ[q] (ι → q) :=
    bF.equivFun.toLinearMap.comp <|
      (LinearMap.inr q E N).comp bN.equivFun.symm.toLinearMap
  let pR : (ι → q) →ₗ[R] (κ → q) := pQ.restrictScalars R
  let jR : (κ → q) →ₗ[R] (ι → q) := jQ.restrictScalars R
  have hpj : pQ.comp jQ = LinearMap.id := by
    refine LinearMap.ext fun x => ?_
    show bN.equivFun (LinearMap.snd q E N
      (bF.equivFun.symm (bF.equivFun (LinearMap.inr q E N (bN.equivFun.symm x))))) = x
    rw [bF.equivFun.symm_apply_apply]
    simp only [LinearMap.snd_apply, LinearMap.inr_apply]
    exact bN.equivFun.apply_symm_apply x
  have hpjR : pR.comp jR = LinearMap.id :=
    LinearMap.ext fun x => LinearMap.congr_fun hpj x
  obtain ⟨φ, hφ⟩ := Module.projective_lifting_property qMapN (pR.comp qMapF)
    (quotientPiMap_surjective I (ι := κ))
  obtain ⟨ψ, hψ⟩ := Module.projective_lifting_property qMapF (jR.comp qMapN)
    (quotientPiMap_surjective I (ι := ι))
  let h : (κ → R) →ₗ[R] (κ → R) := φ.comp ψ
  have hcomp : qMapN.comp h = qMapN := by
    refine LinearMap.ext fun x => ?_
    show qMapN (φ (ψ x)) = qMapN x
    calc
      qMapN (φ (ψ x)) = pR (qMapF (ψ x)) := LinearMap.congr_fun hφ (ψ x)
      _ = pR (jR (qMapN x)) := congrArg pR (LinearMap.congr_fun hψ x)
      _ = qMapN x := LinearMap.congr_fun hpjR (qMapN x)
  obtain ⟨u, hu⟩ := isUnit_of_reduction_eq_id I hI h (fun x i => by
    simpa [h, qMapN, quotientPiMap] using
      congrArg (fun y => y i) (LinearMap.congr_fun hcomp x))
  let hInv : (κ → R) →ₗ[R] (κ → R) := ↑u⁻¹
  have hhInv : h.comp hInv = LinearMap.id :=
    calc
      h.comp hInv = (↑u : Module.End R (κ → R)) * ↑u⁻¹ := by rw [← hu]; rfl
      _ = 1 := by simp
      _ = LinearMap.id := rfl
  let ψ' : (κ → R) →ₗ[R] (ι → R) := ψ.comp hInv
  have hsection : ∀ y, φ (ψ' y) = y := by
    have hsplit : φ.comp ψ' = LinearMap.id := by
      calc
        φ.comp ψ' = (φ.comp ψ).comp hInv := (LinearMap.comp_assoc _ _ _).symm
        _ = LinearMap.id := by simpa [h] using hhInv
    intro y
    simpa using LinearMap.congr_fun hsplit y
  let P := LinearMap.ker φ
  let liftKer : (ι → R) →ₗ[R] P :=
    { toFun := fun x => ⟨x - ψ' (φ x), by
        show φ (x - ψ' (φ x)) = 0
        rw [map_sub, hsection]
        simp⟩
      map_add' := fun x y => Subtype.ext <| by
        show x + y - ψ' (φ (x + y)) = (x - ψ' (φ x)) + (y - ψ' (φ y))
        rw [map_add, map_add]
        abel
      map_smul' := fun r x => Subtype.ext <| by
        show r • x - ψ' (φ (r • x)) = r • (x - ψ' (φ x))
        rw [map_smul, map_smul, smul_sub] }
  have hidLiftKer : ∀ p : P, liftKer p.val = p := fun p => Subtype.ext <| by
    show p.val - ψ' (φ p.val) = p.val
    rw [p.property]
    simp
  have hsurjLiftKer : Function.Surjective liftKer := fun p => ⟨p.val, hidLiftKer p⟩
  let g : (ι → R) →ₗ[R] P × (κ → R) := LinearMap.prod liftKer φ
  let f : (P × (κ → R)) →ₗ[R] (ι → R) :=
    (Submodule.subtype P).comp (LinearMap.fst R P (κ → R)) +
      ψ'.comp (LinearMap.snd R P (κ → R))
  have hfg : ∀ z, g (f z) = z := fun z => Prod.ext
    (Subtype.ext <| by
      show z.1.val + ψ' z.2 - ψ' (φ (z.1.val + ψ' z.2)) = z.1.val
      rw [map_add, z.1.property, zero_add, hsection]
      simp)
    (by
      show φ (z.1.val + ψ' z.2) = z.2
      rw [map_add, z.1.property, zero_add, hsection])
  have hgf : ∀ x, f (g x) = x := fun x => by
    show (liftKer x).val + ψ' (φ x) = x
    simp [liftKer, sub_add_cancel]
  let eSplit : (P × (κ → R)) ≃ₗ[R] (ι → R) :=
    LinearEquiv.ofBijective f
      ⟨fun x y hxy => by simpa only [hfg] using congrArg g hxy, fun x => ⟨g x, hgf x⟩⟩
  have hfinP : Module.Finite R P :=
    Module.Finite.of_surjective ((LinearMap.fst R P (κ → R)).comp g) fun p => ⟨p.val, hidLiftKer p⟩
  let : Module.Free R (P × (κ → R)) := Module.Free.of_equiv eSplit.symm
  have hstableP : IsStablyFree R P := IsStablyFree.of_free_prod R P (κ → R)
  let fP : P →ₛₗ[Ideal.Quotient.mk I] E :=
    { toFun := fun x => (bF.equivFun.symm (qMapF x.val)).1
      map_add' := fun x y => by
        show (bF.equivFun.symm (qMapF (x.val + y.val))).1 =
          (bF.equivFun.symm (qMapF x.val)).1 + (bF.equivFun.symm (qMapF y.val)).1
        rw [map_add, map_add]
        rfl
      map_smul' := fun r x => by
        show (bF.equivFun.symm (qMapF (r • x.val))).1 =
          Ideal.Quotient.mk I r • (bF.equivFun.symm (qMapF x.val)).1
        rw [qMapF.map_smul]
        show (bF.equivFun.symm ((Ideal.Quotient.mk I r) • qMapF x.val)).1 = _
        rw [bF.equivFun.symm.map_smulₛₗ]
        rfl }
  let J : Submodule R P := I • (⊤ : Submodule R P)
  have hJle : J ≤ fP.ker := by
    rw [Submodule.smul_le]
    intro r hr x _
    show fP (r • x) = 0
    rw [fP.map_smulₛₗ]
    simp [Ideal.Quotient.eq_zero_iff_mem.mpr hr]
  have hmapLiftKer : (I • (⊤ : Submodule R (ι → R))).map liftKer = J := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hsurjLiftKer]
  have hker : fP.ker = J := by
    refine le_antisymm (fun x hx => ?_) hJle
    have hvp : pR (qMapF x.val) = 0 :=
      calc
        pR (qMapF x.val) = qMapN (φ x.val) := (LinearMap.congr_fun hφ x.val).symm
        _ = 0 := by rw [show φ x.val = 0 from x.property]; simp
    let w : E × N := bF.equivFun.symm (qMapF x.val)
    have hwE : w.1 = 0 := hx
    have hwN : w.2 = 0 := by
      have hn : bN.equivFun w.2 = 0 := hvp
      exact bN.equivFun.injective (by simpa using hn)
    have hqzero : qMapF x.val = 0 := by
      refine bF.equivFun.symm.injective ?_
      have hw : w = 0 := by ext <;> assumption
      show w = bF.equivFun.symm 0
      simpa using hw
    have hxAmbient : x.val ∈ I • (⊤ : Submodule R (ι → R)) := by
      rw [ideal_smul_top_pi]
      intro i _
      exact Ideal.Quotient.eq_zero_iff_mem.mp (congrArg (fun y : ι → q => y i) hqzero)
    rw [← hmapLiftKer, ← hidLiftKer x]
    exact Submodule.mem_map_of_mem hxAmbient
  have hqψ' : ∀ z, qMapF (ψ' z) = jR (qMapN z) := by
    have hqInv : ∀ z, qMapN (hInv z) = qMapN z := fun z => by
      calc
        qMapN (hInv z) = qMapN (h (hInv z)) :=
          (LinearMap.congr_fun hcomp (hInv z)).symm
        _ = qMapN z := by
          simpa using congrArg qMapN (LinearMap.congr_fun hhInv z)
    intro z
    calc
      qMapF (ψ' z) = jR (qMapN (hInv z)) := LinearMap.congr_fun hψ (hInv z)
      _ = jR (qMapN z) := by rw [hqInv z]
  have hsurj : Function.Surjective fP := by
    intro e
    let v : ι → q := bF.equivFun (e, 0)
    obtain ⟨x, hx⟩ := quotientPiMap_surjective I v
    have hqφ : qMapN (φ x) = 0 :=
      calc
        qMapN (φ x) = pR (qMapF x) := LinearMap.congr_fun hφ x
        _ = pQ v := by rw [hx]; rfl
        _ = 0 := by simp [pQ, v]
    refine ⟨liftKer x, ?_⟩
    show (bF.equivFun.symm (qMapF (liftKer x).val)).1 = e
    have hqLift : qMapF (liftKer x).val = v := by
      show qMapF (x - ψ' (φ x)) = v
      rw [map_sub, hqψ' (φ x), hqφ, map_zero, sub_zero, hx]
    rw [hqLift]
    simp [v]
  have hquotP : Nonempty ((P ⧸ J) ≃ₗ[R ⧸ I] E) := by
    let fbarSem := J.liftQ fP hJle
    let fbar : (P ⧸ J) →ₗ[R ⧸ I] E :=
      { toFun := fbarSem
        map_add' := fbarSem.map_add
        map_smul' := fun a x => by
          obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
          exact fbarSem.map_smulₛₗ r x }
    have hkerBar : fbarSem.ker = ⊥ :=
      Submodule.ker_liftQ_eq_bot J fP hJle (le_of_eq hker)
    refine ⟨LinearEquiv.ofBijective fbar ⟨fun x y hxy => ?_, fun e => ?_⟩⟩
    · have hx : x - y ∈ fbarSem.ker := by
        change fbarSem x = fbarSem y at hxy
        show fbarSem (x - y) = 0
        rw [map_sub, hxy, sub_self]
      exact sub_eq_zero.mp (by simpa using (hkerBar ▸ hx : x - y ∈ (⊥ : Submodule R (P ⧸ J))))
    · obtain ⟨x, hx⟩ := hsurj e
      exact ⟨J.mkQ x, hx⟩
  exact ⟨ModuleCat.of R P, hfinP, hstableP, by simpa [J] using hquotP⟩

end Lift

end Module
