module

public import Mathlib.Algebra.Colimit.Module
public import Mathlib.Algebra.Colimit.Ring
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.Kaehler.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Kähler differentials commute with directed colimits

Let `(I, ≤)` be a directed set and let `(R_i → S_i, φ_{ii'})` be a system of ring maps
over `I`. Put `R = colim_i R_i`, `S = colim_i S_i` and let `u : R → S` be the induced ring
map. Then the canonical comparison map

`Θ : colim_i Ω_{S_i / R_i} → Ω_{S / R}`,

induced by functoriality of `Ω`, is an isomorphism of abelian groups, equivalently of
`S`-modules; in short `Ω_{S / R} = colim_i Ω_{S_i / R_i}`. This is Stacks tag 031G
(Lemma 10.131.5). Directedness of `(I, ≤)` means nonempty and such that any two elements
admit a common upper bound (Stacks tag 00D3).

## Main definitions

* `Stacks.KaehlerDifferential.Colimit.sqMap`: the functoriality map of Kähler differentials
  attached to a
  commuting square of ring maps, with `sqMap (d a) = d (β a)`.
* `Stacks.KaehlerDifferential.Colimit.IsCompatible`: the commuting squares `u_{i'} ∘ φ^R_{ii'} =
  φ^S_{ii'} ∘ u_i`
  defining a system of ring maps over `I`.
* `Stacks.KaehlerDifferential.Colimit.Rinf`, `Stacks.KaehlerDifferential.Colimit.Sinf`,
  `Stacks.KaehlerDifferential.Colimit.uinf`: the colimit rings and
  the induced map `u : R → S`.
* `Stacks.KaehlerDifferential.Colimit.OmegaColim`, `Stacks.KaehlerDifferential.Colimit.omegaTrans`:
  the colimit of the differentials
  and its transition maps.
* `Stacks.KaehlerDifferential.Colimit.Theta`: the comparison map `Θ`.
* `Stacks.KaehlerDifferential.Colimit.omegaColimModule`: the `S`-module structure on `colim_i
  Ω_{S_i / R_i}`.
* `Stacks.KaehlerDifferential.Colimit.δFun`: the universal `R`-derivation `S → colim_i Ω_{S_i /
  R_i}`.

## Main results

* `Stacks.KaehlerDifferential.Colimit.Theta_surjective`,
  `Stacks.KaehlerDifferential.Colimit.Theta_injective` and
  `Stacks.KaehlerDifferential.Colimit.main_theorem_031g` (Stacks tag 031G): `Θ` is surjective,
    injective, and
  hence bijective.

## Implementation notes

A system of ring maps over `I` is encoded as families of commutative rings `R i`, `S i`,
algebra structures `Algebra (R i) (S i)` giving the ring maps `u_i : R_i → S_i`, and
transition ring maps `fR : R i →+* R j`, `fS : S i →+* S j` for `i ≤ j` satisfying the
identity and cocycle conditions and compatible with the `u_i`, the latter packaged as
`IsCompatible`. The identity and cocycle conditions are not needed to *state* the
comparison map, so they appear as hypotheses on the main theorems rather than as part of
the ambient data.

Colimits of rings are `Ring.DirectLimit`, the directed colimit in commutative rings
(Stacks tag 078J). Since each `Ω_{S_i/R_i}` is a module over a different ring `S_i`, the
colimit of differentials is taken in abelian groups, modelled as `Module.DirectLimit`
over `ℤ`; the `S`-module structure on it is then constructed by hand in the sections
below, since Mathlib has no API for a module over a colimit ring with varying base.
-/

@[expose] public section

-- needed file-wide: `actLevel_ofΩ`, `actLevel_raise`, `actLevel_add`, `actLevel_one`,
-- `actLevel_mul`, `act`, `act_apply_ofΩ`, `Theta_surjective` and `Theta_injective` all
-- rewrite through the level-indexed action definitions, which only match when defeq may
-- unfold them past the default transparency
set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct

namespace Stacks.KaehlerDifferential.Colimit

/-! ## Functoriality of `Ω` for a commuting square.

Given a commuting square of ring maps
```
R --algebraMap--> A
|                 |
ψ                 β
v                 v
T --algebraMap--> B
```
i.e. `algebraMap T B ∘ ψ = β ∘ algebraMap R A`, we produce the canonical
additive map `Ω[A⁄R] → Ω[B⁄T]` sending `d a ↦ d (β a)`.  We package it as a
`ℤ`-linear map (i.e. a morphism of abelian groups). -/

/-- The functoriality map of Kähler differentials attached to a commuting
square of ring maps, as a morphism of abelian groups. -/
noncomputable def sqMap (R A T B : Type*) [CommRing R] [CommRing A] [CommRing T]
    [CommRing B] [Algebra R A] [Algebra T B]
    (ψ : R →+* T) (β : A →+* B)
    (h : (algebraMap T B).comp ψ = β.comp (algebraMap R A)) :
    Ω[A⁄R] →ₗ[ℤ] Ω[B⁄T] := by
  letI : Algebra A B := β.toAlgebra
  letI : Algebra R B := ((algebraMap T B).comp ψ).toAlgebra
  letI : Algebra R T := ψ.toAlgebra
  haveI : IsScalarTower R A B := by
    apply IsScalarTower.of_algebraMap_eq; intro x
    change ((algebraMap T B).comp ψ) x = (β.comp (algebraMap R A)) x; rw [h]
  haveI : IsScalarTower R T B := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  haveI : SMulCommClass T A B := by
    constructor; intro t a b
    rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, Algebra.smul_def]; ring
  exact (KaehlerDifferential.map R T A B).toAddMonoidHom.toIntLinearMap

/-- `sqMap` sends `d a` to `d (β a)` and is `β`-semilinear. -/
private theorem sqMap_D_and_smul (R A T B : Type*) [CommRing R] [CommRing A] [CommRing T]
    [CommRing B] [Algebra R A] [Algebra T B]
    (ψ : R →+* T) (β : A →+* B)
    (h : (algebraMap T B).comp ψ = β.comp (algebraMap R A)) :
    (∀ a : A, sqMap R A T B ψ β h (KaehlerDifferential.D R A a)
      = KaehlerDifferential.D T B (β a)) ∧
    ∀ (c : A) (x : Ω[A⁄R]), sqMap R A T B ψ β h (c • x) = β c • sqMap R A T B ψ β h x := by
  let : Algebra A B := β.toAlgebra
  let : Algebra R B := ((algebraMap T B).comp ψ).toAlgebra
  let : Algebra R T := ψ.toAlgebra
  have : IsScalarTower R A B := by
    apply IsScalarTower.of_algebraMap_eq; intro x
    change ((algebraMap T B).comp ψ) x = (β.comp (algebraMap R A)) x; rw [h]
  have : IsScalarTower R T B := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  have : SMulCommClass T A B := by
    constructor; intro t a b
    rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, Algebra.smul_def]; ring
  refine ⟨fun a => ?_, fun c x => ?_⟩
  · change (KaehlerDifferential.map R T A B) (KaehlerDifferential.D R A a) = _
    rw [KaehlerDifferential.map_D]; rfl
  · change (KaehlerDifferential.map R T A B) (c • x) = β c • (KaehlerDifferential.map R T A B) x
    rw [map_smul]; congr 1

/-- Characterisation of `sqMap` on `d`-generators: `sqMap (d a) = d (β a)`. -/
theorem sqMap_D (R A T B : Type*) [CommRing R] [CommRing A] [CommRing T]
    [CommRing B] [Algebra R A] [Algebra T B]
    (ψ : R →+* T) (β : A →+* B)
    (h : (algebraMap T B).comp ψ = β.comp (algebraMap R A)) (a : A) :
    sqMap R A T B ψ β h (KaehlerDifferential.D R A a)
      = KaehlerDifferential.D T B (β a) :=
  (sqMap_D_and_smul R A T B ψ β h).1 a

/-- Semilinearity of `sqMap`: `sqMap (c • x) = β c • sqMap x`. -/
@[ega "0 20.5.2" "partial"]
theorem sqMap_smul (R A T B : Type*) [CommRing R] [CommRing A] [CommRing T]
    [CommRing B] [Algebra R A] [Algebra T B]
    (ψ : R →+* T) (β : A →+* B)
    (h : (algebraMap T B).comp ψ = β.comp (algebraMap R A)) (c : A) (x : Ω[A⁄R]) :
    sqMap R A T B ψ β h (c • x) = β c • sqMap R A T B ψ β h x :=
  (sqMap_D_and_smul R A T B ψ β h).2 c x

/-! ## Set-up: a system of ring maps over a directed set `I`. -/

variable {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I] [DecidableEq I]
variable {R S : I → Type*}
variable [∀ i, CommRing (R i)] [∀ i, CommRing (S i)]
variable [∀ i, Algebra (R i) (S i)]
variable (fR : ∀ ⦃i j⦄, i ≤ j → R i →+* R j) (fS : ∀ ⦃i j⦄, i ≤ j → S i →+* S j)

/-- The commuting squares defining a system of ring maps over `I`:
`u_{i'} ∘ φ^R_{ii'} = φ^S_{ii'} ∘ u_i`, written with `algebraMap` for `u`. -/
def IsCompatible : Prop :=
  ∀ ⦃i j⦄ (h : i ≤ j),
    (fS h).comp (algebraMap (R i) (S i)) = (algebraMap (R j) (S j)).comp (fR h)

/-! ## Colimit rings and the induced ring map `u : R → S`. -/

/-- `R = colim_i R_i`. -/
abbrev Rinf : Type _ := Ring.DirectLimit R (fun _ _ h => (fR h : R _ → R _))

/-- `S = colim_i S_i`. -/
abbrev Sinf : Type _ := Ring.DirectLimit S (fun _ _ h => (fS h : S _ → S _))

/-- The induced ring map `u : colim_i R_i → colim_i S_i`. -/
noncomputable def uinf (hsq : IsCompatible fR fS) : Rinf fR →+* Sinf fS :=
  Ring.DirectLimit.lift R (fun _ _ h => (fR h : R _ → R _)) _
    (fun i => (Ring.DirectLimit.of S (fun _ _ h => (fS h : S _ → S _)) i).comp
      (algebraMap (R i) (S i)))
    (by
      intro i j hij x
      simp only [RingHom.comp_apply]
      have : (fS hij) ((algebraMap (R i) (S i)) x)
          = (algebraMap (R j) (S j)) ((fR hij) x) := by
        have := hsq hij; rw [RingHom.ext_iff] at this; simpa using this x
      rw [← this]
      exact Ring.DirectLimit.of_f hij _)

omit [IsDirectedOrder I] [Nonempty I] [DecidableEq I] in
/-- Computation rule for `uinf`. -/
theorem uinf_of (hsq : IsCompatible fR fS) (i : I) (x : R i) :
    uinf fR fS hsq (Ring.DirectLimit.of R (fun _ _ h => (fR h : R _ → R _)) i x)
      = Ring.DirectLimit.of S (fun _ _ h => (fS h : S _ → S _)) i
          (algebraMap (R i) (S i) x) :=
  Ring.DirectLimit.lift_of _ _ _ _ _

/-- The algebra structure `R = colim R_i → S = colim S_i` induced by `uinf`. -/
@[reducible] noncomputable def alginf (hsq : IsCompatible fR fS) :
    Algebra (Rinf fR) (Sinf fS) :=
  (uinf fR fS hsq).toAlgebra

/-! ## The directed system of differentials and its colimit. -/

/-- The transition map `Ω_{ii'} : Ω[S_i⁄R_i] → Ω[S_{i'}⁄R_{i'}]` for `i ≤ j`,
induced by the commuting square at `i ≤ j`, as a morphism of abelian groups. -/
noncomputable def omegaTrans (hsq : IsCompatible fR fS) (i j : I) (hij : i ≤ j) :
    Ω[S i⁄R i] →ₗ[ℤ] Ω[S j⁄R j] :=
  sqMap (R i) (S i) (R j) (S j) (fR hij) (fS hij) (hsq hij).symm

/-- `colim_i Ω[S_i⁄R_i]`, the colimit of differentials, taken in abelian groups
(= `ℤ`-modules). -/
abbrev OmegaColim (hsq : IsCompatible fR fS) : Type _ :=
  Module.DirectLimit (R := ℤ) (ι := I) (fun i => Ω[S i⁄R i]) (omegaTrans fR fS hsq)

omit [IsDirectedOrder I] [Nonempty I] [DecidableEq I] in
/-- `omegaTrans` on `d`-generators. -/
theorem omegaTrans_D (hsq : IsCompatible fR fS) (i j : I) (hij : i ≤ j) (a : S i) :
    omegaTrans fR fS hsq i j hij (KaehlerDifferential.D (R i) (S i) a)
      = KaehlerDifferential.D (R j) (S j) (fS hij a) :=
  sqMap_D _ _ _ _ _ _ _ a

omit [IsDirectedOrder I] [Nonempty I] [DecidableEq I] in
/-- `omegaTrans` semilinearity. -/
theorem omegaTrans_smul (hsq : IsCompatible fR fS) (i j : I) (hij : i ≤ j)
    (c : S i) (x : Ω[S i⁄R i]) :
    omegaTrans fR fS hsq i j hij (c • x) = fS hij c • omegaTrans fR fS hsq i j hij x :=
  sqMap_smul _ _ _ _ _ _ _ c x

/-! ## The comparison map `Θ`. -/

/-- The per-level map `Ω_i : Ω[S_i⁄R_i] → Ω[S⁄R]`, induced by the square comparing level
`i` with the colimit, as a morphism of abelian groups. -/
noncomputable def omegaToColim (hsq : IsCompatible fR fS) (i : I) :
    Ω[S i⁄R i] →ₗ[ℤ] @KaehlerDifferential (Rinf fR) (Sinf fS) _ _ (alginf fR fS hsq) :=
  letI := alginf fR fS hsq
  sqMap (R i) (S i) (Rinf fR) (Sinf fS)
    (Ring.DirectLimit.of R (fun _ _ h => (fR h : R _ → R _)) i)
    (Ring.DirectLimit.of S (fun _ _ h => (fS h : S _ → S _)) i)
    (by
      let := alginf fR fS hsq
      ext x
      simp only [RingHom.comp_apply]
      change uinf fR fS hsq (Ring.DirectLimit.of R (fun _ _ h => (fR h : R _ → R _)) i x)
        = Ring.DirectLimit.of S (fun _ _ h => (fS h : S _ → S _)) i (algebraMap (R i) (S i) x)
      rw [uinf_of])

/-- The canonical comparison map `Θ : colim_i Ω[S_i⁄R_i] → Ω[S⁄R]`. -/
noncomputable def Theta (hsq : IsCompatible fR fS) :
    OmegaColim fR fS hsq →ₗ[ℤ]
      @KaehlerDifferential (Rinf fR) (Sinf fS) _ _ (alginf fR fS hsq) :=
  Module.DirectLimit.lift (R := ℤ) (ι := I) (fun i => Ω[S i⁄R i]) (omegaTrans fR fS hsq)
    (omegaToColim fR fS hsq)
    (by
      let := alginf fR fS hsq
      intro i j hij x
      -- omegaToColim j (omegaTrans i j x) = omegaToColim i x, by span induction on x
      have hspan := KaehlerDifferential.span_range_derivation (R i) (S i)
      have hx : x ∈ Submodule.span (S i) (Set.range (KaehlerDifferential.D (R i) (S i))) := by
        rw [hspan]; trivial
      induction hx using Submodule.span_induction with
      | mem y hy =>
          obtain ⟨a, rfl⟩ := hy
          simp only [omegaTrans, omegaToColim, sqMap_D]
          congr 1
          exact Ring.DirectLimit.of_f hij _
      | zero => simp
      | add p q _ _ hp hq => rw [map_add, map_add, map_add, hp, hq]
      | smul c p _ hp =>
          simp only [omegaTrans, omegaToColim, sqMap_smul] at hp ⊢
          rw [hp]
          congr 1
          exact Ring.DirectLimit.of_f hij _)

/-! ## Cocycle / identity laws for `fS` and `omegaTrans`. -/

section Cocycle
variable (hsq : IsCompatible fR fS)

omit [IsDirectedOrder I] [Nonempty I] [DecidableEq I] in
/-- The transition map of a directed system from a level to itself is the identity. -/
theorem fS_self (hdirS : DirectedSystem S (fun _ _ h => (fS h : S _ → S _)))
    {i : I} (h : i ≤ i) (x : S i) : fS h x = x :=
  DirectedSystem.map_self (self := hdirS) (i := i) x

omit [IsDirectedOrder I] [Nonempty I] [DecidableEq I] in
/-- The transition maps of a directed system compose: `fS hjk ∘ fS hij = fS hik`. -/
theorem fS_trans (hdirS : DirectedSystem S (fun _ _ h => (fS h : S _ → S _)))
    {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) (hik : i ≤ k) (x : S i) :
    fS hjk (fS hij x) = fS hik x :=
  DirectedSystem.map_map (self := hdirS) hij hjk x

omit [IsDirectedOrder I] [Nonempty I] [DecidableEq I] in
/-- Identity law for `omegaTrans`. -/
theorem omegaTrans_self (hdirS : DirectedSystem S (fun _ _ h => (fS h : S _ → S _)))
    {i : I} (h : i ≤ i) (x : Ω[S i⁄R i]) :
    omegaTrans fR fS hsq i i h x = x := by
  have hx : x ∈ Submodule.span (S i) (Set.range (KaehlerDifferential.D (R i) (S i))) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨a, rfl⟩ := hy
      rw [omegaTrans_D, fS_self fS hdirS]
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, ha, hb]
  | smul c a _ ha =>
      rw [omegaTrans_smul, ha]
      congr 1
      exact fS_self fS hdirS h c

omit [IsDirectedOrder I] [Nonempty I] [DecidableEq I] in
/-- Transitivity (cocycle) law for `omegaTrans`. -/
theorem omegaTrans_trans (hdirS : DirectedSystem S (fun _ _ h => (fS h : S _ → S _)))
    {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) (hik : i ≤ k)
    (x : Ω[S i⁄R i]) :
    omegaTrans fR fS hsq j k hjk (omegaTrans fR fS hsq i j hij x)
      = omegaTrans fR fS hsq i k hik x := by
  have hx : x ∈ Submodule.span (S i) (Set.range (KaehlerDifferential.D (R i) (S i))) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨a, rfl⟩ := hy
      rw [omegaTrans_D, omegaTrans_D, omegaTrans_D, fS_trans fS hdirS hij hjk hik]
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, map_add, ha, hb, map_add]
  | smul c a _ ha =>
      rw [omegaTrans_smul, omegaTrans_smul, omegaTrans_smul, ha]
      congr 1
      exact fS_trans fS hdirS hij hjk hik c

end Cocycle

/-! ## The `Sinf`-module structure on `OmegaColim`. -/

section Action

/-- A chosen common upper bound of `i` and `j`. -/
noncomputable def ub (i j : I) : I := (IsDirected.directed (r := (· ≤ ·)) i j).choose
omit [Nonempty I] [DecidableEq I] in
/-- `ub i j` is an upper bound of `i`. -/
theorem ub_left (i j : I) : i ≤ ub i j :=
  (IsDirected.directed (r := (· ≤ ·)) i j).choose_spec.left

omit [Nonempty I] [DecidableEq I] in
/-- `ub i j` is an upper bound of `j`. -/
theorem ub_right (i j : I) : j ≤ ub i j :=
  (IsDirected.directed (r := (· ≤ ·)) i j).choose_spec.right

variable (hsq : IsCompatible fR fS)

/-- Two elements of a directed colimit of rings come from a common level. -/
private theorem exists_of_common {J : Type*} [Preorder J] [IsDirectedOrder J] [Nonempty J]
    {T : J → Type*} [∀ i, CommRing (T i)] (g : ∀ ⦃i j⦄, i ≤ j → T i →+* T j)
    (s t : Ring.DirectLimit T (fun _ _ h => (g h : T _ → T _))) :
    ∃ (k : J) (a b : T k), s = Ring.DirectLimit.of T (fun _ _ h => (g h : T _ → T _)) k a ∧
      t = Ring.DirectLimit.of T (fun _ _ h => (g h : T _ → T _)) k b := by
  refine s.induction_on fun i a => t.induction_on fun i' b => ?_
  obtain ⟨k, hik, hi'k⟩ := IsDirected.directed (r := (· ≤ ·)) i i'
  exact ⟨k, g hik a, g hi'k b, (Ring.DirectLimit.of_f hik a).symm,
    (Ring.DirectLimit.of_f hi'k b).symm⟩

/-- A family `F i : T i → M` invariant under the transition maps is constant on
representatives of the same element of a directed colimit of rings. -/
private theorem eq_of_of_eq {J : Type*} [Preorder J] [IsDirectedOrder J]
    {T : J → Type*} [∀ i, CommRing (T i)] {g : ∀ ⦃i j⦄, i ≤ j → T i →+* T j}
    (hdir : DirectedSystem T (fun _ _ h => (g h : T _ → T _))) {M : Type*} (F : ∀ i, T i → M)
    (hF : ∀ i i' (h : i ≤ i') (s : T i), F i' (g h s) = F i s) {i i' : J} {s : T i} {s' : T i'}
    (heq : Ring.DirectLimit.of T (fun _ _ h => (g h : T _ → T _)) i s
         = Ring.DirectLimit.of T (fun _ _ h => (g h : T _ → T _)) i' s') :
    F i s = F i' s' := by
  obtain ⟨k, hik, hi'k⟩ := IsDirected.directed (r := (· ≤ ·)) i i'
  have hsub : Ring.DirectLimit.of T (fun _ _ h => (g h : T _ → T _)) k
      (g hik s - g hi'k s') = 0 := by
    rw [map_sub, Ring.DirectLimit.of_f, Ring.DirectLimit.of_f, heq, sub_self]
  obtain ⟨m, hkm, hz⟩ := Ring.DirectLimit.of.zero_exact (f' := fun _ _ h => (g h)) hsub
  have hab : g hkm (g hik s) = g hkm (g hi'k s') := by
    rw [← sub_eq_zero, ← map_sub]; exact hz
  rw [← hF _ _ hik, ← hF _ _ hkm, hab, hF _ _ hkm, hF _ _ hi'k]

/-- Abbreviation for the colimit inclusion of differentials. -/
noncomputable abbrev ofΩ (i : I) : Ω[S i⁄R i] →ₗ[ℤ] OmegaColim fR fS hsq :=
  Module.DirectLimit.of ℤ I (fun i => Ω[S i⁄R i]) (omegaTrans fR fS hsq) i

/-- Multiplication by `c : S j` as a `ℤ`-linear endomorphism of `Ω[S j⁄R j]`. -/
noncomputable abbrev mulZ {j : I} (c : S j) : Ω[S j⁄R j] →ₗ[ℤ] Ω[S j⁄R j] :=
  (LinearMap.lsmul (S j) (Ω[S j⁄R j]) c).restrictScalars ℤ

/-- The component map of `actLevel i s` at level `j`. -/
noncomputable def gComp (i : I) (s : S i) (j : I) : Ω[S j⁄R j] →ₗ[ℤ] OmegaColim fR fS hsq :=
  (ofΩ fR fS hsq (ub i j)).comp
    ((mulZ (fS (ub_left i j) s)).comp (omegaTrans fR fS hsq j (ub i j) (ub_right i j)))

omit [Nonempty I] in
/-- The defining formula for `gComp`: push `s` and `x` up to `ub i j`, multiply there,
and include into the colimit. -/
theorem gComp_apply (i : I) (s : S i) (j : I) (x : Ω[S j⁄R j]) :
    gComp fR fS hsq i s j x
      = ofΩ fR fS hsq (ub i j)
          (fS (ub_left i j) s • omegaTrans fR fS hsq j (ub i j) (ub_right i j) x) := rfl

omit [IsDirectedOrder I] [Nonempty I] in
/-- Collapsing of `ofΩ` along the transition maps. -/
theorem ofΩ_omegaTrans {l k : I} (hlk : l ≤ k) (y : Ω[S l⁄R l]) :
    ofΩ fR fS hsq k (omegaTrans fR fS hsq l k hlk y) = ofΩ fR fS hsq l y :=
  Module.DirectLimit.of_f

omit [Nonempty I] in
/-- A "normal form" for `gComp i s j x` at any level `m ≥ ub i j`: we may use the
image of `s` and `x` at level `m`. -/
theorem gComp_eq_at (hdirS : DirectedSystem S (fun _ _ h => (fS h : S _ → S _)))
    (i : I) (s : S i) (j : I) (x : Ω[S j⁄R j]) {m : I}
    (him : i ≤ m) (hjm : j ≤ m) (hkm : ub i j ≤ m) :
    gComp fR fS hsq i s j x
      = ofΩ fR fS hsq m (fS him s • omegaTrans fR fS hsq j m hjm x) := by
  rw [gComp_apply]
  rw [← ofΩ_omegaTrans fR fS hsq hkm]
  congr 1
  rw [omegaTrans_smul]
  congr 1
  · rw [fS_trans fS hdirS (ub_left i j) hkm him]
  · rw [omegaTrans_trans fR fS hsq hdirS (ub_right i j) hkm hjm]

omit [Nonempty I] in
/-- Well-definedness for the `lift`: `gComp` is compatible with `omegaTrans`. -/
theorem gComp_compat (hdirS : DirectedSystem S (fun _ _ h => (fS h : S _ → S _)))
    (i : I) (s : S i) (j j' : I) (hjj' : j ≤ j')
    (x : Ω[S j⁄R j]) :
    gComp fR fS hsq i s j' (omegaTrans fR fS hsq j j' hjj' x)
      = gComp fR fS hsq i s j x := by
  obtain ⟨m, hm1, hm2⟩ := IsDirected.directed (r := (· ≤ ·)) (ub i j) (ub i j')
  have him : i ≤ m := (ub_left i j).trans hm1
  have hjm : j ≤ m := (ub_right i j).trans hm1
  have hj'm : j' ≤ m := (ub_right i j').trans hm2
  rw [gComp_eq_at fR fS hsq hdirS i s j x him hjm hm1]
  rw [gComp_eq_at fR fS hsq hdirS i s j' _ him hj'm hm2]
  congr 1
  congr 1
  rw [omegaTrans_trans fR fS hsq hdirS hjj' hj'm hjm]

variable (hdirS : DirectedSystem S (fun _ _ h => (fS h : S _ → S _)))

/-- The `ℤ`-linear endomorphism of `OmegaColim` given by acting by `s : S i`. -/
noncomputable def actLevel (i : I) (s : S i) :
    OmegaColim fR fS hsq →ₗ[ℤ] OmegaColim fR fS hsq :=
  Module.DirectLimit.lift ℤ I (fun j => Ω[S j⁄R j]) (omegaTrans fR fS hsq)
    (gComp fR fS hsq i s)
    (fun j j' hjj' x => gComp_compat fR fS hsq hdirS i s j j' hjj' x)

omit [Nonempty I] in
/-- `actLevel i s` computes on the level-`j` inclusion by `gComp`. -/
theorem actLevel_ofΩ (i : I) (s : S i) (j : I) (x : Ω[S j⁄R j]) :
    actLevel fR fS hsq hdirS i s (ofΩ fR fS hsq j x) = gComp fR fS hsq i s j x := by
  simp only [actLevel, ofΩ, Module.DirectLimit.lift_of]

omit [Nonempty I] in
/-- General normal form: for any `m ≥ i, j`, acting by `s : S i` on `ofΩ j x`
collapses to level `m`. -/
theorem actLevel_ofΩ_eq (i : I) (s : S i) (j : I) (x : Ω[S j⁄R j]) {m : I}
    (him : i ≤ m) (hjm : j ≤ m) :
    actLevel fR fS hsq hdirS i s (ofΩ fR fS hsq j x)
      = ofΩ fR fS hsq m (fS him s • omegaTrans fR fS hsq j m hjm x) := by
  rw [actLevel_ofΩ]
  obtain ⟨n, hkn, hmn⟩ := IsDirected.directed (r := (· ≤ ·)) (ub i j) m
  have hin : i ≤ n := (ub_left i j).trans hkn
  have hjn : j ≤ n := (ub_right i j).trans hkn
  rw [gComp_eq_at fR fS hsq hdirS i s j x hin hjn hkn]
  rw [← ofΩ_omegaTrans fR fS hsq hmn (fS him s • omegaTrans fR fS hsq j m hjm x)]
  congr 1
  rw [omegaTrans_smul]
  congr 1
  · rw [fS_trans fS hdirS him hmn hin]
  · rw [omegaTrans_trans fR fS hsq hdirS hjm hmn hjn]

omit [Nonempty I] in
/-- Acting at the same level: `actLevel i s (ofΩ i x) = ofΩ i (s • x)`. -/
theorem actLevel_ofΩ_same (i : I) (s : S i) (x : Ω[S i⁄R i]) :
    actLevel fR fS hsq hdirS i s (ofΩ fR fS hsq i x) = ofΩ fR fS hsq i (s • x) := by
  rw [actLevel_ofΩ_eq fR fS hsq hdirS i s i x (le_refl i) (le_refl i)]
  rw [← omegaTrans_smul]
  rw [ofΩ_omegaTrans fR fS hsq (le_refl i)]

/-- Raising the acting level: acting by `s : S i` equals acting by `fS s : S i'`
when `i ≤ i'`. -/
theorem actLevel_raise (i i' : I) (hii' : i ≤ i') (s : S i) :
    actLevel fR fS hsq hdirS i' (fS hii' s) = actLevel fR fS hsq hdirS i s := by
  refine LinearMap.ext fun ω => ?_
  refine ω.induction_on fun j x => ?_
  rw [actLevel_ofΩ, actLevel_ofΩ]
  -- choose a common upper bound m of i', j, ub i j, ub i' j
  obtain ⟨m0, hm0a, hm0b⟩ := IsDirected.directed (r := (· ≤ ·)) (ub i j) (ub i' j)
  obtain ⟨m, hmm0, hmi'⟩ := IsDirected.directed (r := (· ≤ ·)) m0 i'
  have him : i ≤ m := hii'.trans hmi'
  have hjm : j ≤ m := (ub_right i j).trans (hm0a.trans hmm0)
  have hkm : ub i j ≤ m := hm0a.trans hmm0
  have hkm' : ub i' j ≤ m := hm0b.trans hmm0
  rw [gComp_eq_at fR fS hsq hdirS i s j x him hjm hkm]
  rw [gComp_eq_at fR fS hsq hdirS i' (fS hii' s) j x hmi' hjm hkm']
  congr 2
  exact (fS_trans fS hdirS hii' hmi' him s)

/-- Additivity in the acting scalar (same level). -/
theorem actLevel_add (i : I) (s t : S i) :
    actLevel fR fS hsq hdirS i (s + t)
      = actLevel fR fS hsq hdirS i s + actLevel fR fS hsq hdirS i t := by
  refine LinearMap.ext fun ω => ?_
  refine ω.induction_on fun j x => ?_
  obtain ⟨m, him, hjm⟩ := IsDirected.directed (r := (· ≤ ·)) i j
  rw [← actLevel_raise fR fS hsq hdirS i m him (s + t),
      ← actLevel_raise fR fS hsq hdirS i m him s,
      ← actLevel_raise fR fS hsq hdirS i m him t]
  rw [← ofΩ_omegaTrans fR fS hsq hjm x]
  simp only [LinearMap.add_apply]
  rw [actLevel_ofΩ_same, actLevel_ofΩ_same, actLevel_ofΩ_same, map_add, add_smul, map_add]

/-- Acting by `1` is the identity (same level). -/
theorem actLevel_one (i : I) :
    actLevel fR fS hsq hdirS i (1 : S i) = LinearMap.id := by
  refine LinearMap.ext fun ω => ?_
  refine ω.induction_on fun j x => ?_
  obtain ⟨m, him, hjm⟩ := IsDirected.directed (r := (· ≤ ·)) i j
  rw [← actLevel_raise fR fS hsq hdirS i m him (1 : S i)]
  rw [← ofΩ_omegaTrans fR fS hsq hjm x]
  simp only [LinearMap.id_coe, id_eq]
  rw [actLevel_ofΩ_same, map_one, one_smul]

/-- Multiplicativity in the acting scalar (same level). -/
theorem actLevel_mul (i : I) (s t : S i) :
    actLevel fR fS hsq hdirS i (s * t)
      = (actLevel fR fS hsq hdirS i s).comp (actLevel fR fS hsq hdirS i t) := by
  refine LinearMap.ext fun ω => ?_
  refine ω.induction_on fun j x => ?_
  obtain ⟨m, him, hjm⟩ := IsDirected.directed (r := (· ≤ ·)) i j
  rw [← actLevel_raise fR fS hsq hdirS i m him (s * t),
      ← actLevel_raise fR fS hsq hdirS i m him s,
      ← actLevel_raise fR fS hsq hdirS i m him t]
  rw [← ofΩ_omegaTrans fR fS hsq hjm x]
  rw [LinearMap.comp_apply]
  rw [actLevel_ofΩ_same, actLevel_ofΩ_same, actLevel_ofΩ_same, map_mul, mul_smul]

/-- Same-level well-definedness: if `of S i a = of S i b` in `Sinf`, the actions agree. -/
theorem actLevel_eq_of_of_eq_same (i : I) (a b : S i)
    (heq : Ring.DirectLimit.of S (fun _ _ h => (fS h : S _ → S _)) i a
         = Ring.DirectLimit.of S (fun _ _ h => (fS h : S _ → S _)) i b) :
    actLevel fR fS hsq hdirS i a = actLevel fR fS hsq hdirS i b :=
  eq_of_of_eq hdirS _ (actLevel_raise fR fS hsq hdirS) heq

/-- Full well-definedness across levels. -/
theorem actLevel_well_defined (i i' : I) (s : S i) (s' : S i')
    (heq : Ring.DirectLimit.of S (fun _ _ h => (fS h : S _ → S _)) i s
         = Ring.DirectLimit.of S (fun _ _ h => (fS h : S _ → S _)) i' s') :
    actLevel fR fS hsq hdirS i s = actLevel fR fS hsq hdirS i' s' :=
  eq_of_of_eq hdirS _ (actLevel_raise fR fS hsq hdirS) heq

/-- The underlying function of the `Sinf`-action: choose a representative. -/
noncomputable def actFun (s : Sinf fS) : OmegaColim fR fS hsq →ₗ[ℤ] OmegaColim fR fS hsq :=
  actLevel fR fS hsq hdirS (Ring.DirectLimit.exists_of s).choose
    (Ring.DirectLimit.exists_of s).choose_spec.choose

/-- Computation rule: `actFun (of i s) = actLevel i s`. -/
theorem actFun_of (i : I) (s : S i) :
    actFun fR fS hsq hdirS (Ring.DirectLimit.of S (fun _ _ h => (fS h : S _ → S _)) i s)
      = actLevel fR fS hsq hdirS i s :=
  eq_of_of_eq hdirS _ (actLevel_raise fR fS hsq hdirS)
    (Ring.DirectLimit.exists_of _).choose_spec.choose_spec

/-- Acting by `1 : Sinf` is the identity. -/
theorem actFun_one : actFun fR fS hsq hdirS (1 : Sinf fS) = LinearMap.id := by
  classical
  obtain ⟨i⟩ := ‹Nonempty I›
  have : (1 : Sinf fS) = Ring.DirectLimit.of S (fun _ _ h => (fS h : S _ → S _)) i 1 := by
    rw [map_one]
  rw [this, actFun_of, actLevel_one]

/-- The action of `Sinf` is multiplicative. -/
theorem actFun_mul (s t : Sinf fS) :
    actFun fR fS hsq hdirS (s * t)
      = (actFun fR fS hsq hdirS s).comp (actFun fR fS hsq hdirS t) := by
  obtain ⟨k, a, b, rfl, rfl⟩ := exists_of_common fS s t
  rw [← map_mul, actFun_of, actFun_of, actFun_of, actLevel_mul]

/-- The action of `Sinf` is additive in the acting scalar. -/
theorem actFun_add (s t : Sinf fS) :
    actFun fR fS hsq hdirS (s + t)
      = actFun fR fS hsq hdirS s + actFun fR fS hsq hdirS t := by
  obtain ⟨k, a, b, rfl, rfl⟩ := exists_of_common fS s t
  rw [← map_add, actFun_of, actFun_of, actFun_of, actLevel_add]

/-- The action ring homomorphism `Sinf →+* Module.End ℤ OmegaColim`. -/
noncomputable def act : Sinf fS →+* Module.End ℤ (OmegaColim fR fS hsq) where
  toFun := actFun fR fS hsq hdirS
  map_one' := actFun_one fR fS hsq hdirS
  map_mul' := actFun_mul fR fS hsq hdirS
  map_zero' := by
    classical
    obtain ⟨i⟩ := ‹Nonempty I›
    have h0 : (0 : Sinf fS) = Ring.DirectLimit.of S (fun _ _ h => (fS h : S _ → S _)) i 0 := by
      rw [map_zero]
    rw [h0, actFun_of]
    refine LinearMap.ext fun ω => ?_
    refine ω.induction_on fun j x => ?_
    obtain ⟨m, him, hjm⟩ := IsDirected.directed (r := (· ≤ ·)) i j
    rw [← actLevel_raise fR fS hsq hdirS i m him (0 : S i)]
    rw [← ofΩ_omegaTrans fR fS hsq hjm x]
    rw [actLevel_ofΩ_same]
    simp
  map_add' := actFun_add fR fS hsq hdirS

/-- `act` computes at a single level: `act (of S i s) (ofΩ i x) = ofΩ i (s • x)`. -/
theorem act_apply_ofΩ (i : I) (s : S i) (x : Ω[S i⁄R i]) :
    act fR fS hsq hdirS (Ring.DirectLimit.of S (fun _ _ h => (fS h : S _ → S _)) i s)
        (ofΩ fR fS hsq i x)
      = ofΩ fR fS hsq i (s • x) := by
  show actFun fR fS hsq hdirS _ _ = _
  rw [actFun_of, actLevel_ofΩ_same]

end Action

/-! ## The universal derivation `δ : Sinf → OmegaColim` and the left inverse. -/

section Deriv

variable (hsq : IsCompatible fR fS)
variable (hdirS : DirectedSystem S (fun _ _ h => (fS h : S _ → S _)))

/-- The `Sinf`-module structure on `OmegaColim` from the action ring hom. -/
@[reducible] noncomputable def omegaColimModule :
    Module (Sinf fS) (OmegaColim fR fS hsq) :=
  Module.compHom _ (act fR fS hsq hdirS)

/-- The underlying function of the derivation `δ`. -/
noncomputable def δFun (s : Sinf fS) : OmegaColim fR fS hsq :=
  ofΩ fR fS hsq (Ring.DirectLimit.exists_of s).choose
    (KaehlerDifferential.D _ _ (Ring.DirectLimit.exists_of s).choose_spec.choose)

omit [IsDirectedOrder I] [Nonempty I] in
/-- Raising the level in `δ`. -/
theorem δ_raise (i i' : I) (hii' : i ≤ i') (s : S i) :
    ofΩ fR fS hsq i' (KaehlerDifferential.D (R i') (S i') (fS hii' s))
      = ofΩ fR fS hsq i (KaehlerDifferential.D (R i) (S i) s) := by
  rw [← omegaTrans_D fR fS hsq i i' hii' s]
  rw [ofΩ_omegaTrans fR fS hsq hii']

omit [Nonempty I] in
/-- Same-level well-definedness for `δ`. -/
theorem δ_eq_of_of_eq_same
    (hdirS : DirectedSystem S (fun _ _ h => (fS h : S _ → S _)))
    (i : I) (a b : S i)
    (heq : Ring.DirectLimit.of S (fun _ _ h => (fS h : S _ → S _)) i a
         = Ring.DirectLimit.of S (fun _ _ h => (fS h : S _ → S _)) i b) :
    ofΩ fR fS hsq i (KaehlerDifferential.D (R i) (S i) a)
      = ofΩ fR fS hsq i (KaehlerDifferential.D (R i) (S i) b) :=
  eq_of_of_eq hdirS (fun i s => ofΩ fR fS hsq i (KaehlerDifferential.D (R i) (S i) s))
    (δ_raise fR fS hsq) heq

omit [Nonempty I] in
/-- Full well-definedness for `δ`. -/
theorem δ_well_defined
    (hdirS : DirectedSystem S (fun _ _ h => (fS h : S _ → S _)))
    (i i' : I) (s : S i) (s' : S i')
    (heq : Ring.DirectLimit.of S (fun _ _ h => (fS h : S _ → S _)) i s
         = Ring.DirectLimit.of S (fun _ _ h => (fS h : S _ → S _)) i' s') :
    ofΩ fR fS hsq i (KaehlerDifferential.D (R i) (S i) s)
      = ofΩ fR fS hsq i' (KaehlerDifferential.D (R i') (S i') s') :=
  eq_of_of_eq hdirS (fun i s => ofΩ fR fS hsq i (KaehlerDifferential.D (R i) (S i) s))
    (δ_raise fR fS hsq) heq

/-- Computation rule: `δ (of S i s) = ofΩ i (D s)`. -/
theorem δFun_of
    (hdirS : DirectedSystem S (fun _ _ h => (fS h : S _ → S _)))
    (i : I) (s : S i) :
    δFun fR fS hsq (Ring.DirectLimit.of S (fun _ _ h => (fS h : S _ → S _)) i s)
      = ofΩ fR fS hsq i (KaehlerDifferential.D (R i) (S i) s) :=
  δ_well_defined fR fS hsq hdirS _ i _ s (Ring.DirectLimit.exists_of _).choose_spec.choose_spec

/-- `δ` is additive. -/
theorem δFun_add
    (hdirS : DirectedSystem S (fun _ _ h => (fS h : S _ → S _)))
    (s t : Sinf fS) :
    δFun fR fS hsq (s + t) = δFun fR fS hsq s + δFun fR fS hsq t := by
  obtain ⟨k, a, b, rfl, rfl⟩ := exists_of_common fS s t
  rw [← map_add, δFun_of fR fS hsq hdirS, δFun_of fR fS hsq hdirS,
      δFun_of fR fS hsq hdirS, ← map_add, map_add, map_add]

/-- `δ` as an additive group homomorphism. -/
noncomputable def δAddHom
    (hdirS : DirectedSystem S (fun _ _ h => (fS h : S _ → S _))) :
    Sinf fS →+ OmegaColim fR fS hsq where
  toFun := δFun fR fS hsq
  map_zero' := by
    classical
    obtain ⟨i⟩ := ‹Nonempty I›
    have h0 : (0 : Sinf fS) = Ring.DirectLimit.of S (fun _ _ h => (fS h : S _ → S _)) i 0 := by
      rw [map_zero]
    rw [h0, δFun_of fR fS hsq hdirS, map_zero, map_zero]
  map_add' := δFun_add fR fS hsq hdirS

/-! ### Leibniz rule and `R`-annihilation for `δ`, then the left inverse.

These two facts are what make `δ` a derivation.  They are stated in terms of the
action ring-hom `act` (rather than the `•` notation of the non-instance
`Sinf`-module) to keep instance resolution predictable; inside `Theta_injective` we
register `omegaColimModule` with `letI` and rewrite `s • m = act s m` by
`rfl`/`Module.compHom` defeq. -/

/-- **Leibniz rule for `δ`.**  Reduce `s, t` to a
common level `k` via `Ring.DirectLimit.exists_of` + directedness, write
`s = of S k a`, `t = of S k b`; then `δ (s*t) = ofΩ k (D_k (a*b))` (`δFun_of` +
`map_mul`), expand by the level-wise `Derivation.leibniz`
`D_k (a*b) = a • D_k b + b • D_k a`, and recognise each summand via
`act_apply_ofΩ` (`act (of S k a) (ofΩ k (D_k b)) = ofΩ k (a • D_k b)`) and
`δFun_of` (`δ t = ofΩ k (D_k b)`, `δ s = ofΩ k (D_k a)`). -/
theorem δLeibniz (hdirS : DirectedSystem S (fun _ _ h => (fS h : S _ → S _)))
    (s t : Sinf fS) :
    δFun fR fS hsq (s * t)
      = act fR fS hsq hdirS s (δFun fR fS hsq t)
        + act fR fS hsq hdirS t (δFun fR fS hsq s) := by
  obtain ⟨k, a, b, rfl, rfl⟩ := exists_of_common fS s t
  rw [← map_mul, δFun_of fR fS hsq hdirS, δFun_of fR fS hsq hdirS,
      δFun_of fR fS hsq hdirS, Derivation.leibniz, map_add,
      act_apply_ofΩ, act_apply_ofΩ]

/-- **`δ` annihilates the image of `R`.**  Write
`r = of R i rᵢ` (`Ring.DirectLimit.exists_of`); then
`algebraMap (Rinf) (Sinf) r = uinf r = of S i (algebraMap (R i) (S i) rᵢ)`
(`uinf_of`), so `δ (algebraMap _ _ r) = ofΩ i (D_i (algebraMap (R i)(S i) rᵢ))`
(`δFun_of`), and `D_i (algebraMap (R i)(S i) rᵢ) = 0`
(`Derivation.map_algebraMap` / `KaehlerDifferential.D` kills the base ring), so
the value is `ofΩ i 0 = 0`. -/
theorem δ_algebraMap_eq_zero (hdirS : DirectedSystem S (fun _ _ h => (fS h : S _ → S _)))
    (r : Rinf fR) :
    δFun fR fS hsq
        (letI := alginf fR fS hsq; algebraMap (Rinf fR) (Sinf fS) r) = 0 := by
  show δFun fR fS hsq (uinf fR fS hsq r) = 0
  refine r.induction_on fun i rᵢ => ?_
  rw [uinf_of, δFun_of fR fS hsq hdirS, Derivation.map_algebraMap, map_zero]

end Deriv

/-! ## Bijectivity of `Θ`.

The two directions are different in character. Surjectivity is elementary and finitary:
`Ω[S⁄R]` is generated as an `S`-module by the differentials, each generator comes from some
level, and finitely many elements of a directed colimit lift to a common level.
Injectivity is the substantive half, and is proved by constructing an explicit left inverse
`Ω[S⁄R] → colim` out of the universal property of `Ω[S⁄R]`.

The left inverse is essential, not a convenience. One cannot instead argue that an element
of `Ω[S_i⁄R_i]` dying in `Ω[S⁄R]` already dies at a finite stage: that descent statement is
*equivalent* to injectivity of `Θ`, so invoking it would be circular.
-/

omit [IsDirectedOrder I] [Nonempty I] in /-- `Θ` restricted to level `i` is `omegaToColim i`. -/
  private theorem Theta_ofΩ (hsq : IsCompatible fR fS) (i : I) (y : Ω[S i⁄R i]) :
    Theta fR fS hsq (ofΩ fR fS hsq i y) = omegaToColim fR fS hsq i y := by
  simp only [Theta, ofΩ, Module.DirectLimit.lift_of]

/-- `Θ` is surjective.

`Ω[S⁄R]` is spanned as an `S`-module by the range of `d`, so it is enough to hit `0`, every
generator `d b`, sums and `S`-scalar multiples. For a generator, write `b` as the image of
some `bᵢ : S i`; then `Θ (ofΩ i (d bᵢ)) = d b`, since the level-`i` comparison map carries
`d bᵢ` to `d b`. For a scalar multiple `a • d b` with `a` coming from level `i'`, push both
`a` and `bᵢ` up to a common upper bound `k ≥ i, i'`, where the comparison map is
`S_k`-semilinear. Sums combine additively. -/
theorem Theta_surjective (hsq : IsCompatible fR fS)
    (hdirS : DirectedSystem S (fun _ _ h => (fS h : S _ → S _))) :
    Function.Surjective (Theta fR fS hsq) := by
  classical
  let : Algebra (Rinf fR) (Sinf fS) := alginf fR fS hsq
  let instSMod : Module (Sinf fS) (OmegaColim fR fS hsq) := omegaColimModule fR fS hsq hdirS
  -- The action `s • m` on `OmegaColim` unfolds to `act s m`.
  have hsmul : ∀ (s : Sinf fS) (m : OmegaColim fR fS hsq),
      s • m = act fR fS hsq hdirS s m := fun s m => rfl
  -- Intertwining: `Theta (s • ξ) = s • Theta ξ` for `s = of S i c`.
  have hint : ∀ (i : I) (c : S i) (ξ : OmegaColim fR fS hsq),
      Theta fR fS hsq
        ((Ring.DirectLimit.of S (fun _ _ h => (fS h : S _ → S _)) i c) • ξ)
        = (Ring.DirectLimit.of S (fun _ _ h => (fS h : S _ → S _)) i c)
          • Theta fR fS hsq ξ := by
    intro i c ξ
    refine ξ.induction_on fun j x => ?_
    rw [hsmul]
    show Theta fR fS hsq (actFun fR fS hsq hdirS _ (ofΩ fR fS hsq j x)) = _
    rw [actFun_of]
    -- bring i, j to a common upper bound m
    obtain ⟨m, him, hjm⟩ := IsDirected.directed (r := (· ≤ ·)) i j
    rw [actLevel_ofΩ_eq fR fS hsq hdirS i c j x him hjm]
    rw [Theta_ofΩ, Theta_ofΩ]
    -- LHS: omegaToColim m (fS him c • omegaTrans j m hjm x)
    -- by sqMap_smul:  = (of S m (fS him c)) • omegaToColim m (omegaTrans j m hjm x)
    have h1 : omegaToColim fR fS hsq m (fS him c • omegaTrans fR fS hsq j m hjm x)
        = (Ring.DirectLimit.of S (fun _ _ h => (fS h : S _ → S _)) m (fS him c))
          • omegaToColim fR fS hsq m (omegaTrans fR fS hsq j m hjm x) :=
      sqMap_smul (R m) (S m) (Rinf fR) (Sinf fS) _ _ _ (fS him c) _
    -- compatibility: omegaToColim m (omegaTrans j m x) = omegaToColim j x
    have hcompat : ∀ (l k : I) (hlk : l ≤ k) (z : Ω[S l⁄R l]),
        omegaToColim fR fS hsq k (omegaTrans fR fS hsq l k hlk z)
          = omegaToColim fR fS hsq l z := fun l k hlk z => by
      rw [← Theta_ofΩ, ← Theta_ofΩ, ofΩ_omegaTrans]
    rw [h1, hcompat j m hjm x, Ring.DirectLimit.of_f him]
  -- main argument: every element of the span of `d`-generators is in the range.
  have hgen : ∀ ω ∈ Submodule.span (Sinf fS)
      (Set.range (KaehlerDifferential.D (Rinf fR) (Sinf fS))),
      ∃ ξ, Theta fR fS hsq ξ = ω := by
    intro ω hω
    induction hω using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨b, rfl⟩ := hy
        refine b.induction_on fun i bᵢ => ?_
        refine ⟨ofΩ fR fS hsq i (KaehlerDifferential.D (R i) (S i) bᵢ), ?_⟩
        rw [Theta_ofΩ]
        show omegaToColim fR fS hsq i (KaehlerDifferential.D (R i) (S i) bᵢ) = _
        simp only [omegaToColim, sqMap_D]
    | zero => exact ⟨0, map_zero _⟩
    | add p q _ _ hp hq =>
        obtain ⟨ξp, hξp⟩ := hp
        obtain ⟨ξq, hξq⟩ := hq
        exact ⟨ξp + ξq, by rw [map_add, hξp, hξq]⟩
    | smul c p _ hp =>
        obtain ⟨ξ, hξ⟩ := hp
        refine c.induction_on fun i cᵢ => ?_
        refine ⟨(Ring.DirectLimit.of S (fun _ _ h => (fS h : S _ → S _)) i cᵢ) • ξ, ?_⟩
        rw [hint, hξ]
  intro ω
  obtain ⟨ξ, hξ⟩ := hgen ω (by
    rw [KaehlerDifferential.span_range_derivation]; trivial)
  exact ⟨ξ, hξ⟩

/-- `Θ` is injective, by exhibiting an explicit left inverse.

This is the heart of tag 031G. The left inverse `Ω[S⁄R] → colim_i Ω[S_i⁄R_i]` comes from the
universal property of `Ω[S⁄R]`, and is built in three steps.

1. Make `colim_i Ω[S_i⁄R_i]` an `S`-module. The action of `s`, coming from level `i`, on an
   element coming from level `j` is computed at a common upper bound `k`: push `s` and the
   element up to level `k`, multiply there, and include the result back. Independence of the
   choice of `k` is what makes this well defined, and it makes each inclusion
   `Ω[S_i⁄R_i] → colim` semilinear over `S_i → S`.

2. Exhibit the universal `R`-derivation `δ : S → colim`, defined on a representative
   `s` from level `i` by `δ s = ofΩ i (d sᵢ)`. This is independent of the representative,
   since two representatives agree at some higher level and `d` commutes with the transition
   maps. It is additive, annihilates the image of `R` because each level-wise `d` annihilates
   the image of `R_i` and the squares commute, and satisfies the Leibniz rule because the
   level-wise `d` does and the action of step 1 is computed level-wise.

3. The universal property of `Ω[S⁄R]` turns `δ` into an `S`-linear map
   `invTheta : Ω[S⁄R] →ₗ[S] colim` with `invTheta (d s) = δ s`.

That `invTheta ∘ Θ` is the identity is checked on elements coming from a single level, and
there on the generators `d a`, where both sides are `ofΩ i (d a)`; additivity and
semilinearity of `Θ` and `invTheta` extend this to all of `colim`. -/
theorem Theta_injective (hsq : IsCompatible fR fS)
    (hdirS : DirectedSystem S (fun _ _ h => (fS h : S _ → S _))) :
    Function.Injective (Theta fR fS hsq) := by
  classical
  let : Algebra (Rinf fR) (Sinf fS) := alginf fR fS hsq
  let instSMod : Module (Sinf fS) (OmegaColim fR fS hsq) := omegaColimModule fR fS hsq hdirS
  -- the `Rinf`-module structure on `OmegaColim` is obtained by restriction of scalars
  -- along `algebraMap (Rinf) (Sinf)`.
  let instRMod : Module (Rinf fR) (OmegaColim fR fS hsq) :=
    Module.compHom (OmegaColim fR fS hsq) ((act fR fS hsq hdirS).comp (uinf fR fS hsq))
  have instTower : IsScalarTower (Rinf fR) (Sinf fS) (OmegaColim fR fS hsq) := by
    refine ⟨fun r s m => ?_⟩
    -- both sides are `act (uinf r * s) m`; `Module.compHom` smul is `act _ m`,
    -- and `algebraMap (Rinf) (Sinf) r = uinf r`. (`algebraMap` for `alginf` is `uinf`.)
    show act fR fS hsq hdirS (uinf fR fS hsq r * s) m
        = act fR fS hsq hdirS (uinf fR fS hsq r) (act fR fS hsq hdirS s m)
    rw [map_mul]; rfl
  -- The action `s • m` on `OmegaColim` unfolds to `act s m`.
  have hsmul : ∀ (s : Sinf fS) (m : OmegaColim fR fS hsq),
      s • m = act fR fS hsq hdirS s m := fun s m => rfl
  -- δ as an `Rinf`-linear map, using Leibniz + `δ_algebraMap_eq_zero` for R-linearity.
  let δLin : Sinf fS →ₗ[Rinf fR] OmegaColim fR fS hsq :=
    { toFun := δFun fR fS hsq
      map_add' := δFun_add fR fS hsq hdirS
      map_smul' := by
        intro r s
        simp only [RingHom.id_apply]
        -- r • s in Sinf is algebraMap r * s; r • δs in OmegaColim is act (algebraMap r) (δ s).
        -- Note `algebraMap (Rinf)(Sinf) r = uinf r` (def of `alginf`); reduce both sides
        -- to `act (uinf r) (δ s)` using `δLeibniz` + `δ_algebraMap_eq_zero` (which kills
        -- the `t • δ(algebraMap r) = act _ 0` term).
        have hrs : (r • s : Sinf fS) = uinf fR fS hsq r * s := by
          rw [Algebra.smul_def]; rfl
        have hrm : (r • δFun fR fS hsq s)
            = act fR fS hsq hdirS (uinf fR fS hsq r) (δFun fR fS hsq s) := rfl
        rw [hrs, hrm, δLeibniz fR fS hsq hdirS]
        have hz : δFun fR fS hsq (uinf fR fS hsq r) = 0 :=
          δ_algebraMap_eq_zero fR fS hsq hdirS r
        rw [hz, map_zero, add_zero] }
  -- the universal derivation.
  let δDer : Derivation (Rinf fR) (Sinf fS) (OmegaColim fR fS hsq) :=
    Derivation.mk' δLin (by
      intro s t
      rw [hsmul, hsmul]
      exact δLeibniz fR fS hsq hdirS s t)
  -- the left inverse, via the universal property of `Ω[S⁄R]`.
  let invTheta : @KaehlerDifferential (Rinf fR) (Sinf fS) _ _ _ →ₗ[Sinf fS]
      OmegaColim fR fS hsq := δDer.liftKaehlerDifferential
  -- it is a genuine left inverse of `Θ`; conclude injectivity.
  have hleft : Function.LeftInverse invTheta (Theta fR fS hsq) := by
    -- by `Module.DirectLimit.induction_on` + span induction on `D`-generators.
    -- `invTheta (Theta (ofΩ i x)) = ofΩ i x` for all `i, x`, by span induction on `x`.
    have key : ∀ (i : I) (x : Ω[S i⁄R i]),
        invTheta (Theta fR fS hsq (ofΩ fR fS hsq i x)) = ofΩ fR fS hsq i x := by
      intro i x
      have hx : x ∈ Submodule.span (S i)
          (Set.range (KaehlerDifferential.D (R i) (S i))) := by
        rw [KaehlerDifferential.span_range_derivation]; trivial
      induction hx using Submodule.span_induction with
      | mem y hy =>
          obtain ⟨a, rfl⟩ := hy
          rw [Theta_ofΩ]
          -- omegaToColim i (D a) = D (Rinf)(Sinf) (of S i a)
          show invTheta (sqMap (R i) (S i) (Rinf fR) (Sinf fS) _ _ _
              (KaehlerDifferential.D (R i) (S i) a)) = _
          rw [sqMap_D]
          -- invTheta (D _ _ (of S i a)) = δDer (of S i a) = δFun (of S i a) = ofΩ i (D a)
          show invTheta (KaehlerDifferential.D (Rinf fR) (Sinf fS)
              (Ring.DirectLimit.of S (fun _ _ h => (fS h : S _ → S _)) i a)) = _
          rw [Derivation.liftKaehlerDifferential_comp_D]
          show δFun fR fS hsq
              (Ring.DirectLimit.of S (fun _ _ h => (fS h : S _ → S _)) i a) = _
          rw [δFun_of fR fS hsq hdirS]
      | zero => rw [map_zero, map_zero, map_zero]
      | add p q _ _ hp hq =>
          rw [map_add, map_add, map_add, hp, hq]
      | smul c p _ hp =>
          -- omegaToColim is `S i`-semilinear (via `of S i`); invTheta is `Sinf`-linear.
          rw [Theta_ofΩ] at hp ⊢
          have hsemi : omegaToColim fR fS hsq i (c • p)
              = (Ring.DirectLimit.of S (fun _ _ h => (fS h : S _ → S _)) i c)
                • omegaToColim fR fS hsq i p :=
            sqMap_smul (R i) (S i) (Rinf fR) (Sinf fS) _ _ _ c p
          rw [hsemi, map_smul, hp]
          -- `(of S i c) • ofΩ i p = act (of S i c) (ofΩ i p) = ofΩ i (c • p)`
          rw [hsmul, act_apply_ofΩ fR fS hsq hdirS]
    intro ω
    refine ω.induction_on fun i x => ?_
    exact key i x
  exact hleft.injective

/-- **Stacks Tag 031G.** For a system of ring maps over a directed set `I`, the
canonical comparison map `Θ : colim_i Ω[S_i⁄R_i] → Ω[S⁄R]` is bijective (an
isomorphism of abelian groups, equivalently of `S`-modules). -/
@[stacks 031G]
theorem main_theorem_031g (hsq : IsCompatible fR fS)
    (hdirS : DirectedSystem S (fun _ _ h => (fS h : S _ → S _))) :
    Function.Bijective (Theta fR fS hsq) :=
  ⟨Theta_injective fR fS hsq hdirS, Theta_surjective fR fS hsq hdirS⟩

end Stacks.KaehlerDifferential.Colimit
