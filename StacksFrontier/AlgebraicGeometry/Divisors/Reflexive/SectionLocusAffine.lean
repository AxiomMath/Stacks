module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Stalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModulesStalkSequenceColimit
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.ReflexivePowerSystem
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.ReflexivePowers
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.SectionIsomorphismLocus
public import StacksFrontier.AlgebraicGeometry.FiberRank.GenericPoint
public import StacksFrontier.AlgebraicGeometry.Reflexive.DoubleDual
public import StacksCore.Tactic.StacksAttribute

/-!
# The colimit of the reflexive-power stalks and affine opens over a local ring

Let `X` be an integral locally Noetherian normal scheme, `ℱ` a rank one coherent reflexive
`𝒪_X`-module and `s ∈ Γ(X, ℱ)`. This module treats `ℕ`-indexed colimits of modules along transition
maps, the structure `IsStalkColimit` saying that an `𝒪_{X, x}`-algebra `A` is the colimit of the
stalks `ℱ^{[n]}_x` along multiplication by `s`, and affine opens of the spectrum of a local ring.

## Main definitions

* `transition`: the composite of `k` successive transition maps, from degree `n` to `n + k`.
* `powElt`: the image of `e : M 0` in `M n` under the transition maps.
* `specRes`: the restriction map `R → Γ(Spec R, V)`.
* `stalkLocus`: the inverse image of `sectionIsomorphismOpen X F s` under
  `X.fromSpecStalk x : Spec 𝒪_{X, x} ⟶ X`.
* `sectionPowStalk`: the element `sⁿ` of `ℱ^{[n]}_x`.
* `IsStalkColimit`: `A = colim ℱ^{[n]}_x` with transition maps multiplication by `s` and the unit
  germ going to `1`.
* `isStalkColimitOfIsColimit`: a colimiting cocone on `𝒪_X →ˢ ℱ →ˢ ℱ^{[2]} →ˢ ⋯` whose vertex
  has stalk `A` at `x` gives `IsStalkColimit F s x A`.

## Main results

* `exists_pos_powElt_mem_smul`: in an `ℕ`-indexed colimit `A` of `R`-modules, if the image of
  `e : M 0` lies in `I · A`, then `powElt t e n` lies in `I · M n` for some `n > 0`.
* `mem_smul_of_powElt_mem_smul`: if `powElt t e n` lies in `I · M n`, then the image of `e` lies
  in `I · A`.
* `reflexivePowerStalkMap_eq_modulesStalkFunctor_map` and
  `transition_eq_modulesStalkFunctor_map`: multiplication by `s` at the stalk, and the composite
  of `k` of them, are the stalks of the corresponding maps of `reflexivePowerSystem F s`.
* `map_maximalIdeal_eq_top`: an affine open of `Spec R`, `R` local, that misses the closed point
  has `𝔪 Γ(V, 𝒪_V)` equal to the unit ideal.
* `isAffineOpen_preimage_of_isAffineHom`: the inverse image of an open with affine inclusion,
  under a morphism from an affine scheme, is affine.
* `closedPoint_notMem_preimage`: for `x ∉ U`, the closed point of `Spec 𝒪_{X, x}` is not in the
  inverse image of `U`.

## References

* [Stacks Project, Tag 0EBR](https://stacks.math.columbia.edu/tag/0EBR)
* [Stacks Project, Tag 0EBN](https://stacks.math.columbia.edu/tag/0EBN)
* [Stacks Project, Tag 01AH](https://stacks.math.columbia.edu/tag/01AH)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.ReflexivePowers

universe u

namespace Stacks.AlgebraicGeometry.SectionLocusAffine

/-! ### An `ℕ`-indexed colimit of modules -/

section Colimit

variable {R : Type u} [CommRing R] {A : Type u} [AddCommGroup A] [Module R A]
    {M : ℕ → Type u} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]

/-- The composite of `k` successive transition maps, from degree `n` to degree `n + k`. -/
def transition (t : ∀ n, M n →ₗ[R] M (n + 1)) : (n k : ℕ) → (M n →ₗ[R] M (n + k))
  | _, 0 => LinearMap.id
  | n, (k + 1) => (t (n + k)).comp (transition t n k)

/-- The `n`-th power of the section: the image of `e : M 0` in `M n` under the transitions. -/
def powElt (t : ∀ n, M n →ₗ[R] M (n + 1)) (e : M 0) : (n : ℕ) → M n
  | 0 => e
  | n + 1 => t n (powElt t e n)

/-- The zeroth power is the given element of `M 0`. -/
@[simp]
lemma powElt_zero (t : ∀ n, M n →ₗ[R] M (n + 1)) (e : M 0) : powElt t e 0 = e := rfl

/-- The `(n + 1)`-st power is the `n`-th power pushed along one transition map. -/
lemma powElt_succ (t : ∀ n, M n →ₗ[R] M (n + 1)) (e : M 0) (n : ℕ) :
    powElt t e (n + 1) = t n (powElt t e n) := rfl

/-- Pushing the `n`-th power along `k` further transitions gives the `(n + k)`-th power. -/
lemma transition_powElt (t : ∀ n, M n →ₗ[R] M (n + 1)) (e : M 0) (n k : ℕ) :
    transition t n k (powElt t e n) = powElt t e (n + k) := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (t (n + k)) ih

/-- A linear map carries `I · M` into `I · N`. -/
lemma mem_smul_map {m₁ m₂ : ℕ} (I : Ideal R) (f : M m₁ →ₗ[R] M m₂) {z : M m₁}
    (hz : z ∈ I • (⊤ : Submodule R (M m₁))) : f z ∈ I • (⊤ : Submodule R (M m₂)) := by
  exact Submodule.smul_top_le_comap_smul_top I f hz

/-- A linear map `M n →ₗ[R] A` carries `I · M n` into `I · A`. -/
lemma mem_smul_map_toColimit (I : Ideal R) {n : ℕ} (j : M n →ₗ[R] A) {z : M n}
    (hz : z ∈ I • (⊤ : Submodule R (M n))) : j z ∈ I • (⊤ : Submodule R A) := by
  exact Submodule.smul_top_le_comap_smul_top I j hz

/-- Every power of the section has the same image in the colimit, namely the image of
`e : M 0`. -/
lemma apply_powElt (t : ∀ n, M n →ₗ[R] M (n + 1)) (e : M 0) (j : ∀ n, M n →ₗ[R] A)
    (hcomp : ∀ n, (j (n + 1)).comp (t n) = j n) (n : ℕ) : j n (powElt t e n) = j 0 e := by
  induction n with
  | zero => rfl
  | succ n ih => exact (LinearMap.congr_fun (hcomp n) _).trans ih

/-- Let `A` be the colimit of an `ℕ`-indexed sequence of `R`-modules `M n` along transition maps
`t n`, exhibited by maps `j n : M n →ₗ[R] A` which are compatible with the transitions
(`hcomp`), jointly surjective (`hsurj`) and injective up to a further transition (`hzero`).
If the image of `e : M 0` in `A` lies in `I · A`, then `powElt t e n` lies in `I · M n` for
some `n > 0`. -/
theorem exists_pos_powElt_mem_smul (I : Ideal R) (t : ∀ n, M n →ₗ[R] M (n + 1)) (e : M 0)
    (j : ∀ n, M n →ₗ[R] A) (hcomp : ∀ n, (j (n + 1)).comp (t n) = j n)
    (hsurj : ∀ a : A, ∃ n, ∃ m : M n, j n m = a)
    (hzero : ∀ (n : ℕ) (m : M n), j n m = 0 → ∃ k, transition t n k m = 0)
    (hunit : j 0 e ∈ I • (⊤ : Submodule R A)) :
    ∃ n, 0 < n ∧ powElt t e n ∈ I • (⊤ : Submodule R (M n)) := by
  have hmono : Monotone fun n => LinearMap.range (j n) := by
    refine monotone_nat_of_le_succ fun n => ?_
    rintro a ⟨m, rfl⟩
    exact ⟨t n m, by rw [← hcomp n]; rfl⟩
  have hmono' : Monotone fun n => I • LinearMap.range (j n) :=
    fun a b hab => Submodule.smul_mono le_rfl (hmono hab)
  have htop : (⊤ : Submodule R A) = ⨆ n, LinearMap.range (j n) := by
    refine le_antisymm (fun a _ => ?_) le_top
    obtain ⟨n, m, hm⟩ := hsurj a
    exact Submodule.mem_iSup_of_mem n ⟨m, hm⟩
  rw [htop, Submodule.smul_iSup] at hunit
  obtain ⟨n, hn⟩ := (Submodule.mem_iSup_of_directed _ hmono'.directed_le).1 hunit
  rw [← Submodule.map_top (j n), ← Submodule.map_smul''] at hn
  obtain ⟨m, hmI, hmeq⟩ := hn
  have hje : j n (powElt t e n - m) = 0 := by
    rw [map_sub, apply_powElt t e j hcomp n, hmeq, sub_self]
  obtain ⟨k, hk⟩ := hzero n _ hje
  rw [map_sub, sub_eq_zero] at hk
  have hpow : powElt t e (n + k) ∈ I • (⊤ : Submodule R (M (n + k))) := by
    rw [← transition_powElt t e n k, hk]
    exact mem_smul_map I _ hmI
  exact ⟨n + k + 1, Nat.succ_pos _, mem_smul_map I (t (n + k)) hpow⟩

/-- If `powElt t e n` lies in `I · M n` for some `n`, then the image of `e : M 0` under maps
`j n : M n →ₗ[R] A` compatible with the transitions lies in `I · A`. -/
theorem mem_smul_of_powElt_mem_smul (I : Ideal R) (t : ∀ n, M n →ₗ[R] M (n + 1)) (e : M 0)
    (j : ∀ n, M n →ₗ[R] A) (hcomp : ∀ n, (j (n + 1)).comp (t n) = j n) {n : ℕ}
    (hn : powElt t e n ∈ I • (⊤ : Submodule R (M n))) : j 0 e ∈ I • (⊤ : Submodule R A) := by
  rw [← apply_powElt t e j hcomp n]
  exact mem_smul_map_toColimit I (j n) hn

end Colimit

/-! ### Sections over an affine open of the spectrum of a local ring -/

/-- The restriction map `R → Γ(Spec R, V)`. -/
noncomputable def specRes (R : CommRingCat.{u}) (V : (Spec R).Opens) : R ⟶ Γ(Spec R, V) :=
  (Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.map (homOfLE (le_top (a := V))).op

/-- The basic open of the restriction of `r : R` to `V` is `V ⊓ D(r)`. -/
lemma basicOpen_specRes (R : CommRingCat.{u}) (V : (Spec R).Opens) (r : R) :
    (Spec R).basicOpen (specRes R V r) = V ⊓ PrimeSpectrum.basicOpen r := by
  rw [specRes]
  show (Spec R).basicOpen ((ConcreteCategory.hom ((Spec R).presheaf.map _))
    ((ConcreteCategory.hom (Scheme.ΓSpecIso R).inv) r)) = _
  rw [Scheme.basicOpen_res, basicOpen_eq_of_affine]

/-- An affine open of the spectrum of a local ring which misses the closed point has
`𝔪 Γ(V, 𝒪_V)` equal to the unit ideal. -/
theorem map_maximalIdeal_eq_top (R : CommRingCat.{u}) [IsLocalRing R] (V : (Spec R).Opens)
    (hV : IsAffineOpen V) (hx : IsLocalRing.closedPoint R ∉ V) :
    Ideal.map (specRes R V).hom (IsLocalRing.maximalIdeal R) = ⊤ := by
  rw [Ideal.map, ← hV.self_le_iSup_basicOpen_iff]
  intro p hp
  have hpne : (p : PrimeSpectrum R) ≠ IsLocalRing.closedPoint R := fun h => hx (h ▸ hp)
  have hle : (p : PrimeSpectrum R).asIdeal ≤ IsLocalRing.maximalIdeal R :=
    IsLocalRing.le_maximalIdeal (p : PrimeSpectrum R).isPrime.ne_top
  obtain ⟨r, hrm, hrp⟩ : ∃ r ∈ IsLocalRing.maximalIdeal R,
      r ∉ (p : PrimeSpectrum R).asIdeal := by
    by_contra h
    push Not at h
    exact hpne (PrimeSpectrum.ext (le_antisymm hle h))
  refine Opens.mem_iSup.2 ⟨⟨specRes R V r, ⟨r, hrm, rfl⟩⟩, ?_⟩
  rw [basicOpen_specRes]
  exact ⟨hp, hrp⟩

/-- The inverse image of an open with affine inclusion, under a morphism from an affine
scheme, is affine. -/
theorem isAffineOpen_preimage_of_isAffineHom {X Y : Scheme.{u}} (g : Y ⟶ X) (U : X.Opens)
    [IsAffineHom U.ι] [IsAffine Y] : IsAffineOpen (g ⁻¹ᵁ U) := by
  have h : IsAffineHom (g ⁻¹ᵁ U).ι :=
    isAffineHom_isStableUnderBaseChange.of_isPullback
      (isPullback_morphismRestrict g U) inferInstance
  exact isAffine_of_isAffineHom (g ⁻¹ᵁ U).ι

/-- If `x` is outside an open `U`, the closed point of `Spec 𝒪_{X, x}` is outside the inverse
image of `U` under the canonical morphism `X.fromSpecStalk x`. -/
theorem closedPoint_notMem_preimage {X : Scheme.{u}} (U : X.Opens) (x : X) (hx : x ∉ U) :
    IsLocalRing.closedPoint ↑(X.presheaf.stalk x) ∉ (X.fromSpecStalk x ⁻¹ᵁ U) :=
  fun h => hx (Scheme.fromSpecStalk_closedPoint (X := X) (x := x) ▸ h)


/-! ### The stalk locus and the powers of the section -/

/-- `U_x`: the inverse image of the isomorphism locus `sectionIsomorphismOpen X F s` under the
canonical morphism `f_x : Spec 𝒪_{X, x} ⟶ X`. -/
noncomputable abbrev stalkLocus (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] (F : X.Modules) [F.IsCoherent] (s : F.sections) (x : X) :
    (Spec (X.presheaf.stalk x)).Opens :=
  X.fromSpecStalk x ⁻¹ᵁ sectionIsomorphismOpen X F s

/-- `sⁿ ∈ ℱ^{[n]}_x`: the germ of the unit section, pushed along `n` multiplications by `s`. -/
noncomputable abbrev sectionPowStalk (X : Scheme.{u}) (F : X.Modules) (s : F.sections) (x : X)
    (n : ℕ) : reflexivePowerStalk F x n :=
  powElt (reflexivePowerStalkMap F s x) (reflexivePowerUnit F x) n

/-- The `𝒪_{X, x}`-algebra `A` is the colimit `colim ℱ^{[n]}_x` of the reflexive-power stalks,
with transition maps given by multiplication by `s`, and the unit germ goes to `1`. -/
structure IsStalkColimit {X : Scheme.{u}} (F : X.Modules) (s : F.sections) (x : X) (A : Type u)
    [CommRing A] [Algebra ↑(X.presheaf.stalk x) A] where
  /-- The canonical map `ℱ^{[n]}_x → A` into the colimit. -/
  toColimit (n : ℕ) : reflexivePowerStalk F x n →ₗ[↑(X.presheaf.stalk x)] A
  /-- The maps are compatible with multiplication by `s`. -/
  comp_transition (n : ℕ) :
    (toColimit (n + 1)).comp (reflexivePowerStalkMap F s x n) = toColimit n
  /-- The maps are jointly surjective. -/
  surjective (a : A) : ∃ n, ∃ m : reflexivePowerStalk F x n, toColimit n m = a
  /-- An element killed by one of the maps is killed by a further multiplication by `s`. -/
  eventually_zero (n : ℕ) (m : reflexivePowerStalk F x n) (h : toColimit n m = 0) :
    ∃ k, transition (reflexivePowerStalkMap F s x) n k m = 0
  /-- The germ of the unit section is the unit of `A`. -/
  map_one : toColimit 0 (reflexivePowerUnit F x) = 1

/-! ### `IsStalkColimit` from a colimit of the system of sheaves -/

section OfIsColimit

variable {X : Scheme.{u}} (F : X.Modules) (s : F.sections) (x : X)

open Stacks.ModuleSkyscraper (modulesStalkFunctor) in
/-- Multiplication by `s` at the stalk, `reflexivePowerStalkMap F s x n`, is the stalk of the
successor step `n ⟶ n + 1` of the diagram `reflexivePowerSystem F s`. -/
theorem reflexivePowerStalkMap_eq_modulesStalkFunctor_map (n : ℕ)
    (m : reflexivePowerStalk F x n) :
    reflexivePowerStalkMap F s x n m =
      ((modulesStalkFunctor X x).map
        ((reflexivePowerSystem F s).map (homOfLE (Nat.le_add_right n 1)))).hom m :=
  (congrArg (fun φ : (reflexivePowerSystem F s).obj n ⟶ (reflexivePowerSystem F s).obj (n + 1) =>
      ((modulesStalkFunctor X x).map φ).hom m) (reflexivePowerSystem_map_succ F s n)).symm

open Stacks.ModuleSkyscraper (modulesStalkFunctor) in
/-- The composite of `k` multiplications by `s` at the stalk is the stalk of the map
`n ⟶ n + k` of the diagram `reflexivePowerSystem F s`. -/
theorem transition_eq_modulesStalkFunctor_map (n k : ℕ) (m : reflexivePowerStalk F x n) :
    transition (reflexivePowerStalkMap F s x) n k m =
      ((modulesStalkFunctor X x).map
        ((reflexivePowerSystem F s).map (homOfLE (Nat.le_add_right n k)))).hom m := by
  induction k with
  | zero =>
      exact (Stacks.ModuleSkyscraper.modulesStalkFunctor_map_add_zero X x
        (reflexivePowerSystem F s) n m).symm
  | succ k ih =>
      refine Eq.trans ?_ (Stacks.ModuleSkyscraper.modulesStalkFunctor_map_add_succ X x
        (reflexivePowerSystem F s) n k m).symm
      refine Eq.trans ?_ (congrArg _ ih)
      exact reflexivePowerStalkMap_eq_modulesStalkFunctor_map F s x (n + k)
        (transition (reflexivePowerStalkMap F s x) n k m)

open Stacks.ModuleSkyscraper (modulesStalkFunctor) in
/-- Let `c` be a colimiting cocone on the system `𝒪_X →ˢ ℱ →ˢ ℱ^{[2]} →ˢ ⋯` of `𝒪_X`-modules,
and let `e` identify the stalk of its vertex at `x` with a commutative `𝒪_{X, x}`-algebra `A`,
carrying the image of the unit germ to `1`. Then `A` is the colimit of the stalks `ℱ^{[n]}_x` in
the sense of `IsStalkColimit`. -/
noncomputable def isStalkColimitOfIsColimit {c : Limits.Cocone (reflexivePowerSystem F s)}
    (hc : Limits.IsColimit c) (A : Type u) [CommRing A] [Algebra ↑(X.presheaf.stalk x) A]
    (e : ↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) c.pt.val.presheaf x) ≃ₗ[
        ↑(X.presheaf.stalk x)] A)
    (he : e (((modulesStalkFunctor X x).map (c.ι.app 0)).hom (reflexivePowerUnit F x)) = 1) :
    IsStalkColimit F s x A where
  toColimit n := e.toLinearMap.comp ((modulesStalkFunctor X x).map (c.ι.app n)).hom
  comp_transition n := LinearMap.ext fun m => congrArg e
    ((((congrArg (fun y => ((modulesStalkFunctor X x).map (c.ι.app (n + 1))).hom y)
        (reflexivePowerStalkMap_eq_modulesStalkFunctor_map F s x n m)).trans
      (Stacks.ModuleSkyscraper.modulesStalkFunctor_map_comp_apply X x
        ((reflexivePowerSystem F s).map (homOfLE (Nat.le_add_right n 1)))
        (c.ι.app (n + 1)) m).symm).trans
      (congrArg (fun φ => ((modulesStalkFunctor X x).map φ).hom m)
        (c.w (homOfLE (Nat.le_add_right n 1))))))
  surjective a := by
    obtain ⟨n, m, hm⟩ :=
      Stacks.ModuleSkyscraper.exists_modulesStalkFunctor_map_eq X x hc (e.symm a)
    exact ⟨n, m, (congrArg e hm).trans (e.apply_symm_apply a)⟩
  eventually_zero n m h := by
    have h0 : ((modulesStalkFunctor X x).map (c.ι.app n)).hom m = 0 :=
      e.injective (h.trans (map_zero e).symm)
    obtain ⟨k, hk⟩ :=
      Stacks.ModuleSkyscraper.exists_map_eq_zero_of_modulesStalkFunctor_map_eq_zero X x hc n m h0
    exact ⟨k, (transition_eq_modulesStalkFunctor_map F s x n k m).trans hk⟩
  map_one := he

end OfIsColimit

end Stacks.AlgebraicGeometry.SectionLocusAffine

end
