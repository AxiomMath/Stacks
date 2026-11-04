module

public import Mathlib.RingTheory.Localization.Basic
public import StacksFrontier.Deformation.SquareZero.ExtensionPushoutPullback

/-!
# Restriction of first-order extensions along a localization is injective

Let `k → P` be a ring map, let `S ⊆ P` be a multiplicative subset and let `C` be a localization
of `P` at `S`. For a `C`-module `N` the restriction map of **Stacks 0GPV**

`Ext¹_C(NL_{C/k}, N) → Ext¹_P(NL_{P/k}, N)`

is injective.

The argument is the source's argument for the completion, and it is easier here. A class whose
restriction along `P → C` vanishes is, by **Stacks 0GPV**, represented by a square-zero extension
`0 → N → Y → C → 0` whose middle ring receives a `k`-algebra map from `P` splitting it over `P`.
Every `s ∈ S` becomes a unit in `C`, and the kernel of `Y → C` is square-zero, so the image of
`s` in `Y` is already a unit; the section therefore extends to `C` by `IsLocalization.lift`. A
section splits the extension — the split extension maps to `Y` by `c + n ↦ σ(c) + n` — so by
**Stacks 0GPV** read over the trivial tower `k → C → C` the class is zero.

## Main results

* `Stacks.Deformation.classEquiv_eq_zero_of_isSection`: a square-zero extension with a
  `k`-algebra section of its surjection has vanishing class.  This is where the work is, and it
  is independent of the localization; the henselization analogue of the injectivity below reuses
  it.
* `Stacks.Deformation.injective_naiveCotangentExtOneTowerMap_isLocalization`: the injectivity.

## Implementation notes

Nothing here is restricted to the coefficients a deformation problem produces: `N` is an
arbitrary `C`-module whose `P`-module structure is the restriction of its `C`-module structure,
and no finiteness, smoothness or Noetherian hypothesis enters. That is the whole difference from
the completion case, where the corresponding statement needs the middle ring of the extension to
be adically complete.

## References

* [Stacks Project, Tag 0DZ8](https://stacks.math.columbia.edu/tag/0DZ8)
* [Stacks Project, Tag 0GPV](https://stacks.math.columbia.edu/tag/0GPV)
-/

@[expose] public noncomputable section

universe w

namespace Stacks.Deformation

attribute [local implicit_reducible] Stacks.Deformation.algebraExtensionProblem

/-- An element whose image under a surjection with square-zero kernel is a unit is a unit. -/
private theorem isUnit_of_isUnit_map_of_sq_zero_ker
    {R T : Type*} [CommRing R] [CommRing T] (f : R →+* T) (hf : Function.Surjective f)
    (hker : RingHom.ker f ^ 2 = ⊥) {x : R} (hx : IsUnit (f x)) : IsUnit x := by
  obtain ⟨v, hv⟩ := hx.exists_right_inv
  obtain ⟨w, hw⟩ := hf v
  have hmem : x * w - 1 ∈ RingHom.ker f := by
    rw [RingHom.mem_ker, map_sub, map_mul, map_one, hw, hv, sub_self]
  have hnil : IsNilpotent (x * w - 1) := by
    refine ⟨2, ?_⟩
    have h := Ideal.mul_mem_mul hmem hmem
    rw [← pow_two, hker, Submodule.mem_bot] at h
    rw [pow_two]
    exact h
  have hprod : IsUnit (x * w) := by
    have h1 : x * w = 1 + (x * w - 1) := by ring
    rw [h1]
    exact hnil.isUnit_one_add
  obtain ⟨z, hz⟩ := hprod.exists_right_inv
  exact IsUnit.of_mul_eq_one (w * z) (by rw [← mul_assoc]; exact hz)

/-- The canonical `k`-algebra map from `P` into the ring of the split extension of `P` by `N`. -/
private def splitInlAux (k P : Type w) [CommRing k] [CommRing P] [Algebra k P]
    (N : Type w) [AddCommGroup N] [Module P N] :
    P →ₐ[k] (splitAlgebraExtension k P N).B' where
  toFun p := (TrivSqZeroExt.inl p : (splitAlgebraExtension k P N).B')
  map_one' := rfl
  map_mul' x y := TrivSqZeroExt.ext rfl (by
    change (0 : N) = x • (0 : N) + y • (0 : N)
    rw [smul_zero, smul_zero, add_zero])
  map_zero' := rfl
  map_add' x y := TrivSqZeroExt.ext rfl (by
    change (0 : N) = (0 : N) + (0 : N)
    rw [add_zero])
  commutes' a := rfl

/-- The canonical `k`-algebra map `p ↦ (p, 0)` from `P` into the ring of the split extension of
`P` by `N`.

This is the public restatement of the private helper `splitInlAux` above, so that other modules
can name the inclusion of `P` into the split extension. -/
@[no_expose] public def splitInlAlgHom (k P : Type w) [CommRing k] [CommRing P] [Algebra k P]
    (N : Type w) [AddCommGroup N] [Module P N] :
    P →ₐ[k] (splitAlgebraExtension k P N).B' :=
  splitInlAux k P N

private theorem toB_splitInlAux (k P : Type w) [CommRing k] [CommRing P] [Algebra k P]
    (N : Type w) [AddCommGroup N] [Module P N] (p : P) :
    (splitAlgebraExtension k P N).toB (splitInlAux k P N p) = p := rfl

/-- The inclusion `splitInlAlgHom` of `P` into the split extension of `P` by `N` is a section of
the surjection of that extension onto `P`.

This is the public restatement of the private helper `toB_splitInlAux` above, phrased for
`splitInlAlgHom`, so that other modules can use it. -/
public theorem toB_splitInlAlgHom (k P : Type w) [CommRing k] [CommRing P] [Algebra k P]
    (N : Type w) [AddCommGroup N] [Module P N] (p : P) :
    (splitAlgebraExtension k P N).toB (splitInlAlgHom k P N p) = p :=
  toB_splitInlAux k P N p

/-- A square-zero extension of `C` by `N` admitting a `k`-algebra section of its surjection to
`C` has vanishing class in `Ext¹_C(NL_{C/k}, N)`. -/
private theorem classEquiv_eq_zero_of_section (k C : Type w) [CommRing k] [CommRing C]
    [Algebra k C] (N : Type w) [AddCommGroup N] [Module C N]
    (Y : (algebraExtensionProblem k C N).CompatibleExtension.{w})
    (s : C →ₐ[k] Y.B') (hs : ∀ c : C, Y.toB (s c) = c) :
    squareZeroAlgebraExtensionClassesEquivExtOne k C N ⟦Y⟧ = 0 := by
  classical
  let X := splitAlgebraExtension k C N
  have hz : kernelInclusion Y (0 : N) = 0 := map_zero _
  have ha : ∀ x y : N, kernelInclusion Y (x + y)
      = kernelInclusion Y x + kernelInclusion Y y := fun x y => map_add _ x y
  have hm : ∀ n m : N, kernelInclusion Y n * kernelInclusion Y m = 0 := fun n m =>
    kernelInclusion_mul_kernelInclusion Y n m
  have hsm : ∀ (c : C) (n : N), kernelInclusion Y (c • n) = s c * kernelInclusion Y n :=
    fun c n => by simpa only [hs c] using (mul_kernelInclusion Y (s c) n).symm
  -- the `k`-algebra map `c + n ↦ s c + n` from the split extension to `Y`
  let f : X.B' →ₐ[k] Y.B' :=
    { toFun := fun z => s (TrivSqZeroExt.fst z) + kernelInclusion Y (TrivSqZeroExt.snd z)
      map_one' := by
        change s 1 + kernelInclusion Y 0 = 1
        rw [hz, map_one, add_zero]
      map_mul' := fun z w => by
        change s (z.fst * w.fst) + kernelInclusion Y (z.fst • w.snd + w.fst • z.snd)
          = (s z.fst + kernelInclusion Y z.snd) * (s w.fst + kernelInclusion Y w.snd)
        rw [map_mul, ha, hsm, hsm, add_mul, mul_add, mul_add, hm]
        ring
      map_zero' := by
        change s 0 + kernelInclusion Y 0 = 0
        rw [hz, map_zero, add_zero]
      map_add' := fun z w => by
        change s (z.fst + w.fst) + kernelInclusion Y (z.snd + w.snd)
          = (s z.fst + kernelInclusion Y z.snd) + (s w.fst + kernelInclusion Y w.snd)
        rw [map_add, ha]
        ring
      commutes' := fun a => by
        change s (algebraMap k C a) + kernelInclusion Y 0 = algebraMap k Y.B' a
        rw [hz, add_zero, AlgHom.commutes] }
  have hfB : ∀ z : X.B', Y.toB (f z) = algebraMap C C (X.toB z) := by
    intro z
    change Y.toB (s z.fst + kernelInclusion Y z.snd) = algebraMap C C (X.toB z)
    rw [map_add, hs, toB_kernelInclusion, add_zero, Algebra.algebraMap_self_apply]
    rfl
  have hfN : ∀ n : N, f (kernelInclusion X n)
      = kernelInclusion Y ((LinearMap.id : N →ₗ[C] N) n) := by
    intro n
    change s 0 + kernelInclusion Y n = kernelInclusion Y n
    rw [map_zero, zero_add]
  have hgpv := (exists_compatible_algebraMap_iff k C C (LinearMap.id : N →ₗ[C] N) X Y).mp
    ⟨f, hfB, hfN⟩
  rw [squareZeroAlgebraExtensionClassesEquivExtOne_split_eq_zero, map_zero,
    naiveCotangentExtOneTowerMap_self] at hgpv
  exact hgpv.symm

/-- A square-zero extension of `C` by `N` admitting a `k`-algebra section of its surjection to
`C` has vanishing class in `Ext¹_C(NL_{C/k}, N)`.

This is the public restatement of the private helper `classEquiv_eq_zero_of_section` above, so
that other modules — in particular the henselization analogue of the injectivity below — can
use it. -/
public alias classEquiv_eq_zero_of_isSection := classEquiv_eq_zero_of_section

/-- **Restriction along a localization is injective on first-order extension classes.** For a
localization `C` of `P` at a multiplicative subset `S` and a `C`-module `N`, the restriction map
`Ext¹_C(NL_{C/k}, N) → Ext¹_P(NL_{P/k}, N)` of **Stacks 0GPV** is injective.

This is the localization analogue of
`Deformation.Examples.injective_naiveCotangentExtOneTowerMap_adicCompletion`, and it holds with
no hypothesis on `P`, `S` or `N`. -/
public theorem injective_naiveCotangentExtOneTowerMap_isLocalization
    (k P : Type w) [CommRing k] [CommRing P] [Algebra k P] (S : Submonoid P)
    (C : Type w) [CommRing C] [Algebra k C] [Algebra P C] [IsScalarTower k P C]
    [IsLocalization S C]
    (N : Type w) [AddCommGroup N] [Module P N] [Module C N] [IsScalarTower P C N] :
    Function.Injective (naiveCotangentExtOneTowerMap k P C (N := N)) := by
  classical
  refine (injective_iff_map_eq_zero _).mpr fun ζ hζ => ?_
  obtain ⟨Y, hY⟩ := Quotient.exists_rep
    ((squareZeroAlgebraExtensionClassesEquivExtOne k C N).symm ζ)
  have hYζ : squareZeroAlgebraExtensionClassesEquivExtOne k C N ⟦Y⟧ = ζ :=
    hY ▸ (squareZeroAlgebraExtensionClassesEquivExtOne k C N).apply_symm_apply ζ
  -- restricted along `P → C` the extension `Y` is split, so it has a section over `P`
  obtain ⟨h, hhB, -⟩ := (exists_compatible_algebraMap_iff k P C
      (LinearMap.id : N →ₗ[P] N) (splitAlgebraExtension k P N) Y).mpr (by
        rw [squareZeroAlgebraExtensionClassesEquivExtOne_split_eq_zero, map_zero, hYζ, hζ])
  let σ : P →ₐ[k] Y.B' := h.comp (splitInlAux k P N)
  have hσ : ∀ p : P, Y.toB (σ p) = algebraMap P C p := fun p => hhB (splitInlAux k P N p)
  -- every element of `S` is already a unit in the middle ring
  have hunit : ∀ t : S, IsUnit ((σ : P →+* Y.B') t) := by
    intro t
    refine isUnit_of_isUnit_map_of_sq_zero_ker Y.toB.toRingHom Y.surjective Y.sq_zero ?_
    rw [show Y.toB.toRingHom ((σ : P →+* Y.B') t) = algebraMap P C (t : P) from hσ t]
    exact IsLocalization.map_units C t
  -- the section extends across the localization
  let τ : C →+* Y.B' := IsLocalization.lift (M := S) hunit
  have hτ : ∀ p : P, τ (algebraMap P C p) = σ p := fun p =>
    IsLocalization.lift_eq (M := S) hunit p
  have hext : Y.toB.toRingHom.comp τ = RingHom.id C :=
    IsLocalization.ringHom_ext S <| RingHom.ext fun p => (congrArg Y.toB (hτ p)).trans (hσ p)
  have hsec : ∀ c : C, Y.toB (τ c) = c := RingHom.congr_fun hext
  let τA : C →ₐ[k] Y.B' :=
    { τ with
      commutes' := fun a => by
        change τ (algebraMap k C a) = algebraMap k Y.B' a
        rw [IsScalarTower.algebraMap_apply k P C a, hτ]
        exact σ.commutes a }
  rw [← hYζ]
  exact classEquiv_eq_zero_of_section k C N Y τA hsec

end Stacks.Deformation

end
