module

public import StacksFrontier.AlgebraicGeometry.ProjLargeDegreeSections.Basic
public import StacksFrontier.AlgebraicGeometry.ProjSerreCorrespondence.IrrelevantModules
public import StacksFrontier.AlgebraicGeometry.ProjSerreCorrespondence.TorsionVanishing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The kernel of `M ↦ M̃` is the torsion subcategory

Let `S = ⨁_{d ≥ 0} 𝒮 d` be a nonnegatively graded ring, `X = Proj 𝒮`, and let
`M = ⨁_{i ∈ ℤ} 𝒨 i` be a graded `S`-module. The companion file
`StacksFrontier.AlgebraicGeometry.ProjSerreCorrespondence.TorsionVanishing` proves one half of
the first paragraph of Tag 0BXD: a torsion graded module has zero associated sheaf. This file
proves the converse half, which is also the final paragraph of the proof of Tag 0AG7: if `M̃`
is a zero object then `M` is torsion.

The argument is the one of the source. Over the standard open `D₊(f)` of a homogeneous `f` of
degree `d > 0` the sections of `M̃` are the degree-zero localization `M₍f₎`, by
`AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv`. A zero
object has trivial sections, so every spanning fraction `x / f ^ n` of `M₍f₎` vanishes, which
is exactly annihilation of the numerator by a power of `f`. Taking `d = 1` and letting `f`
range over the degree-one elements — which generate the irrelevant ideal when `S` is generated
in degree one — shows that the irrelevant ideal is contained in the radical of the annihilator
of any fixed homogeneous element. A finitely generated ideal inside a radical has a power
inside the ideal itself, so a power of the irrelevant ideal annihilates that element, and
`Stacks.AlgebraicGeometry.ProjLargeDegreeSections.smul_eq_zero_of_irrelevant_pow_annihilates`
converts that into annihilation by every homogeneous scalar of large enough degree.

## Main results

* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence`
  `.exists_forall_smul_eq_zero_of_isZero_associatedModuleSheaf`: over a ring generated in
  degree one with finitely generated irrelevant ideal, every homogeneous element of such an `M`
  is annihilated by every homogeneous scalar of large enough degree.
* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.isIrrelevant_of_isZero_associatedModuleSheaf`
  and
  `Stacks.AlgebraicGeometry.ProjSerreCorrespondence`
  `.gradeEventuallyZero_of_isZero_associatedModuleSheaf`: the same conclusion in the language of
  Tag 0BXE, for an object of the category of graded modules — **the kernel of `M ↦ M̃` is
  contained in the irrelevant modules**, and for a finite module in the modules vanishing in all
  large degrees.
* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence`
  `.isZero_associatedModuleSheaf_iff_gradeEventuallyZero`: combined with the converse of
  `TorsionVanishing`, **`M̃ = 0` if and only if `M_n = 0` for all large `n`**, for a finite
  graded module over a Noetherian ring generated in degree one.

## Implementation notes

The degree-one hypothesis is not cosmetic in the first statement: for `f` of degree `d` only
the homogeneous elements whose degree is a multiple of `d` can appear as numerators of
degree-zero fractions over `D₊(f)`, and for the others the conclusion is false. Over the graded
ring `k[x]` with `x` in degree `2` and `M = S(1)`, every `M₍x₎` vanishes while no power of `x`
kills the degree-one element `x` of `M`; this is why the source's `d` is a common multiple of
the degrees of generators, and why the results below are stated at `d = 1`.

Vanishing of the sections is extracted from the vanishing of the object by evaluating at the
standard open: `CategoryTheory.SheafOfModules.evaluation` preserves zero morphisms, and a zero
object of `ModuleCat` has a subsingleton carrier.

The Noetherian corollary assumes `IsNoetherianRing S`, which is what discharges finite
generation of the irrelevant ideal; no hypothesis on `𝒮 0` is needed for that step.

## Implementation notes

That a power of a homogeneous `f` of positive degree annihilates every homogeneous element of
`M` whose degree is a multiple of `deg f` is proved here as a local `have` rather than as a
declaration of its own: the sibling development of Tag 0B5R states it, in the strictly more
general form that allows an arbitrary integer degree divisible by `deg f`, as
`Stacks.AlgebraicGeometry.ProjSerreCorrespondence.exists_pow_smul_eq_zero_of_isZero_of_dvd`.
Once that lands, the `have` should be replaced by a call to it.

## References

* [Stacks Project, Tag 0BXD](https://stacks.math.columbia.edu/tag/0BXD)
* [Stacks Project, Tag 0AG7](https://stacks.math.columbia.edu/tag/0AG7)
* [Stacks Project, Tag 0BXF](https://stacks.math.columbia.edu/tag/0BXF)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite DirectSum
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj
open scoped Stacks.GradedLocalization

namespace Stacks.AlgebraicGeometry.ProjSerreCorrespondence

universe u v w t

section Ungraded

variable {S : Type u} {M : Type v} {σ : Type w} {τ : Type t}
  [CommRing S] [AddCommGroup M] [Module S M]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [Decomposition 𝒨]
  [SetLike.GradedSMul 𝒮 𝒨]

/-- If the associated sheaf is a zero object then the degree-zero localization `M₍f₎` at a
homogeneous `f` of positive degree is trivial: it is the module of sections over `D₊(f)`. -/
theorem subsingleton_degreeZeroLocalization_of_isZero_associatedModuleSheaf
    (h : Limits.IsZero (associatedModuleSheaf 𝒮 𝒨)) {d : ℕ} (hd : 0 < d) {f : S}
    (hf : f ∈ 𝒮 d) : Subsingleton (GradedModuleDegreeZeroLocalization 𝒮 𝒨 f) := by
  have hid : 𝟙 (associatedModuleSheaf 𝒮 𝒨) = 0 := (Limits.IsZero.iff_id_eq_zero _).mp h
  have : Subsingleton ((associatedModuleSheaf 𝒮 𝒨).val.obj
      (op (ProjectiveSpectrum.basicOpen 𝒮 f))) := by
    have hsec : ∀ a : (associatedModuleSheaf 𝒮 𝒨).val.obj
        (op (ProjectiveSpectrum.basicOpen 𝒮 f)), a = 0 := fun a => by
      have ha := congrArg
        (fun φ : associatedModuleSheaf 𝒮 𝒨 ⟶ associatedModuleSheaf 𝒮 𝒨 =>
          (φ.val.app (op (ProjectiveSpectrum.basicOpen 𝒮 f))).hom a) hid
      have hz0 : ((0 : associatedModuleSheaf 𝒮 𝒨 ⟶ associatedModuleSheaf 𝒮 𝒨).val.app
          (op (ProjectiveSpectrum.basicOpen 𝒮 f))).hom a = 0 := rfl
      simpa [hz0] using ha
    exact ⟨fun a b => by rw [hsec a, hsec b]⟩
  exact (associatedModuleSheafStandardOpenEquiv 𝒮 𝒨 hf hd).toEquiv.symm.subsingleton

/-- **The kernel of `M ↦ M̃` consists of irrelevant modules.** Over a graded ring generated in
degree one with finitely generated irrelevant ideal, if the associated sheaf of `M` is a zero
object then every homogeneous element of `M` is annihilated by every homogeneous scalar of
large enough degree.

The degree-one elements generate the irrelevant ideal, and each of them has a power killing the
given element, so the irrelevant ideal lies in the radical of its annihilator; finite generation
turns that into a power of the irrelevant ideal inside the annihilator, and degree-one
generation turns that into a bound on degrees. -/
@[ega "II 2.5.6" "necessity clause"]
theorem exists_forall_smul_eq_zero_of_isZero_associatedModuleSheaf
    (hgen : Algebra.adjoin (𝒮 0) ((𝒮 1 : Set S)) = ⊤)
    (hfg : (HomogeneousIdeal.irrelevant 𝒮).toIdeal.FG)
    (h : Limits.IsZero (associatedModuleSheaf 𝒮 𝒨)) {i : ℤ} {x : M} (hx : x ∈ 𝒨 i) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k → ∀ a ∈ 𝒮 k, a • x = 0 := by
  have key : ∀ {d : ℕ}, 0 < d → ∀ {f : S}, f ∈ 𝒮 d → ∀ {m : ℤ},
      x ∈ 𝒨 (m * d) → ∃ k : ℕ, f ^ k • x = 0 := by
    intro d hd f hf m hxm
    have := subsingleton_degreeZeroLocalization_of_isZero_associatedModuleSheaf 𝒮 𝒨 h hd hf
    let := Module.compHom (R := Localization.Away f)
      (LocalizedModule.Away (R := S) f M)
      (algebraMap (HomogeneousLocalization.Away 𝒮 f) (Localization.Away f))
    set e : ℕ := m.natAbs with he
    have hem : 0 ≤ (e : ℤ) + m := by omega
    set n : ℕ := ((e : ℤ) + m).toNat with hn
    have hncast : ((n : ℤ)) = (e : ℤ) + m := Int.toNat_of_nonneg hem
    have hmem : f ^ e • x ∈ 𝒨 (n • (d : ℤ)) := by
      have hpow : f ^ e ∈ 𝒮 (e • d) := SetLike.pow_mem_graded _ hf
      have hsmul := SetLike.GradedSMul.smul_mem (A := 𝒮) (B := 𝒨) hpow hxm
      rw [smul_eq_mul] at hsmul
      have hdeg : (((e * d : ℕ) : ℤ) + m * d) = n • (d : ℤ) := by
        rw [nsmul_eq_mul, hncast]
        push_cast
        ring
      rw [← hdeg]
      exact hsmul
    have hspan : (LocalizedModule.mk (f ^ e • x) ⟨f ^ n, ⟨n, rfl⟩⟩ :
        LocalizedModule.Away (R := S) f M) ∈ GradedModuleDegreeZeroLocalization 𝒮 𝒨 f :=
      Submodule.subset_span ⟨d, n, hf, f ^ e • x, hmem, rfl⟩
    have hzero : (LocalizedModule.mk (f ^ e • x) ⟨f ^ n, ⟨n, rfl⟩⟩ :
        LocalizedModule.Away (R := S) f M) = 0 := by
      have hsub := Subsingleton.elim
        (⟨_, hspan⟩ : GradedModuleDegreeZeroLocalization 𝒮 𝒨 f) 0
      simpa using congrArg Subtype.val hsub
    rw [show (0 : LocalizedModule.Away (R := S) f M) = LocalizedModule.mk 0 1 from
      (LocalizedModule.zero_mk 1).symm, LocalizedModule.mk_eq] at hzero
    obtain ⟨⟨-, j, rfl⟩, hu⟩ := hzero
    simp only [Submonoid.smul_def, one_smul, smul_zero] at hu
    exact ⟨j + e, by rw [pow_add, mul_smul]; exact hu⟩
  have hrad : (HomogeneousIdeal.irrelevant 𝒮).toIdeal ≤
      (Submodule.span S {x}).annihilator.radical := by
    rw [← span_degreeOne_eq_irrelevant 𝒮 hgen, Ideal.span_le]
    intro g hg
    obtain ⟨k, hk⟩ := key Nat.one_pos (SetLike.mem_coe.mp hg) (m := i) (by simpa using hx)
    exact ⟨k, (Submodule.mem_annihilator_span_singleton _ _).2 hk⟩
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad hfg
  exact ⟨N, fun k hk a ha =>
    ProjLargeDegreeSections.smul_eq_zero_of_irrelevant_pow_annihilates 𝒮 hgen
      (fun b hb => (Submodule.mem_annihilator_span_singleton _ _).1 (hN hb)) hk ha⟩

end Ungraded

section Packaged

open Stacks.AlgebraicGeometry.ProjSheafFunctoriality

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- **Stacks 0BXD and 0AG7, the converse half of the first step.** Over a graded ring generated
in degree one with finitely generated irrelevant ideal, a graded module whose associated sheaf
is a zero object is irrelevant in the sense of Tag 0BXE, for the degree `d = 1`. -/
theorem isIrrelevant_of_isZero_associatedModuleSheaf {M : GradedModuleCat.{u, v, w} 𝒮}
    (hgen : Algebra.adjoin (𝒮 0) ((𝒮 1 : Set S)) = ⊤)
    (hfg : (HomogeneousIdeal.irrelevant 𝒮).toIdeal.FG)
    (h : Limits.IsZero ((associatedModuleSheafFunctor 𝒮).obj M)) :
    IsIrrelevant 𝒮 1 M := by
  intro i x hx
  obtain ⟨N, hN⟩ := exists_forall_smul_eq_zero_of_isZero_associatedModuleSheaf 𝒮 M.grade
    hgen hfg h hx
  refine ⟨N + i.toNat, fun n hn k hk hki a ha => hN k ?_ a ha⟩
  have hi : i ≤ (i.toNat : ℤ) := Int.self_le_toNat i
  have hn' : ((N + i.toNat : ℕ) : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
  push_cast at hn' hki
  omega

/-- **Stacks 0BXD and 0AG7, the converse half of the first step, for a finite module.** Over a
graded ring generated in degree one with finitely generated irrelevant ideal, a finite graded
module whose associated sheaf is a zero object has vanishing homogeneous components in all
large degrees. -/
@[ega "II 2.7.3" "(ii)"]
theorem gradeEventuallyZero_of_isZero_associatedModuleSheaf {M : GradedModuleCat.{u, v, w} 𝒮}
    (hgen : Algebra.adjoin (𝒮 0) ((𝒮 1 : Set S)) = ⊤)
    (hfg : (HomogeneousIdeal.irrelevant 𝒮).toIdeal.FG) [Module.Finite S M.carrier]
    (h : Limits.IsZero ((associatedModuleSheafFunctor 𝒮).obj M)) :
    GradeEventuallyZero 𝒮 1 M :=
  gradeEventuallyZero_of_isIrrelevant 𝒮 Nat.one_pos
    (isIrrelevant_of_isZero_associatedModuleSheaf 𝒮 hgen hfg h)

/-- The Noetherian form of the preceding result: over a Noetherian graded ring generated in
degree one, a finite graded module whose associated sheaf is a zero object vanishes in all
large degrees. Finite generation of the irrelevant ideal is automatic. -/
@[ega "II 2.7.3" "(ii)"]
theorem gradeEventuallyZero_of_isZero_associatedModuleSheaf_of_isNoetherianRing
    [IsNoetherianRing S] {M : GradedModuleCat.{u, v, w} 𝒮}
    (hgen : Algebra.adjoin (𝒮 0) ((𝒮 1 : Set S)) = ⊤) [Module.Finite S M.carrier]
    (h : Limits.IsZero ((associatedModuleSheafFunctor 𝒮).obj M)) :
    GradeEventuallyZero 𝒮 1 M :=
  gradeEventuallyZero_of_isZero_associatedModuleSheaf 𝒮 hgen
    (Ideal.fg_of_isNoetherianRing _) h

/-- **Stacks 0BXD, the first paragraph.** Over a Noetherian graded ring generated in degree one,
the associated sheaf of a finite graded module is a zero object exactly when the module vanishes
in all large degrees — that is, the kernel of `M ↦ M̃` on `Mod^{fg}_S` is precisely the torsion
subcategory. -/
@[ega "II 2.5.6" "special case", ega "II 2.7.3" "(ii), special case", ega "II 3.4.2" "special case"]
theorem isZero_associatedModuleSheaf_iff_gradeEventuallyZero
    [IsNoetherianRing S] {M : GradedModuleCat.{u, v, w} 𝒮}
    (hgen : Algebra.adjoin (𝒮 0) ((𝒮 1 : Set S)) = ⊤) [Module.Finite S M.carrier] :
    Limits.IsZero ((associatedModuleSheafFunctor 𝒮).obj M) ↔ GradeEventuallyZero 𝒮 1 M := by
  refine ⟨gradeEventuallyZero_of_isZero_associatedModuleSheaf_of_isNoetherianRing 𝒮 hgen,
    fun hz => ?_⟩
  obtain ⟨N, hN⟩ := hz
  refine isZero_associatedModuleSheaf_of_eventually_eq_zero 𝒮 M.grade
    (N := (N : ℤ)) fun n hn y hy => ?_
  have hnn : ((n.toNat : ℤ) * ((1 : ℕ) : ℤ)) = n := by
    push_cast
    omega
  refine eq_zero_of_mem_grade_eq_bot 𝒮 (hN n.toNat (by omega)) ?_
  rw [hnn]
  exact hy

end Packaged

end Stacks.AlgebraicGeometry.ProjSerreCorrespondence

end
