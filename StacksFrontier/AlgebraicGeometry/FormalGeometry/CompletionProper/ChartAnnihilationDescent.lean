module

public import StacksFrontier.AlgebraicGeometry.Cohomology.LocallyNoetherian.SubQuotient
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.KernelCokernelAnnihilation
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.Quasicoherent.IdealPowerMultiple
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AffineSpecTransport
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AnnihilationLocality
public import StacksFrontier.AlgebraicGeometry.Modules.SubobjectSubmodule

/-!
# The return of the annihilation along the completion chart

`CompletionProper/AffineSpecTransport.lean` reduces the whole of [Stacks, Tag 088B] at a general
base — and with it [Stacks, Tag 088C], `hDev` and the first input of [Stacks, Tag 088E] — to one
hypothesis `h` over the completion chart `c = Spec (B ^∧) ⟶ V` of each affine open `V` of the
base, `Stacks.Algebraization.hasAffineLocalDirectImageSolution_of_adicCompletionChart`. That
hypothesis has two clauses: the first asks for a morphism `ψ` of the chart-pulled-back systems
satisfying the pulled-back characterization of the source, and the second asks that the morphism
`α` over `V` which `ψ` descends from have its levelwise kernels and cokernels annihilated by a
power of `𝒦|_V`.

**This file discharges the second clause.** It is the sheaf form of the step of the second
paragraph of the proof of Stacks 088B that brings the annihilation half of the conclusion back
from `Spec (B ^∧)`, whose commutative-algebra core is
`Stacks.Algebraization.smul_top_eq_bot_of_baseChange_adicCompletion` in
`CompletionProper/AffineLocalSolution.lean`. The two clauses are independent, and the first is
untouched here: it is the remaining obstruction analysed in
`CompletionProper/AdicBaseChangeSquares.lean`.

## Main results

* `Stacks.Algebraization.idealPowerMultiple_eq_bot_of_pullback` — **the return of an annihilation
  for one module.** For a morphism `f : X ⟶ Y` along which pullback is *faithful on the
  power-torsion coherent modules* and a power-torsion coherent `M` on `Y`, an annihilation
  `(f⁻¹𝒦 𝒪_X) ᵗ (f^*M) = 0` returns to `𝒦 ᵗ M = 0`, with the same exponent `t`.

  The power-torsion hypothesis on `M` is **essential, not bookkeeping**: for `B = ℤ`, `J = (p)`
  and `M = ℤ/q` with `q ≠ p` prime, `B ^∧ ⊗_B M = 0` is annihilated by every ideal while `M` is
  annihilated by no power of `(q)` — completion along `J` loses the part of `M` supported away
  from `V(J)`. It is what makes the faithfulness hypothesis available at all: pullback along the
  chart is an equivalence on the power-torsion coherent modules and on nothing larger.
* `Stacks.Algebraization.isKernelCokernelAnnihilatedByPower_of_pullback_app` and
  `…isKernelCokernelAnnihilatedByPower_of_pullback` — **the return of the annihilation for a
  morphism of coherent adic systems**, along a *flat* such `f`. The flatness is what identifies
  the levelwise kernel of the pulled-back morphism with the pullback of the levelwise kernel; for
  the cokernels nothing is needed, pullback being a left adjoint. The power-torsion hypothesis
  that the previous item requires is *supplied*, not assumed: each level of a coherent adic
  system is coherent and annihilated by a power of `𝒥`
  (`Stacks.Coherent.IsCoherentAdicSystem`), so the levelwise kernel is a subobject and the
  levelwise cokernel a quotient of such a level and the two items above apply to them.
* `Stacks.Algebraization.isKernelCokernelAnnihilatedByPower_of_adicCompletionChartPullback` and
  `…isKernelCokernelAnnihilatedByPower_morphismRestrict_of_adicCompletionChart` — the same at the
  completion chart of an affine base and at the completion chart of an affine open of a general
  base. **The second is clause 2 of the hypothesis of
  `Stacks.Algebraization.hasAffineLocalDirectImageSolution_of_adicCompletionChart`,** in the shape
  that binder asks for: the agreement of the chart-pullback of `α` with `ψ` levelwise is the
  hypothesis, and the conclusion is the annihilation for `α` itself.
* `Stacks.Algebraization.hasAffineLocalDirectImageSolution_of_adicCompletionChartAnnihilation` —
  **the assembly with clause 2 gone.** `Stacks.Algebraization.HasAffineLocalDirectImageSolution`
  now follows from a hypothesis over the chart of each affine open which asks only for a `ψ`
  satisfying the pulled-back characterization *and annihilated over the chart's base* — and that
  is exactly what `…exists_isDirectImageCharacterized_isKernelCokernel_adicCompletionChartBase`
  produces, its annihilation clause having previously been discarded for want of a way home.

## What is not here

**Clause 1 is untouched.** What remains of the hypothesis of
`…hasAffineLocalDirectImageSolution_of_adicCompletionChartAnnihilation` is the pulled-back
characterizing equation, which
`…exists_pullbackCharacterization_morphismRestrict_of_adicCompletionChartSquares` reduces to the
base change of `π ∣_ V` along the chart with its comparisons `ι` and `θ`, the source's own
condition `hc`, and the two squares `hδ` and `hγ`; `hγ` is the remaining obstruction described in
`CompletionProper/AdicBaseChangeSquares.lean`. Nothing here bears on it. Note also that that
theorem discards the annihilation of its `α'` on the way, so combining the two needs `ι` to carry
the annihilation across as well; that transport is not assembled here either.

## Implementation notes

The commutative-algebra return
`Stacks.Algebraization.smul_top_eq_bot_of_baseChange_adicCompletion` is **not** consumed, and
neither is the sections-of-a-pullback dictionary that turning it into a sheaf statement would
need. The sheaf form of More on Algebra 05EC along the chart is already available one level up, as
`Stacks.Algebraization.coherentIdealPowerTorsionPullback_adicCompletionChart_isEquivalence` and
its faithfulness
`Stacks.Algebraization.pullback_map_injective_of_coherentIdealPowerTorsion_adicCompletionChart`,
and faithfulness is all the return needs: `𝒦 ᵗ M = 0` says that the inclusion of the subsheaf
`𝒦 ᵗ M` vanishes (`Stacks.Algebraization.submodule_ι_eq_zero_iff`),
`Stacks.Algebraization.pullback_idealPowerMultiple_comp_eq_zero_iff` at the identity turns the
hypothesis into the vanishing of the pullback of that inclusion, and faithfulness cancels the
pullback. The subsheaf `𝒦 ᵗ M` is itself power-torsion coherent, which is what makes it an
allowed source: quasi-coherent by
`Stacks.Algebraization.idealPowerMultiple_isQuasicoherent`, hence coherent by
`Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_of_mono_of_isQuasicoherent` (Tag 01Y1) on a
locally Noetherian base, and annihilated by the same power of `𝒥` as `M` by
`idealPowerMultiple_eq_bot_of_mono`. So the exponent is never touched and the statement is never
weakened: the `t` returned is the `t` given.

`Stacks.Algebraization.isKernelCokernelAnnihilatedByPower_of_pullback_app` takes its hypotheses
levelwise rather than as an `IsKernelCokernelAnnihilatedByPower` of a
`CategoryTheory.Functor.whiskerRight`, because at the chart the datum is a morphism `ψ` of
pulled-back *coherent adic systems* agreeing with the pullback of `α` one level at a time, and
the levelwise form consumes that agreement by `congrArg` without first identifying
`((coherentAdicPullback c 𝒥).obj F).obj` with `F.obj ⋙ Scheme.Modules.pullback c` as functors.
The `whiskerRight` form is derived from it immediately.

`AlgebraicGeometry.Scheme.Modules` is a `def` for `SheafOfModules _`, agreeing with it only at
default transparency, so the ambient category of a `kernel` or a `cokernel` is named explicitly
with `(C := _)`, the complete lattice of submodules and the zero morphisms out of a bare
`SheafOfModules` are supplied by the two `local instance`s below, and the final composites are
assembled in term mode out of `congrArg` and `cast` rather than by `rw`.

No `stacks` attribute is attached. The annihilation half of the conclusion of Stacks 088B is
registered on
`Stacks.Coherent.exists_isDirectImageCharacterized_isKernelCokernel_of_affineOpenCover`, and
05EC on `IPowerTorsion.baseChange_equiv_of_quotientMap_bijective`; what is here is the descent of
one clause of a hypothesis across a flat chart.

## References

* [Stacks Project, Tag 01Y1](https://stacks.math.columbia.edu/tag/01Y1)
* [Stacks Project, Tag 05EC](https://stacks.math.columbia.edu/tag/05EC)
* [Stacks Project, Tag 0888](https://stacks.math.columbia.edu/tag/0888)
* [Stacks Project, Tag 088B](https://stacks.math.columbia.edu/tag/088B)
* [Stacks Project, Tag 088C](https://stacks.math.columbia.edu/tag/088C)
* [Stacks Project, Tag 088E](https://stacks.math.columbia.edu/tag/088E)
* [Stacks Project, Tag 0EHQ](https://stacks.math.columbia.edu/tag/0EHQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

/-! The zero morphism out of a sheaf of modules presented without
`AlgebraicGeometry.Scheme.Modules` is supplied by this `local instance`, reactivated here rather
than restated, as in `CompletionProper/FlatBaseChangeAlgebraization.lean`: instance search does
not see through `AlgebraicGeometry.Scheme.Modules`, a semireducible definition, to find the zero
morphisms of `X.Modules` for a source presented as a bare `SheafOfModules X.ringCatSheaf`. -/
attribute [local instance] Stacks.Algebraization.zeroHomOfSheafOfModules

namespace Stacks.Algebraization

open Stacks.Coherent

/-! ### The return of an annihilation along a pullback faithful on power-torsion modules -/

/-- **The return of an annihilation along a pullback faithful on power-torsion coherent
modules.** Let `f : X ⟶ Y` be a morphism of schemes with `Y` locally Noetherian, let
`𝒥 ⊆ 𝒪_Y` be a quasi-coherent sheaf of ideals and suppose that pullback along `f` is *injective
on morphisms between coherent `𝒪_Y`-modules annihilated by a power of `𝒥`* — the hypothesis `hf`.
Then for such a module `M`, any ideal sheaf `𝒦` and any exponent `t`, an annihilation

`(f ⁻¹𝒦 𝒪_X) ᵗ (f^*M) = 0`

returns to `𝒦 ᵗ M = 0`, **with the same exponent**.

This is the sheaf form of the step of the second paragraph of the proof of [Stacks, Tag 088B]
that brings the annihilation half of the conclusion back from the completed base, and it is the
converse of `Stacks.Coherent.idealPowerMultiple_eq_bot_pullback`, which pushes an annihilation
forward and needs no hypothesis at all.

**The power-torsion hypothesis on `M` is essential, not bookkeeping.** For `B = ℤ`, `J = (p)` and
`M = ℤ/q` with `q ≠ p` prime, the base change `B ^∧ ⊗_B M` is zero, hence annihilated by every
ideal, while `M` is annihilated by no power of `(q)`: completion along `J` loses the part of `M`
supported away from `V(J)`. It is also what makes `hf` available: pullback along the completion
chart is an equivalence on the power-torsion coherent modules
(`Stacks.Algebraization.coherentIdealPowerTorsionPullback_adicCompletionChart_isEquivalence`,
More on Algebra 05EC in sheaf form) and on nothing larger.

`𝒦 ᵗ M = 0` says that the inclusion of the subsheaf `𝒦 ᵗ M` vanishes,
`Stacks.Algebraization.pullback_idealPowerMultiple_comp_eq_zero_iff` at the identity of `f^*M`
turns the hypothesis into the vanishing of the pullback of that inclusion, and `hf` cancels the
pullback — the subsheaf `𝒦 ᵗ M` being itself coherent (Tag 01Y1 at
`Stacks.Algebraization.idealPowerMultiple_isQuasicoherent`) and annihilated by the same power of
`𝒥` as `M` (`idealPowerMultiple_eq_bot_of_mono`), so that it is an allowed source for `hf`. -/
public theorem idealPowerMultiple_eq_bot_of_pullback {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) (𝒥 : Y.IdealSheafData)
    (hf : ∀ {M N : Y.Modules}, coherentIdealPowerTorsion 𝒥 M →
      coherentIdealPowerTorsion 𝒥 N → ∀ {u v : M ⟶ N},
        (Scheme.Modules.pullback f).map u = (Scheme.Modules.pullback f).map v → u = v)
    (K : Y.IdealSheafData) (t : ℕ) (M : Y.Modules)
    (hM : coherentIdealPowerTorsion 𝒥 M)
    (h : idealPowerMultiple (K.comap f) t ((Scheme.Modules.pullback f).obj M) = ⊥) :
    idealPowerMultiple K t M = ⊥ := by
  obtain ⟨m, hMcoh, hMann⟩ := hM
  have : M.IsCoherent := hMcoh
  have : M.IsQuasicoherent := isQuasicoherent_of_isCoherent M
  have hPqc : ((idealPowerMultiple K t M).toSheafOfModules : Y.Modules).IsQuasicoherent :=
    idealPowerMultiple_isQuasicoherent K t M
  have hPcoh : ((idealPowerMultiple K t M).toSheafOfModules : Y.Modules).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_of_mono_of_isQuasicoherent
      (idealPowerMultiple K t M).ι
  have hPann : idealPowerMultiple 𝒥 (m + 1)
      ((idealPowerMultiple K t M).toSheafOfModules : Y.Modules) = ⊥ :=
    idealPowerMultiple_eq_bot_of_mono 𝒥 (idealPowerMultiple K t M).ι (m + 1) hMann
  have h1 : (idealPowerMultiple (K.comap f) t ((Scheme.Modules.pullback f).obj M)).ι = 0 :=
    (submodule_ι_eq_zero_iff _).2 h
  have h2 : (Scheme.Modules.pullback f).map (idealPowerMultiple K t M).ι = 0 :=
    (Category.comp_id _).symm.trans
      ((pullback_idealPowerMultiple_comp_eq_zero_iff f K t M
        (𝟙 ((Scheme.Modules.pullback f).obj M))).2
          ((congrArg (fun z => z ≫ 𝟙 ((Scheme.Modules.pullback f).obj M)) h1).trans zero_comp))
  exact (submodule_ι_eq_zero_iff _).1
    (hf ⟨m, hPcoh, hPann⟩ ⟨m, hMcoh, hMann⟩
      (h2.trans ((Scheme.Modules.pullback f).map_zero _ _).symm))

/-! ### The return of the annihilation for a morphism of coherent adic systems -/

/-- The return of an annihilation along a pullback, for a module whose pullback is only
isomorphic to the module that is annihilated. -/
private theorem idealPowerMultiple_eq_bot_of_pullback_iso {X Y : Scheme.{u}}
    [IsLocallyNoetherian Y] (f : X ⟶ Y) (𝒥 : Y.IdealSheafData)
    (hf : ∀ {M N : Y.Modules}, coherentIdealPowerTorsion 𝒥 M →
      coherentIdealPowerTorsion 𝒥 N → ∀ {u v : M ⟶ N},
        (Scheme.Modules.pullback f).map u = (Scheme.Modules.pullback f).map v → u = v)
    (K : Y.IdealSheafData) (t : ℕ) (M : Y.Modules) (hM : coherentIdealPowerTorsion 𝒥 M)
    {Z : X.Modules} (e : (Scheme.Modules.pullback f).obj M ≅ Z)
    (h : idealPowerMultiple (K.comap f) t Z = ⊥) : idealPowerMultiple K t M = ⊥ :=
  idealPowerMultiple_eq_bot_of_pullback f 𝒥 hf K t M hM
    (idealPowerMultiple_eq_bot_of_iso (K.comap f) e t h)

/-- **Tag 0888 (1) returns along a flat pullback faithful on power-torsion coherent modules, from
its levelwise form.** Let `f : X ⟶ Y` be flat with `Y` locally Noetherian, let `𝒥 ⊆ 𝒪_Y` be a
quasi-coherent sheaf of ideals, suppose pullback along `f` is injective on morphisms between
coherent `𝒪_Y`-modules annihilated by a power of `𝒥`, and let `α : F ⟶ G` be a morphism of
objects of `Coh(Y, 𝒥)`. If one positive exponent `t` annihilates the kernel and the cokernel of
the pullback `f^*(α_k)` at every level `k`, then `𝒦 ᵗ` annihilates the kernel and the cokernel of
`α_k` at every level.

**The power-torsion hypothesis that `Stacks.Algebraization.idealPowerMultiple_eq_bot_of_pullback`
needs is supplied here, not assumed.** Each level of a coherent adic system is coherent and
annihilated by a power of `𝒥` — that is the content of
`Stacks.Coherent.IsCoherentAdicSystem` — so `Ker(α_k)` is a subobject of `F_k` and `Coker(α_k)` a
quotient of `G_k`, hence both are coherent (Tag 01BY (3)) and annihilated by `𝒥 ᵏ⁺¹`, by
`idealPowerMultiple_eq_bot_of_mono` and
`Stacks.Algebraization.idealPowerMultiple_eq_bot_of_epi` respectively. This is why the return is
available for the levelwise kernels and cokernels of Stacks 088B although it is false for an
arbitrary module.

Flatness enters only to identify `f^*(Ker α_k)` with `Ker(f^*α_k)`
(`CategoryTheory.Limits.PreservesKernel.iso` at
`AlgebraicGeometry.preservesFiniteLimits_modulesPullback_of_flat`); for the cokernels
`CategoryTheory.Limits.PreservesCokernel.iso` is free, pullback being a left adjoint. The
exponent is carried across untouched in both cases.

The hypotheses are taken levelwise rather than as an
`Stacks.Algebraization.IsKernelCokernelAnnihilatedByPower` of a
`CategoryTheory.Functor.whiskerRight` because that is the form in which a morphism of
pulled-back coherent adic systems supplies them; see
`isKernelCokernelAnnihilatedByPower_of_pullback` for the whiskered form. -/
public theorem isKernelCokernelAnnihilatedByPower_of_pullback_app {X Y : Scheme.{u}}
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [Flat f] (𝒥 : Y.IdealSheafData)
    (hf : ∀ {M N : Y.Modules}, coherentIdealPowerTorsion 𝒥 M →
      coherentIdealPowerTorsion 𝒥 N → ∀ {u v : M ⟶ N},
        (Scheme.Modules.pullback f).map u = (Scheme.Modules.pullback f).map v → u = v)
    (K : Y.IdealSheafData) {F G : CoherentAdicSystems 𝒥} (α : F.obj ⟶ G.obj) (t : ℕ) (ht : 0 < t)
    (hker : ∀ k : ℕ, idealPowerMultiple (K.comap f) t
      (kernel (C := X.Modules) ((Scheme.Modules.pullback f).map (α.app (op k)))) = ⊥)
    (hcok : ∀ k : ℕ, idealPowerMultiple (K.comap f) t
      (cokernel (C := X.Modules) ((Scheme.Modules.pullback f).map (α.app (op k)))) = ⊥) :
    IsKernelCokernelAnnihilatedByPower K α := by
  have : PreservesFiniteLimits (Scheme.Modules.pullback f) :=
    AlgebraicGeometry.preservesFiniteLimits_modulesPullback_of_flat f
  have : PreservesColimits (Scheme.Modules.pullback f) :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).leftAdjoint_preservesColimits
  refine ⟨t, ht, fun k => ?_⟩
  have : (F.obj.obj (op k)).IsCoherent := F.property.1 k
  have : (G.obj.obj (op k)).IsCoherent := G.property.1 k
  have : (F.obj.obj (op k)).IsQuasicoherent := isQuasicoherent_of_isCoherent _
  have : (G.obj.obj (op k)).IsQuasicoherent := isQuasicoherent_of_isCoherent _
  refine ⟨?_, ?_⟩
  · exact idealPowerMultiple_eq_bot_of_pullback_iso f 𝒥 hf K t
      (kernel (C := Y.Modules) (α.app (op k)))
      ⟨k, AlgebraicGeometry.CoherentAbelian.isCoherent_kernel (α.app (op k)),
        idealPowerMultiple_eq_bot_of_mono 𝒥
          (kernel.ι (C := Y.Modules) (α.app (op k))) (k + 1) (F.property.2.1 k)⟩
      (PreservesKernel.iso (Scheme.Modules.pullback f) (α.app (op k))) (hker k)
  · exact idealPowerMultiple_eq_bot_of_pullback_iso f 𝒥 hf K t
      (cokernel (C := Y.Modules) (α.app (op k)))
      ⟨k, AlgebraicGeometry.CoherentAbelian.isCoherent_cokernel (α.app (op k)),
        idealPowerMultiple_eq_bot_of_epi 𝒥 (k + 1)
          (cokernel.π (C := Y.Modules) (α.app (op k))) (G.property.2.1 k)⟩
      (PreservesCokernel.iso (Scheme.Modules.pullback f) (α.app (op k))) (hcok k)

/-- **Tag 0888 (1) returns along a flat pullback faithful on power-torsion coherent modules.** The
converse of `Stacks.Coherent.isKernelCokernelAnnihilatedByPower_whiskerRight_pullback`, which
pushes the condition forward along any flat morphism with no faithfulness hypothesis: here the
termwise pullback of `α` has its levelwise kernels and cokernels annihilated by `(f ⁻¹𝒦 𝒪_X) ᵗ`
and `α` itself gets `𝒦 ᵗ`, the same exponent.

`isKernelCokernelAnnihilatedByPower_of_pullback_app` read at
`CategoryTheory.Functor.whiskerRight α (AlgebraicGeometry.Scheme.Modules.pullback f)`, whose
component at `op k` *is* `f^*(α_k)`. -/
public theorem isKernelCokernelAnnihilatedByPower_of_pullback {X Y : Scheme.{u}}
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [Flat f] (𝒥 : Y.IdealSheafData)
    (hf : ∀ {M N : Y.Modules}, coherentIdealPowerTorsion 𝒥 M →
      coherentIdealPowerTorsion 𝒥 N → ∀ {u v : M ⟶ N},
        (Scheme.Modules.pullback f).map u = (Scheme.Modules.pullback f).map v → u = v)
    (K : Y.IdealSheafData) {F G : CoherentAdicSystems 𝒥} (α : F.obj ⟶ G.obj)
    (h : IsKernelCokernelAnnihilatedByPower (K.comap f)
      (Functor.whiskerRight α (Scheme.Modules.pullback f))) :
    IsKernelCokernelAnnihilatedByPower K α := by
  obtain ⟨t, ht, hkc⟩ := h
  exact isKernelCokernelAnnihilatedByPower_of_pullback_app f 𝒥 hf K α t ht
    (fun k => (hkc k).1) (fun k => (hkc k).2)

/-! ### The return of the annihilation along the completion chart -/

section Chart

variable {Y : Scheme.{u}} [IsNoetherian Y] (B : Type u) [CommRing B] [IsNoetherianRing B]
  (I : Ideal B) (e : Y ≅ Spec (.of B)) {𝒥 : Y.IdealSheafData}
  (h : (adicIdealSheaf B I).comap e.hom = 𝒥)

include h

/-- **The return of the annihilation along the completion chart.** Let `Y` be a Noetherian scheme
with an isomorphism `e : Y ≅ Spec B`, let `I ⊆ B` be an ideal and let `𝒥 ⊆ 𝒪_Y` be the
corresponding sheaf of ideals; write `c = Spec (B ^∧) ⟶ Y` for the completion chart. Let
`α : F ⟶ G` be a morphism of objects of `Coh(Y, 𝒥)` and let `ψ` be a morphism of their pullbacks
along `c` which agrees with `c^*α` level by level. If the levelwise kernels and cokernels of `ψ`
are annihilated by a power of `c ⁻¹𝒦 𝒪`, then those of `α` are annihilated by the **same** power
of `𝒦`.

`isKernelCokernelAnnihilatedByPower_of_pullback_app` at the chart, whose two hypotheses are
`Stacks.Algebraization.flat_adicCompletionChart` (Algebra 00MB) and
`Stacks.Algebraization.pullback_map_injective_of_coherentIdealPowerTorsion_adicCompletionChart`
(More on Algebra 05EC in sheaf form, through Stacks 0EHQ). The agreement `hpb` is consumed by
`congrArg` at each level, so no identification of
`((coherentAdicPullback c 𝒥).obj F).obj` with `F.obj ⋙ Scheme.Modules.pullback c` as functors is
needed.

**Unconditional, and no completeness hypothesis on `B`.** This is the half of the source's second
paragraph that the chart does discharge for the annihilation clause: the annihilation produced
over `Spec (B ^∧)` by
`Stacks.Algebraization.exists_isDirectImageCharacterized_isKernelCokernel_adicCompletionChartBase`
comes home. -/
public theorem isKernelCokernelAnnihilatedByPower_of_adicCompletionChartPullback
    (K : Y.IdealSheafData) {F G : CoherentAdicSystems 𝒥} (α : F.obj ⟶ G.obj)
    (ψ : ((coherentAdicPullback (adicCompletionChart B I e) 𝒥).obj F).obj ⟶
      ((coherentAdicPullback (adicCompletionChart B I e) 𝒥).obj G).obj)
    (hpb : ∀ n : ℕᵒᵖ,
      (Scheme.Modules.pullback (adicCompletionChart B I e)).map (α.app n) = ψ.app n)
    (hann : IsKernelCokernelAnnihilatedByPower (K.comap (adicCompletionChart B I e)) ψ) :
    IsKernelCokernelAnnihilatedByPower K α := by
  have := flat_adicCompletionChart B I e
  obtain ⟨t, ht, hkc⟩ := hann
  refine isKernelCokernelAnnihilatedByPower_of_pullback_app (adicCompletionChart B I e) 𝒥
    (fun {_ _} hM hN {_ _} huv =>
      pullback_map_injective_of_coherentIdealPowerTorsion_adicCompletionChart B I e h hM hN huv)
    K α t ht (fun k => ?_) (fun k => ?_)
  · exact cast (congrArg (fun z => idealPowerMultiple (K.comap (adicCompletionChart B I e)) t
      (kernel z) = ⊥) (hpb (op k))).symm (hkc k).1
  · exact cast (congrArg (fun z => idealPowerMultiple (K.comap (adicCompletionChart B I e)) t
      (cokernel z) = ⊥) (hpb (op k))).symm (hkc k).2

end Chart

/-! ### Clause 2 of the hypothesis, at the completion chart of an affine open of the base -/

section AffineOpen

variable {X' X : Scheme.{u}} [IsNoetherian X'] [IsNoetherian X] (π : X' ⟶ X) [IsProper π]
  (J K : X.IdealSheafData) (G : CoherentAdicSystems J)
  (𝓕 : AlgebraicGeometry.SheafOfModules.CoherentModules X'.ringCatSheaf)
  (V : X.affineOpens) [IsNoetherianRing ↥Γ(X, V.1)]

/-- **Clause 2 of the hypothesis of
`Stacks.Algebraization.hasAffineLocalDirectImageSolution_of_adicCompletionChart`.** Let
`π : X' ⟶ X` be proper between Noetherian schemes, `𝒥, 𝒦 ⊆ 𝒪_X` quasi-coherent sheaves of ideals,
`(𝒢_n)` an object of `Coh(X, 𝒥)` and `𝓕` a coherent `𝒪_{X'}`-module. Over an affine open `V` of
`X` with `B = Γ(X, V)`, let `α` be a morphism of the restricted systems and `ψ` a morphism of
their pullbacks along `Stacks.Algebraization.affineOpenAdicCompletionChart` agreeing with the
chart-pullback of `α` level by level. If the levelwise kernels and cokernels of `ψ` are
annihilated by a power of the pulled-back `𝒦|_V`, then those of `α` are annihilated by the same
power of `𝒦|_V`.

**This is exactly the second clause of the binder `h` of
`Stacks.Algebraization.hasAffineLocalDirectImageSolution_of_adicCompletionChart`,** which asks
for that conclusion for every `α` whose chart-pullback is `ψ`; see
`hasAffineLocalDirectImageSolution_of_adicCompletionChartAnnihilation` for that binder with the
clause removed. Note that `β` does not appear: the clause is about the annihilation of a morphism
of systems and not about the characterizing equation, which is clause 1.

`isKernelCokernelAnnihilatedByPower_of_adicCompletionChartPullback` at `Y = V`, `B = Γ(X, V)` and
`I = 𝒥(V)`; the ideal sheaf matches by
`Stacks.Algebraization.comap_adicIdealSheaf_isoSpec`. **Unconditional.** -/
public theorem isKernelCokernelAnnihilatedByPower_morphismRestrict_of_adicCompletionChart
    (α : ((Stacks.Coherent.restrictFunctor J V.1.ι).obj G).obj ⟶
      ((completionFunctor V.1.toScheme (J.comap V.1.ι)).obj
        (properPushforwardCoherent (π ∣_ V.1)
          (restrictCoherentModules (π ⁻¹ᵁ V.1).ι 𝓕))).obj)
    (ψ : ((coherentAdicPullback (affineOpenAdicCompletionChart J V) (J.comap V.1.ι)).obj
        ((Stacks.Coherent.restrictFunctor J V.1.ι).obj G)).obj ⟶
      ((coherentAdicPullback (affineOpenAdicCompletionChart J V) (J.comap V.1.ι)).obj
        ((completionFunctor V.1.toScheme (J.comap V.1.ι)).obj
          (properPushforwardCoherent (π ∣_ V.1)
            (restrictCoherentModules (π ⁻¹ᵁ V.1).ι 𝓕)))).obj)
    (hpb : ∀ n : ℕᵒᵖ,
      (Scheme.Modules.pullback (affineOpenAdicCompletionChart J V)).map (α.app n) = ψ.app n)
    (hann : IsKernelCokernelAnnihilatedByPower
      ((K.comap V.1.ι).comap (affineOpenAdicCompletionChart J V)) ψ) :
    IsKernelCokernelAnnihilatedByPower (K.comap V.1.ι) α :=
  isKernelCokernelAnnihilatedByPower_of_adicCompletionChartPullback ↥Γ(X, V.1) (J.ideal V)
    V.2.isoSpec (comap_adicIdealSheaf_isoSpec J V.2) (K.comap V.1.ι) α ψ hpb hann

end AffineOpen

/-! ### The assembly with clause 2 replaced by annihilation over the chart's base -/

section Assembly

/-- **`Stacks.Algebraization.hasAffineLocalDirectImageSolution_of_adicCompletionChart` with its
second clause discharged.** `Stacks.Algebraization.HasAffineLocalDirectImageSolution` — the single
remaining binder behind [Stacks, Tag 088C], `hDev` and the first input of [Stacks, Tag 088E] —
follows from a hypothesis which asks, over the completion chart of each affine open `V` of the
base, for a morphism `ψ` of the chart-pulled-back systems such that

* `ψ` satisfies the characterization of Stacks 088B for `π ∣_ V` and
  `Stacks.Coherent.restrictDirectImageIso` *pulled back along the chart*, and
* the levelwise kernels and cokernels of `ψ` itself are annihilated by a power of the pulled-back
  `𝒦|_V`.

The second clause of
`Stacks.Algebraization.hasAffineLocalDirectImageSolution_of_adicCompletionChart` asked instead
that *every* `α` over `V` with chart-pullback `ψ` have its own levelwise kernels and cokernels
annihilated by a power of `𝒦|_V`, which is a statement over `V` about a morphism that the
hypothesis does not produce. Here it is gone:
`isKernelCokernelAnnihilatedByPower_morphismRestrict_of_adicCompletionChart` derives it from the
annihilation of `ψ`, with the same exponent.

**What this buys.** The annihilation of `ψ` over the chart's base is what
`Stacks.Algebraization.exists_isDirectImageCharacterized_isKernelCokernel_adicCompletionChartBase`
produces and what every assembly so far had to discard — `…of_baseChangeComparison` and
`…exists_pullbackCharacterization_of_adicCompletionChartSquares` both drop it with
`obtain ⟨α', hα', -⟩`, for want of a way home. So the whole of the annihilation half of Stacks
088B at a general base is now a statement over the chart's base, where the base is complete.

**What remains is clause 1 only,** and the two clauses are independent. Supplying `ψ` and the
pulled-back characterizing equation is
`…exists_pullbackCharacterization_morphismRestrict_of_adicCompletionChartSquares`, whose binders
are the base change of `π ∣_ V` along the chart with its comparisons `ι` and `θ`, the source's
condition `hc`, and the two squares `hδ` and `hγ` — `hγ` being the remaining obstruction
described in
`CompletionProper/AdicBaseChangeSquares.lean`. Feeding that `ψ` in here needs, in addition, the
annihilation of `α' ≫ ι` rather than of `α'`, i.e. the transport of the annihilation across the
comparison `ι`; that is not assembled here.

No `stacks` attribute is attached: this is a reduction of a hypothesis, not a statement of the
source. -/
public theorem hasAffineLocalDirectImageSolution_of_adicCompletionChartAnnihilation
    (h : ∀ {X' X : Scheme.{u}} [IsNoetherian X'] [IsNoetherian X] (π : X' ⟶ X) [IsProper π]
      (J K : X.IdealSheafData) (G : CoherentAdicSystems J)
      (𝓕 : AlgebraicGeometry.SheafOfModules.CoherentModules X'.ringCatSheaf)
      (β : (coherentAdicPullback π J).obj G ≅ (completionFunctor X' (J.comap π)).obj 𝓕),
      IsIso (π ∣_ K.support.compl) → ∀ V : X.affineOpens,
        letI : IsNoetherianRing ↥Γ(X, V.1) := IsLocallyNoetherian.component_noetherian V
        ∃ ψ : ((coherentAdicPullback (affineOpenAdicCompletionChart J V)
              (J.comap V.1.ι)).obj ((Stacks.Coherent.restrictFunctor J V.1.ι).obj G)).obj ⟶
            ((coherentAdicPullback (affineOpenAdicCompletionChart J V) (J.comap V.1.ι)).obj
              ((completionFunctor V.1.toScheme (J.comap V.1.ι)).obj
                (properPushforwardCoherent (π ∣_ V.1)
                  (restrictCoherentModules (π ⁻¹ᵁ V.1).ι 𝓕)))).obj,
          (∀ n : ℕ, ψ.app (op n) ≫
                (Scheme.Modules.pullback (affineOpenAdicCompletionChart J V)).map
                  (eqToHom (completionFunctor_obj V.1.toScheme (J.comap V.1.ι)
                      (properPushforwardCoherent (π ∣_ V.1)
                        (restrictCoherentModules (π ⁻¹ᵁ V.1).ι 𝓕)) n) ≫
                    directImageQuotientComparison (π ∣_ V.1) (J.comap V.1.ι) (n + 1)
                      (restrictCoherentModules (π ⁻¹ᵁ V.1).ι 𝓕).obj) =
              (Scheme.Modules.pullback (affineOpenAdicCompletionChart J V)).map
                ((directImageComparison (π ∣_ V.1) (J.comap V.1.ι)
                    ((Stacks.Coherent.restrictFunctor J V.1.ι).obj G)
                    (restrictCoherentModules (π ⁻¹ᵁ V.1).ι 𝓕)
                    (restrictDirectImageIso π V.1 J G 𝓕 β)).app (op n) ≫
                  eqToHom (pushforward_completion_obj (π ∣_ V.1) (J.comap V.1.ι)
                    (restrictCoherentModules (π ⁻¹ᵁ V.1).ι 𝓕) n))) ∧
            IsKernelCokernelAnnihilatedByPower
              ((K.comap V.1.ι).comap (affineOpenAdicCompletionChart J V)) ψ) :
    HasAffineLocalDirectImageSolution.{u} := by
  refine hasAffineLocalDirectImageSolution_of_adicCompletionChart ?_
  intro X' X _ _ π _ J K G 𝓕 β hiso V
  let : IsNoetherianRing ↥Γ(X, V.1) := IsLocallyNoetherian.component_noetherian V
  obtain ⟨ψ, hψ, hann⟩ := h π J K G 𝓕 β hiso V
  exact ⟨ψ, hψ, fun α hpb =>
    isKernelCokernelAnnihilatedByPower_morphismRestrict_of_adicCompletionChart π J K G 𝓕 V
      α ψ hpb hann⟩

end Assembly

end Stacks.Algebraization

end
