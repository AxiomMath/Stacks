module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.PrincipalIdealDomain
public import StacksFrontier.Homology.KFlat.BifunctorTruncationGE
public import StacksFrontier.Homology.KFlat.Resolution

/-!
# Bounded below complexes of flat modules over the integers

Let `Λ = ULift ℤ` be a copy of the integers in the universe of its modules. Over `Λ` a submodule
of a flat module is flat, because `Λ` is a Dedekind domain and flatness is the vanishing of
torsion. Two consequences are recorded here.

* The cycle modules of a complex of flat `Λ`-modules are flat.
* Every object of `D(Λ)` whose cohomology vanishes below `b` is represented by a complex of flat
  `Λ`-modules which vanishes below `b - 1`. This is the first step of the proof of Stacks 0F0E:
  take a resolution `L` with flat terms (Stacks 06Y4) and its canonical truncation
  `τ^{≥ b - 1}L`, whose term in degree `b - 1` is the image of the differential, a submodule of
  the flat module `Lᵇ`. Here `ℤ` having global dimension one is the flatness of submodules.

## Main results

* `CochainComplex.ULiftInt.flat_of_mono`: a submodule of a flat `ULift ℤ`-module is flat.
* `CochainComplex.ULiftInt.flat_cycles`: the cycles of a complex of flat `ULift ℤ`-modules are
  flat.
* `CochainComplex.ULiftInt.exists_flat_isStrictlyGE_iso`: an object of `D(ULift ℤ)` which is
  cohomologically `≥ b` is the image of a complex of flat modules which is strictly `≥ b - 1`.

## References

* [Stacks Project, Tag 0F0E](https://stacks.math.columbia.edu/tag/0F0E)
* [Stacks Project, Tag 0653](https://stacks.math.columbia.edu/tag/0653)
* [Stacks Project, Tag 06Y4](https://stacks.math.columbia.edu/tag/06Y4)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe t w

namespace CochainComplex.ULiftInt

/-- **A submodule of a flat module over a universe-lifted copy of `ℤ` is flat.** The lifted
integers are a Dedekind domain, over which flatness is the vanishing of the torsion submodule,
and torsion elements of `M` are carried to torsion elements of `N` by the injective map `i`. -/
theorem flat_of_mono {M N : ModuleCat.{w} (ULift.{w} ℤ)} (i : M ⟶ N) [Mono i]
    [Module.Flat (ULift.{w} ℤ) N] : Module.Flat (ULift.{w} ℤ) M := by
  let : IsPrincipalIdealRing (ULift.{w} ℤ) :=
    IsPrincipalIdealRing.of_surjective (ULift.ringEquiv : ULift.{w} ℤ ≃+* ℤ).symm.toRingHom
      (ULift.ringEquiv : ULift.{w} ℤ ≃+* ℤ).symm.surjective
  let : IsDomain (ULift.{w} ℤ) :=
    MulEquiv.isDomain ℤ (ULift.ringEquiv : ULift.{w} ℤ ≃+* ℤ).toMulEquiv
  have hi : Function.Injective i.hom := (ModuleCat.mono_iff_injective i).1 inferInstance
  have : Module.IsTorsionFree (ULift.{w} ℤ) M :=
    hi.moduleIsTorsionFree i.hom (fun r m => i.hom.map_smul r m)
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout,
    ← Submodule.isTorsionFree_iff_torsion_eq_bot]
  infer_instance

/-- **The cycles of a complex of flat modules over a universe-lifted copy of `ℤ` are flat**, being
submodules of its terms. -/
theorem flat_cycles (P : CochainComplex (ModuleCat.{w} (ULift.{w} ℤ)) ℤ)
    (hP : ∀ q, Module.Flat (ULift.{w} ℤ) (P.X q)) (q : ℤ) :
    Module.Flat (ULift.{w} ℤ) (P.cycles q) := by
  have := hP q
  exact flat_of_mono (P.iCycles q)

variable [HasDerivedCategory.{t} (ModuleCat.{w} (ULift.{w} ℤ))]

/-- **An object of `D(ℤ)` which is cohomologically `≥ b` is represented by a complex of flat
modules which is strictly `≥ b - 1`.** Resolve a representative by a complex `L` with flat terms
(Stacks 06Y4, `CochainComplex.KFlat.exists_kFlat_resolution`) and truncate canonically at
`b - 1`: the truncation map is a quasi-isomorphism since `L` has no cohomology below `b`, the
terms above `b - 1` are those of `L`, and the term in degree `b - 1` maps injectively into `Lᵇ`
by the differential (`CochainComplex.mono_d_truncGE`), so it is flat by
`CochainComplex.ULiftInt.flat_of_mono`. -/
theorem exists_flat_isStrictlyGE_iso (K : DerivedCategory (ModuleCat.{w} (ULift.{w} ℤ))) (b : ℤ)
    [K.IsGE b] :
    ∃ P : CochainComplex (ModuleCat.{w} (ULift.{w} ℤ)) ℤ, P.IsStrictlyGE (b - 1) ∧
      (∀ q, Module.Flat (ULift.{w} ℤ) (P.X q)) ∧ Nonempty (DerivedCategory.Q.obj P ≅ K) := by
  let G := DerivedCategory.Q.objPreimage K
  let eG : DerivedCategory.Q.obj G ≅ K := DerivedCategory.Q.objObjPreimageIso K
  obtain ⟨L, f, -, hflat, hf, -⟩ := CochainComplex.KFlat.exists_kFlat_resolution.{w, w} G
  have : IsIso (DerivedCategory.Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ f).2 hf
  let eL : DerivedCategory.Q.obj L ≅ K := asIso (DerivedCategory.Q.map f) ≪≫ eG
  have hLb : L.IsGE b := (DerivedCategory.isGE_Q_obj_iff L b).1
    (DerivedCategory.TStructure.t.isGE_of_iso eL.symm b)
  have hLb' : L.IsGE (b - 1 + 1) := by rw [sub_add_cancel]; exact hLb
  have : L.IsGE (b - 1) := L.isGE_of_ge (b - 1) b (by omega)
  have : IsIso (DerivedCategory.Q.map (L.πTruncGE (b - 1))) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
  refine ⟨L.truncGE (b - 1), inferInstance, fun q => ?_,
    ⟨(asIso (DerivedCategory.Q.map (L.πTruncGE (b - 1)))).symm ≪≫ eL⟩⟩
  rcases lt_trichotomy q (b - 1) with hq | rfl | hq
  · have hz := (L.truncGE (b - 1)).isZero_of_isStrictlyGE (b - 1) q hq
    have : Subsingleton ((L.truncGE (b - 1)).X q) := ModuleCat.subsingleton_of_isZero hz
    infer_instance
  · have := hflat b
    have : Mono ((L.truncGE (b - 1)).d (b - 1) (b - 1 + 1)) := CochainComplex.mono_d_truncGE L _
    have : Module.Flat (ULift.{w} ℤ) ((L.truncGE (b - 1)).X (b - 1 + 1)) :=
      Module.Flat.of_linearEquiv (L.truncGEXIso (b - 1) (b - 1 + 1)).toLinearEquiv
    exact flat_of_mono ((L.truncGE (b - 1)).d (b - 1) (b - 1 + 1))
  · have := hflat q
    exact Module.Flat.of_linearEquiv (L.truncGEXIso (b - 1) q hq).toLinearEquiv

end CochainComplex.ULiftInt

end
