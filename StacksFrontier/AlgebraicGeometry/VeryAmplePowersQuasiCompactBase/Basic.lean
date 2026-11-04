module

public import StacksFrontier.AlgebraicGeometry.AmplePowerImmersionCover.Basic
public import StacksFrontier.AlgebraicGeometry.QuasiProjectiveCompactification.UniformFamily
public import StacksFrontier.AlgebraicGeometry.VeryAmpleGlue.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Relative ampleness and very ample powers over a quasi-compact base

For a morphism of schemes `f : X ⟶ S` of finite type with `S` quasi-compact and `L` an invertible
`𝒪_X`-module the following are equivalent:

1. `L` is `f`-relatively ample,
2. `L^{⊗ d}` is `f`-relatively very ample for some `d ≥ 1`, and
3. `L^{⊗ d}` is `f`-relatively very ample for every sufficiently large `d`.

Condition (1) is `Stacks.RelativeAmple.IsRelativelyAmple`, and relative very ampleness is
`Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple`, with respect to the projective bundle `𝐏(E)` of
a quasi-coherent `𝒪_S`-module and its degree-one twist `𝒪_{𝐏(E)}(1)`. Conditions (2) and (3) are
stated for the tensor powers `Stacks.Ample.tensorPowModule`.

## Main definitions

* `Stacks.VeryAmplePowersQuasiCompactBase.ExistsVeryAmplePower`: some positive tensor power of
  `L` is very ample relative to `f`.
* `Stacks.VeryAmplePowersQuasiCompactBase.EventuallyVeryAmplePower`: every sufficiently high
  tensor power of `L` is very ample relative to `f`.

## Main results

* `Stacks.VeryAmplePowersQuasiCompactBase.existsVeryAmplePower_of_eventuallyVeryAmplePower`:
  (3) ⟹ (2).
* `Stacks.VeryAmplePowersQuasiCompactBase.isRelativelyAmple_of_existsVeryAmplePower`:
  (2) ⟹ (1), for `f` quasi-compact.
* `Stacks.VeryAmplePowersQuasiCompactBase.isRelativelyAmple_of_eventuallyVeryAmplePower`:
  (3) ⟹ (1), for `f` quasi-compact.
* `Stacks.VeryAmplePowersQuasiCompactBase.eventuallyVeryAmplePower_of_isRelativelyAmple`:
  (1) ⟹ (3), for `f` locally of finite type and `S` quasi-compact.
* `Stacks.VeryAmplePowersQuasiCompactBase.tfae`: the three conditions are equivalent.

## Implementation notes

Degrees are natural numbers: conditions (2) and (3) take `d : ℕ` with `1 ≤ d` and the tensor
power at `(d : ℤ)`. "For every sufficiently large `d`" is `∃ d₀, 1 ≤ d₀ ∧ ∀ d ≥ d₀`, with the
bound positive. Quasi-compactness of `S` is `CompactSpace S`, and finite type is
`LocallyOfFiniteType` together with `QuasiCompact`.

## References

* [Stacks Project, Tag 01VU](https://stacks.math.columbia.edu/tag/01VU)
* [Stacks Project, Tag 01VH](https://stacks.math.columbia.edu/tag/01VH)
* [Stacks Project, Tag 01VM](https://stacks.math.columbia.edu/tag/01VM)
* [Stacks Project, Tag 01VN](https://stacks.math.columbia.edu/tag/01VN)
* [Stacks Project, Tag 01VR](https://stacks.math.columbia.edu/tag/01VR)
* [Stacks Project, Tag 01VS](https://stacks.math.columbia.edu/tag/01VS)
* [Stacks Project, Tag 01VT](https://stacks.math.columbia.edu/tag/01VT)
* [Stacks Project, Tag 01PT](https://stacks.math.columbia.edu/tag/01PT)
* [Stacks Project, Tag 0FVC](https://stacks.math.columbia.edu/tag/0FVC)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Ample
open Stacks.AmpleProjectiveImmersion

universe u

namespace Stacks.VeryAmplePowersQuasiCompactBase

variable {X S : Scheme.{u}}

/-! ### Conditions (2) and (3) -/

/-- Some positive tensor power of `L` is very ample relative to `f`. -/
def ExistsVeryAmplePower (f : X ⟶ S) (L : X.Modules) [IsInvertibleModule X L] : Prop :=
  ∃ d : ℕ, 1 ≤ d ∧
    Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple f (tensorPowModule X L (d : ℤ))

/-- Every sufficiently high tensor power of `L` is very ample relative to `f`. -/
def EventuallyVeryAmplePower (f : X ⟶ S) (L : X.Modules) [IsInvertibleModule X L] : Prop :=
  ∃ d₀ : ℕ, 1 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d →
    Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple f (tensorPowModule X L (d : ℤ))

/-! ### The implications that end in relative ampleness -/

/-- If every sufficiently high tensor power of `L` is very ample relative to `f`, then some
positive tensor power of `L` is very ample relative to `f`. -/
@[stacks 01VU "(3) implies (2)", ega "II 4.5.10" "(ii): e) implies e')"]
theorem existsVeryAmplePower_of_eventuallyVeryAmplePower (f : X ⟶ S) (L : X.Modules)
    [IsInvertibleModule X L] (h : EventuallyVeryAmplePower f L) : ExistsVeryAmplePower f L :=
  let ⟨d₀, hd₀, hd⟩ := h
  ⟨d₀, hd₀, hd d₀ le_rfl⟩

/-- If some positive tensor power of `L` is very ample relative to a quasi-compact `f`, then `L` is
ample relative to `f`. -/
@[stacks 01VU "(2) implies (1)", ega "II 4.5.10" "more general", ega "II 4.6.2" "more general"]
theorem isRelativelyAmple_of_existsVeryAmplePower (f : X ⟶ S) (L : X.Modules)
    [IsInvertibleModule X L] (hf : QuasiCompact f) (h : ExistsVeryAmplePower f L) :
    Stacks.RelativeAmple.IsRelativelyAmple f L := by
  obtain ⟨d, hd, hv⟩ := h
  exact Stacks.RelativeVeryAmple.isRelativelyAmple_of_isRelativelyAmple_tensorPowModule f L d hd
    (Stacks.RelativeAmple.isRelativelyAmple_of_isRelativelyVeryAmple f _ hf hv)

/-- If every sufficiently high tensor power of `L` is very ample relative to a quasi-compact `f`,
then `L` is ample relative to `f`. -/
@[stacks 01VU "(3) implies (1)", ega "II 4.5.10" "(ii): e) implies ample"]
theorem isRelativelyAmple_of_eventuallyVeryAmplePower (f : X ⟶ S) (L : X.Modules)
    [IsInvertibleModule X L] (hf : QuasiCompact f) (h : EventuallyVeryAmplePower f L) :
    Stacks.RelativeAmple.IsRelativelyAmple f L :=
  isRelativelyAmple_of_existsVeryAmplePower f L hf
    (existsVeryAmplePower_of_eventuallyVeryAmplePower f L h)

/-! ### (1) implies (3) -/

/-- Let `f : X ⟶ S` be locally of finite type with `S` quasi-compact and let `L` be ample
relative to `f`. Then `L^{⊗ d}` is very ample relative to `f` for every sufficiently large `d`. -/
@[stacks 01VU "(1) implies (3)",
  ega "II 4.5.10" "(ii): ample implies e)",
  ega "II 4.5.11" "The case L' = O_X",
  ega "II 4.6.11" "partial"]
theorem eventuallyVeryAmplePower_of_isRelativelyAmple (f : X ⟶ S)
    (L : X.Modules) [IsInvertibleModule X L] [CompactSpace S] [LocallyOfFiniteType f]
    (hL : Stacks.RelativeAmple.IsRelativelyAmple f L) :
    EventuallyVeryAmplePower f L := by
  classical
  have : QuasiCompact f := hL.1
  set 𝒰 := S.affineCover.finiteSubcover with h𝒰
  have hVaff : ∀ j : 𝒰.I₀, IsAffineOpen (𝒰.f j).opensRange := fun j =>
    isAffineOpen_opensRange _
  choose d₀ hd using fun j : 𝒰.I₀ =>
    Stacks.QuasiProjectiveCompactification.eventually_familyImmersionTwist
      (f ∣_ (𝒰.f j).opensRange) _ (hL.2 _ (hVaff j))
  refine ⟨max 1 (Finset.univ.sup d₀), le_max_left _ _, fun d hdd => ?_⟩
  have hd' := fun j : 𝒰.I₀ => hd j d
    (le_trans (le_trans (Finset.le_sup (Finset.mem_univ j)) (le_max_right _ _)) hdd)
  choose n s hs himm using hd'
  have : ∀ j : 𝒰.I₀, IsInvertibleModule (f ⁻¹ᵁ (𝒰.f j).opensRange).toScheme
      (tensorPowModule _
        ((modulePullback (f ⁻¹ᵁ (𝒰.f j).opensRange).ι.toLRSHom.toShHom).obj L) (d : ℤ)) :=
    fun j => Stacks.Ample.isInvertibleModule_tensorPowModule _ _ _
  exact Stacks.VeryAmpleGlue.isRelativelyVeryAmple_of_cover f (tensorPowModule X L (d : ℤ))
    (fun j => (𝒰.f j).opensRange) hVaff (Scheme.OpenCover.iSup_opensRange 𝒰) n
    (fun j => tensorPowModule _
      ((modulePullback (f ⁻¹ᵁ (𝒰.f j).opensRange).ι.toLRSHom.toShHom).obj L) (d : ℤ))
    s hs himm fun j =>
      (Stacks.QuasiProjectiveCompactification.nonempty_natTensorPow_pullback_iso L
        (f ⁻¹ᵁ (𝒰.f j).opensRange) d).some

/-! ### The equivalence -/

/-- For `f : X ⟶ S` of finite type with `S` quasi-compact and `L` an invertible `𝒪_X`-module, the
three conditions

1. `L` is `f`-relatively ample,
2. `L^{⊗ d}` is `f`-relatively very ample for some `d ≥ 1`, and
3. `L^{⊗ d}` is `f`-relatively very ample for every sufficiently large `d`

are equivalent. -/
@[stacks 01VU]
theorem tfae (f : X ⟶ S)
    (L : X.Modules) [IsInvertibleModule X L] [CompactSpace S] [LocallyOfFiniteType f]
    (hf : QuasiCompact f) :
    List.TFAE [Stacks.RelativeAmple.IsRelativelyAmple f L, ExistsVeryAmplePower f L,
      EventuallyVeryAmplePower f L] := by
  tfae_have 1 → 3 := eventuallyVeryAmplePower_of_isRelativelyAmple f L
  tfae_have 3 → 2 := existsVeryAmplePower_of_eventuallyVeryAmplePower f L
  tfae_have 2 → 1 := isRelativelyAmple_of_existsVeryAmplePower f L hf
  tfae_finish

end Stacks.VeryAmplePowersQuasiCompactBase

end
