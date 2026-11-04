module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerBridge
public import StacksFrontier.AlgebraicGeometry.AmpleProjectiveImmersion.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleTensorPower.Basic
public import StacksFrontier.AlgebraicGeometry.NonvanishingSpelling.Basic
public import StacksFrontier.AlgebraicGeometry.PowerFamilyBridge.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmple.TensorPower

/-!
# The two families of tensor powers on a scheme, and Stacks Tag 01VS

On a scheme `X`, the two constructions of the integer tensor powers of an invertible sheaf of
modules, `Stacks.AmpleProjectiveImmersion.tensorPowerModule` (Stacks Tag 01CU) and
`Stacks.Ample.tensorPowModule`, are isomorphic in every integer degree. Consequently ampleness,
and the conditions `Stacks.AmpleProjectiveImmersion.EventualImmersionTwist` and
`Stacks.AmpleProjectiveImmersion.ImmersionTwistGap` of Stacks Tag 01VS, do not depend on the family
used, and the two forms of Tag 01VS, one for each family, follow from the same hypothesis.

## Main definitions

* `Stacks.PowerFamilyBridge.tensorPowerModuleIso`: the comparison of the two families on a
  scheme, in every integer degree.
* `Stacks.PowerFamilyBridge.invertibleTensorPowerModuleIso`: the same comparison, from
  `AlgebraicGeometry.Scheme.Modules.tensorPowerModules`.

## Main results

* `Stacks.PowerFamilyBridge.isAmpleForPowers_tensorPowerModule_iff`: Stacks Tag 01PS over
  `Stacks.AmpleProjectiveImmersion.tensorPowerModule` is `Stacks.Ample.IsAmple`.
* `Stacks.PowerFamilyBridge.hasImmersionTwist_congr`,
  `Stacks.PowerFamilyBridge.eventualImmersionTwist_congr`,
  `Stacks.PowerFamilyBridge.immersionTwistGap_iff`: Tag 01VS's per-degree conclusion, its eventual
  form, and `ImmersionTwistGap` depend on the family only through the isomorphism classes of its
  nonnegative members.
* `Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple`: the two ampleness predicates of Stacks
  Tag 01PS, `AlgebraicGeometry.Scheme.Modules.IsAmple` and `Stacks.Ample.IsAmple`, are the same
  condition.
* `Stacks.PowerFamilyBridge.exists_immersion_tensorPowModule_of_isAmple` and
  `Stacks.PowerFamilyBridge.exists_immersion_tensorPowerModule_of_isAmple`: each of the two forms
  of Tag 01VS from the other form's hypothesis.

## References

* [Stacks Project, Tag 01VS](https://stacks.math.columbia.edu/tag/01VS)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AmpleProjectiveImmersion

universe u

namespace Stacks.PowerFamilyBridge

/-! ### The comparison on a scheme -/

/-- **The two constructions of the integer tensor powers agree on a scheme, in every integer
degree.** On the left `Stacks.AmpleProjectiveImmersion.tensorPowerModule`, which is Stacks Tag
01CU's `Stacks.SheafOfModules.TensorPower.tensorPower`; on the right
`Stacks.Ample.tensorPowModule`, which is `AlgebraicGeometry.SheafOfModules.tensorPow`.

This is `Stacks.PowerFamilyBridge.tensorPowerIsoTensorPow` at `X.presheaf`. -/
def tensorPowerModuleIso (X : Scheme.{u}) (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    (n : ℤ) : tensorPowerModule X L n ≅ Stacks.Ample.tensorPowModule X L n :=
  tensorPowerIsoTensorPow X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L n

/-- **Stacks Tag 01PS over Tag 01CU's family of tensor powers.** `Stacks.Ample.IsAmple` is
`Stacks.Ample.IsAmpleForPowers` at `Stacks.Ample.tensorPowModule`; the same predicate at
`Stacks.AmpleProjectiveImmersion.tensorPowerModule` is the same condition. -/
theorem isAmpleForPowers_tensorPowerModule_iff (X : Scheme.{u}) (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] :
    Stacks.Ample.IsAmpleForPowers X (tensorPowerModule X L) ↔ Stacks.Ample.IsAmple X L :=
  Stacks.RelativeVeryAmple.isAmpleForPowers_congr_nat fun n => tensorPowerModuleIso X L (n : ℤ)

/-! ### Tag 01VS depends on its family only through isomorphism classes -/

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Tag 01VS's per-degree conclusion is an invariant of the isomorphism class of the module. -/
theorem hasImmersionTwist_congr {M M' : X.Modules} (e : M ≅ M') :
    HasImmersionTwist f M ↔ HasImmersionTwist f M' := by
  constructor
  · rintro ⟨n, g, hi, ⟨d⟩⟩
    exact ⟨n, g, hi, ⟨e.symm ≪≫ d⟩⟩
  · rintro ⟨n, g, hi, ⟨d⟩⟩
    exact ⟨n, g, hi, ⟨e ≪≫ d⟩⟩

/-- **Tag 01VS's eventual conclusion depends on the family only in the nonnegative degrees**: a
degreewise isomorphism in the degrees `d : ℕ` transfers
`Stacks.AmpleProjectiveImmersion.EventualImmersionTwist`. -/
theorem eventualImmersionTwist_congr {pow pow' : ℤ → X.Modules}
    (e : ∀ d : ℕ, pow (d : ℤ) ≅ pow' (d : ℤ)) :
    EventualImmersionTwist f pow ↔ EventualImmersionTwist f pow' := by
  have key : ∀ p q : ℤ → X.Modules, (∀ d : ℕ, p (d : ℤ) ≅ q (d : ℤ)) →
      EventualImmersionTwist f p → EventualImmersionTwist f q := by
    rintro p q g ⟨d₀, hd₀, hd⟩
    exact ⟨d₀, hd₀, fun d hdd => (hasImmersionTwist_congr f (g d)).mp (hd d hdd)⟩
  exact ⟨key pow pow' e, key pow' pow fun d => (e d).symm⟩

/-- **`ImmersionTwistGap` is the same condition for both power families**: each side is
`Stacks.AmpleProjectiveImmersion.ImmersionTwistGap` for one of the two constructions of the
tensor powers. -/
theorem immersionTwistGap_iff (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] :
    ImmersionTwistGap f L (tensorPowerModule X L) ↔
      ImmersionTwistGap f L (Stacks.Ample.tensorPowModule X L) :=
  forall_congr' fun _ => forall_congr' fun _ =>
    eventualImmersionTwist_congr f fun d => tensorPowerModuleIso X L (d : ℤ)

/-! ### The two statements of Tag 01VS are interderivable -/

/-- **Stacks Tag 01VS for `Stacks.Ample.tensorPowModule`, from the gap for Tag 01CU's family.**
The hypothesis is the one
`Stacks.AmpleProjectiveImmersion.exists_immersion_projectiveSpaceOver_of_isAmple` takes, stated
for `Stacks.AmpleProjectiveImmersion.tensorPowerModule`; the conclusion is the one its primed
variant gives, stated for `Stacks.Ample.tensorPowModule`. -/
theorem exists_immersion_tensorPowModule_of_isAmple (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (hL : Stacks.Ample.IsAmple X L)
    [hf : LocallyOfFiniteType f] (h : ImmersionTwistGap f L (tensorPowerModule X L)) :
    ∃ d₀ : ℕ, 1 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d →
      ∃ (n : ℕ) (i : X ⟶ projectiveSpaceOver n S),
        IsImmersion i ∧
        i ≫ pullback.fst (terminal.from S)
          (terminal.from (projectiveSpaceAtUniverse.{u} n)) = f ∧
        Nonempty (Stacks.Ample.tensorPowModule X L (d : ℤ) ≅
          (Scheme.Modules.pullback i).obj (projectiveSpaceTwistingSheaf n S)) :=
  exists_immersion_projectiveSpaceOver_of_isAmple' f L hL ((immersionTwistGap_iff f L).mp h)

/-- **Stacks Tag 01VS for Tag 01CU's tensor powers, from the gap for
`Stacks.Ample.tensorPowModule`.** The converse of
`Stacks.PowerFamilyBridge.exists_immersion_tensorPowModule_of_isAmple`. -/
theorem exists_immersion_tensorPowerModule_of_isAmple (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (hL : Stacks.Ample.IsAmple X L)
    [hf : LocallyOfFiniteType f]
    (h : ImmersionTwistGap f L (Stacks.Ample.tensorPowModule X L)) :
    ∃ d₀ : ℕ, 1 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d →
      ∃ (n : ℕ) (i : X ⟶ projectiveSpaceOver n S),
        IsImmersion i ∧
        i ≫ pullback.fst (terminal.from S)
          (terminal.from (projectiveSpaceAtUniverse.{u} n)) = f ∧
        Nonempty (tensorPowerModule X L (d : ℤ) ≅
          (Scheme.Modules.pullback i).obj (projectiveSpaceTwistingSheaf n S)) :=
  exists_immersion_projectiveSpaceOver_of_isAmple f L hL ((immersionTwistGap_iff f L).mpr h)

/-! ### The two ampleness predicates of Stacks Tag 01PS are the same condition -/

section Compare


variable (X : Scheme.{u}) (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property L]

/-- **The comparison of the tensor powers, in the third of the library's three spellings.**
`Stacks.SheafOfModules.Invertible.tensorPower`, which
`AlgebraicGeometry.Scheme.Modules.IsAmple` is stated over, against `Stacks.Ample.tensorPowModule`,
which `Stacks.Ample.IsAmple` is stated over. The first is
`Stacks.SheafOfModules.TensorPower.tensorPower` on the nose, so this is
`Stacks.PowerFamilyBridge.tensorPowerModuleIso` composed with that identification. -/
def invertibleTensorPowerModuleIso (n : ℤ) :
    AlgebraicGeometry.Scheme.Modules.tensorPowerModules L n
      ≅ Stacks.Ample.tensorPowModule X L n :=
  eqToIso (C := X.Modules) (Stacks.SheafOfModules.Invertible.tensorPower_eq_tensorPower
      X.toRingedSpace.presheaf (structureSheafRing X.toRingedSpace).property L n) ≪≫
    tensorPowerModuleIso X L n

/-- **Ampleness over `Stacks.Ample.tensorPowModule` implies ampleness over
`Stacks.SheafOfModules.Invertible.tensorPower`.** -/
theorem modulesIsAmple_of_isAmple (h : Stacks.Ample.IsAmple X L) :
    AlgebraicGeometry.Scheme.Modules.IsAmple X L := by
  refine ⟨h.1, fun x => ?_⟩
  obtain ⟨n, hn, s, U, hU, hxU, hUaff⟩ := h.2 x
  set M := AlgebraicGeometry.Scheme.Modules.tensorPowerModules L (n : ℤ) with hM
  let e : M ≅ Stacks.Ample.tensorPowModule X L (n : ℤ) :=
    invertibleTensorPowerModuleIso X L (n : ℤ)
  refine ⟨n, hn, (Stacks.NonvanishingSpelling.sectionsEquiv X M).symm (e.symm.hom.app ⊤ s), ?_, ?_⟩
  all_goals
    have key : Stacks.SheafOfModules.nonvanishingOpen (X := X.toRingedSpace) M
          ((Stacks.NonvanishingSpelling.sectionsEquiv X M).symm (e.symm.hom.app ⊤ s)) = U :=
      TopologicalSpace.Opens.ext
        (((Stacks.NonvanishingSpelling.stalkNonvanishingLocus_symm_eq X M _).trans
          (Stacks.Ample.nonvanishingLocus_congr e.symm s)).trans hU.symm)
  · exact key.ge hxU
  · exact key ▸ hUaff

/-- **Ampleness over `Stacks.SheafOfModules.Invertible.tensorPower` implies ampleness over
`Stacks.Ample.tensorPowModule`.** -/
theorem isAmple_of_modulesIsAmple (h : AlgebraicGeometry.Scheme.Modules.IsAmple X L) :
    Stacks.Ample.IsAmple X L := by
  refine ⟨h.1, fun x => ?_⟩
  obtain ⟨n, hn, t, hxt, haff⟩ := h.2 x
  set M := AlgebraicGeometry.Scheme.Modules.tensorPowerModules L (n : ℤ) with hM
  let e : M ≅ Stacks.Ample.tensorPowModule X L (n : ℤ) :=
    invertibleTensorPowerModuleIso X L (n : ℤ)
  refine ⟨n, hn, e.hom.app ⊤ (Stacks.NonvanishingSpelling.sectionsEquiv X M t),
    Stacks.SheafOfModules.nonvanishingOpen (X := X.toRingedSpace) M t, ?_, hxt, haff⟩
  exact (Stacks.NonvanishingSpelling.stalkNonvanishingLocus_eq X M t).trans
    (Stacks.Ample.nonvanishingLocus_congr e _).symm

/-- **Stacks Tag 01PS: the library's two ampleness predicates define the same class of modules.**
`AlgebraicGeometry.Scheme.Modules.IsAmple` quantifies over the sections of
`Stacks.SheafOfModules.Invertible.tensorPower` and bundles the nonvanishing locus by Stacks Tag
01CY; `Stacks.Ample.IsAmple` quantifies over the global sections of
`Stacks.Ample.tensorPowModule` and produces the affine open existentially. -/
theorem modulesIsAmple_iff_isAmple :
    AlgebraicGeometry.Scheme.Modules.IsAmple X L ↔ Stacks.Ample.IsAmple X L :=
  ⟨isAmple_of_modulesIsAmple X L, modulesIsAmple_of_isAmple X L⟩

end Compare

end Stacks.PowerFamilyBridge

end
