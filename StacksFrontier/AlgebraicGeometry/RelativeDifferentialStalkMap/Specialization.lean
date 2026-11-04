module

public import StacksFrontier.AlgebraicGeometry.RelativeDifferentialStalkMap.Scheme
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.ExteriorPowerStalkSpecialization

/-!
# Comparing the stalks of the relative differentials along a specialization

Let `q : X ⟶ S` be a morphism of schemes and let `y ⤳ x` be a specialization of points of `X`.
The stalk of `Ω_{X/S}` at a point is the module of Kähler differentials of the stalk map of `q`
there (`Stacks.RelativeDifferentialStalkMap.relativeDifferentialsStalkKaehlerEquiv`, Tag 01V0 at
a point), at `x` as `Ω[𝒪_{X,x}⁄𝒪_{S,q x}]` and at `y` as `Ω[𝒪_{X,y}⁄𝒪_{S,q y}]`. Comparing
those two identifications along `y ⤳ x` is an identity about the square

```
(Ω_{X/S})_x  ──────────────▸  (Ω_{X/S})_y
     │                             │
     ▾                             ▾
Ω[𝒪_{X,x}⁄𝒪_{S,q x}] ──▸ Ω[𝒪_{X,y}⁄𝒪_{S,q y}]
```

whose bottom edge is `KaehlerDifferential.map` of the commuting square of local rings

```
𝒪_{X,x} ──▸ 𝒪_{X,y}
   ▴            ▴
   │            │
𝒪_{S,q x} ─▸ 𝒪_{S,q y}
```

that the comparison of stalks of `q` supplies
(`AlgebraicGeometry.Scheme.Hom.stalkSpecializes_stalkMap`). That identity is proved here.

## Main definitions

* `Stacks.RelativeDifferentialStalkMap.stalkMapAlgebra`,
  `Stacks.RelativeDifferentialStalkMap.stalkSpecializesAlgebra` and
  `Stacks.RelativeDifferentialStalkMap.baseStalkSpecializesAlgebra`: the three sides of that
  square of local rings, as algebra structures.
* `Stacks.RelativeDifferentialStalkMap.relativeDifferentialsStalkKaehlerEquivₗ`:
  `relativeDifferentialsStalkKaehlerEquiv` restated over
  `AlgebraicGeometry.Scheme.Modules.presheaf` and `X.presheaf`, the spelling
  `Stacks.ModuleStalkSpecialization` uses; see the implementation notes.

## Main results

* `Stacks.RelativeDifferentialStalkMap.isScalarTower_stalkMap_stalkSpecializes`,
  `Stacks.RelativeDifferentialStalkMap.isScalarTower_baseStalkSpecializes` and
  `Stacks.RelativeDifferentialStalkMap.smulCommClass_stalkMap_stalkSpecializes`: the three
  compatibilities of that square which `KaehlerDifferential.map` asks for. The second is the
  commuting square itself; the other two are formal.
* `Stacks.RelativeDifferentialStalkMap.relativeDifferentialsStalkKaehlerEquivₗ_germ_d`: the
  identification carries the germ of the universal relative differential of a section to the
  universal differential of its germ, with the neighbourhood of `x` given as an open set rather
  than as an index of the diagram of neighbourhoods.
* `Stacks.RelativeDifferentialStalkMap.relativeDifferentialsStalkKaehlerEquivₗ_stalkSpecializes`:
  **the square above commutes.**

## Implementation notes

As in `StacksFrontier/AlgebraicGeometry/Scheme/Points/ExteriorPowerStalkSpecialization.lean`, the
obstruction to even stating the square is that the two sides are written in different spellings
of a stalk, and the fix is to retype one of them once.
`Stacks.RelativeDifferentialStalkMap.relativeDifferentialsStalkKaehlerEquiv` is stated over
`TopCat.Presheaf.stalk (Scheme.Hom.relativeDifferentials q).val.presheaf x` with scalars
`ToType (X.sheaf.presheaf.stalk x)`, while `Stacks.ModuleStalkSpecialization.stalkSpecializesₗ`
is stated over `(Scheme.Hom.relativeDifferentials q).presheaf.stalk x` with scalars
`X.presheaf.stalk x`. The two are definitionally equal and not syntactically equal, and instance
search will not bridge them: `letI := algebraStalkMap q x` records an `Algebra` whose target is
the `X.sheaf.presheaf` spelling, and a goal asking for the `X.presheaf` one is not closed by it.
So `stalkMapAlgebra` is `algebraStalkMap` retyped, and
`relativeDifferentialsStalkKaehlerEquivₗ` is `relativeDifferentialsStalkKaehlerEquiv` retyped
over it; nothing else is new in either.

The proof of the square is one application of `LinearMap.ext_on` at
`KaehlerDifferential.span_range_derivation` — the differentials `d a` of elements of `𝒪_{X,x}`
span `Ω[𝒪_{X,x}⁄𝒪_{S,q x}]` — followed by `_germ_d` at `x` and at `y` with
`Stacks.ModuleStalkSpecialization.stalkSpecializesₗ_germ` in between on one side and
`KaehlerDifferential.map_D` with
`Stacks.ModuleStalkSpecialization.ringGerm_stalkSpecializes_apply` on the other. The `show`
steps are written with `simp only` over the `LinearMap` coercions instead, because a `show`
that mentions the composite of the three maps exhausts the recursion depth.

## References

* [Stacks Project, Tag 01V0](https://stacks.math.columbia.edu/tag/01V0)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.ModuleStalkSpecialization
open scoped KaehlerDifferential


universe u

namespace Stacks.RelativeDifferentialStalkMap

variable {X S : Scheme.{u}}

/-! ### The square of local rings -/

/-- **`𝒪_{X,x}` as an algebra over `𝒪_{S,q x}`**, in the `X.presheaf` spelling. This is
`Stacks.RelativeDifferentialStalkMap.algebraStalkMap` and nothing else; see the implementation
notes for why the spelling has to be fixed. -/
noncomputable abbrev stalkMapAlgebra (q : X ⟶ S) (x : X) :
    Algebra (ToType (S.presheaf.stalk (q.base x))) (ToType (X.presheaf.stalk x)) :=
  (q.stalkMap x).hom.toAlgebra

/-- **`𝒪_{X,y}` as an algebra over `𝒪_{X,x}`** for a specialization `y ⤳ x`, through the
comparison of local rings. -/
noncomputable abbrev stalkSpecializesAlgebra (X : Scheme.{u}) {x y : X} (h : y ⤳ x) :
    Algebra (ToType (X.presheaf.stalk x)) (ToType (X.presheaf.stalk y)) :=
  (X.presheaf.stalkSpecializes h).hom.toAlgebra

/-- **`𝒪_{X,y}` as an algebra over `𝒪_{S,q x}`**, through `𝒪_{X,x}`. This is the diagonal of the
square of local rings; `isScalarTower_baseStalkSpecializes` says it is also the composite through
`𝒪_{S,q y}`. -/
noncomputable abbrev baseStalkSpecializesAlgebra (q : X ⟶ S) {x y : X} (h : y ⤳ x) :
    Algebra (ToType (S.presheaf.stalk (q.base x))) (ToType (X.presheaf.stalk y)) :=
  ((X.presheaf.stalkSpecializes h).hom.comp (q.stalkMap x).hom).toAlgebra

/-- **`𝒪_{S,q y}` as an algebra over `𝒪_{S,q x}`**, through the comparison of local rings of `S`
at the images of `y` and `x`. -/
noncomputable abbrev baseStalkSpecializesBaseAlgebra (q : X ⟶ S) {x y : X} (h : y ⤳ x) :
    Algebra (ToType (S.presheaf.stalk (q.base x))) (ToType (S.presheaf.stalk (q.base y))) :=
  (S.presheaf.stalkSpecializes (q.base.hom.map_specializes h)).hom.toAlgebra

/-- The scalar tower `𝒪_{S,q x} → 𝒪_{X,x} → 𝒪_{X,y}`: the diagonal of the square is by
definition the composite through `𝒪_{X,x}`. -/
theorem isScalarTower_stalkMap_stalkSpecializes (q : X ⟶ S) {x y : X} (h : y ⤳ x) :
    letI := stalkMapAlgebra q x
    letI := stalkSpecializesAlgebra X h
    letI := baseStalkSpecializesAlgebra q h
    IsScalarTower (ToType (S.presheaf.stalk (q.base x))) (ToType (X.presheaf.stalk x))
      (ToType (X.presheaf.stalk y)) :=
  let := stalkMapAlgebra q x
  let := stalkSpecializesAlgebra X h
  let := baseStalkSpecializesAlgebra q h
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

/-- **The square of local rings commutes**: the scalar tower `𝒪_{S,q x} → 𝒪_{S,q y} → 𝒪_{X,y}`
agrees with the diagonal. This is `AlgebraicGeometry.Scheme.Hom.stalkSpecializes_stalkMap` read
as a scalar tower, and is the only non-formal input the square needs. -/
theorem isScalarTower_baseStalkSpecializes (q : X ⟶ S) {x y : X} (h : y ⤳ x) :
    letI := baseStalkSpecializesBaseAlgebra q h
    letI := stalkMapAlgebra q y
    letI := baseStalkSpecializesAlgebra q h
    IsScalarTower (ToType (S.presheaf.stalk (q.base x))) (ToType (S.presheaf.stalk (q.base y)))
      (ToType (X.presheaf.stalk y)) :=
  let := baseStalkSpecializesBaseAlgebra q h
  let := stalkMapAlgebra q y
  let := baseStalkSpecializesAlgebra q h
  IsScalarTower.of_algebraMap_eq fun z ↦
    (Scheme.Hom.stalkSpecializes_stalkMap_apply q y x h z).symm

/-- The actions of `𝒪_{S,q y}` and of `𝒪_{X,x}` on `𝒪_{X,y}` commute: both are multiplication by
the image of a scalar in the commutative ring `𝒪_{X,y}`. This is what gives
`Ω[𝒪_{X,y}⁄𝒪_{S,q y}]` its `𝒪_{X,x}`-module structure. -/
theorem smulCommClass_stalkMap_stalkSpecializes (q : X ⟶ S) {x y : X} (h : y ⤳ x) :
    letI := stalkMapAlgebra q y
    letI := stalkSpecializesAlgebra X h
    SMulCommClass (ToType (S.presheaf.stalk (q.base y))) (ToType (X.presheaf.stalk x))
      (ToType (X.presheaf.stalk y)) :=
  let := stalkMapAlgebra q y
  let := stalkSpecializesAlgebra X h
  ⟨fun a b z ↦ by
    simp only [Algebra.smul_def]
    rw [← mul_assoc, ← mul_assoc, mul_comm (algebraMap _ _ a)]⟩

/-! ### The identification of the stalk, in one spelling -/

/-- **The stalk of `Ω_{X/S}` at `x` is `Ω[𝒪_{X,x}⁄𝒪_{S,q x}]`**, restated over
`AlgebraicGeometry.Scheme.Modules.presheaf` and `X.presheaf` with the module structure of
`Stacks.ModuleStalkSpecialization.stalkModule`. This is
`Stacks.RelativeDifferentialStalkMap.relativeDifferentialsStalkKaehlerEquiv` and nothing else;
what the restatement buys is that the comparison maps along a specialization can be composed
with it. -/
noncomputable def relativeDifferentialsStalkKaehlerEquivₗ (q : X ⟶ S) (x : X)
    [DecidableEq (OrderDual (TopologicalSpace.OpenNhds x))] :
    letI := stalkMapAlgebra q x
    letI := stalkModule (Scheme.Hom.relativeDifferentials q) x
    ((Scheme.Hom.relativeDifferentials q).presheaf.stalk x) ≃ₗ[X.presheaf.stalk x]
      Ω[(ToType (X.presheaf.stalk x))⁄(ToType (S.presheaf.stalk (q.base x)))] :=
  relativeDifferentialsStalkKaehlerEquiv q x

/-- `Stacks.RelativeDifferentialStalkMap.relativeDifferentialsStalkKaehlerEquiv_germ_d` in the
spelling of `relativeDifferentialsStalkKaehlerEquivₗ`, with the neighbourhood of `x` given as an
open set containing `x` rather than as an index of the diagram of neighbourhoods. -/
theorem relativeDifferentialsStalkKaehlerEquivₗ_germ_d (q : X ⟶ S) (x : X)
    [DecidableEq (OrderDual (TopologicalSpace.OpenNhds x))]
    (U : X.Opens) (hx : x ∈ U) (a : Γ(X, U)) :
    letI := stalkMapAlgebra q x
    letI := stalkModule (Scheme.Hom.relativeDifferentials q) x
    relativeDifferentialsStalkKaehlerEquivₗ q x
        ((Scheme.Hom.relativeDifferentials q).presheaf.germ U x hx
          ((Scheme.Hom.universalRelativeDerivation q).d a)) =
      KaehlerDifferential.D (ToType (S.presheaf.stalk (q.base x)))
        (ToType (X.presheaf.stalk x)) (X.presheaf.germ U x hx a) :=
  relativeDifferentialsStalkKaehlerEquiv_germ_d q x
    (OrderDual.toDual (⟨U, hx⟩ : TopologicalSpace.OpenNhds x)) a

/-! ### The square -/

/-- **Comparing the stalks of `Ω_{X/S}` along a specialization `y ⤳ x`.** Under the
identifications of Tag 01V0 at the two points, the comparison `(Ω_{X/S})_x → (Ω_{X/S})_y` of
stalks is `KaehlerDifferential.map` of the commuting square of local rings that `q` supplies.

Both sides are `𝒪_{X,x}`-linear maps out of `Ω[𝒪_{X,x}⁄𝒪_{S,q x}]`, which is spanned by the
differentials `d a` of elements of `𝒪_{X,x}`; such an element is the germ of a section over a
neighbourhood `U` of `x`, which is a neighbourhood of `y` as well, and on `d` of such a germ both
sides are the universal differential of the germ at `y` of that same section. -/
theorem relativeDifferentialsStalkKaehlerEquivₗ_stalkSpecializes (q : X ⟶ S) {x y : X}
    (h : y ⤳ x) [DecidableEq (OrderDual (TopologicalSpace.OpenNhds x))]
    [DecidableEq (OrderDual (TopologicalSpace.OpenNhds y))] :
    letI := stalkMapAlgebra q x
    letI := stalkMapAlgebra q y
    letI := baseStalkSpecializesBaseAlgebra q h
    letI := stalkSpecializesAlgebra X h
    letI := baseStalkSpecializesAlgebra q h
    haveI := isScalarTower_stalkMap_stalkSpecializes q h
    haveI := isScalarTower_baseStalkSpecializes q h
    haveI := smulCommClass_stalkMap_stalkSpecializes q h
    letI := stalkModule (Scheme.Hom.relativeDifferentials q) x
    letI := stalkModule (Scheme.Hom.relativeDifferentials q) y
    letI := stalkSpecializesModule (Scheme.Hom.relativeDifferentials q) h
    haveI := isScalarTower_stalkSpecializes_stalk (Scheme.Hom.relativeDifferentials q) h
    (relativeDifferentialsStalkKaehlerEquivₗ q y).toLinearMap.restrictScalars
            (X.presheaf.stalk x) ∘ₗ
          (stalkSpecializesₗ (Scheme.Hom.relativeDifferentials q) h ∘ₗ
            (relativeDifferentialsStalkKaehlerEquivₗ q x).symm.toLinearMap) =
      KaehlerDifferential.map (ToType (S.presheaf.stalk (q.base x)))
        (ToType (S.presheaf.stalk (q.base y))) (ToType (X.presheaf.stalk x))
        (ToType (X.presheaf.stalk y)) := by
  let := stalkMapAlgebra q x
  let := stalkMapAlgebra q y
  let := baseStalkSpecializesBaseAlgebra q h
  let := stalkSpecializesAlgebra X h
  let := baseStalkSpecializesAlgebra q h
  have := isScalarTower_stalkMap_stalkSpecializes q h
  have := isScalarTower_baseStalkSpecializes q h
  have := smulCommClass_stalkMap_stalkSpecializes q h
  let := stalkModule (Scheme.Hom.relativeDifferentials q) x
  let := stalkModule (Scheme.Hom.relativeDifferentials q) y
  let := stalkSpecializesModule (Scheme.Hom.relativeDifferentials q) h
  have := isScalarTower_stalkSpecializes_stalk (Scheme.Hom.relativeDifferentials q) h
  refine LinearMap.ext_on (KaehlerDifferential.span_range_derivation
    (R := ToType (S.presheaf.stalk (q.base x)))
    (S := ToType (X.presheaf.stalk x))) ?_
  rintro - ⟨a, rfl⟩
  obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf a
  have hx := relativeDifferentialsStalkKaehlerEquivₗ_germ_d q x U hxU s
  have hy := relativeDifferentialsStalkKaehlerEquivₗ_germ_d q y U (h.mem_open U.isOpen hxU) s
  have halg : algebraMap (ToType (X.presheaf.stalk x)) (ToType (X.presheaf.stalk y))
      (X.presheaf.germ U x hxU s) = X.presheaf.germ U y (h.mem_open U.isOpen hxU) s :=
    ringGerm_stalkSpecializes_apply hxU h s
  simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply,
    LinearEquiv.coe_coe, KaehlerDifferential.map_D, halg]
  rw [← hx, LinearEquiv.symm_apply_apply]
  exact (congrArg (relativeDifferentialsStalkKaehlerEquivₗ q y)
    (stalkSpecializesₗ_germ (Scheme.Hom.relativeDifferentials q) hxU h _)).trans hy

end Stacks.RelativeDifferentialStalkMap

end
