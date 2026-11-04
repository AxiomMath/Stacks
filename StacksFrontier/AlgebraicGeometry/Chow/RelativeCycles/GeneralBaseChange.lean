module

public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.IsomorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.LocalizationSequence
public import StacksFrontier.AlgebraicGeometry.Chow.PerfectClosureCycles
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.BaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Restriction
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Fibre
public import StacksCore.Tactic.StacksAttribute

/-!
# Base change of a family of cycles along an arbitrary morphism of bases

Let `f : X ⟶ S` be locally of finite type, let `r ≥ 0`, let `α` be a family of `r`-cycles on the
fibres of `X/S` and let `g : S' ⟶ S` be an arbitrary morphism of schemes. Write `X' = X ×_S S'`
and `f' : X' ⟶ S'` for the second projection. For a point `t` of `S'` the fibre `X'_t` is
canonically the base change `X_{g t} ×_{κ(g t)} κ(t)` of the fibre of `f` over `g t` along the
extension `κ(t)/κ(g t)` of residue fields induced by `g`, so the member of `α` over `g t` may be
carried to an `r`-cycle on `X'_t` by the base-change map on cycle groups attached to a field
extension. The resulting family `g^*α` of `r`-cycles on the fibres of `X'/S'` is the base change
of `α`.

## Main definitions

* `Stacks.Chow.residueFieldBaseChangeSituation` — the flat base change of Chow situations
  attached to the residue field extension induced by `g` at a point of `S'`.
* `Stacks.Chow.fibreBaseChangeIso` — the canonical isomorphism
  `(X ×_S S')_t ≅ X_{g t} ×_{κ(g t)} κ(t)`.
* `Stacks.Chow.baseChangeFiberCycle` — the induced homomorphism `Z_r(X_{g t}) ⟶ Z_r(X'_t)` of
  fibrewise cycle groups.
* `Stacks.Chow.baseChangeFamilyHom` — the base change of families of cycles as a homomorphism of
  abelian groups.

## Main results

* `Stacks.Chow.isPullback_restrictedFiberMap_baseChange` — the square of fibres exhibiting
  `X'_t` as `X_{g t} ×_{κ(g t)} κ(t)` is a pullback square.
* `Stacks.Chow.baseChangeFamily_eq_baseChangeFiberCycle` — the base change `g^*α` of a family of
  cycles agrees with the fibrewise construction of this file: its member over `t` is the base
  change of the member of `α` over `g t` along the residue field extension `κ(t)/κ(g t)`.
* `Stacks.Chow.baseChangeFamily_apply_flatPullbackWeight` — the coefficient of `g^*α` on the
  fibre over `t` at a point `x` is the coefficient of `α` on the fibre over `g t` at the image of
  `x`, times the multiplicity with which `x` enters the inverse image of the reduced closure of
  that image, the multiplicity being read on `X_{g t} ×_{κ(g t)} κ(t)`.
* `Stacks.Chow.baseChangeFamily_zero`, `Stacks.Chow.baseChangeFamily_add`,
  `Stacks.Chow.baseChangeFamily_neg` — additivity of the base change.

## References

* [Stacks Project, Section 0H4N](https://stacks.math.columbia.edu/tag/0H4N)
* [Stacks Project, Section 0H4E](https://stacks.math.columbia.edu/tag/0H4E)
* [Stacks Project, Tag 0FVG](https://stacks.math.columbia.edu/tag/0FVG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The residue field extension induced at a point of the new base -/

/-- The flat base change of Chow situations attached to the extension `κ(t)/κ(g t)` of residue
fields induced by a morphism `g : S' ⟶ S` at a point `t` of `S'`: the two bases are the spectra
of the two residue fields with their vanishing dimension functions, and the dimension shift is
zero. -/
abbrev residueFieldBaseChangeSituation {S S' : Scheme.{u}} (g : S' ⟶ S) (t : S') :
    FlatBaseChangeSituation.{u} :=
  letI : Algebra (S.residueField (g t)) (S'.residueField t) :=
    (g.residueFieldMap t).hom.toAlgebra
  fieldExtensionBaseChangeSituation (S.residueField (g t)) (S'.residueField t)

/-- The base-change morphism of `Stacks.Chow.residueFieldBaseChangeSituation` is the spectrum of
the residue field map of `g` at `t`. -/
@[simp]
theorem residueFieldBaseChangeSituation_g {S S' : Scheme.{u}} (g : S' ⟶ S) (t : S') :
    (residueFieldBaseChangeSituation g t).g = Spec.map (g.residueFieldMap t) :=
  rfl

/-- The dimension shift of `Stacks.Chow.residueFieldBaseChangeSituation` vanishes: both residue
fields carry the zero dimension function. -/
@[simp]
theorem residueFieldBaseChangeSituation_c {S S' : Scheme.{u}} (g : S' ⟶ S) (t : S') :
    (residueFieldBaseChangeSituation g t).c = 0 :=
  rfl

/-! ### The fibre of a base change is a residue field base change of a fibre -/

/-- The fibre of the base change `X ×_S S' ⟶ S'` over a point `t` of `S'` is the base change of
the fibre of `f` over `g t` along the residue field extension `κ(t)/κ(g t)`: the square formed by
the canonical morphism of fibres, the two structure morphisms to the spectra of the residue
fields and the spectrum of the residue field map of `g` is a pullback square. -/
theorem isPullback_restrictedFiberMap_baseChange {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (t : S') :
    IsPullback
      (restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition t)
      ((pullback.snd f g).fiberToSpecResidueField t) (f.fiberToSpecResidueField (g t))
      (residueFieldBaseChangeSituation g t).g :=
  isPullback_fiberToSpecResidueField_of_isPullback (IsPullback.of_hasPullback f g) t

/-- The canonical isomorphism `(X ×_S S')_t ≅ X_{g t} ×_{κ(g t)} κ(t)` identifying the fibre of a
base change with the residue field base change of the fibre over the image point. -/
def fibreBaseChangeIso {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (t : S') :
    (pullback.snd f g).fiber t ≅
      pullback (f.fiberToSpecResidueField (g t)) (residueFieldBaseChangeSituation g t).g :=
  (isPullback_restrictedFiberMap_baseChange f g t).isoPullback

/-- Read through `Stacks.Chow.fibreBaseChangeIso`, the projection to the fibre over the image
point is the canonical morphism of fibres. -/
@[reassoc]
theorem fibreBaseChangeIso_hom_fst {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (t : S') :
    (fibreBaseChangeIso f g t).hom ≫
        pullback.fst (f.fiberToSpecResidueField (g t)) (residueFieldBaseChangeSituation g t).g =
      restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition t :=
  (isPullback_restrictedFiberMap_baseChange f g t).isoPullback_hom_fst

/-- `Stacks.Chow.fibreBaseChangeIso` is an isomorphism over the spectrum of the residue field at
`t`. -/
@[reassoc]
theorem fibreBaseChangeIso_hom_snd {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (t : S') :
    (fibreBaseChangeIso f g t).hom ≫
        pullback.snd (f.fiberToSpecResidueField (g t)) (residueFieldBaseChangeSituation g t).g =
      (pullback.snd f g).fiberToSpecResidueField t :=
  (isPullback_restrictedFiberMap_baseChange f g t).isoPullback_hom_snd

/-- On points, `Stacks.Chow.fibreBaseChangeIso` followed by the projection to the fibre over the
image point is the canonical morphism of fibres. -/
theorem fst_fibreBaseChangeIso_hom {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (t : S')
    (x : (pullback.snd f g).fiber t) :
    pullback.fst (f.fiberToSpecResidueField (g t)) (residueFieldBaseChangeSituation g t).g
        ((fibreBaseChangeIso f g t).hom x) =
      restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition t x := by
  have h := congrArg (fun m : (pullback.snd f g).fiber t ⟶ f.fiber (g t) => m x)
    (fibreBaseChangeIso_hom_fst f g t)
  simpa only [Scheme.Hom.comp_apply] using h

/-! ### Base change of a cycle on a fibre -/

/-- The base-change homomorphism `Z_r(X_{g t}) ⟶ Z_r((X ×_S S')_t)` on fibrewise cycle groups:
the base change of cycles along the residue field extension `κ(t)/κ(g t)`, read on the fibre of
`X ×_S S' ⟶ S'` over `t` through `Stacks.Chow.fibreBaseChangeIso`. -/
def baseChangeFiberCycle {X S S' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (g : S' ⟶ S)
    (t : S') (r : ℕ) :
    FiberCycleGroup f (g t) r →+ FiberCycleGroup (pullback.snd f g) t r :=
  (cycleGroupRestrict (fieldChowSituation (S'.residueField t))
      (pullback.snd (f.fiberToSpecResidueField (g t)) (residueFieldBaseChangeSituation g t).g)
      ((pullback.snd f g).fiberToSpecResidueField t) (fibreBaseChangeIso f g t).hom
      (fibreBaseChangeIso_hom_snd f g t) (r : ℤ)).comp
    (baseChangeCyclePullback (residueFieldBaseChangeSituation g t)
      (f.fiberToSpecResidueField (g t)) (r : ℤ))

/-- The coefficient of the base change of a fibrewise cycle at a point `x` of `(X ×_S S')_t`: the
coefficient of the cycle at the image of `x` in `X_{g t}`, times the multiplicity with which `x`
enters the scheme-theoretic inverse image of the reduced closure of that image. -/
theorem baseChangeFiberCycle_apply {X S S' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (g : S' ⟶ S) (t : S') (r : ℕ) (z : FiberCycleGroup f (g t) r)
    (x : (pullback.snd f g).fiber t) :
    (baseChangeFiberCycle f g t r z : AlgebraicCycle ((pullback.snd f g).fiber t) ℤ) x =
      (z : AlgebraicCycle (f.fiber (g t)) ℤ)
          (restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition t x) *
        flatPullbackWeight (fieldChowSituation (S'.residueField t))
          (pullback.snd (f.fiberToSpecResidueField (g t)) (residueFieldBaseChangeSituation g t).g)
          (pullback.fst (f.fiberToSpecResidueField (g t)) (residueFieldBaseChangeSituation g t).g)
          (r : ℤ) ((fibreBaseChangeIso f g t).hom x) := by
  rw [← fst_fibreBaseChangeIso_hom f g t x]
  rfl

/-! ### Base change of a family of cycles -/

/-- **Stacks Project, Section 0H4N.** The base change `g^*α` of a family `α` of `r`-cycles on
the fibres of `X/S` along an arbitrary morphism `g : S' ⟶ S`, defined by its fibrewise
coefficient formula as `Stacks.Chow.baseChangeFamily`, has as its member over a point `t` of
`S'` the base change of the member of `α` over `g t` along the residue field extension
`κ(t)/κ(g t)`, read on the fibre `(X ×_S S')_t = X_{g t} ×_{κ(g t)} κ(t)`. -/
theorem baseChangeFamily_eq_baseChangeFiberCycle {X S S' : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (g : S' ⟶ S) (r : ℕ) (α : FamilyOfCycles f r) (t : S') :
    baseChangeFamily f g r α t = baseChangeFiberCycle f g t r (α (g t)) := by
  refine Subtype.ext <| Function.locallyFinsuppWithin.ext fun x => ?_
  rw [baseChangeFamily_apply f g r α t x, baseChangeFiberCycle_apply f g t r (α (g t)) x,
    ← flatPullbackWeight_eq_of_isIso (fieldChowSituation (S'.residueField t))
      ((pullback.snd f g).fiberToSpecResidueField t)
      (pullback.snd (f.fiberToSpecResidueField (g t)) (residueFieldBaseChangeSituation g t).g)
      (𝟙 (f.fiber (g t))) (fibreBaseChangeIso f g t).hom (fibreBaseChangeIso_hom_snd f g t)
      (restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition t)
      (pullback.fst (f.fiberToSpecResidueField (g t)) (residueFieldBaseChangeSituation g t).g)
      (by rw [Category.comp_id, fibreBaseChangeIso_hom_fst]) (r : ℤ) x]
  rfl

/-- The coefficient of the base-changed family on the fibre over `t` at a point `x`: the
coefficient of the member of `α` over `g t` at the image of `x` in `X_{g t}`, times the
multiplicity with which `x` enters the scheme-theoretic inverse image of the reduced closure of
that image, the multiplicity being read on `X_{g t} ×_{κ(g t)} κ(t)`. -/
theorem baseChangeFamily_apply_flatPullbackWeight {X S S' : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (g : S' ⟶ S) (r : ℕ) (α : FamilyOfCycles f r) (t : S')
    (x : (pullback.snd f g).fiber t) :
    (baseChangeFamily f g r α t : AlgebraicCycle ((pullback.snd f g).fiber t) ℤ) x =
      (α (g t) : AlgebraicCycle (f.fiber (g t)) ℤ)
          (restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition t x) *
        flatPullbackWeight (fieldChowSituation (S'.residueField t))
          (pullback.snd (f.fiberToSpecResidueField (g t)) (residueFieldBaseChangeSituation g t).g)
          (pullback.fst (f.fiberToSpecResidueField (g t)) (residueFieldBaseChangeSituation g t).g)
          (r : ℤ) ((fibreBaseChangeIso f g t).hom x) := by
  rw [baseChangeFamily_eq_baseChangeFiberCycle f g r α t]
  exact baseChangeFiberCycle_apply f g t r (α (g t)) x

/-- Base change of the zero family is the zero family. -/
@[simp]
theorem baseChangeFamily_zero {X S S' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (g : S' ⟶ S) (r : ℕ) :
    baseChangeFamily f g r (0 : FamilyOfCycles f r) = 0 :=
  funext fun t => by
    rw [baseChangeFamily_eq_baseChangeFiberCycle]
    exact map_zero _

/-- Base change of families of cycles is additive. -/
theorem baseChangeFamily_add {X S S' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (g : S' ⟶ S) (r : ℕ) (α β : FamilyOfCycles f r) :
    baseChangeFamily f g r (α + β) = baseChangeFamily f g r α + baseChangeFamily f g r β :=
  funext fun t => by
    simp only [Pi.add_apply, baseChangeFamily_eq_baseChangeFiberCycle, map_add]

/-- Base change of families of cycles commutes with negation. -/
theorem baseChangeFamily_neg {X S S' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (g : S' ⟶ S) (r : ℕ) (α : FamilyOfCycles f r) :
    baseChangeFamily f g r (-α) = -baseChangeFamily f g r α :=
  funext fun t => by
    simp only [Pi.neg_apply, baseChangeFamily_eq_baseChangeFiberCycle, map_neg]

/-- Base change of families of cycles on fibres as a homomorphism of abelian groups. -/
def baseChangeFamilyHom {X S S' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (g : S' ⟶ S)
    (r : ℕ) : FamilyOfCycles f r →+ FamilyOfCycles (pullback.snd f g) r where
  toFun := baseChangeFamily f g r
  map_zero' := baseChangeFamily_zero f g r
  map_add' := baseChangeFamily_add f g r

/-- The underlying function of `Stacks.Chow.baseChangeFamilyHom` is
`Stacks.Chow.baseChangeFamily`. -/
@[simp]
theorem baseChangeFamilyHom_apply {X S S' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (g : S' ⟶ S) (r : ℕ) (α : FamilyOfCycles f r) :
    baseChangeFamilyHom f g r α = baseChangeFamily f g r α :=
  rfl

end Stacks.Chow

end
