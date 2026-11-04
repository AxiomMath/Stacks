module

public import StacksFrontier.AlgebraicGeometry.Picard.CurveDegreeHom
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# The degree of a Picard class on a proper relative curve, and the degree components

Let `π : Y ⟶ T` be proper with fibres of dimension at most one. Every point `t` of `T` gives a
fibre `Y_t`, proper of dimension at most one over the residue field `κ(t)`, and restriction of
invertible modules along `Y_t ⟶ Y` followed by the degree on `Y_t` is a homomorphism
`Pic(Y) ⟶ ℤ`. Collecting these over the points of `T` gives

`deg : Pic(Y) ⟶ (T → ℤ)`,

the degree of a Picard class as a `ℤ`-valued function on the base. Its fibres over the functions
`T → ℤ` are the *degree components*: `Pic⁰` is the kernel, hence a subgroup, and each other
component is one of its cosets.

## Main definitions

* `AlgebraicGeometry.relativeInvertibleDegreeHomAt` — the degree at one point of the base, as a
  homomorphism `Pic(Y) ⟶ ℤ`.
* `AlgebraicGeometry.relativeInvertibleDegreeHom` — the degree as a homomorphism
  `Pic(Y) ⟶ (T → ℤ)`.
* `AlgebraicGeometry.relativeDegreeComponent` — the classes whose degree function is a given
  `φ : T → ℤ`.
* `AlgebraicGeometry.relativeDegreeZero` — `Pic⁰`, the kernel of the degree, as a subgroup of
  `Pic(Y)`.
* `AlgebraicGeometry.relativeDegreeComponentConst` — the classes of constant degree `d`, for an
  integer `d`.

## Main results

* `AlgebraicGeometry.relativeDegreeComponent_zero` — the component of the zero function is
  `Pic⁰`.
* `AlgebraicGeometry.add_mem_relativeDegreeComponent` and
  `AlgebraicGeometry.neg_mem_relativeDegreeComponent` — the degree components add, so `Pic⁰` is
  closed under the group law and under inverses while a component with `φ ≠ 0` is not.
* `AlgebraicGeometry.relativeDegreeComponent_eq_vadd_relativeDegreeZero` — a nonempty component
  is a coset of `Pic⁰`.
* `AlgebraicGeometry.relativeDegreeComponent_pairwise_disjoint`,
  `AlgebraicGeometry.existsUnique_mem_relativeDegreeComponent` and
  `AlgebraicGeometry.iUnion_relativeDegreeComponent` — `Pic(Y)` is the disjoint union of its
  degree components: every class has exactly one degree function.
* `AlgebraicGeometry.exists_mem_relativeDegreeComponentConst_of_isLocallyConstant` — on a
  connected base, a class whose degree function is locally constant lies in the component of an
  *integer* degree.

## Implementation notes

**Why the target is `T → ℤ` and not `ℤ`.** The degree of an invertible module on a relative
curve is a function on the base, one integer for each fibre, and nothing in the construction
makes it constant. It is constant when `T` is connected *and* the function is locally constant,
and that is the content of
`AlgebraicGeometry.exists_mem_relativeDegreeComponentConst_of_isLocallyConstant` below: with
local constancy in hand, `Mathlib`'s `IsLocallyConstant.exists_eq_const` gives the integer. Local
constancy itself is **not proved here**, and is not available in this library at this spelling.
What is available is [Stacks, Tag 0B9T] in the derived-fibre form,
`AlgebraicGeometry.ProperFlatFibreEulerCharacteristic.isLocallyConstant_chiFibre`, which is
locally constant in `t` for the function `t ↦ ∑ (-1)ⁱ dim_{κ(t)} Hⁱ(Rπ_*ℒ ⊗^L 𝒪_T κ(t))`. That
function is not identified with `t ↦ χ(Y_t, ℒ_t)` anywhere in this library — the module
documentation of
`StacksFrontier/AlgebraicGeometry/Perfect/ProperFlatFibreEulerCharacteristic.lean` records that the
only such comparison in the repository is an unproved statement — and the degree below is
built from `AlgebraicGeometry.invertibleCurveDegree` of the fibres, which is the difference of two
honest fibre Euler characteristics. So local constancy of this function is carried as a
hypothesis wherever it is needed, and never assumed silently. That identification, together with
the two clauses of [Stacks, Tag 0B9T] already granted in that file, is exactly what would
discharge it.

**Why the degree is a homomorphism without any further input.** It is a composite of two
homomorphisms, each already available: restriction of Picard classes to a fibre is
`Stacks.Picard.schemePullbackClassHom`, whose additivity is Tag 01CD, and the degree on the fibre
is `AlgebraicGeometry.invertibleCurveDegreeHom`, whose additivity is the invertible case of
[Stacks, Tag 0AYX]. Nothing has to be said about how the tensor product interacts with
restriction to the fibre: that is already inside the additivity of
`Stacks.Picard.schemePullbackClassHom`.

**Properness of the fibre map.** `π.fiberToSpecResidueField t` is `pullback.snd` of `π` along
`T.fromSpecResidueField t`, so it is proper because properness is stable under base change. The
instance is declared here because the library did not have it.

No Stacks tag is attached. The decomposition of a *relative Picard functor* into degree
components is clause (1) of Stacks Tag 0BA0, but that tag also asserts representability and
the smoothness, properness and dimension of the components, none of which is in sight here; and
the degree additivity this file consumes already carries [Stacks, Tag 0AYX] where it is proved.

## References

* [Stacks Project, Tag 0AYX](https://stacks.math.columbia.edu/tag/0AYX)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The map from the scheme-theoretic fibre of a proper morphism to the residue field of the
point is proper: it is a base change of the morphism, and properness is stable under base
change. -/
instance isProper_fiberToSpecResidueField {Y T : Scheme.{u}} (π : Y ⟶ T) [IsProper π] (t : T) :
    IsProper (π.fiberToSpecResidueField t) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsProper)
    (IsPullback.of_hasPullback π (T.fromSpecResidueField t)) ‹_›

variable {Y T : Scheme.{u}} (π : Y ⟶ T) [IsProper π]
  (hdim : ∀ t : T, topologicalKrullDim ↥(π.fiber t) ≤ 1)

/-! ### The degree of a Picard class on a relative curve -/

/-- **The degree of a Picard class on the fibre over a point `t` of the base**, as a homomorphism
`Pic(Y) ⟶ ℤ`: restrict the class along `Y_t ⟶ Y` and take its degree on the fibre, which is
proper of dimension at most one over `κ(t)`. -/
def relativeInvertibleDegreeHomAt (t : T) : Stacks.Picard.ofScheme Y →+ ℤ :=
  (invertibleCurveDegreeHom (T.residueField t) (π.fiberToSpecResidueField t) (hdim t)).comp
    (Stacks.Picard.schemePullbackClassHom (π.fiberι t))

/-- The degree at a point of the base is the degree on the fibre of the restriction of the
class. -/
theorem relativeInvertibleDegreeHomAt_apply (t : T) (x : Stacks.Picard.ofScheme Y) :
    relativeInvertibleDegreeHomAt π hdim t x =
      invertibleCurveDegreeHom (T.residueField t) (π.fiberToSpecResidueField t) (hdim t)
        (Stacks.Picard.schemePullbackClass (π.fiberι t) x) :=
  rfl

/-- **The degree of a Picard class on a proper relative curve**, as a homomorphism
`Pic(Y) ⟶ (T → ℤ)`: the function sending a point `t` of the base to the degree of the class on
the fibre `Y_t`.

It is a homomorphism because each of its values is: restriction of Picard classes to a fibre is
additive (Tag 01CD) and the degree on a fibre is additive (the invertible case of
[Stacks, Tag 0AYX]). -/
def relativeInvertibleDegreeHom : Stacks.Picard.ofScheme Y →+ (T → ℤ) :=
  AddMonoidHom.pi fun t => relativeInvertibleDegreeHomAt π hdim t

/-- The value of the degree at a point of the base. -/
@[simp]
theorem relativeInvertibleDegreeHom_apply (x : Stacks.Picard.ofScheme Y) (t : T) :
    relativeInvertibleDegreeHom π hdim x t = relativeInvertibleDegreeHomAt π hdim t x :=
  rfl

/-- The degree of the class of an invertible module `ℒ` at a point `t` of the base is the degree
of the restriction of `ℒ` to the fibre `Y_t`. -/
theorem relativeInvertibleDegreeHom_picardClass (L : Y.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible Y.presheaf
      (Stacks.RingedSpace.structureIsSheaf Y.toRingedSpace) L) (t : T) :
    relativeInvertibleDegreeHom π hdim
        (Stacks.SheafOfModules.picardClass Y.presheaf
          (Stacks.RingedSpace.structureIsSheaf Y.toRingedSpace) L hL) t =
      @invertibleCurveDegree ↥(T.residueField t) _ (π.fiber t) (π.fiberToSpecResidueField t) _
        (hdim t)
        ((Stacks.RingedSpace.pullbackFunctor (π.fiberι t).toLRSHom.toShHom).obj L)
        (Stacks.RingedSpace.modulePullback_isInvertible_of _ L hL) :=
  (congrArg (invertibleCurveDegreeHom ↥(T.residueField t) (π.fiberToSpecResidueField t) (hdim t))
      (Stacks.Picard.pullbackClass_classOf (π.fiberι t).toLRSHom.toShHom L hL)).trans
    (invertibleCurveDegreeHom_picardClass _ _ _ _ _)

/-- The degree of a sum of Picard classes is the sum of the degrees. -/
theorem relativeInvertibleDegreeHom_add (x y : Stacks.Picard.ofScheme Y) :
    relativeInvertibleDegreeHom π hdim (x + y) =
      relativeInvertibleDegreeHom π hdim x + relativeInvertibleDegreeHom π hdim y :=
  map_add _ x y

/-- The degree of the inverse of a Picard class is the negative of its degree. -/
theorem relativeInvertibleDegreeHom_neg (x : Stacks.Picard.ofScheme Y) :
    relativeInvertibleDegreeHom π hdim (-x) = -relativeInvertibleDegreeHom π hdim x :=
  map_neg _ x

/-! ### The degree components -/

/-- **The degree component `Picᵠ`** of a proper relative curve: the Picard classes whose degree
function on the base is `φ`. -/
def relativeDegreeComponent (φ : T → ℤ) : Set (Stacks.Picard.ofScheme Y) :=
  {x | relativeInvertibleDegreeHom π hdim x = φ}

/-- A Picard class lies in `relativeDegreeComponent π hdim φ` if and only if its degree function
is `φ`. -/
theorem mem_relativeDegreeComponent_iff (φ : T → ℤ) (x : Stacks.Picard.ofScheme Y) :
    x ∈ relativeDegreeComponent π hdim φ ↔ relativeInvertibleDegreeHom π hdim x = φ :=
  Iff.rfl

/-- **`Pic⁰` of a proper relative curve, as a subgroup of `Pic(Y)`**: the Picard classes of
degree zero on every fibre, the kernel of `relativeInvertibleDegreeHom`. -/
def relativeDegreeZero : AddSubgroup (Stacks.Picard.ofScheme Y) :=
  (relativeInvertibleDegreeHom π hdim).ker

/-- A Picard class lies in `relativeDegreeZero π hdim` if and only if its degree function is
zero. -/
theorem mem_relativeDegreeZero_iff (x : Stacks.Picard.ofScheme Y) :
    x ∈ relativeDegreeZero π hdim ↔ relativeInvertibleDegreeHom π hdim x = 0 :=
  AddMonoidHom.mem_ker

/-- **`Pic⁰` is the degree component of the zero function.** -/
theorem relativeDegreeComponent_zero :
    relativeDegreeComponent π hdim 0 =
      (relativeDegreeZero π hdim : Set (Stacks.Picard.ofScheme Y)) :=
  rfl

/-- **The degree components add**: the sum of a class of degree `φ` and a class of degree `ψ` has
degree `φ + ψ`. -/
theorem add_mem_relativeDegreeComponent {φ ψ : T → ℤ} {x y : Stacks.Picard.ofScheme Y}
    (hx : x ∈ relativeDegreeComponent π hdim φ) (hy : y ∈ relativeDegreeComponent π hdim ψ) :
    x + y ∈ relativeDegreeComponent π hdim (φ + ψ) := by
  simp only [mem_relativeDegreeComponent_iff] at hx hy ⊢
  rw [relativeInvertibleDegreeHom_add, hx, hy]

/-- **The degree component of the inverse**: the inverse of a class of degree `φ` has degree
`-φ`. -/
theorem neg_mem_relativeDegreeComponent {φ : T → ℤ} {x : Stacks.Picard.ofScheme Y}
    (hx : x ∈ relativeDegreeComponent π hdim φ) :
    -x ∈ relativeDegreeComponent π hdim (-φ) := by
  simp only [mem_relativeDegreeComponent_iff] at hx ⊢
  rw [relativeInvertibleDegreeHom_neg, hx]

/-- **A nonempty degree component is a coset of `Pic⁰`.** Given one class `x` of degree `φ`, the
classes of degree `φ` are exactly the translates of the classes of degree zero by `x`. -/
theorem relativeDegreeComponent_eq_vadd_relativeDegreeZero {φ : T → ℤ}
    {x : Stacks.Picard.ofScheme Y} (hx : x ∈ relativeDegreeComponent π hdim φ) :
    relativeDegreeComponent π hdim φ =
      (fun z => x + z) '' (relativeDegreeZero π hdim : Set (Stacks.Picard.ofScheme Y)) := by
  ext y
  constructor
  · intro hy
    refine ⟨y - x, ?_, by abel⟩
    rw [SetLike.mem_coe, mem_relativeDegreeZero_iff, map_sub, hy, hx, sub_self]
  · rintro ⟨z, hz, rfl⟩
    simpa using add_mem_relativeDegreeComponent π hdim hx hz

/-- **Distinct degree components are disjoint.** -/
theorem relativeDegreeComponent_pairwise_disjoint :
    Pairwise (Function.onFun Disjoint (relativeDegreeComponent π hdim)) := by
  intro φ ψ hne
  rw [Function.onFun, Set.disjoint_left]
  intro x hx hx'
  exact hne (hx.symm.trans hx')

/-- **Every Picard class lies in exactly one degree component**, the one of its own degree
function. With `AlgebraicGeometry.relativeDegreeComponent_pairwise_disjoint` this is the
statement that `Pic(Y)` is the disjoint union of the degree components. -/
theorem existsUnique_mem_relativeDegreeComponent (x : Stacks.Picard.ofScheme Y) :
    ∃! φ : T → ℤ, x ∈ relativeDegreeComponent π hdim φ :=
  ⟨relativeInvertibleDegreeHom π hdim x, rfl, fun _ h => h.symm⟩

/-- **`Pic(Y)` is the union of its degree components.** -/
theorem iUnion_relativeDegreeComponent :
    ⋃ φ : T → ℤ, relativeDegreeComponent π hdim φ = Set.univ :=
  Set.iUnion_eq_univ_iff.2 fun x => ⟨relativeInvertibleDegreeHom π hdim x, rfl⟩

/-! ### The components of integer degree -/

/-- **The degree component `Picᵈ`** of an integer `d`: the Picard classes whose degree is `d` on
every fibre. -/
def relativeDegreeComponentConst (d : ℤ) : Set (Stacks.Picard.ofScheme Y) :=
  relativeDegreeComponent π hdim (Function.const ↥T d)

/-- A Picard class lies in `relativeDegreeComponentConst π hdim d` if and only if its degree on
every fibre is `d`. -/
theorem mem_relativeDegreeComponentConst_iff (d : ℤ) (x : Stacks.Picard.ofScheme Y) :
    x ∈ relativeDegreeComponentConst π hdim d ↔
      ∀ t : T, relativeInvertibleDegreeHom π hdim x t = d :=
  funext_iff

/-- **`Pic⁰` is the component of integer degree zero.** -/
theorem relativeDegreeComponentConst_zero :
    relativeDegreeComponentConst π hdim 0 =
      (relativeDegreeZero π hdim : Set (Stacks.Picard.ofScheme Y)) :=
  rfl

/-- **`Picᵈ` is closed under the group law only for `d = 0`** — the sum of a class of degree `d`
and a class of degree `e` has degree `d + e`. -/
theorem add_mem_relativeDegreeComponentConst {d e : ℤ} {x y : Stacks.Picard.ofScheme Y}
    (hx : x ∈ relativeDegreeComponentConst π hdim d)
    (hy : y ∈ relativeDegreeComponentConst π hdim e) :
    x + y ∈ relativeDegreeComponentConst π hdim (d + e) :=
  add_mem_relativeDegreeComponent π hdim hx hy

/-- The inverse of a class of degree `d` has degree `-d`. -/
theorem neg_mem_relativeDegreeComponentConst {d : ℤ} {x : Stacks.Picard.ofScheme Y}
    (hx : x ∈ relativeDegreeComponentConst π hdim d) :
    -x ∈ relativeDegreeComponentConst π hdim (-d) :=
  neg_mem_relativeDegreeComponent π hdim hx

/-- **A nonempty `Picᵈ` is a coset of `Pic⁰`.** -/
theorem relativeDegreeComponentConst_eq_vadd_relativeDegreeZero {d : ℤ}
    {x : Stacks.Picard.ofScheme Y} (hx : x ∈ relativeDegreeComponentConst π hdim d) :
    relativeDegreeComponentConst π hdim d =
      (fun z => x + z) '' (relativeDegreeZero π hdim : Set (Stacks.Picard.ofScheme Y)) :=
  relativeDegreeComponent_eq_vadd_relativeDegreeZero π hdim hx

/-- Distinct integers give disjoint degree components, provided the base is nonempty: on an empty
base every class has every constant degree. -/
theorem relativeDegreeComponentConst_disjoint [Nonempty ↥T] {d e : ℤ} (hne : d ≠ e) :
    Disjoint (relativeDegreeComponentConst π hdim d) (relativeDegreeComponentConst π hdim e) :=
  relativeDegreeComponent_pairwise_disjoint π hdim fun h =>
    hne (congrFun h (Classical.arbitrary ↥T))

/-- **On a connected base, a class whose degree function is locally constant has an integer
degree**, so it lies in `Picᵈ` for exactly one `d`.

Local constancy is a hypothesis: see this file's implementation notes for what would discharge
it, namely the identification of
`AlgebraicGeometry.ProperFlatFibreEulerCharacteristic.chiFibre` with the fibrewise Euler
characteristic, which this library does not carry. -/
theorem exists_mem_relativeDegreeComponentConst_of_isLocallyConstant [PreconnectedSpace ↥T]
    (x : Stacks.Picard.ofScheme Y)
    (hlc : IsLocallyConstant (relativeInvertibleDegreeHom π hdim x)) :
    ∃ d : ℤ, x ∈ relativeDegreeComponentConst π hdim d :=
  hlc.exists_eq_const

end AlgebraicGeometry

end
