module

public import StacksFrontier.AlgebraicGeometry.Picard.RelativeCurveDegree
public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardFunctor
public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardSequenceLeftExactness

/-!
# The degree decomposition of the Picard functor of a relative curve

Let `f : X ⟶ S` be a morphism of a big fppf site which is proper with fibres of dimension at most
one — a proper relative curve. For a test scheme `T` over `S` the Picard functor's presheaf takes
the value `Pic(X_T)`, and the base change `X_T` is proper over `T` with the same fibres. So the
degree of a Picard class on a proper relative curve applies, and gives

`deg_T : Pic(X_T) ⟶ (T → ℤ)`,

whose kernel is `Pic⁰(X_T)` and whose fibres are the degree components `Picᵈ(X_T)`.

## Main definitions

* `Stacks.PicardFunctor.picardDegreeHom` — the degree on `Pic(X_T)`, valued in the `ℤ`-valued
  functions on `T`.
* `Stacks.PicardFunctor.picardDegreeZero` — `Pic⁰(X_T)`, a subgroup of `Pic(X_T)`.
* `Stacks.PicardFunctor.picardDegreeComponentConst` — `Picᵈ(X_T)` for an integer `d`.

## Main results

* `Stacks.PicardFunctor.isProper_baseChangeProj` — the projection `X_T ⟶ T` is proper when
  `X ⟶ S` is.
* `Stacks.PicardFunctor.picardDegreeComponentConst_zero` — `Pic⁰` is the component of degree
  zero, so it is the one component that is a subgroup.
* `Stacks.PicardFunctor.add_mem_picardDegreeComponentConst` and
  `Stacks.PicardFunctor.picardDegreeComponentConst_eq_vadd_picardDegreeZero` — the components add,
  and a nonempty `Picᵈ` is a coset of `Pic⁰`.
* `Stacks.PicardFunctor.existsUnique_mem_picardDegreeComponent` — every class of `Pic(X_T)` has
  exactly one degree, so `Pic(X_T)` is the disjoint union of the degree components.
* `Stacks.PicardFunctor.exists_mem_picardDegreeComponentConst_of_isLocallyConstant` — on a
  connected test scheme, a class of locally constant degree lies in `Picᵈ` for an integer `d`.

## Implementation notes

These are the objects of clauses (1), (2) and (3) of Stacks Tag 0BA0 with representability
removed: the degree map that cuts the Picard functor into pieces, the pieces, and the fact that
the piece of degree zero is a subgroup while the others are its cosets. The proofs are those of
`StacksFrontier/AlgebraicGeometry/Picard/RelativeCurveDegree.lean`, which states them for an
arbitrary proper relative curve `π : Y ⟶ T`; what is specific to the Picard functor and proved
here is that the base change `X_T ⟶ T` is again such a morphism. `picardAt B hX hS f T` **is**
`Stacks.Picard.ofScheme (baseChange B hX hS f T)`, so nothing has to be transported.

The projection `X_T ⟶ T` itself is `Stacks.PicardFunctor.baseChangeProj` of
`StacksFrontier/AlgebraicGeometry/PicardScheme/PicardSequenceLeftExactness.lean`.

## References

* [Stacks Project, Tag 0B9L](https://stacks.math.columbia.edu/tag/0B9L)
* [Stacks Project, Tag 0B59](https://stacks.math.columbia.edu/tag/0B59)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.PicardFunctor

variable (B : BigFppfSite.{u}) {X S : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S)
  (f : B.obj hX ⟶ B.obj hS)

/-! ### The base change as a relative curve over the test scheme -/

/-- **The base change of a proper morphism is proper over the test scheme.** So if `X ⟶ S` is a
proper relative curve then so is `X_T ⟶ T`. -/
theorem isProper_baseChangeProj (hproper : IsProper (B.inclusion.map f))
    (T : BigFppfOver B S hS) : IsProper (baseChangeProj B hX hS f T) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsProper)
    (IsPullback.of_hasPullback (B.inclusion.map f) (B.inclusion.map T.hom)) hproper

section

variable (T : BigFppfOver B S hS) [IsProper (baseChangeProj B hX hS f T)]
  (hdim : ∀ t : ↥((BigFppfOver.toScheme B S hS).obj T),
    topologicalKrullDim ↥((baseChangeProj B hX hS f T).fiber t) ≤ 1)

/-! ### The degree on the values of the Picard functor -/

/-- **The degree on the Picard group of a base change of a proper relative curve**, the map that
cuts the Picard functor into its degree components: a homomorphism from `Pic(X_T)`, the value at
`T` of the presheaf whose sheafification is the Picard functor, to the `ℤ`-valued functions on
`T`, sending a class to the function recording its degree on each fibre of `X_T ⟶ T`. -/
def picardDegreeHom : picardAt B hX hS f T →+ (↥((BigFppfOver.toScheme B S hS).obj T) → ℤ) :=
  relativeInvertibleDegreeHom (baseChangeProj B hX hS f T) hdim

/-- The degree on `Pic(X_T)` is the degree of a Picard class on the relative curve `X_T ⟶ T`. -/
theorem picardDegreeHom_apply (x : picardAt B hX hS f T)
    (t : ↥((BigFppfOver.toScheme B S hS).obj T)) :
    picardDegreeHom B hX hS f T hdim x t =
      relativeInvertibleDegreeHomAt (baseChangeProj B hX hS f T) hdim t x :=
  rfl

/-! ### The degree components -/

/-- **The degree component of a function `φ : T → ℤ`**: the classes of `Pic(X_T)` whose degree on
the fibre over `t` is `φ t`, for every point `t` of `T`. -/
def picardDegreeComponent (φ : ↥((BigFppfOver.toScheme B S hS).obj T) → ℤ) :
    Set (picardAt B hX hS f T) :=
  relativeDegreeComponent (baseChangeProj B hX hS f T) hdim φ

/-- **`Pic⁰(X_T)`, as a subgroup of `Pic(X_T)`**: the classes of degree zero on every fibre. It
is the kernel of the degree, which is why it and no other component is a subgroup. -/
def picardDegreeZero : AddSubgroup (picardAt B hX hS f T) :=
  relativeDegreeZero (baseChangeProj B hX hS f T) hdim

/-- **`Picᵈ(X_T)` for an integer `d`**: the classes of degree `d` on every fibre of `X_T ⟶ T`. -/
def picardDegreeComponentConst (d : ℤ) : Set (picardAt B hX hS f T) :=
  relativeDegreeComponentConst (baseChangeProj B hX hS f T) hdim d

/-- A class of `Pic(X_T)` lies in `Picᵈ(X_T)` if and only if its degree on the fibre over every
point `t` of `T` is `d`. -/
theorem mem_picardDegreeComponentConst_iff (d : ℤ) (x : picardAt B hX hS f T) :
    x ∈ picardDegreeComponentConst B hX hS f T hdim d ↔
      ∀ t : ↥((BigFppfOver.toScheme B S hS).obj T),
        picardDegreeHom B hX hS f T hdim x t = d :=
  mem_relativeDegreeComponentConst_iff _ hdim d x

/-- **`Picᵈ` is a subgroup exactly for `d = 0`, where it is `Pic⁰`.** -/
theorem picardDegreeComponentConst_zero :
    picardDegreeComponentConst B hX hS f T hdim 0 =
      (picardDegreeZero B hX hS f T hdim : Set (picardAt B hX hS f T)) :=
  relativeDegreeComponentConst_zero _ hdim

/-- **The degree components add**: a class of degree `d` plus a class of degree `e` has degree
`d + e`. In particular `Pic⁰` is closed under the group law, and `Picᵈ` for `d ≠ 0` is not. -/
theorem add_mem_picardDegreeComponentConst {d e : ℤ} {x y : picardAt B hX hS f T}
    (hx : x ∈ picardDegreeComponentConst B hX hS f T hdim d)
    (hy : y ∈ picardDegreeComponentConst B hX hS f T hdim e) :
    x + y ∈ picardDegreeComponentConst B hX hS f T hdim (d + e) :=
  add_mem_relativeDegreeComponentConst _ hdim hx hy

/-- The inverse of a class of degree `d` has degree `-d`; in particular `Pic⁰` is closed under
inverses. -/
theorem neg_mem_picardDegreeComponentConst {d : ℤ} {x : picardAt B hX hS f T}
    (hx : x ∈ picardDegreeComponentConst B hX hS f T hdim d) :
    -x ∈ picardDegreeComponentConst B hX hS f T hdim (-d) :=
  neg_mem_relativeDegreeComponentConst _ hdim hx

/-- **A nonempty `Picᵈ` is a coset of `Pic⁰`.** -/
theorem picardDegreeComponentConst_eq_vadd_picardDegreeZero {d : ℤ} {x : picardAt B hX hS f T}
    (hx : x ∈ picardDegreeComponentConst B hX hS f T hdim d) :
    picardDegreeComponentConst B hX hS f T hdim d =
      (fun z => x + z) '' (picardDegreeZero B hX hS f T hdim : Set (picardAt B hX hS f T)) :=
  relativeDegreeComponentConst_eq_vadd_relativeDegreeZero _ hdim hx

/-- **`Pic(X_T)` is the disjoint union of its degree components**: every class has exactly one
degree function on `T`. -/
theorem existsUnique_mem_picardDegreeComponent (x : picardAt B hX hS f T) :
    ∃! φ : ↥((BigFppfOver.toScheme B S hS).obj T) → ℤ,
      x ∈ picardDegreeComponent B hX hS f T hdim φ :=
  existsUnique_mem_relativeDegreeComponent _ hdim x

/-- **The degree components cover `Pic(X_T)`.** -/
theorem iUnion_picardDegreeComponent :
    ⋃ φ : ↥((BigFppfOver.toScheme B S hS).obj T) → ℤ,
      picardDegreeComponent B hX hS f T hdim φ = Set.univ :=
  iUnion_relativeDegreeComponent _ hdim

/-- **Distinct degree components are disjoint.** -/
theorem picardDegreeComponent_pairwise_disjoint :
    Pairwise (Function.onFun Disjoint (picardDegreeComponent B hX hS f T hdim)) :=
  relativeDegreeComponent_pairwise_disjoint _ hdim

/-- **On a connected test scheme, a class of locally constant degree has an integer degree**, so
it lies in `Picᵈ` for exactly one integer `d`. -/
theorem exists_mem_picardDegreeComponentConst_of_isLocallyConstant
    [PreconnectedSpace ↥((BigFppfOver.toScheme B S hS).obj T)] (x : picardAt B hX hS f T)
    (hlc : IsLocallyConstant (picardDegreeHom B hX hS f T hdim x)) :
    ∃ d : ℤ, x ∈ picardDegreeComponentConst B hX hS f T hdim d :=
  exists_mem_relativeDegreeComponentConst_of_isLocallyConstant _ hdim x hlc

end

end Stacks.PicardFunctor

end
