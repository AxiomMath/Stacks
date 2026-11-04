module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.InfinityDivisorZeroScheme
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.SpecializationProperPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.ProperPushforwardDescent
public import StacksFrontier.AlgebraicGeometry.Chow.FirstChernClassTensor
public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinity
public import StacksFrontier.AlgebraicGeometry.Chow.GysinPushforwardChernCap

/-!
# The class at infinity retracts the Gysin map at infinity

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, let `b : W ⟶ 𝐏¹_X` be a proper morphism which is an isomorphism over the
affine chart `𝐀¹_X`, and let `C ∈ A⁰(W_∞ ⟶ X)` be the class of Stacks 0F9J, carried by
`Stacks.Chow.GysinAtInfinityData`. Stacks 0FAR is the identity

  `C ∘ (W_∞ ⟶ X)_* ∘ i_∞^* = i_∞^*`

of maps `CH_{k+1}(W) ⟶ CH_k(W_∞)`.

It follows from two facts. First, `(W_∞ ⟶ X)_* i_∞^*β = i_0^*β`, because `i_{∞,*}i_∞^*β` and
`i_{0,*}i_0^*β` both represent `c₁(𝒪_{𝐏¹_X}(1)) ∩ β` on `W` and so push forward to the same class
on `X`. Second, `β` restricts over `𝐀¹_X` to the flat pullback of `i_0^*β`, so `β` is a lift
admissible in the recipe `C ∩ α = i_∞^*β` of Stacks 0F9J for `α = i_0^*β`.

## Main definitions

* `Stacks.Chow.InfinityZeroFibrePresentation`: over a test scheme `T ⟶ X`, the zero-scheme
  presentation of the divisor at infinity (`Stacks.Chow.InfinityDivisorZeroScheme`), together with
  the projection `W_T ⟶ T`, a zero-scheme presentation of the fibre over zero, the fact that this
  fibre projects isomorphically to `T`, and an isomorphism between the two invertible modules.
* `Stacks.Chow.InfinityZeroFibrePresentation.gysinCapZero`: the class `i_0^*β`, read on the test
  scheme through the isomorphism `W_{0,T} ≅ T`.

## Main results

* `Stacks.Chow.InfinityZeroFibrePresentation.properChowPushforward_gysinCap`:
  `(W_{∞,T} ⟶ T)_* i_∞^*β = i_0^*β`.
* `Stacks.Chow.gysinAtInfinity_cap_properPushforward_gysinCap`: the identity of Stacks 0FAR for a
  class carried by `Stacks.Chow.GysinAtInfinityData`, given the recipe of Stacks 0F9J and the
  lifting property of `β`.

## Implementation notes

`A⁰(W_∞ ⟶ X)` is `Stacks.Chow.BivariantClass` in degree `0`, and `C` is the `bivariantClass` field
of `Stacks.Chow.GysinAtInfinityData`. The Gysin map `i_∞^*` is
`Stacks.Chow.InfinityDivisorZeroScheme.gysinCap`: the Gysin homomorphism of Stacks 02T8 for the
section cutting out the divisor at infinity, transported along the identification of its zero
scheme with the base change of `W_∞`. It is defined on cycles `β ∈ Z_{k+1}(W_T)`; a statement for
every cycle is a statement for every cycle class, both sides factoring through rational
equivalence. The identity is stated over an arbitrary test scheme `t : T ⟶ X` locally of finite
type, of which the tag is the case `t = 𝟙_X`.

The recipe `C ∩ α = i_∞^*β` of Stacks 0F9J is the hypothesis `hcap`, for `β` lifting `α` in the
sense of an abstract predicate `Ext`; the hypothesis `hExt` says that `β` lifts `i_0^*β`.

The fibre over zero is presented as the zero scheme of a section of an invertible module, so that
Stacks 02T9 (`Stacks.Chow.properChowPushforward_gysinHomomorphismOfInvertible`) computes the
pushforward of its Gysin class as for the divisor at infinity. Both invertible modules are the
pullback of `𝒪_{𝐏¹_X}(1)`; the field `lineIso` records an isomorphism between them, and
`Stacks.Chow.firstChernClassCapOfInvertible_congr` turns it into the equality of the two cap
products. The field `isIso_zeroFibre` is the identification `W_{0,T} ≅ T`, which holds because `b`
is an isomorphism over `𝐀¹_X`.

## References

* [Stacks Project, Tag 0FAR](https://stacks.math.columbia.edu/tag/0FAR)
* [Stacks Project, Tag 0F9J](https://stacks.math.columbia.edu/tag/0F9J)
* [Stacks Project, Tag 0FAQ](https://stacks.math.columbia.edu/tag/0FAQ)
* [Stacks Project, Tag 02T9](https://stacks.math.columbia.edu/tag/02T9)
* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
* [Stacks Project, Tag 0B74](https://stacks.math.columbia.edu/tag/0B74)
* [Stacks Project, Tag 0F96](https://stacks.math.columbia.edu/tag/0F96)
* [Stacks Project, Tag 0GU8](https://stacks.math.columbia.edu/tag/0GU8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The fibre over zero, as a second zero scheme on the ambient of the test scheme -/

/-- Over a test scheme `t : T ⟶ X`: the zero-scheme presentation of the divisor at infinity
(`Stacks.Chow.InfinityDivisorZeroScheme`) together with the proper projection `W_T ⟶ T`, the
compatibility of the identification of the divisor at infinity with it, a zero-scheme presentation
of the fibre over zero, the fact that the fibre over zero projects isomorphically to `T`, and an
isomorphism between the two invertible modules. -/
structure InfinityZeroFibrePresentation (C : ChowSituation.{u}) {X WInf T : Scheme.{u}}
    (sX : X ⟶ C.S) (sWInf : WInf ⟶ C.S) (pInf : WInf ⟶ X) (t : T ⟶ X)
    extends InfinityDivisorZeroScheme C sWInf pInf t where
  /-- The projection `W_T ⟶ T` of the base change. -/
  ambProjection : amb ⟶ T
  [proper_ambProjection : IsProper ambProjection]
  /-- The projection is a morphism over the base of the Chow situation. -/
  ambProjection_comp : ambProjection ≫ (t ≫ sX) = ambStructure
  /-- The identification of the divisor at infinity of `W_T` with the base change of `W_∞` lies
  over `T`. -/
  iso_comp_projection : iso.hom ≫ pullback.snd pInf t =
    (Stacks.Divisors.zeroScheme amb line divisorSection).subschemeι ≫ ambProjection
  /-- An invertible module on `W_T` cutting out the fibre over zero. -/
  lineZero : amb.Modules
  [invertible_lineZero : AlgebraicGeometry.SheafOfModules.IsInvertible amb.sheaf.obj
    amb.ringCatSheaf.property lineZero]
  /-- The section whose zero scheme is the fibre over zero of `W_T`. -/
  zeroFibreSection : Γ(lineZero, ⊤)
  /-- The fibre over zero projects isomorphically to the test scheme. -/
  isIso_zeroFibre :
    IsIso ((Stacks.Divisors.zeroScheme amb lineZero zeroFibreSection).subschemeι ≫ ambProjection)
  /-- An isomorphism between the invertible modules cutting out the fibre over zero and the
  divisor at infinity. -/
  lineIso : lineZero ≅ line

namespace InfinityZeroFibrePresentation

variable {C : ChowSituation.{u}} {X WInf T : Scheme.{u}} {sX : X ⟶ C.S} {sWInf : WInf ⟶ C.S}
  {pInf : WInf ⟶ X} {t : T ⟶ X} (P : InfinityZeroFibrePresentation C sX sWInf pInf t)

/-- The projection `W_T ⟶ T` is proper. -/
instance isProper_ambProjection : IsProper P.ambProjection := P.proper_ambProjection

/-- The module cutting out the fibre over zero is invertible. -/
instance isInvertible_lineZero : AlgebraicGeometry.SheafOfModules.IsInvertible P.amb.sheaf.obj
    P.amb.ringCatSheaf.property P.lineZero := P.invertible_lineZero

/-- The projection of the fibre over zero `W_{0,T} ⟶ T` is an isomorphism. -/
instance isIso_zeroFibreProjection :
    IsIso ((Stacks.Divisors.zeroScheme P.amb P.lineZero P.zeroFibreSection).subschemeι ≫
      P.ambProjection) := P.isIso_zeroFibre

/-- The projection of the fibre over zero to the test scheme is a morphism over the base of the
Chow situation. -/
theorem zeroFibreProjection_comp :
    ((Stacks.Divisors.zeroScheme P.amb P.lineZero P.zeroFibreSection).subschemeι ≫
        P.ambProjection) ≫ (t ≫ sX) =
      (Stacks.Divisors.zeroScheme P.amb P.lineZero P.zeroFibreSection).subschemeι ≫
        P.ambStructure := by
  rw [Category.assoc, P.ambProjection_comp]

variable [LocallyOfFiniteType sX] [LocallyOfFiniteType t]

/-- The class `i_0^*β`: the Gysin homomorphism of the fibre over zero, transported to the test
scheme along the isomorphism `W_{0,T} ≅ T`. -/
def gysinCapZero (k : ℤ) (β : CycleGroup C P.ambStructure (k + 1)) : chowGroup C (t ≫ sX) k :=
  chowPushforwardOfIso C
    ((Stacks.Divisors.zeroScheme P.amb P.lineZero P.zeroFibreSection).subschemeι ≫
      P.ambStructure)
    (t ≫ sX)
    ((Stacks.Divisors.zeroScheme P.amb P.lineZero P.zeroFibreSection).subschemeι ≫
      P.ambProjection)
    P.zeroFibreProjection_comp k
    (gysinHomomorphismOfInvertible C P.ambStructure k P.lineZero P.zeroFibreSection β)

/-- Pushing the Gysin class at infinity forward to the test scheme gives the Gysin class of the
fibre over zero:

  `(W_{∞,T} ⟶ T)_* i_∞^*β = i_0^*β`. -/
theorem properChowPushforward_gysinCap [LocallyOfFiniteType sWInf]
    [IsProper (pullback.snd pInf t)] (hpInf : pInf ≫ sX = sWInf) (k : ℤ)
    (β : CycleGroup C P.ambStructure (k + 1)) :
    properChowPushforward C (pullback.fst pInf t ≫ sWInf) (t ≫ sX) (pullback.snd pInf t)
        (pullbackSnd_comp_structureMorphism_eq C sWInf sX pInf hpInf t) k
        (properPushforwardDescends C _ _ _ _ _)
        (P.gysinCap (properPushforwardDescends C) k β) =
      P.gysinCapZero k β := by
  refine (properChowPushforward_comp_eq C _ _ _ _ P.iso.hom _ _ P.ambProjection
    P.iso_comp_projection P.iso_comp _ rfl P.ambProjection_comp k _ _
    (properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion _ C _ _ rfl k)
    (properPushforwardDescends C _ _ _ _ _) _).trans ?_
  rw [properChowPushforward_gysinHomomorphismOfInvertible,
    ← firstChernClassCapOfInvertible_congr C _ k _ _ P.lineIso,
    ← properChowPushforward_gysinHomomorphismOfInvertible]
  exact (properChowPushforward_comp_apply C _ _ _ _ P.ambProjection _ rfl rfl
    P.ambProjection_comp P.zeroFibreProjection_comp k
    (properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion _ C _ _ rfl k)
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _) _).symm

end InfinityZeroFibrePresentation

/-! ### Stacks 0FAR -/

section Retraction

variable {C : ChowSituation.{u}} {G : GysinSystem C} {X W T : Scheme.{u}} {f : X ⟶ C.S}
  [LocallyOfFiniteType f] {b : W ⟶ projectiveLineProduct f} [IsProper b]
  {hA : IsIso (pullback.snd b (projectiveLineAffineChart f))}
  [LocallyOfFiniteType (modificationProjection f b)]
  [LocallyOfFiniteType (modificationProjectionAtInfinity f b)]
  (D : GysinAtInfinityData C G f b hA) {t : T ⟶ X} [LocallyOfFiniteType t]
  [IsProper (pullback.snd (modificationProjectionAtInfinity f b) t)]
  (P : InfinityZeroFibrePresentation C f (modificationProjectionAtInfinity f b ≫ f)
    (modificationProjectionAtInfinity f b) t)
  (Ext : ∀ k : ℤ, chowGroup C (t ≫ f) k → CycleGroup C P.ambStructure (k + 1) → Prop)

omit [LocallyOfFiniteType (modificationProjection f b)] in
/-- Let `C ∈ A⁰(W_∞ ⟶ X)` be a class carried by `Stacks.Chow.GysinAtInfinityData` which satisfies
the recipe `C ∩ α = i_∞^*β` of Stacks 0F9J (`hcap`) for every `β` lifting `α` in the sense of
`Ext`, and suppose every `β` lifts `i_0^*β` (`hExt`). Then

  `C ∘ (W_∞ ⟶ X)_* ∘ i_∞^* = i_∞^*`

on the test scheme `t : T ⟶ X` and in every degree: for every cycle `β ∈ Z_{k+1}(W_T)`, capping
with `C` the class obtained by pushing `i_∞^*β` forward to `T` returns `i_∞^*β`. -/
theorem gysinAtInfinity_cap_properPushforward_gysinCap (k : ℤ)
    (hcap : ∀ (α : chowGroup C (t ≫ f) k) (β : CycleGroup C P.ambStructure (k + 1)),
      Ext k α β →
      chowGroupDegreeEquiv C
          (pullback.fst (modificationProjectionAtInfinity f b) t ≫
            (modificationProjectionAtInfinity f b ≫ f))
          (sub_zero k) (D.bivariantClass.cap t k α) =
        P.gysinCap (properPushforwardDescends C) k β)
    (hExt : ∀ β : CycleGroup C P.ambStructure (k + 1), Ext k (P.gysinCapZero k β) β)
    (β : CycleGroup C P.ambStructure (k + 1)) :
    chowGroupDegreeEquiv C
        (pullback.fst (modificationProjectionAtInfinity f b) t ≫
          (modificationProjectionAtInfinity f b ≫ f))
        (sub_zero k)
        (D.bivariantClass.cap t k
          (properChowPushforward C
            (pullback.fst (modificationProjectionAtInfinity f b) t ≫
              (modificationProjectionAtInfinity f b ≫ f))
            (t ≫ f) (pullback.snd (modificationProjectionAtInfinity f b) t)
            (pullbackSnd_comp_structureMorphism_eq C
              (modificationProjectionAtInfinity f b ≫ f) f
              (modificationProjectionAtInfinity f b) rfl t) k
            (properPushforwardDescends C _ _ _ _ _)
            (P.gysinCap (properPushforwardDescends C) k β))) =
      P.gysinCap (properPushforwardDescends C) k β := by
  rw [P.properChowPushforward_gysinCap rfl k β]
  exact hcap _ β (hExt β)

end Retraction

end Stacks.Chow

end
