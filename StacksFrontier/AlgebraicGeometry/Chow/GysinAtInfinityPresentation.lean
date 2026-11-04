module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Commuting
public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinity

/-!
# The construction of the Gysin class at infinity, as a presentation of its cap operation

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, let `b : W ⟶ 𝐏¹_X` be proper and an isomorphism over the affine chart
`𝐀¹_X`, and let `C ∈ A⁰(W_∞ ⟶ X)` be the class at infinity, carried by
`Stacks.Chow.GysinAtInfinityData`. The class is constructed by `C ∩ α = i_∞^* β`, where
`β ∈ CH_{k+1}(W ×_X T)` restricts over `𝐀¹` to the flat pullback of `α`; this module records
such a factorisation of the cap operation of `C` as the composite of a lift `α ↦ β` with the
Gysin map `i_∞^*` of the divisor at infinity.

## Main definitions

* `Stacks.Chow.GysinAtInfinityCapPresentation`: for every test scheme `g : T ⟶ X` locally of
  finite type and every degree, a lift `CH_k(T) ⟶ CH_{k+1}(W ×_X T)` and a Gysin step
  `CH_{k+1}(W ×_X T) ⟶ CH_k(W_∞ ×_X T)` whose composite is the cap operation of `C`.
* `Stacks.Chow.GysinAtInfinityCapPresentation.ofGysinCapOfLift`: the presentation given by an
  invertible module with a section whose zero scheme is `W_∞ ×_X T`, and a lift, when the cap
  operation of `C` is the resulting `Stacks.Chow.gysinCapOfLift`.

## Main results

* `Stacks.Chow.GysinAtInfinityCapPresentation.cap_apply`: the cap operation of `C` is the Gysin
  step applied to the lift.
* `Stacks.Chow.GysinAtInfinityCapPresentation.gysinStep_lift_eq`: the Gysin step applied to the
  lift is the cap operation of `C`, in degree `k`.

## References

* [Stacks Project, Tag 0F9J](https://stacks.math.columbia.edu/tag/0F9J)
* [Stacks Project, Tag 0FAS](https://stacks.math.columbia.edu/tag/0FAS)
* [Stacks Project, Tag 0GUH](https://stacks.math.columbia.edu/tag/0GUH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- A presentation of the cap operation of the Gysin class at infinity `C ∈ A⁰(W_∞ ⟶ X)` as
the composite of a lift with the Gysin map of the divisor at infinity: on every test scheme
`g : T ⟶ X` locally of finite type and in every degree `k`, additive maps
`lift : CH_k(T) ⟶ CH_{k+1}(W ×_X T)` and `gysinStep : CH_{k+1}(W ×_X T) ⟶ CH_k(W_∞ ×_X T)`
with `C ∩ α = gysinStep (lift α)`. -/
@[stacks 0F9J "the construction of the class at infinity, as a presentation of its cap operation \
by a lift and a Gysin step"]
structure GysinAtInfinityCapPresentation (C : ChowSituation.{u}) (G : GysinSystem C)
    {X W : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (b : W ⟶ projectiveLineProduct f) [IsProper b]
    (hA : IsIso (pullback.snd b (projectiveLineAffineChart f)))
    [LocallyOfFiniteType (modificationProjection f b)]
    [LocallyOfFiniteType (modificationProjectionAtInfinity f b)]
    (D : GysinAtInfinityData C G f b hA) where
  /-- The lift `α ↦ β`: a class on `W ×_X T` one degree up. -/
  lift : ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ),
    chowGroup C (g ≫ f) k →+ chowGroup C (modificationBaseChangeOver f b g) (k + 1)
  /-- The Gysin map `i_∞^*` of the divisor at infinity, on the base change by the test scheme. -/
  gysinStep : ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ),
    chowGroup C (modificationBaseChangeOver f b g) (k + 1) →+
      chowGroup C (modificationInfinityBaseChangeOver f b g) k
  /-- The cap operation of `C` is the Gysin step applied to the lift. -/
  cap_eq : ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
      (α : chowGroup C (g ≫ f) k),
    D.bivariantClass.cap g k α =
      chowGroupDegreeEquiv C (modificationInfinityBaseChangeOver f b g) (sub_zero k).symm
        (gysinStep g k (lift g k α))

namespace GysinAtInfinityCapPresentation

variable {C : ChowSituation.{u}} {G : GysinSystem C} {X W : Scheme.{u}} {f : X ⟶ C.S}
  [LocallyOfFiniteType f] {b : W ⟶ projectiveLineProduct f} [IsProper b]
  {hA : IsIso (pullback.snd b (projectiveLineAffineChart f))}
  [LocallyOfFiniteType (modificationProjection f b)]
  [LocallyOfFiniteType (modificationProjectionAtInfinity f b)]
  {D : GysinAtInfinityData C G f b hA}

/-- The cap operation of `C` is the Gysin step applied to the lift, transported from degree `k`
to degree `k - 0`. -/
theorem cap_apply (P : GysinAtInfinityCapPresentation C G f b hA D) {T : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ f) k) :
    D.bivariantClass.cap g k α =
      chowGroupDegreeEquiv C (modificationInfinityBaseChangeOver f b g) (sub_zero k).symm
        (P.gysinStep g k (P.lift g k α)) :=
  P.cap_eq g k α

/-- The Gysin step applied to the lift is the cap operation of `C`, transported from degree
`k - 0` to degree `k`. -/
theorem gysinStep_lift_eq (P : GysinAtInfinityCapPresentation C G f b hA D) {T : Scheme.{u}}
    (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ f) k) :
    P.gysinStep g k (P.lift g k α) =
      chowGroupDegreeEquiv C (modificationInfinityBaseChangeOver f b g) (sub_zero k)
        (D.bivariantClass.cap g k α) := by
  rw [P.cap_eq g k α, chowGroupDegreeEquiv_chowGroupDegreeEquiv]
  rfl

end GysinAtInfinityCapPresentation

/-- The presentation of the cap operation of `C` given, on every test scheme `g : T ⟶ X`, by an
invertible module `L` with a global section `s` on `W ×_X T`, an identification `e` of the zero
scheme of `s` with `W_∞ ×_X T` over the base, and a lift, provided the cap operation of `C` is the
resulting `Stacks.Chow.gysinCapOfLift`. The Gysin step is the Gysin map of `s` pushed forward
along `e`. -/
def GysinAtInfinityCapPresentation.ofGysinCapOfLift (C : ChowSituation.{u}) (G : GysinSystem C)
    {X W : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (b : W ⟶ projectiveLineProduct f) [IsProper b]
    (hA : IsIso (pullback.snd b (projectiveLineAffineChart f)))
    [LocallyOfFiniteType (modificationProjection f b)]
    [LocallyOfFiniteType (modificationProjectionAtInfinity f b)]
    (D : GysinAtInfinityData C G f b hA)
    (L : ∀ {T : Scheme.{u}} (g : T ⟶ X), [LocallyOfFiniteType g] →
      (modificationBaseChange f b g).Modules)
    (hL : ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g],
      AlgebraicGeometry.SheafOfModules.IsInvertible (modificationBaseChange f b g).sheaf.obj
        (modificationBaseChange f b g).ringCatSheaf.property (L g))
    (s : ∀ {T : Scheme.{u}} (g : T ⟶ X), [LocallyOfFiniteType g] → Γ(L g, ⊤))
    (e : ∀ {T : Scheme.{u}} (g : T ⟶ X), [LocallyOfFiniteType g] →
      (Stacks.Divisors.zeroScheme (modificationBaseChange f b g) (L g) (s g)).subscheme ≅
        pullback (modificationProjectionAtInfinity f b) g)
    (he : ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g],
      (e g).hom ≫ modificationInfinityBaseChangeOver f b g =
        modificationZeroSchemeOver C f b g (L g) (s g))
    (lift : ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ),
      chowGroup C (g ≫ f) k →+ chowGroup C (modificationBaseChangeOver f b g) (k + 1))
    (hcap : ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
        (α : chowGroup C (g ≫ f) k),
      D.bivariantClass.cap g k α =
        chowGroupDegreeEquiv C (modificationInfinityBaseChangeOver f b g) (sub_zero k).symm
          (letI := hL g
          gysinCapOfLift C G f b g k (L g) (s g) (e g) (he g) (lift g k) α)) :
    GysinAtInfinityCapPresentation C G f b hA D where
  lift := lift
  gysinStep g _ k :=
    letI := hL g
    (chowPushforwardOfIso C (modificationZeroSchemeOver C f b g (L g) (s g))
        (modificationInfinityBaseChangeOver f b g) (e g).hom (he g) k).comp
      (G.onChow (modificationBaseChangeOver f b g) (L g) (s g) k)
  cap_eq g _ k α := hcap g k α

end Stacks.Chow

end
