module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Transport
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles
public import StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisor

/-!
# The Gysin class at infinity

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `X` be locally of
finite type over `S`. Let `b : W ⟶ 𝐏¹_X` be a proper morphism of schemes which is an isomorphism
over the standard affine chart `𝐀¹_X`, and write `i_∞ : W_∞ ⟶ W` for the inverse image of the
divisor at infinity. The Gysin lemma at infinity asserts that there is a canonical bivariant class
`C ∈ A⁰(W_∞ ⟶ X)` with `i_{∞,*}(C ∩ α) = i_{0,*} α` for every `α ∈ A_k(X)`, and that the same
identity holds after every base change along a morphism `X' ⟶ X` locally of finite type.

## Main definitions

* `Stacks.Chow.projectiveLineAffineChart` — the chart `𝐀¹_X ⟶ 𝐏¹_X` cut out by the
  polynomial-ring chart of `𝐏¹_ℤ`. The complement of the divisor at infinity is this chart, so
  "`b` is an isomorphism over `𝐀¹_X`" is `IsIso (pullback.snd b (projectiveLineAffineChart f))`.
* `Stacks.Chow.modificationProjection`, `Stacks.Chow.modificationFibreAtInfinity`,
  `Stacks.Chow.modificationInclusionAtInfinity`,
  `Stacks.Chow.modificationProjectionAtInfinity` — the structure morphism `W ⟶ X`, the fibre at
  infinity `W_∞ = W ×_{𝐏¹_X} X`, the inclusion `i_∞ : W_∞ ⟶ W` and the composite `W_∞ ⟶ X`.
* `Stacks.Chow.modificationSectionAtZero` — the zero section `i_0 : X ⟶ W`, obtained by
  inverting the projection of the fibre over zero, which is an isomorphism because `b` is one
  over `𝐀¹_X`.
* `Stacks.Chow.gysinCapOfLift` — the cap operation `C ∩ - : A_k(T) ⟶ A_k(W_∞ ×_X T)` as
  `i_∞^* ∘ lift`, for a given lift `A_k(T) ⟶ A_{k+1}(W ×_X T)` and a given presentation of the
  base-changed fibre at infinity as the zero scheme of a section of an invertible module.
* `Stacks.Chow.GysinAtInfinityData` — a degree-zero bivariant class for `W_∞ ⟶ X` together with
  the pushforward identity `i_{∞,*} ∘ (C ∩ -) = i_{0,*}` on every test scheme locally of finite
  type over `X`.

## Main results

* `Stacks.Chow.gysinCapOfLift_eq_of_gysin_pushforward_eq_zero` — two lifts differing by a class
  pushed forward from the fibre at infinity give the same cap operation, granted that the Gysin
  map kills such classes.
* `Stacks.Chow.GysinAtInfinityData.properPushforward_cap` — the degree-one normalisation of the
  class: pushing `C ∩ α` forward along `W_∞ ×_X T ⟶ T` returns `α`.
* `Stacks.Chow.GysinAtInfinityData.bivariantClass_eq_of_injective` — two classes with the
  characterising identity agree as soon as pushforward along the base-changed `i_∞` is injective.

## Implementation notes

`A⁰(W_∞ ⟶ X)` is
`BivariantClass C G (modificationProjectionAtInfinity f b ≫ f) f
  (modificationProjectionAtInfinity f b) rfl 0`,
where `G : Stacks.Chow.GysinSystem C` supplies the first Chern class rule and the vanishing used
by the Gysin maps.

`Stacks.Chow.gysinCapOfLift` takes the lift and the zero-scheme presentation of the base-changed
fibre at infinity as data. `Stacks.Chow.GysinAtInfinityData` records the class and its
characterising identity as fields, together with finite-type and properness facts about `W` and
`W_∞` over `X`; no inhabitant is constructed here. The identity
`i_{∞,*}(C ∩ α) = i_{0,*}α` determines `C ∩ α` only modulo the kernel of `i_{∞,*}`.

The proper-pushforward hypotheses `ProperPushforwardFactorsThroughRationalEquivalence` are
quantified throughout.

## References

* [Stacks Project, Tag 0F9J](https://stacks.math.columbia.edu/tag/0F9J)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 02S5](https://stacks.math.columbia.edu/tag/02S5)
* [Stacks Project, Tag 0GU8](https://stacks.math.columbia.edu/tag/0GU8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The affine chart of the relative projective line -/

/-- The standard affine chart `𝐀¹_X ⟶ 𝐏¹_X`, induced by the polynomial-ring chart of the
projective line over the integers. Its image is the complement of the divisor at infinity. -/
def projectiveLineAffineChart {X S : Scheme.{u}} (f : X ⟶ S) :
    affineLineOver X ⟶ projectiveLineProduct f := by
  let A : Scheme.{u} := Spec (.of (Polynomial (ULift.{u} ℤ)))
  let qX : affineLineOver X ⟶ X := pullback.fst (terminal.from X) (terminal.from A)
  let qA : affineLineOver X ⟶ A := pullback.snd (terminal.from X) (terminal.from A)
  let j : A ⟶ projectiveLine (ULift.{u} ℤ) := projectiveLineXChart (ULift.{u} ℤ)
  let m : affineLineOver X ⟶ relativeProjectiveLine S :=
    pullback.lift (qX ≫ f) (qA ≫ j) (by simp)
  refine pullback.lift qX m ?_
  change qX ≫ f = m ≫ pullback.fst _ _
  exact (pullback.lift_fst (qX ≫ f) (qA ≫ j) (by simp)).symm

/-! ### The geometry of a modification of the relative projective line -/

/-- The structure morphism `W ⟶ X` of a morphism `b : W ⟶ 𝐏¹_X`. -/
abbrev modificationProjection {X S W : Scheme.{u}} (f : X ⟶ S)
    (b : W ⟶ projectiveLineProduct f) : W ⟶ X :=
  b ≫ pullback.fst f (relativeProjectiveLine S ↘ S)

/-- The fibre at infinity `W_∞` of `b : W ⟶ 𝐏¹_X`: the inverse image of the divisor at
infinity. -/
abbrev modificationFibreAtInfinity {X S W : Scheme.{u}} (f : X ⟶ S)
    (b : W ⟶ projectiveLineProduct f) : Scheme.{u} :=
  pullback b (infinitySection f)

/-- The inclusion `i_∞ : W_∞ ⟶ W` of the fibre at infinity. -/
abbrev modificationInclusionAtInfinity {X S W : Scheme.{u}} (f : X ⟶ S)
    (b : W ⟶ projectiveLineProduct f) : modificationFibreAtInfinity f b ⟶ W :=
  pullback.fst b (infinitySection f)

/-- The structure morphism `W_∞ ⟶ X` of the fibre at infinity. -/
abbrev modificationProjectionAtInfinity {X S W : Scheme.{u}} (f : X ⟶ S)
    (b : W ⟶ projectiveLineProduct f) : modificationFibreAtInfinity f b ⟶ X :=
  modificationInclusionAtInfinity f b ≫ modificationProjection f b

/-- The projection `W_0 ⟶ X` of the fibre over zero. It is an isomorphism when `b` is an
isomorphism over `𝐀¹_X`. -/
abbrev modificationFibreAtZeroProjection {X S W : Scheme.{u}} (f : X ⟶ S)
    (b : W ⟶ projectiveLineProduct f) : pullback b (zeroSection f) ⟶ X :=
  pullback.snd b (zeroSection f)

/-- The section at zero `i_0 : X ⟶ W`, obtained by inverting the projection of the fibre over
zero. -/
def modificationSectionAtZero {X S W : Scheme.{u}} (f : X ⟶ S)
    (b : W ⟶ projectiveLineProduct f) (h : IsIso (modificationFibreAtZeroProjection f b)) :
    X ⟶ W := by
  letI : IsIso (modificationFibreAtZeroProjection f b) := h
  exact inv (modificationFibreAtZeroProjection f b) ≫ pullback.fst b (zeroSection f)

/-! ### Base change along a test scheme -/

/-- The base change `W ×_X T` of `W ⟶ X` along a morphism `g : T ⟶ X`. -/
abbrev modificationBaseChange {X S W T : Scheme.{u}} (f : X ⟶ S)
    (b : W ⟶ projectiveLineProduct f) (g : T ⟶ X) : Scheme.{u} :=
  pullback (modificationProjection f b) g

/-- The structure morphism of `W ×_X T` over the base. -/
abbrev modificationBaseChangeOver {X S W T : Scheme.{u}} (f : X ⟶ S)
    (b : W ⟶ projectiveLineProduct f) (g : T ⟶ X) : modificationBaseChange f b g ⟶ S :=
  pullback.fst (modificationProjection f b) g ≫ modificationProjection f b ≫ f

/-- The structure morphism of `W_∞ ×_X T` over the base. -/
abbrev modificationInfinityBaseChangeOver {X S W T : Scheme.{u}} (f : X ⟶ S)
    (b : W ⟶ projectiveLineProduct f) (g : T ⟶ X) :
    pullback (modificationProjectionAtInfinity f b) g ⟶ S :=
  pullback.fst (modificationProjectionAtInfinity f b) g ≫
    modificationProjectionAtInfinity f b ≫ f

/-- The base change of the inclusion at infinity, `W_∞ ×_X T ⟶ W ×_X T`. -/
def modificationInfinityBaseChange {X S W T : Scheme.{u}} (f : X ⟶ S)
    (b : W ⟶ projectiveLineProduct f) (g : T ⟶ X) :
    pullback (modificationProjectionAtInfinity f b) g ⟶ modificationBaseChange f b g :=
  pullback.lift
    (pullback.fst (modificationProjectionAtInfinity f b) g ≫
      modificationInclusionAtInfinity f b)
    (pullback.snd (modificationProjectionAtInfinity f b) g)
    (by rw [Category.assoc]; exact pullback.condition)

/-- The base change of the section at zero, `T ⟶ W ×_X T`. -/
def modificationSectionAtZeroBaseChange {X S W T : Scheme.{u}} (f : X ⟶ S)
    (b : W ⟶ projectiveLineProduct f) (h : IsIso (modificationFibreAtZeroProjection f b))
    (hzero : modificationSectionAtZero f b h ≫ modificationProjection f b = 𝟙 X)
    (g : T ⟶ X) : T ⟶ modificationBaseChange f b g :=
  pullback.lift (g ≫ modificationSectionAtZero f b h) (𝟙 T)
    (by rw [Category.assoc, hzero]; simp)

section Coherence

variable {X S W T : Scheme.{u}} (f : X ⟶ S) (b : W ⟶ projectiveLineProduct f) (g : T ⟶ X)

/-- The base-changed inclusion at infinity, followed by the projection to `W`, is the projection
to `W_∞` followed by `i_∞`. -/
@[simp]
theorem modificationInfinityBaseChange_comp_fst :
    modificationInfinityBaseChange f b g ≫ pullback.fst (modificationProjection f b) g =
      pullback.fst (modificationProjectionAtInfinity f b) g ≫
        modificationInclusionAtInfinity f b :=
  pullback.lift_fst _ _ _

/-- The base-changed inclusion at infinity lies over `T`. -/
@[simp]
theorem modificationInfinityBaseChange_comp_snd :
    modificationInfinityBaseChange f b g ≫ pullback.snd (modificationProjection f b) g =
      pullback.snd (modificationProjectionAtInfinity f b) g :=
  pullback.lift_snd _ _ _

/-- The base-changed inclusion at infinity is a morphism over the base. -/
theorem modificationInfinityBaseChange_over :
    modificationInfinityBaseChange f b g ≫ modificationBaseChangeOver f b g =
      modificationInfinityBaseChangeOver f b g := by
  rw [show modificationBaseChangeOver f b g =
      pullback.fst (modificationProjection f b) g ≫ modificationProjection f b ≫ f from rfl,
    ← Category.assoc, modificationInfinityBaseChange_comp_fst, Category.assoc]
  rfl

/-- The projection of `W_∞ ×_X T` to `T` is a morphism over the base. -/
theorem modificationInfinityBaseChange_snd_over :
    pullback.snd (modificationProjectionAtInfinity f b) g ≫ g ≫ f =
      modificationInfinityBaseChangeOver f b g :=
  (pullback.condition_assoc _).symm

/-- The projection of `W ×_X T` to `T` is a morphism over the base. -/
theorem modificationBaseChange_snd_over :
    pullback.snd (modificationProjection f b) g ≫ g ≫ f =
      modificationBaseChangeOver f b g :=
  (pullback.condition_assoc _).symm

/-- The base-changed section at zero is a section of the projection to `T`. -/
@[simp]
theorem modificationSectionAtZeroBaseChange_comp_snd
    (h : IsIso (modificationFibreAtZeroProjection f b))
    (hzero : modificationSectionAtZero f b h ≫ modificationProjection f b = 𝟙 X) :
    modificationSectionAtZeroBaseChange f b h hzero g ≫
        pullback.snd (modificationProjection f b) g = 𝟙 T :=
  pullback.lift_snd _ _ _

/-- The base-changed section at zero is a morphism over the base. -/
theorem modificationSectionAtZeroBaseChange_over
    (h : IsIso (modificationFibreAtZeroProjection f b))
    (hzero : modificationSectionAtZero f b h ≫ modificationProjection f b = 𝟙 X) :
    modificationSectionAtZeroBaseChange f b h hzero g ≫ modificationBaseChangeOver f b g =
      g ≫ f := by
  rw [← modificationBaseChange_snd_over, ← Category.assoc,
    modificationSectionAtZeroBaseChange_comp_snd, Category.id_comp]

/-- The composite of the base-changed inclusion at infinity with the projection to `T` is a
morphism over the base. -/
theorem modificationInfinityBaseChange_comp_snd_over :
    (modificationInfinityBaseChange f b g ≫ pullback.snd (modificationProjection f b) g) ≫
        g ≫ f = modificationInfinityBaseChangeOver f b g := by
  rw [modificationInfinityBaseChange_comp_snd, modificationInfinityBaseChange_snd_over]

/-- The composite of the base-changed section at zero with the projection to `T` is a morphism
over the base. -/
theorem modificationSectionAtZeroBaseChange_comp_snd_over
    (h : IsIso (modificationFibreAtZeroProjection f b))
    (hzero : modificationSectionAtZero f b h ≫ modificationProjection f b = 𝟙 X) :
    (modificationSectionAtZeroBaseChange f b h hzero g ≫
        pullback.snd (modificationProjection f b) g) ≫ g ≫ f = g ≫ f := by
  rw [modificationSectionAtZeroBaseChange_comp_snd, Category.id_comp]

end Coherence

/-! ### The cap operation of the class at infinity -/

section Construction

/-- The structure morphism over the base of the zero scheme of a global section `s` of an
invertible module on `W ×_X T`. -/
abbrev modificationZeroSchemeOver (C : ChowSituation.{u}) {X W T : Scheme.{u}} (f : X ⟶ C.S)
    (b : W ⟶ projectiveLineProduct f) (g : T ⟶ X)
    (L : (modificationBaseChange f b g).Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible (modificationBaseChange f b g).sheaf.obj
      (modificationBaseChange f b g).ringCatSheaf.property L]
    (s : Γ(L, ⊤)) :
    (Stacks.Divisors.zeroScheme (modificationBaseChange f b g) L s).subscheme ⟶ C.S :=
  (Stacks.Divisors.zeroScheme (modificationBaseChange f b g) L s).subschemeι ≫
    modificationBaseChangeOver f b g

/-- The cap operation `C ∩ - : A_k(T) ⟶ A_k(W_∞ ×_X T)` built
from a choice of lift: given a homomorphism `lift : A_k(T) ⟶ A_{k+1}(W ×_X T)` and a presentation
of the base-changed fibre at infinity as the zero scheme of a global section `s` of an invertible
module `L` on `W ×_X T`, it is `i_∞^* ∘ lift`, where `i_∞^*` is the Gysin map of `s` followed by
the identification `e` of that zero scheme with `W_∞ ×_X T`. -/
@[stacks 0F9J "construction of the cap operation from a lift and a zero-scheme presentation"]
def gysinCapOfLift (C : ChowSituation.{u}) (G : GysinSystem C) {X W T : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (b : W ⟶ projectiveLineProduct f)
    [LocallyOfFiniteType (modificationProjection f b)]
    [LocallyOfFiniteType (modificationProjectionAtInfinity f b)]
    (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
    (L : (modificationBaseChange f b g).Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible (modificationBaseChange f b g).sheaf.obj
      (modificationBaseChange f b g).ringCatSheaf.property L]
    (s : Γ(L, ⊤))
    (e : (Stacks.Divisors.zeroScheme (modificationBaseChange f b g) L s).subscheme ≅
      pullback (modificationProjectionAtInfinity f b) g)
    (he : e.hom ≫ modificationInfinityBaseChangeOver f b g =
      modificationZeroSchemeOver C f b g L s)
    (lift : chowGroup C (g ≫ f) k →+ chowGroup C (modificationBaseChangeOver f b g) (k + 1)) :
    chowGroup C (g ≫ f) k →+ chowGroup C (modificationInfinityBaseChangeOver f b g) k :=
  (chowPushforwardOfIso C (modificationZeroSchemeOver C f b g L s)
        (modificationInfinityBaseChangeOver f b g) e.hom he k).comp
    ((G.onChow (modificationBaseChangeOver f b g) L s k).comp lift)

/-- The value of the constructed cap operation on a class. -/
theorem gysinCapOfLift_apply (C : ChowSituation.{u}) (G : GysinSystem C) {X W T : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (b : W ⟶ projectiveLineProduct f)
    [LocallyOfFiniteType (modificationProjection f b)]
    [LocallyOfFiniteType (modificationProjectionAtInfinity f b)]
    (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
    (L : (modificationBaseChange f b g).Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible (modificationBaseChange f b g).sheaf.obj
      (modificationBaseChange f b g).ringCatSheaf.property L]
    (s : Γ(L, ⊤))
    (e : (Stacks.Divisors.zeroScheme (modificationBaseChange f b g) L s).subscheme ≅
      pullback (modificationProjectionAtInfinity f b) g)
    (he : e.hom ≫ modificationInfinityBaseChangeOver f b g =
      modificationZeroSchemeOver C f b g L s)
    (lift : chowGroup C (g ≫ f) k →+ chowGroup C (modificationBaseChangeOver f b g) (k + 1))
    (α : chowGroup C (g ≫ f) k) :
    gysinCapOfLift C G f b g k L s e he lift α =
      chowPushforwardOfIso C (modificationZeroSchemeOver C f b g L s)
        (modificationInfinityBaseChangeOver f b g) e.hom he k
        (G.onChow (modificationBaseChangeOver f b g) L s k (lift α)) :=
  rfl

/-- Two lifts whose difference is pushed forward from the fibre at infinity give the same cap
operation, as soon as the Gysin map of `s` kills everything pushed forward from the fibre at
infinity. -/
@[stacks 0F9J "independence of the chosen lift"]
theorem gysinCapOfLift_eq_of_gysin_pushforward_eq_zero (C : ChowSituation.{u})
    (G : GysinSystem C) {X W T : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (b : W ⟶ projectiveLineProduct f) [LocallyOfFiniteType (modificationProjection f b)]
    [LocallyOfFiniteType (modificationProjectionAtInfinity f b)]
    (g : T ⟶ X) [LocallyOfFiniteType g] [IsProper (modificationInfinityBaseChange f b g)]
    (k : ℤ) (L : (modificationBaseChange f b g).Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible (modificationBaseChange f b g).sheaf.obj
      (modificationBaseChange f b g).ringCatSheaf.property L]
    (s : Γ(L, ⊤))
    (e : (Stacks.Divisors.zeroScheme (modificationBaseChange f b g) L s).subscheme ≅
      pullback (modificationProjectionAtInfinity f b) g)
    (he : e.hom ≫ modificationInfinityBaseChangeOver f b g =
      modificationZeroSchemeOver C f b g L s)
    (lift lift' : chowGroup C (g ≫ f) k →+
      chowGroup C (modificationBaseChangeOver f b g) (k + 1))
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C
      (modificationInfinityBaseChangeOver f b g) (modificationBaseChangeOver f b g)
      (modificationInfinityBaseChange f b g) (modificationInfinityBaseChange_over f b g) (k + 1))
    (hvanish : ∀ γ : chowGroup C (modificationInfinityBaseChangeOver f b g) (k + 1),
      G.onChow (modificationBaseChangeOver f b g) L s k
        (properChowPushforward C (modificationInfinityBaseChangeOver f b g)
          (modificationBaseChangeOver f b g) (modificationInfinityBaseChange f b g)
          (modificationInfinityBaseChange_over f b g) (k + 1) hfac γ) = 0)
    (hdiff : ∀ α : chowGroup C (g ≫ f) k,
      ∃ γ : chowGroup C (modificationInfinityBaseChangeOver f b g) (k + 1),
        lift α - lift' α =
          properChowPushforward C (modificationInfinityBaseChangeOver f b g)
            (modificationBaseChangeOver f b g) (modificationInfinityBaseChange f b g)
            (modificationInfinityBaseChange_over f b g) (k + 1) hfac γ) :
    gysinCapOfLift C G f b g k L s e he lift =
      gysinCapOfLift C G f b g k L s e he lift' := by
  refine AddMonoidHom.ext fun α ↦ ?_
  obtain ⟨γ, hγ⟩ := hdiff α
  rw [gysinCapOfLift_apply, gysinCapOfLift_apply, sub_eq_iff_eq_add'.mp hγ, map_add, hvanish γ,
    add_zero]

end Construction

/-! ### The canonical class at infinity -/

/-- The conclusion of the Gysin-at-infinity lemma, for a proper morphism
`b : W ⟶ 𝐏¹_X` which is an isomorphism over the standard affine chart `𝐀¹_X`: a degree-zero
bivariant class `C ∈ A⁰(W_∞ ⟶ X)` for the fibre at infinity, together with the identity
`i_{∞,*}(C ∩ α) = i_{0,*} α` on every test scheme locally of finite type over `X`. -/
@[stacks 0F9J "statement: the canonical class in A⁰(W_∞ ⟶ X) and its pushforward identity"]
structure GysinAtInfinityData (C : ChowSituation.{u}) (G : GysinSystem C) {X W : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (b : W ⟶ projectiveLineProduct f) [IsProper b]
    (_hA : IsIso (pullback.snd b (projectiveLineAffineChart f))) where
  /-- `W` is locally of finite type over `X`. -/
  finiteTypeModification : LocallyOfFiniteType (modificationProjection f b)
  /-- `W_∞` is locally of finite type over `X`. -/
  finiteTypeInfinity : LocallyOfFiniteType (modificationProjectionAtInfinity f b)
  /-- `W` is proper over `X`. -/
  properModification : IsProper (modificationProjection f b)
  /-- `W_∞` is proper over `X`. -/
  properProjectionAtInfinity : IsProper (modificationProjectionAtInfinity f b)
  /-- The fibre over zero is canonically `X`, because `b` is an isomorphism over `𝐀¹_X`. -/
  isIsoFibreAtZero : IsIso (modificationFibreAtZeroProjection f b)
  /-- The section at zero is a section of `W ⟶ X`. -/
  sectionAtZero_comp :
    modificationSectionAtZero f b isIsoFibreAtZero ≫ modificationProjection f b = 𝟙 X
  /-- Every base change of the inclusion at infinity is proper. -/
  properInclusionAtInfinity : ∀ {T : Scheme.{u}} (g : T ⟶ X),
    IsProper (modificationInfinityBaseChange f b g)
  /-- Every base change of the section at zero is proper. -/
  properSectionAtZero : ∀ {T : Scheme.{u}} (g : T ⟶ X),
    IsProper (modificationSectionAtZeroBaseChange f b isIsoFibreAtZero sectionAtZero_comp g)
  /-- The canonical degree-zero bivariant class `C ∈ A⁰(W_∞ ⟶ X)`. -/
  bivariantClass :
    letI := finiteTypeInfinity
    BivariantClass C G (modificationProjectionAtInfinity f b ≫ f) f
      (modificationProjectionAtInfinity f b) rfl 0
  /-- The characterising identity `i_{∞,*}(C ∩ α) = i_{0,*} α`, on every test scheme locally of
  finite type over `X`. -/
  pushforward_formula :
    letI := finiteTypeModification
    letI := finiteTypeInfinity
    ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ),
      letI := properInclusionAtInfinity g
      letI := properSectionAtZero g
      ∀ (hfacInf : ProperPushforwardFactorsThroughRationalEquivalence C
          (modificationInfinityBaseChangeOver f b g) (modificationBaseChangeOver f b g)
          (modificationInfinityBaseChange f b g)
          (modificationInfinityBaseChange_over f b g) k)
        (hfacZero : ProperPushforwardFactorsThroughRationalEquivalence C (g ≫ f)
          (modificationBaseChangeOver f b g)
          (modificationSectionAtZeroBaseChange f b isIsoFibreAtZero sectionAtZero_comp g)
          (modificationSectionAtZeroBaseChange_over f b g isIsoFibreAtZero sectionAtZero_comp)
          k)
        (α : chowGroup C (g ≫ f) k),
        properChowPushforward C (modificationInfinityBaseChangeOver f b g)
            (modificationBaseChangeOver f b g) (modificationInfinityBaseChange f b g)
            (modificationInfinityBaseChange_over f b g) k hfacInf
            (Eq.mp (congrArg (chowGroup C (modificationInfinityBaseChangeOver f b g))
              (sub_zero k)) (bivariantClass.cap g k α)) =
          properChowPushforward C (g ≫ f) (modificationBaseChangeOver f b g)
            (modificationSectionAtZeroBaseChange f b isIsoFibreAtZero sectionAtZero_comp g)
            (modificationSectionAtZeroBaseChange_over f b g isIsoFibreAtZero sectionAtZero_comp)
            k hfacZero α


namespace GysinAtInfinityData

variable {C : ChowSituation.{u}} {G : GysinSystem C} {X W : Scheme.{u}} {f : X ⟶ C.S}
  [LocallyOfFiniteType f] {b : W ⟶ projectiveLineProduct f} [IsProper b]
  {hA : IsIso (pullback.snd b (projectiveLineAffineChart f))}

section Consequences

variable (D : GysinAtInfinityData C G f b hA)
  [IsProper (modificationProjection f b)] [IsProper (modificationProjectionAtInfinity f b)]
  {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g]
  [IsProper (modificationInfinityBaseChange f b g)]
  [IsProper (modificationSectionAtZeroBaseChange f b D.isIsoFibreAtZero D.sectionAtZero_comp g)]
  (k : ℤ)

/-- The degree-one normalisation of the class at infinity: pushing `C ∩ α` forward along
`W_∞ ×_X T ⟶ T` returns `α`. -/
theorem properPushforward_cap
    (hfacInf : ProperPushforwardFactorsThroughRationalEquivalence C
      (modificationInfinityBaseChangeOver f b g) (modificationBaseChangeOver f b g)
      (modificationInfinityBaseChange f b g) (modificationInfinityBaseChange_over f b g) k)
    (hfacZero : ProperPushforwardFactorsThroughRationalEquivalence C (g ≫ f)
      (modificationBaseChangeOver f b g)
      (modificationSectionAtZeroBaseChange f b D.isIsoFibreAtZero D.sectionAtZero_comp g)
      (modificationSectionAtZeroBaseChange_over f b g D.isIsoFibreAtZero D.sectionAtZero_comp) k)
    (hfacProj : ProperPushforwardFactorsThroughRationalEquivalence C
      (modificationBaseChangeOver f b g) (g ≫ f)
      (pullback.snd (modificationProjection f b) g) (modificationBaseChange_snd_over f b g) k)
    (hfacSnd : ProperPushforwardFactorsThroughRationalEquivalence C
      (modificationInfinityBaseChangeOver f b g) (g ≫ f)
      (pullback.snd (modificationProjectionAtInfinity f b) g)
      (modificationInfinityBaseChange_snd_over f b g) k)
    (hfacId : ProperPushforwardFactorsThroughRationalEquivalence C (g ≫ f) (g ≫ f) (𝟙 T)
      (Category.id_comp (g ≫ f)) k)
    (α : chowGroup C (g ≫ f) k) :
    properChowPushforward C (modificationInfinityBaseChangeOver f b g) (g ≫ f)
        (pullback.snd (modificationProjectionAtInfinity f b) g)
        (modificationInfinityBaseChange_snd_over f b g) k hfacSnd
        (Eq.mp (congrArg (chowGroup C (modificationInfinityBaseChangeOver f b g)) (sub_zero k))
          (D.bivariantClass.cap g k α)) = α := by
  have hhom :
      properChowPushforward C (modificationInfinityBaseChangeOver f b g) (g ≫ f)
          (pullback.snd (modificationProjectionAtInfinity f b) g)
          (modificationInfinityBaseChange_snd_over f b g) k hfacSnd =
        (properChowPushforward C (modificationBaseChangeOver f b g) (g ≫ f)
            (pullback.snd (modificationProjection f b) g)
            (modificationBaseChange_snd_over f b g) k hfacProj).comp
          (properChowPushforward C (modificationInfinityBaseChangeOver f b g)
            (modificationBaseChangeOver f b g) (modificationInfinityBaseChange f b g)
            (modificationInfinityBaseChange_over f b g) k hfacInf) := by
    rw [properChowPushforward_comp C (modificationInfinityBaseChangeOver f b g)
      (modificationBaseChangeOver f b g) (g ≫ f) (modificationInfinityBaseChange f b g)
      (pullback.snd (modificationProjection f b) g)
      (modificationInfinityBaseChange_over f b g) (modificationBaseChange_snd_over f b g) k
      hfacInf hfacProj]
    exact properChowPushforward_congr C (modificationInfinityBaseChangeOver f b g) (g ≫ f)
      (pullback.snd (modificationProjectionAtInfinity f b) g)
      (modificationInfinityBaseChange f b g ≫ pullback.snd (modificationProjection f b) g)
      (modificationInfinityBaseChange_comp_snd f b g).symm
      (modificationInfinityBaseChange_snd_over f b g)
      (modificationInfinityBaseChange_comp_snd_over f b g) k hfacSnd _
  rw [hhom, AddMonoidHom.comp_apply, D.pushforward_formula g k hfacInf hfacZero α,
    ← AddMonoidHom.comp_apply,
    properChowPushforward_comp C (g ≫ f) (modificationBaseChangeOver f b g) (g ≫ f)
      (modificationSectionAtZeroBaseChange f b D.isIsoFibreAtZero D.sectionAtZero_comp g)
      (pullback.snd (modificationProjection f b) g)
      (modificationSectionAtZeroBaseChange_over f b g D.isIsoFibreAtZero D.sectionAtZero_comp)
      (modificationBaseChange_snd_over f b g) k hfacZero hfacProj,
    properChowPushforward_congr C (g ≫ f) (g ≫ f)
      (modificationSectionAtZeroBaseChange f b D.isIsoFibreAtZero D.sectionAtZero_comp g ≫
        pullback.snd (modificationProjection f b) g) (𝟙 T)
      (modificationSectionAtZeroBaseChange_comp_snd f b g D.isIsoFibreAtZero
        D.sectionAtZero_comp)
      (modificationSectionAtZeroBaseChange_comp_snd_over f b g D.isIsoFibreAtZero
        D.sectionAtZero_comp)
      (Category.id_comp (g ≫ f)) k _ hfacId,
    properChowPushforward_id C (g ≫ f) k hfacId]
  rfl

end Consequences

/-- Two classes satisfying the characterising identity of `Stacks.Chow.GysinAtInfinityData` agree
as soon as proper pushforward along the base-changed inclusion at infinity is injective. -/
theorem bivariantClass_eq_of_injective (D D' : GysinAtInfinityData C G f b hA)
    [LocallyOfFiniteType (modificationProjection f b)]
    [LocallyOfFiniteType (modificationProjectionAtInfinity f b)]
    (hfacInf : ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ),
      letI := D.properInclusionAtInfinity g
      ProperPushforwardFactorsThroughRationalEquivalence C
        (modificationInfinityBaseChangeOver f b g) (modificationBaseChangeOver f b g)
        (modificationInfinityBaseChange f b g) (modificationInfinityBaseChange_over f b g) k)
    (hfacZero : ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ),
      letI := D.properSectionAtZero g
      ProperPushforwardFactorsThroughRationalEquivalence C (g ≫ f)
        (modificationBaseChangeOver f b g)
        (modificationSectionAtZeroBaseChange f b D.isIsoFibreAtZero D.sectionAtZero_comp g)
        (modificationSectionAtZeroBaseChange_over f b g D.isIsoFibreAtZero D.sectionAtZero_comp)
        k)
    (hinj : ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ),
      letI := D.properInclusionAtInfinity g
      ∀ (hfac : ProperPushforwardFactorsThroughRationalEquivalence C
          (modificationInfinityBaseChangeOver f b g) (modificationBaseChangeOver f b g)
          (modificationInfinityBaseChange f b g) (modificationInfinityBaseChange_over f b g) k)
        (y z : chowGroup C (modificationInfinityBaseChangeOver f b g) k),
        properChowPushforward C (modificationInfinityBaseChangeOver f b g)
            (modificationBaseChangeOver f b g) (modificationInfinityBaseChange f b g)
            (modificationInfinityBaseChange_over f b g) k hfac y =
          properChowPushforward C (modificationInfinityBaseChangeOver f b g)
            (modificationBaseChangeOver f b g) (modificationInfinityBaseChange f b g)
            (modificationInfinityBaseChange_over f b g) k hfac z → y = z) :
    D.bivariantClass = D'.bivariantClass := by
  apply BivariantClass.ext
  intro T g hg k α
  have := D.properInclusionAtInfinity g
  have := D.properSectionAtZero g
  have h1 := D.pushforward_formula g k (hfacInf g k) (hfacZero g k) α
  have h2 := D'.pushforward_formula g k (hfacInf g k) (hfacZero g k) α
  exact (cast_inj _).mp (hinj g k (hfacInf g k) _ _ (h1.trans h2.symm))

end GysinAtInfinityData

end Stacks.Chow

end
