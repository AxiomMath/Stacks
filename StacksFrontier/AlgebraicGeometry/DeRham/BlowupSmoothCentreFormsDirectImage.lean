module

public import StacksFrontier.AlgebraicGeometry.Blowup.CartierCentre
public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalDifferentials
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesComparison
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.BaseChange
public import StacksFrontier.AlgebraicGeometry.Divisors.IdealSheafSections
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctors.IsomorphismLimit
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SmoothClosedImmersionCoordinates
public import StacksCore.Tactic.StacksAttribute

/-!
# Blowing up a smooth centre and the direct image of differential forms

Let `S` be a scheme, let `f : X ⟶ S` be smooth and let `i : Z ⟶ X` be a closed immersion with
`Z` smooth over `S` as well.  Write `b : X' ⟶ X` for the blowing up of `X` along `Z`, write
`E ⊆ X'` for its exceptional divisor and write `p : E ⟶ Z` for the structure morphism of `E`
over the centre.  **[Stacks, Tag 0FUU] asserts, for every `a ≥ 0`:**

1. `Ω^a_{X/S} ⟶ b_*Ω^a_{X'/S}` is an isomorphism;
2. `Ω^a_{Z/S} ⟶ p_*Ω^a_{E/S}` is an isomorphism;
3. `Rb_*Ω^a_{X'/S} ⟶ i_*Rp_*Ω^a_{E/S}` is an isomorphism on cohomology sheaves in degree `≥ 1`.

This file carries clauses (1) and (2).  What it proves is the reduction of the source's proof to
the local model: invertibility of either comparison is local on the target, the étale-local
structure of a closed immersion of smooth schemes ([Stacks, Tag 0FUE]) puts every point of `X`
in an open on which the situation is the flat pullback of the coordinate situation
`𝐀^m_S ⊆ 𝐀^{m+n}_S`, and away from the centre the blowing-up morphism is an isomorphism, which
settles the comparison there.  Clause (3) is not treated; see the implementation notes.

## Main definitions

* `Stacks.DeRham.blowupFormsDirectImage`: the comparison map `Ω^a_{X/S} ⟶ b_*Ω^a_{X'/S}` of
  clause (1), the adjoint transpose of the canonical map
  `AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsMap` of the square cut out by `b`.
* `Stacks.DeRham.exceptionalFormsDirectImage`: the comparison map `Ω^a_{Z/S} ⟶ p_*Ω^a_{E/S}` of
  clause (2), the adjoint transpose of the canonical map of the square cut out by `p`.
* `Stacks.DeRham.BlowupFormsFlatBaseChange` and
  `Stacks.DeRham.ExceptionalFormsFlatBaseChange`: flat base change for the two comparison maps,
  stated as an explicit input of the reduction below.
* `Stacks.DeRham.LocalModelBlowupForms` and `Stacks.DeRham.LocalModelExceptionalForms`: clauses
  (1) and (2) of [Stacks, Tag 0FUR] for the coordinate situation, likewise an explicit input.

## Main results

* `Stacks.DeRham.isIso_formsDirectImage_of_smooth`: the etale-local REDUCTION of clauses (1)
  and (2) of [Stacks, Tag 0FUU] to the four inputs above.  It bears no tag attribute, because it
  does not prove the tag; it reduces it.
* `Stacks.DeRham.isIso_formsDirectImage_of_isEffectiveCartierDivisor`: **[Stacks, Tag 0FUU],
  clauses (1) and (2) for a centre whose ideal sheaf is an effective Cartier divisor** — for a
  closed immersion of smooth `S`-schemes, the centres of codimension one.  Proved
  unconditionally, and for the degenerate reason: such a centre is unchanged by blowing up, so
  `b` is an isomorphism and `p` is its base change along `i`.  A centre of codimension two or
  more is not covered.
* `Stacks.DeRham.isIso_blowupFormsDirectImage_of_isIso_blowUpToBase` and
  `Stacks.DeRham.isIso_exceptionalFormsDirectImage_of_isIso_exceptionalToCentre`: where the
  blowing-up morphism, respectively the structure morphism of the exceptional divisor over the
  centre, is an isomorphism, the comparison of clause (1), respectively clause (2), is an
  isomorphism.  These are the degenerate half of the covering argument, and they are proved
  unconditionally.

## Implementation notes

**What is proved.** Both comparisons are morphisms of sheaves of modules, so their invertibility
is local on the target, by
`AlgebraicGeometry.Scheme.Modules.isIso_of_isIso_pullback_ι`.  Clause (2) lives on `Z` and the
opens `i⁻¹U` of [Stacks, Tag 0FUE] cover `Z`, so the chart step alone suffices there.  Clause (1)
lives on `X`, where those opens cover only the centre; the complement of the image of `i` is
covered by one further open, on which the inverse-image ideal is the unit ideal, hence an
effective Cartier divisor, hence the blowing-up morphism is an isomorphism ([Stacks, Tag 0807])
and the comparison is the unit of the pullback–direct image adjunction of an isomorphism composed
with an invertible map.  On a chart the situation is the pullback of the coordinate situation
along an étale, hence flat, morphism, and the carried base-change hypothesis turns clause (1) or
(2) for the coordinate situation into the same clause for the chart.

**Which descent the argument uses.** The source argues étale-locally: it chooses a surjective
étale `ε : X₁ ⟶ X`, base-changes the whole situation, and descends invertibility along `ε`
because `ε` is a flat surjection.  Organised chart by chart the descent needed is only the
Zariski one: [Stacks, Tag 0FUE] supplies an *open* `U ⊆ X` together with an étale morphism
`U ⟶ 𝐀^{m+n}_S`, and the coordinate situation's own statement is *pulled back* along that
morphism rather than descended along it — the pullback of an isomorphism is an isomorphism, with
no hypothesis on the morphism beyond what the base-change identification already needs.  So
`AlgebraicGeometry.Scheme.Modules.isIso_of_isIso_pullback_of_flat_surjective` is not used here;
the opens `U` cover `X`, and `isIso_of_isIso_pullback_ι` is the only descent step.

**What is carried, and why.**

* `LocalModelBlowupForms` and `LocalModelExceptionalForms` are clauses (1) and (2) of
  [Stacks, Tag 0FUR] — the computation in the coordinate situation
  `𝐀^m_S ⊆ 𝐀^{m+n}_S` — for all `m`, `n` and all bases `S`.  The library has clause (1) only for
  `n = 1`, where the centre is an effective Cartier divisor and the blowing-up morphism is an
  isomorphism (`Stacks.DeRham.isIso_coordinateBlowupToAmbient_one`), and clause (2) only for
  `n = 1` or `a = 0`; the general computation, which is the content of Section 50.16 of the
  source, is not available.  They are carried in the coordinate form rather than in the
  projective-bundle form of [Stacks, Tag 0FUT] clause (2), so that no identification of the
  exceptional divisor with `𝐏(ℐ/ℐ²)` is needed and nothing of Tag 0FUT is assumed.
* `BlowupFormsFlatBaseChange` and `ExceptionalFormsFlatBaseChange` are flat base change for the
  direct image appearing in the two comparisons: for a flat `ε : X₁ ⟶ X` and the base change
  `i₁ : Z₁ ⟶ X₁` of the centre, the inverse image along `ε` of `b_*Ω^a_{X'/S}` is
  `b₁_*Ω^a_{X₁'/S}`, compatibly with the comparison maps.  A base-change map for the direct image
  of a sheaf of modules does exist, as `Stacks.AlgebraicGeometry.FlatBaseChange
  .pushforwardBaseChange`, and `isIso_pushforwardBaseChange_of_isAffine` proves it invertible over
  an AFFINE base; what is unavailable is that statement in the non-affine chart situation here,
  together with its compatibility with the comparison maps.  [Stacks, Tag 0805] base-changes the
  *blowup*, not the direct image of a module on it.  Each hypothesis is therefore stated as the
  existence of the two identifications together
  with the commuting square they sit in, which is the shape in which the source's reduction uses
  flat base change.  The identifications are asserted only to exist, not to be canonical: the
  conclusion drawn from them — invertibility of a map isomorphic to an invertible one — does not
  see the difference.

**Which blowup.**  The library carries two constructions of the blowup of `X` in an ideal sheaf,
canonically isomorphic over `X` by `AlgebraicGeometry.blowUpIso_hom_blowUpToBase`:
`AlgebraicGeometry.blowUp`, the relative `Proj` of the Rees algebra *sheaf*, and
`Stacks.Blowup.blowUp`, glued from the `Proj` of the ordinary Rees algebras `Γ(X, U)[ℐ(U)t]`.
Both clauses here are stated for the second one, because
`Stacks.Blowup.exceptionalToCentre` — the morphism `p : E ⟶ Z` of clause (2) — is, so that the
`b` of clause (1) and the `p` of clause (2) belong to one and the same blowup.  [Stacks, Tag 0807]
is stated for the first construction and is transported across that isomorphism where it is used.

**Clause (3) is omitted.** Its statement needs the comparison
`Rb_* ∘ j_* ⟶ i_* ∘ Rp_*` of the derived direct images around the exceptional square, where
`j : E ⟶ X'` is the exceptional divisor.  Nothing in this library constructs that natural
transformation on `AlgebraicGeometry.Scheme.Modules`, so clause (3) has no canonical map to be a
statement about and is not stated here.

**Degrees.** `AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms` is indexed by `ℤ`, while
the source's `a` ranges over the non-negative integers; the comparison maps are defined for every
integer degree and the main result is stated for a natural number cast into `ℤ`, so `a ≥ 0` is
automatic.

## References

* [Stacks Project, Tag 0FUU](https://stacks.math.columbia.edu/tag/0FUU)
* [Stacks Project, Tag 0FUT](https://stacks.math.columbia.edu/tag/0FUT)
* [Stacks Project, Tag 0FUR](https://stacks.math.columbia.edu/tag/0FUR)
* [Stacks Project, Tag 0FUE](https://stacks.math.columbia.edu/tag/0FUE)
* [Stacks Project, Tag 0FLV](https://stacks.math.columbia.edu/tag/0FLV)
* [Stacks Project, Tag 0807](https://stacks.math.columbia.edu/tag/0807)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

attribute [local instance] Stacks.AlgebraicGeometry.coordinateSubspaceEmbedding_isClosedImmersion

namespace Stacks.DeRham

/-! ### The two comparison maps -/

/-- **The comparison map `Ω^a_{X/S} ⟶ b_*Ω^a_{X'/S}` of [Stacks, Tag 0FUU] clause (1).**  Here
`b : X' ⟶ X` is the blowing up of `X` along the closed subscheme cut out by `ker(i)`, and the map
is the adjoint transpose, under `b^* ⊣ b_*`, of the canonical map `b^*Ω^a_{X/S} ⟶ Ω^a_{X'/S}` of
the commutative square with horizontal arrows `b` and `𝟙 S`. -/
def blowupFormsDirectImage {S X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (f : X ⟶ S)
    (a : ℤ) :
    Scheme.Hom.relativeDifferentialForms f a ⟶
      (Scheme.Modules.pushforward (Stacks.Blowup.blowUpToBase i.ker)).obj
        (Scheme.Hom.relativeDifferentialForms
          (Stacks.Blowup.blowUpToBase i.ker ≫ f) a) :=
  (Scheme.Modules.pullbackPushforwardAdjunction
    (Stacks.Blowup.blowUpToBase i.ker)).homEquiv _ _
      (Scheme.Hom.relativeDifferentialFormsMap (Stacks.Blowup.blowUpToBase i.ker) f
        (Stacks.Blowup.blowUpToBase i.ker ≫ f) (𝟙 S) (by simp) a)

/-- **The comparison map `Ω^a_{Z/S} ⟶ p_*Ω^a_{E/S}` of [Stacks, Tag 0FUU] clause (2).**  Here
`p : E ⟶ Z` is the structure morphism `Stacks.Blowup.exceptionalToCentre` of the exceptional
divisor of the blowup over its centre, and the map is the adjoint transpose, under `p^* ⊣ p_*`,
of the canonical map `p^*Ω^a_{Z/S} ⟶ Ω^a_{E/S}` of the commutative square with horizontal
arrows `p` and `𝟙 S`. -/
def exceptionalFormsDirectImage {S X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (f : X ⟶ S) (a : ℤ) :
    Scheme.Hom.relativeDifferentialForms (i ≫ f) a ⟶
      (Scheme.Modules.pushforward (Stacks.Blowup.exceptionalToCentre i)).obj
        (Scheme.Hom.relativeDifferentialForms
          (Stacks.Blowup.exceptionalToCentre i ≫ i ≫ f) a) :=
  (Scheme.Modules.pullbackPushforwardAdjunction
    (Stacks.Blowup.exceptionalToCentre i)).homEquiv _ _
      (Scheme.Hom.relativeDifferentialFormsMap (Stacks.Blowup.exceptionalToCentre i) (i ≫ f)
        (Stacks.Blowup.exceptionalToCentre i ≫ i ≫ f) (𝟙 S) (by simp) a)

/-! ### The carried hypotheses -/

/-- **Flat base change for the comparison of [Stacks, Tag 0FUU] clause (1)**, as a hypothesis.

Let `ε : X₁ ⟶ X` be flat, let `i : Z ⟶ X` and `i₁ : Z₁ ⟶ X₁` be closed immersions sitting in a
cartesian square over `ε`, and let `f₁ = ε ≫ f` be the induced structure morphism of `X₁`.  The
assertion is that the inverse image along `ε` of `Ω^a_{X/S}` is `Ω^a_{X₁/S}`, that the inverse
image along `ε` of `b_*Ω^a_{X'/S}` is `b₁_*Ω^a_{X₁'/S}`, and that the two identifications carry
the comparison map of clause (1) for `i` to the one for `i₁`.

The first identification is [Stacks, Tag 0FLV] when `ε` is étale; the second is flat base change
for the direct image along the blowing-up morphism, for which this library has no carrier. -/
def BlowupFormsFlatBaseChange : Prop :=
  ∀ {S X Z X₁ Z₁ : Scheme.{u}} (f : X ⟶ S) (i : Z ⟶ X) [IsClosedImmersion i] (ε : X₁ ⟶ X)
    [Flat ε] (δ : Z₁ ⟶ Z) (i₁ : Z₁ ⟶ X₁) [IsClosedImmersion i₁] (_ : IsPullback δ i₁ i ε)
    (f₁ : X₁ ⟶ S) (_ : ε ≫ f = f₁) (a : ℤ),
    ∃ (α : (Scheme.Modules.pullback ε).obj (Scheme.Hom.relativeDifferentialForms f a) ≅
          Scheme.Hom.relativeDifferentialForms f₁ a)
      (β : (Scheme.Modules.pullback ε).obj
            ((Scheme.Modules.pushforward (Stacks.Blowup.blowUpToBase i.ker)).obj
              (Scheme.Hom.relativeDifferentialForms
                (Stacks.Blowup.blowUpToBase i.ker ≫ f) a)) ≅
          (Scheme.Modules.pushforward (Stacks.Blowup.blowUpToBase i₁.ker)).obj
            (Scheme.Hom.relativeDifferentialForms
              (Stacks.Blowup.blowUpToBase i₁.ker ≫ f₁) a)),
      (Scheme.Modules.pullback ε).map (blowupFormsDirectImage i f a) ≫ β.hom =
        α.hom ≫ blowupFormsDirectImage i₁ f₁ a

/-- **Flat base change for the comparison of [Stacks, Tag 0FUU] clause (2)**, as a hypothesis.

The data are those of `Stacks.DeRham.BlowupFormsFlatBaseChange`, and the assertion is the same
one for the centre: the inverse image along the flat morphism `δ : Z₁ ⟶ Z` of `Ω^a_{Z/S}` is
`Ω^a_{Z₁/S}`, the inverse image along `δ` of `p_*Ω^a_{E/S}` is `p₁_*Ω^a_{E₁/S}`, and the two
identifications carry the comparison map of clause (2) for `i` to the one for `i₁`. -/
def ExceptionalFormsFlatBaseChange : Prop :=
  ∀ {S X Z X₁ Z₁ : Scheme.{u}} (f : X ⟶ S) (i : Z ⟶ X) [IsClosedImmersion i] (ε : X₁ ⟶ X)
    (δ : Z₁ ⟶ Z) [Flat δ] (i₁ : Z₁ ⟶ X₁) [IsClosedImmersion i₁] (_ : IsPullback δ i₁ i ε)
    (f₁ : X₁ ⟶ S) (_ : ε ≫ f = f₁) (a : ℤ),
    ∃ (α : (Scheme.Modules.pullback δ).obj (Scheme.Hom.relativeDifferentialForms (i ≫ f) a) ≅
          Scheme.Hom.relativeDifferentialForms (i₁ ≫ f₁) a)
      (β : (Scheme.Modules.pullback δ).obj
            ((Scheme.Modules.pushforward (Stacks.Blowup.exceptionalToCentre i)).obj
              (Scheme.Hom.relativeDifferentialForms
                (Stacks.Blowup.exceptionalToCentre i ≫ i ≫ f) a)) ≅
          (Scheme.Modules.pushforward (Stacks.Blowup.exceptionalToCentre i₁)).obj
            (Scheme.Hom.relativeDifferentialForms
              (Stacks.Blowup.exceptionalToCentre i₁ ≫ i₁ ≫ f₁) a)),
      (Scheme.Modules.pullback δ).map (exceptionalFormsDirectImage i f a) ≫ β.hom =
        α.hom ≫ exceptionalFormsDirectImage i₁ f₁ a

/-- **[Stacks, Tag 0FUR] clause (1)**, as a hypothesis: in the coordinate situation
`𝐀^m_S ⊆ 𝐀^{m+n}_S` over an arbitrary base scheme `S`, the comparison
`Ω^a_{X/S} ⟶ b_*Ω^a_{X'/S}` of clause (1) of [Stacks, Tag 0FUU] is an isomorphism in every
degree `a ≥ 0`. -/
def LocalModelBlowupForms : Prop :=
  ∀ (S : Scheme.{u}) (m n a : ℕ),
    IsIso (blowupFormsDirectImage (Stacks.AlgebraicGeometry.coordinateSubspaceEmbedding S m n)
      (AffineSpace.over (ULift.{u} (Fin (m + n))) S).hom (a : ℤ))

/-- **[Stacks, Tag 0FUR] clause (2)**, as a hypothesis: in the coordinate situation
`𝐀^m_S ⊆ 𝐀^{m+n}_S` over an arbitrary base scheme `S`, the comparison
`Ω^a_{Z/S} ⟶ p_*Ω^a_{E/S}` of clause (2) of [Stacks, Tag 0FUU] is an isomorphism in every degree
`a ≥ 0`. -/
def LocalModelExceptionalForms : Prop :=
  ∀ (S : Scheme.{u}) (m n a : ℕ),
    IsIso (exceptionalFormsDirectImage
      (Stacks.AlgebraicGeometry.coordinateSubspaceEmbedding S m n)
      (AffineSpace.over (ULift.{u} (Fin (m + n))) S).hom (a : ℤ))

/-! ### The comparison where the blowing-up morphism is invertible -/

/-- Inverse image of sheaves of modules along an isomorphism of schemes is an equivalence of
categories, with inverse the inverse image along the inverse isomorphism. -/
theorem isEquivalence_pullback_of_isIso {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    (Scheme.Modules.pullback g).IsEquivalence :=
  (CategoryTheory.Equivalence.mk (Scheme.Modules.pullback g) (Scheme.Modules.pullback (inv g))
    (Scheme.Modules.pullbackComp (inv g) g ≪≫
        Scheme.Modules.pullbackCongr (IsIso.inv_hom_id g) ≪≫ Scheme.Modules.pullbackId Y).symm
    (Scheme.Modules.pullbackComp g (inv g) ≪≫
      Scheme.Modules.pullbackCongr (IsIso.hom_inv_id g) ≪≫
        Scheme.Modules.pullbackId X)).isEquivalence_functor

/-- The unit of the inverse image–direct image adjunction of an isomorphism of schemes is an
isomorphism on every sheaf of modules: the inverse image functor is then an equivalence, hence
fully faithful. -/
theorem isIso_unit_app_of_isIso {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] (M : Y.Modules) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M) := by
  have := isEquivalence_pullback_of_isIso g
  have : IsIso (Scheme.Modules.pullbackPushforwardAdjunction g).unit := inferInstance
  exact NatIso.isIso_app_of_isIso (Scheme.Modules.pullbackPushforwardAdjunction g).unit M

/-- The adjoint transpose of the canonical map of relative differential forms along an
isomorphism of schemes is an isomorphism. -/
private theorem isIso_homEquiv_relativeDifferentialFormsMap_of_isIso {S X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g] (f : Y ⟶ S) (a : ℤ) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
      (Scheme.Hom.relativeDifferentialFormsMap g f (g ≫ f) (𝟙 S) (by simp) a)) := by
  have := Scheme.Hom.isIso_relativeDifferentialFormsMap_of_etale g f (g ≫ f) (𝟙 S) (by simp) a
  have := isIso_unit_app_of_isIso g (Scheme.Hom.relativeDifferentialForms f a)
  rw [Adjunction.homEquiv_unit]
  infer_instance

/-- **Where the blowing-up morphism is an isomorphism, the comparison of [Stacks, Tag 0FUU]
clause (1) is an isomorphism.**  The comparison is the unit of the inverse image–direct image
adjunction of `b` followed by the direct image of the canonical map `b^*Ω^a_{X/S} ⟶ Ω^a_{X'/S}`;
the first is an isomorphism because `b` is, and the second because an isomorphism is étale, so
that [Stacks, Tag 0FLV] applies. -/
theorem isIso_blowupFormsDirectImage_of_isIso_blowUpToBase {S X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (f : X ⟶ S) (a : ℤ)
    [IsIso (Stacks.Blowup.blowUpToBase i.ker)] :
    IsIso (blowupFormsDirectImage i f a) := by
  exact isIso_homEquiv_relativeDifferentialFormsMap_of_isIso _ _ a

/-- **Where the structure morphism of the exceptional divisor over the centre is an isomorphism,
the comparison of [Stacks, Tag 0FUU] clause (2) is an isomorphism.**  This is the argument of
`Stacks.DeRham.isIso_blowupFormsDirectImage_of_isIso_blowUpToBase` with `p : E ⟶ Z` in place of
`b : X' ⟶ X`: the comparison is the unit of the inverse image–direct image adjunction of `p`
followed by the direct image of the canonical map `p^*Ω^a_{Z/S} ⟶ Ω^a_{E/S}`; the first is an
isomorphism because `p` is, and the second because an isomorphism is étale, so that
[Stacks, Tag 0FLV] applies. -/
theorem isIso_exceptionalFormsDirectImage_of_isIso_exceptionalToCentre {S X Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (f : X ⟶ S) (a : ℤ)
    [IsIso (Stacks.Blowup.exceptionalToCentre i)] :
    IsIso (exceptionalFormsDirectImage i f a) := by
  exact isIso_homEquiv_relativeDifferentialFormsMap_of_isIso _ _ a

/-- **Blowing up an effective Cartier divisor does not change the scheme.**  [Stacks, Tag 0807]
is stated for `AlgebraicGeometry.blowUpToBase`, and
`AlgebraicGeometry.blowUpIso_hom_blowUpToBase` carries the conclusion to the blowup used here. -/
theorem isIso_blowUpToBase_of_isEffectiveCartierDivisor {X : Scheme.{u}}
    (I : X.IdealSheafData) (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) :
    IsIso (Stacks.Blowup.blowUpToBase I) := by
  have h0 : IsIso (AlgebraicGeometry.blowUpToBase I) :=
    Stacks.Blowup.isIso_blowUpToBase_of_isEffectiveCartierDivisor _ hI
  have he : Stacks.Blowup.blowUpToBase I =
      (AlgebraicGeometry.blowUpIso I).inv ≫ AlgebraicGeometry.blowUpToBase I := by
    rw [← AlgebraicGeometry.blowUpIso_hom_blowUpToBase I]
    simp
  rw [he]
  infer_instance

/-- **The blowup of an ideal sheaf which is the unit ideal is the scheme itself.**  The unit
ideal is an effective Cartier divisor, so [Stacks, Tag 0807] applies. -/
theorem isIso_blowUpToBase_of_ker_eq_top {X Z : Scheme.{u}} (i : Z ⟶ X) (h : i.ker = ⊤) :
    IsIso (Stacks.Blowup.blowUpToBase i.ker) := by
  rw [h]
  exact isIso_blowUpToBase_of_isEffectiveCartierDivisor _
    Stacks.Divisors.isEffectiveCartierDivisor_top

/-- **When the centre of the blowup is an effective Cartier divisor, the structure morphism of
its exceptional divisor over the centre is an isomorphism.**  The exceptional divisor is the
fibre product of the blowup with the centre, by
`Stacks.Blowup.isPullback_exceptionalToCentre`, so `p : E ⟶ Z` is the base change of
`b : X' ⟶ X` along `i : Z ⟶ X`, and `b` is an isomorphism by [Stacks, Tag 0807]. -/
theorem isIso_exceptionalToCentre_of_isEffectiveCartierDivisor {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (hi : Stacks.Divisors.IsEffectiveCartierDivisor i.ker) :
    IsIso (Stacks.Blowup.exceptionalToCentre i) :=
  have := isIso_blowUpToBase_of_isEffectiveCartierDivisor i.ker hi
  (Stacks.Blowup.isPullback_exceptionalToCentre i).isIso_snd_of_isIso

/-! ### Restriction of the situation to an open of the ambient scheme -/

section Restrict

variable {X Z : Scheme.{u}} (i : Z ⟶ X) (U : X.Opens)

/-- The restriction of a closed immersion to an open of the ambient scheme and its inverse
image. -/
abbrev restrictCentre : (i ⁻¹ᵁ U).toScheme ⟶ U.toScheme := i.resLE U (i ⁻¹ᵁ U) le_rfl

/-- The inverse image of an open of the ambient scheme is a cartesian square of the closed
immersion against the open immersion. -/
theorem isPullback_restrictCentre :
    IsPullback (i ⁻¹ᵁ U).ι (restrictCentre i U) i U.ι :=
  (by simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using
    isPullback_morphismRestrict i U : IsPullback (restrictCentre i U) (i ⁻¹ᵁ U).ι U.ι i).flip

/-- The restriction of a closed immersion to an open of the ambient scheme is a closed
immersion. -/
instance isClosedImmersion_restrictCentre [IsClosedImmersion i] :
    IsClosedImmersion (restrictCentre i U) := by
  change IsClosedImmersion (i.resLE U (i ⁻¹ᵁ U) le_rfl)
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  exact MorphismProperty.of_isPullback (isPullback_morphismRestrict i U).flip inferInstance

end Restrict

/-! ### The étale-local reduction -/

section Reduction

variable {S X Z : Scheme.{u}} (f : X ⟶ S) (i : Z ⟶ X) [IsClosedImmersion i]

/-- **Clause (1) on an open is clause (1) restricted to that open.**  The inverse image along the
inclusion of an open `U ⊆ X` of the comparison map of clause (1) is invertible as soon as the
comparison map of the situation restricted to `U` is. -/
theorem isIso_pullback_blowupFormsDirectImage_of_restrict
    (hbc : BlowupFormsFlatBaseChange.{u}) (U : X.Opens) (a : ℤ)
    (h : IsIso (blowupFormsDirectImage (restrictCentre i U) (U.ι ≫ f) a)) :
    IsIso ((Scheme.Modules.pullback U.ι).map (blowupFormsDirectImage i f a)) := by
  obtain ⟨α, β, hsq⟩ := hbc f i U.ι (i ⁻¹ᵁ U).ι (restrictCentre i U)
    (isPullback_restrictCentre i U) (U.ι ≫ f) rfl a
  exact (isIso_iff_of_sq_of_isIso α.isIso_hom β.isIso_hom hsq.symm).2 h

/-- **Clause (2) on an open is clause (2) restricted to that open.**  The inverse image along the
inclusion of the open `i⁻¹U ⊆ Z` of the comparison map of clause (2) is invertible as soon as the
comparison map of the situation restricted to `U` is. -/
theorem isIso_pullback_exceptionalFormsDirectImage_of_restrict
    (hbc : ExceptionalFormsFlatBaseChange.{u}) (U : X.Opens) (a : ℤ)
    (h : IsIso (exceptionalFormsDirectImage (restrictCentre i U) (U.ι ≫ f) a)) :
    IsIso ((Scheme.Modules.pullback (i ⁻¹ᵁ U).ι).map (exceptionalFormsDirectImage i f a)) := by
  obtain ⟨α, β, hsq⟩ := hbc f i U.ι (i ⁻¹ᵁ U).ι (restrictCentre i U)
    (isPullback_restrictCentre i U) (U.ι ≫ f) rfl a
  exact (isIso_iff_of_sq_of_isIso α.isIso_hom β.isIso_hom hsq.symm).2 h

variable {m n : ℕ} {U : X.Opens}
  {π : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin (m + n))) S}
  {q : (i ⁻¹ᵁ U).toScheme ⟶ AffineSpace (ULift.{u} (Fin m)) S}

/-- **Clause (1) on an étale coordinate chart.**  If the restriction of the situation to an open
`U ⊆ X` is the pullback of the coordinate situation `𝐀^m_S ⊆ 𝐀^{m+n}_S` along an étale morphism
`π : U ⟶ 𝐀^{m+n}_S` over `S`, then clause (1) for the coordinate situation gives clause (1) for
the restricted situation. -/
theorem isIso_blowupFormsDirectImage_of_chart (hbc : BlowupFormsFlatBaseChange.{u})
    (h0FUR : LocalModelBlowupForms.{u}) [Etale π]
    (hbase : π ≫ (AffineSpace.over (ULift.{u} (Fin (m + n))) S).hom = U.ι ≫ f)
    (hchart : IsPullback (restrictCentre i U) q π
      (Stacks.AlgebraicGeometry.coordinateSubspaceEmbedding S m n))
    (a : ℕ) :
    IsIso (blowupFormsDirectImage (restrictCentre i U) (U.ι ≫ f) (a : ℤ)) := by
  obtain ⟨α, β, hsq⟩ := hbc (AffineSpace.over (ULift.{u} (Fin (m + n))) S).hom
    (Stacks.AlgebraicGeometry.coordinateSubspaceEmbedding S m n) π q (restrictCentre i U)
    hchart.flip (U.ι ≫ f) hbase (a : ℤ)
  have := h0FUR S m n a
  exact (isIso_iff_of_sq_of_isIso α.isIso_hom β.isIso_hom hsq.symm).1
    (Functor.map_isIso (Scheme.Modules.pullback π) _)

/-- **Clause (2) on an étale coordinate chart.**  If the restriction of the situation to an open
`U ⊆ X` is the pullback of the coordinate situation `𝐀^m_S ⊆ 𝐀^{m+n}_S` along an étale morphism
`π : U ⟶ 𝐀^{m+n}_S` over `S`, then clause (2) for the coordinate situation gives clause (2) for
the restricted situation. -/
theorem isIso_exceptionalFormsDirectImage_of_chart (hbc : ExceptionalFormsFlatBaseChange.{u})
    (h0FUR : LocalModelExceptionalForms.{u}) [Etale π]
    (hbase : π ≫ (AffineSpace.over (ULift.{u} (Fin (m + n))) S).hom = U.ι ≫ f)
    (hchart : IsPullback (restrictCentre i U) q π
      (Stacks.AlgebraicGeometry.coordinateSubspaceEmbedding S m n))
    (a : ℕ) :
    IsIso (exceptionalFormsDirectImage (restrictCentre i U) (U.ι ≫ f) (a : ℤ)) := by
  have : Etale q := MorphismProperty.of_isPullback hchart inferInstance
  obtain ⟨α, β, hsq⟩ := hbc (AffineSpace.over (ULift.{u} (Fin (m + n))) S).hom
    (Stacks.AlgebraicGeometry.coordinateSubspaceEmbedding S m n) π q (restrictCentre i U)
    hchart.flip (U.ι ≫ f) hbase (a : ℤ)
  have := h0FUR S m n a
  exact (isIso_iff_of_sq_of_isIso α.isIso_hom β.isIso_hom hsq.symm).1
    (Functor.map_isIso (Scheme.Modules.pullback q) _)

end Reduction

/-! ### Clauses (1) and (2) of Stacks 0FUU -/

/-- **[Stacks, Tag 0FUU], clauses (1) and (2).**  Let `f : X ⟶ S` be smooth, let `i : Z ⟶ X` be a
closed immersion with `Z` smooth over `S`, let `b : X' ⟶ X` be the blowing up of `X` along `Z`,
let `E` be its exceptional divisor and let `p : E ⟶ Z` be the structure morphism of `E` over the
centre.  Then for every `a ≥ 0` the comparison maps

* `Ω^a_{X/S} ⟶ b_*Ω^a_{X'/S}` and
* `Ω^a_{Z/S} ⟶ p_*Ω^a_{E/S}`

are isomorphisms.  This is the étale-local REDUCTION of the source's proof, not a proof of the
tag: it takes clauses (1) and (2) of [Stacks, Tag 0FUR] for the coordinate situation
`𝐀^m_S ⊆ 𝐀^{m+n}_S`, and flat base change for the two direct images, as explicit inputs.  It
therefore bears NO `@[stacks 0FUU]` attribute: the tag is registered in this file on
`Stacks.DeRham.isIso_formsDirectImage_of_isEffectiveCartierDivisor`, which proves the divisorial
case outright.  Of the inputs, the library holds [Stacks, Tag 0FUR] clause (1) only for `n = 1`
and clause (2) only for `n = 1` or `a = 0`; the general case needs [Stacks, Tag 062K], the
existence of the Koszul differential.

Invertibility of a homomorphism of sheaves of modules is local on the target.  Clause (2) lives
on `Z`, which the opens `i⁻¹U` of the charts of [Stacks, Tag 0FUE] cover, and on such an open the
situation is the flat pullback of the coordinate situation.  Clause (1) lives on `X`, where those
opens cover the image of `i`; the complement of that image is one further open, on which the
centre is empty, so that the inverse-image ideal is the unit ideal and the blowing-up morphism is
an isomorphism. -/
theorem isIso_formsDirectImage_of_smooth (hbc1 : BlowupFormsFlatBaseChange.{u})
    (hbc2 : ExceptionalFormsFlatBaseChange.{u}) (h0FUR1 : LocalModelBlowupForms.{u})
    (h0FUR2 : LocalModelExceptionalForms.{u}) {S X Z : Scheme.{u}} (f : X ⟶ S) (i : Z ⟶ X)
    [IsClosedImmersion i] [Smooth f] [Smooth (i ≫ f)] (a : ℕ) :
    IsIso (blowupFormsDirectImage i f (a : ℤ)) ∧
      IsIso (exceptionalFormsDirectImage i f (a : ℤ)) := by
  classical
  -- On a chart around a point of the centre both clauses hold for the restricted situation.
  have hchart : ∀ z : Z, ∃ U : X.Opens, i z ∈ U ∧ z ∈ i ⁻¹ᵁ U ∧
      IsIso (blowupFormsDirectImage (restrictCentre i U) (U.ι ≫ f) (a : ℤ)) ∧
      IsIso (exceptionalFormsDirectImage (restrictCentre i U) (U.ι ≫ f) (a : ℤ)) := by
    intro z
    obtain ⟨m, n, U, hzU, π, q, hπ, hbase, hpb⟩ :=
      Stacks.AlgebraicGeometry.exists_etale_coordinateSubspaceEmbedding_isPullback f i z
    have : Etale π := hπ
    exact ⟨U, hzU, hzU,
      isIso_blowupFormsDirectImage_of_chart f i hbc1 h0FUR1 hbase hpb a,
      isIso_exceptionalFormsDirectImage_of_chart f i hbc2 h0FUR2 hbase hpb a⟩
  constructor
  · -- Clause (1): cover `X` by the charts and by the complement of the image of `i`.
    have hcov : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
        IsIso ((Scheme.Modules.pullback U.ι).map (blowupFormsDirectImage i f (a : ℤ))) := by
      intro x
      by_cases hx : x ∈ Set.range i.base
      · obtain ⟨z, rfl⟩ := hx
        obtain ⟨U, hxU, _, h1, _⟩ := hchart z
        exact ⟨U, hxU, isIso_pullback_blowupFormsDirectImage_of_restrict f i hbc1 U _ h1⟩
      · let W : X.Opens :=
          ⟨(Set.range i.base)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
        have hxW : x ∈ W := hx
        have hempty : IsEmpty ↥(i ⁻¹ᵁ W) := by
          refine ⟨fun y => ?_⟩
          have hy : i.base y.1 ∈ W := y.2
          exact hy ⟨y.1, rfl⟩
        have hIE : IsEmpty ↥(i ⁻¹ᵁ W).toScheme := hempty
        have := isIso_blowUpToBase_of_ker_eq_top (restrictCentre i W)
          (AlgebraicGeometry.Scheme.ker_eq_top_of_isEmpty _)
        exact ⟨W, hxW, isIso_pullback_blowupFormsDirectImage_of_restrict f i hbc1 W _
          (isIso_blowupFormsDirectImage_of_isIso_blowUpToBase _ _ _)⟩
    choose U hxU hU using hcov
    refine Scheme.Modules.isIso_of_isIso_pullback_ι U ?_ _ hU
    exact top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxU x⟩
  · -- Clause (2): the opens `i⁻¹U` of the charts cover `Z`.
    have hcov : ∀ z : Z, ∃ V : Z.Opens, z ∈ V ∧
        IsIso ((Scheme.Modules.pullback V.ι).map
          (exceptionalFormsDirectImage i f (a : ℤ))) := by
      intro z
      obtain ⟨U, _, hzU, _, h2⟩ := hchart z
      exact ⟨i ⁻¹ᵁ U, hzU,
        isIso_pullback_exceptionalFormsDirectImage_of_restrict f i hbc2 U _ h2⟩
    choose V hzV hV using hcov
    refine Scheme.Modules.isIso_of_isIso_pullback_ι V ?_ _ hV
    exact top_le_iff.1 fun z _ => TopologicalSpace.Opens.mem_iSup.2 ⟨z, hzV z⟩

/-! ### Clauses (1) and (2) of Stacks 0FUU for a divisorial centre -/

/-- **[Stacks, Tag 0FUU], clauses (1) and (2), for a centre which is an effective Cartier
divisor.**  Let `i : Z ⟶ X` be a closed immersion whose ideal sheaf is an effective Cartier
divisor, let `f : X ⟶ S` be any morphism, let `b : X' ⟶ X` be the blowing up of `X` along `Z`,
let `E` be its exceptional divisor and let `p : E ⟶ Z` be the structure morphism of `E` over the
centre.  Then in every degree the comparison maps

* `Ω^a_{X/S} ⟶ b_*Ω^a_{X'/S}` and
* `Ω^a_{Z/S} ⟶ p_*Ω^a_{E/S}`

are isomorphisms.

This is the degenerate case of the tag, and it is proved for a nearly trivial reason.  Blowing up
an effective Cartier divisor leaves the scheme unchanged ([Stacks, Tag 0807]), so `b` is an
isomorphism; the exceptional divisor is the fibre product of the blowup with the centre, so `p`
is the base change of `b` along `i` and is an isomorphism too.  Each comparison is then the unit
of the inverse image–direct image adjunction along an isomorphism, followed by the direct image
of a map which is an isomorphism by [Stacks, Tag 0FLV].

For a closed immersion of schemes smooth over `S` the ideal of the centre is locally generated by
a regular sequence, by [Stacks, Tag 0FUE], so the hypothesis here holds precisely when that
sequence has length one at every point of the centre — the centre is a divisor, of codimension
one wherever it is non-empty.  The empty centre satisfies it vacuously, its ideal being the unit
ideal.  The source states the tag for a centre of arbitrary codimension, and nothing of its
proof — the étale-local reduction of [Stacks, Tag 0FUE] to the coordinate situation
`𝐀^m_S ⊆ 𝐀^{m+n}_S` and the computation of [Stacks, Tag 0FUR] there — is used.  Smoothness of
`f` and of `i ≫ f` is not needed for this case and is not assumed. -/
@[stacks 0FUU "clauses (1) and (2) in every integer degree, for a centre whose ideal sheaf is an \
effective Cartier divisor — a divisorial centre, which for a closed immersion of schemes smooth \
over S means codimension one at every point of the centre (the empty centre qualifying \
vacuously).  This is the degenerate case of the tag, proved for \
a nearly trivial reason: blowing up an effective Cartier divisor leaves the scheme unchanged \
(Stacks 0807), so b : X' ⟶ X is an isomorphism, and the exceptional divisor is the fibre product \
of the blowup with the centre, so p : E ⟶ Z is the base change of b along i and is an \
isomorphism too; each comparison is then the unit of the inverse image–direct image adjunction \
along an isomorphism followed by the direct image of a map which is an isomorphism by Stacks \
0FLV.  A centre of codimension two or more is NOT proved, in any degree: none of the content of \
the source's proof — the étale-local reduction of Stacks 0FUE to the coordinate situation \
𝐀^m_S ⊆ 𝐀^{m+n}_S, and the computation of Stacks 0FUR there — is used.  In the other direction \
this is more general than the source: the smoothness of f and of i ≫ f is not needed for a \
divisorial centre and is not assumed, and every integer degree is covered, not only a ≥ 0.  \
Clause (3) is not included: the derived comparison of Rb_* ∘ j_* against i_* ∘ Rp_* has no \
carrier in this library, so clause (3) has no canonical map to be a statement about"]
theorem isIso_formsDirectImage_of_isEffectiveCartierDivisor {S X Z : Scheme.{u}} (f : X ⟶ S)
    (i : Z ⟶ X) [IsClosedImmersion i]
    (hi : Stacks.Divisors.IsEffectiveCartierDivisor i.ker) (a : ℤ) :
    IsIso (blowupFormsDirectImage i f a) ∧ IsIso (exceptionalFormsDirectImage i f a) :=
  have := isIso_blowUpToBase_of_isEffectiveCartierDivisor i.ker hi
  have := isIso_exceptionalToCentre_of_isEffectiveCartierDivisor i hi
  ⟨isIso_blowupFormsDirectImage_of_isIso_blowUpToBase i f a,
    isIso_exceptionalFormsDirectImage_of_isIso_exceptionalToCentre i f a⟩

end Stacks.DeRham

end
