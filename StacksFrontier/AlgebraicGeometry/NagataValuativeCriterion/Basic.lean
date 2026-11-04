module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.RingTheory.Localization.FractionRing
public import StacksFrontier.AlgebraicGeometry.Properties.Nagata
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.RingTheory.DiscreteValuationRing.TFAE
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Valuative criteria over a Nagata base

Over a Nagata base one expects to be able to test universal closedness of a quasi-compact
morphism between schemes locally of finite type using only discrete valuation rings that are
essentially of finite type over the base, namely the local rings of normal integral finite-type
schemes at closed points of local dimension one.  This file states that test condition and
proves the two implications that go *out* of universal closedness.

## Main definitions

* `HasEssentiallyFiniteTypeValuativeExtension` is the extension condition: for every normal
  integral scheme `C` of finite type over the base, every closed point `c ∈ C` whose local ring
  has Krull dimension one, and every pair consisting of a morphism `C ⟶ Y` over the base and a
  morphism `C \ {c} ⟶ X` over it, the induced square over `Spec 𝒪_{C,c}` admits a lift.
* `ClosedAffineSpaceBaseChangeImpliesUniversallyClosed` and
  `ExtensionImpliesClosedAffineSpaceBaseChange` name the two implications that are *not* proved
  here, so that a statement depending on them cannot be mistaken for an unconditional one.

## Main results

* `isDiscreteValuationRing_stalk_of_ringKrullDim_eq_one`: on a locally Noetherian normal scheme,
  a local ring of Krull dimension one is a discrete valuation ring.
* `isClosedMap_affineSpaceMap_of_universallyClosed`: a universally closed morphism stays closed
  after adjoining finitely many affine coordinates.
* `hasEssentiallyFiniteTypeValuativeExtension_of_universallyClosed`: a universally closed
  morphism satisfies the extension condition.
* `universallyClosed_tfae_essentiallyFiniteType_of_converses`: the three conditions are
  equivalent, *given* the two named implications above.

## Implementation notes

The extension condition is transcribed with the `let`-bindings of its source statement.  Those
bindings are deliberately never introduced into the local context when it is proved: an `intro`
turns a `let` into a let-bound free variable, and typeclass synthesis does not unfold such a
variable, so the `IsDomain` hypothesis that the statement supplies becomes unusable for the
`Field` instance on the fraction field.  Term-mode binders zeta-reduce the bindings instead.

The two implications out of universal closedness both factor through Mathlib's valuative
criterion `UniversallyClosed.eq_valuativeCriterion`, which is an equality of morphism
properties, so `QuasiCompact` is not needed as a separate hypothesis for them: it is implied.
That criterion quantifies over *all* valuation rings; the content of the remaining two
implications is exactly that the essentially-finite-type ones suffice over a Nagata base, and
that is not proved here.

`isDiscreteValuationRing_stalk_of_ringKrullDim_eq_one` overlaps
`Stacks.AlgebraicGeometry.UnitsNormalProper.isDiscreteValuationRing_stalk`, which assumes
`IsIntegral` and phrases dimension one as `coheight x = 1`.  Neither hypothesis is needed for
the conclusion, and the statement here supplies `ringKrullDim` directly, so the statement here drops
both rather than converting.

## References

* [Stacks Project, Tag 0GWV](https://stacks.math.columbia.edu/tag/0GWV)
* [Stacks Project, Tag 05JX](https://stacks.math.columbia.edu/tag/05JX)
* [Stacks Project, Tag 00PD](https://stacks.math.columbia.edu/tag/00PD)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.AlgebraicGeometry.NagataValuativeCriterion

/-! ### The extension condition -/

/-- The one-dimensional finite-type test for existence of extensions over a
normal integral scheme. The lower morphism is a morphism over `S`, and the
generic morphism is the one induced by the local ring at the omitted point. -/
def HasEssentiallyFiniteTypeValuativeExtension
    {S X Y : Scheme.{u}} (f : X ⟶ Y) (hY : Y ⟶ S) : Prop :=
  ∀ (C : Scheme.{u}) (p : C ⟶ S),
    LocallyOfFiniteType p → QuasiCompact p →
    IsNormal C → IsIntegral C →
    ∀ (c : C) (hc : IsClosed ({c} : Set C))
      (_hdim : ringKrullDim (C.presheaf.stalk c) = 1),
      let U : C.Opens := ⟨({c} : Set C)ᶜ, hc.isOpen_compl⟩
      ∀ (q : C ⟶ Y) (a : U.toScheme ⟶ X),
        q ≫ hY = p → a ≫ f = U.ι ≫ q →
        ∀ (hdom : IsDomain (C.presheaf.stalk c)),
          letI := hdom
          let A := C.presheaf.stalk c
          let i : Spec (.of (FractionRing A)) ⟶ Spec (.of A) :=
            Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A)))
          ∀ (g : Spec (.of (FractionRing A)) ⟶ U.toScheme),
            g ≫ U.ι = i ≫ C.fromSpecStalk c →
            ∃ l : Spec (.of A) ⟶ X,
              (l ≫ f = C.fromSpecStalk c ≫ q) ∧ (i ≫ l = g ≫ a)

/-! ### Bookkeeping over a Nagata base -/

/-- A Nagata scheme is locally Noetherian, because a Nagata ring is Noetherian. -/
theorem isLocallyNoetherian_of_isNagataScheme {S : Scheme.{u}} (hS : IsNagataScheme S) :
    IsLocallyNoetherian S :=
  ((isNagataScheme_iff_isLocallyNoetherian_and_isUniversallyJapaneseScheme S).mp hS).1

/-- A morphism whose composite with a morphism locally of finite type is locally of finite type
is itself locally of finite type.  This is the form in which the hypotheses of tag `0GWV` give
that `f` is locally of finite type: only the composite is assumed. -/
theorem locallyOfFiniteType_of_comp_eq {S X Y : Scheme.{u}} {hX : X ⟶ S} (hY : Y ⟶ S)
    (f : X ⟶ Y) (hf : f ≫ hY = hX) [LocallyOfFiniteType hX] : LocallyOfFiniteType f := by
  have h : LocallyOfFiniteType (f ≫ hY) := hf ▸ ‹LocallyOfFiniteType hX›
  exact locallyOfFiniteType_of_comp f hY

/-! ### The local ring at a closed point of local dimension one -/

/-- On a locally Noetherian normal scheme, a local ring of Krull dimension one is a discrete
valuation ring.  This is tag `00PD` applied to the stalk, which is a Noetherian local normal
domain by the hypotheses. -/
@[sga "3 X 8.9" "(b)"]
theorem isDiscreteValuationRing_stalk_of_ringKrullDim_eq_one (C : Scheme.{u})
    [IsLocallyNoetherian C] [IsNormal C] {c : C}
    (hdim : ringKrullDim (C.presheaf.stalk c) = 1) :
    IsDiscreteValuationRing (C.presheaf.stalk c) := by
  have h : IsNoetherianRing (C.presheaf.stalk c) ∧ IsLocalRing (C.presheaf.stalk c) ∧
      IsDomain (C.presheaf.stalk c) ∧ IsIntegrallyClosed (C.presheaf.stalk c) ∧
      ringKrullDim (C.presheaf.stalk c) = 1 :=
    ⟨inferInstance, inferInstance, inferInstance, IsNormal.stalk_normal c, hdim⟩
  obtain ⟨_, hdvr⟩ := ((isDiscreteValuationRing_tfae (C.presheaf.stalk c)).out 5 1).mp h
  exact hdvr

/-- On a locally Noetherian normal scheme, a local ring of Krull dimension one is a valuation
ring, so it is admissible in Mathlib's valuative criterion. -/
theorem valuationRing_stalk_of_ringKrullDim_eq_one (C : Scheme.{u})
    [IsLocallyNoetherian C] [IsNormal C] {c : C}
    (hdim : ringKrullDim (C.presheaf.stalk c) = 1) :
    ValuationRing (C.presheaf.stalk c) :=
  have := isDiscreteValuationRing_stalk_of_ringKrullDim_eq_one C hdim
  inferInstance

/-! ### The implications out of universal closedness -/

/-- A universally closed morphism stays closed after adjoining finitely many affine
coordinates, because `𝔸(n; X) ⟶ 𝔸(n; Y)` is the base change of `f` along `𝔸(n; Y) ↘ Y`. -/
theorem isClosedMap_affineSpaceMap_of_universallyClosed {X Y : Scheme.{u}} (f : X ⟶ Y)
    [h : UniversallyClosed f] (n : ℕ) :
    IsClosedMap (AffineSpace.map (ULift.{u} (Fin n)) f) :=
  h.universally_isClosedMap _ _ _ (AffineSpace.isPullback_map f)

/-- A universally closed morphism satisfies the essentially-finite-type extension condition.
The local ring at the omitted point is a discrete valuation ring, hence a valuation ring, so
the square is one of those tested by Mathlib's valuative criterion. -/
theorem hasEssentiallyFiniteTypeValuativeExtension_of_universallyClosed {S X Y : Scheme.{u}}
    (f : X ⟶ Y) (hY : Y ⟶ S) (hS : IsNagataScheme S) [UniversallyClosed f] :
    HasEssentiallyFiniteTypeValuativeExtension f hY := by
  have hexist : ValuativeCriterion.Existence f :=
    (UniversallyClosed.eq_valuativeCriterion.le _ _ f ‹_›).1
  have hSN : IsLocallyNoetherian S := isLocallyNoetherian_of_isNagataScheme hS
  refine fun C p hp _hqc _hn _hi c hc hdim q a _hq ha hdom g hg => ?_
  have hCN : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian p
  have hvr : ValuationRing (C.presheaf.stalk c) :=
    valuationRing_stalk_of_ringKrullDim_eq_one C hdim
  obtain ⟨lift⟩ := (hexist
    { R := (C.presheaf.stalk c : Type u)
      domain := hdom
      valuationRing := hvr
      K := FractionRing (C.presheaf.stalk c)
      field := FractionRing.field _
      i₁ := g ≫ a
      i₂ := C.fromSpecStalk c ≫ q
      commSq := ⟨by rw [Category.assoc, ha, ← Category.assoc, hg, Category.assoc]⟩ }).exists_lift
  exact ⟨lift.l, lift.fac_right, lift.fac_left⟩

/-! ### The two implications that are not proved here -/

/-- **Not proved in this file.**  Tag `05JX`, implication (3) ⇒ (1): a quasi-compact morphism
which stays closed after adjoining finitely many affine coordinates is universally closed.
Its source proof approximates an arbitrary base by one locally of finite presentation. -/
def ClosedAffineSpaceBaseChangeImpliesUniversallyClosed : Prop :=
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), QuasiCompact f →
    (∀ n : ℕ, IsClosedMap (AffineSpace.map (ULift.{u} (Fin n)) f)) → UniversallyClosed f

/-- **Not proved in this file.**  Tag `0GWV`, implication (3) ⇒ (2): over a Nagata base the
essentially-finite-type extension condition already forces every finite-dimensional affine-space
base change to be closed.  This is the whole content of tag `0GWV`; its source proof uses the
finiteness of normalisation over a Nagata base and the gluing lemma of tag `0GWT`. -/
def ExtensionImpliesClosedAffineSpaceBaseChange : Prop :=
  ∀ {S X Y : Scheme.{u}} (hX : X ⟶ S) (hY : Y ⟶ S) (f : X ⟶ Y), f ≫ hY = hX →
    IsNagataScheme S → LocallyOfFiniteType hX → LocallyOfFiniteType hY → QuasiCompact f →
    HasEssentiallyFiniteTypeValuativeExtension f hY →
    ∀ n : ℕ, IsClosedMap (AffineSpace.map (ULift.{u} (Fin n)) f)

/-! ### The equivalence, modulo the two named implications -/

/-- **Stacks Project, Tag 0GWV**, reduced to two named implications.  Universal closedness,
closedness of all finite-dimensional affine-space base changes, and the normal finite-type
one-dimensional extension test are equivalent — *given* `h₂₁`, which is tag `05JX` (3) ⇒ (1),
and `h₃₂`, which is tag `0GWV` (3) ⇒ (2).  The implications (1) ⇒ (2) and (1) ⇒ (3) are proved
here, so this carries no hypothesis beyond those two and the ones of the source statement.
No Stacks tag is attached to this statement, precisely because of `h₂₁` and `h₃₂`. -/
theorem universallyClosed_tfae_essentiallyFiniteType_of_converses
    {S X Y : Scheme.{u}} (hX : X ⟶ S) (hY : Y ⟶ S) (f : X ⟶ Y)
    (hf : f ≫ hY = hX) (hS : IsNagataScheme S)
    [LocallyOfFiniteType hX] [LocallyOfFiniteType hY] [QuasiCompact f]
    (h₂₁ : ClosedAffineSpaceBaseChangeImpliesUniversallyClosed.{u})
    (h₃₂ : ExtensionImpliesClosedAffineSpaceBaseChange.{u}) :
    List.TFAE
      [UniversallyClosed f,
       ∀ n : ℕ, IsClosedMap (AffineSpace.map (ULift.{u} (Fin n)) f),
       HasEssentiallyFiniteTypeValuativeExtension f hY] := by
  tfae_have 1 → 2 := fun h n => by
    have := h
    exact isClosedMap_affineSpaceMap_of_universallyClosed f n
  tfae_have 2 → 1 := fun h => h₂₁ f ‹_› h
  tfae_have 1 → 3 := fun h => by
    have := h
    exact hasEssentiallyFiniteTypeValuativeExtension_of_universallyClosed f hY hS
  tfae_have 3 → 2 := fun h => h₃₂ hX hY f hf hS ‹_› ‹_› ‹_› h
  tfae_finish

end Stacks.AlgebraicGeometry.NagataValuativeCriterion
