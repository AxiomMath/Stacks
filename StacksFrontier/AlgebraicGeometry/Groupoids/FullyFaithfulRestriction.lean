module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.MorphismProperty.Local
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.Evaluation
import all StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.FlatRelationQuotient

/-!
# Morphisms of groupoid schemes which are fully faithful on generalized points

A morphism of groupoid schemes `F : (U, R) ⟶ (Ū, R̄)` is *fully faithful* when for every test
scheme `T` the induced functor on groupoids of generalized points is fully faithful; that is,
when `(U, R)` is the restriction of `(Ū, R̄)` along `U ⟶ Ū`.  This file records what such an `F`
says about a subgroupoid `(U, P)` of `(U, R)` whose pre-relation is the kernel pair of
`U ⟶ Ū` and whose arrows go to identities of `R̄`: `P` is exactly the part of `R` over the
identity of `(Ū, R̄)`, and when `P` is open in `R` and `U ⟶ Ū` is surjective, flat and
quasi-compact, the identity of `(Ū, R̄)` is an open immersion.

## Main results

* `Stacks.Groupoids.GroupoidScheme.isPullback_identity_of_isPullback_restriction`: the
  subgroupoid is the part of the arrow scheme over the identity of the quotient groupoid.
* `Stacks.Groupoids.GroupoidScheme.isOpenImmersion_identity_of_isPullback_identity`: the
  identity of the quotient groupoid is an open immersion when the subgroupoid is open.

## Implementation notes

The transfer of morphism properties along a fully faithful morphism of groupoid schemes (a
property of the map on objects stable under base change and composition is inherited by the map
on arrows) is `AlgebraicGeometry.Bootstrap04S6.property_arrows_of_fullyFaithful_groupoid` of
`StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.FlatRelationQuotient`, private to
that file and reached here by `import all`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Groupoids.GroupoidScheme

/-- **The subgroupoid cut out by the identity of a quotient groupoid.**  Let `F : (U, R) ⟶ (Ū, R̄)`
exhibit `(U, R)` as the restriction of `(Ū, R̄)` along `U ⟶ Ū`, so that the square of `hF` is
cartesian, and let `i : (U, P) ⟶ (U, R)` be a subgroupoid on the same object scheme — up to the
isomorphism `i.mapObjects` — whose pre-relation is the kernel pair of `U ⟶ Ū`.  If the arrows of
`P` are carried to identities of `R̄`, then `P` is *exactly* the part of `R` lying over the
identity of `R̄`: the square

```
P  ⟶  R
↓      ↓
Ū  ⟶  R̄
```

with left vertical the composite of the source of `P` with `U ⟶ Ū` and bottom map the identity
of `(Ū, R̄)`, is cartesian.

Nothing is asked of the arrows of `R` beyond the groupoid axioms; in particular `(t, s)` need
not be jointly monic, so this applies to a groupoid with nontrivial automorphisms. -/
theorem isPullback_identity_of_isPullback_restriction
    {S : Scheme.{u}} {G K H : Stacks.Groupoids.GroupoidScheme S}
    (F : G.Hom K) (i : H.Hom G) [IsIso i.mapObjects]
    (hF : IsPullback F.mapArrows (prod.lift G.target G.source)
      (prod.lift K.target K.source) (prod.map F.mapObjects F.mapObjects))
    (hq : IsPullback H.target H.source (i.mapObjects ≫ F.mapObjects)
      (i.mapObjects ≫ F.mapObjects))
    (hw : i.mapArrows ≫ F.mapArrows =
      (H.source ≫ i.mapObjects ≫ F.mapObjects) ≫ K.identity) :
    IsPullback i.mapArrows (H.source ≫ i.mapObjects ≫ F.mapObjects)
      F.mapArrows K.identity := by
  refine IsPullback.mk' hw ?_ ?_
  · -- Two arrows of `P` with the same image in `R` agree: their source and target in `U` are
    -- read off that image, and `P` is the kernel pair of `U ⟶ Ū`.
    intro T φ φ' hφ _
    have key : ∀ (p : H.arrows ⟶ H.objects) (q : G.arrows ⟶ G.objects),
        i.mapArrows ≫ q = p ≫ i.mapObjects → φ ≫ p = φ' ≫ p := fun p q hpq => by
      refine (cancel_mono i.mapObjects).mp ?_
      simpa only [Category.assoc, ← hpq] using congrArg (· ≫ q) hφ
    exact hq.hom_ext (key _ _ i.map_target) (key _ _ i.map_source)
  · -- An arrow of `R` whose image in `R̄` is an identity has equal source and target in `Ū`,
    -- hence names a point of the kernel pair; the arrow of `P` that point names has the same
    -- image in `R`, by the cartesian square of `hF`.
    intro T a b hab
    have key : ∀ (p : K.arrows ⟶ K.objects) (q : G.arrows ⟶ G.objects),
        F.mapArrows ≫ p = q ≫ F.mapObjects → K.identity ≫ p = 𝟙 _ →
        a ≫ q ≫ F.mapObjects = b := fun p q hpq hid => by
      rw [← hpq, ← Category.assoc, hab, Category.assoc, hid, Category.comp_id]
    have htb := key _ _ F.map_target K.target_identity
    have hsb := key _ _ F.map_source K.source_identity
    have hwq : (a ≫ G.target ≫ inv i.mapObjects) ≫ i.mapObjects ≫ F.mapObjects =
        (a ≫ G.source ≫ inv i.mapObjects) ≫ i.mapObjects ≫ F.mapObjects := by
      simp only [Category.assoc, IsIso.inv_hom_id_assoc]
      rw [htb, hsb]
    obtain ⟨l, hct, hcs⟩ : ∃ l, l ≫ H.target = a ≫ G.target ≫ inv i.mapObjects ∧
        l ≫ H.source = a ≫ G.source ≫ inv i.mapObjects :=
      ⟨hq.lift _ _ hwq, hq.lift_fst _ _ hwq, hq.lift_snd _ _ hwq⟩
    have hlt : l ≫ H.target ≫ i.mapObjects = a ≫ G.target := by
      rw [← Category.assoc, hct]; simp
    have hls : l ≫ H.source ≫ i.mapObjects = a ≫ G.source := by
      rw [← Category.assoc, hcs]; simp
    have hlb : l ≫ H.source ≫ i.mapObjects ≫ F.mapObjects = b := by
      rw [← Category.assoc H.source, ← Category.assoc l, hls, Category.assoc, hsb]
    refine ⟨l, hF.hom_ext ?_ ?_, hlb⟩
    · rw [Category.assoc, hw, hab, ← hlb]
      simp
    · refine prod.hom_ext ?_ ?_ <;> simp [i.map_target, i.map_source, hlt, hls]

open AlgebraicGeometry.Bootstrap04S6 in
/-- **The identity of a quotient groupoid is an open immersion when the subgroupoid it comes
from is.**  If `(U, R)` is the restriction of `(Ū, R̄)` along a surjective, flat, quasi-compact
`U ⟶ Ū`, and `(U, P)` is a subgroupoid whose arrow scheme is an open subscheme of `R` and which
is exactly the part of `R` lying over the identity of `R̄`, then the identity `ē : Ū ⟶ R̄` is an
open immersion.

Being an open immersion descends along surjective flat quasi-compact morphisms, and the square
of `hpb` exhibits the open immersion `P ⟶ R` as a base change of `ē` along the map on arrows,
which inherits the three properties from the map on objects. -/
theorem isOpenImmersion_identity_of_isPullback_identity
    {S : Scheme.{u}} {G K H : Stacks.Groupoids.GroupoidScheme S}
    (F : G.Hom K) (i : H.Hom G)
    (hF : ∀ T, Nonempty (F.evaluation T).FullyFaithful)
    [Surjective F.mapObjects.left] [Flat F.mapObjects.left] [QuasiCompact F.mapObjects.left]
    {π : H.arrows ⟶ K.objects}
    (hpb : IsPullback i.mapArrows π F.mapArrows K.identity)
    [IsOpenImmersion i.mapArrows.left] :
    IsOpenImmersion K.identity.left := by
  let : MorphismProperty.IsStableUnderComposition
      (@Surjective : MorphismProperty Scheme.{u}) := ⟨fun _ _ _ _ => inferInstance⟩
  have hsurj : Surjective F.mapArrows.left :=
    property_arrows_of_fullyFaithful_groupoid (@Surjective) F hF inferInstance
  have hflat : Flat F.mapArrows.left :=
    property_arrows_of_fullyFaithful_groupoid (@Flat) F hF inferInstance
  have hqc : QuasiCompact F.mapArrows.left :=
    property_arrows_of_fullyFaithful_groupoid (@QuasiCompact) F hF inferInstance
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (P := @IsOpenImmersion) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (hpb.map (Over.forget S)) ⟨⟨hsurj, hflat⟩, hqc⟩
    (show IsOpenImmersion i.mapArrows.left from inferInstance)

end Stacks.Groupoids.GroupoidScheme
