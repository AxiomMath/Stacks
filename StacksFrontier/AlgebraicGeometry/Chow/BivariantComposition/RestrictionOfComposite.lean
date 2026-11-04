module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Transport
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Class
public import StacksCore.Tactic.StacksAttribute

/-!
# Restriction of a composite of bivariant classes

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `f : X ⟶ Y` and
`g : Y ⟶ Z` be morphisms of schemes locally of finite type over `S`, let `a ∈ A^p(X ⟶ Y)` and
`b ∈ A^q(Y ⟶ Z)` and let `h : W ⟶ Z` be locally of finite type. This file proves that the
restriction of Stacks 0F9Z of the composite `a ∘ b ∈ A^{p+q}(X ⟶ Z)` of Stacks 0B75 along `h` is
the composite of the restrictions:

  `res_h(a ∘ b) = res_{Y ×_Z W}(a) ∘ res_h(b)`.

## Main results

* `Stacks.Chow.isBivariantTransport_bivariantComposite_bivariantRestriction` — the identity on
  cap operations.
* `Stacks.Chow.bivariantTransport_bivariantComposite_bivariantRestriction` — the identity of
  bivariant classes.

The two sides are classes for different, but canonically identified, morphisms: `res_h(b)` is a
class for `Y ×_Z W ⟶ W` and `res(a)`, the restriction of `a` along
`pullback.fst g h : Y ×_Z W ⟶ Y`, is a class for `X ×_Y (Y ×_Z W) ⟶ Y ×_Z W`, so their composite
is a class for `X ×_Y (Y ×_Z W) ⟶ W`, while `res_h(a ∘ b)` is a class for `X ×_Z W ⟶ W`. The two
sources are the two readings of the same fibre product, identified by
`CategoryTheory.Limits.pullbackRightPullbackFstIso` — the isomorphism the composite cap operation
of Stacks 0B75 is built on — so the identity is stated through `Stacks.Chow.bivariantTransport`
along it.

## References

* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- The comparison isomorphism `X ×_Y (Y ×_Z W) ≅ X ×_Z W` lies over `W`. -/
theorem pullbackRightPullbackFstIso_hom_comp_snd {X Y Z W : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : W ⟶ Z) :
    (pullbackRightPullbackFstIso g h f).hom ≫ pullback.snd (f ≫ g) h =
      pullback.snd f (pullback.fst g h) ≫ pullback.snd g h := by
  simp

section RestrictionOfComposite

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y Z W : Scheme.{u}}
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (f : X ⟶ Y) [LocallyOfFiniteType f] (g : Y ⟶ Z)
  [LocallyOfFiniteType g] (hf : f ≫ sY = sX) (hg : g ≫ sZ = sY) (h : W ⟶ Z)
  [LocallyOfFiniteType h] (p q : ℤ) (a : BivariantClass C G sX sY f hf p)
  (b : BivariantClass C G sY sZ g hg q)

/-- **Stacks 0F9Z, compatibility with the composition of bivariant classes.** The restriction of
the composite `a ∘ b` of Stacks 0B75 along `h : W ⟶ Z` caps exactly as the composite of the
restriction of `a` along `pullback.fst g h` with the restriction of `b` along `h`, read through
the comparison isomorphism `X ×_Y (Y ×_Z W) ≅ X ×_Z W` of the two sources. -/
@[stacks 0F9Z "the clause `res(a ∘ b) = res(a) ∘ res(b)`: restriction commutes with the \
composition of bivariant classes of Tag 0B75, on cap operations, read through the comparison \
isomorphism of the two readings of the source fibre product. The compatibility with the \
composition of BASE CHANGES is the separate Stacks.Chow.bivariantRestrictionCap_comp"]
theorem isBivariantTransport_bivariantComposite_bivariantRestriction
    (hgys : G.IsNaturalUnderBaseChangeIso)
    (hgysc : G.IsNaturalUnderPullbackCompPushforward) :
    IsBivariantTransport C G (pullback.fst f (pullback.fst g h) ≫ sX)
      (pullback.fst (f ≫ g) h ≫ sX) (h ≫ sZ)
      (pullback.snd f (pullback.fst g h) ≫ pullback.snd g h)
      (comp_comp_structureMorphism_eq
        (pullbackSnd_comp_structureMorphism_eq C sX sY f hf (pullback.fst g h))
        (pullbackSnd_comp_structureMorphism_eq C sY sZ g hg h))
      (pullback.snd (f ≫ g) h)
      (pullbackSnd_comp_structureMorphism_eq C sX sZ (f ≫ g)
        (comp_comp_structureMorphism_eq hf hg) h)
      (pullbackRightPullbackFstIso g h f)
      (pullbackRightPullbackFstIso_hom_comp_snd f g h) (p + q)
      (bivariantComposite C G (pullback.fst f (pullback.fst g h) ≫ sX)
        (pullback.fst g h ≫ sY) (h ≫ sZ) (pullback.snd f (pullback.fst g h))
        (pullback.snd g h)
        (pullbackSnd_comp_structureMorphism_eq C sX sY f hf (pullback.fst g h))
        (pullbackSnd_comp_structureMorphism_eq C sY sZ g hg h) p q
        (bivariantRestriction C G sX sY f hf (pullback.fst g h) p hgys a)
        (bivariantRestriction C G sY sZ g hg h q hgys b) hgys hgysc)
      (bivariantRestriction C G sX sZ (f ≫ g) (comp_comp_structureMorphism_eq hf hg) h (p + q)
        hgys
        (bivariantComposite C G sX sY sZ f g hf hg p q a b hgys hgysc)) := by
  intro T t _ k α
  simp only [bivariantRestriction_cap, bivariantRestrictionCap_apply, bivariantComposite_cap,
    bivariantCompositeCap_apply, bivariantTransportCap_apply,
    properChowPushforward_eq_chowPushforwardOfIso, chowGroupDegreeEquiv_chowPushforwardOfIso,
    chowPushforwardOfIso_comp_apply]
  have hm : (pullbackLeftPullbackSndIso g h t).inv ≫
      (pullback.fst (pullback.snd g h) t ≫ pullback.fst g h) = pullback.fst g (t ≫ h) := by
    simp
  rw [chowGroupCongr_chowPushforwardOfIso_target C (pullback.fst g (t ≫ h) ≫ sY)
      (Category.assoc (pullback.fst (pullback.snd g h) t) (pullback.fst g h) sY).symm
      (pullbackLeftPullbackSndIso g h t).inv (by simp) (by rw [← Category.assoc]; simp) (k - q),
    a.cap_chowPushforwardOfIso (pullback.fst (pullback.snd g h) t ≫ pullback.fst g h)
      (pullbackLeftPullbackSndIso g h t).inv (pullback.fst g (t ≫ h)) hm
      (pullback.fst g (t ≫ h) ≫ sY) rfl (k - q) (by rw [← Category.assoc, hm]) _ _
      (eq_of_heq (chowGroupCongr_heq C rfl (k - q) _)),
    chowGroupDegreeEquiv_chowPushforwardOfIso, chowPushforwardOfIso_comp_apply]
  refine chowPushforwardOfIso_congr_apply C _ _ _ _ ?_ _ _ _ _
  refine pullback.hom_ext (pullback.hom_ext ?_ ?_) ?_ <;>
    simp [testBaseChangeIso, transportPullbackIso]

/-- **Stacks 0F9Z, compatibility with the composition of bivariant classes**, as an identity of
bivariant classes: the transport along `X ×_Y (Y ×_Z W) ≅ X ×_Z W` of the composite of the
restrictions is the restriction of the composite. -/
@[stacks 0F9Z "the clause `res(a ∘ b) = res(a) ∘ res(b)` as an equality of bivariant classes, \
the composition being that of Tag 0B75 and the transport the comparison isomorphism of the two \
readings of the source fibre product"]
theorem bivariantTransport_bivariantComposite_bivariantRestriction
    (hgys : G.IsNaturalUnderBaseChangeIso)
    (hgysc : G.IsNaturalUnderPullbackCompPushforward) :
    bivariantTransport C G (pullback.fst f (pullback.fst g h) ≫ sX)
        (pullback.fst (f ≫ g) h ≫ sX) (h ≫ sZ)
        (pullback.snd f (pullback.fst g h) ≫ pullback.snd g h)
        (comp_comp_structureMorphism_eq
          (pullbackSnd_comp_structureMorphism_eq C sX sY f hf (pullback.fst g h))
          (pullbackSnd_comp_structureMorphism_eq C sY sZ g hg h))
        (pullback.snd (f ≫ g) h)
        (pullbackSnd_comp_structureMorphism_eq C sX sZ (f ≫ g)
          (comp_comp_structureMorphism_eq hf hg) h)
        (pullbackRightPullbackFstIso g h f)
        (pullbackRightPullbackFstIso_hom_comp_snd f g h) (p + q) hgys
        (bivariantComposite C G (pullback.fst f (pullback.fst g h) ≫ sX)
          (pullback.fst g h ≫ sY) (h ≫ sZ) (pullback.snd f (pullback.fst g h))
          (pullback.snd g h)
          (pullbackSnd_comp_structureMorphism_eq C sX sY f hf (pullback.fst g h))
          (pullbackSnd_comp_structureMorphism_eq C sY sZ g hg h) p q
          (bivariantRestriction C G sX sY f hf (pullback.fst g h) p hgys a)
          (bivariantRestriction C G sY sZ g hg h q hgys b) hgys hgysc) =
      bivariantRestriction C G sX sZ (f ≫ g) (comp_comp_structureMorphism_eq hf hg) h (p + q)
        hgys (bivariantComposite C G sX sY sZ f g hf hg p q a b hgys hgysc) :=
  eq_of_isBivariantTransport C G _ _ _ _ _ _ _ _ _ (p + q)
    (isBivariantTransport_bivariantTransport C G _ _ _ _ _ _ _ _ _ (p + q) hgys _)
    (isBivariantTransport_bivariantComposite_bivariantRestriction C G sX sY sZ f g hf hg h p q
      a b hgys hgysc)

end RestrictionOfComposite

end Stacks.Chow

end
