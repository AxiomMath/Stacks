module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.SmoothRelativeDimensionShift
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceComposite
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.VirtualNormalCommutingEveryClass
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedFlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackProperPushforward
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Restriction versus composition and flat pullback, and classes commuting with every class

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project. **Stacks 0F9Z** attaches to
a bivariant class `c ∈ A^p(X ⟶ Y)` and a morphism `h : Y' ⟶ Y` its restriction
`res(c) ∈ A^p(X ×_Y Y' ⟶ Y')`, characterized by `res(c) ∩ α = c ∩ α`. This file proves the two
compatibilities of restriction that the proofs of Stacks 0FF4 and Stacks 0FF6 use:

* restriction of a composite (Stacks 0B75) is the composite of the restrictions,
  `res_h(a ∘ b) = res(a) ∘ res_h(b)` for `a ∈ A^p(X ⟶ P)` and `b ∈ A^q(P ⟶ Y)`, where `res(a)` is
  the restriction of `a` along `P ×_Y Y' ⟶ P`, read through the canonical isomorphism
  `X ×_P (P ×_Y Y') ≅ X ×_Y Y'`;
* restriction of a flat-pullback class (Stacks 0B78) is the flat-pullback class of the base
  change, `res_h(f^*) = (f')^*` for `f' : X ×_Y Y' ⟶ Y'`.

It then studies classes commuting with every bivariant class (Stacks 0FA2) on the completed
bivariant groups of Stacks 0FE0. A completed class commutes with every class when every term of
the tuple of homogeneous classes attached to it does. Commuting with every class is local on the
connected components of the source (Stacks 0FDZ): both sides of the identity of Stacks 0FA2 live on
a scheme decomposing along those components, and a class vanishing on a component contributes
nothing over it. From this, the completed flat-pullback class of a flat morphism of locally
constant relative dimension commutes with every class, and so does a composite of completed
classes that commute with every class.

## Main definitions

* `Stacks.Chow.componentFlatPullbackBivariantClass` — the flat pullback on one connected component
  `X_w`, extended by zero: the proper pushforward (Stacks 0EPK) along `X_w ⟶ X` of the
  flat-pullback class of `X_w ⟶ Y`.
* `Stacks.Chow.completedCommutesWithEveryClass` — a completed class commutes with every bivariant
  class.

## Main results

* `Stacks.Chow.bivariantRestriction_bivariantCompositeOfInvertible` — `res_h(a ∘ b)` is the
  transport of `res(a) ∘ res_h(b)` along `X ×_P (P ×_Y Y') ≅ X ×_Y Y'`.
* `Stacks.Chow.bivariantRestriction_flatPullbackBivariantClass` — `res_h(f^*) = (f')^*`.
* `Stacks.Chow.completedBivariantRestriction_completedFlatPullback` and
  `Stacks.Chow.completedBivariantRestriction_completedFlatPullbackOfSmooth` — `res_h(f^*) = (f')^*`
  on completions, for a flat morphism of locally constant relative dimension and for a smooth
  morphism.
* `Stacks.Chow.bivariantConnectedComponentRestriction_bivariantCompositeOfInvertible` — the
  restriction of a composite to a connected component is the composite of the restrictions.
* `Stacks.Chow.bivariantConnectedComponentRestriction_componentFlatPullbackBivariantClass` — the
  flat pullback on `X_w` extended by zero restricts on `X_w` to the flat pullback there.
* `Stacks.Chow.BivariantClass.commutesWithEveryClass_of_connectedComponentRestriction` — a class
  commutes with every class as soon as on every connected component it agrees with a class that
  does.
* `Stacks.Chow.completedCommutesWithEveryClass_completedFlatPullback`,
  `Stacks.Chow.completedCommutesWithEveryClass_completedFlatPullbackOfSmooth` and
  `Stacks.Chow.completedCommutesWithEveryClass_completedFlatPullbackOfFlatLCI` — completed flat
  pullback commutes with every class.
* `Stacks.Chow.completedCommutesWithEveryClass_completedBivariantCompositeOfInvertible` — the
  composite of completed classes commuting with every class commutes with every class.

## Implementation notes

The composite `res(a) ∘ res_h(b)` is a class for `X ×_P (P ×_Y Y') ⟶ Y'` and `res_h(a ∘ b)` one for
`X ×_Y Y' ⟶ Y'`; these sources are isomorphic and not equal, and the first class is carried to the
second by `Stacks.Chow.bivariantTransport` along
`CategoryTheory.Limits.pullbackRightPullbackFstIso`. Both cap operations push `a ∩ (b ∩ α)` forward
along isomorphisms of iterated fibre products; writing every such pushforward as a restriction
along the inverse isomorphism reduces the comparison to an equality of morphisms into a fibre
product, checked on its projections.

A degree `n` term of a completed composite is not a finite sum of composites of homogeneous terms:
its degree support is finite on each connected component but not uniformly. The composite is
therefore compared to such a finite sum one connected component at a time, which is exactly what
the componentwise criterion for commuting with every class consumes. For the same reason the flat
pullback is compared, on a connected component `X_w`, to the flat pullback on `X_w` extended by
zero, which is a global class commuting with every class by Stacks 0FBX for proper pushforward.
The same replacement computes the restriction of the completed flat pullback along a base change:
on a connected component of `X ×_Y Y'` the restriction of a class only depends on the restriction
of the class to the component of `X` below it.

The compatibility of restriction with composition is proved here for homogeneous classes only. Its
form on completions compares classes on the two sources `X ×_P (P ×_Y Y')` and `X ×_Y Y'`, whose
connected components correspond only through the canonical isomorphism, so it needs a transport of
completed classes along isomorphisms of sources
(`Stacks.Chow.completedBivariantRestriction_completedBivariantCompositeOfInvertible`).

Everything is stated at the Gysin system of the first Chern class rule of invertible modules,
`Stacks.Chow.gysinSystemOfInvertible`, where every Gysin compatibility used is a theorem; the
componentwise criterion holds for any Gysin system with the open-immersion case of Stacks 02TA.

## References

* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
* [Stacks Project, Tag 0B78](https://stacks.math.columbia.edu/tag/0B78)
* [Stacks Project, Tag 0FA2](https://stacks.math.columbia.edu/tag/0FA2)
* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
* [Stacks Project, Tag 0EPK](https://stacks.math.columbia.edu/tag/0EPK)
* [Stacks Project, Tag 0FBX](https://stacks.math.columbia.edu/tag/0FBX)
* [Stacks Project, Tag 0FF4](https://stacks.math.columbia.edu/tag/0FF4)
* [Stacks Project, Tag 0FF6](https://stacks.math.columbia.edu/tag/0FF6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Restriction of a flat-pullback class -/

section FlatRestriction

variable (C : ChowSituation.{u}) {X Y Y' : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f] [Flat f]
  (hf : f ≫ sY = sX) (h : Y' ⟶ Y) [LocallyOfFiniteType h] (r : ℕ)
  (hfr : AlgebraicGeometry.RelativeDimension f r)

/-- **Restriction of a flat pullback is flat pullback of the base change** (Stacks 0F9Z and
Stacks 0B78). For `f : X ⟶ Y` flat of relative dimension `r` and `h : Y' ⟶ Y`, the restriction
along `h` of the flat-pullback class `f^* ∈ A^{-r}(X ⟶ Y)` is the flat-pullback class of the base
change `f' : X ×_Y Y' ⟶ Y'`. On a test scheme `t : T ⟶ Y'` both cap by flat pullback along a base
change of `f` to `T`, compared through the canonical isomorphism of the two fibre products by the
isomorphism case of Stacks 02RG. -/
theorem bivariantRestriction_flatPullbackBivariantClass :
    bivariantRestriction C (gysinSystemOfInvertible C) sX sY f hf h (-(r : ℤ))
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (flatPullbackBivariantClassOfInvertible C sX sY f hf r hfr) =
      flatPullbackBivariantClassOfInvertible C (pullback.fst f h ≫ sX) (h ≫ sY) (pullback.snd f h)
          (pullbackSnd_comp_structureMorphism_eq C sX sY f hf h) r
          (relativeDimension_pullback_snd f h r hfr) := by
  refine BivariantClass.ext _ _ _ _ _ _ _ fun {T} t _ k α ↦ ?_
  apply eq_of_heq
  rw [bivariantRestriction_cap, bivariantRestrictionCap_apply]
  refine (chowPushforwardOfIso_heq_congr C _ _ _ _ (by ring : k - -(r : ℤ) = k + r) _ _
    (IsBivariantFlatPullback.cap_heq (hS1 := flatPullbackDescends C)
      (isBivariantFlatPullback_flatPullbackBivariantClassOfInvertible C _ _ _ _ _ _) (t ≫ h)
        k _)).trans ?_
  refine HEq.trans ?_ (IsBivariantFlatPullback.cap_heq (hS1 := flatPullbackDescends C)
      (isBivariantFlatPullback_flatPullbackBivariantClassOfInvertible C _ _ _ _ _ _)
      t k α).symm
  have hv' : pullback.snd f (t ≫ h) ≫ (t ≫ (h ≫ sY)) = pullback.fst f (t ≫ h) ≫ sX := by
    rw [← Category.assoc t h sY, pullbackSnd_comp_structureMorphism hf (t ≫ h)]
  have hb := flatPullbackChow_heq_congr_base C rfl (Category.assoc t h sY) rfl
    (pullbackSnd_comp_structureMorphism hf (t ≫ h)) hv' rfl
    (relativeDimension_pullbackSnd f hfr (t ≫ h)) (relativeDimension_pullbackSnd f hfr (t ≫ h))
    rfl (flatPullbackDescends C _ _ _ _ _ _ _) (flatPullbackDescends C _ _ _ _ _ _ _) _ α
    (chowGroupCongr_heq C (Category.assoc t h sY).symm k α)
  refine HEq.trans (chowPushforwardOfIso_heq_congr C _ _ _ _ rfl _ _ hb) (heq_of_eq ?_)
  have e := chowPushforwardOfIso_flatPullbackChow_eq_of_comp C (pullback.fst f (t ≫ h) ≫ sX)
    (pullback.fst (pullback.snd f h) t ≫ (pullback.fst f h ≫ sX))
    (pullback.fst (pullback.snd f h) t ≫ (pullback.fst f h ≫ sX)) (t ≫ (h ≫ sY))
    (pullback.snd f (t ≫ h)) hv' (pullback.snd (pullback.snd f h) t)
    (pullbackSnd_comp_structureMorphism (pullbackSnd_comp_structureMorphism_eq C sX sY f hf h) t)
    (pullbackLeftPullbackSndIso f h t).inv (by simp) (𝟙 _) (Category.id_comp _)
    (pullback.snd (pullback.snd f h) t) (by simp) (Category.id_comp _) r
    (relativeDimension_pullbackSnd f hfr (t ≫ h))
    (relativeDimension_pullbackSnd _ (relativeDimension_pullback_snd f h r hfr) t) k
    (flatPullbackDescends C _ _ _ _ _ _ _) (flatPullbackDescends C _ _ _ _ _ _ _) α
  rw [chowPushforwardOfIso_id] at e
  exact e.symm

end FlatRestriction

/-! ### Restriction of a composite -/

section CompositeRestriction

variable (C : ChowSituation.{u}) {X P Y Y' : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (i : X ⟶ P) [LocallyOfFiniteType i] (g : P ⟶ Y) [LocallyOfFiniteType g]
  (hi : i ≫ sP = sX) (hg : g ≫ sY = sP) (h : Y' ⟶ Y) [LocallyOfFiniteType h] (p q : ℤ)

/-- **Restriction of a composite is the composite of the restrictions** (Stacks 0F9Z and
Stacks 0B75). For `a ∈ A^p(X ⟶ P)`, `b ∈ A^q(P ⟶ Y)` and `h : Y' ⟶ Y`, the restriction of
`a ∘ b` along `h` is the composite of the restriction of `a` along `P' = P ×_Y Y' ⟶ P` with the
restriction of `b` along `h`, transported (`Stacks.Chow.bivariantTransport`) along the canonical
isomorphism `X ×_P P' ≅ X ×_Y Y'`. -/
theorem bivariantRestriction_bivariantCompositeOfInvertible
    (a : BivariantClass C (gysinSystemOfInvertible C) sX sP i hi p)
    (b : BivariantClass C (gysinSystemOfInvertible C) sP sY g hg q) :
    bivariantRestriction C (gysinSystemOfInvertible C) sX sY (i ≫ g)
        (comp_comp_structureMorphism_eq hi hg) h (p + q)
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (bivariantCompositeOfInvertible C sX sP sY i g hi hg p q a b) =
      bivariantTransport C (gysinSystemOfInvertible C)
        (pullback.fst i (pullback.fst g h) ≫ sX) (pullback.fst (i ≫ g) h ≫ sX) (h ≫ sY)
        (pullback.snd i (pullback.fst g h) ≫ pullback.snd g h)
        (comp_comp_structureMorphism_eq
          (pullbackSnd_comp_structureMorphism_eq C sX sP i hi (pullback.fst g h))
          (pullbackSnd_comp_structureMorphism_eq C sP sY g hg h))
        (pullback.snd (i ≫ g) h)
        (pullbackSnd_comp_structureMorphism_eq C sX sY (i ≫ g)
          (comp_comp_structureMorphism_eq hi hg) h)
        (pullbackRightPullbackFstIso g h i) (pullbackRightPullbackFstIso_hom_snd g h i) (p + q)
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (bivariantCompositeOfInvertible C (pullback.fst i (pullback.fst g h) ≫ sX)
          (pullback.fst g h ≫ sP) (h ≫ sY) (pullback.snd i (pullback.fst g h))
          (pullback.snd g h)
          (pullbackSnd_comp_structureMorphism_eq C sX sP i hi (pullback.fst g h))
          (pullbackSnd_comp_structureMorphism_eq C sP sY g hg h) p q
          (bivariantRestriction C (gysinSystemOfInvertible C) sX sP i hi (pullback.fst g h) p
            (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) a)
          (bivariantRestriction C (gysinSystemOfInvertible C) sP sY g hg h q
            (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) b)) := by
  refine BivariantClass.ext _ _ _ _ _ _ _ fun {T} t _ k α ↦ ?_
  rw [bivariantRestriction_cap, bivariantRestrictionCap_apply, bivariantTransport_cap,
    bivariantTransportCap_apply, bivariantCompositeOfInvertible, bivariantCompositeOfInvertible,
    bivariantComposite_cap, bivariantComposite_cap, bivariantCompositeCap_apply,
    bivariantCompositeCap_apply, bivariantRestriction_cap, bivariantRestrictionCap_apply,
    bivariantRestriction_cap, bivariantRestrictionCap_apply,
    properChowPushforward_eq_chowPushforwardOfIso, properChowPushforward_eq_chowPushforwardOfIso]
  set x := b.cap (t ≫ h) k (chowGroupCongr C (Category.assoc t h sY).symm k α)
  set z := a.cap (pullback.fst g (t ≫ h)) (k - q) x
  have he : (pullbackLeftPullbackSndIso g h t).inv ≫
      (pullback.fst (pullback.snd g h) t ≫ pullback.fst g h) = pullback.fst g (t ≫ h) := by
    simp
  rw [chowGroupCongr_chowPushforwardOfIso_target C (pullback.fst g (t ≫ h) ≫ sP) _
      (pullbackLeftPullbackSndIso g h t).inv _
      (by rw [← Category.assoc, he] : (pullbackLeftPullbackSndIso g h t).inv ≫
        ((pullback.fst (pullback.snd g h) t ≫ pullback.fst g h) ≫ sP) =
          pullback.fst g (t ≫ h) ≫ sP),
    BivariantClass.cap_chowPushforwardOfIso a _ _ (pullback.fst g (t ≫ h)) he _ rfl _ _ x x rfl,
    chowPushforwardOfIso_comp_apply, chowPushforwardOfIso_comp_apply,
    ← chowGroupDegreeEquiv_chowPushforwardOfIso, ← chowGroupDegreeEquiv_chowPushforwardOfIso,
    chowPushforwardOfIso_comp_apply, chowPushforwardOfIso_comp_apply]
  congr 1
  apply chowPushforwardOfIso_congr_apply
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp
    · simp
  · simp

end CompositeRestriction

/-! ### Commuting with every class, piece by piece -/

section Criterion

variable {C : ChowSituation.{u}} {G : GysinSystem C}

/-- The zero class commutes with every class. -/
theorem BivariantClass.commutesWithEveryClass_zero {Z X : Scheme.{u}} {sZ : Z ⟶ C.S}
    [LocallyOfFiniteType sZ] {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {f : Z ⟶ X}
    [LocallyOfFiniteType f] {hf : f ≫ sX = sZ} {p : ℤ} :
    (0 : BivariantClass C G sZ sX f hf p).CommutesWithEveryClass := by
  intro Y g _ q d
  rw [map_zero]
  exact bivariantCommute_zero_left C G sX f g p q d

/-- A sum of two classes commuting with every class commutes with every class. -/
theorem BivariantClass.CommutesWithEveryClass.add {Z X : Scheme.{u}} {sZ : Z ⟶ C.S}
    [LocallyOfFiniteType sZ] {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {f : Z ⟶ X}
    [LocallyOfFiniteType f] {hf : f ≫ sX = sZ} {p : ℤ} {c d : BivariantClass C G sZ sX f hf p}
    (hc : c.CommutesWithEveryClass) (hd : d.CommutesWithEveryClass) :
    (c + d).CommutesWithEveryClass := by
  intro Y g _ q e
  rw [map_add]
  exact bivariantCommute_add_left C G sX f g p q e (hc g q e) (hd g q e)

/-- A finite sum of classes commuting with every class commutes with every class. -/
theorem BivariantClass.commutesWithEveryClass_sum {Z X : Scheme.{u}} {sZ : Z ⟶ C.S}
    [LocallyOfFiniteType sZ] {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {f : Z ⟶ X}
    [LocallyOfFiniteType f] {hf : f ≫ sX = sZ} {p : ℤ} {ι : Type*} (s : Finset ι)
    (c : ι → BivariantClass C G sZ sX f hf p) (hc : ∀ i ∈ s, (c i).CommutesWithEveryClass) :
    (∑ i ∈ s, c i).CommutesWithEveryClass := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using BivariantClass.commutesWithEveryClass_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hc a (Finset.mem_insert_self a s)).add
      (ih fun i hi ↦ hc i (Finset.mem_insert_of_mem hi))

/-- **Chow classes are determined over the connected components.** Two classes on a scheme `W`
with a morphism `π : W ⟶ X` to a locally Noetherian scheme agree as soon as their restrictions to
the preimages of the connected components of `X` agree: these preimages decompose `W` into open
and closed subschemes. -/
theorem chowGroup_eq_of_chowGroupRestrict_preimage_connectedComponent_eq {W X : Scheme.{u}}
    [IsLocallyNoetherian X] (sW : W ⟶ C.S) [LocallyOfFiniteType sW] (π : W ⟶ X) (k : ℤ)
    {x y : chowGroup C sW k}
    (h : ∀ w : _root_.ConnectedComponents X,
      chowGroupRestrict C sW ((π ⁻¹ᵁ X.connectedComponentOpens w).ι ≫ sW)
          (π ⁻¹ᵁ X.connectedComponentOpens w).ι rfl k x =
        chowGroupRestrict C sW ((π ⁻¹ᵁ X.connectedComponentOpens w).ι ≫ sW)
          (π ⁻¹ᵁ X.connectedComponentOpens w).ι rfl k y) :
    x = y := by
  have hX : IsClopenDecomposition X.connectedComponentOpens :=
    ⟨fun _ _ h ↦ X.disjoint_connectedComponentOpens h, X.iSup_connectedComponentOpens⟩
  have hdec := IsClopenDecomposition.preimage hX π
  refine (chowGroupClopenEquiv C sW hdec k
    (rationalEquivalenceDecomposes_of_isClopenDecomposition C sW hdec k)).injective
    (funext fun i ↦ ?_)
  rw [chowGroupClopenEquiv_apply, chowGroupClopenEquiv_apply,
    chowGroupClopenRestrict_eq_chowGroupRestrict, chowGroupClopenRestrict_eq_chowGroupRestrict]
  exact h i

/-- A morphism whose image lies in an open subscheme factors through it. -/
abbrev liftToOpens {A X : Scheme.{u}} (V : X.Opens) (φ : A ⟶ X) (hφ : ∀ a : A, φ a ∈ V) :
    A ⟶ (V : Scheme.{u}) :=
  IsOpenImmersion.lift V.ι φ (by
    rintro _ ⟨a, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hφ a)

/-- If `f ≫ g` is an open immersion and `g` is one, then so is `f`. -/
private theorem isOpenImmersion_of_comp_eq {A B D : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ D)
    (k : A ⟶ D) [IsOpenImmersion g] [IsOpenImmersion k] (h : f ≫ g = k) : IsOpenImmersion f := by
  subst h
  exact IsOpenImmersion.of_comp f g

/-- **Commuting with every class is checked on the connected components.** A class
`c ∈ A^p(X ⟶ Y)` commutes with every bivariant class over `Y` as soon as, for every connected
component `X_w` of `X`, some class commuting with every class has the same restriction to `X_w`
as `c` (Stacks 0FDZ). Both sides of the identity of Stacks 0FA2 are classes on
`Z ×_Y (X ×_Y T)`, which decomposes along the connected components of `X`; on the piece over
`X_w` both sides of the identity for a class vanishing on `X_w` vanish
(`Stacks.Chow.chowGroupRestrict_cap_eq_zero_of_connectedComponentRestriction_eq_zero`, together
with Stacks 0B76 (2) along an open immersion), so there the identity for `c` is the identity for
the class that commutes. -/
theorem BivariantClass.commutesWithEveryClass_of_connectedComponentRestriction {X Y : Scheme.{u}}
    {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {sY : Y ⟶ C.S} [LocallyOfFiniteType sY] {f : X ⟶ Y}
    [LocallyOfFiniteType f] {hf : f ≫ sY = sX} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    {p : ℤ} (hgysO : G.IsNaturalUnderOpenImmersion) (c : BivariantClass C G sX sY f hf p)
    (h : ∀ w : _root_.ConnectedComponents X, ∃ e : BivariantClass C G sX sY f hf p,
      e.CommutesWithEveryClass ∧
        bivariantConnectedComponentRestriction C G sX sY f hf p hgysO e w =
          bivariantConnectedComponentRestriction C G sX sY f hf p hgysO c w) :
    c.CommutesWithEveryClass := by
  subst hf
  intro Z g _ q d
  show BivariantCommute C G sY f g p q c d
  intro T t _ k α
  set m := pullback.fst f t ≫ f
  set π := pullback.snd g m ≫ pullback.fst f t
  refine chowGroup_eq_of_chowGroupRestrict_preimage_connectedComponent_eq _ π _ fun w ↦ ?_
  obtain ⟨e, he, hew⟩ := h w
  have he' : BivariantCommute C G sY f g p q e d := he g q d
  set δ := c - e with hδdef
  have hδ : bivariantConnectedComponentRestriction C G (f ≫ sY) sY f rfl p hgysO δ w = 0 := by
    rw [hδdef, map_sub, Pi.sub_apply, hew, sub_self]
  set U := π ⁻¹ᵁ X.connectedComponentOpens w
  -- the left-hand side vanishes on the piece for `δ`
  have hL : chowGroupRestrict C _ (U.ι ≫ (pullback.fst g m ≫ (g ≫ sY))) U.ι rfl ((k - q) - p)
      (chowPushforwardOfIso C (pullback.fst f (pullback.fst g t ≫ g) ≫ (f ≫ sY))
        (pullback.fst g m ≫ (g ≫ sY)) (commuteComparisonHom f g t)
        (commuteComparisonHom_comp_structureMorphism C sY f g t) ((k - q) - p)
        (bivariantIteratedCap C G sY f g p q δ d t k α)) = 0 := by
    rw [← chowGroupRestrict_eq_chowPushforwardOfIso_of_comp_id C _ _ (commuteComparisonHom g f t)
      (commuteComparisonHom_comp_structureMorphism C sY g f t) _ _
      (commuteComparisonHom_comp_commuteComparisonHom g f t), chowGroupRestrict_comp,
      bivariantIteratedCap_apply]
    have hπ : (U.ι ≫ commuteComparisonHom g f t) ≫ pullback.fst f (pullback.fst g t ≫ g) =
        U.ι ≫ π := by
      rw [Category.assoc, commuteComparisonHom_fst]
    refine chowGroupRestrict_cap_eq_zero_of_connectedComponentRestriction_eq_zero C G (f ≫ sY) sY
      f rfl p hgysO δ w hδ _ _ _ _ _ _
      (liftToOpens (X.connectedComponentOpens w) (U.ι ≫ π) fun x ↦ ?_) ?_
    · rw [Scheme.Hom.comp_apply]
      exact x.2
    · rw [IsOpenImmersion.lift_fac, hπ]
  -- the right-hand side vanishes on the piece for `δ`
  have hR : chowGroupRestrict C _ (U.ι ≫ (pullback.fst g m ≫ (g ≫ sY))) U.ι rfl ((k - q) - p)
      (chowGroupDegreeEquiv C (pullback.fst g m ≫ (g ≫ sY)) (by ring : (k - p) - q = (k - q) - p)
        (bivariantIteratedCap C G sY g f q p d δ t k α)) = 0 := by
    rw [chowGroupRestrict_chowGroupDegreeEquiv, bivariantIteratedCap_apply]
    suffices H : chowGroupRestrict C _ (U.ι ≫ (pullback.fst g m ≫ (g ≫ sY))) U.ι rfl (k - p - q)
        (d.cap m (k - p) (chowGroupCongr C (Category.assoc (pullback.fst f t) f sY).symm (k - p)
          (δ.cap t k α))) = 0 by
      rw [H, map_zero]
    set V := pullback.fst f t ⁻¹ᵁ X.connectedComponentOpens w
    have sq := isPullback_baseChangeMapOfEq g m V.ι (V.ι ≫ m) rfl
    have : IsOpenImmersion (baseChangeMapOfEq g m V.ι (V.ι ≫ m) rfl) :=
      MorphismProperty.of_isPullback sq (P := @IsOpenImmersion) inferInstance
    have hvY : V.ι ≫ (m ≫ sY) = (V.ι ≫ m) ≫ sY := (Category.assoc _ _ _).symm
    have hbase : baseChangeMapOfEq g m V.ι (V.ι ≫ m) rfl ≫ (pullback.fst g m ≫ (g ≫ sY)) =
        pullback.fst g (V.ι ≫ m) ≫ (g ≫ sY) := by
      rw [baseChangeMapOfEq_fst_assoc]
    have hcap := BivariantClass.cap_chowGroupRestrict C G (g ≫ sY) sY g rfl q d m V.ι (V.ι ≫ m)
      rfl (baseChangeMapOfEq g m V.ι (V.ι ≫ m) rfl) sq (baseChangeMapOfEq_fst _ _ _ _ _) (k - p)
      hvY hbase (chowGroupCongr C (Category.assoc (pullback.fst f t) f sY).symm (k - p)
        (δ.cap t k α))
    have h0 : chowGroupRestrict C (m ≫ sY) ((V.ι ≫ m) ≫ sY) V.ι hvY (k - p)
        (chowGroupCongr C (Category.assoc (pullback.fst f t) f sY).symm (k - p)
          (δ.cap t k α)) = 0 := by
      rw [chowGroupRestrict_chowGroupCongr C _ _ _ V.ι (by rw [← hvY]; rfl)]
      refine chowGroupRestrict_cap_eq_zero_of_connectedComponentRestriction_eq_zero C G (f ≫ sY)
        sY f rfl p hgysO δ w hδ t k α _ V.ι _
        (liftToOpens (X.connectedComponentOpens w) (V.ι ≫ pullback.fst f t) fun x ↦ ?_) ?_
      · rw [Scheme.Hom.comp_apply]
        exact x.2
      · rw [IsOpenImmersion.lift_fac]
    rw [h0, map_zero] at hcap
    -- the piece `U` lies in the base change of `V`
    set ψ := liftToOpens V (U.ι ≫ pullback.snd g m) fun x ↦ x.2
    have hψ : ψ ≫ V.ι = U.ι ≫ pullback.snd g m := IsOpenImmersion.lift_fac _ _ _
    have hφc : (U.ι ≫ pullback.fst g m) ≫ g = ψ ≫ (V.ι ≫ m) := by
      rw [← Category.assoc, hψ, Category.assoc, Category.assoc, pullback.condition]
    set φ := pullback.lift _ _ hφc
    have he : φ ≫ baseChangeMapOfEq g m V.ι (V.ι ≫ m) rfl = U.ι := by
      apply pullback.hom_ext
      · rw [Category.assoc, baseChangeMapOfEq_fst, pullback.lift_fst]
      · rw [Category.assoc, baseChangeMapOfEq_snd, pullback.lift_snd_assoc, hψ]
    have := isOpenImmersion_of_comp_eq φ _ _ he
    have hU : φ ≫ (pullback.fst g (V.ι ≫ m) ≫ (g ≫ sY)) =
        U.ι ≫ (pullback.fst g m ≫ (g ≫ sY)) := by
      rw [← hbase, ← Category.assoc, he]
    rw [chowGroupRestrict_congr C _ _ _ _ _ (φ ≫ baseChangeMapOfEq g m V.ι (V.ι ≫ m) rfl)
      he.symm (by rw [Category.assoc, hbase, hU]), ← chowGroupRestrict_comp C _ _ _ hbase _ _ _ hU,
      hcap, map_zero]
  have hsubL : bivariantIteratedCap C G sY f g p q c d t k α =
      bivariantIteratedCap C G sY f g p q e d t k α +
        bivariantIteratedCap C G sY f g p q δ d t k α := by
    simp only [bivariantIteratedCap_apply, hδdef, BivariantClass.sub_cap, add_sub_cancel]
  have hsubR : bivariantIteratedCap C G sY g f q p d c t k α =
      bivariantIteratedCap C G sY g f q p d e t k α +
        bivariantIteratedCap C G sY g f q p d δ t k α := by
    simp only [bivariantIteratedCap_apply, hδdef, BivariantClass.sub_cap, map_sub,
      add_sub_cancel]
  rw [hsubL, hsubR, map_add, map_add, map_add, map_add, hL, hR, add_zero, add_zero, he' t k α]


end Criterion

/-! ### Restriction of a composite to a piece -/

section PieceComposite

variable (C : ChowSituation.{u}) {X Y Z : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (f : X ⟶ Y) [LocallyOfFiniteType f] (g : Y ⟶ Z) [LocallyOfFiniteType g]
  (hf : f ≫ sY = sX) (hg : g ≫ sZ = sY) {I J K : Type u} (UX : I → X.Opens) (UY : J → Y.Opens)
  (UZ : K → Z.Opens) (a : I → J) (b : J → K) (ha : ∀ i, UX i ≤ f ⁻¹ᵁ UY (a i))
  (hb : ∀ j, UY j ≤ g ⁻¹ᵁ UZ (b j)) (hab : ∀ i, UX i ≤ (f ≫ g) ⁻¹ᵁ UZ (b (a i))) (p q : ℤ)

/-- **Restriction to a piece of a composite** (Stacks 0FDZ and Stacks 0B75). The restriction of
`a ∘ b ∈ A^{p+q}(X ⟶ Z)` to a piece `X_i` is the composite of the restriction of `a` to `X_i`
with the restriction of `b` to the piece `Y_{a(i)}` it lands in. The two are classes for the
equal morphisms `X_i ⟶ Z_{b(a(i))}` (`Stacks.Chow.pieceMap_comp`), whence the heterogeneous
equality. On a test scheme both cap by restricting `a ∩ (b ∩ α)` to the same open subscheme,
by Stacks 0B76 (2) along an open immersion. -/
theorem bivariantPieceRestriction_bivariantCompositeOfInvertible_heq (i : I)
    (x : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p)
    (y : BivariantClass C (gysinSystemOfInvertible C) sY sZ g hg q) :
    bivariantPieceRestriction C (gysinSystemOfInvertible C) sX sZ (f ≫ g)
        (comp_comp_structureMorphism_eq hf hg) (p + q) UX UZ (b ∘ a) hab i
        (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
        (bivariantCompositeOfInvertible C sX sY sZ f g hf hg p q x y) ≍
      bivariantCompositeOfInvertible C ((UX i).ι ≫ sX) ((UY (a i)).ι ≫ sY)
        ((UZ (b (a i))).ι ≫ sZ) (pieceMap f UX UY a ha i) (pieceMap g UY UZ b hb (a i))
        (pieceMap_comp_structureMorphism C sX sY f hf UX UY a ha i)
        (pieceMap_comp_structureMorphism C sY sZ g hg UY UZ b hb (a i)) p q
        (bivariantPieceRestriction C (gysinSystemOfInvertible C) sX sY f hf p UX UY a ha i
          (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C) x)
        (bivariantPieceRestriction C (gysinSystemOfInvertible C) sY sZ g hg q UY UZ b hb (a i)
          (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C) y) := by
  refine BivariantClass.heq_of_congrHom_cap_heq
    (@id (pieceMap (f ≫ g) UX UZ (b ∘ a) hab i =
      pieceMap f UX UY a ha i ≫ pieceMap g UY UZ b hb (a i))
      (pieceMap_comp f g UX UY UZ a b ha hb i))
    rfl _ _
    fun {S} s _ k β ↦ heq_of_eq ?_
  rw [bivariantPieceRestriction_cap, bivariantPieceRestrictionCap_apply,
    bivariantCompositeOfInvertible, bivariantCompositeOfInvertible, bivariantComposite_cap,
    bivariantComposite_cap, bivariantCompositeCap_apply, bivariantCompositeCap_apply,
    bivariantPieceRestriction_cap, bivariantPieceRestrictionCap_apply,
    bivariantPieceRestriction_cap, bivariantPieceRestrictionCap_apply,
    properChowPushforward_eq_chowPushforwardOfIso, properChowPushforward_eq_chowPushforwardOfIso,
    chowGroupRestrict_chowGroupDegreeEquiv, ← chowGroupDegreeEquiv_chowPushforwardOfIso]
  set t := s ≫ (UZ (b (a i))).ι
  set gj := pieceMap g UY UZ b hb (a i)
  set fi := pieceMap f UX UY a ha i
  set X₀ := y.cap t k (chowGroupCongr C (Category.assoc s (UZ (b (a i))).ι sZ).symm k β)
  set pcg := pieceComparison g UY UZ b hb (a i) s
  set m := pullback.fst gj s ≫ (UY (a i)).ι
  have hm : pcg ≫ pullback.fst g t = m := opensPullbackComparison_fst _ _ _ _ _ _
  have sq := isPullback_baseChangeMapOfEq f (pullback.fst g t) pcg m hm
  have : IsOpenImmersion (baseChangeMapOfEq f (pullback.fst g t) pcg m hm) :=
    MorphismProperty.of_isPullback sq (P := @IsOpenImmersion) inferInstance
  have hvY : pcg ≫ (pullback.fst g t ≫ sY) = m ≫ sY := by rw [← Category.assoc, hm]
  have hbase : baseChangeMapOfEq f (pullback.fst g t) pcg m hm ≫
        (pullback.fst f (pullback.fst g t) ≫ sX) =
      pullback.fst f m ≫ sX := by
    rw [baseChangeMapOfEq_fst_assoc]
  have hcap := BivariantClass.cap_chowGroupRestrict C (gysinSystemOfInvertible C) sX sY f hf p x
    (pullback.fst g t) pcg m hm (baseChangeMapOfEq f (pullback.fst g t) pcg m hm) sq
    (baseChangeMapOfEq_fst _ _ _ _ _) (k - q) hvY hbase X₀
  rw [chowGroupCongr_chowGroupRestrict C _ _ _ pcg _ hvY, ← hcap]
  congr 1
  rw [chowPushforwardOfIso_hom_eq_chowGroupRestrict, chowPushforwardOfIso_hom_eq_chowGroupRestrict,
    chowPushforwardOfIso_hom_eq_chowGroupRestrict, chowGroupRestrict_comp, chowGroupRestrict_comp,
    chowGroupRestrict_comp, chowGroupRestrict_comp]
  apply DFunLike.congr_fun
  apply chowGroupRestrict_congr
  dsimp only [Function.comp_apply]
  apply pullback.hom_ext
  · simp [gj, t, pcg, m, pieceComparison]
  · apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [← pullback.condition]
      simp only [gj, t, pcg, m, pieceComparison, baseChangeMapOfEq_fst_assoc,
        pullbackRightPullbackFstIso_inv_fst_assoc]
      have hpc : opensPullbackComparison (f ≫ g) (UX i) (UZ ((b ∘ a) i))
          (pieceMap (f ≫ g) UX UZ (b ∘ a) hab i) (pieceMap_comp_ι _ _ _ _ _ i) s ≫
            pullback.fst (f ≫ g) (s ≫ (UZ (b (a i))).ι) =
          pullback.fst (pieceMap (f ≫ g) UX UZ (b ∘ a) hab i) s ≫ (UX i).ι :=
        opensPullbackComparison_fst _ _ _ _ _ _
      have hpc' : opensPullbackComparison f (UX i) (UY (a i)) (pieceMap f UX UY a ha i)
          (pieceMap_comp_ι _ _ _ _ _ i) (pullback.fst (pieceMap g UY UZ b hb (a i)) s) ≫
            pullback.fst f (pullback.fst (pieceMap g UY UZ b hb (a i)) s ≫ (UY (a i)).ι) =
          pullback.fst (pieceMap f UX UY a ha i) (pullback.fst (pieceMap g UY UZ b hb (a i)) s) ≫
            (UX i).ι :=
        opensPullbackComparison_fst _ _ _ _ _ _
      rw [reassoc_of% hpc, reassoc_of% hpc', pullbackRightPullbackFstIso_inv_fst_assoc]
      simp [pullback.congrHom]
    · simp only [gj, t, pcg, m, pieceComparison, Category.assoc,
        pullbackRightPullbackFstIso_inv_snd_snd,
        baseChangeMapOfEq_snd_assoc, opensPullbackComparison_snd, opensPullbackComparison_snd_assoc]
      simp

/-- Restriction to a piece does not see how the index map of the pieces is written. -/
theorem bivariantPieceRestriction_heq_of_index {G : GysinSystem C} {I J : Type u}
    (UX : I → X.Opens) (UY : J → Y.Opens) {a₁ a₂ : I → J} (h : a₁ = a₂)
    (ha₁ : ∀ i, UX i ≤ f ⁻¹ᵁ UY (a₁ i)) (ha₂ : ∀ i, UX i ≤ f ⁻¹ᵁ UY (a₂ i)) (i : I)
    (hgysO : G.IsNaturalUnderOpenImmersion) (x : BivariantClass C G sX sY f hf p) :
    bivariantPieceRestriction C G sX sY f hf p UX UY a₁ ha₁ i hgysO x ≍
      bivariantPieceRestriction C G sX sY f hf p UX UY a₂ ha₂ i hgysO x := by
  subst h
  rfl

variable [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]

/-- **Restriction to a connected component of a composite** (Stacks 0FDZ and Stacks 0B75). On a
connected component `X_w` of `X`, the restriction of `a ∘ b ∈ A^{p+q}(X ⟶ Z)` is the composite of
the restriction of `a` to `X_w` with the restriction of `b` to the component `Y_{a(w)}` it lands
in, read in the factor of the completed group of `f ≫ g` through
`Stacks.Chow.completedBivariantCompositeTransport`. -/
theorem bivariantConnectedComponentRestriction_bivariantCompositeOfInvertible
    (x : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p)
    (y : BivariantClass C (gysinSystemOfInvertible C) sY sZ g hg q)
    (w : _root_.ConnectedComponents X) :
    bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C) sX sZ (f ≫ g)
        (comp_comp_structureMorphism_eq hf hg) (p + q)
        (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
        (bivariantCompositeOfInvertible C sX sY sZ f g hf hg p q x y) w =
      completedBivariantCompositeTransport C (gysinSystemOfInvertible C) sX sY sZ f g hf hg w
        (p + q)
        (bivariantCompositeOfInvertible C _ _ _ (f.resConnectedComponent w)
          (g.resConnectedComponent (f.continuous.connectedComponentsMap w))
          (f.resConnectedComponent_comp_ι_comp hf w) (g.resConnectedComponent_comp_ι_comp hg _)
          p q
          (bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C) sX sY f hf p
            (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C) x w)
          (bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C) sY sZ g hg q
            (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C) y
            (f.continuous.connectedComponentsMap w))) := by
  refine eq_of_heq (HEq.trans ?_ (bivariantClassComponentCongr_heq C _ _ _ _ _ _ _ _ _ _).symm)
  have hcomp : (f ≫ g).continuous.connectedComponentsMap =
      g.continuous.connectedComponentsMap ∘ f.continuous.connectedComponentsMap :=
    funext (Scheme.Hom.connectedComponentsMap_comp f g)
  have hab : ∀ i, X.connectedComponentOpens i ≤ (f ≫ g) ⁻¹ᵁ Z.connectedComponentOpens
      ((g.continuous.connectedComponentsMap ∘ f.continuous.connectedComponentsMap) i) := by
    intro i
    rw [← hcomp]
    exact (f ≫ g).connectedComponentOpens_le_preimage i
  refine (bivariantPieceRestriction_heq_of_index C sX sZ (f ≫ g)
    (comp_comp_structureMorphism_eq hf hg) (p + q) X.connectedComponentOpens
    Z.connectedComponentOpens hcomp _ hab w (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
    (bivariantCompositeOfInvertible C sX sY sZ f g hf hg p q x y)).trans ?_
  exact bivariantPieceRestriction_bivariantCompositeOfInvertible_heq C sX sY sZ f g hf hg
    X.connectedComponentOpens Y.connectedComponentOpens Z.connectedComponentOpens
    f.continuous.connectedComponentsMap g.continuous.connectedComponentsMap
    f.connectedComponentOpens_le_preimage g.connectedComponentOpens_le_preimage _ p q w x y

end PieceComposite

/-! ### The flat pullback on one connected component, extended by zero -/

section ComponentFlatPullback

/-- The inclusion of a connected component of a locally Noetherian scheme is a closed immersion:
the component is open and closed. -/
@[sga "3 X 5.11.0"]
instance isClosedImmersion_connectedComponentOpens_ι {X : Scheme.{u}} [IsLocallyNoetherian X]
    (w : _root_.ConnectedComponents X) : IsClosedImmersion (X.connectedComponentOpens w).ι where
  isClosedEmbedding := ⟨(X.connectedComponentOpens w).ι.isOpenEmbedding.isEmbedding, by
    rw [Scheme.Opens.range_ι]
    exact X.isClosed_connectedComponentOpens w⟩

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f] [Flat f]
  (hf : f ≫ sY = sX) [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  (w : _root_.ConnectedComponents X) (r : ℕ)
  (hr : AlgebraicGeometry.RelativeDimension (f.resConnectedComponent w) r)

include hr in
/-- If the restriction of `f` to the connected component `X_w` has relative dimension `r`, so
does the composite `X_w ⟶ X ⟶ Y`. -/
theorem relativeDimension_connectedComponentOpens_ι_comp :
    AlgebraicGeometry.RelativeDimension ((X.connectedComponentOpens w).ι ≫ f) r := by
  have h := AlgebraicGeometry.RelativeDimension.comp_of_flat (f.resConnectedComponent w) _ hr
    (relativeDimension_of_isOpenImmersion
      (Y.connectedComponentOpens (f.continuous.connectedComponentsMap w)).ι)
  rw [Nat.add_zero] at h
  exact AlgebraicGeometry.RelativeDimension.of_comp_isOpenImmersion _ (𝟙 Y) _
    (by rw [Category.comp_id, Scheme.Hom.resConnectedComponent_comp_ι]) h

/-- **The flat pullback on a connected component, extended by zero.** For a flat morphism
`f : X ⟶ Y` whose restriction to the connected component `X_w` has relative dimension `r`, the
class `ι_* ∘ (ι ≫ f)^* ∈ A^{-r}(X ⟶ Y)`, the proper pushforward (Stacks 0EPK) along the inclusion
`ι : X_w ⟶ X`, which is a closed immersion, of the flat-pullback class (Stacks 0B78) of
`X_w ⟶ Y`. -/
def componentFlatPullbackBivariantClass :
    BivariantClass C (gysinSystemOfInvertible C) sX sY f hf (-(r : ℤ)) :=
  bivariantProperPushforwardOfInvertible C ((X.connectedComponentOpens w).ι ≫ sX) sX sY
    (X.connectedComponentOpens w).ι f rfl hf (-(r : ℤ))
    (flatPullbackBivariantClassOfInvertible C ((X.connectedComponentOpens w).ι ≫ sX) sY
        ((X.connectedComponentOpens w).ι ≫ f) (comp_comp_structureMorphism_eq rfl hf) r
        (relativeDimension_connectedComponentOpens_ι_comp f w r hr))

/-- The flat pullback on a connected component, extended by zero, commutes with every class:
flat pullback does (Stacks 0FF6 for smooth morphisms, in the generality of Stacks 0B78), and
proper pushforward preserves this (Stacks 0FBX). -/
theorem commutesWithEveryClass_componentFlatPullbackBivariantClass :
    (componentFlatPullbackBivariantClass C sX sY f hf w r hr).CommutesWithEveryClass :=
  commutesWithEveryClass_bivariantProperPushforward _ f rfl hf _
    (commutesWithEveryClass_flatPullbackBivariantClass _ r _ (flatPullbackDescends C) _
      (isBivariantFlatPullback_flatPullbackBivariantClassOfInvertible C _ _ _ _ _ _))

/-- **The flat pullback on a connected component, extended by zero, restricts to the flat
pullback there.** The restriction (Stacks 0FDZ) of `ι_* ∘ (ι ≫ f)^*` to `X_w` is the
flat-pullback class of `X_w ⟶ Y_{w'}`: on a test scheme, restricting the pushforward along the
open and closed immersion `X_w ×_Y T ⟶ X ×_Y T` to its image undoes it. -/
theorem bivariantConnectedComponentRestriction_componentFlatPullbackBivariantClass :
    bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C) sX sY f hf (-(r : ℤ))
        (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
        (componentFlatPullbackBivariantClass C sX sY f hf w r hr) w =
      flatPullbackBivariantClassOfInvertible C ((X.connectedComponentOpens w).ι ≫ sX)
          ((Y.connectedComponentOpens (f.continuous.connectedComponentsMap w)).ι ≫ sY)
          (f.resConnectedComponent w) (f.resConnectedComponent_comp_ι_comp hf w) r hr := by
  refine BivariantClass.ext _ _ _ _ _ _ _ fun {S} s _ k β ↦ ?_
  rw [bivariantConnectedComponentRestriction_cap, componentFlatPullbackBivariantClass,
    bivariantProperPushforwardOfInvertible_cap, bivariantProperPushforwardCap_apply]
  set ιX := (X.connectedComponentOpens w).ι
  set ιY := (Y.connectedComponentOpens (f.continuous.connectedComponentsMap w)).ι
  set fw := f.resConnectedComponent w
  set t := s ≫ ιY
  have hc : pullback.fst (ιX ≫ f) t ≫ fw = pullback.snd (ιX ≫ f) t ≫ s := by
    rw [← cancel_mono ιY, Category.assoc, Scheme.Hom.resConnectedComponent_comp_ι, Category.assoc]
    exact pullback.condition
  have hc' : (pullback.fst fw s ≫ ιX) ≫ f = pullback.snd fw s ≫ t := by
    rw [Category.assoc, ← Scheme.Hom.resConnectedComponent_comp_ι, ← Category.assoc,
      pullback.condition, Category.assoc]
  let θ : pullback (ιX ≫ f) t ≅ pullback fw s :=
    { hom := pullback.lift _ _ hc
      inv := pullback.lift (pullback.fst fw s) (pullback.snd fw s)
        (by rw [← Category.assoc]; exact hc')
      hom_inv_id := by
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.id_comp]
        · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.id_comp]
      inv_hom_id := by
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.id_comp]
        · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.id_comp] }
  have hθq : θ.hom ≫ opensPullbackComparison f (X.connectedComponentOpens w)
      (Y.connectedComponentOpens (f.continuous.connectedComponentsMap w)) fw
      (Scheme.Hom.resConnectedComponent_comp_ι f w) s =
      bivariantPushforwardBaseChange ιX f t := by
    apply pullback.hom_ext
    · rw [Category.assoc, opensPullbackComparison_fst, bivariantPushforwardBaseChange_fst]
      exact pullback.lift_fst_assoc _ _ _ _
    · rw [Category.assoc, opensPullbackComparison_snd, bivariantPushforwardBaseChange_snd]
      exact pullback.lift_snd _ _ _
  have hθs : θ.hom ≫ (pullback.fst fw s ≫ (ιX ≫ sX)) = pullback.fst (ιX ≫ f) t ≫ (ιX ≫ sX) :=
    pullback.lift_fst_assoc _ _ _ _
  have : IsIso θ.hom := Iso.isIso_hom θ
  have : IsProper θ.hom := by infer_instance
  rw [chowGroupRestrict_properChowPushforward C _ _ _ _ (bivariantPushforwardBaseChange ιX f t) _
    (𝟙 _) (Category.id_comp _) _ _ θ.hom hθs
    (IsPullback.of_horiz_isIso_mono ⟨by rw [Category.id_comp, hθq]⟩) _ _
    (properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ θ.hom hθs _),
    chowGroupRestrict_id, properChowPushforward_eq_chowPushforwardOfIso]
  have hθv : pullback.snd (ιX ≫ f) t ≫ 𝟙 S = θ.hom ≫ pullback.snd fw s :=
    (Category.comp_id _).trans (pullback.lift_snd _ _ _).symm
  have hd : pullback.snd (ιX ≫ f) t ≫ (t ≫ sY) = pullback.fst (ιX ≫ f) t ≫ (ιX ≫ sX) :=
    pullbackSnd_comp_structureMorphism (comp_comp_structureMorphism_eq rfl hf) t
  have hv : pullback.snd fw s ≫ (s ≫ (ιY ≫ sY)) = pullback.fst fw s ≫ (ιX ≫ sX) :=
    pullbackSnd_comp_structureMorphism (f.resConnectedComponent_comp_ι_comp hf w) s
  have key := flatPullbackChow_chowPushforwardOfIso C (t ≫ sY) _ (s ≫ (ιY ≫ sY)) _ (𝟙 S)
    (by rw [Category.id_comp, Category.assoc]) θ.hom hθs (pullback.snd (ιX ≫ f) t) hd
    (pullback.snd fw s) hv hθv r (relativeDimension_pullbackSnd _
      (relativeDimension_connectedComponentOpens_ι_comp f w r hr) t)
    (relativeDimension_pullbackSnd _ hr s) k (flatPullbackDescends C _ _ _ _ _ _ _)
    (flatPullbackDescends C _ _ _ _ _ _ _)
    (chowGroupCongr C (Category.assoc s ιY sY).symm k β)
  refine eq_of_heq (HEq.trans (chowPushforwardOfIso_heq_congr C _ _ _ _ (by ring) _ _
    (IsBivariantFlatPullback.cap_heq (hS1 := flatPullbackDescends C)
      (isBivariantFlatPullback_flatPullbackBivariantClassOfInvertible C _ _ _ _ _ _) t k _)) ?_)
  refine HEq.trans (heq_of_eq key.symm) ?_
  refine HEq.trans ?_ (IsBivariantFlatPullback.cap_heq (hS1 := flatPullbackDescends C)
      (isBivariantFlatPullback_flatPullbackBivariantClassOfInvertible C _ _ _ _ _ _)
      s k β).symm
  refine flatPullbackChow_heq_congr C _ _ _ _ _ _ rfl rfl _ _ rfl _ _ _ _ ?_
  exact (chowPushforwardOfIso_heq_of_eq_id _ rfl _ _).trans (chowGroupCongr_heq C _ _ _)

end ComponentFlatPullback

/-! ### Completed classes commuting with every class -/

section CompletedCommute

variable {C : ChowSituation.{u}}

/-- A composite of two classes commuting with every class commutes with every class, for classes
whose structure morphisms are arbitrary. -/
theorem BivariantClass.CommutesWithEveryClass.bivariantCompositeOfInvertible {X Y Z : Scheme.{u}}
    {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]
    {sZ : Z ⟶ C.S} [LocallyOfFiniteType sZ] {f : X ⟶ Y} [LocallyOfFiniteType f] {g : Y ⟶ Z}
    [LocallyOfFiniteType g] {hf : f ≫ sY = sX} {hg : g ≫ sZ = sY} {p q : ℤ}
    {a : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p}
    {b : BivariantClass C (gysinSystemOfInvertible C) sY sZ g hg q}
    (ha : a.CommutesWithEveryClass) (hb : b.CommutesWithEveryClass) :
    (Stacks.Chow.bivariantCompositeOfInvertible C sX sY sZ f g hf hg p q a b).CommutesWithEveryClass
      := by
  subst hg
  exact commutesWithEveryClass_bivariantCompositeOfInvertible f g hf p q a b ha hb

variable (C) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
  [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : f ≫ sY = sX)
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y]

/-- **Commuting with every class, on completions** (Stacks 0FA2 on Stacks 0FE0). A completed
bivariant class `c ∈ A^*(X ⟶ Y)^∧` *commutes with every bivariant class* when every term
`c_n ∈ A^n(X ⟶ Y)` of the tuple attached to it by Stacks 0FE0 does. This is the sense in which
Stacks 0FF6 asserts that the Gysin class of a local complete intersection morphism, after any base
change, commutes with every bivariant class. -/
def completedCommutesWithEveryClass
    (c : completedBivariantGroup C (gysinSystemOfInvertible C) sX sY f hf) : Prop :=
  ∀ n : ℤ, (completedBivariantSequenceOfInvertible C sX sY f hf c n).CommutesWithEveryClass

/-- **Commuting with every class is checked componentwise on completions.** A completed class
commutes with every class as soon as, on each connected component `X_w` of `X` and in each
degree `n`, its component agrees with the restriction to `X_w` of some homogeneous class of degree
`n` commuting with every class. -/
theorem completedCommutesWithEveryClass_of_connectedComponent
    (c : completedBivariantGroup C (gysinSystemOfInvertible C) sX sY f hf)
    (h : ∀ (w : _root_.ConnectedComponents X) (n : ℤ),
      ∃ e : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf n, e.CommutesWithEveryClass ∧
        bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C) sX sY f hf n
          (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C) e w = c w n) :
    completedCommutesWithEveryClass C sX sY f hf c := fun n ↦
  BivariantClass.commutesWithEveryClass_of_connectedComponentRestriction
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C) _ fun w ↦
      (h w n).imp fun _ he ↦ ⟨he.1, he.2.trans (restriction_completedBivariantSequence C
        (gysinSystemOfInvertible C) sX sY f hf
        (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
        (gysinSystemOfInvertible_isNaturalUnderOpensRestriction C)
        (gysinSystemOfInvertible_isNaturalUnderPullbackComp C) c n w).symm⟩

/-- **Flat pullback commutes with every class, on completions.** The completed flat-pullback
class `f^* ∈ A^*(X ⟶ Y)^∧` of a flat morphism whose relative dimension is constant on each
connected component commutes with every bivariant class: on a connected component `X_w` its only
nonzero term is the flat pullback there, which is the restriction of the flat pullback on `X_w`
extended by zero (`Stacks.Chow.componentFlatPullbackBivariantClass`), and that class commutes with
every class. -/
theorem completedCommutesWithEveryClass_completedFlatPullback [Flat f]
    (hrel : ∀ a : _root_.ConnectedComponents X,
      ∃ r : ℕ, AlgebraicGeometry.RelativeDimension (f.resConnectedComponent a) r) :
    completedCommutesWithEveryClass C sX sY f hf (completedFlatPullback C sX sY f hf hrel) := by
  refine completedCommutesWithEveryClass_of_connectedComponent C sX sY f hf _ fun w n ↦ ?_
  rw [completedFlatPullback_apply]
  by_cases hn : -(flatComponentRelativeDimension f hrel w : ℤ) = n
  · subst hn
    refine ⟨componentFlatPullbackBivariantClass C sX sY f hf w _
      (relativeDimension_flatComponentRelativeDimension f hrel w),
      commutesWithEveryClass_componentFlatPullbackBivariantClass C sX sY f hf w _ _, ?_⟩
    rw [bivariantConnectedComponentRestriction_componentFlatPullbackBivariantClass,
      DirectSum.of_eq_same]
  · refine ⟨0, BivariantClass.commutesWithEveryClass_zero, ?_⟩
    rw [map_zero, Pi.zero_apply]
    exact (DirectSum.of_eq_of_ne (β := fun n ↦ BivariantClass C (gysinSystemOfInvertible C)
      ((X.connectedComponentOpens w).ι ≫ sX)
      ((Y.connectedComponentOpens (f.continuous.connectedComponentsMap w)).ι ≫ sY)
      (f.resConnectedComponent w) (f.resConnectedComponent_comp_ι_comp hf w) n)
      (-(flatComponentRelativeDimension f hrel w : ℤ)) n _ (Ne.symm hn)).symm

/-- **Smooth pullback commutes with every class, on completions.** The completed flat-pullback
class `g^* ∈ A^*(P ⟶ Y)^∧` of a smooth morphism commutes with every bivariant class. -/
theorem completedCommutesWithEveryClass_completedFlatPullbackOfSmooth [Smooth f] :
    completedCommutesWithEveryClass C sX sY f hf (completedFlatPullbackOfSmooth C sX sY f hf) := by
  rw [completedFlatPullbackOfSmooth_eq_completedFlatPullback C sX sY f hf
    fun a ↦ ⟨_, relativeDimension_smoothComponentRelativeDimension f a⟩]
  exact completedCommutesWithEveryClass_completedFlatPullback C sX sY f hf _

/-- **The completed flat pullback of a flat local complete intersection morphism commutes with
every class.** -/
theorem completedCommutesWithEveryClass_completedFlatPullbackOfFlatLCI [Flat f]
    (hlci : IsLocalCompleteIntersectionMorphism f) :
    completedCommutesWithEveryClass C sX sY f hf
      (completedFlatPullbackOfFlatLCI C sX sY f hf hlci) :=
  completedCommutesWithEveryClass_completedFlatPullback C sX sY f hf _

/-- Restriction to a connected component of a class read in an equal degree. -/
theorem bivariantConnectedComponentRestriction_copy_heq {p p' : ℤ} (hpp' : p = p')
    (x : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p)
    (w : _root_.ConnectedComponents X) :
    bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C) sX sY f hf p'
        (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
        (BivariantClass.copy C (gysinSystemOfInvertible C) sX sY rfl hf hf hpp' x) w ≍
      bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C) sX sY f hf p
        (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C) x w := by
  subst hpp'
  rfl

/-- **The degree `n` part of a completed composite on a connected component** is the restriction
of a finite sum of homogeneous composites. On the connected component `X_w`, the degree `n` part of
`c ∘ d ∈ A^*(X ⟶ Z)^∧` (Stacks 0FE0) is the restriction to `X_w` of `∑_{p ∈ s} c_p ∘ d_{n-p}`, for
any finite set `s` of degrees containing those in which `c` is nonzero on `X_w`, where `c_p` and
`d_q` are the terms of the tuples attached to `c` and `d`
(`Stacks.Chow.bivariantConnectedComponentRestriction_bivariantCompositeOfInvertible`). -/
theorem bivariantConnectedComponentRestriction_sum_bivariantCompositeOfInvertible
    {Z : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (g : Y ⟶ Z)
    [LocallyOfFiniteType g] (hg : g ≫ sZ = sY) [IsLocallyNoetherian Z]
    (c : completedBivariantGroup C (gysinSystemOfInvertible C) sX sY f hf)
    (d : completedBivariantGroup C (gysinSystemOfInvertible C) sY sZ g hg)
    (w : _root_.ConnectedComponents X) (n : ℤ) (s : Finset ℤ) (hs : ∀ p, c w p ≠ 0 → p ∈ s) :
    bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C) sX sZ (f ≫ g)
        (comp_comp_structureMorphism_eq hf hg) n
        (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
        (∑ p ∈ s, BivariantClass.copy C (gysinSystemOfInvertible C) sX sZ rfl
          (comp_comp_structureMorphism_eq hf hg) (comp_comp_structureMorphism_eq hf hg)
          (by ring : p + (n - p) = n)
          (bivariantCompositeOfInvertible C sX sY sZ f g hf hg p (n - p)
            (completedBivariantSequenceOfInvertible C sX sY f hf c p)
            (completedBivariantSequenceOfInvertible C sY sZ g hg d (n - p)))) w =
      completedBivariantCompositeOfInvertible C sX sY sZ f g hf hg c d w n := by
  set cs := completedBivariantSequenceOfInvertible C sX sY f hf c
  set ds := completedBivariantSequenceOfInvertible C sY sZ g hg d
  have hcs : ∀ p, bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C) sX sY f hf p
      (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C) (cs p) w = c w p := fun p ↦
    restriction_completedBivariantSequence C (gysinSystemOfInvertible C) sX sY f hf _ _ _ c p w
  have hds : ∀ q, bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C) sY sZ g hg q
      (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C) (ds q)
        (f.continuous.connectedComponentsMap w) = d (f.continuous.connectedComponentsMap w) q :=
    fun q ↦ restriction_completedBivariantSequence C (gysinSystemOfInvertible C) sY sZ g hg _ _ _
      d q _
  have hcw : ∑ p ∈ s, DirectSum.of _ p (c w p) = c w := by
    classical
    refine Eq.trans ?_ (DirectSum.sum_support_of (c w))
    refine (Finset.sum_subset (fun p hp ↦ hs p (DFinsupp.mem_support_iff.1 hp)) ?_).symm
    intro p _ hp
    rw [DFinsupp.notMem_support_iff.1 hp, map_zero]
  rw [map_sum, Finset.sum_apply, completedBivariantCompositeOfInvertible,
    completedBivariantComposite_apply]
  conv_rhs => rw [← hcw]
  rw [map_sum, AddMonoidHom.finset_sum_apply, map_sum, DFinsupp.finset_sum_apply]
  refine Finset.sum_congr rfl fun p _ ↦ eq_of_heq ?_
  refine (bivariantConnectedComponentRestriction_copy_heq C sX sZ (f ≫ g) _ _ _ w).trans ?_
  rw [bivariantConnectedComponentRestriction_bivariantCompositeOfInvertible, hcs, hds]
  refine (bivariantClassComponentCongr_heq C _ _ _ _ _ _ _ _ _ _).trans ?_
  rw [DFinsupp.mapRange.addEquiv_apply, DFinsupp.mapRange_apply]
  refine HEq.trans ?_ (bivariantClassComponentCongr_heq C _ _ _ _ _ _ _ _ _ _).symm
  exact (directSumBilinear_of_left_apply_heq (fun p q ↦ bivariantCompositeBilinear C
    (gysinSystemOfInvertible C) _ _ _ (f.resConnectedComponent w)
    (g.resConnectedComponent (f.continuous.connectedComponentsMap w))
    (f.resConnectedComponent_comp_ι_comp hf w) (g.resConnectedComponent_comp_ι_comp hg _) p q
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward C)) p (c w p)
    (d (f.continuous.connectedComponentsMap w)) n).symm

/-- **Composition preserves commuting with every class, on completions.** If the completed classes
`c ∈ A^*(X ⟶ Y)^∧` and `d ∈ A^*(Y ⟶ Z)^∧` commute with every bivariant class, so does their
composite `c ∘ d ∈ A^*(X ⟶ Z)^∧` (Stacks 0FE0). On a connected component `X_w` the degree `n`
part of `c ∘ d` is the finite sum over the degrees `p` in which `c` is nonzero on `X_w` of the
composites of the degree `p` part of `c` with the degree `n - p` part of `d`; it is therefore the
restriction to `X_w` of `∑_p c_p ∘ d_{n-p}`, a sum of composites of classes commuting with every
class (`Stacks.Chow.bivariantConnectedComponentRestriction_sum_bivariantCompositeOfInvertible`). -/
theorem completedCommutesWithEveryClass_completedBivariantCompositeOfInvertible {Z : Scheme.{u}}
    (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (g : Y ⟶ Z) [LocallyOfFiniteType g]
    (hg : g ≫ sZ = sY) [IsLocallyNoetherian Z]
    (c : completedBivariantGroup C (gysinSystemOfInvertible C) sX sY f hf)
    (d : completedBivariantGroup C (gysinSystemOfInvertible C) sY sZ g hg)
    (hc : completedCommutesWithEveryClass C sX sY f hf c)
    (hd : completedCommutesWithEveryClass C sY sZ g hg d) :
    completedCommutesWithEveryClass C sX sZ (f ≫ g) (comp_comp_structureMorphism_eq hf hg)
      (completedBivariantCompositeOfInvertible C sX sY sZ f g hf hg c d) := by
  classical
  refine completedCommutesWithEveryClass_of_connectedComponent C sX sZ (f ≫ g) _ _
    fun w n ↦ ⟨_, BivariantClass.commutesWithEveryClass_sum _ _ fun p _ ↦
      (BivariantClass.commutesWithEveryClass_copy rfl _ _ _ _).2
        ((hc p).bivariantCompositeOfInvertible (hd (n - p))),
      bivariantConnectedComponentRestriction_sum_bivariantCompositeOfInvertible C sX sY f hf sZ g
        hg c d w n (c w).support fun _ hp ↦ DFinsupp.mem_support_iff.2 hp⟩

end CompletedCommute

/-! ### Restriction of the completed flat pullback -/

section CompletedFlatRestriction

variable (C : ChowSituation.{u}) {X Y Y' : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f] [Flat f]
  (hf : f ≫ sY = sX) (h : Y' ⟶ Y) [LocallyOfFiniteType h] [IsLocallyNoetherian X]
  [IsLocallyNoetherian Y] [IsLocallyNoetherian Y'] [IsLocallyNoetherian (pullback f h)]

omit [LocallyOfFiniteType h] in
/-- The restriction `X'_j ⟶ Y'_{j'}` of the base change `f' : X' = X ×_Y Y' ⟶ Y'` to a connected
component `X'_j` has the relative dimension of `f` on the connected component `X_a` of `X` that
`X'_j` lands in: it is an open restriction of the base change of `X_a ⟶ Y` (Stacks 02NK). -/
theorem relativeDimension_resConnectedComponent_pullbackSnd
    (j : _root_.ConnectedComponents ↥(pullback f h)) {r : ℕ}
    (hr : AlgebraicGeometry.RelativeDimension
      (f.resConnectedComponent ((pullback.fst f h).continuous.connectedComponentsMap j)) r) :
    AlgebraicGeometry.RelativeDimension ((pullback.snd f h).resConnectedComponent j) r := by
  set a := (pullback.fst f h).continuous.connectedComponentsMap j
  set ιa := (X.connectedComponentOpens a).ι
  set ιj := ((pullback f h).connectedComponentOpens j).ι
  have h2 : AlgebraicGeometry.RelativeDimension (pullback.snd (ιa ≫ f) h) r :=
    relativeDimension_pullback_snd _ h r (relativeDimension_connectedComponentOpens_ι_comp f a r hr)
  set xa := liftToOpens (X.connectedComponentOpens a) (ιj ≫ pullback.fst f h) fun x ↦
    (pullback.fst f h).connectedComponentOpens_le_preimage j x.2
  have hxa : xa ≫ ιa = ιj ≫ pullback.fst f h := IsOpenImmersion.lift_fac _ _ _
  have hc : xa ≫ (ιa ≫ f) = (ιj ≫ pullback.snd f h) ≫ h := by
    rw [← Category.assoc, hxa, Category.assoc, pullback.condition, Category.assoc]
  have hκ : pullback.lift _ _ hc ≫ bivariantPushforwardBaseChange ιa f h = ιj := by
    apply pullback.hom_ext
    · rw [Category.assoc, bivariantPushforwardBaseChange_fst, pullback.lift_fst_assoc, hxa]
    · rw [Category.assoc, bivariantPushforwardBaseChange_snd, pullback.lift_snd]
  have : IsOpenImmersion (bivariantPushforwardBaseChange ιa f h) :=
    MorphismProperty.of_isPullback (isPullback_bivariantPushforwardBaseChange ιa f h)
      (P := @IsOpenImmersion) inferInstance
  have := isOpenImmersion_of_comp_eq _ _ _ hκ
  have h3 := h2.comp_isOpenImmersion (pullback.lift _ _ hc) (pullback.snd (ιa ≫ f) h)
  exact AlgebraicGeometry.RelativeDimension.of_comp_isOpenImmersion _ _ _
    (Scheme.Hom.resConnectedComponent_comp_ι _ j)
    (AlgebraicGeometry.RelativeDimension.of_comp_isOpenImmersion _ (𝟙 _) _
      (by rw [Category.comp_id, pullback.lift_snd]) h3)

/-- **Restriction of the flat pullback on a connected component, extended by zero.** Restricting
`ι_* ∘ (ι ≫ f)^*` along `h` (Stacks 0F9Z) and then to a connected component `X'_j` of
`X' = X ×_Y Y'` lying over the component `X_a` gives the flat-pullback class (Stacks 0B78) of
`X'_j ⟶ Y'_{j'}`. On a test scheme both cap by a flat pullback of the given class: restricting the
pushforward along the open and closed immersion `X_a ×_Y T ⟶ X ×_Y T` to the open subscheme
`X'_j ×_{Y'_{j'}} T`, which lies in its image, undoes it, and restriction to an open subscheme
commutes with flat pullback (Stacks 02RD). -/
theorem bivariantConnectedComponentRestriction_bivariantRestriction_componentFlatPullback
    (j : _root_.ConnectedComponents ↥(pullback f h)) (r : ℕ)
    (hr : AlgebraicGeometry.RelativeDimension
      (f.resConnectedComponent ((pullback.fst f h).continuous.connectedComponentsMap j)) r) :
    bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C) (pullback.fst f h ≫ sX)
        (h ≫ sY) (pullback.snd f h) (pullbackSnd_comp_structureMorphism_eq C sX sY f hf h)
        (-(r : ℤ)) (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
        (bivariantRestriction C (gysinSystemOfInvertible C) sX sY f hf h (-(r : ℤ))
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
          (componentFlatPullbackBivariantClass C sX sY f hf
            ((pullback.fst f h).continuous.connectedComponentsMap j) r hr)) j =
      flatPullbackBivariantClassOfInvertible C
          (((pullback f h).connectedComponentOpens j).ι ≫ (pullback.fst f h ≫ sX))
          ((Y'.connectedComponentOpens
              ((pullback.snd f h).continuous.connectedComponentsMap j)).ι ≫ (h ≫ sY))
          ((pullback.snd f h).resConnectedComponent j)
          ((pullback.snd f h).resConnectedComponent_comp_ι_comp
            (pullbackSnd_comp_structureMorphism_eq C sX sY f hf h) j)
          r (relativeDimension_resConnectedComponent_pullbackSnd f h j hr) := by
  refine BivariantClass.ext _ _ _ _ _ _ _ fun {S} s _ k γ ↦ ?_
  rw [bivariantConnectedComponentRestriction_cap, bivariantRestriction_cap,
    bivariantRestrictionCap_apply, componentFlatPullbackBivariantClass,
    bivariantProperPushforwardOfInvertible_cap, bivariantProperPushforwardCap_apply,
    chowPushforwardOfIso_iso_inv_eq_chowGroupRestrict, chowGroupRestrict_comp]
  set xa := liftToOpens
      (X.connectedComponentOpens ((pullback.fst f h).continuous.connectedComponentsMap j))
      (pullback.fst ((pullback.snd f h).resConnectedComponent j) s ≫
        ((pullback f h).connectedComponentOpens j).ι ≫ pullback.fst f h)
      fun x ↦ (pullback.fst f h).connectedComponentOpens_le_preimage j
        (pullback.fst ((pullback.snd f h).resConnectedComponent j) s x).2
  have hxa : xa ≫
      (X.connectedComponentOpens ((pullback.fst f h).continuous.connectedComponentsMap j)).ι =
      pullback.fst ((pullback.snd f h).resConnectedComponent j) s ≫
        ((pullback f h).connectedComponentOpens j).ι ≫ pullback.fst f h :=
    IsOpenImmersion.lift_fac _ _ _
  have hc : xa ≫ ((X.connectedComponentOpens
        ((pullback.fst f h).continuous.connectedComponentsMap j)).ι ≫ f) =
      pullback.snd ((pullback.snd f h).resConnectedComponent j) s ≫
        ((s ≫ (Y'.connectedComponentOpens
          ((pullback.snd f h).continuous.connectedComponentsMap j)).ι) ≫ h) := by
    rw [← Category.assoc, hxa, Category.assoc, Category.assoc, pullback.condition,
      ← Category.assoc ((pullback f h).connectedComponentOpens j).ι,
      ← Scheme.Hom.resConnectedComponent_comp_ι, Category.assoc,
      ← Category.assoc (pullback.fst ((pullback.snd f h).resConnectedComponent j) s),
      pullback.condition]
    simp only [Category.assoc]
  set mA := pullback.lift xa (pullback.snd ((pullback.snd f h).resConnectedComponent j) s) hc
  have hmA : mA ≫ bivariantPushforwardBaseChange
        (X.connectedComponentOpens ((pullback.fst f h).continuous.connectedComponentsMap j)).ι f
        ((s ≫ (Y'.connectedComponentOpens
          ((pullback.snd f h).continuous.connectedComponentsMap j)).ι) ≫ h) =
      opensPullbackComparison (pullback.snd f h) ((pullback f h).connectedComponentOpens j)
          (Y'.connectedComponentOpens ((pullback.snd f h).continuous.connectedComponentsMap j))
          ((pullback.snd f h).resConnectedComponent j)
          (Scheme.Hom.resConnectedComponent_comp_ι _ j) s ≫
        (pullbackLeftPullbackSndIso f h (s ≫ (Y'.connectedComponentOpens
          ((pullback.snd f h).continuous.connectedComponentsMap j)).ι)).hom := by
    apply pullback.hom_ext
    · rw [Category.assoc, bivariantPushforwardBaseChange_fst, pullback.lift_fst_assoc, hxa,
        Category.assoc, pullbackLeftPullbackSndIso_hom_fst, opensPullbackComparison_fst_assoc]
    · rw [Category.assoc, bivariantPushforwardBaseChange_snd, pullback.lift_snd, Category.assoc,
        pullbackLeftPullbackSndIso_hom_snd, opensPullbackComparison_snd]
  have : IsOpenImmersion (bivariantPushforwardBaseChange
      (X.connectedComponentOpens ((pullback.fst f h).continuous.connectedComponentsMap j)).ι f
      ((s ≫ (Y'.connectedComponentOpens
        ((pullback.snd f h).continuous.connectedComponentsMap j)).ι) ≫ h)) :=
    MorphismProperty.of_isPullback (isPullback_bivariantPushforwardBaseChange
        (X.connectedComponentOpens ((pullback.fst f h).continuous.connectedComponentsMap j)).ι f
        ((s ≫ (Y'.connectedComponentOpens
          ((pullback.snd f h).continuous.connectedComponentsMap j)).ι) ≫ h))
      (P := @IsOpenImmersion) inferInstance
  have : IsOpenImmersion mA := isOpenImmersion_of_comp_eq _ _ _ hmA
  have hmAs : mA ≫ (pullback.fst
        ((X.connectedComponentOpens
          ((pullback.fst f h).continuous.connectedComponentsMap j)).ι ≫ f)
        ((s ≫ (Y'.connectedComponentOpens
          ((pullback.snd f h).continuous.connectedComponentsMap j)).ι) ≫ h) ≫
        ((X.connectedComponentOpens
          ((pullback.fst f h).continuous.connectedComponentsMap j)).ι ≫ sX)) =
      pullback.fst ((pullback.snd f h).resConnectedComponent j) s ≫
        (((pullback f h).connectedComponentOpens j).ι ≫ (pullback.fst f h ≫ sX)) := by
    rw [pullback.lift_fst_assoc, ← Category.assoc, hxa]
    simp only [Category.assoc]
  rw [chowGroupRestrict_properChowPushforward C _ _ _ _ (bivariantPushforwardBaseChange
      (X.connectedComponentOpens ((pullback.fst f h).continuous.connectedComponentsMap j)).ι f
      ((s ≫ (Y'.connectedComponentOpens
        ((pullback.snd f h).continuous.connectedComponentsMap j)).ι) ≫ h)) _
    mA hmAs _ _ (𝟙 _) (Category.id_comp _)
    (IsPullback.of_vert_isIso_mono ⟨by rw [Category.id_comp, hmA]⟩) _ _
    (properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ (𝟙 _)
      (Category.id_comp _) _),
    properChowPushforward_eq_chowPushforwardOfIso, chowPushforwardOfIso_id]
  have hsq : mA ≫ pullback.snd
        ((X.connectedComponentOpens
          ((pullback.fst f h).continuous.connectedComponentsMap j)).ι ≫ f)
        ((s ≫ (Y'.connectedComponentOpens
          ((pullback.snd f h).continuous.connectedComponentsMap j)).ι) ≫ h) =
      pullback.snd ((pullback.snd f h).resConnectedComponent j) s ≫ 𝟙 S := by
    rw [Category.comp_id]
    exact pullback.lift_snd _ _ _
  have ho : 𝟙 S ≫ (((s ≫ (Y'.connectedComponentOpens
        ((pullback.snd f h).continuous.connectedComponentsMap j)).ι) ≫ h) ≫ sY) =
      s ≫ ((Y'.connectedComponentOpens
        ((pullback.snd f h).continuous.connectedComponentsMap j)).ι ≫ (h ≫ sY)) := by
    simp only [Category.id_comp, Category.assoc]
  have key := chowGroupRestrict_flatPullbackChow_of_comm C _ _ _
    (((s ≫ (Y'.connectedComponentOpens
      ((pullback.snd f h).continuous.connectedComponentsMap j)).ι) ≫ h) ≫ sY)
    (pullback.snd
      ((X.connectedComponentOpens
        ((pullback.fst f h).continuous.connectedComponentsMap j)).ι ≫ f)
      ((s ≫ (Y'.connectedComponentOpens
        ((pullback.snd f h).continuous.connectedComponentsMap j)).ι) ≫ h))
    (pullbackSnd_comp_structureMorphism (comp_comp_structureMorphism_eq rfl hf)
      ((s ≫ (Y'.connectedComponentOpens
        ((pullback.snd f h).continuous.connectedComponentsMap j)).ι) ≫ h))
    (pullback.snd ((pullback.snd f h).resConnectedComponent j) s)
    (pullbackSnd_comp_structureMorphism ((pullback.snd f h).resConnectedComponent_comp_ι_comp
      (pullbackSnd_comp_structureMorphism_eq C sX sY f hf h) j) s) mA hmAs (𝟙 S) ho hsq r
    (relativeDimension_pullbackSnd _ (relativeDimension_connectedComponentOpens_ι_comp f
        ((pullback.fst f h).continuous.connectedComponentsMap j) r hr)
      ((s ≫ (Y'.connectedComponentOpens
        ((pullback.snd f h).continuous.connectedComponentsMap j)).ι) ≫ h))
    (relativeDimension_pullbackSnd _ (relativeDimension_resConnectedComponent_pullbackSnd f h j hr)
      s) k
    (chowGroupCongr C (Category.assoc (s ≫ (Y'.connectedComponentOpens
        ((pullback.snd f h).continuous.connectedComponentsMap j)).ι) h sY).symm k
      (chowGroupCongr C (Category.assoc s (Y'.connectedComponentOpens
        ((pullback.snd f h).continuous.connectedComponentsMap j)).ι (h ≫ sY)).symm k γ))
  refine eq_of_heq (HEq.trans (chowGroupRestrict_heq_of_heq C _ _ _ _ (by ring) _ _
    (IsBivariantFlatPullback.cap_heq (hS1 := flatPullbackDescends C)
      (isBivariantFlatPullback_flatPullbackBivariantClassOfInvertible C _ _ _ _ _ _)
        ((s ≫ (Y'.connectedComponentOpens
          ((pullback.snd f h).continuous.connectedComponentsMap j)).ι) ≫ h)
        k _)) ?_)
  refine HEq.trans (heq_of_eq key) ?_
  refine HEq.trans ?_ (IsBivariantFlatPullback.cap_heq (hS1 := flatPullbackDescends C)
      (isBivariantFlatPullback_flatPullbackBivariantClassOfInvertible C _ _ _ _ _ _)
      s k γ).symm
  refine flatPullbackChow_heq_congr C _ _ _ _ _ _ rfl rfl _ _ rfl _ _ _ _ ?_
  rw [chowGroupRestrict_eq_chowPushforwardOfIso_of_comp_id C _ _ (𝟙 S) ho (𝟙 S)
    (by rw [Category.id_comp]; exact ho.symm) (Category.id_comp _)]
  exact (chowPushforwardOfIso_heq_of_eq_id _ rfl _ _).trans
    ((chowGroupCongr_heq C _ _ _).trans (chowGroupCongr_heq C _ _ _))

omit [LocallyOfFiniteType h] in
/-- The relative dimension of the base change `f' : X ×_Y Y' ⟶ Y'` is constant on every connected
component of its source, when that of `f` is. -/
theorem exists_relativeDimension_resConnectedComponent_pullbackSnd
    (hrel : ∀ a : _root_.ConnectedComponents X,
      ∃ r : ℕ, AlgebraicGeometry.RelativeDimension (f.resConnectedComponent a) r)
    (j : _root_.ConnectedComponents ↥(pullback f h)) :
    ∃ r : ℕ, AlgebraicGeometry.RelativeDimension ((pullback.snd f h).resConnectedComponent j) r :=
  (hrel _).imp fun _ hr ↦ relativeDimension_resConnectedComponent_pullbackSnd f h j hr

/-- **Restriction of the completed flat pullback is the completed flat pullback of the base
change** (Stacks 0F9Z and Stacks 0B78 on completions). For a flat morphism `f : X ⟶ Y` whose
relative dimension is constant on each connected component of `X`, the restriction along
`h : Y' ⟶ Y` of `f^* ∈ A^*(X ⟶ Y)^∧` is `(f')^* ∈ A^*(X ×_Y Y' ⟶ Y')^∧`. On a connected component
`X'_j` lying over `X_a`, both are concentrated in degree `-r_a`: the restriction of a class depends
on `X'_j` only through the restriction of the class to `X_a`
(`Stacks.Chow.bivariantConnectedComponentRestriction_bivariantRestriction_eq_zero`), so the degree
`-r_a` term may be replaced by the flat pullback on `X_a` extended by zero, whose restriction is
computed by
`Stacks.Chow.bivariantConnectedComponentRestriction_bivariantRestriction_componentFlatPullback`. -/
theorem completedBivariantRestriction_completedFlatPullback
    (hrel : ∀ a : _root_.ConnectedComponents X,
      ∃ r : ℕ, AlgebraicGeometry.RelativeDimension (f.resConnectedComponent a) r) :
    completedBivariantRestrictionViaSequence C sX sY f hf h
        (completedFlatPullback C sX sY f hf hrel) =
      completedFlatPullback C (pullback.fst f h ≫ sX) (h ≫ sY) (pullback.snd f h)
        (pullbackSnd_comp_structureMorphism_eq C sX sY f hf h)
        (exists_relativeDimension_resConnectedComponent_pullbackSnd f h hrel) := by
  funext j
  refine DirectSum.ext fun n ↦ ?_
  set a := (pullback.fst f h).continuous.connectedComponentsMap j
  have hr := relativeDimension_flatComponentRelativeDimension f hrel a
  rw [completedBivariantRestriction_apply, completedFlatPullback_apply_of_relativeDimension C _ _ _
    _ _ j _ (relativeDimension_resConnectedComponent_pullbackSnd f h j hr)]
  have hxa := restriction_completedBivariantSequence C (gysinSystemOfInvertible C) sX sY f hf
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
    (gysinSystemOfInvertible_isNaturalUnderOpensRestriction C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackComp C)
    (completedFlatPullback C sX sY f hf hrel) n a
  rw [completedFlatPullback_apply] at hxa
  change bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C) sX sY f hf n
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
    (completedBivariantSequenceOfInvertible C sX sY f hf
      (completedFlatPullback C sX sY f hf hrel) n) a = _ at hxa
  set x := completedBivariantSequenceOfInvertible C sX sY f hf
    (completedFlatPullback C sX sY f hf hrel) n
  by_cases hn : -(flatComponentRelativeDimension f hrel a : ℤ) = n
  · subst hn
    set e := componentFlatPullbackBivariantClass C sX sY f hf a _ hr
    have hzero : bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C) sX sY f hf _
        (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C) (x - e) a = 0 := by
      rw [map_sub, Pi.sub_apply, hxa, DirectSum.of_eq_same,
        bivariantConnectedComponentRestriction_componentFlatPullbackBivariantClass, sub_self]
    have h0 := bivariantConnectedComponentRestriction_bivariantRestriction_eq_zero C
      (gysinSystemOfInvertible C) sX sY f hf h _
      (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) (x - e) j hzero
    have hx : x = e + (x - e) := (add_sub_cancel e x).symm
    rw [hx, bivariantRestriction_add, map_add, Pi.add_apply, h0, add_zero,
      bivariantConnectedComponentRestriction_bivariantRestriction_componentFlatPullback,
      DirectSum.of_eq_same]
  · have hzero : bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C) sX sY f hf n
        (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C) x a = 0 := by
      rw [hxa]
      exact DirectSum.of_eq_of_ne (β := fun n ↦ BivariantClass C (gysinSystemOfInvertible C)
        ((X.connectedComponentOpens a).ι ≫ sX)
        ((Y.connectedComponentOpens (f.continuous.connectedComponentsMap a)).ι ≫ sY)
        (f.resConnectedComponent a) (f.resConnectedComponent_comp_ι_comp hf a) n)
        (-(flatComponentRelativeDimension f hrel a : ℤ)) n _ (Ne.symm hn)
    rw [bivariantConnectedComponentRestriction_bivariantRestriction_eq_zero C
      (gysinSystemOfInvertible C) sX sY f hf h n
      (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) x j hzero]
    exact (DirectSum.of_eq_of_ne (β := fun n ↦ BivariantClass C (gysinSystemOfInvertible C)
      (((pullback f h).connectedComponentOpens j).ι ≫ (pullback.fst f h ≫ sX))
      ((Y'.connectedComponentOpens
        ((pullback.snd f h).continuous.connectedComponentsMap j)).ι ≫ (h ≫ sY))
      ((pullback.snd f h).resConnectedComponent j)
      ((pullback.snd f h).resConnectedComponent_comp_ι_comp
        (pullbackSnd_comp_structureMorphism_eq C sX sY f hf h) j) n)
      (-(flatComponentRelativeDimension f hrel a : ℤ)) n _ (Ne.symm hn)).symm

omit [Flat f] in
/-- **Restriction of the completed smooth pullback** (Stacks 0F9Z and Stacks 0B78 on completions).
For a smooth morphism `f : X ⟶ Y`, the restriction along `h : Y' ⟶ Y` of
`f^* ∈ A^*(X ⟶ Y)^∧` is the completed flat pullback of the base change
`f' : X ×_Y Y' ⟶ Y'`, which is smooth. -/
theorem completedBivariantRestriction_completedFlatPullbackOfSmooth [Smooth f] :
    completedBivariantRestrictionViaSequence C sX sY f hf h
        (completedFlatPullbackOfSmooth C sX sY f hf) =
      completedFlatPullbackOfSmooth C (pullback.fst f h ≫ sX) (h ≫ sY) (pullback.snd f h)
        (pullbackSnd_comp_structureMorphism_eq C sX sY f hf h) := by
  have hrel : ∀ a : _root_.ConnectedComponents X,
      ∃ r : ℕ, AlgebraicGeometry.RelativeDimension (f.resConnectedComponent a) r :=
    fun a ↦ ⟨_, relativeDimension_smoothComponentRelativeDimension f a⟩
  rw [completedFlatPullbackOfSmooth_eq_completedFlatPullback C sX sY f hf hrel,
    completedFlatPullbackOfSmooth_eq_completedFlatPullback C _ _ (pullback.snd f h) _
      (exists_relativeDimension_resConnectedComponent_pullbackSnd f h hrel)]
  exact completedBivariantRestriction_completedFlatPullback C sX sY f hf h hrel

end CompletedFlatRestriction

end Stacks.Chow

end
