module

public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsMap
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRestrictionRingedToposHom
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftPairActionSection
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.StructureSharpRestrictEqPostcompose

/-!
# The difference of two lifts over a base is a derivation over that base

Let `G ⊂ X'` be a first-order thickening of algebraic spaces with inclusion `i : X ⟶ X'`, let
`q : Y' ⟶ Bb` be a morphism and let `a', b' : X' ⟶ Y'` be two morphisms with `i ≫ a' = i ≫ b'`
which are morphisms over `Bb`, that is `a' ≫ q = b' ≫ q`.

`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftPairActionSection` forms the derivation of
[Stacks Project, Tag 0618] out of the difference of the two structure maps, and carries the
hypothesis `hφ` — that the two structure maps agree on the base ring sheaf
`(b')^{-1}q^{-1}𝒪_{Bb}`, which is hypothesis (1) of that tag.  Its implementation notes record
`hφ` as owed and name what deriving it from `a' ≫ q = b' ≫ q` needs.

**This file discharges `hφ` from `a' ≫ q = b' ≫ q`**, so the derivation, the acting section and
the chart-free global section of the acting sheaf of [Stacks Project, Tag 061D] all exist with
no hypothesis beyond the thickening and the two morphisms being morphisms over `Bb`.

## Main definitions

* `AlgebraicGeometry.Space.liftPairDerivationSecondOfCompEq`,
  `AlgebraicGeometry.Space.liftPairActionSectionOfCompEq` and
  `AlgebraicGeometry.Space.liftPairGlobalSectionOfCompEq`: the derivation of [Stacks Project,
  Tag 0618], the morphism `a^*Ω_{Y'/Bb} ⟶ 𝒞_{X/X'}` and the global section of the acting sheaf
  of [Stacks Project, Tag 061D] for two lifts, **with `hφ` discharged**.

## Main results

* `Stacks.CategoryTheory.comp_eq_comp_of_homEquiv`: two morphisms out of a left-adjoint value
  agree after two morphisms as soon as one transpose does.  Every datum a variable.
* `AlgebraicGeometry.Space.structureSharpInverseImageSet_comp_map_pushforwardIsoOfRestrictEq`:
  the statement at the level of sheaves of sets and in inverse-image form.
* `AlgebraicGeometry.Space.inverseImageStructureSharp_comp_pushforwardCommRingIsoOfRestrictEq`:
  the same for sheaves of commutative rings.
* `AlgebraicGeometry.Space.commRingInverseImageIsoOfRestrictEq_inv_app_comp`: the comparison of
  the two inverse images carries the one composite to the other at `q^{-1}𝒪_{Bb}`.
* `AlgebraicGeometry.Space.liftPairBaseMap_comp_structureSharpInverseImage` and
  `AlgebraicGeometry.Space.liftPairBaseMap_comp_liftPairSecondSharp`: `hφ` itself, for sheaves of
  commutative rings and then for sheaves of rings, which is the form
  `AlgebraicGeometry.Space.liftPairDerivationSecond` consumes.

## Implementation notes

**The shape of the reduction.**  `hφ` asks that the two structure maps, as homomorphisms out of
`(b')^{-1}𝒪_{Y'}`, agree after the base map `(b')^{-1}(q^♯)`.  One of the two is read through the
comparison `AlgebraicGeometry.Space.commRingInverseImageIsoOfRestrictEq` of the two inverse
images, whose values are not computable — it is a mate.  Three steps remove it:

1. **naturality.**  `AlgebraicGeometry.NatTrans.naturality` of that comparison's inverse at
   `q^♯` moves it from `𝒪_{Y'}` to `q^{-1}𝒪_{Bb}`, so what is asked becomes a statement about
   the two composites `(a')^{-1}q^{-1}𝒪_{Bb} ⟶ (a')^{-1}𝒪_{Y'} ⟶ 𝒪_{X'}` and its `b'` analogue;
2. **transposition.**  Those are two morphisms out of the two left adjoints, so
   `Stacks.CategoryTheory.comp_natIso_inv_app_eq_of_transpose` applies — at `m = 𝟙`, the case
   its existing consumer never takes, since there `m := i^♯` and a difference which already lands
   in the defining ideal is killed by `i^♯` for free.  What remains is one equation about the
   *direct* images;
3. **the direct-image equation**, which is the real content and is
   `AlgebraicGeometry.Space.structureSharpPush_comp_map_smallEtalePushforwardIsoOfRestrictEq`
   of `StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.StructureSharpRestrictEqPostcompose`,
   brought from the base `Bb` to `Y'` by the set-level transpose
   `AlgebraicGeometry.Space.structureSharpInverseImage_of_structureSharpSetComp` and lifted from
   sheaves of sets to sheaves of commutative rings by faithfulness of forgetting the ring
   structure.

**Faithfulness is available at the level of sets, and that is what makes the lift one step.**
`AlgebraicGeometry.Space.fullyFaithfulForgetCommRingSheaf` is the full faithfulness of forgetting
*commutativity*, so the arguments of
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.StructureSharpRestrictEqInverseImage` descend
only as far as sheaves of rings.  But `AlgebraicGeometry.RingedTopos.forgetRing` — which is
`CategoryTheory.sheafCompose _ (CategoryTheory.forget CommRingCat)` — is faithful by instance
resolution, and all three factors of the equation have their underlying maps of sheaves of sets
named: the base map by definition
(`AlgebraicGeometry.Space.structureSharpInverseImageSet` *is* the forget of
`AlgebraicGeometry.Space.structureSharpInverseImage`, by `rfl`), the structure map by
`AlgebraicGeometry.Space.forgetRing_map_structureSharpCommRing`, and the comparison of
[Stacks Project, Tag 05ZM] by
`AlgebraicGeometry.Space.forget_pushforwardCommRingFunctorIsoOfRestrictEq`.  So the descent is a
single application of `CategoryTheory.Functor.map_injective`.

**Term mode, and why.**  `rw` and `simp only` are unusable on these composites, for the reason
recorded in
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.StructureSharpRestrictEqPostcompose`: the
intermediate objects have two definitionally-but-not-syntactically equal spellings, so a
rewritten subterm is not type-correct at the transparency a tactic checks it at, and the tactic
silently declines or dies.  Here the six-step `rw` of the faithfulness descent fires
only its first two steps.  Written as a chain of `congrArg` and
`CategoryTheory.Category.assoc _ _ _`, where the elaborator unifies the two spellings at default
transparency, the same descent checks.  `CategoryTheory.Functor.map_id` and
`CategoryTheory.Category.comp_id` likewise need their arguments supplied.

No `@[stacks]` attribute is claimed.  Hypothesis (1) of [Stacks Project, Tag 0618] is where the
tag already sits, on
`AlgebraicGeometry.Space.inverseImageStructureSharpOfRestrictEq_comp_structureSharp`, and what is
added here is the discharge of a hypothesis, not a new statement of the tag.

## References

* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 05ZM](https://stacks.math.columbia.edu/tag/05ZM)
* [Stacks Project, Tag 061D](https://stacks.math.columbia.edu/tag/061D)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Sheaves.ToposPullback
open Stacks.Sheaves.ToposPushforward

namespace Stacks.CategoryTheory

open _root_.CategoryTheory

/-- **Two morphisms out of a left-adjoint value agree after `m₁` and `m₂` as soon as one
transpose does.**  For `s : F.obj x ⟶ c` with transpose `t`, the equation `t ≫ G.map m₁ =
t ≫ G.map m₂` gives `s ≫ m₁ = s ≫ m₂`, the transposition being a bijection natural in the
target.

Every datum is a variable, so that at an instantiation nothing has to be restated: the transpose
is supplied by an existing lemma. -/
theorem comp_eq_comp_of_homEquiv {C D : Type*} [Category C] [Category D] {F : C ⥤ D}
    {G : D ⥤ C} (adj : F ⊣ G) {x : C} {c d : D} (s : F.obj x ⟶ c) (t : x ⟶ G.obj c)
    (ht : adj.homEquiv x c s = t) (m₁ m₂ : c ⟶ d)
    (key : t ≫ G.map m₁ = t ≫ G.map m₂) :
    s ≫ m₁ = s ≫ m₂ := by
  refine (adj.homEquiv x d).injective ?_
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right, ht, key]

end Stacks.CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X' Y' Bb : AlgebraicSpaces B S hS} {G : Subfunctor X'.1}
  (hG : IsThickening B S hS X' G) (a' b' : X' ⟶ Y')
  (h : IsThickening.inclusion B S hS hG ≫ a' = IsThickening.inclusion B S hS hG ≫ b')

/-! ### The direct-image equation, in inverse-image form -/

/-- **The two structure maps of two lifts agree on the inverse image of the structure sheaf of
the base**, at the level of sheaves of sets.

This is
`AlgebraicGeometry.Space.structureSharpPush_comp_map_smallEtalePushforwardIsoOfRestrictEq`
transposed from `Bb` to `Y'` along `q^{-1} ⊣ q_*`, by
`AlgebraicGeometry.Space.structureSharpInverseImage_of_structureSharpSetComp` of
[Stacks Project, Tag 03G8]. -/
theorem structureSharpInverseImageSet_comp_map_pushforwardIsoOfRestrictEq (q : Y' ⟶ Bb)
    (hq : a' ≫ q = b' ≫ q) :
    structureSharpInverseImageSet B S hS q ≫
        (structureSharpPush B S hS a' ≫
          (smallEtalePushforwardIsoOfRestrictEq B S hS hG a' b' h).hom.app
            (structureSetSheaf B S hS X')) =
      structureSharpInverseImageSet B S hS q ≫ structureSharpPush B S hS b' :=
  structureSharpInverseImage_of_structureSharpSetComp B S hS q _ _
    ((Functor.map_comp (smallToposMorphismTypeU B S hS q).pushforward _ _).symm ▸
      structureSharpPush_comp_map_smallEtalePushforwardIsoOfRestrictEq B S hS hG a' b' h q hq)

/-- **The same for sheaves of commutative rings.**  The structure map of `a'`, read into the
direct image along `b'` through the comparison of [Stacks Project, Tag 05ZM], agrees with that of
`b'` after the inverse-image form of the structure map of `q`.

Obtained from the statement for sheaves of sets by faithfulness of forgetting the ring structure;
the three factors' underlying maps of sheaves of sets are all named.  See the implementation
notes for why this is a term and not a `rw`. -/
theorem inverseImageStructureSharp_comp_pushforwardCommRingIsoOfRestrictEq (q : Y' ⟶ Bb)
    (hq : a' ≫ q = b' ≫ q) :
    (structureSharpInverseImage B S hS q ≫ structureSharpCommRing B S hS a') ≫
        (pushforwardCommRingFunctorIsoOfRestrictEq B S hS hG a' b' h).hom.app
          (smallEtaleRingedTopos B S hS X').O =
      structureSharpInverseImage B S hS q ≫ structureSharpCommRing B S hS b' := by
  refine (smallEtaleRingedTopos B S hS Y').forgetRing.map_injective ?_
  refine (Functor.map_comp (smallEtaleRingedTopos B S hS Y').forgetRing _ _).trans ?_
  refine (congrArg (fun m => m ≫ (smallEtaleRingedTopos B S hS Y').forgetRing.map
      ((pushforwardCommRingFunctorIsoOfRestrictEq B S hS hG a' b' h).hom.app
        (smallEtaleRingedTopos B S hS X').O))
    (Functor.map_comp (smallEtaleRingedTopos B S hS Y').forgetRing _ _)).trans ?_
  refine (congrArg (fun m => ((smallEtaleRingedTopos B S hS Y').forgetRing.map
        (structureSharpInverseImage B S hS q) ≫ m) ≫
      (smallEtaleRingedTopos B S hS Y').forgetRing.map
        ((pushforwardCommRingFunctorIsoOfRestrictEq B S hS hG a' b' h).hom.app
          (smallEtaleRingedTopos B S hS X').O))
    (forgetRing_map_structureSharpCommRing B S hS a')).trans ?_
  refine (congrArg (fun m => ((smallEtaleRingedTopos B S hS Y').forgetRing.map
        (structureSharpInverseImage B S hS q) ≫ structureSharpSet B S hS a') ≫ m)
    (forget_pushforwardCommRingFunctorIsoOfRestrictEq B S hS hG a' b' h)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (structureSharpInverseImageSet_comp_map_pushforwardIsoOfRestrictEq
    B S hS hG a' b' h q hq).trans ?_
  exact (congrArg (fun m => (smallEtaleRingedTopos B S hS Y').forgetRing.map
        (structureSharpInverseImage B S hS q) ≫ m)
      (forgetRing_map_structureSharpCommRing B S hS b').symm).trans
    (Functor.map_comp (smallEtaleRingedTopos B S hS Y').forgetRing _ _).symm

/-! ### Removing the comparison of the two inverse images -/

/-- **The transpose of the base map followed by the structure map in inverse-image form is the
base map followed by the structure map.**  By naturality of the transposition in the source and
`AlgebraicGeometry.RingedToposHom.homEquiv_fSharpInverseImage`. -/
theorem homEquiv_map_structureSharpInverseImage_comp (c' : X' ⟶ Y') (q : Y' ⟶ Bb) :
    (commRingImageAdjunction.{u, u, u, u + 1, u, u + 1}
          (smallToposMorphismTypeU B S hS c')).homEquiv
        (inverseImageStructureSheaf B S hS q) (smallEtaleRingedTopos B S hS X').O
        ((inverseImageCommRingFunctor.{u, u, u, u + 1, u, u + 1}
            (smallToposMorphismTypeU B S hS c')).map
          (structureSharpInverseImage B S hS q) ≫
          structureSharpInverseImage B S hS c') =
      structureSharpInverseImage B S hS q ≫ structureSharpCommRing B S hS c' :=
  (Adjunction.homEquiv_naturality_left _ _ _).trans
    (congrArg (fun m => structureSharpInverseImage B S hS q ≫ m)
      (RingedToposHom.homEquiv_fSharpInverseImage (smallEtaleRingedToposHom B S hS c')))

/-- **The comparison of the two inverse images carries the one composite to the other**, at the
inverse image of the structure sheaf of the base.

This is `Stacks.CategoryTheory.comp_natIso_inv_app_eq_of_transpose` at `m = 𝟙` — the case its
existing consumer never takes.  There `m := i^♯`, and an equation after `i^♯` says nothing about a
difference which already lands in the defining ideal; at `m = 𝟙` the hypothesis is the
direct-image equation above, which is the real content. -/
theorem commRingInverseImageIsoOfRestrictEq_inv_app_comp (q : Y' ⟶ Bb)
    (hq : a' ≫ q = b' ≫ q) :
    (commRingInverseImageIsoOfRestrictEq B S hS hG a' b' h).inv.app
          (inverseImageStructureSheaf B S hS q) ≫
        (inverseImageCommRingFunctor.{u, u, u, u + 1, u, u + 1}
            (smallToposMorphismTypeU B S hS a')).map
          (structureSharpInverseImage B S hS q) ≫
        structureSharpInverseImage B S hS a' =
      (inverseImageCommRingFunctor.{u, u, u, u + 1, u, u + 1}
            (smallToposMorphismTypeU B S hS b')).map
          (structureSharpInverseImage B S hS q) ≫
        structureSharpInverseImage B S hS b' := by
  have hid : ∀ {W} (f : W ⟶ (pushforwardCommRingFunctor.{u, u, u, u + 1, u, u + 1}
          (smallToposMorphismTypeU B S hS b')).obj (smallEtaleRingedTopos B S hS X').O),
      f ≫ (pushforwardCommRingFunctor.{u, u, u, u + 1, u, u + 1}
          (smallToposMorphismTypeU B S hS b')).map (𝟙 (smallEtaleRingedTopos B S hS X').O) = f :=
    fun f => (congrArg (f ≫ ·) (CategoryTheory.Functor.map_id _ _)).trans
      (Category.comp_id f)
  have keyId : (structureSharpInverseImage B S hS q ≫ structureSharpCommRing B S hS a') ≫
        (pushforwardCommRingFunctorIsoOfRestrictEq B S hS hG a' b' h).hom.app
          (smallEtaleRingedTopos B S hS X').O ≫
        (pushforwardCommRingFunctor.{u, u, u, u + 1, u, u + 1}
            (smallToposMorphismTypeU B S hS b')).map
          (𝟙 (smallEtaleRingedTopos B S hS X').O) =
      (structureSharpInverseImage B S hS q ≫ structureSharpCommRing B S hS b') ≫
        (pushforwardCommRingFunctor.{u, u, u, u + 1, u, u + 1}
            (smallToposMorphismTypeU B S hS b')).map
          (𝟙 (smallEtaleRingedTopos B S hS X').O) :=
    ((congrArg (fun m => (structureSharpInverseImage B S hS q ≫
            structureSharpCommRing B S hS a') ≫ m) (hid _)).trans
      (inverseImageStructureSharp_comp_pushforwardCommRingIsoOfRestrictEq
        B S hS hG a' b' h q hq)).trans (hid _).symm
  have H := Stacks.CategoryTheory.comp_natIso_inv_app_eq_of_transpose
    (commRingImageAdjunction.{u, u, u, u + 1, u, u + 1} (smallToposMorphismTypeU B S hS a'))
    (commRingImageAdjunction.{u, u, u, u + 1, u, u + 1} (smallToposMorphismTypeU B S hS b'))
    (pushforwardCommRingFunctorIsoOfRestrictEq B S hS hG a' b' h)
    (inverseImageStructureSheaf B S hS q)
    ((inverseImageCommRingFunctor.{u, u, u, u + 1, u, u + 1}
        (smallToposMorphismTypeU B S hS a')).map
      (structureSharpInverseImage B S hS q) ≫ structureSharpInverseImage B S hS a')
    ((inverseImageCommRingFunctor.{u, u, u, u + 1, u, u + 1}
        (smallToposMorphismTypeU B S hS b')).map
      (structureSharpInverseImage B S hS q) ≫ structureSharpInverseImage B S hS b')
    (𝟙 (smallEtaleRingedTopos B S hS X').O)
    (structureSharpInverseImage B S hS q ≫ structureSharpCommRing B S hS a')
    (structureSharpInverseImage B S hS q ≫ structureSharpCommRing B S hS b')
    (homEquiv_map_structureSharpInverseImage_comp B S hS a' q)
    (homEquiv_map_structureSharpInverseImage_comp B S hS b' q) keyId
  exact (congrArg (fun m => (commRingInverseImageIsoOfRestrictEq B S hS hG a' b' h).inv.app
        (inverseImageStructureSheaf B S hS q) ≫ m)
      (Category.comp_id ((inverseImageCommRingFunctor.{u, u, u, u + 1, u, u + 1}
          (smallToposMorphismTypeU B S hS a')).map
        (structureSharpInverseImage B S hS q) ≫
        structureSharpInverseImage B S hS a')).symm).trans
    (H.trans (Category.comp_id _))

/-! ### `hφ` -/

/-- **`hφ` for sheaves of commutative rings**: the two structure maps of two lifts, in
inverse-image form, agree after the base map `(b')^{-1}(q^♯)`.

Naturality of the comparison of the two inverse images at `q^♯` moves that comparison from
`𝒪_{Y'}` to `q^{-1}𝒪_{Bb}`, where the previous result applies. -/
theorem liftPairBaseMap_comp_structureSharpInverseImage (q : Y' ⟶ Bb)
    (hq : a' ≫ q = b' ≫ q) :
    liftPairBaseMap B S hS b' q ≫ structureSharpInverseImage B S hS b' =
      liftPairBaseMap B S hS b' q ≫
        inverseImageStructureSharpOfRestrictEq B S hS hG a' b' h :=
  ((((Category.assoc
            ((inverseImageCommRingFunctor.{u, u, u, u + 1, u, u + 1}
              (smallToposMorphismTypeU B S hS b')).map
              (structureSharpInverseImage B S hS q))
            ((commRingInverseImageIsoOfRestrictEq B S hS hG a' b' h).inv.app
              (smallEtaleRingedTopos B S hS Y').O)
            (structureSharpInverseImage B S hS a')).symm.trans
        (congrArg (fun m => m ≫ structureSharpInverseImage B S hS a')
          ((commRingInverseImageIsoOfRestrictEq B S hS hG a' b' h).inv.naturality
            (structureSharpInverseImage B S hS q)))).trans
      (Category.assoc _ _ _)).trans
    (commRingInverseImageIsoOfRestrictEq_inv_app_comp B S hS hG a' b' h q hq)).symm

/-- **`hφ` itself**, for sheaves of rings — the form
`AlgebraicGeometry.Space.liftPairDerivationSecond` consumes.  The forgetful functor is applied to
the whole equation. -/
theorem liftPairBaseMap_comp_liftPairSecondSharp (q : Y' ⟶ Bb) (hq : a' ≫ q = b' ≫ q) :
    (sheafCompose (SmallEtale.topology B S hS X'.1)
          (forget₂ CommRingCat.{u} RingCat.{u})).map (liftPairBaseMap B S hS b' q) ≫
        liftPairSecondSharp B S hS b' =
      (sheafCompose (SmallEtale.topology B S hS X'.1)
          (forget₂ CommRingCat.{u} RingCat.{u})).map (liftPairBaseMap B S hS b' q) ≫
        (sheafCompose (SmallEtale.topology B S hS X'.1)
            (forget₂ CommRingCat.{u} RingCat.{u})).map
          (inverseImageStructureSharpOfRestrictEq B S hS hG a' b' h) :=
  (((sheafCompose (SmallEtale.topology B S hS X'.1)
        (forget₂ CommRingCat.{u} RingCat.{u})).map_comp _ _).symm.trans
    (congrArg (sheafCompose (SmallEtale.topology B S hS X'.1)
        (forget₂ CommRingCat.{u} RingCat.{u})).map
      (liftPairBaseMap_comp_structureSharpInverseImage B S hS hG a' b' h q hq))).trans
    ((sheafCompose (SmallEtale.topology B S hS X'.1)
      (forget₂ CommRingCat.{u} RingCat.{u})).map_comp _ _)

/-! ### The difference of two lifts over a base, unconditionally -/

/-- **The derivation `D` of [Stacks Project, Tag 0618] for two lifts over `Bb`**, with `hφ`
discharged: the only hypotheses are that `G ⊂ X'` is a first-order thickening, that the two
morphisms agree on its closed subspace and that they are morphisms over `Bb`. -/
def liftPairDerivationSecondOfCompEq (q : Y' ⟶ Bb)
    (hZ : IsFirstOrderThickening B S hS X' G) (hq : a' ≫ q = b' ≫ q) :
    (liftDifferenceCoefficients B S hS ⟨G, hG.1⟩
      (liftPairSecondSharp B S hS b')).Derivation' (liftPairBaseMap B S hS b' q).hom :=
  liftPairDerivationSecond B S hS hG a' b' h q hZ
    (liftPairBaseMap_comp_liftPairSecondSharp B S hS hG a' b' h q hq)

/-- **The difference of two lifts over `Bb`, as a morphism `a^*Ω_{Y'/Bb} ⟶ 𝒞_{X/X'}`**, with
`hφ` discharged. -/
def liftPairActionSectionOfCompEq (q : Y' ⟶ Bb)
    (hZ : IsFirstOrderThickening B S hS X' G) (hq : a' ≫ q = b' ≫ q) :
    (modulePullback B S hS (IsThickening.inclusion B S hS hG ≫ b')).obj
        (sheafOfDifferentials B S hS q) ⟶
      conormalModule B S hS X' ⟨G, hG.1⟩ :=
  liftPairActionSection B S hS hG a' b' h q hZ
    (liftPairBaseMap_comp_liftPairSecondSharp B S hS hG a' b' h q hq)

/-- **The chart-free difference of two lifts over `Bb`, as a global section of the acting sheaf
of [Stacks Project, Tag 061D]**, with `hφ` discharged.

This is the section which a `AlgebraicGeometry.Space.LiftDifferenceFamily` is to be built from:
it is defined with no reference to any chart presentation, and it now carries no hypothesis
beyond the thickening, the agreement of the two morphisms on the closed subspace and their being
morphisms over `Bb`. -/
def liftPairGlobalSectionOfCompEq (q : Y' ⟶ Bb)
    (hZ : IsFirstOrderThickening B S hS X' G) (hq : a' ≫ q = b' ≫ q) :
    (liftActionSheaf B S hS ⟨G, hG.1⟩ q
      (IsThickening.inclusion B S hS hG ≫ b')).sections :=
  liftPairGlobalSection B S hS hG a' b' h q hZ
    (liftPairBaseMap_comp_liftPairSecondSharp B S hS hG a' b' h q hq)

end AlgebraicGeometry.Space

end
