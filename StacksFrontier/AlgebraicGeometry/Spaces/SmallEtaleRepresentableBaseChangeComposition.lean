module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangeComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRepresentableBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSchemeStructureSharp
public import StacksFrontier.AlgebraicGeometry.Topologies.BigEtale.SmallEtaleComparison
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.MorphismComposition

/-!
# Chart base change of representable algebraic spaces is base change of schemes, compatibly with
composition

`AlgebraicGeometry.Space.representedSmallEtaleBaseChangeIso` identifies, for a morphism
`g : T' ⟶ T` of the big fppf category over `S`, base change of étale scheme charts along the
represented morphism of algebraic spaces with base change along `g` in the associated big étale
site.  This file proves that the identification is compatible with composition: for composable
`h : T'' ⟶ T'` and `g : T' ⟶ T` and a factorisation `hgc` of their composite, the comparison for
`hgc` is the comparison for `h`, the comparison for `g` base changed along `h`, and the two
composition comparisons of the base-change functors on either side.

## Main definitions

* `AlgebraicGeometry.Space.smallBaseChange_factoredComp` is
  `AlgebraicGeometry.Space.smallBaseChange_comp` for a composite presented by a separate
  morphism together with a factorisation, the form in which a consumer whose composite arrow is
  not syntactically `f ≫ g` can use it.

## Main results

* `AlgebraicGeometry.Space.representedSmallEtaleBaseChangeComponent_comp` is the composition law
  at a single étale chart, `AlgebraicGeometry.Space.representedSmallEtaleBaseChangeIso_hom_comp`
  the same for the natural transformations and
  `AlgebraicGeometry.Space.representedSmallEtaleBaseChangeIso_eq_factoredComp` for the natural
  isomorphisms.
* `AlgebraicGeometry.smallEtaleBaseChange_map_left_comp_fst` and
  `AlgebraicGeometry.smallEtale_comp4_hom_left` read base change of a morphism of the small
  étale site, and a four-fold composite there, on the underlying morphisms of schemes.

Nothing here is empty: every morphism of represented algebraic spaces is relatively
representable (`AlgebraicGeometry.Space.relativelyRepresentable_yoneda_map`), so the three
witnesses are always available, and `hgc := h ≫ g` with `w := rfl` is always a factorisation.
The witnesses are kept as explicit arguments because
`CategoryTheory.Functor.relativelyRepresentable.pullback` is a choice and a consumer holds its
own.

## Implementation notes

No value of either comparison is computed.  At a chart both sides are morphisms **into** a chosen
fibre product of the bounded category of schemes, and a morphism of the small étale site into a
base change is determined by its first component — its second component is its own structure
morphism, because it is a morphism over the base of the base change.  So the law is the single
identity obtained by composing with the first projection, and there each of the four factors is
replaced by its own characterisation:

* the two comparisons by `AlgebraicGeometry.Space.representedSmallEtaleBaseChangeComponent_hom`
  together with `CategoryTheory.IsPullback.isoIsPullback_hom_fst`, packaged as
  `AlgebraicGeometry.Space.representedSmallEtaleBaseChangeComponent_hom_comp_fst`;
* the base change of the comparison for `g` by
  `AlgebraicGeometry.smallEtaleBaseChange_map_left_comp_fst`;
* the schemes-side composition comparison by
  `AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso_hom_app_fst`;
* the spaces-side composition comparison by
  `CategoryTheory.Functor.relativelyRepresentable.pullbackCompInv_snd`, which is what
  `AlgebraicGeometry.Space.smallBaseChange_comp_inv_projection` is.

The composite of the two projections of the iterated chosen base change is the projection of the
base change along the composite, on either side, which is why nothing else is needed.

Those five identities are combined by `Stacks.CategoryTheory.comp_four_comp_projection`, a lemma
about composition in an arbitrary category in which every datum is a variable.  That placement is
forced rather than stylistic, for two reasons.

First, the identity cannot be assembled by rewriting in the goal.  The goal mixes the two
spellings `B.Schemes` and `(AlgebraicGeometry.associatedBigEtaleSite B).Scheme` of the bounded
category of schemes, so it is not type-correct at `implicit` transparency and a `rw` step in it
fails with that note; the generic engine does its rewriting where there is only one spelling.

Second — and this is what made the difference between a deterministic timeout and 0.6 s — the
engine takes the composite as a *variable* `m` together with `hm : m = a ≫ b ≫ c ≫ d`.  The
composite of the four factors is a morphism of the small étale site, and recognising its
underlying morphism of schemes as the composite of the four underlying morphisms — three
unfoldings of composition in a full subcategory of a slice category — exhausts the
200,000-heartbeat budget when it is left to the unifier at these objects: the diagnostics show it
descending through `CategoryTheory.Limits.limit.cone` into the structure maps of the schemes
themselves (122,475 unfoldings of it, and 218,597 attempts on the non-exposed `getLimitCone`).
Supplied instead as `AlgebraicGeometry.smallEtale_comp4_hom_left`, a `rfl` lemma at plain
variables, it costs nothing.  Nothing else in the application is measurable — in particular the
three different spellings of the cartesian projection that occur here (the one in the goal, the
one of the schemes-side composition comparison, and the one of the comparison at a chart) are
reconciled for free, which is worth recording because it is the explanation one reaches for
first and it is not the cause.

The composite is taken as a separate morphism `hgc` together with `w : h ≫ g = hgc` rather than
literally `h ≫ g`, on both sides of the square: the schemes side already offers that form as
`AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso`, and the spaces side is given it here.
A consumer then never has to unfold a composition of the slice category inside a larger
elaboration, and the literal case is `w := rfl`
(`AlgebraicGeometry.Space.smallBaseChange_factoredComp_rfl`).

The extensionality principle used here is also available as
`AlgebraicGeometry.smallEtaleBaseChange_hom_ext`, but that is stated in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Constructible/SplitPushforwardProduct.lean`, whose
import closure is far larger than this file's; its two lines are therefore taken directly from
`CategoryTheory.Limits.pullback.hom_ext` and `CategoryTheory.Over.w` instead of importing that
module.

## References

* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 021J](https://stacks.math.columbia.edu/tag/021J)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.CategoryTheory

open CategoryTheory

/-- **Four comparisons pasted along their projections.**  A composite of four morphisms, read
through a projection of its target, where each factor is characterised by its composite with a
projection: the last carries `π` to `πD ≫ πg`, the third carries `πD` to `πC ≫ θ`, the second
carries `πC` to `β`, `θ` carries `πg` to `γ`, and the first carries `β ≫ γ` to `δ`.

Every datum is a variable, so an instantiation restates nothing. -/
theorem comp_four_comp_projection {𝒞 : Type*} [Category 𝒞]
    {X₁ X₂ X₃ X₄ X₅ M N R : 𝒞} {m : X₁ ⟶ X₅}
    {a : X₁ ⟶ X₂} {b : X₂ ⟶ X₃} {c : X₃ ⟶ X₄} {d : X₄ ⟶ X₅}
    {π : X₅ ⟶ R} {πD : X₄ ⟶ M} {πC : X₃ ⟶ N} {πg : M ⟶ R} {θ : N ⟶ M}
    {β : X₂ ⟶ N} {γ : N ⟶ R} {δ : X₁ ⟶ R} (hm : m = a ≫ b ≫ c ≫ d)
    (hd : d ≫ π = πD ≫ πg) (hc : c ≫ πD = πC ≫ θ) (hb : b ≫ πC = β)
    (hθ : θ ≫ πg = γ) (ha : a ≫ β ≫ γ = δ) :
    m ≫ π = δ := by
  subst hm
  simp only [Category.assoc]
  rw [hd, reassoc_of% hc, reassoc_of% hb, hθ]
  exact ha

end Stacks.CategoryTheory

namespace AlgebraicGeometry

/-- A composite of four morphisms of the small étale site, read on the underlying morphisms of
the bounded category of schemes. -/
theorem smallEtale_comp4_hom_left (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)
    {A₁ A₂ A₃ A₄ A₅ : SmallEtale B X hX} (x : A₁ ⟶ A₂) (y : A₂ ⟶ A₃) (z : A₃ ⟶ A₄)
    (u : A₄ ⟶ A₅) :
    (x ≫ y ≫ z ≫ u).hom.left =
      x.hom.left ≫ y.hom.left ≫ z.hom.left ≫ u.hom.left :=
  rfl

/-- Base change of a morphism of the small étale site, followed by the cartesian projection to
the original chart, is that projection followed by the morphism. -/
theorem smallEtaleBaseChange_map_left_comp_fst (B : BigEtaleSite.{u}) {S T : B.Scheme}
    (p : T ⟶ S) {A A' : SmallEtale B S.obj S.property} (a : A ⟶ A') :
    ((smallEtaleBaseChange B p).map a).hom.left ≫ pullback.fst A'.obj.hom p =
      pullback.fst A.obj.hom p ≫ a.hom.left := by
  rw [smallEtaleBaseChange_map_left]
  exact pullback.lift_fst _ _ _

namespace Space

attribute [local instance] BigFppfSite.hasPullbacks_schemes

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Base change of étale scheme charts along a factorised composite -/

section FactoredComp

variable {X Y Z : AlgebraicSpaces B S hS}

/-- `AlgebraicGeometry.Space.smallBaseChange_comp` for a composite presented by a separate
morphism `fg` together with a factorisation `f ≫ g = fg`. -/
noncomputable def smallBaseChange_factoredComp (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (hf : yoneda.relativelyRepresentable f.hom) (hg : yoneda.relativelyRepresentable g.hom)
    (hfg : yoneda.relativelyRepresentable fg.hom) (w : f ≫ g = fg) :
    smallBaseChange B S hS g hg ⋙ smallBaseChange B S hS f hf ≅
      smallBaseChange B S hS fg hfg := by
  subst w
  exact smallBaseChange_comp B S hS f g hf hg hfg

/-- At the literal composite the factorised comparison is
`AlgebraicGeometry.Space.smallBaseChange_comp`. -/
theorem smallBaseChange_factoredComp_rfl (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : yoneda.relativelyRepresentable f.hom) (hg : yoneda.relativelyRepresentable g.hom)
    (hfg : yoneda.relativelyRepresentable (f ≫ g).hom) :
    smallBaseChange_factoredComp B S hS f g (f ≫ g) hf hg hfg rfl =
      smallBaseChange_comp B S hS f g hf hg hfg :=
  rfl

/-- The inverse of the factorised composition comparison, read on the underlying morphism of the
big fppf category over `S`. -/
theorem smallBaseChange_factoredComp_inv_app_hom_left (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (hf : yoneda.relativelyRepresentable f.hom) (hg : yoneda.relativelyRepresentable g.hom)
    (hfg : yoneda.relativelyRepresentable fg.hom) (w : f ≫ g = fg)
    (V : SmallEtale B S hS Z.1) :
    ((smallBaseChange_factoredComp B S hS f g fg hf hg hfg w).inv.app V).hom.left =
      Functor.relativelyRepresentable.pullbackCompInv hf hg hfg
        (congrArg (fun m : X ⟶ Z => m.hom) w) V.1.hom := by
  subst w
  exact smallBaseChange_comp_inv_app_hom_left B S hS f g hf hg hfg V

/-- The inverse of the factorised composition comparison carries the composite of the two
cartesian projections of the iterated base change to the cartesian projection of the base change
along the composite, read on the underlying morphisms of the bounded category of schemes. -/
theorem smallBaseChange_factoredComp_inv_left_snd (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (hf : yoneda.relativelyRepresentable f.hom) (hg : yoneda.relativelyRepresentable g.hom)
    (hfg : yoneda.relativelyRepresentable fg.hom) (w : f ≫ g = fg)
    (V : SmallEtale B S hS Z.1) :
    ((smallBaseChange_factoredComp B S hS f g fg hf hg hfg w).inv.app V).hom.left.left ≫
        (hf.snd ((smallBaseChange B S hS g hg).obj V).1.hom).left ≫ (hg.snd V.1.hom).left =
      (hfg.snd V.1.hom).left := by
  subst w
  exact congrArg (fun m : hfg.pullback V.1.hom ⟶ V.1.left => m.left)
    (Functor.relativelyRepresentable.pullbackCompInv_snd hf hg hfg rfl V.1.hom)

end FactoredComp

/-! ### The composition law -/

section RepresentedComp

variable {T'' T' T : BigFppfOver B S hS}

/-- The identification of the small étale site of a representable algebraic space with the small
étale site of the underlying scheme acts on morphisms by the underlying morphism of the bounded
category of schemes. -/
theorem representedSmallEtaleEquivalence_functor_map_hom_left (U : BigFppfOver B S hS)
    {V W : SmallEtale B S hS (yoneda.obj U)} (k : V ⟶ W) :
    ((representedSmallEtaleEquivalence B S hS U).functor.map k).hom.left = k.hom.left.left :=
  rfl

/-- Passing to represented algebraic spaces carries a factorisation of a composite to a
factorisation of the composite of the represented morphisms.  This is
`AlgebraicGeometry.Space.representedSpaceMap_comp` in factorised form, and holds for the same
reason: by `rfl`. -/
theorem representedSpaceMap_comp_eq (h : T'' ⟶ T') (g : T' ⟶ T) (hgc : T'' ⟶ T)
    (w : h ≫ g = hgc) :
    representedSpaceMap B S hS h ≫ representedSpaceMap B S hS g =
      representedSpaceMap B S hS hgc := by
  subst w
  rfl

/-- `AlgebraicGeometry.Space.smallBaseChange_factoredComp_inv_left_snd` for the represented
morphisms, with the comparison read through the identification of the two sites — the spelling in
which the composition law at a chart meets it. -/
theorem representedSmallBaseChange_factoredComp_inv_left_snd (h : T'' ⟶ T') (g : T' ⟶ T)
    (hgc : T'' ⟶ T) (w : h ≫ g = hgc)
    (hh : yoneda.relativelyRepresentable (yoneda.map h))
    (hg : yoneda.relativelyRepresentable (yoneda.map g))
    (hc : yoneda.relativelyRepresentable (yoneda.map hgc))
    (V : SmallEtale B S hS (yoneda.obj T)) :
    ((representedSmallEtaleEquivalence B S hS T'').functor.map
            ((smallBaseChange_factoredComp B S hS (representedSpaceMap B S hS h)
              (representedSpaceMap B S hS g) (representedSpaceMap B S hS hgc) hh hg hc
              (representedSpaceMap_comp_eq B S hS h g hgc w)).inv.app V)).hom.left ≫
        (hh.snd ((smallBaseChange B S hS (representedSpaceMap B S hS g) hg).obj V).1.hom).left ≫
          (hg.snd V.1.hom).left =
      (hc.snd V.1.hom).left :=
  smallBaseChange_factoredComp_inv_left_snd B S hS (representedSpaceMap B S hS h)
    (representedSpaceMap B S hS g) (representedSpaceMap B S hS hgc) hh hg hc
    (representedSpaceMap_comp_eq B S hS h g hgc w) V

/-- **The sites-level composition law, at a single étale chart.**  The comparison of the two base
changes along `hgc` is the composition comparison of chart base change, the comparison along `h`,
the comparison along `g` base changed along `h`, and the composition comparison of base change of
schemes. -/
theorem representedSmallEtaleBaseChangeComponent_comp (h : T'' ⟶ T') (g : T' ⟶ T)
    (hgc : T'' ⟶ T) (w : h ≫ g = hgc)
    (hh : yoneda.relativelyRepresentable (yoneda.map h))
    (hg : yoneda.relativelyRepresentable (yoneda.map g))
    (hc : yoneda.relativelyRepresentable (yoneda.map hgc))
    (V : SmallEtale B S hS (yoneda.obj T)) :
    (representedSmallEtaleBaseChangeComponent B S hS hgc hc V).hom =
      (representedSmallEtaleEquivalence B S hS T'').functor.map
          ((smallBaseChange_factoredComp B S hS (representedSpaceMap B S hS h)
              (representedSpaceMap B S hS g) (representedSpaceMap B S hS hgc) hh hg hc
              (representedSpaceMap_comp_eq B S hS h g hgc w)).inv.app V) ≫
        (representedSmallEtaleBaseChangeComponent B S hS h hh
            ((smallBaseChange B S hS (representedSpaceMap B S hS g) hg).obj V)).hom ≫
          (_root_.AlgebraicGeometry.smallEtaleBaseChange (associatedBigEtaleSite B) h.left).map
              (representedSmallEtaleBaseChangeComponent B S hS g hg V).hom ≫
            (_root_.AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso
                (associatedBigEtaleSite B) T''.left T'.left T.left h.left g.left hgc.left
                (congrArg (fun m : T'' ⟶ T => m.left) w)).hom.app
              ((representedSmallEtaleEquivalence B S hS T).functor.obj V) := by
  have key := Stacks.CategoryTheory.comp_four_comp_projection
        (_root_.AlgebraicGeometry.smallEtale_comp4_hom_left (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj T'') T''.left.property
          ((representedSmallEtaleEquivalence B S hS T'').functor.map
            ((smallBaseChange_factoredComp B S hS (representedSpaceMap B S hS h)
                (representedSpaceMap B S hS g) (representedSpaceMap B S hS hgc) hh hg hc
                (representedSpaceMap_comp_eq B S hS h g hgc w)).inv.app V))
          (representedSmallEtaleBaseChangeComponent B S hS h hh
            ((smallBaseChange B S hS (representedSpaceMap B S hS g) hg).obj V)).hom
          ((_root_.AlgebraicGeometry.smallEtaleBaseChange (associatedBigEtaleSite B) h.left).map
            (representedSmallEtaleBaseChangeComponent B S hS g hg V).hom)
          ((_root_.AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso
              (associatedBigEtaleSite B) T''.left T'.left T.left h.left g.left hgc.left
              (congrArg (fun m : T'' ⟶ T => m.left) w)).hom.app
            ((representedSmallEtaleEquivalence B S hS T).functor.obj V)))
        (_root_.AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso_hom_app_fst
          (associatedBigEtaleSite B) T''.left T'.left T.left h.left g.left hgc.left
          (congrArg (fun m : T'' ⟶ T => m.left) w)
          ((representedSmallEtaleEquivalence B S hS T).functor.obj V))
        (_root_.AlgebraicGeometry.smallEtaleBaseChange_map_left_comp_fst
          (associatedBigEtaleSite B) h.left
          (representedSmallEtaleBaseChangeComponent B S hS g hg V).hom)
        (representedSmallEtaleBaseChangeComponent_hom_comp_fst B S hS h hh
          ((smallBaseChange B S hS (representedSpaceMap B S hS g) hg).obj V))
        (representedSmallEtaleBaseChangeComponent_hom_comp_fst B S hS g hg V)
        (representedSmallBaseChange_factoredComp_inv_left_snd B S hS h g hgc w hh hg hc V)
  refine ObjectProperty.hom_ext _ (Over.OverMorphism.ext (pullback.hom_ext ?_ ?_))
  · exact (representedSmallEtaleBaseChangeComponent_hom_comp_fst B S hS hgc hc V).trans key.symm
  · exact (Over.w _).trans (Over.w _).symm

/-- **The sites-level composition law**, for the natural transformations. -/
theorem representedSmallEtaleBaseChangeIso_hom_comp (h : T'' ⟶ T') (g : T' ⟶ T)
    (hgc : T'' ⟶ T) (w : h ≫ g = hgc)
    (hh : yoneda.relativelyRepresentable (yoneda.map h))
    (hg : yoneda.relativelyRepresentable (yoneda.map g))
    (hc : yoneda.relativelyRepresentable (yoneda.map hgc)) :
    (representedSmallEtaleBaseChangeIso B S hS hgc hc).hom =
      Functor.whiskerRight
          (smallBaseChange_factoredComp B S hS (representedSpaceMap B S hS h)
            (representedSpaceMap B S hS g) (representedSpaceMap B S hS hgc) hh hg hc
            (representedSpaceMap_comp_eq B S hS h g hgc w)).inv
          (representedSmallEtaleEquivalence B S hS T'').functor ≫
        Functor.whiskerLeft (smallBaseChange B S hS (representedSpaceMap B S hS g) hg)
            (representedSmallEtaleBaseChangeIso B S hS h hh).hom ≫
          Functor.whiskerRight (representedSmallEtaleBaseChangeIso B S hS g hg).hom
              (_root_.AlgebraicGeometry.smallEtaleBaseChange
                (associatedBigEtaleSite B) h.left) ≫
            Functor.whiskerLeft (representedSmallEtaleEquivalence B S hS T).functor
              (_root_.AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso
                (associatedBigEtaleSite B) T''.left T'.left T.left h.left g.left hgc.left
                (congrArg (fun m : T'' ⟶ T => m.left) w)).hom :=
  NatTrans.ext (funext fun V =>
    representedSmallEtaleBaseChangeComponent_comp B S hS h g hgc w hh hg hc V)

/-- **The sites-level composition law**, for the natural isomorphisms. -/
theorem representedSmallEtaleBaseChangeIso_eq_factoredComp (h : T'' ⟶ T') (g : T' ⟶ T)
    (hgc : T'' ⟶ T) (w : h ≫ g = hgc)
    (hh : yoneda.relativelyRepresentable (yoneda.map h))
    (hg : yoneda.relativelyRepresentable (yoneda.map g))
    (hc : yoneda.relativelyRepresentable (yoneda.map hgc)) :
    representedSmallEtaleBaseChangeIso B S hS hgc hc =
      (Functor.isoWhiskerRight
          (smallBaseChange_factoredComp B S hS (representedSpaceMap B S hS h)
            (representedSpaceMap B S hS g) (representedSpaceMap B S hS hgc) hh hg hc
            (representedSpaceMap_comp_eq B S hS h g hgc w))
          (representedSmallEtaleEquivalence B S hS T'').functor).symm ≪≫
        Functor.isoWhiskerLeft (smallBaseChange B S hS (representedSpaceMap B S hS g) hg)
            (representedSmallEtaleBaseChangeIso B S hS h hh) ≪≫
          Functor.isoWhiskerRight (representedSmallEtaleBaseChangeIso B S hS g hg)
              (_root_.AlgebraicGeometry.smallEtaleBaseChange
                (associatedBigEtaleSite B) h.left) ≪≫
            Functor.isoWhiskerLeft (representedSmallEtaleEquivalence B S hS T).functor
              (_root_.AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso
                (associatedBigEtaleSite B) T''.left T'.left T.left h.left g.left hgc.left
                (congrArg (fun m : T'' ⟶ T => m.left) w)) :=
  Iso.ext (representedSmallEtaleBaseChangeIso_hom_comp B S hS h g hgc w hh hg hc)

end RepresentedComp

end Space

end AlgebraicGeometry

end
