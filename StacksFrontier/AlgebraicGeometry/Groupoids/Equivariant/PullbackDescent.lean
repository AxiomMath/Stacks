module

public import StacksFrontier.AlgebraicGeometry.Groupoids.DescentIso
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme

/-!
# Reindexing the pullback of a descent morphism along a morphism of groupoid schemes

For a morphism `f` of groupoid schemes over `S`, `Stacks.Groupoids.GroupoidScheme.pullbackDescent`
is the descent morphism obtained by pulling a descent morphism back along the map on objects.
This file gives its calculus: reindexing it along a morphism into the scheme of arrows produces
again a morphism of the same shape with the arrow map of `f` inserted, and reindexing it along
the identity section of the groupoid returns the identity — the normalization condition required
of a quasi-coherent module on a groupoid scheme.

## Main results

* `Stacks.Groupoids.GroupoidScheme.reindexHom_pullbackDescent` reindexes the pulled-back descent
  morphism along a morphism into the scheme of arrows.
* `Stacks.Groupoids.GroupoidScheme.pullbackDescent_identity` is the normalization of the
  pulled-back descent morphism along the identity section.
* `Stacks.Groupoids.GroupoidScheme.map_target_left_assoc` and
  `Stacks.Groupoids.GroupoidScheme.map_source_left_assoc` are the two commuting squares of a
  morphism of groupoid schemes, precomposed with a morphism into the scheme of arrows; they are
  the hypotheses of `reindexHom_pullbackDescent`.
* `Stacks.Groupoids.pullbackCongr_pullbackComp` commutes the comparison of pullbacks along equal
  morphisms past the comparison for a composite.

## Implementation notes

Pullback of modules is a pseudofunctor rather than a functor, so the canonical comparison
isomorphisms between iterated pullbacks and pullback along a composite appear throughout, and
the phrase `f⁺α` of the source is interpreted through the two commuting squares relating the
source and target maps of the two groupoid schemes rather than by treating canonically
isomorphic pullbacks as definitionally equal.  The auxiliary lemmas of this file are the part of
that calculus which relates the comparison for a composite to the comparison for its two halves,
and which `Stacks.Groupoids.reindexHom_assoc` does not already supply.

The hypotheses `wt` and `ws` of `reindexHom_pullbackDescent` are stated rather than derived so
that any proof of them may be supplied; `map_target_left_assoc` and `map_source_left_assoc` are
the canonical ones.

## References

* [Stacks Project, Tag 03LJ](https://stacks.math.columbia.edu/tag/03LJ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Groupoids

/-- Moving the comparison of iterated pullbacks past the comparison for a composite,
left-associated form. -/
@[reassoc]
private theorem pullbackComp_assoc_bridge_inv {X Y Z W : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) (F : W.Modules) :
    (Scheme.Modules.pullback f).map
        ((Scheme.Modules.pullbackComp g h).inv.app F) ≫
      (Scheme.Modules.pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj F) =
    (Scheme.Modules.pullbackComp f (g ≫ h)).hom.app F ≫
      (Scheme.Modules.pullbackCongr (Category.assoc f g h).symm).hom.app F ≫
      (Scheme.Modules.pullbackComp (f ≫ g) h).inv.app F := by
  have hp := NatTrans.congr_app
    (Scheme.Modules.pseudofunctor_associativity f g h) F
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp] at hp
  rw [← cancel_epi ((Scheme.Modules.pullbackComp f (g ≫ h)).inv.app F),
    ← cancel_mono ((Scheme.Modules.pullbackComp (f ≫ g) h).hom.app F)]
  simpa [Scheme.Modules.pullbackCongr] using hp

/-- Moving the comparison of iterated pullbacks past the comparison for a composite,
right-associated form. -/
@[reassoc]
private theorem pullbackComp_assoc_bridge {X Y Z W : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) (F : W.Modules) :
    (Scheme.Modules.pullbackComp f g).inv.app
        ((Scheme.Modules.pullback h).obj F) ≫
      (Scheme.Modules.pullback f).map
        ((Scheme.Modules.pullbackComp g h).hom.app F) =
      (Scheme.Modules.pullbackComp (f ≫ g) h).hom.app F ≫
        (Scheme.Modules.pullbackCongr (Category.assoc f g h)).hom.app F ≫
        (Scheme.Modules.pullbackComp f (g ≫ h)).inv.app F := by
  have hl : ((Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).inv.app F) ≫
      (Scheme.Modules.pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj F)) ≫
      (Scheme.Modules.pullbackComp f g).inv.app ((Scheme.Modules.pullback h).obj F) ≫
        (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).hom.app F) =
      𝟙 _ := by
    simp [← Functor.map_comp]
  rw [← cancel_epi ((Scheme.Modules.pullback f).map
    ((Scheme.Modules.pullbackComp g h).inv.app F) ≫
      (Scheme.Modules.pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj F)),
    hl, Category.assoc, pullbackComp_assoc_bridge_inv_assoc]
  simp [Scheme.Modules.pullbackCongr]

/-- The comparison of pullbacks along equal morphisms commutes past the comparison for a
composite. -/
@[reassoc]
theorem pullbackCongr_pullbackComp {X Y Z : Scheme.{u}}
    {g h : X ⟶ Y} (p : g = h) (m : Y ⟶ Z) (F : Z.Modules) :
    (Scheme.Modules.pullbackCongr p).hom.app ((Scheme.Modules.pullback m).obj F) ≫
      (Scheme.Modules.pullbackComp h m).hom.app F =
    (Scheme.Modules.pullbackComp g m).hom.app F ≫
      (Scheme.Modules.pullbackCongr (congrArg (fun k => k ≫ m) p)).hom.app F := by
  cases p
  simp [Scheme.Modules.pullbackCongr]

/-- Reindexing a morphism which is conjugated by the comparisons for a composite, rewritten so
that the conjugation is by the comparisons for the reindexed composites. -/
private theorem reindexHom_unflatten {X Y Z W : Scheme.{u}}
    (k : X ⟶ Y) (g h : Y ⟶ Z) (m : Z ⟶ W) (F : W.Modules)
    (α : (Scheme.Modules.pullback (g ≫ m)).obj F ⟶
      (Scheme.Modules.pullback (h ≫ m)).obj F) :
    reindexHom k ((Scheme.Modules.pullbackComp g m).hom.app F ≫ α ≫
        (Scheme.Modules.pullbackComp h m).inv.app F) =
    (Scheme.Modules.pullbackComp (k ≫ g) m).hom.app F ≫
      (Scheme.Modules.pullbackCongr (Category.assoc k g m)).hom.app F ≫
      reindexHom k α ≫
      (Scheme.Modules.pullbackCongr (Category.assoc k h m).symm).hom.app F ≫
      (Scheme.Modules.pullbackComp (k ≫ h) m).inv.app F := by
  simp only [reindexHom, Functor.map_comp, Category.assoc,
    pullbackComp_assoc_bridge_assoc, pullbackComp_assoc_bridge_inv]

namespace GroupoidScheme

variable {S : Scheme.{u}} {G H : GroupoidScheme S}

/-- Compatibility with the target maps, composed with a morphism into the arrows. -/
theorem map_target_left_assoc (f : Hom G H) {X : Scheme.{u}}
    (k : X ⟶ G.arrows.left) :
    (k ≫ G.target.left) ≫ f.mapObjects.left =
      (k ≫ f.mapArrows.left) ≫ H.target.left := by
  rw [Category.assoc, ← f.map_target_left, ← Category.assoc]

/-- Compatibility with the source maps, composed with a morphism into the arrows. -/
theorem map_source_left_assoc (f : Hom G H) {X : Scheme.{u}}
    (k : X ⟶ G.arrows.left) :
    (k ≫ f.mapArrows.left) ≫ H.source.left =
      (k ≫ G.source.left) ≫ f.mapObjects.left := by
  rw [Category.assoc, f.map_source_left, ← Category.assoc]

/-- Reindexing the pulled-back descent morphism along a morphism into the scheme of arrows is
again of the same shape, with the arrow map of the morphism of groupoid schemes inserted. -/
theorem reindexHom_pullbackDescent (f : Hom G H) (M : QuasicoherentModule H)
    {X : Scheme.{u}} (k : X ⟶ G.arrows.left)
    (wt : (k ≫ G.target.left) ≫ f.mapObjects.left =
      (k ≫ f.mapArrows.left) ≫ H.target.left)
    (ws : (k ≫ f.mapArrows.left) ≫ H.source.left =
      (k ≫ G.source.left) ≫ f.mapObjects.left) :
    reindexHom k (pullbackDescent f M) =
    (Scheme.Modules.pullbackComp (k ≫ G.target.left) f.mapObjects.left).hom.app M.module ≫
      (Scheme.Modules.pullbackCongr wt).hom.app M.module ≫
      reindexHom (k ≫ f.mapArrows.left) M.alpha ≫
      (Scheme.Modules.pullbackCongr ws).hom.app M.module ≫
      (Scheme.Modules.pullbackComp (k ≫ G.source.left)
        f.mapObjects.left).inv.app M.module := by
  have key : pullbackDescent f M =
      (Scheme.Modules.pullbackComp G.target.left f.mapObjects.left).hom.app M.module ≫
        ((Scheme.Modules.pullbackCongr f.map_target_left.symm).hom.app M.module ≫
          reindexHom f.mapArrows.left M.alpha ≫
          (Scheme.Modules.pullbackCongr f.map_source_left).hom.app M.module) ≫
        (Scheme.Modules.pullbackComp G.source.left
          f.mapObjects.left).inv.app M.module := by
    unfold pullbackDescent
    simp only [Category.assoc]
  rw [key, reindexHom_unflatten]
  simp only [reindexHom_comp, reindexHom_congr, reindexHom_assoc_rev]
  simp [Scheme.Modules.pullbackCongr, Category.assoc]

/-- The pulled-back descent morphism is normalized along the identity section. -/
theorem pullbackDescent_identity (f : Hom G H) (M : QuasicoherentModule H) :
    identityDescent G (pullbackDescent f M) =
      𝟙 ((Scheme.Modules.pullback f.mapObjects.left).obj M.module) := by
  have he : G.identity.left ≫ f.mapArrows.left =
      f.mapObjects.left ≫ H.identity.left := by
    rw [← Over.comp_left, ← Over.comp_left, f.map_identity]
  have ht : G.identity.left ≫ G.target.left = 𝟙 G.objects.left :=
    identity_left_comp_target_left G
  have hs : G.identity.left ≫ G.source.left = 𝟙 G.objects.left :=
    identity_left_comp_source_left G
  have hr : reindexHom G.identity.left (pullbackDescent f M) =
      (Scheme.Modules.pullbackCongr (ht.trans hs.symm)).hom.app
        ((Scheme.Modules.pullback f.mapObjects.left).obj M.module) := by
    rw [reindexHom_pullbackDescent f M _ (map_target_left_assoc f _) (map_source_left_assoc f _),
      reindexHom_congr_source he, reindexHom_comp_identity H f.mapObjects.left M.alpha M.identity]
    apply (cancel_mono ((Scheme.Modules.pullbackComp
      (G.identity.left ≫ G.source.left) f.mapObjects.left).hom.app M.module)).1
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    rw [pullbackCongr_pullbackComp (ht.trans hs.symm)]
    simp [Scheme.Modules.pullbackCongr]
  simp [identityDescent, hr, Scheme.Modules.pullbackCongr]

end GroupoidScheme

end Stacks.Groupoids

end
