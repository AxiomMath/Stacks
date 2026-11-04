module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleMorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.MorphismComposition

/-!
# The morphisms of ringed sites `ε_a` compose

Let `a : X ⟶ Y` and `b : Y ⟶ Z` be morphisms of a big étale site. Each of them gives a morphism of
ringed sites `ε` between the small étale sites, whose site half is base change and whose structure
map pulls a global function on an étale `W / Z` back along the base-change projection;
`AlgebraicGeometry.SmallEtale.smallEtaleStructureMapRing` is that structure map, read on sheaves
of not necessarily commutative rings.

The structure maps compose: `ε_{b ∘ a}` is `ε_a` after `ε_b`, once the two successive base changes
are identified with the base change along the composite by
`AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.smallEtaleStructureMapRingHom`: the structure map of `ε_a` at the
  presheaf-level spelling of its target.

## Main results

* `AlgebraicGeometry.SmallEtale.smallEtaleStructureMapRingHom_app_comp`: the structure maps of the
  morphisms of ringed sites `ε_a`, `ε_b` and `ε_{b ∘ a}` compose, on sections.
* `AlgebraicGeometry.SmallEtale.inclusion_map_fst_comp_fst`: the triangle of base-change
  projections `X ×_Y (Y ×_Z W) ⟶ Y ×_Z W ⟶ W` and `X ×_Z W ⟶ W`, on underlying schemes.

## References

* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 075D](https://stacks.math.columbia.edu/tag/075D)
* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
* [Stacks Project, Tag 021J](https://stacks.math.columbia.edu/tag/021J)
* [Stacks Project, Tag 076T](https://stacks.math.columbia.edu/tag/076T)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {X Y Z : B.Scheme} (a : X ⟶ Y) (b : Y ⟶ Z)

/-- For `a : X ⟶ Y` and `b : Y ⟶ Z` of the big étale site and `W` a small étale object over `Z`,
on underlying schemes the projection `X ×_Y (Y ×_Z W) ⟶ Y ×_Z W ⟶ W` is the comparison of the two
base changes followed by the projection `X ×_Z W ⟶ W`. -/
public theorem inclusion_map_fst_comp_fst (W : SmallEtale B Z.obj Z.property) :
    B.inclusion.map (Limits.pullback.fst ((smallEtaleBaseChange B b).obj W).obj.hom a) ≫
        B.inclusion.map (Limits.pullback.fst W.obj.hom b) =
      B.inclusion.map (((smallEtaleBaseChange_factoredCompIso B X Y Z a b
          (a ≫ b) rfl).hom.app W).hom.left) ≫
        B.inclusion.map (Limits.pullback.fst W.obj.hom (a ≫ b)) :=
  (B.inclusion.map_comp _ _).symm.trans
    ((congrArg B.inclusion.map
        (smallEtaleBaseChange_factoredCompIso_hom_app_fst B X Y Z a b
          (a ≫ b) rfl W).symm).trans
      (B.inclusion.map_comp _ _))

/-- The structure map of `ε_a` as a morphism of presheaves of rings, from the structure presheaf of
the small étale site of `Y` to the composite of the base change along `a` with the structure
presheaf of the small étale site of `X`. -/
public noncomputable abbrev smallEtaleStructureMapRingHom :
    (structureSheaf B Y.obj Y.property).obj ⟶
      (smallEtaleBaseChange B a).op ⋙ (structureSheaf B X.obj X.property).obj :=
  (smallEtaleStructureMapRing B a).hom

/-- The structure maps of the morphisms of ringed sites `ε_a` compose. For `a : X ⟶ Y` and
`b : Y ⟶ Z` of the big étale site and `W` a small étale object over `Z`, pulling a global function
on `W` back along the projection `Y ×_Z W ⟶ W` and then along `X ×_Y (Y ×_Z W) ⟶ Y ×_Z W` is
pulling it back along `X ×_Z W ⟶ W` and restricting along the comparison of the two base
changes. -/
public theorem smallEtaleStructureMapRingHom_app_comp (W : (SmallEtale B Z.obj Z.property)ᵒᵖ)
    (r : (structureSheaf B Z.obj Z.property).obj.obj W) :
    (smallEtaleStructureMapRingHom B a).app ((smallEtaleBaseChange B b).op.obj W)
        ((smallEtaleStructureMapRingHom B b).app W r) =
      (structureSheaf B X.obj X.property).obj.map
        ((smallEtaleBaseChange_factoredCompIso B X Y Z a b (a ≫ b) rfl).hom.app W.unop).op
        ((smallEtaleStructureMapRingHom B (a ≫ b)).app W r) := by
  induction W with | op W => ?_
  have fuse : ∀ {P Q R : Scheme.{u}} (f : P ⟶ Q) (g : Q ⟶ R)
      (t : ((forget₂ CommRingCat.{u} RingCat.{u}).obj (Scheme.Γ.obj (op R)))),
      (forget₂ CommRingCat.{u} RingCat.{u}).map (Scheme.Γ.map f.op)
          ((forget₂ CommRingCat.{u} RingCat.{u}).map (Scheme.Γ.map g.op) t) =
        (forget₂ CommRingCat.{u} RingCat.{u}).map (Scheme.Γ.map (f ≫ g).op) t :=
    fun f g t ↦ by rw [op_comp, Scheme.Γ.map_comp, Functor.map_comp]; rfl
  refine (fuse (B.inclusion.map (Limits.pullback.fst
        ((smallEtaleBaseChange B b).obj W).obj.hom a))
      (B.inclusion.map (Limits.pullback.fst W.obj.hom b)) r).trans
    (Eq.trans ?_ (fuse (B.inclusion.map (((smallEtaleBaseChange_factoredCompIso B X Y Z a b
        (a ≫ b) rfl).hom.app W).hom.left))
      (B.inclusion.map (Limits.pullback.fst W.obj.hom (a ≫ b))) r).symm)
  rw [inclusion_map_fst_comp_fst]
  rfl

end AlgebraicGeometry.SmallEtale

end
