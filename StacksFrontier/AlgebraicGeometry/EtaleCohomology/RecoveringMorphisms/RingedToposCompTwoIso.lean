module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.RingedToposTwoIso
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.MorphismComposition

/-!
# Composition of the small étale ringed topos morphisms of morphisms of schemes

Let `a : X ⟶ Y` and `q : Y ⟶ Z` be morphisms of schemes of a big étale site.  Stacks 070R
part (2) attaches to each of them a morphism of small étale ringed topoi, and the assignment is
functorial up to a canonical 2-isomorphism: the morphism of ringed topoi of `a ≫ q` is
2-isomorphic to the composite of the morphisms of ringed topoi of `a` and of `q`.

The comparison is not an equality because the fibre products presenting small étale base change
are chosen, so base change along `a ≫ q` agrees with iterated base change only up to the
canonical comparison `AlgebraicGeometry.smallEtaleBaseChange_compIso` of Stacks 021J.  The
geometric half of the 2-isomorphism is the induced comparison of direct images, and its
structure-map half is the statement that pulling a global function back along the projection
`X ×_Z W ⟶ W` is the same as pulling it back along `Y ×_Z W ⟶ W` and then along
`X ×_Y (Y ×_Z W) ⟶ Y ×_Z W`, which is `CategoryTheory.Over.pullbackComp_inv_app_left_fst`
read through the global sections functor.

## Main definitions

* `AlgebraicGeometry.smallEtaleRingedToposHomCompPushforwardIso` — the comparison of the
  composite of the two direct images with the direct image of the composite, at the universe of
  the sections of the structure sheaves.
* `AlgebraicGeometry.smallEtaleRingedToposHomCompTwoIso` — the composition 2-isomorphism.

## Main results

* `AlgebraicGeometry.toScheme_map_smallEtaleBaseChange_compIso_hom_app_comp` — the geometric
  content of the structure-map half: the comparison of base changes carries the projection of
  the base change along the composite to the composite of the two projections.

## Implementation notes

`AlgebraicGeometry.smallEtaleMorphism_comp_pushforwardIso` is the same comparison of direct
images, but stated for sheaves of sets valued in `Type (u + 1)`, the universe of the objects of
the small étale site.  A morphism of small étale ringed topoi has its direct image at `Type u`,
the universe of the sections of the structure sheaf, so that declaration cannot be used here;
the comparison is re-formed at `Type u` from the same site-level input.

## References

* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 021J](https://stacks.math.columbia.edu/tag/021J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X Y Z : B.Scheme) (a : X ⟶ Y) (q : Y ⟶ Z)

/-- **The geometric content of the composition of structure maps.**  The comparison of iterated
small étale base change with base change along the composite carries the projection
`X ×_Z W ⟶ W` to the composite of the two projections `X ×_Y (Y ×_Z W) ⟶ Y ×_Z W ⟶ W`.

This is `CategoryTheory.Over.pullbackComp_inv_app_left_fst` transported to the small étale
category along `AlgebraicGeometry.smallEtaleBaseChange_compIso_app`. -/
theorem toScheme_map_smallEtaleBaseChange_compIso_hom_app_comp
    (W : SmallEtale B Z.obj Z.property) :
    (SmallEtale.toScheme B X.obj X.property).map
          ((smallEtaleBaseChange_compIso B X Y Z a q).val.hom.app W) ≫
        B.inclusion.map (pullback.fst W.obj.hom (a ≫ q)) =
      B.inclusion.map (pullback.fst ((smallEtaleBaseChange B q).obj W).obj.hom a) ≫
        B.inclusion.map (pullback.fst W.obj.hom q) := by
  have hleft : (SmallEtale.toScheme B X.obj X.property).map
      ((smallEtaleBaseChange_compIso B X Y Z a q).val.hom.app W) =
      B.inclusion.map ((Over.pullbackComp a q).inv.app W.obj).left := by
    rw [← smallEtaleBaseChange_compIso_app B X Y Z a q W]
    rfl
  rw [hleft]
  erw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg B.inclusion.map (Over.pullbackComp_inv_app_left_fst a q W.obj)

/-- The comparison of the composite of the two small étale direct images with the direct image
of the composite, for sheaves of sets at the universe of the sections of the structure sheaves.

This is `AlgebraicGeometry.smallEtaleMorphism_comp_pushforwardIso` at `Type u` rather than at
`Type (u + 1)`: it is the direct image comparison a morphism of small étale *ringed* topoi
needs, since the structure sheaf has sections in `Type u`. -/
def smallEtaleRingedToposHomCompPushforwardIso :
    (smallEtaleBaseChange B a).sheafPushforwardContinuous (Type u)
        (SmallEtale.topology B Y.obj Y.property)
        (SmallEtale.topology B X.obj X.property) ⋙
      (smallEtaleBaseChange B q).sheafPushforwardContinuous (Type u)
        (SmallEtale.topology B Z.obj Z.property)
        (SmallEtale.topology B Y.obj Y.property) ≅
    (smallEtaleBaseChange B (a ≫ q)).sheafPushforwardContinuous (Type u)
      (SmallEtale.topology B Z.obj Z.property)
      (SmallEtale.topology B X.obj X.property) :=
  Functor.sheafPushforwardContinuousComp'
    (smallEtaleBaseChange_compIso B X Y Z a q).val
    (Type u) (SmallEtale.topology B Z.obj Z.property)
    (SmallEtale.topology B Y.obj Y.property)
    (SmallEtale.topology B X.obj X.property)

/-- The inverse of the direct image comparison, on sections: it restricts a section along the
comparison of the two base changes. -/
theorem smallEtaleRingedToposHomCompPushforwardIso_inv_app_hom_app
    (M : Sheaf (SmallEtale.topology B X.obj X.property) (Type u))
    (W : SmallEtale B Z.obj Z.property) :
    ((smallEtaleRingedToposHomCompPushforwardIso B X Y Z a q).inv.app M).hom.app (op W) =
      M.obj.map ((smallEtaleBaseChange_compIso B X Y Z a q).val.hom.app W).op :=
  rfl

attribute [local implicit_reducible] AlgebraicGeometry.RingedToposHom.comp MorphismOfTopoi.comp

/-- **Stacks 070R part (2), the composition law as a 2-isomorphism.**  The morphism of small
étale ringed topoi of a composite `a ≫ q` of morphisms of schemes is 2-isomorphic to the
composite of the morphisms of small étale ringed topoi of `a` and of `q`. -/
def smallEtaleRingedToposHomCompTwoIso :
    RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u}
      (smallEtaleRingedToposHom B (a ≫ q))
      (RingedToposHom.comp.{u, u + 1, u, u, u + 1, u, u, u + 1, u}
        (smallEtaleRingedToposHom B q) (smallEtaleRingedToposHom B a)) where
  e := (smallEtaleRingedToposHomCompPushforwardIso B X Y Z a q).symm
  commutes := by
    refine Sheaf.hom_ext (NatTrans.ext (funext fun W ↦ ?_))
    obtain ⟨W⟩ := W
    have hRHS := congrArg (fun m ↦ m.hom.app (Opposite.op W))
      (RingedToposHom.forgetFSharp_comp (smallEtaleRingedToposHom B q)
        (smallEtaleRingedToposHom B a))
    refine Eq.trans ?_ hRHS.symm
    exact (CategoryTheory.Functor.map_comp (Scheme.Γ ⋙ forget CommRingCat.{u})
          (Opposite.op (B.inclusion.map (pullback.fst W.obj.hom (a ≫ q))))
          (Opposite.op ((SmallEtale.toScheme B X.obj X.property).map
            ((smallEtaleBaseChange_compIso B X Y Z a q).val.hom.app W)))).symm.trans
      ((congrArg (fun m ↦ (Scheme.Γ ⋙ forget CommRingCat.{u}).map (Opposite.op m))
            (toScheme_map_smallEtaleBaseChange_compIso_hom_app_comp B X Y Z a q W)).trans
        (CategoryTheory.Functor.map_comp (Scheme.Γ ⋙ forget CommRingCat.{u})
          (Opposite.op (B.inclusion.map (pullback.fst W.obj.hom q)))
          (Opposite.op (B.inclusion.map
            (pullback.fst ((smallEtaleBaseChange B q).obj W).obj.hom a)))))

end AlgebraicGeometry

end
