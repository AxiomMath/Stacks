module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.MorphismComposition
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleProjection
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallToBigTopos
public import StacksFrontier.CategoryTheory.Sites.PullbackSectionsComparison

/-!
# Sections of a sheaf pulled back from the small étale site

Let `S` be a scheme in a big étale site and let `π_S` be the projection from the big étale
topos over `S` to the small étale topos of `S`. For a sheaf `F` on the small étale site of `S`
and a scheme `f : X ⟶ S` over `S`, the value of `π_S⁻¹F` at `X` is the global sections on the
small étale site of `X` of the small-site pullback `f⁻¹F`, naturally in `F` and compatibly with
restriction along any morphism of schemes over `S`.

## Main definitions

* `AlgebraicGeometry.etalePullbackSectionsRestriction` — the canonical restriction map between
  the global sections of two small-site pullbacks along `Y ⟶ X` over `S`.
* `AlgebraicGeometry.etaleInverseImageSectionsIso` — the formula for the sections of `π_S⁻¹F`.

## Main results

* `AlgebraicGeometry.etaleInverseImageSectionsComparison` — the whole family of section
  comparisons, together with its compatibility with the canonical restriction maps.
* `AlgebraicGeometry.etaleInverseImageSectionsIso_naturality` — restriction along a morphism of
  schemes over `S` agrees with the canonical map of global sections of the small-site
  pullbacks.

## Implementation notes

The comparison comes from `CategoryTheory.sheafPullbackIsoOfInitial`, applied to the
factorization of the small-site base-change functor `f_small` through the functor `i_f` from
the small étale site of `X` to the big étale slice of `S`. The hypothesis that the comparison
arrows are initial among structured arrows is the universal property of the fibre product, here
`AlgebraicGeometry.etaleCounitInitial`.

The family of comparisons and its compatibility with restriction are produced together, as the
two components of one subtype: the comparisons are built from an isomorphism of left adjoints,
so no individual comparison is canonical on the nose, while the family is.

## References

* [Stacks Project, Tag 09XN](https://stacks.math.columbia.edu/tag/09XN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Small étale base change along `f` carries the final object `Y / Y` to a final object. -/
public def smallEtaleBaseChange_finalIsTerminal (B : BigEtaleSite.{u}) {X Y : B.Scheme}
    (f : X ⟶ Y) :
    IsTerminal ((smallEtaleBaseChange B f).obj (SmallEtale.final B Y.obj Y.property)) :=
  IsTerminal.isTerminalOfObj (SmallEtale.inclusion B X.obj X.property) _
    ((Over.mkIdTerminal : IsTerminal (Over.mk (𝟙 Y))).isTerminalObj (Over.pullback f) _)

/-- Restrict global sections of a small étale pullback along `Y ⟶ X` over `S`, using the
adjunction unit and the canonical composition of base changes. -/
public def etalePullbackSectionsRestriction (B : BigEtaleSite.{u}) (S : B.Scheme)
    {X Y : BigEtaleOver B S.obj S.property} (g : Y ⟶ X)
    (F : Sheaf (SmallEtale.topology B S.obj S.property) (Type (u + 1))) :
    (Sheaf.Γ (SmallEtale.topology B X.left.obj X.left.property) (Type (u + 1))).obj
      (((smallEtaleBaseChange B X.hom).sheafPullback (Type (u + 1))
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B X.left.obj X.left.property)).obj F) ⟶
    (Sheaf.Γ (SmallEtale.topology B Y.left.obj Y.left.property) (Type (u + 1))).obj
      (((smallEtaleBaseChange B Y.hom).sheafPullback (Type (u + 1))
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B Y.left.obj Y.left.property)).obj F) :=
  sheafPullbackSectionsRestriction
    (SmallEtale.topology B S.obj S.property)
    (SmallEtale.topology B X.left.obj X.left.property)
    (SmallEtale.topology B Y.left.obj Y.left.property)
    (smallEtaleBaseChange B X.hom) (smallEtaleBaseChange B g.left)
    (smallEtaleBaseChange B Y.hom)
    ((smallEtaleBaseChange_compIso B Y.left X.left S g.left X.hom).val ≪≫
      eqToIso (congrArg (smallEtaleBaseChange B) (Over.w g)))
    (SmallEtale.finalIsTerminal B X.left.obj X.left.property)
    (smallEtaleBaseChange_finalIsTerminal B g.left) F

section Geometry

variable (B : BigEtaleSite.{u}) {S T : B.Scheme} (f : T ⟶ S)

/-- The counit comparing an étale scheme `U` over `S` with the image under `i_f` of its base
change along `f : T ⟶ S`. -/
public def etaleCounit :
    smallEtaleBaseChange B f ⋙ smallEtaleToBigEtaleFunctor B T S f ⟶
      SmallEtale.inclusion B S.obj S.property where
  app U := (Over.mapPullbackAdj f).counit.app U.obj
  naturality {_U _V} g := (Over.mapPullbackAdj f).counit.naturality g.hom

/-- Each component of `AlgebraicGeometry.etaleCounit` is initial among the structured arrows
over `i_f`: that is the universal property of the fibre product. -/
public def etaleCounitInitial (U : SmallEtale B S.obj S.property) :
    IsInitial (StructuredArrow.mk
      (T := (smallEtaleToBigEtaleFunctor B T S f).op)
      ((etaleCounit B f).app U).op) := by
  let j := SmallEtale.inclusion B T.obj T.property
  let a := Over.mapPullbackAdj f
  let lift (k : StructuredArrow (Opposite.op U.obj)
      (smallEtaleToBigEtaleFunctor B T S f).op) :
      k.right.unop ⟶ (smallEtaleBaseChange B f).obj U :=
    j.preimage (a.homEquiv (j.obj k.right.unop) U.obj k.hom.unop)
  have hlift (k : StructuredArrow (Opposite.op U.obj) (smallEtaleToBigEtaleFunctor B T S f).op) :
      (a.homEquiv (j.obj k.right.unop) U.obj).symm (j.map (lift k)) = k.hom.unop :=
    (congrArg (a.homEquiv (j.obj k.right.unop) U.obj).symm (j.map_preimage _)).trans
      ((a.homEquiv (j.obj k.right.unop) U.obj).symm_apply_apply _)
  refine IsInitial.ofUniqueHom (fun k => StructuredArrow.homMk (lift k).op ?_) ?_
  · apply Quiver.Hom.unop_inj
    change (Over.map f).map (j.map (lift k)) ≫ a.counit.app U.obj = k.hom.unop
    exact (a.homEquiv_counit _ _ _).symm.trans (hlift k)
  · intro k m
    apply StructuredArrow.hom_ext
    apply Quiver.Hom.unop_inj
    apply j.map_injective
    apply (a.homEquiv (j.obj k.right.unop) U.obj).symm.injective
    have hm : (Over.map f).map (j.map m.right.unop) ≫ a.counit.app U.obj = k.hom.unop :=
      congrArg Quiver.Hom.unop (StructuredArrow.w m)
    change (a.homEquiv _ _).symm (j.map m.right.unop) =
      (a.homEquiv _ _).symm (j.map (lift k))
    exact ((a.homEquiv_counit (j.obj k.right.unop) U.obj (j.map m.right.unop)).trans hm).trans
      (hlift k).symm

/-- The transition comparing the two functors to the big étale slice of `S` attached to a
factorization `h = g ≫ f` of a morphism of `B`. -/
public def etaleTransition {R : B.Scheme} (g : R ⟶ T) (h : R ⟶ S) (w : g ≫ f = h) :
    smallEtaleBaseChange B g ⋙ smallEtaleToBigEtaleFunctor B R S h ⟶
      smallEtaleToBigEtaleFunctor B T S f where
  app V := Over.homMk ((etaleCounit B g).app V).left (by
    have hv := congrArg (fun z => z ≫ f) (Over.w ((etaleCounit B g).app V))
    change ((etaleCounit B g).app V).left ≫ V.obj.hom ≫ f =
      ((smallEtaleBaseChange B g).obj V).obj.hom ≫ h
    change (((etaleCounit B g).app V).left ≫ V.obj.hom) ≫ f =
      (((smallEtaleBaseChange B g).obj V).obj.hom ≫ g) ≫ f at hv
    simpa only [Category.assoc, w] using hv)
  naturality {_U _V} k :=
    Over.OverMorphism.ext (congrArg (fun z => z.left) ((etaleCounit B g).naturality k))

/-- `AlgebraicGeometry.etaleTransition` is compatible with the counits and with the composition
comparison of base changes. -/
public lemma etaleCounit_comp {R : B.Scheme} (g : R ⟶ T) (h : R ⟶ S) (w : g ≫ f = h)
    (U : SmallEtale B S.obj S.property) :
    (etaleTransition B f g h w).app ((smallEtaleBaseChange B f).obj U) ≫
        (etaleCounit B f).app U =
      (smallEtaleToBigEtaleFunctor B R S h).map
        (((smallEtaleBaseChange_compIso B R T S g f).val ≪≫
          eqToIso (congrArg (smallEtaleBaseChange B) w)).hom.app U) ≫
          (etaleCounit B h).app U := by
  subst h
  apply Over.OverMorphism.ext
  change pullback.fst (pullback.snd U.obj.hom f) g ≫ pullback.fst U.obj.hom f =
    ((SmallEtale.inclusion B R.obj R.property).map
      (((smallEtaleBaseChange_compIso B R T S g f).val ≪≫
        eqToIso (congrArg (smallEtaleBaseChange B) rfl)).hom.app U)).left ≫
      pullback.fst U.obj.hom (g ≫ f)
  simp only [eqToIso_refl, Iso.trans_refl]
  rw [smallEtaleBaseChange_compIso_app B R T S g f U]
  exact (Over.pullbackComp_inv_app_left_fst g f U.obj).symm

end Geometry

/-- The transition at the final object recovers the structure morphism `g : Y ⟶ X` of the big
étale slice of `S`. -/
public lemma etaleTransition_final (B : BigEtaleSite.{u}) (S : B.Scheme)
    {X Y : BigEtaleOver B S.obj S.property} (g : Y ⟶ X) :
    (smallEtaleToBigEtaleFunctor B Y.left S Y.hom).map
        ((smallEtaleBaseChange_finalIsTerminal B g.left).from
          (SmallEtale.final B Y.left.obj Y.left.property)) ≫
      (etaleTransition B X.hom g.left Y.hom (Over.w g)).app
        (SmallEtale.final B X.left.obj X.left.property) = g := by
  apply Over.OverMorphism.ext
  let U := SmallEtale.final B X.left.obj X.left.property
  let k := (smallEtaleBaseChange_finalIsTerminal B g.left).from
    (SmallEtale.final B Y.left.obj Y.left.property)
  have hv := Over.w ((etaleCounit B g.left).app U)
  have hk := Over.w k.hom
  change ((etaleCounit B g.left).app U).left ≫ 𝟙 X.left =
    ((smallEtaleBaseChange B g.left).obj U).obj.hom ≫ g.left at hv
  change k.hom.left ≫ ((smallEtaleBaseChange B g.left).obj U).obj.hom = 𝟙 Y.left at hk
  change k.hom.left ≫ ((etaleCounit B g.left).app U).left = g.left
  have hv' : ((etaleCounit B g.left).app U).left =
      ((smallEtaleBaseChange B g.left).obj U).obj.hom ≫ g.left :=
    (Category.comp_id _).symm.trans hv
  rw [hv']
  exact (Category.assoc _ _ _).symm.trans
    ((CategoryTheory.eq_whisker hk _).trans (Category.id_comp _))

/-- The small étale pullback along `f : X ⟶ S` is the inverse image along `π_S` followed by the
direct image along `i_f`. -/
public def etaleSmallPullbackIso (B : BigEtaleSite.{u}) (S : B.Scheme)
    (X : BigEtaleOver B S.obj S.property) :
    (smallEtaleBaseChange B X.hom).sheafPullback (Type (u + 1))
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B X.left.obj X.left.property) ≅
      (bigEtaleToSmallEtaleMorphism B S.obj S.property).inverseImage ⋙
        (smallEtaleToBigEtaleFunctor B X.left S X.hom).sheafPushforwardContinuous
          (Type (u + 1)) (SmallEtale.topology B X.left.obj X.left.property)
          (BigEtaleOver.topology B S.obj S.property) :=
  sheafPullbackIsoOfInitial
    (SmallEtale.topology B S.obj S.property)
    (SmallEtale.topology B X.left.obj X.left.property)
    (BigEtaleOver.topology B S.obj S.property)
    (smallEtaleBaseChange B X.hom)
    (smallEtaleToBigEtaleFunctor B X.left S X.hom)
    (SmallEtale.inclusion B S.obj S.property)
    (etaleCounit B X.hom)
    (bigEtaleToSmallEtaleMorphism B S.obj S.property).inverseImage
    (bigEtaleToSmallEtaleMorphism B S.obj S.property).adj
    (etaleCounitInitial B X.hom)

/-- The canonical comparison of the sections of `π_S⁻¹F` at `X` with the global sections of the
small-site pullback of `F` to `X`. -/
public def etaleInverseImageSectionsComparisonAt (B : BigEtaleSite.{u}) (S : B.Scheme)
    (X : BigEtaleOver B S.obj S.property) :
    (bigEtaleToSmallEtaleMorphism B S.obj S.property).inverseImage ⋙
      (sheafSections (BigEtaleOver.topology B S.obj S.property)
        (Type (u + 1))).obj (Opposite.op X) ≅
    (smallEtaleBaseChange B X.hom).sheafPullback
        (Type (u + 1))
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B X.left.obj X.left.property) ⋙
      Sheaf.Γ (SmallEtale.topology B X.left.obj X.left.property)
        (Type (u + 1)) :=
  sheafPullbackSectionsIso
    (SmallEtale.topology B S.obj S.property)
    (SmallEtale.topology B X.left.obj X.left.property)
    (BigEtaleOver.topology B S.obj S.property)
    (smallEtaleToBigEtaleFunctor B X.left S X.hom)
    (bigEtaleToSmallEtaleMorphism B S.obj S.property).inverseImage _
    (etaleSmallPullbackIso B S X)
    (SmallEtale.finalIsTerminal B X.left.obj X.left.property)

/-- The section comparisons for all schemes over `S`, compatible with the canonical
small-pullback restriction maps. The family and the compatibility are chosen together. -/
@[stacks 09XN "pullback_formula"]
public noncomputable def etaleInverseImageSectionsComparison
    (B : BigEtaleSite.{u}) (S : B.Scheme) :
    { e : ∀ X : BigEtaleOver B S.obj S.property,
        (bigEtaleToSmallEtaleMorphism B S.obj S.property).inverseImage ⋙
          (sheafSections (BigEtaleOver.topology B S.obj S.property)
            (Type (u + 1))).obj (Opposite.op X) ≅
        (smallEtaleBaseChange B X.hom).sheafPullback
            (Type (u + 1))
            (SmallEtale.topology B S.obj S.property)
            (SmallEtale.topology B X.left.obj X.left.property) ⋙
          Sheaf.Γ (SmallEtale.topology B X.left.obj X.left.property)
            (Type (u + 1)) //
      ∀ {X Y : BigEtaleOver B S.obj S.property} (g : Y ⟶ X)
        (F : Sheaf (SmallEtale.topology B S.obj S.property) (Type (u + 1))),
        (e X).hom.app F ≫ etalePullbackSectionsRestriction B S g F =
          ((bigEtaleToSmallEtaleMorphism B S.obj S.property).inverseImage.obj F).obj.map g.op ≫
            (e Y).hom.app F } := by
  refine ⟨etaleInverseImageSectionsComparisonAt B S, fun {X Y} g F => ?_⟩
  refine sheafPullbackSectionsIso_restriction
    (SmallEtale.topology B S.obj S.property)
    (SmallEtale.topology B X.left.obj X.left.property)
    (SmallEtale.topology B Y.left.obj Y.left.property)
    (BigEtaleOver.topology B S.obj S.property)
    (smallEtaleBaseChange B X.hom) (smallEtaleBaseChange B g.left)
    (smallEtaleBaseChange B Y.hom)
    (smallEtaleToBigEtaleFunctor B X.left S X.hom)
    (smallEtaleToBigEtaleFunctor B Y.left S Y.hom)
    (bigEtaleToSmallEtaleMorphism B S.obj S.property).inverseImage
    (etaleSmallPullbackIso B S X) (etaleSmallPullbackIso B S Y)
    ((smallEtaleBaseChange_compIso B Y.left X.left S g.left X.hom).val ≪≫
      eqToIso (congrArg (smallEtaleBaseChange B) (Over.w g)))
    (etaleTransition B X.hom g.left Y.hom (Over.w g))
    (SmallEtale.finalIsTerminal B X.left.obj X.left.property)
    (smallEtaleBaseChange_finalIsTerminal B g.left)
    (SmallEtale.finalIsTerminal B Y.left.obj Y.left.property) g
    (etaleTransition_final B S g) F ?_
  exact sheafPullbackRestriction_comp
    (SmallEtale.topology B S.obj S.property)
    (SmallEtale.topology B X.left.obj X.left.property)
    (SmallEtale.topology B Y.left.obj Y.left.property)
    (BigEtaleOver.topology B S.obj S.property)
    (smallEtaleBaseChange B X.hom) (smallEtaleBaseChange B g.left)
    (smallEtaleBaseChange B Y.hom)
    (smallEtaleToBigEtaleFunctor B X.left S X.hom)
    (smallEtaleToBigEtaleFunctor B Y.left S Y.hom)
    (SmallEtale.inclusion B S.obj S.property)
    (bigEtaleToSmallEtaleMorphism B S.obj S.property).inverseImage
    (bigEtaleToSmallEtaleMorphism B S.obj S.property).adj.unit
    (etaleCounit B X.hom) (etaleCounit B Y.hom)
    (etaleSmallPullbackIso B S X).hom (etaleSmallPullbackIso B S Y).hom
    (sheafPullbackIsoOfInitial_unit
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B X.left.obj X.left.property)
      (BigEtaleOver.topology B S.obj S.property)
      (smallEtaleBaseChange B X.hom)
      (smallEtaleToBigEtaleFunctor B X.left S X.hom)
      (SmallEtale.inclusion B S.obj S.property)
      (etaleCounit B X.hom)
      (bigEtaleToSmallEtaleMorphism B S.obj S.property).inverseImage
      (bigEtaleToSmallEtaleMorphism B S.obj S.property).adj
      (etaleCounitInitial B X.hom))
    (sheafPullbackIsoOfInitial_unit
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B Y.left.obj Y.left.property)
      (BigEtaleOver.topology B S.obj S.property)
      (smallEtaleBaseChange B Y.hom)
      (smallEtaleToBigEtaleFunctor B Y.left S Y.hom)
      (SmallEtale.inclusion B S.obj S.property)
      (etaleCounit B Y.hom)
      (bigEtaleToSmallEtaleMorphism B S.obj S.property).inverseImage
      (bigEtaleToSmallEtaleMorphism B S.obj S.property).adj
      (etaleCounitInitial B Y.hom))
    ((smallEtaleBaseChange_compIso B Y.left X.left S g.left X.hom).val ≪≫
      eqToIso (congrArg (smallEtaleBaseChange B) (Over.w g)))
    (etaleTransition B X.hom g.left Y.hom (Over.w g))
    (etaleCounit_comp B X.hom g.left Y.hom (Over.w g)) F

/-- **Stacks 09XN, pullback formula (étale case).** For a sheaf `F` on the small étale site of
`S` and a scheme `f : X ⟶ S` over `S`, the sections of `π_S⁻¹F` at `X` are the global sections
of the small étale pullback `f⁻¹F`, naturally in `F`. Restriction in `X` is recorded by
`AlgebraicGeometry.etaleInverseImageSectionsIso_naturality`. -/
@[stacks 09XN "pullback_formula"]
public noncomputable def etaleInverseImageSectionsIso
    (B : BigEtaleSite.{u}) (S : B.Scheme) (X : BigEtaleOver B S.obj S.property) :
    (bigEtaleToSmallEtaleMorphism B S.obj S.property).inverseImage ⋙
      (sheafSections (BigEtaleOver.topology B S.obj S.property)
        (Type (u + 1))).obj (Opposite.op X) ≅
    (smallEtaleBaseChange B X.hom).sheafPullback
        (Type (u + 1))
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B X.left.obj X.left.property) ⋙
      Sheaf.Γ (SmallEtale.topology B X.left.obj X.left.property)
        (Type (u + 1)) :=
  (etaleInverseImageSectionsComparison B S).val X

/-- Restriction along any morphism of schemes over `S` agrees with the canonical map on global
sections of the small étale pullbacks. -/
public theorem etaleInverseImageSectionsIso_naturality
    (B : BigEtaleSite.{u}) (S : B.Scheme)
    {X Y : BigEtaleOver B S.obj S.property} (g : Y ⟶ X)
    (F : Sheaf (SmallEtale.topology B S.obj S.property) (Type (u + 1))) :
    (etaleInverseImageSectionsIso B S X).hom.app F ≫
        etalePullbackSectionsRestriction B S g F =
      ((bigEtaleToSmallEtaleMorphism B S.obj S.property).inverseImage.obj F).obj.map g.op ≫
        (etaleInverseImageSectionsIso B S Y).hom.app F :=
  (etaleInverseImageSectionsComparison B S).property g F

end AlgebraicGeometry
