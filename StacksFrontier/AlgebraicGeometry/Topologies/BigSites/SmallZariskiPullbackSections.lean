module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.SmallZariskiProjection
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.ZariskiLimits
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.ZariskiFactorization
public import StacksFrontier.CategoryTheory.Sites.PullbackSectionsComparison

/-!
# Sections of a sheaf pulled back from the small Zariski site

Let `S` be a scheme in a big Zariski site and let `π_S` be the projection from the big Zariski
topos over `S` to the small Zariski topos of `S`. For a sheaf `F` on the small Zariski site of
`S` and a scheme `f : X ⟶ S` over `S`, the value of `π_S⁻¹F` at `X` is the global sections on
the small Zariski site of `X` of the small-site pullback `f⁻¹F`, naturally in `F` and
compatibly with restriction along any morphism of schemes over `S`.

## Main definitions

* `AlgebraicGeometry.smallZariskiBaseChange_compIso` — the comparison of successive small
  Zariski base changes with base change along the composite.
* `AlgebraicGeometry.zariskiPullbackSectionsRestriction` — the canonical restriction map
  between the global sections of two small-site pullbacks along `Y ⟶ X` over `S`.
* `AlgebraicGeometry.zariskiInverseImageSectionsIso` — the formula for the sections of
  `π_S⁻¹F`.

## Main results

* `AlgebraicGeometry.zariskiInverseImageSectionsComparison` — the whole family of section
  comparisons, together with its compatibility with the canonical restriction maps.
* `AlgebraicGeometry.zariskiInverseImageSectionsIso_naturality` — restriction along a morphism
  of schemes over `S` agrees with the canonical map of global sections of the small-site
  pullbacks.

## Implementation notes

The comparison is obtained from
`CategoryTheory.sheafPullbackIsoOfInitial`, applied to the factorization of the small-site
base-change functor `f_small` through the functor `i_f` from the small Zariski site of `X` to
the big Zariski slice of `S`. The hypothesis that the comparison arrows are initial among
structured arrows is the universal property of the fibre product, here
`AlgebraicGeometry.zariskiCounitInitial`.

The family of comparisons and its compatibility with restriction are produced together, as the
two components of one subtype: the comparisons are built from an isomorphism of left adjoints,
so no individual comparison is canonical on the nose, while the family is.

The restriction maps on the right-hand side are the actual maps of global sections of the
small-site pullbacks — the mate of the adjunction unit, evaluated at the final object — and not
transported through the comparison isomorphisms.

## References

* [Stacks Project, Tag 09XN](https://stacks.math.columbia.edu/tag/09XN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The inclusion of the small Zariski site of `X` into the schemes over `X` is full. -/
public instance smallSiteInSchemesOver_full (B : BigZariskiSite.{u}) (X : B.Schemes) :
    (smallSiteInSchemesOver B X).Full := by
  let : (Over.post (X := X) B.inclusion).Full := inferInstance
  change (SmallZariski.inclusion B X.1 X.property ⋙ Over.post B.inclusion).Full
  infer_instance

/-- The inclusion of the small Zariski site of `X` into the schemes over `X` is faithful. -/
public instance smallSiteInSchemesOver_faithful (B : BigZariskiSite.{u}) (X : B.Schemes) :
    (smallSiteInSchemesOver B X).Faithful := by
  let : (Over.post (X := X) B.inclusion).Faithful := inferInstance
  change (SmallZariski.inclusion B X.1 X.property ⋙ Over.post B.inclusion).Faithful
  infer_instance

/-- The comparison of successive small Zariski base changes with base change along the
composite, induced by the canonical comparison of iterated fibre products. -/
public def smallZariskiBaseChange_compIso (B : BigZariskiSite.{u}) {X Y Z : B.Schemes}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    smallZariskiBaseChange B g ⋙ smallZariskiBaseChange B f ≅
      smallZariskiBaseChange B (f ≫ g) := by
  let a := smallZariskiBaseChange B g
  let b := smallZariskiBaseChange B f
  let q := Over.pullback (B.inclusion.map f)
  let e : (a ⋙ b) ⋙ smallSiteInSchemesOver B X ≅
      smallZariskiBaseChange B (f ≫ g) ⋙ smallSiteInSchemesOver B X :=
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft a (smallZariskiBaseChangeIso B f) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (smallZariskiBaseChangeIso B g) q ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (smallSiteInSchemesOver B Z)
      ((Over.pullbackComp (B.inclusion.map f) (B.inclusion.map g)).symm ≪≫
        eqToIso (by rw [Functor.map_comp])) ≪≫
    (smallZariskiBaseChangeIso B (f ≫ g)).symm
  exact Functor.fullyFaithfulCancelRight (smallSiteInSchemesOver B X) e

/-- Small Zariski base change along `f` carries the final object `Y / Y` to a final object. -/
public def smallZariskiBaseChange_finalIsTerminal (B : BigZariskiSite.{u}) {X Y : B.Schemes}
    (f : X ⟶ Y) :
    IsTerminal ((smallZariskiBaseChange B f).obj (SmallZariski.final B Y.1 Y.property)) := by
  apply IsTerminal.isTerminalOfObj (smallSiteInSchemesOver B X)
  have h : IsTerminal ((smallSiteInSchemesOver B Y).obj
      (SmallZariski.final B Y.1 Y.property)) := by
    change IsTerminal (Over.mk (𝟙 Y.1))
    exact Over.mkIdTerminal
  exact (h.isTerminalObj (Over.pullback (B.inclusion.map f)) _).ofIso
    ((smallZariskiBaseChangeIso B f).symm.app _)

/-- Restrict global sections of a small Zariski pullback along `Y ⟶ X` over `S`, using the
adjunction unit and the canonical composition of base changes. -/
public def zariskiPullbackSectionsRestriction (B : BigZariskiSite.{u}) (S : B.Schemes)
    {X Y : BigZariskiOver B S.1 S.property} (g : Y ⟶ X)
    (F : Sheaf (SmallZariski.topology B S.1 S.property) (Type (u + 1))) :
    (Sheaf.Γ (SmallZariski.topology B X.left.1 X.left.property) (Type (u + 1))).obj
      (((smallZariskiBaseChange B X.hom).sheafPullback (Type (u + 1))
        (SmallZariski.topology B S.1 S.property)
        (SmallZariski.topology B X.left.1 X.left.property)).obj F) ⟶
    (Sheaf.Γ (SmallZariski.topology B Y.left.1 Y.left.property) (Type (u + 1))).obj
      (((smallZariskiBaseChange B Y.hom).sheafPullback (Type (u + 1))
        (SmallZariski.topology B S.1 S.property)
        (SmallZariski.topology B Y.left.1 Y.left.property)).obj F) :=
  sheafPullbackSectionsRestriction
    (SmallZariski.topology B S.1 S.property)
    (SmallZariski.topology B X.left.1 X.left.property)
    (SmallZariski.topology B Y.left.1 Y.left.property)
    (smallZariskiBaseChange B X.hom) (smallZariskiBaseChange B g.left)
    (smallZariskiBaseChange B Y.hom)
    (smallZariskiBaseChange_compIso B g.left X.hom ≪≫
      eqToIso (congrArg (smallZariskiBaseChange B) (Over.w g)))
    (SmallZariski.finalIsTerminal B X.left.1 X.left.property)
    (smallZariskiBaseChange_finalIsTerminal B g.left) F

section Geometry

variable (B : BigZariskiSite.{u}) {S T : B.Schemes} (f : T ⟶ S)

/-- Any two morphisms from an object of the big Zariski slice of `S` to an open subscheme of
`S` agree, since the structure morphism of an open subscheme is a monomorphism. -/
public lemma zariskiOverHom_ext {X : BigZariskiOver B S.1 S.property}
    {U : SmallZariski B S.1 S.property} (p q : X ⟶ U.obj) : p = q := by
  apply (Over.post B.inclusion).map_injective
  apply Over.OverMorphism.ext
  have : IsOpenImmersion (B.inclusion.map U.obj.hom) := U.property
  apply (cancel_mono (B.inclusion.map U.obj.hom)).mp
  exact (Over.w ((Over.post B.inclusion).map p)).trans
    (Over.w ((Over.post B.inclusion).map q)).symm

/-- Any two morphisms of open subschemes of `S` agree. -/
public lemma zariskiSmallHom_ext {U V : SmallZariski B S.1 S.property} (p q : U ⟶ V) : p = q :=
  (SmallZariski.inclusion B S.1 S.property).map_injective (zariskiOverHom_ext B _ _)

/-- The counit comparing an open subscheme `U` of `S` with the image under `i_f` of its base
change along `f : T ⟶ S`. -/
public def zariskiCounit :
    smallZariskiBaseChange B f ⋙ smallZariskiToBigZariskiFunctor B T S f ⟶
      SmallZariski.inclusion B S.1 S.property where
  app U := (Over.post B.inclusion).preimage
    ((Over.map (B.inclusion.map f)).map ((smallZariskiBaseChangeIso B f).hom.app U) ≫
      (Over.mapPullbackAdj (B.inclusion.map f)).counit.app ((smallSiteInSchemesOver B S).obj U))
  naturality {_U _V} _k := zariskiOverHom_ext B _ _

/-- Each component of `AlgebraicGeometry.zariskiCounit` is initial among the structured arrows
over `i_f`: that is the universal property of the fibre product. -/
public def zariskiCounitInitial (U : SmallZariski B S.1 S.property) :
    IsInitial (StructuredArrow.mk
      (T := (smallZariskiToBigZariskiFunctor B T S f).op)
      ((zariskiCounit B f).app U).op) := by
  let j := smallSiteInSchemesOver B T
  let q := Over.post (X := S) B.inclusion
  let a := Over.mapPullbackAdj (B.inclusion.map f)
  let e := (smallZariskiBaseChangeIso B f).app U
  let lift (k : StructuredArrow (Opposite.op U.obj)
      (smallZariskiToBigZariskiFunctor B T S f).op) :
      k.right.unop ⟶ (smallZariskiBaseChange B f).obj U :=
    j.preimage (a.homEquiv (j.obj k.right.unop) (q.obj U.obj) (q.map k.hom.unop) ≫ e.inv)
  refine IsInitial.ofUniqueHom (fun k => StructuredArrow.homMk (lift k).op ?_) ?_
  · apply Quiver.Hom.unop_inj
    exact zariskiOverHom_ext B _ _
  · intro k m
    apply StructuredArrow.hom_ext
    apply Quiver.Hom.unop_inj
    exact zariskiSmallHom_ext B _ _

/-- The transition comparing the two functors to the big Zariski slice of `S` attached to a
factorization `h = g ≫ f` of a morphism of `B`. -/
public def zariskiTransition {R : B.Schemes} (g : R ⟶ T) (h : R ⟶ S) (w : g ≫ f = h) :
    smallZariskiBaseChange B g ⋙ smallZariskiToBigZariskiFunctor B R S h ⟶
      smallZariskiToBigZariskiFunctor B T S f where
  app V := Over.homMk ((zariskiCounit B g).app V).left (by
    have hv := congrArg (fun z => z ≫ f) (Over.w ((zariskiCounit B g).app V))
    change ((zariskiCounit B g).app V).left ≫ V.obj.hom ≫ f =
      ((smallZariskiBaseChange B g).obj V).obj.hom ≫ h
    change (((zariskiCounit B g).app V).left ≫ V.obj.hom) ≫ f =
      (((smallZariskiBaseChange B g).obj V).obj.hom ≫ g) ≫ f at hv
    simpa only [Category.assoc, w] using hv)
  naturality {_U _V} k :=
    Over.OverMorphism.ext (congrArg (·.left) ((zariskiCounit B g).naturality k))

/-- `AlgebraicGeometry.zariskiTransition` is compatible with the counits and with the
composition comparison of base changes. -/
public lemma zariskiCounit_comp {R : B.Schemes} (g : R ⟶ T) (h : R ⟶ S) (w : g ≫ f = h)
    (U : SmallZariski B S.1 S.property) :
    (zariskiTransition B f g h w).app ((smallZariskiBaseChange B f).obj U) ≫
        (zariskiCounit B f).app U =
      (smallZariskiToBigZariskiFunctor B R S h).map
        ((smallZariskiBaseChange_compIso B g f ≪≫
          eqToIso (congrArg (smallZariskiBaseChange B) w)).hom.app U) ≫
          (zariskiCounit B h).app U :=
  zariskiOverHom_ext B _ _

end Geometry

/-- The transition at the final object recovers the structure morphism `g : Y ⟶ X` of the big
Zariski slice of `S`. -/
public lemma zariskiTransition_final (B : BigZariskiSite.{u}) (S : B.Schemes)
    {X Y : BigZariskiOver B S.1 S.property} (g : Y ⟶ X) :
    (smallZariskiToBigZariskiFunctor B Y.left S Y.hom).map
        ((smallZariskiBaseChange_finalIsTerminal B g.left).from
          (SmallZariski.final B Y.left.1 Y.left.property)) ≫
      (zariskiTransition B X.hom g.left Y.hom (Over.w g)).app
        (SmallZariski.final B X.left.1 X.left.property) = g := by
  apply Over.OverMorphism.ext
  let U := SmallZariski.final B X.left.1 X.left.property
  let k := (smallZariskiBaseChange_finalIsTerminal B g.left).from
    (SmallZariski.final B Y.left.1 Y.left.property)
  have hv := Over.w ((zariskiCounit B g.left).app U)
  have hk := Over.w k.hom
  change ((zariskiCounit B g.left).app U).left ≫ 𝟙 X.left =
    ((smallZariskiBaseChange B g.left).obj U).obj.hom ≫ g.left at hv
  change k.hom.left ≫ ((smallZariskiBaseChange B g.left).obj U).obj.hom = 𝟙 Y.left at hk
  change k.hom.left ≫ ((zariskiCounit B g.left).app U).left = g.left
  have hv' : ((zariskiCounit B g.left).app U).left =
      ((smallZariskiBaseChange B g.left).obj U).obj.hom ≫ g.left :=
    (Category.comp_id _).symm.trans hv
  rw [hv']
  exact (Category.assoc _ _ _).symm.trans
    ((CategoryTheory.eq_whisker hk _).trans (Category.id_comp _))

/-- The small Zariski pullback along `f : X ⟶ S` is the inverse image along `π_S` followed by
the direct image along `i_f`. -/
public def zariskiSmallPullbackIso (B : BigZariskiSite.{u}) (S : B.Schemes)
    (X : BigZariskiOver B S.1 S.property) :
    (smallZariskiBaseChange B X.hom).sheafPullback (Type (u + 1))
        (SmallZariski.topology B S.1 S.property)
        (SmallZariski.topology B X.left.1 X.left.property) ≅
      (smallZariskiProjection B S).inverseImage ⋙
        (smallZariskiToBigZariskiFunctor B X.left S X.hom).sheafPushforwardContinuous
          (Type (u + 1)) (SmallZariski.topology B X.left.1 X.left.property)
          (BigZariskiOver.topology B S.1 S.property) :=
  sheafPullbackIsoOfInitial
    (SmallZariski.topology B S.1 S.property)
    (SmallZariski.topology B X.left.1 X.left.property)
    (BigZariskiOver.topology B S.1 S.property)
    (smallZariskiBaseChange B X.hom)
    (smallZariskiToBigZariskiFunctor B X.left S X.hom)
    (SmallZariski.inclusion B S.1 S.property)
    (zariskiCounit B X.hom) (smallZariskiProjection B S).inverseImage
    (smallZariskiProjection B S).adj (zariskiCounitInitial B X.hom)

/-- The canonical comparison of the sections of `π_S⁻¹F` at `X` with the global sections of the
small-site pullback of `F` to `X`. -/
public def zariskiInverseImageSectionsComparisonAt (B : BigZariskiSite.{u}) (S : B.Schemes)
    (X : BigZariskiOver B S.1 S.property) :
    (smallZariskiProjection B S).inverseImage ⋙
      (sheafSections (BigZariskiOver.topology B S.1 S.property)
        (Type (u + 1))).obj (Opposite.op X) ≅
    (smallZariskiBaseChange B X.hom).sheafPullback
        (Type (u + 1))
        (SmallZariski.topology B S.1 S.property)
        (SmallZariski.topology B X.left.1 X.left.property) ⋙
      Sheaf.Γ (SmallZariski.topology B X.left.1 X.left.property)
        (Type (u + 1)) :=
  sheafPullbackSectionsIso
    (SmallZariski.topology B S.1 S.property)
    (SmallZariski.topology B X.left.1 X.left.property)
    (BigZariskiOver.topology B S.1 S.property)
    (smallZariskiToBigZariskiFunctor B X.left S X.hom)
    (smallZariskiProjection B S).inverseImage _ (zariskiSmallPullbackIso B S X)
    (SmallZariski.finalIsTerminal B X.left.1 X.left.property)

/-- The section comparisons for all schemes over `S`, compatible with the canonical
small-pullback restriction maps. The family and the compatibility are chosen together. -/
@[stacks 09XN "pullback_formula"]
public noncomputable def zariskiInverseImageSectionsComparison
    (B : BigZariskiSite.{u}) (S : B.Schemes) :
    { e : ∀ X : BigZariskiOver B S.1 S.property,
        (smallZariskiProjection B S).inverseImage ⋙
          (sheafSections (BigZariskiOver.topology B S.1 S.property)
            (Type (u + 1))).obj (Opposite.op X) ≅
        (smallZariskiBaseChange B X.hom).sheafPullback
            (Type (u + 1))
            (SmallZariski.topology B S.1 S.property)
            (SmallZariski.topology B X.left.1 X.left.property) ⋙
          Sheaf.Γ (SmallZariski.topology B X.left.1 X.left.property)
            (Type (u + 1)) //
      ∀ {X Y : BigZariskiOver B S.1 S.property} (g : Y ⟶ X)
        (F : Sheaf (SmallZariski.topology B S.1 S.property) (Type (u + 1))),
        (e X).hom.app F ≫ zariskiPullbackSectionsRestriction B S g F =
          ((smallZariskiProjection B S).inverseImage.obj F).obj.map g.op ≫
            (e Y).hom.app F } := by
  refine ⟨zariskiInverseImageSectionsComparisonAt B S, ?_⟩
  intro X Y g F
  refine sheafPullbackSectionsIso_restriction
    (SmallZariski.topology B S.1 S.property)
    (SmallZariski.topology B X.left.1 X.left.property)
    (SmallZariski.topology B Y.left.1 Y.left.property)
    (BigZariskiOver.topology B S.1 S.property)
    (smallZariskiBaseChange B X.hom) (smallZariskiBaseChange B g.left)
    (smallZariskiBaseChange B Y.hom)
    (smallZariskiToBigZariskiFunctor B X.left S X.hom)
    (smallZariskiToBigZariskiFunctor B Y.left S Y.hom)
    (smallZariskiProjection B S).inverseImage
    (zariskiSmallPullbackIso B S X) (zariskiSmallPullbackIso B S Y)
    (smallZariskiBaseChange_compIso B g.left X.hom ≪≫
      eqToIso (congrArg (smallZariskiBaseChange B) (Over.w g)))
    (zariskiTransition B X.hom g.left Y.hom (Over.w g))
    (SmallZariski.finalIsTerminal B X.left.1 X.left.property)
    (smallZariskiBaseChange_finalIsTerminal B g.left)
    (SmallZariski.finalIsTerminal B Y.left.1 Y.left.property) g
    (zariskiTransition_final B S g) F ?_
  exact sheafPullbackRestriction_comp
    (SmallZariski.topology B S.1 S.property)
    (SmallZariski.topology B X.left.1 X.left.property)
    (SmallZariski.topology B Y.left.1 Y.left.property)
    (BigZariskiOver.topology B S.1 S.property)
    (smallZariskiBaseChange B X.hom) (smallZariskiBaseChange B g.left)
    (smallZariskiBaseChange B Y.hom)
    (smallZariskiToBigZariskiFunctor B X.left S X.hom)
    (smallZariskiToBigZariskiFunctor B Y.left S Y.hom)
    (SmallZariski.inclusion B S.1 S.property)
    (smallZariskiProjection B S).inverseImage (smallZariskiProjection B S).adj.unit
    (zariskiCounit B X.hom) (zariskiCounit B Y.hom)
    (zariskiSmallPullbackIso B S X).hom (zariskiSmallPullbackIso B S Y).hom
    (sheafPullbackIsoOfInitial_unit
      (SmallZariski.topology B S.1 S.property)
      (SmallZariski.topology B X.left.1 X.left.property)
      (BigZariskiOver.topology B S.1 S.property)
      (smallZariskiBaseChange B X.hom)
      (smallZariskiToBigZariskiFunctor B X.left S X.hom)
      (SmallZariski.inclusion B S.1 S.property)
      (zariskiCounit B X.hom) (smallZariskiProjection B S).inverseImage
      (smallZariskiProjection B S).adj (zariskiCounitInitial B X.hom))
    (sheafPullbackIsoOfInitial_unit
      (SmallZariski.topology B S.1 S.property)
      (SmallZariski.topology B Y.left.1 Y.left.property)
      (BigZariskiOver.topology B S.1 S.property)
      (smallZariskiBaseChange B Y.hom)
      (smallZariskiToBigZariskiFunctor B Y.left S Y.hom)
      (SmallZariski.inclusion B S.1 S.property)
      (zariskiCounit B Y.hom) (smallZariskiProjection B S).inverseImage
      (smallZariskiProjection B S).adj (zariskiCounitInitial B Y.hom))
    (smallZariskiBaseChange_compIso B g.left X.hom ≪≫
      eqToIso (congrArg (smallZariskiBaseChange B) (Over.w g)))
    (zariskiTransition B X.hom g.left Y.hom (Over.w g))
    (zariskiCounit_comp B X.hom g.left Y.hom (Over.w g)) F

/-- **Stacks 09XN, pullback formula (Zariski case).** For a sheaf `F` on the small Zariski site
of `S` and a scheme `f : X ⟶ S` over `S`, the sections of `π_S⁻¹F` at `X` are the global
sections of the small Zariski pullback `f⁻¹F`, naturally in `F`. Restriction in `X` is recorded
by `AlgebraicGeometry.zariskiInverseImageSectionsIso_naturality`. -/
@[stacks 09XN "pullback_formula"]
public noncomputable def zariskiInverseImageSectionsIso
    (B : BigZariskiSite.{u}) (S : B.Schemes) (X : BigZariskiOver B S.1 S.property) :
    (smallZariskiProjection B S).inverseImage ⋙
      (sheafSections (BigZariskiOver.topology B S.1 S.property)
        (Type (u + 1))).obj (Opposite.op X) ≅
    (smallZariskiBaseChange B X.hom).sheafPullback
        (Type (u + 1))
        (SmallZariski.topology B S.1 S.property)
        (SmallZariski.topology B X.left.1 X.left.property) ⋙
      Sheaf.Γ (SmallZariski.topology B X.left.1 X.left.property)
        (Type (u + 1)) :=
  (zariskiInverseImageSectionsComparison B S).val X

/-- Restriction along any morphism of schemes over `S` agrees with the canonical map on global
sections of the small Zariski pullbacks. -/
public theorem zariskiInverseImageSectionsIso_naturality
    (B : BigZariskiSite.{u}) (S : B.Schemes)
    {X Y : BigZariskiOver B S.1 S.property} (g : Y ⟶ X)
    (F : Sheaf (SmallZariski.topology B S.1 S.property) (Type (u + 1))) :
    (zariskiInverseImageSectionsIso B S X).hom.app F ≫
        zariskiPullbackSectionsRestriction B S g F =
      ((smallZariskiProjection B S).inverseImage.obj F).obj.map g.op ≫
        (zariskiInverseImageSectionsIso B S Y).hom.app F :=
  (zariskiInverseImageSectionsComparison B S).property g F

end AlgebraicGeometry
