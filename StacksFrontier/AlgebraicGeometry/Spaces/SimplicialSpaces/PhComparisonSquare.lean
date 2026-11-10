module

public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.PhComparisonFunctor
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentPushforwardSections

/-!
# The ph comparison square of a simplicial algebraic space

Let `a : U → X` be an augmented simplicial algebraic space over a scheme `S`. Tag 0DHJ states
that the diagram of topoi
```
Sh((Spaces/U)_{ph, total}) --h--> Sh(U_étale)
        | a_ph                       | a
Sh((Spaces/X)_ph)        --h₋₁--> Sh(X_étale)
```
commutes, where `a_ph` is the augmentation of Section 09X8, `a` the augmentation of Section 0DE7,
and `h`, `h₋₁` are given by the inclusions `V/U_n ↦ V/U_n` and `W ↦ W/X` of objects étale over
`U_n`, respectively `X`.

On direct images: for a sheaf `F` on `(Spaces/U)_{ph, total}` and `W` étale over `X`, the
sections of `h₋₁,* a_{ph,*} F` over `W` are the sections of `F` over the system of all `V/U_n`
with a morphism `V → W` over `X`, and every such `V/U_n` maps uniquely to `W ×_X U_n` over `U_n`.
Hence these sections are the compatible families of sections of `F` over the base changes
`W ×_X U_n`, which are the sections over `W` of `a_* h_* F`, the limit of the cosimplicial system
of the direct images along the augmentations of the degrees.

## Main definitions

* `AlgebraicGeometry.Space.phBaseObj`: the object `W ×_X U_n` of `(Spaces/U)_{ph, total}`.
* `AlgebraicGeometry.Space.phCone`: the cone with vertex `h₋₁,* a_{ph,*} F` over the cosimplicial
  sheaf whose limit is `a_* h_* F`.
* `AlgebraicGeometry.Space.phComparisonSquarePushforwardIso`,
  `AlgebraicGeometry.Space.phComparisonSquareInverseImageIso`: the square, for a topology on
  algebraic spaces whose localizations receive the spaces-étale sites continuously.
* `AlgebraicGeometry.BigPHSpaceSite.phEtaleComparisonSquarePushforwardIso`,
  `AlgebraicGeometry.BigPHSpaceSite.phEtaleComparisonSquareInverseImageIso`: Tag 0DHJ, the
  square for the ph topology.

## Main results

* `AlgebraicGeometry.Space.transition_app_eq`: the cosimplicial structure of the direct images
  along the augmentations of the degrees of `U_étale` acts on sections over `W` as restriction
  along the cartesian arrows `W ×_X U_n → W ×_X U_m`.
* `AlgebraicGeometry.Space.phSections_existsUnique`: the sections of the right Kan extension
  along `V/U_n ↦ V/X` over `W` are the compatible families of sections over the `W ×_X U_n`.
* `AlgebraicGeometry.Space.phConeIsLimit`: the cone is a limit cone.

## Implementation notes

The source deduces the lemma from the general comparison of Tag 0D99 for a morphism of simplicial
sites compatible with augmentations. Here the comparison of the direct images is computed
directly: the direct image along the augmentation of `(Spaces/U)_{ph, total}` is the right Kan
extension along `V/U_n ↦ V/X` (Tag 09WL), and the direct image along the augmentation of
`U_étale` is a limit over the simplex category (Tag 0D70); the two are identified through the
universal property of that limit. The inverse-image square is the conjugate of the direct-image
square. The construction works for every topology `J` on algebraic spaces over `S` for which the
inclusions `X_{spaces, étale} → Spaces/X` are continuous for the localizations of `J`; the ph
topology is such a topology.

## References

* [Stacks Project, Tag 0DHJ](https://stacks.math.columbia.edu/tag/0DHJ)
* [Stacks Project, Section 09X8](https://stacks.math.columbia.edu/tag/09X8)
* [Stacks Project, Section 0DE7](https://stacks.math.columbia.edu/tag/0DE7)
* [Stacks Project, Tag 0D70](https://stacks.math.columbia.edu/tag/0D70)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (A : SimplicialObject.Augmented (AlgebraicSpaces B S hS))

open EtaleComponent SimplicialSiteSituation.Augmentation

/-- The object of the total site of `U_{spaces, étale}` in degree `n` given by an object `W`
étale over `X`: its base change `W ×_X U_n`. -/
abbrev etaleBaseObj (n : SimplexCategory) (W : SpacesEtale B S hS A.right) : EtaleTotal A :=
  ⟨op n, (Sum.inl W : Index A n)⟩

variable {A}

/-- The transitions of the cosimplicial system of direct images along the augmentations of the
degrees of `U_étale` act on sections over `W` as restriction along the cartesian arrow from
`W ×_X U_n` to `W ×_X U_m`. -/
theorem transition_app_eq (F : Sheaf (etaleSimplicialSite A).totalTopology (Type (u + 1)))
    {m n : SimplexCategory} (χ : m ⟶ n) (W : SpacesEtale B S hS A.right) :
    ((componentPushforwardTransition (etaleSituation A) _ _ (etaleAugmentation A) χ).app F).hom.app
      (op W) = F.obj.map ((Pseudofunctor.CoGrothendieck.ιNatTrans
        (etaleSimplicialSite A).totalPseudofunctor χ.op).app (Sum.inl W : Index A m)).op := by
  refine (SimplicialSite.ContinuousAugmentation.componentPushforwardTransition_app_hom_app
    (etaleAugmentation A) χ F W).trans ?_
  let ι := Pseudofunctor.CoGrothendieck.ι (etaleSimplicialSite A).totalPseudofunctor (op n)
  have h₁ : eqToHom (Functor.congr_obj
      ((etaleAugmentation A).componentSiteFunctor_comp_eq χ) W).symm =
      𝟙 (((etaleAugmentation A).componentSiteFunctor n).obj W) := rfl
  exact (congrArg (fun k => F.obj.map (Quiver.Hom.op (k ≫
      (SimplicialSiteSituation.continuousInclusionTransition _ χ).app
        (((etaleAugmentation A).componentSiteFunctor m).obj W))))
      ((ι.congr_map h₁).trans (ι.map_id _))).trans
    (congrArg (fun k => F.obj.map (Quiver.Hom.op k)) (Category.id_comp _))

/-- The inverse of the unit isomorphism of the total pseudofunctor of `U_{spaces, étale}` is the
identification of `x` with `x.push 𝟙`. -/
theorem totalPseudofunctor_mapId_inv_app (b : SimplexCategoryᵒᵖ)
    (x : (etaleSimplicialSite A).totalPseudofunctor.obj ⟨op b⟩) :
    ((etaleSimplicialSite A).totalPseudofunctor.mapId ⟨op b⟩).inv.toNatTrans.app x =
      eqToHom (show x = ((etaleSimplicialSite A).totalPseudofunctor.map
        (𝟙 (⟨op b⟩ : LocallyDiscrete SimplexCategoryᵒᵖᵒᵖ))).toFunctor.obj x from
          (Index.push_id (A := A) (n := b.unop) x).symm) := by
  simp only [SimplicialSite.totalPseudofunctor, Functor.toPseudofunctor'_mapId, eqToIso.inv]
  exact Cat.eqToHom_app _ _ _ x

/-- The comparison functor on a morphism of one simplicial degree is that morphism. -/
theorem phComparisonFunctor_map_ι_fiber_left (b : SimplexCategoryᵒᵖ)
    {x y : (etaleSimplicialSite A).totalPseudofunctor.obj ⟨op b⟩} (k : x ⟶ y) :
    (Grothendieck.Hom.fiber ((phComparisonFunctor A).map
      ((Pseudofunctor.CoGrothendieck.ι _ b).map k))).left = k.hom.hom.left := by
  refine (phComparisonFunctor_map_fiber_left
    ((Pseudofunctor.CoGrothendieck.ι (etaleSimplicialSite A).totalPseudofunctor b).map k)).trans ?_
  change (k ≫ ((etaleSimplicialSite A).totalPseudofunctor.mapId ⟨op b⟩).inv.toNatTrans.app
    y).hom.hom.left ≫ comparison (𝟙 b.unop) y = _
  rw [totalPseudofunctor_mapId_inv_app]
  refine (congrArg₂ (fun s t => s ≫ t) (congrArg (fun t => k.hom.hom.left ≫ t)
    (etaleComponent_eqToHom_left (A := A) (n := b.unop)
      (Index.push_id (A := A) (n := b.unop) y).symm))
    (comparison_id' (A := A) (n := b.unop) y)).trans ?_
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

/-- The functor `V/U_n ↦ V/X` acts on underlying algebraic spaces as the identity. -/
theorem augmentationFunctor_map_left {x y : SpacesTotal A} (f : x ⟶ y) :
    ((SimplicialOver.augmentationFunctor A.left A.hom).map f).left =
      (Grothendieck.Hom.fiber f).left := by
  change _ ≫ (Grothendieck.Hom.fiber f).left = _
  refine (congrArg (· ≫ (Grothendieck.Hom.fiber f).left) ?_).trans (Category.id_comp _)
  rw [eqToHom_app]
  exact (Over.eqToHom_left _).trans (eqToHom_refl _ _)

/-- A morphism `V/U_n → V'/U_m` composed with a morphism over `X` is determined on the underlying
spaces. -/
private theorem augmentationFunctor_map_comp_eq {x y : SpacesTotal A}
    {Z : Over A.right} (f : x ⟶ y)
    (p : (SimplicialOver.augmentationFunctor A.left A.hom).obj y ⟶ Z)
    (q : (SimplicialOver.augmentationFunctor A.left A.hom).obj x ⟶ Z)
    (h : (Grothendieck.Hom.fiber f).left ≫ p.left = q.left) :
    (SimplicialOver.augmentationFunctor A.left A.hom).map f ≫ p = q :=
  Over.OverMorphism.ext ((congrArg (· ≫ p.left) (augmentationFunctor_map_left f)).trans h)

/-! ### The base changes `W ×_X U_n` -/

variable (A) in
/-- The base change `W ×_X U_n → U_n` of an object `W` étale over `X`, as an object of
`(Spaces/U)_total`. -/
abbrev phBaseObj (n : SimplexCategory) (W : SpacesEtale B S hS A.right) : SpacesTotal A :=
  (phComparisonFunctor A).obj (etaleBaseObj A n W)

variable (A) in
/-- The projection `W ×_X U_n → W`, a morphism over `X`. -/
def phBaseProjection (n : SimplexCategory) (W : SpacesEtale B S hS A.right) :
    (SimplicialOver.augmentationFunctor A.left A.hom).obj (phBaseObj A n W) ⟶
      (SpacesEtale.inclusion B S hS A.right).obj W :=
  Over.homMk ((spacesBaseChange B S hS (A.hom.app (op n))).projection.app W)
    ((spacesBaseChange B S hS (A.hom.app (op n))).isPullback W).w

variable (A) in
/-- The underlying morphism of `phBaseProjection` is the projection `W ×_X U_n → W`. -/
@[simp]
theorem phBaseProjection_left (n : SimplexCategory) (W : SpacesEtale B S hS A.right) :
    (phBaseProjection A n W).left =
      (spacesBaseChange B S hS (A.hom.app (op n))).projection.app W :=
  rfl

/-- A morphism `V → W` over `X` from an object `V/U_n` lifts uniquely to `V → W ×_X U_n` over
`U_n`. -/
def phBaseLift {t : SpacesTotal A} (W : SpacesEtale B S hS A.right)
    (f : (SimplicialOver.augmentationFunctor A.left A.hom).obj t ⟶
      (SpacesEtale.inclusion B S hS A.right).obj W) :
    t ⟶ phBaseObj A t.base.unop W :=
  ⟨𝟙 t.base, Over.homMk (((spacesBaseChange B S hS (A.hom.app t.base)).isPullback W).lift
      f.left (SpacesTotal.over t).hom (Over.w f)) (by
    refine (((spacesBaseChange B S hS (A.hom.app t.base)).isPullback W).lift_snd _ _ _).trans ?_
    exact (Category.comp_id _).symm.trans
      (congrArg (fun k => (SpacesTotal.over t).hom ≫ k) (A.left.map_id t.base).symm))⟩

/-- The lift `phBaseLift W f` lies over the identity simplex map. -/
theorem phBaseLift_base {t : SpacesTotal A} (W : SpacesEtale B S hS A.right)
    (f : (SimplicialOver.augmentationFunctor A.left A.hom).obj t ⟶
      (SpacesEtale.inclusion B S hS A.right).obj W) :
    Grothendieck.Hom.base (phBaseLift W f) = 𝟙 t.base :=
  rfl

/-- The lift `phBaseLift W f` followed by the projection to `W` is `f`. -/
theorem phBaseLift_fst {t : SpacesTotal A} (W : SpacesEtale B S hS A.right)
    (f : (SimplicialOver.augmentationFunctor A.left A.hom).obj t ⟶
      (SpacesEtale.inclusion B S hS A.right).obj W) :
    (Grothendieck.Hom.fiber (phBaseLift W f)).left ≫
        (spacesBaseChange B S hS (A.hom.app t.base)).projection.app W = f.left :=
  ((spacesBaseChange B S hS (A.hom.app t.base)).isPullback W).lift_fst _ _ _

/-- Two morphisms into `W ×_X U_n` with the same simplex map and the same projection to `W`
agree. -/
theorem phBase_hom_ext {n : SimplexCategory} {W : SpacesEtale B S hS A.right} {t : SpacesTotal A}
    {g g' : t ⟶ phBaseObj A n W}
    (hb : Grothendieck.Hom.base g = Grothendieck.Hom.base g')
    (hl : (Grothendieck.Hom.fiber g).left ≫
        (spacesBaseChange B S hS (A.hom.app (op n))).projection.app W =
      (Grothendieck.Hom.fiber g').left ≫
        (spacesBaseChange B S hS (A.hom.app (op n))).projection.app W) : g = g' := by
  refine spacesTotal_hom_ext hb
    (((spacesBaseChange B S hS (A.hom.app (op n))).isPullback W).hom_ext hl ?_)
  refine (Over.w (Grothendieck.Hom.fiber g)).trans (Eq.trans ?_
    (Over.w (Grothendieck.Hom.fiber g')).symm)
  change (SpacesTotal.over t).hom ≫ A.left.map (Grothendieck.Hom.base g) =
    (SpacesTotal.over t).hom ≫ A.left.map (Grothendieck.Hom.base g')
  rw [hb]

/-- The morphism `W ×_X U_n → W ×_X U_m` of `(Spaces/U)_total` lying over `U(χ) : U_n → U_m`,
for `χ : [m] → [n]`: the image of the cartesian arrow of `U_{spaces, étale}`. -/
abbrev phBaseTransition {m n : SimplexCategory} (χ : m ⟶ n) (W : SpacesEtale B S hS A.right) :
    phBaseObj A n W ⟶ phBaseObj A m W :=
  (phComparisonFunctor A).map ((Pseudofunctor.CoGrothendieck.ιNatTrans
    (etaleSimplicialSite A).totalPseudofunctor χ.op).app (Sum.inl W : Index A m))

/-- The transition `phBaseTransition χ W` lies over `χ.op`. -/
theorem phBaseTransition_base {m n : SimplexCategory} (χ : m ⟶ n)
    (W : SpacesEtale B S hS A.right) :
    Grothendieck.Hom.base (phBaseTransition χ W) = χ.op :=
  phComparisonFunctor_map_base _

/-- The transition `phBaseTransition χ W` commutes with the projections to `W`. -/
theorem phBaseTransition_fst {m n : SimplexCategory} (χ : m ⟶ n)
    (W : SpacesEtale B S hS A.right) :
    (Grothendieck.Hom.fiber (phBaseTransition χ W)).left ≫
        (spacesBaseChange B S hS (A.hom.app (op m))).projection.app W =
      (spacesBaseChange B S hS (A.hom.app (op n))).projection.app W :=
  (congrArg (· ≫ (spacesBaseChange B S hS (A.hom.app (op m))).projection.app W)
    ((phComparisonFunctor_map_fiber_left ((Pseudofunctor.CoGrothendieck.ιNatTrans
      (etaleSimplicialSite A).totalPseudofunctor χ.op).app (Sum.inl W : Index A m))).trans
        (Category.id_comp _))).trans (comparison_inl_fst χ W)

/-- The transitions of the base changes are compatible with the projections to `W`. -/
theorem augmentationFunctor_map_phBaseTransition {m n : SimplexCategory} (χ : m ⟶ n)
    (W : SpacesEtale B S hS A.right) :
    (SimplicialOver.augmentationFunctor A.left A.hom).map (phBaseTransition χ W) ≫
      phBaseProjection A m W = phBaseProjection A n W :=
  augmentationFunctor_map_comp_eq _ _ _ (phBaseTransition_fst χ W)

variable (A) in
/-- The functor `W ↦ W ×_X U_n` from `X_{spaces, étale}` to `(Spaces/U)_total`: the functor of
the augmentation in degree `n` followed by the comparison functor. -/
abbrev phBaseFunctor (n : SimplexCategory) : SpacesEtale B S hS A.right ⥤ SpacesTotal A :=
  (etaleAugmentation A).totalComponentSiteFunctor n ⋙ phComparisonFunctor A

/-- The projections `W ×_X U_n → W` commute with the morphisms `W ×_X U_n → W' ×_X U_n` induced
by `g : W ⟶ W'`. -/
theorem phBaseFunctor_map_fst (n : SimplexCategory) {W W' : SpacesEtale B S hS A.right}
    (g : W ⟶ W') :
    (Grothendieck.Hom.fiber ((phBaseFunctor A n).map g)).left ≫
        (spacesBaseChange B S hS (A.hom.app (op n))).projection.app W' =
      (spacesBaseChange B S hS (A.hom.app (op n))).projection.app W ≫ g.hom.left := by
  let ψ := SimplexCategory.const (SimplexCategory.mk 0) n 0
  let k := (augmentationFunctor (A := A)).map g
  have h₁ : (Grothendieck.Hom.fiber ((phBaseFunctor A n).map g)).left =
      ((transition ψ).map k).hom.hom.left :=
    phComparisonFunctor_map_ι_fiber_left (op n) ((transition ψ).map k)
  have h₂ := comparison_inl_fst (A := A) ψ W'
  have h₃ := transition_map_hom_comp ψ k
  have h₄ := (spacesBaseChange B S hS
    (A.hom.app (op (SimplexCategory.mk 0)))).projection.naturality g
  have h₅ := comparison_inl_fst (A := A) ψ W
  exact ((congrArg₂ (fun s t => s ≫ t) h₁ h₂.symm).trans (Category.assoc _ _ _).symm).trans
    (((congrArg (· ≫ (spacesBaseChange B S hS
      (A.hom.app (op (SimplexCategory.mk 0)))).projection.app W') h₃).trans
        (Category.assoc _ _ _)).trans (((congrArg (comparison ψ (Sum.inl W : Index A _) ≫ ·)
          h₄).trans (Category.assoc _ _ _).symm).trans (congrArg (· ≫ g.hom.left) h₅)))

variable (A) in
/-- The projections `W ×_X U_n → W`, natural in `W`. -/
def phBaseProjectionNatTrans (n : SimplexCategory) :
    phBaseFunctor A n ⋙ SimplicialOver.augmentationFunctor A.left A.hom ⟶
      SpacesEtale.inclusion B S hS A.right where
  app W := phBaseProjection A n W
  naturality _ W' g := Over.OverMorphism.ext ((congrArg (· ≫ (phBaseProjection A n W').left)
    (augmentationFunctor_map_left ((phBaseFunctor A n).map g))).trans (phBaseFunctor_map_fst n g))

/-- The lift of the projection `W ×_X U_n → W` is the identity. -/
theorem phBaseLift_projection (n : SimplexCategory) (W : SpacesEtale B S hS A.right) :
    phBaseLift W (phBaseProjection A n W) = 𝟙 (phBaseObj A n W) :=
  phBase_hom_ext rfl ((phBaseLift_fst W (phBaseProjection A n W)).trans
    (Eq.trans (Category.id_comp _).symm (congrArg (· ≫ _)
      (spacesTotal_id_fiber_left (phBaseObj A n W)).symm)))

/-- The lift of `f` followed by the projection to `W` is `f`. -/
theorem augmentationFunctor_map_phBaseLift {t : SpacesTotal A} (W : SpacesEtale B S hS A.right)
    (f : (SimplicialOver.augmentationFunctor A.left A.hom).obj t ⟶
      (SpacesEtale.inclusion B S hS A.right).obj W) :
    (SimplicialOver.augmentationFunctor A.left A.hom).map (phBaseLift W f) ≫
      phBaseProjection A t.base.unop W = f :=
  augmentationFunctor_map_comp_eq _ _ _ (phBaseLift_fst W f)

/-- The lifts to the base changes are compatible with the morphisms of `(Spaces/U)_total`. -/
theorem phBaseLift_naturality {t t' : SpacesTotal A} (g : t' ⟶ t)
    (W : SpacesEtale B S hS A.right)
    (f : (SimplicialOver.augmentationFunctor A.left A.hom).obj t ⟶
      (SpacesEtale.inclusion B S hS A.right).obj W) :
    g ≫ phBaseLift W f =
      phBaseLift W ((SimplicialOver.augmentationFunctor A.left A.hom).map g ≫ f) ≫
        phBaseTransition (Grothendieck.Hom.base g).unop W := by
  refine phBase_hom_ext ?_ ?_
  · exact (Category.comp_id _).trans ((Category.id_comp _).symm.trans
      (congrArg (𝟙 _ ≫ ·) (phBaseTransition_base _ W).symm))
  · refine ((congrArg (· ≫ _) (spacesTotal_comp_fiber_left g (phBaseLift W f))).trans
      ((Category.assoc _ _ _).trans (congrArg ((Grothendieck.Hom.fiber g).left ≫ ·)
        (phBaseLift_fst W f)))).trans ?_
    let l := phBaseLift W ((SimplicialOver.augmentationFunctor A.left A.hom).map g ≫ f)
    let τ := phBaseTransition (A := A) (Grothendieck.Hom.base g).unop W
    refine Eq.trans ?_ ((congrArg (· ≫ (spacesBaseChange B S hS
      (A.hom.app t.base)).projection.app W) (spacesTotal_comp_fiber_left l τ)).trans
        (Category.assoc _ _ _)).symm
    refine Eq.trans ?_ (congrArg ((Grothendieck.Hom.fiber l).left ≫ ·)
      (phBaseTransition_fst (Grothendieck.Hom.base g).unop W)).symm
    refine Eq.trans ?_ (phBaseLift_fst W
      ((SimplicialOver.augmentationFunctor A.left A.hom).map g ≫ f)).symm
    exact (congrArg (· ≫ f.left) (augmentationFunctor_map_left g)).symm

variable (A) in
/-- The leg in degree `n` of the comparison: the sections of the direct image of `F` along
`V/U_n ↦ V/X` over `W` restrict, along the projection `W ×_X U_n → W`, to the sections of `F`
over `W ×_X U_n`. -/
def phSectionLeg (n : SimplexCategory) (G : (SpacesTotal A)ᵒᵖ ⥤ Type (u + 1)) :
    (SpacesEtale.inclusion B S hS A.right).op ⋙
        (SimplicialOver.augmentationFunctor A.left A.hom).op.ran.obj G ⟶
      (phBaseFunctor A n).op ⋙ G :=
  Functor.whiskerRight (NatTrans.op (phBaseProjectionNatTrans A n)) _ ≫
    Functor.whiskerLeft (phBaseFunctor A n).op
      ((SimplicialOver.augmentationFunctor A.left A.hom).op.ranCounit.app G)

/-- The sections over `W` of the right Kan extension of `G` along `V/U_n ↦ V/X` are the
compatible families of sections of `G` over the base changes `W ×_X U_n`. -/
theorem phSections_existsUnique (G : (SpacesTotal A)ᵒᵖ ⥤ Type (u + 1))
    (W : SpacesEtale B S hS A.right) (x : ∀ n, G.obj (op (phBaseObj A n W)))
    (hx : ∀ {m n : SimplexCategory} (χ : m ⟶ n), G.map (phBaseTransition χ W).op (x m) = x n) :
    ∃! s : ((SimplicialOver.augmentationFunctor A.left A.hom).op.ran.obj G).obj
        (op ((SpacesEtale.inclusion B S hS A.right).obj W)),
      ∀ n, (phSectionLeg A n G).app (op W) s = x n := by
  let L := (SimplicialOver.augmentationFunctor A.left A.hom).op
  let P := L.isPointwiseRightKanExtensionRanCounit G
    (op ((SpacesEtale.inclusion B S hS A.right).obj W))
  have hP := (Types.isLimit_iff _).mp ⟨P⟩
  let σ : ∀ f : StructuredArrow (op ((SpacesEtale.inclusion B S hS A.right).obj W)) L,
      G.obj f.right := fun f => G.map (phBaseLift W f.hom.unop).op (x f.right.unop.base.unop)
  have hσ : σ ∈ (StructuredArrow.proj _ L ⋙ G).sections := by
    intro f₁ f₂ φ
    have key := phBaseLift_naturality φ.right.unop W f₁.hom.unop
    rw [show (SimplicialOver.augmentationFunctor A.left A.hom).map φ.right.unop ≫ f₁.hom.unop =
      f₂.hom.unop from congrArg Quiver.Hom.unop (StructuredArrow.w φ)] at key
    change G.map φ.right (G.map (phBaseLift W f₁.hom.unop).op (x _)) =
      G.map (phBaseLift W f₂.hom.unop).op (x _)
    rw [← Functor.map_comp_apply, ← hx (Grothendieck.Hom.base φ.right.unop).unop,
      ← Functor.map_comp_apply]
    exact congrArg (fun k => G.map k.op (x _)) key
  obtain ⟨s, hs, huniq⟩ := hP σ hσ
  refine ⟨s, fun n => ?_, fun s' hs' => huniq s' (fun f => ?_)⟩
  · refine (hs (StructuredArrow.mk (phBaseProjection A n W).op)).trans ?_
    exact (congrArg (fun k => G.map (Quiver.Hom.op k) (x n)) (phBaseLift_projection n W)).trans
      (G.map_id_apply _ (x n))
  · let ψ : StructuredArrow.mk (phBaseProjection A f.right.unop.base.unop W).op ⟶ f :=
      StructuredArrow.homMk (phBaseLift W f.hom.unop).op
        (congrArg Quiver.Hom.op (augmentationFunctor_map_phBaseLift W f.hom.unop))
    let c := (Functor.RightExtension.mk _ (L.ranCounit.app G)).coneAt
      (op ((SpacesEtale.inclusion B S hS A.right).obj W))
    refine (ConcreteCategory.congr_hom (c.w ψ) s').symm.trans ?_
    exact congrArg (G.map (phBaseLift W f.hom.unop).op) (hs' f.right.unop.base.unop)

/-- The leg `phSectionLeg A n G` sends a section over `W` to the counit applied to its restriction
along the projection `W ×_X U_n → W`. -/
theorem phSectionLeg_app_apply (n : SimplexCategory) (G : (SpacesTotal A)ᵒᵖ ⥤ Type (u + 1))
    (W : SpacesEtale B S hS A.right)
    (s : ((SimplicialOver.augmentationFunctor A.left A.hom).op.ran.obj G).obj
      (op ((SpacesEtale.inclusion B S hS A.right).obj W))) :
    (phSectionLeg A n G).app (op W) s =
      ((SimplicialOver.augmentationFunctor A.left A.hom).op.ranCounit.app G).app
        (op (phBaseObj A n W))
        (((SimplicialOver.augmentationFunctor A.left A.hom).op.ran.obj G).map
          (phBaseProjection A n W).op s) :=
  rfl

/-- The legs are compatible with the transitions of the base changes. -/
theorem phSectionLeg_transition (G : (SpacesTotal A)ᵒᵖ ⥤ Type (u + 1)) {m n : SimplexCategory}
    (χ : m ⟶ n) (W : SpacesEtale B S hS A.right)
    (s : ((SimplicialOver.augmentationFunctor A.left A.hom).op.ran.obj G).obj
      (op ((SpacesEtale.inclusion B S hS A.right).obj W))) :
    G.map (phBaseTransition χ W).op ((phSectionLeg A m G).app (op W) s) =
      (phSectionLeg A n G).app (op W) s := by
  let L := (SimplicialOver.augmentationFunctor A.left A.hom).op
  refine (NatTrans.naturality_apply (L.ranCounit.app G) (phBaseTransition χ W).op
    ((L.ran.obj G).map (phBaseProjection A m W).op s)).symm.trans ?_
  refine congrArg ((L.ranCounit.app G).app (op (phBaseObj A n W))) ?_
  refine (Functor.map_comp_apply (L.ran.obj G) _ _ s).symm.trans ?_
  exact congrArg (fun k => (L.ran.obj G).map k s)
    (congrArg Quiver.Hom.op (augmentationFunctor_map_phBaseTransition χ W))

/-- The legs are natural in the presheaf. -/
theorem phSectionLeg_naturality (n : SimplexCategory) {G G' : (SpacesTotal A)ᵒᵖ ⥤ Type (u + 1)}
    (α : G ⟶ G') :
    Functor.whiskerLeft (SpacesEtale.inclusion B S hS A.right).op
        ((SimplicialOver.augmentationFunctor A.left A.hom).op.ran.map α) ≫
      phSectionLeg A n G' =
    phSectionLeg A n G ≫ Functor.whiskerLeft (phBaseFunctor A n).op α := by
  let L := (SimplicialOver.augmentationFunctor A.left A.hom).op
  ext W s
  change ((L.ranCounit.app G').app (op (phBaseObj A n W.unop)))
      ((L.ran.obj G').map (phBaseProjection A n W.unop).op ((L.ran.map α).app _ s)) =
    α.app _ (((L.ranCounit.app G).app (op (phBaseObj A n W.unop)))
      ((L.ran.obj G).map (phBaseProjection A n W.unop).op s))
  rw [← NatTrans.naturality_apply (L.ran.map α)]
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (L.ranCounit.naturality α) (op (phBaseObj A n W.unop)))
    ((L.ran.obj G).map (phBaseProjection A n W.unop).op s)

/-! ### The commutative square -/

section Square

variable (J : GrothendieckTopology (AlgebraicSpaces B S hS))
  [hJ : ∀ X : AlgebraicSpaces B S hS,
    (SpacesEtale.inclusion B S hS X).IsContinuous (SpacesEtale.topology B S hS X) (J.over X)]

variable (A) in
/-- The composite `h_{-1, *} ∘ a_*` of the direct images along `V/U_n ↦ V/X` and along
`W ↦ W/X`. -/
abbrev phLowerPushforward :
    Sheaf (SimplicialOver.totalTopology J A.left) (Type (u + 1)) ⥤
      Sheaf (SpacesEtale.topology B S hS A.right) (Type (u + 1)) :=
  (SimplicialOver.augmentationFunctor A.left A.hom).sheafPushforwardCocontinuous (Type (u + 1))
      (SimplicialOver.totalTopology J A.left) (J.over A.right) ⋙
    (spacesEtaleComparisonMorphism J A.right).pushforward

/-- The legs `phSectionLeg` are compatible with the transitions
`componentPushforwardTransition` of the component direct images. -/
theorem phSectionLeg_componentPushforwardTransition
    (F : Sheaf (SimplicialOver.totalTopology J A.left) (Type (u + 1))) {m n : SimplexCategory}
    (χ : m ⟶ n) (W : SpacesEtale B S hS A.right)
    (s : ((SimplicialOver.augmentationFunctor A.left A.hom).op.ran.obj F.obj).obj
      (op ((SpacesEtale.inclusion B S hS A.right).obj W))) :
    ((componentPushforwardTransition (etaleSituation A) _ _ (etaleAugmentation A) χ).app
      ((phComparisonMorphism A J).pushforward.obj F)).hom.app (op W)
        ((phSectionLeg A m F.obj).app (op W) s) = (phSectionLeg A n F.obj).app (op W) s :=
  (ConcreteCategory.congr_hom (transition_app_eq
    ((phComparisonMorphism A J).pushforward.obj F) χ W)
      ((phSectionLeg A m F.obj).app (op W) s)).trans (phSectionLeg_transition F.obj χ W s)

variable (A) in
/-- The leg in degree `n` of the comparison, as a morphism of sheaves. -/
def phConeLeg (F : Sheaf (SimplicialOver.totalTopology J A.left) (Type (u + 1)))
    (n : SimplexCategory) :
    (phLowerPushforward A J).obj F ⟶
      (componentPushforward (etaleSituation A) _ _ (etaleAugmentation A) n).obj
        ((phComparisonMorphism A J).pushforward.obj F) :=
  ObjectProperty.homMk (phSectionLeg A n F.obj)

/-- The leg `phConeLeg A J F n` acts on sections as `phSectionLeg A n F.obj`. -/
theorem phConeLeg_hom_app_apply
    (F : Sheaf (SimplicialOver.totalTopology J A.left) (Type (u + 1))) (n : SimplexCategory)
    (W : (SpacesEtale B S hS A.right)ᵒᵖ) (s : ((phLowerPushforward A J).obj F).obj.obj W) :
    (phConeLeg A J F n).hom.app W s = (phSectionLeg A n F.obj).app (op W.unop) s :=
  rfl

/-- The legs `phConeLeg` are compatible, on sections, with the transitions
`componentPushforwardTransition`. -/
theorem phConeLeg_transition_apply
    (F : Sheaf (SimplicialOver.totalTopology J A.left) (Type (u + 1))) {m n : SimplexCategory}
    (χ : m ⟶ n) (W : SpacesEtale B S hS A.right)
    (s : ((phLowerPushforward A J).obj F).obj.obj (op W)) :
    ((componentPushforwardTransition (etaleSituation A) _ _ (etaleAugmentation A) χ).app
      ((phComparisonMorphism A J).pushforward.obj F)).hom.app (op W)
        ((phConeLeg A J F m).hom.app (op W) s) = (phConeLeg A J F n).hom.app (op W) s :=
  phSectionLeg_componentPushforwardTransition J F χ W s

/-- A section of the composite `phConeLeg A J F m ≫ T` is `T` applied to the section of
`phConeLeg A J F m`. -/
theorem phConeLeg_comp_apply
    (F : Sheaf (SimplicialOver.totalTopology J A.left) (Type (u + 1))) {m : SimplexCategory}
    {Y : Sheaf (SpacesEtale.topology B S hS A.right) (Type (u + 1))}
    (T : (componentPushforward (etaleSituation A) _ _ (etaleAugmentation A) m).obj
      ((phComparisonMorphism A J).pushforward.obj F) ⟶ Y) (W : SpacesEtale B S hS A.right)
    (s : ((phLowerPushforward A J).obj F).obj.obj (op W)) :
    ((phConeLeg A J F m ≫ T).hom.app (op W)) s =
      T.hom.app (op W) ((phConeLeg A J F m).hom.app (op W) s) :=
  rfl

/-- The legs `phConeLeg` are compatible with the transitions `componentPushforwardTransition`. -/
theorem phConeLeg_comp_transition
    (F : Sheaf (SimplicialOver.totalTopology J A.left) (Type (u + 1))) {m n : SimplexCategory}
    (χ : m ⟶ n) :
    phConeLeg A J F m ≫
        (componentPushforwardTransition (etaleSituation A) _ _ (etaleAugmentation A) χ).app
          ((phComparisonMorphism A J).pushforward.obj F) = phConeLeg A J F n := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext W
  induction W with | op W => ?_
  exact ConcreteCategory.hom_ext _ _ fun s =>
    (phConeLeg_comp_apply J F ((componentPushforwardTransition (etaleSituation A) _ _
      (etaleAugmentation A) χ).app ((phComparisonMorphism A J).pushforward.obj F)) W s).trans
        (phConeLeg_transition_apply J F χ W s)

variable (A) in
/-- The cone over the cosimplicial sheaf of the étale augmentation of `h_* F` with vertex
`h_{-1, *} a_* F`: in degree `n`, restriction along the projections `W ×_X U_n → W`. -/
def phCone (F : Sheaf (SimplicialOver.totalTopology J A.left) (Type (u + 1))) :
    Cone (SimplicialSiteSituation.Augmentation.pushforwardDiagram (etaleSituation A) _ _
      (etaleAugmentation A) ((phComparisonMorphism A J).pushforward.obj F)) where
  pt := (phLowerPushforward A J).obj F
  π :=
    { app n := phConeLeg A J F n
      naturality _ _ χ := (Category.id_comp _).trans (phConeLeg_comp_transition J F χ).symm }

/-- The sections of `h_{-1, *} a_* F` over `W` are the compatible families of sections over the
`W ×_X U_n`. -/
theorem phConeLeg_existsUnique
    (F : Sheaf (SimplicialOver.totalTopology J A.left) (Type (u + 1)))
    (W : SpacesEtale B S hS A.right)
    (x : ∀ n, ((componentPushforward (etaleSituation A) _ _ (etaleAugmentation A) n).obj
      ((phComparisonMorphism A J).pushforward.obj F)).obj.obj (op W))
    (hx : ∀ {m n : SimplexCategory} (χ : m ⟶ n),
      ((componentPushforwardTransition (etaleSituation A) _ _ (etaleAugmentation A) χ).app
        ((phComparisonMorphism A J).pushforward.obj F)).hom.app (op W) (x m) = x n) :
    ∃! s : ((phLowerPushforward A J).obj F).obj.obj (op W),
      ∀ n, (phConeLeg A J F n).hom.app (op W) s = x n :=
  phSections_existsUnique F.obj W x fun χ =>
    (ConcreteCategory.congr_hom (transition_app_eq
      ((phComparisonMorphism A J).pushforward.obj F) χ W) (x _)).symm.trans (hx χ)

/-- The cone is a limit cone: a section of `h_{-1, *} a_* F` over `W` is the same as a compatible
family of sections of `F` over the `W ×_X U_n`. -/
def phConeIsLimit (F : Sheaf (SimplicialOver.totalTopology J A.left) (Type (u + 1))) :
    IsLimit (phCone A J F) :=
  isLimitOfReflects (sheafToPresheaf _ _) (evaluationJointlyReflectsLimits _ fun
    | op W => Classical.choice ((Types.isLimit_iff _).mpr fun x hx =>
      phConeLeg_existsUnique J F W x fun χ => hx χ))

/-- The legs are natural in the sheaf. -/
theorem phConeLeg_naturality {F F' : Sheaf (SimplicialOver.totalTopology J A.left) (Type (u + 1))}
    (k : F ⟶ F') (n : SimplexCategory) :
    (phLowerPushforward A J).map k ≫ phConeLeg A J F' n =
      phConeLeg A J F n ≫ (componentPushforward (etaleSituation A) _ _ (etaleAugmentation A) n).map
        ((phComparisonMorphism A J).pushforward.map k) :=
  Sheaf.hom_ext (phSectionLeg_naturality n k.hom)

variable (A) in
/-- **The square of Tag 0DHJ on direct images**, with `h_{-1, *}` and `a_{ph, *}` written as
restriction and right Kan extension along the site functors. -/
def phComparisonSquareRestrictionIso :
    phLowerPushforward A J ≅
      (phComparisonMorphism A J).pushforward ⋙ (etaleAugmentationMorphism A).pushforward :=
  NatIso.ofComponents
    (fun F => (phConeIsLimit J F).conePointUniqueUpToIso (limit.isLimit _))
    (fun {F F'} k => by
      refine limit.hom_ext fun n => ?_
      refine ((Category.assoc _ _ _).trans (congrArg ((phLowerPushforward A J).map k ≫ ·)
        (IsLimit.conePointUniqueUpToIso_hom_comp (phConeIsLimit J F') (limit.isLimit _)
          n))).trans ?_
      refine (phConeLeg_naturality J k n).trans ?_
      refine Eq.trans ?_ (Category.assoc _ _ _).symm
      refine Eq.trans ?_ (congrArg (((phConeIsLimit J F).conePointUniqueUpToIso
        (limit.isLimit _)).hom ≫ ·)
          (limMap_π ((SimplicialSiteSituation.Augmentation.cosimplicialPushforward
            (etaleSituation A) _ _ (etaleAugmentation A)).flip.map
              ((phComparisonMorphism A J).pushforward.map k)) n)).symm
      refine Eq.trans ?_ (Category.assoc _ _ _)
      exact congrArg (· ≫ _) (IsLimit.conePointUniqueUpToIso_hom_comp (phConeIsLimit J F)
        (limit.isLimit _) n).symm)

variable (A) in
/-- **The square of Tag 0DHJ on direct images**, for a topology on algebraic spaces whose
localizations receive the spaces-étale sites continuously: `h_{-1, *} ∘ a_{*} ≅ a_* ∘ h_*`. -/
def phComparisonSquarePushforwardIso :
    (SimplicialOver.augmentationMorphismOfTopoi J A.left A.hom).pushforward ⋙
        (spacesEtaleComparisonMorphism J A.right).pushforward ≅
      (phComparisonMorphism A J).pushforward ⋙ (etaleAugmentationMorphism A).pushforward :=
  Functor.isoWhiskerRight
      (eqToIso (SimplicialOver.augmentationMorphismOfTopoi_pushforward J A.left A.hom)) _ ≪≫
    phComparisonSquareRestrictionIso A J

variable (A) in
/-- **The square of Tag 0DHJ on inverse images**: `h⁻¹ ∘ a⁻¹ ≅ a⁻¹ ∘ h_{-1}⁻¹`, the conjugate of
`phComparisonSquarePushforwardIso`, inverse images being left adjoint to direct images. -/
def phComparisonSquareInverseImageIso :
    (etaleAugmentationMorphism A).inverseImage ⋙ (phComparisonMorphism A J).inverseImage ≅
      (spacesEtaleComparisonMorphism J A.right).inverseImage ⋙
        (SimplicialOver.augmentationMorphismOfTopoi J A.left A.hom).inverseImage :=
  (conjugateIsoEquiv
    ((spacesEtaleComparisonMorphism J A.right).adj.comp
      (SimplicialOver.augmentationMorphismOfTopoi J A.left A.hom).adj)
    ((etaleAugmentationMorphism A).adj.comp (phComparisonMorphism A J).adj)).symm
      (phComparisonSquarePushforwardIso A J)

end Square

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.BigPHSpaceSite

open Space

variable {S : Scheme.{u}} (P : BigPHSpaceSite S) (A : SimplicialObject.Augmented P.Spaces)

/-- **Tag 0DHJ, on direct images.** Let `a : U → X` be an augmented simplicial algebraic space
over `S`. The diagram of topoi
```
Sh((Spaces/U)_{ph, total}) --h--> Sh(U_étale)
        | a_ph                       | a
Sh((Spaces/X)_ph)        --h₋₁--> Sh(X_étale)
```
commutes: the direct image of `h₋₁ ∘ a_ph` is that of `a ∘ h`. -/
@[stacks 0DHJ "the commutative diagram of topoi, on direct images"]
def phEtaleComparisonSquarePushforwardIso :
    (SimplicialOver.augmentationMorphismOfTopoi P.topology A.left A.hom).pushforward ⋙
        (spacesEtaleComparisonMorphism P.topology A.right).pushforward ≅
      (phComparisonMorphism A P.topology).pushforward ⋙ (etaleAugmentationMorphism A).pushforward :=
  phComparisonSquarePushforwardIso A P.topology

/-- **Tag 0DHJ, on inverse images**: `h⁻¹ ∘ a⁻¹ ≅ a_ph⁻¹ ∘ h₋₁⁻¹`. -/
@[stacks 0DHJ "the commutative diagram of topoi, on inverse images"]
def phEtaleComparisonSquareInverseImageIso :
    (etaleAugmentationMorphism A).inverseImage ⋙ (phComparisonMorphism A P.topology).inverseImage ≅
      (spacesEtaleComparisonMorphism P.topology A.right).inverseImage ⋙
        (SimplicialOver.augmentationMorphismOfTopoi P.topology A.left A.hom).inverseImage :=
  phComparisonSquareInverseImageIso A P.topology

end AlgebraicGeometry.BigPHSpaceSite
