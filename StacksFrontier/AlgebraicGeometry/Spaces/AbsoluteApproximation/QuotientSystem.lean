module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Groupoids.QuotientSheaf.BigSitePullbackSquare
public import StacksFrontier.AlgebraicGeometry.LimitApprox.DescendOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartRespectsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineSiteLimitCone
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.CutoffIndexEmptyLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedAbsolute
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae03KM
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.AlgebraicQuotient
import all StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.QcqsCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSiteObject
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.Topology.Dimension.KrullSupplement
public import StacksFrontier.Topology.Sheaves.Functors.Module.PullbackCompSupplement

/-!
# Inverse systems of quotients of étale equivalence relations

The proof of Stacks 07SU (absolute Noetherian approximation) builds the approximating spaces
as quotients `X_i = V_i / R_i` of étale equivalence relations on schemes, forming an inverse
system whose transition squares on the source maps are cartesian, and ends by identifying the
given space with the limit of the quotients. This file carries out that part of the argument
for an arbitrary such system on the big fppf site.

## Main definitions

* `AlgebraicGeometry.Space.quotientHom`: the morphism of quotient sheaves induced by a morphism
  of pairs of morphisms of the site.
* `AlgebraicGeometry.Space.EtaleRelationSystem`: an inverse system of étale equivalence
  relations on objects of the site with cartesian source squares, and
  `AlgebraicGeometry.Space.EtaleRelationSystem.quotient`, its system of quotients.

## Main results

* `AlgebraicGeometry.Space.isPullback_quotientMap`: Stacks 07S3 on the big fppf site, for the
  quotient maps `U ⟶ U/R` of two étale equivalence relations.
* `AlgebraicGeometry.Space.isAffineHom_quotientHom`: the induced morphism of quotients is affine
  when the map of base objects is (Stacks 03WG).
* `AlgebraicGeometry.Space.isPullback_limitLift_of_cartesian`: the limit of a cartesian inverse
  system of representables over an inverse system of presheaves is the base change of the
  limit of the target system.
* `AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_quotient`: Stacks 07S4 for the quotient of
  an étale equivalence relation with quasi-compact relation scheme on a quasi-separated scheme.
* `AlgebraicGeometry.Space.isFiniteType_quotient`: over `Spec ℤ`, the quotient of an étale
  equivalence relation on a quasi-compact scheme locally of finite type over `Spec ℤ` is of
  finite type over `Spec ℤ` (Stacks 040Y, 040W).
* `AlgebraicGeometry.Space.EtaleRelationSystem.isPullback_limitToQuotient_kernelPair` and
  `AlgebraicGeometry.Space.EtaleRelationSystem.exists_iso_limit_quotient`: the limit of the
  relations is the kernel pair of the limit of the quotient maps, and a sheaf presented by the
  limit of the objects with that kernel pair is the limit of the quotients. This is the
  closing step ("proof of the claim") of the proof of Stacks 07SU.
* `AlgebraicGeometry.Space.EtaleRelationSystem.hasNoetherianApproximation`: the conclusion of
  Stacks 07SU for a sheaf presented by the limit of such a system of finite type relations over
  `Spec ℤ`. What remains of Stacks 07SU is the construction of the system (the stratification
  of Stacks 07ST, the descent of the étale neighbourhood to a finite stage, and the glueing of
  the relations `R_i`).

## Implementation notes

No cardinality condition on the index category enters: the limit of the quotient system is the
limit of presheaves, and it is identified with a given sheaf by comparing two coequalizer
presentations in fppf sheaves, rather than by first recognizing the limit as an algebraic space
through Stacks 07SF.

## References

* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
* [Stacks Project, Tag 07S3](https://stacks.math.columbia.edu/tag/07S3)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
* [Stacks Project, Tag 0262](https://stacks.math.columbia.edu/tag/0262)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Groupoids

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasPullback_presheaf_QuotientSystem
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

section

variable [HasSheafify (BigFppfOver.topology B S hS) (Type u)]

/-- The quotient map of a pair of morphisms of the site is the projection onto the quotient
sheaf, read through the identification of the restricted functor of points with the
represented presheaf. -/
theorem quotientMap_eq_pointsIsoYoneda_inv {R U : BigFppfOver B S hS} (s t : R ⟶ U) :
    quotientMap B S hS s t =
      (pointsIsoYoneda (Over.post (X := B.obj hS) B.inclusion) U).inv ≫
        Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion)
          (relation B S hS s t) := by
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp, quotientMap, Equiv.apply_symm_apply]
  congr 1

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- The source map of the pre-relation of a pair of morphisms of the site is the image of the
second morphism. -/
theorem relation_source {R U : BigFppfOver B S hS} (s t : R ⟶ U) :
    (relation B S hS s t).source = (Over.post (X := B.obj hS) B.inclusion).map s :=
  prod.lift_snd _ _

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- The target map of the pre-relation of a pair of morphisms of the site is the image of the
first morphism. -/
theorem relation_target {R U : BigFppfOver B S hS} (s t : R ⟶ U) :
    (relation B S hS s t).target = (Over.post (X := B.obj hS) B.inclusion).map t :=
  prod.lift_fst _ _

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- A morphism of pairs of morphisms of the site, commuting with both maps, as a morphism of
the induced pre-relations: the source compatibility. -/
theorem relation_source_comp {R U R' U' : BigFppfOver B S hS} (s t : R ⟶ U) (s' t' : R' ⟶ U')
    (r : R ⟶ R') (f : U ⟶ U') (hs : r ≫ s' = s ≫ f) :
    (Over.post (X := B.obj hS) B.inclusion).map r ≫ (relation B S hS s' t').source =
      (relation B S hS s t).source ≫ (Over.post (X := B.obj hS) B.inclusion).map f := by
  rw [relation_source, relation_source, ← Functor.map_comp, ← Functor.map_comp, hs]

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- The target compatibility of a morphism of pairs of morphisms of the site. -/
theorem relation_target_comp {R U R' U' : BigFppfOver B S hS} (s t : R ⟶ U) (s' t' : R' ⟶ U')
    (r : R ⟶ R') (f : U ⟶ U') (ht : r ≫ t' = t ≫ f) :
    (Over.post (X := B.obj hS) B.inclusion).map r ≫ (relation B S hS s' t').target =
      (relation B S hS s t).target ≫ (Over.post (X := B.obj hS) B.inclusion).map f := by
  rw [relation_target, relation_target, ← Functor.map_comp, ← Functor.map_comp, ht]

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- The underlying morphism of presheaves of a composite of morphisms of sheaves. -/
theorem _root_.CategoryTheory.Sheaf.comp_hom' {C : Type*} [Category C]
    {J : GrothendieckTopology C} {F G H : Sheaf J (Type u)} (a : F ⟶ G) (b : G ⟶ H) :
    a.hom ≫ b.hom = (a ≫ b).hom := rfl

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
variable {B S hS} in
/-- A commutative square of the site whose image in schemes is cartesian is cartesian after
`Over.post` of the inclusion of the site. -/
theorem isPullback_post_of_isPullback_toScheme {X Y Z W : BigFppfOver B S hS} {a : X ⟶ Y}
    {b : X ⟶ Z} {c : Y ⟶ W} {d : Z ⟶ W} (w : a ≫ c = b ≫ d)
    (h : IsPullback ((BigFppfOver.toScheme B S hS).map a) ((BigFppfOver.toScheme B S hS).map b)
      ((BigFppfOver.toScheme B S hS).map c) ((BigFppfOver.toScheme B S hS).map d)) :
    IsPullback ((Over.post (X := B.obj hS) B.inclusion).map a)
      ((Over.post (X := B.obj hS) B.inclusion).map b)
      ((Over.post (X := B.obj hS) B.inclusion).map c)
      ((Over.post (X := B.obj hS) B.inclusion).map d) :=
  IsPullback.of_map (Over.forget _) (by rw [← Functor.map_comp, ← Functor.map_comp, w]) h

/-- The morphism of quotient sheaves induced by a morphism `(r, f)` of pairs of morphisms of the
site, commuting with both maps. -/
noncomputable def quotientHom {R U R' U' : BigFppfOver B S hS} (s t : R ⟶ U) (s' t' : R' ⟶ U')
    (r : R ⟶ R') (f : U ⟶ U') (hs : r ≫ s' = s ≫ f) (ht : r ≫ t' = t ≫ f) :
    (Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion)
        (relation B S hS s t)).obj ⟶
      (Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion)
        (relation B S hS s' t')).obj :=
  (Stacks.Groupoids.quotientSheafMap (BigFppfOver.topology B S hS) (Over.post B.inclusion) _ _
    ((Over.post (X := B.obj hS) B.inclusion).map r) ((Over.post (X := B.obj hS) B.inclusion).map f)
    (relation_source_comp B S hS s t s' t' r f hs)
    (relation_target_comp B S hS s t s' t' r f ht)).hom

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- The identification of the restricted functor of points with the represented presheaf is
natural, read through its inverse. -/
theorem pointsIsoYoneda_inv_naturality {U U' : BigFppfOver B S hS} (f : U ⟶ U') :
    (pointsIsoYoneda (Over.post (X := B.obj hS) B.inclusion) U).inv ≫
        (Over.post (X := B.obj hS) B.inclusion).op.whiskerLeft
          (yoneda.map ((Over.post (X := B.obj hS) B.inclusion).map f)) =
      yoneda.map f ≫ (pointsIsoYoneda (Over.post (X := B.obj hS) B.inclusion) U').inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← pointsIsoYoneda_naturality, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- The induced morphism of quotient sheaves commutes with the two quotient maps. -/
@[reassoc]
theorem quotientMap_comp_quotientHom {R U R' U' : BigFppfOver B S hS} (s t : R ⟶ U)
    (s' t' : R' ⟶ U') (r : R ⟶ R') (f : U ⟶ U') (hs : r ≫ s' = s ≫ f)
    (ht : r ≫ t' = t ≫ f) :
    quotientMap B S hS s t ≫ quotientHom B S hS s t s' t' r f hs ht =
      yoneda.map f ≫ quotientMap B S hS s' t' := by
  rw [quotientMap_eq_pointsIsoYoneda_inv, quotientMap_eq_pointsIsoYoneda_inv, Category.assoc,
    quotientHom, toQuotientSheaf_comp_quotientSheafMap, ← Category.assoc,
    pointsIsoYoneda_inv_naturality, Category.assoc]

/-- The induced morphism of quotient sheaves depends only on the map of base objects. -/
theorem quotientHom_congr {R U R' U' : BigFppfOver B S hS} (s t : R ⟶ U) (s' t' : R' ⟶ U')
    (r r' : R ⟶ R') (f f' : U ⟶ U') (hs : r ≫ s' = s ≫ f) (ht : r ≫ t' = t ≫ f)
    (hs' : r' ≫ s' = s ≫ f') (ht' : r' ≫ t' = t ≫ f') (hf : f = f') :
    quotientHom B S hS s t s' t' r f hs ht = quotientHom B S hS s t s' t' r' f' hs' ht' := by
  unfold quotientHom
  rw [quotientSheafMap_eq_of_obj_eq (BigFppfOver.topology B S hS)
    (Over.post (X := B.obj hS) B.inclusion) (relation B S hS s t) (relation B S hS s' t')
    _ ((Over.post (X := B.obj hS) B.inclusion).map r') _
    ((Over.post (X := B.obj hS) B.inclusion).map f') _ _
    (relation_source_comp B S hS s t s' t' r' f' hs')
    (relation_target_comp B S hS s t s' t' r' f' ht') (by rw [hf])]

/-- The induced morphisms of quotient sheaves compose. -/
theorem quotientHom_comp {R₀ U₀ R₁ U₁ R₂ U₂ : BigFppfOver B S hS} (s₀ t₀ : R₀ ⟶ U₀)
    (s₁ t₁ : R₁ ⟶ U₁) (s₂ t₂ : R₂ ⟶ U₂) (r₀ : R₀ ⟶ R₁) (f₀ : U₀ ⟶ U₁)
    (hs₀ : r₀ ≫ s₁ = s₀ ≫ f₀) (ht₀ : r₀ ≫ t₁ = t₀ ≫ f₀) (r₁ : R₁ ⟶ R₂) (f₁ : U₁ ⟶ U₂)
    (hs₁ : r₁ ≫ s₂ = s₁ ≫ f₁) (ht₁ : r₁ ≫ t₂ = t₁ ≫ f₁) :
    quotientHom B S hS s₀ t₀ s₁ t₁ r₀ f₀ hs₀ ht₀ ≫ quotientHom B S hS s₁ t₁ s₂ t₂ r₁ f₁ hs₁ ht₁ =
      quotientHom B S hS s₀ t₀ s₂ t₂ (r₀ ≫ r₁) (f₀ ≫ f₁)
        (by rw [Category.assoc, hs₁, ← Category.assoc, hs₀, Category.assoc])
        (by rw [Category.assoc, ht₁, ← Category.assoc, ht₀, Category.assoc]) := by
  unfold quotientHom
  rw [Sheaf.comp_hom', quotientSheafMap_comp]
  congr 1

/-- The identity morphism of a pair induces the identity of its quotient sheaf. -/
theorem quotientHom_id {R U : BigFppfOver B S hS} (s t : R ⟶ U) :
    quotientHom B S hS s t s t (𝟙 R) (𝟙 U) (by simp) (by simp) = 𝟙 _ := by
  unfold quotientHom
  rw [quotientSheafMap_eq_of_obj_eq (BigFppfOver.topology B S hS)
    (Over.post (X := B.obj hS) B.inclusion) (relation B S hS s t) (relation B S hS s t)
    _ (𝟙 _) _ (𝟙 _) _ _ (by rw [Category.id_comp, Category.comp_id])
    (by rw [Category.id_comp, Category.comp_id]) (CategoryTheory.Functor.map_id _ _),
    quotientSheafMap_id]
  rfl

/-- **Stacks 07S3, on the big fppf site.** A morphism `(r, f)` of étale equivalence relations
of the site whose square on the source maps is cartesian in schemes induces a cartesian square
of quotient maps: `U` is the fibre product of `U'` and `U/R` over `U'/R'`. -/
theorem isPullback_quotientMap {R U R' U' : BigFppfOver B S hS} (s t : R ⟶ U)
    (s' t' : R' ⟶ U') [IsEtaleEquivalenceRelation (relation B S hS s t)]
    [IsEtaleEquivalenceRelation (relation B S hS s' t')]
    (r : R ⟶ R') (f : U ⟶ U') (hs : r ≫ s' = s ≫ f) (ht : r ≫ t' = t ≫ f)
    (hcart : IsPullback ((BigFppfOver.toScheme B S hS).map r)
      ((BigFppfOver.toScheme B S hS).map s) ((BigFppfOver.toScheme B S hS).map s')
      ((BigFppfOver.toScheme B S hS).map f)) :
    IsPullback (quotientMap B S hS s t) (yoneda.map f)
      (quotientHom B S hS s t s' t' r f hs ht) (quotientMap B S hS s' t') := by
  have hcart' := isPullback_post_of_isPullback_toScheme hs hcart
  rw [← relation_source B S hS s t, ← relation_source B S hS s' t'] at hcart'
  have h := isPullback_toQuotientSheaf_of_subcanonical (BigFppfOver.topology B S hS)
    (Over.post (X := B.obj hS) B.inclusion) (relation B S hS s t) (relation B S hS s' t')
    ((Over.post (X := B.obj hS) B.inclusion).map r)
    ((Over.post (X := B.obj hS) B.inclusion).map f)
    (relation_source_comp B S hS s t s' t' r f hs)
    (relation_target_comp B S hS s t s' t' r f ht) hcart'
  refine h.of_iso (pointsIsoYoneda _ U) (Iso.refl _) (pointsIsoYoneda _ U') (Iso.refl _)
    ?_ ?_ ?_ ?_
  · rw [quotientMap_eq_pointsIsoYoneda_inv]; simp
  · exact pointsIsoYoneda_naturality _ f
  · simp [quotientHom]
  · rw [quotientMap_eq_pointsIsoYoneda_inv]; simp

/-- **Affineness of the induced morphism of quotients.** In the situation of
`AlgebraicGeometry.Space.isPullback_quotientMap`, if the map of base objects is affine then so
is the induced morphism of quotient sheaves: its base change along the surjective étale
quotient map of the target is the given affine morphism (Stacks 03WG). -/
theorem isAffineHom_quotientHom {R U R' U' : BigFppfOver B S hS} (s t : R ⟶ U)
    (s' t' : R' ⟶ U') [IsEtaleEquivalenceRelation (relation B S hS s t)]
    [IsEtaleEquivalenceRelation (relation B S hS s' t')]
    (r : R ⟶ R') (f : U ⟶ U') (hs : r ≫ s' = s ≫ f) (ht : r ≫ t' = t ≫ f)
    (hcart : IsPullback ((BigFppfOver.toScheme B S hS).map r)
      ((BigFppfOver.toScheme B S hS).map s) ((BigFppfOver.toScheme B S hS).map s')
      ((BigFppfOver.toScheme B S hS).map f))
    (hf : _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map f)) :
    IsAffineHom B S hS (quotientHom B S hS s t s' t' r f hs ht) := by
  have sq := isPullback_quotientMap B S hS s t s' t' r f hs ht hcart
  refine ((isAffineHom_tfae_of_isAlgebraicSpace B S hS (quotientHom B S hS s t s' t' r f hs ht)
    (isAlgebraicSpace_quotient_unconditional B S hS s t)
    (isAlgebraicSpace_quotient_unconditional B S hS s' t')).out 4 2).mp ?_
  refine ⟨U', quotientMap B S hS s' t',
      isSurjective_of_presheafSurjective B S hS _
        (quotientMap_surjective_unconditional B S hS s' t'),
      isEtale_of_presheaf_etale B S hS (quotientMap_etale_unconditional B S hS s' t'), ?_⟩
  refine IsAffineHom.of_isPullback (f := yoneda.map f) (g := 𝟙 _)
    (k := sq.isoPullback.inv) ?_ (isAffineHom_yoneda_map_of_isAffineHom f hf)
  exact IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, IsPullback.isoPullback_inv_snd]⟩

end

section LimitBaseChange

variable {I : Type u} [Category.{u} I] [IsCofiltered I]

/-- The cone over the stages above `j` of a cartesian inverse system of representables, induced
by a point of the base change of the limit of the target system. -/
@[simps]
noncomputable def cartesianLiftCone (Q : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (P : I ⥤ BigFppfOver B S hS) (α : P ⋙ yoneda ⟶ Q)
    (hα : ∀ {i j : I} (g : i ⟶ j),
      IsPullback (α.app i) (yoneda.map (P.map g)) (Q.map g) (α.app j))
    (j : I) (W : PullbackCone (limit.π Q j) (α.app j)) :
    Cone (Over.forget j ⋙ P ⋙ yoneda) where
  pt := W.pt
  π :=
    { app := fun k => (hα k.hom).lift (W.fst ≫ limit.π Q k.left) W.snd (by
        rw [Category.assoc, limit.w, W.condition])
      naturality := fun k k' f => by
        dsimp
        rw [Category.id_comp]
        apply (hα k'.hom).hom_ext
        · have hn := α.naturality f.left
          dsimp at hn
          rw [IsPullback.lift_fst, Category.assoc, hn, ← Category.assoc, IsPullback.lift_fst,
            Category.assoc, limit.w]
        · rw [IsPullback.lift_snd, Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
            Over.w f, IsPullback.lift_snd] }

/-- **A cartesian inverse system of representables over an inverse system of presheaves.** Let
`α : P ⋙ yoneda ⟶ Q` be a morphism from an inverse system of objects of the site to an inverse
system of presheaves all of whose naturality squares are cartesian, and let `c` be a limit cone
of `P`. Then the limit of `P` is the base change of the limit of `Q` along `α_j`, for every
stage `j`. -/
theorem isPullback_limitLift_of_cartesian (Q : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (P : I ⥤ BigFppfOver B S hS) (α : P ⋙ yoneda ⟶ Q)
    (hα : ∀ {i j : I} (g : i ⟶ j),
      IsPullback (α.app i) (yoneda.map (P.map g)) (Q.map g) (α.app j))
    (c : Cone P) (hc : IsLimit c) (j : I) :
    IsPullback (limit.lift Q ((Cone.postcompose α).obj (yoneda.mapCone c)))
      (yoneda.map (c.π.app j)) (limit.π Q j) (α.app j) := by
  let φ : yoneda.obj c.pt ⟶ limit Q := limit.lift Q ((Cone.postcompose α).obj (yoneda.mapCone c))
  have hφ : ∀ k, φ ≫ limit.π Q k = yoneda.map (c.π.app k) ≫ α.app k := fun k => limit.lift_π _ _
  -- the limit cone of `P ⋙ yoneda`, restricted to the stages over `j`
  have hc' : IsLimit ((yoneda.mapCone c).whisker (Over.forget j)) :=
    (Functor.Initial.isLimitWhiskerEquiv (Over.forget j) _).symm (isLimitOfPreserves yoneda hc)
  refine IsPullback.of_isLimit (c := PullbackCone.mk φ (yoneda.map (c.π.app j)) (hφ j)) ?_
  let lift : ∀ W : PullbackCone (limit.π Q j) (α.app j), W.pt ⟶ yoneda.obj c.pt :=
    fun W => hc'.lift (cartesianLiftCone B S hS Q P α hα j W)
  have hlift : ∀ (W : PullbackCone (limit.π Q j) (α.app j)) (k : Over j),
      lift W ≫ yoneda.map (c.π.app k.left) =
      (hα k.hom).lift (W.fst ≫ limit.π Q k.left) W.snd
        (by rw [Category.assoc, limit.w, W.condition]) :=
    fun W k => hc'.fac (cartesianLiftCone B S hS Q P α hα j W) k
  refine PullbackCone.IsLimit.mk _ lift ?_ ?_ ?_
  · intro W
    apply limit.hom_ext
    intro k
    let M : Over j := Over.mk (IsCofiltered.minToRight k j)
    have hM := hlift W M
    have hn := α.naturality (IsCofiltered.minToLeft k j)
    dsimp at hn
    have e1 : φ ≫ limit.π Q k = yoneda.map (c.π.app M.left) ≫ α.app M.left ≫
        Q.map (IsCofiltered.minToLeft k j) := by
      rw [hφ, ← c.w (IsCofiltered.minToLeft k j), Functor.map_comp, Category.assoc, hn]
      rfl
    rw [Category.assoc, e1, ← Category.assoc, ← Category.assoc, hM, IsPullback.lift_fst,
      Category.assoc, limit.w]
  · intro W
    refine (hlift W (Over.mk (𝟙 j))).trans ?_
    simpa using (hα (𝟙 j)).lift_snd (W.fst ≫ limit.π Q j) W.snd
      (by rw [Category.assoc, limit.w, W.condition])
  · intro W m hm₁ hm₂
    apply hc'.hom_ext
    intro k
    refine Eq.trans ?_ (hlift W k).symm
    apply (hα k.hom).hom_ext
    · dsimp at hm₁ ⊢
      rw [IsPullback.lift_fst, Category.assoc, ← hφ, ← Category.assoc, hm₁]
    · dsimp at hm₂ ⊢
      rw [IsPullback.lift_snd, Category.assoc, ← Functor.map_comp, Cone.w, hm₂]

end LimitBaseChange

section RelationSystem

variable [HasSheafify (BigFppfOver.topology B S hS) (Type u)]

/-- **An inverse system of étale equivalence relations on objects of the site with cartesian
source squares.** Over an index category `J`, a system `obj` of objects of the site with a
system `rel` of relations on it, given by the source and target maps `s, t : rel ⟶ obj`, such
that every stage is an étale equivalence relation and every transition square on the source
maps is cartesian in schemes. This is the shape of the systems `(V_i, R_i)` constructed in the
proof of Stacks 07SU. -/
structure EtaleRelationSystem (J : Type u) [Category.{u} J] where
  /-- The objects on which the relations live. -/
  obj : J ⥤ BigFppfOver B S hS
  /-- The relations. -/
  rel : J ⥤ BigFppfOver B S hS
  /-- The source maps. -/
  s : rel ⟶ obj
  /-- The target maps. -/
  t : rel ⟶ obj
  /-- Every stage is an étale equivalence relation. -/
  isEtaleEquivalenceRelation (j : J) :
    IsEtaleEquivalenceRelation (relation B S hS (s.app j) (t.app j))
  /-- The transition squares on the source maps are cartesian in schemes. -/
  isPullback_s {i j : J} (g : i ⟶ j) :
    IsPullback ((BigFppfOver.toScheme B S hS).map (rel.map g))
      ((BigFppfOver.toScheme B S hS).map (s.app i)) ((BigFppfOver.toScheme B S hS).map (s.app j))
      ((BigFppfOver.toScheme B S hS).map (obj.map g))

namespace EtaleRelationSystem

variable {B S hS} {J : Type u} [Category.{u} J] (E : EtaleRelationSystem B S hS J)

attribute [instance] isEtaleEquivalenceRelation

/-- The inverse system of quotients `obj_j / rel_j`. -/
noncomputable def quotient : J ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u where
  obj j := (Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion)
    (relation B S hS (E.s.app j) (E.t.app j))).obj
  map g := quotientHom B S hS _ _ _ _ (E.rel.map g) (E.obj.map g) (E.s.naturality g)
    (E.t.naturality g)
  map_id j := by
    rw [quotientHom_congr B S hS _ _ _ _ _ (𝟙 _) _ (𝟙 _) _ _ (by simp) (by simp)
      (CategoryTheory.Functor.map_id _ _), quotientHom_id]
  map_comp g h := by
    rw [quotientHom_comp]
    exact quotientHom_congr B S hS _ _ _ _ _ _ _ _ _ _ _ _ (CategoryTheory.Functor.map_comp _ _ _)

/-- The stages of the quotient system. -/
theorem quotient_obj (j : J) : E.quotient.obj j =
    (Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion)
      (relation B S hS (E.s.app j) (E.t.app j))).obj := rfl

/-- The transition morphisms of the quotient system. -/
theorem quotient_map {i j : J} (g : i ⟶ j) : E.quotient.map g =
    quotientHom B S hS _ _ _ _ (E.rel.map g) (E.obj.map g) (E.s.naturality g)
      (E.t.naturality g) := rfl

/-- The quotient maps `obj_j ⟶ obj_j / rel_j`, as a morphism of inverse systems. -/
@[simps]
noncomputable def toQuotient : E.obj ⋙ yoneda ⟶ E.quotient where
  app j := quotientMap B S hS (E.s.app j) (E.t.app j)
  naturality _ _ g := (quotientMap_comp_quotientHom B S hS _ _ _ _ _ _ (E.s.naturality g)
    (E.t.naturality g)).symm

/-- **Stacks 07S3 for the system.** The transition squares of the quotient maps are
cartesian. -/
theorem isPullback_toQuotient {i j : J} (g : i ⟶ j) :
    IsPullback (E.toQuotient.app i) (yoneda.map (E.obj.map g)) (E.quotient.map g)
      (E.toQuotient.app j) :=
  isPullback_quotientMap B S hS _ _ _ _ _ _ (E.s.naturality g) (E.t.naturality g)
    (E.isPullback_s g)

/-- The transition morphisms of the quotient system are affine as soon as those of `obj` are. -/
theorem isAffineHom_quotient_map
    (hobj : ∀ {i j : J} (g : i ⟶ j),
      _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map (E.obj.map g)))
    {i j : J} (g : i ⟶ j) : IsAffineHom B S hS (E.quotient.map g) :=
  isAffineHom_quotientHom B S hS _ _ _ _ _ _ (E.s.naturality g) (E.t.naturality g)
    (E.isPullback_s g) (hobj g)

/-- Every stage of the quotient system is an algebraic space (Stacks 02WW). -/
theorem isAlgebraicSpace_quotient_obj (j : J) : IsAlgebraicSpace B S hS (E.quotient.obj j) :=
  isAlgebraicSpace_quotient_unconditional B S hS _ _

section Limit

variable [IsCofiltered J] (cV : Cone E.obj) (hV : IsLimit cV) (cR : Cone E.rel)
  (hR : IsLimit cR) (sL tL : cR.pt ⟶ cV.pt)
  (hs : ∀ j, sL ≫ cV.π.app j = cR.π.app j ≫ E.s.app j)
  (ht : ∀ j, tL ≫ cV.π.app j = cR.π.app j ≫ E.t.app j)

/-- The map from the limit of the objects to the limit of the quotient system. -/
noncomputable def limitToQuotient : yoneda.obj cV.pt ⟶ limit E.quotient :=
  limit.lift E.quotient ((Cone.postcompose E.toQuotient).obj (yoneda.mapCone cV))

omit [IsCofiltered J] in
/-- The `j`-th component of `limitToQuotient` is the projection `cV.pt ⟶ obj_j` followed by the
quotient map `obj_j ⟶ obj_j / rel_j`. -/
@[reassoc (attr := simp)]
theorem limitToQuotient_π (j : J) :
    E.limitToQuotient cV ≫ limit.π E.quotient j =
      yoneda.map (cV.π.app j) ≫ E.toQuotient.app j :=
  limit.lift_π _ _

include hV in
/-- The limit of the objects is the base change of the limit of the quotients along each
quotient map. -/
theorem isPullback_limitToQuotient (j : J) :
    IsPullback (E.limitToQuotient cV) (yoneda.map (cV.π.app j)) (limit.π E.quotient j)
      (E.toQuotient.app j) :=
  isPullback_limitLift_of_cartesian B S hS E.quotient E.obj E.toQuotient
    (fun g => E.isPullback_toQuotient g) cV hV j

include hV hR hs ht in
/-- **The kernel pair of the limit of the quotient maps is the limit of the relations.** -/
theorem isPullback_limitToQuotient_kernelPair :
    IsPullback (yoneda.map tL) (yoneda.map sL) (E.limitToQuotient cV) (E.limitToQuotient cV) := by
  have hk : ∀ j, IsPullback (yoneda.map (E.t.app j)) (yoneda.map (E.s.app j))
      (E.toQuotient.app j) (E.toQuotient.app j) := fun j =>
    quotientMap_isPullback B S hS (E.s.app j) (E.t.app j)
  have hnat : ∀ (η : E.rel ⟶ E.obj) {i j : J} (g : i ⟶ j),
      yoneda.map (E.rel.map g) ≫ yoneda.map (η.app j) =
        yoneda.map (η.app i) ≫ yoneda.map (E.obj.map g) := fun η i j g => by
    rw [← Functor.map_comp, ← Functor.map_comp, η.naturality]
  let liftCone : PullbackCone (E.limitToQuotient cV) (E.limitToQuotient cV) →
      Cone (E.rel ⋙ yoneda) := fun W =>
    { pt := W.pt
      π :=
        { app := fun j => (hk j).lift (W.fst ≫ yoneda.map (cV.π.app j))
            (W.snd ≫ yoneda.map (cV.π.app j)) (by
              rw [Category.assoc, Category.assoc, ← limitToQuotient_π, ← Category.assoc,
                W.condition, Category.assoc])
          naturality := fun i j g => by
            dsimp
            rw [Category.id_comp]
            apply (hk j).hom_ext
            · rw [IsPullback.lift_fst]
              simp only [Category.assoc, hnat E.t, IsPullback.lift_fst_assoc]
              rw [← Functor.map_comp, Cone.w]
            · rw [IsPullback.lift_snd]
              simp only [Category.assoc, hnat E.s, IsPullback.lift_snd_assoc]
              rw [← Functor.map_comp, Cone.w] } }
  refine ⟨⟨?_⟩, ⟨PullbackCone.IsLimit.mk _ (fun W => (isLimitOfPreserves yoneda hR).lift
    (liftCone W)) ?_ ?_ ?_⟩⟩
  · apply limit.hom_ext
    intro j
    simp only [Category.assoc, limitToQuotient_π, ← Functor.map_comp_assoc, ht, hs]
    simp only [Functor.map_comp, Category.assoc, (hk j).w]
  · intro W
    apply (isLimitOfPreserves yoneda hV).hom_ext
    intro j
    have := (isLimitOfPreserves yoneda hR).fac (liftCone W) j
    dsimp at this ⊢
    rw [Category.assoc, ← Functor.map_comp, ht, Functor.map_comp, ← Category.assoc, this,
      IsPullback.lift_fst]
  · intro W
    apply (isLimitOfPreserves yoneda hV).hom_ext
    intro j
    have := (isLimitOfPreserves yoneda hR).fac (liftCone W) j
    dsimp at this ⊢
    rw [Category.assoc, ← Functor.map_comp, hs, Functor.map_comp, ← Category.assoc, this,
      IsPullback.lift_snd]
  · intro W m hm₁ hm₂
    apply (isLimitOfPreserves yoneda hR).hom_ext
    intro j
    rw [(isLimitOfPreserves yoneda hR).fac]
    apply (hk j).hom_ext
    · dsimp
      rw [IsPullback.lift_fst, Category.assoc, ← Functor.map_comp, ← ht, Functor.map_comp,
        ← Category.assoc, hm₁]
    · dsimp
      rw [IsPullback.lift_snd, Category.assoc, ← Functor.map_comp, ← hs, Functor.map_comp,
        ← Category.assoc, hm₂]

include hV in
/-- The map from the limit of the objects to the limit of the quotients is surjective and étale
after every representable base change: it is a base change of a quotient map. -/
theorem limitToQuotient_surjective_etale :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (E.limitToQuotient cV) ∧
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (E.limitToQuotient cV) := by
  obtain ⟨j⟩ := IsCofiltered.nonempty (C := J)
  have h := (E.isPullback_limitToQuotient cV hV j).flip
  exact ⟨(MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback h
      (quotientMap_surjective_unconditional B S hS (E.s.app j) (E.t.app j)),
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback h
      (quotientMap_etale_unconditional B S hS (E.s.app j) (E.t.app j))⟩

include hV hR hs ht in
/-- **The quotient of the limit relation is the limit of the quotients.** If `f` is a
surjective étale atlas of a sheaf `X` from the limit of the objects whose kernel pair is the
limit of the relations, then `X` is the limit of the quotient system, compatibly with `f`.
This is the closing step of the proof of Stacks 07SU. -/
theorem exists_iso_limit_quotient {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X) (f : yoneda.obj cV.pt ⟶ X)
    (hf : IsPullback (yoneda.map tL) (yoneda.map sL) f f)
    (hsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f)
    (hetale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f) :
    ∃ e : X ≅ limit E.quotient, f ≫ e.hom = E.limitToQuotient cV := by
  classical
  let J' := BigFppfOver.topology B S hS
  have hrep : ∀ T : BigFppfOver B S hS, Presheaf.IsSheaf J' (yoneda.obj T) := fun T =>
    (isSheaf_iff_isSheaf_of_type J' (yoneda.obj T)).mpr
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (J := J') _)
  have hLsh : Presheaf.IsSheaf J' (limit E.quotient) :=
    isSheaf_limit B S hS E.quotient fun j => (Stacks.Groupoids.quotientSheaf J'
      (Over.post B.inclusion) (relation B S hS (E.s.app j) (E.t.app j))).property
  let RF : Sheaf J' (Type u) := ⟨yoneda.obj cR.pt, hrep _⟩
  let UF : Sheaf J' (Type u) := ⟨yoneda.obj cV.pt, hrep _⟩
  let XF : Sheaf J' (Type u) := ⟨X, hX⟩
  let LF : Sheaf J' (Type u) := ⟨limit E.quotient, hLsh⟩
  let sf : RF ⟶ UF := ⟨yoneda.map tL⟩
  let tf : RF ⟶ UF := ⟨yoneda.map sL⟩
  let ff : UF ⟶ XF := ⟨f⟩
  let φf : UF ⟶ LF := ⟨E.limitToQuotient cV⟩
  have hK := E.isPullback_limitToQuotient_kernelPair cV hV cR hR sL tL hs ht
  have w : sf ≫ ff = tf ≫ ff := Sheaf.hom_ext hf.w
  have w' : sf ≫ φf = tf ≫ φf := Sheaf.hom_ext hK.w
  have hker : ∀ {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : yoneda.obj cV.pt ⟶ P),
      IsPullback (yoneda.map tL) (yoneda.map sL) g g →
      ∀ ⦃T : BigFppfOver B S hS⦄ (x y : (yoneda.obj cV.pt).obj (op T)),
      g.app (op T) x = g.app (op T) y →
      ∃ r : (yoneda.obj cR.pt).obj (op T),
        (yoneda.map tL).app (op T) r = x ∧ (yoneda.map sL).app (op T) r = y := by
    intro P g hg T x y hxy
    have hxy' : yoneda.map x ≫ g = yoneda.map y ≫ g := by
      apply yonedaEquiv.injective
      simpa only [yonedaEquiv_comp, yonedaEquiv_yoneda_map] using hxy
    refine ⟨yonedaEquiv (hg.lift (yoneda.map x) (yoneda.map y) hxy'), ?_, ?_⟩
    · rw [← yonedaEquiv_comp, hg.lift_fst, yonedaEquiv_yoneda_map]
    · rw [← yonedaEquiv_comp, hg.lift_snd, yonedaEquiv_yoneda_map]
  obtain ⟨h1⟩ : Nonempty (IsColimit (Cofork.ofπ ff w)) :=
    Sheaf.nonempty_isColimitCoforkOfKernelPair sf tf ff w (hker f hf)
      (isLocallySurjective_of_surjective_etale B S hS f hsurj hetale)
  obtain ⟨hφs, hφe⟩ := E.limitToQuotient_surjective_etale cV hV
  obtain ⟨h2⟩ : Nonempty (IsColimit (Cofork.ofπ φf w')) :=
    Sheaf.nonempty_isColimitCoforkOfKernelPair sf tf φf w' (hker _ hK)
      (isLocallySurjective_of_surjective_etale B S hS _ hφs hφe)
  refine ⟨(sheafToPresheaf J' (Type u)).mapIso (h1.coconePointUniqueUpToIso h2), ?_⟩
  exact congrArg InducedCategory.Hom.hom
    (h1.comp_coconePointUniqueUpToIso_hom h2 WalkingParallelPair.one)

end Limit

end EtaleRelationSystem

end RelationSystem

section QuasiSeparated

variable [HasSheafify (BigFppfOver.topology B S hS) (Type u)] (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **The quotient of an étale equivalence relation with quasi-compact relation scheme on a
quasi-separated scheme is quasi-separated** (Stacks 07S4): the kernel pair of the quotient map
is the relation, whose projections are quasi-compact. -/
theorem isAbsolutelyQuasiSeparated_quotient {R U : BigFppfOver B S hS} (s t : R ⟶ U)
    [IsEtaleEquivalenceRelation (relation B S hS s t)]
    (hU : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj U))
    (hR : CompactSpace ((BigFppfOver.toScheme B S hS).obj R)) :
    IsAbsolutelyQuasiSeparated B S hS hZ
      (Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion)
        (relation B S hS s t)).obj := by
  refine isQuasiSeparated_of_etaleAtlas_quasiCompact_projection B S hS hZ _
    (isAlgebraicSpace_quotient_unconditional B S hS s t)
    ⟨U, quotientMap B S hS s t, hU, quotientMap_surjective_unconditional B S hS s t,
      quotientMap_etale_unconditional B S hS s t, Or.inl ?_⟩
  have sq := quotientMap_isPullback B S hS s t
  have hqc : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@QuasiCompact.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (yoneda.map t) :=
    (presheaf_yoneda_map_iff B S hS (P := @QuasiCompact.{u}) inferInstance t).mpr
      (quasiCompact_of_compactSpace _)
  have e : pullback.fst (quotientMap B S hS s t) (quotientMap B S hS s t) =
      sq.isoPullback.inv ≫ yoneda.map t := (sq.isoPullback_inv_fst).symm
  rw [e]
  exact MorphismProperty.RespectsIso.precomp _ sq.isoPullback.inv _ hqc

end QuasiSeparated

section FiniteTypeOverIntegers

variable (hZ : B.Contains (⊤_ Scheme.{u}))

/-- Relocalization of presheaves along the identity of the base is the identity functor: it is
left adjoint to restriction along the identity, which is the identity functor. -/
noncomputable def relocalizePresheafFunctorIdIso {C : Type (u + 1)} [Category.{u} C] (U : C) :
    OverShriek.relocalizePresheafFunctor (𝟙 U) ≅ 𝟭 ((Over U)ᵒᵖ ⥤ Type u) :=
  Adjunction.leftAdjointUniq (OverShriek.relocalizeAdjunction (𝟙 U))
    (Adjunction.id.ofNatIsoRight
      ((Functor.whiskeringLeft (Over U)ᵒᵖ (Over U)ᵒᵖ (Type u)).mapIso
        (NatIso.op (Over.mapId U)).symm).symm)

/-- The structure morphism of the terminal object of the site of `Spec ℤ` is its identity. -/
theorem terminalStructureMap_eq_id :
    (⟨terminal.from (⊤_ Scheme.{u})⟩ : B.obj hZ ⟶ B.obj hZ) = 𝟙 (B.obj hZ) := by
  ext
  exact terminal.hom_ext _ _

/-- **A presheaf over `Spec ℤ`, viewed over `Spec ℤ`, is itself**: the view is relocalization
along the structure morphism of the terminal scheme, which is its identity. -/
noncomputable def viewOverIntegersTopIso (F : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u) :
    viewOverIntegers B (⊤_ Scheme.{u}) hZ hZ F ≅ F :=
  eqToIso (congrArg (fun m => (OverShriek.relocalizePresheafFunctor m).obj F)
      (terminalStructureMap_eq_id B hZ)) ≪≫
    (relocalizePresheafFunctorIdIso (B.obj hZ)).app F

/-- The presheaf represented by the identity of the base is terminal. -/
noncomputable def yonedaOverIdIsoTerminal (T : Scheme.{u}) (hT : B.Contains T) :
    yoneda.obj (Over.mk (𝟙 (B.obj hT))) ≅ ⊤_ ((BigFppfOver B T hT)ᵒᵖ ⥤ Type u) :=
  ((Over.mkIdTerminal (X := B.obj hT)).isTerminalObj yoneda _).uniqueUpToIso terminalIsTerminal

variable [HasSheafify (BigFppfOver.topology B (⊤_ Scheme.{u}) hZ) (Type u)]

/-- **The quotient of an étale equivalence relation on a quasi-compact scheme locally of finite
type over `Spec ℤ` is of finite type over `Spec ℤ`** (Stacks 040Y, 040W): the quotient map is a
surjective étale chart along which the structure morphism is the structure morphism of the
scheme, and the quotient is the image of a quasi-compact scheme. -/
theorem isFiniteType_quotient {R U : BigFppfOver B (⊤_ Scheme.{u}) hZ} (s t : R ⟶ U)
    [IsEtaleEquivalenceRelation (relation B (⊤_ Scheme.{u}) hZ s t)]
    (hU : CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj U))
    (hlft : LocallyOfFiniteType
      (terminal.from ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj U))) :
    IsFiniteType B (⊤_ Scheme.{u}) hZ (terminal.from (viewOverIntegers B (⊤_ Scheme.{u}) hZ hZ
      (Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B (⊤_ Scheme.{u}) hZ)
        (Over.post B.inclusion) (relation B (⊤_ Scheme.{u}) hZ s t)).obj)) := by
  set X := (Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B (⊤_ Scheme.{u}) hZ)
    (Over.post B.inclusion) (relation B (⊤_ Scheme.{u}) hZ s t)).obj
  have hX : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ X :=
    isAlgebraicSpace_quotient_unconditional B (⊤_ Scheme.{u}) hZ s t
  have hXqc : IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ X :=
    isQuasiCompactSpace_of_surjective_etale B (⊤_ Scheme.{u}) hZ _
      (quotientMap_surjective_unconditional B (⊤_ Scheme.{u}) hZ s t)
      (isEtale_of_presheaf_etale B (⊤_ Scheme.{u}) hZ
        (quotientMap_etale_unconditional B (⊤_ Scheme.{u}) hZ s t))
      (isQuasiCompactSpace_yoneda B (⊤_ Scheme.{u}) hZ U hU)
  let e := viewOverIntegersTopIso B hZ X
  let τ := yonedaOverIdIsoTerminal B (⊤_ Scheme.{u}) hZ
  have hterm : terminal.from (viewOverIntegers B (⊤_ Scheme.{u}) hZ hZ X) =
      e.hom ≫ terminal.from X := terminal.hom_ext _ _
  have _ : MorphismProperty.ContainsIdentities (@Etale.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsMultiplicative.toContainsIdentities
  have _ : MorphismProperty.RespectsIso (@Etale.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hτ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)).presheaf τ.hom :=
    presheaf_of_isIso B (⊤_ Scheme.{u}) hZ (MorphismProperty.RespectsIso.inverseImage _ _)
      (fun U => show Etale ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (𝟙 U)) by
        rw [CategoryTheory.Functor.map_id]
        exact MorphismProperty.id_mem (@Etale.{u} : MorphismProperty Scheme.{u}) _) τ.hom
  rw [hterm]
  refine ⟨?_, ?_⟩
  · rw [← hterm, isLocallyOfFiniteType_terminal_iff_of_iso B (⊤_ Scheme.{u}) hZ e]
    refine isLocallyOfFiniteType_of_holdsOnSurjectiveEtaleChart B (⊤_ Scheme.{u}) hZ
      ⟨U, Over.mk (𝟙 (B.obj hZ)), quotientMap B (⊤_ Scheme.{u}) hZ s t, τ.hom,
        Over.homMk U.hom (by simp), quotientMap_etale_unconditional B (⊤_ Scheme.{u}) hZ s t,
        hτ,
        quotientMap_surjective_unconditional B (⊤_ Scheme.{u}) hZ s t,
        terminal.hom_ext _ _, ?_⟩
    have h : (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (Over.homMk U.hom (by simp) :
        U ⟶ Over.mk (𝟙 (B.obj hZ))) =
        terminal.from ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj U) :=
      terminal.hom_ext _ _
    rw [h]
    exact hlft
  · refine isQuasiCompact_isIso_comp B (⊤_ Scheme.{u}) hZ e.hom ?_
    refine isQuasiCompact_of_isQuasiCompactSpace_pullback_affine' B (⊤_ Scheme.{u}) hZ _ hX
      (isAlgebraicSpace_terminal B (⊤_ Scheme.{u}) hZ) fun Z g hZaff => ?_
    have hpb := isQuasiCompactSpace_pullback B (⊤_ Scheme.{u}) hZ hZ (terminal.from X ≫ τ.inv)
      (g ≫ τ.inv) hX (isAlgebraicSpace_yoneda B (⊤_ Scheme.{u}) hZ _) hXqc
      (isQuasiCompactSpace_yoneda_of_isAffine B (⊤_ Scheme.{u}) hZ Z hZaff)
      (isAbsolutelyQuasiSeparated_yoneda_of_isAffine B (⊤_ Scheme.{u}) hZ hZ _
        (inferInstanceAs (IsAffine (⊤_ Scheme.{u}))))
    have hsq : IsPullback (pullback.fst (terminal.from X) g) (pullback.snd (terminal.from X) g)
        (terminal.from X ≫ τ.inv) (g ≫ τ.inv) :=
      (IsPullback.of_hasPullback (terminal.from X) g).of_iso (Iso.refl _) (Iso.refl _)
        (Iso.refl _) τ.symm (by simp) (by simp) (by simp) (by simp)
    exact isQuasiCompactSpace_of_iso B (⊤_ Scheme.{u}) hZ hsq.isoPullback.symm hpb

end FiniteTypeOverIntegers

section Assembly

variable (hZ : B.Contains (⊤_ Scheme.{u}))
  [HasSheafify (BigFppfOver.topology B (⊤_ Scheme.{u}) hZ) (Type u)]

/-- **The conclusion of Stacks 07SU from an inverse system of étale equivalence relations.**
Let `I` be a directed set and `E` an inverse system over it of étale equivalence relations
`(V_i, R_i)` on objects of the big fppf site of `Spec ℤ`, with cartesian source squares, affine
transition morphisms `V_i ⟶ V_{i'}`, every `V_i` quasi-compact and locally of finite type over
`Spec ℤ`, and every `R_i` quasi-compact. Let `V = lim V_i` and `R = lim R_i` in schemes, with
the maps `R ⟶ V` induced by the source and target maps. If a sheaf `X` receives a surjective
étale morphism from `V` whose kernel pair is `R`, then `X` has a Noetherian approximation: it
is the limit of the quotients `V_i / R_i`. -/
theorem EtaleRelationSystem.hasNoetherianApproximation {I : Type u} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] (E : EtaleRelationSystem B (⊤_ Scheme.{u}) hZ Iᵒᵖ)
    (hobj : ∀ {i j : Iᵒᵖ} (g : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (E.obj.map g)))
    (hcpt : ∀ j, CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj (E.obj.obj j)))
    (hlft : ∀ j, LocallyOfFiniteType
      (terminal.from ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj (E.obj.obj j))))
    (hrel : ∀ j, CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj (E.rel.obj j)))
    (cV : Cone E.obj) (hV : IsLimit ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).mapCone cV))
    (cR : Cone E.rel) (hR : IsLimit ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).mapCone cR))
    (sL tL : cR.pt ⟶ cV.pt) (hs : ∀ j, sL ≫ cV.π.app j = cR.π.app j ≫ E.s.app j)
    (ht : ∀ j, tL ≫ cV.π.app j = cR.π.app j ≫ E.t.app j)
    {X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B (⊤_ Scheme.{u}) hZ) X)
    (f : yoneda.obj cV.pt ⟶ X) (hf : IsPullback (yoneda.map tL) (yoneda.map sL) f f)
    (hsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ))) f)
    (hetale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ))) f) :
    HasNoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ X := by
  have : IsConnected Iᵒᵖ := IsCofiltered.isConnected _
  have hV' := BigFppfOver.isLimit_of_isLimit_toScheme B (⊤_ Scheme.{u}) hZ hV
  have hR' := BigFppfOver.isLimit_of_isLimit_toScheme B (⊤_ Scheme.{u}) hZ hR
  obtain ⟨e, -⟩ := E.exists_iso_limit_quotient cV hV' cR hR' sL tL hs ht hX f hf hsurj hetale
  exact ⟨{
    I := I
    diagram := E.quotient
    isAlgebraicSpace := E.isAlgebraicSpace_quotient_obj
    isAffineHom_map := E.isAffineHom_quotient_map hobj
    isAbsolutelyQuasiSeparated := fun j =>
      isAbsolutelyQuasiSeparated_quotient B (⊤_ Scheme.{u}) hZ hZ _ _
        (quasiSeparatedSpace_of_locallyOfFiniteType_terminal _) (hrel j)
    isFiniteTypeOverIntegers := fun j => isFiniteType_quotient B hZ _ _ (hcpt j) (hlft j)
    π := (Functor.const Iᵒᵖ).map e.hom ≫ (limit.cone E.quotient).π
    isLimit := (limit.isLimit E.quotient).ofIsoLimit (Cone.ext e.symm (fun j => by simp)) }⟩

end Assembly

end AlgebraicGeometry.Space

end
