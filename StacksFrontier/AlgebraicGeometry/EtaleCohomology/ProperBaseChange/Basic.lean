module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ScalarExtension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.UniversalHomeomorphismInvariance
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.DerivedCategoryOfTorsionSheaves

/-!
# Étale cohomology after extending the ground field

For a scheme `X` over a field `k` and a field extension `k'/k`, the scalar extension
`X_{k'} = X ×_{Spec k} Spec k'` comes with a projection to `X`, and restriction along that
projection is a map on étale cohomology. This file builds the machinery that compares the two
cohomologies: the criterion for the restriction map to be bijective in terms of the induced map
on `Ext` in the derived category, the behaviour of that criterion under composition and under
isomorphism of functors, the transport of the torsion condition along an inverse image, and the
comparison of the inverse images of a composite.

## Main definitions

* `Stacks.EtaleCohomology.etaleCohomologyBaseChangeMap` is the canonical map on étale cohomology
  after extending the ground field, namely restriction along the scalar-extension projection.
* `Stacks.EtaleCohomology.IsBijectiveOnExt` is the condition that an exact functor is bijective
  on morphisms between the two shifted single complexes computing `Ext`.

## Main results

* `Stacks.EtaleCohomology.etaleCohomologyRestrictionMap_bijective_iff_isBijectiveOnExt`:
  restriction along a morphism of schemes is bijective exactly when its inverse image is
  bijective on the corresponding `Ext` groups.
* `Stacks.EtaleCohomology.isBijectiveOnExt_comp_iff`: for a composite of exact functors, the
  condition for the composite is equivalent to the condition for the first factor as soon as it
  holds for the second one on the images.
* `Stacks.EtaleCohomology.etaleAbelianInverseImageCompIso`: the inverse image of a composite is
  the composite of the inverse images.
* `Stacks.EtaleCohomology.torsionSheafProperty_inverseImage_of_isDenseSubsite`: the inverse
  image of a torsion abelian sheaf along a dense subsite inclusion of small étale sites is
  torsion.
* `Stacks.EtaleCohomology.isBijectiveOnExt_etaleAbelianInverseImage_of_isDenseSubsite`: for an
  equivalence of small étale sites the inverse image is bijective on the `Ext` groups computing
  étale cohomology.

## Implementation notes

The scalar extension and its projection are
`Stacks.EtaleCohomology.scalarExtension` and `Stacks.EtaleCohomology.scalarExtensionFst`, and
the cohomological map is `Stacks.EtaleCohomology.etaleCohomologyRestrictionMap`. Torsion is the
intrinsic local condition `Stacks.Torsion.torsionSheafProperty`.

Bijectivity of a map on `Ext` is not stable under replacing a functor by an isomorphic one if
stated through `Functor.mapExtAddHom`, because the two `Ext` groups then have different types.
`IsBijectiveOnExt` states it instead for the induced map on morphisms in the derived category,
where both sides are literally hom-sets of the same two objects; the lemmas
`isBijectiveOnExt_congr` and `isBijectiveOnExt_congr_obj` are the resulting invariance under
isomorphism of the functor and of its arguments, and
`mapExt_bijective_iff_mapDerivedCategory` is the translation back.

Transport of the torsion condition uses that the inverse image of a sheaf is the pushforward's
left adjoint applied to it, so an inverse image is, up to isomorphism, a sheaf whose pushforward
is the original one; torsion is a local condition and the site functor is a dense subsite
inclusion, so a covering sieve witnessing torsion downstairs pushes forward to one upstairs. In
particular only cover-density of the site functor is needed, never its essential surjectivity:
the sieve of all morphisms from images of the functor is covering, and torsion can be checked
after pulling back along it.

## References

* [Stacks Project, Tag 0A5E](https://stacks.math.columbia.edu/tag/0A5E)
* [Stacks Project, Tag 0DD7](https://stacks.math.columbia.edu/tag/0DD7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace Stacks.EtaleCohomology

universe u v w

/-- The canonical map on étale cohomology after extending the ground field, given by restriction
along the scalar-extension projection. Its target uses the usual inverse image on abelian
sheaves of the small étale site. -/
abbrev etaleCohomologyBaseChangeMap
    (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{max (u + 1) v}]
    [HasSheafify (smallEtaleTopology (scalarExtension k k' f))
      AddCommGrpCat.{max (u + 1) v}]
    [HasExt.{w} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{max (u + 1) v})]
    [HasExt.{w} (Sheaf (smallEtaleTopology (scalarExtension k k' f))
      AddCommGrpCat.{max (u + 1) v})]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{max (u + 1) v}) (q : ℕ) :
    Sheaf.H.{w} F q →+
      Sheaf.H.{w}
        ((Functor.sheafPullbackConstruction.sheafPullback
          (smallEtaleBaseChange (scalarExtensionFst k k' f))
          AddCommGrpCat.{max (u + 1) v} (smallEtaleTopology X)
          (smallEtaleTopology (scalarExtension k k' f))).obj F) q :=
  etaleCohomologyRestrictionMap.{u, v, w} (scalarExtensionFst k k' f) F q

section Ext

open Functor

universe w' u₁ u₂ u₃ v₁ v₂ v₃

attribute [local instance] HasDerivedCategory.standard
  Limits.comp_preservesFiniteLimits Limits.comp_preservesFiniteColimits

/-- Bijectivity of the map a functor induces on a hom-set only depends on the functor up to
isomorphism. -/
lemma map_bijective_iff_of_natIso {C : Type*} [Category C] {D : Type*} [Category D]
    {F G : C ⥤ D} (e : F ≅ G) (X Y : C) :
    Function.Bijective (F.map : (X ⟶ Y) → _) ↔
      Function.Bijective (G.map : (X ⟶ Y) → _) := by
  have h : G.map = (Iso.homCongr (e.app X) (e.app Y)) ∘ (F.map : (X ⟶ Y) → _) := by
    funext f
    change G.map f = (e.app X).inv ≫ F.map f ≫ (e.app Y).hom
    simpa only [Iso.app_hom, Iso.app_inv, Iso.inv_hom_id_app_assoc] using
      congrArg ((e.inv.app X) ≫ ·) (e.hom.naturality f).symm
  rw [h]
  exact (Function.Bijective.of_comp_iff' (Iso.homCongr _ _).bijective _).symm

/-- Bijectivity of the map a functor induces on a hom-set only depends on the source and target
up to isomorphism. -/
lemma map_bijective_iff_of_objIso {C : Type*} [Category C] {D : Type*} [Category D]
    (F : C ⥤ D) {X Y X' Y' : C} (a : X ≅ X') (b : Y ≅ Y') :
    Function.Bijective (F.map : (X ⟶ Y) → _) ↔
      Function.Bijective (F.map : (X' ⟶ Y') → _) := by
  have h : (F.map : (X' ⟶ Y') → _) =
      (Iso.homCongr (F.mapIso a) (F.mapIso b)) ∘ F.map ∘ (Iso.homCongr a b).symm := by
    funext f
    simp [Iso.homCongr, Functor.map_comp]
  rw [h, Function.Bijective.of_comp_iff' (Iso.homCongr _ _).bijective _]
  exact (Function.Bijective.of_comp_iff _ (Iso.homCongr a b).symm.bijective).symm

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]
  {E : Type u₃} [Category.{v₃} E] [Abelian E]

/-- The derived functor of an exact functor identifies the `n`-fold shift of the single complex
of `Y` with the `n`-fold shift of the single complex of `F.obj Y`. -/
private def mapDerivedCategoryShiftSingleIso (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (Y : C) (n : ℕ) :
    F.mapDerivedCategory.obj (((DerivedCategory.singleFunctor C 0).obj Y)⟦(n : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor D 0).obj (F.obj Y))⟦(n : ℤ)⟧ :=
  (F.mapDerivedCategory.commShiftIso (n : ℤ)).app ((DerivedCategory.singleFunctor C 0).obj Y) ≪≫
    (shiftFunctor _ (n : ℤ)).mapIso ((F.mapDerivedCategorySingleFunctor 0).app Y)

/-- The map an exact functor induces on `Ext` is bijective exactly when the induced map on
morphisms of shifted single complexes in the derived category is. -/
lemma mapExt_bijective_iff_mapDerivedCategory (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [HasExt.{w} C] [HasExt.{w'} D] (X Y : C) (n : ℕ) :
    Function.Bijective (F.mapExtAddHom X Y n) ↔
      Function.Bijective (F.mapDerivedCategory.map :
        ((DerivedCategory.singleFunctor C 0).obj X ⟶
          ((DerivedCategory.singleFunctor C 0).obj Y)⟦(n : ℤ)⟧) → _) := by
  let a := (F.mapDerivedCategorySingleFunctor 0).app X
  let b := mapDerivedCategoryShiftSingleIso F Y n
  have h : (F.mapExtAddHom X Y n : _ → _) =
      Abelian.Ext.homEquiv.symm ∘ (Iso.homCongr a b) ∘ F.mapDerivedCategory.map ∘
        Abelian.Ext.homEquiv := by
    funext x
    apply Abelian.Ext.homEquiv.injective
    change (x.mapExactFunctor F).hom = Abelian.Ext.homEquiv (Abelian.Ext.homEquiv.symm _)
    rw [Equiv.apply_symm_apply, Abelian.Ext.mapExactFunctor_hom]
    simp [Function.comp_def, Iso.homCongr, ShiftedHom.map, a, b, Category.assoc,
      mapDerivedCategoryShiftSingleIso]
  rw [h, Function.Bijective.of_comp_iff' Abelian.Ext.homEquiv.symm.bijective _,
    Function.Bijective.of_comp_iff' (Iso.homCongr a b).bijective _]
  exact Function.Bijective.of_comp_iff _ Abelian.Ext.homEquiv.bijective

/-- The derived functor of a composite of exact functors is the composite of their derived
functors. -/
def mapDerivedCategoryCompIso (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ (F ⋙ G).mapDerivedCategory := by
  let : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      (F.mapHomologicalComplex _ ⋙ G.mapHomologicalComplex _ ⋙ DerivedCategory.Q)
      (F.mapDerivedCategory ⋙ G.mapDerivedCategory) :=
    ⟨(Functor.associator _ _ _).symm ≪≫ isoWhiskerRight F.mapDerivedCategoryFactors _ ≪≫
      Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ G.mapDerivedCategoryFactors⟩
  exact Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) _ _ _ _
    ((Functor.associator _ _ _).symm ≪≫ isoWhiskerRight
      (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)) DerivedCategory.Q)

/-- Isomorphic exact functors have isomorphic derived functors. -/
def mapDerivedCategoryIsoOfNatIso {F G : C ⥤ D}
    [F.Additive] [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) :
    F.mapDerivedCategory ≅ G.mapDerivedCategory :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) _ _ _ _
    (isoWhiskerRight (NatIso.mapHomologicalComplex e (.up ℤ)) DerivedCategory.Q)

/-- An exact functor `F` *is bijective on `Ext` from `X` to `Y` in degree `n`* if the induced
map on morphisms from the single complex of `X` to the `n`-fold shift of the single complex of
`Y` is bijective. Stated in the derived category rather than through `Ext` so that it is visibly
invariant under isomorphism of `F`. -/
abbrev IsBijectiveOnExt (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (X Y : C) (n : ℕ) : Prop :=
  Function.Bijective (F.mapDerivedCategory.map :
    ((DerivedCategory.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.singleFunctor C 0).obj Y)⟦(n : ℤ)⟧) → _)

/-- `IsBijectiveOnExt` only depends on its two arguments up to isomorphism. -/
lemma isBijectiveOnExt_congr_obj (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {X Y X' Y' : C} (a : X ≅ X') (b : Y ≅ Y') (n : ℕ) :
    IsBijectiveOnExt F X Y n ↔ IsBijectiveOnExt F X' Y' n :=
  map_bijective_iff_of_objIso _ ((DerivedCategory.singleFunctor C 0).mapIso a)
    ((shiftFunctor _ (n : ℤ)).mapIso ((DerivedCategory.singleFunctor C 0).mapIso b))

/-- `IsBijectiveOnExt` only depends on the functor up to isomorphism. -/
lemma isBijectiveOnExt_congr {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G)
    (X Y : C) (n : ℕ) : IsBijectiveOnExt F X Y n ↔ IsBijectiveOnExt G X Y n :=
  map_bijective_iff_of_natIso (mapDerivedCategoryIsoOfNatIso e) _ _

/-- For a composite of exact functors, the composite is bijective on `Ext` exactly when the
first factor is, provided the second factor is bijective on `Ext` between the images. -/
lemma isBijectiveOnExt_comp_iff (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (X Y : C) (n : ℕ)
    (hG : IsBijectiveOnExt G (F.obj X) (F.obj Y) n) :
    IsBijectiveOnExt (F ⋙ G) X Y n ↔ IsBijectiveOnExt F X Y n := by
  have h := (map_bijective_iff_of_objIso G.mapDerivedCategory
    ((F.mapDerivedCategorySingleFunctor 0).app X)
    (mapDerivedCategoryShiftSingleIso F Y n)).mpr hG
  change Function.Bijective _ ↔ _
  rw [← map_bijective_iff_of_natIso (mapDerivedCategoryCompIso F G)]
  exact Function.Bijective.of_comp_iff' h _

end Ext

section Torsion

universe v₁ v₂ u₁ u₂

/-- A sheaf whose pushforward along a dense subsite inclusion is torsion is itself torsion.

Only cover-density of `G` is used, not essential surjectivity: being torsion is the local
condition that every section is locally killed by a positive integer, so it may be verified
after pulling back along the covering family of all morphisms from images of `G`. -/
lemma torsionSheafProperty_of_pushforward {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) [HasSheafify J AddCommGrpCat.{w}]
    [HasSheafify K AddCommGrpCat.{w}] (G : C ⥤ D)
    [G.IsContinuous J K] [G.IsDenseSubsite J K]
    (F : Sheaf K AddCommGrpCat.{w})
    (hF : Stacks.Torsion.torsionSheafProperty J
      ((G.sheafPushforwardContinuous AddCommGrpCat.{w} J K).obj F)) :
    Stacks.Torsion.torsionSheafProperty K F := by
  have := Functor.IsDenseSubsite.isCoverDense J K G
  intro U x
  let S : Sieve U :=
    { arrows := fun V f => ∃ n : ℕ, 0 < n ∧ n • F.obj.map f.op x = 0
      downward_closed := by
        rintro V W f ⟨n, hn, hx⟩ g
        refine ⟨n, hn, ?_⟩
        simpa using congrArg (F.obj.map g.op) hx }
  refine ⟨S, K.transitive (G.is_cover_of_isCoverDense K U) S ?_, fun _ _ hf => hf⟩
  rintro V' g ⟨⟨W, l, m, rfl⟩⟩
  rw [Sieve.pullback_comp]
  refine K.pullback_stable l ?_
  obtain ⟨R, hR, hRx⟩ := hF W (F.obj.map m.op x)
  apply K.superset_covering (S := R.functorPushforward G) _
    ((G.functorPushforward_mem_iff J K).mpr hR)
  rintro V f ⟨W', g', h, hg', rfl⟩
  obtain ⟨n, hn, hx⟩ := hRx W' g' hg'
  refine ⟨n, hn, ?_⟩
  change n • (F.obj.map (G.map g').op).hom ((F.obj.map m.op).hom x) = 0 at hx
  simpa using congrArg (F.obj.map h.op).hom hx

end Torsion

section Restriction

attribute [local instance] HasDerivedCategory.standard

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]

/-- Bijectivity of the restriction map on étale cohomology is bijectivity of the map the
inverse image induces on the corresponding `Ext` group. -/
lemma etaleCohomologyRestrictionMap_bijective_iff
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (q : ℕ) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w} f F q) ↔
    Function.Bijective ((etaleAbelianInverseImage.{u, v} f).mapExtAddHom
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj
        (AddCommGrpCat.of (ULift.{max (u + 1) v} ℤ))) F q) :=
  Function.Bijective.of_comp_iff'
    (ext_precomp_iso_bijective
      ((etaleAbelianInverseImageConstantIso.{u, v} f).app
        (AddCommGrpCat.of (ULift.{max (u + 1) v} ℤ))) q) _

/-- Bijectivity of the restriction map on étale cohomology, in the form used for comparing two
restrictions: the inverse image is bijective on the `Ext` group out of the constant integer
sheaf. -/
lemma etaleCohomologyRestrictionMap_bijective_iff_isBijectiveOnExt
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (q : ℕ) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w} f F q) ↔
    IsBijectiveOnExt (etaleAbelianInverseImage.{u, v} f)
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj
        (AddCommGrpCat.of (ULift.{max (u + 1) v} ℤ))) F q :=
  (etaleCohomologyRestrictionMap_bijective_iff.{u, v, w} f F q).trans
    (mapExt_bijective_iff_mapDerivedCategory _ _ _ _)

end Restriction

section Composition

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
    [HasSheafify Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]

/-- The inverse image on abelian étale sheaves of a composite is the composite of the inverse
images, in the other order. -/
def etaleAbelianInverseImageCompIso :
    etaleAbelianInverseImage.{u, v} (f ≫ g) ≅
      etaleAbelianInverseImage.{u, v} g ⋙ etaleAbelianInverseImage.{u, v} f := by
  let : MorphismProperty.HasPullbacksAlong (@Etale : MorphismProperty Scheme.{u}) f :=
    ⟨fun _ _ => inferInstance⟩
  let : MorphismProperty.HasPullbacksAlong (@Etale : MorphismProperty Scheme.{u}) g :=
    ⟨fun _ _ => inferInstance⟩
  let : MorphismProperty.IsStableUnderBaseChangeAlong
      (@Etale : MorphismProperty Scheme.{u}) f :=
    ⟨fun pb hg => MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
  let : MorphismProperty.IsStableUnderBaseChangeAlong
      (@Etale : MorphismProperty Scheme.{u}) g :=
    ⟨fun pb hg => MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
  let e : smallEtaleBaseChange (f ≫ g) ≅
      smallEtaleBaseChange g ⋙ smallEtaleBaseChange f :=
    MorphismProperty.Over.pullbackComp f g
  let a := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (smallEtaleBaseChange (f ≫ g)) AddCommGrpCat.{max (u + 1) v}
      Z.smallEtaleTopology X.smallEtaleTopology
  let b := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (smallEtaleBaseChange g) AddCommGrpCat.{max (u + 1) v}
      Z.smallEtaleTopology Y.smallEtaleTopology
  let c := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (smallEtaleBaseChange f) AddCommGrpCat.{max (u + 1) v}
      Y.smallEtaleTopology X.smallEtaleTopology
  exact a.leftAdjointUniq ((b.comp c).ofNatIsoRight
    (Functor.sheafPushforwardContinuousComp' e.symm AddCommGrpCat.{max (u + 1) v}
      Z.smallEtaleTopology Y.smallEtaleTopology X.smallEtaleTopology))

end Composition

section Invariance

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
    [(smallEtaleBaseChange f).IsDenseSubsite
      (smallEtaleTopology Y) (smallEtaleTopology X)]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]

/-- The inverse image of a torsion abelian sheaf along a dense subsite inclusion of small étale
sites is torsion. -/
lemma torsionSheafProperty_inverseImage_of_isDenseSubsite
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hF : Stacks.Torsion.torsionSheafProperty Y.smallEtaleTopology F) :
    Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology
      ((etaleAbelianInverseImage.{u, v} f).obj F) := by
  let G := smallEtaleBaseChange f
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous G
    AddCommGrpCat.{max (u + 1) v} Y.smallEtaleTopology X.smallEtaleTopology
  exact torsionSheafProperty_of_pushforward Y.smallEtaleTopology X.smallEtaleTopology G
    ((etaleAbelianInverseImage.{u, v} f).obj F)
    ((Stacks.Torsion.torsionSheafProperty.{max (u + 1) v} Y.smallEtaleTopology).prop_of_iso
      (asIso (adj.unit.app F)) hF)

/-- For an equivalence of small étale sites the inverse image is bijective on the `Ext` groups
that compute étale cohomology. -/
lemma isBijectiveOnExt_etaleAbelianInverseImage_of_isDenseSubsite
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (q : ℕ) :
    IsBijectiveOnExt (etaleAbelianInverseImage.{u, v} f)
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj
        (AddCommGrpCat.of (ULift.{max (u + 1) v} ℤ))) F q := by
  let := HasExt.standard (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
  let := HasExt.standard (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
  exact (etaleCohomologyRestrictionMap_bijective_iff_isBijectiveOnExt f F q).mp
    (etaleCohomologyRestrictionMap_bijective_of_isDenseSubsite f F q)

end Invariance

end Stacks.EtaleCohomology

end
