module

public import StacksFrontier.AlgebraicGeometry.Quot.RelativelyPerfectDirectImageReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativeTorAtGeometricPoint
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.StalkwiseSlicePoints
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.StalkwiseFiniteTor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkSemilinearComparison
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryCompQh

/-!
# Relative perfectness over a smaller base

Let `h : W ⟶ T` be a morphism of a big fppf site, and let `f : Z₁ ⟶ Z₂` over `W` and
`g : Y₁ ⟶ Y₂` over `T` be flat, locally finitely presented morphisms of algebraic spaces matched by
identifications `εᵢ : Λ_h Zᵢ ≅ Yᵢ` of the lower-shriek extensions (Stacks 04SG). This file proves
`AlgebraicGeometry.Space.SmallerBaseRelativelyPerfectComparison`: an object `K` of `D(𝒪_{Y₁})` is
`Y₂`-perfect (Stacks 0DKN) exactly when the corresponding object of `D(𝒪_{Z₁})` is `Z₂`-perfect.

Pseudo-coherence is `AlgebraicGeometry.Space.isPseudoCoherent_smallerBaseDerivedEquivalence_iff`.
The Tor clause is read at the geometric stalks. It is first made local and stalkwise on one
space: `E`, read in `D(f⁻¹𝒪_Y)`, locally has finite Tor dimension exactly when every chart has a
covering sieve on each member of which one interval bounds the Tor amplitude of `E_x̄` over
`(f⁻¹𝒪_Y)_x̄` at all geometric points `x̄` lifting to it. Then the change of base is compared at
the stalks:

* a geometric point of `Z₁` over `W` and a geometric point of `Y₁` over `T` whose point charts
  correspond have the same fibre functors along the equivalence of small étale sites; every
  geometric point on either side has a partner;
* the stalks of the structure sheaves and of the modules correspond along this matching;
* `(f⁻¹𝒪_{Z₂})_x̄` and `(g⁻¹𝒪_{Y₂})_x̄` are the stalks of `𝒪_{Z₂}` and `𝒪_{Y₂}` at the images
  (Stacks 04K2), and the two fibres of the structure maps correspond, by the uniqueness clause of
  Stacks 04NG.

## Main results

* `AlgebraicGeometry.Space.locallyHasFiniteTorDimension_derivedScalarRestriction_iff`: the Tor
  clause of Stacks 0DKN is a local bound on the geometric stalks.
* `AlgebraicGeometry.Space.stalkStructureMap_smallerBase`: the fibres of the structure maps over
  the two bases agree.
* `AlgebraicGeometry.Space.stalkTorAmplitude_smallerBase_iff`: the stalkwise Tor amplitude over
  the two bases agrees.
* `AlgebraicGeometry.Space.smallerBaseRelativelyPerfectComparison`: the proposition
  `AlgebraicGeometry.Space.SmallerBaseRelativelyPerfectComparison` holds.

## References

* [Stacks Project, Tag 0DKN](https://stacks.math.columbia.edu/tag/0DKN)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 04K2](https://stacks.math.columbia.edu/tag/04K2)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v₁ v₂ u₁ u₂ u₃ v₃ e

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} (e : C ≌ D)
  (Ψ' : J.Point.{w}) (Ψ : K.Point.{w}) (θ : Ψ'.fiber ≅ e.functor ⋙ Ψ.fiber)

/-- The functor of neighbourhoods induced by an equivalence of sites matching the fibre functors
of two points. -/
def elementsFunctorOfFiberIso : Ψ'.fiber.Elements ⥤ Ψ.fiber.Elements :=
  CategoryOfElements.map θ.hom ⋙ Functor.Elements.precomp e.functor Ψ.fiber

/-- The functor of neighbourhoods induced by an equivalence of sites is faithful. -/
instance elementsFunctorOfFiberIso_faithful : (elementsFunctorOfFiberIso e Ψ' Ψ θ).Faithful where
  map_injective {_ _} _ _ hfg := Subtype.ext (e.functor.map_injective (congrArg Subtype.val hfg))

/-- The functor of neighbourhoods induced by an equivalence of sites is full. -/
instance elementsFunctorOfFiberIso_full : (elementsFunctorOfFiberIso e Ψ' Ψ θ).Full where
  map_surjective {x y} φ := by
    refine ⟨⟨e.functor.preimage φ.1, ?_⟩, ?_⟩
    · apply (ConcreteCategory.bijective_of_isIso (θ.hom.app y.1)).1
      have h1 : θ.hom.app y.1 (Ψ'.fiber.map (e.functor.preimage φ.1) x.2) =
          Ψ.fiber.map (e.functor.map (e.functor.preimage φ.1)) (θ.hom.app x.1 x.2) :=
        ConcreteCategory.congr_hom (θ.hom.naturality (e.functor.preimage φ.1)) x.2
      exact h1.trans ((congrArg (fun k : e.functor.obj x.1 ⟶ e.functor.obj y.1 =>
        Ψ.fiber.map k (θ.hom.app x.1 x.2)) (e.functor.map_preimage φ.1)).trans φ.2)
    · exact Subtype.ext (e.functor.map_preimage φ.1)

/-- The functor of neighbourhoods induced by an equivalence of sites is essentially surjective. -/
instance elementsFunctorOfFiberIso_essSurj : (elementsFunctorOfFiberIso e Ψ' Ψ θ).EssSurj where
  mem_essImage z := by
    refine ⟨⟨e.inverse.obj z.1, θ.inv.app _ (Ψ.fiber.map (e.counitIso.inv.app z.1) z.2)⟩,
      ⟨CategoryOfElements.isoMk _ _ (e.counitIso.app z.1) ?_⟩⟩
    change Ψ.fiber.map _ (θ.hom.app _ (θ.inv.app _ _)) = _
    rw [← types_comp_apply (θ.inv.app _) (θ.hom.app _), Iso.inv_hom_id_app]
    change (Ψ.fiber.map (e.counitIso.inv.app z.fst) ≫
      Ψ.fiber.map (e.counitIso.hom.app z.fst)) z.2 = _
    rw [← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id]
    rfl

/-- The functor of neighbourhoods is an equivalence. -/
instance elementsFunctorOfFiberIso_isEquivalence :
    (elementsFunctorOfFiberIso e Ψ' Ψ θ).IsEquivalence where

variable {A : Type u₃} [Category.{v₃} A] [HasColimitsOfSize.{w, w} A]

/-- **The stalk of a presheaf is unchanged by an equivalence of sites matching two points.** -/
def presheafFiberIsoOfEquivalence (P : Dᵒᵖ ⥤ A) :
    Ψ'.presheafFiber.obj (e.functor.op ⋙ P) ≅ Ψ.presheafFiber.obj P :=
  Functor.Final.colimitIso (elementsFunctorOfFiberIso e Ψ' Ψ θ).op
    ((CategoryOfElements.π Ψ.fiber).op ⋙ P)

/-- The comparison of `CategoryTheory.GrothendieckTopology.Point.presheafFiberIsoOfEquivalence`
takes the germ at `(X, x)` to the germ at the image neighbourhood `(e X, θ x)`. -/
@[reassoc]
theorem toPresheafFiber_presheafFiberIsoOfEquivalence_hom (P : Dᵒᵖ ⥤ A) (X : C)
    (x : Ψ'.fiber.obj X) :
    Ψ'.toPresheafFiber X x (e.functor.op ⋙ P) ≫ (presheafFiberIsoOfEquivalence e Ψ' Ψ θ P).hom =
      Ψ.toPresheafFiber (e.functor.obj X) (θ.hom.app X x) P :=
  Functor.Final.ι_colimitIso_hom (elementsFunctorOfFiberIso e Ψ' Ψ θ).op
    ((CategoryOfElements.π Ψ.fiber).op ⋙ P) (op ⟨X, x⟩)

end CategoryTheory.GrothendieckTopology.Point

namespace Stacks

open CategoryTheory.GrothendieckTopology

section ReindexStalk

variable {C' : Type u₁} [Category.{v₁} C'] {C : Type u₂} [Category.{v₂} C]
  [LocallySmall.{w} C] [LocallySmall.{w} C']
  {J' : GrothendieckTopology C'} {J : GrothendieckTopology C} (e : C' ≌ C)
  [e.functor.IsContinuous J' J] [e.inverse.IsContinuous J J']
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J'.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (Ψ' : J'.Point.{w}) (Ψ : J.Point.{w}) (θ : Ψ'.fiber ≅ e.functor ⋙ Ψ.fiber)
  (O : Sheaf J CommRingCat.{w})

/-- A sheaf of commutative rings transported along an equivalence of sites. -/
abbrev reindexCommRingSheaf (J' : GrothendieckTopology C') [e.functor.IsContinuous J' J] :
    Sheaf J' CommRingCat.{w} :=
  (e.functor.sheafPushforwardContinuous CommRingCat.{w} J' J).obj O

/-- The stalks of a sheaf of commutative rings and of its transport along an equivalence of sites
matching two points. -/
def reindexRingStalkIso :
    (Ψ'.presheafFiber (A := CommRingCat.{w})).obj (reindexCommRingSheaf e O J').obj ≅
      (Ψ.presheafFiber (A := CommRingCat.{w})).obj O.obj :=
  Point.presheafFiberIsoOfEquivalence e Ψ' Ψ θ O.obj

omit [LocallySmall.{w, v₂, u₂} C] [LocallySmall.{w, v₁, u₁} C'] [e.inverse.IsContinuous J J'] in
/-- The comparison of ring stalks takes germs to germs. -/
theorem reindexRingStalkIso_hom_ringStalkGerm (U : C') (ξ : Ψ'.fiber.obj U)
    (a : (commRingSheafToRingSheaf (reindexCommRingSheaf e O J')).obj.obj (op U)) :
    (reindexRingStalkIso e Ψ' Ψ θ O).hom.hom
        (ringStalkGerm Ψ' (reindexCommRingSheaf e O J') U ξ a) =
      ringStalkGerm Ψ O (e.functor.obj U) (θ.hom.app U ξ) a :=
  ConcreteCategory.congr_hom
    (Point.toPresheafFiber_presheafFiberIsoOfEquivalence_hom e Ψ' Ψ θ O.obj U ξ) a

/-- The module equivalence of an equivalence of sites, at the sheaf of rings of a sheaf of
commutative rings. -/
abbrev reindexModuleFunctor (J' : GrothendieckTopology C') [e.functor.IsContinuous J' J]
    [e.inverse.IsContinuous J J'] [J'.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] :
    SheafOfModules.{w} (commRingSheafToRingSheaf O) ⥤
      SheafOfModules.{w} (commRingSheafToRingSheaf (reindexCommRingSheaf e O J')) :=
  (SheafOfModules.reindexEquivalence e (commRingSheafToRingSheaf O)).functor

/-- The stalk of a transported module, on underlying abelian groups. -/
def reindexModuleStalkAddIso (M : SheafOfModules.{w} (commRingSheafToRingSheaf O)) :
    (forget₂ _ AddCommGrpCat.{w}).obj
        (moduleStalk Ψ' (reindexCommRingSheaf e O J') ((reindexModuleFunctor e O J').obj M)) ≅
      (forget₂ _ AddCommGrpCat.{w}).obj ((ModuleCat.restrictScalars
        (reindexRingStalkIso e Ψ' Ψ θ O).hom.hom).obj (moduleStalk Ψ O M)) :=
  AlgebraicGeometry.RingedSite.moduleStalkForget₂Iso Ψ' (reindexCommRingSheaf e O J') _ ≪≫
    Point.presheafFiberIsoOfEquivalence e Ψ' Ψ θ M.val.presheaf ≪≫
    (AlgebraicGeometry.RingedSite.moduleStalkRestrictScalarsForget₂Iso Ψ O _ M).symm

/-- The comparison of module stalks takes germs to germs. -/
lemma reindexModuleStalkAddIso_hom_germ (M : SheafOfModules.{w} (commRingSheafToRingSheaf O))
    (U : C') (ξ : Ψ'.fiber.obj U) (t : ((reindexModuleFunctor e O J').obj M).val.obj (op U)) :
    (reindexModuleStalkAddIso e Ψ' Ψ θ O M).hom
        (moduleStalkGerm Ψ' (reindexCommRingSheaf e O J') ((reindexModuleFunctor e O J').obj M)
          U ξ t) =
      moduleStalkGerm Ψ O M (e.functor.obj U) (θ.hom.app U ξ) t := by
  show (Point.presheafFiberIsoOfEquivalence e Ψ' Ψ θ M.val.presheaf).hom.hom
      (Ψ'.toPresheafFiber U ξ (e.functor.op ⋙ M.val.presheaf) t) =
    Ψ.toPresheafFiber (e.functor.obj U) (θ.hom.app U ξ) M.val.presheaf t
  exact ConcreteCategory.congr_hom
    (Point.toPresheafFiber_presheafFiberIsoOfEquivalence_hom e Ψ' Ψ θ M.val.presheaf U ξ) t

/-- The comparison of module stalks is semilinear over the comparison of ring stalks. -/
lemma reindexModuleStalkAddIso_hom_smul (M : SheafOfModules.{w} (commRingSheafToRingSheaf O))
    (r : (Ψ'.presheafFiber (A := CommRingCat.{w})).obj (reindexCommRingSheaf e O J').obj)
    (n : moduleStalk Ψ' (reindexCommRingSheaf e O J') ((reindexModuleFunctor e O J').obj M)) :
    (reindexModuleStalkAddIso e Ψ' Ψ θ O M).hom (r • n) =
      (reindexRingStalkIso e Ψ' Ψ θ O).hom.hom r •
        @id (moduleStalk Ψ O M) ((reindexModuleStalkAddIso e Ψ' Ψ θ O M).hom n) := by
  obtain ⟨W₁, y₁, s, rfl⟩ := moduleStalkGerm_jointly_surjective Ψ' (reindexCommRingSheaf e O J')
    ((reindexModuleFunctor e O J').obj M) n
  obtain ⟨W₂, y₂, a, rfl⟩ := ringStalkGerm_jointly_surjective Ψ' (reindexCommRingSheaf e O J') r
  obtain ⟨W, y, g₁, g₂, h₁, h₂⟩ := exists_common_nbhd (Φ := Ψ') y₁ y₂
  have hs := moduleStalkGerm_restrict Ψ' (reindexCommRingSheaf e O J')
    ((reindexModuleFunctor e O J').obj M) g₁ y s
  have ha := ringStalkGerm_restrict Ψ' (reindexCommRingSheaf e O J') g₂ y a
  rw [h₁] at hs
  rw [h₂] at ha
  rw [← hs, ← ha]
  refine (congrArg (reindexModuleStalkAddIso e Ψ' Ψ θ O M).hom
    (moduleStalkGerm_smul Ψ' (reindexCommRingSheaf e O J') _ W y _ _).symm).trans ?_
  refine (reindexModuleStalkAddIso_hom_germ e Ψ' Ψ θ O M W y _).trans ?_
  refine (moduleStalkGerm_smul Ψ O M (e.functor.obj W) (θ.hom.app W y) _ _).trans ?_
  rw [reindexRingStalkIso_hom_ringStalkGerm]
  exact congrArg (fun m => ringStalkGerm Ψ O (e.functor.obj W) (θ.hom.app W y) _ • m)
    (reindexModuleStalkAddIso_hom_germ e Ψ' Ψ θ O M W y _).symm

/-- **The stalk of a module transported along an equivalence of sites matching two points** is
the stalk of the module, with its scalars restricted along the comparison of the ring stalks. -/
def reindexModuleStalkIso (M : SheafOfModules.{w} (commRingSheafToRingSheaf O)) :
    moduleStalk Ψ' (reindexCommRingSheaf e O J') ((reindexModuleFunctor e O J').obj M) ≅
      (ModuleCat.restrictScalars (reindexRingStalkIso e Ψ' Ψ θ O).hom.hom).obj
        (moduleStalk Ψ O M) :=
  ModuleCat.isoMk (reindexModuleStalkAddIso e Ψ' Ψ θ O M) (fun r => by
    ext n
    exact (reindexModuleStalkAddIso_hom_smul e Ψ' Ψ θ O M r n).symm)

/-- `Stacks.reindexModuleStalkIso` takes germs to germs. -/
lemma reindexModuleStalkIso_hom_germ (M : SheafOfModules.{w} (commRingSheafToRingSheaf O))
    (U : C') (ξ : Ψ'.fiber.obj U) (t : ((reindexModuleFunctor e O J').obj M).val.obj (op U)) :
    (reindexModuleStalkIso e Ψ' Ψ θ O M).hom
        (moduleStalkGerm Ψ' (reindexCommRingSheaf e O J') ((reindexModuleFunctor e O J').obj M)
          U ξ t) =
      moduleStalkGerm Ψ O M (e.functor.obj U) (θ.hom.app U ξ) t :=
  reindexModuleStalkAddIso_hom_germ e Ψ' Ψ θ O M U ξ t

/-- `Stacks.reindexModuleStalkIso`, naturally in the module. -/
def reindexModuleStalkNatIso :
    reindexModuleFunctor e O J' ⋙ sheafModuleFiberOfCommRing Ψ' (reindexCommRingSheaf e O J') ≅
      sheafModuleFiberOfCommRing Ψ O ⋙
        ModuleCat.restrictScalars (reindexRingStalkIso e Ψ' Ψ θ O).hom.hom :=
  NatIso.ofComponents (reindexModuleStalkIso e Ψ' Ψ θ O) (fun {M M'} g => by
    ext n
    obtain ⟨W, y, t, rfl⟩ := moduleStalkGerm_jointly_surjective Ψ' (reindexCommRingSheaf e O J')
      ((reindexModuleFunctor e O J').obj M) n
    change (reindexModuleStalkIso e Ψ' Ψ θ O M').hom ((sheafModuleFiberOfCommRing Ψ'
        (reindexCommRingSheaf e O J')).map ((reindexModuleFunctor e O J').map g)
          (moduleStalkGerm Ψ' _ _ W y t)) =
      (sheafModuleFiberOfCommRing Ψ O).map g
        ((reindexModuleStalkIso e Ψ' Ψ θ O M).hom (moduleStalkGerm Ψ' _ _ W y t))
    rw [moduleStalkGerm_naturality, reindexModuleStalkIso_hom_germ, reindexModuleStalkIso_hom_germ]
    exact (moduleStalkGerm_naturality Ψ O g (e.functor.obj W) (θ.hom.app W y) t).symm)

end ReindexStalk

end Stacks

namespace AlgebraicGeometry.Space

section LocalStalkBound

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

/-- Canonical Tor amplitude is invariant under an isomorphism of derived objects. -/
private theorem hasTorAmplitudeCanonical_iff_of_iso {R : Type u₁} [CommRing R]
    {E F : DerivedCategory (ModuleCat.{u₁} R)} (e : E ≅ F) (a b : ℤ) :
    StacksDraft.TorAmplitude.HasTorAmplitudeCanonical R E a b ↔
      StacksDraft.TorAmplitude.HasTorAmplitudeCanonical R F a b :=
  ⟨AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso e a b,
    AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso e.symm a b⟩

variable (B : BigFppfSite.{u₁}) (S : Scheme.{u₁}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- The Tor amplitude of the geometric stalk `E_x̄`, read over the stalk of `f⁻¹𝒪_Y`, lies in
`[a, b]`. -/
abbrev GeometricStalkTorAmplitude (E : DerivedCategory (Modules.{u₁, u₁} B S hS X.1 X.2))
    (x : GeometricPoint B S hS X.1) (a b : ℤ) : Prop :=
  StacksDraft.TorAmplitude.HasTorAmplitudeCanonical
    (((etaleSitePoint B S hS X.1 x X.2).presheafFiber (A := CommRingCat.{u₁})).obj
      (inverseImageRingedSite B S hS f).O.obj)
    ((ModuleCat.restrictScalars.{u₁} (inverseImageStalkRingHom B S hS f x)).mapDerivedCategory.obj
      ((geometricStalkFunctor B S hS x).mapDerivedCategory.obj E)) a b

/-- The geometric stalks of `E` are bounded locally on the small étale site of `X`: every chart
`U` carries a covering sieve on each member `V` of which one interval contains the Tor amplitude
of `E` at every geometric point lifting to `V`. -/
def HasLocalStalkTorBound (E : DerivedCategory (Modules.{u₁, u₁} B S hS X.1 X.2)) : Prop :=
  ∀ U : (smallEtaleRingedSite B S hS X.1 X.2).C, ∃ R : Sieve U,
    R ∈ (smallEtaleRingedSite B S hS X.1 X.2).J U ∧
    ∀ ⦃V : (smallEtaleRingedSite B S hS X.1 X.2).C⦄ (k : V ⟶ U), R k → ∃ a b : ℤ,
      ∀ (x : GeometricPoint B S hS X.1), (etaleSitePoint B S hS X.1 x X.2).fiber.obj V →
        GeometricStalkTorAmplitude B S hS f E x a b

variable
  [HasDerivedCategory.{e} (RingedSite.Modules.{u₁ + 1, u₁, u₁} (inverseImageRingedSite B S hS f))]

/-- Sheafification of abelian presheaves on a slice of `(X_étale, f⁻¹𝒪_Y)`. -/
local instance (priority := high) inverseImageSlice_hasSheafify_smallerBase
    (V : (inverseImageRingedSite B S hS f).C) :
    HasSheafify ((inverseImageRingedSite B S hS f).over V).J AddCommGrpCat.{u₁} :=
  smallEtaleRingedSite_hasSheafify_over_addCommGrpCat B S hS X.1 X.2 V

attribute [local instance] AlgebraicGeometry.Space.inverseImageRingedSite_hasWeakSheafify_over
  AlgebraicGeometry.Space.inverseImageRingedSite_wEqualsLocallyBijective_over
  RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective
  RingedSite.sliceRestrictionPreservesFiniteLimits
  RingedSite.sliceRestrictionPreservesFiniteColimits

variable
    [∀ U : (inverseImageRingedSite B S hS f).C,
      HasDerivedCategory.{e}
        (RingedSite.Modules.{u₁ + 1, u₁, u₁} ((inverseImageRingedSite B S hS f).over U))]

attribute [local instance] RingedSite.sliceHasDerivedCategory
  Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_obj_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasMapBifunctor
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor

open Stacks.SheafOfModules.DerivedTensorProduct in
/-- **The Tor clause of relative perfectness is a local bound on the geometric stalks.** -/
theorem locallyHasFiniteTorDimension_derivedScalarRestriction_iff
    (T : ∀ U : (inverseImageRingedSite B S hS f).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u₁ + 1, u₁, u₁, e}
        ((inverseImageRingedSite B S hS f).over U))
    (E : DerivedCategory (Modules.{u₁, u₁} B S hS X.1 X.2)) :
    LocallyHasFiniteTorDimension.{u₁ + 1, u₁, u₁, e} T
        ((derivedScalarRestriction B S hS f).obj E) ↔
      HasLocalStalkTorBound B S hS f E := by
  constructor
  · intro hE U
    obtain ⟨P, hP, hamp⟩ := hE U
    refine ⟨Sieve.generate P, hP, fun V k hk => ?_⟩
    obtain ⟨V', w, s, hs, rfl⟩ := hk
    obtain ⟨a, b, hab⟩ := hamp s hs
    refine ⟨a, b, fun x ξ => ?_⟩
    let Φ : (inverseImageRingedSite B S hS f).J.Point.{u₁} := etaleSitePoint B S hS X.1 x X.2
    have := inverseImageSlice_hasSheafify_smallerBase B S hS f V'
    have := AlgebraicGeometry.Space.inverseImageRingedSite_wEqualsLocallyBijective_over f V'
    have h₁ := hasTorAmplitudeCanonical_derivedModuleFiber.{u₁ + 1, u₁, u₁, e} (T V') _ a b
      hab (Φ.over ((etaleSitePoint B S hS X.1 x X.2).fiber.map w ξ))
    have h₂ := (RingedSite.hasTorAmplitudeCanonical_derivedModuleFiber_over_iff Φ _ _ a b).1 h₁
    exact (hasTorAmplitudeCanonical_iff_of_iso (derivedScalarRestrictionStalkIso B S hS f x E)
      a b).1 h₂
  · intro hE
    refine locallyHasFiniteTorDimension_of_stalkwise_family T _
      (t := fun V => Σ x : GeometricPoint B S hS X.1,
        (etaleSitePoint B S hS X.1 x X.2).fiber.obj V)
      (fun V ψ => ((etaleSitePoint B S hS X.1 ψ.1 X.2 :
        (inverseImageRingedSite B S hS f).J.Point.{u₁}).over ψ.2))
      (fun V => isConservativeFamilyOfPoints_etaleSitePointOver B S hS X.2 V) (fun U => ?_)
    obtain ⟨R, hR, hb⟩ := hE U
    refine ⟨R.arrows, by simpa only [Sieve.generate_sieve] using hR, fun V k hk => ?_⟩
    obtain ⟨a, b, hab⟩ := hb k hk
    refine ⟨a, b, fun ψ => ?_⟩
    let Φ : (inverseImageRingedSite B S hS f).J.Point.{u₁} := etaleSitePoint B S hS X.1 ψ.1 X.2
    exact (RingedSite.hasTorAmplitudeCanonical_derivedModuleFiber_over_iff Φ ψ.2 _ a b).2
      ((hasTorAmplitudeCanonical_iff_of_iso (derivedScalarRestrictionStalkIso B S hS f ψ.1 E)
        a b).2 (hab ψ.1 ψ.2))

end LocalStalkBound


/-! ### The geometric fibre as a hom functor of charts -/

section PointChart

variable {B : BigFppfSite.{u₁}} {S : Scheme.{u₁}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u₁}

/-- The chart of `F` on the field spectrum of a geometric point, given by the section the point
carries. -/
abbrev geometricPointChart (x : GeometricPoint B S hS F) : CostructuredArrow yoneda F :=
  CostructuredArrow.mk (yonedaEquiv.symm x.val.value : yoneda.obj x.val.siteObject ⟶ F)

/-- A lift of a geometric point into an étale chart is a morphism of charts from its point
chart. -/
def geometricFiberEquivHom (x : GeometricPoint B S hS F) (U : SmallEtale B S hS F) :
    GeometricFiber B S hS F x U ≃
      (geometricPointChart x ⟶ (SmallEtale.inclusion B S hS F).obj U) where
  toFun p := CostructuredArrow.homMk p.1 (by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
    exact p.2.trans (yonedaEquiv.apply_symm_apply _).symm)
  invFun k := ⟨k.left, by
    have hk := congrArg yonedaEquiv (CostructuredArrow.w k)
    rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map] at hk
    exact hk.trans (yonedaEquiv.apply_symm_apply _)⟩
  left_inv p := rfl
  right_inv k := by
    apply CostructuredArrow.hom_ext
    rfl

/-- **The geometric fibre functor is the hom functor out of the point chart.** -/
def geometricFiberIsoCoyoneda (x : GeometricPoint B S hS F) :
    geometricFiber B S hS F x ≅
      SmallEtale.inclusion B S hS F ⋙ coyoneda.obj (op (geometricPointChart x)) :=
  NatIso.ofComponents (fun U => (geometricFiberEquivHom x U).toIso) (fun {U V} k => by
    ext p
    apply CostructuredArrow.hom_ext
    rfl)

end PointChart

section FiberTransport

variable {B : BigFppfSite.{u₁}} {S₁ S₂ : Scheme.{u₁}} {hS₁ : B.Contains S₁} {hS₂ : B.Contains S₂}
  {F₁ : (BigFppfOver B S₁ hS₁)ᵒᵖ ⥤ Type u₁} {F₂ : (BigFppfOver B S₂ hS₂)ᵒᵖ ⥤ Type u₁}
  (Γ : CostructuredArrow yoneda F₁ ⥤ CostructuredArrow yoneda F₂) (hΓ : Γ.FullyFaithful)
  {x₁ : GeometricPoint B S₁ hS₁ F₁} {x₂ : GeometricPoint B S₂ hS₂ F₂}
  (ι : Γ.obj (geometricPointChart x₁) ≅ geometricPointChart x₂)

/-- **Geometric fibres along a fully faithful functor of charts**, matching the point charts. -/
def geometricFiberIsoOfChartIso :
    geometricFiber B S₁ hS₁ F₁ x₁ ≅
      SmallEtale.inclusion B S₁ hS₁ F₁ ⋙ Γ ⋙ coyoneda.obj (op (geometricPointChart x₂)) :=
  geometricFiberIsoCoyoneda x₁ ≪≫
    NatIso.ofComponents (fun U => Equiv.toIso
      { toFun := fun p => ι.inv ≫ Γ.map p
        invFun := fun q => hΓ.preimage (ι.hom ≫ q)
        left_inv := fun p => by simp
        right_inv := fun q => by simp }) (fun {U V} k => by
        ext p
        simp)

end FiberTransport


section ChangeOfBasePoints

variable {B : BigFppfSite.{u₁}} {W T : Scheme.{u₁}} {hW : B.Contains W} {hT : B.Contains T}
  (h : B.obj hW ⟶ B.obj hT)

/-- The section of `Λ_h F` that the extension of a chart carries is the factorization through `W`
of the structure morphism of the chart, with the section of the chart. -/
theorem yonedaEquiv_relocalizeChart {F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u₁}
    {U : BigFppfOver B W hW} (a : yoneda.obj U ⟶ F) :
    yonedaEquiv (relocalizeChart B W T hW hT h a) =
      OverShriek.relocalizeMk h F (W := op ((Over.map h).obj U)) U.hom (yonedaEquiv a) rfl := by
  apply Subtype.ext
  show (⟨𝟙 U.left ≫ U.hom,
    a.app _ (Over.homMk (𝟙 U.left) rfl : Over.mk (𝟙 U.left ≫ U.hom) ⟶ U)⟩ :
      Σ ψ : ((Over.map h).obj U).left ⟶ B.obj hW, F.obj (op (Over.mk ψ))) = ⟨U.hom, yonedaEquiv a⟩
  rw [← map_yonedaEquiv]
  exact OverShriek.sigmaMk_eq_self F _ _ (by simp)

/-- The charts of `F` over `W` and of `G` over `T`, for `ε : Λ_h F ≅ G`: extend along `h`, then
compose with `ε`. -/
abbrev smallerBaseChartsFunctor {F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u₁}
    {G : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u₁}
    (ε : (OverShriek.relocalizePresheafFunctor h).obj F ≅ G) :
    CostructuredArrow yoneda F ⥤ CostructuredArrow yoneda G :=
  relocalizeChartsFunctor B W T hW hT h F ⋙ (CostructuredArrow.mapIso ε).functor

/-- `AlgebraicGeometry.Space.smallerBaseChartsFunctor` is fully faithful. -/
def smallerBaseChartsFunctorFullyFaithful {F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u₁}
    {G : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u₁}
    (ε : (OverShriek.relocalizePresheafFunctor h).obj F ≅ G) :
    (smallerBaseChartsFunctor h ε).FullyFaithful :=
  (Functor.FullyFaithful.ofFullyFaithful _).comp (CostructuredArrow.mapIso ε).fullyFaithfulFunctor

variable {Z : AlgebraicSpaces B W hW} {Y : AlgebraicSpaces B T hT}
  (ε : (OverShriek.relocalizePresheafFunctor h).obj Z.1 ≅ Y.1)

/-- **The geometric fibres over the smaller base**: a geometric point `x'` of `Z` over `W` and a
geometric point `x` of `Y` over `T` whose point charts correspond have the same fibre functors,
along the equivalence of small étale sites. -/
def smallerBaseFiberIso {x' : GeometricPoint B W hW Z.1} {x : GeometricPoint B T hT Y.1}
    (ι : (smallerBaseChartsFunctor h ε).obj (geometricPointChart x') ≅ geometricPointChart x) :
    (etaleSitePoint B W hW Z.1 x' Z.2).fiber ≅
      (smallerBaseSmallEtaleEquivalenceOfIso B h ε).functor ⋙
        (etaleSitePoint B T hT Y.1 x Y.2).fiber :=
  geometricFiberIsoOfChartIso _ (smallerBaseChartsFunctorFullyFaithful h ε) ι ≪≫
    Functor.isoWhiskerLeft (smallerBaseSmallEtaleEquivalenceOfIso B h ε).functor
      (geometricFiberIsoCoyoneda x).symm

/-- The lift matched with a lift `p` is the extension of `p` along `h`, read through the matching
of the point charts. -/
theorem smallerBaseFiberIso_hom_app_val {x' : GeometricPoint B W hW Z.1}
    {x : GeometricPoint B T hT Y.1}
    (ι : (smallerBaseChartsFunctor h ε).obj (geometricPointChart x') ≅ geometricPointChart x)
    (U : SmallEtale B W hW Z.1) (p : GeometricFiber B W hW Z.1 x' U) :
    ((smallerBaseFiberIso h ε ι).hom.app U p).1 = ι.inv.left ≫ (Over.map h).map p.1 :=
  rfl

/-- A geometric point of `F` over `W`, read over `T`. -/
abbrev relocalizeGeometricPoint {F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u₁}
    (x' : GeometricPoint B W hW F) :
    GeometricPoint B T hT ((OverShriek.relocalizePresheafFunctor h).obj F) :=
  ⟨x'.val.relocalize B W T hW hT h F, x'.property⟩

/-- The extension of the point chart of a field-valued point is the point chart of its
extension. -/
theorem relocalizeChart_yonedaEquiv_symm {F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u₁}
    (x' : FieldValuedPoint B W hW F) :
    relocalizeChart B W T hW hT h (yonedaEquiv.symm x'.value : yoneda.obj x'.siteObject ⟶ F) =
      (yonedaEquiv.symm (x'.relocalize B W T hW hT h F).value :
        yoneda.obj ((Over.map h).obj x'.siteObject) ⟶ _) := by
  refine yonedaEquiv.injective ((yonedaEquiv_relocalizeChart h _).trans ?_)
  refine Eq.trans ?_ (Equiv.apply_symm_apply yonedaEquiv _).symm
  exact congrArg (fun s : F.obj (op x'.siteObject) =>
    OverShriek.relocalizeMk h F (W := op ((Over.map h).obj x'.siteObject)) x'.siteObject.hom s rfl)
    (Equiv.apply_symm_apply yonedaEquiv _)

/-- The point chart of the extension of a geometric point is the extension of its point chart. -/
def smallerBasePointChartIso {F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u₁}
    {G : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u₁} (ε : (OverShriek.relocalizePresheafFunctor h).obj F ≅ G)
    (x' : GeometricPoint B W hW F) :
    (smallerBaseChartsFunctor h ε).obj (geometricPointChart x') ≅
      geometricPointChart (geometricPointMap ε.hom (relocalizeGeometricPoint h x')) :=
  CostructuredArrow.isoMk (Iso.refl ((Over.map h).obj x'.val.siteObject))
    ((congrArg (· ≫ _) (yoneda.map_id _)).trans ((Category.id_comp _).trans
      ((congrArg (· ≫ ε.hom) (relocalizeChart_yonedaEquiv_symm h x'.val)).trans
        (yonedaEquiv_symm_naturality_right _ ε.hom _)).symm))

/-- The extension of the chart of a section, followed by a morphism out of `Λ_h F`. -/
theorem relocalizeChart_yonedaEquiv_symm_comp {F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u₁}
    {G : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u₁} {U : BigFppfOver B W hW} (s : F.obj (op U))
    (φ : (OverShriek.relocalizePresheafFunctor h).obj F ⟶ G) :
    relocalizeChart B W T hW hT h (yonedaEquiv.symm s) ≫ φ =
      yonedaEquiv.symm (φ.app _ (OverShriek.relocalizeMk h F (W := op ((Over.map h).obj U))
        U.hom s rfl)) := by
  refine yonedaEquiv.injective ?_
  refine Eq.trans (yonedaEquiv_comp _ φ) (Eq.trans ?_ (Equiv.apply_symm_apply yonedaEquiv _).symm)
  refine congrArg (φ.app _) ((yonedaEquiv_relocalizeChart h _).trans ?_)
  exact congrArg (fun t : F.obj (op U) =>
    OverShriek.relocalizeMk h F (W := op ((Over.map h).obj U)) U.hom t rfl)
    (Equiv.apply_symm_apply yonedaEquiv _)

/-- Restricting a section of `Λ_h F` along a morphism which is the identity on the underlying
object reads off the factorization the section carries. -/
theorem relocalize_map_of_left_eq_id {F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u₁}
    {V : BigFppfOver B T hT} (q : ((OverShriek.relocalizePresheafFunctor h).obj F).obj (op V))
    (g : (Over.map h).obj (Over.mk q.1.1) ⟶ V) (hg : g.left = 𝟙 _) :
    ((OverShriek.relocalizePresheafFunctor h).obj F).map g.op q =
      OverShriek.relocalizeMk h F (W := op ((Over.map h).obj (Over.mk q.1.1))) q.1.1 q.1.2 rfl :=
  Subtype.ext (OverShriek.sigmaMk_eq_self F q.1.2 _ hg)

/-- A geometric point of `G` over `T`, read over `W` through `ε`. -/
abbrev derelocalizeGeometricPoint {F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u₁}
    {G : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u₁} (ε : (OverShriek.relocalizePresheafFunctor h).obj F ≅ G)
    (x : GeometricPoint B T hT G) : GeometricPoint B W hW F :=
  ⟨(FieldValuedPoint.map B T hT G ε.inv x.val).derelocalize B W T hW hT h F, x.property⟩

/-- Every geometric point over `T` arises from one over `W`, up to an isomorphism of point charts
which is the identity on the underlying scheme. -/
def smallerBasePointChartIsoOfDerelocalize {F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u₁}
    {G : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u₁} (ε : (OverShriek.relocalizePresheafFunctor h).obj F ≅ G)
    (x : GeometricPoint B T hT G) :
    (smallerBaseChartsFunctor h ε).obj (geometricPointChart (derelocalizeGeometricPoint h ε x)) ≅
      geometricPointChart x :=
  let q := (FieldValuedPoint.map B T hT G ε.inv x.val).value
  let ι₀ : (Over.map h).obj (Over.mk q.1.1) ≅ x.val.siteObject :=
    Over.isoMk (Iso.refl _) ((Category.id_comp _).trans (OverShriek.relocalizeFactors h F q).symm)
  CostructuredArrow.isoMk ι₀ (by
    refine (yonedaEquiv_symm_naturality_left _ G _).trans ?_
    refine Eq.trans ?_ (relocalizeChart_yonedaEquiv_symm_comp h q.1.2 ε.hom).symm
    refine congrArg yonedaEquiv.symm ?_
    have hx : x.val.value = ε.hom.app _ q := by
      change x.val.value =
        ε.hom.app (op x.val.siteObject) (ε.inv.app (op x.val.siteObject) x.val.value)
      exact (ConcreteCategory.congr_hom (ε.inv_hom_id_app (op x.val.siteObject)) x.val.value).symm
    refine (congrArg (G.map ι₀.hom.op) hx).trans ?_
    refine (NatTrans.naturality_apply ε.hom ι₀.hom.op q).symm.trans ?_
    exact congrArg (ε.hom.app _) (relocalize_map_of_left_eq_id h q ι₀.hom rfl))

/-- **Matched point charts along a matched pair of morphisms.** If `f : F₁ ⟶ F₂` over `W` and
`g : G₁ ⟶ G₂` over `T` correspond through `ε₁` and `ε₂`, a matching of the point charts of `x'`
and `x` induces one of the point charts of their images, with the same underlying morphism. -/
def smallerBasePointChartIsoMap {F₁ F₂ : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u₁}
    {G₁ G₂ : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u₁}
    (ε₁ : (OverShriek.relocalizePresheafFunctor h).obj F₁ ≅ G₁)
    (ε₂ : (OverShriek.relocalizePresheafFunctor h).obj F₂ ≅ G₂) {f : F₁ ⟶ F₂} {g : G₁ ⟶ G₂}
    (hfg : ε₁.hom ≫ g = (OverShriek.relocalizePresheafFunctor h).map f ≫ ε₂.hom)
    {x' : GeometricPoint B W hW F₁} {x : GeometricPoint B T hT G₁}
    (ι : (smallerBaseChartsFunctor h ε₁).obj (geometricPointChart x') ≅ geometricPointChart x) :
    (smallerBaseChartsFunctor h ε₂).obj (geometricPointChart (geometricPointMap f x')) ≅
      geometricPointChart (geometricPointMap g x) :=
  CostructuredArrow.isoMk ((CostructuredArrow.proj yoneda G₁).mapIso ι) (by
    have hι := CostructuredArrow.w ι.hom
    change yoneda.map ι.hom.left ≫ yonedaEquiv.symm (g.app _ x.val.value) =
      relocalizeChart B W T hW hT h (yonedaEquiv.symm (f.app _ x'.val.value)) ≫ ε₂.hom
    rw [← yonedaEquiv_symm_naturality_right, ← yonedaEquiv_symm_naturality_right,
      ← relocalizeChart_comp, Category.assoc, ← hfg, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ g) hι)

/-- The lifts matched by `AlgebraicGeometry.Space.smallerBaseFiberIso` at a point and at its
image are compatible with a morphism of charts over `f`. -/
theorem smallerBaseFiberIso_hom_app_val_comp {Z₁ Z₂ : AlgebraicSpaces B W hW}
    {Y₁ Y₂ : AlgebraicSpaces B T hT}
    (ε₁ : (OverShriek.relocalizePresheafFunctor h).obj Z₁.1 ≅ Y₁.1)
    (ε₂ : (OverShriek.relocalizePresheafFunctor h).obj Z₂.1 ≅ Y₂.1) {f : Z₁ ⟶ Z₂} {g : Y₁ ⟶ Y₂}
    (hfg : ε₁.hom ≫ g.hom = (OverShriek.relocalizePresheafFunctor h).map f.hom ≫ ε₂.hom)
    {x' : GeometricPoint B W hW Z₁.1} {x : GeometricPoint B T hT Y₁.1}
    (ι : (smallerBaseChartsFunctor h ε₁).obj (geometricPointChart x') ≅ geometricPointChart x)
    {U : SmallEtale B W hW Z₁.1} {V : SmallEtale B W hW Z₂.1}
    (p : GeometricFiber B W hW Z₁.1 x' U)
    (q : GeometricFiber B W hW Z₂.1 (geometricPointMap f.hom x') V)
    (g' : U.obj.left ⟶ V.obj.left) (hpq : p.1 ≫ g' = q.1) :
    ((smallerBaseFiberIso h ε₁ ι).hom.app U p).1 ≫ (Over.map h).map g' =
      ((smallerBaseFiberIso h ε₂ (smallerBasePointChartIsoMap h ε₁ ε₂ hfg ι)).hom.app V q).1 :=
  (Category.assoc _ _ _).trans (congrArg (ι.inv.left ≫ ·)
    (((Over.map h).map_comp _ _).symm.trans (congrArg (Over.map h).map hpq)))

end ChangeOfBasePoints





section StalkStructureMap

open CategoryTheory.GrothendieckTopology

variable {B : BigFppfSite.{u₁}} {W T : Scheme.{u₁}} {hW : B.Contains W} {hT : B.Contains T}
  (h : B.obj hW ⟶ B.obj hT)

/-- The stalks of the structure sheaves at matched geometric points over the two bases. -/
def smallerBaseStalkRingIso {Z : AlgebraicSpaces B W hW} {Y : AlgebraicSpaces B T hT}
    (ε : (OverShriek.relocalizePresheafFunctor h).obj Z.1 ≅ Y.1)
    {x' : GeometricPoint B W hW Z.1} {x : GeometricPoint B T hT Y.1}
    (ι : (smallerBaseChartsFunctor h ε).obj (geometricPointChart x') ≅ geometricPointChart x) :
    ((etaleSitePoint B W hW Z.1 x' Z.2).presheafFiber (A := CommRingCat.{u₁})).obj
        (smallEtaleRingedTopos B W hW Z).O.obj ≅
      ((etaleSitePoint B T hT Y.1 x Y.2).presheafFiber (A := CommRingCat.{u₁})).obj
        (smallEtaleRingedTopos B T hT Y).O.obj :=
  Point.presheafFiberIsoOfEquivalence (smallerBaseSmallEtaleEquivalenceOfIso B h ε)
    (etaleSitePoint B W hW Z.1 x' Z.2) (etaleSitePoint B T hT Y.1 x Y.2)
    (smallerBaseFiberIso h ε ι) (smallEtaleRingedTopos B T hT Y).O.obj

/-- `AlgebraicGeometry.Space.smallerBaseStalkRingIso` takes germs to germs. -/
theorem smallerBaseStalkRingIso_hom_germ {Z : AlgebraicSpaces B W hW}
    {Y : AlgebraicSpaces B T hT} (ε : (OverShriek.relocalizePresheafFunctor h).obj Z.1 ≅ Y.1)
    {x' : GeometricPoint B W hW Z.1} {x : GeometricPoint B T hT Y.1}
    (ι : (smallerBaseChartsFunctor h ε).obj (geometricPointChart x') ≅ geometricPointChart x)
    (U : SmallEtale B W hW Z.1) (ξ : GeometricFiber B W hW Z.1 x' U)
    (s : (structurePresheaf B W hW Z.1).obj (op U)) :
    (smallerBaseStalkRingIso h ε ι).hom
        ((etaleSitePoint B W hW Z.1 x' Z.2).toPresheafFiber U ξ
          (smallEtaleRingedTopos B W hW Z).O.obj s) =
      (etaleSitePoint B T hT Y.1 x Y.2).toPresheafFiber
        ((smallerBaseSmallEtaleEquivalenceOfIso B h ε).functor.obj U)
        ((smallerBaseFiberIso h ε ι).hom.app U ξ) (smallEtaleRingedTopos B T hT Y).O.obj s :=
  ConcreteCategory.congr_hom (Point.toPresheafFiber_presheafFiberIsoOfEquivalence_hom
    (smallerBaseSmallEtaleEquivalenceOfIso B h ε) (etaleSitePoint B W hW Z.1 x' Z.2)
    (etaleSitePoint B T hT Y.1 x Y.2) (smallerBaseFiberIso h ε ι)
    (smallEtaleRingedTopos B T hT Y).O.obj U ξ) s

/-- The inverse of `AlgebraicGeometry.Space.smallerBaseStalkRingIso` takes germs to germs. -/
theorem smallerBaseStalkRingIso_inv_germ {Z : AlgebraicSpaces B W hW}
    {Y : AlgebraicSpaces B T hT} (ε : (OverShriek.relocalizePresheafFunctor h).obj Z.1 ≅ Y.1)
    {x' : GeometricPoint B W hW Z.1} {x : GeometricPoint B T hT Y.1}
    (ι : (smallerBaseChartsFunctor h ε).obj (geometricPointChart x') ≅ geometricPointChart x)
    (U : SmallEtale B W hW Z.1) (ξ : GeometricFiber B W hW Z.1 x' U)
    (s : (structurePresheaf B W hW Z.1).obj (op U)) :
    (smallerBaseStalkRingIso h ε ι).inv
        ((etaleSitePoint B T hT Y.1 x Y.2).toPresheafFiber
          ((smallerBaseSmallEtaleEquivalenceOfIso B h ε).functor.obj U)
          ((smallerBaseFiberIso h ε ι).hom.app U ξ) (smallEtaleRingedTopos B T hT Y).O.obj s) =
      (etaleSitePoint B W hW Z.1 x' Z.2).toPresheafFiber U ξ
        (smallEtaleRingedTopos B W hW Z).O.obj s := by
  rw [← smallerBaseStalkRingIso_hom_germ]
  exact ConcreteCategory.congr_hom (smallerBaseStalkRingIso h ε ι).hom_inv_id _

variable {Z₁ Z₂ : AlgebraicSpaces B W hW} {Y₁ Y₂ : AlgebraicSpaces B T hT}
  (ε₁ : (OverShriek.relocalizePresheafFunctor h).obj Z₁.1 ≅ Y₁.1)
  (ε₂ : (OverShriek.relocalizePresheafFunctor h).obj Z₂.1 ≅ Y₂.1) {f : Z₁ ⟶ Z₂} {g : Y₁ ⟶ Y₂}
  (hfg : ε₁.hom ≫ g.hom = (OverShriek.relocalizePresheafFunctor h).map f.hom ≫ ε₂.hom)
  {x' : GeometricPoint B W hW Z₁.1} {x : GeometricPoint B T hT Y₁.1}
  (ι : (smallerBaseChartsFunctor h ε₁).obj (geometricPointChart x') ≅ geometricPointChart x)

include hfg in
/-- A commutative diagram of étale charts over `f`, read over `T`. -/
theorem smallerBase_chartDiagram_comm {U : SmallEtale B W hW Z₁.1} {V : SmallEtale B W hW Z₂.1}
    (g' : U.obj.left ⟶ V.obj.left) (hcomm : U.obj.hom ≫ f.hom = yoneda.map g' ≫ V.obj.hom) :
    ((smallerBaseSmallEtaleEquivalenceOfIso B h ε₁).functor.obj U).1.hom ≫ g.hom =
      yoneda.map ((Over.map h).map g') ≫
        ((smallerBaseSmallEtaleEquivalenceOfIso B h ε₂).functor.obj V).1.hom := by
  show (relocalizeChart B W T hW hT h U.obj.hom ≫ ε₁.hom) ≫ g.hom =
    yoneda.map ((Over.map h).map g') ≫ (relocalizeChart B W T hW hT h V.obj.hom ≫ ε₂.hom)
  rw [Category.assoc, hfg, ← Category.assoc, relocalizeChart_comp, hcomm,
    ← relocalizeChart_naturality, Category.assoc]

/-- **The fibre of the structure map over the smaller base**: at matched geometric points, the
fibre at `x'` of the structure map of `f` is the fibre at `x` of the structure map of `g`, read
through the comparisons of the stalks. -/
theorem stalkStructureMap_smallerBase :
    stalkStructureMap B W hW f x' =
      (smallerBaseStalkRingIso h ε₂ (smallerBasePointChartIsoMap h ε₁ ε₂ hfg ι)).hom ≫
        stalkStructureMap B T hT g x ≫ (smallerBaseStalkRingIso h ε₁ ι).inv := by
  set φ := (smallerBaseStalkRingIso h ε₂ (smallerBasePointChartIsoMap h ε₁ ε₂ hfg ι)).hom ≫
        stalkStructureMap B T hT g x ≫ (smallerBaseStalkRingIso h ε₁ ι).inv with hφ
  have key : IsEtaleLocalRingMap f.hom x'
      (((pointStalkRingEquiv B W hW Z₁ x').toRingHom.comp φ.hom).comp
        (pointStalkRingEquiv B W hW Z₂ (geometricPointMap f.hom x')).symm.toRingHom) := by
    intro U V g' hcomm hpoint
    refine RingHom.ext fun s => ?_
    have hY : (pointStalkRingEquiv B W hW Z₂ (geometricPointMap f.hom x')).symm
        (etaleLocalRingGerm B W hW Z₂.1 (geometricPointMap f.hom x') (op V) s) =
        (etaleSitePoint B W hW Z₂.1 (geometricPointMap f.hom x') Z₂.2).toPresheafFiber V.chart
          ⟨V.point, V.point_comp⟩ (smallEtaleRingedTopos B W hW Z₂).O.obj s := by
      rw [RingEquiv.symm_apply_eq]
      exact (pointStalkRingEquiv_germ_neighborhood B W hW Z₂ _ V s).symm
    have hX := pointStalkRingEquiv_germ_neighborhood B W hW Z₁ x' U
      (Scheme.Γ.map (op ((BigFppfOver.toScheme B W hW).map g')) s)
    let d : ChartDiagram B T hT Y₁.1 Y₂.1 g.hom :=
      ⟨(smallerBaseSmallEtaleEquivalenceOfIso B h ε₁).functor.obj U.chart,
        (smallerBaseSmallEtaleEquivalenceOfIso B h ε₂).functor.obj V.chart,
        (Over.map h).map g', smallerBase_chartDiagram_comm h ε₁ ε₂ hfg g' hcomm⟩
    have hd := stalkStructureMap_toPresheafFiber B T hT g x d
      ((smallerBaseFiberIso h ε₁ ι).hom.app U.chart ⟨U.point, U.point_comp⟩)
      ((smallerBaseFiberIso h ε₂ (smallerBasePointChartIsoMap h ε₁ ε₂ hfg ι)).hom.app V.chart
        ⟨V.point, V.point_comp⟩)
      (smallerBaseFiberIso_hom_app_val_comp h ε₁ ε₂ hfg ι _ _ g' hpoint) s
    show _ = pointStalkRingEquiv B W hW Z₁ x' (φ.hom
      ((pointStalkRingEquiv B W hW Z₂ (geometricPointMap f.hom x')).symm
        (etaleLocalRingGerm B W hW Z₂.1 (geometricPointMap f.hom x') (op V) s)))
    rw [hY, hφ]
    show _ = pointStalkRingEquiv B W hW Z₁ x' ((smallerBaseStalkRingIso h ε₁ ι).inv
      (stalkStructureMap B T hT g x ((smallerBaseStalkRingIso h ε₂
        (smallerBasePointChartIsoMap h ε₁ ε₂ hfg ι)).hom
          ((etaleSitePoint B W hW Z₂.1 (geometricPointMap f.hom x') Z₂.2).toPresheafFiber V.chart
            ⟨V.point, V.point_comp⟩ (smallEtaleRingedTopos B W hW Z₂).O.obj s))))
    have e1 := smallerBaseStalkRingIso_hom_germ h ε₂ (smallerBasePointChartIsoMap h ε₁ ε₂ hfg ι)
      V.chart ⟨V.point, V.point_comp⟩ s
    have e3 := smallerBaseStalkRingIso_inv_germ h ε₁ ι U.chart ⟨U.point, U.point_comp⟩
      (Scheme.Γ.map (op ((BigFppfOver.toScheme B W hW).map g')) s)
    refine hX.symm.trans (congrArg (pointStalkRingEquiv B W hW Z₁ x') ?_)
    refine e3.symm.trans ?_
    refine Eq.trans ?_ (congrArg (fun z => (smallerBaseStalkRingIso h ε₁ ι).inv
      (stalkStructureMap B T hT g x z)) e1).symm
    exact congrArg (fun z => (smallerBaseStalkRingIso h ε₁ ι).inv z) hd.symm
  have huniq := (existsUnique_etaleLocalRingMap Z₁.2 f.hom x').unique key
    (isEtaleLocalRingMap_stalkStructureMap B W hW f x')
  ext z
  have h2 := DFunLike.congr_fun huniq (pointStalkRingEquiv B W hW Z₂ (geometricPointMap f.hom x') z)
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom] at h2
  have h3 := ((pointStalkRingEquiv B W hW Z₁ x').injective h2).symm
  have e := (pointStalkRingEquiv B W hW Z₂ (geometricPointMap f.hom x')).symm_apply_apply z
  exact (congrArg (fun w => (stalkStructureMap B W hW f x').hom w) e).symm.trans
    (h3.trans (congrArg φ.hom e))

end StalkStructureMap



section RestrictScalarsTorAmplitude

attribute [local instance 10000] HasDerivedCategory.standard

variable {R₀ R₁ R₂ : Type u₁} [CommRing R₀] [CommRing R₁] [CommRing R₂]

/-- Derived restriction of scalars along a composite is the composite of derived restrictions of
scalars. -/
def restrictScalarsMapDerivedCompIso (β : R₀ →+* R₁) (σ : R₁ →+* R₂) (τ : R₀ →+* R₂)
    (hτ : τ = σ.comp β) (N : DerivedCategory (ModuleCat.{u₁} R₂)) :
    (ModuleCat.restrictScalars.{u₁} τ).mapDerivedCategory.obj N ≅
      (ModuleCat.restrictScalars.{u₁} β).mapDerivedCategory.obj
        ((ModuleCat.restrictScalars.{u₁} σ).mapDerivedCategory.obj N) :=
  (Functor.mapDerivedCategoryCompIsoOfIso
    (ModuleCat.restrictScalarsComp'.{u₁} β σ τ hτ).symm).app N

/-- **Tor amplitude over a source ring isomorphic to the base ring of a restriction of
scalars.** -/
theorem hasTorAmplitudeCanonical_restrictScalars_iff_of_ringEquiv (ι : R₀ ≃+* R₁)
    (σ : R₁ →+* R₂) (τ : R₀ →+* R₂) (hτ : τ = σ.comp ι.toRingHom)
    (N : DerivedCategory (ModuleCat.{u₁} R₂)) (a b : ℤ) :
    StacksDraft.TorAmplitude.HasTorAmplitudeCanonical R₁
        ((ModuleCat.restrictScalars.{u₁} σ).mapDerivedCategory.obj N) a b ↔
      StacksDraft.TorAmplitude.HasTorAmplitudeCanonical R₀
        ((ModuleCat.restrictScalars.{u₁} τ).mapDerivedCategory.obj N) a b := by
  refine (Scheme.Hom.hasTorAmplitudeCanonical_restrictScalars_ringEquiv_obj_iff ι _ a b).symm.trans
    (hasTorAmplitudeCanonical_iff_of_iso (restrictScalarsMapDerivedCompIso ι.toRingHom σ τ hτ N)
      a b).symm

end RestrictScalarsTorAmplitude


section StalkTorAmplitudeStructureMap

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable (B : BigFppfSite.{u₁}) (S : Scheme.{u₁}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- The Tor amplitude of a geometric stalk read over `(f⁻¹𝒪_Y)_x̄` is its Tor amplitude read over
`𝒪_{Y, f(x̄)}` along the fibre of the structure map (Stacks 04K2). -/
theorem stalkTorAmplitude_iff_stalkStructureMap
    (E : DerivedCategory (Modules.{u₁, u₁} B S hS X.1 X.2)) (x : GeometricPoint B S hS X.1)
    (a b : ℤ) :
    GeometricStalkTorAmplitude B S hS f E x a b ↔
      StacksDraft.TorAmplitude.HasTorAmplitudeCanonical
        (((etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2).sheafFiber
          (A := CommRingCat.{u₁})).obj (smallEtaleRingedTopos B S hS Y).O)
        ((ModuleCat.restrictScalars.{u₁} (stalkStructureMap B S hS f x).hom).mapDerivedCategory.obj
          ((geometricStalkFunctor B S hS x).mapDerivedCategory.obj E)) a b :=
  hasTorAmplitudeCanonical_restrictScalars_iff_of_ringEquiv
    ((smallEtaleInverseImageFiberRingIso B S hS f x).app
      (smallEtaleRingedTopos B S hS Y).O).commRingCatIsoToRingEquiv
    (inverseImageStalkRingHom B S hS f x) (stalkStructureMap B S hS f x).hom
    (RingHom.ext fun z => (inverseImageStalkRingHom_fiberRingIso B S hS f x z).symm) _ a b

end StalkTorAmplitudeStructureMap


section MatchedStalks

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {B : BigFppfSite.{u₁}} {W T : Scheme.{u₁}} {hW : B.Contains W} {hT : B.Contains T}
  (h : B.obj hW ⟶ B.obj hT)

/-- `AlgebraicGeometry.Space.smallerBaseStalkRingIso` as a ring homomorphism, with its source and
target spelled as the stalks of the structure sheaves of the small étale ringed sites. -/
abbrev smallerBaseStalkRingHom {Z : AlgebraicSpaces B W hW} {Y : AlgebraicSpaces B T hT}
    (ε : (OverShriek.relocalizePresheafFunctor h).obj Z.1 ≅ Y.1)
    {x' : GeometricPoint B W hW Z.1} {x : GeometricPoint B T hT Y.1}
    (ι : (smallerBaseChartsFunctor h ε).obj (geometricPointChart x') ≅ geometricPointChart x) :
    ((etaleSitePoint B W hW Z.1 x' Z.2).presheafFiber (A := CommRingCat.{u₁})).obj
        (smallEtaleRingedSite B W hW Z.1 Z.2).O.obj ⟶
      ((etaleSitePoint B T hT Y.1 x Y.2).presheafFiber (A := CommRingCat.{u₁})).obj
        (smallEtaleRingedSite B T hT Y.1 Y.2).O.obj :=
  (smallerBaseStalkRingIso h ε ι).hom

/-- **The derived geometric stalks over the smaller base**: at matched geometric points, the
derived stalk of the object corresponding to `E` is the derived stalk of `E`, with its scalars
restricted along the comparison of the stalks of the structure sheaves. -/
def smallerBaseDerivedStalkIso {Z : AlgebraicSpaces B W hW} {Y : AlgebraicSpaces B T hT}
    (ε : (OverShriek.relocalizePresheafFunctor h).obj Z.1 ≅ Y.1)
    {x' : GeometricPoint B W hW Z.1} {x : GeometricPoint B T hT Y.1}
    (ι : (smallerBaseChartsFunctor h ε).obj (geometricPointChart x') ≅ geometricPointChart x)
    (E : DerivedCategory (Modules.{u₁, u₁} B T hT Y.1 Y.2)) :
    (geometricStalkFunctor B W hW x').mapDerivedCategory.obj
        ((smallerBaseDerivedEquivalence B h ε).functor.obj E) ≅
      (ModuleCat.restrictScalars.{u₁} (smallerBaseStalkRingHom h ε ι).hom).mapDerivedCategory.obj
        ((geometricStalkFunctor B T hT x).mapDerivedCategory.obj E) :=
  let N : (smallerBaseModulesEquivalenceOfIso B h ε).functor ⋙ geometricStalkFunctor B W hW x' ≅
      geometricStalkFunctor B T hT x ⋙
        ModuleCat.restrictScalars.{u₁} (smallerBaseStalkRingHom h ε ι).hom :=
    Stacks.reindexModuleStalkNatIso (smallerBaseSmallEtaleEquivalenceOfIso B h ε)
      (etaleSitePoint B W hW Z.1 x' Z.2) (etaleSitePoint B T hT Y.1 x Y.2)
      (smallerBaseFiberIso h ε ι) (smallEtaleRingedTopos B T hT Y).O
      (J' := SmallEtale.topology B W hW Z.1)
  let K := DerivedCategory.Q.objPreimage E
  let eK : DerivedCategory.Q.obj K ≅ E := DerivedCategory.Q.objObjPreimageIso E
  let F₂ := geometricStalkFunctor B W hW x'
  let G₁ := geometricStalkFunctor B T hT x
  let G₂ := ModuleCat.restrictScalars.{u₁} (smallerBaseStalkRingHom h ε ι).hom
  let Φ := (smallerBaseModulesEquivalenceOfIso B h ε).functor
  let c : (F₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≅
      (G₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((G₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
    HomologicalComplex.Hom.isoOfComponents (fun i => N.app (K.X i))
      (fun i j _ => (N.hom.naturality (K.d i j)).symm)
  F₂.mapDerivedCategory.mapIso ((smallerBaseDerivedEquivalence B h ε).functor.mapIso eK.symm) ≪≫
    F₂.mapDerivedCategory.mapIso ((smallerBaseDerivedEquivalenceFactors B h ε).app K) ≪≫
    F₂.mapDerivedCategoryFactors.app ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≪≫
    DerivedCategory.Q.mapIso c ≪≫
    (G₂.mapDerivedCategoryFactors.app
      ((G₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).symm ≪≫
    G₂.mapDerivedCategory.mapIso (G₁.mapDerivedCategoryFactors.app K).symm ≪≫
    G₂.mapDerivedCategory.mapIso (G₁.mapDerivedCategory.mapIso eK)

variable {Z₁ Z₂ : AlgebraicSpaces B W hW} {Y₁ Y₂ : AlgebraicSpaces B T hT}
  (ε₁ : (OverShriek.relocalizePresheafFunctor h).obj Z₁.1 ≅ Y₁.1)
  (ε₂ : (OverShriek.relocalizePresheafFunctor h).obj Z₂.1 ≅ Y₂.1) {f : Z₁ ⟶ Z₂} {g : Y₁ ⟶ Y₂}
  (hfg : ε₁.hom ≫ g.hom = (OverShriek.relocalizePresheafFunctor h).map f.hom ≫ ε₂.hom)
  {x' : GeometricPoint B W hW Z₁.1} {x : GeometricPoint B T hT Y₁.1}
  (ι : (smallerBaseChartsFunctor h ε₁).obj (geometricPointChart x') ≅ geometricPointChart x)

include hfg ι in
/-- **Stalkwise relative Tor amplitude over the smaller base**: at matched geometric points, the
Tor amplitude of the geometric stalk of `E` read over the target of `g` is that of the
corresponding object read over the target of `f`. -/
theorem stalkTorAmplitude_smallerBase_iff (E : DerivedCategory (Modules.{u₁, u₁} B T hT Y₁.1 Y₁.2))
    (a b : ℤ) :
    GeometricStalkTorAmplitude B T hT g E x a b ↔
      GeometricStalkTorAmplitude B W hW f ((smallerBaseDerivedEquivalence B h ε₁).functor.obj E)
        x' a b := by
  rw [stalkTorAmplitude_iff_stalkStructureMap, stalkTorAmplitude_iff_stalkStructureMap]
  refine (hasTorAmplitudeCanonical_restrictScalars_iff_of_ringEquiv
    (smallerBaseStalkRingIso h ε₂
      (smallerBasePointChartIsoMap h ε₁ ε₂ hfg ι)).commRingCatIsoToRingEquiv
    (stalkStructureMap B T hT g x).hom
    ((smallerBaseStalkRingHom h ε₁ ι).hom.comp (stalkStructureMap B W hW f x').hom) ?_ _ a b).trans
    (hasTorAmplitudeCanonical_iff_of_iso
      (restrictScalarsMapDerivedCompIso (stalkStructureMap B W hW f x').hom
        (smallerBaseStalkRingHom h ε₁ ι).hom _ rfl _ ≪≫
        (ModuleCat.restrictScalars.{u₁}
          (stalkStructureMap B W hW f x').hom).mapDerivedCategory.mapIso
          (smallerBaseDerivedStalkIso h ε₁ ι E).symm) a b)
  rw [stalkStructureMap_smallerBase h ε₁ ε₂ hfg ι]
  ext z
  exact ConcreteCategory.congr_hom (smallerBaseStalkRingIso h ε₁ ι).inv_hom_id _

include hfg in
/-- **The local stalk bound over the smaller base.** -/
theorem hasLocalStalkTorBound_smallerBase_iff
    (E : DerivedCategory (Modules.{u₁, u₁} B T hT Y₁.1 Y₁.2)) :
    HasLocalStalkTorBound B T hT g E ↔
      HasLocalStalkTorBound B W hW f ((smallerBaseDerivedEquivalence B h ε₁).functor.obj E) := by
  let e := smallerBaseSmallEtaleEquivalenceOfIso B h ε₁
  have hF : e.functor.IsCocontinuous (smallEtaleRingedSite B W hW Z₁.1 Z₁.2).J
      (smallEtaleRingedSite B T hT Y₁.1 Y₁.2).J :=
    (e.toAdjunction.isCocontinuous_iff_coverPreserving _ _).2
      (CoverPreserving.of_isContinuous _ _ _)
  have hG : e.inverse.IsCocontinuous (smallEtaleRingedSite B T hT Y₁.1 Y₁.2).J
      (smallEtaleRingedSite B W hW Z₁.1 Z₁.2).J :=
    (e.symm.toAdjunction.isCocontinuous_iff_coverPreserving _ _).2
      (CoverPreserving.of_isContinuous (F := e.functor) _ _)
  constructor
  · intro hY U'
    obtain ⟨R, hR, hb⟩ := hY (e.functor.obj U')
    refine ⟨R.functorPullback e.functor, e.functor.cover_lift _ _ hR, fun V' k' hk' => ?_⟩
    obtain ⟨a, b, hab⟩ := hb (e.functor.map k') hk'
    refine ⟨a, b, fun x' ξ' => ?_⟩
    let ι := smallerBasePointChartIso h ε₁ x'
    exact (stalkTorAmplitude_smallerBase_iff h ε₁ ε₂ hfg ι E a b).1
      (hab _ ((smallerBaseFiberIso h ε₁ ι).hom.app V' ξ'))
  · intro hZ U
    obtain ⟨R', hR', hb⟩ := hZ (e.inverse.obj U)
    refine ⟨R'.functorPullback e.inverse, e.inverse.cover_lift _ _ hR', fun V k hk => ?_⟩
    obtain ⟨a, b, hab⟩ := hb (e.inverse.map k) hk
    refine ⟨a, b, fun x ξ => ?_⟩
    let ι := smallerBasePointChartIsoOfDerelocalize h ε₁ x
    exact (stalkTorAmplitude_smallerBase_iff h ε₁ ε₂ hfg ι E a b).2
      (hab _ ((smallerBaseFiberIso h ε₁ ι).inv.app (e.inverse.obj V)
        ((etaleSitePoint B T hT Y₁.1 x Y₁.2).fiber.map (e.counitIso.inv.app V) ξ)))

end MatchedStalks


attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance] AlgebraicGeometry.Space.inverseImageRingedSite_hasWeakSheafify_over
  AlgebraicGeometry.Space.inverseImageRingedSite_wEqualsLocallyBijective_over
  AlgebraicGeometry.Space.inverseImageRingedSite_hasDerivedCategory
  Stacks.hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.RingedSite.sliceHasSheafify
  AlgebraicGeometry.RingedSite.sliceWEqualsLocallyBijective
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteLimits
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteColimits
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasDerivedCategory
  AlgebraicGeometry.RingedSite.sliceHasDerivedCategory
  Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_obj_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasMapBifunctor
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor
  AlgebraicGeometry.Space.instModulesHasDerivedCategory

section ChangeOfBase

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u₁}) {W T : Scheme.{u₁}} {hW : B.Contains W} {hT : B.Contains T}
  (h : B.obj hW ⟶ B.obj hT)

/-- **Relative perfectness over the smaller base** (Stacks 0DKN read through Stacks 04SG): the
proposition `AlgebraicGeometry.Space.SmallerBaseRelativelyPerfectComparison` holds.

Pseudo-coherence is `AlgebraicGeometry.Space.isPseudoCoherent_smallerBaseDerivedEquivalence_iff`.
The Tor clause is read at the geometric stalks, locally on the small étale site
(`AlgebraicGeometry.Space.locallyHasFiniteTorDimension_derivedScalarRestriction_iff`): a geometric
point over `W` and its extension over `T` have the same fibre functor along the equivalence of
small étale sites (`AlgebraicGeometry.Space.smallerBaseFiberIso`), every geometric point over `T`
arises so (`AlgebraicGeometry.Space.smallerBasePointChartIsoOfDerelocalize`), the stalks of the
structure sheaves and of the modules correspond, and so do the fibres of the structure maps, by
the uniqueness clause of Stacks 04NG (`AlgebraicGeometry.Space.stalkStructureMap_smallerBase`). -/
theorem smallerBaseRelativelyPerfectComparison : SmallerBaseRelativelyPerfectComparison B h := by
  intro Z₁ Z₂ Y₁ Y₂ ε₁ ε₂ f g hfg hgfl hglfp hffl hflfp K
  refine and_congr (isPseudoCoherent_smallerBaseDerivedEquivalence_iff B h ε₁ K).symm ?_
  exact (locallyHasFiniteTorDimension_derivedScalarRestriction_iff B T hT g _ K).trans
    ((hasLocalStalkTorBound_smallerBase_iff h ε₁ ε₂ hfg K).trans
      (locallyHasFiniteTorDimension_derivedScalarRestriction_iff B W hW f _ _).symm)

end ChangeOfBase

end AlgebraicGeometry.Space
