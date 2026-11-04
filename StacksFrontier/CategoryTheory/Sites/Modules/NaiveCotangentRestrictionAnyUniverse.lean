module

public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentRestriction

/-!
# Restriction of the naive cotangent complex along a functor of sites of different sizes

This is `StacksFrontier/CategoryTheory/Sites/Modules/NaiveCotangentRestriction.lean` with the two
sites in independent universes: `C : Type u₁` with morphisms in `Type v₁` and `D : Type u₂` with
morphisms in `Type v₂`. For a continuous and cocontinuous functor `G : C ⥤ D` whose restriction
functor is the inverse image of a morphism of topoi, and a homomorphism `b : A ⟶ B` of sheaves of
commutative rings on `D`, the restriction of the naive cotangent complex is the naive cotangent
complex of the restriction:

`G^s NL_{B/A} ≅ NL_{G^sB/G^sA}`,

as complexes of sheaves of modules with sections in `max w u₁ v₁ u₂ v₂ z`. On `D` the complex is
`NL_{B/A}` formed at the free parameter `max u₁ v₁ z`, on `C` at `max u₂ v₂ z`, so that both have
their sections in the same universe. This is Stacks 08TZ for the morphism of topoi attached to
`G`, and is how the small étale site of an algebraic space, whose objects lie in `Type (u + 1)`,
is compared with its model in `Type u`. The constructions and proofs are those of the
same-universe file, which is used for the identification of free algebra sheaves along
isomorphisms (`Stacks.SheafOfModules.canonicalFreeAlgebraIsoOfIso`).

## Main definitions

* `Stacks.Sites.Conormal.restrictionConormalSequenceIsoAnyUniverse`: restriction of the conormal
  sequence of a presentation.
* `Stacks.SheafOfModules.restrictionFreeAlgebraIsoAnyUniverse`: `G^s(A[B]) ≅ (G^sA)[G^sB]`.
* `Stacks.SheafOfModules.restrictionNaiveCotangentComplexIsoAnyUniverse`:
  `G^s NL_{B/A} ≅ NL_{G^sB/G^sA}`.

## References

* [Stacks Project, Tag 08TZ](https://stacks.math.columbia.edu/tag/08TZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v₁ u₁ v₂ u₂ w z

attribute [local instance] AlgebraicGeometry.SheafOfModules.siteHasSheafify
  AlgebraicGeometry.SheafOfModules.siteWEqualsLocallyBijective

namespace Stacks.Sites.Conormal

open Stacks.SheafOfModules.PushforwardSheafification

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  {D : Type u₂} [Category.{v₂} D] (K : GrothendieckTopology D)

variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (G : C ⥤ D) [G.IsContinuous J K] [G.IsCocontinuous J K]
  (R A B : Sheaf K CommRingCat.{w}) (a : R ⟶ A) (φ : A ⟶ B)

/-- The sheaf of rings underlying `G^sB` is the restriction along `G` of the sheaf of rings
underlying `B`: the two agree by definition, and this is the identity between them, at the
spelling `SheafOfModules.pushforward` consumes. -/
def ringSheafRestrictionHomAnyUniverse :
    Stacks.SheafOfModules.Tensor.ringSheaf
        ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj B) ⟶
      (G.sheafPushforwardContinuous RingCat.{w} J K).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf B) :=
  𝟙 _

/-- Restriction of sheaves of modules over the sheaf of rings underlying `B` along `G`, read as
sheaves of modules over the sheaf of rings underlying `G^sB`, which is the sheaf of rings the
naive cotangent complex of `G^sB` is a complex of modules over. On sections it is `M ↦ M ∘ G`. -/
noncomputable abbrev ringSheafModuleRestrictionAnyUniverse.{t} :
    _root_.SheafOfModules.{t} (Stacks.SheafOfModules.Tensor.ringSheaf B) ⥤
      _root_.SheafOfModules.{t}
        (Stacks.SheafOfModules.Tensor.ringSheaf
            ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj B)) :=
  _root_.SheafOfModules.pushforward.{t} (ringSheafRestrictionHomAnyUniverse J K G B)

/-- Restricting a locally surjective homomorphism of sheaves of rings along a cocontinuous
functor keeps it locally surjective. -/
instance isLocallySurjective_ringRestriction_mapAnyUniverse [Presheaf.IsLocallySurjective K φ.hom] :
    Presheaf.IsLocallySurjective J ((G.sheafPushforwardContinuous CommRingCat.{w} J K).map φ).hom :=
  Presheaf.isLocallySurjective_whisker J K G φ.hom

variable [Presheaf.IsLocallySurjective K φ.hom]

/-- **The restriction of the conormal sequence of a presentation is the conormal sequence of the
restricted presentation**: for a locally surjective `φ : A ⟶ B` over `a : R ⟶ A`, restriction
along `G` carries the conormal sequence `I/I² ⟶ B ⊗_A Ω_{A/R} ⟶ Ω_{B/R}` to the conormal sequence
of `G^sφ` over `G^sa`. All three terms are sheafifications of objectwise constructions, which
restriction commutes with on the nose, and restriction commutes with the sheafification. -/
noncomputable def restrictionConormalSequenceIsoAnyUniverse :
    (conormalSequence.{v₂, u₂, w, max u₁ v₁ z} K R A B a φ).map
        (ringSheafModuleRestrictionAnyUniverse.{v₁, u₁, v₂, u₂, w, max w u₁ v₁ u₂ v₂ z} J K G B) ≅
      conormalSequence.{v₁, u₁, w, max u₂ v₂ z} J
          ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj R)
        ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj A)
            ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj B)
        ((G.sheafPushforwardContinuous CommRingCat.{w} J K).map a)
            ((G.sheafPushforwardContinuous CommRingCat.{w} J K).map φ) :=
  (ShortComplex.mapNatIso ((conormalPresheafComplex φ.hom a.hom).map
      (liftModules.{v₂, u₂, w, max u₁ v₁ z} _))
    (pushforwardSheafifyNatIsoAlong.{max w u₁ v₁ u₂ v₂ z} J G (quotientToRingSheaf K A B φ))).symm

end Stacks.Sites.Conormal

namespace Stacks.SheafOfModules

open Stacks.Sites.FreeAlgebra Stacks.Sites.Conormal Stacks.Sheaves.ToposPullback
open Stacks.SheafOfModules.PushforwardSheafification

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  {D : Type u₂} [Category.{v₂} D] (K : GrothendieckTopology D)

section Restriction

variable [HasWeakSheafify J CommRingCat.{w}] [HasWeakSheafify K CommRingCat.{w}]
  [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w})]
  [J.HasSheafCompose (forget CommRingCat.{w})] [K.HasSheafCompose (forget CommRingCat.{w})]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (G : C ⥤ D) [G.IsContinuous J K]
  [PreservesFiniteProducts (G.sheafPushforwardContinuous (Type w) J K)]
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w)))
  (e : f.inverseImage ≅ G.sheafPushforwardContinuous (Type w) J K)
  (A B : Sheaf K CommRingCat.{w}) (b : A ⟶ B)

/-- **The restriction of the free algebra is the free algebra of the restriction**:
`G^s(A[B]) ≅ (G^sA)[G^sB]`, for a functor of sites `G` whose restriction functor is the inverse
image of a morphism of topoi `f`. It is the identification of restriction with `f⁻¹`, then
`f⁻¹(A[B]) ≅ (f⁻¹A)[f⁻¹B]`, then the identification of restriction with `f⁻¹` on coefficients
and on variables. -/
noncomputable def restrictionFreeAlgebraIsoAnyUniverse :
    (G.sheafPushforwardContinuous CommRingCat.{w} J K).obj (freeAlgebraSheaf K A
        (underlyingPresheaf K B)) ≅
      freeAlgebraSheaf J ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj A)
        (underlyingPresheaf J ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj B)) :=
  (inverseImageCommRingRestrictionIso J K G f e _).symm ≪≫ inverseImageFreeAlgebraIso f A B ≪≫
    canonicalFreeAlgebraIsoOfIso J (inverseImageCommRingRestrictionIso J K G f e A)
      (inverseImageCommRingRestrictionIso J K G f e B)

omit [J.HasSheafCompose (forget CommRingCat.{w})]
    [K.HasSheafCompose (forget CommRingCat.{w})] in
/-- The forward map of `Stacks.SheafOfModules.restrictionFreeAlgebraIsoAnyUniverse` is the
composite of the three comparisons it is built from. -/
theorem restrictionFreeAlgebraIso_homAnyUniverse :
    (restrictionFreeAlgebraIsoAnyUniverse J K G f e A B).hom =
      (inverseImageCommRingRestrictionIso J K G f e
          (freeAlgebraSheaf K A (underlyingPresheaf K B))).inv ≫
        inverseImageFreeAlgebraHom f A B ≫
          canonicalFreeAlgebraMapOfSquare J (f.inverseImageRing.obj A)
            ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj A) (f.inverseImageRing.obj B)
            ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj B)
                (inverseImageCommRingRestrictionIso J K G f e A).hom
            (inverseImageCommRingRestrictionIso J K G f e B).hom :=
  rfl

/-- The identification `G^s(A[B]) ≅ (G^sA)[G^sB]` is one of `G^sA`-algebras. -/
theorem map_coefficientMap_comp_restrictionFreeAlgebraIsoAnyUniverse :
    (G.sheafPushforwardContinuous CommRingCat.{w} J K).map (freeAlgebraSheafCoefficientMap K A
        (underlyingPresheaf K B)) ≫
        (restrictionFreeAlgebraIsoAnyUniverse J K G f e A B).hom =
      freeAlgebraSheafCoefficientMap J ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj A)
        (underlyingPresheaf J ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj B)) := by
  have ha : (G.sheafPushforwardContinuous CommRingCat.{w} J K).map
        (freeAlgebraSheafCoefficientMap K A (underlyingPresheaf K B)) ≫
        (inverseImageCommRingRestrictionIso J K G f e
          (freeAlgebraSheaf K A (underlyingPresheaf K B))).inv =
      (inverseImageCommRingRestrictionIso J K G f e A).inv ≫
        f.inverseImageRing.map (freeAlgebraSheafCoefficientMap K A (underlyingPresheaf K B)) :=
    inverseImageCommRingRestrictionIso_inv_naturality J K G f e _
  have hc := freeAlgebraSheafCoefficientMap_comp_freeAlgebraMapOfSquare J
    (f.inverseImageRing.obj A) ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj A)
    (underlyingPresheaf J (f.inverseImageRing.obj B))
    (underlyingPresheaf J ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj B))
    (inverseImageCommRingRestrictionIso J K G f e A).hom
    (underlyingPresheafMap J _ _ (inverseImageCommRingRestrictionIso J K G f e B).hom)
  rw [restrictionFreeAlgebraIso_homAnyUniverse]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) ha).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ _) (map_coefficientMap_comp_inverseImageFreeAlgebraHom f A B)).trans
            hc))).trans (Iso.inv_hom_id_assoc _ _))))

/-- The identification `G^s(A[B]) ≅ (G^sA)[G^sB]` carries the restriction of the canonical
presentation of `B` to the canonical presentation of `G^sB`. -/
theorem restrictionFreeAlgebraIso_comp_canonicalPresentationAnyUniverse :
    (restrictionFreeAlgebraIsoAnyUniverse J K G f e A B).hom ≫
        canonicalPresentation J ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj A)
            ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj B)
          ((G.sheafPushforwardContinuous CommRingCat.{w} J K).map b) =
      (G.sheafPushforwardContinuous CommRingCat.{w} J K).map (canonicalPresentation K A B b) := by
  have hsq : f.inverseImageRing.map b ≫ (inverseImageCommRingRestrictionIso J K G f e B).hom =
      (inverseImageCommRingRestrictionIso J K G f e A).hom ≫
          (G.sheafPushforwardContinuous CommRingCat.{w} J K).map b :=
    inverseImageCommRingRestrictionIso_naturality J K G f e b
  have hd := freeAlgebraMapOfSquare_comp_canonicalPresentation J
    (f.inverseImageRing.obj A) ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj A)
    (f.inverseImageRing.obj B) ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj B)
    (f.inverseImageRing.map b) ((G.sheafPushforwardContinuous CommRingCat.{w} J K).map b)
    (inverseImageCommRingRestrictionIso J K G f e A).hom
    (inverseImageCommRingRestrictionIso J K G f e B).hom hsq
  have hf : f.inverseImageRing.map (canonicalPresentation K A B b) ≫
        (inverseImageCommRingRestrictionIso J K G f e B).hom =
      (inverseImageCommRingRestrictionIso J K G f e
          (freeAlgebraSheaf K A (underlyingPresheaf K B))).hom ≫
        (G.sheafPushforwardContinuous CommRingCat.{w} J K).map (canonicalPresentation K A B b) :=
    inverseImageCommRingRestrictionIso_naturality J K G f e _
  rw [restrictionFreeAlgebraIso_homAnyUniverse]
  exact (Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) hd).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ _)
          (inverseImageFreeAlgebraHom_comp_canonicalPresentation f A B b)).trans hf))))).trans
      (Iso.inv_hom_id_assoc _ _))

variable [G.IsCocontinuous J K]

/-- **The restriction of the naive cotangent complex along a continuous and cocontinuous functor
of sites is the naive cotangent complex of the restriction**: `G^s NL_{B/A} ≅ NL_{G^sB/G^sA}`,
as an isomorphism of two-term complexes of sheaves of `G^sB`-modules, for a functor `G` whose
restriction functor on sheaves of sets is the inverse image of a morphism of topoi `f`.

In degree `-1` it is the restriction of the conormal sheaf of `A[B] ⟶ B`, identified with the
conormal sheaf of `G^s(A[B]) ⟶ G^sB` and then, along the isomorphism of presentations
`G^s(A[B]) ≅ (G^sA)[G^sB]`, with that of the canonical presentation of `G^sB`; in degree `0` it
is the same for the scalar extension of the differentials. This is Stacks 08TZ for the morphism
of topoi attached to `G`. -/
noncomputable def restrictionNaiveCotangentComplexIsoAnyUniverse :
    ((ringSheafModuleRestrictionAnyUniverse.{v₁, u₁, v₂, u₂, w, max w u₁ v₁ u₂ v₂ z} J K G
        B).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (naiveCotangentComplex.{v₂, u₂, w, max u₁ v₁ z} K A B b) ≅
      naiveCotangentComplex.{v₁, u₁, w, max u₂ v₂ z} J
          ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj A)
        ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj B)
            ((G.sheafPushforwardContinuous CommRingCat.{w} J K).map b) := by
  letI : HasZeroObject (_root_.SheafOfModules.{max w u₁ v₁ u₂ v₂ z} (Tensor.ringSheaf B)) :=
    hasZeroObject_of_hasTerminal_object
  letI : HasZeroObject (_root_.SheafOfModules.{max w u₁ v₁ u₂ v₂ z}
      (Tensor.ringSheaf ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj B))) :=
    hasZeroObject_of_hasTerminal_object
  let E := restrictionConormalSequenceIsoAnyUniverse.{v₁, u₁, v₂, u₂, w, z} J K G A
    (freeAlgebraSheaf K A (underlyingPresheaf K B)) B
    (freeAlgebraSheafCoefficientMap K A (underlyingPresheaf K B)) (canonicalPresentation K A B b)
  let E₁ :
      (ringSheafModuleRestrictionAnyUniverse.{v₁, u₁, v₂, u₂, w, max w u₁ v₁ u₂ v₂ z} J K G B).obj
        (canonicalConormalSequence.{v₂, u₂, w, max u₁ v₁ z} K A B b).X₁ ≅
      (conormalSequence.{v₁, u₁, w, max u₂ v₂ z} J
          ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj A)
        ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj (freeAlgebraSheaf K A
            (underlyingPresheaf K B)))
        ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj B)
        ((G.sheafPushforwardContinuous CommRingCat.{w} J K).map (freeAlgebraSheafCoefficientMap K A
            (underlyingPresheaf K B)))
        ((G.sheafPushforwardContinuous CommRingCat.{w} J K).map
            (canonicalPresentation K A B b))).X₁ :=
    ShortComplex.π₁.mapIso E
  let E₂ :
      (ringSheafModuleRestrictionAnyUniverse.{v₁, u₁, v₂, u₂, w, max w u₁ v₁ u₂ v₂ z} J K G B).obj
        (canonicalConormalSequence.{v₂, u₂, w, max u₁ v₁ z} K A B b).X₂ ≅
      (conormalSequence.{v₁, u₁, w, max u₂ v₂ z} J
          ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj A)
        ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj (freeAlgebraSheaf K A
            (underlyingPresheaf K B)))
        ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj B)
        ((G.sheafPushforwardContinuous CommRingCat.{w} J K).map (freeAlgebraSheafCoefficientMap K A
            (underlyingPresheaf K B)))
        ((G.sheafPushforwardContinuous CommRingCat.{w} J K).map
            (canonicalPresentation K A B b))).X₂ :=
    ShortComplex.π₂.mapIso E
  let c : (conormalSequence.{v₁, u₁, w, max u₂ v₂ z} J
      ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj A)
        ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj (freeAlgebraSheaf K A
            (underlyingPresheaf K B)))
        ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj B)
        ((G.sheafPushforwardContinuous CommRingCat.{w} J K).map (freeAlgebraSheafCoefficientMap K A
            (underlyingPresheaf K B)))
        ((G.sheafPushforwardContinuous CommRingCat.{w} J K).map
            (canonicalPresentation K A B b))).X₁ ≅
      (canonicalConormalSequence.{v₁, u₁, w, max u₂ v₂ z} J
          ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj A)
        ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj B)
            ((G.sheafPushforwardContinuous CommRingCat.{w} J K).map b)).X₁ :=
    conormalSheafIsoOfFac.{v₁, u₁, w, max u₂ v₂ z} J
        ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj B)
      ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj (freeAlgebraSheaf K A
          (underlyingPresheaf K B)))
      (freeAlgebraSheaf J ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj A)
        (underlyingPresheaf J ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj B)))
      ((G.sheafPushforwardContinuous CommRingCat.{w} J K).map (canonicalPresentation K A B b))
      (canonicalPresentation J ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj A)
          ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj B)
        ((G.sheafPushforwardContinuous CommRingCat.{w} J K).map b))
      (restrictionFreeAlgebraIsoAnyUniverse J K G f e A B)
      (restrictionFreeAlgebraIso_comp_canonicalPresentationAnyUniverse J K G f e A B b)
  let t : (conormalSequence.{v₁, u₁, w, max u₂ v₂ z} J
      ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj A)
        ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj (freeAlgebraSheaf K A
            (underlyingPresheaf K B)))
        ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj B)
        ((G.sheafPushforwardContinuous CommRingCat.{w} J K).map (freeAlgebraSheafCoefficientMap K A
            (underlyingPresheaf K B)))
        ((G.sheafPushforwardContinuous CommRingCat.{w} J K).map
            (canonicalPresentation K A B b))).X₂ ≅
      (canonicalConormalSequence.{v₁, u₁, w, max u₂ v₂ z} J
          ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj A)
        ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj B)
            ((G.sheafPushforwardContinuous CommRingCat.{w} J K).map b)).X₂ :=
    tensorSheafIsoOfFac.{v₁, u₁, w, max u₂ v₂ z} J
        ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj A)
      ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj B)
      ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj (freeAlgebraSheaf K A
          (underlyingPresheaf K B)))
      (freeAlgebraSheaf J ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj A)
        (underlyingPresheaf J ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj B)))
      ((G.sheafPushforwardContinuous CommRingCat.{w} J K).map (freeAlgebraSheafCoefficientMap K A
          (underlyingPresheaf K B)))
      (freeAlgebraSheafCoefficientMap J ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj A)
        (underlyingPresheaf J ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj B)))
      ((G.sheafPushforwardContinuous CommRingCat.{w} J K).map (canonicalPresentation K A B b))
      (canonicalPresentation J ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj A)
          ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj B)
        ((G.sheafPushforwardContinuous CommRingCat.{w} J K).map b))
      (restrictionFreeAlgebraIsoAnyUniverse J K G f e A B)
      (restrictionFreeAlgebraIso_comp_canonicalPresentationAnyUniverse J K G f e A B b)
      (map_coefficientMap_comp_restrictionFreeAlgebraIsoAnyUniverse J K G f e A B)
  have k₁ : E₁.hom ≫ (conormalSequence.{v₁, u₁, w, max u₂ v₂ z} J
      ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj A)
        ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj (freeAlgebraSheaf K A
            (underlyingPresheaf K B)))
        ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj B)
        ((G.sheafPushforwardContinuous CommRingCat.{w} J K).map (freeAlgebraSheafCoefficientMap K A
            (underlyingPresheaf K B)))
        ((G.sheafPushforwardContinuous CommRingCat.{w} J K).map
            (canonicalPresentation K A B b))).f =
      (ringSheafModuleRestrictionAnyUniverse.{v₁, u₁, v₂, u₂, w, max w u₁ v₁ u₂ v₂ z} J K G B).map
        (canonicalConormalSequence.{v₂, u₂, w, max u₁ v₁ z} K A B b).f ≫ E₂.hom :=
    E.hom.comm₁₂
  have k₂ : c.hom ≫ (canonicalConormalSequence.{v₁, u₁, w, max u₂ v₂ z} J
      ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj A)
        ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj B)
            ((G.sheafPushforwardContinuous CommRingCat.{w} J K).map b)).f =
      (conormalSequence.{v₁, u₁, w, max u₂ v₂ z} J
          ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj A)
        ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj (freeAlgebraSheaf K A
            (underlyingPresheaf K B)))
        ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj B)
        ((G.sheafPushforwardContinuous CommRingCat.{w} J K).map (freeAlgebraSheafCoefficientMap K A
            (underlyingPresheaf K B)))
        ((G.sheafPushforwardContinuous CommRingCat.{w} J K).map
            (canonicalPresentation K A B b))).f ≫ t.hom :=
    conormalSheafIsoOfFac_hom_comp_conormalSequence_f.{v₁, u₁, w, max u₂ v₂ z} J
      ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj A)
          ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj B)
      ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj (freeAlgebraSheaf K A
          (underlyingPresheaf K B)))
      (freeAlgebraSheaf J ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj A)
        (underlyingPresheaf J ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj B)))
      ((G.sheafPushforwardContinuous CommRingCat.{w} J K).map (freeAlgebraSheafCoefficientMap K A
          (underlyingPresheaf K B)))
      (freeAlgebraSheafCoefficientMap J ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj A)
        (underlyingPresheaf J ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj B)))
      ((G.sheafPushforwardContinuous CommRingCat.{w} J K).map (canonicalPresentation K A B b))
      (canonicalPresentation J ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj A)
          ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj B)
        ((G.sheafPushforwardContinuous CommRingCat.{w} J K).map b))
      (restrictionFreeAlgebraIsoAnyUniverse J K G f e A B)
      (restrictionFreeAlgebraIso_comp_canonicalPresentationAnyUniverse J K G f e A B b)
      (map_coefficientMap_comp_restrictionFreeAlgebraIsoAnyUniverse J K G f e A B)
  refine HomologicalComplex.isoFromMapDouble
    (ringSheafModuleRestrictionAnyUniverse.{v₁, u₁, v₂, u₂, w, max w u₁ v₁ u₂ v₂ z} J K G B)
    (canonicalConormalSequence.{v₂, u₂, w, max u₁ v₁ z} K A B b).f
    (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) (by decide)
    ((E₁ ≪≫ c).trans
      (naiveCotangentComplexXNegOneIso.{u₁, v₁, w, max u₂ v₂ z} J
          ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj A)
        ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj B)
            ((G.sheafPushforwardContinuous CommRingCat.{w} J K).map b)).symm)
    ((E₂ ≪≫ t).trans
      (naiveCotangentComplexXZeroIso.{u₁, v₁, w, max u₂ v₂ z} J
          ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj A)
        ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj B)
            ((G.sheafPushforwardContinuous CommRingCat.{w} J K).map b)).symm) ?_ ?_ ?_
  · rw [naiveCotangentComplex_d_negOne_zero_iso.{u₁, v₁, w, max u₂ v₂ z} J
      ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj A)
      ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj B)
          ((G.sheafPushforwardContinuous CommRingCat.{w} J K).map b)]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
    rw [reassoc_of% k₂, reassoc_of% k₁]
  · intro k _
    rw [naiveCotangentComplex_d_zero_eq_zero.{u₁, v₁, w, max u₂ v₂ z} J
        ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj A)
      ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj B)
          ((G.sheafPushforwardContinuous CommRingCat.{w} J K).map b) k, Limits.comp_zero]
  · intro k h₀ h₁
    exact naiveCotangentComplex_isZero_X.{v₁, u₁, w, max u₂ v₂ z} J
        ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj A)
      ((G.sheafPushforwardContinuous CommRingCat.{w} J K).obj B)
          ((G.sheafPushforwardContinuous CommRingCat.{w} J K).map b) k h₀ h₁

end Restriction

end Stacks.SheafOfModules

end
