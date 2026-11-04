module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardRightExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardSheafificationAlong
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.PullbackOfModules
public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalPresentationIso
public import
  StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangentSquareIso
public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentInverseImageComplex
public import StacksFrontier.Cotangent.Spaces.EtaleRestriction

/-!
# Restriction of the naive cotangent complex along a cocontinuous functor of sites

Let `G : C ⥤ D` be a continuous and cocontinuous functor of sites, so that restriction of sheaves
along `G`, written `G^s`, is the inverse image of a morphism of topoi `Sh(C) ⟶ Sh(D)`
(Stacks 00XO). For a homomorphism `a : A ⟶ B` of sheaves of commutative rings on `D`, this file
identifies the restriction of the naive cotangent complex with the naive cotangent complex of the
restriction:

`G^s NL_{B/A} ≅ NL_{G^sB/G^sA}`,

as an isomorphism of two-term complexes of sheaves of `G^sB`-modules. This is Stacks 08TZ for
the morphism of topoi attached to `G`, at an arbitrary universe of sections of the sheaves of
modules: the universe of the sections of the rings is independent of the universe of the
objects of the site, as on the small étale site of an algebraic space.

## Main definitions

* `Stacks.Sites.Conormal.ringSheafModuleRestriction`: restriction of sheaves of `B`-modules
  along `G`, as sheaves of `G^sB`-modules.
* `Stacks.Sites.Conormal.restrictionConormalSequenceIso`: the restriction of the conormal
  sequence of a presentation `φ : A ⟶ B` over `R` is the conormal sequence of the restricted
  presentation `G^sφ` over `G^sR`.
* `Stacks.SheafOfModules.canonicalFreeAlgebraIsoOfIso`: the isomorphism `A[B] ≅ A'[B']` of free
  algebra sheaves attached to isomorphisms `A ≅ A'` and `B ≅ B'`.
* `Stacks.SheafOfModules.restrictionFreeAlgebraIso`: `G^s(A[B]) ≅ (G^sA)[G^sB]`.
* `Stacks.SheafOfModules.restrictionNaiveCotangentComplexIso`: `G^s NL_{B/A} ≅ NL_{G^sB/G^sA}`.

## Main results

* `Stacks.SheafOfModules.map_coefficientMap_comp_restrictionFreeAlgebraIso` and
  `Stacks.SheafOfModules.restrictionFreeAlgebraIso_comp_canonicalPresentation`: the
  identification `G^s(A[B]) ≅ (G^sA)[G^sB]` is one of `G^sA`-algebras over `G^sB`, i.e. an
  isomorphism of presentations of `G^sB`.

## Implementation notes

The terms of the conormal sequence of a presentation are the sheafifications, along the locally
bijective map from the image presheaf `A/I` to `B`, of objectwise constructions. Restriction
along `G` commutes with objectwise constructions by definition, and with sheafification along a
ring map by `Stacks.SheafOfModules.PushforwardSheafification.pushforwardSheafifyNatIsoAlong`,
because `G` is cocontinuous; that is `restrictionConormalSequenceIso`.

The restriction of the canonical presentation `A[B] ⟶ B` is a presentation of `G^sB`, but not
the canonical one. The free algebra half of Stacks 08TZ,
`Stacks.Sites.FreeAlgebra.inverseImageFreeAlgebraIso`, holds for a morphism of topoi `f` at any
universe of sections, and is transported to restriction along an identification
`e : f⁻¹ ≅ G^s` of the inverse image with restriction, by
`Stacks.Sheaves.ToposPullback.inverseImageCommRingRestrictionIso`. That is the role of the data
`f` and `e`; for an étale morphism of algebraic spaces they are the morphism of small étale topoi
and Stacks 03LQ. The change of presentation along the resulting isomorphism is
`Stacks.Sites.Conormal.conormalSheafIsoOfFac` and `Stacks.Sites.Conormal.tensorSheafIsoOfFac`,
which commute with the conormal differentials.

The two sheaves of rings `Tensor.ringSheaf (G^sB)` and `G^s (Tensor.ringSheaf B)` are equal by
definition but not syntactically. Every statement is phrased over the first, which is the sheaf
of rings the naive cotangent complex of `G^sB` is over, through
`Stacks.Sites.Conormal.ringSheafRestrictionHom`, the identity morphism between them at its
declared type; spelling the coefficient change as an ascription instead leaves terms that are
not type-correct at reducible transparency, and `rw` and `simp` then cannot act on them.

## References

* [Stacks Project, Tag 08TZ](https://stacks.math.columbia.edu/tag/08TZ)
* [Stacks Project, Tag 08TW](https://stacks.math.columbia.edu/tag/08TW), the naive cotangent
  complex.
* [Stacks Project, Tag 08TS](https://stacks.math.columbia.edu/tag/08TS), the conormal sequence.
* [Stacks Project, Tag 00XO](https://stacks.math.columbia.edu/tag/00XO), the morphism of topoi
  attached to a continuous and cocontinuous functor.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u w z

namespace Stacks.Sites.Conormal

open Stacks.SheafOfModules.PushforwardSheafification

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {D : Type u} [Category.{v} D] (K : GrothendieckTopology D)

/-- Sheafification of presheaves of abelian groups on the essentially small site `(C, J)`. -/
local instance [EssentiallySmall.{z} C] : HasSheafify J AddCommGrpCat.{z} :=
  AlgebraicGeometry.SheafOfModules.siteHasSheafify (J := J)

/-- On the essentially small site `(C, J)`, sheafification of abelian presheaves inverts exactly
the locally bijective morphisms. -/
local instance [EssentiallySmall.{z} C] : J.WEqualsLocallyBijective AddCommGrpCat.{z} :=
  AlgebraicGeometry.SheafOfModules.siteWEqualsLocallyBijective (J := J)

/-- Sheafification of presheaves of abelian groups on the essentially small site `(D, K)`. -/
local instance [EssentiallySmall.{z} D] : HasSheafify K AddCommGrpCat.{z} :=
  AlgebraicGeometry.SheafOfModules.siteHasSheafify (J := K)

/-- On the essentially small site `(D, K)`, sheafification of abelian presheaves inverts exactly
the locally bijective morphisms. -/
local instance [EssentiallySmall.{z} D] : K.WEqualsLocallyBijective AddCommGrpCat.{z} :=
  AlgebraicGeometry.SheafOfModules.siteWEqualsLocallyBijective (J := K)

variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (G : C ⥤ D) [G.IsContinuous J K] [G.IsCocontinuous J K]
  (R A B : Sheaf K CommRingCat.{w}) (a : R ⟶ A) (φ : A ⟶ B)

/-- Restriction of sheaves of commutative rings along `G`. -/
abbrev ringRestriction : Sheaf K CommRingCat.{w} ⥤ Sheaf J CommRingCat.{w} :=
  G.sheafPushforwardContinuous CommRingCat.{w} J K

/-- The sheaf of rings underlying `G^sB` is the restriction along `G` of the sheaf of rings
underlying `B`: the two agree by definition, and this is the identity between them, at the
spelling `SheafOfModules.pushforward` consumes. -/
def ringSheafRestrictionHom :
    Stacks.SheafOfModules.Tensor.ringSheaf ((ringRestriction J K G).obj B) ⟶
      (G.sheafPushforwardContinuous RingCat.{w} J K).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf B) :=
  𝟙 _

/-- Restriction of sheaves of modules over the sheaf of rings underlying `B` along `G`, read as
sheaves of modules over the sheaf of rings underlying `G^sB`, which is the sheaf of rings the
naive cotangent complex of `G^sB` is a complex of modules over. On sections it is `M ↦ M ∘ G`. -/
noncomputable abbrev ringSheafModuleRestriction.{t} :
    _root_.SheafOfModules.{t} (Stacks.SheafOfModules.Tensor.ringSheaf B) ⥤
      _root_.SheafOfModules.{t}
        (Stacks.SheafOfModules.Tensor.ringSheaf ((ringRestriction J K G).obj B)) :=
  _root_.SheafOfModules.pushforward.{t} (ringSheafRestrictionHom J K G B)

/-- Restricting a locally surjective homomorphism of sheaves of rings along a cocontinuous
functor keeps it locally surjective. -/
instance isLocallySurjective_ringRestriction_map [Presheaf.IsLocallySurjective K φ.hom] :
    Presheaf.IsLocallySurjective J ((ringRestriction J K G).map φ).hom :=
  Presheaf.isLocallySurjective_whisker J K G φ.hom

variable [Presheaf.IsLocallySurjective K φ.hom]

/-- **The restriction of the conormal sequence of a presentation is the conormal sequence of the
restricted presentation**: for a locally surjective `φ : A ⟶ B` over `a : R ⟶ A`, restriction
along `G` carries the conormal sequence `I/I² ⟶ B ⊗_A Ω_{A/R} ⟶ Ω_{B/R}` to the conormal sequence
of `G^sφ` over `G^sa`. All three terms are sheafifications of objectwise constructions, which
restriction commutes with on the nose, and restriction commutes with the sheafification. -/
noncomputable def restrictionConormalSequenceIso :
    (conormalSequence.{v, u, w, z} K R A B a φ).map
        (ringSheafModuleRestriction.{v, u, w, max w u v z} J K G B) ≅
      conormalSequence.{v, u, w, z} J ((ringRestriction J K G).obj R)
        ((ringRestriction J K G).obj A) ((ringRestriction J K G).obj B)
        ((ringRestriction J K G).map a) ((ringRestriction J K G).map φ) :=
  (ShortComplex.mapNatIso ((conormalPresheafComplex φ.hom a.hom).map
      (liftModules.{v, u, w, z} _))
    (pushforwardSheafifyNatIsoAlong.{max w u v z} J G (quotientToRingSheaf K A B φ))).symm

end Stacks.Sites.Conormal

namespace Stacks.SheafOfModules

open Stacks.Sites.FreeAlgebra Stacks.Sites.Conormal Stacks.Sheaves.ToposPullback
open Stacks.SheafOfModules.PushforwardSheafification

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {D : Type u} [Category.{v} D] (K : GrothendieckTopology D)

section FreeAlgebraIso

variable [HasWeakSheafify J CommRingCat.{w}]

/-- The isomorphism `A[B] ≅ A'[B']` of free algebra sheaves attached to isomorphisms `A ≅ A'` of
the coefficients and `B ≅ B'` of the sheaves whose sections are the variables. -/
noncomputable def canonicalFreeAlgebraIsoOfIso {A A' B B' : Sheaf J CommRingCat.{w}}
    (eA : A ≅ A') (eB : B ≅ B') :
    freeAlgebraSheaf J A (underlyingPresheaf J B) ≅
      freeAlgebraSheaf J A' (underlyingPresheaf J B') where
  hom := canonicalFreeAlgebraMapOfSquare J A A' B B' eA.hom eB.hom
  inv := canonicalFreeAlgebraMapOfSquare J A' A B' B eA.inv eB.inv
  hom_inv_id := by
    rw [canonicalFreeAlgebraMapOfSquare_comp, eA.hom_inv_id, eB.hom_inv_id]
    exact canonicalFreeAlgebraMapOfSquare_id J A B
  inv_hom_id := by
    rw [canonicalFreeAlgebraMapOfSquare_comp, eA.inv_hom_id, eB.inv_hom_id]
    exact canonicalFreeAlgebraMapOfSquare_id J A' B'

end FreeAlgebraIso

/-- Sheafification of presheaves of abelian groups on the essentially small site `(C, J)`. -/
local instance [EssentiallySmall.{z} C] : HasSheafify J AddCommGrpCat.{z} :=
  AlgebraicGeometry.SheafOfModules.siteHasSheafify (J := J)

/-- On the essentially small site `(C, J)`, sheafification of abelian presheaves inverts exactly
the locally bijective morphisms. -/
local instance [EssentiallySmall.{z} C] : J.WEqualsLocallyBijective AddCommGrpCat.{z} :=
  AlgebraicGeometry.SheafOfModules.siteWEqualsLocallyBijective (J := J)

/-- Sheafification of presheaves of abelian groups on the essentially small site `(D, K)`. -/
local instance [EssentiallySmall.{z} D] : HasSheafify K AddCommGrpCat.{z} :=
  AlgebraicGeometry.SheafOfModules.siteHasSheafify (J := K)

/-- On the essentially small site `(D, K)`, sheafification of abelian presheaves inverts exactly
the locally bijective morphisms. -/
local instance [EssentiallySmall.{z} D] : K.WEqualsLocallyBijective AddCommGrpCat.{z} :=
  AlgebraicGeometry.SheafOfModules.siteWEqualsLocallyBijective (J := K)

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
noncomputable def restrictionFreeAlgebraIso :
    (ringRestriction J K G).obj (freeAlgebraSheaf K A (underlyingPresheaf K B)) ≅
      freeAlgebraSheaf J ((ringRestriction J K G).obj A)
        (underlyingPresheaf J ((ringRestriction J K G).obj B)) :=
  (inverseImageCommRingRestrictionIso J K G f e _).symm ≪≫ inverseImageFreeAlgebraIso f A B ≪≫
    canonicalFreeAlgebraIsoOfIso J (inverseImageCommRingRestrictionIso J K G f e A)
      (inverseImageCommRingRestrictionIso J K G f e B)

omit [J.HasSheafCompose (forget CommRingCat.{w})] [K.HasSheafCompose (forget CommRingCat.{w})] in
/-- The forward map of `Stacks.SheafOfModules.restrictionFreeAlgebraIso` is the composite of the
three comparisons it is built from. -/
theorem restrictionFreeAlgebraIso_hom :
    (restrictionFreeAlgebraIso J K G f e A B).hom =
      (inverseImageCommRingRestrictionIso J K G f e
          (freeAlgebraSheaf K A (underlyingPresheaf K B))).inv ≫
        inverseImageFreeAlgebraHom f A B ≫
          canonicalFreeAlgebraMapOfSquare J (f.inverseImageRing.obj A)
            ((ringRestriction J K G).obj A) (f.inverseImageRing.obj B)
            ((ringRestriction J K G).obj B) (inverseImageCommRingRestrictionIso J K G f e A).hom
            (inverseImageCommRingRestrictionIso J K G f e B).hom :=
  rfl

/-- The identification `G^s(A[B]) ≅ (G^sA)[G^sB]` is one of `G^sA`-algebras. -/
theorem map_coefficientMap_comp_restrictionFreeAlgebraIso :
    (ringRestriction J K G).map (freeAlgebraSheafCoefficientMap K A (underlyingPresheaf K B)) ≫
        (restrictionFreeAlgebraIso J K G f e A B).hom =
      freeAlgebraSheafCoefficientMap J ((ringRestriction J K G).obj A)
        (underlyingPresheaf J ((ringRestriction J K G).obj B)) := by
  have ha : (ringRestriction J K G).map
        (freeAlgebraSheafCoefficientMap K A (underlyingPresheaf K B)) ≫
        (inverseImageCommRingRestrictionIso J K G f e
          (freeAlgebraSheaf K A (underlyingPresheaf K B))).inv =
      (inverseImageCommRingRestrictionIso J K G f e A).inv ≫
        f.inverseImageRing.map (freeAlgebraSheafCoefficientMap K A (underlyingPresheaf K B)) :=
    inverseImageCommRingRestrictionIso_inv_naturality J K G f e _
  have hc := freeAlgebraSheafCoefficientMap_comp_freeAlgebraMapOfSquare J
    (f.inverseImageRing.obj A) ((ringRestriction J K G).obj A)
    (underlyingPresheaf J (f.inverseImageRing.obj B))
    (underlyingPresheaf J ((ringRestriction J K G).obj B))
    (inverseImageCommRingRestrictionIso J K G f e A).hom
    (underlyingPresheafMap J _ _ (inverseImageCommRingRestrictionIso J K G f e B).hom)
  rw [restrictionFreeAlgebraIso_hom]
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) ha).trans
    ((Category.assoc _ _ _).trans ((Iso.inv_comp_eq _).2 ?_)))
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) (map_coefficientMap_comp_inverseImageFreeAlgebraHom f A B)).trans hc)

/-- The identification `G^s(A[B]) ≅ (G^sA)[G^sB]` carries the restriction of the canonical
presentation of `B` to the canonical presentation of `G^sB`. -/
theorem restrictionFreeAlgebraIso_comp_canonicalPresentation :
    (restrictionFreeAlgebraIso J K G f e A B).hom ≫
        canonicalPresentation J ((ringRestriction J K G).obj A) ((ringRestriction J K G).obj B)
          ((ringRestriction J K G).map b) =
      (ringRestriction J K G).map (canonicalPresentation K A B b) := by
  have hsq : f.inverseImageRing.map b ≫ (inverseImageCommRingRestrictionIso J K G f e B).hom =
      (inverseImageCommRingRestrictionIso J K G f e A).hom ≫ (ringRestriction J K G).map b :=
    inverseImageCommRingRestrictionIso_naturality J K G f e b
  have hd := freeAlgebraMapOfSquare_comp_canonicalPresentation J
    (f.inverseImageRing.obj A) ((ringRestriction J K G).obj A)
    (f.inverseImageRing.obj B) ((ringRestriction J K G).obj B)
    (f.inverseImageRing.map b) ((ringRestriction J K G).map b)
    (inverseImageCommRingRestrictionIso J K G f e A).hom
    (inverseImageCommRingRestrictionIso J K G f e B).hom hsq
  have hf : f.inverseImageRing.map (canonicalPresentation K A B b) ≫
        (inverseImageCommRingRestrictionIso J K G f e B).hom =
      (inverseImageCommRingRestrictionIso J K G f e
          (freeAlgebraSheaf K A (underlyingPresheaf K B))).hom ≫
        (ringRestriction J K G).map (canonicalPresentation K A B b) :=
    inverseImageCommRingRestrictionIso_naturality J K G f e _
  rw [restrictionFreeAlgebraIso_hom]
  refine (Category.assoc _ _ _).trans ((Iso.inv_comp_eq _).2 ?_)
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hd).trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) (inverseImageFreeAlgebraHom_comp_canonicalPresentation f A B b)).trans hf)))

variable [G.IsCocontinuous J K]

/-- The canonical presentation `A[B] ⟶ B` is locally surjective, as a morphism of presheaves of
commutative rings. -/
instance isLocallySurjective_canonicalPresentation {E : Type*} [Category E]
    {L : GrothendieckTopology E} [HasWeakSheafify L CommRingCat.{w}]
    (A' B' : Sheaf L CommRingCat.{w}) (b' : A' ⟶ B') :
    Presheaf.IsLocallySurjective L (canonicalPresentation L A' B' b').hom :=
  canonicalPresentation_isLocallySurjective L A' B' b'

/-- **The restriction of the naive cotangent complex along a continuous and cocontinuous functor
of sites is the naive cotangent complex of the restriction**: `G^s NL_{B/A} ≅ NL_{G^sB/G^sA}`,
as an isomorphism of two-term complexes of sheaves of `G^sB`-modules, for a functor `G` whose
restriction functor on sheaves of sets is the inverse image of a morphism of topoi `f`.

In degree `-1` it is the restriction of the conormal sheaf of `A[B] ⟶ B`, identified with the
conormal sheaf of `G^s(A[B]) ⟶ G^sB` and then, along the isomorphism of presentations
`G^s(A[B]) ≅ (G^sA)[G^sB]`, with that of the canonical presentation of `G^sB`; in degree `0` it
is the same for the scalar extension of the differentials. This is Stacks 08TZ for the morphism
of topoi attached to `G`. -/
noncomputable def restrictionNaiveCotangentComplexIso :
    ((ringSheafModuleRestriction.{v, u, w, max w u v z} J K G B).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (naiveCotangentComplex.{v, u, w, z} K A B b) ≅
      naiveCotangentComplex.{v, u, w, z} J ((ringRestriction J K G).obj A)
        ((ringRestriction J K G).obj B) ((ringRestriction J K G).map b) := by
  letI : HasZeroObject (_root_.SheafOfModules.{max w u v z} (Tensor.ringSheaf B)) :=
    hasZeroObject_of_hasTerminal_object
  letI : HasZeroObject (_root_.SheafOfModules.{max w u v z}
      (Tensor.ringSheaf ((ringRestriction J K G).obj B))) :=
    hasZeroObject_of_hasTerminal_object
  let E := restrictionConormalSequenceIso.{v, u, w, z} J K G A
    (freeAlgebraSheaf K A (underlyingPresheaf K B)) B
    (freeAlgebraSheafCoefficientMap K A (underlyingPresheaf K B)) (canonicalPresentation K A B b)
  let E₁ : (ringSheafModuleRestriction.{v, u, w, max w u v z} J K G B).obj
        (canonicalConormalSequence.{v, u, w, z} K A B b).X₁ ≅
      (conormalSequence.{v, u, w, z} J ((ringRestriction J K G).obj A)
        ((ringRestriction J K G).obj (freeAlgebraSheaf K A (underlyingPresheaf K B)))
        ((ringRestriction J K G).obj B)
        ((ringRestriction J K G).map (freeAlgebraSheafCoefficientMap K A (underlyingPresheaf K B)))
        ((ringRestriction J K G).map (canonicalPresentation K A B b))).X₁ :=
    ShortComplex.π₁.mapIso E
  let E₂ : (ringSheafModuleRestriction.{v, u, w, max w u v z} J K G B).obj
        (canonicalConormalSequence.{v, u, w, z} K A B b).X₂ ≅
      (conormalSequence.{v, u, w, z} J ((ringRestriction J K G).obj A)
        ((ringRestriction J K G).obj (freeAlgebraSheaf K A (underlyingPresheaf K B)))
        ((ringRestriction J K G).obj B)
        ((ringRestriction J K G).map (freeAlgebraSheafCoefficientMap K A (underlyingPresheaf K B)))
        ((ringRestriction J K G).map (canonicalPresentation K A B b))).X₂ :=
    ShortComplex.π₂.mapIso E
  let c : (conormalSequence.{v, u, w, z} J ((ringRestriction J K G).obj A)
        ((ringRestriction J K G).obj (freeAlgebraSheaf K A (underlyingPresheaf K B)))
        ((ringRestriction J K G).obj B)
        ((ringRestriction J K G).map (freeAlgebraSheafCoefficientMap K A (underlyingPresheaf K B)))
        ((ringRestriction J K G).map (canonicalPresentation K A B b))).X₁ ≅
      (canonicalConormalSequence.{v, u, w, z} J ((ringRestriction J K G).obj A)
        ((ringRestriction J K G).obj B) ((ringRestriction J K G).map b)).X₁ :=
    conormalSheafIsoOfFac.{v, u, w, z} J ((ringRestriction J K G).obj B)
      ((ringRestriction J K G).obj (freeAlgebraSheaf K A (underlyingPresheaf K B)))
      (freeAlgebraSheaf J ((ringRestriction J K G).obj A)
        (underlyingPresheaf J ((ringRestriction J K G).obj B)))
      ((ringRestriction J K G).map (canonicalPresentation K A B b))
      (canonicalPresentation J ((ringRestriction J K G).obj A) ((ringRestriction J K G).obj B)
        ((ringRestriction J K G).map b))
      (restrictionFreeAlgebraIso J K G f e A B)
      (restrictionFreeAlgebraIso_comp_canonicalPresentation J K G f e A B b)
  let t : (conormalSequence.{v, u, w, z} J ((ringRestriction J K G).obj A)
        ((ringRestriction J K G).obj (freeAlgebraSheaf K A (underlyingPresheaf K B)))
        ((ringRestriction J K G).obj B)
        ((ringRestriction J K G).map (freeAlgebraSheafCoefficientMap K A (underlyingPresheaf K B)))
        ((ringRestriction J K G).map (canonicalPresentation K A B b))).X₂ ≅
      (canonicalConormalSequence.{v, u, w, z} J ((ringRestriction J K G).obj A)
        ((ringRestriction J K G).obj B) ((ringRestriction J K G).map b)).X₂ :=
    tensorSheafIsoOfFac.{v, u, w, z} J ((ringRestriction J K G).obj A)
      ((ringRestriction J K G).obj B)
      ((ringRestriction J K G).obj (freeAlgebraSheaf K A (underlyingPresheaf K B)))
      (freeAlgebraSheaf J ((ringRestriction J K G).obj A)
        (underlyingPresheaf J ((ringRestriction J K G).obj B)))
      ((ringRestriction J K G).map (freeAlgebraSheafCoefficientMap K A (underlyingPresheaf K B)))
      (freeAlgebraSheafCoefficientMap J ((ringRestriction J K G).obj A)
        (underlyingPresheaf J ((ringRestriction J K G).obj B)))
      ((ringRestriction J K G).map (canonicalPresentation K A B b))
      (canonicalPresentation J ((ringRestriction J K G).obj A) ((ringRestriction J K G).obj B)
        ((ringRestriction J K G).map b))
      (restrictionFreeAlgebraIso J K G f e A B)
      (restrictionFreeAlgebraIso_comp_canonicalPresentation J K G f e A B b)
      (map_coefficientMap_comp_restrictionFreeAlgebraIso J K G f e A B)
  have k₁ : E₁.hom ≫ (conormalSequence.{v, u, w, z} J ((ringRestriction J K G).obj A)
        ((ringRestriction J K G).obj (freeAlgebraSheaf K A (underlyingPresheaf K B)))
        ((ringRestriction J K G).obj B)
        ((ringRestriction J K G).map (freeAlgebraSheafCoefficientMap K A (underlyingPresheaf K B)))
        ((ringRestriction J K G).map (canonicalPresentation K A B b))).f =
      (ringSheafModuleRestriction.{v, u, w, max w u v z} J K G B).map
        (canonicalConormalSequence.{v, u, w, z} K A B b).f ≫ E₂.hom :=
    E.hom.comm₁₂
  have k₂ : c.hom ≫ (canonicalConormalSequence.{v, u, w, z} J ((ringRestriction J K G).obj A)
        ((ringRestriction J K G).obj B) ((ringRestriction J K G).map b)).f =
      (conormalSequence.{v, u, w, z} J ((ringRestriction J K G).obj A)
        ((ringRestriction J K G).obj (freeAlgebraSheaf K A (underlyingPresheaf K B)))
        ((ringRestriction J K G).obj B)
        ((ringRestriction J K G).map (freeAlgebraSheafCoefficientMap K A (underlyingPresheaf K B)))
        ((ringRestriction J K G).map (canonicalPresentation K A B b))).f ≫ t.hom :=
    conormalSheafIsoOfFac_hom_comp_conormalSequence_f.{v, u, w, z} J
      ((ringRestriction J K G).obj A) ((ringRestriction J K G).obj B)
      ((ringRestriction J K G).obj (freeAlgebraSheaf K A (underlyingPresheaf K B)))
      (freeAlgebraSheaf J ((ringRestriction J K G).obj A)
        (underlyingPresheaf J ((ringRestriction J K G).obj B)))
      ((ringRestriction J K G).map (freeAlgebraSheafCoefficientMap K A (underlyingPresheaf K B)))
      (freeAlgebraSheafCoefficientMap J ((ringRestriction J K G).obj A)
        (underlyingPresheaf J ((ringRestriction J K G).obj B)))
      ((ringRestriction J K G).map (canonicalPresentation K A B b))
      (canonicalPresentation J ((ringRestriction J K G).obj A) ((ringRestriction J K G).obj B)
        ((ringRestriction J K G).map b))
      (restrictionFreeAlgebraIso J K G f e A B)
      (restrictionFreeAlgebraIso_comp_canonicalPresentation J K G f e A B b)
      (map_coefficientMap_comp_restrictionFreeAlgebraIso J K G f e A B)
  refine HomologicalComplex.isoFromMapDouble
    (ringSheafModuleRestriction.{v, u, w, max w u v z} J K G B)
    (canonicalConormalSequence.{v, u, w, z} K A B b).f
    (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) (by decide)
    ((E₁ ≪≫ c).trans
      (naiveCotangentComplexXNegOneIso.{u, v, w, z} J ((ringRestriction J K G).obj A)
        ((ringRestriction J K G).obj B) ((ringRestriction J K G).map b)).symm)
    ((E₂ ≪≫ t).trans
      (naiveCotangentComplexXZeroIso.{u, v, w, z} J ((ringRestriction J K G).obj A)
        ((ringRestriction J K G).obj B) ((ringRestriction J K G).map b)).symm) ?_ ?_ ?_
  · rw [naiveCotangentComplex_d_negOne_zero_iso.{u, v, w, z} J ((ringRestriction J K G).obj A)
      ((ringRestriction J K G).obj B) ((ringRestriction J K G).map b)]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
    rw [reassoc_of% k₂, reassoc_of% k₁]
  · intro k _
    rw [naiveCotangentComplex_d_zero_eq_zero.{u, v, w, z} J ((ringRestriction J K G).obj A)
      ((ringRestriction J K G).obj B) ((ringRestriction J K G).map b) k, Limits.comp_zero]
  · intro k h₀ h₁
    exact naiveCotangentComplex_isZero_X.{v, u, w, z} J ((ringRestriction J K G).obj A)
      ((ringRestriction J K G).obj B) ((ringRestriction J K G).map b) k h₀ h₁

end Restriction

end Stacks.SheafOfModules

end
