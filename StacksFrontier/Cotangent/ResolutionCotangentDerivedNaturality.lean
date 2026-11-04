module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitByPointResolutionNaturality
public import StacksFrontier.Cotangent.ResolutionCotangentDerived
import StacksCore.Tactic.StacksAttribute

/-!
# Any resolution computes the cotangent complex, functorially in the resolution

Let `A → B` be a ring map and let `κ` be a cardinal. For every resolution `ε : P_• ⟶ B` of
[Stacks, Tag 08QI] whose terms are polynomial algebras on at most `κ` variables,
`CommAlgCat.smallResolutionCotangentDerivedLowerShriekIso` — [Stacks, Tag 08PU] in `D(B)` —
identifies the complex of that resolution with an object that does not mention it:

`Q(Ω[P_•⁄A] ⊗_{P_•} B) ≅ Lπ_!(i^*Ω_{𝒪/A})` in `D(B)`.

This file shows that the identification is **functorial in the resolution**: for a morphism
`w : P_• ⟶ P'_•` of simplicial `A`-algebras over `B`, the triangle

`Q(Ω[P_•⁄A] ⊗_{P_•} B) ⟶ Q(Ω[P'_•⁄A] ⊗_{P'_•} B) ⟶ Lπ_!(i^*Ω_{𝒪/A})`

commutes, the first arrow being the chain-level map induced by `w` on base-changed
differentials. So the isomorphism between the complexes of two resolutions obtained by composing
the two instances of [Stacks, Tag 08PU] is not merely *some* isomorphism: whenever the two
resolutions are related by a morphism, it **is** the map that morphism induces. That is what
[Stacks, Remark 08QI] asserts when it says that any resolution computes `L_{B/A}`, and it is what
a comparison of two presentations needs: the object-level statement alone leaves the arrow
unpinned.

## The route

Everything rests on
`Stacks.ChaoticSite.ModuleValued.mooreCochainQIsoDerivedColimit_naturality`, the naturality of
the derived form of [Stacks, Tag 08PT] in the point resolution. What is done here is to produce,
from `w`, the morphism of cosimplicial objects of the small model of the site that the keystone
consumes, and to match the two comparison isomorphisms
`CommAlgCat.smallResolutionCotangentMooreCochainIso` along it.

Both steps go through full faithfulness rather than through the layers of the small model. A
morphism of cosimplicial objects of the small model is constructed as the preimage, under the
fully faithful inclusion into `CommAlgCat.polynomialSite`, of the conjugate of
`CommAlgCat.resolutionCosimplicialObjectMap` by the two instances of
`CommAlgCat.smallResolutionCosimplicialObjectι`. Its defining property then *is* the compatibility
needed to match the two comparison isomorphisms, so no computation with the equivalence
`CommAlgCat.boundedPolynomialSiteEquiv` is required.

## Main definitions

* `CommAlgCat.resolutionOverMap`: a morphism of resolutions over `B`, read as a morphism of
  simplicial objects of `Over B`.
* `CommAlgCat.resolutionAugmentationMap` and `CommAlgCat.resolutionCosimplicialObjectMap`: the
  same, read in the category of polynomial augmentations and in the site `C_{B/A}`.
* `CommAlgCat.smallResolutionCosimplicialObjectMap`: the induced morphism of cosimplicial objects
  of the small model of the footnote-restricted site.
* `CommAlgCat.resolutionCotangentComplexMap`: the induced map
  `Ω[P_•⁄A] ⊗_{P_•} B ⟶ Ω[P'_•⁄A] ⊗_{P'_•} B` of complexes in cohomological degrees `≤ 0`.

## Main results

* `CommAlgCat.smallResolutionCotangentModuleIso_naturality` and
  `CommAlgCat.smallResolutionCotangentMooreCochainIso_naturality`: the identification of the
  evaluation of `i^*Ω_{𝒪/A}` on a resolution with `Ω[P_•⁄A] ⊗_{P_•} B` is compatible with a
  morphism of resolutions.
* `CommAlgCat.smallResolutionCotangentDerivedLowerShriekIso_naturality`: **[Stacks, Tag 08PU] in
  `D(B)` is functorial in the resolution.**

## Implementation notes

The direction of the induced morphism of cosimplicial objects is opposite to that of `w`: the site
`C_{B/A}` is the *opposite* of the category of polynomial augmentations, so `w : P_• ⟶ P'_•` gives
`CommAlgCat.smallResolutionCosimplicialObject` of `ε'` mapping to that of `ε`. Evaluating
`i^*Ω_{𝒪/A}` reverses it again, which is why the induced map of complexes goes from the complex of
`ε` to the complex of `ε'`, covariantly in `w`.

Like the statement it is deduced from, this is functoriality in the resolution and not naturality
in the coefficient sheaf; the latter the construction cannot give.

## References

* [Stacks Project, Tag 08PT](https://stacks.math.columbia.edu/tag/08PT)
* [Stacks Project, Tag 08PU](https://stacks.math.columbia.edu/tag/08PU)
* [Stacks Project, Tag 08QI](https://stacks.math.columbia.edu/tag/08QI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open Stacks.ChaoticSite.ModuleValued

universe u

namespace CommAlgCat

variable {A : Type u} [CommRing A] {B : CommAlgCat.{u} A}
  {P P' : SimplicialObject (CommAlgCat.{u} A)}
  (ε : P ⟶ (SimplicialObject.const (CommAlgCat.{u} A)).obj B)
  (ε' : P' ⟶ (SimplicialObject.const (CommAlgCat.{u} A)).obj B)

/-! ### A morphism of resolutions, read in the site -/

/-- **A morphism of resolutions of `B` over `A`, read as a morphism of simplicial objects of
`Over B`.** A morphism `w : P_• ⟶ P'_•` of simplicial `A`-algebras compatible with the
augmentations is degreewise a morphism over `B`. -/
def resolutionOverMap (w : P ⟶ P') (hw : w ≫ ε' = ε) :
    resolutionOver ε ⟶ resolutionOver ε' where
  app n := Over.homMk (w.app n) (NatTrans.congr_app hw n)
  naturality _ _ f := Over.OverMorphism.ext (w.naturality f)

variable (hP : ∀ n, IsPolynomialAlgebra A (P.obj n)) (hP' : ∀ n, IsPolynomialAlgebra A (P'.obj n))

/-- **A morphism of resolutions, read in the category of polynomial `A`-algebras augmented to
`B`.** The category of polynomial augmentations is a full subcategory of `Over B`, so the morphism
is the preimage of `CommAlgCat.resolutionOverMap` under the fully faithful inclusion. -/
def resolutionAugmentationMap (w : P ⟶ P') (hw : w ≫ ε' = ε) :
    resolutionAugmentation ε hP ⟶ resolutionAugmentation ε' hP' :=
  (((IsPolynomialAlgebraOver A B).fullyFaithfulι).whiskeringRight SimplexCategoryᵒᵖ).preimage
    (resolutionOverMap ε ε' w hw)

/-- The defining property of `CommAlgCat.resolutionAugmentationMap`: read in `Over B` it is
`CommAlgCat.resolutionOverMap`. -/
lemma whiskerRight_resolutionAugmentationMap (w : P ⟶ P') (hw : w ≫ ε' = ε) :
    Functor.whiskerRight (resolutionAugmentationMap ε ε' hP hP' w hw)
        (IsPolynomialAlgebraOver A B).ι = resolutionOverMap ε ε' w hw :=
  (((IsPolynomialAlgebraOver A B).fullyFaithfulι).whiskeringRight
    SimplexCategoryᵒᵖ).map_preimage _

/-- **A morphism of resolutions, read as a morphism of the cosimplicial objects of the site
`C_{B/A}`.** The site is the opposite of the category of polynomial augmentations, so the
direction is reversed: `w : P_• ⟶ P'_•` gives a morphism from the cosimplicial object of `ε'` to
that of `ε`. -/
def resolutionCosimplicialObjectMap (w : P ⟶ P') (hw : w ≫ ε' = ε) :
    resolutionCosimplicialObject ε' hP' ⟶ resolutionCosimplicialObject ε hP :=
  NatTrans.rightOp (resolutionAugmentationMap ε ε' hP hP' w hw)

/-- **The evaluation of `i^*Ω_{𝒪/A}` on `CommAlgCat.resolutionCosimplicialObjectMap` is the map
induced on base-changed differentials.** Both sides apply `CommAlgCat.overDifferentialsFunctor` to
the degreewise morphism over `B` of `CommAlgCat.resolutionOverMap`; the only content is the
defining property of `CommAlgCat.resolutionAugmentationMap`. -/
lemma whiskerRight_op_resolutionCosimplicialObjectMap (w : P ⟶ P') (hw : w ≫ ε' = ε) :
    Functor.whiskerRight (NatTrans.op (resolutionCosimplicialObjectMap ε ε' hP hP' w hw))
        (polynomialCotangentModulePresheaf A B) =
      Functor.whiskerRight (resolutionOverMap ε ε' w hw) overDifferentialsFunctor := by
  rw [← whiskerRight_resolutionAugmentationMap ε ε' hP hP' w hw]
  rfl

/-! ### A morphism of resolutions in the small model of the restricted site -/

variable (κ : Cardinal.{u}) (hPκ : ∀ n, IsPolynomialAlgebraBelow A κ (P.obj n))
  (hP'κ : ∀ n, IsPolynomialAlgebraBelow A κ (P'.obj n))

/-- **A morphism of bounded resolutions, read as a morphism of cosimplicial objects of the small
model of the footnote-restricted site.** The inclusion of the model into
`CommAlgCat.polynomialSite` is fully faithful, so the morphism is the preimage of the morphism of
cosimplicial objects of the site, conjugated by the two identifications
`CommAlgCat.smallResolutionCosimplicialObjectι`. Taking the preimage rather than descending
through the layers of the model is what makes the compatibility below free. -/
def smallResolutionCosimplicialObjectMap (w : P ⟶ P') (hw : w ≫ ε' = ε) :
    smallResolutionCosimplicialObject ε' κ hP'κ ⟶ smallResolutionCosimplicialObject ε κ hPκ :=
  ((fullyFaithfulSmallBoundedPolynomialSiteToPolynomialSite A B κ).whiskeringRight
      SimplexCategory).preimage
    ((smallResolutionCosimplicialObjectι ε' κ hP'κ).hom ≫
      resolutionCosimplicialObjectMap ε ε' (fun n => (hPκ n).isPolynomialAlgebra)
        (fun n => (hP'κ n).isPolynomialAlgebra) w hw ≫
      (smallResolutionCosimplicialObjectι ε κ hPκ).inv)

/-- The defining property of `CommAlgCat.smallResolutionCosimplicialObjectMap`: read in the
unrestricted site it is `CommAlgCat.resolutionCosimplicialObjectMap`, conjugated by the
identifications of the cosimplicial objects of the model with those of the resolutions. -/
lemma whiskerRight_smallResolutionCosimplicialObjectMap (w : P ⟶ P') (hw : w ≫ ε' = ε) :
    Functor.whiskerRight (smallResolutionCosimplicialObjectMap ε ε' κ hPκ hP'κ w hw)
        (smallBoundedPolynomialSiteToPolynomialSite A B κ) =
      (smallResolutionCosimplicialObjectι ε' κ hP'κ).hom ≫
        resolutionCosimplicialObjectMap ε ε' (fun n => (hPκ n).isPolynomialAlgebra)
          (fun n => (hP'κ n).isPolynomialAlgebra) w hw ≫
        (smallResolutionCosimplicialObjectι ε κ hPκ).inv :=
  ((fullyFaithfulSmallBoundedPolynomialSiteToPolynomialSite A B κ).whiskeringRight
    SimplexCategory).map_preimage _

/-! ### Matching the two comparisons `(i^*Ω_{𝒪/A})(P_•, ε) = Ω[P_•⁄A] ⊗_{P_•} B` -/

/-- `CommAlgCat.smallResolutionCotangentModuleIso` is the evaluation of `i^*Ω_{𝒪/A}` on the
identification `CommAlgCat.smallResolutionCosimplicialObjectι`. -/
lemma smallResolutionCotangentModuleIso_hom :
    (smallResolutionCotangentModuleIso ε κ hPκ).hom =
      Functor.whiskerRight (NatTrans.op (smallResolutionCosimplicialObjectι ε κ hPκ).inv)
        (polynomialCotangentModulePresheaf A B) :=
  rfl

/-- **The identification of `(i^*Ω_{𝒪/A})(P_•, ε)` with `Ω[P_•⁄A] ⊗_{P_•} B` is compatible with a
morphism of resolutions**, the morphism of cosimplicial objects of the small model being
`CommAlgCat.smallResolutionCosimplicialObjectMap`. Both comparisons are the evaluation of
`i^*Ω_{𝒪/A}` on an identification, and the square is the defining property of that morphism
together with the cancellation of the identification at `ε'`. -/
lemma smallResolutionCotangentModuleIso_naturality (w : P ⟶ P') (hw : w ≫ ε' = ε) :
    (smallResolutionCotangentModuleIso ε κ hPκ).hom ≫
        Functor.whiskerRight (resolutionOverMap ε ε' w hw) overDifferentialsFunctor =
      Functor.whiskerRight
          (NatTrans.op (smallResolutionCosimplicialObjectMap ε ε' κ hPκ hP'κ w hw))
          (smallPolynomialCotangentModulePresheaf A B κ) ≫
        (smallResolutionCotangentModuleIso ε' κ hP'κ).hom := by
  have key : Functor.whiskerRight
        (NatTrans.op (smallResolutionCosimplicialObjectMap ε ε' κ hPκ hP'κ w hw))
        (smallPolynomialCotangentModulePresheaf A B κ) =
      Functor.whiskerRight (NatTrans.op (Functor.whiskerRight
        (smallResolutionCosimplicialObjectMap ε ε' κ hPκ hP'κ w hw)
        (smallBoundedPolynomialSiteToPolynomialSite A B κ)))
        (polynomialCotangentModulePresheaf A B) := rfl
  have main :
      Functor.whiskerRight (NatTrans.op (smallResolutionCosimplicialObjectι ε κ hPκ).inv)
            (polynomialCotangentModulePresheaf A B) ≫
          Functor.whiskerRight (NatTrans.op (resolutionCosimplicialObjectMap ε ε'
            (fun n => (hPκ n).isPolynomialAlgebra) (fun n => (hP'κ n).isPolynomialAlgebra) w hw))
            (polynomialCotangentModulePresheaf A B) =
        Functor.whiskerRight (NatTrans.op ((smallResolutionCosimplicialObjectι ε' κ hP'κ).hom ≫
              resolutionCosimplicialObjectMap ε ε'
                (fun n => (hPκ n).isPolynomialAlgebra)
                (fun n => (hP'κ n).isPolynomialAlgebra) w hw ≫
              (smallResolutionCosimplicialObjectι ε κ hPκ).inv))
            (polynomialCotangentModulePresheaf A B) ≫
          Functor.whiskerRight (NatTrans.op (smallResolutionCosimplicialObjectι ε' κ hP'κ).inv)
            (polynomialCotangentModulePresheaf A B) := by
    rw [← Functor.whiskerRight_comp, ← Functor.whiskerRight_comp, ← NatTrans.op_comp,
      ← NatTrans.op_comp, Iso.inv_hom_id_assoc]
  rw [key, whiskerRight_smallResolutionCosimplicialObjectMap,
    ← whiskerRight_op_resolutionCosimplicialObjectMap ε ε'
      (fun n => (hPκ n).isPolynomialAlgebra) (fun n => (hP'κ n).isPolynomialAlgebra) w hw,
    smallResolutionCotangentModuleIso_hom, smallResolutionCotangentModuleIso_hom]
  exact main

/-- **The map `Ω[P_•⁄A] ⊗_{P_•} B ⟶ Ω[P'_•⁄A] ⊗_{P'_•} B` induced by a morphism of
resolutions**, read in cohomological degrees `≤ 0`: degreewise it is the map
`1 ⊗ d p ↦ 1 ⊗ d (w p)` on base-changed differentials. -/
def resolutionCotangentComplexMap (w : P ⟶ P') (hw : w ≫ ε' = ε) :
    ((alternatingFaceMapComplex (ModuleCat.{u} (B : Type u))).obj
        (resolutionOver ε ⋙ overDifferentialsFunctor)).extend
      (ComplexShape.embeddingUpIntLE (0 : ℤ)) ⟶
      ((alternatingFaceMapComplex (ModuleCat.{u} (B : Type u))).obj
        (resolutionOver ε' ⋙ overDifferentialsFunctor)).extend
      (ComplexShape.embeddingUpIntLE (0 : ℤ)) :=
  ((ComplexShape.embeddingUpIntLE (0 : ℤ)).extendFunctor (ModuleCat.{u} (B : Type u))).map
    ((alternatingFaceMapComplex (ModuleCat.{u} (B : Type u))).map
      (Functor.whiskerRight (resolutionOverMap ε ε' w hw) overDifferentialsFunctor))

/-- **The identification of the extended Moore complex of `(i^*Ω_{𝒪/A})(P_•, ε)` with the complex
`Ω[P_•⁄A] ⊗_{P_•} B` is compatible with a morphism of resolutions.** This is
`CommAlgCat.smallResolutionCotangentModuleIso_naturality` after applying the alternating face map
complex and the reindexing into cohomological degrees `≤ 0`. -/
lemma smallResolutionCotangentMooreCochainIso_naturality (w : P ⟶ P') (hw : w ≫ ε' = ε) :
    (smallResolutionCotangentMooreCochainIso ε κ hPκ).hom ≫
        resolutionCotangentComplexMap ε ε' w hw =
      (mooreCochainMap (smallResolutionCosimplicialObjectMap ε ε' κ hPκ hP'κ w hw)).app
          (smallPolynomialCotangentModulePresheaf A B κ) ≫
        (smallResolutionCotangentMooreCochainIso ε' κ hP'κ).hom := by
  have hmcm : (mooreCochainMap (smallResolutionCosimplicialObjectMap ε ε' κ hPκ hP'κ w hw)).app
        (smallPolynomialCotangentModulePresheaf A B κ) =
      ((ComplexShape.embeddingUpIntLE (0 : ℤ)).extendFunctor
          (ModuleCat.{u} (B : Type u))).map
        ((alternatingFaceMapComplex (ModuleCat.{u} (B : Type u))).map
          (Functor.whiskerRight
            (NatTrans.op (smallResolutionCosimplicialObjectMap ε ε' κ hPκ hP'κ w hw))
            (smallPolynomialCotangentModulePresheaf A B κ))) := rfl
  have h := congrArg (fun τ => ((ComplexShape.embeddingUpIntLE (0 : ℤ)).extendFunctor
      (ModuleCat.{u} (B : Type u))).map
        ((alternatingFaceMapComplex (ModuleCat.{u} (B : Type u))).map τ))
    (smallResolutionCotangentModuleIso_naturality ε ε' κ hPκ hP'κ w hw)
  simp only [Functor.map_comp] at h
  dsimp only [smallResolutionCotangentMooreCochainIso, Functor.mapIso_hom,
    resolutionCotangentComplexMap]
  rw [hmcm]
  exact h

/-! ### Tag 08PU in `D(B)` is functorial in the resolution -/

attribute [local instance] HasDerivedCategory.standard

/-- `CommAlgCat.smallResolutionCotangentDerivedLowerShriekIso` is the comparison of the complex of
the resolution with the extended Moore complex of `(i^*Ω_{𝒪/A})(P_•, ε)`, followed by the derived
form of [Stacks, Tag 08PT]. -/
lemma smallResolutionCotangentDerivedLowerShriekIso_hom
    (hε : SSet.trivialKanFibrations (Functor.whiskerRight ε (forget (CommAlgCat.{u} A)))) :
    (smallResolutionCotangentDerivedLowerShriekIso ε κ hPκ hε).hom =
      DerivedCategory.Q.map (smallResolutionCotangentMooreCochainIso ε κ hPκ).inv ≫
        (mooreCochainQIsoDerivedColimit (smallResolutionCosimplicialObject ε κ hPκ)
          (smallPolynomialCotangentModulePresheaf A B κ)
          (isPointResolution_smallResolutionCosimplicialObject ε κ hPκ hε)).hom :=
  rfl

/-- **[Stacks, Tag 08PU] in `D(B)` is functorial in the resolution.** Let `ε : P_• ⟶ B` and
`ε' : P'_• ⟶ B` be resolutions of `B` over `A` in the sense of [Stacks, Tag 08QI] whose terms are
polynomial algebras on at most `κ` variables, and let `w : P_• ⟶ P'_•` be a morphism of simplicial
`A`-algebras over `B`. Then the triangle

`Q(Ω[P_•⁄A] ⊗_{P_•} B) ⟶ Q(Ω[P'_•⁄A] ⊗_{P'_•} B) ⟶ Lπ_!(Ω_{𝒪/A} ⊗_𝒪 B̲)`

commutes: the comparison of `CommAlgCat.smallResolutionCotangentDerivedLowerShriekIso` at `ε'`,
precomposed with the map `CommAlgCat.resolutionCotangentComplexMap` induced by `w`, is the
comparison at `ε`.

In particular the isomorphism between the complexes of two resolutions that the two instances of
[Stacks, Tag 08PU] produce is the map induced by any morphism between the resolutions — which is
the content of [Stacks, Remark 08QI] beyond the object-level statement, and what a comparison of
two presentations consumes.

The proof is the naturality of the derived form of [Stacks, Tag 08PT] in the point resolution
(`Stacks.ChaoticSite.ModuleValued.mooreCochainQIsoDerivedColimit_naturality`), applied at
`CommAlgCat.smallResolutionCosimplicialObjectMap`, together with
`CommAlgCat.smallResolutionCotangentMooreCochainIso_naturality`. -/
@[stacks 08PU "in D(B), at module coefficients: the identification of the complex of a resolution \
  with L pi_!(Omega ⊗ B-underline) is functorial in the resolution, so the isomorphism it gives \
  between the complexes of two resolutions is the map induced by a morphism between them. This is \
  the arrow-level form of Remark 08QI"]
theorem smallResolutionCotangentDerivedLowerShriekIso_naturality (w : P ⟶ P') (hw : w ≫ ε' = ε)
    (hε : SSet.trivialKanFibrations (Functor.whiskerRight ε (forget (CommAlgCat.{u} A))))
    (hε' : SSet.trivialKanFibrations (Functor.whiskerRight ε' (forget (CommAlgCat.{u} A)))) :
    DerivedCategory.Q.map (resolutionCotangentComplexMap ε ε' w hw) ≫
        (smallResolutionCotangentDerivedLowerShriekIso ε' κ hP'κ hε').hom =
      (smallResolutionCotangentDerivedLowerShriekIso ε κ hPκ hε).hom := by
  have hsq := smallResolutionCotangentMooreCochainIso_naturality ε ε' κ hPκ hP'κ w hw
  have hsq' : resolutionCotangentComplexMap ε ε' w hw ≫
        (smallResolutionCotangentMooreCochainIso ε' κ hP'κ).inv =
      (smallResolutionCotangentMooreCochainIso ε κ hPκ).inv ≫
        (mooreCochainMap (smallResolutionCosimplicialObjectMap ε ε' κ hPκ hP'κ w hw)).app
          (smallPolynomialCotangentModulePresheaf A B κ) := by
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
    exact hsq
  have hnat := mooreCochainQIsoDerivedColimit_naturality
    (smallResolutionCosimplicialObjectMap ε ε' κ hPκ hP'κ w hw)
    (isPointResolution_smallResolutionCosimplicialObject ε' κ hP'κ hε')
    (isPointResolution_smallResolutionCosimplicialObject ε κ hPκ hε)
    (smallPolynomialCotangentModulePresheaf A B κ)
  have step := congrArg DerivedCategory.Q.map hsq'
  simp only [Functor.map_comp] at step
  rw [smallResolutionCotangentDerivedLowerShriekIso_hom,
    smallResolutionCotangentDerivedLowerShriekIso_hom, ← hnat]
  exact (reassoc_of% step) _

end CommAlgCat

end
