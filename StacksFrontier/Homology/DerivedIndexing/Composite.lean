module

public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionOfRightDerivedFunctors
public import StacksFrontier.Algebra.Homology.RightDerivedEdge
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# The right derived functor of a composite, and the edge morphism

Let `P : 𝒜 ⥤ ℬ` and `Q : ℬ ⥤ 𝒞` be additive functors between abelian categories, with `𝒜` and
`ℬ` having enough injectives. The canonical transformation `t : R(Q ∘ P) ⟶ RQ ∘ RP` of functors
`D⁺(𝒜) ⥤ D⁺(𝒞)` of [Stacks, Tag 05T2] is an isomorphism when `P` preserves injective objects
([Stacks, Tag 015M]). It then gives a degreewise comparison `R ⁱQ(Pℱ) ⟶ R ⁱ(Q ∘ P)(ℱ)` in the
`ℤ`-indexing of `CategoryTheory.Functor.rightDerivedPlus`, and under
`Stacks.DerivedIndexing.rightDerivedIso` this comparison is the `ℕ`-indexed edge morphism
`Stacks.Cohomology.RightDerivedEdge.edge`.

## Main definitions

* `Stacks.DerivedIndexing.rightDerivedPlusCompUnit`: the transformation
  `Q(P(K)) ⟶ RQ(P(K)) ⟶ RQ(RP(K))` of functors `K⁺(𝒜) ⥤ D⁺(𝒞)` assembled from the units of
  `RQ` and `RP`.
* `Stacks.DerivedIndexing.rightDerivedPlusCompTrans`: the canonical transformation
  `t : R(Q ∘ P) ⟶ RQ ∘ RP`, obtained from the universal property of right derivation.
* `Stacks.DerivedIndexing.rightDerivedPlusCompIso`: `t` as an isomorphism, when `P` preserves
  injective objects.
* `Stacks.DerivedIndexing.rightDerivedPlusUnitSingle`: the canonical map
  `(Pℱ)[0] ⟶ RP(ℱ[0])` in `D⁺(ℬ)`, natural in `ℱ`.
* `Stacks.DerivedIndexing.rightDerivedPlusEdge`: the degreewise comparison
  `R ⁱQ(Pℱ) ⟶ R ⁱ(Q ∘ P)(ℱ)` in the `ℤ`-indexing: `H ⁱ(RQ(-))` applied to
  `rightDerivedPlusUnitSingle`, transported along `rightDerivedPlusCompIso`.
* `Stacks.DerivedIndexing.extendMapHomologyIso`: for an additive `F` and a cochain complex `K`
  indexed by `ℕ`, the isomorphism between the degree-`i` homology of `F(K)` in the homotopy
  category of `ℕ`-indexed complexes and the degree-`i` homology of `F` applied to the extension
  by zero of `K` to a complex indexed by `ℤ`.
* `Stacks.DerivedIndexing.extendResolutionComparison`: the comparison of injective resolutions
  underlying the edge morphism, extended by zero to complexes indexed by `ℤ`;
  `Stacks.DerivedIndexing.extendResolutionComparisonPlus` is its class in `K⁺(ℬ)`.
* `Stacks.DerivedIndexing.resUnitPlusApp`, `Stacks.DerivedIndexing.resUnitPlus`: the
  augmentation `ℱ[0] ⟶ I` of the chosen extended injective resolution, in `K⁺(𝒜)`.

## Main results

* `Stacks.DerivedIndexing.isIso_rightDerivedPlusCompTrans`: if `P` preserves injective objects
  then `R(Q ∘ P) ≅ RQ ∘ RP`.
* `Stacks.DerivedIndexing.isoRightDerivedObj_injectiveResolution`: at the chosen injective
  resolution, `CategoryTheory.InjectiveResolution.isoRightDerivedObj` is the comparison
  `HomotopyCategory.homologyFunctorFactors` between homology computed in the homotopy category
  and homology computed on complexes.
* `Stacks.DerivedIndexing.rightDerivedIsoRes_hom_app_eq`: the comparison
  `Stacks.DerivedIndexing.rightDerivedIsoRes` of the two indexings, evaluated at an object, is
  `extendMapHomologyIso` at the chosen injective resolution.
* `Stacks.DerivedIndexing.extendMapHomologyIso_hom_naturality`,
  `Stacks.DerivedIndexing.extendMapHomologyIso_hom_comp`: `extendMapHomologyIso` is natural in
  the complex, and compatible with a composite of functors.
* `Stacks.DerivedIndexing.edge_comp_rightDerivedIsoRes`: the edge morphism of the pair `(P, Q)`,
  read through the comparison of the two indexings, is the degree-`i` homology of `Q` applied to
  the extension by zero of the comparison of injective resolutions.
* `Stacks.DerivedIndexing.extendResolutionComparison_f_zero`,
  `Stacks.DerivedIndexing.ι'_comp_extendResolutionComparison`: the comparison of the extended
  injective resolutions is compatible with the two augmentations.
* `Stacks.DerivedIndexing.singleFunctorPlusIsoCompQh_inv_app_comp_singleIsoResPlusQh_hom_app`:
  `singleIsoResPlusQh` composed with the identification of the single functors is the image
  under `Qh` of the augmentation.
* `Stacks.DerivedIndexing.mapHomotopyCategorySingleFunctor_inv_app_degree`,
  `Stacks.DerivedIndexing.ι_map_mapSingleFunctorCompQhIsoOfDegree_inv_app`,
  `Stacks.DerivedIndexing.ι_map_singleIsoResPlusQh_hom_app_eq`: closed forms of three
  comparisons of single functors, as `HomologicalComplex.singleMapHomologicalComplex` or the
  augmentation read through the quotient and the localization.
* `Stacks.DerivedIndexing.singleIsoResPlusQh_hom_app_comp_extendResolutionComparisonPlus`: in
  `D⁺(ℬ)`, the comparison of the extended resolutions identifies the two routes from `(Pℱ)[0]`
  to `P` applied to the chosen extended injective resolution of `ℱ`.
* `Stacks.DerivedIndexing.rightDerivedPlusUnitSingle_app_comp_map_singleIsoResPlusQh`: the
  canonical map `(Pℱ)[0] ⟶ RP(ℱ[0])` is compatible with the identifications of `ℱ[0]` and
  `(Pℱ)[0]` with their chosen extended injective resolutions and with the comparison of those
  resolutions.
* `Stacks.DerivedIndexing.rightDerivedPlusIsoRes_hom_app`: the closed form of the five-step
  comparison `Stacks.DerivedIndexing.rightDerivedPlusIsoRes`; its last two steps have identity
  components.
* `Stacks.DerivedIndexing.rightDerivedPlusEdge_comp_rightDerivedPlusIsoRes`: the degreewise
  comparison, read through the comparison of the two indexings, is the degree-`i` homology of
  `Q` applied to the extension by zero of the comparison of injective resolutions.
* `Stacks.DerivedIndexing.edge_comp_rightDerivedIso`: under
  `Stacks.DerivedIndexing.rightDerivedIso`, the `ℕ`-indexed edge morphism
  `Stacks.Cohomology.RightDerivedEdge.edge P Q i` corresponds to
  `Stacks.DerivedIndexing.rightDerivedPlusEdge P Q i`.
* `Stacks.DerivedIndexing.map_comp_edge_comp_rightDerivedIso`: the same, precomposed with the
  map induced by a morphism `u : 𝒢 ⟶ Pℱ`.

## References

* [Stacks, Tag 015M]
* [Stacks, Tag 05T2]
* [Stacks, Tag 015A]
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits ComplexShape DerivedCategory

namespace Stacks.DerivedIndexing

universe w w' w'' v v' v'' u u' u''

/-- Two commuting squares pasted side by side: `a ≫ b₂ ≫ c₂ = (b₁ ≫ c₁) ≫ d`. -/
lemma paste_comm_squares {X : Type*} [Category* X] {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : X}
    (a : X₁ ⟶ X₂) (b₁ : X₁ ⟶ Y₁) (b₂ : X₂ ⟶ Y₂) (a' : Y₁ ⟶ Y₂) (c₁ : Y₁ ⟶ Z₁)
    (c₂ : Y₂ ⟶ Z₂) (d : Z₁ ⟶ Z₂) (h₁ : a ≫ b₂ = b₁ ≫ a') (h₂ : a' ≫ c₂ = c₁ ≫ d) :
    a ≫ b₂ ≫ c₂ = (b₁ ≫ c₁) ≫ d := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc]

/-- Two commuting squares pasted side by side; this is `paste_comm_squares`. -/
private alias pasteSquares := paste_comm_squares

/-- One commuting square followed by one computed composite. -/
private lemma pasteSquare {X : Type*} [Category* X] {X₁ X₂ Y₁ Y₂ Z : X}
    (a : X₁ ⟶ X₂) (b₁ : X₁ ⟶ Y₁) (b₂ : X₂ ⟶ Y₂) (a' : Y₁ ⟶ Y₂) (c₂ : Y₂ ⟶ Z) (k : Y₁ ⟶ Z)
    (h₁ : a ≫ b₂ = b₁ ≫ a') (h₂ : a' ≫ c₂ = k) : a ≫ b₂ ≫ c₂ = b₁ ≫ k := by
  rw [← Category.assoc, h₁, Category.assoc, h₂]

/-! ### The right derived functor of a composite -/

section Composition

attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {C : Type u} {D : Type u'} {E : Type u''}
  [Category.{v} C] [Category.{v'} D] [Category.{v''} E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D] [HasDerivedCategory.{w''} E]
  [EnoughInjectives C] [EnoughInjectives D]
  (P : C ⥤ D) (Q : D ⥤ E) [P.Additive] [Q.Additive]

/-- The transformation `Q(P(K)) ⟶ RQ(P(K)) ⟶ RQ(RP(K))` of functors `K⁺(𝒜) ⥤ D⁺(𝒞)`,
assembled from the units of `RQ` and of `RP` ([Stacks, Tag 05T2]). -/
def rightDerivedPlusCompUnit :
    (P ⋙ Q).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶
      DerivedCategory.Plus.Qh ⋙ P.rightDerivedFunctorPlus ⋙ Q.rightDerivedFunctorPlus :=
  Functor.whiskerRight (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (P ⋙ Q))).inv
      DerivedCategory.Plus.Qh ≫
    Functor.whiskerLeft P.mapHomotopyCategoryPlus Q.rightDerivedFunctorPlusUnit ≫
    Functor.whiskerRight P.rightDerivedFunctorPlusUnit Q.rightDerivedFunctorPlus

/-- The canonical transformation `t : R(Q ∘ P) ⟶ RQ ∘ RP` of [Stacks, Tag 05T2], induced by
`rightDerivedPlusCompUnit` through the universal property of right derivation. -/
def rightDerivedPlusCompTrans :
    (P ⋙ Q).rightDerivedFunctorPlus ⟶
      P.rightDerivedFunctorPlus ⋙ Q.rightDerivedFunctorPlus :=
  Functor.rightDerivedDesc _ (P ⋙ Q).rightDerivedFunctorPlusUnit
    (HomotopyCategory.Plus.quasiIso C) _ (rightDerivedPlusCompUnit P Q)

/-- The factorization that characterises `rightDerivedPlusCompTrans`. -/
theorem rightDerivedPlusCompTrans_fac :
    (P ⋙ Q).rightDerivedFunctorPlusUnit ≫
        Functor.whiskerLeft DerivedCategory.Plus.Qh (rightDerivedPlusCompTrans P Q) =
      rightDerivedPlusCompUnit P Q :=
  Functor.rightDerived_fac _ _ _ _ _

/-- The factorization that characterises `rightDerivedPlusCompTrans`, componentwise. -/
theorem rightDerivedPlusCompTrans_fac_app (K : HomotopyCategory.Plus C) :
    (P ⋙ Q).rightDerivedFunctorPlusUnit.app K ≫
        (rightDerivedPlusCompTrans P Q).app (DerivedCategory.Plus.Qh.obj K) =
      (rightDerivedPlusCompUnit P Q).app K :=
  Functor.rightDerived_fac_app _ _ _ _ _ K

omit [HasDerivedCategory.{w'} D] [EnoughInjectives D] in
/-- Every term of the single complex on an injective object is injective. -/
private lemma injective_single_obj_as_X (I : D) [Injective I] (m : ℤ) :
    Injective (((HomotopyCategory.Plus.singleFunctor D 0).obj I).obj.as.X m) := by
  rcases eq_or_ne m 0 with rfl | hm
  · exact Injective.of_iso
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 I).symm inferInstance
  · exact Injective.of_iso
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 I m hm).isoZero.symm
      inferInstance

/-- If `P` preserves injective objects then `t : R(Q ∘ P) ⟶ RQ ∘ RP` is an isomorphism
([Stacks, Tag 015M]). -/
instance isIso_rightDerivedPlusCompTrans [P.PreservesInjectiveObjects] :
    IsIso (rightDerivedPlusCompTrans P Q) := by
  rw [Functor.isIso_iff_rightAcyclic_obj_injective P Q (rightDerivedPlusCompTrans P Q)
    (rightDerivedPlusCompTrans_fac P Q)]
  intro I hI
  have : Injective I := hI
  have : Injective (P.obj I) := P.injective_obj_of_injective hI
  change IsIso (Q.rightDerivedFunctorPlusUnit.app
    ((HomotopyCategory.Plus.singleFunctor D 0).obj (P.obj I)))
  have hinj : ∀ m : ℤ,
      Injective (((HomotopyCategory.Plus.singleFunctor D 0).obj (P.obj I)).obj.as.X m) :=
    injective_single_obj_as_X (P.obj I)
  infer_instance

/-- The composition isomorphism `R(Q ∘ P) ≅ RQ ∘ RP` for `P` preserving injective objects,
[Stacks, Tag 015M]. -/
def rightDerivedPlusCompIso [P.PreservesInjectiveObjects] :
    (P ⋙ Q).rightDerivedFunctorPlus ≅
      P.rightDerivedFunctorPlus ⋙ Q.rightDerivedFunctorPlus :=
  asIso (rightDerivedPlusCompTrans P Q)

/-- The canonical map `(Pℱ)[0] ⟶ RP(ℱ[0])` in `D⁺(ℬ)`, natural in `ℱ`: the unit of `RP`
evaluated on the single complex, read through the identification of `Q(ℱ[0])` with `(Qℱ)[0]` and
of `ℱ[0]` in `D⁺` with its image from `K⁺`. -/
def rightDerivedPlusUnitSingle :
    P ⋙ DerivedCategory.Plus.singleFunctor D 0 ⟶
      DerivedCategory.Plus.singleFunctor C 0 ⋙ P.rightDerivedFunctorPlus :=
  (Functor.mapSingleFunctorCompQhIso P).inv ≫
    Functor.whiskerLeft (HomotopyCategory.Plus.singleFunctor C 0)
      P.rightDerivedFunctorPlusUnit ≫
    Functor.whiskerRight (Functor.singleFunctorPlusIsoCompQh (A := C) 0).inv
      P.rightDerivedFunctorPlus

/-- The degreewise comparison `R ⁱQ(Pℱ) ⟶ R ⁱ(Q ∘ P)(ℱ)` in the `ℤ`-indexing of
`CategoryTheory.Functor.rightDerivedPlus`: `H ⁱ(RQ(-))` applied to the canonical map
`(Pℱ)[0] ⟶ RP(ℱ[0])`, transported along the composition isomorphism `R(Q ∘ P) ≅ RQ ∘ RP`. -/
def rightDerivedPlusEdge [P.PreservesInjectiveObjects] (i : ℤ) :
    P ⋙ Q.rightDerivedPlus i ⟶ (P ⋙ Q).rightDerivedPlus i :=
  Functor.whiskerRight (rightDerivedPlusUnitSingle P)
      (Q.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor E i) ≫
    Functor.whiskerLeft (DerivedCategory.Plus.singleFunctor C 0)
      (Functor.whiskerRight (rightDerivedPlusCompIso P Q).inv
        (DerivedCategory.Plus.homologyFunctor E i))

end Composition

/-! ### The chosen injective resolution -/

section Chosen

variable {A : Type u} {B : Type u'} [Category.{v} A] [Category.{v'} B]
  [Abelian A] [Abelian B] [EnoughInjectives A] (F : A ⥤ B) [F.Additive] (X : A) (i : ℕ)

/-- The comparison `CategoryTheory.InjectiveResolution.iso` of the chosen injective resolution
of `X` with itself is the identity. -/
theorem injectiveResolution_iso_hom : ((injectiveResolution X).iso).hom =
    𝟙 ((HomotopyCategory.quotient A (ComplexShape.up ℕ)).obj
      (injectiveResolution X).cocomplex) :=
  HomotopyCategory.eq_of_homotopy _ _ (InjectiveResolution.descIdHomotopy _ _)

/-- `injectiveResolution_iso_hom` after an additive functor. -/
theorem map_injectiveResolution_iso_hom :
    (F.mapHomotopyCategory (ComplexShape.up ℕ)).map ((injectiveResolution X).iso).hom =
      𝟙 ((F.mapHomotopyCategory (ComplexShape.up ℕ)).obj
        ((HomotopyCategory.quotient A (ComplexShape.up ℕ)).obj
          (injectiveResolution X).cocomplex)) := by
  rw [injectiveResolution_iso_hom]
  exact (F.mapHomotopyCategory (ComplexShape.up ℕ)).map_id _

/-- At the chosen injective resolution,
`CategoryTheory.InjectiveResolution.isoRightDerivedToHomotopyCategoryObj` is the identity. -/
theorem isoRightDerivedToHomotopyCategoryObj_injectiveResolution :
    ((injectiveResolution X).isoRightDerivedToHomotopyCategoryObj F).hom =
      𝟙 ((F.mapHomotopyCategory (ComplexShape.up ℕ)).obj
        ((HomotopyCategory.quotient A (ComplexShape.up ℕ)).obj
          (injectiveResolution X).cocomplex)) :=
  (congrArg (fun w => w ≫ ((F.mapHomotopyCategoryFactors (ComplexShape.up ℕ)).app
      (injectiveResolution X).cocomplex).hom) (map_injectiveResolution_iso_hom F X)).trans
    (Category.id_comp _)

/-- At the chosen injective resolution, `CategoryTheory.InjectiveResolution.isoRightDerivedObj`
is the comparison between homology computed in the homotopy category and homology computed on
complexes. -/
theorem isoRightDerivedObj_injectiveResolution :
    ((injectiveResolution X).isoRightDerivedObj F i).hom =
      (HomotopyCategory.homologyFunctorFactors B (ComplexShape.up ℕ) i).hom.app
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (injectiveResolution X).cocomplex) :=
  (congrArg (fun w => w ≫ (HomotopyCategory.homologyFunctorFactors B (ComplexShape.up ℕ) i).hom.app
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (injectiveResolution X).cocomplex))
    (((congrArg (HomotopyCategory.homologyFunctor B (ComplexShape.up ℕ) i).map
        (isoRightDerivedToHomotopyCategoryObj_injectiveResolution F X)).trans
      ((HomotopyCategory.homologyFunctor B (ComplexShape.up ℕ) i).map_id _)) :
      (HomotopyCategory.homologyFunctor B (ComplexShape.up ℕ) i).map
        ((injectiveResolution X).isoRightDerivedToHomotopyCategoryObj F).hom = _)).trans
    (Category.id_comp _)

/-- `isoRightDerivedObj_injectiveResolution`, for the inverse. -/
theorem isoRightDerivedObj_injectiveResolution_inv :
    ((injectiveResolution X).isoRightDerivedObj F i).inv =
      (HomotopyCategory.homologyFunctorFactors B (ComplexShape.up ℕ) i).inv.app
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (injectiveResolution X).cocomplex) := by
  have h : ((injectiveResolution X).isoRightDerivedObj F i) =
      (HomotopyCategory.homologyFunctorFactors B (ComplexShape.up ℕ) i).app
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (injectiveResolution X).cocomplex) :=
    Iso.ext (isoRightDerivedObj_injectiveResolution F X i)
  exact congrArg Iso.inv h

end Chosen

/-! ### Extension by zero and the two indexings of homology -/

section Extend

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {A : Type u} {B : Type u'} {G : Type u''}
  [Category.{v} A] [Category.{v'} B] [Category.{v''} G]
  [Preadditive A] [Preadditive B] [Preadditive G]
  [HasZeroObject A] [HasZeroObject B] [HasZeroObject G]

/-- `Stacks.DerivedIndexing.mapExtendXIso` for a composite of additive functors. -/
lemma mapExtendXIso_comp (P : A ⥤ B) [P.Additive] (Q : B ⥤ G) [Q.Additive]
    (K : HomologicalComplex A c) (j : Option ι) :
    (mapExtendXIso (P ⋙ Q) K j).hom =
      (mapExtendXIso Q ((P.mapHomologicalComplex c).obj K) j).hom ≫
        Q.map (mapExtendXIso P K j).hom := by
  cases j with
  | some a => exact ((Category.id_comp _).trans (Q.map_id _)).symm
  | none => exact (Limits.isZero_zero G).eq_of_src _ _

/-- `Stacks.DerivedIndexing.mapExtendIso` for a composite of additive functors. -/
lemma mapExtendIso_comp (e : c.Embedding c') (P : A ⥤ B) [P.Additive] (Q : B ⥤ G) [Q.Additive]
    (K : HomologicalComplex A c) :
    (mapExtendIso (P ⋙ Q) e K).hom =
      (mapExtendIso Q e ((P.mapHomologicalComplex c).obj K)).hom ≫
        (Q.mapHomologicalComplex c').map (mapExtendIso P e K).hom := by
  ext i'
  exact mapExtendXIso_comp P Q K (e.r i')

end Extend

section ExtendHomology

variable {A : Type u} {B : Type u'} {G : Type u''}
  [Category.{v} A] [Category.{v'} B] [Category.{v''} G]
  [Abelian A] [Abelian B] [Abelian G]

/-- The degree-`i` homology of `F(K)` in the homotopy category of `ℕ`-indexed complexes is
isomorphic to the degree-`i` homology of `F` applied to the extension by zero of `K` to a complex
indexed by `ℤ`. -/
def extendMapHomologyIso (F : A ⥤ B) [F.Additive] (K : CochainComplex A ℕ) (i : ℕ) :
    (HomotopyCategory.homologyFunctor B (ComplexShape.up ℕ) i).obj
        ((F.mapHomotopyCategory (ComplexShape.up ℕ)).obj
          ((HomotopyCategory.quotient A (ComplexShape.up ℕ)).obj K)) ≅
      (HomotopyCategory.homologyFunctor B (ComplexShape.up ℤ) (i : ℤ)).obj
        ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((embeddingUpNat.extendHomotopyFunctor A).obj
            ((HomotopyCategory.quotient A (ComplexShape.up ℕ)).obj K))) :=
  ((extendHomotopyHomologyNatIso (A := B) embeddingUpNat
      (rfl : embeddingUpNat.f i = (i : ℤ))).app
    ((F.mapHomotopyCategory (ComplexShape.up ℕ)).obj
      ((HomotopyCategory.quotient A (ComplexShape.up ℕ)).obj K))).symm ≪≫
  (HomotopyCategory.homologyFunctor B (ComplexShape.up ℤ) (i : ℤ)).mapIso
    ((mapExtendHomotopyNatIso F embeddingUpNat).app
      ((HomotopyCategory.quotient A (ComplexShape.up ℕ)).obj K))

/-- The components of `extendMapHomologyIso`. -/
@[simp]
lemma extendMapHomologyIso_hom (F : A ⥤ B) [F.Additive] (K : CochainComplex A ℕ) (i : ℕ) :
    (extendMapHomologyIso F K i).hom =
      (extendHomotopyHomologyNatIso (A := B) embeddingUpNat
          (rfl : embeddingUpNat.f i = (i : ℤ))).inv.app
        ((F.mapHomotopyCategory (ComplexShape.up ℕ)).obj
          ((HomotopyCategory.quotient A (ComplexShape.up ℕ)).obj K)) ≫
      (HomotopyCategory.homologyFunctor B (ComplexShape.up ℤ) (i : ℤ)).map
        ((mapExtendHomotopyNatIso F embeddingUpNat).hom.app
          ((HomotopyCategory.quotient A (ComplexShape.up ℕ)).obj K)) := rfl

/-- `extendMapHomologyIso` is natural in the complex. -/
theorem extendMapHomologyIso_hom_naturality (F : A ⥤ B) [F.Additive]
    {K L : CochainComplex A ℕ} (ψ : K ⟶ L) (i : ℕ) :
    (HomotopyCategory.homologyFunctor B (ComplexShape.up ℕ) i).map
        ((F.mapHomotopyCategory (ComplexShape.up ℕ)).map
          ((HomotopyCategory.quotient A (ComplexShape.up ℕ)).map ψ)) ≫
        (extendMapHomologyIso F L i).hom =
      (extendMapHomologyIso F K i).hom ≫
        (HomotopyCategory.homologyFunctor B (ComplexShape.up ℤ) (i : ℤ)).map
          ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map
            ((embeddingUpNat.extendHomotopyFunctor A).map
              ((HomotopyCategory.quotient A (ComplexShape.up ℕ)).map ψ))) := by
  rw [extendMapHomologyIso_hom, extendMapHomologyIso_hom]
  refine pasteSquares _ _ _ _ _ _ _
    ((extendHomotopyHomologyNatIso (A := B) embeddingUpNat
      (rfl : embeddingUpNat.f i = (i : ℤ))).inv.naturality
      ((F.mapHomotopyCategory (ComplexShape.up ℕ)).map
        ((HomotopyCategory.quotient A (ComplexShape.up ℕ)).map ψ))) ?_
  exact (((HomotopyCategory.homologyFunctor B (ComplexShape.up ℤ) (i : ℤ)).map_comp _ _).symm.trans
    (congrArg (HomotopyCategory.homologyFunctor B (ComplexShape.up ℤ) (i : ℤ)).map
      ((mapExtendHomotopyNatIso F embeddingUpNat).hom.naturality
        ((HomotopyCategory.quotient A (ComplexShape.up ℕ)).map ψ)))).trans
    ((HomotopyCategory.homologyFunctor B (ComplexShape.up ℤ) (i : ℤ)).map_comp _ _)

/-- `extendMapHomologyIso` is compatible with a composite of functors. -/
theorem extendMapHomologyIso_hom_comp (P : A ⥤ B) [P.Additive] (Q : B ⥤ G) [Q.Additive]
    (K : CochainComplex A ℕ) (i : ℕ) :
    (extendMapHomologyIso (P ⋙ Q) K i).hom =
      (extendMapHomologyIso Q ((P.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) i).hom ≫
        (HomotopyCategory.homologyFunctor G (ComplexShape.up ℤ) (i : ℤ)).map
          ((Q.mapHomotopyCategory (ComplexShape.up ℤ)).map
            ((mapExtendHomotopyNatIso P embeddingUpNat).hom.app
              ((HomotopyCategory.quotient A (ComplexShape.up ℕ)).obj K))) := by
  rw [extendMapHomologyIso_hom, extendMapHomologyIso_hom]
  have hmaps : (mapExtendHomotopyNatIso Q embeddingUpNat).hom.app
        ((HomotopyCategory.quotient B (ComplexShape.up ℕ)).obj
          ((P.mapHomologicalComplex (ComplexShape.up ℕ)).obj K)) ≫
        (Q.mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((mapExtendHomotopyNatIso P embeddingUpNat).hom.app
            ((HomotopyCategory.quotient A (ComplexShape.up ℕ)).obj K)) =
      (mapExtendHomotopyNatIso (P ⋙ Q) embeddingUpNat).hom.app
        ((HomotopyCategory.quotient A (ComplexShape.up ℕ)).obj K) :=
    ((HomotopyCategory.quotient G (ComplexShape.up ℤ)).map_comp _ _).symm.trans
      (congrArg (HomotopyCategory.quotient G (ComplexShape.up ℤ)).map
        (mapExtendIso_comp embeddingUpNat P Q K).symm)
  exact (congrArg (fun w => (extendHomotopyHomologyNatIso (A := G) embeddingUpNat
        (rfl : embeddingUpNat.f i = (i : ℤ))).inv.app
      ((Q.mapHomotopyCategory (ComplexShape.up ℕ)).obj
        ((HomotopyCategory.quotient B (ComplexShape.up ℕ)).obj
          ((P.mapHomologicalComplex (ComplexShape.up ℕ)).obj K))) ≫ w)
    ((((HomotopyCategory.homologyFunctor G (ComplexShape.up ℤ) (i : ℤ)).map_comp _ _).symm.trans
      (congrArg (HomotopyCategory.homologyFunctor G (ComplexShape.up ℤ) (i : ℤ)).map
        hmaps)).symm : _ = _)).trans (Category.assoc _ _ _).symm

/-- The comparison `rightDerivedIsoRes F i` of the two indexings of the right derived functors,
evaluated at `X`, is `extendMapHomologyIso` at the chosen injective resolution of `X`. -/
theorem rightDerivedIsoRes_hom_app_eq [EnoughInjectives A] (F : A ⥤ B) [F.Additive] (X : A)
    (i : ℕ) :
    (rightDerivedIsoRes F i).hom.app X =
      (extendMapHomologyIso F (injectiveResolution X).cocomplex i).hom := rfl

end ExtendHomology

/-! ### The edge morphism in the two indexings -/

section Edge

variable {C : Type u} {D : Type u'} {E : Type u''}
  [Category.{v} C] [Category.{v'} D] [Category.{v''} E]
  [Abelian C] [Abelian D] [Abelian E]
  [EnoughInjectives C] [EnoughInjectives D]
  (P : C ⥤ D) (Q : D ⥤ E) [P.Additive] [Q.Additive] [P.PreservesInjectiveObjects]

/-- The comparison of injective resolutions underlying the edge morphism, extended by zero to
complexes indexed by `ℤ`: the extension of
`Stacks.Cohomology.RightDerivedEdge.resolutionComparison`, followed by the identification of the
extension of `P` applied to a complex with `P` applied to the extension. -/
def extendResolutionComparison (X : C) :
    (injectiveResolution (P.obj X)).cochainComplex ⟶
      (P.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (injectiveResolution X).cochainComplex :=
  (embeddingUpNat.extendFunctor D).map
      (Stacks.Cohomology.RightDerivedEdge.resolutionComparison P X) ≫
    (mapExtendIso P embeddingUpNat (injectiveResolution X).cocomplex).hom

/-- The edge morphism `R ⁱQ(Pℱ) ⟶ R ⁱ(Q ∘ P)(ℱ)` of
`Stacks.Cohomology.RightDerivedEdge.edge`, read through the comparison
`Stacks.DerivedIndexing.rightDerivedIsoRes` of the two indexings of the right derived functors,
is the degree-`i` homology of `Q` applied to the extension by zero of the comparison of the
chosen injective resolutions. -/
theorem edge_comp_rightDerivedIsoRes (i : ℕ) (X : C) :
    (Stacks.Cohomology.RightDerivedEdge.edge P Q i).app X ≫
        (rightDerivedIsoRes (P ⋙ Q) i).hom.app X =
      (rightDerivedIsoRes Q i).hom.app (P.obj X) ≫
        (HomotopyCategory.homologyFunctor E (ComplexShape.up ℤ) (i : ℤ)).map
          ((Q.mapHomotopyCategory (ComplexShape.up ℤ)).map
            ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
              (extendResolutionComparison P X))) := by
  rw [Stacks.Cohomology.RightDerivedEdge.edge_app_eq P Q i (injectiveResolution X)
      (injectiveResolution (P.obj X)) (Stacks.Cohomology.RightDerivedEdge.resolutionComparison P X)
      (Stacks.Cohomology.RightDerivedEdge.ι_f_zero_comp_resolutionComparison P X),
    isoRightDerivedObj_injectiveResolution, isoRightDerivedObj_injectiveResolution_inv,
    rightDerivedIsoRes_hom_app_eq, rightDerivedIsoRes_hom_app_eq]
  have hA : (HomotopyCategory.homologyFunctorFactors E (ComplexShape.up ℕ) i).hom.app
        ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (injectiveResolution (P.obj X)).cocomplex) ≫
      (HomologicalComplex.homologyMap
          ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).map
            (Stacks.Cohomology.RightDerivedEdge.resolutionComparison P X)) i ≫
        (HomotopyCategory.homologyFunctorFactors E (ComplexShape.up ℕ) i).inv.app
          (((P ⋙ Q).mapHomologicalComplex (ComplexShape.up ℕ)).obj
            (injectiveResolution X).cocomplex)) =
      (HomotopyCategory.homologyFunctor E (ComplexShape.up ℕ) i).map
        ((Q.mapHomotopyCategory (ComplexShape.up ℕ)).map
          ((HomotopyCategory.quotient D (ComplexShape.up ℕ)).map
            (Stacks.Cohomology.RightDerivedEdge.resolutionComparison P X))) :=
    NatIso.naturality_2 (HomotopyCategory.homologyFunctorFactors E (ComplexShape.up ℕ) i)
      ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).map
        (Stacks.Cohomology.RightDerivedEdge.resolutionComparison P X))
  refine (congrArg (fun w => w ≫ (extendMapHomologyIso (P ⋙ Q)
    (injectiveResolution X).cocomplex i).hom) hA).trans ?_
  refine (congrArg (fun w => (HomotopyCategory.homologyFunctor E (ComplexShape.up ℕ) i).map
      ((Q.mapHomotopyCategory (ComplexShape.up ℕ)).map
        ((HomotopyCategory.quotient D (ComplexShape.up ℕ)).map
          (Stacks.Cohomology.RightDerivedEdge.resolutionComparison P X))) ≫ w)
    (extendMapHomologyIso_hom_comp P Q (injectiveResolution X).cocomplex i)).trans ?_
  refine pasteSquare _ _ _ _ _ _
    (extendMapHomologyIso_hom_naturality Q
      (Stacks.Cohomology.RightDerivedEdge.resolutionComparison P X) i) ?_
  exact (((HomotopyCategory.homologyFunctor E (ComplexShape.up ℤ) (i : ℤ)).map_comp _ _).symm.trans
    (congrArg (HomotopyCategory.homologyFunctor E (ComplexShape.up ℤ) (i : ℤ)).map
      (((Q.mapHomotopyCategory (ComplexShape.up ℤ)).map_comp _ _).symm.trans
        (congrArg (Q.mapHomotopyCategory (ComplexShape.up ℤ)).map
          (((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map_comp _ _).symm :
            _ = (HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
              (extendResolutionComparison P X))))))

end Edge

/-! ### The comparison of resolutions and the two augmentations -/

section Augmentation

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [Abelian C] [Abelian D] [EnoughInjectives C] [EnoughInjectives D]
  (P : C ⥤ D) [P.Additive] [P.PreservesInjectiveObjects]

/-- The degree-zero component of `extendResolutionComparison` is the degree-zero component of
`Stacks.Cohomology.RightDerivedEdge.resolutionComparison`, read through the identifications of the
degree-zero terms of the extensions by zero with those of the resolutions. -/
theorem extendResolutionComparison_f_zero (X : C) :
    (extendResolutionComparison P X).f 0 =
      ((injectiveResolution (P.obj X)).cochainComplexXIso 0 0 (by simp)).hom ≫
        (Stacks.Cohomology.RightDerivedEdge.resolutionComparison P X).f 0 ≫
          P.map ((injectiveResolution X).cochainComplexXIso 0 0 (by simp)).inv := by
  refine Eq.trans (HomologicalComplex.comp_f
    ((embeddingUpNat.extendFunctor D).map
      (Stacks.Cohomology.RightDerivedEdge.resolutionComparison P X))
    (mapExtendIso P embeddingUpNat (injectiveResolution X).cocomplex).hom 0) ?_
  show (HomologicalComplex.extendMap
      (Stacks.Cohomology.RightDerivedEdge.resolutionComparison P X) embeddingUpNat).f 0 ≫
      (mapExtendIso P embeddingUpNat (injectiveResolution X).cocomplex).hom.f 0 = _
  rw [HomologicalComplex.extendMap_f _ embeddingUpNat (i := 0) (by simp), Category.assoc,
    Category.assoc, extendXIso_inv_comp_mapExtendIso_hom_f]
  rfl

/-- The degree-zero component of the comparison of the two extended resolutions, precomposed with
the augmentation of the resolution of `P X`, is `P` applied to the augmentation of the
resolution of `X`. -/
private lemma ι_f_zero_comp_extendResolutionComparison_f_zero (X : C) :
    ((injectiveResolution (P.obj X)).ι.f 0 ≫
        ((injectiveResolution (P.obj X)).cochainComplexXIso 0 0 (by simp)).inv) ≫
      (((injectiveResolution (P.obj X)).cochainComplexXIso 0 0 (by simp)).hom ≫
        (Stacks.Cohomology.RightDerivedEdge.resolutionComparison P X).f 0 ≫
          P.map ((injectiveResolution X).cochainComplexXIso 0 0 (by simp)).inv) =
    P.map ((injectiveResolution X).ι.f 0 ≫
      ((injectiveResolution X).cochainComplexXIso 0 0 (by simp)).inv) := by
  rw [Category.assoc, Iso.inv_hom_id_assoc, P.map_comp,
    ← Stacks.Cohomology.RightDerivedEdge.ι_f_zero_comp_resolutionComparison P X]
  exact (Category.assoc _ _ _).symm

/-- As morphisms out of the single complex on `P X`, the augmentation of the chosen extended
resolution of `P X` followed by `extendResolutionComparison P X` is `P` applied to the
augmentation of the chosen extended resolution of `X`. -/
theorem ι'_comp_extendResolutionComparison (X : C) :
    (injectiveResolution (P.obj X)).ι' ≫ extendResolutionComparison P X =
      (HomologicalComplex.singleMapHomologicalComplex P (ComplexShape.up ℤ) 0).inv.app X ≫
        (P.mapHomologicalComplex (ComplexShape.up ℤ)).map ((injectiveResolution X).ι') := by
  refine HomologicalComplex.from_single_hom_ext ?_
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    CategoryTheory.InjectiveResolution.ι'_f_zero, extendResolutionComparison_f_zero,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
    Functor.mapHomologicalComplex_map_f, CategoryTheory.InjectiveResolution.ι'_f_zero]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, ← P.map_comp, Iso.inv_hom_id_assoc]
  exact congrArg (fun w => (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
    (P.obj X)).hom ≫ w) (ι_f_zero_comp_extendResolutionComparison_f_zero P X)

end Augmentation

/-! ### The augmentation in the bounded below homotopy category -/

section SingleIsoRes

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]

/-- The augmentation `ℱ[0] ⟶ I` in the bounded below homotopy category, where `I` is the chosen
injective resolution of `ℱ` extended by zero to a complex indexed by `ℤ`: the preimage of
`Stacks.DerivedIndexing.resUnit` under the fully faithful inclusion of `K⁺`. -/
noncomputable def resUnitPlusApp (X : C) :
    (HomotopyCategory.Plus.singleFunctor C 0).obj X ⟶ resPlus.obj X :=
  (HomotopyCategory.Plus.ι C).preimage (resUnit.app X)

/-- The defining property of `resUnitPlusApp`. -/
lemma ι_map_resUnitPlusApp (X : C) :
    (HomotopyCategory.Plus.ι C).map (resUnitPlusApp X) = resUnit.app X :=
  (HomotopyCategory.Plus.ι C).map_preimage _

/-- `resUnitPlusApp` is natural in the object. -/
noncomputable def resUnitPlus : HomotopyCategory.Plus.singleFunctor C 0 ⟶ resPlus where
  app X := resUnitPlusApp X
  naturality {X Y} f := (HomotopyCategory.Plus.ι C).map_injective
    ((Functor.map_comp _ _ _).trans
      ((congrArg (fun w => (HomotopyCategory.Plus.ι C).map
            ((HomotopyCategory.Plus.singleFunctor C 0).map f) ≫ w)
          (ι_map_resUnitPlusApp Y)).trans
        ((resUnit.naturality f).trans
          ((congrArg (fun w => w ≫ (HomotopyCategory.Plus.ι C).map (resPlus.map f))
              (ι_map_resUnitPlusApp X).symm).trans
            (Functor.map_comp _ _ _).symm))))

variable [HasDerivedCategory.{w} C]

omit [EnoughInjectives C] in
/-- The components of `CategoryTheory.Functor.singleFunctorPlusIsoCompQh` are
`Plus.ι`-preimages of the components of `DerivedCategory.singleFunctorIsoCompQh`. -/
lemma ι_map_singleFunctorPlusIsoCompQh_inv_app_degree (n : ℤ) (X : C) :
    DerivedCategory.Plus.ι.map ((Functor.singleFunctorPlusIsoCompQh (A := C) n).inv.app X) =
      (DerivedCategory.singleFunctorIsoCompQh C n).inv.app X :=
  DerivedCategory.Plus.ι.map_preimage _

omit [EnoughInjectives C] in
/-- The components of `CategoryTheory.Functor.singleFunctorPlusIsoCompQh` are
`Plus.ι`-preimages of the components of `DerivedCategory.singleFunctorIsoCompQh`. -/
lemma ι_map_singleFunctorPlusIsoCompQh_inv_app (X : C) :
    DerivedCategory.Plus.ι.map ((Functor.singleFunctorPlusIsoCompQh (A := C) 0).inv.app X) =
      (DerivedCategory.singleFunctorIsoCompQh C 0).inv.app X :=
  ι_map_singleFunctorPlusIsoCompQh_inv_app_degree 0 X

/-- The components of `Stacks.DerivedIndexing.singleIsoResPlusQh` are `Plus.ι`-preimages of the
components of the five-step comparison it is built from. -/
lemma ι_map_singleIsoResPlusQh_hom_app (X : C) :
    DerivedCategory.Plus.ι.map ((singleIsoResPlusQh (C := C)).hom.app X) =
      (DerivedCategory.Plus.singleFunctorιIso C 0 ≪≫
        DerivedCategory.singleFunctorIsoCompQh C 0 ≪≫
        asIso (Functor.whiskerRight (resUnit (C := C)) DerivedCategory.Qh) ≪≫
        (Functor.isoWhiskerRight (resPlusCompιIso (C := C)) DerivedCategory.Qh).symm ≪≫
        (Functor.isoWhiskerLeft resPlus
          (DerivedCategory.Plus.QhCompιIsoιCompQh C)).symm).hom.app X :=
  DerivedCategory.Plus.ι.map_preimage _

omit [EnoughInjectives C] in
/-- `DerivedCategory.Plus.Qh` is induced by `DerivedCategory.Qh`, on the nose. -/
lemma ι_map_Plus_Qh_map {K L : HomotopyCategory.Plus C} (f : K ⟶ L) :
    DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Qh.map f) =
      DerivedCategory.Qh.map ((HomotopyCategory.Plus.ι C).map f) := rfl

omit [EnoughInjectives C] in
/-- `DerivedCategory.Plus.singleFunctorιIso` has identity components. -/
lemma singleFunctorιIso_hom_app (X : C) :
    (DerivedCategory.Plus.singleFunctorιIso C 0).hom.app X =
      𝟙 ((DerivedCategory.Plus.singleFunctor C 0 ⋙ DerivedCategory.Plus.ι).obj X) := rfl

omit [HasDerivedCategory.{w} C] in
/-- `Stacks.DerivedIndexing.resPlusCompιIso` has identity components. -/
lemma resPlusCompιIso_inv_app (X : C) :
    (resPlusCompιIso (C := C)).inv.app X = 𝟙 (resH.obj X) := rfl

omit [EnoughInjectives C] in
/-- `DerivedCategory.Plus.QhCompιIsoιCompQh` has identity components. -/
lemma QhCompιIsoιCompQh_inv_app (K : HomotopyCategory.Plus C) :
    (DerivedCategory.Plus.QhCompιIsoιCompQh C).inv.app K =
      𝟙 ((HomotopyCategory.Plus.ι C ⋙ DerivedCategory.Qh).obj K) := rfl

omit [EnoughInjectives C] in
/-- `DerivedCategory.Plus.QhCompιIsoιCompQh` has identity components, the other way round. -/
lemma QhCompιIsoιCompQh_hom_app (K : HomotopyCategory.Plus C) :
    (DerivedCategory.Plus.QhCompιIsoιCompQh C).hom.app K =
      𝟙 ((DerivedCategory.Plus.Qh ⋙ DerivedCategory.Plus.ι).obj K) := rfl

/-- Three identity morphisms, given as hypotheses, cancelled out of a right-associated composite
of five. -/
private lemma head_id {X : Type*} [Category* X] {a b c : X} (q : a ⟶ b) (r : b ⟶ c)
    (i₁ : a ⟶ a) (i₂ i₃ : c ⟶ c) (h₁ : i₁ = 𝟙 a) (h₂ : i₂ = 𝟙 c) (h₃ : i₃ = 𝟙 c) :
    i₁ ≫ q ≫ r ≫ i₂ ≫ i₃ = q ≫ r := by
  subst h₁ h₂ h₃; simp

/-- The closed form of `Stacks.DerivedIndexing.singleIsoResPlusQh`: it is the image under `Qh`
of the augmentation, composed with the identification of the single functor into `D(𝒜)` with the
single functor into `K(𝒜)` followed by `Qh`. -/
private lemma ι_map_singleIsoResPlusQh_hom_app_eq_aux (X : C) :
    DerivedCategory.Plus.ι.map ((singleIsoResPlusQh (C := C)).hom.app X) =
      (DerivedCategory.singleFunctorIsoCompQh C 0).hom.app X ≫
        DerivedCategory.Qh.map (resUnit.app X) := by
  rw [ι_map_singleIsoResPlusQh_hom_app]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, asIso_hom,
    Functor.whiskerRight_app, Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
    Functor.whiskerLeft_app, singleFunctorιIso_hom_app, resPlusCompιIso_inv_app,
    QhCompιIsoιCompQh_inv_app]
  exact head_id _ _ _ _ _ rfl
    (CategoryTheory.Functor.map_id DerivedCategory.Qh (resH.obj X)) rfl

/-- The identification of `ℱ[0]` in `D⁺(𝒜)` with the image of the chosen extended injective
resolution is, after the identification of the single functor into `D⁺(𝒜)` with the single
functor into `K⁺(𝒜)` followed by `Qh`, the image under `Qh` of the augmentation `ℱ[0] ⟶ I` of
`K⁺(𝒜)`. -/
theorem singleFunctorPlusIsoCompQh_inv_app_comp_singleIsoResPlusQh_hom_app (X : C) :
    (Functor.singleFunctorPlusIsoCompQh (A := C) 0).inv.app X ≫
        (singleIsoResPlusQh (C := C)).hom.app X =
      DerivedCategory.Plus.Qh.map (resUnitPlusApp X) := by
  apply DerivedCategory.Plus.ι.map_injective
  rw [Functor.map_comp, ι_map_singleFunctorPlusIsoCompQh_inv_app,
    ι_map_singleIsoResPlusQh_hom_app_eq_aux, ι_map_Plus_Qh_map, ι_map_resUnitPlusApp]
  exact Iso.inv_hom_id_app_assoc _ _ _

end SingleIsoRes

/-! ### The comparison of the single functors with the single functors on complexes -/

section SingleUnwind

/-- Two identity morphisms, given as hypotheses, cancelled out of a composite of three. -/
private lemma cancel_ids_mid {X : Type*} [Category* X] {a b c : X} (u : a ⟶ b) (q : b ⟶ c)
    (i₁ : b ⟶ b) (i₂ : c ⟶ c) (h₁ : i₁ = 𝟙 b) (h₂ : i₂ = 𝟙 c) :
    ((u ≫ i₁) ≫ q) ≫ i₂ = u ≫ q := by
  subst h₁ h₂; simp

/-- Six identity morphisms, given as hypotheses, cancelled out of a left-associated composite of
seven. -/
private lemma cancel_ids₆ {X : Type*} [Category* X] {a b : X} (q : a ⟶ b)
    (i₁ i₂ : a ⟶ a) (i₃ i₄ i₅ i₆ : b ⟶ b) (h₁ : i₁ = 𝟙 a) (h₂ : i₂ = 𝟙 a)
    (h₃ : i₃ = 𝟙 b) (h₄ : i₄ = 𝟙 b) (h₅ : i₅ = 𝟙 b) (h₆ : i₆ = 𝟙 b) :
    (((((i₁ ≫ i₂) ≫ q) ≫ i₃) ≫ i₄) ≫ i₅) ≫ i₆ = q := by
  subst h₁ h₂ h₃ h₄ h₅ h₆; simp

/-- A common factor pulled out of two left-associated composites. -/
private lemma reassoc_of_eq {X : Type*} [Category* X] {a b d c c' : X} (u : a ⟶ b)
    (x : b ⟶ c) (y : c ⟶ d) (x' : b ⟶ c') (y' : c' ⟶ d) (h : x ≫ y = x' ≫ y') :
    (u ≫ x) ≫ y = (u ≫ x') ≫ y' := by
  rw [Category.assoc, Category.assoc, h]

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [Abelian C] [Abelian D] (P : C ⥤ D) [P.Additive]

omit [Abelian D] [P.Additive] in
/-- `HomotopyCategory.singleFunctorPostcompQuotientIso` has identity components. -/
lemma singleFunctorPostcompQuotientIso_hom_app_degree (n : ℤ) (X : C) :
    (HomotopyCategory.singleFunctorPostcompQuotientIso C n).hom.app X =
      𝟙 ((HomotopyCategory.singleFunctor C n).obj X) := rfl

omit [Abelian D] [P.Additive] in
/-- `HomotopyCategory.singleFunctorPostcompQuotientIso` has identity components. -/
lemma singleFunctorPostcompQuotientIso_inv_app_degree (n : ℤ) (X : C) :
    (HomotopyCategory.singleFunctorPostcompQuotientIso C n).inv.app X =
      𝟙 ((HomotopyCategory.singleFunctor C n).obj X) := rfl

omit [Abelian D] [P.Additive] in
/-- `HomotopyCategory.singleFunctorPostcompQuotientIso` has identity components. -/
lemma singleFunctorPostcompQuotientIso_hom_app (X : C) :
    (HomotopyCategory.singleFunctorPostcompQuotientIso C 0).hom.app X =
      𝟙 ((HomotopyCategory.singleFunctor C 0).obj X) := rfl

omit [Abelian D] [P.Additive] in
/-- `HomotopyCategory.singleFunctorPostcompQuotientIso` has identity components. -/
lemma singleFunctorPostcompQuotientIso_inv_app (X : C) :
    (HomotopyCategory.singleFunctorPostcompQuotientIso C 0).inv.app X =
      𝟙 ((HomotopyCategory.singleFunctor C 0).obj X) := rfl

/-- `CategoryTheory.Functor.mapHomotopyCategoryFactors` has identity components. -/
lemma mapHomotopyCategoryFactors_inv_app (K : HomologicalComplex C (ComplexShape.up ℤ)) :
    (P.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app K =
      𝟙 ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj
        ((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) := rfl

/-- `CategoryTheory.Functor.mapHomotopyCategorySingleFunctor` is the class of
`HomologicalComplex.singleMapHomologicalComplex`: the identification of `P(ℱ[n])` with
`(Pℱ)[n]` in the homotopy category is the one on complexes, read through the quotient. -/
lemma mapHomotopyCategorySingleFunctor_inv_app_degree (n : ℤ) (X : C) :
    (P.mapHomotopyCategorySingleFunctor n).inv.app X =
      (HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex P (ComplexShape.up ℤ) n).inv.app X) := by
  simp only [Functor.mapHomotopyCategorySingleFunctor, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.isoWhiskerRight_inv, Functor.whiskerRight_app, Functor.isoWhiskerLeft_inv,
    Functor.whiskerLeft_app, singleFunctorPostcompQuotientIso_hom_app_degree,
    singleFunctorPostcompQuotientIso_inv_app_degree, mapHomotopyCategoryFactors_inv_app]
  exact cancel_ids₆ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl
    (CategoryTheory.Functor.map_id (P.mapHomotopyCategory (ComplexShape.up ℤ))
      ((HomotopyCategory.singleFunctor C n).obj X))

/-- `CategoryTheory.Functor.mapHomotopyCategorySingleFunctor` is the class of
`HomologicalComplex.singleMapHomologicalComplex` in degree zero: the case `n = 0` of
`mapHomotopyCategorySingleFunctor_inv_app_degree`. -/
lemma mapHomotopyCategorySingleFunctor_inv_app (X : C) :
    (P.mapHomotopyCategorySingleFunctor 0).inv.app X =
      (HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex P (ComplexShape.up ℤ) 0).inv.app X) :=
  mapHomotopyCategorySingleFunctor_inv_app_degree P 0 X

variable [HasDerivedCategory.{w} D]

/-- The components of `CategoryTheory.Functor.mapSingleFunctorCompQhIsoOfDegree` are
`Plus.ι`-preimages of the components of the four-step comparison it is built from. -/
lemma ι_map_mapSingleFunctorCompQhIsoOfDegree_inv_app_steps (n : ℤ) (X : C) :
    DerivedCategory.Plus.ι.map ((Functor.mapSingleFunctorCompQhIsoOfDegree P n).inv.app X) =
      ((Functor.associator (HomotopyCategory.singleFunctor C n)
            (P.mapHomotopyCategory (ComplexShape.up ℤ)) DerivedCategory.Qh).symm ≪≫
        Functor.isoWhiskerRight (P.mapHomotopyCategorySingleFunctor n) DerivedCategory.Qh ≪≫
        Functor.associator P (HomotopyCategory.singleFunctor D n) DerivedCategory.Qh ≪≫
        Functor.isoWhiskerLeft P
          (DerivedCategory.singleFunctorIsoCompQh D n).symm).inv.app X :=
  DerivedCategory.Plus.ι.map_preimage _

/-- The closed form of `CategoryTheory.Functor.mapSingleFunctorCompQhIsoOfDegree`: it is the
identification `HomologicalComplex.singleMapHomologicalComplex` of complexes, read through the
quotient and the localization, composed with the identification of the single functor into
`D(ℬ)` with the single functor into `K(ℬ)` followed by `Qh`. -/
lemma ι_map_mapSingleFunctorCompQhIsoOfDegree_inv_app (n : ℤ) (X : C) :
    DerivedCategory.Plus.ι.map ((Functor.mapSingleFunctorCompQhIsoOfDegree P n).inv.app X) =
      (DerivedCategory.singleFunctorIsoCompQh D n).hom.app (P.obj X) ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex P
            (ComplexShape.up ℤ) n).inv.app X)) := by
  rw [ι_map_mapSingleFunctorCompQhIsoOfDegree_inv_app_steps]
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
    mapHomotopyCategorySingleFunctor_inv_app_degree]
  exact cancel_ids_mid _ _ _ _ rfl rfl

/-- The components of `CategoryTheory.Functor.mapSingleFunctorCompQhIso` are `Plus.ι`-preimages
of the components of the four-step comparison it is built from. This is the case `n = 0` of
`ι_map_mapSingleFunctorCompQhIsoOfDegree_inv_app_steps`. -/
lemma ι_map_mapSingleFunctorCompQhIso_inv_app' (X : C) :
    DerivedCategory.Plus.ι.map ((Functor.mapSingleFunctorCompQhIso P).inv.app X) =
      ((Functor.associator (HomotopyCategory.singleFunctor C 0)
            (P.mapHomotopyCategory (ComplexShape.up ℤ)) DerivedCategory.Qh).symm ≪≫
        Functor.isoWhiskerRight (P.mapHomotopyCategorySingleFunctor 0) DerivedCategory.Qh ≪≫
        Functor.associator P (HomotopyCategory.singleFunctor D 0) DerivedCategory.Qh ≪≫
        Functor.isoWhiskerLeft P
          (DerivedCategory.singleFunctorIsoCompQh D 0).symm).inv.app X :=
  ι_map_mapSingleFunctorCompQhIsoOfDegree_inv_app_steps P 0 X

/-- The closed form of `CategoryTheory.Functor.mapSingleFunctorCompQhIso`: the case `n = 0` of
`ι_map_mapSingleFunctorCompQhIsoOfDegree_inv_app`. -/
lemma ι_map_mapSingleFunctorCompQhIso_inv_app (X : C) :
    DerivedCategory.Plus.ι.map ((Functor.mapSingleFunctorCompQhIso P).inv.app X) =
      (DerivedCategory.singleFunctorIsoCompQh D 0).hom.app (P.obj X) ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex P
            (ComplexShape.up ℤ) 0).inv.app X)) :=
  ι_map_mapSingleFunctorCompQhIsoOfDegree_inv_app P 0 X

end SingleUnwind

/-! ### The unit of `RP` at the chosen extended injective resolutions -/

section KeyEquation

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [Abelian C] [Abelian D] [EnoughInjectives C] [EnoughInjectives D]
  (P : C ⥤ D) [P.Additive] [P.PreservesInjectiveObjects]

omit [EnoughInjectives D] [P.Additive] [P.PreservesInjectiveObjects] in
/-- The components of `Stacks.DerivedIndexing.resUnit` are the classes of the augmentations of
the chosen extended injective resolutions. -/
lemma resUnit_app (X : C) :
    resUnit.app X =
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map (injectiveResolution X).ι' := rfl

omit [EnoughInjectives C] [EnoughInjectives D] [P.PreservesInjectiveObjects] in
/-- `CategoryTheory.Functor.mapHomotopyCategoryPlus` is induced by
`CategoryTheory.Functor.mapHomotopyCategory`, on the nose. -/
lemma ι_map_mapHomotopyCategoryPlus_map {K L : HomotopyCategory.Plus C} (f : K ⟶ L) :
    (HomotopyCategory.Plus.ι D).map (P.mapHomotopyCategoryPlus.map f) =
      (P.mapHomotopyCategory (ComplexShape.up ℤ)).map ((HomotopyCategory.Plus.ι C).map f) := rfl

/-- The comparison of the extended injective resolutions, read in `K⁺(ℬ)`: the class of
`Stacks.DerivedIndexing.extendResolutionComparison`. -/
noncomputable def extendResolutionComparisonPlus (X : C) :
    resPlus.obj (P.obj X) ⟶ P.mapHomotopyCategoryPlus.obj (resPlus.obj X) :=
  (HomotopyCategory.Plus.ι D).preimage
    ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map (extendResolutionComparison P X))

/-- The defining property of `extendResolutionComparisonPlus`. -/
lemma ι_map_extendResolutionComparisonPlus (X : C) :
    (HomotopyCategory.Plus.ι D).map (extendResolutionComparisonPlus P X) =
      (HomotopyCategory.quotient D (ComplexShape.up ℤ)).map (extendResolutionComparison P X) :=
  (HomotopyCategory.Plus.ι D).map_preimage _

/-- `ι'_comp_extendResolutionComparison`, read in the homotopy category: the augmentation of the
chosen resolution of `P X`, followed by the comparison of the extended resolutions, is `P`
applied to the augmentation of the chosen resolution of `X`. -/
lemma resUnit_app_comp_quotient_map_extendResolutionComparison (X : C) :
    resUnit.app (P.obj X) ≫ (HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
          (extendResolutionComparison P X) =
      (HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex P (ComplexShape.up ℤ) 0).inv.app X) ≫
        (P.mapHomotopyCategory (ComplexShape.up ℤ)).map (resUnit.app X) :=
  ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map_comp _ _).symm.trans
    ((congrArg (HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
        (ι'_comp_extendResolutionComparison P X)).trans
      ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map_comp _ _))

variable [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]

omit [EnoughInjectives D] [P.Additive] [P.PreservesInjectiveObjects] in
/-- The closed form of `Stacks.DerivedIndexing.singleIsoResPlusQh`: it is the image under `Qh`
of the augmentation, composed with the identification of the single functor into `D(𝒜)` with the
single functor into `K(𝒜)` followed by `Qh`. -/
lemma ι_map_singleIsoResPlusQh_hom_app_eq (X : C) :
    DerivedCategory.Plus.ι.map ((singleIsoResPlusQh (C := C)).hom.app X) =
      (DerivedCategory.singleFunctorIsoCompQh C 0).hom.app X ≫
        DerivedCategory.Qh.map (resUnit.app X) :=
  ι_map_singleIsoResPlusQh_hom_app_eq_aux X

omit [HasDerivedCategory.{w} C] in
/-- In `D⁺(ℬ)`, identifying `(Pℱ)[0]` with the image of the chosen extended injective resolution
of `Pℱ` and then comparing with `P` applied to the chosen extended injective resolution of `ℱ` is
the same as identifying `P(ℱ[0])` with `(Pℱ)[0]` and then applying `P` to the augmentation of the
resolution of `ℱ`. -/
theorem singleIsoResPlusQh_hom_app_comp_extendResolutionComparisonPlus (X : C) :
    (singleIsoResPlusQh (C := D)).hom.app (P.obj X) ≫
        DerivedCategory.Plus.Qh.map (extendResolutionComparisonPlus P X) =
      (Functor.mapSingleFunctorCompQhIso P).inv.app X ≫
        DerivedCategory.Plus.Qh.map
          (P.mapHomotopyCategoryPlus.map (resUnitPlusApp X)) := by
  apply DerivedCategory.Plus.ι.map_injective
  rw [Functor.map_comp, Functor.map_comp, ι_map_singleIsoResPlusQh_hom_app_eq,
    ι_map_mapSingleFunctorCompQhIso_inv_app, ι_map_Plus_Qh_map, ι_map_Plus_Qh_map,
    ι_map_extendResolutionComparisonPlus, ι_map_mapHomotopyCategoryPlus_map,
    ι_map_resUnitPlusApp]
  exact reassoc_of_eq _ _ _ _ _
    ((DerivedCategory.Qh.map_comp _ _).symm.trans
      ((congrArg DerivedCategory.Qh.map
          (resUnit_app_comp_quotient_map_extendResolutionComparison P X)).trans
        (DerivedCategory.Qh.map_comp _ _)))

omit [EnoughInjectives D] [P.PreservesInjectiveObjects] in
/-- The components of `Stacks.DerivedIndexing.rightDerivedPlusUnitSingle`. -/
lemma rightDerivedPlusUnitSingle_app (X : C) :
    (rightDerivedPlusUnitSingle P).app X =
      (Functor.mapSingleFunctorCompQhIso P).inv.app X ≫
        P.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.singleFunctor C 0).obj X) ≫
          P.rightDerivedFunctorPlus.map
            ((Functor.singleFunctorPlusIsoCompQh (A := C) 0).inv.app X) := rfl

/-- In `D⁺(ℬ)`: the canonical map `(Pℱ)[0] ⟶ RP(ℱ[0])`, followed by `RP` applied to the
identification of `ℱ[0]` with the image of the chosen extended injective resolution `I` of `ℱ`,
equals the identification of `(Pℱ)[0]` with the image of the chosen extended injective
resolution of `Pℱ`, followed by the comparison with `P(I)` and the unit of `RP` at `P(I)`. -/
theorem rightDerivedPlusUnitSingle_app_comp_map_singleIsoResPlusQh (X : C) :
    (rightDerivedPlusUnitSingle P).app X ≫
        P.rightDerivedFunctorPlus.map ((singleIsoResPlusQh (C := C)).hom.app X) =
      (singleIsoResPlusQh (C := D)).hom.app (P.obj X) ≫
        DerivedCategory.Plus.Qh.map (extendResolutionComparisonPlus P X) ≫
          P.rightDerivedFunctorPlusUnit.app (resPlus.obj X) := by
  have hnat : P.rightDerivedFunctorPlusUnit.app
          ((HomotopyCategory.Plus.singleFunctor C 0).obj X) ≫
        P.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map (resUnitPlusApp X)) =
      DerivedCategory.Plus.Qh.map (P.mapHomotopyCategoryPlus.map (resUnitPlusApp X)) ≫
        P.rightDerivedFunctorPlusUnit.app (resPlus.obj X) :=
    (P.rightDerivedFunctorPlusUnit.naturality (resUnitPlusApp X)).symm
  rw [rightDerivedPlusUnitSingle_app, Category.assoc, Category.assoc,
    ← P.rightDerivedFunctorPlus.map_comp,
    singleFunctorPlusIsoCompQh_inv_app_comp_singleIsoResPlusQh_hom_app,
    hnat, ← Category.assoc,
    ← singleIsoResPlusQh_hom_app_comp_extendResolutionComparisonPlus, Category.assoc]

end KeyEquation

/-! ### The closed form of the five-step comparison -/

section IsoResApp

/-- Two identity morphisms, given as hypotheses, cancelled off the tail of a right-associated
composite of five. -/
private lemma tail_ids {X : Type*} [Category* X] {a b c d : X} (q : a ⟶ b) (r : b ⟶ c)
    (p : c ⟶ d) (i₁ i₂ : d ⟶ d) (h₁ : i₁ = 𝟙 d) (h₂ : i₂ = 𝟙 d) :
    q ≫ r ≫ p ≫ i₁ ≫ i₂ = q ≫ r ≫ p := by subst h₁ h₂; simp

variable {A : Type u} {B : Type u'} [Category.{v} A] [Category.{v'} B] [Abelian A] [Abelian B]
  [EnoughInjectives A] [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
  (F : A ⥤ B) [F.Additive]

/-- The closed form of `Stacks.DerivedIndexing.rightDerivedPlusIsoRes`: its last two steps,
`Stacks.DerivedIndexing.mapPlusCompιIso` and `Stacks.DerivedIndexing.resPlusCompιIso`, have
identity components, so the comparison is the composite of the first three. -/
lemma rightDerivedPlusIsoRes_hom_app (n : ℤ) (X : A) :
    (rightDerivedPlusIsoRes F n).hom.app X =
      (DerivedCategory.Plus.homologyFunctor B n).map
          (F.rightDerivedFunctorPlus.map ((singleIsoResPlusQh (C := A)).hom.app X)) ≫
        (DerivedCategory.Plus.homologyFunctor B n).map ((resDerivedIso F).inv.app X) ≫
          (plusHomologyIso (D := B) n).hom.app
            (F.mapHomotopyCategoryPlus.obj (resPlus.obj X)) := by
  have h₄ : (mapPlusCompιIso F).hom.app (resPlus.obj X) = 𝟙 _ := rfl
  have h₅ : (resPlusCompιIso (C := A)).hom.app X = 𝟙 _ := rfl
  have h : (rightDerivedPlusIsoRes F n).hom.app X =
      (DerivedCategory.Plus.homologyFunctor B n).map
          (F.rightDerivedFunctorPlus.map ((singleIsoResPlusQh (C := A)).hom.app X)) ≫
        (DerivedCategory.Plus.homologyFunctor B n).map ((resDerivedIso F).inv.app X) ≫
          (plusHomologyIso (D := B) n).hom.app
              (F.mapHomotopyCategoryPlus.obj (resPlus.obj X)) ≫
            (HomotopyCategory.homologyFunctor B (ComplexShape.up ℤ) n).map
                ((mapPlusCompιIso F).hom.app (resPlus.obj X)) ≫
              (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
                  HomotopyCategory.homologyFunctor B (ComplexShape.up ℤ) n).map
                ((resPlusCompιIso (C := A)).hom.app X) := rfl
  exact h.trans (tail_ids _ _ _ _ _
    ((congrArg (HomotopyCategory.homologyFunctor B (ComplexShape.up ℤ) n).map h₄).trans
      ((HomotopyCategory.homologyFunctor B (ComplexShape.up ℤ) n).map_id _))
    ((congrArg (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          HomotopyCategory.homologyFunctor B (ComplexShape.up ℤ) n).map h₅).trans
      ((F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        HomotopyCategory.homologyFunctor B (ComplexShape.up ℤ) n).map_id _)))

end IsoResApp

/-! ### The identification of the edge morphism with the degreewise comparison -/

section EdgeIdentification

/-- One identity morphism, given as a hypothesis, cancelled off the head of a composite. -/
private lemma id_comp_of_eq {X : Type*} [Category* X] {a b : X} (q : a ⟶ b) (i : a ⟶ a)
    (h : i = 𝟙 a) : i ≫ q = q := by subst h; simp

/-- Two morphisms that agree after composition with two isomorphisms agree. -/
private lemma eq_of_postcomp_isos {X : Type*} [Category* X] {a b c d : X} {f g : a ⟶ b}
    (h : b ≅ c) (k : c ≅ d) (e : f ≫ h.hom ≫ k.hom = g ≫ h.hom ≫ k.hom) : f = g := by
  simpa using congrArg (fun z => z ≫ k.inv ≫ h.inv) e

/-- A commuting square with invertible horizontal edges, transported to the inverses. -/
lemma inv_comm_of_comm_iso {X : Type*} [Category* X] {a b c d : X} (u₁ : a ≅ b) (u₂ : c ≅ d)
    (f : a ⟶ c) (g : b ⟶ d) (h : f ≫ u₂.hom = u₁.hom ≫ g) : g ≫ u₂.inv = u₁.inv ≫ f := by
  rw [← cancel_epi u₁.hom, ← Category.assoc, ← h, Category.assoc, u₂.hom_inv_id,
    Category.comp_id, ← Category.assoc, u₁.hom_inv_id, Category.id_comp]

/-- A commuting square with invertible horizontal edges, transported to the inverses; this is
`inv_comm_of_comm_iso`. -/
private alias inv_comm_of_comm := inv_comm_of_comm_iso

/-- Two composites ending in `Dhom ≫ T` agree, given the cancellations `hC`, `hD`, `hE`, the
commuting squares `hnat`, `hfac`, `hpsi` and the equation `hK`. -/
private lemma residual_square {X : Type*} [Category* X] {a b c d e f j k m : X}
    (A : a ⟶ b) (Cinv : b ⟶ c) (Chom : c ⟶ b) (Ss : c ⟶ d) (Dinv : d ⟶ e) (Dhom : e ⟶ d)
    (T : d ⟶ f) (RPs : b ⟶ f) (Sp : a ⟶ j) (Einv : j ⟶ k) (Ehom : k ⟶ j) (Psi : k ⟶ e)
    (aQI : e ⟶ m) (RQaP : m ⟶ f) (QhPsi : j ⟶ m)
    (hC : Cinv ≫ Chom = 𝟙 b) (hD : Dinv ≫ Dhom = 𝟙 d) (hE : Einv ≫ Ehom = 𝟙 j)
    (hnat : Ss ≫ T = Chom ≫ RPs) (hfac : Dhom ≫ T = aQI ≫ RQaP)
    (hpsi : Psi ≫ aQI = Ehom ≫ QhPsi) (hK : A ≫ RPs = Sp ≫ QhPsi ≫ RQaP) :
    (A ≫ Cinv ≫ Ss ≫ Dinv) ≫ Dhom ≫ T = (Sp ≫ Einv ≫ Psi) ≫ Dhom ≫ T := by
  have h₁ : (A ≫ Cinv ≫ Ss ≫ Dinv) ≫ Dhom ≫ T = A ≫ Cinv ≫ Ss ≫ T := by
    simp only [Category.assoc]
    rw [← Category.assoc Dinv Dhom T, hD, Category.id_comp]
  have h₂ : A ≫ Cinv ≫ Ss ≫ T = A ≫ RPs := by
    rw [hnat, ← Category.assoc Cinv Chom RPs, hC, Category.id_comp]
  have h₃ : (Sp ≫ Einv ≫ Psi) ≫ Dhom ≫ T = Sp ≫ QhPsi ≫ RQaP := by
    simp only [Category.assoc]
    rw [hfac, ← Category.assoc Psi aQI RQaP, hpsi, Category.assoc,
      ← Category.assoc Einv Ehom, hE, Category.id_comp]
  rw [h₁, h₂, h₃, hK]

/-- A functor applied to an equation between a composite of four and a composite of three. -/
private lemma map_comp_four {X Y : Type*} [Category* X] [Category* Y] (G : X ⥤ Y)
    {a b c d e j k : X} (A : a ⟶ b) (B : b ⟶ c) (Cc : c ⟶ d) (Dd : d ⟶ e)
    (A' : a ⟶ j) (B' : j ⟶ k) (C' : k ⟶ e) (h : A ≫ B ≫ Cc ≫ Dd = A' ≫ B' ≫ C') :
    G.map A ≫ G.map B ≫ G.map Cc ≫ G.map Dd = G.map A' ≫ G.map B' ≫ G.map C' := by
  simp only [← G.map_comp]
  exact congrArg G.map h

/-- A computed composite pasted onto a commuting square, in the bracketing in which the goal
presents it. -/
private lemma paste_tail {X : Type*} [Category* X] {a₀ a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ : X}
    (x₁ : a₀ ⟶ a₁) (x₂ : a₁ ⟶ a₂) (x₃ : a₂ ⟶ a₃) (x₄ : a₃ ⟶ a₄) (p : a₄ ⟶ a₅)
    (y₁ : a₀ ⟶ b₁) (y₂ : b₁ ⟶ b₂) (y₃ : b₂ ⟶ a₄) (p' : b₂ ⟶ b₃) (z : b₃ ⟶ a₅)
    (h₁ : x₁ ≫ x₂ ≫ x₃ ≫ x₄ = y₁ ≫ y₂ ≫ y₃) (h₂ : y₃ ≫ p = p' ≫ z) :
    (x₁ ≫ x₂) ≫ x₃ ≫ x₄ ≫ p = (y₁ ≫ y₂ ≫ p') ≫ z := by
  simp only [Category.assoc, reassoc_of% h₁, h₂]

attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {C : Type u} {D : Type u'} {E : Type u''}
  [Category.{v} C] [Category.{v'} D] [Category.{v''} E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D] [HasDerivedCategory.{w''} E]
  [EnoughInjectives C] [EnoughInjectives D]
  (P : C ⥤ D) (Q : D ⥤ E) [P.Additive] [Q.Additive] [P.PreservesInjectiveObjects]

omit [P.PreservesInjectiveObjects] in
/-- The components of `Stacks.DerivedIndexing.rightDerivedPlusCompUnit`: the unit of `RQ` at
`P(K)`, followed by `RQ` applied to the unit of `RP` at `K`. -/
lemma rightDerivedPlusCompUnit_app (K : HomotopyCategory.Plus C) :
    (rightDerivedPlusCompUnit P Q).app K =
      Q.rightDerivedFunctorPlusUnit.app (P.mapHomotopyCategoryPlus.obj K) ≫
        Q.rightDerivedFunctorPlus.map (P.rightDerivedFunctorPlusUnit.app K) := by
  have hid : (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (P ⋙ Q))).inv.app K = 𝟙 _ :=
    ObjectProperty.hom_ext _ rfl
  simp only [rightDerivedPlusCompUnit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  exact id_comp_of_eq _ _ ((congrArg DerivedCategory.Plus.Qh.map hid).trans
    (DerivedCategory.Plus.Qh.map_id _))

/-- Let `I` and `J` be the chosen extended injective resolutions of `ℱ` and of `Pℱ`, and
`ψ : J ⟶ P(I)` the comparison of the two. In `D⁺(𝒞)`, `RQ` of the canonical map
`(Pℱ)[0] ⟶ RP(ℱ[0])`, followed by the inverse of the composition isomorphism, `R(Q ∘ P)` of the
identification of `ℱ[0]` with `I` and the inverse of the unit of `R(Q ∘ P)` at `I`, equals `RQ`
of the identification of `(Pℱ)[0]` with `J`, followed by the inverse of the unit of `RQ` at `J`
and `Q(ψ)`. -/
theorem map_rightDerivedPlusUnitSingle_app_comp_rightDerivedPlusCompIso_inv_app (X : C) :
    Q.rightDerivedFunctorPlus.map ((rightDerivedPlusUnitSingle P).app X) ≫
        (rightDerivedPlusCompIso P Q).inv.app
            ((DerivedCategory.Plus.singleFunctor C 0).obj X) ≫
          (P ⋙ Q).rightDerivedFunctorPlus.map ((singleIsoResPlusQh (C := C)).hom.app X) ≫
            (resDerivedIso (P ⋙ Q)).inv.app X =
      Q.rightDerivedFunctorPlus.map ((singleIsoResPlusQh (C := D)).hom.app (P.obj X)) ≫
        (resDerivedIso Q).inv.app (P.obj X) ≫
          DerivedCategory.Plus.Qh.map
            (Q.mapHomotopyCategoryPlus.map (extendResolutionComparisonPlus P X)) := by
  have hK : Q.rightDerivedFunctorPlus.map ((rightDerivedPlusUnitSingle P).app X) ≫
        Q.rightDerivedFunctorPlus.map
          (P.rightDerivedFunctorPlus.map ((singleIsoResPlusQh (C := C)).hom.app X)) =
      Q.rightDerivedFunctorPlus.map ((singleIsoResPlusQh (C := D)).hom.app (P.obj X)) ≫
        Q.rightDerivedFunctorPlus.map
            (DerivedCategory.Plus.Qh.map (extendResolutionComparisonPlus P X)) ≫
          Q.rightDerivedFunctorPlus.map
            (P.rightDerivedFunctorPlusUnit.app (resPlus.obj X)) :=
    (Q.rightDerivedFunctorPlus.map_comp _ _).symm.trans
      ((congrArg Q.rightDerivedFunctorPlus.map
          (rightDerivedPlusUnitSingle_app_comp_map_singleIsoResPlusQh P X)).trans
        ((Q.rightDerivedFunctorPlus.map_comp _ _).trans
          (congrArg (fun z => Q.rightDerivedFunctorPlus.map
              ((singleIsoResPlusQh (C := D)).hom.app (P.obj X)) ≫ z)
            (Q.rightDerivedFunctorPlus.map_comp _ _))))
  refine eq_of_postcomp_isos ((resDerivedIso (P ⋙ Q)).app X)
    ((rightDerivedPlusCompIso P Q).app (DerivedCategory.Plus.Qh.obj (resPlus.obj X))) ?_
  exact residual_square _ _ ((rightDerivedPlusCompIso P Q).hom.app _) _ _ _ _ _ _ _
    ((resDerivedIso Q).hom.app (P.obj X)) _
    (Q.rightDerivedFunctorPlusUnit.app (P.mapHomotopyCategoryPlus.obj (resPlus.obj X))) _ _
    (Iso.inv_hom_id_app _ _) (Iso.inv_hom_id_app _ _) (Iso.inv_hom_id_app _ _)
    ((rightDerivedPlusCompIso P Q).hom.naturality ((singleIsoResPlusQh (C := C)).hom.app X))
    ((rightDerivedPlusCompTrans_fac_app P Q (resPlus.obj X)).trans
      (rightDerivedPlusCompUnit_app P Q (resPlus.obj X)))
    (Q.rightDerivedFunctorPlusUnit.naturality (extendResolutionComparisonPlus P X)) hK

/-- The components of `Stacks.DerivedIndexing.rightDerivedPlusEdge`. -/
lemma rightDerivedPlusEdge_app (i : ℤ) (X : C) :
    (rightDerivedPlusEdge P Q i).app X =
      (DerivedCategory.Plus.homologyFunctor E i).map
          (Q.rightDerivedFunctorPlus.map ((rightDerivedPlusUnitSingle P).app X)) ≫
        (DerivedCategory.Plus.homologyFunctor E i).map
          ((rightDerivedPlusCompIso P Q).inv.app
            ((DerivedCategory.Plus.singleFunctor C 0).obj X)) := rfl

/-- The comparison `Stacks.DerivedIndexing.rightDerivedPlusEdge` built from the composition
isomorphism `R(Q ∘ P) ≅ RQ ∘ RP`, read through the identification
`Stacks.DerivedIndexing.rightDerivedPlusIsoRes` of `R ⁱF` with the homology of `F` applied to
the chosen extended injective resolution, is the degree-`i` homology of `Q` applied to the
comparison of the chosen extended injective resolutions. -/
theorem rightDerivedPlusEdge_comp_rightDerivedPlusIsoRes (i : ℤ) (X : C) :
    (rightDerivedPlusEdge P Q i).app X ≫ (rightDerivedPlusIsoRes (P ⋙ Q) i).hom.app X =
      (rightDerivedPlusIsoRes Q i).hom.app (P.obj X) ≫
        (HomotopyCategory.homologyFunctor E (ComplexShape.up ℤ) i).map
          ((Q.mapHomotopyCategory (ComplexShape.up ℤ)).map
            ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
              (extendResolutionComparison P X))) := by
  have hψ : (HomotopyCategory.Plus.ι E).map
        (Q.mapHomotopyCategoryPlus.map (extendResolutionComparisonPlus P X)) =
      (Q.mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
          (extendResolutionComparison P X)) :=
    (ι_map_mapHomotopyCategoryPlus_map Q _).trans
      (congrArg (Q.mapHomotopyCategory (ComplexShape.up ℤ)).map
        (ι_map_extendResolutionComparisonPlus P X))
  rw [rightDerivedPlusEdge_app, rightDerivedPlusIsoRes_hom_app, rightDerivedPlusIsoRes_hom_app]
  exact paste_tail _ _ _ _ _ _ _
    ((DerivedCategory.Plus.homologyFunctor E i).map
      (DerivedCategory.Plus.Qh.map
        (Q.mapHomotopyCategoryPlus.map (extendResolutionComparisonPlus P X)))) _ _
    (map_comp_four (DerivedCategory.Plus.homologyFunctor E i) _ _ _ _ _ _ _
      (map_rightDerivedPlusUnitSingle_app_comp_rightDerivedPlusCompIso_inv_app P Q X))
    (((plusHomologyIso (D := E) i).hom.naturality
        (Q.mapHomotopyCategoryPlus.map (extendResolutionComparisonPlus P X))).trans
      (congrArg (fun z => (plusHomologyIso (D := E) i).hom.app
          (Q.mapHomotopyCategoryPlus.obj (resPlus.obj (P.obj X))) ≫ z)
        (congrArg (HomotopyCategory.homologyFunctor E (ComplexShape.up ℤ) i).map hψ)))

/-- For additive `P : 𝒜 ⥤ ℬ` and `Q : ℬ ⥤ 𝒞` with `𝒜` and `ℬ` having enough injectives and `P`
preserving injective objects, the `ℕ`-indexed edge morphism
`Stacks.Cohomology.RightDerivedEdge.edge P Q i : R ⁱQ(Pℱ) ⟶ R ⁱ(Q ∘ P)(ℱ)` corresponds, under
the comparison `Stacks.DerivedIndexing.rightDerivedIso` of the two indexings of the right
derived functors, to `Stacks.DerivedIndexing.rightDerivedPlusEdge P Q i`, the degree-`i`
homology of the canonical map `(Pℱ)[0] ⟶ RP(ℱ[0])` transported along the composition
isomorphism of [Stacks, Tag 015M]. -/
theorem edge_comp_rightDerivedIso (i : ℕ) (X : C) :
    (Stacks.Cohomology.RightDerivedEdge.edge P Q i).app X ≫
        (rightDerivedIso (P ⋙ Q) i).hom.app X =
      (rightDerivedIso Q i).hom.app (P.obj X) ≫ (rightDerivedPlusEdge P Q (i : ℤ)).app X :=
  pasteSquares _ _ _ _ _ _ _ (edge_comp_rightDerivedIsoRes P Q i X)
    (inv_comm_of_comm ((rightDerivedPlusIsoRes Q (i : ℤ)).app (P.obj X))
      ((rightDerivedPlusIsoRes (P ⋙ Q) (i : ℤ)).app X)
      ((rightDerivedPlusEdge P Q (i : ℤ)).app X) _
      (rightDerivedPlusEdge_comp_rightDerivedPlusIsoRes P Q (i : ℤ) X))

/-- For a morphism `u : 𝒢 ⟶ Pℱ`, the map induced by `u` on `R ⁱQ` followed by the edge morphism
`Stacks.Cohomology.RightDerivedEdge.edge` corresponds, under
`Stacks.DerivedIndexing.rightDerivedIso`, to the map induced by `u` on
`CategoryTheory.Functor.rightDerivedPlus` followed by the degreewise comparison
`Stacks.DerivedIndexing.rightDerivedPlusEdge`. -/
theorem map_comp_edge_comp_rightDerivedIso (i : ℕ) {X : C} {Y : D} (u : Y ⟶ P.obj X) :
    (Q.rightDerived i).map u ≫ (Stacks.Cohomology.RightDerivedEdge.edge P Q i).app X ≫
        (rightDerivedIso (P ⋙ Q) i).hom.app X =
      (rightDerivedIso Q i).hom.app Y ≫ (Q.rightDerivedPlus (i : ℤ)).map u ≫
        (rightDerivedPlusEdge P Q (i : ℤ)).app X := by
  rw [edge_comp_rightDerivedIso P Q i X, ← Category.assoc,
    (rightDerivedIso Q i).hom.naturality u, Category.assoc]

end EdgeIdentification

end Stacks.DerivedIndexing

end
