module

public import StacksFrontier.AlgebraicGeometry.DeRham.ExteriorGradedPiece
public import StacksFrontier.Algebra.Homology.SpectralSequence.SpectralObjectConvergence
public import StacksCore.CategoryTheory.Abelian.CommSq
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AbelianOfSmallSite
public import StacksFrontier.Algebra.Homology.DerivedCategory.Filtered.DerivedFunctor
public import StacksFrontier.AlgebraicGeometry.DeRham.WedgeFiltrationDegreewise

/-!
# A graded piece is the image of its numerator in the quotient by its denominator

For a composable pair `i : B ⟶ A`, `j : A ⟶ Z` in an abelian category with `j` a monomorphism,

`A/B  ≅  Im(A ⟶ Z/B)`,

compatibly with the two maps into `Z/B`. Applied to the wedge filtration, this identifies the
graded piece `SheafOfModules.exteriorGraded`, defined as the image of `F^k⋀ⁿH` in
`⋀ⁿH/F^{k+1}⋀ⁿH`, with the cokernel of the inclusion `F^{k+1}⋀ⁿH ⟶ F^k⋀ⁿH`.

## Main definitions

* `Stacks.GradedPieceImage.cokernelIsoImageInQuotient`: the isomorphism `A/B ≅ Im(A ⟶ Z/B)`.
* `Stacks.GradedPieceImage.cokernelOfLEFunctorMapIso`: for an exact functor `U` and subobjects
  `W ≤ N`, the isomorphism `U(N)/U(W) ≅ U(N/W)`.
* `SheafOfModules.cokernelOfLEIsoExteriorGraded`: the isomorphism between the cokernel of the
  inclusion `F^{k+1}⋀ⁿH ⟶ F^k⋀ⁿH` and `gr^k⋀ⁿH`.

## Main results

* `Stacks.GradedPieceImage.imageSubobject_comp_cokernelπ`: `Im(A ⟶ Z/B)` is `A/B`, as
  subobjects of `Z/B`.
* `Stacks.GradedPieceImage.cokernelIsoImageInQuotient_hom_comp_arrow` and
  `Stacks.GradedPieceImage.π_cokernelIsoImageInQuotient_hom_comp_arrow`: the isomorphism
  `A/B ≅ Im(A ⟶ Z/B)` is compatible with the maps into `Z/B` and with the projections out of `A`.
* `Stacks.GradedPieceImage.π_cokernelOfLEFunctorMapIso_hom`: the isomorphism
  `U(N)/U(W) ≅ U(N/W)` carries the projection to the image of the projection.

## References

* [Stacks Project, Tag 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
* [Stacks Project, Tag 0129](https://stacks.math.columbia.edu/tag/0129)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf

universe v u

namespace Stacks.GradedPieceImage

variable {C : Type u} [Category.{v} C] [Abelian C] {B A Z : C}

/-- `A/B` is the image of `A` in `Z/B`, as subobjects of `Z/B`, for `i : B ⟶ A` and a
monomorphism `j : A ⟶ Z`. -/
theorem imageSubobject_comp_cokernelπ (i : B ⟶ A) (j : A ⟶ Z) [Mono j] :
    imageSubobject (j ≫ cokernel.π (i ≫ j)) =
      Subobject.mk (cokernel.map i (i ≫ j) (𝟙 B) j (by simp)) := by
  have hq : cokernel.π i ≫ cokernel.map i (i ≫ j) (𝟙 B) j (by simp) =
      j ≫ cokernel.π (i ≫ j) := cokernel.π_desc _ _ _
  refine Eq.trans (CategoryTheory.Abelian.SpectralObject.imageSubobject_congr hq.symm) ?_
  refine Eq.trans (Stacks.CategoryTheory.Subobject.imageSubobject_epi_comp (cokernel.π i)
    inferInstance _) ?_
  exact imageSubobject_mono _

/-- The isomorphism `A/B ≅ Im(A ⟶ Z/B)` between the quotient of `A` by `B` and the image of `A`
in the quotient of `Z` by `B`. -/
def cokernelIsoImageInQuotient (i : B ⟶ A) (j : A ⟶ Z) [Mono j] :
    cokernel i ≅ (imageSubobject (j ≫ cokernel.π (i ≫ j)) : C) :=
  Subobject.isoOfMkEq (cokernel.map i (i ≫ j) (𝟙 B) j (by simp)) _
    (imageSubobject_comp_cokernelπ i j).symm

/-- The isomorphism `A/B ≅ Im(A ⟶ Z/B)` followed by the inclusion of the image is the morphism
`A/B ⟶ Z/B` induced by `j : A ⟶ Z`. -/
@[reassoc]
theorem cokernelIsoImageInQuotient_hom_comp_arrow (i : B ⟶ A) (j : A ⟶ Z) [Mono j] :
    (cokernelIsoImageInQuotient i j).hom ≫
        (imageSubobject (j ≫ cokernel.π (i ≫ j))).arrow =
      cokernel.map i (i ≫ j) (𝟙 B) j (by simp) := by
  simp [cokernelIsoImageInQuotient]

/-- The isomorphism `A/B ≅ Im(A ⟶ Z/B)` carries the projection `A ⟶ A/B` to `A ⟶ Z/B`: read
inside `Z/B`, the composite of the projection with the isomorphism is the map `A ⟶ Z/B`. -/
@[reassoc]
theorem π_cokernelIsoImageInQuotient_hom_comp_arrow (i : B ⟶ A) (j : A ⟶ Z) [Mono j] :
    cokernel.π i ≫ (cokernelIsoImageInQuotient i j).hom ≫
        (imageSubobject (j ≫ cokernel.π (i ≫ j))).arrow =
      j ≫ cokernel.π (i ≫ j) := by
  rw [cokernelIsoImageInQuotient_hom_comp_arrow]
  exact cokernel.π_desc _ _ _

/-- The isomorphism `A/B ≅ Im(A ⟶ Z/ψ)` for a morphism `ψ : B ⟶ Z` equal to `i ≫ j`. -/
def cokernelIsoImageInQuotient' (i : B ⟶ A) (j : A ⟶ Z) [Mono j] (ψ : B ⟶ Z)
    (hij : i ≫ j = ψ) : cokernel i ≅ (imageSubobject (j ≫ cokernel.π ψ) : C) := by
  subst hij
  exact cokernelIsoImageInQuotient i j

/-- `Stacks.GradedPieceImage.π_cokernelIsoImageInQuotient_hom_comp_arrow` with the composite
`B ⟶ Z` named by a hypothesis. -/
@[reassoc]
theorem π_cokernelIsoImageInQuotient_hom_comp_arrow' (i : B ⟶ A) (j : A ⟶ Z) [Mono j]
    (ψ : B ⟶ Z) (hij : i ≫ j = ψ) :
    cokernel.π i ≫ (cokernelIsoImageInQuotient' i j ψ hij).hom ≫
        (imageSubobject (j ≫ cokernel.π ψ)).arrow =
      j ≫ cokernel.π ψ := by
  subst hij
  exact π_cokernelIsoImageInQuotient_hom_comp_arrow i j

/-- The isomorphism `A/B ≅ Q`, where `Q` is a subobject of `Z/ψ` equal to the image of `A`, for
a denominator `ψ : B' ⟶ Z` equal to `(e ≫ i) ≫ j` with `e : B' ⟶ B` an epimorphism. -/
def cokernelEpiCompIsoImageInQuotient {B' : C} (e : B' ⟶ B) [Epi e] (i : B ⟶ A) (j : A ⟶ Z)
    [Mono j] (ψ : B' ⟶ Z) (hij : (e ≫ i) ≫ j = ψ) (Q : Subobject (cokernel ψ))
    (hQ : imageSubobject (j ≫ cokernel.π ψ) = Q) : cokernel i ≅ (Q : C) :=
  (cokernelEpiComp e i).symm ≪≫ cokernelIsoImageInQuotient' (e ≫ i) j ψ hij ≪≫
    Subobject.isoOfEq _ Q hQ

/-- The isomorphism `Stacks.GradedPieceImage.cokernelEpiCompIsoImageInQuotient` carries the
projection `A ⟶ A/B` to `A ⟶ Z/ψ`: read inside `Z/ψ`, the composite of the projection with the
isomorphism and the inclusion of `Q` is the map `A ⟶ Z/ψ`. -/
@[reassoc]
theorem π_cokernelEpiCompIsoImageInQuotient_hom_comp_arrow {B' : C} (e : B' ⟶ B) [Epi e]
    (i : B ⟶ A) (j : A ⟶ Z) [Mono j] (ψ : B' ⟶ Z) (hij : (e ≫ i) ≫ j = ψ)
    (Q : Subobject (cokernel ψ)) (hQ : imageSubobject (j ≫ cokernel.π ψ) = Q) :
    cokernel.π i ≫ (cokernelEpiCompIsoImageInQuotient e i j ψ hij Q hQ).hom ≫ Q.arrow =
      j ≫ cokernel.π ψ := by
  rw [cokernelEpiCompIsoImageInQuotient]
  simp only [Iso.trans_hom, Iso.symm_hom, Subobject.isoOfEq_hom, cokernelEpiComp_inv,
    Category.assoc, Subobject.ofLE_arrow, cokernel.π_desc_assoc]
  exact π_cokernelIsoImageInQuotient_hom_comp_arrow' _ _ _ _

omit [Abelian C] in
/-- A functor preserving monomorphisms carries an inclusion of subobjects to an inclusion of
the subobjects presented by their images. -/
theorem mk_map_arrow_le {D : Type*} [Category* D] (U : C ⥤ D)
    [U.PreservesMonomorphisms] (P Q : Subobject Z) (h : P ≤ Q) :
    Subobject.mk (U.map P.arrow) ≤ Subobject.mk (U.map Q.arrow) :=
  Subobject.mk_le_mk_of_comm (U.map (Subobject.ofLE P Q h))
    (by rw [← U.map_comp, Subobject.ofLE_arrow])

/-- An exact functor commutes with the quotient of one subobject by a smaller one:
`U(N)/U(W) ≅ U(N/W)` for `W ≤ N`. -/
def cokernelOfLEFunctorMapIso {D : Type*} [Category* D] [Abelian D] (U : C ⥤ D) [U.Additive]
    [PreservesFiniteColimits U] [U.PreservesMonomorphisms] (P Q : Subobject Z) (h : P ≤ Q) :
    cokernel (Subobject.ofLE _ _ (mk_map_arrow_le U P Q h)) ≅
      U.obj (cokernel (Subobject.ofLE P Q h)) :=
  cokernel.mapIso _ (U.map (Subobject.ofLE P Q h))
      (Subobject.underlyingIso (U.map P.arrow)) (Subobject.underlyingIso (U.map Q.arrow))
      (by
        rw [← cancel_mono (U.map Q.arrow), Category.assoc, Category.assoc,
          Subobject.underlyingIso_hom_comp_eq_mk, Subobject.ofLE_arrow, ← U.map_comp,
          Subobject.ofLE_arrow, Subobject.underlyingIso_hom_comp_eq_mk]) ≪≫
    (PreservesCokernel.iso U (Subobject.ofLE P Q h)).symm

/-- The isomorphism `U(N)/U(W) ≅ U(N/W)` carries the projection to the image of the projection,
up to the identification of `U(N)` with the subobject it presents. -/
@[reassoc]
theorem π_cokernelOfLEFunctorMapIso_hom {D : Type*} [Category* D] [Abelian D] (U : C ⥤ D)
    [U.Additive] [PreservesFiniteColimits U] [U.PreservesMonomorphisms] (P Q : Subobject Z)
    (h : P ≤ Q) :
    cokernel.π (Subobject.ofLE _ _ (mk_map_arrow_le U P Q h)) ≫
        (cokernelOfLEFunctorMapIso U P Q h).hom =
      (Subobject.underlyingIso (U.map Q.arrow)).hom ≫
        U.map (cokernel.π (Subobject.ofLE P Q h)) := by
  have h1 : cokernel.π (U.map (Subobject.ofLE P Q h)) ≫
      (PreservesCokernel.iso U (Subobject.ofLE P Q h)).inv =
      U.map (cokernel.π (Subobject.ofLE P Q h)) :=
    (Iso.comp_inv_eq _).2 (PreservesCokernel.π_iso_hom U _).symm
  rw [cokernelOfLEFunctorMapIso, Iso.trans_hom, Iso.symm_hom, cokernel.mapIso_hom,
    ← Category.assoc, cokernel.π_desc, Category.assoc, h1]

end Stacks.GradedPieceImage

namespace SheafOfModules

open MonoidalCategory TopologicalSpace

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {F H : SheafOfModules.{u} (Sheaf.toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  (AF : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) F)
  (A : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) H)

attribute [local instance] Stacks.SheafOfModules.abelianOfSmallSite

/-- `gr^k⋀ⁿH` is the cokernel of the inclusion `F^{k+1}⋀ⁿH ⟶ F^k⋀ⁿH`, `n = k + 1 + m`: the
graded piece `SheafOfModules.exteriorGraded`, defined as the image of `F^k⋀ⁿH` in
`⋀ⁿH/F^{k+1}⋀ⁿH`, read as a quotient of subobjects. -/
def cokernelOfLEIsoExteriorGraded (iF : F ⟶ H) (k m : ℕ) :
    cokernel (Subobject.ofLE _ _ (imageSubobject_prodWedgeHom_succ_le AF A iF k m)) ≅
      exteriorGraded AF A iF k m :=
  haveI : Epi (factorThruImageSubobject (prodWedgeHom AF A A iF (𝟙 H) (k + 1) m)) :=
    Stacks.CategoryTheory.Subobject.epi_factorThruImageSubobject _
  Stacks.GradedPieceImage.cokernelEpiCompIsoImageInQuotient
    (factorThruImageSubobject (prodWedgeHom AF A A iF (𝟙 H) (k + 1) m))
    (Subobject.ofLE _ _ (imageSubobject_prodWedgeHom_succ_le AF A iF k m))
    (imageSubobject (prodWedgeHom AF A A iF (𝟙 H) k (1 + m) ≫
      eqToHom (congrArg A.exterior.piece (add_assoc (k : ℤ) (1 : ℤ) (m : ℤ)).symm))).arrow
    (prodWedgeHom AF A A iF (𝟙 H) (k + 1) m)
    (by rw [Category.assoc, Subobject.ofLE_arrow, imageSubobject_arrow_comp])
    _ (imageSubobject_exteriorGradedHom_eq AF A iF k m).symm

end SheafOfModules

end
