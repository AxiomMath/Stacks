module

public import StacksFrontier.AlgebraicGeometry.Modules.ProdWedgeOpenSubspace
public import StacksFrontier.AlgebraicGeometry.DeRham.ExteriorGradedPiece

/-!
# The comparison onto the graded piece of the wedge filtration crosses restriction to an open

Let `X` be a ringed space, `U ⊆ X` open, `0 ⟶ T.X₁ ⟶ T.X₂ ⟶ T.X₃ ⟶ 0` a short exact sequence of
sheaves of `𝒪_X`-modules and `AF₁`, `AG₃`, `A₂` bundles of tensor, exterior and symmetric
algebras of its three terms. `StacksFrontier.AlgebraicGeometry.DeRham.ExteriorGradedPiece` builds,
for a total degree `n = k + 1 + m`,

* `SheafOfModules.exteriorGradedHom`, the canonical morphism
  `⋀^kT.X₁ ⊗ ⋀^{1+m}T.X₂ ⟶ ⋀ⁿT.X₂/F^{k+1}⋀ⁿT.X₂`, and
* `SheafOfModules.exteriorGradedQuotientHom`, the splitting-free comparison
  `⋀^kT.X₁ ⊗ ⋀^{m+1}T.X₃ ⟶ ⋀ⁿT.X₂/F^{k+1}⋀ⁿT.X₂`, which is the descent of the first along the
  presentation of [Stacks, Tag 01CJ] tensored with `⋀^kT.X₁`.

**This file carries both across restriction to `U`.** The first, read through
`(M ⊗ L)|_U ≅ M|_U ⊗ L|_U` at its source, is the tensor product of the restricted maps on
exterior powers followed by the multiplication of the restricted exterior algebra and the
restrictions of the transport and of the cokernel projection. The second is characterized by its
defining equation (`SheafOfModules.tensorLeftFunctor_map_extHom_comp_exteriorGradedQuotientHom`),
and its restriction satisfies the restriction of that equation, read through
`(M ⊗ L)|_U ≅ M|_U ⊗ L|_U` at each source; the epimorphism the equation is precomposed with stays
an epimorphism after restriction and tensoring, so the restricted equation determines the
restricted comparison.

## Main results

* `SheafOfModules.openSubspaceTensorBifunctorIso_inv_comp_map_exteriorGradedHom`: **the canonical
  morphism onto `⋀ⁿT.X₂/F^{k+1}⋀ⁿT.X₂`, restricted to `U`**, is the tensor product of the two
  restricted functorial maps on exterior powers, the multiplication of the restricted exterior
  algebra, and then the restrictions of the transport and of the cokernel projection.
* `SheafOfModules.openSubspaceTensorBifunctorIso_inv_comp_map_exteriorGradedQuotientHom`: **the
  restricted defining equation of the splitting-free comparison**, both of whose legs are read
  through `(M ⊗ L)|_U ≅ M|_U ⊗ L|_U` at the common source `(⋀^kT.X₁ ⊗ ⋀^{m+1}T.X₂)|_U`.
* `SheafOfModules.openSubspaceTensorBifunctorIso_inv_comp_map_exteriorGradedHom_comp_cokernelIso`
  and its `…_exteriorGradedQuotientHom_comp_cokernelIso` counterpart:
  **the same two statements with the target read on `U` as well**, through the comparison
  `(⋀ⁿT.X₂/F^{k+1}⋀ⁿT.X₂)|_U ≅ coker((⋀^{k+1}T.X₁ ⊗ ⋀^mT.X₂)|_U ⟶ (⋀ⁿT.X₂)|_U)` that restriction's
  preservation of finite colimits provides. Nothing of either statement then lives on `X` except
  the restricted exterior algebra.
* `SheafOfModules.openSubspaceExteriorGradedIso`, with
  `…_hom_arrow` and `SheafOfModules.map_toExteriorGraded_comp_openSubspaceExteriorGradedIso_hom`:
  **the restricted graded piece `gr^k⋀ⁿT.X₂` is the graded piece of the restricted morphism**,
  compatibly with the inclusions into the ambient quotient and with the canonical morphisms onto
  the pieces.
* `SheafOfModules.epi_tensorSheafBifunctorMap_openSubspaceRestriction_relComplex` and
  `SheafOfModules.eq_of_tensorSheafBifunctorMap_openSubspaceRestriction_relComplex_comp`:
  **the morphism the restricted defining equation is precomposed with is an epimorphism**, and so
  **the equation determines the restricted comparison.**

## References

* [Stacks Project, Tag 01CJ](https://stacks.math.columbia.edu/tag/01CJ)
* [Stacks Project, Section 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf CategoryTheory.Limits AlgebraicGeometry Opposite
  PresheafOfModules TopologicalSpace
open Stacks.Cohomology.HigherDirectImage (restrictToOpen)

universe u

namespace Stacks.CategoryTheory

/-- **A bifunctor applied to a morphism in its second variable is the uncurried bifunctor applied
to the identity paired with that morphism.** -/
theorem obj_map_eq_uncurry_map_id {C₁ D₁ E₁ : Type*} [_root_.CategoryTheory.Category C₁]
    [_root_.CategoryTheory.Category D₁] [_root_.CategoryTheory.Category E₁]
    (T : C₁ ⥤ D₁ ⥤ E₁) (X : C₁) {P Q : D₁} (h : P ⟶ Q) :
    (T.obj X).map h = (Functor.uncurry.obj T).map ((𝟙 X, h) : (X, P) ⟶ (X, Q)) := by
  simp

end Stacks.CategoryTheory

namespace SheafOfModules

/-- Reassociation of a threefold composite under postcomposition. -/
private theorem compAssocThree {C : Type*} [Category C] {A₀ A₁ A₂ A₃ A₄ : C} (a : A₀ ⟶ A₁)
    (b : A₁ ⟶ A₂) (c : A₂ ⟶ A₃) (i : A₃ ⟶ A₄) :
    (a ≫ b ≫ c) ≫ i = a ≫ b ≫ c ≫ i :=
  Eq.trans (Category.assoc a (b ≫ c) i)
    (congrArg (fun z => a ≫ z) (Category.assoc b c i))

/-- Reassociation of a fourfold composite under postcomposition. -/
private theorem compAssocFour {C : Type*} [Category C] {A₀ A₁ A₂ A₃ A₄ A₅ : C} (a : A₀ ⟶ A₁)
    (b : A₁ ⟶ A₂) (c : A₂ ⟶ A₃) (d : A₃ ⟶ A₄) (i : A₄ ⟶ A₅) :
    (a ≫ b ≫ c ≫ d) ≫ i = a ≫ b ≫ c ≫ d ≫ i :=
  Eq.trans (Category.assoc a (b ≫ c ≫ d) i)
    (congrArg (fun z => a ≫ z)
      (Eq.trans (Category.assoc b (c ≫ d) i)
        (congrArg (fun z => b ≫ z) (Category.assoc c d i))))

section GradedHom

variable {X : RingedSpace.{u, u}} (U : Opens X.carrier)
  {F H : SheafOfModules.{u} (structureSheafRing X)}
  (AF : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology X.carrier) F)
  (A : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology X.carrier) H)
  (iF : F ⟶ H) (k m : ℕ)

/-- `SheafOfModules.exteriorGradedHom` unfolded: the wedge-product morphism onto `⋀ⁿH`, the
transport of the total degree from `k + (1 + m)` to `k + 1 + m`, and the projection onto the
quotient by the `(k+1)`-st step of the wedge filtration. -/
private theorem exteriorGradedHomUnfold :
    exteriorGradedHom AF A iF k m =
      prodWedgeHom AF A A iF (𝟙 H) k (1 + m) ≫
        (eqToHom (congrArg A.exterior.piece (add_assoc (k : ℤ) (1 : ℤ) (m : ℤ)).symm) ≫
          cokernel.π (prodWedgeHom AF A A iF (𝟙 H) (k + 1) m)) :=
  rfl

/-- **The canonical morphism `⋀^kF ⊗ ⋀^{1+m}H ⟶ ⋀ⁿH/F^{k+1}⋀ⁿH` crosses restriction to an open
subspace.** Read through the identification `(M ⊗ L)|_U ≅ M|_U ⊗ L|_U` at the source, the
restriction of `SheafOfModules.exteriorGradedHom` is the tensor product of the restrictions of
the two functorial maps on exterior powers, the multiplication of the restricted exterior algebra
of `H`, and then the restrictions of the transport of the total degree and of the cokernel
projection. -/
theorem openSubspaceTensorBifunctorIso_inv_comp_map_exteriorGradedHom :
    (openSubspaceTensorBifunctorIso U (AF.exteriorPower k) (A.exteriorPower (1 + m))).inv ≫
        (openSubspaceRestriction U).map (exteriorGradedHom AF A iF k m) =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          (restrictToOpen X U).sheaf)).map
          (((openSubspaceRestriction U).map
              (AF.exterior_isExteriorAlgebra.pieceMap A.exterior_isExteriorAlgebra iF (k : ℤ)),
            (openSubspaceRestriction U).map
              (A.exterior_isExteriorAlgebra.pieceMap A.exterior_isExteriorAlgebra (𝟙 H)
                ((1 + m : ℕ) : ℤ))) :
            ((openSubspaceRestriction U).obj (AF.exteriorPower k),
                (openSubspaceRestriction U).obj (A.exteriorPower (1 + m))) ⟶
              ((openSubspaceRestriction U).obj (A.exteriorPower k),
                (openSubspaceRestriction U).obj (A.exteriorPower (1 + m)))) ≫
        GradedAlgebra.mulSheaf (Osharp := (restrictToOpen X U).sheaf)
            (openSubspaceAlg A.exterior U) (k : ℤ) ((1 + m : ℕ) : ℤ) ≫
          (openSubspaceRestriction U).map
              (eqToHom (congrArg A.exterior.piece (add_assoc (k : ℤ) (1 : ℤ) (m : ℤ)).symm)) ≫
            (openSubspaceRestriction U).map
              (cokernel.π (prodWedgeHom AF A A iF (𝟙 H) (k + 1) m)) :=
  Eq.trans
    (congrArg (fun z => (openSubspaceTensorBifunctorIso U (AF.exteriorPower k)
        (A.exteriorPower (1 + m))).inv ≫ (openSubspaceRestriction U).map z)
      (exteriorGradedHomUnfold AF A iF k m))
    (Eq.trans
      (congrArg (fun z => (openSubspaceTensorBifunctorIso U (AF.exteriorPower k)
          (A.exteriorPower (1 + m))).inv ≫ z)
        (Eq.trans
          ((openSubspaceRestriction U).map_comp (prodWedgeHom AF A A iF (𝟙 H) k (1 + m))
            (eqToHom (congrArg A.exterior.piece (add_assoc (k : ℤ) (1 : ℤ) (m : ℤ)).symm) ≫
              cokernel.π (prodWedgeHom AF A A iF (𝟙 H) (k + 1) m)))
          (congrArg (fun z => (openSubspaceRestriction U).map
              (prodWedgeHom AF A A iF (𝟙 H) k (1 + m)) ≫ z)
            ((openSubspaceRestriction U).map_comp
              (eqToHom (congrArg A.exterior.piece (add_assoc (k : ℤ) (1 : ℤ) (m : ℤ)).symm))
              (cokernel.π (prodWedgeHom AF A A iF (𝟙 H) (k + 1) m))))))
      (Eq.trans (Category.assoc _ _ _).symm
        (Eq.trans
          (congrArg (fun z => z ≫ (openSubspaceRestriction U).map
                (eqToHom (congrArg A.exterior.piece (add_assoc (k : ℤ) (1 : ℤ) (m : ℤ)).symm)) ≫
              (openSubspaceRestriction U).map
                (cokernel.π (prodWedgeHom AF A A iF (𝟙 H) (k + 1) m)))
            (openSubspaceTensorBifunctorIso_inv_comp_map_prodWedgeHom U AF A A iF (𝟙 H) k
              (1 + m)))
          (Category.assoc _ _ _))))


/-- **The canonical morphism `⋀^kF ⊗ ⋀^{1+m}H ⟶ ⋀ⁿH/F^{k+1}⋀ⁿH` crosses restriction with its
target read on `U` too.** Postcomposed with the comparison
`CategoryTheory.Limits.PreservesCokernel.iso` of the restricted cokernel with the cokernel formed
on `U`, the restriction of `SheafOfModules.exteriorGradedHom` ends with the projection of the
cokernel formed on `U`, and nothing but the restricted exterior algebra of `H` is left over `X`. -/
theorem openSubspaceTensorBifunctorIso_inv_comp_map_exteriorGradedHom_comp_cokernelIso :
    (openSubspaceTensorBifunctorIso U (AF.exteriorPower k) (A.exteriorPower (1 + m))).inv ≫
        (openSubspaceRestriction U).map (exteriorGradedHom AF A iF k m) ≫
          (PreservesCokernel.iso (openSubspaceRestriction U)
            (prodWedgeHom AF A A iF (𝟙 H) (k + 1) m)).hom =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          (restrictToOpen X U).sheaf)).map
          (((openSubspaceRestriction U).map
              (AF.exterior_isExteriorAlgebra.pieceMap A.exterior_isExteriorAlgebra iF (k : ℤ)),
            (openSubspaceRestriction U).map
              (A.exterior_isExteriorAlgebra.pieceMap A.exterior_isExteriorAlgebra (𝟙 H)
                ((1 + m : ℕ) : ℤ))) :
            ((openSubspaceRestriction U).obj (AF.exteriorPower k),
                (openSubspaceRestriction U).obj (A.exteriorPower (1 + m))) ⟶
              ((openSubspaceRestriction U).obj (A.exteriorPower k),
                (openSubspaceRestriction U).obj (A.exteriorPower (1 + m)))) ≫
        GradedAlgebra.mulSheaf (Osharp := (restrictToOpen X U).sheaf)
            (openSubspaceAlg A.exterior U) (k : ℤ) ((1 + m : ℕ) : ℤ) ≫
          (openSubspaceRestriction U).map
              (eqToHom (congrArg A.exterior.piece (add_assoc (k : ℤ) (1 : ℤ) (m : ℤ)).symm)) ≫
            cokernel.π ((openSubspaceRestriction U).map
              (prodWedgeHom AF A A iF (𝟙 H) (k + 1) m)) :=
  Eq.trans
    (Category.assoc
      (openSubspaceTensorBifunctorIso U (AF.exteriorPower k) (A.exteriorPower (1 + m))).inv
      ((openSubspaceRestriction U).map (exteriorGradedHom AF A iF k m))
      (PreservesCokernel.iso (openSubspaceRestriction U)
        (prodWedgeHom AF A A iF (𝟙 H) (k + 1) m)).hom).symm
    (Eq.trans
      (congrArg
        (fun z => z ≫ (PreservesCokernel.iso (openSubspaceRestriction U)
          (prodWedgeHom AF A A iF (𝟙 H) (k + 1) m)).hom)
        (openSubspaceTensorBifunctorIso_inv_comp_map_exteriorGradedHom U AF A iF k m))
      (Eq.trans
        (compAssocFour _ _ _ _ _)
        (congrArg
          (fun z => (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              (restrictToOpen X U).sheaf)).map
              (((openSubspaceRestriction U).map
                  (AF.exterior_isExteriorAlgebra.pieceMap A.exterior_isExteriorAlgebra iF
                    (k : ℤ)),
                (openSubspaceRestriction U).map
                  (A.exterior_isExteriorAlgebra.pieceMap A.exterior_isExteriorAlgebra (𝟙 H)
                    ((1 + m : ℕ) : ℤ))) :
                ((openSubspaceRestriction U).obj (AF.exteriorPower k),
                    (openSubspaceRestriction U).obj (A.exteriorPower (1 + m))) ⟶
                  ((openSubspaceRestriction U).obj (A.exteriorPower k),
                    (openSubspaceRestriction U).obj (A.exteriorPower (1 + m)))) ≫
            GradedAlgebra.mulSheaf (Osharp := (restrictToOpen X U).sheaf)
                (openSubspaceAlg A.exterior U) (k : ℤ) ((1 + m : ℕ) : ℤ) ≫
              (openSubspaceRestriction U).map
                  (eqToHom (congrArg A.exterior.piece
                    (add_assoc (k : ℤ) (1 : ℤ) (m : ℤ)).symm)) ≫ z)
          (PreservesCokernel.π_iso_hom (openSubspaceRestriction U)
            (prodWedgeHom AF A A iF (𝟙 H) (k + 1) m)))))

/-- **The restricted graded piece `gr^k⋀ⁿH` is the graded piece of the restricted morphism**:
the restriction of the image of `SheafOfModules.exteriorGradedHom` is the image of the
restriction of `SheafOfModules.exteriorGradedHom`. -/
def openSubspaceExteriorGradedIso :
    (openSubspaceRestriction U).obj (exteriorGraded AF A iF k m) ≅
      (imageSubobject ((openSubspaceRestriction U).map (exteriorGradedHom AF A iF k m)) :
        SheafOfModules.{u} _) :=
  mapImageSubobjectIso (openSubspaceRestriction U) (exteriorGradedHom AF A iF k m)

/-- **The identification of the graded pieces is compatible with their inclusions into the
ambient quotient**: followed by the inclusion of the image of the restricted morphism, it is the
restriction of the inclusion of the graded piece. -/
theorem openSubspaceExteriorGradedIso_hom_arrow :
    (openSubspaceExteriorGradedIso U AF A iF k m).hom ≫
        (imageSubobject ((openSubspaceRestriction U).map
          (exteriorGradedHom AF A iF k m))).arrow =
      (openSubspaceRestriction U).map (imageSubobject (exteriorGradedHom AF A iF k m)).arrow :=
  mapImageSubobjectIso_hom_arrow (openSubspaceRestriction U) (exteriorGradedHom AF A iF k m)

/-- **The identification of the graded pieces is compatible with the canonical morphisms onto
them**: the restriction of `SheafOfModules.toExteriorGraded`, followed by the identification, is
the factorization of the restricted morphism through its image. -/
theorem map_toExteriorGraded_comp_openSubspaceExteriorGradedIso_hom :
    (openSubspaceRestriction U).map (toExteriorGraded AF A iF k m) ≫
        (openSubspaceExteriorGradedIso U AF A iF k m).hom =
      factorThruImageSubobject ((openSubspaceRestriction U).map
        (exteriorGradedHom AF A iF k m)) :=
  map_factorThruImageSubobject_comp_mapImageSubobjectIso_hom (openSubspaceRestriction U)
    (exteriorGradedHom AF A iF k m)

end GradedHom

section GradedQuotientHom

variable {X : RingedSpace.{u, u}} (U : Opens X.carrier)
  {T : ShortComplex (SheafOfModules.{u} (structureSheafRing X))}
  (AF₁ : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology X.carrier) T.X₁)
  (AG₃ : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology X.carrier) T.X₃)
  (A₂ : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology X.carrier) T.X₂)

/-- Tensoring on the left with `⋀^rT.X₁`, as it acts on a morphism: the tensor product of the
identity of `⋀^rT.X₁` with that morphism, in the bifunctor spelling
`SheafOfModules.openSubspaceTensorBifunctorIso_naturality` is stated at. -/
private theorem tensorLeftFunctorMapUnfold (r : ℕ)
    {P Q : SheafOfModules.{u} (structureSheafRing X)} (h : P ⟶ Q) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj (AF₁.exteriorPower r)).map h =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf)).map
        ((𝟙 (AF₁.exteriorPower r), h) :
          (AF₁.exteriorPower r, P) ⟶ (AF₁.exteriorPower r, Q)) :=
  Stacks.CategoryTheory.obj_map_eq_uncurry_map_id _ _ _

/-- **The defining equation of the splitting-free comparison `⋀^kT.X₁ ⊗ ⋀^{m+1}T.X₃ ⟶
⋀ⁿT.X₂/F^{k+1}⋀ⁿT.X₂`, restricted to an open subspace.** Both legs are read through the
identification `(M ⊗ L)|_U ≅ M|_U ⊗ L|_U` at their source, so that each is a morphism out of
`(⋀^kT.X₁)|_U ⊗ (⋀^{m+1}T.X₂)|_U`: precomposed with the identity of `(⋀^kT.X₁)|_U` tensored with
the restriction of the surjection `⋀^{m+1}T.X₂ ⟶ ⋀^{m+1}T.X₃` of [Stacks, Tag 01CJ], the
restriction of `SheafOfModules.exteriorGradedQuotientHom` is the restriction of
`SheafOfModules.exteriorGradedHom`, read through the transport of the total degree. -/
theorem openSubspaceTensorBifunctorIso_inv_comp_map_exteriorGradedQuotientHom (hS : T.Exact)
    (hepi : Epi T.g) (k m : ℕ) :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor (restrictToOpen X U).sheaf)).map
          (((openSubspaceRestriction U).map (𝟙 (AF₁.exteriorPower k)),
            (openSubspaceRestriction U).map
              (Stacks.SheafOfModules.TopWedge.relComplex A₂ AG₃ T.f T.g T.zero m).g) :
            ((openSubspaceRestriction U).obj (AF₁.exteriorPower k),
                (openSubspaceRestriction U).obj (A₂.exterior.piece ((m + 1 : ℕ) : ℤ))) ⟶
              ((openSubspaceRestriction U).obj (AF₁.exteriorPower k),
                (openSubspaceRestriction U).obj (AG₃.exterior.piece ((m + 1 : ℕ) : ℤ)))) ≫
        (openSubspaceTensorBifunctorIso U (AF₁.exteriorPower k)
              (AG₃.exterior.piece ((m + 1 : ℕ) : ℤ))).inv ≫
          (openSubspaceRestriction U).map
            (exteriorGradedQuotientHom AF₁ AG₃ A₂ hS hepi k m) =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          (restrictToOpen X U).sheaf)).map
          (((openSubspaceRestriction U).map (𝟙 (AF₁.exteriorPower k)),
            (openSubspaceRestriction U).map
              (eqToHom (exteriorPiece_one_add_eq A₂ m).symm)) :
            ((openSubspaceRestriction U).obj (AF₁.exteriorPower k),
                (openSubspaceRestriction U).obj (A₂.exterior.piece ((m + 1 : ℕ) : ℤ))) ⟶
              ((openSubspaceRestriction U).obj (AF₁.exteriorPower k),
                (openSubspaceRestriction U).obj (A₂.exteriorPower (1 + m)))) ≫
        (openSubspaceTensorBifunctorIso U (AF₁.exteriorPower k)
              (A₂.exteriorPower (1 + m))).inv ≫
          (openSubspaceRestriction U).map (exteriorGradedHom AF₁ A₂ T.f k m) :=
  Eq.trans (Category.assoc _ _ _).symm
    (Eq.trans
      (congrArg
        (fun z => z ≫ (openSubspaceRestriction U).map
          (exteriorGradedQuotientHom AF₁ AG₃ A₂ hS hepi k m))
        (invCompOfCompHom
            (openSubspaceTensorBifunctorIso U (AF₁.exteriorPower k)
              (A₂.exterior.piece ((m + 1 : ℕ) : ℤ)))
            (openSubspaceTensorBifunctorIso U (AF₁.exteriorPower k)
              (AG₃.exterior.piece ((m + 1 : ℕ) : ℤ)))
            _ _
            (openSubspaceTensorBifunctorIso_naturality U (𝟙 (AF₁.exteriorPower k))
              (Stacks.SheafOfModules.TopWedge.relComplex A₂ AG₃ T.f T.g T.zero m).g)).symm)
      (Eq.trans (Category.assoc _ _ _)
        (Eq.trans
          (congrArg
            (fun z => (openSubspaceTensorBifunctorIso U (AF₁.exteriorPower k)
              (A₂.exterior.piece ((m + 1 : ℕ) : ℤ))).inv ≫ z)
            (Eq.trans ((openSubspaceRestriction U).map_comp _ _).symm
              (Eq.trans
                (congrArg (openSubspaceRestriction U).map
                  (Eq.trans
                    (congrArg
                      (fun z => z ≫ exteriorGradedQuotientHom AF₁ AG₃ A₂ hS hepi k m)
                      (tensorLeftFunctorMapUnfold AF₁ k
                        (Stacks.SheafOfModules.TopWedge.relComplex A₂ AG₃ T.f T.g
                          T.zero m).g).symm)
                    (Eq.trans
                      (tensorLeftFunctor_map_extHom_comp_exteriorGradedQuotientHom AF₁ AG₃ A₂ hS
                        hepi k m)
                      (congrArg (fun z => z ≫ exteriorGradedHom AF₁ A₂ T.f k m)
                        (tensorLeftFunctorMapUnfold AF₁ k
                          (eqToHom (exteriorPiece_one_add_eq A₂ m).symm))))))
                ((openSubspaceRestriction U).map_comp _ _))))
          (Eq.trans (Category.assoc _ _ _).symm
            (Eq.trans
              (congrArg
                (fun z => z ≫ (openSubspaceRestriction U).map
                  (exteriorGradedHom AF₁ A₂ T.f k m))
                (invCompOfCompHom
                  (openSubspaceTensorBifunctorIso U (AF₁.exteriorPower k)
                    (A₂.exterior.piece ((m + 1 : ℕ) : ℤ)))
                  (openSubspaceTensorBifunctorIso U (AF₁.exteriorPower k)
                    (A₂.exteriorPower (1 + m)))
                  _ _
                  (openSubspaceTensorBifunctorIso_naturality U (𝟙 (AF₁.exteriorPower k))
                    (eqToHom (exteriorPiece_one_add_eq A₂ m).symm))))
              (Category.assoc _ _ _))))))


/-- **The restricted defining equation of the splitting-free comparison, with its target read on
`U` too.** `SheafOfModules.openSubspaceTensorBifunctorIso_inv_comp_map_exteriorGradedQuotientHom`
postcomposed with the comparison that restriction's preservation of finite colimits provides, so
that both legs land in the cokernel formed on `U`. This is the whole equation over `U`, the
restricted exterior algebra of `T.X₂` excepted. -/
theorem openSubspaceTensorBifunctorIso_inv_comp_map_exteriorGradedQuotientHom_comp_cokernelIso
    (hS : T.Exact) (hepi : Epi T.g) (k m : ℕ) :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor (restrictToOpen X U).sheaf)).map
          (((openSubspaceRestriction U).map (𝟙 (AF₁.exteriorPower k)),
            (openSubspaceRestriction U).map
              (Stacks.SheafOfModules.TopWedge.relComplex A₂ AG₃ T.f T.g T.zero m).g) :
            ((openSubspaceRestriction U).obj (AF₁.exteriorPower k),
                (openSubspaceRestriction U).obj (A₂.exterior.piece ((m + 1 : ℕ) : ℤ))) ⟶
              ((openSubspaceRestriction U).obj (AF₁.exteriorPower k),
                (openSubspaceRestriction U).obj (AG₃.exterior.piece ((m + 1 : ℕ) : ℤ)))) ≫
        (openSubspaceTensorBifunctorIso U (AF₁.exteriorPower k)
              (AG₃.exterior.piece ((m + 1 : ℕ) : ℤ))).inv ≫
          (openSubspaceRestriction U).map
              (exteriorGradedQuotientHom AF₁ AG₃ A₂ hS hepi k m) ≫
            (PreservesCokernel.iso (openSubspaceRestriction U)
              (prodWedgeHom AF₁ A₂ A₂ T.f (𝟙 T.X₂) (k + 1) m)).hom =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          (restrictToOpen X U).sheaf)).map
          (((openSubspaceRestriction U).map (𝟙 (AF₁.exteriorPower k)),
            (openSubspaceRestriction U).map
              (eqToHom (exteriorPiece_one_add_eq A₂ m).symm)) :
            ((openSubspaceRestriction U).obj (AF₁.exteriorPower k),
                (openSubspaceRestriction U).obj (A₂.exterior.piece ((m + 1 : ℕ) : ℤ))) ⟶
              ((openSubspaceRestriction U).obj (AF₁.exteriorPower k),
                (openSubspaceRestriction U).obj (A₂.exteriorPower (1 + m)))) ≫
        (openSubspaceTensorBifunctorIso U (AF₁.exteriorPower k)
              (A₂.exteriorPower (1 + m))).inv ≫
          (openSubspaceRestriction U).map (exteriorGradedHom AF₁ A₂ T.f k m) ≫
            (PreservesCokernel.iso (openSubspaceRestriction U)
              (prodWedgeHom AF₁ A₂ A₂ T.f (𝟙 T.X₂) (k + 1) m)).hom :=
  Eq.trans (compAssocThree _ _ _ _).symm
    (Eq.trans
      (congrArg
        (fun z => z ≫ (PreservesCokernel.iso (openSubspaceRestriction U)
          (prodWedgeHom AF₁ A₂ A₂ T.f (𝟙 T.X₂) (k + 1) m)).hom)
        (openSubspaceTensorBifunctorIso_inv_comp_map_exteriorGradedQuotientHom U AF₁ AG₃ A₂ hS
          hepi k m))
      (compAssocThree _ _ _ _))

/-! ### The epimorphism the restricted defining equation is cancelled against -/

/-- **The surjection `⋀^{m+1}T.X₂ ⟶ ⋀^{m+1}T.X₃` of the presentation of [Stacks, Tag 01CJ] is an
epimorphism.** -/
theorem epi_relComplex_g (hS : T.Exact) (hepi : Epi T.g) (m : ℕ) :
    Epi (Stacks.SheafOfModules.TopWedge.relComplex A₂ AG₃ T.f T.g T.zero m).g :=
  have := hepi
  (ExtPresentation.exteriorPresentation_exact A₂.exteriorGenerator AG₃.exteriorGenerator
    A₂.exterior_isExteriorAlgebra AG₃.exterior_isExteriorAlgebra T.g T.f T.zero hS m).2

/-- The restriction of an identity is an epimorphism. -/
theorem epi_openSubspaceRestriction_map_id (k : ℕ) :
    Epi ((openSubspaceRestriction U).map (𝟙 (AF₁.exteriorPower k))) :=
  Eq.mpr (congrArg Epi ((openSubspaceRestriction U).map_id (AF₁.exteriorPower k)))
    (inferInstance : Epi (𝟙 ((openSubspaceRestriction U).obj (AF₁.exteriorPower k))))

/-- **The morphism the restricted defining equation of the splitting-free comparison is
precomposed with is an epimorphism**: `⋀^kT.X₁|_U` tensored with the restriction of the surjection
of [Stacks, Tag 01CJ]. -/
theorem epi_tensorSheafBifunctorMap_openSubspaceRestriction_relComplex (hS : T.Exact)
    (hepi : Epi T.g) (k m : ℕ) :
    Epi ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        (restrictToOpen X U).sheaf)).map
          (((openSubspaceRestriction U).map (𝟙 (AF₁.exteriorPower k)),
            (openSubspaceRestriction U).map
              (Stacks.SheafOfModules.TopWedge.relComplex A₂ AG₃ T.f T.g T.zero m).g) :
            ((openSubspaceRestriction U).obj (AF₁.exteriorPower k),
                (openSubspaceRestriction U).obj (A₂.exterior.piece ((m + 1 : ℕ) : ℤ))) ⟶
              ((openSubspaceRestriction U).obj (AF₁.exteriorPower k),
                (openSubspaceRestriction U).obj
                  (AG₃.exterior.piece ((m + 1 : ℕ) : ℤ))))) :=
  have : Epi (Stacks.SheafOfModules.TopWedge.relComplex A₂ AG₃ T.f T.g T.zero m).g :=
    epi_relComplex_g AG₃ A₂ hS hepi m
  @Stacks.SheafOfModules.TensorEncodings.epi_tensorSheafBifunctor_map _ _
    (Opens.grothendieckTopology (restrictToOpen X U).carrier) _ _ _
    (restrictToOpen X U).sheaf _ _ _ _
    ((openSubspaceRestriction U).map (𝟙 (AF₁.exteriorPower k)))
    ((openSubspaceRestriction U).map
      (Stacks.SheafOfModules.TopWedge.relComplex A₂ AG₃ T.f T.g T.zero m).g)
    (epi_openSubspaceRestriction_map_id U AF₁ k) ((openSubspaceRestriction U).map_epi _)

/-- **The restricted defining equation determines the restricted comparison**: two morphisms out
of `(⋀^kT.X₁)|_U ⊗ (⋀^{m+1}T.X₃)|_U` that agree after precomposition with `⋀^kT.X₁|_U` tensored
with the restricted surjection of [Stacks, Tag 01CJ] are equal. -/
theorem eq_of_tensorSheafBifunctorMap_openSubspaceRestriction_relComplex_comp (hS : T.Exact)
    (hepi : Epi T.g) (k m : ℕ)
    {Z : SheafOfModules.{u} (Sheaf.toRingCat
      (Opens.grothendieckTopology (restrictToOpen X U).carrier) (restrictToOpen X U).sheaf)}
    (ψ₁ ψ₂ : (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        (restrictToOpen X U).sheaf)).obj
        ((openSubspaceRestriction U).obj (AF₁.exteriorPower k),
          (openSubspaceRestriction U).obj (AG₃.exterior.piece ((m + 1 : ℕ) : ℤ))) ⟶ Z)
    (h : (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        (restrictToOpen X U).sheaf)).map
          (((openSubspaceRestriction U).map (𝟙 (AF₁.exteriorPower k)),
            (openSubspaceRestriction U).map
              (Stacks.SheafOfModules.TopWedge.relComplex A₂ AG₃ T.f T.g T.zero m).g) :
            ((openSubspaceRestriction U).obj (AF₁.exteriorPower k),
                (openSubspaceRestriction U).obj (A₂.exterior.piece ((m + 1 : ℕ) : ℤ))) ⟶
              ((openSubspaceRestriction U).obj (AF₁.exteriorPower k),
                (openSubspaceRestriction U).obj
                  (AG₃.exterior.piece ((m + 1 : ℕ) : ℤ)))) ≫ ψ₁ =
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            (restrictToOpen X U).sheaf)).map
          (((openSubspaceRestriction U).map (𝟙 (AF₁.exteriorPower k)),
            (openSubspaceRestriction U).map
              (Stacks.SheafOfModules.TopWedge.relComplex A₂ AG₃ T.f T.g T.zero m).g) :
            ((openSubspaceRestriction U).obj (AF₁.exteriorPower k),
                (openSubspaceRestriction U).obj (A₂.exterior.piece ((m + 1 : ℕ) : ℤ))) ⟶
              ((openSubspaceRestriction U).obj (AF₁.exteriorPower k),
                (openSubspaceRestriction U).obj
                  (AG₃.exterior.piece ((m + 1 : ℕ) : ℤ)))) ≫ ψ₂) :
    ψ₁ = ψ₂ :=
  (epi_tensorSheafBifunctorMap_openSubspaceRestriction_relComplex U AF₁ AG₃ A₂ hS hepi k
    m).left_cancellation ψ₁ ψ₂ h

end GradedQuotientHom

end SheafOfModules

end
