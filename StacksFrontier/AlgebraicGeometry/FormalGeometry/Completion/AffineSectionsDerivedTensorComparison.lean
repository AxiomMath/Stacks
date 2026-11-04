module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizeAffine
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.AffineSectionsSiteComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorHomInterchange
public import StacksFrontier.Homology.KFlat.BifunctorSingleSecondFactor
public import StacksCore.Tactic.StacksAttribute

/-!
# Sections over an affine open against a derived tensor product

Let `X` be a scheme and `U ⊆ X` an affine open, with `A = Γ(X, U)`. This file builds the
comparison exchanging sections over `U` with a derived tensor product against a quasi-coherent
sheaf, in the form that the Mittag-Leffler step of part (2) of [Stacks, Tag 0A0K] consumes:

`Γ(U, H^i(K ⊗^𝐋_𝒪 ℱ)) ≅ H^i(Γ(U, E) ⊗^𝐋_A Γ(ℱ, U))`

for `K` represented by a K-flat complex `E` of quasi-coherent sheaves. The mechanism is that over
an affine open sections are **exact** on quasi-coherent modules, so they commute with the
cohomology of a complex of quasi-coherent modules; this is the first section below and it is the
reusable part.

## Main results

* `Stacks.Algebraization.preservesColimit_parallelPair_evaluation_of_isAffineOpen` — sections
  over an affine open preserve the cokernel of a morphism of quasi-coherent modules. This is
  `Stacks.Algebraization.affine_evaluation_preservesCokernel` at an arbitrary affine open of an
  arbitrary scheme rather than at `⊤` on an affine scheme.
* `Stacks.Algebraization.preservesRightHomologyOf_evaluation_of_isAffineOpen` — the same
  statement as the preservation of right homology data, which is what Mathlib's
  `CategoryTheory.ShortComplex.mapHomologyIso'` consumes.
* `Stacks.Algebraization.homologySectionsIsoOfIsAffineOpen` — **sections over an affine open
  commute with the cohomology of a complex of quasi-coherent modules**, and
  `Stacks.Algebraization.homologySectionsIsoOfIsAffineOpen_hom_naturality`, its naturality in the
  complex.

## References

* [Stacks Project, Tag 0A0K](https://stacks.math.columbia.edu/tag/0A0K)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

variable {X : Scheme.{u}}

/-! ### Sections over an open set, as an exact-on-quasi-coherents functor

`Stacks.Algebraization.schemeSectionsOver` is the sections functor `ℱ ↦ Γ(U, ℱ)`, ascribed as a
functor out of `X.Modules`; the ascription matters, because the instances carried by `X.Modules`
and by `SheafOfModules X.ringCatSheaf` are separately declared and instance resolution does not
identify them. It is already known additive, hence zero-morphism preserving. Limits of sheaves of
modules are computed on sections, so it preserves finite limits with no hypothesis. -/

/-- Sections over an open set preserve finite limits: limits of sheaves of modules are computed
sectionwise. -/
instance preservesFiniteLimits_schemeSectionsOver (U : X.Opens) :
    PreservesFiniteLimits (schemeSectionsOver U) :=
  _root_.SheafOfModules.Finite.evaluationPreservesFiniteLimits
    (structureSheafRing X.toRingedSpace) (op U)

/-! ### Sections over an affine open are exact on quasi-coherent modules -/

/-- **Sections over an affine open preserve the cokernel of a morphism of quasi-coherent
modules.** On those sections the morphism is exact onto the sections of its cokernel,
`Stacks.Algebraization.affine_sections_cokernel_exact`, and the quotient projection is surjective
there, `Stacks.Algebraization.surjective_app_of_epi_of_isAffineOpen`; that is exactly the
cokernel cofork in modules.

This is `Stacks.Algebraization.affine_evaluation_preservesCokernel` at an arbitrary affine open
of an arbitrary scheme rather than at `⊤` on an affine scheme. -/
theorem preservesColimit_parallelPair_evaluation_of_isAffineOpen
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) (U : X.affineOpens) :
    PreservesColimit (parallelPair (C := X.Modules) f 0) (schemeSectionsOver U.1) := by
  have hq : (cokernel (C := X.Modules) f).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel f
  have hc := ModuleCat.isColimitCokernelCofork
    ((schemeSectionsOver U.1).map f)
    ((schemeSectionsOver U.1).map (cokernel.π (C := X.Modules) f))
    (affine_sections_cokernel_exact f U)
    (surjective_app_of_epi_of_isAffineOpen (cokernel.π (C := X.Modules) f) U)
  refine preservesColimit_of_preserves_colimit_cocone (cokernelIsCokernel (C := X.Modules) f) ?_
  exact ((CokernelCofork.ofπ (cokernel.π (C := X.Modules) f)
    (cokernel.condition (C := X.Modules) f)).isColimitMapCoconeEquiv
      (schemeSectionsOver U.1)).symm hc

/-- **Sections over an affine open preserve the right homology of a short complex of
quasi-coherent modules.** A right homology datum is preserved as soon as the functor preserves
the cokernel of the first map — which is
`Stacks.Algebraization.preservesColimit_parallelPair_evaluation_of_isAffineOpen` — and the kernel
of the induced map out of that cokernel, which is a finite limit and so needs no hypothesis. -/
theorem preservesRightHomologyOf_evaluation_of_isAffineOpen
    (S : ShortComplex X.Modules) [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent]
    (U : X.affineOpens) :
    (schemeSectionsOver U.1).PreservesRightHomologyOf S :=
  ⟨fun _ =>
    { f := preservesColimit_parallelPair_evaluation_of_isAffineOpen S.f U
      g' := inferInstance }⟩

/-! ### Sections over an affine open commute with cohomology -/

/-- **Sections over an affine open commute with the cohomology of a complex of quasi-coherent
modules.** Sections are exact on quasi-coherent modules over an affine open, by
`Stacks.Algebraization.preservesRightHomologyOf_evaluation_of_isAffineOpen`, and an exact functor
commutes with the homology of a short complex; the cohomology of a cochain complex in degree `i`
is the homology of its short complex at `i`. -/
def homologySectionsIsoOfIsAffineOpen (C : CochainComplex X.Modules ℤ)
    (hqc : ∀ i : ℤ, (C.X i).IsQuasicoherent) (U : X.affineOpens) (i : ℤ) :
    (((schemeSectionsOver U.1).mapHomologicalComplex (ComplexShape.up ℤ)).obj C).homology i ≅
      (schemeSectionsOver U.1).obj (C.homology i) :=
  have : (C.sc i).X₁.IsQuasicoherent := hqc _
  have : (C.sc i).X₂.IsQuasicoherent := hqc _
  have := preservesRightHomologyOf_evaluation_of_isAffineOpen (C.sc i) U
  (C.sc i).mapHomologyIso' (schemeSectionsOver U.1)

/-- **`Stacks.Algebraization.homologySectionsIsoOfIsAffineOpen` is natural in the complex.** This
is what makes it usable on a whole inverse system of complexes at once, which is the form in
which the Mittag-Leffler step of part (2) of [Stacks, Tag 0A0K] consumes it: the Mittag-Leffler
condition of [Stacks, Tag 02N0] depends only on the isomorphism class of an inverse system, so a
comparison that is not natural transports nothing. -/
theorem homologySectionsIsoOfIsAffineOpen_hom_naturality {C D : CochainComplex X.Modules ℤ}
    (hC : ∀ i : ℤ, (C.X i).IsQuasicoherent) (hD : ∀ i : ℤ, (D.X i).IsQuasicoherent)
    (φ : C ⟶ D) (U : X.affineOpens) (i : ℤ) :
    HomologicalComplex.homologyMap
          (((schemeSectionsOver U.1).mapHomologicalComplex (ComplexShape.up ℤ)).map φ) i ≫
        (homologySectionsIsoOfIsAffineOpen D hD U i).hom =
      (homologySectionsIsoOfIsAffineOpen C hC U i).hom ≫
        (schemeSectionsOver U.1).map (HomologicalComplex.homologyMap φ i) :=
  have : (C.sc i).X₁.IsQuasicoherent := hC _
  have : (C.sc i).X₂.IsQuasicoherent := hC _
  have : (D.sc i).X₁.IsQuasicoherent := hD _
  have : (D.sc i).X₂.IsQuasicoherent := hD _
  have := preservesRightHomologyOf_evaluation_of_isAffineOpen (C.sc i) U
  have := preservesRightHomologyOf_evaluation_of_isAffineOpen (D.sc i) U
  ShortComplex.mapHomologyIso'_hom_naturality ((HomologicalComplex.shortComplexFunctor
    X.Modules (ComplexShape.up ℤ) i).map φ) (schemeSectionsOver U.1)

/-! ### A derived tensor product against a sheaf in degree zero -/

section DerivedTensorSingle

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.ringSheafSectionsCommRing
  AlgebraicGeometry.RingedSite.presheafOfModulesMonoidalCategory

variable (Y : AlgebraicGeometry.RingedSite.{u, u, u})
  [HasSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} Y.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} Y.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ)]

/-- **A derived tensor product of a K-flat complex with a sheaf of modules placed in degree zero
is the degreewise tensor product.** For `E` a K-flat complex of `𝒪`-modules and `M` a single
`𝒪`-module,

`Q(E) ⊗^𝐋_𝒪 M[0] ≅ Q(p ↦ Eᵖ ⊗_𝒪 M)`.

Three steps, all available. The derived tensor product with a K-flat **left** factor is the total
tensor complex, `AlgebraicGeometry.RingedSite.tensorTotalKFlatComparison` — and `E` is the left
factor here, which is why no flatness is asked of `M`. The total tensor complex of a ringed site
is `HomologicalComplex.mapBifunctor` of the tensor product of sheaves of modules, by
`AlgebraicGeometry.RingedSite.tensorTotalIsoTensorComplex` followed by a definitional
identification. And the total complex of a double complex whose second factor is concentrated in
degree zero is the degreewise complex, `CochainComplex.KFlatBifunctor.totalSingleIso`. -/
def derivedTensorSingleIsoRowComplex
    (E : CochainComplex (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) ℤ)
    (hE : Stacks.SheafOfModules.IsKFlat Y.O E)
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor Y).obj (DerivedCategory.Q.obj E)).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) 0).obj M) ≅
      DerivedCategory.Q.obj (CochainComplex.KFlatBifunctor.rowComplex
        (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) E M) :=
  ((Stacks.SheafOfModules.derivedTensorProductFunctor Y).obj (DerivedCategory.Q.obj E)).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) 0).app M) ≪≫
    AlgebraicGeometry.RingedSite.tensorTotalKFlatComparison Y E
      ((CochainComplex.singleFunctor
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) 0).obj M) hE ≪≫
    DerivedCategory.Q.mapIso
      (AlgebraicGeometry.RingedSite.tensorTotalIsoTensorComplex Y E _) ≪≫
    DerivedCategory.Q.mapIso (CochainComplex.KFlatBifunctor.totalSingleIso
      (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) E M)

end DerivedTensorSingle

end Stacks.Algebraization

end
