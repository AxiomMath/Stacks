module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeSiteComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.EssentiallySmallDerivedDualAdjunction

/-!
# The derived tensor product and the derived dual along an equivalence of ringed sites

Let `(C, 𝒪)` be a ringed site and `e : C' ≌ C` an equivalence of sites, continuous in both
directions and cocontinuous in the forward one, and give `C'` the structure sheaf `𝒪|_{C'}`
transported along `e` (the ringed site `AlgebraicGeometry.RingedSite.reindex`). Restriction of
sheaves of modules along `e` is an exact equivalence of the categories of modules, so it induces an
equivalence `Ψ : D(𝒪) ≌ D(𝒪|_{C'})`. This file shows that `Ψ` commutes with the derived tensor
product of Stacks 06YU, `Ψ(M ⊗^𝐋 K) ≅ Ψ M ⊗^𝐋 Ψ K` naturally in `M`, and, when both sites are
essentially small, with the derived dual `K^∨ = R𝓗om(K, 𝒪)`: `Ψ(K^∨) ≅ (Ψ K)^∨`. The second
statement is formal from the first: the derived dual is the value at `𝒪` of a right adjoint of
`- ⊗^𝐋 K` (Stacks 08J8), and right adjoints are unique.

## Main definitions

* `AlgebraicGeometry.RingedSite.reindexDerived`: the functor `Ψ : D(𝒪) ⥤ D(𝒪|_{C'})`.
* `AlgebraicGeometry.RingedSite.reindexDerivedTensorFlipIso`: `Ψ(M ⊗^𝐋 K) ≅ Ψ M ⊗^𝐋 Ψ K`,
  naturally in `M`.
* `AlgebraicGeometry.RingedSite.reindexDerivedStructureSheafIso`: `Ψ 𝒪 ≅ 𝒪|_{C'}`.
* `AlgebraicGeometry.RingedSite.reindexDerivedDualIso`: `Ψ(K^∨) ≅ (Ψ K)^∨`.

## Implementation notes

The comparison of the tensor products is built exactly as for the restriction to a small model
of the site, `AlgebraicGeometry.RingedSite.smallModelDerivedTensorFlipIso`, which is the case of
the equivalence with a small model: first on K-flat complexes in the first variable, where both
sides are total tensor complexes and restriction commutes with them degreewise (Stacks 01CU),
then descended along the localization of the K-flat complexes at the quasi-isomorphisms.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe c u

namespace AlgebraicGeometry.RingedSite

open Stacks.SheafOfModules Stacks.SheafOfModules.SiteEquivalenceDerivedTensor

variable (X : RingedSite.{c, u, u}) {C' : Type c} [Category.{u} C'] (J' : GrothendieckTopology C')
  (e : C' ≌ X.C) [e.functor.IsContinuous J' X.J] [e.inverse.IsContinuous X.J J']
  [e.functor.IsCocontinuous J' X.J]

variable [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify J' AddCommGrpCat.{u}] [J'.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Restriction of sheaves of modules along an equivalence of sites, on derived categories**:
the functor `Ψ : D(𝒪) ⥤ D(𝒪|_{C'})` induced by the exact equivalence `reindexMod`. -/
abbrev reindexDerived :
    letI := HasDerivedCategory.standard (SheafOfModules.{u} (Tensor.ringSheaf X.O))
    letI := HasDerivedCategory.standard
      (SheafOfModules.{u} (Tensor.ringSheaf (X.reindex J' e).O))
    DerivedCategory (SheafOfModules.{u} (Tensor.ringSheaf X.O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Tensor.ringSheaf (X.reindex J' e).O)) :=
  letI := HasDerivedCategory.standard (SheafOfModules.{u} (Tensor.ringSheaf X.O))
  letI := HasDerivedCategory.standard
      (SheafOfModules.{u} (Tensor.ringSheaf (X.reindex J' e).O))
  (reindexMod J' e X.O).functor.mapDerivedCategory

/-- `Ψ` as an equivalence of derived categories. -/
abbrev reindexDerivedEquivalence :
    letI := HasDerivedCategory.standard (SheafOfModules.{u} (Tensor.ringSheaf X.O))
    letI := HasDerivedCategory.standard
      (SheafOfModules.{u} (Tensor.ringSheaf (X.reindex J' e).O))
    DerivedCategory (SheafOfModules.{u} (Tensor.ringSheaf X.O)) ≌
      DerivedCategory (SheafOfModules.{u} (Tensor.ringSheaf (X.reindex J' e).O)) :=
  letI := HasDerivedCategory.standard (SheafOfModules.{u} (Tensor.ringSheaf X.O))
  letI := HasDerivedCategory.standard
      (SheafOfModules.{u} (Tensor.ringSheaf (X.reindex J' e).O))
  Dualizing.mapDerivedCategoryEquivalenceOfEquivalence (reindexMod J' e X.O)

/-- **`Ψ 𝒪 ≅ 𝒪|_{C'}`**: restriction carries the structure sheaf in degree zero to the
structure sheaf in degree zero. -/
def reindexDerivedStructureSheafIso :
    letI := HasDerivedCategory.standard (SheafOfModules.{u} (Tensor.ringSheaf X.O))
    letI := HasDerivedCategory.standard
      (SheafOfModules.{u} (Tensor.ringSheaf (X.reindex J' e).O))
    (X.reindexDerived J' e).obj (derivedStructureSheaf X) ≅
      derivedStructureSheaf (X.reindex J' e) :=
  letI := HasDerivedCategory.standard (SheafOfModules.{u} (Tensor.ringSheaf X.O))
  letI := HasDerivedCategory.standard
      (SheafOfModules.{u} (Tensor.ringSheaf (X.reindex J' e).O))
  (reindexMod J' e X.O).functor.mapDerivedCategoryFactors.app _ ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex (reindexMod J' e X.O).functor
        (ComplexShape.up ℤ) 0).app (SheafOfModules.unit (Tensor.ringSheaf X.O)))

variable [(Tensor.sheafTensor.{c, u, u, u, u} X.O).Additive]
  [∀ M, ((Tensor.sheafTensor.{c, u, u, u, u} X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{c, u, u} X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor X.O) (ComplexShape.up ℤ)]
  [(Tensor.sheafTensor.{c, u, u, u, u} (X.reindex J' e).O).Additive]
  [∀ M, ((Tensor.sheafTensor.{c, u, u, u, u} (X.reindex J' e).O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Tensor.ringSheaf.{c, u, u} (X.reindex J' e).O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor (X.reindex J' e).O)
      (ComplexShape.up ℤ)]

/-- The restriction of the derived tensor product with a fixed complex `L`, on K-flat first
factors: `Ψ(A ⊗^𝐋 L) ≅ Ψ A ⊗^𝐋 Ψ L` for `A` K-flat, naturally in `A`. -/
def reindexKFlatTensorRightIso
    (L : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf X.O)) ℤ) :
    letI := HasDerivedCategory.standard (SheafOfModules.{u} (Tensor.ringSheaf X.O))
    letI := HasDerivedCategory.standard
      (SheafOfModules.{u} (Tensor.ringSheaf (X.reindex J' e).O))
    kFlatComplexQ X ⋙ (derivedTensorBifunctor X).flip.obj (DerivedCategory.Q.obj L) ⋙
        X.reindexDerived J' e ≅
      kFlatComplexQ X ⋙ X.reindexDerived J' e ⋙
        (derivedTensorBifunctor (X.reindex J' e)).flip.obj
          ((X.reindexDerived J' e).obj (DerivedCategory.Q.obj L)) :=
  letI := HasDerivedCategory.standard (SheafOfModules.{u} (Tensor.ringSheaf X.O))
  letI := HasDerivedCategory.standard
      (SheafOfModules.{u} (Tensor.ringSheaf (X.reindex J' e).O))
  let R := reindexMod J' e X.O
  let Φc := R.functor.mapHomologicalComplex (ComplexShape.up ℤ)
  let fac : Φc ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ X.reindexDerived J' e :=
    R.functor.mapDerivedCategoryFactors.symm
  let Lift : (kFlatComplexes X).FullSubcategory ⥤
      (kFlatComplexes (X.reindex J' e)).FullSubcategory :=
    ObjectProperty.lift _ ((kFlatComplexes X).ι ⋙ Φc) fun A =>
      kFlat_reindexMod_map J' e X.O A.obj A.2
  let e3 : (kFlatComplexes X).ι ⋙ (Tensor.tensorComplex X.O).flip.obj L ⋙ Φc ≅
      (kFlatComplexes X).ι ⋙ Φc ⋙
        (Tensor.tensorComplex (X.reindex J' e).O).flip.obj (Φc.obj L) :=
    NatIso.ofComponents (fun A => reindexModTensorComplexIso J' e X.O A.obj L)
      (fun f => by
        have h := reindexModTensorComplexIso_hom_naturality_left J' e X.O f.hom L
        refine Eq.trans ?_ (h.trans ?_)
        · rfl
        · rfl)
  Functor.isoWhiskerRight (kFlatComplexQTensorRightIso X L) _ ≪≫
    Functor.isoWhiskerLeft ((kFlatComplexes X).ι ⋙ (Tensor.tensorComplex X.O).flip.obj L)
      fac.symm ≪≫
    Functor.isoWhiskerRight e3 DerivedCategory.Q ≪≫
    (Functor.isoWhiskerLeft Lift (kFlatComplexQTensorRightIso (X.reindex J' e) (Φc.obj L))).symm ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft (kFlatComplexes X).ι fac)
      ((derivedTensorBifunctor (X.reindex J' e)).flip.obj (DerivedCategory.Q.obj (Φc.obj L))) ≪≫
    Functor.isoWhiskerLeft (kFlatComplexQ X ⋙ X.reindexDerived J' e)
      ((derivedTensorBifunctor (X.reindex J' e)).flip.mapIso (fac.app L))

/-- **Restriction commutes with the derived tensor product with a fixed object**, on the
derived tensor bifunctor: `Ψ(M ⊗^𝐋 Q L) ≅ Ψ M ⊗^𝐋 Ψ(Q L)`, naturally in `M`. -/
def reindexDerivedTensorBifunctorRightIso
    (L : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf X.O)) ℤ) :
    letI := HasDerivedCategory.standard (SheafOfModules.{u} (Tensor.ringSheaf X.O))
    letI := HasDerivedCategory.standard
      (SheafOfModules.{u} (Tensor.ringSheaf (X.reindex J' e).O))
    (derivedTensorBifunctor X).flip.obj (DerivedCategory.Q.obj L) ⋙ X.reindexDerived J' e ≅
      X.reindexDerived J' e ⋙ (derivedTensorBifunctor (X.reindex J' e)).flip.obj
        ((X.reindexDerived J' e).obj (DerivedCategory.Q.obj L)) :=
  letI := HasDerivedCategory.standard (SheafOfModules.{u} (Tensor.ringSheaf X.O))
  letI := HasDerivedCategory.standard
      (SheafOfModules.{u} (Tensor.ringSheaf (X.reindex J' e).O))
  (Localization.whiskeringLeftFunctor' (kFlatComplexQ X) (kFlatComplexQuasiIso X) _).preimageIso
    (X.reindexKFlatTensorRightIso J' e L)

/-- **Restriction along an equivalence of sites commutes with the derived tensor product with a
fixed object**: `Ψ(M ⊗^𝐋 K) ≅ Ψ M ⊗^𝐋 Ψ K`, naturally in `M`. -/
def reindexDerivedTensorFlipIso
    (K : @DerivedCategory (SheafOfModules.{u} (Tensor.ringSheaf X.O)) _ _
      (HasDerivedCategory.standard _)) :
    letI := HasDerivedCategory.standard (SheafOfModules.{u} (Tensor.ringSheaf X.O))
    letI := HasDerivedCategory.standard
      (SheafOfModules.{u} (Tensor.ringSheaf (X.reindex J' e).O))
    (derivedTensorProductFunctor X).flip.obj K ⋙ X.reindexDerived J' e ≅
      X.reindexDerived J' e ⋙
        (derivedTensorProductFunctor (X.reindex J' e)).flip.obj ((X.reindexDerived J' e).obj K) :=
  letI := HasDerivedCategory.standard (SheafOfModules.{u} (Tensor.ringSheaf X.O))
  letI := HasDerivedCategory.standard
      (SheafOfModules.{u} (Tensor.ringSheaf (X.reindex J' e).O))
  let i := DerivedCategory.Q.objObjPreimageIso K
  Functor.isoWhiskerRight
      (eqToIso (congrArg (fun T => T.flip.obj K) (canonicalDerivedTensorProduct_tensor X)) ≪≫
        (derivedTensorBifunctor X).flip.mapIso i.symm) _ ≪≫
    X.reindexDerivedTensorBifunctorRightIso J' e (DerivedCategory.Q.objPreimage K) ≪≫
    Functor.isoWhiskerLeft _
      ((derivedTensorBifunctor (X.reindex J' e)).flip.mapIso ((X.reindexDerived J' e).mapIso i) ≪≫
        eqToIso (congrArg (fun T => T.flip.obj ((X.reindexDerived J' e).obj K))
          (canonicalDerivedTensorProduct_tensor (X.reindex J' e)).symm))

variable [EssentiallySmall.{u} X.C] [EssentiallySmall.{u} C']

/-- **Restriction along an equivalence of sites commutes with the right adjoint of
`- ⊗^𝐋 K`**: `Ψ R𝓗om(K, N) ≅ R𝓗om(Ψ K, Ψ N)`, the two being the right adjoints of the two
sides of `AlgebraicGeometry.RingedSite.reindexDerivedTensorFlipIso`. -/
def reindexDerivedSheafHomIso
    (K N : @DerivedCategory (SheafOfModules.{u} (Tensor.ringSheaf X.O)) _ _
      (HasDerivedCategory.standard _)) :
    letI := HasDerivedCategory.standard (SheafOfModules.{u} (Tensor.ringSheaf X.O))
    letI := HasDerivedCategory.standard
      (SheafOfModules.{u} (Tensor.ringSheaf (X.reindex J' e).O))
    (X.reindexDerived J' e).obj ((essentiallySmallDerivedSheafHom X K).obj N) ≅
      (essentiallySmallDerivedSheafHom (X.reindex J' e) ((X.reindexDerived J' e).obj K)).obj
        ((X.reindexDerived J' e).obj N) :=
  letI := HasDerivedCategory.standard (SheafOfModules.{u} (Tensor.ringSheaf X.O))
  letI := HasDerivedCategory.standard
      (SheafOfModules.{u} (Tensor.ringSheaf (X.reindex J' e).O))
  let Ψe := X.reindexDerivedEquivalence J' e
  let adjA := ((essentiallySmallDerivedTensorSheafHomAdjunction X K).comp
    Ψe.toAdjunction).ofNatIsoLeft (X.reindexDerivedTensorFlipIso J' e K)
  let adjB := Ψe.toAdjunction.comp
    (essentiallySmallDerivedTensorSheafHomAdjunction (X.reindex J' e) (Ψe.functor.obj K))
  let uniq := adjA.rightAdjointUniq adjB
  Ψe.functor.mapIso ((essentiallySmallDerivedSheafHom X K).mapIso (Ψe.unitIso.app N) ≪≫
      uniq.app (Ψe.functor.obj N)) ≪≫
    Ψe.counitIso.app _

/-- **Restriction along an equivalence of sites commutes with the derived dual**:
`Ψ(K^∨) ≅ (Ψ K)^∨` for every `K`, where `K^∨ = R𝓗om(K, 𝒪)` is
`AlgebraicGeometry.RingedSite.essentiallySmallDerivedDual`. -/
def reindexDerivedDualIso
    (K : @DerivedCategory (SheafOfModules.{u} (Tensor.ringSheaf X.O)) _ _
      (HasDerivedCategory.standard _)) :
    letI := HasDerivedCategory.standard (SheafOfModules.{u} (Tensor.ringSheaf X.O))
    letI := HasDerivedCategory.standard
      (SheafOfModules.{u} (Tensor.ringSheaf (X.reindex J' e).O))
    (X.reindexDerived J' e).obj (essentiallySmallDerivedDual X K) ≅
      essentiallySmallDerivedDual (X.reindex J' e) ((X.reindexDerived J' e).obj K) :=
  letI := HasDerivedCategory.standard (SheafOfModules.{u} (Tensor.ringSheaf X.O))
  letI := HasDerivedCategory.standard
      (SheafOfModules.{u} (Tensor.ringSheaf (X.reindex J' e).O))
  (X.reindexDerived J' e).mapIso (essentiallySmallDerivedDualIso X K) ≪≫
    X.reindexDerivedSheafHomIso J' e K _ ≪≫
    (essentiallySmallDerivedSheafHom (X.reindex J' e) ((X.reindexDerived J' e).obj K)).mapIso
      (X.reindexDerivedStructureSheafIso J' e) ≪≫
    (essentiallySmallDerivedDualIso (X.reindex J' e) _).symm

end AlgebraicGeometry.RingedSite

end
