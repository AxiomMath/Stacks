module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatDeformationKernelSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleRangeSections

/-!
# The sections `1 ⊗ (1 ⊗ c)` of the ideal of a deformation

For a closed immersion `j : T ⟶ T'` of objects of the big fppf site with `T'` affine and a
morphism `q : X ⟶ T`, the pullback to `X` of the conormal module of `T ⊆ T'` is
`𝒪_X ⊗_R (R ⊗_{R'} I)`, `R = Γ(T, 𝒪_T)`, `R' = Γ(T', 𝒪_{T'})`, `I = Ker(R' → R)`
(`AlgebraicGeometry.Space.conormalModuleRangePullbackIso`, [Stacks Project, Tag 04CN]). This
file reads that identification along `AlgebraicGeometry.Space.rangeSchemeSpaceIso` and computes
its pieces on global sections: on `T`, the section `1 ⊗ (1 ⊗ c)` of `𝒪_T ⊗_R (R ⊗_{R'} I)` is the
class of `c` in the conormal module, and pulling back along `q` carries such an identity to the
pulled-back identification. This is a step of the computation of the map of ideals of a
morphism of deformations in the proof of [Stacks Project, Tag 0D1K].

## Main definitions

* `AlgebraicGeometry.Space.rangeConormalBaseElement`: the element `1 ⊗ c` of `R ⊗_{R'} I`.
* `AlgebraicGeometry.Space.conormalModuleRangeSchemePullbackIso`: the identification of the
  pulled-back conormal module, read along `AlgebraicGeometry.Space.rangeSchemeSpaceIso`.

## Main results

* `AlgebraicGeometry.Space.conormalModuleRangeSchemePullbackIso_eq`: the variant is
  `AlgebraicGeometry.Space.conormalModuleRangePullbackIso`.
* `AlgebraicGeometry.Space.baseRingTensorSection_conormalModuleRangeSchemeIso_trans_inv`: the
  section `1 ⊗ (1 ⊗ c)` on `T`.
* `AlgebraicGeometry.Space.modulePullbackGlobalSection_mapIso_inv`: pulling back such identities.

## Implementation notes

The source of `AlgebraicGeometry.Space.rangeSpaceIso` is spelled `⟨yoneda.obj T, _⟩`, while the
morphisms into `T` are morphisms into `AlgebraicGeometry.Space.schemeSpace T` (a `def`). Terms
mixing the two spellings make the kernel unfold the module categories; the variants here use
`AlgebraicGeometry.Space.schemeSpace T` throughout. Each identity is stated with the objects
spelled exactly as in the composite it is used in (for instance with `.symm.inv` of a component
isomorphism rather than `.hom.app`), for the same reason.

## References

* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN)
* [Stacks Project, Tag 0D1K](https://stacks.math.columbia.edu/tag/0D1K)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

/- The global instance `Abelian (SheafOfModules.{max u v r w} O)` leaves a stuck universe
constraint against the `𝒪_X`-modules at the universe of the schemes. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Range

variable {T T' : BigFppfOver B S hS} (j : T ⟶ T')
  (hj : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j))
  (hT' : IsAffine ((BigFppfOver.toScheme B S hS).obj T'))

variable {X : AlgebraicSpaces B S hS} (q : X ⟶ schemeSpace T)

/-- **The conormal module of `T ⊆ T'` pulled back along `q : X ⟶ T` is `𝒪_X ⊗_R (R ⊗_{R'} I)`**:
`AlgebraicGeometry.Space.conormalModuleRangePullbackIso`, read along
`AlgebraicGeometry.Space.rangeSchemeSpaceIso`. -/
def conormalModuleRangeSchemePullbackIso :
    (modulePullback B S hS (q ≫ (rangeSchemeSpaceIso B S hS j hj).hom)).obj
        (rangeConormalModule B S hS j hj) ≅
      (baseRingTensorModule B S hS X (baseRingHomOfMap q)).obj
        (rangeConormalBaseModule B S hS j hj) :=
  ((modulePullbackCompIso B S hS q (rangeSchemeSpaceIso B S hS j hj).hom).app _).symm ≪≫
    (modulePullback B S hS q).mapIso
      (conormalModuleRangeSchemeIso B S hS j hj hT' ≪≫
        eqToIso (congrArg (fun φ => (baseRingTensorModule B S hS (schemeSpace T) φ).obj
          (ModuleCat.of (baseRing B S hS T')
            (closedSubspaceBaseIdeal B S hS (rangeSubspace B S hS j hj))))
          (baseRingHomOfMap_schemeSpaceMap B S hS j)) ≪≫
        ((baseRingTensorModuleCompIso B S hS (schemeSpace T)
          (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map j).op).hom
          (baseRingHomOfMap (𝟙 (schemeSpace T)))).app _).symm) ≪≫
    (baseRingTensorModulePullbackIso B S hS q).app _

/-- The variant `AlgebraicGeometry.Space.conormalModuleRangeSchemePullbackIso` is
`AlgebraicGeometry.Space.conormalModuleRangePullbackIso`. -/
theorem conormalModuleRangeSchemePullbackIso_eq :
    conormalModuleRangeSchemePullbackIso B S hS j hj hT' q =
      conormalModuleRangePullbackIso B S hS j hj hT' q :=
  rfl

/-- The sections `1 ⊗ m` along an equality of base-ring data, read through the inverse of the
identification of the modules. -/
theorem baseRingTensorSection_eqToIso_inv (X : AlgebraicSpaces B S hS) {R : Type u} [CommRing R]
    {φ φ' : R →+* modelGlobalFunctions B S hS X} (h : φ' = φ) (M : ModuleCat.{u} R) (m : M) :
    baseRingTensorSection B S hS X φ M m ≫
        (eqToIso (congrArg (fun φ => (baseRingTensorModule B S hS X φ).obj M) h)).inv =
      baseRingTensorSection B S hS X φ' M m := by
  subst h
  exact Category.comp_id _

/-- The element `1 ⊗ c` of `R ⊗_{R'} I`, `c ∈ I`. -/
def rangeConormalBaseElement (c : closedSubspaceBaseIdeal B S hS (rangeSubspace B S hS j hj)) :
    rangeConormalBaseModule B S hS j hj :=
  ((ModuleCat.extendRestrictScalarsAdj.{u, u, u}
    (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map j).op).hom).unit.app
    (ModuleCat.of (baseRing B S hS T')
      (closedSubspaceBaseIdeal B S hS (rangeSubspace B S hS j hj)))).hom c

/-- `AlgebraicGeometry.Space.baseRingTensorSection_compIso_hom`, with the inverse of the symmetric
component isomorphism. -/
theorem baseRingTensorSection_compIso_app_symm_inv (X : AlgebraicSpaces B S hS) {R R' : Type u}
    [CommRing R] [CommRing R'] (ψ : R →+* R') (φ' : R' →+* modelGlobalFunctions B S hS X)
    (M : ModuleCat.{u} R) (m : M) :
    baseRingTensorSection B S hS X φ' ((ModuleCat.extendScalars.{u, u, u} ψ).obj M)
        ((((ModuleCat.extendRestrictScalarsAdj.{u, u, u} ψ).unit.app M).hom m)) ≫
        ((baseRingTensorModuleCompIso B S hS X ψ φ').app M).symm.inv =
      baseRingTensorSection B S hS X (φ'.comp ψ) M m :=
  baseRingTensorSection_compIso_hom B S hS X ψ φ' M m

/-- The section `1 ⊗ (1 ⊗ c)` of `𝒪_T ⊗_R (R ⊗_{R'} I)` is the section `1 ⊗ c` of
`𝒪_T ⊗_{R'} I`, the ring `R'` acting through `R`. -/
theorem baseRingTensorSection_rangeConormalBaseModule_compIso
    (c : closedSubspaceBaseIdeal B S hS (rangeSubspace B S hS j hj)) :
    baseRingTensorSection B S hS (schemeSpace T) (baseRingHomOfMap (𝟙 (schemeSpace T)))
      (rangeConormalBaseModule B S hS j hj)
        (rangeConormalBaseElement B S hS j hj c) ≫
        ((baseRingTensorModuleCompIso B S hS (schemeSpace T)
          (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map j).op).hom
          (baseRingHomOfMap (𝟙 (schemeSpace T)))).app (ModuleCat.of (baseRing B S hS T')
            (closedSubspaceBaseIdeal B S hS (rangeSubspace B S hS j hj)))).symm.inv =
      baseRingTensorSection B S hS (schemeSpace T)
        ((baseRingHomOfMap (𝟙 (schemeSpace T))).comp
          (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map j).op).hom)
        (ModuleCat.of (baseRing B S hS T')
            (closedSubspaceBaseIdeal B S hS (rangeSubspace B S hS j hj))) c :=
  baseRingTensorSection_compIso_app_symm_inv B S hS
    (schemeSpace T) (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map j).op).hom
    (baseRingHomOfMap (𝟙 (schemeSpace T))) (ModuleCat.of (baseRing B S hS T')
      (closedSubspaceBaseIdeal B S hS (rangeSubspace B S hS j hj))) c

/-- The section `1 ⊗ (1 ⊗ c)` of `𝒪_T ⊗_R (R ⊗_{R'} I)` is the class of `c` in the conormal
module of `T ⊆ T'`, through the identification on `T` that
`AlgebraicGeometry.Space.conormalModuleRangeSchemePullbackIso` pulls back. -/
theorem baseRingTensorSection_conormalModuleRangeSchemeIso_trans_inv
    (c : closedSubspaceBaseIdeal B S hS (rangeSubspace B S hS j hj)) :
    baseRingTensorSection B S hS (schemeSpace T) (baseRingHomOfMap (𝟙 (schemeSpace T)))
      (rangeConormalBaseModule B S hS j hj)
        (rangeConormalBaseElement B S hS j hj c) ≫
      (conormalModuleRangeSchemeIso B S hS j hj hT' ≪≫
        eqToIso (congrArg (fun φ => (baseRingTensorModule B S hS (schemeSpace T) φ).obj
          (ModuleCat.of (baseRing B S hS T')
            (closedSubspaceBaseIdeal B S hS (rangeSubspace B S hS j hj))))
          (baseRingHomOfMap_schemeSpaceMap B S hS j)) ≪≫
        ((baseRingTensorModuleCompIso B S hS (schemeSpace T)
          (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map j).op).hom
          (baseRingHomOfMap (𝟙 (schemeSpace T)))).app _).symm).inv =
      modulePullbackGlobalSection B S hS (rangeSchemeSpaceIso B S hS j hj).hom
        (rangeConormalSection B S hS j hj c) := by
  refine (comp_trans_trans_inv _ _ _ _).trans ?_
  rw [baseRingTensorSection_rangeConormalBaseModule_compIso B S hS j hj c,
    baseRingTensorSection_eqToIso_inv B S hS (schemeSpace T)
      (baseRingHomOfMap_schemeSpaceMap B S hS j)]
  exact baseRingTensorSection_conormalModuleRangeSchemeIso_inv B S hS j hj hT' c

/-- **Pulling back a section read through an identification.** If `t` is the section `s` pulled
back along `e`, read through `K`, then the pullback of `t` along `q`, read through the pullback of
`K`, is the pullback of the pullback of `s`. -/
theorem modulePullbackGlobalSection_mapIso_inv {X Y Z : AlgebraicSpaces B S hS} (q : X ⟶ Y)
    (e : Y ⟶ Z) {C : Modules.{u, u} B S hS Z.1 Z.2}
    (s : SheafOfModules.unit (structureRingSheaf B S hS Z) ⟶ C)
    {N : Modules.{u, u} B S hS Y.1 Y.2} (K : (modulePullback B S hS e).obj C ≅ N)
    (t : SheafOfModules.unit (structureRingSheaf B S hS Y) ⟶ N)
    (ht : t ≫ K.inv = modulePullbackGlobalSection B S hS e s) :
    modulePullbackGlobalSection B S hS q t ≫ ((modulePullback B S hS q).mapIso K).inv =
      modulePullbackGlobalSection B S hS q (modulePullbackGlobalSection B S hS e s) :=
  (modulePullbackGlobalSection_comp B S hS q t K.inv).symm.trans
    (congrArg (modulePullbackGlobalSection B S hS q) ht)

end Range

end AlgebraicGeometry.Space

end
