module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatDeformationIdealSections

/-!
# The pulled-back sections `1 ⊗ (1 ⊗ c)` of the ideal of a deformation

For a closed immersion `j : T ⟶ T'` of objects of the big fppf site with `T'` affine and a
morphism `q : X ⟶ T`, the pullback to `X` of the conormal module of `T ⊆ T'` is
`𝒪_X ⊗_R (R ⊗_{R'} I)`, `R = Γ(T, 𝒪_T)`, `R' = Γ(T', 𝒪_{T'})`, `I = Ker(R' → R)`
(`AlgebraicGeometry.Space.conormalModuleRangePullbackIso`, [Stacks Project, Tag 04CN]). This file
shows that this identification carries the section `1 ⊗ (1 ⊗ c)` of `𝒪_X ⊗_R (R ⊗_{R'} I)`,
`c ∈ I`, to the pullback along `X ⟶ T ≅ T'|_T` of the class of `c` in the conormal module. This is
a step of the computation of the map of ideals of a morphism of deformations in the proof of
[Stacks Project, Tag 0D1K].

## Main definitions

* `AlgebraicGeometry.Space.conormalModuleRangeSchemeBaseIso`: the conormal module of `T ⊆ T'` on
  `T` is `𝒪_T ⊗_R (R ⊗_{R'} I)`.
* `AlgebraicGeometry.Space.conormalModuleRangeSchemeBasePullbackIso`: its pullback along `q`, equal
  to `AlgebraicGeometry.Space.conormalModuleRangePullbackIso`
  (`AlgebraicGeometry.Space.conormalModuleRangeSchemeBasePullbackIso_eq`).

## Main results

* `AlgebraicGeometry.Space.modulePullbackGlobalSection_compIso_symm_trans_mapIso_trans_inv`:
  pulling back a section through a composite identification.
* `AlgebraicGeometry.Space.baseRingTensorSection_conormalModuleRangeSchemeBasePullbackIso_inv`:
  the section `1 ⊗ (1 ⊗ c)` on `X`.

## Implementation notes

The `R`-module `R ⊗_{R'} I` is spelled `(ModuleCat.extendScalars _).obj (ModuleCat.of _ I)`
throughout, not through the abbreviation `AlgebraicGeometry.Space.rangeConormalBaseModule`: the
two spellings are definitionally equal, but a composite of morphisms of modules mixing them makes
the kernel unfold the module categories. Likewise the identifications are unfolded by `rw` with
`rfl` equations (`…_inv_eq`) before the generic statements are applied.

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

/-- **Pulling back a section through a composite identification.** If `t` is the section `s`
pulled back along `e`, read through `K`, and `σ` is the pullback of `t` along `q`, read through
`L`, then `σ`, read through `(q ≫ e)^* C ≅ q^* e^* C ≅ q^* N ≅ P`, is the pullback of `s` along
`q ≫ e`. -/
theorem modulePullbackGlobalSection_compIso_symm_trans_mapIso_trans_inv
    {X Y Z : AlgebraicSpaces B S hS} (q : X ⟶ Y) (e : Y ⟶ Z) {C : Modules.{u, u} B S hS Z.1 Z.2}
    (s : SheafOfModules.unit (structureRingSheaf B S hS Z) ⟶ C)
    {N : Modules.{u, u} B S hS Y.1 Y.2} (K : (modulePullback B S hS e).obj C ≅ N)
    (t : SheafOfModules.unit (structureRingSheaf B S hS Y) ⟶ N)
    (ht : t ≫ K.inv = modulePullbackGlobalSection B S hS e s)
    {P : Modules.{u, u} B S hS X.1 X.2} (L : (modulePullback B S hS q).obj N ≅ P)
    (σ : SheafOfModules.unit (structureRingSheaf B S hS X) ⟶ P)
    (hσ : σ ≫ L.inv = modulePullbackGlobalSection B S hS q t) :
    σ ≫ (((modulePullbackCompIso B S hS q e).app C).symm ≪≫ (modulePullback B S hS q).mapIso K ≪≫
      L).inv = modulePullbackGlobalSection B S hS (q ≫ e) s := by
  have h := comp_trans_trans_inv σ ((modulePullbackCompIso B S hS q e).app C).symm
    ((modulePullback B S hS q).mapIso K) L
  rw [hσ, modulePullbackGlobalSection_mapIso_inv B S hS q e s K t ht, Iso.symm_inv,
    modulePullbackGlobalSection_comp_modulePullbackCompIso_app_hom B S hS q e s] at h
  exact h

/-- `AlgebraicGeometry.Space.modulePullbackGlobalSection_compIso_symm_trans_mapIso_trans_inv`, with
the sections `t` and `σ` given on `AlgebraicGeometry.Space.unitModule`. -/
theorem modulePullbackGlobalSection_compIso_symm_trans_mapIso_trans_inv_of_unitModule
    {X Y Z : AlgebraicSpaces B S hS} (q : X ⟶ Y) (e : Y ⟶ Z) {C : Modules.{u, u} B S hS Z.1 Z.2}
    (s : SheafOfModules.unit (structureRingSheaf B S hS Z) ⟶ C)
    {N : Modules.{u, u} B S hS Y.1 Y.2} (K : (modulePullback B S hS e).obj C ≅ N)
    (t : unitModule B S hS Y.2 ⟶ N)
    (ht : t ≫ K.inv = modulePullbackGlobalSection B S hS e s)
    {P : Modules.{u, u} B S hS X.1 X.2} (L : (modulePullback B S hS q).obj N ≅ P)
    (σ : unitModule B S hS X.2 ⟶ P)
    (hσ : σ ≫ L.inv = modulePullbackGlobalSection B S hS q t) :
    σ ≫ (((modulePullbackCompIso B S hS q e).app C).symm ≪≫ (modulePullback B S hS q).mapIso K ≪≫
      L).inv = modulePullbackGlobalSection B S hS (q ≫ e) s :=
  modulePullbackGlobalSection_compIso_symm_trans_mapIso_trans_inv B S hS q e s K t ht L σ hσ

/-- **`𝒪_X ⊗_R M ≅ 𝒪_X ⊗_{R'} (R' ⊗_R M)`**, the inverse of the component at `M` of
`AlgebraicGeometry.Space.baseRingTensorModuleCompIso`, with its target spelled as
`𝒪_X ⊗_{R'} -` applied to `R' ⊗_R M`. -/
def baseRingTensorModuleExtendScalarsIso (X : AlgebraicSpaces B S hS) {R R' : Type u}
    [CommRing R] [CommRing R'] (ψ : R →+* R') (φ' : R' →+* modelGlobalFunctions B S hS X)
    (M : ModuleCat.{u} R) :
    (baseRingTensorModule B S hS X (φ'.comp ψ)).obj M ≅
      (baseRingTensorModule B S hS X φ').obj ((ModuleCat.extendScalars.{u, u, u} ψ).obj M) :=
  ((baseRingTensorModuleCompIso B S hS X ψ φ').app M).symm

/-- **The conormal module of `T ⊆ T'` on `T` is `𝒪_T ⊗_R (R ⊗_{R'} I)`**, read along
`AlgebraicGeometry.Space.rangeSchemeSpaceIso`. -/
def conormalModuleRangeSchemeBaseIso :
    (modulePullback B S hS (rangeSchemeSpaceIso B S hS j hj).hom).obj
        (rangeConormalModule B S hS j hj) ≅
      (baseRingTensorModule B S hS (schemeSpace T) (baseRingHomOfMap (𝟙 (schemeSpace T)))).obj
        ((ModuleCat.extendScalars.{u, u, u}
          (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map j).op).hom).obj
          (ModuleCat.of (baseRing B S hS T')
            (closedSubspaceBaseIdeal B S hS (rangeSubspace B S hS j hj)))) :=
  conormalModuleRangeSchemeIso B S hS j hj hT' ≪≫
    eqToIso (congrArg (fun φ => (baseRingTensorModule B S hS (schemeSpace T) φ).obj
      (ModuleCat.of (baseRing B S hS T')
        (closedSubspaceBaseIdeal B S hS (rangeSubspace B S hS j hj))))
      (baseRingHomOfMap_schemeSpaceMap B S hS j)) ≪≫
    baseRingTensorModuleExtendScalarsIso B S hS (schemeSpace T)
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map j).op).hom
      (baseRingHomOfMap (𝟙 (schemeSpace T)))
      (ModuleCat.of (baseRing B S hS T')
        (closedSubspaceBaseIdeal B S hS (rangeSubspace B S hS j hj)))


/-- `AlgebraicGeometry.Space.conormalModuleRangeSchemeBaseIso` as the composite it is defined
by, with the last factor spelled as in
`AlgebraicGeometry.Space.conormalModuleRangeSchemePullbackIso`. -/
theorem conormalModuleRangeSchemeBaseIso_inv_eq :
    (conormalModuleRangeSchemeBaseIso B S hS j hj hT').inv =
      (conormalModuleRangeSchemeIso B S hS j hj hT' ≪≫
        eqToIso (congrArg (fun φ => (baseRingTensorModule B S hS (schemeSpace T) φ).obj
          (ModuleCat.of (baseRing B S hS T')
            (closedSubspaceBaseIdeal B S hS (rangeSubspace B S hS j hj))))
          (baseRingHomOfMap_schemeSpaceMap B S hS j)) ≪≫
        ((baseRingTensorModuleCompIso B S hS (schemeSpace T)
          (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map j).op).hom
          (baseRingHomOfMap (𝟙 (schemeSpace T)))).app _).symm).inv := rfl

/-- The section `1 ⊗ (1 ⊗ c)` of `𝒪_T ⊗_R (R ⊗_{R'} I)` is the class of `c` in the conormal
module of `T ⊆ T'`, through `AlgebraicGeometry.Space.conormalModuleRangeSchemeBaseIso`. -/
theorem baseRingTensorSection_conormalModuleRangeSchemeBaseIso_inv
    (c : closedSubspaceBaseIdeal B S hS (rangeSubspace B S hS j hj)) :
    baseRingTensorSection B S hS (schemeSpace T) (baseRingHomOfMap (𝟙 (schemeSpace T)))
      ((ModuleCat.extendScalars.{u, u, u}
          (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map j).op).hom).obj
          (ModuleCat.of (baseRing B S hS T')
            (closedSubspaceBaseIdeal B S hS (rangeSubspace B S hS j hj))))
        (rangeConormalBaseElement B S hS j hj c) ≫
      (conormalModuleRangeSchemeBaseIso B S hS j hj hT').inv =
      modulePullbackGlobalSection B S hS (rangeSchemeSpaceIso B S hS j hj).hom
        (rangeConormalSection B S hS j hj c) := by
  rw [conormalModuleRangeSchemeBaseIso_inv_eq]
  exact baseRingTensorSection_conormalModuleRangeSchemeIso_trans_inv B S hS j hj hT' c

/-- **The conormal module of `T ⊆ T'` pulled back along `q : X ⟶ T` is `𝒪_X ⊗_R (R ⊗_{R'} I)`**,
assembled from `AlgebraicGeometry.Space.conormalModuleRangeSchemeBaseIso`. -/
def conormalModuleRangeSchemeBasePullbackIso :
    (modulePullback B S hS (q ≫ (rangeSchemeSpaceIso B S hS j hj).hom)).obj
        (rangeConormalModule B S hS j hj) ≅
      (baseRingTensorModule B S hS X (baseRingHomOfMap q)).obj
        ((ModuleCat.extendScalars.{u, u, u}
          (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map j).op).hom).obj
          (ModuleCat.of (baseRing B S hS T')
            (closedSubspaceBaseIdeal B S hS (rangeSubspace B S hS j hj)))) :=
  ((modulePullbackCompIso B S hS q (rangeSchemeSpaceIso B S hS j hj).hom).app
      (rangeConormalModule B S hS j hj)).symm ≪≫
    (modulePullback B S hS q).mapIso (conormalModuleRangeSchemeBaseIso B S hS j hj hT') ≪≫
    (baseRingTensorModulePullbackIso B S hS q).app
      ((ModuleCat.extendScalars.{u, u, u}
        (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map j).op).hom).obj
        (ModuleCat.of (baseRing B S hS T')
          (closedSubspaceBaseIdeal B S hS (rangeSubspace B S hS j hj))))

/-- `AlgebraicGeometry.Space.conormalModuleRangeSchemeBasePullbackIso` as the composite it is
defined by. -/
theorem conormalModuleRangeSchemeBasePullbackIso_inv_eq :
    (conormalModuleRangeSchemeBasePullbackIso B S hS j hj hT' q).inv =
      (((modulePullbackCompIso B S hS q (rangeSchemeSpaceIso B S hS j hj).hom).app
        (rangeConormalModule B S hS j hj)).symm ≪≫
      (modulePullback B S hS q).mapIso (conormalModuleRangeSchemeBaseIso B S hS j hj hT') ≪≫
      (baseRingTensorModulePullbackIso B S hS q).app
      ((ModuleCat.extendScalars.{u, u, u}
        (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map j).op).hom).obj
        (ModuleCat.of (baseRing B S hS T')
          (closedSubspaceBaseIdeal B S hS (rangeSubspace B S hS j hj))))).inv :=
  rfl

/-- **The section `1 ⊗ (1 ⊗ c)` of `𝒪_X ⊗_R (R ⊗_{R'} I)`** is, through
`AlgebraicGeometry.Space.conormalModuleRangeSchemeBasePullbackIso`, the pullback along
`q : X ⟶ T ≅ T'|_T` of the class of `c` in the conormal module of `T ⊆ T'`. -/
theorem baseRingTensorSection_conormalModuleRangeSchemeBasePullbackIso_inv
    (c : closedSubspaceBaseIdeal B S hS (rangeSubspace B S hS j hj)) :
    baseRingTensorSection B S hS X (baseRingHomOfMap q)
      ((ModuleCat.extendScalars.{u, u, u}
          (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map j).op).hom).obj
          (ModuleCat.of (baseRing B S hS T')
            (closedSubspaceBaseIdeal B S hS (rangeSubspace B S hS j hj))))
        (rangeConormalBaseElement B S hS j hj c) ≫
        (conormalModuleRangeSchemeBasePullbackIso B S hS j hj hT' q).inv =
      modulePullbackGlobalSection B S hS (q ≫ (rangeSchemeSpaceIso B S hS j hj).hom)
        (rangeConormalSection B S hS j hj c) := by
  rw [conormalModuleRangeSchemeBasePullbackIso_inv_eq]
  have ht := baseRingTensorSection_conormalModuleRangeSchemeBaseIso_inv B S hS j hj hT' c
  have hσ := baseRingTensorSection_comp_pullbackIso_app_inv B S hS q
    ((ModuleCat.extendScalars.{u, u, u}
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map j).op).hom).obj
      (ModuleCat.of (baseRing B S hS T')
        (closedSubspaceBaseIdeal B S hS (rangeSubspace B S hS j hj))))
    (rangeConormalBaseElement B S hS j hj c)
  have g := modulePullbackGlobalSection_compIso_symm_trans_mapIso_trans_inv_of_unitModule B S hS q
    (rangeSchemeSpaceIso B S hS j hj).hom (rangeConormalSection B S hS j hj c) _ _ ht _ _ hσ
  exact g

/-- The variant `AlgebraicGeometry.Space.conormalModuleRangeSchemeBasePullbackIso` is
`AlgebraicGeometry.Space.conormalModuleRangePullbackIso`. -/
theorem conormalModuleRangeSchemeBasePullbackIso_eq :
    conormalModuleRangeSchemeBasePullbackIso B S hS j hj hT' q =
      conormalModuleRangePullbackIso B S hS j hj hT' q :=
  rfl

/-- The section `1 ⊗ m` of `𝒪_X ⊗_R (R ⊗_{R'} I)`, followed by a morphism, does not depend on the
spelling of `R ⊗_{R'} I`. -/
theorem baseRingTensorSection_rangeConormalBaseModule_comp
    (m : rangeConormalBaseModule B S hS j hj)
    {Q : Modules.{u, u} B S hS X.1 X.2}
    (f : (baseRingTensorModule B S hS X (baseRingHomOfMap q)).obj
      ((ModuleCat.extendScalars.{u, u, u}
        (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map j).op).hom).obj
        (ModuleCat.of (baseRing B S hS T')
          (closedSubspaceBaseIdeal B S hS (rangeSubspace B S hS j hj)))) ⟶ Q) :
    baseRingTensorSection B S hS X (baseRingHomOfMap q) (rangeConormalBaseModule B S hS j hj) m ≫
        f =
      baseRingTensorSection B S hS X (baseRingHomOfMap q)
        ((ModuleCat.extendScalars.{u, u, u}
          (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map j).op).hom).obj
          (ModuleCat.of (baseRing B S hS T')
            (closedSubspaceBaseIdeal B S hS (rangeSubspace B S hS j hj)))) m ≫ f :=
  rfl

/-- **The section `1 ⊗ (1 ⊗ c)` of `𝒪_X ⊗_R (R ⊗_{R'} I)`**, with `R ⊗_{R'} I` spelled
`AlgebraicGeometry.Space.rangeConormalBaseModule`, is, through
`AlgebraicGeometry.Space.conormalModuleRangeSchemeBasePullbackIso`, the pullback along
`q : X ⟶ T ≅ T'|_T` of the class of `c` in the conormal module of `T ⊆ T'`. -/
theorem baseRingTensorSection_rangeConormalBaseElement_conormalModuleRangeSchemeBasePullbackIso_inv
    (c : closedSubspaceBaseIdeal B S hS (rangeSubspace B S hS j hj)) :
    baseRingTensorSection B S hS X (baseRingHomOfMap q) (rangeConormalBaseModule B S hS j hj)
        (rangeConormalBaseElement B S hS j hj c) ≫
        (conormalModuleRangeSchemeBasePullbackIso B S hS j hj hT' q).inv =
      modulePullbackGlobalSection B S hS (q ≫ (rangeSchemeSpaceIso B S hS j hj).hom)
        (rangeConormalSection B S hS j hj c) :=
  (baseRingTensorSection_rangeConormalBaseModule_comp B S hS j hj q _ _).trans
    (baseRingTensorSection_conormalModuleRangeSchemeBasePullbackIso_inv B S hS j hj hT' q c)

end Range

end AlgebraicGeometry.Space

end
