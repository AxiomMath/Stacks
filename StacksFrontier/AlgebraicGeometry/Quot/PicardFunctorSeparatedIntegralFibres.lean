module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModuleAdjunction
public import StacksFrontier.Algebra.Homology.DerivedCategory.StandardModelScoped
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedBaseChangeCompFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedBaseChangeComp
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeSheafHom
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedBaseChange
public import StacksFrontier.AlgebraicGeometry.Cohomology.MinimalComplexFunctoriality.FibreCycleLift
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeProper
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffinePerfectSections
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectRetract
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackOpenInCoherentStack
public import StacksFrontier.AlgebraicGeometry.Cohomology.MinimalComplexFunctoriality.GenericFibreDegreeZeroDerived
public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleMapClosedFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackTensorPowerNegOne
public import StacksFrontier.AlgebraicGeometry.Quot.PicardFunctorValuationRingGeneric
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackInertiaCoordinates
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.ProperMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescent
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.PrimeResidueFieldSite
public import StacksFrontier.AlgebraicGeometry.Quot.BaseChangeIntegralFibres
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedSeparatedValuative
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ValuativeCriteria
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact

/-!
# Separatedness of the relative Picard functor with integral geometric fibres (towards Stacks 0DNJ)

Let `f : X ⟶ B` be a flat, proper morphism of finite presentation of algebraic spaces over `S`
such that `𝒪_T ⟶ f_{T,*}𝒪_{X_T}` is an isomorphism for every scheme `T` over `B`, as in the
section "Properties of the Picard functor" of the chapter on moduli. Stacks 0DNJ says that if
moreover the geometric fibres of `f` are integral, then `Pic_{X/B} ⟶ B` is separated.

The source's proof: `Pic_{X/B} ⟶ B` is quasi-separated (Stacks 0DNI), so by Stacks 03KV it
suffices to check the uniqueness part of the valuative criterion. Over a valuation ring `R` with
fraction field `K`, after an extension of `R` a point of `Pic_{X/B}` comes from an invertible
module `L` on `X_R`, and if `L_K` is trivial then so is `L`: the perfect complexes `Rf_*L` and
`Rf_*(L^{⊗ -1})` (Stacks 0CTM), their Betti numbers (Stacks 0D1Y), Stacks 0DMY, 0DMZ and the
minimal complexes over a valuation ring (Stacks 0BCC) produce a section of `L` nonvanishing on
the closed fibre.

## Main results

* `AlgebraicGeometry.Space.isSeparated_of_isQuasiSeparated_of_valuativeUniquenessUpToExtension`:
  Stacks 03KV with the uniqueness part allowed an extension of valuation rings, for
  algebraic spaces.
* `Space.PicardSituation.isSeparated_of_isQuasiSeparated_of_hasIntegralGeometricFibres`: the
  argument of Stacks 0DNJ for an algebraic space `p : H ⟶ B` representing `Pic_{X/B}`, given
  that `p` is quasi-separated. **Not registered**: quasi-separatedness is the first half of
  Stacks 0DNI, whose source proof rests on Stacks 0DMF (Stacks 0D2D and 0DMA), and that
  `Pic_{X/B}` is an algebraic space at all is Stacks 0D2C; none of these is in this library.

## Implementation notes

The valuative part follows an earlier, unpublished argument, given here as
private declarations: the section lift over a valuation ring through Stacks 0CTM and 0BCC, the
triviality of an invertible module over a valuation ring which is trivial on the generic fibre
(through Stacks 0DMZ), and the uniqueness part of the valuative criterion, up to an extension of
the valuation ring, for any model of `Pic_{X/B}`. Instead of the immersive diagonal of Stacks
0D2D which that work assumed, the uniqueness part is fed to Stacks 03KV for algebraic spaces:
the relative diagonal then satisfies the existence part of the valuative criterion (the
extension is allowed there), so it is universally closed by Stacks 03KA, and the argument of
`AlgebraicGeometry.Space.isSeparated_of_isQuasiSeparated_of_valuativeCriterion_uniqueness`
applies.

## References

* [Stacks Project, Tag 0DNJ](https://stacks.math.columbia.edu/tag/0DNJ)
* [Stacks Project, Tag 0DNI](https://stacks.math.columbia.edu/tag/0DNI)
* [Stacks Project, Tag 03KV](https://stacks.math.columbia.edu/tag/03KV)
* [Stacks Project, Tag 0CTM](https://stacks.math.columbia.edu/tag/0CTM)
* [Stacks Project, Tag 0BCC](https://stacks.math.columbia.edu/tag/0BCC)
* [Stacks Project, Tag 0DMZ](https://stacks.math.columbia.edu/tag/0DMZ)
-/

@[expose] public noncomputable section

/-! ### Transposing the derived base change map to sections -/

section

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance 5000] SheafOfModules.instAbelian

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPushforward (derivedPushforward)

namespace AlgebraicGeometry.Space

universe u

open scoped Stacks.StandardDerivedModel

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
  (g' : X' ⟶ X) (w : g' ≫ f = f' ≫ g)

/-- The base change map `Lg (Rf K) ⟶ Rf' (Lg' K)` of a square of adjunctions, precomposed with
`Lg u` for `u : P ⟶ Rf K`, has as transpose under `Lf' ⊣ Rf'` the comparison of the two composites
around the square followed by `Lg'` of the transpose of `u`. -/
private theorem baseChange_homEquiv_symm_map_comp_map {A B A' B' : Type*} [Category A] [Category B]
    [Category A'] [Category B'] {Lf : A ⥤ B} {Rf : B ⥤ A} {Lf' : A' ⥤ B'} {Rf' : B' ⥤ A'}
    {Lg : A ⥤ A'} {Lg' : B ⥤ B'} {Lc : A ⥤ B'} (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf')
    (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc) {P : A} {K : B} (u : P ⟶ Rf.obj K) :
    (adjf'.homEquiv (Lg.obj P) (Lg'.obj K)).symm
        (Lg.map u ≫ Stacks.CategoryTheory.BaseChange.map adjf adjf' eg ef K) =
      eg.hom.app P ≫ ef.inv.app P ≫ Lg'.map ((adjf.homEquiv P K).symm u) := by
  rw [Adjunction.homEquiv_naturality_left_symm, Stacks.CategoryTheory.BaseChange.homEquiv_symm_map,
    Adjunction.homEquiv_counit, Functor.map_comp]
  have h1 := eg.hom.naturality u
  have h2 := ef.inv.naturality u
  simp only [Functor.comp_map] at h1 h2
  rw [← Category.assoc, ← Category.assoc, h1]
  simp only [Category.assoc]
  rw [← reassoc_of% h2]

/-- **The base change map on transposes.** For a map `u : P ⟶ Rf_* K`, the transpose under
`L(f')^* ⊣ Rf'_*` of `Lg^* u` followed by the base change map
`Lg^* Rf_* K ⟶ Rf'_* L(g')^* K` is `L(g')^*` of the transpose `Lf^* P ⟶ K` of `u`, preceded by
the identification `L(f')^* Lg^* P ≅ L(g')^* Lf^* P` of the two iterated derived pullbacks. -/
private theorem smallEtaleDerivedModuleBaseChangeMap_transpose
    {P : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))}
    {K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
    (u : P ⟶ (derivedPushforward (X := smallEtaleRingedTopos B S hS _)
      (Y := smallEtaleRingedTopos B S hS _) (smallEtaleRingedToposHom B S hS f)).obj K) :
    ((smallEtaleDerivedModuleAdjunction B S hS f').homEquiv _ _).symm
        ((smallEtaleDerivedModulePullback B S hS g).map u ≫
          smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' w K) =
      (smallEtaleDerivedModulePullbackCompIso B S hS f' g).hom.app P ≫
        (smallEtaleDerivedModulePullbackSquareIso B S hS f g f' g' w).inv.app P ≫
        (smallEtaleDerivedModulePullback B S hS g').map
          (((smallEtaleDerivedModuleAdjunction B S hS f).homEquiv _ _).symm u) :=
  baseChange_homEquiv_symm_map_comp_map
    (smallEtaleDerivedModuleAdjunction B S hS f) (smallEtaleDerivedModuleAdjunction B S hS f')
    (smallEtaleDerivedModulePullbackCompIso B S hS f' g)
    (smallEtaleDerivedModulePullbackSquareIso B S hS f g f' g' w) u

end AlgebraicGeometry.Space

end

/-! ### Sections of a derived pushforward and their base change -/

section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPushforward (derivedPushforward)

namespace AlgebraicGeometry.Space

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance 5000] SheafOfModules.instAbelian
open scoped Stacks.StandardDerivedModel

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
  (g' : X' ⟶ X) (w : g' ≫ f = f' ≫ g)

/-- The complex `L[0]` of an `𝒪_X`-module. -/
private abbrev singleComplex (L : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) :
    CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ :=
  (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj L

/-- **The section attached to a map `𝒪_Y[0] ⟶ Rf_*L`**: its transpose `Lf^*𝒪_Y[0] ⟶ L[0]`, read
through `Lf^*𝒪_Y[0] ≅ 𝒪_X[0]` and the full faithfulness of `[0]`. -/
private def sectionOfUnitMap (L : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
    (u : (DerivedCategory.singleFunctor _ 0).obj
        (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS Y)) ⟶
      (derivedPushforward (X := smallEtaleRingedTopos B S hS _)
        (Y := smallEtaleRingedTopos B S hS _) (smallEtaleRingedToposHom B S hS f)).obj
        (DerivedCategory.Q.obj (singleComplex B S hS L))) :
    SheafOfModules.unit (ringedToposStructureRingSheaf B S hS X) ⟶ L :=
  (DerivedCategory.singleFunctor _ 0).preimage
    ((smallEtaleDerivedModulePullbackUnitIso f).inv ≫
      ((smallEtaleDerivedModuleAdjunction B S hS f).homEquiv _ _).symm u)

/-- The transpose of `u` is `Lf^*𝒪_Y[0] ≅ 𝒪_X[0]` followed by `s[0]`. -/
private theorem homEquiv_symm_eq_sectionOfUnitMap
    (L : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
    (u : (DerivedCategory.singleFunctor _ 0).obj
        (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS Y)) ⟶
      (derivedPushforward (X := smallEtaleRingedTopos B S hS _)
        (Y := smallEtaleRingedTopos B S hS _) (smallEtaleRingedToposHom B S hS f)).obj
        (DerivedCategory.Q.obj (singleComplex B S hS L))) :
    ((smallEtaleDerivedModuleAdjunction B S hS f).homEquiv _ _).symm u =
      (smallEtaleDerivedModulePullbackUnitIso f).hom ≫
        (DerivedCategory.singleFunctor _ 0).map (sectionOfUnitMap B S hS f L u) := by
  rw [sectionOfUnitMap, Functor.map_preimage, Iso.hom_inv_id_assoc]
  rfl

/-- A functor applied degreewise to the complex map `s[0]` vanishes once it kills `s`. -/
private theorem mapHomologicalComplex_map_single_eq_zero {C D : Type*} [Category C] [Category D]
    [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroObject C] [HasZeroObject D] (F : C ⥤ D)
    [F.PreservesZeroMorphisms]
    {M N : C} (s : M ⟶ N) (hs : F.map s = 0) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).map
      ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).map s) = 0 := by
  ext i
  simp only [Functor.mapHomologicalComplex_map_f, HomologicalComplex.zero_f]
  by_cases hi : i = 0
  · subst hi
    rw [HomologicalComplex.single_map_f_self, F.map_comp, F.map_comp, hs, zero_comp, comp_zero]
  · exact (F.map_isZero (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi)).eq_of_src _ _

/-- If `a ≫ b = 0`, then `P ≫ Q.map a ≫ Q.map b = 0`. -/
private theorem comp_map_comp_map_eq_zero {D E : Type*} [Category D] [Category E]
    [HasZeroMorphisms D] [HasZeroMorphisms E] (Q : D ⥤ E) [Q.PreservesZeroMorphisms]
    {A : E} {b₁ b₂ c : D} (P : A ⟶ Q.obj b₁) (a : b₁ ⟶ b₂) (b : b₂ ⟶ c) (h : a ≫ b = 0) :
    P ≫ Q.map a ≫ Q.map b = 0 := by
  rw [← Q.map_comp, h, Q.map_zero, comp_zero]

/-- If `F.map d ≫ q = 0`, then `(a ≫ b ≫ F.map (c ≫ d)) ≫ q = 0`. -/
private theorem comp_comp_map_comp_eq_zero {C D : Type*} [Category C] [Category D]
    [HasZeroMorphisms D] (F : C ⥤ D) {P₀ P₁ : D} {c₀ c₁ c₂ : C} {Z : D} (a : P₀ ⟶ P₁)
    (b : P₁ ⟶ F.obj c₀) (c : c₀ ⟶ c₁) (d : c₁ ⟶ c₂) (q : F.obj c₂ ⟶ Z) (h : F.map d ≫ q = 0) :
    (a ≫ b ≫ F.map (c ≫ d)) ≫ q = 0 := by
  rw [F.map_comp, Category.assoc, Category.assoc, Category.assoc, h, comp_zero, comp_zero,
    comp_zero]

/-- Under an adjunction whose left adjoint preserves zero morphisms, the transpose of `0` is
`0`. -/
private theorem homEquiv_symm_zero {C D : Type*} [Category C] [Category D] [HasZeroMorphisms C]
    [HasZeroMorphisms D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [L.PreservesZeroMorphisms]
    (X : C) (Y : D) : (adj.homEquiv X Y).symm 0 = 0 := by
  rw [Adjunction.homEquiv_counit, L.map_zero, zero_comp]

/-- If `(g')^*s = 0` for a map of modules `s : M ⟶ L`, then `L(g')^*` of `s[0]` followed by the
comparison `L(g')^*(L[0]) ⟶ (g')^*(L[0])` vanishes. -/
private theorem pullback_map_single_comp_QComparison_eq_zero
    {M L : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)} (s : M ⟶ L)
    (hs : (modulePullback B S hS g').map s = 0) :
    (smallEtaleDerivedModulePullback B S hS g').map ((DerivedCategory.singleFunctor _ 0).map s) ≫
      smallEtaleDerivedModulePullbackQComparison g' (singleComplex B S hS L) = 0 := by
  have hnat := smallEtaleDerivedPullbackQComparison_naturality B S hS g'
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map s)
  show (smallEtaleDerivedModulePullback B S hS g').map (DerivedCategory.Q.map
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map s)) ≫
    smallEtaleDerivedPullbackQComparison g' _ ≫ _ = 0
  let F := Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
    (X := smallEtaleRingedTopos B S hS X') (Y := smallEtaleRingedTopos B S hS X)
    (smallEtaleRingedToposHom B S hS g').toModulesHom
  let G' : type_of% F := modulePullback B S hS g'
  have : G'.Additive := modulePullback_additive g'
  rw [reassoc_of% hnat]
  refine comp_map_comp_map_eq_zero DerivedCategory.Q _ _ _ ?_
  refine (NatTrans.naturality _ _).trans ?_
  exact (congrArg (_ ≫ ·) (mapHomologicalComplex_map_single_eq_zero G' s hs)).trans comp_zero

/-- The transpose under `L(f')^* ⊣ Rf'_*` of `Lg^*u` followed by the base change map and
`Rf'_*φ` is `L(g')^*` of the transpose of `u`, preceded by the identification of the iterated
derived pullbacks and followed by `φ`. -/
private theorem homEquiv_symm_map_comp_baseChangeComp
    {P : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))}
    {K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
    {K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X'))}
    (u : P ⟶ (derivedPushforward (X := smallEtaleRingedTopos B S hS _)
      (Y := smallEtaleRingedTopos B S hS _) (smallEtaleRingedToposHom B S hS f)).obj K)
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj K ⟶ K') :
    ((smallEtaleDerivedModuleAdjunction B S hS f').homEquiv _ _).symm
        ((smallEtaleDerivedModulePullback B S hS g).map u ≫
          smallEtaleDerivedBaseChangeComp B S hS f g f' g' w K K' φ) =
      ((smallEtaleDerivedModulePullbackCompIso B S hS f' g).hom.app P ≫
        (smallEtaleDerivedModulePullbackSquareIso B S hS f g f' g' w).inv.app P ≫
        (smallEtaleDerivedModulePullback B S hS g').map
          (((smallEtaleDerivedModuleAdjunction B S hS f).homEquiv _ _).symm u)) ≫ φ := by
  rw [smallEtaleDerivedBaseChangeComp, ← Category.assoc,
    Adjunction.homEquiv_naturality_right_symm, smallEtaleDerivedModuleBaseChangeMap_transpose]

/-- **A section with nonzero base change.** If `Lg^*u` followed by the base change map
`Lg^* Rf_* L ⟶ Rf'_*((g')^*L)` of Stacks 0CTM is nonzero, the pullback along `g'` of the section
attached to `u` is nonzero: that composite is the transpose of the section `(g')^*s`, up to
isomorphisms on the source. -/
private theorem modulePullback_map_sectionOfUnitMap_ne_zero
    (L : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
    (u : (DerivedCategory.singleFunctor _ 0).obj
        (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS Y)) ⟶
      (derivedPushforward (X := smallEtaleRingedTopos B S hS _)
        (Y := smallEtaleRingedTopos B S hS _) (smallEtaleRingedToposHom B S hS f)).obj
        (DerivedCategory.Q.obj (singleComplex B S hS L)))
    (hu : (smallEtaleDerivedModulePullback B S hS g).map u ≫
        smallEtaleDerivedBaseChangeComp B S hS f g f' g' w _ _
          (smallEtaleDerivedModulePullbackQComparison g' (singleComplex B S hS L)) ≠ 0) :
    (modulePullback B S hS g').map (sectionOfUnitMap B S hS f L u) ≠ 0 := by
  have := (smallEtaleDerivedModuleAdjunction B S hS f').isLeftAdjoint
  have : (smallEtaleDerivedModulePullback B S hS f').PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  intro hs
  apply hu
  apply ((smallEtaleDerivedModuleAdjunction B S hS f').homEquiv _ _).symm.injective
  rw [homEquiv_symm_map_comp_baseChangeComp, homEquiv_symm_eq_sectionOfUnitMap, homEquiv_symm_zero]
  exact comp_comp_map_comp_eq_zero _ _ _ _ _ _
    (pullback_map_single_comp_QComparison_eq_zero B S hS g' (sectionOfUnitMap B S hS f L u) hs)

/-- **A nonzero section after base change gives a nonzero map into `Lg^* Rf_* L`.** If the base
change map of Stacks 0CTM at `L` is invertible and `(g')^*L` has a nonzero section, then there is
a nonzero map `𝒪_{Y'}[0] ⟶ Lg^* Rf_* L`: the transpose of the section, read through the inverse
of the base change map. -/
private theorem exists_unit_map_pullback_ne_zero_of_section
    (L : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
    (hBC : IsIso (smallEtaleDerivedBaseChangeComp B S hS f g f' g' w _ _
      (smallEtaleDerivedModulePullbackQComparison g' (singleComplex B S hS L))))
    (σ : SheafOfModules.unit (ringedToposStructureRingSheaf B S hS X') ⟶
      (show SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X') from
        (modulePullback B S hS g').obj L)) (hσ : σ ≠ 0) :
    ∃ v : (DerivedCategory.singleFunctor _ 0).obj
        (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS Y')) ⟶
      (smallEtaleDerivedModulePullback B S hS g).obj
        ((derivedPushforward (X := smallEtaleRingedTopos B S hS _)
          (Y := smallEtaleRingedTopos B S hS _) (smallEtaleRingedToposHom B S hS f)).obj
          (DerivedCategory.Q.obj (singleComplex B S hS L))), v ≠ 0 := by
  have := (smallEtaleDerivedModuleAdjunction B S hS f').isLeftAdjoint
  have : (smallEtaleDerivedModulePullback B S hS f').PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  let F : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X) ⥤
      SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X') := modulePullback B S hS g'
  have : F.PreservesZeroMorphisms := by
    have : (modulePullback B S hS g').Additive := modulePullback_additive g'
    exact inferInstanceAs (modulePullback B S hS g').PreservesZeroMorphisms
  let e : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (singleComplex B S hS L) ≅
      (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (F.obj L) :=
    (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).app L
  let K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X')) :=
    DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (singleComplex B S hS L))
  let t : (smallEtaleDerivedModulePullback B S hS f').obj ((DerivedCategory.singleFunctor _ 0).obj
        (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS Y'))) ⟶ K' :=
    (smallEtaleDerivedModulePullbackUnitIso f').hom ≫
      (DerivedCategory.singleFunctor _ 0).map σ ≫ DerivedCategory.Q.map e.inv
  let β := smallEtaleDerivedBaseChangeComp B S hS f g f' g' w _ _
      (smallEtaleDerivedModulePullbackQComparison g' (singleComplex B S hS L))
  refine ⟨((smallEtaleDerivedModuleAdjunction B S hS f').homEquiv _ K' t) ≫ @inv _ _ _ _ β hBC,
    fun h0 => hσ ?_⟩
  have h1 : (smallEtaleDerivedModuleAdjunction B S hS f').homEquiv _ K' t = 0 :=
    @zero_of_comp_mono _ _ _ _ _ _ (@inv _ _ _ _ β hBC) _
      (@IsIso.mono_of_iso _ _ _ _ _ (@IsIso.inv_isIso _ _ _ _ _ hBC)) h0
  have h2 : t = 0 := by
    have := congrArg ((smallEtaleDerivedModuleAdjunction B S hS f').homEquiv _ K').symm h1
    rw [Equiv.symm_apply_apply] at this
    rw [this, Adjunction.homEquiv_counit, Functor.map_zero, zero_comp]
  have h4 : (DerivedCategory.singleFunctor _ 0).map σ = 0 :=
    (Preadditive.IsIso.comp_right_eq_zero _ (DerivedCategory.Q.map e.inv)).1
      ((Preadditive.IsIso.comp_left_eq_zero (smallEtaleDerivedModulePullbackUnitIso f').hom _).1 h2)
  exact (DerivedCategory.singleFunctor _ 0).map_injective (h4.trans (Functor.map_zero _ _ _).symm)

end AlgebraicGeometry.Space

end

/-! ### Unit maps over an affine scheme -/

section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance 5000] SheafOfModules.instAbelian
open scoped Stacks.StandardDerivedModel
attribute [local instance] hasProductsOfShape_nat_modules_ringUniverse

open StacksDraft.Perfect.FibreCycleLift (unitComplex)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- If a functor kills a map conjugated by two isomorphisms, it kills the map. -/
private theorem map_eq_zero_of_map_conj_eq_zero {C D : Type*} [Category C] [Category D]
    [HasZeroMorphisms D] (F : C ⥤ D) {X Y Z W : C} (e₁ : Y ≅ X) (f : Y ⟶ Z) (e₂ : Z ≅ W)
    (h : F.map (e₁.inv ≫ f ≫ e₂.hom) = 0) : F.map f = 0 := by
  rw [F.map_comp, F.map_comp] at h
  exact zero_of_comp_mono _ (zero_of_epi_comp _ h)

section Unit

variable (U : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]

/-- `Φ(R[0]) ≅ 𝒪[0]`, read on the unit complex. -/
private abbrev representedAffineUnitComplexIso :
    (representedAffineDerivedAssociated B S hS U).obj
        (DerivedCategory.Q.obj (unitComplex Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        (structureModule (schemeSpace U)) :=
  representedAffineDerivedAssociatedSingleUnitIso B S hS U 0

/-- **The map `𝒪[0] ⟶ E` attached to `y : R[0] ⟶ RΓ(E)`**: `Φ(y)` followed by the counit
`Φ(RΓ(E)) ⟶ E`. -/
private def representedAffineUnitMap
    (E : DerivedCategory (Modules.{u, u} B S hS (schemeSpace U).1 (schemeSpace U).2))
    (y : DerivedCategory.Q.obj (unitComplex Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ⟶
      (representedAffineDerivedSections B S hS U).obj E) :
    (DerivedCategory.singleFunctor _ 0).obj
        (structureModule (schemeSpace U)) ⟶ E :=
  (representedAffineUnitComplexIso B S hS U).inv ≫
    (representedAffineDerivedAssociated B S hS U).map y ≫
      (representedAffineDerivedAdjunction B S hS U).counit.app E

end Unit

section BaseChange

variable {U' U : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U')] (g : U' ⟶ U)

/-- **A map out of the unit with nonzero derived fibre stays nonzero after pullback.** If
`y : R[0] ⟶ RΓ(E)` has nonzero derived extension of scalars along `R ⟶ R'`, then the derived
pullback along `g` of the attached map `𝒪[0] ⟶ E` is nonzero: by affine base change it is
`Φ_{R'}` of the extension of scalars of `y` up to isomorphisms, and `Φ_{R'}` is faithful. -/
private theorem representedAffineUnitMap_pullback_ne_zero
    (E : DerivedCategory (Modules.{u, u} B S hS (schemeSpace U).1 (schemeSpace U).2))
    (hE : QcohDerived B S hS (schemeSpace U) E)
    (y : DerivedCategory.Q.obj (unitComplex Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ⟶
      (representedAffineDerivedSections B S hS U).obj E)
    (hy : (representedAffineDerivedExtension B S hS g).functor.map y ≠ 0) :
    (smallEtaleDerivedModulePullback B S hS (schemeSpaceMap g)).map
      (representedAffineUnitMap B S hS U E y) ≠ 0 := by
  have hc := isIso_representedAffineDerivedAdjunction_counit_app B S hS U E hE
  intro h0
  apply hy
  let Lg := smallEtaleDerivedModulePullback B S hS (schemeSpaceMap g)
  have hΦ : Lg.map ((representedAffineDerivedAssociated B S hS U).map y) = 0 :=
    map_eq_zero_of_map_conj_eq_zero Lg (representedAffineUnitComplexIso B S hS U) _
      (@asIso _ _ _ _ ((representedAffineDerivedAdjunction B S hS U).counit.app E) hc) h0
  have hnat : Lg.map ((representedAffineDerivedAssociated B S hS U).map y) ≫
      (representedAffineDerivedBaseChangeIso B S hS g).hom.app _ =
      (representedAffineDerivedBaseChangeIso B S hS g).hom.app _ ≫
        (representedAffineDerivedAssociated B S hS U').map
          ((representedAffineDerivedExtension B S hS g).functor.map y) :=
    (representedAffineDerivedBaseChangeIso B S hS g).hom.naturality y
  have hnat' := hnat.symm.trans ((congrArg (· ≫ _) hΦ).trans zero_comp)
  have h2 : (representedAffineDerivedAssociated B S hS U').map
      ((representedAffineDerivedExtension B S hS g).functor.map y) = 0 :=
    zero_of_epi_comp ((representedAffineDerivedBaseChangeIso B S hS g).hom.app _) hnat'
  exact (representedAffineDerivedAssociatedFullyFaithful B S hS U').map_injective
    (h2.trans (Functor.map_zero _ _ _).symm)

/-- **A nonzero map out of the unit after pullback gives a nonzero map of derived fibres.** A
nonzero map `𝒪_{U'}[0] ⟶ Lg^*E` gives a nonzero map `R'[0] ⟶ RΓ(E) ⊗ᴸ_R R'`: affine base change
identifies `Lg^*E` with `Φ_{R'}(RΓ(E) ⊗ᴸ_R R')`, and `Φ_{R'}` is bijective on maps out of
`R'[0]`. -/
private theorem exists_unit_map_ne_zero_of_pullback
    (E : DerivedCategory (Modules.{u, u} B S hS (schemeSpace U).1 (schemeSpace U).2))
    (hE : QcohDerived B S hS (schemeSpace U) E)
    (w : (DerivedCategory.singleFunctor (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
          (schemeSpace U'))) 0).obj (SheafOfModules.unit _) ⟶
      (smallEtaleDerivedModulePullback B S hS (schemeSpaceMap g)).obj E)
    (hw : w ≠ 0) :
    ∃ y : DerivedCategory.Q.obj (unitComplex Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)) ⟶
      (representedAffineDerivedExtension B S hS g).functor.obj
        ((representedAffineDerivedSections B S hS U).obj E), y ≠ 0 := by
  have hc := isIso_representedAffineDerivedAdjunction_counit_app B S hS U E hE
  let ε : (smallEtaleDerivedModulePullback B S hS (schemeSpaceMap g)).obj E ≅
      (representedAffineDerivedAssociated B S hS U').obj
        ((representedAffineDerivedExtension B S hS g).functor.obj
          ((representedAffineDerivedSections B S hS U).obj E)) :=
    (smallEtaleDerivedModulePullback B S hS (schemeSpaceMap g)).mapIso
        (@asIso _ _ _ _ ((representedAffineDerivedAdjunction B S hS U).counit.app E) hc).symm ≪≫
      (representedAffineDerivedBaseChangeIso B S hS g).app _
  obtain ⟨y, hy⟩ := (bijective_representedAffineDerivedAssociated_map_single B S hS U' 0
    ((representedAffineDerivedExtension B S hS g).functor.obj
      ((representedAffineDerivedSections B S hS U).obj E))).2
    ((representedAffineDerivedAssociatedSingleUnitIso B S hS U' 0).hom ≫ w ≫ ε.hom)
  refine ⟨y, fun h0 => hw ?_⟩
  have hy' : (representedAffineDerivedAssociated B S hS U').map y = _ := hy
  rw [h0, Functor.map_zero] at hy'
  exact @zero_of_comp_mono _ _ _ _ _ _ ε.hom _ (@IsIso.mono_of_iso _ _ _ _ _ ε.isIso_hom)
    (zero_of_epi_comp (representedAffineDerivedAssociatedSingleUnitIso B S hS U' 0).hom hy'.symm)

end BaseChange

end AlgebraicGeometry.Space

end

/-! ### The section lift over a valuation ring (Stacks 0CTM, 0BCC) -/

section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPushforward (derivedPushforward)
open StacksDraft.Perfect.FibreCycleLift (unitComplex)

namespace AlgebraicGeometry.Space

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance 5000] SheafOfModules.instAbelian
open scoped Stacks.StandardDerivedModel
attribute [local instance] hasProductsOfShape_nat_modules_ringUniverse

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A global section not vanishing on the closed fibre**, over an affine base whose ring is a
valuation ring. See the module documentation. -/
private theorem exists_section_modulePullback_ne_zero_of_valuationRing
    {U Uκ UK : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Uκ)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj UK)]
    [IsDomain Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)]
    [ValuationRing Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)]
    (gκ : Uκ ⟶ U) (gK : UK ⟶ U)
    (hκ : IsField Γ((BigFppfOver.toScheme B S hS).obj Uκ, ⊤))
    (hK : IsField Γ((BigFppfOver.toScheme B S hS).obj UK, ⊤))
    (hχ : IsLocalHom (representedAffineCommRingCatHom B S hS gκ).hom)
    (hι : Function.Injective (representedAffineCommRingCatHom B S hS gK).hom)
    (hfrac : ∀ k : Γ((BigFppfOver.toScheme B S hS).obj UK, ⊤), ∃ a c,
      (representedAffineCommRingCatHom B S hS gK).hom c ≠ 0 ∧
        k * (representedAffineCommRingCatHom B S hS gK).hom c =
          (representedAffineCommRingCatHom B S hS gK).hom a)
    {X Xκ XK : AlgebraicSpaces B S hS}
    (f : X ⟶ schemeSpace U)
    (hfp : IsProper B S hS f.hom) (hfl : IsFlat B S hS f.hom)
    (hf : IsFinitePresentation B S hS f.hom)
    (fκ : Xκ ⟶ schemeSpace Uκ) (jκ : Xκ ⟶ X)
    (sqκ : IsPullback jκ fκ f (schemeSpaceMap gκ))
    (fK : XK ⟶ schemeSpace UK) (jK : XK ⟶ X)
    (sqK : IsPullback jK fK f (schemeSpaceMap gK))
    (L : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
    (hL : IsInvertibleModule X L)
    (σ : SheafOfModules.unit (ringedToposStructureRingSheaf B S hS XK) ⟶
      (show SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS XK) from
        (modulePullback B S hS jK).obj L)) (hσ : σ ≠ 0) :
    ∃ s : SheafOfModules.unit (ringedToposStructureRingSheaf B S hS X) ⟶ L,
      (modulePullback B S hS jκ).map s ≠ 0 := by
  let := hκ.toField
  let := hK.toField
  -- Stacks 0CTM
  have hLfp := Stacks.SheafOfModules.isFinitePresentation_of_isInvertible _ L hL
  have hLfl := isFlatOver_of_isInvertibleModule f L hfl hL
  obtain ⟨hP, hBC⟩ :=
    isPerfect_derivedModulePushforward_single_and_isIso_baseChange f hfp hf L hLfp hLfl
  set E := (derivedPushforward (X := smallEtaleRingedTopos B S hS _)
    (Y := smallEtaleRingedTopos B S hS _) (smallEtaleRingedToposHom B S hS f)).obj
      (DerivedCategory.Q.obj (singleComplex B S hS L)) with hEdef
  have hE : QcohDerived B S hS (schemeSpace U) E :=
    qcohDerived_of_isPerfect_derivedCategoryB _ E hP
  -- the derived sections are pseudo-coherent
  have hM := StacksDraft.Perfect.isPseudoCoherent_of_isPerfect.{u, u} _
    (isPerfect_representedAffineDerivedSections_obj B S hS U E hP)
  -- the generic class
  obtain ⟨w, hw⟩ := exists_unit_map_pullback_ne_zero_of_section B S hS f
    (schemeSpaceMap gK) fK jK sqK.w L (hBC _ _ _ sqK) σ hσ
  obtain ⟨yK, hyK⟩ := exists_unit_map_ne_zero_of_pullback B S hS gK E hE w hw
  -- the lift over the valuation ring
  obtain ⟨y, hy⟩ := StacksDraft.Perfect.FibreCycleLift.exists_unit_map_ne_zero_of_valuationRing
    (representedAffineDerivedExtension B S hS gκ) hι hfrac
    (representedAffineDerivedExtension B S hS gK) _ hM ⟨yK, hyK⟩
  -- back to a section
  have hu := representedAffineUnitMap_pullback_ne_zero B S hS gκ E hE y hy
  refine ⟨sectionOfUnitMap B S hS f L (representedAffineUnitMap B S hS U E y), ?_⟩
  exact modulePullback_map_sectionOfUnitMap_ne_zero B S hS f (schemeSpaceMap gκ) fκ jκ
    sqκ.w L _ fun h0 => hu
      (@zero_of_comp_mono _ _ _ _ _ _ _ _ (@IsIso.mono_of_iso _ _ _ _ _ (hBC _ _ _ sqκ)) h0)

end AlgebraicGeometry.Space

end

/-! ### Invertible modules over a valuation ring trivial on the generic fibre (Stacks 0DMZ) -/

section

open CategoryTheory CategoryTheory.Limits
open Stacks.SheafOfModules.TensorPower (tensorPower)

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The ring homomorphism of global functions of a morphism of spectra in the site, read through
the identifications `Γ(Spec R, ⊤) ≅ R`. -/
private theorem representedAffineCommRingCatHom_specSiteObjectMap_apply {R C : Type u} [CommRing R]
    [CommRing C] (θ : R →+* C) (hR : B.Contains (Spec (.of R))) (hC : B.Contains (Spec (.of C)))
    (a : Spec (.of R) ⟶ S) (x : Γ(Spec (.of R), ⊤)) :
    (representedAffineCommRingCatHom B S hS (specSiteObjectMap θ hR hC a)).hom x =
      (Scheme.ΓSpecIso (.of C)).inv (θ ((Scheme.ΓSpecIso (.of R)).hom x)) := by
  have h := (Iso.eq_comp_inv _).2 (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom θ))
  exact congrArg (fun φ => φ.hom x) h

/-- The ring of global functions of the spectrum of a ring, as a ring isomorphic to it. -/
private abbrev gammaSpecRingEquiv (R : Type u) [CommRing R] : Γ(Spec (.of R), ⊤) ≃+* R :=
  (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv

/-- **The section lift over the spectrum of a valuation ring.** Let `R` be a valuation ring with
fraction field `K`, `f : X ⟶ Spec R` proper, flat and of finite presentation, and `X_κ`, `X_K`
the closed and generic fibres. An invertible `𝒪_X`-module `L` whose restriction to `X_K` has a
nonzero section has a global section whose restriction to `X_κ` is nonzero. -/
private theorem exists_section_modulePullback_ne_zero_of_valuationRing_spec
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (ring_mem : B.Contains (Spec (.of R)))
    (res_mem : B.Contains (Spec (.of (IsLocalRing.ResidueField R))))
    (field_mem : B.Contains (Spec (.of K))) (base : Spec (.of R) ⟶ S)
    {X X₀ XK : AlgebraicSpaces B S hS}
    (f : X ⟶ (schemeSpaceFunctor B S hS).obj (siteObject B S hS ring_mem base))
    (hfp : IsProper B S hS f.hom) (hfl : IsFlat B S hS f.hom)
    (hf : IsFinitePresentation B S hS f.hom)
    (f₀ : X₀ ⟶ (schemeSpaceFunctor B S hS).obj (siteObject B S hS res_mem
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) ≫ base)))
    (j₀ : X₀ ⟶ X)
    (sq₀ : IsPullback j₀ f₀ f ((schemeSpaceFunctor B S hS).map
      (specSiteObjectMap (IsLocalRing.residue R) ring_mem res_mem base)))
    (fK : XK ⟶ (schemeSpaceFunctor B S hS).obj (siteObject B S hS field_mem
      (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ base)))
    (jK : XK ⟶ X)
    (sqK : IsPullback jK fK f ((schemeSpaceFunctor B S hS).map
      (specSiteObjectMap (algebraMap R K) ring_mem field_mem base)))
    (L : Modules.{u, u} B S hS X.1 X.2) (hL : IsInvertibleModule X L)
    (σ : structureModule XK ⟶ (modulePullback B S hS jK).obj L) (hσ : σ ≠ 0) :
    ∃ s : structureModule X ⟶ L, (modulePullback B S hS j₀).map s ≠ 0 := by
  let eR := gammaSpecRingEquiv R
  let eκ := gammaSpecRingEquiv (IsLocalRing.ResidueField R)
  let eK := gammaSpecRingEquiv K
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (siteObject B S hS ring_mem base)) :=
    inferInstanceAs (IsAffine (Spec _))
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (siteObject B S hS res_mem
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) ≫ base))) :=
    inferInstanceAs (IsAffine (Spec _))
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (siteObject B S hS field_mem
      (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ base))) :=
    inferInstanceAs (IsAffine (Spec _))
  have hdom : IsDomain Γ((BigFppfOver.toScheme B S hS).obj (siteObject B S hS ring_mem base), ⊤) :=
    Function.Injective.isDomain eR.toRingHom eR.injective
  have : ValuationRing
      Γ((BigFppfOver.toScheme B S hS).obj (siteObject B S hS ring_mem base), ⊤) := by
    refine ValuationRing.iff_dvd_total.mpr ⟨fun a b => ?_⟩
    rcases (ValuationRing.iff_dvd_total.mp (inferInstance : ValuationRing R)).total (eR a)
      (eR b) with h | h
    · left
      simpa using map_dvd eR.symm.toRingHom h
    · right
      simpa using map_dvd eR.symm.toRingHom h
  have hκ : IsField Γ((BigFppfOver.toScheme B S hS).obj (siteObject B S hS res_mem
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) ≫ base)), ⊤) :=
    MulEquiv.isField (Field.toIsField _) eκ.toMulEquiv
  have hK : IsField Γ((BigFppfOver.toScheme B S hS).obj (siteObject B S hS field_mem
      (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ base)), ⊤) :=
    MulEquiv.isField (Field.toIsField _) eK.toMulEquiv
  have hκapp := representedAffineCommRingCatHom_specSiteObjectMap_apply (hS := hS)
    (IsLocalRing.residue R) ring_mem res_mem base
  have hKapp := representedAffineCommRingCatHom_specSiteObjectMap_apply (hS := hS)
    (algebraMap R K) ring_mem field_mem base
  have hKapp' : ∀ x, (representedAffineCommRingCatHom B S hS
      (specSiteObjectMap (algebraMap R K) ring_mem field_mem base)).hom x =
        eK.symm (algebraMap R K (eR x)) := fun x => hKapp x
  have hχ : IsLocalHom (representedAffineCommRingCatHom B S hS
      (specSiteObjectMap (IsLocalRing.residue R) ring_mem res_mem base)).hom := by
    have : (representedAffineCommRingCatHom B S hS
        (specSiteObjectMap (IsLocalRing.residue R) ring_mem res_mem base)).hom =
        (eκ.symm.toRingHom.comp (IsLocalRing.residue R)).comp eR.toRingHom := by
      ext x
      exact hκapp x
    rw [this]
    refine ⟨fun z hz => ?_⟩
    have h1 : IsUnit (IsLocalRing.residue R (eR z)) := by
      simpa using hz.map eκ.toRingHom
    have h2 : IsUnit (eR z) := IsUnit.of_map (IsLocalRing.residue R) _ h1
    simpa using h2.map eR.symm.toRingHom
  have hι : Function.Injective (representedAffineCommRingCatHom B S hS
      (specSiteObjectMap (algebraMap R K) ring_mem field_mem base)).hom := by
    intro x y hxy
    rw [hKapp', hKapp'] at hxy
    exact eR.injective (IsFractionRing.injective R K (eK.symm.injective hxy))
  have hfrac : ∀ k : Γ((BigFppfOver.toScheme B S hS).obj (siteObject B S hS field_mem
      (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ base)), ⊤), ∃ a c,
      (representedAffineCommRingCatHom B S hS
        (specSiteObjectMap (algebraMap R K) ring_mem field_mem base)).hom c ≠ 0 ∧
        k * (representedAffineCommRingCatHom B S hS
          (specSiteObjectMap (algebraMap R K) ring_mem field_mem base)).hom c =
          (representedAffineCommRingCatHom B S hS
            (specSiteObjectMap (algebraMap R K) ring_mem field_mem base)).hom a := by
    intro k
    obtain ⟨⟨a, c⟩, hac⟩ := IsLocalization.surj (nonZeroDivisors R) (eK k)
    refine ⟨eR.symm a, eR.symm c, ?_, ?_⟩
    · rw [hKapp', eR.apply_symm_apply]
      intro h0
      have h1 : algebraMap R K c = 0 := by
        have := congrArg eK h0
        rwa [eK.apply_symm_apply, map_zero] at this
      exact nonZeroDivisors.coe_ne_zero c
        ((IsFractionRing.injective R K) (h1.trans (map_zero _).symm))
    · rw [hKapp', hKapp', eR.apply_symm_apply, eR.apply_symm_apply]
      apply eK.injective
      rw [map_mul, eK.apply_symm_apply, eK.apply_symm_apply]
      exact hac
  exact exists_section_modulePullback_ne_zero_of_valuationRing B S hS
    (specSiteObjectMap (IsLocalRing.residue R) ring_mem res_mem base)
    (specSiteObjectMap (algebraMap R K) ring_mem field_mem base) hκ hK hχ hι hfrac f hfp hfl hf
    f₀ j₀ sq₀ fK jK sqK L hL σ hσ

/-- On an algebraic space whose global regular functions form a nonzero ring, the identity of
the structure sheaf is nonzero. -/
private theorem id_structureModule_ne_zero {Z : AlgebraicSpaces B S hS}
    (h : Nontrivial (globalFunctions B S hS Z.1)) : 𝟙 (structureModule Z) ≠ 0 := by
  intro h0
  let e := unitEndRingEquivGlobalFunctions B S hS Z.1 Z.2
  have := congrArg (fun φ => e (End.of φ)) h0
  exact one_ne_zero ((map_one e).symm.trans (this.trans (map_zero e)))

/-- **An invertible module over a valuation ring which is trivial on the generic fibre is
trivial.** See the module documentation. -/
private theorem nonempty_iso_structureModule_of_valuationRing
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (ring_mem : B.Contains (Spec (.of R)))
    (res_mem : B.Contains (Spec (.of (IsLocalRing.ResidueField R))))
    (field_mem : B.Contains (Spec (.of K))) (base : Spec (.of R) ⟶ S)
    {X X₀ XK : AlgebraicSpaces B S hS}
    (f : X ⟶ (schemeSpaceFunctor B S hS).obj (siteObject B S hS ring_mem base))
    (hfp : IsProper B S hS f.hom) (hfl : IsFlat B S hS f.hom)
    (hf : IsFinitePresentation B S hS f.hom)
    (f₀ : X₀ ⟶ (schemeSpaceFunctor B S hS).obj (siteObject B S hS res_mem
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) ≫ base)))
    (j₀ : X₀ ⟶ X)
    (sq₀ : IsPullback j₀ f₀ f ((schemeSpaceFunctor B S hS).map
      (specSiteObjectMap (IsLocalRing.residue R) ring_mem res_mem base)))
    (fK : XK ⟶ (schemeSpaceFunctor B S hS).obj (siteObject B S hS field_mem
      (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ base)))
    (jK : XK ⟶ X)
    (sqK : IsPullback jK fK f ((schemeSpaceFunctor B S hS).map
      (specSiteObjectMap (algebraMap R K) ring_mem field_mem base)))
    (hint₀ : IsIntegralSpace B S hS X₀.1) (hfield₀ : IsField (globalFunctions B S hS X₀.1))
    (hK : Nontrivial (globalFunctions B S hS XK.1))
    (L : Modules.{u, u} B S hS X.1 X.2) [hL : IsInvertibleModule X L]
    (hLK : Nonempty ((modulePullback B S hS jK).obj L ≅ structureModule XK)) :
    Nonempty (L ≅ structureModule X) := by
  have hidK := id_structureModule_ne_zero hK
  -- a section of `L` nonzero on the closed fibre
  have lift : ∀ (M : Modules.{u, u} B S hS X.1 X.2) (hM : IsInvertibleModule X M),
      Nonempty ((modulePullback B S hS jK).obj M ≅ structureModule XK) →
      ∃ s : structureModule X ⟶ M, (modulePullback B S hS j₀).map s ≠ 0 := by
    rintro M hM ⟨e⟩
    refine exists_section_modulePullback_ne_zero_of_valuationRing_spec R K ring_mem res_mem
      field_mem base f hfp hfl hf f₀ j₀ sq₀ fK jK sqK M hM e.inv fun h0 => hidK ?_
    rw [← e.inv_hom_id, h0, zero_comp]
  obtain ⟨s, hs⟩ := lift L hL hLK
  have := isEquivalence_tensorRightFunctor B S hS X.1 X.2 L
  have hLinv : IsInvertibleModule X (tensorPower (structureSheaf B S hS X.1 X.2).obj
      (structureRingPresheaf_isSheaf B S hS X.1 X.2) L (-1)) :=
    Stacks.SheafOfModules.TensorPower.isInvertible_tensorPower (structureSheaf B S hS X.1 X.2).obj
      (structureRingPresheaf_isSheaf B S hS X.1 X.2) L (-1)
  obtain ⟨t, ht⟩ := lift _ hLinv
    (nonempty_modulePullback_tensorPower_neg_one_iso_structureModule jK L hLK)
  -- the closed fibre
  have hL₀ : IsInvertibleModule X₀ ((modulePullback B S hS j₀).obj L) :=
    modulePullbackInvertible j₀ L hL
  have := isEquivalence_tensorRightFunctor B S hS X₀.1 X₀.2 ((modulePullback B S hS j₀).obj L)
  let u₀ := modulePullbackUnitIso B S hS j₀
  have comp_ne : ∀ {M M' M'' M''' : Modules.{u, u} B S hS X₀.1 X₀.2} (k : M ⟶ M') (e : M' ≅ M'')
      (e' : M''' ≅ M), k ≠ 0 → e'.hom ≫ k ≫ e.hom ≠ 0 := by
    intro _ _ _ _ k e e' hk h0
    apply hk
    have := congrArg (fun z => e'.inv ≫ z ≫ e.inv) h0
    simpa using this
  have hs₀ : u₀.inv ≫ (modulePullback B S hS j₀).map s ≠ 0 := by
    simpa using comp_ne _ (Iso.refl _) u₀.symm hs
  obtain ⟨eInv⟩ := nonempty_modulePullback_tensorPower_neg_one_iso j₀ L
  have ht₀ := comp_ne _ eInv u₀.symm ht
  have hsec := nontrivial_sections_of_ne_zero _ hs₀
  have hsecInv := nontrivial_sections_of_ne_zero _ ht₀
  obtain ⟨e₀raw⟩ := isTrivial_of_nontrivial_sections B S hS X₀.1 X₀.2 hint₀ hfield₀
    ((modulePullback B S hS j₀).obj L) hsec hsecInv
  let e₀ : ((modulePullback B S hS j₀).obj L : Modules.{u, u} B S hS X₀.1 X₀.2) ≅
      structureModule X₀ := e₀raw
  -- `s` is an isomorphism on the closed fibre
  have hiso₀ : IsIso (u₀.inv ≫ (modulePullback B S hS j₀).map s ≫ e₀.hom) :=
    isIso_of_ne_zero B S hS X₀.1 X₀.2 hfield₀ _
      (fun h => comp_ne _ e₀ u₀.symm hs (congrArg End.asHom h))
  have hiso : IsIso ((modulePullback B S hS j₀).map s) := by
    have := hiso₀
    have : IsIso ((modulePullback B S hS j₀).map s ≫ e₀.hom) :=
      IsIso.of_isIso_comp_left u₀.inv _
    exact IsIso.of_isIso_comp_right _ e₀.hom
  have : IsIso s := isIso_of_isIso_modulePullback_closedPoint R ring_mem res_mem base f
    hfp.universallyClosed f₀ j₀ (AlgebraicSpaces.isPullback_hom B S hS sq₀)
    (isInvertibleModule_structureModule X) hL s hiso
  exact ⟨(asIso s).symm⟩

/-- **Two Picard classes over a valuation ring which agree on the generic fibre agree.** -/
private theorem eq_of_picardPullback_eq_of_valuationRing
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (ring_mem : B.Contains (Spec (.of R)))
    (res_mem : B.Contains (Spec (.of (IsLocalRing.ResidueField R))))
    (field_mem : B.Contains (Spec (.of K))) (base : Spec (.of R) ⟶ S)
    {X X₀ XK : AlgebraicSpaces B S hS}
    (f : X ⟶ (schemeSpaceFunctor B S hS).obj (siteObject B S hS ring_mem base))
    (hfp : IsProper B S hS f.hom) (hfl : IsFlat B S hS f.hom)
    (hf : IsFinitePresentation B S hS f.hom)
    (f₀ : X₀ ⟶ (schemeSpaceFunctor B S hS).obj (siteObject B S hS res_mem
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) ≫ base)))
    (j₀ : X₀ ⟶ X)
    (sq₀ : IsPullback j₀ f₀ f ((schemeSpaceFunctor B S hS).map
      (specSiteObjectMap (IsLocalRing.residue R) ring_mem res_mem base)))
    (fK : XK ⟶ (schemeSpaceFunctor B S hS).obj (siteObject B S hS field_mem
      (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ base)))
    (jK : XK ⟶ X)
    (sqK : IsPullback jK fK f ((schemeSpaceFunctor B S hS).map
      (specSiteObjectMap (algebraMap R K) ring_mem field_mem base)))
    (hint₀ : IsIntegralSpace B S hS X₀.1) (hfield₀ : IsField (globalFunctions B S hS X₀.1))
    (hK : Nontrivial (globalFunctions B S hS XK.1))
    (x y : picardGroup X) (hxy : picardPullback jK x = picardPullback jK y) : x = y := by
  obtain ⟨M, hM, hMxy⟩ := exists_picardClass X (x - y)
  have h0 : picardClass XK _ (modulePullbackInvertible jK M hM) = 0 := by
    rw [← picardPullback_picardClass jK M hM, hMxy, ← picardPullbackHom_apply, map_sub,
      picardPullbackHom_apply, picardPullbackHom_apply, hxy, sub_self]
  have := hM
  obtain ⟨e⟩ := nonempty_iso_structureModule_of_valuationRing R K ring_mem res_mem field_mem base
    f hfp hfl hf f₀ j₀ sq₀ fK jK sqK hint₀ hfield₀ hK M
    ((picardClass_eq_zero_iff XK _ _).1 h0)
  rw [← sub_eq_zero, ← hMxy]
  exact (picardClass_eq_zero_iff X M hM).2 ⟨e⟩

end AlgebraicGeometry.Space

end

/-! ### The uniqueness part of the valuative criterion for a model of Pic_{X/B} -/

section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace PicardSituation

variable (s : PicardSituation B S hS)

/-- The square defining the base change `X_T`. -/
theorem isPullback_baseChange (T : s.SchemesOver) :
    IsPullback (baseChangeProjection s.f T) (baseChangeInclusion s.f T) s.f T.hom :=
  AlgebraicSpaces.isPullback_fiberProduct B S hS s.f T.hom

/-- The projection `X_T ⟶ T` of a proper morphism is proper. -/
theorem isProper_baseChangeInclusion (h : IsProper B S hS s.f.hom) (T : s.SchemesOver) :
    IsProper B S hS (baseChangeInclusion s.f T).hom :=
  isProper_of_isPullback' (s.baseChange T).2 s.X.2 ((schemeSpaceFunctor B S hS).obj T.left).2
    s.base.2 (AlgebraicSpaces.isPullback_hom B S hS (s.isPullback_baseChange T)) h

/-- The projection `X_T ⟶ T` of a morphism of finite presentation is of finite presentation. -/
theorem isFinitePresentation_baseChangeInclusion (h : IsFinitePresentation B S hS s.f.hom)
    (T : s.SchemesOver) : IsFinitePresentation B S hS (baseChangeInclusion s.f T).hom :=
  isFinitePresentation_of_isPullback B S hS (s.baseChange T).2 s.X.2
    ((schemeSpaceFunctor B S hS).obj T.left).2 s.base.2
    (AlgebraicSpaces.isPullback_hom B S hS (s.isPullback_baseChange T)) h

/-- The projection `X_T ⟶ T` of a flat morphism is flat. -/
theorem isFlat_baseChangeInclusion (h : IsFlat B S hS s.f.hom) (T : s.SchemesOver) :
    IsFlat B S hS (baseChangeInclusion s.f T).hom :=
  (isFlat_isStableUnderBaseChange B S hS).of_isPullback (s.isPullback_baseChange T) h

/-- Under the hypothesis of Stacks 0D27, the global functions of the base change to the
spectrum of a field form a field. -/
private theorem isField_globalFunctions_baseChange (hstein : s.StructureSheafMapIso)
    (k : Type u) [Field k] (hk : B.Contains (Spec (.of k))) (a : Spec (.of k) ⟶ S)
    (h : (schemeSpaceFunctor B S hS).obj (siteObject B S hS hk a) ⟶ s.base) :
    IsField (globalFunctions B S hS (s.baseChange (CostructuredArrow.mk h)).1) := by
  let e := RingEquiv.ofBijective (baseChangeGlobalFunctions s.f (CostructuredArrow.mk h))
    (bijective_baseChangeGlobalFunctions hstein (CostructuredArrow.mk h))
  have hΓ : IsField Γ(Spec (.of k), ⊤) :=
    MulEquiv.isField (Field.toIsField _) (gammaSpecRingEquiv k).toMulEquiv
  exact MulEquiv.isField hΓ e.symm.toMulEquiv

/-- Under the hypothesis of Stacks 0D27, the global functions of the base change to the
spectrum of a field form a nonzero ring. -/
private theorem nontrivial_globalFunctions_baseChange (hstein : s.StructureSheafMapIso)
    (k : Type u) [Field k] (hk : B.Contains (Spec (.of k))) (a : Spec (.of k) ⟶ S)
    (h : (schemeSpaceFunctor B S hS).obj (siteObject B S hS hk a) ⟶ s.base) :
    Nontrivial (globalFunctions B S hS (s.baseChange (CostructuredArrow.mk h)).1) :=
  (s.isField_globalFunctions_baseChange hstein k hk a h).nontrivial

/-- **The uniqueness part of the valuative criterion for a model of the relative Picard
functor, up to an extension of valuation rings.** Let `f : X ⟶ B` be flat, proper and of finite
presentation, with `𝒪_T ≅ f_{T,*}𝒪_{X_T}` for every test scheme `T` and with integral fibres
over the spectra of fields. Let `q : F ⟶ B` be a morphism of presheaves whose fibre over each
test scheme `T` is identified with `Pic_{X/B}(T)`, naturally in `T`. Then `q` satisfies
`AlgebraicGeometry.Space.ValuativeUniquenessUpToExtension`. -/
private theorem valuativeUniquenessUpToExtension_of_represents
    (hflat : IsFlat B S hS s.f.hom) (hfp : IsFinitePresentation B S hS s.f.hom)
    (hproper : IsProper B S hS s.f.hom) (hstein : s.StructureSheafMapIso)
    (hint : ∀ (k : Type u) [Field k] (hk : B.Contains (Spec (.of k))) (a : Spec (.of k) ⟶ S)
      (h : (schemeSpaceFunctor B S hS).obj (siteObject B S hS hk a) ⟶ s.base),
      IsIntegralSpace B S hS (s.baseChange (CostructuredArrow.mk h)).1)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (q : F ⟶ s.base.1)
    (e : ∀ T : s.SchemesOver, s.picardFunctor.obj (Opposite.op T) ≃
      {x : F.obj (Opposite.op T.left) //
        q.app (Opposite.op T.left) x =
          yonedaEquiv (show yoneda.obj T.left ⟶ s.base.1 from T.hom.hom)})
    (he : ∀ (T U : s.SchemesOver) (g : T ⟶ U) (x : s.picardFunctor.obj (Opposite.op U)),
      (e T (s.picardFunctor.map g.op x)).val = F.map g.left.op (e U x).val) :
    ValuativeUniquenessUpToExtension.{0} q := by
  intro R _ _ _ K _ _ _ ring_mem field_mem base a b hab hK
  let U := siteObject B S hS ring_mem base
  let a₀ : F.obj (Opposite.op U) := uliftYonedaEquiv.{0} a
  let b₀ : F.obj (Opposite.op U) := uliftYonedaEquiv.{0} b
  have hq : q.app _ a₀ = q.app _ b₀ := by
    have := congrArg uliftYonedaEquiv.{0} hab
    simpa only [uliftYonedaEquiv_comp] using this
  let h : (schemeSpaceFunctor B S hS).obj U ⟶ s.base :=
    ObjectProperty.homMk (yonedaEquiv.symm (q.app _ a₀))
  let T : s.SchemesOver := CostructuredArrow.mk h
  have hT : yonedaEquiv (show yoneda.obj T.left ⟶ s.base.1 from T.hom.hom) = q.app _ a₀ :=
    yonedaEquiv.apply_symm_apply _
  let x := (e T).symm ⟨a₀, hT.symm⟩
  let y := (e T).symm ⟨b₀, hq.symm.trans hT.symm⟩
  have hx : (e T x).val = a₀ := by simp [x]
  have hy : (e T y).val = b₀ := by simp [y]
  -- restriction along a morphism of test schemes, read in `F`
  have key : ∀ (T' : s.SchemesOver) (g : T' ⟶ T),
      s.picardFunctor.map g.op x = s.picardFunctor.map g.op y ↔
        F.map g.left.op a₀ = F.map g.left.op b₀ := by
    intro T' g
    rw [← hx, ← hy, ← he, ← he]
    exact ⟨fun h' => by rw [h'], fun h' => (e T').injective (Subtype.ext h')⟩
  have hmap : ∀ {V : BigFppfOver B S hS} (g : V ⟶ U),
      uliftYoneda.map g ≫ a = uliftYoneda.map g ≫ b ↔ F.map g.op a₀ = F.map g.op b₀ := by
    intro V g
    have ha := uliftYonedaEquiv_naturality.{0} a g.op
    have hb := uliftYonedaEquiv_naturality.{0} b g.op
    simp only [Quiver.Hom.unop_op] at ha hb
    show _ ↔ F.map g.op (uliftYonedaEquiv.{0} a) = F.map g.op (uliftYonedaEquiv.{0} b)
    rw [ha, hb]
    exact ⟨fun h' => by rw [h'], fun h' => uliftYonedaEquiv.injective h'⟩
  have hxyK := (key _ (valuationRingExtensionHom (algebraMap R K) ring_mem field_mem base h)).2
    ((hmap _).1 hK)
  obtain ⟨R', _, _, _, K', _, _, _, ring_mem', field_mem', φ, ψ, hφ, hcompat, L, N, hL, hN,
    hLN⟩ := s.exists_valuationRing_extension_picardMap_generic_eq R K ring_mem field_mem base h
      x y hxyK
  refine ⟨R', inferInstance, inferInstance, inferInstance, K', inferInstance, inferInstance,
    inferInstance, ring_mem', field_mem', φ, ψ, hφ, hcompat, ?_⟩
  refine (hmap _).2 ((key _ (valuationRingExtensionHom φ ring_mem ring_mem' base h)).1 ?_)
  rw [← hL, ← hN]
  congr 1
  -- the closed and generic fibres over `R'`
  let base' := Spec.map (CommRingCat.ofHom φ) ≫ base
  let h' := (schemeSpaceFunctor B S hS).map (specSiteObjectMap φ ring_mem ring_mem' base) ≫ h
  let T' : s.SchemesOver := CostructuredArrow.mk h'
  have res_mem' : B.Contains (Spec (.of (IsLocalRing.ResidueField R'))) :=
    BigFppfSite.contains_spec_of_mk_lt_cutoff B ((Cardinal.mk_le_of_surjective
      (Ideal.Quotient.mk_surjective (I := IsLocalRing.maximalIdeal R'))).trans_lt
        (BigFppfSite.mk_lt_cutoff_of_contains_spec B ring_mem'))
  let g₀ := valuationRingExtensionHom (IsLocalRing.residue R') ring_mem' res_mem' base' h'
  let gK := valuationRingExtensionHom (algebraMap R' K') ring_mem' field_mem' base' h'
  exact eq_of_picardPullback_eq_of_valuationRing R' K' ring_mem' res_mem' field_mem' base'
    (baseChangeInclusion s.f T') (s.isProper_baseChangeInclusion hproper T')
    (s.isFlat_baseChangeInclusion hflat T') (s.isFinitePresentation_baseChangeInclusion hfp T')
    _ (baseChangeMap s.f g₀) (isPullback_baseChangeMap s.f g₀)
    _ (baseChangeMap s.f gK) (isPullback_baseChangeMap s.f gK)
    (hint _ res_mem' _ _) (s.isField_globalFunctions_baseChange hstein _ res_mem' _ _)
    (s.nontrivial_globalFunctions_baseChange hstein _ field_mem' _ _) L N hLN

end PicardSituation

end AlgebraicGeometry.Space

end

/-! ### Stacks 03KV with the uniqueness part up to an extension of valuation rings -/

section Valuative

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The uniqueness part of the valuative criterion up to an extension of valuation rings, read
with the points of `Type u`-valued presheaves given by `CategoryTheory.yoneda`. -/
private def UniquenessUpToExtension (f : X ⟶ Y) : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (ring_mem : B.Contains (Spec (.of R))) (field_mem : B.Contains (Spec (.of K)))
    (base : Spec (.of R) ⟶ S)
    (a b : yoneda.obj (siteObject B S hS ring_mem base) ⟶ X),
    a ≫ f = b ≫ f →
    yoneda.map (specSiteObjectMap (algebraMap R K) ring_mem field_mem base) ≫ a =
      yoneda.map (specSiteObjectMap (algebraMap R K) ring_mem field_mem base) ≫ b →
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : ValuationRing R')
      (K' : Type u) (_ : Field K') (_ : Algebra R' K') (_ : IsFractionRing R' K')
      (ring_mem' : B.Contains (Spec (.of R'))) (_ : B.Contains (Spec (.of K')))
      (φ : R →+* R') (ψ : K →+* K'),
      IsLocalHom φ ∧ (algebraMap R' K').comp φ = ψ.comp (algebraMap R K) ∧
        yoneda.map (specSiteObjectMap φ ring_mem ring_mem' base) ≫ a =
          yoneda.map (specSiteObjectMap φ ring_mem ring_mem' base) ≫ b

/-- The form of the uniqueness part with points read through `CategoryTheory.uliftYoneda.{0}`
gives the form with points read through `CategoryTheory.yoneda`. -/
private theorem uniquenessUpToExtension_of_uLift {f : X ⟶ Y}
    (h : ValuativeUniquenessUpToExtension.{0} f) : UniquenessUpToExtension f := by
  intro R _ _ _ K _ _ _ ring_mem field_mem base a b hab hK
  let ι := (uliftYonedaIsoYoneda.{0} (C := BigFppfOver B S hS))
  have hnat : ∀ {V U : BigFppfOver B S hS} (g : V ⟶ U),
      uliftYoneda.{0}.map g ≫ ι.hom.app U = ι.hom.app V ≫ yoneda.map g :=
    fun g => ι.hom.naturality g
  have hK' : uliftYoneda.{0}.map (specSiteObjectMap (algebraMap R K) ring_mem field_mem base) ≫
        ι.hom.app _ ≫ a =
      uliftYoneda.{0}.map (specSiteObjectMap (algebraMap R K) ring_mem field_mem base) ≫
        ι.hom.app _ ≫ b := by
    rw [reassoc_of% hnat, reassoc_of% hnat, hK]
  obtain ⟨R', _, _, _, K', _, _, _, ring_mem', field_mem', φ, ψ, hφ, hfrac, heq⟩ :=
    h R K ring_mem field_mem base (ι.hom.app _ ≫ a) (ι.hom.app _ ≫ b)
      (by rw [Category.assoc, Category.assoc, hab]) hK'
  refine ⟨R', inferInstance, inferInstance, inferInstance, K', inferInstance, inferInstance,
    inferInstance, ring_mem', field_mem', φ, ψ, hφ, hfrac, ?_⟩
  rw [reassoc_of% hnat, reassoc_of% hnat] at heq
  exact (Iso.cancel_iso_hom_left (ι.app _) _ _).1 heq

/-- **The relative diagonal of a morphism satisfying the uniqueness part of the valuative
criterion up to an extension satisfies the existence part.** A valuative square for the
diagonal gives two points `a, b` of `X` over the valuation ring, the composites of its bottom
edge with the two projections; they agree over `Y` and over the fraction field, hence after an
extension of the valuation ring, and their common value is a lift of the extended square. -/
private theorem existence_pullbackDiagonal_of_uniquenessUpToExtension (f : X ⟶ Y)
    (hval : UniquenessUpToExtension f) :
    ValuativeCriterion.Existence (pullback.diagonal f) := by
  intro q
  set fr := specSiteObjectMap (hS := hS) (algebraMap q.R q.K) q.ring_mem q.field_mem q.base
    with hfr
  set a := q.special ≫ pullback.fst f f with ha
  set b := q.special ≫ pullback.snd f f with hb
  have hab : a ≫ f = b ≫ f := by
    rw [ha, hb, Category.assoc, Category.assoc, pullback.condition]
  have hgen : ∀ (pr : pullback f f ⟶ X), pullback.diagonal f ≫ pr = 𝟙 X →
      yoneda.map fr ≫ q.special ≫ pr = q.generic := by
    intro pr hpr
    have hc := q.comm
    change q.generic ≫ pullback.diagonal f = yoneda.map fr ≫ q.special at hc
    rw [← Category.assoc, ← hc, Category.assoc, hpr, Category.comp_id]
  have hK : yoneda.map fr ≫ a = yoneda.map fr ≫ b := by
    rw [ha, hb, hgen _ (pullback.diagonal_fst f), hgen _ (pullback.diagonal_snd f)]
  obtain ⟨R', _, _, _, K', _, _, _, ring_mem', field_mem', φ, ψ, hloc, hfrac, heq⟩ :=
    hval q.R q.K q.ring_mem q.field_mem q.base a b hab hK
  set sO := specSiteObjectMap (hS := hS) φ q.ring_mem ring_mem' q.base with hsO
  set fr' := specSiteObjectMap (hS := hS) (algebraMap R' K') ring_mem' field_mem'
    (Spec.map (CommRingCat.ofHom φ) ≫ q.base) with hfr'
  have hSpec : Spec.map (CommRingCat.ofHom ψ) ≫
      Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) =
      Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫ Spec.map (CommRingCat.ofHom φ) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, hfrac]
  set gO : siteObject B S hS field_mem'
      (Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫
        (Spec.map (CommRingCat.ofHom φ) ≫ q.base)) ⟶
      siteObject B S hS q.field_mem
        (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base) :=
    Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom ψ)) :
      B.obj field_mem' ⟶ B.obj q.field_mem) (by
        ext1
        show Spec.map (CommRingCat.ofHom ψ) ≫
            (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base) =
          Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫
            (Spec.map (CommRingCat.ofHom φ) ≫ q.base)
        rw [← Category.assoc, hSpec, Category.assoc]) with hgO
  have hsquare : gO ≫ fr = fr' ≫ sO := by
    apply siteObject_hom_ext
    show Spec.map (CommRingCat.ofHom ψ) ≫
        Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) =
      Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫ Spec.map (CommRingCat.ofHom φ)
    exact hSpec
  let square : ValuativeSquare (pullback.diagonal f) :=
    { R := R', K := K', ring_mem := ring_mem', field_mem := field_mem'
      base := Spec.map (CommRingCat.ofHom φ) ≫ q.base
      generic := yoneda.map gO ≫ q.generic
      special := yoneda.map sO ≫ q.special
      comm := by
        show (yoneda.map gO ≫ q.generic) ≫ pullback.diagonal f =
          yoneda.map fr' ≫ yoneda.map sO ≫ q.special
        rw [Category.assoc, q.comm]
        show yoneda.map gO ≫ yoneda.map fr ≫ q.special = _
        rw [← Functor.map_comp_assoc, hsquare, Functor.map_comp_assoc] }
  let ext : q.DominatingExtension :=
    { square := square
      ringMap := φ
      fieldMap := ψ
      isLocalHom := hloc
      fraction_comm := hfrac
      base_comm := rfl
      genericOver := gO
      genericOver_left := rfl
      specialOver := sO
      specialOver_left := rfl
      generic_comm := rfl
      special_comm := rfl }
  refine ⟨ext, ⟨?_⟩⟩
  exact
    { map := yoneda.map sO ≫ a
      generic_comm := by
        show yoneda.map fr' ≫ yoneda.map sO ≫ a = yoneda.map gO ≫ q.generic
        rw [← Functor.map_comp_assoc, ← hsquare, Functor.map_comp_assoc, ha,
          hgen _ (pullback.diagonal_fst f)]
      special_comm := by
        show (yoneda.map sO ≫ a) ≫ pullback.diagonal f = yoneda.map sO ≫ q.special
        apply pullback.hom_ext
        · rw [Category.assoc, Category.assoc, pullback.diagonal_fst, Category.comp_id, ha,
            Category.assoc]
        · rw [Category.assoc, Category.assoc, pullback.diagonal_snd, Category.comp_id, heq, hb,
            Category.assoc] }

/-- **Stacks 03KV, with the uniqueness part up to an extension of valuation rings.** A
quasi-separated morphism of algebraic spaces over `S` which satisfies the uniqueness part of the
valuative criterion up to an extension of valuation rings is separated. The proof is that of
`AlgebraicGeometry.Space.isSeparated_of_isQuasiSeparated_of_valuativeCriterion_uniqueness`, the
existence part for the relative diagonal coming from
`existence_pullbackDiagonal_of_uniquenessUpToExtension`, which allows the extension. -/
theorem isSeparated_of_isQuasiSeparated_of_valuativeUniquenessUpToExtension
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hqs : IsQuasiSeparated B S hS f) (hval : ValuativeUniquenessUpToExtension.{0} f) :
    IsSeparated B S hS f := by
  have hu := uniquenessUpToExtension_of_uLift hval
  have hdAlg := isAlgebraicSpace_pullback B S hS f f hX hX hY
  have hRep : yoneda.relativelyRepresentable (pullback.diagonal f) :=
    relativelyRepresentable_pullbackDiagonal B S hS f hX
  have hUC' : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.UniversallyClosed.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (pullback.diagonal f) :=
    (presheaf_universallyClosed_iff B S hS hX hdAlg hRep).2
      (universallyClosed_of_isQuasiCompact_of_valuativeCriterion_existence hX hdAlg
        (pullback.diagonal f) hqs
        (existence_pullbackDiagonal_of_uniquenessUpToExtension f hu))
  have hProperLqf : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      ((@_root_.AlgebraicGeometry.IsProper.{u} : MorphismProperty Scheme.{u}) ⊓
        (@LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u}))
      (BigFppfOver.toScheme B S hS))) (pullback.diagonal f) := by
    refine ⟨hRep, ?_⟩
    intro V W g fst snd hp
    have hsep := (presheaf_isSeparated_pullbackDiagonal B S hS f hX).property g fst snd hp
    have huc := hUC'.property g fst snd hp
    have hlft :=
      (presheaf_locallyOfFiniteType_pullbackDiagonal B S hS f hX).property g fst snd hp
    have hlqf :=
      ((presheaf_locallyQuasiFinite_pullbackDiagonal B S hS f hX).property g fst snd hp).2
    have h1 : _root_.AlgebraicGeometry.IsSeparated
      ((BigFppfOver.toScheme B S hS).map snd) := hsep
    have h2 : _root_.AlgebraicGeometry.UniversallyClosed
      ((BigFppfOver.toScheme B S hS).map snd) := huc
    have h3 : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map snd) := hlft
    exact ⟨_root_.AlgebraicGeometry.IsProper.mk, hlqf⟩
  have hFinite : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (pullback.diagonal f) := by
    refine MorphismProperty.relative_monotone (F := yoneda) ?_ _ hProperLqf
    intro V W g hg
    exact (_root_.AlgebraicGeometry.IsFinite.iff_isProper_and_locallyQuasiFinite
      ((BigFppfOver.toScheme B S hS).map g)).2 hg
  refine ⟨hRep, fun V W g fst snd hp ↦ ?_⟩
  exact (_root_.AlgebraicGeometry.IsClosedImmersion.iff_isFinite_and_mono
    ((BigFppfOver.toScheme B S hS).map snd)).2
    ⟨hFinite.property g fst snd hp,
      (presheaf_monomorphisms_pullbackDiagonal B S hS f hX).property g fst snd hp⟩

end AlgebraicGeometry.Space

end Valuative

/-! ### Separatedness of `Pic_{X/B}` -/

section Separated

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space.PicardSituation

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {s : PicardSituation B S hS}
  {H : AlgebraicSpaces B S hS} {p : H ⟶ s.base}
  (c : spacePointsOver p ⋙ uliftFunctor.{u + 1, u} ≅ s.picardFunctor)

/-- The bijection between `Pic_{X/B}(T)` and the points of `H` over `T` given by an
identification `c` of the functor of points of `H` over `B` with `Pic_{X/B}`. -/
private def pointsEquiv (T : s.SchemesOver) :
    s.picardFunctor.obj (Opposite.op T) ≃ {x : H.1.obj (Opposite.op T.left) //
      p.hom.app (Opposite.op T.left) x =
        yonedaEquiv (show yoneda.obj T.left ⟶ s.base.1 from T.hom.hom)} where
  toFun ξ := (c.inv.app (Opposite.op T) ξ).down
  invFun x := c.hom.app (Opposite.op T) (ULift.up x)
  left_inv ξ := (c.app (Opposite.op T)).inv_hom_id_apply ξ
  right_inv x := by
    have h := (c.app (Opposite.op T)).hom_inv_id_apply
      (show (spacePointsOver p ⋙ uliftFunctor.{u + 1, u}).obj (Opposite.op T) from ULift.up x)
    exact congrArg ULift.down h

/-- The bijection `pointsEquiv` is natural in the test scheme. -/
private theorem pointsEquiv_map (T U : s.SchemesOver) (g : T ⟶ U)
    (ξ : s.picardFunctor.obj (Opposite.op U)) :
    (pointsEquiv c T (s.picardFunctor.map g.op ξ)).val =
      H.1.map g.left.op (pointsEquiv c U ξ).val := by
  show (c.inv.app (Opposite.op T) (s.picardFunctor.map g.op ξ)).down.1 = _
  rw [NatTrans.naturality_apply]
  rfl

include c in
/-- **The argument of Stacks 0DNJ, given quasi-separatedness.** Let `f : X ⟶ B` be flat,
proper and of finite presentation, with `𝒪_T ≅ f_{T,*}𝒪_{X_T}` for every scheme `T` over `B`, and
with integral geometric fibres. Let `p : H ⟶ B` be an algebraic space over `B` whose functor of
points over `B` is identified (`c`) with `Pic_{X/B}`. If `p` is quasi-separated, it is separated.

Quasi-separatedness is the first half of Stacks 0DNI, whose source proof goes through Stacks
0DMF (0D2D and 0DMA), none of which is in this library; so this is not registered. The rest of
the source's argument is carried out: the uniqueness part of the valuative criterion, up to an
extension of the valuation ring, from Stacks 0CTM, 0BCC and 0DMZ, and Stacks 03KV in that form,
`AlgebraicGeometry.Space.isSeparated_of_isQuasiSeparated_of_valuativeUniquenessUpToExtension`. -/
theorem isSeparated_of_isQuasiSeparated_of_hasIntegralGeometricFibres
    (hflat : IsFlat B S hS s.f.hom) (hfp : IsFinitePresentation B S hS s.f.hom)
    (hproper : IsProper B S hS s.f.hom) (hstein : s.StructureSheafMapIso)
    (hgeom : HasIntegralGeometricFibres B S hS s.f.hom)
    (hqs : IsQuasiSeparated B S hS p.hom) :
    IsSeparated B S hS p.hom := by
  have hint : ∀ (k : Type u) [Field k] (hk : B.Contains (Spec (.of k))) (a : Spec (.of k) ⟶ S)
      (h : (schemeSpaceFunctor B S hS).obj (siteObject B S hS hk a) ⟶ s.base),
      IsIntegralSpace B S hS (s.baseChange (CostructuredArrow.mk h)).1 :=
    fun k _ hk a h => isIntegralSpace_baseChangeSpace_of_hasIntegralGeometricFibres s.f hgeom
      k hk a h
  exact isSeparated_of_isQuasiSeparated_of_valuativeUniquenessUpToExtension H.2 s.base.2 p.hom hqs
    (s.valuativeUniquenessUpToExtension_of_represents hflat hfp hproper hstein hint H.1 p.hom
      (pointsEquiv c) (pointsEquiv_map c))

end AlgebraicGeometry.Space.PicardSituation

end Separated

end
