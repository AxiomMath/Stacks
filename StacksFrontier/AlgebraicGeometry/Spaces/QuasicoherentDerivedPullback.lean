module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedDerivedPullbackQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedEtalePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
import StacksCore.Tactic.StacksAttribute

/-!
# The derived pullback along an arbitrary morphism of algebraic spaces preserves `D_QCoh`

Let `f : Y ⟶ X` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf site
`B`.  The derived pullback `Lf^*` sends `D_QCoh(𝒪_X)` into `D_QCoh(𝒪_Y)`.

## Main results

* `AlgebraicGeometry.Space.derivedQuasicoherent_smallEtaleDerivedModulePullback`: the derived
  pullback `Lf^*` sends `D_QCoh(𝒪_X)` into `D_QCoh(𝒪_Y)`.
* `AlgebraicGeometry.Space.quasicoherentDerivedPullback`: the resulting functor
  `D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_homology_modulePullback_of_isKFlat`: the
  statement on a K-flat complex with flat terms, on which `Lf^*` is computed degreewise.

## References

* [Stacks Project, Tag 08F4](https://stacks.math.columbia.edu/tag/08F4)
* [Stacks Project, Tag 08F2](https://stacks.math.columbia.edu/tag/08F2)
* [Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 0G7E](https://stacks.math.columbia.edu/tag/0G7E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

section Complexes

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable {X Y Z : AlgebraicSpaces B S hS}

/-- Along an étale morphism `a`, the cohomology of the degreewise pullback of a complex is the
pullback of its cohomology. -/
def modulePullbackHomologyIsoOfIsEtale (a : Z ⟶ X) (ha : IsEtale B S hS a.hom)
    (C : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ) (n : ℤ) :
    (((modulePullback B S hS a).mapHomologicalComplex (ComplexShape.up ℤ)).obj C).homology n ≅
      (etaleModulePullback B S hS a ha).obj (C.homology n) :=
  (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) n).mapIso
      ((NatIso.mapHomologicalComplex (modulePullbackIsoEtaleModulePullback B S hS a ha)
        (ComplexShape.up ℤ)).app C) ≪≫
    ((etaleModulePullback B S hS a ha).mapHomologicalComplexHomologyIso
      (ComplexShape.up ℤ) n).app C

/-- The isomorphism `γ^* cZ^* C ≅ cX^* a^* C` of degreewise pullbacks of a complex `C` around a
commuting square `γ ≫ cZ = cX ≫ a` of algebraic spaces. -/
def modulePullbackCommSquareComplexIso {X' X Z' Z : AlgebraicSpaces B S hS} {γ : X' ⟶ Z'}
    {cZ : Z' ⟶ Z} {cX : X' ⟶ X} {a : X ⟶ Z} (hsq : γ ≫ cZ = cX ≫ a)
    (C : CochainComplex (Modules.{u, u} B S hS Z.1 Z.2) ℤ) :
    ((modulePullback B S hS γ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((modulePullback B S hS cZ).mapHomologicalComplex (ComplexShape.up ℤ)).obj C) ≅
      ((modulePullback B S hS cX).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((modulePullback B S hS a).mapHomologicalComplex (ComplexShape.up ℤ)).obj C) :=
  (NatIso.mapHomologicalComplex (modulePullbackCommSquareIso B S hS hsq)
    (ComplexShape.up ℤ)).app C

/-- Degreewise pullback of modules along a morphism of algebraic spaces carries K-flat complexes
with flat terms to K-flat complexes with flat terms. -/
theorem isKFlat_modulePullback_mapHomologicalComplex (f : Y ⟶ X)
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS X).O)) ℤ)
    (hP : Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
      (Y := smallEtaleRingedTopos B S hS X)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) :
    Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
      (Y := smallEtaleRingedTopos B S hS Y)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (((modulePullback B S hS f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) := by
  have h := Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom.isKFlat_pullbackMapHomotopy
    (smallEtaleRingedToposHom B S hS f) _ hP
  exact (@mapHomologicalComplex_obj_congr _ _ _ _ _ _ _ _
    (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
      (pullbackModules_smallEtaleRingedToposHom_additive B S hS f))
    (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ (modulePullback B S hS f)
      (modulePullback_additive f))
    (pullbackModules_eq_modulePullback B S hS f) P
    (fun M => Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
      (Y := smallEtaleRingedTopos B S hS Y)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj M))).1 h

/-- For a morphism of represented algebraic spaces, degreewise pullback of a K-flat complex with
flat terms and quasi-coherent cohomology has quasi-coherent cohomology. -/
theorem isQuasicoherentOnSite_homology_modulePullback_representedSpaceMap
    {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩).O)) ℤ)
    (hP : Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
      (Y := smallEtaleRingedTopos B S hS ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P))
    (hPq : ∀ j : ℤ, (P.homology j).IsQuasicoherentOnSite) (i : ℤ) :
    ((((modulePullback B S hS (representedSpaceMap B S hS g)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P).homology i).IsQuasicoherentOnSite :=
  (isQuasicoherentOnSite_homology_pullbackModules_iff B S hS (representedSpaceMap B S hS g) P
    i).1 (isQuasicoherentOnSite_homology_pullbackModules_representedSpaceMap B S hS g P hP hPq i)

/-- For a morphism between algebraic spaces equal to represented ones, degreewise pullback of a
K-flat complex with flat terms and quasi-coherent cohomology has quasi-coherent cohomology. -/
theorem isQuasicoherentOnSite_homology_modulePullback_of_eq_represented
    {Z' Z : AlgebraicSpaces B S hS} (h : Z' ⟶ Z) (T' T : BigFppfOver B S hS)
    (hZ' : Z' = ⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩)
    (hZ : Z = ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩)
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS Z).O)) ℤ)
    (hP : Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
      (Y := smallEtaleRingedTopos B S hS Z)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P))
    (hPq : ∀ j : ℤ, (P.homology j).IsQuasicoherentOnSite) (i : ℤ) :
    ((((modulePullback B S hS h).mapHomologicalComplex (ComplexShape.up ℤ)).obj P).homology
      i).IsQuasicoherentOnSite := by
  subst hZ' hZ
  obtain ⟨g, rfl⟩ : ∃ g : T' ⟶ T, h = representedSpaceMap B S hS g :=
    ⟨yoneda.preimage h.hom, ObjectProperty.hom_ext _ (yoneda.map_preimage h.hom).symm⟩
  exact isQuasicoherentOnSite_homology_modulePullback_representedSpaceMap B S hS g P hP hPq i

/-- For an arbitrary morphism `f : Y ⟶ X` of algebraic spaces and a K-flat complex `P` of
`𝒪_X`-modules with flat terms all of whose cohomology sheaves are quasi-coherent, every cohomology
sheaf of `f^*P` is quasi-coherent. -/
theorem isQuasicoherentOnSite_homology_modulePullback_of_isKFlat (f : Y ⟶ X)
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS X).O)) ℤ)
    (hP : Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
      (Y := smallEtaleRingedTopos B S hS X)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P))
    (hPq : ∀ j : ℤ, (P.homology j).IsQuasicoherentOnSite) (n : ℤ) :
    ((((modulePullback B S hS f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P).homology
      n).IsQuasicoherentOnSite := by
  refine isQuasicoherentOnSite_of_coversTop_etaleModulePullback B S hS Y
    (affineChartDiagramCharts B S hS f) (coversTop_affineChartDiagramCharts B S hS f) _
    fun W => ?_
  unfold affineChartDiagramCharts
  obtain ⟨-, V, q, hq, -⟩ := W.2
  have hsq : chartSpaceMapOver B S hS q ≫ chartToSpace B S hS X V =
      chartToSpace B S hS Y W.1 ≫ f :=
    chartSpaceMapOver_comp_chartToSpace B S hS f q hq
  have hb := isKFlat_modulePullback_mapHomologicalComplex B S hS (chartToSpace B S hS X V) P hP
  have hbq : ∀ j : ℤ, ((((modulePullback B S hS (chartToSpace B S hS X V)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P).homology j).IsQuasicoherentOnSite := fun j =>
    SheafOfModules.IsQuasicoherentOnSite.of_iso
      (modulePullbackHomologyIsoOfIsEtale B S hS (chartToSpace B S hS X V)
        (isEtale_chartToSpace B S hS X V) P j).symm
      (isQuasicoherentOnSite_etaleModulePullback B S hS _ _ _ (hPq j))
  have hh := isQuasicoherentOnSite_homology_modulePullback_of_eq_represented B S hS
    (chartSpaceMapOver B S hS q) W.1.obj.left V.obj.left rfl rfl _ hb hbq n
  have h₁ := SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) n).mapIso
      (modulePullbackCommSquareComplexIso B S hS hsq P)) hh
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso
    (modulePullbackHomologyIsoOfIsEtale B S hS (chartToSpace B S hS Y W.1)
      (isEtale_chartToSpace B S hS Y W.1) _ n) h₁

end Complexes

section Main

variable {X Y : AlgebraicSpaces B S hS}

section

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

/-- Let `f : Y ⟶ X` be a morphism of algebraic spaces over `S`.  The derived pullback `Lf^*`,
the total left derived functor `AlgebraicGeometry.Space.smallEtaleDerivedModulePullback` of
degreewise pullback along the morphism of small étale ringed topoi of `f`, sends `D_QCoh(𝒪_X)`
into `D_QCoh(𝒪_Y)`: if every cohomology sheaf of `E ∈ D(𝒪_X)` is quasi-coherent, then so is
every cohomology sheaf of `Lf^*E`. -/
@[stacks 08F4]
theorem derivedQuasicoherent_smallEtaleDerivedModulePullback (f : Y ⟶ X)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))) E) :
    DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)))
      ((smallEtaleDerivedModulePullback B S hS f).obj E) := by
  obtain ⟨Kh, hK, s, hs⟩ :=
    Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.hasResolutions_isKFlat
      (Y := smallEtaleRingedTopos B S hS X)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (DerivedCategory.Q.objPreimage E))
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective Kh
  have : IsIso (DerivedCategory.Qh.map s) :=
    Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso _ _) s hs
  let e : DerivedCategory.Q.obj P ≅ E :=
    ((DerivedCategory.quotientCompQhIso _).app P).symm ≪≫ asIso (DerivedCategory.Qh.map s) ≪≫
      (DerivedCategory.quotientCompQhIso _).app _ ≪≫ DerivedCategory.Q.objObjPreimageIso E
  have hPq : ∀ j : ℤ, (P.homology j).IsQuasicoherentOnSite := fun j =>
    SheafOfModules.IsQuasicoherentOnSite.of_iso
      (((DerivedCategory.homologyFunctorFactors _ j).app P).symm ≪≫
        (DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) j).mapIso e).symm (hE j)
  intro n
  have h := (isQuasicoherentOnSite_homology_pullbackModules_iff B S hS f P n).2
    (isQuasicoherentOnSite_homology_modulePullback_of_isKFlat B S hS f P hK hPq n)
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso
    (((DerivedCategory.homologyFunctorFactors
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) n).app _).symm ≪≫
      (DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) n).mapIso
        ((derivedPullbackObjIsoOfIsKFlat B S hS f P hK).symm ≪≫
          (smallEtaleDerivedModulePullback B S hS f).mapIso e)) h

/-- The derived pullback `Lf^*` along an arbitrary morphism `f : Y ⟶ X` of algebraic spaces
restricts to a functor `D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` between the full subcategories of complexes
with quasi-coherent cohomology (Stacks 071X). -/
@[stacks 08F4 "the restriction D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y) of Lf^*, for an arbitrary morphism"]
noncomputable def quasicoherentDerivedPullback (f : Y ⟶ X) :
    (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))) :
      ObjectProperty (DerivedCategory
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))).FullSubcategory ⥤
    (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))) :
      ObjectProperty (DerivedCategory
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))).FullSubcategory :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ smallEtaleDerivedModulePullback B S hS f)
    fun K => derivedQuasicoherent_smallEtaleDerivedModulePullback B S hS f K.obj K.property

end

end Main

end AlgebraicGeometry.Space

end
