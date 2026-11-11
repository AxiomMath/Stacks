module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullbackBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.DerivedPullbackTriangulated
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedPullbackTopDegree
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TopDegreeComparison
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncGEOfIsLESingle
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncationLevelHomology

/-!
# The top cohomology of a derived pullback of algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces. For a module `M` on `Y` placed in degree `d`,
the degree-`d` cohomology of `Lf^*(M[-d])` is the inverse image `f^*M`; and for an object `K` of
`D(𝒪_Y)` with no cohomology above degree `d`, `H^d(Lf^*K) ≅ f^*H^d(K)`. This is the step of
Stacks 0EX3 (c) used in the proof of Stacks 0E1J (3), for the small étale site of an algebraic
space.

The proof is the one for ringed spaces in
`StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/DerivedPullbackTopDegree.lean`: `M[-d]` has a
flat representative with zero terms above `d`
(`AlgebraicGeometry.Space.exists_flat_representative_of_isLE`), on which `Lf^*` is computed
degreewise, and the right exact functor `f^*` commutes with the top cohomology of such a complex
(`Stacks.AlgebraicGeometry.TopDegreeBaseChange.mapTopHomologyIso`). Right t-exactness of `Lf^*`
(`AlgebraicGeometry.Space.isLE_smallEtaleDerivedModulePullback_obj`) then reduces the case of
`K` to that of `H^d(K)[-d]` (`Stacks.TopDegreeComparison.topDegreeIso`).

## Main results

* `AlgebraicGeometry.Space.nonempty_homology_smallEtaleDerivedModulePullback_singleFunctor_iso`:
  `H^d(Lf^*(M[-d])) ≅ f^*M`.
* `AlgebraicGeometry.Space.nonempty_homology_smallEtaleDerivedModulePullback_iso_of_isLE`:
  `H^d(Lf^*K) ≅ f^*H^d(K)` for `K` with no cohomology above `d`.
* `AlgebraicGeometry.Space.homologySmallEtaleDerivedModulePullbackSingleMap` and
  `AlgebraicGeometry.Space.homologySmallEtaleDerivedModulePullbackTopDegreeMap`: the canonical
  maps `H^d(Lf^*(M[-d])) ⟶ f^*M` and `H^d(Lf^*K) ⟶ f^*H^d(K)`, from the comparison `Lf^* ⟶ f^*`,
  with their invertibility.
* `AlgebraicGeometry.Space.modulePullbackHomologyToHomologySmallEtaleDerivedModulePullback`: the
  canonical map `f^*H^d(K) ⟶ H^d(Lf^*K)` for every `K`, an isomorphism when `K` has no cohomology
  above `d`.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 0E1J](https://stacks.math.columbia.edu/tag/0E1J)
-/

@[expose] public noncomputable section


open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS}

/-- **`H^d(Lf^*(M[-d])) ≅ f^*M`** for a morphism `f` of algebraic spaces and a module `M` on the
target placed in degree `d`. -/
theorem nonempty_homology_smallEtaleDerivedModulePullback_singleFunctor_iso (f : X ⟶ Y)
    (M : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (d : ℤ) :
    Nonempty ((DerivedCategory.homologyFunctor _ d).obj
        ((smallEtaleDerivedModulePullback B S hS f).obj
          ((DerivedCategory.singleFunctor _ d).obj M)) ≅ (modulePullback B S hS f).obj M) := by
  obtain ⟨K, hflat, hKLE, ⟨e⟩⟩ := exists_flat_representative_of_isLE
    ((DerivedCategory.singleFunctor _ d).obj M) d inferInstance
  have := hKLE
  obtain ⟨e'⟩ := nonempty_smallEtaleDerivedModulePullback_obj_Q_iso_modulePullback f K d hflat
  have : (modulePullback B S hS f).Additive := modulePullback_additive f
  have : PreservesColimitsOfSize.{0, 0} (modulePullback B S hS f) :=
    (modulePullbackAdjunction B S hS f).leftAdjoint_preservesColimits
  have : PreservesFiniteColimits (modulePullback B S hS f) := inferInstance
  exact ⟨(DerivedCategory.homologyFunctor _ d).mapIso
      ((smallEtaleDerivedModulePullback B S hS f).mapIso e.symm ≪≫ e') ≪≫
    (DerivedCategory.homologyFunctorFactors _ d).app _ ≪≫
    Stacks.AlgebraicGeometry.TopDegreeBaseChange.mapTopHomologyIso (modulePullback B S hS f) K d
      hKLE ≪≫
    (modulePullback B S hS f).mapIso (((DerivedCategory.homologyFunctorFactors _ d).app K).symm ≪≫
      (DerivedCategory.homologyFunctor _ d).mapIso e ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso _ d).app M)⟩

/-- **`H^d(Lf^*K) ≅ f^*H^d(K)`** for an object `K` of `D(𝒪_Y)` with no cohomology above degree
`d`: the top cohomology of a derived pullback is the inverse image of the top cohomology. -/
theorem nonempty_homology_smallEtaleDerivedModulePullback_iso_of_isLE (f : X ⟶ Y)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) (d : ℤ)
    (hK : K.IsLE d) :
    Nonempty ((DerivedCategory.homologyFunctor _ d).obj
        ((smallEtaleDerivedModulePullback B S hS f).obj K) ≅
      (modulePullback B S hS f).obj ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) d).obj K)) := by
  obtain ⟨e⟩ := nonempty_homology_smallEtaleDerivedModulePullback_singleFunctor_iso f
    ((DerivedCategory.homologyFunctor _ d).obj K) d
  have : DerivedCategory.TStructure.t.IsLE K d := hK
  exact ⟨Stacks.TopDegreeComparison.topDegreeIso (smallEtaleDerivedModulePullback B S hS f)
      (fun E n hE => isLE_smallEtaleDerivedModulePullback_obj f E n hE) K d
      (DerivedCategory.truncGEIsoSingleHomologyOfIsLE K d) ≪≫ e⟩

/-! ### The canonical comparison maps -/

/-- **The canonical map `Lf^*(M[-d]) ⟶ (f^*M)[-d]`** for a morphism of algebraic spaces: the
comparison `Lf^* ⟶ f^*` of the derived pullback with degreewise pullback
(`AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackComparison`) at the single complex on
`M`, read through the identifications of the single functors with their homotopy-category and
derived-category forms, followed by the identification of the pullback of modules of the morphism
of small étale ringed topoi with `AlgebraicGeometry.Space.modulePullback`. -/
def smallEtaleDerivedToOrdinaryPullbackSingle (f : X ⟶ Y)
    (M : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (d : ℤ) :
    (smallEtaleDerivedModulePullback B S hS f).obj ((DerivedCategory.singleFunctor _ d).obj M) ⟶
      (DerivedCategory.singleFunctor _ d).obj ((modulePullback B S hS f).obj M) :=
  (smallEtaleDerivedModulePullback B S hS f).map
      ((DerivedCategory.singleFunctorIsoCompQh _ d).hom.app M) ≫
    (smallEtaleDerivedModulePullbackComparison B S hS f).app
      ((HomotopyCategory.singleFunctor _ d).obj M) ≫
    DerivedCategory.Qh.map ((Functor.mapHomotopyCategorySingleFunctor
      (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
        (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
        (smallEtaleRingedToposHom B S hS f).toModulesHom) d).hom.app M) ≫
    (DerivedCategory.singleFunctorIsoCompQh _ d).inv.app _ ≫
    (DerivedCategory.singleFunctor _ d).map ((pullbackModulesIsoModulePullback B S hS f).hom.app M)

/-- **The canonical map `H^d(Lf^*(M[-d])) ⟶ f^*M`**: `smallEtaleDerivedToOrdinaryPullbackSingle`
on degree-`d` cohomology, followed by `H^d(N[-d]) ≅ N`. -/
def homologySmallEtaleDerivedModulePullbackSingleMap (f : X ⟶ Y)
    (M : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (d : ℤ) :
    (DerivedCategory.homologyFunctor _ d).obj
        ((smallEtaleDerivedModulePullback B S hS f).obj
          ((DerivedCategory.singleFunctor _ d).obj M)) ⟶ (modulePullback B S hS f).obj M :=
  (DerivedCategory.homologyFunctor _ d).map (smallEtaleDerivedToOrdinaryPullbackSingle f M d) ≫
    (Stacks.AlgebraicGeometry.TopDegreeBaseChange.homologySingleIso _ d).hom

open Stacks.AlgebraicGeometry.TopDegreeBaseChange in
/-- **The comparison `Lf^*(Q P) ⟶ Q(f^*P)` is invertible on degree-`d` cohomology for every
complex `P` with zero terms above `d`.** Take a quasi-isomorphism `s : F ⟶ P` from a complex of
flat modules with zero terms above `d`; at `F` the comparison is invertible (Stacks 06YY, `F` is
K-flat), `Lf^*` inverts `s`, and `H^d(f^*s)` is invertible because `f^*` is right exact. -/
theorem isIso_homologyFunctor_map_smallEtaleDerivedModulePullbackComparison_app (f : X ⟶ Y)
    (P : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ) (d : ℤ)
    (hP : P.IsStrictlyLE d) :
    IsIso ((DerivedCategory.homologyFunctor _ d).map
      ((smallEtaleDerivedModulePullbackComparison B S hS f).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P))) := by
  have := hP
  let Pflat : ObjectProperty (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) :=
    fun F => AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, u, u}
      (O := (smallEtaleRingedTopos B S hS Y).O) F
  have _ : Pflat.ContainsZero :=
    ⟨⟨⊥_ _, initialIsInitial.isZero, isFlat_of_isZero B S hS initialIsInitial.isZero⟩⟩
  have hcover : ∀ F : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y),
      ∃ (G : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (_ : Pflat G)
        (g : G ⟶ F), Epi g := by
    intro F
    obtain ⟨G, g, hG, hg⟩ :=
      Stacks.SheafOfModules.FlatCover.exists_epi_from_isFlat_ofSize
        (smallEtaleRingedTopos B S hS Y).O F
    exact ⟨G, hG, g, hg⟩
  obtain ⟨F, s, -, hs, hFflat, hFLE⟩ := (CochainComplex.exists_quasiIso_prop Pflat hcover d).1 P
  have := hFLE
  have hcompF := isIso_smallEtaleDerivedModulePullbackComparison_app B S hS f _
    (smallEtaleModuleKFlat_of_isStrictlyLE B S hS Y F d hFflat)
  let G := Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
    (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
    (smallEtaleRingedToposHom B S hS f).toModulesHom
  have := RingedToposHom.pullbackModules_preservesFiniteColimits (smallEtaleRingedToposHom B S hS f)
  have hmap : IsIso (HomologicalComplex.homologyMap
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map s) d) :=
    Stacks.AlgebraicGeometry.TopDegreeBaseChange.isIso_homologyMap_map_of_isStrictlyLE G s d
      hFLE hP ((quasiIsoAt_iff_isIso_homologyMap s d).1 (hs.quasiIsoAt d))
  have hψ : IsIso ((DerivedCategory.homologyFunctor _ d).map
      ((smallEtaleModulePullbackOnHomotopy B S hS f).map
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map s))) :=
    isIso_homologyFunctor_map_Qh_map_quotient_map_of_isIso_homologyMap
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map s) d hmap
  have hQs := Stacks.AlgebraicGeometry.TopDegreeBaseChange.isIso_Qh_map_quotient_map s hs
  have hLs : IsIso ((DerivedCategory.homologyFunctor _ d).map
      ((DerivedCategory.Qh ⋙ smallEtaleDerivedModulePullback B S hS f).map
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map s))) :=
    ((smallEtaleDerivedModulePullback B S hS f ⋙ DerivedCategory.homologyFunctor _ d).mapIso
      (@asIso _ _ _ _ _ hQs)).isIso_hom
  have nat := (smallEtaleDerivedModulePullbackComparison B S hS f).naturality
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map s)
  have hRHS : IsIso ((DerivedCategory.homologyFunctor _ d).map
      ((smallEtaleDerivedModulePullbackComparison B S hS f).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj F) ≫
        (smallEtaleModulePullbackOnHomotopy B S hS f).map
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map s))) := by
    rw [Functor.map_comp]
    infer_instance
  rw [← nat, Functor.map_comp] at hRHS
  exact IsIso.of_isIso_comp_left ((DerivedCategory.homologyFunctor _ d).map
    ((DerivedCategory.Qh ⋙ smallEtaleDerivedModulePullback B S hS f).map
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map s))) _

/-- **`H^d(Lf^*(M[-d])) = f^*M`**: the canonical map
`homologySmallEtaleDerivedModulePullbackSingleMap` is an isomorphism. -/
theorem isIso_homologySmallEtaleDerivedModulePullbackSingleMap (f : X ⟶ Y)
    (M : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (d : ℤ) :
    IsIso (homologySmallEtaleDerivedModulePullbackSingleMap f M d) := by
  have hcomp : IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) d).map
      ((smallEtaleDerivedModulePullbackComparison B S hS f).app
        ((HomotopyCategory.singleFunctor
          (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) d).obj M))) :=
    isIso_homologyFunctor_map_smallEtaleDerivedModulePullbackComparison_app f
      ((CochainComplex.singleFunctor _ d).obj M) d inferInstance
  rw [homologySmallEtaleDerivedModulePullbackSingleMap, smallEtaleDerivedToOrdinaryPullbackSingle]
  refine IsIso.comp_isIso' ?_ (Iso.isIso_hom _)
  rw [Functor.map_comp, Functor.map_comp]
  exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' hcomp
    ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) d).mapIso
      (DerivedCategory.Qh.mapIso ((Functor.mapHomotopyCategorySingleFunctor
        (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
          (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
          (smallEtaleRingedToposHom B S hS f).toModulesHom) d).app M) ≪≫
        ((DerivedCategory.singleFunctorIsoCompQh _ d).app _).symm ≪≫
        (DerivedCategory.singleFunctor _ d).mapIso
          ((pullbackModulesIsoModulePullback B S hS f).app M))).isIso_hom)

/-- **The canonical map `H^d(Lf^*K) ⟶ f^*H^d(K)`** for an object `K` of `D(𝒪_Y)` with no
cohomology above degree `d`: `H^d` of `Lf^*` of the truncation `K ⟶ τ^{≥d}K = H^d(K)[-d]`,
followed by `homologySmallEtaleDerivedModulePullbackSingleMap`. -/
def homologySmallEtaleDerivedModulePullbackTopDegreeMap (f : X ⟶ Y)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) (d : ℤ)
    (hK : K.IsLE d) :
    (DerivedCategory.homologyFunctor _ d).obj ((smallEtaleDerivedModulePullback B S hS f).obj K) ⟶
      (modulePullback B S hS f).obj ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) d).obj K) :=
  (DerivedCategory.homologyFunctor _ d).map ((smallEtaleDerivedModulePullback B S hS f).map
      ((DerivedCategory.TStructure.t.truncGEπ d).app K ≫
        (Stacks.AlgebraicGeometry.TopDegreeBaseChange.truncGEIsoSingleHomology K d hK).hom)) ≫
    homologySmallEtaleDerivedModulePullbackSingleMap f _ d

/-- **`H^d(Lf^*K) = f^*H^d(K)`** for `K` with no cohomology above `d`: the canonical map
`homologySmallEtaleDerivedModulePullbackTopDegreeMap` is an isomorphism. This is the step of
Stacks 0EX3 (c) used in the proof of Stacks 0E1J (3). -/
theorem isIso_homologySmallEtaleDerivedModulePullbackTopDegreeMap (f : X ⟶ Y)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) (d : ℤ)
    (hK : K.IsLE d) :
    IsIso (homologySmallEtaleDerivedModulePullbackTopDegreeMap f K d hK) := by
  have := Stacks.TopDegreeComparison.isIso_homologyMap_map_truncGEπ_app
    (smallEtaleDerivedModulePullback B S hS f)
    (fun E n hE => isLE_smallEtaleDerivedModulePullback_obj f E n hE) K d d le_rfl
  have := isIso_homologySmallEtaleDerivedModulePullbackSingleMap f
    ((DerivedCategory.homologyFunctor _ d).obj K) d
  rw [homologySmallEtaleDerivedModulePullbackTopDegreeMap]
  refine IsIso.comp_isIso' ?_ inferInstance
  rw [Functor.map_comp, Functor.map_comp]
  exact IsIso.comp_isIso' inferInstance inferInstance

/-- **The canonical map `f^*H^d(K) ⟶ H^d(Lf^*K)`** for every object `K` of `D(𝒪_Y)`: through
`τ^{≤d}K ⟶ K`, which does not change `H^d`, it is the inverse of the isomorphism
`H^d(Lf^*τ^{≤d}K) ≅ f^*H^d(τ^{≤d}K)` of `isIso_homologySmallEtaleDerivedModulePullbackTopDegreeMap`
followed by `H^d` of `Lf^*(τ^{≤d}K ⟶ K)`. -/
def modulePullbackHomologyToHomologySmallEtaleDerivedModulePullback (f : X ⟶ Y)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) (d : ℤ) :
    (modulePullback B S hS f).obj ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) d).obj K) ⟶
      (DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) d).obj
        ((smallEtaleDerivedModulePullback B S hS f).obj K) :=
  (modulePullback B S hS f).map (@asIso _ _ _ _ ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) d).map
      ((DerivedCategory.TStructure.t.truncLTι (d + 1)).app K))
      (Stacks.TruncationLevel.isIso_homologyMap_truncLTι_app
        (A := SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (d + 1) d (by omega)
        K)).inv ≫
    (@asIso _ _ _ _ (homologySmallEtaleDerivedModulePullbackTopDegreeMap f _ d
      (DerivedCategory.TStructure.t.isLE_truncLT_obj K (d + 1) d))
      (isIso_homologySmallEtaleDerivedModulePullbackTopDegreeMap f _ d
        (DerivedCategory.TStructure.t.isLE_truncLT_obj K (d + 1) d))).inv ≫
    (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) d).map
      ((smallEtaleDerivedModulePullback B S hS f).map
        ((DerivedCategory.TStructure.t.truncLTι (d + 1)).app K))

/-- **`f^*H^d(K) = H^d(Lf^*K)`** for `K` with no cohomology above `d`: the canonical map
`modulePullbackHomologyToHomologySmallEtaleDerivedModulePullback` is an isomorphism, the
inclusion `τ^{≤d}K ⟶ K` being one. -/
theorem isIso_modulePullbackHomologyToHomologySmallEtaleDerivedModulePullback (f : X ⟶ Y)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) (d : ℤ)
    (hK : K.IsLE d) :
    IsIso (modulePullbackHomologyToHomologySmallEtaleDerivedModulePullback f K d) := by
  have : IsIso ((DerivedCategory.TStructure.t.truncLTι (d + 1)).app K) :=
    (DerivedCategory.TStructure.t.isLE_iff_isIso_truncLTι_app d (d + 1) rfl K).1 hK
  have h₁ := Stacks.TruncationLevel.isIso_homologyMap_truncLTι_app
    (A := SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (d + 1) d (by omega) K
  have hLE := DerivedCategory.TStructure.t.isLE_truncLT_obj K (d + 1) d
  have h₂ := isIso_homologySmallEtaleDerivedModulePullbackTopDegreeMap f _ d hLE
  rw [modulePullbackHomologyToHomologySmallEtaleDerivedModulePullback]
  exact IsIso.comp_isIso' ((modulePullback B S hS f).mapIso (asIso
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) d).map
        ((DerivedCategory.TStructure.t.truncLTι (d + 1)).app K))).symm).isIso_hom
    (IsIso.comp_isIso' (Iso.isIso_inv (asIso
      (homologySmallEtaleDerivedModulePullbackTopDegreeMap f _ d hLE)))
      ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) d).mapIso
      ((smallEtaleDerivedModulePullback B S hS f).mapIso
        (asIso ((DerivedCategory.TStructure.t.truncLTι (d + 1)).app K)))).isIso_hom)

end AlgebraicGeometry.Space

end
