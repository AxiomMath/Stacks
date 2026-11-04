module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TopDegreeAmplitude
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedModelCrossing
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SituationBaseChange
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaQCoh
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ShiftedDegreeZero
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.CohomologyAboveADegree

/-!
# Conclusion (b) of Tag 0EX3: the top higher direct image commutes with tensoring

Let `f : X ⟶ Y` be quasi-compact and quasi-separated and suppose `Rⁱ f_* F = 0` for `i > d` and
every quasi-coherent `F`. Then for quasi-coherent `F` on `X` and `G` on `Y`

`Rᵈ f_*(F ⊗_{𝒪_X} f^* G) ≅ Rᵈ f_* F ⊗_{𝒪_Y} G`.

This is conclusion (b) of [Stacks, Tag 0EX3], for an arbitrary base: applied to the base change
`f'` of a top-degree base-change situation, whose higher direct images vanish above `d` by
conclusion (a), it is (b) for an arbitrary `Y'`.

## The route

The source proves (b) over an affine `Y'` by Eilenberg-Watts. Here the identification is read
off the derived projection formula instead, which holds over an arbitrary base and so needs no
localisation:

* [Stacks, Tag 08EU] (`…ProjectionFormulaQCoh.isIso_projectionFormulaMap_of_isDQCoh`) gives
  `Rf_*(F[0]) ⊗^L G[0] ≅ Rf_*(F[0] ⊗^L Lf^*(G[0]))`;
* on the left, `Rf_*(F[0])` lives in degrees `≤ d`, so `Hᵈ` of its tensor product with `G[0]`
  only sees `τ_{≥ d} Rf_*(F[0]) = Rᵈ f_* F[-d]` ([Stacks, Tag 0DIV]), whose tensor product with
  `G[0]` has `Hᵈ = Rᵈ f_* F ⊗ G` (the degree-zero read-off of the derived tensor product, shifted);
* on the right, `F[0] ⊗^L Lf^*(G[0])` lives in degrees `≤ 0` with `H⁰ = F ⊗ f^* G`, and
  `Hᵈ(Rf_* -)` only sees `H⁰` of such a complex
  (`isIso_homology_derivedPushforward_map_of_isIso_homology_zero`).

Every arrow is canonical: the projection-formula morphism of [Stacks, Tag 0B53], the truncation
`K ⟶ τ_{≥ d} K`, the comparison from derived to ordinary pullback, and the comparison
`A[0] ⊗^L B[0] ⟶ (A ⊗ B)[0]` from derived to ordinary tensor product.

## Main definitions

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.topDegreeTensorIso`: the isomorphism, for a
  quasi-compact quasi-separated morphism with higher direct images vanishing above `d`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.topDegreeTensorSheafIso`: the same for the
  base-changed morphism of a top-degree base-change situation — **conclusion (b) of
  [Stacks, Tag 0EX3]**, with no hypothesis on `Y'`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.homologyDerivedPushforwardTensorIso`: the
  left-hand read-off `Hᵈ(Rf_*(F[0]) ⊗^L G[0]) ≅ Rᵈ f_* F ⊗ G`.
* `Stacks.DerivedTensor.RingedSite.degreeSingleLeftTensorIso`: `Hᶜ(A[c] ⊗^L G[0]) ≅ A ⊗ G`.

## Main results

* `Stacks.DerivedTensor.RingedSite.isIso_homologyMap_tensorObj_map_of_approximation`: tensoring
  with a bounded above object keeps a cohomological approximation.
* `TopDegreeBaseChange.isIso_homologyMap_derivedPushforward_tensorDerivedPullbackToSingle`:
  the right-hand read-off.

## Implementation notes

The module categories are written `SheafOfModules.{u} (structureSheafRing X.toRingedSpace)`
rather than `X.Modules`, the spelling at which the derived pushforward, the derived pullback and
the projection formula are stated; the vanishing hypothesis keeps the `X.Modules` spelling of
[Stacks, Tag 0EX3] (2) and is applied across the two in argument position. Instance search does
not see that `IsLE` and `IsQuasicoherent` instances at one spelling are instances at the other,
so they are passed explicitly (`isLE_singleFunctor_zero`, `‹_›`).

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 0DIV](https://stacks.math.columbia.edu/tag/0DIV)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedTensor.RingedSite
open DerivedCategory CategoryTheory.Pretriangulated

universe u d

noncomputable section

namespace Stacks.DerivedTensor.RingedSite

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasDerivedCategory.{d} (Modules R)]
variable
  [(Stacks.SheafOfModules.Tensor.sheafTensor R).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj M).Additive]
  [∀ (K L : CochainComplex (Modules R) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor R)
      (ComplexShape.up ℤ)]

/-- **Tensoring on the left with a bounded above object keeps a cohomological approximation.**
If `K` lives in degrees `≤ a` and `α` induces isomorphisms on `Hⁱ` for `i > n` and an epimorphism
on `Hⁿ`, then `K ⊗^L α` induces isomorphisms on `Hⁱ` for `i > a + n`. The third vertex of the
cocone triangle of `α` lives in degrees `≤ n - 1`, and tensoring with `K` puts it in degrees
`≤ a + n - 1`. -/
theorem isIso_homologyMap_tensorObj_map_of_approximation
    (K : DerivedModules R) (a : ℤ) [K.IsLE a] {L L' : DerivedModules R} (α : L ⟶ L') (n : ℤ)
    (hiso : ∀ i : ℤ, n < i → IsIso ((DerivedCategory.homologyFunctor (Modules R) i).map α))
    (hepi : Epi ((DerivedCategory.homologyFunctor (Modules R) n).map α))
    (i : ℤ) (hi : a + n < i) :
    IsIso ((DerivedCategory.homologyFunctor (Modules R) i).map
      (((derivedTensorProductFunctor R).obj K).map α)) := by
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle α
  have hZ : Z.IsLE (n - 1) :=
    DerivedCategory.triangle_obj₃_isLE_of_approximation (Triangle.mk α g h) hT n hiso hepi
  have hKZ : (((derivedTensorProductFunctor R).obj K).obj Z).IsLE (a + n - 1) := by
    have := isLE_derivedTensorProductFunctor R K Z a (n - 1)
    rwa [show a + (n - 1) = a + n - 1 by omega] at this
  have hT' := ((derivedTensorProductFunctor R).obj K).map_distinguished _ hT
  have := (DerivedCategory.approximation_of_triangle_isLE _ hT' (a + n) hKZ).1 i hi
  exact this

/-- **The degree-`c` read-off with the module in degree `c` on the left.** For sheaves of
modules `A` and `G` on a small ringed site, `Hᶜ(A[c] ⊗^L_O G[0]) ≅ A ⊗_O G`, with no flatness
hypothesis. The shift is moved out of the left variable of the derived tensor product, cancelled
against the degree, and the degree-zero comparison `degreeZeroTensorIso` concludes. -/
def degreeSingleLeftTensorIso (A G : Modules R) (c : ℤ) :
    (DerivedCategory.homologyFunctor (Modules R) c).obj
        (((derivedTensorProductFunctor R).obj
          ((DerivedCategory.singleFunctor (Modules R) c).obj A)).obj
          (DerivedCategory.Q.obj (sg R G))) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj A).obj G :=
  (DerivedCategory.homologyFunctor (Modules R) c).mapIso
      (((derivedTensorProductFunctor R).flip.obj (DerivedCategory.Q.obj (sg R G))).mapIso
          (singleShiftIso R A c) ≪≫
        (((derivedTensorProductFunctor R).flip.obj (DerivedCategory.Q.obj (sg R G))).commShiftIso
          (-c)).app (DerivedCategory.Q.obj (sg R A))) ≪≫
    (Stacks.HomologyShift.homologyShiftIso (Modules R) (-c) c 0 (by lia)).app
      (((derivedTensorProductFunctor R).obj (DerivedCategory.Q.obj (sg R A))).obj
        (DerivedCategory.Q.obj (sg R G))) ≪≫
    degreeZeroTensorIso R G A

end Stacks.DerivedTensor.RingedSite

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.Cohomology.ProjectionFormulaPerfect.hasSheafifyOpens
  Stacks.Cohomology.ProjectionFormulaPerfect.wEqualsLocallyBijectiveOpens

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A module placed in degree `0` lives in degrees `≤ 0`, stated for an explicit category so that
it can be supplied where the two spellings of the category of modules on a scheme defeat instance
search. -/
theorem isLE_singleFunctor_zero {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (M : C) : ((singleFunctor C 0).obj M).IsLE 0 := inferInstance

/-- A module placed in degree `0` has quasi-coherent cohomology sheaves as soon as the module is
quasi-coherent. -/
theorem isDQCoh_singleFunctor {Z : Scheme.{u}} (M : Z.Modules) (hM : M.IsQuasicoherent) :
    Stacks.DerivedQCoh.IsDQCoh (R := structureSheafRing Z.toRingedSpace)
      ((singleFunctor Z.Modules 0).obj M) := by
  intro i
  have hP := AlgebraicGeometry.containsZero_isQuasicoherent Z
  change ((homologyFunctor Z.Modules i).obj ((singleFunctor Z.Modules 0).obj M)).IsQuasicoherent
  rcases lt_trichotomy i 0 with hi | rfl | hi
  · exact (SheafOfModules.isQuasicoherent Z.ringCatSheaf).prop_of_isZero
      (DerivedCategory.isZero_of_isGE ((singleFunctor Z.Modules 0).obj M) 0 i hi)
  · exact (SheafOfModules.isQuasicoherent Z.ringCatSheaf).prop_of_iso
      ((singleFunctorCompHomologyFunctorIso _ 0).app M).symm hM
  · exact (SheafOfModules.isQuasicoherent Z.ringCatSheaf).prop_of_isZero
      (DerivedCategory.isZero_of_isLE ((singleFunctor Z.Modules 0).obj M) 0 i hi)

/-- **The comparison `F[0] ⊗^L Lf^*(G[0]) ⟶ (F ⊗ f^* G)[0]`**: the derived-to-ordinary pullback
comparison in the right variable, followed by the derived-to-ordinary tensor comparison. -/
def tensorDerivedPullbackToSingle (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (G : SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) :
    ((derivedTensorProductFunctor X.toRingedSpace.sheaf).obj
        ((singleFunctor (Modules X.toRingedSpace.sheaf) 0).obj F)).obj
        ((derivedPullback f.toLRSHom.toShHom).obj
          ((singleFunctor (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) 0).obj G)) ⟶
      (singleFunctor (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf).obj F).obj
          ((RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom).obj G)) :=
  ((derivedTensorProductFunctor X.toRingedSpace.sheaf).obj
      ((singleFunctor (Modules X.toRingedSpace.sheaf) 0).obj F)).map
      (derivedToOrdinaryPullbackSingle f.toLRSHom.toShHom G 0) ≫
    tensorSingleToSingle X.toRingedSpace.sheaf F
      ((RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom).obj G)

section TopDegree

/-- `Rf_*(F[0])` lives in degrees `≤ d`. -/
theorem isLE_derivedPushforward_single_of_vanishing [QuasiCompact f] [QuasiSeparated f] (d : ℕ)
    (hvan : ∀ i : ℤ, (d : ℤ) < i → ∀ F : X.Modules, F.IsQuasicoherent →
      IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus i).obj F))
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) [F.IsQuasicoherent] :
    ((derivedPushforward f.toLRSHom.toShHom).obj ((singleFunctor
        (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj F)).IsLE
      (d : ℤ) :=
  isLE_derivedPushforward_singleFunctor f.toLRSHom.toShHom F (d : ℤ)
    (fun i hi => hvan i hi F ‹_›)

/-- The canonical map `Rf_*(F[0]) ⟶ (Rᵈ f_* F)[-d]`: the truncation `K ⟶ τ_{≥ d} K` followed by the
identification of `τ_{≥ d} K` with the top cohomology placed in degree `d`. -/
def derivedPushforwardToTopSingle [QuasiCompact f] [QuasiSeparated f] (d : ℕ)
    (hvan : ∀ i : ℤ, (d : ℤ) < i → ∀ F : X.Modules, F.IsQuasicoherent →
      IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus i).obj F))
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) [F.IsQuasicoherent] :
    (derivedPushforward f.toLRSHom.toShHom).obj ((singleFunctor
        (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj F) ⟶
      (singleFunctor (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) (d : ℤ)).obj
        ((homologyFunctor (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) (d : ℤ)).obj
        ((derivedPushforward f.toLRSHom.toShHom).obj ((singleFunctor
            (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj F))) :=
  (TStructure.t.truncGEπ (d : ℤ)).app _ ≫
    (truncGEIsoSingleHomology _ (d : ℤ)
      (isLE_derivedPushforward_single_of_vanishing f d hvan F)).hom

/-- `derivedPushforwardToTopSingle` is an isomorphism on cohomology in every degree `≥ d`. -/
theorem isIso_homologyMap_derivedPushforwardToTopSingle [QuasiCompact f] [QuasiSeparated f] (d : ℕ)
    (hvan : ∀ i : ℤ, (d : ℤ) < i → ∀ F : X.Modules, F.IsQuasicoherent →
      IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus i).obj F))
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    [F.IsQuasicoherent] (i : ℤ) (hi : (d : ℤ) ≤ i) :
    IsIso ((homologyFunctor (Modules Y.toRingedSpace.sheaf) i).map
      (derivedPushforwardToTopSingle f d hvan F)) := by
  have h1 := DerivedCategory.isIso_homologyMap_truncGEπ_app (d : ℤ) i hi
    ((derivedPushforward f.toLRSHom.toShHom).obj ((singleFunctor
        (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj F))
  have h2 : IsIso ((homologyFunctor (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) i).map
      (truncGEIsoSingleHomology _ (d : ℤ)
      (isLE_derivedPushforward_single_of_vanishing f d hvan F)).hom) := inferInstance
  exact (homologyFunctor
      (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) i).map_comp _ _ ▸
    IsIso.comp_isIso' h1 h2

/-- **The left-hand read-off**: `Hᵈ(Rf_*(F[0]) ⊗^L G[0]) ≅ Rᵈ f_* F ⊗ G`. -/
def homologyDerivedPushforwardTensorIso [QuasiCompact f] [QuasiSeparated f] (d : ℕ)
    (hvan : ∀ i : ℤ, (d : ℤ) < i → ∀ F : X.Modules, F.IsQuasicoherent →
      IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus i).obj F))
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) [F.IsQuasicoherent]
    (G : SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) [G.IsQuasicoherent] :
    (homologyFunctor (Modules Y.toRingedSpace.sheaf) (d : ℤ)).obj
        (((derivedTensorProductFunctor Y.toRingedSpace.sheaf).obj
          ((derivedPushforward f.toLRSHom.toShHom).obj ((singleFunctor
              (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj F))).obj
          ((singleFunctor (Modules Y.toRingedSpace.sheaf) 0).obj G)) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor Y.toRingedSpace.sheaf).obj
        ((homologyFunctor (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) (d : ℤ)).obj
          ((derivedPushforward f.toLRSHom.toShHom).obj ((singleFunctor
              (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj F)))).obj
        G :=
  @asIso _ _ _ _ ((homologyFunctor (Modules Y.toRingedSpace.sheaf) (d : ℤ)).map
      ((derivedTensorSingle Y.toRingedSpace.sheaf G).map
        (derivedPushforwardToTopSingle f d hvan F)))
    (isIso_homologyMap_derivedTensorSingle_of_isIso Y.toRingedSpace.sheaf
      (derivedPushforwardToTopSingle f d hvan F) G (d : ℤ)
      (isIso_homologyMap_derivedPushforwardToTopSingle f d hvan F) (d : ℤ) le_rfl) ≪≫
    degreeSingleLeftTensorIso Y.toRingedSpace.sheaf _ G (d : ℤ)

/-- The derived pullback of a module placed in degree `0` lives in degrees `≤ 0`. -/
private theorem isLE_derivedPullback_single_zero
    (G : SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) :
    ((derivedPullback f.toLRSHom.toShHom).obj
      ((singleFunctor (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) 0).obj G)).IsLE 0 :=
  isLE_derivedPullback_obj f.toLRSHom.toShHom _ 0 (isLE_singleFunctor_zero G)

/-- `tensorDerivedPullbackToSingle` is an isomorphism on `H⁰`: the derived-to-ordinary pullback
comparison is an isomorphism on `H⁰` and above, which tensoring with `F[0]` preserves in degree
`0`, and the derived-to-ordinary tensor comparison is an isomorphism on `H⁰`. -/
theorem isIso_homologyMap_zero_tensorDerivedPullbackToSingle
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (G : SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) :
    IsIso ((homologyFunctor (Modules X.toRingedSpace.sheaf) 0).map
      (tensorDerivedPullbackToSingle f F G)) := by
  have hle := isLE_derivedPullback_single_zero f G
  have hF : ((singleFunctor (Modules X.toRingedSpace.sheaf) 0).obj F).IsLE 0 :=
    isLE_singleFunctor_zero (C := Modules X.toRingedSpace.sheaf) F
  have h1 : IsIso ((homologyFunctor (Modules X.toRingedSpace.sheaf) 0).map
      (((derivedTensorProductFunctor X.toRingedSpace.sheaf).obj
        ((singleFunctor (Modules X.toRingedSpace.sheaf) 0).obj F)).map
        (derivedToOrdinaryPullbackSingle f.toLRSHom.toShHom G 0))) := by
    refine @isIso_homologyMap_tensorObj_map_of_approximation _ _ _ X.toRingedSpace.sheaf _ _ _
      _ _ _ ((singleFunctor (Modules X.toRingedSpace.sheaf) 0).obj F) 0 hF _ _ _ (-1)
      (fun i hi => ?_) ?_ 0 (by omega)
    · rcases (show (0 : ℤ) ≤ i by omega).eq_or_lt with rfl | hlt
      · have h := isIso_homologyDerivedPullbackSingleMap f.toLRSHom.toShHom G 0
        unfold homologyDerivedPullbackSingleMap at h
        exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ (Iso.isIso_hom _) h
      · exact ⟨0, (DerivedCategory.isZero_of_isLE _ 0 i hlt (hX := hle)).eq_of_src _ _,
          (DerivedCategory.isZero_of_isLE ((singleFunctor
              (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj _) 0 i
            hlt).eq_of_src _ _⟩
    · exact (DerivedCategory.isZero_of_isGE ((singleFunctor
        (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj _) 0 (-1)
        (by omega)).epi _
  have h2 : IsIso ((homologyFunctor (Modules X.toRingedSpace.sheaf) 0).map
      (tensorSingleToSingle X.toRingedSpace.sheaf F
        ((RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom).obj G))) := by
    have h := homologyMap_tensorSingleToSingle X.toRingedSpace.sheaf F
      ((RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom).obj G)
    have h' := isIso_degreeZeroTensorMap X.toRingedSpace.sheaf
      ((RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom).obj G) F
    rw [← h] at h'
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ (Iso.isIso_hom _) h'
  exact ((homologyFunctor (Modules X.toRingedSpace.sheaf) 0).map_comp _ _).symm ▸
    IsIso.comp_isIso' h1 h2

/-- **The right-hand read-off**: `Hᵈ(Rf_*` of the comparison
`F[0] ⊗^L Lf^*(G[0]) ⟶ (F ⊗ f^* G)[0])` is an isomorphism. -/
theorem isIso_homologyMap_derivedPushforward_tensorDerivedPullbackToSingle
    [QuasiCompact f] [QuasiSeparated f] (d : ℕ)
    (hvan : ∀ i : ℤ, (d : ℤ) < i → ∀ F : X.Modules, F.IsQuasicoherent →
      IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus i).obj F))
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) [F.IsQuasicoherent]
    (G : SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) [G.IsQuasicoherent] :
    IsIso ((homologyFunctor (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) (d : ℤ)).map
      ((derivedPushforward f.toLRSHom.toShHom).map (tensorDerivedPullbackToSingle f F G))) := by
  have hG := isDQCoh_singleFunctor G ‹_›
  have hF := isDQCoh_singleFunctor F ‹_›
  have hcoh := Stacks.Cohomology.ProjectionFormulaQCohCoproducts.isDQCoh_derivedTensor_obj X _ _
    hF (Stacks.Cohomology.ProjectionFormulaQCohCoproducts.isDQCoh_derivedPullback_obj f _ hG)
  have hle := isLE_derivedPullback_single_zero f G
  have hF0 : ((singleFunctor (Modules X.toRingedSpace.sheaf) 0).obj F).IsLE 0 :=
    isLE_singleFunctor_zero (C := Modules X.toRingedSpace.sheaf) F
  have hE := @isLE_derivedTensorProductFunctor _ _ _ X.toRingedSpace.sheaf _ _ _ _ _ _
    ((singleFunctor (Modules X.toRingedSpace.sheaf) 0).obj F)
    ((derivedPullback f.toLRSHom.toShHom).obj ((singleFunctor
        (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) 0).obj G)) 0 0 hF0 hle
  exact isIso_homology_derivedPushforward_map_of_isIso_homology_zero f d hvan hcoh hE _
    (tensorDerivedPullbackToSingle f F G)
    (isIso_homologyMap_zero_tensorDerivedPullbackToSingle f F G) (d : ℤ) le_rfl

/-- **Conclusion (b) of [Stacks, Tag 0EX3] for an arbitrary base.** For `f` quasi-compact and
quasi-separated with `Rⁱ f_* = 0` on quasi-coherent modules for `i > d`, and `F`, `G`
quasi-coherent,

`Rᵈ f_*(F ⊗_{𝒪_X} f^* G) ≅ Rᵈ f_* F ⊗_{𝒪_Y} G`,

with `Rᵈ f_*` read as the degree-`d` cohomology of the derived direct image of a module placed
in degree `0`. The isomorphism is the composite of canonical maps: `Hᵈ(Rf_*)` of the comparison
`F[0] ⊗^L Lf^*(G[0]) ⟶ (F ⊗ f^* G)[0]`, the projection formula morphism of [Stacks, Tag 0B53]
(invertible by [Stacks, Tag 08EU]), and the top-degree read-off
`homologyDerivedPushforwardTensorIso`. -/
def topDegreeTensorIso [QuasiCompact f] [QuasiSeparated f] (d : ℕ)
    (hvan : ∀ i : ℤ, (d : ℤ) < i → ∀ F : X.Modules, F.IsQuasicoherent →
      IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus i).obj F))
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) [F.IsQuasicoherent]
    (G : SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) [G.IsQuasicoherent] :
    (homologyFunctor (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) (d : ℤ)).obj
        ((derivedPushforward f.toLRSHom.toShHom).obj ((singleFunctor
            (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj
          (((Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf).obj F).obj
            ((RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom).obj G)))) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor Y.toRingedSpace.sheaf).obj
        ((homologyFunctor (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) (d : ℤ)).obj
          ((derivedPushforward f.toLRSHom.toShHom).obj ((singleFunctor
              (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj F)))).obj
        G :=
  (@asIso _ _ _ _ ((homologyFunctor (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))
      (d : ℤ)).map
      ((derivedPushforward f.toLRSHom.toShHom).map (tensorDerivedPullbackToSingle f F G)))
    (isIso_homologyMap_derivedPushforward_tensorDerivedPullbackToSingle f d hvan F G)).symm ≪≫
    ((homologyFunctor (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) (d : ℤ)).mapIso
      (@asIso _ _ _ _ (Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap
        f.toLRSHom.toShHom
        ((singleFunctor (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj F)
        ((singleFunctor (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) 0).obj G))
        (Stacks.Cohomology.ProjectionFormulaQCoh.isIso_projectionFormulaMap_of_isDQCoh f
          ((singleFunctor (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj F)
          ((singleFunctor (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) 0).obj G)
          (isDQCoh_singleFunctor F ‹_›) (isDQCoh_singleFunctor G ‹_›)))).symm ≪≫
    homologyDerivedPushforwardTensorIso f d hvan F G

end TopDegree

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation

open Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.Cohomology.ProjectionFormulaPerfect.hasSheafifyOpens
  Stacks.Cohomology.ProjectionFormulaPerfect.wEqualsLocallyBijectiveOpens

variable (S : TopDegreeBaseChangeSituation.{u})

/-- **Conclusion (b) of [Stacks, Tag 0EX3].** In a top-degree base-change situation, for `F'`
quasi-coherent on `X'` and `G'` quasi-coherent on `Y'`,

`Rᵈ f'_*(F' ⊗_{𝒪_{X'}} (f')^* G') ≅ Rᵈ f'_* F' ⊗_{𝒪_{Y'}} G'`.

No hypothesis is placed on `Y'`: the base-changed morphism `f'` is quasi-compact and
quasi-separated (`quasiCompact_f'`, `quasiSeparated_f'`) and its higher direct images vanish
above `d` by conclusion (a), `isZero_rightDerivedPlus_pushforward_baseChange`, so this is
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.topDegreeTensorIso` for `f'`. Over an affine `Y'`
the same conclusion is read on global sections by `TopDegreeBaseChangeSituation.topDegreeTensorIso`
(`EilenbergWattsSituation.lean`). -/
@[stacks 0EX3 "(b)"]
def topDegreeTensorSheafIso
    (F' : SheafOfModules.{u} (structureSheafRing S.X'.toRingedSpace)) [F'.IsQuasicoherent]
    (G' : SheafOfModules.{u} (structureSheafRing S.Y'.toRingedSpace)) [G'.IsQuasicoherent] :
    (homologyFunctor (SheafOfModules.{u} (structureSheafRing S.Y'.toRingedSpace)) (S.d : ℤ)).obj
        ((derivedPushforward S.f'.toLRSHom.toShHom).obj
          ((singleFunctor (SheafOfModules.{u} (structureSheafRing S.X'.toRingedSpace)) 0).obj
            (((Stacks.SheafOfModules.Tensor.sheafTensor S.X'.toRingedSpace.sheaf).obj F').obj
              ((RingedSpaceModuleAdjunction.modulePullback S.f'.toLRSHom.toShHom).obj G')))) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor S.Y'.toRingedSpace.sheaf).obj
        ((homologyFunctor (SheafOfModules.{u} (structureSheafRing S.Y'.toRingedSpace))
            (S.d : ℤ)).obj
          ((derivedPushforward S.f'.toLRSHom.toShHom).obj
            ((singleFunctor (SheafOfModules.{u} (structureSheafRing S.X'.toRingedSpace)) 0).obj
              F')))).obj
        G' :=
  have := S.quasiCompact_f'
  have := S.quasiSeparated_f'
  Stacks.AlgebraicGeometry.TopDegreeBaseChange.topDegreeTensorIso S.f' S.d
    (fun i hi F hF => by
      have : F.IsQuasicoherent := hF
      exact isZero_rightDerivedPlus_pushforward_baseChange S i hi F)
    F' G'

end Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation
