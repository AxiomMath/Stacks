module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.Algebra.Homology.RestrictScalarsHomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ConstructibleFlatSliceFiniteTor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ConstructibleFlatOfFlatStalks
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtfOpenClosed
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ShriekSumResolution
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.Stalks
public import StacksFrontier.Homology.TorAmplitude.DerivedComparison
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Open
import StacksCore.Tactic.EgaSgaAttribute

/-!
# An object of `D_ctf` is represented by a finite complex of constructible flat sheaves

This file proves the direction (1) ⟹ (2) of [Stacks, Tag 03TT], with the bound of its last
sentence, and with it the equivalence of (1) and (2).

## Main results

In the namespace `Stacks.EtaleCohomology`:

* `exists_constructibleFlat_representative_of_hasTorAmplitude` — on a quasi-compact and
  quasi-separated `X`, an object of `D_ctf(X_étale, Λ)` of Tor amplitude in `[a, b]` is represented
  by a complex of constructible flat sheaves concentrated in degrees `[a, b]`.
* `exists_constructibleFiniteTor_iff_isRepresentedByConstructibleFlatComplex` — an object of
  `D(X_étale, Λ)` lies in `D_ctf(X_étale, Λ)` if and only if it is represented by a finite complex
  of constructible flat sheaves.

## References

* [Stacks Project, Tag 03TT](https://stacks.math.columbia.edu/tag/03TT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ZeroObject

universe u r d

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
  GrothendieckTopology.hasSheafify_addCommGrpCat
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat
  Stacks.hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.RingedSite.sliceHasSheafify
  AlgebraicGeometry.RingedSite.sliceWEqualsLocallyBijective
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteLimits
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteColimits
  SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [CommRing Λ]

/-! ### A fibre functor factoring through a stalk of modules -/

/-- A module over a ring `R'` is flat as soon as its restriction of scalars along a ring
isomorphism `Λ ≃+* R'` is a flat `Λ`-module. -/
theorem flat_of_flat_restrictScalars_ringEquiv {R' : CommRingCat.{max (u + 1) r}} (E : Λ ≃+* R')
    (N : ModuleCat.{max (u + 1) r} R')
    (h : Module.Flat Λ ((ModuleCat.restrictScalars E.toRingHom).obj N)) : Module.Flat R' N := by
  let N' := (ModuleCat.restrictScalars E.toRingHom).obj N
  exact flat_of_semilinear_equiv (R := R') (S := Λ) (N₀ := N) (N₁ := N')
    E.symm (AddEquiv.refl N) (fun c m => by
      change c • m = E (E.symm c) • m
      rw [RingEquiv.apply_symm_apply])

/-- Restriction of scalars along a ring isomorphism `Λ ≃+* R'` preserves flatness. -/
theorem flat_restrictScalars_ringEquiv {R' : CommRingCat.{max (u + 1) r}} (E : Λ ≃+* R')
    (N : ModuleCat.{max (u + 1) r} R') [Module.Flat R' N] :
    Module.Flat Λ ((ModuleCat.restrictScalars E.toRingHom).obj N) :=
  flat_of_semilinear_equiv (S := R') (N₁ := N) E (AddEquiv.refl N) (fun _ _ => rfl)

/-- Canonical Tor amplitude in `[a, b]` is invariant under isomorphism in the derived category. -/
private theorem hasTorAmplitudeCanonical_of_iso {R : Type*} [CommRing R]
    {E F : DerivedCategory (ModuleCat R)} (e : E ≅ F) (a b : ℤ)
    (h : StacksDraft.TorAmplitude.HasTorAmplitudeCanonical R E a b) :
    StacksDraft.TorAmplitude.HasTorAmplitudeCanonical R F a b := by
  rw [StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_iff_hasFlatRepresentative] at h ⊢
  exact StacksDraft.TorAmplitude.hasFlatRepresentative_of_iso e h

omit [CommRing Λ] in
/-- **Canonical Tor amplitude of a stalk complex, read at the fibre of a point.** Let `Ψ` be a
point of the small étale site and `G` an exact functor from sheaves of `Λ`-modules to modules
over a ring `R'` such that, after restriction of scalars along a ring isomorphism `Λ ≃+* R'`, `G`
applied degreewise is the fibre at `Ψ`. If `G` applied to a complex `C` has canonical Tor
amplitude in `[a, b]`, then the fibre at `Ψ` of every cohomology sheaf of `C` outside `[a, b]`
vanishes, and if `C` is a bounded above complex with flat fibres at `Ψ`, the fibre at `Ψ` of the
cokernel of the differential into degree `a` is flat. -/
theorem fiber_of_hasTorAmplitudeCanonical [CommRing Λ] {R' : CommRingCat.{max (u + 1) r}}
    (E : Λ ≃+* R')
    (G : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ) ⥤
      ModuleCat.{max (u + 1) r} R')
    [G.PreservesZeroMorphisms]
    [HasSheafify (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ)]
    (Ψ : (SmallEtale.topology B X.obj X.property).Point.{max (u + 1) r})
    (eN : (Ψ.sheafFiber (A := ModuleCat.{max (u + 1) r} Λ)).mapHomologicalComplex
        (ComplexShape.up ℤ) ≅
      (G ⋙ ModuleCat.restrictScalars E.toRingHom).mapHomologicalComplex (ComplexShape.up ℤ))
    (C : CochainComplex
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ)) ℤ)
    (a b : ℤ)
    (hD : StacksDraft.TorAmplitude.HasTorAmplitudeCanonical R'
      (DerivedCategory.Q.obj ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj C)) a b) :
    (∀ i : ℤ, i ∉ Set.Icc a b →
        IsZero ((Ψ.sheafFiber (A := ModuleCat.{max (u + 1) r} Λ)).obj (C.homology i))) ∧
      (CochainComplex.minus _ C →
        (∀ n : ℤ, Module.Flat Λ ((Ψ.sheafFiber (A := ModuleCat.{max (u + 1) r} Λ)).obj (C.X n))) →
        Module.Flat Λ (cokernel ((Ψ.sheafFiber (A := ModuleCat.{max (u + 1) r} Λ)).map
          (C.d (a - 1) a)) : ModuleCat.{max (u + 1) r} Λ)) := by
  let rs := ModuleCat.restrictScalars.{max (u + 1) r} E.toRingHom
  let D := (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj C
  let eC : ((Ψ.sheafFiber (A := ModuleCat.{max (u + 1) r} Λ)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj C ≅ (rs.mapHomologicalComplex (ComplexShape.up ℤ)).obj D :=
    eN.app C
  have : (Ψ.sheafFiber (A := ModuleCat.{max (u + 1) r} Λ)).Additive :=
    Functor.additive_of_preserves_binary_products _
  have hrep := (StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_iff_hasFlatRepresentative
    _ _ a b).1 hD
  obtain ⟨F', -, hge, hle, ⟨eF⟩⟩ := id hrep
  refine ⟨fun i hi => ?_, fun hminus hflat => ?_⟩
  · have hz : IsZero (D.homology i) := by
      have : (DerivedCategory.Q.obj D).IsGE a := DerivedCategory.TStructure.t.isGE_of_iso eF.symm a
      have : (DerivedCategory.Q.obj D).IsLE b := DerivedCategory.TStructure.t.isLE_of_iso eF.symm b
      simp only [Set.mem_Icc, not_and_or, not_le] at hi
      have h' : IsZero ((DerivedCategory.homologyFunctor _ i).obj (DerivedCategory.Q.obj D)) := by
        rcases hi with hi | hi
        · exact DerivedCategory.isZero_of_isGE _ a i hi
        · exact DerivedCategory.isZero_of_isLE _ b i hi
      exact h'.of_iso ((DerivedCategory.homologyFunctorFactors _ i).app D).symm
    have h1 : IsZero (((rs.mapHomologicalComplex (ComplexShape.up ℤ)).obj D).homology i) :=
      (rs.map_isZero hz).of_iso
        (Stacks.Homology.RestrictScalars.mapHomologicalComplexHomologyIso rs D i)
    have h2 : IsZero ((((Ψ.sheafFiber (A := ModuleCat.{max (u + 1) r} Λ)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj C).homology i) :=
      h1.of_iso (HomologicalComplex.homologyMapIso eC i)
    exact h2.of_iso (Stacks.Homology.RestrictScalars.mapHomologicalComplexHomologyIso
      (Ψ.sheafFiber (A := ModuleCat.{max (u + 1) r} Λ)) C i).symm
  · obtain ⟨M, hM⟩ := hminus
    have hbd : StacksDraft.TorAmplitude.BoundedAbove D :=
      ⟨M, fun n hn => G.map_isZero (C.isZero_of_isStrictlyLE M n hn)⟩
    have hflatD : ∀ n : ℤ, Module.Flat R' (D.X n) := fun n =>
      flat_of_flat_restrictScalars_ringEquiv.{u, r} Λ E (D.X n)
        (by
          let en : (Ψ.sheafFiber (A := ModuleCat.{max (u + 1) r} Λ)).obj (C.X n) ≅ rs.obj (D.X n) :=
            (HomologicalComplex.eval _ (ComplexShape.up ℤ) n).mapIso eC
          have := hflat n
          exact Module.Flat.of_linearEquiv en.symm.toLinearEquiv)
    have hgen : StacksDraft.TorAmplitude.HasTorAmplitude
        (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R').tensor
        (StacksDraft.TorAmplitude.canonicalTensorComparison R')
        (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived R')
        (DerivedCategory.Q.obj D) a b :=
      (StacksDraft.TorAmplitude.hasTorAmplitude_iff_hasFlatRepresentative
        (StacksDraft.TorAmplitude.canonicalTensorComparison R')
        (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived R') _ a b).2
        hrep
    have hcok := StacksDraft.TorAmplitude.cokernel_flat_of_torAmplitude.{max (u + 1) r, 0}
      D a b hbd hflatD hgen
    have h1 : Module.Flat Λ (rs.obj (cokernel (D.d (a - 1) a))) :=
      flat_restrictScalars_ringEquiv.{u, r} Λ E _
    let e2 : cokernel ((Ψ.sheafFiber (A := ModuleCat.{max (u + 1) r} Λ)).map (C.d (a - 1) a)) ≅
        cokernel (rs.map (D.d (a - 1) a)) :=
      cokernel.mapIso _ _ ((HomologicalComplex.eval _ (ComplexShape.up ℤ) (a - 1)).mapIso eC)
        ((HomologicalComplex.eval _ (ComplexShape.up ℤ) a).mapIso eC) (eC.hom.comm (a - 1) a).symm
    exact Module.Flat.of_linearEquiv (e2 ≪≫ (PreservesCokernel.iso rs _).symm).toLinearEquiv

/-! ### The fibre at a point, read on a slice -/

/-- The stalk at `Ψ.over y` of the restriction to the slice over `V` of the constant coefficient
ring sheaf. -/
abbrev sliceStalkRing (Ψ : (SmallEtale.topology B X.obj X.property).Point.{max (u + 1) r})
    {V : SmallEtale B X.obj X.property} (y : Ψ.fiber.obj V) : CommRingCat.{max (u + 1) r} :=
  ((Ψ.over y).presheafFiber (A := CommRingCat.{max (u + 1) r})).obj
    ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over V).O.obj

/-! ### Tor amplitude on a slice, read at the fibre of a point -/

variable [IsNoetherianRing Λ]
  [HasSheafify (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ)]
  [HasDerivedCategory.{d} (RingedSite.Modules.{u + 1, u, max (u + 1) r}
    (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ))]
  [hSliceDerived : ∀ U : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C,
    HasDerivedCategory.{d} (RingedSite.Modules.{u + 1, u, max (u + 1) r}
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over U))]
  [∀ U : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C,
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) r, max (u + 1) r,
      max (u + 1) r}
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over U).O).Additive]
  [∀ (U : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) r, max (u + 1) r,
      max (u + 1) r}
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over U).O).obj M).Additive]
  [∀ (U : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C)
    (K L : CochainComplex (RingedSite.Modules.{u + 1, u, max (u + 1) r}
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor
        ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over U).O)
      (ComplexShape.up ℤ)]

attribute [local instance] Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor
  AlgebraicGeometry.RingedSite.sliceHasDerivedCategory


omit [IsNoetherianRing Λ] in
open Stacks.SheafOfModules.DerivedTensorProduct in
/-- **Tor amplitude on a slice, read at the fibre of a point.** Let `K` be an object of
`D(X_étale, Λ)` represented by a complex `C`, and let `Ψ` be a point of the small étale site
lifting to `y` over `V`. If the restriction to the slice over `V` of the associated object of
`D(𝒪)` has Tor amplitude in `[a, b]`, then the fibre at `Ψ` of every cohomology sheaf of `C`
outside `[a, b]` vanishes, and if `C` is a bounded above complex with flat fibres at `Ψ`, the
fibre at `Ψ` of the cokernel of the differential into degree `a` is flat. -/
theorem fiber_of_hasTorAmplitude_derivedRestriction
    (T : ∀ U : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, max (u + 1) r, d}
        ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over U))
    (K : DerivedCategory
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ)))
    (C : CochainComplex
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ)) ℤ)
    (eC : DerivedCategory.Q.obj C ≅ K)
    (Ψ : (SmallEtale.topology B X.obj X.property).Point.{max (u + 1) r})
    {V : SmallEtale B X.obj X.property} (y : Ψ.fiber.obj V) (a b : ℤ)
    (hamp : HasTorAmplitude (T V)
      ((RingedSite.derivedRestriction.{u + 1, u, max (u + 1) r, d}
        (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ) V).obj
          ((moduleSheafOverConstantCoefficientsFunctor.{u, max (u + 1) r, r}
            B X Λ).mapDerivedCategory.obj K)) a b) :
    (∀ i : ℤ, i ∉ Set.Icc a b →
        IsZero ((Ψ.sheafFiber (A := ModuleCat.{max (u + 1) r} Λ)).obj (C.homology i))) ∧
      (CochainComplex.minus _ C →
        (∀ n : ℤ, Module.Flat Λ ((Ψ.sheafFiber (A := ModuleCat.{max (u + 1) r} Λ)).obj (C.X n))) →
        Module.Flat Λ (cokernel ((Ψ.sheafFiber (A := ModuleCat.{max (u + 1) r} Λ)).map
          (C.d (a - 1) a)) : ModuleCat.{max (u + 1) r} Λ)) := by
  let : HasDerivedCategory.{d} (SheafOfModules.{max (u + 1) r}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).O).over V)) :=
    hSliceDerived V
  let hd : HasDerivedCategory.{d} (SheafOfModules.{max (u + 1) r}
      (Stacks.commRingSheafToRingSheaf.{u, u + 1, max (u + 1) r}
        ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over V).O)) :=
    hSliceDerived V
  let Φ := moduleSheafOverConstantCoefficientsFunctor.{u, max (u + 1) r, r} B X Λ
  let ρ := SheafOfModules.overFunctor
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).O) V
  let G : SheafOfModules.{max (u + 1) r} (Stacks.commRingSheafToRingSheaf.{u, u + 1, max (u + 1) r}
        ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over V).O) ⥤
      ModuleCat.{max (u + 1) r} (sliceStalkRing B X Λ Ψ y) :=
    Stacks.sheafModuleFiberOfCommRing (Ψ.over y)
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over V).O
  have : (Φ ⋙ ρ ⋙ G).PreservesZeroMorphisms := ⟨fun _ _ => by
    change G.map (ρ.map (Φ.map 0)) = 0
    rw [Φ.map_zero, ρ.map_zero]
    exact G.map_zero _ _⟩
  refine fiber_of_hasTorAmplitudeCanonical B X Λ
    (constantCoefficientRingOverFiberEquiv.{u, max (u + 1) r, r} B X Λ Ψ y) (Φ ⋙ ρ ⋙ G) Ψ
    (moduleSheafOverConstantCoefficientsSheafFiberComplexIso B X Λ Ψ y) C a b ?_
  have h0 := hasTorAmplitudeCanonical_derivedModuleFiber
    (Y := (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over V)
    (T V) _ a b hamp (Ψ.over y)
  refine hasTorAmplitudeCanonical_of_iso ?_ a b h0
  exact (Functor.mapDerivedCategory.{d} G).mapIso
      (((Functor.mapDerivedCategoryFactors.{d, d} ρ).app _).symm ≪≫
        (RingedSite.derivedRestriction.{u + 1, u, max (u + 1) r, d}
          (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ) V).mapIso
          (((Functor.mapDerivedCategoryFactors.{_, d} Φ).app C).symm ≪≫
            Φ.mapDerivedCategory.mapIso eC)).symm ≪≫
    (Functor.mapDerivedCategoryFactors.{d, _} G).app _

/-! ### One interval for all geometric points of a quasi-compact scheme -/

omit [IsNoetherianRing Λ]
  [HasSheafify (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ)] in
open Stacks.SheafOfModules.DerivedTensorProduct in
/-- **One Tor-amplitude interval serves every geometric point of a quasi-compact scheme.** If an
object `E` of `D(𝒪)` locally has finite Tor dimension and `X` is quasi-compact, there are
integers `a, b` such that every geometric point `s` of `X` lifts to an object `V` of the small
étale site over which `E` has Tor amplitude in `[a, b]`. -/
theorem exists_uniform_hasTorAmplitude_derivedRestriction [CompactSpace X.obj]
    (T : ∀ U : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, max (u + 1) r, d}
        ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over U))
    (E : RingedSite.DerivedModules.{u + 1, u, max (u + 1) r, d}
      (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ))
    (hE : LocallyHasFiniteTorDimension
      (X := constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ) T E) :
    ∃ a b : ℤ, ∀ s : GeometricPoint X.obj, ∃ (V : SmallEtale B X.obj X.property)
      (_ : ((geometricSitePoint B X s).ulift.{max (u + 1) r}).fiber.obj V),
      HasTorAmplitude (T V) ((RingedSite.derivedRestriction.{u + 1, u, max (u + 1) r, d}
        (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ) V).obj E) a b := by
  classical
  have key : ∀ x : X.obj, ∃ (V : SmallEtale B X.obj X.property) (a b : ℤ),
      x ∈ Set.range (B.inclusion.map V.obj.hom) ∧
      HasTorAmplitude (T V) ((RingedSite.derivedRestriction.{u + 1, u, max (u + 1) r, d}
        (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ) V).obj E) a b := by
    intro x
    let Ψ := (geometricSitePoint B X (.ofPoint X.obj x)).ulift.{max (u + 1) r}
    obtain ⟨P⟩ := IsCofiltered.nonempty (C := Ψ.fiber.Elements)
    obtain ⟨V, -, y, a, b, -, hab⟩ :=
      exists_hasTorAmplitude_derivedRestriction_of_point T E hE Ψ P.val
    refine ⟨V, a, b, ⟨y.down.1 default, ?_⟩, hab⟩
    have h := congrArg (fun g => g default) y.down.2
    simp only [Scheme.Hom.comp_apply] at h
    exact h.trans (GeometricPoint.ofPoint_liesOver X.obj x)
  choose V a b hx hab using key
  let O : X.obj → Set X.obj := fun x => Set.range (B.inclusion.map (V x).obj.hom)
  have hO : ∀ x, IsOpen (O x) := fun x =>
    (B.inclusion.map (V x).obj.hom).isOpenMap.isOpen_range
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover O hO
    (fun x _ => Set.mem_iUnion.2 ⟨x, hx x⟩)
  refine ⟨-∑ x ∈ S, |a x|, ∑ x ∈ S, |b x|, fun s => ?_⟩
  obtain ⟨x, hxS, v, hv⟩ := Set.mem_iUnion₂.1 (hS (Set.mem_univ (s.hom default)))
  obtain ⟨l, hl, -⟩ := Scheme.exists_fac_of_etale_of_isSepClosed
    (B.inclusion.map (V x).obj.hom) s.hom v hv
  refine ⟨V x, ULift.up ⟨l, hl⟩, (hab x).mono ?_ ?_⟩
  · have h1 := Finset.single_le_sum (f := fun x => |a x|) (fun _ _ => abs_nonneg _) hxS
    have h2 := neg_abs_le (a x)
    linarith
  · have h1 := Finset.single_le_sum (f := fun x => |b x|) (fun _ _ => abs_nonneg _) hxS
    have h2 := le_abs_self (b x)
    linarith

/-! ### Fibres at geometric points -/

/-- The fibre at the universe lift of the point of a geometric point is the étale stalk, at the
module universe `max (u + 1) r`. -/
def uliftGeometricSitePointFiberIso (s : GeometricPoint X.obj)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ)) :
    ((geometricSitePoint B X s).ulift.{max (u + 1) r}.sheafFiber
        (A := ModuleCat.{max (u + 1) r} Λ)).obj F ≅
      (etaleModuleStalkFunctor.{u, max (u + 1) r, r} B X Λ s).obj F :=
  ((upliftedEtaleFiberFunctorIso B X Λ _).app F).symm ≪≫
    upliftedEtaleFiberIso.{u, max (u + 1) r, r} B X Λ s F ≪≫
    (moduleCatUliftFunctorIdIso Λ).app _

omit [IsNoetherianRing Λ]
  [HasDerivedCategory.{d} (RingedSite.Modules.{u + 1, u, max (u + 1) r}
    (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ))] hSliceDerived
  [∀ U : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C,
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) r, max (u + 1) r,
      max (u + 1) r}
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over U).O).Additive]
  [∀ (U : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) r, max (u + 1) r,
      max (u + 1) r}
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over U).O).obj M).Additive]
  [∀ (U : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C)
    (K L : CochainComplex (RingedSite.Modules.{u + 1, u, max (u + 1) r}
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor
        ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over U).O)
      (ComplexShape.up ℤ)] in
/-- A sheaf of `Λ`-modules whose fibres at the universe lifts of the geometric points of `X` vanish
is zero. -/
theorem isZero_of_isZero_uliftGeometricSitePoint_sheafFiber
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ))
    (h : ∀ x : X.obj, IsZero (((geometricSitePoint B X (.ofPoint X.obj x)).ulift.{max (u + 1) r}
      ).sheafFiber (A := ModuleCat.{max (u + 1) r} Λ) |>.obj F)) :
    IsZero F := by
  have hP := isConservativeFamilyOfPoints_uliftGeometricSitePoint.{u, max (u + 1) r, r} B X
  let : PreservesFilteredColimits (forget (ModuleCat.{max (u + 1) r} Λ)) :=
    comp_preservesFilteredColimits
      (forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat) (forget AddCommGrpCat)
  let f : F ⟶ 0 := 0
  have : ∀ Φ : (ObjectProperty.ofObj (fun x : ↥X.obj =>
      (geometricSitePoint B X (.ofPoint X.obj x)).ulift.{max (u + 1) r})).FullSubcategory,
      IsIso (Φ.obj.sheafFiber.map f) := by
    rintro ⟨Φ, hΦ⟩
    obtain ⟨x⟩ := hΦ
    have : (((geometricSitePoint B X (.ofPoint X.obj x)).ulift.{max (u + 1) r}).sheafFiber
        (A := ModuleCat.{max (u + 1) r} Λ)).Additive :=
      Functor.additive_of_preserves_binary_products _
    exact isIso_of_source_target_iso_zero _ (h x).isoZero
      (Functor.map_isZero _ (isZero_zero _)).isoZero
  have : IsIso f := (hP.jointlyReflectIsomorphisms (ModuleCat.{max (u + 1) r} Λ)).isIso f
  exact (isZero_zero _).of_iso (asIso f)

variable [CompactSpace X.obj] [QuasiSeparatedSpace X.obj]

omit [HasDerivedCategory.{d} (RingedSite.Modules.{u + 1, u, max (u + 1) r}
    (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ))] hSliceDerived
  [∀ U : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C,
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) r, max (u + 1) r,
      max (u + 1) r}
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over U).O).Additive]
  [∀ (U : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) r, max (u + 1) r,
      max (u + 1) r}
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over U).O).obj M).Additive]
  [∀ (U : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C)
    (K L : CochainComplex (RingedSite.Modules.{u + 1, u, max (u + 1) r}
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor
        ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over U).O)
      (ComplexShape.up ℤ)] in
open Stacks.SheafOfModules.DerivedTensorProduct in
/-- On a quasi-compact and quasi-separated scheme, a constructible object `K` of `D(X_étale, Λ)`
such that every geometric point lifts to an object of the small étale site over which `K` has Tor
amplitude in `[a, b]` is represented by a complex of constructible flat sheaves of `Λ`-modules
concentrated in degrees `[a, b]`. -/
theorem exists_constructibleFlat_representative_of_fiber
    (K : DerivedCategory
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ)))
    (hK : IsConstructible B X Λ K) (a b : ℤ)
    (hfib : ∀ (C : CochainComplex
        (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ)) ℤ)
      (_ : DerivedCategory.Q.obj C ≅ K) (s : GeometricPoint X.obj),
      (∀ i : ℤ, i ∉ Set.Icc a b → IsZero
          ((((geometricSitePoint B X s).ulift.{max (u + 1) r}).sheafFiber
            (A := ModuleCat.{max (u + 1) r} Λ)).obj (C.homology i))) ∧
        (CochainComplex.minus _ C →
          (∀ n : ℤ, Module.Flat Λ ((((geometricSitePoint B X s).ulift.{max (u + 1) r}).sheafFiber
            (A := ModuleCat.{max (u + 1) r} Λ)).obj (C.X n))) →
          Module.Flat Λ (cokernel ((((geometricSitePoint B X s).ulift.{max (u + 1) r}).sheafFiber
            (A := ModuleCat.{max (u + 1) r} Λ)).map (C.d (a - 1) a)) :
              ModuleCat.{max (u + 1) r} Λ))) :
    ∃ F : CochainComplex
        (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ)) ℤ,
      F.IsStrictlyGE a ∧ F.IsStrictlyLE b ∧
        (∀ i : ℤ, IsConstructibleFlatModuleSheaf B X Λ (F.X i)) ∧
        Nonempty (DerivedCategory.Q.obj F ≅ K) := by
  let 𝒜 := Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ)
  let Ψ : GeometricPoint X.obj → (SmallEtale.topology B X.obj X.property).Point.{max (u + 1) r} :=
    fun s => (geometricSitePoint B X s).ulift.{max (u + 1) r}
  have hvan : ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((DerivedCategory.homologyFunctor 𝒜 i).obj K) := by
    intro i hi
    let C₀ := DerivedCategory.Q.objPreimage K
    let e₀ : DerivedCategory.Q.obj C₀ ≅ K := DerivedCategory.Q.objObjPreimageIso K
    have hC₀ : IsZero (C₀.homology i) :=
      isZero_of_isZero_uliftGeometricSitePoint_sheafFiber B X Λ _
        fun x => (hfib C₀ e₀ (.ofPoint X.obj x)).1 i (by simp only [Set.mem_Icc]; omega)
    exact hC₀.of_iso ((DerivedCategory.homologyFunctor 𝒜 i).mapIso e₀.symm ≪≫
      (DerivedCategory.homologyFunctorFactors 𝒜 i).app C₀)
  have hKLE : K.IsLE b := by
    rw [DerivedCategory.isLE_iff]
    exact fun i hi => hvan i (.inr hi)
  have hKGE : K.IsGE a := by
    rw [DerivedCategory.isGE_iff]
    exact fun i hi => hvan i (.inl hi)
  by_cases hab : a ≤ b
  swap
  · have hKz : IsZero K := DerivedCategory.TStructure.t.isZero K b a (by omega)
    have h0 : ∀ i, IsZero ((0 : CochainComplex 𝒜 ℤ).X i) := fun i =>
      (HomologicalComplex.eval _ _ i).map_isZero (isZero_zero _)
    refine ⟨0, ?_, ?_, fun i => ?_, ⟨IsZero.iso ?_ hKz⟩⟩
    · rw [CochainComplex.isStrictlyGE_iff]
      exact fun i _ => h0 i
    · rw [CochainComplex.isStrictlyLE_iff]
      exact fun i _ => h0 i
    · exact isConstructibleFlatModuleSheaf_of_isZero B Λ X _ (h0 i)
    · exact DerivedCategory.Q.map_isZero (isZero_zero _)
  have := isWeakSerreClass_isConstructibleModuleSheafProperty B X Λ
  set P := isConstructibleModuleSheafProperty.{u, max (u + 1) r, r} B X Λ with hP
  obtain ⟨A, hA, ⟨e⟩⟩ := K.exists_iso_Q_obj_of_isLE b
  have hAhom : ∀ i : ℤ, P (A.homology i) := fun i =>
    P.prop_of_iso
      ((((DerivedCategory.homologyFunctorFactors _ i).app A).symm ≪≫
        (DerivedCategory.homologyFunctor _ i).mapIso e.symm).symm) (hK i)
  obtain ⟨Y, hY, f, hf, hterms⟩ :=
    Stacks.Homology.BoundedAboveResolution.exists_quasiIso_isStrictlyLE_of_coversEpis
      P (IsAffineShriekSum.{u, r} B X Λ) A
      (coversEpis_isAffineShriekSum B X Λ)
      (isAffineShriekSum_zero B X Λ)
      (fun _ _ => isAffineShriekSum_biprod B X Λ)
      (fun _ _ g hg hM => by
        have := hg
        exact isAffineShriekSum_of_iso B X Λ (asIso g) hM)
      b hAhom
  have eY : DerivedCategory.Q.obj Y ≅ K := asIso (DerivedCategory.Q.map f) ≪≫ e.symm
  have hYflat : ∀ i : ℤ, IsConstructibleFlatModuleSheaf B X Λ (Y.X i) := fun i => by
    obtain ⟨n, U, hU, ⟨eU⟩⟩ := hterms i
    exact isConstructibleFlatModuleSheaf_congr B X Λ eU.symm
      (isConstructibleFlatModuleSheaf_sigma_moduleShriekConstant_of_quasiSeparated B X Λ U hU)
  have hcok : IsConstructibleFlatModuleSheaf B X Λ (cokernel (Y.d (a - 1) a) : 𝒜) := by
    refine isConstructibleFlatModuleSheaf_of_flat_etaleModuleStalk B X Λ _
      (P.prop_of_isColimit_cokernelCofork (colimit.isColimit _)
        (isConstructibleModuleSheaf_of_isConstructibleFlatModuleSheaf B X Λ (hYflat (a - 1)))
        (isConstructibleModuleSheaf_of_isConstructibleFlatModuleSheaf B X Λ (hYflat a)))
      (fun s => ?_)
    have hflat := (hfib Y eY s).2
      ⟨b, hY⟩ (fun n => by
        have := etaleModuleStalk_projective_of_isConstructibleFlatModuleSheaf B X Λ (Y.X n)
          (hYflat n) s
        exact Module.Flat.of_linearEquiv
          (uliftGeometricSitePointFiberIso B X Λ s (Y.X n)).toLinearEquiv)
    exact Module.Flat.of_linearEquiv ((uliftGeometricSitePointFiberIso B X Λ s _).symm ≪≫
      PreservesCokernel.iso ((Ψ s).sheafFiber (A := ModuleCat.{max (u + 1) r} Λ))
        (Y.d (a - 1) a)).toLinearEquiv
  have hYGE : Y.IsGE a := by
    rw [← DerivedCategory.isGE_Q_obj_iff]
    exact DerivedCategory.TStructure.t.isGE_of_iso eY.symm a
  have eOpCoker : Y.opcycles a ≅ (cokernel (Y.d (a - 1) a) : 𝒜) :=
    IsColimit.coconePointUniqueUpToIso
      (Y.opcyclesIsCokernel (a - 1) a (by simp)) (colimit.isColimit _)
  refine ⟨Y.truncGE a, inferInstance, ?_, fun i => ?_,
    ⟨(asIso (DerivedCategory.Q.map (Y.πTruncGE a))).symm ≪≫ eY⟩⟩
  · rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact (Y.isZero_of_isStrictlyLE b i hi).of_iso (Y.truncGEXIso a i (by omega))
  · rcases lt_trichotomy i a with hlt | heq | hgt
    · exact isConstructibleFlatModuleSheaf_of_isZero B Λ X _
        ((Y.truncGE a).isZero_of_isStrictlyGE a i hlt)
    · subst heq
      exact isConstructibleFlatModuleSheaf_congr B X Λ
        (eOpCoker.symm ≪≫ (Y.truncGEXIsoOpcycles i).symm) hcok
    · exact isConstructibleFlatModuleSheaf_congr B X Λ (Y.truncGEXIso a i hgt).symm (hYflat i)

/-! ### Tag 03TT -/

open Stacks.SheafOfModules.DerivedTensorProduct in
/-- On a quasi-compact and quasi-separated scheme, an object of `D(X_étale, Λ)` with
constructible cohomology sheaves which, read in `D(𝒪)`, locally has finite Tor dimension is
represented by a bounded complex of constructible flat sheaves of `Λ`-modules. -/
@[sga "6 I 5.5" "special case"]
theorem isRepresentedByConstructibleFlatComplex_of_locallyHasFiniteTorDimension
    (T : ∀ U : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, max (u + 1) r, d}
        ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over U))
    (K : DerivedCategory
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ)))
    (hK : IsConstructible B X Λ K)
    (hloc : LocallyHasFiniteTorDimension
      (X := constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ)
      T ((moduleSheafOverConstantCoefficientsFunctor.{u, max (u + 1) r, r}
        B X Λ).mapDerivedCategory.obj K)) :
    IsRepresentedByConstructibleFlatComplex.{u, max (u + 1) r, r} B X Λ K := by
  obtain ⟨a, b, hab⟩ := exists_uniform_hasTorAmplitude_derivedRestriction B X Λ T _ hloc
  obtain ⟨F, hGE, hLE, hF, hFK⟩ := exists_constructibleFlat_representative_of_fiber B X Λ K hK a b
    (fun C eC s => by
      obtain ⟨V, y, h⟩ := hab s
      exact fiber_of_hasTorAmplitude_derivedRestriction B X Λ T K C eC _ y a b h)
  exact ⟨F, a, b, hGE, hLE, hF, hFK⟩

/-- Let `Λ` be a Noetherian ring and `X` a quasi-compact and quasi-separated
scheme. An object `K` of `D(X_étale, Λ)` lies in `D_ctf(X_étale, Λ)` (Tag 03TQ) if and only if it
can be represented by a finite complex of constructible flat sheaves of `Λ`-modules.

`D_ctf(X_étale, Λ)` is the category of Tag 03TQ, measured against the given derived tensor
products `T` on the slices; membership of `K` is the existence of an object of that category
isomorphic to `K`. -/
@[stacks 03TT "the equivalence of (1) and (2)", sga "4½ Rapport 4.6" "special case"]
public theorem exists_constructibleFiniteTor_iff_isRepresentedByConstructibleFlatComplex
    (T : ∀ U : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, max (u + 1) r, d}
        ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over U))
    (K : DerivedCategory
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ))) :
    (∃ L : ConstructibleFiniteTorDerivedCategory.{u, max (u + 1) r, r, d} B X Λ T,
        Nonempty (L.obj.obj ≅ K)) ↔
      IsRepresentedByConstructibleFlatComplex.{u, max (u + 1) r, r} B X Λ K := by
  refine ⟨fun ⟨L, ⟨e⟩⟩ => ?_,
    exists_constructibleFiniteTor_of_isRepresentedByConstructibleFlatComplex B X Λ T K⟩
  obtain ⟨C, a, b, ha, hb, hC, ⟨eC⟩⟩ :=
    isRepresentedByConstructibleFlatComplex_of_locallyHasFiniteTorDimension B X Λ T L.obj.obj
      L.obj.property L.property
  exact ⟨C, a, b, ha, hb, hC, ⟨eC ≪≫ e⟩⟩

section GlobalAmplitude

variable
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) r, max (u + 1) r,
      max (u + 1) r} (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).O).Additive]
  [∀ M : RingedSite.Modules.{u + 1, u, max (u + 1) r}
      (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ),
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) r, max (u + 1) r,
      max (u + 1) r} (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u + 1, u, max (u + 1) r}
      (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) r, max (u + 1) r,
        max (u + 1) r} (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).O)
      (ComplexShape.up ℤ)]

omit [IsNoetherianRing Λ] hSliceDerived
  [∀ U : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C,
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) r, max (u + 1) r,
      max (u + 1) r}
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over U).O).Additive]
  [∀ (U : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) r, max (u + 1) r,
      max (u + 1) r}
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over U).O).obj M).Additive]
  [∀ (U : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C)
    (K L : CochainComplex (RingedSite.Modules.{u + 1, u, max (u + 1) r}
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor
        ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over U).O)
      (ComplexShape.up ℤ)]
  [CompactSpace X.obj] [QuasiSeparatedSpace X.obj] in
open Stacks.SheafOfModules.DerivedTensorProduct in
/-- **Tor amplitude, read at the fibre of a point.** Let `K` be an object of `D(X_étale, Λ)`
represented by a complex `C`, whose associated object of `D(𝒪)` has Tor amplitude in `[a, b]`
for a derived tensor product `T₀` on `𝒪`. Then at every point `Ψ` of the small étale site the
fibre of every cohomology sheaf of `C` outside `[a, b]` vanishes, and if `C` is a bounded above
complex with flat fibres at `Ψ`, the fibre at `Ψ` of the cokernel of the differential into
degree `a` is flat. -/
theorem fiber_of_hasTorAmplitude
    (T₀ : Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, max (u + 1) r, d}
      (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ))
    (K : DerivedCategory
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ)))
    (C : CochainComplex
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ)) ℤ)
    (eC : DerivedCategory.Q.obj C ≅ K)
    (Ψ : (SmallEtale.topology B X.obj X.property).Point.{max (u + 1) r}) (a b : ℤ)
    (hamp : HasTorAmplitude T₀
      ((moduleSheafOverConstantCoefficientsFunctor.{u, max (u + 1) r, r}
        B X Λ).mapDerivedCategory.obj K) a b) :
    (∀ i : ℤ, i ∉ Set.Icc a b →
        IsZero ((Ψ.sheafFiber (A := ModuleCat.{max (u + 1) r} Λ)).obj (C.homology i))) ∧
      (CochainComplex.minus _ C →
        (∀ n : ℤ, Module.Flat Λ ((Ψ.sheafFiber (A := ModuleCat.{max (u + 1) r} Λ)).obj (C.X n))) →
        Module.Flat Λ (cokernel ((Ψ.sheafFiber (A := ModuleCat.{max (u + 1) r} Λ)).map
          (C.d (a - 1) a)) : ModuleCat.{max (u + 1) r} Λ)) := by
  let hd : HasDerivedCategory.{d} (SheafOfModules.{max (u + 1) r}
      (Stacks.commRingSheafToRingSheaf.{u, u + 1, max (u + 1) r}
        (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).O)) :=
    inferInstanceAs (HasDerivedCategory.{d} (RingedSite.Modules.{u + 1, u, max (u + 1) r}
      (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ)))
  let Φ := moduleSheafOverConstantCoefficientsFunctor.{u, max (u + 1) r, r} B X Λ
  let G : SheafOfModules.{max (u + 1) r} (Stacks.commRingSheafToRingSheaf.{u, u + 1, max (u + 1) r}
        (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).O) ⥤
      ModuleCat.{max (u + 1) r} ((Ψ.presheafFiber (A := CommRingCat.{max (u + 1) r})).obj
        (constantCoefficientSheaf.{u, max (u + 1) r, r} B X Λ).obj) :=
    Stacks.sheafModuleFiberOfCommRing Ψ (constantCoefficientSheaf.{u, max (u + 1) r, r} B X Λ)
  have : (Φ ⋙ G).PreservesZeroMorphisms := ⟨fun _ _ => by
    change G.map (Φ.map 0) = 0
    rw [Φ.map_zero]
    exact G.map_zero _ _⟩
  refine fiber_of_hasTorAmplitudeCanonical B X Λ
    (constantCoefficientRingFiberEquiv.{u, max (u + 1) r, r} B X Λ Ψ) (Φ ⋙ G) Ψ
    ((upliftedEtaleFiberSheafFiberComplexIso B X Λ Ψ).symm ≪≫
      moduleSheafOverConstantCoefficientsFiberComplexIso.{u, max (u + 1) r, r} B X Λ Ψ) C a b ?_
  have h0 := hasTorAmplitudeCanonical_derivedModuleFiber
    (Y := constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ) T₀ _ a b hamp Ψ
  refine hasTorAmplitudeCanonical_of_iso ?_ a b h0
  exact (Functor.mapDerivedCategory.{d} G).mapIso
      (((Functor.mapDerivedCategoryFactors.{_, d} Φ).app C).symm ≪≫
        Φ.mapDerivedCategory.mapIso eC).symm ≪≫
    (Functor.mapDerivedCategoryFactors.{d, _} G).app _

omit hSliceDerived
  [∀ U : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C,
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) r, max (u + 1) r,
      max (u + 1) r}
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over U).O).Additive]
  [∀ (U : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) r, max (u + 1) r,
      max (u + 1) r}
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over U).O).obj M).Additive]
  [∀ (U : (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).C)
    (K L : CochainComplex (RingedSite.Modules.{u + 1, u, max (u + 1) r}
      ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor
        ((constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ).over U).O)
      (ComplexShape.up ℤ)] in
open Stacks.SheafOfModules.DerivedTensorProduct in
/-- Let `Λ` be a Noetherian ring and `X` a quasi-compact and
quasi-separated scheme. If `K ∈ D_ctf(X_étale, Λ)` has Tor amplitude in `[a, b]`, then `K` can be
represented by a complex `F^a → ⋯ → F^b` of constructible flat sheaves of `Λ`-modules.

Tor amplitude is that of the associated object of `D(𝒪)`, `𝒪` the constant coefficient ring
sheaf, against a derived tensor product `T₀` on `𝒪` (Stacks 08FZ (1)); the hypothesis `hK` is
the constructibility of the cohomology sheaves of `K`. -/
@[stacks 03TT "the last sentence: Tor amplitude in [a, b] gives a representative \
  F^a → ⋯ → F^b by constructible flat sheaves"]
public theorem exists_constructibleFlat_representative_of_hasTorAmplitude
    (T₀ : Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, max (u + 1) r, d}
      (constantCoefficientRingedSite.{u, max (u + 1) r, r} B X Λ))
    (K : DerivedCategory
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ)))
    (hK : IsConstructible B X Λ K) (a b : ℤ)
    (hamp : HasTorAmplitude T₀
      ((moduleSheafOverConstantCoefficientsFunctor.{u, max (u + 1) r, r}
        B X Λ).mapDerivedCategory.obj K) a b) :
    ∃ F : CochainComplex
        (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ)) ℤ,
      F.IsStrictlyGE a ∧ F.IsStrictlyLE b ∧
        (∀ i : ℤ, IsConstructibleFlatModuleSheaf B X Λ (F.X i)) ∧
        Nonempty (DerivedCategory.Q.obj F ≅ K) :=
  exists_constructibleFlat_representative_of_fiber B X Λ K hK a b
    (fun C eC _ => fiber_of_hasTorAmplitude B X Λ T₀ K C eC _ a b hamp)

end GlobalAmplitude

end Stacks.EtaleCohomology
