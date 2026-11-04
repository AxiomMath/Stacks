module

public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionUpperShriekDualizing
public import StacksFrontier.AlgebraicGeometry.Duality.ModelComparisonRightAdjoint
public import StacksFrontier.AlgebraicGeometry.Duality.NormalizedModelOnAffineLocalBase
public import StacksFrontier.AlgebraicGeometry.Duality.ProperDualityTransportAffineBase
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.CoherentCohomology
public import StacksFrontier.AlgebraicGeometry.Duality.SheafyTraceProperPseudoCoherent
public import StacksFrontier.AlgebraicGeometry.Duality.StandardModelGlobalSections
public import StacksFrontier.AlgebraicGeometry.Duality.SurfaceDualizingDegree.CoherentGlobalSections
public import StacksFrontier.AlgebraicGeometry.Duality.SurfaceDualizingDegree.NormalizedUpperShriek
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatDerivedSectionsPseudoCoherent
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.PseudoCoherentPushforwardLocallySmall
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.DualizingDivisor.DerivedSections
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.GrauertRiemenschneiderFinite
public import StacksFrontier.RingTheory.Dualizing.NormalizedResidueFieldShiftDual
public import StacksCore.Tactic.StacksAttribute

/-!
# The duality step of Grauert-Riemenschneider vanishing

In Situation [Stacks, Tag 0AX8] with `X` normal, let `ω_A^•` be a normalized dualizing complex
over `A` and let `ω_X` be a coherent module on `X` with `f^×(ω̃_A^•) ≅ ω_X[2]`. Then every
`A`-linear map `H¹(X, ω_X) → κ` is zero, and Grauert-Riemenschneider vanishing
`H¹(X, ω_X) = 0` ([Stacks, Tag 0AXD]) follows.

## Main results

* `Stacks.Duality.isBoundedAbove_of_isDualizingComplex`: a dualizing complex on a quasi-compact
  locally Noetherian scheme is cohomologically bounded above.
* `AlgebraicGeometry.isPseudoCoherent_derivedGlobalSectionsOver_of_isProper`: over a Noetherian
  affine base a proper morphism carries a pseudo-coherent object to one with pseudo-coherent
  derived global sections.
* `Stacks.Duality.nonempty_iso_dualizingDerivedHom_derivedGlobalSections_relativeDualizing`:
  `RHom_A(RΓ(X, ω_X^•), ω_A^•) ≅ RΓ(X, 𝒪_X)`.
* `AlgebraicGeometry.VanishingSituation.forall_linearMap_residueField_eq_zero`: every
  `A`-linear map `H¹(X, ω_X) → κ` is zero.
* `AlgebraicGeometry.VanishingSituation.isZero_firstCohomology_dualizingModule_of_isTildeDualizing`
  — `H¹(X, ω_X) = 0` for a dualizing module `ω_X` normalized with respect to `ω_A^•`.

## References

* [Stacks Project, Tag 0AXD](https://stacks.math.columbia.edu/tag/0AXD)
* [Stacks Project, Tag 0AX8](https://stacks.math.columbia.edu/tag/0AX8)
* [Stacks Project, Tag 0AXC](https://stacks.math.columbia.edu/tag/0AXC)
* [Stacks Project, Tag 0A7B](https://stacks.math.columbia.edu/tag/0A7B)
* [Stacks Project, Tag 0A7C](https://stacks.math.columbia.edu/tag/0A7C)
* [Stacks Project, Tag 0A7M](https://stacks.math.columbia.edu/tag/0A7M)
* [Stacks Project, Tag 0AA3](https://stacks.math.columbia.edu/tag/0AA3)
* [Stacks Project, Tag 0GEW](https://stacks.math.columbia.edu/tag/0GEW)
* [Stacks Project, Tag 08E8](https://stacks.math.columbia.edu/tag/08E8)
* [Stacks Project, Tag 06XS](https://stacks.math.columbia.edu/tag/06XS)
* [Stacks Project, Tag 0B4X](https://stacks.math.columbia.edu/tag/0B4X)
* [Stacks Project, Tag 0B4R](https://stacks.math.columbia.edu/tag/0B4R)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory Opposite TopologicalSpace
open Stacks.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

universe w u

namespace Stacks.Duality

/-! ### A faithful contravariant functor reflects the vanishing of a group of morphisms -/

/-- Let `F : Cᵒᵖ ⥤ C` and `ι : C ⥤ D` be faithful, let `K`, `L` be objects of `C`, and suppose
`ι(F(L)) ≅ P` and `ι(F(K)) ≅ Q` with at most one morphism `P ⟶ Q`. Then there is at most one
morphism `K ⟶ L`. -/
theorem subsingleton_hom_of_faithful_op {C D : Type*} [Category C] [Category D] (ι : C ⥤ D)
    [ι.Faithful] (F : Cᵒᵖ ⥤ C) [F.Faithful] {K L : C} {P Q : D}
    (e₁ : ι.obj (F.obj (op L)) ≅ P) (e₂ : ι.obj (F.obj (op K)) ≅ Q)
    (hPQ : Subsingleton (P ⟶ Q)) : Subsingleton (K ⟶ L) := by
  have := (Iso.homCongr e₁ e₂).subsingleton
  exact Function.Injective.subsingleton (f := fun α : K ⟶ L => ι.map (F.map α.op))
    fun _ _ h => Quiver.Hom.op_inj (F.map_injective (ι.map_injective h))

/-- A full functor carries a subsingleton group of morphisms to a subsingleton group of
morphisms. -/
theorem subsingleton_hom_map_of_subsingleton {C D : Type*} [Category C] [Category D] (ι : C ⥤ D)
    [ι.Full] {K L : C} (h : Subsingleton (K ⟶ L)) : Subsingleton (ι.obj K ⟶ ι.obj L) := by
  exact ι.map_surjective.subsingleton

/-! ### A dualizing complex on a quasi-compact scheme is bounded above -/

/-- On an affine open where `K` has a dualizing model, the cohomology sheaves of `K` vanish in
all sufficiently positive degrees after restriction to that open. -/
theorem exists_isZero_restrict_homology_above_of_hasDualizingModelOn {X : Scheme.{u}}
    [IsLocallyNoetherian X] [HasDerivedCategory.{w} X.Modules] {K : DerivedCategory X.Modules}
    {U : X.Opens} (hU : IsAffineOpen U) (h : HasDualizingModelOn K U hU) :
    ∃ b : ℤ, ∀ i, b < i → IsZero ((Scheme.Modules.restrictFunctor U.ι).obj
      ((DerivedCategory.homologyFunctor X.Modules i).obj K)) := by
  let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let := HasDerivedCategory.standard U.toScheme.Modules
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ(X, U))
  obtain ⟨ω, hω, ⟨e⟩⟩ := h
  obtain ⟨-, ⟨b, hb⟩⟩ := Dualizing.IsDualizingComplex.bounded.{u, u} hω
  refine ⟨b, fun i hi => ?_⟩
  have hz : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U)) i).obj ω) :=
    DerivedCategory.isZero_of_isLE ω b i hi
  exact IsZero.of_iso
    (((tilde.functor Γ(X, U) ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom).map_isZero hz))
    (((Dualizing.mapDerivedCategoryHomologyIso
      (Scheme.Modules.restrictFunctor U.ι) i).app K).symm ≪≫
    (DerivedCategory.homologyFunctor _ i).mapIso e ≪≫
    (Dualizing.mapDerivedCategoryHomologyIso
      (tilde.functor Γ(X, U) ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom) i).app ω)

/-- A dualizing complex on a quasi-compact locally Noetherian scheme is cohomologically bounded
above. -/
theorem isBoundedAbove_of_isDualizingComplex {X : Scheme.{u}} [IsLocallyNoetherian X]
    [CompactSpace X] [HasDerivedCategory.{w} X.Modules] (K : DerivedCategory X.Modules)
    (hK : IsDualizingComplex K) : DerivedCategoryB.IsBoundedAbove K := by
  have hloc : ∀ U : X.affineOpens, ∃ b : ℤ, ∀ i : ℤ, b < i →
      IsZero ((Scheme.Modules.restrictFunctor U.1.ι).obj
        ((DerivedCategory.homologyFunctor X.Modules i).obj K)) :=
    fun U => exists_isZero_restrict_homology_above_of_hasDualizingModelOn U.2 (hK U.1 U.2)
  choose N hN using hloc
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun U : X.affineOpens => (U.1 : Set X))
    (fun U => U.1.isOpen) (by
      intro x _
      have hx : x ∈ (⨆ U : X.affineOpens, (U : X.Opens)) := by
        rw [iSup_affineOpens_eq_top]; trivial
      obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      exact Set.mem_iUnion.mpr ⟨U, hU⟩)
  refine ⟨∑ U ∈ t, |N U|, fun n hn => ?_⟩
  refine Stacks.DerivedQCoh.isZero_schemeModules_of_cover _ (fun U : t => U.1.1) ?_
    (fun U => hN U.1 n ?_)
  · apply top_unique
    intro x _
    obtain ⟨U, hU, hxU⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨U, hU⟩, hxU⟩
  · have h := Finset.single_le_sum (f := fun U => |N U|) (fun U _ => abs_nonneg (N U)) U.2
    have := le_abs_self (N U.1)
    omega

end Stacks.Duality

/-! ### Pseudo-coherence of derived global sections over a Noetherian affine base -/

namespace AlgebraicGeometry

/-- Over a Noetherian affine base, a proper morphism carries a pseudo-coherent object to one with
pseudo-coherent derived global sections. -/
theorem isPseudoCoherent_derivedGlobalSectionsOver_of_isProper {A : Type u} [CommRing A]
    [IsNoetherianRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (F : DerivedCategory X.Modules)
    (hF : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) F) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent ((derivedGlobalSectionsOver f).obj F) :=
  have : IsNoetherian (Spec (CommRingCat.of A)) := isNoetherian_Spec.mpr ‹_›
  (isPseudoCoherent_derivedGlobalSectionsOver_id_of_isPseudoCoherent (CommRingCat.of A)
      ((derivedPushforwardModules f).obj F)
      (open Stacks.AlgebraicGeometry.ProperSupportCoherent in
        isPseudoCoherent_derivedPushforwardModules_of_isProper f F hF)).ofIso
    ((derivedGlobalSectionsOverPushforwardIso f).app F).symm

end AlgebraicGeometry

/-! ### The duality transport, with every hypothesis of its inputs discharged -/

namespace Stacks.Duality

/-- For a proper morphism `f : X ⟶ Spec A` with `A` Noetherian and a dualizing complex `ω_A^•`
over `A` whose derived sheafification `ω̃_A^•` is a dualizing complex on `Spec A`,
`RHom_A(RΓ(X, f^×(ω̃_A^•)), ω_A^•) ≅ RΓ(X, 𝒪_X)`. -/
theorem nonempty_iso_dualizingDerivedHom_derivedGlobalSections_relativeDualizing
    {A : Type u} [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (ωA : DerivedCategory (ModuleCat.{u} A)) (hωA : Dualizing.IsDualizingComplex ωA)
    (hK : IsDualizingComplex ((derivedTilde (CommRingCat.of A)).obj ωA).obj) :
    letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    letI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    letI : IsNoetherian X := ⟨⟩
    letI := derivedMonoidalStructure X.sheaf
    Nonempty ((Dualizing.dualizingDerivedHomFunctor.{u, u} A ωA).obj
        (op ((derivedGlobalSectionsOver f).obj
          ((properRightAdjoint f).obj ((derivedTilde (CommRingCat.of A)).obj ωA)).obj)) ≅
      (derivedGlobalSectionsOver f).obj
        (𝟙_ (DerivedCategory (StructureSheafModules X.sheaf)))) := by
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : IsNoetherian X := ⟨⟩
  let : IsNoetherian (Spec (CommRingCat.of A)) := isNoetherian_Spec.mpr ‹_›
  have hdual : IsDualizingComplex
      ((properRightAdjoint f).obj ((derivedTilde (CommRingCat.of A)).obj ωA)).obj :=
    isDualizingComplex_properRightAdjoint_obj f _ hK
  have hbm : DerivedCategoryB.derivedCategoryBMinus (fun N : X.Modules => N.IsCoherent)
      ((properRightAdjoint f).obj ((derivedTilde (CommRingCat.of A)).obj ωA)).obj :=
    ⟨isBoundedAbove_of_isDualizingComplex _ hdual,
      fun i => isCoherent_homology_of_isDualizingComplex hdual i⟩
  have hbb : DerivedCategoryB.IsBoundedBelow ((derivedTilde (CommRingCat.of A)).obj ωA).obj :=
    AlgebraicGeometry.isBoundedBelow_tilde_mapDerivedCategory_obj (CommRingCat.of A) ωA
      (Dualizing.isBoundedBelow_of_bounded.{u, u} ωA hωA.bounded)
  have hpc := AlgebraicGeometry.isPseudoCoherent_derivedGlobalSectionsOver_of_isProper f
    ((properRightAdjoint f).obj ((derivedTilde (CommRingCat.of A)).obj ωA)).obj
    (isPseudoCoherent_of_derivedCategoryBMinus_isCoherent _ hbm)
  exact nonempty_dualizingDerivedHomDerivedGlobalSectionsRelativeDualizing_iso f ωA
    hbm hbb hK hpc hωA.bounded.1

end Stacks.Duality

/-! ### Shifting an object of `D^b_{Coh}(A)` -/

namespace Dualizing

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- The shift `P[n]` of an object `P` of `D^b_{Coh}(A)`. -/
def boundedCoherentShiftBy (P : BoundedCoherentDerivedCategory.{u, u} A) (n : ℤ) :
    BoundedCoherentDerivedCategory.{u, u} A :=
  ⟨P.obj⟦n⟧, fun i => by
      have := P.property.1 (n + i)
      have e : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (n + i)).obj P.obj ≅
          (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj (P.obj⟦n⟧) :=
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).shiftIso n i (n + i)
          rfl).app P.obj).symm
      exact Module.Finite.equiv e.toLinearEquiv,
    by
      obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := P.property.2
      exact ⟨⟨a - n, DerivedCategory.TStructure.t.isGE_shift P.obj a n (a - n) (by omega)⟩,
        ⟨b - n, DerivedCategory.TStructure.t.isLE_shift P.obj b n (b - n) (by omega)⟩⟩⟩

/-- Let `ω` be a dualizing complex over `A`, let `K` and `L` be objects of `D^b_{Coh}(A)` and
suppose `RHom_A(L, ω) ≅ P` and `RHom_A(K, ω) ≅ Q` with at most one morphism `P ⟶ Q`. Then there is
at most one morphism `K ⟶ L`. -/
theorem subsingleton_hom_of_dualizingDerivedHom {A : Type u} [CommRing A] [IsNoetherianRing A]
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : IsDualizingComplex ω)
    (PK PL : BoundedCoherentDerivedCategory.{u, u} A)
    {P Q : DerivedCategory (ModuleCat.{u} A)}
    (eP : (dualizingDerivedHomFunctor.{u, u} A ω).obj (op PL.obj) ≅ P)
    (eQ : (dualizingDerivedHomFunctor.{u, u} A ω).obj (op PK.obj) ≅ Q)
    (hPQ : Subsingleton (P ⟶ Q)) : Subsingleton (PK.obj ⟶ PL.obj) := by
  have : (boundedCoherentDualizingDerivedHomFunctor.{u, u} A ω hω).IsEquivalence :=
    boundedCoherentDualizingDerivedHom_isEquivalence.{u, u} A ω hω
  exact Stacks.Duality.subsingleton_hom_map_of_subsingleton (ObjectProperty.ι _)
    (Stacks.Duality.subsingleton_hom_of_faithful_op (ObjectProperty.ι _)
      (boundedCoherentDualizingDerivedHomFunctor.{u, u} A ω hω) eP eQ hPQ)

/-- The isomorphism between `Dualizing.residueFieldSingle A`, which places `ULift κ` in degree
zero, and the residue field `κ` itself placed in degree zero. -/
def residueFieldSingleIso (A : Type u) [CommRing A] [IsLocalRing A] :
    residueFieldSingle.{u, u} A ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (IsLocalRing.ResidueField A)) :=
  (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).mapIso
    (ULift.moduleEquiv (R := A) (M := IsLocalRing.ResidueField A)).toModuleIso

end Dualizing

/-! ### The duality step -/

namespace AlgebraicGeometry.VanishingSituation

open Stacks.Duality

variable (V : VanishingSituation.{u})

/-- In Situation [Stacks, Tag 0AX8] with `X` normal, `RΓ(X, ℱ)` lies in `D^{≤ 1}(A)` for every
quasi-coherent `ℱ`, that is `Hⁿ(X, ℱ) = 0` for `n ≥ 2` ([Stacks, Tag 0B4X] (1)). -/
theorem isLE_one_derivedGlobalSections [IsNormal V.X] (ℱ : V.X.Modules) [ℱ.IsQuasicoherent] :
    ((derivedGlobalSectionsOver V.f).obj
      ((DerivedCategory.singleFunctor V.X.Modules 0).obj ℱ)).IsLE 1 := by
  rw [DerivedCategory.isLE_iff]
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = (m : ℤ) := ⟨n.toNat, by omega⟩
  exact (DualizingDivisor.isZero_rightDerived_globalSectionsOver_of_one_lt V.dimension_two V.f
      V.modification ℱ m (by omega)).of_iso
    ((Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived (globalSectionsOver V.f)
      (derivedGlobalSectionsOver V.f) (derivedGlobalSectionsOverUnit V.f)
      (Scheme.Modules.exists_quasiIso_isKInjective V.X) m).app ℱ)

/-- In Situation [Stacks, Tag 0AX8] with `X` normal, let `ω_A^•` be a normalized dualizing complex
over `A` whose derived sheafification is a dualizing complex on `Spec A`, and let `ω_X` be a
coherent module on `X` with `ω_X^• = f^×(ω̃_A^•) ≅ ω_X[2]`. Then every `A`-linear map
`H¹(X, ω_X) → κ` to the residue field is zero. -/
theorem forall_linearMap_residueField_eq_zero [IsNormal V.X] [CompactSpace V.X]
    [QuasiSeparatedSpace V.X] [IsLocallyNoetherian V.X] [AlgebraicGeometry.IsNoetherian V.X]
    (ωA : DerivedCategory (ModuleCat.{u} V.A))
    (hωA : Dualizing.IsNormalizedDualizingComplex.{u, u} ωA)
    (hK : IsDualizingComplex ((derivedTilde (CommRingCat.of V.A)).obj ωA).obj)
    (ωX : V.X.Modules) (hωX : ωX.IsCoherent)
    (hshift : Nonempty (((properRightAdjoint V.f).obj
        ((derivedTilde (CommRingCat.of V.A)).obj ωA)).obj ≅
      ((DerivedCategory.singleFunctor V.X.Modules 0).obj ωX)⟦(2 : ℤ)⟧)) :
    ∀ φ : firstCohomologySheafAsBaseModule V.X V.f ωX →ₗ[V.A]
      IsLocalRing.ResidueField V.A, φ = 0 := by
  have : ωX.IsCoherent := hωX
  have : ωX.IsQuasicoherent := isQuasicoherent_of_isCoherent ωX
  have : Module.Finite V.A V.residueFieldModule :=
    Module.Finite.of_surjective (Submodule.mkQ (IsLocalRing.maximalIdeal V.A))
      (Submodule.mkQ_surjective _)
  obtain ⟨eshift⟩ := hshift
  obtain ⟨etr⟩ := nonempty_iso_dualizingDerivedHom_derivedGlobalSections_relativeDualizing
    V.f ωA hωA.1 hK
  obtain ⟨eres⟩ :=
    Dualizing.nonempty_iso_dualizingDerivedHom_residueFieldSingleShiftOne.{u, u} ωA hωA
  have hYfin : ∀ i : ℤ, Module.Finite V.A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} V.A) i).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} V.A) 0).obj V.residueFieldModule)) := by
    intro i
    by_cases hi : i = 0
    · subst hi
      have e : (DerivedCategory.homologyFunctor (ModuleCat.{u} V.A) 0).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} V.A) 0).obj
              V.residueFieldModule) ≃ₗ[V.A] V.residueFieldModule :=
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} V.A) 0).app
          V.residueFieldModule).toLinearEquiv
      exact Module.Finite.equiv e.symm
    · have hz : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} V.A) i).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} V.A) 0).obj V.residueFieldModule)) := by
        rcases lt_or_gt_of_ne hi with hi | hi
        · exact DerivedCategory.isZero_of_isGE _ 0 i hi
        · exact DerivedCategory.isZero_of_isLE _ 0 i hi
      have := ModuleCat.isZero_iff_subsingleton.mp hz
      exact Module.Finite.of_finite
  have hYb : (DerivedCategory.TStructure.t).bounded
      ((DerivedCategory.singleFunctor (ModuleCat.{u} V.A) 0).obj V.residueFieldModule) :=
    ⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩
  have eN : (derivedGlobalSectionsOver V.f).obj
        ((properRightAdjoint V.f).obj ((derivedTilde (CommRingCat.of V.A)).obj ωA)).obj ≅
      ((derivedGlobalSectionsOver V.f).obj
        ((DerivedCategory.singleFunctor V.X.Modules 0).obj ωX))⟦(2 : ℤ)⟧ :=
    (derivedGlobalSectionsOver V.f).mapIso eshift ≪≫
      ((derivedGlobalSectionsOver V.f).commShiftIso (2 : ℤ)).app _
  have eP : (Dualizing.dualizingDerivedHomFunctor.{u, u} V.A ωA).obj
        (op (((DerivedCategory.singleFunctor (ModuleCat.{u} V.A) 0).obj
          V.residueFieldModule)⟦(1 : ℤ)⟧)) ≅ V.standardResidueFieldShift :=
    (Dualizing.dualizingDerivedHomFunctor.{u, u} V.A ωA).mapIso
        ((shiftFunctor (DerivedCategory (ModuleCat.{u} V.A)) (1 : ℤ)).mapIso
          (Dualizing.residueFieldSingleIso V.A)).op ≪≫
      eres ≪≫ (shiftFunctor (DerivedCategory (ModuleCat.{u} V.A)) (-1 : ℤ)).mapIso
        (Dualizing.residueFieldSingleIso V.A)
  have eQ : (Dualizing.dualizingDerivedHomFunctor.{u, u} V.A ωA).obj
        (op (((derivedGlobalSectionsOver V.f).obj
          ((DerivedCategory.singleFunctor V.X.Modules 0).obj ωX))⟦(2 : ℤ)⟧)) ≅
      standardDerivedGlobalSectionsStructureSheaf V.f :=
    (Dualizing.dualizingDerivedHomFunctor.{u, u} V.A ωA).mapIso eN.op ≪≫ etr
  have hPQ : Subsingleton (V.standardResidueFieldShift ⟶
      standardDerivedGlobalSectionsStructureSheaf V.f) :=
    ⟨fun a b => by
      rw [V.hom_standardResidueFieldShift_eq_zero a, V.hom_standardResidueFieldShift_eq_zero b]⟩
  have hsub := Dualizing.subsingleton_hom_of_dualizingDerivedHom ωA hωA.1
    (Dualizing.boundedCoherentShiftBy
      ⟨(derivedGlobalSectionsOver V.f).obj
        ((DerivedCategory.singleFunctor V.X.Modules 0).obj ωX),
        moduleFinite_homology_derivedGlobalSections V.f ωX,
        bounded_derivedGlobalSections V.f ωX⟩ 2)
    (Dualizing.boundedCoherentShiftBy
      ⟨(DerivedCategory.singleFunctor (ModuleCat.{u} V.A) 0).obj V.residueFieldModule,
        hYfin, hYb⟩ 1) eP eQ hPQ
  have : ((derivedGlobalSectionsOver V.f).obj
    ((DerivedCategory.singleFunctor V.X.Modules 0).obj ωX)).IsLE 1 :=
    V.isLE_one_derivedGlobalSections ωX
  have : (((derivedGlobalSectionsOver V.f).obj
      ((DerivedCategory.singleFunctor V.X.Modules 0).obj ωX))⟦(2 : ℤ)⟧).IsLE (-1) :=
    DerivedCategory.TStructure.t.isLE_shift _ 1 2 (-1) (by omega)
  have hbij := DerivedCategory.bijective_homologyFunctor_shiftMap_of_isLE_of_isGE
    (((derivedGlobalSectionsOver V.f).obj
      ((DerivedCategory.singleFunctor V.X.Modules 0).obj ωX))⟦(2 : ℤ)⟧)
    ((DerivedCategory.singleFunctor (ModuleCat.{u} V.A) 0).obj V.residueFieldModule)
    (-1) 0 1 0 (by omega) (le_refl 0)
  have hhom : Subsingleton
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} V.A) (-1)).obj
          (((derivedGlobalSectionsOver V.f).obj
            ((DerivedCategory.singleFunctor V.X.Modules 0).obj ωX))⟦(2 : ℤ)⟧) ⟶
        (DerivedCategory.homologyFunctor (ModuleCat.{u} V.A) 0).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} V.A) 0).obj V.residueFieldModule)) := by
    exact @Function.Surjective.subsingleton _ _ _ hsub hbij.2
  have e₀ : (DerivedCategory.homologyFunctor (ModuleCat.{u} V.A) (-1)).obj
        (((derivedGlobalSectionsOver V.f).obj
          ((DerivedCategory.singleFunctor V.X.Modules 0).obj ωX))⟦(2 : ℤ)⟧) ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{u} V.A) 1).obj
        ((derivedGlobalSectionsOver V.f).obj
          ((DerivedCategory.singleFunctor V.X.Modules 0).obj ωX)) := by
    exact ((DerivedCategory.homologyFunctor (ModuleCat.{u} V.A) 0).shiftIso 2 (-1) 1
      (by omega)).app ((derivedGlobalSectionsOver V.f).obj
        ((DerivedCategory.singleFunctor V.X.Modules 0).obj ωX))
  have e₁ : (DerivedCategory.homologyFunctor (ModuleCat.{u} V.A) (-1)).obj
        (((derivedGlobalSectionsOver V.f).obj
          ((DerivedCategory.singleFunctor V.X.Modules 0).obj ωX))⟦(2 : ℤ)⟧) ≅
      firstCohomologySheafAsBaseModule V.X V.f ωX :=
    e₀ ≪≫ (firstCohomologySheafAsBaseModuleIsoDerivedCohomology V.f ωX).symm
  have e₂ : (DerivedCategory.homologyFunctor (ModuleCat.{u} V.A) 0).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} V.A) 0).obj V.residueFieldModule) ≅
      V.residueFieldModule :=
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} V.A) 0).app _
  have hsub2 : Subsingleton (firstCohomologySheafAsBaseModule V.X V.f ωX ⟶
      V.residueFieldModule) := by
    have := hhom
    exact (Iso.homCongr e₁ e₂).symm.subsingleton
  intro φ
  obtain ⟨g, hg⟩ := ModuleCat.hom_surjective
    (M := firstCohomologySheafAsBaseModule V.X V.f ωX) (N := V.residueFieldModule) φ
  rw [← hg, hsub2.allEq g 0]
  simp

/-- Grauert-Riemenschneider vanishing ([Stacks, Tag 0AXD]). In Situation [Stacks, Tag 0AX8] with
`X` normal and `A` Nagata, let `ω_A^•` be a normalized dualizing complex over `A` whose derived
sheafification is a dualizing complex on `Spec A`, and let `ω_X` be a dualizing module of `X`
normalized with respect to `ω_A^•`, in the sense that `f^×(ω̃_A^•) ≅ ω_X[2]`. Then
`H¹(X, ω_X) = 0`. -/
theorem isZero_firstCohomology_dualizingModule_of_isTildeDualizing [IsNormal V.X]
    [IsLocallyNoetherian V.X] [CompactSpace V.X] [QuasiSeparatedSpace V.X]
    [AlgebraicGeometry.IsNoetherian V.X]
    (hnag : IsNagataRing V.A)
    (ωA : DerivedCategory (ModuleCat.{u} V.A))
    (hωA : Dualizing.IsNormalizedDualizingComplex.{u, u} ωA)
    (hK : IsDualizingComplex ((derivedTilde (CommRingCat.of V.A)).obj ωA).obj)
    (ωX : V.X.Modules) (hωX : IsDualizingModule ωX)
    (hshift : Nonempty (((properRightAdjoint V.f).obj
        ((derivedTilde (CommRingCat.of V.A)).obj ωA)).obj ≅
      ((DerivedCategory.singleFunctor V.X.Modules 0).obj ωX)⟦(2 : ℤ)⟧)) :
    IsZero (firstCohomologySheafAsBaseModule V.X V.f ωX) :=
  V.isZero_firstCohomology_dualizingModule_of_forall_linearMap_eq_zero hnag ωA hωA.1 ωX hωX
    (V.forall_linearMap_residueField_eq_zero ωA hωA hK ωX hωX.1 hshift)

end AlgebraicGeometry.VanishingSituation

end
