module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.Boundedness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ExtensionByZeroTorsion
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowComparisonDevissage

/-!
# Boundedness of `Rf_!` on `D⁺_tors` for an arbitrary coefficient ring

Let `f : X ⟶ Y` be a morphism of schemes with `Y` quasi-compact, `j : X ⟶ X̄` a compactification
of `X` over `Y`, and `Λ` an arbitrary ring. On the objects of `D⁺(X_étale, Λ)` whose cohomology
sheaves are torsion (`Stacks.EtaleCohomology.isTorsionPlus`), the functor
`Rf_! = Rf̄_* ∘ Rj_!` has bounded cohomological amplitude: parts (2) and (3) of
[Stacks, Tag 0G2A] for `D⁺_tors`. Part (1) holds on all of `D⁺`
(`Stacks.EtaleCohomology.isIso_homology_derivedLowerShriek_map_truncLEι`).

## Main results

* `Stacks.EtaleCohomology.exists_isLE_derivedLowerShriek_of_isTorsionPlus`: part (3), upper
  bound, on `D⁺_tors`.
* `Stacks.EtaleCohomology.exists_isIso_homology_derivedLowerShriek_map_truncGEπ_of_isTorsionPlus`:
  part (2) on `D⁺_tors`.

## Implementation notes

The proof follows [Stacks, Tag 0G2A], by induction on `b - a` along the truncation triangles and
Stacks 095U: by Stacks 0A3V the fibres of the proper `f̄` have dimension at most
some `d`; extension by zero carries torsion sheaves to torsion sheaves
(`Stacks.EtaleCohomology.isTorsionEtaleModule_etaleModuleExtensionByZero_obj`); so by Stacks 095U
`R^q f̄_*(j_! M) = 0` for `q > 2d` and every torsion `M`; the Postnikov induction
`Stacks.BoundedCohomologicalDimension.isLE_map_obj_of_cohomology_mem` with the class of torsion
sheaves gives the bound for bounded complexes with torsion cohomology.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

-- instances of `Stacks.Models.RegularModelSituation` whose conclusions (`QuasiCompact ?f`, ...)
-- match every goal and send instance search into a loop; they are irrelevant here
attribute [-instance] Stacks.Models.RegularModelSituation.commRingR
  Stacks.Models.RegularModelSituation.isDomainR
  Stacks.Models.RegularModelSituation.isDiscreteValuationRingR
  Stacks.Models.RegularModelSituation.fieldK Stacks.Models.RegularModelSituation.algebraRK
  Stacks.Models.RegularModelSituation.isFractionRingRK Stacks.Models.RegularModelSituation.fieldk
  Stacks.Models.RegularModelSituation.algebraRk Stacks.Models.RegularModelSituation.isCurve
  Stacks.Models.RegularModelSituation.smooth Stacks.Models.RegularModelSituation.flat
  Stacks.Models.RegularModelSituation.locallyOfFiniteType
  Stacks.Models.RegularModelSituation.quasiCompact

universe u

namespace Stacks.EtaleCohomology

section Torsion

variable (Λ : Type) [Ring Λ] (X : Scheme.{u})

/-- Torsion sheaves of modules are closed under isomorphism. -/
theorem IsTorsionEtaleModule.of_iso {F G : EtaleModules.{u, 0} Λ X} (e : F ≅ G)
    (hF : IsTorsionEtaleModule.{u, 0} Λ X F) : IsTorsionEtaleModule.{u, 0} Λ X G :=
  IsLocallyTorsionModulePresheaf.of_isLocallySurjective
    ((sheafToPresheaf X.smallEtaleTopology _).map e.hom) inferInstance hF

/-- The torsion sheaves of modules are closed under isomorphisms. -/
instance isClosedUnderIsomorphisms_isTorsionEtaleModule :
    ObjectProperty.IsClosedUnderIsomorphisms
      (IsTorsionEtaleModule.{u, 0} Λ X : ObjectProperty (EtaleModules.{u, 0} Λ X)) :=
  ⟨fun e hF => IsTorsionEtaleModule.of_iso Λ X e hF⟩

/-- A zero sheaf of modules is torsion: its sections vanish. -/
theorem isTorsionEtaleModule_of_isZero {F : EtaleModules.{u, 0} Λ X} (hF : IsZero F) :
    IsTorsionEtaleModule.{u, 0} Λ X F := by
  intro V x
  refine ⟨⊤, X.smallEtaleTopology.top_mem V, fun W g _ => ⟨1, one_pos, ?_⟩⟩
  have hz : IsZero (F.obj.obj (Opposite.op W)) :=
    (sheafToPresheaf X.smallEtaleTopology _ ⋙
      (evaluation _ _).obj (Opposite.op W)).map_isZero hF
  have : Subsingleton (F.obj.obj (Opposite.op W)) := ModuleCat.subsingleton_of_isZero hz
  exact Subsingleton.elim _ _

open ZeroObject in
/-- The torsion sheaves of modules contain a zero object. -/
instance containsZero_isTorsionEtaleModule :
    ObjectProperty.ContainsZero
      (IsTorsionEtaleModule.{u, 0} Λ X : ObjectProperty (EtaleModules.{u, 0} Λ X)) :=
  ⟨(0 : EtaleModules.{u, 0} Λ X), isZero_zero _, isTorsionEtaleModule_of_isZero Λ X (isZero_zero _)⟩

/-- The underlying abelian sheaf of a torsion sheaf of modules is a torsion abelian sheaf: the
two conditions are the same condition on the same sections. -/
theorem torsionSheafProperty_etaleModuleForget_obj_of_isTorsionEtaleModule
    {G : EtaleModules.{u, 0} Λ X} (hG : IsTorsionEtaleModule.{u, 0} Λ X G) :
    Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology
      ((etaleModuleForgetAb.{u, 0} Λ X).obj G) :=
  hG

end Torsion

variable (Λ : Type) [Ring Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
  (j : CompactificationOf (Over.mk f))

/-- **Part (3) of Stacks 0G2A on `D⁺_tors`, upper bound.** If `Y` is quasi-compact there is `N`
such that `Rf_!` carries every object of `D⁺(X_étale, Λ)` with torsion cohomology sheaves vanishing
above degree `b` to an object vanishing above degree `b + N`. The lower bound is
`Stacks.EtaleCohomology.isGE_derivedLowerShriek_obj`, on all of `D⁺`. -/
theorem isLE_derivedLowerShriek_of_isTorsionPlus (d : ℕ)
    (hd : ∀ y : Y, topologicalKrullDim (j.toBase.fiber y) ≤ d)
    (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X)) (hK : isTorsionPlus.{u, 0} Λ X K)
    (b : ℤ) (hLE : K.IsLE b) :
    (DerivedCategory.Plus.ι.obj ((derivedLowerShriek.{u, 0} f j Λ).obj K)).IsLE
      (b + (2 * d : ℕ)) := by
  obtain ⟨a₀, ha₀⟩ := K.property
  let a := min a₀ b
  have hGE : K.IsGE a := by
    have : (DerivedCategory.Plus.ι.obj K).IsGE a₀ := ha₀
    exact (DerivedCategory.Plus.isGE_ι_obj_iff K a).1
      (DerivedCategory.TStructure.t.isGE_of_ge _ a a₀ (min_le_left _ _))
  have hLE' : K.IsLE (a + ((b - a).toNat : ℕ)) := by
    rw [Int.toNat_of_nonneg (by omega)]; simpa using hLE
  have := Stacks.BoundedCohomologicalDimension.isLE_map_obj_of_cohomology_mem
    (derivedLowerShriek.{u, 0} f j Λ ⋙ DerivedCategory.Plus.ι) (IsTorsionEtaleModule.{u, 0} Λ X)
    inferInstance (2 * d : ℕ) (fun q M hM => ?_) a (b - a).toNat K hGE hLE' (fun q _ _ => hK q)
  · rw [Int.toNat_of_nonneg (by omega)] at this
    simpa using this
  · let e : (DerivedCategory.Plus.singleFunctor _ q).obj
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj M) ≅
        (etaleModuleDerivedExtensionByZero.{u, 0} Λ j.immersion).obj
          ((DerivedCategory.Plus.singleFunctor _ q).obj M) :=
      (Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
        (etaleModuleExtensionByZero.{u, 0} Λ j.immersion) q).app M
    have h := Stacks.BoundedCohomologicalDimension.isLE_rightDerivedFunctorPlus_single
      (etaleModuleDirectImage.{u, 0} Λ j.toBase)
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj M) (2 * d : ℕ) q
      (fun p hp => isZero_rightDerived_etaleModuleDirectImage_of_isProper Λ j.toBase d hd _
        (torsionSheafProperty_etaleModuleForget_obj_of_isTorsionEtaleModule Λ _
          (isTorsionEtaleModule_etaleModuleExtensionByZero_obj Λ j.immersion M hM)) p
        (by exact_mod_cast hp))
    have : DerivedCategory.TStructure.t.IsLE (DerivedCategory.Plus.ι.obj
        ((etaleModuleDerivedDirectImage.{u, 0} Λ j.toBase).obj
          ((DerivedCategory.Plus.singleFunctor _ q).obj
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj M)))) (q + (2 * d : ℕ)) := h
    exact DerivedCategory.TStructure.t.isLE_of_iso
      (DerivedCategory.Plus.ι.mapIso
        ((etaleModuleDerivedDirectImage.{u, 0} Λ j.toBase).mapIso e)) _

/-- **Part (3) of Stacks 0G2A on `D⁺_tors`, upper bound**, with the bound `N` existential. -/
theorem exists_isLE_derivedLowerShriek_of_isTorsionPlus [CompactSpace Y] :
    ∃ N : ℕ, ∀ (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X)),
      isTorsionPlus.{u, 0} Λ X K → ∀ b : ℤ, K.IsLE b →
        (DerivedCategory.Plus.ι.obj ((derivedLowerShriek.{u, 0} f j Λ).obj K)).IsLE (b + N) := by
  have hP : IsProper j.toBase := j.property.2
  obtain ⟨d, hd⟩ := @AlgebraicGeometry.exists_topologicalKrullDim_fiber_le _ _ j.toBase
    hP.toLocallyOfFiniteType
    (@AlgebraicGeometry.instQuasiCompactOfUniversallyClosed _ _ _ hP.toUniversallyClosed) ‹_›
  exact ⟨2 * d, isLE_derivedLowerShriek_of_isTorsionPlus Λ f j d hd⟩

/-- **Part (2) of Stacks 0G2A on `D⁺_tors`.** If `Y` is quasi-compact there is `N` such that for
every `E` in `D⁺(X_étale, Λ)` with torsion cohomology sheaves and `i ≥ b`, the map
`Hⁱ(Rf_! E) ⟶ Hⁱ(Rf_!(τ_{≥ b - N} E))` is an isomorphism: the first vertex `Rf_!(τ_{≤ b-N-1} E)`
of the image of the truncation triangle has torsion cohomology in degrees `≤ b - N - 1`, so lives
in degrees `≤ b - 1` by part (3). -/
theorem isIso_homology_derivedLowerShriek_map_truncGEπ_of_isTorsionPlus (d : ℕ)
    (hd : ∀ y : Y, topologicalKrullDim (j.toBase.fiber y) ≤ d)
    (E : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X)) (hE : isTorsionPlus.{u, 0} Λ X E)
    (b i : ℤ) (hbi : b ≤ i) :
    IsIso ((DerivedCategory.Plus.homologyFunctor _ i).map ((derivedLowerShriek.{u, 0} f j Λ).map
      ((DerivedCategory.Plus.TStructure.t.truncGEπ (b - (2 * d : ℕ))).app E))) := by
  let N : ℕ := 2 * d
  have hN := isLE_derivedLowerShriek_of_isTorsionPlus Λ f j d hd
  let t := DerivedCategory.Plus.TStructure.t (C := EtaleModules.{u, 0} Λ X)
  let T := (t.triangleLEGE (b - N - 1) (b - N) (by omega)).obj E
  have hT := t.triangleLEGE_distinguished (b - N - 1) (b - N) (by omega) E
  let L := (t.truncLE (b - N - 1)).obj E
  have hL : isTorsionPlus.{u, 0} Λ X L := fun q =>
    DerivedCategory.Plus.prop_homology_truncLE_obj (IsTorsionEtaleModule.{u, 0} Λ X) E
      (b - N - 1) (fun i _ => hE i) q
  have hLLE : L.IsLE (b - N - 1) := t.isLE_truncLE_obj E _ _ le_rfl
  have hLE := hN L hL (b - N - 1) hLLE
  let R := derivedLowerShriek.{u, 0} f j Λ ⋙ DerivedCategory.Plus.ι
  have hLE' : (R.mapTriangle.obj T).obj₁.IsLE (b - 1) := by
    show (DerivedCategory.Plus.ι.obj ((derivedLowerShriek.{u, 0} f j Λ).obj L)).IsLE (b - 1)
    rwa [show b - 1 = b - N - 1 + N by omega]
  exact DerivedCategory.isIso_homologyMap_mor₂_of_isLE₁ (R.mapTriangle.obj T)
    (R.map_distinguished T hT) i (b - 1) hLE' (by omega)

/-- **Part (2) of Stacks 0G2A on `D⁺_tors`**, with the bound `N` existential. -/
theorem exists_isIso_homology_derivedLowerShriek_map_truncGEπ_of_isTorsionPlus [CompactSpace Y] :
    ∃ N : ℕ, ∀ (E : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X)), isTorsionPlus.{u, 0} Λ X E →
      ∀ (b i : ℤ), b ≤ i →
      IsIso ((DerivedCategory.Plus.homologyFunctor _ i).map ((derivedLowerShriek.{u, 0} f j Λ).map
        ((DerivedCategory.Plus.TStructure.t.truncGEπ (b - N)).app E))) := by
  have hP : IsProper j.toBase := j.property.2
  obtain ⟨d, hd⟩ := @AlgebraicGeometry.exists_topologicalKrullDim_fiber_le _ _ j.toBase
    hP.toLocallyOfFiniteType
    (@AlgebraicGeometry.instQuasiCompactOfUniversallyClosed _ _ _ hP.toUniversallyClosed) ‹_›
  exact ⟨2 * d, isIso_homology_derivedLowerShriek_map_truncGEπ_of_isTorsionPlus Λ f j d hd⟩

end Stacks.EtaleCohomology

end
