module

public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedGlobalSectionsAtModel
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DetectingBoundedBelow
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffinePerfectSectionsLocalModels
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSetBaseChangeMateIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.InterfaceUnitNaturality
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposFlatModule

/-!
# Detecting boundedness below with a perfect generator on an algebraic space

Let `X` be a quasi-compact and quasi-separated algebraic space, `G` a perfect object of `D(𝒪_X)`
generating `D_QCoh(𝒪_X)` and `E` an object of `D_QCoh(𝒪_X)`. Then `E` is bounded below if and
only if `Hom(G[-i], E) = 0` for `i ≪ 0`, if and only if `Ext^i(G, E) = 0` for `i ≪ 0`, if and only
if `RHom_X(G, E)` is bounded below, if and only if `H^i(X, G^∨ ⊗^L E) = 0` for `i ≪ 0`, if and only
if `RΓ(X, G^∨ ⊗^L E)` is bounded below, if and only if these hold for every perfect `P` in place of
`G` together with the vanishing of `H^i(X, P ⊗^L E)` for `i ≪ 0` (Stacks 0GFI).

## Main results

* `AlgebraicGeometry.Space.subsingleton_hom_shift_iff_isZero_homology_tensorDual`:
  `Ext^i(P, E) = H^i(X, P^∨ ⊗^L E)` for perfect `P`, as a vanishing statement.
* `AlgebraicGeometry.Space.tfae_isGE_of_isPerfect_generator`: **Stacks 0GFI**.

## Implementation notes

`Ext^i_X(G, E)` is `Hom_{D(𝒪_X)}(G, E[i])`. `RΓ(X, -)` and `RHom_X(G, -) = RΓ(X, R𝓗om(G, -))`
are read in `D(Γ(X, 𝒪_X))`; their membership in `D⁺(ℤ)` is the vanishing of their cohomology in
all sufficiently negative degrees, which does not depend on the ring of scalars. Generation of
`D_QCoh(𝒪_X)` by `G` is the condition that an object of `D_QCoh(𝒪_X)` receiving only zero morphisms
from the shifts of `G` is zero.

## References

* [Stacks Project, Tag 0GFI](https://stacks.math.columbia.edu/tag/0GFI)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
attribute [local instance] ModuleCat.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Pretriangulated

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 20000] ModuleCat.hasDerivedCategory

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **`Ext^i(P, E) = H^i(X, P^∨ ⊗^L E)` for a perfect `P`, as a vanishing statement.** -/
theorem subsingleton_hom_shift_iff_isZero_homology_tensorDual (X : AlgebraicSpaces B S hS)
    (P : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hP : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect P)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (i : ℤ) :
    Subsingleton (P ⟶ E⟦i⟧) ↔
      IsZero ((DerivedCategory.homologyFunctor
        (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS X.1 X.2)) i).obj
          ((derivedModuleGlobalSectionsSmallEtaleAtModel B S hS X.1 X.2).obj
            (((smallEtaleDerivedTensor B S hS X).obj
              (smallEtaleDerivedDual B S hS X P)).obj E))) := by
  refine Iff.trans ?_ (isZero_homology_derivedModuleGlobalSectionsSmallEtale_iff X _ i).symm
  let φ := (shiftFunctor (DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) i).mapIso
    (smallEtaleDerivedSheafHomIsoTensorDual B S hS X P E hP)
  refine ((homUnitShiftSmallEtaleDerivedSheafHomEquiv X P E i).subsingleton_congr.symm.trans
    (Iso.homCongr (Iso.refl _) φ).subsingleton_congr).trans ?_
  exact subsingleton_iff_forall_eq _

/-- A complex is bounded below exactly when its cohomology vanishes in all sufficiently negative
degrees. -/
theorem exists_isGE_iff_exists_isZero_homology {R : Type (u + 1)} [Ring R]
    (K : DerivedCategory (ModuleCat.{u + 1} R)) :
    (∃ a : ℤ, K.IsGE a) ↔
      ∃ N : ℤ, ∀ i : ℤ, i ≤ N → IsZero ((DerivedCategory.homologyFunctor _ i).obj K) := by
  simp_rw [DerivedCategory.isGE_iff]
  exact ⟨fun ⟨a, ha⟩ => ⟨a - 1, fun i hi => ha i (by omega)⟩,
    fun ⟨N, hN⟩ => ⟨N + 1, fun i hi => hN i (by omega)⟩⟩

/-- `H^i(RHom_X(P, E)) = 0` exactly when `Ext^i(P, E) = 0` (Stacks 0B6E). -/
theorem isZero_homology_globalDerivedHom_iff (X : AlgebraicSpaces B S hS)
    (P E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (i : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((derivedModuleGlobalSectionsSmallEtaleAtModel B S hS X.1 X.2).obj
        (((smallEtaleDerivedSheafHom B S hS X).obj (op P)).obj E))) ↔
      Subsingleton (P ⟶ E⟦i⟧) := by
  refine (isZero_homology_derivedModuleGlobalSectionsSmallEtale_iff X _ i).trans ?_
  refine Iff.trans ?_ (homUnitShiftSmallEtaleDerivedSheafHomEquiv X P E i).subsingleton_congr
  exact (subsingleton_iff_forall_eq _).symm

/-- `RHom_X(P, E)` is bounded below exactly when `Ext^i(P, E) = 0` for `i ≪ 0`. -/
theorem exists_isGE_globalDerivedHom_iff (X : AlgebraicSpaces B S hS)
    (P E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) :
    (∃ a : ℤ, ((derivedModuleGlobalSectionsSmallEtaleAtModel B S hS X.1 X.2).obj
        (((smallEtaleDerivedSheafHom B S hS X).obj (op P)).obj E)).IsGE a) ↔
      ∃ N : ℤ, ∀ i : ℤ, i ≤ N → Subsingleton (P ⟶ E⟦i⟧) := by
  rw [exists_isGE_iff_exists_isZero_homology]
  exact exists_congr fun _ => forall₂_congr fun i _ => isZero_homology_globalDerivedHom_iff X P E i

/-- **`RΓ(X, -)` is left t-exact**: if `M ∈ D^{≥ a}` then `H^i(X, M) = 0` for `i < a`. -/
theorem isZero_homology_derivedModuleGlobalSectionsSmallEtale_of_isGE (X : AlgebraicSpaces B S hS)
    (M : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (a : ℤ) (hM : M.IsGE a) (i : ℤ)
    (hi : i < a) :
    IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS X.1 X.2)) i).obj
        ((derivedModuleGlobalSectionsSmallEtaleAtModel B S hS X.1 X.2).obj M)) := by
  refine (isZero_homology_derivedModuleGlobalSectionsSmallEtale_iff X M i).2 fun g => ?_
  exact DerivedCategory.TStructure.t.zero_of_isLE_of_isGE g 0 (a - i) (by omega) inferInstance
    (DerivedCategory.TStructure.t.isGE_shift M a i (a - i) (by omega))

/-- **Stacks 0GFI.** Let `X` be a quasi-compact and quasi-separated algebraic space, `G` a perfect
object of `D(𝒪_X)` which generates `D_QCoh(𝒪_X)`, and `E` an object of `D_QCoh(𝒪_X)`. The
following are equivalent:
1. `E ∈ D⁺_QCoh(𝒪_X)`;
2. `Hom(G[-i], E) = 0` for `i ≪ 0`;
3. `Ext^i_X(G, E) = 0` for `i ≪ 0`;
4. `RHom_X(G, E)` is bounded below;
5. `H^i(X, G^∨ ⊗^L E) = 0` for `i ≪ 0`;
6. `RΓ(X, G^∨ ⊗^L E)` is bounded below;
7. for every perfect `P`: (2), (3), (4) hold with `P` in place of `G`, `H^i(X, P ⊗^L E) = 0` for
   `i ≪ 0`, and `RΓ(X, P ⊗^L E)` is bounded below. -/
@[stacks 0GFI]
theorem tfae_isGE_of_isPerfect_generator (X : AlgebraicSpaces B S hS)
    (hqc : IsQuasiCompactSpace B S hS X.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1)
    (G : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hG : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect G)
    (hgen : ∀ E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2,
      (∀ n : ℤ, Subsingleton (G⟦n⟧ ⟶ E.obj)) → IsZero E.obj)
    (E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) :
    List.TFAE [
      ∃ a : ℤ, E.obj.IsGE a,
      ∃ N : ℤ, ∀ i : ℤ, i ≤ N → Subsingleton (G⟦-i⟧ ⟶ E.obj),
      ∃ N : ℤ, ∀ i : ℤ, i ≤ N → Subsingleton (G ⟶ E.obj⟦i⟧),
      ∃ a : ℤ, ((derivedModuleGlobalSectionsSmallEtaleAtModel B S hS X.1 X.2).obj
        (((smallEtaleDerivedSheafHom B S hS X).obj (op G)).obj E.obj)).IsGE a,
      ∃ N : ℤ, ∀ i : ℤ, i ≤ N → IsZero ((DerivedCategory.homologyFunctor
        (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS X.1 X.2)) i).obj
          ((derivedModuleGlobalSectionsSmallEtaleAtModel B S hS X.1 X.2).obj
            (((smallEtaleDerivedTensor B S hS X).obj
              (smallEtaleDerivedDual B S hS X G)).obj E.obj))),
      ∃ a : ℤ, ((derivedModuleGlobalSectionsSmallEtaleAtModel B S hS X.1 X.2).obj
          (((smallEtaleDerivedTensor B S hS X).obj
            (smallEtaleDerivedDual B S hS X G)).obj E.obj)).IsGE a,
      ∀ P : DerivedCategory (Modules.{u, u} B S hS X.1 X.2),
        (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect P →
          (∃ N : ℤ, ∀ i : ℤ, i ≤ N → Subsingleton (P⟦-i⟧ ⟶ E.obj)) ∧
          (∃ N : ℤ, ∀ i : ℤ, i ≤ N → Subsingleton (P ⟶ E.obj⟦i⟧)) ∧
          (∃ a : ℤ, ((derivedModuleGlobalSectionsSmallEtaleAtModel B S hS X.1 X.2).obj
            (((smallEtaleDerivedSheafHom B S hS X).obj (op P)).obj E.obj)).IsGE a) ∧
          (∃ N : ℤ, ∀ i : ℤ, i ≤ N → IsZero ((DerivedCategory.homologyFunctor
            (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS X.1 X.2)) i).obj
              ((derivedModuleGlobalSectionsSmallEtaleAtModel B S hS X.1 X.2).obj
                (((smallEtaleDerivedTensor B S hS X).obj P).obj E.obj)))) ∧
          (∃ a : ℤ, ((derivedModuleGlobalSectionsSmallEtaleAtModel B S hS X.1 X.2).obj
              (((smallEtaleDerivedTensor B S hS X).obj P).obj E.obj)).IsGE a)] := by
  have h23 : ∀ P : DerivedCategory (Modules.{u, u} B S hS X.1 X.2),
      (∃ N : ℤ, ∀ i : ℤ, i ≤ N → Subsingleton (P⟦-i⟧ ⟶ E.obj)) ↔
        ∃ N : ℤ, ∀ i : ℤ, i ≤ N → Subsingleton (P ⟶ E.obj⟦i⟧) := fun P =>
    exists_congr fun _ => forall₂_congr fun i _ => subsingleton_hom_shift_neg_iff P E.obj i
  tfae_have 1 → 7 := by
    rintro ⟨a, ha⟩ P hP
    obtain ⟨b, hb⟩ := exists_isLE_of_isPerfect hqc P hP
    have h2 : ∃ N : ℤ, ∀ i : ℤ, i ≤ N → Subsingleton (P⟦-i⟧ ⟶ E.obj) :=
      ⟨a - b - 1, fun i hi => ⟨fun f g => by
        have hb' : (P⟦-i⟧).IsLE (b + i) :=
          DerivedCategory.TStructure.t.isLE_shift P b (-i) (b + i) (by omega)
        rw [DerivedCategory.TStructure.t.zero_of_isLE_of_isGE f (b + i) a (by omega) hb' ha,
          DerivedCategory.TStructure.t.zero_of_isLE_of_isGE g (b + i) a (by omega) hb' ha]⟩⟩
    obtain ⟨c, hc⟩ := exists_isGE_smallEtaleDerivedTensor_of_isPerfect hqc P hP
    have h5 : ∃ N : ℤ, ∀ i : ℤ, i ≤ N → IsZero ((DerivedCategory.homologyFunctor
        (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS X.1 X.2)) i).obj
          ((derivedModuleGlobalSectionsSmallEtaleAtModel B S hS X.1 X.2).obj
            (((smallEtaleDerivedTensor B S hS X).obj P).obj E.obj))) :=
      ⟨a + c - 1, fun i hi => isZero_homology_derivedModuleGlobalSectionsSmallEtale_of_isGE X _
        (a + c) (hc E.obj a ha) i (by omega)⟩
    exact ⟨h2, (h23 P).1 h2, (exists_isGE_globalDerivedHom_iff X P E.obj).2 ((h23 P).1 h2), h5,
      (exists_isGE_iff_exists_isZero_homology _).2 h5⟩
  tfae_have 7 → 2 := fun h => (h G hG).1
  tfae_have 2 → 1 := by
    rintro ⟨N, hN⟩
    obtain ⟨hGc, hGg⟩ :=
      isCompactObject_and_isWeakTriangulatedGenerator_of_isPerfect X hqc hqs G hG hgen
    exact exists_isGE_of_lowHomVanishingOnCompact X hqc hqs E
      (lowHomVanishingOnCompact_of_generator _ hGc hGg E.obj ⟨N, hN⟩)
  tfae_have 2 ↔ 3 := h23 G
  tfae_have 3 ↔ 4 := (exists_isGE_globalDerivedHom_iff X G E.obj).symm
  tfae_have 3 ↔ 5 := exists_congr fun _ => forall₂_congr fun i _ =>
    subsingleton_hom_shift_iff_isZero_homology_tensorDual X G hG E.obj i
  tfae_have 5 ↔ 6 := (exists_isGE_iff_exists_isZero_homology _).symm
  tfae_finish

end AlgebraicGeometry.Space

end
