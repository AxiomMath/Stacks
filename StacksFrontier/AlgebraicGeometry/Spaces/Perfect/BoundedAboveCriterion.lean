module

public import StacksFrontier.AlgebraicGeometry.Spaces.CompactGeneration.QcqsUnitCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedGlobalSectionsAtModel
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.BoundedBelowCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DetectingBoundedAbove
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedTensorClosed
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedFibreBettiRepresented

/-!
# Detecting boundedness above with a perfect generator on an algebraic space

Let `X` be a quasi-compact and quasi-separated algebraic space, `G` a perfect object of `D(𝒪_X)`
generating `D_QCoh(𝒪_X)` and `E` an object of `D_QCoh(𝒪_X)`. Then `E` is bounded above if and
only if `Hom(G[-i], E) = 0` for `i ≫ 0`, if and only if `Ext^i(G, E) = 0` for `i ≫ 0`, if and only
if `RHom_X(G, E)` is bounded above, if and only if `H^i(X, G^∨ ⊗^L E) = 0` for `i ≫ 0`, if and only
if `RΓ(X, G^∨ ⊗^L E)` is bounded above, if and only if these hold for every perfect `P` in place of
`G` together with the vanishing of `H^i(X, P ⊗^L E)` for `i ≫ 0` (Stacks 0GFH).

## Main results

* `AlgebraicGeometry.Space.tfae_isLE_of_isPerfect_generator`: **Stacks 0GFH**.

## Implementation notes

As for Stacks 0GFI (`AlgebraicGeometry.Space.tfae_isGE_of_isPerfect_generator`): `Ext^i_X(G, E)`
is `Hom_{D(𝒪_X)}(G, E[i])`, `RΓ(X, -)` and `RHom_X(G, -)` are read in `D(Γ(X, 𝒪_X))`, and their
membership in `D⁻(ℤ)` is the vanishing of their cohomology in all sufficiently large degrees.

## References

* [Stacks Project, Tag 0GFH](https://stacks.math.columbia.edu/tag/0GFH)
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

/-- A complex is bounded above exactly when its cohomology vanishes in all sufficiently large
degrees. -/
theorem exists_isLE_iff_exists_isZero_homology {R : Type (u + 1)} [Ring R]
    (K : DerivedCategory (ModuleCat.{u + 1} R)) :
    (∃ a : ℤ, K.IsLE a) ↔
      ∃ N : ℤ, ∀ i : ℤ, N ≤ i → IsZero ((DerivedCategory.homologyFunctor _ i).obj K) := by
  simp only [DerivedCategory.isLE_iff]
  exact ⟨fun ⟨a, ha⟩ => ⟨a + 1, fun i hi => ha i (by omega)⟩,
    fun ⟨N, hN⟩ => ⟨N - 1, fun i hi => hN i (by omega)⟩⟩

/-- `RHom_X(P, E)` is bounded above exactly when `Ext^i(P, E) = 0` for `i ≫ 0`. -/
theorem exists_isLE_globalDerivedHom_iff (X : AlgebraicSpaces B S hS)
    (P E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) :
    (∃ a : ℤ, ((derivedModuleGlobalSectionsSmallEtaleAtModel B S hS X.1 X.2).obj
        (((smallEtaleDerivedSheafHom B S hS X).obj (op P)).obj E)).IsLE a) ↔
      ∃ N : ℤ, ∀ i : ℤ, N ≤ i → Subsingleton (P ⟶ E⟦i⟧) := by
  rw [exists_isLE_iff_exists_isZero_homology]
  exact exists_congr fun _ => forall_congr' fun i => imp_congr_right fun _ =>
    isZero_homology_globalDerivedHom_iff X P E i

/-- If `M` lies in degrees `≤ a` and `a + N ≤ i`, then `M⟦i⟧` lies in degrees `≤ -N`. -/
private theorem isLE_shift_neg_of_isLE (X : AlgebraicSpaces B S hS)
    (M : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (a i N : ℤ) [M.IsLE a]
    (h : a + N ≤ i) : (M⟦i⟧).IsLE (-N) :=
  have : (M⟦i⟧).IsLE (a - i) := DerivedCategory.TStructure.t.isLE_shift M a i (a - i) (by omega)
  DerivedCategory.TStructure.t.isLE_of_le _ (a - i) (-N) (by omega)

/-- **`RΓ(X, -)` has finite cohomological dimension on `D_QCoh(𝒪_X)`** for `X` quasi-compact and
quasi-separated: there is `N` with `H^i(X, M) = 0` for `i ≥ a + N` whenever `M` in `D_QCoh(𝒪_X)`
lies in degrees `≤ a`. -/
theorem exists_isZero_homology_derivedModuleGlobalSectionsSmallEtale_of_isLE
    (X : AlgebraicSpaces B S hS) (hqc : IsQuasiCompactSpace B S hS X.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1) :
    ∃ N : ℤ, ∀ (M : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)), QcohDerived B S hS X M →
      ∀ a : ℤ, M.IsLE a → ∀ i : ℤ, a + N ≤ i →
        IsZero ((DerivedCategory.homologyFunctor
          (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS X.1 X.2)) i).obj
            ((derivedModuleGlobalSectionsSmallEtaleAtModel B S hS X.1 X.2).obj M)) := by
  obtain ⟨N, hN⟩ := exists_hom_eq_zero_of_isCompactObject X hqc hqs _
    (isCompactObject_unitQuasicoherent_of_qcqs B.contains_terminal X hqc hqs)
  refine ⟨N, fun M hM a ha i hi => ?_⟩
  refine (isZero_homology_derivedModuleGlobalSectionsSmallEtale_iff X M i).2 fun g => ?_
  have := isLE_shift_neg_of_isLE X M a i N hi
  exact hN _ (qcohDerived_shift M i hM) this g

/-- **Stacks 0GFH.** Let `X` be a quasi-compact and quasi-separated algebraic space, `G` a perfect
object of `D(𝒪_X)` which generates `D_QCoh(𝒪_X)`, and `E` an object of `D_QCoh(𝒪_X)`. The
following are equivalent:
1. `E ∈ D⁻_QCoh(𝒪_X)`;
2. `Hom(G[-i], E) = 0` for `i ≫ 0`;
3. `Ext^i_X(G, E) = 0` for `i ≫ 0`;
4. `RHom_X(G, E)` is bounded above;
5. `H^i(X, G^∨ ⊗^L E) = 0` for `i ≫ 0`;
6. `RΓ(X, G^∨ ⊗^L E)` is bounded above;
7. for every perfect `P`: (2), (3), (4) hold with `P` in place of `G`, `H^i(X, P ⊗^L E) = 0` for
   `i ≫ 0`, and `RΓ(X, P ⊗^L E)` is bounded above. -/
@[stacks 0GFH]
theorem tfae_isLE_of_isPerfect_generator (X : AlgebraicSpaces B S hS)
    (hqc : IsQuasiCompactSpace B S hS X.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1)
    (G : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hG : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect G)
    (hgen : ∀ E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2,
      (∀ n : ℤ, Subsingleton (G⟦n⟧ ⟶ E.obj)) → IsZero E.obj)
    (E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) :
    List.TFAE [
      ∃ a : ℤ, E.obj.IsLE a,
      ∃ N : ℤ, ∀ i : ℤ, N ≤ i → Subsingleton (G⟦-i⟧ ⟶ E.obj),
      ∃ N : ℤ, ∀ i : ℤ, N ≤ i → Subsingleton (G ⟶ E.obj⟦i⟧),
      ∃ a : ℤ, ((derivedModuleGlobalSectionsSmallEtaleAtModel B S hS X.1 X.2).obj
        (((smallEtaleDerivedSheafHom B S hS X).obj (op G)).obj E.obj)).IsLE a,
      ∃ N : ℤ, ∀ i : ℤ, N ≤ i → IsZero ((DerivedCategory.homologyFunctor
        (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS X.1 X.2)) i).obj
          ((derivedModuleGlobalSectionsSmallEtaleAtModel B S hS X.1 X.2).obj
            (((smallEtaleDerivedTensor B S hS X).obj
              (smallEtaleDerivedDual B S hS X G)).obj E.obj))),
      ∃ a : ℤ, ((derivedModuleGlobalSectionsSmallEtaleAtModel B S hS X.1 X.2).obj
          (((smallEtaleDerivedTensor B S hS X).obj
            (smallEtaleDerivedDual B S hS X G)).obj E.obj)).IsLE a,
      ∀ P : DerivedCategory (Modules.{u, u} B S hS X.1 X.2),
        (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect P →
          (∃ N : ℤ, ∀ i : ℤ, N ≤ i → Subsingleton (P⟦-i⟧ ⟶ E.obj)) ∧
          (∃ N : ℤ, ∀ i : ℤ, N ≤ i → Subsingleton (P ⟶ E.obj⟦i⟧)) ∧
          (∃ a : ℤ, ((derivedModuleGlobalSectionsSmallEtaleAtModel B S hS X.1 X.2).obj
            (((smallEtaleDerivedSheafHom B S hS X).obj (op P)).obj E.obj)).IsLE a) ∧
          (∃ N : ℤ, ∀ i : ℤ, N ≤ i → IsZero ((DerivedCategory.homologyFunctor
            (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS X.1 X.2)) i).obj
              ((derivedModuleGlobalSectionsSmallEtaleAtModel B S hS X.1 X.2).obj
                (((smallEtaleDerivedTensor B S hS X).obj P).obj E.obj)))) ∧
          (∃ a : ℤ, ((derivedModuleGlobalSectionsSmallEtaleAtModel B S hS X.1 X.2).obj
              (((smallEtaleDerivedTensor B S hS X).obj P).obj E.obj)).IsLE a)] := by
  have h23 : ∀ P : DerivedCategory (Modules.{u, u} B S hS X.1 X.2),
      (∃ N : ℤ, ∀ i : ℤ, N ≤ i → Subsingleton (P⟦-i⟧ ⟶ E.obj)) ↔
        ∃ N : ℤ, ∀ i : ℤ, N ≤ i → Subsingleton (P ⟶ E.obj⟦i⟧) := fun P =>
    exists_congr fun _ => forall_congr' fun i => imp_congr_right fun _ =>
      subsingleton_hom_shift_neg_iff P E.obj i
  tfae_have 1 → 7 := by
    rintro ⟨a, ha⟩ P hP
    have hPq := derivedCategoryB_of_isPerfect B S hS X P hP
    obtain ⟨NP, hNP⟩ := exists_hom_eq_zero_of_isCompactObject X hqc hqs ⟨P, hPq⟩
      (isCompactObject_of_isPerfect X hqc hqs ⟨P, hPq⟩ hP)
    have h3 : ∃ N : ℤ, ∀ i : ℤ, N ≤ i → Subsingleton (P ⟶ E.obj⟦i⟧) :=
      ⟨a + NP, fun i hi => ⟨fun f g => by
        have := isLE_shift_neg_of_isLE X E.obj a i NP hi
        exact (hNP _ (qcohDerived_shift _ i E.property) this f).trans
          (hNP _ (qcohDerived_shift _ i E.property) this g).symm⟩⟩
    obtain ⟨m, hm'⟩ := exists_isLE_smallEtaleDerivedTensor_of_isPerfect_of_isLE hqc P hP E.obj a ha
    obtain ⟨N₀, hN₀⟩ := exists_isZero_homology_derivedModuleGlobalSectionsSmallEtale_of_isLE
      X hqc hqs
    have h5 : ∃ N : ℤ, ∀ i : ℤ, N ≤ i → IsZero ((DerivedCategory.homologyFunctor
        (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS X.1 X.2)) i).obj
          ((derivedModuleGlobalSectionsSmallEtaleAtModel B S hS X.1 X.2).obj
            (((smallEtaleDerivedTensor B S hS X).obj P).obj E.obj))) :=
      ⟨m + N₀, hN₀ _ (qcohDerived_smallEtaleDerivedTensor X _ _ hPq E.property) m hm'⟩
    exact ⟨(h23 P).2 h3, h3, (exists_isLE_globalDerivedHom_iff X P E.obj).2 h3, h5,
      (exists_isLE_iff_exists_isZero_homology _).2 h5⟩
  tfae_have 7 → 2 := fun h => (h G hG).1
  tfae_have 2 → 1 := by
    rintro ⟨N, hN⟩
    obtain ⟨hGc, hGg⟩ := isCompactObject_and_isWeakTriangulatedGenerator_of_isPerfect
      X hqc hqs G hG hgen
    exact exists_isLE_of_highHomVanishingOnCompact X hqc hqs E
      (highHomVanishingOnCompact_of_generator _ hGc hGg E.obj ⟨N, hN⟩)
  tfae_have 2 ↔ 3 := h23 G
  tfae_have 3 ↔ 4 := (exists_isLE_globalDerivedHom_iff X G E.obj).symm
  tfae_have 3 ↔ 5 := exists_congr fun _ => forall_congr' fun i => imp_congr_right fun _ =>
    subsingleton_hom_shift_iff_isZero_homology_tensorDual X G hG E.obj i
  tfae_have 5 ↔ 6 := (exists_isLE_iff_exists_isZero_homology _).symm
  tfae_finish

end AlgebraicGeometry.Space

end
