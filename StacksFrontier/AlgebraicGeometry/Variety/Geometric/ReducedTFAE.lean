module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Data.List.TFAE
public import Mathlib.FieldTheory.IsPerfectClosure
public import Mathlib.FieldTheory.PurelyInseparable.AdjoinPthRoots
public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Reduced

/-!
# Characterizations of geometrically reduced schemes

For a scheme over a field, geometric reducedness can be tested after arbitrary field extensions,
after finite purely inseparable extensions, after adjoining all `p`-th roots, after passing to a
perfect closure or an algebraic closure, or on the rings of sections of affine opens.

## Main results

* `AlgebraicGeometry.geometricallyReduced_tfae` gives the seven equivalent characterizations of a
  geometrically reduced scheme.

## Implementation notes

The seven entries of the `List.TFAE` are the seven numbered conditions in the source. The fields
serving as the perfect closure and algebraic closure are given abstractly, so the result is
independent of chosen models. Mathlib's `AdjoinPthRoots k` is `k^{1/p}` for the exponential
characteristic `p`. The algebra structure on the sections of an affine open is induced canonically
by the structure morphism.

The reduction to the ring-theoretic statement `Algebra.isGeometricallyReduced_tfae` goes through
an affine open cover: base change commutes with restriction to an affine open, and over an affine
open the base change is the spectrum of a tensor product of rings.

## References

* [Stacks Project, Tag 035X](https://stacks.math.columbia.edu/tag/035X)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CommRingCat

namespace AlgebraicGeometry

universe u

section

open scoped TensorProduct

/-- Over an affine open, reducedness of the base change along a field extension is reducedness
of the corresponding tensor product of rings. -/
private theorem reduced_pullback_affine_iff
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (L : Type u) [Field L] [Algebra k L] (U : X.affineOpens) :
    letI : Algebra k Γ(X, U.1) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U.1 (by simp)).hom.toAlgebra
    _root_.IsReduced (L ⊗[k] Γ(X, U.1)) ↔
      IsReduced (pullback (U.1.ι ≫ f)
        (Spec.map (CommRingCat.ofHom (algebraMap k L)))) := by
  let : Algebra k Γ(X, U.1) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U.1 (by simp)).hom.toAlgebra
  let A := Γ(X, U.1)
  let s := Spec.map (CommRingCat.ofHom (algebraMap k A))
  let g := Spec.map (CommRingCat.ofHom (algebraMap k L))
  let fU := U.1.ι ≫ f
  have hspec : s = U.2.fromSpec ≫ f := by
    change Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫
      f.appLE ⊤ U.1 (by simp)) = U.2.fromSpec ≫ f
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) U.2 (by simp), Spec.map_comp,
      IsAffineOpen.fromSpec_top]
    congr 1
    rw [← cancel_mono (Spec (.of k)).toSpecΓ]
    simp
  have hcomp : U.2.isoSpec.inv ≫ fU = s := by
    rw [U.2.isoSpec_inv_ι_assoc, hspec]
  let m : pullback s g ⟶ pullback fU g :=
    pullback.map s g fU g U.2.isoSpec.inv (𝟙 _) (𝟙 _) hcomp.symm (by simp)
  have : IsIso m := by
    dsimp [m]
    apply pullback.map_isIso
  let e : pullback s g ≅ pullback fU g := asIso m
  let eSpec := pullbackSpecIso k A L
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have : _root_.IsReduced (A ⊗[k] L) :=
      isReduced_of_injective (Algebra.TensorProduct.comm k A L)
        (Algebra.TensorProduct.comm k A L).injective
    exact ObjectProperty.prop_of_iso IsReduced e
      (ObjectProperty.prop_of_iso IsReduced eSpec.symm ((affine_isReduced_iff _).2 this))
  · have : _root_.IsReduced (A ⊗[k] L) := (affine_isReduced_iff _).mp
      (ObjectProperty.prop_of_iso IsReduced eSpec (ObjectProperty.prop_of_iso IsReduced e.symm h))
    exact isReduced_of_injective (Algebra.TensorProduct.comm k L A)
      (Algebra.TensorProduct.comm k L A).injective

/-- Reducedness of the base change along a field extension is detected on the rings of sections
of the affine opens. -/
private theorem reduced_baseChange_iff_affine_sections
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (L : Type u) [Field L] [Algebra k L] :
    IsReduced (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k L)))) ↔
      ∀ U : X.affineOpens, letI : Algebra k Γ(X, U.1) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U.1 (by simp)).hom.toAlgebra
        _root_.IsReduced (L ⊗[k] Γ(X, U.1)) := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap k L))
  let 𝒰 : X.OpenCover := X.openCoverOfIsOpenCover
    (fun U : X.affineOpens => U)
    X.isBasis_affineOpens.isOpenCover
  let 𝒱 := Scheme.Pullback.openCoverOfLeft 𝒰 f g
  rw [IsReduced.iff_of_openCover (pullback f g) 𝒱]
  have he (U : X.affineOpens) : pullback (U.1.ι ≫ f) g ≅ 𝒱.X U := by
    dsimp [𝒱, Scheme.Pullback.openCoverOfLeft]
    exact pullback.congrHom rfl (by simp)
  exact ⟨fun h U => (reduced_pullback_affine_iff k f L U).mpr
      (ObjectProperty.prop_of_iso IsReduced (he U).symm (h U)),
    fun h U => ObjectProperty.prop_of_iso IsReduced (he U)
      ((reduced_pullback_affine_iff k f L U).mp (h U))⟩

end

/-- **Stacks Project, Tag 035X.** The seven standard characterizations of geometric reducedness
for a scheme over a field are equivalent. -/
@[stacks 035X]
public theorem geometricallyReduced_tfae
    (k : Type u) [Field k] (p : ℕ) [ExpChar k p] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k))
    (kperf : Type u) [Field kperf] [Algebra k kperf] [ExpChar kperf p]
    [PerfectRing kperf p] [IsPerfectClosure (algebraMap k kperf) p]
    (K : Type u) [Field K] [Algebra k K] [IsAlgClosure k K] :
    let isReducedAfterBaseChange := fun (k' : Type u) [Field k'] [Algebra k k'] ↦
      IsReduced (pullback f (Spec.map (ofHom (algebraMap k k'))))
    let geometricallyReducedSections := fun U : X.Opens ↦
      letI : Algebra k Γ(X, U) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U (by simp)).hom.toAlgebra
      Algebra.IsGeometricallyReduced k Γ(X, U)
    List.TFAE
      [ GeometricallyReduced f,
        ∀ (k' : Type u) [Field k'] [Algebra k k'], isReducedAfterBaseChange k',
        ∀ (k' : Type u) [Field k'] [Algebra k k'] [FiniteDimensional k k']
          [IsPurelyInseparable k k'], isReducedAfterBaseChange k',
        isReducedAfterBaseChange (AdjoinPthRoots k),
        isReducedAfterBaseChange kperf,
        isReducedAfterBaseChange K,
        ∀ U : X.affineOpens, geometricallyReducedSections U.1 ] := by
  classical
  tfae_have 1 ↔ 2 := by
    rw [GeometricallyReduced.eq_geometrically,
      geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  tfae_have 2 → 7 := by
    intro h U
    let : Algebra k Γ(X, U.1) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U.1 (by simp)).hom.toAlgebra
    have hbase : ∀ (L : Type u) [Field L] [Algebra k L],
        _root_.IsReduced (TensorProduct k L Γ(X, U.1)) := by
      intro L _ _
      exact (reduced_baseChange_iff_affine_sections k f L).mp (h L) U
    exact ((Algebra.isGeometricallyReduced_tfae k p Γ(X, U.1) kperf K).out 5 6).mp hbase
  tfae_have 7 → 2 := by
    intro h L _ _
    refine (reduced_baseChange_iff_affine_sections k f L).mpr fun U => ?_
    let : Algebra k Γ(X, U.1) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U.1 (by simp)).hom.toAlgebra
    have hAll : ∀ (L' : Type u) [Field L'] [Algebra k L'],
        _root_.IsReduced (TensorProduct k L' Γ(X, U.1)) :=
      ((Algebra.isGeometricallyReduced_tfae k p Γ(X, U.1) kperf K).out 6 5).mp (h U)
    exact hAll L
  tfae_have 3 → 7 := by
    intro h U
    let : Algebra k Γ(X, U.1) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U.1 (by simp)).hom.toAlgebra
    have hPI : ∀ (L : Type u) [Field L] [Algebra k L] [FiniteDimensional k L]
        [IsPurelyInseparable k L], _root_.IsReduced (TensorProduct k L Γ(X, U.1)) := by
      intro L _ _ _ _
      exact (reduced_baseChange_iff_affine_sections k f L).mp (h L) U
    exact ((Algebra.isGeometricallyReduced_tfae k p Γ(X, U.1) kperf K).out 1 6).mp hPI
  tfae_have 2 → 3 := fun h L _ _ _ _ => h L
  tfae_have 4 → 7 := fun h U =>
    let : Algebra k Γ(X, U.1) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U.1 (by simp)).hom.toAlgebra
    ((Algebra.isGeometricallyReduced_tfae k p Γ(X, U.1) kperf K).out 2 6).mp
      ((reduced_baseChange_iff_affine_sections k f _).mp h U)
  tfae_have 2 → 4 := fun h => h _
  tfae_have 5 → 7 := fun h U =>
    let : Algebra k Γ(X, U.1) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U.1 (by simp)).hom.toAlgebra
    ((Algebra.isGeometricallyReduced_tfae k p Γ(X, U.1) kperf K).out 3 6).mp
      ((reduced_baseChange_iff_affine_sections k f _).mp h U)
  tfae_have 2 → 5 := fun h => h kperf
  tfae_have 6 → 7 := fun h U =>
    let : Algebra k Γ(X, U.1) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U.1 (by simp)).hom.toAlgebra
    ((Algebra.isGeometricallyReduced_tfae k p Γ(X, U.1) kperf K).out 4 6).mp
      ((reduced_baseChange_iff_affine_sections k f _).mp h U)
  tfae_have 2 → 6 := fun h => h K
  tfae_finish

end AlgebraicGeometry
