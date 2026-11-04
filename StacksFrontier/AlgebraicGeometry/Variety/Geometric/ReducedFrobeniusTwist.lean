module

public import Mathlib.FieldTheory.IsPerfectClosure
public import Mathlib.FieldTheory.PurelyInseparable.AdjoinPthRoots
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Frobenius
public import StacksFrontier.AlgebraicGeometry.Variety.Frobenius.Twist
public import StacksFrontier.AlgebraicGeometry.Variety.Geometric.ReducedTFAE

/-!
# Geometric reducedness and the Frobenius twist

For a scheme over a field of positive characteristic, geometric reducedness is equivalent to
reducedness of its Frobenius twist.

## Main results

* `AlgebraicGeometry.geometricallyReduced_iff_isReduced_frobeniusTwist` characterizes geometric
  reducedness by reducedness after Frobenius base change.

## Implementation notes

The Frobenius twist is the base change functor along the absolute Frobenius of `Spec k`. The
characteristic of `Spec k` follows from the characteristic of `k` via its identity structure
morphism.

## References

* [Stacks Project, Tag 0CCE](https://stacks.math.columbia.edu/tag/0CCE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CommRingCat
open Stacks.Frobenius

namespace AlgebraicGeometry

universe u

/-- The absolute Frobenius of the spectrum of a field of characteristic `p` is the spectrum of
the `p`-th power map of that field. -/
private theorem absoluteFrobenius_spec_eq {k : Type u} [Field k] (p : ℕ) [Fact p.Prime]
    [CharP k p] (hS : IsInCharacteristic (Spec (.of k)) p) :
    absoluteFrobenius (Spec (.of k)) p hS =
      Spec.map (CommRingCat.ofHom (frobenius k p)) := by
  let F := absoluteFrobenius (Spec (.of k)) p hS
  have hF : F = Spec.map (Spec.preimage F) := by simp
  show F = Spec.map (CommRingCat.ofHom (frobenius k p))
  rw [hF, Spec.map_inj]
  calc
    Spec.preimage F = Spec.preimage F ≫ (Scheme.ΓSpecIso (.of k)).inv ≫
        (Scheme.ΓSpecIso (.of k)).hom := by simp
    _ = (Scheme.ΓSpecIso (.of k)).inv ≫ F.appTop ≫ (Scheme.ΓSpecIso (.of k)).hom := by
      rw [← Category.assoc, Scheme.ΓSpecIso_inv_naturality, ← hF]
      simp [Category.assoc]
    _ = CommRingCat.ofHom (frobenius k p) := by
      ext x
      show (Scheme.ΓSpecIso (.of k)).hom.hom
        ((absoluteFrobenius (Spec (.of k)) p hS).appLE ⊤ ⊤ (by simp)
          ((Scheme.ΓSpecIso (.of k)).inv.hom x)) = x ^ p
      rw [absoluteFrobenius_appLE_apply]
      simp

/-- **Stacks Project, Tag 0CCE.** A scheme over a field of characteristic `p > 0` is
geometrically reduced if and only if its Frobenius twist is reduced. -/
@[stacks 0CCE]
public theorem geometricallyReduced_iff_isReduced_frobeniusTwist
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) :
    let hS : IsInCharacteristic (Spec (.of k)) p :=
      Stacks.Frobenius.isInCharacteristic_of_over (Over.mk (𝟙 (Spec (.of k))))
    GeometricallyReduced f ↔
      IsReduced (((frobeniusTwist (Spec (.of k)) p hS).obj (Over.mk f)).left) := by
  let hS := Stacks.Frobenius.isInCharacteristic_of_over (Over.mk (𝟙 (Spec (.of k))))
  show GeometricallyReduced f ↔
    IsReduced (((frobeniusTwist (Spec (.of k)) p hS).obj (Over.mk f)).left)
  let : ExpChar k p := inferInstance
  let kperf : Type u := PerfectClosure k p
  let : Algebra k kperf := (PerfectClosure.of k p).toAlgebra
  let : IsPerfectClosure (algebraMap k kperf) p := PerfectClosure.isPRadical k p
  have ht := geometricallyReduced_tfae k p f kperf (AlgebraicClosure k)
  let A : Type u := AdjoinPthRoots k
  let g : Spec (.of A) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k A))
  let r := (AdjoinPthRoots.root k).toCommRingCatIso
  let e : Spec (.of k) ≅ Spec (.of A) :=
    (AlgebraicGeometry.Scheme.Spec.mapIso r.op).symm
  let F := absoluteFrobenius (Spec (.of k)) p hS
  have hcomp : e.hom ≫ g = F := by
    dsimp [e, r, g, F]
    rw [absoluteFrobenius_spec_eq, ← Spec.map_comp]
    apply congrArg Spec.map
    ext x
    show (AdjoinPthRoots.root k).symm (algebraMap k A x) = x ^ p
    rw [← AdjoinPthRoots.root_pow p x, map_pow, RingEquiv.symm_apply_apply]
  have h₂ : g = e.inv ≫ F := by rw [← hcomp]; simp
  have hred : IsReduced (pullback f g) ↔ IsReduced (pullback f F) :=
    CategoryTheory.ObjectProperty.prop_iff_of_iso (IsReduced ·)
      (asIso (pullback.map f g f F (𝟙 X) e.inv (𝟙 _) (by simp) (by simpa using h₂)))
  simpa only [frobeniusTwist_obj_left, Over.mk_hom] using
    (show GeometricallyReduced f ↔ IsReduced (pullback f g) from by
      simpa [g] using ht.out 1 4).trans hred

end AlgebraicGeometry
