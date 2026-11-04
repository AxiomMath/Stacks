module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDerivedHomDualCore
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.DualOfAPerfectComplex
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Triangles

/-!
# Cohomological bounds in the proof of Stacks 0DJU

Let `f : X ⟶ S` be a morphism of schemes and `(Kₙ)` a system of perfect objects of `D(𝒪_X)`
whose transition maps `Kₙ ⟶ Kₙ₊₁` are isomorphisms on `Hⁱ` for `i ≥ -n`, and let
`E ∈ D(𝒪_X)` move lower bounds uniformly: `E ⊗^L Lf^*Y ∈ D^{≥ m + a}` for `Y ∈ D^{≥ m}`. The
proof of [Stacks, Tag 0DJU] shows that the transition maps `Lₙ ⟶ Lₙ₊₁` of the dual system
`Lₙ = (Rf_* R𝓗om(Kₙ, E))^∨` are isomorphisms on `Hⁱ` for `i ≥ -n - a + 1`, which makes
`L = hocolim Lₙ` pseudo-coherent. This file proves those bounds.

The cone of `Lₙ ⟶ Lₙ₊₁` is `N^∨` with `N = Rf_* R𝓗om(Qₙ, E)` and `Qₙ` the cone of `Kₙ ⟶ Kₙ₊₁`,
which lies in `D^{≤ -n-1}`. A morphism `N^∨ ⟶ M[-j]` with `M` quasi-coherent is a morphism
`Qₙ ⟶ E ⊗^L Lf^*M[-j]` (`subsingleton_hom_dual_pushforward_sheafHom`), which vanishes for
`j > -n-1-a`; and the top-cohomology argument of the proof of [Stacks, Tag 08IF]
(`DerivedCategory.isLE_of_subsingleton_hom_single`) turns this into `N^∨ ∈ D^{≤ -n-1-a}`.

## Implementation notes

As in `StacksFrontier.AlgebraicGeometry.Perfect.RelativeDerivedHomDualCore`, the derived categories
are read at the standard model, which is the only one in the import closure of this file, and the
projection formula and the bound on `E` are hypotheses on the terms: both are proved in files
that bring the locally small model into scope, and the main file
`StacksFrontier.AlgebraicGeometry.Perfect.RelativeDerivedHomDual` discharges them.

## References

* [Stacks Project, Tag 0DJU](https://stacks.math.columbia.edu/tag/0DJU)
* [Stacks Project, Tag 08IF](https://stacks.math.columbia.edu/tag/08IF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry DerivedCategory

universe u

namespace DerivedCategory

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

/-- **The third vertex of a distinguished triangle whose first map is an isomorphism on `Hⁱ` for
`i ≥ a` lies in `D^{≤ a - 1}`.** -/
theorem isLE_obj₃_of_isIso_homologyMap_mor₁ (T : Triangle (DerivedCategory C))
    (hT : T ∈ distTriang _) (a : ℤ)
    (h : ∀ i : ℤ, a ≤ i → IsIso ((homologyFunctor C i).map T.mor₁)) : T.obj₃.IsLE (a - 1) := by
  rw [isLE_iff]
  intro i hi
  have := h i (by omega)
  have := h (i + 1) (by omega)
  have h₂ : (homologyFunctor C i).map T.mor₂ = 0 :=
    (HomologySequence.epi_homologyMap_mor₁_iff T hT i).1 inferInstance
  have hδ : HomologySequence.δ T i (i + 1) (by omega) = 0 :=
    (HomologySequence.mono_homologyMap_mor₁_iff T hT i (i + 1) (by omega)).1 inferInstance
  have : Epi ((homologyFunctor C i).map T.mor₂) :=
    (HomologySequence.epi_homologyMap_mor₂_iff T hT i (i + 1) (by omega)).2 hδ
  exact IsZero.of_epi_eq_zero _ h₂

end DerivedCategory

namespace Stacks.AlgebraicGeometry.RelativeDerivedHomDual

open Stacks.SheafOfModules

attribute [local implicit_reducible] TopCat.Sheaf structureSheafRing CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

section StandardModel

-- The only model of the derived categories in the import closure of this file; see the module
-- docstring of `StacksFrontier.AlgebraicGeometry.Perfect.RelativeDerivedHomDualCore`.
attribute [local instance] HasDerivedCategory.standard

open MonoidalCategory

attribute [local instance] derivedMonoidalStructure derivedSymmetricStructure

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- A quasi-coherent module placed in degree `j` has quasi-coherent cohomology sheaves. -/
theorem isQuasicoherent_homology_singleFunctor {S : Scheme.{u}} (M : StructureSheafModules S.sheaf)
    (hM : M.IsQuasicoherent) (j i : ℤ) :
    ((HStd S i).obj ((singleStd S j).obj M)).IsQuasicoherent := by
  rcases lt_trichotomy i j with hij | rfl | hij
  · exact (SheafOfModules.isQuasicoherent _).prop_of_isZero
      (isZero_of_isGE ((singleStd S j).obj M) j i hij)
  · exact (SheafOfModules.isQuasicoherent _).prop_of_iso
      ((singleFunctorCompHomologyFunctorIso _ i).app M).symm hM
  · exact (SheafOfModules.isQuasicoherent _).prop_of_isZero
      (isZero_of_isLE ((singleStd S j).obj M) j i hij)

/-- **The dual of a pushed-forward internal Hom out of a bounded above perfect object is bounded
above**, with the bound moved by the lower bound `a` of `E`: for `Q ∈ D^{≤ q}` perfect,
`(Rf_* R𝓗om(Q, E))^∨ ∈ D^{≤ q - a}`.

`hE` says that `E ⊗^L Lf^* -` moves lower bounds by `a`, and `proj` is the projection formula
at quasi-coherent modules placed in a single degree. -/
theorem isLE_derivedDual_pushforward_sheafHom [CompactSpace S] (Q E : DStd X)
    (hQ : IsPerfectSite Q)
    (hN : IsPerfectSite ((pushStd f).obj (((derivedSheafHom X.sheaf).obj (op Q)).obj E)))
    (q a : ℤ) (hq : Q.IsLE q)
    (hE : ∀ (Y : DStd S) (m : ℤ), Y.IsGE m → (E ⊗ (pullStd f).obj Y).IsGE (m + a))
    (proj : ∀ (M : StructureSheafModules S.sheaf), M.IsQuasicoherent → ∀ j : ℤ,
      Nonempty ((pushStd f).obj (((derivedSheafHom X.sheaf).obj (op Q)).obj E) ⊗
          (singleStd S j).obj M ≅
        (pushStd f).obj ((((derivedSheafHom X.sheaf).obj (op Q)).obj E) ⊗
          (pullStd f).obj ((singleStd S j).obj M)))) :
    (derivedDual S.sheaf
      ((pushStd f).obj (((derivedSheafHom X.sheaf).obj (op Q)).obj E)) : DStd S).IsLE (q - a) := by
  obtain ⟨b, hb⟩ := Stacks.DerivedQCoh.exists_isLE_derivedDual S
    ((pushStd f).obj (((derivedSheafHom X.sheaf).obj (op Q)).obj E))
    (isPerfect_ringedSpace_of_isPerfectSite hN)
  refine isLE_of_subsingleton_hom_single
    (fun M : StructureSheafModules S.sheaf => M.IsQuasicoherent)
    (fun e hM => (SheafOfModules.isQuasicoherent _).prop_of_iso e hM) _ b (q - a) hb
    (fun j => Stacks.DerivedQCoh.isQuasicoherent_homology_derivedDual S _
      (isPerfect_ringedSpace_of_isPerfectSite hN) j)
    (fun j hj M hM => ?_)
  obtain ⟨e⟩ := proj M hM j
  refine subsingleton_hom_dual_pushforward_sheafHom f Q E hQ hN _ e
    (subsingleton_of_forall_eq 0 fun g => ?_)
  exact TStructure.t.zero_of_isLE_of_isGE g q (j + a) (by omega) hq
    (hE ((singleStd S j).obj M) j inferInstance)

/-- **The transition maps of the dual system are isomorphisms in high degrees.** Let `(Kₙ)` be a
system of perfect objects of `D(𝒪_X)` whose transition maps are isomorphisms on `Hⁱ` for
`i ≥ -n`, and let `E` move lower bounds by `a`. Then the transition map `Lₖ ⟶ Lₖ₊₁` of
`Lₙ = (Rf_* R𝓗om(Kₙ, E))^∨` is an isomorphism on `Hⁱ` for `i ≥ -k - a + 1`.

`hpush` is the perfectness of `Rf_*` of the internal Homs out of perfect objects and `proj`
the projection formula at quasi-coherent modules placed in a single degree. -/
theorem isIso_homology_dualSystem_map [CompactSpace S] (F : ℕ ⥤ DStd X)
    (hF : ∀ n, IsPerfectSite (F.obj n))
    (htr : ∀ (n : ℕ) (i : ℤ), -(n : ℤ) ≤ i →
      IsIso ((HStd X i).map (F.map (homOfLE (Nat.le_succ n)))))
    (E : DStd X)
    (hpush : ∀ Q : DStd X, IsPerfectSite Q →
      IsPerfectSite ((pushStd f).obj (((derivedSheafHom X.sheaf).obj (op Q)).obj E)))
    (a : ℤ) (hE : ∀ (Y : DStd S) (m : ℤ), Y.IsGE m → (E ⊗ (pullStd f).obj Y).IsGE (m + a))
    (proj : ∀ Q : DStd X, IsPerfectSite Q →
      ∀ (M : StructureSheafModules S.sheaf), M.IsQuasicoherent → ∀ j : ℤ,
      Nonempty ((pushStd f).obj (((derivedSheafHom X.sheaf).obj (op Q)).obj E) ⊗
          (singleStd S j).obj M ≅
        (pushStd f).obj ((((derivedSheafHom X.sheaf).obj (op Q)).obj E) ⊗
          (pullStd f).obj ((singleStd S j).obj M))))
    (k : ℕ) (i : ℤ) (hi : -(k : ℤ) - a + 1 ≤ i) :
    IsIso ((HStd S i).map ((dualSystem (pushforwardSheafHomSystem f F E)).map
      (homOfLE (Nat.le_succ k)))) := by
  obtain ⟨Q, g, h, hT⟩ := distinguished_cocone_triangle (F.map (homOfLE (Nat.le_succ k)))
  have hQ : IsPerfectSite Q := isPerfectSite_of_isPerfect_ringedSpace
    (@Stacks.Cohomology.PerfectComplexTriangles.isPerfect_obj₃_of_distinguished X.toRingedSpace
      (HasDerivedCategory.standard _) (Triangle.mk (F.map (homOfLE (Nat.le_succ k))) g h) hT
      (isPerfect_ringedSpace_of_isPerfectSite (hF k))
      (isPerfect_ringedSpace_of_isPerfectSite (hF (k + 1))))
  have hQle : Q.IsLE (-(k : ℤ) - 1) :=
    isLE_obj₃_of_isIso_homologyMap_mor₁ _ hT (-(k : ℤ)) (htr k)
  obtain ⟨δ, hTd⟩ := exists_distinguished_dual_pushforward_sheafHom f E _ hT
  have hD := isLE_derivedDual_pushforward_sheafHom f Q E hQ (hpush Q hQ) (-(k : ℤ) - 1) a hQle hE
    (proj Q hQ)
  exact isIso_homologyMap_mor₁_of_isLE _ hTd (-(k : ℤ) - 1 - a) hD i (by omega)

end StandardModel

end Stacks.AlgebraicGeometry.RelativeDerivedHomDual
