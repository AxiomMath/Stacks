module

public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposModuleAdjunction
public import StacksFrontier.Algebra.Module.Projective.Invertible
public import StacksFrontier.AlgebraicGeometry.NonvanishingTrivialization.Basic
public import StacksFrontier.RingTheory.Module.LocallyFree.SheafBridge
public import StacksFrontier.RingTheory.Norm.Projective
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Invertible modules on the spectrum of a ring with trivial Picard group

Let `R` be a commutative ring whose ring-theoretic Picard group `CommRing.Pic R` is trivial —
for instance a unique factorization domain. This file proves that every invertible sheaf of
`𝒪`-modules on `Spec R` is trivial, that is, isomorphic to `𝒪` itself. The module-theoretic
input, that an invertible module over such a ring is isomorphic to the ring, is Mathlib's
`Module.Invertible.free_iff_linearEquiv` applied to the instance `Module.Free R M` provided by
`Subsingleton (CommRing.Pic R)`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_of_sheafOfModules`: for a sheaf
  of modules on a scheme, finite local freeness of rank `r` stated through local generators is
  finite local freeness stated through trivializing opens.
* `Stacks.PicardUFD.invertible_of_isFiniteLocallyFreeOfRank_one`: a module which is finite
  locally free of rank one is invertible.
* `Stacks.PicardUFD.isTrivial_of_isInvertible_spec`: every invertible sheaf of modules on
  `Spec R` is trivial when `CommRing.Pic R` is trivial, and
  `Stacks.PicardUFD.isTrivial_of_isInvertible_spec_of_ufd` for `R` a unique factorization
  domain.

## References

* [Stacks Project, Tag 0BDA](https://stacks.math.columbia.edu/tag/0BDA)
* [Stacks Project, Tag 0BCH](https://stacks.math.columbia.edu/tag/0BCH)
* [Stacks Project, Tag 0B8I](https://stacks.math.columbia.edu/tag/0B8I)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 05JM](https://stacks.math.columbia.edu/tag/05JM)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The free sheaf of modules on an open `U` of a scheme, compared across the equivalence
between sheaves of modules over the localized site and sheaves of modules on `U`. -/
private def freeOverIso (X : Scheme.{u}) (U : X.Opens) (I : Type u) :
    SheafOfModules.free (R := ((U : Scheme).ringCatSheaf)) I ≅
      (Scheme.Modules.overEquiv U).functor.obj
        (SheafOfModules.free (R := X.ringCatSheaf.over U) I) := by
  let F := (Scheme.Modules.overEquiv U).functor
  haveI : Limits.PreservesColimitsOfShape.{u, u} (Discrete I) F :=
    Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint.{u, u, u, u + 1, u, u + 1} F
  exact @SheafOfModules.mapFreeIso _ _ _ _ _ _ _ _ _ _ _ _ F I this (Iso.refl _)

/-- Finite local freeness of rank `r` for a sheaf of modules on a scheme, stated through local
generators over a covering of the terminal object, implies it stated through a trivializing
open around each point. -/
theorem isFiniteLocallyFreeOfRank_of_sheafOfModules {X : Scheme.{u}} (F : X.Modules) (r : ℕ)
    (h : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r) :
    Scheme.Modules.IsFiniteLocallyFreeOfRank F r := by
  classical
  obtain ⟨q, hfree, hrank⟩ := h.exists_isFiniteLocallyFreeOfRankData
  intro x
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1
    (show x ∈ ⨆ i, q.X i by rw [(Opens.coversTop_iff _ _).1 q.coversTop]; trivial)
  have : IsIso (q.generators i).π := hfree.isIso i
  let eLocal : F.restrict (Scheme.Opens.ι (q.X i)) ≅
      SheafOfModules.free (q.generators i).I :=
    ((Scheme.Modules.overFunctorEquiv (q.X i)).app F).symm ≪≫
      (Scheme.Modules.overEquiv (q.X i)).functor.mapIso (asIso (q.generators i).π).symm ≪≫
      (freeOverIso X (q.X i) (q.generators i).I).symm
  exact ⟨q.X i, hi, ⟨eLocal ≪≫ (SheafOfModules.freeFunctor
    (R := (Scheme.Opens.toScheme (q.X i)).ringCatSheaf)).mapIso
      ((hrank i).some.trans Equiv.ulift.symm).toIso⟩⟩

end AlgebraicGeometry.Scheme.Modules

namespace Stacks.PicardUFD

/-- A module which is finite locally free of rank one is invertible. -/
theorem invertible_of_isFiniteLocallyFreeOfRank_one {R M : Type u} [CommRing R] [AddCommGroup M]
    [Module R M] (h : Module.IsFiniteLocallyFreeOfRank R M 1) : Module.Invertible R M := by
  obtain ⟨ι, f, hspan, hb⟩ := h
  obtain ⟨hfin, hproj⟩ := Module.finite_and_projective_of_isFiniteLocallyFree
    (R := R) (M := M) ⟨ι, f, hspan, fun i => ⟨Module.Free.of_basis (hb i).some,
      Module.Finite.of_basis (hb i).some⟩⟩
  have hrank : Module.rankAtStalk M = Function.const (PrimeSpectrum R) 1 :=
    funext (Module.rankAtStalk_eq_of_isFiniteLocallyFreeOfRank 1 ⟨ι, f, hspan, hb⟩)
  have h12 := (Module.finite_projective_rankAtStalk_one_tfae_invertible_exists_tensor_inverse.{u,
    u, u} R M).1.out 1 2
  exact h12.mp ⟨hfin, hproj, hrank⟩

/-- Every invertible sheaf of modules on the spectrum of a ring with trivial Picard group is
trivial. -/
theorem isTrivial_of_isInvertible_spec (R : Type u) [CommRing R]
    [Subsingleton (CommRing.Pic R)] (L : (Spec (CommRingCat.of R)).Modules)
    [Stacks.SheafOfModules.IsInvertible (Spec (CommRingCat.of R)).presheaf
      (structureSheafRing (Spec (CommRingCat.of R)).toRingedSpace).property L] :
    Stacks.SheafOfModules.IsTrivial (Spec (CommRingCat.of R)).presheaf
      (structureSheafRing (Spec (CommRingCat.of R)).toRingedSpace).property L := by
  have := Stacks.SheafOfModules.Scheme.isQuasicoherent_of_isInvertible _ L
  have hiso : IsIso L.fromTildeΓ := inferInstance
  let e : tilde (R := CommRingCat.of R)
      (ModuleCat.of R (moduleSpecΓFunctor.obj L)) ≅ L := @asIso _ _ _ _ L.fromTildeΓ hiso
  have hL := (Stacks.SheafOfModules.Scheme.isInvertible_iff_isFiniteLocallyFreeOfRank_one
    _ L).1 ‹_›
  have hpt : Scheme.Modules.IsFiniteLocallyFreeOfRank
      (tilde (R := CommRingCat.of R) (ModuleCat.of R (moduleSpecΓFunctor.obj L))) 1 := by
    intro x
    obtain ⟨U, hxU, ⟨φ⟩⟩ :=
      Scheme.Modules.isFiniteLocallyFreeOfRank_of_sheafOfModules L 1 hL x
    exact ⟨U, hxU, ⟨(Scheme.Modules.restrictFunctor (Scheme.Opens.ι U)).mapIso e ≪≫ φ⟩⟩
  have : Module.Invertible R (moduleSpecΓFunctor.obj L) :=
    invertible_of_isFiniteLocallyFreeOfRank_one
      ((tilde_isFiniteLocallyFreeOfRank_iff R (moduleSpecΓFunctor.obj L) 1).mp hpt)
  obtain ⟨φ⟩ := (Module.Invertible.free_iff_linearEquiv (R := R)
    (M := moduleSpecΓFunctor.obj L)).mp inferInstance
  exact ⟨e.symm ≪≫ (tilde.functor (CommRingCat.of R)).mapIso φ.toModuleIso ≪≫ tildeSelf⟩

/-- Every invertible sheaf of modules on the spectrum of a unique factorization domain is
trivial. -/
@[ega "I 2.4.8"]
theorem isTrivial_of_isInvertible_spec_of_ufd (R : Type u) [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] (L : (Spec (CommRingCat.of R)).Modules)
    [Stacks.SheafOfModules.IsInvertible (Spec (CommRingCat.of R)).presheaf
      (structureSheafRing (Spec (CommRingCat.of R)).toRingedSpace).property L] :
    Stacks.SheafOfModules.IsTrivial (Spec (CommRingCat.of R)).presheaf
      (structureSheafRing (Spec (CommRingCat.of R)).toRingedSpace).property L :=
  have : GCDMonoid R := UniqueFactorizationMonoid.toGCDMonoid R
  isTrivial_of_isInvertible_spec R L

end Stacks.PicardUFD

end
