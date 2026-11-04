module

public import StacksFrontier.AlgebraicGeometry.AffineExtend.Induction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Extending a finite type submodule from a quasi-compact open, below a given one

Let `Y` be a quasi-compact and quasi-separated scheme, `F` an `𝒪_Y`-module, `K ⊆ F` a
quasi-coherent submodule, `U ⊆ Y` a quasi-compact open and `D ⊆ F|_U` a quasi-coherent
submodule of finite type contained in `K|_U`. Then there is a quasi-coherent submodule `N ⊆ K`
of finite type whose restriction to `U` is exactly `D`.

This is [Stacks, Tag 01PF] with the extension kept below a prescribed quasi-coherent
submodule. It is the module form of `Stacks.FiniteTypeIdealSheaf.exists_isFiniteType_le_comap_eq`,
which is the case `F = 𝒪_Y` read through
`AlgebraicGeometry.Scheme.IdealSheafData.unitSubmodule` and
`Stacks.FiniteTypeIdealSheaf.isFiniteType_unitSubmodule_iff`; and it is the scheme input, on a
quasi-compact open, of the extension of finite type quasi-coherent submodules on a
quasi-compact quasi-separated algebraic space (the module form of [Stacks, Tag 0829] compatible
with a chart, proved along [Stacks, Tag 08GP]).

## Main definitions

* `Stacks.FiniteTypeSubmodule.asSubmoduleOf`: a submodule `P ≤ N` of a sheaf of modules `M`,
  read as a submodule of the sheaf of modules of `N`.

## Main results

* `Stacks.FiniteTypeSubmodule.compose_asSubmoduleOf`: composing back gives `P`.
* `Stacks.FiniteTypeSubmodule.restrictTo_compose`, `Stacks.FiniteTypeSubmodule.restrictTo_inf`:
  restriction to an open commutes with composition and with binary infima of submodules.
* `Stacks.FiniteTypeSubmodule.exists_isFiniteType_le_restrictTo_eq`: a quasi-coherent submodule
  of finite type of `F|_U` below `K|_U` is the restriction of a quasi-coherent submodule of
  finite type of `F` below `K`.

## Implementation notes

The extension applies [Stacks, Tag 01PF], in the form
`Stacks.AlgebraicGeometry.Tag01PFAffineExtend.exists_isFiniteType_submodule_restrictTo_eq_of_qcqs`,
to the quasi-coherent module `K` itself rather than to `F`. The prescribed `D` is read as a
submodule of `K|_U`, namely as the restriction of `coRestrict D ⊓ K` read inside `K` by
`asSubmoduleOf`, which gives it the spelling `(K|_U).Submodule` that Tag 01PF asks for. The
extension found inside `K` is carried back to a submodule of `F` by
`Stacks.AlgebraicGeometry.SubmodulePrimitives.compose`, which does not change the underlying
module (`Stacks.AlgebraicGeometry.SubmodulePrimitives.composeIso`).

## References

* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
* [Stacks Project, Tag 0829](https://stacks.math.columbia.edu/tag/0829)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.SubmodulePrimitives Stacks.AlgebraicGeometry.SubmoduleRestrict

universe v v₁ u₁ u

namespace Stacks.FiniteTypeSubmodule

/-! ### A submodule below `N`, read inside `N` -/

section General

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  {M : SheafOfModules.{v} R}

/-- A submodule `P ≤ N` of a sheaf of modules `M`, read as a submodule of the sheaf of modules
of `N`: over an object its sections are the sections of `N` which lie in `P`. -/
def asSubmoduleOf (N P : M.Submodule) (_h : P ≤ N) : N.toSheafOfModules.Submodule where
  obj U := (P.obj U).comap (N.obj U).subtype
  map g := fun _ hs => P.map_mem g hs
  isSheaf := fun _ s hs => P.isSheaf s.1 hs

/-- A section of `N` lies in `asSubmoduleOf N P h` if and only if it lies in `P`. -/
theorem mem_asSubmoduleOf_iff (N P : M.Submodule) (h : P ≤ N) (U : Cᵒᵖ) (s : ↥(N.obj U)) :
    s ∈ (asSubmoduleOf N P h).obj U ↔ s.1 ∈ P.obj U :=
  Iff.rfl

/-- **Composing back gives the submodule one started from.** -/
theorem compose_asSubmoduleOf (N P : M.Submodule) (h : P ≤ N) :
    compose N (asSubmoduleOf N P h) = P := by
  refine SheafOfModules.Submodule.ext (PresheafOfModules.Submodule.ext fun U => ?_)
  ext s
  rw [mem_compose_iff]
  exact ⟨fun ⟨_, hs⟩ => hs, fun hs => ⟨h U hs, hs⟩⟩

end General

/-! ### Restriction to an open commutes with composition -/

section Restrict

variable {X : Scheme.{u}} {F : X.Modules}

/-- **Restriction along an open immersion commutes with composition of submodules.** The
module of `restrictTo f K` is, by definition, the restriction of the module of `K`, so a
submodule of the latter is a submodule of the former. -/
theorem restrictTo_compose {Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f] (K : F.Submodule)
    (N : (K.toSheafOfModules : X.Modules).Submodule) :
    restrictTo f (compose K N) = compose (restrictTo f K) (restrictTo f N) := by
  refine SheafOfModules.Submodule.ext (PresheafOfModules.Submodule.ext fun U => ?_)
  ext s
  rfl

/-- Restriction along an open immersion commutes with binary infima of submodules. -/
theorem restrictTo_inf {Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f] (N N' : F.Submodule) :
    restrictTo f (N ⊓ N') = restrictTo f N ⊓ restrictTo f N' := by
  refine SheafOfModules.Submodule.ext (PresheafOfModules.Submodule.ext fun U => ?_)
  ext s
  rfl

/-- Restriction along an open immersion commutes with composition of submodules, with the
restricted inner submodule replaced by an equal one. Stated for a general open immersion so that
the comparison of the two spellings of the module of `K|_Y` is made by unification once, here,
and not at every use. -/
theorem restrictTo_compose_of_restrictTo_eq {Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (K : F.Submodule) {N P : (K.toSheafOfModules : X.Modules).Submodule}
    (h : restrictTo f N = restrictTo f P) :
    restrictTo f (compose K N) = compose (restrictTo f K) (restrictTo f P) := by
  rw [restrictTo_compose, h]

/-- **A submodule of `F|_Y` below `K|_Y`, read inside `K|_Y` as a restriction.** For
`D ≤ K|_Y`, the submodule `P` of the module of `K` given by `coRestrict D ⊓ K` restricts to a
submodule of `K|_Y` which composes back to `D`; its module is that of `D`, so it inherits
quasi-coherence and finite type. This is what lets [Stacks, Tag 01PF] be applied to `K` with
`D` as the prescription: the restriction of `P` has the spelling `(K|_Y).Submodule` it asks
for. -/
theorem exists_restrictTo_compose_eq {Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (K : F.Submodule) (D : (F.restrict f).Submodule) (hDK : D ≤ restrictTo f K)
    (hDqc : (D.toSheafOfModules : Y.Modules).IsQuasicoherent)
    (hDft : (D.toSheafOfModules : Y.Modules).IsFiniteType) :
    ∃ P : (K.toSheafOfModules : X.Modules).Submodule,
      ((restrictTo f P).toSheafOfModules : Y.Modules).IsQuasicoherent ∧
      ((restrictTo f P).toSheafOfModules : Y.Modules).IsFiniteType ∧
      compose (restrictTo f K) (restrictTo f P) = D := by
  refine ⟨asSubmoduleOf K (coRestrict f D ⊓ K) inf_le_right, ?_⟩
  have hGD : compose (restrictTo f K) (restrictTo f (asSubmoduleOf K (coRestrict f D ⊓ K)
      inf_le_right)) = D := by
    rw [← restrictTo_compose]
    calc restrictTo f (compose K (asSubmoduleOf K (coRestrict f D ⊓ K) inf_le_right))
        = restrictTo f (coRestrict f D ⊓ K) :=
          congrArg (restrictTo f) (compose_asSubmoduleOf _ _ _)
      _ = restrictTo f (coRestrict f D) ⊓ restrictTo f K := restrictTo_inf f _ _
      _ = D ⊓ restrictTo f K := by rw [restrictTo_coRestrict]
      _ = D := inf_eq_left.mpr hDK
  refine ⟨?_, ?_, hGD⟩
  · have h := hDqc
    rw [← hGD] at h
    exact Stacks.AlgebraicGeometry.SubmoduleRelativeLocality.isQuasicoherent_of_iso
      (composeIso _ _) h
  · have h := hDft
    rw [← hGD] at h
    exact AlgebraicGeometry.Modules.isFiniteType_of_iso (composeIso _ _) h

/-! ### The extension -/

/-- **Extension of a finite type quasi-coherent submodule from a quasi-compact open, below a
given quasi-coherent submodule.** On a quasi-compact quasi-separated scheme `Y`, let `K` be a
quasi-coherent submodule of an `𝒪_Y`-module `F`, `U` a quasi-compact open and `D` a
quasi-coherent submodule of finite type of `F|_U` with `D ≤ K|_U`. Then some quasi-coherent
submodule `N ≤ K` of finite type restricts to exactly `D` on `U`.

[Stacks, Tag 01PF] applied to the quasi-coherent module `K`. -/
@[ega "I 9.4.3" "special case", ega "I 9.4.7" "more general"]
theorem exists_isFiniteType_le_restrictTo_eq [CompactSpace X] [QuasiSeparatedSpace X]
    (K : F.Submodule) (hK : (K.toSheafOfModules : X.Modules).IsQuasicoherent)
    {U : X.Opens} (hU : IsCompact (U : Set X)) (D : (F.restrict U.ι).Submodule)
    (hDqc : (D.toSheafOfModules : U.toScheme.Modules).IsQuasicoherent)
    (hDft : (D.toSheafOfModules : U.toScheme.Modules).IsFiniteType)
    (hDK : D ≤ restrictTo U.ι K) :
    ∃ N : F.Submodule, (N.toSheafOfModules : X.Modules).IsQuasicoherent ∧
      (N.toSheafOfModules : X.Modules).IsFiniteType ∧ N ≤ K ∧ restrictTo U.ι N = D := by
  have : (K.toSheafOfModules : X.Modules).IsQuasicoherent := hK
  obtain ⟨P, hPqc, hPft, hPD⟩ := exists_restrictTo_compose_eq U.ι K D hDK hDqc hDft
  obtain ⟨N', hN'qc, hN'ft, hN'⟩ :=
    Stacks.AlgebraicGeometry.Tag01PFAffineExtend.exists_isFiniteType_submodule_restrictTo_eq_of_qcqs
      hU (restrictTo U.ι P) hPqc hPft
  refine ⟨compose K N',
    Stacks.AlgebraicGeometry.SubmoduleRelativeLocality.isQuasicoherent_of_iso
      (composeIso K N').symm hN'qc,
    AlgebraicGeometry.Modules.isFiniteType_of_iso (composeIso K N').symm hN'ft,
    compose_le K N', ?_⟩
  exact (restrictTo_compose_of_restrictTo_eq U.ι K hN').trans hPD

end Restrict

end Stacks.FiniteTypeSubmodule

end
