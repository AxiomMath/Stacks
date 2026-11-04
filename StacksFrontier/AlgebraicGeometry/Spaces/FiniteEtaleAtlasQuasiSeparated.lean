module

public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedAbsolute

/-!
# A finite étale atlas by a quasi-separated scheme

An algebraic space admitting a finite surjective étale morphism from a quasi-separated scheme
is quasi-separated.

## Main results

* `AlgebraicGeometry.BigFppfSite.contains_terminal`: a big fppf site contains the terminal
  scheme.
* `AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_finite_etale_atlas`: an algebraic
  space admitting a finite surjective étale morphism from a quasi-separated scheme is
  quasi-separated.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A big fppf site contains the terminal scheme. -/
theorem BigFppfSite.contains_terminal (B : BigFppfSite.{u}) : B.Contains (⊤_ Scheme.{u}) := by
  have htop : (⊤_ Scheme.{u}).size = Cardinal.aleph0 := by
    let e : (⊤_ Scheme.{u}) ≅ Spec (.of (ULift.{u} ℤ)) :=
      terminalIsTerminal.uniqueUpToIso specULiftZIsTerminal
    calc
      (⊤_ Scheme.{u}).size = (Spec (.of (ULift.{u} ℤ))).size := Scheme.size_congr e
      _ = max Cardinal.aleph0 (Cardinal.mk (ULift.{u} ℤ)) := Scheme.size_Spec _
      _ = Cardinal.aleph0 := by simp
  show (⊤_ Scheme.{u}).size < B.cutoff
  rw [htop]
  exact B.aleph0_lt_cutoff

namespace Space

/-- An algebraic space admitting a finite surjective étale morphism from an object of the site
whose underlying scheme is quasi-separated is quasi-separated. -/
theorem isAbsolutelyQuasiSeparated_of_finite_etale_atlas (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u}))
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (U : BigFppfOver B S hS) (q : yoneda.obj U ⟶ F)
    (hUqs : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj U))
    (hqfinite : IsFinite B S hS q)
    (hqetale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) q)
    (hqsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) q) :
    IsAbsolutelyQuasiSeparated B S hS hZ F := by
  have _ : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks (BigFppfOver B S hS)
  have hrep := (isFinite_iff_representable B S hS q
    (_root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U) hF).mp hqfinite
  let Pfin := MorphismProperty.inverseImage
    (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  have hfinite : Pfin.presheaf (pullback.fst q q) := by
    have _ : Pfin.IsStableUnderBaseChange :=
      ⟨fun sq hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := @_root_.AlgebraicGeometry.IsFinite.{u})
        (sq.map (BigFppfOver.toScheme B S hS)) hg⟩
    exact (MorphismProperty.relative_isStableUnderBaseChange Pfin).of_isPullback
      (IsPullback.of_hasPullback q q).flip hrep.2
  have hle : Pfin ≤ MorphismProperty.inverseImage
      (@QuasiCompact.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS) :=
    fun _ _ f (_ : _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map f)) ↦
      inferInstanceAs (QuasiCompact ((BigFppfOver.toScheme B S hS).map f))
  exact isQuasiSeparated_of_etaleAtlas_quasiCompact_projection B S hS hZ F hF
    ⟨U, q, hUqs, hqsurj, hqetale,
      Or.inl (MorphismProperty.relative_monotone hle (pullback.fst q q) hfinite)⟩

end Space

end AlgebraicGeometry

end
