module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.RingTheory.HopkinsLevitzki
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.EssentialFiniteness.ArtinianTarget

/-!
# Finite type morphisms from spectra of Artinian local rings

For a morphism from the spectrum of an Artinian local ring, being of finite type can be
checked after restricting the morphism to the spectrum of the residue field.

## Main results

* `AlgebraicGeometry.finiteType_iff_residueField_comp_finiteType` characterizes finite type for
  a morphism from the spectrum of an Artinian local ring in terms of its residue-field point.

## Implementation notes

A finite type morphism is expressed by the conjunction of Mathlib's
`AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.QuasiCompact` predicates.
The residue field and residue map are the canonical `IsLocalRing.ResidueField A` and
`IsLocalRing.residue A`.

## References

* [Stacks Project, Tag 02HV](https://stacks.math.columbia.edu/tag/02HV)
-/

@[expose] public section

namespace AlgebraicGeometry

open CategoryTheory

universe u

/-- A morphism from the spectrum of an Artinian local ring is of finite type if and only if
its composite with the spectrum of the residue field is of finite type. -/
@[stacks 02HV]
theorem finiteType_iff_residueField_comp_finiteType
    (S : Scheme.{u}) (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A]
    (f : Spec (CommRingCat.of A) ⟶ S) :
    (LocallyOfFiniteType f ∧ QuasiCompact f) ↔
      (LocallyOfFiniteType
          (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ f) ∧
        QuasiCompact
          (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ f)) := by
  let g : Spec (CommRingCat.of (IsLocalRing.ResidueField A)) ⟶
      Spec (CommRingCat.of A) := Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))
  change (LocallyOfFiniteType f ∧ QuasiCompact f) ↔
    (LocallyOfFiniteType (g ≫ f) ∧ QuasiCompact (g ≫ f))
  constructor
  · rintro ⟨hf, hfc⟩
    have hg : LocallyOfFiniteType g := HasRingHomProperty.Spec_iff.mpr
      (RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective).to_finiteType
    have hgc : QuasiCompact g := ⟨fun _ _ _ => (Set.toFinite _).isCompact⟩
    exact ⟨inferInstance, inferInstance⟩
  · rintro ⟨hgf, -⟩
    have : Ring.KrullDimLE 0 A := isArtinianRing_iff_krullDimLE_zero.mp inferInstance
    have : Subsingleton (Spec (CommRingCat.of A)) :=
      Ring.KrullDimLE.subsingleton_primeSpectrum A
    have hgf' : ∀ x : Spec (CommRingCat.of (IsLocalRing.ResidueField A)), _ :=
      (HasRingHomProperty.iff_exists_appLE (P := @LocallyOfFiniteType)
        (RingHom.finiteType_stableUnderComposition.stableUnderCompositionWithLocalizationAway
          RingHom.finiteType_holdsForLocalizationAway).left).mp hgf
    have hlf : LocallyOfFiniteType f := by
      rcases hgf' (IsLocalRing.closedPoint (IsLocalRing.ResidueField A)) with
        ⟨U, V, hxV, hVU, h⟩
      have hVtop : V = ⟨⊤, isAffineOpen_top _⟩ := by
        apply Subtype.ext
        apply le_antisymm le_top
        intro y hy
        have : y = IsLocalRing.closedPoint (IsLocalRing.ResidueField A) := Subsingleton.elim _ _
        simpa [this] using hxV
      subst V
      have hVUf : (⊤ : (Spec (CommRingCat.of A)).Opens) ≤ f ⁻¹ᵁ U := by
        intro y _
        have hy : y = g (IsLocalRing.closedPoint (IsLocalRing.ResidueField A)) :=
          Subsingleton.elim _ _
        change f y ∈ U.1
        rw [hy]
        exact hVU hxV
      set W : (Spec (CommRingCat.of A)).Opens := f ⁻¹ᵁ U
      have hpre : W = ⊤ := le_antisymm le_top hVUf
      have hVUf' : (⊤ : (Spec (CommRingCat.of A)).Opens) ≤ W := hVUf
      have hVUκ' : (⊤ : (Spec (CommRingCat.of (IsLocalRing.ResidueField A))).Opens) ≤
          (g ≫ f) ⁻¹ᵁ U := hVU
      have hVUcomp : (⊤ : (Spec (CommRingCat.of (IsLocalRing.ResidueField A))).Opens) ≤
          g ⁻¹ᵁ W := by simp [hpre]
      have hpreG : g ⁻¹ᵁ W = ⊤ := by
        simpa using congrArg (fun O : (Spec (CommRingCat.of A)).Opens => g ⁻¹ᵁ O) hpre
      have hIA : homOfLE hVUf' = eqToHom hpre.symm := Subsingleton.elim _ _
      have hIK : homOfLE hVUcomp = eqToHom hpreG.symm := Subsingleton.elim _ _
      have hIG : (TopologicalSpace.Opens.map g.base).map (eqToHom hpre.symm) =
          eqToHom hpreG.symm := Subsingleton.elim _ _
      let Vtop : (Spec (CommRingCat.of A)).affineOpens := ⟨⊤, isAffineOpen_top _⟩
      have hcomp : (f.appLE U Vtop hVUf).hom.FiniteType := by
        dsimp [Vtop]
        let eA := (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv
        let eκ := (Scheme.ΓSpecIso
          (CommRingCat.of (IsLocalRing.ResidueField A))).commRingCatIsoToRingEquiv
        let φA := eA.toRingHom.comp (f.appLE U ⊤ hVUf').hom
        have hκ : (eκ.toRingHom.comp ((g ≫ f).appLE U ⊤ hVUκ').hom).FiniteType :=
          (RingHom.Finite.of_surjective _ eκ.surjective).to_finiteType.comp
            (by simpa using h)
        have hcompMap : (g ≫ f).appLE U ⊤ hVUκ' = f.appLE U ⊤ hVUf' ≫ g.appTop := by
          rw [← Scheme.Hom.appLE_comp_appLE g f U W ⊤ le_rfl hVUcomp, Scheme.Hom.appLE_eq_app]
          simp only [Scheme.Hom.appLE, Scheme.Hom.appTop, hIA, hIK]
          have hn := g.naturality (eqToHom hpre.symm).op
          simp only [Quiver.Hom.unop_op] at hn
          rw [hIG] at hn
          exact (Category.assoc _ _ _).trans
            ((congrArg (fun k => f.app U ≫ k) hn.symm).trans
              (Category.assoc _ _ _).symm)
        have hnat : eκ.toRingHom.comp ((g ≫ f).appLE U ⊤ hVUκ').hom =
            (IsLocalRing.residue A).comp φA := by
          ext x
          rw [hcompMap]
          change eκ (g.appTop (f.appLE U ⊤ hVUf' x)) =
            IsLocalRing.residue A (eA (f.appLE U ⊤ hVUf' x))
          exact congrArg
            (fun k : Γ(Spec (CommRingCat.of A), ⊤) ⟶
                CommRingCat.of (IsLocalRing.ResidueField A) =>
              k (f.appLE U ⊤ hVUf' x))
            (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (IsLocalRing.residue A)))
        exact (RingHom.finiteType_respectsIso.cancel_right_isIso
          (f.appLE U ⊤ hVUf') (Scheme.ΓSpecIso (CommRingCat.of A)).hom).mp
            ((finiteType_iff_residue_finiteType φA).mpr (by rwa [← hnat]))
      rw [HasRingHomProperty.iff_exists_appLE (P := @LocallyOfFiniteType)
        (RingHom.finiteType_stableUnderComposition.stableUnderCompositionWithLocalizationAway
          RingHom.finiteType_holdsForLocalizationAway).left]
      intro x
      exact ⟨U, Vtop, (by change x ∈ (⊤ : (Spec (CommRingCat.of A)).Opens); trivial),
        hVUf, hcomp⟩
    exact ⟨hlf, ⟨fun _ _ _ => (Set.toFinite _).isCompact⟩⟩

end AlgebraicGeometry
