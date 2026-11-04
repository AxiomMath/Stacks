module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import StacksFrontier.AlgebraicGeometry.AmpleBridge.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleTransport.Basic
public import StacksFrontier.AlgebraicGeometry.FieldExtensionDescent.Unconditional
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AmpleSmoothIrreducible
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.QuasiProjectiveIdentityComponent
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.SmoothCharacteristicZero
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.SmoothPerfectField
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverFieldProperties.Reduction
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.NoetherianSource
public import StacksFrontier.AlgebraicGeometry.NormInvertible.Ample
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.Basic
public import StacksFrontier.AlgebraicGeometry.RelativelyAmple.AffineBase
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Quasi-projectivity of an algebraic group scheme over a field

An algebraic group scheme over a field is quasi-projective over that field exactly when its
underlying scheme carries an ample invertible sheaf, and the search for such a sheaf reduces to
the smooth group schemes over an algebraically closed field.

## Main results

* `AlgebraicGeometry.isQuasiProjective_groupScheme_iff_exists_isAmple`: quasi-projectivity of an
  algebraic group scheme over a field is the existence of an ample invertible sheaf on it.
* `AlgebraicGeometry.exists_isAmple_of_groupScheme_of_smooth_case`: over a perfect field an
  algebraic group scheme carries an ample invertible sheaf as soon as every smooth one does.
* `AlgebraicGeometry.exists_isAmple_of_smooth_of_isAlgClosed`: a smooth algebraic group scheme
  over an algebraically closed field carries an ample invertible sheaf.
* `AlgebraicGeometry.isQuasiProjective_of_groupScheme_over_field`: an algebraic group scheme over
  a field is quasi-projective over it.

## References

* [Stacks Project, Tag 0BF7](https://stacks.math.columbia.edu/tag/0BF7)
* [Stacks Project, Tag 01VT](https://stacks.math.columbia.edu/tag/01VT)
* [Stacks Project, Tag 01T6](https://stacks.math.columbia.edu/tag/01T6)
* [Stacks Project, Tag 047N](https://stacks.math.columbia.edu/tag/047N)
* [Stacks Project, Tag 047P](https://stacks.math.columbia.edu/tag/047P)
* [Stacks Project, Tag 047R](https://stacks.math.columbia.edu/tag/047R)
* [Stacks Project, Tag 0BD4](https://stacks.math.columbia.edu/tag/0BD4)
* [Stacks Project, Tag 0BDC](https://stacks.math.columbia.edu/tag/0BDC)
* [Stacks Project, Tag 0BCW](https://stacks.math.columbia.edu/tag/0BCW)
* [Stacks Project, Tag 0B7R](https://stacks.math.columbia.edu/tag/0B7R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

/-- A scheme locally of finite type and quasi-compact over a field is Noetherian. -/
theorem isNoetherian_of_locallyOfFiniteType_over_field {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] [QuasiCompact f] :
    IsNoetherian X :=
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  ⟨⟩

/-- On a scheme over a field of characteristic `p`, the natural number `p` vanishes in the global
sections. -/
theorem natCast_eq_zero_sectionsTop_of_charP {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (p : ℕ) [CharP k p] : (p : Γ(X, ⊤)) = 0 := by
  rw [← map_natCast ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop).hom p,
    CharP.cast_eq_zero, map_zero]

/-- An algebraic group scheme over a field is quasi-projective over that field exactly when its
underlying scheme carries an ample invertible sheaf. -/
theorem isQuasiProjective_groupScheme_iff_exists_isAmple
    (G : Grp (Over (Spec (CommRingCat.of k)))) [LocallyOfFiniteType G.X.hom]
    [QuasiCompact G.X.hom] :
    IsQuasiProjective G.X.hom ↔
      ∃ M : G.X.left.Modules, ∃ _ : AlgebraicGeometry.SheafOfModules.IsInvertible
          G.X.left.toRingedSpace.presheaf
          (structureSheafRing G.X.left.toRingedSpace).property M,
        Scheme.Modules.IsAmple G.X.left M := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨M, hM, hrel⟩ := h.exists_isRelativelyAmple
    have := hM
    exact ⟨M, hM, Scheme.Modules.isAmple_of_isRelativelyAmple G.X.hom M hrel⟩
  · obtain ⟨M, hM, hamp⟩ := h
    have := hM
    exact IsQuasiProjective.mk' ‹LocallyOfFiniteType G.X.hom› M
      (Scheme.Modules.isRelativelyAmple_of_isAmple G.X.hom M hamp)

/-- Over a perfect field an algebraic group scheme carries an ample invertible sheaf as soon as
every smooth algebraic group scheme over that field does. -/
theorem exists_isAmple_of_groupScheme_of_smooth_case [PerfectField k]
    (hSmooth : ∀ H : Grp (Over (Spec (CommRingCat.of k))), LocallyOfFiniteType H.X.hom →
      QuasiCompact H.X.hom → Smooth H.X.hom →
      ∃ M : H.X.left.Modules, ∃ _ : AlgebraicGeometry.SheafOfModules.IsInvertible
          H.X.left.toRingedSpace.presheaf
          (structureSheafRing H.X.left.toRingedSpace).property M,
        Scheme.Modules.IsAmple H.X.left M)
    (G : Grp (Over (Spec (CommRingCat.of k)))) [LocallyOfFiniteType G.X.hom]
    [QuasiCompact G.X.hom] :
    ∃ M : G.X.left.Modules, ∃ _ : AlgebraicGeometry.SheafOfModules.IsInvertible
        G.X.left.toRingedSpace.presheaf
        (structureSheafRing G.X.left.toRingedSpace).property M,
      Scheme.Modules.IsAmple G.X.left M := by
  have : GrpObj (Over.mk G.X.hom) := inferInstanceAs (GrpObj G.X)
  rcases CharP.char_is_prime_or_zero k (ringChar k) with hp | hp
  · obtain ⟨H, e, -⟩ := exists_closedSubgroupScheme_reduction G
    set I := Scheme.IdealSheafData.vanishingIdeal (⊤ : Closeds G.X.left)
    have hw : e.hom.left ≫ H.carrier.X.hom = I.subschemeι ≫ G.X.hom := e.hom.w
    have hiso : IsIso e.hom.left :=
      inferInstanceAs (IsIso ((Over.forget _).mapIso e).hom)
    have hhom : inv e.hom.left ≫ I.subschemeι ≫ G.X.hom = H.carrier.X.hom :=
      (IsIso.inv_comp_eq _).mpr hw.symm
    have hft : LocallyOfFiniteType (inv e.hom.left ≫ I.subschemeι ≫ G.X.hom) := inferInstance
    have hqc : QuasiCompact (inv e.hom.left ≫ I.subschemeι ≫ G.X.hom) := inferInstance
    rw [hhom] at hft hqc
    have hred : IsReduced (Over.mk (I.subschemeι ≫ G.X.hom)).left :=
      Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
    have : IsReduced H.carrier.X.left := isReduced_of_isOpenImmersion (inv e.hom.left)
    have : GrpObj (Over.mk H.carrier.X.hom) := inferInstanceAs (GrpObj H.carrier.X)
    obtain ⟨N, hN, hampN⟩ := hSmooth H.carrier hft hqc
      (smooth_of_isReduced_groupScheme_of_perfectField k H.carrier.X.left H.carrier.X.hom)
    obtain ⟨N', hN', hampN'⟩ :=
      Scheme.Modules.exists_isAmple_of_isIso e.hom.left ⟨N, hN, hampN⟩
    have : IsNoetherian G.X.left :=
      isNoetherian_of_locallyOfFiniteType_over_field G.X.hom
    have hNB : Stacks.Ample.IsInvertibleModule _ N' := hN'
    have := ringChar.charP k
    obtain ⟨M, hM, hampM⟩ := Stacks.Divisors.exists_isAmple_of_isAmple_reduction_char_p
      G.X.left (ringChar k) hp (natCast_eq_zero_sectionsTop_of_charP G.X.hom (ringChar k)) N'
      ((Stacks.AmpleBridge.isAmple_iff_isAmple _ N').mpr hampN')
    exact ⟨M, inferInstance, (Stacks.AmpleBridge.isAmple_iff_isAmple _ M).mp hampM⟩
  · have : CharP k 0 := hp ▸ ringChar.charP k
    have : CharZero k := CharP.charP_to_charZero k
    exact hSmooth G ‹_› ‹_› (smooth_of_groupScheme_of_charZero k G.X.left G.X.hom)

/-- A smooth algebraic group scheme over an algebraically closed field carries an ample invertible
sheaf. -/
theorem exists_isAmple_of_smooth_of_isAlgClosed (K : Type u) [Field K] [IsAlgClosed K]
    (H : Grp (Over (Spec (CommRingCat.of K)))) [LocallyOfFiniteType H.X.hom]
    [QuasiCompact H.X.hom] [Smooth H.X.hom] :
    ∃ M : H.X.left.Modules, ∃ _ : AlgebraicGeometry.SheafOfModules.IsInvertible
        H.X.left.toRingedSpace.presheaf
        (structureSheafRing H.X.left.toRingedSpace).property M,
      Scheme.Modules.IsAmple H.X.left M := by
  have : IsNormal H.X.left := isNormal_of_smooth_over_field H.X.hom
  let H₀ := (identityComponent K H).carrier
  have : LocallyOfFiniteType H₀.X.hom := locallyOfFiniteType_identityComponent H
  have : QuasiCompact H₀.X.hom := quasiCompact_identityComponent H
  have : Smooth H₀.X.hom := smooth_identityComponent H
  have : GeometricallyIrreducible H₀.X.hom := identityComponent_geometricallyIrreducible K H
  have : IrreducibleSpace H₀.X.left :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton H₀.X.hom
  obtain ⟨M, hM, hamp⟩ := exists_isAmple_of_smooth_of_irreducibleSpace K H₀
  have h₀ : IsQuasiProjective H₀.X.hom :=
    (isQuasiProjective_groupScheme_iff_exists_isAmple H₀).mpr
      ⟨M, hM, (Stacks.AmpleBridge.isAmple_iff_isAmple _ M).mp hamp⟩
  exact (isQuasiProjective_groupScheme_iff_exists_isAmple H).mp
    (isQuasiProjective_of_isQuasiProjective_identityComponent H h₀)

/-- Let `k` be a field and `G` an algebraic group scheme over `k`. Then `G` is quasi-projective
over `k`. -/
@[stacks 0BF7, sga "3 VIB 5.5" "special case"]
theorem isQuasiProjective_of_groupScheme_over_field
    (G : Grp (Over (Spec (CommRingCat.of k)))) [LocallyOfFiniteType G.X.hom]
    [QuasiCompact G.X.hom] :
    IsQuasiProjective G.X.hom := by
  have : GrpObj (Over.mk G.X.hom) := inferInstanceAs (GrpObj G.X)
  set K := AlgebraicClosure k
  set g : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k K))
  have hgrp : GrpObj (Over.mk (pullback.snd G.X.hom g)) := Over.grpObjMkPullbackSnd
  set GK : Grp (Over (Spec (CommRingCat.of K))) :=
    Grp.mk (Over.mk (pullback.snd G.X.hom g))
  have hft : LocallyOfFiniteType GK.X.hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd G.X.hom g))
  have hqc : QuasiCompact GK.X.hom :=
    inferInstanceAs (QuasiCompact (pullback.snd G.X.hom g))
  have hampK := exists_isAmple_of_groupScheme_of_smooth_case
    (fun H _ _ _ => exists_isAmple_of_smooth_of_isAlgClosed K H) GK
  rw [isQuasiProjective_groupScheme_iff_exists_isAmple G]
  exact exists_isAmple_of_fieldExtension k K G.X.hom
    ((Scheme.Modules.exists_isAmple_pullback_comm G.X.hom g).mp hampK)

end AlgebraicGeometry

end
