module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
public import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Frobenius.RelativeUniversalHomeomorphism
public import StacksCore.Tactic.StacksAttribute

/-!
# Weakly étale morphisms that are isomorphisms

A weakly étale morphism of schemes that is a universal homeomorphism is an isomorphism.
Consequently, for a weakly étale morphism `U ⟶ X` of schemes with `X` in prime characteristic,
the relative Frobenius of `U` over `X` is an isomorphism.

## Main results

* `AlgebraicGeometry.isIso_of_weaklyEtale_of_universalHomeomorphism` gives an isomorphism from
  these two properties.
* `AlgebraicGeometry.isIso_relativeFrobenius_of_weaklyEtale` states that the relative Frobenius
  of a weakly étale `X`-scheme is an isomorphism in `Over X`.

## References

* [Stacks Project, Tag 0F6V](https://stacks.math.columbia.edu/tag/0F6V)
* [Stacks Project, Tag 0F6W](https://stacks.math.columbia.edu/tag/0F6W)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Frobenius

universe u

namespace AlgebraicGeometry

/-- A weakly étale universal homeomorphism of schemes is an isomorphism. -/
@[stacks 0F6V]
instance isIso_of_weaklyEtale_of_universalHomeomorphism
    {X Y : Scheme.{u}} (f : X ⟶ Y) [WeaklyEtale f]
    [UniversalHomeomorphism f] : IsIso f := by
  have hhomeo : IsHomeomorph f.base :=
    UniversalHomeomorphism.universally_isHomeomorph _ _ _ .of_id_snd
  have : QuasiCompact f := ⟨fun U hU hUc => hhomeo.homeomorph.isCompact_preimage.mpr hUc⟩
  have : Surjective f := ⟨hhomeo.surjective⟩
  have hfst : IsHomeomorph (pullback.fst f f).base :=
    UniversalHomeomorphism.universally_isHomeomorph _ _ _
      (IsPullback.of_hasPullback f f)
  have hdiag_homeo : IsHomeomorph ⇑(pullback.diagonal f) := by
    convert hfst.homeomorph.symm.isHomeomorph using 1
    funext x; apply hfst.injective
    rw [← Scheme.Hom.comp_apply, pullback.diagonal_fst]
    exact (hfst.homeomorph.apply_symm_apply x).symm
  have : QuasiCompact (pullback.diagonal f) :=
    ⟨fun U hU hUc => hdiag_homeo.homeomorph.isCompact_preimage.mpr hUc⟩
  have : Surjective (pullback.diagonal f) := ⟨hdiag_homeo.surjective⟩
  have : Mono f :=
    (pullback.isIso_diagonal_iff f).mp (Flat.isIso_of_surjective_of_mono (pullback.diagonal f))
  exact Flat.isIso_of_surjective_of_mono f

/-- The relative Frobenius of a weakly étale scheme is an isomorphism. -/
@[stacks 0F6W,
  sga "4½ Fonctions_L 3.4" "more general",
  sga "4½ Rapport 1.2" "special case",
  sga "5 XV 1.Proposition2" "more general"]
instance isIso_relativeFrobenius_of_weaklyEtale (X : Scheme.{u}) (p : ℕ)
    [Fact p.Prime] (hX : IsInCharacteristic X p) (U : Over X) [WeaklyEtale U.hom] :
    IsIso (relativeFrobenius X p hX U) := by
  let f := relativeFrobenius X p hX U
  have : WeaklyEtale ((frobeniusTwist X p hX).obj U).hom := by
    change WeaklyEtale (pullback.snd U.hom (absoluteFrobenius X p hX)); infer_instance
  have : WeaklyEtale (f.left ≫ ((frobeniusTwist X p hX).obj U).hom) := by
    rw [frobeniusTwist_obj_hom, relativeFrobenius_snd]; infer_instance
  have : WeaklyEtale f.left := WeaklyEtale.of_comp f.left ((frobeniusTwist X p hX).obj U).hom
  have : IsIso ((Over.forget X).map f) := by change IsIso f.left; infer_instance
  exact isIso_of_reflects_iso _ (Over.forget X)

end AlgebraicGeometry
