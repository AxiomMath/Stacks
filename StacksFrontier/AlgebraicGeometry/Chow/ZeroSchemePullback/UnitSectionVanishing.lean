module

public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemeBaseChange.PullbackSections
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionCorrespondence

/-!
# The pullback of the section attached to a morphism out of the structure sheaf

A global section `s` of an `𝒪_X`-module `M` is the same thing as a morphism of `𝒪_X`-modules
`σ : 𝒪_X ⟶ M`, namely `s = σ(1)`. This file records that the pullback map on global sections of
[Stacks, Tag 0EUA] kills `s` exactly when the pullback functor kills `σ`:

`f^* s = 0  ↔  f^* σ = 0`.

That is the step by which a statement about the vanishing of a *section* — the hypothesis of the
factorization clause of [Stacks, Tag 02OR] — becomes a statement about the vanishing of a
*morphism of modules*, which is what the universal property of a relative spectrum speaks about.

## Main results

* `AlgebraicGeometry.unitHom_zero_app_top` and `AlgebraicGeometry.unitHom_eq_zero_iff_app_top`:
  a morphism out of the structure sheaf vanishes exactly when its value at the unit section over
  the whole space does.
* `AlgebraicGeometry.pullbackGlobalSections_app_top_one_eq_zero_iff`: **the pulled-back section
  vanishes exactly when the pulled-back morphism does.**

## Implementation notes

The structure sheaf as an `𝒪_X`-module is written `AlgebraicGeometry.Scheme.unitModule`, which
is `SheafOfModules.unit X.ringCatSheaf` typed as an object of `X.Modules`. The ascription
matters: the underlying site of a scheme has two spellings, and with the unit written at the
other one the additive structure of `𝒪_X ⟶ M` — in particular the zero morphism — is not found
by instance search.

That a morphism out of the structure sheaf is determined by its value at `1` is the injectivity
of `SheafOfModules.unitHomEquiv` together with
`AlgebraicGeometry.Scheme.Modules.sections_ext_of_eval_top`. The rest is the unit of the
pullback–pushforward adjunction: `AlgebraicGeometry.pullbackGlobalSections_eq_unit` identifies
the pullback map on global sections with that unit at the top open, and the naturality of the
unit turns composition with it into the hom-equivalence, which is injective and additive.

The three steps are `Iff.trans`es of `congrArg`s rather than rewrites. The two spellings of the
site make a goal mixing them ill-typed at the `implicit` transparency level that `rw` builds its
motive at, so `rw` refuses to fire; term elaboration runs at default transparency and accepts
the identification. This is the device
`StacksFrontier/AlgebraicGeometry/Chow/ZeroSchemePullback/Factorization.lean` already uses.

## References

* [Stacks Project, Tag 02OR](https://stacks.math.columbia.edu/tag/02OR)
* [Stacks Project, Lemma 35.13.2 (Tag 0EUA)](https://stacks.math.columbia.edu/tag/0EUA)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

/-- The zero morphism out of the structure sheaf kills the unit section. -/
theorem unitHom_zero_app_top {Z : Scheme.{u}} {M : Z.Modules} :
    Scheme.Modules.Hom.app (0 : Z.unitModule ⟶ M) ⊤ (1 : Γ(Z, ⊤)) = 0 := by
  rw [Scheme.Modules.Hom.zero_app]
  rfl

/-- **A morphism out of the structure sheaf vanishes exactly when its value at the unit section
over the whole space does.** -/
theorem unitHom_eq_zero_iff_app_top {Z : Scheme.{u}} {M : Z.Modules} (a : Z.unitModule ⟶ M) :
    a = 0 ↔ Scheme.Modules.Hom.app a ⊤ (1 : Γ(Z, ⊤)) = 0 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact (congrArg (fun b : Z.unitModule ⟶ M =>
      Scheme.Modules.Hom.app b ⊤ (1 : Γ(Z, ⊤))) h).trans (unitHom_zero_app_top (M := M))
  · exact (SheafOfModules.unitHomEquiv M).injective
      (Scheme.Modules.sections_ext_of_eval_top (h.trans (unitHom_zero_app_top (M := M)).symm))

/-- **The pullback of the global section attached to a morphism out of the structure sheaf
vanishes exactly when that morphism pulls back to zero.** -/
theorem pullbackGlobalSections_app_top_one_eq_zero_iff {Z Y : Scheme.{u}} (k : Y ⟶ Z)
    (M : Z.Modules) (σ : Z.unitModule ⟶ M) :
    pullbackGlobalSections k M (Scheme.Modules.Hom.app σ ⊤ (1 : Γ(Z, ⊤))) = 0 ↔
      (Scheme.Modules.pullback k).map σ = 0 := by
  have hunit : pullbackGlobalSections k M (Scheme.Modules.Hom.app σ ⊤ (1 : Γ(Z, ⊤))) =
      Scheme.Modules.Hom.app
        (σ ≫ (Scheme.Modules.pullbackPushforwardAdjunction k).unit.app M) ⊤
        (1 : Γ(Z, ⊤)) := by
    refine Eq.trans (congrArg (fun φ : Γ(M, ⊤) ⟶ Γ((Scheme.Modules.pullback k).obj M, ⊤) =>
      φ (Scheme.Modules.Hom.app σ ⊤ (1 : Γ(Z, ⊤)))) (pullbackGlobalSections_eq_unit k M)) ?_
    rfl
  have hnat : σ ≫ (Scheme.Modules.pullbackPushforwardAdjunction k).unit.app M =
      (Scheme.Modules.pullbackPushforwardAdjunction k).homEquiv Z.unitModule
        ((Scheme.Modules.pullback k).obj M)
        ((Scheme.Modules.pullback k).map σ) := by
    simp [Adjunction.homEquiv_unit]
  refine Iff.trans (iff_of_eq (congrArg (fun z => z = 0) hunit)) ?_
  refine Iff.trans (unitHom_eq_zero_iff_app_top _).symm ?_
  refine Iff.trans (iff_of_eq (congrArg (fun z => z = 0) hnat)) ?_
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact ((Scheme.Modules.pullbackPushforwardAdjunction k).homEquiv _ _).injective
      (h.trans ((Scheme.Modules.pullbackPushforwardAdjunction k).homAddEquiv_zero _ _).symm)
  · exact (congrArg ((Scheme.Modules.pullbackPushforwardAdjunction k).homEquiv _ _) h).trans
      ((Scheme.Modules.pullbackPushforwardAdjunction k).homAddEquiv_zero _ _)

end AlgebraicGeometry

end
