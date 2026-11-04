module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LevelLimitNaturality
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.HigherDerivedLimitVanishing

/-!
# The higher direct images of the completion of the little affine crystalline topos

Work in an affine crystalline situation `(A, I, γ) → C` ([Stacks, Tag 07MD]), and let
`g : Sh(𝒞) ⟶ Sh(𝒞^∧)` be the morphism of topoi of [Stacks, Tag 07JL] from the little affine
crystalline category to its completion. For an abelian sheaf `𝓖` on `𝒞 = (Cris(C/A))ᵒᵖ` and a
completed thickening `B` with finite levels `B_e = B/(p)^{N + e}`, where `N` is the cutoff
`Crystalline.uniformLevel s` and the levels are those of `Crystalline.uniformLevelSystem B`,

`R ᵖ g_* 𝓖 (B) ≅ R ᵖ lim_e 𝓖(B_e)` for every `p`.

In particular `R ¹ g_* 𝓖 (B) ≅ R ¹ lim_e 𝓖(B_e)`, and `R ᵖ g_* 𝓖 = 0` for `p ≥ 2`.

## Main results

* `Crystalline.rightDerivedPushforwardSectionsIsoRightDerivedLimit`:
  `R ᵖ g_* 𝓖(B) ≅ R ᵖ lim_e 𝓖(B_e)` in every degree `p`, for the direct image
  `Crystalline.abelianSheafPushforward` of `g`.
* `Crystalline.rightDerivedOnePushforwardSectionsIsoRightDerivedOneLimit`:
  `R ¹ g_* 𝓖(B) ≅ R ¹ lim_e 𝓖(B_e)`.
* `Crystalline.isZero_rightDerived_abelianSheafPushforward_of_two_le`: `R ᵖ g_* 𝓖 = 0` for every
  `p ≥ 2`.

## References

* [Stacks Project, Tag 07JL](https://stacks.math.columbia.edu/tag/07JL)
* [Stacks Project, Tag 07KW](https://stacks.math.columbia.edu/tag/07KW)
* [Stacks Project, Tag 07MD](https://stacks.math.columbia.edu/tag/07MD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Crystalline

universe u v w

variable {s : AffineCrystallineSituation.{u, v}}

/-- For an abelian sheaf `𝓖` on `𝒞 = (Cris(C/A))ᵒᵖ`, a completed thickening `B` and every degree
`p`, the sections over `B` of the `p`-th higher direct image of `𝓖` along the morphism of topoi
`g : Sh(𝒞) ⟶ Sh(𝒞^∧)` are the `p`-th derived inverse limit of the sections of `𝓖` on the finite
levels of `B`:

`R ᵖ g_* 𝓖 (B) ≅ R ᵖ lim_e 𝓖(B/(p)^{N + e})`. -/
@[stacks 07JL "the higher direct images as the derived limits over the finite levels"]
def rightDerivedPushforwardSectionsIsoRightDerivedLimit
    (𝓖 : Sheaf (littleChaoticTopology.{u, v, w} s) Ab.{max u v (w + 1)})
    (B : CompletedCrystallineThickening.{u, v, w} s) (p : ℕ) :
    ((completedAbelianSheafEquivalence.{u, v, w} s).functor.obj
        (((abelianSheafPushforward.{u, v, w} s).rightDerived p).obj 𝓖)).obj B ≅
      ((lim : Rlim.InvSystemAb.{max u v (w + 1)} ⥤ Ab.{max u v (w + 1)}).rightDerived p).obj
        (finiteLevelSections (uniformLevelSystem B)
          ((abelianSheafEquivalence.{u, v, w} s).functor.obj 𝓖)) :=
  ((Functor.rightDerivedCompIso (abelianSheafPushforward.{u, v, w} s)
        (completedSheafSections s B) p).app 𝓖).symm ≪≫
    (Functor.rightDerivedIsoOfNatIso (pushforwardCompSectionsIso.{u, v, w} s B) p).app 𝓖 ≪≫
      rightDerivedLevelLimitIso (uniformLevelSystem B) 𝓖 p

/-- `R ¹ g_* 𝓖 (B) ≅ R ¹ lim_e 𝓖(B_e)`: for an abelian sheaf `𝓖` on `𝒞 = (Cris(C/A))ᵒᵖ` and a
completed thickening `B`, the sections over `B` of the first higher direct image of `𝓖` along the
morphism of topoi `g : Sh(𝒞) ⟶ Sh(𝒞^∧)` are the first derived inverse limit of the inverse system
`e ↦ 𝓖(B/(p)^{N + e})` of sections on the finite levels of `B`. -/
@[stacks 07JL "the first higher direct image as the first derived limit over the finite levels"]
def rightDerivedOnePushforwardSectionsIsoRightDerivedOneLimit
    (𝓖 : Sheaf (littleChaoticTopology.{u, v, w} s) Ab.{max u v (w + 1)})
    (B : CompletedCrystallineThickening.{u, v, w} s) :
    ((completedAbelianSheafEquivalence.{u, v, w} s).functor.obj
        (((abelianSheafPushforward.{u, v, w} s).rightDerived 1).obj 𝓖)).obj B ≅
      ((lim : Rlim.InvSystemAb.{max u v (w + 1)} ⥤ Ab.{max u v (w + 1)}).rightDerived 1).obj
        (finiteLevelSections (uniformLevelSystem B)
          ((abelianSheafEquivalence.{u, v, w} s).functor.obj 𝓖)) :=
  rightDerivedPushforwardSectionsIsoRightDerivedLimit 𝓖 B 1

/-- `R ᵖ g_* 𝓖 = 0` for every `p ≥ 2` and every abelian sheaf `𝓖` on `𝒞 = (Cris(C/A))ᵒᵖ`, where
`g_*` is the direct image `Crystalline.abelianSheafPushforward` of the morphism of topoi
`g : Sh(𝒞) ⟶ Sh(𝒞^∧)`. -/
@[stacks 07JL "the vanishing of the higher direct images in degrees at least two"]
theorem isZero_rightDerived_abelianSheafPushforward_of_two_le
    (𝓖 : Sheaf (littleChaoticTopology.{u, v, w} s) Ab.{max u v (w + 1)})
    (p : ℕ) (hp : 2 ≤ p) :
    IsZero (((abelianSheafPushforward.{u, v, w} s).rightDerived p).obj 𝓖) := by
  have hfun : IsZero ((completedAbelianSheafEquivalence.{u, v, w} s).functor.obj
      (((abelianSheafPushforward.{u, v, w} s).rightDerived p).obj 𝓖)) :=
    (Functor.isZero_iff _).2 fun B ↦ (Rlim.isZero_rightDerived_lim_of_two_le _ p hp).of_iso
      (rightDerivedPushforwardSectionsIsoRightDerivedLimit 𝓖 B p)
  exact ((completedAbelianSheafEquivalence.{u, v, w} s).inverse.map_isZero hfun).of_iso
    ((completedAbelianSheafEquivalence.{u, v, w} s).unitIso.app _)

end Crystalline

end
