module

public import StacksFrontier.AlgebraicGeometry.RelativeSegre.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.BaseChange

/-!
# Fibre products of projective bundles are projective

Let `H` and `G` be quasi-coherent modules of finite type on a scheme `X`. The relative Segre
morphism closed-immerses `𝐏(H) ×_X 𝐏(G)` into `𝐏(H ⊗ G)` over `X`, and `H ⊗ G` is quasi-coherent
of finite type, so `𝐏(H) ×_X 𝐏(G) ⟶ X` is projective in the sense of Stacks 01W8. No
quasi-compactness of `X` is needed.

Consequently, if `g : Y ⟶ X` is projective and `G` is a quasi-coherent `𝒪_X`-module of finite type,
the projective bundle `𝐏(G') ⟶ Y` of a module `G' ≅ g^*G` composed with `g` is projective: it is
the base change `Y ×_X 𝐏(G)`, which closed-immerses into `𝐏(H) ×_X 𝐏(G)` for any closed immersion
`Y ⟶ 𝐏(H)` over `X`.

## Main results

* `Stacks.RelativeSegre.isProjective_pullback_fst_toBase`: `𝐏(H) ×_X 𝐏(G) ⟶ X` is projective.
* `Stacks.RelativeSegre.isProjective_bundle_comp`: `𝐏(g^*G) ⟶ Y ⟶ X` is projective when
  `Y ⟶ X` is.

## References

* [Stacks Project, Tag 01WD](https://stacks.math.columbia.edu/tag/01WD)
* [Stacks Project, Tag 01W8](https://stacks.math.columbia.edu/tag/01W8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.RelativeSegre

variable {X : Scheme.{u}}

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso Stacks.SheafInternalHom.isLocalization_sheafify
  Stacks.SheafInternalHom.monoidalCategory Stacks.SheafInternalHom.sheafifyMonoidal
  Stacks.SheafInternalHom.braidedCategory Stacks.SheafInternalHom.schemeMonoidalCategory

/-- **The fibre product of two projective bundles of quasi-coherent modules of finite type is
projective over the base** (Stacks 01W8), with no hypothesis on the base: the relative Segre
morphism is a closed immersion over `X` into the projective bundle of `H ⊗ G`. -/
theorem isProjective_pullback_fst_toBase (H G : X.Modules) [H.IsQuasicoherent]
    [G.IsQuasicoherent] (hH : H.IsFiniteType) (hG : G.IsFiniteType) :
    IsProjective (pullback.fst (bun H).toBase (bun G).toBase ≫ (bun H).toBase) := by
  have : (tens H G).IsFiniteType :=
    Stacks.AmpleCharacterization.isFiniteType_tensor H G hH hG
  have := isClosedImmersion_segre H G
  exact isProjective_of_isClosedImmersion (tens H G) (segre H G) (segre_toBase H G)

/-- **A projective bundle over a projective `X`-scheme, pulled back from `X`, is projective over
`X`.** If `g : Y ⟶ X` is projective, `G` is a quasi-coherent `𝒪_X`-module of finite type and
`G' ≅ g^*G`, then `𝐏(G') ⟶ Y ⟶ X` is projective (Stacks 01W8), with no hypothesis on `X`. -/
theorem isProjective_bundle_comp {Y : Scheme.{u}} {g : Y ⟶ X} (hg : IsProjective g)
    (G : X.Modules) [G.IsQuasicoherent] (hG : G.IsFiniteType) (G' : Y.Modules)
    [G'.IsQuasicoherent] (e : G' ≅ (Scheme.Modules.pullback g).obj G) :
    IsProjective ((bun G').toBase ≫ g) := by
  obtain ⟨H, hHq, hHf, hqc, i, hi, hig⟩ := hg
  obtain ⟨b, hb⟩ := projectiveBundleBaseChangeComparison g G
    (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent G) G'
    (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent G') e
  -- the base change of the closed immersion `i : Y ⟶ 𝐏(H)` along `𝐏(H) ×_X 𝐏(G) ⟶ 𝐏(H)`
  have hcomm : i ≫ (bun H).toBase = g := hig
  have hw : (pullback.fst g (bun G).toBase ≫ i) ≫ (bun H).toBase =
      pullback.snd g (bun G).toBase ≫ (bun G).toBase := by
    rw [Category.assoc, hcomm, pullback.condition]
  set j : pullback g (bun G).toBase ⟶ pullback (bun H).toBase (bun G).toBase :=
    pullback.lift _ _ hw with hj_def
  have hs : IsPullback (j ≫ pullback.snd (bun H).toBase (bun G).toBase)
      (pullback.fst g (bun G).toBase) (bun G).toBase (i ≫ (bun H).toBase) := by
    have e1 : j ≫ pullback.snd (bun H).toBase (bun G).toBase = pullback.snd g (bun G).toBase := by
      rw [hj_def, pullback.lift_snd]
    rw [e1, hcomm]
    exact (IsPullback.of_hasPullback g (bun G).toBase).flip
  have hsq : IsPullback j (pullback.fst g (bun G).toBase)
      (pullback.fst (bun H).toBase (bun G).toBase) i :=
    IsPullback.of_right hs (by rw [hj_def, pullback.lift_fst])
      (IsPullback.of_hasPullback (bun H).toBase (bun G).toBase).flip
  have hj : IsClosedImmersion j :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) hsq.flip hi
  have hproj := isProjective_pullback_fst_toBase H G hHf hG
  obtain ⟨N, hNq, hNf, hNqc, k, hk, hkN⟩ := hproj
  have := hk
  refine ⟨N, hNq, hNf, hNqc, b.hom ≫ j ≫ k, inferInstance, ?_⟩
  rw [Category.assoc, Category.assoc, hkN, ← Category.assoc j, hj_def, pullback.lift_fst,
    Category.assoc, hcomm, ← Category.assoc, hb]

end Stacks.RelativeSegre

end
