module

public import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsBaseRing
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.AffineOpenSectionsCohomology

/-!
# The pure tensors generate: `γ⁺` on sections from its values on `1 ⊗ a`

`Stacks.AlgebraicGeometry.TopDegreeBaseChange.sourceSectionsIsoTensor` presents the module of
sections of the source of the canonical map `γ⁺` of [Stacks, Tag 0EX3] (c) over an affine open
`W` of `Y''` lying inside `h⁻¹(V)`, for `V` an affine open of `Y'`, as the base change

> `Γ(Y'', W) ⊗_{Γ(Y', V)} Γ(R^d f'_* F', V)`.

A `Γ(Y'', W)`-linear map out of such a base change is determined by its restriction to the pure
tensors `1 ⊗ a`, since `r ⊗ a = r • (1 ⊗ a)`. This file turns that observation into the step
conclusion (c) consumes: a bijective `Γ(Y'', W)`-linear map out of the base change which agrees
with `Γ(W, γ⁺)` on the pure tensors forces `Γ(W, γ⁺)` to be bijective, and by
`isIso_topDirectImageBaseChangeMap_of_bijective_app_plus_affineOpens` that is conclusion (c).

## Main results

* `…TopDegreeBaseChange.bijective_app_topDirectImageBaseChangeMapPlus_of_one_tmul`: **`Γ(W, γ⁺)`
  is bijective as soon as some bijective `Γ(Y'', W)`-linear map out of the base change
  `Γ(Y'', W) ⊗_{Γ(Y', V)} Γ(R^d f'_* F', V)` agrees with it on the pure tensors `1 ⊗ a`.** The
  bases `Y'` and `Y''` carry no hypothesis; only the two opens are affine.

## Implementation notes

*Where the pure tensors come from.* The identification of the sections of `h^* R^d f'_* F'` over
`W` with the base change is `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso`, which needs
`R^d f'_* F'` to be quasi-coherent — that is [Stacks, Tag 01XJ], in the form
`AlgebraicGeometry.ProperCoherentFiniteType.isQuasicoherent_rightDerivedPlus`. Its normalisation
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso_one_tmul` sends `1 ⊗ a` to
`AlgebraicGeometry.Scheme.Modules.pullbackSection`, which is the spelling in which the
hypothesis on the pure tensors is stated.

*Why one hypothesis on the pure tensors suffices.* The comparison and `Γ(W, γ⁺)` compose to a
`Γ(Y'', W)`-linear map out of the base change, so `ModuleCat.ExtendScalars.hom_ext_one_tmul`
identifies it with the given map from their agreement on `1 ⊗ a` alone. The comparison is an
isomorphism, hence bijective by `CategoryTheory.ConcreteCategory.bijective_of_isIso`, and
bijectivity of `Γ(W, γ⁺)` follows by cancelling it.

*The linearity of `Γ(W, γ⁺)`.* `AlgebraicGeometry.Scheme.Modules.sectionsLinearMap` packages the
map on sections of a morphism of modules as a linear map over the ring of the open; its
underlying function is the `val.app` at that open, which is how the bijectivity statement of
`isIso_topDirectImageBaseChangeMapPlus_of_bijective_app` is phrased.

*No `@[stacks 0EX3]` attribute is placed.* This is a reduction step for the invertibility of
`γ⁺`, not a conclusion of the tag.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped ChangeOfRings

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance 10000] HasDerivedCategory.standard

variable {X'' Y'' : Scheme.{u}}

/-- **`Γ(W, γ⁺)` is bijective as soon as a bijective linear map out of the base change agrees
with it on the pure tensors.** Let `W` be an affine open of `Y''` contained in `h⁻¹(V)` for an
affine open `V` of `Y'`. The sections of the source `h^* R^d f'_* F'` of the canonical map `γ⁺`
of [Stacks, Tag 0EX3] (c) over `W` are the base change along `Γ(Y', V) ⟶ Γ(Y'', W)` of the
sections of `R^d f'_* F'` over `V`, and a `Γ(Y'', W)`-linear map out of a base change is
determined by its values on the pure tensors `1 ⊗ a`. So a bijective `ψ` out of that base change
whose value at `1 ⊗ a` is the value of `Γ(W, γ⁺)` at the pullback of the section `a` is
`Γ(W, γ⁺)` composed with an isomorphism, and `Γ(W, γ⁺)` is bijective.

Neither `Y'` nor `Y''` carries a hypothesis: the affineness is asked of the two opens only. -/
theorem bijective_app_topDirectImageBaseChangeMapPlus_of_one_tmul
    (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})
    (F' : S.X'.Modules) [F'.IsQuasicoherent]
    (h' : X'' ⟶ S.X') (f'' : X'' ⟶ Y'') (h : Y'' ⟶ S.Y')
    (sq : h'.toLRSHom.toShHom ≫ S.f'.toLRSHom.toShHom
      = f''.toLRSHom.toShHom ≫ h.toLRSHom.toShHom)
    {V : S.Y'.Opens} (hV : IsAffineOpen V) {W : Y''.Opens} (hW : IsAffineOpen W)
    (hWV : W ≤ h ⁻¹ᵁ V)
    (ψ : (ModuleCat.extendScalars (h.appLE V W hWV).hom).obj
          (ModuleCat.of Γ(S.Y', V) Γ(((Scheme.Modules.pushforward S.f').rightDerivedPlus
            (S.d : ℤ)).obj F', V)) ⟶
        ModuleCat.of Γ(Y'', W) Γ(((Scheme.Modules.pushforward f'').rightDerivedPlus
            (S.d : ℤ)).obj ((Scheme.Modules.pullback h').obj F'), W))
    (hψ : Function.Bijective ψ)
    (hone : ∀ a : Γ(((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).obj F', V),
      ψ ((1 : Γ(Y'', W)) ⊗ₜ[Γ(S.Y', V), (h.appLE V W hWV).hom] a) =
        (topDirectImageBaseChangeMapPlus S F' h' f'' h sq).val.app (op W)
          (Scheme.Modules.pullbackSection h
            (((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).obj F')
            V W hWV a)) :
    Function.Bijective
      ((topDirectImageBaseChangeMapPlus S F' h' f'' h sq).val.app (op W)) := by
  have := S.quasiCompact_f'
  have := S.quasiSeparated_f'
  have hA : (((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).obj
      F').IsQuasicoherent :=
    AlgebraicGeometry.ProperCoherentFiniteType.isQuasicoherent_rightDerivedPlus S.f' F'
      inferInstance (S.d : ℤ)
  have hmor : ψ = (affinePullbackSectionsBaseChangeIso h
        (((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).obj F')
        hV hW hWV).hom ≫
      ModuleCat.ofHom (Scheme.Modules.sectionsLinearMap
        (topDirectImageBaseChangeMapPlus S F' h' f'' h sq) W) := by
    refine ModuleCat.ExtendScalars.hom_ext_one_tmul _ fun a => ?_
    refine (hone a).trans (Eq.trans ?_ (CategoryTheory.comp_apply
      (affinePullbackSectionsBaseChangeIso h
        (((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).obj F')
        hV hW hWV).hom
      (ModuleCat.ofHom (Scheme.Modules.sectionsLinearMap
        (topDirectImageBaseChangeMapPlus S F' h' f'' h sq) W)) _).symm)
    exact congrArg (fun z => ModuleCat.ofHom (Scheme.Modules.sectionsLinearMap
        (topDirectImageBaseChangeMapPlus S F' h' f'' h sq) W) z)
      (affinePullbackSectionsBaseChangeIso_one_tmul h
        (((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).obj F')
        hV hW hWV a).symm
  have hbij : Function.Bijective (affinePullbackSectionsBaseChangeIso h
      (((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).obj F')
      hV hW hWV).hom :=
    ConcreteCategory.bijective_of_isIso _
  have happ : ∀ x, ψ x =
      (topDirectImageBaseChangeMapPlus S F' h' f'' h sq).val.app (op W)
        ((affinePullbackSectionsBaseChangeIso h
          (((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).obj F')
          hV hW hWV).hom x) := by
    intro x
    rw [hmor, CategoryTheory.comp_apply]
    rfl
  refine ⟨fun x y hxy => ?_, fun b => ?_⟩
  · obtain ⟨u, hu⟩ := hbij.2 x
    obtain ⟨v, hv⟩ := hbij.2 y
    have huv : u = v := hψ.1 (by rw [happ u, happ v, hu, hv]; exact hxy)
    rw [← hu, ← hv, huv]
  · obtain ⟨u, hu⟩ := hψ.2 b
    exact ⟨_, (happ u).symm.trans hu⟩

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
