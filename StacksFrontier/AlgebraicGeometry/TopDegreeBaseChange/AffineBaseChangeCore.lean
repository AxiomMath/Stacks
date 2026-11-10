module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.BaseChangeSectionsGenerators
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.BaseChangeTop

/-!
# Conclusion (c) of [Stacks, Tag 0EX3] over affine bases, from a bijection out of a tensor product

Let `Y'` and `Y''` be affine, and write `R' = Γ(Y', ⊤)`, `R'' = Γ(Y'', ⊤)`,
`M = Γ(R^d f'_* F', ⊤)` and `N = Γ(R^d f''_* (h')^* F', ⊤)`. The sections over `⊤` of the source of
the canonical map `γ⁺` of conclusion (c) are the base change `R'' ⊗_{R'} M`
(`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso`), and `Γ(⊤, γ⁺)` is `R''`-linear. So
`Γ(⊤, γ⁺)` is bijective as soon as **some** additive bijection `Ξ : M ⊗_{R'} R'' ⟶ N` satisfies
`Ξ(a ⊗ r) = r • γ⁺(a)`, the right-hand side being read at the pullback of the section `a`: both
`Ξ` and `Γ(⊤, γ⁺)` composed with the base change isomorphism are additive and agree on the pure
tensors. No linearity of `Ξ` is asked for; the identity on pure tensors carries all of it.

This is the module-theoretic half of the source's affine computation. The geometric half — the
construction of `Ξ` from conclusion (b), the projection formula and the Leray comparison
`…TopDegreeBaseChange.isIso_lerayTail` — supplies the bijection.

## Main results

* `…TopDegreeBaseChange.bijective_app_top_topDirectImageBaseChangeMapPlus_of_tensor`: `Γ(⊤, γ⁺)`
  is bijective, given `Ξ`.
* `…TopDegreeBaseChange.isIso_topDirectImageBaseChangeMap_of_isAffine_of_tensor`: `γ` is an
  isomorphism, given `Ξ`, for affine `Y'` and `Y''`.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped ChangeOfRings

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance 10000] HasDerivedCategory.standard

variable {X'' Y'' : Scheme.{u}}

/-- An additive map out of an extension of scalars whose value on every pure tensor `r ⊗ m` is
`r • g m` is linear. -/
theorem extendScalars_map_smul_of_tmul {R S : CommRingCat.{u}} (φ : R ⟶ S)
    {M : ModuleCat.{u} R} {N : ModuleCat.{u} S}
    (Ξ : (ModuleCat.extendScalars φ.hom).obj M →+ N) (g : M → N)
    (hΞ : ∀ (r : S) (m : M), Ξ (r ⊗ₜ[R,φ.hom] m) = r • g m)
    (s : S) (x : (ModuleCat.extendScalars φ.hom).obj M) : Ξ (s • x) = s • Ξ x := by
  have : SMulCommClass R S ((ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of S S)) :=
    ⟨fun r s t ↦ mul_left_comm (φ.hom r) s (t : S)⟩
  induction x using TensorProduct.inductionOn with
  | tmul r m =>
    exact (congrArg Ξ (ModuleCat.ExtendScalars.smul_tmul φ.hom (M := M) s r m)).trans
      ((hΞ _ m).trans ((mul_smul s r (g m)).trans (congrArg (s • ·) (hΞ r m).symm)))
  | add x y hx hy =>
    calc Ξ (s • (x + y)) = Ξ (s • x + s • y) := congrArg Ξ (smul_add s x y)
      _ = Ξ (s • x) + Ξ (s • y) := Ξ.map_add _ _
      _ = s • Ξ x + s • Ξ y := congrArg₂ (· + ·) hx hy
      _ = s • (Ξ x + Ξ y) := (smul_add s _ _).symm
      _ = s • Ξ (x + y) := congrArg (fun z ↦ s • z) (Ξ.map_add x y).symm

/-- The linear map out of an extension of scalars given by an additive map with the values of
`extendScalars_map_smul_of_tmul`. -/
def extendScalarsHomOfTmul {R S : CommRingCat.{u}} (φ : R ⟶ S)
    {M : ModuleCat.{u} R} {N : ModuleCat.{u} S}
    (Ξ : (ModuleCat.extendScalars φ.hom).obj M →+ N) (g : M → N)
    (hΞ : ∀ (r : S) (m : M), Ξ (r ⊗ₜ[R,φ.hom] m) = r • g m) :
    (ModuleCat.extendScalars φ.hom).obj M ⟶ N :=
  ModuleCat.ofHom (X := ↑((ModuleCat.extendScalars φ.hom).obj M)) (Y := ↑N)
    { toFun := Ξ
      map_add' := Ξ.map_add
      map_smul' := extendScalars_map_smul_of_tmul φ Ξ g hΞ }

/-- `extendScalarsHomOfTmul φ Ξ g hΞ` agrees with `Ξ` at every element. -/
theorem extendScalarsHomOfTmul_apply {R S : CommRingCat.{u}} (φ : R ⟶ S)
    {M : ModuleCat.{u} R} {N : ModuleCat.{u} S}
    (Ξ : (ModuleCat.extendScalars φ.hom).obj M →+ N) (g : M → N)
    (hΞ : ∀ (r : S) (m : M), Ξ (r ⊗ₜ[R,φ.hom] m) = r • g m) (x) :
    extendScalarsHomOfTmul φ Ξ g hΞ x = Ξ x := rfl

/-- **`Γ(⊤, γ⁺)` is bijective over affine bases, given an additive bijection out of
`R'' ⊗_{R'} M` with the right values on pure tensors.** -/
theorem bijective_app_top_topDirectImageBaseChangeMapPlus_of_tensor
    (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})
    (F' : S.X'.Modules) [F'.IsQuasicoherent]
    (h' : X'' ⟶ S.X') (f'' : X'' ⟶ Y'') (h : Y'' ⟶ S.Y')
    (sq : h'.toLRSHom.toShHom ≫ S.f'.toLRSHom.toShHom
      = f''.toLRSHom.toShHom ≫ h.toLRSHom.toShHom)
    [IsAffine S.Y'] [IsAffine Y''] (hle : (⊤ : Y''.Opens) ≤ h ⁻¹ᵁ ⊤)
    (Ξ : (ModuleCat.extendScalars (h.appLE ⊤ ⊤ hle).hom).obj
          (ModuleCat.of Γ(S.Y', ⊤) Γ(((Scheme.Modules.pushforward S.f').rightDerivedPlus
            (S.d : ℤ)).obj F', ⊤)) →+
      Γ(((Scheme.Modules.pushforward f'').rightDerivedPlus (S.d : ℤ)).obj
        ((Scheme.Modules.pullback h').obj F'), ⊤))
    (hΞ : Function.Bijective Ξ)
    (hval : ∀ (r : Γ(Y'', ⊤))
        (a : Γ(((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).obj F', ⊤)),
      Ξ (r ⊗ₜ[Γ(S.Y', ⊤), (h.appLE ⊤ ⊤ hle).hom] a) =
        r • (show Γ(((Scheme.Modules.pushforward f'').rightDerivedPlus (S.d : ℤ)).obj
            ((Scheme.Modules.pullback h').obj F'), ⊤) from
          (topDirectImageBaseChangeMapPlus S F' h' f'' h sq).val.app (op ⊤)
          (Scheme.Modules.pullbackSection h
            (((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).obj F')
            ⊤ ⊤ hle a))) :
    Function.Bijective ((topDirectImageBaseChangeMapPlus S F' h' f'' h sq).val.app (op ⊤)) :=
  bijective_app_topDirectImageBaseChangeMapPlus_of_one_tmul S F' h' f'' h sq
    (isAffineOpen_top S.Y') (isAffineOpen_top Y'') hle
    (extendScalarsHomOfTmul (h.appLE ⊤ ⊤ hle) Ξ _ hval) hΞ
    fun a => (extendScalarsHomOfTmul_apply _ _ _ _ _).trans ((hval 1 a).trans (one_smul _ _))

/-- **Conclusion (c) of [Stacks, Tag 0EX3] over affine bases, given the bijection out of the
tensor product.** -/
theorem isIso_topDirectImageBaseChangeMap_of_isAffine_of_tensor
    (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})
    (F' : S.X'.Modules) [F'.IsQuasicoherent]
    (h' : X'' ⟶ S.X') (f'' : X'' ⟶ Y'') (h : Y'' ⟶ S.Y')
    (hsq : IsPullback h' f'' S.f' h) [IsAffine S.Y'] [IsAffine Y'']
    (hle : (⊤ : Y''.Opens) ≤ h ⁻¹ᵁ ⊤)
    (Ξ : (ModuleCat.extendScalars (h.appLE ⊤ ⊤ hle).hom).obj
          (ModuleCat.of Γ(S.Y', ⊤) Γ(((Scheme.Modules.pushforward S.f').rightDerivedPlus
            (S.d : ℤ)).obj F', ⊤)) →+
      Γ(((Scheme.Modules.pushforward f'').rightDerivedPlus (S.d : ℤ)).obj
        ((Scheme.Modules.pullback h').obj F'), ⊤))
    (hΞ : Function.Bijective Ξ)
    (hval : ∀ (r : Γ(Y'', ⊤))
        (a : Γ(((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).obj F', ⊤)),
      Ξ (r ⊗ₜ[Γ(S.Y', ⊤), (h.appLE ⊤ ⊤ hle).hom] a) =
        r • (show Γ(((Scheme.Modules.pushforward f'').rightDerivedPlus (S.d : ℤ)).obj
            ((Scheme.Modules.pullback h').obj F'), ⊤) from
          (topDirectImageBaseChangeMapPlus S F' h' f'' h
            (toShHom_comm_of_isPullback h' f'' h hsq)).val.app (op ⊤)
          (Scheme.Modules.pullbackSection h
            (((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).obj F')
            ⊤ ⊤ hle a))) :
    IsIso (topDirectImageBaseChangeMap S F' h' f'' h
      (toShHom_comm_of_isPullback h' f'' h hsq)) := by
  refine (isIso_topDirectImageBaseChangeMapPlus_iff S F' h' f'' h _).1 ?_
  refine isIso_topDirectImageBaseChangeMapPlus_of_bijective_app S F' h' f'' h _
    (MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @QuasiCompact) hsq
      S.quasiCompact_f')
    (MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @QuasiSeparated) hsq
      S.quasiSeparated_f')
    (fun _ : PUnit.{u + 1} => (⊤ : Y''.Opens))
    (IsOpenCover.mk (by simp)) (fun _ => isAffineOpen_top Y'') (fun _ => ?_)
  exact bijective_app_top_topDirectImageBaseChangeMapPlus_of_tensor S F' h' f'' h _ hle Ξ hΞ hval

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
