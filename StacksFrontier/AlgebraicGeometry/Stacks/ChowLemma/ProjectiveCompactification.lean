module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveSpaceOver
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartProperImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperPermanence

/-!
# Relative projective space over an algebraic space is proper over it

Let `X` be an algebraic space over `S` and `n` a natural number. Relative projective `n`-space
`ℙⁿ_X = X × ℙⁿ_S` (`AlgebraicGeometry.Space.projectiveSpaceOver`) is an algebraic space, and its
projection to `X` is proper, being the base change of the proper morphism `ℙⁿ_S ⟶ S`. Together
with the open immersion `𝔸ⁿ_X ⟶ ℙⁿ_X` over `X`
(`AlgebraicGeometry.Space.isOpenImmersion_affineSpaceOverToProjectiveSpaceOver`) this is what the
proof of Stacks 0CQ8 needs: Stacks 088N produces an immersion of a dense open of the gerbe's base
space into `𝔸ⁿ_Y`, and the source composes it with `𝔸ⁿ_Y ⊆ ℙⁿ_Y` so that scheme theoretic images
taken in `ℙⁿ_Y` are proper over `Y`.

## Main results

* `AlgebraicGeometry.Space.isAlgebraicSpace_projectiveSpaceOver`: `ℙⁿ_X` is an algebraic space.
* `AlgebraicGeometry.Space.isProper_projectiveSpaceOver_fst`: `ℙⁿ_X ⟶ X` is proper.
* `AlgebraicGeometry.Space.exists_isOpenImmersion_affineSpaceOver_isProper`: the open immersion
  `𝔸ⁿ_X ⟶ ℙⁿ_X` over `X`, packaged with the properness of `ℙⁿ_X ⟶ X`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- `ℙⁿ_X = X × ℙⁿ_S` is isomorphic to the product of the presheaf represented by the object
`ℙⁿ_S` of the site with `X`, the factors swapped. -/
noncomputable def projectiveSpaceOverIsoProdYoneda (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (n : ℕ) :
    projectiveSpaceOver B S hS X n ≅ yoneda.obj (projectiveSpaceSiteObject B S hS n) ⨯ X :=
  prod.braiding _ _ ≪≫ prod.mapIso (projectiveSpaceFunctorIso B S hS n) (Iso.refl X)

/-- **Relative projective space over an algebraic space is an algebraic space**: it is the
restriction of `X` to the object `ℙⁿ_S` of the site (`isAlgebraicSpace_prod_yoneda_obj`). -/
theorem isAlgebraicSpace_projectiveSpaceOver {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (n : ℕ) :
    IsAlgebraicSpace B S hS (projectiveSpaceOver B S hS X n) :=
  (isAlgebraicSpace_prod_yoneda_obj (projectiveSpaceSiteObject B S hS n) hX).of_iso
    (projectiveSpaceOverIsoProdYoneda B S hS X n).symm

/-- **Relative projective space over an algebraic space is proper over it.** The projection
`ℙⁿ_S × X ⟶ X` is the base change of the proper morphism `ℙⁿ_S ⟶ S`, hence representable and
proper; `ℙⁿ_X ⟶ X` is it precomposed with an isomorphism. -/
theorem isProper_projectiveSpaceOver_fst {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (n : ℕ) :
    IsProper B S hS (prod.fst : projectiveSpaceOver B S hS X n ⟶ X) := by
  let Pₛ := projectiveSpaceSiteObject B S hS n
  have hterm : ∀ T : BigFppfOver B S hS,
      (BigFppfOver.toScheme B S hS).map (Over.mkIdTerminal.from T) = B.inclusion.map T.hom := by
    intro T
    simp
  have hP : IsAlgebraicSpace B S hS (yoneda.obj Pₛ ⨯ X) := isAlgebraicSpace_prod_yoneda_obj Pₛ hX
  have hsnd : IsProper B S hS (prod.snd : yoneda.obj Pₛ ⨯ X ⟶ X) :=
    (presheaf_isProper_iff B S hS prod.snd hP hX (relativelyRepresentable_prod_snd Pₛ X)).2
      (presheaf_prod_snd inferInstance Pₛ X
        (by rw [hterm]; exact isProper_projectiveSpaceOver n S))
  have hfac : (prod.fst : projectiveSpaceOver B S hS X n ⟶ X) =
      (projectiveSpaceOverIsoProdYoneda B S hS X n).hom ≫ prod.snd := by
    simp [projectiveSpaceOverIsoProdYoneda]
  rw [hfac]
  exact isProper_comp' B S hS _ _ hP hX (isProper_of_isIso B S hS _) hsnd

/-- **Relative affine space over an algebraic space is an open subspace of a space proper over
it.** For an algebraic space `X` over `S` and `n : ℕ`, `𝔸ⁿ_X ⟶ ℙⁿ_X` is an open immersion over
`X` and `ℙⁿ_X ⟶ X` is proper. -/
theorem exists_isOpenImmersion_affineSpaceOver_isProper
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X) (n : ℕ) :
    ∃ (P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS P) (p : P ⟶ X)
      (k : affineSpaceOver B S hS X n ⟶ P),
      IsProper B S hS p ∧ IsOpenImmersion B S hS k ∧ k ≫ p = prod.fst :=
  ⟨projectiveSpaceOver B S hS X n, isAlgebraicSpace_projectiveSpaceOver B S hS hX n, prod.fst,
    affineSpaceOverToProjectiveSpaceOver B S hS X n, isProper_projectiveSpaceOver_fst B S hS hX n,
    isOpenImmersion_affineSpaceOverToProjectiveSpaceOver B S hS X n,
    affineSpaceOverToProjectiveSpaceOver_fst B S hS X n⟩

end AlgebraicGeometry.Space
