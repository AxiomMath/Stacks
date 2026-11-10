module

public import StacksFrontier.Homology.CompositeCollapse

/-!
# The collapse isomorphism inverted, read at a second resolution

`Stacks.RightDerivedComp.objIso` is the collapse `R ⁿ (G ⋙ T) (A) ≅ R ⁿ T (G A)` for `G`
additive, left exact and injectives-preserving at a `G`-acyclic `A`, and
`Stacks.RightDerivedComp.objIso_hom_eq` computes it on a comparison
`φ : mapCocomplex G I ⟶ J.cocomplex` of `G` applied to a resolution of `A` **into** an injective
resolution `J` of `G A`.

A consumer that holds the comparison in the other direction cannot use that form. The comparison
one gets for free is the one `CategoryTheory.InjectiveResolution.desc` produces out of the
**chosen** resolution of `G A`, so it points `J.cocomplex ⟶ mapCocomplex G I`, and its
augmentation clause is `CategoryTheory.InjectiveResolution.desc_mapOfPreservesInjectives_f_zero`.
This file reads the collapse at that comparison instead.

## Main results

* `Stacks.RightDerivedComp.objIso_inv_eq`: **the collapse isomorphism inverted, computed by a
  comparison out of a second resolution.** For any injective resolution `J` of `G A` and any
  `φ : J.cocomplex ⟶ mapCocomplex G I` carrying the augmentation of `J` to `G` of the
  augmentation of `I`, the inverse of the collapse is the computation of `R ⁿ T (G A)` on `J`,
  then the degree-`n` homology of `T` applied to `φ`, then the computation of
  `R ⁿ (G ⋙ T) (A)` on `I` inverted.

  Nothing is assumed beyond what `Stacks.RightDerivedComp.objIso` itself asks for, and in
  particular nothing of `J` or of `φ` past the augmentation clause: as with `objIso_hom_eq`, the
  statement is an independence statement, the comparison being pinned only up to homotopy.

## Implementation notes

*The augmentation hypothesis is given in the `desc` shape, not the `objIso_hom_eq` shape.* The
two differ by which side the identity of `G A` sits on, and writing
`𝟙 (G.obj A) ≫ (mapOfAcyclic G I hA).ι.f 0` out as the type of a `have` is **not type-correct at
`implicit` transparency**: the identity is at
`((CochainComplex.single₀ _).obj (G A)).X 0`, which reduces to `G A` only at default
transparency. So the hypothesis of
`CategoryTheory.InjectiveResolution.isoRightDerivedObj_hom_naturality` is supplied inline, where
the application fixes its expected type, and `CategoryTheory.Category.id_comp` is used as a term.

## References

* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.RightDerivedComp

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasInjectiveResolutions C] [HasInjectiveResolutions D]
  (G : C ⥤ D) [G.Additive] {A : C} (I : InjectiveResolution A)
  [PreservesFiniteLimits G] (hA : ∀ n, 0 < n → IsZero ((G.rightDerived n).obj A))
  [G.PreservesInjectiveObjects] (T : D ⥤ E) [T.Additive] (n : ℕ)

/-- **The collapse isomorphism inverted, computed by a comparison out of a second injective
resolution of `G A`.** For an injective resolution `J` of `G.obj A` and a comparison
`φ : J.cocomplex ⟶ mapCocomplex G I` carrying the augmentation of `J` to `G` applied to the
augmentation of `I`, the inverse of `Stacks.RightDerivedComp.objIso` is

> the computation of `R ⁿ T (G A)` on `J`, then the degree-`n` homology of `T` applied to `φ`,
> then the computation of `R ⁿ (G ⋙ T) (A)` on `I` inverted.

This is `CategoryTheory.InjectiveResolution.isoRightDerivedObj_hom_naturality` at the identity of
`G.obj A` between `J` and `Stacks.RightDerivedComp.mapOfAcyclic`, whose augmentation in degree
zero is `G` applied to that of `I` by `Stacks.RightDerivedComp.mapOfAcyclic_ι_f_zero`.

It is the mirror of `Stacks.RightDerivedComp.objIso_hom_eq`, at the direction of comparison that
`CategoryTheory.InjectiveResolution.desc_mapOfPreservesInjectives_f_zero` supplies. Nothing is
assumed beyond what `objIso` asks for. -/
theorem objIso_inv_eq (J : InjectiveResolution (G.obj A))
    (φ : J.cocomplex ⟶ mapCocomplex G I)
    (hφ : J.ι.f 0 ≫ φ.f 0 = G.map (I.ι.f 0)) :
    (objIso G I hA T n).inv =
      (J.isoRightDerivedObj T n).hom ≫
        HomologicalComplex.homologyMap ((T.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) n ≫
          (I.isoRightDerivedObj (G ⋙ T) n).inv := by
  have h := InjectiveResolution.isoRightDerivedObj_hom_naturality (𝟙 (G.obj A)) J
    (mapOfAcyclic G I hA) φ
    (by rw [mapOfAcyclic_ι_f_zero]; exact hφ.trans (Category.id_comp _).symm) T n
  rw [CategoryTheory.Functor.map_id, Category.id_comp] at h
  change ((mapOfAcyclic G I hA).isoRightDerivedObj T n).hom ≫
    (I.isoRightDerivedObj (G ⋙ T) n).inv = _
  rw [h]
  exact Category.assoc _ _ _

end Stacks.RightDerivedComp

end
