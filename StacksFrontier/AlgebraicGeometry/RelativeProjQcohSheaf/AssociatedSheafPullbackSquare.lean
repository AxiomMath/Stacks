module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AssociatedSheafPullback

/-!
# The comparison square of property (2) of Tag 01O7, from the degreewise families

Let `S` be a scheme, `𝒜` a graded `𝒪_S`-algebra and `ℳ` a graded `𝒜`-module (Situation 01NN).
Property (1) of [Stacks, Tag 01O7] asserts a canonical isomorphism `ℳ̃_T ≅ h^*ℳ̃` between the
module `ℳ̃_T` of [Stacks, Tag 01O6] attached to a quadruple `(d, f : T → S, L, ψ)` and the pullback
of the sheaf on the relative projective spectrum along the morphism `h` the quadruple classifies;
property (2) asserts that those isomorphisms are compatible with pullback along a morphism
`g : T' ⟶ T` of test schemes.

Let `c : ℳ̃_T ⟶ 𝒩` be a morphism out of the module of a quadruple, `c' : ℳ̃_{T'} ⟶ 𝒩'` a morphism
out of the module of the pulled-back quadruple and `e : g^*𝒩 ⟶ 𝒩'`. If the degreewise families of
`c` and `c'` correspond under the pullback, one equation per degree, then the square

```
g^*ℳ̃_T  --g^*c-->  g^*𝒩
   |                  |
   | base change      | e
   v                  v
ℳ̃_{T'}  --c'-->     𝒩'
```

commutes, the left vertical being the canonical base-change isomorphism
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.associatedSheafPullbackIso` of [Stacks, Tag 01O6].

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.pullback_comparison_square`: the square commutes,
  given the degreewise correspondence.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.pullback_comparison_eq`: the comparison over `T'`
  is the comparison over `T` pulled back and transported along the base-change isomorphism.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.isIso_pullback_comparison`: if `c` and `e` are
  isomorphisms, then so is `c'`.

## References

* [Stacks Project, Tag 01O7](https://stacks.math.columbia.edu/tag/01O7)
* [Stacks Project, Tag 01O6](https://stacks.math.columbia.edu/tag/01O6)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

open AlgebraicGeometry Stacks.RingedSpace

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory
attribute [local instance] Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.modulesAbelian
  Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.modulesHasCoproducts

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

variable {T' T S : Scheme.{u}} {f : T ⟶ S}
  {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)}
  (M : SheafOfModules.GradedModule.{u, u, u} A) (d : ℤ)
  (L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
  (g : T' ⟶ T)

/-- The comparison square of property (2) of [Stacks, Tag 01O7] commutes as soon as the degreewise
families correspond: for a quadruple `(d, f : T → S, L, ψ)`, a morphism `c : ℳ̃_T ⟶ 𝒩`, a morphism
`c' : ℳ̃_{T'} ⟶ 𝒩'` for the pulled-back quadruple and a morphism `e : g^*𝒩 ⟶ 𝒩'`, suppose that in
every degree `n` the pullback of the degree-`n` component of `c` followed by `e` is the comparison
of the degreewise summands followed by the degree-`n` component of `c'`. Then `g^*c` followed by
`e` is the base-change isomorphism of [Stacks, Tag 01O6] followed by `c'`. -/
theorem pullback_comparison_square (ψ : Twisting f A d L)
    {N : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
    {N' : SheafOfModules.{u} (structureRingSheaf T'.toRingedSpace)}
    (e : (pullbackFunctor (ringedSpaceHom g)).obj N ⟶ N')
    (c : Twisting.associatedSheaf M ψ ⟶ N)
    (c' : Twisting.associatedSheaf M (ψ.pullback g) ⟶ N')
    (hb : ∀ n : ℤ,
      (pullbackFunctor (ringedSpaceHom g)).map (Twisting.pureTensor M ψ n ≫ c) ≫ e =
        summandPullback M d L g n ≫ Twisting.pureTensor M (ψ.pullback g) n ≫ c') :
    (pullbackFunctor (ringedSpaceHom g)).map c ≫ e =
      (associatedSheafPullbackIso M d L g ψ).hom ≫ c' := by
  have hbal : ∀ p : ℤ × ℤ,
      (pullbackFunctor (ringedSpaceHom g)).map (relationLeft f M d L p) ≫
          (summandPullback M d L g (p.1 + p.2) ≫
            Twisting.pureTensor M (ψ.pullback g) (p.1 + p.2) ≫ c') =
        (pullbackFunctor (ringedSpaceHom g)).map (Twisting.relationRight M ψ p) ≫
          (summandPullback M d L g p.1 ≫ Twisting.pureTensor M (ψ.pullback g) p.1 ≫ c') := by
    intro p
    simpa only [Category.assoc] using
      congrArg (· ≫ c') (summandPullback_pureTensor_balanced M d L g ψ p)
  obtain ⟨k, -, huniq⟩ := pullback_existsUnique_hom M d L g ψ N'
    (fun n => summandPullback M d L g n ≫ Twisting.pureTensor M (ψ.pullback g) n ≫ c') hbal
  refine (huniq _ fun n => ?_).trans (huniq _ fun n => ?_).symm
  · rw [← Category.assoc, ← Functor.map_comp, hb n]
  · rw [← Category.assoc, associatedSheafPullbackIso_pureTensor, Category.assoc]

/-- Under the hypotheses of `pullback_comparison_square`, the morphism `c'` out of the module of
the pulled-back quadruple is the inverse of the base-change isomorphism of [Stacks, Tag 01O6]
followed by the pullback of `c` and by `e`. -/
theorem pullback_comparison_eq (ψ : Twisting f A d L)
    {N : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
    {N' : SheafOfModules.{u} (structureRingSheaf T'.toRingedSpace)}
    (e : (pullbackFunctor (ringedSpaceHom g)).obj N ⟶ N')
    (c : Twisting.associatedSheaf M ψ ⟶ N)
    (c' : Twisting.associatedSheaf M (ψ.pullback g) ⟶ N')
    (hb : ∀ n : ℤ,
      (pullbackFunctor (ringedSpaceHom g)).map (Twisting.pureTensor M ψ n ≫ c) ≫ e =
        summandPullback M d L g n ≫ Twisting.pureTensor M (ψ.pullback g) n ≫ c') :
    c' = (associatedSheafPullbackIso M d L g ψ).inv ≫
      (pullbackFunctor (ringedSpaceHom g)).map c ≫ e :=
  (Iso.eq_inv_comp _).mpr
    (pullback_comparison_square M d L g ψ e c c' hb).symm

/-- Under the hypotheses of `pullback_comparison_square`, if `c` and `e` are isomorphisms, then so
is the morphism `c'` out of the module of the pulled-back quadruple. -/
theorem isIso_pullback_comparison (ψ : Twisting f A d L)
    {N : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
    {N' : SheafOfModules.{u} (structureRingSheaf T'.toRingedSpace)}
    (e : (pullbackFunctor (ringedSpaceHom g)).obj N ⟶ N')
    (c : Twisting.associatedSheaf M ψ ⟶ N)
    (c' : Twisting.associatedSheaf M (ψ.pullback g) ⟶ N')
    (hb : ∀ n : ℤ,
      (pullbackFunctor (ringedSpaceHom g)).map (Twisting.pureTensor M ψ n ≫ c) ≫ e =
        summandPullback M d L g n ≫ Twisting.pureTensor M (ψ.pullback g) n ≫ c')
    (hc : IsIso c) (he : IsIso e) : IsIso c' := by
  rw [pullback_comparison_eq M d L g ψ e c c' hb]
  infer_instance

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
