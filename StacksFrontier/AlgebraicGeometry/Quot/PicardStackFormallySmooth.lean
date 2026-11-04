module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackToBase
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.FormallySmoothFaithfulTarget

/-!
# Formal smoothness of the Picard stack over its base, reduced to lifting invertible modules

Let `f : X ⟶ B` be a morphism of algebraic spaces over a scheme `S`. The proof of Stacks 0DPJ
begins: "taking base change, this immediately reduces to the following problem: given a first
order thickening `T ⊂ T'` of affine schemes, … and for `X = T ×_{T'} X'` given an invertible
`𝒪_X`-module `𝓛`, prove that there exists an invertible `𝒪_{X'}`-module `𝓛'` whose restriction
to `X` is `𝓛`." Accordingly, the structure morphism
`Picardstack_{X/B} ⟶ 𝒮_B` is formally smooth on objects (Stacks 06D0) as soon as every invertible
module on `X_T` extends along `X_T ⟶ X_{T'}` for every morphism `T ⟶ T'` of test schemes over
`B` which is a first-order thickening of affine schemes.

## Main results

* `AlgebraicGeometry.Space.isFormallySmoothOnObjects_picardToBase_of_exists_lift`: the
  reduction.

## References

* [Stacks Project, Tag 0DPJ](https://stacks.math.columbia.edu/tag/0DPJ)
* [Stacks Project, Tag 06D0](https://stacks.math.columbia.edu/tag/06D0)
* [Stacks Project, Section 0DM9](https://stacks.math.columbia.edu/tag/0DM9)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A morphism of the site which agrees with a first-order thickening up to the identifications
of its source and target is a first-order thickening. -/
private theorem isFirstOrderThickening_of_eq_eqToHom {V W U U' : BigFppfOver B S hS}
    (i : U ⟶ U') (hi : Stacks.Thickenings.IsFirstOrderThickening
      ((BigFppfOver.toScheme B S hS).map i))
    (hV : V = U) (hW : W = U') (j : V ⟶ W) (hj : j = eqToHom hV ≫ i ≫ eqToHom hW.symm) :
    Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map j) := by
  subst hV hW hj
  simpa using hi

/-- **The first step of the proof of Stacks 0DPJ: the reduction to extending invertible
modules.** Let `f : X ⟶ B` be a morphism of algebraic spaces over `S`. If for every morphism
`g : T ⟶ T'` of test schemes over `B` whose underlying morphism of schemes is a first-order
thickening of affine schemes, every invertible module `𝓛` on `X_T` is isomorphic to the inverse
image along `X_T ⟶ X_{T'}` of an invertible module on `X_{T'}`, then the structure morphism
`Picardstack_{X/B} ⟶ 𝒮_B` is formally smooth on objects (Stacks 06D0). -/
theorem isFormallySmoothOnObjects_picardToBase_of_exists_lift
    (hc : ModulePushforwardCoherence B S hS) (s : PicardSituation B S hS)
    (h : ∀ ⦃T T' : s.SchemesOver⦄ (g : T ⟶ T'),
      IsAffine ((BigFppfOver.toScheme B S hS).obj T.left) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj T'.left) →
      Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map g.left) →
      ∀ L : Modules.{u, u} B S hS (s.baseChange T).1 (s.baseChange T).2,
        IsInvertibleModule (s.baseChange T) L →
        ∃ (L' : Modules.{u, u} B S hS (s.baseChange T').1 (s.baseChange T').2)
          (_ : IsInvertibleModule (s.baseChange T') L'),
          Nonempty ((modulePullback B S hS (baseChangeMap s.f g)).obj L' ≅ L)) :
    Stack.IsFormallySmoothOnObjects B S hS _ _ (picardToBase hc s) := by
  refine Stack.isFormallySmoothOnObjects_of_faithful_of_exists_lift ?_
  intro U U' i hU hU' hi x hx y' hy' ψ hψ
  let : Category.{u + 1} (PicardObject s) := (picardCategoryData hc s).category
  let T' : s.SchemesOver := ULiftHom.objDown y'
  let gm : x.T ⟶ T' := ψ.down
  have hTx : x.T.left = U := hx
  have hT' : T'.left = U' := hy'
  have hgl : gm.left = eqToHom hTx ≫ i ≫ eqToHom hT'.symm :=
    IsHomLift.fac' (baseCFG s.base).val.p i ψ
  have hA : IsAffine ((BigFppfOver.toScheme B S hS).obj x.T.left) := by rwa [hTx]
  have hA' : IsAffine ((BigFppfOver.toScheme B S hS).obj T'.left) := by rwa [hT']
  obtain ⟨L', hL', ⟨e⟩⟩ := h gm hA hA'
    (isFirstOrderThickening_of_eq_eqToHom i hi hTx hT' gm.left hgl) x.lineBundle x.invertible
  let x' : PicardObject s := ⟨T', L', hL'⟩
  let m : x ⟶ x' := (⟨gm, e.hom, inferInstance⟩ : PicardHom x x')
  have hm : (picardCFG hc s).val.p.IsHomLift i m := IsHomLift.of_fac' _ i m hTx hT' hgl
  exact ⟨x', hT', m, hm, 𝟙 y', IsHomLift.id hy'⟩

end AlgebraicGeometry.Space

end
