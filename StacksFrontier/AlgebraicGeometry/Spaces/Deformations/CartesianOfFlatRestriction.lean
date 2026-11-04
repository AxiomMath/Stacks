module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleBaseChangeCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.Properties
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningAffineOverAffineBase.EtaleIsoAlongSurjection
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.BaseChangeOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleSite

/-!
# A flat deformation mapping to a base change is itself a base change

Let `W ⊂ B'` be a finite order thickening of algebraic spaces over a scheme `S`, let `B' ⟶ Z`
and `π : X' ⟶ Z` be morphisms of algebraic spaces, and let `q : Xₙ ⟶ B'` be flat. Let
`g : Xₙ ⟶ X'` lie over `Z`. If the restriction of `g` to `X₀ = Xₙ ×_{B'} W` exhibits `X₀` as
`X' ×_Z W`, then `g` exhibits `Xₙ` as `X' ×_Z B'`.

The morphism `h : Xₙ ⟶ P = B' ×_Z X'` is a morphism of thickenings `(X₀ ⊂ Xₙ) ⟶ (P_W ⊂ P)` over
`W ⊂ B'`, with `Xₙ` flat over `B'` and both special fibres the base changes along `W ⊂ B'`:
a cartesian finite-order deformation. Its special fibre `X₀ ⟶ P_W` is an isomorphism (both are
`X' ×_Z W`), so it is étale, and Stacks 0CG6 (part 0CGR) makes `h` étale. The base change of
`h` along the surjection `P_W ⊂ P` is the isomorphism `X₀ ⟶ P_W`, so `h` is an isomorphism.

This is how the body of [Stacks Project, Tag 0D3X] gets `Xₙ = X ×_{Spec(lim Rₙ)} Spec(Rₙ)` for
the space `X` it constructs.

## Main results

* `AlgebraicGeometry.Space.isPullback_of_isFlat_of_isPullback_restriction`: the statement above.

## References

* [Stacks Project, Tag 0CG6](https://stacks.math.columbia.edu/tag/0CG6)
* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A flat deformation mapping to a base change is a base change.**  Let `W ⊂ B'` be a finite
order thickening, `q : Xₙ ⟶ B'` flat, `β : B' ⟶ Z`, `π : X' ⟶ Z` and `g : Xₙ ⟶ X'` with
`g ≫ π = q ≫ β`. Suppose `X₀` with `a : X₀ ⟶ Xₙ`, `i = a ≫ g` and `r : X₀ ⟶ W` is both
`Xₙ ×_{B'} W` and `X' ×_Z W`. Then `Xₙ = B' ×_Z X'`. -/
theorem isPullback_of_isFlat_of_isPullback_restriction {Xn X' B' Z : AlgebraicSpaces B S hS}
    (W : ClosedSubspaces B S hS B'.1) (hW : IsFiniteOrderThickening B S hS B' W.1)
    (q : Xn ⟶ B') (hq : IsFlat B S hS q.hom) (β : B' ⟶ Z) (π : X' ⟶ Z) (g : Xn ⟶ X')
    (hg : g ≫ π = q ≫ β) {X₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : X₀ ⟶ Xn.1)
    (i : X₀ ⟶ X'.1) (r : X₀ ⟶ W.1.toFunctor) (ha : IsPullback a r q.hom W.1.ι)
    (hi : IsPullback i r π.hom (W.1.ι ≫ β.hom)) (hai : a ≫ g.hom = i) :
    IsPullback q.hom g.hom β.hom π.hom := by
  obtain ⟨k, hk⟩ := hW
  have hgw : q.hom ≫ β.hom = g.hom ≫ π.hom := (congrArg (fun m => m.hom) hg).symm
  let P : AlgebraicSpaces B S hS :=
    ⟨pullback β.hom π.hom, isAlgebraicSpace_pullback B S hS β.hom π.hom B'.2 X'.2 Z.2⟩
  let p₁ : P ⟶ B' := ObjectProperty.homMk (pullback.fst β.hom π.hom)
  let h : Xn.1 ⟶ P.1 := pullback.lift q.hom g.hom hgw
  have hh₁ : h ≫ p₁.hom = q.hom := pullback.lift_fst _ _ _
  have hh₂ : h ≫ pullback.snd β.hom π.hom = g.hom := pullback.lift_snd _ _ _
  have hF := isPullback_preimageSubspace B S hS q W
  have hG := isPullback_preimageSubspace B S hS p₁ W
  let f := hG.lift ((preimageSubspace B S hS q W).1.ι ≫ h) (preimageProjection B S hS q W).hom
    (by rw [Category.assoc, hh₁]; exact hF.w)
  have hf₁ : f ≫ (preimageSubspace B S hS p₁ W).1.ι = (preimageSubspace B S hS q W).1.ι ≫ h :=
    hG.lift_fst _ _ _
  have hf₂ : f ≫ (preimageProjection B S hS p₁ W).hom = (preimageProjection B S hS q W).hom :=
    hG.lift_snd _ _ _
  let D : CartesianFiniteOrderDeformation B S hS :=
    { X' := Xn
      Y' := P
      B' := B'
      X := (preimageSubspace B S hS q W).1
      Y := (preimageSubspace B S hS p₁ W).1
      B := W.1
      base_finiteOrder := ⟨k, hk⟩
      source_thickening := (isNthOrderThickening_preimage B S hS W.1 q hk).isThickening
      target_thickening := (isNthOrderThickening_preimage B S hS W.1 p₁ hk).isThickening
      f := f
      f' := h
      g := (preimageProjection B S hS p₁ W).hom
      g' := p₁.hom
      comm_f := hf₁
      comm_g := hG.w.symm
      isPullback_X := by rw [hf₂, hh₁]; exact hF
      isPullback_Y := hG
      flat_X' := by rw [hh₁]; exact hq }
  -- `X₀ ≅ Xₙ ×_{B'} W` and `X₀ ≅ P ×_{B'} W ≅ X' ×_Z W`, compatibly with `f`
  have hGX : IsPullback ((preimageSubspace B S hS p₁ W).1.ι ≫ pullback.snd β.hom π.hom)
      (preimageProjection B S hS p₁ W).hom π.hom (W.1.ι ≫ β.hom) :=
    hG.paste_horiz (IsPullback.of_hasPullback β.hom π.hom).flip
  have he : (ha.isoIsPullback _ _ hF).hom ≫ f = (hi.isoIsPullback _ _ hGX).hom := by
    apply hGX.hom_ext
    · rw [IsPullback.isoIsPullback_hom_fst, Category.assoc, reassoc_of% hf₁, hh₂,
        ← Category.assoc, IsPullback.isoIsPullback_hom_fst, hai]
    · rw [IsPullback.isoIsPullback_hom_snd, Category.assoc, hf₂, IsPullback.isoIsPullback_hom_snd]
  have hfiso : IsIso f := by
    have : IsIso ((ha.isoIsPullback _ _ hF).hom ≫ f) := by rw [he]; infer_instance
    exact IsIso.of_isIso_comp_left (ha.isoIsPullback _ _ hF).hom f
  have hhet : IsEtale B S hS h := D.isEtale_iff.1 (isEtale_of_isIso B S hS f)
  have sq : IsPullback f (preimageSubspace B S hS q W).1.ι (preimageSubspace B S hS p₁ W).1.ι h :=
    (IsPullback.of_bot D.isPullback_X hf₁.symm hG).flip
  have hiso : IsIso h :=
    isIso_of_isEtale_of_isIso_pullback_of_isSurjective B S hS P.2
      (preimageSubspace B S hS p₁ W).2.1 Xn.2 sq hfiso
      (isSurjective_ι_of_isThickening B S hS D.target_thickening) hhet
  exact IsPullback.of_iso_pullback ⟨hgw⟩ (asIso h) hh₁ hh₂

end AlgebraicGeometry.Space

end
