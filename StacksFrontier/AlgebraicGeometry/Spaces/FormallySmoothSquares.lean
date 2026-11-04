module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFormallySmooth

/-!
# Formal smoothness of the étale scheme squares of a morphism of algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`, and let `a : U ⟶ X`,
`b : V ⟶ Y` be étale scheme charts fitting in a commuting square over `ψ : U ⟶ V`. The
infinitesimal lifting property of `ψ` can be read either in the site — as formal smoothness of
the morphism `yoneda.map ψ` of representable presheaves, in the sense of
`AlgebraicGeometry.Space.FormallySmooth` — or in schemes, as formal smoothness of the
underlying morphism of schemes in the sense of `Stacks.Smooth.FormallySmoothScheme`. The first
is tested only against square-zero closed immersions of affine *objects of the site*, the
second against first-order thickenings of *all* affine schemes.

## Main results

* `AlgebraicGeometry.Space.isFirstOrderThickening_of_isSquareZeroClosedImmersion`: a
  square-zero closed immersion of objects of the site underlies a first-order thickening of
  schemes.
* `AlgebraicGeometry.Space.exists_hom_of_map_comp_eq`: a morphism of the underlying schemes of
  two objects of the site which is compatible with a morphism of the site is itself a morphism
  of the site.
* `AlgebraicGeometry.Space.formallySmooth_yoneda_map_of_formallySmooth`: if `f` is formally
  smooth then so is `yoneda.map ψ`, for every commuting square of étale scheme charts of `f`.
* `AlgebraicGeometry.Space.formallySmooth_yoneda_map_of_formallySmoothScheme`: if the scheme
  morphism underlying `ψ` is formally smooth, then `yoneda.map ψ` is formally smooth.

## References

* [Stacks Project, Tag 02H0](https://stacks.math.columbia.edu/tag/02H0)
* [Stacks Project, Tag 03FR](https://stacks.math.columbia.edu/tag/03FR)
* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
* [Stacks Project, Tag 061H](https://stacks.math.columbia.edu/tag/061H)
* [Stacks Project, Tag 061K](https://stacks.math.columbia.edu/tag/061K)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A square-zero closed immersion of objects of the big fppf site of `S` underlies a
first-order thickening of schemes. -/
theorem isFirstOrderThickening_of_isSquareZeroClosedImmersion {T T' : BigFppfOver B S hS}
    {i : T ⟶ T'} (hi : IsSquareZeroClosedImmersion B S hS i) :
    Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map i) :=
  ⟨hi.1, hi.2⟩

/-- A morphism of the underlying schemes of two objects of the big fppf site of `S` which is
compatible with a morphism `ψ` of the site is itself a morphism of the site. -/
theorem exists_hom_of_map_comp_eq {T' U V : BigFppfOver B S hS} (ψ : U ⟶ V) {k : T' ⟶ V}
    {ρ : (BigFppfOver.toScheme B S hS).obj T' ⟶ (BigFppfOver.toScheme B S hS).obj U}
    (hρ : ρ ≫ (BigFppfOver.toScheme B S hS).map ψ = (BigFppfOver.toScheme B S hS).map k) :
    ∃ z : T' ⟶ U, (BigFppfOver.toScheme B S hS).map z = ρ ∧ z ≫ ψ = k := by
  have hρ' : ρ ≫ B.inclusion.map ψ.left = B.inclusion.map k.left := hρ
  have hover : B.inclusion.preimage ρ ≫ U.hom = T'.hom := B.inclusion.map_injective (by
    rw [B.inclusion.map_comp, B.inclusion.map_preimage, ← Over.w ψ, B.inclusion.map_comp,
      ← Category.assoc, hρ', ← B.inclusion.map_comp, Over.w k])
  set z : T' ⟶ U := Over.homMk (B.inclusion.preimage ρ) hover
  have hmapz : (BigFppfOver.toScheme B S hS).map z = ρ := B.inclusion.map_preimage ρ
  exact ⟨z, hmapz, (BigFppfOver.toScheme B S hS).map_injective (by
    rw [Functor.map_comp, hmapz, hρ])⟩

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U V : BigFppfOver B S hS} {ψ : U ⟶ V}

/-- Let `f : X ⟶ Y` be a formally smooth morphism of algebraic spaces over `S` and let
`a : U ⟶ X`, `b : V ⟶ Y` be étale scheme charts fitting in a commuting square over `ψ : U ⟶ V`.
Then the morphism `yoneda.map ψ` of representable presheaves is formally smooth. -/
theorem formallySmooth_yoneda_map_of_formallySmooth {f : X ⟶ Y} (hf : FormallySmooth f)
    {a : yoneda.obj U ⟶ X} {b : yoneda.obj V ⟶ Y} (hsq : a ≫ f = yoneda.map ψ ≫ b)
    (ha : IsEtale B S hS a) (hb : IsEtale B S hS b) :
    FormallySmooth (yoneda.map ψ) :=
  fun _ _ hT hT' _ hi x y hxy ↦ exists_lift_of_formallySmooth hf
    (presheaf_etale_of_isEtale B S hS ha) (presheaf_etale_of_isEtale B S hS hb) hsq.symm hT hT' hi
    (g := x) (k := y) hxy

/-- If the morphism of schemes underlying `ψ : U ⟶ V` is formally smooth, that is, has the lifting
property against first-order thickenings of all affine schemes, then the morphism `yoneda.map ψ`
of representable presheaves on the big fppf site of `S` is formally smooth. -/
theorem formallySmooth_yoneda_map_of_formallySmoothScheme
    (hψ : Stacks.Smooth.FormallySmoothScheme ((BigFppfOver.toScheme B S hS).map ψ)) :
    FormallySmooth (yoneda.map ψ) := by
  intro T T' hT hT' i hi x y hxy
  obtain ⟨ρ, hρ₁, hρ₂⟩ := hψ hT hT' ((BigFppfOver.toScheme B S hS).map i)
    (isFirstOrderThickening_of_isSquareZeroClosedImmersion hi)
    ((BigFppfOver.toScheme B S hS).map x) ((BigFppfOver.toScheme B S hS).map y)
    (by rw [← Functor.map_comp, ← Functor.map_comp]; exact congrArg _ hxy)
  obtain ⟨z, hmapz, h₂⟩ := exists_hom_of_map_comp_eq ψ hρ₁
  have h₁ : i ≫ z = x := (BigFppfOver.toScheme B S hS).map_injective (by
    rw [Functor.map_comp, hmapz, hρ₂])
  exact ⟨z, h₁, h₂⟩

end AlgebraicGeometry.Space

end
