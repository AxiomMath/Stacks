module

public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesBandModule

/-!
# The sections of the band over a frame are the parameters `Hom(Δ^*Ω_{I/U'}, 𝒞_{U/U'})`

Let `ζ` be an object over `U` of the gerbe of smooth lifts of Stacks 0CJP, along a first order
thickening, and `𝒢` the band of Stacks 0CJY. The sections of `𝒢` over `U` are the automorphisms
of `ζ` (`CategoryTheory.Functor.bandFrame`), and these are the `𝒪_U`-linear maps
`Δ^*Ω_{I/U'} ⟶ 𝒞_{U/U'}` (`AlgebraicGeometry.Stack.EtaleSmoothLift.paramOf`, equation 0CKH of the
proof of Stacks 0CKG). This file records the composite as an additive isomorphism
`AlgebraicGeometry.Stack.EtaleSmoothLift.bandParam`, and that it carries the descended product of
`AlgebraicGeometry.Stack.EtaleSmoothLift.bandSmul` to multiplication by the function on `U`
(`AlgebraicGeometry.Stack.EtaleSmoothLift.bandParam_bandSmul`): the band module, read at a frame,
is the module of parameters.

## References

* [Stacks Project, Tag 0CKG](https://stacks.math.columbia.edu/tag/0CKG)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Stack.EtaleSmoothLift

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} {ι : 𝒳 ⟶ 𝒳'} {hι : IsThickening ι}
  {W : AlgebraicSpaces B S hS}
  {x : (algebraicSpaceStackFunctor B S hS).obj W ⟶ 𝒳}
  {hx : AlgebraicStacks.IsSmooth B S hS x}

attribute [local instance] isFibered_proj

variable (hι₁ : AlgebraicStacks.IsFirstOrderThickening B S hS ι)
  {𝒢 : Sheaf (Space.SpacesEtale.topology B S hS W) CommGrpCat.{u + 1}}
  (θ : ∀ (U : Space.SpacesEtale B S hS W)
    (ξ : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U),
    (Over.forget U).op ⋙ 𝒢.obj ⋙ forget CommGrpCat.{u + 1} ≅
      (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).morPresheaf ξ ξ ⋙
        uliftFunctor.{u + 1, u + 1})
  (h₁ : ∀ (U : Space.SpacesEtale B S hS W)
    (ξ : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U) (g : Over U)
    (a b : 𝒢.obj.obj (op g.left)),
      ((θ U ξ).hom.app (op g) (a * b)).down =
        ((θ U ξ).hom.app (op g) a).down ≫ ((θ U ξ).hom.app (op g) b).down)

/-- The automorphism of `ζ` attached to the parameter `paramOf hι₁ α` of an automorphism `α` is
`α` itself. -/
theorem ofParam_paramOf {U : Space.SpacesEtale B S hS W}
    {ζ : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U} (α : ζ ⟶ ζ) :
    ofParam hι₁ ζ (paramOf hι₁ α) = α :=
  paramOf_injective hι₁ (paramOf_ofParam hι₁ ζ _)

include h₁ in
/-- **The sections of the band over `U` are the parameters of a frame `ζ` over `U`**: the
composite of the banding `𝒢(U) ≃ Aut(ζ)` with `Aut(ζ) ≃ Hom(Δ^*Ω_{I/U'}, 𝒞_{U/U'})`, an
isomorphism of groups. -/
def bandParam (U : Space.SpacesEtale B S hS W)
    (ζ : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U) :
    Additive (𝒢.val.obj (op U)) ≃+ LiftsActingGroup hι₁ ζ.1 where
  toFun a := paramOf hι₁ (Functor.bandFrame θ U ζ a.toMul)
  invFun t := Additive.ofMul ((Functor.bandFrame θ U ζ).symm (ofParam hι₁ ζ t))
  left_inv a := by
    change Additive.ofMul ((Functor.bandFrame θ U ζ).symm
      (ofParam hι₁ ζ (paramOf hι₁ (Functor.bandFrame θ U ζ a.toMul)))) = a
    rw [ofParam_paramOf, Equiv.symm_apply_apply]
    rfl
  right_inv t := by
    change paramOf hι₁ (Functor.bandFrame θ U ζ ((Functor.bandFrame θ U ζ).symm
      (ofParam hι₁ ζ t))) = t
    rw [Equiv.apply_symm_apply, paramOf_ofParam]
  map_add' a b := by
    change paramOf hι₁ (Functor.bandFrame θ U ζ (a.toMul * b.toMul)) =
      paramOf hι₁ (Functor.bandFrame θ U ζ a.toMul) + paramOf hι₁ (Functor.bandFrame θ U ζ b.toMul)
    rw [Functor.bandFrame_mul θ h₁, paramOf_comp]

/-- `bandParam hι₁ θ h₁ U ζ` sends a section `a` of the band to the parameter of the automorphism
`Functor.bandFrame θ U ζ a` of `ζ`. -/
theorem bandParam_apply (U : Space.SpacesEtale B S hS W)
    (ζ : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U)
    (a : Additive (𝒢.val.obj (op U))) :
    bandParam hι₁ θ h₁ U ζ a = paramOf hι₁ (Functor.bandFrame θ U ζ a.toMul) :=
  rfl

/-- **The band module, read at a frame, is the module of parameters**: the descended product by a
function `r` on `U` is carried to multiplication by `r` on `𝒞_{U/U'}`. -/
theorem bandParam_bandSmul
    (hne : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).LocallyNonempty
      (Space.SpacesEtale.topology B S hS W))
    (hlc : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).LocallyConnected
      (Space.SpacesEtale.topology B S hS W)) (h₂ h₃)
    (U : Space.SpacesEtale B S hS W)
    (ζ : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U)
    (r : (bandRing B S hS W).obj (op U)) (a : 𝒢.val.obj (op U)) :
    bandParam hι₁ θ h₁ U ζ (Additive.ofMul (bandSmul hι₁ hne hlc 𝒢 θ h₁ h₂ h₃ U r a)) =
      bandParam hι₁ θ h₁ U ζ (Additive.ofMul a) ≫ frameMul hι₁ ζ r := by
  have h := bandFrame_bandSmul hι₁ hne hlc 𝒢 θ h₁ h₂ h₃ U U (𝟙 U) ζ r a
  simp only [op_id, CategoryTheory.Functor.map_id] at h
  rw [bandParam_apply, bandParam_apply]
  show paramOf hι₁ (Functor.bandFrame θ U ζ (bandSmul hι₁ hne hlc 𝒢 θ h₁ h₂ h₃ U r a)) = _
  rw [show Functor.bandFrame θ U ζ (bandSmul hι₁ hne hlc 𝒢 θ h₁ h₂ h₃ U r a) =
      frameSmul hι₁ ζ r (Functor.bandFrame θ U ζ a) from h, paramOf_frameSmul]
  rfl

end AlgebraicGeometry.Stack.EtaleSmoothLift
