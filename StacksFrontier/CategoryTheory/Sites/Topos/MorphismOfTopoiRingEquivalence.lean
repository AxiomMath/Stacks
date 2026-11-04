module

public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoiRing

/-!
# Adjoints of isomorphisms along a morphism of topoi with invertible direct image

Let `f` be a morphism of topoi whose direct image `f_*` on sheaves of sets is an equivalence
(for instance the morphism of small étale topoi of a thickening, Stacks 05ZH). A map
`ψ : 𝒪 ⟶ f_*𝒜` of sheaves of commutative rings which is an isomorphism has an adjoint
`f⁻¹𝒪 ⟶ 𝒜` which is again an isomorphism: on underlying sheaves of sets the adjoint is
`f⁻¹ψ` followed by the counit of `f⁻¹ ⊣ f_*`, which is invertible because `f_*` is fully
faithful, and forgetting the ring structure reflects isomorphisms.

This is how an identification of `𝒪_{X'}` with a direct image `i_*𝒜` along a thickening
`i : X ⟶ X'` becomes an identification `i⁻¹𝒪_{X'} ≅ 𝒜` on the small étale site of `X`, the
form in which Stacks 05ZT states its conclusion.

## Main definitions

* `MorphismOfTopoi.ringAdjunctionIsoOfIso`: the isomorphism `f⁻¹𝒪 ≅ 𝒜` adjoint to an isomorphism
  `𝒪 ≅ f_*𝒜`.

## Main results

* `MorphismOfTopoi.isIso_ringAdjunction_homEquiv_symm`: the adjoint `f⁻¹𝒪 ⟶ 𝒜` of an isomorphism
  `𝒪 ≅ f_*𝒜` of sheaves of rings is an isomorphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w w' v v' u u'

namespace MorphismOfTopoi

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))

/-- **The adjoint of an isomorphism `𝒪 ≅ f_*𝒜` is an isomorphism `f⁻¹𝒪 ≅ 𝒜`** when the direct
image of sheaves of sets along `f` is an equivalence. -/
theorem isIso_ringAdjunction_homEquiv_symm [f.pushforward.IsEquivalence]
    {O : Sheaf K CommRingCat.{w'}} {O' : Sheaf J CommRingCat.{w}}
    (ψ : O ⟶ f.pushforwardRing.obj O') [IsIso ψ] :
    IsIso ((f.ringAdjunction.homEquiv O O').symm ψ) := by
  have h : IsIso ((sheafCompose J (forget CommRingCat.{w})).map
      ((f.ringAdjunction.homEquiv O O').symm ψ)) := by
    rw [ringAdjunction_homEquiv_symm_forget]
    have hcu : IsIso (f.adj.counit.app ((sheafCompose J (forget CommRingCat.{w})).obj O')) :=
      NatIso.isIso_app_of_isIso f.adj.counit _
    have h1 : IsIso ((sheafCompose K (forget CommRingCat.{w'})).map ψ) := Functor.map_isIso _ ψ
    have h2 : IsIso (f.inverseImage.map ((sheafCompose K (forget CommRingCat.{w'})).map ψ)) :=
      Functor.map_isIso _ _
    have hc : IsIso (f.inverseImage.map ((sheafCompose K (forget CommRingCat.{w'})).map ψ) ≫
        f.adj.counit.app ((sheafCompose J (forget CommRingCat.{w})).obj O')) :=
      @IsIso.comp_isIso _ _ _ _ _ _ _ h2 hcu
    exact (Adjunction.homEquiv_counit f.adj _ _ _).symm ▸ hc
  exact isIso_of_reflects_iso _ (sheafCompose J (forget CommRingCat.{w}))

/-- The isomorphism `f⁻¹𝒪 ≅ 𝒜` adjoint to an isomorphism `𝒪 ≅ f_*𝒜`, when the direct image of
sheaves of sets along `f` is an equivalence. -/
noncomputable def ringAdjunctionIsoOfIso [f.pushforward.IsEquivalence]
    {O : Sheaf K CommRingCat.{w'}} {O' : Sheaf J CommRingCat.{w}}
    (e : O ≅ f.pushforwardRing.obj O') : f.inverseImageRing.obj O ≅ O' :=
  @asIso _ _ _ _ ((f.ringAdjunction.homEquiv O O').symm e.hom)
    (isIso_ringAdjunction_homEquiv_symm f e.hom)

/-- The underlying map of `ringAdjunctionIsoOfIso` is the adjoint of `e.hom`. -/
theorem ringAdjunctionIsoOfIso_hom [f.pushforward.IsEquivalence]
    {O : Sheaf K CommRingCat.{w'}} {O' : Sheaf J CommRingCat.{w}}
    (e : O ≅ f.pushforwardRing.obj O') :
    (f.ringAdjunctionIsoOfIso e).hom = (f.ringAdjunction.homEquiv O O').symm e.hom :=
  rfl

end MorphismOfTopoi

end
