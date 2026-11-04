module

public import StacksFrontier.CategoryTheory.FiberedCategory.BasedFunctorWhiskering

/-!
# Postcomposition with a fully faithful based functor

Let `𝒮` be a category and `F : 𝒴 ⥤ᵇ 𝒵` a functor of categories over `𝒮` whose underlying
functor is fully faithful. Then for every category `𝒳` over `𝒮`, postcomposition with `F` is a
fully faithful functor from the category of functors over `𝒮` from `𝒳` to `𝒴` to that from `𝒳`
to `𝒵`: a morphism of functors over `𝒮` between two composites with `F` has components lying
over identities, and their preimages along `F` lie over identities as well.

This is how the category of morphisms from a category over `𝒮` into a full subcategory of a
category over `𝒮` — for instance the families of curves inside the finitely presented, flat and
proper families of algebraic spaces — is a full subcategory of the category of morphisms into the
ambient category.

## Main definitions

* `CategoryTheory.BasedFunctor.postcompFullyFaithful`: postcomposition with a fully faithful
  based functor is fully faithful.
-/

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] (𝒳 : BasedCategory.{v₂, u₂} 𝒮)
  {𝒴 : BasedCategory.{v₃, u₃} 𝒮} {𝒵 : BasedCategory.{v₄, u₄} 𝒮}

namespace BasedFunctor

/-- An arrow of `𝒴` whose image under a based functor lies over an identity lies over that
identity. -/
theorem isHomLift_id_of_map_eq (F : 𝒴 ⥤ᵇ 𝒵) {a b : 𝒴.obj} {S : 𝒮} {m : a ⟶ b}
    {n : F.obj a ⟶ F.obj b} (h : F.map m = n) (hn : 𝒵.p.IsHomLift (𝟙 S) n) :
    𝒴.p.IsHomLift (𝟙 S) m := by
  subst h
  exact isHomLift_map F _ _

/-- **Postcomposition with a fully faithful based functor is fully faithful.** -/
def postcompFullyFaithful (F : 𝒴 ⥤ᵇ 𝒵) (hF : F.toFunctor.FullyFaithful) :
    (postcompFunctor 𝒳 F).FullyFaithful where
  preimage {g h} θ :=
    { toNatTrans := (hF.whiskeringRight 𝒳.obj).preimage
        (θ.toNatTrans : g.toFunctor ⋙ F.toFunctor ⟶ h.toFunctor ⋙ F.toFunctor)
      isHomLift' := fun a =>
        isHomLift_id_of_map_eq F
          (n := (θ.toNatTrans : g.toFunctor ⋙ F.toFunctor ⟶ h.toFunctor ⋙ F.toFunctor).app a)
          (congrArg (fun k => NatTrans.app k a) ((hF.whiskeringRight 𝒳.obj).map_preimage
            (θ.toNatTrans : g.toFunctor ⋙ F.toFunctor ⟶ h.toFunctor ⋙ F.toFunctor)))
          (θ.isHomLift' a) }
  map_preimage {g h} θ := by
    refine BasedNatTrans.ext _ _ ?_
    exact (hF.whiskeringRight 𝒳.obj).map_preimage
      (θ.toNatTrans : g.toFunctor ⋙ F.toFunctor ⟶ h.toFunctor ⋙ F.toFunctor)
  preimage_map {g h} θ := by
    refine BasedNatTrans.ext _ _ ?_
    exact (hF.whiskeringRight 𝒳.obj).preimage_map θ.toNatTrans

/-- Postcomposition with a fully faithful based functor is full. -/
theorem full_postcompFunctor (F : 𝒴 ⥤ᵇ 𝒵) (hF : F.toFunctor.FullyFaithful) :
    (postcompFunctor 𝒳 F).Full :=
  (postcompFullyFaithful 𝒳 F hF).full

/-- Postcomposition with a fully faithful based functor is faithful. -/
theorem faithful_postcompFunctor (F : 𝒴 ⥤ᵇ 𝒵) (hF : F.toFunctor.FullyFaithful) :
    (postcompFunctor 𝒳 F).Faithful :=
  (postcompFullyFaithful 𝒳 F hF).faithful

end BasedFunctor

end CategoryTheory

end
