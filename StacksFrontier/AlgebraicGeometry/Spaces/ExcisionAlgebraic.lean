module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCoverFamilyImage
public import StacksFrontier.AlgebraicGeometry.Spaces.ExcisionLegsEtale

/-!
# Algebraicity of a presheaf covered by the excision legs

Let `f : V ⟶ W` be a separated étale morphism of algebraic spaces over `S` and let `T ⊂ W` be a
closed subspace along which `f` is an isomorphism. A presheaf `X` over `W` is covered by two legs:
the part of `X` over the open complement `W⁰` of `T`, and the fibre product `X ×_W V`. This file
shows that an fppf sheaf `X` over `W` is an algebraic space as soon as those two legs are, a step
in the proof of [Stacks, Tag 0BGY].

## Main results

* `AlgebraicGeometry.Space.isAlgebraicSpace_of_excisionBaseSource`: an fppf sheaf `X` over `W`
  whose two excision legs have algebraic sources is an algebraic space.

## References

* [Stacks Project, Tag 0BGR](https://stacks.math.columbia.edu/tag/0BGR)
* [Stacks Project, Tag 0BGY](https://stacks.math.columbia.edu/tag/0BGY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {V W : AlgebraicSpaces B S hS}

/-- **A presheaf over `W` whose two excision legs are algebraic is an algebraic space.**

Let `f : V ⟶ W` be a separated étale morphism of algebraic spaces over `S`, let `T` be a
closed subspace of `W` with `f⁻¹T ≅ T`, and let `X` be an fppf sheaf with a morphism
`g : X ⟶ W`. If the part of `X` lying over the open complement of `T` and the fibre product
`X ×_W V` are both algebraic spaces over `S`, then so is `X`. The coproduct `G` of the two legs
is given as a sheaf with a colimit cofan. -/
theorem isAlgebraicSpace_of_excisionBaseSource (f : V ⟶ W) (hf : IsEtale B S hS f.hom)
    (hsep : IsSeparated B S hS f.hom) (T : Subfunctor W.obj)
    (hT : IsClosedSubspace B S hS T) (hfT : IsIso (T.fromPreimage f.hom))
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X) (g : X ⟶ W.obj)
    (hsrc : ∀ b, IsAlgebraicSpace B S hS (excisionBaseSource B S hS f T g b))
    (G : Sheaf (BigFppfOver.topology B S hS) (Type u))
    (ι : ∀ b, (⟨excisionBaseSource B S hS f T g b, (hsrc b).isSheaf⟩ :
      Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶ G)
    (hcoprod : IsColimit (Cofan.mk G ι)) :
    IsAlgebraicSpace B S hS X := by
  classical
  let Xs : Sheaf (BigFppfOver.topology B S hS) (Type u) := ⟨X, hX⟩
  let fam : Cofan (fun b => (⟨excisionBaseSource B S hS f T g b, (hsrc b).isSheaf⟩ :
      Sheaf (BigFppfOver.topology B S hS) (Type u))) :=
    Cofan.mk Xs fun b => ⟨excisionBaseMap B S hS f T g b⟩
  have hfac : ∀ b, (ι b).hom ≫ (hcoprod.desc fam).hom = excisionBaseMap B S hS f T g b :=
    fun b => by
      simpa [fam, Cofan.mk_ι_app] using
        congrArg (fun φ : _ ⟶ Xs => φ.hom) (hcoprod.fac fam ⟨b⟩)
  refine isAlgebraicSpace_of_etale_familyImage_cover B S hS hX hsrc ι hcoprod
    (hcoprod.desc fam).hom (fun b => ?_) (fun Z x => ?_)
  · rw [hfac b]
    exact presheafEtale_excisionBaseMap B S hS f hf hsep T hT g b
  · rw [funext hfac]
    exact familyImage_excisionBaseMap_sieveOfSection_mem B S hS f T hT hfT hf g Z x

end AlgebraicGeometry.Space

end
