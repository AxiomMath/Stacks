module

public import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes
public import StacksFrontier.CategoryTheory.Sites.Localization.Relocalize

/-!
# Relocalizing a restriction is a product with a representable presheaf

Let `f : V ⟶ U` be a morphism of a category `C` and let `j = Over.map f : C/V ⥤ C/U` be the
associated localization functor. For a presheaf `F` on `C/U`, relocalizing its restriction
`j^{-1} F` back along `f` gives the product of `F` with the representable presheaf of the object
`V →f U` of `C/U`:

```
  Λ_f (j^{-1} F)  ≅  h_{(V ⟶ U)} ⨯ F .
```

Concretely a section of the left-hand side over `W : C/U` is a factorization `ψ : W.left ⟶ V` of
the structure morphism of `W` together with a section of `F` over `W.left →ψ ≫ f U`; the
factorization *is* a morphism `W ⟶ (V →f U)` of `C/U`, and restricting the section along the
resulting isomorphism `(W.left →ψ ≫ f U) ≅ W` makes it a section of `F` over `W`.

## Main definitions

* `CategoryTheory.OverShriek.relocalizeRestrictIsoProduct`: the isomorphism above.

## Implementation notes

The isomorphism is built pointwise as an equivalence of types and then assembled with
`CategoryTheory.NatIso.ofComponents`; the two round trips and naturality all reduce to
restricting one section of `F` along two morphisms with the same underlying morphism of `C`.

`CategoryTheory.OverShriek.isPullback_relocalizeRestrictMap` is the same phenomenon in the
relative form `Λ_{m ≫ a}(F|_{C/A'}) = Λ_a F ×_{h_a} h_{m ≫ a}`, and the isomorphism here is its
special case `a = 𝟙 U`. It is proved directly rather than deduced from it, because specializing
would require identifying `Λ_{𝟙 U} F` with `F`, `h_{(U →𝟙 U)}` with a terminal presheaf and a
fibre product over a terminal object with a product, and transporting along `f ≫ 𝟙 U = f`; the
direct description of a section of a relocalization is shorter than that chain.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.OverShriek

universe v u

variable {C : Type u} [Category.{v} C] {U V : C} (f : V ⟶ U)

/-- A morphism `α : W ⟶ (V →f U)` of `C/U` identifies `W` with the object `V →α.left ≫ f U`
of `C/U`. -/
def overMkIsoOfFactorization {W : Over U} (α : W ⟶ Over.mk f) :
    Over.mk (α.left ≫ f) ≅ W :=
  Over.isoMk (Iso.refl _) (by simpa using (Over.w α).symm)

/-- **Relocalizing a restriction is a product.** For a presheaf `F` on `C/U`, the relocalization
along `f : V ⟶ U` of the restriction of `F` to `C/V` is the product of `F` with the representable
presheaf of the object `V →f U` of `C/U`. -/
noncomputable def relocalizeRestrictIsoProduct (F : (Over U)ᵒᵖ ⥤ Type v) :
    (relocalizePresheafFunctor f).obj ((relocalizeRestrict f).obj F) ≅
      yoneda.obj (Over.mk f) ⨯ F := by
  let H := yoneda.obj (Over.mk f)
  let P := FunctorToTypes.prod H F
  let e : (relocalizePresheafFunctor f).obj ((relocalizeRestrict f).obj F) ≅ P := by
    refine NatIso.ofComponents (fun W => ?_) ?_
    · refine Equiv.toIso ?_
      refine Equiv.mk
        (fun p =>
          let ψ := p.val.1
          let s : F.obj (op (Over.mk (ψ ≫ f))) := p.val.2
          have hψ : ψ ≫ f = W.unop.hom := p.property
          let α : W.unop ⟶ Over.mk f := Over.homMk ψ hψ
          (α, F.map (overMkIsoOfFactorization f α).inv.op s))
        (fun p =>
          ⟨⟨p.1.left, F.map (overMkIsoOfFactorization f p.1).hom.op p.2⟩, Over.w p.1⟩)
        ?_ ?_
      · rintro ⟨⟨ψ, s⟩, hψ⟩
        change ψ ≫ f = W.unop.hom at hψ
        change F.obj (op (Over.mk (ψ ≫ f))) at s
        apply Subtype.ext
        refine Sigma.ext rfl ?_
        dsimp
        exact heq_of_eq (F.map_inv_hom'_apply (overMkIsoOfFactorization f (Over.homMk ψ hψ)).op s)
      · rintro ⟨α, s⟩
        refine Prod.ext (Over.OverMorphism.ext rfl) ?_
        exact F.map_inv_hom'_apply (overMkIsoOfFactorization f α).symm.op s
    · intro W W' g
      ext x
      · exact Over.OverMorphism.ext rfl
      · rcases x with ⟨⟨ψ, s⟩, hψ⟩
        change ψ ≫ f = W.unop.hom at hψ
        let β : W'.unop ⟶ W.unop := g.unop
        let α : W.unop ⟶ Over.mk f := Over.homMk ψ hψ
        let t : Over.mk (β.left ≫ ψ) ⟶ Over.mk ψ := Over.homMk β.left rfl
        let k : Over.mk (ψ ≫ f) ≅ W.unop := overMkIsoOfFactorization f α
        let k' : Over.mk ((β.left ≫ ψ) ≫ f) ≅ W'.unop := overMkIsoOfFactorization f (β ≫ α)
        change F.map k'.inv.op (F.map ((Over.map f).map t).op s) = F.map β.op (F.map k.inv.op s)
        rw [← F.map_comp_apply, ← op_comp, ← F.map_comp_apply, ← op_comp]
        have hcomp : k'.inv ≫ (Over.map f).map t = β ≫ k.inv :=
          Over.OverMorphism.ext (by simp [k, k', t, overMkIsoOfFactorization])
        rw [hcomp]
  exact e ≪≫ (FunctorToTypes.binaryProductIso H F).symm

end CategoryTheory.OverShriek

end
