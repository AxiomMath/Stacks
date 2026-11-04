module

public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.SimplicialSheafEquivalence

/-!
# Local surjectivity and local injectivity on `D × C` are the levelwise conditions

Let `(C, J)` be a site, let `D` be a category and let `D × C` carry the topology it inherits
from `(C, J)` along the second projection, which is the topology of Stacks 09D0 when `D = Δ`.
`CategoryTheory.Presheaf.isSheaf_inheritedTopology_prodSnd` says that being a sheaf there is the
levelwise condition. This file proves the same for the two halves of local bijectivity: a
morphism of presheaves on `D × C` is locally surjective, resp. locally injective, as soon as each
of its restrictions to a slice `{d} × C` is.

## Main results

* `CategoryTheory.Presheaf.isLocallySurjective_inheritedTopology_prodSnd`
* `CategoryTheory.Presheaf.isLocallyInjective_inheritedTopology_prodSnd`

## Implementation notes

Both are the same two-line argument. The sieve the levelwise hypothesis produces is a sieve on
`X.2` in `C`; its preimage under the second projection is a covering sieve of `X` for the
inherited topology (`CategoryTheory.Prod.functorPullback_snd_mem_inheritedTopology`), and it is
contained in the sieve the conclusion asks to be covering, because every arrow `g` of `D × C`
into `X` factors as

`(g.1, 𝟙) ≫ (𝟙, g.2)`

and both the image sieve and the equalizer sieve are stable under the restriction along the
first factor.

## References

* [Stacks Project, Tag 09D0](https://stacks.math.columbia.edu/tag/09D0), where the simplicial
  site and this topology are introduced.
* [Stacks Project, Tag 06NV](https://stacks.math.columbia.edu/tag/06NV), the inherited topology.
-/

@[expose] public section

open CategoryTheory Opposite

namespace CategoryTheory

universe w₁ v₁ u₁ v₂ u₂ v₃ u₃

section ProductSite

variable {D : Type u₁} [Category.{v₁} D] {C : Type u₂} [Category.{v₂} C]
  {A : Type u₃} [Category.{v₃} A] {FA : A → A → Type*} {CA : A → Type w₁}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w₁} A FA]
  (J : GrothendieckTopology C)

/-- The factorisation of an arrow of `D × C` through the two coordinate sections. -/
theorem Prod.prodSectionFst_map_comp_prodSectionSnd_map {X Y : D × C} (g : Y ⟶ X) :
    (Functor.prodSectionFst Y.2).map g.1 ≫ (Functor.prodSectionSnd X.1).map g.2 = g :=
  Prod.ext (Category.comp_id g.1) (Category.id_comp g.2)

/-- **Local surjectivity on `D × C` is the levelwise condition.** A morphism of presheaves on
`D × C` each of whose restrictions to a slice `{d} × C` is locally surjective for `J` is locally
surjective for the topology inherited along the second projection. -/
theorem Presheaf.isLocallySurjective_inheritedTopology_prodSnd {P Q : (D × C)ᵒᵖ ⥤ A} (φ : P ⟶ Q)
    (h : ∀ d : D, Presheaf.IsLocallySurjective J
      (Functor.whiskerLeft (Functor.prodSectionSnd (C := C) d).op φ)) :
    Presheaf.IsLocallySurjective ((Prod.snd D C).inheritedTopology J) φ where
  imageSieve_mem {X} s := by
    obtain ⟨d, U⟩ := X
    refine ((Prod.snd D C).inheritedTopology J).superset_covering ?_
      (Prod.functorPullback_snd_mem_inheritedTopology J d
        (Presheaf.imageSieve_mem J
          (Functor.whiskerLeft (Functor.prodSectionSnd (C := C) d).op φ)
          (U := op U) s))
    intro Y g hg
    obtain ⟨e, V⟩ := Y
    obtain ⟨t, ht⟩ := hg
    refine ⟨P.map (CategoryTheory.Prod.mkHom g.1 (𝟙 V) :
      ((e, V) : D × C) ⟶ ((d, V) : D × C)).op t, ?_⟩
    have h2 : ConcreteCategory.hom (φ.app (op ((d, V) : D × C))) t
        = ConcreteCategory.hom (Q.map (CategoryTheory.Prod.mkHom (𝟙 d) g.2 :
            ((d, V) : D × C) ⟶ ((d, U) : D × C)).op) s := ht
    have key : ∀ u : ((e, V) : D × C) ⟶ ((d, U) : D × C),
        (CategoryTheory.Prod.mkHom g.1 (𝟙 V) : ((e, V) : D × C) ⟶ ((d, V) : D × C)) ≫
            (CategoryTheory.Prod.mkHom (𝟙 d) g.2 :
              ((d, V) : D × C) ⟶ ((d, U) : D × C)) = u →
        ConcreteCategory.hom (φ.app (op ((e, V) : D × C)))
            (ConcreteCategory.hom (P.map (CategoryTheory.Prod.mkHom g.1 (𝟙 V) :
              ((e, V) : D × C) ⟶ ((d, V) : D × C)).op) t)
          = ConcreteCategory.hom (Q.map u.op) s := by
      rintro u rfl
      rw [op_comp, Functor.map_comp_apply Q, ← h2]
      exact NatTrans.naturality_apply φ _ t
    exact key g (Prod.prodSectionFst_map_comp_prodSectionSnd_map g)

/-- **Local injectivity on `D × C` is the levelwise condition.** -/
theorem Presheaf.isLocallyInjective_inheritedTopology_prodSnd {P Q : (D × C)ᵒᵖ ⥤ A} (φ : P ⟶ Q)
    (h : ∀ d : D, Presheaf.IsLocallyInjective J
      (Functor.whiskerLeft (Functor.prodSectionSnd (C := C) d).op φ)) :
    Presheaf.IsLocallyInjective ((Prod.snd D C).inheritedTopology J) φ where
  equalizerSieve_mem {X} x y hxy := by
    obtain ⟨⟨d, U⟩⟩ := X
    refine ((Prod.snd D C).inheritedTopology J).superset_covering ?_
      (Prod.functorPullback_snd_mem_inheritedTopology J d
        (Presheaf.equalizerSieve_mem J
          (Functor.whiskerLeft (Functor.prodSectionSnd (C := C) d).op φ)
          (X := op U) x y hxy))
    intro Y g hg
    obtain ⟨e, V⟩ := Y
    have hfac : (CategoryTheory.Prod.mkHom g.1 (𝟙 V) :
          ((e, V) : D × C) ⟶ ((d, V) : D × C)) ≫
        (CategoryTheory.Prod.mkHom (𝟙 d) g.2 : ((d, V) : D × C) ⟶ ((d, U) : D × C)) = g :=
      Prod.prodSectionFst_map_comp_prodSectionSnd_map g
    have hx : ConcreteCategory.hom (P.map (CategoryTheory.Prod.mkHom (𝟙 d) g.2 :
            ((d, V) : D × C) ⟶ ((d, U) : D × C)).op) x
        = ConcreteCategory.hom (P.map (CategoryTheory.Prod.mkHom (𝟙 d) g.2 :
            ((d, V) : D × C) ⟶ ((d, U) : D × C)).op) y := hg
    change ConcreteCategory.hom (P.map g.op) x = ConcreteCategory.hom (P.map g.op) y
    rw [← hfac, op_comp, Functor.map_comp_apply P, Functor.map_comp_apply P, hx]

end ProductSite

end CategoryTheory

end
