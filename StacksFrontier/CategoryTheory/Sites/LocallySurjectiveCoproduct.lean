module

public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Local surjectivity of a map out of a coproduct

A family of maps `f i : A i ⟶ F` of presheaves is jointly locally surjective — that is,
`Sigma.desc f` is locally surjective — as soon as it is dominated by a family which is known to
be jointly locally surjective: if `u i : B i ⟶ P` is jointly locally surjective, `h : P ⟶ F` is
locally surjective, and each `u i ≫ h` factors through `f i`, then `Sigma.desc f` is locally
surjective.

This is the shape in which joint local surjectivity is usually available. One has a single
locally surjective map `h : P ⟶ F` onto the target, and a covering of `P` by objects `B i`
mapping to the charts `A i`; the conclusion is that the charts cover `F`.

A jointly locally surjective family of morphisms of sheaves may also be *refined*: replacing
each `A i` by a sheaf mapping onto it locally surjectively keeps the family jointly locally
surjective, because the map which a family of locally surjective morphisms of sheaves induces
on the coproducts is itself locally surjective.

## Main results

* `CategoryTheory.Presheaf.isLocallySurjective_sigmaDesc_of_fac`: joint local surjectivity
  transported along a dominating family.
* `CategoryTheory.Sheaf.isLocallySurjective_sigmaMap`: a coproduct of locally surjective
  morphisms of sheaves of types is locally surjective.

## Implementation notes

The proof of the first is the factorization `Sigma.map v ≫ Sigma.desc f = Sigma.desc u ≫ h`,
checked on each component of the coproduct, together with
`CategoryTheory.Presheaf.isLocallySurjective_of_isLocallySurjective_fac`: the right-hand side is
a composite of locally surjective maps, so the second factor of the left-hand side is locally
surjective.

The coproduct maps must be written `CategoryTheory.Limits.Sigma.map`, since under
`open CategoryTheory.Limits` the bare name resolves to the map of dependent pairs.

Local surjectivity of `Sigma.map` is proved on the sheaf side rather than the presheaf side,
where the coproduct is a sheafification and nothing can be read off its sections: for sheaves of
types local surjectivity is the same as being an epimorphism
(`CategoryTheory.Sheaf.isLocallySurjective_iff_epi`), and a coproduct of epimorphisms is an
epimorphism (`CategoryTheory.Limits.Sigma.map_epi`).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace CategoryTheory.Presheaf

/-- **Joint local surjectivity is inherited from a dominating family.** Let `f i : A i ⟶ F` be a
family of maps of presheaves of types, let `h : P ⟶ F` be locally surjective, and let
`u i : B i ⟶ P` be a family whose induced map out of the coproduct is locally surjective. If
each `u i ≫ h` factors through `f i` by a map `v i : B i ⟶ A i`, then the map out of the
coproduct induced by `f` is locally surjective. -/
theorem isLocallySurjective_sigmaDesc_of_fac {C : Type v} [Category.{w} C]
    (J : GrothendieckTopology C) {I : Type*} {A Bi : I → Cᵒᵖ ⥤ Type u} {P F : Cᵒᵖ ⥤ Type u}
    [HasCoproduct A] [HasCoproduct Bi]
    (f : ∀ i, A i ⟶ F) (u : ∀ i, Bi i ⟶ P) (v : ∀ i, Bi i ⟶ A i) (h : P ⟶ F)
    (hu : Presheaf.IsLocallySurjective J (Sigma.desc u))
    (hh : Presheaf.IsLocallySurjective J h)
    (hfac : ∀ i, v i ≫ f i = u i ≫ h) :
    Presheaf.IsLocallySurjective J (Sigma.desc f) := by
  have _ := hu
  have _ := hh
  have key : Limits.Sigma.map v ≫ Sigma.desc f = Sigma.desc u ≫ h := by
    refine Limits.Sigma.hom_ext _ _ fun i => ?_
    rw [← Category.assoc, Limits.Sigma.ι_map, Category.assoc, Limits.Sigma.ι_desc,
      ← Category.assoc, Limits.Sigma.ι_desc]
    exact hfac i
  exact Presheaf.isLocallySurjective_of_isLocallySurjective_fac J (f₃ := Sigma.desc u ≫ h) key

end CategoryTheory.Presheaf

namespace CategoryTheory.Sheaf

variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C} [HasSheafify J (Type u)]
  {I : Type*} {A Bi : I → Sheaf J (Type u)} [HasCoproduct A] [HasCoproduct Bi]

/-- **A coproduct of locally surjective morphisms of sheaves of types is locally surjective.**
If `f i : A i ⟶ B i` is locally surjective for every `i`, then so is the induced morphism
`∐ A ⟶ ∐ B` of coproducts.

For sheaves of types local surjectivity is epimorphy, and a coproduct of epimorphisms is an
epimorphism. -/
theorem isLocallySurjective_sigmaMap (f : ∀ i, A i ⟶ Bi i)
    (hf : ∀ i, IsLocallySurjective (f i)) :
    IsLocallySurjective (Limits.Sigma.map f) := by
  have : ∀ i, Epi (f i) := fun i => (isLocallySurjective_iff_epi (f i)).1 (hf i)
  exact (isLocallySurjective_iff_epi _).2 inferInstance

end CategoryTheory.Sheaf

end
