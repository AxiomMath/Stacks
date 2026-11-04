module

public import Mathlib.CategoryTheory.Galois.GaloisObjects

/-!
# Connected and Galois objects are carried along an equivalence of Galois categories

An equivalence `G : C ⥤ D` of Galois categories carries connected objects to connected objects
and Galois objects to Galois objects.

For connectedness this is formal: an equivalence reflects initial objects, so `G.obj X` is not
initial, and a subobject of `G.obj X` is carried by the inverse to a subobject of `X`, which is
therefore an isomorphism; an equivalence reflects isomorphisms, so the original monomorphism is
one too.

For the Galois condition the fibre-functor criterion
`CategoryTheory.PreGaloisCategory.isGalois_iff_pretransitive` reduces the claim to transitivity
of `Aut (G.obj X)` on a fibre of `G.obj X`. If `F` is a fibre functor on `D`, then `G ⋙ F` is a
fibre functor on `C` — every axiom is a preservation property, and an equivalence preserves and
reflects everything — and `G.obj X`'s fibre under `F` *is* `X`'s fibre under `G ⋙ F`. The group
homomorphism `CategoryTheory.Functor.mapAut` sends an automorphism of `X` to one of `G.obj X`
acting by the same permutation of that fibre, so transitivity of `Aut X` on it, which is the
Galois condition for `X`, gives transitivity of `Aut (G.obj X)`.

## Main results

* `CategoryTheory.PreGaloisCategory.isConnected_obj_of_isEquivalence` — an equivalence carries
  connected objects to connected objects.
* `CategoryTheory.PreGaloisCategory.isGalois_obj_of_isEquivalence` — an equivalence of Galois
  categories carries Galois objects to Galois objects.
-/

@[expose] public section

open CategoryTheory.Limits

universe u₁ u₂ v₁

namespace CategoryTheory.PreGaloisCategory

variable {C : Type u₁} [Category.{u₂, u₁} C] {D : Type v₁} [Category.{u₂, v₁} D]

/-- **An equivalence of categories carries connected objects to connected objects.** An initial
`G.obj X` would make `X` initial, since an equivalence reflects colimits; and a monomorphism
`i : Y ⟶ G.obj X` from a non-initial `Y` becomes, after applying the inverse and the unit
isomorphism, a monomorphism into `X` from a non-initial object, hence an isomorphism — and an
equivalence reflects isomorphisms. -/
theorem isConnected_obj_of_isEquivalence (G : C ⥤ D) [G.IsEquivalence] (X : C)
    [IsConnected X] : IsConnected (G.obj X) where
  notInitial h := IsConnected.notInitial (X := X) (IsInitial.isInitialOfObj G X h)
  noTrivialComponent Y i hmi hY := by
    have : Mono i := hmi
    obtain ⟨ψ⟩ : Nonempty (G.asEquivalence.inverse.obj (G.obj X) ≅ X) :=
      ⟨(G.asEquivalence.unitIso.app X).symm⟩
    have : Mono (G.asEquivalence.inverse.map i) := inferInstance
    have : IsIso (G.asEquivalence.inverse.map i ≫ ψ.hom) :=
      IsConnected.noTrivialComponent _ _ fun hi ↦
        hY (IsInitial.isInitialOfObj G.asEquivalence.inverse Y hi)
    have : IsIso (G.asEquivalence.inverse.map i) := IsIso.of_isIso_comp_right _ ψ.hom
    exact isIso_of_reflects_iso i G.asEquivalence.inverse

/-- **An equivalence of Galois categories carries Galois objects to Galois objects.** Both halves
of the Galois condition are preserved: connectedness by
`CategoryTheory.PreGaloisCategory.isConnected_obj_of_isEquivalence`, and the simple transitivity
of the automorphism group on a fibre because, `F` being a fibre functor on the target, `G ⋙ F` is
a fibre functor on the source with the same fibre, on which `CategoryTheory.Functor.mapAut`
realizes every automorphism of `X` as one of `G.obj X`. -/
theorem isGalois_obj_of_isEquivalence [GaloisCategory C] [GaloisCategory D] (G : C ⥤ D)
    [G.IsEquivalence] (X : C) [IsGalois X] : IsGalois (G.obj X) := by
  have : IsConnected (G.obj X) := isConnected_obj_of_isEquivalence G X
  obtain ⟨F, hF⟩ := GaloisCategory.hasFiberFunctor D
  have := hF
  have : FiberFunctor (G ⋙ F) :=
    { preservesQuotientsByFiniteGroups := fun _ _ _ ↦ inferInstance }
  have hpre : MulAction.IsPretransitive (Aut X) ((G ⋙ F).obj X) :=
    isPretransitive_of_isGalois (G ⋙ F) X
  rw [isGalois_iff_pretransitive F]
  refine ⟨fun x y ↦ ?_⟩
  obtain ⟨σ, hσ⟩ := hpre.exists_smul_eq x y
  exact ⟨G.mapAut X σ, hσ⟩

end CategoryTheory.PreGaloisCategory

end
