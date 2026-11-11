module

public import StacksFrontier.CategoryTheory.Sites.Gerbe.Equivalence
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.StackAlongFullyFaithful

/-! # Gerbes over a site are invariant under equivalence over the base (Stacks 06P0)

Stacks 06P0: two categories over a site `(𝒞, J)` which are equivalent as categories over `𝒞` are
gerbes over `(𝒞, J)` (`CategoryTheory.Functor.IsGerbe`, Stacks 06NZ) at the same time. Equivalence
over `𝒞` is `CategoryTheory.Functor.IsEquivalenceOver` together with the 1-morphism condition
`a ⋙ p' = p`, as in `StacksFrontier/CategoryTheory/Sites/Gerbe/Equivalence.lean`.

As in the source proof, the stack-in-groupoids clause is transported by Stacks 042X, here for the
rendering `CategoryTheory.Functor.IsStackInGroupoids` (Stacks 02ZI) of "stack in groupoids", and
local nonemptiness and local connectedness by `CategoryTheory.isGerbeOver_iff_of_isEquivalenceOver`
read through `CategoryTheory.isGerbeOver_id_iff`.

## Main results

* `CategoryTheory.Functor.IsStackInGroupoids.of_isEquivalenceOver` and
  `CategoryTheory.Functor.IsStackInGroupoids.iff_of_isEquivalenceOver`: being a stack in groupoids
  transports along an equivalence over `𝒞`.
* `CategoryTheory.Functor.isGerbe_iff_of_isEquivalenceOver`: **Stacks 06P0**.
-/

@[expose] public section

namespace CategoryTheory

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace Functor

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {𝒳' : Type u₃} [Category.{v₃} 𝒳'] {p : 𝒳 ⥤ 𝒞} {r : 𝒳' ⥤ 𝒞} {a : 𝒳 ⥤ 𝒳'}

/-- Being a stack in groupoids (`CategoryTheory.Functor.IsStackInGroupoids`, Stacks 02ZI)
transports along an equivalence over `𝒞`: if `a : 𝒳 ⥤ 𝒳'` is a 1-morphism over `𝒞` which is an
equivalence over `𝒞` and `p` is a stack in groupoids, then so is `r`.

The quasi-inverse `e.inv` is fully faithful, strictly over `𝒞`, and every object of `𝒳` is
isomorphic over an identity to one in its image by the unit, so
`CategoryTheory.Functor.IsStackInGroupoids.comp_of_full_of_faithful` applies to it. -/
theorem IsStackInGroupoids.of_isEquivalenceOver {J : GrothendieckTopology 𝒞} (ha : a ⋙ r = p)
    (e : IsEquivalenceOver p r a) (h : p.IsStackInGroupoids.{w} J) :
    r.IsStackInGroupoids.{w} J := by
  have hr := IsFiberedInGroupoids.of_isEquivalenceOver ha e h.isFiberedInGroupoids
  obtain ⟨b, hb, unitIso, counitIso, hu, -⟩ := e
  subst hb
  have := Full.of_quasiInverse unitIso counitIso
  have := Faithful.of_quasiInverse unitIso counitIso
  exact h.comp_of_full_of_faithful b (fun x => ⟨a.obj x, unitIso.app x, hu x⟩) hr

/-- Two categories over a site `(𝒞, J)` which are equivalent as categories over `𝒞` are stacks
in groupoids (`CategoryTheory.Functor.IsStackInGroupoids`, Stacks 02ZI) at the same time. This is
Stacks 042X for that rendering of "stack in groupoids"; the rendering through
`CategoryTheory.Functor.IsStack` is
`CategoryTheory.BasedCategory.isFiberedInGroupoids_and_isStack_iff_of_equivalence`. -/
theorem IsStackInGroupoids.iff_of_isEquivalenceOver {J : GrothendieckTopology 𝒞}
    (ha : a ⋙ r = p) (e : IsEquivalenceOver p r a) :
    p.IsStackInGroupoids.{w} J ↔ r.IsStackInGroupoids.{w} J :=
  ⟨of_isEquivalenceOver ha e, of_isEquivalenceOver e.inv_over (e.symm ha)⟩

end Functor

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {𝒳' : Type u₃} [Category.{v₃} 𝒳']

/-- **Stacks 06P0.** Let `(𝒞, J)` be a site and let `p : 𝒳 ⥤ 𝒞`, `p' : 𝒳' ⥤ 𝒞` be categories
over `𝒞` which are equivalent as categories over `𝒞`: `a : 𝒳 ⥤ 𝒳'` is a 1-morphism over `𝒞`
(`a ⋙ p' = p`) and an equivalence over `𝒞` (its quasi-inverse is strictly over `𝒞` and unit and
counit are vertical). Then `𝒳` is a gerbe over `(𝒞, J)` (`CategoryTheory.Functor.IsGerbe`,
Stacks 06NZ) if and only if `𝒳'` is.

As in the source, the stack clause is Stacks 042X,
`CategoryTheory.Functor.IsStackInGroupoids.iff_of_isEquivalenceOver`, and local nonemptiness and
local connectedness transport by `isGerbeOver_iff_of_isEquivalenceOver` read through
`isGerbeOver_id_iff`. -/
@[stacks 06P0]
theorem Functor.isGerbe_iff_of_isEquivalenceOver {J : GrothendieckTopology 𝒞} {p : 𝒳 ⥤ 𝒞}
    {p' : 𝒳' ⥤ 𝒞} {a : 𝒳 ⥤ 𝒳'} (ha : a ⋙ p' = p) (e : Functor.IsEquivalenceOver p p' a) :
    p.IsGerbe.{w} J ↔ p'.IsGerbe.{w} J := by
  have key := isGerbeOver_iff_of_isEquivalenceOver (J := J) (q := 𝟭 𝒞) ha e
  rw [isGerbeOver_id_iff, isGerbeOver_id_iff] at key
  constructor
  · rintro ⟨hs, hn, hc⟩
    obtain ⟨-, hn', hc'⟩ := key.1 ⟨hs.isFiberedInGroupoids, hn, hc⟩
    exact ⟨hs.of_isEquivalenceOver ha e, hn', hc'⟩
  · rintro ⟨hs, hn, hc⟩
    obtain ⟨-, hn', hc'⟩ := key.2 ⟨hs.isFiberedInGroupoids, hn, hc⟩
    exact ⟨hs.of_isEquivalenceOver e.inv_over (e.symm ha), hn', hc'⟩

end CategoryTheory
