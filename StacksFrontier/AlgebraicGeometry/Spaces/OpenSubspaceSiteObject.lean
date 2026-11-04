module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Glueing.SchemeSizeBounds
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceSiteFactorization

/-!
# An open subspace of a representable algebraic space is a scheme of the site

Let `U₀` be a scheme of the big fppf site of `S`, let `r : yoneda.obj U₀ ≅ U` present an
algebraic space `U` over `S` as the functor of points of `U₀`, and let `V ⊆ U` be an open
subspace in the sense of **Stacks 02YU**, part (2). This file assembles, in one statement, the
four things a chart construction needs of `V`: that `V` is the functor of points of an object
`V₀` of the site, through a comparison isomorphism `yoneda.obj V₀ ≅ V.toFunctor`; that the
morphism `v : V₀ ⟶ U₀` realizing the inclusion is a monomorphism of the site, with open
immersion of schemes underlying it; that the comparison isomorphism is compatible with the
inclusion `V.ι`; and that the size of the representing scheme is bounded by `2 ^ 2 ^ size U₀`.

The bound is the one a family of such subspaces has to satisfy for its coproduct to lie in the
site, `AlgebraicGeometry.BigFppfSite.contains_sigma_of_forall_size_le` asking for a bound uniform
in the index, and it is the same `2 ^ 2 ^ size U₀` as in
`AlgebraicGeometry.Stack.exists_siteObject_toScheme_map_eq_size_le`.

## Main results

* `AlgebraicGeometry.Space.exists_siteObject_iso_mono_of_isOpenSubspace`: the four clauses
  above.

## Implementation notes

The representability and the comparison isomorphism come from base-changing the inclusion
`V.ι` along `r`, as in `AlgebraicGeometry.Space.exists_isOpenImmersion_iso_of_isOpenImmersion_ι`
(which does it along the identity): an open immersion of algebraic spaces is by definition
representable by open immersions of schemes, so the base change along a morphism out of a
representable is a scheme of the site, and along an *isomorphism* the first projection is itself
an isomorphism, which is the comparison. Only the open-immersion half of
`AlgebraicGeometry.Space.IsOpenSubspace` is used; the algebraicity half is not needed, the
subspace being representable a posteriori.

Monomorphy is read on the underlying morphism of schemes and pulled back: an open immersion of
schemes is a monomorphism by `AlgebraicGeometry.IsOpenImmersion.le_monomorphisms`, and
`AlgebraicGeometry.BigFppfOver.toScheme` is faithful, so `v` is a monomorphism of the site. That
monomorphism of schemes is exactly what the size bound
`AlgebraicGeometry.size_le_of_mono_double_power` consumes — no finiteness hypothesis on `v` is
available or needed — and it is also exactly the input of
`AlgebraicGeometry.Stack.exists_siteObject_toScheme_map_eq_size_le`, which this statement
therefore makes unnecessary for an open subspace: the object of the site is produced here
directly, rather than recovered from the monomorphism.

No declaration here carries a Stacks attribute. **Stacks 02YU**, part (2) is the definition of an
open subspace and already sits on `AlgebraicGeometry.Space.IsOpenSubspace`; what is proved here
is the unlabelled consequence of that definition for a representable ambient space, together
with the size estimate, which is not part of any source statement.

## References

* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An open subspace of a representable algebraic space is representable by a scheme of the
site, by a monomorphism into the representing chart and of bounded size.** Let `r : yoneda.obj
U₀ ≅ U` present `U` as the functor of points of a scheme `U₀` of the big fppf site of `S`, and
let `V ⊆ U` be an open subspace in the sense of **Stacks 02YU**, part (2). Then there are an
object `V₀` of the site, a morphism `v : V₀ ⟶ U₀` of the site and an isomorphism
`e : yoneda.obj V₀ ≅ V.toFunctor` such that the morphism of schemes underlying `v` is an open
immersion, `v` is a monomorphism, `e` carries `V.ι` to `v` read through `r`, and
`size V₀ ≤ 2 ^ 2 ^ size U₀`.

See the module documentation. -/
theorem exists_siteObject_iso_mono_of_isOpenSubspace {U₀ : BigFppfOver B S hS}
    {U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (r : yoneda.obj U₀ ≅ U) {V : Subfunctor U}
    (hV : IsOpenSubspace B S hS V) :
    ∃ (V₀ : BigFppfOver B S hS) (v : V₀ ⟶ U₀) (e : yoneda.obj V₀ ≅ V.toFunctor),
      _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map v) ∧
        Mono v ∧ e.hom ≫ V.ι = yoneda.map v ≫ r.hom ∧
          ((BigFppfOver.toScheme B S hS).obj V₀).size ≤
            (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^
              ((BigFppfOver.toScheme B S hS).obj U₀).size := by
  -- base-change the inclusion `V.ι`, which is representable by open immersions, along `r`
  have hpb := hV.2.rep.isPullback r.hom
  have _ : IsIso (hV.2.rep.fst r.hom) := hpb.isIso_fst_of_isIso
  obtain ⟨V₀, v, hv, e, he⟩ : ∃ (V₀ : BigFppfOver B S hS) (v : V₀ ⟶ U₀),
      _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map v) ∧
        ∃ e : yoneda.obj V₀ ≅ V.toFunctor, e.hom ≫ V.ι = yoneda.map v ≫ r.hom :=
    ⟨hV.2.rep.pullback r.hom, hV.2.rep.snd r.hom, hV.2.property_snd r.hom,
      asIso (hV.2.rep.fst r.hom), hpb.w⟩
  have hmono : Mono ((BigFppfOver.toScheme B S hS).map v) :=
    _root_.AlgebraicGeometry.IsOpenImmersion.le_monomorphisms _ hv
  exact ⟨V₀, v, e, hv, (BigFppfOver.toScheme B S hS).mono_of_mono_map hmono, he,
    size_le_of_mono_double_power ((BigFppfOver.toScheme B S hS).map v)⟩

end AlgebraicGeometry.Space

end
