module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.BaseChange

/-!
# The finite part of a morphism of algebraic spaces

For a morphism `f : X ⟶ Y` of algebraic spaces over `S`, the *finite part* `(X/Y)_fin` of `f`
is the presheaf on the big fppf site of `S` whose sections over a scheme `T` are the pairs
consisting of a morphism `T ⟶ Y` and an open subspace of `T ×_Y X` finite over `T`, with
restriction along `T' ⟶ T` given by base change of that open subspace. It carries a canonical
projection to `Y`, taking a pair to its morphism to `Y`.

## Main definitions

* `AlgebraicGeometry.Space.FinitePartPresheaf`: the data of a presheaf of types together with
  an identification of its sections with the pairs of Stacks 04PC, a projection to `Y`, and
  the base-change description of its restriction maps.
* `AlgebraicGeometry.Space.finiteOpenSubspacePresheaf`: the finite part of `f`.

## Main results

* `AlgebraicGeometry.Space.FinitePartPresheaf.existsUnique_projection`: the rule sending a
  pair to its morphism to `Y` determines the projection to `Y` uniquely.

## Implementation notes

Algebraic spaces over `S` are presheaves of types in the universe `u` of the site, while a
pair of Stacks 04PC presents its open subspace as a subfunctor, which lives one universe
higher. `AlgebraicGeometry.Space.small_finiteOpenSubspace` says the pairs over a fixed scheme
are nevertheless essentially small, so the finite part can be, and is, a presheaf of types in
`u`; the identification of its sections with the pairs is therefore part of the data rather
than a definitional unfolding, and `FinitePartPresheaf` records it.

For the same reason the projection to `Y` is recorded as a morphism of presheaves together
with its component formula, rather than being read off the sections. The formula determines it,
which is `existsUnique_projection`, so this packaging adds no choice.

Separatedness of `f` is not needed anywhere here: it enters only when one asks the finite part
to be an algebraic space.

## References

* [Stacks Project, Tag 04PC](https://stacks.math.columbia.edu/tag/04PC)
* [Stacks Project, Tag 04PD](https://stacks.math.columbia.edu/tag/04PD)
* [Stacks Project, Tag 04PI](https://stacks.math.columbia.edu/tag/04PI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

/-- A presheaf of types whose sections over each scheme of the site are identified with the
pairs of Stacks 04PC, whose restriction maps are base change of those pairs, and which carries
the projection to `Y`. -/
structure FinitePartPresheaf (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) where
  /-- The small-valued contravariant functor of finite open subspaces. -/
  toFunctor : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- Canonical identification of sections over a scheme with finite open pairs. -/
  sections : ∀ T, toFunctor.obj (op T) ≃ FiniteOpenSubspace B S hS f (schemeSpace T)
  /-- The natural projection taking a finite open pair to its map into `Y`. -/
  baseMap : toFunctor ⟶ Y.obj
  /-- The projection agrees with the base map in the pair presentation. -/
  baseMap_spec : ∀ T (p : toFunctor.obj (op T)),
    yonedaEquiv.symm (baseMap.app (op T) p) = (sections T p).toBase.hom
  /-- Restriction along `h` is canonically the base change of the pair. -/
  map_isBaseChange : ∀ {T T'} (h : T' ⟶ T) (p : toFunctor.obj (op T)),
    FiniteOpenSubspace.IsBaseChange B S hS f h (sections T p)
      (sections T' (toFunctor.map h.op p))

namespace FinitePartPresheaf

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}

/-- **Stacks 04PI.** The component rule sending a finite open pair to its morphism to `Y`
determines a unique morphism of presheaves to `Y`, namely the projection
`FinitePartPresheaf.baseMap`. -/
@[stacks 04PI "projection_to_base"]
theorem existsUnique_projection (P : FinitePartPresheaf B S hS f) :
    ∃! π : P.toFunctor ⟶ Y.obj,
      ∀ T (p : P.toFunctor.obj (op T)),
        yonedaEquiv.symm (π.app (op T) p) = (P.sections T p).toBase.hom := by
  refine ⟨P.baseMap, P.baseMap_spec, fun π' hπ' => ?_⟩
  ext T p
  exact yonedaEquiv.symm.injective ((hπ' T.unop p).trans (P.baseMap_spec T.unop p).symm)

end FinitePartPresheaf

/-- **Stacks 04PD.** The finite part `(X/Y)_fin` of a morphism `f : X ⟶ Y` of algebraic spaces
over `S`: the presheaf whose sections over a scheme `T` are the pairs consisting of a morphism
`T ⟶ Y` and an open subspace of `T ×_Y X` finite over `T`, with restriction given by base
change. -/
@[stacks 04PD]
noncomputable def finiteOpenSubspacePresheaf (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    FinitePartPresheaf B S hS f := by
  classical
  let pair (T : BigFppfOver B S hS) := FiniteOpenSubspace B S hS f (schemeSpace T)
  let _ : ∀ T, Small.{u} (pair T) := fun T => small_finiteOpenSubspace B S hS f T
  let e (T : BigFppfOver B S hS) : pair T ≃ Shrink.{u} (pair T) := equivShrink (pair T)
  let F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
    { obj := fun T => Shrink.{u} (pair T.unop)
      map := fun {T T'} h => TypeCat.ofHom (fun p =>
        (e T'.unop) (restrictFinitePair B S hS f h.unop ((e T.unop).symm p)))
      map_id := by
        intro T
        ext p
        simp [e, restrictFinitePair_id]
      map_comp := by
        intro T T' T'' h k
        ext p
        simp only [TypeCat.hom_ofHom, TypeCat.Fun.toFun_apply, TypeCat.Fun.coe_mk, unop_comp]
        apply (e T''.unop).injective
        simpa [e, Category.comp_apply] using
          (restrictFinitePair_comp B S hS f h.unop k.unop ((e T.unop).symm p)).symm }
  let sec (T : BigFppfOver B S hS) : F.obj (op T) ≃ pair T := (e T).symm
  let bm : F ⟶ Y.obj :=
    { app := fun T => TypeCat.ofHom (fun p => yonedaEquiv ((e T.unop).symm p).toBase.hom)
      naturality := by
        intro T T' h
        ext p
        change yonedaEquiv ((e T'.unop).symm ((F.map h) p)).toBase.hom =
          (Y.obj.map h) (yonedaEquiv (((e T.unop).symm p).toBase.hom))
        rw [show (e T'.unop).symm ((F.map h) p) =
            restrictFinitePair B S hS f h.unop ((e T.unop).symm p) by simp [F, e]]
        exact (congrArg yonedaEquiv
          (restrictFinitePair_isBaseChange B S hS f h.unop ((e T.unop).symm p)).1).trans
            (yonedaEquiv_naturality' ((e T.unop).symm p).toBase.hom h).symm }
  exact
    { toFunctor := F
      sections := sec
      baseMap := bm
      baseMap_spec := fun T p => Equiv.symm_apply_apply yonedaEquiv _
      map_isBaseChange := by
        intro T T' h p
        change FiniteOpenSubspace.IsBaseChange B S hS f h (sec T p) (sec T' (F.map h.op p))
        simp only [F, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk, sec, Equiv.symm_apply_apply]
        exact restrictFinitePair_isBaseChange B S hS f h (sec T p) }

end AlgebraicGeometry.Space

end
