module

public import Mathlib.CategoryTheory.Sites.Point.Over
public import StacksFrontier.CategoryTheory.Sites.Point.ConservativeFamily
import StacksCore.Tactic.StacksAttribute

/-!
# Conservative families of points of a localization

Let `(C, J)` be a site, `U` an object of `C` and `{p_i}_{i ∈ I}` a family of points of `C`, with
fibre functors `u_i`. For `x ∈ u_i(U)` Stacks 04H2 constructs a point `q_{i,x}` of the localized
site `C/U`, Mathlib's `CategoryTheory.GrothendieckTopology.Point.over`, whose fibre functor sends
`(φ : V ⟶ U)` to `{y ∈ u_i(V) | u_i(φ)(y) = x}`. Stacks 04H6 says that if `{p_i}` is a
conservative family, then so is `{q_{i,x}}_{i ∈ I, x ∈ u_i(U)}`, and hence that every
localization of a site with enough points has enough points.

## Main results

* `CategoryTheory.GrothendieckTopology.IsConservativeFamily.mem_of_forall_exists`: a sieve
  `S` on `X` all of whose arrows jointly reach every element of `u_i(X)`, for every member `p_i`
  of a conservative family, is a covering sieve.
* `CategoryTheory.GrothendieckTopology.IsConservativeFamily.over`: Stacks 04H6, the points
  `q_{i,x}` form a conservative family of points of `C/U`.
* `CategoryTheory.GrothendieckTopology.HasConservativeFamily.over`: Stacks 04H6, the "in
  particular": if `C` has enough points, then so does `C/U`.

## Implementation notes

Conservative families are those of Stacks 00YK,
`CategoryTheory.GrothendieckTopology.IsConservativeFamily`, which asks for no smallness of the
index type. Mathlib's `CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.over` states
the same result for a `w`-small family; its proof passes through
`CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.jointly_reflect_ofArrows_mem_of_small`,
which replaces a sieve by a family of arrows indexed by the points and their elements, and that
is where smallness is used. Here the sieve is used directly, through the subpresheaf
`CategoryTheory.Sieve.shrinkFunctor` of `shrinkYoneda X` that it cuts out: it is a covering
sieve as soon as the inclusion of that subpresheaf is locally surjective, and local
surjectivity is detected on the stalks at a conservative family of points with no smallness
condition on the family.

## References

* [Stacks Project, Tag 04H6](https://stacks.math.columbia.edu/tag/04H6)
* [Stacks Project, Tag 04H2](https://stacks.math.columbia.edu/tag/04H2)
-/

@[expose] public section

namespace CategoryTheory.GrothendieckTopology

open Limits Opposite

universe w v u t

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [LocallySmall.{w} C]
  [HasSheafify J (Type w)] [J.WEqualsLocallyBijective (Type w)]

/-- Let `{p_i}` be a conservative family of points of a site `(C, J)`, with fibre functors
`u_i`. A sieve `S` on `X` such that, for every `i`, every element of `u_i(X)` is the image of an
element of `u_i(Y)` along some arrow `Y ⟶ X` of `S`, is a covering sieve. -/
theorem IsConservativeFamily.mem_of_forall_exists {ι : Type t} {p : ι → Point.{w} J}
    (hp : IsConservativeFamily p) {X : C} (S : Sieve X)
    (hS : ∀ (i : ι) (x : (p i).fiber.obj X), ∃ (Y : C) (g : Y ⟶ X) (_ : S g)
      (y : (p i).fiber.obj Y), (p i).fiber.map g y = x) :
    S ∈ J X := by
  have : Presheaf.IsLocallySurjective J (Sieve.shrinkFunctor.{w} S).ι := by
    refine ((isConservativeFamily_iff_ofObj p).1 hp).jointly_reflect_isLocallySurjective _
      (fun Φ ξ ↦ ?_)
    obtain ⟨_, ⟨i⟩⟩ := Φ
    obtain ⟨x, rfl⟩ :=
      ((p i).shrinkYonedaCompPresheafFiberIso.app X).toEquiv.symm.surjective ξ
    obtain ⟨Y, g, hg, y, rfl⟩ := hS i x
    let s : (Sieve.shrinkFunctor.{w} S).toFunctor.obj (op Y) :=
      ⟨shrinkYonedaObjObjEquiv.symm g, by simpa using hg⟩
    refine ⟨(p i).toPresheafFiber Y y (Sieve.shrinkFunctor.{w} S).toFunctor s, ?_⟩
    have h₂ := Point.toPresheafFiber_w_apply (p i) g y (shrinkYoneda.{w}.obj X)
      (shrinkYonedaObjObjEquiv.symm (𝟙 X))
    rw [shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm, Quiver.Hom.unop_op,
      Category.comp_id] at h₂
    exact (Point.toPresheafFiber_naturality_apply (p i) (Sieve.shrinkFunctor.{w} S).ι Y y s).trans
      (h₂.trans (Point.shrinkYonedaCompPresheafFiberIso_inv_app_toPresheafFiber (p i) _).symm)
  refine J.superset_covering ?_
    (Presheaf.imageSieve_mem J (Sieve.shrinkFunctor.{w} S).ι
      (shrinkYonedaObjObjEquiv.symm (𝟙 X)))
  rintro Y g ⟨⟨t, ht⟩, h⟩
  dsimp at h
  rw [shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm] at h
  subst h
  simpa using ht

/-- **Stacks 04H6.** Let `{p_i}_{i ∈ I}` be a conservative family of points of a site `(C, J)`,
with fibre functors `u_i`, and let `X` be an object of `C`. Then the points
`q_{i,x} = (p i).over x` of the localized site `C/X` of Stacks 04H2, for `i ∈ I` and
`x ∈ u_i(X)`, form a conservative family of points of `C/X`. -/
@[stacks 04H6]
theorem IsConservativeFamily.over {ι : Type t} {p : ι → Point.{w} J}
    (hp : IsConservativeFamily p) (X : C) [HasSheafify (J.over X) (Type w)] :
    IsConservativeFamily (fun ix : Σ i, (p i).fiber.obj X ↦ (p ix.1).over ix.2) := by
  rw [isConservativeFamily_iff_ofObj]
  refine ObjectProperty.IsConservativeFamilyOfPoints.mk' (fun Y S hS ↦ ?_)
  obtain ⟨Y, f, rfl⟩ := Over.mk_surjective Y
  obtain ⟨S, rfl⟩ := (Sieve.overEquiv _).symm.surjective S
  rw [mem_over_iff, OrderIso.apply_symm_apply]
  refine hp.mem_of_forall_exists S (fun i y ↦ ?_)
  obtain ⟨T, a, ha, ⟨z, hz₁⟩, hz₂⟩ :=
    hS ⟨_, ObjectProperty.ofObj_apply _ ⟨i, (p i).fiber.map f y⟩⟩
      ⟨by exact y, by rw [FunctorToTypes.mem_fromOverSubfunctor_iff]; rfl⟩
  exact ⟨T.left, a.left, (Sieve.overEquiv_symm_iff _ _).1 ha, z, congrArg Subtype.val hz₂⟩

/-- **Stacks 04H6**, the "in particular": if a site `(C, J)` has enough points, i.e. a
conservative family of points (Stacks 00YK (2)), then so does every localization `C/X`. -/
@[stacks 04H6 "in particular"]
theorem HasConservativeFamily.over (h : HasConservativeFamily.{w} J) (X : C)
    [HasSheafify (J.over X) (Type w)] : HasConservativeFamily.{w} (J.over X) := by
  obtain ⟨S, hS⟩ := h
  exact IsConservativeFamily.hasConservativeFamily (IsConservativeFamily.over hS X)

end CategoryTheory.GrothendieckTopology
