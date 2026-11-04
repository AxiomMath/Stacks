module

public import Mathlib.CategoryTheory.Sites.Descent.DescentData

/-!
# Fullness of the canonical descent functor along a refinement

Let `F` be a pseudofunctor from `LocallyDiscrete Cᵒᵖ` to `Cat`, let `f i : X i ⟶ S` be a family
of morphisms and let `f' j : X' j ⟶ S` be a family refining it, that is, one equipped with a
reindexing `α` and morphisms `p' j : X' j ⟶ X (α j)` over `S`.  This file proves that
`CategoryTheory.Pseudofunctor.toDescentData` for `f` is **full** as soon as it is full for `f'`,
under one hypothesis about the family `f` alone: that a morphism between objects over `X i` is
determined by its pullbacks along the morphisms into `X i` which, after composing with `f i`,
factor through the refining family.

## Main results

* `CategoryTheory.Pseudofunctor.map_eq_of_map_eq_of_comp`: if two parallel morphisms agree after
  applying the pullback functor of one factor of a composite, they agree after applying the
  pullback functor of the composite.  This holds in an arbitrary bicategory.
* `CategoryTheory.Pseudofunctor.DescentData.faithful_pullFunctor_of_hom_ext`: the refinement
  functor `F.DescentData f ⥤ F.DescentData f'` is faithful.
* `CategoryTheory.Pseudofunctor.DescentData.full_toDescentData_of_refinement`: consequently
  `F.toDescentData f` is full if `F.toDescentData f'` is.

## Implementation notes

Faithfulness of the refinement functor is already available twice, and neither form can be used
where this one is needed.  Mathlib's
`CategoryTheory.Pseudofunctor.DescentData.faithful_pullFunctor` assumes a *global* prestack
condition `[F.IsPrestack J]`, which is exactly what an application of this file is trying to
prove, so using it would be circular.  The local form
`CategoryTheory.Pseudofunctor.DescentData.nonempty_fullyFaithful_pullFunctor` of
`StacksFrontier/CategoryTheory/Sites/Descent/OfRefinement.lean` assumes the full sheaf condition for
the presheaf of morphisms over each `X i`, which is stronger than what the faithfulness half of
its proof uses, and it also assumes chosen fibre products of the members of `f` with each other.

The hypothesis used here instead is stated directly as the determination of a morphism by its
pullbacks, with no presheaf of morphisms and no fibre products.  That makes it available from a
separatedness statement about the family `f` and nothing else, and it is what lets the proof run
with none of the `backward.isDefEq` options that both existing proofs require: those are needed
because they unfold `CategoryTheory.Pseudofunctor.presheafHom` inside a goal which is then no
longer type-correct at `implicit` transparency.  Here the compatibility of a morphism of descent
data is used as it stands, and the only normalisation is
`CategoryTheory.Pseudofunctor.mapComp'_naturality_2`, applied through
`map_eq_of_map_eq_of_comp`.

The refinement morphism is taken over the identity of `S`, so the comparison with
`CategoryTheory.Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso` needs the unit
comparison `CategoryTheory.Pseudofunctor.mapId`.  The commutation hypothesis is therefore stated
as `p' j ≫ f (α j) = f' j ≫ 𝟙 S` rather than `p' j ≫ f (α j) = f' j`: it is passed unchanged to
`CategoryTheory.Pseudofunctor.DescentData.pullFunctor` in both results, so that the two
statements speak about the same functor rather than about two functors differing by a proof of a
proposition.

## References

* [Stacks Project, Tag 02ZD](https://stacks.math.columbia.edu/tag/02ZD)
-/

@[expose] public section

universe t t' w v' v u' u

namespace CategoryTheory

open Bicategory Opposite Pseudofunctor Pseudofunctor.LocallyDiscreteOpToCat

namespace Pseudofunctor

section Bicategory

variable {B : Type u} [Bicategory.{w, v} B] (F : Pseudofunctor B Cat.{v', u'})

/-- **Pullback along a composite detects nothing new.**  If two parallel morphisms of `F.obj b₀`
have the same image under the functor attached to `g : b₀ ⟶ b₁`, they have the same image under
the functor attached to any composite `g ≫ h`.

The two images under the composite are conjugate, by the components of
`CategoryTheory.Pseudofunctor.mapComp'`, to the images under `h` of the images under `g`. -/
theorem map_eq_of_map_eq_of_comp {b₀ b₁ b₂ : B} (g : b₀ ⟶ b₁) (h : b₁ ⟶ b₂) (gh : b₀ ⟶ b₂)
    (hgh : g ≫ h = gh) {M N : F.obj b₀} {a a' : M ⟶ N}
    (ha : (F.map g).toFunctor.map a = (F.map g).toFunctor.map a') :
    (F.map gh).toFunctor.map a = (F.map gh).toFunctor.map a' := by
  rw [← F.mapComp'_naturality_2 g h gh hgh a, ← F.mapComp'_naturality_2 g h gh hgh a', ha]

end Bicategory

variable {C : Type u} [Category.{v} C]

namespace DescentData

variable {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
  {ι : Type t} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}
  {ι' : Type t'} {X' : ι' → C} {f' : ∀ j, X' j ⟶ S}
  {α : ι' → ι} {p' : ∀ j, X' j ⟶ X (α j)}
  (w : ∀ j, p' j ≫ f (α j) = f' j ≫ 𝟙 S)
  (hdet : ∀ (i : ι) (M N : F.obj (.mk (op (X i)))) (θ θ' : M ⟶ N),
    (∀ (j : ι') (Z : C) (r : Z ⟶ X i) (b : Z ⟶ X' j), b ≫ f' j = r ≫ f i →
      (F.map r.op.toLoc).toFunctor.map θ = (F.map r.op.toLoc).toFunctor.map θ') → θ = θ')

include w hdet in
/-- **The refinement functor on descent data is faithful.**  If a morphism between objects over
`X i` is determined by its pullbacks along the morphisms into `X i` that factor through the
refining family `f'` over `S`, then the functor `F.DescentData f ⥤ F.DescentData f'` induced by
the refinement is faithful.

Given two morphisms of descent data with the same image, the compatibility of each with the
transition morphisms of its source and target, taken over an object `Z` mapping to `X i` and, via
the refinement, to `X (α j)`, expresses the pullback of its `i`-th component as a conjugate of
the pullback of its `α j`-th component.  The latter agrees for the two morphisms because the
`j`-th components of their images do, by
`CategoryTheory.Pseudofunctor.map_eq_of_map_eq_of_comp`. -/
lemma faithful_pullFunctor_of_hom_ext :
    (pullFunctor F (f := f) (p := 𝟙 _) (f' := f') (p' := p') w).Faithful where
  map_injective {D₁ D₂ ψ ψ'} hψ := by
    refine hom_ext fun i ↦ hdet i _ _ _ _ fun j Z r b fac ↦ ?_
    have hf₂ : (b ≫ p' j) ≫ f (α j) = r ≫ f i := by
      rw [Category.assoc, w j, Category.comp_id, fac]
    have hj : (F.map (p' j).op.toLoc).toFunctor.map (ψ.hom (α j)) =
        (F.map (p' j).op.toLoc).toFunctor.map (ψ'.hom (α j)) :=
      congrFun (congrArg Hom.hom hψ) j
    have hbig : (F.map (b ≫ p' j).op.toLoc).toFunctor.map (ψ.hom (α j)) =
        (F.map (b ≫ p' j).op.toLoc).toFunctor.map (ψ'.hom (α j)) :=
      map_eq_of_map_eq_of_comp F (p' j).op.toLoc b.op.toLoc (b ≫ p' j).op.toLoc
        (by rw [← Quiver.Hom.comp_toLoc, ← op_comp]) hj
    rw [← cancel_mono (D₂.hom (r ≫ f i) r (b ≫ p' j) rfl hf₂), ψ.comm _ r (b ≫ p' j) rfl hf₂,
      ψ'.comm _ r (b ≫ p' j) rfl hf₂, hbig]

include w hdet in
/-- **Fullness of the canonical descent functor passes from a refinement to the family refined.**
If the canonical descent functor of the refining family `f'` is full, and a morphism between
objects over `X i` is determined by its pullbacks along the morphisms into `X i` that factor
through `f'` over `S`, then the canonical descent functor of `f` is full.

The composite of `F.toDescentData f` with the refinement functor is isomorphic to
`F.toDescentData f'`, by
`CategoryTheory.Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso` and the unit
comparison, and the refinement functor is faithful by
`CategoryTheory.Pseudofunctor.DescentData.faithful_pullFunctor_of_hom_ext`. -/
lemma full_toDescentData_of_refinement [(F.toDescentData f').Full] :
    (F.toDescentData f).Full := by
  have := faithful_pullFunctor_of_hom_ext w hdet
  refine Functor.Full.of_comp_faithful_iso
    (G := pullFunctor F (f := f) (p := 𝟙 _) (f' := f') (p' := p') w)
    (H := F.toDescentData f') ?_
  exact toDescentDataCompPullFunctorIso _ _ ≪≫
    Functor.isoWhiskerRight (Cat.Hom.toNatIso (F.mapId _)) _ ≪≫ Functor.leftUnitor _

end DescentData

end Pseudofunctor

end CategoryTheory

end
