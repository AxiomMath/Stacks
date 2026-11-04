module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Sheaves.Skyscraper
public import Mathlib.Topology.Sheaves.Stalks

/-!
# A pushout of sheaves of commutative rings is generated, on stalks, by its two legs

Let
```
R --f--> B
|g       |h
C --k--> Q
```
be a pushout square of sheaves of commutative rings on a topological space `Z`.  This file
proves that every germ of `Q` at a point `x` is a *finite sum of products* `h(b) k(c)` of a
germ of `B` and a germ of `C`.

Equivalently: `Q` is generated as a sheaf of `C`-modules by the image of `B`, stalkwise.  That
is the content which separates a pushout of *rings* from a tensor product of *modules*, and it is
the one assertion about an abstract pushout which cannot be obtained formally — the pushout of
commutative rings is not the coproduct of the two legs' images in any formal sense, and an
epimorphism of commutative rings need not be surjective, so the statement has to be proved
through the tensor product.

Two steps, both of which are short because the inputs exist:

* taking stalks is a **left adjoint** — `stalkSkyscraperSheafAdjunction` exhibits
  `TopCat.Sheaf.forget C Z ⋙ TopCat.Presheaf.stalkFunctor C x` as the left adjoint of the
  skyscraper sheaf functor, for any value category with a terminal object and colimits — so it
  preserves pushouts (`isPushout_stalkFunctor_map`);
* a pushout of commutative rings *is* a tensor product (`CommRingCat.isPushout_tensorProduct`),
  every element of a tensor product is a finite sum of pure tensors, and under the canonical
  identification a pure tensor `b ⊗ c` is the product of the two legs' images
  (`exists_list_of_isPushout`).

## Main results

* `Stacks.Sheaves.CommRingPushout.exists_list_of_isPushout` — every element of a pushout of
  commutative rings is a finite sum of products of elements from the two legs.
* `Stacks.Sheaves.CommRingPushout.isPushout_stalkFunctor_map` — the stalk functor at a point of
  a topological space carries a pushout square of sheaves of commutative rings to a pushout
  square of commutative rings.
* `Stacks.Sheaves.CommRingPushout.exists_list_germ_of_isPushout` — the two combined, on germs.

## Implementation notes

`exists_list_of_isPushout` is stated for an arbitrary pushout square rather than for the
explicit tensor-product cocone, so the two ring homomorphisms of the span need not be algebra
maps;  `RingHom.toAlgebra` turns them into algebra maps and
`CategoryTheory.IsPushout.isoIsPushout` transports the conclusion from the tensor product to the
given pushout.  The conclusion is phrased with a `List` rather than a `Finset` because the
multiplicands are not assumed distinct and the induction over `TensorProduct.induction_on`
appends.

The decidability instance that `skyscraperSheafFunctor` needs is supplied classically;  it
occurs only in the right adjoint, so the left adjoint — the stalk functor, which is what carries
the colimit — is unaffected.

**No `@[stacks]` attribute is placed in this file.**  Nothing here is a tagged result of the
source;  it is the generation statement that the base-change clause of [Stacks, Tag 0EY6] and
the `algebraPullback_isQuasicoherent` clause of [Stacks, Tag 01SA] need.

## References

* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
* [Stacks Project, Tag 0EY6](https://stacks.math.columbia.edu/tag/0EY6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopCat TensorProduct

universe u

namespace Stacks.Sheaves.CommRingPushout

/-- **Every element of a pushout of commutative rings is a finite sum of products of the two
legs.**  For a pushout square with span `f : R ⟶ B`, `g : R ⟶ C` and legs `h : B ⟶ Q`,
`k : C ⟶ Q`, every `q : Q` is `∑ h(bᵢ) k(cᵢ)`:  the pushout is the tensor product `B ⊗_R C`, every
element of which is a finite sum of pure tensors, and a pure tensor is the product of the images
of its two factors. -/
public theorem exists_list_of_isPushout {R B C Q : CommRingCat.{u}} {f : R ⟶ B} {g : R ⟶ C}
    {h : B ⟶ Q} {k : C ⟶ Q} (H : IsPushout f g h k) (q : Q) :
    ∃ L : List (B × C), q = (L.map (fun p => h.hom p.1 * k.hom p.2)).sum := by
  let _i1 : Algebra R B := f.hom.toAlgebra
  let _i2 : Algebra R C := g.hom.toAlgebra
  have hf : CommRingCat.ofHom (algebraMap R B) = f := rfl
  have hg : CommRingCat.ofHom (algebraMap R C) = g := rfl
  have H' : IsPushout f g
      (CommRingCat.ofHom (S := B ⊗[R] C) Algebra.TensorProduct.includeLeftRingHom)
      (CommRingCat.ofHom (S := B ⊗[R] C)
        Algebra.TensorProduct.includeRight.toRingHom) := by
    rw [← hf, ← hg]
    exact CommRingCat.isPushout_tensorProduct R B C
  let e := IsPushout.isoIsPushout _ _ H' H
  have h0 := IsPushout.inl_isoIsPushout_hom _ _ H' H
  have h1 := IsPushout.inr_isoIsPushout_hom _ _ H' H
  have hl : ∀ b : B, e.hom.hom (Algebra.TensorProduct.includeLeftRingHom b) = h.hom b :=
    fun b => congrArg (fun z : B ⟶ Q => z.hom b) h0
  have hr : ∀ c : C,
      e.hom.hom (Algebra.TensorProduct.includeRight.toRingHom c) = k.hom c :=
    fun c => congrArg (fun z : C ⟶ Q => z.hom c) h1
  have hq : e.hom.hom (e.inv.hom q) = q :=
    congrArg (fun z : Q ⟶ Q => z.hom q) e.inv_hom_id
  have key : ∀ t : B ⊗[R] C, ∃ L : List (B × C),
      e.hom.hom t = (L.map (fun p => h.hom p.1 * k.hom p.2)).sum := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨[], by simp⟩
    | tmul b c =>
        refine ⟨[(b, c)], ?_⟩
        have ht : (b ⊗ₜ[R] c : B ⊗[R] C) =
            Algebra.TensorProduct.includeLeftRingHom b *
              Algebra.TensorProduct.includeRight.toRingHom c := by
          simp [Algebra.TensorProduct.includeLeftRingHom_apply,
            Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul]
        rw [ht, map_mul, hl, hr]
        simp
    | add x y hx hy =>
        obtain ⟨L1, hL1⟩ := hx
        obtain ⟨L2, hL2⟩ := hy
        refine ⟨L1 ++ L2, ?_⟩
        rw [map_add, hL1, hL2, List.map_append, List.sum_append]
  exact (key (e.inv.hom q)).imp fun L hL => hq.symm.trans hL

/-- **Taking stalks preserves pushouts of sheaves of commutative rings.**  The composite
`TopCat.Sheaf.forget ⋙ TopCat.Presheaf.stalkFunctor` at a point is the left adjoint of the
skyscraper sheaf functor, hence preserves all colimits. -/
public theorem isPushout_stalkFunctor_map {Z : TopCat.{u}} (x : Z)
    {R B C Q : TopCat.Sheaf CommRingCat.{u} Z} {f : R ⟶ B} {g : R ⟶ C} {h : B ⟶ Q} {k : C ⟶ Q}
    (H : IsPushout f g h k) :
    IsPushout ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map f.hom)
      ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map g.hom)
      ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map h.hom)
      ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map k.hom) := by
  classical
  have hadj := stalkSkyscraperSheafAdjunction (C := CommRingCat.{u}) x
  have : (TopCat.Sheaf.forget CommRingCat.{u} Z ⋙
      TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).IsLeftAdjoint := hadj.isLeftAdjoint
  exact H.map (TopCat.Sheaf.forget CommRingCat.{u} Z ⋙
    TopCat.Presheaf.stalkFunctor CommRingCat.{u} x)

/-- **A pushout of sheaves of commutative rings is generated by its two legs on germs.**  Every
germ at `x` of the pushout of a span of sheaves of commutative rings is a finite sum of products
of the images of a germ of `B` and a germ of `C`.  Each of those germs is the germ of a section
over some neighbourhood of `x` (`TopCat.Presheaf.germ_exist`), so this is the local generation
statement. -/
public theorem exists_list_germ_of_isPushout {Z : TopCat.{u}} (x : Z)
    {R B C Q : TopCat.Sheaf CommRingCat.{u} Z} {f : R ⟶ B} {g : R ⟶ C} {h : B ⟶ Q} {k : C ⟶ Q}
    (H : IsPushout f g h k) (q : Q.presheaf.stalk x) :
    ∃ L : List (B.presheaf.stalk x × C.presheaf.stalk x),
      q = (L.map (fun p =>
        ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map h.hom).hom p.1 *
          ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map k.hom).hom p.2)).sum :=
  exists_list_of_isPushout (isPushout_stalkFunctor_map x H) q

end Stacks.Sheaves.CommRingPushout

end
