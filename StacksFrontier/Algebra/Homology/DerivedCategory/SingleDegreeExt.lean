module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# The morphisms of `D(𝒜)` between objects concentrated in one degree are `Ext`-groups

Let `𝒜` be an abelian category and `A`, `B` two of its objects. For `p`, `q` in `ℤ` the
morphisms of `D(𝒜)` from `A` placed in degree `p` to `B` placed in degree `q` are

* zero when `p < q` (`DerivedCategory.hom_singleFunctor_obj_eq_zero`), and
* `Ext^{p - q}_𝒜(A, B)` when `q ≤ p` (`DerivedCategory.singleHomEquivExt`).

Both are read off the degree conventions: `DerivedCategory.singleFunctor 𝒜 p` places the object
in degree `p`, the shift `K⟦n⟧` moves degree `d` to `d - n`, and
`CategoryTheory.Abelian.Ext.homEquiv` identifies `Ext^i_𝒜(A, B)` with
`Hom_{D(𝒜)}(A[0], (B[0])⟦i⟧)`, whose target has `B` in degree `-i`. So the pair
`(A` in degree `p`, `B` in degree `q)` is the pair `(A[0], (B[0])⟦p - q⟧)` shifted by `-p`, and
`Ext^{p - q}` is what it computes.

This is the identification the dévissage of [Stacks, Tag 0G2H] needs in order to turn the
reduced form of its statement — the source system concentrated in one degree, the target
concentrated in one degree — into the `Ext`-group statement
`colim_n Ext^i_X(𝓘^n𝓕, 𝓖) = Ext^i_U(𝓕|_U, 𝓖|_U)` its third step proves.

## Main results

* `DerivedCategory.hom_singleFunctor_obj_eq_zero`: the morphisms vanish when `p < q`.
* `DerivedCategory.singleHomEquivExt`: the bijection onto `Ext^{p - q}_𝒜(A, B)` when `q ≤ p`.

## Naturality

`DerivedCategory.singleHomEquivExt` is a bijection of `Hom`-sets. Its naturality in the source —
that precomposing `(singleFunctor 𝒜 p).map a` for `a : A' ⟶ A` corresponds to Yoneda composition
with `CategoryTheory.Abelian.Ext.mk₀ a` — and its compatibility with an exact functor, which are
what an application to [Stacks, Tag 0G2H] needs, are proved in
`StacksFrontier/Algebra/Homology/DerivedCategory/SingleDegreeExtNaturality.lean`.

## References

* [Stacks Project, Tag 0G2H](https://stacks.math.columbia.edu/tag/0G2H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe w w' v u

namespace DerivedCategory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- **No morphisms from a lower degree to a higher one.** A morphism of `D(𝒜)` from `A` placed in
degree `p` to `B` placed in degree `q` is zero when `p < q`: the source is in `D^{≤p}`, the
target in `D^{≥q}`, and `p < q`. -/
public lemma hom_singleFunctor_obj_eq_zero [HasDerivedCategory.{w'} 𝒜] (A B : 𝒜) (p q : ℤ)
    (hpq : p < q) (f : (singleFunctor 𝒜 p).obj A ⟶ (singleFunctor 𝒜 q).obj B) : f = 0 :=
  TStructure.t.zero_of_isLE_of_isGE f p q hpq inferInstance inferInstance

variable [HasDerivedCategory.{w'} 𝒜] [HasExt.{w} 𝒜]

/-- **The morphisms of `D(𝒜)` between objects concentrated in one degree are `Ext`-groups.** For
`A`, `B` in `𝒜` and `i : ℕ` with `q + i = p`, the morphisms from `A` placed in degree `p` to `B`
placed in degree `q` are `Ext^i_𝒜(A, B)`.

The two objects are the two objects of `CategoryTheory.Abelian.Ext.homEquiv`, namely `A[0]` and
`(B[0])⟦i⟧`, shifted by `-p`; `CategoryTheory.SingleFunctors.shiftIso` identifies the shifts of
`A[0]` and `B[0]` with the single functors, `CategoryTheory.shiftFunctorAdd'` splits the shift of
the target in two, and the shift by `-p` is an equivalence. -/
public noncomputable def singleHomEquivExt (A B : 𝒜) (p q : ℤ) (i : ℕ) (hi : q + (i : ℤ) = p) :
    ((singleFunctor 𝒜 p).obj A ⟶ (singleFunctor 𝒜 q).obj B) ≃ Ext.{w} A B i :=
  (Iso.homCongr (((singleFunctors 𝒜).shiftIso (-p) p 0 (by lia)).app A).symm
      ((((singleFunctors 𝒜).shiftIso (-q) q 0 (by lia)).app B).symm ≪≫
        (shiftFunctorAdd' (DerivedCategory 𝒜) (i : ℤ) (-p) (-q) (by lia)).app
          ((singleFunctor 𝒜 0).obj B))).trans
    (((Functor.FullyFaithful.ofFullyFaithful
          (shiftFunctor (DerivedCategory 𝒜) (-p))).homEquiv).symm.trans Ext.homEquiv.symm)

end DerivedCategory

end
