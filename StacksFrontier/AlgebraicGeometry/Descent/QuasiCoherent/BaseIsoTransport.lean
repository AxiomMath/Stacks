module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.StandardAffineComparison

/-!
# Descent data and an isomorphism of the base

For a pseudofunctor `F` out of `LocallyDiscrete Cᵒᵖ`, families `f : X i ⟶ S` and
`f' : X i ⟶ S'`, and an isomorphism `e : S' ≅ S` with `f' i ≫ e.hom = f i`, the categories of
descent data for `f` and for `f'` are equivalent, compatibly with the canonical descent functors.
Mathlib supplies the equivalence of the two categories of descent data
(`CategoryTheory.Pseudofunctor.DescentData.pullFunctorEquivalence`) and the comparison of the two
canonical functors (`CategoryTheory.Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso`);
this file shows that `F` carries an isomorphism of `C` to an equivalence of fibres, and deduces
that fullness, essential surjectivity and being an equivalence of the canonical descent functor
are invariant under an isomorphism of the base.

## Main definitions

* `Stacks.Descent.mapIsoEquivalence`: the equivalence of fibres `F.obj (op S) ≌ F.obj (op S')`
  induced by an isomorphism `e : S' ≅ S` of the base.
* `Stacks.Descent.descentDataEquivalenceOfBaseIso`: the equivalence
  `F.DescentData f ≌ F.DescentData f'`.
* `Stacks.Descent.toDescentDataIsoOfBaseIso`: the identification of `F.toDescentData f'` with
  `(mapIsoEquivalence F e).inverse ⋙ F.toDescentData f ⋙ pullFunctor F w`.

## Main results

* `Stacks.Descent.full_toDescentData_of_baseIso`,
  `Stacks.Descent.essSurj_toDescentData_of_baseIso` and
  `Stacks.Descent.isEquivalence_toDescentData_of_baseIso`: fullness, essential surjectivity and
  being an equivalence transfer from `F.toDescentData f` to `F.toDescentData f'`.

## Implementation notes

`CategoryTheory.Pseudofunctor.mapComp'` and `CategoryTheory.Pseudofunctor.mapId` are isomorphisms
of `1`-morphisms of `CategoryTheory.Cat`, so `CategoryTheory.Cat.Hom.toNatIso` is applied to each
of them to obtain natural isomorphisms of the underlying functors;
`CategoryTheory.Cat.Hom.id_toFunctor` and `CategoryTheory.Cat.Hom.comp_toFunctor` are `rfl`, so
the types match on the nose.

`Stacks.Descent.mapIsoEquivalence` is built with `CategoryTheory.Equivalence.mk`, which adjusts
the unit so that the triangle identity holds; the two isomorphisms fed to it are the composition
comparisons at `e.hom ≫ e.inv` and `e.inv ≫ e.hom`, and no coherence of the pseudofunctor beyond
`CategoryTheory.Pseudofunctor.mapComp'` and `CategoryTheory.Pseudofunctor.mapId` is used.

The reindexing data of `CategoryTheory.Pseudofunctor.DescentData.pullFunctorEquivalence` is the
identity in both directions here, and `α` and `p'` are pinned at every call: the lemma does not
determine them from its commutative square.

## References

* [Stacks Project, Tag 023S](https://stacks.math.columbia.edu/tag/023S)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe t v' u' v u

namespace Stacks.Descent

section Abstract

variable {C : Type u} [Category.{v} C] (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})

/-- **A pseudofunctor carries an isomorphism of the base to an equivalence of fibres.**  For an
isomorphism `e : S' ≅ S` the pullback functor `F.map e.hom.op.toLoc` from the fibre over `S` to
the fibre over `S'` is an equivalence, with inverse the pullback along `e.inv`.  The two
isomorphisms are the composition comparisons of the pseudofunctor at `e.hom ≫ e.inv` and at
`e.inv ≫ e.hom`. -/
def mapIsoEquivalence {S S' : C} (e : S' ≅ S) :
    (F.obj (.mk (op S)) : Type u') ≌ F.obj (.mk (op S')) :=
  .mk (F.map e.hom.op.toLoc).toFunctor (F.map e.inv.op.toLoc).toFunctor
    ((Cat.Hom.toNatIso (F.mapId (.mk (op S)))).symm ≪≫
      Cat.Hom.toNatIso (F.mapComp' e.hom.op.toLoc e.inv.op.toLoc (𝟙 _)
        (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, e.inv_hom_id, op_id,
          Quiver.Hom.id_toLoc])))
    ((Cat.Hom.toNatIso (F.mapComp' e.inv.op.toLoc e.hom.op.toLoc (𝟙 _)
        (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, e.hom_inv_id, op_id,
          Quiver.Hom.id_toLoc]))).symm ≪≫
      Cat.Hom.toNatIso (F.mapId (.mk (op S'))))

/-- The pullback functor along an isomorphism of the base is an equivalence of fibres. -/
instance {S S' : C} (e : S' ≅ S) : (F.map e.hom.op.toLoc).toFunctor.IsEquivalence :=
  inferInstanceAs (mapIsoEquivalence F e).functor.IsEquivalence

variable {ι : Type t} {S S' : C} {X : ι → C} {f : ∀ i, X i ⟶ S} {f' : ∀ i, X i ⟶ S'}

/-- If `f' i ≫ e.hom = f i` for an isomorphism `e : S' ≅ S`, then
`𝟙 (X i) ≫ f i = f' i ≫ e.hom`. -/
theorem baseIsoW (e : S' ≅ S) (hf : ∀ i, f' i ≫ e.hom = f i) (i : ι) :
    𝟙 (X i) ≫ f i = f' i ≫ e.hom := by rw [Category.id_comp, hf]

/-- If `f' i ≫ e.hom = f i` for an isomorphism `e : S' ≅ S`, then
`𝟙 (X i) ≫ f' i = f i ≫ e.inv`. -/
theorem baseIsoW' (e : S' ≅ S) (hf : ∀ i, f' i ≫ e.hom = f i) (i : ι) :
    𝟙 (X i) ≫ f' i = f i ≫ e.inv := by
  rw [Category.id_comp, ← hf, Category.assoc, e.hom_inv_id, Category.comp_id]

/-- **The categories of descent data over two isomorphic bases agree.**  This is
`CategoryTheory.Pseudofunctor.DescentData.pullFunctorEquivalence` with both reindexings taken to
be the identity. -/
def descentDataEquivalenceOfBaseIso (e : S' ≅ S) (hf : ∀ i, f' i ≫ e.hom = f i) :
    F.DescentData f ≌ F.DescentData f' :=
  Pseudofunctor.DescentData.pullFunctorEquivalence F e
    (α := id) (p' := fun i ↦ 𝟙 (X i)) (baseIsoW e hf)
    (β := id) (q' := fun i ↦ 𝟙 (X i)) (baseIsoW' e hf)

/-- **The canonical descent functor over an isomorphic base.**  The canonical descent functor
`F.toDescentData f'` is isomorphic to the composite of the inverse of
`Stacks.Descent.mapIsoEquivalence F e`, the canonical descent functor `F.toDescentData f`, and the
pullback of descent data along the identity reindexing. -/
def toDescentDataIsoOfBaseIso (e : S' ≅ S) (hf : ∀ i, f' i ≫ e.hom = f i) :
    F.toDescentData f' ≅
      (mapIsoEquivalence F e).inverse ⋙ F.toDescentData f ⋙
        Pseudofunctor.DescentData.pullFunctor F (α := id) (p' := fun i ↦ 𝟙 (X i))
          (baseIsoW e hf) :=
  ((mapIsoEquivalence F e).invFunIdAssoc (F.toDescentData f')).symm ≪≫
    Functor.isoWhiskerLeft _
      (Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso F
        (α := id) (p' := fun i ↦ 𝟙 (X i)) (baseIsoW e hf)).symm

/-- The pullback of descent data along the identity reindexing is an equivalence. -/
private theorem isEquivalence_pullFunctor_of_baseIso (e : S' ≅ S)
    (hf : ∀ i, f' i ≫ e.hom = f i) :
    (Pseudofunctor.DescentData.pullFunctor F (α := id) (p' := fun i ↦ 𝟙 (X i))
      (baseIsoW e hf)).IsEquivalence :=
  (descentDataEquivalenceOfBaseIso F e hf).isEquivalence_functor

/-- **Fullness of the canonical descent functor transfers along an isomorphism of the base.** -/
theorem full_toDescentData_of_baseIso (e : S' ≅ S) (hf : ∀ i, f' i ≫ e.hom = f i)
    (h : (F.toDescentData f).Full) : (F.toDescentData f').Full := by
  have := h
  have := isEquivalence_pullFunctor_of_baseIso F e hf
  exact Functor.Full.of_iso (F := (mapIsoEquivalence F e).inverse ⋙ F.toDescentData f ⋙
    Pseudofunctor.DescentData.pullFunctor F (α := id) (p' := fun i ↦ 𝟙 (X i)) (baseIsoW e hf))
    (toDescentDataIsoOfBaseIso F e hf).symm

/-- **Essential surjectivity of the canonical descent functor transfers along an isomorphism of
the base.** -/
theorem essSurj_toDescentData_of_baseIso (e : S' ≅ S) (hf : ∀ i, f' i ≫ e.hom = f i)
    (h : (F.toDescentData f).EssSurj) : (F.toDescentData f').EssSurj := by
  have := h
  have := isEquivalence_pullFunctor_of_baseIso F e hf
  exact Functor.essSurj_of_iso (F := (mapIsoEquivalence F e).inverse ⋙ F.toDescentData f ⋙
    Pseudofunctor.DescentData.pullFunctor F (α := id) (p' := fun i ↦ 𝟙 (X i)) (baseIsoW e hf))
    (toDescentDataIsoOfBaseIso F e hf).symm

/-- **Being an equivalence transfers along an isomorphism of the base.** -/
theorem isEquivalence_toDescentData_of_baseIso (e : S' ≅ S) (hf : ∀ i, f' i ≫ e.hom = f i)
    (h : (F.toDescentData f).IsEquivalence) : (F.toDescentData f').IsEquivalence := by
  have := h
  have := isEquivalence_pullFunctor_of_baseIso F e hf
  exact Functor.isEquivalence_of_iso
    (F := (mapIsoEquivalence F e).inverse ⋙ F.toDescentData f ⋙
      Pseudofunctor.DescentData.pullFunctor F (α := id) (p' := fun i ↦ 𝟙 (X i)) (baseIsoW e hf))
    (toDescentDataIsoOfBaseIso F e hf).symm

end Abstract

end Stacks.Descent

end

end
