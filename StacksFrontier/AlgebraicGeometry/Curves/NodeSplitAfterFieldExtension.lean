module

public import StacksFrontier.AlgebraicGeometry.Curves.IsSplitNode
public import StacksFrontier.AlgebraicGeometry.Curves.NodeFittingIdealClosedPoint
public import StacksFrontier.AlgebraicGeometry.Curves.NodeQuadraticAlgebra.SplitNodeBaseChange
public import StacksFrontier.AlgebraicGeometry.Scheme.BaseChange.PrescribedResidueFieldPoint

/-!
# A node becomes split after an extension of the ground field that splits its quadratic algebra

Let `k` be a field, let `X` be a one-dimensional scheme locally of finite type over `k` and let
`x` be a node of `X`. The quadratic algebra `κ'` of Stacks Tag 0CBT attached to the local ring at
`x` is a separable `κ(x)`-algebra of degree two, and a `k`-algebra map `κ' → K` into a field `K`
makes the node *split* at a suitable point of the base change `X_K`:

* the point is the one with residue field `K` above `x`
  (`AlgebraicGeometry.exists_baseChange_point_of_residueFieldHom`), so its residue field is the
  new ground field;
* it is a node, because the node condition is invariant under extension of the ground field
  (Stacks Tag 0C56);
* and the quadratic algebra there is the trivial one, because the local homomorphism of local
  rings extends the maximal ideal (Stacks Tag 0C50) and the quadratic algebra of the node
  therefore acquires the prescribed rational point
  (`Stacks.Curves.nonempty_quadraticAlgebra_algEquiv_prod_of_map_maximalIdeal_eq_of_ringHom`).

Such a `K` always exists, and may be taken finite separable over `k` at a node whose residue
field is finite over `k`: the quadratic algebra is a separable `κ(x)`-algebra of degree two, so
the residue field of any of its maximal ideals receives a `κ(x)`-algebra map from it
(`Stacks.Curves.exists_finiteSeparable_algHom_quadraticAlgebra_over_base`).

This is the reduction of Stacks Tag 0CBY to the case of a split node, at the level of a single
curve over a field.

## Main results

* `Stacks.Curves.exists_isSplitNode_baseChange_of_quadraticAlgebraHom` — a node becomes a split
  node at the point with residue field `K` of the base change, provided `K` receives a
  `k`-algebra map from the quadratic algebra of the node.
* `Stacks.Curves.exists_finiteSeparable_isSplitNode_baseChange` — such a `K` exists and may be
  taken finite separable over `k`.

## Implementation notes

The point of the base change is produced before anything is said about it, and the equality of
its image with `x` is then substituted away; this is what keeps every statement about the two
local rings free of `AlgebraicGeometry.Scheme.residueFieldCongr`, whose presence makes the
identification of the two residue-field maps cost more than the heartbeat budget allows.

The `k`-algebra structures on the local ring and on the residue field at a point are the ones
attached to `AlgebraicGeometry.fieldToStalk` and `AlgebraicGeometry.fieldToResidue`, matching
`Stacks.Curves.isNode_iff_isNodalAlgebra_stalk`.

## References

* [Stacks Project, Tag 0CBY](https://stacks.math.columbia.edu/tag/0CBY)
* [Stacks Project, Tag 0CBT](https://stacks.math.columbia.edu/tag/0CBT)
* [Stacks Project, Tag 0C50](https://stacks.math.columbia.edu/tag/0C50)
* [Stacks Project, Tag 0C56](https://stacks.math.columbia.edu/tag/0C56)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

universe u

namespace Stacks.Curves

/-- The isomorphism of residue fields attached to a proof that a point equals itself is the
identity; the proof is irrelevant. -/
private lemma residueFieldCongr_hom_of_eq_self (W : Scheme.{u}) (w : W) (h : w = w) :
    (W.residueFieldCongr h).hom = 𝟙 (W.residueField w) := by
  rw [show h = rfl from rfl, Scheme.residueFieldCongr_refl, Iso.refl_hom]

/-- A node of a one-dimensional scheme locally of finite type over `k` has a nodal local ring, for
the `k`-algebra structure attached to `fieldToStalk`. -/
private lemma isNodalAlgebra_stalk_of_isNode_fieldToStalk
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ AlgebraicGeometry.Spec (.of k))
    [LocallyOfFiniteType f] (hdim : topologicalKrullDim X = 1) (x : X)
    (hnode : letI : X.Over (AlgebraicGeometry.Spec (.of k)) := ⟨f⟩
      IsNode k X x) :
    letI : Algebra k (X.presheaf.stalk x) := (fieldToStalk f x).hom.toAlgebra
    IsNodalAlgebra k (X.presheaf.stalk x) :=
  letI : X.Over (AlgebraicGeometry.Spec (.of k)) := ⟨f⟩
  haveI : LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType f)
  (isNode_iff_isNodalAlgebra_stalk k X hdim x).mp hnode

/-- **A node becomes a split node after an extension of the ground field that splits its
quadratic algebra.** Let `x` be a node of a one-dimensional scheme `X` locally of finite type
over a field `k`, and let `ψ` be a `k`-algebra map from the quadratic algebra of the local ring
at `x` to a field `K`. Then the base change `X_K` has a point above `x` which is a split node of
`X_K` over `K`.

The point is the one whose residue field is `K`, which is what makes the residue-field clause of
`Stacks.Curves.IsSplitNode` hold; it is a node by Stacks Tag 0C56, and its quadratic algebra is
the trivial one because the local homomorphism of local rings extends the maximal ideal (Stacks
Tag 0C50). -/
theorem exists_isSplitNode_baseChange_of_quadraticAlgebraHom
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : Scheme.{u}) (f : X ⟶ AlgebraicGeometry.Spec (.of k)) [LocallyOfFiniteType f]
    (hdim : topologicalKrullDim X = 1) (x : X)
    (hnode : letI : X.Over (AlgebraicGeometry.Spec (.of k)) := ⟨f⟩
      IsNode k X x)
    (ψ : quadraticAlgebra (X.presheaf.stalk x) →+* K)
    (hψ : ∀ c : k, ψ (algebraMap (ResidueField (X.presheaf.stalk x))
        (quadraticAlgebra (X.presheaf.stalk x)) ((fieldToResidue f x).hom c)) =
      algebraMap k K c) :
    ∃ y : (pullback f (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}),
      (pullback.fst f (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap k K)))).base y = x ∧
      letI : (pullback f (AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}).Over
            (AlgebraicGeometry.Spec (.of K)) :=
        ⟨pullback.snd f (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K)))⟩
      IsSplitNode K (pullback f (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap k K)))) y := by
  have hσ : fieldToResidue f x ≫ CommRingCat.ofHom (ψ.comp (algebraMap
        (ResidueField (X.presheaf.stalk x)) (quadraticAlgebra (X.presheaf.stalk x)))) =
      CommRingCat.ofHom (algebraMap k K) :=
    CommRingCat.hom_ext (RingHom.ext fun c => hψ c)
  obtain ⟨y, hy, hbij, hcompat⟩ := AlgebraicGeometry.exists_baseChange_point_of_residueFieldHom
    f x (CommRingCat.ofHom (ψ.comp (algebraMap (ResidueField (X.presheaf.stalk x))
      (quadraticAlgebra (X.presheaf.stalk x))))) hσ
  refine ⟨y, hy, ?_⟩
  subst hy
  let : X.Over (AlgebraicGeometry.Spec (.of k)) := ⟨f⟩
  have : LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType f)
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : (pullback f (AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}).Over
        (AlgebraicGeometry.Spec (.of K)) :=
    ⟨pullback.snd f (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K)))⟩
  have : LocallyOfFiniteType ((pullback f (AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}) ↘
        AlgebraicGeometry.Spec (.of K)) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd f (AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (algebraMap k K)))))
  have : IsLocallyNoetherian (pullback f (AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f (AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (algebraMap k K))))
  -- the node upstairs, Stacks Tag 0C56
  have hnodeY : IsNode K (pullback f (AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}) y :=
    (isNode_iff_of_fieldExtension k K X f hdim _ y rfl).mp hnode
  have hdimY : topologicalKrullDim (pullback f (AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}) = 1 :=
    (AlgebraicGeometry.topologicalKrullDim_baseChange k K
      (pullback.fst f (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K))))
      (pullback.snd f (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K)))) f
      (IsPullback.of_hasPullback f (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap k K))))).trans hdim
  -- the two local rings, as algebras over the two ground fields and over one another
  let : Algebra k (X.presheaf.stalk ((pullback.fst f (AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (algebraMap k K)))).base y)) :=
    (fieldToStalk f ((pullback.fst f (AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (algebraMap k K)))).base y)).hom.toAlgebra
  let : Algebra K ((pullback f (AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}).presheaf.stalk y) :=
    (fieldToStalk (pullback.snd f (AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (algebraMap k K)))) y).hom.toAlgebra
  let : Algebra (X.presheaf.stalk ((pullback.fst f (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap k K)))).base y))
      ((pullback f (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}).presheaf.stalk y) :=
    ((pullback.fst f (AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (algebraMap k K)))).stalkMap y).hom.toAlgebra
  have : IsLocalHom (algebraMap (X.presheaf.stalk ((pullback.fst f (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap k K)))).base y))
      ((pullback f (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}).presheaf.stalk y)) := by
    rw [RingHom.algebraMap_toAlgebra]
    infer_instance
  -- the nodal algebras downstairs and upstairs, Stacks Tag 0C4D clause (2)
  have hA := isNodalAlgebra_stalk_of_isNode_fieldToStalk k X f hdim _ hnode
  have hB := isNodalAlgebra_stalk_of_isNode_fieldToStalk K _ (pullback.snd f
    (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K)))) hdimY y hnodeY
  -- the maximal ideal extends, Stacks Tag 0C50
  have hmax : Ideal.map (algebraMap (X.presheaf.stalk ((pullback.fst f
          (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K)))).base y))
        ((pullback f (AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}).presheaf.stalk y))
      (maximalIdeal (X.presheaf.stalk ((pullback.fst f (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap k K)))).base y))) =
      maximalIdeal ((pullback f (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}).presheaf.stalk y) := by
    rw [RingHom.algebraMap_toAlgebra]
    exact map_maximalIdeal_stalkMap_baseChange_eq_of_isSeparableExtension k K X f y hnode.1 hA.1
  rw [residueFieldCongr_hom_of_eq_self, Category.id_comp] at hcompat
  refine ⟨hnodeY, hbij,
    nonempty_quadraticAlgebra_algEquiv_prod_of_map_maximalIdeal_eq_of_ringHom k K hA hB hmax
      ((fieldToResidue (pullback.snd f (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap k K)))) y).hom.comp ψ) (fun z => ?_)⟩
  exact congrArg (fun φ : X.residueField ((pullback.fst f (AlgebraicGeometry.Spec.map
    (CommRingCat.ofHom (algebraMap k K)))).base y) ⟶
      (pullback f (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}).residueField y => φ.hom z) hcompat

/-- **A node becomes a split node after a finite separable extension of the ground field.** At a
node of a one-dimensional scheme locally of finite type over `k` whose residue field is finite
over `k`, there is a finite separable extension `K / k` and a point of the base change `X_K`
above the node which is a split node of `X_K` over `K`.

The extension is the residue field of a maximal ideal of the quadratic algebra of the node
(`Stacks.Curves.exists_finiteSeparable_algHom_quadraticAlgebra_over_base`); it realizes the
source's case distinction between a split and a non-split node uniformly. -/
theorem exists_finiteSeparable_isSplitNode_baseChange
    (k : Type u) [Field k]
    (X : Scheme.{u}) (f : X ⟶ AlgebraicGeometry.Spec (.of k)) [LocallyOfFiniteType f]
    (hdim : topologicalKrullDim X = 1) (x : X)
    (hnode : letI : X.Over (AlgebraicGeometry.Spec (.of k)) := ⟨f⟩
      IsNode k X x)
    (hfin : letI : Algebra k (X.presheaf.stalk x) := (fieldToStalk f x).hom.toAlgebra
      Module.Finite k (ResidueField (X.presheaf.stalk x))) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K) (_ : Module.Finite k K)
      (_ : Algebra.IsSeparableExtension k K)
      (y : (pullback f (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u})),
      (pullback.fst f (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap k K)))).base y = x ∧
      letI : (pullback f (AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}).Over
            (AlgebraicGeometry.Spec (.of K)) :=
        ⟨pullback.snd f (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K)))⟩
      IsSplitNode K (pullback f (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap k K)))) y := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : Algebra k (X.presheaf.stalk x) := (fieldToStalk f x).hom.toAlgebra
  have hA := isNodalAlgebra_stalk_of_isNode_fieldToStalk k X f hdim x hnode
  obtain ⟨L, hfld, halgres, halgk, htower, hfinL, hsepL, ⟨ψ₀⟩⟩ :=
    exists_finiteSeparable_algHom_quadraticAlgebra_over_base k (X.presheaf.stalk x) hA hfin
  let : Field L := hfld
  let : Algebra (ResidueField (X.presheaf.stalk x)) L := halgres
  let : Algebra k L := halgk
  let : IsScalarTower k (ResidueField (X.presheaf.stalk x)) L := htower
  have hψ : ∀ c : k, ψ₀.toRingHom (algebraMap (ResidueField (X.presheaf.stalk x))
      (quadraticAlgebra (X.presheaf.stalk x)) ((fieldToResidue f x).hom c)) =
      algebraMap k L c := by
    intro c
    exact (ψ₀.commutes ((fieldToResidue f x).hom c)).trans
      (IsScalarTower.algebraMap_apply k (ResidueField (X.presheaf.stalk x)) L c).symm
  obtain ⟨y, hy, hsplit⟩ := exists_isSplitNode_baseChange_of_quadraticAlgebraHom k L X f hdim x
    hnode ψ₀.toRingHom hψ
  exact ⟨L, hfld, halgk, hfinL, hsepL, y, hy, hsplit⟩

end Stacks.Curves

end
