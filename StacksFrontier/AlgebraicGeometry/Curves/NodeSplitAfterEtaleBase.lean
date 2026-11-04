module

public import StacksFrontier.AlgebraicGeometry.Curves.NodeSplitAfterFieldExtension
public import StacksFrontier.AlgebraicGeometry.Curves.SplitNodeIsoTransfer
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.ResidueField
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.SpecializationTrdeg
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.ResidueField
public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.Separable

/-!
# A node of a fibre becomes split after an étale base change

Let `f : X ⟶ S` be a morphism locally of finite type, let `t` be a point of `X` whose image
`s = f t` has a one-dimensional fibre, and suppose `t` is a node of that fibre `X_s` over
`κ(s)`. There is then an étale morphism `V ⟶ S` and a point `t'` of `X ×_S V` above `t` at
which the node of the fibre of `X ×_S V ⟶ V` is *split*.

This is the étale-neighbourhood form of the reduction of Stacks Tag 0CBY to the case of a split
node, and it is stated in exactly the spelling that Stacks Tag 0CBX consumes: for `f'` the
family `X ×_S V ⟶ V`, the conclusion is
`IsSplitNode κ(f' t') (f'.fiber (f' t')) (f'.asFiber t')`.

Three steps make it up.

* The curve `X_s` over `κ(s)` acquires a split node over a finite separable extension `L/κ(s)`
  (`Stacks.Curves.exists_finiteSeparable_algHom_quadraticAlgebra_over_base` for the choice of
  `L`, then `Stacks.Curves.exists_isSplitNode_baseChange_of_quadraticAlgebraHom`). Finiteness of
  `κ(t)/κ(s)`, which the choice of `L` needs, is Stacks Tag 01TF
  (`AlgebraicGeometry.isClosed_asFiber_iff_finite_residueField`) at the closed point `t` of the
  fibre, read on the fibre's own residue field through
  `AlgebraicGeometry.nonempty_fiberResidueFieldAlgEquiv`.
* That `L` is realized as the residue field of an étale neighbourhood `(V, v)` of `(S, s)`,
  which is Stacks Tag 02LF
  (`AlgebraicGeometry.exists_etaleNeighborhood_residueField_algEquiv`).
* The fibre of `X ×_S V ⟶ V` over `v` *is* the base change of `X_s` along `κ(s) → κ(v)`:
  Mathlib's `AlgebraicGeometry.isPullback_fiberToSpecResidueField_of_isPullback`, applied to the
  cartesian square defining `X ×_S V`, presents it as a pullback of the same cospan, and
  `CategoryTheory.IsPullback.isoIsPullback` together with `Stacks.Curves.isSplitNode_of_isIso`
  carries the split node across.

## Main results

* `Stacks.Curves.exists_isSplitNode_fiber_baseChange_of_quadraticAlgebraHom` — the fibre
  comparison: an algebra map from the quadratic algebra of the node to `κ(v)` makes the node of
  the fibre of `X ×_S V ⟶ V` over `v` split.
* `Stacks.Curves.exists_etale_isSplitNode_fiber_baseChange` — the étale neighbourhood of the
  base over which the node becomes split.

## Implementation notes

The base point `s` of the fibre and the equality `eV v = s` are arguments of
`Stacks.Curves.exists_isSplitNode_fiber_baseChange_of_quadraticAlgebraHom`, which substitutes
the equality away at once. That is what keeps every statement about the fibre free of
`AlgebraicGeometry.Scheme.residueFieldCongr`: the étale neighbourhood of Tag 02LF comes with its
residue-field map built from such a congruence, and transporting the quadratic algebra and the
structure map of the fibre along it, rather than substituting, costs more than the heartbeat
budget allows.

For the same reason the predicate `Stacks.Curves.IsSplitNode` is moved between the two
presentations of the same point of the same fibre by
`Stacks.Curves.isSplitNode_fiber_congr`, a substitution-based congruence, rather than by
rewriting inside it.

Only the fibre over the image of `t` is required to be one-dimensional, which is what the
hypothesis of Tag 0CBY — `f` at-worst-nodal of relative dimension one — gives for every nonempty
fibre (`AlgebraicGeometry.isAtWorstNodalOfRelativeDimensionOne_iff_fibres`). No flatness and no
finite presentation are used.

## References

* [Stacks Project, Tag 0CBY](https://stacks.math.columbia.edu/tag/0CBY)
* [Stacks Project, Tag 0CBX](https://stacks.math.columbia.edu/tag/0CBX)
* [Stacks Project, Tag 02LF](https://stacks.math.columbia.edu/tag/02LF)
* [Stacks Project, Tag 01TF](https://stacks.math.columbia.edu/tag/01TF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

universe u

namespace Stacks.Curves

variable {X S V : Scheme.{u}}

/-- **Being a split node of a fibre is transported along an equality of base points.** For two
equal points of the target the two fibres are the same scheme over the same residue field, so a
point of one is a split node exactly when the corresponding point of the other is. -/
theorem isSplitNode_fiber_congr (g : X ⟶ V) {v v' : V} (h : v = v') (z : g.fiber v) :
    letI := g.fiberOverSpecResidueField v
    letI := g.fiberOverSpecResidueField v'
    (IsSplitNode (V.residueField v) (g.fiber v) z ↔
      IsSplitNode (V.residueField v') (g.fiber v') (h ▸ z)) := by
  subst h
  exact Iff.rfl

/-- The map from a fibre to the spectrum of the residue field is locally of finite type. -/
private theorem locallyOfFiniteType_fiberToSpecResidueField (f : X ⟶ S) [LocallyOfFiniteType f]
    (s : S) : LocallyOfFiniteType (f.fiberToSpecResidueField s) := by
  dsimp only [Scheme.Hom.fiberToSpecResidueField, Scheme.Hom.fiber]
  infer_instance

/-- **The fibre of the base change along `V ⟶ S` has a split node over the residue field of
`v`.** Let `f : X ⟶ S` be locally of finite type, let `v` be a point of `V` over `s`, let `z` be
a node of the one-dimensional fibre `X_s` over `κ(s)`, and let `ψ` be a `κ(s)`-algebra map from
the quadratic algebra of the local ring at `z` into `κ(v)`. Then the fibre of
`X ×_S V ⟶ V` over `v` has a split node above `z`.

The fibre of the base change is a pullback of `X_s ⟶ Spec κ(s)` along `Spec κ(v) ⟶ Spec κ(s)`
(`AlgebraicGeometry.isPullback_fiberToSpecResidueField_of_isPullback`), which is the shape in
which `Stacks.Curves.exists_isSplitNode_baseChange_of_quadraticAlgebraHom` delivers the split
node; the two pullbacks of the one cospan are identified by
`CategoryTheory.IsPullback.isoIsPullback` and the split node is carried across by
`Stacks.Curves.isSplitNode_of_isIso`. -/
theorem exists_isSplitNode_fiber_baseChange_of_quadraticAlgebraHom
    (f : X ⟶ S) [LocallyOfFiniteType f] (eV : V ⟶ S) (v : V) (s : S) (hvs : eV v = s)
    (hdim : topologicalKrullDim (f.fiber s) = 1) (z : f.fiber s)
    (hnode : letI := f.fiberOverSpecResidueField s
      IsNode (S.residueField s) (f.fiber s) z)
    (ψ : quadraticAlgebra ((f.fiber s).presheaf.stalk z) →+* ↥(V.residueField v))
    (hψ : ∀ c : S.residueField s,
      ψ (algebraMap (ResidueField ((f.fiber s).presheaf.stalk z))
          (quadraticAlgebra ((f.fiber s).presheaf.stalk z))
          ((fieldToResidue (f.fiberToSpecResidueField s) z).hom c)) =
        ((S.residueFieldCongr hvs).inv ≫ eV.residueFieldMap v).hom c) :
    ∃ z' : (pullback.snd f eV).fiber v,
      (pullback.fst f eV).base ((pullback.snd f eV).fiberι v z') = f.fiberι s z ∧
      letI := (pullback.snd f eV).fiberOverSpecResidueField v
      IsSplitNode (V.residueField v) ((pullback.snd f eV).fiber v) z' := by
  subst hvs
  have hLOFT := locallyOfFiniteType_fiberToSpecResidueField f (eV v)
  let : Algebra ↥(S.residueField (eV v)) ↥(V.residueField v) :=
    (eV.residueFieldMap v).hom.toAlgebra
  have hψ' : ∀ c : S.residueField (eV v),
      ψ (algebraMap (ResidueField ((f.fiber (eV v)).presheaf.stalk z))
          (quadraticAlgebra ((f.fiber (eV v)).presheaf.stalk z))
          ((fieldToResidue (f.fiberToSpecResidueField (eV v)) z).hom c)) =
        algebraMap ↥(S.residueField (eV v)) ↥(V.residueField v) c := by
    intro c
    rw [hψ c, Scheme.residueFieldCongr_refl, Iso.refl_inv, Category.id_comp]
    rfl
  -- the split node of the base change of the fibre, from the curve-level reduction
  obtain ⟨y, hy, hsplit⟩ := exists_isSplitNode_baseChange_of_quadraticAlgebraHom
    (S.residueField (eV v)) (V.residueField v) (f.fiber (eV v))
    (f.fiberToSpecResidueField (eV v)) hdim z hnode ψ hψ'
  -- the fibre of the base change, as a pullback of the same cospan
  obtain ⟨m, hm, hmfst⟩ : ∃ m : (pullback.snd f eV).fiber v ⟶ f.fiber (eV v),
      IsPullback m ((pullback.snd f eV).fiberToSpecResidueField v)
        (f.fiberToSpecResidueField (eV v)) (Spec.map (eV.residueFieldMap v)) ∧
      m ≫ f.fiberι (eV v) = (pullback.snd f eV).fiberι v ≫ pullback.fst f eV :=
    ⟨_, isPullback_fiberToSpecResidueField_of_isPullback
      (IsPullback.of_hasPullback f eV) v, pullback.lift_fst _ _ _⟩
  have hpb := IsPullback.of_hasPullback (f.fiberToSpecResidueField (eV v))
    (Spec.map (CommRingCat.ofHom
      (algebraMap ↥(S.residueField (eV v)) ↥(V.residueField v))))
  have hdimP : topologicalKrullDim
      (pullback (f.fiberToSpecResidueField (eV v)) (Spec.map (CommRingCat.ofHom
        (algebraMap ↥(S.residueField (eV v)) ↥(V.residueField v)))) : Scheme.{u}) = 1 :=
    (topologicalKrullDim_baseChange ↥(S.residueField (eV v)) ↥(V.residueField v) _ _
      (f.fiberToSpecResidueField (eV v)) hpb).trans hdim
  let e := hpb.isoIsPullback _ _ hm
  have hinv : e.inv.base (e.hom.base y) = y :=
    congrArg (fun φ : (_ : Scheme.{u}) ⟶ _ => φ.base y) e.hom_inv_id
  refine ⟨e.hom.base y, ?_, ?_⟩
  · have h1 : m.base (e.hom.base y) = z :=
      (congrArg (fun φ : (_ : Scheme.{u}) ⟶ _ => φ.base y)
        (hpb.isoIsPullback_hom_fst _ _ hm)).trans hy
    have h2 := congrArg (fun φ : (pullback.snd f eV).fiber v ⟶ X => φ.base (e.hom.base y)) hmfst
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, h1] at h2
    exact h2.symm
  · refine isSplitNode_of_isIso (V.residueField v) _ _ (pullback.snd _ _) hdimP e.inv
      ((pullback.snd f eV).fiberToSpecResidueField v)
      (hpb.isoIsPullback_inv_snd _ _ hm) (e.hom.base y) ?_
    rwa [hinv]

/-- **A node of a fibre becomes split after an étale base change.** Let `f : X ⟶ S` be locally
of finite type and let `t` be a point of `X` which is a node of the one-dimensional fibre over
its image. There is an étale morphism `V ⟶ S` and a point `t'` of `X ×_S V` above `t` which is a
*split* node of the fibre of `X ×_S V ⟶ V` through it.

This is the reduction of Stacks Tag 0CBY to a split node, in the spelling that Tag 0CBX
consumes. The residue field of `V` at the chosen point is the finite separable extension of
`κ(f t)` over which the quadratic algebra of the node acquires a rational point, realized by
Stacks Tag 02LF. -/
theorem exists_etale_isSplitNode_fiber_baseChange (f : X ⟶ S) [LocallyOfFiniteType f] (t : X)
    (hdim : topologicalKrullDim (f.fiber (f t)) = 1)
    (hnode : letI := f.fiberOverSpecResidueField (f t)
      IsNode (S.residueField (f t)) (f.fiber (f t)) (f.asFiber t)) :
    ∃ (W : Scheme.{u}) (eW : W ⟶ S) (_ : Etale eW) (t' : (pullback f eW : Scheme.{u})),
      (pullback.fst f eW).base t' = t ∧
      letI := (pullback.snd f eW).fiberOverSpecResidueField ((pullback.snd f eW).base t')
      IsSplitNode (W.residueField ((pullback.snd f eW).base t'))
        ((pullback.snd f eW).fiber ((pullback.snd f eW).base t'))
        ((pullback.snd f eW).asFiber t') := by
  let := f.fiberOverSpecResidueField (f t)
  have hLOFT := locallyOfFiniteType_fiberToSpecResidueField f (f t)
  have hLOFT' : LocallyOfFiniteType (f.fiber (f t) ↘ Spec (.of ↥(S.residueField (f t)))) := hLOFT
  let : Algebra ↥(S.residueField (f t))
      ↥((f.fiber (f t)).presheaf.stalk (f.asFiber t)) :=
    (fieldToStalk (f.fiberToSpecResidueField (f t)) (f.asFiber t)).hom.toAlgebra
  have hLN := LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField (f t))
  -- Stacks Tag 0C4D, clauses (1) and (2): the local ring of the node is a nodal algebra
  have hA : IsNodalAlgebra ↥(S.residueField (f t))
      ↥((f.fiber (f t)).presheaf.stalk (f.asFiber t)) :=
    (isNode_iff_isNodalAlgebra_stalk (S.residueField (f t)) (f.fiber (f t)) hdim
      (f.asFiber t)).mp hnode
  -- Stacks Tag 01TF: the residue field at the node is finite over the residue field of the base
  have hfin : Module.Finite ↥(S.residueField (f t))
      (ResidueField ↥((f.fiber (f t)).presheaf.stalk (f.asFiber t))) := by
    let : Algebra ↥(S.residueField (f t)) ↥(X.residueField t) :=
      (f.residueFieldMap t).hom.toAlgebra
    let : Algebra ↥(S.residueField (f t))
        ↥((f.fiber (f t)).residueField (f.asFiber t)) :=
      (fieldToResidue (f.fiberToSpecResidueField (f t)) (f.asFiber t)).hom.toAlgebra
    have hXfin : Module.Finite ↥(S.residueField (f t)) ↥(X.residueField t) :=
      (isClosed_asFiber_iff_finite_residueField f t).mp hnode.1
    obtain ⟨ε⟩ := nonempty_fiberResidueFieldAlgEquiv f t
    exact Module.Finite.of_surjective ε.symm.toLinearMap ε.symm.surjective
  -- the finite separable extension of the ground field that splits the quadratic algebra
  obtain ⟨L, hfld, halgres, halgk, htower, hfinL, hsepL, ⟨ψ₀⟩⟩ :=
    exists_finiteSeparable_algHom_quadraticAlgebra_over_base (S.residueField (f t))
      ↥((f.fiber (f t)).presheaf.stalk (f.asFiber t)) hA hfin
  let : Field L := hfld
  let : Algebra (ResidueField ↥((f.fiber (f t)).presheaf.stalk (f.asFiber t))) L := halgres
  let : Algebra ↥(S.residueField (f t)) L := halgk
  have : IsScalarTower ↥(S.residueField (f t))
    (ResidueField ↥((f.fiber (f t)).presheaf.stalk (f.asFiber t))) L := htower
  have : Module.Finite ↥(S.residueField (f t)) L := hfinL
  let : Algebra.IsSeparableExtension ↥(S.residueField (f t)) L := hsepL
  have : Algebra.IsSeparable ↥(S.residueField (f t)) L :=
    Stacks.AlgebraicGeometry.ProperSectionsGeom.isSeparable_of_isSeparableExtension
      ↥(S.residueField (f t)) L
  -- Stacks Tag 02LF: that extension is the residue field of an étale neighbourhood of the base
  obtain ⟨U, ⟨ε⟩⟩ := exists_etaleNeighborhood_residueField_algEquiv S (f t) L
  let : Algebra ↥(S.residueField (f t)) ↥(U.scheme.residueField U.point) :=
    U.residueFieldMap.hom.toAlgebra
  -- the quadratic algebra of the node acquires a point with values in that residue field
  have hψ : ∀ c : S.residueField (f t),
      (ε.symm.toRingEquiv.toRingHom.comp ψ₀.toRingHom)
        (algebraMap (ResidueField ↥((f.fiber (f t)).presheaf.stalk (f.asFiber t)))
          (quadraticAlgebra ↥((f.fiber (f t)).presheaf.stalk (f.asFiber t)))
          ((fieldToResidue (f.fiberToSpecResidueField (f t)) (f.asFiber t)).hom c)) =
        ((S.residueFieldCongr U.map_point).inv ≫
          U.toBase.residueFieldMap U.point).hom c := by
    intro c
    change ε.symm (ψ₀ (algebraMap _ _ (algebraMap _ _ c))) = _
    rw [ψ₀.commutes, ← IsScalarTower.algebraMap_apply, ε.symm.commutes]
    rfl
  obtain ⟨z', hz', hsplit⟩ := exists_isSplitNode_fiber_baseChange_of_quadraticAlgebraHom
    f U.toBase U.point (f t) U.map_point hdim (f.asFiber t) hnode
    (ε.symm.toRingEquiv.toRingHom.comp ψ₀.toRingHom) hψ
  refine ⟨U.scheme, U.toBase, inferInstance, (pullback.snd f U.toBase).fiberι U.point z',
    hz'.trans (f.fiberι_asFiber t), (isSplitNode_fiber_congr (pullback.snd f U.toBase)
      ((pullback.snd f U.toBase).apply_fiberι U.point z')
      ((pullback.snd f U.toBase).asFiber _)).mpr ?_⟩
  rwa [Scheme.Hom.cast_asFiber_fiberι]

end Stacks.Curves

end
