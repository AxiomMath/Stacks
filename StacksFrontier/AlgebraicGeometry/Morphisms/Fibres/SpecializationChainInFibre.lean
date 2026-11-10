module

public import Mathlib.AlgebraicGeometry.Fiber
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.FibrePointResidueField
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.ClosedPointChain
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Trdeg
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Fibre

/-!
# A chain of immediate specializations inside a fibre

Let `f : X ⟶ S` be locally of finite type, let `x` be a point of `X` and set `s = f x`. The
fibre `X_s` is locally of finite type over the residue field `κ(s)`, so the general theory of
locally algebraic schemes applies to it: writing

`d = trdeg_{κ(s)}(κ(x))`,

the point `x`, viewed in `X_s`, is the head of a chain

`x ⤳ x₁ ⤳ x₂ ⤳ ⋯ ⤳ x_d`

of exactly `d` *immediate* specializations inside `X_s` whose last term is a closed point of
`X_s`; the integer `d` is also the dimension of the closure of `x` in `X_s`; and the chain can
be chosen to avoid any prescribed closed subset of `X_s` not containing `x`.

This is the content of Stacks 053V about the points `xᵢ` themselves. The remark asserts in
addition that the chain can be made to end in a prescribed `x'` with `x ⤳ x'` and `x'` closed in
`X_{f x'}`, i.e. that `x_d ⤳ x'`; that last link is precisely Stacks 053U, which is
`AlgebraicGeometry.closure_closedPoints_between_fiber_eq_iff` in
`StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.ClosedPointsBetweenInFibres` and is not used
here. Nothing is assumed about `x'` below, and nothing is concluded about it.

## On Stacks 05GV

Stacks 05GV, the other remark of the same section, records that Stacks 05GT, or its
scheme-theoretic variant Stacks 05GU, can be used to prove Stacks 053U again when `S` is locally
Noetherian, and sketches how. The theorem it asserts — Stacks 053U with `S` locally Noetherian
added — is proved by that route in
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.ClosedPointsFibre.DenseClosedPoints`; the two
lemmas the route uses are in
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.ClosedPointsFibre.LocalRing` (05GT) and
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.ClosedPointsFibre.ClosedSubscheme` (05GU).

## Main definitions

* `AlgebraicGeometry.natTrdegFiber` is the integer `d = trdeg_{κ(s)}(κ(x))` of the remark,
  computed in the fibre.

## Main results

* `AlgebraicGeometry.exists_chain_isImmediateSpecialization_isClosed_fiber`: the chain of `d`
  immediate specializations from `x` to a closed point of `X_s`, avoiding a prescribed closed
  subset of `X_s` which does not contain `x`.
* `AlgebraicGeometry.natTrdegFiber_eq_topologicalKrullDim_closure`: `d` is the dimension of the
  closure of `x` in `X_s`.
* `AlgebraicGeometry.natTrdegFiber_eq_toNat_trdeg_residueField`: `d` is the transcendence degree
  `trdeg_{κ(s)}(κ(x))` named in the remark, built on
  `AlgebraicGeometry.trdeg_fiberResidueField_eq_trdeg_residueField`, which identifies the
  residue field of the fibre at `f.asFiber x` with that of `X` at `x` as `κ(s)`-algebras.

## Implementation notes

The fibre is Mathlib's `f.fiber (f x)`, a pullback, with `f.asFiber x` the canonical point of
it over `x` and `f.fiberToSpecResidueField (f x)` its structure morphism to `Spec κ(s)`; that
morphism is locally of finite type by base change, which is the instance
`AlgebraicGeometry.Scheme.Hom.locallyOfFiniteType_fiberToSpecResidueField`. The avoidance
clause is obtained by running
the chain inside the open subscheme complementary to the prescribed closed set: an immediate
specialization in an open subscheme is immediate in the ambient scheme, and residue fields — so
also transcendence degrees — are unchanged by an open immersion, which is what keeps the length
of the chain and the closedness of its last term statements about `X_s` rather than about the
open piece.

`d` is a natural number, obtained from the cardinal-valued `Algebra.trdeg` through
`Cardinal.toNat`; this loses nothing because the degree is finite here.

## References

* [Stacks Project, Tag 053V](https://stacks.math.columbia.edu/tag/053V)
* [Stacks Project, Tag 053U](https://stacks.math.columbia.edu/tag/053U)
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- The transcendence degree of `κ(x)` over `κ(f x)`, computed at the canonical point of the
fibre `X_{f x}` and taken as a natural number. This is the integer `d` of Stacks 053V. -/
noncomputable def natTrdegFiber (f : X ⟶ S) (x : X) : ℕ :=
  natTrdegResidueField (S.residueField (f x)) (f.fiber (f x))
    (f.fiberToSpecResidueField (f x)) (f.asFiber x)

/-- **Stacks 053V**, the chain of immediate specializations inside the fibre, together with the
avoidance clause. For `f` locally of finite type and `W` a closed subset of the fibre `X_{f x}`
not containing `x`, there is a chain

`x = c 0 ⤳ c 1 ⤳ ⋯ ⤳ c d`

of `d = natTrdegFiber f x` immediate specializations inside `X_{f x}`, avoiding `W`, whose last
term is a closed point of `X_{f x}`. -/
@[stacks 053V "the chain of immediate specializations inside the fibre, of length `d`, ending in
a closed point of the fibre, together with the avoidance clause, and with nothing assumed about
a prescribed `x'`. The final link `x_d ⤳ x'` to a prescribed `x'` with `x ⤳ x'` closed in its
own fibre is not in this file, which never mentions `x'`; it is
`AlgebraicGeometry.exists_chain_isImmediateSpecialization_specializes_fiber_of_isClosed` in
`StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.SpecializationChainToClosedSpecialization`,
where `AlgebraicGeometry.exists_chain_isImmediateSpecialization_specializes_fiber_iff` states
every assertion of the remark at once, at the hypotheses of the tag, together with the exact
range of validity of the remark."]
theorem exists_chain_isImmediateSpecialization_isClosed_fiber
    (f : X ⟶ S) [LocallyOfFiniteType f] (x : X)
    {W : Set (f.fiber (f x))} (hW : IsClosed W) (hxW : f.asFiber x ∉ W) :
    ∃ c : Fin (natTrdegFiber f x + 1) → f.fiber (f x),
      c 0 = f.asFiber x ∧
      (∀ i : Fin (natTrdegFiber f x),
        IsImmediateSpecialization (c i.castSucc) (c i.succ)) ∧
      IsClosed ({c (Fin.last (natTrdegFiber f x))} : Set (f.fiber (f x))) ∧
      ∀ i, c i ∉ W := by
  let k := S.residueField (f x)
  let T := f.fiber (f x)
  let g : T ⟶ Spec (.of k) := f.fiberToSpecResidueField (f x)
  let : LocallyOfFiniteType g := inferInstance
  let V : T.Opens := ⟨Wᶜ, hW.isOpen_compl⟩
  let : LocallyOfFiniteType (V.ι ≫ g) :=
    AlgebraicGeometry.locallyOfFiniteType_comp V.ι g
  let p : V.toScheme := ⟨f.asFiber x, hxW⟩
  have hιp : V.ι p = f.asFiber x := rfl
  -- The degree at `p`, computed in the open subscheme, is the degree at `x` in the fibre.
  have hdeg : ∀ q : V.toScheme,
      natTrdegResidueField k V.toScheme (V.ι ≫ g) q =
        natTrdegResidueField k T g (V.ι q) := fun q ↦
    (congrArg Cardinal.toNat (trdeg_residueField_of_surjectiveOnStalks k g V.ι q)).symm
  have hp : natTrdegResidueField k V.toScheme (V.ι ≫ g) p = natTrdegFiber f x := by
    rw [hdeg p, hιp]
    rfl
  rw [← hp]
  obtain ⟨c, hc0, hcstep, hclosed⟩ :=
    exists_chain_isImmediateSpecialization_isClosed k V.toScheme (V.ι ≫ g) p
  refine ⟨fun i ↦ V.ι (c i), by simpa only [hc0] using hιp, fun i ↦ ?_, ?_, fun i ↦ (c i).2⟩
  · exact isImmediateSpecialization_val_of_isOpen V.isOpen (hcstep i)
  · refine isClosed_singleton_of_natTrdegResidueField_eq_zero k T g _ ?_
    rw [← hdeg]
    exact natTrdegResidueField_eq_zero_of_isClosed k V.toScheme (V.ι ≫ g) _ hclosed

/-- **Stacks 053V**, the identity `d = dim(closure of {x})`, the closure being taken in the
fibre `X_{f x}`. -/
@[stacks 053V "the equality of `d` with the dimension of the closure of `x` in the fibre"]
theorem natTrdegFiber_eq_topologicalKrullDim_closure (f : X ⟶ S) [LocallyOfFiniteType f]
    (x : X) :
    ((natTrdegFiber f x : ℕ∞) : WithBot ℕ∞) =
      topologicalKrullDim (closure ({f.asFiber x} : Set (f.fiber (f x)))) := by
  let k := S.residueField (f x)
  let T := f.fiber (f x)
  let g : T ⟶ Spec (.of k) := f.fiberToSpecResidueField (f x)
  let : LocallyOfFiniteType g := inferInstance
  let x₀ : T := f.asFiber x
  let : Algebra k (T.residueField x₀) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop ≫ T.Γevaluation x₀).hom.toAlgebra
  -- The dimension of the closure, computed on the reduced induced subscheme structure.
  let I := Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x₀} : Set T))
  let y : I.subscheme := ⟨x₀, subset_closure (Set.mem_singleton x₀)⟩
  have : IrreducibleSpace I.subscheme :=
    Subtype.irreducibleSpace (isIrreducible_singleton (x := x₀)).closure
  have hy : IsGenericPoint y (Set.univ : Set I.subscheme) :=
    isGenericPoint_iff_specializes.mpr fun z ↦ iff_of_true
      (Topology.IsInducing.subtypeVal.specializes_iff.mp
        (show x₀ ⤳ z.1 from specializes_iff_mem_closure.mpr z.2)) (Set.mem_univ z)
  let : LocallyOfFiniteType (I.subschemeι ≫ g) := locallyOfFiniteType_comp I.subschemeι g
  have hdim := topologicalKrullDim_eq_trdeg_residueField k I.subscheme (I.subschemeι ≫ g) y hy
  rw [← trdeg_residueField_of_surjectiveOnStalks k g I.subschemeι y] at hdim
  -- Pass from the cardinal degree to the natural number.
  let : FinTrdeg k (T.residueField x₀) := residueField_finTrdeg k g x₀
  have hcast : ((natTrdegFiber f x : ℕ∞) : WithBot ℕ∞) =
      (Cardinal.toENat (Algebra.trdeg k (T.residueField x₀)) : WithBot ℕ∞) := by
    congr 1
    exact ENat.natCast_toNat (Cardinal.toENat_eq_top.not.mpr (not_le_of_gt (trdeg_lt_aleph0 k _)))
  exact hcast.trans hdim.symm

/-- The transcendence degree of the residue field of the fibre `X_{f x}` at `f.asFiber x` over
`κ(f x)` is that of the residue field of `X` at `x`: the two residue fields are identified by
`AlgebraicGeometry.fiberResidueFieldEquiv`, compatibly with `κ(f x)`. -/
theorem trdeg_fiberResidueField_eq_trdeg_residueField (f : X ⟶ S) (x : X) :
    letI := (f.residueFieldMap x).hom.toAlgebra
    letI : Algebra (S.residueField (f x))
        ((f.fiber (f x)).residueField (f.asFiber x)) :=
      ((Scheme.ΓSpecIso (.of (S.residueField (f x)))).inv ≫
        (f.fiberToSpecResidueField (f x)).appTop ≫
        (f.fiber (f x)).Γevaluation (f.asFiber x)).hom.toAlgebra
    Algebra.trdeg (S.residueField (f x)) ((f.fiber (f x)).residueField (f.asFiber x)) =
      Algebra.trdeg (S.residueField (f x)) (X.residueField x) := by
  let k := S.residueField (f x)
  let g : f.fiber (f x) ⟶ Spec (.of k) := f.fiberToSpecResidueField (f x)
  let : Algebra k ((f.fiber (f x)).residueField (f.asFiber x)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop ≫
      (f.fiber (f x)).Γevaluation (f.asFiber x)).hom.toAlgebra
  let : Algebra k (X.residueField x) := (f.residueFieldMap x).hom.toAlgebra
  have halg : CommRingCat.ofHom
      (algebraMap k ((f.fiber (f x)).residueField (f.asFiber x))) =
      (Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop ≫
        (f.fiber (f x)).Γevaluation (f.asFiber x) := rfl
  have hspec : Spec.map (CommRingCat.ofHom
      (algebraMap k ((f.fiber (f x)).residueField (f.asFiber x)))) =
      (f.fiber (f x)).fromSpecResidueField (f.asFiber x) ≫ g := by
    rw [← cancel_mono (Spec (CommRingCat.of k)).isoSpec.hom]
    change _ ≫ (Spec _).toSpecΓ = _ ≫ (Spec _).toSpecΓ
    conv_rhs => rw [Category.assoc, Scheme.toSpecΓ_naturality]
    simp only [Scheme.fromSpecResidueField, Category.assoc,
      Scheme.fromSpecStalk_toSpecΓ_assoc, ← Spec.map_comp]
    rw [← SpecMap_ΓSpecIso_hom, ← Spec.map_comp, Spec.map_inj, halg]
    change ((((Scheme.ΓSpecIso (CommRingCat.of k)).hom ≫
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv) ≫ g.appTop) ≫
        (f.fiber (f x)).Γevaluation (f.asFiber x)) = _
    rw [Iso.hom_inv_id, Category.id_comp]
    rfl
  exact AlgEquiv.trdeg_eq (R := k) <| AlgEquiv.ofRingEquiv (f := fiberResidueFieldEquiv f x) (by
      intro z
      have hh : CommRingCat.ofHom ((fiberResidueFieldEquiv f x).toRingHom.comp
          (algebraMap k ((f.fiber (f x)).residueField (f.asFiber x)))) =
          CommRingCat.ofHom (algebraMap k (X.residueField x)) := by
        apply Spec.map_injective
        rw [CommRingCat.ofHom_comp, Spec.map_comp, hspec, ← Category.assoc,
          fiberResidueFieldEquiv_spec, f.asFiberHom_fiberToSpecResidueField]
        rfl
      exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hh) z)

/-- **Stacks 053V**, the identity `d = trdeg_{κ(s)}(κ(x))`: the integer produced by
`AlgebraicGeometry.natTrdegFiber` is the transcendence degree of the residue field of `X` at `x`
over the residue field of `S` at `s = f x`. -/
@[stacks 053V "the equality of the length `d` of the chain with the transcendence degree
`trdeg_{κ(s)}(κ(x))`"]
theorem natTrdegFiber_eq_toNat_trdeg_residueField (f : X ⟶ S) (x : X) :
    letI := (f.residueFieldMap x).hom.toAlgebra
    natTrdegFiber f x =
      Cardinal.toNat (Algebra.trdeg (S.residueField (f x)) (X.residueField x)) := by
  let : Algebra (S.residueField (f x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  exact congrArg Cardinal.toNat (trdeg_fiberResidueField_eq_trdeg_residueField f x)

end AlgebraicGeometry

end
