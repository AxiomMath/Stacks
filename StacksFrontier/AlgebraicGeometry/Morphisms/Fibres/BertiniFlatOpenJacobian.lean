module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniResiduePointDivisor

/-!
# The Bertini dimension count run over the open where the universal family is flat

Work in the standing situation of the Bertini theorems ([Stacks, Tag 0G47]) with `X` smooth over
an algebraically closed field `k` and of finite type over it, under hypotheses (2) and (3) of
[Stacks, Tag 0FD6]. This module closes the dimension count of the proof of that tag against
**one** geometric input, the Jacobian criterion, and — unlike
`StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniEvaluationFibreBound` and
`StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniEvaluationMatrix`, which ask for that
input at every closed point of `H_univ` — asks for it only at the closed points of `q⁻¹(W)` for
an open `W ⊂ 𝔸^r_k` **over which `q` is flat**, flatness being supplied by
`Stacks.Bertini.FamilyDivisors.exists_nonempty_opens_flat_universalFamilyMapOver`.

That is the shape the Jacobian criterion can actually be applied in: smoothness of `q` at a point
of a fibre follows from regularity of the fibre at that point only in the presence of flatness
(`AlgebraicGeometry.smoothAt_fiberι_of_notMem_maximalSqSmul`), and flatness of `q` is available
only over an open of the parameter space. Restricting the count to such an open is legitimate
because the conclusion of Tag 0FD6 is itself a statement over some nonempty open: the two opens
are intersected at the end, and `𝔸^r_k` is irreducible, so the intersection is again nonempty.

## Main results

* `Stacks.Bertini.FamilyDivisors.topologicalKrullDim_fiber_nonSmoothToXOver_le_of_evalSubspace`:
  the fibre bound `r - #τ` for `Σ_W → X` over a closed point of `X`.
* `Stacks.Bertini.FamilyDivisors.exists_nonempty_opens_subset_smoothLocus_of_evalSubspace_over`:
  **`hsing`** from the Jacobian criterion over `W`.
* `Stacks.Bertini.FamilyDivisors.exists_nonempty_opens_subset_smoothLocus_of_jacobian_flat` and
  `Stacks.Bertini.FamilyDivisors.smooth_specializedDivisor_forGeneral_of_jacobian_flat`:
  **`hsing` and the conclusion of [Stacks, Tag 0FD6]** from the Jacobian criterion with flatness
  available: the hypothesis quantifies over the opens `W` of the parameter space over which the
  restricted family `q⁻¹(W) → 𝔸^r_k` is flat, and the flat open itself is produced here.
* `Stacks.Bertini.FamilyDivisors.JacobianAtDivisor`: the Jacobian criterion in the Bertini
  situation, in the shape that is left once the dimension count, the flatness and the
  identification of the fibre of `q` with a divisor are all discharged — smoothness of one
  divisor at one point.
* `Stacks.Bertini.FamilyDivisors.exists_nonempty_opens_subset_smoothLocus_of_jacobianAtDivisor`
  and
  `Stacks.Bertini.FamilyDivisors.smooth_specializedDivisor_forGeneral_of_jacobianAtDivisor`:
  **`hsing` and the conclusion of [Stacks, Tag 0FD6] from that criterion.**
* the `_pointwise` forms of those two: the same conclusions with **no dimension data assumed at
  all**, the count being run at each closed point of `X` with the local dimension of `X` there.
* the `_pointwise_of_basis` forms, which in addition take **hypothesis (3) at an arbitrary basis
  of the linear system**: the basis at which the immersion hypothesis is taken and the basis the
  Jacobian criterion is stated against are separate parameters. The `_pointwise` forms are the
  case of the two coinciding.
* the `_of_basis` forms of the four results that do assume the dimension data —
  `…exists_nonempty_opens_subset_smoothLocus_of_jacobian_flat_of_basis`,
  `…smooth_specializedDivisor_forGeneral_of_jacobian_flat_of_basis`,
  `…exists_nonempty_opens_subset_smoothLocus_of_jacobianAtDivisor_of_basis` and
  `…smooth_specializedDivisor_forGeneral_of_jacobianAtDivisor_of_basis` — which take hypothesis
  (3) at an arbitrary basis in the same way, and at an unrelated index type. Each is its
  unprimed sibling applied to the hypothesis transported by
  `Stacks.Bertini.FamilyDivisors.isImmersive_basis_of_isImmersive`, so nothing is proved twice.

## What is still an input

`Stacks.Bertini.FamilyDivisors.JacobianAtDivisor`, the hypothesis of the last two results. Given
an open `W` of the parameter space over which `q⁻¹(W) → 𝔸^r_k` is flat, a closed point `x` of
`X`, the matrix `M` of the evaluation `ev_x`, a closed point `w` of `q⁻¹(W)` lying over `x` at
which some form `∑ᵢ Mᵢⱼxᵢ` of the matrix does not vanish, and the point `z` of the fibre of `q`
through `w` — which is the divisor `H_a` of the residue coordinates `a` of `q(w)`,
`Stacks.Bertini.FamilyDivisors.parameterPoint_residueCoord` — it asks that `H_a` be smooth over
`κ(q(w))` at `z`.

That is the Jacobian criterion and nothing else: `H_a` is the zero scheme on `X_{κ(q(w))}` of the
single section `∑ᵢ aᵢψ(vᵢ)`, so
`AlgebraicGeometry.smoothAt_zeroScheme_of_notMem_maximalSqSmul_of_perfectField` reduces its
smoothness at `z` to the germ of that section at the image of `z` avoiding `𝔪²ℒ`
(`Stacks.LocalEquationJet.Γgerm_mem_maximalSqSmul_iff`), and the non-vanishing of a form of `M`
at `w` is exactly the non-vanishing of `ev_x` on the coordinate vector of `w`
(`Stacks.ImmersionEvaluationSurjective.evalCoord`). The remaining
ingredients — flatness of `q`, the cartesian square presenting the fibre, the passage from the
divisor back to the morphism — are proved: see
`Stacks.Bertini.FamilyDivisors.exists_nonempty_opens_flat_universalFamilyMapOver`,
`Stacks.Bertini.FamilyDivisors.parameterPoint_residueCoord` and
`Stacks.Bertini.FamilyDivisors.mem_smoothLocus_of_mem_smoothLocus_residueCoordDivisor`.

Accordingly **no `@[stacks]` attribute is attached**: Tag 0FD6 is registered on
`Stacks.Bertini.FamilyDivisors.forGeneral_smooth_specializedDivisor_of_isImmersion_`
`canonicalMorphism`.

## References

* [Stacks Project, Tag 0FD6](https://stacks.math.columbia.edu/tag/0FD6)
* [Stacks Project, Tag 0G47](https://stacks.math.columbia.edu/tag/0G47)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.ImmersionEvaluationSurjective

universe u v w

namespace Stacks.Bertini.FamilyDivisors

open Stacks.LinearSubspace

section Subspace

variable (D : FamilyDivisors.{u, v}) (W : D.parameterBase.Opens)

/-- **The linear subspace `L` of `H_univ` cut out by the forms of `M` over `x`, read inside
`q⁻¹(W)`.** -/
def evalSubspaceOver (x : D.X) {τ : Type w} [Fintype τ] (M : D.basisIndex → τ → D.k) :
    Set (D.universalDivisorSchemeOver W).toScheme :=
  (D.universalDivisorSchemeOver W).ι.base ⁻¹' D.evalSubspace x M

/-- **`L ∩ q⁻¹(W)` is closed in `q⁻¹(W)`.** -/
theorem isClosed_evalSubspaceOver {x : D.X} (hx : IsClosed ({x} : Set D.X)) {τ : Type w}
    [Fintype τ] (M : D.basisIndex → τ → D.k) : IsClosed (D.evalSubspaceOver W x M) :=
  (D.isClosed_evalSubspace hx M).preimage
    (D.universalDivisorSchemeOver W).ι.base.hom.continuous

/-- **`dim (L ∩ q⁻¹(W)) ≤ r - #τ`**: the open immersion of `q⁻¹(W)` is a topological embedding,
so the dimension of the part of `L` lying over `W` is at most that of `L`. -/
theorem topologicalKrullDim_evalSubspaceOver_le [IsAlgClosed D.k] [LocallyOfFiniteType D.toBase]
    {x : D.X} (hx : IsClosed ({x} : Set D.X)) {τ : Type w} [Fintype τ]
    (M : D.basisIndex → τ → D.k) (hM : Function.Surjective (coeffMap M)) :
    topologicalKrullDim (D.evalSubspaceOver W x M) ≤
      ((Nat.card D.basisIndex - Fintype.card τ : ℕ) : WithBot ℕ∞) := by
  have hemb : Topology.IsEmbedding (D.universalDivisorSchemeOver W).ι.base :=
    (D.universalDivisorSchemeOver W).ι.isOpenEmbedding.isEmbedding
  refine le_trans (le_of_eq (IsHomeomorph.topologicalKrullDim_eq _
    (hemb.homeomorphImage (D.evalSubspaceOver W x M)).isHomeomorph)) ?_
  refine le_trans (topologicalKrullDim_le_of_subset (Set.image_preimage_subset
    (D.universalDivisorSchemeOver W).ι.base (D.evalSubspace x M))) ?_
  exact D.topologicalKrullDim_evalSubspace_le hx M hM

/-- **The fibre bound over a closed point of `X`, from the Jacobian criterion at the closed
points of `q⁻¹(W)`.** If every closed point of `q⁻¹(W)` over `x` at which one of the forms of the
evaluation matrix `M` is nonzero is a point of smoothness of the restricted family, then the
fibre of the projection `Σ_W → X` over `x` has dimension at most `r - #τ`. -/
theorem topologicalKrullDim_fiber_nonSmoothToXOver_le_of_evalSubspace [Smooth D.toBase]
    [LocallyOfFiniteType D.toBase] [IsAlgClosed D.k] {x : D.X}
    (hx : IsClosed ({x} : Set D.X)) {τ : Type w} [Fintype τ] (M : D.basisIndex → τ → D.k)
    (hM : Function.Surjective (coeffMap M))
    (hsmooth : ∀ w : (D.universalDivisorSchemeOver W).toScheme,
      IsClosed ({w} : Set (D.universalDivisorSchemeOver W).toScheme) →
      D.parameterProjection.base (D.universalDivisor.subschemeι.base
        ((D.universalDivisorSchemeOver W).ι.base w)) = x →
      (∃ j, D.universalDivisor.subschemeι.base
        ((D.universalDivisorSchemeOver W).ι.base w) ∈
          D.parameterSpace.basicOpen (D.evalCoordForm M j)) →
      w ∈ (D.universalFamilyMapOver W).smoothLocus) :
    topologicalKrullDim ((D.nonSmoothToXOver W).fiber x) ≤
      ((Nat.card D.basisIndex - Fintype.card τ : ℕ) : WithBot ℕ∞) :=
  D.topologicalKrullDim_fiber_nonSmoothToXOver_le_of_closedPoints W hx
    (D.evalSubspaceOver W x M) (D.isClosed_evalSubspaceOver W hx M)
    (fun w hwc hwns hwx => D.mem_evalZeroSet.mpr ⟨hwx, fun j hj =>
      hwns (hsmooth w hwc hwx ⟨j, hj⟩)⟩)
    (D.topologicalKrullDim_evalSubspaceOver_le W hx M hM)

/-- **`hsing` of [Stacks, Tag 0FD6] from the Jacobian criterion at the closed points of
`q⁻¹(W)`.** With `#τ = n + 1`, `dim X ≤ n` and `n + 1 ≤ r`, and with the Jacobian criterion
available at the closed points of `q⁻¹(W)` over every closed point of `X`, there is a nonempty
open `U ⊂ 𝔸^r_k` whose preimage under `q` lies in the smooth locus of `q`. -/
theorem exists_nonempty_opens_subset_smoothLocus_of_evalSubspace_over [Smooth D.toBase]
    [LocallyOfFiniteType D.toBase] [NoetherianSpace D.universalDivisorScheme] [IsAlgClosed D.k]
    (hW : (W : Set D.parameterBase).Nonempty) {n : ℕ} (hnr : n + 1 ≤ Nat.card D.basisIndex)
    (hX : topologicalKrullDim D.X ≤ (n : WithBot ℕ∞))
    (M : ∀ x : D.X, IsClosed ({x} : Set D.X) → D.basisIndex → Fin (n + 1) → D.k)
    (hM : ∀ (x : D.X) (hx : IsClosed ({x} : Set D.X)),
      Function.Surjective (coeffMap (M x hx)))
    (hsmooth : ∀ (x : D.X) (hx : IsClosed ({x} : Set D.X))
      (w : (D.universalDivisorSchemeOver W).toScheme),
      IsClosed ({w} : Set (D.universalDivisorSchemeOver W).toScheme) →
      D.parameterProjection.base (D.universalDivisor.subschemeι.base
        ((D.universalDivisorSchemeOver W).ι.base w)) = x →
      (∃ j, D.universalDivisor.subschemeι.base
        ((D.universalDivisorSchemeOver W).ι.base w) ∈
          D.parameterSpace.basicOpen (D.evalCoordForm (M x hx) j)) →
      w ∈ (D.universalFamilyMapOver W).smoothLocus) :
    ∃ U : D.parameterBase.Opens, (U : Set D.parameterBase).Nonempty ∧
      ((D.universalFamilyMap ⁻¹ᵁ U : D.universalDivisorScheme.Opens) :
          Set D.universalDivisorScheme) ⊆
        (D.universalFamilyMap.smoothLocus : Set D.universalDivisorScheme) :=
  D.exists_nonempty_opens_subset_smoothLocus_of_fiber_le_over W hW hnr hX
    (D.fiber_nonSmoothToXOver_le_of_isClosed_singleton W fun x hx => by
      have h := D.topologicalKrullDim_fiber_nonSmoothToXOver_le_of_evalSubspace W hx (M x hx)
        (hM x hx) (hsmooth x hx)
      rwa [Fintype.card_fin] at h)

end Subspace

section Matrix

variable (D : FamilyDivisors.{u, u})

/-- **`hsing` of [Stacks, Tag 0FD6] from the Jacobian criterion with flatness available.** Under
hypotheses (2) and (3) of the tag, with `X` of finite type over `k`, of dimension `n` at each of
its closed points and of dimension at most `n`, and with the Jacobian criterion available at the
closed points of `q⁻¹(W)` for every open `W` of the parameter space over which the restricted
family is flat, there is a nonempty open `U ⊂ 𝔸^r_k` whose preimage under `q` lies in the smooth
locus of `q`.

The open over which the family is flat comes from generic flatness
(`Stacks.Bertini.FamilyDivisors.exists_nonempty_opens_flat_universalFamilyMapOver`), so no
flatness hypothesis is left in the signature; what `hjac` has to do is apply the Jacobian
criterion in the presence of the flatness it is handed. -/
theorem exists_nonempty_opens_subset_smoothLocus_of_jacobian_flat [IsAlgClosed D.k]
    [Smooth D.toBase] [QuasiCompact D.toBase] [NoetherianSpace D.universalDivisorScheme]
    {m n : ℕ} {b : Module.Basis (Fin (m + 1)) D.k D.V} {hb : D.GeneratesBy b}
    (himm : D.IsImmersive b hb) (hnr : n + 1 ≤ Nat.card D.basisIndex)
    (hX : topologicalKrullDim D.X ≤ (n : WithBot ℕ∞))
    (hdim : ∀ x : D.X, IsClosed ({x} : Set D.X) →
      topologicalKrullDimAt D.X x = (n : WithBot ℕ∞))
    (hjac : ∀ W : D.parameterBase.Opens, Flat (D.universalFamilyMapOver W) →
      ∀ x : D.X, IsClosed ({x} : Set D.X) →
      ∀ M : D.basisIndex → Fin (n + 1) → D.k,
      (∀ c : D.basisIndex → D.k, coeffMap M c = 0 ↔
        evalCoord (fun i => D.sectionOf (b i)) D.toBase x
          (fun l => c (D.basisIndexEquiv b l)) = 0) →
      ∀ w : (D.universalDivisorSchemeOver W).toScheme,
      IsClosed ({w} : Set (D.universalDivisorSchemeOver W).toScheme) →
      D.parameterProjection.base (D.universalDivisor.subschemeι.base
        ((D.universalDivisorSchemeOver W).ι.base w)) = x →
      (∃ j, D.universalDivisor.subschemeι.base
        ((D.universalDivisorSchemeOver W).ι.base w) ∈
          D.parameterSpace.basicOpen (D.evalCoordForm M j)) →
      w ∈ (D.universalFamilyMapOver W).smoothLocus) :
    ∃ U : D.parameterBase.Opens, (U : Set D.parameterBase).Nonempty ∧
      ((D.universalFamilyMap ⁻¹ᵁ U : D.universalDivisorScheme.Opens) :
          Set D.universalDivisorScheme) ⊆
        (D.universalFamilyMap.smoothLocus : Set D.universalDivisorScheme) := by
  have : LocallyOfFiniteType D.toBase := inferInstance
  obtain ⟨W, hW, hflat⟩ := D.exists_nonempty_opens_flat_universalFamilyMapOver
  choose M hMsurj hMker using fun (x : D.X) (hx : IsClosed ({x} : Set D.X)) =>
    D.exists_evalMatrix himm hx (hdim x hx)
  exact D.exists_nonempty_opens_subset_smoothLocus_of_evalSubspace_over W hW hnr hX M hMsurj
    (fun x hx => hjac W hflat x hx (M x hx) (hMker x hx))

/-- **`hsing` of [Stacks, Tag 0FD6] from the Jacobian criterion with flatness available and
hypothesis (3) at an arbitrary basis of the linear system.** This is
`Stacks.Bertini.FamilyDivisors.exists_nonempty_opens_subset_smoothLocus_of_jacobian_flat` with
the basis `b'` at which hypothesis (3) is taken and the basis `b` the Jacobian criterion is
stated against separate parameters, at unrelated index types; the hypothesis is transported onto
`b` by `Stacks.Bertini.FamilyDivisors.isImmersive_basis_of_isImmersive`, which supplies
hypothesis (2) at `b` as well. -/
theorem exists_nonempty_opens_subset_smoothLocus_of_jacobian_flat_of_basis [IsAlgClosed D.k]
    [Smooth D.toBase] [QuasiCompact D.toBase] [NoetherianSpace D.universalDivisorScheme]
    {m n p : ℕ} {b' : Module.Basis (Fin (p + 1)) D.k D.V} {hb' : D.GeneratesBy b'}
    (himm : D.IsImmersive b' hb') (b : Module.Basis (Fin (m + 1)) D.k D.V)
    (hnr : n + 1 ≤ Nat.card D.basisIndex)
    (hX : topologicalKrullDim D.X ≤ (n : WithBot ℕ∞))
    (hdim : ∀ x : D.X, IsClosed ({x} : Set D.X) →
      topologicalKrullDimAt D.X x = (n : WithBot ℕ∞))
    (hjac : ∀ W : D.parameterBase.Opens, Flat (D.universalFamilyMapOver W) →
      ∀ x : D.X, IsClosed ({x} : Set D.X) →
      ∀ M : D.basisIndex → Fin (n + 1) → D.k,
      (∀ c : D.basisIndex → D.k, coeffMap M c = 0 ↔
        evalCoord (fun i => D.sectionOf (b i)) D.toBase x
          (fun l => c (D.basisIndexEquiv b l)) = 0) →
      ∀ w : (D.universalDivisorSchemeOver W).toScheme,
      IsClosed ({w} : Set (D.universalDivisorSchemeOver W).toScheme) →
      D.parameterProjection.base (D.universalDivisor.subschemeι.base
        ((D.universalDivisorSchemeOver W).ι.base w)) = x →
      (∃ j, D.universalDivisor.subschemeι.base
        ((D.universalDivisorSchemeOver W).ι.base w) ∈
          D.parameterSpace.basicOpen (D.evalCoordForm M j)) →
      w ∈ (D.universalFamilyMapOver W).smoothLocus) :
    ∃ U : D.parameterBase.Opens, (U : Set D.parameterBase).Nonempty ∧
      ((D.universalFamilyMap ⁻¹ᵁ U : D.universalDivisorScheme.Opens) :
          Set D.universalDivisorScheme) ⊆
        (D.universalFamilyMap.smoothLocus : Set D.universalDivisorScheme) :=
  D.exists_nonempty_opens_subset_smoothLocus_of_jacobian_flat
    (D.isImmersive_basis_of_isImmersive himm b) hnr hX hdim hjac

/-- The conclusion of [Stacks, Tag 0FD6] from `hsing`, in the form of a nonempty open `U` whose
preimage lies in the smooth locus of `q`. -/
private theorem forGeneral_smooth_specializedDivisor_of_exists_opens [Smooth D.toBase]
    [LocallyOfFinitePresentation D.universalFamilyMap]
    (h : ∃ U : D.parameterBase.Opens, (U : Set D.parameterBase).Nonempty ∧
      ((D.universalFamilyMap ⁻¹ᵁ U : D.universalDivisorScheme.Opens) :
          Set D.universalDivisorScheme) ⊆
        (D.universalFamilyMap.smoothLocus : Set D.universalDivisorScheme)) :
    D.ForGeneral (fun K _ _ w =>
      ∀ a : Fin (Module.finrank D.k D.V) → K,
        w = ∑ i, TensorProduct.tmul D.k (D.basis i) (a i) →
          Smooth ((D.specializedDivisor K a).subschemeι ≫ D.baseChangeToSpec K)) :=
  let ⟨U, hU, hsing⟩ := h
  D.smooth_specializedDivisor_forGeneral U hU hsing

/-- **[Stacks, Tag 0FD6] from the Jacobian criterion with flatness available.** In the standing
situation of [Stacks, Tag 0G47] with `X` smooth and of finite type over an algebraically closed
field `k`, under hypotheses (2) and (3) of the tag, with `X` of dimension `n` at each closed
point and of dimension at most `n`, and with the Jacobian criterion available at the closed
points of `q⁻¹(W)` for every open `W` of the parameter space over which the restricted family is
flat, the divisor `H_v` is smooth over `k'` for general `v ∈ V ⊗_k k'`.

Everything in the source's dimension count is proved: the surjectivity of the evaluation at a
closed point and the resulting kernel dimension `r - (n + 1)`, the linear subspace of the fibre
that the kernel cuts out together with its dimension bound, the reduction of the fibre bound to
the closed points of `X` and then of `q⁻¹(W)`, the passage from `dim Σ_W < r` to a nonempty open
of `𝔸^r_k`, and the generic flatness of `q` that the Jacobian criterion needs. What remains is
the Jacobian criterion itself in the Bertini situation; see this module's header. -/
theorem smooth_specializedDivisor_forGeneral_of_jacobian_flat [IsAlgClosed D.k]
    [Smooth D.toBase] [QuasiCompact D.toBase] [NoetherianSpace D.universalDivisorScheme]
    {m n : ℕ} {b : Module.Basis (Fin (m + 1)) D.k D.V} {hb : D.GeneratesBy b}
    (himm : D.IsImmersive b hb) (hnr : n + 1 ≤ Nat.card D.basisIndex)
    (hX : topologicalKrullDim D.X ≤ (n : WithBot ℕ∞))
    (hdim : ∀ x : D.X, IsClosed ({x} : Set D.X) →
      topologicalKrullDimAt D.X x = (n : WithBot ℕ∞))
    (hjac : ∀ W : D.parameterBase.Opens, Flat (D.universalFamilyMapOver W) →
      ∀ x : D.X, IsClosed ({x} : Set D.X) →
      ∀ M : D.basisIndex → Fin (n + 1) → D.k,
      (∀ c : D.basisIndex → D.k, coeffMap M c = 0 ↔
        evalCoord (fun i => D.sectionOf (b i)) D.toBase x
          (fun l => c (D.basisIndexEquiv b l)) = 0) →
      ∀ w : (D.universalDivisorSchemeOver W).toScheme,
      IsClosed ({w} : Set (D.universalDivisorSchemeOver W).toScheme) →
      D.parameterProjection.base (D.universalDivisor.subschemeι.base
        ((D.universalDivisorSchemeOver W).ι.base w)) = x →
      (∃ j, D.universalDivisor.subschemeι.base
        ((D.universalDivisorSchemeOver W).ι.base w) ∈
          D.parameterSpace.basicOpen (D.evalCoordForm M j)) →
      w ∈ (D.universalFamilyMapOver W).smoothLocus) :
    D.ForGeneral (fun K _ _ w =>
      ∀ a : Fin (Module.finrank D.k D.V) → K,
        w = ∑ i, TensorProduct.tmul D.k (D.basis i) (a i) →
          Smooth ((D.specializedDivisor K a).subschemeι ≫ D.baseChangeToSpec K)) :=
  D.forGeneral_smooth_specializedDivisor_of_exists_opens
    (D.exists_nonempty_opens_subset_smoothLocus_of_jacobian_flat himm hnr hX hdim hjac)

/-- **[Stacks, Tag 0FD6] from the Jacobian criterion with flatness available, with hypothesis (3)
at an arbitrary basis of the linear system.** This is
`Stacks.Bertini.FamilyDivisors.smooth_specializedDivisor_forGeneral_of_jacobian_flat` with the
basis `b'` at which hypothesis (3) is taken and the basis `b` the Jacobian criterion is stated
against separate parameters, at unrelated index types.

**No `@[stacks]` attribute is attached**, as for the unprimed version: `hjac` is still an assumed
input, so this is not an assertion of the tag. -/
theorem smooth_specializedDivisor_forGeneral_of_jacobian_flat_of_basis [IsAlgClosed D.k]
    [Smooth D.toBase] [QuasiCompact D.toBase] [NoetherianSpace D.universalDivisorScheme]
    {m n p : ℕ} {b' : Module.Basis (Fin (p + 1)) D.k D.V} {hb' : D.GeneratesBy b'}
    (himm : D.IsImmersive b' hb') (b : Module.Basis (Fin (m + 1)) D.k D.V)
    (hnr : n + 1 ≤ Nat.card D.basisIndex)
    (hX : topologicalKrullDim D.X ≤ (n : WithBot ℕ∞))
    (hdim : ∀ x : D.X, IsClosed ({x} : Set D.X) →
      topologicalKrullDimAt D.X x = (n : WithBot ℕ∞))
    (hjac : ∀ W : D.parameterBase.Opens, Flat (D.universalFamilyMapOver W) →
      ∀ x : D.X, IsClosed ({x} : Set D.X) →
      ∀ M : D.basisIndex → Fin (n + 1) → D.k,
      (∀ c : D.basisIndex → D.k, coeffMap M c = 0 ↔
        evalCoord (fun i => D.sectionOf (b i)) D.toBase x
          (fun l => c (D.basisIndexEquiv b l)) = 0) →
      ∀ w : (D.universalDivisorSchemeOver W).toScheme,
      IsClosed ({w} : Set (D.universalDivisorSchemeOver W).toScheme) →
      D.parameterProjection.base (D.universalDivisor.subschemeι.base
        ((D.universalDivisorSchemeOver W).ι.base w)) = x →
      (∃ j, D.universalDivisor.subschemeι.base
        ((D.universalDivisorSchemeOver W).ι.base w) ∈
          D.parameterSpace.basicOpen (D.evalCoordForm M j)) →
      w ∈ (D.universalFamilyMapOver W).smoothLocus) :
    D.ForGeneral (fun K _ _ w =>
      ∀ a : Fin (Module.finrank D.k D.V) → K,
        w = ∑ i, TensorProduct.tmul D.k (D.basis i) (a i) →
          Smooth ((D.specializedDivisor K a).subschemeι ≫ D.baseChangeToSpec K)) :=
  D.smooth_specializedDivisor_forGeneral_of_jacobian_flat
    (D.isImmersive_basis_of_isImmersive himm b) hnr hX hdim hjac

/-- The Jacobian criterion in the Bertini situation, in the shape left over once the dimension
count, the generic flatness of `q` and the identification of the fibre of `q` with the divisor of
a coordinate tuple have been discharged.

Given an open `W` of the parameter space over which `q⁻¹(W) → 𝔸^r_k` is flat, a closed point `x`
of `X`, the matrix `M` of the evaluation `ev_x`, a closed point `w` of `q⁻¹(W)` lying over `x` at
which some form `∑ᵢ Mᵢⱼxᵢ` does not vanish, and the point `z` of the divisor of the residue
coordinates of `q(w)` which `w` comes from, it asks that **that divisor be smooth over `κ(q(w))`
at `z`**.

Nothing about the parameter space is left in it: the divisor is a closed subscheme of
`X_{κ(q(w))}` cut out by one section of an invertible module, and
`AlgebraicGeometry.smoothAt_zeroScheme_of_notMem_maximalSqSmul_of_perfectField` reduces its
smoothness at `z` to the germ of that section at the image of `z` avoiding `𝔪²ℒ`, which is what
the non-vanishing of a form of `M` at `w` says about `ev_x`. -/
def JacobianAtDivisor [Smooth D.toBase] {n : ℕ} {m : ℕ}
    (b : Module.Basis (Fin (m + 1)) D.k D.V) : Prop :=
  ∀ W : D.parameterBase.Opens, Flat (D.universalFamilyMapOver W) →
    ∀ x : D.X, IsClosed ({x} : Set D.X) →
    ∀ M : D.basisIndex → Fin (n + 1) → D.k,
    (∀ c : D.basisIndex → D.k, coeffMap M c = 0 ↔
      evalCoord (fun i => D.sectionOf (b i)) D.toBase x
        (fun l => c (D.basisIndexEquiv b l)) = 0) →
    ∀ w : (D.universalDivisorSchemeOver W).toScheme,
    IsClosed ({w} : Set (D.universalDivisorSchemeOver W).toScheme) →
    D.parameterProjection.base (D.universalDivisor.subschemeι.base
      ((D.universalDivisorSchemeOver W).ι.base w)) = x →
    (∃ j, D.universalDivisor.subschemeι.base
      ((D.universalDivisorSchemeOver W).ι.base w) ∈
        D.parameterSpace.basicOpen (D.evalCoordForm M j)) →
    ∀ z : D.residueCoordDivisor ((D.universalFamilyMapOver W).base w),
      (D.specializedToUniversal _
          (D.residueCoord ((D.universalFamilyMapOver W).base w))).base z =
        (D.universalDivisorSchemeOver W).ι.base w →
      z ∈ (D.residueCoordDivisorToBase ((D.universalFamilyMapOver W).base w)).smoothLocus

/-- **`hsing` of [Stacks, Tag 0FD6] from the Jacobian criterion on the divisor.** The hypothesis
is `Stacks.Bertini.FamilyDivisors.JacobianAtDivisor`: smoothness of the divisor of a coordinate
tuple at a point, with no flatness, no fibre product and no base change left in it. -/
theorem exists_nonempty_opens_subset_smoothLocus_of_jacobianAtDivisor [IsAlgClosed D.k]
    [Smooth D.toBase] [QuasiCompact D.toBase] [NoetherianSpace D.universalDivisorScheme]
    {m n : ℕ} {b : Module.Basis (Fin (m + 1)) D.k D.V} {hb : D.GeneratesBy b}
    (himm : D.IsImmersive b hb) (hnr : n + 1 ≤ Nat.card D.basisIndex)
    (hX : topologicalKrullDim D.X ≤ (n : WithBot ℕ∞))
    (hdim : ∀ x : D.X, IsClosed ({x} : Set D.X) →
      topologicalKrullDimAt D.X x = (n : WithBot ℕ∞))
    (hjac : D.JacobianAtDivisor (n := n) b) :
    ∃ U : D.parameterBase.Opens, (U : Set D.parameterBase).Nonempty ∧
      ((D.universalFamilyMap ⁻¹ᵁ U : D.universalDivisorScheme.Opens) :
          Set D.universalDivisorScheme) ⊆
        (D.universalFamilyMap.smoothLocus : Set D.universalDivisorScheme) :=
  D.exists_nonempty_opens_subset_smoothLocus_of_jacobian_flat himm hnr hX hdim
    fun W hflat x hx M hM w hw hwx hform =>
      D.mem_smoothLocus_of_mem_smoothLocus_residueCoordDivisor W hflat w
        (hjac W hflat x hx M hM w hw hwx hform)

/-- **`hsing` of [Stacks, Tag 0FD6] from the Jacobian criterion on the divisor, with
hypothesis (3) at an arbitrary basis of the linear system.** This is
`Stacks.Bertini.FamilyDivisors.exists_nonempty_opens_subset_smoothLocus_of_jacobianAtDivisor`
with the basis `b'` at which hypothesis (3) is taken and the basis `b` the criterion
`Stacks.Bertini.FamilyDivisors.JacobianAtDivisor` is stated against separate parameters, at
unrelated index types; the hypothesis is transported onto `b` by
`Stacks.Bertini.FamilyDivisors.isImmersive_basis_of_isImmersive`.

The dimension data `hnr`, `hX` and `hdim` is still assumed here; the `_pointwise_of_basis`
sibling below has it discharged. -/
theorem exists_nonempty_opens_subset_smoothLocus_of_jacobianAtDivisor_of_basis [IsAlgClosed D.k]
    [Smooth D.toBase] [QuasiCompact D.toBase] [NoetherianSpace D.universalDivisorScheme]
    {m n p : ℕ} {b' : Module.Basis (Fin (p + 1)) D.k D.V} {hb' : D.GeneratesBy b'}
    (himm : D.IsImmersive b' hb') (b : Module.Basis (Fin (m + 1)) D.k D.V)
    (hnr : n + 1 ≤ Nat.card D.basisIndex)
    (hX : topologicalKrullDim D.X ≤ (n : WithBot ℕ∞))
    (hdim : ∀ x : D.X, IsClosed ({x} : Set D.X) →
      topologicalKrullDimAt D.X x = (n : WithBot ℕ∞))
    (hjac : D.JacobianAtDivisor (n := n) b) :
    ∃ U : D.parameterBase.Opens, (U : Set D.parameterBase).Nonempty ∧
      ((D.universalFamilyMap ⁻¹ᵁ U : D.universalDivisorScheme.Opens) :
          Set D.universalDivisorScheme) ⊆
        (D.universalFamilyMap.smoothLocus : Set D.universalDivisorScheme) :=
  D.exists_nonempty_opens_subset_smoothLocus_of_jacobianAtDivisor
    (D.isImmersive_basis_of_isImmersive himm b) hnr hX hdim hjac

/-- **`hsing` of [Stacks, Tag 0FD6] from the Jacobian criterion on the divisor, with no dimension
data assumed and hypothesis (3) at an arbitrary basis of the linear system.** The basis `b'` at
which the immersion hypothesis is taken and the basis `b` the Jacobian criterion is stated
against are unrelated, and `b'` is not required to be the standing basis.

That decoupling is forced by the two roles the basis plays. The Jacobian criterion
`Stacks.Bertini.FamilyDivisors.JacobianAtDivisor` can only be stated against the standing basis,
because the coordinates of the parameter space are coefficients against it. Hypothesis (3), by
contrast, is a condition on the linear system alone, and everything the count takes from it —
the surjectivity of `ev_x` and the two numbers `dim ker ev_x = r - (n + 1)` and `n + 1 ≤ r` — is
a property of the basis-free evaluation `Stacks.Bertini.FamilyDivisors.evalVector`
(`Stacks.Bertini.FamilyDivisors.exists_evalMatrix_of_basis`,
`Stacks.Bertini.FamilyDivisors.succ_le_of_smooth_of_basis`). So the hypothesis may be taken at
any basis while the criterion stays at the standing one.

The dimension data is supplied at each closed point from the local dimension of `X` there,
exactly as in the sibling
`…exists_nonempty_opens_subset_smoothLocus_of_jacobianAtDivisor_pointwise` below; see its
docstring for how each of the three numerical hypotheses is discharged. -/
theorem exists_nonempty_opens_subset_smoothLocus_of_jacobianAtDivisor_pointwise_of_basis
    [IsAlgClosed D.k] [Smooth D.toBase] [QuasiCompact D.toBase] {m p : ℕ}
    {b' : Module.Basis (Fin (p + 1)) D.k D.V} {hb' : D.GeneratesBy b'}
    (himm : D.IsImmersive b' hb') (b : Module.Basis (Fin (m + 1)) D.k D.V)
    (hjac : ∀ n : ℕ, D.JacobianAtDivisor (n := n) b) :
    ∃ U : D.parameterBase.Opens, (U : Set D.parameterBase).Nonempty ∧
      ((D.universalFamilyMap ⁻¹ᵁ U : D.universalDivisorScheme.Opens) :
          Set D.universalDivisorScheme) ⊆
        (D.universalFamilyMap.smoothLocus : Set D.universalDivisorScheme) := by
  have : LocallyOfFiniteType D.toBase := inferInstance
  have hcard : Nat.card D.basisIndex = m + 1 := by
    rw [D.natCard_basisIndex, D.finrank_eq_of_basis b]
  obtain ⟨W, hW, hflat⟩ := D.exists_nonempty_opens_flat_universalFamilyMapOver
  refine D.exists_nonempty_opens_subset_smoothLocus_of_closedPoints_over W hW (by omega) ?_
  intro x hx
  obtain ⟨n, hn⟩ := D.exists_natCast_eq_topologicalKrullDimAt_of_isClosed hx
  obtain ⟨M, hMsurj, hMker⟩ := D.exists_evalMatrix_of_basis himm b hx hn
  have hfib := D.topologicalKrullDim_fiber_nonSmoothToXOver_le_of_evalSubspace W hx M hMsurj
    (fun w hw hwx hform => D.mem_smoothLocus_of_mem_smoothLocus_residueCoordDivisor W hflat w
      (hjac n W hflat x hx M hMker w hw hwx hform))
  rw [Fintype.card_fin] at hfib
  have hle : n + 1 ≤ Nat.card D.basisIndex := by
    rw [hcard]; exact D.succ_le_of_smooth_of_basis himm b hx hn
  rw [hn]
  refine le_trans (add_le_add hfib le_rfl) ?_
  have hnat : Nat.card D.basisIndex - (n + 1) + n ≤ Nat.card D.basisIndex - 1 := by omega
  exact_mod_cast hnat

/-- **`hsing` of [Stacks, Tag 0FD6] from the Jacobian criterion on the divisor, with no
dimension data assumed.** Under hypotheses (2) and (3) of the tag, with `X` smooth and of finite
type over an algebraically closed field `k`, and with
`Stacks.Bertini.FamilyDivisors.JacobianAtDivisor` available at every size of evaluation matrix,
there is a nonempty open `U ⊂ 𝔸^r_k` whose preimage under `q` lies in the smooth locus of `q`.

This is the sibling
`Stacks.Bertini.FamilyDivisors.exists_nonempty_opens_subset_smoothLocus_of_jacobianAtDivisor`
with all three numerical hypotheses removed. Each is supplied here, at each closed point `x` of
`X` separately and from its own local dimension `n_x`:

* `n_x` exists, by
  `Stacks.Bertini.FamilyDivisors.exists_natCast_eq_topologicalKrullDimAt_of_isClosed` — the local
  ring of a smooth scheme at a closed point is regular, so its Krull dimension is a
  natural number. This replaces `dim X ≤ n`, which the sibling uses only to know that a
  dimension `n` is available.
* `n_x + 1 ≤ r`, by `Stacks.Bertini.FamilyDivisors.succ_le_of_smooth_of_basis` — the evaluation
  `ev_x` surjects `V` onto a space of dimension `n_x + 1`. This replaces `n + 1 ≤ r`, read off
  surjectivity exactly as in the source.
* the fibre bound, which is `r - (n_x + 1)` with `n_x` the dimension at that point rather than
  one uniform number. The count that consumes it is
  `Stacks.Bertini.FamilyDivisors.exists_nonempty_opens_subset_smoothLocus_of_closedPoints_over`,
  which bounds the fibre dimension and the local dimension of `X` *together* by `r - 1`; since
  `(r - (n_x + 1)) + n_x = r - 1` whatever `n_x` is, no equidimensionality of `X` is needed.

Hypothesis (3) is taken here at the basis the Jacobian criterion is stated against; the
`…_of_basis` version above takes it at an arbitrary basis. -/
theorem exists_nonempty_opens_subset_smoothLocus_of_jacobianAtDivisor_pointwise
    [IsAlgClosed D.k] [Smooth D.toBase] [QuasiCompact D.toBase] {m : ℕ}
    {b : Module.Basis (Fin (m + 1)) D.k D.V} {hb : D.GeneratesBy b}
    (himm : D.IsImmersive b hb) (hjac : ∀ n : ℕ, D.JacobianAtDivisor (n := n) b) :
    ∃ U : D.parameterBase.Opens, (U : Set D.parameterBase).Nonempty ∧
      ((D.universalFamilyMap ⁻¹ᵁ U : D.universalDivisorScheme.Opens) :
          Set D.universalDivisorScheme) ⊆
        (D.universalFamilyMap.smoothLocus : Set D.universalDivisorScheme) :=
  D.exists_nonempty_opens_subset_smoothLocus_of_jacobianAtDivisor_pointwise_of_basis himm b hjac

/-- **[Stacks, Tag 0FD6] from the Jacobian criterion on the divisor, with no dimension data
assumed and hypothesis (3) at an arbitrary basis of the linear system.** In the standing
situation of [Stacks, Tag 0G47] with `X` smooth and of finite type over an algebraically closed
field `k`, under hypotheses (2) and (3) of the tag — the latter taken at a basis `b'` unrelated
to the basis `b` the Jacobian criterion is stated against — and with
`Stacks.Bertini.FamilyDivisors.JacobianAtDivisor` for `b` available at every size of evaluation
matrix, the divisor `H_v` is smooth over `k'` for general `v ∈ V ⊗_k k'`.

The two bases have to be separate parameters because the criterion can only be stated against
the standing basis while hypothesis (3) is a condition on the linear system alone; see the
companion `hsing` result above. -/
theorem smooth_specializedDivisor_forGeneral_of_jacobianAtDivisor_pointwise_of_basis
    [IsAlgClosed D.k] [Smooth D.toBase] [QuasiCompact D.toBase] {m p : ℕ}
    {b' : Module.Basis (Fin (p + 1)) D.k D.V} {hb' : D.GeneratesBy b'}
    (himm : D.IsImmersive b' hb') (b : Module.Basis (Fin (m + 1)) D.k D.V)
    (hjac : ∀ n : ℕ, D.JacobianAtDivisor (n := n) b) :
    D.ForGeneral (fun K _ _ w =>
      ∀ a : Fin (Module.finrank D.k D.V) → K,
        w = ∑ i, TensorProduct.tmul D.k (D.basis i) (a i) →
          Smooth ((D.specializedDivisor K a).subschemeι ≫ D.baseChangeToSpec K)) :=
  D.forGeneral_smooth_specializedDivisor_of_exists_opens
    (D.exists_nonempty_opens_subset_smoothLocus_of_jacobianAtDivisor_pointwise_of_basis himm b
      hjac)

/-- **[Stacks, Tag 0FD6] from the Jacobian criterion on the divisor, with no dimension data
assumed.** In the standing situation of [Stacks, Tag 0G47] with `X` smooth and of finite type
over an algebraically closed field `k`, under hypotheses (2) and (3) of the tag, and with
`Stacks.Bertini.FamilyDivisors.JacobianAtDivisor` available at every size of evaluation matrix,
the divisor `H_v` is smooth over `k'` for general `v ∈ V ⊗_k k'`.

This is `Stacks.Bertini.FamilyDivisors.smooth_specializedDivisor_forGeneral_of_jacobianAtDivisor`
with `dim X ≤ n`, `n + 1 ≤ r` and the equidimensionality of `X` all discharged; see the
companion `hsing` result above for how each is supplied. Hypothesis (3) is taken at the basis the
Jacobian criterion is stated against; the `…_of_basis` version above takes it at an arbitrary
basis. -/
theorem smooth_specializedDivisor_forGeneral_of_jacobianAtDivisor_pointwise [IsAlgClosed D.k]
    [Smooth D.toBase] [QuasiCompact D.toBase] {m : ℕ}
    {b : Module.Basis (Fin (m + 1)) D.k D.V} {hb : D.GeneratesBy b}
    (himm : D.IsImmersive b hb) (hjac : ∀ n : ℕ, D.JacobianAtDivisor (n := n) b) :
    D.ForGeneral (fun K _ _ w =>
      ∀ a : Fin (Module.finrank D.k D.V) → K,
        w = ∑ i, TensorProduct.tmul D.k (D.basis i) (a i) →
          Smooth ((D.specializedDivisor K a).subschemeι ≫ D.baseChangeToSpec K)) :=
  D.smooth_specializedDivisor_forGeneral_of_jacobianAtDivisor_pointwise_of_basis himm b hjac

/-- **[Stacks, Tag 0FD6] from the Jacobian criterion on the divisor.** In the standing situation
of [Stacks, Tag 0G47] with `X` smooth and of finite type over an algebraically closed field `k`,
under hypotheses (2) and (3) of the tag, with `X` of dimension `n` at each closed point and of
dimension at most `n`, and with `Stacks.Bertini.FamilyDivisors.JacobianAtDivisor` available, the
divisor `H_v` is smooth over `k'` for general `v ∈ V ⊗_k k'`.

This is the strongest form of the conclusion reached so far: everything in the source's proof is
discharged except the Jacobian criterion applied to a single divisor at a single point. -/
theorem smooth_specializedDivisor_forGeneral_of_jacobianAtDivisor [IsAlgClosed D.k]
    [Smooth D.toBase] [QuasiCompact D.toBase] [NoetherianSpace D.universalDivisorScheme]
    {m n : ℕ} {b : Module.Basis (Fin (m + 1)) D.k D.V} {hb : D.GeneratesBy b}
    (himm : D.IsImmersive b hb) (hnr : n + 1 ≤ Nat.card D.basisIndex)
    (hX : topologicalKrullDim D.X ≤ (n : WithBot ℕ∞))
    (hdim : ∀ x : D.X, IsClosed ({x} : Set D.X) →
      topologicalKrullDimAt D.X x = (n : WithBot ℕ∞))
    (hjac : D.JacobianAtDivisor (n := n) b) :
    D.ForGeneral (fun K _ _ w =>
      ∀ a : Fin (Module.finrank D.k D.V) → K,
        w = ∑ i, TensorProduct.tmul D.k (D.basis i) (a i) →
          Smooth ((D.specializedDivisor K a).subschemeι ≫ D.baseChangeToSpec K)) :=
  D.forGeneral_smooth_specializedDivisor_of_exists_opens
    (D.exists_nonempty_opens_subset_smoothLocus_of_jacobianAtDivisor himm hnr hX hdim hjac)

/-- **[Stacks, Tag 0FD6] from the Jacobian criterion on the divisor, with hypothesis (3) at an
arbitrary basis of the linear system.** This is
`Stacks.Bertini.FamilyDivisors.smooth_specializedDivisor_forGeneral_of_jacobianAtDivisor` with
the basis `b'` at which hypothesis (3) is taken and the basis `b` the criterion
`Stacks.Bertini.FamilyDivisors.JacobianAtDivisor` is stated against separate parameters, at
unrelated index types.

**No `@[stacks]` attribute is attached**, as for the unprimed version: the dimension data
`hnr`, `hX` and `hdim` is assumed, and the registered carriers of the tag are in
`StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniJacobianDivisor` and
`StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniImmersionQuasiCompact`. -/
theorem smooth_specializedDivisor_forGeneral_of_jacobianAtDivisor_of_basis [IsAlgClosed D.k]
    [Smooth D.toBase] [QuasiCompact D.toBase] [NoetherianSpace D.universalDivisorScheme]
    {m n p : ℕ} {b' : Module.Basis (Fin (p + 1)) D.k D.V} {hb' : D.GeneratesBy b'}
    (himm : D.IsImmersive b' hb') (b : Module.Basis (Fin (m + 1)) D.k D.V)
    (hnr : n + 1 ≤ Nat.card D.basisIndex)
    (hX : topologicalKrullDim D.X ≤ (n : WithBot ℕ∞))
    (hdim : ∀ x : D.X, IsClosed ({x} : Set D.X) →
      topologicalKrullDimAt D.X x = (n : WithBot ℕ∞))
    (hjac : D.JacobianAtDivisor (n := n) b) :
    D.ForGeneral (fun K _ _ w =>
      ∀ a : Fin (Module.finrank D.k D.V) → K,
        w = ∑ i, TensorProduct.tmul D.k (D.basis i) (a i) →
          Smooth ((D.specializedDivisor K a).subschemeι ≫ D.baseChangeToSpec K)) :=
  D.smooth_specializedDivisor_forGeneral_of_jacobianAtDivisor
    (D.isImmersive_basis_of_isImmersive himm b) hnr hX hdim hjac

end Matrix

end Stacks.Bertini.FamilyDivisors

end
