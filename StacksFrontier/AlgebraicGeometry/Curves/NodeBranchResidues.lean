module

public import StacksFrontier.AlgebraicGeometry.Curves.IsSplitNode
public import StacksFrontier.AlgebraicGeometry.Curves.NodeFittingIdealClosedPoint
public import StacksFrontier.AlgebraicGeometry.Curves.NodeMulticrossBridge
public import StacksFrontier.AlgebraicGeometry.Curves.NodeNormalizationExactSequence
public import StacksFrontier.AlgebraicGeometry.Curves.NodeQuadraticAlgebra.GeometricBranches
public import StacksFrontier.AlgebraicGeometry.Curves.NodeQuadraticAlgebra.SplitNode
public import StacksFrontier.AlgebraicGeometry.Curves.NodeStalkCharacterization
public import StacksFrontier.AlgebraicGeometry.Curves.SheafDerivationNodalDescent
public import StacksFrontier.AlgebraicGeometry.NormalizationQuotient.StalkVanishing
public import StacksFrontier.AlgebraicGeometry.Variety.MulticrossBranches.BranchBound

/-!
# The two branch residues at a node

Let `k` be an algebraically closed field, let `X` be a scheme locally of finite type over `k`
of dimension one, and let `x` be a node of `X` in the sense of Tag 0C47. Write
`A = 𝒪_{X, x}` and `A' = integralClosure A (FractionRing A)` for its normalization inside its
total ring of fractions. Then `A'` carries two distinct `k`-algebra maps `ε₁, ε₂ : A' → k`
restricting to the same map on `A` — the residues at the two points of `X^ν` above `x`.

Everything that the local theory of Tag 0E68 took as a hypothesis about a node is therefore
available from the node hypothesis alone: the exact sequence
`0 → 𝒪_{X, x} → 𝒪_{X^ν, x'} × 𝒪_{X^ν, x''} → k → 0` of Tag 0C1X, the identification of the
image of `𝒪_{X, x}` as the elements with equal branch residues, and the restriction to
`𝒪_{X, x}` of a `k`-derivation of `A'` fixing the two points. At the sheaf level the
right-to-left direction of Tag 0E68 is likewise freed of its node data: the only hypothesis
left at a singular point is that the vector field on the normalization fix the `k`-points of
the stalk of `ν_* 𝒪_{X^ν}`, which is the source's own hypothesis.

## Main definitions

There are no definitions.

## Main results

* `Stacks.Curves.nonempty_quadraticAlgebra_algEquiv_prod_of_isSepClosed` — over a separably
  closed residue field the quadratic algebra of a node is the split one `κ × κ`.
* `Stacks.Curves.exists_branchResidues_of_quadraticAlgebra_algEquiv_prod` — a split quadratic
  algebra and a rational residue field produce the two branch residues on the normalization.
* `Stacks.Curves.isSplitNode_of_isNode` — over an algebraically closed field every node is a
  split node, the parenthetical step of the proof of Tag 0E68.
* `Stacks.Curves.isNodalAlgebra_stalk_and_exists_branch_residues_of_isNode` — at a node the
  local ring is a nodal `k`-algebra and its normalization carries the two branch residues.
* `Stacks.Curves.exists_branchResidues_exact_integralClosure_of_isNode` — the exact sequence of
  the node and the restriction of a fixing derivation, with no data assumed.
* `Stacks.Curves.existsUnique_descend_normalization_of_isNode` — the right-to-left direction of
  Tag 0E68 with the node data derived rather than assumed.

## Implementation notes

The splitting of the quadratic algebra is not obtained from the quadratic relation but from the
branch count: a node has exactly two *geometric* branches
(`Stacks.Curves.numberOfGeometricBranchesOfLocalRing_eq_two_of_isNodalAlgebra`, Tag 0C4A), and
over a separably closed residue field the geometric count is the ordinary one
(`numberOfBranches_eq_numberOfGeometricBranches_of_sepClosed`), which is the number of maximal
ideals of `A'` and hence, by Tag 0CBU, the splitting of the quadratic algebra. The residue field
of a closed point of a scheme locally of finite type over an algebraically closed field is the
base field (`Stacks.Curves.surjective_evaluation_of_isAlgClosed`, Zariski's lemma), so that
separable closedness is available.

The two residues are read off the split quadratic algebra rather than from the two maximal
ideals of `A'`: the composite `A' → A' ⧸ 𝔪_A A' = quadraticAlgebra A ≅ κ × κ → κ ≅ k` of the
quotient map, the splitting, a projection and the identification of the residue field with `k`.
The `k`-algebra structure is available because `A → quadraticAlgebra A` factors through `κ` and
the splitting is a `κ`-algebra map, so each projection restricts on the image of `A` to the
residue map; the two composites therefore agree on `A`, and they differ because the two
projections of `κ × κ` differ at `(1, 0)`.

At the sheaf level the transport from `A'` to `(ν_* 𝒪_{X^ν})_x` is along Tag 0C3B(2); the one
compatibility it needs is that the `k`-algebra structure on that stalk, which goes through a
global section of the base pulled back to `X^ν`, factors through `𝒪_{X, x}`
(`Stacks.Curves.algebraMap_directImageStalkFieldAlgebra`). That is the naturality of the germ
with respect to `ν^♯` at the top open.

The hypothesis of `Stacks.Curves.existsUnique_descend_normalization_of_isNode` quantifies over
*all* `k`-algebra maps from the stalk of the direct image to `k`, rather than over the two
branch residues. At a node these are the same condition: such a map has maximal kernel, `A'` has
exactly two maximal ideals, and the identification of each residue field with `k` is unique; so
there are exactly two such maps and they are the two branch residues. That count is not proved
here, so the hypothesis is formally the stronger one. It costs nothing, because the stronger
condition is the one the extension of a vector field satisfies:
`Stacks.Curves.forall_fixes_of_extend_normalizationStalk_of_isNode` shows that an extension
fixes *every* `k`-point of the stalk, by pairing an arbitrary one with a second rather than by
counting them.

## What is not done here

The left-to-right direction of Tag 0E68 — extending a vector field on `X` to `X^ν`, for which
the source uses `𝒪_{X^ν, x'} = k + (u)` — is not addressed here, at the sheaf level or the
local one. It is proved: at a node and on the stalk of the direct image by
`Stacks.Curves.exists_branchResidues_existsUnique_extend_normalizationStalk_of_isNode`, and for
the sheaves by `Stacks.Curves.existsUnique_extend_normalization_of_hasAtWorstNodalSingularities`;
`Stacks.Curves.derivations_eq_normalization_derivations_fixing_nodes` puts that together with
the direction proved here, and `Stacks.Curves.NodalVectorFields.range_branchPair` is the whole
tag.

The statements here are phrased through the `k`-points of `(ν_* 𝒪_{X^ν})_x`. The passage to the
sheaf-theoretic condition that a vector field fix the points of `S` is made in
`StacksFrontier.AlgebraicGeometry.Curves.NodalVectorFieldsEquivalence`, by
`Stacks.Curves.forall_fixes_stalkDerivation_of_forall_fixes` and
`Stacks.Curves.fixes_of_forall_fixes_stalkDerivation`; the bridge at one point in the first
direction is `Stacks.Curves.fixes_stalkDerivation_of_fixes`.

## References

* [Stacks Project, Tag 0E68](https://stacks.math.columbia.edu/tag/0E68)
* [Stacks Project, Tag 0C1X](https://stacks.math.columbia.edu/tag/0C1X)
* [Stacks Project, Tag 0C4A](https://stacks.math.columbia.edu/tag/0C4A)
* [Stacks Project, Tag 0CBU](https://stacks.math.columbia.edu/tag/0CBU)
* [Stacks Project, Tag 0CBV](https://stacks.math.columbia.edu/tag/0CBV)
* [Stacks Project, Tag 0C3B](https://stacks.math.columbia.edu/tag/0C3B)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing

universe u v

namespace Stacks.Curves

section Split

variable (k : Type u) (A : Type v) [Field k] [CommRing A] [IsLocalRing A] [Algebra k A]

/-- **A node with separably closed residue field is split.** The quadratic algebra of a nodal
Nagata local algebra over `k` whose residue field is separably closed is the trivial quadratic
extension `κ × κ`: a node has exactly two geometric branches (Tag 0C4A), over a separably closed
residue field the geometric branches are the branches, and two branches is one of the equivalent
conditions of Tag 0CBU for the quadratic algebra to split. -/
theorem nonempty_quadraticAlgebra_algEquiv_prod_of_isSepClosed
    (hNagata : IsNagataRing A) (hA : IsNodalAlgebra k A)
    [IsSepClosed (ResidueField A)] :
    Nonempty (quadraticAlgebra A ≃ₐ[ResidueField A] (ResidueField A × ResidueField A)) := by
  have : IsNoetherianRing A := hNagata.isNoetherianRing
  refine (nonempty_quadraticAlgebra_algEquiv_prod_iff_numberOfBranches_eq_two k A hA).mpr ?_
  rw [numberOfBranches_eq_numberOfGeometricBranches_of_sepClosed A]
  exact numberOfGeometricBranchesOfLocalRing_eq_two_of_isNodalAlgebra k A hNagata hA

end Split

section Residues

variable (k : Type u) (A : Type v) [Field k] [CommRing A] [IsLocalRing A] [Algebra k A]

/-- **The two branch residues of a split node with rational residue field.** Let `A` be a local
`k`-algebra whose residue field is `k` and whose quadratic algebra
`quadraticAlgebra A = A' ⧸ 𝔪_A A'` is the split one `κ × κ`, where
`A' = integralClosure A (FractionRing A)`. Then `A'` carries two distinct `k`-algebra maps to `k`
which agree on the image of `A`.

They are the composites of the quotient map `A' → quadraticAlgebra A`, the splitting, one of the
two projections, and the identification `κ ≅ k`. Both restrict on the image of `A` to the residue
map, since `A → quadraticAlgebra A` factors through `κ` and the splitting is a `κ`-algebra map;
and they differ because the two projections of `κ × κ` differ at `(1, 0)`.

These are the maps `ε₁`, `ε₂` that the local statements of Tag 0E68 take as hypotheses — the
residues at the two points of the normalization above the node. -/
theorem exists_branchResidues_of_quadraticAlgebra_algEquiv_prod
    (eκ : ResidueField A ≃ₐ[k] k)
    (e : quadraticAlgebra A ≃ₐ[ResidueField A] (ResidueField A × ResidueField A)) :
    ∃ ε₁ ε₂ : ↥(integralClosure A (FractionRing A)) →ₐ[k] k,
      (∀ a : A, ε₁ (algebraMap A ↥(integralClosure A (FractionRing A)) a) =
          ε₂ (algebraMap A ↥(integralClosure A (FractionRing A)) a)) ∧
        ε₁ ≠ ε₂ := by
  set A' := ↥(integralClosure A (FractionRing A)) with hA'
  set J := (maximalIdeal A).map (algebraMap A A') with hJ
  let π : A' →+* quadraticAlgebra A := Ideal.Quotient.mk J
  let θ : A' →+* (k × k) :=
    (RingHom.prodMap (eκ : ResidueField A →+* k) (eκ : ResidueField A →+* k)).comp
      ((e : quadraticAlgebra A →+* (ResidueField A × ResidueField A)).comp π)
  have hθ : ∀ y, θ y = (eκ (e (π y)).1, eκ (e (π y)).2) := fun _ => rfl
  have hπa : ∀ a : A, π (algebraMap A A' a) =
      algebraMap (ResidueField A) (quadraticAlgebra A) (residue A a) := fun a => rfl
  have hθa : ∀ a : A, θ (algebraMap A A' a) = (eκ (residue A a), eκ (residue A a)) := by
    intro a
    rw [hθ, hπa a, e.commutes]
    rfl
  have hπk : ∀ c : k, π (algebraMap k A' c) = algebraMap k (quadraticAlgebra A) c := fun c => rfl
  have hθk : ∀ c : k, θ (algebraMap k A' c) = (c, c) := by
    intro c
    rw [hθ, hπk c, IsScalarTower.algebraMap_apply k (ResidueField A) (quadraticAlgebra A) c,
      e.commutes]
    have h1 : (algebraMap (ResidueField A) (ResidueField A × ResidueField A)
        (algebraMap k (ResidueField A) c)) =
        (algebraMap k (ResidueField A) c, algebraMap k (ResidueField A) c) := rfl
    rw [h1]
    simp [eκ.commutes]
  refine ⟨AlgHom.mk ((RingHom.fst k k).comp θ) (fun c => congrArg Prod.fst (hθk c)),
    AlgHom.mk ((RingHom.snd k k).comp θ) (fun c => congrArg Prod.snd (hθk c)),
    fun a => (congrArg Prod.fst (hθa a)).trans (congrArg Prod.snd (hθa a)).symm, ?_⟩
  intro hcon
  obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (I := J) (e.symm (1, 0))
  have hθt : θ t = (1, 0) := by
    rw [hθ]
    have : e (π t) = (1, 0) := by
      change e (Ideal.Quotient.mk J t) = _
      rw [ht, e.apply_symm_apply]
    rw [this]
    simp
  have h : (θ t).1 = (θ t).2 := congrArg (fun f : A' →ₐ[k] k => f t) hcon
  rw [hθt] at h
  exact one_ne_zero h

end Residues

section Node

variable (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))]

/-- **At a closed point of a scheme locally of finite type over an algebraically closed field
the residue field is the base field.** This is Zariski's lemma, in the form
`Stacks.Curves.surjective_evaluation_of_isAlgClosed`, packaged as a `k`-algebra equivalence. -/
theorem nonempty_residueField_stalk_algEquiv_of_isClosed (x : X) (hx : IsClosed ({x} : Set X)) :
    letI : Algebra k (X.presheaf.stalk x) := (fieldToStalk (X ↘ Spec (.of k)) x).hom.toAlgebra
    Nonempty (ResidueField (X.presheaf.stalk x) ≃ₐ[k] k) := by
  let : Algebra k (X.presheaf.stalk x) := (fieldToStalk (X ↘ Spec (.of k)) x).hom.toAlgebra
  have hsurj : Function.Surjective (algebraMap k (ResidueField (X.presheaf.stalk x))) :=
    surjective_evaluation_of_isAlgClosed k (X ↘ Spec (.of k)) x hx
  exact ⟨(AlgEquiv.ofBijective (Algebra.ofId k (ResidueField (X.presheaf.stalk x)))
    ⟨(algebraMap k (ResidueField (X.presheaf.stalk x))).injective, hsurj⟩).symm⟩

/-- At a node the local ring is nodal, its residue field is `k`, and its quadratic algebra
splits. -/
private theorem isNodalAlgebra_and_algEquivs_of_isNode (hdim : topologicalKrullDim X = 1) (x : X)
    (hnode : IsNode k X x) :
    letI : Algebra k (X.presheaf.stalk x) := (fieldToStalk (X ↘ Spec (.of k)) x).hom.toAlgebra
    IsNodalAlgebra k (X.presheaf.stalk x) ∧ Nonempty (ResidueField (X.presheaf.stalk x) ≃ₐ[k] k) ∧
      Nonempty (quadraticAlgebra (X.presheaf.stalk x) ≃ₐ[ResidueField (X.presheaf.stalk x)]
        (ResidueField (X.presheaf.stalk x) × ResidueField (X.presheaf.stalk x))) := by
  let : Algebra k (X.presheaf.stalk x) := (fieldToStalk (X ↘ Spec (.of k)) x).hom.toAlgebra
  have hx : IsClosed ({x} : Set X) := hnode.1
  have hnodal : IsNodalAlgebra k (X.presheaf.stalk x) :=
    ((isNode_tfae_of_isClosed k X hdim x hx).out 1 2).mp hnode
  obtain ⟨eκ⟩ := nonempty_residueField_stalk_algEquiv_of_isClosed k X x hx
  let : IsSepClosed (ResidueField (X.presheaf.stalk x)) :=
    IsSepClosed.of_ringEquiv eκ.toRingEquiv
  exact ⟨hnodal, ⟨eκ⟩, nonempty_quadraticAlgebra_algEquiv_prod_of_isSepClosed k
    (X.presheaf.stalk x) (isNagataRing_stalk_of_locallyOfFiniteType k (X ↘ Spec (.of k)) x)
    hnodal⟩

/-- **Over an algebraically closed field every node is a split node.** This is the
parenthetical step of the proof of Tag 0E68, which the source attributes to Definition 0CBV and
Lemma 0CBW: the residue field at a closed point is `k` by Zariski's lemma, so it is separably
closed, and then the quadratic algebra of the node splits by
`Stacks.Curves.nonempty_quadraticAlgebra_algEquiv_prod_of_isSepClosed`. -/
theorem isSplitNode_of_isNode (hdim : topologicalKrullDim X = 1) (x : X)
    (hnode : IsNode k X x) : IsSplitNode k X x :=
  ⟨hnode, ⟨(fieldToResidue (X ↘ Spec (.of k)) x).hom.injective,
    surjective_evaluation_of_isAlgClosed k (X ↘ Spec (.of k)) x hnode.1⟩,
    (isNodalAlgebra_and_algEquivs_of_isNode k X hdim x hnode).2.2⟩

/-- **At a node the local ring is nodal and its normalization carries the two branch
residues.** For `k` algebraically closed, `X` locally of finite type over `k` of dimension one
and `x` a node, the local ring `𝒪_{X, x}` is a nodal `k`-algebra and its normalization
`A' = integralClosure 𝒪_{X, x} (Frac 𝒪_{X, x})` carries two distinct `k`-algebra maps to `k`
agreeing on `𝒪_{X, x}`.

This is the data that the local statements of Tag 0E68 assumed, derived from the node
hypothesis: nodality from Tag 0C4D, and the two residues from the splitting of the quadratic
algebra at a node over an algebraically closed field. -/
theorem isNodalAlgebra_stalk_and_exists_branch_residues_of_isNode
    (hdim : topologicalKrullDim X = 1) (x : X) (hnode : IsNode k X x) :
    letI : Algebra k (X.presheaf.stalk x) := (fieldToStalk (X ↘ Spec (.of k)) x).hom.toAlgebra
    IsNodalAlgebra k (X.presheaf.stalk x) ∧
      ∃ ε₁ ε₂ : ↥(integralClosure (X.presheaf.stalk x)
          (FractionRing (X.presheaf.stalk x))) →ₐ[k] k,
        (∀ a : X.presheaf.stalk x,
            ε₁ (algebraMap (X.presheaf.stalk x) ↥(integralClosure (X.presheaf.stalk x)
                (FractionRing (X.presheaf.stalk x))) a) =
              ε₂ (algebraMap (X.presheaf.stalk x) ↥(integralClosure (X.presheaf.stalk x)
                (FractionRing (X.presheaf.stalk x))) a)) ∧
          ε₁ ≠ ε₂ := by
  let : Algebra k (X.presheaf.stalk x) := (fieldToStalk (X ↘ Spec (.of k)) x).hom.toAlgebra
  obtain ⟨hnodal, ⟨eκ⟩, ⟨e⟩⟩ := isNodalAlgebra_and_algEquivs_of_isNode k X hdim x hnode
  exact ⟨hnodal,
    exists_branchResidues_of_quadraticAlgebra_algEquiv_prod k (X.presheaf.stalk x) eκ e⟩

/-- **The exact sequence of a node, and the restriction of a derivation fixing its two branch
points, with no data assumed.** At a node `x` of a scheme locally of finite type of dimension one
over an algebraically closed field there are two distinct `k`-algebra maps `ε₁, ε₂` from the
normalization `A'` of `A = 𝒪_{X, x}` to `k` agreeing on `A` such that

* `A → A'` is injective and `t ↦ ε₁ t - ε₂ t` is surjective,
* the image of `A` in `A'` is exactly the set of elements whose two residues agree, and
* a `k`-derivation of `A'` fixing the two points cut out by `ε₁` and `ε₂` restricts uniquely to
  a `k`-derivation of `A`.

The first two are the sequence `0 → 𝒪_{X, x} → 𝒪_{X^ν, x'} × 𝒪_{X^ν, x''} → k → 0` that the
proof of Tag 0E68 takes from Tag 0C1X; the third is the local content of its right-to-left
direction. Unlike `Stacks.Curves.exact_integralClosure_of_isNodalAlgebra` and
`Stacks.Curves.existsUnique_restrict_of_fixes`, which take the nodality of the local ring and
the two residues as hypotheses, here both come from the node. -/
theorem exists_branchResidues_exact_integralClosure_of_isNode
    (hdim : topologicalKrullDim X = 1) (x : X) (hnode : IsNode k X x) :
    letI : Algebra k (X.presheaf.stalk x) := (fieldToStalk (X ↘ Spec (.of k)) x).hom.toAlgebra
    ∃ ε₁ ε₂ : ↥(integralClosure (X.presheaf.stalk x)
        (FractionRing (X.presheaf.stalk x))) →ₐ[k] k,
      ε₁ ≠ ε₂ ∧
        (∀ a : X.presheaf.stalk x,
            ε₁ (algebraMap (X.presheaf.stalk x) _ a) =
              ε₂ (algebraMap (X.presheaf.stalk x) _ a)) ∧
          Function.Injective (algebraMap (X.presheaf.stalk x)
            ↥(integralClosure (X.presheaf.stalk x) (FractionRing (X.presheaf.stalk x)))) ∧
            Function.Surjective (fun t : ↥(integralClosure (X.presheaf.stalk x)
                (FractionRing (X.presheaf.stalk x))) => ε₁ t - ε₂ t) ∧
              (∀ t : ↥(integralClosure (X.presheaf.stalk x)
                  (FractionRing (X.presheaf.stalk x))),
                  ε₁ t - ε₂ t = 0 ↔
                    t ∈ Set.range (algebraMap (X.presheaf.stalk x) _)) ∧
                ∀ D : Derivation k
                    ↥(integralClosure (X.presheaf.stalk x)
                      (FractionRing (X.presheaf.stalk x)))
                    ↥(integralClosure (X.presheaf.stalk x)
                      (FractionRing (X.presheaf.stalk x))),
                  NodalVectorFields.Fixes ε₁ D → NodalVectorFields.Fixes ε₂ D →
                    ∀ a : X.presheaf.stalk x, ∃! b : X.presheaf.stalk x,
                      algebraMap (X.presheaf.stalk x) _ b =
                        D (algebraMap (X.presheaf.stalk x) _ a) := by
  let : Algebra k (X.presheaf.stalk x) := (fieldToStalk (X ↘ Spec (.of k)) x).hom.toAlgebra
  have : IsNoetherianRing (X.presheaf.stalk x) :=
    (isNagataRing_stalk_of_locallyOfFiniteType k (X ↘ Spec (.of k)) x).isNoetherianRing
  obtain ⟨hnodal, ε₁, ε₂, hres, hne⟩ :=
    isNodalAlgebra_stalk_and_exists_branch_residues_of_isNode k X hdim x hnode
  obtain ⟨hinj, hsurj, hker⟩ :=
    exact_integralClosure_of_isNodalAlgebra k (X.presheaf.stalk x) hnodal ε₁ ε₂ hres hne
  exact ⟨ε₁, ε₂, hne, hres, hinj, hsurj, hker, fun D h₁ h₂ =>
    existsUnique_restrict_of_fixes k (X.presheaf.stalk x) hnodal ε₁ ε₂ hres hne D h₁ h₂⟩

end Node

section Tower

variable {k : Type u} [Field k] {X Y : Scheme.{u}}

/-- **The `k`-algebra structure on the stalk of a direct image factors through the local ring
of the base.** The structure map of `(ν_* 𝒪_Y)_x` pulls a global section of `Spec k` back to `X`,
then to `Y`, and takes its germ; the claim is that this is the germ on `X` followed by the stalk
comparison map of `ν^♯`, which is the naturality of the germ at the top open. -/
theorem algebraMap_directImageStalkFieldAlgebra (ν : Y ⟶ X) (hX : X ⟶ Spec (.of k)) (x : X)
    (c : k) :
    letI : Algebra k (X.presheaf.stalk x) := (fieldToStalk hX x).hom.toAlgebra
    letI := directImageStalkAlgebra ν x
    letI := directImageStalkFieldAlgebra ν hX x
    algebraMap k ((ν.base _* Y.presheaf).stalk x) c =
      algebraMap (X.presheaf.stalk x) ((ν.base _* Y.presheaf).stalk x)
        (algebraMap k (X.presheaf.stalk x) c) := by
  let : Algebra k (X.presheaf.stalk x) := (fieldToStalk hX x).hom.toAlgebra
  let := directImageStalkAlgebra ν x
  let := directImageStalkFieldAlgebra ν hX x
  change (ν.base _* Y.presheaf).germ (hX ⁻¹ᵁ ⊤) x trivial
      ((ν.app (hX ⁻¹ᵁ ⊤)).hom ((hX.app ⊤).hom ((Scheme.ΓSpecIso (.of k)).inv.hom c))) =
    ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map ν.c).hom
      (X.presheaf.germ ⊤ x trivial
        ((Scheme.Hom.appTop hX).hom ((Scheme.ΓSpecIso (.of k)).inv.hom c)))
  exact (TopCat.Presheaf.stalkFunctor_map_germ_apply (C := CommRingCat.{u}) ⊤ x trivial ν.c
    ((Scheme.Hom.appTop hX).hom ((Scheme.ΓSpecIso (.of k)).inv.hom c))).symm

end Tower

section Transport

/-- **Two distinct branch residues transport along an `A`-algebra equivalence.** If `S ≃ₐ[A] T`
and `T` carries two distinct `k`-algebra maps to `k` agreeing on the image of `A`, then so does
`S`, provided the `k`-algebra structure of `S` factors through `A`. -/
theorem exists_branchResidues_of_algEquiv {k : Type u} {A S T : Type*} [Field k] [CommRing A]
    [CommRing S] [CommRing T] [Algebra k A] [Algebra A S] [Algebra A T] [Algebra k S]
    [Algebra k T] [IsScalarTower k A T]
    (htow : ∀ c : k, algebraMap k S c = algebraMap A S (algebraMap k A c))
    (E : S ≃ₐ[A] T) (ε₁ ε₂ : T →ₐ[k] k)
    (hres : ∀ a : A, ε₁ (algebraMap A T a) = ε₂ (algebraMap A T a)) (hne : ε₁ ≠ ε₂) :
    ∃ δ₁ δ₂ : S →ₐ[k] k,
      (∀ a : A, δ₁ (algebraMap A S a) = δ₂ (algebraMap A S a)) ∧ δ₁ ≠ δ₂ := by
  have key : ∀ (ε : T →ₐ[k] k) (c : k), ε (E (algebraMap k S c)) = algebraMap k k c := by
    intro ε c
    rw [htow c, E.commutes, ← IsScalarTower.algebraMap_apply]
    exact ε.commutes c
  refine ⟨AlgHom.mk (ε₁.toRingHom.comp E.toAlgHom.toRingHom) (key ε₁),
    AlgHom.mk (ε₂.toRingHom.comp E.toAlgHom.toRingHom) (key ε₂), fun a => ?_, ?_⟩
  · change ε₁ (E (algebraMap A S a)) = ε₂ (E (algebraMap A S a))
    rw [E.commutes]
    exact hres a
  · intro hcon
    refine hne (AlgHom.ext fun t => ?_)
    have h : ε₁ (E (E.symm t)) = ε₂ (E (E.symm t)) :=
      congrArg (fun f : S →ₐ[k] k => f (E.symm t)) hcon
    rwa [E.apply_symm_apply] at h

end Transport

section Descent

open Stacks.AlgebraicGeometry.NormalizationQuotient Stacks.NormalizationStalkAmbient

variable (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u}) [IsReduced X]
  [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]

/-- **The two branch residues on the stalk of the direct image of the normalization.** At a
node, `Stacks.Curves.isNodalAlgebra_stalk_and_exists_branch_residues_of_isNode` transported along
Tag 0C3B(2), which identifies `(ν_* 𝒪_{X^ν})_x` with the integral closure of `𝒪_{X, x}` in its
total ring of fractions as an `𝒪_{X, x}`-algebra. -/
theorem exists_branchResidues_normalizationStalk_of_isNode
    (hfin : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (hdim : topologicalKrullDim X = 1) (x : X) (hnode : IsNode k X x) :
    letI : Algebra k (X.presheaf.stalk x) := (fieldToStalk (X ↘ Spec (.of k)) x).hom.toAlgebra
    letI := directImageStalkAlgebra (Scheme.normalization X hfin) x
    letI := directImageStalkFieldAlgebra (Scheme.normalization X hfin) (X ↘ Spec (.of k)) x
    IsNodalAlgebra k (X.presheaf.stalk x) ∧
      ∃ ε₁ ε₂ : (((Scheme.normalization X hfin).base _*
          (Scheme.normalizationScheme X hfin).presheaf).stalk x) →ₐ[k] k,
        (∀ a : X.presheaf.stalk x,
            ε₁ (algebraMap (X.presheaf.stalk x) _ a) =
              ε₂ (algebraMap (X.presheaf.stalk x) _ a)) ∧ ε₁ ≠ ε₂ := by
  let : Algebra k (X.presheaf.stalk x) := (fieldToStalk (X ↘ Spec (.of k)) x).hom.toAlgebra
  let := directImageStalkAlgebra (Scheme.normalization X hfin) x
  let := directImageStalkFieldAlgebra (Scheme.normalization X hfin) (X ↘ Spec (.of k)) x
  obtain ⟨hnodal, ε₁, ε₂, hres, hne⟩ :=
    isNodalAlgebra_stalk_and_exists_branch_residues_of_isNode k X hdim x hnode
  refine ⟨hnodal, exists_branchResidues_of_algEquiv (A := X.presheaf.stalk x)
    (fun c => algebraMap_directImageStalkFieldAlgebra (Scheme.normalization X hfin)
      (X ↘ Spec (.of k)) x c)
    (normalizationStalkAlgEquivIntegralClosureSelf X hfin x) ε₁ ε₂ hres hne⟩

/-- **The right-to-left direction of Tag 0E68, with the node data derived from the node.** Let
`k` be algebraically closed, `X` a reduced scheme locally of finite type over `k` of dimension
one, `ν : X^ν ⟶ X` its normalization and `D'` a vector field on `X^ν`. Suppose that at every
point `x` of `X` either `𝒪_{X, x} → (ν_* 𝒪_{X^ν})_x` is surjective — the points where `ν` is an
isomorphism — or `x` is a node and the derivation that `D'` induces on `(ν_* 𝒪_{X^ν})_x` fixes
every `k`-point of that stalk. Then `D'` is `ν^♯` applied to a unique vector field on `X`.

This is `Stacks.Curves.existsUnique_descend_normalization_of_fixes` with its node data — the
nodality of the local ring and the two branch residues — supplied from the node hypothesis
instead of assumed. At a node the `k`-points of the stalk are exactly the two residues at the
points of `X^ν` above `x`, so the hypothesis is the source's "`D'` fixes every `x^ν ∈ S`"; the
count of those points is not proved here, so the hypothesis is formally the stronger
quantification over all `k`-points — which is what the extension of a vector field satisfies,
by `Stacks.Curves.forall_fixes_of_extend_normalizationStalk_of_isNode`, so nothing is lost. -/
theorem existsUnique_descend_normalization_of_isNode
    (hfin : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (hdim : topologicalKrullDim X = 1)
    (D' : SheafDerivationOf (Scheme.normalization X hfin ≫ (X ↘ Spec (.of k))))
    (h : ∀ x : X,
      letI : Algebra k (X.presheaf.stalk x) := (fieldToStalk (X ↘ Spec (.of k)) x).hom.toAlgebra
      letI := directImageStalkAlgebra (Scheme.normalization X hfin) x
      letI := directImageStalkFieldAlgebra (Scheme.normalization X hfin) (X ↘ Spec (.of k)) x
      Function.Surjective
          (algebraMap (X.presheaf.stalk x)
            (((Scheme.normalization X hfin).base _*
              (Scheme.normalizationScheme X hfin).presheaf).stalk x)) ∨
        (IsNode k X x ∧ ∀ ε : (((Scheme.normalization X hfin).base _*
            (Scheme.normalizationScheme X hfin).presheaf).stalk x) →ₐ[k] k,
          NodalVectorFields.Fixes ε (stalkDerivation (Scheme.normalization X hfin) D' x))) :
    ∃! D : SheafDerivationOf (X ↘ Spec (.of k)), ∀ (U : X.Opens) (s : Γ(X, U)),
      ((Scheme.normalization X hfin).app U).hom (D.onSections s) =
        D'.onSections (((Scheme.normalization X hfin).app U).hom s) := by
  refine existsUnique_descend_normalization_of_fixes k X (X ↘ Spec (.of k)) hfin
    (fun x => (isNagataRing_stalk_of_locallyOfFiniteType k (X ↘ Spec (.of k)) x).isNoetherianRing)
    D' fun x => ?_
  rcases h x with hsurj | ⟨hnode, hfix⟩
  · exact Or.inl hsurj
  · obtain ⟨hnodal, ε₁, ε₂, hres, hne⟩ :=
      exists_branchResidues_normalizationStalk_of_isNode k X hfin hdim x hnode
    exact Or.inr ⟨hnodal, ε₁, ε₂, hres, hne, hfix ε₁, hfix ε₂⟩

/-- **At a point with a regular local ring the normalization is surjective on stalks.** This is
`Stacks.AlgebraicGeometry.NormalizationQuotient`'s
`normalizationStalkMap_surjective_of_isIntegrallyClosed` for a regular local ring, which is
integrally closed, in the form the descent criterion wants. -/
theorem surjective_algebraMap_normalizationStalk_of_isRegularLocalRing
    (hfin : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) (x : X)
    (hreg : IsRegularLocalRing (X.presheaf.stalk x)) :
    letI := directImageStalkAlgebra (Scheme.normalization X hfin) x
    Function.Surjective
      (algebraMap (X.presheaf.stalk x)
        (((Scheme.normalization X hfin).base _*
          (Scheme.normalizationScheme X hfin).presheaf).stalk x)) := by
  let := directImageStalkAlgebra (Scheme.normalization X hfin) x
  let : IsRegularLocalRing (X.presheaf.stalk x) := hreg
  exact normalizationStalkMap_surjective_of_isIntegrallyClosed X hfin x
    (isIntegrallyClosed_of_isRegularLocalRing (X.presheaf.stalk x))

/-- **The right-to-left direction of Tag 0E68, with the dichotomy stated intrinsically.** At
every point of `X` either the local ring is regular — where the normalization is an isomorphism
on stalks, so there is nothing to descend — or the point is a node and the derivation that `D'`
induces on `(ν_* 𝒪_{X^ν})_x` fixes every `k`-point of that stalk. Then `D'` is `ν^♯` applied to
a unique vector field on `X`.

This is `Stacks.Curves.existsUnique_descend_normalization_of_isNode` with the surjectivity
alternative replaced by the regularity of the local ring, which is the shape of the dichotomy of
`Stacks.Curves.HasAtWorstNodalSingularities`.
`Stacks.Curves.isRegularLocalRing_stalk_or_isNode_of_hasAtWorstNodalSingularities` deduces that
dichotomy from the predicate, and
`Stacks.Curves.existsUnique_descend_normalization_of_hasAtWorstNodalSingularities` is the
resulting statement whose only condition on `D'` is the one the source imposes. -/
theorem existsUnique_descend_normalization_of_isRegular_or_isNode
    (hfin : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (hdim : topologicalKrullDim X = 1)
    (D' : SheafDerivationOf (Scheme.normalization X hfin ≫ (X ↘ Spec (.of k))))
    (h : ∀ x : X,
      letI : Algebra k (X.presheaf.stalk x) := (fieldToStalk (X ↘ Spec (.of k)) x).hom.toAlgebra
      letI := directImageStalkFieldAlgebra (Scheme.normalization X hfin) (X ↘ Spec (.of k)) x
      IsRegularLocalRing (X.presheaf.stalk x) ∨
        (IsNode k X x ∧ ∀ ε : (((Scheme.normalization X hfin).base _*
            (Scheme.normalizationScheme X hfin).presheaf).stalk x) →ₐ[k] k,
          NodalVectorFields.Fixes ε (stalkDerivation (Scheme.normalization X hfin) D' x))) :
    ∃! D : SheafDerivationOf (X ↘ Spec (.of k)), ∀ (U : X.Opens) (s : Γ(X, U)),
      ((Scheme.normalization X hfin).app U).hom (D.onSections s) =
        D'.onSections (((Scheme.normalization X hfin).app U).hom s) := by
  refine existsUnique_descend_normalization_of_isNode k X hfin hdim D' fun x => ?_
  rcases h x with hreg | hnode
  · exact Or.inl (surjective_algebraMap_normalizationStalk_of_isRegularLocalRing X hfin x hreg)
  · exact Or.inr hnode

end Descent

end Stacks.Curves

end
