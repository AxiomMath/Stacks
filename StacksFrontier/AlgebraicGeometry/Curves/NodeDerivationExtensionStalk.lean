module

public import StacksFrontier.AlgebraicGeometry.Curves.NodeBranchResidues
public import StacksFrontier.AlgebraicGeometry.Curves.NodeDerivationExtension
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Extending a vector field at a node, on the stalk of the direct image

Let `k` be algebraically closed, let `X` be a reduced scheme locally of finite type over `k` of
dimension one, let `ν : X^ν ⟶ X` be its normalization and let `x` be a node of `X`. Then the
stalk `(ν_* 𝒪_{X^ν})_x` carries two distinct `k`-algebra maps `ε₁, ε₂` to `k` agreeing on
`𝒪_{X, x}` — the residues at the two points of `X^ν` above `x` — and every `k`-derivation of
`𝒪_{X, x}` is the restriction of a unique `k`-derivation of `(ν_* 𝒪_{X^ν})_x`, which
automatically fixes both of those points.

This is the left-to-right direction of Tag 0E68 at one node, with the node data derived from
`IsNode` rather than assumed, in exactly the form in which
`Stacks.Curves.exists_branchResidues_exact_integralClosure_of_isNode` states the right-to-left
direction. The two together are the local content of the equality of the tag.

## Main definitions

* `Stacks.Curves.congrDerivation` — conjugation of a `k`-derivation by a `k`-algebra
  equivalence.

## Main results

* `Stacks.Curves.existsUnique_extend_of_algEquiv` — the extension-and-fixing property transports
  along a `k`-algebra equivalence.
* `Stacks.Curves.exists_branchResidues_existsUnique_extend_of_algEquiv` — the same for an
  equivalence of algebras over the base ring whose `k`-structure factors through it, carrying
  the two branch residues along.
* `Stacks.Curves.exists_branchResidues_existsUnique_extend_normalizationStalk_of_isNode` — the
  extension at the stalk of the direct image at a node.

## Implementation notes

The ring-theoretic statement is
`Stacks.Curves.existsUnique_extend_integralClosure_of_isNodalAlgebra`, about
`integralClosure 𝒪_{X, x} (Frac 𝒪_{X, x})`. The transport to `(ν_* 𝒪_{X^ν})_x` is along Tag
0C3B(2), as for the branch residues themselves; what it needs beyond
`Stacks.Curves.exists_branchResidues_of_algEquiv` is that a derivation can be conjugated by the
equivalence (`Stacks.Curves.congrDerivation`). Conjugation is a bijection on derivations and
matches both the extension property and the `Fixes` conditions on the two sides, so the
uniqueness statement transports as it stands.

The equivalence of Tag 0C3B(2) is one of `𝒪_{X, x}`-algebras; that it is one of `k`-algebras is
the factorisation `Stacks.Curves.algebraMap_directImageStalkFieldAlgebra` of the `k`-structure of
the stalk of the direct image through `𝒪_{X, x}`, which is why that factorisation is a hypothesis
of `Stacks.Curves.exists_branchResidues_existsUnique_extend_of_algEquiv` rather than an
`IsScalarTower` instance — the `k`-algebra structure on that stalk goes through a global section
of the base and is not defined as a composite.

## What is not done here

The sheaf-level left-to-right direction of Tag 0E68 — producing a vector field on `X^ν` from
one on `X` — is not proved here. It is
`Stacks.Curves.existsUnique_extend_normalization_of_hasAtWorstNodalSingularities`, and it does
not glue the stalkwise extensions obtained in this file: the gluing runs over an open cover
(`Stacks.Curves.existsUnique_sheafDerivationOf_of_affineCover`) with the datum over an affine
open a single `k`-derivation of the coordinate ring
(`Stacks.AlgebraicGeometry.DifferentialsAffine.exists_rawOp_of_leibniz`, resting on the
affine-open form of Tag 01UO), the derivation over the preimage of an affine open being
`Stacks.Curves.exists_leibniz_extension_normalizationSections`. There is still no passage from
a compatible family of derivations of the *stalks* to a vector field; what this file
contributes to the tag is instead the fixing of the branch points, which
`Stacks.Curves.forall_fixes_of_extend_normalizationStalk_of_isNode` strengthens to every
`k`-point of the stalk and
`Stacks.Curves.existsUnique_extend_fixing_normalization_of_hasAtWorstNodalSingularities`
applies to the glued extension.

The passage from the `k`-points of `(ν_* 𝒪_{X^ν})_x` to the points of `X^ν` above `x` is
`Stacks.Curves.fixes_of_forall_fixes_stalkDerivation`, which the tag,
`Stacks.Curves.NodalVectorFields.range_branchPair`, uses to state the fixing condition in the
source's form.

## References

* [Stacks Project, Tag 0E68](https://stacks.math.columbia.edu/tag/0E68)
* [Stacks Project, Tag 0C1X](https://stacks.math.columbia.edu/tag/0C1X)
* [Stacks Project, Tag 0C3B](https://stacks.math.columbia.edu/tag/0C3B)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing

universe u v w

namespace Stacks.Curves

section Transport

variable {k : Type u} {S : Type v} {T : Type w} [Field k] [CommRing S] [CommRing T]
variable [Algebra k S] [Algebra k T]

/-- **Conjugation of a derivation by an algebra equivalence.** For `E : S ≃ₐ[k] T` and a
`k`-derivation `D` of `S`, the map `t ↦ E (D (E.symm t))` is a `k`-derivation of `T`. -/
def congrDerivation (E : S ≃ₐ[k] T) (D : Derivation k S S) : Derivation k T T where
  toFun t := E (D (E.symm t))
  map_add' t s := by simp
  map_smul' c t := by simp
  map_one_eq_zero' := by simp
  leibniz' t s := by
    change E (D (E.symm (t * s))) = t • E (D (E.symm s)) + s • E (D (E.symm t))
    simp only [smul_eq_mul]
    rw [map_mul, Derivation.leibniz]
    simp only [smul_eq_mul, map_add, map_mul, AlgEquiv.apply_symm_apply]

/-- The conjugate derivation `congrDerivation E D` sends `t` to `E (D (E.symm t))`. -/
@[simp] theorem congrDerivation_apply (E : S ≃ₐ[k] T) (D : Derivation k S S) (t : T) :
    congrDerivation E D t = E (D (E.symm t)) := rfl

/-- Conjugating by `E` and then by `E.symm` is the identity on derivations. -/
theorem congrDerivation_symm_congrDerivation (E : S ≃ₐ[k] T) (D : Derivation k S S) :
    congrDerivation E.symm (congrDerivation E D) = D :=
  Derivation.ext fun s => by simp

variable {A : Type*} [CommRing A] [Algebra k A] [Algebra A S] [Algebra A T]

/-- **The extension of a derivation, and its fixing of two points, transports along an algebra
equivalence.** Let `E : S ≃ₐ[k] T` be compatible with the two `A`-algebra structures. If every
`k`-derivation of `A` has a unique extension to `T` fixing the points cut out by `δ₁` and `δ₂`,
the same holds on `S` for the points cut out by `δ₁ ∘ E` and `δ₂ ∘ E`. -/
theorem existsUnique_extend_of_algEquiv (E : S ≃ₐ[k] T)
    (hE : ∀ a : A, E (algebraMap A S a) = algebraMap A T a) (δ₁ δ₂ : T →ₐ[k] k)
    (D : Derivation k A A)
    (h : ∃! D' : Derivation k T T,
      (∀ a : A, D' (algebraMap A T a) = algebraMap A T (D a)) ∧
        NodalVectorFields.Fixes δ₁ D' ∧ NodalVectorFields.Fixes δ₂ D') :
    ∃! D' : Derivation k S S,
      (∀ a : A, D' (algebraMap A S a) = algebraMap A S (D a)) ∧
        NodalVectorFields.Fixes (δ₁.comp (E : S →ₐ[k] T)) D' ∧
        NodalVectorFields.Fixes (δ₂.comp (E : S →ₐ[k] T)) D' := by
  obtain ⟨D', ⟨hext, hf₁, hf₂⟩, huniq⟩ := h
  have hEs : ∀ a : A, E.symm (algebraMap A T a) = algebraMap A S a := by
    intro a
    rw [← hE a, E.symm_apply_apply]
  have hfwd : ∀ G : Derivation k S S,
      (∀ a : A, G (algebraMap A S a) = algebraMap A S (D a)) →
      NodalVectorFields.Fixes (δ₁.comp (E : S →ₐ[k] T)) G →
      NodalVectorFields.Fixes (δ₂.comp (E : S →ₐ[k] T)) G →
      (∀ a : A, congrDerivation E G (algebraMap A T a) = algebraMap A T (D a)) ∧
        NodalVectorFields.Fixes δ₁ (congrDerivation E G) ∧
        NodalVectorFields.Fixes δ₂ (congrDerivation E G) := by
    intro G hg h₁ h₂
    refine ⟨fun a => ?_, fun t htt => ?_, fun t htt => ?_⟩
    · rw [congrDerivation_apply, hEs, hg, hE]
    · simpa using h₁ (E.symm t) (by simpa using htt)
    · simpa using h₂ (E.symm t) (by simpa using htt)
  refine ⟨congrDerivation E.symm D', ⟨fun a => ?_, fun s hs => ?_, fun s hs => ?_⟩, ?_⟩
  · rw [congrDerivation_apply, AlgEquiv.symm_symm, hE, hext, hEs]
  · simpa using hf₁ (E s) (by simpa using hs)
  · simpa using hf₂ (E s) (by simpa using hs)
  · rintro G ⟨hg, h₁, h₂⟩
    rw [← huniq (congrDerivation E G) (hfwd G hg h₁ h₂), congrDerivation_symm_congrDerivation]

/-- **The two branch residues and the unique extension transport along an equivalence of
`A`-algebras.** Let `S` and `T` be `A`-algebras which are also `k`-algebras, the structure of `S`
factoring through `A` by `htow` and that of `T` by the tower instance, and let `E : S ≃ₐ[A] T`.
If `T` carries two distinct `k`-algebra maps to `k` agreeing on `A` and every `k`-derivation of
`A` extends uniquely to `T` fixing the two points they cut out, then so does `S`.

The `k`-structure of `S` is a hypothesis rather than an instance because in the application `S`
is the stalk of a direct image, whose `k`-algebra structure goes through a global section of the
base rather than through the local ring. -/
theorem exists_branchResidues_existsUnique_extend_of_algEquiv
    (htow : ∀ c : k, algebraMap k S c = algebraMap A S (algebraMap k A c))
    [IsScalarTower k A T] (E : S ≃ₐ[A] T) (ε₁ ε₂ : T →ₐ[k] k) (hne : ε₁ ≠ ε₂)
    (hres : ∀ a : A, ε₁ (algebraMap A T a) = ε₂ (algebraMap A T a))
    (hext : ∀ D : Derivation k A A, ∃! D' : Derivation k T T,
      (∀ a : A, D' (algebraMap A T a) = algebraMap A T (D a)) ∧
        NodalVectorFields.Fixes ε₁ D' ∧ NodalVectorFields.Fixes ε₂ D') :
    ∃ δ₁ δ₂ : S →ₐ[k] k, δ₁ ≠ δ₂ ∧
      (∀ a : A, δ₁ (algebraMap A S a) = δ₂ (algebraMap A S a)) ∧
      ∀ D : Derivation k A A, ∃! D' : Derivation k S S,
        (∀ a : A, D' (algebraMap A S a) = algebraMap A S (D a)) ∧
          NodalVectorFields.Fixes δ₁ D' ∧ NodalVectorFields.Fixes δ₂ D' := by
  let E' : S ≃ₐ[k] T := AlgEquiv.ofRingEquiv (f := E.toRingEquiv) fun c => by
    show E (algebraMap k S c) = algebraMap k T c
    rw [htow c, E.commutes, ← IsScalarTower.algebraMap_apply k A T]
  have hE : ∀ a : A, E' (algebraMap A S a) = algebraMap A T a := E.commutes
  refine ⟨ε₁.comp (E' : S →ₐ[k] T), ε₂.comp (E' : S →ₐ[k] T), ?_, fun a => ?_, fun D => ?_⟩
  · intro hcon
    refine hne (AlgHom.ext fun t => ?_)
    have h : ε₁ (E' (E'.symm t)) = ε₂ (E' (E'.symm t)) :=
      congrArg (fun f : S →ₐ[k] k => f (E'.symm t)) hcon
    rwa [E'.apply_symm_apply] at h
  · show ε₁ (E' (algebraMap A S a)) = ε₂ (E' (algebraMap A S a))
    rw [hE]
    exact hres a
  · exact existsUnique_extend_of_algEquiv E' hE ε₁ ε₂ D (hext D)

end Transport

section Node

open Stacks.AlgebraicGeometry.NormalizationQuotient Stacks.NormalizationStalkAmbient

variable (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u}) [IsReduced X]
  [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]

/-- **The left-to-right direction of Tag 0E68 on the stalk of the direct image at a node.** At a
node `x` of a reduced scheme locally of finite type of dimension one over an algebraically closed
field, the stalk `(ν_* 𝒪_{X^ν})_x` carries two distinct `k`-algebra maps `ε₁, ε₂` to `k`
agreeing on `𝒪_{X, x}`, and every `k`-derivation of `𝒪_{X, x}` is the restriction of a unique
`k`-derivation of that stalk, which fixes both of the points `ε₁` and `ε₂` cut out.

This is the counterpart of
`Stacks.Curves.exists_branchResidues_exact_integralClosure_of_isNode`, which is the right-to-left
direction, with the node data likewise derived from `IsNode` rather than assumed. -/
@[sga "7 X 2.33" "special case"]
theorem exists_branchResidues_existsUnique_extend_normalizationStalk_of_isNode
    (hfin : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (hdim : topologicalKrullDim X = 1) (x : X) (hnode : IsNode k X x) :
    letI : Algebra k (X.presheaf.stalk x) := (fieldToStalk (X ↘ Spec (.of k)) x).hom.toAlgebra
    letI := directImageStalkAlgebra (Scheme.normalization X hfin) x
    letI := directImageStalkFieldAlgebra (Scheme.normalization X hfin) (X ↘ Spec (.of k)) x
    ∃ ε₁ ε₂ : (((Scheme.normalization X hfin).base _*
        (Scheme.normalizationScheme X hfin).presheaf).stalk x) →ₐ[k] k,
      ε₁ ≠ ε₂ ∧
        (∀ a : X.presheaf.stalk x,
            ε₁ (algebraMap (X.presheaf.stalk x) _ a) =
              ε₂ (algebraMap (X.presheaf.stalk x) _ a)) ∧
          ∀ D : Derivation k (X.presheaf.stalk x) (X.presheaf.stalk x),
            ∃! D' : Derivation k
                (((Scheme.normalization X hfin).base _*
                  (Scheme.normalizationScheme X hfin).presheaf).stalk x)
                (((Scheme.normalization X hfin).base _*
                  (Scheme.normalizationScheme X hfin).presheaf).stalk x),
              (∀ a : X.presheaf.stalk x,
                  D' (algebraMap (X.presheaf.stalk x) _ a) =
                    algebraMap (X.presheaf.stalk x) _ (D a)) ∧
                NodalVectorFields.Fixes ε₁ D' ∧ NodalVectorFields.Fixes ε₂ D' := by
  let : Algebra k (X.presheaf.stalk x) := (fieldToStalk (X ↘ Spec (.of k)) x).hom.toAlgebra
  let := directImageStalkAlgebra (Scheme.normalization X hfin) x
  let := directImageStalkFieldAlgebra (Scheme.normalization X hfin) (X ↘ Spec (.of k)) x
  have : IsNoetherianRing (X.presheaf.stalk x) :=
    (isNagataRing_stalk_of_locallyOfFiniteType k (X ↘ Spec (.of k)) x).isNoetherianRing
  obtain ⟨hnodal, ε₁, ε₂, hres, hne⟩ :=
    isNodalAlgebra_stalk_and_exists_branch_residues_of_isNode k X hdim x hnode
  exact exists_branchResidues_existsUnique_extend_of_algEquiv
    (A := X.presheaf.stalk x)
    (fun c => algebraMap_directImageStalkFieldAlgebra (Scheme.normalization X hfin)
      (X ↘ Spec (.of k)) x c)
    (normalizationStalkAlgEquivIntegralClosureSelf X hfin x) ε₁ ε₂ hne hres
    (fun D => existsUnique_extend_integralClosure_of_isNodalAlgebra k (X.presheaf.stalk x)
      hnodal ε₁ ε₂ hres hne D)

end Node

end Stacks.Curves

end
