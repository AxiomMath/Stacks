module

public import StacksFrontier.AlgebraicGeometry.Curves.NodeDerivationExtensionStalk
public import StacksFrontier.RingTheory.Derivation.IntegralClosureUnique
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Every extension of a vector field at a node fixes every branch

Let `A` be the local ring of a node and `S` its normalization. The source of Tag 0E68 extends a
`k`-derivation of `A` to `S` and observes that the extension fixes the two points of `S` above
the node. `Stacks.Curves.existsUnique_extend_integralClosure_of_isNodalAlgebra` proves that for
the two points named in its statement; what is proved here is that *no* `k`-point of `S` escapes,
so that an extension satisfies the hypothesis under which
`Stacks.Curves.existsUnique_descend_normalization_of_isNode` descends it again. That is the step
which turns the two inclusions of the tag into the tag's equality.

The argument does not count the `k`-points of `S`. It uses instead that they all agree on `A`:
a `k`-algebra map from `A` to `k` is surjective, so its kernel is a maximal ideal of the local
ring `A` and therefore *the* maximal ideal, which pins the map down
(`Stacks.Curves.algHom_eq_of_isLocalRing`). So any `k`-point of `S` may be paired with any other
one, and a pair of distinct `k`-points agreeing on `A` is exactly the input that the extension
theorem wants. Since a derivation of `A` has at most one extension to `S`
(`Stacks.DerivationExtension.extend_integralClosure_unique_fractionRing`), the extension fixing
the chosen pair is the extension one started with.

## Main results

* `Stacks.Curves.algHom_eq_of_isLocalRing` — a local `k`-algebra admits at most one `k`-algebra
  map to `k`.
* `Stacks.Curves.extend_eq_of_algEquiv` — uniqueness of the extension of a derivation transports
  along an algebra equivalence.
* `Stacks.Curves.forall_fixes_of_extend_of_algEquiv` — **an extension of a derivation of `A`
  fixes every `k`-point of `S`**, for `S` equivalent to a ring on which pairs of distinct
  `k`-points admit unique fixing extensions.
* `Stacks.Curves.forall_fixes_of_extend_normalizationStalk_of_isNode` — the same at a node of a
  curve, for the stalk of the direct image of the structure sheaf of the normalization.

## References

* [Stacks Project, Tag 0E68](https://stacks.math.columbia.edu/tag/0E68)
* [Stacks Project, Tag 0C1X](https://stacks.math.columbia.edu/tag/0C1X)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing

universe u v w

namespace Stacks.Curves

section LocalPoint

/-- **A local `k`-algebra has at most one `k`-point.** A `k`-algebra map `A → k` is surjective
because it is the identity on `k`, so its kernel is a maximal ideal; in a local ring that is the
maximal ideal, the same for every such map, and a `k`-algebra map to `k` is determined by its
kernel. -/
theorem algHom_eq_of_isLocalRing {k : Type u} {A : Type v} [Field k] [CommRing A]
    [IsLocalRing A] [Algebra k A] (φ ψ : A →ₐ[k] k) : φ = ψ := by
  have hker : ∀ χ : A →ₐ[k] k, RingHom.ker (χ : A →+* k) = maximalIdeal A := fun χ =>
    eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective (χ : A →+* k)
      fun c => ⟨algebraMap k A c, χ.commutes c⟩)
  refine AlgHom.ext fun a => ?_
  have hmem : a - algebraMap k A (φ a) ∈ RingHom.ker (φ : A →+* k) := by
    rw [RingHom.mem_ker]
    change φ (a - algebraMap k A (φ a)) = 0
    simp
  rw [hker φ, ← hker ψ, RingHom.mem_ker] at hmem
  have h : ψ (a - algebraMap k A (φ a)) = 0 := hmem
  have h2 : ψ a = φ a := sub_eq_zero.mp (by simpa using h)
  exact h2.symm

end LocalPoint

section Transport

variable {k : Type u} {S : Type v} {T : Type w} [Field k] [CommRing S] [CommRing T]
variable [Algebra k S] [Algebra k T]
variable {A : Type*} [CommRing A] [Algebra k A] [Algebra A S] [Algebra A T]

/-- Conjugating an extension of `D` to `S` along `E` gives an extension of `D` to `T`. -/
private theorem congrDerivation_extends (E : S ≃ₐ[k] T)
    (hE : ∀ a : A, E (algebraMap A S a) = algebraMap A T a)
    (D : Derivation k A A) (F : Derivation k S S)
    (hF : ∀ a : A, F (algebraMap A S a) = algebraMap A S (D a)) (a : A) :
    congrDerivation E F (algebraMap A T a) = algebraMap A T (D a) := by
  rw [congrDerivation_apply, ← hE a, E.symm_apply_apply, hF, hE]

/-- **Uniqueness of the extension of a derivation transports along an algebra equivalence.**
If a `k`-derivation of `A` has at most one extension to `T`, and `E : S ≃ₐ[k] T` is an
equivalence over `A`, then it has at most one extension to `S`: conjugating by `E` turns an
extension on `S` into one on `T`, and conjugating back is the identity. -/
theorem extend_eq_of_algEquiv (E : S ≃ₐ[k] T)
    (hE : ∀ a : A, E (algebraMap A S a) = algebraMap A T a)
    (huniq : ∀ (D : Derivation k A A) (G₁ G₂ : Derivation k T T),
      (∀ a : A, G₁ (algebraMap A T a) = algebraMap A T (D a)) →
      (∀ a : A, G₂ (algebraMap A T a) = algebraMap A T (D a)) → G₁ = G₂)
    (D : Derivation k A A) (F₁ F₂ : Derivation k S S)
    (h₁ : ∀ a : A, F₁ (algebraMap A S a) = algebraMap A S (D a))
    (h₂ : ∀ a : A, F₂ (algebraMap A S a) = algebraMap A S (D a)) :
    F₁ = F₂ := by
  have hT := huniq D _ _ (congrDerivation_extends E hE D F₁ h₁)
    (congrDerivation_extends E hE D F₂ h₂)
  rw [← congrDerivation_symm_congrDerivation E F₁, ← congrDerivation_symm_congrDerivation E F₂,
    hT]

/-- **An extension of a derivation of `A` to `S` fixes every `k`-point of `S`.** Suppose `S` is
equivalent over `A` to a ring `T` on which every pair of distinct `k`-algebra maps to `k`
agreeing on `A` admits a unique extension of a given derivation of `A` fixing both of them, that
extensions to `T` are unique, that `A` is local with its `k`-algebra structure inherited by `S`,
and that `S` carries at least two distinct `k`-points. Then every extension to `S` of a
`k`-derivation of `A` fixes every `k`-point of `S`.

Each `k`-point of `S` restricts to a `k`-point of the local ring `A`, and there is only one of
those (`Stacks.Curves.algHom_eq_of_isLocalRing`), so any two `k`-points of `S` agree on `A` and
a given one can be paired with a different one. The extension fixing that pair is the given
extension, by `Stacks.Curves.extend_eq_of_algEquiv`. -/
theorem forall_fixes_of_extend_of_algEquiv [IsLocalRing A]
    (htow : ∀ c : k, algebraMap k S c = algebraMap A S (algebraMap k A c))
    (E : S ≃ₐ[k] T) (hE : ∀ a : A, E (algebraMap A S a) = algebraMap A T a)
    (hpair : ∃ δ₁ δ₂ : S →ₐ[k] k, δ₁ ≠ δ₂)
    (hext : ∀ ε₁ ε₂ : T →ₐ[k] k, ε₁ ≠ ε₂ →
      (∀ a : A, ε₁ (algebraMap A T a) = ε₂ (algebraMap A T a)) →
      ∀ D : Derivation k A A, ∃! G : Derivation k T T,
        (∀ a : A, G (algebraMap A T a) = algebraMap A T (D a)) ∧
          NodalVectorFields.Fixes ε₁ G ∧ NodalVectorFields.Fixes ε₂ G)
    (huniq : ∀ (D : Derivation k A A) (G₁ G₂ : Derivation k T T),
      (∀ a : A, G₁ (algebraMap A T a) = algebraMap A T (D a)) →
      (∀ a : A, G₂ (algebraMap A T a) = algebraMap A T (D a)) → G₁ = G₂)
    (D : Derivation k A A) (F : Derivation k S S)
    (hF : ∀ a : A, F (algebraMap A S a) = algebraMap A S (D a)) :
    ∀ δ : S →ₐ[k] k, NodalVectorFields.Fixes δ F := by
  classical
  -- every `k`-point of `S` restricts to the unique `k`-point of the local ring `A`
  have hrestrict : ∀ δ δ' : S →ₐ[k] k, ∀ a : A,
      δ (algebraMap A S a) = δ' (algebraMap A S a) := by
    intro δ δ'
    have key : ∀ χ : S →ₐ[k] k, ∃ ρ : A →ₐ[k] k, ∀ a : A, ρ a = χ (algebraMap A S a) := by
      intro χ
      refine ⟨{ toRingHom := (χ : S →+* k).comp (algebraMap A S)
                commutes' := fun c => ?_ }, fun _ => rfl⟩
      change χ (algebraMap A S (algebraMap k A c)) = c
      rw [← htow c]
      exact χ.commutes c
    obtain ⟨ρ, hρ⟩ := key δ
    obtain ⟨ρ', hρ'⟩ := key δ'
    intro a
    rw [← hρ, ← hρ', algHom_eq_of_isLocalRing ρ ρ']
  -- a second `k`-point of `S`, distinct from the given one
  have hother : ∀ δ : S →ₐ[k] k, ∃ δ' : S →ₐ[k] k, δ' ≠ δ := by
    obtain ⟨δ₁, δ₂, hne⟩ := hpair
    intro δ
    by_cases h : δ₁ = δ
    · exact ⟨δ₂, fun hc => hne (h.trans hc.symm)⟩
    · exact ⟨δ₁, h⟩
  have hEs : ∀ s : S, E.symm (E s) = s := fun s => E.symm_apply_apply s
  intro δ
  obtain ⟨δ', hne⟩ := hother δ
  -- push the pair over to `T`
  set ε : T →ₐ[k] k := δ.comp (E.symm : T →ₐ[k] S) with hεdef
  set ε' : T →ₐ[k] k := δ'.comp (E.symm : T →ₐ[k] S) with hε'def
  have hneT : ε ≠ ε' := by
    intro hc
    refine hne (AlgHom.ext fun s => ?_).symm
    have h : δ (E.symm (E s)) = δ' (E.symm (E s)) :=
      congrArg (fun f : T →ₐ[k] k => f (E s)) hc
    rwa [hEs] at h
  have hresT : ∀ a : A, ε (algebraMap A T a) = ε' (algebraMap A T a) := by
    intro a
    change δ (E.symm (algebraMap A T a)) = δ' (E.symm (algebraMap A T a))
    rw [← hE a, hEs]
    exact hrestrict δ δ' a
  obtain ⟨G, ⟨hGext, hGfix, -⟩, -⟩ := hext ε ε' hneT hresT D
  -- the conjugate of `F` is an extension of `D` to `T`, hence is `G`
  have hFG : congrDerivation E F = G :=
    huniq D _ G (congrDerivation_extends E hE D F hF) hGext
  intro s hs
  have hεs : ε (E s) = 0 := by
    change δ (E.symm (E s)) = 0
    rwa [hEs]
  have := hGfix (E s) hεs
  rw [← hFG, congrDerivation_apply, hEs] at this
  change δ (F s) = 0
  have hback : ε (E (F s)) = δ (F s) := by
    change δ (E.symm (E (F s))) = δ (F s)
    rw [hEs]
  rwa [hback] at this

/-- **The same over an equivalence of `A`-algebras.** This is
`Stacks.Curves.forall_fixes_of_extend_of_algEquiv` with the equivalence given over `A` rather
than over `k`, which is the form in which Tag 0C3B(2) produces it; the `k`-algebra structure of
`S` is a hypothesis because in the application it goes through a global section of the base
rather than through the local ring. -/
theorem forall_fixes_of_extend_of_algEquivTower [IsLocalRing A] [IsScalarTower k A T]
    (htow : ∀ c : k, algebraMap k S c = algebraMap A S (algebraMap k A c))
    (E : S ≃ₐ[A] T)
    (hpair : ∃ δ₁ δ₂ : S →ₐ[k] k, δ₁ ≠ δ₂)
    (hext : ∀ ε₁ ε₂ : T →ₐ[k] k, ε₁ ≠ ε₂ →
      (∀ a : A, ε₁ (algebraMap A T a) = ε₂ (algebraMap A T a)) →
      ∀ D : Derivation k A A, ∃! G : Derivation k T T,
        (∀ a : A, G (algebraMap A T a) = algebraMap A T (D a)) ∧
          NodalVectorFields.Fixes ε₁ G ∧ NodalVectorFields.Fixes ε₂ G)
    (huniq : ∀ (D : Derivation k A A) (G₁ G₂ : Derivation k T T),
      (∀ a : A, G₁ (algebraMap A T a) = algebraMap A T (D a)) →
      (∀ a : A, G₂ (algebraMap A T a) = algebraMap A T (D a)) → G₁ = G₂)
    (D : Derivation k A A) (F : Derivation k S S)
    (hF : ∀ a : A, F (algebraMap A S a) = algebraMap A S (D a)) :
    ∀ δ : S →ₐ[k] k, NodalVectorFields.Fixes δ F :=
  forall_fixes_of_extend_of_algEquiv htow
    (AlgEquiv.ofRingEquiv (f := E.toRingEquiv) fun c => by
      change E (algebraMap k S c) = algebraMap k T c
      rw [htow c, E.commutes, ← IsScalarTower.algebraMap_apply k A T])
    E.commutes hpair hext huniq D F hF

end Transport

section Node

open Stacks.AlgebraicGeometry.NormalizationQuotient Stacks.NormalizationStalkAmbient

variable (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u}) [IsReduced X]
  [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]

/-- **At a node, an extension of a derivation to the stalk of the direct image fixes every
`k`-point of that stalk.** Let `k` be algebraically closed, `X` a reduced scheme locally of
finite type over `k` of dimension one, `ν : X^ν ⟶ X` its normalization and `x` a node. If a
`k`-derivation `F` of `(ν_* 𝒪_{X^ν})_x` restricts on `𝒪_{X, x}` to a `k`-derivation `D` of that
local ring, then `F` fixes every `k`-algebra map from the stalk to `k`.

This is `Stacks.Curves.forall_fixes_of_extend_of_algEquiv` transported along Tag 0C3B(2),
which identifies the stalk with the integral closure of `𝒪_{X, x}` in its total ring of
fractions. The two distinct `k`-points it needs are the branch residues of
`Stacks.Curves.exists_branchResidues_normalizationStalk_of_isNode`, the extension theorem for a
pair of them is `Stacks.Curves.existsUnique_extend_integralClosure_of_isNodalAlgebra`, and the
uniqueness of extensions is
`Stacks.DerivationExtension.extend_integralClosure_unique_fractionRing`.

The source's observation that the extension "fixes `x'`" is made for the two points above the
node; the statement here is for every `k`-point because that is the hypothesis of
`Stacks.Curves.existsUnique_descend_normalization_of_isNode`, and the two conditions coincide
without the count of the `k`-points being needed. -/
@[sga "7 X 2.33" "special case"]
theorem forall_fixes_of_extend_normalizationStalk_of_isNode
    (hfin : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (hdim : topologicalKrullDim X = 1) (x : X) (hnode : IsNode k X x) :
    letI : Algebra k (X.presheaf.stalk x) := (fieldToStalk (X ↘ Spec (.of k)) x).hom.toAlgebra
    letI := directImageStalkAlgebra (Scheme.normalization X hfin) x
    letI := directImageStalkFieldAlgebra (Scheme.normalization X hfin) (X ↘ Spec (.of k)) x
    ∀ (D : Derivation k (X.presheaf.stalk x) (X.presheaf.stalk x))
      (F : Derivation k (((Scheme.normalization X hfin).base _*
            (Scheme.normalizationScheme X hfin).presheaf).stalk x)
          (((Scheme.normalization X hfin).base _*
            (Scheme.normalizationScheme X hfin).presheaf).stalk x)),
      (∀ a : X.presheaf.stalk x,
          F (algebraMap (X.presheaf.stalk x) _ a) =
            algebraMap (X.presheaf.stalk x) _ (D a)) →
        ∀ ε : (((Scheme.normalization X hfin).base _*
            (Scheme.normalizationScheme X hfin).presheaf).stalk x) →ₐ[k] k,
          NodalVectorFields.Fixes ε F := by
  let : Algebra k (X.presheaf.stalk x) := (fieldToStalk (X ↘ Spec (.of k)) x).hom.toAlgebra
  let := directImageStalkAlgebra (Scheme.normalization X hfin) x
  let := directImageStalkFieldAlgebra (Scheme.normalization X hfin) (X ↘ Spec (.of k)) x
  have : IsNoetherianRing (X.presheaf.stalk x) :=
    (isNagataRing_stalk_of_locallyOfFiniteType k (X ↘ Spec (.of k)) x).isNoetherianRing
  obtain ⟨hnodal, ε₁, ε₂, -, hne⟩ :=
    exists_branchResidues_normalizationStalk_of_isNode k X hfin hdim x hnode
  intro D F hF
  exact forall_fixes_of_extend_of_algEquivTower (A := X.presheaf.stalk x)
    (algebraMap_directImageStalkFieldAlgebra (Scheme.normalization X hfin)
      (X ↘ Spec (.of k)) x)
    (normalizationStalkAlgEquivIntegralClosureSelf X hfin x) ⟨ε₁, ε₂, hne⟩
    (fun δ₁ δ₂ hne' hres' D₀ =>
      existsUnique_extend_integralClosure_of_isNodalAlgebra k (X.presheaf.stalk x) hnodal
        δ₁ δ₂ hres' hne' D₀)
    (fun D₀ G₁ G₂ h₁ h₂ =>
      Stacks.DerivationExtension.extend_integralClosure_unique_fractionRing D₀ G₁ G₂ h₁ h₂)
    D F hF

end Node

end Stacks.Curves

end
