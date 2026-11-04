module

public import StacksFrontier.Deformation.Examples.Geometric.SpacesInfinitesimalAutomorphismsLinear
public import StacksFrontier.Deformation.Examples.Geometric.SpacesFiniteDimensionalDerivations
public import StacksFrontier.Deformation.Examples.Geometric.SpacesRimSchlessinger

/-!
# Stacks 0E42: `Inf(𝓓_X)` and `T𝓓_X` are finite dimensional for a proper algebraic space

In Example 0E3Z let `X` be an algebraic space over the residue field `k`, with deformation
category `𝓓_X`.  [Stacks Project, Tag 0E42]: if `X` is proper over `k`, then `Inf(𝓓_X)` and `T𝓓_X`
are finite dimensional.

The source's proof: by Stacks 0E41 it suffices to show that `Ext⁰_{𝒪_X}(NL_{X/k}, 𝒪_X)` and
`Ext¹_{𝒪_X}(NL_{X/k}, 𝒪_X)` are finite dimensional; `NL_{X/k}` has coherent cohomology sheaves,
zero outside degrees `-1` and `0` (Stacks 0D0Z, `X` being Noetherian), so Stacks 0D0T applies.

## The infinitesimal automorphisms

`Inf(𝓓_X)` is the group `Deformation.infinitesimalAutomorphismGroup` of Stacks 06JS, at every point
`x₀` over `k` and every pushforward `i : x₀ ⟶ xε` along a dual-number pair, with the vector-space
structure of Stacks 06JV: addition is composition and a scalar `c` acts by pushforward along
`ε ↦ c ε`.  By the first display of Stacks 0E41 in its `k`-linear form (the first identification
`Deformation.Examples.spaceInfinitesimalAutomorphismGroupMulEquivDerivations` and its compatibility
with the rescalings of the dual numbers,
`Deformation.Examples.spaceInfinitesimalAutomorphismGroupMulEquivDerivations_pushforward`) it is
`Der_k(𝒪_X, 𝒪_X) = Hom_{𝒪_X}(Ω_{X/k}, 𝒪_X) = Ext⁰_{𝒪_X}(NL_{X/k}, 𝒪_X)` as a `k`-vector space,
finite dimensional by `Deformation.Examples.finiteDimensional_spaceDerivations` (Stacks 0D0Z and
0D0T).

## Main results

* `Deformation.Examples.spaceInfinitesimalAutomorphisms_finiteDimensional`: **Stacks 0E42**, the
  infinitesimal automorphisms, the rescalings `ε ↦ c ε` of the dual numbers being
  `Deformation.Examples.IsDualNumberScaling`.

## References

* [Stacks Project, Tag 0E42](https://stacks.math.columbia.edu/tag/0E42)
* [Stacks Project, Tag 0E41](https://stacks.math.columbia.edu/tag/0E41)
* [Stacks Project, Tag 06JV](https://stacks.math.columbia.edu/tag/06JV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace Deformation.Examples

variable {Λ : Type u} {k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable (B : BigFppfSite.{u}) (hΛ : B.Contains (Spec (.of Λ)))
variable (hSpec : ∀ A : ArtinianLocalAlgCat.{u, u, u} Λ k, B.Contains (Spec (.of A)))
variable (X : (BigFppfOver B (Spec (.of Λ)) hΛ)ᵒᵖ ⥤ Type u)
  (hX : IsAlgebraicSpace B (Spec (.of Λ)) hΛ X)
  (toK : X ⟶ yoneda.obj (spaceBaseOver B hΛ hSpec (residueFieldBase Λ k)))

/-- Along an equivalence `e : α ≃ β` to a module, with the transported structures on `α`,
`c • a = b` exactly when `c • e a = e b`. -/
theorem smul_eq_iff_smul_equiv_eq {α β R : Type*} [Semiring R] [AddCommGroup β] [Module R β]
    (e : α ≃ β) (c : R) (a b : α) :
    letI := e.addCommGroup
    letI := e.addEquiv.module R
    c • a = b ↔ c • e a = e b := by
  let := e.addCommGroup
  let := e.addEquiv.module R
  change e.symm (c • e a) = b ↔ _
  exact ⟨fun h => by rw [← h, e.apply_symm_apply], fun h => by rw [h, e.symm_apply_apply]⟩

/-- An endomorphism `s` of an object `Aε` of `𝒞_Λ` is **the rescaling `ε ↦ c ε`** of a dual-number
coordinate: there is an isomorphism `Aε ≅ k[ε]` over `Λ`, compatible with the residue field, in
which `s` is the identity on `k` and sends `ε` to `c ε`. -/
def IsDualNumberScaling {Aε : ArtinianLocalAlgCat.{u, u, u} Λ k} (c : k) (s : Aε ⟶ Aε) : Prop :=
  ∃ φ : Aε ≃ₐ[Λ] DualNumber k,
    (∀ t : Aε, (φ t).1 = Aε.residueEquiv (IsLocalRing.residue Aε t)) ∧
    (∀ t : k, φ (s.hom (φ.symm (TrivSqZeroExt.inl t))) = TrivSqZeroExt.inl t) ∧
    φ (s.hom (φ.symm DualNumber.eps)) = c • DualNumber.eps

/-- **Stacks 0E42, the infinitesimal automorphisms.**  In Example 0E3Z, let `X` be an algebraic
space over the field `k` which is proper over `k`.  Then `Inf(𝓓_X)` is a finite-dimensional
`k`-vector space: at every point `x₀` of `𝓓_X` over `k` and every pushforward `i : x₀ ⟶ xε` of it
along a dual-number pair `k → Aε → k`, the infinitesimal automorphism group of Stacks 06JS carries
a `k`-vector-space structure

* whose addition is composition of infinitesimal automorphisms, and
* in which a scalar `c` acts by pushforward along `ε ↦ c ε`: for every endomorphism `s` of `Aε`
  which is `ε ↦ c ε` in a dual-number coordinate of `Aε` (and the identity on the residue field)
  and every arrow `j : xε ⟶ xε` over `s` fixing `i`, `c • a` is the pushforward of `a` along `j`,

and this vector space is finite dimensional.  The predeformation-category structure of `𝓓_X` is
that of Stacks 0E40 (`Deformation.Examples.isDeformationCategory_spaceDeformationProjection`). -/
@[stacks 0E42 "infinitesimal automorphisms: for an algebraic space X proper over the field k, \
Inf(Def_X), with the vector space structure of 06JV (addition is composition; c acts by \
pushforward along eps -> c eps), is finite dimensional over k, at every point x0 over k and every \
pushforward x0 -> x_eps along a dual-number pair"]
theorem spaceInfinitesimalAutomorphisms_finiteDimensional
    (hproper : Space.IsProper B (Spec (.of Λ)) hΛ toK)
    {Aε : ArtinianLocalAlgCat.{u, u, u} Λ k}
    {x₀ : (spaceDeformationProjection B hΛ hSpec X hX toK).Fiber
      (residueFieldObject.{u, u, u} Λ k)}
    {xε : (spaceDeformationProjection B hΛ hSpec X hX toK).Fiber Aε}
    (g : residueFieldObject.{u, u, u} Λ k ⟶ Aε) (e : Aε ⟶ residueFieldObject.{u, u, u} Λ k)
    (hpair : IsCanonicalDualNumberPair g e) (i : x₀.1 ⟶ xε.1)
    (hi : (spaceDeformationProjection B hΛ hSpec X hX toK).IsHomLift g i) :
    ∃ hA : AddCommGroup (infinitesimalAutomorphismGroup
        (isDeformationCategory_spaceDeformationProjection B hΛ hSpec X hX toK).predeformation g e
        hpair i hi),
      letI := hA
      ∃ hM : Module k (infinitesimalAutomorphismGroup
        (isDeformationCategory_spaceDeformationProjection B hΛ hSpec X hX toK).predeformation g e
        hpair i hi),
        letI := hM
        (∀ a b : (infinitesimalAutomorphismGroup
        (isDeformationCategory_spaceDeformationProjection B hΛ hSpec X hX toK).predeformation g e
        hpair i hi), a + b = a * b) ∧
        (∀ (c : k) (s : Aε ⟶ Aε),
            IsDualNumberScaling c s →
            s ≫ e = e →
            ∀ (j : xε.1 ⟶ xε.1)
                (hj : (spaceDeformationProjection B hΛ hSpec X hX toK).IsHomLift s j),
              i ≫ j = i → ∀ a : (infinitesimalAutomorphismGroup
        (isDeformationCategory_spaceDeformationProjection B hΛ hSpec X hX toK).predeformation g e
        hpair i hi),
                ∃ b : (infinitesimalAutomorphismGroup
        (isDeformationCategory_spaceDeformationProjection B hΛ hSpec X hX toK).predeformation g e
        hpair i hi),
                  b.val = pushforwardAutomorphismHom
                    (isDeformationCategory_spaceDeformationProjection B hΛ hSpec X hX
                      toK).predeformation.cofibered s j hj a.val ∧ c • a = b) ∧
        FiniteDimensional k (infinitesimalAutomorphismGroup
        (isDeformationCategory_spaceDeformationProjection B hΛ hSpec X hX toK).predeformation g e
        hpair i hi) := by
  let hp := (isDeformationCategory_spaceDeformationProjection B hΛ hSpec X hX toK).predeformation
  let : Module k (SpaceDerivations B hΛ (spaceStructureMap B hΛ hSpec X hX toK)) :=
    Space.derivationModuleOfRingHom B (Spec (.of Λ)) hΛ (X := spaceOf B hΛ X hX)
      (spaceResidueFieldRingHom B hΛ hSpec X hX toK)
      (spaceStructureMap B hΛ hSpec X hX toK) (spaceStructureModule B hΛ (spaceOf B hΛ X hX))
  have hDer := finiteDimensional_spaceDerivations B hΛ hSpec X hX toK hproper
  -- carry the vector space `Der_k(𝒪_X, 𝒪_X)` to `Inf(𝓓_X)` along the first identification of
  -- the first display of Stacks 0E41
  let Φ := spaceInfinitesimalAutomorphismGroupMulEquivDerivations B hΛ hSpec X hX toK hpair i hp hi
  let eD : infinitesimalAutomorphismGroup hp g e hpair i hi ≃
      SpaceDerivations B hΛ (spaceStructureMap B hΛ hSpec X hX toK) :=
    Φ.toEquiv.trans Multiplicative.toAdd
  let hA : AddCommGroup (infinitesimalAutomorphismGroup hp g e hpair i hi) := eD.addCommGroup
  let hM : Module k (infinitesimalAutomorphismGroup hp g e hpair i hi) := eD.addEquiv.module k
  refine ⟨hA, hM, fun a b => ?_, fun c s hs _ j hj hj0 a => ?_, ?_⟩
  · have h : eD (a * b) = eD a + eD b := by
      change Multiplicative.toAdd (Φ (a * b)) =
        Multiplicative.toAdd (Φ a) + Multiplicative.toAdd (Φ b)
      rw [map_mul]
      rfl
    rw [Equiv.add_def, ← h, Equiv.symm_apply_apply]
  · obtain ⟨b, hb, hΦ⟩ := spaceInfinitesimalAutomorphismGroupMulEquivDerivations_pushforward B hΛ
      hSpec X hX toK hpair i hp hi c s hs j hj hj0 a
    exact ⟨b, hb, (smul_eq_iff_smul_equiv_eq eD c a b).2 hΦ.symm⟩
  · exact Module.Finite.equiv (eD.addEquiv.linearEquiv k).symm

end Deformation.Examples

end
