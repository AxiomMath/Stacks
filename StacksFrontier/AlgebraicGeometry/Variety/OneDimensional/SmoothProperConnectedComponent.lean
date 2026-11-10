module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GeomConnectedFibres.Basic
public import StacksFrontier.AlgebraicGeometry.HQuasiProjectiveDimensionOne.Basic
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.EtaleLocalStructure
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.CancelEtale
public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.ConnectedLocal
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.HProjective
public import StacksFrontier.RingTheory.Smooth.GeometricallyReducedFibres

/-!
# A connected smooth proper curve is a curve over its field of global functions

Let `k` be a field and let `Z` be a connected scheme, smooth and proper over `k`, with
`dim(Z) ≤ 1`. Put `k_Z = Γ(Z, 𝒪_Z)`. Then `k_Z` is a finite separable extension of `k`, and the
canonical morphism `Z ⟶ Spec k_Z` is smooth, H-projective and geometrically irreducible, with
`dim(Z) ≤ 1`.

This is clauses (4) and (5) of [Stacks, Tag 0GK5] at a single component: in the source the
normalization decomposes as `Y₁ ⨿ … ⨿ Yₙ`, each `Yᵢ` sitting as a dense open in a compactification
`Ȳᵢ` which is smooth, projective and geometrically irreducible over `k'ᵢ = Γ(Ȳᵢ, 𝒪)`, and `Ȳᵢ` is
exactly a `Z` as above. See the implementation notes for what the tag still needs.

## Main results

* `AlgebraicGeometry.exists_isSeparable_smooth_isProjectiveMorphism_geometricallyIrreducible`:
  the field `k_Z`, the morphism `Z ⟶ Spec k_Z` and its four properties.

## Implementation notes

**What this gives of [Stacks, Tag 0GK5], and what it does not.** The tag asks for a diagram over
an arbitrary separated finite-type `X` of dimension at most one: a finite purely inseparable
`k'/k` (clause 1), the normalization `ν` of `X_{k'}` (clause 2), an open immersion `j` with dense
image into a disjoint union of compactifications (clause 3), finite separable `k'ᵢ/k'` (clause 4),
and the compactified pieces smooth, projective and geometrically irreducible of dimension at most
one over `k'ᵢ` (clause 5). Clauses (1) and (2) are
`AlgebraicGeometry.exists_isPurelyInseparable_smooth_normalization`. This file is clauses (4) and
(5) for one compactified piece: given such a piece -- a connected scheme smooth and proper over a
field with dimension at most one -- it produces its base field and all four properties the source
asserts of it. What is *not* done here is the assembly: decomposing the normalization of the
compactification of `X` into its components and transporting the result back along the open
immersion of clause (3).

**The route.** `k_Z = Γ(Z, 𝒪_Z)` is a field because `Z` is connected, reduced and proper
(`isField_globalSections_of_connectedSpace_of_isReduced`, [Stacks, Tag 0BUG] clauses (2) and
(3)), and separable over `k` because `Z` is geometrically
reduced, being smooth ([Stacks, Tag 0BUG] clause (4)). The structure morphism factors as
`Z ⟶ Spec k_Z ⟶ Spec k` and the second map is etale, `k_Z/k` being finite separable; so
`Z ⟶ Spec k_Z` is smooth by cancelling the etale map off a smooth composite
([Stacks, Tag 0G80], `AlgebraicGeometry.Smooth.of_comp_of_etale`). It is proper because `Z` is
proper over `k` and `Spec k_Z` is affine
(`Stacks.AlgebraicGeometry.ProperGeomConnected.isProper_toSpecΓ`), hence H-projective: a reduced
separated finite-type scheme of dimension at most one over a field is H-quasi-projective
([Stacks, Tag 0A25], unconditionally in the reduced case), and H-quasi-projective plus proper is
H-projective ([Stacks, Tag 0BCL]). It is geometrically connected by [Stacks, Tag 0FD1], and
geometrically connected plus smooth is geometrically irreducible, a connected normal Noetherian
scheme being irreducible.

Separatedness of `Z` over `k` is not assumed: properness supplies it.

## References

* [Stacks Project, Tag 0GK5](https://stacks.math.columbia.edu/tag/0GK5)
* [Stacks Project, Tag 0BUG](https://stacks.math.columbia.edu/tag/0BUG)
* [Stacks Project, Tag 0FD1](https://stacks.math.columbia.edu/tag/0FD1)
* [Stacks Project, Tag 0A25](https://stacks.math.columbia.edu/tag/0A25)
* [Stacks Project, Tag 0BCL](https://stacks.math.columbia.edu/tag/0BCL)
* [Stacks Project, Tag 0G80](https://stacks.math.columbia.edu/tag/0G80)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ProperGeomConnected
open Stacks.AlgebraicGeometry.ProperSectionsGeom
open Stacks.HQuasiProjectiveDimensionOne

universe u

namespace AlgebraicGeometry

/-- **[Stacks, Tag 0GK5], clauses (4) and (5) at one component.** Let `Z` be a connected scheme,
smooth and proper over a field `k`, of dimension at most one. Then there is a finite separable
extension `K/k` and a morphism `r : Z ⟶ Spec K` over `k` which is smooth, H-projective and
geometrically irreducible, with `dim(Z) ≤ 1`.

The field is `K = Γ(Z, 𝒪_Z)` and the morphism is the canonical `Z ⟶ Spec Γ(Z, 𝒪_Z)`, exactly as
in the source. -/
@[stacks 0GK5 "clauses (4) and (5), at one component: for a CONNECTED scheme Z smooth and proper \
over a field k with dim Z <= 1 -- that is, for one of the compactified pieces Ybar_i of the \
diagram -- the field k'_i = Gamma(Z, O_Z) of clause (4) is a finite SEPARABLE extension of k, \
and Z is SMOOTH, PROJECTIVE and GEOMETRICALLY IRREDUCIBLE of dimension at most one over it, \
which is clause (5). The assembly of the diagram -- decomposing the normalization into its \
components and transporting along the open immersion j of clause (3) -- is not done here; \
clauses (1) and (2) are carried by \
AlgebraicGeometry.exists_isPurelyInseparable_smooth_normalization."]
public theorem exists_isSeparable_smooth_isProjectiveMorphism_geometricallyIrreducible
    (k : Type u) [Field k] {Z : Scheme.{u}} (q : Z ⟶ Spec (.of k))
    [IsProper q] [Smooth q] [ConnectedSpace Z]
    (hdim : topologicalKrullDim (Z : Type u) ≤ 1) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K) (_ : Module.Finite k K)
      (_ : Algebra.IsSeparable k K) (r : Z ⟶ Spec (.of K)),
      r ≫ Spec.map (CommRingCat.ofHom (algebraMap k K)) = q ∧
        Smooth r ∧ IsProjectiveMorphism r ∧ GeometricallyIrreducible r ∧
        topologicalKrullDim (Z : Type u) ≤ 1 := by
  let alg : Algebra k Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ q.appTop).hom.toAlgebra
  -- `Z` is geometrically reduced, hence reduced, because it is smooth over `k`.
  have hgred : GeometricallyReduced q := geometricallyReduced_of_smooth q
  have hZred : AlgebraicGeometry.IsReduced Z := self_of_isIntegral_of_geometrically
    (P := AlgebraicGeometry.IsReduced) hgred.geometrically_isReduced
  -- Clause (4): `Γ(Z, ⊤)` is a finite separable extension of `k`.
  let fieldK : Field Γ(Z, ⊤) :=
    (isField_globalSections_of_connectedSpace_of_isReduced k q).toField
  have hfin : Module.Finite k Γ(Z, ⊤) := moduleFinite_globalSections_of_isProper k q
  have hsep : Algebra.IsSeparable k Γ(Z, ⊤) :=
    isSeparable_globalSections_of_connectedSpace_of_geometricallyReduced k q
  -- The structure morphism factors through `Spec Γ(Z, ⊤)`.
  have hfac : Z.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap k Γ(Z, ⊤))) = q := by
    change Z.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫ q.appTop) = q
    rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
      toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  -- The second factor is etale, `Γ(Z, ⊤)` being a finite separable extension of `k`.
  obtain ⟨hetaleAlg, -⟩ := etale_globalSections_of_geometricallyReduced k q
  have hetale : Etale (Spec.map (CommRingCat.ofHom (algebraMap k Γ(Z, ⊤)))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr hetaleAlg)
  -- Clause (5), smoothness: cancel the etale factor off the smooth composite.
  have hsmcomp : Smooth (Z.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap k Γ(Z, ⊤)))) := by
    rw [hfac]
    infer_instance
  have hsm : Smooth Z.toSpecΓ :=
    @Smooth.of_comp_of_etale _ _ _ Z.toSpecΓ _ hsmcomp hetale
  -- Clause (5), properness and hence H-projectivity.
  have hproper : IsProper Z.toSpecΓ := isProper_toSpecΓ q
  have hproj : IsProjectiveMorphism Z.toSpecΓ :=
    isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mpr
      ⟨isHQuasiProjective_of_topologicalKrullDim_le_one Z.toSpecΓ hdim, hproper⟩
  -- Clause (5), geometric irreducibility: geometrically connected fibres plus smoothness.
  have hgc : GeometricallyConnected Z.toSpecΓ :=
    geometricallyConnected_toSpecΓ_of_isProper_over_field k Z q
  have hgi : GeometricallyIrreducible Z.toSpecΓ :=
    @geometricallyIrreducible_of_geometricallyConnected_of_smooth _ _ Z.toSpecΓ hsm
      inferInstance inferInstance hgc
  exact ⟨Γ(Z, ⊤), fieldK, alg, hfin, hsep, Z.toSpecΓ, hfac, hsm, hproj, hgi, hdim⟩

end AlgebraicGeometry

end
