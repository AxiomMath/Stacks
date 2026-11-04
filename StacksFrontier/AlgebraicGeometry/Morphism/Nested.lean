module

public import StacksFrontier.AlgebraicGeometry.ProjMapComposition.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProjMapDomain.Open

/-!
# The nested compatibility square of Tag 07ZG's morphism

Tag 07ZG attaches to a homomorphism `ψ` of quasi-coherent graded `𝒪_S`-algebras an open
`U(ψ)` of the relative projective spectrum of the target and a morphism
`r_ψ : U(ψ) ⟶ Proj_S(A)` over `S`. The open is defined as
`SheafGradedAlgebraHom.relativeMapDomain`; this file proves the
single compatibility the morphism is glued from, which the docstring of
`SheafGradedAlgebraHom.relativeMapDomain` records as the next missing declaration:

for a nested pair `U ⊆ V` of affine opens of the base, the square

```
U(ψ_U) ─────────────→ U(ψ_V)
  │                     │
  │ r_{ψ_U}             │ r_{ψ_V}
  ↓                     ↓
Proj Γ(U, A) ───────→ Proj Γ(V, A)
```

commutes, where the top arrow is the transition morphism of Tag 01NO for the target algebra
restricted to the chart domains and the bottom arrow is the transition morphism of Tag 01NO for
the source algebra.

## Main definitions

* `Stacks.AlgebraicGeometry.Tag07ZGMorphism.chartDomainTrans`: the top arrow, the restriction of
  the transition morphism of the target to the chart domains. It is well defined because the
  inverse image of the chart domain over `V` is the chart domain over `U`
  (`SheafGradedAlgebraHom.projInclusionMap_preimage_chartDomain`).

## Main results

* `Stacks.AlgebraicGeometry.Tag07ZGMorphism.mapHom_comp'`: **the composition law of Tag 01MZ in
  factorized form.** For composable graded ring homomorphisms, the morphism induced by the
  composite is any factorization of the outer morphism through the inner domain of definition,
  followed by the inner morphism. This restates
  `Stacks.AlgebraicGeometry.ProjTwistChain.mapHom_comp`, whose statement carries the canonical
  identification of the two descriptions of the domain as a composite of a
  `AlgebraicGeometry.Scheme.Hom.isoImage` and a `AlgebraicGeometry.Scheme.isoOfEq`, in a form
  where the caller supplies its own morphism and one equation about it.
* `Stacks.AlgebraicGeometry.Tag07ZGMorphism.chartDomainTrans_comp_mapHom`: **the nested
  compatibility square.**

## The route

Both arrows of the square are the morphism induced by the single graded ring homomorphism
`Γ(V, A) ⟶ Γ(U, B)`, written the two ways that
`SheafGradedAlgebraHom.res_comp_sectionHom` equates — the same
observation that makes the surjective case work in
`Stacks.AlgebraicGeometry.ProjBundleSurjection.chartMap_comp_projInclusionMap`. The difference is
that there both factorizations are everywhere defined, so the composition law needed is the one
for `Stacks.AlgebraicGeometry.RelativeProj.mapHomOfTop`; here the source side is everywhere
defined and the target side is not, so the law needed is Tag 01MZ's, on domains of definition.

The domain of definition of that single homomorphism is `U(ψ_U)`:
`Stacks.AlgebraicGeometry.Tag07ZGMorphism.mapDomain_sectionHom_comp_res`. Read through the
factorization `res_A` then `ψ_U` it is `U(ψ_U)` because restriction along an inclusion of affine
opens is everywhere defined (Tag 01NO); read through the factorization `ψ_V` then `res_B` it is
the inverse image of `U(ψ_V)` under the transition. Those are the two sides of the square.

## Implementation notes

Everything here is stated at the `Stacks.AlgebraicGeometry.ProjShared.mapDomain` spelling rather
than at `SheafGradedAlgebraHom.chartDomain`, which is a `def` for
it. The two are definitionally equal and that is not enough: a goal mixing them is not type-correct
at implicit transparency, and `rw [Category.assoc]` then fails on a composite that is visibly
present, reporting that it did not find the pattern (a `def`-versus-`abbrev`
mismatch). `Stacks.AlgebraicGeometry.Tag07ZGMorphism.chartDomain_eq` converts, by `rfl`.

`Stacks.AlgebraicGeometry.ProjTwistChain.mapHom_comp` is stated with the canonical identification
of the two descriptions of the domain of the composite. Using it directly means carrying an
`isoImage` and an `isoOfEq` through every step; `mapHom_comp'` discharges that bookkeeping once,
against an arbitrary factorizing morphism, and both applications below then supply a morphism built
from the data at hand. The hypothesis of `mapHom_comp'` determines the morphism uniquely, because
the inclusion of an open subscheme is a monomorphism.

The two graded ring homomorphisms `res_B ∘ ψ_V` and `ψ_U ∘ res_A` are equal but not syntactically
equal, and the equality cannot be rewritten in a statement that mentions the proof
`mapDomain … = U(ψ_U)`: that proof occurs inside an `AlgebraicGeometry.Scheme.isoOfEq`, so the
motive is not type-correct. The transport is therefore done by
`Stacks.AlgebraicGeometry.Tag07ZGMorphism.isoOfEq_comp_eq_mapHom_congr`, which substitutes the
equality of homomorphisms and then relies on definitional proof irrelevance for the two proofs
about the domains.

## References

* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
* [Stacks Project, Tag 01MZ](https://stacks.math.columbia.edu/tag/01MZ)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)

## Scope

Nothing here is tagged: this file supplies the glueing datum, and the assertions of Tag 07ZG it
serves are claimed where they are stated — assertion (1) in
`StacksFrontier/AlgebraicGeometry/RelativeProjMapDomain/Open.lean` and assertion (2) in
`StacksFrontier/AlgebraicGeometry/Morphism/Glue.lean`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.AlgebraicGeometry.ProjShared
open Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.ProjTwistCompare
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjMapDomain

namespace Stacks.AlgebraicGeometry.Tag07ZGMorphism

universe u w w' w''

/-! ### The composition law of Tag 01MZ, in factorized form -/

section Composition

variable {A B C : Type u} {σ : Type w} {τ : Type w'} {υ : Type w''}
  [CommRing A] [CommRing B] [CommRing C]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  [SetLike υ C] [AddSubgroupClass υ C]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) (𝒞 : ℕ → υ) [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞]

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- The canonical identification of the two descriptions of the domain of definition of a
composite, followed by the inclusion of the inverse image, is the inclusion of one domain of
definition in the other. -/
public theorem mapDomainCompIso_inv_ι (φ : 𝒜 →+*ᵍ ℬ) (ψ : ℬ →+*ᵍ 𝒞) :
    ((mapDomain ℬ 𝒞 ψ).ι.isoImage (mapHom ℬ 𝒞 ψ ⁻¹ᵁ mapDomain 𝒜 ℬ φ) ≪≫
          (AlgebraicGeometry.Proj 𝒞).isoOfEq (mapDomain_comp 𝒜 ℬ 𝒞 φ ψ).symm).inv ≫
        (mapHom ℬ 𝒞 ψ ⁻¹ᵁ mapDomain 𝒜 ℬ φ).ι =
      (AlgebraicGeometry.Proj 𝒞).homOfLE (mapDomain_comp_le 𝒜 ℬ 𝒞 φ ψ) := by
  rw [← cancel_mono (mapDomain ℬ 𝒞 ψ).ι]
  simp only [Iso.trans_inv, Category.assoc, Scheme.Opens.isoImage_ι_inv_ι,
    Scheme.isoOfEq_inv_ι, Scheme.homOfLE_ι]

/-- **Tag 01MZ's composition law, in factorized form.** Let `q` be a morphism from the domain of
definition of the composite to the domain of definition of the inner homomorphism which, followed
by the inclusion, is the inclusion followed by the morphism of the outer homomorphism. Then the
morphism induced by the composite is `q` followed by the morphism of the inner homomorphism.

`q` is unique with that property, because the inclusion of an open subscheme is a monomorphism, so
this is an equivalent form of `Stacks.AlgebraicGeometry.ProjTwistChain.mapHom_comp` with the
canonical identification of the domains replaced by its characterizing equation. -/
public theorem mapHom_comp' (φ : 𝒜 →+*ᵍ ℬ) (ψ : ℬ →+*ᵍ 𝒞)
    (q : (mapDomain 𝒜 𝒞 (ψ.comp φ)).toScheme ⟶ (mapDomain 𝒜 ℬ φ).toScheme)
    (hq : q ≫ (mapDomain 𝒜 ℬ φ).ι =
      (AlgebraicGeometry.Proj 𝒞).homOfLE (mapDomain_comp_le 𝒜 ℬ 𝒞 φ ψ) ≫ mapHom ℬ 𝒞 ψ) :
    mapHom 𝒜 𝒞 (ψ.comp φ) = q ≫ mapHom 𝒜 ℬ φ := by
  have key := mapHom_comp 𝒜 ℬ 𝒞 φ ψ
  have hqe : q = ((mapDomain ℬ 𝒞 ψ).ι.isoImage (mapHom ℬ 𝒞 ψ ⁻¹ᵁ mapDomain 𝒜 ℬ φ) ≪≫
        (AlgebraicGeometry.Proj 𝒞).isoOfEq (mapDomain_comp 𝒜 ℬ 𝒞 φ ψ).symm).inv ≫
      (mapHom ℬ 𝒞 ψ ∣_ mapDomain 𝒜 ℬ φ) := by
    rw [← cancel_mono (mapDomain 𝒜 ℬ φ).ι, hq, Category.assoc, morphismRestrict_ι,
      ← Category.assoc, mapDomainCompIso_inv_ι 𝒜 ℬ 𝒞 φ ψ]
  rw [hqe, Category.assoc, ← key, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- Transport of a factorization statement along an equality of graded ring homomorphisms. The
equality is substituted, after which the two proofs that the domains of definition agree are
definitionally equal by proof irrelevance. -/
public theorem isoOfEq_comp_eq_mapHom_congr {f g : 𝒜 →+*ᵍ ℬ} (hfg : f = g)
    {D : (AlgebraicGeometry.Proj ℬ).Opens}
    (hf : mapDomain 𝒜 ℬ f = D) (hg : mapDomain 𝒜 ℬ g = D)
    (p : D.toScheme ⟶ AlgebraicGeometry.Proj 𝒜)
    (H : ((AlgebraicGeometry.Proj ℬ).isoOfEq hf).hom ≫ p = mapHom 𝒜 ℬ f) :
    ((AlgebraicGeometry.Proj ℬ).isoOfEq hg).hom ≫ p = mapHom 𝒜 ℬ g := by
  subst hfg
  exact H

end Composition

/-! ### The nested square -/

section Nested

variable {S : Scheme.{u}} {A B : SheafGradedAlgebra S} (ψ : SheafGradedAlgebraHom A B)
  (U V : S.Opens) (h : U ≤ V)

/-- The chart domain of Tag 07ZG is the domain of definition of the induced homomorphism of the
graded rings of sections, by definition. Stated so that the two spellings can be exchanged by a
rewrite rather than only by `exact`. -/
public theorem chartDomain_eq :
    ψ.chartDomain U = mapDomain (A.grading U) (B.grading U) (ψ.sectionHom U) :=
  rfl

/-- `SheafGradedAlgebraHom.projInclusionMap_preimage_chartDomain`
at the `mapDomain` spelling. -/
public theorem projInclusionMap_preimage_mapDomain (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    projInclusionMap B U V h hU hV ⁻¹ᵁ
        mapDomain (A.grading V) (B.grading V) (ψ.sectionHom V) =
      mapDomain (A.grading U) (B.grading U) (ψ.sectionHom U) :=
  ψ.projInclusionMap_preimage_chartDomain U V h hU hV

/-- **The domain of definition of the single graded ring homomorphism `Γ(V, A) ⟶ Γ(U, B)` is the
chart domain over `U`.** Read through the factorization by restriction followed by `ψ_U`, the
domain of the composite is the image of the inverse image of the domain of the restriction — and
restriction along an inclusion of affine opens is everywhere defined by Tag 01NO. -/
public theorem mapDomain_sectionHom_comp_res (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    mapDomain (A.grading V) (B.grading U) ((ψ.sectionHom U).comp (A.res h)) =
      mapDomain (A.grading U) (B.grading U) (ψ.sectionHom U) := by
  rw [mapDomain_comp (A.grading V) (A.grading U) (B.grading U) (A.res h) (ψ.sectionHom U),
    projInclusionDomain_eq_top A U V h hU hV, Scheme.Hom.preimage_top,
    Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]

/-- The same statement for the other factorization, through `ψ_V` followed by restriction. -/
public theorem mapDomain_res_comp_sectionHom (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    mapDomain (A.grading V) (B.grading U) ((B.res h).comp (ψ.sectionHom V)) =
      mapDomain (A.grading U) (B.grading U) (ψ.sectionHom U) := by
  rw [ψ.res_comp_sectionHom h]
  exact mapDomain_sectionHom_comp_res ψ U V h hU hV

/-- **The transition morphism on the chart domains.** The transition morphism of Tag 01NO for the
target algebra carries the chart domain over `U` into the chart domain over `V`, because the
inverse image of the latter is exactly the former. -/
public def chartDomainTrans (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    (mapDomain (A.grading U) (B.grading U) (ψ.sectionHom U)).toScheme ⟶
      (mapDomain (A.grading V) (B.grading V) (ψ.sectionHom V)).toScheme :=
  ((AlgebraicGeometry.Proj (B.grading U)).isoOfEq
      (projInclusionMap_preimage_mapDomain ψ U V h hU hV).symm).hom ≫
    (projInclusionMap B U V h hU hV ∣_
      mapDomain (A.grading V) (B.grading V) (ψ.sectionHom V))

/-- The transition morphism on the chart domains is the transition morphism of Tag 01NO. -/
@[reassoc]
public theorem chartDomainTrans_ι (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    chartDomainTrans ψ U V h hU hV ≫
        (mapDomain (A.grading V) (B.grading V) (ψ.sectionHom V)).ι =
      (mapDomain (A.grading U) (B.grading U) (ψ.sectionHom U)).ι ≫
        projInclusionMap B U V h hU hV := by
  rw [chartDomainTrans, Category.assoc, morphismRestrict_ι, ← Category.assoc,
    Scheme.isoOfEq_hom_ι]

/-- The morphism of projective spectra of the single homomorphism `Γ(V, A) ⟶ Γ(U, B)`, read
through the factorization by restriction followed by `ψ_U`: it is `r_{ψ_U}` followed by the
transition morphism of the source algebra. -/
public theorem isoOfEq_comp_mapHom_comp_projInclusionMap
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    ((AlgebraicGeometry.Proj (B.grading U)).isoOfEq
        (mapDomain_sectionHom_comp_res ψ U V h hU hV)).hom ≫
      (mapHom (A.grading U) (B.grading U) (ψ.sectionHom U) ≫
        projInclusionMap A U V h hU hV) =
      mapHom (A.grading V) (B.grading U) ((ψ.sectionHom U).comp (A.res h)) := by
  have hq : (((AlgebraicGeometry.Proj (B.grading U)).isoOfEq
          (mapDomain_sectionHom_comp_res ψ U V h hU hV)).hom ≫
        mapHom (A.grading U) (B.grading U) (ψ.sectionHom U) ≫
          projInclusionTopSection A U V h hU hV) ≫
        (mapDomain (A.grading V) (A.grading U) (A.res h)).ι =
      (AlgebraicGeometry.Proj (B.grading U)).homOfLE
          (mapDomain_comp_le (A.grading V) (A.grading U) (B.grading U)
            (A.res h) (ψ.sectionHom U)) ≫
        mapHom (A.grading U) (B.grading U) (ψ.sectionHom U) := by
    rw [Category.assoc, Category.assoc, projInclusionTopSection_ι, Category.comp_id]
    -- the comparison of the two inclusions of `U(ψ_U)` in itself is definitional
    congr 1
  rw [mapHom_comp' (A.grading V) (A.grading U) (B.grading U) (A.res h) (ψ.sectionHom U) _ hq,
    Category.assoc, Category.assoc, ← projInclusionMap_eq_comp A U V h hU hV, projMapData_hom]

/-- The same morphism read through the other factorization, by `ψ_V` followed by restriction: it
is the transition on the chart domains followed by `r_{ψ_V}`. -/
public theorem isoOfEq_comp_chartDomainTrans_comp_mapHom
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    ((AlgebraicGeometry.Proj (B.grading U)).isoOfEq
        (mapDomain_res_comp_sectionHom ψ U V h hU hV)).hom ≫
      (chartDomainTrans ψ U V h hU hV ≫
        mapHom (A.grading V) (B.grading V) (ψ.sectionHom V)) =
      mapHom (A.grading V) (B.grading U) ((B.res h).comp (ψ.sectionHom V)) := by
  have hq : (((AlgebraicGeometry.Proj (B.grading U)).isoOfEq
          (mapDomain_res_comp_sectionHom ψ U V h hU hV)).hom ≫
        chartDomainTrans ψ U V h hU hV) ≫
        (mapDomain (A.grading V) (B.grading V) (ψ.sectionHom V)).ι =
      (AlgebraicGeometry.Proj (B.grading U)).homOfLE
          (mapDomain_comp_le (A.grading V) (B.grading V) (B.grading U)
            (ψ.sectionHom V) (B.res h)) ≫
        mapHom (B.grading V) (B.grading U) (B.res h) := by
    rw [Category.assoc, chartDomainTrans_ι, ← Category.assoc, Scheme.isoOfEq_hom_ι,
      ← projInclusionMap_eq_comp B U V h hU hV, projMapData_hom, ← Category.assoc]
    congr 1
    rw [← cancel_mono (mapDomain (B.grading V) (B.grading U) (B.res h)).ι, Category.assoc,
      projInclusionTopSection_ι, Category.comp_id, Scheme.homOfLE_ι]
  rw [mapHom_comp' (A.grading V) (B.grading V) (B.grading U) (ψ.sectionHom V) (B.res h) _ hq,
    Category.assoc]

/-- **The nested compatibility square of Tag 07ZG.** For a nested pair `U ⊆ V` of affine opens of
the base, the transition morphism on the chart domains followed by the morphism induced over `V`
is the morphism induced over `U` followed by the transition morphism of the source algebra.

Both sides are the morphism of projective spectra of the single graded ring homomorphism
`Γ(V, A) ⟶ Γ(U, B)`, read through the two factorizations that
`SheafGradedAlgebraHom.res_comp_sectionHom` equates. -/
@[reassoc]
public theorem chartDomainTrans_comp_mapHom (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    chartDomainTrans ψ U V h hU hV ≫
        mapHom (A.grading V) (B.grading V) (ψ.sectionHom V) =
      mapHom (A.grading U) (B.grading U) (ψ.sectionHom U) ≫
        projInclusionMap A U V h hU hV := by
  have key := isoOfEq_comp_eq_mapHom_congr (A.grading V) (B.grading U)
    (ψ.res_comp_sectionHom h) (mapDomain_res_comp_sectionHom ψ U V h hU hV)
    (mapDomain_sectionHom_comp_res ψ U V h hU hV) _
    (isoOfEq_comp_chartDomainTrans_comp_mapHom ψ U V h hU hV)
  rw [← isoOfEq_comp_mapHom_comp_projInclusionMap ψ U V h hU hV] at key
  exact (cancel_epi _).mp key

end Nested

end Stacks.AlgebraicGeometry.Tag07ZGMorphism

end
