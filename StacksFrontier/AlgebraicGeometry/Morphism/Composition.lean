module

public import StacksFrontier.AlgebraicGeometry.Morphism.Glue
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Composition of the morphisms of relative Proj

Let `φ : A ⟶ B` and `ψ : B ⟶ C` be homomorphisms of quasi-coherent graded `𝒪_S`-algebras, and
write `X`, `Y`, `Z` for the relative projective spectra of `A`, `B` and `C`. Tag 07ZG attaches to
each homomorphism an open of the relative Proj of its target and a morphism out of that open; this
file compares the data of the composite with the data of the two factors.

The open `U(ψ ∘ φ) ⊆ Z` is the inverse image of `U(φ) ⊆ Y` under `r_ψ : U(ψ) ⟶ Y`, and the
morphism `r_{ψ ∘ φ}` is the restriction of `r_ψ` followed by `r_φ`.

## A correction to the source, stated explicitly

**Tag 07ZH's first assertion is type-incorrect as printed, and this file proves the intended
reading rather than the printed one.** The source prints

`U(ψ ∘ φ) = r_φ^{-1}(U(ψ))`,

which does not parse: `r_φ : U(φ) ⟶ X` is defined on the open `U(φ) ⊆ Y = Proj_S(B)`, so its
inverse image accepts an open of `X = Proj_S(A)`, whereas `U(ψ) ⊆ Z = Proj_S(C)`. The two names
are interchanged. The intended — and provable — statement is

`U(ψ ∘ φ) = r_ψ^{-1}(U(φ))`,

an equality of opens of `Z`: `r_ψ : U(ψ) ⟶ Y` does accept the open `U(φ) ⊆ Y`. That is what
`Stacks.AlgebraicGeometry.RelativeProjMapComp.relativeMapDomain_comp` states and proves, with the
inverse image carried over to an open of `Z` by the inclusion of `U(ψ)`; its `stacks` clause
string records the same correction. Nothing is weakened by the substitution — the printed form has
no content to weaken — but it is a deviation from the source and is disclosed here rather than
absorbed silently, so that a reader comparing the two can see which statement was formalized.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjMapDomain.SheafGradedAlgebraHom.comp`: the composite of
  two homomorphisms of graded `𝒪_S`-algebras.

## Main results

* `RelativeProjMapDomain.SheafGradedAlgebraHom.sectionHom_comp`: the homomorphism a composite
  induces on the graded rings of sections over an open is the composite of the two induced
  homomorphisms.
* `Stacks.AlgebraicGeometry.RelativeProjMapComp.relativeMapDomain_comp`: **the first assertion of
  Tag 07ZH**, `U(ψ ∘ φ) = r_ψ^{-1}(U(φ))`, with the inverse image carried over to an open of `Z`
  by the inclusion of `U(ψ)`.
* `Stacks.AlgebraicGeometry.RelativeProjMapComp.relativeMapDomainCompIso_hom_ι`: the canonical
  identification of the two descriptions of that open is compatible with their inclusions into
  the relative Proj of `C`.
* `Stacks.AlgebraicGeometry.RelativeProjMapComp.relativeMapHom_comp'` and
  `relativeMapHom_comp`: **the second assertion of Tag 07ZH**, `r_{ψ ∘ φ} = r_φ ∘ r_ψ|_{U(ψ∘φ)}`,
  in a factorized form and in the form that names the canonical identification of the domains.

## The route

Both assertions are affine-local over the base, where they are the corresponding assertions of
Tag 01MZ for the induced homomorphisms of graded rings of sections. The one obstacle is that the
homomorphism a composite induces on sections over an open is only *propositionally* equal to the
composite of the two induced homomorphisms, so the absolute statements have to be transported
along that equality — and a rewrite is impossible, because the domain of definition occurs inside
the proof that an open subscheme inclusion is an inclusion. Each absolute input is therefore
restated for a homomorphism which is a variable, equal to a composite by hypothesis
(`mapDomain_comp_le_of_eq`, `mapHom_preimage_mapDomain_of_eq`, `mapHom_comp_of_eq`), so that the
transport is a substitution.

The first assertion is proved at a point, by reading the point through the chart over an affine
open of the base containing its image: there the morphism of Tag 07ZG is the absolute morphism of
Tag 01MY, by `Stacks.AlgebraicGeometry.Tag07ZGMorphism.chart_comp_relativeMapHom`.

The second is proved from the affine-local uniqueness
`Stacks.AlgebraicGeometry.Tag07ZGMorphism.relativeMapHom_unique`: on the chart over an affine open
of the base, the composite being tested factors as the absolute composite by the factorized form
of Tag 01MZ, and the remaining identity is an equality of morphisms between open subschemes of `Z`
which is checked after composing with the inclusion into `Z`.

## Implementation notes

The third assertion of Tag 07ZH, the compatibility `θ_ψ ∘ r_ψ^*θ_φ = θ_{ψ ∘ φ}` of the maps on
twists, is proved in `StacksFrontier/AlgebraicGeometry/Morphism/TwistComp.lean` as
`Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistMap_comp'` and, at the canonical morphisms,
`relativeTwistMap_comp`. It needs, besides the maps on twists themselves, the twist assertion of
Tag 01MZ for a composable pair read at legs out of one scheme
(`Stacks.AlgebraicGeometry.Tag07ZGTwist.twistMapAt_comp`), applied over the piece of `U(ψ ∘ φ)`
over an affine open of the base at the three legs the assertions above supply; the two assertions
of this file are what identify those legs.

## References

* [Stacks Project, Tag 07ZH](https://stacks.math.columbia.edu/tag/07ZH)
* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01MZ](https://stacks.math.columbia.edu/tag/01MZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.AlgebraicGeometry.ProjShared
open Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjTwistGlue
open Stacks.AlgebraicGeometry.RelativeProjMapDomain
open Stacks.AlgebraicGeometry.Tag07ZGMorphism

universe u w w' w''

namespace Stacks.AlgebraicGeometry.RelativeProjMapDomain.SheafGradedAlgebraHom

variable {S : Scheme.{u}} {A B C : SheafGradedAlgebra S}

/-- The composite of two homomorphisms of graded `𝒪_S`-algebras: the composite of the morphisms
of sheaves of modules in each degree. -/
public def comp (ψ : SheafGradedAlgebraHom B C) (φ : SheafGradedAlgebraHom A B) :
    SheafGradedAlgebraHom A C where
  app n := φ.app n ≫ ψ.app n
  app_mul i j U a b := by
    change (ψ.app (i + j)).app U ((φ.app (i + j)).app U ((A.mul i j).app U a b)) =
      (C.mul i j).app U ((ψ.app i).app U ((φ.app i).app U a))
        ((ψ.app j).app U ((φ.app j).app U b))
    rw [φ.app_mul i j U a b, ψ.app_mul i j U ((φ.app i).app U a) ((φ.app j).app U b)]
  app_one U := by
    change (ψ.app 0).app U ((φ.app 0).app U (A.one U)) = C.one U
    rw [φ.app_one U, ψ.app_one U]

/-- The degreewise maps of a composite. -/
public theorem comp_app (ψ : SheafGradedAlgebraHom B C) (φ : SheafGradedAlgebraHom A B) (n : ℤ) :
    (ψ.comp φ).app n = φ.app n ≫ ψ.app n :=
  rfl

/-- **The homomorphism of graded rings of sections induced by a composite is the composite of the
induced homomorphisms.** The two sides are not definitionally equal: one applies the universal
property of the direct sum to a composite of degreewise maps, the other composes two such
universal maps. They agree on every homogeneous summand. -/
public theorem sectionHom_comp (ψ : SheafGradedAlgebraHom B C) (φ : SheafGradedAlgebraHom A B)
    (U : S.Opens) :
    (ψ.comp φ).sectionHom U = (ψ.sectionHom U).comp (φ.sectionHom U) := by
  refine GradedRingHom.ext fun x => ?_
  rw [GradedRingHom.comp_apply]
  induction x using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | of n y =>
    rw [sectionHom_of (ψ.comp φ) U y, sectionHom_of φ U y,
      sectionHom_of ψ U (φ.sectionPieceHom U n y)]
    rfl
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

end Stacks.AlgebraicGeometry.RelativeProjMapDomain.SheafGradedAlgebraHom

namespace Stacks.AlgebraicGeometry.RelativeProjMapComp

/-! ### The assertions of Tag 01MZ, for a homomorphism equal to a composite -/

section Absolute

variable {A B C : Type u} {σ : Type w} {τ : Type w'} {υ : Type w''}
  [CommRing A] [CommRing B] [CommRing C]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  [SetLike υ C] [AddSubgroupClass υ C]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) (𝒞 : ℕ → υ) [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞]

omit [AddSubgroupClass σ A] [AddSubgroupClass τ B] [GradedRing 𝒜] [GradedRing ℬ] in
/-- The domain of definition of a homomorphism equal to a composite is contained in the domain of
definition of the outer factor. -/
public theorem mapDomain_comp_le_of_eq {f : 𝒜 →+*ᵍ 𝒞} (φ : 𝒜 →+*ᵍ ℬ) (ψ : ℬ →+*ᵍ 𝒞)
    (hf : f = ψ.comp φ) :
    mapDomain 𝒜 𝒞 f ≤ mapDomain ℬ 𝒞 ψ := by
  subst hf
  exact mapDomain_comp_le 𝒜 ℬ 𝒞 φ ψ

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- The inverse image, under the morphism of the outer factor, of the domain of definition of the
inner factor, for a homomorphism equal to the composite. -/
public theorem mapHom_preimage_mapDomain_of_eq {f : 𝒜 →+*ᵍ 𝒞} (φ : 𝒜 →+*ᵍ ℬ) (ψ : ℬ →+*ᵍ 𝒞)
    (hf : f = ψ.comp φ) :
    mapHom ℬ 𝒞 ψ ⁻¹ᵁ mapDomain 𝒜 ℬ φ =
      (mapDomain ℬ 𝒞 ψ).ι ⁻¹ᵁ mapDomain 𝒜 𝒞 f := by
  subst hf
  exact mapHom_preimage_mapDomain 𝒜 ℬ 𝒞 φ ψ

/-- **Tag 01MZ's composition law for a homomorphism equal to a composite.** There is a morphism
from the domain of definition of `f` to the domain of definition of the inner factor which,
followed by the inclusion, is the inclusion followed by the morphism of the outer factor, and `f`
induces that morphism followed by the morphism of the inner factor. -/
@[ega "II 2.8.4"]
public theorem mapHom_comp_of_eq {f : 𝒜 →+*ᵍ 𝒞} (φ : 𝒜 →+*ᵍ ℬ) (ψ : ℬ →+*ᵍ 𝒞)
    (hf : f = ψ.comp φ) (hle : mapDomain 𝒜 𝒞 f ≤ mapDomain ℬ 𝒞 ψ) :
    ∃ q : (mapDomain 𝒜 𝒞 f).toScheme ⟶ (mapDomain 𝒜 ℬ φ).toScheme,
      q ≫ (mapDomain 𝒜 ℬ φ).ι =
          (AlgebraicGeometry.Proj 𝒞).homOfLE hle ≫ mapHom ℬ 𝒞 ψ ∧
        mapHom 𝒜 𝒞 f = q ≫ mapHom 𝒜 ℬ φ := by
  subst hf
  refine ⟨((mapDomain ℬ 𝒞 ψ).ι.isoImage (mapHom ℬ 𝒞 ψ ⁻¹ᵁ mapDomain 𝒜 ℬ φ) ≪≫
      (AlgebraicGeometry.Proj 𝒞).isoOfEq (mapDomain_comp 𝒜 ℬ 𝒞 φ ψ).symm).inv ≫
      (mapHom ℬ 𝒞 ψ ∣_ mapDomain 𝒜 ℬ φ), ?_, mapHom_comp' 𝒜 ℬ 𝒞 φ ψ _ ?_⟩ <;>
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, mapDomainCompIso_inv_ι 𝒜 ℬ 𝒞 φ ψ]

end Absolute

/-! ### The open and the morphism of the composite -/

section Relative

variable {S : Scheme.{u}} {A B C : SheafGradedAlgebra S}

/-- An open of a relative projective spectrum is contained in a second one as soon as its inverse
image under every chart of the base is. The chart images cover. -/
public theorem le_of_chart_preimage_le {B : SheafGradedAlgebra S}
    {W W' : (relativeProj B).scheme.Opens}
    (h : ∀ (V : S.Opens) (hV : IsAffineOpen V),
      (relativeProj B).chart V hV ⁻¹ᵁ W ≤ (relativeProj B).chart V hV ⁻¹ᵁ W') :
    W ≤ W' := by
  intro x hx
  obtain ⟨V, hxV⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (show x ∈ ⨆ V : AffineOpen S, (relativeProj B).toBase ⁻¹ᵁ V.1 by
      rw [iSup_toBase_preimage_eq_top' B (relativeProj B)]; trivial)
  rw [← chart_image_top (relativeProj B) V.1 V.2] at hxV
  obtain ⟨y, -, hyx⟩ := hxV
  subst hyx
  exact h V.1 V.2 hx

/-- The inverse image of the open of Tag 07ZG under a chart of the base is the domain of definition
of the induced homomorphism of graded rings of sections. -/
private theorem chart_preimage_relativeMapDomain_eq_mapDomain (ξ : SheafGradedAlgebraHom A B)
    (V : S.Opens) (hV : IsAffineOpen V) :
    (relativeProj B).chart V hV ⁻¹ᵁ ξ.relativeMapDomain =
      mapDomain (A.grading V) (B.grading V) (ξ.sectionHom V) :=
  (ξ.chart_preimage_relativeMapDomain V hV).trans (chartDomain_eq ξ V)

variable (φ : SheafGradedAlgebraHom A B) (ψ : SheafGradedAlgebraHom B C)

/-- The open of Tag 07ZG attached to a composite is contained in the one attached to the outer
factor. -/
public theorem relativeMapDomain_comp_le :
    (ψ.comp φ).relativeMapDomain ≤ ψ.relativeMapDomain := by
  refine le_of_chart_preimage_le fun V hV => ?_
  rw [chart_preimage_relativeMapDomain_eq_mapDomain, chart_preimage_relativeMapDomain_eq_mapDomain]
  exact mapDomain_comp_le_of_eq (A.grading V) (B.grading V) (C.grading V) (φ.sectionHom V)
    (ψ.sectionHom V) (SheafGradedAlgebraHom.sectionHom_comp ψ φ V)

/-- **The morphism of Tag 07ZG, read at a point of a chart of the base.** A point of `U(ψ)` that
is the image of a point `x` of the chart over an affine open `V` of the base is sent to the image
under the chart of `Proj_S(A)` over `V` of the image of `x` under the absolute morphism of
Tag 01MY. -/
public theorem relativeMapHom_apply (V : S.Opens) (hV : IsAffineOpen V)
    (y : (mapDomain (B.grading V) (C.grading V) (ψ.sectionHom V)).toScheme)
    (w : ψ.relativeMapDomain.toScheme)
    (hw : (relativeProj C).chart V hV
        ((mapDomain (B.grading V) (C.grading V) (ψ.sectionHom V)).ι y) =
      ψ.relativeMapDomain.ι w) :
    relativeMapHom ψ w =
      (relativeProj B).chart V hV
        (mapHom (B.grading V) (C.grading V) (ψ.sectionHom V) y) := by
  have hι : (((relativeProj C).chart V hV).isoImage
          (mapDomain (B.grading V) (C.grading V) (ψ.sectionHom V))).hom ≫
        (relativeProj C).scheme.homOfLE (chartImage_le ψ (⟨V, hV⟩ : AffineOpen S)) ≫
          ψ.relativeMapDomain.ι =
      (mapDomain (B.grading V) (C.grading V) (ψ.sectionHom V)).ι ≫
        (relativeProj C).chart V hV := by
    rw [Scheme.homOfLE_ι, Scheme.Hom.isoImage_hom_ι]
  have hιpt := congr($hι y)
  have hkey := congr($(chart_comp_relativeMapHom ψ (⟨V, hV⟩ : AffineOpen S)) y)
  simp only [Scheme.Hom.comp_apply] at hιpt hkey
  rw [ψ.relativeMapDomain.ι.isOpenEmbedding.injective (hw.symm.trans hιpt.symm)]
  exact hkey

/-- **The inverse image of `U(φ)` under `r_ψ`.** It is the part of `U(ψ)` lying in the open
attached to the composite. This is the first assertion of Tag 07ZH, before the inverse image is
carried over to an open of the relative Proj of `C`. -/
public theorem relativeMapHom_preimage_relativeMapDomain :
    relativeMapHom ψ ⁻¹ᵁ φ.relativeMapDomain =
      ψ.relativeMapDomain.ι ⁻¹ᵁ (ψ.comp φ).relativeMapDomain := by
  refine TopologicalSpace.Opens.ext (Set.ext fun w => ?_)
  obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (show ψ.relativeMapDomain.ι w ∈ ⨆ U : AffineOpen S, chartImage ψ U from w.2)
  obtain ⟨x, hx, hxw⟩ := hU
  have hr := relativeMapHom_apply ψ U.1 U.2
    (⟨x, hx⟩ : (mapDomain (B.grading U.1) (C.grading U.1) (ψ.sectionHom U.1)).toScheme) w hxw
  have key := mapHom_preimage_mapDomain_of_eq (A.grading U.1) (B.grading U.1) (C.grading U.1)
    (φ.sectionHom U.1) (ψ.sectionHom U.1) (SheafGradedAlgebraHom.sectionHom_comp ψ φ U.1)
  have h1 : relativeMapHom ψ w ∈ φ.relativeMapDomain ↔
      (⟨x, hx⟩ : (mapDomain (B.grading U.1) (C.grading U.1) (ψ.sectionHom U.1)).toScheme) ∈
        mapHom (B.grading U.1) (C.grading U.1) (ψ.sectionHom U.1) ⁻¹ᵁ
          mapDomain (A.grading U.1) (B.grading U.1) (φ.sectionHom U.1) := by
    rw [hr, ← chart_preimage_relativeMapDomain_eq_mapDomain φ]
    exact Iff.rfl
  have h2 : ψ.relativeMapDomain.ι w ∈ (ψ.comp φ).relativeMapDomain ↔
      (⟨x, hx⟩ : (mapDomain (B.grading U.1) (C.grading U.1) (ψ.sectionHom U.1)).toScheme) ∈
        mapHom (B.grading U.1) (C.grading U.1) (ψ.sectionHom U.1) ⁻¹ᵁ
          mapDomain (A.grading U.1) (B.grading U.1) (φ.sectionHom U.1) := by
    rw [← hxw, key, ← chart_preimage_relativeMapDomain_eq_mapDomain (ψ.comp φ)]
    exact Iff.rfl
  exact h1.trans h2.symm

/-- **The first assertion of Tag 07ZH.** The open of Tag 07ZG attached to a composite is the
inverse image, under the morphism attached to the outer factor, of the open attached to the inner
factor, read as an open of the relative projective spectrum of the target of the composite.

**This is the intended reading of a source statement that is type-incorrect as printed.** Tag
07ZH prints `U(ψ ∘ φ) = r_φ^{-1}(U(ψ))`, in which `r_φ`, being defined on `U(φ) ⊆ Proj_S(B)`,
takes inverse images of opens of `Proj_S(A)` while `U(ψ)` is an open of `Proj_S(C)`: the two
names are interchanged. The statement below is `U(ψ ∘ φ) = r_ψ^{-1}(U(φ))`, which does typecheck
and is what the rest of the tag uses. See the implementation notes at the head of this file. -/
public theorem relativeMapDomain_comp :
    (ψ.comp φ).relativeMapDomain =
      ψ.relativeMapDomain.ι ''ᵁ (relativeMapHom ψ ⁻¹ᵁ φ.relativeMapDomain) := by
  rw [relativeMapHom_preimage_relativeMapDomain, Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι]
  exact (inf_eq_right.mpr (relativeMapDomain_comp_le φ ψ)).symm

/-- **The canonical identification of the two descriptions of the open attached to a composite is
compatible with the inclusions.** Read inside the relative projective spectrum of the target of
the composite, the identification is the inclusion of the inverse image into the open attached to
the outer factor. No transport is needed to compare the two sides: both are morphisms from the
inverse image to the relative projective spectrum of the target of the composite. -/
public theorem relativeMapDomainCompIso_hom_ι :
    let V := relativeMapHom ψ ⁻¹ᵁ φ.relativeMapDomain
    let e := (ψ.relativeMapDomain.ι.isoImage V) ≪≫
      (relativeProj C).scheme.isoOfEq (relativeMapDomain_comp φ ψ).symm
    e.hom ≫ (ψ.comp φ).relativeMapDomain.ι = V.ι ≫ ψ.relativeMapDomain.ι := by
  intro V e
  simp only [e, Iso.trans_hom, Category.assoc, Scheme.isoOfEq_hom_ι,
    Scheme.Hom.isoImage_hom_ι]

/-- **The second assertion of Tag 07ZH, in factorized form.** Let `q` be a morphism from the open
attached to the composite to the open attached to the inner factor which, followed by the
inclusion, is the inclusion followed by the morphism of the outer factor. Then the morphism
attached to the composite is `q` followed by the morphism of the inner factor.

`q` is unique with that property, because the inclusion of an open subscheme is a monomorphism. -/
public theorem relativeMapHom_comp'
    (q : (ψ.comp φ).relativeMapDomain.toScheme ⟶ φ.relativeMapDomain.toScheme)
    (hq : q ≫ φ.relativeMapDomain.ι =
      (relativeProj C).scheme.homOfLE (relativeMapDomain_comp_le φ ψ) ≫ relativeMapHom ψ) :
    relativeMapHom (ψ.comp φ) = q ≫ relativeMapHom φ := by
  refine (relativeMapHom_unique (ψ.comp φ) (q ≫ relativeMapHom φ) fun U => ?_).symm
  have hle := mapDomain_comp_le_of_eq (A.grading U.1) (B.grading U.1) (C.grading U.1)
    (φ.sectionHom U.1) (ψ.sectionHom U.1) (SheafGradedAlgebraHom.sectionHom_comp ψ φ U.1)
  obtain ⟨qU, hqU, hqU'⟩ := mapHom_comp_of_eq (A.grading U.1) (B.grading U.1) (C.grading U.1)
    (φ.sectionHom U.1) (ψ.sectionHom U.1) (SheafGradedAlgebraHom.sectionHom_comp ψ φ U.1) hle
  have hcomm : (((relativeProj C).chart U.1 U.2).isoImage
          (mapDomain (A.grading U.1) (C.grading U.1) ((ψ.comp φ).sectionHom U.1))).hom ≫
        (relativeProj C).scheme.homOfLE (chartImage_le (ψ.comp φ) U) ≫
          (relativeProj C).scheme.homOfLE (relativeMapDomain_comp_le φ ψ) =
      (AlgebraicGeometry.Proj (C.grading U.1)).homOfLE hle ≫
        (((relativeProj C).chart U.1 U.2).isoImage
            (mapDomain (B.grading U.1) (C.grading U.1) (ψ.sectionHom U.1))).hom ≫
          (relativeProj C).scheme.homOfLE (chartImage_le ψ U) := by
    rw [← cancel_mono ψ.relativeMapDomain.ι]
    simp only [Category.assoc, Scheme.homOfLE_ι, Scheme.homOfLE_ι_assoc,
      Scheme.Hom.isoImage_hom_ι]
  have hmid : (((relativeProj C).chart U.1 U.2).isoImage
          (mapDomain (A.grading U.1) (C.grading U.1) ((ψ.comp φ).sectionHom U.1))).hom ≫
        (relativeProj C).scheme.homOfLE (chartImage_le (ψ.comp φ) U) ≫ q =
      qU ≫ (((relativeProj B).chart U.1 U.2).isoImage
          (mapDomain (A.grading U.1) (B.grading U.1) (φ.sectionHom U.1))).hom ≫
        (relativeProj B).scheme.homOfLE (chartImage_le φ U) := by
    have hcomm' := congrArg (fun m => m ≫ relativeMapHom ψ) hcomm
    have hqU'' := congrArg (fun m => m ≫ (relativeProj B).chart U.1 U.2) hqU
    simp only [Category.assoc] at hcomm' hqU''
    rw [← cancel_mono φ.relativeMapDomain.ι]
    simp only [Category.assoc, Scheme.homOfLE_ι, Scheme.Hom.isoImage_hom_ι]
    rw [hq, hcomm', chart_comp_relativeMapHom ψ U, ← hqU'']
  have hgoal := congrArg (fun m => m ≫ relativeMapHom φ) hmid
  simp only [Category.assoc] at hgoal
  rw [hgoal, hqU']
  simp only [Category.assoc]
  rw [← chart_comp_relativeMapHom φ U]

/-- **The second assertion of Tag 07ZH.** Under the canonical identification of the open attached
to the composite with the inverse image of the open attached to the inner factor, the morphism
attached to the composite is the restriction of the morphism of the outer factor followed by the
morphism of the inner factor. -/
public theorem relativeMapHom_comp :
    let V := relativeMapHom ψ ⁻¹ᵁ φ.relativeMapDomain
    let e := (ψ.relativeMapDomain.ι.isoImage V) ≪≫
      (relativeProj C).scheme.isoOfEq (relativeMapDomain_comp φ ψ).symm
    e.hom ≫ relativeMapHom (ψ.comp φ) =
      (relativeMapHom ψ ∣_ φ.relativeMapDomain) ≫ relativeMapHom φ := by
  intro V e
  have hinv : e.inv ≫ V.ι =
      (relativeProj C).scheme.homOfLE (relativeMapDomain_comp_le φ ψ) := by
    rw [← cancel_mono ψ.relativeMapDomain.ι]
    simp only [e, Iso.trans_inv, Category.assoc, Scheme.Opens.isoImage_ι_inv_ι,
      Scheme.isoOfEq_inv_ι, Scheme.homOfLE_ι]
  have hq : (e.inv ≫ (relativeMapHom ψ ∣_ φ.relativeMapDomain)) ≫ φ.relativeMapDomain.ι =
      (relativeProj C).scheme.homOfLE (relativeMapDomain_comp_le φ ψ) ≫ relativeMapHom ψ := by
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hinv]
  rw [relativeMapHom_comp' φ ψ _ hq, Category.assoc, Iso.hom_inv_id_assoc]

end Relative

end Stacks.AlgebraicGeometry.RelativeProjMapComp

end
