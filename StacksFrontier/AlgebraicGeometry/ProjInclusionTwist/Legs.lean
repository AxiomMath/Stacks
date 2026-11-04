module

public import StacksFrontier.AlgebraicGeometry.ProjInclusionTwist.Basic

/-!
# Tag 01NO's twist comparison in the vocabulary of Tag 01MY's morphism and comparison map

Tag 01NO's comparison map on the `n`-th twist,
`Stacks.AlgebraicGeometry.ProjInclusionTwist.projInclusionTwistMap`, is a composite of six factors
written with the bundle `Stacks.AlgebraicGeometry.ProjTwistCompare.projMapData`:
`(projMapData …).hom` for the morphism of Tag 01MY and `(projMapData …).twistMap n` for its
comparison map. This file writes it with `Stacks.AlgebraicGeometry.ProjTwistCompare.mapHom` and
`Stacks.AlgebraicGeometry.ProjTwistCompare.twistMap` in their place.

## Main results

* `Stacks.AlgebraicGeometry.ProjInclusionTwist.twistLegs_eq`: the five-fold composite of Tag
  01MY's comparison map read at given legs, in the two spellings, at the level of variables.
* `Stacks.AlgebraicGeometry.ProjInclusionTwist.twistLegs_comp_eq`: the same equation with a sixth
  factor appended.
* `Stacks.AlgebraicGeometry.ProjInclusionTwist.projInclusionTopSection_comp_mapHom`: the
  factorisation of `Stacks.AlgebraicGeometry.RelativeProj.projInclusionMap` with `mapHom` in place
  of the bundle's morphism.
* `Stacks.AlgebraicGeometry.ProjInclusionTwist.projInclusionTwistMap_eq_mapHom`: Tag 01NO's
  comparison map on the `n`-th twist is the five-fold composite built from
  `Stacks.AlgebraicGeometry.ProjTwistCompare.mapHom` and `twistMap`, followed by the
  identification of the inverse image along the identity.
* `Stacks.AlgebraicGeometry.ProjInclusionTwist.projInclusionTwistIso_hom_eq_mapHom`: the same for
  the underlying morphism of the canonical isomorphism.

## Implementation notes

The two spellings are equal, by `Stacks.AlgebraicGeometry.ProjTwistCompare.projMapData_hom` and
`projMapData_twistMap`, both `rfl`. Identifying the two six-fold composites at a concrete pair of
affine opens of the base exceeds the kernel's deterministic budget, both by `rfl` and by rewriting
with those two equations: every junction of the composite asks for a comparison of two inverse
images along two definitionally equal but distinct morphisms, and that unfolds
`AlgebraicGeometry.Scheme.Modules.pullback`. The comparison is therefore stated at the level
of variables, where the two spellings differ by one delta step and one projection on a structure
literal, and the concrete statement is a substitution instance of it.

The three factor equations are stated separately so that each conversion stays isolated and the
five-fold equation can be assembled with `Stacks.AlgebraicGeometry.ProjInclusionTwist.comp_congr`,
which abstracts no motive over the offending term.

## References

* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01MZ](https://stacks.math.columbia.edu/tag/01MZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.ProjTwistCompare
open Stacks.AlgebraicGeometry.RelativeProj Stacks.AlgebraicGeometry.RelativeProjBridge

namespace Stacks.AlgebraicGeometry.ProjInclusionTwist

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj

universe u

section General

variable {C : Type*} [Category C]

/-- `(a ≫ b ≫ c ≫ d ≫ e) ≫ g = a ≫ b ≫ c ≫ d ≫ e ≫ g`, at the level of variables. -/
public theorem comp₅_comp {X₀ X₁ X₂ X₃ X₄ X₅ X₆ : C} (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃)
    (d : X₃ ⟶ X₄) (e : X₄ ⟶ X₅) (g : X₅ ⟶ X₆) :
    (a ≫ b ≫ c ≫ d ≫ e) ≫ g = a ≫ b ≫ c ≫ d ≫ e ≫ g := by
  simp only [Category.assoc]

end General

/-! ### The two spellings, at the level of variables -/

section Legs

universe w w'

variable {R₁ R₂ : Type u} {σ : Type w} {τ : Type w'}
  [CommRing R₁] [CommRing R₂]
  [SetLike σ R₁] [AddSubgroupClass σ R₁]
  [SetLike τ R₂] [AddSubgroupClass τ R₂]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

variable (φ : 𝒜 →+*ᵍ ℬ) (n : ℤ) {W : Scheme.{u}}

/-- **The leading congruence factor in the two spellings.** -/
public theorem pullbackCongr_inv_app_projMapData_hom {q : W ⟶ (mapDomain 𝒜 ℬ φ).toScheme}
    {d : W ⟶ AlgebraicGeometry.Proj 𝒜} (hd : q ≫ (projMapData 𝒜 ℬ φ).hom = d)
    (hd' : q ≫ mapHom 𝒜 ℬ φ = d) :
    (Scheme.Modules.pullbackCongr hd).inv.app (twistingSheaf 𝒜 n) =
      (Scheme.Modules.pullbackCongr hd').inv.app (twistingSheaf 𝒜 n) :=
  rfl

/-- **The pseudofunctoriality factor for the leg into the projective spectrum, in the two
spellings.** -/
public theorem pullbackComp_inv_app_projMapData_hom (q : W ⟶ (mapDomain 𝒜 ℬ φ).toScheme) :
    (Scheme.Modules.pullbackComp q (projMapData 𝒜 ℬ φ).hom).inv.app (twistingSheaf 𝒜 n) =
      (Scheme.Modules.pullbackComp q (mapHom 𝒜 ℬ φ)).inv.app (twistingSheaf 𝒜 n) :=
  rfl

/-- **The functor image of Tag 01MY's comparison map, in the two spellings.** -/
public theorem pullback_map_projMapData_twistMap (q : W ⟶ (mapDomain 𝒜 ℬ φ).toScheme) :
    (Scheme.Modules.pullback q).map ((projMapData 𝒜 ℬ φ).twistMap n) =
      (Scheme.Modules.pullback q).map (twistMap 𝒜 ℬ φ n) :=
  rfl

/-- **Tag 01MY's comparison map on the `n`-th twist, read at given legs, in the two spellings.**
A morphism `q` from a scheme to the domain of definition of `φ` presents the inverse images along
`q ≫ r_φ` and along `q ≫ U(φ).ι` of the two twists; the five-fold composite transporting the
comparison map to them is the same whether the morphism and the comparison map of Tag 01MY are
named through `Stacks.AlgebraicGeometry.ProjTwistCompare.projMapData` or directly. -/
public theorem twistLegs_eq (q : W ⟶ (mapDomain 𝒜 ℬ φ).toScheme)
    {d : W ⟶ AlgebraicGeometry.Proj 𝒜} (hd : q ≫ (projMapData 𝒜 ℬ φ).hom = d)
    (hd' : q ≫ mapHom 𝒜 ℬ φ = d)
    {i : W ⟶ AlgebraicGeometry.Proj ℬ} (hi : q ≫ (mapDomain 𝒜 ℬ φ).ι = i) :
    (Scheme.Modules.pullbackCongr hd).inv.app (twistingSheaf 𝒜 n) ≫
        (Scheme.Modules.pullbackComp q (projMapData 𝒜 ℬ φ).hom).inv.app (twistingSheaf 𝒜 n) ≫
        (Scheme.Modules.pullback q).map ((projMapData 𝒜 ℬ φ).twistMap n) ≫
        (Scheme.Modules.pullbackComp q (mapDomain 𝒜 ℬ φ).ι).hom.app (twistingSheaf ℬ n) ≫
        (Scheme.Modules.pullbackCongr hi).hom.app (twistingSheaf ℬ n) =
      (Scheme.Modules.pullbackCongr hd').inv.app (twistingSheaf 𝒜 n) ≫
        (Scheme.Modules.pullbackComp q (mapHom 𝒜 ℬ φ)).inv.app (twistingSheaf 𝒜 n) ≫
        (Scheme.Modules.pullback q).map (twistMap 𝒜 ℬ φ n) ≫
        (Scheme.Modules.pullbackComp q (mapDomain 𝒜 ℬ φ).ι).hom.app (twistingSheaf ℬ n) ≫
        (Scheme.Modules.pullbackCongr hi).hom.app (twistingSheaf ℬ n) :=
  comp_congr (pullbackCongr_inv_app_projMapData_hom 𝒜 ℬ φ n hd hd')
    (comp_congr (pullbackComp_inv_app_projMapData_hom 𝒜 ℬ φ n q)
      (comp_congr (pullback_map_projMapData_twistMap 𝒜 ℬ φ n q) rfl))

/-- **Tag 01MY's comparison map read at given legs, in the two spellings, with a sixth factor
appended.** The left-hand side is the right-associated six-fold composite; the right-hand side is
bracketed as the five factors of the comparison map followed by the sixth. -/
public theorem twistLegs_comp_eq (q : W ⟶ (mapDomain 𝒜 ℬ φ).toScheme)
    {d : W ⟶ AlgebraicGeometry.Proj 𝒜} (hd : q ≫ (projMapData 𝒜 ℬ φ).hom = d)
    (hd' : q ≫ mapHom 𝒜 ℬ φ = d)
    {i : W ⟶ AlgebraicGeometry.Proj ℬ} (hi : q ≫ (mapDomain 𝒜 ℬ φ).ι = i)
    {Z : W.Modules} (g : (Scheme.Modules.pullback i).obj (twistingSheaf ℬ n) ⟶ Z) :
    (Scheme.Modules.pullbackCongr hd).inv.app (twistingSheaf 𝒜 n) ≫
        (Scheme.Modules.pullbackComp q (projMapData 𝒜 ℬ φ).hom).inv.app (twistingSheaf 𝒜 n) ≫
        (Scheme.Modules.pullback q).map ((projMapData 𝒜 ℬ φ).twistMap n) ≫
        (Scheme.Modules.pullbackComp q (mapDomain 𝒜 ℬ φ).ι).hom.app (twistingSheaf ℬ n) ≫
        (Scheme.Modules.pullbackCongr hi).hom.app (twistingSheaf ℬ n) ≫ g =
      ((Scheme.Modules.pullbackCongr hd').inv.app (twistingSheaf 𝒜 n) ≫
          (Scheme.Modules.pullbackComp q (mapHom 𝒜 ℬ φ)).inv.app (twistingSheaf 𝒜 n) ≫
          (Scheme.Modules.pullback q).map (twistMap 𝒜 ℬ φ n) ≫
          (Scheme.Modules.pullbackComp q (mapDomain 𝒜 ℬ φ).ι).hom.app (twistingSheaf ℬ n) ≫
          (Scheme.Modules.pullbackCongr hi).hom.app (twistingSheaf ℬ n)) ≫ g :=
  (comp₅_comp ((Scheme.Modules.pullbackCongr hd).inv.app (twistingSheaf 𝒜 n))
      ((Scheme.Modules.pullbackComp q (projMapData 𝒜 ℬ φ).hom).inv.app (twistingSheaf 𝒜 n))
      ((Scheme.Modules.pullback q).map ((projMapData 𝒜 ℬ φ).twistMap n))
      ((Scheme.Modules.pullbackComp q (mapDomain 𝒜 ℬ φ).ι).hom.app (twistingSheaf ℬ n))
      ((Scheme.Modules.pullbackCongr hi).hom.app (twistingSheaf ℬ n)) g).symm.trans
    (congrArg (fun z => z ≫ g) (twistLegs_eq 𝒜 ℬ φ n q hd hd' hi))

end Legs

/-! ### Tag 01NO's comparison map, in the `mapHom`/`twistMap` spelling -/

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S) (U V : S.Opens) (h : U ≤ V)
  (hU : IsAffineOpen U) (hV : IsAffineOpen V) (n : ℤ)

/-- **The everywhere-defined morphism of projective spectra is the identification of
`Proj Γ(U, A)` with the open domain followed by the morphism of Tag 01MY**, with the morphism
written `Stacks.AlgebraicGeometry.ProjTwistCompare.mapHom`. -/
public theorem projInclusionTopSection_comp_mapHom :
    projInclusionTopSection A U V h hU hV ≫ mapHom (A.grading V) (A.grading U) (A.res h) =
      projInclusionMap A U V h hU hV :=
  Category.assoc _ _ _

/-- **Tag 01NO's comparison map on the `n`-th twist, in the vocabulary of Tag 01MY's morphism and
comparison map.** The five factors transporting
`Stacks.AlgebraicGeometry.ProjTwistCompare.twistMap` along the identification of the open domain
of the restriction with the whole projective spectrum, followed by the identification of the
inverse image along the identity. The first five factors are Tag 01MY's comparison map for the
restriction `Γ(V, A) ⟶ Γ(U, A)`, read at the legs
`Stacks.AlgebraicGeometry.RelativeProj.projInclusionMap` and `𝟙 (Proj Γ(U, A))`. -/
public theorem projInclusionTwistMap_eq_mapHom :
    projInclusionTwistMap A U V h hU hV n =
      ((Scheme.Modules.pullbackCongr
              (projInclusionTopSection_comp_mapHom A U V h hU hV)).inv.app
            (twistingSheaf (A.grading V) n) ≫
          (Scheme.Modules.pullbackComp (projInclusionTopSection A U V h hU hV)
              (mapHom (A.grading V) (A.grading U) (A.res h))).inv.app
            (twistingSheaf (A.grading V) n) ≫
          (Scheme.Modules.pullback (projInclusionTopSection A U V h hU hV)).map
            (twistMap (A.grading V) (A.grading U) (A.res h) n) ≫
          (Scheme.Modules.pullbackComp (projInclusionTopSection A U V h hU hV)
              (mapDomain (A.grading V) (A.grading U) (A.res h)).ι).hom.app
            (twistingSheaf (A.grading U) n) ≫
          (Scheme.Modules.pullbackCongr (projInclusionTopSection_ι A U V h hU hV)).hom.app
            (twistingSheaf (A.grading U) n)) ≫
        (Scheme.Modules.pullbackId
          (AlgebraicGeometry.Proj (A.grading U))).hom.app (twistingSheaf (A.grading U) n) :=
  (projInclusionTwistMap_eq A U V h hU hV n).trans
    (twistLegs_comp_eq (A.grading V) (A.grading U) (A.res h) n
      (projInclusionTopSection A U V h hU hV) (projInclusionMap_eq_comp A U V h hU hV)
      (projInclusionTopSection_comp_mapHom A U V h hU hV)
      (projInclusionTopSection_ι A U V h hU hV)
      ((Scheme.Modules.pullbackId
        (AlgebraicGeometry.Proj (A.grading U))).hom.app (twistingSheaf (A.grading U) n)))

/-- **The underlying morphism of Tag 01NO's canonical isomorphism on the `n`-th twist, in the
vocabulary of Tag 01MY's morphism and comparison map.** -/
public theorem projInclusionTwistIso_hom_eq_mapHom :
    (projInclusionTwistIso A U V h hU hV n).hom =
      ((Scheme.Modules.pullbackCongr
              (projInclusionTopSection_comp_mapHom A U V h hU hV)).inv.app
            (twistingSheaf (A.grading V) n) ≫
          (Scheme.Modules.pullbackComp (projInclusionTopSection A U V h hU hV)
              (mapHom (A.grading V) (A.grading U) (A.res h))).inv.app
            (twistingSheaf (A.grading V) n) ≫
          (Scheme.Modules.pullback (projInclusionTopSection A U V h hU hV)).map
            (twistMap (A.grading V) (A.grading U) (A.res h) n) ≫
          (Scheme.Modules.pullbackComp (projInclusionTopSection A U V h hU hV)
              (mapDomain (A.grading V) (A.grading U) (A.res h)).ι).hom.app
            (twistingSheaf (A.grading U) n) ≫
          (Scheme.Modules.pullbackCongr (projInclusionTopSection_ι A U V h hU hV)).hom.app
            (twistingSheaf (A.grading U) n)) ≫
        (Scheme.Modules.pullbackId
          (AlgebraicGeometry.Proj (A.grading U))).hom.app (twistingSheaf (A.grading U) n) :=
  (projInclusionTwistIso_hom A U V h hU hV n).trans
    (projInclusionTwistMap_eq_mapHom A U V h hU hV n)

end Stacks.AlgebraicGeometry.ProjInclusionTwist

end
