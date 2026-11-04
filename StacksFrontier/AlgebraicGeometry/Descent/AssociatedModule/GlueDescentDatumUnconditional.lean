module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.EffectiveGlueAgreementRestrFun
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.EffectiveGlueAgreementTransport
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.EquivalenceUnconditional
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.QcohGlueEffectivity

/-!
# The glued module of Stacks 03DX (1) with its compatible local isomorphisms

`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/EffectiveGlueAgreementTransport.lean`
proves the essential-surjectivity half of Stacks 03DX (1) for `τ = fppf` with no hypothesis —
`AlgebraicGeometry.BigFppfOver.quasicoherentIsEssImageAssociatedModule'` — and
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/EffectiveGlueAgreementRestrFun.lean`
proves the agreement criterion
`AlgebraicGeometry.BigFppfOver.homRestr_eq_of_restrictObjRestrictIso_eq`, the descent datum
`AlgebraicGeometry.BigFppfOver.associatedModuleGlueDescentDatum` and the fppf equivalence
`AlgebraicGeometry.BigFppfOver.isEquivalence_associatedModuleQcohOnSite_fppf`.  This file
records one statement beyond those: the glued module together with its compatible family of
local isomorphisms, as one existence statement.

## Main results

* `AlgebraicGeometry.BigFppfOver.exists_objRestrict_agree_of_fpqc`: out of the local
  associated-module data on a family whose structure morphisms are an fpqc covering family of `S`,
  a quasi-coherent `𝓕` on `S` and a compatible family of local isomorphisms
  `𝓕^a|_{(Sch/X_i)_fppf} ≅ 𝒢|_{(Sch/X_i)_fppf}`.

## Implementation notes

Nothing here carries a `stacks` attribute.  Clause (1) of Stacks 03DX at `τ = fppf` is registered
on `AlgebraicGeometry.BigFppfOver.quasicoherentIsEssImageAssociatedModule'`, and the clause at
every `τ` on `AlgebraicGeometry.BigFppfOver.baseAssociatedModuleEquivalenceOnSite'`.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
* [Stacks Project, Tag 06WI](https://stacks.math.columbia.edu/tag/06WI)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
-/
@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The local isomorphisms of Stacks 03DX (1), with their agreement -/

/-- **The glued module of Stacks 03DX (1) and its compatible family of local isomorphisms.**  Let
`𝒢` be a sheaf of modules on `(Sch/S)_fppf`, let `X` be a family of objects whose structure
morphisms are an fpqc covering family of the scheme `S`, and let the restriction of `𝒢` to the big
fppf site of the scheme of each member be the associated module of a quasi-coherent `𝓕_i` there.
Then there is a quasi-coherent `𝒪_S`-module `𝓕` and isomorphisms
`𝓕^a|_{(Sch/X_i)_fppf} ≅ 𝒢|_{(Sch/X_i)_fppf}` whose relocalizations agree over the fibre products
`X i ×_S X j`.

The module is `AlgebraicGeometry.BigFppfOver.effectiveGlueModule` at the effectivity witness
`AlgebraicGeometry.BigFppfOver.isEffective_memberQcohDatum` — the effectivity half of
Stacks 023T applied to the quasi-coherent descent datum of the family — the local isomorphisms are
`AlgebraicGeometry.BigFppfOver.effectiveGlueObjRestrictIso`, their agreement in the `objRestrict`
spelling is `AlgebraicGeometry.BigFppfOver`
`.restrictObjRestrictIso_effectiveGlueObjRestrictIso_eq`, and
`AlgebraicGeometry.BigFppfOver.homRestr_eq_of_restrictObjRestrictIso_eq`
transports that agreement to the relocalizations. -/
public theorem exists_objRestrict_agree_of_fpqc {I : Type w} (X : I → BigFppfOver B S hS)
    (G : SheafOfModules.{u} (structureSheaf B S hS))
    (F : ∀ i, (objScheme B S hS (X i)).Modules) (hF : ∀ i, (F i).IsQuasicoherent)
    (e : ∀ i, (associatedModule B (objScheme B S hS (X i))
      (contains_objScheme B S hS (X i))).obj (F i) ≅ (objRestrict B S hS (X i)).obj G)
    (hfpqc : (objHypercover B S hS X).presieve₀ ∈ Scheme.fpqcPrecoverage.{u} S) :
    ∃ (𝓕 : S.Modules) (_ : 𝓕.IsQuasicoherent)
      (θ : ∀ i, (objRestrict B S hS (X i)).obj ((associatedModule B S hS).obj 𝓕) ≅
        (objRestrict B S hS (X i)).obj G),
      ∀ i j, homRestr (commStructurePresheaf B S hS)
            ((associatedModule B S hS).obj 𝓕).val G.val (memberProdFst B S hS X i j)
            (objRestrictPreimageIso B S hS (θ i)).hom.val =
          homRestr (commStructurePresheaf B S hS) ((associatedModule B S hS).obj 𝓕).val G.val
            (memberProdSnd B S hS X i j) (objRestrictPreimageIso B S hS (θ j)).hom.val := by
  have heff := isEffective_memberQcohDatum B S hS X G F hF e hfpqc
  refine ⟨effectiveGlueModule B S hS X G F hF e heff,
    isQuasicoherent_effectiveGlueModule B S hS X G F hF e heff,
    effectiveGlueObjRestrictIso B S hS X G F hF e heff, fun i j => ?_⟩
  exact homRestr_eq_of_restrictObjRestrictIso_eq B S hS
    (memberProdFst B S hS X i j) (memberProdSnd B S hS X i j) _ _
    (restrictObjRestrictIso_effectiveGlueObjRestrictIso_eq B S hS X G F hF e heff
      (memberProdFst B S hS X i j) (memberProdSnd B S hS X i j))

end AlgebraicGeometry.BigFppfOver

end
