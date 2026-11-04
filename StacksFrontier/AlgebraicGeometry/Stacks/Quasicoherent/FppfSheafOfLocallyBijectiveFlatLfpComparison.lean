module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfSheafFromSheafFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangePropertySheafified

/-!
# Stacks 076T, with the comparison maps read as maps of sheaves

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and `F` a presheaf of modules over
the structure sheaf of **Stacks 06TV**. **Stacks 076T** says: if `F` is locally quasi-coherent
(**Stacks 06WJ**) and the comparison map `c_φ : f_{small}^*(F|_{V_ét}) ⟶ F|_{U_ét}` of
**Stacks 06WC** is an isomorphism for every arrow `φ` of `𝒳` lying over a morphism of schemes
`f : U ⟶ V` which is flat and locally of finite presentation, then `F` is a sheaf for the fppf
topology of **Stacks 06TP**.

In the source `f_{small}^*` is the inverse image of *sheaves* of modules, so the hypothesis on
`c_φ` is that the comparison of the library at `φ` be an isomorphism after étale sheafification
of its source, that is, that it be locally injective and locally surjective for the étale
topology of the small site of `U`
(`AlgebraicGeometry.Stack.IsLocallyBijectiveRestrictModulePullbackComparisonUnivLE`, and
`AlgebraicGeometry.Stack.isIso_sheafifiedRestrictModulePullbackComparison_iff` for the
identification with the sheafified comparison). The proof is
`AlgebraicGeometry.Stack.isSheaf_fppf_of_isLocallyQuasicoherent_of_sheafFlatLfpBaseChange`, whose
hypothesis `AlgebraicGeometry.Stack.HasSheafFlatLfpBaseChangeProperty` is this condition.

## Main results

* `AlgebraicGeometry.Stack.isSheaf_fppf_of_isLocallyQuasicoherent_of_isLocallyBijective_flatLfp`:
  **Stacks 076T**.

## References

* [Stacks Project, Tag 06TP](https://stacks.math.columbia.edu/tag/06TP)
* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 076T](https://stacks.math.columbia.edu/tag/076T)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
    (etaleTopology_le_topology B)).obj)

/-- **Stacks 076T**, with the pullback of sheaves of Stacks 06WC. Let `F` be a presheaf of
modules over the structure sheaf of a category fibred in groupoids over `(Sch/S)_{fppf}`. If `F`
is locally quasi-coherent (Stacks 06WJ) and the comparison map
`c_φ : f_{small}^*(F|_{V_ét}) ⟶ F|_{U_ét}` is an isomorphism of sheaves (it is locally injective
and locally surjective for the étale topology of the small site of `U`) for every arrow `φ` of
`𝒳` lying over a morphism of schemes which is flat and locally of finite presentation, then `F`
is a sheaf for the fppf topology of Stacks 06TP. -/
@[stacks 076T "with the pullback of sheaves of Stacks 06WC in hypothesis (b)"]
theorem isSheaf_fppf_of_isLocallyQuasicoherent_of_isLocallyBijective_flatLfp
    (hlqc : IsLocallyQuasicoherent B E h S hS p hp F)
    (hbc : ∀ {x y : 𝒳} (φ : x ⟶ y), Flat (B.inclusion.map (p.map φ).left) →
      LocallyOfFinitePresentation (B.inclusion.map (p.map φ).left) →
        IsLocallyBijectiveRestrictModulePullbackComparisonUnivLE B E h S hS p hp
          (etaleTopology B) (etaleTopology_le_topology B) φ F) :
    Presheaf.IsSheaf (associatedTopology B S hS p B.topology) F.presheaf :=
  isSheaf_fppf_of_isLocallyQuasicoherent_of_sheafFlatLfpBaseChange B E h S hS p hp F hlqc hbc

end AlgebraicGeometry.Stack

end
