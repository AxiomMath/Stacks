module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Algebra.Homology.HomotopyCategory.Adjunction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CoefficientChange.TorsionFreeComplexes
public import StacksFrontier.CategoryTheory.Localization.HomBijective
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorsionFreeResolutions

/-!
# Maps out of a torsion-free complex are computed in the homotopy category

Let `Λ` be a coefficient ring and `X` a scheme.  For `K` a cohomologically bounded-above complex
of abelian sheaves on the small étale site of `X` with sectionwise torsion-free terms, and `I` a
K-injective complex of sheaves of `Λ`-modules, the localization functor
`CategoryTheory.DerivedCategory.Qh` is *bijective* on maps from `K` into the abelian complex
underlying `I`.  That is: such maps are computed in the homotopy category, with no fractions.

This is the engine of the first diagram of [Stacks, Tag 0GL6].  Restriction of coefficients does
not preserve K-injective complexes, so the comparison of the two derived direct images cannot be
read off from a K-injective resolution; what replaces that is the adjunction
`Stacks.EtaleCohomology.etaleAbelianExtendForgetAdj`, through which maps out of a complex where
extension of coefficients is *exact* -- a torsion-free one -- are computed in the homotopy
category.  The bijectivity below is exactly the corepresentability input that
`Stacks.Cohomology.DerivedLowerShriek.rightDerivedUnit_isIso_of_corepresentable` consumes.

## Main results

* `Stacks.EtaleCohomology.forgetToAbelian_precomp_bijective_of_isTorsionFree`
* `Stacks.EtaleCohomology.qh_map_bijective_of_isLE_of_isTorsionFree`

## Implementation notes

The argument is not new; it is the dévissage of [Stacks, Tag 0D6J], and the generic steps are
taken from the library rather than rebuilt: `Stacks.Localization.adjunction_precomp_bijective`,
`Stacks.Localization.precomp_bijective_of_localization` and
`Stacks.Localization.localization_map_bijective_of_refinements`, with Mathlib's
`CochainComplex.IsKInjective.Qh_map_bijective` as the base case.  The only étale-specific inputs
are `Stacks.EtaleCohomology.quasiIso_map_etaleAbelianSheafExtend_of_isTorsionFree` and
the resolution `CategoryTheory.exists_isTorsionFree_resolution_of_isLE`.

**Why this is stated here and not reused from the two existing library copies.**  The same two
lemmas exist, `private`, in `Stacks.Cohomology.ForgetModule` and in the topological-site file,
and neither can be instantiated here: both are stated for a `SmallCategory` site with the site
and sheaf universes collapsed to one `u`.  The small étale site is large and only essentially
small, and its sheaves live at a module universe strictly above the site's, so it is precisely
the excluded case.  The generic steps above, by contrast, are stated at `Type*` with
no smallness and no universe coupling, which is why they are reused verbatim.

## References

* [Stacks Project, Tag 0GL6](https://stacks.math.columbia.edu/tag/0GL6)
* [Stacks Project, Tag 0D6J](https://stacks.math.columbia.edu/tag/0D6J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Localization
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [CommRing Λ] (X : Scheme.{u})

/-- **Precomposition with a quasi-isomorphism of torsion-free complexes is bijective on maps into
the abelian complex underlying a K-injective complex of modules.**  This is the adjunction
`etaleAbelianExtendForgetAdj` transported to homotopy categories: on the other side of it the
statement is about extension of coefficients, which is exact on torsion-free complexes. -/
theorem forgetToAbelian_precomp_bijective_of_isTorsionFree
    {K L : CochainComplex (EtaleAbelianSheaves.{u, r} X) ℤ} (q : K ⟶ L) [QuasiIso q]
    (hK : ∀ i V, Module.IsTorsionFree ℤ ((K.X i).obj.obj V))
    (hL : ∀ i V, Module.IsTorsionFree ℤ ((L.X i).obj.obj V))
    (I : CochainComplex (EtaleModules.{u, r} Λ X) ℤ) [I.IsKInjective] :
    let Q := HomotopyCategory.quotient (EtaleAbelianSheaves.{u, r} X) (.up ℤ)
    let V := (etaleModuleForgetToAbelian.{u, r} Λ X).mapHomotopyCategory (.up ℤ)
    Function.Bijective (fun a : Q.obj L ⟶ V.obj
      ((HomotopyCategory.quotient _ (.up ℤ)).obj I) => Q.map q ≫ a) := by
  let F := (etaleAbelianSheafExtend.{u, r} Λ X).mapHomotopyCategory (.up ℤ)
  let Q := HomotopyCategory.quotient (EtaleAbelianSheaves.{u, r} X) (.up ℤ)
  apply adjunction_precomp_bijective
    ((etaleAbelianExtendForgetAdj.{u, r} Λ X).mapHomotopyCategory (.up ℤ))
  have hiso : IsIso (DerivedCategory.Qh.map (F.map (Q.map q))) := by
    apply Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso _ (.up ℤ))
    show HomotopyCategory.quasiIso _ (.up ℤ)
      ((HomotopyCategory.quotient _ (.up ℤ)).map
        (((etaleAbelianSheafExtend.{u, r} Λ X).mapHomologicalComplex (.up ℤ)).map q))
    rw [HomotopyCategory.quotient_map_mem_quasiIso_iff]
    exact quasiIso_map_etaleAbelianSheafExtend_of_isTorsionFree.{u, r} Λ X q hK hL
  exact precomp_bijective_of_localization DerivedCategory.Qh (F.map (Q.map q))
    (CochainComplex.IsKInjective.Qh_map_bijective _ I)
    (CochainComplex.IsKInjective.Qh_map_bijective _ I)

/-- **Maps from a cohomologically bounded-above sectionwise torsion-free complex of abelian
sheaves into the abelian complex underlying a K-injective complex of `Λ`-modules are computed in
the homotopy category.**  The right calculus of fractions is refined away using the torsion-free
resolution: any quasi-isomorphism onto the source is refined by one out of a torsion-free
complex, where the previous lemma applies. -/
theorem qh_map_bijective_of_isLE_of_isTorsionFree
    (K : CochainComplex (EtaleAbelianSheaves.{u, r} X) ℤ) (n : ℤ) [K.IsLE n]
    (hK : ∀ i V, Module.IsTorsionFree ℤ ((K.X i).obj.obj V))
    (I : CochainComplex (EtaleModules.{u, r} Λ X) ℤ) [I.IsKInjective] :
    let Q := HomotopyCategory.quotient (EtaleAbelianSheaves.{u, r} X) (.up ℤ)
    let G := (etaleModuleForgetToAbelian.{u, r} Λ X).mapHomologicalComplex (.up ℤ)
    Function.Bijective (DerivedCategory.Qh.map :
      (Q.obj K ⟶ Q.obj (G.obj I)) → _) := by
  let Q := HomotopyCategory.quotient (EtaleAbelianSheaves.{u, r} X) (.up ℤ)
  apply localization_map_bijective_of_refinements (HomotopyCategory.quasiIso _ (.up ℤ))
  intro Z s hs
  obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective Z
  obtain ⟨s, rfl⟩ := Q.map_surjective s
  have hqs : QuasiIso s := (HomotopyCategory.quotient_map_mem_quasiIso_iff s).mp hs
  have : CochainComplex.IsLE L n := (CochainComplex.isLE_iff L n).mpr (fun i hi =>
    let := hqs.quasiIsoAt i
    (exactAt_iff_of_quasiIsoAt s i).mpr (K.exactAt_of_isLE n i hi))
  obtain ⟨P, p, hp, hP⟩ := exists_isTorsionFree_resolution_of_isLE X.smallEtaleTopology L n
  refine ⟨Q.obj P, Q.map p, (HomotopyCategory.quotient_map_mem_quasiIso_iff p).mpr hp, ?_⟩
  let e := ((etaleModuleForgetToAbelian.{u, r} Λ X).mapHomotopyCategoryFactors (.up ℤ)).app I
  have hb : Function.Bijective
      (fun a : Q.obj K ⟶ ((etaleModuleForgetToAbelian.{u, r} Λ X).mapHomotopyCategory
        (.up ℤ)).obj ((HomotopyCategory.quotient _ (.up ℤ)).obj I) =>
        (Q.map p ≫ Q.map s) ≫ a) := by
    simpa only [Functor.map_comp] using
      forgetToAbelian_precomp_bijective_of_isTorsionFree.{u, r} Λ X (p ≫ s) hP hK I
  refine ⟨fun a b hab => ?_, fun b => ?_⟩
  · apply (cancel_mono e.inv).mp
    apply hb.injective
    simpa only [Category.assoc] using congrArg (fun t => t ≫ e.inv) hab
  · obtain ⟨a, ha⟩ := hb.surjective (b ≫ e.inv)
    refine ⟨a ≫ e.hom, ?_⟩
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
      congrArg (fun t => t ≫ e.hom) ha

end Stacks.EtaleCohomology

end
