module

public import StacksFrontier.AlgebraicGeometry.RelativeProjTwistChartBridge.TwistQuadrupleChart
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.Zariski

/-!
# The quadruple of the glued twists along a morphism into the degree-`d` locus

Let `r : T ⟶ Proj_S(𝒜)` be a morphism over `f : T ⟶ S` landing in the relative degree-`d` locus
`U_d`. The twisting `...RelativeProjTwistChartBridge.twistTwisting` of the glued twists of
[Stacks, Tag 01NR] along `r` has surjective degree-one component, so it is a quadruple of
Section 01NS, `twistQuadruple`; and the morphism `T ⟶ U_d` that the representation of `F_d`
attaches to its class is the factorization of `r` through `U_d`.

## Main results

* `...RelativeProjTwistChartBridge.epi_twistTwisting_app_one`: the degree-one component of the
  twisting is an epimorphism.
* `...RelativeProjTwistChartBridge.twistQuadruple`: the quadruple.
* `...RelativeProjTwistChartBridge.homDegreeOpen_twistQuadruple`: **its class is classified by
  the factorization of `r` through `U_d`.**

## References

* [Stacks Project, Tag 01O1](https://stacks.math.columbia.edu/tag/01O1)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.RingedSpace
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.RelativeProjTwists
open Stacks.AlgebraicGeometry.RelativeVeroneseTwists
open Stacks.AlgebraicGeometry.ProjChartFromRatios (VeroneseSections)
open Stacks.AlgebraicGeometry.MorphismsIntoProj (toProj)

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjTwistChartBridge

variable {S : Scheme.{u}} {A : SheafGradedAlgebra.{u} S}

/-! ### Two transports of a generation condition -/

/-- The generation condition read back from the grading `𝒜(U')` at the grading of the global
sections of `A|_U`. -/
theorem iSup_nonvanishingOpen_psiSection_restrict_heq' (U : S.Opens) {U' : S.Opens} {k : ℕ}
    {T : Scheme.{u}} (L : T.Modules) [Stacks.Ample.IsInvertibleModule T L]
    (hU' : U.ι ''ᵁ (⊤ : Opens U.toScheme.toRingedSpace.carrier) = U')
    (ψ : VeroneseSections ((A.restrict U.ι).grading (⊤ : U.toScheme.Opens)) k L)
    (ψ' : VeroneseSections (A.grading U') k L) (hψ : HEq ψ ψ')
    (hgen : (⨆ g : A.grading U' k, Stacks.NonvanishingOpen.nonvanishingOpen T L
      (MorphismToProjUniversal.psiSection (A.grading U') ψ' g)) = ⊤) :
    (⨆ g : (A.restrict U.ι).grading (⊤ : U.toScheme.Opens) k,
      Stacks.NonvanishingOpen.nonvanishingOpen T L
        (MorphismToProjUniversal.psiSection ((A.restrict U.ι).grading (⊤ : U.toScheme.Opens)) ψ
          g)) = ⊤ := by
  subst hU'
  exact iSup_nonvanishingOpen_psiSection_heq _ _ _ _
    (SheafGradedAlgebra.restrict_ι_sectionRing_image A U).symm
    (SheafGradedAlgebra.restrict_ι_addSubgroup_eq A U).symm
    (SheafGradedAlgebra.restrict_ι_commRing_heq A U).symm
    (SheafGradedAlgebra.restrict_ι_setLike_heq A U).symm
    (SheafGradedAlgebra.restrict_ι_grading_heq A U).symm ψ' ψ hψ.symm hgen

/-- The generation condition of the Veronese family of a twisting over an affine base, read on
the degree-one sections of the twisting. -/
theorem iSup_nonvanishingOpen_degreeOneSectionHom_of_veroneseSections {T S : Scheme.{u}}
    {f : T ⟶ S} {B : SheafGradedAlgebra S} {k : ℕ} {L : T.Modules}
    [Stacks.Ample.IsInvertibleModule T L]
    (ψ : Twisting f (situationAlgebra B) (k : ℤ) L)
    (hgen : (⨆ a : B.grading (⊤ : S.Opens) k, Stacks.NonvanishingOpen.nonvanishingOpen T L
      (MorphismToProjUniversal.psiSection (B.grading (⊤ : S.Opens)) (veroneseSections ψ) a)) =
        ⊤) :
    (⨆ b : ((situationAlgebra B).piece (k : ℤ)).val.obj
        (op (⊤ : TopologicalSpace.Opens S.toRingedSpace.carrier)),
      Stacks.NonvanishingOpen.nonvanishingOpen T L (Twisting.degreeOneSectionHom ψ b)) = ⊤ := by
  refine top_unique ((le_of_eq hgen.symm).trans ?_)
  refine iSup_le fun a => le_iSup_of_le ((a : B.sectionRing ⊤) k) (le_of_eq ?_)
  rw [← nonvanishingOpen_psiSection_veroneseSections ψ ((a : B.sectionRing ⊤) k)]
  exact congrArg (fun z => Stacks.NonvanishingOpen.nonvanishingOpen T L
    (MorphismToProjUniversal.psiSection (B.grading (⊤ : S.Opens)) (veroneseSections ψ) z))
    (Subtype.ext (of_component a)).symm

/-! ### The degree-one component is an epimorphism -/

variable (D : TwistData A) (d : ℕ) {T : Scheme.{u}} (r : T ⟶ (relativeProj A).scheme)
  (hg : ∀ t : T, r.base t ∈ (relativeProj A).degreeOpen d)
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T)
    (twistLine D d r)]

/-- An epimorphism in degree one survives the transport along an equality of base morphisms. -/
theorem epi_app_one_of_congrBase {T S : Scheme.{u}}
    {B : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} {e : ℤ}
    {L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
    [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
    {g g' : T ⟶ S} (h : g = g') (ψ : Twisting g B e L)
    (hψ : Epi ((Twisting.congrBase h ψ).app 1)) : Epi (ψ.app 1) := by
  subst h
  exact hψ

include hg in
/-- **Over the preimage of an affine open of the base, the pulled-back twisting has surjective
degree-one component.** -/
theorem epi_pullback_twistTwisting_app_one (U : S.Opens) (hU : IsAffineOpen U) :
    Epi (((twistTwisting D d r hg rfl).pullback
      ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι).app 1) := by
  obtain ⟨ψ, hψ⟩ := exists_veroneseSections_restrict A U _ U.ι_image_top
    (veroneseSections (chartTwisting A U (chartBase U r) (chartTwistingOf D d U r hg)))
  have hgenR := iSup_nonvanishingOpen_psiSection_restrict_heq' U _ U.ι_image_top _ ψ hψ
    (iSup_nonvanishingOpen_chartTwistingOf D d U hU r hg ψ hψ)
  have hgenB := iSup_nonvanishingOpen_degreeOneSectionHom_of_veroneseSections
    (chartTwisting A U (chartBase U r) (chartTwistingOf D d U r hg)) hgenR
  have hepi := AffineTwisting.epi_app_one _ _ _ _
    (chartTwisting A U (chartBase U r) (chartTwistingOf D d U r hg)) hgenB
  have h1 : Epi ((pullbackFunctor (ringedSpaceHom (chartBase U r))).map
      ((unitalHomInverse (restrictPullbackUnitalHom A U.ι)
        (isIso_restrictPullbackUnitalHom_app_forall A U.ι)).app (1 * (d : ℤ))) ≫
      (@inv _ _ _ _ (compComparison (chartBase U r) U.ι ((situationAlgebra A).piece (1 * (d : ℤ))))
        (isIso_compComparison _ _ _) ≫
        (chartTwistingOf D d U r hg).app 1)) := hepi
  have h2 : Epi (@inv _ _ _ _ (compComparison (chartBase U r) U.ι
      ((situationAlgebra A).piece (1 * (d : ℤ)))) (isIso_compComparison _ _ _) ≫
        (chartTwistingOf D d U r hg).app 1) :=
    @epi_of_epi _ _ _ _ _ ((pullbackFunctor (ringedSpaceHom (chartBase U r))).map
      ((unitalHomInverse (restrictPullbackUnitalHom A U.ι)
        (isIso_restrictPullbackUnitalHom_app_forall A U.ι)).app (1 * (d : ℤ)))) _ h1
  have h3 : Epi ((chartTwistingOf D d U r hg).app 1) :=
    @epi_of_epi _ _ _ _ _ (@inv _ _ _ _ (compComparison (chartBase U r) U.ι
      ((situationAlgebra A).piece (1 * (d : ℤ)))) (isIso_compComparison _ _ _)) _ h2
  exact epi_app_one_of_congrBase _ _ h3

include hg in
/-- **The degree-one component of the twisting of the glued twists along `r` is an
epimorphism**, for `r ≫ π` itself. Being an epimorphism is local, and over the preimage of each
affine open of the base it is `epi_pullback_twistTwisting_app_one`. -/
theorem epi_twistTwisting_app_one_rfl :
    Epi ((twistTwisting D d r hg rfl).app 1) := by
  have hloc : ∀ a : {U : S.Opens // IsAffineOpen U},
      Epi ((Scheme.Modules.pullback ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ a.1).ι).map
        ((twistTwisting D d r hg rfl).app 1)) := by
    intro a
    have h1 := epi_pullback_twistTwisting_app_one D d r hg a.1 a.2
    have h2 : Epi ((pullbackFunctor (ringedSpaceHom ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ a.1).ι)).map
        ((twistTwisting D d r hg rfl).app 1) ≫
        laurentPullback ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ a.1).ι (twistLine D d r) 1) :=
      @epi_of_epi _ _ _ _ _ (compComparison ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ a.1).ι
        (r ≫ (relativeProj A).toBase) ((situationAlgebra A).piece (1 * (d : ℤ)))) _ h1
    have h3 : (pullbackFunctor (ringedSpaceHom ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ a.1).ι)).map
        ((twistTwisting D d r hg rfl).app 1) =
        ((pullbackFunctor (ringedSpaceHom ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ a.1).ι)).map
          ((twistTwisting D d r hg rfl).app 1) ≫
          laurentPullback ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ a.1).ι (twistLine D d r) 1) ≫
        inv (laurentPullback ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ a.1).ι (twistLine D d r) 1) := by
      rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    change Epi ((pullbackFunctor (ringedSpaceHom ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ a.1).ι)).map
        ((twistTwisting D d r hg rfl).app 1))
    rw [h3]
    exact epi_comp _ _
  refine Stacks.Descent.epi_of_pullback_map_epi
    (fun a : {U : S.Opens // IsAffineOpen U} => ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ a.1).ι)
    ?_ ((twistTwisting D d r hg rfl).app 1) hloc
  refine top_unique fun x _ => ?_
  obtain ⟨a, ha⟩ := exists_mem_preimage_affineOpen (r ≫ (relativeProj A).toBase) x
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨a, by rw [Scheme.Opens.opensRange_ι]; exact ha⟩

include hg in
/-- **The degree-one component of the twisting of the glued twists along `r` is an
epimorphism.** -/
theorem epi_twistTwisting_app_one {f : T ⟶ S}
    (hr : r ≫ (relativeProj A).toBase = f) :
    Epi ((twistTwisting D d r hg hr).app 1) := by
  subst hr
  exact epi_twistTwisting_app_one_rfl D d r hg

/-! ### The quadruple, and the morphism it classifies -/

/-- **The quadruple of the glued twists along `r`**: `(f, d, r^*𝒪(d), ψ)`, the twisting being the
second leg of [Stacks, Tag 01O1]'s triangle followed by the recognition comparison. -/
def twistQuadruple {f : T ⟶ S} (hr : r ≫ (relativeProj A).toBase = f) :
    Quadruple f (situationAlgebra A) (d : ℤ) where
  L := twistLine D d r
  isInvertible := inferInstance
  twisting := twistTwisting D d r hg hr
  epi_app_one := epi_twistTwisting_app_one D d r hg hr

/-- The degree-`n` component of the twisting of `twistQuadruple` is the Veronese leg
`psiLegVeronese` followed by the degree-`n` component of `twistRecognition`. -/
@[simp] theorem twistQuadruple_twisting_app {f : T ⟶ S}
    (hr : r ≫ (relativeProj A).toBase = f) (n : ℤ) :
    (twistQuadruple D d r hg hr).twisting.app n =
      D.psiLegVeronese r hr (d : ℤ) n ≫ (twistRecognition D d r hg).hom.app n := rfl

/-- **The class of the quadruple of the glued twists along `r` is classified by the
factorization of `r` through `U_d`.** -/
theorem homDegreeOpen_twistQuadruple (hd : 0 < d) {f : T ⟶ S}
    (hr : r ≫ (relativeProj A).toBase = f)
    (r' : T ⟶ ((relativeProj A).degreeOpen d).toScheme)
    (hr' : r' ≫ ((relativeProj A).degreeOpen d).ι = r) :
    Fd.homDegreeOpen A (relativeProj A) hd (Fd.mk f (twistQuadruple D d r hg hr)) = r' := by
  subst hr
  refine (Fd.eq_homDegreeOpen A (relativeProj A) hd _ r' fun U hU η hη => ?_).symm
  obtain ⟨g', q⟩ := η
  have hfst : g' ≫ U.ι = ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι ≫ r ≫
      (relativeProj A).toBase :=
    congrArg Sigma.fst hη
  obtain rfl : g' = chartBase U r :=
    (cancel_mono U.ι).mp (hfst.trans (chartBase_ι U r).symm)
  have hq := Quadruple.eq_mk_congrBaseStrict_of_heq (chartBase_ι U r).symm
    ((twistQuadruple D d r hg rfl).pullback ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι) _
    (Fd.heq_snd hη)
  have hηeq := (Fd.chartClass_chartClassInv A U ⟨chartBase U r, q⟩).symm.trans
    (congrArg (Fd.chartClass A U (chartBase U r)) hq)
  change ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι ≫ r' ≫ ((relativeProj A).degreeOpen d).ι =
    Fd.chartHom A U (relativeProj A) hU hd ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).toScheme
      ⟨chartBase U r, q⟩
  rw [hηeq, Fd.chartClass_mk, Fd.chartHom_eq_toProj_comp_chart]
  obtain ⟨ψ, hψ⟩ := exists_veroneseSections_restrict A U
    ((pullbackFunctor (ringedSpaceHom ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι)).obj
      (twistLine D d r)) U.ι_image_top
    (veroneseSections (chartTwisting A U (chartBase U r) (chartTwistingOf D d U r hg)))
  have key := Fd.toProj_chartEquiv_mk A U hU hd (chartBase U r)
    (((Quadruple.congrBaseStrict (chartBase_ι U r).symm ((twistQuadruple D d r hg rfl).pullback
      ((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι)).baseChangeDown U.ι (chartBase U r)
        (situationAlgebra A) (d : ℤ)).algebraTransport
      (unitalHomInverse (restrictPullbackUnitalHom A U.ι)
        (isIso_restrictPullbackUnitalHom_app_forall A U.ι))
      (isIso_unitalHomInverse_app (restrictPullbackUnitalHom A U.ι)
        (isIso_restrictPullbackUnitalHom_app_forall A U.ι))) rfl ψ hψ
    (iSup_nonvanishingOpen_chartTwistingOf D d U hU r hg ψ hψ)
  refine Eq.trans ?_ (congrArg (· ≫ (relativeProj A).chart U hU) key).symm
  refine Eq.trans ?_ (congrArg (fun φ => toProj (A.grading U) φ ≫ (relativeProj A).chart U hU)
    (classifyingHom_chartTwistingOf D d U hU r hg hd ψ hψ)).symm
  refine Eq.trans ?_ (chartLift_fac D d U hU r hg).symm
  exact congrArg (((r ≫ (relativeProj A).toBase) ⁻¹ᵁ U).ι ≫ ·) hr'

end Stacks.AlgebraicGeometry.RelativeProjTwistChartBridge

end
