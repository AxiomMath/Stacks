module

public import StacksFrontier.AlgebraicGeometry.OpensCoverHom
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartClassComap
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartClassInverse

/-!
# The chart-wise morphisms of two affine opens of the base agree

Let `S` be a scheme, `𝒜` a quasi-coherent graded `𝒪_S`-algebra (Situation 01NN), `d ≥ 1` and `X`
a relative homogeneous spectrum of `𝒜` ([Stacks, Tag 01NQ]). For an affine open `U` of the base,
`...RelativeProjQcohSheaf.Fd.chartHom` of
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartFdRepresentation` attaches to a point of
`F_d(T)` for the restriction `𝒜|_U` a morphism `T ⟶ X`, by [Stacks, Tag 01NU] over the affine base
`U` followed by the chart of `U`. Gluing those morphisms into one morphism out of a test scheme —
the forward half of residue (i) of [Stacks, Tag 01NY] — needs them to **agree** where two charts
both see a point, and that is what this file proves, for two *arbitrary* affine opens of the base.

## What was missing, and what the refinement is

The change of chart `...RelativeProjQcohSheaf.Fd.toProj_chartEquiv_comp_projInclusionMap` of
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartClassifyingTransport` holds for a
**nested** pair `Z ≤ U` of affine opens and carries two hypotheses: that the Veronese families of
the two chart-wise quadruples are related by
`...ProjChartGradedClassifying.comapVeronese` along the restriction `𝒜(U) → 𝒜(Z)`, and the
generation condition for the family at `U`. The first is discharged by
`...RelativeProjQcohSheaf.heq_comapVeronese_chartTwisting` of
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartClassComap`. The second was not: the
quadruple at `U` carries its generation condition over the grading of the *global* sections of
`𝒜|_U`, and the change of chart asks for it over `𝒜(U)`. The transport is
`iSup_nonvanishingOpen_psiSection_restrict_heq` below, in the discipline of
`...RelativeProjQcohSheaf.veroneseSections_toFun_heq`: every instance an argument, the two
`GradedRing` instances identified by `AlgebraicGeometry.Proj.gradedRing_eq` and never by defeq.

Two arbitrary affine opens `U`, `V` are then handled by refining the overlap. The morphism
`g : T ⟶ S` a chart-wise class records factors through `U` and through `V`, so it carries every
point of `T` into `U ⊓ V`; `AlgebraicGeometry.Scheme.isBasis_affineOpens` supplies an affine open
`Z` of `S` with `g(x) ∈ Z ≤ U ⊓ V`, and over the member `g⁻¹(Z)` of the resulting covering of `T`
the nested agreement applies twice, through `Z ≤ U` and `Z ≤ V`.

## No transports in the statements

Both agreement statements are phrased with `...RelativeProjQcohSheaf.Fd.chartClassInv` of
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartClassInverse`: two chart-wise classes
are compared by asking that they have the same image under it, i.e. that they are chart-wise
classes of **one** point of `F_d(T)` for `𝒜`. That is an equation between elements of one type,
where saying "the chart-wise classes of one class at two opens" directly would need a transport
along `g_U ≫ U.ι = g_V ≫ V.ι` — an equality of two *terms*, neither a variable, which `subst`
cannot remove. Inside the proofs the transport appears exactly once, as
`Quadruple.congrBaseStrict`, which differs from the existing
`...RelativeProjQcohSheaf.Quadruple.congrBase` by being fieldwise: its invertible module and its
map are `P.L` and `Twisting.congrBase h P.twisting` *definitionally*, which is what keeps the
change of chart's two equations `P.L = L` from carrying a transport into every later
heterogeneous comparison.

## Main results

* `...RelativeProjQcohSheaf.iSup_nonvanishingOpen_psiSection_heq` and
  `...iSup_nonvanishingOpen_psiSection_restrict_heq`: **the generation condition of
  [Stacks, Tag 01N8] transported along an identification of the graded ring.**
* `...RelativeProjQcohSheaf.Fd.toProj_chartEquiv_chartClass_comp_projInclusionMap`: **the change
  of chart for a nested pair of affine opens, with every hypothesis discharged.**
* `...RelativeProjQcohSheaf.Fd.chartHom_eq_of_le`: the same, read as an equality of morphisms into
  a relative homogeneous spectrum.
* `...RelativeProjQcohSheaf.Fd.chartHom_eq_of_chartClassInv_eq`: **the chart-wise morphisms of two
  arbitrary affine opens of the base agree.**

## What this is not

This is the **compatibility** the gluing of the chart-wise morphisms consumes, and it is not
residue (i) of [Stacks, Tag 01NY]: nothing here constructs the bijection `F_d(W) ≃ Mor(W, U_d)`.
Its **forward** map is glued out of these morphisms in
`StacksFrontier/AlgebraicGeometry/RelativeProjQcohSheaf/ChartGlue.lean`, as
`...RelativeProjQcohSheaf.Fd.existsUnique_hom_degreeOpen`, together with its naturality in the
test scheme. Its **inverse** needs, besides the unconditional amalgamation
`...RelativeProjQcohSheaf.Fd.exists_amalgamation_opens`, the **converse** of the agreement proved
here — that two chart-wise classes with the same morphism into `X` have the same image under
`Fd.chartClassInv`. That converse is `...RelativeProjQcohSheaf.Fd.chartClassInv_eq_of_chartHom_eq`
of `StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartConverse`, which carries the clause
that the two chart-wise classes record the same morphism to `S`; the compatibility `equiv_scale`
of `...RelativeProjQcohSheaf.ProjDegreeRepresentation` with the transitions `F_d → F_{ad}` is
untouched by this file, its chart-wise Veronese computation being
`...RelativeProjQcohSheaf.Fd.chartHom_scale` of
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartScale`.

## References

* [Stacks Project, Tag 01NY](https://stacks.math.columbia.edu/tag/01NY)
* [Stacks Project, Tag 01NU](https://stacks.math.columbia.edu/tag/01NU)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry Stacks.RingedSpace
open AlgebraicGeometry.Proj (degreeOpen)
open Stacks.AlgebraicGeometry.MorphismsIntoProj
open Stacks.AlgebraicGeometry.MorphismToProjUniversal
open Stacks.AlgebraicGeometry.ProjChartFromRatios
open Stacks.AlgebraicGeometry.ProjTripleClassifying
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.NonvanishingOpen (nonvanishingOpen)

universe u v w

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

/-! ### The generation condition transported along an identification of the graded ring -/

/-- **The generation condition of [Stacks, Tag 01N8] transported along an identification of the
graded ring.** The hypotheses are those of
`...RelativeProjQcohSheaf.veroneseSections_toFun_heq`: every datum of the two sides is a separate
argument, the `GradedRing` instance is explicit on each side and is never compared, the two being
identified by `AlgebraicGeometry.Proj.gradedRing_eq`. -/
theorem iSup_nonvanishingOpen_psiSection_heq {σ₁ σ₂ : Type w} {R₁ R₂ : Type u}
    [cr₁ : CommRing R₁] [cr₂ : CommRing R₂] [sl₁ : SetLike σ₁ R₁] [sl₂ : SetLike σ₂ R₂]
    [asc₁ : AddSubgroupClass σ₁ R₁] [asc₂ : AddSubgroupClass σ₂ R₂]
    (𝒜 : ℕ → σ₁) (ℬ : ℕ → σ₂) (i : GradedRing 𝒜) (j : GradedRing ℬ)
    (hR : R₁ = R₂) (hσ : σ₁ = σ₂) (hcr : HEq cr₁ cr₂) (hsl : HEq sl₁ sl₂) (h𝒜 : HEq 𝒜 ℬ)
    {d : ℕ} {Y : Scheme.{u}} {L : Y.Modules} [Stacks.Ample.IsInvertibleModule Y L]
    (ψ : @VeroneseSections σ₁ R₁ cr₁ sl₁ asc₁ 𝒜 i d Y L)
    (ψ' : @VeroneseSections σ₂ R₂ cr₂ sl₂ asc₂ ℬ j d Y L) (hψ : HEq ψ ψ')
    (hgen : (⨆ g : 𝒜 d, nonvanishingOpen Y L (psiSection 𝒜 ψ g)) = ⊤) :
    (⨆ g : ℬ d, nonvanishingOpen Y L (psiSection ℬ ψ' g)) = ⊤ := by
  subst hR
  subst hσ
  obtain rfl := eq_of_heq hcr
  obtain rfl := eq_of_heq hsl
  obtain rfl := eq_of_heq h𝒜
  obtain rfl := AlgebraicGeometry.Proj.gradedRing_eq i j
  obtain rfl := eq_of_heq hψ
  exact hgen

section Restrict

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S) (U : S.Opens) {U' : S.Opens} {k : ℕ}
  {T : Scheme.{u}} (L : T.Modules) [Stacks.Ample.IsInvertibleModule T L]

/-- `iSup_nonvanishingOpen_psiSection_heq` at the two spellings of the grading of the global
sections of `A|_U`, in the shape `...RelativeProjQcohSheaf.exists_veroneseSections_restrict` has:
the open `U'` the second grading is read at is a variable given with the equality
`U.ι ''ᵁ ⊤ = U'`, which `subst` removes. -/
theorem iSup_nonvanishingOpen_psiSection_restrict_heq
    (hU' : U.ι ''ᵁ (⊤ : Opens U.toScheme.toRingedSpace.carrier) = U')
    (ψ : VeroneseSections ((A.restrict U.ι).grading (⊤ : U.toScheme.Opens)) k L)
    (ψ' : VeroneseSections (A.grading U') k L) (hψ : HEq ψ ψ')
    (hgen : (⨆ g : (A.restrict U.ι).grading (⊤ : U.toScheme.Opens) k,
      nonvanishingOpen T L
        (psiSection ((A.restrict U.ι).grading (⊤ : U.toScheme.Opens)) ψ g)) = ⊤) :
    (⨆ g : A.grading U' k, nonvanishingOpen T L (psiSection (A.grading U') ψ' g)) = ⊤ := by
  subst hU'
  exact iSup_nonvanishingOpen_psiSection_heq _ _ _ _
    (SheafGradedAlgebra.restrict_ι_sectionRing_image A U)
    (SheafGradedAlgebra.restrict_ι_addSubgroup_eq A U)
    (SheafGradedAlgebra.restrict_ι_commRing_heq A U)
    (SheafGradedAlgebra.restrict_ι_setLike_heq A U)
    (SheafGradedAlgebra.restrict_ι_grading_heq A U) ψ ψ' hψ hgen

end Restrict

/-! ### The transport of a quadruple along an equality of base morphisms, fieldwise -/

namespace Quadruple

variable {T S : Scheme.{u}}
  {B : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} {d : ℤ}

/-- **A quadruple read over an equal base morphism, transported fieldwise.** This agrees with
`...RelativeProjQcohSheaf.Quadruple.congrBase`, which is `h ▸ P`, but its invertible module is
`P.L` and its map is `...RelativeProjQcohSheaf.Twisting.congrBase h P.twisting` *by definition*
rather than up to a transport. That is the whole point of it: the change of chart consumes a
quadruple together with an equation `P.L = L` and a heterogeneous equality of Veronese families,
and with `congrBase` both would be equations proved by `subst`, which puts the transport inside
every later heterogeneous comparison. Here both are `rfl`. -/
def congrBaseStrict {g g' : T ⟶ S} (h : g = g') (P : Quadruple g B d) : Quadruple g' B d where
  L := P.L
  isInvertible := P.isInvertible
  twisting := Twisting.congrBase h P.twisting
  epi_app_one := by
    subst h
    exact P.epi_app_one

/-- The fieldwise transport does not change the invertible module, definitionally. -/
@[simp] theorem congrBaseStrict_L {g g' : T ⟶ S} (h : g = g') (P : Quadruple g B d) :
    (congrBaseStrict h P).L = P.L := rfl

/-- The map of the fieldwise transport is the transported map, definitionally. -/
@[simp] theorem congrBaseStrict_twisting {g g' : T ⟶ S} (h : g = g') (P : Quadruple g B d) :
    (congrBaseStrict h P).twisting = Twisting.congrBase h P.twisting := rfl

/-- Transporting along reflexivity changes nothing. -/
@[simp] theorem congrBaseStrict_rfl {g : T ⟶ S} (P : Quadruple g B d) :
    congrBaseStrict (rfl : g = g) P = P := rfl

/-- **A class of quadruples over one of two equal base morphisms, read over the other.** This is
the only shape in which the two chart-wise classes of one class of quadruples for `𝒜` on `S` can
be compared: the two factorizations `g_Z ≫ Z.ι` and `g_U ≫ U.ι` of one morphism `T ⟶ S` are
*equal* and not identical, so the two quotients are different types. -/
theorem eq_mk_congrBaseStrict_of_heq {g g' : T ⟶ S} (h : g = g') (P : Quadruple g B d)
    (q : Quotient (Quadruple.setoid g' B d))
    (hq : HEq q (Quotient.mk (Quadruple.setoid g B d) P)) :
    q = Quotient.mk (Quadruple.setoid g' B d) (congrBaseStrict h P) := by
  subst h
  rw [congrBaseStrict_rfl]
  exact eq_of_heq hq

end Quadruple

/-! ### The change of chart for a nested pair of affine opens, unconditionally -/

section Nested

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S) {Z : S.Opens} (U : S.Opens)

/-- **The change of chart for the chart-wise representation of `F_d`, with every hypothesis
discharged.** Let `Z ≤ U` be affine opens of the base, `T` a test scheme, `g_Z ≫ Z.ι = g_U ≫ U.ι`
two factorizations of one morphism `T ⟶ S` through them, and `P` a quadruple for `𝒜` over the
first. Then the chart-wise morphism of the chart-wise class of `P` at `Z`, followed by the
[Stacks, Tag 01NO] transition, is the chart-wise morphism of the chart-wise class of `P` at `U`.

This is `...RelativeProjQcohSheaf.Fd.toProj_chartEquiv_comp_projInclusionMap` with its hypothesis
`hψU` supplied by `...RelativeProjQcohSheaf.heq_comapVeronese_chartTwisting` and its generation
hypothesis `hgen` supplied by `...RelativeProjQcohSheaf.Quadruple`
`.iSup_nonvanishingOpen_psiSection_eq_top` of [Stacks, Tag 01NU] over the affine base `U`,
transported to the grading `𝒜(U)` by `iSup_nonvanishingOpen_psiSection_restrict_heq` above. No
hypothesis is left: the two chart-wise classes are those of **one** quadruple for `𝒜` on `S`, as
`Fd.chartClass` is built to produce, so nothing here restricts one chart's class to the other. -/
theorem Fd.toProj_chartEquiv_chartClass_comp_projInclusionMap (hZU : Z ≤ U)
    (hZ : IsAffineOpen Z) (hU : IsAffineOpen U) {k : ℕ} (hk : 0 < k) {T : Scheme.{u}}
    (gZ : T ⟶ Z.toScheme) (gU : T ⟶ U.toScheme) (hbase : gU ≫ U.ι = gZ ≫ Z.ι)
    (P : Quadruple (gZ ≫ Z.ι) (situationAlgebra A) (k : ℤ)) :
    toProj (A.grading Z)
          (Fd.chartEquiv A Z hZ hk T (Fd.chartClass A Z gZ (Quotient.mk _ P)))
        ≫ RelativeProj.projInclusionMap A Z U hZU hZ hU
      = toProj (A.grading U)
          (Fd.chartEquiv A U hU hk T
            (Fd.chartClass A U gU (Quotient.mk _ (Quadruple.congrBaseStrict hbase.symm P)))) := by
  have : IsAffine U.toScheme := hU
  set PU := Quadruple.congrBaseStrict hbase.symm P with hPU
  -- the chart-wise quadruples at the two opens
  rw [Fd.chartClass_mk A Z gZ P, Fd.chartClass_mk A U gU PU]
  set QZ := (P.baseChangeDown Z.ι gZ (situationAlgebra A) (k : ℤ)).algebraTransport
      (unitalHomInverse (restrictPullbackUnitalHom A Z.ι)
        (isIso_restrictPullbackUnitalHom_app_forall A Z.ι))
      (isIso_unitalHomInverse_app (restrictPullbackUnitalHom A Z.ι)
        (isIso_restrictPullbackUnitalHom_app_forall A Z.ι)) with hQZ
  set QU := (PU.baseChangeDown U.ι gU (situationAlgebra A) (k : ℤ)).algebraTransport
      (unitalHomInverse (restrictPullbackUnitalHom A U.ι)
        (isIso_restrictPullbackUnitalHom_app_forall A U.ι))
      (isIso_unitalHomInverse_app (restrictPullbackUnitalHom A U.ι)
        (isIso_restrictPullbackUnitalHom_app_forall A U.ι)) with hQU
  -- the Veronese family of the chart-wise class at `Z`, read at the grading `𝒜(Z)`
  obtain ⟨ψ, hψ⟩ := exists_veroneseSections_restrict A Z (L := P.L) Z.ι_image_top
    (veroneseSections QZ.twisting)
  -- the relation of the two Veronese families
  have hψU : HEq (veroneseSections QU.twisting)
      (ProjChartGradedClassifying.comapVeronese (A.res hZU) ψ) :=
    heq_comapVeronese_chartTwisting A gZ gU hZU hbase
      (Twisting.congrBase hbase.symm P.twisting) P.twisting
      (Twisting.heq_congrBase hbase.symm P.twisting) ψ hψ
  -- the generation condition at the grading `𝒜(U)`
  have hgen : (⨆ g : A.grading U k, nonvanishingOpen T P.L
      (psiSection (A.grading U)
        (ProjChartGradedClassifying.comapVeronese (A.res hZU) ψ) g)) = ⊤ :=
    iSup_nonvanishingOpen_psiSection_restrict_heq A U (L := P.L) U.ι_image_top
      (veroneseSections QU.twisting) _ hψU
      (Quadruple.iSup_nonvanishingOpen_psiSection_eq_top (B := A.restrict U.ι) (d := k)
        (fun n => (A.restrict U.ι).isQuasicoherent n) QU)
  exact Fd.toProj_chartEquiv_comp_projInclusionMap A U hZU hZ hU hk gZ QZ gU QU rfl rfl
    ψ hψ hψU hgen

/-! ### The same, in the transport-free spelling the descent consumes -/

/-- **Every point of `F_d(T)` for `𝒜` with a chosen factorization of its morphism through an open
`V` of the base is the chart-wise class of a class of quadruples for `𝒜`.** This is the
surjectivity of `...RelativeProjQcohSheaf.Fd.chartClassInv` onto the points whose morphism
factors, and it is how a chart-wise class is produced without naming a transport: the
factorization is given as an equation to a *variable* morphism, which `subst` removes. -/
theorem Fd.exists_chartClassInv_eq (V : S.Opens) {k : ℤ} {T : Scheme.{u}}
    (ξ : Fd (situationAlgebra A) k T) (gV : T ⟶ V.toScheme) (hgV : gV ≫ V.ι = ξ.1) :
    ∃ η : Fd (situationAlgebra (A.restrict V.ι)) k T, Fd.chartClassInv A V η = ξ := by
  obtain ⟨g, q⟩ := ξ
  subst hgV
  exact ⟨Fd.chartClass A V gV q, Fd.chartClassInv_chartClass A V gV q⟩

/-- The morphism into a relative homogeneous spectrum attached to a chart-wise class, written as
the absolute classifying morphism read into `Proj 𝒜(U)` followed by the chart of `U`. This is
`...RelativeProjQcohSheaf.Fd.chartHom_eq_comp` reassociated; the reassociation is a separate step
because `CategoryTheory.Category.assoc` in `Scheme` is `rfl` without being syntactically an
identity, so `rw` across it fails where `exact` against it succeeds. -/
theorem Fd.chartHom_eq_toProj_comp_chart (P : RelativeProjData A) (hU : IsAffineOpen U)
    {k : ℕ} (hk : 0 < k) (T : Scheme.{u})
    (ξ : Fd (situationAlgebra (A.restrict U.ι)) (k : ℤ) T) :
    Fd.chartHom A U P hU hk T ξ
      = toProj (A.grading U) (Fd.chartEquiv A U hU hk T ξ) ≫ P.chart U hU :=
  (Fd.chartHom_eq_comp A U P hU hk T ξ).trans (Category.assoc _ _ _).symm

/-- **The chart-wise morphisms of a nested pair of affine opens of the base agree**, in the
spelling that names no transport: two chart-wise classes which come from *one* point of `F_d(T)`
for `𝒜` — that is, which have the same image under
`...RelativeProjQcohSheaf.Fd.chartClassInv` — define the same morphism into a relative
homogeneous spectrum of `𝒜`.

This is `Fd.toProj_chartEquiv_chartClass_comp_projInclusionMap` composed with the chart of `U`,
where the [Stacks, Tag 01NO] transition is absorbed by the compatibility
`...RelativeProj.RelativeProjData.chart_transition` of the charts with the transitions. -/
theorem Fd.chartHom_eq_of_le (P : RelativeProjData A) (hZU : Z ≤ U)
    (hZ : IsAffineOpen Z) (hU : IsAffineOpen U) {k : ℕ} (hk : 0 < k) {T : Scheme.{u}}
    (ηZ : Fd (situationAlgebra (A.restrict Z.ι)) (k : ℤ) T)
    (ηU : Fd (situationAlgebra (A.restrict U.ι)) (k : ℤ) T)
    (h : Fd.chartClassInv A Z ηZ = Fd.chartClassInv A U ηU) :
    Fd.chartHom A Z P hZ hk T ηZ = Fd.chartHom A U P hU hk T ηU := by
  obtain ⟨gZ, qZ⟩ := ηZ
  obtain ⟨gU, qU⟩ := ηU
  have hbase : gU ≫ U.ι = gZ ≫ Z.ι := (congrArg Sigma.fst h).symm
  -- one quadruple for `𝒜` on `S`, over the factorization through `Z`
  obtain ⟨Pq, hPq⟩ := Quotient.exists_rep
    (show Quotient (Quadruple.setoid (gZ ≫ Z.ι) (situationAlgebra A) (k : ℤ)) from
      (Fd.chartClassInv A Z (⟨gZ, qZ⟩ : Fd (situationAlgebra (A.restrict Z.ι)) (k : ℤ) T)).2)
  have hZclass : (⟨gZ, qZ⟩ : Fd (situationAlgebra (A.restrict Z.ι)) (k : ℤ) T)
      = Fd.chartClass A Z gZ (Quotient.mk _ Pq) := by
    rw [hPq]
    exact (Fd.chartClass_chartClassInv A Z _).symm
  have hq2 : (show Quotient (Quadruple.setoid (gU ≫ U.ι) (situationAlgebra A) (k : ℤ)) from
        (Fd.chartClassInv A U (⟨gU, qU⟩ : Fd (situationAlgebra (A.restrict U.ι)) (k : ℤ) T)).2)
      = Quotient.mk _ (Quadruple.congrBaseStrict hbase.symm Pq) :=
    Quadruple.eq_mk_congrBaseStrict_of_heq hbase.symm Pq _
      ((Fd.heq_snd h).symm.trans (heq_of_eq hPq.symm))
  have hUclass : (⟨gU, qU⟩ : Fd (situationAlgebra (A.restrict U.ι)) (k : ℤ) T)
      = Fd.chartClass A U gU (Quotient.mk _ (Quadruple.congrBaseStrict hbase.symm Pq)) := by
    rw [← hq2]
    exact (Fd.chartClass_chartClassInv A U _).symm
  rw [hZclass, hUclass, Fd.chartHom_eq_toProj_comp_chart A Z P hZ hk T,
    Fd.chartHom_eq_toProj_comp_chart A U P hU hk T,
    ← P.chart_transition Z U hZU hZ hU]
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  exact congrArg (fun φ => φ ≫ P.chart U hU)
    (Fd.toProj_chartEquiv_chartClass_comp_projInclusionMap A U hZU hZ hU hk gZ gU hbase Pq)

/-! ### Two arbitrary affine opens of the base, refined -/

/-- **The chart-wise morphisms of two *arbitrary* affine opens of the base agree.** Let `U`, `V`
be affine opens of `S`, `T` a test scheme, and let `η_U ∈ F_d(T)` for `𝒜|_U` and
`η_V ∈ F_d(T)` for `𝒜|_V` be chart-wise classes of **one** point of `F_d(T)` for `𝒜` — that is,
let them have the same image under `...RelativeProjQcohSheaf.Fd.chartClassInv`. Then they define
the same morphism into a relative homogeneous spectrum of `𝒜`.

This is the chart agreement the descent of [Stacks, Tag 01NU] along the charts needs, and it is
`Fd.chartHom_eq_of_le` — which holds only for a **nested** pair — plus the refinement of the
overlap. The refinement is the content: the morphism `T ⟶ S` the two classes record factors
through `U` and through `V`, so every point of `T` is carried into `U ⊓ V`, and
`AlgebraicGeometry.Scheme.isBasis_affineOpens` produces an affine open `Z` of `S` with
`g(x) ∈ Z ≤ U ⊓ V`. Over the member `g⁻¹(Z)` of the resulting open covering of `T` both
restricted classes are the chart-wise classes at `U` and at `V` of one point of `F_d(g⁻¹(Z))`
whose morphism factors through `Z` (`Fd.exists_chartClassInv_eq`), and the nested agreement
applies twice, through `Z ≤ U` and `Z ≤ V`. The passage between `T` and `g⁻¹(Z)` is the
naturality of both sides in the test scheme —
`...RelativeProjQcohSheaf.Fd.chartHom_pullback` and
`...RelativeProjQcohSheaf.Fd.chartClassInv_pullback` — and the conclusion over `T` is
`AlgebraicGeometry.Scheme.hom_ext_of_forall`. -/
theorem Fd.chartHom_eq_of_chartClassInv_eq (P : RelativeProjData A) {V : S.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) {k : ℕ} (hk : 0 < k) {T : Scheme.{u}}
    (ηU : Fd (situationAlgebra (A.restrict U.ι)) (k : ℤ) T)
    (ηV : Fd (situationAlgebra (A.restrict V.ι)) (k : ℤ) T)
    (h : Fd.chartClassInv A U ηU = Fd.chartClassInv A V ηV) :
    Fd.chartHom A U P hU hk T ηU = Fd.chartHom A V P hV hk T ηV := by
  have hgU : (Fd.chartClassInv A U ηU).1 = ηU.1 ≫ U.ι := rfl
  have hgV : (Fd.chartClassInv A U ηU).1 = ηV.1 ≫ V.ι :=
    (congrArg Sigma.fst h).trans (Fd.chartClassInv_fst A V ηV)
  refine Scheme.hom_ext_of_forall _ _ fun x => ?_
  have hmem : (Fd.chartClassInv A U ηU).1.base x ∈ (U ⊓ V : S.Opens) := by
    refine ⟨?_, ?_⟩
    · rw [hgU, ← Scheme.Opens.range_ι U]
      exact ⟨ηU.1.base x, by simp⟩
    · rw [hgV, ← Scheme.Opens.range_ι V]
      exact ⟨ηV.1.base x, by simp⟩
  obtain ⟨_, ⟨Z, hZ, rfl⟩, hxZ, hZUV⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open hmem (U ⊓ V : S.Opens).isOpen
  have hZU : Z ≤ U := fun y hy => (hZUV hy).1
  have hZV : Z ≤ V := fun y hy => (hZUV hy).2
  refine ⟨(Fd.chartClassInv A U ηU).1 ⁻¹ᵁ Z, hxZ, ?_⟩
  set j := ((Fd.chartClassInv A U ηU).1 ⁻¹ᵁ Z).ι with hj
  obtain ⟨ηZ, hηZ⟩ := Fd.exists_chartClassInv_eq A Z
    (Fd.pullback j (Fd.chartClassInv A U ηU)) ((Fd.chartClassInv A U ηU).1 ∣_ Z)
    (by rw [Fd.pullback_fst]; exact morphismRestrict_ι _ Z)
  have hcU : Fd.chartClassInv A Z ηZ = Fd.chartClassInv A U (Fd.pullback j ηU) := by
    rw [hηZ, Fd.chartClassInv_pullback]
  have hcV : Fd.chartClassInv A Z ηZ = Fd.chartClassInv A V (Fd.pullback j ηV) := by
    rw [hηZ, Fd.chartClassInv_pullback]
    exact congrArg (Fd.pullback j) h
  refine Eq.trans (Fd.chartHom_pullback A U P hU hk j ηU).symm ?_
  refine Eq.trans (Fd.chartHom_eq_of_le A U P hZU hZ hU hk ηZ (Fd.pullback j ηU) hcU).symm ?_
  refine Eq.trans (Fd.chartHom_eq_of_le A V P hZV hZ hV hk ηZ (Fd.pullback j ηV) hcV) ?_
  exact Fd.chartHom_pullback A V P hV hk j ηV

end Nested

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
