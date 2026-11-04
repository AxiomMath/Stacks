module

public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPushforwardAffineSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealSheafDataFromCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineOverlaps
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Coverings
public import StacksFrontier.RingTheory.Descent.FaithfullyFlatModules

/-!
# The product of a sheaf of ideals with a module is objectwise on an affine chart

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, let `I ⊆ 𝒪_X` be
a sheaf of ideals on its small étale site and let `M` be an `𝒪_X`-module.  The product `I · M` of
`Stacks.Sites.idealSmul` is the smallest submodule of `M` with local membership containing the
objectwise product `I(U) · M(U)`, so a section of it is only *locally* a sum of products.  **Over
an affine étale chart it is nevertheless already the objectwise product**, as soon as `I` and `M`
are cartesian on affine charts — equivalently, by Descent, Proposition 03DX (2), quasi-coherent.

This is the small-étale twin of the scheme-level `Stacks.Algebraization.mem_submodule_of_affine`,
and unlike it, it is a descent statement: a covering sieve of a chart of an algebraic space is not
refined by opens of the chart, so there is no basis argument and faithful flatness of the product
of the rings of a covering family has to do the work.

## Main results

* `Submodule.mem_of_forall_mem_span_image_of_bijective_liftBaseChange`: **faithfully flat descent
  of membership in a submodule.**  Let `C` be a commutative ring, let `Dᵢ` be a finite family of
  `C`-algebras whose product is faithfully flat over `C`, and let `Mᵢ` be `Dᵢ`-modules presented
  as base changes of a `C`-module `M`.  A section of `M` whose image in each `Mᵢ` lies in the
  `Dᵢ`-span of the image of a submodule `N` lies in `N`.
* `AlgebraicGeometry.Space.mem_span_image_restrict_of_mem_presheafIdealSmul`: over the smaller of
  two affine charts the objectwise product is spanned by the restrictions of the objectwise
  product over the larger one.
* `AlgebraicGeometry.Space.mem_presheafIdealSmul_of_mem_idealSmul_of_isAffine` and
  `AlgebraicGeometry.Space.mem_idealSmul_iff_mem_presheafIdealSmul_of_isAffine`: **the product
  `I · M` is objectwise over an affine chart**, for `I` and `M` cartesian on affine charts.
* `AlgebraicGeometry.Space.mem_presheafIdealSmul_of_mem_idealSmul_of_isQuasicoherentOnSite`: the
  same for a quasi-coherent sheaf of ideals and a quasi-coherent module.
* `AlgebraicGeometry.Space.faithfullyFlat_pi_chartSectionsRing_of_ofArrows_mem_etalePrecoverage`:
  the product of the rings of a finite étale covering family of an affine chart by affine charts
  is faithfully flat over the ring of the chart covered.

## Implementation notes

The descent lemma is stated for a finite family of algebras rather than for a single faithfully
flat algebra, because that is the shape a covering family of an affine chart comes in; the proof
splits the unit of the product into the units of the factors, exactly as
`Ideal.eq_of_le_of_forall_map_le`
(`StacksFrontier/AlgebraicGeometry/Spaces/ClosedSubspaceFromQuasicoherentIdeal.lean`) does for a pair
of nested ideals.  That lemma is the case of a submodule of the structure sheaf; the one here
needs the base change presentation of the sections because the ambient module is arbitrary, and
that is what `Module.Descent.mem_range_of_one_tmul_mem_range` supplies.

The ring of sections of the structure sheaf over a chart carries two definitionally equal
spellings, `AlgebraicGeometry.Space.chartRing` and `AlgebraicGeometry.Space.chartSectionsRing`;
instance search is syntactic and does not pass between them, and the sections of a sheaf of
modules indexed over `AlgebraicGeometry.Space.smallEtaleRingSheaf` are a module over the second.
The base change comparison `AlgebraicGeometry.Space.sectionsBaseChange` and the ideal comparison
`AlgebraicGeometry.Space.chartIdeal_map_of_isCartesianOnAffineCharts` are stated over the first,
so each is restated here over the second —
`AlgebraicGeometry.Space.bijective_liftBaseChange_chartSectionsRestrictLinear` and
`AlgebraicGeometry.Space.chartSectionsIdeal_le_map_of_isCartesianOnAffineCharts` — with the
existing declaration as the proof.  The same obstruction is recorded on
`AlgebraicGeometry.Space.chartSectionsRing` and on `AlgebraicGeometry.Space.chartIdeal`.

`AlgebraicGeometry.Space.chartSectionsRestrictFun` exists because the restriction map of a
presheaf of modules lands in the restriction of scalars of the sections over the smaller chart,
which has the same carrier but a different spelling: a span taken over the image of the raw
restriction map is a submodule of that restriction of scalars, and rewriting inside a membership
in it is not type-correct at the transparency `rw` builds its motive at.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0GF8](https://stacks.math.columbia.edu/tag/0GF8)
-/

@[expose] public section

open CategoryTheory Opposite TensorProduct

universe m v u

/-- **Faithfully flat descent of membership in a submodule.** -/
theorem Submodule.mem_of_forall_mem_span_image_of_bijective_liftBaseChange
    {C : Type u} [CommRing C] {ι : Type v} [Finite ι]
    {D : ι → Type u} [∀ i, CommRing (D i)] [∀ i, Algebra C (D i)]
    [Module.FaithfullyFlat C (∀ i, D i)]
    {M : Type*} [AddCommGroup M] [Module C M]
    {Mi : ι → Type*} [∀ i, AddCommGroup (Mi i)] [∀ i, Module C (Mi i)]
    [∀ i, Module (D i) (Mi i)] [∀ i, IsScalarTower C (D i) (Mi i)]
    (ρ : ∀ i, M →ₗ[C] Mi i) (hρ : ∀ i, Function.Bijective ((ρ i).liftBaseChange (D i)))
    {N : Submodule C M} {x : M}
    (h : ∀ i, ρ i x ∈ Submodule.span (D i) (ρ i '' N)) :
    x ∈ N := by
  classical
  have _ := Fintype.ofFinite ι
  have step1 : ∀ i, (1 : D i) ⊗ₜ[C] x ∈
      LinearMap.range (LinearMap.lTensor (D i) N.subtype) := by
    intro i
    set ψ := (ρ i).liftBaseChange (D i) with hψ
    set L : Submodule (D i) ((D i) ⊗[C] M) :=
      LinearMap.range (N.subtype.baseChange (D i)) with hL
    have hgen : Submodule.span (D i) (ρ i '' N) ≤ Submodule.map ψ L := by
      refine Submodule.span_le.2 ?_
      rintro w ⟨y, hy, rfl⟩
      refine ⟨(1 : D i) ⊗ₜ[C] y, ⟨(1 : D i) ⊗ₜ[C] (⟨y, hy⟩ : N), ?_⟩, ?_⟩
      · simp
      · simp [hψ]
    obtain ⟨t, htL, hteq⟩ := hgen (h i)
    have hone : ψ ((1 : D i) ⊗ₜ[C] x) = ρ i x := by simp [hψ]
    rw [(hρ i).1 (hone.trans hteq.symm)]
    rw [hL] at htL
    obtain ⟨s, hs⟩ := htL
    exact ⟨s, by
      rw [← hs]
      exact (congrFun (LinearMap.baseChange_eq_ltensor (A := D i) N.subtype) s).symm⟩
  have step2 : (1 : ∀ i, D i) ⊗ₜ[C] x ∈
      LinearMap.range (LinearMap.lTensor (∀ i, D i) N.subtype) := by
    have h1 : (1 : ∀ i, D i) = ∑ i, Pi.single i (1 : D i) := by
      rw [← Finset.univ_sum_single (1 : ∀ i, D i)]
      rfl
    rw [h1, TensorProduct.sum_tmul]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨t, ht⟩ := step1 i
    refine ⟨LinearMap.rTensor (↥N) (LinearMap.single C D i) t, ?_⟩
    have e1 : LinearMap.lTensor (∀ i, D i) N.subtype
        (LinearMap.rTensor (↥N) (LinearMap.single C D i) t) =
          LinearMap.rTensor M (LinearMap.single C D i)
            (LinearMap.lTensor (D i) N.subtype t) := by
      rw [← LinearMap.comp_apply, ← LinearMap.comp_apply,
        LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]
    rw [e1, ht]
    simp
  simpa only [Submodule.range_subtype] using
    Module.Descent.mem_range_of_one_tmul_mem_range C (∀ i, D i) N.subtype step2

namespace AlgebraicGeometry.Space

noncomputable section

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (X : AlgebraicSpaces B S hS)

/-- Restriction of regular functions along a chart morphism. -/
abbrev chartSectionsRestrict {U V : SmallEtale B S hS X.1} (mm : V ⟶ U) :
    chartSectionsRing B S hS X U →+* chartSectionsRing B S hS X V :=
  ((smallEtaleRingSheaf B S hS X.1 X.2).obj.map mm.op).hom

/-- Restriction of sections of an `𝒪_X`-module along a chart morphism, as a plain function.

The restriction map of a presheaf of modules lands in the restriction of scalars of the sections
over the smaller chart, which has the same carrier; this is that map with its codomain spelled
as the sections themselves. -/
abbrev chartSectionsRestrictFun
    (M : SheafOfModules.{m} (smallEtaleRingSheaf B S hS X.1 X.2))
    {U V : SmallEtale B S hS X.1} (mm : V ⟶ U) :
    M.val.obj (op U) → M.val.obj (op V) := fun v => M.val.map mm.op v

/-- The algebra structure given by restriction along a chart morphism. -/
@[instance_reducible]
def chartSectionsRestrictAlgebra {U V : SmallEtale B S hS X.1} (mm : V ⟶ U) :
    Algebra (chartSectionsRing B S hS X U) (chartSectionsRing B S hS X V) :=
  (chartSectionsRestrict B S hS X mm).toAlgebra

/-- The `𝒪_X(U)`-module structure on the sections over a smaller chart. -/
@[instance_reducible]
def chartSectionsRestrictModule (M : SheafOfModules.{m} (smallEtaleRingSheaf B S hS X.1 X.2))
    {U V : SmallEtale B S hS X.1} (mm : V ⟶ U) :
    Module (chartSectionsRing B S hS X U) (M.val.obj (op V)) :=
  Module.compHom _ (chartSectionsRestrict B S hS X mm)

/-- Restriction of sections along a chart morphism, as an `𝒪_X(U)`-linear map. -/
def chartSectionsRestrictLinear (M : SheafOfModules.{m} (smallEtaleRingSheaf B S hS X.1 X.2))
    {U V : SmallEtale B S hS X.1} (mm : V ⟶ U) :
    letI := chartSectionsRestrictModule B S hS X M mm
    M.val.obj (op U) →ₗ[chartSectionsRing B S hS X U] M.val.obj (op V) :=
  (M.val.map mm.op).hom

/-- `AlgebraicGeometry.Space.chartSections_isScalarTower` in the spelling of
`AlgebraicGeometry.Space.chartSectionsRing`. -/
theorem chartSectionsRestrict_isScalarTower
    (M : SheafOfModules.{m} (smallEtaleRingSheaf B S hS X.1 X.2))
    {U V : SmallEtale B S hS X.1} (mm : V ⟶ U) :
    letI := chartSectionsRestrictAlgebra B S hS X mm
    letI := chartSectionsRestrictModule B S hS X M mm
    IsScalarTower (chartSectionsRing B S hS X U) (chartSectionsRing B S hS X V)
      (M.val.obj (op V)) :=
  chartSections_isScalarTower (hF := X.2) M mm

/-- **A module cartesian on affine charts has, over a morphism of affine charts, a bijective
base change comparison**, in the spelling of `AlgebraicGeometry.Space.chartSectionsRing`. -/
theorem bijective_liftBaseChange_chartSectionsRestrictLinear
    (M : SheafOfModules.{m} (smallEtaleRingSheaf B S hS X.1 X.2))
    (hM : IsCartesianOnAffineCharts (hF := X.2) M) {U V : SmallEtale B S hS X.1}
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj U))
    (hV : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj V))
    (mm : V ⟶ U) :
    letI := chartSectionsRestrictAlgebra B S hS X mm
    letI := chartSectionsRestrictModule B S hS X M mm
    haveI := chartSectionsRestrict_isScalarTower B S hS X M mm
    Function.Bijective ((chartSectionsRestrictLinear B S hS X M mm).liftBaseChange
      (chartSectionsRing B S hS X V)) :=
  hM U V hU hV mm

/-- **For a sheaf of ideals cartesian on affine charts, the ideal of sections over the smaller of
two affine charts is generated by the restrictions of the sections over the larger one**, in the
spelling of `AlgebraicGeometry.Space.chartSectionsRing`. -/
theorem chartSectionsIdeal_le_map_of_isCartesianOnAffineCharts
    (I : (SheafOfModules.unit (smallEtaleRingSheaf B S hS X.1 X.2)).Submodule)
    (hI : IsCartesianOnAffineCharts (hF := X.2) I.toSheafOfModules)
    {U V : SmallEtale B S hS X.1}
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj U))
    (hV : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj V))
    (mm : V ⟶ U) :
    chartSectionsIdeal B S hS X I V ≤
      Ideal.map (chartSectionsRestrict B S hS X mm) (chartSectionsIdeal B S hS X I U) :=
  le_of_eq (chartIdeal_map_of_isCartesianOnAffineCharts B S hS X I hI hU hV mm).symm

/-- Every section over a chart lies in the span of the restrictions of the sections over a larger
affine chart, as soon as the module is cartesian on affine charts. -/
theorem mem_span_range_restrict_of_isCartesianOnAffineCharts
    (M : SheafOfModules.{m} (smallEtaleRingSheaf B S hS X.1 X.2))
    (hM : IsCartesianOnAffineCharts (hF := X.2) M) {U V : SmallEtale B S hS X.1}
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj U))
    (hV : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj V))
    (mm : V ⟶ U) (w : M.val.obj (op V)) :
    w ∈ Submodule.span (chartSectionsRing B S hS X V)
      (Set.range (chartSectionsRestrictFun B S hS X M mm)) :=
  Submodule.eq_top_iff'.1 ((chartBaseChange_surjective_iff_span_eq_top M mm).1
    (hM U V hU hV mm).2) w

/-- **The objectwise product over the smaller of two affine charts is spanned by the restrictions
of the objectwise product over the larger one.**

A section of `I` over the smaller chart is a combination of restricted sections of `I` over the
larger one, a section of the module over the smaller chart is a combination of restricted
sections over the larger one, and the product of two restrictions is the restriction of the
product. -/
theorem mem_span_image_restrict_of_mem_presheafIdealSmul
    (I : (SheafOfModules.unit (smallEtaleRingSheaf B S hS X.1 X.2)).Submodule)
    (M : SheafOfModules.{m} (smallEtaleRingSheaf B S hS X.1 X.2))
    (hI : IsCartesianOnAffineCharts (hF := X.2) I.toSheafOfModules)
    (hM : IsCartesianOnAffineCharts (hF := X.2) M) {U V : SmallEtale B S hS X.1}
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj U))
    (hV : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj V))
    (mm : V ⟶ U) {y : M.val.obj (op V)}
    (hy : y ∈ (Stacks.Sites.presheafIdealSmul (O := structureSheaf B S hS X.1 X.2) I
      (⊤ : M.Submodule).toSubmodule).obj (op V)) :
    y ∈ Submodule.span (chartSectionsRing B S hS X V)
      (chartSectionsRestrictFun B S hS X M mm ''
        ((Stacks.Sites.presheafIdealSmul (O := structureSheaf B S hS X.1 X.2) I
          (⊤ : M.Submodule).toSubmodule).obj (op U) : Set (M.val.obj (op U)))) := by
  let P := Submodule.span (chartSectionsRing B S hS X V)
    (chartSectionsRestrictFun B S hS X M mm ''
      ((Stacks.Sites.presheafIdealSmul (O := structureSheaf B S hS X.1 X.2) I
        (⊤ : M.Submodule).toSubmodule).obj (op U) : Set (M.val.obj (op U))))
  have hQ : ∀ b : chartSectionsRing B S hS X U, b ∈ chartSectionsIdeal B S hS X I U →
      ∀ w : M.val.obj (op V), chartSectionsRestrict B S hS X mm b • w ∈ P := by
    intro b hb w
    have hw := mem_span_range_restrict_of_isCartesianOnAffineCharts B S hS X M hM hU hV mm w
    induction hw using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨v₀, rfl⟩ := hv
      have htop : v₀ ∈ (⊤ : M.Submodule).toSubmodule.obj (op U) := by
        rw [Stacks.SheafOfModules.toSubmodule_top]
        trivial
      have h1 : chartSectionsRestrictFun B S hS X M mm (b • v₀) ∈ P :=
        Submodule.subset_span ⟨b • v₀, Stacks.Sites.smul_mem_presheafIdealSmul I hb htop, rfl⟩
      rwa [show chartSectionsRestrictFun B S hS X M mm (b • v₀) =
        chartSectionsRestrict B S hS X mm b • chartSectionsRestrictFun B S hS X M mm v₀ from
          M.val.map_smul mm.op b v₀] at h1
    | zero =>
      rw [smul_zero]
      exact P.zero_mem
    | add _ _ _ _ h1 h2 =>
      rw [smul_add]
      exact P.add_mem h1 h2
    | smul c v _ h1 =>
      rw [smul_smul, mul_comm, ← smul_smul]
      exact P.smul_mem c h1
  let Q : Ideal (chartSectionsRing B S hS X V) :=
    { carrier := {d | ∀ v : M.val.obj (op V), d • v ∈ P}
      add_mem' := fun h1 h2 v => by rw [add_smul]; exact P.add_mem (h1 v) (h2 v)
      zero_mem' := fun v => by rw [zero_smul]; exact P.zero_mem
      smul_mem' := fun c d hd v => by
        rw [smul_eq_mul, mul_smul]
        exact P.smul_mem c (hd v) }
  have hmapQ : Ideal.map (chartSectionsRestrict B S hS X mm)
      (chartSectionsIdeal B S hS X I U) ≤ Q :=
    Ideal.map_le_iff_le_comap.2 fun b hb => hQ b hb
  refine Submodule.span_le.2 ?_ hy
  rintro t ⟨a, ha, w, -, rfl⟩
  exact hmapQ
    (chartSectionsIdeal_le_map_of_isCartesianOnAffineCharts B S hS X I hI hU hV mm ha) w

/-- **The product of the rings of regular functions on the members of a finite étale covering
family of an affine chart by affine charts is faithfully flat over the ring of the chart
covered**, in the spelling of `AlgebraicGeometry.Space.chartSectionsRing`.

This is
`AlgebraicGeometry.Space.SmallEtale.faithfullyFlat_pi_gamma_of_ofArrows_mem_fppfPrecoverage`
at the slice over the chart, with the étale covering family read as an fppf one. -/
theorem faithfullyFlat_pi_chartSectionsRing_of_ofArrows_mem_etalePrecoverage
    {U : SmallEtale B S hS X.1} {ι : Type*} [Finite ι]
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS X.1).obj U)))
    (z : ι → SmallEtale B S hS X.1) (φ : ∀ i, z i ⟶ U)
    (hzaff : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS X.1).obj (z i))))
    (hzet : Presieve.ofArrows
        (fun i ↦ (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj (z i)))
        (fun i ↦ (BigFppfOver.toScheme B S hS).map
          ((SmallEtale.toOver B S hS X.1).map (φ i))) ∈
      Scheme.etalePrecoverage
        ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj U))) :
    letI : ∀ i, Algebra (chartSectionsRing B S hS X U) (chartSectionsRing B S hS X (z i)) :=
      fun i ↦ chartSectionsRestrictAlgebra B S hS X (φ i)
    Module.FaithfullyFlat (chartSectionsRing B S hS X U)
      (∀ i, chartSectionsRing B S hS X (z i)) := by
  let algΓ : ∀ i, Algebra Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS X.1).obj (Over.mk (𝟙 U) : Over U).left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS X.1).obj (Over.mk (φ i) : Over U).left), ⊤) := fun i ↦
    ((BigFppfOver.toScheme B S hS).map
      ((SmallEtale.toOver B S hS X.1).map (φ i))).appTop.hom.toAlgebra
  exact SmallEtale.faithfullyFlat_pi_gamma_of_ofArrows_mem_fppfPrecoverage
    B S hS X.1 (fun i ↦ (Over.mk (φ i) : Over U))
    (fun i ↦ (Over.homMk (φ i) (by simp) : (Over.mk (φ i) : Over U) ⟶ Over.mk (𝟙 U)))
    hU hzaff (Scheme.etalePrecoverage_le_fppfPrecoverage _ hzet) fun _ ↦ rfl

/-- **The product of a sheaf of ideals with a module is objectwise over an affine chart.**  For a
sheaf of ideals `I ⊆ 𝒪_X` and an `𝒪_X`-module `M`, both cartesian on affine charts, a section of
`M` over an affine étale chart `U` which lies in `I · M` already lies in the objectwise product
`I(U) · M(U)`.

The converse inclusion is `Stacks.SheafOfModules.le_sheafifySubmodule` and needs nothing.

A section of `I · M` lies in the objectwise product along a covering sieve of `U`, which contains
a finite family of affine charts whose underlying schemes cover the underlying scheme of `U`
flatly, so that the product of their rings of functions is faithfully flat over the ring of `U`
(`AlgebraicGeometry.Space.faithfullyFlat_pi_chartSectionsRing_of_ofArrows_mem_etalePrecoverage`).
Over each member the objectwise product is spanned by the restrictions of the objectwise product
over `U` (`AlgebraicGeometry.Space.mem_span_image_restrict_of_mem_presheafIdealSmul`), and the
sections over each member are the base change of the sections over `U`, so
`Submodule.mem_of_forall_mem_span_image_of_bijective_liftBaseChange` descends the membership. -/
theorem mem_presheafIdealSmul_of_mem_idealSmul_of_isAffine
    (I : (SheafOfModules.unit (smallEtaleRingSheaf B S hS X.1 X.2)).Submodule)
    (M : SheafOfModules.{u} (smallEtaleRingSheaf B S hS X.1 X.2))
    (hI : IsCartesianOnAffineCharts (hF := X.2) I.toSheafOfModules)
    (hM : IsCartesianOnAffineCharts (hF := X.2) M) (U : SmallEtale B S hS X.1)
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj U))
    {x : M.val.obj (op U)}
    (hx : x ∈ (Stacks.Sites.idealSmul (O := structureSheaf B S hS X.1 X.2) I
      (⊤ : M.Submodule)).obj (op U)) :
    x ∈ (Stacks.Sites.presheafIdealSmul (O := structureSheaf B S hS X.1 X.2) I
      (⊤ : M.Submodule).toSubmodule).obj (op U) := by
  obtain ⟨T, hT, hmem⟩ := (Stacks.Sites.mem_idealSmul_iff
    (O := structureSheaf B S hS X.1 X.2) (M := M) (I := I) (N := (⊤ : M.Submodule))
    (Z := op U) (x := x)).1 hx
  obtain ⟨_, z, φ, hzaff, hzT, -, hzet⟩ :=
    SmallEtale.exists_finite_affine_etale_ofArrows_le B S hS X.1 hU hT
  let algz : ∀ i, Algebra (chartSectionsRing B S hS X U) (chartSectionsRing B S hS X (z i)) :=
    fun i ↦ chartSectionsRestrictAlgebra B S hS X (φ i)
  let modz : ∀ i, Module (chartSectionsRing B S hS X U) (M.val.obj (op (z i))) :=
    fun i ↦ chartSectionsRestrictModule B S hS X M (φ i)
  have towz : ∀ i, IsScalarTower (chartSectionsRing B S hS X U)
      (chartSectionsRing B S hS X (z i)) (M.val.obj (op (z i))) :=
    fun i ↦ chartSectionsRestrict_isScalarTower B S hS X M (φ i)
  have hff := faithfullyFlat_pi_chartSectionsRing_of_ofArrows_mem_etalePrecoverage
    B S hS X hU z φ hzaff hzet
  exact Submodule.mem_of_forall_mem_span_image_of_bijective_liftBaseChange
    (fun i ↦ chartSectionsRestrictLinear B S hS X M (φ i))
    (fun i ↦ bijective_liftBaseChange_chartSectionsRestrictLinear B S hS X M hM hU
      (hzaff i) (φ i))
    fun i ↦ mem_span_image_restrict_of_mem_presheafIdealSmul B S hS X I M hI hM hU (hzaff i)
      (φ i) (hmem (φ i) (hzT i))

/-- **Membership in the product of a sheaf of ideals with a module is objectwise over an affine
chart**, for a sheaf of ideals and a module cartesian on affine charts. -/
theorem mem_idealSmul_iff_mem_presheafIdealSmul_of_isAffine
    (I : (SheafOfModules.unit (smallEtaleRingSheaf B S hS X.1 X.2)).Submodule)
    (M : SheafOfModules.{u} (smallEtaleRingSheaf B S hS X.1 X.2))
    (hI : IsCartesianOnAffineCharts (hF := X.2) I.toSheafOfModules)
    (hM : IsCartesianOnAffineCharts (hF := X.2) M) (U : SmallEtale B S hS X.1)
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj U))
    (x : M.val.obj (op U)) :
    x ∈ (Stacks.Sites.idealSmul (O := structureSheaf B S hS X.1 X.2) I
        (⊤ : M.Submodule)).obj (op U) ↔
      x ∈ (Stacks.Sites.presheafIdealSmul (O := structureSheaf B S hS X.1 X.2) I
        (⊤ : M.Submodule).toSubmodule).obj (op U) :=
  ⟨mem_presheafIdealSmul_of_mem_idealSmul_of_isAffine B S hS X I M hI hM U hU,
    fun hx => Stacks.SheafOfModules.le_sheafifySubmodule _ (op U) hx⟩

/-- **The product of a quasi-coherent sheaf of ideals with a quasi-coherent module is objectwise
over an affine chart.**

Quasi-coherence gives cartesianness on affine charts by the forward implication of Descent,
Proposition 03DX (2) — `AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isQuasicoherentOnSite`
— which is unconditional. -/
theorem mem_presheafIdealSmul_of_mem_idealSmul_of_isQuasicoherentOnSite
    (I : (SheafOfModules.unit (smallEtaleRingSheaf B S hS X.1 X.2)).Submodule)
    (M : SheafOfModules.{u} (smallEtaleRingSheaf B S hS X.1 X.2))
    (hI : I.toSheafOfModules.IsQuasicoherentOnSite) (hM : M.IsQuasicoherentOnSite)
    (U : SmallEtale B S hS X.1)
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj U))
    {x : M.val.obj (op U)}
    (hx : x ∈ (Stacks.Sites.idealSmul (O := structureSheaf B S hS X.1 X.2) I
      (⊤ : M.Submodule)).obj (op U)) :
    x ∈ (Stacks.Sites.presheafIdealSmul (O := structureSheaf B S hS X.1 X.2) I
      (⊤ : M.Submodule).toSubmodule).obj (op U) :=
  mem_presheafIdealSmul_of_mem_idealSmul_of_isAffine B S hS X I M
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X.1 X.2 I.toSheafOfModules hI)
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X.1 X.2 M hM) U hU hx

end

end AlgebraicGeometry.Space
