module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.SchemeTheoretic
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionFromSite
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionReadingsFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealSheafDataFromCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeTheoreticSupport

/-!
# The scheme-theoretic support on an étale scheme chart, compared with the scheme-level one

Let `X` be an algebraic space over a scheme `S`, let `F` be a finite type quasi-coherent
`𝒪_X`-module and let `i : Z → X` be its scheme-theoretic support, Stacks 07U1.  Part (1) of
**Stacks 07U0** says that for a scheme `U` étale over `X` the fibre product `Z ×_X U` is the
scheme-theoretic support of the restriction of `F` to `U`, this last taken in the sense of
schemes — Stacks 05JV, `AlgebraicGeometry.Scheme.Modules.schemeTheoreticSupport`.  That is what
is proved here.

An étale scheme chart `A` of `X` *is* a scheme with an étale morphism to `X`, and the
restriction of `F` to it is `AlgebraicGeometry.Space.chartRestrictionSheaf`, whose sections over
a Zariski open `V` of the chart's scheme are the sections of `F` over the étale chart that `V`
cuts out.  Both sides of the claim are therefore ideals of `Γ(A, V)` for `V` affine, and both
are the annihilator of those sections:

* the scheme-level support is, by its definition, the annihilator of `Γ(F|_A, V)` over
  `Γ(A, V)`, and the comparison `AlgebraicGeometry.Scheme.Opens.topIso` carries the sections of
  `F` over the chart `V` cuts out onto `Γ(F|_A, V)` semilinearly and bijectively, so the two
  annihilators correspond;
* the ideal that `Z` cuts out on the chart is, by
  `AlgebraicGeometry.Space.exists_isClosedSubspace_schemeTheoreticSupport`, the annihilator
  ideal of `F` over that same chart, and on an affine chart that is the annihilator of the
  sections, by
  `AlgebraicGeometry.Space.chartIdeal_annihilatorIdealSheaf_eq_annihilator`.

## Main definitions

* `AlgebraicGeometry.Space.chartRestrictionSheafSectionsSemilinear` is the semilinear bijection
  identifying the sections of the chart restriction over a Zariski open with the sections of the
  module over the étale chart that open cuts out.

## Main results

* `AlgebraicGeometry.Space.annihilator_sections_chartRestrictionSheaf`: the annihilator of the
  former is the image of the annihilator ideal at the latter.
* `AlgebraicGeometry.Space.openChartIdeal_eq_map_chartOpens`: the two readings of a Zariski open
  of a chart as an étale chart give the same ideal.
* `AlgebraicGeometry.Space.schemeTheoreticSupport_chartRestrictionSheaf`: **Stacks 07U0,
  part (1)**, with the scheme-theoretic support of the restriction taken in the sense of schemes.

## Implementation notes

The inverse image of `Z` on the chart is
`AlgebraicGeometry.Space.idealSheafDataOfChart` at the defining ideal sheaf of `Z`.  That this
is the inverse image, and not merely a chartwise family of ideals, is
`AlgebraicGeometry.Space.comap_idealSheafDataOfChart`: those sheaves of ideals are compatible
with inverse image along every morphism of charts, which is the statement that they are pulled
back from `X`.  Its cartesianity hypothesis is discharged by
`AlgebraicGeometry.Space.definingIdealSheaf_isCartesianOnAffineCharts`, which is unconditional,
so it is supplied in the statement rather than assumed.

Quasi-coherence and finite type of the restriction are likewise supplied in the statement, by
`AlgebraicGeometry.Space.isQuasicoherent_chartRestrictionSheaf` and by the affine-sections
criterion of Stacks 01XZ at
`AlgebraicGeometry.Space.moduleFinite_sections_chartRestrictionSheaf`; the scheme-level
scheme-theoretic support takes them as instances, and they are what quasi-coherence and finite
type of `F` give.  Only one finite type hypothesis on `F` is asked for, the categorical
`SheafOfModules.IsFiniteTypeOnSite`; the sectionwise form of Stacks 03DL(5) that the
construction of the closed subspace needs is obtained from it by
`Stacks.SheafOfModules.presheaf_isFiniteType_of_isFiniteTypeOnSite`.

The restriction used is `AlgebraicGeometry.Space.chartRestrictionSheaf`, the restriction with no
sheafification, whose sections are the sections of `F` over the charts cut out by the Zariski
opens on the nose.  `AlgebraicGeometry.Space.restrictToChart` sheafifies that presheaf and is
isomorphic to it by `AlgebraicGeometry.Space.restrictToChartIsoChartRestrictionSheaf`.

The two readings of a Zariski open of a chart as an étale chart of `X` —
`AlgebraicGeometry.Space.chartOpens`, used by the restriction, and
`AlgebraicGeometry.Space.openChart`, used by the chartwise ideals — are equal but not
definitionally so, because `openChart` goes through `CategoryTheory.Functor.preimage`.  The
ideals they give are compared by transporting along that equality, which is what the private
`map_submodule_obj_eq_of_chart_eq` does; the rings of sections over the two charts *are*
definitionally equal, so the ring map needs no transport.

## References

* [Stacks Project, Lemma 67.15.3 (Tag 07U0)](https://stacks.math.columbia.edu/tag/07U0)
* [Stacks Project, Definition 67.15.4 (Tag 07U1)](https://stacks.math.columbia.edu/tag/07U1)
* [Stacks Project, Lemma 29.5.3 (Tag 05JU)](https://stacks.math.columbia.edu/tag/05JU)
* [Stacks Project, Definition 29.5.5 (Tag 05JV)](https://stacks.math.columbia.edu/tag/05JV)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- The annihilator of a module transported along a bijective semilinear map over a surjective
ring map is the image of the annihilator.  This is the semilinear form of
`LinearEquiv.annihilator_eq`. -/
private theorem annihilator_eq_map_of_bijective {R R' M N : Type*} [CommRing R] [CommRing R']
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R' N] (φ : R →+* R')
    (hφ : Function.Surjective φ) (f : M →ₛₗ[φ] N) (hf : Function.Bijective f) :
    Module.annihilator R' N = (Module.annihilator R M).map φ := by
  refine le_antisymm (fun s hs => ?_) ?_
  · obtain ⟨r, rfl⟩ := hφ s
    refine Ideal.mem_map_of_mem _ (Module.mem_annihilator.2 fun m => hf.1 ?_)
    rw [map_smulₛₗ, map_zero]
    exact Module.mem_annihilator.1 hs (f m)
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    refine Module.mem_annihilator.2 fun n => ?_
    obtain ⟨m, rfl⟩ := hf.2 n
    rw [← map_smulₛₗ, Module.mem_annihilator.1 hr m, map_zero]

/-- The sections of the chart restriction over a Zariski open of the chart's scheme are the
sections of the module over the étale chart that open cuts out, semilinearly over the
comparison of rings `AlgebraicGeometry.Scheme.Opens.topIso`. -/
def chartRestrictionSheafSectionsSemilinear (F : Modules.{u, u} B S hS X.1 X.2)
    (A : SmallEtale B S hS X.1) (V : (chartScheme A).Opens) :
    letI : Module (Γ(↑V, ⊤) : Type u)
        (F.val.obj (op ((chartOpens B S hS A).obj V)) : Type u) :=
      moduleChartSections B S hS X F ((chartOpens B S hS A).obj V)
    (F.val.obj (op ((chartOpens B S hS A).obj V)) : Type u) →ₛₗ[(V.topIso.hom).hom]
      (Γ(chartRestrictionSheaf B S hS X F A, V) : Type u) :=
  letI : Module (Γ(↑V, ⊤) : Type u)
      (F.val.obj (op ((chartOpens B S hS A).obj V)) : Type u) :=
    moduleChartSections B S hS X F ((chartOpens B S hS A).obj V)
  { toFun := fun m => ULift.up m
    map_add' := fun _ _ => rfl
    map_smul' := fun r m => congrArg ULift.up (congrArg (fun y => y • m)
      (ConcreteCategory.congr_hom V.topIso.hom_inv_id r).symm) }

/-- **The annihilator of the sections of the chart restriction over an affine open of the
chart's scheme.**  It is the image, along the comparison of rings
`AlgebraicGeometry.Scheme.Opens.topIso`, of the annihilator ideal of `F` at the étale chart that
open cuts out.

The sections correspond semilinearly and bijectively by
`AlgebraicGeometry.Space.chartRestrictionSheafSectionsSemilinear`, and over an affine chart the
annihilator ideal of a quasi-coherent module is the annihilator of its sections. -/
theorem annihilator_sections_chartRestrictionSheaf (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) (A : SmallEtale B S hS X.1)
    (V : (chartScheme A).affineOpens) :
    Module.annihilator Γ(chartScheme A, V.1) Γ(chartRestrictionSheaf B S hS X F A, V.1) =
      Ideal.map (V.1.topIso.hom).hom
        (annihilatorIdealAt B S hS X F (op ((chartOpens B S hS A).obj V.1))) := by
  let : Module (Γ(↑(V.1), ⊤) : Type u)
      (F.val.obj (op ((chartOpens B S hS A).obj V.1)) : Type u) :=
    moduleChartSections B S hS X F ((chartOpens B S hS A).obj V.1)
  rw [annihilator_eq_map_of_bijective (V.1.topIso.hom).hom
    (ConcreteCategory.bijective_of_isIso V.1.topIso.hom).2
    (chartRestrictionSheafSectionsSemilinear B S hS X F A V.1)
    ⟨fun _ _ h => ULift.up_injective h, fun y => ⟨y.down, rfl⟩⟩]
  exact congrArg (Ideal.map (V.1.topIso.hom).hom)
    (chartIdeal_annihilatorIdealSheaf_eq_annihilator B S hS X F hF
      ((chartOpens B S hS A).obj V.1) V.2).symm

/-- The image of the ideal of sections of a sheaf of ideals of `𝒪_X` over a chart is unchanged
when the chart is replaced by an equal one and the ring map by one agreeing with it. -/
private theorem map_submodule_obj_eq_of_chart_eq
    (N : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    {R : Type u} [CommRing R] {W W' : SmallEtale B S hS X.1} (h : W = W')
    (φ : ToType ((structureRingSheaf B S hS X).obj.obj (op W)) →+* R)
    (φ' : ToType ((structureRingSheaf B S hS X).obj.obj (op W')) →+* R)
    (hφ : ∀ a, φ a = φ' (cast (congrArg (fun Y : SmallEtale B S hS X.1 =>
      ToType ((structureRingSheaf B S hS X).obj.obj (op Y))) h) a)) :
    Ideal.map φ (N.obj (op W)) = Ideal.map φ' (N.obj (op W')) := by
  subst h
  exact congrArg (fun ψ => Ideal.map ψ (N.obj (op W))) (RingHom.ext hφ)

/-- The ideal that a sheaf of ideals of `𝒪_X` cuts out on a Zariski open of an étale scheme
chart, with the open read as a chart by `AlgebraicGeometry.Space.chartOpens` rather than by
`AlgebraicGeometry.Space.openChart`. -/
theorem openChartIdeal_eq_map_chartOpens
    (N : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (A : SmallEtale B S hS X.1) (V : (chartScheme A).Opens) :
    openChartIdeal B S hS X N A V =
      Ideal.map (V.topIso.hom).hom (N.obj (op ((chartOpens B S hS A).obj V))) :=
  (map_submodule_obj_eq_of_chart_eq B S hS X N (chartOpens_obj_eq_openChart B S hS A V)
    (V.topIso.hom).hom (openChartTopRingHom B S hS X A V) fun _ => rfl).symm

/-- **Stacks 07U0, part (1), with the support of the restriction taken in the sense of
schemes.**  Let `F` be a finite type quasi-coherent `𝒪_X`-module, let `Z ⊆ X` be its
scheme-theoretic support and let `A` be an étale scheme chart of `X` — a scheme `U` with an
étale morphism to `X`.  Then the scheme-theoretic support of Stacks 05JV of the restriction of
`F` to `U` is the sheaf of ideals that `Z` cuts out on `U`, that is, `Z ×_X U`.

Over an affine open `V` of `U` both sides are the annihilator of the sections of `F` over the
étale chart `V` cuts out: the left-hand side by
`AlgebraicGeometry.Space.annihilator_sections_chartRestrictionSheaf` and the right-hand side
because the ideal cutting out the scheme-theoretic support is the annihilator ideal sheaf of
`F`. -/
@[stacks 07U0 "part (1): on a scheme U étale over X the scheme-theoretic support of the \
restriction of F, in the sense of schemes, is the sheaf of ideals that the scheme-theoretic \
support of F cuts out on U"]
theorem schemeTheoreticSupport_chartRestrictionSheaf (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) (hFft : SheafOfModules.IsFiniteTypeOnSite F)
    (Z : ClosedSubspaces B S hS X.1) (hZ : Z.1 = schemeTheoreticSupport B S hS X F)
    (A : SmallEtale B S hS X.1) :
    letI : (chartRestrictionSheaf B S hS X F A).IsQuasicoherent :=
      isQuasicoherent_chartRestrictionSheaf B S hS X F hF A
    letI : (chartRestrictionSheaf B S hS X F A).IsFiniteType :=
      Stacks.AlgebraicGeometry.TopDegreeFiniteType.isFiniteType_of_forall_moduleFinite_sections
        (chartRestrictionSheaf B S hS X F A)
        (moduleFinite_sections_chartRestrictionSheaf B S hS X F hF hFft A)
    Scheme.Modules.schemeTheoreticSupport (chartRestrictionSheaf B S hS X F A) =
      idealSheafDataOfChart B S hS X (definingIdealSheaf B S hS X Z)
        (definingIdealSheaf_isCartesianOnAffineCharts B S hS X Z) A := by
  obtain ⟨hZ', hid'⟩ := exists_isClosedSubspace_schemeTheoreticSupport B S hS X F hF
    (Stacks.SheafOfModules.presheaf_isFiniteType_of_isFiniteTypeOnSite F hFft)
  have hid : definingIdealSheaf B S hS X Z = annihilatorIdealSheaf B S hS X F := by
    rw [show Z = (⟨schemeTheoreticSupport B S hS X F, hZ'⟩ : ClosedSubspaces B S hS X.1) from
      Subtype.ext hZ]
    exact hid'
  refine Scheme.IdealSheafData.ext (funext fun V => ?_)
  rw [Scheme.Modules.schemeTheoreticSupport_ideal,
    annihilator_sections_chartRestrictionSheaf B S hS X F hF A V,
    ideal_idealSheafDataOfChart, openChartIdeal_eq_map_chartOpens, hid]
  rfl

end AlgebraicGeometry.Space

end
