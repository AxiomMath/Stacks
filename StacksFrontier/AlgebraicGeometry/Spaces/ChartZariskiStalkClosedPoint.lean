module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartZariskiStalkOrdinary

/-!
# The Zariski stalk at a point whose only neighbourhood is the whole space

A point `x` of a topological space whose only open neighbourhood is `⊤` sees no more of a
presheaf than its global sections: the index category of the stalk colimit has `⊤` as its
initial object, so the germ `F(⊤) ⟶ F_x` is an isomorphism.  The spectrum of a local ring is
the example this development needs — an open of `Spec A` containing the closed point is the
whole of `Spec A` — and so, for an étale scheme chart whose scheme is the spectrum of a local
ring and the point of it under a geometric point lying over the closed point, both the local
ring of the chart `𝒪_{U, u}` of Stacks 05VP and the Zariski stalk
`AlgebraicGeometry.Space.chartZariskiModuleStalk` of the chart restriction of an `𝒪_X`-module
are computed by the sections over the whole chart.

## Main results

* `TopCat.Presheaf.isIso_Γgerm_of_forall_eq_top`: **the germ of the global sections is an
  isomorphism at a point whose only open neighbourhood is the whole space.**
* `AlgebraicGeometry.forall_eq_top_of_mem_of_isLocalRing`: the closed point of the spectrum of
  a local ring is such a point.
* `AlgebraicGeometry.Space.chartLocalRingIsoTop`: at such a point of an étale scheme chart the
  local ring `𝒪_{U, u}` is the ring of global regular functions on the chart.
* `AlgebraicGeometry.Space.chartZariskiModuleStalkTopAddEquiv` and
  `AlgebraicGeometry.Space.chartZariskiModuleStalkTopAddEquiv_smul`: at such a point the Zariski
  stalk of the chart restriction is the module of its sections over the whole chart, with the
  scalars matched along `AlgebraicGeometry.Space.chartLocalRingIsoTop`.
* `AlgebraicGeometry.Space.chartZariskiModuleStalkTopLinearEquiv`: the two together, as a
  linear equivalence over the local ring of the chart.

## Implementation notes

The hypothesis is taken as `∀ V, x ∈ V → V = ⊤` rather than as local-ring-ness of a ring, so
that nothing here depends on how the chart's scheme is presented as a spectrum; the spectrum of
a local ring is the instance recorded as
`AlgebraicGeometry.forall_eq_top_of_mem_of_isLocalRing`.

The module statement is phrased as an additive equivalence plus its scalar law, as
`AlgebraicGeometry.Space.chartZariskiStalkAddEquiv` and
`AlgebraicGeometry.Space.etaleLocalRingToGeometricModuleStalkAddEquiv` are, because the two
sides carry scalars over two different rings — the sections over `⊤` over `Γ(U, ⊤)` and the
stalk over `𝒪_{U, u}` — and the comparison of the rings is itself the germ, so no single
`LinearEquiv` is available before the ring germ has been inverted.

No declaration here carries a `stacks` attribute: a point with a smallest neighbourhood is not
a clause of any tag, and the chart statements are readings of
`AlgebraicGeometry.Space.chartZariskiModuleStalk` rather than assertions about Stacks 05VP.

## References

* [Stacks Project, Tag 05VP](https://stacks.math.columbia.edu/tag/05VP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v u

/-! ### Points with no proper open neighbourhood -/

namespace TopCat.Presheaf

/-- The whole space is the initial open neighbourhood of a point which has no other one. -/
def isInitialOpenNhdsTop {X : TopCat.{v}} (x : X)
    (h : ∀ V : Opens X, x ∈ V → V = ⊤) : IsInitial (⊤ : OpenNhds x) :=
  IsInitial.ofUniqueHom (fun V => homOfLE (by
      rw [OpenNhds.le_def]
      exact le_of_eq (h V.1 V.2).symm))
    (fun _ _ => Subsingleton.elim _ _)

/-- **The germ of the global sections is an isomorphism at a point whose only open
neighbourhood is the whole space.**  The stalk is the colimit over the open neighbourhoods of
the point, and `⊤` is the initial one, so the colimit is attained there. -/
theorem isIso_Γgerm_of_forall_eq_top {C : Type u} [Category.{v} C] [HasColimits.{v} C]
    {X : TopCat.{v}} (F : X.Presheaf C) (x : X)
    (h : ∀ V : Opens X, x ∈ V → V = ⊤) : IsIso (F.Γgerm x) :=
  (colimit.isColimit ((OpenNhds.inclusion x).op ⋙ F)).isIso_ι_app_of_isTerminal
    (op (⊤ : OpenNhds x)) (terminalOpOfInitial (isInitialOpenNhdsTop x h))

/-- The sections over the whole space and the stalk at a point with no other open
neighbourhood, as an isomorphism. -/
def ΓgermIso {C : Type u} [Category.{v} C] [HasColimits.{v} C] {X : TopCat.{v}}
    (F : X.Presheaf C) (x : X) (h : ∀ V : Opens X, x ∈ V → V = ⊤) :
    F.obj (op ⊤) ≅ F.stalk x :=
  @asIso _ _ _ _ (F.Γgerm x) (isIso_Γgerm_of_forall_eq_top F x h)

end TopCat.Presheaf

/-! ### Points to which everything specializes -/

namespace TopCat.Presheaf

/-- A point to which every point of the space specializes lies in no proper open. -/
theorem forall_eq_top_of_specializes {X : TopCat.{v}} (x : X)
    (hx : ∀ z : X, z ⤳ x) (V : Opens X) (hV : x ∈ V) : V = ⊤ :=
  eq_top_iff.mpr fun z _ => (hx z).mem_open V.2 hV

end TopCat.Presheaf

namespace AlgebraicGeometry

/-- **The closed point of the spectrum of a local ring lies in no proper open.**  This is
`IsLocalRing.closedPoint_mem_iff` read on the opens of the scheme `Spec R`. -/
theorem forall_eq_top_of_mem_of_isLocalRing (R : CommRingCat.{u}) [IsLocalRing R]
    (V : (Spec R).Opens) (hV : IsLocalRing.closedPoint R ∈ V) : V = ⊤ :=
  (IsLocalRing.closedPoint_mem_iff (R := R) V).mp hV

end AlgebraicGeometry

/-! ### The chart local ring and the chart Zariski stalk at such a point -/

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
  {x : GeometricPoint B S hS X} (V : SmallEtaleNeighborhood x)
  (F : Modules.{u, u} B S hS X hX)

/-- **The local ring of an étale scheme chart at a point with no proper open neighbourhood is
the ring of global regular functions on the chart.** -/
def chartLocalRingIsoTop
    (h : ∀ O : (chartScheme V.chart).Opens, chartPoint B S hS X V ∈ O → O = ⊤) :
    CommRingCat.of Γ(chartScheme V.chart, ⊤) ≅ chartLocalRing B S hS X V :=
  TopCat.Presheaf.ΓgermIso (chartScheme V.chart).presheaf (chartPoint B S hS X V) h

/-- The ring equivalence underlying `AlgebraicGeometry.Space.chartLocalRingIsoTop`. -/
def chartLocalRingRingEquivTop
    (h : ∀ O : (chartScheme V.chart).Opens, chartPoint B S hS X V ∈ O → O = ⊤) :
    Γ(chartScheme V.chart, ⊤) ≃+* ↥(chartLocalRing B S hS X V) :=
  (chartLocalRingIsoTop B S hS V h).commRingCatIsoToRingEquiv

/-- `AlgebraicGeometry.Space.chartLocalRingRingEquivTop` is the germ of the structure sheaf. -/
theorem chartLocalRingRingEquivTop_apply
    (h : ∀ O : (chartScheme V.chart).Opens, chartPoint B S hS X V ∈ O → O = ⊤)
    (c : Γ(chartScheme V.chart, ⊤)) :
    chartLocalRingRingEquivTop B S hS V h c =
      (chartScheme V.chart).presheaf.germ ⊤ (chartPoint B S hS X V) trivial c :=
  rfl

/-- **At a point of an étale scheme chart with no proper open neighbourhood the Zariski stalk
of the chart restriction is its module of sections over the whole chart**, as additive
groups. -/
def chartZariskiModuleStalkTopAddEquiv
    (h : ∀ O : (chartScheme V.chart).Opens, chartPoint B S hS X V ∈ O → O = ⊤) :
    ↥((chartRestrictionPresheafOfModules B S hS hX V F).obj (op ⊤)) ≃+
      ↥(chartZariskiModuleStalk B S hS X hX V F) :=
  ((TopCat.Presheaf.ΓgermIso
        (chartRestrictionPresheafOfModules B S hS hX V F).presheaf
        (chartPoint B S hS X V) h).addCommGroupIsoToAddEquiv).trans
    (chartZariskiStalkAddEquiv B S hS hX V F).symm

/-- **The comparison of the Zariski stalk with the sections over the whole chart is semilinear
along the germ of the structure sheaf**, which is
`AlgebraicGeometry.Space.chartLocalRingRingEquivTop`. -/
theorem chartZariskiModuleStalkTopAddEquiv_smul
    (h : ∀ O : (chartScheme V.chart).Opens, chartPoint B S hS X V ∈ O → O = ⊤)
    (c : Γ(chartScheme V.chart, ⊤))
    (s : ↥((chartRestrictionPresheafOfModules B S hS hX V F).obj (op ⊤))) :
    chartZariskiModuleStalkTopAddEquiv B S hS hX V F h (c • s) =
      chartLocalRingRingEquivTop B S hS V h c •
        chartZariskiModuleStalkTopAddEquiv B S hS hX V F h s := by
  refine (chartZariskiStalkAddEquiv B S hS hX V F).injective ?_
  refine Eq.trans ((chartZariskiStalkAddEquiv B S hS hX V F).apply_symm_apply _) ?_
  refine Eq.trans (PresheafOfModules.germ_smul
    (chartRestrictionPresheafOfModules B S hS hX V F) (chartPoint B S hS X V) ⊤ trivial c s) ?_
  refine Eq.trans ?_ (chartZariskiStalkAddEquiv_smul B S hS hX V F
    (chartLocalRingRingEquivTop B S hS V h c)
    ((chartZariskiStalkAddEquiv B S hS hX V F).symm _)).symm
  exact congrArg (fun z => chartLocalRingRingEquivTop B S hS V h c • z)
    ((chartZariskiStalkAddEquiv B S hS hX V F).apply_symm_apply _).symm

/-- **The Zariski stalk of the chart restriction at a point with no proper open neighbourhood
is its module of sections over the whole chart**, as modules over the ring of global regular
functions on the chart, whose germ identifies it with the local ring `𝒪_{U, u}`. -/
def chartZariskiModuleStalkTopLinearEquiv
    (h : ∀ O : (chartScheme V.chart).Opens, chartPoint B S hS X V ∈ O → O = ⊤)
    (g : ↥(chartZariskiModuleStalk B S hS X hX V F) ≃ₗ[↥(chartLocalRing B S hS X V)]
      ↥(chartLocalRing B S hS X V)) :
    ↥((chartRestrictionPresheafOfModules B S hS hX V F).obj (op ⊤)) ≃ₗ[
        Γ(chartScheme V.chart, ⊤)] Γ(chartScheme V.chart, ⊤) :=
  letI e : ↥((chartRestrictionPresheafOfModules B S hS hX V F).obj (op ⊤)) ≃+
      Γ(chartScheme V.chart, ⊤) :=
    ((chartZariskiModuleStalkTopAddEquiv B S hS hX V F h).trans
      g.toAddEquiv).trans (chartLocalRingRingEquivTop B S hS V h).toAddEquiv.symm
  e.toLinearEquiv (fun c s => by
    change (chartLocalRingRingEquivTop B S hS V h).symm
        (g ((chartZariskiModuleStalkTopAddEquiv B S hS hX V F h) (c • s)))
      = c • (chartLocalRingRingEquivTop B S hS V h).symm
        (g ((chartZariskiModuleStalkTopAddEquiv B S hS hX V F h) s))
    rw [chartZariskiModuleStalkTopAddEquiv_smul B S hS hX V F h c s, map_smul, smul_eq_mul,
      map_mul, RingEquiv.symm_apply_apply, smul_eq_mul])

end AlgebraicGeometry.Space

end
