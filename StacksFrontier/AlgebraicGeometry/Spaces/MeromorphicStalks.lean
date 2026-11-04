module

public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.StalksWeaklyAssociated
public import StacksFrontier.AlgebraicGeometry.Spaces.CodimensionZeroPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierPullbackCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.RegularSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHom
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeNormalization
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingChart
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicFunctions

/-!
# Regular sections and meromorphic functions at a geometric point

Let `X` be an algebraic space over a scheme `S` and let `x` be a geometric point of `X`. The
regular sections `𝒮_X` of the structure sheaf form a multiplicative subpresheaf of `𝒪_X`
(Stacks 0EN2), and the germs of regular sections at `x` form a multiplicative subset
`𝒮_x ⊆ 𝒪_{X, x}` of the étale local ring at `x`.

Every germ of a regular section is a nonzerodivisor of the étale local ring: the étale local
ring is the filtered colimit of the rings of sections over the small étale neighbourhoods of
`x`, a product of germs vanishes only if it already vanishes on a refinement, and over a
refinement the restriction of a regular section is still regular and hence a nonzerodivisor
in the ring of sections there.

Under the two hypotheses of Stacks 0EN6 — every weakly associated point of `X` is a point of
codimension `0`, and every quasi-compact open of every étale scheme chart has finitely many
irreducible components — the converse holds as well, so `𝒮_x` is *exactly* the set of
nonzerodivisors.  A nonzerodivisor of `𝒪_{X, x}` is the germ of a section `f` over some
neighbourhood; its image in the ordinary local ring `𝒪_{U, u}` of the chart at the point below
`x` is a nonzerodivisor there (Stacks 04KF, the étale local ring being the strict henselization
of that local ring), and the two hypotheses give the chart the hypotheses of Stacks 0EMF, so
after shrinking the chart to an affine open neighbourhood of `u` the restriction of `f` becomes
a regular section.  Consequently the stalk of the sheaf of meromorphic functions `𝒦_X` at `x`
is the total ring of fractions of `𝒪_{X, x}`.

## Main definitions

* `AlgebraicGeometry.Space.regularSectionsStalk` is `𝒮_x`, the submonoid of germs at `x` of
  regular sections over the small étale neighbourhoods of `x`.
* `AlgebraicGeometry.Space.regularLocalizationPresheaf` is the presheaf
  `U ↦ 𝒮_X(U)⁻¹ 𝒪_X(U)` whose sheafification is `𝒦_X`, and
  `AlgebraicGeometry.Space.regularLocalizationStalk` its stalk at `x`.
* `AlgebraicGeometry.Space.meromorphicStalk` is the stalk `𝒦_{X, x}` of the sheaf of
  meromorphic functions, and `AlgebraicGeometry.Space.toMeromorphicStalk` the canonical map
  `𝒪_{X, x} → 𝒦_{X, x}`.

## Main results

* `AlgebraicGeometry.Space.mem_nonZeroDivisors_etaleLocalRingGerm`: the germ at `x` of a
  regular section is a nonzerodivisor of the étale local ring, and
  `AlgebraicGeometry.Space.regularSectionsStalk_le_nonZeroDivisors` is the resulting
  containment `𝒮_x ⊆ 𝒪_{X, x}⁰`.
* `AlgebraicGeometry.Space.nonZeroDivisors_le_regularSectionsStalk` is the reverse
  containment under the hypotheses of Stacks 0EN6, and
  `AlgebraicGeometry.Space.regularSectionsStalk_eq_nonZeroDivisors` is **Stacks 0EN6, part
  (3)**.
* `AlgebraicGeometry.Space.isLocalization_regularLocalizationStalk`: the stalk of the presheaf
  of sectionwise localizations is the localization of `𝒪_{X, x}` at `𝒮_x`.
* `AlgebraicGeometry.Space.isFractionRing_meromorphicStalk` is **Stacks 0EN6, part (4)**.

## Implementation notes

`𝒮_x` is defined as the supremum over the small étale neighbourhoods of the images of the
multiplicative subsets of regular sections. The neighbourhoods are cofiltered (Stacks 04K0),
so this supremum is the union of those images; the proofs below use the colimit presentation
`AlgebraicGeometry.Space.spaceGerms_isColimit` of the étale local ring directly rather than
that description.

`𝒦_{X, x}` is taken as the fibre of `𝒦_X` at the point of the small étale site determined by
the geometric point (Stacks 04K0) rather than as the colimit over the small étale
neighbourhoods of Stacks 04JY: the sections of `𝒦_X` live in `CommRingCat` at the universe of
the schemes, where that colimit shape is too large, while the fibre at the point of the site
is formed over an initially small index category.  The two agree, and
`AlgebraicGeometry.Space.pointStalkRingEquiv` is the comparison for the structure sheaf, which
is what relates the two sides of the statement.

Parts (1) and (2) of Stacks 0EN6 — quasi-coherence of `𝒦_X` and the computation of `𝒦_X(U)`
on an affine chart — are proved in
`StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicQuasicoherent`, not here: this file carries
only parts (3) and (4), the stalkwise statement.

## References

* [Stacks Project, Tag 0EN2](https://stacks.math.columbia.edu/tag/0EN2)
* [Stacks Project, Tag 0EN3](https://stacks.math.columbia.edu/tag/0EN3)
* [Stacks Project, Tag 0EN6](https://stacks.math.columbia.edu/tag/0EN6)
* [Stacks Project, Tag 04JY](https://stacks.math.columbia.edu/tag/04JY)
* [Stacks Project, Tag 04K0](https://stacks.math.columbia.edu/tag/04K0)
* [Stacks Project, Tag 04KF](https://stacks.math.columbia.edu/tag/04KF)
* [Stacks Project, Tag 0EMF](https://stacks.math.columbia.edu/tag/0EMF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The germs at a geometric point `x` of the regular sections of the structure sheaf of `F`,
as a multiplicative subset `𝒮_x` of the étale local ring `𝒪_{F, x}`. -/
noncomputable def regularSectionsStalk (x : GeometricPoint B S hS F) :
    Submonoid (etaleLocalRing B S hS F x) :=
  ⨆ U : (SmallEtaleNeighborhood x)ᵒᵖ,
    (regularSections B S hS F U.unop.chart).map
      (etaleLocalRingGerm B S hS F x U).toMonoidHom

/-- The germ of a regular section over a small étale neighbourhood belongs to `𝒮_x`. -/
theorem etaleLocalRingGerm_mem_regularSectionsStalk {x : GeometricPoint B S hS F}
    (U : (SmallEtaleNeighborhood x)ᵒᵖ)
    {s : (structurePresheaf B S hS F).obj (op U.unop.chart)}
    (hs : IsRegularSection B S hS F U.unop.chart s) :
    etaleLocalRingGerm B S hS F x U s ∈ regularSectionsStalk x :=
  Submonoid.mem_iSup_of_mem U ⟨s, hs, rfl⟩

/-- The germ of a restricted section over a refinement is the germ of the original section. -/
private theorem etaleLocalRingGerm_map {x : GeometricPoint B S hS F}
    {U W : SmallEtaleNeighborhood x} (f : U ⟶ W)
    (a : (structurePresheaf B S hS F).obj (op W.chart)) :
    etaleLocalRingGerm B S hS F x (op U) ((structurePresheaf B S hS F).map f.hom.op a) =
      etaleLocalRingGerm B S hS F x (op W) a :=
  DFunLike.congr_fun (spaceGerm_naturality (x := x) f.op) a

/-- **The germ of a regular section is a nonzerodivisor in the étale local ring.** If the
product of such a germ with another germ vanishes, then the two sections already have
vanishing product over some common refinement of their neighbourhoods; there the restriction
of the regular section is regular (Stacks 02OU, through
`AlgebraicGeometry.Space.isRegularSection_map`) and hence a nonzerodivisor in the ring of
sections, so the other section vanishes there and its germ is zero. -/
theorem mem_nonZeroDivisors_etaleLocalRingGerm (hF : IsAlgebraicSpace B S hS F)
    (x : GeometricPoint B S hS F) (U : (SmallEtaleNeighborhood x)ᵒᵖ)
    (s : (structurePresheaf B S hS F).obj (op U.unop.chart))
    (hs : IsRegularSection B S hS F U.unop.chart s) :
    etaleLocalRingGerm B S hS F x U s ∈ (etaleLocalRing B S hS F x)⁰ := by
  have hcof : IsCofiltered (SmallEtaleNeighborhood x) :=
    isCofiltered_smallEtaleNeighborhood B S hS F hF x
  have hc := spaceGerms_isColimit (x := x) hF
  rw [mem_nonZeroDivisors_iff_right]
  intro a ha
  obtain ⟨V, t, hVt⟩ := hc.ι_jointly_surjective a
  have hVt' : etaleLocalRingGerm B S hS F x V t = a := hVt
  obtain ⟨W, k, l, -⟩ := IsCofilteredOrEmpty.cone_objs U.unop V.unop
  set s' := (structurePresheaf B S hS F).map k.hom.op s with hs'
  set t' := (structurePresheaf B S hS F).map l.hom.op t with ht'
  have hgs : etaleLocalRingGerm B S hS F x (op W) s' =
      etaleLocalRingGerm B S hS F x U s :=
    etaleLocalRingGerm_map k s
  have hgt : etaleLocalRingGerm B S hS F x (op W) t' = a :=
    (etaleLocalRingGerm_map l t).trans hVt'
  have hzero : etaleLocalRingGerm B S hS F x (op W) (t' * s') =
      etaleLocalRingGerm B S hS F x (op W) 0 := by
    rw [map_mul, map_zero, hgs, hgt]
    exact ha
  obtain ⟨Z, φ, hφ⟩ :=
    (Functor.CoconeTypes.descColimitType_injective_iff_of_isFiltered'
      (CommRingCat.coconeTypesOfRingHoms (spaceSections (x := x))
        (etaleLocalRingGerm B S hS F x) (fun f ↦ spaceGerm_naturality f))).mp
      hc.bijective.1 (op W) (t' * s') 0 hzero
  have hres : (structurePresheaf B S hS F).map φ.unop.hom.op t' *
      (structurePresheaf B S hS F).map φ.unop.hom.op s' = 0 := by
    have h := hφ
    change ((spaceSections (x := x)).map φ).hom (t' * s') =
      ((spaceSections (x := x)).map φ).hom 0 at h
    rw [map_mul, map_zero] at h
    exact h
  have hsreg : IsRegularSection B S hS F Z.unop.chart
      ((structurePresheaf B S hS F).map φ.unop.hom.op s') :=
    isRegularSection_map B S hS F φ.unop.hom _ (isRegularSection_map B S hS F k.hom s hs)
  have hnd := mem_nonZeroDivisors_of_isRegularSectionOn_top _ _ hsreg
  have htz : (structurePresheaf B S hS F).map φ.unop.hom.op t' = 0 :=
    mem_nonZeroDivisors_iff_right.mp hnd _ hres
  have hstep : etaleLocalRingGerm B S hS F x Z
      ((structurePresheaf B S hS F).map φ.unop.hom.op t') =
      etaleLocalRingGerm B S hS F x (op W) t' :=
    etaleLocalRingGerm_map φ.unop t'
  rw [← hgt, ← hstep, htz, map_zero]

/-- Every element of `𝒮_x` is a nonzerodivisor of the étale local ring at `x`. -/
theorem regularSectionsStalk_le_nonZeroDivisors (hF : IsAlgebraicSpace B S hS F)
    (x : GeometricPoint B S hS F) :
    regularSectionsStalk x ≤ (etaleLocalRing B S hS F x)⁰ := by
  refine iSup_le fun U ↦ ?_
  rintro _ ⟨s, hs, rfl⟩
  exact mem_nonZeroDivisors_etaleLocalRingGerm hF x U s hs

/-! ### Shrinking a chart so that a section becomes regular -/

section SchemeLevel

open TopologicalSpace

/-- Two successive restrictions of a section of the structure sheaf are the single restriction:
there is at most one morphism between two opens. -/
private theorem res_comp_eq {X : Scheme.{u}} {Z W' W : X.Opens} (iZ : Z ⟶ W') (iW : W' ⟶ W)
    (hZW : Z ≤ W) (t : Γ(X, W)) :
    X.presheaf.map iZ.op (X.presheaf.map iW.op t) = X.presheaf.map (homOfLE hZW).op t := by
  rw [← Functor.map_comp_apply, ← op_comp, Subsingleton.elim (iZ ≫ iW) (homOfLE hZW)]

/-- Restricting a regular section to a smaller open keeps it regular. -/
private theorem isRegularSectionOn_restrict {X : Scheme.{u}} {W W' : X.Opens} (h : W' ≤ W)
    (t : Γ(X, W)) (ht : IsRegularSectionOn X.toLocallyRingedSpace W t) :
    IsRegularSectionOn X.toLocallyRingedSpace W' (X.presheaf.map (homOfLE h).op t) := by
  rw [Stacks.Meromorphic.isRegularSectionOn_iff_forall_le] at ht ⊢
  intro Z hZ
  rw [res_comp_eq (homOfLE hZ) (homOfLE h) (hZ.trans h) t]
  exact ht Z (hZ.trans h)

/-- The germs at a point of a scheme of the sections of the structure sheaf that are regular on
some open neighbourhood of that point.  These form a multiplicative subset of the local ring:
the regular sections over an open are a multiplicative subset, stable under restriction. -/
private noncomputable def regularGermSubmonoid (X : Scheme.{u}) (z : X) :
    Submonoid (X.presheaf.stalk z) where
  carrier := {a | ∃ (W : X.Opens) (hz : z ∈ W) (t : Γ(X, W)),
    IsRegularSectionOn X.toLocallyRingedSpace W t ∧ X.presheaf.germ W z hz t = a}
  one_mem' := by
    refine ⟨⊤, trivial, 1, ?_, map_one _⟩
    refine (Stacks.Meromorphic.isRegularSectionOn_iff_germ _ ⊤ _).mpr fun y hy ↦ ?_
    rw [show X.presheaf.germ ⊤ y hy (1 : Γ(X, ⊤)) = 1 from map_one _]
    exact IsSMulRegular.one _
  mul_mem' := by
    rintro _ _ ⟨W₁, hz₁, t₁, hr₁, rfl⟩ ⟨W₂, hz₂, t₂, hr₂, rfl⟩
    refine ⟨W₁ ⊓ W₂, ⟨hz₁, hz₂⟩,
      X.presheaf.map (homOfLE inf_le_left).op t₁ * X.presheaf.map (homOfLE inf_le_right).op t₂,
      ?_, ?_⟩
    · have k₁ := isRegularSectionOn_restrict (inf_le_left (a := W₁) (b := W₂)) t₁ hr₁
      have k₂ := isRegularSectionOn_restrict (inf_le_right (a := W₁) (b := W₂)) t₂ hr₂
      rw [Stacks.Meromorphic.isRegularSectionOn_iff_germ] at k₁ k₂ ⊢
      intro y hy
      rw [map_mul]
      exact (k₁ y hy).mul (k₂ y hy)
    · rw [map_mul, X.presheaf.germ_res_apply (homOfLE inf_le_left) z ⟨hz₁, hz₂⟩ t₁,
        X.presheaf.germ_res_apply (homOfLE inf_le_right) z ⟨hz₁, hz₂⟩ t₂]

/-- **Shrinking to an affine open on which a section is a nonzerodivisor.** If every weakly
associated point of a scheme is a generic point of an irreducible component and every
quasi-compact open has finitely many irreducible components, then a global section whose germ
at a point is a nonzerodivisor of the local ring there restricts to a nonzerodivisor on some
affine open neighbourhood of that point.

By Stacks 0EMF the germ is the germ of a section that is regular on some open neighbourhood;
the two sections agree on a smaller neighbourhood, and shrinking further to an affine open
makes the restriction of the global section a nonzerodivisor. -/
private theorem exists_isAffineOpen_isSMulRegular_restrict (X : Scheme.{u})
    (hass : Stacks.Divisors.schemeWeaklyAssociatedPoints X ⊆ genericPoints X)
    (hfinite : ∀ (U : X.Opens), IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (z : X) (f : Γ(X, ⊤))
    (hf : X.presheaf.germ ⊤ z trivial f ∈ (X.presheaf.stalk z)⁰) :
    ∃ O : X.Opens, IsAffineOpen O ∧ ∃ _hz : z ∈ O,
      IsSMulRegular Γ(X, O) (X.presheaf.map (homOfLE (le_top (a := O))).op f) := by
  have hmem : X.presheaf.germ ⊤ z trivial f ∈ regularGermSubmonoid X z := by
    have hsup :
        (⨆ (U : Opens X) (hz : z ∈ U),
          ((X.presheaf.submonoidPresheafOfStalk
            (fun y ↦ nonZeroDivisors (X.presheaf.stalk y))).obj (Opposite.op U)).map
              (X.presheaf.germ U z hz).hom) ≤ regularGermSubmonoid X z := by
      refine iSup_le fun U ↦ iSup_le fun hz ↦ ?_
      rintro _ ⟨t, ht, rfl⟩
      exact ⟨U, hz, t,
        (Stacks.Meromorphic.mem_denominators_iff X.toLocallyRingedSpace U t).mp ht, rfl⟩
    have hEMF :=
      regularSectionGerms_eq_nonZeroDivisors_of_weaklyAssociatedPoints_subset_genericPoints
        X hass hfinite z
    refine hsup ?_
    rw [hEMF]
    exact hf
  obtain ⟨W, hzW, t, hreg, hgerm⟩ := hmem
  obtain ⟨W', hzW', iW, iT, he⟩ :=
    TopCat.Presheaf.germ_eq X.presheaf (V := ⊤) z hzW trivial t f hgerm
  obtain ⟨O, hO, hzO, hOW'set⟩ := exists_isAffineOpen_mem_and_subset hzW'
  have hOW' : O ≤ W' := hOW'set
  refine ⟨O, hO, hzO, ?_⟩
  have hOW : O ≤ W := hOW'.trans iW.le
  have hkey : IsSMulRegular Γ(X, O) (X.presheaf.map (homOfLE hOW).op t) :=
    (Stacks.Meromorphic.isRegularSectionOn_iff_forall_le _ W t).mp hreg O hOW
  have heq : X.presheaf.map (homOfLE hOW).op t =
      X.presheaf.map (homOfLE (le_top (a := O))).op f := by
    rw [← res_comp_eq (homOfLE hOW') iW hOW t, he,
      res_comp_eq (homOfLE hOW') iT (le_top (a := O)) f]
  rw [← heq]
  exact hkey

end SchemeLevel

/-! ### Every nonzerodivisor of the étale local ring is a germ of a regular section -/

section Converse

open TopologicalSpace IsLocalRing

variable (B) (S) (hS)

/-- A Zariski open of the scheme underlying a small étale neighbourhood which contains the
selected point, read as a small étale neighbourhood refining it.  The inclusion of an open
subscheme is étale and the geometric point lifts through it, so the open is again an étale
chart carrying a lift of the geometric point. -/
private noncomputable def openNeighborhoodRefinement {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {x : GeometricPoint B S hS F} (V : SmallEtaleNeighborhood x)
    (O : (chartScheme V.chart).Opens) (hu : chartPoint B S hS F V ∈ O) :
    Over V := by
  have hB : B.Contains O.toScheme :=
    Scheme.size_lt_of_isOpenImmersion O.ι V.chart.obj.left.left.property
  have hrange : Set.range (chartGeometricPoint V).hom ⊆ Set.range O.ι := by
    rintro _ ⟨b, rfl⟩
    rw [Subsingleton.elim b (closedPoint (chartGeometricPoint V).residueField)]
    rw [O.range_ι]
    exact hu
  exact chartRefinement V hB O.ι inferInstance
    (_root_.AlgebraicGeometry.IsOpenImmersion.lift O.ι (chartGeometricPoint V).hom hrange)
    (_root_.AlgebraicGeometry.IsOpenImmersion.lift_fac O.ι (chartGeometricPoint V).hom hrange)

/-- The morphism of charts underlying `openNeighborhoodRefinement` is the inclusion of the
open subscheme. -/
private theorem neighborhoodChartMap_openNeighborhoodRefinement
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {x : GeometricPoint B S hS F}
    (V : SmallEtaleNeighborhood x) (O : (chartScheme V.chart).Opens)
    (hu : chartPoint B S hS F V ∈ O) :
    neighborhoodChartMap (openNeighborhoodRefinement B S hS V O hu).hom = O.ι :=
  rfl

variable {B} {S} {hS}

/-- Regularity of the restriction of a global section transports along an equality of opens. -/
private lemma isSMulRegular_res_top_congr {X : Scheme.{u}} {W W' : X.Opens} (e : W' = W)
    (s : Γ(X, ⊤))
    (hr : IsSMulRegular Γ(X, W) (X.presheaf.map (homOfLE (le_top (a := W))).op s)) :
    IsSMulRegular Γ(X, W') (X.presheaf.map (homOfLE (le_top (a := W'))).op s) := by
  subst e; exact hr

variable (B) (S) (hS)

/-- **Every nonzerodivisor of the étale local ring is the germ of a regular section.**

A nonzerodivisor of `𝒪_{X, x̄}` is the germ of a section `f` over a small étale neighbourhood,
and by Stacks 04KF its image in the local ring `𝒪_{U, u}` of the chart at the point below the
geometric point is a nonzerodivisor there, the former being the strict henselization of the
latter.  Hypotheses (a) and (b) of Stacks 0EN6 give the chart the hypotheses of Stacks 0EMF, so
after shrinking the chart to an affine open neighbourhood of `u` the restriction of `f` becomes
a nonzerodivisor on the whole of that open, i.e. a regular section over a refinement of the
neighbourhood.  Its germ is the original element. -/
theorem nonZeroDivisors_le_regularSectionsStalk (X : AlgebraicSpaces B S hS)
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1)
    (x : GeometricPoint B S hS X.1) :
    (etaleLocalRing B S hS X.1 x)⁰ ≤ regularSectionsStalk x := by
  intro a ha
  obtain ⟨V, f, hVf⟩ := (spaceGerms_isColimit (x := x) X.2).ι_jointly_surjective a
  obtain ⟨V⟩ := V
  have hVf' : etaleLocalRingGerm B S hS X.1 x (op V) f = a := hVf
  have hEt : IsEtale B S hS V.chart.obj.hom :=
    (isEtale_iff_presheaf_of_yoneda B S hS V.chart.obj.hom).mpr V.chart.property
  -- hypothesis (b), read on the chart
  have hfinY : ∀ W : (chartScheme V.chart).Opens, IsCompact (W : Set (chartScheme V.chart)) →
      (irreducibleComponents W).Finite :=
    hfin V.chart.obj.left V.chart.obj.hom hEt
  -- hypothesis (a), read on the chart
  have hassY : Stacks.Divisors.schemeWeaklyAssociatedPoints (chartScheme V.chart) ⊆
      genericPoints (chartScheme V.chart) := by
    intro y hy
    have hcp : ChartPoint B S hS V.chart.obj.left V.chart.obj.hom y
        (chartSchemeToPoints B S hS X.1 V.chart y) :=
      ⟨canonicalSiteFieldPoint B S hS V.chart.obj.left y,
        canonicalSiteFieldPoint_point B S hS V.chart.obj.left y, rfl⟩
    exact (localRingDimension_eq_zero_iff_all_etale_genericPoints B S hS X.2 _).mp
      (hwa _ (mem_weaklyAssociatedPointsOfSpace_chartSchemeToPoints B S hS X V.chart y hy))
      V.chart.obj.left V.chart.obj.hom y hEt hcp
  -- the germ of `f` in the local ring of the chart is a nonzerodivisor
  have hregY : (chartScheme V.chart).presheaf.germ ⊤ (chartPoint B S hS X.1 V) trivial f ∈
      ((chartScheme V.chart).presheaf.stalk (chartPoint B S hS X.1 V))⁰ := by
    rw [← isSMulRegular_iff_mem_nonZeroDivisors]
    rw [← isSMulRegular_etaleLocalRing_iff_germ B S hS X.1 X.2 x V f, hVf']
    exact (isSMulRegular_iff_mem_nonZeroDivisors a).mpr ha
  obtain ⟨O, hO, huO, hregO⟩ := exists_isAffineOpen_isSMulRegular_restrict
    (chartScheme V.chart) hassY hfinY (chartPoint B S hS X.1 V) f hregY
  -- the shrunken chart
  set N := openNeighborhoodRefinement B S hS V O huO with hN
  have hIsAff : IsAffine O.toScheme := hO
  have hnd : Scheme.Γ.map O.ι.op f ∈ Γ(O.toScheme, ⊤)⁰ :=
    (isSMulRegular_iff_mem_nonZeroDivisors _).mp
      (isSMulRegular_res_top_congr O.ι_image_top f hregO)
  have hreg2 : IsRegularSectionOn O.toScheme.toLocallyRingedSpace ⊤ (Scheme.Γ.map O.ι.op f) :=
    (isRegularSectionOn_top_iff_mem_nonZeroDivisors O.toScheme _).mpr hnd
  have hval : (structurePresheaf B S hS X.1).map N.hom.hom.op f = Scheme.Γ.map O.ι.op f :=
    congrArg (fun k : smallEtaleScheme B S hS X.1 N.left.chart ⟶ chartScheme V.chart =>
      Scheme.Γ.map k.op f) (neighborhoodChartMap_openNeighborhoodRefinement B S hS V O huO)
  have hRS : IsRegularSection B S hS X.1 N.left.chart
      ((structurePresheaf B S hS X.1).map N.hom.hom.op f) := by
    rw [hval]; exact hreg2
  have hgerm : etaleLocalRingGerm B S hS X.1 x (op N.left)
      ((structurePresheaf B S hS X.1).map N.hom.hom.op f) =
      etaleLocalRingGerm B S hS X.1 x (op V) f :=
    etaleLocalRingGerm_map N.hom f
  rw [← hVf', ← hgerm]
  exact etaleLocalRingGerm_mem_regularSectionsStalk (op N.left) hRS

/-- **Stacks 0EN6, part (3).** Let `X` be an algebraic space over a scheme `S` such that every
weakly associated point of `X` is a point of codimension `0` and every quasi-compact open of
every étale scheme chart of `X` has finitely many irreducible components (the condition of
Stacks 0BB1).  Then for every geometric point `x̄` of `X` the set `𝒮_x̄` of germs of regular
sections is exactly the set of nonzerodivisors of the étale local ring `𝒪_{X, x̄}`. -/
@[stacks 0EN6 "part (3): for a geometric point the germs of regular sections are exactly the
nonzerodivisors of the étale local ring"]
theorem regularSectionsStalk_eq_nonZeroDivisors (X : AlgebraicSpaces B S hS)
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1)
    (x : GeometricPoint B S hS X.1) :
    regularSectionsStalk x = (etaleLocalRing B S hS X.1 x)⁰ :=
  le_antisymm (regularSectionsStalk_le_nonZeroDivisors X.2 x)
    (nonZeroDivisors_le_regularSectionsStalk B S hS X hwa hfin x)

end Converse

/-! ### The stalk of the sheaf of meromorphic functions -/

section MeromorphicStalk

variable (B) (S) (hS) (X : AlgebraicSpaces B S hS) (x : GeometricPoint B S hS X.1)

/-- The multiplicative subpresheaf `𝒮_X` of regular sections of the structure sheaf of `X`. -/
noncomputable abbrev regularSubpresheaf :
    RingedSite.MultiplicativeSubpresheaf (smallEtaleRingedSite B S hS X.1 X.2) :=
  regularSectionsSubpresheaf B S hS X.1 X.2

/-- The presheaf `U ↦ 𝒮_X(U)⁻¹ 𝒪_X(U)` whose sheafification is the sheaf of meromorphic
functions `𝒦_X` of Stacks 0EN3. -/
noncomputable abbrev regularLocalizationPresheaf :
    (SmallEtale B S hS X.1)ᵒᵖ ⥤ CommRingCat.{u} :=
  (regularSubpresheaf B S hS X).localizationPresheaf

/-- The stalk at the geometric point `x` of the presheaf of sectionwise localizations, taken
as the fibre at the point of the small étale site determined by `x` (Stacks 04K0). -/
noncomputable abbrev regularLocalizationStalk : CommRingCat.{u} :=
  ((etaleSitePoint B S hS X.1 x X.2).presheafFiber (A := CommRingCat.{u})).obj
    (regularLocalizationPresheaf B S hS X)

/-- The canonical map from the étale local ring at `x` to the stalk of the presheaf of
sectionwise localizations. -/
noncomputable def toRegularLocalizationStalk :
    etaleLocalRing B S hS X.1 x →+* regularLocalizationStalk B S hS X x :=
  (((etaleSitePoint B S hS X.1 x X.2).presheafFiber (A := CommRingCat.{u})).map
      (regularSubpresheaf B S hS X).toLocalizationPresheaf).hom.comp
    (pointStalkRingEquiv B S hS X x).symm.toRingHom

/-- The canonical map sends the germ at `x` of a regular function on a small étale
neighbourhood to the germ of its image in the sectionwise localization over that
neighbourhood. -/
theorem toRegularLocalizationStalk_germ (N : SmallEtaleNeighborhood x)
    (a : (smallEtaleRingedTopos B S hS X).O.obj.obj (op N.chart)) :
    toRegularLocalizationStalk B S hS X x (etaleLocalRingGerm B S hS X.1 x (op N) a) =
      (etaleSitePoint B S hS X.1 x X.2).toPresheafFiber N.chart ⟨N.point, N.point_comp⟩
        (regularLocalizationPresheaf B S hS X)
        (((regularSubpresheaf B S hS X).toLocalizationPresheaf.app (op N.chart)).hom a) := by
  have hsymm : (pointStalkRingEquiv B S hS X x).symm
      (etaleLocalRingGerm B S hS X.1 x (op N) a) =
      (etaleSitePoint B S hS X.1 x X.2).toPresheafFiber N.chart ⟨N.point, N.point_comp⟩
        (smallEtaleRingedTopos B S hS X).O.obj a := by
    rw [← pointStalkRingEquiv_germ_neighborhood B S hS X x N a, RingEquiv.symm_apply_apply]
  show ((etaleSitePoint B S hS X.1 x X.2).presheafFiber.map
      (regularSubpresheaf B S hS X).toLocalizationPresheaf)
    ((pointStalkRingEquiv B S hS X x).symm (etaleLocalRingGerm B S hS X.1 x (op N) a)) = _
  rw [hsymm]
  exact (etaleSitePoint B S hS X.1 x X.2).toPresheafFiber_naturality_apply
    (regularSubpresheaf B S hS X).toLocalizationPresheaf N.chart
    ⟨N.point, N.point_comp⟩ a

/-- **The stalk of the presheaf of sectionwise localizations is the localization of the étale
local ring at `𝒮_x`.**  The three conditions are checked on the filtered colimit presentation
of the stalk: the germ of a regular section becomes a unit already over one neighbourhood,
every germ of a sectionwise fraction is a fraction of germs, and two germs with the same image
agree after multiplying by the germ of a regular section over a common refinement. -/
theorem isLocalization_regularLocalizationStalk :
    letI : Algebra (etaleLocalRing B S hS X.1 x) (regularLocalizationStalk B S hS X x) :=
      (toRegularLocalizationStalk B S hS X x).toAlgebra
    IsLocalization (regularSectionsStalk x) (regularLocalizationStalk B S hS X x) := by
  let _ : Algebra (etaleLocalRing B S hS X.1 x) (regularLocalizationStalk B S hS X x) :=
    (toRegularLocalizationStalk B S hS X x).toAlgebra
  have halg : (algebraMap (etaleLocalRing B S hS X.1 x)
      (regularLocalizationStalk B S hS X x)) = toRegularLocalizationStalk B S hS X x := rfl
  rw [_root_.isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨y, hy⟩
    rw [halg]
    refine (?_ : regularSectionsStalk x ≤
      Submonoid.comap (toRegularLocalizationStalk B S hS X x).toMonoidHom
        (IsUnit.submonoid (regularLocalizationStalk B S hS X x))) hy
    refine iSup_le fun U ↦ ?_
    obtain ⟨U⟩ := U
    rintro _ ⟨s, hs, rfl⟩
    refine Eq.mpr (congrArg IsUnit (toRegularLocalizationStalk_germ B S hS X x U s)) ?_
    exact IsUnit.map ((etaleSitePoint B S hS X.1 x X.2).toPresheafFiber U.chart
        ⟨U.point, U.point_comp⟩ (regularLocalizationPresheaf B S hS X)).hom
      (IsLocalization.map_units (M := (regularSubpresheaf B S hS X).obj (op U.chart))
        (Localization ((regularSubpresheaf B S hS X).obj (op U.chart))) ⟨s, hs⟩)
  · intro z
    obtain ⟨U, ⟨p, hp⟩, w, rfl⟩ :=
      (etaleSitePoint B S hS X.1 x X.2).toPresheafFiber_jointly_surjective z
    obtain ⟨⟨a, m⟩, hm⟩ := IsLocalization.surj
      (M := (regularSubpresheaf B S hS X).obj (op U))
      (S := Localization ((regularSubpresheaf B S hS X).obj (op U)))
      (show Localization ((regularSubpresheaf B S hS X).obj (op U)) from w)
    refine ⟨⟨etaleLocalRingGerm B S hS X.1 x (op ⟨U, p, hp⟩) a,
      ⟨etaleLocalRingGerm B S hS X.1 x (op ⟨U, p, hp⟩) m.1,
        etaleLocalRingGerm_mem_regularSectionsStalk (op ⟨U, p, hp⟩) m.2⟩⟩, ?_⟩
    show (etaleSitePoint B S hS X.1 x X.2).toPresheafFiber U ⟨p, hp⟩
          (regularLocalizationPresheaf B S hS X) w *
        toRegularLocalizationStalk B S hS X x
          (etaleLocalRingGerm B S hS X.1 x (op ⟨U, p, hp⟩) m.1) =
      toRegularLocalizationStalk B S hS X x
        (etaleLocalRingGerm B S hS X.1 x (op ⟨U, p, hp⟩) a)
    rw [toRegularLocalizationStalk_germ B S hS X x ⟨U, p, hp⟩ m.1,
      toRegularLocalizationStalk_germ B S hS X x ⟨U, p, hp⟩ a]
    exact (map_mul ((etaleSitePoint B S hS X.1 x X.2).toPresheafFiber U ⟨p, hp⟩
      (regularLocalizationPresheaf B S hS X)).hom _ _).symm.trans (congrArg _ hm)
  · intro c d hcd
    obtain ⟨U, ⟨p, hp⟩, za, zb, hza, hzb⟩ :=
      (etaleSitePoint B S hS X.1 x X.2).toPresheafFiber_jointly_surjective₂
        ((pointStalkRingEquiv B S hS X x).symm c) ((pointStalkRingEquiv B S hS X x).symm d)
    have hger : ∀ (z : (structurePresheaf B S hS X.1).obj (op U)) (c),
        (etaleSitePoint B S hS X.1 x X.2).toPresheafFiber U ⟨p, hp⟩
          (smallEtaleRingedTopos B S hS X).O.obj z = (pointStalkRingEquiv B S hS X x).symm c →
        etaleLocalRingGerm B S hS X.1 x (op ⟨U, p, hp⟩) z = c := fun z c hz =>
      (pointStalkRingEquiv_germ_neighborhood B S hS X x ⟨U, p, hp⟩ z).symm.trans
        ((congrArg (pointStalkRingEquiv B S hS X x) hz).trans
          ((pointStalkRingEquiv B S hS X x).apply_symm_apply c))
    have hc := hger za c hza
    have hd := hger zb d hzb
    have heq : (etaleSitePoint B S hS X.1 x X.2).toPresheafFiber U ⟨p, hp⟩
          (regularLocalizationPresheaf B S hS X)
          (((regularSubpresheaf B S hS X).toLocalizationPresheaf.app (op U)).hom za) =
        (etaleSitePoint B S hS X.1 x X.2).toPresheafFiber U ⟨p, hp⟩
          (regularLocalizationPresheaf B S hS X)
          (((regularSubpresheaf B S hS X).toLocalizationPresheaf.app (op U)).hom zb) := by
      rw [← toRegularLocalizationStalk_germ B S hS X x ⟨U, p, hp⟩ za,
        ← toRegularLocalizationStalk_germ B S hS X x ⟨U, p, hp⟩ zb, hc, hd]
      exact hcd
    obtain ⟨Y, g, ⟨y, hy⟩, hyp, hres⟩ :=
      ((etaleSitePoint B S hS X.1 x X.2).toPresheafFiber_eq_iff' U ⟨p, hp⟩ _ _).mp heq
    have hnat : ∀ v : (smallEtaleRingedTopos B S hS X).O.obj.obj (op U),
        (regularLocalizationPresheaf B S hS X).map g.op
            (((regularSubpresheaf B S hS X).toLocalizationPresheaf.app (op U)).hom v) =
          ((regularSubpresheaf B S hS X).toLocalizationPresheaf.app (op Y)).hom
            ((smallEtaleRingedTopos B S hS X).O.obj.map g.op v) := fun v =>
      (ConcreteCategory.congr_hom
        ((regularSubpresheaf B S hS X).toLocalizationPresheaf.naturality g.op) v).symm
    rw [hnat, hnat] at hres
    have hres' : algebraMap ((smallEtaleRingedSite B S hS X.1 X.2).O.obj.obj (op Y))
          (Localization ((regularSubpresheaf B S hS X).obj (op Y)))
          ((smallEtaleRingedTopos B S hS X).O.obj.map g.op za) =
        algebraMap ((smallEtaleRingedSite B S hS X.1 X.2).O.obj.obj (op Y))
          (Localization ((regularSubpresheaf B S hS X).obj (op Y)))
          ((smallEtaleRingedTopos B S hS X).O.obj.map g.op zb) := hres
    obtain ⟨cc, hcc⟩ := IsLocalization.exists_of_eq
      (M := (regularSubpresheaf B S hS X).obj (op Y))
      (S := Localization ((regularSubpresheaf B S hS X).obj (op Y))) hres'
    refine ⟨⟨etaleLocalRingGerm B S hS X.1 x (op ⟨Y, y, hy⟩) cc.1,
      etaleLocalRingGerm_mem_regularSectionsStalk (op ⟨Y, y, hy⟩) cc.2⟩, ?_⟩
    let hmor : (⟨Y, y, hy⟩ : SmallEtaleNeighborhood x) ⟶ ⟨U, p, hp⟩ :=
      ⟨g, congrArg Subtype.val hyp⟩
    have hgc := (etaleLocalRingGerm_map hmor za).trans hc
    have hgd := (etaleLocalRingGerm_map hmor zb).trans hd
    show etaleLocalRingGerm B S hS X.1 x (op ⟨Y, y, hy⟩) cc.1 * c =
      etaleLocalRingGerm B S hS X.1 x (op ⟨Y, y, hy⟩) cc.1 * d
    rw [← hgc, ← hgd]
    exact (map_mul (etaleLocalRingGerm B S hS X.1 x (op ⟨Y, y, hy⟩)) _ _).symm.trans
      ((congrArg (etaleLocalRingGerm B S hS X.1 x (op ⟨Y, y, hy⟩)) hcc).trans (map_mul _ _ _))

/-- **The stalk `𝒦_{X, x̄}` of the sheaf of meromorphic functions at a geometric point.**  The
sheaf of meromorphic functions of Stacks 0EN3 is a sheaf on the small étale site of `X`, and
this is its fibre at the point of that site determined by `x̄` (Stacks 04K0), that is, its
geometric stalk. -/
noncomputable abbrev meromorphicStalk : CommRingCat.{u} :=
  ((etaleSitePoint B S hS X.1 x X.2).presheafFiber (A := CommRingCat.{u})).obj
    (meromorphicFunctionSheaf B S hS X.1 X.2).obj

/-- Sheafification does not change the stalk at a point of a site, so the stalk of `𝒦_X` is
the stalk of the presheaf of sectionwise localizations. -/
noncomputable def meromorphicStalkIso :
    regularLocalizationStalk B S hS X x ≅ meromorphicStalk B S hS X x :=
  @asIso _ _ _ _ (((etaleSitePoint B S hS X.1 x X.2).presheafFiber (A := CommRingCat.{u})).map
      (CategoryTheory.toSheafify (SmallEtale.topology B S hS X.1)
        (regularLocalizationPresheaf B S hS X)))
    (GrothendieckTopology.Point.W_isInvertedBy_presheafFiber
      (etaleSitePoint B S hS X.1 x X.2) (A := CommRingCat.{u}) _
      (GrothendieckTopology.W_toSheafify _ _))

/-- The canonical map `𝒪_{X, x̄} → 𝒦_{X, x̄}` on stalks induced by `𝒪_X ⟶ 𝒦_X`. -/
noncomputable def toMeromorphicStalk :
    etaleLocalRing B S hS X.1 x →+* meromorphicStalk B S hS X x :=
  ((meromorphicStalkIso B S hS X x).commRingCatIsoToRingEquiv.toRingHom).comp
    (toRegularLocalizationStalk B S hS X x)

/-- **Stacks 0EN6, part (4).** Let `X` be an algebraic space over a scheme `S` such that every
weakly associated point of `X` is a point of codimension `0` and every quasi-compact open of
every étale scheme chart of `X` has finitely many irreducible components (the condition of
Stacks 0BB1).  Then for every geometric point `x̄` of `X` the stalk `𝒦_{X, x̄}` of the sheaf of
meromorphic functions is the total ring of fractions of the étale local ring `𝒪_{X, x̄}`.

The stalk of `𝒦_X` is the stalk of the presheaf of sectionwise localizations, which is the
localization of `𝒪_{X, x̄}` at `𝒮_x̄`; by part (3) that multiplicative subset is exactly the
set of nonzerodivisors of `𝒪_{X, x̄}`. -/
@[stacks 0EN6 "part (4): for a geometric point the stalk of the sheaf of meromorphic functions
is the total ring of fractions of the étale local ring"]
theorem isFractionRing_meromorphicStalk
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1) :
    letI : Algebra (etaleLocalRing B S hS X.1 x) (meromorphicStalk B S hS X x) :=
      (toMeromorphicStalk B S hS X x).toAlgebra
    IsFractionRing (etaleLocalRing B S hS X.1 x) (meromorphicStalk B S hS X x) := by
  let _ : Algebra (etaleLocalRing B S hS X.1 x) (regularLocalizationStalk B S hS X x) :=
    (toRegularLocalizationStalk B S hS X x).toAlgebra
  have h2 : IsLocalization (etaleLocalRing B S hS X.1 x)⁰
      (regularLocalizationStalk B S hS X x) := by
    rw [← regularSectionsStalk_eq_nonZeroDivisors B S hS X hwa hfin x]
    exact isLocalization_regularLocalizationStalk B S hS X x
  exact (IsLocalization.isLocalization_iff_of_ringEquiv _
    (meromorphicStalkIso B S hS X x).commRingCatIsoToRingEquiv).mp h2

end MeromorphicStalk

end AlgebraicGeometry.Space

end
