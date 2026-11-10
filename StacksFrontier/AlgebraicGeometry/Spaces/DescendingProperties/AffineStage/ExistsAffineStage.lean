module

public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.AffineStage.ChartPresentation

/-!
# An affine limit of algebraic spaces has an affine stage

Stacks 07SQ, over a terminal base, over an arbitrary base and for an index set in an arbitrary
universe, and Stacks 0A0R.
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe v u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace DescentSituation

section ChartModels

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : DescentSituation B S hS hZ I)

/-! ### Stacks 07SQ -/

/-- **Stacks 07SQ over a terminal base scheme.** In the situation of Stacks 084R over a terminal
base, if the limit `X` of the inverse system is an affine algebraic space then so is some stage
`X_i` with `i` at or beyond the distinguished index. The hypothesis on the base is removed in
`AlgebraicGeometry.Space.DescentSituation.exists_isAffineSpace_system_obj`, the form the source
states and the one carrying the tag.

The proof follows the source. An affine étale surjective chart `U₀ ⟶ X₀` of the distinguished
stage base changes to a system of affine charts `U_i` with limit `U`, which is an affine étale
surjective chart of `X`; so `Γ(U, 𝒪_U)` is an étale algebra with surjective spectrum over a
`u`-model `A` of `Γ(X, 𝒪_X)`
(`AlgebraicGeometry.Space.etale_globalFunctionsChartRestriction`). The ring of global functions
of the limit is the filtered colimit of those of the stages — Stacks 07SI for the structure
sheaf — so the commutative-algebra core
`MvPolynomial.exists_ge_etale_surjective_quotient_of_directed` presents that algebra by a square
family `q` of polynomials over the model `A_j` of a stage, étale and surjective there, whose base
change to `A` presents `Γ(U, 𝒪_U)`. Its coordinates are regular functions on `U`, and they and
the relations they satisfy descend to a stage `m ≥ j`
(`AlgebraicGeometry.Space.DescentSituation.exists_ge_eval₂_map_eq_zero`). That is the data of
display 70.5.10.1 at `m`, and
`AlgebraicGeometry.Space.DescentSituation.exists_isAffineSpace_system_obj_of_presentation`
concludes. -/
theorem exists_isAffineSpace_system_obj_of_isTerminal (hterminal : IsTerminal S)
    (hI : #I < B.cutoff.ord.cof) (hX : IsAffineSpace B S hS D.limitCone.pt) :
    ∃ i, D.base ≤ i ∧ IsAffineSpace B S hS (D.system.obj (op i)) := by
  classical
  have : Nonempty I := ⟨D.base⟩
  have : IsDirectedOrder I := inferInstance
  obtain ⟨U₀, chart, hU₀, hchartS, hchartE⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS
      (D.system.obj (op D.base)) (D.algebraicSpace D.base)).mp (D.quasiCompact D.base)
  have hchart : IsEtaleChart B S hS (D.system.obj (op D.base)) (CostructuredArrow.mk chart) :=
    (isEtale_iff_presheaf_of_yoneda B S hS chart).mp hchartE
  have hchartSurj : IsSurjective B S hS chart :=
    isSurjective_of_presheafSurjective B S hS chart hchartS
  set C := D.toLimitSituation.chartSystem ⟨U₀, hU₀⟩ chart with hCdef
  set L := D.toLimitSituation.chartLimitBridge ⟨U₀, hU₀⟩ chart hI with hLdef
  -- the global functions of the limit chart are an étale algebra with surjective spectrum
  obtain ⟨hEt, hSu⟩ := etale_globalFunctionsChartRestriction B S hS hterminal
    D.limitSpace (canonicalGlobalFunctionsModel B S hS D.limitSpace) hX
    (D.toLimitSituation.limitEtaleChart C L hchart) L.isAffine_pt
    (D.toLimitSituation.isSurjective_limitEtaleChart C L hchart hchartSurj)
  have hEt' : RingHom.Etale (D.limitChartHom C hchart L) := hEt
  have hSu' : Function.Surjective (PrimeSpectrum.comap (D.limitChartHom C hchart L)) := hSu
  let : Algebra (globalFunctionsModel B S hS D.limitSpace)
      (Γ((LimitSituation.stagesSchemeCone D.toLimitSituation C L).pt, ⊤) : Type u) :=
    (D.limitChartHom C hchart L).toAlgebra
  have : Algebra.Etale (globalFunctionsModel B S hS D.limitSpace)
      (Γ((LimitSituation.stagesSchemeCone D.toLimitSituation C L).pt, ⊤) : Type u) := hEt'
  have hds := D.directedSystem_modelTransition
  have hmodel := D.isStagesColimit_modelProjection hI
  -- the commutative-algebra core presents it over a stage
  obtain ⟨n, j, hj, q, hqE, hqS, ⟨ealg⟩⟩ :=
    MvPolynomial.exists_ge_etale_surjective_quotient_of_directed hmodel.hφ hmodel.hsurj
      hmodel.hzero (Γ((LimitSituation.stagesSchemeCone D.toLimitSituation C L).pt, ⊤) : Type u)
      hSu' D.base
  set x := fun k => ealg.symm (Ideal.Quotient.mk
    (Ideal.span (Set.range fun k => MvPolynomial.map (D.modelProjection j) (q k)))
    (MvPolynomial.X k)) with hx
  have hrelLim : ∀ l, MvPolynomial.eval₂ (D.limitChartHom C hchart L) x
      (MvPolynomial.map (D.modelProjection j) (q l)) = 0 := fun l =>
    eval₂_mk_X_eq_zero _ ealg l
  -- the coordinates and the relations descend to a stage
  obtain ⟨m, hm, y, hyt, hyrel⟩ :=
    D.exists_ge_eval₂_map_eq_zero C hchart L hI ⟨j, hj⟩ q x hrelLim
  have hrelGlim : ∀ l, MvPolynomial.eval₂ (D.limitChartHom C hchart L) x
      ((fun k => MvPolynomial.map (D.modelProjection m.1)
        (MvPolynomial.map (D.modelTransition j m.1 hm) (q k))) l) = 0 := by
    intro l
    change MvPolynomial.eval₂ _ _ (MvPolynomial.map (D.modelProjection m.1)
      (MvPolynomial.map (D.modelTransition j m.1 hm) (q l))) = 0
    rw [MvPolynomial.map_map_eq_of_comp hmodel.hφ hm (q l)]
    exact hrelLim l
  obtain ⟨i, hi, hiaff⟩ := D.exists_isAffineSpace_system_obj_of_presentation C hchart L
    hterminal hchartSurj hI hX m
    (fun k => MvPolynomial.map (D.modelTransition j m.1 hm) (q k)) y hyrel
    x hyt hrelGlim
    (bijective_coordinateHom_of_algEquiv ealg
      (funext fun k => (MvPolynomial.map_map_eq_of_comp hmodel.hφ hm (q k)).symm) _
      (fun _ => rfl) hrelGlim)
    (etale_presentationAlgebra_map_of_le
      (f := fun a b (h : a ≤ b) => D.modelTransition a b h) (show j ≤ m.1 from hm) q hqE)
    (surjective_comap_presentationStructureHom_map (D.modelTransition j m.1 hm) q hqS)
  exact ⟨i, m.2.trans hi, hiaff⟩

/-- **Stacks 07SQ.** In the situation of Stacks 084R, over an arbitrary base scheme, if the limit
`X` of the inverse system is an affine algebraic space then so is some stage `X_i` with `i` at or
beyond the distinguished index.

Affineness of an algebraic space is the absolute notion, taken over the terminal scheme, so the
whole descent may be read there: the relocalization along `S ⟶ Spec ℤ` carries the descent
situation over `S` to one over the terminal scheme, which is where the identification of an
affine algebraic space with the spectrum of its global functions is available, and affineness of
a presheaf and of its view over the terminal scheme are the same condition. This is the same
passage as for Stacks 084T,
`AlgebraicGeometry.Space.DescentSituation.exists_isAbsolutelySeparated_system_obj`.

The index set is asked to be small compared to the cofinality of the site's size cutoff. That is
the explicit form of the all-rings-in-the-site convention under which Stacks 07SF holds, and it
is used three times: to make the limit of the affine charts of the system an object of the site,
to make the ring of global functions of the limit the filtered colimit of those of the stages
(Stacks 07SI for the structure sheaf), and in the morphism descent system of Stacks 084W that
Stacks 084S is applied to. It is the same hypothesis the library's Stacks 084T and Stacks 086X
carry.

This is the case of an index set in the universe of the site; the registered statement,
`AlgebraicGeometry.Space.DescentSituation.exists_isAffineSpace_system_obj`, allows an index set
in an arbitrary universe. -/
theorem exists_isAffineSpace_system_obj_of_mk_lt (hI : #I < B.cutoff.ord.cof)
    (hX : IsAffineSpace B S hS D.limitCone.pt) :
    ∃ i, D.base ≤ i ∧ IsAffineSpace B S hS (D.system.obj (op i)) := by
  obtain ⟨i, hi, hres⟩ :=
    exists_isAffineSpace_system_obj_of_isTerminal (D := D.viewOverIntegers B S hS hZ)
      terminalIsTerminal hI
      ((isAffineSpace_viewOverIntegers_iff B S hS hZ (F := D.limitCone.pt)).2 hX)
  exact ⟨i, hi,
    (isAffineSpace_viewOverIntegers_iff B S hS hZ (F := D.system.obj (op i))).1 hres⟩

end ChartModels

end DescentSituation

/-! ### Stacks 07SQ for an index set in an arbitrary universe -/

/-- **Stacks 07SQ.** In the situation of Stacks 084R over a scheme `S` — a directed inverse
system of quasi-compact and quasi-separated algebraic spaces over `S` with affine transition
morphisms, with a chosen limit `X` and a chosen index `0` — if `X` is affine then so is some stage
`X_i` with `0 ≤ i`.

The index set may live in any universe; its cardinality is asked to be below the cofinality of
the size cutoff of the site, which is how the standing convention of Section 70.2 of the source
(every ring considered has its spectrum in the site) reads in this size model. Without it the
statement fails here: for fields `F_a` (`a` below the cofinality) of sizes cofinal in the
cutoff, the system `P¹_{F_a}` has no point over any object of the site, so its limit is the
empty, affine, scheme while no stage is affine.

The index set is replaced by an order-isomorphic one in the universe of the site,
`AlgebraicGeometry.Space.DescentSituation.exists_orderIso_of_lift_mk_lt`, along which the
situation is reindexed, and the case of an index set in that universe is
`AlgebraicGeometry.Space.DescentSituation.exists_isAffineSpace_system_obj_of_mk_lt`. -/
@[stacks 07SQ "Correction: the index set is taken smaller than the cofinality of the site's \
size cutoff, the form the convention of Section 70.2 takes in this size model; without it the \
statement is false here (a system of projective lines over fields of sizes cofinal in the \
cutoff has empty, hence affine, limit)"]
theorem DescentSituation.exists_isAffineSpace_system_obj {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type v} [Preorder I]
    [IsDirected I (· ≤ ·)] (D : DescentSituation B S hS hZ I)
    (hI : Cardinal.lift.{u} #I < Cardinal.lift.{v} B.cutoff.ord.cof)
    (hX : IsAffineSpace B S hS D.limitCone.pt) :
    ∃ i, D.base ≤ i ∧ IsAffineSpace B S hS (D.system.obj (op i)) := by
  obtain ⟨J, _, ⟨e⟩, hJ, hdir⟩ := DescentSituation.exists_orderIso_of_lift_mk_lt hI
  have _ : IsDirected J (· ≤ ·) := hdir inferInstance
  obtain ⟨j, hj, hjaff⟩ :=
    (D.reindex e).exists_isAffineSpace_system_obj_of_mk_lt hJ hX
  exact ⟨e j, (D.reindex_base_le_iff e j).1 hj, hjaff⟩

/-! ### Stacks 0A0R -/

section AffineOverBase

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hZ : B.Contains (⊤_ Scheme.{u})) {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]

/-- **Stacks 0A0R.** Let `Y` be a quasi-compact and quasi-separated algebraic space over `S` and
let `X = lim X_i` be a directed limit, over `Y` and with affine transition morphisms, of
quasi-compact and quasi-separated algebraic spaces over `S`, as in the standing situation of
Stacks 084R. If `X ⟶ Y` is affine then `X_i ⟶ Y` is affine for all `i` large enough.

This is the source's proof, assembled in
`AlgebraicGeometry.Space.DescentSituation.exists_isAffineHom_system_app_of_affineStage` from an
affine surjective étale chart `h_W ⟶ Y`, which exists because `Y` is quasi-compact: base
changing the situation along it is again a situation of Stacks 084R whose limit `X ×_Y W` is an
affine algebraic space, and affineness of a stage over `Y` descends from affineness of
`X_i ×_Y W` by the implication (4) ⇒ (2) of Stacks 03WG. That assembly carries the appeal to
Stacks 07SQ — an affine limit has an affine stage — as a hypothesis; here it is supplied by
`AlgebraicGeometry.Space.DescentSituation.exists_isAffineSpace_system_obj_of_mk_lt`, Stacks 07SQ
as proved above.

The index set is asked to be small compared to the cofinality of the site's size cutoff, the
size form of the convention of Section 70.2 that Stacks 07SQ needs as well. The conclusion is the
source's "for `i` large enough" in its strong reading: an index beyond which *every* stage is
affine over `Y`. -/
theorem DescentSituation.exists_isAffineHom_system_app (D : DescentSituation B S hS hZ I)
    (hI : #I < B.cutoff.ord.cof) (hY : IsAlgebraicSpace B S hS Y)
    (hYqc : IsQuasiCompactSpace B S hS Y)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y)
    (t : D.system ⟶ (Functor.const Iᵒᵖ).obj Y) (f : D.limitCone.pt ⟶ Y)
    (hf : ∀ j, D.limitCone.π.app j ≫ t.app j = f) (haff : IsAffineHom B S hS f) :
    ∃ i, D.base ≤ i ∧ ∀ k, i ≤ k → IsAffineHom B S hS (t.app (op k)) :=
  D.exists_isAffineHom_system_app_of_affineStage B S hS hZ hI hY hYqc hYqs t f hf haff
    fun E hIE hElim => E.exists_isAffineSpace_system_obj_of_mk_lt hIE hElim

end AffineOverBase

end AlgebraicGeometry.Space

end
