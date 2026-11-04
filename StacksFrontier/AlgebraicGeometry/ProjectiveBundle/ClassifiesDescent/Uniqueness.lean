module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.ClassifiesDescent.ExistsClassifies
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A section of `π` is determined by the quotient it classifies

* Clause (a) at an arbitrary section of `π`, and the degree-one dictionary as a value of the
  chart bijection.
* `Stacks.RelativeProj.eq_of_classifies_tautologicalDatum`,
  `Stacks.RelativeProj.isUniversal_tautologicalDatum` and
  `Stacks.RelativeProj.projectiveBundleSectionsEquiv`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.ModuleHomGlue

universe u

namespace Stacks.RelativeProj

open Stacks.Divisors

variable {X : Scheme.{u}} {F : X.Modules} [F.IsQuasicoherent]

variable {L : X.Modules}
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

/-! ### Clause (a) at an arbitrary section of `π` -/

section StandardOpen

open Opposite
open Stacks.AlgebraicGeometry.MorphismsIntoProj
open Stacks.AlgebraicGeometry.MorphismToProjUniversal (preimage_basicOpen_eq_nonvanishingOpen)
open Stacks.AlgebraicGeometry.ProjChartAlphaInstance
open Stacks.AlgebraicGeometry.ProjChartCocycleMatch (resTop_pullbackSectionHom)
open Stacks.AlgebraicGeometry.ProjDegreeOneRepresents
open Stacks.AlgebraicGeometry.ProjF1Dehomogenization
open Stacks.Chow.GenuineChern (resTop app_resTop)
open Stacks.SymGraded

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf

variable (V : X.Opens) (hV : IsAffineOpen V) (q : F ⟶ L)
  (e : L.over V ≅ SheafOfModules.unit (X.ringCatSheaf.over V))
  (σ : X ⟶ projectiveBundle X F) (hσ : σ ≫ projectiveBundleToBase X F = 𝟙 X)
  (α : (Scheme.Modules.pullback σ).obj (tautologicalDatumTwist F) ≅ L)

omit [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] in
/-- **The degree-one dictionary at an arbitrary classified section, over `⊤` rather than over
`V.ι ⁻¹ᵁ V`.**

`classifyingTrivialisationOfSection_hom_pullbackSection` is stated over `V.ι ⁻¹ᵁ V`, because the
pulled-back section the tautological map produces lives there;
`AlgebraicGeometry.Scheme.Opens.ι_preimage_self` says that open is `⊤`, but *not*
definitionally, so the transport is a genuine restriction map rather than a coincidence of terms.
`Stacks.AlgebraicGeometry.ProjChartCocycleMatch.resTop_pullbackSectionHom` performs it on the
source — restricting a pulled-back section is pulling it back to the smaller open — and
`Stacks.Chow.GenuineChern.app_resTop` carries it past the trivialisation. The value is therefore
the restriction of `e (q x)` along the same inclusion, and the consumer needs that only at an
`x` whose value is `1`, where the restriction is `1` by `map_one`. -/
public theorem classifyingTrivialisationOfSection_hom_pullbackSection_top
    (hα : (tautologicalDatum F).pullbackQuotientMap σ hσ ≫ α.hom = q)
    (hf : V.ι ⁻¹ᵁ V ≤ sectionChartMap V σ hσ hV ⁻¹ᵁ ⊤)
    (ht : (⊤ : V.toScheme.Opens) ≤ sectionChartMap V σ hσ hV ⁻¹ᵁ ⊤) (x : Γ(F, V)) :
    (classifyingTrivialisationOfSection V hV e σ hσ α).hom.val.app (op ⊤)
        (Scheme.Modules.pullbackSection (sectionChartMap V σ hσ hV)
          (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf
            ((schemeSheafGradedAlgebra F
              (isQuasicoherentPieces_of_isQuasicoherent F)).grading V) 1) ⊤ ⊤ ht
          (Stacks.ProjectiveBundleConormal.chartDegreeOneSection F
            (isQuasicoherentPieces_of_isQuasicoherent F) hV x))
      = resTop (SheafOfModules.unit V.toScheme.ringCatSheaf) V.ι_preimage_self.ge
          (ofPushforwardUnit V.ι ((trivializedQuotientHom V q e).val.app (op V) x)) :=
  (congrArg
      ((classifyingTrivialisationOfSection V hV e σ hσ α).hom.val.app (op ⊤))
      (resTop_pullbackSectionHom (sectionChartMap V σ hσ hV) _ ⊤ hf ht
        V.ι_preimage_self.ge _).symm).trans
    ((app_resTop (classifyingTrivialisationOfSection V hV e σ hσ α).hom
        V.ι_preimage_self.ge _).trans
      (congrArg (resTop (SheafOfModules.unit V.toScheme.ringCatSheaf) V.ι_preimage_self.ge)
        (classifyingTrivialisationOfSection_hom_pullbackSection V hV q e σ hσ α hα hf x)))

/-- A section of `𝒪_V` read in `Γ(V, ⊤)` through `V.ι_preimage_self` is `1` if its pushforward
reading is `1`. -/
private theorem resTop_ofPushforwardUnit_eq_one {x : (pushforwardUnit V.ι).val.obj (op V)}
    (hx : ofPushforwardUnit V.ι x = 1) :
    resTop (SheafOfModules.unit V.toScheme.ringCatSheaf) V.ι_preimage_self.ge
      (ofPushforwardUnit V.ι x) = (1 : Γ(V.toScheme, (⊤ : V.toScheme.Opens))) :=
  (congrArg (resTop (SheafOfModules.unit V.toScheme.ringCatSheaf) V.ι_preimage_self.ge) hx).trans
    (map_one (V.toScheme.presheaf.map (homOfLE V.ι_preimage_self.ge).op).hom)

omit [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] in
/-- **Clause (a) of [Stacks, Tag 0B3V] at an arbitrary section of `π : 𝐏(ℰ) ⟶ X`**: the chart
factorisation `Stacks.RelativeProj.sectionChartMap` of an arbitrary section `σ` lands wholly
inside the standard open of the degree-one element of a section `m₀` of `ℰ` whose trivialised
quotient is the unit.

**This is item 3 of the degree-one route to
`Stacks.RelativeProj.TautologicalDatum.IsUniversal.eq_of_classifies`, and it is where the
geometry of that route is.** For the glued section
`Stacks.RelativeProj.preimage_basicOpen_localDegreeOne_eq_top` gets it for nothing, because
`Stacks.RelativeProj.localChartMap` is `AlgebraicGeometry.Proj.fromOfGlobalSections` of an
explicit dehomogenisation and its preimages of standard opens are computed; `sectionChartMap` is
produced by `Stacks.AlgebraicGeometry.RelativeProj.chartHomEquivOver` and nothing is known about
it, so the standard open has to be reached through the *section* instead:

* the pulled-back degree-one section of `m₀` is carried by an **isomorphism** of `𝒪_V`-modules to
  `e (q m₀) = 1` — `classifyingTrivialisationOfSection_hom_pullbackSection_top`, which is item 2
  transported from `V.ι ⁻¹ᵁ V` to `⊤` — hence vanishes nowhere
  (`nonvanishingOpen_pullbackSection_eq_top`);
* the preimage of the standard open *is* that nonvanishing open, by
  `Stacks.AlgebraicGeometry.MorphismToProjUniversal.preimage_basicOpen_eq_nonvanishingOpen`,
  which is stated for a morphism through `U_1` and is fed
  `Stacks.AlgebraicGeometry.ProjDegreeOneRepresents.factorThroughDegreeOpenOne` at
  `…ProjDegreeOneRepresents.degreeOpen_one_eq_top`, whose generation hypothesis is
  `Stacks.SymGraded.adjoin_grading_one_eq_top` — `Sym(ℰ)` is generated in degree one over an
  affine open.

Such an `m₀` exists over an affine open on which `ℒ` is trivialised, by
`Stacks.RelativeProj.exists_app_trivializedQuotientHom_eq_one` together with
`Stacks.RelativeProj.surjective_app_of_isAffineOpen_of_epi`. -/
public theorem preimage_basicOpen_sectionChartMap_eq_top
    (hα : (tautologicalDatum F).pullbackQuotientMap σ hσ ≫ α.hom = q)
    {m₀ : Γ(F, V)}
    (hm₀ : ofPushforwardUnit V.ι
      ((trivializedQuotientHom V q e).val.app (op V) m₀) = 1) :
    sectionChartMap V σ hσ hV ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
        ((schemeSheafGradedAlgebra F (isQuasicoherentPieces_of_isQuasicoherent F)).grading V)
        (localDegreeOne V m₀).1 = ⊤ := by
  have htop : AlgebraicGeometry.Proj.degreeOpen
      ((schemeSheafGradedAlgebra F
        (isQuasicoherentPieces_of_isQuasicoherent F)).grading V) 1 = ⊤ :=
    degreeOpen_one_eq_top _ (adjoin_grading_one_eq_top F V
      (isQuasicoherentPieces_of_isQuasicoherent F) hV)
  have hφ₀ := toProj_factorThroughDegreeOpenOne
    ((schemeSheafGradedAlgebra F (isQuasicoherentPieces_of_isQuasicoherent F)).grading V)
    htop (sectionChartMap V σ hσ hV)
  have ht : (⊤ : V.toScheme.Opens) ≤ sectionChartMap V σ hσ hV ⁻¹ᵁ ⊤ := le_top
  have hf : V.ι ⁻¹ᵁ V ≤ sectionChartMap V σ hσ hV ⁻¹ᵁ ⊤ := le_top
  have ht0 : (⊤ : V.toScheme.Opens) ≤ toProj _ (factorThroughDegreeOpenOne
      ((schemeSheafGradedAlgebra F
        (isQuasicoherentPieces_of_isQuasicoherent F)).grading V)
      htop (sectionChartMap V σ hσ hV)) ⁻¹ᵁ ⊤ := le_top
  refine (congrArg (fun k : V.toScheme ⟶ AlgebraicGeometry.Proj
      ((schemeSheafGradedAlgebra F
        (isQuasicoherentPieces_of_isQuasicoherent F)).grading V) =>
      k ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen _ (localDegreeOne V m₀).1) hφ₀).symm.trans ?_
  refine (preimage_basicOpen_eq_nonvanishingOpen _ _ (localDegreeOne V m₀)).trans ?_
  refine nonvanishingOpen_pullbackSection_eq_top hφ₀ _
    (classifyingTrivialisationOfSection V hV e σ hσ α) ht0 ht
    (chartDegreeOneSection_eq_degreeSection_localDegreeOne V hV m₀).symm
    (pullbackDegreeSection_eq_pullbackSection _ _ (localDegreeOne V m₀) ht0) ?_ isUnit_one
  exact (classifyingTrivialisationOfSection_hom_pullbackSection_top
    V hV q e σ hσ α hα hf ht m₀).trans (resTop_ofPushforwardUnit_eq_one V hm₀)

end StandardOpen


/-! ### The degree-one dictionary as a value of the chart bijection -/

section ChartValue

open Opposite
open Stacks.AlgebraicGeometry.ProjF1Dehomogenization
open Stacks.AlgebraicGeometry.ProjF1DegreeOneChart (chartHomEquiv)
open Stacks.Chow.GenuineChern (resTop)
open Stacks.SymGraded
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistingSheaf degreeSection)

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf

/-- **The scalar action on the unit module is multiplication.** True by `rfl`:
`SheafOfModules.unit R` has `R` itself as its sections and the ring acting on itself. Named
because the goal below is an equation in `Γ(unit 𝒪_Y, ⊤)` whose right-hand side has to be read
in `Γ(Y, ⊤)`, and no lemma says the two actions agree. -/
public theorem unit_smul_eq_mul {Y : Scheme.{u}} (U : Y.Opens) (c x : Γ(Y, U)) :
    c • (x : Γ(SheafOfModules.unit Y.ringCatSheaf, U)) = c * x := rfl

/-- **Reading a scalar off a frame.** If a trivialisation `ε` of an `𝒪_Y`-module carries `u` to
`r` and `u₀` to `w`, and `u` is `c` times `u₀`, then `c · w = r`.

**Everything is a variable**, and the three identifications `hv`, `huv`, `hu0` are *arguments*:
the consumer meets its two sections in two spellings — the one
`Stacks.TwistPullbackRatio.pullbackSection_degreeSection_eq_smul` produces, over the standard
open, and the one `classifyingTrivialisationOfSection_hom_pullbackSection_top` consumes, over
`⊤` — and substituting between them at the projective bundle's twist is exactly the `congrArg`
the heartbeat note of `comp_val_app_apply` measures as prohibitive. Here the module and the
trivialisation are opaque, so each substitution is a metavariable assignment. -/
public theorem eq_of_smul_frame_app {Y : Scheme.{u}} (M : Y.Modules)
    (ε : M ≅ SheafOfModules.unit Y.ringCatSheaf)
    {v v₀ u u₀ : Γ(M, (⊤ : Y.Opens))} {c r w : Γ(Y, (⊤ : Y.Opens))}
    (hv : v = (M.smul c).hom v₀) (huv : u = v) (hu0 : u₀ = v₀)
    (h1 : ε.hom.val.app (op ⊤) u = r)
    (h0 : ε.hom.val.app (op ⊤) u₀ = w) : c * w = r := by
  subst huv
  subst hu0
  subst hv
  subst h0
  refine Eq.symm (h1.symm.trans ?_)
  refine Eq.trans (Scheme.Modules.Hom.app_smul ε.hom c u₀) ?_
  exact unit_smul_eq_mul ⊤ c _

variable (V : X.Opens) (hV : IsAffineOpen V) (q : F ⟶ L)
  (e : L.over V ≅ SheafOfModules.unit (X.ringCatSheaf.over V))
  (σ : X ⟶ projectiveBundle X F) (hσ : σ ≫ projectiveBundleToBase X F = 𝟙 X)
  (α : (Scheme.Modules.pullback σ).obj (tautologicalDatumTwist F) ≅ L)

omit [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] in
/-- **The degree-one dictionary at an arbitrary classified section, as a value of the chart
bijection.** For a section `σ` of `π` classifying `q : ℰ ↠ ℒ` by `α`, a trivialisation `e` of `ℒ`
over an affine open `V` and a section `m₀` of `ℰ` whose trivialised quotient is the unit, the
chart homomorphism of `Stacks.RelativeProj.sectionChartMap` sends the fraction
`localDegreeOne m / localDegreeOne m₀` to `e (q m)`.

**This is the form the uniqueness clause consumes.**
`Stacks.AlgebraicGeometry.ProjF1DegreeOneChart.eq_of_chartHomEquiv_eq` compares *chart
homomorphisms*, and `classifyingTrivialisationOfSection_hom_pullbackSection_top` — item 2 of the
degree-one route — computes a *section*; this is the bridge. The chart homomorphism appears as
the scalar of `Stacks.TwistPullbackRatio.pullbackSection_degreeSection_eq_smul`, which is proved
at an arbitrary morphism into `Proj` landing in a standard open and is therefore available at
`sectionChartMap` as soon as `preimage_basicOpen_sectionChartMap_eq_top` — item 3 — supplies that
hypothesis. Identifying that scalar with `e (q m)` is `eq_of_smul_frame_app` at the trivialisation
`classifyingTrivialisationOfSection`, the frame being the pulled-back degree-one section of `m₀`,
which item 2 carries to `1`.

So no choice of frame and no pinning isomorphism is read off: the frame enters only through the
value `1` that item 2 gives it. -/
public theorem chartHomEquiv_sectionChartMap_localDegreeOne
    (hα : (tautologicalDatum F).pullbackQuotientMap σ hσ ≫ α.hom = q)
    {m₀ : Γ(F, V)}
    (hm₀ : ofPushforwardUnit V.ι
      ((trivializedQuotientHom V q e).val.app (op V) m₀) = 1)
    (m : Γ(F, V)) :
    (chartHomEquiv ((schemeSheafGradedAlgebra F
            (isQuasicoherentPieces_of_isQuasicoherent F)).grading V)
          (localDegreeOne V m₀).2 Nat.one_pos V.toScheme
          ⟨sectionChartMap V σ hσ hV,
            preimage_basicOpen_sectionChartMap_eq_top V hV q e σ hσ α hα hm₀⟩).hom
        (HomogeneousLocalization.Away.mk _ (localDegreeOne V m₀).2 1
          (localDegreeOne V m).1 (by simp))
      = resTop (SheafOfModules.unit V.toScheme.ringCatSheaf) V.ι_preimage_self.ge
          (ofPushforwardUnit V.ι
            ((trivializedQuotientHom V q e).val.app (op V) m)) := by
  have hg := preimage_basicOpen_sectionChartMap_eq_top V hV q e σ hσ α hα hm₀
  have hf : V.ι ⁻¹ᵁ V ≤ sectionChartMap V σ hσ hV ⁻¹ᵁ ⊤ := le_top
  have ht : (⊤ : V.toScheme.Opens) ≤ sectionChartMap V σ hσ hV ⁻¹ᵁ ⊤ := le_top
  have hsm := Stacks.TwistPullbackRatio.pullbackSection_degreeSection_eq_smul
    ((schemeSheafGradedAlgebra F (isQuasicoherentPieces_of_isQuasicoherent F)).grading V)
    (localDegreeOne V m).2 (localDegreeOne V m₀).2 (sectionChartMap V σ hσ hV) hg
  have huv := fun x : Γ(F, V) =>
    (congrArg
        (Scheme.Modules.pullbackSection (sectionChartMap V σ hσ hV) _ ⊤ ⊤ ht)
        (chartDegreeOneSection_eq_degreeSection_localDegreeOne V hV x)).trans
      (Scheme.Modules.pullbackSection_res (sectionChartMap V σ hσ hV) _ le_top ⊤ hg.ge _).symm
  exact (mul_one _).symm.trans
    (eq_of_smul_frame_app _ (classifyingTrivialisationOfSection V hV e σ hσ α)
      hsm (huv m) (huv m₀)
      (classifyingTrivialisationOfSection_hom_pullbackSection_top V hV q e σ hσ α hα hf ht m)
      ((classifyingTrivialisationOfSection_hom_pullbackSection_top
        V hV q e σ hσ α hα hf ht m₀).trans (resTop_ofPushforwardUnit_eq_one V hm₀)))

end ChartValue

/-! ### `eq_of_classifies` and the universal property -/

section Uniqueness

open Opposite
open Stacks.AlgebraicGeometry.ProjF1Dehomogenization
open Stacks.AlgebraicGeometry.ProjF1DegreeOneChart (chartHomEquiv)
open Stacks.SymGraded

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf

/-- **Every degree-one element of the chart ring over `V` is `Stacks.RelativeProj.localDegreeOne`
of a section of `ℰ` over `V`.** The degree-one part of `Γ(V, Sym ℰ)` is the sections of
`Sym¹(ℰ)`, and the generator `ℰ ⟶ Sym¹(ℰ)` is an isomorphism
(`AlgebraicGeometry.Scheme.Modules.symmetricAlgebraGenIso`), so the family
`localDegreeOne V · ` already exhausts it. This is what turns the dictionary
`chartHomEquiv_sectionChartMap_localDegreeOne`, which is indexed by sections of `ℰ`, into the
hypothesis of
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.away_ringHom_ext_degree_one`,
which quantifies over the degree-one part. -/
public theorem exists_localDegreeOne_eq (V : X.Opens)
    {z : (schemeSheafGradedAlgebra F
      (isQuasicoherentPieces_of_isQuasicoherent F)).sectionRing V}
    (hz : z ∈ (schemeSheafGradedAlgebra F
      (isQuasicoherentPieces_of_isQuasicoherent F)).grading V 1) :
    ∃ m : Γ(F, V), (localDegreeOne V m).1 = z := by
  obtain ⟨y, rfl⟩ := hz
  refine ⟨(Scheme.Modules.symmetricAlgebraGenIso X F).inv.val.app (op V) y,
    congrArg (DirectSum.of _ 1) ?_⟩
  exact (SheafOfModules.comp_val_app_apply
      (Scheme.Modules.symmetricAlgebraGenIso X F).inv
      (Scheme.Modules.symmetricAlgebraGen X F) (op V) y).symm.trans
    (congrArg
      (fun φ : (Scheme.Modules.symmetricAlgebra X F).piece 1 ⟶
          (Scheme.Modules.symmetricAlgebra X F).piece 1 => φ.val.app (op V) y)
      (Scheme.Modules.symmetricAlgebraGenIso X F).inv_hom_id)

/-- **Two sections of `π : 𝐏(ℰ) ⟶ X` classifying the same invertible quotient agree over an
affine open on which the quotient is trivialised.**

This is the uniqueness clause of [Stacks, Tag 0B3V] localised on the base, and it is where the
four items of the degree-one route meet:

* a section `m₀` of `ℰ` over `V` whose trivialised quotient is the unit exists, by
  `exists_app_trivializedQuotientHom_eq_one` at
  `surjective_app_of_isAffineOpen_of_epi`;
* `preimage_basicOpen_sectionChartMap_eq_top` — item 3 — puts both chart factorisations inside
  the standard open of its degree-one element, so both are in the domain of
  `Stacks.AlgebraicGeometry.ProjF1DegreeOneChart.chartHomEquiv`;
* `chartHomEquiv_sectionChartMap_localDegreeOne` — items 1 and 2 — says that both chart
  homomorphisms send `localDegreeOne m / localDegreeOne m₀` to the *same* value `e (q m)`, for
  every section `m` of `ℰ`, and `exists_localDegreeOne_eq` says those `m` exhaust the degree-one
  part;
* `…RelativeProjBridge.SheafGradedAlgebra.away_ringHom_ext_degree_one` — item 4 — concludes that
  the two chart homomorphisms are equal, which by
  `…ProjF1DegreeOneChart.eq_of_chartHomEquiv_eq` makes the two chart factorisations equal.

Composing with the chart (`sectionChartMap_comp_chart`) and cancelling the isomorphism
`Stacks.RelativeProj.bundlePresentationIso` then gives `V.ι ≫ σ = V.ι ≫ σ'`.

**`Stacks.AlgebraicGeometry.RelativeProj.comp_chart_injective` is not used**, and cannot be: it
goes from an equality of the composites with the chart to an equality of the chart morphisms,
whereas the route produces the chart morphisms' equality first and needs the composites' equality.
The step in that direction is `congrArg` and `CategoryTheory.cancel_mono`. -/
public theorem ι_comp_eq_of_classifies (V : X.Opens) (hV : IsAffineOpen V) (q : F ⟶ L) [Epi q]
    (e : L.over V ≅ SheafOfModules.unit (X.ringCatSheaf.over V))
    (σ : X ⟶ projectiveBundle X F) (hσ : σ ≫ projectiveBundleToBase X F = 𝟙 X)
    (α : (Scheme.Modules.pullback σ).obj (tautologicalDatumTwist F) ≅ L)
    (hα : (tautologicalDatum F).pullbackQuotientMap σ hσ ≫ α.hom = q)
    (σ' : X ⟶ projectiveBundle X F) (hσ' : σ' ≫ projectiveBundleToBase X F = 𝟙 X)
    (α' : (Scheme.Modules.pullback σ').obj (tautologicalDatumTwist F) ≅ L)
    (hα' : (tautologicalDatum F).pullbackQuotientMap σ' hσ' ≫ α'.hom = q) :
    V.ι ≫ σ = V.ι ≫ σ' := by
  obtain ⟨m₀, hm₀⟩ := exists_app_trivializedQuotientHom_eq_one V q e
    (surjective_app_of_isAffineOpen_of_epi q hV)
  have hchart : chartHomEquiv ((schemeSheafGradedAlgebra F
            (isQuasicoherentPieces_of_isQuasicoherent F)).grading V)
          (localDegreeOne V m₀).2 Nat.one_pos V.toScheme
          ⟨sectionChartMap V σ hσ hV,
            preimage_basicOpen_sectionChartMap_eq_top V hV q e σ hσ α hα hm₀⟩
      = chartHomEquiv ((schemeSheafGradedAlgebra F
            (isQuasicoherentPieces_of_isQuasicoherent F)).grading V)
          (localDegreeOne V m₀).2 Nat.one_pos V.toScheme
          ⟨sectionChartMap V σ' hσ' hV,
            preimage_basicOpen_sectionChartMap_eq_top V hV q e σ' hσ' α' hα' hm₀⟩ := by
    refine CommRingCat.hom_ext
      (Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.away_ringHom_ext_degree_one
        _ V (adjoin_grading_one_eq_top F V (isQuasicoherentPieces_of_isQuasicoherent F) hV)
        (localDegreeOne V m₀).2 fun z hz => ?_)
    obtain ⟨m, hmz⟩ := exists_localDegreeOne_eq V hz
    subst hmz
    exact (chartHomEquiv_sectionChartMap_localDegreeOne V hV q e σ hσ α hα hm₀ m).trans
      (chartHomEquiv_sectionChartMap_localDegreeOne V hV q e σ' hσ' α' hα' hm₀ m).symm
  have hmap := Stacks.AlgebraicGeometry.ProjF1DegreeOneChart.eq_of_chartHomEquiv_eq
    ((schemeSheafGradedAlgebra F (isQuasicoherentPieces_of_isQuasicoherent F)).grading V)
    (localDegreeOne V m₀).2 Nat.one_pos _ _ hchart
  exact (cancel_mono (bundlePresentationIso F).inv).mp
    ((sectionChartMap_comp_chart V σ hσ hV).trans
      ((congrArg (fun k : V.toScheme ⟶ AlgebraicGeometry.Proj ((schemeSheafGradedAlgebra F
            (isQuasicoherentPieces_of_isQuasicoherent F)).grading V) =>
          k ≫ (symGradedBundle F).chart V hV) hmap).trans
        (sectionChartMap_comp_chart V σ' hσ' hV).symm))

/-- **A section of `π : 𝐏(ℰ) ⟶ X` is determined by the invertible quotient it classifies.**

This is the second field of `Stacks.RelativeProj.TautologicalDatum.IsUniversal` for the
repository's own tautological datum, and the half of [Stacks, Tag 0B3V]'s bijection that
`exists_classifies_tautologicalDatum` does not give.

The trivialising affine opens of `ℒ` cover `X` (`exists_trivAffineOpen_mem_le`),
`ι_comp_eq_of_classifies` gives the agreement over each of them, and a morphism out of a scheme
is determined on an open cover (`AlgebraicGeometry.Scheme.Cover.hom_ext`). -/
@[ega "II 4.2.3" "partial"]
public theorem eq_of_classifies_tautologicalDatum (σ σ' : X ⟶ projectiveBundle X F)
    (hσ : σ ≫ projectiveBundleToBase X F = 𝟙 X)
    (hσ' : σ' ≫ projectiveBundleToBase X F = 𝟙 X)
    (Q : Stacks.Divisors.InvertibleQuotient X F)
    (h : (tautologicalDatum F).Classifies σ hσ Q)
    (h' : (tautologicalDatum F).Classifies σ' hσ' Q) : σ = σ' := by
  have : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property Q.L :=
    Q.invertible
  have : Epi Q.q := Q.epi
  obtain ⟨α, hα⟩ := h
  obtain ⟨α', hα'⟩ := h'
  have hcov : TopologicalSpace.IsOpenCover (fun Vt : TrivAffineOpens Q.L => Vt.1.1) :=
    top_le_iff.mp fun x _ => by
      obtain ⟨Vt, hxV, -⟩ := exists_trivAffineOpen_mem_le (L := Q.L) (U := ⊤) (x := x) trivial
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨Vt, hxV⟩
  refine Scheme.Cover.hom_ext
    (X.openCoverOfIsOpenCover (fun Vt : TrivAffineOpens Q.L => Vt.1.1) hcov) σ σ' fun Vt => ?_
  exact ι_comp_eq_of_classifies Vt.1.1 Vt.1.2 Q.q Vt.2.some σ hσ α hα σ' hσ' α' hα'

/-- **The tautological datum of the projective bundle is universal.** Both fields are
proved: `exists_classifies_tautologicalDatum` and `eq_of_classifies_tautologicalDatum`. With this
instance `Stacks.RelativeProj.TautologicalDatum.bijective_sectionsMap`,
`…TautologicalDatum.sectionsEquivInvertibleQuotients` and its two normalisation lemmas become
unconditional for `Stacks.RelativeProj.tautologicalDatum`. -/
@[ega "II 4.2.5" "special case"]
public instance isUniversal_tautologicalDatum : (tautologicalDatum F).IsUniversal where
  exists_classifies := exists_classifies_tautologicalDatum
  eq_of_classifies := eq_of_classifies_tautologicalDatum

/-- **[Stacks, Tag 0B3V]: the sections of `π : 𝐏(ℰ) ⟶ X` are in bijection with the invertible
quotients of `ℰ` up to isomorphism**, for an arbitrary quasi-coherent `ℰ` on an arbitrary scheme
`X`, with no hypothesis of any kind.

The map is `Stacks.RelativeProj.TautologicalDatum.sectionsMap` of the repository's tautological
datum, i.e. a section goes to the class of the invertible quotient it pulls back from the
tautological one, so the bijection is normalised by the tautological quotient:
`…TautologicalDatum.sectionsEquivInvertibleQuotients_eq_iff` says it sends `σ` to the class of
`Q` exactly when `σ` classifies `Q`.

Surjectivity is `exists_classifies_tautologicalDatum` and injectivity is
`eq_of_classifies_tautologicalDatum`. -/
public def projectiveBundleSectionsEquiv :
    { σ : X ⟶ projectiveBundle X F // σ ≫ projectiveBundleToBase X F = 𝟙 X } ≃
      Stacks.Divisors.InvertibleQuotientClass X F :=
  (tautologicalDatum F).sectionsEquivInvertibleQuotients

/-- `projectiveBundleSectionsEquiv` is the tautological datum's bijection, so every statement
about the latter applies to it. -/
public theorem projectiveBundleSectionsEquiv_apply
    (σ : { σ : X ⟶ projectiveBundle X F // σ ≫ projectiveBundleToBase X F = 𝟙 X }) :
    projectiveBundleSectionsEquiv σ =
      Quotient.mk (Stacks.Divisors.invertibleQuotientSetoid X F)
        ((tautologicalDatum F).pullbackQuotient σ.1 σ.2) :=
  rfl

end Uniqueness


end Stacks.RelativeProj

end
