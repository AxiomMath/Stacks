module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartStalkLength
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleAtGeometricPointEquiv
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks 05WY: the critère de platitude par fibres on an algebraic space

Work in Situation 05WX: a scheme `S`, algebraic spaces `X`, `Y`, `Z` over `S` with morphisms
`f : X ⟶ Y` and `h : Y ⟶ Z`, a quasi-coherent `𝒪_X`-module `F` and a geometric point `x̄` of
`X`.  Writing `ȳ = f ∘ x̄` and `z̄ = h ∘ ȳ`, Stacks 05WY compares

1. the fibre `F_x̄ / 𝔪_z̄ F_x̄` of the geometric stalk is flat over the fibre
   `𝒪_{Y, ȳ} / 𝔪_z̄ 𝒪_{Y, ȳ}` of the étale local ring;
3. there are schemes `U ⟶ V ⟶ W` étale over `f` and `h` in two commuting squares, and a point
   `u` of `U` above the image of `x̄`, at which the fibre of `F|_U` is flat over the fibre of
   `V`.

This file states both conditions and proves them equivalent.  The composite `g = h ∘ f` of the
source is not named: the geometric point `z̄ = g ∘ x̄` is the image of `ȳ` under `h`, and the
homomorphism `𝒪_{Z, z̄} → 𝒪_{Y, ȳ}` it carries is the canonical one of Stacks 04NG for `h` at
`ȳ`.

## Main definitions

* `AlgebraicGeometry.Space.IsFibreFlatOverAtGeometricPoint`: condition (1).
* `Module.FlatQuotSMul`: flatness of `M/JM` over `T/I`, for a ring homomorphism `T → U`, an
  ideal `I` of `T`, the ideal `J` it generates in `U` and a `U`-module `M`.  Condition (1) and
  the local-ring reading of condition (3) are both instances of it.

## Main results

* `AlgebraicGeometry.Space.exists_flatQuotSMul_chart_iff_isFibreFlatOverAtGeometricPoint`:
  **Stacks 05WY**, conditions (1) and (3), with condition (3) read at some diagram.
* `AlgebraicGeometry.Space.forall_flatQuotSMul_chart_iff_isFibreFlatOverAtGeometricPoint`:
  **Stacks 05WY**, conditions (1) and (3), with condition (3) read at an *arbitrary chosen*
  diagram.  This is the "any choice works" content of the source's "choose a commutative
  diagram": together with the previous result the some-diagram and every-diagram readings of
  condition (3) agree.
* `AlgebraicGeometry.Space.exists_chartSquares`: a diagram as in condition (3) exists, which is
  what makes the two readings agree.
* Condition (3) with the point presented as the source presents it, a point `u` of `U` above
  `x` rather than a lift of `x̄`, is
  `Space.exists_chartPoint_isFibreFlatOnChartSquares_iff_isFibreFlatOverAtGeometricPoint`
  of `StacksFrontier/AlgebraicGeometry/Spaces/FibreFlatnessChartPoint.lean`, which also yields the
  independence of condition (1) from the choice of `x̄`.
* Condition (2) is
  `Space.isFlatOverAtGeometricPoint_fieldFibreSpace_iff_isFibreFlatOverAtGeometricPoint`
  of `StacksFrontier/AlgebraicGeometry/Spaces/FibreFlatnessFieldFibre.lean`, and
  `AlgebraicGeometry.Space.isFlatOverAtGeometricPoint_fieldFibreSpace_iff_exists_chartPoint`
  composes it with the equivalence proved here to reach condition (3).
* `Space.flatQuotSMul_chartZariskiModuleStalk_iff_isFibreFlatOverAtGeometricPoint` is the
  same equivalence at one fixed pointed pair of commuting squares of charts, which is where the
  mathematics is.
* `Module.Flat.quotSMul_baseChange_linearEquiv_iff`: Stacks 0584 (2) after dividing by an ideal
  of the base and transporting along an isomorphism with the base change.
* `AlgebraicGeometry.Space.flat_quotSMul_chartZariskiModuleStalk_iff_geometricModuleStalk`:
  Stacks 05VP after dividing by an ideal of a chart's local ring.
* `Module.Flat.quotient_ringEquiv_iff_of_isHenselization` and
  `AlgebraicGeometry.Space.flat_quotient_chartLocalRing_iff_quotient_etaleLocalRing`:
  Stacks 05WS across the comparison of Stacks 04KF, which crosses a universe.

## Implementation notes

Condition (3) of the source reads the fibre condition on the scheme-theoretic fibres `U_w` and
`V_w`; here it is read on their local rings, through the canonical identifications
`𝒪_{V_w, v} = 𝒪_{V, v}/𝔪_w 𝒪_{V, v}` and `(F_w)_u = (F|_U)_u/𝔪_w (F|_U)_u` which the source
records at the start of its proof.  Correspondingly the point `u` above `x̄` is presented as a
lift of `x̄` to the chart; by Stacks 05VN
(`AlgebraicGeometry.Space.exists_chartLift_of_chartPoint` and
`AlgebraicGeometry.Space.chartPoint_isChartPoint`) that is the same data.

**Condition (2) of the source is proved**, in
`StacksFrontier/AlgebraicGeometry/Spaces/FibreFlatnessFieldFibre.lean`.  It asserts flatness of the
pullback of `F` to the fibre `X_z = Spec(K) ×_{z, Z} X` over `Y_z = Spec(K) ×_{z, Z} Y` in the
sense of Stacks 05VV, for a representative `x : Spec(K) → X` of the point.  The fibre is
`AlgebraicGeometry.Space.fieldFibreSpace`, an algebraic space by Stacks 02X2
(`AlgebraicGeometry.isAlgebraicSpace_pullback`); the module is
`AlgebraicGeometry.Space.modulePullback`; and flatness over the target at a point in the sense
of Stacks 05VV is read at a geometric point as
`AlgebraicGeometry.Space.IsFlatOverAtGeometricPoint`, which is condition (2) of Stacks 05VU
(`AlgebraicGeometry.Space.isFlatOverAt_exists_chartDiagram_iff_isFlatOverAtGeometricPoint`).
The equivalence with condition (1) is
`Space.isFlatOverAtGeometricPoint_fieldFibreSpace_iff_isFibreFlatOverAtGeometricPoint`,
and
`AlgebraicGeometry.Space.isFlatOverAtGeometricPoint_fieldFibreSpace_iff_exists_chartPoint`
composes that with the equivalence proved here to reach condition (3).

The comparison is the source's.  At the étale local rings it is
`Module.Flat.flatQuotSMul_iff_flat_tensor_of_isPushout` of
`StacksFrontier/AlgebraicGeometry/Spaces/FibreFlatnessFieldFibreAlgebra.lean` composed with
`AlgebraicGeometry.Space.isFlatOverAtGeometricPoint_modulePullback_iff_flat_tensor` of
`StacksFrontier/AlgebraicGeometry/Spaces/FlatModuleBaseChangeTensor.lean`: with `R`, `A` the étale
local rings of `Y` and `X`, `I = 𝔪_z̄ 𝒪_{Y, ȳ}`, and `R'`, `A'` those of `Y_z` and `X_z`, the
first says that `F_x̄/𝔪_z̄ F_x̄` is flat over `R/I` exactly when `A' ⊗_A F_x̄` is flat over `R'`,
and the second identifies the latter with condition (2) through the base-change formula for the
geometric stalk of a pullback (Stacks 05VQ,
`AlgebraicGeometry.Space.geometricModuleStalkPullbackIso`).  Nothing in it asks quasi-coherence
of `F`.

The two inputs the comparison needs about the right-hand column come from the defining square of
the field fibre, where `𝒪_{Spec(K), k̄}` is a field
(`AlgebraicGeometry.Space.isField_etaleLocalRing_yoneda` applied to
`AlgebraicGeometry.isField_stalk_Spec_field`): `𝔪_z̄` extends to `⊥` in `𝒪_{Y_z, ȳ_z}`
(`AlgebraicGeometry.Space.map_maximalIdeal_etaleLocalRingMap_fieldFibreSpace_eq_bot`, and in the
spelling condition (1) fixes
`AlgebraicGeometry.Space.map_maximalIdeal_map_etaleLocalRingMap_eq_bot_of_point_eq`), and
`𝒪_{Y_z, ȳ_z}` is flat over the fibre `R/I`
(`Module.Flat.quotMaximalIdeal_of_isPushout_of_isField`, with the index of its étale local rings
moved to that spelling by
`AlgebraicGeometry.Space.flat_quotMaximalIdeal_etaleLocalRing_of_isPullback_of_isField`).  The
cartesian squares are `AlgebraicGeometry.Space.isPullback_fieldFibreSpace` and
`AlgebraicGeometry.Space.isPullback_fieldFibreSpace_snd` of
`StacksFrontier/AlgebraicGeometry/Spaces/FieldFibreSourceSquare.lean`, the first with the induced
morphism `AlgebraicGeometry.Space.fieldFibreSourceMap` — the functoriality of `fieldFibre` in the
source of the morphism.  Since `fieldFibre` is a plain presheaf `pullback`, the upper square is
pullback pasting and needs no algebraic-space input:
`X_z = Spec(K) ×_Z X = (Spec(K) ×_Z Y) ×_Y X = Y_z ×_Y X`.

Condition (2) is proved at *every* geometric point of `X_z`, not only at one above the
`K`-rational point that the source's representative defines; a geometric point above that point
is available outright from `AlgebraicGeometry.Space.exists_geometricRepresentative`, which
produces a geometric point above any point of a presheaf by taking the algebraic closure of a
field-valued representative.

On the source: it does not leave the independence of condition (2) from the representative of
`x` unjustified.  Having picked `x : Spec(K) → X`, it says the condition in (2) is independent of
that choice with "details omitted; this will also follow from the arguments below because the
other conditions do not depend on this choice" — and that deferral is sound, since (2) is proved
equivalent to (3) for *each* representative while (3) names none.  The formalization gets the
independence the same way:
`Space.isFlatOverAtGeometricPoint_fieldFibreSpace_iff_isFibreFlatOverAtGeometricPoint`
states condition (1) at the image of the geometric point of `X_z` in `|X|`, and condition (1)
depends only on that image, by
`AlgebraicGeometry.Space.isFibreFlatOverAtGeometricPoint_congr_of_image_eq`.

Condition (2) is stated a second time with `AlgebraicGeometry.Space.IsFlatOverAtPoint`, the
chartwise predicate of Definition 05VV that the source actually cites, as
`AlgebraicGeometry.Space.isFlatOverAtPoint_fieldFibreSpace_iff_isFibreFlatOverAtGeometricPoint`.
The bridge to the geometric-point reading is
`AlgebraicGeometry.Space.isFlatOverAtPoint_iff_isFlatOverAtGeometricPoint`: Stacks 05VU names
the point of the chart by `AlgebraicGeometry.Space.ChartPoint` and `IsFlatOverAtPoint` names it
by `(pointsEquivScheme …).symm u`, and the two agree because the comparison map
`AlgebraicGeometry.Space.pointsToScheme` of Stacks 03BV is the forward map of that bijection and
sends the class of a field-valued point to its scheme point
(`AlgebraicGeometry.Space.pointsToScheme_class`,
`AlgebraicGeometry.Space.chartPoint_pointsToScheme`).  That form asks quasi-coherence of the
pullback `F_z`, which is Stacks 03GA and holds here with no further hypothesis
(`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite`); the
geometric-point reading asks no quasi-coherence at all.

The independence of condition (1) from the choice of geometric point above the point of `|X|` is
`AlgebraicGeometry.Space.isFibreFlatOverAtGeometricPoint_congr_of_image_eq` of
`StacksFrontier/AlgebraicGeometry/Spaces/FibreFlatnessChartPoint.lean`.  It follows from the
equivalence proved here: two geometric points above one point of `|X|` lift to one chart at one
point of it by Stacks 05VN, and the chart condition depends only on the chart and that point, so
restating condition (3) with a point of the chart above `x` in place of a lift of `x̄`
(`Space.exists_chartPoint_isFibreFlatOnChartSquares_iff_isFibreFlatOverAtGeometricPoint`)
makes the two conditions the same statement.

The proof is the source's chain of identifications, in three steps, each with its own
declaration.  Stacks 05VP writes the geometric stalk as the base change of the Zariski stalk on
the chart along the faithfully flat `𝒪_{U, u} → 𝒪_{X, x̄}`, and Stacks 0584 (2) sees through
that base change after dividing by `𝔪_w`.  The étale local ring `𝒪_{Y, ȳ}` is the strict
henselization of `𝒪_{V, v}` by Stacks 04KF, and flatness over a local ring modulo an ideal
agrees with flatness over its strict henselization modulo the extension of that ideal
(Stacks 05WS).  Finally the maximal ideal of `𝒪_{Z, z̄}` is generated by `𝔪_w`
(`AlgebraicGeometry.Space.map_maximalIdeal_chartLocalRingToEtaleLocalRing`), so the fibre taken
in condition (1) is the one the chain produces; the two commuting squares of local rings that
this uses are `AlgebraicGeometry.Space.etaleLocalRingMap_comp_chartLocalRingToEtaleLocalRing`.

`𝒪_{V, v}` and its strict henselization in
`AlgebraicGeometry.Space.chartHenselizationTower` lie in the universe of the schemes, while
`𝒪_{Y, ȳ}` lies one universe up; `Module.Flat.quotient_ringEquiv_iff_of_isHenselization`
absorbs the difference by transporting along the comparison of Stacks 04KF, whose source and
target may lie in different universes.

Two restrictions of scalars that agree on elements but are built differently are identified
with `Module.ext`; the ideals of the statements are arguments carrying their defining
equations, so that a caller may substitute them.

## References

* [Stacks Project, Tag 05WY](https://stacks.math.columbia.edu/tag/05WY)
* [Stacks Project, Tag 05WX](https://stacks.math.columbia.edu/tag/05WX)
* [Stacks Project, Tag 05WS](https://stacks.math.columbia.edu/tag/05WS)
* [Stacks Project, Tag 05VP](https://stacks.math.columbia.edu/tag/05VP)
* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
* [Stacks Project, Tag 05VV](https://stacks.math.columbia.edu/tag/05VV)
* [Stacks Project, Tag 0584](https://stacks.math.columbia.edu/tag/0584)
* [Stacks Project, Tag 04KF](https://stacks.math.columbia.edu/tag/04KF)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
* [Stacks Project, Tag 0CZS](https://stacks.math.columbia.edu/tag/0CZS)
* [Stacks Project, Tag 0CZT](https://stacks.math.columbia.edu/tag/0CZT)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u v w x m

/-- **Flatness over a quotient of a local ring and over the corresponding quotient of a strict
henselization in another universe.** Let `T^{sh}` be a strict henselization of a local ring `C`
and let `γ : C → C^{sh}` be the composite of its structure map with a ring isomorphism
`T^{sh} ≃ C^{sh}`. For an ideal `I ⊆ 𝔪_C` and a module over `C^{sh}/I C^{sh}`, flatness over
`C/I` and over `C^{sh}/I C^{sh}` are the same condition. -/
@[sga "4 VIII 4.4" "more general", sga "4 XVII 5.5.29" "partial"]
public theorem Module.Flat.quotient_ringEquiv_iff_of_isHenselization
    {C Tsh : Type u} [CommRing C] [IsLocalRing C] [CommRing Tsh] [IsLocalRing Tsh]
    [Algebra C Tsh] (L : Type v) [Field L] [Algebra (ResidueField C) L]
    [IsHenselization C L Tsh] [IsSepClosure (ResidueField C) L]
    {Csh : Type w} [CommRing Csh] (e : Tsh ≃+* Csh) (γ : C →+* Csh)
    (hγ : γ = (e : Tsh →+* Csh).comp (algebraMap C Tsh))
    {I : Ideal C} (hI : I ≤ maximalIdeal C) (J : Ideal Csh) (hJ : J = I.map γ)
    (N : Type x) [AddCommGroup N] [Module (Csh ⧸ J) N] :
    letI : Module (C ⧸ I) N :=
      Module.compHom N (Ideal.quotientMap J γ (hJ ▸ Ideal.le_comap_map))
    (Module.Flat (C ⧸ I) N ↔ Module.Flat (Csh ⧸ J) N) := by
  let qm : (C ⧸ I) →+* (Csh ⧸ J) := Ideal.quotientMap J γ (hJ ▸ Ideal.le_comap_map)
  let : Module (C ⧸ I) N := Module.compHom N qm
  have hJ' : J = (I.map (algebraMap C Tsh)).map (e : Tsh →+* Csh) := by
    rw [Ideal.map_map, ← hγ, hJ]
  let qe : (Tsh ⧸ I.map (algebraMap C Tsh)) →+* (Csh ⧸ J) :=
    (Ideal.quotientEquiv _ J e hJ').toRingHom
  let : Module (Tsh ⧸ I.map (algebraMap C Tsh)) N := Module.compHom N qe
  have hfac (a : C ⧸ I) :
      qm a = qe (algebraMap (C ⧸ I) (Tsh ⧸ I.map (algebraMap C Tsh)) a) := by
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective a
    change Ideal.Quotient.mk J (γ c) = _
    rw [hγ]
    rfl
  let : IsScalarTower (C ⧸ I) (Tsh ⧸ I.map (algebraMap C Tsh)) N := by
    refine ⟨fun a b n => ?_⟩
    change qe (a • b) • n = qm a • (qe b • n)
    rw [Algebra.smul_def, map_mul, mul_smul, hfac]
  exact (Module.Flat.quotient_iff_of_isHenselization L hI N).trans
    (Module.Flat.quotient_ringEquiv_iff e _ J hJ' N)

/-- **Flatness of the fibre of a module over the fibre of the base.** For a ring homomorphism
`ψ : T → U`, an ideal `I` of `T`, the ideal `J = I U` it generates and a `U`-module `M`: the
module `M/JM` is flat over `T/I`, the scalars being restricted along the induced homomorphism
of quotients. -/
public abbrev Module.FlatQuotSMul {T U : Type*} [CommRing T] [CommRing U] (ψ : T →+* U)
    (I : Ideal T) (J : Ideal U) (hJ : J = I.map ψ) (M : Type*) [AddCommGroup M] [Module U M] :
    Prop :=
  letI : Module (T ⧸ I) (M ⧸ (J • (⊤ : Submodule U M))) :=
    Module.compHom _ (Ideal.quotientMap J ψ (hJ ▸ Ideal.le_comap_map))
  Module.Flat (T ⧸ I) (M ⧸ (J • (⊤ : Submodule U M)))

/-- In a commuting square of ring homomorphisms, the ideal generated by an ideal of the initial
ring in the terminal ring is computed along either side. -/
private theorem ideal_map_square {A C Ash Csh : Type*} [CommRing A] [CommRing C] [CommRing Ash]
    [CommRing Csh] (σ : A →+* C) (α : A →+* Ash) (γ : C →+* Csh) (τ : Ash →+* Csh)
    (hsq : γ.comp σ = τ.comp α) (I : Ideal A) :
    (I.map σ).map γ = (I.map α).map τ := by
  rw [Ideal.map_map, Ideal.map_map, hsq]

/-- Flatness over a ring is unchanged by replacing the module structure by one with the same
scalar multiplication. -/
private theorem flat_iff_of_module_ext {R M : Type*} [CommRing R] [AddCommGroup M]
    (P Q : Module R M)
    (w : ∀ (r : R) (m : M), (letI := P; r • m) = (letI := Q; r • m)) :
    (letI := P; Module.Flat R M) ↔ (letI := Q; Module.Flat R M) := by
  have hPQ : P = Q := Module.ext (funext fun r => funext fun m => w r m)
  subst hPQ
  exact Iff.rfl

/-- **The two restrictions of scalars in a commuting square of ring homomorphisms agree.** For
`δ ∘ σ = τ ∘ γ`, an ideal `I` of the initial ring and a module over the terminal ring, the
residue class of a scalar acts on the fibre of the module the same way along either side of the
square. -/
private theorem quotientMap_square_smul {C D Csh Dsh : Type*} [CommRing C] [CommRing D]
    [CommRing Csh] [CommRing Dsh] {σ : C →+* D} {δ : D →+* Dsh} {γ : C →+* Csh} {τ : Csh →+* Dsh}
    (hsq : δ.comp σ = τ.comp γ) {I : Ideal C} {Iσ : Ideal D} {Iγ : Ideal Csh} {P : Ideal Dsh}
    (hσ : I ≤ Iσ.comap σ) (hδ : Iσ ≤ P.comap δ) (hγ : I ≤ Iγ.comap γ) (hτ : Iγ ≤ P.comap τ)
    (M : Type*) [AddCommGroup M] [Module Dsh M] (r : C ⧸ I)
    (m : M ⧸ (P • (⊤ : Submodule Dsh M))) :
    (Ideal.quotientMap P δ hδ) ((Ideal.quotientMap Iσ σ hσ) r) • m =
      (Ideal.quotientMap P τ hτ) ((Ideal.quotientMap Iγ γ hγ) r) • m := by
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective r
  exact congrArg (fun y => (Ideal.Quotient.mk P y) • m) (RingHom.congr_fun hsq c)

/-- Flatness of the fibre of a module over the fibre of the base depends only on the two
ideals, not on the presentation of the second as generated by the first. -/
public theorem Module.flatQuotSMul_congr {T U : Type*} [CommRing T] [CommRing U] (ψ : T →+* U)
    {I I' : Ideal T} {J J' : Ideal U} (hI : I = I') (hJJ : J = J')
    (hJ : J = I.map ψ) (hJ' : J' = I'.map ψ) (M : Type*) [AddCommGroup M] [Module U M] :
    Module.FlatQuotSMul ψ I J hJ M ↔ Module.FlatQuotSMul ψ I' J' hJ' M := by
  subst hI
  subst hJJ
  exact Iff.rfl

/-- On the quotient of a module by an extended ideal, the residue class of a scalar acts as the
scalar itself. -/
private theorem quotIdealSMul_mk_smul {T : Type*} [CommRing T] (I : Ideal T) (M : Type*)
    [AddCommGroup M] [Module T M] (d : T) (z : M ⧸ (I • (⊤ : Submodule T M))) :
    (Ideal.Quotient.mk I d) • z = d • z := by
  induction z using Submodule.Quotient.induction_on with
  | _ m => rw [← Submodule.Quotient.mk_smul, Module.Quotient.mk_smul_mk]

open scoped TensorProduct in
/-- **Stacks 0584 (2) on fibres.** Let `D → D'` be faithfully flat, let `K` be an ideal of `D`,
let `M` be a `D`-module and let `G` be a `D'`-module isomorphic to the base change `D' ⊗_D M`.
For a ring `R₀` mapping to `D/K`, flatness of `M/KM` and of `G/K G` over `R₀` are the same
condition. -/
public theorem Module.Flat.quotSMul_baseChange_linearEquiv_iff
    {D D' : Type*} [CommRing D] [CommRing D'] [Algebra D D'] [Module.FaithfullyFlat D D']
    (K : Ideal D) {M : Type*} [AddCommGroup M] [Module D M]
    {G : Type*} [AddCommGroup G] [Module D' G] (e : D' ⊗[D] M ≃ₗ[D'] G)
    {R₀ : Type*} [CommRing R₀] (ρ : R₀ →+* D ⧸ K) :
    letI : Module R₀ (M ⧸ (K • (⊤ : Submodule D M))) := Module.compHom _ ρ
    letI : Module R₀ (G ⧸ (K.map (algebraMap D D') • (⊤ : Submodule D' G))) :=
      Module.compHom _
        ((Ideal.quotientMap _ (algebraMap D D') Ideal.le_comap_map).comp ρ)
    (Module.Flat R₀ (M ⧸ (K • (⊤ : Submodule D M))) ↔
      Module.Flat R₀ (G ⧸ (K.map (algebraMap D D') • (⊤ : Submodule D' G)))) := by
  let ρ' : R₀ →+* D' ⧸ K.map (algebraMap D D') :=
    (Ideal.quotientMap _ (algebraMap D D') Ideal.le_comap_map).comp ρ
  let : Module R₀ (M ⧸ (K • (⊤ : Submodule D M))) := Module.compHom _ ρ
  let : Module R₀ (G ⧸ (K.map (algebraMap D D') • (⊤ : Submodule D' G))) :=
    Module.compHom _ ρ'
  let : Module R₀ ((D' ⊗[D] M) ⧸
      (K.map (algebraMap D D') • (⊤ : Submodule D' (D' ⊗[D] M)))) := Module.compHom _ ρ'
  let : Algebra R₀ (D ⧸ K) := ρ.toAlgebra
  let : Algebra R₀ (D' ⧸ K.map (algebraMap D D')) := ρ'.toAlgebra
  let : Algebra (D ⧸ K) (D' ⧸ K.map (algebraMap D D')) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  let : IsScalarTower R₀ (D ⧸ K) (D' ⧸ K.map (algebraMap D D')) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower R₀ (D ⧸ K) (M ⧸ (K • (⊤ : Submodule D M))) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : IsScalarTower R₀ (D' ⧸ K.map (algebraMap D D')) ((D' ⊗[D] M) ⧸
      (K.map (algebraMap D D') • (⊤ : Submodule D' (D' ⊗[D] M)))) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  refine Iff.trans (Module.Flat.quotSMul_baseChange_iff_of_faithfullyFlat D' K M).symm ?_
  let eT : ((D' ⊗[D] M) ⧸ (K.map (algebraMap D D') • (⊤ : Submodule D' (D' ⊗[D] M))))
      ≃ₗ[D'] (G ⧸ (K.map (algebraMap D D') • (⊤ : Submodule D' G))) :=
    Submodule.Quotient.equiv _ _ e (by
      rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range])
  exact Module.Flat.equiv_iff
    { toFun := eT
      map_add' := map_add eT
      map_smul' := fun r z => by
        change eT (ρ' r • z) = ρ' r • eT z
        obtain ⟨d, hd⟩ := Ideal.Quotient.mk_surjective (ρ' r)
        rw [← hd, quotIdealSMul_mk_smul, quotIdealSMul_mk_smul]
        exact eT.map_smul d z
      invFun := eT.symm
      left_inv := eT.left_inv
      right_inv := eT.right_inv }

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Condition (1) of Stacks 05WY -/

/-- **Condition (1) of Stacks 05WY.** For `f : X ⟶ Y` and `h : Y ⟶ Z` morphisms of algebraic
spaces, a geometric point `x̄` of `X` with `ȳ = f ∘ x̄` and `z̄ = h ∘ ȳ`, and an `𝒪_X`-module
`F`: the fibre `F_x̄ / 𝔪_z̄ F_x̄` of the geometric stalk is flat over the fibre
`𝒪_{Y, ȳ} / 𝔪_z̄ 𝒪_{Y, ȳ}` of the étale local ring.

The composite `g = h ∘ f` of the source is not named: the geometric point `z̄ = g ∘ x̄` and the
map `𝒪_{Z, z̄} → 𝒪_{Y, ȳ}` it carries are taken as the image of `ȳ` under `h` and the
canonical homomorphism of Stacks 04NG for `h` at `ȳ`. -/
def IsFibreFlatOverAtGeometricPoint {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (h : Y ⟶ Z)
    (F : Modules.{u, m} B S hS X.1 X.2) (xbar : GeometricPoint B S hS X.1) : Prop :=
  let : IsLocalRing ↥(etaleLocalRing B S hS Z.1
      (geometricPointMap h.hom (geometricPointMap f.hom xbar))) :=
    isLocalRing_etaleLocalRing B S hS Z.1 Z.2 _
  Module.FlatQuotSMul (etaleLocalRingMap X.2 f.hom xbar)
    ((maximalIdeal ↥(etaleLocalRing B S hS Z.1
        (geometricPointMap h.hom (geometricPointMap f.hom xbar)))).map
      (etaleLocalRingMap Y.2 h.hom (geometricPointMap f.hom xbar)))
    ((maximalIdeal ↥(etaleLocalRing B S hS Z.1
        (geometricPointMap h.hom (geometricPointMap f.hom xbar)))).map
      ((etaleLocalRingMap X.2 f.hom xbar).comp
        (etaleLocalRingMap Y.2 h.hom (geometricPointMap f.hom xbar))))
    (Ideal.map_map _ _).symm ↥(geometricModuleStalk B S hS X xbar F)

/-! ### From the Zariski stalk on a chart of `X` to the geometric stalk -/

/-- **Stacks 05VP on fibres.** Let `(U, ū)` be a small étale neighbourhood of a geometric point
`x̄` of `X` whose chart is a scheme, let `F` be a quasi-coherent `𝒪_X`-module and let `K` be an
ideal of `𝒪_{U, u}`. For a ring `R₀` mapping to `𝒪_{U, u}/K`, flatness over `R₀` of the fibre
`(φ^* F)_u / K (φ^* F)_u` of the Zariski stalk and of the fibre `F_x̄ / K F_x̄` of the geometric
stalk are the same condition.

The base change `F_x̄ = (φ^* F)_u ⊗_{𝒪_{U, u}} 𝒪_{X, x̄}` of Stacks 05VP is along a faithfully
flat map, so Stacks 0584 (2) applies to it after dividing by `K`. -/
theorem flat_quotSMul_chartZariskiModuleStalk_iff_geometricModuleStalk
    {Xs : AlgebraicSpaces B S hS} {xbar : GeometricPoint B S hS Xs.1}
    (Nb : SmallEtaleNeighborhood xbar) (F : Modules.{u, u} B S hS Xs.1 Xs.2)
    [F.IsQuasicoherentOnSite] (K : Ideal ↥(chartLocalRing B S hS Xs.1 Nb))
    {R₀ : Type w} [CommRing R₀] (ρ : R₀ →+* ↥(chartLocalRing B S hS Xs.1 Nb) ⧸ K) :
    letI : Module R₀ (↥(chartZariskiModuleStalk B S hS Xs.1 Xs.2 Nb F) ⧸
        (K • (⊤ : Submodule ↥(chartLocalRing B S hS Xs.1 Nb)
          ↥(chartZariskiModuleStalk B S hS Xs.1 Xs.2 Nb F)))) := Module.compHom _ ρ
    letI : Module R₀ (↥(geometricModuleStalk B S hS Xs xbar F) ⧸
        (K.map (chartLocalRingToEtaleLocalRing B S hS Xs.1 Xs.2 Nb) •
          (⊤ : Submodule ↥(etaleLocalRing B S hS Xs.1 xbar)
            ↥(geometricModuleStalk B S hS Xs xbar F)))) :=
      Module.compHom _ ((Ideal.quotientMap _
        (chartLocalRingToEtaleLocalRing B S hS Xs.1 Xs.2 Nb) Ideal.le_comap_map).comp ρ)
    (Module.Flat R₀ (↥(chartZariskiModuleStalk B S hS Xs.1 Xs.2 Nb F) ⧸
        (K • (⊤ : Submodule ↥(chartLocalRing B S hS Xs.1 Nb)
          ↥(chartZariskiModuleStalk B S hS Xs.1 Xs.2 Nb F)))) ↔
      Module.Flat R₀ (↥(geometricModuleStalk B S hS Xs xbar F) ⧸
        (K.map (chartLocalRingToEtaleLocalRing B S hS Xs.1 Xs.2 Nb) •
          (⊤ : Submodule ↥(etaleLocalRing B S hS Xs.1 xbar)
            ↥(geometricModuleStalk B S hS Xs xbar F))))) := by
  let : Algebra ↥(chartLocalRing B S hS Xs.1 Nb) ↥(etaleLocalRing B S hS Xs.1 xbar) :=
    (chartLocalRingToEtaleLocalRing B S hS Xs.1 Xs.2 Nb).toAlgebra
  let : Module.FaithfullyFlat ↥(chartLocalRing B S hS Xs.1 Nb)
      ↥(etaleLocalRing B S hS Xs.1 xbar) :=
    faithfullyFlat_chartLocalRingToEtaleLocalRing B S hS Xs.1 Xs.2 Nb
  have hiso := isIso_chartStalkTensorComparison B S hS Xs.2 Nb F
  exact Module.Flat.quotSMul_baseChange_linearEquiv_iff K
    (@asIso _ _ _ _ _ hiso).toLinearEquiv ρ

/-! ### From the local ring of a chart of `Y` to the étale local ring -/

/-- **The last step of the proof of Stacks 05WY.** Flatness of a module over the quotient of the
local ring `𝒪_{V, v}` of a scheme chart of `Y` by an ideal `I ⊆ 𝔪_v`, and over the quotient of
the étale local ring `𝒪_{Y, ȳ}` by the ideal it generates there, are the same condition.

The étale local ring is the strict henselization of `𝒪_{V, v}` by Stacks 04KF, and flatness
over a local ring modulo an ideal agrees with flatness over its strict henselization modulo the
extension of that ideal (Stacks 05WS). The two rings lie in different universes, which the
transport along the comparison of Stacks 04KF absorbs. -/
theorem flat_quotient_chartLocalRing_iff_quotient_etaleLocalRing
    {Y : AlgebraicSpaces B S hS} {ybar : GeometricPoint B S hS Y.1}
    (V : SmallEtaleNeighborhood ybar) {I : Ideal ↥(chartLocalRing B S hS Y.1 V)}
    (hI : I ≤ maximalIdeal ↥(chartLocalRing B S hS Y.1 V))
    (J : Ideal ↥(etaleLocalRing B S hS Y.1 ybar))
    (hJ : J = I.map (chartLocalRingToEtaleLocalRing B S hS Y.1 Y.2 V))
    (N : Type x) [AddCommGroup N] [Module (↥(etaleLocalRing B S hS Y.1 ybar) ⧸ J) N] :
    letI : Module (↥(chartLocalRing B S hS Y.1 V) ⧸ I) N :=
      Module.compHom N (Ideal.quotientMap J
        (chartLocalRingToEtaleLocalRing B S hS Y.1 Y.2 V) (hJ ▸ Ideal.le_comap_map))
    (Module.Flat (↥(chartLocalRing B S hS Y.1 V) ⧸ I) N ↔
      Module.Flat (↥(etaleLocalRing B S hS Y.1 ybar) ⧸ J) N) :=
  Module.Flat.quotient_ringEquiv_iff_of_isHenselization
    (separableClosure (ResidueField ↥(chartLocalRing B S hS Y.1 V))
      (chartGeometricPoint V).residueField)
    (chartStrictHenselizationEquiv B S hS Y.1 Y.2 V)
    (chartLocalRingToEtaleLocalRing B S hS Y.1 Y.2 V) rfl hI J hJ N

/-! ### Stacks 05WY at one pair of composable squares of charts -/

section Squares

variable {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (h : Y ⟶ Z)
  {xbar : GeometricPoint B S hS X.1} (N : SmallEtaleNeighborhood xbar)
  (Vc : SmallEtale B S hS Y.1) (g₁ : N.chart.obj.left ⟶ Vc.obj.left)
  (hcomm₁ : N.chart.obj.hom ≫ f.hom = yoneda.map g₁ ≫ Vc.obj.hom)
  (Wc : SmallEtale B S hS Z.1) (g₂ : Vc.obj.left ⟶ Wc.obj.left)
  (hcomm₂ : Vc.obj.hom ≫ h.hom = yoneda.map g₂ ≫ Wc.obj.hom)

/-- **Stacks 05WY, condition (3) if and only if condition (1), at one point of one pair of
composable commuting squares of étale scheme charts.** Let `U ⟶ V ⟶ W` be schemes étale over
`X ⟶ Y ⟶ Z` in two commuting squares, let `u` be the point of `U` under a chosen lift of a
geometric point `x̄` of `X`, let `v` and `w` be its images and let `F` be a quasi-coherent
`𝒪_X`-module. Then the fibre `(F|_U)_u / 𝔪_w (F|_U)_u` is flat over
`𝒪_{V, v} / 𝔪_w 𝒪_{V, v}` exactly when condition (1) of Stacks 05WY holds at `x̄`.

Condition (3) of the source reads the left-hand side on the scheme-theoretic fibres `U_w` and
`V_w`; here it is read on the local rings, through the canonical identifications
`𝒪_{V_w, v} = 𝒪_{V, v}/𝔪_w 𝒪_{V, v}` and `(F_w)_u = (F|_U)_u/𝔪_w (F|_U)_u` which the source
records at the start of its proof. The two ideals are arguments carrying their defining
equations, so that the statement applies at whichever presentation of them the caller has.

The proof is the source's chain of identifications: Stacks 05VP turns the Zariski stalk on the
chart into the geometric stalk after base change along the faithfully flat map
`𝒪_{U, u} → 𝒪_{X, x̄}`, which Stacks 0584 (2) sees through modulo `𝔪_w`; Stacks 04KF and
Stacks 05WS replace `𝒪_{V, v}` by its strict henselization `𝒪_{Y, ȳ}`; and the maximal ideal
of `𝒪_{Z, z̄}` is generated by `𝔪_w`, so the two fibres taken are the same. -/
theorem flatQuotSMul_chartZariskiModuleStalk_iff_isFibreFlatOverAtGeometricPoint
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite]
    (I : Ideal ↥(chartLocalRing B S hS Y.1 (targetNeighborhood B S hS N Vc g₁ hcomm₁)))
    (hI : I = (maximalIdeal ↥(chartLocalRing B S hS Z.1
          (targetNeighborhood B S hS (targetNeighborhood B S hS N Vc g₁ hcomm₁)
            Wc g₂ hcomm₂))).map
        (((BigFppfOver.toScheme B S hS).map g₂).stalkMap
          (chartPoint B S hS Y.1 (targetNeighborhood B S hS N Vc g₁ hcomm₁))).hom)
    (K : Ideal ↥(chartLocalRing B S hS X.1 N))
    (hK : K = I.map (((BigFppfOver.toScheme B S hS).map g₁).stalkMap
      (chartPoint B S hS X.1 N)).hom) :
    Module.FlatQuotSMul
        (((BigFppfOver.toScheme B S hS).map g₁).stalkMap (chartPoint B S hS X.1 N)).hom
        I K hK ↥(chartZariskiModuleStalk B S hS X.1 X.2 N F) ↔
      IsFibreFlatOverAtGeometricPoint B S hS f h F xbar := by
  subst hK
  have : I.IsTwoSided := inferInstance
  let : IsLocalRing ↥(etaleLocalRing B S hS Z.1
      (geometricPointMap h.hom (geometricPointMap f.hom xbar))) :=
    isLocalRing_etaleLocalRing B S hS Z.1 Z.2 _
  have hsq₁ :=
    etaleLocalRingMap_comp_chartLocalRingToEtaleLocalRing B S hS f xbar N Vc g₁ hcomm₁
  have hsq₂ := etaleLocalRingMap_comp_chartLocalRingToEtaleLocalRing B S hS h
    (geometricPointMap f.hom xbar) (targetNeighborhood B S hS N Vc g₁ hcomm₁) Wc g₂ hcomm₂
  have hmax := map_maximalIdeal_chartLocalRingToEtaleLocalRing B S hS Z.1 Z.2
    (targetNeighborhood B S hS (targetNeighborhood B S hS N Vc g₁ hcomm₁) Wc g₂ hcomm₂)
  have hI₁ := (congrArg
      (Ideal.map (etaleLocalRingMap Y.2 h.hom (geometricPointMap f.hom xbar))) hmax).symm.trans
    ((ideal_map_square _ _ _ _ hsq₂ _).symm.trans
      (congrArg (Ideal.map (chartLocalRingToEtaleLocalRing B S hS Y.1 Y.2
        (targetNeighborhood B S hS N Vc g₁ hcomm₁))) hI.symm))
  have hJ' := ideal_map_square _ _ _ _ hsq₁ I
  have hI₂ := (Ideal.map_map _ _).symm.trans ((congrArg (Ideal.map (etaleLocalRingMap X.2 f.hom
    xbar)) hI₁).trans hJ'.symm)
  have hle := Ideal.map_le_iff_le_comap.1 (le_of_eq hJ'.symm)
  have hIle : I ≤ maximalIdeal ↥(chartLocalRing B S hS Y.1
      (targetNeighborhood B S hS N Vc g₁ hcomm₁)) := by
    rw [hI]
    exact Ideal.map_le_iff_le_comap.2 (le_of_eq (IsLocalRing.maximalIdeal_comap
      (((BigFppfOver.toScheme B S hS).map g₂).stalkMap
        (((BigFppfOver.toScheme B S hS).map g₁).base
          (chartPoint B S hS X.1 N))).hom).symm)
  let : Module (↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom xbar)) ⧸
      I.map (chartLocalRingToEtaleLocalRing B S hS Y.1 Y.2
        (targetNeighborhood B S hS N Vc g₁ hcomm₁)))
      (↥(geometricModuleStalk B S hS X xbar F) ⧸
        ((I.map (((BigFppfOver.toScheme B S hS).map g₁).stalkMap
            (chartPoint B S hS X.1 N)).hom).map
          (chartLocalRingToEtaleLocalRing B S hS X.1 X.2 N) •
          (⊤ : Submodule ↥(etaleLocalRing B S hS X.1 xbar)
            ↥(geometricModuleStalk B S hS X xbar F)))) :=
    Module.compHom _ (Ideal.quotientMap
      ((I.map (((BigFppfOver.toScheme B S hS).map g₁).stalkMap
          (chartPoint B S hS X.1 N)).hom).map
        (chartLocalRingToEtaleLocalRing B S hS X.1 X.2 N))
      (etaleLocalRingMap X.2 f.hom xbar)
      hle)
  let rho : (↥(chartLocalRing B S hS Y.1 (targetNeighborhood B S hS N Vc g₁ hcomm₁)) ⧸ I) →+*
      (↥(chartLocalRing B S hS X.1 N) ⧸
        I.map (((BigFppfOver.toScheme B S hS).map g₁).stalkMap
          (chartPoint B S hS X.1 N)).hom) :=
    Ideal.quotientMap _ (((BigFppfOver.toScheme B S hS).map g₁).stalkMap
      (chartPoint B S hS X.1 N)).hom Ideal.le_comap_map
  refine Iff.trans (flat_quotSMul_chartZariskiModuleStalk_iff_geometricModuleStalk B S hS N F
    (I.map (((BigFppfOver.toScheme B S hS).map g₁).stalkMap (chartPoint B S hS X.1 N)).hom)
    rho) ?_
  have hC := flat_quotient_chartLocalRing_iff_quotient_etaleLocalRing B S hS
      (targetNeighborhood B S hS N Vc g₁ hcomm₁) hIle
      (I.map (chartLocalRingToEtaleLocalRing B S hS Y.1 Y.2
        (targetNeighborhood B S hS N Vc g₁ hcomm₁))) rfl
      (↥(geometricModuleStalk B S hS X xbar F) ⧸
        ((I.map (((BigFppfOver.toScheme B S hS).map g₁).stalkMap
            (chartPoint B S hS X.1 N)).hom).map
          (chartLocalRingToEtaleLocalRing B S hS X.1 X.2 N) •
          (⊤ : Submodule ↥(etaleLocalRing B S hS X.1 xbar)
            ↥(geometricModuleStalk B S hS X xbar F))))
  have hcong := Module.flatQuotSMul_congr (etaleLocalRingMap X.2 f.hom xbar) hI₁ hI₂
      (Ideal.map_map _ _).symm hJ' ↥(geometricModuleStalk B S hS X xbar F)
  have h2 := hC.trans hcong.symm
  refine Iff.trans (flat_iff_of_module_ext _ _ ?_) h2
  intro r n
  exact quotientMap_square_smul hsq₁ (I := I)
    (Iσ := I.map (((BigFppfOver.toScheme B S hS).map g₁).stalkMap
      (chartPoint B S hS X.1 N)).hom)
    (Iγ := I.map (chartLocalRingToEtaleLocalRing B S hS Y.1 Y.2
      (targetNeighborhood B S hS N Vc g₁ hcomm₁)))
    (P := (I.map (((BigFppfOver.toScheme B S hS).map g₁).stalkMap
        (chartPoint B S hS X.1 N)).hom).map
      (chartLocalRingToEtaleLocalRing B S hS X.1 X.2 N))
    Ideal.le_comap_map Ideal.le_comap_map Ideal.le_comap_map
    hle _ r n

end Squares


/-! ### A pointed pair of composable squares of charts always exists -/

/-- **A diagram as in condition (3) of Stacks 05WY exists.** For `f : X ⟶ Y` and `h : Y ⟶ Z`
and a geometric point `x̄` of `X` there are schemes `U ⟶ V ⟶ W` étale over `X ⟶ Y ⟶ Z` in two
commuting squares, with `U` a small étale neighbourhood of `x̄`.

This is the construction the source gives: take `W ⟶ Z` surjective étale, then `V ⟶ W ×_Z Y`
and `U ⟶ V ×_Y X` surjective étale, and lift `x̄` to a point of `U` using surjectivity of
`U ⟶ X` (Stacks 05VN, `AlgebraicGeometry.Space.exists_chartLift_of_chartPoint`). -/
theorem exists_chartSquares {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (h : Y ⟶ Z)
    (xbar : GeometricPoint B S hS X.1) :
    ∃ (N : SmallEtaleNeighborhood xbar) (Vc : SmallEtale B S hS Y.1)
      (g₁ : N.chart.obj.left ⟶ Vc.obj.left)
      (_hcomm₁ : N.chart.obj.hom ≫ f.hom = yoneda.map g₁ ≫ Vc.obj.hom)
      (Wc : SmallEtale B S hS Z.1) (g₂ : Vc.obj.left ⟶ Wc.obj.left),
      Vc.obj.hom ≫ h.hom = yoneda.map g₂ ≫ Wc.obj.hom := by
  obtain ⟨W₀, c, hcSurjective, hcEtale⟩ := Z.2.exists_atlas
  obtain ⟨V₀, b, g₂, hcomm₂, hbSurjective, hbEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS Y.2 Z.2 h.hom W₀ c hcSurjective hcEtale
  obtain ⟨U₀, a, g₁, hcomm₁, haSurjective, haEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS X.2 Y.2 f.hom V₀ b hbSurjective hbEtale
  obtain ⟨z, hz⟩ := (surjective_iff_surjective_pointsMap B S hS X.1 X.2 U₀ a).mp
    haSurjective xbar.image
  have hcp : ChartPoint B S hS U₀ a (pointsToScheme B S hS U₀ z) xbar.image :=
    hz ▸ chartPoint_pointsToScheme B S hS U₀ a z
  obtain ⟨q, hq, -⟩ := exists_chartLift_of_chartPoint B S hS X.2 xbar
    ⟨CostructuredArrow.mk a, haEtale⟩ _ hcp
  exact ⟨⟨⟨CostructuredArrow.mk a, haEtale⟩, q, hq⟩, ⟨CostructuredArrow.mk b, hbEtale⟩, g₁,
    hcomm₁, ⟨CostructuredArrow.mk c, hcEtale⟩, g₂, hcomm₂⟩


/-! ### Stacks 05WY -/

/-- **Stacks 05WY: condition (3) if and only if condition (1).** In Situation 05WX — a scheme
`S`, algebraic spaces `X`, `Y`, `Z` over `S` with `f : X ⟶ Y` and `h : Y ⟶ Z`, a quasi-coherent
`𝒪_X`-module `F` and a geometric point `x̄` of `X` — the following are equivalent:

1. writing `ȳ = f ∘ x̄` and `z̄ = h ∘ ȳ`, the fibre `F_x̄ / 𝔪_z̄ F_x̄` is flat over
   `𝒪_{Y, ȳ} / 𝔪_z̄ 𝒪_{Y, ȳ}`;
3. there is a commuting diagram of schemes `U ⟶ V ⟶ W` étale over `f` and `h`, and a point `u`
   of `U` above the image of `x̄`, at which the fibre of `F|_U` over the fibre of `V` is flat.

Condition (3) of the source reads the second condition on the scheme-theoretic fibres `U_w` and
`V_w`; here it is read on their local rings, through the canonical identifications
`𝒪_{V_w, v} = 𝒪_{V, v}/𝔪_w 𝒪_{V, v}` and `(F_w)_u = (F|_U)_u/𝔪_w (F|_U)_u` which the source
records at the start of its proof. The point `u` above `x̄` is presented as a lift of `x̄` to the
chart, which is the same data by Stacks 05VN
(`AlgebraicGeometry.Space.exists_chartLift_of_chartPoint` and
`AlgebraicGeometry.Space.chartPoint_isChartPoint`).

Condition (2) of the source, flatness of the pullback of `F` to the fibre `X_z` over `Y_z` in
the sense of Stacks 05VV, is not among the conditions compared here; it is
`Space.isFlatOverAtGeometricPoint_fieldFibreSpace_iff_isFibreFlatOverAtGeometricPoint`
of `StacksFrontier/AlgebraicGeometry/Spaces/FibreFlatnessFieldFibre.lean`, and
`AlgebraicGeometry.Space.isFlatOverAtGeometricPoint_fieldFibreSpace_iff_exists_chartPoint`
composes it with this lemma.

Such a diagram always exists (`AlgebraicGeometry.Space.exists_chartSquares`), which is what the
second direction uses: take `W ⟶ Z` surjective étale, then `V ⟶ W ×_Z Y` and `U ⟶ V ×_Y X`
surjective étale, and a point of `U` above the image of `x̄`.  Since no diagram is privileged,
condition (3) in fact holds at *every* diagram as soon as it holds at one, which is
`AlgebraicGeometry.Space.forall_flatQuotSMul_chart_iff_isFibreFlatOverAtGeometricPoint`. -/
@[stacks 05WY "(1) iff (3), condition (3) read on the local rings of the charts"]
theorem exists_flatQuotSMul_chart_iff_isFibreFlatOverAtGeometricPoint
    {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (h : Y ⟶ Z)
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite]
    (xbar : GeometricPoint B S hS X.1) :
    (∃ (N : SmallEtaleNeighborhood xbar) (Vc : SmallEtale B S hS Y.1)
        (g₁ : N.chart.obj.left ⟶ Vc.obj.left)
        (hcomm₁ : N.chart.obj.hom ≫ f.hom = yoneda.map g₁ ≫ Vc.obj.hom)
        (Wc : SmallEtale B S hS Z.1) (g₂ : Vc.obj.left ⟶ Wc.obj.left)
        (hcomm₂ : Vc.obj.hom ≫ h.hom = yoneda.map g₂ ≫ Wc.obj.hom),
      Module.FlatQuotSMul
        (((BigFppfOver.toScheme B S hS).map g₁).stalkMap (chartPoint B S hS X.1 N)).hom
        ((maximalIdeal ↥(chartLocalRing B S hS Z.1 (targetNeighborhood B S hS
              (targetNeighborhood B S hS N Vc g₁ hcomm₁) Wc g₂ hcomm₂))).map
          (((BigFppfOver.toScheme B S hS).map g₂).stalkMap
            (chartPoint B S hS Y.1 (targetNeighborhood B S hS N Vc g₁ hcomm₁))).hom)
        (((maximalIdeal ↥(chartLocalRing B S hS Z.1 (targetNeighborhood B S hS
                (targetNeighborhood B S hS N Vc g₁ hcomm₁) Wc g₂ hcomm₂))).map
            (((BigFppfOver.toScheme B S hS).map g₂).stalkMap
              (chartPoint B S hS Y.1 (targetNeighborhood B S hS N Vc g₁ hcomm₁))).hom).map
          (((BigFppfOver.toScheme B S hS).map g₁).stalkMap (chartPoint B S hS X.1 N)).hom)
        rfl ↥(chartZariskiModuleStalk B S hS X.1 X.2 N F)) ↔
      IsFibreFlatOverAtGeometricPoint B S hS f h F xbar := by
  constructor
  · rintro ⟨N, Vc, g₁, hcomm₁, Wc, g₂, hcomm₂, hflat⟩
    exact (flatQuotSMul_chartZariskiModuleStalk_iff_isFibreFlatOverAtGeometricPoint
      B S hS f h N Vc g₁ hcomm₁ Wc g₂ hcomm₂ F _ rfl _ rfl).1 hflat
  · intro hgeom
    obtain ⟨N, Vc, g₁, hcomm₁, Wc, g₂, hcomm₂⟩ := exists_chartSquares B S hS f h xbar
    exact ⟨N, Vc, g₁, hcomm₁, Wc, g₂, hcomm₂,
      (flatQuotSMul_chartZariskiModuleStalk_iff_isFibreFlatOverAtGeometricPoint B S hS f h
        N Vc g₁ hcomm₁ Wc g₂ hcomm₂ F _ rfl _ rfl).2 hgeom⟩

/-- **Stacks 05WY: condition (3) at an arbitrary chosen diagram if and only if condition (1).**
In Situation 05WX the chart condition (3) of Stacks 05WY holds on *every* pointed pair of
composable commuting squares of étale scheme charts `U ⟶ V ⟶ W` of `f` and `h` exactly when
condition (1) holds at `x̄`.

This is the "any choice works" reading of condition (3) the source intends: the source says
"choose a commutative diagram", so the condition must not depend on the choice.  Together with
`AlgebraicGeometry.Space.exists_flatQuotSMul_chart_iff_isFibreFlatOverAtGeometricPoint` it says
that the some-diagram and every-diagram readings of condition (3) agree, a diagram existing by
`AlgebraicGeometry.Space.exists_chartSquares`. -/
@[stacks 05WY "(1) iff (3) at an arbitrary chosen diagram: the every-diagram reading of \
condition (3), read on the local rings of the charts"]
theorem forall_flatQuotSMul_chart_iff_isFibreFlatOverAtGeometricPoint
    {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (h : Y ⟶ Z)
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite]
    (xbar : GeometricPoint B S hS X.1) :
    (∀ (N : SmallEtaleNeighborhood xbar) (Vc : SmallEtale B S hS Y.1)
        (g₁ : N.chart.obj.left ⟶ Vc.obj.left)
        (hcomm₁ : N.chart.obj.hom ≫ f.hom = yoneda.map g₁ ≫ Vc.obj.hom)
        (Wc : SmallEtale B S hS Z.1) (g₂ : Vc.obj.left ⟶ Wc.obj.left)
        (hcomm₂ : Vc.obj.hom ≫ h.hom = yoneda.map g₂ ≫ Wc.obj.hom),
      Module.FlatQuotSMul
        (((BigFppfOver.toScheme B S hS).map g₁).stalkMap (chartPoint B S hS X.1 N)).hom
        ((maximalIdeal ↥(chartLocalRing B S hS Z.1 (targetNeighborhood B S hS
              (targetNeighborhood B S hS N Vc g₁ hcomm₁) Wc g₂ hcomm₂))).map
          (((BigFppfOver.toScheme B S hS).map g₂).stalkMap
            (chartPoint B S hS Y.1 (targetNeighborhood B S hS N Vc g₁ hcomm₁))).hom)
        (((maximalIdeal ↥(chartLocalRing B S hS Z.1 (targetNeighborhood B S hS
                (targetNeighborhood B S hS N Vc g₁ hcomm₁) Wc g₂ hcomm₂))).map
            (((BigFppfOver.toScheme B S hS).map g₂).stalkMap
              (chartPoint B S hS Y.1 (targetNeighborhood B S hS N Vc g₁ hcomm₁))).hom).map
          (((BigFppfOver.toScheme B S hS).map g₁).stalkMap (chartPoint B S hS X.1 N)).hom)
        rfl ↥(chartZariskiModuleStalk B S hS X.1 X.2 N F)) ↔
      IsFibreFlatOverAtGeometricPoint B S hS f h F xbar := by
  constructor
  · intro hall
    obtain ⟨N, Vc, g₁, hcomm₁, Wc, g₂, hcomm₂⟩ := exists_chartSquares B S hS f h xbar
    exact (flatQuotSMul_chartZariskiModuleStalk_iff_isFibreFlatOverAtGeometricPoint
      B S hS f h N Vc g₁ hcomm₁ Wc g₂ hcomm₂ F _ rfl _ rfl).1
      (hall N Vc g₁ hcomm₁ Wc g₂ hcomm₂)
  · intro hgeom N Vc g₁ hcomm₁ Wc g₂ hcomm₂
    exact (flatQuotSMul_chartZariskiModuleStalk_iff_isFibreFlatOverAtGeometricPoint
      B S hS f h N Vc g₁ hcomm₁ Wc g₂ hcomm₂ F _ rfl _ rfl).2 hgeom

end AlgebraicGeometry.Space

end
