module

public import Mathlib.RingTheory.Regular.IsSMulRegular
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.PuncturedSpectrumPicard.PuncturedSpectrumFirstHalf
public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowup
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierEtaleEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.AtAPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransform
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportedSectionsSubsheaf
import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.RegularSections
import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.PointwiseBaseChange
import StacksFrontier.AlgebraicGeometry.Spaces.LocallyPrincipalPullback
import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatEtaleLocalRing
import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatLocus
import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentStructureSheaf
import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformLocalGenerators
import StacksFrontier.AlgebraicGeometry.Spaces.Support.CompatibleEtaleCharts

/-!
# Base change of flatness at a point, and the supported sections it kills

Let a cartesian square of algebraic spaces over a scheme `S` of a big fppf site be given, with
`f : X₀ ⟶ Y₀`, `g : Y₁ ⟶ Y₀`, `f' : X₁ ⟶ Y₁` and `g' : X₁ ⟶ X₀`.  If `f` is flat at the image
in `|X₀|` of a point `x'` of `|X₁|`, then its base change `f'` is flat at `x'`.

That is the first half of this file.  The second half is what it was proved for: for a
morphism `f : Y ⟶ X` of algebraic spaces and a closed subspace `D ⊆ X` whose inverse images
are effective Cartier on the étale scheme charts of `X`, if `f` is flat at every point of `|Y|`
lying over `|D|` then `𝒪_Y` has no nonzero local section supported on `|f^{-1}D|`.  Applied to
the projection `X ×_A A' ⟶ A'` of a blowup `b : A' ⟶ A` of `A` in `Z` this is the vanishing of
the ideal of supported sections that **Stacks 0865, part (1)** needs, and it is what makes
`AlgebraicGeometry.Space.strictTransformSubfunctor_eq_top_of_isFlatAt` carry the source's
hypotheses and nothing else.

This is the structure-sheaf case of Stacks 05VW, the only case of that tag this development
proves; the module case, about the flat locus of a quasi-coherent module, is an acknowledged
debt carried as the hypothesis
`AlgebraicGeometry.Space.IsFlatAtPointStableUnderBaseChange` of
`StacksFrontier/AlgebraicGeometry/Spaces/FlatModuleLocusBaseChange.lean`.  No finiteness
hypothesis enters: in particular this is *not*
`AlgebraicGeometry.Space.isFlatAt_baseChangeOverBase_iff` of
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/FlatLocusBaseChange.lean`, which is the
equivalence of Stacks 05X3 and consumes finite presentation and flatness of the structure
morphism of the source together with finite type of that of the target.

## Main results

* `AlgebraicGeometry.Space.isFlatAt_of_isPullback`: base change of flatness at a point.
* `AlgebraicGeometry.Space.exists_affine_chartPair_isRegular_span_definingIdealAt`: through
  every point of every étale chart of `Y` there is an affine chart over an affine chart of `X`
  on which `D` is cut out by a nonzerodivisor, with the inverse image cut out by its pullback.
* `AlgebraicGeometry.Space.hasNoSectionsSupportedIn_preimage_of_isFlatAt`: the vanishing of the
  sections of `𝒪_Y` supported on `|f^{-1}D|`.
* `AlgebraicGeometry.Space.isFlatAt_strictTransformPullbackToBlowUp_of_isFlatAt` and
  `AlgebraicGeometry.Space.strictTransformIdealSubmodule_eq_bot_of_isFlatAt`: the two of them
  at the blowup, the second being the input of Stacks 0865, part (1).

## Implementation notes

**The route is native to algebraic spaces.**  The source proves Stacks 0865 by reducing to the
case of schemes, Stacks 080F, by étale localization — Stacks 0863, parts (2) and (3).  What
replaces it is the chart-level computation of the supported
sections as an ideal-power torsion, Stacks 0859 (2) in the form
`AlgebraicGeometry.Space.mem_supportedSectionsSubmodule_iff_mem_primaryComponent`, which needs
no comparison between the modules on a chart and the modules on the space: the structure sheaf
is quasi-coherent on the site unconditionally
(`SheafOfModules.isQuasicoherentOnSite_unit`), so the torsion statement is available for it,
and killing that torsion is then commutative algebra in the local rings of one chart scheme.
Only the structure sheaf is treated here, which is part (1).  Part (2) of Stacks 0865 is about a
module `F`, and the same route needs quasi-coherence of `pr_X^*F`, which is Stacks 03GA in the
form `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite`;
that is carried out in
`StacksFrontier/AlgebraicGeometry/Spaces/FlatModuleSupportedSections.lean`.

Most imports are not `public`: the proofs need the flat-locus and regular-section theories, but
re-exporting them would put `AlgebraicGeometry.IsRegular` of
`StacksFrontier/AlgebraicGeometry/Properties/Regular.lean` into the scope of the modules above
this one, where `IsRegular` means the predicate on a ring element.

The base change statement is proved here rather than alongside the equivalence of Stacks 0CIC
that first needed it, in `StacksFrontier/AlgebraicGeometry/Stacks/FlatAtAPoint.lean`: the import
closure it asks for is the étale-chart theory alone, not the whole theory of algebraic stacks,
and that module imports it from here.  The scheme-level step it rests on is
`AlgebraicGeometry.isFlatAt_of_isPullback` of
`StacksFrontier/AlgebraicGeometry/Morphisms/FlatMorphisms/PointwiseBaseChange.lean`, the single
home of that statement, applied at the flipped orientation `hcharts.flip`.

No `@[stacks]` attribute is carried: Stacks 05VW is a statement about modules, and this is only
its structure-sheaf case.

## References

* [Stacks Project, Tag 05VW](https://stacks.math.columbia.edu/tag/05VW)
* [Stacks Project, Tag 04NC](https://stacks.math.columbia.edu/tag/04NC)
* [Stacks Project, Tag 04ND](https://stacks.math.columbia.edu/tag/04ND)
* [Stacks Project, Tag 03ML](https://stacks.math.columbia.edu/tag/03ML)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search in the presheaf category of the big fppf site is slow in this proof
set_option maxHeartbeats 1600000 in
-- instance search in the presheaf category of the big fppf site is slow in this proof
/-- **Base change of flatness at a point, for morphisms of algebraic spaces** — the structure
sheaf case of **Stacks 05VW**. In a cartesian square of algebraic spaces over `S`, the
projection to the new base is flat at a point of the apex as soon as the morphism it is a base
change of is flat at the image of that point.

Compatible surjective étale charts of the cartesian square
(`AlgebraicGeometry.Space.exists_compatible_etale_charts`) give a chart `V` of the target, a
chart `U ⟶ V` of `f`, a chart `V' ⟶ V` of `g` and the induced chart `U' = U ×_V V' ⟶ V'` of the
base change, with `U'` an atlas of the fibre product. A field-valued point of `U'` lying over
the given point turns the two squares into pointed étale charts, whose selected scheme points
correspond under `U' ⟶ U`. Flatness of a morphism of germs being étale local on source and
target (**Stacks 04ND**), flatness at a point is the induced germ condition read in any one
pointed chart (**Stacks 04NC**), so the statement becomes the one for schemes.

This carries no `@[stacks]` attribute: Stacks 05VW is a statement about modules, which this
development does not prove, and this is its structure sheaf case. It is what the equivalence of
Stacks 0CIC consumes, through
`AlgebraicGeometry.Stack.AlgebraicStacks.isFlatAt_of_isPullback_presheaf`. -/
theorem isFlatAt_of_isPullback
    {X₁ X₀ Y₁ Y₀ : AlgebraicSpaces B S hS} {g' : X₁ ⟶ X₀} {f' : X₁ ⟶ Y₁} {f : X₀ ⟶ Y₀}
    {g : Y₁ ⟶ Y₀} (sq : IsPullback g' f' f g) (x' : points B S hS X₁.1)
    (hf : IsFlatAt B S hS f.hom (pointsMap B S hS X₁.1 g'.hom x')) :
    IsFlatAt B S hS f'.hom x' := by
  classical
  have _ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderComposition :=
    inverseImage_isStableUnderComposition B S hS etale_isStableUnderComposition
  have hQbc := MorphismProperty.relative_isStableUnderBaseChange
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) (F := yoneda)
  obtain ⟨U, V, U', V', p, q, pU, pV', v, a, b, c, hcharts, hap, hbq, hcX, hcY,
      hvSurj, hvEtale, haSurj, haEtale, hbSurj, hbEtale, hcSurj, hcEtale⟩ :=
    exists_compatible_etale_charts B S hS f g
  let eAs : X₁ ≅ AlgebraicSpaces.fiberProduct B S hS f g :=
    sq.isoIsPullback _ _ (AlgebraicSpaces.isPullback_fiberProduct B S hS f g)
  let e : X₁.1 ≅ Limits.pullback f.hom g.hom :=
    { hom := eAs.hom.hom
      inv := eAs.inv.hom
      hom_inv_id := congrArg (fun k => k.hom) eAs.hom_inv_id
      inv_hom_id := congrArg (fun k => k.hom) eAs.inv_hom_id }
  have heFst : e.hom ≫ Limits.pullback.fst f.hom g.hom = g'.hom :=
    congrArg (fun k => k.hom) (IsPullback.isoIsPullback_hom_fst _ _ sq
      (AlgebraicSpaces.isPullback_fiberProduct B S hS f g))
  have heSnd : e.hom ≫ Limits.pullback.snd f.hom g.hom = f'.hom :=
    congrArg (fun k => k.hom) (IsPullback.isoIsPullback_hom_snd _ _ sq
      (AlgebraicSpaces.isPullback_fiberProduct B S hS f g))
  have heInvSnd : e.inv ≫ f'.hom = Limits.pullback.snd f.hom g.hom := by
    rw [← heSnd, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  have hSndFEtale := hQbc.of_isPullback (IsPullback.of_hasPullback v f.hom) hvEtale
  have hSndGEtale := hQbc.of_isPullback (IsPullback.of_hasPullback v g.hom) hvEtale
  have hAEtale := MorphismProperty.comp_mem _ a (Limits.pullback.snd v f.hom) haEtale hSndFEtale
  have hBEtale := MorphismProperty.comp_mem _ b (Limits.pullback.snd v g.hom) hbEtale hSndGEtale
  have hcXEtale : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (c ≫ e.inv) :=
    have _ : IsIso e.inv := ⟨e.hom, e.inv_hom_id, e.hom_inv_id⟩
    MorphismProperty.RespectsIso.postcomp _ e.inv c hcEtale
  have hcommF : yoneda.map p ≫ v = (a ≫ Limits.pullback.snd v f.hom) ≫ f.hom := by
    calc yoneda.map p ≫ v = (a ≫ Limits.pullback.fst v f.hom) ≫ v := by rw [← hap]
      _ = (a ≫ Limits.pullback.snd v f.hom) ≫ f.hom := by
          simp only [Category.assoc, Limits.pullback.condition]
  have hcommF' : yoneda.map pV' ≫ (b ≫ Limits.pullback.snd v g.hom) = (c ≫ e.inv) ≫ f'.hom := by
    calc yoneda.map pV' ≫ (b ≫ Limits.pullback.snd v g.hom)
        = c ≫ Limits.pullback.snd f.hom g.hom := by
          simpa only [Category.assoc] using hcY.symm
      _ = (c ≫ e.inv) ≫ f'.hom := by rw [Category.assoc, heInvSnd]
  have hPull : IsAlgebraicSpace B S hS (Limits.pullback f.hom g.hom) :=
    isAlgebraicSpace_pullback B S hS f.hom g.hom X₀.property Y₁.property Y₀.property
  obtain ⟨z, hz⟩ :=
    (surjective_iff_surjective_pointsMap B S hS (Limits.pullback f.hom g.hom) hPull
      U' c).mp hcSurj (pointsMap B S hS X₁.1 e.hom x')
  obtain ⟨r, rfl⟩ := Quot.exists_rep z
  have hz' : pointsMap B S hS (yoneda.obj U') c (r.class B S hS (yoneda.obj U')) =
      pointsMap B S hS X₁.1 e.hom x' := hz
  let chartF : EtaleChartAtPoint B S hS f.hom
      (pointsMap B S hS X₁.1 g'.hom x') :=
    { U := U
      V := V
      a := a ≫ Limits.pullback.snd v f.hom
      b := v
      h := p
      a_etale := hAEtale
      b_etale := hvEtale
      comm := hcommF
      representative := FieldValuedPoint.map B S hS (yoneda.obj U') (yoneda.map pU) r
      point := IsLocalRing.closedPoint r.carrier
      maps_to := by
        have h₁ : pointsMap B S hS (yoneda.obj U) (a ≫ Limits.pullback.snd v f.hom)
            ((FieldValuedPoint.map B S hS (yoneda.obj U') (yoneda.map pU) r).class B S hS
              (yoneda.obj U)) =
            pointsMap B S hS (yoneda.obj U')
              (yoneda.map pU ≫ a ≫ Limits.pullback.snd v f.hom)
              (r.class B S hS (yoneda.obj U')) := rfl
        rw [h₁, ← hcX, pointsMap_comp_apply, hz', ← pointsMap_comp_apply, heFst] }
  let chartF' : EtaleChartAtPoint B S hS f'.hom x' :=
    { U := U'
      V := V'
      a := c ≫ e.inv
      b := b ≫ Limits.pullback.snd v g.hom
      h := pV'
      a_etale := hcXEtale
      b_etale := hBEtale
      comm := hcommF'
      representative := r
      point := IsLocalRing.closedPoint r.carrier
      maps_to := by
        rw [pointsMap_comp_apply, hz', ← pointsMap_comp_apply, e.hom_inv_id, pointsMap_id,
          id_eq] }
  have hsource : chartF.sourcePoint B S hS =
      (BigFppfOver.toScheme B S hS).map pU (chartF'.sourcePoint B S hS) := by
    change ((BigFppfOver.toScheme B S hS).map (r.value ≫ pU))
        (IsLocalRing.closedPoint r.carrier) =
      (BigFppfOver.toScheme B S hS).map pU
        (((BigFppfOver.toScheme B S hS).map r.value) (IsLocalRing.closedPoint r.carrier))
    rw [Functor.map_comp]
    exact Scheme.Hom.comp_apply _ _ _
  refine (holdsOnEveryEtaleChartAtPoint_iff_some B S hS _
    MorphismOfGerms.isEtaleLocalOnSourceAndTarget_isFlat X₁.property Y₁.property
    f'.hom x').mpr ⟨chartF', ?_⟩
  refine (MorphismOfGerms.isFlat_ofSchemeHom_iff _ _).mpr ?_
  refine _root_.AlgebraicGeometry.isFlatAt_of_isPullback hcharts.flip
    (chartF'.sourcePoint B S hS) ?_
  rw [← hsource]
  exact (MorphismOfGerms.isFlat_ofSchemeHom_iff _ _).mp (hf chartF)


/-! ### A section killed by a power of a pullback nonzerodivisor -/

/-- **The germ of a section killed by a power of the pullback of a nonzerodivisor vanishes at a
point where the morphism is flat.**  Let `h : V ⟶ U` be a morphism of schemes with `U` affine
and let `a` be a nonzerodivisor on `U`.  A global function on `V` annihilated by a power of the
pullback of `a` has vanishing germ at a point `y`: if the germ of that pullback is a unit this
is immediate, and otherwise flatness of `h` at `y` carries `a` to a nonzerodivisor on the local
ring of `V` at `y`. -/
private theorem germ_eq_zero_of_pow_mul_eq_zero_of_isFlatAt {V U : Scheme.{u}} [IsAffine U]
    (h : V ⟶ U) {a : Γ(U, ⊤)} (ha : IsSMulRegular Γ(U, ⊤) a) (s : Γ(V, ⊤)) (n : ℕ)
    (hn : h.appTop a ^ n * s = 0) (y : V)
    (hflat : ¬ IsUnit (V.presheaf.germ ⊤ y trivial (h.appTop a)) →
      _root_.AlgebraicGeometry.IsFlatAt h.toLRSHom.toShHom y) :
    V.presheaf.germ ⊤ y trivial s = 0 := by
  have hzero : V.presheaf.germ ⊤ y trivial (h.appTop a) ^ n *
      V.presheaf.germ ⊤ y trivial s = 0 := by
    rw [← map_pow, ← map_mul, hn, map_zero]
  by_cases hu : IsUnit (V.presheaf.germ ⊤ y trivial (h.appTop a))
  · exact (hu.pow n).mul_right_eq_zero.mp hzero
  · have hfl := hflat hu
    set aR : U.presheaf.stalk (h.base y) :=
      U.presheaf.germ ⊤ (h.base y) trivial a with haR
    have hregR : IsSMulRegular (U.presheaf.stalk (h.base y)) aR :=
      isSMulRegular_germ_of_isAffineOpen U (isAffineOpen_top U) ha ⟨h.base y, trivial⟩
    have hnzd : ∀ {R : Type u} [CommRing R] {c : R},
        IsSMulRegular R c → c ∈ nonZeroDivisors R := fun hc =>
      mem_nonZeroDivisors_iff.mpr
        ⟨fun x hx => hc (by simpa [smul_eq_mul] using hx),
          fun x hx => hc (by simpa [smul_eq_mul, mul_comm] using hx)⟩
    have hmem : aR ^ n ∈ nonZeroDivisors (U.presheaf.stalk (h.base y)) :=
      pow_mem (hnzd hregR) n
    let : Algebra (U.presheaf.stalk (h.base y)) (V.presheaf.stalk y) :=
      (h.stalkMap y).hom.toAlgebra
    have : Module.Flat (U.presheaf.stalk (h.base y)) (V.presheaf.stalk y) := hfl
    have hscalar : V.presheaf.germ ⊤ y trivial (h.appTop a) = (h.stalkMap y).hom aR := by
      rw [haR, Scheme.Hom.germ_stalkMap_apply h ⊤ y trivial a]
      rfl
    have hsmul : aR ^ n • V.presheaf.germ ⊤ y trivial s =
        (h.stalkMap y).hom (aR ^ n) * V.presheaf.germ ⊤ y trivial s := rfl
    have key : aR ^ n • V.presheaf.germ ⊤ y trivial s =
        aR ^ n • (0 : V.presheaf.stalk y) := by
      rwa [smul_zero, hsmul, map_pow, ← hscalar]
    exact Module.Flat.isSMulRegular_of_nonZeroDivisors hmem key

/-- **A section killed by a power of the pullback of a nonzerodivisor vanishes, if the morphism
is flat wherever that pullback is not invertible.**  Every germ vanishes by
`AlgebraicGeometry.Space.germ_eq_zero_of_pow_mul_eq_zero_of_isFlatAt`. -/
private theorem eq_zero_of_pow_mul_eq_zero_of_isFlatAt {V U : Scheme.{u}} [IsAffine U]
    (h : V ⟶ U) {a : Γ(U, ⊤)} (ha : IsSMulRegular Γ(U, ⊤) a) (s : Γ(V, ⊤)) (n : ℕ)
    (hn : h.appTop a ^ n * s = 0)
    (hflat : ∀ y : V, ¬ IsUnit (V.presheaf.germ ⊤ y trivial (h.appTop a)) →
      _root_.AlgebraicGeometry.IsFlatAt h.toLRSHom.toShHom y) :
    s = 0 := by
  refine TopCat.Presheaf.section_ext V.sheaf ⊤ s 0 fun y hy => ?_
  rw [map_zero]
  exact germ_eq_zero_of_pow_mul_eq_zero_of_isFlatAt h ha s n hn y (hflat y)


/-! ### Chart data at a point -/

/-- **An affine chart over an affine chart on which the defining ideal is generated by a
nonzerodivisor, through any point of any chart of the source.**

Let `f : Y ⟶ X` be a morphism of algebraic spaces over `S` and let `D ⊆ X` be a closed
subspace whose inverse image is an effective Cartier divisor on every étale scheme chart of
`X`, condition (3) of Stacks 083C.  Through every point of every étale chart of `Y` there is a
commuting square of affine étale scheme charts over `f` on whose chart of `X` the defining
ideal of `D` is generated by a nonzerodivisor `a`; the defining ideal of the inverse image
`f^{-1}D` on the chart of `Y` is then generated by the pullback of `a`, by Stacks 083X in the
form `AlgebraicGeometry.Space.definingIdealAt_preimage_eq_map`.

This refines the chart data of
`AlgebraicGeometry.Space.exists_openChart_isRegular_span_definingIdealAt_of_etalePullbacks`
from one space to a morphism, in the shape the vanishing argument below consumes. -/
theorem exists_affine_chartPair_isRegular_span_definingIdealAt
    {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X) (D : ClosedSubspaces B S hS X.1)
    (hD : HasEffectiveCartierEtalePullbacks B S hS X D)
    (V : SmallEtale B S hS Y.1) (z : (BigFppfOver.toScheme B S hS).obj V.1.left) :
    ∃ (T : SmallEtale B S hS Y.1) (π : T ⟶ V) (U : SmallEtale B S hS X.1)
        (p : T.1.left ⟶ U.1.left) (a : Γ((BigFppfOver.toScheme B S hS).obj U.1.left, ⊤)),
      yoneda.map p ≫ U.1.hom = T.1.hom ≫ f.hom ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj T.1.left) ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj U.1.left) ∧
      IsSMulRegular Γ((BigFppfOver.toScheme B S hS).obj U.1.left, ⊤) a ∧
      definingIdealAt B S hS Y ⟨D.1.preimage f.hom,
          isClosedSubspace_preimage B S hS f.hom D.1 X.2 Y.2 D.2⟩ (op T) =
        Ideal.span {((BigFppfOver.toScheme B S hS).map p).appTop.hom a} ∧
      ∃ w : (BigFppfOver.toScheme B S hS).obj T.1.left,
        (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS Y.1).map π) w = z := by
  obtain ⟨U₀, g₀, hg₀S, hg₀E⟩ := X.2.exists_atlas
  obtain ⟨V₁, π₁, q₁, hq₁, z₁, hz₁⟩ :=
    exists_chart_over B S hS f V ⟨CostructuredArrow.mk g₀, hg₀E⟩ hg₀S z
  obtain ⟨U', m, a, hU'aff, hreg, hgen, y', hy'⟩ :=
    exists_openChart_isRegular_span_definingIdealAt_of_etalePullbacks B S hS X D hD
      ⟨CostructuredArrow.mk g₀, hg₀E⟩ ((BigFppfOver.toScheme B S hS).map q₁ z₁)
  obtain ⟨T₂, π₂, p₂, hp₂, -, w₂, hw₂, -⟩ :=
    exists_chart_pullback B S hS f V₁ q₁ hq₁ m z₁ y' hy'.symm
  obtain ⟨T₃, π₃, hT₃aff, w₃, hw₃⟩ := exists_affine_chart_at B S hS Y.1 T₂ w₂
  have hp₃ : yoneda.map ((SmallEtale.toOver B S hS Y.1).map π₃ ≫ p₂) ≫ U'.1.hom =
      T₃.1.hom ≫ f.hom := by
    rw [Functor.map_comp, Category.assoc, hp₂, ← Category.assoc]
    exact congrArg (fun φ => φ ≫ f.hom) (CostructuredArrow.w (π₃.hom))
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj U'.1.left) := hU'aff
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj T₃.1.left) := hT₃aff
  refine ⟨T₃, π₃ ≫ π₂ ≫ π₁, U', (SmallEtale.toOver B S hS Y.1).map π₃ ≫ p₂, a, hp₃,
    hT₃aff, hU'aff, hreg.left.isSMulRegular, ?_, w₃, ?_⟩
  · rw [definingIdealAt_preimage_eq_map B S hS f D U' T₃
      ((SmallEtale.toOver B S hS Y.1).map π₃ ≫ p₂) hp₃, hgen]
    refine (Ideal.map_span ((BigFppfOver.toScheme B S hS).map
      ((SmallEtale.toOver B S hS Y.1).map π₃ ≫ p₂)).appTop.hom {a}).trans ?_
    congr 1
    exact Set.image_singleton
  · rw [Functor.map_comp, Functor.map_comp, Scheme.Hom.comp_apply,
      Functor.map_comp, Functor.map_comp, Scheme.Hom.comp_apply, hw₃, hw₂, hz₁]


/-! ### No sections supported on the inverse image -/

/-- Flatness at a point of an algebraic space, read as flatness of the chart morphism of a
commuting square of étale scheme charts at a point of the chart of the source. -/
private theorem schemeIsFlatAt_chart_of_isFlatAt {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (T : SmallEtale B S hS Y.1) (U : SmallEtale B S hS X.1) (p : T.1.left ⟶ U.1.left)
    (hp : yoneda.map p ≫ U.1.hom = T.1.hom ≫ f.hom)
    (y : (BigFppfOver.toScheme B S hS).obj T.1.left)
    (hflat : IsFlatAt B S hS f.hom (chartPointsMap T y)) :
    _root_.AlgebraicGeometry.IsFlatAt
      ((BigFppfOver.toScheme B S hS).map p).toLRSHom.toShHom y := by
  obtain ⟨q, hq⟩ := exists_fieldValuedPoint_schemePoint_eq B S hS T.1.left y
  have hfwd : (schemePointsHomeomorph B S hS T.1.left)
      (q.class B S hS (yoneda.obj T.1.left)) = y := hq
  have hsym : (schemePointsHomeomorph B S hS T.1.left).symm y =
      q.class B S hS (yoneda.obj T.1.left) := by
    rw [← hfwd, Homeomorph.symm_apply_apply]
  have hcl : pointsMap B S hS (yoneda.obj T.1.left) T.1.hom
      (q.class B S hS (yoneda.obj T.1.left)) = chartPointsMap T y := by
    rw [← hsym]
    rfl
  have h1 : IsFlatAt B S hS (yoneda.map p) (q.class B S hS (yoneda.obj T.1.left)) :=
    (isFlatAt_chart_iff B S hS f.hom T.1.left U.1.left T.1.hom U.1.hom p T.2 U.2 hp.symm q
      (IsLocalRing.closedPoint q.carrier)).mpr (by rwa [hcl])
  have h2 := (isFlatAt_yoneda_iff B S hS T.1.left U.1.left p q).mp h1
  rwa [hq] at h2

/-- **The structure sheaf has no section supported on the inverse image of a closed subspace
whose inverse images are effective Cartier, along a morphism flat above that subspace.**

Let `f : Y ⟶ X` be a morphism of algebraic spaces over `S` and let `D ⊆ X` be a closed subspace
satisfying condition (3) of Stacks 083C.  If `f` is flat at every point of `|Y|` lying over
`|D|`, then every local section of `𝒪_Y` whose support maps into the point set of `f^{-1}D` is
zero.

This is the algebraic-spaces form of the vanishing that the proof of Stacks 080F establishes
for schemes.  Through every point of the chart carrying the section there is an affine chart
over an affine chart of `X` on which `D` is cut out by a nonzerodivisor `a`, by
`AlgebraicGeometry.Space.exists_affine_chartPair_isRegular_span_definingIdealAt`; on it the
section is annihilated by a power of the pullback of `a`, because Stacks 0859 (2) in the form
`AlgebraicGeometry.Space.mem_supportedSectionsSubmodule_iff_mem_primaryComponent` identifies
the supported sections with that ideal-power torsion, the structure sheaf being quasi-coherent;
and the pullback of `a` acts injectively on every local ring of the chart — where it is
invertible because its germ is a unit, and where it is not because the point then lies over
`|D|`, so `f` is flat there and carries the nonzerodivisor `a` across.  Every point of the
chart is therefore a zero image of the section, and a section all of whose points are zero
images vanishes.

The conclusion is `AlgebraicGeometry.Space.HasNoSectionsSupportedIn` of
`StacksFrontier/AlgebraicGeometry/Spaces/StrictTransformUniversalProperty.lean`, spelled out:
that module cannot be imported here, since it lies above
`StacksFrontier/AlgebraicGeometry/Spaces/StrictTransformProperties.lean`, which consumes this
file. -/
theorem hasNoSectionsSupportedIn_preimage_of_isFlatAt
    {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X) (D : ClosedSubspaces B S hS X.1)
    (hD : HasEffectiveCartierEtalePullbacks B S hS X D)
    (hflat : ∀ y : points B S hS Y.1,
      pointsMap B S hS Y.1 f.hom y ∈ Set.range (pointsMap B S hS D.1.toFunctor D.1.ι) →
        IsFlatAt B S hS f.hom y) :
    ∀ (W₀ : SmallEtale B S hS Y.1)
      (s : (SheafOfModules.unit (structureRingSheaf B S hS Y)).val.obj (op W₀)),
      SectionSupportedIn B S hS Y.1 Y.2
        (Set.range (pointsMap B S hS
          (⟨D.1.preimage f.hom, isClosedSubspace_preimage B S hS f.hom D.1 X.2 Y.2 D.2⟩ :
            ClosedSubspaces B S hS Y.1).1.toFunctor
          (⟨D.1.preimage f.hom, isClosedSubspace_preimage B S hS f.hom D.1 X.2 Y.2 D.2⟩ :
            ClosedSubspaces B S hS Y.1).1.ι))
        (SheafOfModules.unit (structureRingSheaf B S hS Y)) W₀ s →
      s = 0 := by
  classical
  set Dpre : ClosedSubspaces B S hS Y.1 :=
    ⟨D.1.preimage f.hom, isClosedSubspace_preimage B S hS f.hom D.1 X.2 Y.2 D.2⟩ with hDpre
  set G : Modules.{u, u} B S hS Y.1 Y.2 := SheafOfModules.unit (structureRingSheaf B S hS Y)
  have hGqc : G.IsQuasicoherentOnSite := SheafOfModules.isQuasicoherentOnSite_unit _
  intro W₀ s hs
  have hzi : ∀ x : points B S hS (yoneda.obj ((SmallEtale.toOver B S hS Y.1).obj W₀)),
      x ∈ zeroImages B S hS Y.1 (moduleAddSheaf B S hS Y.1 Y.2 G) W₀ s := by
    intro x
    obtain ⟨T, π, U, p, a, hp, hTaff, hUaff, hareg, hgen, w, hw⟩ :=
      exists_affine_chartPair_isRegular_span_definingIdealAt B S hS f D hD W₀
        (pointsToScheme B S hS ((SmallEtale.toOver B S hS Y.1).obj W₀) x)
    have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj U.1.left) := hUaff
    have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj T.1.left) := hTaff
    -- membership in the primary component of a principal ideal, as annihilation by a power
    have hprim : ∀ {R : Type u} [CommRing R] (a s : R),
        s ∈ Ideal.primaryComponent R (Ideal.span {a}) ↔ ∃ n : ℕ, a ^ n * s = 0 := by
      intro R _ a s
      rw [Ideal.primaryComponent_mem]
      constructor
      · rintro ⟨n, hn⟩
        rw [Submodule.mem_torsionBySet_iff] at hn
        refine ⟨n, ?_⟩
        have h := hn ⟨a ^ n, by
          rw [SetLike.mem_coe, Ideal.span_singleton_pow]
          exact Ideal.mem_span_singleton_self _⟩
        rwa [smul_eq_mul] at h
      · rintro ⟨n, hn⟩
        refine ⟨n, ?_⟩
        rw [Submodule.mem_torsionBySet_iff]
        intro c
        have hc : (c : R) ∈ Ideal.span {a ^ n} := by
          rw [← Ideal.span_singleton_pow]
          exact c.2
        obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp hc
        rw [smul_eq_mul, hd, mul_comm (a ^ n) d, mul_assoc, hn, mul_zero]
    have htor : ∀ t : Γ((BigFppfOver.toScheme B S hS).obj T.1.left, ⊤),
        t ∈ (supportedSectionsSubmodule B S hS Y.1 Y.2
              (Set.range (pointsMap B S hS Dpre.1.toFunctor Dpre.1.ι))
              G).toSubmodule.obj (op T) ↔
          ∃ n : ℕ, ((BigFppfOver.toScheme B S hS).map p).appTop a ^ n * t = 0 := fun t =>
      (mem_supportedSectionsSubmodule_iff_mem_primaryComponent B S hS Y Dpre G hGqc T hTaff
          _ hgen t).trans
        (hprim _ t)
    obtain ⟨n, hn⟩ := (htor (G.val.map π.op s)).mp
      ((mem_supportedSectionsSubmodule_iff B S hS Y.1 Y.2 _ G T _).mpr
        (sectionSupportedIn_restrict π s hs))
    have hres : G.val.map π.op s = 0 := by
      refine eq_zero_of_pow_mul_eq_zero_of_isFlatAt ((BigFppfOver.toScheme B S hS).map p)
        hareg (G.val.map π.op s) n hn fun y hy => ?_
      obtain ⟨y, rfl⟩ : ∃ y' : chartScheme T, y' = y := ⟨y, rfl⟩
      refine schemeIsFlatAt_chart_of_isFlatAt B S hS f T U p hp y (hflat _ ?_)
      have hpt : chartPointsMap T y ∈
          Set.range (pointsMap B S hS Dpre.1.toFunctor Dpre.1.ι) := by
        rw [← Set.mem_preimage, preimage_chartPointsMap_range_ι_eq_zeroLocus B S hS Y Dpre T
          hTaff (Ideal.span {((BigFppfOver.toScheme B S hS).map p).appTop a}) hgen]
        refine (Scheme.mem_zeroLocus_iff _ _ y).mpr ?_
        rintro c hc
        obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton.mp hc
        rw [Scheme.basicOpen_mul]
        intro hmemc
        exact hy ((Scheme.mem_basicOpen (chartScheme T) (U := ⊤) _ y trivial).mp hmemc.1)
      rwa [hDpre, range_pointsMap_preimage_ι B S hS f.hom D.1] at hpt
    refine ⟨T, π, hres, ?_⟩
    obtain ⟨y₀, hy₀⟩ := surjective_pointsToScheme B S hS ((SmallEtale.toOver B S hS Y.1).obj T) w
    refine ⟨y₀, injective_pointsToScheme B S hS ((SmallEtale.toOver B S hS Y.1).obj W₀) ?_⟩
    rw [pointsToScheme_pointsMap, hy₀, hw]
  have hzero := eq_zero_of_imageInOpen_zeroImages B S hS Y.1
    (moduleAddSheaf B S hS Y.1 Y.2 G) W₀ s W₀ (𝟙 W₀) fun y => by simpa using hzi _
  rwa [op_id, (moduleAddSheaf B S hS Y.1 Y.2 G).obj.map_id] at hzero


/-! ### The ideal of supported sections on the strict-transform fibre product -/

section Blowup

variable {A X A' : AlgebraicSpaces B S hS}

/-- **The projection `X ×_A A' ⟶ A'` is flat at every point lying over the exceptional
divisor**, when `X` is flat over `A` at every point lying over the centre `Z`.

The exceptional divisor is the inverse image of `Z`, so a point of `X ×_A A'` lying over it
lies over `Z`, and its image in `|X|` therefore lies over `Z` as well; flatness of `f` there
passes to the projection by `AlgebraicGeometry.Space.isFlatAt_of_isPullback`. -/
theorem isFlatAt_strictTransformPullbackToBlowUp_of_isFlatAt (f : X ⟶ A) (b : A' ⟶ A)
    (Z : ClosedSubspaces B S hS A.1)
    (hflat : ∀ x : points B S hS X.1,
      pointsMap B S hS X.1 f.hom x ∈ Set.range (pointsMap B S hS Z.1.toFunctor Z.1.ι) →
        IsFlatAt B S hS f.hom x)
    (w : points B S hS (strictTransformPullback B S hS f b).1)
    (hw : pointsMap B S hS (strictTransformPullback B S hS f b).1
        (strictTransformPullbackToBlowUp B S hS f b).hom w ∈
      Set.range (pointsMap B S hS (preimageClosedSubspace b Z).1.toFunctor
        (preimageClosedSubspace b Z).1.ι)) :
    IsFlatAt B S hS (strictTransformPullbackToBlowUp B S hS f b).hom w := by
  have sq := AlgebraicSpaces.isPullback_fiberProduct B S hS f b
  refine isFlatAt_of_isPullback B S hS sq w (hflat _ ?_)
  have hcomp : pointsMap B S hS A'.1 b.hom
        (pointsMap B S hS (strictTransformPullback B S hS f b).1
          (strictTransformPullbackToBlowUp B S hS f b).hom w) =
      pointsMap B S hS X.1 f.hom
        (pointsMap B S hS (strictTransformPullback B S hS f b).1
          (strictTransformPullbackToSource B S hS f b).hom w) := by
    exact pointsMap_apply_comm B S hS (congrArg (·.hom) sq.w).symm w
  rw [← hcomp]
  exact (range_pointsMap_preimage_ι B S hS b.hom Z.1).le hw

/-- **Stacks 0865, part (1), the ideal of supported sections.**  Let `Z ⊆ A` be a closed
subspace of an algebraic space over `S`, let `b : A' ⟶ A` be the blowup of `A` in `Z` and let
`f : X ⟶ A` be flat at every point lying over `Z`.  Then the ideal of sections of
`𝒪_{X ×_A A'}` supported on the exceptional preimage vanishes on every affine étale chart.

This is the input `hloc` that
`AlgebraicGeometry.Space.strictTransformSubfunctor_eq_top_of_isFlatAt` carries as a
hypothesis: the exceptional divisor is an effective Cartier divisor on `A'` because `b` is a
blowup, so
`AlgebraicGeometry.Space.hasNoSectionsSupportedIn_preimage_of_isFlatAt` applies to the
projection `X ×_A A' ⟶ A'`, which is flat above the exceptional divisor by
`AlgebraicGeometry.Space.isFlatAt_strictTransformPullbackToBlowUp_of_isFlatAt`. -/
theorem strictTransformIdealSubmodule_eq_bot_of_isFlatAt (f : X ⟶ A) (b : A' ⟶ A)
    (Z : ClosedSubspaces B S hS A.1) (hb : IsBlowupAlong B S hS Z b)
    (hflat : ∀ x : points B S hS X.1,
      pointsMap B S hS X.1 f.hom x ∈ Set.range (pointsMap B S hS Z.1.toFunctor Z.1.ι) →
        IsFlatAt B S hS f.hom x)
    (U : SmallEtale B S hS (strictTransformPullback B S hS f b).1) :
    (strictTransformIdealSubmodule B S hS f b (Z.1.preimage b.hom)).toSubmodule.obj (op U) = ⊥ := by
  have hD : HasEffectiveCartierEtalePullbacks B S hS A' (preimageClosedSubspace b Z) :=
    hasEffectiveCartierEtalePullbacks_of_isEffectiveCartier B S hS A'
      (preimageClosedSubspace b Z) hb.isPullbackDefined
  have hno := hasNoSectionsSupportedIn_preimage_of_isFlatAt B S hS
    (strictTransformPullbackToBlowUp B S hS f b) (preimageClosedSubspace b Z) hD
    (isFlatAt_strictTransformPullbackToBlowUp_of_isFlatAt B S hS f b Z hflat)
  exact (Submodule.eq_bot_iff _).mpr fun x hx => hno U x
    ((mem_supportedSectionsSubmodule_iff B S hS (strictTransformPullback B S hS f b).1
      (strictTransformPullback B S hS f b).2 _ _ U x).mp hx)

end Blowup

end AlgebraicGeometry.Space

end
