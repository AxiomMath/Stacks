module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.NonAlgebraizableLevelChart
public import StacksFrontier.AlgebraicGeometry.NormInvertible.TwoChartPushforward

/-!
# The transition maps `𝓛ₙ₊₁ ⟶ 𝓛ₙ` of the non-algebraizable example

For `A = k[x,y][[t]]` the module `𝓛ₙ` of [Stacks, Tag 0EHE] lives on the punctured spectrum of
`A/tⁿA`, glued from the two charts `D(x̄)` and `D(ȳ)` along the transition element
(`Stacks.Algebraization.NonAlgebraizableExample.levelModule`). The reduction `A/t^{n+1}A → A/tⁿA`
gives a closed immersion of punctured spectra, and this file produces the transition map of the
system `(𝓛ₙ)` out of it: the morphism of schemes carries the transition unit of level `n + 1` to
the one of level `n`, so `Stacks.SheafOfModules.glueHomOfOverlapUnit` applies.

The ring-level compatibility is
`Stacks.Algebraization.NonAlgebraizableExample.chartReduction_transitionElement`. Everything here
is its transport to the scheme level, across the identification of the chart ring with a ring of
sections (`Stacks.Algebraization.NonAlgebraizableExample.chartOpenEquiv`) and across
`Stacks.Algebraization.NonAlgebraizableExample.levelOverlapRingEquiv`.

## Main definitions

* `Stacks.Algebraization.NonAlgebraizableExample.levelOverlap` — the overlap `D(x̄ȳ)` of the two
  charts, as an open of the punctured spectrum of `A/tⁿA`.
* `Stacks.Algebraization.NonAlgebraizableExample.levelReductionRing` — the reduction
  `A/t^{n+1}A → A/tⁿA`.
* `Stacks.Algebraization.NonAlgebraizableExample.levelSchemeMap` and `levelOpenMap` — the closed
  immersion `Spec(A/tⁿA) ⟶ Spec(A/t^{n+1}A)` and its restriction to the punctured spectra.
* `Stacks.Algebraization.NonAlgebraizableExample.levelTransition` — the transition map
  `𝓛ₙ₊₁ ⟶ (𝓛ₙ)` of the system, as a morphism into the direct image of `𝓛ₙ`.

## Main results

* `Stacks.Algebraization.NonAlgebraizableExample.preimage_levelChart` — the preimage of a chart of
  level `n + 1` is the chart of level `n`.
* `Stacks.Algebraization.NonAlgebraizableExample.app_levelSchemeMap_chartOpenEquiv` — on the chart
  rings the closed immersion induces the reduction `A_r/t^{n+1}A_r → A_r/tⁿA_r`.
* `Stacks.Algebraization.NonAlgebraizableExample.app_levelOverlapUnit` — the closed immersion of
  punctured spectra carries the transition unit of level `n + 1` to the one of level `n`. This is
  the intertwining hypothesis the transition map is built from.
* `Stacks.Algebraization.NonAlgebraizableExample.chartLinearEquiv_levelTransition` — in the chart
  trivializations the transition map is the reduction of functions, which pins it down.

## Implementation notes

Both `levelSchemeMap` and `levelOpenMap` are `abbrev`s, as `levelToAmbient` already is, so that
Mathlib's `AlgebraicGeometry.Scheme.Hom.resLE_appLE` and
`AlgebraicGeometry.Scheme.Hom.resLE_preimage` apply to them without an unfolding step. The
proof-carrying `≤` argument of `AlgebraicGeometry.Scheme.Hom.resLE` is given as
`(preimage_levelOpen k n).ge` rather than as `le_rfl`, equal though the two opens are by `rfl`: the
stated type is then the one those lemmas unify against, and `le_rfl` makes them fail.

Two statements about `levelSchemeMap` hold by `rfl`: the preimage of a basic open is the basic open
of the reduced element, and hence the preimage of the punctured spectrum of `A/t^{n+1}A` is the
punctured spectrum of `A/tⁿA`. The corresponding statement one level up, for `levelOpenMap` and the
charts of the punctured spectra, is not `rfl` — `AlgebraicGeometry.Scheme.Hom.resLE` goes through a
pullback — and is `preimage_levelChart`.

The ring-hom identity that carries the transport on the affine charts,
`app_levelSchemeMap_chartOpenEquiv`, is proved by `IsLocalization.ringHom_ext` against
`Stacks.Algebraization.NonAlgebraizableExample.isLocalization_away_levelToChart`: a ring map out of
the chart ring is determined by its restriction to the level ring, where the identity is
`AlgebraicGeometry.StructureSheaf.toOpen_comp_comap`. So no computation with sections of the
structure sheaf is needed there. Passing from the affine charts to the opens of the punctured
spectra is then `AlgebraicGeometry.Scheme.Hom.resLE_appLE` together with the `appLE` calculus, and
the transports inside `levelOverlapRingEquiv` collapse against it because any two morphisms of
opens with the same source and target are equal.

## References

* [Stacks Project, Tag 0EHE](https://stacks.math.columbia.edu/tag/0EHE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.Algebraization.NonAlgebraizableExample

variable (k : Type u) [Field k]

/-- The overlap `D(x̄ȳ)` of the two charts, as an open of the punctured spectrum of `A/tⁿA`. -/
public abbrev levelOverlap (n : ℕ) : (levelOpen k n).toScheme.Opens :=
  levelChart k (xVar k) n ⊓ levelChart k (yVar k) n

/-- The reduction `A/t^{n+1}A → A/tⁿA` of the level rings. -/
public def levelReductionRing (n : ℕ) : levelRing k (n + 1) →+* levelRing k n :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ n))

/-- The closed immersion `Spec(A/tⁿA) ⟶ Spec(A/t^{n+1}A)` of level schemes. -/
public abbrev levelSchemeMap (n : ℕ) : levelScheme k n ⟶ levelScheme k (n + 1) :=
  Spec.map (CommRingCat.ofHom (levelReductionRing k n))

/-- The preimage of a basic open `D(r̄)` of `Spec(A/t^{n+1}A)` is the basic open `D(r̄)` of
`Spec(A/tⁿA)`: the reduction carries the one image of `r` to the other. -/
public theorem preimage_chartOpen (r : AmbientRing k) (n : ℕ) :
    levelSchemeMap k n ⁻¹ᵁ chartOpen k r (n + 1) = chartOpen k r n := rfl

/-- The preimage of the punctured spectrum of `A/t^{n+1}A` is the punctured spectrum of
`A/tⁿA`. -/
public theorem preimage_levelOpen (n : ℕ) :
    levelSchemeMap k n ⁻¹ᵁ levelOpen k (n + 1) = levelOpen k n := rfl

/-- The closed immersion of the punctured spectrum of `A/tⁿA` in that of `A/t^{n+1}A`, the
restriction of `levelSchemeMap` to the two opens it carries one into the other. -/
public abbrev levelOpenMap (n : ℕ) :
    (levelOpen k n).toScheme ⟶ (levelOpen k (n + 1)).toScheme :=
  (levelSchemeMap k n).resLE (levelOpen k (n + 1)) (levelOpen k n) (preimage_levelOpen k n).ge

/-- **Stacks Project, Tag 0EHE (the charts are compatible down the tower).** The preimage of the
chart `D(r̄)` of the punctured spectrum of `A/t^{n+1}A` is the chart `D(r̄)` of the punctured
spectrum of `A/tⁿA`, for a chart whose basic open lies in the punctured spectrum. -/
@[stacks 0EHE "the preimage of the chart D(r) of level n+1 is the chart D(r) of level n"]
public theorem preimage_levelChart (r : AmbientRing k) (n : ℕ)
    (h : chartOpen k r (n + 1) ≤ levelOpen k (n + 1)) :
    levelOpenMap k n ⁻¹ᵁ levelChart k r (n + 1) = levelChart k r n := by
  rw [Scheme.Hom.resLE_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι, inf_eq_right.mpr h]
  rfl

/-- The preimage of the overlap of the two charts of level `n + 1` is the overlap of the two
charts of level `n`. -/
public theorem preimage_levelOverlap (n : ℕ) :
    levelOpenMap k n ⁻¹ᵁ levelOverlap k (n + 1) = levelOverlap k n := by
  change levelOpenMap k n ⁻¹ᵁ levelChart k (xVar k) (n + 1) ⊓
      levelOpenMap k n ⁻¹ᵁ levelChart k (yVar k) (n + 1) = _
  rw [preimage_levelChart k (xVar k) n (le_sup_left : chartOpen k (xVar k) (n + 1) ≤ _),
    preimage_levelChart k (yVar k) n (le_sup_right : chartOpen k (yVar k) (n + 1) ≤ _)]

/-- The image in `Spec(A/tⁿA)` of the overlap of the two charts is the basic open `D(x̄ȳ)`. -/
public theorem image_levelOverlap (n : ℕ) :
    (levelOpen k n).ι ''ᵁ levelOverlap k n = chartOpen k (xVar k * yVar k) n := by
  rw [levelOverlap, inf_levelChart]
  exact image_levelChart_mul k n

/-- Restricting a function to a chart commutes with reduction modulo `tⁿ`. -/
public theorem chartReduction_levelToChart (r : AmbientRing k) (n : ℕ)
    (z : levelRing k (n + 1)) :
    chartReduction k r n (levelToChart k r (n + 1) z) =
      levelToChart k r n (levelReductionRing k n z) := by
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
  rfl

/-- **Stacks Project, Tag 0EHE (the closed immersion induces the reduction on chart rings).** On
the ring of sections over the basic open `D(r̄)`, the closed immersion
`Spec(A/tⁿA) ⟶ Spec(A/t^{n+1}A)` induces the reduction `A_r/t^{n+1}A_r → A_r/tⁿA_r`. -/
@[stacks 0EHE "on D(r) the closed immersion of level schemes induces A_r/t^(n+1) -> A_r/t^n"]
public theorem app_levelSchemeMap_chartOpenEquiv (r : AmbientRing k) (n : ℕ)
    (w : chartRing k r (n + 1)) :
    ((levelSchemeMap k n).app (chartOpen k r (n + 1))).hom (chartOpenEquiv k r (n + 1) w) =
      chartOpenEquiv k r n (chartReduction k r n w) := by
  have : IsLocalization.Away (levelElt k r (n + 1)) (chartRing k r (n + 1)) :=
    isLocalization_away_levelToChart k r (n + 1)
  have hext : ((levelSchemeMap k n).app (chartOpen k r (n + 1))).hom.comp
      (chartOpenEquiv k r (n + 1)).toRingEquiv.toRingHom =
      (chartOpenEquiv k r n).toRingEquiv.toRingHom.comp (chartReduction k r n).toRingHom := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (levelElt k r (n + 1)))
      (RingHom.ext fun z => ?_)
    have h1 : chartOpenEquiv k r (n + 1) (levelToChart k r (n + 1) z) =
        algebraMap (levelRing k (n + 1)) Γ(levelScheme k (n + 1), chartOpen k r (n + 1)) z :=
      (chartOpenEquiv k r (n + 1)).commutes z
    have h2 : chartOpenEquiv k r n (chartReduction k r n (levelToChart k r (n + 1) z)) =
        algebraMap (levelRing k n) Γ(levelScheme k n, chartOpen k r n)
          (levelReductionRing k n z) := by
      rw [chartReduction_levelToChart]
      exact (chartOpenEquiv k r n).commutes _
    change ((levelSchemeMap k n).app (chartOpen k r (n + 1))).hom
        (chartOpenEquiv k r (n + 1) (levelToChart k r (n + 1) z)) =
      chartOpenEquiv k r n (chartReduction k r n (levelToChart k r (n + 1) z))
    exact (congrArg ((levelSchemeMap k n).app (chartOpen k r (n + 1))).hom h1).trans
      ((StructureSheaf.toOpen_comp_comap_apply (levelReductionRing k n)
        (chartOpen k r (n + 1)) z).trans h2.symm)
  exact DFunLike.congr_fun hext w

/-- Two restrictions of sections compose to the restriction along any morphism with the same
source and target. -/
private theorem presheaf_map_hom_comp {C : Type*} [Category C] [Quiver.IsThin C]
    (F : Cᵒᵖ ⥤ CommRingCat) {U V W : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) (h : U ⟶ W) (x : F.obj U) :
    (F.map g).hom ((F.map f).hom x) = (F.map h).hom x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp, Subsingleton.elim (f ≫ g) h]

/-- The sections of `𝒪` over the overlap of the two charts are the chart ring `A_{xy}/tⁿA_{xy}`
through restriction from the basic open `D(x̄ȳ)` of `Spec(A/tⁿA)`. -/
public theorem levelOverlapRingEquiv_apply (n : ℕ) (v : chartRing k (xVar k * yVar k) n) :
    levelOverlapRingEquiv k n v =
      ((levelScheme k n).presheaf.map (homOfLE (image_levelOverlap k n).le).op).hom
        (chartOpenEquiv k (xVar k * yVar k) n v) :=
  presheaf_map_hom_comp (levelScheme k n).presheaf (eqToIso (image_levelChart_mul k n)).op.hom
    ((levelOpen k n).ι.opensFunctor.map (eqToHom (inf_levelChart k n))).op _ _

/-- Restricting the sections over the overlap of the two charts to a smaller open which still
covers the basic open `D(x̄ȳ)`, read through the chart ring. -/
public theorem map_levelOverlapRingEquiv (n : ℕ) {W : (levelOpen k n).toScheme.Opens}
    (hW : (levelOpen k n).ι ''ᵁ W = chartOpen k (xVar k * yVar k) n)
    (h : W ≤ levelOverlap k n) (v : chartRing k (xVar k * yVar k) n) :
    ((levelOpen k n).toScheme.presheaf.map (homOfLE h).op).hom (levelOverlapRingEquiv k n v) =
      ((levelScheme k n).presheaf.map (homOfLE hW.le).op).hom
        (chartOpenEquiv k (xVar k * yVar k) n v) := by
  rw [levelOverlapRingEquiv_apply]
  exact presheaf_map_hom_comp (levelScheme k n).presheaf _ _ _ _

/-- The closed immersion of punctured spectra, read on the sections over the overlap of the two
charts, is the reduction of the chart ring `A_{xy}/t^{n+1}A_{xy} → A_{xy}/tⁿA_{xy}`. -/
public theorem appLE_levelOpenMap_levelOverlapRingEquiv (n : ℕ)
    {W : (levelOpen k n).toScheme.Opens}
    (hW : (levelOpen k n).ι ''ᵁ W = chartOpen k (xVar k * yVar k) n)
    (e : W ≤ levelOpenMap k n ⁻¹ᵁ levelOverlap k (n + 1)) (h : W ≤ levelOverlap k n)
    (v : chartRing k (xVar k * yVar k) (n + 1)) :
    ((levelOpenMap k n).appLE (levelOverlap k (n + 1)) W e).hom
        (levelOverlapRingEquiv k (n + 1) v) =
      ((levelOpen k n).toScheme.presheaf.map (homOfLE h).op).hom
        (levelOverlapRingEquiv k n (chartReduction k (xVar k * yVar k) n v)) := by
  have h1 := Scheme.Hom.map_appLE (levelSchemeMap k n)
    (U := (levelOpen k (n + 1)).ι ''ᵁ levelOverlap k (n + 1))
    (U' := chartOpen k (xVar k * yVar k) (n + 1)) (V := (levelOpen k n).ι ''ᵁ W)
    ((Scheme.Hom.le_resLE_preimage_iff (levelSchemeMap k n) (preimage_levelOpen k n).ge
      (levelOverlap k (n + 1)) W).mp e)
    (homOfLE (image_levelOverlap k (n + 1)).le).op
  have h2 := Scheme.Hom.appLE_map (levelSchemeMap k n)
    (U := chartOpen k (xVar k * yVar k) (n + 1))
    (V := levelSchemeMap k n ⁻¹ᵁ chartOpen k (xVar k * yVar k) (n + 1))
    (V' := (levelOpen k n).ι ''ᵁ W) le_rfl (homOfLE hW.le).op
  rw [Scheme.Hom.appLE_eq_app] at h2
  have hsq : (levelScheme k (n + 1)).presheaf.map
        (homOfLE (image_levelOverlap k (n + 1)).le).op ≫
      (levelOpenMap k n).appLE (levelOverlap k (n + 1)) W e =
    (levelSchemeMap k n).app (chartOpen k (xVar k * yVar k) (n + 1)) ≫
      (levelScheme k n).presheaf.map (homOfLE hW.le).op := by
    rw [Scheme.Hom.resLE_appLE]
    exact h1.trans h2.symm
  rw [levelOverlapRingEquiv_apply, map_levelOverlapRingEquiv k n hW h,
    ← app_levelSchemeMap_chartOpenEquiv]
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hsq)
    (chartOpenEquiv k (xVar k * yVar k) (n + 1) v)

/-- The closed immersion of punctured spectra, read on the sections over the overlap of the two
charts, is the reduction `A_{xy}/t^{n+1}A_{xy} → A_{xy}/tⁿA_{xy}` followed by restriction. -/
public theorem app_levelOverlapRingEquiv (n : ℕ) (v : chartRing k (xVar k * yVar k) (n + 1)) :
    ((levelOpenMap k n).app (levelOverlap k (n + 1))).hom
        (levelOverlapRingEquiv k (n + 1) v) =
      ((levelOpen k n).toScheme.presheaf.map (homOfLE (preimage_levelOverlap k n).le).op).hom
        (levelOverlapRingEquiv k n (chartReduction k (xVar k * yVar k) n v)) := by
  rw [← Scheme.Hom.appLE_eq_app]
  exact appLE_levelOpenMap_levelOverlapRingEquiv k n
    ((congrArg (fun W => (levelOpen k n).ι ''ᵁ W) (preimage_levelOverlap k n)).trans
      (image_levelOverlap k n)) le_rfl (preimage_levelOverlap k n).le v

/-- **Stacks Project, Tag 0EHE (the transition units form a tower on the schemes).** The closed
immersion of the punctured spectrum of `A/tⁿA` in that of `A/t^{n+1}A` carries the transition unit
of level `n + 1` to the transition unit of level `n`. This is the scheme-level form of
`Stacks.Algebraization.NonAlgebraizableExample.chartReduction_transitionElement`, and the
intertwining hypothesis the transition map `𝓛ₙ₊₁ ⟶ 𝓛ₙ` is built from. -/
@[stacks 0EHE "the closed immersion of punctured spectra carries u at level n+1 to u at level n"]
public theorem app_levelOverlapUnit (a : ℕ → PlaneRing k) (φ : ℕ → ℕ) (n : ℕ) :
    Units.map ((levelOpenMap k n).app (levelOverlap k (n + 1))).hom
        (levelOverlapUnit k a φ (n + 1)) =
      Stacks.SheafOfModules.overlapUnit (levelOverlapUnit k a φ n)
        (levelOpenMap k n ⁻¹ᵁ levelOverlap k (n + 1)) (preimage_levelOverlap k n).le := by
  refine Units.ext ?_
  change ((levelOpenMap k n).app (levelOverlap k (n + 1))).hom
      (levelOverlapRingEquiv k (n + 1) (isUnit_transitionElement k a φ (n + 1)).unit.val) =
    ((levelOpen k n).toScheme.presheaf.map (homOfLE (preimage_levelOverlap k n).le).op).hom
      (levelOverlapRingEquiv k n (isUnit_transitionElement k a φ n).unit.val)
  rw [IsUnit.unit_spec, IsUnit.unit_spec]
  exact (app_levelOverlapRingEquiv k n (transitionElement k a φ (n + 1))).trans
    (congrArg (fun z => ((levelOpen k n).toScheme.presheaf.map
      (homOfLE (preimage_levelOverlap k n).le).op).hom (levelOverlapRingEquiv k n z))
      (chartReduction_transitionElement k a φ n))

/-- **Stacks Project, Tag 0EHE (the transition maps of the system).** The transition map
`𝓛ₙ₊₁ ⟶ 𝓛ₙ` of the system of [Stacks, Tag 0EHE], as a morphism from the module of level `n + 1`
on the punctured spectrum of `A/t^{n+1}A` to the direct image of the module of level `n` along the
closed immersion of punctured spectra. -/
@[stacks 0EHE "the transition map L_(n+1) -> L_n of the system"]
public def levelTransition (a : ℕ → PlaneRing k) (φ : ℕ → ℕ) (n : ℕ) :
    levelModule k a φ (n + 1) ⟶
      (Scheme.Modules.pushforward (levelOpenMap k n)).obj (levelModule k a φ n) :=
  Stacks.SheafOfModules.glueHomOfOverlapUnit (levelOpenMap k n) (levelOverlapUnit k a φ (n + 1))
    (levelOverlapUnit k a φ n)
    (preimage_levelChart k (xVar k) n (le_sup_left : chartOpen k (xVar k) (n + 1) ≤ _))
    (preimage_levelChart k (yVar k) n (le_sup_right : chartOpen k (yVar k) (n + 1) ≤ _))
    (app_levelOverlapUnit k a φ n)

/-- **Stacks Project, Tag 0EHE (the transition map in the chart trivializations).** Over an open
inside one of the two charts, where both modules are trivialized by reading the coordinate of that
chart, the transition map is the reduction of functions. This pins `levelTransition` down. -/
@[stacks 0EHE "in the chart trivializations L_(n+1) -> L_n is the reduction of functions"]
public theorem chartLinearEquiv_levelTransition (a : ℕ → PlaneRing k) (φ : ℕ → ℕ) (n : ℕ)
    (i : ULift.{u} Bool) {V : (levelOpen k (n + 1)).toScheme.Opens}
    (hV : V ≤ Stacks.SheafOfModules.twoChartFamily
      (levelChart k (xVar k) (n + 1)) (levelChart k (yVar k) (n + 1)) i)
    (hV' : levelOpenMap k n ⁻¹ᵁ V ≤ Stacks.SheafOfModules.twoChartFamily
      (levelChart k (xVar k) n) (levelChart k (yVar k) n) i)
    (s : (Stacks.SheafOfModules.twoChartCocycle
      (levelOverlapUnit k a φ (n + 1))).sectionsSubmodule V) :
    (Stacks.SheafOfModules.twoChartCocycle (levelOverlapUnit k a φ n)).chartLinearEquiv i hV'
        ((levelTransition k a φ n).val.app (op V) s) =
      ((levelOpenMap k n).app V).hom
        ((Stacks.SheafOfModules.twoChartCocycle
          (levelOverlapUnit k a φ (n + 1))).chartLinearEquiv i hV s) :=
  Stacks.SheafOfModules.chartLinearEquiv_glueHomOfOverlapUnit (levelOpenMap k n) _ _ _ _
    (app_levelOverlapUnit k a φ n) i hV hV' s

end Stacks.Algebraization.NonAlgebraizableExample

end
