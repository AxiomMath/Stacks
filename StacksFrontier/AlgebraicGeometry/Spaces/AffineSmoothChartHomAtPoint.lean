module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineSmoothChartAtPoint
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The site morphism under the affine smooth chart of Stacks 056U

`AlgebraicGeometry.Space`
`.exists_affine_chartGeometricPoint_isClosed_isRegularLocalRing_finiteSeparable` produces the
slicing datum of the chart construction of **Stacks 06N3** — an affine étale chart
`Vch` of `F = U ×_𝒳 Spec k` through a prescribed point, a closed point `v` on it with regular
local ring and finite separable residue field, and a geometric point above `v` — but it states
the smoothness at a *bare morphism of schemes* `π : chartScheme Vch ⟶ Spec k`, existentially
quantified. The morphism of the site underneath `π` is produced inside its proof, by
`AlgebraicGeometry.Space.exists_hom_comp_eq_yoneda_map`, and then discarded.

Two consumers of the chart need exactly that discarded datum:

* `AlgebraicGeometry.Space.exists_representedUnitSection_isRegular_etaleLocalRing_of_isAffine`,
  which reads the slicing sequence of **Stacks 06MD** off the chart, takes the morphism of the
  site `p : Vch ⟶ T` together with the square `Vch.obj.hom ≫ ξ = yoneda.map p` — it has to, since
  the regular sequence it produces is a sequence of global *sections of the structure sheaf of
  the algebraic space*, whose value on the chart is the pullback of a global function along the
  morphism of the site;
* `AlgebraicGeometry.Stack`
  `.exists_fibreIsUnramifiedNear_zeroLocusOnOpen_of_forall_germ_mem_maximalIdeal`, which asks for
  the étale chart of the fibre with a morphism `β` to the site object on `Spec k` under the
  structure morphism, in the same shape.

This file states the chart with both of them retained. Nothing new is proved: the proof is that
of the unstrengthened form with the square kept rather than dropped, and the structure morphism
of the chart spelled out as the composite
`(BigFppfOver.toScheme B S hS).map h ≫ eqToHom hT` it is built from, instead of being hidden
behind an existential.

## Main results

* `AlgebraicGeometry.Space`
  `.exists_affine_chartGeometricPoint_hom_isClosed_isRegularLocalRing_finiteSeparable`: the
  slicing datum of **Stacks 06N3** at a prescribed point of `|F|`, together with the
  morphism of the site under the structure morphism of the chart and the commuting square
  exhibiting it.

## Implementation notes

The structure morphism `π` stays existentially quantified, with the defining equation
`π = (BigFppfOver.toScheme B S hS).map h ≫ eqToHom hT` beside it, rather than being replaced by
that composite throughout: the residue field clause is a `letI` over the algebra structure
`π` induces, and stating it at a variable keeps it one instance to elaborate instead of a
composite to re-synthesize at each of its four occurrences. A consumer substitutes the equation.

Smoothness is recorded both for `(BigFppfOver.toScheme B S hS).map h` — the form
`AlgebraicGeometry.Space.smooth_toScheme_map_of_isSmooth_yoneda` delivers it in, and the one the
slicing lemmas ask for — and for `π`, which is what **Stacks 056U** was applied to.

A caller feeding `h` to
`AlgebraicGeometry.Space.exists_representedUnitSection_isRegular_etaleLocalRing_of_isAffine`
hands it over as the morphism of the site below the small étale neighbourhood
`AlgebraicGeometry.Space.SmallEtaleNeighborhood.ofChartGeometricPoint B S hS X Vch y`, whose
chart is `Vch` by `rfl` but not reducibly: the instance arguments of that lemma — the
`AlgebraicGeometry.LocallyOfFiniteType` of `(BigFppfOver.toScheme B S hS).map h` — therefore have
to be presented at the neighbourhood's own spelling of the source, with `h` ascribed to the type
`(SmallEtaleNeighborhood.ofChartGeometricPoint B S hS X Vch y).chart.obj.left ⟶ T`. The
hypotheses `hsq`, `hunr` and `hregular` cross unaided.

No `@[stacks]` attribute is claimed: this is a step of the proof of **Stacks 06N3**, which is no
tag of its own, and whose registration sits on
`AlgebraicGeometry.Stack.isAbsolutelyDM_iff_isDeligneMumfordStack_unconditional`.

## References

* [Stacks Project, Tag 056U](https://stacks.math.columbia.edu/tag/056U)
* [Stacks Project, Tag 06MD](https://stacks.math.columbia.edu/tag/06MD)
* [Stacks Project, Tag 06N3](https://stacks.math.columbia.edu/tag/06N3)
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The slicing datum of the chart construction of Stacks 06N3 at a prescribed point of the
fibre, with the morphism of the site under the structure morphism retained.** Let
`ξ : X ⟶ yoneda.obj T` be a smooth morphism of algebraic spaces whose target is represented by an
object of the site with underlying scheme `Spec k`, and let `x` be a point of `|X|`. Then there
are an **affine** étale chart `Vch` of `X` with a point over `x`, a morphism `h : Vch ⟶ T` of the
site with `Vch.obj.hom ≫ ξ = yoneda.map h` — so that the structure morphism of the chart over
`Spec k` is `(BigFppfOver.toScheme B S hS).map h ≫ eqToHom hT`, which is **smooth** — a point `v`
of the chart scheme which is **closed**, has **regular** local ring and has residue field finite
separable over the residue field of `Spec k`, and a geometric point of `X` — presented as a
geometric point of the presheaf represented by `Vch` — a small étale neighbourhood of which has
chart `Vch` and chart point `v`.

This is `AlgebraicGeometry.Space`
`.exists_affine_chartGeometricPoint_isClosed_isRegularLocalRing_finiteSeparable` with the
morphism of the site that its proof builds the structure morphism from kept in the
conclusion, together with the square it satisfies. Both consumers of the chart need it: the
slicing sequence of **Stacks 06MD** is read off the chart as *global sections of the structure
sheaf of the algebraic space* by
`AlgebraicGeometry.Space.exists_representedUnitSection_isRegular_etaleLocalRing_of_isAffine`,
whose square hypothesis this is, and the unramifiedness clause of **Stacks 06N2** is checked at
a chart of the fibre carrying a morphism of the site to the site object on `Spec k`. -/
@[sga "3 XXIV 8.1.2" "more general"]
theorem exists_affine_chartGeometricPoint_hom_isClosed_isRegularLocalRing_finiteSeparable
    (X : AlgebraicSpaces B S hS) {T : BigFppfOver B S hS} {k : Type u} [Field k]
    (hT : (BigFppfOver.toScheme B S hS).obj T = Spec (.of k))
    (ξ : X.1 ⟶ yoneda.obj T) (hξ : IsSmooth B S hS ξ) (x : points B S hS X.1) :
    ∃ (Vch : SmallEtale B S hS X.1) (h : Vch.obj.left ⟶ T)
      (π : chartScheme Vch ⟶ Spec (.of k)) (v : chartScheme Vch)
      (y : GeometricPoint B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj Vch))),
      IsAffine (chartScheme Vch) ∧
      Vch.obj.hom ≫ ξ = yoneda.map h ∧
      π = (BigFppfOver.toScheme B S hS).map h ≫ eqToHom hT ∧
      Smooth ((BigFppfOver.toScheme B S hS).map h) ∧
      Smooth π ∧
      (∃ v₀ : chartScheme Vch, chartSchemeToPoints B S hS X.1 Vch v₀ = x) ∧
      chartPoint B S hS X.1 (SmallEtaleNeighborhood.ofChartGeometricPoint B S hS X Vch y) = v ∧
        IsClosed ({v} : Set (chartScheme Vch)) ∧
          IsRegularLocalRing ((chartScheme Vch).presheaf.stalk v) ∧
            (letI := (π.residueFieldMap v).hom.toAlgebra;
              Module.Finite ((Spec (.of k)).residueField (π v))
                  ((chartScheme Vch).residueField v) ∧
                Algebra.IsSeparable ((Spec (.of k)).residueField (π v))
                  ((chartScheme Vch).residueField v)) := by
  obtain ⟨Vch, h, hVaff, hsq, hsm, v₀, hv₀⟩ :=
    exists_affine_smallEtale_smooth_chartScheme_at_point B S hS X.2 ξ hξ x
  have : Smooth ((BigFppfOver.toScheme B S hS).map h) := hsm
  have : Nonempty (chartScheme Vch) := ⟨v₀⟩
  obtain ⟨v, y, hy, hvclosed, hvreg, hvsep⟩ :=
    exists_chartGeometricPoint_isClosed_isRegularLocalRing_finiteSeparable B S hS X Vch
      ((BigFppfOver.toScheme B S hS).map h ≫ eqToHom hT)
  exact ⟨Vch, h, (BigFppfOver.toScheme B S hS).map h ≫ eqToHom hT, v, y, hVaff, hsq, rfl, hsm,
    inferInstance, ⟨v₀, hv₀⟩, hy, hvclosed, hvreg, hvsep⟩

end AlgebraicGeometry.Space

end
