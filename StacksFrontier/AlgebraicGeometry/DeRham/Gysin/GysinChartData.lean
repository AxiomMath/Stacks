module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinChartLift
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinTargetExcision
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.LocalCohomologyExcision
public import StacksFrontier.AlgebraicGeometry.ConormalEquations.RankGenerators
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinDifferentialSquare
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.WedgeDeterminant

/-!
# The equation charts and the target of the Gysin map of Tag 0G86

This file supplies, for a closed immersion `i : Z ⟶ X` of finite presentation whose conormal
sheaf is locally free of rank `c`, the parts of `Stacks.Gysin.GysinChartData` that do not
mention the local Gysin maps: the target sheaf and the equation charts.

* `Stacks.Gysin.gysinTarget` is the sheaf `i_*ℋ^c_Z(Ω^{p+c}_{X/S})`, read on the ambient scheme,
  in the spelling `Stacks.Perfect.SupportedFraction.supportCohomologySheafFunctor`: the degree-`c`
  cohomology sheaf of `i_* R𝓗_Z(ℱ[0])`. This is the spelling in which [Stacks, Tag 0G7Q] and
  [Stacks, Tag 0G7S] are stated, and the one for which the **derived** excision of
  [Stacks, Tag 0G78] is available, as `Stacks.Gysin.supportCohomologyRestrictIso`; so the chart
  transports below are that excision, and no comparison of two independently constructed
  isomorphisms occurs. That this sheaf is the direct image of the local cohomology sheaf of
  [Stacks, Tag 0G6N] is
  `Stacks.Perfect.GysinAbelianSquare.supportCohomologySheafFunctorLocalCohomologyIso`, and that it
  is the right derived functor
  `Stacks.Perfect.LocalCohomologyExcision.localCohomologyOn` of the subsheaf of sections supported
  on `Z` is `Stacks.Gysin.supportCohomologyOnIso`, so this is the sheaf the source names, and the
  two spellings are right derived functors of one degree-zero functor. Crucially it depends only
  on the closed subset and not on any choice of equations, which is what lets one sheaf receive
  the Gysin maps of every chart.
* `Stacks.Gysin.exists_gysinCharts` packages
  `Stacks.AlgebraicGeometry.ConormalEquations.exists_equationCharts_of_conormalRank` in exactly
  the shape the fields `ambient`, `equations`, `equations_vanish` and `ambient_cover` of
  `Stacks.Gysin.GysinChartData` take, with the chart index type `Chart := ↥X`, and carries along
  the two further clauses a construction of the local Gysin maps needs: the charts are affine,
  and on a chart the ideal of `Z` is the span of the `c` equations.

The affineness clause is what makes `Stacks.Gysin.ChartComparison.lift` free, by
`Stacks.Gysin.exists_subschemeFormPullback_of_isAffineOpen`.

## Implementation notes

**The hypothesis `c ≠ 0`.** It is inherited from
`Stacks.AlgebraicGeometry.ConormalEquations.exists_equationCharts_of_conormalRank` and is needed
only to cover the points *outside* `Z`, where the ideal sheaf is the unit ideal and the chart
equations are taken to be `1, …, 1`: the empty family generates the zero ideal, not the unit
ideal. It is not a restriction on the geometry of `Z` in `X`, and it is not needed for the charts
around the points of `Z`, for which
`Stacks.AlgebraicGeometry.ConormalEquations.exists_affineOpen_equations_of_conormalRank` has no
condition on `c`.

## References

* [Stacks Project, Tag 0G86](https://stacks.math.columbia.edu/tag/0G86)
* [Stacks Project, Tag 0G6N](https://stacks.math.columbia.edu/tag/0G6N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.Scheme.Hom
open Stacks.Perfect.LocalCohomologyExcision
open Stacks.AlgebraicGeometry.ConormalEquations
open Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u

namespace Stacks.Gysin

variable {Z X S : Scheme.{u}}

/-! ### The target sheaf -/

/-- The image of a closed immersion is closed. -/
theorem isClosed_range_base (i : Z ⟶ X) [IsClosedImmersion i] : IsClosed (Set.range i.base) :=
  i.isClosedEmbedding.isClosed_range

/-- The part of the image of a closed immersion lying over an open subscheme is closed in that
open subscheme. This is the closedness hypothesis the chart constructions carry, so a chart need
not be given it. -/
theorem isClosed_preimage_range_base (i : Z ⟶ X) [IsClosedImmersion i] (W : X.Opens) :
    IsClosed (W.ι ⁻¹' Set.range i.base) :=
  (isClosed_range_base i).preimage W.ι.base.hom.continuous

/-- **The target `i_*ℋ^c_Z(Ω^{p+c}_{X/S})` of the Gysin map of [Stacks, Tag 0G86].** The local
cohomology of the relative differential forms with supports in the closed subset underlying the
closed immersion `i`, pushed forward to the ambient scheme, in the spelling
`Stacks.Perfect.SupportedFraction.supportCohomologySheafFunctor` — the degree-`c` cohomology
sheaf of `i_* R𝓗_Z(ℱ[0])` — which is the spelling of [Stacks, Tag 0G7Q] and [Stacks, Tag 0G7S]
and the one for which the **derived** excision of [Stacks, Tag 0G78] is available, as
`Stacks.Gysin.supportCohomologyRestrictIso`.

That it is the direct image of the local cohomology sheaf of [Stacks, Tag 0G6N] is
`Stacks.Perfect.GysinAbelianSquare.supportCohomologySheafFunctorLocalCohomologyIso`, and that it
is the right derived functor
`Stacks.Perfect.LocalCohomologyExcision.localCohomologyOn` of the subsheaf of sections supported
on `Z` is `Stacks.Gysin.supportCohomologyOnIso`; the two functors are right derived functors of
the same degree-zero functor, so nothing is lost by taking this spelling rather than that one,
and what is gained is that the chart transports are the derived excision and need no coherence
between two independently constructed isomorphisms.

It depends on `i` only through the closed subset `Set.range i.base`, and in particular on no
choice of local equations: that is what allows the Gysin maps of all the equation charts to land
in one and the same sheaf, which is the whole point of the globalisation. -/
def gysinTarget (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) (c p : ℕ) : X.Modules :=
  (Stacks.Perfect.SupportedFraction.supportCohomologySheafFunctor
      (isClosed_range_base i) (c : ℤ)).obj
    (relativeDifferentialForms π ((p : ℤ) + (c : ℤ)))

/-! ### The equation charts -/

/-- **The equation charts of [Stacks, Tag 0G86], in the shape `Stacks.Gysin.GysinChartData`
consumes.** For a closed immersion of finite presentation whose conormal sheaf is locally free of
rank `c ≠ 0`, the scheme `X` is covered by affine opens on each of which `Z` is cut out by
exactly `c` equations.

The chart index type is `↥X` itself, the chart of a point being an affine neighbourhood of it.
The second and third clauses are literally the fields
`Stacks.Gysin.GysinChartData.equations_vanish` and `Stacks.Gysin.GysinChartData.ambient_cover`;
the fourth says the charts are affine, which is what
`Stacks.Gysin.exists_subschemeFormPullback_of_isAffineOpen` needs; and the last two say that on a
chart the ideal of `Z` is generated by the equations — over every open of the chart, which is what
`cls_vanish` needs, and as a span of sections over the chart itself, which is the hypothesis of the
local Gysin map of [Stacks, Tag 0G83]. -/
theorem exists_gysinCharts (i : Z ⟶ X) [IsClosedImmersion i] [LocallyOfFinitePresentation i]
    (c : ℕ) (hE : ConormalRank i c) (hc : c ≠ 0) :
    ∃ (ambient : X → X.Opens) (equations : (a : X) → Fin c → Γ(X, ambient a)),
      (∀ (a : X) (V : X.Opens) (hV : V ≤ ambient a) (j : Fin c),
          (i.app V).hom (X.presheaf.map (homOfLE hV).op (equations a j)) = 0) ∧
        (∀ x : X, ∃ a, x ∈ ambient a) ∧
        (∀ a, IsAffineOpen (ambient a)) ∧
        (∀ a, IsGeneratedByOn X.toRingedSpace (definingIdealOfHom i) (ambient a) (equations a)) ∧
        ∀ a, RingHom.ker (i.app (ambient a)).hom = Ideal.span (Set.range (equations a)) := by
  obtain ⟨ambient, equations, haff, hmem, hvanish, hgen, hspan⟩ :=
    exists_equationCharts_of_conormalRank i c hE hc
  exact ⟨ambient, equations, hvanish, fun x => ⟨x, hmem x⟩, haff, hgen, hspan⟩

/-! ### The class map of 0G7Q lands in the target -/

section Bridge

attribute [local instance 10000] HasDerivedCategory.standard

open Stacks.Perfect.SupportedFraction Stacks.Perfect.GysinAbelianSquare
open Stacks.Perfect.CechDerivedSupport
open Stacks.Cohomology.SupportedComplexes

/-- **The target of the class map of [Stacks, Tag 0G7Q] is the target of the Gysin map.** The
sheaf `i_*ℋ ⁿ_T(ℱ)` in the derived-category spelling `supportCohomologySheafFunctor`, in which
[Stacks, Tag 0G7Q] and [Stacks, Tag 0G7S] are stated, is the right derived functor
`Stacks.Perfect.LocalCohomologyExcision.localCohomologyOn`, in which excision is available.

Composing `Stacks.Perfect.GysinAbelianSquare.supportCohomologySheafFunctorLocalCohomologyIso`,
which identifies the derived-category cohomology sheaf with the classical right derived functor
of the sections supported on the closed subset of `T`, with
`Stacks.Perfect.LocalCohomologyExcision.localCohomologyOnIso`, which identifies the direct image
of that with the right derived functor of the sections supported on `T` taken on `X`. -/
def supportCohomologyOnIso (X : Scheme.{u}) (T : Set X) (hT : IsClosed T) (n : ℕ) :
    supportCohomologySheafFunctor hT (n : ℤ) ≅ localCohomologyOn X T n :=
  letI := pushforward_preservesFiniteLimits X.toRingedSpace T
  letI := pushforward_preservesFiniteColimits X.toRingedSpace T hT
  supportCohomologySheafFunctorLocalCohomologyIso hT n ≪≫ localCohomologyOnIso X T hT n

/-- **The class map `c_{f₁, …, f_c}` of a chart, transported to the ambient scheme.** On the
chart `W` the equations are global sections of `𝒪_W`, so [Stacks, Tag 0G7Q] applies verbatim and
gives `Ω^{p+c}_{X/S}|_W ⟶ i_*ℋ^c_{W ∩ Z}(Ω^{p+c}_{X/S}|_W)`; the **derived** excision of
[Stacks, Tag 0G78], read on degree-`c` cohomology sheaves as
`Stacks.Gysin.supportCohomologyRestrictIso`, carries that back to the restriction to `W` of the
global target `Stacks.Gysin.gysinTarget`.

One transport, not two: both sides of the excision are the cohomology-sheaf spelling
`Stacks.Perfect.SupportedFraction.supportCohomologySheafFunctor` in which [Stacks, Tag 0G7Q] is
stated, so no comparison with a second construction of the local cohomology sheaf occurs here.

Being a morphism of sheaves of modules on `W`, it is automatically additive, `𝒪`-linear and
compatible with restriction to smaller opens, which is what the fields `cls_vanish` and
`loc_res` of `Stacks.Gysin.GysinChartData` ask of the class map. -/
def chartClsHom (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {d : ℕ} (p : ℕ) (W : X.Opens)
    (f : Fin (d + 1) → Γ(W.toScheme, ⊤))
    (hT : IsClosed (W.ι ⁻¹' Set.range i.base))
    (hTf : equationsClosedSet f ⊆ W.ι ⁻¹' Set.range i.base) :
    (Scheme.Modules.restrictFunctor W.ι).obj
        (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ))) ⟶
      (Scheme.Modules.restrictFunctor W.ι).obj (gysinTarget i π (d + 1) p) :=
  haveI : (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ))).IsQuasicoherent :=
    isQuasicoherent_relativeDifferentialForms_natCast_add π p (d + 1)
  supportedFractionSource f
      ((Scheme.Modules.restrictFunctor W.ι).obj
        (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ)))) hT hTf ≫
    (supportCohomologyRestrictIso W (isClosed_range_base i) hT ((d + 1 : ℕ) : ℤ)
      (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ)))).inv

/-- **The `cls` field of `Stacks.Gysin.GysinChartData`**: the class map of a chart on the sections
over an open `V` of the ambient scheme contained in the chart.

This is `chartClsHom` read over `chartOpen W hV`, whose sections are *by definition* the sections
over `W.ι ''ᵁ chartOpen W hV` — that is `restrict_sections_eq` — and that open is `V` again, by
`ι_image_chartOpen`. The identification of the two opens is applied as the pair of mutually
inverse restriction maps along it rather than as a transport of the section types: `chartOpen W hV`
mentions `V`, so a transport cannot be eliminated by substitution, whereas restriction maps
compose and commute with the module structure, which is what the laws below need. -/
def chartCls (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {d : ℕ} (p : ℕ) (W : X.Opens)
    (f : Fin (d + 1) → Γ(W.toScheme, ⊤))
    (hT : IsClosed (W.ι ⁻¹' Set.range i.base))
    (hTf : equationsClosedSet f ⊆ W.ι ⁻¹' Set.range i.base)
    (V : X.Opens) (hV : V ≤ W) :
    Γ(relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ)), V) →+
      Γ(gysinTarget i π (d + 1) p, V) :=
  (((gysinTarget i π (d + 1) p).presheaf.map
        (homOfLE (ι_image_chartOpen W hV).ge).op).hom).comp
    ((((chartClsHom i π p W f hT hTf).val.app
          (op (chartOpen W hV))).hom.toAddMonoidHom).comp
      (((relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ))).presheaf.map
        (homOfLE (ι_image_chartOpen W hV).le).op).hom))

/-- **The `wedge_det` field of `Stacks.Gysin.ChartComparison`.** The equation wedges of two
families related by a matrix differ by the determinant of the matrix, modulo the equations. This
is `AlgebraicGeometry.Scheme.Hom.wedge_det_self`, phrased through `Stacks.Gysin.gysinWedgeOn`. -/
theorem chartWedgeDet (π : X ⟶ S) (V : X.Opens) {c p : ℕ}
    (N : Matrix (Fin c) (Fin c) Γ(X, V)) (f g : Fin c → Γ(X, V))
    (hg : ∀ j, g j = ∑ l, N j l * f l)
    (ω : Γ(relativeDifferentialForms π (p : ℤ), V)) :
    ∃ η : Fin c → Γ(relativeDifferentialForms π ((p : ℤ) + (c : ℤ)), V),
      gysinWedgeOn π g (p : ℤ) (le_refl V) ω =
        N.det • gysinWedgeOn π f (p : ℤ) (le_refl V) ω + ∑ l, f l • η l :=
  AlgebraicGeometry.Scheme.Hom.wedge_det_self π V (p : ℤ) N f g hg ω

/-- **The determinant rule of [Stacks, Tag 0G7S] over an arbitrary closed subset.** The library's
`Stacks.Perfect.SupportedFraction.supportedFractionSource_eq_det_smul` fixes the supporting closed
subset to be the common zero locus of the first family; what a chart needs is the same identity
with the supporting subset given in advance, namely the part of the closed subscheme lying over
the chart. Since the subset is then a variable constrained by an equation, substituting it
reduces one statement to the other. -/
theorem supportedFractionSource_eq_det_smul_of_eq {Y : Scheme.{u}} {d : ℕ}
    (f g : Fin (d + 1) → Γ(Y, ⊤)) (A : Matrix (Fin (d + 1)) (Fin (d + 1)) Γ(Y, ⊤))
    (F : Y.Modules) [F.IsQuasicoherent] (hg : ∀ j, g j = ∑ l, A j l * f l)
    {T : Set Y} (hT : IsClosed T) (hfT : equationsClosedSet f = T)
    (hgT : equationsClosedSet g = T) :
    supportedFractionSource f F hT hfT.le =
      globalSmul A.det F ≫ supportedFractionSource g F hT hgT.le := by
  subst hfT
  exact supportedFractionSource_eq_det_smul f g A F hg hgT

/-- **The determinant rule of [Stacks, Tag 0G7S] for the chart class map**: changing the chart's
equations by a matrix multiplies the class map by the determinant of the matrix. This is the
content of the field `Stacks.Gysin.ChartComparison.cls_det`.

The proof is that the transport `chartClsHom` composes the class map with — the derived excision
`Stacks.Gysin.supportCohomologyRestrictIso` — does not mention the equations at all, so the
identity of `supportedFractionSource_eq_det_smul_of_eq` survives composition with it
unchanged. -/
theorem chartClsHom_det (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {d : ℕ} (p : ℕ)
    (W : X.Opens)
    (f g : Fin (d + 1) → Γ(W.toScheme, ⊤))
    (A : Matrix (Fin (d + 1)) (Fin (d + 1)) Γ(W.toScheme, ⊤))
    (hg : ∀ j, g j = ∑ l, A j l * f l)
    (hT : IsClosed (W.ι ⁻¹' Set.range i.base))
    (hfT : equationsClosedSet f = W.ι ⁻¹' Set.range i.base)
    (hgT : equationsClosedSet g = W.ι ⁻¹' Set.range i.base) :
    chartClsHom i π p W f hT hfT.le =
      globalSmul A.det ((Scheme.Modules.restrictFunctor W.ι).obj
          (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ)))) ≫
        chartClsHom i π p W g hT hgT.le :=
  have : (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ))).IsQuasicoherent :=
    isQuasicoherent_relativeDifferentialForms_natCast_add π p (d + 1)
  Eq.trans
    (congrArg
      (fun ψ => ψ ≫
        (supportCohomologyRestrictIso W (isClosed_range_base i) hT ((d + 1 : ℕ) : ℤ)
          (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ)))).inv)
      (supportedFractionSource_eq_det_smul_of_eq f g A
        ((Scheme.Modules.restrictFunctor W.ι).obj
          (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ)))) hg hT hfT hgT))
    (Category.assoc _ _ _)

/-- The determinant rule of [Stacks, Tag 0G7S] for the chart class map, **on sections** over an
open of the chart. This is `chartClsHom_det` evaluated, with the scalar computed by
`Stacks.Perfect.SupportedFraction.globalSmul_app`: the determinant acts by its restriction to the
open. Stated over an open of the chart rather than over the corresponding open of `X`, so that no
transport of the sections is involved. -/
theorem chartClsHom_app_det (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {d : ℕ} (p : ℕ)
    (W : X.Opens)
    (f g : Fin (d + 1) → Γ(W.toScheme, ⊤))
    (A : Matrix (Fin (d + 1)) (Fin (d + 1)) Γ(W.toScheme, ⊤))
    (hg : ∀ j, g j = ∑ l, A j l * f l)
    (hT : IsClosed (W.ι ⁻¹' Set.range i.base))
    (hfT : equationsClosedSet f = W.ι ⁻¹' Set.range i.base)
    (hgT : equationsClosedSet g = W.ι ⁻¹' Set.range i.base)
    (V' : W.toScheme.Opens)
    (y : Γ((Scheme.Modules.restrictFunctor W.ι).obj
      (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ))), V')) :
    (chartClsHom i π p W f hT hfT.le).app V' y =
      (chartClsHom i π p W g hT hgT.le).app V'
        (W.toScheme.presheaf.map (homOfLE (show V' ≤ ⊤ from le_top)).op A.det • y) :=
  congrArg (fun φ => Scheme.Modules.Hom.app φ V' y)
    (chartClsHom_det i π p W f g A hg hT hfT hgT)

/-- Restriction of a section of the structure sheaf along two *equal* opens, composed both ways,
is the identity. -/
private theorem presheaf_map_ge_le (M : X.Modules) {A B : X.Opens} (h : A = B) (z : Γ(M, A)) :
    M.presheaf.map (homOfLE h.le).op (M.presheaf.map (homOfLE h.ge).op z) = z := by
  rw [← ConcreteCategory.comp_apply, ← M.presheaf.map_comp, ← op_comp,
    show (homOfLE h.le ≫ homOfLE h.ge : A ⟶ A) = 𝟙 A from Subsingleton.elim _ _]
  simp

/-- The determinant of a chart's change-of-equations matrix, read as a function on the open `V`
of the ambient scheme: restrict it from the chart to `chartOpen W hV`, whose sections are those
of `𝒪_X` over `W.ι ''ᵁ chartOpen W hV`, and carry it along to `V`. -/
def chartScalar (W : X.Opens) {V : X.Opens} (hV : V ≤ W) (r : Γ(W.toScheme, ⊤)) : Γ(X, V) :=
  X.presheaf.map (homOfLE (ι_image_chartOpen W hV).ge).op
    (W.toScheme.presheaf.map (homOfLE (show chartOpen W hV ≤ ⊤ from le_top)).op r)

/-- Restricting a section `chartScalar W hV r • y` to the chart opens `chartOpen W hV` multiplies
the restriction of `y` by the restriction of `r`. -/
private theorem restrict_chartScalar_smul (M : X.Modules) (W : X.Opens) {V : X.Opens}
    (hV : V ≤ W) (r : Γ(W.toScheme, ⊤)) (y : Γ(M, V)) :
    M.presheaf.map (homOfLE (ι_image_chartOpen W hV).le).op (chartScalar W hV r • y) =
      W.toScheme.presheaf.map (homOfLE (show chartOpen W hV ≤ ⊤ from le_top)).op r •
        (show Γ((Scheme.Modules.restrictFunctor W.ι).obj M, chartOpen W hV) from
          M.presheaf.map (homOfLE (ι_image_chartOpen W hV).le).op y) := by
  refine Eq.trans (Scheme.Modules.map_smul _ _ _ _) ?_
  congr 1
  simp only [chartScalar, Scheme.Opens.ι_appIso]
  exact presheaf_map_ge_le (SheafOfModules.unit X.ringCatSheaf) (ι_image_chartOpen W hV) _

/-- **The `cls_det` field of `Stacks.Gysin.ChartComparison`**: changing a chart's equations by a
matrix multiplies the class map by the determinant, on the sections over an open `V` of the
ambient scheme contained in the chart.

This is `chartClsHom_app_det` conjugated by the two restriction maps of `chartCls`. The only
bookkeeping is that the determinant must be read on `V`, which is `chartScalar`: restricting it
back along the identification of the opens returns the determinant on the chart, by
`presheaf_map_ge_le`, and restriction is semilinear, so the scalar passes through. -/
theorem chartCls_det (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {d : ℕ} (p : ℕ)
    (W : X.Opens)
    (f g : Fin (d + 1) → Γ(W.toScheme, ⊤))
    (A : Matrix (Fin (d + 1)) (Fin (d + 1)) Γ(W.toScheme, ⊤))
    (hg : ∀ j, g j = ∑ l, A j l * f l)
    (hT : IsClosed (W.ι ⁻¹' Set.range i.base))
    (hfT : equationsClosedSet f = W.ι ⁻¹' Set.range i.base)
    (hgT : equationsClosedSet g = W.ι ⁻¹' Set.range i.base)
    (V : X.Opens) (hV : V ≤ W)
    (y : Γ(relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ)), V)) :
    chartCls i π p W f hT hfT.le V hV y =
      chartCls i π p W g hT hgT.le V hV (chartScalar W hV A.det • y) := by
  show (gysinTarget i π (d + 1) p).presheaf.map _ _ = (gysinTarget i π (d + 1) p).presheaf.map _ _
  refine congrArg ((gysinTarget i π (d + 1) p).presheaf.map
    (homOfLE (ι_image_chartOpen W hV).ge).op) ?_
  refine Eq.trans (chartClsHom_app_det i π p W f g A hg hT hfT hgT (chartOpen W hV) _) ?_
  exact congrArg ((chartClsHom i π p W g hT hgT.le).app (chartOpen W hV))
    (restrict_chartScalar_smul _ W hV _ y).symm

/-- **The chart class map of a multiple by a function lifted from the chart**, read through the
two restriction maps of `chartCls`: the scalar comes back to the chart, where the class map is
a morphism of sheaves of modules and so `𝒪_W`-homogeneous. This is the half of `chartCls_det`
that does not mention the determinant, isolated so that the vanishing statements can use it. -/
theorem chartCls_chartScalar_smul (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {d : ℕ} (p : ℕ)
    (W : X.Opens)
    (f : Fin (d + 1) → Γ(W.toScheme, ⊤))
    (hT : IsClosed (W.ι ⁻¹' Set.range i.base))
    (hTf : equationsClosedSet f ⊆ W.ι ⁻¹' Set.range i.base)
    (V : X.Opens) (hV : V ≤ W) (r : Γ(W.toScheme, ⊤))
    (y : Γ(relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ)), V)) :
    chartCls i π p W f hT hTf V hV (chartScalar W hV r • y) =
      (gysinTarget i π (d + 1) p).presheaf.map (homOfLE (ι_image_chartOpen W hV).ge).op
        ((chartClsHom i π p W f hT hTf).app (chartOpen W hV)
          (W.toScheme.presheaf.map (homOfLE (show chartOpen W hV ≤ ⊤ from le_top)).op r •
            (show Γ((Scheme.Modules.restrictFunctor W.ι).obj
                (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ))), chartOpen W hV) from
              (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ))).presheaf.map
                (homOfLE (ι_image_chartOpen W hV).le).op y))) := by
  show (gysinTarget i π (d + 1) p).presheaf.map _ _ = _
  refine congrArg ((gysinTarget i π (d + 1) p).presheaf.map
    (homOfLE (ι_image_chartOpen W hV).ge).op) ?_
  exact congrArg ((chartClsHom i π p W f hT hTf).app (chartOpen W hV))
    (restrict_chartScalar_smul _ W hV r y)

end Bridge

end Stacks.Gysin

end
