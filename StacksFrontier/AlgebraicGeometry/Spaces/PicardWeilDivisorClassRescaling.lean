module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorCanonicalRatio
public import StacksFrontier.AlgebraicGeometry.Spaces.PicardWeilDivisorClassIntegral
public import StacksFrontier.AlgebraicGeometry.Spaces.WeilDivisorClassGroup

/-!
# Rescaling a regular meromorphic section by an invertible rational function

Let `X` be a decent, locally Noetherian, integral algebraic space over a scheme `S`, let `ℒ` be
an invertible `𝒪_X`-module and let `f` be an invertible rational function on `X`. This file
produces, at the canonical ratio `s / s_ξ` of Stacks 0EPR, a meromorphic section `t` of `ℒ`
whose ratio at the generic point of every prime divisor is `f⁻¹` times the ratio of the chosen
regular meromorphic section `s`; equivalently `s / s_ξ = f · (t / s_ξ)` at every prime divisor.
This is the hypothesis `hscale` of the conditional Stacks 0EPX,
`AlgebraicGeometry.Space.PicardDivisorData.injective_picardToWeilDivisorClassGroup`, read at the
constructed ratio.

The section is `t = f⁻¹ · s`, formed through the module structure of the global meromorphic
sections of `ℒ` over the global meromorphic functions of `X`, and the ratio identity is the
semilinearity of the canonical ratio,
`AlgebraicGeometry.Space.PrimeDivisor.canonicalGenericRatio_smul_of_eval`.

## Main results

* `AlgebraicGeometry.Space.isRegularMeromorphicSection_units_smul`: an invertible global
  meromorphic function times a regular meromorphic section is again regular.
* `AlgebraicGeometry.Space.exists_canonicalGenericRatio_eq_mul_of_units`: the ratio identity for
  the rescaled section, with the invertible meromorphic function given.
* `AlgebraicGeometry.Space.exists_isRegularMeromorphicSection_canonicalLocalRatio_eq_emb_mul`
  and `AlgebraicGeometry.Space.exists_meromorphicSection_canonicalLocalRatio_eq_emb_mul`: **the
  hypothesis `hscale` of Stacks 0EPX at the canonical ratio**, from the one assumption that an
  invertible rational function is an invertible meromorphic function compatibly with the
  embedding `R(X) → Q(𝒪^h_{X, ξ})`. The first also records that the rescaled section is
  *regular*, which the hypothesis as stated does not ask for and which the claim of Stacks
  0EPX needs: without it that claim is refutable even at the canonical ratio
  (`AlgebraicGeometry.Space.not_htriv_canonicalLocalRatioFamily`).

## Implementation notes

The global meromorphic functions are spelled `RingCat.sectionsSubring` of the ring sheaf of the
meromorphic ringed site rather than `AlgebraicGeometry.Space.MeromorphicFunction`. The two are
the same subring of the same product — the latter's `CommRing` instance *is* the former — but
only the first spelling makes instance search find the module structure
`Stacks.Cohomology.SiteModules.sectionsModule` on the meromorphic sections and give the
evaluation at a chart the type
`(Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite …).O).obj.obj (op V)` that
`AlgebraicGeometry.Space.PrimeDivisor.canonicalGenericRatio_smul_of_eval` multiplies by.

The compatibility of the embedding `R(X) → Q(𝒪^h_{X, ξ})` of Stacks 0ENK with the chartwise
pullback of meromorphic functions is *assumed here*, as the single hypothesis `hcomp` of
`AlgebraicGeometry.Space.exists_meromorphicSection_canonicalLocalRatio_eq_emb_mul`; it is the first
assertion of Stacks 0EPT and is proved, at the embedding of Stacks 0ENK, by
`AlgebraicGeometry.Space.exists_units_meromorphicFunctionEval_eq_emb` in
`StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorFunctionFieldMeromorphic`, which
discharges it. Its existence half is not at issue: the ring homomorphism `R(X) → Γ(X, 𝒦_X)` is the
`AlgebraicGeometry.Space.rationalToMeromorphicRingHom`, whose three inputs — a presentation of the
schematic locus at the codimension-zero points, codimension zero of the weakly associated points
and local finiteness of the irreducible components — all hold on such an `X`, as the proof of
`AlgebraicGeometry.Space.exists_isRegularMeromorphicSection_of_isIntegralSpace` shows. What `hcomp`
adds is that the resulting meromorphic function, pulled back to `Spec(𝒪_{U, u})` and pushed into
`Q(𝒪^h_{X, ξ})`, is the image of `f` under the embedding.

## References

* [Stacks Project, Tag 0EPR](https://stacks.math.columbia.edu/tag/0EPR)
* [Stacks Project, Tag 0EPT](https://stacks.math.columbia.edu/tag/0EPT)
* [Stacks Project, Tag 0EPX](https://stacks.math.columbia.edu/tag/0EPX)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X)

/-- Evaluation of a global meromorphic function at an étale scheme chart, as a ring
homomorphism. -/
def meromorphicFunctionEval (V : SmallEtale B S hS X) :
    ↥(RingCat.sectionsSubring
        ((Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS X hX).O).obj)) →+*
      (Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS X hX).O).obj.obj
        (op V) :=
  (Pi.evalRingHom _ (op V)).comp
    (RingCat.sectionsSubring
      ((Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS X hX).O).obj)).subtype

/-- The value of a global meromorphic function at a chart is its evaluation there. -/
theorem meromorphicFunctionEval_apply (V : SmallEtale B S hS X)
    (g : ↥(RingCat.sectionsSubring
        ((Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS X hX).O).obj))) :
    meromorphicFunctionEval B S hS hX V g = g.val (op V) :=
  rfl

/-- An invertible global meromorphic function is invertible at every étale scheme chart. -/
theorem isUnit_meromorphicFunctionEval (V : SmallEtale B S hS X)
    (g : (↥(RingCat.sectionsSubring
        ((Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS X hX).O).obj)))ˣ) :
    IsUnit (meromorphicFunctionEval B S hS hX V g) :=
  (Units.map (meromorphicFunctionEval B S hS hX V).toMonoidHom g).isUnit

variable (L : Modules.{u, u} B S hS X hX)

/-- The value over a chart of an invertible global meromorphic function times a meromorphic
section is the value of the function there times the value of the section. -/
theorem units_smul_eval
    (g : (↥(RingCat.sectionsSubring
        ((Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS X hX).O).obj)))ˣ)
    (s : MeromorphicSection.{u, u} B S hS X hX L) (V : SmallEtale B S hS X) :
    ((g : ↥(RingCat.sectionsSubring
        ((Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS X hX).O).obj))) •
          s).eval (op V) =
      meromorphicFunctionEval B S hS hX V g • s.eval (op V) :=
  rfl

/-- **An invertible meromorphic function times a regular meromorphic section is regular.**
Multiplication by the function at a chart is a bijection of the meromorphic functions there,
so it does not disturb the injectivity that regularity asks for. -/
theorem isRegularMeromorphicSection_units_smul
    (g : (↥(RingCat.sectionsSubring
        ((Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS X hX).O).obj)))ˣ)
    (s : MeromorphicSection.{u, u} B S hS X hX L)
    (hs : IsRegularMeromorphicSection.{u, u} B S hS X hX L s) :
    IsRegularMeromorphicSection.{u, u} B S hS X hX L
      ((g : ↥(RingCat.sectionsSubring
        ((Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS X hX).O).obj))) •
          s) := by
  intro V r r' hr
  obtain ⟨v, hv⟩ := isUnit_meromorphicFunctionEval B S hS hX V g
  have hr' : (r * v) • s.eval (op V) = (r' * v) • s.eval (op V) := by
    rw [hv]
    simpa only [units_smul_eval B S hS hX L g s V, smul_smul] using hr
  exact (Units.mul_left_inj v).1 (hs V hr')

variable (hInt : IsIntegralSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))
    (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)

include hInt hN in
/-- **The canonical ratio of a rescaled regular meromorphic section.** For an invertible global
meromorphic function `g` and a regular meromorphic section `s` of `ℒ`, the section `t = g⁻¹ · s`
is regular and `s / s_ξ` is the image of `g` over `Spec(𝒪_{U, u})` times `t / s_ξ`, at the
generic point of every prime divisor. -/
theorem exists_canonicalGenericRatio_eq_mul_of_units
    (g : (↥(RingCat.sectionsSubring
        ((Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS X hX).O).obj)))ˣ)
    (s : MeromorphicSection.{u, u} B S hS X hX L)
    (hs : IsRegularMeromorphicSection.{u, u} B S hS X hX L s) :
    ∃ t : MeromorphicSection.{u, u} B S hS X hX L,
      IsRegularMeromorphicSection.{u, u} B S hS X hX L t ∧
        ∀ W : PrimeDivisor B S hS X,
          W.canonicalGenericRatio B S hS hX hdec L hL hInt hN s =
            W.genericStalkMeromorphicToGeneric B S hS hX hdec hInt hN
                (chartMeromorphicRingedSitePullbackHom B S hS
                  (W.genericStalkMorphism B S hS hX hdec)
                  (W.pullbacksMeromorphicSections_genericStalkMorphism B S hS hX hdec)
                  (W.genericStalkChartDiagram B S hS hX hdec)
                  (meromorphicFunctionEval B S hS hX
                    (W.genericEtaleChart B S hS hX hdec) g)) *
              W.canonicalGenericRatio B S hS hX hdec L hL hInt hN t := by
  refine ⟨((g⁻¹ : (↥(RingCat.sectionsSubring
      ((Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS X hX).O).obj)))ˣ) :
        ↥(RingCat.sectionsSubring
          ((Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS X hX).O).obj))) •
          s,
    isRegularMeromorphicSection_units_smul B S hS hX L g⁻¹ s hs, fun W => ?_⟩
  refine W.canonicalGenericRatio_smul_of_eval B S hS hX hdec L hL hInt hN s _ _ ?_
  rw [units_smul_eval B S hS hX L g⁻¹ s (W.genericEtaleChart B S hS hX hdec), smul_smul,
    ← map_mul, Units.mul_inv, map_one, one_smul]

variable (E : GenericFractionEmbedding B S hS hX hdec)

include hInt hN in
/-- **The hypothesis `hscale` of Stacks 0EPX at the canonical ratio.** Every invertible rational
function `f` rescales the chosen regular meromorphic section of an invertible `𝒪_X`-module: there
is a meromorphic section `t` with `s / s_ξ = f · (t / s_ξ)` at the generic point of every prime
divisor.

The one assumption is that `f` is an invertible global meromorphic function whose image in
`Q(𝒪^h_{X, ξ})` is `f`'s image under the embedding of Stacks 0ENK, which is the first assertion
of Stacks 0EPT. -/
theorem exists_isRegularMeromorphicSection_canonicalLocalRatio_eq_emb_mul
    (hcomp : ∀ f : (rationalFunctions B S hS hX)ˣ,
      ∃ g : (↥(RingCat.sectionsSubring
          ((Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS X hX).O).obj)))ˣ,
        ∀ W : PrimeDivisor B S hS X,
          W.genericStalkMeromorphicToGeneric B S hS hX hdec hInt hN
              (chartMeromorphicRingedSitePullbackHom B S hS
                (W.genericStalkMorphism B S hS hX hdec)
                (W.pullbacksMeromorphicSections_genericStalkMorphism B S hS hX hdec)
                (W.genericStalkChartDiagram B S hS hX hdec)
                (meromorphicFunctionEval B S hS hX
                  (W.genericEtaleChart B S hS hX hdec) g)) =
            E.emb W (f : rationalFunctions B S hS hX))
    (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
    (f : (rationalFunctions B S hS hX)ˣ) :
    ∃ t : MeromorphicSection.{u, u} B S hS X hX L,
      IsRegularMeromorphicSection.{u, u} B S hS X hX L t ∧
        ∀ W : PrimeDivisor B S hS X,
          (canonicalLocalRatioFamily B S hS hX hdec L hL hInt hN W
              (regularMeromorphicSection B S hS hX hInt hN L hL) :
            W.genericTotalFractionRing B S hS hX hdec) =
            E.emb W (f : rationalFunctions B S hS hX) *
              (canonicalLocalRatioFamily B S hS hX hdec L hL hInt hN W t :
                W.genericTotalFractionRing B S hS hX hdec) := by
  obtain ⟨g, hg⟩ := hcomp f
  obtain ⟨t, ht, hratio⟩ := exists_canonicalGenericRatio_eq_mul_of_units B S hS hX hdec L hInt hN
    hL g (regularMeromorphicSection B S hS hX hInt hN L hL)
    (isRegularMeromorphicSection_regularMeromorphicSection B S hS hX hInt hN L hL)
  refine ⟨t, ht, fun W => ?_⟩
  have hc : ∀ s, IsRegularMeromorphicSection.{u, u} B S hS X hX L s →
      (canonicalLocalRatioFamily B S hS hX hdec L hL hInt hN W s :
        W.genericTotalFractionRing B S hS hX hdec) =
      W.canonicalGenericRatio B S hS hX hdec L hL hInt hN s :=
    W.coe_canonicalLocalRatio B S hS hX hdec L hL hInt hN
  rw [hc _ (isRegularMeromorphicSection_regularMeromorphicSection B S hS hX hInt hN L hL),
    hc t ht, hratio W, hg W]

include hInt hN in
/-- **The hypothesis `hscale` of Stacks 0EPX at the canonical ratio**, with the regularity of
the rescaled section forgotten. This is the hypothesis as
`AlgebraicGeometry.Space.PicardDivisorData.injective_picardToWeilDivisorClassGroup` states
it. -/
theorem exists_meromorphicSection_canonicalLocalRatio_eq_emb_mul
    (hcomp : ∀ f : (rationalFunctions B S hS hX)ˣ,
      ∃ g : (↥(RingCat.sectionsSubring
          ((Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS X hX).O).obj)))ˣ,
        ∀ W : PrimeDivisor B S hS X,
          W.genericStalkMeromorphicToGeneric B S hS hX hdec hInt hN
              (chartMeromorphicRingedSitePullbackHom B S hS
                (W.genericStalkMorphism B S hS hX hdec)
                (W.pullbacksMeromorphicSections_genericStalkMorphism B S hS hX hdec)
                (W.genericStalkChartDiagram B S hS hX hdec)
                (meromorphicFunctionEval B S hS hX
                  (W.genericEtaleChart B S hS hX hdec) g)) =
            E.emb W (f : rationalFunctions B S hS hX))
    (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
    (f : (rationalFunctions B S hS hX)ˣ) :
    ∃ t : MeromorphicSection.{u, u} B S hS X hX L, ∀ W : PrimeDivisor B S hS X,
      (canonicalLocalRatioFamily B S hS hX hdec L hL hInt hN W
          (regularMeromorphicSection B S hS hX hInt hN L hL) :
        W.genericTotalFractionRing B S hS hX hdec) =
        E.emb W (f : rationalFunctions B S hS hX) *
          (canonicalLocalRatioFamily B S hS hX hdec L hL hInt hN W t :
            W.genericTotalFractionRing B S hS hX hdec) :=
  let ⟨t, _, h⟩ := exists_isRegularMeromorphicSection_canonicalLocalRatio_eq_emb_mul B S hS hX
    hdec hInt hN E hcomp L hL f
  ⟨t, h⟩

end AlgebraicGeometry.Space

end
