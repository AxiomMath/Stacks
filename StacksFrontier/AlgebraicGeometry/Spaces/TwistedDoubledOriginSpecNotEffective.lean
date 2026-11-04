module

public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedDoubledOriginNotScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedDoubledOriginSpecCocycle

/-!
# The closing claim of Stacks 03FN: a descent datum which is not effective

The example closes with the sentence that it *gives an example of a descent datum for schemes
relative to the covering `{Spec k' ⟶ Spec k}` which is not effective*.  The datum is the one on
the affine line over `k'` with the origin doubled — the scheme `X_{k'}` of part (6) — whose
gluing isomorphism is the Galois twist exchanging the two sheets.

Concretely, write `U = Spec k'[x]` for the chart and `V` for the doubled line, with its two
sheets `ι₀, ι₁ : U ⟶ V` and its projection `V ⟶ U`.  The Galois automorphism `a` of `U`
assembles with the exchange of sheets into an automorphism `τ` of `V` with
`ι_b ≫ τ = a ≫ ι_{¬b}`, which is an involution and is semilinear over the Galois automorphism
of `Spec k'`.  Since the self-product of the covering splits as `Spec k' ⨿ Spec k'`, that is
exactly a descent datum relative to the covering
(`AlgebraicGeometry.exists_descentDatum_not_isEffective_of_semilinear`).

It is not effective.  If it were, there would be a scheme `W₀` over `Spec k` and an isomorphism
`Spec k' ×_{Spec k} W₀ ≅ V` over `Spec k'` whose projection `b : V ⟶ W₀` is `τ`-invariant.  Then
`c_b := ι_b ≫ b` satisfy `c₀ = a ≫ c₁`, because `τ` carries one sheet to the other twisted by
`a`, and they agree on the puncture, because the two sheets of `V` do.  The puncture is dense in
the chart and the chart is reduced, so `c₀` and `c₁` already agree at the origin: the first
identity makes them agree there *as points*, since `Spec k'` has only one point and `a` fixes the
origin, and the second then upgrades that to an equality of morphisms out of the origin.  But `b`
separates the two origins of `V`, because the two sheets meet only over the puncture, so this is
a contradiction.

## Main definitions

* `AlgebraicGeometry.TwistedDoubledOrigin.doubledLineToSpec`: the structure morphism over
  `Spec k'` of the affine line over `k'` with the origin doubled.
* `AlgebraicGeometry.TwistedDoubledOrigin.doubledLineTwist`: the Galois twist `τ` of the doubled
  line, obtained by gluing the Galois automorphism of the chart followed by the *other* sheet.
* `AlgebraicGeometry.TwistedDoubledOrigin.specOrigin`: the `k'`-rational origin of the chart.

## Main results

* `AlgebraicGeometry.TwistedDoubledOrigin.doubledLineTwist_involutive` and
  `AlgebraicGeometry.TwistedDoubledOrigin.doubledLineTwist_semilinear`: `τ` is a semilinear
  involution, which is what makes it a descent datum.
* `AlgebraicGeometry.TwistedDoubledOrigin.specOrigin_chart_ne`: **the doubled line has two
  distinct origins.**
* `AlgebraicGeometry.TwistedDoubledOrigin.exists_descentDatum_specExtension_not_isEffective`:
  **the closing claim of Stacks 03FN.**

## Implementation notes

The twist is built with `AlgebraicGeometry.Scheme.Cover.glueMorphisms` on the cover of the
doubled line by its two sheets.  The compatibility condition is where the geometry enters: on the
diagonal overlaps the two projections of the fibre square agree because a sheet is a split
monomorphism, and on the off-diagonal ones the fibre square is the puncture
(`Stacks.Examples.doubleSectionCover_isPullback_chart`), where the two sheets agree
(`Stacks.Examples.doubleSectionCover_chart_agree`) — after transporting along the Galois
automorphism, which preserves the puncture
(`AlgebraicGeometry.TwistedDoubledOrigin.galoisActionPuncturedMap_ι`).

That the two origins are distinct is read off the same fibre square: a morphism equalising the two
sheets factors through the puncture, and the origin does not, because the coordinate pulls back
to `0` along it.

The contradiction is assembled from the *projection* form of effectivity,
`AlgebraicGeometry.DescentData.exists_descent_proj_of_isEffective`: the ordinary form
`AlgebraicGeometry.DescentData.exists_descent_of_isEffective` takes the invariant morphism out of
the datum as input, which is circular here, since the morphism the argument needs is the
projection to the scheme effectivity would produce.

## References

* [Stacks Project, Tag 03FN](https://stacks.math.columbia.edu/tag/03FN)
* [Stacks Project, Tag 023V](https://stacks.math.columbia.edu/tag/023V)
* [Stacks Project, Tag 023Z](https://stacks.math.columbia.edu/tag/023Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Examples

universe u

namespace AlgebraicGeometry.TwistedDoubledOrigin

variable (k K : Type u) [Field k] [Field K] [Algebra k K]

/-- The structure morphism over `Spec k'` of the affine line over `k'` with the origin doubled —
the scheme `X_{k'}` of part (6) of Stacks 03FN, presented as two copies of the chart
`U = Spec k'[x]` glued along the puncture: project to the chart, then take the chart's own
structure morphism. -/
def doubledLineToSpec :
    (doubleSectionCover (cover K) (puncturedCover K)).total ⟶ Spec (.of K) :=
  (doubleSectionCover (cover K) (puncturedCover K)).proj ≫ coverToSpecExtension K

/-- Each sheet of the doubled line is a section of the structure morphism over `Spec k'`. -/
theorem chart_comp_doubledLineToSpec (b : Bool) :
    (doubleSectionCover (cover K) (puncturedCover K)).chart b ≫ doubledLineToSpec K =
      coverToSpecExtension K := by
  rw [doubledLineToSpec, ← Category.assoc,
    (doubleSectionCover (cover K) (puncturedCover K)).chart_comp_proj, Category.id_comp]

/-- **The Galois twist is compatible on the overlaps of the two sheets.** This is the condition
under which the Galois automorphism of the chart, followed on each sheet by the *other* sheet,
glues to a morphism of the doubled line.

On the diagonal overlaps the two projections of the fibre square coincide, because a sheet is a
split monomorphism; on the off-diagonal ones the fibre square is the puncture, where the two
sheets agree. -/
theorem galoisAction_chart_compat (σ : K ≃ₐ[k] K) (b c : Bool) :
    pullback.fst ((doubleSectionCover (cover K) (puncturedCover K)).chart b)
          ((doubleSectionCover (cover K) (puncturedCover K)).chart c) ≫
        galoisAction k K σ ≫ (doubleSectionCover (cover K) (puncturedCover K)).chart (!b) =
      pullback.snd ((doubleSectionCover (cover K) (puncturedCover K)).chart b)
          ((doubleSectionCover (cover K) (puncturedCover K)).chart c) ≫
        galoisAction k K σ ≫ (doubleSectionCover (cover K) (puncturedCover K)).chart (!c) := by
  have hdiag : ∀ d : Bool,
      pullback.fst ((doubleSectionCover (cover K) (puncturedCover K)).chart d)
          ((doubleSectionCover (cover K) (puncturedCover K)).chart d) =
        pullback.snd ((doubleSectionCover (cover K) (puncturedCover K)).chart d)
          ((doubleSectionCover (cover K) (puncturedCover K)).chart d) := by
    intro d
    have : IsSplitMono ((doubleSectionCover (cover K) (puncturedCover K)).chart d) :=
      IsSplitMono.mk' ⟨(doubleSectionCover (cover K) (puncturedCover K)).proj,
        (doubleSectionCover (cover K) (puncturedCover K)).chart_comp_proj d⟩
    exact (cancel_mono ((doubleSectionCover (cover K) (puncturedCover K)).chart d)).mp
      pullback.condition
  have hagree : (puncturedCover K).ι ≫ galoisAction k K σ ≫
        (doubleSectionCover (cover K) (puncturedCover K)).chart true =
      (puncturedCover K).ι ≫ galoisAction k K σ ≫
        (doubleSectionCover (cover K) (puncturedCover K)).chart false := by
    have h := congrArg (fun m : (puncturedCover K).toScheme ⟶
          (doubleSectionCover (cover K) (puncturedCover K)).total =>
        galoisActionPuncturedMap k K σ ≫ m)
      (doubleSectionCover_chart_agree (cover K) (puncturedCover K))
    rw [← Category.assoc, ← Category.assoc, galoisActionPuncturedMap_ι, Category.assoc,
      Category.assoc] at h
    exact h
  have hoff : ∀ b c : Bool, b ≠ c →
      pullback.fst ((doubleSectionCover (cover K) (puncturedCover K)).chart b)
            ((doubleSectionCover (cover K) (puncturedCover K)).chart c) ≫
          galoisAction k K σ ≫ (doubleSectionCover (cover K) (puncturedCover K)).chart (!b) =
        pullback.snd ((doubleSectionCover (cover K) (puncturedCover K)).chart b)
            ((doubleSectionCover (cover K) (puncturedCover K)).chart c) ≫
          galoisAction k K σ ≫ (doubleSectionCover (cover K) (puncturedCover K)).chart (!c) := by
    intro b c hbc
    have hp := doubleSectionCover_isPullback_chart (cover K) (puncturedCover K) hbc
    rw [← cancel_epi hp.isoPullback.hom, hp.isoPullback_hom_fst_assoc,
      hp.isoPullback_hom_snd_assoc]
    cases b <;> cases c <;> simp_all
  cases b <;> cases c
  · rw [hdiag]
  · exact hoff false true (by decide)
  · exact hoff true false (by decide)
  · rw [hdiag]

/-- **The Galois twist of the doubled line**: the morphism gluing, on each sheet, the Galois
automorphism of the chart followed by the *other* sheet. -/
def doubledLineTwist (σ : K ≃ₐ[k] K) :
    (doubleSectionCover (cover K) (puncturedCover K)).total ⟶
      (doubleSectionCover (cover K) (puncturedCover K)).total :=
  (doubleSectionCover (cover K) (puncturedCover K)).cover.glueMorphisms
    (fun b => galoisAction k K σ ≫ (doubleSectionCover (cover K) (puncturedCover K)).chart (!b))
    (galoisAction_chart_compat k K σ)

/-- The Galois twist carries each sheet of the doubled line to the other, twisted by the Galois
automorphism of the chart. -/
theorem chart_comp_doubledLineTwist (σ : K ≃ₐ[k] K) (b : Bool) :
    (doubleSectionCover (cover K) (puncturedCover K)).chart b ≫ doubledLineTwist k K σ =
      galoisAction k K σ ≫ (doubleSectionCover (cover K) (puncturedCover K)).chart (!b) :=
  (doubleSectionCover (cover K) (puncturedCover K)).cover.ι_glueMorphisms _ _ b

/-- **The Galois twist is semilinear** over the Galois automorphism of `Spec k'`: it covers that
automorphism through the structure morphism of the doubled line. -/
theorem doubledLineTwist_semilinear (σ : K ≃ₐ[k] K) :
    doubledLineTwist k K σ ≫ doubledLineToSpec K =
      doubledLineToSpec K ≫ specGaloisAction k K σ := by
  have key : ∀ b : Bool,
      (doubleSectionCover (cover K) (puncturedCover K)).chart b ≫
          doubledLineTwist k K σ ≫ doubledLineToSpec K =
        (doubleSectionCover (cover K) (puncturedCover K)).chart b ≫
          doubledLineToSpec K ≫ specGaloisAction k K σ := by
    intro b
    rw [← Category.assoc, chart_comp_doubledLineTwist, Category.assoc,
      chart_comp_doubledLineToSpec, ← Category.assoc, chart_comp_doubledLineToSpec]
    dsimp only [coverToSpecExtension, galoisAction, specGaloisAction]
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact RingHom.ext fun a => by simp
  exact (doubleSectionCover (cover K) (puncturedCover K)).cover.hom_ext _ _ key

/-- **The Galois twist is an involution**, because the Galois automorphism of the chart is one and
the two sheets are exchanged twice. -/
theorem doubledLineTwist_involutive [FiniteDimensional k K] [IsGalois k K]
    (hdegree : Module.finrank k K = 2) (σ : K ≃ₐ[k] K) :
    doubledLineTwist k K σ ≫ doubledLineTwist k K σ =
      𝟙 (doubleSectionCover (cover K) (puncturedCover K)).total := by
  have key : ∀ b : Bool,
      (doubleSectionCover (cover K) (puncturedCover K)).chart b ≫
          doubledLineTwist k K σ ≫ doubledLineTwist k K σ =
        (doubleSectionCover (cover K) (puncturedCover K)).chart b ≫
          𝟙 (doubleSectionCover (cover K) (puncturedCover K)).total := by
    intro b
    rw [← Category.assoc, chart_comp_doubledLineTwist, Category.assoc,
      chart_comp_doubledLineTwist, Bool.not_not, ← Category.assoc,
      galoisAction_involutive k K hdegree σ, Category.id_comp, Category.comp_id]
  exact (doubleSectionCover (cover K) (puncturedCover K)).cover.hom_ext _ _ key

/-- The `k'`-rational origin of the chart `U = Spec k'[x]`, the point whose `x`-coordinate is
zero. -/
def specOrigin : Spec (.of K) ⟶ cover K :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : K)))

/-- The origin is a section of the structure morphism of the chart over `Spec k'`. -/
theorem specOrigin_comp_coverToSpecExtension :
    specOrigin K ≫ coverToSpecExtension K = 𝟙 (Spec (.of K)) := by
  dsimp only [specOrigin, coverToSpecExtension]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
    show (Polynomial.evalRingHom (0 : K)).comp (algebraMap K (Polynomial K)) = RingHom.id K from
      RingHom.ext fun a => by simp]
  simp

/-- The Galois automorphism of the chart carries the origin to the origin, twisted by the Galois
automorphism of `Spec k'`. -/
theorem specOrigin_comp_galoisAction (σ : K ≃ₐ[k] K) :
    specOrigin K ≫ galoisAction k K σ = specGaloisAction k K σ ≫ specOrigin K := by
  dsimp only [specOrigin, galoisAction, specGaloisAction]
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext <;> simp

/-- The puncture is dense in the chart: the chart is irreducible and the puncture is a nonempty
open subscheme of it. -/
theorem dense_puncturedCover : Dense ((puncturedCover K : Set (cover K))) := by
  have : PreirreducibleSpace (cover K) := by
    show PreirreducibleSpace (PrimeSpectrum (Polynomial K)); infer_instance
  refine (puncturedCover K).isOpen.dense ⟨⟨⊥, inferInstance⟩, ?_⟩
  exact Polynomial.X_ne_zero

/-- The origin does not lie in the puncture: the coordinate pulls back to `0` along it. -/
theorem specOrigin_preimage_puncturedCover : specOrigin K ⁻¹ᵁ puncturedCover K = ⊥ := by
  rw [specOrigin, SpecMap_preimage_basicOpen]
  show PrimeSpectrum.basicOpen ((Polynomial.evalRingHom (0 : K)) Polynomial.X) = ⊥
  simp

/-- **The doubled line has two distinct origins.** The two sheets do not agree at the origin of
the chart: a morphism out of `Spec k'` equalising them factors through the puncture, by the fibre
square of the two sheets, and the origin does not lie in the puncture. -/
theorem specOrigin_chart_ne :
    specOrigin K ≫ (doubleSectionCover (cover K) (puncturedCover K)).chart true ≠
      specOrigin K ≫ (doubleSectionCover (cover K) (puncturedCover K)).chart false := by
  intro h
  have hp := doubleSectionCover_isPullback_chart (cover K) (puncturedCover K)
    (show (true : Bool) ≠ false by decide)
  obtain ⟨l, hl, -⟩ := hp.exists_lift (specOrigin K) (specOrigin K) h
  have hmem : (specOrigin K) (default : Spec (.of K)) ∈ (puncturedCover K : Set (cover K)) := by
    rw [← Scheme.Opens.range_ι]
    exact ⟨l (default : Spec (.of K)),
      congrArg (fun m : Spec (.of K) ⟶ cover K => m (default : Spec (.of K))) hl⟩
  have hbot : (default : Spec (.of K)) ∈ specOrigin K ⁻¹ᵁ puncturedCover K := hmem
  rw [specOrigin_preimage_puncturedCover] at hbot
  exact hbot

variable [FiniteDimensional k K] [IsGalois k K]

/-- **Stacks 03FN, the closing claim.** For a degree two Galois extension `k'/k` with nonidentity
automorphism `σ` there is a descent datum for schemes relative to the one-member covering
`{Spec k' ⟶ Spec k}` which is not effective.

The datum is the Galois twist of the affine line over `k'` with the origin doubled; were it
effective, the two origins of that line would have the same image in the descended scheme, which
`AlgebraicGeometry.TwistedDoubledOrigin.specOrigin_chart_ne` forbids. -/
@[stacks 03FN "the descent datum relative to {Spec k' -> Spec k} which is not effective"]
theorem exists_descentDatum_specExtension_not_isEffective (hdegree : Module.finrank k K = 2)
    (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1) :
    ∃ D : DescentDatum (specExtension k K), ¬ DescentData.IsEffective D := by
  have hred : IsReduced (cover K) := by
    show IsReduced (Spec (.of (Polynomial K))); infer_instance
  have hsub : Subsingleton (Spec (.of K)) := by
    show Subsingleton (PrimeSpectrum K); infer_instance
  refine exists_descentDatum_not_isEffective_of_semilinear
    (isPullback_specExtension_split k K hdegree σ hσ)
    (specGaloisAction_involutive k K hdegree σ)
    (doubledLineTwist_involutive k K hdegree σ) (doubledLineTwist_semilinear k K σ) ?_
  intro W₀ w₀ α₀ hα₀ hinv
  -- the projection to the scheme the datum would descend to, read on each sheet
  have hinvfst : α₀.inv ≫ pullback.fst (specExtension k K) w₀ = doubledLineToSpec K := by
    rw [← hα₀, Iso.inv_hom_id_assoc]
  -- the two sheets, followed by that projection, differ by the Galois automorphism of the chart
  have hc : (doubleSectionCover (cover K) (puncturedCover K)).chart true ≫
        α₀.inv ≫ pullback.snd (specExtension k K) w₀ =
      galoisAction k K σ ≫ (doubleSectionCover (cover K) (puncturedCover K)).chart false ≫
        α₀.inv ≫ pullback.snd (specExtension k K) w₀ := by
    calc (doubleSectionCover (cover K) (puncturedCover K)).chart true ≫
          α₀.inv ≫ pullback.snd (specExtension k K) w₀
        = (doubleSectionCover (cover K) (puncturedCover K)).chart true ≫
            doubledLineTwist k K σ ≫ α₀.inv ≫ pullback.snd (specExtension k K) w₀ := by
          rw [hinv]
      _ = ((doubleSectionCover (cover K) (puncturedCover K)).chart true ≫
            doubledLineTwist k K σ) ≫ α₀.inv ≫ pullback.snd (specExtension k K) w₀ :=
          (Category.assoc _ _ _).symm
      _ = (galoisAction k K σ ≫
            (doubleSectionCover (cover K) (puncturedCover K)).chart false) ≫
            α₀.inv ≫ pullback.snd (specExtension k K) w₀ := by
          rw [chart_comp_doubledLineTwist, Bool.not_true]
      _ = galoisAction k K σ ≫ (doubleSectionCover (cover K) (puncturedCover K)).chart false ≫
            α₀.inv ≫ pullback.snd (specExtension k K) w₀ := Category.assoc _ _ _
  -- and they agree on the puncture, because the two sheets of the doubled line do
  have hagree : (puncturedCover K).ι ≫
        (doubleSectionCover (cover K) (puncturedCover K)).chart true ≫
          α₀.inv ≫ pullback.snd (specExtension k K) w₀ =
      (puncturedCover K).ι ≫
        (doubleSectionCover (cover K) (puncturedCover K)).chart false ≫
          α₀.inv ≫ pullback.snd (specExtension k K) w₀ := by
    have h := congrArg (fun m : (puncturedCover K).toScheme ⟶
          (doubleSectionCover (cover K) (puncturedCover K)).total =>
        m ≫ α₀.inv ≫ pullback.snd (specExtension k K) w₀)
      (doubleSectionCover_chart_agree (cover K) (puncturedCover K))
    simpa only [Category.assoc] using h
  -- the Galois automorphism of the chart fixes the origin, since `Spec k'` has one point
  have hfix : (galoisAction k K σ) ((specOrigin K) (default : Spec (.of K))) =
      (specOrigin K) (default : Spec (.of K)) := by
    have h := congrArg (fun m : Spec (.of K) ⟶ cover K => m (default : Spec (.of K)))
      (specOrigin_comp_galoisAction k K σ)
    change (galoisAction k K σ) ((specOrigin K) _) =
      (specOrigin K) ((specGaloisAction k K σ) _) at h
    rw [h, Subsingleton.elim ((specGaloisAction k K σ) (default : Spec (.of K)))
      (default : Spec (.of K))]
  -- so the two sheets already agree at the origin as points
  have hx : ((doubleSectionCover (cover K) (puncturedCover K)).chart true ≫
          α₀.inv ≫ pullback.snd (specExtension k K) w₀)
        ((specOrigin K) (default : Spec (.of K))) =
      ((doubleSectionCover (cover K) (puncturedCover K)).chart false ≫
          α₀.inv ≫ pullback.snd (specExtension k K) w₀)
        ((specOrigin K) (default : Spec (.of K))) := by
    have h := congrArg (fun m : cover K ⟶ W₀ => m ((specOrigin K) (default : Spec (.of K)))) hc
    change ((doubleSectionCover (cover K) (puncturedCover K)).chart true ≫
        α₀.inv ≫ pullback.snd (specExtension k K) w₀) _ =
      ((doubleSectionCover (cover K) (puncturedCover K)).chart false ≫
        α₀.inv ≫ pullback.snd (specExtension k K) w₀) ((galoisAction k K σ) _) at h
    rw [h, hfix]
  -- the puncture is dense and the chart is reduced, so they agree on the whole origin
  have hz : specOrigin K ≫ (doubleSectionCover (cover K) (puncturedCover K)).chart true ≫
        α₀.inv ≫ pullback.snd (specExtension k K) w₀ =
      specOrigin K ≫ (doubleSectionCover (cover K) (puncturedCover K)).chart false ≫
        α₀.inv ≫ pullback.snd (specExtension k K) w₀ :=
    comp_eq_of_dense_of_subsingleton _ _ (puncturedCover K) (dense_puncturedCover K) hagree
      (specOrigin K) (default : Spec (.of K)) hx
  -- hence the two origins of the doubled line coincide, which they do not
  refine specOrigin_chart_ne K ((cancel_mono α₀.inv).mp (pullback.hom_ext ?_ ?_))
  · simp only [Category.assoc, hinvfst, chart_comp_doubledLineToSpec]
  · simpa only [Category.assoc] using hz

end AlgebraicGeometry.TwistedDoubledOrigin

end
