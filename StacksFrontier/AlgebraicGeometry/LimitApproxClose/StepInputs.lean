module

public import StacksFrontier.AlgebraicGeometry.LimitApproxClose.ChartingLeg
public import StacksFrontier.AlgebraicGeometry.LimitApproxClose.FibreProductRange
public import StacksFrontier.AlgebraicGeometry.LimitApproxJoin.StepTwo

/-!
# Four inputs of the one-affine-open step

The one-affine-open step of Tag 07RN builds its second glueing leg out of a *charting family*:
at every sufficiently late stage `k` of the overlap, finitely many sections `f k` of the model
`W_k` whose standard opens are affine and cover it, lifting a fixed finite family `g` of sections
of the affine open being added.  This file states three facts about that family:

* the family itself, at a stage, *together with* the affineness and covering conditions — step (ii)
  consumes those conditions and returns only the open immersion, so the family
  cannot be recovered from it;
* the **image** of the charting morphism, not merely that it is an open immersion — this is what
  makes the two chart hypotheses `hrU` and `hcover` of
  `Stacks.StageSubalgebra.isOpenImmersion_specLeg_app` available at every stage;
* that each stage of the *spectral* leg is of finite type over the terminal scheme, the
  distinguished subalgebras being finitely generated over the integers.

## Main results

* `AlgebraicGeometry.opensRange_comp_congr`: two open immersions with the same image have the
  same image after composition with a further morphism.  The further morphism is *not* assumed to
  be an open immersion — in the application it is the spectrum of a projection of a fibre product,
  which is not one; only the two composites are.  That is why Mathlib's
  `AlgebraicGeometry.Scheme.Hom.opensRange_comp` does not apply and this is proved on ranges of
  the underlying maps.

* `AlgebraicGeometry.opensRange_toSpecΓ_comp_SpecMap_snd` is the image of the charting morphism:
  the union of the standard opens of the family read inside the spectrum of the fibre product.
  It is `AlgebraicGeometry.Scheme.opensRange_toSpecΓ_eq_iSup_basicOpen` to move the
  image onto the union of standard opens, then `opensRange_comp_congr`, then
  `AlgebraicGeometry.opensRange_iSup_basicOpen_comp_SpecMap_snd`, which is the strengthened
  Tag 01Z9.

* `AlgebraicGeometry.exists_stage_affine_basicOpen_cover_of_opensRange` is the family at a stage.
  Its proof is the first half of
  `AlgebraicGeometry.exists_stage_isOpenImmersion_toSpecΓ_comp_SpecMap_snd`: the standard opens of
  the `g l` pulled back to the vertex are affine and cover it, and then
  `AlgebraicGeometry.exists_stage_affine_basicOpen_cover` descends them to a stage.  Unlike that
  result, it returns the family.

* `AlgebraicGeometry.locallyOfFiniteType_terminal_from_spec_of_finiteType`: the spectrum of a
  finite-type algebra over the integers is of finite type over the terminal scheme.  The chosen
  terminal scheme is not `Spec ℤ`, so the structure morphism is factored through
  `Spec (ULift ℤ)` by `CategoryTheory.Limits.terminal.hom_ext` and the second factor is an
  isomorphism — the pattern of
  `Stacks.AlgebraicGeometry.locallyOfFiniteType_terminalFrom_proj`.

## Implementation notes

One scheme universe throughout; the index categories are `Category.{u}` as step (ii)
and Tag 01Z0 require, which the preorders here satisfy.

Transparency gotchas:

* `AlgebraicGeometry.opensRange_toSpecΓ_comp_SpecMap_snd` states the open-immersion instance it
  needs with `haveI` inside its own type, since `AlgebraicGeometry.Scheme.Hom.opensRange` is only
  defined for open immersions; the instance is step (ii) at the same arguments, and a
  consumer that has its own proof of the same instance still matches by proof irrelevance.

* `AlgebraicGeometry.opensRange_comp_congr` is proved on `Set.range` of the underlying continuous
  maps rather than by rewriting with the image of an open, because the composite is written
  through `Scheme.Hom.comp_base` and the coercion to a set does not reduce through the open's
  structure.

## References

* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
* [Stacks Project, Tag 01Z9](https://stacks.math.columbia.edu/tag/01Z9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

/-- **Two open immersions with the same image have the same image after composition.**  The
morphism composed with is not assumed to be an open immersion; only the two composites are. -/
lemma opensRange_comp_congr {X X' Y Z : Scheme.{u}} (a : X ⟶ Y) (a' : X' ⟶ Y) (b : Y ⟶ Z)
    [IsOpenImmersion a] [IsOpenImmersion a'] [IsOpenImmersion (a ≫ b)]
    [IsOpenImmersion (a' ≫ b)] (h : a.opensRange = a'.opensRange) :
    (a ≫ b).opensRange = (a' ≫ b).opensRange := by
  have h' : Set.range a.base = Set.range a'.base :=
    congrArg (fun U : Y.Opens ↦ (U : Set Y)) h
  refine Opens.ext ?_
  change Set.range (a ≫ b).base = Set.range (a' ≫ b).base
  simp only [Scheme.Hom.comp_base, TopCat.coe_comp]
  rw [Set.range_comp, Set.range_comp, h']

/-- **The image of the charting morphism of the one-affine-open step.**  At a quasi-affine stage
covered by the affine standard opens of lifts `f` of the `s (g l)`, the morphism to the spectrum
of the fibre product has image the union of the standard opens of the lifted pairs. -/
lemma opensRange_toSpecΓ_comp_SpecMap_snd {J : Type u} [Category.{u} J]
    {D : J ⥤ Scheme.{u}} {R : CommRingCat.{u}}
    (τ : D.op ⋙ Scheme.Γ ⟶ (Functor.const Jᵒᵖ).obj R) {B : CommRingCat.{u}} (s : B ⟶ R)
    (j : J) [(D.obj j).IsQuasiAffine] {n : ℕ} (g : Fin n → B) (f : Fin n → Γ(D.obj j, ⊤))
    (hf : ∀ l, τ.app (op j) (f l) = s (g l))
    (hloc : ∀ l, Function.Bijective (Localization.awayMap s.hom (g l)))
    (haff : ∀ l, IsAffineOpen ((D.obj j).basicOpen (f l)))
    (hcov : ⨆ l, (D.obj j).basicOpen (f l) = ⊤) :
    haveI := isOpenImmersion_toSpecΓ_comp_SpecMap_snd τ s j g f hf hloc haff hcov
    ((D.obj j).toSpecΓ ≫ Spec.map (Stacks.FibreProduct.snd s (τ.app (op j)))).opensRange =
      (⨆ l, PrimeSpectrum.basicOpen (Stacks.FibreProduct.mk s (τ.app (op j)) (g l) (f l)
          (hf l).symm) :
        (Spec (Stacks.FibreProduct.obj s (τ.app (op j)))).Opens) := by
  have := isOpenImmersion_toSpecΓ_comp_SpecMap_snd τ s j g f hf hloc haff hcov
  have hoi : IsOpenImmersion
      ((⨆ l, PrimeSpectrum.basicOpen (f l) : (Spec Γ(D.obj j, ⊤)).Opens).ι ≫
        Spec.map (Stacks.FibreProduct.snd s (τ.app (op j)))) :=
    isOpenImmersion_spec_fibreProduct_of_app_eq τ s g (op j) f hf hloc
  have heq : (D.obj j).toSpecΓ.opensRange =
      (⨆ l, PrimeSpectrum.basicOpen (f l) : (Spec Γ(D.obj j, ⊤)).Opens) :=
    Scheme.opensRange_toSpecΓ_eq_iSup_basicOpen _ f haff hcov
  refine (opensRange_comp_congr (D.obj j).toSpecΓ
    (⨆ l, PrimeSpectrum.basicOpen (f l) : (Spec Γ(D.obj j, ⊤)).Opens).ι
    (Spec.map (Stacks.FibreProduct.snd s (τ.app (op j))))
    (heq.trans (Scheme.Opens.opensRange_ι _).symm)).trans ?_
  exact opensRange_iSup_basicOpen_comp_SpecMap_snd s (τ.app (op j)) g f
    (fun l ↦ (hf l).symm) hloc hoi

/-- **The charting family at a stage, with its affineness and covering conditions.**  The
standard opens of the `g l` pulled back to the vertex of a limiting cone are affine and cover it,
so `AlgebraicGeometry.exists_stage_affine_basicOpen_cover` descends them to a stage. -/
lemma exists_stage_affine_basicOpen_cover_of_opensRange {J : Type u} [Category.{u} J]
    [IsCofiltered J] (D : J ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : J} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    {Y : Scheme.{u}} [IsAffine Y] (jVY : c.pt ⟶ Y) [IsOpenImmersion jVY]
    {n : ℕ} (g : Fin n → Γ(Y, ⊤)) (hin : ∀ l, Y.basicOpen (g l) ≤ jVY.opensRange)
    (hcover : jVY.opensRange ≤ ⨆ l, Y.basicOpen (g l)) :
    ∃ (j : J) (f : Fin n → Γ(D.obj j, ⊤)),
      (∀ l, (c.π.app j).appTop (f l) = jVY.appTop (g l)) ∧
        (∀ l, IsAffineOpen ((D.obj j).basicOpen (f l))) ∧
        ⨆ l, (D.obj j).basicOpen (f l) = ⊤ := by
  have hcpt : CompactSpace c.pt := Scheme.compactSpace_of_isLimit D c hc
  have : c.pt.IsQuasiAffine := Scheme.IsQuasiAffine.of_isImmersion jVY
  have haff : ∀ l, IsAffineOpen (c.pt.basicOpen (jVY.appTop (g l))) := fun l ↦ by
    rw [← Scheme.preimage_basicOpen_top,
      ← Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion jVY,
      show jVY ''ᵁ (jVY ⁻¹ᵁ Y.basicOpen (g l)) = Y.basicOpen (g l) from
        Opens.ext (Set.image_preimage_eq_of_subset fun x hx ↦ hin l hx)]
    exact (isAffineOpen_top Y).basicOpen (g l)
  have hcov : ⨆ l, c.pt.basicOpen (jVY.appTop (g l)) = ⊤ := by
    refine top_unique fun x _ ↦ Opens.mem_iSup.mpr ?_
    obtain ⟨l, hl⟩ := Opens.mem_iSup.mp (hcover ⟨x, rfl⟩)
    exact ⟨l, (Scheme.preimage_basicOpen_top jVY (g l)).le hl⟩
  exact exists_stage_affine_basicOpen_cover D c hc (fun l ↦ jVY.appTop (g l)) haff hcov

/-- **The spectrum of a finite-type algebra over the integers is of finite type over the terminal
scheme.**  The chosen terminal scheme is not the spectrum of the integers, so the structure
morphism is factored through `Spec (ULift ℤ)`, whose own structure morphism is an
isomorphism. -/
lemma locallyOfFiniteType_terminal_from_spec_of_finiteType (A : Type u) [CommRing A]
    [Algebra ℤ A] [Algebra.FiniteType ℤ A] :
    LocallyOfFiniteType (terminal.from (Spec (CommRingCat.of A))) := by
  have := isIso_of_isTerminal specULiftZIsTerminal.{u} terminalIsTerminal (terminal.from _)
  set φ : ULift.{u} ℤ →+* A :=
    (algebraMap ℤ A).comp (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toRingHom with hφ
  have hfac : terminal.from (Spec (CommRingCat.of A)) =
      Spec.map (CommRingCat.ofHom φ) ≫
        terminal.from (Spec (CommRingCat.of (ULift.{u} ℤ))) := terminal.hom_ext _ _
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom φ)) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact (RingHom.finiteType_algebraMap.mpr inferInstance).comp
      (RingHom.FiniteType.of_surjective _ (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).surjective)
  rw [hfac]
  infer_instance

end AlgebraicGeometry
