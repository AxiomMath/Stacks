module

public import Mathlib.Algebra.Category.Grp.Biproducts
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AlmostBlowUp.GeneratorAlmostBlowUpFppfCriterion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HStructureSheaf.AffineAcyclic

/-!
# The sections of `𝒪^{perf}` along an almost blow up square

Let `p` be a prime, `S` a scheme over `𝔽_p` and `(Sch/S)_h` a big h site over `S`, and regard
`𝒪^{perf}` as a module over itself on the underlying category with the fppf topology. For an
almost blow up square `E ⟶ X'`, `Z ⟶ X` of the site, the sequence of sections

`0 ⟶ 𝒪^{perf}(X) ⟶ 𝒪^{perf}(Z) ⊕ 𝒪^{perf}(X') ⟶ 𝒪^{perf}(E) ⟶ 0`

is exact on the left and in the middle because `𝒪^{perf}` is an h sheaf (Stacks 0EVD), and it is
exact on the right as soon as `𝒪^{perf}(Z) ⟶ 𝒪^{perf}(E)` is surjective. This file proves that,
and that for the squares of More on Flatness, Example 0EVG, all four corners are affine and the
restriction from the centre to the exceptional corner is surjective. This is the input from
(the proof of) More on Flatness, Lemma 0EVK used in the proof of Stacks 0EWT.

## Main results

* `AddCommGrpCat.shortExact_biprodLift_biprodDesc`: a criterion for a short complex
  `A ⟶ B ⊞ C ⟶ D` of abelian groups of Mayer–Vietoris shape to be short exact.
* `AlgebraicGeometry.BigHOver.shortExact_sectionsShortComplex_perfectionModule`: the sequence of
  sections of `𝒪^{perf}` along an almost blow up square is short exact as soon as the restriction
  from the centre to the exceptional corner is surjective.

## References

* [Stacks Project, Tag 0EWT](https://stacks.math.columbia.edu/tag/0EWT)
* [Stacks Project, Tag 0EVK](https://stacks.math.columbia.edu/tag/0EVK)
* [Stacks Project, Tag 0EVD](https://stacks.math.columbia.edu/tag/0EVD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AddCommGrpCat

/-- **Short exactness of a Mayer–Vietoris short complex of abelian groups.** The short complex
`A ⟶ B ⊞ C ⟶ D` with maps `a ↦ (r₁ a, r₂ a)` and `(b, c) ↦ s₁ b - s₂ c` is short exact when the
first map is injective, a pair `(b, c)` with `s₁ b = s₂ c` comes from `A`, and every element of
`D` is of the form `s₁ b + s₂ c`. -/
theorem shortExact_biprodLift_biprodDesc {A B C D : AddCommGrpCat.{v}} (r₁ : A ⟶ B) (r₂ : A ⟶ C)
    (s₁ : B ⟶ D) (s₂ : C ⟶ D) (w : biprod.lift r₁ r₂ ≫ biprod.desc s₁ (-s₂) = 0)
    (hinj : ∀ a a', r₁ a = r₁ a' → r₂ a = r₂ a' → a = a')
    (hmid : ∀ b c, s₁ b = s₂ c → ∃ a, r₁ a = b ∧ r₂ a = c)
    (hsurj : ∀ d, ∃ b c, s₁ b + s₂ c = d) :
    (ShortComplex.mk _ _ w).ShortExact := by
  have hfst (x : ToType (B ⊞ C)) : (biprod.fst : B ⊞ C ⟶ B) x = ((biprodIsoProd B C).hom x).1 := by
    conv_lhs => rw [← (biprodIsoProd B C).hom_inv_id_apply x]
    exact biprodIsoProd_inv_comp_fst_apply B C _
  have hsnd (x : ToType (B ⊞ C)) : (biprod.snd : B ⊞ C ⟶ C) x = ((biprodIsoProd B C).hom x).2 := by
    conv_lhs => rw [← (biprodIsoProd B C).hom_inv_id_apply x]
    exact biprodIsoProd_inv_comp_snd_apply B C _
  have hext (x y : ToType (B ⊞ C)) (h₁ : (biprod.fst : B ⊞ C ⟶ B) x = (biprod.fst : B ⊞ C ⟶ B) y)
      (h₂ : (biprod.snd : B ⊞ C ⟶ C) x = (biprod.snd : B ⊞ C ⟶ C) y) : x = y := by
    rw [hfst, hfst] at h₁
    rw [hsnd, hsnd] at h₂
    exact (ConcreteCategory.bijective_of_isIso (biprodIsoProd B C).hom).1 (Prod.ext h₁ h₂)
  have hg (x : ToType (B ⊞ C)) : biprod.desc s₁ (-s₂) x =
      s₁ ((biprod.fst : B ⊞ C ⟶ B) x) - s₂ ((biprod.snd : B ⊞ C ⟶ C) x) := by
    conv_lhs => rw [← (biprodIsoProd B C).hom_inv_id_apply x]
    rw [biprodIsoProd_inv_comp_desc_apply, hfst, hsnd]
    simp [sub_eq_add_neg]
  have hl₁ (a : ToType A) : (biprod.fst : B ⊞ C ⟶ B) (biprod.lift r₁ r₂ a) = r₁ a := by
    rw [← ConcreteCategory.comp_apply, biprod.lift_fst]
  have hl₂ (a : ToType A) : (biprod.snd : B ⊞ C ⟶ C) (biprod.lift r₁ r₂ a) = r₂ a := by
    rw [← ConcreteCategory.comp_apply, biprod.lift_snd]
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · rw [ShortComplex.ab_exact_iff]
    intro x hx
    obtain ⟨a, ha₁, ha₂⟩ := hmid _ _ (sub_eq_zero.mp ((hg x).symm.trans hx))
    exact ⟨a, hext _ _ ((hl₁ a).trans ha₁) ((hl₂ a).trans ha₂)⟩
  · rw [AddCommGrpCat.mono_iff_injective]
    intro a a' h
    exact hinj a a' ((hl₁ a).symm.trans ((congrArg _ h).trans (hl₁ a')))
      ((hl₂ a).symm.trans ((congrArg _ h).trans (hl₂ a')))
  · rw [AddCommGrpCat.epi_iff_surjective]
    intro d
    obtain ⟨b, c, rfl⟩ := hsurj d
    refine ⟨(biprodIsoProd B C).inv (b, -c), ?_⟩
    change biprod.desc s₁ (-s₂) _ = _
    rw [biprodIsoProd_inv_comp_desc_apply]
    simp

end AddCommGrpCat

namespace AlgebraicGeometry.BigHOver

-- See `StacksFrontier.AlgebraicGeometry.EtaleCohomology.HStructureSheaf.AffineAcyclic`.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  [HasSheafify (fppfTopology B S hS) AddCommGrpCat.{u + 1}]
  [(fppfTopology B S hS).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]

/-- **The sections of `𝒪^{perf}` along a square sent to a cartesian square.** If
`X ↦ Γ(Xᵃʷⁿ, 𝒪)` sends a square `E ⟶ X'`, `Z ⟶ X` of the site to a cartesian square of sets, the
sequence `𝒪^{perf}(X) ⟶ 𝒪^{perf}(Z) ⊕ 𝒪^{perf}(X') ⟶ 𝒪^{perf}(E)` of sections of `𝒪^{perf}`,
regarded as a module over itself, is short exact as soon as every section over `E` is the
sum of the restrictions of a section over `Z` and a section over `X'`. -/
theorem shortExact_sectionsShortComplex_perfectionModule_of_isPullback
    (sq : Square (BigHOver B S hS))
    (hpb : IsPullback ((awnSections B S hS).map sq.f₃₄.op) ((awnSections B S hS).map sq.f₂₄.op)
      ((awnSections B S hS).map sq.f₁₃.op) ((awnSections B S hS).map sq.f₁₂.op))
    (hsurj : ∀ d, ∃ b c, (awnRingSheaf B S hS).obj.map sq.f₁₃.op b +
      (awnRingSheaf B S hS).obj.map sq.f₁₂.op c = d) :
    (Stacks.Cohomology.MayerVietoris.sectionsShortComplex sq
      (perfectionModule B S hS)).ShortExact := by
  refine AddCommGrpCat.shortExact_biprodLift_biprodDesc _ _ _ _ _ (fun a a' h₁ h₂ ↦ ?_)
    (fun b c h ↦ ?_) (fun d ↦ ?_)
  · exact congrArg ULift.up (Types.ext_of_isPullback hpb (congrArg ULift.down h₁)
      (congrArg ULift.down h₂))
  · obtain ⟨x, hx₁, hx₂⟩ := Types.exists_of_isPullback hpb b.down c.down (congrArg ULift.down h)
    exact ⟨ULift.up x, congrArg ULift.up hx₁, congrArg ULift.up hx₂⟩
  · obtain ⟨b, c, hbc⟩ := hsurj d.down
    exact ⟨ULift.up b, ULift.up c, congrArg ULift.up hbc⟩

/-- **The sections of `𝒪^{perf}` along an almost blow up square.** For an almost blow up square
`E ⟶ X'`, `Z ⟶ X` of the big h category over `S`, the sequence
`𝒪^{perf}(X) ⟶ 𝒪^{perf}(Z) ⊕ 𝒪^{perf}(X') ⟶ 𝒪^{perf}(E)` of sections of `𝒪^{perf}`, regarded as a
module over itself, is short exact as soon as every section over `E` is the difference of the
restrictions of a section over `Z` and a section over `X'`. Exactness on the left and in the
middle is the h sheaf property of `𝒪^{perf}` along the square, Stacks 0EVD. -/
theorem shortExact_sectionsShortComplex_perfectionModule (sq : Square (BigHOver B S hS))
    (I : ((BigHOver.toScheme B S hS).obj sq.X₄).IdealSheafData)
    (hb : IsAlmostBlowUpSquare I ((BigHOver.toScheme B S hS).map sq.f₂₄))
    (hZ : Nonempty (Over.mk ((BigHOver.toScheme B S hS).map sq.f₃₄) ≅ Over.mk I.subschemeι))
    (hSquare : (sq.map (BigHOver.toScheme B S hS)).IsPullback)
    (hsurj : ∀ d, ∃ b c, (awnRingSheaf B S hS).obj.map sq.f₁₃.op b +
      (awnRingSheaf B S hS).obj.map sq.f₁₂.op c = d) :
    (Stacks.Cohomology.MayerVietoris.sectionsShortComplex sq
      (perfectionModule B S hS)).ShortExact :=
  shortExact_sectionsShortComplex_perfectionModule_of_isPullback B S hS sq
    (isPullback_of_almostBlowUpSquare_bigH B S hS (awnSections B S hS)
      (isSheaf_awnSections B S hS) sq.f₂₄ sq.f₃₄ sq.f₁₂ sq.f₁₃ I hb hZ hSquare.flip) hsurj

section Frobenius

variable (p : ℕ) [Fact p.Prime] (hSp : Stacks.Frobenius.IsInCharacteristic S p)

include hSp in
omit [HasSheafify (fppfTopology B S hS) AddCommGrpCat.{u + 1}]
  [(fppfTopology B S hS).WEqualsLocallyBijective AddCommGrpCat.{u + 1}] in
/-- **Restriction of `𝒪^{perf}` along a morphism of affine objects surjective on functions is
surjective.** Over an affine object every section of `X ↦ Γ(Xᵃʷⁿ, 𝒪)` is the `pⁿ`-th root of the
pullback of a function, and the stage maps commute with restriction. -/
theorem surjective_awnSections_map_of_surjective {V W : BigHOver B S hS} (f : W ⟶ V)
    (hW : IsAffine ((BigHOver.toScheme B S hS).obj W))
    (hf : Function.Surjective ((BigHOver.toScheme B S hS).map f).appTop) :
    Function.Surjective ((awnSections B S hS).map f.op) := by
  intro y
  obtain ⟨n, b, -, hb, -⟩ := exists_awnStageFun_eq_pair B S hS p hSp W hW y y
  obtain ⟨a, rfl⟩ := hf b
  refine ⟨awnStageFun B S hS p hSp n V a, ?_⟩
  have h := NatTrans.naturality_apply (perfectionStage B S hS p hSp n) f.op a
  exact ((congrArg ((awnSections B S hS).map f.op)
    (perfectionStage_app_apply B S hS p hSp n (op V) a).symm).trans h.symm).trans
      ((perfectionStage_app_apply B S hS p hSp n (op W) _).trans hb)

end Frobenius


/-! ### The squares of Example 0EVG -/

section OneGenerator

variable {B S hS}

omit [HasSheafify (fppfTopology B S hS) AddCommGrpCat.{u + 1}]
  [(fppfTopology B S hS).WEqualsLocallyBijective AddCommGrpCat.{u + 1}] in
/-- The centre of a square of the family tested by Stacks 0EWR is a closed immersion. -/
theorem _root_.AlgebraicGeometry.GeneratorAlmostBlowUpSquare.isClosedImmersion_center
    (sq : GeneratorAlmostBlowUpSquare B S hS) :
    IsClosedImmersion ((BigHOver.toScheme B S hS).map sq.square.f₃₄) := by
  obtain ⟨e⟩ := sq.centerIso
  have hiso : IsIso e.hom.left :=
    (Over.forget ((BigHOver.toScheme B S hS).obj sq.square.X₄)).map_isIso e.hom
  have heq : e.hom.left ≫ sq.center.subschemeι = (BigHOver.toScheme B S hS).map sq.square.f₃₄ :=
    Over.w e.hom
  rw [← heq]
  infer_instance

omit [HasSheafify (fppfTopology B S hS) AddCommGrpCat.{u + 1}]
  [(fppfTopology B S hS).WEqualsLocallyBijective AddCommGrpCat.{u + 1}] in
/-- The centre of a square of the family tested by Stacks 0EWR has affine underlying scheme, being
closed in the affine base. -/
theorem _root_.AlgebraicGeometry.GeneratorAlmostBlowUpSquare.isAffine_center
    (sq : GeneratorAlmostBlowUpSquare B S hS) :
    IsAffine ((BigHOver.toScheme B S hS).obj sq.square.X₃) := by
  have := sq.isAffine_base
  have := sq.isClosedImmersion_center
  exact (IsClosedImmersion.isAffine_surjective_of_isAffine
    ((BigHOver.toScheme B S hS).map sq.square.f₃₄)).1

omit [HasSheafify (fppfTopology B S hS) AddCommGrpCat.{u + 1}]
  [(fppfTopology B S hS).WEqualsLocallyBijective AddCommGrpCat.{u + 1}] in
/-- **The corners of a square of Example 0EVG.** In a square of the shape of Example 0EVG the
modification is a closed immersion, so the modification and the exceptional corner have affine
underlying schemes, and restriction of functions from the centre to the exceptional corner is
surjective, the exceptional corner being closed in the affine centre. -/
theorem _root_.AlgebraicGeometry.GeneratorAlmostBlowUpSquare.oneGenerator_corners
    (sq : GeneratorAlmostBlowUpSquare B S hS)
    (h : IsOneGeneratorAlmostBlowUpModel ((BigHOver.toScheme B S hS).map sq.square.f₂₄)
      ((BigHOver.toScheme B S hS).map sq.square.f₃₄)) :
    IsAffine ((BigHOver.toScheme B S hS).obj sq.square.X₂) ∧
      IsAffine ((BigHOver.toScheme B S hS).obj sq.square.X₁) ∧
      Function.Surjective ((BigHOver.toScheme B S hS).map sq.square.f₁₃).appTop := by
  obtain ⟨A, hA, _f, J, -, -, iX, iX', -, hb, -⟩ := h
  have hcl : IsClosedImmersion ((BigHOver.toScheme B S hS).map sq.square.f₂₄) := by
    have hb' : (BigHOver.toScheme B S hS).map sq.square.f₂₄ =
        iX'.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ iX.inv := by
      rw [← Category.assoc, ← hb, Category.assoc, iX.hom_inv_id, Category.comp_id]
    have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    rw [hb']
    infer_instance
  have := sq.isAffine_base
  have := sq.isAffine_center
  have hE : IsClosedImmersion ((BigHOver.toScheme B S hS).map sq.square.f₁₃) :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) sq.isPullback hcl
  exact ⟨(IsClosedImmersion.isAffine_surjective_of_isAffine
      ((BigHOver.toScheme B S hS).map sq.square.f₂₄)).1,
    IsClosedImmersion.isAffine_surjective_of_isAffine
      ((BigHOver.toScheme B S hS).map sq.square.f₁₃)⟩

end OneGenerator


/-! ### The canonical map of Stacks 0F16 at `𝒪^{perf}` -/

section CSquare

variable (p : ℕ) [Fact p.Prime] (hSp : Stacks.Frobenius.IsInCharacteristic S p)
  [HasExt.{u + 1} (Sheaf (fppfTopology B S hS) AddCommGrpCat.{u + 1})]
  [EnoughInjectives (Sheaf (fppfTopology B S hS) AddCommGrpCat.{u + 1})]
  [EnoughInjectives (SheafOfModules.{u + 1} (perfectionRing B S hS))]

variable {B S hS}

omit [HasExt.{u + 1} (Sheaf (fppfTopology B S hS) AddCommGrpCat.{u + 1})]
  [EnoughInjectives (Sheaf (fppfTopology B S hS) AddCommGrpCat.{u + 1})]
  [EnoughInjectives (SheafOfModules.{u + 1} (perfectionRing B S hS))] in
/-- **The canonical map of Stacks 0F16 at `𝒪^{perf}` along a square of the family of Stacks
0EWR**, when the sections over each corner carry an injective resolution of `𝒪^{perf}` to a
quasi-isomorphism and every section of `𝒪^{perf}` over the exceptional corner is the sum of
restrictions from the centre and the modification. The sequence of sections is then short
exact. -/
theorem quasiIso_cSquare_perfectionModule (sq : GeneratorAlmostBlowUpSquare B S hS)
    (Rs : InjectiveResolution (perfectionModule B S hS))
    (hsurj : ∀ d, ∃ b c, (awnRingSheaf B S hS).obj.map sq.square.f₁₃.op b +
      (awnRingSheaf B S hS).obj.map sq.square.f₁₂.op c = d)
    [QuasiIso ((Stacks.MayerVietoris.CanonicalMapOfComplexes.sectionsComplex.{u + 1, u + 1}
      (perfectionRing B S hS) sq.square.X₁).map Rs.ι')]
    [QuasiIso ((Stacks.MayerVietoris.CanonicalMapOfComplexes.sectionsComplex.{u + 1, u + 1}
      (perfectionRing B S hS) sq.square.X₂).map Rs.ι')]
    [QuasiIso ((Stacks.MayerVietoris.CanonicalMapOfComplexes.sectionsComplex.{u + 1, u + 1}
      (perfectionRing B S hS) sq.square.X₃).map Rs.ι')]
    [QuasiIso ((Stacks.MayerVietoris.CanonicalMapOfComplexes.sectionsComplex.{u + 1, u + 1}
      (perfectionRing B S hS) sq.square.X₄).map Rs.ι')] :
    QuasiIso (Stacks.MayerVietoris.CanonicalMapOfComplexes.cSquare sq.square Rs.cochainComplex) :=
  Stacks.MayerVietoris.CanonicalMapOfComplexes.quasiIso_cSquare_of_shortExact sq.square Rs
    (shortExact_sectionsShortComplex_perfectionModule B S hS sq.square sq.center
      sq.isAlmostBlowUpSquare sq.centerIso sq.isPullback hsurj)

include hSp in
/-- **The squares of Example 0EVG.** At a square of the shape of More on Flatness, Example 0EVG,
all four corners are affine, so `𝒪^{perf}` has no higher cohomology on them, and the restriction
from the centre to the exceptional corner is surjective; the canonical map of Stacks 0F16 at
`𝒪^{perf}` is therefore a quasi-isomorphism. -/
theorem quasiIso_cSquare_perfectionModule_of_oneGenerator (sq : GeneratorAlmostBlowUpSquare B S hS)
    (h : IsOneGeneratorAlmostBlowUpModel ((BigHOver.toScheme B S hS).map sq.square.f₂₄)
      ((BigHOver.toScheme B S hS).map sq.square.f₃₄))
    (Rs : InjectiveResolution (perfectionModule B S hS)) :
    QuasiIso (Stacks.MayerVietoris.CanonicalMapOfComplexes.cSquare sq.square
      Rs.cochainComplex) := by
  obtain ⟨hX', hE, hsurj⟩ := sq.oneGenerator_corners h
  have := quasiIso_sections_map_ι'_perfectionModule B S hS p hSp _ hE Rs
  have := quasiIso_sections_map_ι'_perfectionModule B S hS p hSp _ hX' Rs
  have := quasiIso_sections_map_ι'_perfectionModule B S hS p hSp _ sq.isAffine_center Rs
  have := quasiIso_sections_map_ι'_perfectionModule B S hS p hSp _ sq.isAffine_base Rs
  exact quasiIso_cSquare_perfectionModule sq Rs (fun d ↦ by
    obtain ⟨b, hb⟩ := surjective_awnSections_map_of_surjective B S hS p hSp _ hE hsurj d
    exact ⟨b, 0, by rwa [map_zero, add_zero]⟩)

end CSquare


end AlgebraicGeometry.BigHOver
