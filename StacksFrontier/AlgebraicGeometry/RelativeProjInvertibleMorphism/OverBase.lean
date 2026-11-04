module

public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.GlobalMorphism
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTripleStructureMorphism
public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.ThetaChartDatum

/-!
# `r_{ℒ,ψ}` is a morphism over the base

Let `(S, 𝒜, f : X ⟶ S, ℒ, ψ)` be the data of [Stacks, Tag 01O8] and
`r_{ℒ,ψ} : U(ψ) ⟶ Proj_S(𝒜)` the morphism glued from the clause (3) prescriptions
(`…GradedPowerMap.globalMorphism`). [Stacks, Tag 01O9] calls it a morphism of schemes **over
`S`**: its composite with the structure morphism `π : Proj_S(𝒜) ⟶ S` is `f|_{U(ψ)}`. This file
proves that.

## The degree-zero compatibility

Over an affine open `V` of the base the prescription is [Stacks, Tag 01NK]'s morphism for the
induced datum followed by the chart of [Stacks, Tag 01NQ], and the chart lies over `V`. So what
has to be shown is that [Stacks, Tag 01NK]'s morphism `U(ψ_V) ⟶ Proj 𝒜(V)`, followed by
`Proj 𝒜(V) ⟶ Spec 𝒜(V)_0 ⟶ V`, is `f` restricted. On a chart `T_{ψ(g)}` the first morphism is
`Spec` of `a / g^n ↦ ψ(a) / ψ(g^n)`, so the composite ring map `Γ(V, 𝒪_S) ⟶ Γ(T_{ψ(g)}, 𝒪)` sends
`s` to `ψ(s · 1) / ψ(1)`; and `ψ` is `𝒪_S`-linear through `f^♯`, so this is `f^♯(s)`.
`glued_comp_projInclusionToOpen_ι` is that computation for an arbitrary datum, with the
linearity as its one hypothesis; `affineDatum_toFun_gradeZeroHom` discharges it for the datum
induced by `ψ`.

No unit law for `ψ` is used: `ψ(1)` cancels against itself on every chart.

## Main results

* `…RelativeProjInvertibleMorphism.glued_comp_projInclusionToOpen_ι`: a [Stacks, Tag 01NK]
  datum over `𝒜(V)` whose degree-zero component is linear through a morphism `F : Y ⟶ S` lying
  over `V` has its morphism lying over `V` through `F`.
* `…GradedPowerMap.globalMorphism_comp_toBase`: **`r_{ℒ,ψ} ≫ π = f|_{U(ψ)}`.**

## References

* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 01O8](https://stacks.math.columbia.edu/tag/01O8)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace HomogeneousLocalization
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.ProjChartFullGraded (GradedSections)
open Stacks.AlgebraicGeometry.ProjChartCocycle (ratioOf ratioOf_eq_of_resTop_eq)
open Stacks.TensorPowers (natTensorPow)
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.TensorPowerTrivialize (resTop)

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

section Datum

variable {S : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} {V : S.Opens} (hV : IsAffineOpen V)
  {Y : Scheme.{u}} {L : Y.Modules} [Stacks.Ample.IsInvertibleModule Y L]
  (ψ : GradedSections (A.grading V) L) (F : Y ⟶ S) (hF : F ⁻¹ᵁ V = ⊤)

/-- The ratio `ψ(x) / ψ(t)` depends only on the elements `t`, `x` and the degree they are read
at, not on the proofs of membership or the index spelling. -/
theorem ratioOf_toFun_congr {k k' : ℕ} {t x t' x' : A.sectionRing V}
    (ht : t ∈ A.grading V k) (hx : x ∈ A.grading V k) (ht' : t' ∈ A.grading V k')
    (hx' : x' ∈ A.grading V k') {W : Y.Opens}
    (hW : W ≤ nonvanishingOpen Y (natTensorPow L k) (ψ.toFun k ⟨t, ht⟩))
    (hW' : W ≤ nonvanishingOpen Y (natTensorPow L k') (ψ.toFun k' ⟨t', ht'⟩))
    (hk : k = k') (htt : t = t') (hxx : x = x') :
    ratioOf L (ψ.toFun k ⟨t, ht⟩) hW (ψ.toFun k ⟨x, hx⟩)
      = ratioOf L (ψ.toFun k' ⟨t', ht'⟩) hW' (ψ.toFun k' ⟨x', hx'⟩) := by
  subst hk htt hxx
  rfl

/-- `Spec` of a composite of three ring maps, checked on elements. -/
theorem spec_three_comp {R₀ R₁ R₂ R₃ : CommRingCat.{u}} (a : R₀ ⟶ R₁) (b : R₁ ⟶ R₂)
    (c : R₂ ⟶ R₃) (d : R₀ ⟶ R₃) (h : ∀ x, c (b (a x)) = d x) :
    Spec.map c ≫ Spec.map b ≫ Spec.map a = Spec.map d := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext h)

include hF in
/-- **On one chart**: the dehomogenisation chart of a homogeneous `g` of positive degree,
followed by `Proj 𝒜(V) ⟶ V ⊆ S`, is `F` restricted, for a datum linear through `F`. -/
theorem chartToProj_comp_projInclusionToOpen_ι
    (hq : ∀ s : Γ(S, V), ψ.toFun 0 (A.gradeZeroHom V s)
      = F.appLE V ⊤ hF.ge s • ψ.toFun 0 ⟨1, SetLike.one_mem_graded _⟩)
    {e : ℕ} {g : A.sectionRing V} (hg : g ∈ A.grading V e) (he : 0 < e) {W : Y.Opens}
    (hW : W ≤ nonvanishingOpen Y (natTensorPow L e) (ψ.toFun e ⟨g, hg⟩)) :
    ψ.chartToProj hg hW he ≫ projInclusionToOpen A V hV ≫ V.ι = W.ι ≫ F := by
  have hWF : W ≤ F ⁻¹ᵁ V := hF ▸ le_top
  have hR : W.ι ≫ F = (W.toSpecΓ ≫ Spec.map (F.appLE V W hWF)) ≫ hV.fromSpec := by
    rw [Scheme.Opens.toSpecΓ_SpecMap_appLE, Category.assoc, IsAffineOpen.toSpecΓ_fromSpec,
      Scheme.Hom.resLE_comp_ι]
  have hL : projInclusionToOpen A V hV ≫ V.ι
      = AlgebraicGeometry.Proj.toSpecZero (A.grading V) ≫
          Spec.map (A.toGradedAlgebra.strZero ⟨V, hV⟩) ≫ hV.fromSpec :=
    GradedAlgebra.toOpen_ι _ _
  rw [hR, hL]
  show ((ψ.homogeneousRatios hg hW).toSpecAway he ≫
      AlgebraicGeometry.Proj.awayι (A.grading V) g hg he) ≫ _ = _
  rw [Category.assoc, ← Category.assoc (AlgebraicGeometry.Proj.awayι _ _ _ _),
    AlgebraicGeometry.Proj.awayι_toSpecZero,
    Stacks.MorphismToProj.HomogeneousRatios.toSpecAway]
  simp only [Category.assoc]
  congr 1
  refine (spec_three_comp _ _ _ _ fun s => ?_) =≫ hV.fromSpec
  have hstr : A.toGradedAlgebra.strZero ⟨V, hV⟩ s = A.gradeZeroHom V s :=
    Subtype.ext (GradedAlgebra.coe_strZero_apply _ _ _)
  have hz : ((A.gradeZeroHom V s : A.grading V 0) : A.sectionRing V)
      ∈ A.grading V (0 • e) := by simpa using (A.gradeZeroHom V s).2
  have h1 : (1 : A.sectionRing V) ∈ A.grading V 0 := SetLike.one_mem_graded _
  have hW1 : W ≤ nonvanishingOpen Y (natTensorPow L 0) (ψ.toFun 0 ⟨1, h1⟩) :=
    (ψ.le_nonvanishingOpen_pow hg hW 0).trans
      (le_of_eq (ψ.nonvanishingOpen_congr _ h1 (Nat.zero_mul e) (pow_zero g)))
  show (ψ.homogeneousRatios hg hW).lift he
      (fromZeroRingHom (A.grading V) (Submonoid.powers g)
        (A.toGradedAlgebra.strZero ⟨V, hV⟩ s)) = F.appLE V W hWF s
  rw [hstr, Stacks.AlgebraicGeometry.ProjTripleStructureMorphism.fromZeroRingHom_eq_awayMk
      (A.grading V) hg _ hz,
    (ψ.homogeneousRatios hg hW).lift_mk he 0 _ hz ⟨_, hz⟩ rfl,
    GradedSections.homogeneousRatios_toFun,
    ratioOf_toFun_congr ψ _ _ h1 (A.gradeZeroHom V s).2 _ hW1 (Nat.zero_mul e) (pow_zero g) rfl]
  refine ratioOf_eq_of_resTop_eq L _ hW1 ?_
  rw [show (⟨_, (A.gradeZeroHom V s).2⟩ : A.grading V 0) = A.gradeZeroHom V s from rfl, hq s,
    Stacks.TensorPowerTrivialize.resTop, Scheme.Modules.map_smul]
  congr 1
  exact congrArg (fun φ => φ s) (congrArg CommRingCat.Hom.hom
    (Scheme.Hom.appLE_map F hF.ge (homOfLE (le_top : W ≤ ⊤)).op))

include hF in
/-- **[Stacks, Tag 01NK]'s morphism lies over the base, for a datum linear through `F`.** Let
`ψ` be a [Stacks, Tag 01NK] datum for the graded ring `𝒜(V)` on a scheme `Y`, and `F : Y ⟶ S` a
morphism landing in `V`. If the degree-zero component of `ψ` is `Γ(V, 𝒪_S)`-linear through `F`
— the value at the scalar `s · 1` is `F^♯(s)` times the value at `1` — then `r_{L, ψ}` followed by
`Proj 𝒜(V) ⟶ V ⊆ S` is `F` restricted to `U(ψ)`.

On the chart of `g` the composite ring map sends `s` to `ψ(s · 1) / ψ(1) = F^♯(s)`; that is
`chartToProj_comp_projInclusionToOpen_ι`, and the charts cover `U(ψ)`. -/
theorem glued_comp_projInclusionToOpen_ι
    (hq : ∀ s : Γ(S, V), ψ.toFun 0 (A.gradeZeroHom V s)
      = F.appLE V ⊤ hF.ge s • ψ.toFun 0 ⟨1, SetLike.one_mem_graded _⟩) :
    ψ.glued ≫ projInclusionToOpen A V hV ≫ V.ι = ψ.coveringOpen.ι ≫ F := by
  refine ψ.hom_ext_of_homOfLE_eq fun e g => ?_
  calc Y.homOfLE (ψ.nonvanishingOpenAt_le_coveringOpen e g) ≫ ψ.glued ≫
        projInclusionToOpen A V hV ≫ V.ι
      = (Y.homOfLE (ψ.nonvanishingOpenAt_le_coveringOpen e g) ≫ ψ.glued) ≫
          projInclusionToOpen A V hV ≫ V.ι := (Category.assoc _ _ _).symm
    _ = (ψ.nonvanishingOpenAt (e + 1) g).ι ≫ F := by
        rw [ψ.homOfLE_glued ⟨e, g⟩]
        exact chartToProj_comp_projInclusionToOpen_ι hV ψ F hF hq g.2 (Nat.succ_pos e) _
    _ = (Y.homOfLE (ψ.nonvanishingOpenAt_le_coveringOpen e g) ≫ ψ.coveringOpen.ι) ≫ F := by
        rw [Scheme.homOfLE_ι]
    _ = _ := Category.assoc _ _ _

end Datum

/-! ### The restriction of a section to an open subscheme is semilinear -/

section Restrict

variable {Z : Scheme.{u}} (M : Z.Modules) [Stacks.Ample.IsInvertibleModule Z M] (U : Z.Opens)

/-- **Reading a section over `U` as a global section on the open subscheme `U` is semilinear**:
a scalar `r ∈ Γ(Z, U)` acts afterwards as its image `U.ι^♯ r` restricted to `⊤`. -/
theorem restrictSection_smul (N : Z.Modules) (r : Γ(Z, U)) (x : Γ(N, U)) :
    Stacks.NonvanishingLocusRestrict.restrictSection U N (r • x)
      = U.toScheme.presheaf.map
          (homOfLE (Stacks.NonvanishingLocusRestrict.top_le_ι_preimage_self U)).op
          (U.ι.app U r) • Stacks.NonvanishingLocusRestrict.restrictSection U N x :=
  (congrArg (fun y => ((Stacks.AmpleLocallyClosed.pullbackModule U.ι N).presheaf.map
      (homOfLE (Stacks.NonvanishingLocusRestrict.top_le_ι_preimage_self U)).op).hom y)
    (Stacks.RingedSpace.pullbackUnit_smul U.ι.toLRSHom.toShHom N (op U) r x)).trans
    (Scheme.Modules.map_smul _ _ _ _)

/-- **`restrictPowSection` is semilinear** through `U.ι^♯`. -/
theorem restrictPowSection_smul (n : ℕ) (r : Γ(Z, U)) (x : Γ(natTensorPow M n, U)) :
    Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.restrictPowSection M U n (r • x)
      = U.toScheme.presheaf.map
          (homOfLE (Stacks.NonvanishingLocusRestrict.top_le_ι_preimage_self U)).op
          (U.ι.app U r) •
        Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.restrictPowSection M U n x := by
  rw [Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.restrictPowSection_eq,
    Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.restrictPowSection_eq,
    restrictSection_smul]
  exact Scheme.Modules.Hom.app_smul _ _ _

end Restrict

/-! ### The induced datum is linear through `f` -/

namespace GradedPowerMap

variable {S : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} {T : Scheme.{u}} {f : T ⟶ S}
  (P : GradedPowerMap A f)

/-- `f` restricted to `f^{-1}(V)`, read into `S`, has preimage of `V` everything. -/
theorem _root_.Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.preimage_ι_comp_eq_top
    {S T : Scheme.{u}} (f : T ⟶ S) (V : S.Opens) : ((f ⁻¹ᵁ V).ι ≫ f) ⁻¹ᵁ V = ⊤ := by
  rw [Scheme.Hom.comp_preimage, Scheme.Opens.ι_preimage_self]

/-- **The degree-zero component of the induced datum over `V` is `Γ(V, 𝒪_S)`-linear through
`f`**: its value at the scalar `s · 1` is `f^♯(s)` times its value at `1`. This is the
`𝒪_S`-linearity of the component `ψ_0`, `…GradedPowerMap.value_smul`, carried to the open
subscheme `f^{-1}(V)`. -/
theorem affineDatum_toFun_gradeZeroHom (V : S.Opens) (s : Γ(S, V)) :
    (P.affineDatum V).toFun 0 (A.gradeZeroHom V s)
      = ((f ⁻¹ᵁ V).ι ≫ f).appLE V ⊤ (preimage_ι_comp_eq_top f V).ge s •
          (P.affineDatum V).toFun 0 ⟨1, SetLike.one_mem_graded _⟩ := by
  have hc : A.componentEquiv V 0 (A.gradeZeroHom V s) = s • A.one V := by
    show (DirectSum.of (A.sectionPieces V) 0 (s • A.one V)) 0 = s • A.one V
    exact DirectSum.of_eq_same _ _
  have h1 : A.componentEquiv V 0 ⟨1, SetLike.one_mem_graded _⟩ = A.one V := by
    show (1 : A.sectionRing V) 0 = A.one V
    rw [DirectSum.one_def]
    exact DirectSum.of_eq_same _ _
  rw [affineDatum_toFun_apply, affineDatum_toFun_apply, hc, h1]
  show Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.restrictPowSection P.L
      (f ⁻¹ᵁ V) 0 (P.value 0 V (s • A.one V)) = _
  rw [P.value_smul 0 V s (A.one V), restrictPowSection_smul]
  congr 1

/-- **The prescription over an affine open `V` lies over `V`**: [Stacks, Tag 01NK]'s morphism for
the induced datum, followed by `Proj 𝒜(V) ⟶ V ⊆ S`, is `f` restricted. -/
theorem affineDatum_glued_comp_projInclusionToOpen_ι (V : S.Opens) (hV : IsAffineOpen V) :
    (P.affineDatum V).glued ≫ projInclusionToOpen A V hV ≫ V.ι
      = (P.affineDatum V).coveringOpen.ι ≫ (f ⁻¹ᵁ V).ι ≫ f :=
  glued_comp_projInclusionToOpen_ι hV (P.affineDatum V) ((f ⁻¹ᵁ V).ι ≫ f)
    (preimage_ι_comp_eq_top f V) (P.affineDatum_toFun_gradeZeroHom V)

variable (rp : RelativeProjData A)

/-- **`r_{ℒ,ψ}` is a morphism over `S`**: `r_{ℒ,ψ} ≫ π = f|_{U(ψ)}`, `π` the structure morphism of
the relative homogeneous spectrum. -/
theorem globalMorphism_comp_toBase : P.globalMorphism rp ≫ rp.toBase = P.toBase := by
  refine Scheme.hom_ext_of_affinePreimages P.toBase fun V => ?_
  have e0 : (P.toBase ⁻¹ᵁ V.1).ι ≫ P.globalMorphism rp ≫ rp.toBase = P.piece rp V ≫ rp.toBase :=
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ rp.toBase) (P.ι_globalMorphism rp V))
  have e1 : P.piece rp V ≫ rp.toBase
      = (P.toBaseIso V.1 V.2).hom ≫ (P.datumIso V.1).inv ≫
          ((P.affineDatum V.1).glued ≫ projInclusionToOpen A V.1 V.2 ≫ (V.1 : S.Opens).ι) := by
    simp only [piece, chartOver, Category.assoc]
    exact congrArg (fun k => (P.toBaseIso V.1 V.2).hom ≫ (P.datumIso V.1).inv ≫ k)
      (Stacks.AlgebraicGeometry.RelativeProjFromSections.relativeChart_comp_toBase rp V.1 V.2
        (P.affineDatum V.1))
  have e4 : (P.toBaseIso V.1 V.2).hom ≫ (P.datumIso V.1).inv = (P.pieceIso V.1 V.2).hom := rfl
  calc (P.toBase ⁻¹ᵁ V.1).ι ≫ P.globalMorphism rp ≫ rp.toBase
      = (P.toBaseIso V.1 V.2).hom ≫ (P.datumIso V.1).inv ≫
          ((P.affineDatum V.1).coveringOpen.ι ≫ (f ⁻¹ᵁ V.1).ι ≫ f) := by
        rw [e0, e1, P.affineDatum_glued_comp_projInclusionToOpen_ι V.1 V.2]
    _ = ((P.pieceIso V.1 V.2).hom ≫ (P.affineDatum V.1).coveringOpen.ι ≫ (f ⁻¹ᵁ V.1).ι) ≫ f := by
        rw [← e4]
        simp only [Category.assoc]
    _ = (P.toBase ⁻¹ᵁ V.1).ι ≫ P.toBase := by
        rw [P.pieceIso_comp_ι V.1 V.2]
        rfl

end GradedPowerMap

end Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

end
