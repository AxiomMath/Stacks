module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.EtalePointReadingRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.ChartClosedSubschemeBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.HomPoints

/-!
# The restriction of homogeneous sections between étale scheme points, read on `𝒜`

In Situation 0849 let `f : T ⟶ X` and `f ∘ k : T' ⟶ X` be étale scheme points of the base, for
a morphism `k : T' ⟶ T` of test objects, and let `W₁ ≤ k⁻¹(W)` be Zariski opens. A homogeneous
section `a` of `f^*𝒜_n` over `W` restricts to the section `Φ⁻¹(k^*a)` of `(f ∘ k)^*𝒜_n` over `W₁`,
where `Φ : (f ∘ k)^*𝒜 ≅ k^*(f^*𝒜)` is the identification of the restriction datum of Stacks 084A
(`AlgebraicGeometry.Space.RelativeProjSituation.pointTwistKerRestrict`). This file proves that,
read on the étale charts `W₁ ⟶ T' ⟶ X` and `W ⟶ T ⟶ X` of `X` through Stacks 03LW
(`AlgebraicGeometry.Space.RelativeProjSituation.etalePointReading`), this restriction is the
restriction map of `𝒜_n` along the morphism of charts
`AlgebraicGeometry.Space.RelativeProjSituation.etalePointChartRestrict`.

## Main results

* `AlgebraicGeometry.Space.RelativeProjSituation.etalePointReading_pointTwistKerRestrict`: the
  reading of `Φ⁻¹(k^*a)` is the restriction in `𝒜_n` of the reading of `a`.

## Implementation notes

The restriction datum unfolds to the inverse of the comparison of restricted algebras of the
shrunk situation, whose implicit site is `s.shrink.site`, while the readings live over `s.site`.
The two sites are equal by unfolding `shrink`, but comparing sections spelled through the two
times out. The proof is therefore carried out for a situation presented as
`RelativeProjSituation.mk B S hS X 𝒜 …` with variable fields, where both sites reduce to `B`,
and with every object spelled through that rebuilt situation, so that the instantiation for an
arbitrary situation, after `obtain`, matches syntactically. Each step is a separate lemma.

## References

* [Stacks Project, Tag 0849](https://stacks.math.columbia.edu/tag/0849)
* [Stacks Project, Tag 084A](https://stacks.math.columbia.edu/tag/084A)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Space

section Abstract

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X))
  {T T' : BigFppfOver B S hS} (k : T' ⟶ T) (f : yoneda.obj T ⟶ X.1)

/-- The comparison of restricted algebras on a pulled-back section is the restriction map, read
over `W₁ ≤ k⁻¹(W)`, at an abstract graded algebra. -/
private theorem pointComparison_app_val_app_pullbackSection (n : ℤ)
    {W : ((BigFppfOver.toScheme B S hS).obj T).Opens}
    {W₁ : ((BigFppfOver.toScheme B S hS).obj T').Opens}
    (hW : W₁ ≤ preimageOpens k W)
    (a : ((zariskiReading T (etalePointAlgebra A T f)).piece n).val.obj (op W)) :
    ((pointComparison A k f (yoneda.map k ≫ f) rfl).app n).val.app (op W₁)
        (Scheme.Modules.pullbackSection ((BigFppfOver.toScheme B S hS).map k)
          ((zariskiReading T (etalePointAlgebra A T f)).piece n) W W₁ hW a) =
      ((zariskiReading T' (etalePointAlgebra A T' (yoneda.map k ≫ f))).piece n).val.map
        (homOfLE hW).op
        (((pointRestriction A k f (yoneda.map k ≫ f) rfl).app n).val.app (op W) a) :=
  (PresheafOfModules.naturality_apply
    ((pointComparison A k f (yoneda.map k ≫ f) rfl).app n).val (homOfLE hW).op _).trans
    (congrArg (((zariskiReading T' (etalePointAlgebra A T' (yoneda.map k ≫ f))).piece n).val.map
      (homOfLE hW).op)
      (Stacks.RingedSpace.transposeHomApp_pullbackUnit _
        (pointRestriction A k f (yoneda.map k ≫ f) rfl) n W a))

end Abstract

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space.RelativeProjSituation

/-! ### For a situation presented by `RelativeProjSituation.mk` -/

section Mk

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  {𝒜 : SheafOfModules.GradedAlgebra.{u, u, u, u + 1} (structureRingSheaf B S hS X)}
  (hc : ∀ (i j : ℤ) (U : (SmallEtale B S hS X.1)ᵒᵖ) (a : (𝒜.piece i).val.obj U)
    (b : (𝒜.piece j).val.obj U), HEq ((𝒜.mul i j).app U a b) ((𝒜.mul j i).app U b a))
  (hn : ∀ n : ℤ, n < 0 → Limits.IsZero (𝒜.piece n))
  (hq : ∀ n : ℤ, (𝒜.piece n).IsQuasicoherentOnSite)
  (hκ : ∀ (n : ℤ) (U : (SmallEtale B S hS X.1)ᵒᵖ),
    HasCardinalLT ↥((𝒜.piece n).val.obj U) B.cutoff)

local notation "𝔰" => RelativeProjSituation.mk B S hS X 𝒜 hc hn hq hκ

variable {T T' : BigFppfOver (RelativeProjSituation.mk B S hS X 𝒜 hc hn hq hκ).site
    (RelativeProjSituation.mk B S hS X 𝒜 hc hn hq hκ).base
    (RelativeProjSituation.mk B S hS X 𝒜 hc hn hq hκ).containsBase}
  (k : T' ⟶ T)
  (hk : IsEtale (RelativeProjSituation.mk B S hS X 𝒜 hc hn hq hκ).site
    (RelativeProjSituation.mk B S hS X 𝒜 hc hn hq hκ).base
    (RelativeProjSituation.mk B S hS X 𝒜 hc hn hq hκ).containsBase
    (representedSpaceMap (RelativeProjSituation.mk B S hS X 𝒜 hc hn hq hκ).site
    (RelativeProjSituation.mk B S hS X 𝒜 hc hn hq hκ).base
    (RelativeProjSituation.mk B S hS X 𝒜 hc hn hq hκ).containsBase k).hom)
  (f : yoneda.obj T ⟶ (RelativeProjSituation.mk B S hS X 𝒜 hc hn hq hκ).space.1)
  (hf : IsEtale (RelativeProjSituation.mk B S hS X 𝒜 hc hn hq hκ).site
    (RelativeProjSituation.mk B S hS X 𝒜 hc hn hq hκ).base
    (RelativeProjSituation.mk B S hS X 𝒜 hc hn hq hκ).containsBase
    (pointHom (X := (RelativeProjSituation.mk B S hS X 𝒜 hc hn hq hκ).space) f).hom)
  (hf' : IsEtale (RelativeProjSituation.mk B S hS X 𝒜 hc hn hq hκ).site
    (RelativeProjSituation.mk B S hS X 𝒜 hc hn hq hκ).base
    (RelativeProjSituation.mk B S hS X 𝒜 hc hn hq hκ).containsBase
    (pointHom (X := (RelativeProjSituation.mk B S hS X 𝒜 hc hn hq hκ).space)
      (yoneda.map k ≫ f)).hom)

/-- The inverse of the restriction of the restriction datum is the comparison of restricted
algebras, spelled through the site of the situation. -/
private theorem inv_restrict_app_mk (n : ℤ) :
    haveI := (𝔰).quadrupleRestriction.isIso_restrict_app k f (yoneda.map k ≫ f) rfl n
    inv (((𝔰).quadrupleRestriction.restrict k f (yoneda.map k ≫ f) rfl).app n) =
      (pointComparison (B := (𝔰).site) (S := (𝔰).base) (hS := (𝔰).containsBase)
        (X := (𝔰).space) ((𝔰).shrink.algebra : SheafOfModules.GradedAlgebra.{u, u}
          (structureRingSheaf (𝔰).site (𝔰).base (𝔰).containsBase (𝔰).space))
        k f (yoneda.map k ≫ f) rfl).app n :=
  inv_quadrupleRestriction_restrict_app (𝔰) k f n

/-- The restriction `Φ⁻¹(k^*a)` is the restriction, to `W₁`, of the restriction map of the
restricted algebras, spelled through the site of the situation. -/
private theorem pointTwistKerRestrict_mk (n : ℤ)
    {W : ((BigFppfOver.toScheme (𝔰).site (𝔰).base (𝔰).containsBase).obj T).Opens}
    {W₁ : ((BigFppfOver.toScheme (𝔰).site (𝔰).base (𝔰).containsBase).obj T').Opens}
    (hW : W₁ ≤ preimageOpens k W) (a : Γ(((𝔰).relativeProjPoints.algebra T f).piece n, W)) :
    pointTwistKerRestrict (s := 𝔰) k f n hW a =
      ((zariskiReading (B := (𝔰).site) T' (etalePointAlgebra
          (B := (𝔰).site) (S := (𝔰).base) (hS := (𝔰).containsBase)
          (X := (𝔰).space) ((𝔰).shrink.algebra : SheafOfModules.GradedAlgebra.{u, u}
            (structureRingSheaf (𝔰).site (𝔰).base (𝔰).containsBase (𝔰).space))
          T' (yoneda.map k ≫ f))).piece n).val.map (homOfLE hW).op
        (((pointRestriction (B := (𝔰).site) (S := (𝔰).base) (hS := (𝔰).containsBase)
          (X := (𝔰).space) ((𝔰).shrink.algebra : SheafOfModules.GradedAlgebra.{u, u}
            (structureRingSheaf (𝔰).site (𝔰).base (𝔰).containsBase (𝔰).space))
          k f (yoneda.map k ≫ f) rfl).app n).val.app (op W) a) :=
  (congrArg (fun φ => φ.val.app (op W₁) (Scheme.Modules.pullbackSection
      ((BigFppfOver.toScheme (𝔰).site (𝔰).base (𝔰).containsBase).map k)
      ((zariskiReading (B := (𝔰).site) T (etalePointAlgebra
          (B := (𝔰).site) (S := (𝔰).base) (hS := (𝔰).containsBase)
        (X := (𝔰).space) ((𝔰).shrink.algebra : SheafOfModules.GradedAlgebra.{u, u}
          (structureRingSheaf (𝔰).site (𝔰).base (𝔰).containsBase (𝔰).space))
        T f)).piece n) W W₁ hW a))
    (inv_restrict_app_mk hc hn hq hκ k f n)).trans
    (pointComparison_app_val_app_pullbackSection
        (B := (𝔰).site) (S := (𝔰).base) (hS := (𝔰).containsBase)
      (X := (𝔰).space) ((𝔰).shrink.algebra : SheafOfModules.GradedAlgebra.{u, u}
        (structureRingSheaf (𝔰).site (𝔰).base (𝔰).containsBase (𝔰).space))
      k f n hW a)

/-- The reading on the chart of `W₁` of the restriction to `W₁ ≤ k⁻¹(W)`. -/
private theorem etalePointReading_restrict_pointRestriction_mk (n : ℤ)
    {W : ((BigFppfOver.toScheme (𝔰).site (𝔰).base (𝔰).containsBase).obj T).Opens}
    {W₁ : ((BigFppfOver.toScheme (𝔰).site (𝔰).base (𝔰).containsBase).obj T').Opens}
    (hW : W₁ ≤ preimageOpens k W) (a : Γ(((𝔰).relativeProjPoints.algebra T f).piece n, W)) :
    (𝔰).etalePointReading (yoneda.map k ≫ f) hf' n W₁
        (((zariskiReading (B := (𝔰).site) T' (etalePointAlgebra
            (B := (𝔰).site) (S := (𝔰).base) (hS := (𝔰).containsBase)
          (X := (𝔰).space) ((𝔰).shrink.algebra : SheafOfModules.GradedAlgebra.{u, u}
            (structureRingSheaf (𝔰).site (𝔰).base (𝔰).containsBase (𝔰).space))
          T' (yoneda.map k ≫ f))).piece n).val.map (homOfLE hW).op
        (((pointRestriction (B := (𝔰).site) (S := (𝔰).base) (hS := (𝔰).containsBase)
          (X := (𝔰).space) ((𝔰).shrink.algebra : SheafOfModules.GradedAlgebra.{u, u}
            (structureRingSheaf (𝔰).site (𝔰).base (𝔰).containsBase (𝔰).space))
          k f (yoneda.map k ≫ f) rfl).app n).val.app (op W) a)) =
      ((𝔰).algebra.piece n).val.map ((smallEtalePostcomp (𝔰).site (𝔰).base (𝔰).containsBase
          (pointHom (X := (𝔰).space) (yoneda.map k ≫ f)) hf').map
            ((selfOpensFunctor (𝔰).site (𝔰).base (𝔰).containsBase T').map (homOfLE hW))).op
        ((𝔰).etalePointReading (yoneda.map k ≫ f) hf' n (preimageOpens k W)
          (((pointRestriction (B := (𝔰).site) (S := (𝔰).base) (hS := (𝔰).containsBase)
            (X := (𝔰).space) ((𝔰).shrink.algebra : SheafOfModules.GradedAlgebra.{u, u}
              (structureRingSheaf (𝔰).site (𝔰).base (𝔰).containsBase (𝔰).space))
            k f (yoneda.map k ≫ f) rfl).app n).val.app (op W) a)) :=
  (𝔰).etalePointReading_restrict (yoneda.map k ≫ f) hf' n hW
    (((pointRestriction (B := (𝔰).site) (S := (𝔰).base) (hS := (𝔰).containsBase)
      (X := (𝔰).space) ((𝔰).shrink.algebra : SheafOfModules.GradedAlgebra.{u, u}
        (structureRingSheaf (𝔰).site (𝔰).base (𝔰).containsBase (𝔰).space))
      k f (yoneda.map k ≫ f) rfl).app n).val.app (op W) a)

/-- `AlgebraicGeometry.Space.RelativeProjSituation.etalePointReading_pointTwistKerRestrict` for
a situation presented by `RelativeProjSituation.mk`. -/
private theorem etalePointReading_pointTwistKerRestrict_mk (n : ℤ)
    {W : ((BigFppfOver.toScheme (𝔰).site (𝔰).base (𝔰).containsBase).obj T).Opens}
    {W₁ : ((BigFppfOver.toScheme (𝔰).site (𝔰).base (𝔰).containsBase).obj T').Opens}
    (hW : W₁ ≤ preimageOpens k W) (a : Γ(((𝔰).relativeProjPoints.algebra T f).piece n, W)) :
    (𝔰).etalePointReading (yoneda.map k ≫ f) hf' n W₁
        (pointTwistKerRestrict (s := 𝔰) k f n hW a) =
      ((𝔰).algebra.piece n).val.map ((𝔰).etalePointChartRestrict k hk f hf hf' hW).op
        ((𝔰).etalePointReading f hf n W a) :=
  ((congrArg ((𝔰).etalePointReading (yoneda.map k ≫ f) hf' n W₁)
      (pointTwistKerRestrict_mk hc hn hq hκ k f n hW a)).trans
    (etalePointReading_restrict_pointRestriction_mk hc hn hq hκ k f hf' n hW a)).trans
  ((congrArg (((𝔰).algebra.piece n).val.map ((smallEtalePostcomp (𝔰).site (𝔰).base (𝔰).containsBase
      (pointHom (X := (𝔰).space) (yoneda.map k ≫ f)) hf').map
        ((selfOpensFunctor (𝔰).site (𝔰).base (𝔰).containsBase T').map (homOfLE hW))).op)
      ((𝔰).etalePointReading_pointRestriction k hk f hf hf' n W a)).trans
    (CategoryTheory.congr_fun (((𝔰).algebra.piece n).val.presheaf.map_comp _ _) _).symm)

end Mk

/-! ### For an arbitrary situation -/

section Situation

variable (s : RelativeProjSituation.{u, u}) {T T' : BigFppfOver s.site s.base s.containsBase}
  (k : T' ⟶ T) (hk : IsEtale s.site s.base s.containsBase (representedSpaceMap s.site s.base
    s.containsBase k).hom)
  (f : yoneda.obj T ⟶ s.space.1)
  (hf : IsEtale s.site s.base s.containsBase (pointHom (X := s.space) f).hom)
  (hf' : IsEtale s.site s.base s.containsBase (pointHom (X := s.space) (yoneda.map k ≫ f)).hom)

/-- **The restriction of homogeneous sections along a morphism of étale scheme points, read on
`𝒜`.** For étale scheme points `f` and `f ∘ k` and Zariski opens `W₁ ≤ k⁻¹(W)`, the restriction
`Φ⁻¹(k^*a)` of a section `a` of `f^*𝒜_n` over `W` (`pointTwistKerRestrict`, for the restriction
datum of Stacks 084A) reads, on the chart `W₁ ⟶ T' ⟶ X`, as the restriction in `𝒜_n`, along the
morphism of charts `etalePointChartRestrict`, of the reading of `a` on the chart `W ⟶ T ⟶ X`. -/
theorem etalePointReading_pointTwistKerRestrict (n : ℤ)
    {W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens}
    {W₁ : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T').Opens}
    (hW : W₁ ≤ preimageOpens k W) (a : Γ((s.relativeProjPoints.algebra T f).piece n, W)) :
    s.etalePointReading (yoneda.map k ≫ f) hf' n W₁ (pointTwistKerRestrict k f n hW a) =
      (s.algebra.piece n).val.map (s.etalePointChartRestrict k hk f hf hf' hW).op
        (s.etalePointReading f hf n W a) := by
  obtain ⟨B, S, hS, X, 𝒜, hc, hn, hq, hκ⟩ := s
  exact etalePointReading_pointTwistKerRestrict_mk (B := B) (S := S) (hS := hS) (X := X)
    (𝒜 := 𝒜) hc hn hq hκ k hk f hf hf' n hW a

end Situation

end AlgebraicGeometry.Space.RelativeProjSituation

end
