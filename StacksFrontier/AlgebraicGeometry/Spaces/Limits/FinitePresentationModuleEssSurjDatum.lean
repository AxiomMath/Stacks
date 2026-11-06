module

public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationEtaleDescentSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationModuleEssSurjPair

/-!
# Essential surjectivity in Stacks 07V7: the descent datum at a stage

Let `ψ` be a twisted transition morphism on the kernel pair `U_m ×_{X_m} U_m` of the chart of a
stage (`AlgebraicGeometry.Space.exists_isTwistedTransition`).  Its restrictions along the
morphisms into the kernel pair are the pair morphisms of this file.  At the limit they are the
twisted comparisons, so they satisfy the cocycle condition there and are the identity on the
diagonal; by the faithfulness clause for the systems of base changes of the triple product and
of the chart, they satisfy both at a later stage, where they form a descent datum relative to
the chart.

## Main definitions

* `AlgebraicGeometry.Space.pairMorphism`: the restriction of `ψ` along the morphism into the
  kernel pair given by two morphisms into the chart.

## References

* [Stacks Project, Tag 07V7](https://stacks.math.columbia.edu/tag/07V7)
* [Stacks Project, Tag 04W3](https://stacks.math.columbia.edu/tag/04W3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hZ : B.Contains (⊤_ Scheme.{u}))
variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (hL : HasSiteLimit B S hS D)
  (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
variable {i : I} {U₀ : BigAffineFppf B S hS}
  {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i}
  (C : AffineChartSystem B S hS i D U₀ f₀) (m : Over i)

section Naturality

open QuasiCoherentDescent

omit [IsCofiltered I] in
/-- The canonical comparison through the comparisons of iterated inverse images. -/
theorem canonicalComparison_eq_trans {X' P Q : AlgebraicSpaces B S hS} (a b : P ⟶ Q) (g : Q ⟶ X')
    (h : a ≫ g = b ≫ g) (M : Modules.{u, u} B S hS X'.1 X'.2) :
    canonicalComparison a b g g h M =
      (pullbackComparison B S hS a g (a ≫ g) rfl M).symm ≪≫
        pullbackComparison B S hS b g (a ≫ g) h.symm M := by
  rw [pullbackComparison_eq_trans b g (a ≫ g) h.symm M, canonicalComparison]

omit [IsCofiltered I] in
/-- The forward morphism of the canonical comparison is the inverse of the first comparison of
iterated inverse images followed by the second. -/
theorem canonicalComparison_hom_eq {X' P Q : AlgebraicSpaces B S hS} (a b : P ⟶ Q) (g : Q ⟶ X')
    (h : a ≫ g = b ≫ g) (M : Modules.{u, u} B S hS X'.1 X'.2) :
    (canonicalComparison a b g g h M).hom =
      (pullbackComparison B S hS a g (a ≫ g) rfl M).inv ≫
        (pullbackComparison B S hS b g (a ≫ g) h.symm M).hom :=
  congrArg Iso.hom (canonicalComparison_eq_trans B S hS a b g h M)

omit [IsCofiltered I] in
/-- **The twisted comparison of an identification compatible with a descent datum is its
transition morphism.**  Let `α : f^*G ≅ g^*M` be compatible with an isomorphism
`φ : a^*(f^*G) ≅ b^*(f^*G)` and the canonical comparison of the two inverse images of `M`.  Then
the twisted comparison of `α⁻¹` at `a, b` is `φ`, read through `homConjLInv`. -/
theorem twistedComparison_eq_of_naturality {X' Q P V : AlgebraicSpaces B S hS} (g : Q ⟶ X')
    (f : Q ⟶ V) {M : Modules.{u, u} B S hS X'.1 X'.2} {G : Modules.{u, u} B S hS V.1 V.2}
    (α : (modulePullback B S hS f).obj G ≅ (modulePullback B S hS g).obj M) (a b : P ⟶ Q)
    (hab : a ≫ g = b ≫ g)
    (φ : (modulePullback B S hS a).obj ((modulePullback B S hS f).obj G) ⟶
      (modulePullback B S hS b).obj ((modulePullback B S hS f).obj G))
    (hφ : (modulePullback B S hS a).map α.hom ≫ (canonicalComparison a b g g hab M).hom =
      φ ≫ (modulePullback B S hS b).map α.hom) :
    twistedComparison g f α.symm a b (a ≫ g) (a ≫ f) (b ≫ f) rfl hab.symm rfl rfl =
      homConjLInv a b f f φ := by
  have hφ' : φ = (modulePullback B S hS a).map α.hom ≫
      (canonicalComparison a b g g hab M).hom ≫ (modulePullback B S hS b).map α.inv := by
    rw [← Category.assoc, hφ, Category.assoc, ← Functor.map_comp, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.comp_id]
  rw [twistedComparison, homConjLInv, hφ', canonicalComparison_hom_eq B S hS a b g hab M]
  simp only [moduleHomRestrict₂, Iso.symm_inv, Iso.symm_hom, pullbackComparison_rfl,
    Iso.app_inv, Iso.app_hom, Category.assoc]

end Naturality

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_FinitePresentationModuleEssSurjDatum :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- Pullbacks of presheaves on the big fppf site, found directly. -/
local instance (priority := high) hasPullback_presheaf_FinitePresentationModuleEssSurjDatum
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

section PairMorphism

variable {V : AlgebraicSpaces B S hS} (u : schemeSpace (C.siteDiagram.obj m) ⟶ V)
  {G : Modules.{u, u} B S hS V.1 V.2}
  (ψ : (modulePullback B S hS (stageChartPairFst B S hS D hD C m ≫ u)).obj G ⟶
    (modulePullback B S hS (stageChartPairSnd B S hS D hD C m ≫ u)).obj G)

/-- The morphism into the kernel pair given by two morphisms into the chart. -/
noncomputable def chartPairLift {T : AlgebraicSpaces B S hS}
    (x y : T ⟶ schemeSpace (C.siteDiagram.obj m))
    (h : x ≫ chartStageMap B S hS D hD U₀ f₀ C m = y ≫ chartStageMap B S hS D hD U₀ f₀ C m) :
    T ⟶ stageChartPair B S hS D hD C m :=
  ObjectProperty.homMk (pullback.lift x.hom y.hom (congrArg (fun z => z.hom) h))

omit [IsCofiltered I] in
/-- The first projection of `chartPairLift x y h` is `x`. -/
@[simp]
theorem chartPairLift_fst {T : AlgebraicSpaces B S hS}
    (x y : T ⟶ schemeSpace (C.siteDiagram.obj m))
    (h : x ≫ chartStageMap B S hS D hD U₀ f₀ C m = y ≫ chartStageMap B S hS D hD U₀ f₀ C m) :
    chartPairLift B S hS D hD C m x y h ≫ stageChartPairFst B S hS D hD C m = x :=
  ObjectProperty.hom_ext _ (pullback.lift_fst _ _ _)

omit [IsCofiltered I] in
/-- The second projection of `chartPairLift x y h` is `y`. -/
@[simp]
theorem chartPairLift_snd {T : AlgebraicSpaces B S hS}
    (x y : T ⟶ schemeSpace (C.siteDiagram.obj m))
    (h : x ≫ chartStageMap B S hS D hD U₀ f₀ C m = y ≫ chartStageMap B S hS D hD U₀ f₀ C m) :
    chartPairLift B S hS D hD C m x y h ≫ stageChartPairSnd B S hS D hD C m = y :=
  ObjectProperty.hom_ext _ (pullback.lift_snd _ _ _)

omit [IsCofiltered I] in
/-- If `w ≫ pr = x` and `x ≫ u = vx`, then `w ≫ pr ≫ u = vx`. -/
theorem pairMorphism_aux {T R' Um : AlgebraicSpaces B S hS} (w : T ⟶ R') (pr : R' ⟶ Um)
    (x : T ⟶ Um) (vx : T ⟶ V) (u : Um ⟶ V) (hw : w ≫ pr = x) (hx : x ≫ u = vx) :
    w ≫ pr ≫ u = vx := by
  rw [← Category.assoc, hw, hx]

/-- **The pair morphisms.**  The restriction of `ψ` along the morphism into the kernel pair given
by two morphisms `x, y` into the chart with equal composites to the stage. -/
noncomputable def pairMorphism {T : AlgebraicSpaces B S hS}
    (x y : T ⟶ schemeSpace (C.siteDiagram.obj m))
    (h : x ≫ chartStageMap B S hS D hD U₀ f₀ C m = y ≫ chartStageMap B S hS D hD U₀ f₀ C m)
    (vx vy : T ⟶ V) (hx : x ≫ u = vx) (hy : y ≫ u = vy) :
    (modulePullback B S hS vx).obj G ⟶ (modulePullback B S hS vy).obj G :=
  moduleHomRestrict₂ G G (chartPairLift B S hS D hD C m x y h)
    (stageChartPairFst B S hS D hD C m ≫ u)
    (stageChartPairSnd B S hS D hD C m ≫ u) vx vy
    (pairMorphism_aux B S hS _ _ x vx u (chartPairLift_fst B S hS D hD C m x y h) hx)
    (pairMorphism_aux B S hS _ _ y vy u (chartPairLift_snd B S hS D hD C m x y h) hy) ψ

omit [IsCofiltered I] in
/-- The restriction of `ψ` along any morphism into the kernel pair is a pair morphism. -/
theorem moduleHomRestrict₂_eq_pairMorphism {T : AlgebraicSpaces B S hS}
    (w : T ⟶ stageChartPair B S hS D hD C m) (x y : T ⟶ schemeSpace (C.siteDiagram.obj m))
    (hw₁ : w ≫ stageChartPairFst B S hS D hD C m = x)
    (hw₂ : w ≫ stageChartPairSnd B S hS D hD C m = y)
    (h : x ≫ chartStageMap B S hS D hD U₀ f₀ C m = y ≫ chartStageMap B S hS D hD U₀ f₀ C m)
    (vx vy : T ⟶ V) (hx : x ≫ u = vx) (hy : y ≫ u = vy) :
    moduleHomRestrict₂ G G w (stageChartPairFst B S hS D hD C m ≫ u)
        (stageChartPairSnd B S hS D hD C m ≫ u) vx vy
        (pairMorphism_aux B S hS _ _ x vx u hw₁ hx) (pairMorphism_aux B S hS _ _ y vy u hw₂ hy)
        ψ =
      pairMorphism B S hS D hD C m u ψ x y h vx vy hx hy := by
  have : w = chartPairLift B S hS D hD C m x y h := chartPair_hom_ext B S hS D hD C m
    (by rw [hw₁, chartPairLift_fst]) (by rw [hw₂, chartPairLift_snd])
  subst this
  rfl

omit [IsCofiltered I] in
/-- **The pair morphisms are stable under restriction.** -/
theorem moduleHomRestrict₂_pairMorphism {T T' : AlgebraicSpaces B S hS} (s : T' ⟶ T)
    (x y : T ⟶ schemeSpace (C.siteDiagram.obj m))
    (h : x ≫ chartStageMap B S hS D hD U₀ f₀ C m = y ≫ chartStageMap B S hS D hD U₀ f₀ C m)
    (vx vy : T ⟶ V) (hx : x ≫ u = vx) (hy : y ≫ u = vy)
    (x' y' : T' ⟶ schemeSpace (C.siteDiagram.obj m)) (hsx : s ≫ x = x') (hsy : s ≫ y = y')
    (h' : x' ≫ chartStageMap B S hS D hD U₀ f₀ C m = y' ≫ chartStageMap B S hS D hD U₀ f₀ C m)
    (vx' vy' : T' ⟶ V) (hsvx : s ≫ vx = vx') (hsvy : s ≫ vy = vy') (hx' : x' ≫ u = vx')
    (hy' : y' ≫ u = vy') :
    moduleHomRestrict₂ G G s vx vy vx' vy' hsvx hsvy
        (pairMorphism B S hS D hD C m u ψ x y h vx vy hx hy) =
      pairMorphism B S hS D hD C m u ψ x' y' h' vx' vy' hx' hy' := by
  rw [pairMorphism, moduleHomRestrict₂_moduleHomRestrict₂ _ s _ rfl]
  exact moduleHomRestrict₂_eq_pairMorphism B S hS D hD C m u ψ _ x' y'
    (by rw [Category.assoc, chartPairLift_fst, hsx])
    (by rw [Category.assoc, chartPairLift_snd, hsy])
    h' vx' vy' hx' hy'

omit [IsCofiltered I] in
/-- The pair morphism at `x, y` equals the pair morphism at `x', y'` when `x = x'` and `y = y'`. -/
theorem pairMorphism_congr {T : AlgebraicSpaces B S hS}
    {x y x' y' : T ⟶ schemeSpace (C.siteDiagram.obj m)} (ex : x = x') (ey : y = y')
    (h : x ≫ chartStageMap B S hS D hD U₀ f₀ C m = y ≫ chartStageMap B S hS D hD U₀ f₀ C m)
    (vx vy : T ⟶ V) (hx : x ≫ u = vx) (hy : y ≫ u = vy) :
    pairMorphism B S hS D hD C m u ψ x y h vx vy hx hy =
      pairMorphism B S hS D hD C m u ψ x' y' (ex ▸ ey ▸ h) vx vy (ex ▸ hx) (ey ▸ hy) := by
  subst ex ey
  rfl

section At

variable (n : Over i) (uu : schemeSpace (C.siteDiagram.obj n) ⟶ schemeSpace (C.siteDiagram.obj m))
  (huu : ∀ (T : AlgebraicSpaces B S hS) (x y : T ⟶ schemeSpace (C.siteDiagram.obj n)),
      x ≫ chartStageMap B S hS D hD U₀ f₀ C n = y ≫ chartStageMap B S hS D hD U₀ f₀ C n →
        (x ≫ uu) ≫ chartStageMap B S hS D hD U₀ f₀ C m =
          (y ≫ uu) ≫ chartStageMap B S hS D hD U₀ f₀ C m)

/-- The pair morphisms at points of the chart `U_n`, through `uu : U_n ⟶ U_m`. -/
noncomputable def pairMorphismAt {T : AlgebraicSpaces B S hS}
    (x y : T ⟶ schemeSpace (C.siteDiagram.obj n))
    (h : x ≫ chartStageMap B S hS D hD U₀ f₀ C n = y ≫ chartStageMap B S hS D hD U₀ f₀ C n) :
    (modulePullback B S hS (x ≫ uu ≫ u)).obj G ⟶ (modulePullback B S hS (y ≫ uu ≫ u)).obj G :=
  pairMorphism B S hS D hD C m u ψ (x ≫ uu) (y ≫ uu) (huu T x y h) (x ≫ uu ≫ u) (y ≫ uu ≫ u)
    (Category.assoc _ _ _) (Category.assoc _ _ _)

omit [IsCofiltered I] in
/-- `pairMorphismAt` at `x, y` is the pair morphism at `x ≫ uu, y ≫ uu`. -/
theorem pairMorphismAt_eq {T : AlgebraicSpaces B S hS}
    (x y : T ⟶ schemeSpace (C.siteDiagram.obj n))
    (h : x ≫ chartStageMap B S hS D hD U₀ f₀ C n = y ≫ chartStageMap B S hS D hD U₀ f₀ C n) :
    pairMorphismAt B S hS D hD C m u ψ n uu huu x y h =
      pairMorphism B S hS D hD C m u ψ (x ≫ uu) (y ≫ uu) (huu T x y h) (x ≫ uu ≫ u) (y ≫ uu ≫ u)
        (Category.assoc _ _ _) (Category.assoc _ _ _) := rfl

omit [IsCofiltered I] in
/-- The restriction along `s : T' ⟶ T` of `pairMorphismAt` at `x, y` is `pairMorphismAt` at
`s ≫ x, s ≫ y`. -/
theorem moduleHomRestrict₂_pairMorphismAt {T T' : AlgebraicSpaces B S hS} (s : T' ⟶ T)
    (x y : T ⟶ schemeSpace (C.siteDiagram.obj n))
    (h : x ≫ chartStageMap B S hS D hD U₀ f₀ C n = y ≫ chartStageMap B S hS D hD U₀ f₀ C n)
    (x' y' : T' ⟶ schemeSpace (C.siteDiagram.obj n)) (hsx : s ≫ x = x') (hsy : s ≫ y = y')
    (h' : x' ≫ chartStageMap B S hS D hD U₀ f₀ C n = y' ≫ chartStageMap B S hS D hD U₀ f₀ C n) :
    moduleHomRestrict₂ G G s (x ≫ uu ≫ u) (y ≫ uu ≫ u) (x' ≫ uu ≫ u) (y' ≫ uu ≫ u)
        (by subst hsx; simp only [Category.assoc]) (by subst hsy; simp only [Category.assoc])
        (pairMorphismAt B S hS D hD C m u ψ n uu huu x y h) =
      pairMorphismAt B S hS D hD C m u ψ n uu huu x' y' h' :=
  by
  subst hsx hsy
  exact moduleHomRestrict₂_pairMorphism B S hS D hD C m u ψ s (x ≫ uu) (y ≫ uu) (huu T x y h)
    (x ≫ uu ≫ u) (y ≫ uu ≫ u) (Category.assoc _ _ _) (Category.assoc _ _ _) _ _
    (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm (huu T' _ _ h') _ _
    (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm (Category.assoc _ _ _)
    (Category.assoc _ _ _)

variable (hcoc : ∀ (T : AlgebraicSpaces B S hS) (x y z : T ⟶ schemeSpace (C.siteDiagram.obj n))
      (hxy : x ≫ chartStageMap B S hS D hD U₀ f₀ C n = y ≫ chartStageMap B S hS D hD U₀ f₀ C n)
      (hyz : y ≫ chartStageMap B S hS D hD U₀ f₀ C n = z ≫ chartStageMap B S hS D hD U₀ f₀ C n),
      pairMorphismAt B S hS D hD C m u ψ n uu huu x y hxy ≫
          pairMorphismAt B S hS D hD C m u ψ n uu huu y z hyz =
        pairMorphismAt B S hS D hD C m u ψ n uu huu x z (hxy.trans hyz))
  (hid : ∀ (T : AlgebraicSpaces B S hS) (x : T ⟶ schemeSpace (C.siteDiagram.obj n)),
      pairMorphismAt B S hS D hD C m u ψ n uu huu x x rfl = 𝟙 _)

open QuasiCoherentDescent

include hcoc hid in
omit [IsCofiltered I] in
/-- Under the cocycle and identity conditions, `pairMorphismAt` at `x, y` followed by
`pairMorphismAt` at `y, x` is the identity. -/
theorem pairMorphismAt_comp_eq_id {T : AlgebraicSpaces B S hS}
    (x y : T ⟶ schemeSpace (C.siteDiagram.obj n))
    (h : x ≫ chartStageMap B S hS D hD U₀ f₀ C n = y ≫ chartStageMap B S hS D hD U₀ f₀ C n)
    (h' : y ≫ chartStageMap B S hS D hD U₀ f₀ C n = x ≫ chartStageMap B S hS D hD U₀ f₀ C n) :
    pairMorphismAt B S hS D hD C m u ψ n uu huu x y h ≫
        pairMorphismAt B S hS D hD C m u ψ n uu huu y x h' = 𝟙 _ := by
  rw [hcoc T x y x h h']
  exact hid T x

omit [IsCofiltered I] in
/-- The two projections from the fibre product of the chart `U_n` with itself over the stage have
equal composites to the stage. -/
theorem chartPair_condition' :
    pairFst B S hS (fun _ : Unit => schemeSpace (C.siteDiagram.obj n))
        (fun _ => chartStageMap B S hS D hD U₀ f₀ C n) () () ≫ chartStageMap B S hS D hD U₀ f₀ C n =
      pairSnd B S hS (fun _ : Unit => schemeSpace (C.siteDiagram.obj n))
        (fun _ => chartStageMap B S hS D hD U₀ f₀ C n) () () ≫
          chartStageMap B S hS D hD U₀ f₀ C n :=
  ObjectProperty.hom_ext _ pullback.condition

omit [IsCofiltered I] in
/-- The restriction along `v`, with projections `x` and `y`, of the conjugated `pairMorphismAt` on
the fibre product of the chart with itself is the conjugated `pairMorphismAt` at `x, y`. -/
theorem moduleHomRestrict₂_homConjL_pairMorphismAt {T : AlgebraicSpaces B S hS}
    (v : T ⟶ pair B S hS (fun _ : Unit => schemeSpace (C.siteDiagram.obj n))
      (fun _ => chartStageMap B S hS D hD U₀ f₀ C n) () ())
    (x y : T ⟶ schemeSpace (C.siteDiagram.obj n))
    (hx : v ≫ pairFst B S hS _ _ () () = x) (hy : v ≫ pairSnd B S hS _ _ () () = y)
    (h : x ≫ chartStageMap B S hS D hD U₀ f₀ C n = y ≫ chartStageMap B S hS D hD U₀ f₀ C n) :
    moduleHomRestrict₂ _ _ v _ _ x y hx hy
        (homConjL _ _ (uu ≫ u) (uu ≫ u) (pairMorphismAt B S hS D hD C m u ψ n uu huu _ _
          (chartPair_condition' B S hS D hD C n))) =
      homConjL x y (uu ≫ u) (uu ≫ u) (pairMorphismAt B S hS D hD C m u ψ n uu huu x y h) := by
  rw [moduleHomRestrict₂_homConjL]
  exact congrArg (homConjL x y (uu ≫ u) (uu ≫ u))
    (moduleHomRestrict₂_pairMorphismAt B S hS D hD C m u ψ n uu huu v _ _ _ x y hx hy h)

omit [IsCofiltered I] in
/-- Two morphisms into the chart `U_n` with equal composites to the stage factor through the
fibre product of the chart with itself over the stage. -/
theorem exists_lift_pair {T : AlgebraicSpaces B S hS} (x y : T ⟶ schemeSpace (C.siteDiagram.obj n))
    (h : x ≫ chartStageMap B S hS D hD U₀ f₀ C n = y ≫ chartStageMap B S hS D hD U₀ f₀ C n) :
    ∃ v : T ⟶ pair B S hS (fun _ : Unit => schemeSpace (C.siteDiagram.obj n))
        (fun _ => chartStageMap B S hS D hD U₀ f₀ C n) () (),
      v ≫ pairFst B S hS _ _ () () = x ∧ v ≫ pairSnd B S hS _ _ () () = y :=
  ⟨chartPairLift B S hS D hD C n x y h, chartPairLift_fst B S hS D hD C n x y h,
    chartPairLift_snd B S hS D hD C n x y h⟩

include hcoc in
omit [IsCofiltered I] in
/-- The cocycle condition for the transition morphism given by the pair morphisms. -/
theorem pairDatum_cocycle (T : AlgebraicSpaces B S hS)
    (vi vj vk : T ⟶ schemeSpace (C.siteDiagram.obj n))
    (vij vjk vik : T ⟶ pair B S hS (fun _ : Unit => schemeSpace (C.siteDiagram.obj n))
      (fun _ => chartStageMap B S hS D hD U₀ f₀ C n) () ())
    (hij₀ : vij ≫ pairFst B S hS _ _ () () = vi) (hij₁ : vij ≫ pairSnd B S hS _ _ () () = vj)
    (hjk₀ : vjk ≫ pairFst B S hS _ _ () () = vj) (hjk₁ : vjk ≫ pairSnd B S hS _ _ () () = vk)
    (hik₀ : vik ≫ pairFst B S hS _ _ () () = vi) (hik₁ : vik ≫ pairSnd B S hS _ _ () () = vk) :
    moduleHomRestrict₂ _ _ vij _ _ vi vj hij₀ hij₁
        (homConjL _ _ (uu ≫ u) (uu ≫ u) (pairMorphismAt B S hS D hD C m u ψ n uu huu _ _
          (chartPair_condition' B S hS D hD C n))) ≫
      moduleHomRestrict₂ _ _ vjk _ _ vj vk hjk₀ hjk₁
        (homConjL _ _ (uu ≫ u) (uu ≫ u) (pairMorphismAt B S hS D hD C m u ψ n uu huu _ _
          (chartPair_condition' B S hS D hD C n))) =
      moduleHomRestrict₂ _ _ vik _ _ vi vk hik₀ hik₁
        (homConjL _ _ (uu ≫ u) (uu ≫ u) (pairMorphismAt B S hS D hD C m u ψ n uu huu _ _
          (chartPair_condition' B S hS D hD C n))) := by
  have hc : ∀ (v : T ⟶ pair B S hS (fun _ : Unit => schemeSpace (C.siteDiagram.obj n))
      (fun _ => chartStageMap B S hS D hD U₀ f₀ C n) () ()) (x y : T ⟶ _)
      (hx : v ≫ pairFst B S hS _ _ () () = x) (hy : v ≫ pairSnd B S hS _ _ () () = y),
      x ≫ chartStageMap B S hS D hD U₀ f₀ C n = y ≫ chartStageMap B S hS D hD U₀ f₀ C n :=
    fun v x y hx hy => by rw [← hx, ← hy, Category.assoc, Category.assoc,
      chartPair_condition' B S hS D hD C n]
  rw [moduleHomRestrict₂_homConjL_pairMorphismAt B S hS D hD C m u ψ n uu huu vij vi vj hij₀ hij₁
      (hc _ _ _ hij₀ hij₁),
    moduleHomRestrict₂_homConjL_pairMorphismAt B S hS D hD C m u ψ n uu huu vjk vj vk hjk₀ hjk₁
      (hc _ _ _ hjk₀ hjk₁),
    moduleHomRestrict₂_homConjL_pairMorphismAt B S hS D hD C m u ψ n uu huu vik vi vk hik₀ hik₁
      (hc _ _ _ hik₀ hik₁), ← homConjL_comp, hcoc]

include hcoc hid in
omit [IsCofiltered I] in
/-- **The module descended from the pair morphisms.** -/
theorem exists_descended_module_aux
    (hG : ((modulePullback B S hS (uu ≫ u)).obj G).IsFinitePresentationOnSite)
    (hcov : IsEtaleCovering B S hS (fun _ : Unit => (schemeSpace (C.siteDiagram.obj n)).1)
      (fun _ => (chartStageMap B S hS D hD U₀ f₀ C n).hom))
    (hsurj : IsSurjective B S hS (chartStageMap B S hS D hD U₀ f₀ C n).hom) :
    ∃ (Q : Modules.{u, u} B S hS (stageAlgebraicSpace B S hS D hD n.left).1
        (stageAlgebraicSpace B S hS D hD n.left).2) (_ : Q.IsFinitePresentationOnSite)
      (α : (modulePullback B S hS (uu ≫ u)).obj G ≅
        (modulePullback B S hS (chartStageMap B S hS D hD U₀ f₀ C n)).obj Q),
      (modulePullback B S hS (pairFst B S hS (fun _ : Unit => schemeSpace (C.siteDiagram.obj n))
          (fun _ => chartStageMap B S hS D hD U₀ f₀ C n) () ())).map α.hom ≫
          (canonicalComparison (pairFst B S hS (fun _ : Unit => schemeSpace (C.siteDiagram.obj n))
            (fun _ => chartStageMap B S hS D hD U₀ f₀ C n) () ())
            (pairSnd B S hS (fun _ : Unit => schemeSpace (C.siteDiagram.obj n))
              (fun _ => chartStageMap B S hS D hD U₀ f₀ C n) () ())
            (chartStageMap B S hS D hD U₀ f₀ C n) (chartStageMap B S hS D hD U₀ f₀ C n)
            (pair_condition B S hS (fun _ : Unit => schemeSpace (C.siteDiagram.obj n))
              (fun _ => chartStageMap B S hS D hD U₀ f₀ C n) () ()) Q).hom =
        homConjL _ _ (uu ≫ u) (uu ≫ u) (pairMorphismAt B S hS D hD C m u ψ n uu huu _ _
          (chartPair_condition' B S hS D hD C n)) ≫ (modulePullback B S hS
            (pairSnd B S hS (fun _ : Unit => schemeSpace (C.siteDiagram.obj n))
              (fun _ => chartStageMap B S hS D hD U₀ f₀ C n) () ())).map α.hom :=
  exists_descent_of_isEtale B S hS
    (chartStageMap B S hS D hD U₀ f₀ C n) (hcov.etale ()) hcov hsurj hG
    (homConjL _ _ (uu ≫ u) (uu ≫ u) (pairMorphismAt B S hS D hD C m u ψ n uu huu _ _
      (chartPair_condition' B S hS D hD C n)))
    (homConjL _ _ (uu ≫ u) (uu ≫ u) (pairMorphismAt B S hS D hD C m u ψ n uu huu _ _
      (chartPair_condition' B S hS D hD C n).symm))
    (homConjL_comp_homConjL_eq_id _ _ _ _ _
      (pairMorphismAt_comp_eq_id B S hS D hD C m u ψ n uu huu hcoc hid _ _ _ _))
    (homConjL_comp_homConjL_eq_id _ _ _ _ _
      (pairMorphismAt_comp_eq_id B S hS D hD C m u ψ n uu huu hcoc hid _ _ _ _))
    (pairDatum_cocycle B S hS D hD C m u ψ n uu huu hcoc)

omit [IsCofiltered I] in
/-- **The twisted comparisons of the descended module are the pair morphisms.** -/
theorem twistedComparison_descended
    {Q : Modules.{u, u} B S hS (stageAlgebraicSpace B S hS D hD n.left).1
        (stageAlgebraicSpace B S hS D hD n.left).2}
    (α : (modulePullback B S hS (uu ≫ u)).obj G ≅
        (modulePullback B S hS (chartStageMap B S hS D hD U₀ f₀ C n)).obj Q)
    (hα : (modulePullback B S hS (pairFst B S hS (fun _ : Unit => schemeSpace (C.siteDiagram.obj n))
          (fun _ => chartStageMap B S hS D hD U₀ f₀ C n) () ())).map α.hom ≫
          (canonicalComparison (pairFst B S hS (fun _ : Unit => schemeSpace (C.siteDiagram.obj n))
            (fun _ => chartStageMap B S hS D hD U₀ f₀ C n) () ())
            (pairSnd B S hS (fun _ : Unit => schemeSpace (C.siteDiagram.obj n))
              (fun _ => chartStageMap B S hS D hD U₀ f₀ C n) () ())
            (chartStageMap B S hS D hD U₀ f₀ C n) (chartStageMap B S hS D hD U₀ f₀ C n)
            (pair_condition B S hS (fun _ : Unit => schemeSpace (C.siteDiagram.obj n))
              (fun _ => chartStageMap B S hS D hD U₀ f₀ C n) () ()) Q).hom =
        homConjL _ _ (uu ≫ u) (uu ≫ u) (pairMorphismAt B S hS D hD C m u ψ n uu huu _ _
          (chartPair_condition' B S hS D hD C n)) ≫ (modulePullback B S hS
            (pairSnd B S hS (fun _ : Unit => schemeSpace (C.siteDiagram.obj n))
              (fun _ => chartStageMap B S hS D hD U₀ f₀ C n) () ())).map α.hom)
    (T : AlgebraicSpaces B S hS) (x y : T ⟶ schemeSpace (C.siteDiagram.obj n))
    (h : x ≫ chartStageMap B S hS D hD U₀ f₀ C n = y ≫ chartStageMap B S hS D hD U₀ f₀ C n)
    (t : T ⟶ stageAlgebraicSpace B S hS D hD n.left)
    (ht : x ≫ chartStageMap B S hS D hD U₀ f₀ C n = t)
    (vx vy : T ⟶ V) (hvx : x ≫ uu ≫ u = vx) (hvy : y ≫ uu ≫ u = vy) :
    twistedComparison (chartStageMap B S hS D hD U₀ f₀ C n) (uu ≫ u) α.symm x y t vx vy ht
        (h.symm.trans ht) hvx hvy =
      pairMorphism B S hS D hD C m u ψ (x ≫ uu) (y ≫ uu) (huu T x y h) vx vy
        (by rw [Category.assoc, hvx]) (by rw [Category.assoc, hvy]) := by
  have hpair := twistedComparison_eq_of_naturality B S hS (chartStageMap B S hS D hD U₀ f₀ C n)
    (uu ≫ u) α _ _ (pair_condition B S hS (fun _ : Unit => schemeSpace (C.siteDiagram.obj n))
      (fun _ => chartStageMap B S hS D hD U₀ f₀ C n) () ()) _ hα
  rw [homConjLInv_homConjL] at hpair
  obtain ⟨v, hv₁, hv₂⟩ := exists_lift_pair B S hS D hD C n x y h
  have e₁ := moduleHomRestrict₂_twistedComparison _ _ α.symm v _ _ _ _ _ rfl
    (pair_condition B S hS (fun _ : Unit => schemeSpace (C.siteDiagram.obj n))
      (fun _ => chartStageMap B S hS D hD U₀ f₀ C n) () ()).symm rfl rfl x y t vx vy hv₁ hv₂
    (by rw [← Category.assoc, hv₁, ht]) (by rw [← Category.assoc, hv₁, hvx])
    (by rw [← Category.assoc, hv₂, hvy]) ht (h.symm.trans ht) hvx hvy
  rw [hpair] at e₁
  exact e₁.symm.trans (moduleHomRestrict₂_pairMorphism B S hS D hD C m u ψ v _ _ _ _ _ _ _
    (x ≫ uu) (y ≫ uu) (by rw [← Category.assoc, hv₁]) (by rw [← Category.assoc, hv₂]) _ vx vy
    (by rw [← Category.assoc, hv₁, hvx]) (by rw [← Category.assoc, hv₂, hvy]) _ _)

end At

end PairMorphism

end AlgebraicGeometry.Space

end
