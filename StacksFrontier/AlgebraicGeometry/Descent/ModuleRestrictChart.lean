module

public import StacksFrontier.AlgebraicGeometry.Descent.ModuleRestrictPushforward
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.RestrictPullbackCoherence

/-!
# The chart comparison of `RestrictIsoGlueData`, read by restrictions

`AlgebraicGeometry.RestrictIsoGlueData` asks, for charts `a : A ⟶ S` and `b : B ⟶ S` and an open
`V` of `S` inside both ranges, for an isomorphism `a_* M |_V ≅ b_* N |_V`, compatible with
shrinking `V` and satisfying the cocycle condition on triple overlaps.
`StacksFrontier/AlgebraicGeometry/Descent/ModuleRestrictPushforward.lean` reduces the datum itself to
an isomorphism of the *inverse images* of `M` and `N` along the factorisations
`AlgebraicGeometry.openLift` of `V` through the two charts.  The two compatibilities, however, are
not visible on the inverse image: `AlgebraicGeometry.Scheme.Modules.pullback` is defined by a
left-adjoint construction and computes nothing, whereas
`AlgebraicGeometry.Scheme.Modules.restrictFunctor` -- the restriction along an open immersion,
isomorphic to the inverse image -- has sections over `U` *equal* to the sections of the module
over the image of `U`, and every comparison isomorphism between restrictions along equal or
composite open immersions has for components a restriction map of the module along an `eqToHom`.

This file therefore repeats the reduction with `restrictFunctor` in place of `pullback`, and
proves the two compatibilities there.  Everything rests on one associativity identity,
`AlgebraicGeometry.restrictCompIso_assoc`, which is proved by comparing components: both sides are
composites of restriction maps of one module with the same source and target, and the homs of a
poset are unique.

## Main definitions

* `AlgebraicGeometry.restrictCompIso`: the restriction along a composite of open immersions is the
  iterated restriction.
* `AlgebraicGeometry.restrictChartIso`: from an identification `σ` of the restriction of `M` along
  `p` with `M'`, the identification of the restriction of `M` along `c ≫ p` with the restriction
  of `M'` along `c`.
* `AlgebraicGeometry.openLiftRestrictIso`: **the chart comparison** `a_* M |_V ≅ M|_{openLift}`.
* `AlgebraicGeometry.restrictPushforwardIsoOfRestrictIso`: **the comparison of two charts over a
  common open**, from a comparison of the restrictions along the factorisations -- the shape the
  `iso` field of `AlgebraicGeometry.RestrictIsoGlueData` asks for.
* `AlgebraicGeometry.openLiftShrinkIso`: the comparison of the restrictions along the
  factorisations, shrunk to a smaller open.

## Main results

* `AlgebraicGeometry.restrictCompIso_assoc`: the associativity coherence of
  `AlgebraicGeometry.restrictCompIso`.
* `AlgebraicGeometry.restrictChartIso_shrink`: **`restrictChartIso` is compatible with
  precomposition** of the second leg.
* `AlgebraicGeometry.restrictChartIso_trans`: **`restrictChartIso` is pseudo-functorial** in the
  first leg.
* `AlgebraicGeometry.restrictLocal_restrictPushforwardIsoOfRestrictIso`: **the `iso_restrict`
  field**: the chart comparison of a comparison of restrictions is compatible with shrinking the
  open, the shrunk comparison being `AlgebraicGeometry.openLiftShrinkIso`.
* `AlgebraicGeometry.restrictMiddleIso`, `AlgebraicGeometry.restrictMiddleIso_trans` and
  `AlgebraicGeometry.restrictMiddleIso_refine`: a comparison given through a middle chart, its
  independence of the middle chart, and the resulting cocycle condition.
* `AlgebraicGeometry.openLiftShrinkIso_restrictMiddleIso`: such a comparison, shrunk, is the
  comparison through the middle chart over the smaller open.
* `AlgebraicGeometry.restrictPushforwardIsoOfRestrictIso_trans`: **the `iso_trans` field**: the
  chart comparisons compose as the comparisons of restrictions do.
* `AlgebraicGeometry.restrictChartIso_pullback_trans`: **`restrictChartIso` is pseudo-functorial
  for an identification given on the inverse images**, the hypothesis being the cocycle
  condition read on the inverse images.

## References

* [Stacks Project, Tag 00AM](https://stacks.math.columbia.edu/tag/00AM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-! ### The factorisation of an open through a chart is an open immersion -/

/-- The factorisation `AlgebraicGeometry.openLift a hV` of an open `V` contained in the range of
an open immersion `a` is an open immersion. -/
instance isOpenImmersion_openLift {S A : Scheme.{u}} (a : A ⟶ S) [IsOpenImmersion a]
    {V : S.Opens} (hV : V ≤ a.opensRange) : IsOpenImmersion (openLift a hV) :=
  inferInstanceAs (IsOpenImmersion (IsOpenImmersion.lift a V.ι _))

/-- **The factorisation of a smaller open is the factorisation of the larger one, preceded by the
inclusion.**  This is `AlgebraicGeometry.eq_openLift` at the inclusion of a smaller open. -/
theorem homOfLE_openLift {S A : Scheme.{u}} (a : A ⟶ S) [IsOpenImmersion a]
    {V V' : S.Opens} (hV : V ≤ a.opensRange) (hV' : V' ≤ V) :
    S.homOfLE hV' ≫ openLift a hV = openLift a (hV'.trans hV) :=
  eq_openLift a _ _ (by rw [Category.assoc, openLift_comp, Scheme.homOfLE_ι])

/-! ### Restriction along a composite -/

/-- The component of the counit of the restriction--direct image adjunction is a restriction map
of the module. -/
theorem restrictFunctorAdjCounitIso_hom_app_app {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (M : X.Modules) (U : X.Opens) :
    ((Scheme.Modules.restrictFunctorAdjCounitIso f).hom.app M).app U =
      M.presheaf.map (eqToHom (f.preimage_image_eq U).symm).op := rfl

/-- **The restriction along a composite of open immersions is the iterated restriction.** -/
def restrictCompIso {T' T Q : Scheme.{u}} (g : T' ⟶ T) (h : T ⟶ Q) [IsOpenImmersion g]
    [IsOpenImmersion h] {k : T' ⟶ Q} (hk : g ≫ h = k) [IsOpenImmersion k] (M : Q.Modules) :
    Scheme.Modules.restrict M k ≅
      (Scheme.Modules.restrictFunctor g).obj (Scheme.Modules.restrict M h) :=
  ((Scheme.Modules.restrictFunctorCongr hk).app M).symm ≪≫
    (Scheme.Modules.restrictFunctorComp g h).app M

/-- `AlgebraicGeometry.restrictCompIso` is natural in the module. -/
theorem restrictCompIso_naturality {T' T Q : Scheme.{u}} (g : T' ⟶ T) (h : T ⟶ Q)
    [IsOpenImmersion g] [IsOpenImmersion h] {k : T' ⟶ Q} (hk : g ≫ h = k) [IsOpenImmersion k]
    {M N : Q.Modules} (φ : M ⟶ N) :
    (Scheme.Modules.restrictFunctor k).map φ ≫ (restrictCompIso g h hk N).hom =
      (restrictCompIso g h hk M).hom ≫
        (Scheme.Modules.restrictFunctor g).map ((Scheme.Modules.restrictFunctor h).map φ) := by
  have h1 := (Scheme.Modules.restrictFunctorCongr hk).inv.naturality φ
  have h2 := (Scheme.Modules.restrictFunctorComp g h).hom.naturality φ
  simp only [restrictCompIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv]
  rw [← Category.assoc, h1, Category.assoc, h2]
  rfl

/-- Two composites of four restriction maps of a module with the same source and target agree. -/
private theorem presheaf_map_comp₄ {X : Scheme.{u}} (M : X.Modules)
    {P₀ P₁ P₂ P₃ P₄ Q₁ Q₂ Q₃ : (X.Opens)ᵒᵖ} (h₁ : P₀ ⟶ P₁) (h₂ : P₁ ⟶ P₂)
    (h₃ : P₂ ⟶ P₃) (h₄ : P₃ ⟶ P₄) (k₁ : P₀ ⟶ Q₁) (k₂ : Q₁ ⟶ Q₂)
    (k₃ : Q₂ ⟶ Q₃) (k₄ : Q₃ ⟶ P₄) :
    M.presheaf.map h₁ ≫ M.presheaf.map h₂ ≫ M.presheaf.map h₃ ≫ M.presheaf.map h₄ =
      (M.presheaf.map k₁ ≫ M.presheaf.map k₂) ≫ M.presheaf.map k₃ ≫ M.presheaf.map k₄ := by
  simp only [← Functor.map_comp, ← Category.assoc]
  exact presheaf_map_eq M _ _

/-- **The associativity coherence of `AlgebraicGeometry.restrictCompIso`**:  restricting along
`g ≫ c ≫ p` by first splitting off `p` and then `c` is restricting by first splitting off `c ≫ p`
and then `c`.  Both sides have for components a composite of restriction maps of `M` with the
same source and target. -/
theorem restrictCompIso_assoc {T' T P' P : Scheme.{u}} (g : T' ⟶ T) (c : T ⟶ P') (p : P' ⟶ P)
    [IsOpenImmersion g] [IsOpenImmersion c] [IsOpenImmersion p] {k : T ⟶ P} (hk : c ≫ p = k)
    [IsOpenImmersion k] {k' : T' ⟶ P} (hk' : g ≫ k = k') [IsOpenImmersion k']
    {c' : T' ⟶ P'} (hc : g ≫ c = c') [IsOpenImmersion c'] (M : P.Modules) :
    (restrictCompIso g k hk' M).hom ≫
        (Scheme.Modules.restrictFunctor g).map (restrictCompIso c p hk M).hom =
      (restrictCompIso c' p (by rw [← hc, Category.assoc, hk, hk']) M).hom ≫
        (restrictCompIso g c hc (Scheme.Modules.restrict M p)).hom := by
  refine Scheme.Modules.hom_ext _ _ fun U ↦ ?_
  simp only [restrictCompIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Scheme.Modules.Hom.comp_app, restrictFunctor_map_app,
    Scheme.Modules.restrictFunctorCongr_inv_app_app,
    Scheme.Modules.restrictFunctorComp_hom_app_app]
  exact presheaf_map_comp₄ M _ _ _ _ _ _ _ _

/-- **`AlgebraicGeometry.restrictLocal` is conjugation by `AlgebraicGeometry.restrictCompIso`.**
This is the definition of `restrictLocal` read through `restrictCompIso`. -/
theorem restrictLocal_eq {S : Scheme.{u}} {A B : S.Modules} {V W : S.Opens}
    (φ : Scheme.Modules.restrict A W.ι ⟶ Scheme.Modules.restrict B W.ι) (hV : V ≤ W) :
    restrictLocal φ hV =
      (restrictCompIso (S.homOfLE hV) W.ι (Scheme.homOfLE_ι S hV) A).hom ≫
        (Scheme.Modules.restrictFunctor (S.homOfLE hV)).map φ ≫
          (restrictCompIso (S.homOfLE hV) W.ι (Scheme.homOfLE_ι S hV) B).inv :=
  rfl

/-! ### The chart comparison -/

/-- **The restriction of `M` along `c ≫ p` is the restriction along `c` of `M'`**, for an
identification `σ` of the restriction of `M` along `p` with `M'`. -/
def restrictChartIso {T P' P : Scheme.{u}} (p : P' ⟶ P) [IsOpenImmersion p] {M : P.Modules}
    {M' : P'.Modules} (σ : Scheme.Modules.restrict M p ≅ M') (c : T ⟶ P') [IsOpenImmersion c]
    {k : T ⟶ P} (hk : c ≫ p = k) [IsOpenImmersion k] :
    Scheme.Modules.restrict M k ≅ Scheme.Modules.restrict M' c :=
  restrictCompIso c p hk M ≪≫ (Scheme.Modules.restrictFunctor c).mapIso σ

/-- **`AlgebraicGeometry.restrictChartIso` is compatible with precomposing the second leg.** -/
theorem restrictChartIso_shrink {T' T P' P : Scheme.{u}} (p : P' ⟶ P)
    [IsOpenImmersion p] {M : P.Modules} {M' : P'.Modules}
    (σ : Scheme.Modules.restrict M p ≅ M') (c : T ⟶ P') [IsOpenImmersion c] {k : T ⟶ P}
    (hk : c ≫ p = k) [IsOpenImmersion k] (g : T' ⟶ T) [IsOpenImmersion g] {k' : T' ⟶ P}
    (hk' : g ≫ k = k') [IsOpenImmersion k'] {c' : T' ⟶ P'} (hc : g ≫ c = c')
    [IsOpenImmersion c'] :
    restrictCompIso g k hk' M ≪≫
        (Scheme.Modules.restrictFunctor g).mapIso (restrictChartIso p σ c hk) =
      restrictChartIso p σ c' (by rw [← hc, Category.assoc, hk, hk']) ≪≫
        restrictCompIso g c hc M' := by
  refine Iso.ext ?_
  simp only [restrictChartIso, Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp,
    Category.assoc]
  rw [← Category.assoc (restrictCompIso g k hk' M).hom,
    restrictCompIso_assoc g c p hk hk' hc M, restrictCompIso_naturality g c hc σ.hom,
    Category.assoc]

/-- **`AlgebraicGeometry.restrictChartIso` is pseudo-functorial in the first leg.** -/
theorem restrictChartIso_trans {T P'' P' P : Scheme.{u}} (p : P' ⟶ P) (p' : P'' ⟶ P')
    [IsOpenImmersion p] [IsOpenImmersion p'] {p'' : P'' ⟶ P} (hp : p' ≫ p = p'')
    [IsOpenImmersion p''] {M : P.Modules} {M' : P'.Modules}
    {M'' : P''.Modules} (σ : Scheme.Modules.restrict M p ≅ M')
    (σ' : Scheme.Modules.restrict M' p' ≅ M'') (c : T ⟶ P'') [IsOpenImmersion c] {k : T ⟶ P}
    (hk : c ≫ p'' = k) [IsOpenImmersion k] {c' : T ⟶ P'} (hc : c ≫ p' = c')
    [IsOpenImmersion c'] :
    restrictChartIso p'' (restrictChartIso p σ p' hp ≪≫ σ') c hk =
      restrictChartIso p σ c' (by rw [← hc, Category.assoc, hp, hk]) ≪≫
        restrictChartIso p' σ' c hc := by
  refine Iso.ext ?_
  simp only [restrictChartIso, Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp,
    Category.assoc]
  rw [← Category.assoc (restrictCompIso c p'' hk M).hom,
    restrictCompIso_assoc c p' p hp hk hc M, Category.assoc,
    ← Category.assoc (restrictCompIso c p' hc (Scheme.Modules.restrict M p)).hom,
    ← restrictCompIso_naturality c p' hc σ.hom, Category.assoc]

/-! ### The comparison of two charts over a common open -/

/-- Conjugating a comparison `e` by two isomorphisms that commute with a functor `F` up to
natural comparisons `sA`, `sB`, `sA'`, `sB'`. -/
private theorem comp_mapIso_comp_symm_eq {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A A₁ B B₁ : C} {P P' Q Q' : D} (sA : P ≅ F.obj A) (sB : P' ≅ F.obj B)
    (sA' : Q ≅ F.obj A₁) (sB' : Q' ≅ F.obj B₁) (ra : A ≅ A₁) (rb : B ≅ B₁) (ra' : P ≅ Q)
    (rb' : P' ≅ Q') (e : A₁ ≅ B₁) (hA : sA ≪≫ F.mapIso ra = ra' ≪≫ sA')
    (hB : sB ≪≫ F.mapIso rb = rb' ≪≫ sB') :
    sA ≪≫ F.mapIso (ra ≪≫ e ≪≫ rb.symm) ≪≫ sB.symm =
      ra' ≪≫ (sA' ≪≫ F.mapIso e ≪≫ sB'.symm) ≪≫ rb'.symm := by
  have hB' := congrArg Iso.hom (congrArg Iso.symm hB)
  have hA' := congrArg Iso.hom hA
  refine Iso.ext ?_
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_symm, Functor.mapIso_hom, Functor.mapIso_inv,
    Functor.map_comp, Category.assoc] at hA' hB' ⊢
  rw [hB', ← Category.assoc sA.hom, hA', Category.assoc]

section Charts

variable {S A B C : Scheme.{u}} (a : A ⟶ S) (b : B ⟶ S) (c : C ⟶ S) [IsOpenImmersion a]
  [IsOpenImmersion b] [IsOpenImmersion c] (M : A.Modules) (N : B.Modules) (P : C.Modules)

/-- **The chart comparison at an open inside the range of an open immersion**, in the restriction
world:  over an open `V` of `S` contained in the range of `a`, the restriction of the direct image
`a_* M` is the restriction of `M` along the factorisation `AlgebraicGeometry.openLift` of `V`. -/
def openLiftRestrictIso {V : S.Opens} (hV : V ≤ a.opensRange) :
    Scheme.Modules.restrict ((Scheme.Modules.pushforward a).obj M) V.ι ≅
      Scheme.Modules.restrict M (openLift a hV) :=
  restrictChartIso a ((Scheme.Modules.restrictFunctorAdjCounitIso a).app M) (openLift a hV)
    (openLift_comp a hV)

/-- **The chart comparison is compatible with shrinking the open.** -/
theorem openLiftRestrictIso_shrink {V V' : S.Opens} (hV : V ≤ a.opensRange) (hV' : V' ≤ V) :
    restrictCompIso (S.homOfLE hV') V.ι (Scheme.homOfLE_ι S hV')
          ((Scheme.Modules.pushforward a).obj M) ≪≫
        (Scheme.Modules.restrictFunctor (S.homOfLE hV')).mapIso (openLiftRestrictIso a M hV) =
      openLiftRestrictIso a M (hV'.trans hV) ≪≫
        restrictCompIso (S.homOfLE hV') (openLift a hV) (homOfLE_openLift a hV hV') M :=
  restrictChartIso_shrink a ((Scheme.Modules.restrictFunctorAdjCounitIso a).app M)
    (openLift a hV) (openLift_comp a hV) (S.homOfLE hV') (Scheme.homOfLE_ι S hV')
    (homOfLE_openLift a hV hV')

/-- **The comparison of two charts over a common open, from a comparison of the restrictions
along the factorisations.**  This is the exact shape of the `iso` field of
`AlgebraicGeometry.RestrictIsoGlueData`. -/
def restrictPushforwardIsoOfRestrictIso {V : S.Opens} (ha : V ≤ a.opensRange)
    (hb : V ≤ b.opensRange)
    (e : Scheme.Modules.restrict M (openLift a ha) ≅ Scheme.Modules.restrict N (openLift b hb)) :
    Scheme.Modules.restrict ((Scheme.Modules.pushforward a).obj M) V.ι ≅
      Scheme.Modules.restrict ((Scheme.Modules.pushforward b).obj N) V.ι :=
  openLiftRestrictIso a M ha ≪≫ e ≪≫ (openLiftRestrictIso b N hb).symm

/-- **A comparison of the restrictions along the factorisations, shrunk to a smaller open.**  The
two factorisations of the smaller open are the two factorisations of the larger one preceded by
the inclusion (`AlgebraicGeometry.homOfLE_openLift`), so the comparison over the smaller open is
the restriction of the comparison over the larger one. -/
def openLiftShrinkIso {V V' : S.Opens} (ha : V ≤ a.opensRange) (hb : V ≤ b.opensRange)
    (hV' : V' ≤ V)
    (e : Scheme.Modules.restrict M (openLift a ha) ≅ Scheme.Modules.restrict N (openLift b hb)) :
    Scheme.Modules.restrict M (openLift a (hV'.trans ha)) ≅
      Scheme.Modules.restrict N (openLift b (hV'.trans hb)) :=
  restrictCompIso (S.homOfLE hV') (openLift a ha) (homOfLE_openLift a ha hV') M ≪≫
    (Scheme.Modules.restrictFunctor (S.homOfLE hV')).mapIso e ≪≫
      (restrictCompIso (S.homOfLE hV') (openLift b hb) (homOfLE_openLift b hb hV') N).symm

/-- **The `iso_restrict` field of `AlgebraicGeometry.RestrictIsoGlueData`** for the chart
comparison of a comparison of restrictions:  restricting the comparison over `V` to a smaller
open `V'` gives the chart comparison of `AlgebraicGeometry.openLiftShrinkIso`. -/
theorem restrictLocal_restrictPushforwardIsoOfRestrictIso {V V' : S.Opens}
    (ha : V ≤ a.opensRange) (hb : V ≤ b.opensRange) (hV' : V' ≤ V)
    (e : Scheme.Modules.restrict M (openLift a ha) ≅ Scheme.Modules.restrict N (openLift b hb)) :
    restrictLocal (restrictPushforwardIsoOfRestrictIso a b M N ha hb e).hom hV' =
      (restrictPushforwardIsoOfRestrictIso a b M N (hV'.trans ha) (hV'.trans hb)
        (openLiftShrinkIso a b M N ha hb hV' e)).hom := by
  rw [restrictLocal_eq]
  exact congrArg Iso.hom (comp_mapIso_comp_symm_eq _ _ _ _ _ _ _ _ _ e
    (openLiftRestrictIso_shrink a M ha hV') (openLiftRestrictIso_shrink b N hb hV'))

/-- **The `iso_trans` field of `AlgebraicGeometry.RestrictIsoGlueData`** for the chart comparison
of a comparison of restrictions:  the chart comparisons compose as the comparisons of the
restrictions do, the comparison with the middle chart cancelling. -/
theorem restrictPushforwardIsoOfRestrictIso_trans {V : S.Opens} (ha : V ≤ a.opensRange)
    (hb : V ≤ b.opensRange) (hc : V ≤ c.opensRange)
    (e : Scheme.Modules.restrict M (openLift a ha) ≅ Scheme.Modules.restrict N (openLift b hb))
    (e' : Scheme.Modules.restrict N (openLift b hb) ≅ Scheme.Modules.restrict P (openLift c hc)) :
    (restrictPushforwardIsoOfRestrictIso a b M N ha hb e).hom ≫
        (restrictPushforwardIsoOfRestrictIso b c N P hb hc e').hom =
      (restrictPushforwardIsoOfRestrictIso a c M P ha hc (e ≪≫ e')).hom := by
  simp only [restrictPushforwardIsoOfRestrictIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc]

/-! ### The comparison through a middle chart -/

/-- **The comparison of two charts through a third chart contained in both.**  `t` is a chart
factoring through `a` and through `b`, carrying a module `L`, and the restrictions of `M` and of
`N` along the two factorisations are both identified with `L`; over an open `V` inside the range
of `t` the two restrictions of `M` and `N` along the factorisations of `V` are then identified
through `L`. -/
def restrictMiddleIso {S A B T : Scheme.{u}} (a : A ⟶ S) (b : B ⟶ S) (t : T ⟶ S)
    [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion t] {pa : T ⟶ A} {pb : T ⟶ B}
    (hpa : pa ≫ a = t) (hpb : pb ≫ b = t) [IsOpenImmersion pa] [IsOpenImmersion pb]
    {M : A.Modules} {N : B.Modules} {L : T.Modules}
    (σa : Scheme.Modules.restrict M pa ≅ L) (σb : Scheme.Modules.restrict N pb ≅ L)
    {V : S.Opens} (hV : V ≤ t.opensRange) (ha : V ≤ a.opensRange) (hb : V ≤ b.opensRange) :
    Scheme.Modules.restrict M (openLift a ha) ≅ Scheme.Modules.restrict N (openLift b hb) :=
  restrictChartIso pa σa (openLift t hV) (openLift_comp_eq a hpa hV) ≪≫
    (restrictChartIso pb σb (openLift t hV) (openLift_comp_eq b hpb hV)).symm

/-- **The comparison through a middle chart, shrunk to a smaller open, is the comparison through
the middle chart over that open.** -/
theorem openLiftShrinkIso_restrictMiddleIso {S A B T : Scheme.{u}} (a : A ⟶ S) (b : B ⟶ S)
    (t : T ⟶ S) [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion t] {pa : T ⟶ A}
    {pb : T ⟶ B} (hpa : pa ≫ a = t) (hpb : pb ≫ b = t) [IsOpenImmersion pa]
    [IsOpenImmersion pb] {M : A.Modules} {N : B.Modules} {L : T.Modules}
    (σa : Scheme.Modules.restrict M pa ≅ L) (σb : Scheme.Modules.restrict N pb ≅ L)
    {V V' : S.Opens} (hV : V ≤ t.opensRange) (ha : V ≤ a.opensRange) (hb : V ≤ b.opensRange)
    (hV' : V' ≤ V) :
    openLiftShrinkIso a b M N ha hb hV' (restrictMiddleIso a b t hpa hpb σa σb hV ha hb) =
      restrictMiddleIso a b t hpa hpb σa σb (hV'.trans hV) (hV'.trans ha) (hV'.trans hb) := by
  have := comp_mapIso_comp_symm_eq _ _ _ _ _ _ _ _ _ (Iso.refl _)
    (restrictChartIso_shrink pa σa (openLift t hV) (openLift_comp_eq a hpa hV) (S.homOfLE hV')
      (homOfLE_openLift a ha hV') (homOfLE_openLift t hV hV'))
    (restrictChartIso_shrink pb σb (openLift t hV) (openLift_comp_eq b hpb hV) (S.homOfLE hV')
      (homOfLE_openLift b hb hV') (homOfLE_openLift t hV hV'))
  simpa [openLiftShrinkIso, restrictMiddleIso] using this

/-- **Three comparisons through one common middle chart satisfy the cocycle condition**, the
identification with the module on the middle chart cancelling. -/
theorem restrictMiddleIso_trans {S A B C T : Scheme.{u}} (a : A ⟶ S) (b : B ⟶ S) (c : C ⟶ S)
    (t : T ⟶ S) [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion c]
    [IsOpenImmersion t] {qa : T ⟶ A} {qb : T ⟶ B} {qc : T ⟶ C} (hqa : qa ≫ a = t)
    (hqb : qb ≫ b = t) (hqc : qc ≫ c = t) [IsOpenImmersion qa] [IsOpenImmersion qb]
    [IsOpenImmersion qc] {M : A.Modules} {N : B.Modules} {P : C.Modules} {L : T.Modules}
    (σa : Scheme.Modules.restrict M qa ≅ L) (σb : Scheme.Modules.restrict N qb ≅ L)
    (σc : Scheme.Modules.restrict P qc ≅ L) {V : S.Opens} (hV : V ≤ t.opensRange)
    (ha : V ≤ a.opensRange) (hb : V ≤ b.opensRange) (hc : V ≤ c.opensRange) :
    restrictMiddleIso a b t hqa hqb σa σb hV ha hb ≪≫
        restrictMiddleIso b c t hqb hqc σb σc hV hb hc =
      restrictMiddleIso a c t hqa hqc σa σc hV ha hc := by
  refine Iso.ext ?_
  simp only [restrictMiddleIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc]

/-- **The comparison through a middle chart does not depend on the middle chart**, as long as the
latter is small enough:  a chart `s` factoring through `t`, with its module identified with the
restriction of `L`, computes the same comparison. -/
theorem restrictMiddleIso_refine {S A B T T' : Scheme.{u}} (a : A ⟶ S) (b : B ⟶ S) (t : T ⟶ S)
    (s : T' ⟶ S) [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion t]
    [IsOpenImmersion s] {pa : T ⟶ A} {pb : T ⟶ B} (hpa : pa ≫ a = t) (hpb : pb ≫ b = t)
    [IsOpenImmersion pa] [IsOpenImmersion pb] {q : T' ⟶ T} (hq : q ≫ t = s)
    [IsOpenImmersion q] {qa : T' ⟶ A} {qb : T' ⟶ B} (hqa : q ≫ pa = qa)
    (hqb : q ≫ pb = qb) [IsOpenImmersion qa] [IsOpenImmersion qb]
    {M : A.Modules} {N : B.Modules} {L : T.Modules} {L' : T'.Modules}
    (σa : Scheme.Modules.restrict M pa ≅ L) (σb : Scheme.Modules.restrict N pb ≅ L)
    (τ : Scheme.Modules.restrict L q ≅ L')
    (σa' : Scheme.Modules.restrict M qa ≅ L') (σb' : Scheme.Modules.restrict N qb ≅ L')
    (ha' : restrictChartIso pa σa q hqa ≪≫ τ = σa')
    (hb' : restrictChartIso pb σb q hqb ≪≫ τ = σb')
    {V : S.Opens} (hV : V ≤ s.opensRange) (ha : V ≤ a.opensRange) (hb : V ≤ b.opensRange) :
    restrictMiddleIso a b s (show qa ≫ a = s by rw [← hqa, Category.assoc, hpa, hq])
        (show qb ≫ b = s by rw [← hqb, Category.assoc, hpb, hq]) σa' σb' hV ha hb =
      restrictMiddleIso a b t hpa hpb σa σb (hV.trans (opensRange_le_of_comp t hq)) ha hb := by
  have hA := restrictChartIso_trans pa q hqa σa τ (openLift s hV)
    (openLift_comp_eq a (show qa ≫ a = s by rw [← hqa, Category.assoc, hpa, hq]) hV)
    (openLift_comp_eq t hq hV)
  have hB := restrictChartIso_trans pb q hqb σb τ (openLift s hV)
    (openLift_comp_eq b (show qb ≫ b = s by rw [← hqb, Category.assoc, hpb, hq]) hV)
    (openLift_comp_eq t hq hV)
  rw [ha'] at hA
  rw [hb'] at hB
  rw [restrictMiddleIso, hA, hB, restrictMiddleIso]
  refine Iso.ext ?_
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]

end Charts

/-! ### The chart comparison of an identification of inverse images

A construction whose comparison isomorphisms are given on the *inverse images* meets
`AlgebraicGeometry.restrictChartIso` through
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`, and its cocycle condition is
naturally stated on the inverse images too.  The translation is
`Stacks.AlgebraicGeometry.ModuleLimits.restrictFunctorIsoPullback_hom_comp_of_eq`, the one
coherence relating an iterated restriction to an iterated inverse image.
-/

/-- **The inverse image along a composite of morphisms**, with the composite presented as a given
morphism. -/
def pullbackCompIsoOfEq {T' T Q : Scheme.{u}} (g : T' ⟶ T) (h : T ⟶ Q) {k : T' ⟶ Q}
    (hk : g ≫ h = k) (M : Q.Modules) :
    (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback h).obj M) ≅
      (Scheme.Modules.pullback k).obj M :=
  (Scheme.Modules.pullbackComp g h).app M ≪≫ (Scheme.Modules.pullbackCongr hk).app M

/-- **`AlgebraicGeometry.restrictChartIso` is pseudo-functorial for a comparison given on the
inverse images.**  The restriction of `M` along `a` is identified with `M'` and that of `M'`
along `b` with `M''` through comparisons `ρ`, `ρ'` of the inverse images; if those satisfy the
cocycle condition on the inverse image along the composite, then the two identifications of the
restriction of `M` along `b ≫ a` with `M''` -- the iterated one and the direct one `ρ''` --
agree. -/
theorem restrictChartIso_pullback_trans {Q P P' : Scheme.{u}} (a : P ⟶ Q) (b : P' ⟶ P)
    [IsOpenImmersion a] [IsOpenImmersion b] {k : P' ⟶ Q} (hk : b ≫ a = k) [IsOpenImmersion k]
    {M : Q.Modules} {M' : P.Modules} {M'' : P'.Modules}
    (ρ : (Scheme.Modules.pullback a).obj M ≅ M')
    (ρ' : (Scheme.Modules.pullback b).obj M' ≅ M'')
    (ρ'' : (Scheme.Modules.pullback k).obj M ≅ M'')
    (hρ : (pullbackCompIsoOfEq b a hk M).hom ≫ ρ''.hom =
      (Scheme.Modules.pullback b).map ρ.hom ≫ ρ'.hom) :
    restrictChartIso a ((Scheme.Modules.restrictFunctorIsoPullback a).app M ≪≫ ρ) b hk ≪≫
        ((Scheme.Modules.restrictFunctorIsoPullback b).app M' ≪≫ ρ') =
      (Scheme.Modules.restrictFunctorIsoPullback k).app M ≪≫ ρ'' := by
  have hcoh := NatTrans.congr_app
    (Stacks.AlgebraicGeometry.ModuleLimits.restrictFunctorIsoPullback_hom_comp_of_eq b a hk) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hcoh
  have hnat := (Scheme.Modules.restrictFunctorIsoPullback b).hom.naturality ρ.hom
  have key : (Scheme.Modules.restrictFunctor b).map
        ((Scheme.Modules.restrictFunctorIsoPullback a).hom.app M) ≫
      (Scheme.Modules.restrictFunctorIsoPullback b).hom.app
          ((Scheme.Modules.pullback a).obj M) ≫ (pullbackCompIsoOfEq b a hk M).hom =
      (restrictCompIso b a hk M).inv ≫
        (Scheme.Modules.restrictFunctorIsoPullback k).hom.app M := by
    rw [show (restrictCompIso b a hk M).inv =
        (Scheme.Modules.restrictFunctorComp b a).inv.app M ≫
          (Scheme.Modules.restrictFunctorCongr hk).hom.app M from rfl, pullbackCompIsoOfEq]
    simp only [Iso.trans_hom, Iso.app_hom, Category.assoc]
    exact hcoh.symm
  have key2 := congrArg (fun z => (restrictCompIso b a hk M).hom ≫ z ≫ ρ''.hom) key
  simp only [Category.assoc, Iso.hom_inv_id_assoc] at key2
  refine Iso.ext ?_
  simp only [restrictChartIso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Functor.map_comp,
    Category.assoc]
  rw [← Category.assoc ((Scheme.Modules.restrictFunctor b).map ρ.hom), hnat, Category.assoc,
    ← hρ]
  exact key2

end AlgebraicGeometry

end
