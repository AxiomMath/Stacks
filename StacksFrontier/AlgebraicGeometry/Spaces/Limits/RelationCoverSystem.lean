module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartSystemEtalePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartLimitEqualizerPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SeparatedRelationSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.EtaleRelationChart
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleFlatBaseChangeEqualizer
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleSectionsEvaluation
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSheafConditionOneElement
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae03KM

/-!
# An affine étale cover of the relation of an affine chart, at every stage

In the proof of Stacks 07SI one chooses an affine étale chart `U₀ ⟶ X₀` of the chosen stage of
a limit situation, surjective on points, and presents the global sections of a module on a
stage `Xᵢ` as the sections over `Uᵢ = Xᵢ ×_{X₀} U₀` equalized by the two restrictions to
`Rᵢ = Uᵢ ×_{Xᵢ} Uᵢ`.  The relation `R₀ = U₀ ×_{X₀} U₀` is a quasi-compact scheme, but it is
affine only when `X₀` is separated, which Situation 084R does not assume.

This file replaces `R₀` by an affine scheme `W₀` with an étale morphism onto `R₀` that is
surjective (Stacks 03H6, applied to the quasi-compact `R₀`).  The two projections of `R₀`
composed with `W₀ ⟶ R₀` are two morphisms `W₀ ⟶ U₀` over `X₀`, and at every stage the chart
system of `W₀` covers the relation `Rᵢ`: the induced map `Wᵢ ⟶ Rᵢ` is the base change of
`W₀ ⟶ R₀` along `Rᵢ ⟶ R₀`, hence surjective on points by Stacks 03MH.  So a section over `Uᵢ`
whose two restrictions to `Wᵢ` agree already has agreeing restrictions to `Rᵢ`, and is the value
over `Uᵢ` of a global section by Stacks 03M8.  No separatedness of `X₀` is used.

## Main results

* `AlgebraicGeometry.Space.exists_isPullback_of_relationCover`: in any category with pullbacks,
  the map from a base change `Wⱼ = Xⱼ ×_{X₀} W₀` to the self fibre product of `Uⱼ = Xⱼ ×_{X₀} U₀`
  is a base change of `W₀ ⟶ U₀ ×_{X₀} U₀`.
* `AlgebraicGeometry.Space.injective_smallEtale_map_of_isSurjective`: restriction of a sheaf of
  sets on the small étale site along a morphism surjective on points is injective.
* `AlgebraicGeometry.Space.exists_sections_eq_of_relationCover`: Stacks 03M8 with the relation
  replaced by a cover of it.
* `AlgebraicGeometry.Space.LimitSituation.exists_relationCover_stages_limit`: an affine `W₀`
  étale over `X₀` with two morphisms to `U₀` over `X₀` such that, at every stage and at the limit
  and for every module, a section over the chart with equal restrictions to the chart of `W₀` is
  the value of a global section; `.exists_relationCover` is its stagewise half.

The limit `X = lim Xᵢ` is handled in the same way as a stage: its chart `U = X ×_{X₀} U₀` and the
chart `W = X ×_{X₀} W₀` are base changes along the projection `X ⟶ X₀`
(`AlgebraicGeometry.Space.LimitSituation.isPullback_limitChartToSpace`), which is all the pasting
uses.

## References

* [Stacks Project, Tag 07SI](https://stacks.math.columbia.edu/tag/07SI)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 03M8](https://stacks.math.columbia.edu/tag/03M8)
* [Stacks Project, Tag 03MH](https://stacks.math.columbia.edu/tag/03MH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe u

namespace AlgebraicGeometry.Space

/-! ### The cover of the relation is a base change -/

section Pasting

variable {𝒞 : Type*} [Category 𝒞] [HasPullbacks 𝒞]

/-- **A cover of the relation of a base-changed chart is a base change of the cover of the
relation.**  Let `Uⱼ = Xⱼ ×_{X₀} U₀` and `Wⱼ = Xⱼ ×_{X₀} W₀` be base changes of `f₀ : U₀ ⟶ X₀`
and `g₀ : W₀ ⟶ X₀` along `Xⱼ ⟶ X₀`, let `T = U₀ ×_{X₀} U₀` with projections `τ, υ`, and let
`c : W₀ ⟶ T` with `c ≫ τ ≫ f₀ = g₀`.  Let `a, b : Wⱼ ⟶ Uⱼ` be the maps induced by `c ≫ τ` and
`c ≫ υ`, let `R` with projections `p, q` be the self fibre product of `Uⱼ` over `Xⱼ`, and let
`k : Wⱼ ⟶ R` have projections `a` and `b`.  Then `k` is a base change of `c`: there is
`h : R ⟶ T` making the square `Wⱼ ⟶ W₀`, `k`, `c`, `h` cartesian.

The relation `R` is identified with `Xⱼ ×_{X₀} T` by comparing both with the self fibre product
of `Uⱼ`, by the pasting calculus; the square for `k` is then the left half of the cartesian
square `Wⱼ = Xⱼ ×_{X₀} W₀`. -/
theorem exists_isPullback_of_relationCover {Xj X₀ U₀ W₀ Uj Wj T R : 𝒞} (π : Xj ⟶ X₀)
    {f₀ : U₀ ⟶ X₀} {g₀ : W₀ ⟶ X₀} {st : Uj ⟶ Xj} {cb : Uj ⟶ U₀}
    (hC : IsPullback st cb π f₀) {est : Wj ⟶ Xj} {ecb : Wj ⟶ W₀}
    (hE : IsPullback est ecb π g₀) {τ υ : T ⟶ U₀} (hT : IsPullback τ υ f₀ f₀) (c : W₀ ⟶ T)
    (ht : (c ≫ τ) ≫ f₀ = g₀) {a b : Wj ⟶ Uj} (ha₁ : a ≫ st = est) (ha₂ : a ≫ cb = ecb ≫ c ≫ τ)
    (hb₂ : b ≫ cb = ecb ≫ c ≫ υ) {p q : R ⟶ Uj} (hR : IsPullback p q st st) (k : Wj ⟶ R)
    (hkp : k ≫ p = a) (hkq : k ≫ q = b) :
    ∃ h : R ⟶ T, IsPullback ecb k c h := by
  obtain ⟨P, fst, snd, hP⟩ : ∃ (P : 𝒞) (fst : P ⟶ Xj) (snd : P ⟶ T),
      IsPullback fst snd π (τ ≫ f₀) :=
    ⟨_, _, _, IsPullback.of_hasPullback _ _⟩
  have w₁ : fst ≫ π = (snd ≫ τ) ≫ f₀ := by rw [hP.w, Category.assoc]
  have w₂ : fst ≫ π = (snd ≫ υ) ≫ f₀ := by rw [hP.w, Category.assoc, hT.w]
  let α := hC.lift fst (snd ≫ τ) w₁
  let β := hC.lift fst (snd ≫ υ) w₂
  have hα₁ : α ≫ st = fst := hC.lift_fst _ _ _
  have hα₂ : α ≫ cb = snd ≫ τ := hC.lift_snd _ _ _
  have hβ₁ : β ≫ st = fst := hC.lift_fst _ _ _
  have hβ₂ : β ≫ cb = snd ≫ υ := hC.lift_snd _ _ _
  have h₁ : IsPullback snd α τ cb := by
    refine IsPullback.of_bot ?_ hα₂.symm hC.flip
    rw [hα₁]
    exact hP.flip
  have hker : IsPullback α β st st := by
    refine (IsPullback.of_right ?_ (hβ₁.trans hα₁.symm) hC.flip).flip
    rw [hβ₂, hC.w]
    exact h₁.paste_horiz hT.flip
  let e := hR.isoIsPullback _ _ hker
  have he₁ : e.hom ≫ α = p := hR.isoIsPullback_hom_fst _ _ hker
  have he₂ : e.hom ≫ β = q := hR.isoIsPullback_hom_snd _ _ hker
  have hRT : IsPullback (p ≫ st) (e.hom ≫ snd) π (τ ≫ f₀) := by
    refine IsPullback.of_iso hP e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · rw [← he₁, Iso.symm_hom, Iso.refl_hom, Category.comp_id, Category.assoc,
        Iso.inv_hom_id_assoc, hα₁]
    all_goals simp
  refine ⟨e.hom ≫ snd, ?_⟩
  have hsq : k ≫ e.hom ≫ snd = ecb ≫ c := by
    refine hT.hom_ext ?_ ?_
    · simp only [Category.assoc]
      rw [← hα₂, reassoc_of% he₁, reassoc_of% hkp, ha₂]
    · simp only [Category.assoc]
      rw [← hβ₂, reassoc_of% he₂, reassoc_of% hkq, hb₂]
  refine (IsPullback.of_right ?_ hsq hRT).flip
  rwa [← Category.assoc k p, hkp, ha₁, ← Category.assoc c τ, ht]

end Pasting

/-! ### Restriction along a morphism surjective on points is injective -/

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Restriction of a sheaf of sets on the small étale site along a morphism of charts which is
surjective on points is injective.**  The sheaf is the restriction of its right Kan extension
along the comparison functor to the spaces-étale site, by the counit of the comparison
adjunction, which is bijective; there a morphism surjective on points is a covering by
Stacks 03H7, so restriction along it is injective. -/
theorem injective_smallEtale_map_of_isSurjective {X : AlgebraicSpaces B S hS}
    (G : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) {R R' : SmallEtale B S hS X.1}
    (k : R' ⟶ R)
    (hk : IsSurjective B S hS
      ((SpacesEtale.toSpaces B S hS X).map ((comparisonFunctor B S hS X).map k)).hom) :
    Function.Injective (G.obj.map k.op) := by
  intro a b hab
  obtain ⟨a', rfl⟩ := (bijective_comparisonAdjunction_counit G (op R)).2 a
  obtain ⟨b', rfl⟩ := (bijective_comparisonAdjunction_counit G (op R)).2 b
  exact congrArg _ (injective_map_of_isSurjective
    (Q := (smallEtaleComparisonRan B S hS X).obj G) _ hk
    ((bijective_comparisonAdjunction_counit G (op R')).1
      ((comparisonAdjunction_counit_naturality G k a').trans
        (hab.trans (comparisonAdjunction_counit_naturality G k b').symm))))

/-! ### Gluing over a cover of the relation -/

/-- **Stacks 03M8 over a cover of the relation.**  Let `U` be an étale scheme chart of an
algebraic space `Y`, surjective on points, and let `a, b : W ⟶ U` be two morphisms of charts
which cover the relation `U ×_Y U`, in the sense that every map `k : W ⟶ R` into a self fibre
product `R` of `U` over `Y` with projections `a` and `b` is surjective on points.  Then, for every
module `N` on `Y`, a section of `N` over `U` whose two restrictions to `W` agree is the value over
`U` of a global section.

The restrictions to the self fibre product agree because restriction along the surjective `k` is
injective (`AlgebraicGeometry.Space.injective_smallEtale_map_of_isSurjective`), and the section
then glues by `AlgebraicGeometry.Space.moduleSectionsEquivEqualizer`. -/
theorem exists_sections_eq_of_relationCover {Y : AlgebraicSpaces B S hS}
    (N : Modules.{u, u} B S hS Y.1 Y.2) {U W : SmallEtale B S hS Y.1}
    (hU : IsSurjective B S hS U.1.hom) (a b : W ⟶ U)
    (hcov : ∀ {R : SmallEtale B S hS Y.1} {p q : R ⟶ U} (k : W ⟶ R),
      IsPullback (yoneda.map ((SmallEtale.toOver B S hS Y.1).map p))
        (yoneda.map ((SmallEtale.toOver B S hS Y.1).map q)) U.1.hom U.1.hom →
      k ≫ p = a → k ≫ q = b →
      IsSurjective B S hS (yoneda.map ((SmallEtale.toOver B S hS Y.1).map k)))
    (x : (moduleSetSheaf B S hS Y N).obj.obj (op U))
    (hx : (moduleSetSheaf B S hS Y N).obj.map a.op x = (moduleSetSheaf B S hS Y N).obj.map b.op x) :
    ∃ σ : N.sections, σ.val (op U) = x := by
  have := comparisonFunctor_full B S hS Y
  have := comparisonFunctor_faithful B S hS Y
  obtain ⟨R, p, q, hR⟩ := exists_etaleChart_isPullback_self B S hS Y
    (SpacesEtale.idObj B S hS Y) U ((SpacesEtale.isTerminal_idObj B S hS Y).from _)
  let k : W ⟶ R := (comparisonFunctor B S hS Y).preimage
    (hR.lift ((comparisonFunctor B S hS Y).map a) ((comparisonFunctor B S hS Y).map b)
      ((SpacesEtale.isTerminal_idObj B S hS Y).hom_ext _ _))
  have hkp : k ≫ p = a := (comparisonFunctor B S hS Y).map_injective (by simp [k])
  have hkq : k ≫ q = b := (comparisonFunctor B S hS Y).map_injective (by simp [k])
  have K : IsPullback (yoneda.map ((SmallEtale.toOver B S hS Y.1).map p))
      (yoneda.map ((SmallEtale.toOver B S hS Y.1).map q)) U.1.hom U.1.hom := by
    have h₀ := AlgebraicSpaces.isPullback_hom B S hS (hR.map (SpacesEtale.toSpaces B S hS Y))
    rwa [toSpaces_comparisonFunctor_map_hom, toSpaces_comparisonFunctor_map_hom,
      SpacesEtale.toSpaces_map_from_idObj] at h₀
  have hk : IsSurjective B S hS
      ((SpacesEtale.toSpaces B S hS Y).map ((comparisonFunctor B S hS Y).map k)).hom := by
    rw [toSpaces_comparisonFunctor_map_hom]
    exact hcov k K hkp hkq
  let G := moduleSetSheaf B S hS Y N
  have hpq : G.obj.map p.op x = G.obj.map q.op x := by
    apply injective_smallEtale_map_of_isSurjective G k hk
    rwa [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp,
      hkp, hkq]
  exact ⟨(moduleSectionsEquivEqualizer B S hS N hU hR).symm ⟨x, hpq⟩,
    (moduleSectionsEquivEqualizer_apply_val B S hS N hU hR _).symm.trans
      (congrArg Subtype.val ((moduleSectionsEquivEqualizer B S hS N hU hR).apply_symm_apply _))⟩

/-- Composing the images in presheaves over `Y` of `k` and `p` gives the image of `a = k ≫ p`. -/
private theorem yoneda_map_toOver_comp_eq {Y : AlgebraicSpaces B S hS}
    {W R U : SmallEtale B S hS Y.1} (k : W ⟶ R) (p : R ⟶ U) {a : W ⟶ U} (h : k ≫ p = a) :
    yoneda.map ((SmallEtale.toOver B S hS Y.1).map k) ≫
      yoneda.map ((SmallEtale.toOver B S hS Y.1).map p) =
    yoneda.map ((SmallEtale.toOver B S hS Y.1).map a) := by
  rw [← yoneda.map_comp, ← Functor.map_comp, h]

/-! ### The cover of the relation of an affine chart of a limit situation -/

namespace LimitSituation

variable {hZ : B.Contains (⊤_ Scheme.{u})} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **An affine étale cover of the relation of an affine chart, valid at every stage and at the
limit.**  Let `f₀ : U₀ ⟶ X₀` be an affine étale chart of the chosen stage of a limit situation,
surjective on points.  There are an affine étale chart `g₀ : W₀ ⟶ X₀` and two morphisms
`t, v : W₀ ⟶ U₀` over `X₀` such that, at every stage `Xᵢ` and at the limit `X`, and for every
module `N` there, a section of `N` over the chart `Uᵢ` (or `U = lim Uᵢ`) whose two restrictions
to the chart `Wᵢ` (or `W = lim Wᵢ`) agree is the value of a global section of `N`.

`W₀` is an affine scheme étale and surjective onto the relation `U₀ ×_{X₀} U₀`, which is a
quasi-compact scheme because `X₀` is quasi-separated (Stacks 03H6), and `t`, `v` are the two
projections composed with it.  At a stage, and at the limit, the map from the chart of `W₀` to
the self fibre product of the chart of `U₀` is a base change of `W₀ ⟶ U₀ ×_{X₀} U₀`
(`AlgebraicGeometry.Space.exists_isPullback_of_relationCover`), so it is surjective on points by
Stacks 03MH, and `AlgebraicGeometry.Space.exists_sections_eq_of_relationCover` glues.

Unlike
`AlgebraicGeometry.Space.LimitSituation.exists_affine_relationChart_of_isAbsolutelySeparated`, no
separatedness of the chosen stage is assumed. -/
theorem exists_relationCover_stages_limit (A : LimitSituation B S hS hZ X)
    {U₀ : BigAffineFppf B S hS}
    {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ A.system.obj (op A.base)}
    (hf₀ : IsEtaleChart B S hS (A.system.obj (op A.base)) (CostructuredArrow.mk f₀))
    (hsurj : IsSurjective B S hS f₀) :
    ∃ (W₀ : BigAffineFppf B S hS)
      (g₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj W₀) ⟶ A.system.obj (op A.base))
      (hg₀ : IsEtaleChart B S hS (A.system.obj (op A.base)) (CostructuredArrow.mk g₀))
      (t v : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj W₀) ⟶
        yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀))
      (ht : t ≫ f₀ = g₀) (hv : v ≫ f₀ = g₀),
      (∀ (i : A.Stages) (N : Modules.{u, u} B S hS (A.stage i.1).obj (A.stage i.1).property)
        (x : (moduleSetSheaf B S hS (A.stage i.1) N).obj.obj
          (op (A.stagesEtaleChart (A.chartSystem U₀ f₀) hf₀ i))),
        (moduleSetSheaf B S hS (A.stage i.1) N).obj.map
            (A.stagesEtaleChartMap (A.chartSystem U₀ f₀) hf₀ (A.chartSystem W₀ g₀) hg₀ ht i).op x =
          (moduleSetSheaf B S hS (A.stage i.1) N).obj.map
            (A.stagesEtaleChartMap (A.chartSystem U₀ f₀) hf₀ (A.chartSystem W₀ g₀) hg₀ hv i).op x →
        ∃ σ : N.sections, σ.val (op (A.stagesEtaleChart (A.chartSystem U₀ f₀) hf₀ i)) = x) ∧
      (∀ (hX : IsAlgebraicSpace B S hS X) (hI : #A.I < B.cutoff.ord.cof)
        (N : Modules.{u, u} B S hS (A.limitSpace hX).obj (A.limitSpace hX).property)
        (x : (moduleSetSheaf B S hS (A.limitSpace hX) N).obj.obj
          (op (A.limitEtaleChart (A.chartSystem U₀ f₀) (A.chartLimitBridge U₀ f₀ hI) hf₀))),
        (moduleSetSheaf B S hS (A.limitSpace hX) N).obj.map
            (A.limitEtaleChartMap (A.chartSystem U₀ f₀) (A.chartLimitBridge U₀ f₀ hI)
              (A.chartSystem W₀ g₀) (A.chartLimitBridge W₀ g₀ hI) hf₀ hg₀ ht).op x =
          (moduleSetSheaf B S hS (A.limitSpace hX) N).obj.map
            (A.limitEtaleChartMap (A.chartSystem U₀ f₀) (A.chartLimitBridge U₀ f₀ hI)
              (A.chartSystem W₀ g₀) (A.chartLimitBridge W₀ g₀ hI) hf₀ hg₀ hv).op x →
        ∃ σ : N.sections, σ.val (op (A.limitEtaleChart (A.chartSystem U₀ f₀)
          (A.chartLimitBridge U₀ f₀ hI) hf₀)) = x) := by
  obtain ⟨T, τ, υ, hT, hτe, -⟩ := exists_etale_kernelPair B S hS f₀ hf₀
  have hU₀c : CompactSpace
      ((BigFppfOver.toScheme B S hS).obj ((BigAffineFppf.inclusion B S hS).obj U₀)) := by
    have : IsAffine
        ((BigFppfOver.toScheme B S hS).obj ((BigAffineFppf.inclusion B S hS).obj U₀)) :=
      U₀.property
    infer_instance
  obtain ⟨T₁, c, hT₁, hcs, hce⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS (yoneda.obj T)
      (isAlgebraicSpace_yoneda B S hS T)).1 (isQuasiCompactSpace_yoneda B S hS T
        (compactSpace_of_isAbsolutelyQuasiSeparated B S hS hZ (A.quasiSeparated A.base) hT hU₀c
          hU₀c))
  let W₀ : BigAffineFppf B S hS := ⟨T₁, hT₁⟩
  let c' : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj W₀) ⟶ yoneda.obj T := c
  have hc' : IsSurjective B S hS c' := isSurjective_of_presheafSurjective B S hS c hcs
  let g₀ := c' ≫ yoneda.map τ ≫ f₀
  have hg₀ : IsEtaleChart B S hS (A.system.obj (op A.base)) (CostructuredArrow.mk g₀) :=
    presheaf_etale_of_isEtale B S hS (isEtale_comp B S hS hce
      (isEtale_of_presheaf_etale B S hS (etale_comp_of_scheme B S hS τ f₀ hτe hf₀)))
  have ht : (c' ≫ yoneda.map τ) ≫ f₀ = g₀ := Category.assoc _ _ _
  have hv : (c' ≫ yoneda.map υ) ≫ f₀ = g₀ :=
    (Category.assoc _ _ _).trans (congrArg (c' ≫ ·) hT.w.symm)
  let C := A.chartSystem U₀ f₀
  let E := A.chartSystem W₀ g₀
  refine ⟨W₀, g₀, hg₀, c' ≫ yoneda.map τ, c' ≫ yoneda.map υ, ht, hv, ?_, ?_⟩
  · intro i N x hx
    let j := (stagesOverEquivalence A).functor.obj (op i)
    refine exists_sections_eq_of_relationCover N (A.isSurjective_stagesEtaleChart C hf₀ hsurj i)
      _ _ (fun {R p q} k K hkp hkq => ?_) x hx
    obtain ⟨h, hsq⟩ := exists_isPullback_of_relationCover (A.system.map j.hom) (C.isPullback j)
      (E.isPullback j) hT c' ht (C.inducedPresheafMap_comp_stageMap E ht j)
      ((C.inducedPresheafMap_comp_baseMap E ht j).trans (Category.assoc _ _ _))
      ((C.inducedPresheafMap_comp_baseMap E hv j).trans (Category.assoc _ _ _)) K
      (yoneda.map ((SmallEtale.toOver B S hS (A.stage i.1).1).map k))
      ((yoneda_map_toOver_comp_eq k p hkp).trans (C.yoneda_map_inducedMap E ht j))
      ((yoneda_map_toOver_comp_eq k q hkq).trans (C.yoneda_map_inducedMap E hv j))
    exact surjective_pointsMap_of_isPullback B S hS hsq hc'
  · intro hX hI N x hx
    let LC := A.chartLimitBridge U₀ f₀ hI
    let LE := A.chartLimitBridge W₀ g₀ hI
    refine exists_sections_eq_of_relationCover N (A.isSurjective_limitEtaleChart C LC hf₀ hsurj)
      _ _ (fun {R p q} k K hkp hkq => ?_) x hx
    have hia : ∀ {τ' : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj W₀) ⟶
        yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀)} (hτ' : τ' ≫ f₀ = g₀),
        yoneda.map (AffineChartSystem.LimitBridge.inducedMap LC LE hτ') ≫ LC.toBase
          = LE.toBase ≫ τ' := fun hτ' => by
      rw [AffineChartSystem.LimitBridge.yoneda_map_inducedMap,
        AffineChartSystem.LimitBridge.inducedPresheafMap_comp_toBase]
    obtain ⟨h, hsq⟩ := exists_isPullback_of_relationCover (A.π.app (op A.base))
      (A.isPullback_limitChartToSpace C LC) (A.isPullback_limitChartToSpace E LE) hT c' ht
      (A.yoneda_map_inducedMap_comp_limitChartToSpace C LC E LE ht)
      ((hia ht).trans (Category.assoc _ _ _)) ((hia hv).trans (Category.assoc _ _ _)) K
      (yoneda.map ((SmallEtale.toOver B S hS (A.limitSpace hX).1).map k))
      (yoneda_map_toOver_comp_eq k p hkp) (yoneda_map_toOver_comp_eq k q hkq)
    exact surjective_pointsMap_of_isPullback B S hS hsq hc'

/-- **An affine étale cover of the relation of an affine chart, valid at every stage.**  The
stagewise half of
`AlgebraicGeometry.Space.LimitSituation.exists_relationCover_stages_limit`: there are an affine
étale chart `g₀ : W₀ ⟶ X₀` and two morphisms `t, v : W₀ ⟶ U₀` over `X₀` such that, at every
stage `Xᵢ` and for every module `N` on it, a section of `N` over the chart `Uᵢ` whose two
restrictions to the chart `Wᵢ` agree is the value over `Uᵢ` of a global section of `N`. -/
theorem exists_relationCover (A : LimitSituation B S hS hZ X) {U₀ : BigAffineFppf B S hS}
    {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ A.system.obj (op A.base)}
    (hf₀ : IsEtaleChart B S hS (A.system.obj (op A.base)) (CostructuredArrow.mk f₀))
    (hsurj : IsSurjective B S hS f₀) :
    ∃ (W₀ : BigAffineFppf B S hS)
      (g₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj W₀) ⟶ A.system.obj (op A.base))
      (hg₀ : IsEtaleChart B S hS (A.system.obj (op A.base)) (CostructuredArrow.mk g₀))
      (t v : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj W₀) ⟶
        yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀))
      (ht : t ≫ f₀ = g₀) (hv : v ≫ f₀ = g₀),
      ∀ (i : A.Stages) (N : Modules.{u, u} B S hS (A.stage i.1).obj (A.stage i.1).property)
        (x : (moduleSetSheaf B S hS (A.stage i.1) N).obj.obj
          (op (A.stagesEtaleChart (A.chartSystem U₀ f₀) hf₀ i))),
        (moduleSetSheaf B S hS (A.stage i.1) N).obj.map
            (A.stagesEtaleChartMap (A.chartSystem U₀ f₀) hf₀ (A.chartSystem W₀ g₀) hg₀ ht i).op x =
          (moduleSetSheaf B S hS (A.stage i.1) N).obj.map
            (A.stagesEtaleChartMap (A.chartSystem U₀ f₀) hf₀ (A.chartSystem W₀ g₀) hg₀ hv i).op x →
        ∃ σ : N.sections, σ.val (op (A.stagesEtaleChart (A.chartSystem U₀ f₀) hf₀ i)) = x :=
  let ⟨W₀, g₀, hg₀, t, v, ht, hv, h, _⟩ := A.exists_relationCover_stages_limit hf₀ hsurj
  ⟨W₀, g₀, hg₀, t, v, ht, hv, h⟩

end LimitSituation

end AlgebraicGeometry.Space

end
