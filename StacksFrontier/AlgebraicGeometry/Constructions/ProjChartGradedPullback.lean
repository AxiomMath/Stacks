module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartFullGradedGluing
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartRatioPullback

/-!
# The morphism `r_{L, ψ} : U(ψ) ⟶ Proj A` commutes with pullback

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded ring, `T` a scheme, `L` an invertible `𝒪_T`-module and
`ψ : A → Γ_*(T, L)` a graded map in the degreewise spelling
`Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections`, and `r_{L, ψ} : U(ψ) ⟶ Proj 𝒜`
the morphism of [Stacks, Tag 01NK]. For a morphism `j : T' ⟶ T` and a graded map `ψ'` each of whose
values is the pullback `Stacks.AlgebraicGeometry.ProjChartRatioPullback.pullSection` of the
corresponding value of `ψ`,

`U(ψ') = j^{-1}(U(ψ))`  and  `(j : U(ψ') ⟶ U(ψ)) ≫ r_{L, ψ} = r_{j^*L, ψ'}`.

## Main results

* `Stacks.AlgebraicGeometry.ProjChartGradedPullback.nonvanishingOpen_eq`: `T'_{ψ'(a)}` is the
  preimage of `T_{ψ(a)}`.
* `Stacks.AlgebraicGeometry.ProjChartGradedPullback.coveringOpen_eq`: `U(ψ') = j^{-1}(U(ψ))`.
* `Stacks.AlgebraicGeometry.ProjChartGradedPullback.lift_eq`: the dehomogenisation ring map
  `A_{(f)} ⟶ Γ(T_{ψ(f)}, 𝒪_T)` commutes with pullback, i.e. the one for `ψ'` is the one for `ψ`
  followed by `AlgebraicGeometry.Scheme.Hom.appLE`.
* `Stacks.AlgebraicGeometry.ProjChartGradedPullback.resLE_chartToProj`: the chart of a
  homogeneous element commutes with pullback.
* `Stacks.AlgebraicGeometry.ProjChartGradedPullback.resLE_glued`: `r_{L, ψ}` commutes with
  pullback.

## References

* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry HomogeneousLocalization
open Stacks.TensorPowers (natTensorPow)
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.AlgebraicGeometry.ProjChartCocycle (ratioOf)
open Stacks.AlgebraicGeometry.ProjChartFullGraded (GradedSections)
open Stacks.AlgebraicGeometry.ProjChartRatioPullback (pullSection nonvanishingOpen_pullSection
  ratioOf_pullback)
open Stacks.MorphismToProj (HomogeneousRatios)

universe u w

namespace Stacks.AlgebraicGeometry.ProjChartGradedPullback

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

/-! ### Two spellings of one denominator -/

/-- The ratio depends on the denominator only through the section. -/
theorem ratioOf_den_congr {Y : Scheme.{u}} (M : Y.Modules)
    [Stacks.Ample.IsInvertibleModule Y M] {n : ℕ} {V : Y.Opens}
    {t t' : Γ(natTensorPow M n, ⊤)} (h : t = t')
    (hV : V ≤ nonvanishingOpen Y (natTensorPow M n) t)
    (hV' : V ≤ nonvanishingOpen Y (natTensorPow M n) t')
    (x : Γ(natTensorPow M n, ⊤)) :
    ratioOf M t hV x = ratioOf M t' hV' x := by
  subst h
  rfl

/-! ### Charts on opens of two different schemes -/

section Away

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] {d : ℕ} {f : A} {hf : f ∈ 𝒜 d}

/-- For a morphism of schemes `g : X ⟶ Y`, an open `U` of `Y` and an open `V ≤ g^{-1}(U)` of `X`,
if the ring map of `R'` is the ring map of `R` followed by `AlgebraicGeometry.Scheme.Hom.appLE`,
then the morphism `V ⟶ Spec A_{(f)}` of `R'` is that of `R` precomposed with
`AlgebraicGeometry.Scheme.Hom.resLE`. -/
theorem resLE_toSpecAway {X Y : Scheme.{u}} (g : X ⟶ Y) {U : Y.Opens} {V : X.Opens}
    (hUV : V ≤ g ⁻¹ᵁ U) (R : HomogeneousRatios 𝒜 hf ↥Γ(Y, U))
    (R' : HomogeneousRatios 𝒜 hf ↥Γ(X, V)) (hd : 0 < d)
    (hlift : R'.lift hd
      = (CommRingCat.Hom.hom (g.appLE U V hUV)).comp (R.lift hd)) :
    g.resLE U V hUV ≫ R.toSpecAway hd = R'.toSpecAway hd := by
  rw [HomogeneousRatios.toSpecAway, HomogeneousRatios.toSpecAway, ← Category.assoc,
    ← Scheme.Opens.toSpecΓ_SpecMap_appLE g U V hUV, Category.assoc, ← Spec.map_comp, hlift,
    CommRingCat.ofHom_comp, CommRingCat.ofHom_hom]

end Away

/-! ### The pullback of a graded map, and its charts -/

section Pullback

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] {T T' : Scheme.{u}} (j : T' ⟶ T) (L : T.Modules)
  [Stacks.Ample.IsInvertibleModule T L] (ψ : GradedSections 𝒜 L)
  (ψ' : GradedSections 𝒜 ((Scheme.Modules.pullback j).obj L))
  (hψ : ∀ (n : ℕ) (a : 𝒜 n), ψ'.toFun n a = pullSection j L n (ψ.toFun n a))

include hψ

/-- The nonvanishing open of a value of `ψ'` is the preimage of that of `ψ`. -/
theorem nonvanishingOpen_eq (n : ℕ) (a : 𝒜 n) :
    nonvanishingOpen T' (natTensorPow ((Scheme.Modules.pullback j).obj L) n) (ψ'.toFun n a)
      = j ⁻¹ᵁ nonvanishingOpen T (natTensorPow L n) (ψ.toFun n a) := by
  rw [hψ n a, nonvanishingOpen_pullSection]

/-- `U(ψ') = j^{-1}(U(ψ))`: the open on which the pulled-back graded map generates is the
preimage of the open on which the original one does. -/
theorem coveringOpen_eq : ψ'.coveringOpen = j ⁻¹ᵁ ψ.coveringOpen := by
  rw [GradedSections.coveringOpen, GradedSections.coveringOpen, Scheme.Hom.preimage_iSup]
  exact iSup_congr fun p => nonvanishingOpen_eq j L ψ ψ' hψ (p.1 + 1) p.2

/-- `U(ψ')` lies in the preimage of `U(ψ)`. -/
theorem coveringOpen_le_preimage : ψ'.coveringOpen ≤ j ⁻¹ᵁ ψ.coveringOpen :=
  (coveringOpen_eq j L ψ ψ' hψ).le

variable {e : ℕ} {f : A} (hf : f ∈ 𝒜 e) (he : 0 < e) {V : T.Opens}
  (hV : V ≤ nonvanishingOpen T (natTensorPow L e) (ψ.toFun e ⟨f, hf⟩)) {V' : T'.Opens}
  (hVV' : V' ≤ j ⁻¹ᵁ V)
  (hV' : V' ≤ nonvanishingOpen T' (natTensorPow ((Scheme.Modules.pullback j).obj L) e)
    (ψ'.toFun e ⟨f, hf⟩))

include hV hVV' hV'

/-- The dehomogenisation ring map commutes with pullback: the ring map
`A_{(f)} ⟶ Γ(T'_{ψ'(f)}, 𝒪_{T'})` of `ψ'` is the ring map `A_{(f)} ⟶ Γ(T_{ψ(f)}, 𝒪_T)` of `ψ`
followed by `AlgebraicGeometry.Scheme.Hom.appLE`. -/
theorem lift_eq :
    (ψ'.homogeneousRatios hf hV').lift he
      = (CommRingCat.Hom.hom (j.appLE V V' hVV')).comp
          ((ψ.homogeneousRatios hf hV).lift he) := by
  refine Stacks.ProjGlobalSectionsAppTop.away_ringHom_ext 𝒜 hf fun n x hx => ?_
  have hxm : x ∈ 𝒜 (n * e) := by simpa [smul_eq_mul] using hx
  have hfn : (f : A) ^ n ∈ 𝒜 (n * e) := HomogeneousRatios.pow_mem hf n
  have hden : V' ≤ nonvanishingOpen T'
      (natTensorPow ((Scheme.Modules.pullback j).obj L) (n * e))
      (pullSection j L (n * e) (ψ.toFun (n * e) ⟨f ^ n, hfn⟩)) := by
    rw [nonvanishingOpen_pullSection]
    exact fun z hz => ψ.le_nonvanishingOpen_pow hf hV n (hVV' hz)
  rw [ψ'.lift_mk hf hV' he n x hx ⟨x, hxm⟩ rfl]
  show _ = j.appLE V V' hVV' ((ψ.homogeneousRatios hf hV).lift he _)
  rw [ψ.lift_mk hf hV he n x hx ⟨x, hxm⟩ rfl,
    ← ratioOf_pullback j L (ψ.toFun (n * e) ⟨f ^ n, hfn⟩)
      (ψ.le_nonvanishingOpen_pow hf hV n) (ψ.toFun (n * e) ⟨x, hxm⟩) hVV' hden,
    hψ (n * e) ⟨x, hxm⟩]
  exact ratioOf_den_congr _ (hψ (n * e) ⟨f ^ n, hfn⟩) _ hden _

/-- The chart of a homogeneous element commutes with pullback: the chart `T'_{ψ'(f)} ⟶ Proj 𝒜`
of `ψ'` is the chart `T_{ψ(f)} ⟶ Proj 𝒜` of `ψ` precomposed with the restriction of `j`. -/
theorem resLE_chartToProj :
    j.resLE V V' hVV' ≫ ψ.chartToProj hf hV he = ψ'.chartToProj hf hV' he := by
  rw [GradedSections.chartToProj, GradedSections.chartToProj, HomogeneousRatios.chartToProj,
    HomogeneousRatios.chartToProj, ← Category.assoc,
    resLE_toSpecAway j hVV' (ψ.homogeneousRatios hf hV) (ψ'.homogeneousRatios hf hV') he
      (lift_eq j L ψ ψ' hψ hf he hV hVV' hV')]

end Pullback

/-! ### The morphism `r_{L, ψ}` commutes with pullback -/

section Glued

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] {T T' : Scheme.{u}} (j : T' ⟶ T) (L : T.Modules)
  [Stacks.Ample.IsInvertibleModule T L] (ψ : GradedSections 𝒜 L)
  (ψ' : GradedSections 𝒜 ((Scheme.Modules.pullback j).obj L))
  (hψ : ∀ (n : ℕ) (a : 𝒜 n), ψ'.toFun n a = pullSection j L n (ψ.toFun n a))

include hψ

/-- The morphism `r_{L, ψ}` commutes with pullback: for a morphism of schemes `j : T' ⟶ T` and
the graded map `ψ'` whose values are the pullbacks of the values of `ψ`, the restriction
`U(ψ') ⟶ U(ψ)` of `j` followed by `r_{L, ψ}` is `r_{j^*L, ψ'}`. -/
theorem resLE_glued :
    j.resLE ψ.coveringOpen ψ'.coveringOpen (coveringOpen_le_preimage j L ψ ψ' hψ) ≫ ψ.glued
      = ψ'.glued := by
  refine ψ'.hom_ext_of_homOfLE_eq fun e g => ?_
  have hle : ψ'.nonvanishingOpenAt (e + 1) g ≤ j ⁻¹ᵁ ψ.nonvanishingOpenAt (e + 1) g :=
    (nonvanishingOpen_eq j L ψ ψ' hψ (e + 1) g).le
  have key : T'.homOfLE (ψ'.nonvanishingOpenAt_le_coveringOpen e g)
        ≫ j.resLE ψ.coveringOpen ψ'.coveringOpen (coveringOpen_le_preimage j L ψ ψ' hψ)
      = j.resLE (ψ.nonvanishingOpenAt (e + 1) g) (ψ'.nonvanishingOpenAt (e + 1) g) hle
        ≫ T.homOfLE (ψ.nonvanishingOpenAt_le_coveringOpen e g) := by
    rw [Scheme.Hom.map_resLE, Scheme.Hom.resLE_map]
  rw [← Category.assoc, key, Category.assoc, ψ.homOfLE_glued ⟨e, g⟩, ψ'.homOfLE_glued ⟨e, g⟩]
  exact resLE_chartToProj j L ψ ψ' hψ g.2 (Nat.succ_pos e) le_rfl hle le_rfl

end Glued

end Stacks.AlgebraicGeometry.ProjChartGradedPullback

end
