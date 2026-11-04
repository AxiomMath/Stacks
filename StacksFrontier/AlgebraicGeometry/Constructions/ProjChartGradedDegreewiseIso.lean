module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedTransport
public import StacksFrontier.AlgebraicGeometry.Constructions.RelativeProjMorphismIsoTransport

/-!
# The morphism of Stacks Tag 01NK only sees the positive degrees, up to isomorphism

Let `ψ : A → Γ_*(T, L)` and `ψ' : A → Γ_*(T, L')` be two data of graded sections on one scheme
`T` (the datum of [Stacks, Tag 01NK]), and suppose that in every *positive* degree `n` some
isomorphism `γ_n : L ^⊗ n ≅ L' ^⊗ n` of `𝒪_T`-modules carries the values of `ψ` to the values of
`ψ'`. The isomorphisms `γ_n` are arbitrary: they need not come from an isomorphism `L ≅ L'`, nor be
compatible with one another, and nothing is asked in degree `0`. Then `ψ` and `ψ'` have the same
open `U(ψ) = U(ψ')` and the same morphism `r_{L, ψ} = r_{L', ψ'}` into `Proj A`.

The reason is that the ring map `A_{(f)} ⟶ Γ(T_{ψ(f)}, 𝒪_T)` of the chart of a homogeneous `f` of
positive degree `e` sends `x / f ^ k` to the ratio `ψ(x) / ψ(f ^ k)` of two sections of one tensor
power, and a ratio of two sections of one invertible module is unchanged by any isomorphism of that
module (`Stacks.AlgebraicGeometry.ProjChartGradedVeronese.ratioOf_iso`); the fractions with
`k = 0` are rewritten as `x f / f`, whose degree is positive.

Together with `Stacks.AlgebraicGeometry.ProjChartGradedPullback.resLE_glued` this gives the
compatibility of `r_{L, ψ}` with a morphism of schemes `j : T' ⟶ T` for a datum on `T'` whose
values are the pulled-back values of `ψ` only up to such isomorphisms, and only in positive
degrees.

## Main results

* `…GradedSections.lift_eq_of_degreewiseIso`, `…chartToProj_eq_of_degreewiseIso`: the charts agree.
* `…GradedSections.coveringOpen_eq_of_degreewiseIso`: `U(ψ) = U(ψ')`.
* `…GradedSections.homOfLE_glued_of_degreewiseIso`: `r_{L, ψ} = r_{L', ψ'}`.
* `…GradedSections.resLE_glued_of_degreewiseIso`: the compatibility with a morphism of schemes.

## References

* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjChartGradedVeronese (ratioOf_iso)
open Stacks.AlgebraicGeometry.ProjChartGradedPullback
  (ratioOf_den_congr resLE_glued coveringOpen_eq)
open Stacks.AlgebraicGeometry.ProjChartRatioPullback (pullSection)
open AlgebraicGeometry (pullbackSectionHom)
open Stacks.AlgebraicGeometry.ProjChartCocycle (ratioOf)
open Stacks.MorphismToProj (HomogeneousRatios)
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.TensorPowers (natTensorPow)

universe u w

namespace Stacks.AlgebraicGeometry.ProjChartFullGraded

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

namespace GradedSections

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜]

section DegreewiseIso

variable {T : Scheme.{u}} {L L' : T.Modules} [Stacks.Ample.IsInvertibleModule T L]
  [Stacks.Ample.IsInvertibleModule T L'] (γ : ∀ n : ℕ, natTensorPow L n ≅ natTensorPow L' n)
  (ψ : GradedSections 𝒜 L) (ψ' : GradedSections 𝒜 L')
  (hγ : ∀ n : ℕ, 0 < n → ∀ a : 𝒜 n, (γ n).hom.app ⊤ (ψ.toFun n a) = ψ'.toFun n a)

include hγ

/-- **The two data have the same nonvanishing opens in positive degrees**: an isomorphism of
modules does not move the nonvanishing locus of a section. -/
theorem nonvanishingOpenAt_eq_of_degreewiseIso (n : ℕ) (hn : 0 < n) (a : 𝒜 n) :
    ψ'.nonvanishingOpenAt n a = ψ.nonvanishingOpenAt n a := by
  rw [nonvanishingOpenAt, nonvanishingOpenAt, ← hγ n hn a]
  exact TopologicalSpace.Opens.ext (Stacks.Ample.nonvanishingLocus_congr (γ n) (ψ.toFun n a))

/-- **`U(ψ) = U(ψ')`.** -/
theorem coveringOpen_eq_of_degreewiseIso : ψ'.coveringOpen = ψ.coveringOpen :=
  iSup_congr fun p => nonvanishingOpenAt_eq_of_degreewiseIso γ ψ ψ' hγ (p.1 + 1)
    (Nat.succ_pos _) p.2

/-- **The dehomogenisation ring maps of the two data agree** on every open on which the value at a
homogeneous `f` of positive degree does not vanish. -/
theorem lift_eq_of_degreewiseIso {e : ℕ} {f : A} (hf : f ∈ 𝒜 e) (he : 0 < e) {V : T.Opens}
    (hV : V ≤ nonvanishingOpen T (natTensorPow L e) (ψ.toFun e ⟨f, hf⟩))
    (hV' : V ≤ nonvanishingOpen T (natTensorPow L' e) (ψ'.toFun e ⟨f, hf⟩)) :
    (ψ'.homogeneousRatios hf hV').lift he = (ψ.homogeneousRatios hf hV).lift he := by
  have key : ∀ (k : ℕ) (x : A) (hx : x ∈ 𝒜 (k • e)), 0 < k →
      (ψ'.homogeneousRatios hf hV').lift he (HomogeneousLocalization.Away.mk 𝒜 hf k x hx) =
        (ψ.homogeneousRatios hf hV).lift he (HomogeneousLocalization.Away.mk 𝒜 hf k x hx) := by
    intro k x hx hk
    have hxm : x ∈ 𝒜 (k * e) := by simpa [smul_eq_mul] using hx
    have hfk : (f : A) ^ k ∈ 𝒜 (k * e) := HomogeneousRatios.pow_mem hf k
    have hpos : 0 < k * e := Nat.mul_pos hk he
    rw [ψ'.lift_mk hf hV' he k x hx ⟨x, hxm⟩ rfl, ψ.lift_mk hf hV he k x hx ⟨x, hxm⟩ rfl]
    have h1 := ψ'.le_nonvanishingOpen_pow hf hV' k
    have h2 : V ≤ nonvanishingOpen T (natTensorPow L' (k * e))
        ((γ (k * e)).hom.app ⊤ (ψ.toFun (k * e) ⟨f ^ k, hfk⟩)) := by
      rw [hγ (k * e) hpos]; exact h1
    refine (ratioOf_den_congr L' (hγ (k * e) hpos ⟨f ^ k, hfk⟩).symm h1 h2 _).trans ?_
    rw [← hγ (k * e) hpos ⟨x, hxm⟩]
    exact ratioOf_iso L L' (γ (k * e)) _ _ (ψ.le_nonvanishingOpen_pow hf hV k) h2
  refine Stacks.ProjGlobalSectionsAppTop.away_ringHom_ext 𝒜 hf fun k x hx => ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have hx1 : x * f ∈ 𝒜 (1 • e) := by
      have : x ∈ 𝒜 0 := by simpa using hx
      simpa using SetLike.mul_mem_graded this hf
    have hmk : HomogeneousLocalization.Away.mk 𝒜 hf 0 x hx =
        HomogeneousLocalization.Away.mk 𝒜 hf 1 (x * f) hx1 := by
      apply HomogeneousLocalization.val_injective
      rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
        Localization.mk_eq_mk_iff, Localization.r_iff_exists]
      exact ⟨1, by simp [mul_comm]⟩
    rw [hmk]
    exact key 1 (x * f) hx1 Nat.one_pos
  · exact key k x hx hk

/-- **The charts of the two data agree.** -/
theorem chartToProj_eq_of_degreewiseIso {e : ℕ} {f : A} (hf : f ∈ 𝒜 e) (he : 0 < e)
    {V : T.Opens} (hV : V ≤ nonvanishingOpen T (natTensorPow L e) (ψ.toFun e ⟨f, hf⟩))
    (hV' : V ≤ nonvanishingOpen T (natTensorPow L' e) (ψ'.toFun e ⟨f, hf⟩)) :
    ψ'.chartToProj hf hV' he = ψ.chartToProj hf hV he := by
  unfold GradedSections.chartToProj HomogeneousRatios.chartToProj HomogeneousRatios.toSpecAway
  rw [lift_eq_of_degreewiseIso γ ψ ψ' hγ hf he hV hV']

/-- **`r_{L, ψ} = r_{L', ψ'}`**, the two sources being the one open `U(ψ) = U(ψ')`. -/
theorem homOfLE_glued_of_degreewiseIso :
    T.homOfLE (coveringOpen_eq_of_degreewiseIso γ ψ ψ' hγ).ge ≫ ψ'.glued = ψ.glued := by
  refine ψ.eq_glued_of_homOfLE_eq fun e f hf he => ?_
  have hV' : nonvanishingOpen T (natTensorPow L e) (ψ.toFun e ⟨f, hf⟩) ≤
      nonvanishingOpen T (natTensorPow L' e) (ψ'.toFun e ⟨f, hf⟩) :=
    (nonvanishingOpenAt_eq_of_degreewiseIso γ ψ ψ' hγ e he ⟨f, hf⟩).ge
  rw [← Category.assoc, T.homOfLE_homOfLE]
  exact (ψ'.homOfLE_glued_of_le hf he hV' _).trans
    (chartToProj_eq_of_degreewiseIso γ ψ ψ' hγ hf he le_rfl hV')

end DegreewiseIso

section Pullback

variable {T T' : Scheme.{u}} (j : T' ⟶ T) {L : T.Modules} [Stacks.Ample.IsInvertibleModule T L]
  (ψ : GradedSections 𝒜 L) {M : T'.Modules} [Stacks.Ample.IsInvertibleModule T' M]
  (χ : GradedSections 𝒜 M)
  (γ : ∀ n : ℕ, natTensorPow M n ≅ natTensorPow ((Scheme.Modules.pullback j).obj L) n)
  (hγ : ∀ n : ℕ, 0 < n → ∀ a : 𝒜 n, (γ n).hom.app ⊤ (χ.toFun n a) = pullSection j L n (ψ.toFun n a))

include hγ

/-- `U(χ) = j^{-1}(U(ψ))` for a datum `χ` on `T'` whose values in positive degrees are the
pulled-back values of `ψ` up to isomorphisms of the tensor powers. -/
theorem coveringOpen_eq_preimage_of_degreewiseIso : χ.coveringOpen = j ⁻¹ᵁ ψ.coveringOpen :=
  (coveringOpen_eq_of_degreewiseIso γ χ (pullback j ψ) hγ).symm.trans
    (coveringOpen_eq j L ψ (pullback j ψ) fun _ _ => rfl)

/-- **The morphism `r_{L, ψ}` of [Stacks, Tag 01NK] commutes with a morphism of schemes
`j : T' ⟶ T`**, for a datum `χ` on `T'` whose values in positive degrees are the pulled-back values
of `ψ` up to arbitrary isomorphisms of the tensor powers: the restriction `U(χ) ⟶ U(ψ)` of `j`
followed by `r_{L, ψ}` is `r_{M, χ}`. This is `ProjChartGradedPullback.resLE_glued` for the
inverse-image datum, together with `homOfLE_glued_of_degreewiseIso`. -/
theorem resLE_glued_of_degreewiseIso :
    j.resLE ψ.coveringOpen χ.coveringOpen
        (coveringOpen_eq_preimage_of_degreewiseIso j ψ χ γ hγ).le ≫ ψ.glued = χ.glued := by
  have h1 := resLE_glued j L ψ (pullback j ψ) fun _ _ => rfl
  have h2 := homOfLE_glued_of_degreewiseIso γ χ (pullback j ψ) hγ
  rw [← h2, ← h1, ← Category.assoc, Scheme.Hom.map_resLE]

end Pullback

section PullbackVia

variable {T T' : Scheme.{u}} (j : T' ⟶ T) {L : T.Modules} [Stacks.Ample.IsInvertibleModule T L]
  (ψ : GradedSections 𝒜 L) {M : T'.Modules} [Stacks.Ample.IsInvertibleModule T' M]
  (χ : GradedSections 𝒜 M) (K : ℕ → T'.Modules)
  (γ : ∀ n : ℕ, natTensorPow M n ≅ K n)
  (δ : ∀ n : ℕ, (Scheme.Modules.pullback j).obj (natTensorPow L n) ≅ K n)
  (hγ : ∀ n : ℕ, 0 < n → ∀ a : 𝒜 n, (γ n).hom.app ⊤ (χ.toFun n a) =
    (δ n).hom.app ⊤ (pullbackSectionHom j (natTensorPow L n) ⊤ ⊤
      (Stacks.AlgebraicGeometry.ProjChartRatioPullback.top_le_preimage_top j) (ψ.toFun n a)))

/-- The isomorphisms `γ_n` and `δ_n` combined into isomorphisms
`M ^⊗ n ≅ (j^*L) ^⊗ n`. -/
def degreewiseIsoOfVia (n : ℕ) :
    natTensorPow M n ≅ natTensorPow ((Scheme.Modules.pullback j).obj L) n :=
  γ n ≪≫ (δ n).symm ≪≫
    (Stacks.AlgebraicGeometry.ProjChartRatioPullback.pullbackNatTensorPowIso j L n).symm

omit [Stacks.Ample.IsInvertibleModule T' M] in
include hγ in
/-- In positive degrees, the isomorphism `degreewiseIsoOfVia` sends `χ(a)` to the pullback
`j^*ψ(a)` of `ψ(a)`. -/
theorem degreewiseIsoOfVia_spec (n : ℕ) (hn : 0 < n) (a : 𝒜 n) :
    (degreewiseIsoOfVia j K γ δ n).hom.app ⊤ (χ.toFun n a) = pullSection j L n (ψ.toFun n a) := by
  have e := congrArg
    (fun z => (Stacks.AlgebraicGeometry.ProjChartRatioPullback.pullbackNatTensorPowIso
      j L n).inv.app ⊤ ((δ n).inv.app ⊤ z)) (hγ n hn a)
  refine e.trans ?_
  exact congrArg (fun z => (Stacks.AlgebraicGeometry.ProjChartRatioPullback.pullbackNatTensorPowIso
    j L n).inv.app ⊤ z)
    ((ConcreteCategory.congr_hom
      (congrArg (fun t => Scheme.Modules.Hom.app t ⊤) (δ n).hom_inv_id) _).trans rfl)

include hγ in
/-- `U(χ) = j^{-1}(U(ψ))`, for values compared through isomorphisms `γ_n`, `δ_n` with a common
target. -/
theorem coveringOpen_eq_preimage_of_degreewiseIsoVia : χ.coveringOpen = j ⁻¹ᵁ ψ.coveringOpen :=
  coveringOpen_eq_preimage_of_degreewiseIso j ψ χ (degreewiseIsoOfVia j K γ δ)
    (degreewiseIsoOfVia_spec j ψ χ K γ δ hγ)

include hγ in
/-- **`resLE_glued_of_degreewiseIso` with the values compared through isomorphisms with a common
target**: `γ_n(χ(a)) = δ_n(j^*ψ(a))` in positive degrees, for isomorphisms
`γ_n : M ^⊗ n ≅ K_n` and `δ_n : j^*(L ^⊗ n) ≅ K_n`. -/
theorem resLE_glued_of_degreewiseIsoVia :
    j.resLE ψ.coveringOpen χ.coveringOpen
        (coveringOpen_eq_preimage_of_degreewiseIsoVia j ψ χ K γ δ hγ).le ≫ ψ.glued = χ.glued :=
  resLE_glued_of_degreewiseIso j ψ χ (degreewiseIsoOfVia j K γ δ)
    (degreewiseIsoOfVia_spec j ψ χ K γ δ hγ)

end PullbackVia

end GradedSections

end Stacks.AlgebraicGeometry.ProjChartFullGraded

end
