module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.Examples.RootsOfUnity
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.GradedModuleEquivariantSheaf
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeOverSchemeWithGroup
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeStratificationChart
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeStratificationStrata
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStack
public import StacksFrontier.AlgebraicGeometry.Stacks.Substack
public import StacksFrontier.CategoryTheory.Sites.Gerbe.Basic
public import StacksFrontier.CategoryTheory.Sites.Stack.LiftGluing
import StacksFrontier.CategoryTheory.FiberedCategory.HomLift
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The strata of `[U/𝐆_m]` are gerbes over schemes with groups

Let `k` be a commutative ring, `p` a nonzero natural number, `U = Spec k[x_0, x_1, …]` with the
action of `𝐆_m` in which `x_i` has weight `p^i`, and `𝒳 = [U/𝐆_m]` the weighted quotient stack
of **Stacks 06RE** (`AlgebraicGeometry.PPowerWeighted.weightedQuotientStack`). This file proves
the clause of 06RE saying that each stratum `𝒳_i` is a gerbe over a scheme with group `μ_{p^i}`
and `𝒳_∞` is a gerbe over a scheme with group `𝐆_m`.

## Main definitions

* `AlgebraicGeometry.PPowerWeighted.stratumGroup`: the group scheme `μ_{p^i}`, resp. `𝐆_m`, over
  `Spec ℤ`, with its group structure `AlgebraicGeometry.PPowerWeighted.stratumGroupGrpObj`, and
  `AlgebraicGeometry.PPowerWeighted.stratumHomMulEquiv`, the identification of its sections over
  `T` with the `p^i`-th roots of unity, resp. all units, of `Γ(T)`.
* `AlgebraicGeometry.PPowerWeighted.coarse`: the coarse 1-morphism `𝒳_a ⟶ M_a` to the scheme
  `M_a = coarseSiteObject hU a`, sending an object to the morphism through which the coarse
  images of all its charts factor.
* `AlgebraicGeometry.PPowerWeighted.band`: the identification of the vertical automorphisms of
  an object of `𝒳_a` over `T` with the sections of the stratum group over `T`.

## Main results

* `AlgebraicGeometry.PPowerWeighted.isGerbeOver_coarse`: `𝒳_a` is a gerbe over `M_a`.
* `AlgebraicGeometry.PPowerWeighted.band_naturality`: the band is natural along every morphism.
* `AlgebraicGeometry.PPowerWeighted.isGerbeOverSchemeWithGroup_stratum`: **Stacks 06RE**, the
  stratum `𝒳_a` is a gerbe over a scheme with group `stratumGroup p a`.

## Implementation notes

Everything is first proved for an arbitrary property `P` of objects of `𝒳` which is inherited
along morphisms and cuts out the stratum `X_a ⊆ U` on the chart objects
(`AlgebraicGeometry.PPowerWeighted.isGerbeOverSchemeWithGroup_of_chart`), and then read at
`AlgebraicGeometry.PPowerWeighted.stratumProperty`.

The coarse map of an object is glued in the representable sheaf of `M_a` from the coarse images
of its charts, which agree because two charts over the same base morphism differ by a unit
(`AlgebraicGeometry.PPowerWeighted.exists_actMap_eq_of_lifts`) and the coarse maps are invariant.
The automorphism of an object attached to a unit `t` of the stratum group is glued in the stack
`𝒳` from the action of `t` on the chart objects, which commutes with every morphism between
chart objects because the group of units is commutative
(`AlgebraicGeometry.PPowerWeighted.comp_chartAct`); conversely every vertical automorphism is,
chart by chart, the action of a unit, and these units glue in the fppf sheaf of units
(`AlgebraicGeometry.PPowerWeighted.units_existsUnique_of_locally`). The gluing statements used
for the stack are `CategoryTheory.Functor.IsStack.exists_hom_of_locally` and its companions.

## References

* [Stacks Project, Tag 06RE](https://stacks.math.columbia.edu/tag/06RE)
* [Stacks Project, Section 06RB](https://stacks.math.columbia.edu/tag/06RB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped MonObj

universe u w

namespace AlgebraicGeometry.PPowerWeighted

/-- The base `Spec ℤ` of the site. -/
local macro "𝒵" : term => `(Spec (CommRingCat.of (ULift ℤ)))

/-! ### The groups of the strata -/

section Groups

variable (p : ℕ)

/-- **The group of the stratum `X_a` of Stacks 06RE**: the group scheme `μ_{p^i}` for `a = i` and
`𝐆_m` for `a = ∞`, over `Spec ℤ`. -/
noncomputable def stratumGroup : WithTop ℕ → Over 𝒵
  | ⊤ => multiplicativeGroupULift.{u}.asOver 𝒵
  | (i : ℕ) => (AlgebraicGeometry.rootsOfUnity.{u} (p ^ i)).asOver 𝒵

/-- The group-scheme structures of the groups of the strata. -/
noncomputable instance stratumGroupGrpObj [NeZero p] :
    ∀ a : WithTop ℕ, GrpObj (stratumGroup.{u} p a)
  | ⊤ => instGrpObjSpecAsOverSpec (R := .of (ULift.{u} ℤ))
      (A := .of (LaurentPolynomial (ULift.{u} ℤ)))
  | (i : ℕ) =>
      haveI : Fact (0 < p ^ i) := ⟨pow_pos (Nat.pos_of_ne_zero (NeZero.ne p)) i⟩
      rootsOfUnityGrpObj (p ^ i)

/-- The units of a ring which are the sections of the group of the stratum `X_a`: the
`p^i`-th roots of unity for `a = i`, all units for `a = ∞`. -/
def stratumUnits (p : ℕ) {A : Type u} [CommRing A] : WithTop ℕ → Subgroup Aˣ
  | ⊤ => ⊤
  | (i : ℕ) => rootsUnitsSubgroup (p ^ i)

/-- Every unit lies in `stratumUnits p ⊤`. -/
@[simp] theorem mem_stratumUnits_top (p : ℕ) {A : Type u} [CommRing A] (t : Aˣ) :
    t ∈ stratumUnits p (⊤ : WithTop ℕ) := Subgroup.mem_top t

/-- A unit lies in `stratumUnits p i` if and only if it is a `p^i`-th root of unity. -/
theorem mem_stratumUnits_coe (p i : ℕ) {A : Type u} [CommRing A] (t : Aˣ) :
    t ∈ stratumUnits p (i : WithTop ℕ) ↔ t ^ p ^ i = 1 := Iff.rfl

/-- The stratum units are preserved by ring maps. -/
theorem map_mem_stratumUnits (p : ℕ) (a : WithTop ℕ) {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) {t : Aˣ} (ht : t ∈ stratumUnits p a) :
    Units.map f.toMonoidHom t ∈ stratumUnits p a := by
  induction a using WithTop.recTopCoe with
  | top => exact Subgroup.mem_top _
  | coe i =>
    show Units.map f.toMonoidHom t ^ p ^ i = 1
    rw [← map_pow, show t ^ p ^ i = 1 from ht, map_one]

/-- Every power of a nonzero natural number is positive. -/
theorem pow_pos_of_neZero (p : ℕ) [NeZero p] (i : ℕ) : 0 < p ^ i :=
  pow_pos (Nat.pos_of_ne_zero (NeZero.ne p)) i

/-- The sections of `μ_{p^i}` over a scheme over `Spec ℤ` are the `p^i`-th roots of unity in its
global sections, as groups. -/
noncomputable def rootsHomMulEquiv (p : ℕ) [NeZero p] (i : ℕ) (T : Over 𝒵) :
    (T ⟶ stratumGroup.{u} p (i : WithTop ℕ)) ≃* rootsUnitsSubgroup (A := Γ(T.left, ⊤)) (p ^ i) :=
  haveI : Fact (0 < p ^ i) := ⟨pow_pos_of_neZero p i⟩
  { toEquiv := rootsOverEquiv (p ^ i) (pow_pos_of_neZero p i) T
    map_mul' := ((yonedaMonObjIsoOfRepresentableBy _
      (rootsOfUnityGroupFunctor (p ^ i) ⋙ forget₂ GrpCat MonCat)
      (rootsOfUnityRepresentableBy (p ^ i) (pow_pos_of_neZero p i))).hom.app (op T)).hom.map_mul }

/-- The root of unity attached by `rootsHomMulEquiv` to a section of `μ_{p^i}` is the one given
by `rootsOverEquiv`. -/
theorem rootsHomMulEquiv_val (p : ℕ) [NeZero p] (i : ℕ) (T : Over 𝒵)
    (f : T ⟶ stratumGroup.{u} p (i : WithTop ℕ)) :
    (rootsHomMulEquiv p i T f).1 = (rootsOverEquiv (p ^ i) (pow_pos_of_neZero p i) T f).1 := rfl

/-- Restriction of sections of `μ_{p^i}` is restriction of units. -/
theorem rootsHomMulEquiv_comp (p : ℕ) [NeZero p] (i : ℕ) {T T' : Over 𝒵} (v : T ⟶ T')
    (f : T' ⟶ stratumGroup.{u} p (i : WithTop ℕ)) :
    (rootsHomMulEquiv p i T (v ≫ f)).1 =
      Units.map (Scheme.Γ.map v.left.op).hom.toMonoidHom (rootsHomMulEquiv p i T' f).1 :=
  congrArg Subtype.val ((rootsOfUnityRepresentableBy (p ^ i) (pow_pos_of_neZero p i)).homEquiv_comp
    v f)

/-- The coordinate `T` of `𝐆_m`, as a global function. -/
noncomputable def gmCoord : Γ(GmEquivariant.gm.{u}.left, ⊤) :=
  (Scheme.ΓSpecIso (.of (LaurentPolynomial (ULift.{u} ℤ)))).inv (LaurentPolynomial.T 1)

/-- The unit of a morphism to `𝐆_m` over `Spec ℤ`: the pullback of the coordinate `T`. -/
noncomputable def gmHomEquiv (T : Over 𝒵) : (T ⟶ GmEquivariant.gm.{u}) ≃ Γ(T.left, ⊤)ˣ :=
  (overSpecULiftZHomEquiv _ _).trans (specHomEquiv.trans (laurentHomEquiv _))

/-- The unit attached to a morphism `f` to `𝐆_m` is the pullback of the coordinate `T` along
`f`. -/
theorem gmHomEquiv_val (T : Over 𝒵) (f : T ⟶ GmEquivariant.gm.{u}) :
    (gmHomEquiv T f).val = f.left.appTop gmCoord :=
  rfl

/-- The sections of `𝐆_m` over a scheme over `Spec ℤ` are the units of its global sections, as
groups. -/
@[sga "3 X 8.4"]
noncomputable def gmHomMulEquiv (T : Over 𝒵) : (T ⟶ GmEquivariant.gm.{u}) ≃* Γ(T.left, ⊤)ˣ where
  toEquiv := gmHomEquiv T
  map_mul' f g := by
    apply Units.ext
    change (gmHomEquiv T (f * g)).val = (gmHomEquiv T f).val * (gmHomEquiv T g).val
    rw [gmHomEquiv_val, gmHomEquiv_val, gmHomEquiv_val]
    change (CartesianMonoidalCategory.lift f g ≫ MonObj.mul (X := GmEquivariant.gm.{u})).left.appTop
      gmCoord = f.left.appTop gmCoord * g.left.appTop gmCoord
    have hμ : (MonObj.mul (X := GmEquivariant.gm.{u})).left.appTop gmCoord =
        (CartesianMonoidalCategory.fst GmEquivariant.gm.{u} GmEquivariant.gm.{u}).left.appTop
            gmCoord *
          (CartesianMonoidalCategory.snd GmEquivariant.gm.{u} GmEquivariant.gm.{u}).left.appTop
            gmCoord :=
      GmEquivariant.gm_mul_appTop_laurent 1
    rw [GmEquivariant.appTop_comp_left, hμ, map_mul, ← GmEquivariant.appTop_comp_left,
      ← GmEquivariant.appTop_comp_left, CartesianMonoidalCategory.lift_fst,
      CartesianMonoidalCategory.lift_snd]

/-- The underlying map of `gmHomMulEquiv T` is `gmHomEquiv T`. -/
theorem gmHomMulEquiv_apply (T : Over 𝒵) (f : T ⟶ GmEquivariant.gm.{u}) :
    gmHomMulEquiv T f = gmHomEquiv T f := rfl

/-- Restriction of sections of `𝐆_m` is restriction of units. -/
theorem gmHomEquiv_comp {T T' : Over 𝒵} (v : T ⟶ T') (f : T' ⟶ GmEquivariant.gm.{u}) :
    gmHomEquiv T (v ≫ f) =
      Units.map (Scheme.Γ.map v.left.op).hom.toMonoidHom (gmHomEquiv T' f) := by
  apply Units.ext
  rw [gmHomEquiv_val, GmEquivariant.appTop_comp_left]
  rfl

/-- **The sections of the group of the stratum `X_a`** over a scheme `T` over `Spec ℤ`, as a
group: the `p^i`-th roots of unity of `Γ(T)` for `a = i`, all units of `Γ(T)` for `a = ∞`. -/
noncomputable def stratumHomMulEquiv [NeZero p] :
    ∀ (a : WithTop ℕ) (T : Over 𝒵),
      (T ⟶ stratumGroup.{u} p a) ≃* stratumUnits p a (A := Γ(T.left, ⊤))
  | ⊤, T => (gmHomMulEquiv T).trans Subgroup.topEquiv.symm
  | (i : ℕ), T => rootsHomMulEquiv p i T

/-- The identification of sections of the stratum group with units is natural. -/
theorem stratumHomMulEquiv_comp [NeZero p] (a : WithTop ℕ) {T T' : Over 𝒵} (v : T ⟶ T')
    (f : T' ⟶ stratumGroup.{u} p a) :
    (stratumHomMulEquiv p a T (v ≫ f)).1 =
      Units.map (Scheme.Γ.map v.left.op).hom.toMonoidHom (stratumHomMulEquiv p a T' f).1 := by
  induction a using WithTop.recTopCoe with
  | top => exact gmHomEquiv_comp v f
  | coe i => exact rootsHomMulEquiv_comp p i v f

end Groups

/-! ### Charts of objects of a stratum -/

section Charts

variable {𝒞 : BigFppfSite.{u}} {k : Type u} [CommRing k] {p : ℕ}
  {hU : 𝒞.Contains (Spec (.of (MvPolynomial ℕ k)))}

/-- The weighted quotient stack is a stack. -/
theorem isStack_weightedQuotientStack :
    (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsStack
      (BigFppfOver.topology 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)) :=
  (weightedQuotientStack.{u, w} 𝒞 k p hU).property.elim fun _ h => h.1.1

/-- The strata are stable under restriction. -/
theorem comp_mem_stratumSubfunctor (a : WithTop ℕ)
    {V W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (c : W ⟶ V) {h : V ⟶ totalSiteObject 𝒞 k hU} (hh : h ∈ (stratumSubfunctor hU a).obj (op V)) :
    c ≫ h ∈ (stratumSubfunctor hU a).obj (op W) :=
  (stratumSubfunctor hU a).map c.op hh

variable (p) in
/-- The chart object of `h` lies over the source of `h`. -/
theorem obj_chartObj {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (h : W ⟶ totalSiteObject 𝒞 k hU) :
    (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.obj (chartObj.{u, w} p h) = W :=
  (chart.{u, w} 𝒞 k p hU).hom.hom.w_obj (Over.mk h)

/-- **Two charts over the same base morphism are in the same orbit.** If the chart objects of
`h₁` and `h₂` both map to `ξ` over the same `g`, then `h₂ = γ • h₁` for a unit `γ`. -/
theorem exists_actMap_eq_of_lifts {V T : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    {g : V ⟶ T} {ξ : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.obj}
    {h₁ h₂ : V ⟶ totalSiteObject 𝒞 k hU} (φ₁ : chartObj.{u, w} p h₁ ⟶ ξ)
    (φ₂ : chartObj.{u, w} p h₂ ⟶ ξ)
    [(weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift g φ₁]
    [(weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift g φ₂] :
    ∃ t : (Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj V, ⊤))ˣ,
      actMap p t h₁ = h₂ := by
  obtain ⟨ε, hε, -⟩ :=
    (isFiberedInGroupoids_weightedQuotientStack.{u, w} p).exists_isHomLift_id_comp
    (g := g) φ₂ φ₁
  exact ⟨(chartVerticalEquiv.{u, w} p h₁ h₂ ⟨ε, hε⟩).1,
    (chartVerticalEquiv.{u, w} p h₁ h₂ ⟨ε, hε⟩).2⟩

/-- Two charts over the same base morphism have the same image in the coarse space. -/
theorem coarseMap_eq_of_lifts (a : WithTop ℕ)
    {V T : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    {g : V ⟶ T} {ξ : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.obj}
    {h₁ h₂ : V ⟶ totalSiteObject 𝒞 k hU} (hh₁ : h₁ ∈ (stratumSubfunctor hU a).obj (op V))
    (hh₂ : h₂ ∈ (stratumSubfunctor hU a).obj (op V)) (φ₁ : chartObj.{u, w} p h₁ ⟶ ξ)
    (φ₂ : chartObj.{u, w} p h₂ ⟶ ξ)
    [(weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift g φ₁]
    [(weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift g φ₂] :
    coarseMap p a ⟨h₁, hh₁⟩ = coarseMap p a ⟨h₂, hh₂⟩ := by
  obtain ⟨t, ht⟩ := exists_actMap_eq_of_lifts.{u, w} (g := g) φ₁ φ₂
  have e : (⟨h₂, hh₂⟩ : (stratumSubfunctor hU a).obj (op V)) =
      actMapStratum p a t ⟨h₁, hh₁⟩ := Subtype.ext ht.symm
  rw [e, coarseMap_actMapStratum]

end Charts

/-! ### The coarse 1-morphism -/

section Coarse

variable {𝒞 : BigFppfSite.{u}} {k : Type u} [CommRing k] {p : ℕ}
  {hU : 𝒞.Contains (Spec (.of (MvPolynomial ℕ k)))} (a : WithTop ℕ)
  {P : ObjectProperty (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.obj}
  (hPmor : ∀ ⦃x y : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.obj⦄, (x ⟶ y) → P y → P x)
  (hPchart : ∀ ⦃W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)⦄
    (h : W ⟶ totalSiteObject 𝒞 k hU),
    P (chartObj.{u, w} p h) ↔ h ∈ (stratumSubfunctor hU a).obj (op W))

include hPmor hPchart in
/-- The chart objects mapping to an object of the stratum are points of the stratum. -/
theorem mem_stratumSubfunctor_of_chart {ξ : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.obj}
    (hξ : P ξ) {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    {h : W ⟶ totalSiteObject 𝒞 k hU} (φ : chartObj.{u, w} p h ⟶ ξ) :
    h ∈ (stratumSubfunctor hU a).obj (op W) :=
  (hPchart h).1 (hPmor φ hξ)

/-- An object all of whose charts lie in the stratum is covered by charts of the stratum. -/
private theorem exists_covering_chart_mem {ξ : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.obj}
    (hmem : ∀ {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
      {h : W ⟶ totalSiteObject 𝒞 k hU}, (chartObj.{u, w} p h ⟶ ξ) →
        h ∈ (stratumSubfunctor hU a).obj (op W)) :
    ∃ R ∈ BigFppfOver.topology 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
        ((weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.obj ξ),
      ∀ ⦃V : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)⦄
        ⦃g : V ⟶ (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.obj ξ⦄, R.arrows g →
        ∃ (h : V ⟶ totalSiteObject 𝒞 k hU) (_ : h ∈ (stratumSubfunctor hU a).obj (op V))
          (φ : chartObj.{u, w} p h ⟶ ξ),
          (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift g φ := by
  obtain ⟨R, hR, hch⟩ := exists_chart_isHomLift.{u, w} 𝒞 k p hU
    ((weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.obj ξ) ⟨ξ, rfl⟩
  refine ⟨R, hR, fun V g hg => ?_⟩
  obtain ⟨h, φ, hφ⟩ := hch hg
  exact ⟨h, hmem φ, φ, hφ⟩

/-- The relation defining the coarse map: `z : V ⟶ M_a` is the coarse image of the restriction of
`ξ` along `g` when it computes the coarse image of every chart of a restriction of `ξ|_V`. -/
def CoarseRel (ξ : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.obj)
    ⦃V : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)⦄
    (g : V ⟶ (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.obj ξ)
    (z : V ⟶ coarseSiteObject hU a) : Prop :=
  ∀ ⦃W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)⦄ (c : W ⟶ V)
    (h : W ⟶ totalSiteObject 𝒞 k hU) (hh : h ∈ (stratumSubfunctor hU a).obj (op W))
    (φ : chartObj.{u, w} p h ⟶ ξ),
    (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift (c ≫ g) φ →
      coarseMap p a ⟨h, hh⟩ = c ≫ z

/-- The coarse image of a chart satisfies the defining relation. -/
theorem coarseRel_coarseMap {ξ : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.obj}
    {V : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (g : V ⟶ (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.obj ξ)
    (h : V ⟶ totalSiteObject 𝒞 k hU) (hh : h ∈ (stratumSubfunctor hU a).obj (op V))
    (φ : chartObj.{u, w} p h ⟶ ξ)
    [(weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift g φ] :
    CoarseRel.{u, w} a ξ g (coarseMap p a ⟨h, hh⟩) := by
  intro W c h' hh' φ' hφ'
  rw [← coarseMap_restrictStratum]
  exact coarseMap_eq_of_lifts.{u, w} a (g := c ≫ g) hh' _ φ' (chartHom.{u, w} p c rfl ≫ φ)

include hPmor hPchart in
/-- **The coarse map of an object of the stratum.** -/
theorem existsUnique_coarse {ξ : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.obj} (hξ : P ξ) :
    ∃! y : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.obj ξ ⟶ coarseSiteObject hU a,
      ∀ ⦃V : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)⦄
        (g : V ⟶ (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.obj ξ)
        (z : V ⟶ coarseSiteObject hU a), CoarseRel.{u, w} a ξ g z → z = g ≫ y := by
  obtain ⟨R, hR, hch⟩ := exists_covering_chart_mem.{u, w} a
    (mem_stratumSubfunctor_of_chart.{u, w} a hPmor hPchart hξ)
  refine Presheaf.existsUnique_of_locally (F := yoneda.obj (coarseSiteObject hU a))
    (BigFppfOver.isSheaf_yoneda_obj _ _ _ _) hR (CoarseRel.{u, w} a ξ) ?_ ?_ ?_
  · intro V g hg z z' hz hz'
    obtain ⟨h, hh, φ, hφ⟩ := hch hg
    have e1 := hz (𝟙 V) h hh φ (by rwa [Category.id_comp])
    have e2 := hz' (𝟙 V) h hh φ (by rwa [Category.id_comp])
    rw [Category.id_comp] at e1 e2
    exact e1.symm.trans e2
  · intro V W g c z hz W' c' h hh φ hφ
    show coarseMap p a ⟨h, hh⟩ = c' ≫ c ≫ z
    rw [← Category.assoc]
    exact hz (c' ≫ c) h hh φ (by rwa [Category.assoc])
  · intro V g hg
    obtain ⟨h, hh, φ, hφ⟩ := hch hg
    exact ⟨_, coarseRel_coarseMap.{u, w} a g h hh φ⟩

include hPmor hPchart in
/-- Two maps to the coarse space computing the coarse images of all charts agree. -/
theorem coarse_ext {ξ : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.obj} (hξ : P ξ)
    {y y' : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.obj ξ ⟶ coarseSiteObject hU a}
    (hy : ∀ ⦃V : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)⦄
      (g : V ⟶ (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.obj ξ)
      (h : V ⟶ totalSiteObject 𝒞 k hU) (hh : h ∈ (stratumSubfunctor hU a).obj (op V))
      (φ : chartObj.{u, w} p h ⟶ ξ),
      (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift g φ →
        coarseMap p a ⟨h, hh⟩ = g ≫ y)
    (hy' : ∀ ⦃V : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)⦄
      (g : V ⟶ (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.obj ξ)
      (h : V ⟶ totalSiteObject 𝒞 k hU) (hh : h ∈ (stratumSubfunctor hU a).obj (op V))
      (φ : chartObj.{u, w} p h ⟶ ξ),
      (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift g φ →
        coarseMap p a ⟨h, hh⟩ = g ≫ y') : y = y' := by
  obtain ⟨R, hR, hch⟩ := exists_covering_chart_mem.{u, w} a
    (mem_stratumSubfunctor_of_chart.{u, w} a hPmor hPchart hξ)
  apply ((isSheaf_iff_isSheaf_of_type _ _).1
    (BigFppfOver.isSheaf_yoneda_obj _ _ _ (coarseSiteObject hU a)) R hR).isSeparatedFor.ext
  intro V g hg
  obtain ⟨h, hh, φ, hφ⟩ := hch hg
  exact (hy g h hh φ hφ).symm.trans (hy' g h hh φ hφ)

include hPmor hPchart in
/-- **The coarse map of an object `ξ` of the stratum**, `T_ξ ⟶ M_a`: the unique morphism through
which the coarse image of every chart of a restriction of `ξ` factors. -/
noncomputable def coarseOf {ξ : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.obj} (hξ : P ξ) :
    (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.obj ξ ⟶ coarseSiteObject hU a :=
  (existsUnique_coarse.{u, w} a hPmor hPchart hξ).exists.choose

/-- Every coarse image `z` of the restriction of `ξ` along `g` factors as `g` followed by the
coarse map of `ξ`. -/
theorem coarseOf_spec {ξ : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.obj} (hξ : P ξ)
    ⦃V : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)⦄
    (g : V ⟶ (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.obj ξ)
    (z : V ⟶ coarseSiteObject hU a) (hz : CoarseRel.{u, w} a ξ g z) :
    z = g ≫ coarseOf.{u, w} a hPmor hPchart hξ :=
  (existsUnique_coarse.{u, w} a hPmor hPchart hξ).exists.choose_spec g z hz

/-- **The coarse map computes the coarse images of the charts.** -/
theorem coarseMap_eq_comp_coarseOf {ξ : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.obj}
    (hξ : P ξ) {V : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (g : V ⟶ (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.obj ξ)
    (h : V ⟶ totalSiteObject 𝒞 k hU) (hh : h ∈ (stratumSubfunctor hU a).obj (op V))
    (φ : chartObj.{u, w} p h ⟶ ξ)
    [(weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift g φ] :
    coarseMap p a ⟨h, hh⟩ = g ≫ coarseOf.{u, w} a hPmor hPchart hξ :=
  coarseOf_spec.{u, w} a hPmor hPchart hξ g _ (coarseRel_coarseMap.{u, w} a g h hh φ)

/-- The coarse map is characterised by computing the coarse images of the charts. -/
theorem eq_coarseOf {ξ : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.obj} (hξ : P ξ)
    (y : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.obj ξ ⟶ coarseSiteObject hU a)
    (hy : ∀ ⦃V : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)⦄
      (g : V ⟶ (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.obj ξ)
      (h : V ⟶ totalSiteObject 𝒞 k hU) (hh : h ∈ (stratumSubfunctor hU a).obj (op V))
      (φ : chartObj.{u, w} p h ⟶ ξ),
      (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift g φ →
        coarseMap p a ⟨h, hh⟩ = g ≫ y) :
    y = coarseOf.{u, w} a hPmor hPchart hξ :=
  coarse_ext.{u, w} a hPmor hPchart hξ hy fun _ g h hh φ hφ =>
    have := hφ
    coarseMap_eq_comp_coarseOf.{u, w} a hPmor hPchart hξ g h hh φ

/-- **The coarse maps are compatible with the morphisms of the stratum.** -/
theorem map_comp_coarseOf {ξ ξ' : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.obj}
    (f : ξ ⟶ ξ') (hξ : P ξ) (hξ' : P ξ') :
    (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.map f ≫
        coarseOf.{u, w} a hPmor hPchart hξ' = coarseOf.{u, w} a hPmor hPchart hξ := by
  refine eq_coarseOf.{u, w} a hPmor hPchart hξ _ fun V g h hh φ hφ => ?_
  have := hφ
  rw [← Category.assoc]
  exact coarseMap_eq_comp_coarseOf.{u, w} a hPmor hPchart hξ' _ h hh (φ ≫ f)

/-- The coarse map of a chart object is the coarse image of its point. -/
theorem coarseOf_chartObj {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (h : W ⟶ totalSiteObject 𝒞 k hU) (hh : h ∈ (stratumSubfunctor hU a).obj (op W)) :
    coarseOf.{u, w} a hPmor hPchart ((hPchart h).2 hh) =
      eqToHom (obj_chartObj.{u, w} p h) ≫ coarseMap p a ⟨h, hh⟩ := by
  have : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift
      (eqToHom (obj_chartObj.{u, w} p h).symm) (𝟙 (chartObj.{u, w} p h)) :=
    IsHomLift.id_lift_eqToHom_domain _ (obj_chartObj.{u, w} p h)
  rw [coarseMap_eq_comp_coarseOf.{u, w} a hPmor hPchart ((hPchart h).2 hh)
    (eqToHom (obj_chartObj.{u, w} p h).symm) h hh (𝟙 _), eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp]

/-- **The coarse 1-morphism of the stratum, as a functor.** -/
noncomputable def coarseFunctor : P.FullSubcategory ⥤ Over (coarseSiteObject hU a) where
  obj x := Over.mk (coarseOf.{u, w} a hPmor hPchart x.property)
  map {x y} f := Over.homMk ((weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.map f.hom)
    (map_comp_coarseOf.{u, w} a hPmor hPchart f.hom x.property y.property)
  map_id _ := Over.OverMorphism.ext ((weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.map_id _)
  map_comp _ _ :=
    Over.OverMorphism.ext ((weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.map_comp _ _)

/-- **The coarse 1-morphism of the stratum**, as a functor over the site. -/
noncomputable def coarseBased :
    Stack.fullSubcategoryBased (weightedQuotientStack.{u, w} 𝒞 k p hU) P ⥤ᵇ
      (Stack.schemeFibredCategory 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
        (coarseSiteObject hU a)).val where
  toFunctor := coarseFunctor.{u, w} a hPmor hPchart
  w := rfl

/-- **The coarse 1-morphism `𝒳_a ⟶ M_a` of the stratum.** -/
noncomputable def coarse
    (hP : Stack.IsAlgebraicStack.{u, w} 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
      (Stack.fullSubcategoryBased (weightedQuotientStack.{u, w} 𝒞 k p hU) P)) :
    Stack.fullSubcategoryAlgebraicStack (weightedQuotientStack.{u, w} 𝒞 k p hU) P hP ⟶
      Stack.schemeStack.{u, w} 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) (coarseSiteObject hU a) :=
  Bicategory.InducedBicategory.mkHom
    (Bicategory.InducedBicategory.mkHom (coarseBased.{u, w} a hPmor hPchart))

/-- Two objects of the stratum with the same coarse image are fppf locally isomorphic. -/
theorem locally_iso_of_coarseOf_eq [NeZero p] {U : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    {x x' : P.FullSubcategory}
    (hx : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.obj x.obj = U)
    (hx' : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.obj x'.obj = U)
    (he : eqToHom hx.symm ≫ coarseOf.{u, w} a hPmor hPchart x.property =
      eqToHom hx'.symm ≫ coarseOf.{u, w} a hPmor hPchart x'.property) :
    ∃ S ∈ BigFppfOver.topology 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) U,
      ∀ ⦃V : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)⦄ (f : V ⟶ U), S f →
        ∃ (z z' : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.obj) (_ : P z) (_ : P z')
          (ξ : z ⟶ x.obj) (ξ' : z' ⟶ x'.obj) (α : z ⟶ z'),
          (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift f ξ ∧
          (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift f ξ' ∧
          (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift (𝟙 V) α := by
  obtain ⟨R₁, hR₁, h₁⟩ := exists_chart_isHomLift.{u, w} 𝒞 k p hU U ⟨x.obj, hx⟩
  obtain ⟨R₂, hR₂, h₂⟩ := exists_chart_isHomLift.{u, w} 𝒞 k p hU U ⟨x'.obj, hx'⟩
  refine GrothendieckTopology.exists_covering_of_refine _
    (GrothendieckTopology.intersection_covering _ hR₁ hR₂) ?_
  intro V f hf
  obtain ⟨k₁, φ₁, hφ₁⟩ := h₁ hf.1
  obtain ⟨k₂, φ₂, hφ₂⟩ := h₂ hf.2
  have hk₁ := mem_stratumSubfunctor_of_chart.{u, w} a hPmor hPchart x.property φ₁
  have hk₂ := mem_stratumSubfunctor_of_chart.{u, w} a hPmor hPchart x'.property φ₂
  have hc : coarseMap p a ⟨k₁, hk₁⟩ = coarseMap p a ⟨k₂, hk₂⟩ := by
    rw [coarseMap_eq_comp_coarseOf.{u, w} a hPmor hPchart x.property (f ≫ eqToHom hx.symm) k₁
        hk₁ φ₁,
      coarseMap_eq_comp_coarseOf.{u, w} a hPmor hPchart x'.property (f ≫ eqToHom hx'.symm) k₂
        hk₂ φ₂, Category.assoc, Category.assoc, he]
  obtain ⟨R', hR', hR'g⟩ := exists_covering_actMap_eq p (Nat.pos_of_ne_zero (NeZero.ne p)) a
    ⟨k₁, hk₁⟩ ⟨k₂, hk₂⟩ hc
  refine ⟨R', hR', fun W c hc' => ?_⟩
  obtain ⟨t, ht⟩ := hR'g c hc'
  have hk₁' := comp_mem_stratumSubfunctor a c hk₁
  have hk₂' := comp_mem_stratumSubfunctor a c hk₂
  let θ := (chartVerticalEquiv.{u, w} p (c ≫ k₁) (c ≫ k₂)).symm ⟨t, ht⟩
  have hθ : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift (𝟙 W) θ.1 := θ.2
  have l₁ : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift (c ≫ f)
      (chartHom.{u, w} p c rfl ≫ φ₁) := inferInstance
  have l₂ : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift (c ≫ f)
      (chartHom.{u, w} p c rfl ≫ φ₂) := inferInstance
  exact ⟨_, _, (hPchart _).2 hk₁', (hPchart _).2 hk₂', _, _, _, l₁, l₂, hθ⟩

omit [CommRing k] in
/-- A composite of `eqToHom`s through an object `U`, followed by `c`, simplifies to the direct
`eqToHom` followed by `c`. -/
theorem eqToHom_symm_comp_fac {C : Type*} [Category C] {A B U Z : C} (hx : A = U) (hx' : B = U)
    (c : B ⟶ Z) : eqToHom hx.symm ≫ (eqToHom hx ≫ 𝟙 U ≫ eqToHom hx'.symm) ≫ c =
      eqToHom hx'.symm ≫ c := by
  subst hx hx'
  simp

omit [CommRing k] in
/-- If `ξ` and `ξ'` lie over the same `f : V ⟶ U`, `α` is vertical, and the images of the targets
of `ξ` and `ξ'` are both identified with `U`, then the square of images of `α`, `ξ'`, `ξ` and the
induced morphism `bl` commutes. -/
theorem square_aux {𝒮 𝒳 : Type*} [Category 𝒮] [Category 𝒳] {q : 𝒳 ⥤ 𝒮} {U V : 𝒮}
    {x x' z z' : 𝒳} {f : V ⟶ U} (hx : q.obj x = U) (hx' : q.obj x' = U) {bl : q.obj x ⟶ q.obj x'}
    (hfac : bl = eqToHom hx ≫ 𝟙 U ≫ eqToHom hx'.symm) (ξ : z ⟶ x) (ξ' : z' ⟶ x') (α : z ⟶ z')
    [q.IsHomLift f ξ] [q.IsHomLift f ξ'] [q.IsHomLift (𝟙 V) α] :
    q.map α ≫ q.map ξ' = q.map ξ ≫ bl := by
  subst hx
  rw [hfac, IsHomLift.fac' q (𝟙 V) α, IsHomLift.fac' q f ξ', IsHomLift.fac' q f ξ]
  simp

/-- **Stacks 06RE: the stratum `𝒳_a` is a gerbe over its coarse space `M_a`.** Every object of
`M_a` is, after no refinement at all, the coarse image of a chart object (the coarse maps have
sections); and two objects of the stratum with the same coarse image are fppf locally isomorphic,
since two points of `X_a` with the same image in `M_a` are fppf locally in the same orbit. -/
theorem isGerbeOver_coarse [NeZero p]
    (hP : Stack.IsAlgebraicStack.{u, w} 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
      (Stack.fullSubcategoryBased (weightedQuotientStack.{u, w} 𝒞 k p hU) P)) :
    Stack.AlgebraicStacks.IsGerbeOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
      (coarse.{u, w} a hPmor hPchart hP) := by
  refine ⟨(Stack.schemeStack.{u, w} 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
      (coarseSiteObject hU a)).val.isFiberedInGroupoids,
    (Stack.fullSubcategoryAlgebraicStack (weightedQuotientStack.{u, w} 𝒞 k p hU) P
      hP).val.isFiberedInGroupoids, ?_, ?_⟩
  · intro U y hy
    refine ⟨⊤, GrothendieckTopology.top_mem _ _, fun V f _ => ?_⟩
    subst hy
    let s := coarseSection a (f ≫ y.hom)
    refine ⟨⟨chartObj.{u, w} p s.1, (hPchart s.1).2 s.2⟩,
      Over.homMk (eqToHom (obj_chartObj.{u, w} p s.1) ≫ f) ?_, ?_⟩
    · show _ = coarseOf.{u, w} a hPmor hPchart ((hPchart s.1).2 s.2)
      rw [coarseOf_chartObj.{u, w} a hPmor hPchart s.1 s.2]
      exact (Category.assoc _ _ _).trans
        (congrArg _ (coarseMap_coarseSection p a (f ≫ y.hom)).symm)
    · exact IsHomLift.of_fac' _ f _ (obj_chartObj.{u, w} p s.1) rfl
        (by rw [eqToHom_refl, Category.comp_id]; rfl)
  · intro U x x' b hb
    have hb' : (Over.forget (coarseSiteObject hU a)).IsHomLift (𝟙 U) b := hb
    have hx : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.obj x.obj = U :=
      IsHomLift.domain_eq (Over.forget (coarseSiteObject hU a)) (𝟙 U) b
    have hx' : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.obj x'.obj = U :=
      IsHomLift.codomain_eq (Over.forget (coarseSiteObject hU a)) (𝟙 U) b
    have hfac : b.left = eqToHom hx ≫ 𝟙 U ≫ eqToHom hx'.symm :=
      IsHomLift.fac' (Over.forget (coarseSiteObject hU a)) (𝟙 U) b
    have hw : b.left ≫ coarseOf.{u, w} a hPmor hPchart x'.property =
        coarseOf.{u, w} a hPmor hPchart x.property := Over.w b
    have he : eqToHom hx.symm ≫ coarseOf.{u, w} a hPmor hPchart x.property =
        eqToHom hx'.symm ≫ coarseOf.{u, w} a hPmor hPchart x'.property := by
      rw [← hw, hfac]
      exact eqToHom_symm_comp_fac hx hx' _
    obtain ⟨S, hS, hloc⟩ := locally_iso_of_coarseOf_eq.{u, w} a hPmor hPchart (x := x) (x' := x')
      hx hx' he
    refine ⟨S, hS, fun V f hf => ?_⟩
    obtain ⟨z, z', hz, hz', ξ, ξ', α, hξ, hξ', hα⟩ := hloc f hf
    have key : ∀ {z₁ z₂ : P.FullSubcategory} {V₁ V₂ : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
        {g : V₁ ⟶ V₂} (φ : z₁ ⟶ z₂),
        (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift g φ.hom →
        (CatFiberedInGroupoids.homFunctor (coarse.{u, w} a hPmor hPchart hP).hom ⋙
          (Stack.schemeStack.{u, w} 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
            (coarseSiteObject hU a)).val.val.p).IsHomLift g φ :=
      fun φ h => (Functor.isHomLift_comp_iff P.ι
        (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p _ φ).2 h
    refine ⟨⟨z, hz⟩, ⟨z', hz'⟩, ObjectProperty.homMk ξ, ObjectProperty.homMk ξ',
      ObjectProperty.homMk α, key _ hξ, key _ hξ', key _ hα, Over.OverMorphism.ext ?_⟩
    exact square_aux (f := f) hx hx' hfac ξ ξ' α

end Coarse

/-! ### Gluing units -/

section Units

variable {𝒞 : BigFppfSite.{u}}

/-- The units of the global sections, restricted along a morphism of the site. -/
noncomputable abbrev restrictUnits {V W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (g : V ⟶ W) (t : (Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤))ˣ) :
    (Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj V, ⊤))ˣ :=
  Units.map (restrict g).toMonoidHom t

/-- Restriction of units along the identity is the identity. -/
theorem restrictUnits_id {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (t : (Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤))ˣ) :
    restrictUnits (𝟙 W) t = t := by
  apply Units.ext
  simp [restrict]

/-- Restriction of units along a composite is the composite of the restrictions. -/
theorem restrictUnits_comp {V V' W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (c : V' ⟶ V) (g : V ⟶ W)
    (t : (Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤))ˣ) :
    restrictUnits (c ≫ g) t = restrictUnits c (restrictUnits g t) :=
  Units.ext (restrict_comp c g t.1)

/-- The presheaf of points of `𝐆_m` is a sheaf. -/
theorem isSheaf_gmPoints :
    Presheaf.IsSheaf (BigFppfOver.topology 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)) (gmPoints 𝒞) :=
  (Presheaf.isSheaf_of_iso_iff (Space.pointsOnSiteRepresentableBy 𝒞 𝒵 _ _ _).toIso).1
    (BigFppfOver.isSheaf_yoneda_obj _ _ _ _)

/-- The point of `𝐆_m` attached to a unit is natural: restricting it along `g` gives the point
attached to the restricted unit. -/
theorem gmUnitsEquiv_symm_naturality {V W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (g : V ⟶ W) (t : (Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤))ˣ) :
    (gmPoints 𝒞).map g.op ((gmUnitsEquiv W).symm t) =
      (gmUnitsEquiv V).symm (restrictUnits g t) := by
  apply (gmUnitsEquiv V).injective
  rw [gmUnitsEquiv_naturality, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- **Units are separated for the fppf topology.** -/
theorem units_ext_of_locally {T : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)} {R : Sieve T}
    (hR : R ∈ BigFppfOver.topology 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) T)
    {t t' : (Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj T, ⊤))ˣ}
    (h : ∀ ⦃V : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)⦄ (g : V ⟶ T), R g →
      restrictUnits g t = restrictUnits g t') : t = t' := by
  apply (gmUnitsEquiv T).symm.injective
  apply ((isSheaf_iff_isSheaf_of_type _ _).1 isSheaf_gmPoints R hR).isSeparatedFor.ext
  intro V g hg
  rw [gmUnitsEquiv_symm_naturality, gmUnitsEquiv_symm_naturality, h g hg]

/-- **Units glue for the fppf topology**, from a local relation. -/
theorem units_existsUnique_of_locally {T : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    {R : Sieve T} (hR : R ∈ BigFppfOver.topology 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) T)
    (Q : ∀ ⦃V : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)⦄, (V ⟶ T) →
      (Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj V, ⊤))ˣ → Prop)
    (hfun : ∀ ⦃V : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)⦄ (g : V ⟶ T), R g →
      ∀ s s', Q g s → Q g s' → s = s')
    (hres : ∀ ⦃V W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)⦄ (g : V ⟶ T) (c : W ⟶ V) (s),
      Q g s → Q (c ≫ g) (restrictUnits c s))
    (hloc : ∀ ⦃V : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)⦄ (g : V ⟶ T), R g → ∃ s, Q g s) :
    ∃ t : (Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj T, ⊤))ˣ,
      ∀ ⦃V : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)⦄ (g : V ⟶ T) (s), Q g s →
        s = restrictUnits g t := by
  obtain ⟨y, hy, -⟩ := Presheaf.existsUnique_of_locally isSheaf_gmPoints hR
    (fun V g m => Q g (gmUnitsEquiv V m))
    (fun V g hg m m' hm hm' => (gmUnitsEquiv V).injective (hfun g hg _ _ hm hm'))
    (fun V W g c m hm => by
      rw [gmUnitsEquiv_naturality]
      exact hres g c _ hm)
    (fun V g hg => by
      obtain ⟨s, hs⟩ := hloc g hg
      exact ⟨(gmUnitsEquiv V).symm s, by simpa using hs⟩)
  refine ⟨gmUnitsEquiv T y, fun V g s hs => ?_⟩
  apply (gmUnitsEquiv V).symm.injective
  rw [← gmUnitsEquiv_symm_naturality, Equiv.symm_apply_apply]
  exact hy g ((gmUnitsEquiv V).symm s) (by simpa using hs)

end Units

/-! ### The action of the band on chart objects -/

section ChartAction

variable {𝒞 : BigFppfSite.{u}} {k : Type u} [CommRing k] {p : ℕ}
  {hU : 𝒞.Contains (Spec (.of (MvPolynomial ℕ k)))}

/-- A unit of the stratum group fixes the points of the stratum. -/
theorem actMap_eq_self_of_mem_stratumUnits (a : WithTop ℕ)
    {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    {t : (Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤))ˣ}
    (ht : t ∈ stratumUnits p a) {h : W ⟶ totalSiteObject 𝒞 k hU}
    (hh : h ∈ (stratumSubfunctor hU a).obj (op W)) : actMap p t h = h := by
  induction a using WithTop.recTopCoe with
  | top => exact actMap_eq_self_of_top p t hh
  | coe i => exact (actMap_eq_self_iff_coe p t hh).2 ht

/-- A unit fixing a point of the stratum is a unit of the stratum group. -/
theorem mem_stratumUnits_of_actMap_eq_self (a : WithTop ℕ)
    {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    {t : (Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤))ˣ}
    {h : W ⟶ totalSiteObject 𝒞 k hU} (hh : h ∈ (stratumSubfunctor hU a).obj (op W))
    (ht : actMap p t h = h) : t ∈ stratumUnits p a := by
  induction a using WithTop.recTopCoe with
  | top => exact Subgroup.mem_top t
  | coe i => exact (actMap_eq_self_iff_coe p t hh).1 ht

/-- The vertical automorphism of the chart object of `h` given by a unit `t` fixing `h`. -/
noncomputable def chartAct {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (h : W ⟶ totalSiteObject 𝒞 k hU)
    (t : (Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤))ˣ)
    (ht : actMap p t h = h) : chartObj.{u, w} p h ⟶ chartObj.{u, w} p h :=
  ((chartVerticalEquiv.{u, w} p h h).symm ⟨t, ht⟩).1

/-- The action of a unit on a chart object lies over the identity. -/
instance isHomLift_chartAct {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (h : W ⟶ totalSiteObject 𝒞 k hU)
    (t : (Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤))ˣ)
    (ht : actMap p t h = h) :
    (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift (𝟙 W) (chartAct.{u, w} h t ht) :=
  ((chartVerticalEquiv.{u, w} p h h).symm ⟨t, ht⟩).2

/-- Equal units act by equal automorphisms of a chart object. -/
theorem chartAct_congr {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (h : W ⟶ totalSiteObject 𝒞 k hU)
    {t t' : (Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤))ˣ}
    (e : t = t') (ht : actMap p t h = h) (ht' : actMap p t' h = h) :
    chartAct.{u, w} h t ht = chartAct.{u, w} h t' ht' := by
  subst e
  rfl

/-- The unit corresponding to the action of `t` on a chart object is `t`. -/
theorem chartVerticalEquiv_chartAct {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (h : W ⟶ totalSiteObject 𝒞 k hU)
    (t : (Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤))ˣ)
    (ht : actMap p t h = h) :
    (chartVerticalEquiv.{u, w} p h h ⟨chartAct.{u, w} h t ht, inferInstance⟩).1 = t := by
  show (chartVerticalEquiv.{u, w} p h h ((chartVerticalEquiv.{u, w} p h h).symm ⟨t, ht⟩)).1 = t
  rw [Equiv.apply_symm_apply]

/-- A vertical endomorphism of a chart object is the action of its unit. -/
theorem eq_chartAct {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (h : W ⟶ totalSiteObject 𝒞 k hU) (θ : chartObj.{u, w} p h ⟶ chartObj.{u, w} p h)
    (hθ : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift (𝟙 W) θ) :
    θ = chartAct.{u, w} h (chartVerticalEquiv.{u, w} p h h ⟨θ, hθ⟩).1
      (chartVerticalEquiv.{u, w} p h h ⟨θ, hθ⟩).2 := by
  show θ = ((chartVerticalEquiv.{u, w} p h h).symm (chartVerticalEquiv.{u, w} p h h ⟨θ, hθ⟩)).1
  rw [Equiv.symm_apply_apply]

/-- The action of units on a chart object is injective. -/
theorem chartAct_injective {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (h : W ⟶ totalSiteObject 𝒞 k hU)
    {t t' : (Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤))ˣ}
    (ht : actMap p t h = h) (ht' : actMap p t' h = h)
    (e : chartAct.{u, w} h t ht = chartAct.{u, w} h t' ht') : t = t' := by
  rw [← chartVerticalEquiv_chartAct.{u, w} h t ht, ← chartVerticalEquiv_chartAct.{u, w} h t' ht']
  exact congrArg (fun θ => (chartVerticalEquiv.{u, w} p h h θ).1) (Subtype.ext e)

/-- Composing vertical morphisms of chart objects multiplies their units. -/
theorem chartVerticalEquiv_comp' {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    {h h' h'' : W ⟶ totalSiteObject 𝒞 k hU} (θ : chartObj.{u, w} p h ⟶ chartObj.{u, w} p h')
    (θ' : chartObj.{u, w} p h' ⟶ chartObj.{u, w} p h'')
    (hθ : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift (𝟙 W) θ)
    (hθ' : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift (𝟙 W) θ')
    (hθθ' : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift (𝟙 W) (θ ≫ θ')) :
    (chartVerticalEquiv.{u, w} p h h'' ⟨θ ≫ θ', hθθ'⟩).1 =
      (chartVerticalEquiv.{u, w} p h' h'' ⟨θ', hθ'⟩).1 *
        (chartVerticalEquiv.{u, w} p h h' ⟨θ, hθ⟩).1 :=
  chartVerticalEquiv_comp.{u, w} p ⟨θ, hθ⟩ ⟨θ', hθ'⟩

/-- **Vertical morphisms of chart objects commute with the action of units.** -/
theorem chartAct_comp_eq_comp_chartAct {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    {h h' : W ⟶ totalSiteObject 𝒞 k hU} (θ : chartObj.{u, w} p h ⟶ chartObj.{u, w} p h')
    (hθ : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift (𝟙 W) θ)
    (t : (Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤))ˣ)
    (ht : actMap p t h = h) (ht' : actMap p t h' = h') :
    chartAct.{u, w} h t ht ≫ θ = θ ≫ chartAct.{u, w} h' t ht' := by
  have h1 : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift (𝟙 W)
      (chartAct.{u, w} h t ht ≫ θ) := inferInstance
  have h2 : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift (𝟙 W)
      (θ ≫ chartAct.{u, w} h' t ht') := inferInstance
  have e := chartVerticalEquiv_comp'.{u, w} (chartAct.{u, w} h t ht) θ inferInstance hθ h1
  have e' := chartVerticalEquiv_comp'.{u, w} θ (chartAct.{u, w} h' t ht') hθ inferInstance h2
  rw [chartVerticalEquiv_chartAct] at e
  rw [chartVerticalEquiv_chartAct] at e'
  have := (chartVerticalEquiv.{u, w} p h h').injective (Subtype.ext ((e.trans (mul_comm _ _)).trans
    e'.symm) : chartVerticalEquiv.{u, w} p h h' ⟨_, h1⟩ = chartVerticalEquiv.{u, w} p h h' ⟨_, h2⟩)
  exact congrArg Subtype.val this

/-- The action of `t` followed by that of `t'` on a chart object is the action of `t * t'`. -/
theorem chartAct_comp {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (h : W ⟶ totalSiteObject 𝒞 k hU)
    (t t' : (Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤))ˣ)
    (ht : actMap p t h = h) (ht' : actMap p t' h = h) (htt' : actMap p (t * t') h = h) :
    chartAct.{u, w} h t ht ≫ chartAct.{u, w} h t' ht' = chartAct.{u, w} h (t * t') htt' := by
  have h1 : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift (𝟙 W)
      (chartAct.{u, w} h t ht ≫ chartAct.{u, w} h t' ht') := inferInstance
  rw [eq_chartAct.{u, w} h _ h1]
  refine chartAct_congr.{u, w} h ?_ _ _
  rw [chartVerticalEquiv_comp'.{u, w} _ _ inferInstance inferInstance h1,
    chartVerticalEquiv_chartAct,
    chartVerticalEquiv_chartAct, mul_comm]

/-- The unit `1` acts on a chart object by the identity. -/
theorem chartAct_one {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (h : W ⟶ totalSiteObject 𝒞 k hU) (ht : actMap p 1 h = h) :
    chartAct.{u, w} h 1 ht = 𝟙 _ := by
  have h1 : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift (𝟙 W)
      (𝟙 (chartObj.{u, w} p h)) := IsHomLift.id (obj_chartObj.{u, w} p h)
  rw [eq_chartAct.{u, w} h _ h1]
  exact chartAct_congr.{u, w} h (chartVerticalEquiv_id.{u, w} p h).symm _ _

/-- **The action of units on chart objects is central and compatible with restriction.** -/
theorem comp_chartAct {V V' : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)} {c : V' ⟶ V}
    {h : V ⟶ totalSiteObject 𝒞 k hU} {h' : V' ⟶ totalSiteObject 𝒞 k hU}
    (χ : chartObj.{u, w} p h' ⟶ chartObj.{u, w} p h)
    [(weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift c χ]
    (t : (Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj V, ⊤))ˣ)
    (ht : actMap p t h = h) (ht' : actMap p (restrictUnits c t) h' = h') :
    χ ≫ chartAct.{u, w} h t ht = chartAct.{u, w} h' (restrictUnits c t) ht' ≫ χ := by
  obtain ⟨θ, hθ, hθχ⟩ :=
    (isFiberedInGroupoids_weightedQuotientStack.{u, w} p).exists_isHomLift_id_comp
    (g := c) (chartHom.{u, w} p c (rfl : c ≫ h = c ≫ h)) χ
  have hr := chartMap_comp_chartVerticalEquiv_symm.{u, w} p c (⟨t, ht⟩ :
    {s : (Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj V, ⊤))ˣ //
      actMap p s h = h})
  have hfix : actMap p (restrictUnits c t) (c ≫ h) = c ≫ h := by
    rw [← comp_actMap, ht]
  change chartHom.{u, w} p c rfl ≫ chartAct.{u, w} h t ht =
    chartAct.{u, w} (c ≫ h) (restrictUnits c t) hfix ≫ chartHom.{u, w} p c rfl at hr
  rw [← hθχ, Category.assoc, hr, ← Category.assoc,
    ← chartAct_comp_eq_comp_chartAct.{u, w} θ hθ (restrictUnits c t) ht' hfix, Category.assoc]

end ChartAction

/-! ### The band -/

section Band

variable {𝒞 : BigFppfSite.{u}} {k : Type u} [CommRing k] {p : ℕ}
  {hU : 𝒞.Contains (Spec (.of (MvPolynomial ℕ k)))}

omit [CommRing k] in
/-- If `φ` lies over `g` and `χ ≫ φ` lies over `b`, then `χ` lies over some `c` with
`c ≫ g = b`. -/
theorem exists_isHomLift_comp_eq {𝒮 𝒳 : Type*} [Category 𝒮] [Category 𝒳] (q : 𝒳 ⥤ 𝒮)
    {R S T : 𝒮} {x y z : 𝒳} (χ : x ⟶ y) (φ : y ⟶ z) (g : S ⟶ T) (b : R ⟶ T)
    [q.IsHomLift g φ] [q.IsHomLift b (χ ≫ φ)] : ∃ c : R ⟶ S, q.IsHomLift c χ ∧ c ≫ g = b := by
  obtain rfl : q.obj x = R := IsHomLift.domain_eq q b (χ ≫ φ)
  obtain rfl : q.obj y = S := IsHomLift.domain_eq q g φ
  obtain rfl : q.obj z = T := IsHomLift.codomain_eq q g φ
  refine ⟨q.map χ, inferInstance, ?_⟩
  rw [IsHomLift.eq_of_isHomLift (p := q) g φ, IsHomLift.eq_of_isHomLift (p := q) b (χ ≫ φ),
    Functor.map_comp]

omit [CommRing k] in
/-- A morphism with the same image as a morphism lying over `g` also lies over `g`. -/
theorem isHomLift_of_map_eq {𝒮 𝒳 : Type*} [Category 𝒮] [Category 𝒳] (q : 𝒳 ⥤ 𝒮)
    {R S : 𝒮} {x y : 𝒳} {φ ψ : x ⟶ y} {g : R ⟶ S} (hφ : q.IsHomLift g φ)
    (e : q.map ψ = q.map φ) : q.IsHomLift g ψ := by
  have := hφ
  exact IsHomLift.of_fac' q g ψ (IsHomLift.domain_eq q g φ) (IsHomLift.codomain_eq q g φ)
    (e.trans (IsHomLift.fac' q g φ))

variable (a : WithTop ℕ)
  {P : ObjectProperty (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.obj}
  (hPmor : ∀ ⦃x y : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.obj⦄, (x ⟶ y) → P y → P x)
  (hPchart : ∀ ⦃W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)⦄
    (h : W ⟶ totalSiteObject 𝒞 k hU),
    P (chartObj.{u, w} p h) ↔ h ∈ (stratumSubfunctor hU a).obj (op W))

/-- The units of the stratum group over the base of `ξ`. -/
noncomputable abbrev baseUnits (ξ : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.obj) :
    Subgroup (Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj
      ((weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.obj ξ), ⊤))ˣ :=
  stratumUnits p a

/-- The restriction of a unit of the stratum group fixes every point of the stratum. -/
theorem actMap_restrictUnits {ξ : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.obj}
    {t : (Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj
      ((weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.obj ξ), ⊤))ˣ}
    (ht : t ∈ baseUnits.{u, w} a ξ) {V : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (g : V ⟶ (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.obj ξ)
    {h : V ⟶ totalSiteObject 𝒞 k hU} (hh : h ∈ (stratumSubfunctor hU a).obj (op V)) :
    actMap p (restrictUnits g t) h = h :=
  actMap_eq_self_of_mem_stratumUnits a (map_mem_stratumUnits p a (restrict g) ht) hh

/-- The relation defining the automorphism of `ξ` attached to a unit `t` of the stratum group:
`ψ` is `φ` followed by `t`, read on every chart of the source of `φ`. -/
def BandRel {ξ : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.obj}
    {t : (Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj
      ((weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.obj ξ), ⊤))ˣ}
    (ht : t ∈ baseUnits.{u, w} a ξ) ⦃x' : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.obj⦄
    (φ ψ : x' ⟶ ξ) : Prop :=
  (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.map ψ =
      (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.map φ ∧
    ∀ ⦃W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)⦄ (h : W ⟶ totalSiteObject 𝒞 k hU)
      (hh : h ∈ (stratumSubfunctor hU a).obj (op W)) (χ : chartObj.{u, w} p h ⟶ x')
      (b : W ⟶ (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.obj ξ),
      (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift b (χ ≫ φ) →
        χ ≫ ψ = chartAct.{u, w} h (restrictUnits b t) (actMap_restrictUnits.{u, w} a ht b hh) ≫
          χ ≫ φ

/-- The relation holds on every chart. -/
theorem bandRel_chart {ξ : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.obj}
    {t : (Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj
      ((weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.obj ξ), ⊤))ˣ}
    (ht : t ∈ baseUnits.{u, w} a ξ) {V : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (g : V ⟶ (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.obj ξ)
    (h : V ⟶ totalSiteObject 𝒞 k hU) (hh : h ∈ (stratumSubfunctor hU a).obj (op V))
    (φ : chartObj.{u, w} p h ⟶ ξ)
    [(weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift g φ] :
    BandRel.{u, w} a ht φ
      (chartAct.{u, w} h (restrictUnits g t) (actMap_restrictUnits.{u, w} a ht g hh) ≫ φ) := by
  refine ⟨?_, fun W h' hh' χ b hb => ?_⟩
  · rw [Functor.map_comp, IsHomLift.fac' _ (𝟙 V) (chartAct.{u, w} h _ _)]
    simp
  · obtain ⟨c, hc, hcg⟩ := exists_isHomLift_comp_eq
      (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p χ φ g b
    have := hc
    rw [← Category.assoc, comp_chartAct.{u, w} χ (restrictUnits g t)
        (actMap_restrictUnits.{u, w} a ht g hh)
        (by rw [← restrictUnits_comp, hcg]; exact actMap_restrictUnits.{u, w} a ht b hh'),
      Category.assoc]
    congr 1
    exact chartAct_congr.{u, w} h' (by rw [← restrictUnits_comp, hcg]) _ _

/-- The defining property of the automorphism of `ξ` attached to a unit `t`. -/
def IsBandHom {ξ : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.obj}
    {t : (Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj
      ((weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.obj ξ), ⊤))ˣ}
    (ht : t ∈ baseUnits.{u, w} a ξ) (m : ξ ⟶ ξ) : Prop :=
  ∀ ⦃V : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)⦄
    (g : V ⟶ (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.obj ξ)
    (h : V ⟶ totalSiteObject 𝒞 k hU) (hh : h ∈ (stratumSubfunctor hU a).obj (op V))
    (φ : chartObj.{u, w} p h ⟶ ξ), (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift g φ →
      φ ≫ m = chartAct.{u, w} h (restrictUnits g t) (actMap_restrictUnits.{u, w} a ht g hh) ≫ φ

include hPmor hPchart in
/-- **The automorphism of an object of the stratum attached to a unit of the stratum group**,
glued in the stack from its action on the charts. -/
theorem exists_bandHom {ξ : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.obj} (hξ : P ξ)
    {t : (Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj
      ((weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.obj ξ), ⊤))ˣ}
    (ht : t ∈ baseUnits.{u, w} a ξ) :
    ∃ m : ξ ⟶ ξ, (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift
      (𝟙 ((weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.obj ξ)) m ∧
      IsBandHom.{u, w} a ht m := by
  have hp := isFiberedInGroupoids_weightedQuotientStack.{u, w} p (𝒞 := 𝒞) (k := k) (hU := hU)
  have hst := isStack_weightedQuotientStack.{u, w} (𝒞 := 𝒞) (k := k) (p := p) (hU := hU)
  obtain ⟨R, hR, hch⟩ := exists_covering_chart_mem.{u, w} a
    (mem_stratumSubfunctor_of_chart.{u, w} a hPmor hPchart hξ)
  obtain ⟨m, hm, hmQ⟩ := hst.exists_hom_of_locally hp rfl rfl (BandRel.{u, w} a ht)
    (fun V x' g φ ψ ψ' hφ hQ hQ' => by
      have := hφ
      have hψ := isHomLift_of_map_eq _ hφ hQ.1
      have hψ' := isHomLift_of_map_eq _ hφ hQ'.1
      obtain ⟨R', hR', hch'⟩ := exists_chart_isHomLift.{u, w} 𝒞 k p hU V
        ⟨x', IsHomLift.domain_eq _ g φ⟩
      refine hst.eq_of_locally hp (g := g) ψ ψ' hR' (fun W c hc => ?_)
      obtain ⟨h, χ, hχ⟩ := hch' hc
      have := hχ
      have hh := mem_stratumSubfunctor_of_chart.{u, w} a hPmor hPchart hξ (χ ≫ φ)
      exact ⟨_, χ, hχ, (hQ.2 h hh χ (c ≫ g) inferInstance).trans
        (hQ'.2 h hh χ (c ≫ g) inferInstance).symm⟩)
    (fun x' x'' χ φ ψ hQ => ⟨by rw [Functor.map_comp, Functor.map_comp, hQ.1],
      fun W h hh χ' b hb => by
        have e := hQ.2 h hh (χ' ≫ χ) b (by rwa [Category.assoc])
        exact (Category.assoc _ _ _).symm.trans (e.trans (congrArg _ (Category.assoc _ _ _)))⟩)
    (fun V x' g φ ψ hQ hφ => isHomLift_of_map_eq _ hφ hQ.1) hR
    (fun V g hg => by
      obtain ⟨h, hh, φ, hφ⟩ := hch hg
      have := hφ
      exact ⟨_, φ, _, hφ, bandRel_chart.{u, w} a ht g h hh φ⟩)
  refine ⟨m, hm, fun V g h hh φ hφ => ?_⟩
  have := hφ
  exact (hmQ g φ _ hφ (bandRel_chart.{u, w} a ht g h hh φ)).symm

include hPmor hPchart in
/-- Two vertical endomorphisms of `ξ` with the defining property of the automorphism attached to
`t` agree. -/
theorem bandHom_ext {ξ : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.obj} (hξ : P ξ)
    {t : (Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj
      ((weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.obj ξ), ⊤))ˣ}
    (ht : t ∈ baseUnits.{u, w} a ξ) {m m' : ξ ⟶ ξ}
    [(weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift
      (𝟙 ((weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.obj ξ)) m]
    [(weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift
      (𝟙 ((weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.obj ξ)) m']
    (hm : IsBandHom.{u, w} a ht m) (hm' : IsBandHom.{u, w} a ht m') : m = m' := by
  obtain ⟨R, hR, hch⟩ := exists_covering_chart_mem.{u, w} a
    (mem_stratumSubfunctor_of_chart.{u, w} a hPmor hPchart hξ)
  refine (isStack_weightedQuotientStack.{u, w}).hom_ext_of_locally
    (isFiberedInGroupoids_weightedQuotientStack.{u, w} p) m m' hR (fun V g hg => ?_)
  obtain ⟨h, hh, φ, hφ⟩ := hch hg
  exact ⟨_, φ, hφ, (hm g h hh φ hφ).trans (hm' g h hh φ hφ).symm⟩

include hPmor hPchart in
/-- **The automorphism of an object of the stratum attached to a unit of the stratum group.** -/
noncomputable def bandHom {ξ : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.obj} (hξ : P ξ)
    (t : baseUnits.{u, w} a ξ) : ξ ⟶ ξ :=
  (exists_bandHom.{u, w} a hPmor hPchart hξ t.2).choose

/-- The automorphism attached to a unit lies over the identity. -/
instance isHomLift_bandHom {ξ : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.obj} (hξ : P ξ)
    (t : baseUnits.{u, w} a ξ) :
    (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift
      (𝟙 ((weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.obj ξ))
      (bandHom.{u, w} a hPmor hPchart hξ t) :=
  (exists_bandHom.{u, w} a hPmor hPchart hξ t.2).choose_spec.1

/-- The automorphism attached to a unit `t` satisfies `IsBandHom` for `t`. -/
theorem isBandHom_bandHom {ξ : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.obj} (hξ : P ξ)
    (t : baseUnits.{u, w} a ξ) : IsBandHom.{u, w} a t.2 (bandHom.{u, w} a hPmor hPchart hξ t) :=
  (exists_bandHom.{u, w} a hPmor hPchart hξ t.2).choose_spec.2

/-- A vertical endomorphism satisfying `IsBandHom` for `t` is the automorphism attached to `t`. -/
theorem eq_bandHom {ξ : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.obj} (hξ : P ξ)
    (t : baseUnits.{u, w} a ξ) (m : ξ ⟶ ξ)
    [(weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift
      (𝟙 ((weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.obj ξ)) m]
    (hm : IsBandHom.{u, w} a t.2 m) : m = bandHom.{u, w} a hPmor hPchart hξ t :=
  bandHom_ext.{u, w} a hPmor hPchart hξ t.2 hm (isBandHom_bandHom.{u, w} a hPmor hPchart hξ t)

/-- The automorphism attached to `t * t'` is the composite of those attached to `t` and `t'`. -/
theorem bandHom_mul {ξ : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.obj} (hξ : P ξ)
    (t t' : baseUnits.{u, w} a ξ) :
    bandHom.{u, w} a hPmor hPchart hξ (t * t') =
      bandHom.{u, w} a hPmor hPchart hξ t ≫ bandHom.{u, w} a hPmor hPchart hξ t' := by
  refine (eq_bandHom.{u, w} a hPmor hPchart hξ _ _ fun V g h hh φ hφ => ?_).symm
  have := hφ
  have hfix : actMap p (restrictUnits g t.1 * restrictUnits g t'.1) h = h := by
    rw [← map_mul]
    exact actMap_restrictUnits.{u, w} a (t * t').2 g hh
  have e : restrictUnits g (t * t').1 = restrictUnits g t.1 * restrictUnits g t'.1 := map_mul _ _ _
  calc φ ≫ bandHom.{u, w} a hPmor hPchart hξ t ≫ bandHom.{u, w} a hPmor hPchart hξ t'
      = (φ ≫ bandHom.{u, w} a hPmor hPchart hξ t) ≫ bandHom.{u, w} a hPmor hPchart hξ t' :=
        (Category.assoc _ _ _).symm
    _ = (chartAct.{u, w} h (restrictUnits g t.1) (actMap_restrictUnits.{u, w} a t.2 g hh) ≫ φ) ≫
          bandHom.{u, w} a hPmor hPchart hξ t' :=
        congrArg (· ≫ _) (isBandHom_bandHom.{u, w} a hPmor hPchart hξ t g h hh φ hφ)
    _ = chartAct.{u, w} h (restrictUnits g t.1) (actMap_restrictUnits.{u, w} a t.2 g hh) ≫
          (φ ≫ bandHom.{u, w} a hPmor hPchart hξ t') := Category.assoc _ _ _
    _ = chartAct.{u, w} h (restrictUnits g t.1) (actMap_restrictUnits.{u, w} a t.2 g hh) ≫
          (chartAct.{u, w} h (restrictUnits g t'.1) (actMap_restrictUnits.{u, w} a t'.2 g hh) ≫
            φ) :=
        congrArg (_ ≫ ·) (isBandHom_bandHom.{u, w} a hPmor hPchart hξ t' g h hh φ hφ)
    _ = (chartAct.{u, w} h (restrictUnits g t.1) (actMap_restrictUnits.{u, w} a t.2 g hh) ≫
          chartAct.{u, w} h (restrictUnits g t'.1) (actMap_restrictUnits.{u, w} a t'.2 g hh)) ≫
            φ := (Category.assoc _ _ _).symm
    _ = _ := congrArg (· ≫ φ) ((chartAct_comp.{u, w} h _ _ _ _ hfix).trans
        (chartAct_congr.{u, w} h e.symm _ _))

/-- The automorphism attached to the unit `1` is the identity. -/
theorem bandHom_one {ξ : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.obj} (hξ : P ξ) :
    bandHom.{u, w} a hPmor hPchart hξ 1 = 𝟙 ξ := by
  have : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift
      (𝟙 ((weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.obj ξ)) (𝟙 ξ) := IsHomLift.id rfl
  refine (eq_bandHom.{u, w} a hPmor hPchart hξ _ _ fun V g h hh φ hφ => ?_).symm
  have e : restrictUnits g (1 : baseUnits.{u, w} a ξ).1 = 1 := map_one _
  exact (Category.comp_id φ).trans ((Category.id_comp φ).symm.trans (congrArg (· ≫ φ)
    ((chartAct_one.{u, w} h (by rw [actMap_one])).symm.trans
      (chartAct_congr.{u, w} h e.symm _ _))))

/-- The automorphism attached to `t * t'` is also the composite of those attached to `t'` and
`t`. -/
theorem bandHom_comm {ξ : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.obj} (hξ : P ξ)
    (t t' : baseUnits.{u, w} a ξ) :
    bandHom.{u, w} a hPmor hPchart hξ (t * t') =
      bandHom.{u, w} a hPmor hPchart hξ t' ≫ bandHom.{u, w} a hPmor hPchart hξ t := by
  rw [← bandHom_mul, mul_comm]

/-- The automorphism of an object of the stratum, in the stratum, attached to a unit. -/
noncomputable def bandAut (x : P.FullSubcategory) (t : baseUnits.{u, w} a x.obj) : Aut x where
  hom := ObjectProperty.homMk (bandHom.{u, w} a hPmor hPchart x.property t)
  inv := ObjectProperty.homMk (bandHom.{u, w} a hPmor hPchart x.property t⁻¹)
  hom_inv_id := ObjectProperty.hom_ext _ (by
    change bandHom.{u, w} a hPmor hPchart x.property t ≫
      bandHom.{u, w} a hPmor hPchart x.property t⁻¹ = 𝟙 x.obj
    rw [← bandHom_mul, mul_inv_cancel, bandHom_one])
  inv_hom_id := ObjectProperty.hom_ext _ (by
    change bandHom.{u, w} a hPmor hPchart x.property t⁻¹ ≫
      bandHom.{u, w} a hPmor hPchart x.property t = 𝟙 x.obj
    rw [← bandHom_mul, inv_mul_cancel, bandHom_one])

/-- **The band of the stratum, from units to automorphisms.** -/
noncomputable def bandMonoidHom (x : P.FullSubcategory) :
    baseUnits.{u, w} a x.obj →*
      (P.ι ⋙ (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p).verticalAut x where
  toFun t := ⟨bandAut.{u, w} a hPmor hPchart x t, by
    rw [Functor.mem_verticalAut_iff]
    change (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.map
      (bandHom.{u, w} a hPmor hPchart x.property t) = _
    rw [IsHomLift.fac' _ (𝟙 ((weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.obj x.obj))
      (bandHom.{u, w} a hPmor hPchart x.property t)]
    simp⟩
  map_one' := Subtype.ext (Aut.ext (ObjectProperty.hom_ext _
    (bandHom_one.{u, w} a hPmor hPchart x.property)))
  map_mul' t t' := Subtype.ext (Aut.ext (ObjectProperty.hom_ext _
    (bandHom_comm.{u, w} a hPmor hPchart x.property t t')))

/-- Membership in the stratum group is local. -/
theorem mem_stratumUnits_of_locally {T : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    {R : Sieve T} (hR : R ∈ BigFppfOver.topology 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) T)
    {t : (Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj T, ⊤))ˣ}
    (h : ∀ ⦃V : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)⦄ (g : V ⟶ T), R g →
      restrictUnits g t ∈ stratumUnits p a) : t ∈ stratumUnits p a := by
  induction a using WithTop.recTopCoe with
  | top => exact Subgroup.mem_top t
  | coe i =>
    show t ^ p ^ i = 1
    refine units_ext_of_locally hR (fun V g hg => ?_)
    show Units.map _ (t ^ p ^ i) = Units.map _ 1
    rw [map_pow, map_one]
    exact h g hg

/-- Two units acting by the same morphism on a chart, followed by a chart `φ`, are equal. -/
private theorem eq_of_chartAct_comp_eq {ξ : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.obj}
    {V : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    {h : V ⟶ totalSiteObject 𝒞 k hU}
    (g : V ⟶ (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.obj ξ)
    (φ : chartObj.{u, w} p h ⟶ ξ)
    [(weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift g φ]
    {t t' : (Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj V, ⊤))ˣ}
    (ht : actMap p t h = h) (ht' : actMap p t' h = h)
    (e : chartAct.{u, w} h t ht ≫ φ = chartAct.{u, w} h t' ht' ≫ φ) : t = t' := by
  have := (isFiberedInGroupoids_weightedQuotientStack.{u, w} p).isStronglyCartesian_homLift g φ
  exact chartAct_injective.{u, w} h ht ht'
    (Functor.IsCartesian.ext (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p g φ _ _ e)

/-- The automorphism attached to a unit determines the unit. -/
theorem bandHom_injective {ξ : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.obj} (hξ : P ξ)
    {t t' : baseUnits.{u, w} a ξ}
    (e : bandHom.{u, w} a hPmor hPchart hξ t = bandHom.{u, w} a hPmor hPchart hξ t') : t = t' := by
  obtain ⟨R, hR, hch⟩ := exists_covering_chart_mem.{u, w} a
    (mem_stratumSubfunctor_of_chart.{u, w} a hPmor hPchart hξ)
  apply Subtype.ext
  refine units_ext_of_locally hR (fun V g hg => ?_)
  obtain ⟨h, hh, φ, hφ⟩ := hch hg
  have e1 := (isBandHom_bandHom.{u, w} a hPmor hPchart hξ t g h hh φ hφ).symm.trans
    ((congrArg (φ ≫ ·) e).trans (isBandHom_bandHom.{u, w} a hPmor hPchart hξ t' g h hh φ hφ))
  exact eq_of_chartAct_comp_eq.{u, w} g φ _ _ e1

/-- The relation describing a vertical endomorphism `m` of `ξ` on the charts over `g`. -/
def AutRel {ξ : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.obj} (m : ξ ⟶ ξ)
    ⦃V : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)⦄
    (g : V ⟶ (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.obj ξ)
    (s : (Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj V, ⊤))ˣ) : Prop :=
  ∀ ⦃W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)⦄ (c : W ⟶ V)
    (h : W ⟶ totalSiteObject 𝒞 k hU) (_ : h ∈ (stratumSubfunctor hU a).obj (op W))
    (φ : chartObj.{u, w} p h ⟶ ξ),
    (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift (c ≫ g) φ →
      ∃ hfix : actMap p (restrictUnits c s) h = h, φ ≫ m = chartAct.{u, w} h _ hfix ≫ φ

/-- On a chart, a vertical endomorphism of `ξ` is the action of a unit of the stratum group. -/
theorem exists_autRel {ξ : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.obj} (m : ξ ⟶ ξ)
    [(weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift
      (𝟙 ((weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.obj ξ)) m]
    {V : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (g : V ⟶ (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.obj ξ)
    {h₀ : V ⟶ totalSiteObject 𝒞 k hU} (hh₀ : h₀ ∈ (stratumSubfunctor hU a).obj (op V))
    (φ₀ : chartObj.{u, w} p h₀ ⟶ ξ)
    [(weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift g φ₀] :
    ∃ s, s ∈ stratumUnits p a ∧ AutRel.{u, w} a m g s := by
  have hp := isFiberedInGroupoids_weightedQuotientStack.{u, w} p (𝒞 := 𝒞) (k := k) (hU := hU)
  obtain ⟨ε, hε, hεφ⟩ := hp.exists_isHomLift_id_comp (g := g) φ₀ (φ₀ ≫ m)
  have hs0 := (chartVerticalEquiv.{u, w} p h₀ h₀ ⟨ε, hε⟩).2
  have hsm := mem_stratumUnits_of_actMap_eq_self a hh₀ hs0
  refine ⟨_, hsm, fun W c h hh φ hφ => ?_⟩
  have := hφ
  have hfix := actMap_eq_self_of_mem_stratumUnits a (map_mem_stratumUnits p a (restrict c) hsm) hh
  refine ⟨hfix, ?_⟩
  obtain ⟨θ, hθ, hθφ⟩ := hp.exists_isHomLift_id_comp (g := c ≫ g)
    (chartHom.{u, w} p c (rfl : c ≫ h₀ = c ≫ h₀) ≫ φ₀) φ
  have := hθ
  have hχ : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift c
      (θ ≫ chartHom.{u, w} p c (rfl : c ≫ h₀ = c ≫ h₀)) := inferInstance
  have key := comp_chartAct.{u, w} (θ ≫ chartHom.{u, w} p c (rfl : c ≫ h₀ = c ≫ h₀))
    (chartVerticalEquiv.{u, w} p h₀ h₀ ⟨ε, hε⟩).1 hs0 hfix
  rw [← eq_chartAct.{u, w} h₀ ε hε] at key
  calc φ ≫ m = (θ ≫ chartHom.{u, w} p c rfl) ≫ φ₀ ≫ m := by
        rw [← hθφ, Category.assoc, Category.assoc, Category.assoc]
    _ = ((θ ≫ chartHom.{u, w} p c rfl) ≫ ε) ≫ φ₀ := by
        rw [← hεφ]; simp only [Category.assoc]
    _ = (chartAct.{u, w} h _ hfix ≫ θ ≫ chartHom.{u, w} p c rfl) ≫ φ₀ := by rw [key]
    _ = _ := by rw [← hθφ]; simp only [Category.assoc]

include hPmor hPchart in
/-- Every vertical endomorphism of an object of the stratum is the automorphism attached to a
unit of the stratum group. -/
theorem exists_bandHom_eq {ξ : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.obj} (hξ : P ξ)
    (m : ξ ⟶ ξ)
    [(weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift
      (𝟙 ((weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.obj ξ)) m] :
    ∃ t : baseUnits.{u, w} a ξ, bandHom.{u, w} a hPmor hPchart hξ t = m := by
  obtain ⟨R, hR, hch⟩ := exists_covering_chart_mem.{u, w} a
    (mem_stratumSubfunctor_of_chart.{u, w} a hPmor hPchart hξ)
  have hfun : ∀ ⦃V : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)⦄
      (g : V ⟶ (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.obj ξ)
      {h : V ⟶ totalSiteObject 𝒞 k hU} (_ : h ∈ (stratumSubfunctor hU a).obj (op V))
      (φ : chartObj.{u, w} p h ⟶ ξ),
      (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift g φ →
      ∀ s s', AutRel.{u, w} a m g s → AutRel.{u, w} a m g s' → s = s' := by
    intro V g h hh φ hφ s s' hs hs'
    have := hφ
    obtain ⟨hf, e⟩ := hs (𝟙 V) h hh φ (by rwa [Category.id_comp])
    obtain ⟨hf', e'⟩ := hs' (𝟙 V) h hh φ (by rwa [Category.id_comp])
    rw [← restrictUnits_id s, ← restrictUnits_id s']
    exact eq_of_chartAct_comp_eq.{u, w} g φ hf hf' (e.symm.trans e')
  obtain ⟨t, ht⟩ := units_existsUnique_of_locally hR (AutRel.{u, w} a m)
    (fun V g hg s s' hs hs' => by
      obtain ⟨h, hh, φ, hφ⟩ := hch hg
      exact hfun g hh φ hφ s s' hs hs')
    (fun V W g c s hs W' c' h hh φ hφ => by
      obtain ⟨hfix, e⟩ := hs (c' ≫ c) h hh φ (by rwa [Category.assoc])
      refine ⟨by rwa [← restrictUnits_comp], e.trans ?_⟩
      exact congrArg (· ≫ φ) (chartAct_congr.{u, w} h (restrictUnits_comp c' c s) _ _))
    (fun V g hg => by
      obtain ⟨h, hh, φ, hφ⟩ := hch hg
      have := hφ
      obtain ⟨s, -, hs⟩ := exists_autRel.{u, w} a m g hh φ
      exact ⟨s, hs⟩)
  have htm : t ∈ baseUnits.{u, w} a ξ := mem_stratumUnits_of_locally a hR (fun V g hg => by
    obtain ⟨h, hh, φ, hφ⟩ := hch hg
    have := hφ
    obtain ⟨s, hsm, hs⟩ := exists_autRel.{u, w} a m g hh φ
    rwa [← ht g s hs])
  have hb : IsBandHom.{u, w} a htm m := by
    intro V g h hh φ hφ
    have := hφ
    obtain ⟨s, -, hs⟩ := exists_autRel.{u, w} a m g hh φ
    obtain ⟨hfix, e⟩ := hs (𝟙 V) h hh φ (by rwa [Category.id_comp])
    have e2 : restrictUnits (𝟙 V) s = restrictUnits g t := by rw [restrictUnits_id, ht g s hs]
    exact e.trans (congrArg (· ≫ φ) (chartAct_congr.{u, w} h e2 _ _))
  exact ⟨Subtype.mk t htm, (eq_bandHom.{u, w} a hPmor hPchart hξ (Subtype.mk t htm) m hb).symm⟩


include hPmor hPchart in
/-- **Naturality of the units attached to automorphisms.** If `f : x ⟶ y` intertwines the
automorphisms attached to `t` and `t'`, then `t` is the restriction of `t'` along the base of
`f`. -/
theorem eq_restrictUnits_of_comp_eq {x y : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.obj}
    (hx : P x) (hy : P y) (f : x ⟶ y) (t : baseUnits.{u, w} a x) (t' : baseUnits.{u, w} a y)
    (hf : bandHom.{u, w} a hPmor hPchart hx t ≫ f = f ≫ bandHom.{u, w} a hPmor hPchart hy t') :
    t.1 = restrictUnits ((weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.map f) t'.1 := by
  obtain ⟨R, hR, hch⟩ := exists_covering_chart_mem.{u, w} a
    (mem_stratumSubfunctor_of_chart.{u, w} a hPmor hPchart hx)
  refine units_ext_of_locally hR (fun V g hg => ?_)
  obtain ⟨h, hh, φ, hφ⟩ := hch hg
  have hφf : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.IsHomLift
      (g ≫ (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.map f) (φ ≫ f) := inferInstance
  have e1 := isBandHom_bandHom.{u, w} a hPmor hPchart hx t g h hh φ hφ
  have e2 := isBandHom_bandHom.{u, w} a hPmor hPchart hy t' _ h hh (φ ≫ f) hφf
  have e3 : chartAct.{u, w} h (restrictUnits g t.1) (actMap_restrictUnits.{u, w} a t.2 g hh) ≫
      φ ≫ f = chartAct.{u, w} h _ (actMap_restrictUnits.{u, w} a t'.2
        (g ≫ (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.map f) hh) ≫ φ ≫ f :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ f) e1.symm).trans
      ((Category.assoc _ _ _).trans ((congrArg (φ ≫ ·) hf).trans
        ((Category.assoc _ _ _).symm.trans e2))))
  exact (eq_of_chartAct_comp_eq.{u, w}
    (g ≫ (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.map f) (φ ≫ f) _ _ e3).trans
    (restrictUnits_comp g _ _)

/-- The underlying morphism of `bandMonoidHom x t` is the automorphism attached to `t`. -/
theorem bandMonoidHom_apply_hom (x : P.FullSubcategory) (t : baseUnits.{u, w} a x.obj) :
    ((bandMonoidHom.{u, w} a hPmor hPchart x t).1 : Aut x).hom.hom =
      bandHom.{u, w} a hPmor hPchart x.property t :=
  rfl

/-- A vertical automorphism whose underlying morphism is the automorphism attached to `t` is
`bandMonoidHom x t`. -/
theorem bandMonoidHom_eq_of (x : P.FullSubcategory) (t : baseUnits.{u, w} a x.obj)
    (α : (P.ι ⋙ (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p).verticalAut x)
    (h : bandHom.{u, w} a hPmor hPchart x.property t = (α.1 : Aut x).hom.hom) :
    bandMonoidHom.{u, w} a hPmor hPchart x t = α :=
  Subtype.ext (Aut.ext (ObjectProperty.hom_ext _ h))

/-- Every vertical automorphism of an object of the stratum is the automorphism attached to some
unit of the stratum group. -/
theorem exists_bandHom_eq_of_vertical (x : P.FullSubcategory)
    (α : (P.ι ⋙ (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p).verticalAut x) :
    ∃ t : baseUnits.{u, w} a x.obj,
      bandHom.{u, w} a hPmor hPchart x.property t = (α.1 : Aut x).hom.hom := by
  have hc : (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.map (α.1 : Aut x).hom.hom =
      𝟙 ((weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.obj x.obj) :=
    Functor.verticalAut.cond α
  have hα := IsHomLift.map (p := (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p)
    (α.1 : Aut x).hom.hom
  rw [hc] at hα
  exact exists_bandHom_eq.{u, w} a hPmor hPchart x.property _

/-- **The band of the stratum is bijective.** -/
theorem bijective_bandMonoidHom (x : P.FullSubcategory) :
    Function.Bijective (bandMonoidHom.{u, w} a hPmor hPchart x) := by
  refine ⟨fun t t' e => bandHom_injective.{u, w} a hPmor hPchart x.property
    (((bandMonoidHom_apply_hom.{u, w} a hPmor hPchart x t).symm.trans
      (congrArg (fun α => (α.1 : Aut x).hom.hom) e)).trans
      (bandMonoidHom_apply_hom.{u, w} a hPmor hPchart x t')),
    fun α => (exists_bandHom_eq_of_vertical.{u, w} a hPmor hPchart x α).imp
      fun t ht => bandMonoidHom_eq_of.{u, w} a hPmor hPchart x t α ht⟩


include hPmor hPchart in
/-- **The band of the stratum**: the vertical automorphisms of an object `x` of `𝒳_a` over `T`
are the sections over `T` of the group of the stratum. -/
noncomputable def band [NeZero p] (x : P.FullSubcategory) :
    (P.ι ⋙ (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p).verticalAut x ≃*
      ((Over.mk ((weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.obj x.obj).hom.hom : Over 𝒵) ⟶
        stratumGroup.{u} p a) :=
  (MulEquiv.ofBijective _ (bijective_bandMonoidHom.{u, w} a hPmor hPchart x)).symm.trans
    (stratumHomMulEquiv p a
      (Over.mk ((weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.obj x.obj).hom.hom :
        Over 𝒵)).symm

/-- The automorphism attached to the unit that the inverse of `bandMonoidHom x` assigns to a
vertical automorphism `α` is the underlying morphism of `α`. -/
theorem bandHom_band_symm [NeZero p] (x : P.FullSubcategory)
    (α : (P.ι ⋙ (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p).verticalAut x) :
    bandHom.{u, w} a hPmor hPchart x.property
        ((MulEquiv.ofBijective _ (bijective_bandMonoidHom.{u, w} a hPmor hPchart x)).symm α) =
      (α.1 : Aut x).hom.hom :=
  congrArg (fun β => (β.1 : Aut x).hom.hom)
    ((MulEquiv.ofBijective _ (bijective_bandMonoidHom.{u, w} a hPmor hPchart x)).apply_symm_apply α)


include hPmor hPchart in
/-- **The band of the stratum is natural** along every morphism of the stratum. -/
theorem band_naturality [NeZero p] (x y : P.FullSubcategory) (f : x ⟶ y)
    (α : (P.ι ⋙ (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p).verticalAut x)
    (β : (P.ι ⋙ (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p).verticalAut y)
    (h : (α : Aut x).hom ≫ f = f ≫ (β : Aut y).hom) :
    Over.Hom.left (band.{u, w} a hPmor hPchart x α) =
      ((P.ι ⋙ (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p).map f).left.hom ≫
        Over.Hom.left (band.{u, w} a hPmor hPchart y β) := by
  have hx := bandHom_band_symm.{u, w} a hPmor hPchart x α
  have hy := bandHom_band_symm.{u, w} a hPmor hPchart y β
  have hf : bandHom.{u, w} a hPmor hPchart x.property
        ((MulEquiv.ofBijective _ (bijective_bandMonoidHom.{u, w} a hPmor hPchart x)).symm α) ≫
        f.hom = f.hom ≫ bandHom.{u, w} a hPmor hPchart y.property
        ((MulEquiv.ofBijective _ (bijective_bandMonoidHom.{u, w} a hPmor hPchart y)).symm β) := by
    have h' : (α.1 : Aut x).hom.hom ≫ f.hom = f.hom ≫ (β.1 : Aut y).hom.hom :=
      congrArg InducedCategory.Hom.hom h
    exact (congrArg (· ≫ f.hom) hx).trans (h'.trans (congrArg (f.hom ≫ ·) hy.symm))
  have ht := eq_restrictUnits_of_comp_eq.{u, w} a hPmor hPchart x.property y.property f.hom _ _ hf
  let Tx : Over 𝒵 := Over.mk ((weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.obj x.obj).hom.hom
  let Ty : Over 𝒵 := Over.mk ((weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.obj y.obj).hom.hom
  let v : Tx ⟶ Ty :=
    Over.homMk ((P.ι ⋙ (weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p).map f).left.hom
      (specULiftZIsTerminal.hom_ext _ _)
  have hres : ∀ t : (Γ(Ty.left, ⊤))ˣ, Units.map (Scheme.Γ.map v.left.op).hom.toMonoidHom t =
      restrictUnits ((weightedQuotientStack.{u, w} 𝒞 k p hU).val.val.p.map f.hom) t := fun _ => rfl
  have key : band.{u, w} a hPmor hPchart x α = v ≫ band.{u, w} a hPmor hPchart y β := by
    apply (stratumHomMulEquiv p a Tx).injective
    apply Subtype.ext
    refine Eq.trans ?_ (stratumHomMulEquiv_comp p a v _).symm
    refine Eq.trans ?_ (hres _).symm
    refine Eq.trans ?_ (congrArg (restrictUnits _) (congrArg Subtype.val
      ((stratumHomMulEquiv p a Ty).apply_symm_apply _)).symm)
    exact (congrArg Subtype.val ((stratumHomMulEquiv p a Tx).apply_symm_apply _)).trans ht
  exact congrArg Over.Hom.left key

include hPmor hPchart in
/-- **Stacks 06RE: the strata are gerbes over schemes with groups**, for any property `P` of the
objects of `𝒳 = [U/𝐆_m]` which is inherited along morphisms and cuts out the stratum `X_a` on the
chart objects: the full subcategory on `P` is a gerbe over the scheme `M_a` with group
`μ_{p^i}` for `a = i` and `𝐆_m` for `a = ∞`. -/
theorem isGerbeOverSchemeWithGroup_of_chart [NeZero p]
    (hP : Stack.IsAlgebraicStack.{u, w} 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
      (Stack.fullSubcategoryBased (weightedQuotientStack.{u, w} 𝒞 k p hU) P)) :
    Stack.AlgebraicStacks.IsGerbeOverSchemeWithGroup 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
      (Stack.fullSubcategoryAlgebraicStack (weightedQuotientStack.{u, w} 𝒞 k p hU) P hP)
      (stratumGroup.{u} p a) :=
  ⟨⟨coarseSiteObject hU a, coarse.{u, w} a hPmor hPchart hP,
      isGerbeOver_coarse.{u, w} a hPmor hPchart hP⟩,
    band.{u, w} a hPmor hPchart, fun x y f α β h =>
      band_naturality.{u, w} a hPmor hPchart x y f α β h⟩

end Band

/-! ### The strata -/

section Strata

variable {𝒞 : BigFppfSite.{u}} {k : Type u} [CommRing k] {p : ℕ}
  {hU : 𝒞.Contains (Spec (.of (MvPolynomial ℕ k)))}

/-- **Stacks 06RE: each stratum is a gerbe over a scheme with group `μ_{p^i}` for `𝒳_i` and
`𝐆_m` for `𝒳_∞`.** The stratum `𝒳_a` of `𝒳 = [U/𝐆_m]`, given as an algebraic stack, is a gerbe
over its coarse space `M_a` (`U` for `a = i`, `Spec k` for `a = ∞`) whose band is the group
scheme `AlgebraicGeometry.PPowerWeighted.stratumGroup p a`. -/
theorem isGerbeOverSchemeWithGroup_stratum [NeZero p] (a : WithTop ℕ)
    (hP : Stack.IsAlgebraicStack.{u, w} 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
      (Stack.fullSubcategoryBased (weightedQuotientStack.{u, w} 𝒞 k p hU)
        (stratumProperty.{u, w} 𝒞 k p hU a))) :
    Stack.AlgebraicStacks.IsGerbeOverSchemeWithGroup 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
      (Stack.fullSubcategoryAlgebraicStack (weightedQuotientStack.{u, w} 𝒞 k p hU)
        (stratumProperty.{u, w} 𝒞 k p hU a) hP)
      (stratumGroup.{u} p a) :=
  isGerbeOverSchemeWithGroup_of_chart.{u, w} a (fun _ _ φ hy => stratumProperty_of_hom p φ hy)
    (fun _ h => chartObj_mem_stratumProperty_iff p a h) hP

end Strata

end AlgebraicGeometry.PPowerWeighted

end
