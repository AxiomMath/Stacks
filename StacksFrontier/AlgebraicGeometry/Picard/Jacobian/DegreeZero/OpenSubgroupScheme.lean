module

public import StacksFrontier.AlgebraicGeometry.Picard.Jacobian.DegreeZero.ResidueDegree
public import StacksFrontier.AlgebraicGeometry.Picard.TorsionSmoothProjectiveCurve.RepresentingGroup
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSiteObject

/-!
# `Pic⁰_{X/k}` as an open subgroup scheme of the Picard scheme

Let `X` be a smooth projective curve over an algebraically closed field `k`, and let `P` be a
scheme representing its Picard functor `Pic_{X/k}` on a big fppf site, with the group law of
`Stacks.PicardFunctor.representingGrpObj`. A point `p ∈ P` carries the section `ξ_p` of
`Pic_{X/k}` over `κ(p)` obtained by restricting the universal section, and `ξ_p` has a degree
(`Stacks.PicardFunctor.residueDegree`). The function `p ↦ deg ξ_p` is locally constant, so its
zero set `P⁰` is open and closed. A morphism `a : T ⟶ P` factors through `P⁰` exactly when the
section `a^*ξ` lies in the degree-zero subfunctor `Pic⁰_{X/k}`
(`Stacks.PicardFunctor.degreeZeroSubfunctor`): `P⁰` represents `Pic⁰_{X/k}`. As the degree is
additive, `P⁰` is an open subgroup scheme of `P` ([Stacks, Tag 0BA0], clauses (1) and (2) at
`d = 0`), and its `k`-points are the classes of degree zero.

## Main definitions

* `Stacks.PicardFunctor.pointDegree`: `p ↦ deg ξ_p` on the representing scheme.
* `Stacks.PicardFunctor.degreeZeroOpens`: its zero set, an open subset of `P`.
* `Stacks.PicardFunctor.degreeZeroObj`, `Stacks.PicardFunctor.degreeZeroHom`: the open
  subscheme as an object of the site, and its inclusion into `P`.
* `Stacks.PicardFunctor.degreeZeroOpenSubgroupScheme`: **`Pic⁰_{X/k}`** as an
  `AlgebraicGeometry.OpenSubgroupScheme` of the Picard scheme.

## Main results

* `Stacks.PicardFunctor.exists_comp_degreeZeroHom_iff_mem_degreeZeroSubfunctor`: `P⁰` represents
  `Pic⁰_{X/k}`.
* `Stacks.PicardFunctor.isClosed_degreeZeroOpens`: `P⁰` is also closed.
* `Stacks.PicardFunctor.exists_comp_degreeZeroOpenSubgroupScheme_iff`: a `k`-point of `P` factors
  through `Pic⁰_{X/k}` if and only if its class in `Pic(X)` has degree zero; this is the
  hypothesis of `Stacks.PicardFunctor.kerOfSchemeDegreeAddEquivPointsOfOpenSubgroupScheme`.

## References

* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
* [Stacks Project, Tag 0G8L](https://stacks.math.columbia.edu/tag/0G8L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry Opposite

open scoped CategoryTheory.MonObj

universe u

namespace Stacks.PicardFunctor

attribute [local instance] bigFppfOverCartesianMonoidal

variable (B : BigFppfSite.{u}) {X : Scheme.{u}} (hX : B.Contains X)
  (k : Type u) [Field k] [IsAlgClosed k] {hk : B.Contains (Spec (.of k))}
  (g : B.obj hX ⟶ B.obj hk) [IsCurve k (B.inclusion.map g)]
  [IsProjectiveVariety k (B.inclusion.map g)] [Smooth (B.inclusion.map g)]
  {P : BigFppfOver B (Spec (.of k)) hk} (R : (picardFunctor B hX hk g).RepresentableBy P)

/-- **The degree at a point of the representing scheme**: the degree of the restriction of the
universal section to `Spec κ(p)`. -/
def pointDegree (p : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj P) : ℤ :=
  residueDegree B hX k g P (R.homEquiv (𝟙 P)) p

/-- The degree at `t` of the section attached to `a : T ⟶ P` is the degree at the point `a(t)`. -/
theorem residueDegree_homEquiv {T : BigFppfOver B (Spec (.of k)) hk} (a : T ⟶ P)
    (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj T) :
    residueDegree B hX k g T (R.homEquiv a) t =
      pointDegree B hX k g R ((BigFppfOver.toScheme B (Spec (.of k)) hk).map a t) := by
  rw [← Category.comp_id a, R.homEquiv_comp, residueDegree_map, Category.comp_id]
  rfl

/-- The degree at a point of the representing scheme is locally constant. -/
theorem isLocallyConstant_pointDegree : IsLocallyConstant (pointDegree B hX k g R) :=
  isLocallyConstant_residueDegree B hX k g P _

/-- **The open subset `P⁰` of the representing scheme** where the degree vanishes. -/
def degreeZeroOpens : ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj P).Opens :=
  ⟨pointDegree B hX k g R ⁻¹' {0}, (isLocallyConstant_pointDegree B hX k g R).isOpen_fiber 0⟩

/-- A point lies in `P⁰` if and only if the degree at it vanishes. -/
theorem mem_degreeZeroOpens_iff (p : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj P) :
    p ∈ degreeZeroOpens B hX k g R ↔ pointDegree B hX k g R p = 0 :=
  Iff.rfl

/-- `P⁰` is also closed in `P`. -/
theorem isClosed_degreeZeroOpens :
    IsClosed (degreeZeroOpens B hX k g R :
      Set ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj P)) :=
  (isLocallyConstant_pointDegree B hX k g R).isClosed_fiber 0

/-- `P⁰` as an object of the site. -/
abbrev degreeZeroObj : BigFppfOver B (Spec (.of k)) hk :=
  Space.openSiteObject B (Spec (.of k)) hk P (degreeZeroOpens B hX k g R)

/-- The inclusion `P⁰ ⟶ P`. -/
abbrev degreeZeroHom : degreeZeroObj B hX k g R ⟶ P :=
  Space.openSiteObjectHom B (Spec (.of k)) hk P (degreeZeroOpens B hX k g R)

/-- A morphism of schemes whose image lies in an open subset factors through the open subscheme. -/
private theorem exists_comp_opens_ι_eq {Z Y : Scheme} (U : Y.Opens) (f : Z ⟶ Y)
    (h : ∀ p, f p ∈ U) : ∃ l, l ≫ U.ι = f :=
  ⟨IsOpenImmersion.lift U.ι f (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨p, rfl⟩
    exact h p), IsOpenImmersion.lift_fac _ _ _⟩

/-- **A morphism to the representing scheme factors through `P⁰` exactly when the degree vanishes
at every point of its image.** -/
theorem exists_comp_degreeZeroHom_iff {T : BigFppfOver B (Spec (.of k)) hk} (a : T ⟶ P) :
    (∃ b, b ≫ degreeZeroHom B hX k g R = a) ↔
      ∀ t, pointDegree B hX k g R ((BigFppfOver.toScheme B (Spec (.of k)) hk).map a t) = 0 := by
  have hι := Space.map_openSiteObjectHom B (Spec (.of k)) hk P (degreeZeroOpens B hX k g R)
  constructor
  · rintro ⟨b, rfl⟩ t
    rw [Functor.map_comp, Scheme.Hom.comp_apply, hι]
    exact ((BigFppfOver.toScheme B (Spec (.of k)) hk).map b t).2
  · intro h
    obtain ⟨l, hl⟩ := exists_comp_opens_ι_eq (degreeZeroOpens B hX k g R)
      ((BigFppfOver.toScheme B (Spec (.of k)) hk).map a) h
    let lB : T.left ⟶ (degreeZeroObj B hX k g R).left :=
      B.inclusion.preimage (X := T.left) (Y := (degreeZeroObj B hX k g R).left) l
    have e1 : B.inclusion.map lB = l :=
      B.inclusion.map_preimage (X := T.left) (Y := (degreeZeroObj B hX k g R).left) l
    have hlB : B.inclusion.map lB ≫ B.inclusion.map (degreeZeroHom B hX k g R).left =
        B.inclusion.map a.left := by
      rw [e1, show B.inclusion.map (degreeZeroHom B hX k g R).left =
        (degreeZeroOpens B hX k g R).ι from hι]
      exact hl
    refine ⟨Over.homMk lB ?_, ?_⟩
    · apply B.inclusion.map_injective
      rw [← Over.w (degreeZeroHom B hX k g R), ← Category.assoc, Functor.map_comp,
        Functor.map_comp, hlB, ← Functor.map_comp, Over.w a]
    · exact Over.OverMorphism.ext <| B.inclusion.map_injective <| by
        rw [Over.comp_left, Functor.map_comp]
        exact hlB

/-- **`P⁰` represents `Pic⁰_{X/k}`**: a morphism `a : T ⟶ P` factors through `P⁰` exactly when the
corresponding section of `Pic_{X/k}` over `T` lies in the degree-zero subfunctor. -/
theorem exists_comp_degreeZeroHom_iff_mem_degreeZeroSubfunctor
    {T : BigFppfOver B (Spec (.of k)) hk} (a : T ⟶ P) :
    (∃ b, b ≫ degreeZeroHom B hX k g R = a) ↔
      R.homEquiv a ∈ (degreeZeroSubfunctor B hX hk g
        (topologicalKrullDim_le_one_of_curve B hX k g)).obj (op T) := by
  rw [exists_comp_degreeZeroHom_iff, mem_degreeZeroSubfunctor_iff_residueDegree]
  exact forall_congr' fun t => by rw [residueDegree_homEquiv]

/-- A morphism to `P` factors through `P⁰` exactly when the corresponding section has degree zero
at every point. -/
theorem exists_comp_degreeZeroHom_iff_residueDegree {T : BigFppfOver B (Spec (.of k)) hk}
    (a : T ⟶ P) :
    (∃ b, b ≫ degreeZeroHom B hX k g R = a) ↔
      ∀ t, residueDegree B hX k g T (R.homEquiv a) t = 0 := by
  rw [exists_comp_degreeZeroHom_iff]
  exact forall_congr' fun t => by rw [residueDegree_homEquiv]

section GroupLaw

attribute [local instance] toOverMonoidal

omit [IsAlgClosed k] [IsCurve k (B.inclusion.map g)] [IsProjectiveVariety k (B.inclusion.map g)]
    [Smooth (B.inclusion.map g)] in
/-- The representing bijection sends the unit of the group of `T`-points to `0`. -/
theorem RepresentableBy.homEquiv_one {T : BigFppfOver B (Spec (.of k)) hk} :
    letI := grpObjOfRepresentableBy R
    R.homEquiv (1 : T ⟶ P) = 0 := by
  let := grpObjOfRepresentableBy R
  have h := RepresentableBy.homEquiv_mul R (1 : T ⟶ P) 1
  rw [mul_one] at h
  exact left_eq_add.mp h

omit [IsAlgClosed k] [IsCurve k (B.inclusion.map g)] [IsProjectiveVariety k (B.inclusion.map g)]
    [Smooth (B.inclusion.map g)] in
/-- The representing bijection sends inverses to negatives. -/
theorem RepresentableBy.homEquiv_inv {T : BigFppfOver B (Spec (.of k)) hk} (a : T ⟶ P) :
    letI := grpObjOfRepresentableBy R
    R.homEquiv a⁻¹ = -R.homEquiv a := by
  let := grpObjOfRepresentableBy R
  have h := RepresentableBy.homEquiv_mul R a⁻¹ a
  rw [inv_mul_cancel, RepresentableBy.homEquiv_one B hX k g R] at h
  exact (neg_eq_of_add_eq_zero_left h.symm).symm

/-- The inclusion of `P⁰` into the Picard scheme, as a morphism of schemes over `Spec k`. -/
abbrev degreeZeroOverHom :
    (BigFppfOver.toOver B (Spec (.of k)) hk).obj (degreeZeroObj B hX k g R) ⟶
      (BigFppfOver.toOver B (Spec (.of k)) hk).obj P :=
  (BigFppfOver.toOver B (Spec (.of k)) hk).map (degreeZeroHom B hX k g R)

/-- The inclusion of `P⁰` into the Picard scheme is an open immersion. -/
instance isOpenImmersion_degreeZeroOverHom :
    IsOpenImmersion (degreeZeroOverHom B hX k g R).left := by
  have h : (degreeZeroOverHom B hX k g R).left = (degreeZeroOpens B hX k g R).ι :=
    Space.map_openSiteObjectHom B (Spec (.of k)) hk P (degreeZeroOpens B hX k g R)
  rw [h]
  exact Scheme.Opens.instIsOpenImmersionι _

/-- The unit of the Picard scheme factors through `P⁰`. -/
theorem degreeZero_one_factor :
    letI := grpObjOfRepresentableBy R
    ∃ b, b ≫ degreeZeroHom B hX k g R = (η[P] : 𝟙_ _ ⟶ P) := by
  let := grpObjOfRepresentableBy R
  rw [exists_comp_degreeZeroHom_iff_residueDegree]
  intro t
  have h1 : (η[P] : 𝟙_ _ ⟶ P) = 1 := by
    rw [Hom.one_def]
    simp
  rw [h1, RepresentableBy.homEquiv_one B hX k g R, residueDegree_zero]

/-- The multiplication of the Picard scheme, restricted to `P⁰ ⊗ P⁰`, factors through `P⁰`. -/
theorem degreeZero_mul_factor :
    letI := grpObjOfRepresentableBy R
    ∃ b, b ≫ degreeZeroHom B hX k g R =
      (degreeZeroHom B hX k g R ⊗ₘ degreeZeroHom B hX k g R) ≫ μ[P] := by
  let := grpObjOfRepresentableBy R
  rw [exists_comp_degreeZeroHom_iff_residueDegree]
  intro t
  have h1 : (degreeZeroHom B hX k g R ⊗ₘ degreeZeroHom B hX k g R) ≫ μ[P] =
      (fst _ _ ≫ degreeZeroHom B hX k g R) * (snd _ _ ≫ degreeZeroHom B hX k g R) := by
    rw [Hom.mul_def, lift_fst_comp_snd_comp]
  rw [h1, RepresentableBy.homEquiv_mul, residueDegree_add,
    (exists_comp_degreeZeroHom_iff_residueDegree B hX k g R _).1 ⟨_, rfl⟩ t,
    (exists_comp_degreeZeroHom_iff_residueDegree B hX k g R _).1 ⟨_, rfl⟩ t, add_zero]

/-- The inversion of the Picard scheme, restricted to `P⁰`, factors through `P⁰`. -/
theorem degreeZero_inv_factor :
    letI := grpObjOfRepresentableBy R
    ∃ b, b ≫ degreeZeroHom B hX k g R = degreeZeroHom B hX k g R ≫ ι[P] := by
  let := grpObjOfRepresentableBy R
  rw [exists_comp_degreeZeroHom_iff_residueDegree]
  intro t
  rw [← Hom.inv_def, RepresentableBy.homEquiv_inv B hX k g R, residueDegree_neg,
    (exists_comp_degreeZeroHom_iff_residueDegree B hX k g R _).1 ⟨𝟙 _, Category.id_comp _⟩ t,
    neg_zero]

/-- The identity, multiplication and inverse of the Picard scheme factor through `P⁰`. -/
theorem degreeZero_factors :
    letI := representingGrpObj R
    (∃ e : 𝟙_ (Over (Spec (.of k))) ⟶ (BigFppfOver.toOver B (Spec (.of k)) hk).obj
        (degreeZeroObj B hX k g R),
        e ≫ degreeZeroOverHom B hX k g R = η[(BigFppfOver.toOver B (Spec (.of k)) hk).obj P]) ∧
      (∃ m : (BigFppfOver.toOver B (Spec (.of k)) hk).obj (degreeZeroObj B hX k g R) ⊗
          (BigFppfOver.toOver B (Spec (.of k)) hk).obj (degreeZeroObj B hX k g R) ⟶
          (BigFppfOver.toOver B (Spec (.of k)) hk).obj (degreeZeroObj B hX k g R),
        m ≫ degreeZeroOverHom B hX k g R =
          (degreeZeroOverHom B hX k g R ⊗ₘ degreeZeroOverHom B hX k g R) ≫
            μ[(BigFppfOver.toOver B (Spec (.of k)) hk).obj P]) ∧
      (∃ i : (BigFppfOver.toOver B (Spec (.of k)) hk).obj (degreeZeroObj B hX k g R) ⟶
          (BigFppfOver.toOver B (Spec (.of k)) hk).obj (degreeZeroObj B hX k g R),
        i ≫ degreeZeroOverHom B hX k g R =
          degreeZeroOverHom B hX k g R ≫ ι[(BigFppfOver.toOver B (Spec (.of k)) hk).obj P]) := by
  let := grpObjOfRepresentableBy R
  let := representingGrpObj R
  set F := BigFppfOver.toOver B (Spec (.of k)) hk
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨b, hb⟩ := degreeZero_one_factor B hX k g R
    refine ⟨Functor.LaxMonoidal.ε F ≫ F.map b, ?_⟩
    rw [Category.assoc, ← F.map_comp, hb]
    rfl
  · obtain ⟨b, hb⟩ := degreeZero_mul_factor B hX k g R
    refine ⟨Functor.LaxMonoidal.μ F _ _ ≫ F.map b, ?_⟩
    rw [Category.assoc, ← F.map_comp, hb, F.map_comp, ← Category.assoc,
      ← Functor.LaxMonoidal.μ_natural, Category.assoc]
    rfl
  · obtain ⟨b, hb⟩ := degreeZero_inv_factor B hX k g R
    refine ⟨F.map b, ?_⟩
    rw [← F.map_comp, hb, F.map_comp]
    rfl

/-- The open subscheme `P⁰` is an open subgroup scheme of the Picard scheme, by the factorization
criterion `AlgebraicGeometry.isOpenSubgroupScheme_iff_factor` ([Stacks, Tag 0G8L], part (2)). -/
theorem exists_openSubgroupScheme_degreeZero :
    letI := representingGrpObj R
    ∃ (K : OpenSubgroupScheme (Grp.mk ((BigFppfOver.toOver B (Spec (.of k)) hk).obj P)))
      (e : (BigFppfOver.toOver B (Spec (.of k)) hk).obj (degreeZeroObj B hX k g R) ≅
        K.carrier.X), degreeZeroOverHom B hX k g R = e.hom ≫ K.ι.hom.hom :=
  let := representingGrpObj R
  (isOpenSubgroupScheme_iff_factor (Grp.mk ((BigFppfOver.toOver B (Spec (.of k)) hk).obj P))
    (degreeZeroOverHom B hX k g R)).2 (degreeZero_factors B hX k g R)

/-- **`Pic⁰_{X/k}` as an open subgroup scheme of the Picard scheme**: the open and closed
subscheme `P⁰` where the degree vanishes, with the group law restricted from
`Stacks.PicardFunctor.representingGrpObj`. -/
def degreeZeroOpenSubgroupScheme :
    letI := representingGrpObj R
    OpenSubgroupScheme (Grp.mk ((BigFppfOver.toOver B (Spec (.of k)) hk).obj P)) :=
  (exists_openSubgroupScheme_degreeZero B hX k g R).choose

/-- The underlying scheme of `Stacks.PicardFunctor.degreeZeroOpenSubgroupScheme` is `P⁰`,
compatibly with the inclusions into the Picard scheme. -/
theorem exists_iso_degreeZeroOpenSubgroupScheme :
    letI := representingGrpObj R
    ∃ e : (BigFppfOver.toOver B (Spec (.of k)) hk).obj (degreeZeroObj B hX k g R) ≅
        (degreeZeroOpenSubgroupScheme B hX k g R).carrier.X,
      degreeZeroOverHom B hX k g R = e.hom ≫ (degreeZeroOpenSubgroupScheme B hX k g R).ι.hom.hom :=
  (exists_openSubgroupScheme_degreeZero B hX k g R).choose_spec

/-- A morphism over `Spec k` into the Picard scheme factors through `P⁰` exactly when its image
lies in `P⁰`. -/
private theorem exists_comp_degreeZeroOverHom_iff {Z : Over (Spec (.of k))}
    (x : Z ⟶ (BigFppfOver.toOver B (Spec (.of k)) hk).obj P) :
    (∃ y, y ≫ degreeZeroOverHom B hX k g R = x) ↔
      ∀ p, x.left p ∈ degreeZeroOpens B hX k g R := by
  have hleft : (degreeZeroOverHom B hX k g R).left = (degreeZeroOpens B hX k g R).ι :=
    Space.map_openSiteObjectHom B (Spec (.of k)) hk P (degreeZeroOpens B hX k g R)
  constructor
  · rintro ⟨y, rfl⟩ p
    rw [Over.comp_left, Scheme.Hom.comp_apply, hleft]
    exact (y.left p).2
  · intro h
    obtain ⟨l, hl'⟩ := exists_comp_opens_ι_eq (degreeZeroOpens B hX k g R) x.left h
    have hl : (l : Z.left ⟶
        ((BigFppfOver.toOver B (Spec (.of k)) hk).obj (degreeZeroObj B hX k g R)).left) ≫
          (degreeZeroOverHom B hX k g R).left = x.left := by
      rw [hleft]
      exact hl'
    refine ⟨Over.homMk l ?_, Over.OverMorphism.ext hl⟩
    rw [← Over.w (degreeZeroOverHom B hX k g R), ← Over.w x]
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ ((BigFppfOver.toOver B (Spec (.of k)) hk).obj P).hom) hl)

/-- The degree at any point of the image of a `k`-point of the Picard scheme is the degree of the
corresponding class of `Pic(X)`. -/
private theorem pointDegree_eq_ofSchemeDegree (hdim : topologicalKrullDim X ≤ 1) :
    letI := representingGrpObj R
    ∀ (x : 𝟙_ (Over (Spec (.of k))) ⟶ (BigFppfOver.toOver B (Spec (.of k)) hk).obj P)
      (p : (𝟙_ (Over (Spec (.of k)))).left),
      pointDegree B hX k g R (x.left p) =
        Stacks.Picard.ofSchemeDegree k (B.inclusion.map g) hdim
          ((ofSchemeAddEquivRepresentingPoints k g R).symm (Additive.ofMul x)) := by
  let := representingGrpObj R
  intro x p
  obtain ⟨xB, hxB, hrep⟩ := exists_representingPointsAddEquiv_eq R x
  have hc : (ofSchemeAddEquivRepresentingPoints k g R).symm (Additive.ofMul x) =
      (ofSchemeAddEquivPicardFunctorOfCurve B hX k g).symm (R.homEquiv xB) := by
    rw [← hrep]
    rfl
  have h1 : x.left p = (BigFppfOver.toScheme B (Spec (.of k)) hk).map xB p := by
    rw [hxB]
    rfl
  rw [h1, ← residueDegree_homEquiv, hc, ← residueDegree_ofSchemeAddEquivPicardFunctorOfCurve
    B hX k g hdim _ p, AddEquiv.apply_symm_apply]

/-- **The `k`-points of `Pic⁰_{X/k}` are the classes of degree zero**: a `k`-point of the Picard
scheme factors through `Stacks.PicardFunctor.degreeZeroOpenSubgroupScheme` exactly when the
corresponding class of `Pic(X)` (`Stacks.PicardFunctor.ofSchemeAddEquivRepresentingPoints`) has
degree zero. This is the hypothesis `hH` of
`Stacks.PicardFunctor.kerOfSchemeDegreeAddEquivPointsOfOpenSubgroupScheme`. -/
theorem exists_comp_degreeZeroOpenSubgroupScheme_iff (hdim : topologicalKrullDim X ≤ 1) :
    letI := representingGrpObj R
    ∀ x : 𝟙_ (Over (Spec (.of k))) ⟶ (BigFppfOver.toOver B (Spec (.of k)) hk).obj P,
      (∃ y, y ≫ (degreeZeroOpenSubgroupScheme B hX k g R).ι.hom.hom = x) ↔
        Stacks.Picard.ofSchemeDegree k (B.inclusion.map g) hdim
          ((ofSchemeAddEquivRepresentingPoints k g R).symm (Additive.ofMul x)) = 0 := by
  let := representingGrpObj R
  intro x
  obtain ⟨e, he⟩ := exists_iso_degreeZeroOpenSubgroupScheme B hX k g R
  have hpt := pointDegree_eq_ofSchemeDegree B hX k g R hdim x
  rw [show (∃ y, y ≫ (degreeZeroOpenSubgroupScheme B hX k g R).ι.hom.hom = x) ↔
      ∃ y, y ≫ degreeZeroOverHom B hX k g R = x from
    ⟨fun ⟨y, hy⟩ => ⟨y ≫ e.inv, by rw [he, Category.assoc, e.inv_hom_id_assoc, hy]⟩,
      fun ⟨y, hy⟩ => ⟨y ≫ e.hom, by rw [Category.assoc, ← he, hy]⟩⟩,
    exists_comp_degreeZeroOverHom_iff]
  refine ⟨fun h => ?_, fun h p => (mem_degreeZeroOpens_iff B hX k g R _).2 ((hpt p).trans h)⟩
  let p0 : (𝟙_ (Over (Spec (.of k)))).left := (IsLocalRing.closedPoint k : Spec (.of k))
  exact (hpt p0).symm.trans ((mem_degreeZeroOpens_iff B hX k g R _).1 (h p0))

/-- **`Pic⁰(X)` is the group of `k`-points of `Pic⁰_{X/k}`**: the kernel of the degree on `Pic(X)`
is isomorphic to the group of `k`-points of `Stacks.PicardFunctor.degreeZeroOpenSubgroupScheme`. -/
def degreeZeroPointsAddEquiv (hdim : topologicalKrullDim X ≤ 1) :
    letI := representingGrpObj R
    (Stacks.Picard.ofSchemeDegree k (B.inclusion.map g) hdim).ker ≃+
      Additive (𝟙_ (Over (Spec (.of k))) ⟶ (degreeZeroOpenSubgroupScheme B hX k g R).carrier.X) :=
  kerOfSchemeDegreeAddEquivPointsOfOpenSubgroupScheme k g R hdim
    (degreeZeroOpenSubgroupScheme B hX k g R)
    (exists_comp_degreeZeroOpenSubgroupScheme_iff B hX k g R hdim)

end GroupLaw

end Stacks.PicardFunctor

end
