module

public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.UnitQuasicoherent
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Subgroups.Defs
public import StacksFrontier.AlgebraicGeometry.Picard.TorsionSmoothProjectiveCurve.Degree
public import StacksFrontier.AlgebraicGeometry.Picard.TorsionSmoothProjectiveCurve.PicardFunctorPoints
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.GroupScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation

/-!
# The group law on a scheme representing the Picard functor, and its rational points

Let `X ⟶ S` be a morphism of a big fppf site `B` and suppose that an `S`-scheme `P` of the site
represents the Picard functor `Pic_{X/S}` of [Stacks, Tag 0B9L]. The Picard functor takes values
in abelian groups (`Stacks.PicardFunctor.picardAddFunctor`), so by the Yoneda lemma `P` is a group
object, and the bijection `(T ⟶ P) ≃ Pic_{X/S}(T)` is an isomorphism of groups for every test
scheme `T`.

This is how the Picard *scheme* of [Stacks, Tag 0B9Z] becomes a group scheme, and it is the first
half of the identification, in the proof of [Stacks, Tag 0C1Z], of the group of `k`-points of
`Pic⁰_{X/k}` with `Pic⁰(X)`.

## Main definitions

* `Stacks.PicardFunctor.picardGrpFunctor`: the Picard functor with values in `GrpCat`, written
  multiplicatively.
* `Stacks.PicardFunctor.grpObjOfRepresentableBy`: the group-object structure on a representing
  scheme.

* `Stacks.PicardFunctor.representingGrpObj`: the same structure on the underlying scheme over
  `S`, carried along the monoidal functor `BigFppfOver.toOver`.
* `Stacks.PicardFunctor.representingPointsAddEquiv`: the `S`-points of that group scheme are
  `Pic_{X/S}(S)`, as groups.
* `Stacks.PicardFunctor.ofSchemeAddEquivRepresentingPoints`: for a smooth projective curve over
  an algebraically closed field, `Pic(X)` is the group of `k`-points of the Picard scheme.
* `Stacks.PicardFunctor.kerOfSchemeDegreeAddEquivPointsOfOpenSubgroupScheme`: `Pic⁰(X)` is the
  group of `k`-points of any open subgroup scheme whose `k`-points are the degree-zero classes.

## Main results

* `Stacks.PicardFunctor.RepresentableBy.homEquiv_mul`: the representing bijection carries the
  product of `T`-points to the sum of Picard classes.
* `Stacks.PicardFunctor.addSubgroupAddEquivPointsOfMono`: the points of a subgroup object are
  the subgroup of points they cut out.

## References

* [Stacks Project, Tag 0B9L](https://stacks.math.columbia.edu/tag/0B9L)
* [Stacks Project, Tag 0B9Z](https://stacks.math.columbia.edu/tag/0B9Z)
* [Stacks Project, Tag 0C1Z](https://stacks.math.columbia.edu/tag/0C1Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry Opposite

open scoped CategoryTheory.MonObj

universe u

namespace Stacks.PicardFunctor

variable (B : BigFppfSite.{u}) {X S : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S)
  (f : B.obj hX ⟶ B.obj hS)

/-- The Cartesian monoidal structure on the big fppf category over `S`, the slice category over
`S` of the underlying category of the site, by fibre products over `S`. -/
abbrev bigFppfOverCartesianMonoidal : CartesianMonoidalCategory (BigFppfOver B S hS) :=
  haveI : HasPullbacks B.Schemes := AlgebraicGeometry.Space.schemeCutoff_hasPullbacks B
  Over.cartesianMonoidalCategory (B.obj hS)

attribute [local instance] bigFppfOverCartesianMonoidal

/-- The Picard functor of sets is the underlying functor of the Picard functor in groups. -/
def picardFunctorIsoPicardGrpFunctor :
    picardFunctor B hX hS f ≅ picardGrpFunctor B hX hS f ⋙ forget GrpCat :=
  picardFunctorIsoPicardAddFunctor B hX hS f ≪≫
    NatIso.ofComponents (fun _ => (Multiplicative.ofAdd).toIso) (fun _ => rfl)

variable {B hX hS f}

/-- A representation of the Picard functor is a representation of the Picard functor in groups. -/
def representableByPicardGrpFunctor {P : BigFppfOver B S hS}
    (R : (picardFunctor B hX hS f).RepresentableBy P) :
    (picardGrpFunctor B hX hS f ⋙ forget GrpCat).RepresentableBy P :=
  R.ofIso (picardFunctorIsoPicardGrpFunctor B hX hS f)

/-- **The group-object structure on a scheme representing the Picard functor.** -/
abbrev grpObjOfRepresentableBy {P : BigFppfOver B S hS}
    (R : (picardFunctor B hX hS f).RepresentableBy P) : GrpObj P :=
  GrpObj.ofRepresentableBy P (picardGrpFunctor B hX hS f) (representableByPicardGrpFunctor R)

/-- **The representing bijection is multiplicative into the Picard group**: the product of two
`T`-points of `P` corresponds to the sum of the corresponding Picard classes. -/
theorem RepresentableBy.homEquiv_mul {P : BigFppfOver B S hS}
    (R : (picardFunctor B hX hS f).RepresentableBy P) {T : BigFppfOver B S hS} (a b : T ⟶ P) :
    letI := grpObjOfRepresentableBy R
    R.homEquiv (a * b) = R.homEquiv a + R.homEquiv b := by
  let := grpObjOfRepresentableBy R
  set α := representableByPicardGrpFunctor R
  have key : α.homEquiv' (a * b) = α.homEquiv' a * α.homEquiv' b := by
    rw [Hom.mul_def]
    show α.homEquiv' (lift a b ≫ α.homEquiv'.symm (α.homEquiv' (fst P P) *
      α.homEquiv' (snd P P))) = _
    simp only [α.homEquiv'_comp, Equiv.apply_symm_apply, map_mul]
    simp only [← α.homEquiv'_comp, lift_fst, lift_snd]
  have key' := congrArg Multiplicative.toAdd key
  set e := (picardFunctorIsoPicardAddFunctor B hX hS f).app (op T)
  change e.hom (R.homEquiv (a * b)) = e.hom (R.homEquiv a) + e.hom (R.homEquiv b) at key'
  show R.homEquiv (a * b) = e.inv (e.hom (R.homEquiv a) + e.hom (R.homEquiv b))
  rw [← key']
  exact (congrFun (congrArg DFunLike.coe (congrArg ConcreteCategory.hom e.hom_inv_id))
    (R.homEquiv (a * b))).symm

variable (B hS) in
/-- The functor from the big fppf category over `S` to schemes over `S` preserves finite limits. -/
theorem preservesFiniteLimits_toOver : PreservesFiniteLimits (BigFppfOver.toOver B S hS) := by
  have : HasPullbacks B.Schemes := AlgebraicGeometry.Space.schemeCutoff_hasPullbacks B
  have : HasFiniteLimits B.Schemes := hasFiniteLimits_of_hasTerminal_and_pullbacks
  have : PreservesFiniteLimits B.inclusion :=
    preservesFiniteLimits_of_preservesTerminal_and_pullbacks B.inclusion
  exact PreservesFiniteLimits.overPost (X := B.obj hS)

variable (B hS) in
/-- The functor from the big fppf category over `S` to schemes over `S` is monoidal for the
Cartesian structures, preserving finite products. -/
abbrev toOverMonoidal : (BigFppfOver.toOver B S hS).Monoidal :=
  haveI := preservesFiniteLimits_toOver B hS
  Functor.Monoidal.ofChosenFiniteProducts (BigFppfOver.toOver B S hS)

attribute [local instance] toOverMonoidal

variable (B hS) in
/-- The functor from the big fppf category over `S` to schemes over `S` is fully faithful. -/
def fullyFaithfulToOver : (BigFppfOver.toOver B S hS).FullyFaithful :=
  haveI : (Over.post (X := B.obj hS) B.inclusion).Full := inferInstance
  haveI : (Over.post (X := B.obj hS) B.inclusion).Faithful := inferInstance
  Functor.FullyFaithful.ofFullyFaithful (Over.post (X := B.obj hS) B.inclusion)

/-- Precomposition with an isomorphism is an isomorphism of groups of morphisms into a group
object. -/
def homMulEquivOfIso {C : Type*} [Category C] [CartesianMonoidalCategory C] {A A' M : C}
    [GrpObj M] (e : A ≅ A') : (A' ⟶ M) ≃* (A ⟶ M) where
  toFun g := e.hom ≫ g
  invFun g := e.inv ≫ g
  left_inv g := by simp
  right_inv g := by simp
  map_mul' g h := MonObj.comp_mul e.hom g h

/-- **The scheme over `S` underlying a representing object of the Picard functor**, with its group
structure (`Stacks.PicardFunctor.grpObjOfRepresentableBy`, carried along the monoidal functor
`BigFppfOver.toOver`). -/
abbrev representingGrpObj {P : BigFppfOver B S hS}
    (R : (picardFunctor B hX hS f).RepresentableBy P) :
    GrpObj ((BigFppfOver.toOver B S hS).obj P) :=
  letI := grpObjOfRepresentableBy R
  Functor.grpObjObj

/-- **The `S`-points of a scheme representing the Picard functor are `Pic_{X/S}(S)`, as groups.**
The group structure on the left is the one of `Stacks.PicardFunctor.representingGrpObj`. -/
def representingPointsAddEquiv {P : BigFppfOver B S hS}
    (R : (picardFunctor B hX hS f).RepresentableBy P) :
    letI := representingGrpObj R
    Additive (𝟙_ (Over S) ⟶ (BigFppfOver.toOver B S hS).obj P) ≃+
      (picardFunctor B hX hS f).obj (op (terminalTest B hS)) :=
  letI := grpObjOfRepresentableBy R
  letI := representingGrpObj R
  have hid : B.inclusion.map (𝟙 (B.obj hS)) = 𝟙 S := CategoryTheory.Functor.map_id _ _
  let eT : 𝟙_ (Over S) ≅ (BigFppfOver.toOver B S hS).obj (terminalTest B hS) :=
    { hom := Over.homMk (𝟙 _) (by
        change 𝟙 S ≫ B.inclusion.map (𝟙 (B.obj hS)) = 𝟙 S
        rw [hid, Category.comp_id])
      inv := Over.homMk (𝟙 _) (by
        change 𝟙 S ≫ 𝟙 S = B.inclusion.map (𝟙 (B.obj hS))
        rw [hid, Category.comp_id])
      hom_inv_id := Over.OverMorphism.ext (Category.comp_id _)
      inv_hom_id := Over.OverMorphism.ext (Category.comp_id _) }
  let m : (terminalTest B hS ⟶ P) ≃* (𝟙_ (Over S) ⟶ (BigFppfOver.toOver B S hS).obj P) :=
    ((fullyFaithfulToOver B hS).homMulEquiv).trans (homMulEquivOfIso eT)
  (MulEquiv.toAdditive m.symm).trans
    { toEquiv := R.homEquiv
      map_add' := fun a b => RepresentableBy.homEquiv_mul R a b }

/-- **The section attached to an `S`-point of the representing scheme.** The image of an `S`-point
`x` under `Stacks.PicardFunctor.representingPointsAddEquiv` is `R.homEquiv xB` for a morphism
`xB : S ⟶ P` of the site with the same underlying morphism of schemes as `x`. -/
theorem exists_representingPointsAddEquiv_eq {P : BigFppfOver B S hS}
    (R : (picardFunctor B hX hS f).RepresentableBy P) :
    letI := representingGrpObj R
    ∀ x : 𝟙_ (Over S) ⟶ (BigFppfOver.toOver B S hS).obj P,
      ∃ xB : terminalTest B hS ⟶ P,
        (BigFppfOver.toScheme B S hS).map xB = x.left ∧
          representingPointsAddEquiv R (Additive.ofMul x) = R.homEquiv xB := by
  let := grpObjOfRepresentableBy R
  let := representingGrpObj R
  intro x
  have hid : B.inclusion.map (𝟙 (B.obj hS)) = 𝟙 S := CategoryTheory.Functor.map_id _ _
  let eT : 𝟙_ (Over S) ≅ (BigFppfOver.toOver B S hS).obj (terminalTest B hS) :=
    { hom := Over.homMk (𝟙 _) (by
        show 𝟙 S ≫ B.inclusion.map (𝟙 (B.obj hS)) = 𝟙 S
        rw [hid, Category.comp_id])
      inv := Over.homMk (𝟙 _) (by
        show 𝟙 S ≫ 𝟙 S = B.inclusion.map (𝟙 (B.obj hS))
        rw [hid, Category.comp_id])
      hom_inv_id := Over.OverMorphism.ext (Category.comp_id _)
      inv_hom_id := Over.OverMorphism.ext (Category.comp_id _) }
  refine ⟨(fullyFaithfulToOver B hS).preimage (eT.inv ≫ x), ?_, rfl⟩
  have h := congrArg (fun φ => φ.left) ((fullyFaithfulToOver B hS).map_preimage (eT.inv ≫ x))
  exact h.trans (Category.id_comp _)

section Curve

variable (k : Type u) [Field k] [IsAlgClosed k] {hk : B.Contains (Spec (.of k))}
  (g : B.obj hX ⟶ B.obj hk) [IsCurve k (B.inclusion.map g)]
  [IsProjectiveVariety k (B.inclusion.map g)] [Smooth (B.inclusion.map g)]

/-- **The Picard group of a smooth projective curve over an algebraically closed field is the
group of `k`-points of a scheme representing its Picard functor**, with the group law of
`Stacks.PicardFunctor.representingGrpObj`. -/
def ofSchemeAddEquivRepresentingPoints {P : BigFppfOver B (Spec (.of k)) hk}
    (R : (picardFunctor B hX hk g).RepresentableBy P) :
    letI := representingGrpObj R
    Stacks.Picard.ofScheme X ≃+
      Additive (𝟙_ (Over (Spec (.of k))) ⟶ (BigFppfOver.toOver B (Spec (.of k)) hk).obj P) :=
  letI := representingGrpObj R
  (ofSchemeAddEquivPicardFunctorOfCurve B hX k g).trans (representingPointsAddEquiv R).symm

end Curve

/-- **The points of a subgroup object.** Let `i : A ⟶ M` be a monomorphism of group objects in a
Cartesian monoidal category, and let `e : G ≃+ M(𝟙)` identify the points of `M` with an
additive group `G`. If the points of `M` factoring through `i` are exactly those coming from a
subgroup `H` of `G`, then `H` is the group of points of `A`. -/
def addSubgroupAddEquivPointsOfMono {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {A M : C} [GrpObj A] [GrpObj M] (i : A ⟶ M) [IsMonHom i] [Mono i] {G : Type*} [AddGroup G]
    (e : G ≃+ Additive (𝟙_ C ⟶ M)) (H : AddSubgroup G)
    (h : ∀ x : 𝟙_ C ⟶ M, (∃ y, y ≫ i = x) ↔ e.symm (Additive.ofMul x) ∈ H) :
    H ≃+ Additive (𝟙_ C ⟶ A) :=
  let ψ : Additive (𝟙_ C ⟶ A) →+ G :=
    e.symm.toAddMonoidHom.comp (MonoidHom.toAdditive (IsMonHom.monoidHom i (𝟙_ C)))
  have hψ : ∀ y, ψ y = e.symm (Additive.ofMul (y.toMul ≫ i)) := fun _ => rfl
  let φ : Additive (𝟙_ C ⟶ A) →+ H :=
    ψ.codRestrict H fun y => by rw [hψ]; exact (h _).1 ⟨y.toMul, rfl⟩
  (AddEquiv.ofBijective φ ⟨fun y y' hyy' => by
      have h1 : ψ y = ψ y' := congrArg Subtype.val hyy'
      rw [hψ, hψ] at h1
      exact Additive.toMul.injective
        ((cancel_mono i).1 (Additive.ofMul.injective (e.symm.injective h1))),
    fun z => by
      obtain ⟨y, hy⟩ := (h (e (z : G)).toMul).2 (by simp)
      refine ⟨Additive.ofMul y, Subtype.ext ?_⟩
      change ψ (Additive.ofMul y) = z
      rw [hψ]
      simp [hy]⟩).symm

section Curve

variable (k : Type u) [Field k] [IsAlgClosed k] {hk : B.Contains (Spec (.of k))}
  (g : B.obj hX ⟶ B.obj hk) [IsCurve k (B.inclusion.map g)]
  [IsProjectiveVariety k (B.inclusion.map g)] [Smooth (B.inclusion.map g)]

/-- **`Pic⁰(X)` is the group of `k`-points of an open subgroup scheme of the Picard scheme whose
`k`-points are the classes of degree zero.** Let `P` represent the Picard functor of a smooth
projective curve `X` over an algebraically closed field `k`, with the group law of
`Stacks.PicardFunctor.representingGrpObj`, and let `H` be an open subgroup scheme of it such that
a `k`-point of `P` factors through `H` exactly when the corresponding Picard class has degree
zero. Then `Pic⁰(X) = ker deg` is isomorphic to the group of `k`-points of `H`. -/
def kerOfSchemeDegreeAddEquivPointsOfOpenSubgroupScheme {P : BigFppfOver B (Spec (.of k)) hk}
    (R : (picardFunctor B hX hk g).RepresentableBy P) (hdim : topologicalKrullDim X ≤ 1)
    (H : letI := representingGrpObj R
      OpenSubgroupScheme (Grp.mk ((BigFppfOver.toOver B (Spec (.of k)) hk).obj P)))
    (hH : letI := representingGrpObj R
      ∀ x : 𝟙_ (Over (Spec (.of k))) ⟶ (BigFppfOver.toOver B (Spec (.of k)) hk).obj P,
        (∃ y, y ≫ H.ι.hom.hom = x) ↔
          Stacks.Picard.ofSchemeDegree k (B.inclusion.map g) hdim
            ((ofSchemeAddEquivRepresentingPoints k g R).symm (Additive.ofMul x)) = 0) :
    (Stacks.Picard.ofSchemeDegree k (B.inclusion.map g) hdim).ker ≃+
      Additive (𝟙_ (Over (Spec (.of k))) ⟶ H.carrier.X) :=
  letI := representingGrpObj R
  haveI : IsOpenImmersion H.ι.hom.hom.left := H.isOpenImmersion
  haveI : Mono H.ι.hom.hom := Over.mono_of_mono_left _
  addSubgroupAddEquivPointsOfMono H.ι.hom.hom (ofSchemeAddEquivRepresentingPoints k g R)
    _ hH

end Curve

end Stacks.PicardFunctor

end
