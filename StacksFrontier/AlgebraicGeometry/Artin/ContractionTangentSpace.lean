module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionOnePoint
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSolutionModification
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAlgebraicSpaceAtlas
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TangentRingChart
public import StacksFrontier.Deformation.Artin.FunctorTangentSpace

/-!
# The tangent spaces of Artin's contraction functor are finite dimensional (Stacks 0GI7)

In Situation 0GH8, let `F` be the functor of Stacks 0GHA. Its tangent spaces are finite
dimensional: this is axiom `[3]` for `F`, in the form
`AlgebraicGeometry.LocallyNoetherianOver.HasFiniteDimensionalTangentSpaces`.

The proof is the one of the source. A deformation of a point `x₀ = (Z₀, u'₀, x̂₀)` of `F` over
`Spec k` lives over the spectrum of an Artinian local ring, which has a single point; so it is
either a triple with `Z = ∅`, determined by `u' : V ⟶ U' ⊆ X'`, or a triple with `Z = V`,
determined by `x̂ : V ⟶ W`
(`AlgebraicGeometry.Artin.ContractionSituation.Triple.ext_of_Z_eq_empty`,
`AlgebraicGeometry.Artin.ContractionSituation.Triple.ext_of_Z_eq_univ`), according as `Z₀` is
empty or not. In both cases the deformations of `x₀` inject, compatibly with the maps of
square-zero extensions, into the first-order deformations of a point of a locally Noetherian
formal algebraic space `P`: the completion `X'_{/|X'|}` of `X'` along all of its points in the
first case (an algebraic space locally of finite type over `S` is locally Noetherian, Stacks
0AQ1 (2)), and `W` itself in the second. The source then appeals to Stacks 07X1 for `U'` and for
the second infinitesimal neighbourhood `W₂` of `W_red` in `W`; here the bound on the tangent
space of `P` is read off an étale chart of `P` directly
(`AlgebraicGeometry.FormalSpace.TangentChart.exists_ringChart`), which covers both cases at once,
and the criterion `Deformation.finiteDimensional_artinianTangentSpace_of_ringValue` concludes.

## Main results

* `AlgebraicGeometry.Artin.ContractionSituation.hasFiniteDimensionalTangentSpaces`: the
  finite-dimensionality of Stacks 0GI7, for every vector-space structure of Stacks 06IH on the
  tangent spaces; the registered form, with that structure constructed from (RS), is
  `AlgebraicGeometry.Artin.ContractionSituation.finiteDimensional_artinianTangentSpace`.

## References

* [Stacks Project, Tag 0GI7](https://stacks.math.columbia.edu/tag/0GI7)
* [Stacks Project, Tag 0GI6](https://stacks.math.columbia.edu/tag/0GI6)
* [Stacks Project, Tag 07X1](https://stacks.math.columbia.edu/tag/07X1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe u

namespace AlgebraicGeometry.Artin.ContractionSituation

open Deformation Deformation.Artin FormalSpace.TangentChart

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (c : ContractionSituation B S hS)

/-! ### Elements of the functor -/

/-- The object of the site underlying an element of `F`. -/
abbrev siteOf (x : (contractionFunctor c).Elementsᵒᵖ) : BigFppfOver B S hS := x.unop.1.unop.obj

/-- The triple of an element of `F`. -/
abbrev tripleOf (x : (contractionFunctor c).Elementsᵒᵖ) : Triple c (siteOf c x) := x.unop.2

/-- The morphism of the site underlying an arrow of the category fibred in sets of `F`. -/
abbrev siteMap {x y : (contractionFunctor c).Elementsᵒᵖ} (a : x ⟶ y) : siteOf c x ⟶ siteOf c y :=
  a.unop.1.unop.hom

/-- The triple of the source of an arrow of `F` is the restriction of the triple of its target. -/
theorem tripleOf_map {x y : (contractionFunctor c).Elementsᵒᵖ} (a : x ⟶ y) :
    mapTriple c (siteMap c a) (tripleOf c y) = tripleOf c x := a.unop.2

/-- `siteMap` is functorial. -/
theorem siteMap_comp {x y z : (contractionFunctor c).Elementsᵒᵖ} (a : x ⟶ y) (b : y ⟶ z) :
    siteMap c (a ≫ b) = siteMap c a ≫ siteMap c b := rfl

/-! ### Transport along equalities of Artinian algebras -/

section Transport

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]

/-- `Spec A → Spec Λ` is compatible with an equality `A = A'` of Artinian algebras. -/
theorem eqToHom_spec_algebraMap {A A' : ArtinianLocalAlgCat.{u, u, u} Λ k} (h : A = A') :
    eqToHom (congrArg (fun A : ArtinianLocalAlgCat.{u, u, u} Λ k => Spec (CommRingCat.of A)) h) ≫
      Spec.map (CommRingCat.ofHom (algebraMap Λ A')) =
        Spec.map (CommRingCat.ofHom (algebraMap Λ A)) := by
  subst h; simp

/-- `Spec k → Spec A` is compatible with an equality `A = A'` of Artinian algebras. -/
theorem spec_residueMap_eqToHom {A A' : ArtinianLocalAlgCat.{u, u, u} Λ k} (h : A = A') :
    Spec.map (CommRingCat.ofHom (residueMap A)) =
      Spec.map (CommRingCat.ofHom (residueMap A')) ≫
        eqToHom (congrArg (fun A : ArtinianLocalAlgCat.{u, u, u} Λ k =>
          Spec (CommRingCat.of A)) h).symm := by
  subst h; simp

/-- `Spec` of a morphism of Artinian algebras conjugated by equalities. -/
theorem spec_eqToHom_comp {A A₁ A' A₁' : ArtinianLocalAlgCat.{u, u, u} Λ k} (hx : A = A₁)
    (hy : A' = A₁') (g : A₁ ⟶ A₁') :
    Spec.map (CommRingCat.ofHom (eqToHom hx ≫ g ≫ eqToHom hy.symm).hom.toRingHom) =
      eqToHom (congrArg (fun A : ArtinianLocalAlgCat.{u, u, u} Λ k =>
          Spec (CommRingCat.of A)) hy) ≫ Spec.map (CommRingCat.ofHom g.hom.toRingHom) ≫
        eqToHom (congrArg (fun A : ArtinianLocalAlgCat.{u, u, u} Λ k =>
          Spec (CommRingCat.of A)) hx).symm := by
  subst hx hy; simp

end Transport

/-! ### Reading the deformations of a point in a formal algebraic space -/

/-- A way of reading the deformations of a point `t₀ ∈ F(V₀)` as points of a locally Noetherian
formal algebraic space `P`: a class `Good` of triples containing every triple over a one-point
scheme which restricts to `t₀`, stable under restriction, and an injective map from `Good`
triples to sections of `P`, compatible with restriction. -/
structure PointRead (V₀ : BigFppfOver B S hS) (t₀ : Triple c V₀) where
  /-- The formal algebraic space. -/
  P : FormalSpace.FppfSheaf B S hS
  /-- It is locally Noetherian. -/
  isLocallyNoetherian : FormalSpace.IsLocallyNoetherian B S hS P
  /-- The triples which are read. -/
  Good : ∀ {V : BigFppfOver B S hS}, Triple c V → Prop
  /-- The reading of a triple. -/
  val : ∀ {V : BigFppfOver B S hS} (t : Triple c V), Good t → P.obj.obj (op V)
  /-- The class of read triples is stable under restriction. -/
  good_map : ∀ {V₂ V₁ : BigFppfOver B S hS} (φ : V₂ ⟶ V₁) (t : Triple c V₁), Good t →
    Good (mapTriple c φ t)
  /-- The reading is compatible with restriction. -/
  val_map : ∀ {V₂ V₁ : BigFppfOver B S hS} (φ : V₂ ⟶ V₁) (t : Triple c V₁) (ht : Good t),
    val (mapTriple c φ t) (good_map φ t ht) = P.obj.map φ.op (val t ht)
  /-- The reading is injective. -/
  val_inj : ∀ {V : BigFppfOver B S hS} (t t' : Triple c V) (ht : Good t) (ht' : Good t'),
    val t ht = val t' ht' → t = t'
  /-- Every triple over a scheme with at most one point which restricts to `t₀` is read. -/
  good_of_map : ∀ {V : BigFppfOver B S hS}, Subsingleton ((BigFppfOver.toScheme B S hS).obj V) →
    ∀ (φ : V₀ ⟶ V) (t : Triple c V), mapTriple c φ t = t₀ → Good t

variable {c}

/-- The reading does not depend on the proof that the triple is read. -/
theorem PointRead.val_congr {V₀ : BigFppfOver B S hS} {t₀ : Triple c V₀}
    (R : PointRead c V₀ t₀) {V : BigFppfOver B S hS} {t t' : Triple c V} (h : t = t')
    (ht : R.Good t) (ht' : R.Good t') : R.val t ht = R.val t' ht' := by
  subst h; rfl

/-- If `V₀` has at most one point, then `t₀` is read. -/
theorem PointRead.good₀ {V₀ : BigFppfOver B S hS} {t₀ : Triple c V₀} (R : PointRead c V₀ t₀)
    (h : Subsingleton ((BigFppfOver.toScheme B S hS).obj V₀)) : R.Good t₀ :=
  R.good_of_map h (𝟙 V₀) t₀ (mapTriple_id c t₀)

/-! ### Deformations of a point of `F` as test data -/

section Deformations

/-- The right `k`-module structure on a vector space under which `TrivSqZeroExt k V` is formed in
`Deformation.squareZeroExtensionArtinian`. -/
local instance {k : Type u} [Field k] (V : FGModuleCat.{u} k) : Module kᵐᵒᵖ V :=
  Module.compHom V {
    toFun := MulOpposite.unop
    map_one' := rfl
    map_mul' := by simp [mul_comm]
    map_zero' := rfl
    map_add' := by intros; rfl }

/-- The left and right `k`-module structures on a vector space agree. -/
local instance {k : Type u} [Field k] (V : FGModuleCat.{u} k) : IsCentralScalar k V where
  op_smul_eq_smul _ _ := rfl

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] {iΛ : Spec (.of Λ) ⟶ S}
  {x₀ : (contractionFunctor c).Elementsᵒᵖ}
  (hx₀ : (LocallyNoetherianOver.elementsToOver B S hS (contractionFunctor c)).obj x₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))

include hx₀ in
/-- The scheme of the base point `x₀` is `Spec k`. -/
theorem siteOf_eq₀ : (BigFppfOver.toScheme B S hS).obj (siteOf c x₀) = Spec (.of k) :=
  congrArg Over.left hx₀

/-- The structure morphism of the base point `x₀` is `Spec k → Spec Λ → S`. -/
theorem siteOf_hom_eq₀ : B.inclusion.map (siteOf c x₀).hom = eqToHom (siteOf_eq₀ hx₀) ≫
    Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ := by
  have h := Over.w (eqToHom hx₀)
  rw [Over.eqToHom_left] at h
  exact h.symm

variable {hx₀}

/-- The scheme of a deformation `o` of `x₀` is `Spec A`, for `A` its Artinian algebra. -/
theorem defSiteOf_eq
    (o : DeformationObject iΛ (LocallyNoetherianOver.elementsToOver B S hS (contractionFunctor c))
      x₀ hx₀) :
    (BigFppfOver.toScheme B S hS).obj (siteOf c o.point) = Spec (.of o.algebra) :=
  congrArg Over.left o.base

/-- The structure morphism of a deformation over `A` is `Spec A → Spec Λ → S`. -/
theorem defSiteOf_hom_eq
    (o : DeformationObject iΛ (LocallyNoetherianOver.elementsToOver B S hS (contractionFunctor c))
      x₀ hx₀) :
    B.inclusion.map (siteOf c o.point).hom = eqToHom (defSiteOf_eq o) ≫
      Spec.map (CommRingCat.ofHom (algebraMap Λ o.algebra)) ≫ iΛ := by
  have h := Over.w (eqToHom o.base)
  rw [Over.eqToHom_left] at h
  exact h.symm

/-- The arrow from a deformation over `A` to `x₀` lies over `Spec k → Spec A`. -/
theorem defSiteMap_arrow_eq
    (o : DeformationObject iΛ (LocallyNoetherianOver.elementsToOver B S hS (contractionFunctor c))
      x₀ hx₀) :
    B.inclusion.map (siteMap c o.arrow).left = eqToHom (siteOf_eq₀ hx₀) ≫
      Spec.map (CommRingCat.ofHom (residueMap o.algebra)) ≫ eqToHom (defSiteOf_eq o).symm := by
  have h : eqToHom (siteOf_eq₀ hx₀).symm ≫ B.inclusion.map (siteMap c o.arrow).left ≫
      eqToHom (defSiteOf_eq o) = Spec.map (CommRingCat.ofHom (residueMap o.algebra)) := o.arrow_base
  rw [← h]
  simp

/-- The test datum of a deformation over `k[V]`. -/
def defTestDatum
    (o : DeformationObject iΛ (LocallyNoetherianOver.elementsToOver B S hS (contractionFunctor c))
      x₀ hx₀) {V : FGModuleCat.{u} k}
    (hA : o.algebra = (artinianSquareZeroExtensionFunctor Λ k).obj V) :
    TestDatum iΛ (siteOf c x₀) (siteOf_eq₀ hx₀) V where
  T := siteOf c o.point
  eS := (defSiteOf_eq o).trans (congrArg (fun A : ArtinianLocalAlgCat.{u, u, u} Λ k =>
    Spec (CommRingCat.of A)) hA)
  hom_eq := by
    have : B.inclusion.map (siteOf c o.point).hom = eqToHom ((defSiteOf_eq o).trans
        (congrArg (fun A : ArtinianLocalAlgCat.{u, u, u} Λ k => Spec (CommRingCat.of A)) hA)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap Λ
            ((artinianSquareZeroExtensionFunctor Λ k).obj V))) ≫ iΛ := by
      rw [defSiteOf_hom_eq o, ← eqToHom_spec_algebraMap hA]
      simp
    exact this
  j := siteMap c o.arrow
  j_eq := by
    have : B.inclusion.map (siteMap c o.arrow).left = eqToHom (siteOf_eq₀ hx₀) ≫
        Spec.map (CommRingCat.ofHom (residueMap
          ((artinianSquareZeroExtensionFunctor Λ k).obj V))) ≫ eqToHom ((defSiteOf_eq o).trans
        (congrArg (fun A : ArtinianLocalAlgCat.{u, u, u} Λ k =>
          Spec (CommRingCat.of A)) hA)).symm := by
      rw [defSiteMap_arrow_eq o, spec_residueMap_eqToHom hA]
      simp
    exact this

/-- The scheme of a deformation over `k[V]` has a single point. -/
theorem subsingleton_siteOf
    (o : DeformationObject iΛ (LocallyNoetherianOver.elementsToOver B S hS (contractionFunctor c))
      x₀ hx₀) {V : FGModuleCat.{u} k}
    (hA : o.algebra = (artinianSquareZeroExtensionFunctor Λ k).obj V) :
    Subsingleton ((BigFppfOver.toScheme B S hS).obj (siteOf c o.point)) := by
  have e : (BigFppfOver.toScheme B S hS).obj (siteOf c o.point) =
      Spec (.of (TrivSqZeroExt k V)) := (defTestDatum o hA).eS
  rw [e]
  exact subsingleton_spec_squareZero V

variable (R : PointRead c (siteOf c x₀) (tripleOf c x₀))

/-- The point of `P` read off a deformation over `k[V]`. -/
def pointOf
    (o : DeformationObject iΛ (LocallyNoetherianOver.elementsToOver B S hS (contractionFunctor c))
      x₀ hx₀) {V : FGModuleCat.{u} k}
    (hA : o.algebra = (artinianSquareZeroExtensionFunctor Λ k).obj V) :
    R.P.obj.obj (op (siteOf c o.point)) :=
  R.val (tripleOf c o.point) (R.good_of_map (subsingleton_siteOf o hA) (siteMap c o.arrow) _
    (tripleOf_map c o.arrow))

include hx₀ in
/-- The point of `P` read off `x₀`. -/
def pointOf₀ : R.P.obj.obj (op (siteOf c x₀)) :=
  R.val (tripleOf c x₀) (R.good₀ (by rw [siteOf_eq₀ hx₀]; infer_instance))

/-- The point of `P` read off a deformation restricts to the point read off `x₀`. -/
theorem pointOf_j
    (o : DeformationObject iΛ (LocallyNoetherianOver.elementsToOver B S hS (contractionFunctor c))
      x₀ hx₀) {V : FGModuleCat.{u} k}
    (hA : o.algebra = (artinianSquareZeroExtensionFunctor Λ k).obj V) :
    R.P.obj.map (siteMap c o.arrow).op (pointOf R o hA) = pointOf₀ (hx₀ := hx₀) R := by
  rw [pointOf, ← R.val_map]
  exact R.val_congr (tripleOf_map c o.arrow) _ _

/-- The morphism of test data underlying a morphism of deformations over `k[V] ⟶ k[V']`. -/
def testDatumHom
    {o o' : DeformationObject iΛ (LocallyNoetherianOver.elementsToOver B S hS
      (contractionFunctor c)) x₀ hx₀} (a : DeformationMorphism iΛ
        (LocallyNoetherianOver.elementsToOver B S hS (contractionFunctor c)) x₀ hx₀ o o')
    {V V' : FGModuleCat.{u} k} (f : V ⟶ V')
    (hA : o.algebra = (artinianSquareZeroExtensionFunctor Λ k).obj V)
    (hA' : o'.algebra = (artinianSquareZeroExtensionFunctor Λ k).obj V')
    (hf : a.ringHom = eqToHom hA ≫ (artinianSquareZeroExtensionFunctor Λ k).map f ≫
      eqToHom hA'.symm) :
    TestDatum.Hom f (defTestDatum o hA) (defTestDatum o' hA') where
  m := siteMap c a.arrow
  m_eq := by
    have h : eqToHom (defSiteOf_eq o').symm ≫ B.inclusion.map (siteMap c a.arrow).left ≫
        eqToHom (defSiteOf_eq o) = Spec.map (CommRingCat.ofHom a.ringHom.hom.toRingHom) :=
      a.arrow_base
    rw [hf, spec_eqToHom_comp hA hA'] at h
    have key : B.inclusion.map (siteMap c a.arrow).left = eqToHom (defSiteOf_eq o') ≫
        (eqToHom (defSiteOf_eq o').symm ≫ B.inclusion.map (siteMap c a.arrow).left ≫
          eqToHom (defSiteOf_eq o)) ≫ eqToHom (defSiteOf_eq o).symm := by
      simp
    rw [h] at key
    refine key.trans ?_
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
    rfl
  j_m := (siteMap_comp c _ _).symm.trans (congrArg (siteMap c) a.triangle)

/-- The points of `P` read off deformations are compatible with morphisms of deformations. -/
theorem pointOf_hom
    {o o' : DeformationObject iΛ (LocallyNoetherianOver.elementsToOver B S hS
      (contractionFunctor c)) x₀ hx₀} (a : DeformationMorphism iΛ
        (LocallyNoetherianOver.elementsToOver B S hS (contractionFunctor c)) x₀ hx₀ o o')
    {V V' : FGModuleCat.{u} k}
    (hA : o.algebra = (artinianSquareZeroExtensionFunctor Λ k).obj V)
    (hA' : o'.algebra = (artinianSquareZeroExtensionFunctor Λ k).obj V') :
    pointOf R o' hA' = R.P.obj.map (siteMap c a.arrow).op (pointOf R o hA) := by
  rw [pointOf, pointOf, ← R.val_map]
  exact R.val_congr (tripleOf_map c a.arrow).symm _ _

/-- `Spec` of an equality of Artinian algebras. -/
theorem spec_eqToHom {A A' : ArtinianLocalAlgCat.{u, u, u} Λ k} (h : A = A') :
    Spec.map (CommRingCat.ofHom (eqToHom h).hom.toRingHom) =
      eqToHom (congrArg (fun A : ArtinianLocalAlgCat.{u, u, u} Λ k =>
        Spec (CommRingCat.of A)) h).symm := by
  subst h; simp

/-- The scheme of a deformation over `k[V]` is `Spec k[V]`. -/
theorem canonEq
    (o : DeformationObject iΛ (LocallyNoetherianOver.elementsToOver B S hS
      (contractionFunctor c)) x₀ hx₀) {V : FGModuleCat.{u} k}
    (hA : o.algebra = (artinianSquareZeroExtensionFunctor Λ k).obj V) :
    B.inclusion.obj (siteOf c o.point).left = Spec (.of (TrivSqZeroExt k V)) :=
  (defTestDatum o hA).eS

/-- The structure morphism of a deformation over `k[V]` is `Spec k[V] → Spec Λ → S`. -/
theorem canonEq_hom
    (o : DeformationObject iΛ (LocallyNoetherianOver.elementsToOver B S hS
      (contractionFunctor c)) x₀ hx₀) {V : FGModuleCat.{u} k}
    (hA : o.algebra = (artinianSquareZeroExtensionFunctor Λ k).obj V) :
    B.inclusion.map (siteOf c o.point).hom = eqToHom (canonEq o hA) ≫
      Spec.map (CommRingCat.ofHom (algebraMap Λ
        ((artinianSquareZeroExtensionFunctor Λ k).obj V))) ≫ iΛ :=
  (defTestDatum o hA).hom_eq

/-- The arrow from a deformation over `k[V]` to `x₀` lies over `Spec k → Spec k[V]`. -/
theorem canonEq_j
    (o : DeformationObject iΛ (LocallyNoetherianOver.elementsToOver B S hS
      (contractionFunctor c)) x₀ hx₀) {V : FGModuleCat.{u} k}
    (hA : o.algebra = (artinianSquareZeroExtensionFunctor Λ k).obj V) :
    B.inclusion.map (siteMap c o.arrow).left = eqToHom (siteOf_eq₀ hx₀) ≫
      Spec.map (CommRingCat.ofHom (residueMap
        ((artinianSquareZeroExtensionFunctor Λ k).obj V))) ≫ eqToHom (canonEq o hA).symm :=
  (defTestDatum o hA).j_eq

/-- The identification of the schemes of two deformations over the same `k[V]`. -/
def canonicalSite
    (o o' : DeformationObject iΛ (LocallyNoetherianOver.elementsToOver B S hS
      (contractionFunctor c)) x₀ hx₀) {V : FGModuleCat.{u} k}
    (hA : o.algebra = (artinianSquareZeroExtensionFunctor Λ k).obj V)
    (hA' : o'.algebra = (artinianSquareZeroExtensionFunctor Λ k).obj V) :
    siteOf c o'.point ⟶ siteOf c o.point :=
  Over.homMk (B.inclusion.preimage (X := (siteOf c o'.point).left)
    (Y := (siteOf c o.point).left) (eqToHom ((canonEq o' hA').trans (canonEq o hA).symm))) (by
      apply B.inclusion.map_injective
      rw [Functor.map_comp, Functor.map_preimage, canonEq_hom o hA, canonEq_hom o' hA',
        eqToHom_trans_assoc])

/-- The underlying morphism of schemes of `canonicalSite`. -/
theorem toScheme_canonicalSite
    (o o' : DeformationObject iΛ (LocallyNoetherianOver.elementsToOver B S hS
      (contractionFunctor c)) x₀ hx₀) {V : FGModuleCat.{u} k}
    (hA : o.algebra = (artinianSquareZeroExtensionFunctor Λ k).obj V)
    (hA' : o'.algebra = (artinianSquareZeroExtensionFunctor Λ k).obj V) :
    B.inclusion.map (canonicalSite o o' hA hA').left =
      eqToHom ((canonEq o' hA').trans (canonEq o hA).symm) :=
  Functor.map_preimage _ _

/-- `canonicalSite` is compatible with the arrows to `x₀`. -/
theorem siteMap_canonicalSite
    (o o' : DeformationObject iΛ (LocallyNoetherianOver.elementsToOver B S hS
      (contractionFunctor c)) x₀ hx₀) {V : FGModuleCat.{u} k}
    (hA : o.algebra = (artinianSquareZeroExtensionFunctor Λ k).obj V)
    (hA' : o'.algebra = (artinianSquareZeroExtensionFunctor Λ k).obj V) :
    siteMap c o'.arrow ≫ canonicalSite o o' hA hA' = siteMap c o.arrow := by
  apply (BigFppfOver.forget B S hS).map_injective
  apply B.inclusion.map_injective
  show B.inclusion.map ((siteMap c o'.arrow).left ≫ (canonicalSite o o' hA hA').left) =
    B.inclusion.map (siteMap c o.arrow).left
  rw [Functor.map_comp, toScheme_canonicalSite, canonEq_j o' hA', canonEq_j o hA]
  simp only [Category.assoc]
  congr 2
  exact eqToHom_trans _ _

/-- The identification as a morphism of test data. -/
def canonicalMap
    (o o' : DeformationObject iΛ (LocallyNoetherianOver.elementsToOver B S hS
      (contractionFunctor c)) x₀ hx₀) {V : FGModuleCat.{u} k}
    (hA : o.algebra = (artinianSquareZeroExtensionFunctor Λ k).obj V)
    (hA' : o'.algebra = (artinianSquareZeroExtensionFunctor Λ k).obj V) :
    TestDatum.Hom (𝟙 V) (defTestDatum o hA) (defTestDatum o' hA') where
  m := canonicalSite o o' hA hA'
  m_eq := by
    have : B.inclusion.map (canonicalSite o o' hA hA').left = eqToHom (canonEq o' hA') ≫
        Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map (𝟙 V : V ⟶ V).hom.hom).toRingHom) ≫
          eqToHom (canonEq o hA).symm := by
      rw [toScheme_canonicalSite]
      change _ = _ ≫ Spec.map (CommRingCat.ofHom
        (TrivSqZeroExt.map (LinearMap.id : V →ₗ[k] V)).toRingHom) ≫ _
      rw [TrivSqZeroExt.map_id]
      simp
    exact this
  j_m := siteMap_canonicalSite o o' hA hA'

/-- Two deformations over the same `k[V]` whose triples correspond under the identification of
their schemes are joined by a morphism of deformations over the identity. -/
def deformationMorphismOfEq
    (o o' : DeformationObject iΛ (LocallyNoetherianOver.elementsToOver B S hS
      (contractionFunctor c)) x₀ hx₀) {V : FGModuleCat.{u} k}
    (hA : o.algebra = (artinianSquareZeroExtensionFunctor Λ k).obj V)
    (hA' : o'.algebra = (artinianSquareZeroExtensionFunctor Λ k).obj V)
    (ht : mapTriple c (canonicalSite o o' hA hA') (tripleOf c o.point) = tripleOf c o'.point) :
    DeformationMorphism iΛ (LocallyNoetherianOver.elementsToOver B S hS (contractionFunctor c))
      x₀ hx₀ o o' where
  ringHom := eqToHom (hA.trans hA'.symm)
  arrow := Quiver.Hom.op ⟨(ObjectProperty.homMk (canonicalSite o o' hA hA') :
    o'.point.unop.1.unop ⟶ o.point.unop.1.unop).op, ht⟩
  triangle := by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    exact siteMap_canonicalSite o o' hA hA'
  arrow_base := by
    change eqToHom (defSiteOf_eq o').symm ≫
        B.inclusion.map (canonicalSite o o' hA hA').left ≫ eqToHom (defSiteOf_eq o) =
          Spec.map (CommRingCat.ofHom (eqToHom (hA.trans hA'.symm)).hom.toRingHom)
    rw [toScheme_canonicalSite, spec_eqToHom]
    simp

/-- The triple of a deformation over `k[V]` is read. -/
private theorem good_tripleOf
    (o : DeformationObject iΛ (LocallyNoetherianOver.elementsToOver B S hS
      (contractionFunctor c)) x₀ hx₀) {V : FGModuleCat.{u} k}
    (hA : o.algebra = (artinianSquareZeroExtensionFunctor Λ k).obj V) :
    R.Good (tripleOf c o.point) :=
  R.good_of_map (subsingleton_siteOf o hA) (siteMap c o.arrow) _ (tripleOf_map c o.arrow)

include R in
/-- **The tangent space of `F` at `x₀` is finite dimensional**, given a reading of the
deformations of `x₀` in a locally Noetherian formal algebraic space. -/
theorem finiteDimensional_of_pointRead [IsNoetherianRing Λ] [IsOpenImmersion iΛ]
    [Module.Finite Λ k] :
    let D := predeformationCategory iΛ
      (LocallyNoetherianOver.elementsToOver B S hS (contractionFunctor c)) x₀ hx₀
    letI : Category D.carrier := D.category
    ∀ (h : IsPredeformationCategory (BasedCategory.ofFunctor D.projection).p)
      (hS2 : SchlessingerConditionS2 (CategoryOfElements.π
        (isomorphismClasses (BasedCategory.ofFunctor D.projection) h.cofibered))),
      letI : Fact (IsPredeformationCategory (BasedCategory.ofFunctor D.projection).p) := ⟨h⟩
      letI : Fact (SchlessingerConditionS2 (CategoryOfElements.π
        (isomorphismClasses (BasedCategory.ofFunctor D.projection) h.cofibered))) := ⟨hS2⟩
      FiniteDimensional k (artinianTangentSpace Λ k
        (isomorphismClasses (BasedCategory.ofFunctor D.projection) h.cofibered)) := by
  intro D h hS2
  let : Category D.carrier := D.category
  let 𝓕 := BasedCategory.ofFunctor D.projection
  obtain ⟨l, _, _, hfin, _, _, Rr, _, _, _, φ₀, value, hφ₀, halg, hfst, hnat, hinj⟩ :=
    exists_ringChart (siteOf_hom_eq₀ hx₀) R.isLocallyNoetherian (pointOf₀ (hx₀ := hx₀) R)
  have : Module.Finite Λ l := Module.Finite.trans k l
  let F := artinianSquareZeroExtensionFunctor Λ k
  refine finiteDimensional_artinianTangentSpace_of_ringValue (𝓕 := 𝓕) (l := l) (R := Rr)
    (value := fun V x => value V (defTestDatum x.1 x.2) (pointOf R x.1 x.2) (pointOf_j R x.1 x.2))
    h φ₀ hS2 hφ₀ ?_ (fun V x r => halg V _ _ _ r) (fun V x r => hfst V _ _ _ r) ?_
  · intro V V' f x y a ha
    have hf : a.ringHom = eqToHom x.2 ≫ F.map f ≫ eqToHom y.2.symm :=
      IsHomLift.fac' 𝓕.p (F.map f) a
    exact hnat f _ _ (testDatumHom a f x.2 y.2 hf) _ _ _ _ (pointOf_hom R a x.2 y.2)
  · rintro ⟨o, hA⟩ ⟨o', hA'⟩ hxy
    change DeformationObject iΛ (LocallyNoetherianOver.elementsToOver B S hS
      (contractionFunctor c)) x₀ hx₀ at o o'
    change o.algebra = (artinianSquareZeroExtensionFunctor Λ k).obj (FGModuleCat.of k k) at hA
    change o'.algebra = (artinianSquareZeroExtensionFunctor Λ k).obj (FGModuleCat.of k k) at hA'
    let V₀ := FGModuleCat.of k k
    -- transport `x` to the scheme of `y`
    let φ := canonicalMap o o' hA hA'
    have hp' : R.P.obj.map (defTestDatum o' hA').j.op
        (R.P.obj.map φ.m.op (pointOf R o hA)) = pointOf₀ (hx₀ := hx₀) R := by
      show R.P.obj.map (siteMap c o'.arrow).op
        (R.P.obj.map (canonicalSite o o' hA hA').op (pointOf R o hA)) = _
      rw [← types_comp_apply (R.P.obj.map _) (R.P.obj.map _), ← Functor.map_comp, ← op_comp,
        siteMap_canonicalSite]
      exact pointOf_j R o hA
    have h1 := hnat (𝟙 V₀) _ _ φ _ (pointOf_j R o hA) _ hp' rfl
    have h1' : value V₀ (defTestDatum o' hA') (R.P.obj.map φ.m.op (pointOf R o hA)) hp' =
        value V₀ (defTestDatum o hA) (pointOf R o hA) (pointOf_j R o hA) := by
      ext r
      rw [RingHom.congr_fun h1 r]
      show (Algebra.TensorProduct.map (TrivSqZeroExt.map (LinearMap.id : V₀ →ₗ[k] V₀))
        (AlgHom.id k l)) _ = _
      rw [TrivSqZeroExt.map_id, Algebra.TensorProduct.map_id]
      rfl
    have h2 := hinj _ _ _ _ _ _ (h1'.trans hxy)
    -- the triples correspond
    have ht : mapTriple c (canonicalSite o o' hA hA') (tripleOf c o.point) =
        tripleOf c o'.point := by
      refine R.val_inj _ _ (R.good_map _ _ (good_tripleOf R o hA)) (good_tripleOf R o' hA') ?_
      rw [R.val_map]
      exact h2
    -- the morphism of deformations and its invertibility
    let m := deformationMorphismOfEq o o' hA hA' ht
    let ψ : (show 𝓕.obj from o) ⟶ (show 𝓕.obj from o') := m
    have hψ : 𝓕.p.IsHomLift (𝟙 (F.obj V₀)) ψ := by
      apply IsHomLift.of_fac 𝓕.p _ ψ hA hA'
      show 𝟙 (F.obj V₀) = eqToHom _ ≫ eqToHom (hA.trans hA'.symm) ≫ eqToHom _
      have key : ∀ {X Y Z : ArtinianLocalAlgCat.{u, u, u} Λ k} (h₁ : X = Y) (h₂ : Y = Z)
          (h₃ : Z = X), 𝟙 X = eqToHom h₁ ≫ eqToHom h₂ ≫ eqToHom h₃ := by
        intro X Y Z h₁ h₂ h₃
        subst h₁ h₂
        simp
      exact key _ _ _
    have : IsIso (𝓕.p.map ψ) := by
      show IsIso (eqToHom (hA.trans hA'.symm))
      infer_instance
    have : IsIso ψ := Deformation.isIso_of_isIso_map h.cofibered ψ
    apply classOf_eq_of_isIsomorphic
    have : 𝓕.p.IsHomLift (𝟙 (F.obj V₀)) (inv ψ) := by
      simpa using IsHomLift.inv 𝓕.p (𝟙 (F.obj V₀)) ψ
    exact ⟨⟨Functor.Fiber.homMk 𝓕.p _ ψ, Functor.Fiber.homMk 𝓕.p _ (inv ψ),
      Functor.Fiber.hom_ext (IsIso.hom_inv_id ψ), Functor.Fiber.hom_ext (IsIso.inv_hom_id ψ)⟩⟩

end Deformations

/-! ### The two readings -/

section Readings

variable (c)

/-- The set of points of a nonempty scheme is not empty. -/
theorem not_points_eq_empty_of_nonempty {V₀ : BigFppfOver B S hS}
    (hne : Nonempty ((BigFppfOver.toScheme B S hS).obj V₀))
    (h : (Set.univ : Set (Space.points B S hS (yoneda.obj V₀))) = ∅) : False :=
  (Set.univ_eq_empty_iff.1 h).elim' ((Space.pointsEquivScheme B S hS V₀).symm hne.some)

/-- The reading of the deformations of a point with `Z₀ = |V₀|` in `W`. -/
def pointReadW {V₀ : BigFppfOver B S hS} (t₀ : Triple c V₀)
    (hne : Nonempty ((BigFppfOver.toScheme B S hS).obj V₀)) (ht₀ : t₀.Z = Set.univ) :
    PointRead c V₀ t₀ where
  P := c.W
  isLocallyNoetherian := c.isLocallyNoetherian_W
  Good t := t.Z = Set.univ
  val t h := t.xhatValue h
  good_map φ t h := Triple.mapTriple_Z_eq_univ c φ t h
  val_map φ t h := Triple.xhatValue_mapTriple φ t h _
  val_inj t t' h h' e := Triple.ext_of_Z_eq_univ h h' e
  good_of_map hV φ t e := by
    have := hV
    rcases t.Z_eq_empty_or_eq_univ with h | h
    · exfalso
      have h2 : t₀.Z = ∅ := e ▸ Triple.mapTriple_Z_eq_empty c φ t h
      rw [ht₀] at h2
      exact not_points_eq_empty_of_nonempty hne h2
    · exact h

/-- The reading of a triple with `Z = ∅` as a point of the completion `X'_{/|X'|}`. -/
def uPoint {V : BigFppfOver B S hS} (t : Triple c V) (h : t.Z = ∅) :
    (Space.completionSheaf B S hS c.X' Set.univ).obj.obj (op V) :=
  ((BigFppfOver.topology B S hS).toSheafify
    (Space.completionSubfunctor B S hS c.X' Set.univ).toFunctor).app (op V)
      ⟨ULift.up (t.uValue h), fun _ => Set.mem_univ _⟩

/-- The reading of triples with `Z = ∅` in `X'_{/|X'|}` is injective. -/
theorem uPoint_injective {V : BigFppfOver B S hS} {t t' : Triple c V} (h : t.Z = ∅)
    (h' : t'.Z = ∅) (e : uPoint c t h = uPoint c t' h') : t = t' := by
  let J := BigFppfOver.topology B S hS
  let G := (Space.completionSubfunctor B S hS c.X' Set.univ)
  have hsheaf : Presheaf.IsSheaf J (c.X' ⋙ uliftFunctor.{u + 1}) :=
    (isSheaf_iff_isSheaf_of_type _ _).mpr (Presieve.isSheaf_comp_uliftFunctor _
      ((isSheaf_iff_isSheaf_of_type _ _).mp c.isAlgebraicSpace_X'.isSheaf))
  have := GrothendieckTopology.isIso_toSheafify J hsheaf
  have hnat := GrothendieckTopology.toSheafify_naturality J G.ι
  let e₁ : G.toFunctor.obj (op V) := ⟨ULift.up (t.uValue h), fun _ => Set.mem_univ _⟩
  let e₂ : G.toFunctor.obj (op V) := ⟨ULift.up (t'.uValue h'), fun _ => Set.mem_univ _⟩
  have key : ∀ e : G.toFunctor.obj (op V),
      (J.toSheafify (c.X' ⋙ uliftFunctor.{u + 1})).app (op V) (G.ι.app (op V) e) =
        (J.sheafifyMap G.ι).app (op V) ((J.toSheafify G.toFunctor).app (op V) e) :=
    fun e => congrArg (fun η => η.app (op V) e) hnat
  have e₀ : (J.toSheafify G.toFunctor).app (op V) e₁ = (J.toSheafify G.toFunctor).app (op V) e₂ :=
    e
  have e' : (J.toSheafify (c.X' ⋙ uliftFunctor.{u + 1})).app (op V) (G.ι.app (op V) e₁) =
      (J.toSheafify (c.X' ⋙ uliftFunctor.{u + 1})).app (op V) (G.ι.app (op V) e₂) := by
    rw [key, key, e₀]
  have e'' := (mono_iff_injective ((J.toSheafify (c.X' ⋙ uliftFunctor.{u + 1})).app (op V))).mp
    inferInstance e'
  exact Triple.ext_of_Z_eq_empty h h' (congrArg ULift.down e'')

/-- The reading of triples with `Z = ∅` in `X'_{/|X'|}` is compatible with restriction. -/
theorem uPoint_mapTriple {V₂ V₁ : BigFppfOver B S hS} (φ : V₂ ⟶ V₁) (t : Triple c V₁)
    (h : t.Z = ∅) :
    uPoint c (mapTriple c φ t) (Triple.mapTriple_Z_eq_empty c φ t h) =
      (Space.completionSheaf B S hS c.X' Set.univ).obj.map φ.op (uPoint c t h) := by
  let J := BigFppfOver.topology B S hS
  let G := (Space.completionSubfunctor B S hS c.X' Set.univ)
  let e₁ : G.toFunctor.obj (op V₁) := ⟨ULift.up (t.uValue h), fun _ => Set.mem_univ _⟩
  let e₂ : G.toFunctor.obj (op V₂) := ⟨ULift.up ((mapTriple c φ t).uValue
    (Triple.mapTriple_Z_eq_empty c φ t h)), fun _ => Set.mem_univ _⟩
  have he : e₂ = G.toFunctor.map φ.op e₁ :=
    Subtype.ext (ULift.ext _ _ (Triple.uValue_mapTriple φ t h
      (Triple.mapTriple_Z_eq_empty c φ t h)))
  show (J.toSheafify G.toFunctor).app (op V₂) e₂ =
    (J.sheafify G.toFunctor).map φ.op ((J.toSheafify G.toFunctor).app (op V₁) e₁)
  rw [he]
  exact NatTrans.naturality_apply (J.toSheafify G.toFunctor) φ.op e₁

/-- The reading of the deformations of a point with `Z₀ = ∅` in the completion `X'_{/|X'|}`. -/
def pointReadX' {V₀ : BigFppfOver B S hS} (t₀ : Triple c V₀)
    (hne : Nonempty ((BigFppfOver.toScheme B S hS).obj V₀)) (ht₀ : t₀.Z = ∅) :
    PointRead c V₀ t₀ where
  P := Space.completionSheaf B S hS c.X' Set.univ
  isLocallyNoetherian :=
    letI := Space.pointTopology B S hS c.X'
    FormalSpace.isLocallyNoetherian_completionSheaf_of_isLocallyNoetherian c.isAlgebraicSpace_X'
      (isLocallyNoetherian_of_isLocallyOfFiniteType_base c c.isLocallyOfFiniteType_X')
      Set.univ isClosed_univ
  Good t := t.Z = ∅
  val t h := uPoint c t h
  good_map φ t h := Triple.mapTriple_Z_eq_empty c φ t h
  val_map φ t h := uPoint_mapTriple c φ t h
  val_inj t t' h h' e := uPoint_injective c h h' e
  good_of_map hV φ t e := by
    have := hV
    rcases t.Z_eq_empty_or_eq_univ with h | h
    · exact h
    · exfalso
      have h2 : t₀.Z = Set.univ := e ▸ Triple.mapTriple_Z_eq_univ c φ t h
      rw [ht₀] at h2
      exact not_points_eq_empty_of_nonempty hne h2.symm

end Readings

/-! ### Stacks 0GI7 -/

variable (c)

/-- **The tangent spaces of Artin's contraction functor are finite dimensional**, in the form
of Artin's axiom `[3]`: for every field `k` of finite type over `S`, every affine open
`Spec Λ ⊆ S` through which `Spec k ⟶ S` factors with `Λ → k` finite, and every
`x₀ ∈ F(Spec k)`, the tangent space of the predeformation category `𝓕_{F,k,x₀}` is a finite
dimensional `k`-vector space, for every vector-space structure of Stacks 06IH it carries. That
such a structure exists, `𝓕_{F,k,x₀}` being a deformation category, is
`AlgebraicGeometry.Artin.ContractionSituation.isDeformationCategory_predeformationCategory`; the
two together are Stacks 0GI7,
`AlgebraicGeometry.Artin.ContractionSituation.finiteDimensional_artinianTangentSpace`. -/
theorem hasFiniteDimensionalTangentSpaces :
    LocallyNoetherianOver.HasFiniteDimensionalTangentSpaces B S hS (contractionFunctor c) := by
  intro Λ k _ _ _ _ iΛ hiΛ x₀ hx₀
  have := c.isLocallyNoetherian_base
  have : _root_.AlgebraicGeometry.IsLocallyNoetherian (Spec (.of Λ)) :=
    isLocallyNoetherian_of_isOpenImmersion iΛ
  have : IsNoetherianRing Λ := (isLocallyNoetherian_Spec (R := CommRingCat.of Λ)).mp inferInstance
  have hsub : Subsingleton ((BigFppfOver.toScheme B S hS).obj (siteOf c x₀)) := by
    rw [siteOf_eq₀ hx₀]; infer_instance
  have hne : Nonempty ((BigFppfOver.toScheme B S hS).obj (siteOf c x₀)) := by
    rw [siteOf_eq₀ hx₀]; infer_instance
  rcases (tripleOf c x₀).Z_eq_empty_or_eq_univ with h | h
  · exact finiteDimensional_of_pointRead (hx₀ := hx₀) (pointReadX' c _ hne h)
  · exact finiteDimensional_of_pointRead (hx₀ := hx₀) (pointReadW c _ hne h)

end AlgebraicGeometry.Artin.ContractionSituation

end
