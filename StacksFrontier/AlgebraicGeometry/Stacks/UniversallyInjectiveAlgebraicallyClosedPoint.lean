module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.LinearDisjoint
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalOnSourceAndTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalityFiniteness
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteria
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteriaProductsToDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteriaSchemePoints
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.MorphismSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.Points
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsInjective
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedClosedSubstackExistence
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedUniquePointStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbe
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRepresented
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductUniversalProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyInjective
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyInjectiveBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyInjectiveDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyInjectiveGeometricTwoArrows
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.BaseFieldUniqueness
public import StacksFrontier.CategoryTheory.Sites.Gerbe.Equivalence
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Fibres
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap
public import StacksFrontier.CategoryTheory.TwoYoneda.Basic
public import StacksFrontier.RingTheory.GeometricallyIntegral.TFAE

/-!
# Lifting a geometric point along a universally injective 1-morphism (Stacks 0DTM)

Let `f : 𝒳 ⟶ 𝒴` be a universally injective 1-morphism of algebraic stacks over `S` and let
`y : Spec k ⟶ 𝒴` be a morphism with `k` algebraically closed, i.e. a field-valued point of `𝒴`
(**Stacks 04XG**) whose field is algebraically closed. If the point of `|𝒴|` it represents lies in
the image of `|𝒳| → |𝒴|`, then `y` factors through `f`: there is a morphism `x : Spec k ⟶ 𝒳`, over
the *same* field `k`, with `y = f ∘ x`.

## Main results

* `AlgebraicGeometry.Stack.exists_fiber_lift_of_universallyInjective`: a field-valued point of
  `𝒴` over an algebraically closed field whose point lies in the image of `|𝒳| → |𝒴|` factors
  through `f` over the same field.

## Implementation notes

A morphism `Spec k ⟶ 𝒳` is recorded, as the 2-Yoneda lemma licenses, by an object of the fibre of
`𝒳` over the site object whose underlying scheme is `Spec k` — this is what an
`AlgebraicGeometry.Stack.FieldValuedPoint` is. Accordingly the equation `y = f ∘ x` is the
assertion that the image of `x` under `f` is isomorphic to `y` *in the fibre over that object*,
i.e. by a vertical isomorphism; that isomorphism is the 2-morphism filling the triangle. The
hypothesis that `y` is in the image of `|𝒳| → |𝒴|` is membership of its point class in the range of
`AlgebraicGeometry.Stack.pointsMap`.

## References

* [Stacks Project, Tag 04MK](https://stacks.math.columbia.edu/tag/04MK)
* [Stacks Project, Tag 04XG](https://stacks.math.columbia.edu/tag/04XG)
* [Stacks Project, Tag 04XH](https://stacks.math.columbia.edu/tag/04XH)
* [Stacks Project, Tag 0509](https://stacks.math.columbia.edu/tag/0509)
* [Stacks Project, Tag 06MN](https://stacks.math.columbia.edu/tag/06MN)
* [Stacks Project, Tag 0CI2](https://stacks.math.columbia.edu/tag/0CI2)
* [Stacks Project, Tag 0CPN](https://stacks.math.columbia.edu/tag/0CPN)
* [Stacks Project, Tag 0DTM](https://stacks.math.columbia.edu/tag/0DTM)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Bicategory Opposite TopologicalSpace

namespace AlgebraicGeometry.Stack

universe u w vC

open scoped TensorProduct

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

private lemma algebraicClosure_residueField_in_site
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T : AlgebraicGeometry.BigFppfOver B S hS)
    (z : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T) :
    B.Contains (Spec (.of
      (AlgebraicClosure
        (((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T).residueField z)))) := by
  let X := (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T
  let K := X.residueField z
  have hX : X.size < B.cutoff := T.left.property
  have hK : Cardinal.mk K ≤ X.size := by
    have hs : (Spec (X.residueField z)).size ≤ X.size :=
      Scheme.size_le_of_mono_quasiCompact (X.fromSpecResidueField z)
    rw [Scheme.size_Spec] at hs
    exact (le_max_right _ _).trans hs
  have hL : Cardinal.mk (AlgebraicClosure K) ≤ X.size := by
    calc
      Cardinal.mk (AlgebraicClosure K) ≤ max (Cardinal.mk K) Cardinal.aleph0 :=
        Algebra.IsAlgebraic.cardinalMk_le_max _ _
      _ = max Cardinal.aleph0 (Cardinal.mk K) := max_comm _ _
      _ ≤ X.size := max_le (Scheme.aleph0_le_size X) hK
  show (Spec (.of (AlgebraicClosure K))).size < B.cutoff
  rw [Scheme.size_Spec]
  exact (max_le (Scheme.aleph0_le_size X) hL).trans_lt hX

private lemma tensorProduct_spec_in_site
    (B : AlgebraicGeometry.BigFppfSite.{u}) {R A : Type u}
    [CommRing R] [CommRing A] [Algebra R A]
    (hA : B.Contains (Spec (.of A))) :
    B.Contains (Spec (.of (A ⊗[R] A))) := by
  have hAcard : Cardinal.mk A < B.cutoff :=
    lt_of_le_of_lt (le_max_right _ _) (by simpa [Scheme.size_Spec] using hA)
  have hbound :
      max Cardinal.aleph0 (max (Cardinal.mk A) (Cardinal.mk A)) < B.cutoff :=
    max_lt B.aleph0_lt_cutoff (max_lt hAcard hAcard)
  show (Spec (.of (A ⊗[R] A))).size < B.cutoff
  rw [Scheme.size_Spec]
  exact max_lt B.aleph0_lt_cutoff (Cardinal.mk_tensorProduct_le.trans_lt hbound)

private lemma isDomain_tensorProduct_of_isAlgClosed
    (k A : Type u) [Field k] [IsAlgClosed k] [CommRing A] [IsDomain A]
    [Algebra k A] (K : Type u) [Field K] [Algebra k K] :
    IsDomain (A ⊗[k] K) := by
  let e : k ≃ₐ[k] AlgebraicClosure k :=
    AlgEquiv.ofBijective (Algebra.ofId k (AlgebraicClosure k))
      IsAlgClosed.algebraMap_bijective_of_isIntegral
  have h : IsDomain (A ⊗[k] AlgebraicClosure k) := by
    let f : A ⊗[k] AlgebraicClosure k ≃ₐ[k] A :=
      (Algebra.TensorProduct.congr (AlgEquiv.refl) e.symm).trans
        (Algebra.TensorProduct.rid k k A)
    exact Function.Injective.isDomain f.toRingHom f.injective
  have hall : ∀ (K : Type u) [Field K] [Algebra k K], IsDomain (A ⊗[k] K) :=
    ((Algebra.isGeometricallyIntegral_tfae k A).out 4 2).mp h
  exact hall K

private lemma algebraMap_surjective_of_integralClosure_eq
    (k K : Type*) [Field k] [Field K] [Algebra k K] [IsAlgClosed k]
    [IsDomain (K ⊗[k] K)]
    {A : Type*} [CommRing A]
    (φ : K ⊗[k] K →+* A) (hφ : Function.Injective φ)
    (h : ∀ a : A, (φ.comp Algebra.TensorProduct.includeRight.toRingHom).IsIntegralElem a →
      (φ.comp Algebra.TensorProduct.includeLeftRingHom).IsIntegralElem a) :
    Function.Surjective (algebraMap k K) := by
  let : Algebra K A := (φ.comp Algebra.TensorProduct.includeLeftRingHom).toAlgebra
  let ψ : K ⊗[k] K →ₐ[K] A :=
    { φ with commutes' := fun _ => rfl }
  have hi (b : K) : _root_.IsIntegral K (ψ (1 ⊗ₜ[k] b)) := by
    show (φ.comp Algebra.TensorProduct.includeLeftRingHom).IsIntegralElem _
    exact h _ (φ.comp Algebra.TensorProduct.includeRight.toRingHom).isIntegralElem_map
  have ht (z : K ⊗[k] K) : _root_.IsIntegral K (ψ z) := by
    induction z using TensorProduct.induction_on with
    | zero => simpa using isIntegral_zero (R := K) (B := A)
    | tmul a b =>
      have hh : ψ (a ⊗ₜ[k] b) = algebraMap K A a * ψ (1 ⊗ₜ[k] b) := by
        rw [← ψ.commutes, ← map_mul]
        congr 1
        simp
      rw [hh]
      exact (isIntegral_algebraMap).mul (hi b)
    | add a b ha hb => simpa using ha.add hb
  have : Algebra.IsIntegral K (K ⊗[k] K) :=
    ⟨fun z => (_root_.isIntegral_algHom_iff ψ hφ).mp (ht z)⟩
  have hfield : IsField (K ⊗[k] K) := isField_of_isIntegral_of_isField' (R := K) (Field.toIsField K)
  have : Algebra.IsAlgebraic k K :=
    (Algebra.TensorProduct.isAlgebraic_of_isField k K K hfield).elim id id
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral.2

/-- **Stacks 04MK, read on integral elements.** On a reduced connected scheme locally of finite
type over one field `K` through two different structure morphisms, a global section integral over
the first copy of `K` is integral over the second: the two integral closures in global sections
agree. -/
private lemma isIntegralElem_of_isIntegralElem_baseField (K : Type u) [Field K] (X : Scheme.{u})
    (a b : X ⟶ Spec (.of K)) [LocallyOfFiniteType a] [LocallyOfFiniteType b]
    [AlgebraicGeometry.IsReduced X] [ConnectedSpace X] (s : Γ(X, ⊤))
    (hs : ((Scheme.ΓSpecIso (.of K)).inv ≫ a.appTop).hom.IsIntegralElem s) :
    ((Scheme.ΓSpecIso (.of K)).inv ≫ b.appTop).hom.IsIntegralElem s := by
  have h := AlgebraicGeometry.integralClosure_baseField_toSubring_eq K K X a b
  exact (SetLike.ext_iff.mp h s).1 hs

private lemma algebraMap_surjective_of_dominant_to_tensorProduct
    (k K : Type u) [Field k] [Field K] [Algebra k K] [IsAlgClosed k]
    [IsDomain (K ⊗[k] K)] (U : Scheme.{u}) [IsReduced U] [ConnectedSpace U]
    (f : U ⟶ Spec (.of (K ⊗[k] K))) [IsDominant f] [QuasiCompact f]
    [LocallyOfFiniteType
      (f ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom))]
    [LocallyOfFiniteType
      (f ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom))] :
    Function.Surjective (algebraMap k K) := by
  let : IsSchemeTheoreticallyDominant f := .of_isDominant f
  let φ := ((Scheme.ΓSpecIso (.of (K ⊗[k] K))).inv ≫ f.appTop).hom
  have hφ : Function.Injective φ :=
    (f.app_injective ⊤).comp
      ((ConcreteCategory.bijective_of_isIso ((Scheme.ΓSpecIso (.of (K ⊗[k] K))).inv)).1)
  apply algebraMap_surjective_of_integralClosure_eq k K φ hφ
  have hn (α : K →+* K ⊗[k] K) :
      ((Scheme.ΓSpecIso (.of K)).inv ≫
        (f ≫ Spec.map (CommRingCat.ofHom α)).appTop).hom = φ.comp α := by
    rw [Scheme.Hom.comp_appTop, ← Category.assoc,
      ← Scheme.ΓSpecIso_inv_naturality]
    rfl
  intro s hs
  rw [← hn Algebra.TensorProduct.includeLeftRingHom]
  rw [← hn Algebra.TensorProduct.includeRight.toRingHom] at hs
  exact isIntegralElem_of_isIntegralElem_baseField K U
    (f ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom))
    (f ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom)) s hs

private lemma exists_fiber_lift_of_split_base
    {C X Y : Type*} [Category C] [Category X] [Category Y]
    (pX : X ⥤ C) (pY : Y ⥤ C) (F : X ⥤ Y) (hw : F ⋙ pY = pX)
    (hX : pX.IsFiberedInGroupoids) (hY : pY.IsFiberedInGroupoids)
    {U V : C} (b : V ⟶ U) (s : U ⟶ V) (hs : s ≫ b = 𝟙 U)
    (x : X) (hx : pX.obj x = V) (y : pY.Fiber U)
    (e : F.obj x ⟶ y.1) (he : pY.IsHomLift b e) :
    ∃ z : pX.Fiber U, Nonempty ((Functor.fiberMap pX pY F hw U).obj z ≅ y) := by
  obtain ⟨z, l, hl⟩ := hX.exists_lift s x hx
  let z' : pX.Fiber U := ⟨z, IsHomLift.domain_eq pX s l⟩
  have hlF : pY.IsHomLift s (F.map l) := by
    have hl' : (F ⋙ pY).IsHomLift s l := by rwa [hw]
    exact IsHomLift.of_fac' pY s (F.map l)
      (IsHomLift.domain_eq (F ⋙ pY) s l)
      (IsHomLift.codomain_eq (F ⋙ pY) s l)
      (IsHomLift.fac' (F ⋙ pY) s l)
  have hcomp : pY.IsHomLift (𝟙 U) (F.map l ≫ e) := by
    rw [← hs]
    exact IsHomLift.comp pY s b (F.map l) e
  have := hY.fiber_isGroupoid U
  let α : (Functor.fiberMap pX pY F hw U).obj z' ⟶ y := ⟨F.map l ≫ e, hcomp⟩
  exact ⟨z', ⟨asIso α⟩⟩

private lemma isIso_of_surjective_spec_preimage
    {k K : Type u} [Field k] [Field K] (f : Spec (.of K) ⟶ Spec (.of k))
    (hf : Function.Surjective (Spec.preimage f).hom) : IsIso f := by
  let φ := Spec.preimage f
  let e := RingEquiv.ofBijective φ.hom ⟨φ.hom.injective, hf⟩
  have hφ : IsIso φ := e.toCommRingCatIso.isIso_hom
  have h : IsIso (Spec.map φ) := inferInstance
  simpa only [φ, Spec.map_preimage] using h

private lemma overFunctor_obj_hom
    {C : Type*} [Category C] {T U : C}
    (F : Over T ⥤ Over U) (hF : F ⋙ Over.forget U = Over.forget T)
    (A : Over T) :
    eqToHom (Functor.congr_obj hF A).symm ≫ (F.obj A).hom =
      A.hom ≫ eqToHom (Functor.congr_obj hF (Over.mk (𝟙 T))).symm ≫
        (F.obj (Over.mk (𝟙 T))).hom := by
  let l : A ⟶ Over.mk (𝟙 T) := Over.homMk A.hom (by simp)
  have hw := (F.map l).w
  have hm := Functor.congr_hom hF l
  dsimp at hm
  rw [hm] at hw
  simpa [l] using (congrArg (fun e => eqToHom (Functor.congr_obj hF A).symm ≫ e) hw).symm

private lemma overFunctor_verticalIso_of_equal_comp
    {C : Type*} [Category C] {T U W : C}
    (F : Over T ⥤ Over U) (hF : F ⋙ Over.forget U = Over.forget T)
    (t : T ⟶ U)
    (ht : ∀ A : Over T,
      eqToHom (Functor.congr_obj hF A).symm ≫ (F.obj A).hom = A.hom ≫ t)
    (a b : W ⟶ T) (h : a ≫ t = b ≫ t) :
    ∃ β : F.obj (Over.mk a) ≅ F.obj (Over.mk b),
      (Over.forget U).IsHomLift (𝟙 W) β.hom := by
  let A := F.obj (Over.mk a)
  let B := F.obj (Over.mk b)
  have ha : A.left = W := Functor.congr_obj hF (Over.mk a)
  have hb : B.left = W := Functor.congr_obj hF (Over.mk b)
  let e : A.left ≅ B.left := (eqToIso ha).trans (eqToIso hb).symm
  have hw : e.hom ≫ B.hom = A.hom := by
    have hc : eqToHom ha.symm ≫ A.hom = eqToHom hb.symm ≫ B.hom :=
      (ht (Over.mk a)).trans (h.trans (ht (Over.mk b)).symm)
    have hc' := congrArg (fun z => eqToHom ha ≫ z) hc
    simpa [e, Category.assoc] using hc'.symm
  let β : A ≅ B := Over.isoMk e hw
  refine ⟨β, ?_⟩
  apply IsHomLift.of_fac (Over.forget U) (𝟙 W) β.hom ha hb
  simp [β, e]

private lemma exists_reduced_connected_affine_through_point
    (V : Scheme.{u}) (v : V) :
    ∃ (U : Scheme.{u}) (i : U ⟶ V),
      IsReduced U ∧ ConnectedSpace U ∧ IsAffine U ∧
      LocallyOfFiniteType i ∧ v ∈ Set.range i := by
  obtain ⟨n, a, ha⟩ := V.affineCover.exists_eq v
  let A := V.affineCover.X n
  let j : A ⟶ V := V.affineCover.f n
  let I : A.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal (.closure {a})
  have hI : (I.support : Set A) = closure {a} :=
    Scheme.IdealSheafData.coe_support_vanishingIdeal _
  have : IrreducibleSpace I.subscheme := by
    show IrreducibleSpace (I.support : Set A)
    apply Subtype.irreducibleSpace
    rw [hI]
    exact (isIrreducible_singleton (x := a)).closure
  have : IsReduced I.subscheme :=
    Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  have : IsAffine I.subscheme := isAffine_of_isAffineHom I.subschemeι
  refine ⟨I.subscheme, I.subschemeι ≫ j, inferInstance, inferInstance,
    inferInstance, inferInstance, ?_⟩
  have haI : a ∈ (I.support : Set A) := by rw [hI]; exact subset_closure (Set.mem_singleton a)
  exact ⟨⟨a, haI⟩, ha⟩

private lemma exists_reduced_connected_dominant_of_generic_point
    (V Y : Scheme.{u}) [QuasiSeparatedSpace Y] (a : V ⟶ Y)
    (v : V) (hv : IsGenericPoint (a v) Set.univ) :
    ∃ (U : Scheme.{u}) (i : U ⟶ V),
      IsReduced U ∧ ConnectedSpace U ∧ LocallyOfFiniteType i ∧
      IsDominant (i ≫ a) ∧ QuasiCompact (i ≫ a) := by
  obtain ⟨U, i, hred, hconn, haff, hlft, z, hz⟩ :=
    exists_reduced_connected_affine_through_point V v
  have hd : IsDominant (i ≫ a) := by
    constructor
    intro y
    have hin : {a v} ⊆ Set.range (i ≫ a) := by
      rintro _ rfl
      exact ⟨z, by simpa using congrArg a hz⟩
    have hgen : closure {a v} = Set.univ := hv
    exact closure_mono hin (hgen.symm ▸ Set.mem_univ y)
  exact ⟨U, i, hred, hconn, hlft, hd, inferInstance⟩

private lemma algebraMap_surjective_of_generic_point_lift
    (k K : Type u) [Field k] [Field K] [Algebra k K] [IsAlgClosed k]
    [IsDomain (K ⊗[k] K)] (V : Scheme.{u})
    (a : V ⟶ Spec (.of (K ⊗[k] K)))
    [LocallyOfFiniteType
      (a ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom))]
    [LocallyOfFiniteType
      (a ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom))]
    (v : V) (hv : IsGenericPoint (a v) Set.univ) :
    Function.Surjective (algebraMap k K) := by
  obtain ⟨U, i, hred, hconn, hlft, hdom, hqc⟩ :=
    exists_reduced_connected_dominant_of_generic_point V _ a v hv
  have hleft : LocallyOfFiniteType
      ((i ≫ a) ≫ Spec.map
        (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom)) := by
    rw [Category.assoc]
    infer_instance
  have hright : LocallyOfFiniteType
      ((i ≫ a) ≫ Spec.map
        (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom)) := by
    rw [Category.assoc]
    infer_instance
  exact algebraMap_surjective_of_dominant_to_tensorProduct k K U (i ≫ a)

section


private abbrev schemePresheafTotalCategory {C : Type u} [Category.{vC} C]
    (X : C) :=
  (presheafOfCategories (yoneda.obj X ⋙ typeToCat)).obj

private theorem schemePresheafHom_ext {C : Type u} [Category.{vC} C] (X : C)
    {A B : schemePresheafTotalCategory X} (f g : A ⟶ B)
    (h : f.base = g.base) : f = g := by
  cases A with
  | mk abase afiber =>
    cases B with
    | mk bbase bfiber =>
      change Discrete (abase ⟶ X) at afiber
      change Discrete (bbase ⟶ X) at bfiber
      change Pseudofunctor.CoGrothendieck.Hom _ _ at f g
      cases f with
      | mk fb ff =>
        cases g with
        | mk gb gf =>
          dsimp at h
          cases h
          congr 1
          dsimp [schemePresheafTotalCategory, presheafOfCategories,
            Functor.toPseudofunctor', pseudofunctorOfIsLocallyDiscrete, typeToCat]
          change afiber ⟶ Discrete.mk (fb ≫ bfiber.as) at ff
          change afiber ⟶ Discrete.mk (fb ≫ bfiber.as) at gf
          exact (show Subsingleton (afiber ⟶ Discrete.mk (fb ≫ bfiber.as)) from
            inferInstance).elim ff gf

private noncomputable def overToSchemePresheaf
    {C : Type u} [Category.{vC} C] (X : C) :
    Over X ⥤ schemePresheafTotalCategory X where
  obj A := ⟨A.left, Discrete.mk A.hom⟩
  map {A B} f := ⟨f.left, Discrete.eqToHom (by
    change A.hom = ((yoneda.obj X).map f.left.op) B.hom
    rw [show ((yoneda.obj X).map f.left.op) B.hom = f.left ≫ B.hom from rfl]
    exact f.w.symm)⟩
  map_id := by
    intro A
    apply schemePresheafHom_ext
    change Over.Hom.left (𝟙 A) = 𝟙 A.left
    simp
  map_comp := by
    intro A B D f g
    apply schemePresheafHom_ext
    change Over.Hom.left (f ≫ g) = Over.Hom.left f ≫ Over.Hom.left g
    simp

private noncomputable def schemePresheafToOver
    {C : Type u} [Category.{vC} C] (X : C) :
    schemePresheafTotalCategory X ⥤ Over X where
  obj A := Over.mk A.fiber.as
  map {A B} f := Over.homMk f.base (by
    have hf := Discrete.eq_of_hom f.fiber
    change A.fiber.as = ((yoneda.obj X).map f.base.op) B.fiber.as at hf
    rw [show ((yoneda.obj X).map f.base.op) B.fiber.as = f.base ≫ B.fiber.as from rfl] at hf
    exact hf.symm)
  map_id := by
    intro A
    apply Over.OverMorphism.ext
    rfl
  map_comp := by
    intro A B D f g
    apply Over.OverMorphism.ext
    rfl

private noncomputable def schemePresheafEquivalence
    {C : Type u} [Category.{vC} C] (X : C) :
    Over X ≌ schemePresheafTotalCategory X where
  functor := overToSchemePresheaf X
  inverse := schemePresheafToOver X
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro A B f
    apply Over.OverMorphism.ext
    simp [Functor.comp_map, overToSchemePresheaf, schemePresheafToOver])
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro A B f
    apply schemePresheafHom_ext
    change f.base ≫ 𝟙 B.base = 𝟙 A.base ≫ f.base
    simp)
  functor_unitIso_comp := by
    intro A
    apply schemePresheafHom_ext
    change 𝟙 A.left ≫ 𝟙 A.left = 𝟙 A.left
    simp

private noncomputable def schemePresheafEquivalenceOver
    {C : Type u} [Category.{vC} C] (X : C) :
    StacksRepresentableCFG.EquivalenceOver (Over.forget X)
      (presheafOfCategories (yoneda.obj X ⋙ typeToCat)).p := by
  let e := schemePresheafEquivalence X
  refine ⟨⟨e.functor, rfl⟩, ⟨e.inverse, rfl⟩, e.unitIso, e.counitIso, ?_, ?_⟩
  · ext a; rfl
  · ext a; rfl

/-- **Cancelling the comparison isomorphisms of a vertical arrow in an `Over` category.** If
`X₂` is the object `Over.mk v` of `Over T` and a vertical arrow `X₁ ⟶ X₂` over `W` identifies the
structure morphisms, then `v` is the structure morphism of `X₁` read through the identification of
its source with `W`. -/
private lemma eqToHom_comp_hom_eq_of_mk {C : Type*} [Category C] {W T : C}
    {X₁ X₂ : Over T} {v : W ⟶ T} (hX₂ : X₂ = Over.mk v)
    {E : W = X₁.left} {q₁ : X₁.left = W} {q₂ : W = X₂.left}
    (h : (eqToHom q₁ ≫ 𝟙 W ≫ eqToHom q₂) ≫ X₂.hom = X₁.hom) :
    v = eqToHom E ≫ X₁.hom := by
  have hv : eqToHom q₂ ≫ X₂.hom = v := by
    subst hX₂
    simp
  have h' : eqToHom q₁ ≫ v = X₁.hom := by
    rw [← h, ← hv]
    simp
  rw [← h', ← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]

private lemma morphismSpaceEquiv_to_scheme_apply
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (AlgebraicGeometry.BigFppfOver B S hS))
    (T : AlgebraicGeometry.BigFppfOver B S hS)
    (F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eF : StacksRepresentableCFG.EquivalenceOver 𝒳.val.p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (H : 𝒳.val.obj ⥤ Over T) (hH : H ⋙ Over.forget T = 𝒳.val.p)
    (W : AlgebraicGeometry.BigFppfOver B S hS) (a : F.obj (op W)) :
    (AlgebraicGeometry.Stack.morphismSpaceEquiv B S hS 𝒳
      (AlgebraicGeometry.Stack.schemeFibredCategory B S hS T)
      F (yoneda.obj T) eF (schemePresheafEquivalenceOver T)
      (Quotient.mk _ ⟨H, hH⟩)).app (op W) a =
      eqToHom ((Functor.congr_obj hH _).trans (Functor.congr_obj eF.inv.w _)).symm ≫
        (H.obj (eF.inv.functor.obj ⟨W, Discrete.mk a⟩)).hom := by
  let 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1}
      (AlgebraicGeometry.BigFppfOver B S hS) :=
    AlgebraicGeometry.Stack.schemeFibredCategory B S hS T
  let : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.isFiberedInGroupoids.isFibered
  have hh := AlgebraicGeometry.Stack.morphismSpaceEquiv_map B S hS 𝒳 𝒴 F (yoneda.obj T)
    eF (schemePresheafEquivalenceOver T) ⟨H, hH⟩ W a
  rw [Functor.isoClassMap_app_isoClassMk] at hh
  obtain ⟨α⟩ := Functor.exists_iso_of_isoClassMk_eq hh
  have ha := α.hom.1.w
  have hα : (Over.forget T).IsHomLift (𝟙 W) α.hom.1 := α.hom.2
  have hb := IsHomLift.fac' (Over.forget T) (𝟙 W) α.hom.1
  dsimp at ha hb
  rw [hb] at ha
  exact eqToHom_comp_hom_eq_of_mk rfl ha

private lemma overFunctor_comp_eq_of_vertical
    {C : Type*} [Category C] {T U W : C}
    (F : Over T ⥤ Over U) (hF : F ⋙ Over.forget U = Over.forget T)
    (A B : Over T) (ha : A.left = W) (hb : B.left = W)
    (α : F.obj A ⟶ F.obj B) (hα : (Over.forget U).IsHomLift (𝟙 W) α) :
    (eqToHom ha.symm ≫ A.hom) ≫
        (eqToHom (Functor.congr_obj hF (Over.mk (𝟙 T))).symm ≫
          (F.obj (Over.mk (𝟙 T))).hom) =
      (eqToHom hb.symm ≫ B.hom) ≫
        (eqToHom (Functor.congr_obj hF (Over.mk (𝟙 T))).symm ≫
          (F.obj (Over.mk (𝟙 T))).hom) := by
  rw [Category.assoc, ← overFunctor_obj_hom F hF A,
    Category.assoc, ← overFunctor_obj_hom F hF B]
  have hw := α.w
  have hh := IsHomLift.fac' (Over.forget U) (𝟙 W) α
  dsimp at hh
  rw [hh] at hw
  have hhA : (F.obj A).left = W := (Functor.congr_obj hF A).trans ha
  simpa using (congrArg (fun z => eqToHom hhA.symm ≫ z) hw).symm

private def swapFibreProduct
    {C X Y Z : Type*} [Category C] [Category X] [Category Y] [Category Z]
    (pX : X ⥤ C) (pY : Y ⥤ C) (pZ : Z ⥤ C) (F : X ⥤ Z) (G : Y ⥤ Z) :
    TwoFibreProductOver pX pY pZ F G ⥤ TwoFibreProductOver pY pX pZ G F where
  obj P :=
    { base := P.base
      x := P.y
      y := P.x
      hx := P.hy
      hy := P.hx
      iso := P.iso.symm
      vertical := TwoFibreProductOver.psiIso_inv_vertical P }
  map {P Q} f :=
    { hbase := f.hbase
      a := f.b
      b := f.a
      ha := f.hb
      hb := f.ha
      w := by
        change G.map f.b ≫ Q.iso.inv = P.iso.inv ≫ F.map f.a
        simpa [Category.assoc] using
          congrArg (fun z => P.iso.inv ≫ z ≫ Q.iso.inv) f.w.symm }
  map_id P := by apply TwoFibreProductOver.Hom.ext <;> rfl
  map_comp f g := by apply TwoFibreProductOver.Hom.ext <;> rfl

private def swapFibreProductEquivalenceOver
    {C X Y Z : Type*} [Category C] [Category X] [Category Y] [Category Z]
    (pX : X ⥤ C) (pY : Y ⥤ C) (pZ : Z ⥤ C) (F : X ⥤ Z) (G : Y ⥤ Z) :
    StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.structureFunctor pX pY pZ F G)
      (TwoFibreProductOver.structureFunctor pY pX pZ G F) where
  hom := ⟨swapFibreProduct pX pY pZ F G, rfl⟩
  inv := ⟨swapFibreProduct pY pX pZ G F, rfl⟩
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro P Q f
    change f ≫ 𝟙 Q = 𝟙 P ≫ f
    simp)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro P Q f
    change f ≫ 𝟙 Q = 𝟙 P ≫ f
    simp)
  unit_over := by ext P; rfl
  counit_over := by ext P; rfl

private lemma isLocallyOfFiniteType_morphismSpaceEquiv
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hlocal : AlgebraicGeometry.Space.IsSmoothLocalOnSourceAndTarget B S hS
      (fun {_ _} f => AlgebraicGeometry.Space.IsLocallyOfFiniteType B S hS f))
    {𝒳 𝒴 : AlgebraicGeometry.Stack.AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (hf : AlgebraicGeometry.Stack.AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (F G : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : AlgebraicGeometry.IsAlgebraicSpace B S hS F)
    (hG : AlgebraicGeometry.IsAlgebraicSpace B S hS G)
    (eF : StacksRepresentableCFG.EquivalenceOver 𝒳.val.val.p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver 𝒴.val.val.p
      (presheafOfCategories (G ⋙ typeToCat)).p) :
    AlgebraicGeometry.Space.IsLocallyOfFiniteType B S hS
      (AlgebraicGeometry.Stack.morphismSpaceEquiv B S hS 𝒳.val 𝒴.val F G eF eG
        (Quotient.mk _ ⟨f.hom.hom.toFunctor, f.hom.hom.w⟩)) :=
  (AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_iff_represented B S hS _ hlocal
    𝒳.property 𝒴.property F G hF hG eF eG f.hom).mp
      ((AlgebraicGeometry.Stack.hasPropertyOnEverySmoothDiagram_iff_some B S hS _ hlocal
        𝒳.property 𝒴.property f.hom).mp hf)


/-- The morphisms of the big fppf site of `S` whose underlying morphism of schemes is étale
contain the identities and are closed under composition. -/
private theorem inverseImage_etale_isMultiplicative
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    MorphismProperty.IsMultiplicative
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)) where
  id_mem X := by
    show Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (𝟙 X))
    rw [(AlgebraicGeometry.BigFppfOver.toScheme B S hS).map_id]
    infer_instance
  comp_mem g h hg hh := by
    change Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g) at hg
    change Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map h) at hh
    show Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (g ≫ h))
    rw [Functor.map_comp]
    exact Etale.etale_comp _ _

private lemma locallyOfFiniteType_etale_chart
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (T V : AlgebraicGeometry.BigFppfOver B S hS)
    (d : F ⟶ yoneda.obj T) (hd : AlgebraicGeometry.Space.IsLocallyOfFiniteType B S hS d)
    (p : yoneda.obj V ⟶ F)
    (hp : (MorphismProperty.inverseImage (@Etale.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf p) :
    LocallyOfFiniteType ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
      (yoneda.preimage (p ≫ d))) := by
  apply hd V T p (𝟙 _) (yoneda.preimage (p ≫ d)) hp
  · let : MorphismProperty.RespectsIso (@Etale.{u} : MorphismProperty Scheme.{u}) :=
      MorphismProperty.RespectsIso.mk _
        (fun e g hg => (inferInstance : MorphismProperty.IsMultiplicative
          (@Etale.{u} : MorphismProperty Scheme.{u})).comp_mem _ _ (by infer_instance) hg)
        (fun e g hg => (inferInstance : MorphismProperty.IsMultiplicative
          (@Etale.{u} : MorphismProperty Scheme.{u})).comp_mem _ _ hg (by infer_instance))
    let E : MorphismProperty (AlgebraicGeometry.BigFppfOver B S hS) :=
      MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
    let : MorphismProperty.IsMultiplicative E :=
      inverseImage_etale_isMultiplicative B S hS
    let : MorphismProperty.RespectsIso E :=
      MorphismProperty.RespectsIso.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
    let : MorphismProperty.IsMultiplicative E.presheaf :=
      MorphismProperty.relative_isMultiplicative E
    exact MorphismProperty.id_mem E.presheaf _
  · simp

private lemma presheafObject_eq_of_base_eq
    {C : Type vC} [Category.{u} C] (F : Cᵒᵖ ⥤ Type u)
    (x : (presheafOfCategories (F ⋙ typeToCat)).obj) {U : C}
    (h : x.base = U) :
    x = ⟨U, Discrete.mk
      (cast (congrArg (fun V => F.obj (op V)) h) x.fiber.as)⟩ := by
  cases h
  obtain ⟨U, ⟨a⟩⟩ := x
  rfl

private lemma overFunctor_obj_hom_eq_of_vertical
    {C D : Type*} [Category C] [Category D] {T U : C}
    (p : D ⥤ C) (F : D ⥤ Over T) (hF : F ⋙ Over.forget T = p)
    (x y : D) (hx : p.obj x = U) (hy : p.obj y = U)
    (α : x ⟶ y) (hα : p.IsHomLift (𝟙 U) α) :
    eqToHom ((Functor.congr_obj hF x).trans hx).symm ≫ (F.obj x).hom =
      eqToHom ((Functor.congr_obj hF y).trans hy).symm ≫ (F.obj y).hom := by
  have hα' : (Over.forget T).IsHomLift (𝟙 U) (F.map α) :=
    Functor.isHomLift_map_of_comp_eq hF (𝟙 U) α
  have hw := (F.map α).w
  have hfac := IsHomLift.fac' (Over.forget T) (𝟙 U) (F.map α)
  dsimp at hw hfac
  rw [hfac] at hw
  simpa using
    (congrArg (fun z =>
      eqToHom ((Functor.congr_obj hF x).trans hx).symm ≫ z) hw).symm

end

/-- The Yoneda preimage of a map between representables is the corresponding Yoneda element. -/
private lemma yoneda_preimage_eq_yonedaEquiv {C : Type*} [Category C] {X Y : C}
    (g : yoneda.obj X ⟶ yoneda.obj Y) : yoneda.preimage g = yonedaEquiv g := by
  simpa only [yonedaEquiv_yoneda_map] using congrArg yonedaEquiv (yoneda.map_preimage g)

private def baseFieldPointOfFieldPoint
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒴 : AlgebraicGeometry.Stack.AlgebraicStacks.{u, w} B S hS}
    (y : AlgebraicGeometry.Stack.FieldValuedPoint B S hS 𝒴.val.val) :
    AlgebraicGeometry.Stack.FieldValuedPoint B S hS
      (AlgebraicGeometry.Stack.schemeStack.{u, w} B S hS y.base).val.val where
  carrier := y.carrier
  field := y.field
  base := y.base
  isSpec := y.isSpec
  obj := Over.mk (𝟙 y.base)
  «over» := rfl


/-- Let `f : 𝒳 ⟶ 𝒴` be a universally injective 1-morphism of algebraic stacks and `y : Spec k ⟶ 𝒴`
a morphism with `k` algebraically closed. If `y` is in the image of `|𝒳| → |𝒴|`, then there is
`x : Spec k ⟶ 𝒳` with `y = f ∘ x`: an object `x` of the fibre of `𝒳` over the base of `y` whose
image under `f` is isomorphic to `y` in that fibre. -/
@[stacks 0DTM]
theorem exists_fiber_lift_of_universallyInjective
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : AlgebraicGeometry.Stack.AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (hf : AlgebraicGeometry.Stack.UniversallyInjective B S hS f)
    (y : AlgebraicGeometry.Stack.FieldValuedPoint B S hS 𝒴.val.val)
    [IsAlgClosed y.carrier]
    (hy : AlgebraicGeometry.Stack.pointClass B S hS 𝒴.val.val
      𝒴.val.isFiberedInGroupoids y ∈
        Set.range (AlgebraicGeometry.Stack.pointsMap B S hS 𝒳.val.val
          𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids f.hom.hom)) :
    ∃ x : 𝒳.val.val.p.Fiber y.base,
      Nonempty
        (((Functor.fiberMap 𝒳.val.val.p 𝒴.val.val.p
          f.hom.hom.toFunctor f.hom.hom.w y.base).obj x) ≅
          (⟨y.obj, y.over⟩ : 𝒴.val.val.p.Fiber y.base)) := by
  classical
  have hf' : AlgebraicGeometry.Stack.UniversallyInjective.{u, w} B S hS f := hf
  rcases hy with ⟨c, hc⟩
  obtain ⟨p, rfl⟩ := Quotient.exists_rep c
  have hclass :
      AlgebraicGeometry.Stack.pointClass B S hS 𝒴.val.val 𝒴.val.isFiberedInGroupoids
          (AlgebraicGeometry.Stack.fieldValuedPointMap B S hS 𝒳.val.val f.hom.hom p) =
        AlgebraicGeometry.Stack.pointClass B S hS 𝒴.val.val
          𝒴.val.isFiberedInGroupoids y := by
    simpa only [AlgebraicGeometry.Stack.pointsMap_class] using hc
  let Z : AlgebraicGeometry.Stack.AlgebraicStacks.{u, w} B S hS :=
    AlgebraicGeometry.Stack.schemeStack.{u, w} B S hS y.base
  let z : AlgebraicGeometry.Stack.FieldValuedPoint B S hS Z.val.val :=
    baseFieldPointOfFieldPoint B S hS y
  let gInner : AlgebraicGeometry.Stack.schemeFibredCategory B S hS y.base ⟶ 𝒴.val :=
    Bicategory.InducedBicategory.mkHom
      (Functor.TwoYoneda.liftBased 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
        y.base (Functor.Fiber.mk (a := y.obj) y.over))
  let g : Z ⟶ 𝒴 := Bicategory.InducedBicategory.mkHom gInner
  have hbasePoint :
      AlgebraicGeometry.Stack.pointsMap B S hS Z.val.val Z.val.isFiberedInGroupoids
        𝒴.val.isFiberedInGroupoids g.hom.hom
          (AlgebraicGeometry.Stack.pointClass B S hS Z.val.val Z.val.isFiberedInGroupoids z) =
        AlgebraicGeometry.Stack.pointClass B S hS 𝒴.val.val 𝒴.val.isFiberedInGroupoids y := by
    rw [AlgebraicGeometry.Stack.pointsMap_class]
    apply (AlgebraicGeometry.Stack.class_eq_class_iff_hasCommonExtension B S hS
      𝒴.val.val 𝒴.val.isFiberedInGroupoids _ _).2
    let mapped := AlgebraicGeometry.Stack.fieldValuedPointMap B S hS Z.val.val g.hom.hom z
    let L := Functor.TwoYoneda.chosenLift 𝒴.val.val.p
      𝒴.val.isFiberedInGroupoids y.base (Functor.Fiber.mk (a := y.obj) y.over)
      (Over.mk (𝟙 y.base))
    refine ⟨mapped, ⟨𝟙 mapped.obj⟩, ?_⟩
    show Nonempty ((g.hom.hom.toFunctor.obj z.obj) ⟶ y.obj)
    show Nonempty (L.y ⟶ y.obj)
    exact ⟨L.φ⟩
  let P := AlgebraicGeometry.Stack.AlgebraicStacks.twoFibreProductSquare.{u, w} B S hS g f
  have hP : Bicategory.IsTwoFibreProduct P :=
    AlgebraicGeometry.Stack.AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare.{u, w}
      B S hS g f
  have hcompat :
      AlgebraicGeometry.Stack.pointsMap B S hS Z.val.val Z.val.isFiberedInGroupoids
        𝒴.val.isFiberedInGroupoids g.hom.hom
          (AlgebraicGeometry.Stack.pointClass B S hS Z.val.val Z.val.isFiberedInGroupoids z) =
      AlgebraicGeometry.Stack.pointsMap B S hS 𝒳.val.val 𝒳.val.isFiberedInGroupoids
        𝒴.val.isFiberedInGroupoids f.hom.hom
          (AlgebraicGeometry.Stack.pointClass B S hS 𝒳.val.val 𝒳.val.isFiberedInGroupoids p) :=
    hbasePoint.trans hclass.symm
  obtain ⟨fiberPoint, _, _⟩ :=
    AlgebraicGeometry.Stack.AlgebraicStacks.exists_point_of_isTwoFibreProduct.{u, w}
    B S hS P hP (AlgebraicGeometry.Stack.pointClass B S hS Z.val.val Z.val.isFiberedInGroupoids z)
    (AlgebraicGeometry.Stack.pointClass B S hS 𝒳.val.val 𝒳.val.isFiberedInGroupoids p) hcompat
  have hinj :
      Function.Injective (AlgebraicGeometry.Stack.pointsMap B S hS P.pt.val.val
        (Classical.choose P.pt.property) Z.val.isFiberedInGroupoids P.fst.hom.hom) :=
    hf' Z g P hP
  have hZ : Subsingleton (AlgebraicGeometry.Stack.points B S hS Z.val.val
      Z.val.isFiberedInGroupoids) := by
    let hrep (a : AlgebraicGeometry.Stack.points B S hS Z.val.val Z.val.isFiberedInGroupoids) :
        a = AlgebraicGeometry.Stack.pointClass B S hS Z.val.val Z.val.isFiberedInGroupoids z := by
      refine Quotient.inductionOn a ?_
      intro a
      apply (AlgebraicGeometry.Stack.class_eq_class_iff_hasCommonExtension B S hS
        Z.val.val Z.val.isFiberedInGroupoids a z).2
      refine ⟨a, ⟨𝟙 a.obj⟩, ?_⟩
      exact ⟨Over.homMk a.obj.hom (by
        show Over.hom a.obj ≫ Over.hom z.obj = Over.hom a.obj
        simp [z, baseFieldPointOfFieldPoint])⟩
    exact ⟨fun a b => (hrep a).trans (hrep b).symm⟩
  have hPsub : Subsingleton (AlgebraicGeometry.Stack.points B S hS P.pt.val.val
      (Classical.choose P.pt.property)) :=
    ⟨fun a b => hinj (hZ.elim _ _)⟩
  let := hPsub
  obtain ⟨R, inc, hincFull, hincFaithful, hincSurj, hRred⟩ :
      ∃ (ℛ : AlgebraicGeometry.Stack.AlgebraicStacks.{u, w} B S hS) (inc : ℛ ⟶ P.pt),
        Functor.Full (CatFiberedInGroupoids.homFunctor inc.hom) ∧
          Functor.Faithful (CatFiberedInGroupoids.homFunctor inc.hom) ∧
          Function.Surjective (AlgebraicGeometry.Stack.pointsMap B S hS ℛ.val.val
            (Classical.choose ℛ.property) (Classical.choose P.pt.property) inc.hom.hom) ∧
          AlgebraicGeometry.Stack.IsReducedStack B S hS ℛ := by
    obtain ⟨Q, ⟨-, hQ, -⟩, hQspec⟩ :=
      AlgebraicGeometry.Stack.exists_reduction.{u, w} B S hS P.pt
    obtain ⟨hQred, hQsurj⟩ := hQspec hQ
    exact ⟨fullSubcategoryAlgebraicStack P.pt Q hQ, fullSubcategoryInclusion P.pt Q hQ,
      ObjectProperty.full_ι Q, ObjectProperty.faithful_ι Q, hQsurj, hQred⟩
  let := hincFull
  let := hincFaithful
  have hRnonempty : Nonempty (AlgebraicGeometry.Stack.points B S hS R.val.val
      (Classical.choose R.property)) := by
    obtain ⟨r, -⟩ := hincSurj fiberPoint
    exact ⟨r⟩
  have hinc : Function.Injective (AlgebraicGeometry.Stack.pointsMap B S hS R.val.val
      (Classical.choose R.property) (Classical.choose P.pt.property) inc.hom.hom) :=
    AlgebraicGeometry.Stack.pointsMap_injective_of_fullyFaithful.{u, w} B S hS inc
  have hRsub : Subsingleton (AlgebraicGeometry.Stack.points B S hS R.val.val
      (Classical.choose R.property)) :=
    ⟨fun _ _ ↦ hinc (hPsub.elim _ _)⟩
  have h06MN : AlgebraicGeometry.Stack.IsReducedWithUniquePoint B S hS R ↔
      AlgebraicGeometry.Stack.HasLocallyOfFiniteTypeFlatFieldSpectrumCover B S hS R :=
    (AlgebraicGeometry.Stack.tfae_isReducedWithUniquePoint.{u, w} B S hS R).out 1 3
  obtain ⟨F, cover, hcoverLft, -, -⟩ := h06MN.mp ⟨hRred, hRnonempty, hRsub⟩
  obtain ⟨k', T, eT⟩ := F
  have hkSpec : Nonempty (((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T) ≅
      Spec (.of k')) := ⟨eT⟩
  have hkIso := hkSpec
  let r := cover.hom.hom.toFunctor.obj (Over.mk (𝟙 T))
  let q := inc.hom.hom.toFunctor.obj r
  let b : q.x.left ⟶ y.base := q.x.hom
  let L := Functor.TwoYoneda.chosenLift 𝒴.val.val.p
    𝒴.val.isFiberedInGroupoids y.base (Functor.Fiber.mk (a := y.obj) y.over) q.x
  let e : f.hom.hom.toFunctor.obj q.y ⟶ y.obj := q.iso.inv ≫ L.φ
  have he : 𝒴.val.val.p.IsHomLift b e := by
    have hv : 𝒴.val.val.p.IsHomLift (𝟙 q.base) q.iso.inv := by
      have := q.vertical
      exact IsHomLift.lift_id_inv 𝒴.val.val.p q.base q.iso
    have hv' : 𝒴.val.val.p.IsHomLift (𝟙 q.x.left) q.iso.inv := by
      have hqx : q.x.left = q.base := q.hx
      rwa [← hqx] at hv
    have hl : 𝒴.val.val.p.IsHomLift b L.φ :=
      L.isStronglyCartesian.toIsHomLift
    exact @IsHomLift.comp_lift_id_left' _ _ _ _ 𝒴.val.val.p
      _ _ _ q.x.left q.iso.inv hv' _ _ b L.φ hl
  suffices hb : IsIso b by
    exact exists_fiber_lift_of_split_base 𝒳.val.val.p 𝒴.val.val.p
      f.hom.hom.toFunctor f.hom.hom.w 𝒳.val.isFiberedInGroupoids
      𝒴.val.isFiberedInGroupoids b (inv b) (IsIso.inv_hom_id b)
      q.y (q.hy.trans q.hx.symm) ⟨y.obj, y.over⟩ e he
  have hqbase : q.base = T :=
    (inc.hom.hom.w_obj r).trans
      (cover.hom.hom.w_obj (Over.mk (𝟙 T)))
  have hdom : q.x.left = T := q.hx.trans hqbase
  let eK : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj q.x.left ≅
      Spec (.of k') :=
    eqToIso (congrArg (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj hdom) ≪≫ hkIso.some
  let ek := y.isSpec
  let bSpec : Spec (.of k') ⟶ Spec (.of y.carrier) :=
    eK.inv ≫ (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map b ≫ ek.hom
  let φ : y.carrier →+* k' := (Spec.preimage bSpec).hom
  let : Algebra y.carrier k' := φ.toAlgebra
  have : IsDomain (k' ⊗[y.carrier] k') :=
    isDomain_tensorProduct_of_isAlgClosed y.carrier k' k'
  suffices hφ : Function.Surjective (algebraMap y.carrier k') by
    have hbSpec : IsIso bSpec := isIso_of_surjective_spec_preimage bSpec hφ
    have hmap : IsIso ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map b) := by
      have heq : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map b =
          eK.hom ≫ bSpec ≫ ek.inv := by simp [bSpec]
      rw [heq]
      infer_instance
    exact isIso_of_reflects_iso b (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  suffices hchart : ∃ (U : Scheme.{u})
      (a : U ⟶ Spec (.of (k' ⊗[y.carrier] k'))),
      LocallyOfFiniteType
        (a ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom)) ∧
      LocallyOfFiniteType
        (a ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom)) ∧
      ∃ v : U, IsGenericPoint (a v) Set.univ by
    obtain ⟨U, a, hleft, hright, v, hv⟩ := hchart
    exact algebraMap_surjective_of_generic_point_lift y.carrier k' U a v hv
  have hgeom :=
    (AlgebraicGeometry.Stack.universallyInjective_iff_liftsTwoArrowsAtGeometricPoints.{u, w}
      B S hS P.fst).mp
      (AlgebraicGeometry.Stack.universallyInjective_baseChange.{u, w} B S hS f g hf' P hP)
  have hdiagR : AlgebraicGeometry.Stack.HasRepresentableDiagonal B S hS R.val :=
    (Classical.choose_spec R.property).2.1
  have hrepR :=
    (AlgebraicGeometry.Stack.isAlgebraicSpaceIsomPresheaf_iff_isRepresentableFromSchemes
      B S hS R.val).mp
      ((AlgebraicGeometry.Stack.hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf
        B S hS R.val).mp hdiagR)
  have hrel :=
    (AlgebraicGeometry.Stack.isRepresentableFromSchemes_iff_hasAlgebraicSpaceSchemePointProducts
      B S hS R.val).mp hrepR T T cover.hom.hom cover.hom.hom
  obtain ⟨F, hF, ⟨eF⟩⟩ := hrel
  obtain ⟨V, pV, hpVSurj, hpVEtale⟩ := hF.exists_atlas
  let relPoint := eF.inv.functor.obj
    ⟨V, Discrete.mk (yonedaEquiv pV)⟩
  have hrelBase : relPoint.base = V :=
    congrArg (fun H => H.obj ⟨V, Discrete.mk (yonedaEquiv pV)⟩) eF.inv.w
  let a₁ : V ⟶ T := eqToHom (relPoint.hx.trans hrelBase).symm ≫ relPoint.x.hom
  let a₂ : V ⟶ T := eqToHom (relPoint.hy.trans hrelBase).symm ≫ relPoint.y.hom
  let Q := AlgebraicGeometry.Stack.AlgebraicStacks.twoFibreProductSquare.{u, w} B S hS cover cover
  have hrelFst : Q.fst.hom.hom.toFunctor.obj relPoint = relPoint.x := by
    rfl
  have hrelSnd : Q.snd.hom.hom.toFunctor.obj relPoint = relPoint.y := by
    rfl
  have hQlft :=
    AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFiniteType_baseChange.{u, w}
      B S hS cover cover Q
      (AlgebraicGeometry.Stack.AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare.{u, w}
        B S hS cover cover) hcoverLft
  have hQsndLft : AlgebraicGeometry.Stack.AlgebraicStacks.IsLocallyOfFiniteType B S hS Q.snd :=
    AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFiniteType_baseChange.{u, w}
      B S hS cover cover Q.swap
      (Bicategory.isTwoFibreProduct_swap
        (AlgebraicGeometry.Stack.AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare.{u, w}
          B S hS cover cover)) hcoverLft
  let d (G : Q.pt ⟶ AlgebraicGeometry.Stack.schemeStack.{u, w} B S hS T) : F ⟶ yoneda.obj T :=
    AlgebraicGeometry.Stack.morphismSpaceEquiv.{u, u + 1} B S hS Q.pt.val
      (AlgebraicGeometry.Stack.schemeStack.{u, w} B S hS T).val
      F (yoneda.obj T) eF (schemePresheafEquivalenceOver T)
      (Quotient.mk _ ⟨G.hom.hom.toFunctor, G.hom.hom.w⟩)
  have hlft (G : Q.pt ⟶ AlgebraicGeometry.Stack.schemeStack.{u, w} B S hS T)
      (hG : AlgebraicGeometry.Stack.AlgebraicStacks.IsLocallyOfFiniteType B S hS G)
      (a' : V ⟶ T) (ha : yoneda.preimage (pV ≫ d G) = a') :
      LocallyOfFiniteType ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map a') := by
    rw [← ha]
    exact locallyOfFiniteType_etale_chart B S hS T V (d G)
      (isLocallyOfFiniteType_morphismSpaceEquiv.{u, w} B S hS
        (AlgebraicGeometry.Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType
          B S hS) G hG F (yoneda.obj T) hF
        (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T) eF
        (schemePresheafEquivalenceOver T)) pV hpVEtale
  have ha₁ : yoneda.preimage (pV ≫ d Q.fst) = a₁ := by
    rw [yoneda_preimage_eq_yonedaEquiv, yonedaEquiv_comp]
    convert
      morphismSpaceEquiv_to_scheme_apply B S hS Q.pt.val T F eF
        Q.fst.hom.hom.toFunctor Q.fst.hom.hom.w V (yonedaEquiv pV) using 1
    simp [a₁, d, relPoint, Q,
      AlgebraicGeometry.Stack.AlgebraicStacks.twoFibreProductSquare]
    rfl
  have ha₂ : yoneda.preimage (pV ≫ d Q.snd) = a₂ := by
    rw [yoneda_preimage_eq_yonedaEquiv, yonedaEquiv_comp]
    convert
      morphismSpaceEquiv_to_scheme_apply B S hS Q.pt.val T F eF
        Q.snd.hom.hom.toFunctor Q.snd.hom.hom.w V (yonedaEquiv pV) using 1
    simp [a₂, d, relPoint, Q,
      AlgebraicGeometry.Stack.AlgebraicStacks.twoFibreProductSquare]
    rfl
  let H : Over T ⥤ Over y.base :=
    cover.hom.hom.toFunctor ⋙ inc.hom.hom.toFunctor ⋙ P.fst.hom.hom.toFunctor
  have hH : H ⋙ Over.forget y.base = Over.forget T := by
    show (cover.hom.hom.toFunctor ⋙ inc.hom.hom.toFunctor ⋙
      P.fst.hom.hom.toFunctor) ⋙ Z.val.val.p = Over.forget T
    simp only [Functor.assoc, P.fst.hom.hom.w,
      inc.hom.hom.w, cover.hom.hom.w]
    rfl
  let bT : T ⟶ y.base :=
    eqToHom (Functor.congr_obj hH (Over.mk (𝟙 T))).symm ≫
      (H.obj (Over.mk (𝟙 T))).hom
  let α := P.fst.hom.hom.toFunctor.map
    (inc.hom.hom.toFunctor.map relPoint.iso.hom)
  have hα : (Over.forget y.base).IsHomLift (𝟙 V) α := by
    have hi : R.val.val.p.IsHomLift (𝟙 V) relPoint.iso.hom := by
      rw [← hrelBase]
      exact relPoint.vertical
    have hi' : (inc.hom.hom.toFunctor ⋙ P.fst.hom.hom.toFunctor ⋙
        Over.forget y.base).IsHomLift (𝟙 V) relPoint.iso.hom := by
      have hw : inc.hom.hom.toFunctor ⋙ P.fst.hom.hom.toFunctor ⋙
          Over.forget y.base = R.val.val.p := by
        show inc.hom.hom.toFunctor ⋙ P.fst.hom.hom.toFunctor ⋙
          Z.val.val.p = R.val.val.p
        simp only [P.fst.hom.hom.w, inc.hom.hom.w]
      rwa [hw]
    show (Z.val.val.p).IsHomLift (𝟙 V) α
    let pComp := inc.hom.hom.toFunctor ⋙ P.fst.hom.hom.toFunctor ⋙ Z.val.val.p
    let : pComp.IsHomLift (𝟙 V) relPoint.iso.hom := hi'
    have hd : Z.val.val.p.obj (P.fst.hom.hom.toFunctor.obj
        (inc.hom.hom.toFunctor.obj
          (cover.hom.hom.toFunctor.obj relPoint.x))) = V :=
      IsHomLift.domain_eq pComp (𝟙 V) relPoint.iso.hom
    have hc : Z.val.val.p.obj (P.fst.hom.hom.toFunctor.obj
        (inc.hom.hom.toFunctor.obj
          (cover.hom.hom.toFunctor.obj relPoint.y))) = V :=
      IsHomLift.codomain_eq pComp (𝟙 V) relPoint.iso.hom
    apply IsHomLift.of_fac (Z.val.val.p) (𝟙 V) α hd hc
    simpa only [pComp, α, Functor.comp_map] using
      (IsHomLift.fac pComp (𝟙 V) relPoint.iso.hom)
  have hab : a₁ ≫ bT = a₂ ≫ bT :=
    overFunctor_comp_eq_of_vertical H hH relPoint.x relPoint.y
      (relPoint.hx.trans hrelBase) (relPoint.hy.trans hrelBase) α hα
  let j₁ : V.left.obj ⟶ Spec (.of k') :=
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map a₁ ≫ hkIso.some.hom
  let j₂ : V.left.obj ⟶ Spec (.of k') :=
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map a₂ ≫ hkIso.some.hom
  have hbT : bT = eqToHom hdom.symm ≫ b := rfl
  have hbSpecMap : hkIso.some.inv ≫
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map bT ≫ ek.hom = bSpec := by
    simp [hbT, bSpec, eK]
  have hcomm :
      j₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap y.carrier k')) =
        j₂ ≫ Spec.map (CommRingCat.ofHom (algebraMap y.carrier k')) := by
    have hm : Spec.map (CommRingCat.ofHom (algebraMap y.carrier k')) = bSpec :=
      Spec.map_preimage bSpec
    rw [hm, ← hbSpecMap]
    simpa [j₁, j₂, ← Functor.map_comp] using
      congrArg (fun z => (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map z ≫ ek.hom) hab
  let a : V.left.obj ⟶ Spec (.of (k' ⊗[y.carrier] k')) :=
    Limits.pullback.lift j₁ j₂ hcomm ≫ (pullbackSpecIso y.carrier k' k').hom
  have hal : a ≫ Spec.map
      (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) = j₁ := by
    simp only [a, Category.assoc, pullbackSpecIso_hom_fst,
      Limits.pullback.lift_fst]
  have har : a ≫ Spec.map
      (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) = j₂ := by
    dsimp [a]
    rw [Category.assoc, pullbackSpecIso_hom_snd, Limits.pullback.lift_snd]
  let : LocallyOfFiniteType
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map a₁) := hlft Q.fst hQlft a₁ ha₁
  have hl : LocallyOfFiniteType
      (a ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom)) := by
    rw [hal]
    let : IsFinite hkIso.some.hom := inferInstance
    exact locallyOfFiniteType_comp
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map a₁) hkIso.some.hom
  let : LocallyOfFiniteType
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map a₂) := hlft Q.snd hQsndLft a₂ ha₂
  have hr : LocallyOfFiniteType j₂ := by
    let : IsFinite hkIso.some.hom := inferInstance
    exact locallyOfFiniteType_comp
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map a₂) hkIso.some.hom
  suffices hrest : ∃ v : V.left.obj,
      IsGenericPoint (a v) Set.univ by
    exact ⟨V.left.obj, a, hl, har.symm ▸ hr, hrest⟩
  have hk'Site : B.Contains (Spec (.of k')) := by
    show (Spec (.of k')).size < B.cutoff
    rw [← Scheme.size_congr hkIso.some]
    exact T.left.property
  have hTensorSite : B.Contains (Spec (.of (k' ⊗[y.carrier] k'))) :=
    tensorProduct_spec_in_site B hk'Site
  let pLs : Spec (.of (k' ⊗[y.carrier] k')) ⟶ Spec (.of k') :=
    Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom)
  let pRs : Spec (.of (k' ⊗[y.carrier] k')) ⟶ Spec (.of k') :=
    Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom)
  have hpSpecBase :
      pRs ≫ Spec.map (CommRingCat.ofHom (algebraMap y.carrier k')) =
        pLs ≫ Spec.map (CommRingCat.ofHom (algebraMap y.carrier k')) := by
    dsimp [pRs, pLs]
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    ext r
    show (Algebra.TensorProduct.includeRight : k' →ₐ[y.carrier]
      k' ⊗[y.carrier] k') (algebraMap y.carrier k' r) =
        (Algebra.TensorProduct.includeLeft : k' →ₐ[y.carrier]
          k' ⊗[y.carrier] k') (algebraMap y.carrier k' r)
    rw [Algebra.TensorProduct.includeRight.commutes,
      Algebra.TensorProduct.includeLeft.commutes]
  let specToS : Spec (.of k') ⟶ S :=
    hkIso.some.inv ≫ B.inclusion.map T.hom
  let Dbase : Spec (.of (k' ⊗[y.carrier] k')) ⟶ S := pLs ≫ specToS
  let Dobj : AlgebraicGeometry.BigFppfOver B S hS :=
    Over.mk (ObjectProperty.homMk Dbase : B.obj hTensorSite ⟶ B.obj hS)
  have hSpecToS :
      specToS = Spec.map (CommRingCat.ofHom (algebraMap y.carrier k')) ≫
        ek.inv ≫ B.inclusion.map y.base.hom := by
    have hOver :
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map bT ≫
          B.inclusion.map y.base.hom = B.inclusion.map T.hom := by
      show B.inclusion.map bT.left ≫ B.inclusion.map y.base.hom =
        B.inclusion.map T.hom
      rw [← Functor.map_comp, bT.w]
    have hm : Spec.map (CommRingCat.ofHom (algebraMap y.carrier k')) = bSpec :=
      Spec.map_preimage bSpec
    calc
      specToS = hkIso.some.inv ≫
          ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map bT ≫
            B.inclusion.map y.base.hom) := by rw [hOver]
      _ = (hkIso.some.inv ≫
            (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map bT ≫ ek.hom) ≫
            ek.inv ≫ B.inclusion.map y.base.hom := by simp [Category.assoc]
      _ = bSpec ≫ ek.inv ≫ B.inclusion.map y.base.hom := by
        rw [hbSpecMap]
      _ = Spec.map (CommRingCat.ofHom (algebraMap y.carrier k')) ≫
            ek.inv ≫ B.inclusion.map y.base.hom := by rw [hm]
  have hpRsBase : pRs ≫ specToS = Dbase := by
    dsimp [Dbase]
    rw [hSpecToS]
    simpa only [Category.assoc] using congrArg
      (fun z => z ≫ ek.inv ≫ B.inclusion.map y.base.hom) hpSpecBase
  let pLSpec : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj Dobj ⟶
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T :=
    pLs ≫ hkIso.some.inv
  let pRSpec : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj Dobj ⟶
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T :=
    pRs ≫ hkIso.some.inv
  let pL : Dobj ⟶ T := Over.homMk (B.inclusion.preimage pLSpec) (by
    apply B.inclusion.map_injective
    rw [B.inclusion.map_comp, B.inclusion.map_preimage]
    rfl)
  let pR : Dobj ⟶ T := Over.homMk (B.inclusion.preimage pRSpec) (by
    apply B.inclusion.map_injective
    rwa [B.inclusion.map_comp, B.inclusion.map_preimage])
  have hpLPR : pL ≫ bT = pR ≫ bT := by
    have hSpecComposed :
        pLSpec ≫ (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map bT ≫ ek.hom =
          pRSpec ≫ (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map bT ≫ ek.hom := by
      calc
        pLSpec ≫ (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map bT ≫ ek.hom =
            pLs ≫ bSpec := by simp only [pLSpec, Category.assoc, hbSpecMap]
        _ = pRs ≫ bSpec := by
          rw [← Spec.map_preimage bSpec]
          exact hpSpecBase.symm
        _ = pRSpec ≫ (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map bT ≫ ek.hom := by
          simp only [pRSpec, Category.assoc, hbSpecMap]
    have hSpec : pLSpec ≫ (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map bT =
        pRSpec ≫ (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map bT := by
      simpa [Category.assoc] using congrArg (fun z => z ≫ ek.inv) hSpecComposed
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    show B.inclusion.map (B.inclusion.preimage pLSpec ≫ bT.left) =
      B.inclusion.map (B.inclusion.preimage pRSpec ≫ bT.left)
    rwa [B.inclusion.map_comp, B.inclusion.map_comp,
      B.inclusion.map_preimage, B.inclusion.map_preimage]
  let eta : Spec (.of (k' ⊗[y.carrier] k')) := genericPoint _
  have hEta : IsGenericPoint eta Set.univ := genericPoint_spec _
  have hClosureSite := algebraicClosure_residueField_in_site B S hS Dobj eta
  let K := ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj Dobj).residueField eta
  let L := AlgebraicClosure K
  let qSpec : Spec (.of L) ⟶
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj Dobj :=
    Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj Dobj).fromSpecResidueField eta
  let Ubase : Spec (.of L) ⟶ S := qSpec ≫ Dbase
  let U : AlgebraicGeometry.BigFppfOver B S hS :=
    Over.mk (ObjectProperty.homMk Ubase : B.obj hClosureSite ⟶ B.obj hS)
  let q : U ⟶ Dobj := Over.homMk (B.inclusion.preimage qSpec) (by
    apply B.inclusion.map_injective
    rw [B.inclusion.map_comp, B.inclusion.map_preimage]
    rfl)
  have hqGeneric : qSpec (default : Spec (.of L)) = eta := by
    have hUnique :
        Spec.map (CommRingCat.ofHom (algebraMap K L))
          (default : Spec (.of L)) = (default : Spec (.of K)) :=
      (inferInstance : Unique (Spec (.of K))).uniq _
    show ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj Dobj).fromSpecResidueField eta
      (Spec.map (CommRingCat.ofHom (algebraMap K L)) (default : Spec (.of L))) = eta
    rw [hUnique]
    exact ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj Dobj).fromSpecResidueField_apply
      eta (default : Spec (.of K))
  let uL : U ⟶ T := q ≫ pL
  let uR : U ⟶ T := q ≫ pR
  have huLUR : uL ≫ bT = uR ≫ bT := by
    simpa only [uL, uR, Category.assoc] using
      congrArg (fun z : Dobj ⟶ y.base => q ≫ z) hpLPR
  let oL : Over T := Over.mk uL
  let oR : Over T := Over.mk uR
  let rL := cover.hom.hom.toFunctor.obj oL
  let rR := cover.hom.hom.toFunctor.obj oR
  let xL := inc.hom.hom.toFunctor.obj rL
  let xR := inc.hom.hom.toFunctor.obj rR
  have hxL : P.pt.val.val.p.obj xL = U :=
    (inc.hom.hom.w_obj rL).trans (cover.hom.hom.w_obj oL)
  have hxR : P.pt.val.val.p.obj xR = U :=
    (inc.hom.hom.w_obj rR).trans (cover.hom.hom.w_obj oR)
  have ht (A : Over T) :
      eqToHom (Functor.congr_obj hH A).symm ≫ (H.obj A).hom =
        A.hom ≫ bT :=
    overFunctor_obj_hom H hH A
  obtain ⟨β, hβ⟩ :=
    overFunctor_verticalIso_of_equal_comp H hH bT ht uL uR huLUR
  have hβ' : Z.val.val.p.IsHomLift (𝟙 U) β.hom := hβ
  obtain ⟨α, hα, hαmap⟩ := hgeom L U (Iso.refl _) xL xR hxL hxR β.hom hβ'
  let αR : rL ⟶ rR := inc.hom.hom.toFunctor.preimage α
  have hαR : R.val.val.p.IsHomLift (𝟙 U) αR := by
    have hmap : P.pt.val.val.p.IsHomLift (𝟙 U)
        (inc.hom.hom.toFunctor.map αR) := by
      simpa [αR] using hα
    let := hmap
    exact inc.hom.hom.isHomLift_map (𝟙 U) αR
  let : IsIso αR := R.val.isFiberedInGroupoids.isIso_of_isHomLift_id αR hαR
  let relLift : Q.pt.val.val.obj := {
    base := U
    x := oL
    y := oR
    hx := rfl
    hy := rfl
    iso := asIso αR
    vertical := hαR
  }
  let s : F.obj (op U) :=
    cast (congrArg (fun W => F.obj (op W))
      (Functor.congr_obj eF.hom.w relLift))
      (eF.hom.functor.obj relLift).fiber.as
  let gs : yoneda.obj U ⟶ F := (yonedaEquiv (X := U) (F := F)).symm s
  let W := hpVSurj.1.pullback gs
  let tW : W ⟶ U := hpVSurj.1.snd gs
  let vW : yoneda.obj W ⟶ yoneda.obj V := hpVSurj.1.fst gs
  have htW : Surjective ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map tW) :=
    hpVSurj.2 gs vW tW (hpVSurj.1.isPullback gs)
  have hsections : yoneda.preimage (gs ≫ d Q.fst) = uL ∧
      yoneda.preimage (gs ≫ d Q.snd) = uR := by
    have henc : eF.hom.functor.obj relLift = ⟨U, Discrete.mk s⟩ :=
      presheafObject_eq_of_base_eq F _
        (Functor.congr_obj eF.hom.w relLift)
    let z := eF.inv.functor.obj ⟨U, Discrete.mk s⟩
    let δ : relLift ⟶ z := eF.unitIso.hom.app relLift ≫
      eF.inv.functor.map (eqToHom henc)
    have hEq : (presheafOfCategories (F ⋙ typeToCat)).p.IsHomLift
        (𝟙 U) (eqToHom henc) :=
      IsHomLift.eqToHom_codomain_lift_id _ rfl
    have hδ : Q.pt.val.val.p.IsHomLift (𝟙 U) δ := by
      have hunit : Q.pt.val.val.p.IsHomLift (𝟙 U)
          (eF.unitIso.hom.app relLift) := eF.isHomLift_unitIso_hom_app relLift
      have hmap : Q.pt.val.val.p.IsHomLift (𝟙 U)
          (eF.inv.functor.map (eqToHom henc)) :=
        Functor.isHomLift_map_of_comp_eq eF.inv.w (𝟙 U) (eqToHom henc)
      simpa [δ] using IsHomLift.comp Q.pt.val.val.p (𝟙 U) (𝟙 U)
        (eF.unitIso.hom.app relLift) (eF.inv.functor.map (eqToHom henc))
    have hz : Q.pt.val.val.p.obj z = U :=
      Functor.congr_obj eF.inv.w ⟨U, Discrete.mk s⟩
    have hvia₁ := overFunctor_obj_hom_eq_of_vertical Q.pt.val.val.p
      Q.fst.hom.hom.toFunctor Q.fst.hom.hom.w relLift z rfl hz δ hδ
    have hvia₂ := overFunctor_obj_hom_eq_of_vertical Q.pt.val.val.p
      Q.snd.hom.hom.toFunctor Q.snd.hom.hom.w relLift z rfl hz δ hδ
    constructor
    · rw [yoneda_preimage_eq_yonedaEquiv, yonedaEquiv_comp]
      show (d Q.fst).app (op U) (yonedaEquiv gs) = uL
      rw [show yonedaEquiv gs = s from
        Equiv.apply_symm_apply (yonedaEquiv (X := U) (F := F)) s]
      rw [morphismSpaceEquiv_to_scheme_apply B S hS Q.pt.val T F eF
        Q.fst.hom.hom.toFunctor Q.fst.hom.hom.w U s]
      have hfin := hvia₁.symm
      simp only [z, Q, AlgebraicGeometry.Stack.AlgebraicStacks.twoFibreProductSquare,
        CatFiberedInGroupoids.twoFibreProductSquare, relLift, oL,
        TwoFibreProductOver.fst, TwoFibreProductOver.structureFunctor,
        CategoryTheory.BasedCategory.ofFunctor, Over.mk_hom] at hfin
      exact hfin
    · rw [yoneda_preimage_eq_yonedaEquiv, yonedaEquiv_comp]
      show (d Q.snd).app (op U) (yonedaEquiv gs) = uR
      rw [show yonedaEquiv gs = s from
        Equiv.apply_symm_apply (yonedaEquiv (X := U) (F := F)) s]
      rw [morphismSpaceEquiv_to_scheme_apply B S hS Q.pt.val T F eF
        Q.snd.hom.hom.toFunctor Q.snd.hom.hom.w U s]
      have hfin := hvia₂.symm
      simp only [z, Q, AlgebraicGeometry.Stack.AlgebraicStacks.twoFibreProductSquare,
        CatFiberedInGroupoids.twoFibreProductSquare, relLift, oR,
        TwoFibreProductOver.snd, TwoFibreProductOver.structureFunctor,
        CategoryTheory.BasedCategory.ofFunctor, Over.mk_hom] at hfin
      exact hfin
  let vSite : W ⟶ V := yoneda.preimage vW
  have hproj (a' : V ⟶ T) (u : U ⟶ T) (d : F ⟶ yoneda.obj T)
      (ha : yoneda.preimage (pV ≫ d) = a') (hu : yoneda.preimage (gs ≫ d) = u) :
      vSite ≫ a' = tW ≫ u := by
    apply yoneda.map_injective
    have hv : yoneda.map vSite = vW := yoneda.map_preimage vW
    have ha' : yoneda.map a' = pV ≫ d := by
      rw [← ha]
      exact yoneda.map_preimage _
    have hu' : yoneda.map u = gs ≫ d := by
      rw [← hu]
      exact yoneda.map_preimage _
    simp only [yoneda.map_comp, hv, ha', hu']
    simpa only [Category.assoc] using
      congrArg (fun z => z ≫ d) (hpVSurj.1.isPullback gs).w
  let tSch := (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map tW
  let vSch := (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map vSite
  have hqSpec : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map q = qSpec := by
    show B.inclusion.map q.left = qSpec
    exact B.inclusion.map_preimage (X := U.left) (Y := Dobj.left) qSpec
  have hqside (p : Spec (.of (k' ⊗[y.carrier] k')) ⟶ Spec (.of k')) (pX : Dobj ⟶ T)
      (h : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map pX = p ≫ hkIso.some.inv) :
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (q ≫ pX) ≫ hkIso.some.hom =
        qSpec ≫ p := by
    rw [Functor.map_comp, hqSpec, h]
    simp [Category.assoc]
  have hside (p : Spec (.of (k' ⊗[y.carrier] k')) ⟶ Spec (.of k')) (a' : V ⟶ T) (u : U ⟶ T)
      (hap : a ≫ p = (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map a' ≫ hkIso.some.hom)
      (hq : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map u ≫ hkIso.some.hom =
        qSpec ≫ p)
      (hp : vSite ≫ a' = tW ≫ u) : (vSch ≫ a) ≫ p = (tSch ≫ qSpec) ≫ p := by
    calc
      _ = vSch ≫ (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map a' ≫
          hkIso.some.hom := by rw [Category.assoc, hap]
      _ = tSch ≫ (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map u ≫
          hkIso.some.hom := by
            simpa only [vSch, tSch, Functor.map_comp, Category.assoc] using
              congrArg (fun m => (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map m ≫
                hkIso.some.hom) hp
      _ = _ := by rw [Category.assoc, hq, Category.assoc]
  have hTensorEq : vSch ≫ a = tSch ≫ qSpec := by
    let iso := pullbackSpecIso y.carrier k' k'
    have h₁ : iso.inv ≫ Limits.pullback.fst _ _ = pLs := by
      simpa only [iso, pLs] using (pullbackSpecIso_inv_fst y.carrier k' k')
    have h₂ : iso.inv ≫ Limits.pullback.snd _ _ = pRs := by
      simpa only [iso, pRs, AlgHom.toRingHom_eq_coe] using
        (pullbackSpecIso_inv_snd y.carrier k' k')
    have hh : (vSch ≫ a) ≫ iso.inv = (tSch ≫ qSpec) ≫ iso.inv := by
      apply Limits.pullback.hom_ext
      · simpa only [Category.assoc, h₁] using
          hside pLs a₁ uL hal (hqside pLs pL (B.inclusion.map_preimage pLSpec))
            (hproj a₁ uL (d Q.fst) ha₁ hsections.1)
      · simpa only [Category.assoc, h₂] using
          hside pRs a₂ uR har (hqside pRs pR (B.inclusion.map_preimage pRSpec))
            (hproj a₂ uR (d Q.snd) ha₂ hsections.2)
    simpa [Category.assoc] using congrArg (fun z => z ≫ iso.hom) hh
  let : Surjective ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map tW) := htW
  obtain ⟨w₀, hw₀⟩ :=
    ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map tW).surjective
      (default : Spec (.of L))
  refine ⟨vSch w₀, ?_⟩
  have hpoint' : a (vSch w₀) = qSpec (tSch w₀) := congrArg (fun m => m w₀) hTensorEq
  rwa [hpoint', hw₀, hqGeneric]

end AlgebraicGeometry.Stack

end
