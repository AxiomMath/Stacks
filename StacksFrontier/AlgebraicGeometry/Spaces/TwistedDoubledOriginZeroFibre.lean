module

public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.RingTheory.Polynomial.Quotient
public import Mathlib.RingTheory.PolynomialAlgebra
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedDoubledOrigin
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Continuous

/-!
# The fibre of the twisted doubled origin over the origin

Over the origin of the base `S = Spec k[x]` the punctured twisted diagonal of the relation
`R = Δ(U) ⨿ Δ'(U ∖ {0})` disappears, so the two projections of `R` agree there and the
quotient `X = U/R` has the same fibre as the chart `U = Spec K[x]`.  That fibre is
`Spec K`, which is the third assertion of the example.

## Main definitions

* `AlgebraicGeometry.TwistedDoubledOrigin.zeroBaseOverBase` and
  `AlgebraicGeometry.TwistedDoubledOrigin.zeroCoverOverBase` are the origin of the base and
  the origin of the chart, each regarded as a scheme over the base.

## Main results

* `AlgebraicGeometry.TwistedDoubledOrigin.twistedRelationQuotient_zeroFibre`: the fibre of
  the quotient sheaf over the origin of the base is the functor of points of `Spec K`.

## Implementation notes

The fibre is taken as a product of presheaves on the big fppf site over the base; since the
functor of points of the base is terminal there, that product is the fibre product over the
base, and the isomorphism asserted is an isomorphism of presheaves, hence natural in the
test object.

The geometric input is that the second summand of the relation has empty base change to the
origin, so that the base change of the relation to the origin is its first summand, on which
the two projections agree.  Sheafification is left exact and the functor of points of a
scheme over the base is already a sheaf on the site, so the product of the sheafified
coequalizer with the fibre is the sheafification of the product, and the product of the
functors of points is the functor of points of the fibre product.

The conclusion is about the quotient of the twisted relation for an arbitrary automorphism
`σ`, before any hypothesis on the degree of the extension, and specializes to the quotient
of the example by definition.

## References

* [Stacks Project, Tag 03FN](https://stacks.math.columbia.edu/tag/03FN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u v

namespace AlgebraicGeometry.TwistedDoubledOrigin

open Stacks.Groupoids

/-- If a parallel pair of presheaves becomes equal after taking the product with `Z`, then
the product of `Z` with the sheafification of its coequalizer is the sheafification of the
product of `Z` with the common target. -/
private def sheafifyProductCoequalizerIso
    {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) [HasSheafify J (Type u)]
    {P U : Cᵒᵖ ⥤ Type u} (f g : P ⟶ U) (Z : Cᵒᵖ ⥤ Type u)
    (h : (prod.functor.obj Z).map f = (prod.functor.obj Z).map g) :
    (((presheafToSheaf J (Type u)).obj (coequalizer f g)).obj ⨯
      ((presheafToSheaf J (Type u)).obj Z).obj) ≅
      ((presheafToSheaf J (Type u)).obj (Z ⨯ U)).obj := by
  letI : PreservesColimitsOfShape WalkingParallelPair (prod.functor.obj Z) := by
    apply preservesColimitsOfShape_of_evaluation
    intro X
    let E := (evaluation Cᵒᵖ (Type u)).obj X
    let e : prod.functor.obj Z ⋙ E ≅ E ⋙ prod.functor.obj (Z.obj X) :=
      NatIso.ofComponents (fun Y => PreservesLimitPair.iso E Z Y)
        (fun f => prodComparison_natural E (𝟙 Z) f)
    exact preservesColimitsOfShape_of_natIso e.symm
  let L := presheafToSheaf J (Type u)
  let Q := coequalizer f g
  let eprod : L.obj Q ⨯ L.obj Z ≅ L.obj (Q ⨯ Z) := (asIso (prodComparison L Q Z)).symm
  let eflip : Q ⨯ Z ≅ Z ⨯ Q := prod.braiding Q Z
  let ecomp : Z ⨯ Q ≅ Z ⨯ U := by
    have hcoe : coequalizer ((prod.functor.obj Z).map f) ((prod.functor.obj Z).map g) ≅
        (Z ⨯ U) := by
      rw [h]
      exact coequalizer.isoTargetOfSelf ((prod.functor.obj Z).map g)
    exact (PreservesCoequalizer.iso (prod.functor.obj Z) f g).symm.trans hcoe
  let eSheaf := eprod.trans ((L.mapIso eflip).trans (L.mapIso ecomp))
  let E := sheafToPresheaf J (Type u)
  let eForget : E.obj (L.obj Q) ⨯ E.obj (L.obj Z) ≅ E.obj (L.obj Q ⨯ L.obj Z) :=
    (asIso (prodComparison E (L.obj Q) (L.obj Z))).symm
  exact eForget.trans (E.mapIso eSheaf)

/-- The functor of points restricted along a functor into `S`-schemes turns a product of
`S`-schemes into a product of presheaves. -/
private def pointsProductIso
    {C : Type v} [Category.{u} C] {S : Scheme.{u}} (F : C ⥤ Over S) (Y Z : Over S) :
    (points F Y ⨯ points F Z) ≅ points F (Y ⨯ Z) := by
  let W : ((Over S)ᵒᵖ ⥤ Type _) ⥤ (Cᵒᵖ ⥤ Type _) :=
    (Functor.whiskeringLeft Cᵒᵖ (Over S)ᵒᵖ (Type _)).obj F.op
  exact (asIso (prodComparison W (yoneda.obj Y) (yoneda.obj Z))).symm ≪≫
    W.mapIso (asIso (prodComparison (yoneda : Over S ⥤ (Over S)ᵒᵖ ⥤ Type _) Y Z)).symm

variable (k K : Type u) [Field k] [Field K] [Algebra k K]

/-- `K` is a scalar tower over `k` and `K[x]` when `K[x]` acts through evaluation at `0`. -/
private lemma zeroFiberIsScalarTower [Algebra (Polynomial K) K]
    (h : algebraMap (Polynomial K) K = Polynomial.evalRingHom (0 : K)) :
    IsScalarTower k (Polynomial K) K :=
  .of_algebraMap_eq fun a => by simp [h]

/-- Reducing `K[x]` modulo the extension of the ideal of the origin of `k[x]` gives `K`:
the fibre of the chart over the origin of the base is `Spec K`, in algebraic form. -/
private def zeroFiberTensorAlgEquiv :
    letI : Algebra (Polynomial k) (Polynomial K) := Polynomial.algebra k K
    letI : Algebra (Polynomial k) k := (Polynomial.evalRingHom (0 : k)).toAlgebra
    letI : Algebra (Polynomial K) K := (Polynomial.evalRingHom (0 : K)).toAlgebra
    letI : IsScalarTower k (Polynomial K) K := zeroFiberIsScalarTower k K rfl
    Polynomial K ⊗[Polynomial k] k ≃ₐ[k] K := by
  letI : Algebra (Polynomial k) (Polynomial K) := Polynomial.algebra k K
  letI : Algebra (Polynomial k) k := (Polynomial.evalRingHom (0 : k)).toAlgebra
  letI : Algebra (Polynomial K) K := (Polynomial.evalRingHom (0 : K)).toAlgebra
  letI : IsScalarTower k (Polynomial K) K := zeroFiberIsScalarTower k K rfl
  let I : Ideal (Polynomial k) := Ideal.span {(Polynomial.X : Polynomial k) - Polynomial.C 0}
  let qEquiv : (Polynomial k ⧸ I) ≃ₐ[Polynomial k] k :=
    { __ := (Polynomial.quotientSpanXSubCAlgEquiv (0 : k)).toRingEquiv
      commutes' := by
        intro p
        change Polynomial.eval 0 p = Polynomial.evalRingHom (0 : k) p
        simp }
  let J : Ideal (Polynomial K) := I.map (algebraMap (Polynomial k) (Polynomial K))
  let e1 : (Polynomial K ⧸ J) ≃ₐ[Polynomial K]
      Polynomial K ⊗[Polynomial k] (Polynomial k ⧸ I) :=
    Algebra.TensorProduct.quotIdealMapEquivTensorQuot (Polynomial K) I
  have hJ : J = Ideal.span {(Polynomial.X : Polynomial K) - Polynomial.C 0} := by
    simp [J, I, Ideal.map_span, Polynomial.algebraMap_def]
  let rEq : (Polynomial K ⧸ J) ≃+* K :=
    (Ideal.quotEquivOfEq hJ).trans (Polynomial.quotientSpanXSubCAlgEquiv (0 : K)).toRingEquiv
  let eQ : (Polynomial K ⧸ J) ≃ₐ[Polynomial K] K :=
    AlgEquiv.ofRingEquiv (R := Polynomial K) (f := rEq) fun _ => rfl
  exact (Algebra.TensorProduct.congr
      (AlgEquiv.refl (R := Polynomial K) (A₁ := Polynomial K)) qEquiv).symm.trans
      (e1.symm.trans eQ) |>.restrictScalars k

/-- The punctured chart does not meet the fibre over the origin: the second summand of the
relation has empty base change to the origin of the base. -/
private lemma puncturedZeroPullbackIsEmpty :
    IsEmpty ↑(pullback ((puncturedCover K).ι ≫ coverMap k K)
      (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))))) := by
  let f := (puncturedCover K).ι ≫ coverMap k K
  let g := Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k)))
  let D : (base k).Opens := PrimeSpectrum.basicOpen (Polynomial.X : Polynomial k)
  have hpre : (coverMap k K) ⁻¹ᵁ D = puncturedCover K := by
    show (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k K)))) ⁻¹ᵁ
        PrimeSpectrum.basicOpen (Polynomial.X : Polynomial k) =
      PrimeSpectrum.basicOpen (Polynomial.X : Polynomial K)
    rw [AlgebraicGeometry.SpecMap_preimage_basicOpen]
    simp [Polynomial.map_X]
    rfl
  have hpre' : f ⁻¹ᵁ D = ⊤ := by
    show ((puncturedCover K).ι ≫ coverMap k K) ⁻¹ᵁ D = ⊤
    rw [Scheme.Hom.comp_preimage, hpre, (puncturedCover K).ι_preimage_self]
  have hf : Set.range f ⊆ D := by
    rintro x ⟨y, rfl⟩
    have hy : y ∈ f ⁻¹ᵁ D := by rw [hpre']; trivial
    rw [Scheme.Hom.mem_preimage] at hy
    exact hy
  have hg : g ⁻¹ᵁ D = ⊥ := by
    show (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k)))) ⁻¹ᵁ
      PrimeSpectrum.basicOpen (Polynomial.X : Polynomial k) = ⊥
    rw [AlgebraicGeometry.SpecMap_preimage_basicOpen]
    simp
    rfl
  refine Scheme.isEmpty_pullback f g (Set.disjoint_left.2 ?_)
  rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
  have hyD : y ∈ g ⁻¹ᵁ D := by
    rw [Scheme.Hom.mem_preimage, hy]
    exact hf ⟨x, rfl⟩
  simp [hg] at hyD

/-- The origin of the base, as a scheme over the base. -/
abbrev zeroBaseOverBase : Over (base k) :=
  Over.mk (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))))

/-- The origin of the chart, `Spec K`, as a scheme over the base. -/
abbrev zeroCoverOverBase : Over (base k) :=
  Over.mk (Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom (algebraMap k K) (0 : K))))

/-- The fibre of the chart over the origin of the base is `Spec K`. -/
private def zeroFiberSchemeIso :
    letI : Algebra (Polynomial k) (Polynomial K) := Polynomial.algebra k K
    letI : Algebra (Polynomial k) k := (Polynomial.evalRingHom (0 : k)).toAlgebra
    letI : Algebra (Polynomial K) K := (Polynomial.evalRingHom (0 : K)).toAlgebra
    letI : IsScalarTower k (Polynomial K) K := zeroFiberIsScalarTower k K rfl
    pullback (coverMap k K)
      (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k)))) ≅ Spec (.of K) := by
  letI : Algebra (Polynomial k) (Polynomial K) := Polynomial.algebra k K
  letI : Algebra (Polynomial k) k := (Polynomial.evalRingHom (0 : k)).toAlgebra
  letI : Algebra (Polynomial K) K := (Polynomial.evalRingHom (0 : K)).toAlgebra
  letI : IsScalarTower k (Polynomial K) K := zeroFiberIsScalarTower k K rfl
  let f := coverMap k K
  let g := Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k)))
  let f' := Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k) (Polynomial K)))
  let g' := Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k) k))
  have hf : f = f' := by
    change Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k K))) =
      Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k) (Polynomial K)))
    congr 1
  have hg : g = g' := rfl
  exact (pullback.congrHom hf hg).trans <|
    (pullbackSpecIso (Polynomial k) (Polynomial K) k).trans
      (Scheme.Spec.mapIso (zeroFiberTensorAlgEquiv k K).symm.toRingEquiv.toCommRingCatIso.op)

/-- The fibre of the chart over the origin of the base is the origin of the chart, as
schemes over the base. -/
private def zeroFiberOverIso :
    (coverOverBase k K ⨯ zeroBaseOverBase k) ≅ zeroCoverOverBase k K := by
  letI : Algebra (Polynomial k) (Polynomial K) := Polynomial.algebra k K
  letI : Algebra (Polynomial k) k := (Polynomial.evalRingHom (0 : k)).toAlgebra
  letI : Algebra (Polynomial K) K := (Polynomial.evalRingHom (0 : K)).toAlgebra
  letI : IsScalarTower k (Polynomial K) K := zeroFiberIsScalarTower k K rfl
  let Y := coverOverBase k K
  let Z := zeroBaseOverBase k
  let e₁ : (Y ⨯ Z).left ≅ pullback Y.hom Z.hom := Over.prodLeftIsoPullback Y Z
  let e₂ : pullback Y.hom Z.hom ≅ zeroCoverOverBase k K |>.left := zeroFiberSchemeIso k K
  let e : (Y ⨯ Z).left ≅ (zeroCoverOverBase k K).left := e₁.trans e₂
  have hmap :
      Spec.map (CommRingCat.ofHom (zeroFiberTensorAlgEquiv k K).symm.toRingEquiv.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom (algebraMap k K) (0 : K))) =
      Spec.map (CommRingCat.ofHom
        (algebraMap (Polynomial k) (Polynomial K ⊗[Polynomial k] k))) := by
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.Hom.ext
    apply Polynomial.ringHom_ext
    · intro a
      change (zeroFiberTensorAlgEquiv k K).symm.toRingEquiv.toRingHom
          (Polynomial.eval₂ (algebraMap k K) (0 : K) (Polynomial.C a)) =
        algebraMap (Polynomial k) (Polynomial K ⊗[Polynomial k] k) (Polynomial.C a)
      rw [Polynomial.eval₂_C]
      have hC : algebraMap (Polynomial k) (Polynomial K ⊗[Polynomial k] k) (Polynomial.C a) =
          algebraMap k (Polynomial K ⊗[Polynomial k] k) a := by
        simp [Polynomial.algebraMap_def]
      rw [hC]
      exact (zeroFiberTensorAlgEquiv k K).symm.commutes a
    · change (zeroFiberTensorAlgEquiv k K).symm.toRingEquiv.toRingHom
          (Polynomial.eval₂ (algebraMap k K) (0 : K) Polynomial.X) =
        algebraMap (Polynomial k) (Polynomial K ⊗[Polynomial k] k) Polynomial.X
      rw [Polynomial.eval₂_X]
      simp only [RingHom.map_zero]
      rw [Algebra.TensorProduct.algebraMap_def]
      simp only [RingHom.comp_apply]
      simp only [Polynomial.algebraMap_def]
      change (0 : Polynomial K ⊗[Polynomial k] k) =
        Algebra.TensorProduct.includeLeftRingHom
          ((Polynomial.mapRingHom (algebraMap k K)) Polynomial.X)
      change (0 : Polynomial K ⊗[Polynomial k] k) =
        (algebraMap (Polynomial k) (Polynomial K) Polynomial.X) ⊗ₜ[Polynomial k] 1
      rw [Algebra.TensorProduct.tmul_one_eq_one_tmul
        (R := Polynomial k) (A := Polynomial K) (B := k) (r := Polynomial.X)]
      change (0 : Polynomial K ⊗[Polynomial k] k) =
        1 ⊗ₜ[Polynomial k] Polynomial.eval (0 : k) Polynomial.X
      rw [Polynomial.eval_X]
      simp
  have hmap' :
      Scheme.Spec.map
          (((zeroFiberTensorAlgEquiv k K).symm.toRingEquiv.toCommRingCatIso.hom).op) ≫
        Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom (algebraMap k K) (0 : K))) =
      Spec.map (CommRingCat.ofHom
        (algebraMap (Polynomial k) (Polynomial K ⊗[Polynomial k] k))) := by
    change Spec.map (CommRingCat.ofHom
        (zeroFiberTensorAlgEquiv k K).symm.toRingEquiv.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom (algebraMap k K) (0 : K))) = _
    exact hmap
  exact Over.isoMk e (by
    dsimp only [e, e₁, e₂, zeroFiberSchemeIso, zeroCoverOverBase]
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, Category.assoc, Over.mk_hom]
    rw [← Category.assoc, hmap', pullbackSpecIso_hom_base]
    simp only [pullback.congrHom_hom, pullback.map, Category.assoc, pullback.lift_fst_assoc,
      Category.comp_id]
    change (Over.prodLeftIsoPullback Y Z).hom ≫ pullback.fst Y.hom Z.hom ≫ Y.hom = (Y ⨯ Z).hom
    rw [← Category.assoc, Over.prodLeftIsoPullback_hom_fst]
    exact Over.w (prod.fst (X := Y) (Y := Z)))

/-- Over the origin of the base the two projections of the relation agree: on the first
summand they are both the identity, and the second summand has empty base change. -/
private lemma zeroFiberRelationProjectionsEq (σ : K ≃ₐ[k] K) :
    pullback.fst (relationOverBase k K).hom (zeroBaseOverBase k).hom ≫
        (relationFirst k K).left =
      pullback.fst (relationOverBase k K).hom (zeroBaseOverBase k).hom ≫
        (relationSecond k K σ).left := by
  let U : Scheme.OpenCover.{u} (relationScheme K) :=
    coprodOpenCover.{u} (cover K) ((puncturedCover K).toScheme)
  let f := (relationOverBase k K).hom
  let g := (zeroBaseOverBase k).hom
  let V : Scheme.OpenCover.{u} (pullback f g) :=
    { I₀ := U.I₀
      X := fun i => pullback (U.f i ≫ f) g
      f := fun i => pullback.map (U.f i ≫ f) g f g (U.f i) (𝟙 _) (𝟙 _) (by simp) (by simp)
      mem₀ := (Scheme.Pullback.openCoverOfLeft U f g).mem₀ }
  apply V.hom_ext
  intro i
  change U.I₀ at i
  cases i with
  | inl p =>
    cases p
    have hU : U.f (Sum.inl PUnit.unit) = coprod.inl := rfl
    dsimp [V]
    rw [hU]
    have hmap :
        pullback.map (coprod.inl ≫ f) g f g coprod.inl (𝟙 _) (𝟙 _) (by simp) (by simp) ≫
          pullback.fst f g = pullback.fst (coprod.inl ≫ f) g ≫ coprod.inl := by
      dsimp [pullback.map]
      exact pullback.lift_fst _ _ _
    show
      (pullback.map (coprod.inl ≫ f) g f g coprod.inl (𝟙 _) (𝟙 _) (by simp) (by simp)) ≫
          pullback.fst f g ≫ (relationFirst k K).left =
        (pullback.map (coprod.inl ≫ f) g f g coprod.inl (𝟙 _) (𝟙 _) (by simp) (by simp)) ≫
          pullback.fst f g ≫ (relationSecond k K σ).left
    rw [← Category.assoc, hmap, ← Category.assoc, hmap]
    simp [Category.assoc, relationFirst_inl, relationSecond_inl]
  | inr p =>
    cases p
    have : IsEmpty ↑(V.X (Sum.inr PUnit.unit)) := by
      dsimp [V]
      show IsEmpty ↑(pullback
        ((coprod.inr : (puncturedCover K).toScheme ⟶ relationScheme K) ≫
            coprod.desc (coverMap k K) ((puncturedCover K).ι ≫ coverMap k K))
        (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k)))))
      rw [coprod.inr_desc]
      exact puncturedZeroPullbackIsEmpty (k := k) (K := K)
    apply Scheme.hom_ext_of_forall
    intro x
    exact isEmptyElim x

/-- After taking the product with the functor of points of the origin of the base, the
source and target maps of the twisted relation become equal. -/
private lemma zeroFiberRelationPointsMapsEq (σ : K ≃ₐ[k] K) (B : BigFppfSite.{u})
    (hS : B.Contains (base k)) (F : BigFppfOver B (base k) hS ⥤ Over (base k)) :
    let j := twistedRelation k K σ
    (prod.functor.obj (points F (zeroBaseOverBase k))).map (sourceMap F j) =
      (prod.functor.obj (points F (zeroBaseOverBase k))).map (targetMap F j) := by
  let Z := points F (zeroBaseOverBase k)
  let R := points F (relationOverBase k K)
  let j := twistedRelation k K σ
  show prod.map (𝟙 Z) (sourceMap F j) = prod.map (𝟙 Z) (targetMap F j)
  apply prod.hom_ext
  · rw [prod.map_fst, prod.map_fst]
  · ext X x
    let z := ((Limits.prod.fst : Z ⨯ R ⟶ Z).app X) x
    let r := ((Limits.prod.snd : Z ⨯ R ⟶ R).app X) x
    have hrel : (sourceMap F j).app X r = (targetMap F j).app X r := by
      apply Over.OverMorphism.ext
      let f := (relationOverBase k K).hom
      let g := (zeroBaseOverBase k).hom
      have hcompat : r.left ≫ f = z.left ≫ g := by rw [Over.w r, Over.w z]
      let q : (F.obj X.unop).left ⟶ pullback f g := pullback.lift r.left z.left hcompat
      have hpb := congrArg (fun t => q ≫ t) (zeroFiberRelationProjectionsEq (k := k) (K := K) σ)
      show (r ≫ j.source).left = (r ≫ j.target).left
      have hs : j.source = relationSecond k K σ := by simp [j]
      have ht : j.target = relationFirst k K := by simp [j]
      rw [hs, ht, Over.comp_left, Over.comp_left]
      show r.left ≫ (relationSecond k K σ).left = r.left ≫ (relationFirst k K).left
      calc
        r.left ≫ (relationSecond k K σ).left =
            (pullback.lift r.left z.left hcompat ≫ pullback.fst f g) ≫
              (relationSecond k K σ).left := by rw [pullback.lift_fst]
        _ = (pullback.lift r.left z.left hcompat ≫ pullback.fst f g) ≫
              (relationFirst k K).left := by simpa [q, f, g, Category.assoc] using hpb.symm
        _ = r.left ≫ (relationFirst k K).left := by rw [pullback.lift_fst]
    simpa [r] using hrel

/-- **Stacks 03FN.** Over the origin the punctured twisted diagonal disappears, so the fibre
of the quotient over the origin of the base is the origin of the chart, `Spec K`. -/
@[stacks 03FN "zero_fibre"]
theorem twistedRelationQuotient_zeroFibre (σ : K ≃ₐ[k] K) (B : BigFppfSite.{u})
    (hS : B.Contains (base k))
    [HasSheafify (BigFppfOver.topology B (base k) hS) (Type u)] :
    let C := BigFppfOver B (base k) hS
    let F : C ⥤ Over (base k) := Over.post B.inclusion
    let Q : Cᵒᵖ ⥤ Type u :=
      (quotientSheaf (BigFppfOver.topology B (base k) hS) F (twistedRelation k K σ)).obj
    Nonempty ((Q ⨯ points F (zeroBaseOverBase k)) ≅ points F (zeroCoverOverBase k K)) := by
  let C := BigFppfOver B (base k) hS
  let F : C ⥤ Over (base k) := Over.post B.inclusion
  let J := BigFppfOver.topology B (base k) hS
  let j := twistedRelation k K σ
  let R := points F (relationOverBase k K)
  let U := points F (coverOverBase k K)
  let Z := points F (zeroBaseOverBase k)
  let f := sourceMap F j
  let g := targetMap F j
  let equot :
      (((presheafToSheaf J (Type u)).obj (coequalizer f g)).obj ⨯
        ((presheafToSheaf J (Type u)).obj Z).obj) ≅
      ((presheafToSheaf J (Type u)).obj (Z ⨯ U)).obj :=
    sheafifyProductCoequalizerIso (C := C) (J := J) (P := R) (U := U) f g Z
      (zeroFiberRelationPointsMapsEq (k := k) (K := K) σ B hS F)
  let Z₀ := zeroBaseOverBase k
  let U₀ := coverOverBase k K
  let T := Z₀ ⨯ U₀
  let epoints := pointsProductIso (C := C) (S := base k) F Z₀ U₀
  have hT : Presheaf.IsSheaf J (points F T) :=
    BigFppfOver.isSheaf_post_inclusion_op_comp_yoneda_obj B (base k) hS T
  have hZU : Presheaf.IsSheaf J (Z ⨯ U) := (Presheaf.isSheaf_of_iso_iff epoints).2 hT
  let esheaf := (CategoryTheory.isoSheafify J hZU).symm
  let eOver : (Z₀ ⨯ U₀) ≅ zeroCoverOverBase k K :=
    (prod.braiding Z₀ U₀).trans (zeroFiberOverIso k K)
  let W : ((Over (base k))ᵒᵖ ⥤ Type u) ⥤ (Cᵒᵖ ⥤ Type u) :=
    (Functor.whiskeringLeft Cᵒᵖ (Over (base k))ᵒᵖ (Type u)).obj F.op
  have hZ : Presheaf.IsSheaf J Z :=
    BigFppfOver.isSheaf_post_inclusion_op_comp_yoneda_obj B (base k) hS Z₀
  let eZ := CategoryTheory.isoSheafify J hZ
  exact ⟨(prod.mapIso (Iso.refl _) eZ).trans (equot.trans (esheaf.trans
    (epoints.trans (W.mapIso (yoneda.mapIso eOver)))))⟩

end AlgebraicGeometry.TwistedDoubledOrigin

end
