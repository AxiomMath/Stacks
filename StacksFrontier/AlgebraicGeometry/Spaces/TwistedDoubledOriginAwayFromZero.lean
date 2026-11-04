module

public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteLocalSurjectivity
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedDoubledOriginSelfProduct

/-!
# The twisted doubled origin away from the origin

The first assertion of the example is that the quotient `X = U/R` agrees with the base
`S = Spec k[x]` away from the origin of `S`.  Away from the origin the twisted diagonal is
present in full, so the relation is all of `U ×_S U` there and the quotient of `U` by it is
`S` itself.

This file states that in the form that the base change of the structure morphism
`X ⟶ S` to the punctured base is an isomorphism, and proves it.

## Main definitions

* `AlgebraicGeometry.TwistedDoubledOrigin.quotientBaseMap` is the structure morphism of the
  quotient sheaf to the functor of points of the base.
* `AlgebraicGeometry.TwistedDoubledOrigin.coverPuncturedOverBase`,
  `AlgebraicGeometry.TwistedDoubledOrigin.coverPuncturedMap`,
  `AlgebraicGeometry.TwistedDoubledOrigin.coverPuncturedInclusion` and
  `AlgebraicGeometry.TwistedDoubledOrigin.coverPuncturedToBase` are the punctured chart over
  the base, its map to the punctured base, and its two structural morphisms.

## Main results

* `AlgebraicGeometry.TwistedDoubledOrigin`
  `.isIso_quadraticGaloisTwistedDoubledOrigin_over_puncturedBase`: the base change of the
  structure morphism of the quotient to the punctured base is an isomorphism.
* `AlgebraicGeometry.TwistedDoubledOrigin.exists_relation_of_punctured`: two points of the
  chart which agree over the base and whose second one lands in the puncture are related by
  the twisted relation.  This is the geometric content of the assertion.
* `AlgebraicGeometry.TwistedDoubledOrigin.coverMap_fppf` and
  `AlgebraicGeometry.TwistedDoubledOrigin.coverPuncturedMap_fppf`: the chart and the
  punctured chart are flat, surjective and locally of finite presentation over the base and
  over the punctured base respectively, so they are fppf coverings.

## Implementation notes

A morphism of presheaves on the big fppf site of `S` with locally subsingleton target is an
isomorphism as soon as, locally, the source is inhabited and any two of its sections agree;
`isIso_pullback_snd_of_locally_inhabited` is that criterion, and the two hypotheses it needs
are supplied by local surjectivity of the punctured chart onto the punctured base
(`coverPuncturedMap_fppf` through `AlgebraicGeometry.Space.points_locallySurjective`) and by
`exists_relation_of_punctured`.

That the relation is everything over the punctured base is read off the splitting
`U ×_S U ≅ U ⨿ U` of `TwistedDoubledOriginSelfProduct`: restricting both summands to the
puncture, the relation scheme `U ⨿ (U ∖ {0})` covers the restriction of `U ×_S U`, which is
`kernelSource_punctured_isPullback`.  The comparison between the graph of the Galois
automorphism restricted to the puncture and the pullback of that automorphism along the
puncture is an isomorphism because the automorphism is one.

## References

* [Stacks Project, Tag 03FN](https://stacks.math.columbia.edu/tag/03FN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe u v w

namespace AlgebraicGeometry.TwistedDoubledOrigin

attribute [local instance] Polynomial.algebra

/-! ### Two general criteria on presheaves -/

/-- A morphism of presheaves on a site is an isomorphism when its target is objectwise
subsingleton, the source is a sheaf, and a locally surjective map into the base presheaf
witnesses that the fibres of the source are inhabited and subsingleton. -/
private theorem isIso_pullback_snd_of_locally_inhabited {C : Type v} [Category.{w} C]
    (J : GrothendieckTopology C) {U Q M N : Cᵒᵖ ⥤ Type u} (f : Q ⟶ M) (g : N ⟶ M)
    (a : U ⟶ Q) (p : U ⟶ N) (hQ : Presheaf.IsSheaf J Q)
    [Presheaf.IsLocallySurjective J p] (hM : ∀ T, Subsingleton (M.obj T))
    (huniq : ∀ T, N.obj T → Subsingleton (Q.obj T)) : IsIso (pullback.snd f g) := by
  have hne (T : Cᵒᵖ) (n : N.obj T) : Nonempty (Q.obj T) := by
    let S := Presheaf.imageSieve p n
    have hS : S ∈ J T.unop := Presheaf.imageSieve_mem J p n
    let t : Presieve.FamilyOfElements Q S.arrows :=
      fun Y b hb => a.app (op Y) (Presheaf.localPreimage p n b hb)
    have ht : t.Compatible := by
      intro Y₁ Y₂ W g₁ g₂ f₁ f₂ hf₁ hf₂ heq
      exact (huniq (op W) (N.map (g₁ ≫ f₁).op n)).elim _ _
    exact ⟨((isSheaf_iff_isSheaf_of_type J Q).mp hQ _ hS).amalgamate t ht⟩
  rw [NatTrans.isIso_iff_isIso_app]
  intro T
  rw [isIso_iff_bijective]
  have hp := (IsPullback.of_hasPullback f g).map ((evaluation Cᵒᵖ (Type u)).obj T)
  refine ⟨fun x y hxy => ?_, fun n => ?_⟩
  · exact Types.ext_of_isPullback hp ((huniq T ((pullback.snd f g).app T x)).elim _ _) hxy
  · obtain ⟨q⟩ := hne T n
    obtain ⟨x, -, hn⟩ := Types.exists_of_isPullback hp q n ((hM T).elim _ _)
    exact ⟨x, hn⟩

/-- If a locally surjective map into a sheaf identifies all the sections it hits whenever a
section of a further presheaf is given, then the sheaf is subsingleton wherever that further
presheaf has a section. -/
private theorem subsingleton_of_locallySurjective {C : Type v} [Category.{w} C]
    (J : GrothendieckTopology C) {U Q N : Cᵒᵖ ⥤ Type u} (q : U ⟶ Q)
    (hQ : Presheaf.IsSheaf J Q) [Presheaf.IsLocallySurjective J q]
    (heq : ∀ T, N.obj T → ∀ x y, q.app T x = q.app T y) (T : Cᵒᵖ) (n : N.obj T) :
    Subsingleton (Q.obj T) := by
  refine ⟨fun x y => ?_⟩
  let S := Presheaf.imageSieve q x ⊓ Presheaf.imageSieve q y
  have hS : S ∈ J T.unop := J.intersection_covering
    (Presheaf.imageSieve_mem J q x) (Presheaf.imageSieve_mem J q y)
  apply (((isSheaf_iff_isSheaf_of_type J Q).mp hQ).isSeparated _ hS).ext
  rintro V f ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  exact ha.symm.trans ((heq (op V) (N.map f.op n) a b).trans hb)

/-- A binary coproduct of base changes along a common morphism is the base change of the
binary coproduct, because schemes are finitarily preextensive. -/
theorem coproductPullback_isPullback {Y Z : Scheme.{u}} (X : Bool → Scheme.{u})
    (f : (i : Bool) → X i ⟶ Y) (g : Z ⟶ Y) :
    IsPullback
      (coprod.desc (pullback.fst (f true) g ≫ coprod.inl)
        (pullback.fst (f false) g ≫ coprod.inr))
      (coprod.desc (pullback.snd (f true) g) (pullback.snd (f false) g))
      (coprod.desc (f true) (f false)) g := by
  let a : Cofan X := Cofan.mk (X true ⨿ X false) (fun
    | true => coprod.inl
    | false => coprod.inr)
  let F : (i : Bool) → Scheme := fun i => pullback (f i) g
  let q₁ : (i : Bool) → F i ⟶ X i := fun i => pullback.fst (f i) g
  let q₂ : (i : Bool) → F i ⟶ Z := fun i => pullback.snd (f i) g
  let d : Cofan F := Cofan.mk (F true ⨿ F false) (fun
    | true => coprod.inl
    | false => coprod.inr)
  have colimit (W : Bool → Scheme.{u}) :
      IsColimit (Cofan.mk (W true ⨿ W false) (fun
        | true => coprod.inl
        | false => coprod.inr)) := by
    refine Cofan.IsColimit.mk _ (fun s => coprod.desc (s.inj true) (s.inj false)) ?_ ?_
    · intro s i
      cases i
      · exact coprod.inr_desc _ _
      · exact coprod.inl_desc _ _
    · intro s m hm
      apply coprod.hom_ext
      · exact (hm true).trans (coprod.inl_desc _ _).symm
      · exact (hm false).trans (coprod.inr_desc _ _).symm
  have hau : IsUniversalColimit a :=
    FinitaryPreExtensive.isUniversal_finiteCoproducts (colimit X)
  have hd : IsColimit d := colimit F
  have hP (i : Bool) : IsPullback (q₁ i) (q₂ i) (f i) g := IsPullback.of_hasPullback _ _
  have hh := hau.isPullback_of_isColimit_right
    (f := f) (u := coprod.desc (f true) (f false)) (v := g)
    (q₁ := q₁) (q₂ := q₂) hP hd (by
      intro i
      cases i
      · exact coprod.inr_desc _ _
      · exact coprod.inl_desc _ _)
  have hdesc {W : Scheme.{u}} (g : (i : Bool) → F i ⟶ W) :
      Cofan.IsColimit.desc hd g = coprod.desc (g true) (g false) := by
    apply coprod.hom_ext
    · rw [coprod.inl_desc]
      simpa [d] using Cofan.IsColimit.fac hd g true
    · rw [coprod.inr_desc]
      simpa [d] using Cofan.IsColimit.fac hd g false
  rw [hdesc (fun i => q₁ i ≫ a.inj i), hdesc q₂] at hh
  simpa [d, a, F, q₁, q₂, Category.assoc, coprod.desc_comp] using hh

/-! ### The punctured chart -/

variable (k K : Type u) [Field k] [Field K] [Algebra k K]

/-- The structure morphism from the quotient sheaf to the functor of points of the base. -/
def quotientBaseMap [FiniteDimensional k K] [IsGalois k K]
    (hdegree : Module.finrank k K = 2) (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1)
    (B : BigFppfSite.{u}) (hS : B.Contains (base k))
    [HasSheafify (BigFppfOver.topology B (base k) hS) (Type u)] :
    (quadraticGaloisTwistedDoubledOrigin k K hdegree σ hσ B hS).obj ⟶
      Stacks.Groupoids.points (Over.post (X := B.obj hS) B.inclusion) (baseOverBase k) where
  app := fun T => TypeCat.ofHom fun _ =>
    (Over.mkIdTerminal (X := base k)).from
      ((Over.post (X := B.obj hS) B.inclusion).obj (Opposite.unop T))
  naturality := by
    intro X Y f
    ext x
    exact (Over.mkIdTerminal (X := base k)).hom_ext _ _

/-- The graph of the Galois automorphism restricted to the puncture has the restricted
automorphism as its first projection composed with itself. -/
theorem puncturedGaloisGraph_fst_comp (σ : K ≃ₐ[k] K) :
    pullback.fst ((puncturedCover K).ι ≫ galoisAction k K σ) (puncturedCover K).ι ≫
        galoisActionPuncturedMap k K σ =
      pullback.snd ((puncturedCover K).ι ≫ galoisAction k K σ) (puncturedCover K).ι := by
  apply (cancel_mono (puncturedCover K).ι).1
  calc
    pullback.fst ((puncturedCover K).ι ≫ galoisAction k K σ) (puncturedCover K).ι ≫
        galoisActionPuncturedMap k K σ ≫ (puncturedCover K).ι =
        pullback.fst ((puncturedCover K).ι ≫ galoisAction k K σ) (puncturedCover K).ι ≫
          (puncturedCover K).ι ≫ galoisAction k K σ := by rw [galoisActionPuncturedMap_ι]
    _ = pullback.snd ((puncturedCover K).ι ≫ galoisAction k K σ) (puncturedCover K).ι ≫
        (puncturedCover K).ι := pullback.condition

/-- The graph of the Galois automorphism over the puncture is the puncture itself. -/
private def puncturedGaloisGraphPullbackIso (σ : K ≃ₐ[k] K) :
    (pullback ((puncturedCover K).ι ≫ galoisAction k K σ) (puncturedCover K).ι) ≅
      (puncturedCover K).toScheme := by
  let τ := galoisActionPuncturedMap k K σ
  let e : (puncturedCover K).toScheme ⟶
      pullback ((puncturedCover K).ι ≫ galoisAction k K σ) (puncturedCover K).ι :=
    pullback.lift (𝟙 _) τ (by simpa [τ] using (galoisActionPuncturedMap_ι k K σ).symm)
  have hfst : e ≫ pullback.fst ((puncturedCover K).ι ≫ galoisAction k K σ)
      (puncturedCover K).ι = 𝟙 _ :=
    pullback.lift_fst _ _ _
  refine ⟨pullback.fst ((puncturedCover K).ι ≫ galoisAction k K σ) (puncturedCover K).ι,
    e, ?_, hfst⟩
  apply pullback.hom_ext
  · simp only [Category.assoc, hfst, Category.comp_id, Category.id_comp]
  · simpa only [Category.assoc, e, pullback.lift_snd, Category.id_comp, τ] using
    puncturedGaloisGraph_fst_comp k K σ

/-- The comparison from the graph of the Galois automorphism restricted to the puncture to
the base change of that automorphism along the puncture. -/
private def puncturedGraphPullbackComparison (σ : K ≃ₐ[k] K) :
    pullback ((puncturedCover K).ι ≫ galoisAction k K σ) (puncturedCover K).ι ⟶
      pullback (galoisAction k K σ) (puncturedCover K).ι :=
  pullback.lift
    (pullback.fst ((puncturedCover K).ι ≫ galoisAction k K σ) (puncturedCover K).ι ≫
      (puncturedCover K).ι)
    (pullback.snd ((puncturedCover K).ι ≫ galoisAction k K σ) (puncturedCover K).ι)
    ((Category.assoc _ _ _).trans pullback.condition)

private instance isIso_puncturedGraphPullbackComparison (σ : K ≃ₐ[k] K) :
    IsIso (puncturedGraphPullbackComparison k K σ) := by
  let s := pullback.snd (galoisAction k K σ) (puncturedCover K).ι
  have : IsIso s := (IsPullback.of_hasPullback (galoisAction k K σ)
    (puncturedCover K).ι).isIso_snd_of_isIso inferInstance
  have h : puncturedGraphPullbackComparison k K σ ≫ s =
      pullback.fst ((puncturedCover K).ι ≫ galoisAction k K σ) (puncturedCover K).ι ≫
        galoisActionPuncturedMap k K σ :=
    (pullback.lift_snd _ _ _).trans (puncturedGaloisGraph_fst_comp k K σ).symm
  have : IsIso (puncturedGraphPullbackComparison k K σ ≫ s) := by
    rw [h]
    have : IsIso (pullback.fst ((puncturedCover K).ι ≫ galoisAction k K σ)
      (puncturedCover K).ι) := (puncturedGaloisGraphPullbackIso k K σ).isIso_hom
    infer_instance
  exact IsIso.of_isIso_comp_right _ s

/-- A point of the chart whose image in the base lands in the puncture factors through the
puncture of the chart. -/
def factorThroughPuncturedCover {T : Scheme.{u}} (f : T ⟶ cover K)
    (a : T ⟶ (puncturedBase k).toScheme) (h : f ≫ coverMap k K = a ≫ (puncturedBase k).ι) :
    T ⟶ (puncturedCover K).toScheme :=
  T.topIso.inv ≫ f.resLE (puncturedCover K) ⊤ (by
    rw [← coverMap_preimage_puncturedBase k K, ← Scheme.Hom.comp_preimage, h]
    simp)

/-- The factorization `factorThroughPuncturedCover` composed with the inclusion of the puncture
of the chart recovers the original point. -/
@[simp]
theorem factorThroughPuncturedCover_ι {T : Scheme.{u}} (f : T ⟶ cover K)
    (a : T ⟶ (puncturedBase k).toScheme) (h : f ≫ coverMap k K = a ≫ (puncturedBase k).ι) :
    factorThroughPuncturedCover k K f a h ≫ (puncturedCover K).ι = f := by
  simp [factorThroughPuncturedCover, Scheme.Hom.resLE_comp_ι]

/-- The restriction of the map of affine lines to the punctures. -/
def coverPuncturedMap : (puncturedCover K).toScheme ⟶ (puncturedBase k).toScheme :=
  ((cover K).isoOfEq (coverMap_preimage_puncturedBase k K)).inv ≫
    morphismRestrict (coverMap k K) (puncturedBase k)

/-- The punctured chart regarded as a scheme over the base. -/
abbrev coverPuncturedOverBase : Over (base k) :=
  Over.mk ((puncturedCover K).ι ≫ coverMap k K)

/-- The inclusion of the punctured chart into the chart, over the base. -/
def coverPuncturedInclusion : coverPuncturedOverBase k K ⟶ coverOverBase k K :=
  Over.homMk (puncturedCover K).ι (by simp [coverPuncturedOverBase, coverOverBase])

/-- The punctured chart as a scheme over the punctured base. -/
def coverPuncturedToBase : coverPuncturedOverBase k K ⟶ puncturedBaseOverBase k :=
  Over.homMk (coverPuncturedMap k K) (by
    change ((cover K).isoOfEq (coverMap_preimage_puncturedBase k K)).inv ≫
      morphismRestrict (coverMap k K) (puncturedBase k) ≫ (puncturedBase k).ι = _
    rw [morphismRestrict_ι]
    exact congrArg (fun f => f ≫ coverMap k K)
      (Scheme.isoOfEq_inv_ι (cover K) (coverMap_preimage_puncturedBase k K)))

/-! ### The relation is everything over the punctured base -/

variable [FiniteDimensional k K] [IsGalois k K]

/-- Restricted to the puncture, the second projection of the self-product of the chart is
covered by the two summands of the relation scheme. -/
private theorem kernelSource_punctured_isPullback (hdegree : Module.finrank k K = 2)
    (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1) :
    IsPullback
      (coprod.desc
        (pullback.fst (𝟙 (cover K)) (puncturedCover K).ι ≫ coprod.inl ≫
          (coverFiberProductSplitIso k K hdegree σ hσ).inv)
        (pullback.fst (galoisAction k K σ) (puncturedCover K).ι ≫ coprod.inr ≫
          (coverFiberProductSplitIso k K hdegree σ hσ).inv))
      (coprod.desc (pullback.snd (𝟙 (cover K)) (puncturedCover K).ι)
        (pullback.snd (galoisAction k K σ) (puncturedCover K).ι))
      (pullback.snd (coverMap k K) (coverMap k K)) (puncturedCover K).ι := by
  let e := coverFiberProductSplitIso k K hdegree σ hσ
  let f : Bool → Scheme := fun _ => cover K
  let p : (i : Bool) → f i ⟶ cover K := fun
    | true => 𝟙 (cover K)
    | false => galoisAction k K σ
  let hcoprod := coproductPullback_isPullback f p (puncturedCover K).ι
  let top' : (pullback (𝟙 (cover K)) (puncturedCover K).ι ⨿
      pullback (galoisAction k K σ) (puncturedCover K).ι) ⟶
      pullback (coverMap k K) (coverMap k K) :=
    coprod.desc (pullback.fst (𝟙 (cover K)) (puncturedCover K).ι ≫ coprod.inl ≫ e.inv)
      (pullback.fst (galoisAction k K σ) (puncturedCover K).ι ≫ coprod.inr ≫ e.inv)
  let bottom : (pullback (𝟙 (cover K)) (puncturedCover K).ι ⨿
      pullback (galoisAction k K σ) (puncturedCover K).ι) ⟶ (puncturedCover K).toScheme :=
    coprod.desc (pullback.snd (𝟙 (cover K)) (puncturedCover K).ι)
      (pullback.snd (galoisAction k K σ) (puncturedCover K).ι)
  have heq : coprod.desc (𝟙 (cover K)) (galoisAction k K σ) =
      e.inv ≫ pullback.snd (coverMap k K) (coverMap k K) := by
    rw [← coverFiberProductSplitIso_second_factor k K hdegree σ hσ]
  have h := hcoprod.of_iso (e₁ := Iso.refl _) (e₂ := e.symm) (e₃ := Iso.refl _)
    (e₄ := Iso.refl _) (fst' := top') (snd' := bottom)
    (f' := pullback.snd (coverMap k K) (coverMap k K)) (g' := (puncturedCover K).ι)
    (by
      show coprod.desc (pullback.fst (𝟙 (cover K)) (puncturedCover K).ι ≫ coprod.inl)
          (pullback.fst (galoisAction k K σ) (puncturedCover K).ι ≫ coprod.inr) ≫ e.inv = _
      rw [coprod.desc_comp]
      rfl)
    (by
      show coprod.desc (pullback.snd (𝟙 (cover K)) (puncturedCover K).ι)
        (pullback.snd (galoisAction k K σ) (puncturedCover K).ι) = _
      rfl)
    (by simpa using heq) rfl
  simpa [top', bottom, e, f, p, hcoprod, Category.assoc, coprod.desc_comp] using h

/-- **Stacks 03FN.** Two points of the chart which agree over the base and whose second one
factors through the puncture are related by the twisted relation. -/
theorem exists_relation_of_punctured (hdegree : Module.finrank k K = 2) (σ : K ≃ₐ[k] K)
    (hσ : σ ≠ 1) {T : Scheme.{u}} (a b : T ⟶ cover K) (c : T ⟶ (puncturedCover K).toScheme)
    (h : a ≫ coverMap k K = b ≫ coverMap k K) (hc : b = c ≫ (puncturedCover K).ι) :
    ∃ r : T ⟶ relationScheme K,
      r ≫ (relationFirst k K).left = a ∧ r ≫ (relationSecond k K σ).left = b := by
  let i := (puncturedCover K).ι
  let τ := galoisAction k K σ
  let e := coverFiberProductSplitIso k K hdegree σ hσ
  let A := pullback (𝟙 (cover K)) i
  let D := pullback (i ≫ τ) i
  let E := pullback τ i
  let v : A ⨿ D ⟶ A ⨿ E := coprod.map (𝟙 A) (puncturedGraphPullbackComparison k K σ)
  have : IsIso v := by
    dsimp [v]
    infer_instance
  let r₀ : A ⨿ D ⟶ relationScheme K := coprod.desc
    (pullback.fst (𝟙 (cover K)) i ≫ coprod.inl) (pullback.fst (i ≫ τ) i ≫ coprod.inr)
  let z : A ⨿ E ⟶ pullback (coverMap k K) (coverMap k K) := coprod.desc
    (pullback.fst (𝟙 (cover K)) i ≫ coprod.inl ≫ e.inv)
    (pullback.fst τ i ≫ coprod.inr ≫ e.inv)
  have he₁ : coprod.inl ≫ e.inv ≫ pullback.fst (coverMap k K) (coverMap k K) =
      𝟙 (cover K) := by
    rw [← Category.assoc, coverFiberProductSplitIso_inl, pullback.diagonal_fst]
  have he₂ : coprod.inl ≫ e.inv ≫ pullback.snd (coverMap k K) (coverMap k K) =
      𝟙 (cover K) := by
    rw [← Category.assoc, coverFiberProductSplitIso_inl, pullback.diagonal_snd]
  have hz₁ : r₀ ≫ (relationFirst k K).left =
      v ≫ z ≫ pullback.fst (coverMap k K) (coverMap k K) := by
    apply coprod.hom_ext
    · simp only [r₀, v, z, Category.assoc, coprod.inl_desc_assoc, coprod.inl_map_assoc,
        Category.id_comp, he₁, relationFirst_inl, Category.comp_id]
    · simp only [r₀, v, z, Category.assoc, coprod.inr_desc_assoc, coprod.inr_map_assoc,
        relationFirst_inr,
        show coprod.inr ≫ e.inv ≫ pullback.fst (coverMap k K) (coverMap k K) = 𝟙 _ from
          coverFiberProductSplitIso_inr_fst k K hdegree σ hσ, Category.comp_id]
      exact (pullback.lift_fst _ _ _).symm
  have hz₂ : r₀ ≫ (relationSecond k K σ).left =
      v ≫ z ≫ pullback.snd (coverMap k K) (coverMap k K) := by
    apply coprod.hom_ext
    · simp only [r₀, v, z, Category.assoc, coprod.inl_desc_assoc, coprod.inl_map_assoc,
        Category.id_comp, he₂, relationSecond_inl, Category.comp_id]
    · simp only [r₀, v, z, Category.assoc, coprod.inr_desc_assoc, coprod.inr_map_assoc,
        relationSecond_inr,
        show coprod.inr ≫ e.inv ≫ pullback.snd (coverMap k K) (coverMap k K) = τ from
          coverFiberProductSplitIso_inr_snd k K hdegree σ hσ]
      conv_rhs => rw [← Category.assoc, show puncturedGraphPullbackComparison k K σ ≫
        pullback.fst τ i = pullback.fst (i ≫ τ) i ≫ i from pullback.lift_fst _ _ _]
      rfl
  let hp := kernelSource_punctured_isPullback k K hdegree σ hσ
  let l := hp.lift (pullback.lift a b h) c ((pullback.lift_snd _ _ _).trans hc)
  have hl : l ≫ z = pullback.lift a b h := hp.lift_fst _ _ _
  refine ⟨l ≫ inv v ≫ r₀, ?_, ?_⟩
  · simp only [Category.assoc, hz₁]
    rw [IsIso.inv_hom_id_assoc, ← Category.assoc, hl, pullback.lift_fst]
  · simp only [Category.assoc, hz₂]
    rw [IsIso.inv_hom_id_assoc, ← Category.assoc, hl, pullback.lift_snd]

/-! ### The chart is an fppf covering of the base -/

/-- The chart is flat, surjective and locally of finite presentation over the base. -/
theorem coverMap_fppf :
    Flat (coverMap k K) ∧ LocallyOfFinitePresentation (coverMap k K) ∧
      Surjective (coverMap k K) := by
  have : Algebra.FinitePresentation k K :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Module.FaithfullyFlat (Polynomial k) (Polynomial K) :=
    Module.FaithfullyFlat.of_linearEquiv _ _ (polynomialCoefficientEquiv k K).toLinearEquiv
  have hf : Flat (coverMap k K) ∧ Surjective (coverMap k K) := by
    rw [coverMap, flat_and_surjective_SpecMap_iff]
    show (algebraMap (Polynomial k) (Polynomial K)).FaithfullyFlat
    exact RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance
  refine ⟨hf.1, ?_, hf.2⟩
  rw [coverMap, HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
  show (algebraMap (Polynomial k) (Polynomial K)).FinitePresentation
  exact RingHom.finitePresentation_algebraMap.mpr
    (Algebra.FinitePresentation.equiv (polynomialCoefficientEquiv k K).symm)

/-- The punctured chart is flat, surjective and locally of finite presentation over the
punctured base. -/
theorem coverPuncturedMap_fppf :
    Flat (coverPuncturedMap k K) ∧ LocallyOfFinitePresentation (coverPuncturedMap k K) ∧
      Surjective (coverPuncturedMap k K) := by
  obtain ⟨hf, hfp, hs⟩ := coverMap_fppf k K
  have : Surjective (morphismRestrict (coverMap k K) (puncturedBase k)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Surjective)
      (isPullback_morphismRestrict (coverMap k K) (puncturedBase k)).flip hs
  dsimp [coverPuncturedMap]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- The punctured chart is locally surjective onto the punctured base on functors of
points. -/
theorem puncturedCover_points_locallySurjective (B : BigFppfSite.{u})
    (hS : B.Contains (base k)) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B (base k) hS)
      ((Over.post (X := B.obj hS) B.inclusion).op.whiskerLeft
        (yoneda.map (coverPuncturedToBase k K))) := by
  have hfp : LocallyOfFinitePresentation (coverMap k K) := (coverMap_fppf k K).2.1
  have hU : B.Contains (cover K) :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact (coverMap k K) hS
  have hU' : B.Contains (puncturedCover K).toScheme :=
    Scheme.size_lt_of_isOpenImmersion (puncturedCover K).ι hU
  have hS' : B.Contains (puncturedBase k).toScheme :=
    Scheme.size_lt_of_isOpenImmersion (puncturedBase k).ι hS
  let X : BigFppfOver B (base k) hS :=
    Over.mk (⟨(coverPuncturedOverBase k K).hom⟩ : B.obj hU' ⟶ B.obj hS)
  let Y : BigFppfOver B (base k) hS :=
    Over.mk (⟨(puncturedBaseOverBase k).hom⟩ : B.obj hS' ⟶ B.obj hS)
  let f : X ⟶ Y := Over.homMk
    (⟨(coverPuncturedToBase k K).left⟩ : X.left ⟶ Y.left) (by
      apply ObjectProperty.hom_ext
      exact (coverPuncturedToBase k K).w)
  exact Space.points_locallySurjective B hS f (coverPuncturedMap_fppf k K)

/-- Over the punctured base the quotient sheaf has at most one section. -/
private theorem quotient_sections_subsingleton_of_punctured
    (hdegree : Module.finrank k K = 2) (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1) (B : BigFppfSite.{u})
    (hS : B.Contains (base k))
    [HasSheafify (BigFppfOver.topology B (base k) hS) (Type u)]
    (T : (BigFppfOver B (base k) hS)ᵒᵖ)
    (n : (Stacks.Groupoids.points (Over.post (X := B.obj hS) B.inclusion)
      (puncturedBaseOverBase k)).obj T) :
    Subsingleton ((quadraticGaloisTwistedDoubledOrigin k K hdegree σ hσ B hS).obj.obj T) := by
  let J := BigFppfOver.topology B (base k) hS
  let F := Over.post (X := B.obj hS) B.inclusion
  let j := twistedRelation k K σ
  have := Stacks.Groupoids.toQuotientSheaf_isLocallySurjective J F j
  apply subsingleton_of_locallySurjective J (Stacks.Groupoids.toQuotientSheaf J F j)
    (Stacks.Groupoids.quotientSheaf J F j).property
    (N := Stacks.Groupoids.points F (puncturedBaseOverBase k)) _ T n
  intro V m a b
  have hb : b.left ≫ coverMap k K = m.left ≫ (puncturedBase k).ι := b.w.trans m.w.symm
  let c := factorThroughPuncturedCover k K b.left m.left hb
  obtain ⟨r, hr₁, hr₂⟩ := exists_relation_of_punctured k K hdegree σ hσ a.left b.left c
    (a.w.trans b.w.symm) (factorThroughPuncturedCover_ι k K b.left m.left hb).symm
  let rr : F.obj V.unop ⟶ relationOverBase k K := Over.homMk r (by
    rw [← (relationFirst k K).w, ← Category.assoc, hr₁]
    exact a.w)
  have h₁ : rr ≫ j.target = a := by
    apply Over.OverMorphism.ext
    simpa [j, rr] using hr₁
  have h₂ : rr ≫ j.source = b := by
    apply Over.OverMorphism.ext
    simpa [j, rr] using hr₂
  have h := ConcreteCategory.congr_hom
    (congr_app (Stacks.Groupoids.sourceMap_toQuotientSheaf J F j) V) rr
  change (Stacks.Groupoids.toQuotientSheaf J F j).app V (rr ≫ j.source) =
    (Stacks.Groupoids.toQuotientSheaf J F j).app V (rr ≫ j.target) at h
  rw [h₁, h₂] at h
  exact h.symm

/-- **Stacks 03FN.** The quotient `X = U/R` agrees with the base away from the origin: the
base change of its structure morphism to the punctured base is an isomorphism. -/
@[stacks 03FN "away_from_zero"]
theorem isIso_quadraticGaloisTwistedDoubledOrigin_over_puncturedBase
    (hdegree : Module.finrank k K = 2) (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1) (B : BigFppfSite.{u})
    (hS : B.Contains (base k))
    [HasSheafify (BigFppfOver.topology B (base k) hS) (Type u)] :
    IsIso (pullback.snd (quotientBaseMap k K hdegree σ hσ B hS)
      ((Over.post (X := B.obj hS) B.inclusion).op.whiskerLeft
        (yoneda.map (puncturedBaseInclusion k)))) := by
  let J := BigFppfOver.topology B (base k) hS
  let F := Over.post (X := B.obj hS) B.inclusion
  let j := twistedRelation k K σ
  let q := Stacks.Groupoids.toQuotientSheaf J F j
  let p := F.op.whiskerLeft (yoneda.map (coverPuncturedToBase k K))
  have : Presheaf.IsLocallySurjective J p := puncturedCover_points_locallySurjective k K B hS
  apply isIso_pullback_snd_of_locally_inhabited J (quotientBaseMap k K hdegree σ hσ B hS)
    (F.op.whiskerLeft (yoneda.map (puncturedBaseInclusion k)))
    ((F.op.whiskerLeft (yoneda.map (coverPuncturedInclusion k K))) ≫ q) p
    (Stacks.Groupoids.quotientSheaf J F j).property
  · exact fun T => ⟨fun a b => (Over.mkIdTerminal (X := base k)).hom_ext a b⟩
  · exact quotient_sections_subsingleton_of_punctured k K hdegree σ hσ B hS

end AlgebraicGeometry.TwistedDoubledOrigin

end
