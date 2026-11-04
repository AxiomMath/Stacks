module

public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Relative
public import StacksFrontier.AlgebraicGeometry.ObjectDescent.Basic

/-!
# A pair of étale morphisms over a cofiltered limit descends to a finite stage

Let a scheme be the limit of a cofiltered system of affine schemes, let `X₀` and `Y₀` be schemes
of finite presentation over one stage, and let `U` be a scheme of finite presentation over the
limit equipped with two étale morphisms into the base changes of `X₀` and of `Y₀`. Then the whole
diagram `X₀ ← U → Y₀` already comes, by base change, from such a diagram over some later stage,
and both of its arrows are étale there.

This is the step "by Limits, Lemma 32.10.1 we can choose an `i` and a diagram `X_i ← U_i → Y_i`
whose base change to the limit recovers the given one; by Limits, Lemma 32.8.10, after increasing
`i` we may assume both arrows are étale" in the proof of tag 0GDX.

## Main results

* `AlgebraicGeometry.exists_descent_compat`: one morphism into a base change descends to a later
  stage, compatibly with a chosen model of its source.
* `AlgebraicGeometry.exists_descent_compat_pair`: two morphisms descend to one common stage, with
  one common model of their source.
* `AlgebraicGeometry.exists_stage_etale_pair`: the étale pair descends.

## Implementation notes

Schemes over a stage are objects of its over category and base change is
`CategoryTheory.Over.pullback`, so the two schemes `X₀` and `Y₀` are always base changed
*directly* from the fixed stage `i₀`, never iteratedly: each time the stage moves along a
transition `w`, the iterated base change is identified with the direct one along `w ≫ e` by
`AlgebraicGeometry.overPullbackCompIso`. The bookkeeping this needs is exactly
`AlgebraicGeometry.overPullbackCompIso_comp`, the cocycle identity for three composable
morphisms of bases, which together with the naturality of that comparison isomorphism moves a
descent datum along a further transition in `AlgebraicGeometry.descent_compat_step`.

A descent datum at a stage `j` is recorded as an isomorphism `ε` of `U` with the base change of a
model `V`, a morphism `m : V ⟶ (Over.pullback (D.map e)).obj X₀`, and the single equation saying
that base changing `m` to the limit and comparing recovers the given morphism. The isomorphisms
produced by tag 01ZM part (2) are *the* comparison isomorphisms, by the characterisation
`AlgebraicGeometry.iso_eq_overPullbackCompIso`, which is what lets the two applications of that
tag be chained without any further choice.

The morphism `ψ` of the final statement is the underlying morphism of schemes of the last
isomorphism `ε` followed by the first pullback projection; the three equations are its
compatibility with the `X₀`-component, the `Y₀`-component and the base, which together with the
triangles of the over categories pin it down. Translating the `Over`-level equation into those
three is `AlgebraicGeometry.descent_compat_left_fst` and
`AlgebraicGeometry.descent_compat_base`.

The affineness hypothesis on the stages is only used to supply the affine transition morphisms and
the quasi-compact, quasi-separated stages that tags 01ZM and 07RP ask for.

## References

* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 07RP](https://stacks.math.columbia.edu/tag/07RP)
* [Stacks Project, Tag 0GDX](https://stacks.math.columbia.edu/tag/0GDX)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A morphism into the base change of `X` along `p` is determined by its composite with the
first pullback projection. -/
lemma overPullback_hom_ext_left_fst {S T : Scheme.{u}} (p : T ⟶ S) {A : Over T} {X : Over S}
    {m n : A ⟶ (Over.pullback p).obj X}
    (h : m.left ≫ pullback.fst X.hom p = n.left ≫ pullback.fst X.hom p) : m = n := by
  apply Over.OverMorphism.ext
  refine pullback.hom_ext h ?_
  have hm := Over.w m
  have hn := Over.w n
  simp only [Over.pullback_obj_hom] at hm hn
  rw [hm, hn]

/-- The composite of the base change of a morphism into a base change with the comparison
isomorphism, read through the first pullback projections. -/
lemma left_fst_overPullback_map_compIso {S T T' : Scheme.{u}} (p : S ⟶ T) (q : T' ⟶ S)
    (r : T' ⟶ T) (hqr : q ≫ p = r) (V : Over S) (X : Over T)
    (m : V ⟶ (Over.pullback p).obj X) :
    ((Over.pullback q).map m ≫ (overPullbackCompIso p q r hqr X).hom).left ≫
        pullback.fst X.hom r =
      pullback.fst V.hom q ≫ m.left ≫ pullback.fst X.hom p := by
  rw [Over.comp_left, Category.assoc, overPullbackCompIso_fst,
    overPullback_map_left_fst_assoc]

/-- The comparison isomorphisms between iterated and direct base change satisfy a cocycle
identity for three composable morphisms of bases. -/
lemma overPullbackCompIso_comp {S₁ S₂ S₃ S₄ : Scheme.{u}} (p : S₂ ⟶ S₁) (q : S₃ ⟶ S₂)
    (r : S₄ ⟶ S₃) (pq : S₃ ⟶ S₁) (hpq : q ≫ p = pq) (qr : S₄ ⟶ S₂) (hqr : r ≫ q = qr)
    (pqr : S₄ ⟶ S₁) (hpqr : r ≫ pq = pqr) (hqrp : qr ≫ p = pqr) (X : Over S₁) :
    (Over.pullback r).map (overPullbackCompIso p q pq hpq X).hom ≫
        (overPullbackCompIso pq r pqr hpqr X).hom =
      (overPullbackCompIso q r qr hqr ((Over.pullback p).obj X)).hom ≫
        (overPullbackCompIso p qr pqr hqrp X).hom := by
  refine overPullback_hom_ext_left_fst pqr ?_
  rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc,
    overPullbackCompIso_fst pq r pqr hpqr X, overPullbackCompIso_fst p qr pqr hqrp X,
    overPullback_map_left_fst_assoc, overPullbackCompIso_fst p q pq hpq X,
    reassoc_of% overPullbackCompIso_fst q r qr hqr ((Over.pullback p).obj X)]

/-- A morphism between two objects of finite presentation over a common base is locally of finite
presentation. -/
lemma locallyOfFinitePresentation_left_of_over {S : Scheme.{u}} {V W : Over S} (f : V ⟶ W)
    (hV : FinitePresentation V.hom) (hW : FinitePresentation W.hom) :
    LocallyOfFinitePresentation f.left := by
  have : LocallyOfFinitePresentation V.hom := hV.1
  have : LocallyOfFinitePresentation W.hom := hW.1
  have : LocallyOfFiniteType W.hom := inferInstance
  have : LocallyOfFinitePresentation (f.left ≫ W.hom) := by rw [Over.w]; infer_instance
  exact locallyOfFinitePresentation_of_comp f.left W.hom

/-- The descent datum for one morphism, transported along a further transition morphism: if `m`
over the stage `j` recovers `t` over the limit, then its base change to the stage `j'` recovers
`t` as well. -/
lemma descent_compat_step {I : Type u} [SmallCategory I] (D : I ⥤ Scheme.{u}) (c : Cone D)
    {i₀ j j' : I} (e : j ⟶ i₀) (w : j' ⟶ j) (X₀ : Over (D.obj i₀)) (V : Over (D.obj j))
    (A : Over c.pt) (t : A ⟶ (Over.pullback (c.π.app i₀)).obj X₀)
    (ε : A ≅ (Over.pullback (c.π.app j)).obj V)
    (m : V ⟶ (Over.pullback (D.map e)).obj X₀)
    (h : ε.hom ≫ (Over.pullback (c.π.app j)).map m ≫
      (overPullbackCompIso (D.map e) (c.π.app j) (c.π.app i₀) (c.w e) X₀).hom = t) :
    (ε ≪≫ (overPullbackCompIso (D.map w) (c.π.app j') (c.π.app j) (c.w w) V).symm).hom ≫
        (Over.pullback (c.π.app j')).map ((Over.pullback (D.map w)).map m ≫
          (overPullbackCompIso (D.map e) (D.map w) (D.map (w ≫ e))
            (D.map_comp w e).symm X₀).hom) ≫
        (overPullbackCompIso (D.map (w ≫ e)) (c.π.app j') (c.π.app i₀)
          (c.w (w ≫ e)) X₀).hom = t := by
  have hmc : (Over.pullback (c.π.app j')).map ((Over.pullback (D.map w)).map m ≫
      (overPullbackCompIso (D.map e) (D.map w) (D.map (w ≫ e)) (D.map_comp w e).symm X₀).hom) =
      (Over.pullback (c.π.app j')).map ((Over.pullback (D.map w)).map m) ≫
        (Over.pullback (c.π.app j')).map (overPullbackCompIso (D.map e) (D.map w)
          (D.map (w ≫ e)) (D.map_comp w e).symm X₀).hom := Functor.map_comp _ _ _
  rw [← h, Iso.trans_hom, Iso.symm_hom, hmc]
  simp only [Category.assoc]
  rw [overPullbackCompIso_comp (D.map e) (D.map w) (c.π.app j') (D.map (w ≫ e))
      (D.map_comp w e).symm (c.π.app j) (c.w w) (c.π.app i₀) (c.w (w ≫ e)) (c.w e) X₀,
    ← reassoc_of% (overPullbackCompIso_naturality (D.map w) (c.π.app j') (c.π.app j) (c.w w) m),
    Iso.inv_hom_id_assoc]

/-- A morphism from a scheme over the limit, modelled at a stage `j`, into the base change of a
scheme of finite presentation over a stage `i₀` reachable from `j`, descends to a morphism over
some later stage, compatibly with the model. -/
lemma exists_descent_compat {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c) [∀ i, IsAffine (D.obj i)]
    {i₀ j : I} (e : j ⟶ i₀) (X₀ : Over (D.obj i₀)) (hX₀ : FinitePresentation X₀.hom)
    (V : Over (D.obj j)) (hV : FinitePresentation V.hom)
    (A : Over c.pt) (ε : A ≅ (Over.pullback (c.π.app j)).obj V)
    (t : A ⟶ (Over.pullback (c.π.app i₀)).obj X₀) :
    ∃ (j' : I) (w : j' ⟶ j) (m : (Over.pullback (D.map w)).obj V ⟶
        (Over.pullback (D.map (w ≫ e))).obj X₀),
      (ε ≪≫ (overPullbackCompIso (D.map w) (c.π.app j') (c.π.app j) (c.w w) V).symm).hom ≫
        (Over.pullback (c.π.app j')).map m ≫
          (overPullbackCompIso (D.map (w ≫ e)) (c.π.app j') (c.π.app i₀)
            (c.w (w ≫ e)) X₀).hom = t := by
  have : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f) := fun _ => inferInstance
  have : ∀ i : I, CompactSpace (D.obj i) := fun _ => inferInstance
  have : ∀ i : I, QuasiSeparatedSpace (D.obj i) := fun _ => inferInstance
  have hXj : FinitePresentation ((Over.pullback (D.map e)).obj X₀).hom :=
    LimitFPObjectDescent.finitePresentation_overPullback (D.map e) X₀ hX₀
  obtain ⟨j', w, g, α, β, hα, hβ, hg⟩ := exists_morphism_after_baseChange D c hc j V
    ((Over.pullback (D.map e)).obj X₀) hV hXj
    (ε.inv ≫ t ≫ (overPullbackCompIso (D.map e) (c.π.app j) (c.π.app i₀) (c.w e) X₀).inv)
  have hαe : α = overPullbackCompIso (D.map w) (c.π.app j') (c.π.app j) (c.w w) V :=
    iso_eq_overPullbackCompIso _ _ _ (c.w w) V α hα
  have hβe : β = overPullbackCompIso (D.map w) (c.π.app j') (c.π.app j) (c.w w)
      ((Over.pullback (D.map e)).obj X₀) := iso_eq_overPullbackCompIso _ _ _ (c.w w) _ β hβ
  subst hαe
  subst hβe
  refine ⟨j', w, g ≫ (overPullbackCompIso (D.map e) (D.map w) (D.map (w ≫ e))
    (D.map_comp w e).symm X₀).hom, ?_⟩
  have hmc : (Over.pullback (c.π.app j')).map (g ≫ (overPullbackCompIso (D.map e) (D.map w)
      (D.map (w ≫ e)) (D.map_comp w e).symm X₀).hom) =
      (Over.pullback (c.π.app j')).map g ≫ (Over.pullback (c.π.app j')).map
        (overPullbackCompIso (D.map e) (D.map w) (D.map (w ≫ e))
          (D.map_comp w e).symm X₀).hom := Functor.map_comp _ _ _
  rw [Iso.trans_hom, Iso.symm_hom, hmc]
  simp only [Category.assoc]
  rw [overPullbackCompIso_comp (D.map e) (D.map w) (c.π.app j') (D.map (w ≫ e))
      (D.map_comp w e).symm (c.π.app j) (c.w w) (c.π.app i₀) (c.w (w ≫ e)) (c.w e) X₀,
    ← reassoc_of% hg, Iso.inv_hom_id_assoc]
  simp

/-- The underlying morphism of schemes of an isomorphism in an over category is an
isomorphism. -/
lemma isIso_left_of_over_iso {S : Scheme.{u}} {V W : Over S} (e : V ≅ W) : IsIso e.hom.left :=
  inferInstanceAs (IsIso ((Over.forget S).map e.hom))

/-- The compatibility of a descent datum with the morphism over the limit, read through the first
pullback projections. -/
lemma descent_compat_left_fst {I : Type u} [SmallCategory I] (D : I ⥤ Scheme.{u}) (c : Cone D)
    {i₀ j : I} (e : j ⟶ i₀) (X₀ : Over (D.obj i₀)) (V : Over (D.obj j)) (A : Over c.pt)
    (ε : A ≅ (Over.pullback (c.π.app j)).obj V)
    (m : V ⟶ (Over.pullback (D.map e)).obj X₀)
    (t : A ⟶ (Over.pullback (c.π.app i₀)).obj X₀)
    (h : ε.hom ≫ (Over.pullback (c.π.app j)).map m ≫
      (overPullbackCompIso (D.map e) (c.π.app j) (c.π.app i₀) (c.w e) X₀).hom = t) :
    (ε.hom.left ≫ pullback.fst V.hom (c.π.app j)) ≫ m.left ≫ pullback.fst X₀.hom (D.map e) =
      t.left ≫ pullback.fst X₀.hom (c.π.app i₀) := by
  rw [← h, Over.comp_left]
  simp only [Category.assoc]
  rw [left_fst_overPullback_map_compIso (D.map e) (c.π.app j) (c.π.app i₀) (c.w e) V X₀ m]

/-- A model of a scheme over the base of a base change is compatible with the structure
morphisms. -/
lemma descent_compat_base {S T : Scheme.{u}} (p : T ⟶ S) (V : Over S) (A : Over T)
    (ε : A ≅ (Over.pullback p).obj V) :
    (ε.hom.left ≫ pullback.fst V.hom p) ≫ V.hom = A.hom ≫ p := by
  have hw := Over.w ε.hom
  simp only [Over.pullback_obj_hom] at hw
  rw [Category.assoc, pullback.condition, ← Category.assoc, hw]

/-- A scheme of finite presentation over the limit is the base change of a scheme of finite
presentation over a stage lying below a prescribed stage. -/
lemma exists_model_over_stage {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c) [∀ i, IsAffine (D.obj i)]
    (i₀ : I) (U : Over c.pt) (hU : FinitePresentation U.hom) :
    ∃ (j : I) (_ : j ⟶ i₀) (V : Over (D.obj j)), FinitePresentation V.hom ∧
      Nonempty (U ≅ (Over.pullback (c.π.app j)).obj V) := by
  have : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f) := fun _ => inferInstance
  have : ∀ i : I, CompactSpace (D.obj i) := fun _ => inferInstance
  have : ∀ i : I, QuasiSeparatedSpace (D.obj i) := fun _ => inferInstance
  obtain ⟨j₁, V₁, hV₁, ⟨eU⟩⟩ :=
    LimitFPObjectDescent.exists_model_of_finitePresentation D c hc U hU
  exact ⟨IsCofiltered.min j₁ i₀, IsCofiltered.minToRight j₁ i₀,
    (Over.pullback (D.map (IsCofiltered.minToLeft j₁ i₀))).obj V₁,
    LimitFPObjectDescent.finitePresentation_overPullback _ _ hV₁,
    ⟨eU ≪≫ (overPullbackCompIso (D.map (IsCofiltered.minToLeft j₁ i₀))
      (c.π.app (IsCofiltered.min j₁ i₀)) (c.π.app j₁)
      (c.w (IsCofiltered.minToLeft j₁ i₀)) V₁).symm⟩⟩

/-- Two morphisms out of a scheme of finite presentation over the limit, into the base changes of
two schemes of finite presentation over a stage, descend to one common later stage together with
one model of their source. -/
lemma exists_descent_compat_pair {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c) [∀ i, IsAffine (D.obj i)]
    (i₀ : I) (X₀ Y₀ : Over (D.obj i₀)) (hX₀ : FinitePresentation X₀.hom)
    (hY₀ : FinitePresentation Y₀.hom)
    (U : Over c.pt) (hU : FinitePresentation U.hom)
    (a : U ⟶ (Over.pullback (c.π.app i₀)).obj X₀)
    (b : U ⟶ (Over.pullback (c.π.app i₀)).obj Y₀) :
    ∃ (j : I) (e : j ⟶ i₀) (V : Over (D.obj j)) (_ : FinitePresentation V.hom)
      (ε : U ≅ (Over.pullback (c.π.app j)).obj V)
      (ma : V ⟶ (Over.pullback (D.map e)).obj X₀)
      (mb : V ⟶ (Over.pullback (D.map e)).obj Y₀),
      ε.hom ≫ (Over.pullback (c.π.app j)).map ma ≫
          (overPullbackCompIso (D.map e) (c.π.app j) (c.π.app i₀) (c.w e) X₀).hom = a ∧
        ε.hom ≫ (Over.pullback (c.π.app j)).map mb ≫
          (overPullbackCompIso (D.map e) (c.π.app j) (c.π.app i₀) (c.w e) Y₀).hom = b := by
  obtain ⟨j₂, v, V₂, hV₂, ⟨ε₂⟩⟩ := exists_model_over_stage D c hc i₀ U hU
  obtain ⟨j₃, w₃, ma, hma⟩ := exists_descent_compat D c hc v X₀ hX₀ V₂ hV₂ U ε₂ a
  obtain ⟨j₄, w₄, mb, hmb⟩ := exists_descent_compat D c hc (w₃ ≫ v) Y₀ hY₀
    ((Over.pullback (D.map w₃)).obj V₂)
    (LimitFPObjectDescent.finitePresentation_overPullback _ _ hV₂) U
    (ε₂ ≪≫ (overPullbackCompIso (D.map w₃) (c.π.app j₃) (c.π.app j₂) (c.w w₃) V₂).symm) b
  refine ⟨j₄, w₄ ≫ w₃ ≫ v,
    (Over.pullback (D.map w₄)).obj ((Over.pullback (D.map w₃)).obj V₂),
    LimitFPObjectDescent.finitePresentation_overPullback _ _
      (LimitFPObjectDescent.finitePresentation_overPullback _ _ hV₂),
    (ε₂ ≪≫ (overPullbackCompIso (D.map w₃) (c.π.app j₃) (c.π.app j₂) (c.w w₃) V₂).symm) ≪≫
      (overPullbackCompIso (D.map w₄) (c.π.app j₄) (c.π.app j₃) (c.w w₄)
        ((Over.pullback (D.map w₃)).obj V₂)).symm,
    (Over.pullback (D.map w₄)).map ma ≫ (overPullbackCompIso (D.map (w₃ ≫ v)) (D.map w₄)
      (D.map (w₄ ≫ w₃ ≫ v)) (D.map_comp w₄ (w₃ ≫ v)).symm X₀).hom, mb, ?_, hmb⟩
  exact descent_compat_step D c (w₃ ≫ v) w₄ X₀ ((Over.pullback (D.map w₃)).obj V₂) U a
    (ε₂ ≪≫ (overPullbackCompIso (D.map w₃) (c.π.app j₃) (c.π.app j₂) (c.w w₃) V₂).symm) ma hma

/-- A pair of étale morphisms out of a scheme of finite presentation over the limit, into the base
changes of two schemes of finite presentation over a stage, is the base change of a pair of étale
morphisms over some later stage. -/
theorem exists_stage_etale_pair
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c) [∀ i, IsAffine (D.obj i)]
    (i₀ : I) (X₀ Y₀ : Over (D.obj i₀))
    (hX₀ : FinitePresentation X₀.hom) (hY₀ : FinitePresentation Y₀.hom)
    (U : Over c.pt) (hU : FinitePresentation U.hom)
    (a : U ⟶ (Over.pullback (c.π.app i₀)).obj X₀)
    (b : U ⟶ (Over.pullback (c.π.app i₀)).obj Y₀)
    (ha : Etale a.left) (hb : Etale b.left) :
    ∃ (j : I) (e : j ⟶ i₀) (U' : Over (D.obj j))
      (a' : U' ⟶ (Over.pullback (D.map e)).obj X₀)
      (b' : U' ⟶ (Over.pullback (D.map e)).obj Y₀),
      Etale a'.left ∧ Etale b'.left ∧
      ∃ ψ : U.left ⟶ U'.left,
        ψ ≫ a'.left ≫ pullback.fst X₀.hom (D.map e) =
          a.left ≫ pullback.fst X₀.hom (c.π.app i₀) ∧
        ψ ≫ b'.left ≫ pullback.fst Y₀.hom (D.map e) =
          b.left ≫ pullback.fst Y₀.hom (c.π.app i₀) ∧
        ψ ≫ U'.hom = U.hom ≫ c.π.app j := by
  have : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f) := fun _ => inferInstance
  have : ∀ i : I, CompactSpace (D.obj i) := fun _ => inferInstance
  have : ∀ i : I, QuasiSeparatedSpace (D.obj i) := fun _ => inferInstance
  have : MorphismProperty.RespectsIso (@Etale : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  obtain ⟨j₄, e₄, V₄, hV₄, ε₄, ma, mb, hma, hmb⟩ :=
    exists_descent_compat_pair D c hc i₀ X₀ Y₀ hX₀ hY₀ U hU a b
  -- Everything about one of the two morphisms: the finiteness hypotheses of tag 07RP, the
  -- étaleness of the descended morphism, and its étaleness along any refinement of the stage.
  have key : ∀ (Z₀ : Over (D.obj i₀)), FinitePresentation Z₀.hom →
      ∀ (z : U ⟶ (Over.pullback (c.π.app i₀)).obj Z₀)
        (m : V₄ ⟶ (Over.pullback (D.map e₄)).obj Z₀),
      ε₄.hom ≫ (Over.pullback (c.π.app j₄)).map m ≫
        (overPullbackCompIso (D.map e₄) (c.π.app j₄) (c.π.app i₀) (c.w e₄) Z₀).hom = z →
      Etale z.left → ∃ p : Over j₄, ∀ {k : I} (g : k ⟶ j₄) (f : k ⟶ p.left), f ≫ p.hom = g →
        Etale (((Over.pullback (D.map g)).map m ≫ (overPullbackCompIso (D.map e₄) (D.map g)
          (D.map (g ≫ e₄)) (D.map_comp g e₄).symm Z₀).hom).left) := by
    intro Z₀ hZ₀ z m hm hz
    have hZe : FinitePresentation ((Over.pullback (D.map e₄)).obj Z₀).hom :=
      LimitFPObjectDescent.finitePresentation_overPullback _ _ hZ₀
    have : IsIso ε₄.hom.left := isIso_left_of_over_iso ε₄
    have : IsIso (overPullbackCompIso (D.map e₄) (c.π.app j₄) (c.π.app i₀) (c.w e₄) Z₀).hom.left :=
      isIso_left_of_over_iso _
    have hELim : Etale ((Over.pullback (c.π.app j₄)).map m).left := by
      rw [← hm, Over.comp_left, Over.comp_left] at hz
      exact (MorphismProperty.cancel_right_of_respectsIso (P := @Etale) _ _).mp
        ((MorphismProperty.cancel_left_of_respectsIso (P := @Etale) _ _).mp hz)
    have : QuasiCompact V₄.hom := hV₄.2.1
    have : QuasiSeparated V₄.hom := hV₄.2.2
    have : CompactSpace V₄.left := QuasiCompact.compactSpace_of_compactSpace V₄.hom
    have : QuasiSeparatedSpace V₄.left := quasiSeparatedSpace_of_quasiSeparated V₄.hom
    have : QuasiCompact ((Over.pullback (D.map e₄)).obj Z₀).hom := hZe.2.1
    have : QuasiSeparated ((Over.pullback (D.map e₄)).obj Z₀).hom := hZe.2.2
    have : CompactSpace ((Over.pullback (D.map e₄)).obj Z₀).left :=
      QuasiCompact.compactSpace_of_compactSpace ((Over.pullback (D.map e₄)).obj Z₀).hom
    have : QuasiSeparatedSpace ((Over.pullback (D.map e₄)).obj Z₀).left :=
      quasiSeparatedSpace_of_quasiSeparated ((Over.pullback (D.map e₄)).obj Z₀).hom
    have : LocallyOfFinitePresentation m.left := locallyOfFinitePresentation_left_of_over m hV₄ hZe
    obtain ⟨p, hp⟩ := exists_etale_pullback_of_isLimit D c hc j₄ V₄
      ((Over.pullback (D.map e₄)).obj Z₀) m
    refine ⟨p, fun g f hfg => ?_⟩
    have h := overPullback_map_comp (@Etale) (D.map p.hom) (D.map f) m hp
    rw [← D.map_comp, hfg] at h
    have : IsIso (overPullbackCompIso (D.map e₄) (D.map g) (D.map (g ≫ e₄))
        (D.map_comp g e₄).symm Z₀).hom.left := isIso_left_of_over_iso _
    rw [Over.comp_left]
    exact (MorphismProperty.cancel_right_of_respectsIso (P := @Etale) _ _).2 h
  obtain ⟨p₁, hp₁⟩ := key X₀ hX₀ a ma hma ha
  obtain ⟨p₂, hp₂⟩ := key Y₀ hY₀ b mb hmb hb
  obtain ⟨n, n₁, n₂, hn⟩ := IsCofiltered.cospan p₁.hom p₂.hom
  -- Transport the two descent data to the common stage and read off the conclusion.
  have hma₅ := descent_compat_step D c e₄ (n₁ ≫ p₁.hom) X₀ V₄ U a ε₄ ma hma
  have hmb₅ := descent_compat_step D c e₄ (n₁ ≫ p₁.hom) Y₀ V₄ U b ε₄ mb hmb
  refine ⟨n, (n₁ ≫ p₁.hom) ≫ e₄, (Over.pullback (D.map (n₁ ≫ p₁.hom))).obj V₄,
    (Over.pullback (D.map (n₁ ≫ p₁.hom))).map ma ≫ (overPullbackCompIso (D.map e₄)
      (D.map (n₁ ≫ p₁.hom)) (D.map ((n₁ ≫ p₁.hom) ≫ e₄))
      (D.map_comp (n₁ ≫ p₁.hom) e₄).symm X₀).hom,
    (Over.pullback (D.map (n₁ ≫ p₁.hom))).map mb ≫ (overPullbackCompIso (D.map e₄)
      (D.map (n₁ ≫ p₁.hom)) (D.map ((n₁ ≫ p₁.hom) ≫ e₄))
      (D.map_comp (n₁ ≫ p₁.hom) e₄).symm Y₀).hom, hp₁ _ n₁ rfl, hp₂ _ n₂ hn.symm, ?_⟩
  refine ⟨(ε₄ ≪≫ (overPullbackCompIso (D.map (n₁ ≫ p₁.hom)) (c.π.app n) (c.π.app j₄)
      (c.w (n₁ ≫ p₁.hom)) V₄).symm).hom.left ≫
      pullback.fst ((Over.pullback (D.map (n₁ ≫ p₁.hom))).obj V₄).hom (c.π.app n), ?_, ?_, ?_⟩
  · exact descent_compat_left_fst D c ((n₁ ≫ p₁.hom) ≫ e₄) X₀ _ U _ _ a hma₅
  · exact descent_compat_left_fst D c ((n₁ ≫ p₁.hom) ≫ e₄) Y₀ _ U _ _ b hmb₅
  · exact descent_compat_base (c.π.app n) ((Over.pullback (D.map (n₁ ≫ p₁.hom))).obj V₄) U _

end AlgebraicGeometry

end
