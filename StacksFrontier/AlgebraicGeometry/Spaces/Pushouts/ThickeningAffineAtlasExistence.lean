module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutRelation
public import StacksFrontier.AlgebraicGeometry.Size.Pushout
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfaeComplete
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineSpacesSupplement
public import StacksFrontier.CategoryTheory.EquivalenceRelation.Slice
public import StacksFrontier.CategoryTheory.EquivalenceRelation.Transfer

/-!
# The compatible étale charts of a thickening-and-affine span of algebraic spaces

Let `i : X ⟶ X'` be a thickening of algebraic spaces over `S` and `f : X ⟶ Y` an affine
morphism.  The proof of [Stacks Project, Tag 07VX] chooses a surjective étale scheme chart
`V ⟶ Y`, puts `U = X ×_Y V` (a scheme, affine over `V`), lifts the chart `U ⟶ X` across the
thickening to a surjective étale scheme chart `U' ⟶ X'` with `U = X ×_{X'} U'`
([Stacks Project, Tag 05ZS]), forms the scheme pushouts `P = U' ⨿_U V` and
`Rel = (U' ×_{X'} U') ⨿_{U ×_X U} (V ×_Y V)` ([Stacks Project, Tag 07RT]), and observes that
`Rel ⇉ P` is an étale equivalence relation.

This module carries out that construction: given the lift of a surjective étale scheme chart of
`X` across the thickening, it produces an `AlgebraicGeometry.Space.ThickeningAffineAtlas`.  The
lift is the only input; it is the essential surjectivity half of Tag 05ZS in chart form, which
is `AlgebraicGeometry.Space.exists_etaleChart_lift_of_isThickeningHom` once Stacks 05ZR is
available.

## Main results

* `CategoryTheory.Limits.isPullback_kernelPair_map`: the kernel pair of the base change of a
  morphism is the base change of its kernel pair.
* `AlgebraicGeometry.Space.nonempty_thickeningAffineAtlas_of_chartLift`: the atlas, from the lift
  of a chart.
* `AlgebraicGeometry.Space.hasThickeningAffineAtlases_of_chartLift`: hence
  `AlgebraicGeometry.Space.HasThickeningAffineAtlases`, the carried input of the Stacks 07VY,
  07W1, 07W2 and 07W3 carriers, from the chart lift of Stacks 05ZS alone.

## Implementation notes

The three kernel pairs `R₀ = U ×_X U`, `R' = U' ×_{X'} U'` and `T = V ×_Y V` are chosen
independently in the site, and `R₀ ⟶ R'`, `R₀ ⟶ T` are the induced morphisms; the two squares
over each projection of `R₀` are cartesian by `CategoryTheory.Limits.isPullback_kernelPair_map`.
The two scheme pushouts lie in the site by
`AlgebraicGeometry.Scheme.size_lt_of_isPushout_of_isThickening_of_isStrongPrelimit`.  The
relation is an étale equivalence relation by
`Stacks.Pushout.nonempty_equivalenceRelation_of_isPushout`, the kernel pairs of the charts being
étale equivalence relations by Stacks 0262.

## References

* [Stacks Project, Tag 05ZS](https://stacks.math.columbia.edu/tag/05ZS)
* [Stacks Project, Tag 07RT](https://stacks.math.columbia.edu/tag/07RT)
* [Stacks Project, Tag 07VX](https://stacks.math.columbia.edu/tag/07VX)
* [Stacks Project, Tag 0262](https://stacks.math.columbia.edu/tag/0262)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.Limits

variable {C : Type*} [Category C]

/-- **The kernel pair of a base change is the base change of the kernel pair.**  If
`U = U' ×_{X'} X` and `R₀ ⇉ U`, `R' ⇉ U'` are kernel pairs of `p : U ⟶ X` and `p' : U' ⟶ X'`,
then any `kR : R₀ ⟶ R'` over `k : U ⟶ U'` exhibits `R₀` as `R' ×_{s', U'} U`. -/
theorem isPullback_kernelPair_map {U U' X X' R₀ R' : C} {k : U ⟶ U'} {p : U ⟶ X}
    {p' : U' ⟶ X'} {i : X ⟶ X'} (h : IsPullback k p p' i) {s₀ t₀ : R₀ ⟶ U}
    (h₀ : IsPullback s₀ t₀ p p) {s' t' : R' ⟶ U'} (h' : IsPullback s' t' p' p')
    {kR : R₀ ⟶ R'} (hs : kR ≫ s' = s₀ ≫ k) (ht : kR ≫ t' = t₀ ≫ k) :
    IsPullback kR s₀ s' k := by
  have hcond : ∀ l : PullbackCone s' k, (l.fst ≫ t') ≫ p' = (l.snd ≫ p) ≫ i := fun l => by
    rw [Category.assoc, ← h'.w, ← Category.assoc, l.condition, Category.assoc, h.w,
      Category.assoc]
  let lift : ∀ l : PullbackCone s' k, l.pt ⟶ R₀ := fun l =>
    h₀.lift l.snd (h.lift (l.fst ≫ t') (l.snd ≫ p) (hcond l)) (by rw [h.lift_snd])
  refine ⟨⟨hs⟩, ⟨PullbackCone.IsLimit.mk hs lift (fun l => ?_) (fun l => ?_)
    (fun l m h₁ h₂ => ?_)⟩⟩
  · apply h'.hom_ext
    · rw [Category.assoc, hs, ← Category.assoc, h₀.lift_fst, l.condition]
    · rw [Category.assoc, ht, ← Category.assoc, h₀.lift_snd, h.lift_fst]
  · exact h₀.lift_fst _ _ _
  · apply h₀.hom_ext
    · rw [h₂, h₀.lift_fst]
    · rw [h₀.lift_snd]
      apply h.hom_ext
      · rw [Category.assoc, ← ht, ← Category.assoc, h₁, h.lift_fst]
      · rw [Category.assoc, ← h₀.w, ← Category.assoc, h₂, h.lift_snd]

end CategoryTheory.Limits

namespace AlgebraicGeometry.Space

attribute [local instance] AlgebraicGeometry.preservesPullbacks_bigFppfOverToScheme

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Two morphisms of the site out of the same object agree after composing with the structure
morphisms and mapping to schemes. -/
private theorem inclusion_map_left_comp_hom_eq {A C C' : BigFppfOver B S hS} (x : A ⟶ C)
    (y : A ⟶ C') : B.inclusion.map x.left ≫ B.inclusion.map C.hom =
      B.inclusion.map y.left ≫ B.inclusion.map C'.hom := by
  rw [← Functor.map_comp, ← Functor.map_comp, Over.w x, Over.w y]

/-- A commuting square in the site maps to a commuting square of schemes. -/
private theorem toScheme_map_comp_eq {A₁ A₂ A₃ A₄ : BigFppfOver B S hS} {x : A₁ ⟶ A₂}
    {y : A₂ ⟶ A₄} {u : A₁ ⟶ A₃} {v : A₃ ⟶ A₄} (h : x ≫ y = u ≫ v) :
    (BigFppfOver.toScheme B S hS).map x ≫ (BigFppfOver.toScheme B S hS).map y =
      (BigFppfOver.toScheme B S hS).map u ≫ (BigFppfOver.toScheme B S hS).map v := by
  rw [← Functor.map_comp, ← Functor.map_comp, h]

/-- The scheme pushout of two morphisms of the site along a thickening and an affine morphism, as
an object of the site, with its two legs. -/
theorem exists_isPushout_site {A A₁ A₂ : BigFppfOver B S hS} (k : A ⟶ A₁) (g : A ⟶ A₂)
    (hk : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map k))
    [_root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map g)] :
    ∃ (Q : BigFppfOver B S hS) (a : A₁ ⟶ Q) (b : A₂ ⟶ Q),
      IsPushout ((BigFppfOver.toScheme B S hS).map k) ((BigFppfOver.toScheme B S hS).map g)
        ((BigFppfOver.toScheme B S hS).map a) ((BigFppfOver.toScheme B S hS).map b) := by
  let F := BigFppfOver.toScheme B S hS
  have : HasPushout (F.map k) (F.map g) :=
    Stacks.Pushout.hasPushout_of_isThickening_of_isAffineHom' _ _ hk
  have hsize : B.Contains (pushout (F.map k) (F.map g)) :=
    Scheme.size_lt_of_isPushout_of_isThickening_of_isStrongPrelimit B.cutoff_isStrongPrelimit
      (IsPushout.of_hasPushout _ _) hk A₂.left.property A₁.left.property
  have hw : F.map k ≫ B.inclusion.map A₁.hom = F.map g ≫ B.inclusion.map A₂.hom :=
    inclusion_map_left_comp_hom_eq B S hS k g
  let str : pushout (F.map k) (F.map g) ⟶ S :=
    pushout.desc (B.inclusion.map A₁.hom) (B.inclusion.map A₂.hom) hw
  exact ⟨BigFppfOver.mk B S hS hsize str,
    BigFppfOver.homMk B S hS hsize str (pushout.inl _ _) (pushout.inl_desc _ _ _),
    BigFppfOver.homMk B S hS hsize str (pushout.inr _ _) (pushout.inr_desc _ _ _),
    IsPushout.of_hasPushout _ _⟩

/-- The morphism between two scheme pushouts in the site induced by two morphisms of the legs. -/
theorem exists_desc_site {A A₁ A₂ Q W : BigFppfOver B S hS}
    {k : A ⟶ A₁} {g : A ⟶ A₂} {a : A₁ ⟶ Q} {b : A₂ ⟶ Q}
    (hQ : IsPushout ((BigFppfOver.toScheme B S hS).map k) ((BigFppfOver.toScheme B S hS).map g)
      ((BigFppfOver.toScheme B S hS).map a) ((BigFppfOver.toScheme B S hS).map b))
    (x : A₁ ⟶ W) (y : A₂ ⟶ W) (hxy : k ≫ x = g ≫ y) :
    ∃ m : Q ⟶ W, a ≫ m = x ∧ b ≫ m = y := by
  let F := BigFppfOver.toScheme B S hS
  let m₀ : F.obj Q ⟶ F.obj W := hQ.desc (F.map x) (F.map y) (toScheme_map_comp_eq B S hS hxy)
  have hm₀ : m₀ ≫ B.inclusion.map W.hom = B.inclusion.map Q.hom := by
    refine hQ.hom_ext ?_ ?_
    · rw [hQ.inl_desc_assoc]
      exact inclusion_map_left_comp_hom_eq B S hS x a
    · rw [hQ.inr_desc_assoc]
      exact inclusion_map_left_comp_hom_eq B S hS y b
  let m : Q ⟶ W := Over.homMk (ObjectProperty.homMk m₀) (by
    apply ObjectProperty.hom_ext
    exact hm₀)
  exact ⟨m, F.map_injective ((F.map_comp _ _).trans (hQ.inl_desc _ _ _)),
    F.map_injective ((F.map_comp _ _).trans (hQ.inr_desc _ _ _))⟩

/-- The morphism of kernel pairs induced by a cartesian square of charts, with its two cartesian
squares over the projections. -/
private theorem exists_kernelPair_map {G G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U U' R₀ R' : BigFppfOver B S hS} {k : U ⟶ U'} {p : yoneda.obj U ⟶ G}
    {p' : yoneda.obj U' ⟶ G'} {i : G ⟶ G'} (h : IsPullback (yoneda.map k) p p' i)
    {s₀ t₀ : R₀ ⟶ U} (h₀ : IsPullback (yoneda.map s₀) (yoneda.map t₀) p p)
    {s' t' : R' ⟶ U'} (h' : IsPullback (yoneda.map s') (yoneda.map t') p' p') :
    ∃ kR : R₀ ⟶ R', kR ≫ s' = s₀ ≫ k ∧ kR ≫ t' = t₀ ≫ k ∧
      IsPullback kR s₀ s' k ∧ IsPullback kR t₀ t' k := by
  have hcond : yoneda.map (s₀ ≫ k) ≫ p' = yoneda.map (t₀ ≫ k) ≫ p' := by
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, h.w,
      ← Category.assoc, h₀.w, Category.assoc]
  let kR : R₀ ⟶ R' := yoneda.preimage (h'.lift _ _ hcond)
  have hs : kR ≫ s' = s₀ ≫ k := yoneda.map_injective (by
    rw [Functor.map_comp, yoneda.map_preimage, h'.lift_fst])
  have ht : kR ≫ t' = t₀ ≫ k := yoneda.map_injective (by
    rw [Functor.map_comp, yoneda.map_preimage, h'.lift_snd])
  exact ⟨kR, hs, ht,
    IsPullback.of_map yoneda hs (isPullback_kernelPair_map h h₀ h'
      (by rw [← Functor.map_comp, hs, Functor.map_comp])
      (by rw [← Functor.map_comp, ht, Functor.map_comp])),
    IsPullback.of_map yoneda ht (isPullback_kernelPair_map h h₀.flip h'.flip
      (by rw [← Functor.map_comp, ht, Functor.map_comp])
      (by rw [← Functor.map_comp, hs, Functor.map_comp]))⟩

/-- The relation `Rel = R' ⨿_{R₀} T ⇉ P = U' ⨿_U V` pushed out from the kernel pairs of two étale
charts along a thickening and an affine morphism is an étale equivalence relation. -/
private theorem isEtaleEquivalenceRelation_relation_of_isPushout
    {G G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U U' V R₀ R' T P Rel : BigFppfOver B S hS} {k : U ⟶ U'} {g : U ⟶ V} {kR : R₀ ⟶ R'}
    {gR : R₀ ⟶ T} {s₀ t₀ : R₀ ⟶ U} {s' t' : R' ⟶ U'} {sY tY : T ⟶ V} {a : U' ⟶ P}
    {b : V ⟶ P} {aR : R' ⟶ Rel} {bR : T ⟶ Rel} {s t : Rel ⟶ P}
    {p' : yoneda.obj U' ⟶ G'} {q : yoneda.obj V ⟶ G}
    (hp'E : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) p')
    (hqE : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) q)
    (hR' : IsPullback (yoneda.map s') (yoneda.map t') p' p')
    (hT : IsPullback (yoneda.map sY) (yoneda.map tY) q q)
    (hP : IsPushout ((BigFppfOver.toScheme B S hS).map k) ((BigFppfOver.toScheme B S hS).map g)
      ((BigFppfOver.toScheme B S hS).map a) ((BigFppfOver.toScheme B S hS).map b))
    (hRel : IsPushout ((BigFppfOver.toScheme B S hS).map kR)
      ((BigFppfOver.toScheme B S hS).map gR) ((BigFppfOver.toScheme B S hS).map aR)
      ((BigFppfOver.toScheme B S hS).map bR))
    (hk : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map k))
    (hkR : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map kR))
    [_root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map g)]
    [_root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map gR)]
    (hsi : IsPullback kR s₀ s' k) (hti : IsPullback kR t₀ t' k)
    (hsf : IsPullback gR s₀ sY g) (htf : IsPullback gR t₀ tY g)
    (hsa : aR ≫ s = s' ≫ a) (hsb : bR ≫ s = sY ≫ b) (hta : aR ≫ t = t' ≫ a)
    (htb : bR ≫ t = tY ≫ b) :
    Stacks.Groupoids.IsEtaleEquivalenceRelation (relation B S hS s t) := by
  let F := BigFppfOver.toScheme B S hS
  have etale_of : ∀ {Z W : BigFppfOver B S hS} {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
      {r : yoneda.obj W ⟶ G} {x y : Z ⟶ W},
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) r →
      IsPullback (yoneda.map x) (yoneda.map y) r r → AlgebraicGeometry.Etale (F.map y) :=
    fun hr h => hr.property _ (yoneda.map _) _ h
  have : AlgebraicGeometry.Etale (F.map s') := etale_of hp'E hR'.flip
  have : AlgebraicGeometry.Etale (F.map t') := etale_of hp'E hR'
  have : AlgebraicGeometry.Etale (F.map sY) := etale_of hqE hT.flip
  have : AlgebraicGeometry.Etale (F.map tY) := etale_of hqE hT
  have equiv_of : ∀ {Z W : BigFppfOver B S hS} {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
      {r : yoneda.obj W ⟶ G} {x y : Z ⟶ W}, IsPullback (yoneda.map x) (yoneda.map y) r r →
      Nonempty (EquivalenceRelation (F.map y) (F.map x)) := fun {Z W G r x y} h =>
    (isEquivalenceRelation_left _ _
      (isEquivalenceRelation_of_isPullback B S hS r y x h.flip)).nonempty_equivalenceRelation
  have hsaS := toScheme_map_comp_eq B S hS hsa
  have hsbS := toScheme_map_comp_eq B S hS hsb
  have htaS := toScheme_map_comp_eq B S hS hta
  have htbS := toScheme_map_comp_eq B S hS htb
  obtain ⟨eRel⟩ := Stacks.Pushout.nonempty_equivalenceRelation_of_isPushout hP hk hRel hkR
    (hsi.map F) (hsf.map F) (hti.map F) (htf.map F) hsaS hsbS htaS htbS (equiv_of hR').some
    (equiv_of hT).some
  have : AlgebraicGeometry.Etale (F.map s) :=
    Stacks.Pushout.etale_of_isPushout_relation hP hk hRel hkR (hsi.map F) (hsf.map F) hsaS hsbS
  have : AlgebraicGeometry.Etale (F.map t) :=
    Stacks.Pushout.etale_of_isPushout_relation hP hk hRel hkR (hti.map F) (htf.map F) htaS htbS
  have : IsEquivalenceRelation (F.map t) (F.map s) := eRel.isEquivalenceRelation
  exact
    { isEquivalenceRelation := by
        simp only [Stacks.Groupoids.PreRelation.target, Stacks.Groupoids.PreRelation.source,
          relation, prod.lift_fst, prod.lift_snd]
        have h : IsEquivalenceRelation ((Over.post B.inclusion).map t).left
            ((Over.post B.inclusion).map s).left := eRel.isEquivalenceRelation
        exact isEquivalenceRelation_of_left _ _
      etale_source := by
        simp only [Stacks.Groupoids.PreRelation.source, relation, prod.lift_snd]
        exact (inferInstance : AlgebraicGeometry.Etale (F.map s))
      etale_target := by
        simp only [Stacks.Groupoids.PreRelation.target, relation, prod.lift_fst]
        exact (inferInstance : AlgebraicGeometry.Etale (F.map t)) }

/-- **[Stacks Project, Tag 07VX] on prescribed charts: the cube of 07W1.**  Let
`i : X ⟶ X'` be a thickening of algebraic spaces over `S` and `f : X ⟶ Y` an affine morphism.
Let `q : V ⟶ Y` be a surjective étale scheme chart, `U = X ×_Y V` with its affine `g : U ⟶ V`,
and let `p' : U' ⟶ X'` be a surjective étale scheme chart with `U = X ×_{X'} U'` along a
thickening `k : U ⟶ U'`.  Then the scheme pushout `P = U' ⨿_U V` lies in the site, there is a
pushout `Y' = Y ⨿_X X'` of algebraic spaces, and `P ⟶ Y'` is a surjective étale chart whose two
squares over `X' ⟶ Y'` and `Y ⟶ Y'` are cartesian; and the span admits a
`AlgebraicGeometry.Space.ThickeningAffineAtlas`. -/
theorem exists_chartCube_of_charts
    {X X' Y : AlgebraicSpaces B S hS} (i : X ⟶ X') (f : X ⟶ Y) (hi : IsThickeningHom B S hS i)
    {V : BigFppfOver B S hS} (q : yoneda.obj V ⟶ Y.1)
    (hqS : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) q)
    (hqE : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) q)
    {U : BigFppfOver B S hS} (p : yoneda.obj U ⟶ X.1) (g : U ⟶ V)
    (hpaff : IsPullback p (yoneda.map g) f.hom q)
    [hgaff : _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map g)]
    {U' : BigFppfOver B S hS} (p' : yoneda.obj U' ⟶ X'.1) (k : U ⟶ U')
    (hp'S : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) p')
    (hp'E : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) p')
    (hthick : IsPullback (yoneda.map k) p p' i.hom)
    (hk : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map k)) :
    ∃ (P : BigFppfOver B S hS) (a : U' ⟶ P) (b : V ⟶ P) (E : AlgebraicSpaces B S hS)
      (aY : X' ⟶ E) (bY : Y ⟶ E) (qm : yoneda.obj P ⟶ E.1),
      IsPushout ((BigFppfOver.toScheme B S hS).map k) ((BigFppfOver.toScheme B S hS).map g)
        ((BigFppfOver.toScheme B S hS).map a) ((BigFppfOver.toScheme B S hS).map b) ∧
      IsPushout i f aY bY ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) qm ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) qm ∧
      IsPullback (yoneda.map a) p' qm aY.hom ∧ IsPullback (yoneda.map b) q qm bY.hom ∧
      Nonempty (ThickeningAffineAtlas B S hS i f) := by
  let F := BigFppfOver.toScheme B S hS
  have hpE : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) p :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hpaff.flip hqE
  have hpS : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) p :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hpaff.flip hqS
  obtain ⟨R', s', t', hR'⟩ := exists_kernelPair_of_etale_atlas B S hS p' hp'E
  obtain ⟨T, sY, tY, hT⟩ := exists_kernelPair_of_etale_atlas B S hS q hqE
  obtain ⟨R₀, s₀, t₀, hR₀⟩ := exists_kernelPair_of_etale_atlas B S hS p hpE
  obtain ⟨kR, hkRs, hkRt, hsi, hti⟩ := exists_kernelPair_map B S hS hthick hR₀ hR'
  obtain ⟨gR, hgRs, hgRt, hsf, htf⟩ := exists_kernelPair_map B S hS hpaff.flip hR₀ hT
  have hkR : Stacks.Thickenings.IsThickening (F.map kR) :=
    Stacks.Thickenings.isThickening_of_isPullback (hsi.map F) hk
  have hgRaff : _root_.AlgebraicGeometry.IsAffineHom (F.map gR) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @_root_.AlgebraicGeometry.IsAffineHom) (hsf.map F).flip hgaff
  obtain ⟨P, a, b, hP⟩ := exists_isPushout_site B S hS k g hk
  obtain ⟨Rel, aR, bR, hRel⟩ := exists_isPushout_site B S hS kR gR hkR
  have hab : k ≫ a = g ≫ b := F.map_injective (by simpa only [Functor.map_comp] using hP.w)
  obtain ⟨s, hsa, hsb⟩ := exists_desc_site B S hS hRel (s' ≫ a) (sY ≫ b) (by
    rw [← Category.assoc, hkRs, ← Category.assoc, hgRs, Category.assoc, Category.assoc, hab])
  obtain ⟨t, hta, htb⟩ := exists_desc_site B S hS hRel (t' ≫ a) (tY ≫ b) (by
    rw [← Category.assoc, hkRt, ← Category.assoc, hgRt, Category.assoc, Category.assoc, hab])
  let A : ThickeningAffineAtlas B S hS i f :=
    { U := U, U' := U', V := V, R₀ := R₀, R' := R', T := T, P := P, Rel := Rel
      p := p, p' := p', q := q, k := k, g := g, kR := kR, gR := gR
      s' := s', t' := t', sY := sY, tY := tY, a := a, b := b, aR := aR, bR := bR
      s := s, t := t
      isPullback_affine := hpaff, isPullback_thickening := hthick
      isThickening_k := hk, isAffineHom_g := hgaff
      isThickening_kR := hkR, isAffineHom_gR := hgRaff
      surjective_p := hpS, etale_p := hpE, surjective_p' := hp'S, etale_p' := hp'E
      surjective_q := hqS, etale_q := hqE, kernelPair_X' := hR', kernelPair_Y := hT
      isPushout_chart := hP, isPushout_relation := hRel
      aR_s := hsa, aR_t := hta, bR_s := hsb, bR_t := htb
      etaleRelation := isEtaleEquivalenceRelation_relation_of_isPushout B S hS hp'E hqE hR' hT
        hP hRel hk hkR hsi hti hsf htf hsa hsb hta htb }
  obtain ⟨E, aY, bY, qm, hpush, -, hqmS, hqmE, haX', hbY⟩ :=
    exists_pushout_chart_of_thickeningAffineAtlas B S hS A hi
  exact ⟨P, a, b, E, aY, bY, qm, hP, hpush, hqmS, hqmE, haX', hbY, ⟨A⟩⟩

/-- **The compatible étale charts of [Stacks Project, Tag 07VX], from the lift of a chart.**  Let
`i : X ⟶ X'` be a thickening of algebraic spaces over `S` and `f : X ⟶ Y` an affine morphism.
If every surjective étale scheme chart of `X` lifts across `i` to a surjective étale scheme chart
of `X'` — the chart form of the essential surjectivity half of [Stacks Project, Tag 05ZS] — then
the span admits a `AlgebraicGeometry.Space.ThickeningAffineAtlas`. -/
theorem nonempty_thickeningAffineAtlas_of_chartLift
    {X X' Y : AlgebraicSpaces B S hS} (i : X ⟶ X') (f : X ⟶ Y) (hi : IsThickeningHom B S hS i)
    (hf : IsAffineHom B S hS f.hom)
    (hlift : ∀ {U : BigFppfOver B S hS} (p : yoneda.obj U ⟶ X.1),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) p →
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) p →
      ∃ (U' : BigFppfOver B S hS) (p' : yoneda.obj U' ⟶ X'.1) (k : U ⟶ U'),
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) p' ∧
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) p' ∧
        IsPullback (yoneda.map k) p p' i.hom ∧
        Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map k)) :
    Nonempty (ThickeningAffineAtlas B S hS i f) := by
  obtain ⟨V, q, hqS, hqE⟩ := Y.property.exists_atlas
  have hpres := presheaf_isAffineHom_of_isAffineHom_of_isAlgebraicSpace B S hS X.property
    Y.property hf
  have : _root_.AlgebraicGeometry.IsAffineHom
      ((BigFppfOver.toScheme B S hS).map (hpres.2.rep.snd q)) := hpres.2.property_snd q
  have hpaff := hpres.2.rep.isPullback q
  obtain ⟨U', p', k, hp'S, hp'E, hthick, hk⟩ := hlift (hpres.2.rep.fst q)
    ((MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hpaff.flip hqS)
    ((MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hpaff.flip hqE)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hA⟩ :=
    exists_chartCube_of_charts B S hS i f hi q hqS hqE _ _ hpaff p' k hp'S hp'E hthick hk
  exact hA

/-- Every thickening-and-affine span of algebraic spaces over `S` admits compatible étale charts,
`AlgebraicGeometry.Space.HasThickeningAffineAtlases`, as soon as surjective étale scheme charts
lift across every thickening — the chart form of the essential surjectivity half of
[Stacks Project, Tag 05ZS], which is the conclusion of
`AlgebraicGeometry.Space.exists_etaleChart_lift_of_isThickeningHom`. -/
theorem hasThickeningAffineAtlases_of_chartLift
    (hlift : ∀ {X X' : AlgebraicSpaces B S hS} (i : X ⟶ X'), IsThickeningHom B S hS i →
      ∀ {U : BigFppfOver B S hS} (p : yoneda.obj U ⟶ X.1),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) p →
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) p →
      ∃ (U' : BigFppfOver B S hS) (p' : yoneda.obj U' ⟶ X'.1) (k : U ⟶ U'),
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) p' ∧
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) p' ∧
        IsPullback (yoneda.map k) p p' i.hom ∧
        Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map k)) :
    HasThickeningAffineAtlases B S hS :=
  fun i f hi hf => nonempty_thickeningAffineAtlas_of_chartLift B S hS i f hi hf (hlift i hi)

end AlgebraicGeometry.Space

end
