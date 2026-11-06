module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.Presheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.SeparatedClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.Retrofit
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import Mathlib.CategoryTheory.Subfunctor.Image
public import Mathlib.CategoryTheory.Subfunctor.OfSection
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable

/-!
# The finite part containing a section

Fix a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` with a section `σ : Y ⟶ X`.
Inside the finite part `(X/Y)_fin` sits the subfunctor `(X/Y, σ)_fin` of those pairs `(a, Z)`
whose open subspace contains the section of `T ×_Y X` over `T` induced by `σ`. Its inclusion is
the transformation `t` of the source, and it is representable by open immersions; by open and
closed immersions when `f` is separated; so `(X/Y, σ)_fin` is an open subspace of `(X/Y)_fin`
whenever the latter is an algebraic space, and an open subscheme whenever it is a scheme.

## Main definitions

* `AlgebraicGeometry.Space.ContainsSection` — the condition on a pair of Stacks 04PC that it
  contain the induced section, which is the `containsSection` field of Stacks 04RQ read as a
  predicate.
* `AlgebraicGeometry.Space.FinitePartWithSection` — the subfunctor `(X/Y, σ)_fin` together with
  its pointwise characterisation.
* `AlgebraicGeometry.Space.finitePartWithSection` — the transformation `t` of Stacks 04RR.

## Main results

* `AlgebraicGeometry.Space.isOpenImmersion_finitePartWithSection` — Stacks 04RR, part (1).
* `AlgebraicGeometry.Space.isClosedImmersion_finitePartWithSection` — part (2).
* `AlgebraicGeometry.Space.isOpenSubspace_finitePartWithSection` — part (3).
* `AlgebraicGeometry.Space.openSubscheme_finitePartWithSection` — part (4).

## Implementation notes

The transformation `t` is presented as the inclusion of a subfunctor rather than as a bare
morphism of presheaves, so that `(X/Y, σ)_fin` is literally a subobject of `(X/Y)_fin` and
parts (3) and (4) are statements about that subobject. `FinitePartWithSection` bundles the
subfunctor with the equivalence between membership and `ContainsSection`, which is what makes
the inclusion *the* transformation of the source rather than some morphism with the same source
and target.

Parts (1) and (2) share one engine: the pullback of `(X/Y, σ)_fin` along a representable map is
the preimage of that pair's own open subspace under the induced section, so any
base-change-stable property of morphisms which holds for every pair's subspace inclusion holds
for `t`. For part (1) that property is being an open immersion, which is the `isOpen` field of
the pair; for part (2) it is being a closed immersion, which is Stacks 04PH.

Containment of the section is recorded as an actual factorisation through the inclusion of the
subspace, not as a containment of images: the factorising morphism is unique because the
inclusion is a monomorphism, so this carries no extra information and is directly usable.

## References

* [Stacks Project, Tag 04RR](https://stacks.math.columbia.edu/tag/04RR)
* [Stacks Project, Tag 04RQ](https://stacks.math.columbia.edu/tag/04RQ)
* [Stacks Project, Tag 04PC](https://stacks.math.columbia.edu/tag/04PC)
* [Stacks Project, Tag 04PH](https://stacks.math.columbia.edu/tag/04PH)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

set_option synthInstance.maxHeartbeats 400000

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
private instance (priority := high) hasPullbacks_presheaf_finitePartWithSection
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    HasPullbacks ((AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

private instance (priority := high) hasPullback_presheaf_finitePartWithSection
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_finitePartWithSection B S hS).has_limit _

private theorem yoneda_subfunctor_lift_iff
    {C : Type*} [Category C] {F : Cᵒᵖ ⥤ Type u} (Z : Subfunctor F)
    (U : C) (α : yoneda.obj U ⟶ F) :
    (∃ l : yoneda.obj U ⟶ Z.toFunctor, l ≫ Z.ι = α) ↔ yonedaEquiv α ∈ Z.obj (op U) := by
  constructor
  · rintro ⟨l, hl⟩
    rw [← Subfunctor.ofSection_le_iff, ← Subfunctor.range_eq_ofSection α, ← hl]
    simpa [Subfunctor.range_ι] using Subfunctor.range_comp_le l Z.ι
  · intro h
    have h' : Subfunctor.range α ≤ Z := by simpa [Subfunctor.range_eq_ofSection] using h
    exact ⟨Subfunctor.lift α h', Subfunctor.lift_ι α h'⟩

/-- A finite open pair contains the section induced by `σ`. -/
public def ContainsSection
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y T : AlgebraicGeometry.AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (σ : Y ⟶ X) (hσ : σ.hom ≫ f.hom = 𝟙 Y.obj)
    (p : Space.FiniteOpenSubspace B S hS f T) : Prop :=
  ∃ sectionLift : T.obj ⟶ p.subspace.toFunctor,
    sectionLift ≫ p.subspace.ι =
      pullback.lift (𝟙 T.obj) (p.toBase.hom ≫ σ.hom) (by
        simp only [Category.id_comp, Category.assoc, hσ, Category.comp_id])

/-- Containing the section after restriction is equivalent to factorization of the
restricted section through the original finite open subspace. -/
public theorem containsSection_restrict_iff_factor
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicGeometry.AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (σ : Y ⟶ X) (hσ : σ.hom ≫ f.hom = 𝟙 Y.obj)
    (P : Space.FinitePartPresheaf B S hS f)
    {T T' : AlgebraicGeometry.BigFppfOver B S hS} (h : T' ⟶ T)
    (x : P.toFunctor.obj (op T)) :
    ContainsSection B S hS f σ hσ
        (P.sections T' (P.toFunctor.map h.op x)) ↔
      ∃ l : (schemeSpace T').obj ⟶ (P.sections T x).subspace.toFunctor,
        l ≫ (P.sections T x).subspace.ι =
          (schemeSpaceMap h).hom ≫ pullback.lift
            (𝟙 (schemeSpace T).obj)
            ((P.sections T x).toBase.hom ≫ σ.hom) (by
              simp only [Category.assoc, hσ, Category.id_comp, Category.comp_id]) := by
  classical
  let p := P.sections T x
  let q := P.sections T' (P.toFunctor.map h.op x)
  obtain ⟨hbase, j, hpb, hX⟩ := P.map_isBaseChange h x
  let hmap := (schemeSpaceMap h).hom
  have hbase' : q.toBase.hom = hmap ≫ p.toBase.hom := hbase
  have hpbw : q.subspace.ι ≫ pullback.fst q.toBase.hom f.hom ≫ hmap =
      j ≫ p.subspace.ι ≫ pullback.fst p.toBase.hom f.hom := hpb.w
  let sP := pullback.lift (f := p.toBase.hom) (g := f.hom)
    (𝟙 (schemeSpace T).obj) (p.toBase.hom ≫ σ.hom)
    (by simp only [Category.id_comp, Category.assoc, hσ, Category.comp_id])
  let sQ := pullback.lift (f := q.toBase.hom) (g := f.hom)
    (𝟙 (schemeSpace T').obj) (q.toBase.hom ≫ σ.hom)
    (by simp only [Category.id_comp, Category.assoc, hσ, Category.comp_id])
  have hsPfst : sP ≫ pullback.fst p.toBase.hom f.hom =
      𝟙 (schemeSpace T).obj := pullback.lift_fst _ _ _
  have hsPsnd : sP ≫ pullback.snd p.toBase.hom f.hom =
      p.toBase.hom ≫ σ.hom := pullback.lift_snd _ _ _
  have hsQfst : sQ ≫ pullback.fst q.toBase.hom f.hom =
      𝟙 (schemeSpace T').obj := pullback.lift_fst _ _ _
  have hsQsnd : sQ ≫ pullback.snd q.toBase.hom f.hom =
      q.toBase.hom ≫ σ.hom := pullback.lift_snd _ _ _
  constructor
  · rintro ⟨l, hl⟩
    refine ⟨l ≫ j, ?_⟩
    apply pullback.hom_ext
    · calc
        (l ≫ j) ≫ p.subspace.ι ≫ pullback.fst p.toBase.hom f.hom
            = l ≫ (q.subspace.ι ≫ pullback.fst q.toBase.hom f.hom) ≫
                hmap := by simpa [Category.assoc] using congrArg (fun k => l ≫ k) hpbw.symm
        _ = hmap := by
          change l ≫ q.subspace.ι = sQ at hl
          simpa only [← Category.assoc, hsQfst, Category.id_comp] using
            congrArg (fun k => k ≫ pullback.fst q.toBase.hom f.hom ≫ hmap) hl
        _ = hmap ≫ sP ≫ pullback.fst p.toBase.hom f.hom := by rw [hsPfst, Category.comp_id]
    · calc
        (l ≫ j) ≫ p.subspace.ι ≫ pullback.snd p.toBase.hom f.hom
            = l ≫ (q.subspace.ι ≫ pullback.snd q.toBase.hom f.hom) := by
                simpa [Category.assoc] using congrArg (fun k => l ≫ k) hX
        _ = sQ ≫ pullback.snd q.toBase.hom f.hom :=
              congrArg (fun k => k ≫ pullback.snd q.toBase.hom f.hom) hl
        _ = hmap ≫ sP ≫ pullback.snd p.toBase.hom f.hom := by
              rw [hsQsnd, hbase', Category.assoc, hsPsnd]
  · rintro ⟨l, hl⟩
    have hfirst : 𝟙 (schemeSpace T').obj ≫ hmap =
        l ≫ p.subspace.ι ≫ pullback.fst p.toBase.hom f.hom := by
      have hh := congrArg (fun k => k ≫ pullback.fst p.toBase.hom f.hom) hl.symm
      change hmap ≫ sP ≫ pullback.fst p.toBase.hom f.hom =
        l ≫ p.subspace.ι ≫ pullback.fst p.toBase.hom f.hom at hh
      simpa only [Category.id_comp, ← Category.assoc, hsPfst, Category.comp_id] using hh
    let l' := hpb.lift (𝟙 (schemeSpace T').obj) l hfirst
    refine ⟨l', ?_⟩
    apply pullback.hom_ext
    · calc
        l' ≫ q.subspace.ι ≫ pullback.fst q.toBase.hom f.hom =
            𝟙 (schemeSpace T').obj :=
              hpb.lift_fst (𝟙 (schemeSpace T').obj) l hfirst
        _ = sQ ≫ pullback.fst q.toBase.hom f.hom := by rw [hsQfst]
    · have h₂ := hpb.lift_snd (𝟙 (schemeSpace T').obj) l hfirst
      have hsnd := congrArg (fun k => k ≫ pullback.snd p.toBase.hom f.hom) hl
      calc
        l' ≫ q.subspace.ι ≫ pullback.snd q.toBase.hom f.hom
            = l' ≫ j ≫ p.subspace.ι ≫ pullback.snd p.toBase.hom f.hom := by
                simpa only [Category.assoc] using congrArg (fun k => l' ≫ k) hX.symm
        _ = l ≫ p.subspace.ι ≫ pullback.snd p.toBase.hom f.hom := by
              simpa [Category.assoc] using congrArg
                (fun k => k ≫ p.subspace.ι ≫ pullback.snd p.toBase.hom f.hom) h₂
        _ = hmap ≫ sP ≫ pullback.snd p.toBase.hom f.hom := by
              simpa only [Category.assoc] using hsnd
        _ = hmap ≫ (p.toBase.hom ≫ σ.hom) := by rw [hsPsnd]
        _ = q.toBase.hom ≫ σ.hom := by rw [hbase', Category.assoc]
        _ = sQ ≫ pullback.snd q.toBase.hom f.hom := hsQsnd.symm

/-- The finite-part functor with the condition that its open subspace contains
the given section. The pointwise equivalence fixes the subfunctor uniquely. -/
public structure FinitePartWithSection
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicGeometry.AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (σ : Y ⟶ X) (hσ : σ.hom ≫ f.hom = 𝟙 Y.obj) where
  /-- The subfunctor of finite open pairs whose open subspace contains the section. -/
  toSubfunctor : Subfunctor (Space.finiteOpenSubspacePresheaf B S hS f).toFunctor
  /-- A finite open pair lies in `toSubfunctor` exactly when its open subspace contains the
  section `σ`. -/
  mem_iff : ∀ (T : AlgebraicGeometry.BigFppfOver B S hS)
      (p : (Space.finiteOpenSubspacePresheaf B S hS f).toFunctor.obj (op T)),
    p ∈ toSubfunctor.obj (op T) ↔
      ContainsSection B S hS f σ hσ
        ((Space.finiteOpenSubspacePresheaf B S hS f).sections T p)

/-- The canonical transformation from finite open pairs containing a section
to all finite open pairs, with its pointwise characterization. -/
@[stacks 04RR "the transformation"]
public noncomputable def finitePartWithSection
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicGeometry.AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (σ : Y ⟶ X) (hσ : σ.hom ≫ f.hom = 𝟙 Y.obj) :
    FinitePartWithSection B S hS f σ hσ := by
  classical
  let P := Space.finiteOpenSubspacePresheaf B S hS f
  refine ⟨Subfunctor.mk (fun T x =>
      ContainsSection B S hS f σ hσ (P.sections (Opposite.unop T) x)) ?_, ?_⟩
  · intro A A' g x hx
    obtain ⟨l, hl⟩ : ContainsSection B S hS f σ hσ (P.sections A.unop x) := hx
    exact (containsSection_restrict_iff_factor B S hS f σ hσ P g.unop x).2
      ⟨(schemeSpaceMap g.unop).hom ≫ l, by rw [Category.assoc, hl]⟩
  · intro T x
    rfl

private theorem preimage_finitePartWithSection
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicGeometry.AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (σ : Y ⟶ X) (hσ : σ.hom ≫ f.hom = 𝟙 Y.obj)
    (U : AlgebraicGeometry.BigFppfOver B S hS)
    (g : yoneda.obj U ⟶ (Space.finiteOpenSubspacePresheaf B S hS f).toFunctor) :
    let P := Space.finiteOpenSubspacePresheaf B S hS f
    let x := yonedaEquiv g
    let p := P.sections U x
    let s := pullback.lift (f := p.toBase.hom) (g := f.hom)
      (𝟙 (schemeSpace U).obj) (p.toBase.hom ≫ σ.hom) (by
        simp only [Category.id_comp, Category.assoc, hσ, Category.comp_id])
    (finitePartWithSection B S hS f σ hσ).toSubfunctor.preimage g =
      p.subspace.preimage s := by
  classical
  intro P x p s
  let G := finitePartWithSection B S hS f σ hσ
  let H := G.toSubfunctor
  have hsectionmap (V : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ)
      (z : (yoneda.obj U).obj V) : P.toFunctor.map (z : V.unop ⟶ U).op x =
        g.app V z := by
    have hg : yonedaEquiv.symm x = g := Equiv.symm_apply_apply _ _
    rw [← hg]
    exact (yonedaEquiv_symm_app_apply x V z).symm
  ext V z
  show g.app V z ∈ H.obj V ↔ s.app V z ∈ p.subspace.obj V
  let h : V.unop ⟶ U := z
  have heval : yonedaEquiv ((schemeSpaceMap h).hom ≫ s) = s.app V z := by
    rw [yonedaEquiv_apply]
    dsimp [schemeSpaceMap, schemeSpace]
    show s.app V ((yoneda.map h).app V (𝟙 (V.unop))) = s.app V z
    simp [h]
  rw [← hsectionmap]
  calc
    P.toFunctor.map h.op x ∈ H.obj V ↔
        ContainsSection B S hS f σ hσ (P.sections V.unop (P.toFunctor.map h.op x)) :=
      G.mem_iff V.unop (P.toFunctor.map h.op x)
    _ ↔ ∃ l, l ≫ p.subspace.ι = (schemeSpaceMap h).hom ≫ s :=
      containsSection_restrict_iff_factor B S hS f σ hσ P h x
    _ ↔ yonedaEquiv ((schemeSpaceMap h).hom ≫ s) ∈ p.subspace.obj V :=
      yoneda_subfunctor_lift_iff p.subspace V.unop _
    _ ↔ s.app V z ∈ p.subspace.obj V := by rw [heval]

private theorem presheaf_ι_of_preimage
    {C : Type (u + 1)} [Category.{u} C] {F : Cᵒᵖ ⥤ Type u}
    (Q : MorphismProperty C) [Q.RespectsIso] [Q.presheaf.IsStableUnderBaseChange]
    (H : Subfunctor F)
    (h : ∀ (U : C) (g : yoneda.obj U ⟶ F), Q.presheaf ((H.preimage g).ι)) :
    Q.presheaf H.ι := by
  apply MorphismProperty.relative.of_exists (F := yoneda) (P := Q)
  intro U g
  let idU : yoneda.obj U ⟶ yoneda.obj U := 𝟙 _
  let i := (h U g).1.fst idU
  let j := (h U g).1.snd idU
  have hpb : IsPullback i (yoneda.map j) (H.preimage g).ι idU := (h U g).1.isPullback idU
  exact ⟨(h U g).1.pullback idU, i ≫ H.fromPreimage g, j,
    hpb.paste_horiz (Subfunctor.isPullback_preimage g H), (h U g).2 idU i j hpb⟩

private theorem finitePartWithSection_property
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicGeometry.AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (σ : Y ⟶ X) (hσ : σ.hom ≫ f.hom = 𝟙 Y.obj)
    (Q : MorphismProperty (AlgebraicGeometry.BigFppfOver B S hS))
    [Q.RespectsIso] [Q.presheaf.IsStableUnderBaseChange]
    (hp : ∀ (U : AlgebraicGeometry.BigFppfOver B S hS)
      (p : Space.FiniteOpenSubspace B S hS f (schemeSpace U)),
      Q.presheaf p.subspace.ι) :
    Q.presheaf (finitePartWithSection B S hS f σ hσ).toSubfunctor.ι := by
  classical
  refine presheaf_ι_of_preimage Q (finitePartWithSection B S hS f σ hσ).toSubfunctor ?_
  intro U g
  let p := (Space.finiteOpenSubspacePresheaf B S hS f).sections U (yonedaEquiv g)
  let s := pullback.lift (f := p.toBase.hom) (g := f.hom)
    (𝟙 (schemeSpace U).obj) (p.toBase.hom ≫ σ.hom)
    (by simp only [Category.id_comp, Category.assoc, hσ, Category.comp_id])
  rw [preimage_finitePartWithSection B S hS f σ hσ U g]
  exact Q.presheaf.of_isPullback (Subfunctor.isPullback_preimage s p.subspace) (hp U p)

/-- The transformation is representable by open immersions. -/
@[stacks 04RR "part (1)"]
public theorem isOpenImmersion_finitePartWithSection
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicGeometry.AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (σ : Y ⟶ X) (hσ : σ.hom ≫ f.hom = 𝟙 Y.obj) :
    Space.IsOpenImmersion B S hS
      (finitePartWithSection B S hS f σ hσ).toSubfunctor.ι := by
  classical
  let Q := MorphismProperty.inverseImage (@AlgebraicGeometry.IsOpenImmersion.{u} :
    MorphismProperty Scheme.{u}) (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  have : Q.presheaf.IsStableUnderBaseChange := MorphismProperty.relative_isStableUnderBaseChange Q
  exact finitePartWithSection_property B S hS f σ hσ Q (fun _ p => p.isOpen.2)

/-- For separated `f`, the same transformation is representable by closed
immersions as well as open immersions. -/
@[stacks 04RR "part (2)"]
public theorem isClosedImmersion_finitePartWithSection
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicGeometry.AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (σ : Y ⟶ X) (hσ : σ.hom ≫ f.hom = 𝟙 Y.obj)
    (hf : Space.IsSeparated B S hS f.hom) :
    Space.IsClosedImmersion B S hS
      (finitePartWithSection B S hS f σ hσ).toSubfunctor.ι := by
  classical
  let Q := MorphismProperty.inverseImage (@AlgebraicGeometry.IsClosedImmersion.{u} :
    MorphismProperty Scheme.{u}) (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  have := AlgebraicGeometry.IsClosedImmersion.respectsIso
  have : Q.RespectsIso := MorphismProperty.RespectsIso.inverseImage _ _
  have : Q.presheaf.IsStableUnderBaseChange := MorphismProperty.relative_isStableUnderBaseChange Q
  exact finitePartWithSection_property B S hS f σ hσ Q
    (fun U p => (Space.FiniteOpenSubspace.isClosedSubspace B S hS f
      (schemeSpace U) p hf).2)

/-- If the finite-part functor is an algebraic space, the section-containing
subfunctor is an open algebraic subspace of it. -/
@[stacks 04RR "part (3)"]
public theorem isOpenSubspace_finitePartWithSection
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicGeometry.AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (σ : Y ⟶ X) (hσ : σ.hom ≫ f.hom = 𝟙 Y.obj)
    (hfin : AlgebraicGeometry.IsAlgebraicSpace B S hS
      (Space.finiteOpenSubspacePresheaf B S hS f).toFunctor) :
    Space.IsOpenSubspace B S hS
      (finitePartWithSection B S hS f σ hσ).toSubfunctor :=
  ⟨AlgebraicGeometry.isAlgebraicSpace_of_relativelyRepresentable B S hS _
    (isOpenImmersion_finitePartWithSection B S hS f σ hσ).1 hfin,
    isOpenImmersion_finitePartWithSection B S hS f σ hσ⟩

/-- A scheme representing the finite-part functor contains the
section-containing functor as a compatible open subscheme. -/
@[stacks 04RR "part (4)"]
public theorem openSubscheme_finitePartWithSection
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicGeometry.AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (σ : Y ⟶ X) (hσ : σ.hom ≫ f.hom = 𝟙 Y.obj)
    (V : AlgebraicGeometry.BigFppfOver B S hS)
    (e : yoneda.obj V ≅
      (Space.finiteOpenSubspacePresheaf B S hS f).toFunctor) :
    ∃ (U : AlgebraicGeometry.BigFppfOver B S hS) (i : U ⟶ V)
      (e' : yoneda.obj U ≅
        (finitePartWithSection B S hS f σ hσ).toSubfunctor.toFunctor),
      AlgebraicGeometry.IsOpenImmersion
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map i) ∧
      yoneda.map i ≫ e.hom =
        e'.hom ≫ (finitePartWithSection B S hS f σ hσ).toSubfunctor.ι := by
  classical
  have hO := isOpenImmersion_finitePartWithSection B S hS f σ hσ
  let a := hO.1.fst e.hom
  let i := hO.1.snd e.hom
  have hpb := hO.1.isPullback e.hom
  have : IsIso a := hpb.isIso_fst_of_isIso
  exact ⟨hO.1.pullback e.hom, i, asIso a, hO.2 e.hom a i hpb, hpb.w.symm⟩

end AlgebraicGeometry.Space

end
