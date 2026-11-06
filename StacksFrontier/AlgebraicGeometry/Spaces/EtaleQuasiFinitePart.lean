module

public import Mathlib.CategoryTheory.Subfunctor.Image
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PropertyGammaPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSplitQuasiFinitePart
public import StacksFrontier.AlgebraicGeometry.Spaces.Finite
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoveringPoints
public import StacksFrontier.AlgebraicGeometry.Topologies.BigFppfOverTypeSheafification

/-!
# Étale splitting of one quasi-finite part

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is separated and
locally of finite type, and let `x` be a point of `|X|` at which `f` is quasi-finite. Then there
is an étale morphism `g : U ⟶ Y` of algebraic spaces over `S` and a point `u` of `|U|` with the
same image in `|Y|` as `x`, such that the fibre product `U ×_Y X` splits as a disjoint union of
two open-and-closed subspaces `W` and `V` with `V ⟶ U` finite, where `V` carries a point lying
over `x` and over `u`.

The splitting isolates the quasi-finite point: after the étale base change `g` the part of the
fibre product near `x` becomes finite over the base, while the rest is cut off into the
complementary clopen piece `W`.

## Main results

* `AlgebraicGeometry.Space.exists_etale_finite_clopen_part` is Stacks 0ADU: the étale
  neighbourhood, the complementary open-and-closed subspaces, the finiteness of the part
  containing the chosen point, and the compatible points over `x` and `u`.

## Implementation notes

The decomposition is expressed by complementary subfunctors of the presheaf fibre product: the
sheafification of their supremum is the whole pullback and their infimum is the sheafification of
the empty subfunctor. Both subfunctors are open and closed, and the projections composed with
their inclusions are the canonical maps of the decomposition.

The statement is deduced from Stacks 082H
(`AlgebraicGeometry.Space.exists_etale_decomposition_isFinite_of_isQuasiFiniteAt`), which carries
the extra hypothesis that `f` be quasi-compact or that `Y` be decent. That hypothesis is
discharged by first replacing `Y` by a scheme chart `A ⟶ Y` through which `x` is hit on points: a
presheaf represented by an object of the big fppf category over `S` is a decent algebraic space,
so Stacks 082H applies to the base change of `f` along the chart. The resulting decomposition
lives over the fibre product `U ×_A (A ×_Y X)`, and the associativity and symmetry isomorphisms of
fibre products transport it to `U ×_Y X`; the transport is carried out subfunctor by subfunctor,
because openness, closedness, finiteness and the two sheafification identities all have to be
moved across the isomorphism.

The point of `V` over `x` is produced from the fact that the two clopen pieces cover the points of
the fibre product, together with the clause of Stacks 082H forbidding the complementary piece `W`
from meeting the fibre over `u` in a point above `x`.

## References

* [Stacks Project, Tag 0ADU](https://stacks.math.columbia.edu/tag/0ADU)
* [Stacks Project, Tag 082H](https://stacks.math.columbia.edu/tag/082H)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.Space

/- Instance search for pullbacks of presheaves on `BigFppfOver B S hS` times out under Lean
v4.35.0; supply the functor-category instances. -/
local instance (priority := high) {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  functorCategoryHasLimitsOfShape

local instance (priority := high) {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {Y Z W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : Y ⟶ W) (g : Z ⟶ W) : HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit (cospan f g)

local instance (priority := high) {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (J : Type) : HasLimitsOfShape (Discrete J) ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  functorCategoryHasLimitsOfShape

/-- The preimage of a subfunctor along the inverse of an isomorphism of presheaves is isomorphic
to the subfunctor itself. -/
private def subfunctorPreimageIso
    {C : Type v} [Category.{w} C] {F G : Cᵒᵖ ⥤ Type u}
    (e : F ≅ G) (W : Subfunctor F) :
    (W.preimage e.inv).toFunctor ≅ W.toFunctor := by
  have hrange : Subfunctor.range (W.ι ≫ e.hom) ≤ W.preimage e.inv := by
    intro T z hz
    rcases hz with ⟨x, rfl⟩
    change e.inv.app T (e.hom.app T (W.ι.app T x)) ∈ W.obj T
    simpa using x.property
  refine ⟨W.fromPreimage e.inv, Subfunctor.lift (W.ι ≫ e.hom) hrange, ?_, ?_⟩
  · ext T x
    apply Subtype.ext
    change e.hom.app T (e.inv.app T x.1) = x.1
    simp
  · ext T x
    apply Subtype.ext
    change e.inv.app T (e.hom.app T x.1) = x.1
    simp

private lemma subfunctorPreimageIso_hom_ι_comp {C : Type v} [Category.{w} C]
    {F G : Cᵒᵖ ⥤ Type u} (e : F ≅ G) (W : Subfunctor F) :
    (subfunctorPreimageIso e W).hom ≫ W.ι ≫ e.hom = (W.preimage e.inv).ι := by
  simpa [subfunctorPreimageIso, Category.assoc] using
    congrArg (fun a => a ≫ e.hom) (Subfunctor.fromPreimage_ι W e.inv)

/-- A subspace whose inclusion satisfies an isomorphism-stable property keeps both after taking
its preimage along the inverse of an isomorphism of presheaves. -/
private theorem subspace_preimage_iso
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (Q : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) [Q.RespectsIso]
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ≅ G) (W : Subfunctor F)
    (hW : IsAlgebraicSpace B S hS W.toFunctor ∧ Q W.ι) :
    IsAlgebraicSpace B S hS (W.preimage e.inv).toFunctor ∧ Q (W.preimage e.inv).ι := by
  let wIso := subfunctorPreimageIso e W
  exact ⟨_root_.AlgebraicGeometry.isAlgebraicSpace_of_iso B S hS wIso hW.1,
    subfunctorPreimageIso_hom_ι_comp e W ▸
      MorphismProperty.RespectsIso.postcomp Q e.hom _
        (MorphismProperty.RespectsIso.precomp Q wIso.hom W.ι hW.2)⟩

/-- An open subspace stays an open subspace after taking its preimage along the inverse of an
isomorphism of presheaves. -/
private theorem openSubspace_preimage_iso
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ≅ G)
    (W : Subfunctor F) (hW : IsOpenSubspace B S hS W) :
    IsOpenSubspace B S hS (W.preimage e.inv) :=
  subspace_preimage_iso B S hS _ e W hW

/-- A closed subspace stays a closed subspace after taking its preimage along the inverse of an
isomorphism of presheaves. -/
private theorem closedSubspace_preimage_iso
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ≅ G)
    (W : Subfunctor F) (hW : IsClosedSubspace B S hS W) :
    IsClosedSubspace B S hS (W.preimage e.inv) :=
  subspace_preimage_iso B S hS (closedImmersionPresheafProperty B S hS) e W hW

/-- Precomposing a finite morphism of algebraic spaces with an isomorphism keeps it finite. -/
private theorem finite_precomp_iso
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ≅ G)
    (m : G ⟶ T) (hm : IsFinite B S hS m)
    (m' : F ⟶ T) (hcomp : e.hom ≫ m = m') :
    IsFinite B S hS m' := by
  subst hcomp
  intro U hU ξ
  obtain ⟨V, p, i, hV, hfin, sq⟩ := hm U hU ξ
  refine ⟨V, p, i ≫ e.inv, hV, hfin, ?_⟩
  have hcomm : (i ≫ e.inv) ≫ e.hom ≫ m = yoneda.map p ≫ ξ := by simpa using sq.w
  have hc : ∀ c : PullbackCone (e.hom ≫ m) ξ, (c.fst ≫ e.hom) ≫ m = c.snd ≫ ξ := fun c => by
    simpa using c.condition
  refine IsPullback.of_isLimit' (CommSq.mk hcomm) ?_
  refine PullbackCone.IsLimit.mk hcomm (fun c => sq.lift (c.fst ≫ e.hom) c.snd (hc c))
    (fun c => by simp) (fun c => by simp) fun c l hl₁ hl₂ => ?_
  apply sq.hom_ext
  · simp [← hl₁]
  · simp [hl₂]

/-- Sheafification of a subfunctor commutes with taking preimages along the inverse of an
isomorphism between two sheaves. -/
private theorem sheafify_preimage_iso
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {F G : Cᵒᵖ ⥤ Type w} (hF : Presieve.IsSheaf J F)
    (hG : Presieve.IsSheaf J G) (e : F ≅ G) (A : Subfunctor F) :
    (A.preimage e.inv).sheafify J = (A.sheafify J).preimage e.inv := by
  have hpre : ∀ {F' G' : Cᵒᵖ ⥤ Type w} (e' : F' ≅ G') (D : Subfunctor F'),
      Presieve.IsSheaf J D.toFunctor → Presieve.IsSheaf J (D.preimage e'.inv).toFunctor :=
    fun e' D hD => (isSheaf_iff_isSheaf_of_type J _).1
      ((Presheaf.isSheaf_of_iso_iff (subfunctorPreimageIso e' D)).mpr
        ((isSheaf_iff_isSheaf_of_type J D.toFunctor).2 hD))
  have hApre : Presieve.IsSheaf J (((A.sheafify J).preimage e.inv).toFunctor) :=
    hpre e _ (A.sheafify_isSheaf hF)
  have hBpre : Presieve.IsSheaf J
      ((((A.preimage e.inv).sheafify J).preimage e.hom).toFunctor) :=
    hpre e.symm _ ((A.preimage e.inv).sheafify_isSheaf hG)
  have hAB : A ≤ ((A.preimage e.inv).sheafify J).preimage e.hom := by
    intro U x hx
    show e.hom.app U x ∈ ((A.preimage e.inv).sheafify J).obj U
    apply (A.preimage e.inv).le_sheafify J
    show e.inv.app U (e.hom.app U x) ∈ A.obj U
    simpa using hx
  have hclose : A.sheafify J ≤ ((A.preimage e.inv).sheafify J).preimage e.hom :=
    Subfunctor.sheafify_le (J := J) (G := A) (G' := _)
      hAB hF hBpre
  apply le_antisymm
  · apply Subfunctor.sheafify_le (J := J) (G := A.preimage e.inv) (G' := _)
      (fun U x hx => ?_) hG hApre
    change e.inv.app U x ∈ A.obj U at hx
    show e.inv.app U x ∈ (A.sheafify J).obj U
    exact (A.le_sheafify J U) hx
  · intro U x hx
    change e.inv.app U x ∈ (A.sheafify J).obj U at hx
    have hmem := hclose U hx
    change e.hom.app U (e.inv.app U x) ∈ ((A.preimage e.inv).sheafify J).obj U at hmem
    simpa using hmem

private theorem range_sigmaDesc_ite_ι
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (W V : Subfunctor F) :
    Subfunctor.range (Sigma.desc fun b : ULift.{u} Bool => (if b.down then V else W).ι) =
      W ⊔ V := by
  apply le_antisymm
  · let d : (∐ fun b : ULift.{u} Bool => (if b.down then V else W).toFunctor) ⟶
        (W ⊔ V).toFunctor :=
      Sigma.desc fun b => Subfunctor.homOfLe (by
        cases b with
        | up b => cases b <;> simp)
    have hfactor : d ≫ (W ⊔ V).ι =
        Sigma.desc fun b : ULift.{u} Bool => (if b.down then V else W).ι := by
      apply Sigma.hom_ext
      intro b
      simp [d]
    rw [← hfactor]
    exact Subfunctor.range_comp_le _ _ |>.trans (by simp)
  · have h : ∀ b : ULift.{u} Bool, Subfunctor.range (if b.down then V else W).ι ≤
        Subfunctor.range (Sigma.desc fun b : ULift.{u} Bool => (if b.down then V else W).ι) :=
      fun b => by
        simpa using Subfunctor.range_comp_le
          (Sigma.ι (fun b : ULift.{u} Bool => (if b.down then V else W).toFunctor) b)
          (Sigma.desc fun b : ULift.{u} Bool => (if b.down then V else W).ι)
    exact sup_le (by simpa using h (.up false)) (by simpa using h (.up true))

/-- Two open subspaces whose supremum sheafifies to everything cover the points of the ambient
algebraic space. -/
private theorem point_lifts_to_clopen_partition
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F)
    (W V : Subfunctor F) (hWo : IsOpenSubspace B S hS W)
    (hVo : IsOpenSubspace B S hS V)
    (hparts : (W ⊔ V).sheafify (BigFppfOver.topology B S hS) = ⊤)
    (z : points B S hS F) :
    (∃ w : points B S hS W.toFunctor, pointsMap B S hS W.toFunctor W.ι w = z) ∨
    (∃ v : points B S hS V.toFunctor, pointsMap B S hS V.toFunctor V.ι v = z) := by
  let pieces : ULift.{u} Bool → Subfunctor F := fun b => if b.down then V else W
  have hpiecesOpen : ∀ b, IsOpenSubspace B S hS (pieces b) := by
    rintro ⟨_ | _⟩ <;> simpa [pieces]
  have hrange : Subfunctor.range (Sigma.desc fun b => (pieces b).ι) = W ⊔ V :=
    range_sigmaDesc_ite_ι B S hS W V
  have hloc : Presheaf.IsLocallySurjective
      (BigFppfOver.topology B S hS)
      (Sigma.desc fun b => (pieces b).ι) := by
    rwa [Presheaf.isLocallySurjective_iff_range_sheafify_eq_top', hrange]
  have hpoints := (isZariskiCover_iff_iUnion_points B S hS F hF (ULift.{u} Bool) pieces
    hpiecesOpen).mp ⟨hpiecesOpen, hloc⟩
  have hz : z ∈ ⋃ b, Set.range
      (pointsMap B S hS (pieces b).toFunctor (pieces b).ι) := hpoints ▸ Set.mem_univ z
  obtain ⟨⟨_ | _⟩, hb⟩ := Set.mem_iUnion.mp hz
  exacts [Or.inl hb, Or.inr hb]

/-- The two sheafification identities of a clopen decomposition are inherited by the preimages of
the two pieces along the inverse of an isomorphism of sheaves. -/
private theorem sheafify_decomposition_preimage
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presieve.IsSheaf (BigFppfOver.topology B S hS) F)
    (hG : Presieve.IsSheaf (BigFppfOver.topology B S hS) G)
    (e : F ≅ G) (W V : Subfunctor F)
    (hparts : (W ⊔ V).sheafify (BigFppfOver.topology B S hS) = ⊤)
    (hdisj : W ⊓ V = (⊥ : Subfunctor F).sheafify (BigFppfOver.topology B S hS)) :
    (W.preimage e.inv ⊔ V.preimage e.inv).sheafify (BigFppfOver.topology B S hS) = ⊤ ∧
      W.preimage e.inv ⊓ V.preimage e.inv =
        (⊥ : Subfunctor G).sheafify (BigFppfOver.topology B S hS) := by
  let J := BigFppfOver.topology B S hS
  have hsupPre : (W ⊔ V).preimage e.inv = W.preimage e.inv ⊔ V.preimage e.inv := by
    ext
    simp
  refine ⟨?_, ?_⟩
  · calc
      (W.preimage e.inv ⊔ V.preimage e.inv).sheafify J
          = ((W ⊔ V).preimage e.inv).sheafify J := by rw [hsupPre]
      _ = ((W ⊔ V).sheafify J).preimage e.inv :=
        sheafify_preimage_iso J hF hG e (W ⊔ V)
      _ = (⊤ : Subfunctor F).preimage e.inv := by rw [hparts]
      _ = ⊤ := by
        ext
        simp
  · calc
      W.preimage e.inv ⊓ V.preimage e.inv = (W ⊓ V).preimage e.inv := by
        ext
        simp
      _ = ((⊥ : Subfunctor F).sheafify J).preimage e.inv := by rw [hdisj]
      _ = ((⊥ : Subfunctor F).preimage e.inv).sheafify J :=
        (sheafify_preimage_iso J hF hG e (⊥ : Subfunctor F)).symm
      _ = (⊥ : Subfunctor G).sheafify J := by congr 1

/-- Finiteness of a piece of a clopen decomposition over a fixed presheaf, and a point of that
piece with prescribed images under two morphisms, are inherited by the preimage of the piece along
the inverse of an isomorphism of presheaves. -/
private theorem isFinite_preimage_and_exists_point
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G T₁ T₂ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ≅ G)
    (V : Subfunctor F) (a : G ⟶ T₁) (b : G ⟶ T₂) (m₁ : F ⟶ T₁) (m₂ : F ⟶ T₂)
    (ha : e.hom ≫ a = m₁) (hb : e.hom ≫ b = m₂)
    (hfinite : IsFinite B S hS (V.ι ≫ m₁))
    (z : points B S hS F) (v₀ : points B S hS V.toFunctor)
    (hvQ : pointsMap B S hS V.toFunctor V.ι v₀ = z) :
    IsFinite B S hS ((V.preimage e.inv).ι ≫ a) ∧
      ∃ v : points B S hS (V.preimage e.inv).toFunctor,
        pointsMap B S hS (V.preimage e.inv).toFunctor ((V.preimage e.inv).ι ≫ b) v =
            pointsMap B S hS F m₂ z ∧
          pointsMap B S hS (V.preimage e.inv).toFunctor ((V.preimage e.inv).ι ≫ a) v =
            pointsMap B S hS F m₁ z := by
  subst ha hb
  let V' := V.preimage e.inv
  let vIso := subfunctorPreimageIso e V
  have hV : vIso.hom ≫ V.ι ≫ e.hom = V'.ι := subfunctorPreimageIso_hom_ι_comp e V
  have hVinv : vIso.inv ≫ V'.ι = V.ι ≫ e.hom := by
    rw [← hV]
    simp
  refine ⟨finite_precomp_iso B S hS vIso _ hfinite _ (by
    rw [← hV]
    simp), ?_⟩
  let v' := pointsMap B S hS V.toFunctor vIso.inv v₀
  have hvR : pointsMap B S hS V'.toFunctor V'.ι v' = pointsMap B S hS F e.hom z := by
    calc
      _ = pointsMap B S hS V.toFunctor (vIso.inv ≫ V'.ι) v₀ := by
        rw [pointsMap_comp_apply]
      _ = pointsMap B S hS V.toFunctor (V.ι ≫ e.hom) v₀ := by rw [hVinv]
      _ = pointsMap B S hS F e.hom (pointsMap B S hS V.toFunctor V.ι v₀) :=
        pointsMap_comp_apply B S hS V.ι e.hom v₀
      _ = pointsMap B S hS F e.hom z := by rw [hvQ]
  exact ⟨v', by rw [pointsMap_comp_apply B S hS V'.ι b v', hvR, pointsMap_comp_apply],
    by rw [pointsMap_comp_apply B S hS V'.ι a v', hvR, pointsMap_comp_apply]⟩

private theorem exists_iso_pullback_comp {C : Type v} [Category.{w} C] [HasPullbacks C]
    {X Y A A₁ : C} (f : X ⟶ Y) (g : A ⟶ Y) (k : A₁ ⟶ A) :
    ∃ e : pullback k (pullback.snd f g) ≅ pullback (k ≫ g) f,
      e.hom ≫ pullback.fst (k ≫ g) f = pullback.fst k (pullback.snd f g) ∧
      e.hom ≫ pullback.snd (k ≫ g) f = pullback.snd k (pullback.snd f g) ≫ pullback.fst f g :=
  ⟨pullbackSymmetry _ _ ≪≫ pullbackLeftPullbackSndIso f g k ≪≫ pullbackSymmetry _ _,
    by simp, by simp⟩

/-- A clopen decomposition with a finite piece avoiding a point on its complement is carried along
an isomorphism of algebraic spaces compatible with two morphisms. -/
private theorem exists_clopen_part_of_iso
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G T₁ T₂ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G) (e : F ≅ G)
    (a : G ⟶ T₁) (b : G ⟶ T₂) (m₁ : F ⟶ T₁) (m₂ : F ⟶ T₂)
    (ha : e.hom ≫ a = m₁) (hb : e.hom ≫ b = m₂) (W V : Subfunctor F)
    (hWo : IsOpenSubspace B S hS W) (hWc : IsClosedSubspace B S hS W)
    (hVo : IsOpenSubspace B S hS V) (hVc : IsClosedSubspace B S hS V)
    (hparts : (W ⊔ V).sheafify (BigFppfOver.topology B S hS) = ⊤)
    (hdisj : W ⊓ V = (⊥ : Subfunctor F).sheafify (BigFppfOver.topology B S hS))
    (hfinite : IsFinite B S hS (V.ι ≫ m₁)) (z : points B S hS F)
    (hz : ∀ w : points B S hS W.toFunctor, pointsMap B S hS W.toFunctor W.ι w ≠ z) :
    ∃ W' V' : Subfunctor G,
      IsOpenSubspace B S hS W' ∧ IsClosedSubspace B S hS W' ∧
      IsOpenSubspace B S hS V' ∧ IsClosedSubspace B S hS V' ∧
      (W' ⊔ V').sheafify (BigFppfOver.topology B S hS) = ⊤ ∧
      W' ⊓ V' = (⊥ : Subfunctor G).sheafify (BigFppfOver.topology B S hS) ∧
      IsFinite B S hS (V'.ι ≫ a) ∧
      ∃ v : points B S hS V'.toFunctor,
        pointsMap B S hS V'.toFunctor (V'.ι ≫ b) v = pointsMap B S hS F m₂ z ∧
        pointsMap B S hS V'.toFunctor (V'.ι ≫ a) v = pointsMap B S hS F m₁ z := by
  obtain ⟨v₀, hvQ⟩ := (point_lifts_to_clopen_partition B S hS F hF W V hWo hVo hparts
    z).resolve_left fun ⟨w, hw⟩ => hz w hw
  obtain ⟨hparts', hdisj'⟩ := sheafify_decomposition_preimage B S hS
    ((isSheaf_iff_isSheaf_of_type _ F).1 hF.isSheaf)
    ((isSheaf_iff_isSheaf_of_type _ G).1 hG.isSheaf) e W V hparts hdisj
  exact ⟨W.preimage e.inv, V.preimage e.inv, openSubspace_preimage_iso B S hS e W hWo,
    closedSubspace_preimage_iso B S hS e W hWc, openSubspace_preimage_iso B S hS e V hVo,
    closedSubspace_preimage_iso B S hS e V hVc, hparts', hdisj',
    isFinite_preimage_and_exists_point B S hS e V a b m₁ m₂ ha hb hfinite z v₀ hvQ⟩

/-- **Stacks 0ADU.** An étale neighbourhood of the image of `x` splits the pullback into two
open-and-closed parts, one of them finite over the neighbourhood and containing a point above
`x`. -/
@[stacks 0ADU]
public theorem exists_etale_finite_clopen_part
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (x : points B S hS X.1)
    (hft : IsLocallyOfFiniteType B S hS f.hom)
    (hsep : IsSeparated B S hS f.hom)
    (hqf : IsQuasiFiniteAt B S hS f.hom x) :
    ∃ (U : AlgebraicSpaces B S hS) (g : U ⟶ Y)
      (u : points B S hS U.1)
      (W V : Subfunctor (pullback g.hom f.hom)),
      IsEtale B S hS g.hom ∧
      pointsMap B S hS U.1 g.hom u = pointsMap B S hS X.1 f.hom x ∧
      IsOpenSubspace B S hS W ∧
      IsClosedSubspace B S hS W ∧
      IsOpenSubspace B S hS V ∧
      IsClosedSubspace B S hS V ∧
      (W ⊔ V).sheafify (BigFppfOver.topology B S hS) = ⊤ ∧
      W ⊓ V = (⊥ : Subfunctor (pullback g.hom f.hom)).sheafify
        (BigFppfOver.topology B S hS) ∧
      IsFinite B S hS (V.ι ≫ pullback.fst g.hom f.hom) ∧
      ∃ v : points B S hS V.toFunctor,
        pointsMap B S hS V.toFunctor (V.ι ≫ pullback.snd g.hom f.hom) v = x ∧
        pointsMap B S hS V.toFunctor (V.ι ≫ pullback.fst g.hom f.hom) v = u := by
  classical
  let _ := BigFppfOver.hasSheafify_type B S hS
  have hY := Y.property
  obtain ⟨A, φ, hsurj, heta⟩ := hY.exists_atlas
  obtain ⟨u₀, hu₀⟩ :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS Y.1 hY A φ).mp hsurj
      (pointsMap B S hS X.1 f.hom x)
  -- A scheme chart of `Y` is a decent algebraic space, which is what Stacks 082H needs.
  let Aspace : AlgebraicSpaces B S hS := ⟨yoneda.obj A, isAlgebraicSpace_yoneda B S hS A⟩
  let g : Aspace ⟶ Y := ObjectProperty.homMk φ
  let P := AlgebraicSpaces.fiberProduct B S hS f g
  let p : P ⟶ Aspace := ObjectProperty.homMk (pullback.snd f.hom g.hom)
  let q : P ⟶ X := ObjectProperty.homMk (pullback.fst f.hom g.hom)
  have hcart : IsPullback q p f g := AlgebraicSpaces.isPullback_fiberProduct B S hS f g
  obtain ⟨x', hxA, hxX⟩ := exists_point_of_isPullback B S hS hcart.flip u₀ x hu₀
  have hqfP : IsQuasiFiniteAt B S hS p.hom x' := by
    show x' ∈ {z | IsQuasiFiniteAt B S hS p.hom z}
    rw [setOf_isQuasiFiniteAt_eq_preimage_of_isPullback B S hS hcart hft]
    show pointsMap B S hS P.1 q.hom x' ∈ {z | IsQuasiFiniteAt B S hS f.hom z}
    simpa [hxX] using hqf
  obtain ⟨A₁, k, u₁, W, V, hke, hku, hWo, hWc, hVo, hVc, hparts, hdisj,
      hfinite, -, hWpoints⟩ :=
    exists_etale_decomposition_isFinite_of_isQuasiFiniteAt B S hS P.property Aspace.property
      p.hom u₀ (fun _ : Fin 1 => x') (fun _ => hxA)
      ((isLocallyOfFiniteType_isStableUnderBaseChange B S hS).of_isPullback hcart hft)
      (isSeparated_pullback B S hS f.hom g.hom hsep) (fun _ => hqfP)
      (Or.inr (isDecentSpace_yoneda B S hS A))
  let U₁ : AlgebraicSpaces B S hS := ⟨yoneda.obj A₁, isAlgebraicSpace_yoneda B S hS A₁⟩
  let kS : U₁ ⟶ Aspace := ObjectProperty.homMk k
  let g' : U₁ ⟶ Y := kS ≫ g
  obtain ⟨z, hzU, hzP⟩ := exists_point_of_isPullback B S hS
    (AlgebraicSpaces.isPullback_fiberProduct B S hS kS p) u₁ x' (hku.trans hxA.symm)
  change points B S hS (pullback k p.hom) at z
  change pointsMap B S hS (pullback k p.hom) (pullback.fst k p.hom) z = u₁ at hzU
  change pointsMap B S hS (pullback k p.hom) (pullback.snd k p.hom) z = x' at hzP
  obtain ⟨e, eFst, eSnd⟩ : ∃ e : pullback k p.hom ≅ pullback g'.hom f.hom,
      e.hom ≫ pullback.fst g'.hom f.hom = pullback.fst k p.hom ∧
      e.hom ≫ pullback.snd g'.hom f.hom = pullback.snd k p.hom ≫ pullback.fst f.hom g.hom :=
    exists_iso_pullback_comp f.hom g.hom k
  obtain ⟨W', V', hW'o, hW'c, hV'o, hV'c, hparts', hdisj', hfinite', v', hv'snd, hv'fst⟩ :=
    exists_clopen_part_of_iso B S hS
      (_root_.AlgebraicGeometry.isAlgebraicSpace_pullback B S hS k p.hom U₁.property
        P.property Aspace.property)
      (_root_.AlgebraicGeometry.isAlgebraicSpace_pullback B S hS g'.hom f.hom U₁.property
        X.property Y.property)
      e _ _ _ _ eFst eSnd W V hWo hWc hVo hVc hparts hdisj hfinite z fun w hw =>
        hWpoints w (by rw [pointsMap_comp_apply, hw, hzU]) 0
          (by rw [pointsMap_comp_apply, hw, hzP])
  refine ⟨U₁, g', u₁, W', V', ?_, ?_, hW'o, hW'c, hV'o, hV'c, hparts', hdisj', hfinite', v', ?_,
    hv'fst.trans hzU⟩
  · show IsEtale B S hS (k ≫ g.hom)
    exact isEtale_comp B S hS hke ((isEtale_iff_presheaf_of_yoneda B S hS φ).mpr heta)
  · refine (pointsMap_comp_apply B S hS k g.hom u₁).trans ?_
    rw [hku]
    exact hu₀
  · refine hv'snd.trans <| (pointsMap_comp_apply B S hS (pullback.snd k p.hom)
      (pullback.fst f.hom g.hom) z).trans ?_
    rw [hzP]
    exact hxX

end AlgebraicGeometry.Space

end
