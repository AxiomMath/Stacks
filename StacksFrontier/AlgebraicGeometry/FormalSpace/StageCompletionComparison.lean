module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionCofinalColimit
public import StacksFrontier.AlgebraicGeometry.FormalSpace.StageComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemePointsAffineHom

/-!
# The stage comparison as a natural isomorphism over the formal spectrum

Let `R` be a topological ring presenting an affine formal algebraic space `Spf R` over `S`, let
`v : V ⟶ Spf R` be a morphism from an affine formal algebraic space which is representable by
algebraic spaces and étale, let `J₀ ⊆ R` be a weak ideal of definition, let
`A = stageLiftAlgebra` be the chosen étale `R`-algebra and let `A^∧` be its completion over `R`.
`AlgebraicGeometry.FormalSpace.stageComparison` identifies `A ⧸ JA` with the coordinate ring
`Ā_J` of the chosen affine model of `Spec (R ⧸ J) ×_{Spf R} V`, for every weak ideal of
definition `J ⊆ J₀`, compatibly with the stage transitions. This file turns that family of ring
isomorphisms into an isomorphism of *diagrams of sheaves*

`Spec (R ⧸ J) ×_{Spf R} V ≅ Spec (A^∧ ⧸ ker (A^∧ → A ⧸ JA))`,

natural in `J ⊆ J₀`, **and over `Spf R`**: the composite of a stage of it with the inclusion of
that quotient stage of `A^∧` into `Spf A^∧` and with `Spf` of the canonical map is the structure
morphism of the stage base change to `Spf R`.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.homOfTriangle`: a scheme morphism commuting with two morphisms
  of the site to a common object is a morphism of the site.
* `AlgebraicGeometry.FormalSpace.stageCompletionRingEquiv`: the ring isomorphism
  `A^∧ ⧸ ker (A^∧ → A ⧸ JA) ≅ Ā_J`.
* `AlgebraicGeometry.FormalSpace.stageCompletionSchemeIso` and
  `AlgebraicGeometry.FormalSpace.stageCompletionSiteIso`: the same identification as an
  isomorphism of schemes and then of objects of the site.
* `AlgebraicGeometry.FormalSpace.stageCompletionModelNatIso` and
  `AlgebraicGeometry.FormalSpace.stageCompletionNatIso`: the isomorphism of diagrams, of objects
  of the site and then of sheaves.

## Main results

* `AlgebraicGeometry.FormalSpace.stageCompletionRingEquiv_comp_quotientMap`: the ring
  isomorphism is one of `R ⧸ J`-algebras.
* `AlgebraicGeometry.FormalSpace.stageCompletionSiteIso_hom_comp`: the identification is one
  over the quotient stage `Spec (R ⧸ J)` of the base.
* `AlgebraicGeometry.FormalSpace.stageCompletionNatIso_hom_app_comp`: the over-the-base clause,
  stated for the morphisms into `Spf R`.

## References

* [Stacks Project, Tag 0AN8](https://stacks.math.columbia.edu/tag/0AN8)
* [Stacks Project, Tag 0AN6](https://stacks.math.columbia.edu/tag/0AN6)
* [Stacks Project, Tag 0ALI](https://stacks.math.columbia.edu/tag/0ALI)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

section SiteHom

variable (𝔅 : BigFppfSite.{u}) (S : Scheme.{u}) (hS : 𝔅.Contains S)

/-- **A scheme morphism between two objects of the big fppf category over `S` which commutes
with morphisms of that category to a common third object is a morphism of that category.** -/
noncomputable def BigFppfOver.homOfTriangle {T W Z : BigFppfOver 𝔅 S hS} (a : T ⟶ Z) (b : W ⟶ Z)
    (θ : (BigFppfOver.toScheme 𝔅 S hS).obj T ⟶ (BigFppfOver.toScheme 𝔅 S hS).obj W)
    (h : θ ≫ (BigFppfOver.toScheme 𝔅 S hS).map b = (BigFppfOver.toScheme 𝔅 S hS).map a) :
    T ⟶ W :=
  BigFppfOver.homOfCompEq 𝔅 S hS θ (by
    have hb : (BigFppfOver.toScheme 𝔅 S hS).map b ≫ 𝔅.inclusion.map Z.hom =
        𝔅.inclusion.map W.hom := by
      rw [show (BigFppfOver.toScheme 𝔅 S hS).map b = 𝔅.inclusion.map b.left from rfl,
        ← Functor.map_comp, Over.w]
    have ha : (BigFppfOver.toScheme 𝔅 S hS).map a ≫ 𝔅.inclusion.map Z.hom =
        𝔅.inclusion.map T.hom := by
      rw [show (BigFppfOver.toScheme 𝔅 S hS).map a = 𝔅.inclusion.map a.left from rfl,
        ← Functor.map_comp, Over.w]
    rw [← hb, ← Category.assoc, h, ha])

/-- The underlying scheme morphism of `AlgebraicGeometry.BigFppfOver.homOfTriangle` is the given
scheme morphism. -/
@[simp]
theorem BigFppfOver.toScheme_map_homOfTriangle {T W Z : BigFppfOver 𝔅 S hS} (a : T ⟶ Z)
    (b : W ⟶ Z) (θ : (BigFppfOver.toScheme 𝔅 S hS).obj T ⟶ (BigFppfOver.toScheme 𝔅 S hS).obj W)
    (h : θ ≫ (BigFppfOver.toScheme 𝔅 S hS).map b = (BigFppfOver.toScheme 𝔅 S hS).map a) :
    (BigFppfOver.toScheme 𝔅 S hS).map (BigFppfOver.homOfTriangle 𝔅 S hS a b θ h) = θ :=
  BigFppfOver.toScheme_map_homOfCompEq 𝔅 S hS θ _

/-- The morphism of the site produced by `AlgebraicGeometry.BigFppfOver.homOfTriangle` commutes
with the two morphisms to the common object. -/
theorem BigFppfOver.homOfTriangle_comp {T W Z : BigFppfOver 𝔅 S hS} (a : T ⟶ Z)
    (b : W ⟶ Z) (θ : (BigFppfOver.toScheme 𝔅 S hS).obj T ⟶ (BigFppfOver.toScheme 𝔅 S hS).obj W)
    (h : θ ≫ (BigFppfOver.toScheme 𝔅 S hS).map b = (BigFppfOver.toScheme 𝔅 S hS).map a) :
    BigFppfOver.homOfTriangle 𝔅 S hS a b θ h ≫ b = a :=
  (BigFppfOver.toScheme 𝔅 S hS).map_injective (by
    rw [Functor.map_comp, BigFppfOver.toScheme_map_homOfTriangle, h])

end SiteHom

/-- **A morphism from a scheme to a spectrum, read through `Scheme.toSpecΓ`.** If the ring map
`k` followed by `b` is the ring map `p` induces on global sections, then the spectrum of `b`
composed with the spectrum of `k` recovers `p`. -/
theorem Scheme.toSpecΓ_comp_Spec_map {X : Scheme.{u}} {T : Type u} [CommRing T]
    (p : X ⟶ Spec (CommRingCat.of T)) {Q : Type u} [CommRing Q] (b : Q →+* Γ(X, ⊤))
    (k : T →+* Q)
    (h : b.comp k = p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom) :
    (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom b)) ≫ Spec.map (CommRingCat.ofHom k) = p := by
  have h' : CommRingCat.ofHom k ≫ CommRingCat.ofHom b =
      (Scheme.ΓSpecIso (CommRingCat.of T)).inv ≫ p.appTop := by
    change CommRingCat.ofHom (b.comp k) = _
    rw [h]
    rfl
  rw [Category.assoc, ← Spec.map_comp, h', Spec.map_comp, ← Category.assoc,
    ← Scheme.toSpecΓ_naturality, ← SpecMap_ΓSpecIso_hom, Category.assoc, ← Spec.map_comp,
    Iso.inv_hom_id, Spec.map_id]
  exact Category.comp_id p

/-- **Naturality of `Scheme.toSpecΓ` against spectra of ring maps.** For `m : X ⟶ Y` and ring maps
`a : P →+* Γ(Y, ⊤)`, `b : Q →+* Γ(X, ⊤)` and `k : P →+* Q` with `m.appTop ∘ a = b ∘ k`, the
morphisms `m ≫ Y.toSpecΓ ≫ Spec a` and `X.toSpecΓ ≫ Spec b ≫ Spec k` to `Spec P` agree. -/
theorem Scheme.toSpecΓ_Spec_map_naturality {X Y : Scheme.{u}} (m : X ⟶ Y)
    {P Q : Type u} [CommRing P] [CommRing Q] (a : P →+* Γ(Y, ⊤)) (b : Q →+* Γ(X, ⊤))
    (k : P →+* Q) (h : m.appTop.hom.comp a = b.comp k) :
    m ≫ Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom a) =
      (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom b)) ≫ Spec.map (CommRingCat.ofHom k) := by
  have h' : CommRingCat.ofHom a ≫ m.appTop =
      CommRingCat.ofHom k ≫ CommRingCat.ofHom b := by
    change CommRingCat.ofHom (m.appTop.hom.comp a) = CommRingCat.ofHom (b.comp k)
    rw [h]
  rw [← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc, ← Spec.map_comp, h',
    Spec.map_comp, Category.assoc]

end AlgebraicGeometry

namespace AlgebraicGeometry.FormalSpace

attribute [local instance] sheaf_hasColimits

variable {𝔅 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝔅.Contains S}
  {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R]
  (D : QuotientSystem 𝔅 S hS R)
  {V : FppfSheaf 𝔅 S hS} (v : V ⟶ formalSpectrum D)
  (hY : IsAffineFormalAlgebraicSpace 𝔅 S hS (formalSpectrum D))
  (hV : IsAffineFormalAlgebraicSpace 𝔅 S hS V) (hv : IsRepresentableEtale 𝔅 S hS v)
  (J₀ : TopologicalRing.WeakIdealOfDefinitionIndex R)

/-- **The quotient stage of the completion of the chosen étale lift is the stage model**:
`A^∧ ⧸ ker (A^∧ → A ⧸ JA) ≅ Ā_J`, for a weak ideal of definition `J ⊆ J₀`. The first half is
`AlgebraicGeometry.FormalSpace.quotientKerProjectionRingEquiv`, the second
`AlgebraicGeometry.FormalSpace.stageComparison`. -/
noncomputable def stageCompletionRingEquiv (J : WeakIdealsBelow R J₀) :
    (TopologicalRing.CompletionOver (algebraMap R (stageLiftAlgebra D v hY hV hv J₀)) ⧸
        (kerProjectionIdeal (algebraMap R (stageLiftAlgebra D v hY hV hv J₀))
          (OrderDual.ofDual J.1)).1) ≃+*
      stageBaseChangeRing D v hY hV hv J.1 :=
  (quotientKerProjectionRingEquiv (algebraMap R (stageLiftAlgebra D v hY hV hv J₀))
      (OrderDual.ofDual J.1)).trans
    (stageComparison D v hY hV hv J₀ J).toRingEquiv

/-- `AlgebraicGeometry.FormalSpace.stageCompletionRingEquiv` sends the class of `x` to the image
under `AlgebraicGeometry.FormalSpace.stageComparison` of the projection of `x` to `A ⧸ JA`. -/
theorem stageCompletionRingEquiv_mk (J : WeakIdealsBelow R J₀)
    (x : TopologicalRing.CompletionOver (algebraMap R (stageLiftAlgebra D v hY hV hv J₀))) :
    stageCompletionRingEquiv D v hY hV hv J₀ J (Ideal.Quotient.mk _ x) =
      stageComparison D v hY hV hv J₀ J
        (TopologicalRing.CompletionOver.projection
          (algebraMap R (stageLiftAlgebra D v hY hV hv J₀)) (OrderDual.ofDual J.1) x) := rfl

/-- **The identifications `A^∧ ⧸ ker (A^∧ → A ⧸ KA) ≅ Ā_K` are compatible with the stage
transitions.** -/
theorem stageCompletionRingEquiv_naturality {J K : WeakIdealsBelow R J₀} (g : J ⟶ K) :
    (stageBaseChangeRingMap D v hY hV hv J₀ g).comp
        (stageCompletionRingEquiv D v hY hV hv J₀ K).toRingHom =
      (stageCompletionRingEquiv D v hY hV hv J₀ J).toRingHom.comp
        (Ideal.Quotient.factor (kerProjectionIdeal_mono
          (algebraMap R (stageLiftAlgebra D v hY hV hv J₀))
          (le_of_weakIdealsBelowHom g))) := by
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun x => ?_)
  change stageBaseChangeRingMap D v hY hV hv J₀ g
      (stageCompletionRingEquiv D v hY hV hv J₀ K (Ideal.Quotient.mk _ x)) =
    stageCompletionRingEquiv D v hY hV hv J₀ J
      (Ideal.Quotient.factor _ (Ideal.Quotient.mk _ x))
  rw [Ideal.Quotient.factor_mk, stageCompletionRingEquiv_mk, stageCompletionRingEquiv_mk]
  refine (RingHom.congr_fun (stageComparison_naturality D v hY hV hv J₀ g)
    (TopologicalRing.CompletionOver.projection _ (OrderDual.ofDual K.1) x)).trans ?_
  exact congrArg (stageComparison D v hY hV hv J₀ J)
    (x.2 (OrderDual.ofDual K.1) (OrderDual.ofDual J.1) (le_of_weakIdealsBelowHom g))

variable (E : QuotientSystem 𝔅 S hS
    (TopologicalRing.CompletionOver (algebraMap R (stageLiftAlgebra D v hY hV hv J₀))))
  (c : ContinuousHom D E)
  (hc : c.toRingHom =
    TopologicalRing.CompletionOver.canonicalMap
      (algebraMap R (stageLiftAlgebra D v hY hV hv J₀)))

/-- **The identification `A^∧ ⧸ ker (A^∧ → A ⧸ JA) ≅ Ā_J` is one of `R ⧸ J`-algebras.**
Composing it with the stage map of the canonical continuous map gives the structure map of the
stage model. -/
theorem stageCompletionRingEquiv_comp_quotientMap (J : WeakIdealsBelow R J₀) :
    (stageCompletionRingEquiv D v hY hV hv J₀ J).toRingHom.comp
        (Ideal.quotientMap
          (kerProjectionIdeal (algebraMap R (stageLiftAlgebra D v hY hV hv J₀))
            (OrderDual.ofDual J.1)).1 c.toRingHom
          (le_comap_kerProjectionIdeal
              (algebraMap R (stageLiftAlgebra D v hY hV hv J₀)) c hc (OrderDual.ofDual J.1))) =
      stageBaseChangeRingHom D v hY hV hv J.1 := by
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun r => ?_)
  change stageCompletionRingEquiv D v hY hV hv J₀ J
      (Ideal.quotientMap _ c.toRingHom _ (Ideal.Quotient.mk _ r)) = _
  rw [Ideal.quotientMap_mk, stageCompletionRingEquiv_mk, hc,
    TopologicalRing.CompletionOver.projection_canonicalMap]
  exact (stageComparison D v hY hV hv J₀ J).commutes
    (Ideal.Quotient.mk (OrderDual.ofDual J.1).1 r)


/-- The quotient stage of the completion attached to a weak ideal of definition `J ⊆ J₀`, as an
object of the big affine fppf category over `S`. -/
noncomputable abbrev completionStage (J : WeakIdealsBelow R J₀) : BigAffineFppf 𝔅 S hS :=
  E.diagram.obj ((kerProjectionDiagram
    (algebraMap R (stageLiftAlgebra D v hY hV hv J₀))).obj J.1)

/-- The stage map of the canonical continuous map, from the quotient stage of the completion at
`J` down to the quotient stage `Spec (R ⧸ J)` of the base. -/
noncomputable abbrev completionStageProj (J : WeakIdealsBelow R J₀) :
    (BigAffineFppf.inclusion 𝔅 S hS).obj (completionStage D v hY hV hv J₀ E J) ⟶
      (BigAffineFppf.inclusion 𝔅 S hS).obj (D.diagram.obj J.1) :=
  (BigAffineFppf.inclusion 𝔅 S hS).map
    (c.stageMap (OrderDual.ofDual J.1)
      (kerProjectionIdeal (algebraMap R (stageLiftAlgebra D v hY hV hv J₀))
        (OrderDual.ofDual J.1))
      (le_comap_kerProjectionIdeal
        (algebraMap R (stageLiftAlgebra D v hY hV hv J₀)) c hc (OrderDual.ofDual J.1)))

/-- **The stage model and the quotient stage of the completion have isomorphic underlying
schemes**: the spectrum of `AlgebraicGeometry.FormalSpace.stageCompletionRingEquiv`, transported
along `Scheme.isoSpec` of the chosen affine model. -/
noncomputable def stageCompletionSchemeIso (J : WeakIdealsBelow R J₀) :
    (BigFppfOver.toScheme 𝔅 S hS).obj (stageBaseChangeModel D v hY hV hv J.1).obj ≅
      (BigFppfOver.toScheme 𝔅 S hS).obj
        ((BigAffineFppf.inclusion 𝔅 S hS).obj (completionStage D v hY hV hv J₀ E J)) :=
  have _ := (stageBaseChangeModel D v hY hV hv J.1).isAffine
  ((BigFppfOver.toScheme 𝔅 S hS).obj
      (stageBaseChangeModel D v hY hV hv J.1).obj).isoSpec.trans
    (Scheme.Spec.mapIso (stageCompletionRingEquiv D v hY hV hv J₀ J).toCommRingCatIso.op)

/-- The forward direction of `AlgebraicGeometry.FormalSpace.stageCompletionSchemeIso` is
`Scheme.toSpecΓ` followed by the spectrum of the ring isomorphism. -/
theorem stageCompletionSchemeIso_hom (J : WeakIdealsBelow R J₀) :
    (stageCompletionSchemeIso D v hY hV hv J₀ E J).hom =
      ((BigFppfOver.toScheme 𝔅 S hS).obj
          (stageBaseChangeModel D v hY hV hv J.1).obj).toSpecΓ ≫
        Spec.map (CommRingCat.ofHom
          (stageCompletionRingEquiv D v hY hV hv J₀ J).toRingHom) := rfl

/-- The stage map of the canonical continuous map, on underlying schemes. -/
theorem toScheme_map_completionStageProj (J : WeakIdealsBelow R J₀) :
    (BigFppfOver.toScheme 𝔅 S hS).map (completionStageProj D v hY hV hv J₀ E c hc J) =
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap
        (kerProjectionIdeal (algebraMap R (stageLiftAlgebra D v hY hV hv J₀))
          (OrderDual.ofDual J.1)).1 c.toRingHom
        (le_comap_kerProjectionIdeal
          (algebraMap R (stageLiftAlgebra D v hY hV hv J₀)) c hc
          (OrderDual.ofDual J.1)))) := rfl

/-- The transition of the quotient stages of the completion, on underlying schemes. -/
theorem toScheme_map_completionStage_map {J K : WeakIdealsBelow R J₀} (g : J ⟶ K) :
    (BigFppfOver.toScheme 𝔅 S hS).map ((BigAffineFppf.inclusion 𝔅 S hS).map
        (E.diagram.map ((kerProjectionDiagram
          (algebraMap R (stageLiftAlgebra D v hY hV hv J₀))).map
            ((weakIdealsBelowInclusion R J₀).map g)))) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
        (kerProjectionIdeal_mono (algebraMap R (stageLiftAlgebra D v hY hV hv J₀))
          (le_of_weakIdealsBelowHom g)))) := rfl

/-- **The identification of the stage model with the quotient stage of the completion is one
over the quotient stage `Spec (R ⧸ J)` of the base**, at the level of schemes. -/
theorem stageCompletionSchemeIso_hom_comp (J : WeakIdealsBelow R J₀) :
    (stageCompletionSchemeIso D v hY hV hv J₀ E J).hom ≫
        (BigFppfOver.toScheme 𝔅 S hS).map (completionStageProj D v hY hV hv J₀ E c hc J) =
      (BigFppfOver.toScheme 𝔅 S hS).map (stageBaseChangeModel D v hY hV hv J.1).proj := by
  rw [stageCompletionSchemeIso_hom, toScheme_map_completionStageProj]
  exact Scheme.toSpecΓ_comp_Spec_map _ _ _
    (stageCompletionRingEquiv_comp_quotientMap D v hY hV hv J₀ E c hc J)

/-- **The naturality square of
`AlgebraicGeometry.FormalSpace.stageCompletionSchemeIso`.** -/
theorem stageCompletionSchemeIso_naturality {J K : WeakIdealsBelow R J₀} (g : J ⟶ K) :
    (BigFppfOver.toScheme 𝔅 S hS).map
          ((stageBaseChangeModelDiagram D v hY hV hv).map
            ((weakIdealsBelowInclusion R J₀).map g)) ≫
        (stageCompletionSchemeIso D v hY hV hv J₀ E K).hom =
      (stageCompletionSchemeIso D v hY hV hv J₀ E J).hom ≫
        (BigFppfOver.toScheme 𝔅 S hS).map ((BigAffineFppf.inclusion 𝔅 S hS).map
          (E.diagram.map ((kerProjectionDiagram
            (algebraMap R (stageLiftAlgebra D v hY hV hv J₀))).map
              ((weakIdealsBelowInclusion R J₀).map g)))) := by
  rw [stageCompletionSchemeIso_hom, stageCompletionSchemeIso_hom]
  exact Scheme.toSpecΓ_Spec_map_naturality _ _ _ _
    (stageCompletionRingEquiv_naturality D v hY hV hv J₀ g)

include hc in
/-- **The stage model and the quotient stage of the completion are isomorphic objects of the
site**, with underlying scheme isomorphism
`AlgebraicGeometry.FormalSpace.stageCompletionSchemeIso`. -/
noncomputable def stageCompletionSiteIso (J : WeakIdealsBelow R J₀) :
    (stageBaseChangeModel D v hY hV hv J.1).obj ≅
      (BigAffineFppf.inclusion 𝔅 S hS).obj (completionStage D v hY hV hv J₀ E J) where
  hom := BigFppfOver.homOfTriangle 𝔅 S hS (stageBaseChangeModel D v hY hV hv J.1).proj
    (completionStageProj D v hY hV hv J₀ E c hc J)
    (stageCompletionSchemeIso D v hY hV hv J₀ E J).hom
    (stageCompletionSchemeIso_hom_comp D v hY hV hv J₀ E c hc J)
  inv := BigFppfOver.homOfTriangle 𝔅 S hS
    (completionStageProj D v hY hV hv J₀ E c hc J)
    (stageBaseChangeModel D v hY hV hv J.1).proj
    (stageCompletionSchemeIso D v hY hV hv J₀ E J).inv
    ((congrArg (fun z => (stageCompletionSchemeIso D v hY hV hv J₀ E J).inv ≫ z)
        (stageCompletionSchemeIso_hom_comp D v hY hV hv J₀ E c hc J)).symm.trans
      (Iso.inv_hom_id_assoc (stageCompletionSchemeIso D v hY hV hv J₀ E J) _))
  hom_inv_id := (BigFppfOver.toScheme 𝔅 S hS).map_injective (by
    rw [Functor.map_comp, BigFppfOver.toScheme_map_homOfTriangle,
      BigFppfOver.toScheme_map_homOfTriangle, Iso.hom_inv_id, CategoryTheory.Functor.map_id])
  inv_hom_id := (BigFppfOver.toScheme 𝔅 S hS).map_injective (by
    rw [Functor.map_comp, BigFppfOver.toScheme_map_homOfTriangle,
      BigFppfOver.toScheme_map_homOfTriangle, Iso.inv_hom_id, CategoryTheory.Functor.map_id])

/-- The underlying scheme morphism of `AlgebraicGeometry.FormalSpace.stageCompletionSiteIso` is
`AlgebraicGeometry.FormalSpace.stageCompletionSchemeIso`. -/
theorem toScheme_map_stageCompletionSiteIso_hom (J : WeakIdealsBelow R J₀) :
    (BigFppfOver.toScheme 𝔅 S hS).map
        (stageCompletionSiteIso D v hY hV hv J₀ E c hc J).hom =
      (stageCompletionSchemeIso D v hY hV hv J₀ E J).hom :=
  BigFppfOver.toScheme_map_homOfTriangle 𝔅 S hS
    (stageBaseChangeModel D v hY hV hv J.1).proj
    (completionStageProj D v hY hV hv J₀ E c hc J)
    (stageCompletionSchemeIso D v hY hV hv J₀ E J).hom
    (stageCompletionSchemeIso_hom_comp D v hY hV hv J₀ E c hc J)

/-- **The identification of the stage model with the quotient stage of the completion is one
over the quotient stage `Spec (R ⧸ J)` of the base.** -/
theorem stageCompletionSiteIso_hom_comp (J : WeakIdealsBelow R J₀) :
    (stageCompletionSiteIso D v hY hV hv J₀ E c hc J).hom ≫
        completionStageProj D v hY hV hv J₀ E c hc J =
      (stageBaseChangeModel D v hY hV hv J.1).proj :=
  BigFppfOver.homOfTriangle_comp 𝔅 S hS
    (stageBaseChangeModel D v hY hV hv J.1).proj
    (completionStageProj D v hY hV hv J₀ E c hc J)
    (stageCompletionSchemeIso D v hY hV hv J₀ E J).hom
    (stageCompletionSchemeIso_hom_comp D v hY hV hv J₀ E c hc J)

/-- **The naturality square of
`AlgebraicGeometry.FormalSpace.stageCompletionSiteIso`.** -/
theorem stageCompletionSiteIso_naturality {J K : WeakIdealsBelow R J₀} (g : J ⟶ K) :
    (stageBaseChangeModelDiagram D v hY hV hv).map ((weakIdealsBelowInclusion R J₀).map g) ≫
        (stageCompletionSiteIso D v hY hV hv J₀ E c hc K).hom =
      (stageCompletionSiteIso D v hY hV hv J₀ E c hc J).hom ≫
        (BigAffineFppf.inclusion 𝔅 S hS).map (E.diagram.map
          ((kerProjectionDiagram (algebraMap R (stageLiftAlgebra D v hY hV hv J₀))).map
            ((weakIdealsBelowInclusion R J₀).map g))) :=
  (BigFppfOver.toScheme 𝔅 S hS).map_injective (by
    refine (CategoryTheory.Functor.map_comp _ _ _).trans
      (Eq.trans ?_ (CategoryTheory.Functor.map_comp _ _ _).symm)
    refine Eq.trans (congrArg (fun z => (BigFppfOver.toScheme 𝔅 S hS).map
        ((stageBaseChangeModelDiagram D v hY hV hv).map
          ((weakIdealsBelowInclusion R J₀).map g)) ≫ z)
      (toScheme_map_stageCompletionSiteIso_hom D v hY hV hv J₀ E c hc K)) ?_
    refine Eq.trans (stageCompletionSchemeIso_naturality D v hY hV hv J₀ E g) ?_
    exact congrArg (fun z => z ≫ (BigFppfOver.toScheme 𝔅 S hS).map
        ((BigAffineFppf.inclusion 𝔅 S hS).map (E.diagram.map
          ((kerProjectionDiagram (algebraMap R (stageLiftAlgebra D v hY hV hv J₀))).map
            ((weakIdealsBelowInclusion R J₀).map g)))))
      (toScheme_map_stageCompletionSiteIso_hom D v hY hV hv J₀ E c hc J).symm)

include hc in
/-- **The chosen affine models of the stage base changes below `J₀` are naturally the quotient
stages of the completion of the chosen étale lift**, as a diagram of objects of the site. -/
noncomputable def stageCompletionModelNatIso :
    weakIdealsBelowInclusion R J₀ ⋙ stageBaseChangeModelDiagram D v hY hV hv ≅
      weakIdealsBelowInclusion R J₀ ⋙
        (kerProjectionDiagram (algebraMap R (stageLiftAlgebra D v hY hV hv J₀)) ⋙
          E.diagram ⋙ BigAffineFppf.inclusion 𝔅 S hS) :=
  NatIso.ofComponents (fun J => stageCompletionSiteIso D v hY hV hv J₀ E c hc J)
    (fun g => stageCompletionSiteIso_naturality D v hY hV hv J₀ E c hc g)

/-- The naturality square of
`AlgebraicGeometry.FormalSpace.stageCompletionSiteIso`, read on the represented sheaves and
transported along `AlgebraicGeometry.FormalSpace.isoStageBaseChange`. -/
theorem stageCompletionSheafIso_naturality {J K : WeakIdealsBelow R J₀} (g : J ⟶ K) :
    (stageBaseChangeDiagram D v).map ((weakIdealsBelowInclusion R J₀).map g) ≫
        ((isoStageBaseChange D v hY hV hv K.1).inv ≫
          (Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).map
            (stageCompletionSiteIso D v hY hV hv J₀ E c hc K).hom) =
      ((isoStageBaseChange D v hY hV hv J.1).inv ≫
          (Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).map
            (stageCompletionSiteIso D v hY hV hv J₀ E c hc J).hom) ≫
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).map
          ((BigAffineFppf.inclusion 𝔅 S hS).map (E.diagram.map
            ((kerProjectionDiagram (algebraMap R (stageLiftAlgebra D v hY hV hv J₀))).map
              ((weakIdealsBelowInclusion R J₀).map g)))) := by
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (Iso.inv_hom_id_assoc (isoStageBaseChange D v hY hV hv J.1) _).symm ?_
  refine Eq.trans (congrArg (fun z => (isoStageBaseChange D v hY hV hv J.1).inv ≫ z)
    (Category.assoc _ _ _).symm) ?_
  refine Eq.trans (congrArg (fun z => (isoStageBaseChange D v hY hV hv J.1).inv ≫
      (z ≫ (Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).map
        (stageCompletionSiteIso D v hY hV hv J₀ E c hc K).hom))
    (map_stageBaseChangeModelDiagram_map D v hY hV hv
      ((weakIdealsBelowInclusion R J₀).map g)).symm) ?_
  refine Eq.trans (congrArg (fun z => (isoStageBaseChange D v hY hV hv J.1).inv ≫ z)
    (CategoryTheory.Functor.map_comp _ _ _).symm) ?_
  refine Eq.trans (congrArg (fun z => (isoStageBaseChange D v hY hV hv J.1).inv ≫
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).map z)
    (stageCompletionSiteIso_naturality D v hY hV hv J₀ E c hc g)) ?_
  refine Eq.trans (congrArg (fun z => (isoStageBaseChange D v hY hV hv J.1).inv ≫ z)
    (CategoryTheory.Functor.map_comp _ _ _)) ?_
  exact (Category.assoc _ _ _).symm

include hc in
/-- **The base changes of `V` to the quotient stages below `J₀` are naturally the quotient
stages of the completion of the chosen étale lift.** -/
noncomputable def stageCompletionNatIso :
    weakIdealsBelowInclusion R J₀ ⋙ stageBaseChangeDiagram D v ≅
      weakIdealsBelowInclusion R J₀ ⋙
        (kerProjectionDiagram (algebraMap R (stageLiftAlgebra D v hY hV hv J₀)) ⋙
          formalSpectrumDiagram E) :=
  NatIso.ofComponents
    (fun J => (isoStageBaseChange D v hY hV hv J.1).symm.trans
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).mapIso
        (stageCompletionSiteIso D v hY hV hv J₀ E c hc J)))
    (fun g => stageCompletionSheafIso_naturality D v hY hV hv J₀ E c hc g)

/-- The component of `AlgebraicGeometry.FormalSpace.stageCompletionNatIso` at `J` is the inverse
of `AlgebraicGeometry.FormalSpace.isoStageBaseChange` followed by the sheafified Yoneda image of
`AlgebraicGeometry.FormalSpace.stageCompletionSiteIso`. -/
theorem stageCompletionNatIso_hom_app (J : WeakIdealsBelow R J₀) :
    (stageCompletionNatIso D v hY hV hv J₀ E c hc).hom.app J =
      (isoStageBaseChange D v hY hV hv J.1).inv ≫
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).map
          (stageCompletionSiteIso D v hY hV hv J₀ E c hc J).hom := rfl

/-- **The stagewise identification is over `Spf R`.** The composite of a stage of
`AlgebraicGeometry.FormalSpace.stageCompletionNatIso` with the inclusion of that quotient stage
of `A^∧` into `Spf A^∧` and with `Spf` of the canonical map is the structure morphism of the
stage base change to `Spf R`. -/
theorem stageCompletionNatIso_hom_app_comp (hR : TopologicalRing.IsWeaklyAdmissible R)
    (J : WeakIdealsBelow R J₀) :
    (stageCompletionNatIso D v hY hV hv J₀ E c hc).hom.app J ≫
          formalSpectrumInclusion E
            ((kerProjectionDiagram
              (algebraMap R (stageLiftAlgebra D v hY hV hv J₀))).obj J.1) ≫
        formalSpectrumMap hR c =
      pullback.fst (formalSpectrumInclusion D J.1) v ≫ formalSpectrumInclusion D J.1 := by
  have h2 : (Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).map
        (stageCompletionSiteIso D v hY hV hv J₀ E c hc J).hom ≫
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).map
        (completionStageProj D v hY hV hv J₀ E c hc J) =
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).map
        (stageBaseChangeModel D v hY hV hv J.1).proj := by
    rw [← Functor.map_comp, stageCompletionSiteIso_hom_comp]
  have h3 : (isoStageBaseChange D v hY hV hv J.1).inv ≫
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).map
        (stageBaseChangeModel D v hY hV hv J.1).proj =
      pullback.fst (formalSpectrumInclusion D J.1) v :=
    (congrArg (fun z => (isoStageBaseChange D v hY hV hv J.1).inv ≫ z)
        (isoStageBaseChange_hom_fst D v hY hV hv J.1)).symm.trans
      (Iso.inv_hom_id_assoc (isoStageBaseChange D v hY hV hv J.1)
        (pullback.fst (formalSpectrumInclusion D J.1) v))
  have h1 : (stageCompletionNatIso D v hY hV hv J₀ E c hc).hom.app J ≫
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).map
        (completionStageProj D v hY hV hv J₀ E c hc J) =
      pullback.fst (formalSpectrumInclusion D J.1) v :=
    (congrArg (fun z => z ≫ (Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).map
          (completionStageProj D v hY hV hv J₀ E c hc J))
        (stageCompletionNatIso_hom_app D v hY hV hv J₀ E c hc J)).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun z => (isoStageBaseChange D v hY hV hv J.1).inv ≫ z) h2).trans h3))
  exact (congrArg (fun z => (stageCompletionNatIso D v hY hV hv J₀ E c hc).hom.app J ≫ z)
      (formalSpectrumMap_spec hR c (OrderDual.ofDual J.1)
        (kerProjectionIdeal (algebraMap R (stageLiftAlgebra D v hY hV hv J₀))
          (OrderDual.ofDual J.1))
        (le_comap_kerProjectionIdeal
          (algebraMap R (stageLiftAlgebra D v hY hV hv J₀)) c hc
          (OrderDual.ofDual J.1)))).trans
    ((Category.assoc _ _ _).symm.trans
      (congrArg (fun z => z ≫ formalSpectrumInclusion D J.1) h1))

end AlgebraicGeometry.FormalSpace

end
