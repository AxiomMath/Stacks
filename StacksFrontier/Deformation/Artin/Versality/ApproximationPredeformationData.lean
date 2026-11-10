module

public import StacksFrontier.Deformation.Artin.Versality.FormalObjectVersal

/-!
# The levelwise data of a formal object attached to a complete local restriction

This file gives the levelwise data of the versality criterion of [Stacks, Tag 06IU] for the formal
object `ξ` of a complete local object mapping to `x`: a compatible family of arrows from the levels
of `ξ` to the original object `x`, the morphism out of the base of the associated formal object of
the predeformation category, the two compatibilities of that family with the thickenings and with
the closed fibre, and the existence and uniqueness of Artinian points of the complete local base.

These are stated as theorems about explicit terms, with the ambient hypotheses of
[Stacks, Tag 0CXK] read over an arbitrary base ring `Λ` as in
`Deformation.Artin.isVersalAt_iff_isVersal_affineChart`. The arrows are the maps
`Deformation.Artin.approximationLevelToOriginal` out of the levels of `ξ`, and the morphism out of
the base is the chosen presentation `g` of the completed local ring itself.

## Main results

* `Deformation.Artin.approximationRestriction_transition` — the family is compatible with
  the transition maps of the formal object of the predeformation category.
* `Deformation.Artin.approximationRestriction_closedPoint` — it restricts to the map out of
  level `0` on the closed fibre.
* `Deformation.Artin.approximationRestriction_base` — level `n` lies over the `n`-th adic
  thickening of the complete local base cut out by `g`.
* `Deformation.Artin.approximationRestriction_residue` — the map out of level `0` lies over
  the residue point of `g`.
* `Deformation.Artin.approximationPoints` — every Artinian point of `U` compatible with the
  base and with that residue point factors through `g`.
* `Deformation.Artin.approximationPoints_injective` — it factors through `g` in at most one
  way.

## Implementation notes

The identifications that [Stacks, Tag 0CXK] carries as a conjunction `hη` of four equalities
hold by `rfl` here: the base of `ξ.predeformationFormalObject` *is*
`ξ.completeLocalBase`, and the underlying object of level `n` *is* `ξ.level n`. The transports
are therefore kept only where a lemma of `FormalObjectVersal` is stated with them, and
discharged on the spot by `CategoryTheory.eqToHom_comp_heq`: the source and target of each
such transport being definitionally equal, the heterogeneous equation it provides is a genuine
one.

## References

* [Stacks Project, Tag 0CXK](https://stacks.math.columbia.edu/tag/0CXK)
* [Stacks Project, Tag 06IU](https://stacks.math.columbia.edu/tag/06IU)
* [Stacks Project, Tag 07YM](https://stacks.math.columbia.edu/tag/07YM)
* [Stacks Project, Tag 07X6](https://stacks.math.columbia.edu/tag/07X6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace Deformation.Artin

universe u v w

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor
attribute [local implicit_reducible] Deformation.Artin.baseOver
attribute [local implicit_reducible] Deformation.Artin.truncationOver

attribute [local instance] Deformation.Artin.versal_predeformationCategory_category

section ApproximationPackage

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {F : Type v} [Category.{w} F]
  (p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (U : Over S) (x : F) (hx : (p ⋙ Over.post B.inclusion).obj x = U)
  (u₀ : U.left) [IsLocallyNoetherian U.left]
  (xR : Deformation.Artin.CompleteLocalObjects B S hS p)
  (ξ : Deformation.Artin.FormalObject B S hS p)
  (hξ : ξ = (Deformation.Artin.approximationFunctor B S hS p hp).obj xR)
  (e : AlgebraicGeometry.Scheme.completedLocalRing U.left u₀ ≃+* ξ.base.R)
  (g : Spec (.of ξ.base.R) ⟶ U.left)
  (hg : g = Spec.map (CommRingCat.ofHom e.toRingHom) ≫
    Spec.map (CommRingCat.ofHom
      (algebraMap (U.left.presheaf.stalk u₀)
        (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀))) ≫
    U.left.fromSpecStalk u₀)
  (hbase : ξ.base.toS = g ≫ U.hom)
  (r : xR.obj.1 ⟶ x)
  (hrbase : HEq
    ((eqToHom (Deformation.Artin.chosenBase_eq B S hS p xR.obj).symm ≫
      p.map r).left.hom ≫ eqToHom (congrArg Over.left hx)) g)
  (Λ : Type u) [CommRing Λ] [Algebra Λ ξ.base.R]
  (iΛ : Spec (.of Λ) ⟶ S) [Mono iΛ]
  (hΛ : Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base.R)) ≫ iΛ = ξ.base.toS)

/-- The predeformation category of the closed fibre of `ξ`, over the base ring `Λ`. This is
the category the formal object `Deformation.Artin.FormalObject.predeformationFormalObject`
lives in. -/
public abbrev approximationPredeformationCategory :
    Deformation.Artin.PredeformationConstruction iΛ (p ⋙ Over.post B.inclusion)
      (ξ.level 0) (ξ.basePoint Λ iΛ hΛ) :=
  Deformation.Artin.predeformationCategory iΛ (p ⋙ Over.post B.inclusion) (ξ.level 0)
    (ξ.basePoint Λ iΛ hΛ)

/-- The morphism out of the base of the formal object of the predeformation category: the
chosen presentation `g` of the completed local ring, whose source is already the spectrum of
that base. -/
public abbrev approximationBaseMap :
    Spec (CommRingCat.of (ξ.predeformationFormalObject Λ iΛ hΛ).base) ⟶ U.left := g

include hp xR hξ r in
/-- The arrow from level `n` of the formal object of the predeformation category to the
original object `x`: the map out of level `n` of `ξ` supplied by the approximation functor
of [Stacks, Tag 07X6]. -/
public abbrev approximationRestriction (n : ℕ) :
    (Deformation.Artin.deformationForget
        (approximationPredeformationCategory B S hS p ξ Λ iΛ hΛ)).obj
      (.op ((ξ.predeformationFormalObject Λ iΛ hΛ).level n)) ⟶ x :=
  Deformation.Artin.approximationLevelToOriginal B S hS p hp xR ξ hξ r n

omit [Mono iΛ] in
/-- **The family of arrows is compatible with the transitions.** -/
public theorem approximationRestriction_transition (n : ℕ) :
    (Deformation.Artin.deformationForget
          (approximationPredeformationCategory B S hS p ξ Λ iΛ hΛ)).map
        ((ξ.predeformationFormalObject Λ iΛ hΛ).transition n).op ≫
      approximationRestriction B S hS p hp x xR ξ hξ r Λ iΛ hΛ (n + 1) =
    approximationRestriction B S hS p hp x xR ξ hξ r Λ iΛ hΛ n :=
  Deformation.Artin.approximationLevelToOriginal_transition B S hS p hp xR ξ hξ r n

omit [Mono iΛ] in
/-- **The family of arrows restricts to the map out of level `0` on the closed fibre.** -/
public theorem approximationRestriction_closedPoint (n : ℕ) :
    ((approximationPredeformationCategory B S hS p ξ Λ iΛ hΛ).objects
          ((ξ.predeformationFormalObject Λ iΛ hΛ).level n)).arrow ≫
        approximationRestriction B S hS p hp x xR ξ hξ r Λ iΛ hΛ n =
      Deformation.Artin.approximationLevelToOriginal B S hS p hp xR ξ hξ r 0 :=
  Deformation.Artin.closedPointArrow_restriction ξ
    (Deformation.Artin.approximationLevelToOriginal B S hS p hp xR ξ hξ r)
    (Deformation.Artin.approximationLevelToOriginal_transition B S hS p hp xR ξ hξ r) n

omit [IsLocallyNoetherian U.left] [Mono iΛ] in
include hrbase in
/-- **Level `n` lies over the `n`-th infinitesimal thickening of the complete local base.**
The underlying morphism of schemes of the arrow out of level `n` is the quotient map onto the
`n`-th adic truncation followed by `g`. -/
public theorem approximationRestriction_base (n : ℕ) :
    schemeMap (p ⋙ Over.post B.inclusion)
        (Deformation.Artin.deformationPointBase
          (approximationPredeformationCategory B S hS p ξ Λ iΛ hΛ)
          ((ξ.predeformationFormalObject Λ iΛ hΛ).level n)
          (Deformation.AdicTruncation.obj (ξ.predeformationFormalObject Λ iΛ hΛ).base n)
          ((ξ.predeformationFormalObject Λ iΛ hΛ).level_eq n)) hx
        (approximationRestriction B S hS p hp x xR ξ hξ r Λ iΛ hΛ n) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (Deformation.AdicTruncation.ideal (ξ.predeformationFormalObject Λ iΛ hΛ).base n))) ≫
        approximationBaseMap B S hS p U ξ g Λ iΛ hΛ := by
  have hη1 : (ξ.predeformationFormalObject Λ iΛ hΛ).base = ξ.completeLocalBase Λ := rfl
  have hη21 : ∀ m, ((approximationPredeformationCategory B S hS p ξ Λ iΛ hΛ).objects
      ((ξ.predeformationFormalObject Λ iΛ hΛ).level m)).point = ξ.level m := fun _ => rfl
  have ht : Spec (CommRingCat.of
        (Deformation.AdicTruncation.obj (ξ.predeformationFormalObject Λ iΛ hΛ).base n)) =
      ξ.base.truncation n :=
    congrArg (fun R : Deformation.CompleteLocalAlgCat.{u, u, u} Λ (ResidueField ξ.base.R) =>
      Spec (CommRingCat.of (Deformation.AdicTruncation.obj R n))) hη1
  have hrn : schemeMap (p ⋙ Over.post B.inclusion)
        (congrArg (Over.post B.inclusion).obj (ξ.level_eq n)) hx
        (Deformation.Artin.approximationLevelToOriginal B S hS p hp xR ξ hξ r n) =
      AlgebraicGeometry.adicThickeningι ξ.base.R (maximalIdeal ξ.base.R) n ≫ g := by
    simpa [schemeMap, AlgebraicGeometry.BigFppfOver.toScheme,
      AlgebraicGeometry.BigFppfOver.forget, Over.post, Category.assoc] using
      Deformation.Artin.approximationLevelToOriginal_schemeMap B S hS p hp xR ξ hξ r U hx g
        hrbase n
  have hs := Deformation.Artin.schemeMap_eqToHom_comp (p ⋙ Over.post B.inclusion)
    (Deformation.Artin.deformationPointBase
      (approximationPredeformationCategory B S hS p ξ Λ iΛ hΛ)
      ((ξ.predeformationFormalObject Λ iΛ hΛ).level n)
      (Deformation.AdicTruncation.obj (ξ.predeformationFormalObject Λ iΛ hΛ).base n)
      ((ξ.predeformationFormalObject Λ iΛ hΛ).level_eq n))
    (congrArg (Over.post B.inclusion).obj (ξ.level_eq n)) hx (hη21 n) ht
    (Deformation.Artin.approximationLevelToOriginal B S hS p hp xR ξ hξ r n)
  have htr := congrArg (fun a => a ≫ g) (Deformation.Artin.truncationι_eqToHom hη1 n)
  have key := hs.trans ((congrArg (fun a => eqToHom ht ≫ a) hrn).trans
    ((Category.assoc _ _ _).symm.trans (htr.symm.trans (Category.assoc _ _ _))))
  have hid : eqToHom (hη21 n) ≫
        Deformation.Artin.approximationLevelToOriginal B S hS p hp xR ξ hξ r n =
      Deformation.Artin.approximationLevelToOriginal B S hS p hp xR ξ hξ r n :=
    eq_of_heq (eqToHom_comp_heq _ _)
  have hgid : eqToHom (congrArg
        (fun R : Deformation.CompleteLocalAlgCat.{u, u, u} Λ (ResidueField ξ.base.R) =>
          Spec (CommRingCat.of R)) hη1) ≫ g = g :=
    eq_of_heq (eqToHom_comp_heq _ _)
  rw [hid] at key
  exact key.trans (congrArg (fun t => Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
    (Deformation.AdicTruncation.ideal (ξ.predeformationFormalObject Λ iΛ hΛ).base n))) ≫ t) hgid)

omit [IsLocallyNoetherian U.left] [Mono iΛ] in
include hrbase in
/-- **The map out of level `0` lies over the residue point of `g`.** -/
public theorem approximationRestriction_residue :
    schemeMap (p ⋙ Over.post B.inclusion) (ξ.basePoint Λ iΛ hΛ) hx
        (Deformation.Artin.approximationLevelToOriginal B S hS p hp xR ξ hξ r 0) =
      Spec.map (CommRingCat.ofHom (residue ξ.base.R)) ≫ g := by
  have hrn : schemeMap (p ⋙ Over.post B.inclusion)
        (congrArg (Over.post B.inclusion).obj (ξ.level_eq 0)) hx
        (Deformation.Artin.approximationLevelToOriginal B S hS p hp xR ξ hξ r 0) =
      AlgebraicGeometry.adicThickeningι ξ.base.R (maximalIdeal ξ.base.R) 0 ≫ g := by
    simpa [schemeMap, AlgebraicGeometry.BigFppfOver.toScheme,
      AlgebraicGeometry.BigFppfOver.forget, Over.post, Category.assoc] using
      Deformation.Artin.approximationLevelToOriginal_schemeMap B S hS p hp xR ξ hξ r U hx g
        hrbase 0
  have ht : Spec (CommRingCat.of (ResidueField ξ.base.R)) = ξ.base.truncation 0 :=
    (congrArg Over.left (ξ.basePoint Λ iΛ hΛ)).symm.trans
      (congrArg Over.left (congrArg (Over.post B.inclusion).obj (ξ.level_eq 0)))
  have he := Deformation.Artin.schemeMap_eqToHom_comp (p ⋙ Over.post B.inclusion)
    (ξ.basePoint Λ iΛ hΛ) (congrArg (Over.post B.inclusion).obj (ξ.level_eq 0)) hx rfl ht
    (Deformation.Artin.approximationLevelToOriginal B S hS p hp xR ξ hξ r 0)
  have hι := Deformation.Artin.quotientSpecMap_eqToHom ξ.base.R
    (pow_one (maximalIdeal ξ.base.R)) ht
  have hchain := he.trans ((congrArg (fun a => eqToHom ht ≫ a) hrn).trans
    ((Category.assoc _ _ _).symm.trans (congrArg (fun a => a ≫ g) hι)))
  simp only [eqToHom_refl, Category.id_comp] at hchain
  exact hchain

include e hg hbase hrbase in
/-- **Artinian points of `U` compatible with the residue point factor through `g`.** This is
the existence half of the universal property of the complete local presentation, read for the
base of the formal object of the predeformation category. -/
public theorem approximationPoints
    (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ (ResidueField ξ.base.R))
    (f : Spec (CommRingCat.of A) ⟶ U.left)
    (hfbase : f ≫ U.hom = Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ)
    (hfres : Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap A)) ≫ f =
      schemeMap (p ⋙ Over.post B.inclusion) (ξ.basePoint Λ iΛ hΛ) hx
        (Deformation.Artin.approximationLevelToOriginal B S hS p hp xR ξ hξ r 0)) :
    ∃ α : (ξ.predeformationFormalObject Λ iΛ hΛ).base ⟶
        Deformation.artinianToComplete.obj A,
      Spec.map (CommRingCat.ofHom α.hom.toRingHom) ≫
        approximationBaseMap B S hS p U ξ g Λ iΛ hΛ = f := by
  have hη1 : (ξ.predeformationFormalObject Λ iΛ hΛ).base = ξ.completeLocalBase Λ := rfl
  have g_closedPoint : g (closedPoint ξ.base.R) = u₀ := by
    rw [hg]
    exact Deformation.Artin.completionPresentation_closedPoint U.left u₀ e
  have hres : Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap A)) ≫ f =
      Spec.map (CommRingCat.ofHom (residue ξ.base.R)) ≫ g :=
    hfres.trans (approximationRestriction_residue B S hS p hp U x hx xR ξ hξ g r hrbase Λ iΛ hΛ)
  have : IsLocalHom (Deformation.Artin.residueMap A) := IsLocalHom.of_surjective _
    (A.residueEquiv.surjective.comp (residue_surjective (R := A)))
  have : IsLocalHom (CommRingCat.ofHom (residue ξ.base.R)).hom :=
    IsLocalHom.of_surjective _ (residue_surjective (R := ξ.base.R))
  have hf : f (closedPoint A) = u₀ := by
    have hev := congrArg
      (fun t : Spec (CommRingCat.of (ResidueField ξ.base.R)) ⟶ U.left =>
        t (closedPoint (ResidueField ξ.base.R))) hres
    exact (Deformation.Artin.closedPoint_comp_eq
      (CommRingCat.ofHom (Deformation.Artin.residueMap A)) f).symm.trans
        (hev.trans ((Deformation.Artin.closedPoint_comp_eq
          (CommRingCat.ofHom (residue ξ.base.R)) g).trans g_closedPoint))
  have hex := Deformation.Artin.exists_completeLocalAlgHom_of_completionPresentation iΛ U u₀
    (ξ.completeLocalBase Λ) e g hg (hΛ.trans hbase) A f hf hfbase hres
  obtain ⟨α, hα⟩ :=
    Deformation.Artin.completeLocalAlg_points_of_eq hη1 g A f hex.exists
  refine ⟨α, ?_⟩
  have hgid : eqToHom (congrArg
        (fun R : Deformation.CompleteLocalAlgCat.{u, u, u} Λ (ResidueField ξ.base.R) =>
          Spec (CommRingCat.of R)) hη1) ≫ g = g :=
    eq_of_heq (eqToHom_comp_heq _ _)
  rwa [hgid] at hα

omit [Mono iΛ] in
include e hg in
/-- **An Artinian point factors through `g` in at most one way.** This is the uniqueness half
of the universal property of the complete local presentation, read for the base of the formal
object of the predeformation category. -/
public theorem approximationPoints_injective
    (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ (ResidueField ξ.base.R))
    (α β : (ξ.predeformationFormalObject Λ iΛ hΛ).base ⟶
      Deformation.artinianToComplete.obj A)
    (he : Spec.map (CommRingCat.ofHom α.hom.toRingHom) ≫
        approximationBaseMap B S hS p U ξ g Λ iΛ hΛ =
      Spec.map (CommRingCat.ofHom β.hom.toRingHom) ≫
        approximationBaseMap B S hS p U ξ g Λ iΛ hΛ) : α = β := by
  have hη1 : (ξ.predeformationFormalObject Λ iΛ hΛ).base = ξ.completeLocalBase Λ := rfl
  have hgid : eqToHom (congrArg
        (fun R : Deformation.CompleteLocalAlgCat.{u, u, u} Λ (ResidueField ξ.base.R) =>
          Spec (CommRingCat.of R)) hη1) ≫ g = g :=
    eq_of_heq (eqToHom_comp_heq _ _)
  have pointMaps_injective (A' : Type u) [CommRing A'] [IsArtinianRing A'] [IsLocalRing A']
      (φ ψ : ξ.base.R →+* A') [IsLocalHom φ] [IsLocalHom ψ]
      (h : Spec.map (CommRingCat.ofHom φ) ≫ g = Spec.map (CommRingCat.ofHom ψ) ≫ g) :
      φ = ψ := by
    apply Deformation.Artin.completionPresentation_map_injective U.left u₀ e
    simpa only [← hg] using h
  have he' : Spec.map (CommRingCat.ofHom α.hom.toRingHom) ≫
        eqToHom (congrArg
          (fun R : Deformation.CompleteLocalAlgCat.{u, u, u} Λ (ResidueField ξ.base.R) =>
            Spec (CommRingCat.of R)) hη1) ≫ g =
      Spec.map (CommRingCat.ofHom β.hom.toRingHom) ≫
        eqToHom (congrArg
          (fun R : Deformation.CompleteLocalAlgCat.{u, u, u} Λ (ResidueField ξ.base.R) =>
            Spec (CommRingCat.of R)) hη1) ≫ g := by
    rwa [hgid]
  refine Deformation.Artin.completeLocalAlg_points_injective_of_eq hη1 g
    (fun A' a b hab => ?_) A α β he'
  exact Deformation.CompleteLocalAlgCat.Hom.ext (AlgHom.toRingHom_injective
    (@pointMaps_injective A' _ _ _ a.hom.toRingHom b.hom.toRingHom a.isLocal b.isLocal hab))

end ApproximationPackage

end Deformation.Artin

end
