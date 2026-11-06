module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteTypePoint
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.AlgebraicGeometry.Variety.CompleteLocal.Stalk
public import StacksFrontier.Deformation.Artin.FormalObject
public import StacksFrontier.Deformation.Artin.FormalObject.Predeformation
public import StacksFrontier.Deformation.Artin.FormalObject.Versal
public import StacksFrontier.Deformation.Artin.Predeformation
public import StacksFrontier.Deformation.Artin.Versality
public import StacksFrontier.Deformation.Artin.Versality.FormalObjectVersal.ApproximationLevels
public import StacksFrontier.Deformation.Artin.Versality.FormalObjectVersal.CompletionLifts
public import StacksFrontier.Deformation.Artin.Versality.FormalObjectVersal.ResiduePointLifting
public import StacksFrontier.Deformation.ArtinCriteria.Predeformation
public import StacksFrontier.Deformation.Basic
public import StacksFrontier.Deformation.Cofibered
public import StacksFrontier.Deformation.Completed.Basic
public import StacksFrontier.Deformation.FormalObject.Associated
public import StacksFrontier.Deformation.FormalObject.Basic
public import StacksFrontier.Deformation.Groupoid.BaseCategory
public import StacksFrontier.Deformation.Predeformation.Basic
public import StacksFrontier.Deformation.Smooth.Basic
public import StacksFrontier.Deformation.Smooth.Pushforward
public import StacksFrontier.Deformation.Smooth.Versal
public import StacksFrontier.RingTheory.Ideal.RadicalMaximalQuotient

/-!
# Versality at a point and versality of the associated formal object

The comparison of the lifting property at the residue point with versality of the formal
object attached by the approximation functor, over an arbitrary base ring
(`Deformation.Artin.liftsAtResiduePoint_iff_isVersal`), the resulting **Stacks 0CXK**
(`Deformation.Artin.isVersalAt_iff_isVersal`), and its variant for a formal object of a
predeformation category realized by compatible restrictions
(`Deformation.Artin.liftsAtResiduePoint_iff_isVersal_of_restrictions`).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace Deformation.Artin

universe u v w

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor
attribute [local implicit_reducible] Deformation.Artin.baseOver
attribute [local implicit_reducible] Deformation.Artin.truncationOver

/-- **The core of Stacks 0CXK, over an arbitrary base ring.** With the notation of
**Stacks 07XF**, let `R` be the completed local ring of `U` at `u₀`, presented by a ring
equivalence `e`, and let `ξ` be the formal object attached by the approximation functor of
**Stacks 07X6** to a Cartesian restriction `x_R` of `x` over `Spec R`. For *any* ring `Λ`
carrying a monomorphism `Spec Λ ⟶ S` through which the structure morphism of `ξ.base`
factors, the lifting property of **Stacks 07XF** at the residue field of `R` holds exactly
when `ξ` is versal relative to `Λ` in the sense of **Stacks 0CXJ**.

`Deformation.Artin.isVersalAt_iff_isVersal` is this statement at the one base ring the
left-hand side is *literally* the lifting property over, the local ring `𝒪_{S,s}`. Nothing
else about `Λ` was ever used: in the proof of that comparison the identifications
`CommRingCat.of Λ = 𝒪_{S,s}` and `HEq iΛ (S.fromSpecStalk s)` entered only in rewriting
`Deformation.Artin.IsVersalAt` as the lifting property, and `Mono iΛ` — which they supply —
only in `Deformation.Artin.exists_completeLocalAlgHom_of_completionPresentation`. Separating
the two is what lets the criterion of **Stacks 06IU** be applied over the ring of an affine
open of `S`, which is where conditions (i) and (ii) of **Stacks 07YM** are stated; the
passage from the lifting property there back to versality at the point is
`Deformation.Artin.isVersalAt_iff_liftsAtResiduePoint_affineOpen`. -/
public theorem liftsAtResiduePoint_iff_isVersal
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : Type v} [Category.{w} F]
    (p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids)
    (U : Over S) (x : F)
    (hx : (p ⋙ Over.post B.inclusion).obj x = U)
    (u₀ : U.left)
    [IsLocallyNoetherian U.left]
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
    (_hr : p.IsCartesian (p.map r) r)
    (hrbase : HEq
      ((eqToHom (Deformation.Artin.chosenBase_eq B S hS p xR.obj).symm ≫
        p.map r).left.hom ≫ eqToHom (congrArg Over.left hx)) g)
    (Λ : Type u) [CommRing Λ] [Algebra Λ ξ.base.R]
    (iΛ : Spec (.of Λ) ⟶ S) [Mono iΛ]
    (hΛ : Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base.R)) ≫ iΛ =
      ξ.base.toS) :
    LiftsAtResiduePoint (Λ := Λ) (k := ResidueField ξ.base.R)
        (alg := ResidueField.algebra ξ.base.R) iΛ (p ⋙ Over.post B.inclusion) U x hx
        (Spec.map (CommRingCat.ofHom (residue ξ.base.R)) ≫ g) ↔
      Deformation.Artin.FormalObject.IsVersal B S hS p hp ξ Λ iΛ hΛ := by
  let : CommRing ξ.base.R := ξ.base.commRing
  have : IsLocalRing ξ.base.R := ξ.base.localRing
  let k := ResidueField ξ.base.R
  let : Field k := ResidueField.field ξ.base.R
  let : Algebra Λ k := ResidueField.algebra ξ.base.R
  let q : F ⥤ Over S := p ⋙ Over.post B.inclusion
  let hx₀ := Deformation.Artin.FormalObject.basePoint ξ Λ iΛ hΛ
  let C := Deformation.Artin.predeformationCategory iΛ q (ξ.level 0) hx₀
  let : Category C.carrier := C.category
  let η : Deformation.FormalObject C.projection :=
    Deformation.Artin.FormalObject.predeformationFormalObject ξ Λ iΛ hΛ
  let hpC :=
    (Deformation.Artin.predeformationCategory_isPredeformationCategory
      B hS iΛ p (ξ.level 0) hx₀ hp).cofibered
  show LiftsAtResiduePoint iΛ q U x hx
      (Spec.map (CommRingCat.ofHom (residue ξ.base.R)) ≫ g) ↔ Deformation.IsVersal hpC η
  have g_closedPoint : g (closedPoint ξ.base.R) = u₀ := by
    rw [hg]
    exact completionPresentation_closedPoint U.left u₀ e
  have complete_points (A : Type u) [CommRing A] [IsArtinianRing A] [IsLocalRing A]
      (f : Spec (.of A) ⟶ U.left) (hf : f (closedPoint A) = u₀) :
      ∃! φ : { φ : ξ.base.R →+* A // IsLocalHom φ },
        Spec.map (CommRingCat.ofHom φ.1) ≫ g = f := by
    simpa only [hg] using exists_unique_completionPresentation_lift U.left u₀ e f hf
  have pointMaps_injective (A : Type u) [CommRing A] [IsArtinianRing A] [IsLocalRing A]
      (φ ψ : ξ.base.R →+* A) [IsLocalHom φ] [IsLocalHom ψ]
      (h : Spec.map (CommRingCat.ofHom φ) ≫ g = Spec.map (CommRingCat.ofHom ψ) ≫ g) :
      φ = ψ := by
    apply completionPresentation_map_injective U.left u₀ e
    simpa only [← hg] using h
  have restriction_base (n : ℕ) :=
    approximationLevelToOriginal_schemeMap B S hS p hp xR ξ hξ r U hx g hrbase n
  have hη : η.base = Deformation.Artin.FormalObject.completeLocalBase ξ Λ ∧
      (∀ n, (C.objects (η.level n)).point = ξ.level n) ∧
      (∀ n, HEq (C.objects (η.level n)).arrow
        (Deformation.Artin.FormalObject.closedPointArrow ξ n)) ∧
      (∀ n, HEq (C.morphisms (η.level (n + 1)) (η.level n) (η.transition n)).arrow
        (ξ.transition n)) :=
    ⟨rfl, fun _ => rfl, fun _ => HEq.rfl, fun _ => HEq.rfl⟩
  let G := deformationForget C
  have : G.Faithful := deformationForget_faithful C
  let restriction (n : ℕ) : G.obj (.op (η.level n)) ⟶ x :=
    eqToHom (hη.2.1 n) ≫ approximationLevelToOriginal B S hS p hp xR ξ hξ r n
  have restriction_transition (n : ℕ) :
      G.map (η.transition n).op ≫ restriction (n + 1) = restriction n :=
    restriction_compatible_of_heq G η.level ξ.level η.transition ξ.transition
      hη.2.1 hη.2.2.2
      (approximationLevelToOriginal B S hS p hp xR ξ hξ r)
      (approximationLevelToOriginal_transition B S hS p hp xR ξ hξ r) n
  let r₀ := approximationLevelToOriginal B S hS p hp xR ξ hξ r 0
  have restriction_closedPoint (n : ℕ) :
      (C.objects (η.level n)).arrow ≫ restriction n = r₀ := by
    show (C.objects (η.level n)).arrow ≫
      (eqToHom (hη.2.1 n) ≫ approximationLevelToOriginal B S hS p hp xR ξ hξ r n) = _
    rw [← Category.assoc]
    have he : (C.objects (η.level n)).arrow ≫ eqToHom (hη.2.1 n) =
        Deformation.Artin.FormalObject.closedPointArrow ξ n :=
      eq_of_heq ((comp_eqToHom_heq _ _).trans (hη.2.2.1 n))
    rw [he]
    exact closedPointArrow_restriction ξ
      (approximationLevelToOriginal B S hS p hp xR ξ hξ r)
      (approximationLevelToOriginal_transition B S hS p hp xR ξ hξ r) n
  have restriction_base_normalized (n : ℕ) :
      schemeMap q (congrArg (Over.post B.inclusion).obj (ξ.level_eq n)) hx
        (approximationLevelToOriginal B S hS p hp xR ξ hξ r n) =
      AlgebraicGeometry.adicThickeningι ξ.base.R (maximalIdeal ξ.base.R) n ≫ g := by
    simpa [schemeMap, q, AlgebraicGeometry.BigFppfOver.toScheme,
      AlgebraicGeometry.BigFppfOver.forget, Over.post, Category.assoc] using restriction_base n
  have r₀_base : schemeMap q hx₀ hx r₀ =
      Spec.map (CommRingCat.ofHom (residue ξ.base.R)) ≫ g := by
    let hξ₀ := congrArg (Over.post B.inclusion).obj (ξ.level_eq 0)
    have ht : Spec (.of k) = ξ.base.truncation 0 :=
      (congrArg Over.left hx₀).symm.trans (congrArg Over.left hξ₀)
    have he := schemeMap_eqToHom_comp q hx₀ hξ₀ hx rfl ht r₀
    have hι := quotientSpecMap_eqToHom ξ.base.R
      (pow_one (maximalIdeal ξ.base.R)) ht
    have hchain := he.trans
      ((congrArg (fun a => eqToHom ht ≫ a) (restriction_base_normalized 0)).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (fun a => a ≫ g) hι)))
    simp only [eqToHom_refl, Category.id_comp] at hchain
    exact hchain
  let gη : Spec (.of η.base) ⟶ U.left :=
    eqToHom (congrArg (fun R : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k =>
      Spec (.of R)) hη.1) ≫ g
  have restriction_level_base (n : ℕ) :
      schemeMap q (deformationPointBase C (η.level n)
        (Deformation.AdicTruncation.obj η.base n) (η.level_eq n)) hx (restriction n) =
      Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (Deformation.AdicTruncation.ideal η.base n))) ≫ gη := by
    let hξn : q.obj (ξ.level n) = Over.mk (ξ.base.truncationToS n) :=
      congrArg (Over.post B.inclusion).obj (ξ.level_eq n)
    have ht : Spec (.of (Deformation.AdicTruncation.obj η.base n)) = ξ.base.truncation n :=
      congrArg (fun R : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k =>
        Spec (.of (Deformation.AdicTruncation.obj R n))) hη.1
    have hs := schemeMap_eqToHom_comp q
      (deformationPointBase C (η.level n) (Deformation.AdicTruncation.obj η.base n)
        (η.level_eq n)) hξn hx (hη.2.1 n) ht
      (approximationLevelToOriginal B S hS p hp xR ξ hξ r n)
    have htr := congrArg (fun a => a ≫ g) (truncationι_eqToHom hη.1 n)
    exact hs.trans ((congrArg (fun a => eqToHom ht ≫ a) (restriction_base_normalized n)).trans
      ((Category.assoc _ _ _).symm.trans
        (htr.symm.trans (Category.assoc _ _ _))))
  let toOriginal (P : Deformation.ChosenPushforwards
      C.projection) :=
    associatedMorphismRestriction η
      (Deformation.associatedMorphism hpC η P)
      G restriction restriction_transition
  have toOriginal_closedPoint
      (P : Deformation.ChosenPushforwards C.projection)
      (α : (Deformation.restrictedCoyoneda η.base).Elements) :
      (C.objects ((Deformation.associatedMorphism
          hpC η P).toBasedFunctor.obj α)).arrow ≫ (toOriginal P).app (.op α) = r₀ :=
    associatedMorphismRestriction_closedPoint C η _ restriction restriction_transition
      r₀ restriction_closedPoint α
  have toOriginal_base
      (P : Deformation.ChosenPushforwards C.projection)
      (α : (Deformation.restrictedCoyoneda η.base).Elements) :
      schemeMap q (deformationPointBase C
        ((Deformation.associatedMorphism
          hpC η P).toBasedFunctor.obj α) α.1
        ((Deformation.associatedMorphism
          hpC η P).toBasedFunctor.w_obj α)) hx ((toOriginal P).app (.op α)) =
        Spec.map (CommRingCat.ofHom α.2.hom.toRingHom) ≫ gη :=
    associatedMorphismRestriction_base C η _ restriction restriction_transition U hx gη
      restriction_level_base α
  have pointMapsη_injective
      (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k)
      (α β : η.base ⟶ Deformation.artinianToComplete.obj A)
      (he : Spec.map (CommRingCat.ofHom α.hom.toRingHom) ≫ gη =
        Spec.map (CommRingCat.ofHom β.hom.toRingHom) ≫ gη) : α = β := by
    apply completeLocalAlg_points_injective_of_eq hη.1 g _ A α β he
    intro A α β hab
    apply Deformation.CompleteLocalAlgCat.Hom.ext
    apply AlgHom.coe_ringHom_injective
    exact @pointMaps_injective A _ _ _ α.hom.toRingHom β.hom.toRingHom
      α.isLocal β.isLocal hab
  have completeLocal_points (hiMono : Mono iΛ)
      (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k)
      (f : Spec (.of A) ⟶ U.left)
      (hfbase : f ≫ U.hom = Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ)
      (hfres : Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap A)) ≫ f =
        schemeMap q hx₀ hx r₀) :
      ∃! α : Deformation.Artin.FormalObject.completeLocalBase ξ Λ ⟶
          Deformation.artinianToComplete.obj A,
        Spec.map (CommRingCat.ofHom α.hom.toRingHom) ≫ g = f := by
    have := hiMono
    have hres : Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap A)) ≫ f =
        Spec.map (CommRingCat.ofHom (residue ξ.base.R)) ≫ g := hfres.trans r₀_base
    have : IsLocalHom (Deformation.Artin.residueMap A) := IsLocalHom.of_surjective _
      (A.residueEquiv.surjective.comp (residue_surjective (R := A)))
    have : IsLocalHom (CommRingCat.ofHom (residue ξ.base.R)).hom :=
      IsLocalHom.of_surjective _ (residue_surjective (R := ξ.base.R))
    have hf : f (closedPoint A) = u₀ := by
      have he := congrArg (fun t : Spec (.of k) ⟶ U.left => t (closedPoint k)) hres
      exact (closedPoint_comp_eq (CommRingCat.ofHom (Deformation.Artin.residueMap A))
        f).symm.trans (he.trans
          ((closedPoint_comp_eq (CommRingCat.ofHom (residue ξ.base.R)) g).trans
            g_closedPoint))
    exact exists_completeLocalAlgHom_of_completionPresentation iΛ U u₀
      (Deformation.Artin.FormalObject.completeLocalBase ξ Λ) e g hg (hΛ.trans hbase) A f hf
      hfbase hres
  have hpoints (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k)
      (f : Spec (.of A) ⟶ U.left)
      (hfbase : f ≫ U.hom = Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ)
      (hfres : Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap A)) ≫ f =
        schemeMap q hx₀ hx r₀) :
      ∃ α : η.base ⟶ Deformation.artinianToComplete.obj A,
        Spec.map (CommRingCat.ofHom α.hom.toRingHom) ≫ gη = f :=
    completeLocalAlg_points_of_eq hη.1 g A f
      (completeLocal_points inferInstance A f hfbase hfres).exists
  rw [← r₀_base]
  constructor
  · intro hl P
    exact isSmooth_of_liftsAtResiduePoint B S hS p hp hx₀ C η.base
      (Deformation.associatedMorphism hpC η P).toBasedFunctor
      U hx (toOriginal P) gη (toOriginal_base P) r₀ (toOriginal_closedPoint P)
      hpoints pointMapsη_injective hl
  · intro hv
    let P : Deformation.ChosenPushforwards C.projection :=
      Deformation.chosenPushforwardsOfCofibered C.projection hpC
    exact liftsAtResiduePoint_of_isSmooth B S hS p hp hx₀ C η.base
      (Deformation.associatedMorphism hpC η P).toBasedFunctor
      U hx (toOriginal P) gη (toOriginal_base P) r₀ hpoints (hv P)

/-- With the notation of **Stacks 07XF**, let `R` be the completed local ring of `U` at a finite
type point `u₀`, presented by a ring equivalence `e`, and let `ξ` be the formal object attached
by the approximation functor of **Stacks 07X6** to a Cartesian restriction `x_R` of `x` over
`Spec R`. Then `x` is versal at `u₀` exactly when `ξ` is versal in the sense of
**Stacks 0CXJ**. -/
@[stacks 0CXK]
public theorem isVersalAt_iff_isVersal
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : Type v} [Category.{w} F]
    (p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids)
    (U : Over S) (x : F)
    (hx : (p ⋙ Over.post B.inclusion).obj x = U)
    (u₀ : U.left)
    [IsLocallyNoetherian S] [LocallyOfFiniteType U.hom]
    (_hu₀ : AlgebraicGeometry.IsFiniteTypePoint u₀)
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
    (_hr : p.IsCartesian (p.map r) r)
    (hrbase : HEq
      ((eqToHom (Deformation.Artin.chosenBase_eq B S hS p xR.obj).symm ≫
        p.map r).left.hom ≫ eqToHom (congrArg Over.left hx)) g)
    (Λ : Type u) [CommRing Λ] [Algebra Λ ξ.base.R]
    (hΛstalk : CommRingCat.of Λ = S.presheaf.stalk (Deformation.Artin.basePoint U u₀))
    (iΛ : Spec (.of Λ) ⟶ S)
    (hiΛ : HEq iΛ (S.fromSpecStalk (Deformation.Artin.basePoint U u₀)))
    (hΛ : Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base.R)) ≫ iΛ =
      ξ.base.toS) :
    Deformation.Artin.IsVersalAt U (p ⋙ Over.post B.inclusion) u₀ x hx ↔
      Deformation.Artin.FormalObject.IsVersal B S hS p hp ξ Λ iΛ hΛ := by
  have : IsLocallyNoetherian U.left := LocallyOfFiniteType.isLocallyNoetherian U.hom
  have hRing := congr_arg_heq
    (fun A : CommRingCat.{u} => (inferInstance : CommRing A)) hΛstalk
  have hΛcarrier : Λ = S.presheaf.stalk (Deformation.Artin.basePoint U u₀) :=
    congrArg (fun A : CommRingCat.{u} => (A : Type u)) hΛstalk
  subst Λ
  have hRing' := eq_of_heq hRing
  cases hRing'
  have hiΛ' := eq_of_heq hiΛ
  cases hiΛ'
  exact (isVersalAt_iff_liftsAtCompletionResiduePoint U (p ⋙ Over.post B.inclusion) u₀ x hx
      e g hg (hΛ.trans hbase)).trans
    (liftsAtResiduePoint_iff_isVersal B S hS p hp U x hx u₀ xR ξ hξ e g hg hbase r _hr hrbase
      _ _ hΛ)

/-- **Versality of a formal object of a predeformation category from its realization.** Let `η`
be a formal object of the predeformation category of `x₀` over `𝒞_Λ`, and let `r_n` be compatible
arrows from its levels to an object `x` over `U`, lying over `Spec(η.base / 𝔪^{n+1}) ⟶ Spec η.base
⟶ U` for a morphism `g : Spec η.base ⟶ U`, all compatible with the arrows out of `x₀`. If `g`
identifies the points of `U` over Artinian local `Λ`-algebras lifting the closed point with the
local homomorphisms out of `η.base` (`hpoints`, `hinj`), then `η` is versal exactly when `x` has
the lifting property at the residue point `x₀ ⟶ x`.

This is the core of `Deformation.Artin.liftsAtResiduePoint_iff_isVersal`, with the completion
of `U` at a point replaced by any `g` with the two point-lifting properties; it applies in
particular to `U = Spec η.base` and `g` the identity, i.e. to an object over `Spec η.base`
realizing `η`. -/
public theorem liftsAtResiduePoint_iff_isVersal_of_restrictions
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : Type v} [Category.{w} F] (p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {iΛ : Spec (.of Λ) ⟶ S} {x₀ : F}
    (hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (η : Deformation.FormalObject
      (Deformation.Artin.predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection)
    {x : F} (U : Over S) (hx : (p ⋙ Over.post B.inclusion).obj x = U)
    (g : Spec (.of η.base) ⟶ U.left)
    (r : ∀ n, (deformationForget (Deformation.Artin.predeformationCategory iΛ
      (p ⋙ Over.post B.inclusion) x₀ hx₀)).obj (.op (η.level n)) ⟶ x)
    (hr : ∀ n, (deformationForget (Deformation.Artin.predeformationCategory iΛ
      (p ⋙ Over.post B.inclusion) x₀ hx₀)).map (η.transition n).op ≫ r (n + 1) = r n)
    (hbase : ∀ n,
      eqToHom (congrArg Over.left (deformationPointBase (Deformation.Artin.predeformationCategory
          iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀) (η.level n)
          (Deformation.AdicTruncation.obj η.base n) (η.level_eq n))).symm ≫
        ((p ⋙ Over.post B.inclusion).map (r n)).left ≫ eqToHom (congrArg Over.left hx) =
      Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (Deformation.AdicTruncation.ideal η.base n))) ≫ g)
    (r₀ : x₀ ⟶ x)
    (hclosed : ∀ n, ((Deformation.Artin.predeformationCategory iΛ (p ⋙ Over.post B.inclusion)
      x₀ hx₀).objects (η.level n)).arrow ≫ r n = r₀)
    (hpoints : ∀ (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k)
      (f : Spec (.of A) ⟶ U.left),
      f ≫ U.hom = Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ →
      Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap A)) ≫ f =
        schemeMap (p ⋙ Over.post B.inclusion) hx₀ hx r₀ →
      ∃ α : η.base ⟶ Deformation.artinianToComplete.obj A,
        Spec.map (CommRingCat.ofHom α.hom.toRingHom) ≫ g = f)
    (hinj : ∀ (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k)
      (α β : η.base ⟶ Deformation.artinianToComplete.obj A),
      Spec.map (CommRingCat.ofHom α.hom.toRingHom) ≫ g =
        Spec.map (CommRingCat.ofHom β.hom.toRingHom) ≫ g → α = β) :
    LiftsAtResiduePoint iΛ (p ⋙ Over.post B.inclusion) U x hx
        (schemeMap (p ⋙ Over.post B.inclusion) hx₀ hx r₀) ↔
      Deformation.IsVersal (Deformation.Artin.predeformationCategory_isPredeformationCategory
        B hS iΛ p x₀ hx₀ hp).cofibered η := by
  let C := Deformation.Artin.predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀
  let : Category C.carrier := C.category
  let hpC := (Deformation.Artin.predeformationCategory_isPredeformationCategory
    B hS iΛ p x₀ hx₀ hp).cofibered
  let toOriginal (P : Deformation.ChosenPushforwards C.projection) :=
    associatedMorphismRestriction η (Deformation.associatedMorphism hpC η P)
      (deformationForget C) r hr
  have toOriginal_closedPoint (P : Deformation.ChosenPushforwards C.projection)
      (α : (Deformation.restrictedCoyoneda η.base).Elements) :
      (C.objects ((Deformation.associatedMorphism hpC η P).toBasedFunctor.obj α)).arrow ≫
        (toOriginal P).app (.op α) = r₀ :=
    associatedMorphismRestriction_closedPoint C η _ r hr r₀ hclosed α
  have toOriginal_base (P : Deformation.ChosenPushforwards C.projection)
      (α : (Deformation.restrictedCoyoneda η.base).Elements) :
      schemeMap (p ⋙ Over.post B.inclusion) (deformationPointBase C
        ((Deformation.associatedMorphism hpC η P).toBasedFunctor.obj α) α.1
        ((Deformation.associatedMorphism hpC η P).toBasedFunctor.w_obj α)) hx
          ((toOriginal P).app (.op α)) =
        Spec.map (CommRingCat.ofHom α.2.hom.toRingHom) ≫ g :=
    associatedMorphismRestriction_base C η _ r hr U hx g hbase α
  constructor
  · intro hl P
    exact isSmooth_of_liftsAtResiduePoint B S hS p hp hx₀ C η.base
      (Deformation.associatedMorphism hpC η P).toBasedFunctor
      U hx (toOriginal P) g (toOriginal_base P) r₀ (toOriginal_closedPoint P)
      hpoints hinj hl
  · intro hv
    let P : Deformation.ChosenPushforwards C.projection :=
      Deformation.chosenPushforwardsOfCofibered C.projection hpC
    exact liftsAtResiduePoint_of_isSmooth B S hS p hp hx₀ C η.base
      (Deformation.associatedMorphism hpC η P).toBasedFunctor
      U hx (toOriginal P) g (toOriginal_base P) r₀ hpoints (hv P)

end Deformation.Artin

end
