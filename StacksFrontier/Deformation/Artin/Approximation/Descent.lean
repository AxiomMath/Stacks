module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.RingTheory.Localization.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.SpecField
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.LimitPreservingOnObjects
public import StacksFrontier.CategoryTheory.Sites.Gerbe.Equivalence
public import StacksFrontier.Deformation.Artin.Approximation.QuotientEquiv
public import StacksFrontier.Deformation.Artin.Approximation.TruncationIso
public import StacksFrontier.RingTheory.AdicCompletion.PolynomialSurjection
public import StacksFrontier.RingTheory.Algebra.DirectLimit.FinitePresentation
public import StacksFrontier.RingTheory.ArtinRees.AssociatedGraded
public import StacksFrontier.RingTheory.ArtinRees.Constant
public import StacksFrontier.RingTheory.Etale.AssociatedGraded
public import StacksFrontier.RingTheory.Filtration.AssociatedGraded
public import StacksFrontier.RingTheory.GRing.Defs
public import StacksFrontier.RingTheory.GRing.EssFiniteType
public import StacksFrontier.RingTheory.Noetherian.ArtinRees
public import StacksFrontier.RingTheory.Smoothing.ApproximationGRing
import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
import all StacksFrontier.Deformation.Artin.Approximation.QuotientEquiv
import all StacksFrontier.Deformation.Artin.Approximation.TruncationIso

/-!
# Approximation over a complete local ring: descent and graded comparison

Third part of `StacksFrontier.Deformation.Artin.Approximation`. It contains the steps of the
proof of Stacks 07XB that are elaborated separately: the assembly of the conclusion from
abstract approximation data, the descent step through limit preservation on objects, the
Artin-Rees precision for equal graded-piece denominators, and clause (6) over abstract
approximation data.

## References

* [Stacks Project, Tag 07XB](https://stacks.math.columbia.edu/tag/07XB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing AssociatedGraded

namespace Deformation.Artin.Approximation

universe u v w

/-- The conclusion of Stacks 07XB, assembled from the approximation data.

Stating the assembly over abstract data is what keeps it affordable: unifying the nested
existential of the conclusion directly against the `let`-bound definitions of the
construction forces all of them to be unfolded. -/
private theorem exists_approximation_of_data
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (Site B S hS))
    (R : Type u) [CommRing R] [IsLocalRing R]
    (hR : B.Contains (Spec (.of R)))
    (fR : Spec (.of R) ⟶ S)
    (x : 𝒳.val.p.Fiber (siteObject B S hS hR fR))
    (N : ℕ)
    (A : Type u) [instA : CommRing A] (mA : Ideal A) (hmA : mA.IsMaximal)
    (fA : Spec (.of A) ⟶ S)
    (hA : B.Contains (Spec (.of A)))
    (hRN : B.Contains (Spec (.of (R ⧸ maximalIdeal R ^ N))))
    (hAN : B.Contains (Spec (.of (A ⧸ mA ^ N))))
    (xA : 𝒳.val.p.Fiber (siteObject B S hS hA fA))
    (hfinA : LocallyOfFiniteType fA) (hqcA : QuasiCompact fA)
    (φ : (R ⧸ maximalIdeal R ^ N) ≃+* (A ⧸ mA ^ N))
    (hφ : Spec.map (CommRingCat.ofHom φ.symm.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (mA ^ N))) ≫ fA =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((maximalIdeal R) ^ N))) ≫ fR)
    (iR : siteObject B S hS hRN
        (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk ((maximalIdeal R) ^ N))) ≫ fR) ⟶
        siteObject B S hS hR fR)
    (iA : siteObject B S hS hAN
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (mA ^ N))) ≫ fA) ⟶
        siteObject B S hS hA fA)
    (eBase : siteObject B S hS hRN
        (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk ((maximalIdeal R) ^ N))) ≫ fR) ⟶
        siteObject B S hS hAN
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (mA ^ N))) ≫ fA))
    (xRN : 𝒳.val.p.Fiber (siteObject B S hS hRN
        (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk ((maximalIdeal R) ^ N))) ≫ fR)))
    (xAN : 𝒳.val.p.Fiber (siteObject B S hS hAN
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (mA ^ N))) ≫ fA)))
    (r : xRN.1 ⟶ x.1) (a : xAN.1 ⟶ xA.1) (e : xRN.1 ⟶ xAN.1)
    (hiR : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map iR =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((maximalIdeal R) ^ N))))
    (hiA : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map iA =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (mA ^ N))))
    (heBase : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map eBase =
      Spec.map (CommRingCat.ofHom φ.symm.toRingHom))
    (hcartR : 𝒳.val.p.IsStronglyCartesian iR r)
    (hcartA : 𝒳.val.p.IsStronglyCartesian iA a)
    (hlift : 𝒳.val.p.IsHomLift eBase e) (hiso : IsIso e)
    (gr : AssociatedGraded.gradedRing (maximalIdeal R) ≃+*
      AssociatedGraded.gradedRing mA)
    (hgrGrade : ∀ n (z : AssociatedGraded.piece (M := R) (maximalIdeal R) n),
      ∃ w : AssociatedGraded.piece (M := A) mA n,
        gr (DirectSum.of _ n z) = DirectSum.of _ n w)
    (hgrZero : ∀ (r₀ : R) (a₀ : A),
      φ (Ideal.Quotient.mk ((maximalIdeal R) ^ N) r₀) =
          Ideal.Quotient.mk (mA ^ N) a₀ →
      gr (DirectSum.of _ 0
            (AssociatedGraded.mk (maximalIdeal R) 0
              (⟨r₀, by simp⟩ : AssociatedGraded.power (M := R) (maximalIdeal R) 0))) =
        DirectSum.of _ 0
          (AssociatedGraded.mk mA 0
            (⟨a₀, by simp⟩ : AssociatedGraded.power (M := A) mA 0))) :
    ∃ (A : Type u) (_ : CommRing A) (mA : Ideal A) (_ : mA.IsMaximal)
      (fA : Spec (.of A) ⟶ S)
      (hA : B.Contains (Spec (.of A)))
      (hRN : B.Contains (Spec (.of (R ⧸ maximalIdeal R ^ N))))
      (hAN : B.Contains (Spec (.of (A ⧸ mA ^ N))))
      (xA : 𝒳.val.p.Fiber (siteObject B S hS hA fA)),
      LocallyOfFiniteType fA ∧ QuasiCompact fA ∧
      ∃ (φ : (R ⧸ maximalIdeal R ^ N) ≃+* (A ⧸ mA ^ N)),
        Spec.map (CommRingCat.ofHom φ.symm.toRingHom) ≫
            Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (mA ^ N))) ≫ fA =
          Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((maximalIdeal R) ^ N))) ≫ fR ∧
        ∃ (iR : siteObject B S hS hRN
              (Spec.map (CommRingCat.ofHom
                (Ideal.Quotient.mk ((maximalIdeal R) ^ N))) ≫ fR) ⟶
              siteObject B S hS hR fR)
          (iA : siteObject B S hS hAN
              (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (mA ^ N))) ≫ fA) ⟶
              siteObject B S hS hA fA)
          (eBase : siteObject B S hS hRN
              (Spec.map (CommRingCat.ofHom
                (Ideal.Quotient.mk ((maximalIdeal R) ^ N))) ≫ fR) ⟶
              siteObject B S hS hAN
                (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (mA ^ N))) ≫ fA))
          (xRN : 𝒳.val.p.Fiber (siteObject B S hS hRN
              (Spec.map (CommRingCat.ofHom
                (Ideal.Quotient.mk ((maximalIdeal R) ^ N))) ≫ fR)))
          (xAN : 𝒳.val.p.Fiber (siteObject B S hS hAN
              (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (mA ^ N))) ≫ fA)))
          (r : xRN.1 ⟶ x.1) (a : xAN.1 ⟶ xA.1)
          (e : xRN.1 ⟶ xAN.1),
          (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map iR =
              Spec.map (CommRingCat.ofHom
                (Ideal.Quotient.mk ((maximalIdeal R) ^ N))) ∧
          (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map iA =
              Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (mA ^ N))) ∧
          (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map eBase =
              Spec.map (CommRingCat.ofHom φ.symm.toRingHom) ∧
          𝒳.val.p.IsStronglyCartesian iR r ∧
          𝒳.val.p.IsStronglyCartesian iA a ∧
          𝒳.val.p.IsHomLift eBase e ∧ IsIso e ∧
          ∃ (gr : AssociatedGraded.gradedRing (maximalIdeal R) ≃+*
              AssociatedGraded.gradedRing mA),
            (∀ n (z : AssociatedGraded.piece (M := R) (maximalIdeal R) n),
              ∃ w : AssociatedGraded.piece (M := A) mA n,
                gr (DirectSum.of _ n z) = DirectSum.of _ n w) ∧
            ∀ (r₀ : R) (a₀ : A),
              φ (Ideal.Quotient.mk ((maximalIdeal R) ^ N) r₀) =
                  Ideal.Quotient.mk (mA ^ N) a₀ →
              gr (DirectSum.of _ 0
                    (AssociatedGraded.mk (maximalIdeal R) 0
                      (⟨r₀, by simp⟩ :
                        AssociatedGraded.power (M := R) (maximalIdeal R) 0))) =
                DirectSum.of _ 0
                  (AssociatedGraded.mk mA 0
                    (⟨a₀, by simp⟩ : AssociatedGraded.power (M := A) mA 0)) :=
  ⟨A, instA, mA, hmA, fA, hA, hRN, hAN, xA, hfinA, hqcA, φ, hφ, iR, iA, eBase,
    xRN, xAN, r, a, e, hiR, hiA, heBase, hcartR, hcartA, hlift, hiso,
    gr, hgrGrade, hgrZero⟩

/-- **Stacks 07XB, descent step.** Limit preservation on objects lets an object over
`Spec R` descend to a finitely presented stage.

`R` is the filtered colimit of its finitely presented `Λ`-subalgebras, so `Spec R` is the
inverse limit of the corresponding affine schemes over `S`. Limit preservation therefore
produces a finitely presented `Λ`-algebra `C`, an object `x'` over `Spec C`, and a
cartesian comparison `δ` over the structure map `Spec R → Spec C`, matched with `x` up to
the vertical isomorphism `β`.

Isolating this step is what keeps the main theorem affordable: the direct system, the cone
and the colimit computation are elaborated once here instead of inside the main proof. -/
private theorem exists_descent_of_limitPreserving
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (Site B S hS))
    (hp : AlgebraicGeometry.BigFppfOver.IsLimitPreservingOnObjects.{u, u, u, u, u + 1} B S hS 𝒳
      (baseFiberedCategory B S hS) (structureMorphism B S hS 𝒳))
    (Λ : Type u) [CommRing Λ] (uΛ : Spec (.of Λ) ⟶ S)
    (hΛsite : B.Contains (Spec (.of Λ)))
    (R : Type u) [CommRing R] [Algebra Λ R] (hR : B.Contains (Spec (.of R)))
    (fR : Spec (.of R) ⟶ S)
    (hfΛR : Spec.map (CommRingCat.ofHom (algebraMap Λ R)) ≫ uΛ = fR)
    (x : 𝒳.val.p.Fiber (siteObject B S hS hR fR)) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra Λ C)
      (_ : Algebra.FinitePresentation Λ C) (toRC : C →ₐ[Λ] R)
      (hCsite : B.Contains (Spec (.of C)))
      (hfC : Spec.map (CommRingCat.ofHom toRC.toRingHom) ≫
        (Spec.map (CommRingCat.ofHom (algebraMap Λ C)) ≫ uΛ) = fR)
      (x' : 𝒳.val.p.Fiber (siteObject B S hS hCsite
        (Spec.map (CommRingCat.ofHom (algebraMap Λ C)) ≫ uΛ)))
      (xU : 𝒳.val.p.Fiber (siteObject B S hS hR fR))
      (δ : xU.1 ⟶ x'.1) (β : xU.1 ⟶ x.1),
      𝒳.val.p.IsStronglyCartesian
        (siteObjectHom B S hS hR hCsite fR
          (Spec.map (CommRingCat.ofHom (algebraMap Λ C)) ≫ uΛ)
          (Spec.map (CommRingCat.ofHom toRC.toRingHom)) hfC) δ ∧
      𝒳.val.p.IsHomLift (𝟙 (siteObject B S hS hR fR)) β ∧ IsIso β := by
  classical
  obtain ⟨J, orderJ, nonemptyJ, directedJ, G, ringG, algebraG,
    transition, systemG, toR, compatibleG, finitePresentationG, _, colimitG⟩ :=
    Algebra.exists_directedSystem_finitePresentation_lift_bijective Λ R
  let : PartialOrder J := orderJ
  let : Nonempty J := nonemptyJ
  let : IsDirectedOrder J := directedJ
  let instRingG (j : J) : CommRing (G j) := ringG j
  let instAlgebraG (j : J) : Algebra Λ (G j) := algebraG j
  let : DirectedSystem G (fun i j h ↦ ⇑(transition i j h)) := systemG
  have hGsite (j : J) : B.Contains (Spec (.of (G j))) := by
    let : Algebra.FinitePresentation Λ (G j) := finitePresentationG j
    exact Scheme.size_Spec_lt_of_finiteType B.aleph0_lt_cutoff
      B.cutoff_isStrongPrelimit Λ (G j) hΛsite
  let fG (j : J) : Spec (.of (G j)) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap Λ (G j))) ≫ uΛ
  have hfG {C D : Type u} [CommRing C] [CommRing D] [Algebra Λ C] [Algebra Λ D]
      (g : C →ₐ[Λ] D) :
      Spec.map (CommRingCat.ofHom g.toRingHom) ≫
        (Spec.map (CommRingCat.ofHom (algebraMap Λ C)) ≫ uΛ) =
      Spec.map (CommRingCat.ofHom (algebraMap Λ D)) ≫ uΛ := by
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 3
    exact g.comp_algebraMap
  have htoR (j : J) :
      Spec.map (CommRingCat.ofHom (toR j).toRingHom) ≫ fG j = fR :=
    (hfG (toR j)).trans hfΛR
  have htransition (i j : J) (hij : i ≤ j) :
      Spec.map (CommRingCat.ofHom (transition i j hij).toRingHom) ≫ fG i = fG j :=
    hfG (transition i j hij)
  have stage_hom_ext {X Y : AlgebraicGeometry.BigAffineFppf B S hS} {f g : X ⟶ Y}
      (h : (AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map f =
        (AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map g) : f = g := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact h
  let stage (j : J) : AlgebraicGeometry.BigAffineFppf B S hS :=
    ⟨siteObject B S hS (hGsite j) (fG j), by
      change IsAffine (Spec (.of (G j)))
      infer_instance⟩
  let stageMap {i j : Jᵒᵖ} (a : i ⟶ j) : stage i.unop ⟶ stage j.unop :=
    ObjectProperty.homMk (X := stage i.unop) (Y := stage j.unop)
      (siteObjectHom B S hS (hGsite i.unop) (hGsite j.unop)
        (fG i.unop) (fG j.unop)
        (Spec.map (CommRingCat.ofHom
          (transition j.unop i.unop (leOfHom a.unop)).toRingHom))
        (htransition j.unop i.unop (leOfHom a.unop)))
  have hstageMap_id (i : Jᵒᵖ) : stageMap (𝟙 i) = 𝟙 (stage i.unop) := by
    apply stage_hom_ext
    change Spec.map (CommRingCat.ofHom
        (transition i.unop i.unop le_rfl).toRingHom) = 𝟙 _
    have htr : (transition i.unop i.unop le_rfl).toRingHom = RingHom.id _ := by
      ext z
      exact DirectedSystem.map_self' transition z
    rw [htr]
    simp
  have hstageMap_comp {i j k : Jᵒᵖ} (a : i ⟶ j) (b : j ⟶ k) :
      stageMap (a ≫ b) = stageMap a ≫ stageMap b := by
    apply stage_hom_ext
    change Spec.map (CommRingCat.ofHom
        (transition k.unop i.unop (leOfHom (a ≫ b).unop)).toRingHom) =
      Spec.map (CommRingCat.ofHom
        (transition j.unop i.unop (leOfHom a.unop)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (transition k.unop j.unop (leOfHom b.unop)).toRingHom)
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1
    ext z
    exact (DirectedSystem.map_map' transition
      (leOfHom b.unop) (leOfHom a.unop) z).symm
  let D : Jᵒᵖ ⥤ AlgebraicGeometry.BigAffineFppf B S hS := {
    obj := fun i ↦ stage i.unop
    map := fun a ↦ stageMap a
    map_id := hstageMap_id
    map_comp := hstageMap_comp }
  let limitStage : AlgebraicGeometry.BigAffineFppf B S hS :=
    ⟨siteObject B S hS hR fR, by
      change IsAffine (Spec (.of R))
      infer_instance⟩
  let limitMap (j : Jᵒᵖ) : limitStage ⟶ D.obj j :=
    ObjectProperty.homMk (X := limitStage) (Y := D.obj j)
      (siteObjectHom B S hS hR (hGsite j.unop) fR (fG j.unop)
        (Spec.map (CommRingCat.ofHom (toR j.unop).toRingHom))
        (htoR j.unop))
  have hlimitMap (i j : Jᵒᵖ) (a : i ⟶ j) :
      limitMap i ≫ D.map a = limitMap j := by
    apply stage_hom_ext
    change Spec.map (CommRingCat.ofHom (toR i.unop).toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (transition j.unop i.unop (leOfHom a.unop)).toRingHom) =
      Spec.map (CommRingCat.ofHom (toR j.unop).toRingHom)
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1
    ext z
    exact compatibleG j.unop i.unop (leOfHom a.unop) z
  let c : CategoryTheory.Limits.Cone D := {
    pt := limitStage
    π := { app := limitMap
           naturality := by
             intro i j a
             simpa using (hlimitMap i j a).symm } }
  let F : J ⥤ CommRingCat.{u} := {
    obj := fun j ↦ CommRingCat.of (G j)
    map := fun {i j} a ↦ CommRingCat.ofHom
      (transition i j (leOfHom a)).toRingHom
    map_id := by
      intro i
      ext z
      exact DirectedSystem.map_self' transition z
    map_comp := by
      intro i j k a b
      ext z
      exact (DirectedSystem.map_map' transition
        (leOfHom a) (leOfHom b) z).symm }
  let cRing : CategoryTheory.Limits.Cocone F := {
    pt := CommRingCat.of R
    ι := {
      app := fun j ↦ CommRingCat.ofHom (toR j).toRingHom
      naturality := by
        intro i j a
        ext z
        exact compatibleG i j (leOfHom a) z } }
  have hcRing : CategoryTheory.Limits.IsColimit cRing := by
    let := CategoryTheory.Limits.reflectsColimit_of_reflectsIsomorphisms
      F (forget CommRingCat)
    apply CategoryTheory.Limits.isColimitOfReflects (forget CommRingCat)
    apply CategoryTheory.Limits.Types.FilteredColimit.isColimitOf'
    · intro z
      obtain ⟨v, hv⟩ := colimitG.2 z
      obtain ⟨j, a, rfl⟩ := DirectLimit.exists_eq_mk _ v
      exact ⟨j, a, hv.symm⟩
    · intro i a b hab
      change toR i a = toR i b at hab
      have hEq : (⟦⟨i, a⟩⟧ : DirectLimit G
          (fun i j h ↦ (transition i j h).toRingHom)) = ⟦⟨i, b⟩⟧ :=
        colimitG.1 hab
      obtain ⟨j, hij, _, heq⟩ := Quotient.exact hEq
      exact ⟨j, homOfLE hij, heq⟩
  have hcScheme : CategoryTheory.Limits.IsLimit
      ((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).mapCone c) := by
    convert CategoryTheory.Limits.isLimitOfPreserves Scheme.Spec hcRing.op using 1 <;>
      rfl
  let : IsCofiltered Jᵒᵖ := inferInstance
  let i₀ : Jᵒᵖ := Opposite.op (Classical.arbitrary J)
  let y₀ : (baseFiberedCategory B S hS).val.p.Fiber
      ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj (D.obj i₀)) :=
    ⟨(AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj (D.obj i₀), rfl⟩
  let hxBase : 𝒳.val.p.obj x.1 =
      (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj c.pt := x.2
  let γ : (CatFiberedInGroupoids.homFunctor
      (structureMorphism B S hS 𝒳)).obj x.1 ⟶ y₀.1 :=
    eqToHom hxBase ≫
      (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map (c.π.app i₀)
  have hγ : (baseFiberedCategory B S hS).val.p.IsStronglyCartesian
      ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map (c.π.app i₀)) γ := by
    have : (baseFiberedCategory B S hS).val.p.IsHomLift
        ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map (c.π.app i₀)) γ := by
      apply IsHomLift.of_fac (baseFiberedCategory B S hS).val.p _ γ
        hxBase rfl
      change (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map (c.π.app i₀) =
        (eqToIso hxBase).inv ≫ (eqToIso hxBase).hom ≫
          (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map (c.π.app i₀)
      simp
    exact (baseFiberedCategory B S hS).isFiberedInGroupoids.isStronglyCartesian_homLift
      _ _
  obtain ⟨i', _, x', xU, δ, β, _, hδ, hβ, hβiso, _, _⟩ :=
    hp Jᵒᵖ D c hcScheme i₀ y₀ x γ hγ
  exact ⟨G i'.unop, ringG i'.unop, algebraG i'.unop, finitePresentationG i'.unop,
    toR i'.unop, hGsite i'.unop, htoR i'.unop, x', xU, δ, β, hδ, hβ, hβiso⟩

/-- Artin-Rees stability supplies a single constant with the following property: once a
presentation is replaced by one whose generators and whose syzygy coefficients are
congruent to the originals modulo that power of the maximal ideal, and which is still a
complex, the two presentations cut out the same denominators in every graded piece.

This is the input to the graded comparison of `ringGradedEquivOfDenomEq`; the constant has
to be produced *before* the approximating generators are known, because it is what fixes
the precision the approximation must be asked for. -/
theorem exists_artinRees_denominator_eq
    {P : Type u} [CommRing P] [IsLocalRing P] [IsNoetherianRing P]
    {rP tP : ℕ} (bP : Fin rP → P) (kP : Fin tP → Fin rP → P)
    (hExact : LinearMap.ker (Fintype.linearCombination P bP) =
      LinearMap.range (Fintype.linearCombination P kP)) :
    ∃ c : ℕ, ∀ (bP' : Fin rP → P) (kP' : Fin tP → Fin rP → P),
      (∀ j, bP j - bP' j ∈ maximalIdeal P ^ (c + 1)) →
      (∀ i j, kP i j - kP' i j ∈ maximalIdeal P ^ (c + 1)) →
      (∀ i, ∑ j, kP' i j * bP' j = 0) →
      ∀ n, (power (M := P) (maximalIdeal P) (n + 1) ⊔
            (Ideal.span (Set.range bP) : Submodule P P)).comap
            (power (maximalIdeal P) n).subtype =
          (power (M := P) (maximalIdeal P) (n + 1) ⊔
            (Ideal.span (Set.range bP') : Submodule P P)).comap
            (power (maximalIdeal P) n).subtype := by
  classical
  let g : (Fin rP → P) →ₗ[P] P := Fintype.linearCombination P bP
  let f : (Fin tP → P) →ₗ[P] (Fin rP → P) := Fintype.linearCombination P kP
  obtain ⟨cf, hcf⟩ := exists_comap_smul_eq_and_range_inf_le f (maximalIdeal P)
  obtain ⟨cg, hcg⟩ := exists_comap_smul_eq_and_range_inf_le g (maximalIdeal P)
  have hcf' : IsArtinReesConstant (maximalIdeal P) f cf := fun n hn ↦ (hcf n hn).2
  have hcg' : IsArtinReesConstant (maximalIdeal P) g cg := fun n hn ↦ (hcg n hn).2
  have hfStable : IsArtinReesConstant (maximalIdeal P) f (max cf cg) :=
    hcf'.mono (le_max_left _ _)
  have hgStable : IsArtinReesConstant (maximalIdeal P) g (max cf cg) :=
    hcg'.mono (le_max_right _ _)
  have hjac : maximalIdeal P ≤ (⊥ : Ideal P).jacobson :=
    IsLocalRing.maximalIdeal_le_jacobson ⊥
  refine ⟨max cf cg, fun bP' kP' hb hk hsyz n ↦ ?_⟩
  let g' : (Fin rP → P) →ₗ[P] P := Fintype.linearCombination P bP'
  let f' : (Fin tP → P) →ₗ[P] (Fin rP → P) := Fintype.linearCombination P kP'
  have hComplex : g'.comp f' = 0 := by
    apply LinearMap.range_le_ker_iff.mp
    rw [Fintype.range_linearCombination]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change (∑ j, kP' i j * bP' j) = 0
    exact hsyz i
  have hgg : CongruentModPow (maximalIdeal P) g g' (max cf cg + 1) := by
    rintro _ ⟨a, rfl⟩
    change (g - g') a ∈ maximalIdeal P ^ (max cf cg + 1) • (⊤ : Submodule P P)
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
    change g a - g' a ∈ maximalIdeal P ^ (max cf cg + 1)
    change (∑ j, a j * bP j) - (∑ j, a j * bP' j) ∈ _
    rw [← Finset.sum_sub_distrib]
    apply Ideal.sum_mem
    intro j _
    rw [← mul_sub]
    exact (maximalIdeal P ^ (max cf cg + 1)).mul_mem_left _ (hb j)
  have hff : CongruentModPow (maximalIdeal P) f f' (max cf cg + 1) := by
    rintro _ ⟨a, rfl⟩
    apply mem_ideal_smul_top_pi
    intro j
    have hcoord : ((f - f') a) j = ∑ i, a i * (kP i j - kP' i j) := by
      simp [f, f', Fintype.linearCombination_apply, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
    rw [hcoord]
    apply Ideal.sum_mem
    intro i _
    exact (maximalIdeal P ^ (max cf cg + 1)).mul_mem_left _ (hk i j)
  have hg'Stable : IsArtinReesConstant (maximalIdeal P) g' (max cf cg) :=
    (artinRees_stability (maximalIdeal P) hjac f f' g g' (max cf cg)
      hComplex hfStable hgStable hExact hff hgg).1
  have hrange {r : ℕ} (b : Fin r → P) : LinearMap.range (Fintype.linearCombination P b) =
      (Ideal.span (Set.range b) : Submodule P P) := by
    rw [Fintype.range_linearCombination]
  simpa only [g, g', hrange] using
    presentation_denominator_eq (maximalIdeal P) g g' (max cf cg) n hgStable hg'Stable hgg

/-- Clause (6) of Stacks 07XB over abstract approximation data.

The approximating ring is `Afin`, reached from the complete ring `P` through the étale
`B'` and its quotient `B' ⧸ JB`. The graded isomorphism is the composite of four
comparisons: `P ⧸ ker φP ≅ R`, the change of denominators `ker φP ⇝ JP` supplied by
`hden`, the étale quotient `B' ⧸ JB → P ⧸ JP`, and the localization `Afin → B' ⧸ JB`.
Each of the three ring maps induces an isomorphism on associated graded rings because it
induces one on every truncation. -/
theorem exists_gradedRingEquiv_of_approximation
    {P R B' Afin : Type u} [CommRing P] [IsLocalRing P] [CommRing R] [IsLocalRing R]
    [CommRing B'] [CommRing Afin]
    (φP : P →+* R) (hφPsurj : Function.Surjective φP)
    (ιB : B' →+* P) (mB JB : Ideal B')
    (hι : mB ≤ Ideal.comap ιB (maximalIdeal P))
    (hιTrunc : ∀ n, Function.Bijective (Ideal.quotientMap (maximalIdeal P ^ n) ιB
      ((Ideal.pow_right_mono hι n).trans (Ideal.le_comap_pow ιB n))))
    (JP : Ideal P) (hJP : Ideal.map ιB JB = JP)
    (hden : ∀ n, (power (M := P) (maximalIdeal P) (n + 1) ⊔
          (RingHom.ker φP : Submodule P P)).comap (power (maximalIdeal P) n).subtype =
        (power (M := P) (maximalIdeal P) (n + 1) ⊔
          (JP : Submodule P P)).comap (power (maximalIdeal P) n).subtype)
    (mAfin : Ideal Afin) (inc : Afin →+* B' ⧸ JB)
    (hinc : mAfin ≤ Ideal.comap inc (Ideal.map (Ideal.Quotient.mk JB) mB))
    (hincTrunc : ∀ n, Function.Bijective (Ideal.quotientMap
      (Ideal.map (Ideal.Quotient.mk JB) mB ^ n) inc
      ((Ideal.pow_right_mono hinc n).trans (Ideal.le_comap_pow inc n))))
    (N : ℕ) (hN : 1 ≤ N)
    (eRtrunc : (R ⧸ maximalIdeal R ^ N) ≃+*
      ((B' ⧸ JB) ⧸ Ideal.map (Ideal.Quotient.mk JB) mB ^ N))
    (heApprox : ∀ (p : P) (b : B'), p - ιB b ∈ maximalIdeal P ^ N →
      eRtrunc (Ideal.Quotient.mk (maximalIdeal R ^ N) (φP p)) =
        Ideal.Quotient.mk _ (Ideal.Quotient.mk JB b))
    (eFin : (Afin ⧸ mAfin ^ N) ≃+*
      ((B' ⧸ JB) ⧸ Ideal.map (Ideal.Quotient.mk JB) mB ^ N))
    (heFin : ∀ a : Afin, eFin (Ideal.Quotient.mk (mAfin ^ N) a) =
      Ideal.Quotient.mk _ (inc a))
    (φ : (R ⧸ maximalIdeal R ^ N) ≃+* (Afin ⧸ mAfin ^ N))
    (hφ : ∀ z, eFin (φ z) = eRtrunc z) :
    ∃ gr : gradedRing (maximalIdeal R) ≃+* gradedRing mAfin,
      (∀ n (z : piece (M := R) (maximalIdeal R) n),
        ∃ w : piece (M := Afin) mAfin n,
          gr (DirectSum.of _ n z) = DirectSum.of _ n w) ∧
      (∀ (r₀ : R) (a₀ : Afin),
        φ (Ideal.Quotient.mk (maximalIdeal R ^ N) r₀) =
            Ideal.Quotient.mk (mAfin ^ N) a₀ →
        gr (DirectSum.of _ 0
              (mk (maximalIdeal R) 0
                (⟨r₀, mem_power_zero _ _⟩ : power (M := R) (maximalIdeal R) 0))) =
          DirectSum.of _ 0
            (mk mAfin 0 (⟨a₀, mem_power_zero _ _⟩ : power (M := Afin) mAfin 0))) := by
  classical
  let : IsLocalHom φP := IsLocalHom.of_surjective φP hφPsurj
  let KP := RingHom.ker φP
  let A₀ := B' ⧸ JB
  let mA₀ : Ideal A₀ := Ideal.map (Ideal.Quotient.mk JB) mB
  let IP : Ideal (P ⧸ KP) := Ideal.map (Ideal.Quotient.mk KP) (maximalIdeal P)
  let IQ : Ideal (P ⧸ JP) := Ideal.map (Ideal.Quotient.mk JP) (maximalIdeal P)
  let eGrQuot := ringGradedEquivOfDenomEq (maximalIdeal P) KP JP hden
  let ePR : (P ⧸ KP) ≃+* R := φP.quotientKerEquivOfSurjective hφPsurj
  have hePR (p : P) : ePR (Ideal.Quotient.mk KP p) = φP p :=
    RingHom.quotientKerEquivOfSurjective_apply_mk _ _
  have hIP : Ideal.map ePR.toRingHom IP = maximalIdeal R := by
    rw [Ideal.map_map]
    have hcomp : ePR.toRingHom.comp (Ideal.Quotient.mk KP) = φP := by
      ext p
      exact hePR p
    rw [hcomp]
    exact IsLocalRing.map_maximalIdeal_of_surjective φP hφPsurj
  have hePRI : IP ≤ Ideal.comap ePR.toRingHom (maximalIdeal R) :=
    Ideal.map_le_iff_le_comap.mp hIP.le
  have hePRTrunc (n : ℕ) : Function.Bijective (Ideal.quotientMap
      (maximalIdeal R ^ n) ePR.toRingHom
      ((Ideal.pow_right_mono hePRI n).trans (Ideal.le_comap_pow ePR.toRingHom n))) :=
    ringEquiv_trunc_bijective ePR IP (maximalIdeal R) hIP n
  let grR := gradedRingEquiv ePR.toRingHom IP (maximalIdeal R) hePRI hePRTrunc
  have hJBJP : JB ≤ Ideal.comap ιB JP := Ideal.map_le_iff_le_comap.mp hJP.le
  let qAQ : A₀ →+* (P ⧸ JP) := Ideal.quotientMap JP ιB hJBJP
  have hqAQ (b : B') : qAQ (Ideal.Quotient.mk JB b) = Ideal.Quotient.mk JP (ιB b) := rfl
  have hAQ : mA₀ ≤ Ideal.comap qAQ IQ := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_map]
    change Ideal.map ((Ideal.Quotient.mk JP).comp ιB) mB ≤ _
    rw [← Ideal.map_map]
    exact Ideal.map_mono (Ideal.map_le_iff_le_comap.mpr hι)
  have hAQTrunc (n : ℕ) : Function.Bijective (Ideal.quotientMap (IQ ^ n) qAQ
      ((Ideal.pow_right_mono hAQ n).trans (Ideal.le_comap_pow qAQ n))) :=
    quotient_trunc_bijective ιB mB JB (maximalIdeal P) JP hι hJP n
      (hιTrunc n) qAQ rfl hAQ
  let grAQ := gradedRingEquiv qAQ mA₀ IQ hAQ hAQTrunc
  let grFin := gradedRingEquiv inc mAfin mA₀ hinc hincTrunc
  refine ⟨((grR.symm.trans eGrQuot).trans grAQ.symm).trans grFin.symm, ?_, ?_⟩
  · intro n z
    obtain ⟨a, ha⟩ := gradedRingEquiv_symm_grade ePR.toRingHom IP
      (maximalIdeal R) hePRI hePRTrunc n z
    obtain ⟨b, hb⟩ := gradedRingEquiv_symm_grade qAQ mA₀ IQ hAQ hAQTrunc n
      (ringPieceEquiv (maximalIdeal P) KP JP n (hden n) a)
    obtain ⟨c, hc⟩ := gradedRingEquiv_symm_grade inc mAfin mA₀ hinc hincTrunc n b
    refine ⟨c, ?_⟩
    change grFin.symm (grAQ.symm (eGrQuot (grR.symm (DirectSum.of _ n z)))) = _
    rw [ha, ringGradedEquivOfDenomEq_of, hb, hc]
  · intro r₀ a₀ heq
    obtain ⟨p, rfl⟩ := hφPsurj r₀
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (inc a₀)
    have htrunc : eRtrunc (Ideal.Quotient.mk _ (φP p)) =
        Ideal.Quotient.mk _ (Ideal.Quotient.mk JB b) := by
      have h := congrArg eFin heq
      rwa [hφ, heFin, ← hb] at h
    have hpr : Ideal.Quotient.mk (maximalIdeal R ^ N) (φP p) =
        Ideal.Quotient.mk (maximalIdeal R ^ N) (φP (ιB b)) := by
      apply eRtrunc.injective
      rw [htrunc, heApprox (ιB b) b (by simp)]
    have hpmod : p - ιB b ∈ maximalIdeal P := by
      rw [← IsLocalRing.maximalIdeal_comap φP]
      change φP (p - ιB b) ∈ maximalIdeal R
      rw [map_sub]
      exact (Ideal.pow_le_self (by omega : N ≠ 0))
        ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).1 hpr)
    have hQzero : DirectSum.of _ 0 (mk IQ 0
          (⟨Ideal.Quotient.mk JP p, by simp⟩ : power (M := P ⧸ JP) IQ 0)) =
        DirectSum.of _ 0 (mk IQ 0
          (⟨qAQ (inc a₀), by simp⟩ : power (M := P ⧸ JP) IQ 0)) := by
      rw [← hb, hqAQ]
      apply degreeZero_eq_of_sub_mem
      rw [← map_sub]
      exact Ideal.mem_map_of_mem _ hpmod
    apply grFin.injective
    apply grAQ.injective
    change grAQ (grFin (grFin.symm (grAQ.symm (eGrQuot (grR.symm
      (DirectSum.of _ 0 (mk (maximalIdeal R) 0 ⟨φP p, by simp⟩))))))) = _
    rw [grFin.apply_symm_apply, grAQ.apply_symm_apply]
    have hRzero : grR (DirectSum.of _ 0
          (ringPieceRep (maximalIdeal P) KP 0 ⟨p, by simp⟩)) =
        DirectSum.of _ 0 (mk (maximalIdeal R) 0 ⟨φP p, by simp⟩) := by
      change grR (DirectSum.of _ 0 (mk IP 0 ⟨Ideal.Quotient.mk KP p, _⟩)) = _
      rw [gradedRingEquiv_zero]
      change DirectSum.of _ 0 (mk (maximalIdeal R) 0
        (⟨ePR (Ideal.Quotient.mk KP p), _⟩ : power (M := R) (maximalIdeal R) 0)) = _
      exact congrArg (fun a : R => DirectSum.of _ 0
        (mk (maximalIdeal R) 0 (⟨a, by simp⟩ : power (M := R) (maximalIdeal R) 0)))
        (hePR p)
    rw [← hRzero, grR.symm_apply_apply, ringGradedEquivOfDenomEq_rep]
    change DirectSum.of _ 0 (mk IQ 0 ⟨Ideal.Quotient.mk JP p, _⟩) =
      grAQ (grFin (DirectSum.of _ 0 (mk mAfin 0 ⟨a₀, _⟩)))
    rw [gradedRingEquiv_zero, gradedRingEquiv_zero]
    exact hQzero

end Deformation.Artin.Approximation
