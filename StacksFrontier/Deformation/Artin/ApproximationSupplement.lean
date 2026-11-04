module

public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingOverTerminal
public import StacksFrontier.Deformation.Artin.Approximation
import all StacksFrontier.Deformation.Artin.Approximation

/-!
# Stacks 07XB at general universes

The declarations of this module restate, under weaker hypotheses or at more general universes,
declarations of `StacksFrontier.Deformation.Artin.Approximation`, whose statements are kept as they
are. Each carries the name of the declaration it generalizes with the suffix `_univ`. The proofs
use the private steps of that module, reached by `import all`.

## Main results

* `Deformation.Artin.Approximation.exists_finiteType_approximation_univ`: **Stacks 07XB** for a
  category fibred in groupoids over the big fppf site whose fibres live in an arbitrary universe,
  limit preserving over the terminal object.

## References

* [Stacks Project, Tag 07XB](https://stacks.math.columbia.edu/tag/07XB)
-/


universe u v w

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing AssociatedGraded

namespace Deformation.Artin.Approximation


/-- The conclusion of Stacks 07XB, assembled from the approximation data.

Stating the assembly over abstract data is what keeps it affordable: unifying the nested
existential of the conclusion directly against the `let`-bound definitions of the
construction forces all of them to be unfolded. -/
private theorem exists_approximation_of_data_univ
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : CatFiberedInGroupoids.{u, max u v, u + 1, max (u + 1) v w} (Site B S hS))
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

/-- Precomposing two ring maps whose composite is a third one gives equal morphisms over `u`. -/
private theorem specMap_comp_comp_eq_of_comp_eq {S : Scheme.{u}} {X Y Z : Type u}
    [CommRing X] [CommRing Y] [CommRing Z] (f : Y →+* Z) (g : X →+* Y) (h : X →+* Z)
    (hfg : f.comp g = h) (u : Spec (.of X) ⟶ S) :
    Spec.map (CommRingCat.ofHom f) ≫ Spec.map (CommRingCat.ofHom g) ≫ u =
      Spec.map (CommRingCat.ofHom h) ≫ u := by
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hfg]

/-- **Stacks 07XB, descent step.** Limit preservation on objects lets an object over
`Spec R` descend to a finitely presented stage.

`R` is the filtered colimit of its finitely presented `Λ`-subalgebras, so `Spec R` is the
inverse limit of the corresponding affine schemes over `S`. Limit preservation therefore
produces a finitely presented `Λ`-algebra `C`, an object `x'` over `Spec C`, and a
cartesian comparison `δ` over the structure map `Spec R → Spec C`, matched with `x` up to
the vertical isomorphism `β`.

Isolating this step is what keeps the main theorem affordable: the direct system, the cone
and the colimit computation are elaborated once here instead of inside the main proof. -/
private theorem exists_descent_of_limitPreserving_univ
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : CatFiberedInGroupoids.{u, max u v, u + 1, max (u + 1) v w} (Site B S hS))
    (hp : AlgebraicGeometry.Stack.IsLimitPreservingOverTerminal.{u, u, u} B S hS 𝒳)
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
  have htoR (j : J) :
      Spec.map (CommRingCat.ofHom (toR j).toRingHom) ≫ fG j = fR := by
    exact (specMap_comp_comp_eq_of_comp_eq _ _ _ (toR j).comp_algebraMap uΛ).trans hfΛR
  have htransition (i j : J) (hij : i ≤ j) :
      Spec.map (CommRingCat.ofHom (transition i j hij).toRingHom) ≫ fG i =
        fG j := by
    exact specMap_comp_comp_eq_of_comp_eq _ _ _ (transition i j hij).comp_algebraMap uΛ
  let stage (j : J) : AlgebraicGeometry.BigAffineFppf B S hS :=
    ⟨siteObject B S hS (hGsite j) (fG j), by
      show IsAffine (Spec (.of (G j)))
      infer_instance⟩
  let stageMap {i j : Jᵒᵖ} (a : i ⟶ j) : stage i.unop ⟶ stage j.unop :=
    ObjectProperty.homMk (X := stage i.unop) (Y := stage j.unop)
      (siteObjectHom B S hS (hGsite i.unop) (hGsite j.unop)
        (fG i.unop) (fG j.unop)
        (Spec.map (CommRingCat.ofHom
          (transition j.unop i.unop (leOfHom a.unop)).toRingHom))
        (htransition j.unop i.unop (leOfHom a.unop)))
  have hstageMap_id (i : Jᵒᵖ) : stageMap (𝟙 i) = 𝟙 (stage i.unop) := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    show Spec.map (CommRingCat.ofHom
        (transition i.unop i.unop le_rfl).toRingHom) = 𝟙 _
    have htr : (transition i.unop i.unop le_rfl).toRingHom = RingHom.id _ := by
      ext z
      exact DirectedSystem.map_self' transition z
    rw [htr]
    simp
  have hstageMap_comp {i j k : Jᵒᵖ} (a : i ⟶ j) (b : j ⟶ k) :
      stageMap (a ≫ b) = stageMap a ≫ stageMap b := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    show Spec.map (CommRingCat.ofHom
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
      show IsAffine (Spec (.of R))
      infer_instance⟩
  let limitMap (j : Jᵒᵖ) : limitStage ⟶ D.obj j :=
    ObjectProperty.homMk (X := limitStage) (Y := D.obj j)
      (siteObjectHom B S hS hR (hGsite j.unop) fR (fG j.unop)
        (Spec.map (CommRingCat.ofHom (toR j.unop).toRingHom))
        (htoR j.unop))
  have hlimitMap (i j : Jᵒᵖ) (a : i ⟶ j) :
      limitMap i ≫ D.map a = limitMap j := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    show Spec.map (CommRingCat.ofHom (toR i.unop).toRingHom) ≫
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
        colimitG.1 (by change toR i a = toR i b; exact hab)
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
  let γ : 𝒳.val.p.obj x.1 ⟶ y₀.1 :=
    eqToHom hxBase ≫
      (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map (c.π.app i₀)
  have hγ : (baseFiberedCategory B S hS).val.p.IsStronglyCartesian
      ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map (c.π.app i₀)) γ := by
    have : (baseFiberedCategory B S hS).val.p.IsHomLift
        ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map (c.π.app i₀)) γ := by
      apply IsHomLift.of_fac (baseFiberedCategory B S hS).val.p _ γ
        hxBase rfl
      show (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map (c.π.app i₀) =
        (eqToIso hxBase).inv ≫ (eqToIso hxBase).hom ≫
          (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map (c.π.app i₀)
      simp
    exact (baseFiberedCategory B S hS).isFiberedInGroupoids.isStronglyCartesian_homLift
      _ _
  obtain ⟨i', _, x', xU, δ, β, _, hδ, hβ, hβiso, _, _⟩ :=
    hp Jᵒᵖ D c hcScheme i₀ y₀ x γ hγ
  exact ⟨G i'.unop, ringG i'.unop, algebraG i'.unop, finitePresentationG i'.unop,
    toR i'.unop, hGsite i'.unop, htoR i'.unop, x', xU, δ, β, hδ, hβ, hβiso⟩

/-- **Stacks Project, Tag 07XB.** Approximation of a fibred object over a Noetherian
complete local ring by an object over a finite type `S`-algebra.

Let `S` be a locally Noetherian scheme, let `𝒳` be a category fibred in groupoids over the
big fppf site of `S`, and let `x` be an object of `𝒳` over `Spec R` for `R` a Noetherian
complete local ring whose residue field is of finite type over `S`. Let `s ∈ S` be the image
of `Spec k`. If `O_{S, s}` is a G-ring and the structure morphism of `𝒳` is limit preserving
on objects, then for every `N ≥ 1` there are a finite type `S`-algebra `A`, a maximal ideal
`m_A ⊆ A`, an object `x_A` of `𝒳` over `Spec A`, an `S`-isomorphism `R/m_R^N ≅ A/m_A^N`, an
isomorphism of the restrictions of `x` and `x_A` to those truncations compatible with it,
and an isomorphism of graded `k`-algebras `Gr_{m_R}(R) ≅ Gr_{m_A}(A)`.

These are clauses (1)-(6) of the tag. Clause (6) is the final existential: a ring
isomorphism of the associated graded rings which carries each homogeneous summand to the
summand of the same degree and which, in degree zero, agrees with the truncation
isomorphism `φ` of clause (4).

Artin approximation over a G-ring (Stacks 07QZ) is used in the proof and is discharged by
`Stacks.Smoothing.exists_localEtaleSolution_of_isGRing`, so the statement below carries no
hypothesis beyond the source's own. -/
public theorem exists_finiteType_approximation_univ
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [IsLocallyNoetherian S]
    (𝒳 : CatFiberedInGroupoids.{u, max u v, u + 1, max (u + 1) v w} (Site B S hS))
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R]
    (hR : B.Contains (Spec (.of R)))
    (fR : Spec (.of R) ⟶ S)
    (hfinite : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R))) ≫ fR))
    (hquasi : QuasiCompact
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R))) ≫ fR))
    (s : S)
    (hs : fR (closedPoint R) = s)
    (hG : IsGRing (S.presheaf.stalk s))
    (hp : AlgebraicGeometry.Stack.IsLimitPreservingOverTerminal.{u, u, u} B S hS 𝒳)
    (x : 𝒳.val.p.Fiber (siteObject B S hS hR fR))
    (N : ℕ) (hN : 1 ≤ N) :
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
                    (⟨a₀, by simp⟩ : AssociatedGraded.power (M := A) mA 0)) := by
  classical
  let : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field (maximalIdeal R)
  have : IsLocalHom (Ideal.Quotient.mk (maximalIdeal R)) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  let fK : Spec (.of (R ⧸ maximalIdeal R)) ⟶ S :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R))) ≫ fR
  let κpt : Spec (.of (R ⧸ maximalIdeal R)) := closedPoint (R ⧸ maximalIdeal R)
  have hpoint : fK κpt = s := by
    show fR (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R)))
      κpt) = s
    rw [Spec.map_apply, IsLocalRing.comap_closedPoint]
    exact hs
  obtain ⟨U, hU, hfinK⟩ :=
    exists_finite_affine_chart_of_field fK hfinite hquasi
  have hsU : s ∈ U.1 := by
    have h := hU (show κpt ∈ ⊤ by simp)
    change fK κpt ∈ U.1 at h
    rwa [hpoint] at h
  obtain ⟨fU, hfU⟩ := factorsThrough_affineOpen_of_closedPoint fR U s hs hsU
  have hUR : (⊤ : (Spec (.of R)).Opens) ≤ fR ⁻¹ᵁ U.1 := by
    intro z _
    show fR z ∈ U.1
    rw [← hfU]
    exact (fU z).property
  let Λ := Γ(S, U.1)
  let : IsNoetherianRing Λ := IsLocallyNoetherian.component_noetherian U
  let φΛk : Λ →+* (R ⧸ maximalIdeal R) :=
    (fK.appLE U ⊤ hU ≫ (Scheme.ΓSpecIso (.of (R ⧸ maximalIdeal R))).hom).hom
  let : Algebra Λ (R ⧸ maximalIdeal R) := φΛk.toAlgebra
  have : Module.Finite Λ (R ⧸ maximalIdeal R) := hfinK
  obtain ⟨s₀, f₀, hf₀⟩ :=
    Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
      (inferInstance : Algebra.FiniteType Λ (R ⧸ maximalIdeal R))
  let a₀ (i : Fin s₀) : R :=
    Classical.choose (Ideal.Quotient.mk_surjective (f₀ (MvPolynomial.X i)))
  have ha₀ (i : Fin s₀) :
      Ideal.Quotient.mk (maximalIdeal R) (a₀ i) = f₀ (MvPolynomial.X i) :=
    Classical.choose_spec (Ideal.Quotient.mk_surjective (f₀ (MvPolynomial.X i)))
  obtain ⟨s₁, b, hb⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp
      (maximalIdeal R).fg_of_isNoetherianRing
  let φΛR : Λ →+* R :=
    (fR.appLE U ⊤ hUR ≫ (Scheme.ΓSpecIso (.of R)).hom).hom
  let : Algebra Λ R := φΛR.toAlgebra
  let s₂ := s₀ + s₁
  let a₂ : Fin s₂ → R := Fin.append a₀ b
  let f₂ : MvPolynomial (Fin s₂) Λ →ₐ[Λ] R := MvPolynomial.aeval a₂
  have hΓSpec {X : Type u} [CommRing X] (g : Spec (.of X) ⟶ S)
      (hg : (⊤ : (Spec (.of X)).Opens) ≤ g ⁻¹ᵁ U.1) :
      Spec.map (CommRingCat.ofHom (g.appLE U ⊤ hg ≫ (Scheme.ΓSpecIso (.of X)).hom).hom) ≫
        U.2.fromSpec = g := by
    rw [show CommRingCat.ofHom (g.appLE U ⊤ hg ≫ (Scheme.ΓSpecIso (.of X)).hom).hom =
        g.appLE U ⊤ hg ≫ (Scheme.ΓSpecIso (.of X)).hom by rfl,
      Spec.map_comp, Category.assoc,
      U.2.SpecMap_appLE_fromSpec g (isAffineOpen_top _) hg,
      IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec]
    simp
  have hφΛR : Spec.map (CommRingCat.ofHom φΛR) ≫ U.2.fromSpec = fR := hΓSpec fR hUR
  have hφΛk : Spec.map (CommRingCat.ofHom φΛk) ≫ U.2.fromSpec = fK := hΓSpec fK hU
  have hφΛquot : (Ideal.Quotient.mk (maximalIdeal R)).comp φΛR = φΛk := by
    have heq : CommRingCat.ofHom ((Ideal.Quotient.mk (maximalIdeal R)).comp φΛR) =
        CommRingCat.ofHom φΛk := by
      apply Spec.map_inj.mp
      let : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
      apply (cancel_mono U.2.fromSpec).mp
      calc
        Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk (maximalIdeal R)).comp φΛR)) ≫
            U.2.fromSpec = fK := by
          rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hφΛR]
        _ = Spec.map (CommRingCat.ofHom φΛk) ≫ U.2.fromSpec := hφΛk.symm
    exact congrArg CommRingCat.Hom.hom heq
  let qAlg : R →ₐ[Λ] (R ⧸ maximalIdeal R) := {
    toRingHom := Ideal.Quotient.mk (maximalIdeal R)
    commutes' := fun z ↦ congrArg (fun h : Λ →+* (R ⧸ maximalIdeal R) ↦ h z)
      hφΛquot }
  let embed₀ : MvPolynomial (Fin s₀) Λ →ₐ[Λ]
      MvPolynomial (Fin s₂) Λ := MvPolynomial.rename (Fin.castAdd s₁)
  have hres : qAlg.comp (f₂.comp embed₀) = f₀ := by
    ext i
    simp only [AlgHom.comp_apply, MvPolynomial.rename_X, MvPolynomial.aeval_X,
      embed₀, f₂, a₂, Fin.append_left]
    exact ha₀ i
  have hresSurj : Function.Surjective (qAlg.comp f₂) := by
    intro z
    obtain ⟨p, hp⟩ := hf₀ z
    refine ⟨embed₀ p, ?_⟩
    simpa only [← hres, AlgHom.comp_apply] using hp
  let p₂ := Ideal.comap f₂.toRingHom (maximalIdeal R)
  have hp₂ : p₂.IsMaximal := by
    have hpeq : p₂ = Ideal.comap (qAlg.comp f₂).toRingHom
        (⊥ : Ideal (R ⧸ maximalIdeal R)) := by
      ext z
      show f₂ z ∈ maximalIdeal R ↔
        Ideal.Quotient.mk (maximalIdeal R) (f₂ z) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.symm
    rw [hpeq]
    exact Ideal.comap_isMaximal_of_surjective _ hresSurj
  have hliftResidue (r₀ : R) :
      ∃ p : MvPolynomial (Fin s₂) Λ, r₀ - f₂ p ∈ maximalIdeal R := by
    obtain ⟨p, hp⟩ := hresSurj (qAlg r₀)
    refine ⟨p, Ideal.Quotient.eq_zero_iff_mem.mp ?_⟩
    show (Ideal.Quotient.mk (maximalIdeal R)) (r₀ - f₂ p) = 0
    rw [map_sub, sub_eq_zero]
    exact hp.symm
  have hspanB : Ideal.span (Set.range b) = maximalIdeal R := hb
  have hbmem (i : Fin s₁) : b i ∈ maximalIdeal R := by
    rw [← hspanB]
    exact Ideal.subset_span ⟨i, rfl⟩
  have hmod₂ : Function.Surjective
      ((Ideal.Quotient.mk ((maximalIdeal R) ^ 2)).comp f₂.toRingHom) := by
    intro z
    obtain ⟨r₀, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨p₀, hp₀⟩ := hliftResidue r₀
    have hmem : r₀ - f₂ p₀ ∈ Ideal.span (Set.range b) := by
      rwa [hspanB]
    obtain ⟨coeff, hcoeff⟩ :=
      Ideal.mem_span_range_iff_exists_fun.mp hmem
    have hr : r₀ = f₂ p₀ + ∑ i, coeff i * b i := by
      linear_combination -hcoeff
    let polys (i : Fin s₁) : MvPolynomial (Fin s₂) Λ :=
      Classical.choose (hliftResidue (coeff i))
    have hpolys (i : Fin s₁) : coeff i - f₂ (polys i) ∈ maximalIdeal R :=
      Classical.choose_spec (hliftResidue (coeff i))
    refine ⟨p₀ + ∑ i, polys i * MvPolynomial.X (Fin.natAdd s₀ i), ?_⟩
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2
    have hcomb :
        f₂ (p₀ + ∑ i, polys i * MvPolynomial.X (Fin.natAdd s₀ i)) - r₀ =
          ∑ i, (f₂ (polys i) - coeff i) * b i := by
      simp only [map_add, map_sum, map_mul, MvPolynomial.aeval_X,
        f₂, a₂, Fin.append_right]
      rw [hr]
      simp [f₂, a₂, sub_mul, Finset.sum_sub_distrib]
    show f₂ (p₀ + ∑ i, polys i * MvPolynomial.X (Fin.natAdd s₀ i)) - r₀ ∈
      maximalIdeal R ^ 2
    rw [hcomb]
    apply Ideal.sum_mem
    intro i hi
    have hm : f₂ (polys i) - coeff i ∈ maximalIdeal R := by
      simpa only [neg_sub] using (maximalIdeal R).neg_mem (hpolys i)
    simpa only [pow_two] using Ideal.mul_mem_mul hm (hbmem i)
  let : p₂.IsMaximal := hp₂
  obtain ⟨hPnoeth, hPlocal, hPcomplete, gP, hgP, hglocal, φP, hφP,
    hφPsurj, hφPlocal, hφPunique⟩ :=
    AdicCompletion.exists_surjective_adicCompletionMap Λ R s₂ p₂ f₂ rfl hmod₂
  have hUsite : B.Contains U.1 :=
    Scheme.size_lt_of_isOpenImmersion U.1.ι hS
  have hΛsite : B.Contains (Spec (.of Λ)) := by
    show (Spec Γ(S, U.1)).size < B.cutoff
    rw [← Scheme.size_congr U.2.isoSpec]
    exact hUsite
  have hRN : B.Contains (Spec (.of (R ⧸ maximalIdeal R ^ N))) :=
    contains_spec_quotient B hR (maximalIdeal R ^ N)
  let iR : siteObject B S hS hRN
      (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk ((maximalIdeal R) ^ N))) ≫ fR) ⟶
      siteObject B S hS hR fR :=
    siteObjectHom B S hS hRN hR _ _ _ rfl
  let : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  let xRN := 𝒳.val.p.pullbackFiber x iR
  let r : xRN.1 ⟶ x.1 := Functor.IsPreFibered.pullbackMap x.2 iR
  have hr : 𝒳.val.p.IsStronglyCartesian iR r :=
    𝒳.isFiberedInGroupoids.isStronglyCartesian_homLift iR r
  obtain ⟨C, ringC, algC, fpC, toRC, hCsite, hfC, x', xU, δ, β, hδ, hβ, hβiso⟩ :=
    exists_descent_of_limitPreserving_univ B S hS 𝒳 hp Λ U.2.fromSpec hΛsite R hR fR hφΛR x
  let : CommRing C := ringC
  let : Algebra Λ C := algC
  let : Algebra.FinitePresentation Λ C := fpC
  let fC : Spec (.of C) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap Λ C)) ≫ U.2.fromSpec
  let lC := siteObjectHom B S hS hR hCsite fR fC
    (Spec.map (CommRingCat.ofHom toRC.toRingHom)) hfC
  obtain ⟨sC, qC, hqCsurj, hqCker⟩ :=
    Algebra.FinitePresentation.out (R := Λ) (A := C)
  obtain ⟨rC, bC, hbC⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp hqCker
  let aC : Fin sC → R := fun i ↦ toRC (qC (MvPolynomial.X i))
  have hqCcomp : toRC.comp qC = MvPolynomial.aeval aC := by
    ext i
    simp [aC]
  have hbCzero (i : Fin rC) :
      MvPolynomial.aeval aC (bC i) = 0 := by
    rw [← hqCcomp, AlgHom.comp_apply]
    have hmem : bC i ∈ RingHom.ker qC.toRingHom := by
      rw [← hbC]
      exact Ideal.subset_span ⟨i, rfl⟩
    have hzero : qC (bC i) = 0 := RingHom.mem_ker.mp hmem
    rw [hzero, map_zero]
  let T := Localization.AtPrime p₂
  let P := AdicCompletion (maximalIdeal T) T
  let : IsNoetherianRing P := hPnoeth
  let : IsLocalRing P := hPlocal
  let : IsAdicComplete (maximalIdeal P) P := hPcomplete
  let aP : Fin sC → P := fun i ↦ Classical.choose (hφPsurj (aC i))
  have haP (i : Fin sC) : φP (aP i) = aC i :=
    Classical.choose_spec (hφPsurj (aC i))
  obtain ⟨rP, bP, hbP⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp
      (RingHom.ker φP).fg_of_isNoetherianRing
  let φΛP : Λ →+* P :=
    (algebraMap T P).comp
      ((algebraMap (MvPolynomial (Fin s₂) Λ) T).comp MvPolynomial.C)
  have hφΛP : φP.comp φΛP = φΛR := by
    ext z
    have h₁ := congrArg (fun f : T →+* R ↦
      f (algebraMap (MvPolynomial (Fin s₂) Λ) T (MvPolynomial.C z))) hφP
    have h₂ := congrArg (fun f : MvPolynomial (Fin s₂) Λ →+* R ↦
      f (MvPolynomial.C z)) hgP
    calc
      φP (φΛP z) = gP (algebraMap (MvPolynomial (Fin s₂) Λ) T
          (MvPolynomial.C z)) := h₁
      _ = f₂ (MvPolynomial.C z) := h₂
      _ = φΛR z := f₂.commutes z
  let : Algebra Λ P := φΛP.toAlgebra
  let φPAlg : P →ₐ[Λ] R :=
    { toRingHom := φP
      commutes' := fun z ↦ congrArg (fun f : Λ →+* R ↦ f z) hφΛP }
  have hEvalP : φPAlg.comp (MvPolynomial.aeval aP) =
      MvPolynomial.aeval aC := by
    ext i
    simpa [φPAlg] using haP i
  have hrelPmem (i : Fin rC) :
      MvPolynomial.aeval aP (bC i) ∈ RingHom.ker φP := by
    rw [RingHom.mem_ker]
    show φPAlg (MvPolynomial.aeval aP (bC i)) = 0
    rw [← AlgHom.comp_apply, hEvalP]
    exact hbCzero i
  have hrelPspan (i : Fin rC) :
      MvPolynomial.aeval aP (bC i) ∈ Ideal.span (Set.range bP) := by
    show MvPolynomial.aeval aP (bC i) ∈
      Submodule.span P (Set.range bP)
    rw [hbP]
    exact hrelPmem i
  let cP (i : Fin rC) : Fin rP → P :=
    Classical.choose (Ideal.mem_span_range_iff_exists_fun.mp (hrelPspan i))
  have hcP (i : Fin rC) :
      MvPolynomial.aeval aP (bC i) = ∑ j, cP i j * bP j :=
    (Classical.choose_spec
      (Ideal.mem_span_range_iff_exists_fun.mp (hrelPspan i))).symm
  let gPlinear : (Fin rP → P) →ₗ[P] P := Fintype.linearCombination P bP
  have hrangegP : LinearMap.range gPlinear = RingHom.ker φP := by
    rw [Fintype.range_linearCombination]
    exact hbP
  obtain ⟨tP, kP, hkP⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp
      (IsNoetherian.noetherian (LinearMap.ker gPlinear))
  let fPlinear : (Fin tP → P) →ₗ[P] (Fin rP → P) :=
    Fintype.linearCombination P kP
  have hExactP : LinearMap.ker gPlinear = LinearMap.range fPlinear := by
    rw [Fintype.range_linearCombination]
    exact hkP.symm
  have hComplexP : gPlinear.comp fPlinear = 0 :=
    LinearMap.range_le_ker_iff.mp (le_of_eq hExactP.symm)
  have hsyzygyP (i : Fin tP) : ∑ j, kP i j * bP j = 0 := by
    have hmem : kP i ∈ LinearMap.ker gPlinear := by
      rw [← hkP]
      exact Submodule.subset_span ⟨i, rfl⟩
    simpa only [LinearMap.mem_ker, gPlinear, Fintype.linearCombination_apply,
      smul_eq_mul]
      using hmem
  obtain ⟨cAR, hcAR⟩ := exists_artinRees_denominator_eq bP kP hExactP
  let V := Sum (Fin sC)
    (Sum (Fin rP) (Sum (Fin rC × Fin rP) (Fin tP × Fin rP)))
  let E := Sum (Fin rC) (Fin tP)
  let aVec : V → P
    | .inl i => aP i
    | .inr (.inl j) => bP j
    | .inr (.inr (.inl ij)) => cP ij.1 ij.2
    | .inr (.inr (.inr ij)) => kP ij.1 ij.2
  let φΛT : Λ →+* T :=
    (algebraMap (MvPolynomial (Fin s₂) Λ) T).comp MvPolynomial.C
  let rel : E → MvPolynomial V T
    | .inl i =>
        MvPolynomial.rename Sum.inl (MvPolynomial.map φΛT (bC i)) -
          ∑ j : Fin rP,
            MvPolynomial.X (Sum.inr (Sum.inr (Sum.inl (i, j)))) *
              MvPolynomial.X (Sum.inr (Sum.inl j))
    | .inr i =>
        ∑ j : Fin rP,
          MvPolynomial.X (Sum.inr (Sum.inr (Sum.inr (i, j)))) *
            MvPolynomial.X (Sum.inr (Sum.inl j))
  have hrelZero (i : E) :
      MvPolynomial.eval₂ (algebraMap T P) aVec (rel i) = 0 := by
    cases i with
    | inl i =>
      simp only [rel, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_sum,
        MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X,
        MvPolynomial.eval₂_rename, MvPolynomial.eval₂_map]
      show MvPolynomial.aeval aP (bC i) - ∑ j, cP i j * bP j = 0
      rw [hcP i, sub_self]
    | inr i =>
      simp only [rel, MvPolynomial.eval₂_sum,
        MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
      show (∑ j, kP i j * bP j) = 0
      exact hsyzygyP i
  let qΛ : Ideal Λ := (U.2.primeIdealOf ⟨s, hsU⟩).asIdeal
  have hqΛ : qΛ = Ideal.comap φΛR (maximalIdeal R) := by
    have hpointΛ :
        Spec.map (CommRingCat.ofHom φΛR) (closedPoint R) =
          U.2.primeIdealOf ⟨s, hsU⟩ := by
      let : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
      apply U.2.fromSpec.isOpenEmbedding.injective
      show (Spec.map (CommRingCat.ofHom φΛR) ≫ U.2.fromSpec)
          (closedPoint R) = U.2.fromSpec (U.2.primeIdealOf ⟨s, hsU⟩)
      rw [hφΛR, U.2.fromSpec_primeIdealOf, hs]
    exact congrArg PrimeSpectrum.asIdeal hpointΛ.symm
  have hgf : gP.comp φΛT = φΛR := by
    ext z
    exact (RingHom.congr_fun hgP (MvPolynomial.C z)).trans (f₂.commutes z)
  let : IsLocalHom gP := hglocal
  have hqΛT : Ideal.comap φΛT (maximalIdeal T) = qΛ := by
    rw [hqΛ]
    ext z
    simp only [Ideal.mem_comap]
    rw [← IsLocalRing.maximalIdeal_comap gP]
    show gP (φΛT z) ∈ maximalIdeal R ↔ φΛR z ∈ maximalIdeal R
    rw [← RingHom.comp_apply, hgf]
  let : Algebra Λ T := φΛT.toAlgebra
  let : qΛ.IsPrime := inferInstance
  let : Algebra Λ (S.presheaf.stalk s) :=
    S.presheaf.algebra_section_stalk ⟨s, hsU⟩
  let : IsLocalization.AtPrime (S.presheaf.stalk s) qΛ :=
    U.2.isLocalization_stalk ⟨s, hsU⟩
  have hunitΛT : ∀ z : qΛ.primeCompl, IsUnit (φΛT z) := by
    intro z
    apply IsLocalRing.notMem_maximalIdeal.mp
    intro hz
    have hzcomap : (z : Λ) ∈ Ideal.comap φΛT (maximalIdeal T) := hz
    have hz' : (z : Λ) ∈ qΛ :=
      Eq.mp (congrArg (fun I : Ideal Λ ↦ (z : Λ) ∈ I) hqΛT) hzcomap
    exact z.property hz'
  let fST : S.presheaf.stalk s →+* T :=
    IsLocalization.lift (M := qΛ.primeCompl) (g := φΛT) hunitΛT
  have hfST : fST.comp (algebraMap Λ (S.presheaf.stalk s)) = φΛT :=
    IsLocalization.lift_comp hunitΛT
  let : Algebra (S.presheaf.stalk s) T := fST.toAlgebra
  have hEssΛT : Algebra.EssFiniteType Λ T := by
    have hloc : Algebra.EssFiniteType (MvPolynomial (Fin s₂) Λ) T :=
      Algebra.EssFiniteType.of_isLocalization T p₂.primeCompl
    apply RingHom.essFiniteType_algebraMap.mp
    show φΛT.EssFiniteType
    exact (RingHom.FiniteType.essFiniteType
      (RingHom.finiteType_algebraMap.mpr
        (inferInstance : Algebra.FiniteType Λ (MvPolynomial (Fin s₂) Λ)))).comp
        (RingHom.essFiniteType_algebraMap.mpr hloc)
  have : Algebra.EssFiniteType (S.presheaf.stalk s) T :=
    RingHom.essFiniteType_algebraMap.mp
      (RingHom.EssFiniteType.of_comp (algebraMap Λ (S.presheaf.stalk s))
        (hfST ▸ (RingHom.essFiniteType_algebraMap.mpr hEssΛT)))
  have hGT : IsGRing T := isGRing_of_essFiniteType hG
  let N' := max N (cAR + 1)
  have hNN' : N ≤ N' := le_max_left _ _
  have hcN' : cAR + 1 ≤ N' := le_max_right _ _
  obtain ⟨B', ringB', algB', etaleB', mB, hmB, hoverB, hresB,
    ιB, bVec, hιlocal, hBzero, hBclose⟩ :=
    exists_etale_solution_approximating_fintype
      T hGT rel aVec hrelZero N'
  let : CommRing B' := ringB'
  let : Algebra T B' := algB'
  let : Algebra.Etale T B' := etaleB'
  let : mB.IsMaximal := hmB
  have hmBmap : Ideal.map ιB.toRingHom mB ≤ maximalIdeal P := by
    rw [Ideal.map_le_iff_le_comap, hιlocal]
  have hι : mB ≤ Ideal.comap ιB.toRingHom (maximalIdeal P) := by rw [hιlocal]
  have hιTrunc (n : ℕ) : Function.Bijective (Ideal.quotientMap
      (maximalIdeal P ^ n) ιB.toRingHom
      ((Ideal.pow_right_mono hι n).trans (Ideal.le_comap_pow ιB.toRingHom n))) :=
    etale_completion_trunc_bijective mB hoverB hresB ιB hιlocal n
  have hcloseP (v : V) :
      aVec v - ιB (bVec v) ∈ (maximalIdeal P) ^ N' := by
    have hpow : Ideal.map ιB.toRingHom (mB ^ N') ≤
        (maximalIdeal P) ^ N' := by
      rw [Ideal.map_pow]
      exact Ideal.pow_right_mono hmBmap N'
    exact hpow (hBclose v)
  have hclosePN (v : V) :
      aVec v - ιB (bVec v) ∈ (maximalIdeal P) ^ N :=
    Ideal.pow_le_pow_right hNN' (hcloseP v)
  let : IsLocalHom φP := hφPlocal
  have hbPmax (j : Fin rP) : bP j ∈ maximalIdeal P := by
    have hker : bP j ∈ RingHom.ker φP := by
      rw [← hbP]
      exact Submodule.subset_span ⟨j, rfl⟩
    have hφ : φP (bP j) = 0 := RingHom.mem_ker.mp hker
    have hm : φP (bP j) ∈ maximalIdeal R := hφ ▸ zero_mem _
    rw [← IsLocalRing.maximalIdeal_comap φP]
    exact hm
  have hbBmax (j : Fin rP) :
      bVec (Sum.inr (Sum.inl j)) ∈ mB := by
    rw [← hιlocal]
    have hd : bP j - ιB (bVec (Sum.inr (Sum.inl j))) ∈ maximalIdeal P :=
      (Ideal.pow_le_self (by omega : N' ≠ 0)) (hcloseP _)
    have heq : ιB (bVec (Sum.inr (Sum.inl j))) =
        bP j - (bP j - ιB (bVec (Sum.inr (Sum.inl j)))) := by ring
    show ιB (bVec (Sum.inr (Sum.inl j))) ∈ maximalIdeal P
    rw [heq]
    exact (maximalIdeal P).sub_mem (hbPmax j) hd
  let bB : Fin rP → B' := fun j ↦ bVec (Sum.inr (Sum.inl j))
  let JB : Ideal B' := Ideal.span (Set.range bB)
  have hJBle : JB ≤ mB := by
    show Ideal.span (Set.range bB) ≤ mB
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact hbBmax j
  let A₀ := B' ⧸ JB
  let mA₀ : Ideal A₀ := Ideal.map (Ideal.Quotient.mk JB) mB
  have hmA₀ : mA₀.IsMaximal := by
    apply Ideal.IsMaximal.map_of_surjective_of_ker_le
      (Ideal.Quotient.mk_surjective (I := JB))
    simpa only [Ideal.mk_ker] using hJBle
  let aB : Fin sC → B' := fun i ↦ bVec (Sum.inl i)
  let cB : Fin rC → Fin rP → B' := fun i j ↦
    bVec (Sum.inr (Sum.inr (Sum.inl (i, j))))
  let φΛB : Λ →+* B' := (algebraMap T B').comp φΛT
  have hBrel (i : Fin rC) :
      MvPolynomial.eval₂ φΛB aB (bC i) =
        ∑ j, cB i j * bB j := by
    have h := hBzero (Sum.inl i)
    simp only [rel, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_sum,
      MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X,
      MvPolynomial.eval₂_rename, MvPolynomial.eval₂_map] at h
    change MvPolynomial.eval₂ φΛB aB (bC i) -
      ∑ j, cB i j * bB j = 0 at h
    exact sub_eq_zero.mp h
  let φΛA₀ : Λ →+* A₀ := (Ideal.Quotient.mk JB).comp φΛB
  let aA₀ : Fin sC → A₀ := fun i ↦ Ideal.Quotient.mk JB (aB i)
  let qA₀ : MvPolynomial (Fin sC) Λ →+* A₀ :=
    MvPolynomial.eval₂Hom φΛA₀ aA₀
  have hqA₀rel (i : Fin rC) : qA₀ (bC i) = 0 := by
    show MvPolynomial.eval₂
      ((Ideal.Quotient.mk JB).comp φΛB)
      ((Ideal.Quotient.mk JB) ∘ aB) (bC i) = 0
    rw [← MvPolynomial.eval₂_comp_left, hBrel i]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.sum_mem _ fun j _ ↦ JB.mul_mem_left _ (Ideal.subset_span ⟨j, rfl⟩))
  have hkerCA : RingHom.ker qC.toRingHom ≤ RingHom.ker qA₀ := by
    rw [← hbC]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact RingHom.mem_ker.mpr (hqA₀rel i)
  let qCA₀ : C →+* A₀ :=
    (qC.toRingHom.liftOfSurjective hqCsurj) ⟨qA₀, hkerCA⟩
  have hqCA₀ : qCA₀.comp qC.toRingHom = qA₀ :=
    qC.toRingHom.liftOfSurjective_comp hqCsurj ⟨qA₀, hkerCA⟩
  have hΛCA₀ : qCA₀.comp (algebraMap Λ C) = φΛA₀ := by
    ext z
    calc
      qCA₀ (algebraMap Λ C z) = qCA₀ (qC (MvPolynomial.C z)) := by
        rw [← qC.commutes z, MvPolynomial.algebraMap_eq]
      _ = qA₀ (MvPolynomial.C z) :=
        congrArg (fun f : MvPolynomial (Fin sC) Λ →+* A₀ ↦
          f (MvPolynomial.C z)) hqCA₀
      _ = φΛA₀ z := by simp [qA₀]
  let kB : Fin tP → Fin rP → B' := fun i j ↦
    bVec (Sum.inr (Sum.inr (Sum.inr (i, j))))
  have hBsyzygy (i : Fin tP) : ∑ j, kB i j * bB j = 0 := by
    have h := hBzero (Sum.inr i)
    simpa only [rel, MvPolynomial.eval₂_sum,
      MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X] using h
  let bP' : Fin rP → P := fun j ↦ ιB (bB j)
  have hbPclose (j : Fin rP) : bP j - bP' j ∈ (maximalIdeal P) ^ N' :=
    hcloseP (Sum.inr (Sum.inl j))
  have hbPcongN (j : Fin rP) : bP j - bP' j ∈ (maximalIdeal P) ^ N :=
    Ideal.pow_le_pow_right hNN' (hbPclose j)
  let kP' : Fin tP → Fin rP → P := fun i j ↦ ιB (kB i j)
  have hkPclose (i : Fin tP) (j : Fin rP) :
      kP i j - kP' i j ∈ (maximalIdeal P) ^ N' :=
    hcloseP (Sum.inr (Sum.inr (Sum.inr (i, j))))
  have hsyzygyB (i : Fin tP) : ∑ j, kP' i j * bP' j = 0 := by
    have h : ∑ j, kP' i j * bP' j = ιB (∑ j, kB i j * bB j) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ ↦ (map_mul ιB (kB i j) (bB j)).symm
    rw [h, hBsyzygy i, map_zero]
  obtain ⟨eRtruncA₀, heApprox⟩ :=
    exists_truncation_equiv_of_approximating_generators φP hφPsurj ιB.toRingHom mB hι
      hιTrunc bP bB hbP N hbPcongN
  have heRtruncA₀_Λ (z : Λ) :
      eRtruncA₀ (Ideal.Quotient.mk ((maximalIdeal R) ^ N) (φΛR z)) =
        Ideal.Quotient.mk (mA₀ ^ N) (φΛA₀ z) := by
    have hp : φP (φΛP z) = φΛR z := RingHom.congr_fun hφΛP z
    have hg : ιB (φΛB z) = φΛP z := ιB.commutes (φΛT z)
    show eRtruncA₀ (Ideal.Quotient.mk _ (φΛR z)) =
      Ideal.Quotient.mk _ (Ideal.Quotient.mk JB (φΛB z))
    rw [← hp]
    apply heApprox
    show φΛP z - ιB (φΛB z) ∈ maximalIdeal P ^ N
    rw [hg, sub_self]
    exact zero_mem _
  have htruncRing₀ :
      eRtruncA₀.symm.toRingHom.comp
          ((Ideal.Quotient.mk (mA₀ ^ N)).comp φΛA₀) =
        (Ideal.Quotient.mk ((maximalIdeal R) ^ N)).comp φΛR := by
    ext z
    show eRtruncA₀.symm (Ideal.Quotient.mk (mA₀ ^ N) (φΛA₀ z)) =
      Ideal.Quotient.mk ((maximalIdeal R) ^ N) (φΛR z)
    exact eRtruncA₀.symm_apply_eq.mpr (heRtruncA₀_Λ z).symm
  have heRtruncA₀_aC (i : Fin sC) :
      eRtruncA₀ (Ideal.Quotient.mk ((maximalIdeal R) ^ N) (aC i)) =
        Ideal.Quotient.mk (mA₀ ^ N) (aA₀ i) := by
    rw [← haP i]
    exact heApprox (aP i) (aB i) (hclosePN (Sum.inl i))
  have htruncC :
      eRtruncA₀.toRingHom.comp
          ((Ideal.Quotient.mk ((maximalIdeal R) ^ N)).comp
            toRC.toRingHom) =
        (Ideal.Quotient.mk (mA₀ ^ N)).comp qCA₀ := by
    let f : C →+* (A₀ ⧸ mA₀ ^ N) :=
      eRtruncA₀.toRingHom.comp
        ((Ideal.Quotient.mk ((maximalIdeal R) ^ N)).comp
          toRC.toRingHom)
    let g : C →+* (A₀ ⧸ mA₀ ^ N) :=
      (Ideal.Quotient.mk (mA₀ ^ N)).comp qCA₀
    have hpoly : f.comp qC.toRingHom = g.comp qC.toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro z
        show eRtruncA₀ (Ideal.Quotient.mk _
            (toRC (qC (MvPolynomial.C z)))) =
          Ideal.Quotient.mk _ (qCA₀ (qC (MvPolynomial.C z)))
        rw [← MvPolynomial.algebraMap_eq, qC.commutes, toRC.commutes]
        have h := RingHom.congr_fun hΛCA₀ z
        change qCA₀ (algebraMap Λ C z) = φΛA₀ z at h
        rw [h]
        exact heRtruncA₀_Λ z
      · intro i
        show eRtruncA₀ (Ideal.Quotient.mk _ (aC i)) =
          Ideal.Quotient.mk _ (qCA₀ (qC (MvPolynomial.X i)))
        rw [show qCA₀ (qC (MvPolynomial.X i)) = qA₀ (MvPolynomial.X i) from
          RingHom.congr_fun hqCA₀ (MvPolynomial.X i)]
        simpa only [qA₀, MvPolynomial.eval₂Hom_X'] using heRtruncA₀_aC i
    show f = g
    apply RingHom.ext
    intro c
    obtain ⟨p, rfl⟩ := hqCsurj c
    exact RingHom.congr_fun hpoly p
  have htruncC' :
      eRtruncA₀.symm.toRingHom.comp
          ((Ideal.Quotient.mk (mA₀ ^ N)).comp qCA₀) =
        (Ideal.Quotient.mk ((maximalIdeal R) ^ N)).comp
          toRC.toRingHom := by
    ext c₀
    have h := RingHom.congr_fun htruncC c₀
    change eRtruncA₀ (Ideal.Quotient.mk _ (toRC c₀)) =
      Ideal.Quotient.mk _ (qCA₀ c₀) at h
    show eRtruncA₀.symm (Ideal.Quotient.mk _ (qCA₀ c₀)) =
      Ideal.Quotient.mk _ (toRC c₀)
    rw [← h, eRtruncA₀.symm_apply_apply]
  let : IsIso β := hβiso
  let : 𝒳.val.p.IsHomLift (𝟙 (siteObject B S hS hR fR)) β := hβ
  have hβinv : 𝒳.val.p.IsHomLift
      (𝟙 (siteObject B S hS hR fR)) (inv β) := by
    simpa using (inferInstance : 𝒳.val.p.IsHomLift
      (inv (𝟙 (siteObject B S hS hR fR))) (inv β))
  let : 𝒳.val.p.IsStronglyCartesian
      (𝟙 (siteObject B S hS hR fR)) (inv β) := by
    let := hβinv
    infer_instance
  let rU : xRN.1 ⟶ xU.1 := r ≫ inv β
  have hrU : 𝒳.val.p.IsStronglyCartesian iR rU := by
    let : 𝒳.val.p.IsStronglyCartesian iR r := hr
    have h : 𝒳.val.p.IsStronglyCartesian
        (iR ≫ 𝟙 (siteObject B S hS hR fR)) (r ≫ inv β) := inferInstance
    simpa only [Category.comp_id, rU] using h
  have hrUδ : 𝒳.val.p.IsStronglyCartesian (iR ≫ lC) (rU ≫ δ) := by
    let : 𝒳.val.p.IsStronglyCartesian iR rU := hrU
    let : 𝒳.val.p.IsStronglyCartesian lC δ := hδ
    infer_instance
  let : Algebra Λ B' := φΛB.toAlgebra
  have hEssΛB' : Algebra.EssFiniteType Λ B' := by
    apply RingHom.essFiniteType_algebraMap.mp
    show φΛB.EssFiniteType
    exact (RingHom.essFiniteType_algebraMap.mpr hEssΛT).comp
      (RingHom.essFiniteType_algebraMap.mpr
        (inferInstance : Algebra.EssFiniteType T B'))
  let : Algebra Λ A₀ := φΛA₀.toAlgebra
  let qBA₀ : B' →ₐ[Λ] A₀ :=
    { toRingHom := Ideal.Quotient.mk JB
      commutes' := fun _ ↦ rfl }
  have hEssΛA₀ : Algebra.EssFiniteType Λ A₀ :=
    Algebra.EssFiniteType.of_surjective qBA₀ Ideal.Quotient.mk_surjective
  obtain ⟨Abar, Mbar, hAbarFinite, hAbarLoc⟩ :=
    (Algebra.essFiniteType_iff_exists_subalgebra Λ A₀).mp hEssΛA₀
  let : Algebra.FiniteType Λ Abar := hAbarFinite
  let : IsLocalization Mbar A₀ := hAbarLoc
  let eAlg : (R ⧸ maximalIdeal R ^ N) ≃ₐ[Λ] (A₀ ⧸ mA₀ ^ N) :=
    AlgEquiv.ofRingEquiv (f := eRtruncA₀) (by
      intro z
      show eRtruncA₀ (Ideal.Quotient.mk ((maximalIdeal R) ^ N) (φΛR z)) =
        Ideal.Quotient.mk (mA₀ ^ N) (φΛA₀ z)
      exact heRtruncA₀_Λ z)
  let : Module.Finite Λ (R ⧸ maximalIdeal R) :=
    finite_quotient_of_compatible_algebraMap φΛR φΛk hφΛquot hfinK
  let : Module.Finite Λ mA₀.ResidueField :=
    finite_residueField_of_trunc_equiv mA₀ N hN eAlg
  let qCA₀Alg : C →ₐ[Λ] A₀ :=
    { toRingHom := qCA₀
      commutes' := fun z ↦ RingHom.congr_fun hΛCA₀ z }
  obtain ⟨Afin, hAbarAfin, hAfinFinite, qCAfin, hqCAfin⟩ :=
    exists_finiteType_intermediate_range Abar qCA₀Alg
  let : Algebra.FiniteType Λ Afin := hAfinFinite
  let mAfin : Ideal Afin := Ideal.comap (algebraMap Afin A₀) mA₀
  have hmAfin : mAfin.IsMaximal := by
    let : mA₀.IsMaximal := hmA₀
    exact isMaximal_comap_of_finite_residueField (Λ := Λ) mA₀
  have hAfinSite : B.Contains (Spec (.of Afin)) :=
    Scheme.size_Spec_lt_of_finiteType B.aleph0_lt_cutoff
      B.cutoff_isStrongPrelimit Λ Afin hΛsite
  let fAfin : Spec (.of Afin) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap Λ Afin)) ≫ U.2.fromSpec
  have hAfinLocFinite : LocallyOfFiniteType fAfin := by
    dsimp [fAfin]
    have : LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom (algebraMap Λ Afin))) :=
      (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
        (RingHom.finiteType_algebraMap.mpr inferInstance)
    have : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
    infer_instance
  have hAfinQuasi : QuasiCompact fAfin := quasiCompact_of_compactSpace _
  have hqCAfinGeom :
      Spec.map (CommRingCat.ofHom qCAfin.toRingHom) ≫ fC = fAfin := by
    exact specMap_comp_comp_eq_of_comp_eq _ _ _ qCAfin.comp_algebraMap _
  let uFin : siteObject B S hS hAfinSite fAfin ⟶
      siteObject B S hS hCsite fC :=
    siteObjectHom B S hS hAfinSite hCsite fAfin fC
      (Spec.map (CommRingCat.ofHom qCAfin.toRingHom)) hqCAfinGeom
  let xAfin := 𝒳.val.p.pullbackFiber x' uFin
  let aAfin : xAfin.1 ⟶ x'.1 := Functor.IsPreFibered.pullbackMap x'.2 uFin
  have haAfin : 𝒳.val.p.IsStronglyCartesian uFin aAfin :=
    𝒳.isFiberedInGroupoids.isStronglyCartesian_homLift uFin aAfin
  let Mfin : Submonoid Afin := Mbar.map (Subalgebra.inclusion hAbarAfin).toRingHom
  let : IsLocalization Mfin A₀ := localization_intermediate Abar Afin hAbarAfin Mbar
  let : mAfin.IsMaximal := hmAfin
  let : mA₀.IsMaximal := hmA₀
  let inc : Afin →+* A₀ := algebraMap Afin A₀
  have hinc : mAfin ≤ Ideal.comap inc mA₀ := le_rfl
  have hincTrunc (n : ℕ) : Function.Bijective (Ideal.quotientMap (mA₀ ^ n) inc
      ((Ideal.pow_right_mono hinc n).trans (Ideal.le_comap_pow inc n))) :=
    localization_trunc_bijective Mfin mA₀ mAfin rfl n
  let eFinN : (Afin ⧸ mAfin ^ N) ≃+* (A₀ ⧸ mA₀ ^ N) :=
    RingEquiv.ofBijective _ (hincTrunc N)
  have heFinN (a : Afin) : eFinN (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ (inc a) := rfl
  let φ := eRtruncA₀.trans eFinN.symm
  have htruncFinC : φ.symm.toRingHom.comp
      ((Ideal.Quotient.mk (mAfin ^ N)).comp qCAfin.toRingHom) =
      (Ideal.Quotient.mk ((maximalIdeal R) ^ N)).comp toRC.toRingHom := by
    ext a
    show eRtruncA₀.symm (eFinN (Ideal.Quotient.mk _ (qCAfin a))) = _
    rw [heFinN]
    have hq : inc (qCAfin a) = qCA₀ a := AlgHom.congr_fun hqCAfin a
    rw [hq]
    exact RingHom.congr_fun htruncC' a
  have htruncFinΛ : φ.symm.toRingHom.comp
      ((Ideal.Quotient.mk (mAfin ^ N)).comp (algebraMap Λ Afin)) =
      (Ideal.Quotient.mk ((maximalIdeal R) ^ N)).comp φΛR := by
    ext z
    show eRtruncA₀.symm (eFinN (Ideal.Quotient.mk _ (algebraMap Λ Afin z))) = _
    rw [heFinN]
    show eRtruncA₀.symm (Ideal.Quotient.mk _ (φΛA₀ z)) = _
    exact RingHom.congr_fun htruncRing₀ z
  have htruncFinGeom : Spec.map (CommRingCat.ofHom φ.symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (mAfin ^ N))) ≫ fAfin =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((maximalIdeal R) ^ N))) ≫ fR :=
    specMap_truncation_square U.2.fromSpec (algebraMap Λ Afin)
      (Ideal.Quotient.mk (mAfin ^ N)) φΛR (Ideal.Quotient.mk ((maximalIdeal R) ^ N))
      φ.symm.toRingHom fAfin fR rfl hφΛR htruncFinΛ
  have hFinNsite : B.Contains (Spec (.of (Afin ⧸ mAfin ^ N))) :=
    contains_spec_quotient B hAfinSite (mAfin ^ N)
  let iFin : siteObject B S hS hFinNsite
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (mAfin ^ N))) ≫ fAfin) ⟶
      siteObject B S hS hAfinSite fAfin :=
    siteObjectHom B S hS hFinNsite hAfinSite _ _ _ rfl
  let eBase : siteObject B S hS hRN
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((maximalIdeal R) ^ N))) ≫ fR) ⟶
      siteObject B S hS hFinNsite
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (mAfin ^ N))) ≫ fAfin) :=
    siteObjectHom B S hS hRN hFinNsite _ _
      (Spec.map (CommRingCat.ofHom φ.symm.toRingHom)) htruncFinGeom
  have : IsIso eBase := by
    apply (isIso_iff_of_reflects_iso eBase (Over.forget (B.obj hS))).mp
    apply (ObjectProperty.isIso_hom_iff _).mp
    show IsIso (Spec.map (CommRingCat.ofHom φ.symm.toRingHom))
    let : IsIso (CommRingCat.ofHom φ.symm.toRingHom) :=
      Iso.isIso_hom φ.symm.toCommRingCatIso
    infer_instance
  let xFinN := 𝒳.val.p.pullbackFiber xAfin iFin
  let aFinN : xFinN.1 ⟶ xAfin.1 := Functor.IsPreFibered.pullbackMap xAfin.2 iFin
  have haFinN : 𝒳.val.p.IsStronglyCartesian iFin aFinN :=
    𝒳.isFiberedInGroupoids.isStronglyCartesian_homLift iFin aFinN
  have hbaseFin : iR ≫ lC = eBase ≫ (iFin ≫ uFin) := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact (specMap_comp_three_eq_of_ringHom φ.symm.toRingHom
      (Ideal.Quotient.mk (mAfin ^ N)) qCAfin.toRingHom
      (Ideal.Quotient.mk ((maximalIdeal R) ^ N)) toRC.toRingHom htruncFinC).symm
  let : 𝒳.val.p.IsStronglyCartesian iFin aFinN := haFinN
  let : 𝒳.val.p.IsStronglyCartesian uFin aAfin := haAfin
  let : 𝒳.val.p.IsHomLift (iR ≫ lC) (rU ≫ δ) := hrUδ.toIsHomLift
  let eFinObj : xRN.1 ⟶ xFinN.1 := Functor.IsStronglyCartesian.map 𝒳.val.p
    (iFin ≫ uFin) (aFinN ≫ aAfin) hbaseFin (rU ≫ δ)
  have heFinObjLift : 𝒳.val.p.IsHomLift eBase eFinObj := by
    dsimp only [eFinObj]
    infer_instance
  have : IsIso eFinObj := by
    let : 𝒳.val.p.IsHomLift eBase eFinObj := heFinObjLift
    let : 𝒳.val.p.IsStronglyCartesian eBase eFinObj :=
      𝒳.isFiberedInGroupoids.isStronglyCartesian_homLift eBase eFinObj
    exact Functor.IsStronglyCartesian.isIso_of_base_isIso 𝒳.val.p eBase eFinObj
  have hJP : Ideal.map ιB.toRingHom JB = Ideal.span (Set.range bP') := by
    show Ideal.map ιB.toRingHom (Ideal.span (Set.range bB)) = _
    rw [Ideal.map_span, ← Set.range_comp']
    rfl
  obtain ⟨gr, hgrGrade, hgrZero⟩ := exists_gradedRingEquiv_of_approximation
    φP hφPsurj ιB.toRingHom mB JB hι hιTrunc (Ideal.span (Set.range bP')) hJP
    (fun n ↦ by
      rw [← hbP]
      exact hcAR bP' kP' (fun j ↦ Ideal.pow_le_pow_right hcN' (hbPclose j))
        (fun i j ↦ Ideal.pow_le_pow_right hcN' (hkPclose i j)) hsyzygyB n)
    mAfin inc hinc hincTrunc N hN eRtruncA₀ heApprox eFinN heFinN φ
    (fun z ↦ eFinN.apply_symm_apply (eRtruncA₀ z))
  exact exists_approximation_of_data_univ B S hS 𝒳 R hR fR x N Afin mAfin hmAfin fAfin
    hAfinSite hRN hFinNsite xAfin hAfinLocFinite hAfinQuasi φ htruncFinGeom
    iR iFin eBase xRN xFinN r aFinN eFinObj rfl rfl rfl hr haFinN heFinObjLift
    inferInstance gr hgrGrade hgrZero
end Deformation.Artin.Approximation
