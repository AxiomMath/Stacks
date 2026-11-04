module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Data.List.TFAE
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndEtale.VTopologyLimits
public import StacksFrontier.AlgebraicGeometry.Topologies.H.Coverings
public import StacksFrontier.AlgebraicGeometry.Topologies.V.PhVFlatteningModification
public import StacksFrontier.AlgebraicGeometry.Topologies.V.PhVTfae
public import StacksFrontier.RingTheory.Algebra.DirectLimit.FinitePresentation
public import StacksCore.Tactic.StacksAttribute

/-!
# Standard V coverings as limits of ph and of h coverings

A morphism of affine schemes is a standard V covering exactly when it is a directed inverse
limit, over a fixed affine base, of affine ph coverings, and exactly when it is such a limit
of affine h coverings.

## Main results

* `AlgebraicGeometry.standardVCovering_of_isVCovering_singleton` and
  `AlgebraicGeometry.isVCovering_of_standardVCovering_singleton`: for a single morphism of
  affine schemes, being a V covering and being a standard V covering agree.
* `AlgebraicGeometry.isStandardVCovering_of_exists_isPHCovering_limit`: a directed inverse
  limit over the base of affine ph coverings is a standard V covering.
* `AlgebraicGeometry.exists_isPHCovering_limit_of_exists_isHCovering_limit`: a directed inverse
  limit over the base of affine h coverings is one of affine ph coverings.
* `AlgebraicGeometry.isStandardVCovering_limit_tfae_unconditional`: the three conditions are
  equivalent.
* `AlgebraicGeometry.isStandardVCovering_limit_tfae`: the same equivalence, stated with
  `AlgebraicGeometry.StandardVCoveringHasPHRefinement` as a hypothesis.

## References

* [Stacks Project, Tag 0EVP](https://stacks.math.columbia.edu/tag/0EVP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Reindexing a directed preorder by `ULift` is an equivalence of the opposite categories. -/
@[reducible] private def uliftOppositeOrderEquiv (α : Type u) [Preorder α] :
    (ULift.{u + 1} α)ᵒᵖ ≌ αᵒᵖ := by
  let F : (ULift.{u + 1} α)ᵒᵖ ⥤ αᵒᵖ :=
    { obj := fun i ↦ Opposite.op i.unop.down
      map := fun {i j} f ↦
        (homOfLE (show j.unop.down ≤ i.unop.down by simpa using f.unop.le)).op
      map_id := by intros; exact Subsingleton.elim _ _
      map_comp := by intros; exact Subsingleton.elim _ _ }
  let G : αᵒᵖ ⥤ (ULift.{u + 1} α)ᵒᵖ :=
    { obj := fun i ↦ Opposite.op (ULift.up.{u + 1} i.unop)
      map := fun {i j} f ↦
        (homOfLE (show ULift.up.{u + 1} j.unop ≤ ULift.up.{u + 1} i.unop by
          exact ULift.up_le.mpr f.unop.le)).op
      map_id := by intro i; exact Subsingleton.elim _ _
      map_comp := by intros; exact Subsingleton.elim _ _ }
  refine
    { functor := F
      inverse := G
      unitIso := NatIso.ofComponents (fun i ↦ eqToIso (by cases i; rfl))
        (by intro i j f; exact Subsingleton.elim _ _)
      counitIso := NatIso.ofComponents (fun i ↦ eqToIso (by cases i; rfl))
        (by intro i j f; exact Subsingleton.elim _ _) }

namespace DirectedPresentation

variable {R : Type u} [CommRing R] {Λ : Type u} [PartialOrder Λ]
  [Nonempty Λ] [IsDirectedOrder Λ]
  (G : Λ → Type u) [∀ i, CommRing (G i)] [∀ i, Algebra R (G i)]
  (q : ∀ i j, i ≤ j → G i →ₐ[R] G j)
  [DirectedSystem G fun i j h ↦ ⇑(q i j h)]

/-- A directed system of algebras, read as a diagram of commutative rings. -/
def ringDiagram : Λ ⥤ CommRingCat.{u} where
  obj i := CommRingCat.of (G i)
  map {i j} h := CommRingCat.ofHom (q i j h.le).toRingHom
  map_id i := by ext x; exact DirectedSystem.map_self (f := fun i j h ↦ ⇑(q i j h)) x
  map_comp {i j k} h₁ h₂ := by
    ext x
    exact (DirectedSystem.map_map (f := fun i j h ↦ ⇑(q i j h)) h₁.le h₂.le x).symm

variable {A : Type u} [CommRing A] [Algebra R A]
  (g : ∀ i, G i →ₐ[R] A) (hg : ∀ i j h x, g j (q i j h x) = g i x)

/-- A compatible family of algebra maps out of a directed system, read as a cocone. -/
def compatibleCocone : Cocone (ringDiagram G q) where
  pt := CommRingCat.of A
  ι := { app i := CommRingCat.ofHom (g i).toRingHom
         naturality := fun i j h ↦ by ext x; exact hg i j h.le x }

/-- The direct limit of a directed system of algebras, read as a cocone. -/
noncomputable def directLimitCocone : Cocone (ringDiagram G q) :=
  compatibleCocone G q (DirectLimit.Algebra.of G q)
    (fun _ _ h x ↦ DirectLimit.Algebra.of_f h x)

/-- The direct-limit cocone is a colimit cocone. -/
noncomputable def directLimitIsColimit : IsColimit (directLimitCocone G q) where
  desc t := CommRingCat.ofHom <| DirectLimit.Ring.lift G q ↑t.pt
    (fun i ↦ (t.ι.app i).hom) (fun _ _ h x ↦ congr($(t.w (homOfLE h)).hom x))
  fac t i := by ext x; rfl
  uniq t m hm := by
    ext x
    induction x using DirectLimit.induction with
    | _ i y => exact congr($(hm i).hom y)

/-- A compatible family whose induced map from the direct limit is bijective presents its
target as the colimit. -/
noncomputable def compatibleIsColimit
    (hbij : Function.Bijective (DirectLimit.Algebra.lift G q A g hg)) :
    IsColimit (compatibleCocone G q g hg) :=
  (directLimitIsColimit G q).ofIsoColimit <| Cocone.ext
    (RingEquiv.ofBijective (DirectLimit.Algebra.lift G q A g hg).toRingHom hbij).toCommRingCatIso
    (fun _ ↦ by ext x; rfl)

end DirectedPresentation

open DirectedPresentation

/-- A single morphism of affine schemes which is a V covering is a standard V covering. -/
theorem standardVCovering_of_isVCovering_singleton
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    (hv : IsVCovering (fun _ : Unit ↦ X) (fun _ ↦ f)) :
    IsStandardVCovering (fun _ : Unit ↦ X) (fun _ ↦ f) := by
  let U : Y.Opens := ⊤
  let T := U.toScheme
  let g : T ⟶ Y := U.ι
  let : IsAffine T := isAffineOpen_top Y
  let : IsIso g := by
    refine ⟨(Scheme.topIso Y).inv, ?_, ?_⟩
    · dsimp [g, U]; exact (Scheme.topIso Y).hom_inv_id
    · dsimp [g, U]; exact (Scheme.topIso Y).inv_hom_id
  let P : PreZeroHypercover T :=
    ({ I₀ := Unit, X := fun _ ↦ X, f := fun _ ↦ f } : PreZeroHypercover Y).pullback₂ g
  let : Finite P.I₀ := by change Finite Unit; infer_instance
  let : ∀ i, IsAffine (P.X i) := by
    intro i
    cases i
    show IsAffine (pullback f g)
    let : IsIso (pullback.fst f g) := inferInstance
    exact IsAffine.of_isIso (pullback.fst f g)
  let : IsIso (pullback.fst f g) := inferInstance
  obtain ⟨𝒰, _, _, h𝒰, hrefine⟩ := hv U (isAffineOpen_top Y)
  have hstd : IsStandardVCovering P.X P.f := by
    intro V _ _ _ a
    obtain ⟨W, _, _, _, e, he, k, h, hw⟩ := h𝒰 V a
    obtain ⟨r⟩ := hrefine
    refine ⟨W, inferInstance, inferInstance, inferInstance, e, he, r.s₀ k, h ≫ r.h₀ k, ?_⟩
    rw [Category.assoc, r.w₀, hw]
  let eY : T ≅ Y := Scheme.topIso Y
  let eX (j : P.I₀) : P.X j ≅ X := by
    cases j
    show pullback f g ≅ X
    exact asIso (pullback.fst f g)
  have hfactor (j : P.I₀) : (eX j).hom ≫ f = P.f j ≫ eY.hom := by
    cases j
    dsimp [eX, eY, P, PreZeroHypercover.pullback₂]
    exact pullback.condition
  rw [isStandardVCovering_iff] at hstd ⊢
  intro V _ _ _ k
  obtain ⟨W, _, _, _, e, he, j, h, hh⟩ := hstd V (k ≫ eY.inv)
  refine ⟨W, inferInstance, inferInstance, inferInstance, e, he, j, h ≫ (eX j).hom, ?_⟩
  calc
    Spec.map (CommRingCat.ofHom e) ≫ k =
        (Spec.map (CommRingCat.ofHom e) ≫ k ≫ eY.inv) ≫ eY.hom := by simp [Category.assoc]
    _ = (h ≫ P.f j) ≫ eY.hom := by rw [hh]
    _ = (h ≫ (eX j).hom) ≫ f := by rw [Category.assoc, Category.assoc, hfactor j]

/-- A single morphism of affine schemes which is a standard V covering is a V covering. -/
theorem isVCovering_of_standardVCovering_singleton
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    (hs : IsStandardVCovering (fun _ : Unit ↦ X) (fun _ ↦ f)) :
    IsVCovering (fun _ : Unit ↦ X) (fun _ ↦ f) := by
  rw [isVCovering_iff]
  intro U hU
  let : IsAffine U.toScheme := hU
  let P := ({ I₀ := Unit, X := fun _ ↦ X, f := fun _ ↦ f } : PreZeroHypercover Y).pullback₂ U.ι
  have hP := isStandardVCovering_pullback (X := fun _ : Unit ↦ X) (f := fun _ ↦ f) U.ι hs
  have hPLift : IsStandardVCovering
      (fun _ : ULift.{u} Unit ↦ pullback f U.ι) (fun _ ↦ pullback.snd f U.ι) := by
    rw [isStandardVCovering_iff] at hP ⊢
    intro V _ _ _ k
    obtain ⟨W, _, _, _, e, he, j, h, hh⟩ := hP V k
    exact ⟨W, inferInstance, inferInstance, inferInstance, e, he, ⟨()⟩, h, hh⟩
  let V : PreZeroHypercover.{u} U.toScheme :=
    { I₀ := ULift.{u} Unit
      X := fun _ ↦ pullback f U.ι
      f := fun _ ↦ pullback.snd f U.ι }
  let : Finite V.I₀ := inferInstance
  let : ∀ i, IsAffine (V.X i) := fun _ ↦ inferInstance
  have hV : IsStandardVCovering V.X V.f := hPLift
  have hRefine : Nonempty (V.Hom P) :=
    ⟨{ s₀ := fun _ ↦ ()
       h₀ := fun _ ↦ 𝟙 (pullback f U.ι)
       w₀ := fun _ ↦ by simp [V, P, PreZeroHypercover.pullback₂] }⟩
  exact ⟨V, inferInstance, inferInstance, hV, hRefine⟩

/-- `Spec` turns a commuting triangle of ring homomorphisms into a commuting triangle. -/
private theorem spec_map_ofHom_comp_eq {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (a : A →+* B) (b : B →+* C) (c : A →+* C) (h : ∀ x, b (a x) = c x) :
    Spec.map (CommRingCat.ofHom b) ≫ Spec.map (CommRingCat.ofHom a) =
      Spec.map (CommRingCat.ofHom c) := by
  rw [← Spec.map_comp]
  congr 1
  ext x
  exact h x

/-- A morphism of affine schemes which is a directed inverse limit over the base of affine ph
coverings is a standard V covering. -/
@[stacks 0EVP "(2) implies (1)"]
theorem isStandardVCovering_of_exists_isPHCovering_limit
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    (h : ∃ (I : Type (u + 1)) (_ : Preorder I) (_ : Nonempty I)
        (_ : IsDirectedOrder I) (D : Iᵒᵖ ⥤ Scheme.{u})
        (t : D ⟶ (Functor.const Iᵒᵖ).obj Y)
        (p : (Functor.const Iᵒᵖ).obj X ⟶ D)
        (_ : IsLimit (Cone.mk X p))
        (_ : IsColimit ((Scheme.Γ ⋙ forget CommRingCat).mapCocone (Cone.mk X p).op)),
      (p ≫ t = (Functor.const Iᵒᵖ).map f) ∧
        (∀ i, IsAffine (D.obj i)) ∧
        (∀ i, IsPHCovering (fun _ : Unit ↦ D.obj i) (fun _ ↦ t.app i))) :
    IsStandardVCovering (fun _ : Unit ↦ X) (fun _ ↦ f) := by
  obtain ⟨I, hpre, hnonempty, hdirected, D, t, p, hlim, hΓ, hcompat, haffine, hph⟩ := h
  let : Preorder I := hpre
  let : Nonempty I := hnonempty
  let : IsDirectedOrder I := hdirected
  let : ∀ i, IsAffine (D.obj i) := haffine
  let (i : Iᵒᵖ) : IsAffine (((Functor.const (Iᵒᵖ)).obj Y).obj i) := by
    show IsAffine Y
    infer_instance
  let c : Cone D := Cone.mk X p
  have hStage : ∀ i, IsStandardVCovering (fun _ : Unit ↦ D.obj i) (fun _ ↦ t.app i) := by
    intro i
    exact standardVCovering_of_isVCovering_singleton (t.app i)
      (isVCovering_of_isPHCovering (fun _ : Unit ↦ D.obj i) (fun _ ↦ t.app i) (hph i))
  exact (ProEtale.isStandardVCovering_limit_iff D t c hlim hΓ f hcompat).mpr hStage

/-- A presentation of a morphism of affine schemes as a directed inverse limit over the base of
affine h coverings is one by affine ph coverings. -/
@[stacks 0EVP "(3) implies (2)"]
theorem exists_isPHCovering_limit_of_exists_isHCovering_limit
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    (h : ∃ (I : Type (u + 1)) (_ : Preorder I) (_ : Nonempty I)
        (_ : IsDirectedOrder I) (D : Iᵒᵖ ⥤ Scheme.{u})
        (t : D ⟶ (Functor.const Iᵒᵖ).obj Y)
        (p : (Functor.const Iᵒᵖ).obj X ⟶ D)
        (_ : IsLimit (Cone.mk X p))
        (_ : IsColimit ((Scheme.Γ ⋙ forget CommRingCat).mapCocone (Cone.mk X p).op)),
      (p ≫ t = (Functor.const Iᵒᵖ).map f) ∧
        (∀ i, IsAffine (D.obj i)) ∧
        (∀ i, IsHCovering (fun _ : Unit ↦ D.obj i) (fun _ ↦ t.app i))) :
    ∃ (I : Type (u + 1)) (_ : Preorder I) (_ : Nonempty I)
      (_ : IsDirectedOrder I) (D : Iᵒᵖ ⥤ Scheme.{u})
      (t : D ⟶ (Functor.const Iᵒᵖ).obj Y)
      (p : (Functor.const Iᵒᵖ).obj X ⟶ D)
      (_ : IsLimit (Cone.mk X p))
      (_ : IsColimit ((Scheme.Γ ⋙ forget CommRingCat).mapCocone (Cone.mk X p).op)),
      (p ≫ t = (Functor.const Iᵒᵖ).map f) ∧
        (∀ i, IsAffine (D.obj i)) ∧
        (∀ i, IsPHCovering (fun _ : Unit ↦ D.obj i) (fun _ ↦ t.app i)) := by
  obtain ⟨I, hpre, hnonempty, hdirected, D, t, p, hlim, hΓ, hcompat, haffine, hh⟩ := h
  exact ⟨I, hpre, hnonempty, hdirected, D, t, p, hlim, hΓ, hcompat, haffine,
    fun i ↦ (hh i).2⟩

/-- A morphism of affine schemes is a standard V covering exactly when it is a directed inverse
limit over the base of affine ph coverings, and exactly when it is such a limit of affine h
coverings. -/
@[stacks 0EVP "(1) implies (3); the other two implications are stated without the hard \
direction of Stacks 0ETR and tagged separately"]
theorem isStandardVCovering_limit_tfae_unconditional
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) :
    List.TFAE [
      IsStandardVCovering (fun _ : Unit ↦ X) (fun _ ↦ f),
      (∃ (I : Type (u + 1)) (_ : Preorder I) (_ : Nonempty I)
          (_ : IsDirectedOrder I) (D : Iᵒᵖ ⥤ Scheme.{u})
          (t : D ⟶ (Functor.const Iᵒᵖ).obj Y)
          (p : (Functor.const Iᵒᵖ).obj X ⟶ D)
          (_ : IsLimit (Cone.mk X p))
          (_ : IsColimit ((Scheme.Γ ⋙ forget CommRingCat).mapCocone (Cone.mk X p).op)),
        (p ≫ t = (Functor.const Iᵒᵖ).map f) ∧
          (∀ i, IsAffine (D.obj i)) ∧
          (∀ i, IsPHCovering (fun _ : Unit ↦ D.obj i) (fun _ ↦ t.app i))),
      (∃ (I : Type (u + 1)) (_ : Preorder I) (_ : Nonempty I)
          (_ : IsDirectedOrder I) (D : Iᵒᵖ ⥤ Scheme.{u})
          (t : D ⟶ (Functor.const Iᵒᵖ).obj Y)
          (p : (Functor.const Iᵒᵖ).obj X ⟶ D)
          (_ : IsLimit (Cone.mk X p))
          (_ : IsColimit ((Scheme.Γ ⋙ forget CommRingCat).mapCocone (Cone.mk X p).op)),
        (p ≫ t = (Functor.const Iᵒᵖ).map f) ∧
          (∀ i, IsAffine (D.obj i)) ∧
          (∀ i, IsHCovering (fun _ : Unit ↦ D.obj i) (fun _ ↦ t.app i)))] := by
  tfae_have 2 → 1 := isStandardVCovering_of_exists_isPHCovering_limit f
  tfae_have 3 → 2 := exists_isPHCovering_limit_of_exists_isHCovering_limit f
  tfae_have 1 → 3 := by
    intro hStd
    let R : Type u := (Γ(Y, ⊤)).carrier
    let A : Type u := (Γ(X, ⊤)).carrier
    let : Algebra R A := f.appTop.hom.toAlgebra
    obtain ⟨Λ, hPO, hNonempty, hDirected, G, hComm, hAlg, q, hDS, g, hg, hFP, _, hbij⟩ :=
      Algebra.exists_directedSystem_finitePresentation_lift_bijective R A
    let : PartialOrder Λ := hPO
    let : Nonempty Λ := hNonempty
    let : IsDirectedOrder Λ := hDirected
    let : ∀ i, CommRing (G i) := hComm
    let : ∀ i, Algebra R (G i) := hAlg
    let : DirectedSystem G (fun i j h ↦ ⇑(q i j h)) := hDS
    let F : Λ ⥤ CommRingCat.{u} := ringDiagram G q
    let C : Cocone F := compatibleCocone G q g hg
    have hC : IsColimit C := compatibleIsColimit G q g hg hbij
    let D₀ : Λᵒᵖ ⥤ Scheme.{u} := F.op ⋙ Scheme.Spec
    let c₀ : Cone D₀ := Scheme.Spec.mapCone (Cocone.op C)
    have hc₀ : IsLimit c₀ := isLimitOfPreserves Scheme.Spec hC.op
    let I := ULift.{u + 1} Λ
    let : PartialOrder I := inferInstance
    let : Nonempty I := ⟨⟨Classical.choice hNonempty⟩⟩
    let : IsDirectedOrder I := ⟨fun a b ↦ by
      obtain ⟨c, hac, hbc⟩ := hDirected.directed a.down b.down
      exact ⟨⟨c⟩, hac, hbc⟩⟩
    let eop := uliftOppositeOrderEquiv Λ
    let D : Iᵒᵖ ⥤ Scheme.{u} := eop.functor ⋙ D₀
    let c : Cone D := Cone.whisker eop.functor c₀
    have hc : IsLimit c := hc₀.whiskerEquivalence eop
    let p : (Functor.const Iᵒᵖ).obj X ⟶ D :=
      { app i := by
          show X ⟶ Spec (CommRingCat.of (G i.unop.down))
          exact X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (g i.unop.down).toRingHom)
        naturality := by
          intro i j α
          have hij : j.unop.down ≤ i.unop.down := (α.unop).le
          show X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (g j.unop.down).toRingHom) =
            (X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (g i.unop.down).toRingHom)) ≫
              Spec.map (CommRingCat.ofHom (q j.unop.down i.unop.down hij).toRingHom)
          rw [Category.assoc, spec_map_ofHom_comp_eq _ _ _ (hg j.unop.down i.unop.down hij)] }
    let cX : Cone D := Cone.mk X p
    have hcX : IsLimit cX := by
      let eX : c.pt ≅ X := by
        show Spec (CommRingCat.of A) ≅ X
        exact X.isoSpec.symm
      apply hc.ofIsoLimit (Cone.ext (c := c) (c' := cX) eX (by
        intro i
        dsimp [cX, p, c, c₀, D, D₀, F, C, compatibleCocone, ringDiagram,
          eop, uliftOppositeOrderEquiv, eX]
        rw [Iso.inv_hom_id_assoc]))
    let t : D ⟶ (Functor.const Iᵒᵖ).obj Y :=
      { app i := by
          show Spec (CommRingCat.of (G i.unop.down)) ⟶ Y
          exact Spec.map (CommRingCat.ofHom (algebraMap R (G i.unop.down))) ≫ Y.isoSpec.inv
        naturality := by
          intro i j α
          have hij : j.unop.down ≤ i.unop.down := (α.unop).le
          show Spec.map (CommRingCat.ofHom (q j.unop.down i.unop.down hij).toRingHom) ≫
              (Spec.map (CommRingCat.ofHom (algebraMap R (G j.unop.down))) ≫ Y.isoSpec.inv) =
            (Spec.map (CommRingCat.ofHom (algebraMap R (G i.unop.down))) ≫ Y.isoSpec.inv) ≫ 𝟙 Y
          rw [← Category.assoc, spec_map_ofHom_comp_eq _ _ _
            (q j.unop.down i.unop.down hij).commutes]
          simp }
    have hcompat : p ≫ t = (Functor.const Iᵒᵖ).map f := by
      ext i
      dsimp [p, t]
      show X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (g i.unop.down).toRingHom) ≫
          (Spec.map (CommRingCat.ofHom (algebraMap R (G i.unop.down))) ≫ Y.isoSpec.inv) = f
      have hbase := spec_map_ofHom_comp_eq (algebraMap R (G i.unop.down)) (g i.unop.down).toRingHom
        f.appTop.hom fun x ↦ ((g i.unop.down).commutes x).trans
          (by simp [A, RingHom.algebraMap_toAlgebra])
      have hnat : X.isoSpec.hom ≫
          Spec.map (CommRingCat.ofHom f.appTop.hom) = f ≫ Y.isoSpec.hom := by
        simpa using Scheme.isoSpec_hom_naturality f
      calc
        _ = (X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom f.appTop.hom)) ≫
            Y.isoSpec.inv := by rw [← hbase]; simp only [Category.assoc]
        _ = f := by rw [hnat]; simp
    let (i : Iᵒᵖ) : IsAffine (((Functor.const Iᵒᵖ).obj Y).obj i) := by
      show IsAffine Y
      infer_instance
    let (i : Iᵒᵖ) : IsAffine (D.obj i) := by
      show IsAffine (Spec (CommRingCat.of (G i.unop.down)))
      infer_instance
    have hΓ : IsColimit ((Scheme.Γ ⋙ forget CommRingCat).mapCocone cX.op) := by
      let : PreservesColimitsOfShape (Iᵒᵖ)ᵒᵖ (forget CommRingCat.{u}) :=
        preservesColimitsOfShape_of_equiv eop.op.symm (forget CommRingCat.{u})
      have (i : (Iᵒᵖ)ᵒᵖ) : IsAffine (D.op.obj i).unop := by
        show IsAffine (D.obj i.unop)
        infer_instance
      exact isColimitOfPreserves (forget CommRingCat) (isColimitOfPreserves Scheme.Γ hcX.op)
    have hStage : ∀ i, IsHCovering (fun _ : Unit ↦ D.obj i) (fun _ ↦ t.app i) := by
      intro i
      have hlfpSpec : LocallyOfFinitePresentation
          (Spec.map (CommRingCat.ofHom (algebraMap R (G i.unop.down)))) :=
        (LocallyOfFinitePresentation.SpecMap_iff
          (CommRingCat.ofHom (algebraMap R (G i.unop.down)))).2 (by
            show (algebraMap R (G i.unop.down)).FinitePresentation
            rw [RingHom.finitePresentation_algebraMap]
            exact hFP i.unop.down)
      have hlfp : LocallyOfFinitePresentation (t.app i) := by
        show LocallyOfFinitePresentation
          (Spec.map (CommRingCat.ofHom (algebraMap R (G i.unop.down))) ≫ Y.isoSpec.inv)
        let : LocallyOfFinitePresentation
            (Spec.map (CommRingCat.ofHom (algebraMap R (G i.unop.down)))) := hlfpSpec
        infer_instance
      let : ∀ _ : Unit, LocallyOfFinitePresentation (t.app i) := fun _ ↦ hlfp
      have hV := isVCovering_of_standardVCovering_singleton (t.app i)
        ((ProEtale.isStandardVCovering_limit_iff D t cX hcX hΓ f hcompat).mp hStd i)
      exact ⟨fun _ ↦ hlfp,
        (isPHCovering_iff_isVCovering
          (fun _ : Unit ↦ D.obj i) (fun _ ↦ t.app i) (fun _ ↦ hlfp)).mpr hV⟩
    exact ⟨I, inferInstance, inferInstance, inferInstance, D, t, p, hcX, hΓ,
      hcompat, (fun i ↦ inferInstance), hStage⟩
  tfae_finish

/-- A morphism of affine schemes is a standard V covering exactly when it is a directed inverse
limit over the base of affine ph coverings, and exactly when it is such a limit of affine h
coverings; stated with the hypothesis `AlgebraicGeometry.StandardVCoveringHasPHRefinement`,
which is not used. -/
theorem isStandardVCovering_limit_tfae (H : StandardVCoveringHasPHRefinement.{u})
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) :
    List.TFAE [
      IsStandardVCovering (fun _ : Unit ↦ X) (fun _ ↦ f),
      (∃ (I : Type (u + 1)) (_ : Preorder I) (_ : Nonempty I)
          (_ : IsDirectedOrder I) (D : Iᵒᵖ ⥤ Scheme.{u})
          (t : D ⟶ (Functor.const Iᵒᵖ).obj Y)
          (p : (Functor.const Iᵒᵖ).obj X ⟶ D)
          (_ : IsLimit (Cone.mk X p))
          (_ : IsColimit ((Scheme.Γ ⋙ forget CommRingCat).mapCocone (Cone.mk X p).op)),
        (p ≫ t = (Functor.const Iᵒᵖ).map f) ∧
          (∀ i, IsAffine (D.obj i)) ∧
          (∀ i, IsPHCovering (fun _ : Unit ↦ D.obj i) (fun _ ↦ t.app i))),
      (∃ (I : Type (u + 1)) (_ : Preorder I) (_ : Nonempty I)
          (_ : IsDirectedOrder I) (D : Iᵒᵖ ⥤ Scheme.{u})
          (t : D ⟶ (Functor.const Iᵒᵖ).obj Y)
          (p : (Functor.const Iᵒᵖ).obj X ⟶ D)
          (_ : IsLimit (Cone.mk X p))
          (_ : IsColimit ((Scheme.Γ ⋙ forget CommRingCat).mapCocone (Cone.mk X p).op)),
        (p ≫ t = (Functor.const Iᵒᵖ).map f) ∧
          (∀ i, IsAffine (D.obj i)) ∧
          (∀ i, IsHCovering (fun _ : Unit ↦ D.obj i) (fun _ ↦ t.app i)))] :=
  isStandardVCovering_limit_tfae_unconditional f

end AlgebraicGeometry

end
