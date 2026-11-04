module

public import StacksFrontier.AlgebraicGeometry.Stacks.VersalRing.Basic

/-!
# Versal rings: rebasing deformation objects along a second affine chart

The Artinian rebasing of `VersalRing.Basic`, taken along the canonical open lift, extended to the
objects and morphisms of the predeformation category of a field-valued point; part of the proof
that being a versal ring does not depend on the affine-open presentation (Stacks 0DQV).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace AlgebraicGeometry.Stack

universe u v w

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

/-- `B` read as an Artinian local `Λ'`-algebra along `canonicalArtinianOpenLift`. -/
noncomputable def rebaseArtinianAlgebraCanonical
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
    [Algebra Λ k] [Algebra Λ' k] {S : Scheme.{u}}
    (iΛ : Spec (.of Λ) ⟶ S) (iΛ' : Spec (.of Λ') ⟶ S)
    (hiΛ' : IsOpenImmersion iΛ')
    (hclosed : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ =
      Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ')
    (B : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k) :
    Deformation.ArtinianLocalAlgCat.{u, u, u} Λ' k :=
  rebaseArtinianAlgebra B (canonicalArtinianOpenLift iΛ iΛ' hiΛ' hclosed B)
    (canonicalArtinianOpenLift_residue iΛ iΛ' hiΛ' hclosed B)

/-- Canonical rebasing commutes with adic truncation. -/
theorem rebaseArtinianCanonical_truncation
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
    [Algebra Λ k] [Algebra Λ' k] {S : Scheme.{u}}
    (iΛ : Spec (.of Λ) ⟶ S) (iΛ' : Spec (.of Λ') ⟶ S)
    (hiΛ' : IsOpenImmersion iΛ')
    (hclosed : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ =
      Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ')
    (A : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k)
    (g : Λ' →+* A)
    (hg : ∀ a : Λ', A.residueEquiv (residue A (g a)) = algebraMap Λ' k a)
    (hS : Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ =
      Spec.map (CommRingCat.ofHom g) ≫ iΛ') (n : ℕ) :
    rebaseArtinianAlgebraCanonical iΛ iΛ' hiΛ' hclosed
        (Deformation.AdicTruncation.obj A n) =
      Deformation.AdicTruncation.obj (rebaseCompleteLocalAlgebra A g hg) n := by
  let B := Deformation.AdicTruncation.obj A n
  let q : A →+* B := Ideal.Quotient.mk (Deformation.AdicTruncation.ideal A n)
  let gN : Λ' →+* B := q.comp g
  have hgN : ∀ a : Λ', B.residueEquiv (residue B (gN a)) = algebraMap Λ' k a := by
    intro a
    change Deformation.AdicTruncation.residueEquiv A n
      (residue B (Ideal.Quotient.mk (Deformation.AdicTruncation.ideal A n) (g a))) = _
    have hmk := Deformation.AdicTruncation.residueEquiv_residue_mk A n (g a)
    exact hmk.trans (hg a)
  have hring : CommRingCat.ofHom (algebraMap Λ B) =
      CommRingCat.ofHom (algebraMap Λ A) ≫ CommRingCat.ofHom q := by
    apply CommRingCat.hom_ext
    ext a
    rfl
  have hspec := congrArg Spec.map hring
  have hstruct : Spec.map (CommRingCat.ofHom q) ≫
      Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ =
        Spec.map (CommRingCat.ofHom (algebraMap Λ B)) ≫ iΛ := by
    simpa [Category.assoc] using
      (congrArg (fun f => f ≫ iΛ) hspec).symm
  have hgNspec : Spec.map (CommRingCat.ofHom gN) =
      Spec.map (CommRingCat.ofHom q) ≫ Spec.map (CommRingCat.ofHom g) := by
    rw [CommRingCat.ofHom_comp, ← Spec.map_comp]
  have hgNfac : Spec.map (CommRingCat.ofHom gN) ≫ iΛ' =
      Spec.map (CommRingCat.ofHom (algebraMap Λ B)) ≫ iΛ := by
    calc
      _ = Spec.map (CommRingCat.ofHom q) ≫
          Spec.map (CommRingCat.ofHom g) ≫ iΛ' := by rw [hgNspec, Category.assoc]
      _ = Spec.map (CommRingCat.ofHom q) ≫
          Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ := by rw [← hS]
      _ = _ := hstruct
  have hmap : gN = canonicalArtinianOpenLift iΛ iΛ' hiΛ' hclosed B :=
    algebraMap_eq_canonicalArtinianOpenLift B iΛ iΛ' hiΛ' hclosed gN hgNfac
  unfold rebaseArtinianAlgebraCanonical
  rw [rebaseArtinianAlgebra_congr B _ gN _ hgN hmap.symm]
  exact rebaseArtinianAlgebra_truncation A g hg n

/-- If `ρ ≫ f = σ ≫ i'`, then `f` maps the image of a point under `ρ` into the range of `i'`. -/
private theorem apply_mem_range_of_comp_eq {R : CommRingCat.{u}} {k : Type u} [Field k]
    {X S : Scheme.{u}} (f : Spec R ⟶ S) (i' : X ⟶ S) (ρ : Spec (.of k) ⟶ Spec R)
    (σ : Spec (.of k) ⟶ X) (h : ρ ≫ f = σ ≫ i') (xk : Spec (.of k)) :
    f (ρ xk) ∈ Set.range i' :=
  ⟨σ xk, (congrArg (fun g : Spec (.of k) ⟶ S => g.base xk) h).symm⟩

/-- Two ring maps whose spectra agree after composing with a monomorphism are equal. -/
private theorem ringHom_eq_of_spec_comp_eq {R T : Type u} [CommRing R] [CommRing T]
    {S : Scheme.{u}} (i : Spec (.of R) ⟶ S) [Mono i] {g₁ g₂ : R →+* T}
    (h : Spec.map (CommRingCat.ofHom g₁) ≫ i = Spec.map (CommRingCat.ofHom g₂) ≫ i) :
    g₁ = g₂ :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono i).1 h))

/-- The morphism of canonically rebased Artinian local `Λ'`-algebras induced by a morphism
over `Λ`. -/
noncomputable def rebaseArtinianHomCanonical
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
    [Algebra Λ k] [Algebra Λ' k] {S : Scheme.{u}}
    (iΛ : Spec (.of Λ) ⟶ S) (iΛ' : Spec (.of Λ') ⟶ S)
    (hiΛ' : IsOpenImmersion iΛ')
    (hclosed : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ =
      Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ')
    {B C : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k} (f : B ⟶ C) :
    rebaseArtinianAlgebraCanonical iΛ iΛ' hiΛ' hclosed B ⟶
      rebaseArtinianAlgebraCanonical iΛ iΛ' hiΛ' hclosed C := by
  letI : IsOpenImmersion iΛ' := hiΛ'
  let xk : PrimeSpectrum k := ⟨⊥, inferInstance⟩
  let xB : PrimeSpectrum B :=
    (Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap B))).base xk
  let xC : PrimeSpectrum C :=
    (Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap C))).base xk
  let fB : Spec (.of B) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap Λ B)) ≫ iΛ
  let fC : Spec (.of C) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap Λ C)) ≫ iΛ
  have hclosedB : Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap B)) ≫ fB =
      Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ' := by
    calc
      _ = (Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap B)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap Λ B))) ≫ iΛ := by
        simp [fB, Category.assoc]
      _ = Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ := by
        rw [specMap_residueMap_comp_base B]
      _ = _ := hclosed
  have hclosedC : Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap C)) ≫ fC =
      Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ' := by
    calc
      _ = (Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap C)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap Λ C))) ≫ iΛ := by
        simp [fC, Category.assoc]
      _ = Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ := by
        rw [specMap_residueMap_comp_base C]
      _ = _ := hclosed
  have hxB : fB xB ∈ Set.range iΛ' := by
    refine ⟨(Spec.map (CommRingCat.ofHom (algebraMap Λ' k))).base xk, ?_⟩
    have hp := congrArg (fun g : Spec (.of k) ⟶ S => g.base xk) hclosedB
    change iΛ'.base ((Spec.map (CommRingCat.ofHom (algebraMap Λ' k))).base xk) =
      iΛ.base ((Spec.map (CommRingCat.ofHom (algebraMap Λ B))).base
        ((Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap B))).base xk))
    exact hp.symm
  have hxC : fC xC ∈ Set.range iΛ' := by
    refine ⟨(Spec.map (CommRingCat.ofHom (algebraMap Λ' k))).base xk, ?_⟩
    have hp := congrArg (fun g : Spec (.of k) ⟶ S => g.base xk) hclosedC
    change iΛ'.base ((Spec.map (CommRingCat.ofHom (algebraMap Λ' k))).base xk) =
      iΛ.base ((Spec.map (CommRingCat.ofHom (algebraMap Λ C))).base
        ((Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap C))).base xk))
    exact hp.symm
  let gB := artinianAlgebraMapOfOpenLift B iΛ' fB xB hxB
  let gC := artinianAlgebraMapOfOpenLift C iΛ' fC xC hxC
  have hfbase : Spec.map (CommRingCat.ofHom f.hom.toRingHom) ≫ fB = fC := by
    change Spec.map (CommRingCat.ofHom f.hom.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap Λ B)) ≫ iΛ =
      Spec.map (CommRingCat.ofHom (algebraMap Λ C)) ≫ iΛ
    have hring : CommRingCat.ofHom
        (f.hom.toRingHom.comp (algebraMap Λ B)) =
        CommRingCat.ofHom (algebraMap Λ C) := by
      apply CommRingCat.hom_ext
      ext r
      change f.hom (algebraMap Λ B r) = algebraMap Λ C r
      exact f.hom.commutes r
    have hspec := congrArg Spec.map hring
    calc
      _ = (Spec.map (CommRingCat.ofHom f.hom.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap Λ B))) ≫ iΛ := by
        simp [Category.assoc]
      _ = Spec.map (CommRingCat.ofHom (algebraMap Λ C)) ≫ iΛ := by
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
        exact congrArg (fun h => h ≫ iΛ) hspec
  have hnat := artinianAlgebraMapOfOpenLift_natural iΛ' fB xB hxB fC xC hxC f hfbase
  have hring : (f.hom.toRingHom.comp gB) = gC :=
    congrArg CommRingCat.Hom.hom hnat
  refine {
    hom := AlgHom.mk f.hom.toRingHom (fun r => ?_)
    isLocal := f.isLocal
    residue_comm := f.residue_comm }
  change f.hom.toRingHom (gB r) = gC r
  exact congrArg (fun h : Λ' →+* C => h r) hring

/-- Canonical rebasing as a functor from Artinian local `Λ`-algebras to Artinian local
`Λ'`-algebras. -/
noncomputable def rebaseArtinianFunctorCanonical
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
    [Algebra Λ k] [Algebra Λ' k] {S : Scheme.{u}}
    (iΛ : Spec (.of Λ) ⟶ S) (iΛ' : Spec (.of Λ') ⟶ S)
    (hiΛ' : IsOpenImmersion iΛ')
    (hclosed : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ =
      Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ') :
    Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k ⥤
      Deformation.ArtinianLocalAlgCat.{u, u, u} Λ' k where
  obj B := rebaseArtinianAlgebraCanonical iΛ iΛ' hiΛ' hclosed B
  map f := rebaseArtinianHomCanonical iΛ iΛ' hiΛ' hclosed f
  map_id B := by
    apply Deformation.ArtinianLocalAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    rfl
  map_comp f g := by
    apply Deformation.ArtinianLocalAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    rfl

/-- Every deformation object over `Spec Λ ⟶ S` carries a compatible `Λ'`-algebra structure
over `S`. -/
private theorem deformationObject_rebaseMap
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
    [Algebra Λ k] [Algebra Λ' k] {S : Scheme.{u}}
    (iΛ : Spec (.of Λ) ⟶ S) (iΛ' : Spec (.of Λ') ⟶ S)
    (hiΛ' : IsOpenImmersion iΛ')
    {X : Type w} [Category X] (q : X ⥤ Over S) (x₀ : X)
    (hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hx₀' : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ'))
    (O : Deformation.Artin.DeformationObject iΛ q x₀ hx₀) :
    ∃ (g : Λ' →+* O.algebra),
      (∀ a, O.algebra.residueEquiv
        (residue O.algebra (g a)) = algebraMap Λ' k a) ∧
      Spec.map (CommRingCat.ofHom g) ≫ iΛ' =
        Spec.map (CommRingCat.ofHom (algebraMap Λ O.algebra)) ≫ iΛ := by
  have : IsOpenImmersion iΛ' := hiΛ'
  let f : Spec (.of O.algebra) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap Λ O.algebra)) ≫ iΛ
  have hclosed : Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap O.algebra)) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ' := by
    exact (deformationObject_closedMap iΛ q x₀ hx₀ O).trans
      (closedPointCharts_eq iΛ iΛ' q x₀ hx₀ hx₀')
  let xk : PrimeSpectrum k := ⟨⊥, inferInstance⟩
  let x : PrimeSpectrum O.algebra :=
    (Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap O.algebra))).base xk
  have hx : f x ∈ Set.range iΛ' := apply_mem_range_of_comp_eq _ _ _ _ hclosed xk
  refine ⟨artinianAlgebraMapOfOpenLift O.algebra iΛ' f x hx, ?_, ?_⟩
  · exact artinianAlgebraMapOfOpenLift_residue O.algebra iΛ' f x hx hclosed
  · rw [specMap_artinianAlgebraMapOfOpenLift]
    exact artinianSpecLift_fac O.algebra f iΛ' x hx

/-- A deformation object for the presentation `Spec Λ ⟶ S`, read as one for `Spec Λ' ⟶ S`. -/
noncomputable def rebaseDeformationObject
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
    [Algebra Λ k] [Algebra Λ' k] {S : Scheme.{u}}
    (iΛ : Spec (.of Λ) ⟶ S) (iΛ' : Spec (.of Λ') ⟶ S)
    (hiΛ' : IsOpenImmersion iΛ')
    {X : Type w} [Category X] (q : X ⥤ Over S) (x₀ : X)
    (hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hx₀' : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ'))
    (O : Deformation.Artin.DeformationObject iΛ q x₀ hx₀) :
    Deformation.Artin.DeformationObject iΛ' q x₀ hx₀' := by
  letI := hiΛ'
  let hclosed := closedPointCharts_eq iΛ iΛ' q x₀ hx₀ hx₀'
  let g := canonicalArtinianOpenLift iΛ iΛ' hiΛ' hclosed O.algebra
  have hg := canonicalArtinianOpenLift_residue iΛ iΛ' hiΛ' hclosed O.algebra
  let B' := rebaseArtinianAlgebra O.algebra g hg
  have hnew : Spec.map (CommRingCat.ofHom (algebraMap Λ' B')) ≫ iΛ' =
      Spec.map (CommRingCat.ofHom (algebraMap Λ O.algebra)) ≫ iΛ := by
    change Spec.map (CommRingCat.ofHom g) ≫ iΛ' = _
    exact canonicalArtinianOpenLift_fac iΛ iΛ' hiΛ' hclosed O.algebra
  let bnew := O.base.trans (congrArg Over.mk hnew.symm)
  refine ⟨B', O.point, O.arrow, bnew, ?_⟩
  have hdom : congrArg Over.left bnew = congrArg Over.left O.base := by
    simp [bnew]
  cases hdom
  have hres : Deformation.Artin.residueMap B' = Deformation.Artin.residueMap O.algebra := by
    ext a
    rfl
  have hresSpec : Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap O.algebra)) =
      Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap B')) :=
    congrArg (fun r => Spec.map (CommRingCat.ofHom r)) hres.symm
  exact O.arrow_base.trans hresSpec

/-- The map chosen by `deformationObject_rebaseMap` is the canonical open lift. -/
private theorem deformationObject_rebaseMap_eq_canonical
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
    [Algebra Λ k] [Algebra Λ' k] {S : Scheme.{u}}
    (iΛ : Spec (.of Λ) ⟶ S) (iΛ' : Spec (.of Λ') ⟶ S)
    (hiΛ' : IsOpenImmersion iΛ')
    {X : Type w} [Category X] (q : X ⥤ Over S) (x₀ : X)
    (hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hx₀' : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ'))
    (O : Deformation.Artin.DeformationObject iΛ q x₀ hx₀) :
    Classical.choose
        (deformationObject_rebaseMap iΛ iΛ' hiΛ' q x₀ hx₀ hx₀' O) =
      canonicalArtinianOpenLift iΛ iΛ' hiΛ'
        (closedPointCharts_eq iΛ iΛ' q x₀ hx₀ hx₀') O.algebra := by
  let hdata := deformationObject_rebaseMap iΛ iΛ' hiΛ' q x₀ hx₀ hx₀' O
  let f : Spec (.of O.algebra) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap Λ O.algebra)) ≫ iΛ
  have hclosed : Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap O.algebra)) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ' := by
    exact (deformationObject_closedMap iΛ q x₀ hx₀ O).trans
      (closedPointCharts_eq iΛ iΛ' q x₀ hx₀ hx₀')
  let xk : PrimeSpectrum k := ⟨⊥, inferInstance⟩
  let x : PrimeSpectrum O.algebra :=
    (Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap O.algebra))).base xk
  have hx : f x ∈ Set.range iΛ' := apply_mem_range_of_comp_eq _ _ _ _ hclosed xk
  have hsource := (Classical.choose_spec hdata).2
  have htarget : Spec.map (CommRingCat.ofHom
      (canonicalArtinianOpenLift iΛ iΛ' hiΛ'
        (closedPointCharts_eq iΛ iΛ' q x₀ hx₀ hx₀') O.algebra)) ≫ iΛ' = f := by
    change Spec.map (CommRingCat.ofHom
        (artinianAlgebraMapOfOpenLift O.algebra iΛ' f x hx)) ≫ iΛ' = f
    rw [specMap_artinianAlgebraMapOfOpenLift]
    exact artinianSpecLift_fac O.algebra f iΛ' x hx
  exact ringHom_eq_of_spec_comp_eq iΛ' (hsource.trans htarget.symm)

/-- The underlying algebra of a rebased deformation object is the canonical rebase of its
algebra. -/
theorem rebaseDeformationObject_algebra_eq_canonical
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
    [Algebra Λ k] [Algebra Λ' k] {S : Scheme.{u}}
    (iΛ : Spec (.of Λ) ⟶ S) (iΛ' : Spec (.of Λ') ⟶ S)
    (hiΛ' : IsOpenImmersion iΛ')
    {X : Type w} [Category X] (q : X ⥤ Over S) (x₀ : X)
    (hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hx₀' : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ'))
    (O : Deformation.Artin.DeformationObject iΛ q x₀ hx₀) :
    (rebaseDeformationObject iΛ iΛ' hiΛ' q x₀ hx₀ hx₀' O).algebra =
        (rebaseArtinianAlgebraCanonical iΛ iΛ' hiΛ'
        (closedPointCharts_eq iΛ iΛ' q x₀ hx₀ hx₀') O.algebra) := by
  unfold rebaseDeformationObject
  dsimp
  unfold rebaseArtinianAlgebraCanonical
  rfl

/-- Rebasing a deformation object does not change the underlying object of its base. -/
theorem rebaseDeformationObject_base_dom
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
    [Algebra Λ k] [Algebra Λ' k] {S : Scheme.{u}}
    (iΛ : Spec (.of Λ) ⟶ S) (iΛ' : Spec (.of Λ') ⟶ S)
    (hiΛ' : IsOpenImmersion iΛ')
    {X : Type w} [Category X] (q : X ⥤ Over S) (x₀ : X)
    (hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hx₀' : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ'))
    (O : Deformation.Artin.DeformationObject iΛ q x₀ hx₀) :
    congrArg Over.left (rebaseDeformationObject iΛ iΛ' hiΛ' q x₀ hx₀ hx₀' O).base =
      congrArg Over.left O.base := by
  unfold rebaseDeformationObject
  simp

/-- The chosen rebase maps are natural along a morphism of deformation objects. -/
private theorem rebaseMaps_natural
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
    [Algebra Λ k] [Algebra Λ' k] {S : Scheme.{u}}
    (iΛ : Spec (.of Λ) ⟶ S) (iΛ' : Spec (.of Λ') ⟶ S)
    (hiΛ' : IsOpenImmersion iΛ')
    {X : Type w} [Category X] (q : X ⥤ Over S) (x₀ : X)
    (hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hx₀' : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ'))
    {a b : Deformation.Artin.DeformationObject iΛ q x₀ hx₀}
    (m : Deformation.Artin.DeformationMorphism iΛ q x₀ hx₀ a b) :
    CommRingCat.ofHom
        (m.ringHom.hom.toRingHom.comp
          (Classical.choose (deformationObject_rebaseMap iΛ iΛ' hiΛ' q x₀ hx₀ hx₀' a))) =
      CommRingCat.ofHom
        (Classical.choose (deformationObject_rebaseMap iΛ iΛ' hiΛ' q x₀ hx₀ hx₀' b)) := by
  let ha := deformationObject_rebaseMap iΛ iΛ' hiΛ' q x₀ hx₀ hx₀' a
  let hb := deformationObject_rebaseMap iΛ iΛ' hiΛ' q x₀ hx₀ hx₀' b
  let ga := Classical.choose ha
  let gb := Classical.choose hb
  have hfa := (Classical.choose_spec ha).2
  have hfb := (Classical.choose_spec hb).2
  have hcomp : Spec.map (CommRingCat.ofHom (m.ringHom.hom.toRingHom.comp ga)) =
      Spec.map (CommRingCat.ofHom m.ringHom.hom.toRingHom) ≫
        Spec.map (CommRingCat.ofHom ga) := by
    rw [CommRingCat.ofHom_comp, ← Spec.map_comp]
  have hfactor : Spec.map (CommRingCat.ofHom (m.ringHom.hom.toRingHom.comp ga)) ≫ iΛ' =
      Spec.map (CommRingCat.ofHom gb) ≫ iΛ' := by
    calc
      _ = Spec.map (CommRingCat.ofHom m.ringHom.hom.toRingHom) ≫
          Spec.map (CommRingCat.ofHom ga) ≫ iΛ' := by rw [hcomp, Category.assoc]
      _ = Spec.map (CommRingCat.ofHom m.ringHom.hom.toRingHom) ≫
          (Spec.map (CommRingCat.ofHom (algebraMap Λ a.algebra)) ≫ iΛ) := by rw [hfa]
      _ = Spec.map (CommRingCat.ofHom (algebraMap Λ b.algebra)) ≫ iΛ :=
        deformationMorphism_baseMap iΛ q x₀ hx₀ m
      _ = Spec.map (CommRingCat.ofHom gb) ≫ iΛ' := hfb.symm
  exact congrArg CommRingCat.ofHom (ringHom_eq_of_spec_comp_eq iΛ' hfactor)

/-- Rebasing to `Λ'` and back to `Λ` returns the original structure map. -/
theorem canonicalOpenLift_roundtrip
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
    [Algebra Λ k] [Algebra Λ' k] {S : Scheme.{u}}
    (iΛ : Spec (.of Λ) ⟶ S) (iΛ' : Spec (.of Λ') ⟶ S)
    (hiΛ : IsOpenImmersion iΛ) (hiΛ' : IsOpenImmersion iΛ')
    (hclosed : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ =
      Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ')
    (B : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k) :
    canonicalArtinianOpenLift iΛ' iΛ hiΛ hclosed.symm
        (rebaseArtinianAlgebraCanonical iΛ iΛ' hiΛ' hclosed B) =
      algebraMap Λ B := by
  exact (algebraMap_eq_canonicalArtinianOpenLift
    (rebaseArtinianAlgebraCanonical iΛ iΛ' hiΛ' hclosed B) iΛ' iΛ hiΛ hclosed.symm
    (algebraMap Λ B) (canonicalArtinianOpenLift_fac iΛ iΛ' hiΛ' hclosed B).symm).symm

/-- The morphism of rebased deformation objects induced by a morphism of deformation objects. -/
noncomputable def rebaseDeformationMorphism
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
    [Algebra Λ k] [Algebra Λ' k] {S : Scheme.{u}}
    (iΛ : Spec (.of Λ) ⟶ S) (iΛ' : Spec (.of Λ') ⟶ S)
    (hiΛ' : IsOpenImmersion iΛ')
    {X : Type w} [Category X] (q : X ⥤ Over S) (x₀ : X)
    (hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hx₀' : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ'))
    {a b : Deformation.Artin.DeformationObject iΛ q x₀ hx₀}
    (m : Deformation.Artin.DeformationMorphism iΛ q x₀ hx₀ a b) :
    Deformation.Artin.DeformationMorphism iΛ' q x₀ hx₀'
      (rebaseDeformationObject iΛ iΛ' hiΛ' q x₀ hx₀ hx₀' a)
      (rebaseDeformationObject iΛ iΛ' hiΛ' q x₀ hx₀ hx₀' b) := by
  let hclosed := closedPointCharts_eq iΛ iΛ' q x₀ hx₀ hx₀'
  let ga := canonicalArtinianOpenLift iΛ iΛ' hiΛ' hclosed a.algebra
  let gb := canonicalArtinianOpenLift iΛ iΛ' hiΛ' hclosed b.algebra
  let A' := (rebaseDeformationObject iΛ iΛ' hiΛ' q x₀ hx₀ hx₀' a).algebra
  let B' := (rebaseDeformationObject iΛ iΛ' hiΛ' q x₀ hx₀ hx₀' b).algebra
  let fA : Spec (.of a.algebra) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap Λ a.algebra)) ≫ iΛ
  let fB : Spec (.of b.algebra) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap Λ b.algebra)) ≫ iΛ
  let xA := Classical.choose (canonicalArtinianOpenLift_point iΛ iΛ' hclosed a.algebra)
  have hxA := Classical.choose_spec
    (canonicalArtinianOpenLift_point iΛ iΛ' hclosed a.algebra)
  let xB := Classical.choose (canonicalArtinianOpenLift_point iΛ iΛ' hclosed b.algebra)
  have hxB := Classical.choose_spec
    (canonicalArtinianOpenLift_point iΛ iΛ' hclosed b.algebra)
  have hbase : Spec.map (CommRingCat.ofHom m.ringHom.hom.toRingHom) ≫ fA = fB :=
    deformationMorphism_baseMap iΛ q x₀ hx₀ m
  let liftA := artinianAlgebraMapOfOpenLift a.algebra iΛ' fA xA hxA
  let liftB := artinianAlgebraMapOfOpenLift b.algebra iΛ' fB xB hxB
  have hnat := artinianAlgebraMapOfOpenLift_natural iΛ' fA xA hxA fB xB hxB
    m.ringHom hbase
  have hnat' : CommRingCat.ofHom (m.ringHom.hom.toRingHom.comp liftA) =
      CommRingCat.ofHom liftB := by
    rwa [CommRingCat.ofHom_comp]
  have hring₀ := congrArg CommRingCat.Hom.hom hnat'
  have hga : liftA = ga := artinianAlgebraMapOfOpenLift_eq_canonical
    a.algebra iΛ iΛ' hiΛ' hclosed xA hxA
  have hgb : liftB = gb := artinianAlgebraMapOfOpenLift_eq_canonical
    b.algebra iΛ iΛ' hiΛ' hclosed xB hxB
  have hring : m.ringHom.hom.toRingHom.comp ga = gb := by
    rwa [← hga, ← hgb]
  let ringMap : A' →ₐ[Λ'] B' := AlgHom.mk m.ringHom.hom.toRingHom (by
    intro r
    change m.ringHom.hom.toRingHom (ga r) = gb r
    exact congrArg (fun f : Λ' →+* b.algebra => f r) hring)
  have haDom := rebaseDeformationObject_base_dom
    iΛ iΛ' hiΛ' q x₀ hx₀ hx₀' a
  have hbDom := rebaseDeformationObject_base_dom
    iΛ iΛ' hiΛ' q x₀ hx₀ hx₀' b
  let ringHom' : Deformation.ArtinianLocalAlgCat.Hom A' B' := {
    hom := ringMap
    isLocal := m.ringHom.isLocal
    residue_comm := by
      intro z
      change b.algebra.residueEquiv
          (residue b.algebra (m.ringHom.hom z)) =
        a.algebra.residueEquiv (residue a.algebra z)
      exact m.ringHom.residue_comm z
  }
  refine {
    ringHom := ringHom'
    arrow := m.arrow
    triangle := m.triangle
    arrow_base := ?_
  }
  cases haDom
  cases hbDom
  exact m.arrow_base

/-- Rebasing a morphism of deformation objects does not change its underlying ring map. -/
private theorem rebaseDeformationMorphism_ringHom
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
    [Algebra Λ k] [Algebra Λ' k] {S : Scheme.{u}}
    (iΛ : Spec (.of Λ) ⟶ S) (iΛ' : Spec (.of Λ') ⟶ S)
    (hiΛ' : IsOpenImmersion iΛ') {X : Type w} [Category X]
    (q : X ⥤ Over S) (x₀ : X)
    (hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hx₀' : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ'))
    {a b : Deformation.Artin.DeformationObject iΛ q x₀ hx₀}
    (m : Deformation.Artin.DeformationMorphism iΛ q x₀ hx₀ a b) :
    (rebaseDeformationMorphism iΛ iΛ' hiΛ' q x₀ hx₀ hx₀' m).ringHom.hom.toRingHom =
      m.ringHom.hom.toRingHom := by
  rfl

/-- Rebasing a morphism of deformation objects does not change its underlying arrow. -/
theorem rebaseDeformationMorphism_arrow_eq
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
    [Algebra Λ k] [Algebra Λ' k] {S : Scheme.{u}}
    (iΛ : Spec (.of Λ) ⟶ S) (iΛ' : Spec (.of Λ') ⟶ S)
    (hiΛ' : IsOpenImmersion iΛ') {X : Type w} [Category X]
    (q : X ⥤ Over S) (x₀ : X)
    (hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hx₀' : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ'))
    {a b : Deformation.Artin.DeformationObject iΛ q x₀ hx₀}
    (m : Deformation.Artin.DeformationMorphism iΛ q x₀ hx₀ a b) :
    (rebaseDeformationMorphism iΛ iΛ' hiΛ' q x₀ hx₀ hx₀' m).arrow = m.arrow := by
  rfl

/-- A morphism of deformation objects transported along equalities of its source and target. -/
def transportDeformationMorphism
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}} {X : Type w} [Category X]
    {iΛ : Spec (.of Λ) ⟶ S} {q : X ⥤ Over S} {x₀ : X}
    {hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    {a a' b b' : Deformation.Artin.DeformationObject iΛ q x₀ hx₀}
    (ha : a' = a) (hb : b' = b)
    (m : Deformation.Artin.DeformationMorphism iΛ q x₀ hx₀ a b) :
    Deformation.Artin.DeformationMorphism iΛ q x₀ hx₀ a' b' :=
  hb.symm ▸ ha.symm ▸ m

/-- The ring map of a transported morphism is the original one conjugated by `eqToHom`. -/
theorem transportDeformationMorphism_ringHom
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}} {X : Type w} [Category X]
    {iΛ : Spec (.of Λ) ⟶ S} {q : X ⥤ Over S} {x₀ : X}
    {hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    {a a' b b' : Deformation.Artin.DeformationObject iΛ q x₀ hx₀}
    (ha : a' = a) (hb : b' = b)
    (m : Deformation.Artin.DeformationMorphism iΛ q x₀ hx₀ a b) :
    (transportDeformationMorphism ha hb m).ringHom =
      eqToHom (congrArg (fun z : Deformation.Artin.DeformationObject iΛ q x₀ hx₀ => z.algebra) ha) ≫
        m.ringHom ≫
          eqToHom (congrArg
            (fun z : Deformation.Artin.DeformationObject iΛ q x₀ hx₀ => z.algebra) hb).symm := by
  cases ha
  cases hb
  simp [transportDeformationMorphism]

/-- The arrow of a transported morphism is the original one conjugated by `eqToHom`. -/
theorem transportDeformationMorphism_arrow
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}} {X : Type w} [Category X]
    {iΛ : Spec (.of Λ) ⟶ S} {q : X ⥤ Over S} {x₀ : X}
    {hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    {a a' b b' : Deformation.Artin.DeformationObject iΛ q x₀ hx₀}
    (ha : a' = a) (hb : b' = b)
    (m : Deformation.Artin.DeformationMorphism iΛ q x₀ hx₀ a b) :
    (transportDeformationMorphism ha hb m).arrow =
      eqToHom (congrArg (fun z : Deformation.Artin.DeformationObject iΛ q x₀ hx₀ => z.point) hb) ≫
        m.arrow ≫
          eqToHom (congrArg
            (fun z : Deformation.Artin.DeformationObject iΛ q x₀ hx₀ => z.point) ha).symm := by
  cases ha
  cases hb
  simp [transportDeformationMorphism]

/-- `eqToHom h ≫ eqToHom h.symm` is the identity. -/
theorem eqToHom_comp_symm
    {Y : Type*} [Category Y] {a b : Y} (h : a = b) :
    eqToHom h ≫ eqToHom h.symm = 𝟙 a := by
  simp

/-- `eqToHom h.symm ≫ eqToHom h` is the identity. -/
private theorem eqToHom_symm_comp
    {Y : Type*} [Category Y] {a b : Y} (h : a = b) :
    eqToHom h.symm ≫ eqToHom h = 𝟙 b := by
  simp

/-- On underlying algebra maps, `eqToHom h.symm` and `eqToHom h` compose to the identity. -/
private theorem eqToHom_algHom_comp
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {A B : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k} (h : A = B) :
    (eqToHom h.symm).hom.comp (eqToHom h).hom = AlgHom.id Λ A := by
  have hh := congrArg Deformation.ArtinianLocalAlgCat.Hom.hom
    (eqToHom_comp_symm h)
  exact hh

/-- On underlying algebra maps, `eqToHom h` and `eqToHom h.symm` compose to the identity. -/
private theorem eqToHom_algHom_symm_comp
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {A B : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k} (h : A = B) :
    (eqToHom h).hom.comp (eqToHom h.symm).hom = AlgHom.id Λ B := by
  exact eqToHom_algHom_comp h.symm

/-- Two `eqToHom`-conjugated morphisms compose to the conjugate of their composite. -/
theorem eqToHom_conjugate_comp
    {Y : Type*} [Category Y]
    {A A' B B' C C' : Y} (hA : A' = A) (hB : B' = B) (hC : C' = C)
    (f : A ⟶ B) (g : B ⟶ C) :
    (eqToHom hA ≫ f ≫ eqToHom hB.symm) ≫
        (eqToHom hB ≫ g ≫ eqToHom hC.symm) =
      eqToHom hA ≫ (f ≫ g) ≫ eqToHom hC.symm := by
  calc
    _ = eqToHom hA ≫ f ≫
        (eqToHom hB.symm ≫ eqToHom hB) ≫ g ≫ eqToHom hC.symm := by
      simp [Category.assoc]
    _ = _ := by rw [eqToHom_symm_comp hB]; simp [Category.assoc]

/-- An `eqToHom` conjugate nested inside another collapses to a single conjugate. -/
theorem eqToHom_squeeze
    {Y : Type*} [Category Y] {W X X' Y' Z' Z : Y}
    (h₁ : W = X) (h₂ : X = X') (g : X' ⟶ Y') (h₃ : Y' = Z') (h₄ : Z' = Z)
    (h₅ : W = X') (h₆ : Y' = Z) :
    eqToHom h₁ ≫ (eqToHom h₂ ≫ g ≫ eqToHom h₃) ≫ eqToHom h₄ =
      (eqToHom h₅ ≫ g) ≫ eqToHom h₆ := by
  cases h₁
  cases h₂
  cases h₃
  cases h₄
  simp

/-- Two morphisms of deformation objects agreeing on ring maps and on arrows are equal. -/
theorem deformationMorphism_ext_of_ringMap
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}} {X : Type w} [Category X]
    {iΛ : Spec (.of Λ) ⟶ S} {q : X ⥤ Over S} {x₀ : X}
    {hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    {a b : Deformation.Artin.DeformationObject iΛ q x₀ hx₀}
    {f g : Deformation.Artin.DeformationMorphism iΛ q x₀ hx₀ a b}
    (hr : ∀ x, f.ringHom.hom x = g.ringHom.hom x)
    (ha : f.arrow = g.arrow) : f = g := by
  have hhom : f.ringHom.hom = g.ringHom.hom := AlgHom.ext hr
  have hring : f.ringHom = g.ringHom :=
    Deformation.ArtinianLocalAlgCat.hom_ext hhom
  cases f with
  | mk fr fa ft fb =>
    cases g with
    | mk gr ga gt gb => simp_all

end AlgebraicGeometry.Stack

end
