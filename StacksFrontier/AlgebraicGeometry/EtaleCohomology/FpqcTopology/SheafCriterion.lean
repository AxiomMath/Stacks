module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Sites.SheafQuasiCompact
public import Mathlib.CategoryTheory.Sites.EqualizerSheafCondition
public import Mathlib.CategoryTheory.Sites.Over
public import StacksCore.Tactic.StacksAttribute

/-!
# Fpqc sheaves from Zariski descent and affine faithfully flat descent

A presheaf on the category of schemes over a base `S` is an fpqc sheaf exactly when it is a
Zariski sheaf and satisfies descent for every faithfully flat morphism of affine schemes over
`S`. The hard direction reduces the fpqc sheaf condition, which quantifies over arbitrary
coverings, to these two special cases.

## Main results

* `Stacks.EtaleCohomology.isSheaf_fpqc_iff_zariski_and_affine_singleton` is the fpqc sheaf
  criterion.

## Implementation notes

The reduction goes through the *total presheaf* of a presheaf `F` on `Over S`: the presheaf on
all schemes whose sections over `X` are pairs consisting of a morphism `φ : X ⟶ S` and a section
of `F` over `Over.mk φ`. Projecting to the first component is a morphism to the representable
presheaf of `S`, and the sheaf condition for `F` relative to a sieve of `Over S` is equivalent
to the sheaf condition for the total presheaf relative to the image sieve, because the
representable presheaf of `S` is already an fpqc sheaf. Descent for arbitrary fpqc coverings is
then supplied by Mathlib's reduction of the sheaf condition for a quasi-compact topology to the
Zariski condition together with affine singleton coverings.

An affine scheme over `S` is specified by its structure morphism `g` to `S`. The singleton
presieve of the induced morphism in `Over S` expresses precisely the equalizer condition for
`Spec(B) → Spec(A)`: its two comparison maps are restriction along the projections from
`Spec(B ⊗_A B)`.

## References

* [Stacks Project, Tag 03O1](https://stacks.math.columbia.edu/tag/03O1)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite

universe u v

namespace Stacks.EtaleCohomology

/-- Flatness of morphisms of schemes, packaged as a morphism property. The ascription is what
lets instance search see the flatness instances of `AlgebraicGeometry.Scheme.propQCTopology` and
of `AlgebraicGeometry.isSheaf_type_propQCTopology_iff`, whose arguments are morphism properties
rather than universe-polymorphic predicates. -/
private abbrev flatProperty : MorphismProperty Scheme.{u} := @Flat

/-- Two sections of a presheaf on `Over S` transported along morphisms with equal underlying
scheme morphisms agree as elements of the total space of sections. -/
private lemma totalSigmaMkEq {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type v}
    {V W : Scheme.{u}} {φ : W ⟶ S} (s : F.obj (op (Over.mk φ)))
    {ψ ψ' : V ⟶ S} (e : Over.mk ψ ⟶ Over.mk φ) (e' : Over.mk ψ' ⟶ Over.mk φ)
    (h : e.left = e'.left) :
    (⟨ψ, F.map e.op s⟩ : Σ χ : V ⟶ S, F.obj (op (Over.mk χ))) = ⟨ψ', F.map e'.op s⟩ := by
  have h1 := Over.w e
  have h2 := Over.w e'
  simp only [Over.mk_hom, Over.mk_left] at h1 h2
  have hψ : ψ = ψ' := by rw [← h1, ← h2, h]
  subst hψ
  rw [Over.OverMorphism.ext h]

/-- The total presheaf of a presheaf `F` on `Over S`: its sections over a scheme `X` are the
pairs consisting of a morphism `φ : X ⟶ S` and a section of `F` over `Over.mk φ`. -/
private def totalPresheaf {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type v) :
    Schemeᵒᵖ ⥤ Type (max u v) where
  obj X := Σ φ : X.unop ⟶ S, F.obj (op (Over.mk φ))
  map {X Y} (f : X ⟶ Y) :
      (Σ φ : X.unop ⟶ S, F.obj (op (Over.mk φ))) ⟶
        (Σ φ : Y.unop ⟶ S, F.obj (op (Over.mk φ))) := ↾fun p =>
    ⟨f.unop ≫ p.1,
      F.map (Over.homMk f.unop rfl : Over.mk (f.unop ≫ p.1) ⟶ Over.mk p.1).op p.2⟩
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro p
    rcases p with ⟨φ, s⟩
    change (⟨(𝟙 X).unop ≫ φ,
      F.map (Over.homMk (𝟙 X).unop rfl :
        Over.mk ((𝟙 X).unop ≫ φ) ⟶ Over.mk φ).op s⟩ :
          Σ ψ : X.unop ⟶ S, F.obj (op (Over.mk ψ))) = ⟨φ, s⟩
    have h := totalSigmaMkEq s
      (Over.homMk (𝟙 X).unop rfl :
        Over.mk ((𝟙 X).unop ≫ φ) ⟶ Over.mk φ)
      (𝟙 (Over.mk φ)) (by simp [unop_id])
    simpa [unop_id] using h
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro p
    rcases p with ⟨φ, s⟩
    change (⟨(f ≫ g).unop ≫ φ,
      F.map (Over.homMk (f ≫ g).unop rfl :
        Over.mk ((f ≫ g).unop ≫ φ) ⟶ Over.mk φ).op s⟩ :
          Σ ψ : _ ⟶ S, F.obj (op (Over.mk ψ))) =
      ⟨g.unop ≫ f.unop ≫ φ,
        F.map (Over.homMk g.unop rfl :
          Over.mk (g.unop ≫ f.unop ≫ φ) ⟶ Over.mk (f.unop ≫ φ)).op
          (F.map (Over.homMk f.unop rfl :
            Over.mk (f.unop ≫ φ) ⟶ Over.mk φ).op s)⟩
    have hpair := totalSigmaMkEq s
      (Over.homMk (f ≫ g).unop rfl :
        Over.mk ((f ≫ g).unop ≫ φ) ⟶ Over.mk φ)
      ((Over.homMk g.unop rfl : Over.mk (g.unop ≫ f.unop ≫ φ) ⟶
        Over.mk (f.unop ≫ φ)) ≫
        (Over.homMk f.unop rfl : Over.mk (f.unop ≫ φ) ⟶ Over.mk φ)) (by simp)
    simpa [Functor.map_comp, ConcreteCategory.comp_apply] using hpair

/-- The projection of the total presheaf onto the first component, a morphism to the
representable presheaf of the base, lifted to the universe of the sections of `F`. -/
private def totalToYoneda {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type v) :
    totalPresheaf F ⟶ yoneda.obj S ⋙ uliftFunctor.{max u v} where
  app _ := ↾fun p => ULift.up p.1
  naturality {X Y} x := by
    apply ConcreteCategory.hom_ext
    intro p
    change ULift.up (x.unop ≫ p.1) = ULift.up (x.unop ≫ p.1)
    rfl

/-- The section of `F` over an object `A` of `Over S` underlying a section of the total presheaf
whose first component is the structure morphism of `A`. -/
private def totalSection {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type v}
    {A : Over S} (p : (totalPresheaf F).obj (op A.left))
    (h : p.1 = A.hom) : F.obj (op A) :=
  F.map (Over.homMk (𝟙 A.left) (by simpa using h) : A ⟶ Over.mk p.1).op p.2

/-- Restricting a section of the total presheaf whose first component is a structure morphism
again produces one whose first component is a structure morphism. -/
private lemma totalMapFst {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type v}
    {A B : Over S} (b : B ⟶ A) {p : (totalPresheaf F).obj (op A.left)}
    (h : p.1 = A.hom) {q : (totalPresheaf F).obj (op B.left)}
    (hq : (totalPresheaf F).map b.left.op p = q) : q.1 = B.hom := by
  have hfst : b.left ≫ p.1 = q.1 := by
    have hh := congrArg (fun z : (totalPresheaf F).obj (op B.left) => z.1) hq
    change b.left ≫ p.1 = q.1 at hh
    exact hh
  rw [← hfst, h]
  exact Over.w b

/-- Reassembling a section of the total presheaf from its underlying section of `F` recovers it. -/
private lemma totalMkSection {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type v}
    {A : Over S} (p : (totalPresheaf F).obj (op A.left)) (h : p.1 = A.hom) :
    (⟨A.hom, totalSection p h⟩ : (totalPresheaf F).obj (op A.left)) = p := by
  have h1 := totalSigmaMkEq p.2
    (Over.homMk (𝟙 A.left) (by simpa using h) : Over.mk A.hom ⟶ Over.mk p.1)
    (𝟙 (Over.mk p.1)) rfl
  have h2 : (⟨p.1, F.map (𝟙 (Over.mk p.1)).op p.2⟩ :
      (totalPresheaf F).obj (op A.left)) = p := by
    change (⟨p.1, F.map (𝟙 (Over.mk p.1)).op p.2⟩ :
      Σ ψ : A.left ⟶ S, F.obj (op (Over.mk ψ))) = p
    cases p
    simp
  exact h1.trans h2

/-- Restriction in the total presheaf of a section built from a section of `F` is the section
built from its restriction in `F`. -/
private lemma totalMapMk {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type v}
    {A B : Over S} (b : B ⟶ A) (t : F.obj (op A)) :
    (totalPresheaf F).map b.left.op (⟨A.hom, t⟩ :
      (totalPresheaf F).obj (op A.left)) = ⟨B.hom, F.map b.op t⟩ := by
  change (⟨b.left ≫ A.hom,
    F.map (Over.homMk b.left rfl : Over.mk (b.left ≫ A.hom) ⟶ Over.mk A.hom).op t⟩ :
      (totalPresheaf F).obj (op B.left)) = ⟨B.hom, F.map b.op t⟩
  exact totalSigmaMkEq t
    (Over.homMk b.left rfl : Over.mk (b.left ≫ A.hom) ⟶ Over.mk A.hom) b rfl

/-- Two sections of `F` over the same object of `Over S` that agree in the total presheaf are
equal. -/
private lemma totalSigmaSndInj {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type v}
    {V : Scheme.{u}} {φ : V ⟶ S} {s t : F.obj (op (Over.mk φ))}
    (hst : (⟨φ, s⟩ : Σ ψ : V ⟶ S, F.obj (op (Over.mk ψ))) = ⟨φ, t⟩) : s = t := by
  simpa using hst

/-- Taking the underlying section of `F` commutes with restriction. -/
private lemma totalMapSection {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type v}
    {A B : Over S} (b : B ⟶ A) {p : (totalPresheaf F).obj (op A.left)}
    (h : p.1 = A.hom) {q : (totalPresheaf F).obj (op B.left)}
    (hq : (totalPresheaf F).map b.left.op p = q) :
    F.map b.op (totalSection p h) = totalSection q (totalMapFst b h hq) :=
  totalSigmaSndInj <| (totalMapMk b (totalSection p h)).symm.trans <|
    ((congrArg (fun z => (totalPresheaf F).map b.left.op z) (totalMkSection p h)).trans hq).trans
      (totalMkSection q (totalMapFst b h hq)).symm

/-- A morphism of `Over S` with underlying morphism in a sieve lies in the corresponding sieve of
`Over S`. -/
private lemma overEquiv_symm_arrows_homMk {S : Scheme.{u}} {A : Over S} (R : Sieve A.left)
    {Y : Scheme.{u}} {f : Y ⟶ A.left} (hf : R.arrows f) :
    ((Sieve.overEquiv A).symm R).arrows (Over.homMk f rfl : Over.mk (f ≫ A.hom) ⟶ A) :=
  (Sieve.overEquiv_symm_iff (Y := A) R _).2 hf

/-- The representable presheaf of the base, lifted to a larger universe, satisfies the sheaf
condition for every covering sieve of a subcanonical topology. -/
private lemma isSheafFor_yoneda_uliftFunctor {S : Scheme.{u}} (J : GrothendieckTopology Scheme.{u})
    [J.Subcanonical] {V : Scheme.{u}} {R : Sieve V} (hR : R ∈ J V) :
    Presieve.IsSheafFor (yoneda.obj S ⋙ uliftFunctor.{max u v}) R.arrows :=
  Presieve.isSheafFor_comp_uliftFunctor_iff.2 <|
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
      (yoneda.obj S)).isSheafFor R.arrows (by simpa using hR)

/-- The sieve generated by the singleton presieve of a faithfully flat morphism is an fpqc
covering. -/
private lemma generate_singleton_mem_fpqcTopology {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    [Surjective f] [QuasiCompact f] : Sieve.generate (.singleton f) ∈ Scheme.fpqcTopology Y := by
  rw [Scheme.fpqcTopology_eq_propQCTopology]
  exact Precoverage.generate_mem_toGrothendieck (Scheme.Hom.singleton_mem_fpqcPrecoverage f)

/-- The total presheaf satisfies the sheaf condition for a sieve as soon as the representable
presheaf of the base does and `F` satisfies it for the corresponding sieve of `Over S`. -/
private lemma total_isSheafFor {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type v}
    {V : Scheme.{u}}
    (R : Sieve V) (hS : Presieve.IsSheafFor
      (yoneda.obj S ⋙ uliftFunctor.{max u v}) R.arrows)
    (hF : ∀ φ : V ⟶ S, Presieve.IsSheafFor F
      ((Sieve.overEquiv (Over.mk φ)).symm R).arrows) :
    Presieve.IsSheafFor (totalPresheaf F) R.arrows := by
  intro x hx
  let x' := x.map (totalToYoneda F)
  have hx' := hx.map (totalToYoneda F)
  obtain ⟨φ', hφ, hφuniq⟩ := hS x' hx'
  let φ : V ⟶ S := φ'.down
  have key : ∀ {A : Over S} (a : A ⟶ Over.mk φ) (ha : R.arrows a.left),
      (x a.left ha).1 = A.hom := by
    intro A a ha
    have hφa : (x a.left ha).1 = a.left ≫ φ := (congrArg ULift.down (hφ a.left ha)).symm
    exact hφa.trans (Over.w a)
  obtain ⟨t, ht, htuniq⟩ := hF φ
    (fun _ a ha => by
      have ha' : R.arrows a.left :=
      (Sieve.overEquiv_symm_iff (Y := Over.mk φ) R a).mp ha
      exact totalSection (x a.left ha') (key a ha'))
    (by
      intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ hcomm
      have h₁' : R.arrows f₁.left :=
        (Sieve.overEquiv_symm_iff (Y := Over.mk φ) R f₁).mp h₁
      have h₂' : R.arrows f₂.left :=
        (Sieve.overEquiv_symm_iff (Y := Over.mk φ) R f₂).mp h₂
      let p₁ := x f₁.left h₁'
      let p₂ := x f₂.left h₂'
      let q₁ := (totalPresheaf F).map g₁.left.op p₁
      let q₂ := (totalPresheaf F).map g₂.left.op p₂
      have hq : q₁ = q₂ := hx g₁.left g₂.left h₁' h₂'
        (congrArg Over.Hom.left hcomm)
      have hp₁ : p₁.1 = Y₁.hom := key f₁ h₁'
      have hp₂ : p₂.1 = Y₂.hom := key f₂ h₂'
      have hq₁' : q₁.1 = Z.hom := totalMapFst g₁ hp₁ rfl
      have hq₂' : q₂.1 = Z.hom := totalMapFst g₂ hp₂ rfl
      have h₁sec := totalMapSection g₁ hp₁ rfl
      have h₂sec := totalMapSection g₂ hp₂ rfl
      have hpairs : (⟨Z.hom, totalSection q₁ hq₁'⟩ :
          (totalPresheaf F).obj (op Z.left)) = ⟨Z.hom, totalSection q₂ hq₂'⟩ :=
        (totalMkSection q₁ hq₁').trans (hq.trans (totalMkSection q₂ hq₂').symm)
      exact h₁sec.trans ((totalSigmaSndInj hpairs).trans h₂sec.symm))
  refine ⟨⟨φ, t⟩, ?_, ?_⟩
  · intro Y f hf
    let b : Over.mk (f ≫ φ) ⟶ Over.mk φ := Over.homMk f rfl
    have hb := overEquiv_symm_arrows_homMk (A := Over.mk φ) R hf
    exact (totalMapMk b t).trans
      ((congrArg (fun s => (⟨f ≫ φ, s⟩ :
        (totalPresheaf F).obj (op Y))) (ht b hb)).trans
          (totalMkSection (A := Over.mk (f ≫ φ)) (x f hf) (key b hf)))
  · intro p hp
    have hψ : p.1 = φ := congrArg ULift.down (hφuniq _ (hp.map (totalToYoneda F)))
    have htuniq' := htuniq (totalSection p hψ) fun _ a ha =>
      totalMapSection a hψ (hp a.left ((Sieve.overEquiv_symm_iff (Y := Over.mk φ) R a).mp ha))
    exact (totalMkSection (A := Over.mk φ) p hψ).symm.trans
      (congrArg (fun s => (⟨φ, s⟩ : (totalPresheaf F).obj (op V))) htuniq')

/-- The total presheaf satisfies the sheaf condition for the singleton covering of a faithfully
flat morphism of affine schemes whenever `F` satisfies it for each of its lifts to `Over S`. -/
private lemma total_isSheafFor_affineSingleton {S : Scheme.{u}}
    (F : (Over S)ᵒᵖ ⥤ Type v) {R T : CommRingCat.{u}}
    (f : R ⟶ T) [Flat (Spec.map f)] [Surjective (Spec.map f)]
    (hF : ∀ g : Spec R ⟶ S, Presieve.IsSheafFor F (.singleton
      (Over.homMk (Spec.map f) rfl :
        Over.mk (Spec.map f ≫ g) ⟶ Over.mk g))) :
    Presieve.IsSheafFor (totalPresheaf F) (.singleton (Spec.map f)) := by
  rw [Presieve.isSheafFor_iff_generate]
  let R' : Sieve (Spec R) := Sieve.generate (.singleton (Spec.map f))
  apply total_isSheafFor R'
    (isSheafFor_yoneda_uliftFunctor _ (generate_singleton_mem_fpqcTopology (Spec.map f)))
  intro g
  have hFgen := (Presieve.isSheafFor_iff_generate _).1 (hF g)
  have hQ : (Sieve.overEquiv (Over.mk g)).symm R' =
      Sieve.generate (.singleton (Over.homMk (Spec.map f) rfl :
        Over.mk (Spec.map f ≫ g) ⟶ Over.mk g)) := by
    have hright : Sieve.overEquiv (Over.mk g)
        (Sieve.generate (.singleton (Over.homMk (Spec.map f) rfl :
          Over.mk (Spec.map f ≫ g) ⟶ Over.mk g))) = R' := by
      change (Sieve.generate (.singleton (Over.homMk (Spec.map f) rfl :
        Over.mk (Spec.map f ≫ g) ⟶ Over.mk g))).functorPushforward (Over.forget S) = R'
      rw [← Sieve.generate_map_eq_functorPushforward]
      simp [R']
    rw [← hright, OrderIso.symm_apply_apply]
  rw [hQ]
  exact hFgen

/-- The total presheaf of a sheaf on `Over S` for the localized topology is a sheaf for the
topology itself, provided the representable presheaf of the base is. -/
private lemma total_isSheaf_of_isSheaf {S : Scheme.{u}} (J : GrothendieckTopology Scheme.{u})
    (F : (Over S)ᵒᵖ ⥤ Type v)
    (hS : Presieve.IsSheaf J (yoneda.obj S ⋙ uliftFunctor.{max u v}))
    (hF : Presieve.IsSheaf (J.over S) F) : Presieve.IsSheaf J (totalPresheaf F) := by
  intro V R hR
  exact total_isSheafFor R (hS R hR) fun φ =>
    hF.isSheafFor _ (by simpa using J.overEquiv_symm_mem_over (Over.mk φ) R hR)

/-- Conversely, the sheaf condition for the total presheaf relative to a sieve implies the sheaf
condition for `F` relative to the corresponding sieve of `Over S`. -/
private lemma fiber_isSheafFor_of_total {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type v}
    {A : Over S} (R : Sieve A.left)
    (hBase : Presieve.IsSheafFor
      (yoneda.obj S ⋙ uliftFunctor.{max u v}) R.arrows)
    (hTotal : Presieve.IsSheafFor (totalPresheaf F) R.arrows) :
    Presieve.IsSheafFor F ((Sieve.overEquiv A).symm R).arrows := by
  intro x hx
  let xTotal : Presieve.FamilyOfElements (totalPresheaf F) R.arrows := fun _ f hf => by
    exact ⟨f ≫ A.hom, x _ (overEquiv_symm_arrows_homMk R hf)⟩
  have hTotalCompat : xTotal.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ hcomm
    let b₁ : Over.mk (f₁ ≫ A.hom) ⟶ A := Over.homMk f₁ rfl
    let b₂ : Over.mk (f₂ ≫ A.hom) ⟶ A := Over.homMk f₂ rfl
    let c₁ : Over.mk (g₁ ≫ f₁ ≫ A.hom) ⟶ Over.mk (f₁ ≫ A.hom) :=
      Over.homMk g₁ rfl
    let c₂ : Over.mk (g₁ ≫ f₁ ≫ A.hom) ⟶ Over.mk (f₂ ≫ A.hom) :=
      Over.homMk g₂ (by
        simpa [Category.assoc] using
          (congrArg (fun k => k ≫ A.hom) hcomm).symm)
    have hb₁ := overEquiv_symm_arrows_homMk R h₁
    have hb₂ := overEquiv_symm_arrows_homMk R h₂
    have hcomm' : c₁ ≫ b₁ = c₂ ≫ b₂ := by
      apply Over.OverMorphism.ext
      simpa [c₁, c₂, b₁, b₂, Category.assoc] using hcomm
    have hsnd := hx c₁ c₂ (f₁ := b₁) (f₂ := b₂) hb₁ hb₂ hcomm'
    let p₁ : (totalPresheaf F).obj (op Z) :=
      ⟨g₁ ≫ f₁ ≫ A.hom, F.map c₁.op (x b₁ hb₁)⟩
    let p₂ : (totalPresheaf F).obj (op Z) :=
      ⟨g₁ ≫ f₁ ≫ A.hom, F.map c₂.op (x b₂ hb₂)⟩
    have hp : p₁ = p₂ := by
      apply Sigma.ext
      · rfl
      · exact heq_of_eq hsnd
    have hleft : (totalPresheaf F).map g₁.op (xTotal f₁ h₁) = p₁ := totalMapMk c₁ (x b₁ hb₁)
    have hright : (totalPresheaf F).map g₂.op (xTotal f₂ h₂) = p₂ := totalMapMk c₂ (x b₂ hb₂)
    exact hleft.trans (hp.trans hright.symm)
  let y := xTotal.map (totalToYoneda F)
  have hy : y.Compatible := hTotalCompat.map (totalToYoneda F)
  have hyφ : y.IsAmalgamation (ULift.up A.hom) := by
    intro Y f hf
    change ULift.up (f ≫ A.hom) = _
    rfl
  obtain ⟨b, hb, hbuniq⟩ := hBase y hy
  obtain ⟨p, hp, hpuniq⟩ := hTotal xTotal hTotalCompat
  have hbaseφ := hbuniq (ULift.up A.hom) hyφ
  have hbasep := hbuniq (ULift.up p.1) (hp.map (totalToYoneda F))
  have hψ : p.1 = A.hom := congrArg ULift.down (hbasep.trans hbaseφ.symm)
  refine ⟨totalSection p hψ, ?_, ?_⟩
  · intro B a ha
    have hf : R.arrows a.left :=
      (Sieve.overEquiv_symm_iff (Y := A) R a).mp ha
    let b' : Over.mk (a.left ≫ A.hom) ⟶ A := Over.homMk a.left rfl
    let e : B ⟶ Over.mk (a.left ≫ A.hom) :=
      Over.homMk (𝟙 B.left) (by simp)
    have hb' := overEquiv_symm_arrows_homMk R hf
    have htotal := hp a.left hf
    have hmap := totalMapSection a hψ htotal
    have hcompat : F.map (𝟙 B).op (x a ha) = F.map e.op (x b' hb') :=
      hx (𝟙 B) e (f₁ := a) (f₂ := b') ha hb' (by
        apply Over.OverMorphism.ext
        simp [e, b'])
    have hcompat' : x a ha = F.map e.op (x b' hb') := by
      simpa using hcompat
    have hsec : totalSection (xTotal a.left hf)
        (totalMapFst a hψ htotal) = F.map e.op (x b' hb') := by
      dsimp [totalSection, xTotal, e, b']
    exact hmap.trans (hsec.trans hcompat'.symm)
  · intro t' ht'
    have htotal' : xTotal.IsAmalgamation (⟨A.hom, t'⟩ :
        (totalPresheaf F).obj (op A.left)) := by
      intro Y f hf
      let b' : Over.mk (f ≫ A.hom) ⟶ A := Over.homMk f rfl
      have hb' := overEquiv_symm_arrows_homMk R hf
      simpa [xTotal, b'] using (totalMapMk b' t').trans
        (congrArg (fun s => (⟨f ≫ A.hom, s⟩ :
          (totalPresheaf F).obj (op Y))) (ht' b' hb'))
    have hpair := hpuniq _ htotal'
    have heq : (⟨A.hom, t'⟩ : (totalPresheaf F).obj (op A.left)) =
        ⟨A.hom, totalSection p hψ⟩ := hpair.trans
          (totalMkSection (A := A) p hψ).symm
    exact totalSigmaSndInj heq

/-- **Stacks Project, Tag 03O1.** A presheaf on schemes over `S` is an fpqc
sheaf if and only if it is a Zariski sheaf and satisfies the singleton sheaf
condition for faithfully flat morphisms between affine schemes over `S`. -/
@[stacks 03O1, sga "3 IV 6.3.1" "(ii) fpqc only"]
public theorem isSheaf_fpqc_iff_zariski_and_affine_singleton
    (S : Scheme.{u}) (F : (Over S)ᵒᵖ ⥤ Type v) :
    Presheaf.IsSheaf (Scheme.fpqcTopology.over S) F ↔
      (Presheaf.IsSheaf (Scheme.zariskiTopology.over S) F ∧
        ∀ {R T : CommRingCat.{u}} (f : R ⟶ T) (g : Spec R ⟶ S)
          [Flat (Spec.map f)] [Surjective (Spec.map f)],
          Presieve.IsSheafFor F
            (.singleton (Over.homMk (Spec.map f) rfl :
              Over.mk (Spec.map f ≫ g) ⟶ Over.mk g))) := by
  constructor
  · intro hF
    refine ⟨Presheaf.IsSheaf.of_le (fun X R hR ↦ ?_) hF, ?_⟩
    · rw [GrothendieckTopology.mem_over_iff] at hR ⊢
      exact Scheme.zariskiTopology_le_fpqcTopology _ hR
    · intro R T f g hf hs
      apply (Presieve.isSheafFor_iff_generate _).2
      apply hF.isSheafFor (Sieve.generate (.singleton
        (Over.homMk (Spec.map f) rfl : Over.mk (Spec.map f ≫ g) ⟶ Over.mk g)))
      rw [GrothendieckTopology.mem_over_iff]
      simpa [Sieve.overEquiv, ← Sieve.generate_map_eq_functorPushforward] using
        generate_singleton_mem_fpqcTopology (Spec.map f)
  · rintro ⟨hZar, hAff⟩
    have hBaseZar : Presieve.IsSheaf Scheme.zariskiTopology
        (yoneda.obj S ⋙ uliftFunctor.{max u v}) := fun _ _ hR =>
      isSheafFor_yoneda_uliftFunctor _ hR
    have hZar' : Presieve.IsSheaf (Scheme.zariskiTopology.over S) F :=
      (isSheaf_iff_isSheaf_of_type (J := Scheme.zariskiTopology.over S) F).1 hZar
    have hTotalZar : Presieve.IsSheaf Scheme.zariskiTopology (totalPresheaf F) :=
      total_isSheaf_of_isSheaf Scheme.zariskiTopology F hBaseZar hZar'
    have hTotalType : Presieve.IsSheaf Scheme.fpqcTopology (totalPresheaf F) :=
      (AlgebraicGeometry.isSheaf_type_propQCTopology_iff (P := flatProperty.{u})
        (totalPresheaf F)).mpr ⟨hTotalZar, fun {_ _} f hf hs ↦
          have := hf; have := hs; total_isSheafFor_affineSingleton F f (fun g => hAff f g)⟩
    refine (isSheaf_iff_isSheaf_of_type (J := Scheme.fpqcTopology.over S) F).2 ?_
    intro A Q hQ
    rw [GrothendieckTopology.mem_over_iff] at hQ
    let R : Sieve A.left := Sieve.overEquiv A Q
    simpa [R] using fiber_isSheafFor_of_total (A := A) R
      (isSheafFor_yoneda_uliftFunctor _ hQ) (hTotalType R hQ)

end Stacks.EtaleCohomology

end
