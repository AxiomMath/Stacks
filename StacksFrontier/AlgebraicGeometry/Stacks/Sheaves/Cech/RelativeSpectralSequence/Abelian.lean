module

public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.RelativeSpectralSequence.Resolution
import all StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.RelativeSpectralSequence.Resolution

/-!
# The relative Čech spectral sequence of an abelian sheaf

This file constructs the relative Čech-to-cohomology spectral sequence of an abelian sheaf on
`𝒳_τ` (`Stacks.RelativeCech.exists_spectralSequenceData`, **Stacks 06XF**) and its relative
version with higher direct images along a `1`-morphism `g : 𝒳 ⥤ 𝒴` in place of cohomology
(`Stacks.RelativeCech.exists_pushforwardSpectralSequenceData`, **Stacks 072D**). It also
defines the sheaf of rings `Stacks.RelativeCech.moduleRingSheaf` and the inverse and direct
images of sheaves of modules along a `1`-morphism, with the adjunction between them.

## References

* [Stacks Project, Tag 06XF](https://stacks.math.columbia.edu/tag/06XF)
* [Stacks Project, Tag 072D](https://stacks.math.columbia.edu/tag/072D)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Stacks.RelativeCech

section Statement

universe u vᵤ vₓ wᵤ wₓ a b

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒰 : Type vᵤ} [Category.{wᵤ} 𝒰]
  {𝒳 : Type vₓ} [Category.{wₓ} 𝒳]
  (p : 𝒰 ⥤ AlgebraicGeometry.BigFppfOver B S hS)
  (q : 𝒳 ⥤ AlgebraicGeometry.BigFppfOver B S hS)
  (f : 𝒰 ⥤ 𝒳) (τ : AlgebraicGeometry.SiteKind)

/-- The first page, first-quadrant vanishing and finite abutment of the relative Čech spectral
sequence of a `1`-morphism `f` of categories fibred in groupoids and an abelian sheaf `𝓕`. -/
public structure SpectralSequenceData
    [HasSheafify (BigFppfOver.associatedTopology B S hS q τ) AddCommGrpCat.{a}]
    [HasExt.{b} (Sheaf (BigFppfOver.associatedTopology B S hS q τ) AddCommGrpCat.{a})]
    [∀ n : ℕ, HasSheafify
      (BigFppfOver.associatedTopology B S hS (Tuple.projection q f n ⋙ q) τ)
        AddCommGrpCat.{a}]
    [∀ n : ℕ, HasExt.{b} (Sheaf
      (BigFppfOver.associatedTopology B S hS (Tuple.projection q f n ⋙ q) τ)
      AddCommGrpCat.{a})]
    (𝓕 : Sheaf (BigFppfOver.associatedTopology B S hS q τ) AddCommGrpCat.{a}) where
  /-- Each projection from the Čech nerve induces restriction of sheaves. -/
  continuous (n : ℕ) :
    (Tuple.projection q f n).IsContinuous
      (BigFppfOver.associatedTopology B S hS (Tuple.projection q f n ⋙ q) τ)
      (BigFppfOver.associatedTopology B S hS q τ)
  /-- A spectral sequence starting at its first page. -/
  sequence : CohomologicalSpectralSequence AddCommGrpCat.{b} 1
  /-- The first page is cohomology on the terms of the Čech nerve. -/
  pageOneIso (i j : ℕ) :
    letI := continuous i
    (sequence.page 1).X ((i : ℤ), (j : ℤ)) ≅
      (Sheaf.functorH
        (BigFppfOver.associatedTopology B S hS (Tuple.projection q f i ⋙ q) τ) j).obj
        (((Tuple.projection q f i).sheafPushforwardContinuous AddCommGrpCat.{a}
            (BigFppfOver.associatedTopology B S hS (Tuple.projection q f i ⋙ q) τ)
            (BigFppfOver.associatedTopology B S hS q τ)).obj 𝓕)
  /-- All terms outside the first quadrant vanish. -/
  firstQuadrant (i j : ℤ) (h : (i < 0) ∨ (j < 0)) :
    IsZero ((sequence.page 1).X (i, j))
  /-- The finite filtration abuts to target-site cohomology. -/
  abutment : Stacks.RelativeLeray.AbutsTo sequence (fun n : ℤ =>
    if n < 0 then (⊥_ AddCommGrpCat.{b}) else
      (Sheaf.functorH (BigFppfOver.associatedTopology B S hS q τ) n.toNat).obj 𝓕)

private theorem exists_spectralSequenceData_of_largeCoefficients
    [HasSheafify (BigFppfOver.associatedTopology B S hS q τ)
      AddCommGrpCat.{max vᵤ vₓ wₓ a}]
    [HasExt.{b} (Sheaf (BigFppfOver.associatedTopology B S hS q τ)
      AddCommGrpCat.{max vᵤ vₓ wₓ a})]
    [∀ n : ℕ, HasSheafify
      (BigFppfOver.associatedTopology B S hS (Tuple.projection q f n ⋙ q) τ)
        AddCommGrpCat.{max vᵤ vₓ wₓ a}]
    [∀ n : ℕ, HasExt.{b} (Sheaf
      (BigFppfOver.associatedTopology B S hS (Tuple.projection q f n ⋙ q) τ)
        AddCommGrpCat.{max vᵤ vₓ wₓ a})]
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (hf : p.IsFibredOneMorphism q f) [f.Faithful] [HasEqualizers 𝒰]
    (hcover : ∀ x : 𝒳, ∃ R : Presieve x,
      Sieve.generate R ∈ BigFppfOver.associatedTopology B S hS q τ x ∧
        ∀ ⦃y : 𝒳⦄ (g : y ⟶ x), R g → ∃ z : 𝒰, Nonempty (y ≅ f.obj z))
    (𝓕 : Sheaf (BigFppfOver.associatedTopology B S hS q τ)
      AddCommGrpCat.{max vᵤ vₓ wₓ a}) :
    Nonempty (SpectralSequenceData (B := B) (S := S) (hS := hS)
      (q := q) (f := f) (τ := τ) 𝓕) := by
  let : EnoughInjectives (Sheaf (BigFppfOver.associatedTopology B S hS q τ)
      AddCommGrpCat.{max vᵤ vₓ wₓ a}) :=
    enoughInjectives_of_site_size.{vₓ, wₓ, max vᵤ a}
      (BigFppfOver.associatedTopology B S hS q τ)
  let I := injectiveResolution 𝓕
  have hcontinuous := tuple_projection_continuous_cocontinuous q f
    (hf.comp_eq.symm ▸ hp) hq (BigFppfOver.baseOverTopology B S hS τ)
  obtain ⟨E, hpage, hquad, habut⟩ :=
    exists_cechSpectralSequence.{u, wᵤ, wₓ, vᵤ, vₓ, a, b}
      B S hS p q f τ hp hq hf hcover 𝓕 I
  refine ⟨{
    continuous := fun n => (hcontinuous n).1
    sequence := E
    pageOneIso := fun i j => ?_
    firstQuadrant := hquad
    abutment := habut
  }⟩
  exact (hpage i j).some ≪≫
    cechColumnCohomologyIso.{u, wᵤ, wₓ, vᵤ, vₓ, a, b}
      B S hS p q f τ hp hq hf 𝓕 I i j

/-- For a faithful `1`-morphism `f : 𝒰 ⥤ 𝒳` of categories fibred in groupoids over the big fppf
site of `S`, with equalizers in `𝒰` and image covering `𝒳` locally, there is a first-quadrant
spectral sequence `E₁^{i,j} = Hʲ((𝒰ᵢ)_τ, fᵢ⁻¹𝓕) ⇒ Hⁱ⁺ʲ(𝒳_τ, 𝓕)`. -/
@[stacks 06XF]
public theorem exists_spectralSequenceData
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (hf : p.IsFibredOneMorphism q f) [f.Faithful] [HasEqualizers 𝒰]
    (hcover : ∀ x : 𝒳, ∃ R : Presieve x,
      Sieve.generate R ∈ BigFppfOver.associatedTopology B S hS q τ x ∧
        ∀ ⦃y : 𝒳⦄ (g : y ⟶ x), R g → ∃ z : 𝒰, Nonempty (y ≅ f.obj z))
    [HasSheafify (BigFppfOver.associatedTopology B S hS q τ)
      AddCommGrpCat.{max vᵤ vₓ wₓ a}]
    [HasExt.{b} (Sheaf (BigFppfOver.associatedTopology B S hS q τ)
      AddCommGrpCat.{max vᵤ vₓ wₓ a})]
    [∀ n : ℕ, HasSheafify
      (BigFppfOver.associatedTopology B S hS (Tuple.projection q f n ⋙ q) τ)
        AddCommGrpCat.{max vᵤ vₓ wₓ a}]
    [∀ n : ℕ, HasExt.{b} (Sheaf
      (BigFppfOver.associatedTopology B S hS (Tuple.projection q f n ⋙ q) τ)
        AddCommGrpCat.{max vᵤ vₓ wₓ a})]
    (𝓕 : Sheaf (BigFppfOver.associatedTopology B S hS q τ)
      AddCommGrpCat.{max vᵤ vₓ wₓ a}) :
    Nonempty (SpectralSequenceData (B := B) (S := S) (hS := hS)
      (q := q) (f := f) (τ := τ) 𝓕) :=
  exists_spectralSequenceData_of_largeCoefficients.{u, vᵤ, vₓ, wᵤ, wₓ, a, b}
    B S hS p q f τ hp hq hf hcover 𝓕

end Statement

section RelativePushforward

section Generalities

/-- Direct image along a cocontinuous functor is additive: on underlying presheaves it is the
right Kan extension along the opposite functor, which is a right adjoint. -/
public lemma additive_pushforwardCocontinuous
    {C₁ : Type*} [Category C₁] {C₂ : Type*} [Category C₂]
    (A : Type*) [Category A] [Preadditive A]
    (J₁ : GrothendieckTopology C₁) (J₂ : GrothendieckTopology C₂) (u : C₁ ⥤ C₂)
    [u.IsCocontinuous J₁ J₂]
    [∀ P : C₁ᵒᵖ ⥤ A, u.op.HasPointwiseRightKanExtension P] :
    (u.sheafPushforwardCocontinuous A J₁ J₂).Additive := by
  let := (u.op.ranAdjunction A).right_adjoint_additive
  let := Functor.additive_of_iso
    (u.sheafPushforwardCocontinuousCompSheafToPresheafIso A J₁ J₂).symm
  exact Functor.additive_of_comp_faithful _ (sheafToPresheaf J₂ A)

/-- Direct image along a composite of `1`-morphisms is the composite of the direct images:
both are right adjoint to restriction along the composite. -/
private def pushforwardCocontinuousComp
    {C₁ : Type*} [Category C₁] {C₂ : Type*} [Category C₂] {C₃ : Type*} [Category C₃]
    (A : Type*) [Category A]
    (J₁ : GrothendieckTopology C₁) (J₂ : GrothendieckTopology C₂)
    (J₃ : GrothendieckTopology C₃) (u : C₁ ⥤ C₂) (v : C₂ ⥤ C₃)
    [u.IsContinuous J₁ J₂] [u.IsCocontinuous J₁ J₂]
    [v.IsContinuous J₂ J₃] [v.IsCocontinuous J₂ J₃]
    [(u ⋙ v).IsContinuous J₁ J₃] [(u ⋙ v).IsCocontinuous J₁ J₃]
    [∀ P : C₁ᵒᵖ ⥤ A, u.op.HasPointwiseRightKanExtension P]
    [∀ P : C₂ᵒᵖ ⥤ A, v.op.HasPointwiseRightKanExtension P]
    [∀ P : C₁ᵒᵖ ⥤ A, (u ⋙ v).op.HasPointwiseRightKanExtension P] :
    u.sheafPushforwardCocontinuous A J₁ J₂ ⋙ v.sheafPushforwardCocontinuous A J₂ J₃ ≅
      (u ⋙ v).sheafPushforwardCocontinuous A J₁ J₃ :=
  Adjunction.rightAdjointUniq
    (((v.sheafAdjunctionCocontinuous A J₂ J₃).comp
        (u.sheafAdjunctionCocontinuous A J₁ J₂)).ofNatIsoLeft
      (u.sheafPushforwardContinuousComp v A J₁ J₂ J₃))
    ((u ⋙ v).sheafAdjunctionCocontinuous A J₁ J₃)

/-- The `k`-th right derived functor of an additive functor at an object, read off from an
injective resolution of that object: it is the `k`-th homology of the image of the associated
`ℤ`-indexed complex. -/
private def rightDerivedHomologyIso {D A : Type*} [Category D] [Abelian D]
    [HasInjectiveResolutions D] [Category A] [Abelian A] (T : D ⥤ A) [T.Additive]
    {Z : D} (I : InjectiveResolution Z) (k : ℕ) :
    ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.cochainComplex).homology (k : ℤ) ≅
      (T.rightDerived k).obj Z :=
  HomologicalComplex.homologyMapIso (mapExtendIso T I.cocomplex) (k : ℤ) ≪≫
    ((T.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).extendHomologyIso
      ComplexShape.embeddingUpNat (by simp) ≪≫
    (I.isoRightDerivedObj T k).symm

end Generalities

section Column

universe u vU vX vY uU uX uY w

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {U : Type uU} {X : Type uX} {Y : Type uY}
  [Category.{vU} U] [Category.{vX} X] [Category.{vY} Y]
  (p : U ⥤ AlgebraicGeometry.BigFppfOver B S hS)
  (q : X ⥤ AlgebraicGeometry.BigFppfOver B S hS)
  (r : Y ⥤ AlgebraicGeometry.BigFppfOver B S hS)
  (f : U ⥤ X) (g : X ⥤ Y)
  (τ : AlgebraicGeometry.SiteKind)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids) (hr : r.IsFiberedInGroupoids)
  (hf : p.IsFibredOneMorphism q f) (hg : q.IsFibredOneMorphism r g)
  [HasSheafify (BigFppfOver.associatedTopology B S hS q τ)
    AddCommGrpCat.{max uU uX vX w}]
  [HasSheafify (BigFppfOver.associatedTopology B S hS r τ)
    AddCommGrpCat.{max uU uX vX w}]
  [∀ P : Xᵒᵖ ⥤ AddCommGrpCat.{max uU uX vX w}, g.op.HasPointwiseRightKanExtension P]
  [∀ (n : ℕ) (P : (Tuple q f n)ᵒᵖ ⥤ AddCommGrpCat.{max uU uX vX w}),
    (Tuple.projection q f n ⋙ g).op.HasPointwiseRightKanExtension P]
  (F : Sheaf (BigFppfOver.associatedTopology B S hS q τ)
    AddCommGrpCat.{max uU uX vX w})

include hp hq hr hf hg in
/-- The `n`-th column of the double complex computing the relative Čech spectral sequence for
the direct image along `g` is the direct image along `g ∘ fₙ` of an injective resolution of the
inverse image of `𝓕` on the `n`-th term of the Čech nerve, so its `k`-th homology is the `k`-th
higher direct image of that inverse image. -/
private def pushforwardColumnIso
    [f.Faithful] [HasEqualizers U]
    [∀ n : ℕ, HasSheafify (BigFppfOver.associatedTopology B S hS
      (Tuple.projection q f n ⋙ q) τ) AddCommGrpCat.{max uU uX vX w}]
    [∀ n : ℕ, EnoughInjectives (Sheaf (BigFppfOver.associatedTopology B S hS
      (Tuple.projection q f n ⋙ q) τ) AddCommGrpCat.{max uU uX vX w})]
    (I : InjectiveResolution F) (n k : ℕ) :
    letI := cechSheafComplexFunctor_additive.{u, vU, vX, uU, uX, w} B S hS q f τ
    let fn := Tuple.projection q f n
    let JX := BigFppfOver.associatedTopology B S hS q τ
    let JY := BigFppfOver.associatedTopology B S hS r τ
    let Jn := BigFppfOver.associatedTopology B S hS (fn ⋙ q) τ
    letI : fn.IsContinuous Jn JX :=
      (tuple_projection_continuous_cocontinuous q f (hf.comp_eq.symm ▸ hp) hq
        (BigFppfOver.baseOverTopology B S hS τ) n).1
    letI : fn.IsCocontinuous Jn JX :=
      (tuple_projection_continuous_cocontinuous q f (hf.comp_eq.symm ▸ hp) hq
        (BigFppfOver.baseOverTopology B S hS τ) n).2
    letI : q.IsFibered := hq.isFibered
    letI : r.IsFibered := hr.isFibered
    letI : g.IsContinuous JX JY :=
      (hg.isContinuous_and_isCocontinuous_inheritedTopology
        (BigFppfOver.baseOverTopology B S hS τ)).1
    letI : g.IsCocontinuous JX JY :=
      (hg.isContinuous_and_isCocontinuous_inheritedTopology
        (BigFppfOver.baseOverTopology B S hS τ)).2
    letI : (fn ⋙ g).IsContinuous Jn JY := Functor.isContinuous_comp fn g Jn JX JY
    letI : (fn ⋙ g).IsCocontinuous Jn JY := isCocontinuous_comp fn g Jn JX
    letI : (g.sheafPushforwardCocontinuous AddCommGrpCat.{max uU uX vX w} JX JY).Additive :=
      additive_pushforwardCocontinuous AddCommGrpCat.{max uU uX vX w} JX JY g
    letI : ((fn ⋙ g).sheafPushforwardCocontinuous
        AddCommGrpCat.{max uU uX vX w} Jn JY).Additive :=
      additive_pushforwardCocontinuous AddCommGrpCat.{max uU uX vX w} Jn JY (fn ⋙ g)
    let Γ := g.sheafPushforwardCocontinuous AddCommGrpCat.{max uU uX vX w} JX JY
    let G := cechSheafComplexFunctor.{u, vU, vX, uU, uX, w} B S hS q f τ ⋙
      Γ.mapHomologicalComplex (.up ℕ) ⋙
        ComplexShape.embeddingUpNat.extendFunctor
          (Sheaf JY AddCommGrpCat.{max uU uX vX w})
    (((G ⋙ HomologicalComplex.eval (Sheaf JY AddCommGrpCat.{max uU uX vX w})
      (.up ℤ) (n : ℤ)).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex).homology (k : ℤ) ≅
      (((fn ⋙ g).sheafPushforwardCocontinuous AddCommGrpCat.{max uU uX vX w}
          Jn JY).rightDerived k).obj
        ((fn.sheafPushforwardContinuous AddCommGrpCat.{max uU uX vX w} Jn JX).obj F) := by
  letI := cechSheafComplexFunctor_additive.{u, vU, vX, uU, uX, w} B S hS q f τ
  intro fn JX JY Jn Γ G
  have hp' : (f ⋙ q).IsFiberedInGroupoids := hf.comp_eq.symm ▸ hp
  have htop := tuple_projection_continuous_cocontinuous q f hp' hq
    (BigFppfOver.baseOverTopology B S hS τ) n
  letI : fn.IsContinuous Jn JX := htop.1
  letI : fn.IsCocontinuous Jn JX := htop.2
  letI : q.IsFibered := hq.isFibered
  letI : r.IsFibered := hr.isFibered
  have hgtop := hg.isContinuous_and_isCocontinuous_inheritedTopology
    (BigFppfOver.baseOverTopology B S hS τ)
  letI : g.IsContinuous JX JY := hgtop.1
  letI : g.IsCocontinuous JX JY := hgtop.2
  letI : (fn ⋙ g).IsContinuous Jn JY := Functor.isContinuous_comp fn g Jn JX JY
  letI : (fn ⋙ g).IsCocontinuous Jn JY := isCocontinuous_comp fn g Jn JX
  let Q := fn.sheafPushforwardContinuous AddCommGrpCat.{max uU uX vX w} Jn JX
  let P := fn.sheafPushforwardCocontinuous AddCommGrpCat.{max uU uX vX w} Jn JX
  letI : Q.Additive := { map_add := rfl }
  letI : (g.sheafPushforwardCocontinuous AddCommGrpCat.{max uU uX vX w} JX JY).Additive :=
    additive_pushforwardCocontinuous AddCommGrpCat.{max uU uX vX w} JX JY g
  letI : ((fn ⋙ g).sheafPushforwardCocontinuous
      AddCommGrpCat.{max uU uX vX w} Jn JY).Additive :=
    additive_pushforwardCocontinuous AddCommGrpCat.{max uU uX vX w} Jn JY (fn ⋙ g)
  let T := (fn ⋙ g).sheafPushforwardCocontinuous AddCommGrpCat.{max uU uX vX w} Jn JY
  have hpn := tuple_isFiberedInGroupoids q f hp' hq n
  have hfn := tuple_projection_isFibredOneMorphism q f hq n
  letI : (fn ⋙ q).IsFibered := hpn.isFibered
  letI : fn.Faithful := tuple_projection_faithful q f n
  letI := tuple_hasEqualizers q f hp' hq n
  have hI (j : ℕ) : Injective (Q.obj (I.cocomplex.X j)) :=
    AlgebraicGeometry.Stack.injective_sheafPushforwardContinuous_obj
      B S hS (fn ⋙ q) q fn (B.baseTopology τ) hpn hq rfl (I.cocomplex.X j)
  letI : Q.PreservesHomology := by
    have := hfn.preservesFiniteLimits_inverseImage
      (BigFppfOver.baseOverTopology B S hS τ) AddCommGrpCat.{max uU uX vX w}
    infer_instance
  let In := mapInjectiveResolution Q I hI
  let R := cechSheafComplexFunctor.{u, vU, vX, uU, uX, w} B S hS q f τ
  let e₁ : G ⋙ HomologicalComplex.eval _ (.up ℤ) (n : ℤ) ≅
      R ⋙ HomologicalComplex.eval _ (.up ℕ) n ⋙ Γ :=
    Functor.isoWhiskerLeft (R ⋙ Γ.mapHomologicalComplex (.up ℕ))
      (ComplexShape.embeddingUpNat.extendFunctorCompEvalIso
        (Sheaf JY AddCommGrpCat.{max uU uX vX w}) (i := n) rfl)
  let e₂ : R ⋙ HomologicalComplex.eval _ (.up ℕ) n ≅ Q ⋙ P :=
    sheafifyRanRestrictionNatIso Jn JX fn
  let e₃ : G ⋙ HomologicalComplex.eval _ (.up ℤ) (n : ℤ) ≅ Q ⋙ T :=
    e₁ ≪≫ Functor.isoWhiskerRight e₂ Γ ≪≫
      Functor.isoWhiskerLeft Q
        (pushforwardCocontinuousComp AddCommGrpCat.{max uU uX vX w} Jn JX JY fn g)
  let e₄ := (NatIso.mapHomologicalComplex e₃ (.up ℤ)).app I.cochainComplex
  let e₅ : (T.mapHomologicalComplex (.up ℤ)).obj
        ((Q.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex) ≅
      (T.mapHomologicalComplex (.up ℤ)).obj In.cochainComplex :=
    (T.mapHomologicalComplex (.up ℤ)).mapIso (mapExtendIso Q I.cocomplex)
  exact HomologicalComplex.homologyMapIso (e₄ ≪≫ e₅) (k : ℤ) ≪≫
    rightDerivedHomologyIso T In k

end Column

section PushforwardStatement

open ZeroObject

universe u v₁ v₂ v₃ w₁ w₂ w₃ a

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒰 : Type v₁} [Category.{w₁} 𝒰]
  {𝒳 : Type v₂} [Category.{w₂} 𝒳]
  {𝒴 : Type v₃} [Category.{w₃} 𝒴]
  (p : 𝒰 ⥤ AlgebraicGeometry.BigFppfOver B S hS)
  (q : 𝒳 ⥤ AlgebraicGeometry.BigFppfOver B S hS)
  (r : 𝒴 ⥤ AlgebraicGeometry.BigFppfOver B S hS)
  (f : 𝒰 ⥤ 𝒳) (g : 𝒳 ⥤ 𝒴) (τ : AlgebraicGeometry.SiteKind)

/-- The first page, first-quadrant vanishing and abutment of the relative Čech spectral
sequence of a `1`-morphism `f` of categories fibred in groupoids, an abelian sheaf `𝓕` on the
target of `f`, and a further `1`-morphism `g` along which the direct images are taken. -/
public structure PushforwardSpectralSequenceData
    [HasSheafify (BigFppfOver.associatedTopology B S hS q τ) AddCommGrpCat.{a}]
    [HasSheafify (BigFppfOver.associatedTopology B S hS r τ) AddCommGrpCat.{a}]
    [∀ n : ℕ, HasSheafify
      (BigFppfOver.associatedTopology B S hS (Tuple.projection q f n ⋙ q) τ)
        AddCommGrpCat.{a}]
    [∀ P : 𝒳ᵒᵖ ⥤ AddCommGrpCat.{a}, g.op.HasPointwiseRightKanExtension P]
    [∀ (n : ℕ) (P : (Tuple q f n)ᵒᵖ ⥤ AddCommGrpCat.{a}),
      (Tuple.projection q f n ⋙ g).op.HasPointwiseRightKanExtension P]
    (𝓕 : Sheaf (BigFppfOver.associatedTopology B S hS q τ) AddCommGrpCat.{a}) where
  /-- Each projection from the Čech nerve induces restriction of sheaves. -/
  continuous (n : ℕ) :
    (Tuple.projection q f n).IsContinuous
      (BigFppfOver.associatedTopology B S hS (Tuple.projection q f n ⋙ q) τ)
      (BigFppfOver.associatedTopology B S hS q τ)
  /-- Each projection from the Čech nerve induces a direct image of sheaves. -/
  cocontinuous (n : ℕ) :
    (Tuple.projection q f n).IsCocontinuous
      (BigFppfOver.associatedTopology B S hS (Tuple.projection q f n ⋙ q) τ)
      (BigFppfOver.associatedTopology B S hS q τ)
  /-- The `1`-morphism `g` induces a direct image of sheaves. -/
  gCocontinuous :
    g.IsCocontinuous (BigFppfOver.associatedTopology B S hS q τ)
      (BigFppfOver.associatedTopology B S hS r τ)
  /-- Abelian sheaves on each term of the Čech nerve have enough injectives, which is what
  makes the higher direct images along the terms of the nerve defined. -/
  enoughInjectives (n : ℕ) :
    EnoughInjectives (Sheaf (BigFppfOver.associatedTopology B S hS
      (Tuple.projection q f n ⋙ q) τ) AddCommGrpCat.{a})
  /-- Abelian sheaves on the target of `f` have enough injectives, which is what makes the
  higher direct images along `g` defined. -/
  enoughInjectivesSource :
    EnoughInjectives (Sheaf (BigFppfOver.associatedTopology B S hS q τ) AddCommGrpCat.{a})
  /-- A spectral sequence of abelian sheaves on the site of `𝒴`, starting at its first page. -/
  sequence : CohomologicalSpectralSequence
    (Sheaf (BigFppfOver.associatedTopology B S hS r τ) AddCommGrpCat.{a}) 1
  /-- The first page is the higher direct image along `g ∘ fᵢ` of the inverse image of `𝓕` on
  the `i`-th term of the Čech nerve. -/
  pageOneIso (i j : ℕ) :
    letI := continuous i
    letI := cocontinuous i
    letI := gCocontinuous
    letI := enoughInjectives i
    letI : (Tuple.projection q f i ⋙ g).IsCocontinuous
        (BigFppfOver.associatedTopology B S hS (Tuple.projection q f i ⋙ q) τ)
        (BigFppfOver.associatedTopology B S hS r τ) :=
      isCocontinuous_comp (Tuple.projection q f i) g
        (BigFppfOver.associatedTopology B S hS (Tuple.projection q f i ⋙ q) τ)
        (BigFppfOver.associatedTopology B S hS q τ)
    letI := additive_pushforwardCocontinuous AddCommGrpCat.{a}
      (BigFppfOver.associatedTopology B S hS (Tuple.projection q f i ⋙ q) τ)
      (BigFppfOver.associatedTopology B S hS r τ) (Tuple.projection q f i ⋙ g)
    (sequence.page 1).X ((i : ℤ), (j : ℤ)) ≅
      (((Tuple.projection q f i ⋙ g).sheafPushforwardCocontinuous AddCommGrpCat.{a}
          (BigFppfOver.associatedTopology B S hS (Tuple.projection q f i ⋙ q) τ)
          (BigFppfOver.associatedTopology B S hS r τ)).rightDerived j).obj
        (((Tuple.projection q f i).sheafPushforwardContinuous AddCommGrpCat.{a}
            (BigFppfOver.associatedTopology B S hS (Tuple.projection q f i ⋙ q) τ)
            (BigFppfOver.associatedTopology B S hS q τ)).obj 𝓕)
  /-- All terms outside the first quadrant vanish. -/
  firstQuadrant (i j : ℤ) (h : (i < 0) ∨ (j < 0)) :
    IsZero ((sequence.page 1).X (i, j))
  /-- The finite filtration abuts to the higher direct images of `𝓕` along `g`. -/
  abutment :
    letI := gCocontinuous
    letI := enoughInjectivesSource
    letI := additive_pushforwardCocontinuous AddCommGrpCat.{a}
      (BigFppfOver.associatedTopology B S hS q τ)
      (BigFppfOver.associatedTopology B S hS r τ) g
    Stacks.RelativeLeray.AbutsTo sequence (fun n : ℤ =>
      if n < 0 then 0 else
        ((g.sheafPushforwardCocontinuous AddCommGrpCat.{a}
          (BigFppfOver.associatedTopology B S hS q τ)
          (BigFppfOver.associatedTopology B S hS r τ)).rightDerived n.toNat).obj 𝓕)

/-- Let `f : 𝒰 ⥤ 𝒳` and `g : 𝒳 ⥤ 𝒴` be `1`-morphisms of categories fibred in groupoids over the
big fppf site of `S`, with `f` faithful, with equalizers in `𝒰` and with the image of `f` covering
`𝒳` locally for the topology `τ`. For an abelian sheaf `𝓕` on `𝒳_τ` there is a first-quadrant
spectral sequence of abelian sheaves on `𝒴_τ` with first page `E₁^{i,j} = Rʲ(g ∘ fᵢ)_* fᵢ⁻¹𝓕`
abutting to `Rⁱ⁺ʲ g_* 𝓕`. -/
@[stacks 072D]
public theorem exists_pushforwardSpectralSequenceData
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids) (hr : r.IsFiberedInGroupoids)
    (hf : p.IsFibredOneMorphism q f) (hg : q.IsFibredOneMorphism r g)
    [f.Faithful] [HasEqualizers 𝒰]
    (hcover : ∀ x : 𝒳, ∃ R : Presieve x,
      Sieve.generate R ∈ BigFppfOver.associatedTopology B S hS q τ x ∧
        ∀ ⦃y : 𝒳⦄ (k : y ⟶ x), R k → ∃ z : 𝒰, Nonempty (y ≅ f.obj z))
    [HasSheafify (BigFppfOver.associatedTopology B S hS q τ)
      AddCommGrpCat.{max v₁ w₁ v₂ w₂ v₃ w₃ a}]
    [HasSheafify (BigFppfOver.associatedTopology B S hS r τ)
      AddCommGrpCat.{max v₁ w₁ v₂ w₂ v₃ w₃ a}]
    [∀ n : ℕ, HasSheafify
      (BigFppfOver.associatedTopology B S hS (Tuple.projection q f n ⋙ q) τ)
        AddCommGrpCat.{max v₁ w₁ v₂ w₂ v₃ w₃ a}]
    [∀ P : 𝒳ᵒᵖ ⥤ AddCommGrpCat.{max v₁ w₁ v₂ w₂ v₃ w₃ a},
      g.op.HasPointwiseRightKanExtension P]
    [∀ (n : ℕ) (P : (Tuple q f n)ᵒᵖ ⥤ AddCommGrpCat.{max v₁ w₁ v₂ w₂ v₃ w₃ a}),
      (Tuple.projection q f n ⋙ g).op.HasPointwiseRightKanExtension P]
    (𝓕 : Sheaf (BigFppfOver.associatedTopology B S hS q τ)
      AddCommGrpCat.{max v₁ w₁ v₂ w₂ v₃ w₃ a}) :
    Nonempty (PushforwardSpectralSequenceData (B := B) (S := S) (hS := hS)
      (q := q) (r := r) (f := f) (g := g) (τ := τ) 𝓕) := by
  have hp' : (f ⋙ q).IsFiberedInGroupoids := hf.comp_eq.symm ▸ hp
  have hcont := tuple_projection_continuous_cocontinuous q f hp' hq
    (BigFppfOver.baseOverTopology B S hS τ)
  let : q.IsFibered := hq.isFibered
  let : r.IsFibered := hr.isFibered
  have hgtop := hg.isContinuous_and_isCocontinuous_inheritedTopology
    (BigFppfOver.baseOverTopology B S hS τ)
  let : g.IsContinuous (BigFppfOver.associatedTopology B S hS q τ)
    (BigFppfOver.associatedTopology B S hS r τ) := hgtop.1
  let : g.IsCocontinuous (BigFppfOver.associatedTopology B S hS q τ)
    (BigFppfOver.associatedTopology B S hS r τ) := hgtop.2
  let : EnoughInjectives (Sheaf (BigFppfOver.associatedTopology B S hS q τ)
      AddCommGrpCat.{max v₁ w₁ v₂ w₂ v₃ w₃ a}) :=
    enoughInjectives_of_site_size.{v₂, w₂, max v₁ w₁ v₃ w₃ a}
      (BigFppfOver.associatedTopology B S hS q τ)
  have hEI : ∀ n : ℕ, EnoughInjectives (Sheaf (BigFppfOver.associatedTopology B S hS
      (Tuple.projection q f n ⋙ q) τ) AddCommGrpCat.{max v₁ w₁ v₂ w₂ v₃ w₃ a}) := fun n =>
    enoughInjectives_of_site_size.{max v₁ v₂ w₂, max w₁ w₂, max v₃ w₃ a} _
  let := cechSheafComplexFunctor_additive.{u, w₁, w₂, v₁, v₂, max w₁ v₃ w₃ a} B S hS q f τ
  let Γ := g.sheafPushforwardCocontinuous AddCommGrpCat.{max v₁ w₁ v₂ w₂ v₃ w₃ a}
    (BigFppfOver.associatedTopology B S hS q τ)
    (BigFppfOver.associatedTopology B S hS r τ)
  let : Γ.Additive :=
    additive_pushforwardCocontinuous AddCommGrpCat.{max v₁ w₁ v₂ w₂ v₃ w₃ a}
      (BigFppfOver.associatedTopology B S hS q τ)
      (BigFppfOver.associatedTopology B S hS r τ) g
  let I := injectiveResolution 𝓕
  obtain ⟨E, hpage, hquad, habut⟩ :=
    exists_spectralSequence_of_natFunctorResolution Γ
      (cechSheafComplexFunctor.{u, w₁, w₂, v₁, v₂, max w₁ v₃ w₃ a} B S hS q f τ)
      (augmentationResolutionNatTrans.{u, w₁, w₂, v₁, v₂, max w₁ v₃ w₃ a} B S hS q f τ)
      I.cochainComplex
      (fun n => augmentationResolution_map_quasiIso.{u, w₁, w₂, v₁, v₂, max w₁ v₃ w₃ a}
        B S hS p q f τ hp hq hf hcover (I.cochainComplex.X n) Γ)
  refine ⟨{
    continuous := fun n => (hcont n).1
    cocontinuous := fun n => (hcont n).2
    gCocontinuous := hgtop.2
    enoughInjectives := hEI
    enoughInjectivesSource := inferInstance
    sequence := E
    pageOneIso := fun i j => (hpage i j).some ≪≫
      pushforwardColumnIso.{u, w₁, w₂, w₃, v₁, v₂, v₃, max w₁ v₃ w₃ a}
        B S hS p q r f g τ hp hq hr hf hg 𝓕 I i j
    firstQuadrant := hquad
    abutment := ?_ }⟩
  refine spectralSequence_abutsTo_of_iso E habut (fun n => ?_)
  split_ifs with hn
  · exact (HomologicalComplex.ExactAt.of_isZero
      (K := ((Γ.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex)) (i := n)
      (Γ.map_isZero (CochainComplex.isZero_of_isStrictlyGE I.cochainComplex 0 n
        hn))).isZero_homology.iso (isZero_zero _)
  · have hn' : (n.toNat : ℤ) = n := by omega
    simpa only [hn'] using rightDerivedHomologyIso Γ I n.toNat

end PushforwardStatement

end RelativePushforward

section Modules

/-! ### Direct and inverse images of sheaves of modules along a `1`-morphism -/

section RingSheaf

universe u v w

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The sheaf of rings for modules on the site associated with a category fibred in groupoids
over the big fppf site of `S` and one of the five topologies `τ`: the underlying sheaf of rings
of the structure sheaf of **Stacks 06TV**. -/
public noncomputable abbrev moduleRingSheaf {𝒜 : Type v} [Category.{w} 𝒜]
    (p : 𝒜 ⥤ AlgebraicGeometry.BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
    (τ : AlgebraicGeometry.SiteKind) :
    Sheaf (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS p τ) RingCat.{u} :=
  AlgebraicGeometry.Stack.ringStructureSheafCore B S hS p hp (B.baseTopology τ)
    (B.baseTopology_le_topology τ)

end RingSheaf

section ImageFunctors

universe u v₁ v₂ w₁ w₂ t

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒜 : Type v₁} [Category.{w₁} 𝒜] {ℬ : Type v₂} [Category.{w₂} ℬ]
  (p : 𝒜 ⥤ AlgebraicGeometry.BigFppfOver B S hS)
  (q : ℬ ⥤ AlgebraicGeometry.BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
  (F : 𝒜 ⥤ ℬ) (hF : F ⋙ q = p) (τ : AlgebraicGeometry.SiteKind)

/-- The structure sheaf of rings of the source of a `1`-morphism of categories fibred in
groupoids is the inverse image of the structure sheaf of rings of the target: both restrict
the structure sheaf of the base along the structure functor of the source. -/
public theorem ringStructureSheafCore_eq_pushforward :
    letI : p.IsFibered := hp.isFibered
    letI : q.IsFibered := hq.isFibered
    letI := ((hq.isFibredOneMorphism hF).isContinuous_and_isCocontinuous_inheritedTopology
      (AlgebraicGeometry.BigFppfOver.baseOverTopology B S hS τ)).1
    moduleRingSheaf B S hS p hp τ =
      (F.sheafPushforwardContinuous RingCat.{u}
          (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS p τ)
          (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)).obj
        (moduleRingSheaf B S hS q hq τ) := by
  cases hF
  rfl

/-- The inverse image of sheaves of modules along a `1`-morphism of categories fibred in
groupoids, computed in the topology `τ`: restriction of scalars along the identification of
the structure sheaf of the source with the inverse image of the structure sheaf of the
target. -/
public noncomputable def moduleInverseImage :
    SheafOfModules.{t} (moduleRingSheaf B S hS q hq τ) ⥤
      SheafOfModules.{t}
        (moduleRingSheaf B S hS p hp τ) :=
  letI : p.IsFibered := hp.isFibered
  letI : q.IsFibered := hq.isFibered
  letI := ((hq.isFibredOneMorphism hF).isContinuous_and_isCocontinuous_inheritedTopology
    (AlgebraicGeometry.BigFppfOver.baseOverTopology B S hS τ)).1
  SheafOfModules.pushforward.{t}
    (AlgebraicGeometry.Stack.ringStructureSheafCoreHom B S hS p q F (B.baseTopology τ)
      hp hq hF (B.baseTopology_le_topology τ))

/-- The direct image of sheaves of modules along a `1`-morphism of categories fibred in
groupoids, computed in the topology `τ`: the right adjoint of the inverse image
`Stacks.RelativeCech.moduleInverseImage`. Its right derived functors are the higher direct
images of the `1`-morphism. -/
public noncomputable def moduleDirectImage :
    SheafOfModules.{max v₁ w₂ t}
        (moduleRingSheaf B S hS p hp τ) ⥤
      SheafOfModules.{max v₁ w₂ t}
        (moduleRingSheaf B S hS q hq τ) :=
  letI : p.IsFibered := hp.isFibered
  letI : q.IsFibered := hq.isFibered
  letI := ((hq.isFibredOneMorphism hF).isContinuous_and_isCocontinuous_inheritedTopology
    (AlgebraicGeometry.BigFppfOver.baseOverTopology B S hS τ)).1
  letI := ((hq.isFibredOneMorphism hF).isContinuous_and_isCocontinuous_inheritedTopology
    (AlgebraicGeometry.BigFppfOver.baseOverTopology B S hS τ)).2
  SheafOfModules.directImageOfEq.{u, max v₁ w₂ t} F _ _ _
    (ringStructureSheafCore_eq_pushforward B S hS p q hp hq F hF τ)

/-- The inverse image of sheaves of modules is left adjoint to the direct image. -/
public noncomputable def moduleInverseDirectImageAdjunction :
    moduleInverseImage.{u, v₁, v₂, w₁, w₂, max v₁ w₂ t} B S hS p q hp hq F hF τ ⊣
      moduleDirectImage.{u, v₁, v₂, w₁, w₂, t} B S hS p q hp hq F hF τ :=
  letI : p.IsFibered := hp.isFibered
  letI : q.IsFibered := hq.isFibered
  letI := ((hq.isFibredOneMorphism hF).isContinuous_and_isCocontinuous_inheritedTopology
    (AlgebraicGeometry.BigFppfOver.baseOverTopology B S hS τ)).1
  letI := ((hq.isFibredOneMorphism hF).isContinuous_and_isCocontinuous_inheritedTopology
    (AlgebraicGeometry.BigFppfOver.baseOverTopology B S hS τ)).2
  SheafOfModules.pushforwardDirectImageAdjunctionOfEq.{u, max v₁ w₂ t} F _ _ _
    (ringStructureSheafCore_eq_pushforward B S hS p q hp hq F hF τ)

/-- The inverse image of sheaves of modules is additive: it is restriction of scalars, which
is additive on the underlying presheaves of abelian groups. -/
public lemma moduleInverseImage_additive :
    (moduleInverseImage.{u, v₁, v₂, w₁, w₂, t} B S hS p q hp hq F hF τ).Additive where
  map_add := by intros; ext; rfl

/-- The direct image of sheaves of modules is additive: it is right adjoint to the inverse
image, which preserves finite limits. -/
public lemma moduleDirectImage_additive :
    (moduleDirectImage.{u, v₁, v₂, w₁, w₂, t} B S hS p q hp hq F hF τ).Additive := by
  let := moduleInverseImage_additive.{u, v₁, v₂, w₁, w₂, max v₁ w₂ t}
    B S hS p q hp hq F hF τ
  exact (moduleInverseDirectImageAdjunction.{u, v₁, v₂, w₁, w₂, t}
    B S hS p q hp hq F hF τ).right_adjoint_additive

end ImageFunctors

end Modules

end Stacks.RelativeCech

end
