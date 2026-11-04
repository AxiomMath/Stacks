module

public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.RelativeSpectralSequence.ModuleCech
import all StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.RelativeSpectralSequence.Resolution
import all StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.RelativeSpectralSequence.Abelian
import all StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.RelativeSpectralSequence.ModuleCech

/-!
# The relative Čech spectral sequence of a sheaf of modules

This file identifies the columns of the double complex attached to a sheaf of modules with the
higher direct images of its inverse images on the Čech terms, and constructs the relative Čech
spectral sequence of sheaves of modules
(`Stacks.RelativeCech.exists_modulePushforwardSpectralSequenceData`, **Stacks 072E**).

## References

* [Stacks Project, Tag 072E](https://stacks.math.columbia.edu/tag/072E)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Stacks.RelativeCech

section Modules

/-! ### The columns of the double complex -/

section ModuleColumn

open scoped Simplicial

universe u v₁ v₂ v₃ w₁ w₂ w₃ a

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒰 : Type v₁} [Category.{w₁} 𝒰] {𝒳 : Type v₂} [Category.{w₂} 𝒳]
  {𝒴 : Type v₃} [Category.{w₃} 𝒴]
  (p : 𝒰 ⥤ AlgebraicGeometry.BigFppfOver B S hS)
  (q : 𝒳 ⥤ AlgebraicGeometry.BigFppfOver B S hS)
  (r : 𝒴 ⥤ AlgebraicGeometry.BigFppfOver B S hS)
  (f : 𝒰 ⥤ 𝒳) (g : 𝒳 ⥤ 𝒴) (τ : AlgebraicGeometry.SiteKind)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids) (hr : r.IsFiberedInGroupoids)
  (hf : p.IsFibredOneMorphism q f) (hg : q.IsFibredOneMorphism r g)

include hg in
/-- The composite of a projection of the relative Čech nerve with `g` is a `1`-morphism to
`𝒴` over the base. -/
public lemma tupleProjection_comp_g_comp_eq (n : ℕ) :
    (Tuple.projection q f n ⋙ g) ⋙ r = Tuple.projection q f n ⋙ q := by
  rw [Functor.assoc, hg.comp_eq]

include hp hq hr hf hg in
/-- The `n`-th column of the double complex computing the relative Čech spectral sequence of
sheaves of modules is the direct image along `g ∘ fₙ` of an injective resolution of the inverse
image of `𝓕` on the `n`-th term of the Čech nerve, so its `k`-th homology is the `k`-th higher
direct image of that inverse image. -/
private noncomputable def moduleColumnIso
    [f.Faithful] [HasEqualizers 𝒰]
    (hRightAdjoint : ∀ n : ℕ, (PresheafOfModules.pushforward.{max u v₁ w₁ v₂ w₂ v₃ w₃ a}
      (AlgebraicGeometry.Stack.ringStructureSheafCoreHom B S hS
        (Tuple.projection q f n ⋙ q) q (Tuple.projection q f n) (B.baseTopology τ)
        (tupleProjection_comp_isFiberedInGroupoids B S hS p q f hp hq hf n) hq rfl
        (B.baseTopology_le_topology τ)).hom).IsRightAdjoint)
    [∀ (n : ℕ) (G : (Tuple q f n)ᵒᵖ ⥤ AddCommGrpCat.{max u v₁ w₁ v₂ w₂ v₃ w₃ a}),
      (Tuple.projection q f n).op.HasPointwiseLeftKanExtension G]
    [HasSheafify (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)
      AddCommGrpCat.{max u v₁ w₁ v₂ w₂ v₃ w₃ a}]
    [(AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ).WEqualsLocallyBijective
      AddCommGrpCat.{max u v₁ w₁ v₂ w₂ v₃ w₃ a}]
    [HasSheafify (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS r τ)
      AddCommGrpCat.{max u v₁ w₁ v₂ w₂ v₃ w₃ a}]
    [(AlgebraicGeometry.BigFppfOver.associatedTopology B S hS r τ).WEqualsLocallyBijective
      AddCommGrpCat.{max u v₁ w₁ v₂ w₂ v₃ w₃ a}]
    [∀ n : ℕ, HasSheafify (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS
      (Tuple.projection q f n ⋙ q) τ) AddCommGrpCat.{max u v₁ w₁ v₂ w₂ v₃ w₃ a}]
    [∀ n : ℕ, (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS
      (Tuple.projection q f n ⋙ q) τ).WEqualsLocallyBijective
        AddCommGrpCat.{max u v₁ w₁ v₂ w₂ v₃ w₃ a}]
    [∀ n : ℕ, EnoughInjectives (SheafOfModules.{max u v₁ w₁ v₂ w₂ v₃ w₃ a}
      (moduleRingSheaf B S hS (Tuple.projection q f n ⋙ q)
        (tupleProjection_comp_isFiberedInGroupoids B S hS p q f hp hq hf n) τ))]
    (𝓕 : SheafOfModules.{max u v₁ w₁ v₂ w₂ v₃ w₃ a} (moduleRingSheaf B S hS q hq τ))
    (I : InjectiveResolution 𝓕) (n k : ℕ) :
    letI := cechModuleComplexFunctor_additive.{u, v₁, v₂, w₁, w₂, max u v₁ w₁ v₂ w₂ v₃ w₃ a}
      B S hS p q f τ hp hq hf
    letI := moduleDirectImage_additive.{u, v₂, v₃, w₂, w₃, max u v₁ w₁ v₂ w₂ v₃ w₃ a}
      B S hS q r hq hr g hg.comp_eq τ
    letI := moduleDirectImage_additive.{u, max v₁ v₂ w₂, v₃, max w₁ w₂, w₃,
      max u v₁ w₁ v₂ w₂ v₃ w₃ a} B S hS (Tuple.projection q f n ⋙ q) r
      (tupleProjection_comp_isFiberedInGroupoids B S hS p q f hp hq hf n) hr
      (Tuple.projection q f n ⋙ g)
      (tupleProjection_comp_g_comp_eq B S hS q r f g hg n) τ
    let Γ := moduleDirectImage.{u, v₂, v₃, w₂, w₃, max u v₁ w₁ v₂ w₂ v₃ w₃ a}
      B S hS q r hq hr g hg.comp_eq τ
    let G := cechModuleComplexFunctor.{u, v₁, v₂, w₁, w₂, max u v₁ w₁ v₂ w₂ v₃ w₃ a}
        B S hS p q f τ hp hq hf ⋙
      Γ.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
        ComplexShape.embeddingUpNat.extendFunctor
          (SheafOfModules.{max u v₁ w₁ v₂ w₂ v₃ w₃ a} (moduleRingSheaf B S hS r hr τ))
    (((G ⋙ HomologicalComplex.eval
      (SheafOfModules.{max u v₁ w₁ v₂ w₂ v₃ w₃ a} (moduleRingSheaf B S hS r hr τ))
      (ComplexShape.up ℤ) (n : ℤ)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        I.cochainComplex).homology (k : ℤ) ≅
      ((moduleDirectImage.{u, max v₁ v₂ w₂, v₃, max w₁ w₂, w₃, max u v₁ w₁ v₂ w₂ v₃ w₃ a}
          B S hS (Tuple.projection q f n ⋙ q) r
          (tupleProjection_comp_isFiberedInGroupoids B S hS p q f hp hq hf n) hr
          (Tuple.projection q f n ⋙ g)
          (tupleProjection_comp_g_comp_eq B S hS q r f g hg n) τ).rightDerived k).obj
        ((moduleInverseImage.{u, max v₁ v₂ w₂, v₂, max w₁ w₂, w₂, max u v₁ w₁ v₂ w₂ v₃ w₃ a}
          B S hS (Tuple.projection q f n ⋙ q) q
          (tupleProjection_comp_isFiberedInGroupoids B S hS p q f hp hq hf n) hq
          (Tuple.projection q f n) rfl τ).obj 𝓕) := by
  have hpn := tupleProjection_comp_isFiberedInGroupoids B S hS p q f hp hq hf n
  have hcg := tupleProjection_comp_g_comp_eq B S hS q r f g hg n
  letI := cechModuleComplexFunctor_additive.{u, v₁, v₂, w₁, w₂, max u v₁ w₁ v₂ w₂ v₃ w₃ a}
    B S hS p q f τ hp hq hf
  letI := moduleDirectImage_additive.{u, v₂, v₃, w₂, w₃, max u v₁ w₁ v₂ w₂ v₃ w₃ a}
    B S hS q r hq hr g hg.comp_eq τ
  letI := moduleDirectImage_additive.{u, max v₁ v₂ w₂, v₃, max w₁ w₂, w₃, max u v₁ w₁ v₂ w₂ v₃ w₃ a}
    B S hS (Tuple.projection q f n ⋙ q) r
    hpn hr
    (Tuple.projection q f n ⋙ g)
    hcg τ
  letI := tupleProjection_isContinuous B S hS p q f τ hp hq hf n
  letI := tupleProjection_isCocontinuous B S hS p q f τ hp hq hf n
  letI : q.IsFibered := hq.isFibered
  letI : r.IsFibered := hr.isFibered
  have hgtop := hg.isContinuous_and_isCocontinuous_inheritedTopology
    (AlgebraicGeometry.BigFppfOver.baseOverTopology B S hS τ)
  letI : g.IsContinuous (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)
    (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS r τ) := hgtop.1
  letI : g.IsCocontinuous (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)
    (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS r τ) := hgtop.2
  letI : (Tuple.projection q f n ⋙ g).IsContinuous
      (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS
        (Tuple.projection q f n ⋙ q) τ)
      (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS r τ) :=
    Functor.isContinuous_comp (Tuple.projection q f n) g
      (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS
        (Tuple.projection q f n ⋙ q) τ)
      (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)
      (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS r τ)
  letI : (Tuple.projection q f n ⋙ g).IsCocontinuous
      (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS
        (Tuple.projection q f n ⋙ q) τ)
      (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS r τ) :=
    isCocontinuous_comp (Tuple.projection q f n) g
      (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS
        (Tuple.projection q f n ⋙ q) τ)
      (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)
  letI : PreservesFiniteLimits (moduleInverseImage.{u, max v₁ v₂ w₂, v₂, max w₁ w₂,
      w₂, max u v₁ w₁ v₂ w₂ v₃ w₃ a} B S hS (Tuple.projection q f n ⋙ q) q
      hpn hq
      (Tuple.projection q f n) rfl τ) :=
    AlgebraicGeometry.Stack.preservesFiniteLimits_sheafOfModules_pushforward.{u,
      max v₁ v₂ w₂, v₂, max w₁ w₂, w₂,
      max u v₁ w₁ v₂ w₂ v₃ w₃ a} B S hS (Tuple.projection q f n ⋙ q)
      q (Tuple.projection q f n) (B.baseTopology τ)
      hpn hq rfl
      (B.baseTopology_le_topology τ)
  letI : PreservesColimits (moduleInverseImage.{u, max v₁ v₂ w₂, v₂, max w₁ w₂,
      w₂, max u v₁ w₁ v₂ w₂ v₃ w₃ a} B S hS (Tuple.projection q f n ⋙ q) q
      hpn hq
      (Tuple.projection q f n) rfl τ) :=
    (moduleInverseDirectImageAdjunction.{u, max v₁ v₂ w₂, v₂, max w₁ w₂, w₂,
      max u v₁ w₁ v₂ w₂ v₃ w₃ a} B S hS (Tuple.projection q f n ⋙ q) q
      hpn hq
      (Tuple.projection q f n) rfl τ).leftAdjoint_preservesColimits
  letI : (moduleInverseImage.{u, max v₁ v₂ w₂, v₂, max w₁ w₂, w₂, max u v₁ w₁ v₂ w₂ v₃ w₃ a}
      B S hS (Tuple.projection q f n ⋙ q) q
      hpn hq
      (Tuple.projection q f n) rfl τ).PreservesHomology := inferInstance
  letI : (Tuple.projection q f n).Faithful := tuple_projection_faithful q f n
  letI : HasEqualizers (Tuple q f n) :=
    tuple_hasEqualizers q f (hf.comp_eq.symm ▸ hp) hq n
  letI := moduleInverseImage_additive.{u, max v₁ v₂ w₂, v₂, max w₁ w₂, w₂,
    max u v₁ w₁ v₂ w₂ v₃ w₃ a} B S hS (Tuple.projection q f n ⋙ q) q hpn hq
    (Tuple.projection q f n) rfl τ
  let Q := moduleInverseImage.{u, max v₁ v₂ w₂, v₂, max w₁ w₂, w₂,
    max u v₁ w₁ v₂ w₂ v₃ w₃ a} B S hS (Tuple.projection q f n ⋙ q) q hpn hq
    (Tuple.projection q f n) rfl τ
  let P := moduleDirectImage.{u, max v₁ v₂ w₂, v₂, max w₁ w₂, w₂,
    max u v₁ w₁ v₂ w₂ v₃ w₃ a} B S hS (Tuple.projection q f n ⋙ q) q hpn hq
    (Tuple.projection q f n) rfl τ
  let Γ := moduleDirectImage.{u, v₂, v₃, w₂, w₃, max u v₁ w₁ v₂ w₂ v₃ w₃ a}
    B S hS q r hq hr g hg.comp_eq τ
  let T := moduleDirectImage.{u, max v₁ v₂ w₂, v₃, max w₁ w₂, w₃,
    max u v₁ w₁ v₂ w₂ v₃ w₃ a} B S hS (Tuple.projection q f n ⋙ q) r hpn hr
    (Tuple.projection q f n ⋙ g) hcg τ
  let R := cechModuleComplexFunctor.{u, v₁, v₂, w₁, w₂, max u v₁ w₁ v₂ w₂ v₃ w₃ a}
    B S hS p q f τ hp hq hf
  let G := R ⋙ Γ.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
    ComplexShape.embeddingUpNat.extendFunctor
      (SheafOfModules.{max u v₁ w₁ v₂ w₂ v₃ w₃ a} (moduleRingSheaf B S hS r hr τ))
  let e₁ : G ⋙ HomologicalComplex.eval _ (ComplexShape.up ℤ) (n : ℤ) ≅
      R ⋙ HomologicalComplex.eval _ (ComplexShape.up ℕ) n ⋙ Γ :=
    Functor.isoWhiskerLeft (R ⋙ Γ.mapHomologicalComplex (ComplexShape.up ℕ))
      (ComplexShape.embeddingUpNat.extendFunctorCompEvalIso
        (SheafOfModules.{max u v₁ w₁ v₂ w₂ v₃ w₃ a} (moduleRingSheaf B S hS r hr τ)) (i := n) rfl)
  let e₂ : R ⋙ HomologicalComplex.eval _ (ComplexShape.up ℕ) n ≅ Q ⋙ P :=
    Functor.isoWhiskerRight (SheafOfModules.pushforwardIdIsoPushforward₀.{u,
      max u v₁ w₁ v₂ w₂ v₃ w₃ a} (Tuple.projection q f n)
      (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS
        (Tuple.projection q f n ⋙ q) τ)
      (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)
      (moduleRingSheaf B S hS q hq τ)).symm P
  let e₃ : G ⋙ HomologicalComplex.eval _ (ComplexShape.up ℤ) (n : ℤ) ≅ Q ⋙ T :=
    e₁ ≪≫ Functor.isoWhiskerRight e₂ Γ ≪≫ Functor.isoWhiskerLeft Q
      (SheafOfModules.directImageCompOfEq.{u, max u v₁ w₁ v₂ w₂ v₃ w₃ a} (Tuple.projection q f n) g
        (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS
          (Tuple.projection q f n ⋙ q) τ)
        (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)
        (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS r τ)
        (moduleRingSheaf B S hS r hr τ)
        (ringStructureSheafCore_eq_pushforward B S hS q r hq hr g hg.comp_eq τ)
        (ringStructureSheafCore_eq_pushforward B S hS (Tuple.projection q f n ⋙ q) q
          hpn hq (Tuple.projection q f n) rfl τ)
        (ringStructureSheafCore_eq_pushforward B S hS (Tuple.projection q f n ⋙ q) r
          hpn hr (Tuple.projection q f n ⋙ g) hcg τ))
  have hI : ∀ j : ℕ, Injective (Q.obj (I.cocomplex.X j)) := by
    intro j
    let := I.injective j
    exact AlgebraicGeometry.Stack.injective_sheafOfModules_pushforward_obj
      B S hS (Tuple.projection q f n ⋙ q) q (Tuple.projection q f n) (B.baseTopology τ)
      hpn hq rfl (B.baseTopology_le_topology τ) (hRightAdjoint n) (I.cocomplex.X j)
  exact HomologicalComplex.homologyMapIso
      ((NatIso.mapHomologicalComplex e₃ (ComplexShape.up ℤ)).app I.cochainComplex ≪≫
        (T.mapHomologicalComplex (ComplexShape.up ℤ)).mapIso (mapExtendIso Q I.cocomplex))
      (k : ℤ) ≪≫
    rightDerivedHomologyIso T (mapInjectiveResolution Q I hI) k

end ModuleColumn

/-! ### The relative Čech spectral sequence of a sheaf of modules -/

section ModuleStatement

open ZeroObject

universe u v₁ v₂ v₃ w₁ w₂ w₃ a

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒰 : Type v₁} [Category.{w₁} 𝒰] {𝒳 : Type v₂} [Category.{w₂} 𝒳]
  {𝒴 : Type v₃} [Category.{w₃} 𝒴]
  (p : 𝒰 ⥤ AlgebraicGeometry.BigFppfOver B S hS)
  (q : 𝒳 ⥤ AlgebraicGeometry.BigFppfOver B S hS)
  (r : 𝒴 ⥤ AlgebraicGeometry.BigFppfOver B S hS)
  (f : 𝒰 ⥤ 𝒳) (g : 𝒳 ⥤ 𝒴) (τ : AlgebraicGeometry.SiteKind)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids) (hr : r.IsFiberedInGroupoids)
  (hf : p.IsFibredOneMorphism q f) (hg : q.IsFibredOneMorphism r g)

/-- The first page, first-quadrant vanishing and abutment of the relative Čech spectral
sequence of a `1`-morphism `f` of categories fibred in groupoids, a sheaf of modules `𝓕` on
the target of `f`, and a further `1`-morphism `g` along which the direct images are taken. -/
public structure ModulePushforwardSpectralSequenceData
    [HasSheafify (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)
      AddCommGrpCat.{max u v₁ w₁ v₂ w₂ v₃ w₃ a}]
    [(AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ).WEqualsLocallyBijective
      AddCommGrpCat.{max u v₁ w₁ v₂ w₂ v₃ w₃ a}]
    [HasSheafify (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS r τ)
      AddCommGrpCat.{max u v₁ w₁ v₂ w₂ v₃ w₃ a}]
    [(AlgebraicGeometry.BigFppfOver.associatedTopology B S hS r τ).WEqualsLocallyBijective
      AddCommGrpCat.{max u v₁ w₁ v₂ w₂ v₃ w₃ a}]
    [∀ n : ℕ, HasSheafify (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS
      (Tuple.projection q f n ⋙ q) τ) AddCommGrpCat.{max u v₁ w₁ v₂ w₂ v₃ w₃ a}]
    [∀ n : ℕ, (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS
      (Tuple.projection q f n ⋙ q) τ).WEqualsLocallyBijective
        AddCommGrpCat.{max u v₁ w₁ v₂ w₂ v₃ w₃ a}]
    (𝓕 : SheafOfModules.{max u v₁ w₁ v₂ w₂ v₃ w₃ a} (moduleRingSheaf B S hS q hq τ)) where
  /-- Sheaves of modules on each term of the Čech nerve have enough injectives, which is what
  makes the higher direct images along the terms of the nerve defined. -/
  enoughInjectives (n : ℕ) : EnoughInjectives (SheafOfModules.{max u v₁ w₁ v₂ w₂ v₃ w₃ a}
    (moduleRingSheaf B S hS (Tuple.projection q f n ⋙ q)
      (tupleProjection_comp_isFiberedInGroupoids B S hS p q f hp hq hf n) τ))
  /-- Sheaves of modules on the target of `f` have enough injectives, which is what makes the
  higher direct images along `g` defined. -/
  enoughInjectivesSource :
    EnoughInjectives (SheafOfModules.{max u v₁ w₁ v₂ w₂ v₃ w₃ a} (moduleRingSheaf B S hS q hq τ))
  /-- A spectral sequence of sheaves of modules on the site of `𝒴`, starting at its first
  page. -/
  sequence : CohomologicalSpectralSequence
    (SheafOfModules.{max u v₁ w₁ v₂ w₂ v₃ w₃ a} (moduleRingSheaf B S hS r hr τ)) 1
  /-- The first page is the higher direct image along `g ∘ fᵢ` of the inverse image of `𝓕` on
  the `i`-th term of the Čech nerve. -/
  pageOneIso (i j : ℕ) :
    letI := enoughInjectives i
    letI := moduleDirectImage_additive.{u, max v₁ v₂ w₂, v₃, max w₁ w₂, w₃,
      max u v₁ w₁ v₂ w₂ v₃ w₃ a} B S hS (Tuple.projection q f i ⋙ q) r
      (tupleProjection_comp_isFiberedInGroupoids B S hS p q f hp hq hf i) hr
      (Tuple.projection q f i ⋙ g)
      (tupleProjection_comp_g_comp_eq B S hS q r f g hg i) τ
    (sequence.page 1).X ((i : ℤ), (j : ℤ)) ≅
      ((moduleDirectImage.{u, max v₁ v₂ w₂, v₃, max w₁ w₂, w₃,
          max u v₁ w₁ v₂ w₂ v₃ w₃ a} B S hS (Tuple.projection q f i ⋙ q) r
          (tupleProjection_comp_isFiberedInGroupoids B S hS p q f hp hq hf i) hr
          (Tuple.projection q f i ⋙ g)
          (tupleProjection_comp_g_comp_eq B S hS q r f g hg i) τ).rightDerived j).obj
        ((moduleInverseImage.{u, max v₁ v₂ w₂, v₂, max w₁ w₂, w₂,
          max u v₁ w₁ v₂ w₂ v₃ w₃ a} B S hS (Tuple.projection q f i ⋙ q) q
          (tupleProjection_comp_isFiberedInGroupoids B S hS p q f hp hq hf i) hq
          (Tuple.projection q f i) rfl τ).obj 𝓕)
  /-- All terms outside the first quadrant vanish. -/
  firstQuadrant (i j : ℤ) (h : (i < 0) ∨ (j < 0)) :
    IsZero ((sequence.page 1).X (i, j))
  /-- The finite filtration abuts to the higher direct images of `𝓕` along `g`. -/
  abutment :
    letI := enoughInjectivesSource
    letI := moduleDirectImage_additive.{u, v₂, v₃, w₂, w₃, max u v₁ w₁ v₂ w₂ v₃ w₃ a}
      B S hS q r hq hr g hg.comp_eq τ
    Stacks.RelativeLeray.AbutsTo sequence (fun n : ℤ =>
      if n < 0 then 0 else
        ((moduleDirectImage.{u, v₂, v₃, w₂, w₃, max u v₁ w₁ v₂ w₂ v₃ w₃ a}
          B S hS q r hq hr g hg.comp_eq τ).rightDerived n.toNat).obj 𝓕)

include hp hq hr hf hg in
/-- Let `f : 𝒰 ⥤ 𝒳` and `g : 𝒳 ⥤ 𝒴` be `1`-morphisms of categories fibred in groupoids over the
big fppf site of `S`, with `f` faithful, with equalizers in `𝒰` and with the image of `f` covering
`𝒳` locally for the topology `τ`. For a sheaf of `𝒪_𝒳`-modules `𝓕` on `𝒳_τ` there is a
first-quadrant spectral sequence of sheaves of `𝒪_𝒴`-modules on `𝒴_τ` with first page
`E₁^{i,j} = Rʲ(g ∘ fᵢ)_* fᵢ⁻¹𝓕` abutting to `Rⁱ⁺ʲ g_* 𝓕`, all higher direct images being computed
in the `τ`-topology. -/
@[stacks 072E]
public theorem exists_modulePushforwardSpectralSequenceData
    [f.Faithful] [HasEqualizers 𝒰]
    (hcover : ∀ x : 𝒳, ∃ R : Presieve x,
      Sieve.generate R ∈ AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ x ∧
        ∀ ⦃y : 𝒳⦄ (k : y ⟶ x), R k → ∃ z : 𝒰, Nonempty (y ≅ f.obj z))
    (hRightAdjoint : ∀ n : ℕ, (PresheafOfModules.pushforward.{max u v₁ w₁ v₂ w₂ v₃ w₃ a}
      (AlgebraicGeometry.Stack.ringStructureSheafCoreHom B S hS
        (Tuple.projection q f n ⋙ q) q (Tuple.projection q f n) (B.baseTopology τ)
        (tupleProjection_comp_isFiberedInGroupoids B S hS p q f hp hq hf n) hq rfl
        (B.baseTopology_le_topology τ)).hom).IsRightAdjoint)
    [∀ (n : ℕ) (G : (Tuple q f n)ᵒᵖ ⥤ AddCommGrpCat.{max u v₁ w₁ v₂ w₂ v₃ w₃ a}),
      (Tuple.projection q f n).op.HasPointwiseLeftKanExtension G]
    [HasSheafify (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)
      AddCommGrpCat.{max u v₁ w₁ v₂ w₂ v₃ w₃ a}]
    [(AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ).WEqualsLocallyBijective
      AddCommGrpCat.{max u v₁ w₁ v₂ w₂ v₃ w₃ a}]
    [HasSheafify (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS r τ)
      AddCommGrpCat.{max u v₁ w₁ v₂ w₂ v₃ w₃ a}]
    [(AlgebraicGeometry.BigFppfOver.associatedTopology B S hS r τ).WEqualsLocallyBijective
      AddCommGrpCat.{max u v₁ w₁ v₂ w₂ v₃ w₃ a}]
    [∀ n : ℕ, HasSheafify (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS
      (Tuple.projection q f n ⋙ q) τ) AddCommGrpCat.{max u v₁ w₁ v₂ w₂ v₃ w₃ a}]
    [∀ n : ℕ, (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS
      (Tuple.projection q f n ⋙ q) τ).WEqualsLocallyBijective
        AddCommGrpCat.{max u v₁ w₁ v₂ w₂ v₃ w₃ a}]
    [∀ n : ℕ, EnoughInjectives (SheafOfModules.{max u v₁ w₁ v₂ w₂ v₃ w₃ a}
      (moduleRingSheaf B S hS (Tuple.projection q f n ⋙ q)
        (tupleProjection_comp_isFiberedInGroupoids B S hS p q f hp hq hf n) τ))]
    [EnoughInjectives (SheafOfModules.{max u v₁ w₁ v₂ w₂ v₃ w₃ a} (moduleRingSheaf B S hS q hq τ))]
    (𝓕 : SheafOfModules.{max u v₁ w₁ v₂ w₂ v₃ w₃ a} (moduleRingSheaf B S hS q hq τ)) :
    Nonempty (ModulePushforwardSpectralSequenceData.{u, v₁, v₂, v₃, w₁, w₂, w₃, a}
      B S hS p q r f g τ hp hq hr hf hg 𝓕) := by
  let := cechModuleComplexFunctor_additive.{u, v₁, v₂, w₁, w₂, max u v₁ w₁ v₂ w₂ v₃ w₃ a}
    B S hS p q f τ hp hq hf
  let := moduleDirectImage_additive.{u, v₂, v₃, w₂, w₃, max u v₁ w₁ v₂ w₂ v₃ w₃ a}
    B S hS q r hq hr g hg.comp_eq τ
  let Γ := moduleDirectImage.{u, v₂, v₃, w₂, w₃, max u v₁ w₁ v₂ w₂ v₃ w₃ a}
    B S hS q r hq hr g hg.comp_eq τ
  let I := injectiveResolution 𝓕
  obtain ⟨E, hpage, hquad, habut⟩ :=
    exists_spectralSequence_of_natFunctorResolution Γ
      (cechModuleComplexFunctor.{u, v₁, v₂, w₁, w₂, max u v₁ w₁ v₂ w₂ v₃ w₃ a}
        B S hS p q f τ hp hq hf)
      (cechModuleAugmentationNatTrans.{u, v₁, v₂, w₁, w₂, max u v₁ w₁ v₂ w₂ v₃ w₃ a}
        B S hS p q f τ hp hq hf)
      I.cochainComplex (fun n => by
        let := quasiIso_cechModuleAugmentationNatTrans_app.{u, v₁, v₂, w₁, w₂,
          max u v₁ w₁ v₂ w₂ v₃ w₃ a} B S hS p q f τ hp hq hf hcover (I.cochainComplex.X n)
        let : ∀ k : ℕ, Injective
            (((cechModuleComplexFunctor.{u, v₁, v₂, w₁, w₂, max u v₁ w₁ v₂ w₂ v₃ w₃ a}
              B S hS p q f τ hp hq hf).obj (I.cochainComplex.X n)).X k) := fun k =>
          injective_cechModuleTerm.{u, v₁, v₂, w₁, w₂, max u v₁ w₁ v₂ w₂ v₃ w₃ a}
            B S hS p q f τ hp hq hf hRightAdjoint (I.cochainComplex.X n) k
        exact quasiIso_map_of_injective Γ _)
  refine ⟨{
    enoughInjectives := fun _ => inferInstance
    enoughInjectivesSource := inferInstance
    sequence := E
    pageOneIso := fun i j => (hpage i j).some ≪≫
      moduleColumnIso.{u, v₁, v₂, v₃, w₁, w₂, w₃, a} B S hS p q r f g τ hp hq hr hf hg
        hRightAdjoint 𝓕 I i j
    firstQuadrant := hquad
    abutment := ?_ }⟩
  refine spectralSequence_abutsTo_of_iso E habut (fun n => ?_)
  split_ifs with hn
  · exact (HomologicalComplex.ExactAt.of_isZero
      (K := ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.cochainComplex)) (i := n)
      (Γ.map_isZero (CochainComplex.isZero_of_isStrictlyGE I.cochainComplex 0 n
        hn))).isZero_homology.iso (isZero_zero _)
  · have hn' : (n.toNat : ℤ) = n := by omega
    simpa only [hn'] using rightDerivedHomologyIso Γ I n.toNat

end ModuleStatement

end Modules

end Stacks.RelativeCech

end
