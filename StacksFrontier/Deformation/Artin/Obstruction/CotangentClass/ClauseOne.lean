module

public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Algebra.TrivSqZeroExt.Ideal
public import Mathlib.RingTheory.Finiteness.Prod
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import StacksFrontier.AlgebraicGeometry.Smooth.ThickeningRestriction
public import StacksFrontier.Deformation.Artin.Infinitesimal.AutomorphismFunctor
public import StacksFrontier.Deformation.Artin.Infinitesimal.CanonicalElement
public import StacksFrontier.Deformation.Artin.Obstruction
public import StacksFrontier.Deformation.Artin.Obstruction.DualSituation
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveTheory
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveCotangentPresentation
public import StacksFrontier.Homology.DoubleExtend
public import StacksFrontier.Deformation.Artin.Obstruction.CotangentClass.CotangentPushout
public import StacksFrontier.Deformation.Artin.Obstruction.CotangentClass.Thickenings
public import StacksFrontier.Deformation.Artin.Obstruction.CotangentClass.ExtensionClass

/-!
# The obstruction class on the naive cotangent complex (07YY, clause (1))

The connecting morphism of a degreewise split short exact sequence and of the tensored
triangle of a two-term complex, and the assembly of the class on `NL_{A/Λ}` that computes
all obstruction elements.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Pretriangulated NaiveCotangent
open ComplexShape (upIntRelNegOneZero)

namespace Deformation.Artin

universe u v w

attribute [local instance] HasDerivedCategory.standard

section ConnectingMorphism

open CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Preadditive
  HomologicalComplex CochainComplex CochainComplex.HomComplex

/-! ### The connecting morphism of a degreewise split short exact sequence -/

section DegreewiseSplit

variable {C : Type u} [Category.{v} C] [Abelian C]
  (S : ShortComplex (CochainComplex C ℤ))
  (σ : ∀ n, (S.map (eval C (ComplexShape.up ℤ) n)).Splitting)

/-- The third morphism of the standard triangle of `S.f`, with its target spelled
`S.X₁⟦1⟧` rather than through the triangle. -/
public def coneMor₃ : mappingCone S.f ⟶ S.X₁⟦(1 : ℤ)⟧ := (mappingCone.triangle S.f).mor₃

/-- The third morphism of the standard triangle of `S.f` on the `inl` components of the
mapping cone is minus the shift isomorphism. -/
@[reassoc] public theorem inl_v_coneMor₃_f (p q : ℤ) (hpq : p + (-1) = q) :
    (mappingCone.inl S.f).v p q hpq ≫ (coneMor₃ S).f q =
      -(shiftFunctorObjXIso S.X₁ 1 q p (by omega)).inv :=
  mappingCone.inl_v_triangle_mor₃_f _ p q hpq

/-- The third morphism of the standard triangle of `S.f` vanishes on the `inr` components of
the mapping cone. -/
@[reassoc] public theorem inr_f_coneMor₃_f (p : ℤ) :
    (mappingCone.inr S.f).f p ≫ (coneMor₃ S).f p = 0 :=
  mappingCone.inr_f_triangle_mor₃_f _ p

/-- The morphism built from the splittings, precomposed with the comparison of the mapping
cone of `S.f` with `S.X₃`, is homotopic to the third morphism of the standard triangle
of `S.f`. The homotopy is `CochainComplex.retractionCochain`, the `(-1)`-cochain
`S.X₂ ⟶ S.X₁⟦1⟧` assembled from the retractions of the splittings. -/
public def homotopy_coneMor₃ :
    Homotopy (mappingCone.descShortComplex S ≫ homOfDegreewiseSplit S σ) (coneMor₃ S) :=
  mappingCone.descHomotopy _ _ _ 0 (CochainComplex.retractionCochain S σ)
    (by
      ext p q hpq
      have hfr : S.f.f p ≫ (σ p).r = 𝟙 (S.X₁.X p) := (σ p).f_r
      -- `retractionCochain` spells the degree shift with `XIsoOfEq` and `inl_v_coneMor₃_f`
      -- with `shiftFunctorObjXIso`; the two are the same morphism.
      have hiso : (shiftFunctorObjXIso S.X₁ 1 q p (by omega)).inv =
        (S.X₁.XIsoOfEq (show p = q + 1 by omega)).hom := rfl
      rw [Cochain.add_v, Cochain.add_v, δ_zero, Cochain.zero_v,
        Cochain.comp_zero_cochain_v, Cochain.comp_zero_cochain_v,
        Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.ofHom_v, Cochain.ofHom_v,
        HomologicalComplex.comp_f, mappingCone.inl_v_descShortComplex_f_assoc,
        inl_v_coneMor₃_f S p q hpq, CochainComplex.retractionCochain_v, ← assoc, hfr, id_comp,
        zero_add, hiso, add_neg_cancel, zero_comp])
    (by
      ext p
      have hid := (σ p).id
      have hfr : S.f.f (p + 1) ≫ (σ (p + 1)).r = 𝟙 (S.X₁.X (p + 1)) := (σ (p + 1)).f_r
      have hcomm := S.f.comm p (p + 1)
      have hr : (σ (p + 1)).r ≫ 𝟙 (S.X₁.X (p + 1)) = (σ (p + 1)).r := comp_id _
      dsimp at hid
      have h₁ : ((σ p).r ≫ S.f.f p) ≫ (S.X₂.d p (p + 1) ≫ (σ (p + 1)).r) =
          (σ p).r ≫ S.X₁.d p (p + 1) := by
        rw [assoc, reassoc_of% hcomm, hfr, comp_id]
      have h₂ : 𝟙 (S.X₂.X p) ≫ (S.X₂.d p (p + 1) ≫ (σ (p + 1)).r) =
          S.X₂.d p (p + 1) ≫ (σ (p + 1)).r := id_comp _
      rw [← hid, add_comp, h₁] at h₂
      rw [Cochain.add_v, Cochain.ofHom_v, Cochain.ofHom_v,
        δ_v (-1) 0 rfl _ p p (by omega) (p - 1) (p + 1) (by omega) rfl]
      simp only [HomologicalComplex.comp_f, CochainComplex.retractionCochain_v,
        mappingCone.inr_f_descShortComplex_f_assoc, homOfDegreewiseSplit_f,
        cocycleOfDegreewiseSplit, Cocycle.mk_coe, Cochain.mk_v, inr_f_coneMor₃_f, add_zero,
        shiftFunctor_obj_d', Int.negOnePow_one, Int.negOnePow_zero, one_smul,
        assoc, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
        HomologicalComplex.XIsoOfEq_hom_comp_d, Units.neg_smul, comp_neg]
      rw [hr, ← assoc, eq_neg_add_iff_add_eq]
      exact h₂)

variable [HasDerivedCategory.{w} C]

/-- **The connecting morphism of a degreewise split short exact sequence of cochain
complexes is the morphism built from the splittings.** Both sides are available in
Mathlib — `DerivedCategory.triangleOfSESδ` and `CochainComplex.homOfDegreewiseSplit` — but
are not compared there. There is no sign. -/
public theorem triangleOfSESδ_eq_homOfDegreewiseSplit (hS : S.ShortExact) :
    DerivedCategory.triangleOfSESδ hS =
      DerivedCategory.Q.map (homOfDegreewiseSplit S σ) ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app S.X₁ := by
  have := mappingCone.quasiIso_descShortComplex hS
  have hQ := DerivedCategory.Q_map_eq_of_homotopy C (homotopy_coneMor₃ S σ)
  rw [← cancel_epi (DerivedCategory.Q.map (mappingCone.descShortComplex S)),
    DerivedCategory.descShortComplex_triangleOfSESδ, ← Functor.map_comp_assoc, hQ]
  rfl

/-- The connecting morphism of a degreewise split short exact sequence, for a factorization
of the morphism built from the splittings. Stating the factorization as a hypothesis keeps
the composite of the conclusion written with the objects of `S`, which is what lets the
morphism induced by the factors be pulled out. -/
public theorem triangleOfSESδ_eq_of_factorization (hS : S.ShortExact)
    {Y : CochainComplex C ℤ} (φ : S.X₃ ⟶ Y) (ψ : Y ⟶ S.X₁⟦(1 : ℤ)⟧)
    (hφψ : homOfDegreewiseSplit S σ = φ ≫ ψ) :
    DerivedCategory.triangleOfSESδ hS =
      DerivedCategory.Q.map φ ≫ DerivedCategory.Q.map ψ ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app S.X₁ := by
  rw [triangleOfSESδ_eq_homOfDegreewiseSplit S σ hS, hφψ, Functor.map_comp, assoc]

end DegreewiseSplit

/-! ### The splittings of the short exact sequence of a two-term complex -/

section Splittings

variable {A : Type u} [CommRing A] {N M : ModuleCat.{u} A}

/-- The degreewise splittings of the short complex `M[0] ⟶ (N ⟶ M) ⟶ N[-1]` of a two-term
complex. -/
public def twoTermSplitting (d : N ⟶ M) (i : ℤ) :
    ((twoTermShortComplex d).map (eval (ModuleCat.{u} A) (ComplexShape.up ℤ) i)).Splitting :=
  if h₀ : i = 0 then h₀ ▸ twoTermSplitting₀ d
  else if h₁ : i = -1 then h₁ ▸ twoTermSplitting₁ d
  else twoTermSplitting₂ d i h₀ h₁

/-- The retraction of `twoTermSplitting d` in degree `0`, through the identifications of the
components in degree `0`. -/
@[simp] public theorem twoTermSplitting_zero_r (d : N ⟶ M) :
    (twoTermSplitting d 0).r =
      (doubleXIso₁ d upIntRelNegOneZero NaiveCotangent.TwoTerm.negOne_ne_zero).hom ≫
        (singleObjXSelf (ComplexShape.up ℤ) 0 M).inv :=
  rfl

/-- The section of `twoTermSplitting d` in degree `-1`, through the identifications of the
components in degree `-1`. -/
@[simp] public theorem twoTermSplitting_neg_one_s (d : N ⟶ M) :
    (twoTermSplitting d (-1)).s = (singleObjXSelf (ComplexShape.up ℤ) (-1) N).hom ≫
      (doubleXIso₀ d upIntRelNegOneZero).inv :=
  rfl

/-- The morphism built from the degreewise splittings of the short complex of a two-term
complex `d : N ⟶ M` is the image of `d` under the single functor in degree `-1`, read
through the shift isomorphism of the single functors. -/
public theorem homOfDegreewiseSplit_twoTermShortComplex (d : N ⟶ M) :
    homOfDegreewiseSplit (twoTermShortComplex d) (twoTermSplitting d) =
      (CochainComplex.singleFunctor (ModuleCat.{u} A) (-1)).map d ≫
        ((CochainComplex.singleFunctors (ModuleCat.{u} A)).shiftIso 1 (-1) 0
          (by omega)).inv.app M := by
  apply from_single_hom_ext
  rw [homOfDegreewiseSplit_f]
  simp [cocycleOfDegreewiseSplit, twoTermShortComplex,
    double_d _ _ NaiveCotangent.TwoTerm.negOne_ne_zero, CochainComplex.singleFunctors,
    CochainComplex.singleFunctor, single_map_f_self, singleObjXSelf, singleObjXIsoOfEq,
    doubleXIso₀, doubleXIso₁]

end Splittings

/-! ### The connecting morphism of the triangle of a two-term complex -/

section Triangle

variable {A : Type u} [CommRing A]

/-- **The connecting morphism of the triangle of a two-term complex is the map induced by
its differential.** In the triangle `M[0] ⟶ (N ⟶ M) ⟶ N[-1] ⟶ M[0]⟦1⟧` the morphism
`N[-1] ⟶ M[0]⟦1⟧` is the image of `d` under the single functor in degree `-1`, both sides
being the module placed in cohomological degree `-1`. There is no sign. -/
public theorem twoTermTriangle_mor₃ {N M : ModuleCat.{u} A} (d : N ⟶ M) :
    (twoTermTriangle d).mor₃ =
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) (-1)).map d ≫
        ((DerivedCategory.singleFunctors (ModuleCat.{u} A)).shiftIso 1 (-1) 0
          (by omega)).inv.app M := by
  have h : (twoTermTriangle d).mor₃ =
      DerivedCategory.triangleOfSESδ (shortExact_twoTermShortComplex d) :=
    DerivedCategory.triangleOfSES_mor₃ _
  rw [h, triangleOfSESδ_eq_of_factorization _ (twoTermSplitting d) _
    ((CochainComplex.singleFunctor (ModuleCat.{u} A) (-1)).map d)
    (((CochainComplex.singleFunctors (ModuleCat.{u} A)).shiftIso 1 (-1) 0
      (by omega)).inv.app M) (homOfDegreewiseSplit_twoTermShortComplex d)]
  dsimp only [DerivedCategory.singleFunctors]
  rw [SingleFunctors.postcomp_shiftIso_inv_app]
  rfl

end Triangle

/-! ### The connecting map of the tensored triangle -/

section DerivedTensor

variable {A : Type u} [CommRing A]

/-- The degree shift `H¹(K ⊗ᴸ M[-1]) ≅ H²(K ⊗ᴸ M)` is the shifted map of the shift
isomorphism of the single functors. -/
public theorem shiftedCohomologyIso_hom_eq (K : DerivedCategory (ModuleCat.{u} A))
    (M : ModuleCat.{u} A) :
    (shiftedCohomologyIso A K M).hom =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).shiftMap
        ((CochainComplex.DerivedTensor.derivedTensorProduct K).map
            (((DerivedCategory.singleFunctors (ModuleCat.{u} A)).shiftIso 1 (-1) 0
              (by omega)).inv.app M) ≫
          ((CochainComplex.DerivedTensor.derivedTensorProduct K).commShiftIso (1 : ℤ)).hom.app
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)) 1 2 (by omega) := by
  dsimp only [Functor.shiftMap]
  rw [Functor.map_comp, assoc]
  rfl

/-- The connecting map of the tensored triangle of a two-term complex, for a factorization
of the connecting morphism of the untensored triangle. -/
public theorem derivedTensorTwoTermδ_eq_of_factorization
    (K : DerivedCategory (ModuleCat.{u} A)) (T : NaiveCotangent.TwoTerm.{u, u, u} A)
    {Y : DerivedCategory (ModuleCat.{u} A)} (φ : (twoTermComplexTriangle T).obj₃ ⟶ Y)
    (ψ : Y ⟶ ((twoTermComplexTriangle T).obj₁)⟦(1 : ℤ)⟧)
    (hφψ : (twoTermComplexTriangle T).mor₃ = φ ≫ ψ) :
    derivedTensorTwoTermδ K T =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).shift 1).map
          ((CochainComplex.DerivedTensor.derivedTensorProduct K).map φ) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).shiftMap
          ((CochainComplex.DerivedTensor.derivedTensorProduct K).map ψ ≫
            ((CochainComplex.DerivedTensor.derivedTensorProduct K).commShiftIso
              (1 : ℤ)).hom.app ((twoTermComplexTriangle T).obj₁)) 1 2 (by omega) := by
  show (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).shiftMap
      ((CochainComplex.DerivedTensor.derivedTensorProduct K).map
          ((twoTermComplexTriangle T).mor₃) ≫
        ((CochainComplex.DerivedTensor.derivedTensorProduct K).commShiftIso
          (1 : ℤ)).hom.app ((twoTermComplexTriangle T).obj₁)) 1 2 (by omega) = _
  rw [hφψ, Functor.map_comp, assoc, Functor.shiftMap_comp']

/-- The connecting map of the tensored triangle of a two-term complex is the map induced by
its differential, read through the degree shift. -/
public theorem derivedTensorTwoTermδ_eq (K : DerivedCategory (ModuleCat.{u} A))
    (T : NaiveCotangent.TwoTerm.{u, u, u} A) :
    derivedTensorTwoTermδ K T =
      (shiftedCohomologyIso A K (ModuleCat.of A T.X₁)).hom ≫
        (derivedCohomology A K 2).map (ModuleCat.ofHom T.d) := by
  rw [← shiftedCohomologyIso_naturality A K (ModuleCat.ofHom T.d),
    derivedTensorTwoTermδ_eq_of_factorization K T
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) (-1)).map (ModuleCat.ofHom T.d))
      (((DerivedCategory.singleFunctors (ModuleCat.{u} A)).shiftIso 1 (-1) 0
        (by omega)).inv.app (ModuleCat.of A T.X₀))
      (twoTermTriangle_mor₃ (ModuleCat.ofHom T.d)),
    shiftedCohomologyIso_hom_eq K (ModuleCat.of A T.X₀)]
  rfl

end DerivedTensor

end ConnectingMorphism

/-! ### The obstruction class on the naive cotangent complex (07YY, clause (1)) -/

section Assembly

variable {Λ A : Type u} [CommRing Λ] [CommRing A] [Algebra Λ A] {ι : Type u}

/-- The map `J/J² ⟶ I` of conormal modules induced by a lift of a presentation into a
square-zero thickening, the descended lift `P/J² ⟶ A'` restricted to kernels. -/
public def presentationKernelMap (P : Algebra.Generators Λ A ι) {A' : Type u} [CommRing A']
    (q : A' →+* A) (hq : IsDeformationSituation q) (f : Λ →+* A')
    (hqf : q.comp f = algebraMap Λ A) :
    letI := Stacks.Smooth.kerModule hq.1 hq.2
    P.toExtension.Cotangent →ₗ[A] RingHom.ker q :=
  letI := Stacks.Smooth.kerModule hq.1 hq.2
  letI := Stacks.Smooth.kerModule (isDeformationSituation_infinitesimal P.toExtension).1
    (isDeformationSituation_infinitesimal P.toExtension).2
  kerRestrict (isDeformationSituation_infinitesimal P.toExtension) hq
      (infinitesimalLift P q hq.1 f hqf hq.2)
      (comp_infinitesimalLift P q hq.1 f hqf hq.2) ∘ₗ
    (infinitesimalKernelEquiv P.toExtension).symm.toLinearMap

/-- The induced map of conormal modules carries the class of `j ∈ J` to the image of `j`
under the lift. -/
public theorem presentationKernelMap_mk (P : Algebra.Generators Λ A ι) {A' : Type u}
    [CommRing A'] (q : A' →+* A) (hq : IsDeformationSituation q) (f : Λ →+* A')
    (hqf : q.comp f = algebraMap Λ A) (x : P.toExtension.ker) :
    letI := Stacks.Smooth.kerModule hq.1 hq.2
    (presentationKernelMap P q hq f hqf (Algebra.Extension.Cotangent.mk x)).1 =
      presentationLift P q hq.1 f x.1 := by
  let := Stacks.Smooth.kerModule hq.1 hq.2
  let := Stacks.Smooth.kerModule (isDeformationSituation_infinitesimal P.toExtension).1
    (isDeformationSituation_infinitesimal P.toExtension).2
  have hsymm : (infinitesimalKernelEquiv P.toExtension).symm
      (Algebra.Extension.Cotangent.mk x) =
      ⟨Ideal.Quotient.mk (P.toExtension.ker ^ 2) x.1,
        quotient_mk_mem_ker_infinitesimal P.toExtension x⟩ :=
    (LinearEquiv.symm_apply_eq _).2 (infinitesimalKernelEquiv_mk P.toExtension x).symm
  have hval : presentationKernelMap P q hq f hqf (Algebra.Extension.Cotangent.mk x) =
      kerRestrict (isDeformationSituation_infinitesimal P.toExtension) hq
        (infinitesimalLift P q hq.1 f hqf hq.2)
        (comp_infinitesimalLift P q hq.1 f hqf hq.2)
        ((infinitesimalKernelEquiv P.toExtension).symm
          (Algebra.Extension.Cotangent.mk x)) := rfl
  rw [hval, hsymm]
  rfl

/-- The kernel of the infinitesimal extension of a presentation, identified with the
conormal module `J/J²`, as a morphism of `Mod_A`. -/
public def infinitesimalKernelHom (E : Algebra.Extension.{u} Λ A) :
    letI := Stacks.Smooth.kerModule (isDeformationSituation_infinitesimal E).1
      (isDeformationSituation_infinitesimal E).2
    ModuleCat.of A (RingHom.ker (algebraMap E.infinitesimal.Ring A)) ⟶
      ModuleCat.of A E.Cotangent :=
  letI := Stacks.Smooth.kerModule (isDeformationSituation_infinitesimal E).1
    (isDeformationSituation_infinitesimal E).2
  ModuleCat.ofHom (infinitesimalKernelEquiv E).toLinearMap

/-- The kernel of the projection of the pushout algebra onto `A`, identified with the
cotangent space of the presentation: an element of the kernel has vanishing first component,
and a scalar of `A` acts on it through any of its preimages. -/
public def pushoutKernelMap (E : Algebra.Extension.{u} Λ A) :
    letI := Stacks.Smooth.kerModule (isDeformationSituation_cotangentPushout E).1
      (isDeformationSituation_cotangentPushout E).2
    RingHom.ker (cotangentPushoutProj E) →ₗ[A] cotangentSpaceModule E := by
  letI := Stacks.Smooth.kerModule (isDeformationSituation_cotangentPushout E).1
    (isDeformationSituation_cotangentPushout E).2
  refine
    { toFun := fun y => (y : cotangentPushout E).snd
      map_add' := fun _ _ => rfl
      map_smul' := ?_ }
  intro a y
  obtain ⟨x, hx⟩ := (isDeformationSituation_cotangentPushout E).1 a
  subst hx
  simp only [RingHom.id_apply]
  rw [Stacks.Smooth.kerModule_smul (isDeformationSituation_cotangentPushout E).1
    (isDeformationSituation_cotangentPushout E).2]
  have hy : (y : cotangentPushout E).fst = 0 := y.2
  have hcoe : ((x • y : RingHom.ker (cotangentPushoutProj E)) : cotangentPushout E) =
      x * (y : cotangentPushout E) := rfl
  rw [hcoe, TrivSqZeroExt.snd_mul, hy]
  simp

/-- The identification of the kernel of the pushout algebra with the cotangent space, as a
morphism of `Mod_A`. -/
public def pushoutKernelHom (E : Algebra.Extension.{u} Λ A) :
    letI := Stacks.Smooth.kerModule (isDeformationSituation_cotangentPushout E).1
      (isDeformationSituation_cotangentPushout E).2
    ModuleCat.of A (RingHom.ker (cotangentPushoutProj E)) ⟶
      ModuleCat.of A (cotangentSpaceModule E) :=
  letI := Stacks.Smooth.kerModule (isDeformationSituation_cotangentPushout E).1
    (isDeformationSituation_cotangentPushout E).2
  ModuleCat.ofHom (pushoutKernelMap E)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))

/-- Two morphisms out of the kernel of a square-zero thickening agree as soon as they agree
at every element of the kernel. -/
public theorem kernelHom_ext {A' : Type u} [CommRing A']
    (D : SquareZeroThickening A B S hS toS hA A') (M : ModuleCat.{u} A)
    {g₁ g₂ : D.kernel ⟶ M} (h : ∀ y : RingHom.ker D.q, g₁.hom y = g₂.hom y) :
    g₁ = g₂ := by
  let := Stacks.Smooth.kerModule D.squareZeroSurjection.1 D.squareZeroSurjection.2
  exact ModuleCat.hom_ext (LinearMap.ext h)

end Assembly

section ClauseOne

variable (Λ A : Type u) [CommRing Λ] [CommRing A] [Algebra Λ A]
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) [IsLocallyNoetherian S]
variable (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
variable (X : Type v) [Category.{w} X] (p : X ⥤ BigFppfOver B S hS)
variable (sit : DualDeformationSituation A Λ B S hS toS hA X p)

/-- **The class of 07YY clause (1), built from a chosen presentation.** For every
presentation `P` of `A` over `Λ` whose polynomial ring and pushout algebra occur in the site
there is a class on the two-term complex `NL(α)` whose image on `NL_{A/Λ}` evaluates to the
obstruction element at every square-zero thickening, for every `Λ`-algebra structure on the
thickening lying over the base. Keeping the presentation and the `Λ`-algebra structure as
inputs rather than choosing them is what lets clause (2) be proved for the same class: the
correction that clause (2) needs lives on the degree-zero term of this presentation, and the
boundary identity of condition (iv) is read at the pushout algebra of this presentation. -/
public theorem exists_obstructionEvaluation_eq_obstruction_of_presentation {ι : Type u}
    [Finite ι] (P : Algebra.Generators Λ A ι) (hE : B.Contains (Spec (.of P.Ring)))
    (hC : B.Contains (Spec (.of (cotangentPushout P.toExtension)))) :
    ∃ ξ₀ : (derivedTensorCohomology A sit.K 1).obj
        (DerivedCategory.Q.obj (twoTermComplex (nlRestrict A P))),
      ∀ (A' : Type u) [CommRing A'] (D : SquareZeroThickening A B S hS toS hA A')
        (f : Λ →+* A')
        (_hfS : Spec.map (CommRingCat.ofHom f) ≫ sit.affineOpen = B.inclusion.map D.toS')
        (hf : D.q.comp f = algebraMap Λ A),
        letI : Algebra Λ A' := f.toAlgebra
        letI : Algebra A' A := D.q.toAlgebra
        letI : IsScalarTower Λ A' A :=
          IsScalarTower.of_algebraMap_eq fun r =>
            (congrArg (fun g : Λ →+* A => g r) hf).symm
        obstructionEvaluation Λ A' A sit.K D.squareZeroSurjection.1
            D.squareZeroSurjection.2
            ((derivedTensorCohomology A sit.K 1).map
              (derivedNaiveCotangentComplexIso Λ A P
                (P.defaultHom (canonicalGenerators Λ A))).hom ξ₀) =
          sit.obstruction A' D := by
  let o := sit.obstruction P.toExtension.infinitesimal.Ring
    (infinitesimalThickening B S hS toS hA P.toExtension hE sit.affineOpen sit.factorization)
  let e₁ : (infinitesimalThickening B S hS toS hA P.toExtension hE sit.affineOpen
      sit.factorization).kernel ⟶ ModuleCat.of A (nlRestrict A P).X₁ :=
    infinitesimalKernelHom P.toExtension
  let e₂ : (cotangentPushoutThickening B S hS toS hA P.toExtension hC sit.affineOpen
      sit.factorization).kernel ⟶ ModuleCat.of A (nlRestrict A P).X₀ :=
    pushoutKernelHom P.toExtension
  have hcomm : (infinitesimalToPushoutHom B S hS toS hA P.toExtension hE hC sit.affineOpen
        sit.factorization).kernelMap ≫ e₂ =
      e₁ ≫ ModuleCat.ofHom (nlRestrict A P).d := by
    refine kernelHom_ext B S hS toS hA _ _ fun y => ?_
    exact squareZeroExtKernelEquiv_kerRestrict_infinitesimal P.toExtension y
  have hzero := map_obstruction_infinitesimal_eq_zero Λ A B S hS toS hA X p sit
    P.toExtension hE hC
  have hd : (derivedCohomology A sit.K 2).map (ModuleCat.ofHom (nlRestrict A P).d)
      ((derivedCohomology A sit.K 2).map e₁ o) = 0 := by
    rw [← ModuleCat.comp_apply, ← Functor.map_comp, ← hcomm, Functor.map_comp,
      ModuleCat.comp_apply, hzero, map_zero]
  obtain ⟨c, hc'⟩ := (ConcreteCategory.bijective_of_isIso
    (shiftedCohomologyIso A sit.K (ModuleCat.of A (nlRestrict A P).X₁)).hom).2
    ((derivedCohomology A sit.K 2).map e₁ o)
  have hc : derivedTensorTwoTermδ sit.K (nlRestrict A P) c = 0 := by
    refine (ConcreteCategory.congr_hom (derivedTensorTwoTermδ_eq sit.K (nlRestrict A P)) c).trans ?_
    erw [ModuleCat.comp_apply, hc']
    exact hd
  obtain ⟨ξ₀, hξ₀⟩ : ∃ ζ : (derivedTensorCohomology A sit.K 1).obj
        (DerivedCategory.Q.obj (twoTermComplex (nlRestrict A P))),
      (derivedTensorCohomology A sit.K 1).map
        (DerivedCategory.Q.map
          (twoTermProjection (ModuleCat.ofHom (nlRestrict A P).d))) ζ = c :=
    exists_of_derivedTensorTwoTermδ_eq_zero sit.K (nlRestrict A P) c hc
  refine ⟨ξ₀, ?_⟩
  intro A' _ D f hfS hqf
  let : Algebra Λ A' := f.toAlgebra
  let : Algebra A' A := D.q.toAlgebra
  let : IsScalarTower Λ A' A := IsScalarTower.of_algebraMap_eq fun r =>
    (congrArg (fun g : Λ →+* A => g r) hqf).symm
  let : Module A (RingHom.ker (algebraMap A' A)) :=
    Stacks.Smooth.kerModule D.squareZeroSurjection.1 D.squareZeroSurjection.2
  have hψ : ∀ x, algebraMap A' A (presentationLift P D.q D.squareZeroSurjection.1 f x) =
      algebraMap P.toExtension.Ring A x :=
    presentationLift_spec P D.q D.squareZeroSurjection.1 f hqf
  have hψΛ : ∀ r : Λ, presentationLift P D.q D.squareZeroSurjection.1 f
      (algebraMap Λ P.toExtension.Ring r) = algebraMap Λ A' r := by
    have h : ∀ s : Λ, MvPolynomial.eval₂Hom f
        (fun i => (D.squareZeroSurjection.1 (P.val i)).choose)
        (algebraMap Λ P.Ring s) = f s := fun s => by simp
    exact h
  let k : P.toExtension.Cotangent →ₗ[A] RingHom.ker (algebraMap A' A) :=
    presentationKernelMap P D.q D.squareZeroSurjection f hqf
  have hbridge := derivedNaiveCotangentComplexIso_hom_comp_cotangentExtensionClass
    P (P.defaultHom (canonicalGenerators Λ A)) D.squareZeroSurjection.1
    D.squareZeroSurjection.2 (presentationLift P D.q D.squareZeroSurjection.1 f) hψ hψΛ
    k (presentationKernelMap_mk P D.q D.squareZeroSurjection f hqf)
  have hek : e₁ ≫ ModuleCat.ofHom k =
      (infinitesimalToThickeningHom B S hS toS hA P hE sit.affineOpen sit.factorization
        D f hfS hqf).kernelMap := by
    refine kernelHom_ext B S hS toS hA _ _ fun y => ?_
    have hy : (infinitesimalKernelEquiv P.toExtension).symm
        ((infinitesimalKernelEquiv P.toExtension) y) = y :=
      (infinitesimalKernelEquiv P.toExtension).symm_apply_apply y
    have h1 : (e₁ ≫ ModuleCat.ofHom k).hom y =
        kerRestrict (isDeformationSituation_infinitesimal P.toExtension)
            D.squareZeroSurjection
            (infinitesimalLift P D.q D.squareZeroSurjection.1 f hqf
              D.squareZeroSurjection.2)
            (comp_infinitesimalLift P D.q D.squareZeroSurjection.1 f hqf
              D.squareZeroSurjection.2)
          ((infinitesimalKernelEquiv P.toExtension).symm
            ((infinitesimalKernelEquiv P.toExtension) y)) := rfl
    have h2 : ((infinitesimalToThickeningHom B S hS toS hA P hE sit.affineOpen
          sit.factorization D f hfS hqf).kernelMap).hom y =
        kerRestrict (isDeformationSituation_infinitesimal P.toExtension)
            D.squareZeroSurjection
            (infinitesimalLift P D.q D.squareZeroSurjection.1 f hqf
              D.squareZeroSurjection.2)
            (comp_infinitesimalLift P D.q D.squareZeroSurjection.1 f hqf
              D.squareZeroSurjection.2) y := rfl
    rw [h1, h2, hy]
  have hnat := sit.obstructionNatural P.toExtension.infinitesimal.Ring A'
    (infinitesimalThickening B S hS toS hA P.toExtension hE sit.affineOpen
      sit.factorization) D
    (infinitesimalToThickeningHom B S hS toS hA P hE sit.affineOpen sit.factorization
      D f hfS hqf)
  have hs1 : (derivedTensorCohomology A sit.K 1).map
        (cotangentExtensionClass Λ A' A D.squareZeroSurjection.1
          D.squareZeroSurjection.2)
        ((derivedTensorCohomology A sit.K 1).map
          (derivedNaiveCotangentComplexIso Λ A P
            (P.defaultHom (canonicalGenerators Λ A))).hom ξ₀) =
      (derivedTensorCohomology A sit.K 1).map
        (DerivedCategory.Q.map
            (twoTermProjection (ModuleCat.ofHom (nlRestrict A P).d)) ≫
          (DerivedCategory.singleFunctor (ModuleCat.{u} A) (-1)).map
            (ModuleCat.ofHom k)) ξ₀ := by
    rw [← ModuleCat.comp_apply, ← Functor.map_comp, hbridge]
  have hc₂ : (shiftedCohomologyIso A sit.K
        (ModuleCat.of A P.toExtension.Cotangent)).hom c =
      (derivedCohomology A sit.K 2).map e₁ o := hc'
  have hgoal : (shiftedCohomologyIso A sit.K
        (ModuleCat.of A (RingHom.ker (algebraMap A' A)))).hom
      ((derivedTensorCohomology A sit.K 1).map
        (cotangentExtensionClass Λ A' A D.squareZeroSurjection.1
          D.squareZeroSurjection.2)
        ((derivedTensorCohomology A sit.K 1).map
          (derivedNaiveCotangentComplexIso Λ A P
            (P.defaultHom (canonicalGenerators Λ A))).hom ξ₀)) =
      sit.obstruction A' D := by
    rw [hs1, Functor.map_comp, ModuleCat.comp_apply, hξ₀, ← ModuleCat.comp_apply,
      shiftedCohomologyIso_naturality A sit.K (ModuleCat.ofHom k),
      ModuleCat.comp_apply, hc₂, ← ModuleCat.comp_apply, ← Functor.map_comp, hek]
    exact hnat
  exact hgoal

/-- There is a class `ξ` in `H¹(K ⊗ᴸ NL_{A/Λ})` such that every square-zero thickening
`D : A' → A` of the situation `sit` admits a ring map `Λ → A'` compatible with `sit.affineOpen`
and with `Λ → A`, along which the evaluation `obstructionEvaluation` of `ξ` is the obstruction
element `sit.obstruction A' D`. -/
@[stacks 07YY "clause (1) alone, and WITHOUT the boundary condition (iv): a single class ξ \
on NL_{A/Λ} whose canonical evaluation `obstructionEvaluation` at every deformation \
situation is that situation's obstruction element. The whole tag — clause (1) together with \
clause (2), that ξ's image in H¹(K ⊗ᴸ Ω_{A/Λ}) is the canonical element of the tangent \
functor — is `Deformation.Artin.exists_isCotangentObstructionClass`, which assumes (iv) and \
whose conclusion is `Deformation.Artin.IsCotangentObstructionClass`, the full conjunction. \
This theorem is kept beside it because clause (1) needs no hypothesis: the class it produces \
is adjusted there by an element of H¹(K ⊗ᴸ Ω_{P/Λ} ⊗_P A) to achieve clause (2), an \
adjustment clause (1) cannot see because `mor₁ ≫ mor₂ = 0`."]
public theorem exists_obstructionEvaluation_eq_obstruction :
    ∃ ξ : (derivedTensorCohomology A sit.K 1).obj (derivedNaiveCotangentComplex Λ A),
      ∀ (A' : Type u) [CommRing A'] (D : SquareZeroThickening A B S hS toS hA A'),
        ∃ f : Λ →+* A',
          Spec.map (CommRingCat.ofHom f) ≫ sit.affineOpen = B.inclusion.map D.toS' ∧
          ∃ hf : D.q.comp f = algebraMap Λ A,
          letI : Algebra Λ A' := f.toAlgebra
          letI : Algebra A' A := D.q.toAlgebra
          letI : IsScalarTower Λ A' A :=
            IsScalarTower.of_algebraMap_eq fun r =>
              (congrArg (fun g : Λ →+* A => g r) hf).symm
          obstructionEvaluation Λ A' A sit.K D.squareZeroSurjection.1
              D.squareZeroSurjection.2 ξ = sit.obstruction A' D := by
  obtain ⟨ι, hfin, ⟨P⟩⟩ := exists_finite_generators (Λ := Λ) (A := A) sit.finiteType
  have : Finite ι := hfin
  have hΛ : B.Contains (Spec (.of Λ)) :=
    contains_of_isOpenImmersion B sit.affineOpen sit.openImmersion hS
  have hE : B.Contains (Spec (.of P.Ring)) := presentation_mem_site_of_finite P B hΛ
  have hC : B.Contains (Spec (.of (cotangentPushout P.toExtension))) :=
    cotangentPushout_mem_site_of_finite P B hA
  obtain ⟨ξ₀, hξ₀⟩ := exists_obstructionEvaluation_eq_obstruction_of_presentation Λ A B S hS
    toS hA X p sit P hE hC
  refine ⟨(derivedTensorCohomology A sit.K 1).map
    (derivedNaiveCotangentComplexIso Λ A P (P.defaultHom (canonicalGenerators Λ A))).hom ξ₀,
    ?_⟩
  intro A' _ D
  obtain ⟨f, hfS, hqf⟩ := exists_baseRingHom B S hS toS hA D sit.affineOpen
    sit.openImmersion sit.factorization
  exact ⟨f, hfS, hqf, hξ₀ A' D f hfS hqf⟩

end ClauseOne

end Deformation.Artin

end
