module

public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentHomologyZero
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangentTower
public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentPushforwardSectionsH1

/-!
# The cokernel of the differential of `NL_{B/A}` corepresents derivations

For a morphism `a : A ⟶ B` of sheaves of commutative rings on a site, the cokernel of the only
nonzero differential `d : NL_{B/A}^{-1} ⟶ NL_{B/A}^0` of the naive cotangent complex is the
sheaf of relative differentials `Ω_{B/A}` (Stacks 08TY in degree `0`).  This file transports the
universal property of `Ω_{B/A}` (Stacks 04BL) to that cokernel, and computes the universal
derivation on generators: it sends a local section `b` of `B` to the class of `1 ⊗ d[b]`, the
differential of the variable `[b]` of the polynomial algebra `A[B]`.

This is the form in which the comparison of cokernels in Stacks 0D0X is tested: a morphism out
of the cokernel is a derivation, and the class of `1 ⊗ d[b]` is what the chain maps between
naive cotangent complexes are computed on.

## Main definitions

* `Stacks.SheafOfModules.naiveCotangentCokernelIso`: `coker d ≅ Ω_{B/A}`.
* `Stacks.SheafOfModules.naiveCotangentCokernelDerivation`: the universal derivation of `B` over
  `A` with values in `coker d`.

## Main results

* `Stacks.SheafOfModules.existsUnique_naiveCotangentCokernelDerivation`: every derivation of `B`
  over `A` with values in a sheaf of modules factors uniquely through it.
* `Stacks.SheafOfModules.naiveCotangentCokernelDerivation_d`: it sends `b` to the class of
  `1 ⊗ d[b]`.

## References

* [Stacks Project, Tag 08TY](https://stacks.math.columbia.edu/tag/08TY)
* [Stacks Project, Tag 04BL](https://stacks.math.columbia.edu/tag/04BL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v₀ u₀ v u w z

namespace Stacks.SheafOfModules

open AlgebraicGeometry.SheafOfModules (moduleOfDifferentialsOfSite universalDerivationOfSite)
open Stacks.Sites.FreeAlgebra (freeAlgebraSheaf underlyingPresheaf freeAlgebraSheafCoefficientMap
  canonicalPresentation)

/-- Moving a local section along an equality of sheaves of modules and back. -/
theorem eqToHom_comp_val_app_eqToHom_symm {C' : Type*} [Category C'] {J' : GrothendieckTopology C'}
    {R : Sheaf J' RingCat.{w}}
    {M N P : _root_.SheafOfModules.{z} R} (h : M = N) (g : N ⟶ P) (X : C'ᵒᵖ) (t : N.val.obj X) :
    (eqToHom h ≫ g).val.app X ((eqToHom h.symm).val.app X t) = g.val.app X t := by
  subst h
  rfl

section Cokernel

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J CommRingCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (A B : Sheaf J CommRingCat.{w}) (a : A ⟶ B)
  [HasSheafify J AddCommGrpCat.{max w u v z}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w u v z}]

/-- The cokernel of the differential of `NL_{B/A}` is the cokernel of the conormal map. -/
noncomputable def naiveCotangentCokernelIsoConormal :
    cokernel ((naiveCotangentComplex.{v, u, w, z} J A B a).d (-1) 0) ≅
      cokernel (canonicalConormalSequence.{v, u, w, z} J A B a).f :=
  cokernel.mapIso _ _ (eqToIso (naiveCotangentComplex_X_negOne.{v, u, w, z} J A B a))
    (eqToIso (naiveCotangentComplex_X_zero.{v, u, w, z} J A B a))
    (by simp [naiveCotangentComplex_d_negOne_zero])

/-- **The cokernel of the differential of `NL_{B/A}` is `Ω_{B/A}`.** -/
noncomputable def naiveCotangentCokernelIso :
    cokernel ((naiveCotangentComplex.{v, u, w, z} J A B a).d (-1) 0) ≅
      moduleOfDifferentialsOfSite.{v, u, w, z} A B a :=
  naiveCotangentCokernelIsoConormal.{v, u, w, z} J A B a ≪≫
    cokernelCanonicalConormalSequenceIso.{v, u, w, z} J A B a ≪≫
    Stacks.Sites.Conormal.imageDifferentialsIso.{v, u, w, z} J A
      (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
      (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B))
      (canonicalPresentation J A B a) ≪≫
    eqToIso (congrArg (fun φ ↦ moduleOfDifferentialsOfSite.{v, u, w, z} A B φ)
      (Stacks.Sites.FreeAlgebra.canonicalPresentation_comp_coefficientMap J A B a))

/-- **The universal derivation of `B` over `A` with values in the cokernel of the differential of
`NL_{B/A}`.** -/
noncomputable def naiveCotangentCokernelDerivation :
    (cokernel ((naiveCotangentComplex.{v, u, w, z} J A B a).d (-1) 0)).val.Derivation' a.hom :=
  (universalDerivationOfSite.{v, u, w, z} A B a).postcomp
    (naiveCotangentCokernelIso.{v, u, w, z} J A B a).inv.val

/-- **The cokernel of the differential of `NL_{B/A}` corepresents derivations**: every derivation
of `B` over `A` with values in a sheaf of modules factors through
`Stacks.SheafOfModules.naiveCotangentCokernelDerivation` by a unique morphism. -/
theorem existsUnique_naiveCotangentCokernelDerivation
    (F : _root_.SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B))
    (D : F.val.Derivation' a.hom) :
    ∃! g : cokernel ((naiveCotangentComplex.{v, u, w, z} J A B a).d (-1) 0) ⟶ F,
      (naiveCotangentCokernelDerivation.{v, u, w, z} J A B a).postcomp g.val = D := by
  obtain ⟨f, hf, hu⟩ :=
    AlgebraicGeometry.SheafOfModules.existsUnique_descDerivation.{v, u, w, z} A B a F D
  refine ⟨(naiveCotangentCokernelIso.{v, u, w, z} J A B a).hom ≫ f, ?_, fun g hg => ?_⟩
  · refine Eq.trans ?_ hf
    ext X x
    exact congrArg (fun m : moduleOfDifferentialsOfSite.{v, u, w, z} A B a ⟶ F =>
      m.val.app X ((universalDerivationOfSite.{v, u, w, z} A B a).d x))
      (Iso.inv_hom_id_assoc (naiveCotangentCokernelIso.{v, u, w, z} J A B a) f)
  · have h := hu ((naiveCotangentCokernelIso.{v, u, w, z} J A B a).inv ≫ g) (Eq.trans (by
      ext X x; rfl) hg)
    rw [← h, Iso.hom_inv_id_assoc]

/-- Morphisms out of the cokernel of the differential of `NL_{B/A}` are derivations: composing
with `Stacks.SheafOfModules.naiveCotangentCokernelDerivation` is a bijection. -/
theorem bijective_postcomp_naiveCotangentCokernelDerivation
    (F : _root_.SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B)) :
    Function.Bijective (fun g : cokernel ((naiveCotangentComplex.{v, u, w, z} J A B a).d (-1) 0) ⟶
      F ↦ (naiveCotangentCokernelDerivation.{v, u, w, z} J A B a).postcomp g.val) := by
  refine ⟨fun g₁ g₂ h => ?_, fun D => ?_⟩
  · obtain ⟨g, -, hg⟩ := existsUnique_naiveCotangentCokernelDerivation.{v, u, w, z} J A B a F
      ((naiveCotangentCokernelDerivation.{v, u, w, z} J A B a).postcomp g₁.val)
    exact (hg g₁ rfl).trans (hg g₂ h.symm).symm
  · obtain ⟨g, hg, -⟩ := existsUnique_naiveCotangentCokernelDerivation.{v, u, w, z} J A B a F D
    exact ⟨g, hg⟩

omit [HasWeakSheafify J CommRingCat.{w}] [HasSheafify J AddCommGrpCat.{max w u v z}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w u v z}] in
/-- Transport of the universal derivation along an equality of ring maps. -/
theorem eqToIso_moduleOfDifferentialsOfSite_universalDerivationOfSite_d {φ₁ φ₂ : A ⟶ B}
    (h : φ₁ = φ₂) (X : Cᵒᵖ) (b : B.obj.obj X) :
    (eqToIso (congrArg (fun φ ↦ moduleOfDifferentialsOfSite.{v, u, w, z} A B φ) h)).hom.val.app X
        ((universalDerivationOfSite.{v, u, w, z} A B φ₁).d b) =
      (universalDerivationOfSite.{v, u, w, z} A B φ₂).d b := by
  subst h
  rfl

/-- The local section `1 ⊗ d[b]` of `NL_{B/A}^0`, for `[b]` the variable of `A[B]` attached to a
local section `b` of `B`. -/
noncomputable def naiveCotangentVariableDifferential (X : Cᵒᵖ) (b : B.obj.obj X) :
    ((naiveCotangentComplex.{v, u, w, z} J A B a).X 0).val.obj X :=
  have : Presheaf.IsLocallySurjective J (canonicalPresentation J A B a).hom :=
    (Presheaf.isLocallySurjective_iff_whisker_forget J _).mpr
      (Stacks.Sites.FreeAlgebra.canonicalPresentation_isLocallySurjective J A B a)
  (eqToHom (naiveCotangentComplex_X_zero.{v, u, w, z} J A B a).symm).val.app X
    (Stacks.Sites.Conormal.tensorDifferential.{v, u, w, z} J A
      (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
      (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B))
      (canonicalPresentation J A B a) X (variableSection J A B X b))

/-- The projection to the cokernel followed by `coker d ≅ Ω_{B/A}`, on `NL_{B/A}^0` written as the
middle term of the conormal sequence, is the right-hand map of the conormal sequence followed by
the identification of its target with `Ω_{B/A}`. -/
theorem eqToHom_π_naiveCotangentCokernelIso_hom :
    eqToHom (naiveCotangentComplex_X_zero.{v, u, w, z} J A B a).symm ≫
        cokernel.π ((naiveCotangentComplex.{v, u, w, z} J A B a).d (-1) 0) ≫
        (naiveCotangentCokernelIso.{v, u, w, z} J A B a).hom =
      (canonicalConormalSequence.{v, u, w, z} J A B a).g ≫
        (Stacks.Sites.Conormal.imageDifferentialsIso.{v, u, w, z} J A
          (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
          (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B))
          (canonicalPresentation J A B a)).hom ≫
        (eqToIso (congrArg (fun φ ↦ moduleOfDifferentialsOfSite.{v, u, w, z} A B φ)
          (Stacks.Sites.FreeAlgebra.canonicalPresentation_comp_coefficientMap J A B a))).hom := by
  have h₁ : cokernel.π ((naiveCotangentComplex.{v, u, w, z} J A B a).d (-1) 0) ≫
      (naiveCotangentCokernelIsoConormal.{v, u, w, z} J A B a).hom =
      eqToHom (naiveCotangentComplex_X_zero.{v, u, w, z} J A B a) ≫
        cokernel.π (canonicalConormalSequence.{v, u, w, z} J A B a).f := by
    simp [naiveCotangentCokernelIsoConormal]
  have h₂ : cokernel.π (canonicalConormalSequence.{v, u, w, z} J A B a).f ≫
      (cokernelCanonicalConormalSequenceIso.{v, u, w, z} J A B a).hom =
      (canonicalConormalSequence.{v, u, w, z} J A B a).g := by
    unfold cokernelCanonicalConormalSequenceIso
    exact IsColimit.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel _)
      (Stacks.Sites.Conormal.conormalSequence_exact.{v, u, w, z} J A
        (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
        (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B))
        (canonicalPresentation J A B a)).gIsCokernel WalkingParallelPair.one
  simp only [naiveCotangentCokernelIso, Iso.trans_hom, ← Category.assoc, h₁]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [reassoc_of% h₂]

/-- **The universal derivation into the cokernel sends `b` to the class of `1 ⊗ d[b]`.** -/
theorem naiveCotangentCokernelDerivation_d (X : Cᵒᵖ) (b : B.obj.obj X) :
    (naiveCotangentCokernelDerivation.{v, u, w, z} J A B a).d b =
      (cokernel.π ((naiveCotangentComplex.{v, u, w, z} J A B a).d (-1) 0)).val.app X
        (naiveCotangentVariableDifferential.{v, u, w, z} J A B a X b) := by
  have h : (naiveCotangentCokernelIso.{v, u, w, z} J A B a).hom.val.app X
      ((cokernel.π ((naiveCotangentComplex.{v, u, w, z} J A B a).d (-1) 0)).val.app X
        (naiveCotangentVariableDifferential.{v, u, w, z} J A B a X b)) =
      (universalDerivationOfSite.{v, u, w, z} A B a).d b := by
    refine (congrArg (fun m => m.val.app X (Stacks.Sites.Conormal.tensorDifferential.{v, u, w, z}
      J A (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
      (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B))
      (canonicalPresentation J A B a) X (variableSection J A B X b)))
      (eqToHom_π_naiveCotangentCokernelIso_hom.{v, u, w, z} J A B a)).trans ?_
    show (eqToIso (congrArg (fun φ ↦ moduleOfDifferentialsOfSite.{v, u, w, z} A B φ)
          (Stacks.Sites.FreeAlgebra.canonicalPresentation_comp_coefficientMap J A B a))).hom.val.app
        X ((Stacks.Sites.Conormal.imageDifferentialsIso.{v, u, w, z} J A
          (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
          (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B))
          (canonicalPresentation J A B a)).hom.val.app X
        (((canonicalConormalSequence.{v, u, w, z} J A B a).g.val.app X)
          (Stacks.Sites.Conormal.tensorDifferential.{v, u, w, z} J A
            (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
            (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B))
            (canonicalPresentation J A B a) X (variableSection J A B X b)))) = _
    rw [Stacks.Sites.Conormal.conormalSequence_g_differential,
      Stacks.Sites.Conormal.imageDifferentialsIso_d,
      eqToIso_moduleOfDifferentialsOfSite_universalDerivationOfSite_d J A B
        (Stacks.Sites.FreeAlgebra.canonicalPresentation_comp_coefficientMap J A B a),
      canonicalPresentation_variableSection]
  show (naiveCotangentCokernelIso.{v, u, w, z} J A B a).inv.val.app X
    ((universalDerivationOfSite.{v, u, w, z} A B a).d b) = _
  rw [← h]
  exact congrArg (fun m => m.val.app X
      ((cokernel.π ((naiveCotangentComplex.{v, u, w, z} J A B a).d (-1) 0)).val.app X
        (naiveCotangentVariableDifferential.{v, u, w, z} J A B a X b)))
    (naiveCotangentCokernelIso.{v, u, w, z} J A B a).hom_inv_id

end Cokernel

section Pushforward

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J CommRingCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (A B : Sheaf J CommRingCat.{w}) (a : A ⟶ B)
  [HasSheafify J AddCommGrpCat.{max w u₀ v₀ u v z}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w u₀ v₀ u v z}]

variable {C₀ : Type u₀} [Category.{v₀} C₀] (J₀ : GrothendieckTopology C₀) (F : C₀ ⥤ C)
  [F.IsContinuous J₀ J] [HasWeakSheafify J₀ CommRingCat.{w}]
  [J₀.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasSheafify J₀ AddCommGrpCat.{max w u₀ v₀ u v z}]
  [J₀.WEqualsLocallyBijective AddCommGrpCat.{max w u₀ v₀ u v z}]
  (A₀ B₀ : Sheaf J₀ CommRingCat.{w}) (a₀ : A₀ ⟶ B₀)
  (ψ : A₀ ⟶ (F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj A)
  (β : B₀ ⟶ (F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj B)
  (hsq : a₀ ≫ β = ψ ≫ (F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map a)

omit [HasSheafify J AddCommGrpCat.{max w u₀ v₀ u v z}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w u₀ v₀ u v z}]
  [HasSheafify J₀ AddCommGrpCat.{max w u₀ v₀ u v z}]
  [J₀.WEqualsLocallyBijective AddCommGrpCat.{max w u₀ v₀ u v z}] in
include hsq in
/-- **The chain map `NL_{B₀/A₀} ⟶ F_*NL_{B/A}` of a square on `1 ⊗ d[b]`**: in degree `0` it sends
`1 ⊗ d[b]` over `X` to `1 ⊗ d[β b]` over `F(X)`. -/
theorem naiveCotangentComplexPushforwardSquareMap_f_zero_variableDifferential (X : C₀ᵒᵖ)
    (b : B₀.obj.obj X) :
    ((naiveCotangentComplexPushforwardSquareMap.{v₀, u₀, v, u, w, z} J₀ J F A B a A₀ B₀ a₀ ψ β
        hsq).f 0).val.app X
        (naiveCotangentVariableDifferential.{v₀, u₀, w, max u v z} J₀ A₀ B₀ a₀ X b) =
      naiveCotangentVariableDifferential.{v, u, w, max u₀ v₀ z} J A B a (Opposite.op (F.obj X.unop))
        (β.hom.app X b) := by
  have hvar : ((pushforwardFreeAlgebraMap J₀ J F A B).hom.app X).hom
      (((Stacks.SheafOfModules.canonicalFreeAlgebraMapOfSquare J₀ A₀
        ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj A) B₀
        ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj B) ψ β).hom.app X).hom
        (variableSection J₀ A₀ B₀ X b)) =
      variableSection J A B (Opposite.op (F.obj X.unop)) ((β.hom.app X).hom b) := by
    have h := pushforwardFreeAlgebraMap_freeAlgebraSectionsMap J₀ J F A B A₀ B₀ ψ β X
      (MvPolynomial.X b)
    rw [MvPolynomial.eval₂Hom_X'] at h
    exact h
  rw [naiveCotangentComplexPushforwardSquareMap_f_zero]
  refine (eqToHom_comp_val_app_eqToHom_symm _ _ X _).trans ?_
  show (eqToHom (naiveCotangentComplex_X_zero.{v, u, w, max u₀ v₀ z} J A B a).symm).val.app
    (Opposite.op (F.obj X.unop))
    ((conormalPushforwardTensorMap.{v₀, u₀, v, u, w, z} J₀ J F A B a).val.app X
    ((naiveCotangentTensorMapOfSquare.{v₀, u₀, w, max u v z} J₀ A₀ B₀ a₀ _ _ _ ψ β hsq).val.app X
      _)) = _
  unfold naiveCotangentTensorMapOfSquare
  refine (congrArg (fun y => (eqToHom (naiveCotangentComplex_X_zero.{v, u, w, max u₀ v₀ z} J A B
    a).symm).val.app (Opposite.op (F.obj X.unop))
      ((conormalPushforwardTensorMap.{v₀, u₀, v, u, w, z} J₀ J F A B a).val.app X y))
    (Stacks.Sites.Conormal.tensorSheafMapOfSquare_tensorDifferential (J := J₀) (X := X) ..)).trans
    ?_
  rw [conormalPushforwardTensorMap_tensorDifferential]
  exact congrArg (fun y => (eqToHom (naiveCotangentComplex_X_zero.{v, u, w, max u₀ v₀ z} J A B
    a).symm).val.app (Opposite.op (F.obj X.unop)) (Stacks.Sites.Conormal.tensorDifferential J A
      (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
      (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B))
      (canonicalPresentation J A B a) (Opposite.op (F.obj X.unop)) y)) hvar

include hsq in
/-- **A derivation restricted along a square.**  A derivation `D` of `B` over `A` with values in a
sheaf of `B`-modules `T` on `C` gives the derivation `b ↦ D(β b)` of `B₀` over `A₀` with values
in `F_*T`, read over `B₀` along `β`. -/
def derivationPushforwardOfSquare
    {T : _root_.SheafOfModules.{max w u₀ v₀ u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B)}
    (D : T.val.Derivation' a.hom) :
    ((_root_.SheafOfModules.pushforward.{max w u₀ v₀ u v z}
      (pushforwardRingHomOfSquare J₀ J F B B₀ β)).obj T).val.Derivation' a₀.hom where
  d {X} := (D.d (X := Opposite.op (F.obj X.unop))).comp (β.hom.app X).hom.toAddMonoidHom
  d_mul {X} x y := (congrArg D.d (map_mul (β.hom.app X).hom x y)).trans (D.d_mul _ _)
  d_map g x := (congrArg D.d (ConcreteCategory.congr_hom (β.hom.naturality g) x)).trans
    (D.d_map _ _)
  d_app {X} r := (congrArg D.d (ConcreteCategory.congr_hom
    (congrArg (fun m => m.hom.app X) hsq) r)).trans (D.d_app _)

include hsq in
/-- **The map induced on the cokernels by the chain map of a square is the restriction of
derivations.**  If `κ : coker d₀ ⟶ F_*(coker d)` is induced by the degree `0` part of
`NL_{B₀/A₀} ⟶ F_*NL_{B/A}`, then for every `h : coker d ⟶ T` the derivation corresponding to
`κ ≫ F_*h` is the restriction along the square of the derivation corresponding to `h`. -/
theorem naiveCotangentCokernelDerivation_postcomp_pushforward
    {T : _root_.SheafOfModules.{max w u₀ v₀ u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B)}
    (κ : cokernel ((naiveCotangentComplex.{v₀, u₀, w, max u v z} J₀ A₀ B₀ a₀).d (-1) 0) ⟶
      (_root_.SheafOfModules.pushforward.{max w u₀ v₀ u v z}
        (pushforwardRingHomOfSquare J₀ J F B B₀ β)).obj
        (cokernel ((naiveCotangentComplex.{v, u, w, max u₀ v₀ z} J A B a).d (-1) 0)))
    (hκ : cokernel.π _ ≫ κ =
      (naiveCotangentComplexPushforwardSquareMap.{v₀, u₀, v, u, w, z} J₀ J F A B a A₀ B₀ a₀ ψ β
        hsq).f 0 ≫ (_root_.SheafOfModules.pushforward.{max w u₀ v₀ u v z}
          (pushforwardRingHomOfSquare J₀ J F B B₀ β)).map (cokernel.π _))
    (h : cokernel ((naiveCotangentComplex.{v, u, w, max u₀ v₀ z} J A B a).d (-1) 0) ⟶ T) :
    (naiveCotangentCokernelDerivation.{v₀, u₀, w, max u v z} J₀ A₀ B₀ a₀).postcomp
        (κ ≫ (_root_.SheafOfModules.pushforward.{max w u₀ v₀ u v z}
          (pushforwardRingHomOfSquare J₀ J F B B₀ β)).map h).val =
      derivationPushforwardOfSquare.{v₀, u₀, v, u, w, z} J A B a J₀ F A₀ B₀ a₀ ψ β hsq
        ((naiveCotangentCokernelDerivation.{v, u, w, max u₀ v₀ z} J A B a).postcomp h.val) := by
  ext X x
  show (κ ≫ (_root_.SheafOfModules.pushforward.{max w u₀ v₀ u v z}
      (pushforwardRingHomOfSquare J₀ J F B B₀ β)).map h).val.app X
      ((naiveCotangentCokernelDerivation.{v₀, u₀, w, max u v z} J₀ A₀ B₀ a₀).d x) =
    h.val.app (Opposite.op (F.obj X.unop))
      ((naiveCotangentCokernelDerivation.{v, u, w, max u₀ v₀ z} J A B a).d ((β.hom.app X).hom x))
  rw [naiveCotangentCokernelDerivation_d]
  refine Eq.trans ?_ (congrArg (fun t => h.val.app (Opposite.op (F.obj X.unop)) t)
    ((naiveCotangentCokernelDerivation_d J A B a (Opposite.op (F.obj X.unop))
      ((β.hom.app X).hom x)).trans (congrArg (fun t => (cokernel.π ((naiveCotangentComplex.{v, u, w,
        max u₀ v₀ z} J A B a).d (-1) 0)).val.app (Opposite.op (F.obj X.unop)) t)
      (naiveCotangentComplexPushforwardSquareMap_f_zero_variableDifferential J A B a J₀ F A₀ B₀
        a₀ ψ β hsq X x).symm))).symm
  exact congrArg (fun m => m.val.app X
      (naiveCotangentVariableDifferential.{v₀, u₀, w, max u v z} J₀ A₀ B₀ a₀ X x))
    (show cokernel.π _ ≫ κ ≫ (_root_.SheafOfModules.pushforward.{max w u₀ v₀ u v z}
        (pushforwardRingHomOfSquare J₀ J F B B₀ β)).map h = _ from by
      rw [reassoc_of% hκ, ← Functor.map_comp])

include hsq in
/-- **Bijectivity on cokernels is bijectivity of the restriction of derivations.** -/
theorem bijective_comp_pushforward_map_iff
    (T : _root_.SheafOfModules.{max w u₀ v₀ u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B))
    (κ : cokernel ((naiveCotangentComplex.{v₀, u₀, w, max u v z} J₀ A₀ B₀ a₀).d (-1) 0) ⟶
      (_root_.SheafOfModules.pushforward.{max w u₀ v₀ u v z}
        (pushforwardRingHomOfSquare J₀ J F B B₀ β)).obj
        (cokernel ((naiveCotangentComplex.{v, u, w, max u₀ v₀ z} J A B a).d (-1) 0)))
    (hκ : cokernel.π _ ≫ κ =
      (naiveCotangentComplexPushforwardSquareMap.{v₀, u₀, v, u, w, z} J₀ J F A B a A₀ B₀ a₀ ψ β
        hsq).f 0 ≫ (_root_.SheafOfModules.pushforward.{max w u₀ v₀ u v z}
          (pushforwardRingHomOfSquare J₀ J F B B₀ β)).map (cokernel.π _)) :
    Function.Bijective (fun h : cokernel ((naiveCotangentComplex.{v, u, w, max u₀ v₀ z} J A B
        a).d (-1) 0) ⟶ T ↦ κ ≫ (_root_.SheafOfModules.pushforward.{max w u₀ v₀ u v z}
          (pushforwardRingHomOfSquare J₀ J F B B₀ β)).map h) ↔
      Function.Bijective (fun D : T.val.Derivation' a.hom ↦
        derivationPushforwardOfSquare.{v₀, u₀, v, u, w, z} J A B a J₀ F A₀ B₀ a₀ ψ β hsq D) := by
  rw [← (bijective_postcomp_naiveCotangentCokernelDerivation.{v₀, u₀, w, max u v z} J₀ A₀ B₀ a₀
      _).of_comp_iff',
    ← Function.Bijective.of_comp_iff _
      (bijective_postcomp_naiveCotangentCokernelDerivation.{v, u, w, max u₀ v₀ z} J A B a T)]
  have key : ((fun g ↦ (naiveCotangentCokernelDerivation.{v₀, u₀, w, max u v z} J₀ A₀ B₀
      a₀).postcomp g.val) ∘ fun h : cokernel ((naiveCotangentComplex.{v, u, w, max u₀ v₀ z} J A B
        a).d (-1) 0) ⟶ T ↦ κ ≫ (_root_.SheafOfModules.pushforward.{max w u₀ v₀ u v z}
          (pushforwardRingHomOfSquare J₀ J F B B₀ β)).map h) =
      (fun D : T.val.Derivation' a.hom ↦
        derivationPushforwardOfSquare.{v₀, u₀, v, u, w, z} J A B a J₀ F A₀ B₀ a₀ ψ β hsq D) ∘
        fun g ↦ (naiveCotangentCokernelDerivation.{v, u, w, max u₀ v₀ z} J A B a).postcomp
          g.val :=
    funext fun h => naiveCotangentCokernelDerivation_postcomp_pushforward J A B a J₀ F A₀ B₀ a₀
      ψ β hsq κ hκ h
  rw [key]

include hsq in
/-- `Stacks.SheafOfModules.bijective_comp_pushforward_map_iff` with the two complexes, the
pushforward functor and the chain map as free data identified with the canonical ones by
equations: in this form it applies to any spelling of them without unfolding. -/
theorem bijective_comp_map_iff_of_eq
    {K₀ : CochainComplex (_root_.SheafOfModules.{max w u₀ v₀ u v z}
      (Stacks.SheafOfModules.Tensor.ringSheaf B₀)) ℤ}
    {K : CochainComplex (_root_.SheafOfModules.{max w u₀ v₀ u v z}
      (Stacks.SheafOfModules.Tensor.ringSheaf B)) ℤ}
    (hK₀ : K₀ = naiveCotangentComplex.{v₀, u₀, w, max u v z} J₀ A₀ B₀ a₀)
    (hK : K = naiveCotangentComplex.{v, u, w, max u₀ v₀ z} J A B a)
    {G : _root_.SheafOfModules.{max w u₀ v₀ u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B) ⥤
      _root_.SheafOfModules.{max w u₀ v₀ u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B₀)}
    (hG : G = _root_.SheafOfModules.pushforward.{max w u₀ v₀ u v z}
      (pushforwardRingHomOfSquare J₀ J F B B₀ β)) [G.PreservesZeroMorphisms]
    (bm : K₀ ⟶ (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
    (hbm : HEq bm (naiveCotangentComplexPushforwardSquareMap.{v₀, u₀, v, u, w, z} J₀ J F A B a A₀
      B₀ a₀ ψ β hsq))
    (T : _root_.SheafOfModules.{max w u₀ v₀ u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B))
    (κ : cokernel (K₀.d (-1) 0) ⟶ G.obj (cokernel (K.d (-1) 0)))
    (hκ : cokernel.π _ ≫ κ = bm.f 0 ≫ G.map (cokernel.π _)) :
    Function.Bijective (fun h : cokernel (K.d (-1) 0) ⟶ T ↦ κ ≫ G.map h) ↔
      Function.Bijective (fun D : T.val.Derivation' a.hom ↦
        derivationPushforwardOfSquare.{v₀, u₀, v, u, w, z} J A B a J₀ F A₀ B₀ a₀ ψ β hsq D) := by
  subst hK₀ hK hG
  obtain rfl := eq_of_heq hbm
  exact bijective_comp_pushforward_map_iff J A B a J₀ F A₀ B₀ a₀ ψ β hsq T κ hκ

omit [HasWeakSheafify J CommRingCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasSheafify J AddCommGrpCat.{max w u₀ v₀ u v z}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w u₀ v₀ u v z}]
  [HasWeakSheafify J₀ CommRingCat.{w}]
  [J₀.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasSheafify J₀ AddCommGrpCat.{max w u₀ v₀ u v z}]
  [J₀.WEqualsLocallyBijective AddCommGrpCat.{max w u₀ v₀ u v z}] in
include hsq in
/-- Restricting a derivation along the square commutes with composing with a morphism of
sheaves of modules. -/
theorem derivationPushforwardOfSquare_postcomp
    {T T' : _root_.SheafOfModules.{max w u₀ v₀ u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B)}
    (D : T.val.Derivation' a.hom) (m : T ⟶ T') :
    derivationPushforwardOfSquare.{v₀, u₀, v, u, w, z} J A B a J₀ F A₀ B₀ a₀ ψ β hsq
        (D.postcomp m.val) =
      (derivationPushforwardOfSquare.{v₀, u₀, v, u, w, z} J A B a J₀ F A₀ B₀ a₀ ψ β hsq D).postcomp
        ((_root_.SheafOfModules.pushforward.{max w u₀ v₀ u v z}
          (pushforwardRingHomOfSquare J₀ J F B B₀ β)).map m).val := by
  ext X x
  rfl

omit [HasWeakSheafify J CommRingCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasSheafify J AddCommGrpCat.{max w u₀ v₀ u v z}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w u₀ v₀ u v z}] in
include hsq in
/-- **Bijectivity of the restriction of derivations from injectivity and one extension.**  Let
`L` be left adjoint to the pushforward `G` along the square.  If restricting derivations is
injective at every `T`, and the derivation `coker d₀ ⟶ G(L(coker d₀))` obtained from the universal
one by the unit of the adjunction is the restriction of a derivation `d^ε` of `B` with values in
`L(coker d₀)`, then restricting derivations is bijective at every `T`: a derivation
`D₀ = δ₀ ∘ g₀` is the restriction of `d^ε` followed by the adjunct of `g₀`. -/
theorem bijective_derivationPushforwardOfSquare_of_injective
    {G : _root_.SheafOfModules.{max w u₀ v₀ u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B) ⥤
      _root_.SheafOfModules.{max w u₀ v₀ u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B₀)}
    (hG : G = _root_.SheafOfModules.pushforward.{max w u₀ v₀ u v z}
      (pushforwardRingHomOfSquare J₀ J F B B₀ β))
    {L : _root_.SheafOfModules.{max w u₀ v₀ u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B₀) ⥤
      _root_.SheafOfModules.{max w u₀ v₀ u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B)}
    (adj : L ⊣ G)
    (hinj : ∀ T : _root_.SheafOfModules.{max w u₀ v₀ u v z}
        (Stacks.SheafOfModules.Tensor.ringSheaf B),
      Function.Injective (fun D : T.val.Derivation' a.hom ↦
        derivationPushforwardOfSquare.{v₀, u₀, v, u, w, z} J A B a J₀ F A₀ B₀ a₀ ψ β hsq D))
    (dε : (L.obj (cokernel ((naiveCotangentComplex.{v₀, u₀, w, max u v z} J₀ A₀ B₀ a₀).d (-1)
      0))).val.Derivation' a.hom)
    (hdε : HEq (derivationPushforwardOfSquare.{v₀, u₀, v, u, w, z} J A B a J₀ F A₀ B₀ a₀ ψ β hsq dε)
      ((naiveCotangentCokernelDerivation.{v₀, u₀, w, max u v z} J₀ A₀ B₀ a₀).postcomp
        (adj.unit.app _).val))
    (T : _root_.SheafOfModules.{max w u₀ v₀ u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B)) :
    Function.Bijective (fun D : T.val.Derivation' a.hom ↦
      derivationPushforwardOfSquare.{v₀, u₀, v, u, w, z} J A B a J₀ F A₀ B₀ a₀ ψ β hsq D) := by
  subst hG
  refine ⟨hinj T, fun D₀ => ?_⟩
  obtain ⟨g₀, hg₀, -⟩ := existsUnique_naiveCotangentCokernelDerivation.{v₀, u₀, w, max u v z}
    J₀ A₀ B₀ a₀ _ D₀
  refine ⟨dε.postcomp ((adj.homEquiv _ _).symm g₀).val, ?_⟩
  refine (derivationPushforwardOfSquare_postcomp J A B a J₀ F A₀ B₀ a₀ ψ β hsq dε _).trans ?_
  rw [eq_of_heq hdε, ← hg₀]
  have hm : adj.unit.app _ ≫ (_root_.SheafOfModules.pushforward.{max w u₀ v₀ u v z}
      (pushforwardRingHomOfSquare J₀ J F B B₀ β)).map ((adj.homEquiv _ _).symm g₀) = g₀ :=
    (adj.homEquiv_unit _ _ _).symm.trans ((adj.homEquiv _ _).apply_symm_apply g₀)
  refine Eq.trans ?_ (congrArg (fun m : cokernel ((naiveCotangentComplex.{v₀, u₀, w, max u v z}
    J₀ A₀ B₀ a₀).d (-1) 0) ⟶ _ => (naiveCotangentCokernelDerivation.{v₀, u₀, w, max u v z} J₀ A₀
      B₀ a₀).postcomp m.val) hm)
  ext X x
  rfl

end Pushforward

end Stacks.SheafOfModules

end
