module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.Smooth.NoetherianDescent
public import Mathlib.RingTheory.TensorProduct.Maps
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.AffineModel
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Defs
public import StacksFrontier.RingTheory.FinitePresentation.ColimitsII
public import StacksFrontier.RingTheory.FinitePresentation.ModuleDescent
public import StacksFrontier.RingTheory.SpreadingOut.FlatModel
public import StacksFrontier.RingTheory.Syntomic.Morphisms
public import StacksCore.Tactic.StacksAttribute

/-!
# Noetherian approximation of affine morphisms

A morphism of affine schemes which is of finite presentation is the base change of a morphism of
affine schemes over a base of finite type over `Spec ℤ`, and the approximating morphism can be
chosen to inherit flatness, smoothness or the standard syntomic property from the original one.
Since a base of finite type over `ℤ` is Noetherian, this reduces statements about finitely
presented morphisms to the Noetherian case.

## Main definitions

* `AlgebraicGeometry.finiteTypeAffineModel` chooses an affine finite-type model for an affine
  morphism of finite presentation.

## Main results

* `AlgebraicGeometry.exists_finiteTypeAffineModel`: existence of an affine finite-type model
  over a base of finite type over the integers.
* `AlgebraicGeometry.exists_flat_finiteTypeAffineModel`: the model can be taken flat.
* `AlgebraicGeometry.exists_smooth_finiteTypeAffineModel`: the model can be taken smooth.
* `AlgebraicGeometry.exists_finiteTypeAffineModel_standardSyntomic`: the model can be taken
  standard syntomic.

## Implementation notes

The approximation diagram is represented by `AlgebraicGeometry.FiniteTypeAffineModel`, whose
`isPullback` field records the cartesian square and whose `property` field records the extra
property imposed on the modeled morphism. In the plain case that property is `⊤`, since the
result imposes no additional condition; in the three variants it is `AlgebraicGeometry.Flat`,
`AlgebraicGeometry.Smooth` and the standard syntomic condition respectively. Finite type is
expressed by its locally finite type and quasi-compact components, and the structural morphism
to `Spec ℤ` is the morphism to the terminal scheme.

Each proof descends the ring map `Γ(S, ⊤) → Γ(X, ⊤)` to a finitely generated subring of the
base and applies `AlgebraicGeometry.isPullback_SpecMap_of_isPushout` to turn the resulting
pushout of rings into the cartesian square of schemes.

## References

* [Stacks Project, Tag 05FB](https://stacks.math.columbia.edu/tag/05FB)
* [Stacks Project, Tag 05FE](https://stacks.math.columbia.edu/tag/05FE)
* [Stacks Project, Tag 05FF](https://stacks.math.columbia.edu/tag/05FF)
* [Stacks Project, Tag 05FK](https://stacks.math.columbia.edu/tag/05FK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- The structure morphism to the terminal scheme of the spectrum of a finite type `ℤ`-algebra
is locally of finite type. -/
private theorem locallyOfFiniteType_terminal_from_spec {R : Type u} [CommRing R]
    (h : Algebra.FiniteType ℤ R) : LocallyOfFiniteType (terminal.from (Spec (.of R))) := by
  let zMap : ULift.{u} ℤ →+* R := (algebraMap ℤ R).comp ULift.ringEquiv.toRingHom
  let g₀ : Spec (.of R) ⟶ Spec (.of (ULift.{u} ℤ)) := Spec.map (CommRingCat.ofHom zMap)
  let e : Spec (.of (ULift.{u} ℤ)) ≅ ⊤_ Scheme.{u} :=
    specULiftZIsTerminal.uniqueUpToIso (terminalIsTerminal)
  have : LocallyOfFiniteType g₀ :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      ((RingHom.finiteType_algebraMap.mpr h).comp
        (RingHom.FiniteType.of_surjective _ ULift.down_surjective))
  have : LocallyOfFiniteType e.hom := inferInstance
  simpa only [Subsingleton.elim (g₀ ≫ e.hom) (terminal.from _)] using
    (inferInstance : LocallyOfFiniteType (g₀ ≫ e.hom))

/-- A pushout square of rings under `Γ(X, ⊤) ← Γ(S, ⊤)` gives a pullback square of schemes
for affine `X` and `S`. -/
private theorem isPullback_isoSpec_hom_comp_spec_map {X S : Scheme.{u}} [IsAffine X] [IsAffine S]
    (f : X ⟶ S) {A₀ B₀ : CommRingCat.{u}} (a : A₀ ⟶ B₀) (b : A₀ ⟶ Γ(S, ⊤))
    (c : B₀ ⟶ Γ(X, ⊤)) (h : IsPushout a b c f.appTop) :
    IsPullback (X.isoSpec.hom ≫ Spec.map c) f (Spec.map a) (S.isoSpec.hom ≫ Spec.map b) := by
  apply (isPullback_SpecMap_of_isPushout a b c f.appTop h).of_iso X.isoSpec.symm (Iso.refl _)
    S.isoSpec.symm (Iso.refl _)
  all_goals simp [Scheme.isoSpec_inv_naturality]

/-- **Stacks Project, Tag 05FB.** An affine morphism of finite presentation between affine
schemes admits an affine finite-type model over a base of finite type over `ℤ`. -/
@[stacks 05FB]
theorem exists_finiteTypeAffineModel {X S : Scheme.{u}} [IsAffine X] [IsAffine S]
    (f : X ⟶ S) (hf : FinitePresentation f) :
    Nonempty (FiniteTypeAffineModel ⊤ f) := by
  have : LocallyOfFinitePresentation f := hf.1
  have : QuasiCompact f := hf.2.1
  let A := Γ(S, ⊤)
  let B := Γ(X, ⊤)
  let : Algebra A B := f.appTop.hom.toAlgebra
  have : Algebra.FinitePresentation A B := f.finitePresentation_appTop
  obtain ⟨A₀, B₀, M₀, _, _, _, _, _, _, _, _, φ, hA₀, hB₀, _, hpush, _⟩ :=
    Algebra.exists_subring_finiteType_int_isPushout_isBaseChange (R := A) (S := B) B
  let X₀ : Scheme.{u} := Spec (.of B₀)
  let S₀ : Scheme.{u} := Spec (.of A₀)
  let f₀ : X₀ ⟶ S₀ := Spec.map (CommRingCat.ofHom (algebraMap A₀ B₀))
  let toSource : X ⟶ X₀ := X.isoSpec.hom ≫
    Spec.map (CommRingCat.ofHom (algebraMap B₀ B))
  let toBase : S ⟶ S₀ := S.isoSpec.hom ≫
    Spec.map (CommRingCat.ofHom A₀.subtype)
  have hp : IsPullback toSource f f₀ toBase := by
    have hsring' : IsPushout (CommRingCat.ofHom (algebraMap A₀ B₀))
        (CommRingCat.ofHom A₀.subtype) (CommRingCat.ofHom (algebraMap B₀ B)) f.appTop := by
      convert CommRingCat.isPushout_iff_isPushout.mpr hpush.symm using 1 <;> ext <;> rfl
    exact isPullback_isoSpec_hom_comp_spec_map f _ _ _ hsring'
  have hf₀ : LocallyOfFiniteType f₀ :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr hB₀)
  have hbase := locallyOfFiniteType_terminal_from_spec hA₀
  exact ⟨⟨X₀, S₀, f₀, toSource, toBase, hp, inferInstance, inferInstance,
    hbase, inferInstance, hf₀, inferInstance, trivial⟩⟩

/-- A chosen affine finite-type model over a base of finite type over `ℤ` for an affine
morphism of finite presentation. Its fields give the comparison morphisms, the pullback
square, and the affine and finite-type specifications. -/
noncomputable def finiteTypeAffineModel {X S : Scheme.{u}} [IsAffine X] [IsAffine S]
    (f : X ⟶ S) (hf : FinitePresentation f) :
    FiniteTypeAffineModel ⊤ f :=
  Classical.choice (exists_finiteTypeAffineModel f hf)

section Flat

private noncomputable def tensorRightUnitLinearEquiv
    {R A M : Type u} [CommSemiring R] [CommSemiring A] [CommSemiring M]
    [Algebra R M] [Algebra A M] [SMulCommClass A R M] :
    M ⊗[R] R ≃ₗ[A] M := by
  let e := TensorProduct.rid R M
  refine { e with map_smul' := ?_ }
  intro a x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m r =>
      simp only [TensorProduct.smul_tmul']
      exact (smul_comm a r m).symm
  | add x y hx hy =>
      change e (a • x) = a • e x at hx
      change e (a • y) = a • e y at hy
      change e (a • (x + y)) = a • e (x + y)
      rw [smul_add, map_add, map_add, hx, hy, smul_add]

/-- **Stacks Project, Tag 05FE.** A flat morphism of finite presentation between affine
schemes admits an affine finite-type model whose modeled morphism is flat. -/
@[stacks 05FE]
theorem exists_flat_finiteTypeAffineModel
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S] (f : X ⟶ S)
    (hf : FinitePresentation f) [Flat f] :
    Nonempty (FiniteTypeAffineModel @Flat f) := by
  let A := Γ(S, ⊤)
  let B := Γ(X, ⊤)
  let : Algebra A B := f.appTop.hom.toAlgebra
  have : LocallyOfFinitePresentation f := hf.1
  have : QuasiCompact f := hf.2.1
  have : Algebra.FinitePresentation A B := f.finitePresentation_appTop
  have : Module.Flat A B := RingHom.flat_algebraMap_iff.mpr f.flat_appTop
  obtain ⟨R₀, S₀, M₀, _, _, _, _, _, _, _, _, φ, hR₀, hS₀, _, hpush, _⟩ :=
    Algebra.exists_subring_finiteType_int_isPushout_isBaseChange (R := A) (S := B) B
  obtain ⟨i, hflatStage⟩ := Algebra.FiniteTypeSystem.exists_flat_stage R₀ S₀ S₀
    (fun q : PrimeSpectrum B => by
      have hloc : Module.Flat A (Localization.AtPrime q.asIdeal) := by infer_instance
      have : SMulCommClass A S₀ (Localization.AtPrime q.asIdeal) := ⟨fun a s m => by
        simp only [Algebra.smul_def]
        ring⟩
      exact Module.Flat.of_linearEquiv
        (tensorRightUnitLinearEquiv (R := S₀) (A := A)
          (M := Localization.AtPrime q.asIdeal)))
  let A₀ := Algebra.FiniteTypeSystem.Base R₀ i
  let B₀ := Algebra.FiniteTypeSystem.Ring R₀ S₀ i
  let : Algebra S₀ B₀ := Algebra.TensorProduct.rightAlgebra
  have hflatB₀ : Module.Flat A₀ B₀ := by
    have : SMulCommClass A₀ S₀ B₀ := ⟨fun a s m => by
      simp only [Algebra.smul_def]
      ring⟩
    have : Module.Flat A₀ (B₀ ⊗[S₀] S₀) := hflatStage
    exact Module.Flat.of_linearEquiv
      (tensorRightUnitLinearEquiv (R := S₀) (A := A₀) (M := B₀)).symm
  let X₀ : Scheme.{u} := Spec (.of B₀)
  let S₁ : Scheme.{u} := Spec (.of A₀)
  let f₀ : X₀ ⟶ S₁ := Spec.map (CommRingCat.ofHom (algebraMap A₀ B₀))
  let toSource : X ⟶ X₀ := X.isoSpec.hom ≫
    Spec.map (CommRingCat.ofHom (algebraMap B₀ B))
  let toBase : S ⟶ S₁ := S.isoSpec.hom ≫
    Spec.map (CommRingCat.ofHom (algebraMap A₀ A))
  have : Algebra.IsPushout R₀ A S₀ B := hpush
  have hringPushout : IsPushout (CommRingCat.ofHom (algebraMap A₀ B₀))
      (CommRingCat.ofHom (algebraMap A₀ A)) (CommRingCat.ofHom (algebraMap B₀ B)) f.appTop :=
    CommRingCat.isPushout_iff_isPushout.mpr
      (Algebra.FiniteTypeSystem.ringToRing_isPushout R₀ S₀ i).symm
  have hp : IsPullback toSource f f₀ toBase :=
    isPullback_isoSpec_hom_comp_spec_map f _ _ _ hringPushout
  have hf₀ : Flat f₀ :=
    (HasRingHomProperty.Spec_iff (P := @Flat)).mpr (RingHom.flat_algebraMap_iff.mpr hflatB₀)
  have hf₀lt : LocallyOfFiniteType f₀ :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr (show Algebra.FiniteType A₀ B₀ from inferInstance))
  have hbase := locallyOfFiniteType_terminal_from_spec (R := A₀) inferInstance
  exact ⟨⟨X₀, S₁, f₀, toSource, toBase, hp, inferInstance, inferInstance,
    hbase, inferInstance, hf₀lt, inferInstance, hf₀⟩⟩

end Flat

section Smooth

/-- **Stacks Project, Tag 05FF.** A smooth morphism between affine schemes
admits an affine finite-type model whose modeled morphism is smooth. -/
@[stacks 05FF]
theorem exists_smooth_finiteTypeAffineModel
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S] (f : X ⟶ S) [Smooth f] :
    Nonempty (FiniteTypeAffineModel @Smooth f) := by
  classical
  let A : Type u := Γ(S, ⊤)
  let B : Type u := Γ(X, ⊤)
  let : Algebra A B := f.appTop.hom.toAlgebra
  have htop : f.appTop.hom.Smooth := by
    have hlocal := f.smooth_appLE (isAffineOpen_top S) (isAffineOpen_top X) (by simp)
    have hmap : f.appLE ⊤ ⊤ (by simp) = f.appTop := by
      simpa [Scheme.Hom.appLE, Scheme.Hom.appTop] using
        (Category.comp_id (f.app ⊤))
    rwa [hmap] at hlocal
  have : Algebra.Smooth A B := htop.toAlgebra
  obtain ⟨A₀, B₀, _, _, hA₀, hB₀, he⟩ :=
    Algebra.Smooth.exists_subalgebra_fg (R := ℤ) A B
  let : CommRing B₀ := inferInstance
  let : Algebra A₀ B₀ := inferInstance
  let X₀ : Scheme.{u} := Spec (.of B₀)
  let S₀ : Scheme.{u} := Spec (.of A₀)
  let f₀ : X₀ ⟶ S₀ := Spec.map (CommRingCat.ofHom (algebraMap A₀ B₀))
  let e : B ≃ₐ[A] (A ⊗[A₀] B₀) := Classical.choice he
  let φRing : B₀ →+* B := e.symm.toRingEquiv.toRingHom.comp
    ((Algebra.TensorProduct.includeRight (R := A₀) (A := A) (B := B₀)).toRingHom)
  let : Algebra A₀ B := Algebra.compHom B A₀.subtype
  let : Algebra B₀ B := φRing.toAlgebra
  have hmapA₀ : algebraMap A₀ B = φRing.comp (algebraMap A₀ B₀) := by
    ext a
    show algebraMap A B (A₀.subtype a) = _
    calc
      _ = e.symm (algebraMap A (A ⊗[A₀] B₀) (A₀.subtype a)) := by simp
      _ = e.symm (1 ⊗ₜ[A₀] algebraMap A₀ B₀ a) := by
        congr 1
        exact Algebra.TensorProduct.tmul_one_eq_one_tmul (R := A₀) (A := A) (B := B₀) a
      _ = _ := rfl
  have hscalar : IsScalarTower A₀ B₀ B :=
    .of_algebraMap_eq fun a => DFunLike.congr_fun hmapA₀ a
  have hAB : IsScalarTower A₀ A B := IsScalarTower.of_algebraMap_eq' rfl
  let φ : B₀ →ₐ[A₀] B := {
    toRingHom := φRing
    commutes' := fun a => (DFunLike.congr_fun hmapA₀ a).symm
  }
  let toSource : X ⟶ X₀ := X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom φ.toRingHom)
  let toBase : S ⟶ S₀ := S.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom A₀.subtype)
  have hpushAlg : @Algebra.IsPushout A₀ A _ _ _ B₀ B _ _ _ _ _ _ hscalar hAB := by
    let := Algebra.TensorProduct.rightAlgebra (R := A₀) (A := A) (B := B₀)
    let : IsScalarTower A₀ B₀ (A ⊗[A₀] B₀) := by
      apply IsScalarTower.of_algebraMap_eq'
      ext a
      exact Algebra.TensorProduct.tmul_one_eq_one_tmul (R := A₀) (A := A) (B := B₀) a
    have hTensor := CommRingCat.isPushout_tensorProduct A₀ A B₀
    have hTensor' : IsPushout (CommRingCat.ofHom (algebraMap A₀ A))
        (CommRingCat.ofHom (algebraMap A₀ B₀))
        (CommRingCat.ofHom (algebraMap A (A ⊗[A₀] B₀)))
        (CommRingCat.ofHom (algebraMap B₀ (A ⊗[A₀] B₀))) := by
      convert hTensor using 1
    have hTensorAlg : Algebra.IsPushout A₀ A B₀ (A ⊗[A₀] B₀) :=
      (CommRingCat.isPushout_iff_isPushout).mp hTensor'
    exact @Algebra.IsPushout.of_equiv A₀ B₀ inferInstance inferInstance inferInstance
      A (A ⊗[A₀] B₀) inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance hTensorAlg
      B inferInstance inferInstance inferInstance inferInstance hscalar hAB e.symm rfl
  have hpush : IsPushout (CommRingCat.ofHom (algebraMap A₀ B₀))
      (CommRingCat.ofHom A₀.subtype) (CommRingCat.ofHom φ.toRingHom) f.appTop := by
    have hpushAlgSwap : @Algebra.IsPushout A₀ B₀
        (inferInstance : CommSemiring A₀) (inferInstance : CommSemiring B₀)
        (inferInstance : Algebra A₀ B₀) A B
        (inferInstance : CommSemiring A) (inferInstance : CommSemiring B)
        (inferInstance : Algebra A₀ A) (inferInstance : Algebra B₀ B)
        (inferInstance : Algebra A B) (inferInstance : Algebra A₀ B)
        hAB hscalar :=
      @Algebra.IsPushout.symm A₀ A
        (inferInstance : CommSemiring A₀) (inferInstance : CommSemiring A)
        (inferInstance : Algebra A₀ A) B₀ B
        (inferInstance : CommSemiring B₀) (inferInstance : CommSemiring B)
        (inferInstance : Algebra A₀ B₀) (inferInstance : Algebra A B)
        (inferInstance : Algebra B₀ B) (inferInstance : Algebra A₀ B)
        hscalar hAB hpushAlg
    have h := (@CommRingCat.isPushout_iff_isPushout A₀ A
      (inferInstance : CommRing A₀) (inferInstance : CommRing A)
      (inferInstance : Algebra A₀ A) B₀ B
      (inferInstance : CommRing B₀) (inferInstance : CommRing B)
      (inferInstance : Algebra A₀ B₀) (inferInstance : Algebra A B)
      (inferInstance : Algebra B₀ B) (inferInstance : Algebra A₀ B)
      hscalar hAB).mpr hpushAlgSwap
    convert h using 1 <;> ext <;> rfl
  have hp : IsPullback toSource f f₀ toBase :=
    isPullback_isoSpec_hom_comp_spec_map f _ _ _ hpush
  have : Algebra.Smooth A₀ B₀ := hB₀
  have hf₀ : Smooth f₀ :=
    (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
      ((RingHom.smooth_algebraMap).mpr hB₀)
  have hbase := locallyOfFiniteType_terminal_from_spec ((Subalgebra.fg_iff_finiteType A₀).mp hA₀)
  exact ⟨⟨X₀, S₀, f₀, toSource, toBase, hp, inferInstance, inferInstance,
    hbase, inferInstance, inferInstance, inferInstance, hf₀⟩⟩

end Smooth

section StandardSyntomic

/-- The spectrum of a relative global complete intersection is a standard syntomic morphism of
affine schemes: transporting the algebra structure along the canonical isomorphisms
`Γ(Spec R, ⊤) ≅ R` turns the ring-level hypothesis into the condition on global sections which
defines `AlgebraicGeometry.IsStandardSyntomic`. -/
private lemma isStandardSyntomic_specMap_algebraMap
    {R₀ T : Type u} [CommRing R₀] [CommRing T] [Algebra R₀ T]
    [Algebra.IsRelativeGlobalCompleteIntersection R₀ T] :
    IsStandardSyntomic
      (Spec.map (CommRingCat.ofHom (algebraMap R₀ T)) :
        Spec (.of T) ⟶ Spec (.of R₀)) := by
  set α₀T : CommRingCat.of R₀ ⟶ CommRingCat.of T :=
    CommRingCat.ofHom (algebraMap R₀ T) with hα₀T
  set X₀ : Scheme.{u} := Spec (.of T) with hX₀
  set S₀ : Scheme.{u} := Spec (.of R₀) with hS₀
  set f₀' : X₀ ⟶ S₀ := Spec.map α₀T with hf₀'
  let eR : Γ(S₀, ⊤) ≃+* R₀ :=
    (Scheme.ΓSpecIso (.of R₀)).commRingCatIsoToRingEquiv
  let eT : Γ(X₀, ⊤) ≃+* T :=
    (Scheme.ΓSpecIso (.of T)).commRingCatIsoToRingEquiv
  have hcomp : α₀T.hom.comp eR.toRingHom =
      eT.toRingHom.comp f₀'.appTop.hom :=
    congrArg CommRingCat.Hom.hom (Scheme.ΓSpecIso_naturality α₀T).symm
  let : Algebra Γ(S₀, ⊤) Γ(X₀, ⊤) := f₀'.appTop.hom.toAlgebra
  show Algebra.IsRelativeGlobalCompleteIntersection Γ(S₀, ⊤) Γ(X₀, ⊤)
  let : Algebra R₀ Γ(S₀, ⊤) := eR.symm.toRingHom.toAlgebra
  let g : Γ(S₀, ⊤) →+* T :=
    α₀T.hom.comp (eR.toRingHom : Γ(S₀, ⊤) →+* R₀)
  let : Algebra Γ(S₀, ⊤) T :=
    RingHom.toAlgebra (R := Γ(S₀, ⊤)) (S := T) g
  let : IsScalarTower R₀ Γ(S₀, ⊤) T := .of_algebraMap_eq fun x => by
    show (algebraMap R₀ T) x =
      ((algebraMap R₀ T).comp eR.toRingHom) (eR.symm x)
    simp
  have hpush : Algebra.IsPushout R₀ T Γ(S₀, ⊤) T :=
    Algebra.IsPushout.of_bijective_left (R := R₀) (T := T) (A := Γ(S₀, ⊤))
      eR.symm.bijective
  have hbase : Algebra.IsRelativeGlobalCompleteIntersection Γ(S₀, ⊤) T :=
    Algebra.IsRelativeGlobalCompleteIntersection.baseChange R₀ T Γ(S₀, ⊤) T
  let eA : Γ(X₀, ⊤) ≃ₐ[Γ(S₀, ⊤)] T := AlgEquiv.ofRingEquiv (f := eT) (by
    intro x
    show (eT.toRingHom.comp f₀'.appTop.hom) x =
      (α₀T.hom.comp eR.toRingHom) x
    exact (congrArg (fun k : Γ(S₀, ⊤) →+* T => k x) hcomp).symm)
  exact Algebra.IsRelativeGlobalCompleteIntersection.of_algEquiv
    (R := Γ(S₀, ⊤)) (A := T) (B := Γ(X₀, ⊤)) eA.symm

/-- **Stacks Project, Tag 05FK.** A standard syntomic morphism of affine schemes
admits an affine finite-type model whose modeled morphism is standard syntomic. -/
@[stacks 05FK]
theorem exists_finiteTypeAffineModel_standardSyntomic
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S] (f : X ⟶ S)
    (hf : IsStandardSyntomic f) :
    Nonempty {m : FiniteTypeAffineModel ⊤ f //
      letI : IsAffine m.X₀ := m.source_affine
      letI : IsAffine m.S₀ := m.base_affine
      IsStandardSyntomic m.f₀} := by
  classical
  let R := Γ(S, ⊤)
  let A := Γ(X, ⊤)
  let : Algebra R A := f.appTop.hom.toAlgebra
  obtain ⟨n, c, P, hP⟩ := (show Algebra.IsRelativeGlobalCompleteIntersection R A from hf).out
  obtain ⟨R₀, hR₀, f₀, hf₀, hP₀⟩ :=
    Algebra.Presentation.exists_fg_isRelativeGlobalCompleteIntersection_naive P
  let T := MvPolynomial (Fin n) R₀ ⧸ Ideal.span (Set.range f₀)
  let P₀ : Algebra.Presentation R₀ T (Fin n) (Fin c) :=
    Algebra.Presentation.naive (v := f₀)
      (Function.surjInv Ideal.Quotient.mk_surjective)
      (Function.surjInv_eq Ideal.Quotient.mk_surjective)
  let : Algebra R₀ A := ((algebraMap R A).comp (algebraMap R₀ R)).toAlgebra
  let : @IsScalarTower R₀ R A Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    .of_algebraMap_eq fun _ => rfl
  let φ : T →+* A := Ideal.Quotient.lift _
    (MvPolynomial.eval₂Hom (algebraMap R₀ A) P.val) (by
      intro F hF
      refine RingHom.mem_ker.mp ((Ideal.span_le.mpr ?_) hF)
      rintro _ ⟨j, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, MvPolynomial.coe_eval₂Hom,
        show algebraMap R₀ A = (algebraMap R A).comp (algebraMap R₀ R) from rfl,
        ← MvPolynomial.eval₂_map, hf₀ j]
      exact P.aeval_val_relation j)
  let : Algebra T A := φ.toAlgebra
  let : @IsScalarTower R₀ T A Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq (R := R₀) (S := T) (A := A) fun x =>
      (MvPolynomial.eval₂_C (algebraMap R₀ A) P.val x).symm
  have hPush : Algebra.IsPushout R₀ R T A :=
    P.isPushout_quotient_of_map_eq f₀ hf₀ fun i => by
      show φ (Ideal.Quotient.mk _ (MvPolynomial.X i)) = P.val i
      simp [φ, T, Ideal.Quotient.lift_mk]
  let X₀ : Scheme.{u} := Spec (.of T)
  let S₀ : Scheme.{u} := Spec (.of R₀)
  let α₀T : CommRingCat.of R₀ ⟶ CommRingCat.of T :=
    CommRingCat.ofHom (algebraMap R₀ T)
  let f₀' : X₀ ⟶ S₀ := Spec.map α₀T
  let toSource : X ⟶ X₀ := X.isoSpec.hom ≫
    Spec.map (CommRingCat.ofHom (algebraMap T A))
  let toBase : S ⟶ S₀ := S.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom R₀.subtype)
  have hPull : IsPullback toSource f f₀' toBase := by
    have hRing : IsPushout α₀T
        (CommRingCat.ofHom R₀.subtype) (CommRingCat.ofHom (algebraMap T A)) f.appTop := by
      have h := (CommRingCat.isPushout_iff_isPushout
        (R := R₀) (S := R) (R' := T) (S' := A)).mpr hPush.symm
      convert h using 1 <;> ext <;> rfl
    exact isPullback_isoSpec_hom_comp_spec_map f _ _ _ hRing
  have hf₀' : LocallyOfFiniteType f₀' :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  have hbase := locallyOfFiniteType_terminal_from_spec ((Subalgebra.fg_iff_finiteType R₀).mp hR₀)
  have hStd : IsStandardSyntomic f₀' := by
    have : P₀.IsRelativeGlobalCompleteIntersection := hP₀
    have : Algebra.IsRelativeGlobalCompleteIntersection ↥R₀ T :=
      Algebra.IsRelativeGlobalCompleteIntersection.of_presentation P₀
    exact isStandardSyntomic_specMap_algebraMap (R₀ := ↥R₀) (T := T)
  exact ⟨⟨⟨X₀, S₀, f₀', toSource, toBase, hPull, inferInstance, inferInstance,
    hbase, inferInstance, hf₀', inferInstance, trivial⟩, hStd⟩⟩

end StandardSyntomic

end AlgebraicGeometry
