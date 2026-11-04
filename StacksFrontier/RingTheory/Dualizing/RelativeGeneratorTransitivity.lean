module

public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsTotalComp
public import StacksFrontier.RingTheory.Dualizing.RelativeBaseChangeRepresentatives
public import StacksFrontier.RingTheory.Dualizing.RelativeBaseChangeTransitivity
public import StacksFrontier.RingTheory.Dualizing.RelativeGeneratorResidue

/-!
# The "moreover" clause of [stacks 0E2F] along base change and isomorphisms of algebras

Let `R₁ → A₁` be flat of finite presentation and `K₁` a relative dualizing complex for it such
that derived base change along `A₁ ⊗_{R₁} A₁ → A₁' ⊗_{R'} A₁'` preserves the generators of
`Hom(A₁, K₁ ⊗ᴸ_{A₁} (A₁ ⊗_{R₁} A₁))` for every `R₁ → R'`.  For a ring map `R₁ → R` this file
proves the same of `K = K₁ ⊗ᴸ_{A₁} A` for `R → A = A₁ ⊗_{R₁} R`, and it proves that the property
transports along isomorphisms of `R`-algebras.  These are the two bookkeeping steps by which the
source carries the "moreover" clause from the Noetherian model to `R → A`.

Neither needs the property at `R₁ → R` itself.  Derived base change from `A₁ ⊗_{R₁} A₁` first to
`A ⊗_R A` and then to `A' ⊗_{R'} A'` is derived base change along the composite, which is the map
for `R₁ → R'` up to an isomorphism of rings; and the image in `D(A ⊗_R A)` of a generator for
`K₁` factors through every generator for `K` (`Dualizing.PreservesGenerators.of_comp`).

## Main definitions

* `Dualizing.IsUniversallyGeneratorPreserving` — the property at every `R → R'`.

## Main results

* `Dualizing.IsUniversallyGeneratorPreserving.of_iso`,
  `Dualizing.IsUniversallyGeneratorPreserving.baseChange` and
  `Dualizing.IsUniversallyGeneratorPreserving.of_algEquiv`.

## References

* [Stacks Project, Tag 0E2F](https://stacks.math.columbia.edu/tag/0E2F)
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct
open CochainComplex.DerivedExtensionScalars

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

namespace Dualizing

noncomputable section

/-- If `F ⋙ G` is isomorphic to `F₀ ⋙ H` with `H` fully faithful and `F₀` preserves the generators
`X ⟶ Y`, then `G` preserves the generators `F X ⟶ F Y`, given that a generator `X ⟶ Y` exists. -/
private theorem preservesGenerators_of_natIso_fullyFaithful_comp {C D D₀ E : Type*} [Category* C]
    [Category* D] [Category* D₀] [Category* E] (F : C ⥤ D) (G : D ⥤ E) (F₀ : C ⥤ D₀)
    (H : D₀ ⥤ E) [H.Full] [H.Faithful] (e : F ⋙ G ≅ F₀ ⋙ H) {X Y : C}
    (h : PreservesGenerators F₀ X Y) (hex : ∃ ξ : X ⟶ Y, IsPostcompGenerator ξ) :
    PreservesGenerators G (F.obj X) (F.obj Y) :=
  PreservesGenerators.of_comp
    (PreservesGenerators.of_natIso e.symm
      (PreservesGenerators.comp h (PreservesGenerators.of_fullyFaithful _ _ _))) hex

/-- **The "moreover" clause of [stacks 0E2F] at every base change.**  For every ring map
`R → R'`, derived base change along `A ⊗[R] A → A' ⊗[R'] A'` carries every generator of
`Hom(A, K ⊗ᴸ_A (A ⊗[R] A))` to a generator. -/
def IsUniversallyGeneratorPreserving (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] (K : DerivedCategory (ModuleCat.{u} A)) : Prop :=
  ∀ (R' : Type u) [CommRing R'] [Algebra R R'], IsGeneratorPreservingAt R A R' K

/-- The derived extension of scalars along `f` is the left derived functor of extension of scalars
along `f`, as a statement about the `comparison` of `totalDerivedExtensionScalars`. -/
private theorem isLeftDerivedFunctor_totalDerivedExtensionScalars {B C : Type u} [CommRing B]
    [CommRing C] (f : B →+* C) :
    (totalDerivedExtensionScalars.{u, u, u} f).functor.IsLeftDerivedFunctor
      (show DerivedCategory.Q ⋙ (totalDerivedExtensionScalars.{u, u, u} f).functor ⟶
        (ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q from
        (totalDerivedExtensionScalars.{u, u, u} f).comparison)
      (HomologicalComplex.quasiIso (ModuleCat.{u} B) (ComplexShape.up ℤ)) :=
  (totalDerivedExtensionScalars.{u, u, u} f).isLeftDerived

/-- The property depends only on the isomorphism class of `K`. -/
theorem IsUniversallyGeneratorPreserving.of_iso {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] [Module.Flat R A] {K L : DerivedCategory (ModuleCat.{u} A)}
    (hK : IsUniversallyGeneratorPreserving R A K) (e : K ≅ L) :
    IsUniversallyGeneratorPreserving R A L :=
  fun R' _ _ => (hK R').of_iso e

section BaseChange

variable {R₁ R A₁ : Type u} [CommRing R₁] [CommRing R] [CommRing A₁] [Algebra R₁ R]
  [Algebra R₁ A₁]

/-- The value of `Dualizing.baseChangeBaseChangeAlgEquiv` on `(a ⊗ 1) ⊗ 1`. -/
theorem baseChangeBaseChangeAlgEquiv_tmul_one (R' : Type u) [CommRing R'] [Algebra R R']
    (a : A₁) :
    letI : Algebra R₁ R' := ((algebraMap R R').comp (algebraMap R₁ R)).toAlgebra
    baseChangeBaseChangeAlgEquiv (R₁ := R₁) (R := R) (A₁ := A₁) R'
        ((a ⊗ₜ[R₁] (1 : R)) ⊗ₜ[R] (1 : R')) =
      a ⊗ₜ[R₁] (1 : R') :=
  let : Algebra R₁ R' := ((algebraMap R R').comp (algebraMap R₁ R)).toAlgebra
  RingHom.congr_fun (baseChangeBaseChangeAlgEquiv_comp (R₁ := R₁) (R := R) (A₁ := A₁) R') a

/-- The ring isomorphism `B' ≅ B₁'` between the diagonals of `(A₁ ⊗_{R₁} R) ⊗_R R'` and of
`A₁ ⊗_{R₁} R'`, induced by `Dualizing.baseChangeBaseChangeAlgEquiv`. -/
def diagonalBaseChangeBaseChangeEquiv (R' : Type u) [CommRing R'] [Algebra R R'] :
    letI : Algebra R₁ R' := ((algebraMap R R').comp (algebraMap R₁ R)).toAlgebra
    (((A₁ ⊗[R₁] R) ⊗[R] R') ⊗[R'] ((A₁ ⊗[R₁] R) ⊗[R] R')) ≃+*
      ((A₁ ⊗[R₁] R') ⊗[R'] (A₁ ⊗[R₁] R')) :=
  letI : Algebra R₁ R' := ((algebraMap R R').comp (algebraMap R₁ R)).toAlgebra
  (Algebra.TensorProduct.congr (baseChangeBaseChangeAlgEquiv (R₁ := R₁) (R := R) (A₁ := A₁) R')
    (baseChangeBaseChangeAlgEquiv (R₁ := R₁) (R := R) (A₁ := A₁) R')).toRingEquiv

/-- The two-step map of diagonals `B₁ → B → B'` is the one-step map `B₁ → B₁'` followed by the
inverse of `Dualizing.diagonalBaseChangeBaseChangeEquiv`. -/
theorem diagonalBaseChangeBaseChangeEquiv_comp (R' : Type u) [CommRing R'] [Algebra R R'] :
    letI : Algebra R₁ R' := ((algebraMap R R').comp (algebraMap R₁ R)).toAlgebra
    (diagonalBaseChangeBaseChangeEquiv (R₁ := R₁) (R := R) (A₁ := A₁) R').toRingHom.comp
        ((envelopingBaseChangeRingHom R (A₁ ⊗[R₁] R) R').comp
          (envelopingBaseChangeRingHom R₁ A₁ R)) =
      envelopingBaseChangeRingHom R₁ A₁ R' := by
  let : Algebra R₁ R' := ((algebraMap R R').comp (algebraMap R₁ R)).toAlgebra
  rw [envelopingBaseChangeRingHom_eq, envelopingBaseChangeRingHom_eq,
    envelopingBaseChangeRingHom_eq]
  refine RingHom.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add] at *; rw [hx, hy]
  | tmul a₁ a₂ =>
      show diagonalBaseChangeBaseChangeEquiv (R₁ := R₁) (R := R) (A₁ := A₁) R'
        (diagonalBaseChangeMap R (A₁ ⊗[R₁] R) R'
          (diagonalBaseChangeMap R₁ A₁ R (a₁ ⊗ₜ[R₁] a₂))) =
        diagonalBaseChangeMap R₁ A₁ R' (a₁ ⊗ₜ[R₁] a₂)
      rw [diagonalBaseChangeMap_tmul, diagonalBaseChangeMap_tmul, diagonalBaseChangeMap_tmul]
      show Algebra.TensorProduct.congr
        (baseChangeBaseChangeAlgEquiv (R₁ := R₁) (R := R) (A₁ := A₁) R')
        (baseChangeBaseChangeAlgEquiv (R₁ := R₁) (R := R) (A₁ := A₁) R')
        ((((a₁ ⊗ₜ[R₁] (1 : R)) ⊗ₜ[R] (1 : R'))) ⊗ₜ[R'] ((a₂ ⊗ₜ[R₁] (1 : R)) ⊗ₜ[R] (1 : R'))) = _
      rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
      simp only [AlgEquiv.coe_algHom, baseChangeBaseChangeAlgEquiv_tmul_one]

variable [Module.Flat R₁ A₁] [Algebra.FinitePresentation R₁ A₁]

/-- **The "moreover" clause along base change.**  If `K₁` is a relative dualizing complex for
`R₁ → A₁` with the property at every `R₁ → R'`, then for every `R₁ → R` the derived base change
`K₁ ⊗ᴸ_{A₁} (A₁ ⊗_{R₁} R)` has it for `R → A₁ ⊗_{R₁} R`. -/
theorem IsUniversallyGeneratorPreserving.baseChange {K₁ : DerivedCategory (ModuleCat.{u} A₁)}
    (hK₁ : IsRelativeDualizingComplex R₁ A₁ K₁) (hG : IsUniversallyGeneratorPreserving R₁ A₁ K₁) :
    letI : Module.Flat R (A₁ ⊗[R₁] R) := flat_baseChange R₁ A₁ R
    IsUniversallyGeneratorPreserving R (A₁ ⊗[R₁] R)
      ((totalDerivedExtensionScalars.{u, u, u}
        (Algebra.TensorProduct.includeLeftRingHom : A₁ →+* A₁ ⊗[R₁] R)).functor.obj K₁) := by
  let : Module.Flat R (A₁ ⊗[R₁] R) := flat_baseChange R₁ A₁ R
  intro R' _ _
  let : Algebra R₁ R' := ((algebraMap R R').comp (algebraMap R₁ R)).toAlgebra
  let env₁ := envelopingBaseChangeRingHom R₁ A₁ R
  let env₂ := envelopingBaseChangeRingHom R (A₁ ⊗[R₁] R) R'
  let env₁' := envelopingBaseChangeRingHom R₁ A₁ R'
  let F := (totalDerivedExtensionScalars.{u, u, u} env₁).functor
  let G := (totalDerivedExtensionScalars.{u, u, u} env₂).functor
  -- `F ⋙ G` is base change to `B₁'` followed by the equivalence `D(B₁') ≌ D(B')`
  let eC := diagonalBaseChangeBaseChangeEquiv (R₁ := R₁) (R := R) (A₁ := A₁) R'
  let h : (A₁ ⊗[R₁] A₁) →+* ((A₁ ⊗[R₁] R) ⊗[R] R') ⊗[R'] ((A₁ ⊗[R₁] R) ⊗[R] R') :=
    eC.symm.toRingHom.comp (env₁'.comp (RingEquiv.refl (A₁ ⊗[R₁] A₁)).toRingHom)
  have hh : h = env₂.comp env₁ := by
    refine RingHom.ext fun x => ?_
    show eC.symm (env₁' x) = env₂ (env₁ x)
    have h₁ := RingHom.congr_fun
      (diagonalBaseChangeBaseChangeEquiv_comp (R₁ := R₁) (R := R) (A₁ := A₁) R') x
    change eC (env₂ (env₁ x)) = env₁' x at h₁
    rw [← h₁]
    exact eC.symm_apply_apply _
  let D' := totalDerivedExtensionScalars.{u, u, u} env₁'
  let H := totalDerivedExtensionScalars.{u, u, u} h
  have := isLeftDerivedFunctor_totalDerivedExtensionScalars env₁'
  have := isLeftDerivedFunctor_totalDerivedExtensionScalars h
  have eH := StacksDraft.DerivedRingEquivIso.derivedExtensionRingEquivIsoRight.{u}
    eC env₁' D'.functor D'.comparison H.functor H.comparison
  let eFG : F ⋙ G ≅ D'.functor ⋙ _ :=
    totalDerivedExtensionScalarsComp env₁ env₂ ≪≫
      eqToIso (congrArg (fun k => (totalDerivedExtensionScalars.{u, u, u} k).functor) hh.symm) ≪≫
      eH
  have hGF := preservesGenerators_of_natIso_fullyFaithful_comp F G D'.functor _ eFG (hG R')
    (exists_isPostcompGenerator hK₁)
  -- the two objects, identified
  have hΔ := envelopingBaseChangeRingHom_eq R₁ A₁ R
  let eΔ : F.obj (diagonalSingle R₁ A₁) ≅ diagonalSingle R (A₁ ⊗[R₁] R) :=
    eqToIso (congrArg (fun k => (totalDerivedExtensionScalars.{u, u, u} k).functor.obj
      (diagonalSingle R₁ A₁)) hΔ) ≪≫ diagonalBaseChangeSingleIso R₁ A₁ R
  let eM : F.obj ((diagonalDerivedExtension R₁ A₁).obj K₁) ≅
      (diagonalDerivedExtension R (A₁ ⊗[R₁] R)).obj
        ((totalDerivedExtensionScalars.{u, u, u}
          (Algebra.TensorProduct.includeLeftRingHom : A₁ →+* A₁ ⊗[R₁] R)).functor.obj K₁) :=
    eqToIso (congrArg (fun k => (totalDerivedExtensionScalars.{u, u, u} k).functor.obj
      ((diagonalDerivedExtension R₁ A₁).obj K₁)) hΔ) ≪≫
      (nonempty_diagonalDerivedExtension_baseChange_iso R₁ A₁ R K₁).some
  exact hGF.of_iso eΔ eM

end BaseChange

section AlgEquiv

variable {R A₂ A : Type u} [CommRing R] [CommRing A₂] [CommRing A] [Algebra R A₂] [Algebra R A]

/-- The multiplication maps of the two diagonals are compatible with an isomorphism of
`R`-algebras. -/
theorem lmul'_congr_symm (e : A₂ ≃ₐ[R] A) (b : A ⊗[R] A) :
    e (Algebra.TensorProduct.lmul' R ((Algebra.TensorProduct.congr e e).symm b)) =
      Algebra.TensorProduct.lmul' R b := by
  induction b using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c₁ c₂ =>
      rw [Algebra.TensorProduct.congr_symm_apply, Algebra.TensorProduct.map_tmul,
        Algebra.TensorProduct.lmul'_apply_tmul, Algebra.TensorProduct.lmul'_apply_tmul]
      simp

/-- **The diagonal transports along an isomorphism of algebras.**  Restricting the diagonal `A₂`
of `A₂ ⊗_R A₂` along `(e ⊗ e)⁻¹` gives the diagonal `A` of `A ⊗_R A`. -/
def diagonalSingleTransportIso (e : A₂ ≃ₐ[R] A) :
    (ModuleCat.restrictScalars.{u}
        (Algebra.TensorProduct.congr e e).symm.toRingEquiv.toRingHom).mapDerivedCategory.obj
      (diagonalSingle R A₂) ≅ diagonalSingle R A := by
  let Fm := ModuleCat.restrictScalars.{u}
    (Algebra.TensorProduct.congr e e).symm.toRingEquiv.toRingHom
  let l : Fm.obj ((ModuleCat.restrictScalars
        (Algebra.TensorProduct.lmul' R : A₂ ⊗[R] A₂ →ₐ[R] A₂).toRingHom).obj
          (ModuleCat.of A₂ A₂)) ≃ₗ[A ⊗[R] A]
      (ModuleCat.restrictScalars
        (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).obj (ModuleCat.of A A) :=
    { toFun := fun x => e x
      invFun := fun y => e.symm y
      map_add' := fun x y => e.map_add x y
      map_smul' := fun b x => by
        change e (Algebra.TensorProduct.lmul' R ((Algebra.TensorProduct.congr e e).symm b) *
            @id A₂ x) = Algebra.TensorProduct.lmul' R b * e (@id A₂ x)
        rw [map_mul, lmul'_congr_symm]
      left_inv := fun x => e.symm_apply_apply x
      right_inv := fun y => e.apply_symm_apply y }
  exact (Fm.mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor (ModuleCat.{u} (A ⊗[R] A)) 0).mapIso l.toModuleIso

variable [Module.Flat R A₂] [Module.Flat R A] [Algebra.FinitePresentation R A₂]

/-- **The "moreover" clause along an isomorphism of algebras.**  If `K₂` is a relative dualizing
complex for `R → A₂` with the property at every `R → R'` and `e : A₂ ≃ₐ[R] A`, then its transport
to `D(A)` has the property for `R → A`. -/
theorem IsUniversallyGeneratorPreserving.of_algEquiv (e : A₂ ≃ₐ[R] A)
    {K₂ : DerivedCategory (ModuleCat.{u} A₂)} (hK₂ : IsRelativeDualizingComplex R A₂ K₂)
    (hG : IsUniversallyGeneratorPreserving R A₂ K₂) :
    IsUniversallyGeneratorPreserving R A
      ((ModuleCat.restrictScalars.{u} e.symm.toRingEquiv.toRingHom).mapDerivedCategory.obj K₂) := by
  intro R' _ _
  let e' := baseChangeAlgEquiv R' e
  let eB : (A ⊗[R] A) ≃+* (A₂ ⊗[R] A₂) := (Algebra.TensorProduct.congr e e).symm.toRingEquiv
  let eC : ((A ⊗[R] R') ⊗[R'] (A ⊗[R] R')) ≃+* ((A₂ ⊗[R] R') ⊗[R'] (A₂ ⊗[R] R')) :=
    (Algebra.TensorProduct.congr e' e').symm.toRingEquiv
  let env₂ := envelopingBaseChangeRingHom R A₂ R'
  let env := envelopingBaseChangeRingHom R A R'
  let h : (A ⊗[R] A) →+* ((A ⊗[R] R') ⊗[R'] (A ⊗[R] R')) :=
    eC.symm.toRingHom.comp (env₂.comp eB.toRingHom)
  have hh : h = env := by
    rw [show env = diagonalBaseChangeMap R A R' from envelopingBaseChangeRingHom_eq R A R']
    refine RingHom.ext fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul c₁ c₂ =>
        show Algebra.TensorProduct.congr e' e'
          (env₂ ((Algebra.TensorProduct.congr e e).symm (c₁ ⊗ₜ[R] c₂))) = _
        rw [show env₂ = diagonalBaseChangeMap R A₂ R' from envelopingBaseChangeRingHom_eq R A₂ R',
          Algebra.TensorProduct.congr_symm_apply, Algebra.TensorProduct.map_tmul,
          diagonalBaseChangeMap_tmul, diagonalBaseChangeMap_tmul,
          Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
        simp [e', baseChangeAlgEquiv, Algebra.TensorProduct.congr_apply]
  let D₂ := totalDerivedExtensionScalars.{u, u, u} env₂
  let H := totalDerivedExtensionScalars.{u, u, u} h
  have := isLeftDerivedFunctor_totalDerivedExtensionScalars env₂
  have := isLeftDerivedFunctor_totalDerivedExtensionScalars h
  have eG := StacksDraft.DerivedRingEquivIso.derivedExtensionRingEquivIso.{u, 0}
    eB eC env₂ D₂.functor D₂.comparison H.functor H.comparison
  let F := (mapDerivedCategoryEquivalenceOfEquivalence
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{u, u, u} eB)).functor
  let G := (totalDerivedExtensionScalars.{u, u, u} env).functor
  let eFG : F ⋙ G ≅ D₂.functor ⋙ _ :=
    Functor.isoWhiskerLeft F
      (eqToIso (congrArg (fun k => (totalDerivedExtensionScalars.{u, u, u} k).functor) hh.symm)) ≪≫
      eG
  have hGF := preservesGenerators_of_natIso_fullyFaithful_comp F G D₂.functor _ eFG (hG R')
    (exists_isPostcompGenerator hK₂)
  exact hGF.of_iso (diagonalSingleTransportIso e)
    (RelativeExistence.diagonalExtensionTransportIso e K₂)

end AlgEquiv

end

end Dualizing

end
