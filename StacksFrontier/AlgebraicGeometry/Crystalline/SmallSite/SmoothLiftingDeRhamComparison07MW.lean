module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.SmoothLiftingLevelMap07MW
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineDeRhamSectionsComplex
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CompletedDeRhamNilpotentReduction
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineObjectCompletedFormsComparison
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LevelZeroDeRhamComparison07MW
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrysBaseChangeAlong
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.BaseChangeConnectionReduction

/-!
# The de Rham complex of a crystal over an affine smooth lifting

In the situation of [Stacks, Tag 07MW] (`...SmallSite.Situation07MW`) with `X`, `S` and `Y` affine,
let `ψ : (X, Y, γ) ⟶ T(0)_e` be the chosen morphism to a level of the system
(`...Situation07MW.levelHom`), `a : D → D'` its envelope map (`...Situation07MW.levelEnvelopeMap`)
and `ℱ` a crystal in quasi-coherent modules with pair `(M, ∇)` over `D`
(`...SmallSite.crystalPairConnModule`).  This module identifies the base change
`M' ⊗^∧_{D'} Ω^*_{D'}` of the pair along `a` with the explicit complex of sections of the de Rham
complex `ℱ ⊗ Ω^•_{X/S}` over the affine-over-affine object `(X, Y, γ)`
(`...SmallSite.affineDeRhamSectionsComplex`):

`(M ⊗̂_D D') ⊗^∧_{D'} Ω^*_{D'} ≅ Γ(Y, ℱ) ⊗ ⋀^• Ω_{X/S}(Y)`,

for every level with `p^{N+e} = 0` in `E(0)`.  The degree-`a` map is `x ⊗ ω ↦ λ_Y(x) ⊗ Θ_Y(ω)`
where `θ_Y : D' ≃ Γ(Y, ⊤)` comes from `D' ≃ E' ≃ Γ(Y, ⊤)` (`...Situation07MW.envelopeEquiv`),
`Θ_Y` is the comparison of forms (`Crystalline.GlobalCrystallineSituation.formsHom`) and
`λ_Y : M' → Γ(Y, ℱ)`, `d ⊗ m ↦ θ_Y(d) · ψ^*(m_e)`, is the base change of sections of the crystal
along `ψ` (`...SmallSite.crysBaseChangeAlong`), bijective because `ℱ` is a crystal.  It is an
instance of `Crystalline.FormsData.ConnModule.reduceComplexHom`.

## Main definitions

* `Situation07MW.liftingObject`, `Situation07MW.levelAffineHom` — `(X, Y, γ)` and `ψ` in the
  affine-over-affine subsite.
* `Situation07MW.envelopeFormsHom` — `a` as a morphism of rings with forms.
* `Situation07MW.liftingComponent` — `λ_Y`.
* `Situation07MW.liftingDeRhamComplexHom` — the morphism of complexes.

## Main results

* `Situation07MW.liftingRingHom_envelopeFormsHom` — `θ_Y ∘ a = ψ^♯ ∘ θ_{T(0)_e}`.
* `Situation07MW.envelopeFormsHom_psi_completedUnitZeroForm` — `a` fixes the unit zero-form.
* `Situation07MW.bijective_liftingComponent` — `λ_Y` is bijective.
* `Situation07MW.liftingRingConnection_liftingComponent` — the canonical connection of
  [Stacks, Tag 07J6] on `Γ(Y, ℱ)` corresponds to the base-changed connection on `M'`.
* `Situation07MW.isIso_liftingDeRhamComplexHom` — the morphism of complexes is an isomorphism.

## What is and is not proved

Everything stated is proved, under the explicit hypothesis `p^{N+e} = 0` in `E(0)` for the
bijectivity statements.  No tag attribute is placed.

## References

* [Stacks Project, Tag 07MW](https://stacks.math.columbia.edu/tag/07MW)
* [Stacks Project, Lemma 60.15.1, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite DividedPowers Simplicial
open scoped AlgebraicGeometry TensorProduct

universe u

namespace Crystalline.GlobalCrystallineSituation.SmallSite.Situation07MW

open AffineConnection

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.X] [IsAffine S.S.scheme]
  (T : Situation07MW S) [IsAffine T.Y]

attribute [local instance] crysTopAlgebra wsEnvelopeTopAlgebra tensorPowerEnvelopeAlgebraInstance
  presentationEnvelopeAlgebraInst Situation07MW.liftingAlgebra

/-- The ambient scheme `Y` of the object `(X, Y, γ)` is affine. -/
instance isAffine_crystallineThickening_target :
    IsAffine T.crystallineThickening.obj.thickening.target.scheme :=
  inferInstanceAs (IsAffine T.Y)

/-- **The object `(X, Y, γ)` of the affine-over-affine subsite**: `Y` is affine and lies over the
affine open `⊤` of `S`. -/
abbrev liftingObject : AffineOverAffineCrystallineThickening S :=
  ⟨T.crystallineThickening, inferInstanceAs (IsAffine T.Y), ⊤, isAffineOpen_top _, le_rfl⟩

omit [IsAffine S.X] in
/-- The underlying object of `liftingObject` is `(X, Y, γ)`. -/
@[simp]
theorem liftingObject_obj : T.liftingObject.obj = T.crystallineThickening :=
  rfl

/-- **The morphism `ψ : (X, Y, γ) ⟶ T(0)_e` in the affine-over-affine subsite.** -/
def levelAffineHom (e : ℕ) (he : T.levelBound ≤ e) :
    T.liftingObject ⟶ levelAffineObject T.primeNilpotentX 0 e :=
  ObjectProperty.homMk (T.levelHom e he)

/-- The underlying morphism of `levelAffineHom` is `ψ`. -/
@[simp]
theorem levelAffineHom_hom (e : ℕ) (he : T.levelBound ≤ e) :
    (T.levelAffineHom e he).hom = T.levelHom e he :=
  rfl

/-! ### The envelope `E'` of the smooth lifting over `Γ(S, ⊤)` -/

/-- The envelope `E'` of the presentation `Γ(Y, ⊤) → C` as an algebra over `Γ(S, ⊤)`, in the
spelling of the base ring used by `Crystalline.GlobalCrystallineSituation.formsHom`. -/
abbrev liftingEnvelopeTopAlgebra :
    Algebra (Γ(S.S.scheme, ⊤) : Type u)
      (presentationEnvelope T.affineCrystallineSituation T.liftingPresentation).object :=
  presentationEnvelopeAlgebraInst T.affineCrystallineSituation T.liftingPresentation

attribute [local instance] liftingEnvelopeTopAlgebra

/-- **The identification `E' ≃ Γ(Y, ⊤)` as a morphism of `Γ(S, ⊤)`-algebras**, the target carrying
the algebra structure `crysTopAlgebra` of the object `(X, Y, γ)`. -/
def liftingEnvelopeAlgHom :
    (presentationEnvelope T.affineCrystallineSituation T.liftingPresentation).object →ₐ[
      (Γ(S.S.scheme, ⊤) : Type u)] Γ(T.crystallineThickening.obj.thickening.target.scheme, ⊤) :=
  { T.envelopeEquiv.toRingEquiv.toRingHom with
    commutes' := fun a ↦ (T.envelopeEquiv.commutes a).trans
      (congrArg (fun i : Algebra (T.affineCrystallineSituation.A : Type u) Γ(T.Y, ⊤) ↦
        @algebraMap _ _ _ _ i a) T.liftingAlgebra_eq_crysTopAlgebra) }

/-- The inverse identification `Γ(Y, ⊤) ≃ E'` as a morphism of `Γ(S, ⊤)`-algebras. -/
def liftingEnvelopeAlgHomInv :
    Γ(T.crystallineThickening.obj.thickening.target.scheme, ⊤) →ₐ[(Γ(S.S.scheme, ⊤) : Type u)]
      (presentationEnvelope T.affineCrystallineSituation T.liftingPresentation).object :=
  { T.envelopeEquiv.symm.toRingEquiv.toRingHom with
    commutes' := fun a ↦ (congrArg T.envelopeEquiv.symm
      (congrArg (fun i : Algebra (T.affineCrystallineSituation.A : Type u) Γ(T.Y, ⊤) ↦
        @algebraMap _ _ _ _ i a) T.liftingAlgebra_eq_crysTopAlgebra).symm).trans
      (T.envelopeEquiv.symm.commutes a) }

omit [IsAffine S.X] [IsAffine S.S.scheme] in
/-- `E' ≃ Γ(Y, ⊤)` is a divided power morphism. -/
theorem isDPMorphism_liftingEnvelopeAlgHom :
    IsDPMorphism
      (presentationEnvelope T.affineCrystallineSituation T.liftingPresentation).object.dividedPowers
      (crysDividedPowers S T.crystallineThickening.obj) T.liftingEnvelopeAlgHom.toRingHom :=
  T.isDPMorphism_envelopeEquiv

omit [IsAffine S.X] [IsAffine S.S.scheme] in
/-- `Γ(Y, ⊤) ≃ E'` is a divided power morphism. -/
theorem isDPMorphism_liftingEnvelopeAlgHomInv :
    IsDPMorphism (crysDividedPowers S T.crystallineThickening.obj)
      (presentationEnvelope T.affineCrystallineSituation T.liftingPresentation).object.dividedPowers
      T.liftingEnvelopeAlgHomInv.toRingHom :=
  T.isDPMorphism_envelopeEquiv_symm

omit [IsAffine S.X] [IsAffine S.S.scheme] in
/-- The inverse is a left inverse. -/
theorem liftingEnvelopeAlgHomInv_comp :
    T.liftingEnvelopeAlgHomInv.comp T.liftingEnvelopeAlgHom = AlgHom.id _ _ :=
  AlgHom.ext fun x ↦ T.envelopeEquiv.symm_apply_apply x

omit [IsAffine S.X] [IsAffine S.S.scheme] in
/-- The inverse is a right inverse. -/
theorem comp_liftingEnvelopeAlgHomInv :
    T.liftingEnvelopeAlgHom.comp T.liftingEnvelopeAlgHomInv = AlgHom.id _ _ :=
  AlgHom.ext fun x ↦ T.envelopeEquiv.apply_symm_apply x

omit [IsAffine S.X] [IsAffine S.S.scheme] [IsAffine T.Y] in
/-- `p` is nilpotent in the envelope `E'`. -/
theorem exists_pow_eq_zero_liftingEnvelope :
    ∃ k, (S.p : (presentationEnvelope T.affineCrystallineSituation
      T.liftingPresentation).object) ^ k = 0 := by
  obtain ⟨k, hk⟩ := T.prime_nilpotent
  refine ⟨k, ?_⟩
  have h := congrArg (algebraMap (Γ(S.S.scheme, ⊤) : Type u)
    (presentationEnvelope T.affineCrystallineSituation T.liftingPresentation).object) hk
  rwa [map_pow, map_natCast, map_zero] at h

omit [IsAffine S.X] [IsAffine S.S.scheme] [IsAffine T.Y] in
/-- `p` is nilpotent in the completed envelope `D'`. -/
theorem exists_pow_eq_zero_liftingFormsRing :
    ∃ k, ((T.affineCrystallineSituation.p : ℕ) :
      (presentationFormsData T.affineCrystallineSituation T.liftingPresentation).ring) ^ k = 0 := by
  obtain ⟨k, hk⟩ := T.exists_pow_eq_zero_liftingEnvelope
  refine ⟨k, ?_⟩
  have h := congrArg (algebraMap
    (presentationEnvelope T.affineCrystallineSituation T.liftingPresentation).object
    (AdicCompletion (pAdicIdeal (A :=
      (presentationEnvelope T.affineCrystallineSituation T.liftingPresentation).object) S.p)
      (presentationEnvelope T.affineCrystallineSituation T.liftingPresentation).object)) hk
  rw [map_pow, map_natCast, map_zero] at h
  exact h

/-! ### The comparison of rings and forms at the smooth lifting -/

/-- **The ring map `θ_Y : D' → Γ(Y, ⊤)`**: the inverse of `AdicCompletion.of` followed by
`E' ≃ Γ(Y, ⊤)`. -/
abbrev liftingRingHom :
    (presentationFormsData T.affineCrystallineSituation T.liftingPresentation).ring →+*
      GlobalCrystallineSituation.crysFormRing S T.crystallineThickening.obj :=
  formsRingHom T.exists_pow_eq_zero_liftingEnvelope T.liftingEnvelopeAlgHom

/-- The comparison of one-forms `Ω̂¹_{D'} → Ω_{X/S}(Y)` at the smooth lifting. -/
abbrev liftingFormsOneHom :
    (presentationFormsData T.affineCrystallineSituation T.liftingPresentation).Om 1 →ₛₗ[
      T.liftingRingHom]
      ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op T.crystallineThickening.obj)) :=
  formsOneHom T.exists_pow_eq_zero_liftingEnvelope T.liftingEnvelopeAlgHom
    T.isDPMorphism_liftingEnvelopeAlgHom

/-- The comparison of forms `Ω̂^a_{D'} → Ω^a_{X/S}(Y)` at the smooth lifting. -/
abbrev liftingFormsHom (a : ℕ) :
    (presentationFormsData T.affineCrystallineSituation T.liftingPresentation).Om a →ₛₗ[
      T.liftingRingHom]
      ⋀[GlobalCrystallineSituation.crysFormRing S T.crystallineThickening.obj]^a
        ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op T.crystallineThickening.obj)) :=
  formsHom T.exists_pow_eq_zero_liftingEnvelope T.liftingEnvelopeAlgHom
    T.isDPMorphism_liftingEnvelopeAlgHom a

omit [IsAffine S.X] [IsAffine S.S.scheme] in
/-- `θ_Y` is bijective. -/
theorem bijective_liftingRingHom : Function.Bijective T.liftingRingHom :=
  formsRingHom_bijective _ _ T.envelopeEquiv.bijective

omit [IsAffine S.X] in
/-- The comparison of forms at the smooth lifting is bijective in every degree. -/
theorem bijective_liftingFormsHom (a : ℕ) : Function.Bijective (T.liftingFormsHom a) :=
  formsHom_bijective _ _ _ T.liftingEnvelopeAlgHomInv T.isDPMorphism_liftingEnvelopeAlgHomInv
    T.liftingEnvelopeAlgHomInv_comp T.comp_liftingEnvelopeAlgHomInv a

omit [IsAffine S.X] [IsAffine S.S.scheme] in
/-- `θ_Y` undoes the identification `Γ(Y, ⊤) ≃ D'`. -/
theorem liftingRingHom_completedEnvelopeEquiv_symm (y : Γ(T.Y, ⊤)) :
    T.liftingRingHom (T.completedEnvelopeEquiv.symm y) = y := by
  have h1 : T.completedEnvelopeEquiv.symm y = AdicCompletion.of _ _ (T.envelopeEquiv.symm y) := by
    rw [completedEnvelopeEquiv_symm_apply, AdicCompletion.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply]
    rfl
  exact (congrArg T.liftingRingHom h1).trans
    ((formsRingHom_of _ _ _).trans (T.envelopeEquiv.apply_symm_apply y))

/-! ### The envelope map as a morphism of rings with forms -/

/-- **The envelope map `a : D → D'` of `ψ` as a morphism of rings with forms.** -/
abbrev envelopeFormsHom (e : ℕ) (he : T.levelBound ≤ e) :
    FormsData.Hom (presTowerFormsData (affineSituation S T.primeNilpotentX)
        (wholeSpacePresentation S T.primeNilpotentX) 0)
      (presentationFormsData T.affineCrystallineSituation T.liftingPresentation) :=
  FormsData.Hom.ofCompletion T.affineCrystallineSituation.p T.affineCrystallineSituation.A _
    (presTowerPrime_nilpotent T.affineCrystallineSituation
      (wholeSpacePresentation S T.primeNilpotentX)
      (wholeSpacePresentation_surjective S T.primeNilpotentX) 0) _
    (presentationEnvelope_prime_nilpotent T.affineCrystallineSituation T.liftingPresentation
      T.surjective_liftingPresentation)
    (T.levelEnvelopeMap e he) (T.isDPMorphism_levelEnvelopeMap e he)

/-- **The key ring identity `θ_Y ∘ a = ψ^♯ ∘ θ_{T(0)_e}`.** -/
theorem liftingRingHom_envelopeFormsHom (e : ℕ) (he : T.levelBound ≤ e)
    (x : (presTowerFormsData (affineSituation S T.primeNilpotentX)
      (wholeSpacePresentation S T.primeNilpotentX) 0).ring) :
    T.liftingRingHom ((T.envelopeFormsHom e he).toRingHom x) =
      crysRingMap S (T.levelHom e he).hom (T.levelRingHom e x) :=
  T.liftingRingHom_completedEnvelopeEquiv_symm _

/-- The envelope map before completion: `E(0) → Γ(T(0)_e, 𝒪) → Γ(Y, ⊤) ≃ E'`, as a morphism of
`A`-algebras. -/
def levelEnvelopeAlgHomLift (e : ℕ) (he : T.levelBound ≤ e) :
    wsEnvelope T.primeNilpotentX 0 →ₐ[(T.affineCrystallineSituation.A : Type u)]
      (presentationEnvelope T.affineCrystallineSituation T.liftingPresentation).object :=
  { T.envelopeEquiv.symm.toRingEquiv.toRingHom.comp
      ((T.levelSectionsMap e he).comp (envLevelMap T.primeNilpotentX 0 e)) with
    commutes' := fun a ↦ by
      have h1 : envLevelMap T.primeNilpotentX 0 e
          (algebraMap _ (wsEnvelope T.primeNilpotentX 0 : Type u) a) =
          crysBaseAppLE S (levelObj T.primeNilpotentX 0 e).obj a :=
        (levelEnvelopeAlgHom T.primeNilpotentX 0 e).commutes a
      have h2 : T.levelSectionsMap e he
          (crysBaseAppLE S (levelObj T.primeNilpotentX 0 e).obj a) =
          crysBaseAppLE S T.crystallineThickening.obj a :=
        crysRingMap_crysBase S (T.levelHom e he).hom a
      have h3 : crysBaseAppLE S T.crystallineThickening.obj a =
          algebraMap (T.affineCrystallineSituation.A : Type u) Γ(T.Y, ⊤) a :=
        (congrArg (fun i : Algebra (T.affineCrystallineSituation.A : Type u) Γ(T.Y, ⊤) ↦
          @algebraMap _ _ _ _ i a) T.liftingAlgebra_eq_crysTopAlgebra).symm
      change T.envelopeEquiv.symm (T.levelSectionsMap e he (envLevelMap T.primeNilpotentX 0 e
        (algebraMap _ _ a))) = _
      rw [h1, h2, h3]
      exact T.envelopeEquiv.symm.commutes a }

/-- The uncompleted envelope map is a divided power morphism. -/
theorem isDPMorphism_levelEnvelopeAlgHomLift (e : ℕ) (he : T.levelBound ≤ e) :
    IsDPMorphism (wsEnvelope T.primeNilpotentX 0).dividedPowers
      (presentationEnvelope T.affineCrystallineSituation T.liftingPresentation).object.dividedPowers
      (T.levelEnvelopeAlgHomLift e he).toRingHom :=
  T.isDPMorphism_envelopeEquiv_symm.comp _
    ((T.isDPMorphism_levelSectionsMap e he).comp _ (isDPMorphism_envLevelMap _ 0 e))

/-- The envelope map is the completion of the uncompleted one. -/
theorem levelEnvelopeMap_of (e : ℕ) (he : T.levelBound ≤ e)
    (y : wsEnvelope T.primeNilpotentX 0) :
    T.levelEnvelopeMap e he (AdicCompletion.of _ _ y) =
      AdicCompletion.of _ _ (T.levelEnvelopeAlgHomLift e he y) :=
  (T.levelEnvelopeRingHom_of e he y).trans (T.completedEnvelopeEquiv_symm_apply _)

/-- **The envelope map carries the unit zero-form to the unit zero-form.** -/
theorem envelopeFormsHom_psi_completedUnitZeroForm (e : ℕ) (he : T.levelBound ≤ e) :
    (T.envelopeFormsHom e he).psi 0
        (completedUnitZeroForm S.p (Γ(S.S.scheme, ⊤) : Type u)
          (wsEnvelope T.primeNilpotentX 0).dividedPowers) =
      completedUnitZeroForm S.p (Γ(S.S.scheme, ⊤) : Type u)
        (presentationEnvelope T.affineCrystallineSituation
          T.liftingPresentation).object.dividedPowers :=
  (FormsData.Hom.ofCompletion_psi_eq _ _ _ _ _ _ _ _ (T.levelEnvelopeAlgHomLift e he)
    (T.isDPMorphism_levelEnvelopeAlgHomLift e he) (T.levelEnvelopeMap_of e he) 0 _).trans
    (completedMapDifferentialForms_completedUnitZeroForm _ _ _ _ _ _)

/-! ### The base change of sections along `ψ` -/

/-- The reduction `θ_{T(0)_e} : D → Γ(T(0)_e, 𝒪)`, with values in the spelling of the ring of
sections over which the base change of sections along `ψ` is taken. -/
abbrev levelSheafRingHom (e : ℕ) :
    (presTowerFormsData (affineSituation S T.primeNilpotentX)
        (wholeSpacePresentation S T.primeNilpotentX) 0).ring →+*
      crysSheafRing S (levelObj T.primeNilpotentX 0 e).obj :=
  T.levelRingHom e

/-- `D'` as an algebra over `D` through the envelope map `a`. -/
abbrev envelopeFormsAlgebra (e : ℕ) (he : T.levelBound ≤ e) :
    Algebra (presTowerFormsData (affineSituation S T.primeNilpotentX)
        (wholeSpacePresentation S T.primeNilpotentX) 0).ring
      (presentationFormsData T.affineCrystallineSituation T.liftingPresentation).ring :=
  (T.envelopeFormsHom e he).toRingHom.toAlgebra

/-- `θ_Y : D' → Γ(Y, ⊤)` read into the sections over `Y` as an algebra over the sections over
`T(0)_e` through `ψ`; it is semilinear over `θ_{T(0)_e}` by the key ring identity. -/
def liftingAlongMap (e : ℕ) (he : T.levelBound ≤ e) :
    @LinearMap _ _ _ _ (T.levelSheafRingHom e)
      (presentationFormsData T.affineCrystallineSituation T.liftingPresentation).ring
      (ringAlong (T.levelHom e he).hom) _ _ (T.envelopeFormsAlgebra e he).toModule _ := by
  letI := T.envelopeFormsAlgebra e he
  exact
  { toFun := fun d ↦ ringAlongSection (T.levelHom e he).hom (T.liftingRingHom d)
    map_add' := fun d d' ↦ congrArg (ringAlongSection (T.levelHom e he).hom)
      (map_add T.liftingRingHom d d')
    map_smul' := fun c d ↦ by
      change ringAlongSection (T.levelHom e he).hom
          (T.liftingRingHom ((T.envelopeFormsHom e he).toRingHom c * d)) =
        ringAlongSection (T.levelHom e he).hom
          (crysSheafRingMap (T.levelHom e he).hom (T.levelSheafRingHom e c) *
            siteRingAlong (T.levelHom e he).hom
              (ringAlongSection (T.levelHom e he).hom (T.liftingRingHom d)))
      rw [map_mul, T.liftingRingHom_envelopeFormsHom e he c]
      rfl }

/-- `liftingAlongMap` is `θ_Y`. -/
theorem liftingAlongMap_apply (e : ℕ) (he : T.levelBound ≤ e)
    (d : (presentationFormsData T.affineCrystallineSituation T.liftingPresentation).ring) :
    siteRingAlong (T.levelHom e he).hom (T.liftingAlongMap e he d) = T.liftingRingHom d :=
  rfl

/-- `liftingAlongMap` is bijective. -/
theorem bijective_liftingAlongMap (e : ℕ) (he : T.levelBound ≤ e) :
    Function.Bijective (T.liftingAlongMap e he) :=
  T.bijective_liftingRingHom

/-! ### The comparison `M' → Γ(Y, ℱ)` -/

variable (Fc : QuasiCoherentCrystal S)

/-- **The base change `M' = M ⊗̂_D D'`** of the pair `(M, ∇)` of the crystal along the envelope
map `a`. -/
abbrev liftingConnModule (e : ℕ) (he : T.levelBound ≤ e) :
    FormsData.ConnModule
      (presentationFormsData T.affineCrystallineSituation T.liftingPresentation) :=
  (crystalPairConnModule T.primeNilpotentX Fc).baseChange (T.envelopeFormsHom e he)

/-- The inclusion `m ↦ 1 ⊗ m` of `M` into `M'`. -/
abbrev liftingInclusion (e : ℕ) (he : T.levelBound ≤ e) :
    (crystalPairConnModule T.primeNilpotentX Fc).carrier →ₛₗ[(T.envelopeFormsHom e he).toRingHom]
      (T.liftingConnModule Fc e he).carrier := by
  letI := T.envelopeFormsAlgebra e he
  exact CompletedConnection.baseChangeInclusion _ _ _ _

/-- **The base change of sections `D' ⊗_D M → Γ(Y, ℱ)`**, `d ⊗ m ↦ θ_Y(d) · ψ^*(m_e)`: the
reduction `D' ⊗_D M → Γ(Y, 𝒪_Y) ⊗ Γ(T(0)_e, ℱ)` followed by the base change of sections of the
crystal along `ψ`. -/
def liftingComponentRaw (e : ℕ) (he : T.levelBound ≤ e) :
    @TensorProduct (presTowerFormsData (affineSituation S T.primeNilpotentX)
        (wholeSpacePresentation S T.primeNilpotentX) 0).ring _
        (presentationFormsData T.affineCrystallineSituation
        T.liftingPresentation).ring (crystalPairConnModule T.primeNilpotentX Fc).carrier _ _
        (T.envelopeFormsAlgebra e he).toModule _ →+
      Fc.obj.val.obj (op T.crystallineThickening) := by
  letI := T.envelopeFormsAlgebra e he
  exact (crysBaseChangeAlong Fc.obj (T.levelHom e he)).comp
    (reduceRaw (T.levelSheafRingHom e) (T.liftingAlongMap e he)
      (levelZeroComponent T.primeNilpotentX T.prime_nilpotent Fc (e := e)))

/-- The base change of sections on a pure tensor. -/
theorem liftingComponentRaw_tmul (e : ℕ) (he : T.levelBound ≤ e)
    (d : (presentationFormsData T.affineCrystallineSituation T.liftingPresentation).ring)
    (m : (crystalPairConnModule T.primeNilpotentX Fc).carrier) :
    T.liftingComponentRaw Fc e he
        (@TensorProduct.tmul (presTowerFormsData (affineSituation S T.primeNilpotentX)
        (wholeSpacePresentation S T.primeNilpotentX) 0).ring _ _ _ _ _
          (T.envelopeFormsAlgebra e he).toModule _ d m) =
      T.liftingRingHom d • crysSiteRestrict Fc.obj (T.levelHom e he)
        (levelZeroComponent T.primeNilpotentX T.prime_nilpotent Fc (e := e) m) :=
  rfl

/-- The base change of sections is semilinear over `θ_Y`. -/
theorem liftingComponentRaw_smul (e : ℕ) (he : T.levelBound ≤ e)
    (c : (presentationFormsData T.affineCrystallineSituation T.liftingPresentation).ring)
    (t : @TensorProduct (presTowerFormsData (affineSituation S T.primeNilpotentX)
        (wholeSpacePresentation S T.primeNilpotentX) 0).ring _
        (presentationFormsData T.affineCrystallineSituation
        T.liftingPresentation).ring (crystalPairConnModule T.primeNilpotentX Fc).carrier _ _
        (T.envelopeFormsAlgebra e he).toModule _) :
    T.liftingComponentRaw Fc e he (c • t) =
      T.liftingRingHom c • T.liftingComponentRaw Fc e he t := by
  let := T.envelopeFormsAlgebra e he
  induction t using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul d m =>
    rw [TensorProduct.smul_tmul', smul_eq_mul, liftingComponentRaw_tmul, liftingComponentRaw_tmul,
      map_mul, mul_smul]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

/-- The base change of sections `D' ⊗_D M → Γ(Y, ℱ)` as a map semilinear over `θ_Y`. -/
def liftingComponentRawₛₗ (e : ℕ) (he : T.levelBound ≤ e) :
    @LinearMap _ _ _ _ T.liftingRingHom
      (@TensorProduct (presTowerFormsData (affineSituation S T.primeNilpotentX)
        (wholeSpacePresentation S T.primeNilpotentX) 0).ring _
        (presentationFormsData T.affineCrystallineSituation
        T.liftingPresentation).ring (crystalPairConnModule T.primeNilpotentX Fc).carrier _ _
        (T.envelopeFormsAlgebra e he).toModule _)
      (Fc.obj.val.obj (op T.crystallineThickening)) _ _
      (by letI := T.envelopeFormsAlgebra e he; infer_instance) _ := by
  letI := T.envelopeFormsAlgebra e he
  exact
  { toFun := T.liftingComponentRaw Fc e he
    map_add' := map_add _
    map_smul' := T.liftingComponentRaw_smul Fc e he }

/-- **The comparison `λ_Y : M' → Γ(Y, ℱ)`**, semilinear over `θ_Y`: since `p` is nilpotent in
`D'`, the completion `M'` is `D' ⊗_D M`, on which `λ_Y` is the base change of sections. -/
def liftingComponent (e : ℕ) (he : T.levelBound ≤ e) :
    (T.liftingConnModule Fc e he).carrier →ₛₗ[T.liftingRingHom]
      Fc.obj.val.obj (op T.crystallineThickening) := by
  letI := T.envelopeFormsAlgebra e he
  exact (T.liftingComponentRawₛₗ Fc e he).comp
    (ofLinearEquivOfPowEqZero T.exists_pow_eq_zero_liftingFormsRing _).symm.toLinearMap

/-- `λ_Y` on `d • (1 ⊗ m)` is `θ_Y(d) · ψ^*(m_e)`. -/
theorem liftingComponent_smul_liftingInclusion (e : ℕ) (he : T.levelBound ≤ e)
    (d : (presentationFormsData T.affineCrystallineSituation T.liftingPresentation).ring)
    (m : (crystalPairConnModule T.primeNilpotentX Fc).carrier) :
    T.liftingComponent Fc e he (d • T.liftingInclusion Fc e he m) =
      T.liftingRingHom d • crysSiteRestrict Fc.obj (T.levelHom e he)
        (levelZeroComponent T.primeNilpotentX T.prime_nilpotent Fc (e := e) m) := by
  let := T.envelopeFormsAlgebra e he
  have h : d • T.liftingInclusion Fc e he m =
      ofLinearEquivOfPowEqZero T.exists_pow_eq_zero_liftingFormsRing _
        (@TensorProduct.tmul (presTowerFormsData (affineSituation S T.primeNilpotentX)
        (wholeSpacePresentation S T.primeNilpotentX) 0).ring _ _ _ _ _
          (T.envelopeFormsAlgebra e he).toModule _ d m) :=
    (CompletedConnection.of_tmul_eq_smul_inclusion _ _ _ _ d m).symm
  rw [h]
  change T.liftingComponentRaw Fc e he ((ofLinearEquivOfPowEqZero
    T.exists_pow_eq_zero_liftingFormsRing _).symm (ofLinearEquivOfPowEqZero
      T.exists_pow_eq_zero_liftingFormsRing _ _)) = _
  refine (congrArg (T.liftingComponentRaw Fc e he)
    ((ofLinearEquivOfPowEqZero T.exists_pow_eq_zero_liftingFormsRing _).symm_apply_apply _)).trans
    ?_
  exact T.liftingComponentRaw_tmul Fc e he d m

/-- **`λ_Y (1 ⊗ m) = ψ^*(m_e)`.** -/
theorem liftingComponent_liftingInclusion (e : ℕ) (he : T.levelBound ≤ e)
    (m : (crystalPairConnModule T.primeNilpotentX Fc).carrier) :
    T.liftingComponent Fc e he (T.liftingInclusion Fc e he m) =
      crysSiteRestrict Fc.obj (T.levelHom e he)
        (levelZeroComponent T.primeNilpotentX T.prime_nilpotent Fc (e := e) m) := by
  have h := T.liftingComponent_smul_liftingInclusion Fc e he 1 m
  rwa [one_smul, map_one, one_smul] at h

/-- **`λ_Y` is bijective** once `p^{N+e} = 0` in `E(0)`: it is the base change of sections of the
crystal along `ψ` (bijective, `ℱ` being a crystal) after the bijective reduction. -/
theorem bijective_liftingComponent (e : ℕ) (he : T.levelBound ≤ e)
    (hpe : ((S.p ^ (_root_.Crystalline.uniformLevel (affineSituation S T.primeNilpotentX) + e) :
      ℕ) : wsEnvelope T.primeNilpotentX 0) = 0) :
    Function.Bijective (T.liftingComponent Fc e he) := by
  let := T.envelopeFormsAlgebra e he
  have := isQuasicoherent_ambientSchemeOf Fc.obj
    (isLocallyQuasiCoherent_of_isQuasicoherentOnSite Fc.obj Fc.property.1)
    (levelObj T.primeNilpotentX 0 e)
  have hθ : Function.Bijective (T.levelSheafRingHom e) :=
    formsRingHom_bijective _ _ (bijective_envLevelMap_of_pow_eq_zero hpe)
  have hlam : Function.Bijective
      (levelZeroComponent T.primeNilpotentX T.prime_nilpotent Fc (e := e)) :=
    bijective_levelZeroComponent T.primeNilpotentX T.prime_nilpotent Fc hpe
  have hraw : Function.Bijective (T.liftingComponentRaw Fc e he) :=
    (bijective_crysBaseChangeAlong Fc.obj (T.levelHom e he) Fc.property.2).comp
      (bijective_reduceRaw (T.levelSheafRingHom e) hθ (T.liftingAlongMap e he)
        (T.bijective_liftingAlongMap e he)
        (levelZeroComponent T.primeNilpotentX T.prime_nilpotent Fc (e := e)) hlam)
  exact hraw.comp (ofLinearEquivOfPowEqZero T.exists_pow_eq_zero_liftingFormsRing _).symm.bijective

/-! ### The connection -/

/-- The reduction `M ⊗̂_D Ω̂¹_D → Γ(T(0)_e, ℱ) ⊗ Ω_{X/S}(T(0)_e)` at the level. -/
abbrev levelReduceTensor (e : ℕ) :=
  reduceTensor (levelZeroRingHom T.primeNilpotentX T.prime_nilpotent (e := e))
    (exists_pow_eq_zero_presTowerRing T.primeNilpotentX T.prime_nilpotent)
    (levelZeroComponent T.primeNilpotentX T.prime_nilpotent Fc (e := e))
    (levelZeroFormsOneHom T.primeNilpotentX T.prime_nilpotent (e := e))

/-- The reduction `M' ⊗̂_{D'} Ω̂¹_{D'} → Γ(Y, ℱ) ⊗ Ω_{X/S}(Y)` at the smooth lifting. -/
abbrev liftingReduceTensor (e : ℕ) (he : T.levelBound ≤ e) :=
  reduceTensor T.liftingRingHom T.exists_pow_eq_zero_liftingFormsRing
    (T.liftingComponent Fc e he) T.liftingFormsOneHom

/-- **The reductions are compatible with `ψ`**: reducing at `Y` the image of `z` under
`M ⊗̂ Ω̂¹_D → M' ⊗̂ Ω̂¹_{D'}` is restricting along `ψ` the reduction of `z` at `T(0)_e`. -/
theorem liftingReduceTensor_baseChangeValues (e : ℕ) (he : T.levelBound ≤ e)
    (z : CompletedTensor S.p (presTowerFormsData (affineSituation S T.primeNilpotentX)
      (wholeSpacePresentation S T.primeNilpotentX) 0).ring
      ((presTowerFormsData (affineSituation S T.primeNilpotentX)
        (wholeSpacePresentation S T.primeNilpotentX) 0).Om 1)
      (crystalPairConnModule T.primeNilpotentX Fc).carrier) :
    T.liftingReduceTensor Fc e he
        (@CompletedConnection.baseChangeValues S.p _ _ _ _ (T.envelopeFormsAlgebra e he) _ _ _ _ _
          _ _ _ _ ((T.envelopeFormsHom e he).psi 1) z) =
      restrictTensor Fc.obj (T.levelHom e he) (T.levelReduceTensor Fc e z) := by
  let := T.envelopeFormsAlgebra e he
  have h := completedTensor_addMonoidHom_ext_of_pow_eq_zero
    (exists_pow_eq_zero_presTowerRing T.primeNilpotentX T.prime_nilpotent)
    (f := (T.liftingReduceTensor Fc e he).comp
      (CompletedConnection.baseChangeValues _ _ _ _ _ _
        ((T.envelopeFormsHom e he).psi 1)).toAddMonoidHom)
    (g := (restrictTensor Fc.obj (T.levelHom e he)).comp (T.levelReduceTensor Fc e)) fun m ω ↦ ?_
  · exact DFunLike.congr_fun h z
  · refine (congrArg (T.liftingReduceTensor Fc e he)
      (CompletedConnection.baseChangeValues_of_tmul _ _ _ _ _ _ _ m ω)).trans
      ((reduceTensor_of_tmul _ _ _ _ _ _).trans ?_)
    refine Eq.trans ?_ (congrArg (restrictTensor Fc.obj (T.levelHom e he))
      (reduceTensor_of_tmul _ _ _ _ m ω)).symm
    refine Eq.trans ?_ (restrictTensor_tmul Fc.obj (T.levelHom e he) _ _).symm
    exact congrArg₂ (· ⊗ₜ ·) (T.liftingComponent_liftingInclusion Fc e he m)
      (formsOneHom_naturality T.exists_pow_eq_zero_liftingEnvelope T.liftingEnvelopeAlgHom
        T.isDPMorphism_liftingEnvelopeAlgHom
        (exists_pow_eq_zero_wsEnvelope T.primeNilpotentX T.prime_nilpotent 0)
        (levelEnvelopeAlgHom T.primeNilpotentX 0 e)
        (isDPMorphism_levelEnvelopeAlgHom T.primeNilpotentX 0 e) (T.levelHom e he).hom
        (T.envelopeFormsHom e he) (T.liftingRingHom_envelopeFormsHom e he) ω)

/-- The canonical connection of [Stacks, Tag 07J6] on `Γ(Y, ℱ)`. -/
abbrev liftingRingConnection :=
  ringConnection T.liftingObject.top_le_preimage_baseOpen T.liftingObject.isAffineOpen_baseOpen
    (bijective_crysExtensionSectionsMap_affine Fc.property.1 T.liftingObject)

/-- The connection compatibility on the generators `d · (1 ⊗ m)` of `M'`: both sides are
`θ_Y(d) · ψ^*(∇_{T(0)_e} m_e) + ψ^*(m_e) ⊗ d θ_Y(d)`. -/
theorem liftingRingConnection_liftingComponent_smul_liftingInclusion (e : ℕ)
    (he : T.levelBound ≤ e)
    (d : (presentationFormsData T.affineCrystallineSituation T.liftingPresentation).ring)
    (m : (crystalPairConnModule T.primeNilpotentX Fc).carrier) :
    (T.liftingRingConnection Fc).toAddMonoidHom
        (T.liftingComponent Fc e he (d • T.liftingInclusion Fc e he m)) =
      T.liftingReduceTensor Fc e he ((T.liftingConnModule Fc e he).nabla
        (d • T.liftingInclusion Fc e he m)) := by
  let := T.envelopeFormsAlgebra e he
  have hnat : (T.liftingRingConnection Fc).toAddMonoidHom (crysSiteRestrict Fc.obj
      (T.levelHom e he) (levelZeroComponent T.primeNilpotentX T.prime_nilpotent Fc (e := e) m)) =
      restrictTensor Fc.obj (T.levelHom e he)
        (T.levelReduceTensor Fc e ((crystalPairConnModule T.primeNilpotentX Fc).nabla m)) :=
    (ringConnection_naturality T.liftingObject.top_le_preimage_baseOpen
      T.liftingObject.isAffineOpen_baseOpen
      (levelAffineObject T.primeNilpotentX 0 e).top_le_preimage_baseOpen
      (levelAffineObject T.primeNilpotentX 0 e).isAffineOpen_baseOpen
      (bijective_crysExtensionSectionsMap_affine Fc.property.1 T.liftingObject)
      (bijective_crysExtensionSectionsMap_affine Fc.property.1
        (levelAffineObject T.primeNilpotentX 0 e)) (T.levelHom e he) _).trans
      (congrArg (restrictTensor Fc.obj (T.levelHom e he))
        (reduceTensor_crystalPairConnModule_nabla T.primeNilpotentX T.prime_nilpotent Fc
          (e := e) m))
  have hL : (T.liftingRingConnection Fc).toAddMonoidHom
      (T.liftingComponent Fc e he (d • T.liftingInclusion Fc e he m)) =
      T.liftingRingHom d • restrictTensor Fc.obj (T.levelHom e he)
        (T.levelReduceTensor Fc e ((crystalPairConnModule T.primeNilpotentX Fc).nabla m)) +
      crysSiteRestrict Fc.obj (T.levelHom e he)
          (levelZeroComponent T.primeNilpotentX T.prime_nilpotent Fc (e := e) m) ⊗ₜ
        GlobalCrystallineSituation.crysD S T.crystallineThickening.obj (T.liftingRingHom d) :=
    (congrArg (T.liftingRingConnection Fc).toAddMonoidHom
      (T.liftingComponent_smul_liftingInclusion Fc e he d m)).trans
      (((T.liftingRingConnection Fc).leibniz _ _).trans
        (congrArg₂ (· + ·) (congrArg (T.liftingRingHom d • ·) hnat) rfl))
  have hR : T.liftingReduceTensor Fc e he ((T.liftingConnModule Fc e he).nabla
      (d • T.liftingInclusion Fc e he m)) =
      T.liftingRingHom d • restrictTensor Fc.obj (T.levelHom e he)
        (T.levelReduceTensor Fc e ((crystalPairConnModule T.primeNilpotentX Fc).nabla m)) +
      crysSiteRestrict Fc.obj (T.levelHom e he)
          (levelZeroComponent T.primeNilpotentX T.prime_nilpotent Fc (e := e) m) ⊗ₜ
        GlobalCrystallineSituation.crysD S T.crystallineThickening.obj (T.liftingRingHom d) := by
    refine (congrArg (T.liftingReduceTensor Fc e he)
      ((T.liftingConnModule Fc e he).nabla.leibniz d _)).trans ?_
    refine (map_add (T.liftingReduceTensor Fc e he) _ _).trans (congrArg₂ (· + ·) ?_ ?_)
    · refine (reduceTensor_smul _ _ _ _ d _).trans (congrArg (T.liftingRingHom d • ·) ?_)
      refine (congrArg (T.liftingReduceTensor Fc e he)
        (CompletedConnection.baseChange_inclusion _ _ _ _ _ _ _ _ _ _ _ _ m)).trans ?_
      exact T.liftingReduceTensor_baseChangeValues Fc e he _
    · refine (reduceTensor_of_tmul _ _ _ _ _ _).trans ?_
      exact congrArg₂ (· ⊗ₜ ·) (T.liftingComponent_liftingInclusion Fc e he m)
        (formsOneHom_diff _ _ _ d)
  exact hL.trans hR.symm

/-- **The connection compatibility at the smooth lifting**: the canonical connection on `Γ(Y, ℱ)`
applied to `λ_Y(x)` is the reduction of the base-changed connection `∇'(x)`.  On `d · (1 ⊗ m)`
both sides are `θ_Y(d) · ψ^*(∇_{T(0)_e} m_e) + ψ^*(m_e) ⊗ d θ_Y(d)`, by the Leibniz rules, the
naturality of the canonical connection along `ψ`, and the identification of the connection of
the pair at the level (`...SmallSite.reduceTensor_crystalPairConnModule_nabla`). -/
theorem liftingRingConnection_liftingComponent (e : ℕ) (he : T.levelBound ≤ e)
    (x : (T.liftingConnModule Fc e he).carrier) :
    (T.liftingRingConnection Fc).toAddMonoidHom (T.liftingComponent Fc e he x) =
      T.liftingReduceTensor Fc e he ((T.liftingConnModule Fc e he).nabla x) := by
  let := T.envelopeFormsAlgebra e he
  let e0 := ofLinearEquivOfPowEqZero T.exists_pow_eq_zero_liftingFormsRing
    ((presentationFormsData T.affineCrystallineSituation T.liftingPresentation).ring ⊗[
      (presTowerFormsData (affineSituation S T.primeNilpotentX)
        (wholeSpacePresentation S T.primeNilpotentX) 0).ring]
      (crystalPairConnModule T.primeNilpotentX Fc).carrier)
  let F1 := (T.liftingRingConnection Fc).toAddMonoidHom.comp
    ((T.liftingComponent Fc e he).toAddMonoidHom.comp e0.toAddMonoidHom)
  let F2 := (T.liftingReduceTensor Fc e he).comp
    ((AddMonoidHom.mk' (T.liftingConnModule Fc e he).nabla
      (T.liftingConnModule Fc e he).nabla.map_add).comp e0.toAddMonoidHom)
  have key : ∀ t, F1 t = F2 t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact (map_zero F1).trans (map_zero F2).symm
    | add a b ha hb => exact (map_add F1 a b).trans ((congrArg₂ (· + ·) ha hb).trans
        (map_add F2 a b).symm)
    | tmul d m =>
      have hx : @Eq (T.liftingConnModule Fc e he).carrier (e0 (d ⊗ₜ m))
          (d • T.liftingInclusion Fc e he m) :=
        CompletedConnection.of_tmul_eq_smul_inclusion _ _ _ _ d m
      exact (congrArg (fun y ↦ (T.liftingRingConnection Fc).toAddMonoidHom
        (T.liftingComponent Fc e he y)) hx).trans
        ((T.liftingRingConnection_liftingComponent_smul_liftingInclusion Fc e he d m).trans
          (congrArg (fun y ↦ T.liftingReduceTensor Fc e he ((T.liftingConnModule Fc e he).nabla y))
            hx).symm)
  have hx : @Eq (T.liftingConnModule Fc e he).carrier (e0 (e0.symm x)) x := e0.apply_symm_apply x
  exact (congrArg (fun y ↦ (T.liftingRingConnection Fc).toAddMonoidHom
    (T.liftingComponent Fc e he y)) hx).symm.trans ((key (e0.symm x)).trans
      (congrArg (fun y ↦ T.liftingReduceTensor Fc e he ((T.liftingConnModule Fc e he).nabla y))
        hx))

/-! ### The comparison of complexes at the smooth lifting -/

/-- **The morphism of complexes `M' ⊗^∧_{D'} Ω^*_{D'} → Γ(Y, ℱ ⊗ Ω^•_{X/S})`**, in degree `a` the
map `x ⊗ ω ↦ λ_Y(x) ⊗ Θ_Y(ω)`. -/
def liftingDeRhamComplexHom (e : ℕ) (he : T.levelBound ≤ e) :
    (T.liftingConnModule Fc e he).complex ⟶
      affineDeRhamSectionsComplex Fc.property.1 T.liftingObject :=
  (T.liftingConnModule Fc e he).reduceComplexHom T.liftingRingHom
    T.exists_pow_eq_zero_liftingFormsRing T.liftingFormsOneHom T.liftingFormsHom
    (fun a ω η ↦ formsHom_wedge _ _ _ a ω η)
    (fun a ↦ (crysDeRhamComplex S).differential a T.crystallineThickening.obj)
    (fun a ω ↦ formsHom_deRham _ _ _ a ω) (T.liftingComponent Fc e he)
    (T.liftingRingConnection Fc).toAddMonoidHom
    (T.liftingRingConnection_liftingComponent Fc e he)
    (fun a ↦ extDiff T.liftingObject.top_le_preimage_baseOpen T.liftingObject.isAffineOpen_baseOpen
      (bijective_crysExtensionSectionsMap_affine Fc.property.1 T.liftingObject) a)
    (fun a n ω ↦ extDiff_tmul _ _ _ a n ω)
    (fun a ↦ AddMonoidHom.ext fun x ↦ extDiff_comp_extDiff _ _ _
      (injective_crysSecondExtensionSectionsMap_affine Fc.property.1 T.liftingObject) a x)

/-- The degree-`a` component of `liftingDeRhamComplexHom` is `x ⊗ ω ↦ λ_Y(x) ⊗ Θ_Y(ω)`. -/
theorem liftingDeRhamComplexHom_f_of_tmul (e : ℕ) (he : T.levelBound ≤ e) (a : ℕ)
    (x : (T.liftingConnModule Fc e he).carrier)
    (ω : (presentationFormsData T.affineCrystallineSituation T.liftingPresentation).Om a) :
    ((T.liftingDeRhamComplexHom Fc e he).f a).hom
        (toCompletedTensor T.affineCrystallineSituation.p _ _ _ (x ⊗ₜ ω)) =
      T.liftingComponent Fc e he x ⊗ₜ[GlobalCrystallineSituation.crysFormRing S
        T.crystallineThickening.obj] T.liftingFormsHom a ω :=
  reduceTensor_of_tmul _ _ _ _ x ω

/-- **`liftingDeRhamComplexHom` is an isomorphism** once `p^{N+e} = 0` in `E(0)`. -/
theorem isIso_liftingDeRhamComplexHom (e : ℕ) (he : T.levelBound ≤ e)
    (hpe : ((S.p ^ (_root_.Crystalline.uniformLevel (affineSituation S T.primeNilpotentX) + e) :
      ℕ) : wsEnvelope T.primeNilpotentX 0) = 0) :
    IsIso (T.liftingDeRhamComplexHom Fc e he) :=
  (T.liftingConnModule Fc e he).isIso_reduceComplexHom T.liftingRingHom
    T.exists_pow_eq_zero_liftingFormsRing _ _ _ _ _ _ _ _ _ _ _ T.bijective_liftingRingHom
    (T.bijective_liftingComponent Fc e he hpe) T.bijective_liftingFormsHom

end Crystalline.GlobalCrystallineSituation.SmallSite.Situation07MW

end
