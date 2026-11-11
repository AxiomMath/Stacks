module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.SmoothPresentationCohomology07LH
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.SmoothLiftingEnvelope07MW
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.SmoothLiftingLevelMorphism07MW
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.WholeSpaceLevelProducts
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LevelEnvelopeIdentification07MW
public import StacksFrontier.AlgebraicGeometry.Crystalline.AffineObjectFormsDPNaturality

/-!
# A morphism from an affine smooth lifting to a level of the system, and its envelope map

In the situation of [Stacks, Tag 07MW] (`...SmallSite.Situation07MW`) with `X` and `Y` affine, let
`D` be the completed divided power envelope of the canonical presentation of `C = Γ(X, 𝒪_X)` and
`T(0)_e` the finite levels of the system of [Stacks, Tag 07JN].  The object `(X, Y, γ)` of part (1)
of the remark is an affine object of `Cris(X/S)`, so it maps to `T(0)_e` for every large `e`
([Stacks, Tag 07HP], `...SmallSite.exists_forall_le_hom_wholeSpaceLevel`).  This module fixes such
a morphism `ψ` and reads it as the divided power `A`-algebra map

`a : D → Γ(T(0)_e, 𝒪) → Γ(Y, 𝒪_Y) = D'`

into the completed envelope `D'` of the presentation `Γ(Y, 𝒪_Y) → C` (which is `Γ(Y, 𝒪_Y)` itself,
`...SmallSite.Situation07MW.completedEnvelopeEquiv`).  The map `a` is compatible with the
augmentations to `C`, so [Stacks, Lemma 60.21.4, Tag 07LH] applies to it: the base change map
`M ⊗^∧_D Ω^*_D → M' ⊗^∧_{D'} Ω^*_{D'}` of the pair of a crystal is a quasi-isomorphism
(`...SmallSite.Situation07MW.quasiIso_baseChangeHom_levelEnvelopeMap`).

## Main definitions

* `Situation07MW.levelBound`, `Situation07MW.levelHom` — the morphism `ψ : (X, Y, γ) ⟶ T(0)_e`
  for `e ≥ levelBound`.
* `Situation07MW.levelEnvelopeMap` — the divided power `A`-algebra map `a : D → D'` it induces.

## Main results

* `Situation07MW.isDPMorphism_levelEnvelopeMap`,
  `Situation07MW.completedEnvelopeAugmentation_comp_levelEnvelopeMap` — `a` is a divided power
  morphism compatible with the augmentations.
* `Situation07MW.quasiIso_baseChangeHom_levelEnvelopeMap` — the base change along `a` of the pair
  of a crystal in quasi-coherent modules is a quasi-isomorphism.

## What is and is not proved

Everything stated is proved.  The morphism `ψ` is a choice (`Classical.choice` of the existence
statement of [Stacks, Tag 07HP]); everything here holds for that choice.  The source obtains the
map `D → D'` from a lift of the variables (`Crystalline.exists_smoothPresentationMap`); here it is
read off `ψ` instead, so that it is the map of sections of a morphism of `Cris(X/S)`, which is what
the comparison of de Rham complexes of sections needs.  No tag attribute is placed.

## References

* [Stacks Project, Tag 07MW](https://stacks.math.columbia.edu/tag/07MW)
* [Stacks Project, Lemma 60.21.4, Tag 07LH](https://stacks.math.columbia.edu/tag/07LH)
* [Stacks Project, Lemma 60.5.6, Tag 07HP](https://stacks.math.columbia.edu/tag/07HP)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite DividedPowers Simplicial
open scoped AlgebraicGeometry

universe u

namespace Crystalline.GlobalCrystallineSituation.SmallSite.Situation07MW

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.X] [IsAffine S.S.scheme]
  (T : Situation07MW S) [IsAffine T.Y]

attribute [local instance] tensorPowerEnvelopeAlgebraInstance presentationEnvelopeAlgebraInst
  Situation07MW.liftingAlgebra wsEnvelopeTopAlgebra

omit [IsAffine S.S.scheme] in
/-- The object `(X, Y, γ)` of `Cris(X/S)` is an affine object: `X` and `Y` are affine. -/
theorem isAffineObject_crystallineThickening : IsAffineObject S T.crystallineThickening :=
  ⟨inferInstanceAs (IsAffine S.X), inferInstanceAs (IsAffine T.Y)⟩

/-- **[Stacks, Tag 07HP] at the smooth lifting**: `(X, Y, γ)` maps to every large level `T(0)_e`. -/
theorem exists_levelHom :
    ∃ N, ∀ e, N ≤ e →
      Nonempty (T.crystallineThickening ⟶ levelObj T.primeNilpotentX 0 e) :=
  exists_forall_le_hom_wholeSpaceLevel T.primeNilpotentX T.isAffineObject_crystallineThickening

/-- A level past which `(X, Y, γ)` maps to `T(0)_e`. -/
def levelBound : ℕ := T.exists_levelHom.choose

/-- **The morphism `ψ : (X, Y, γ) ⟶ T(0)_e`** of `Cris(X/S)`, for `e ≥ levelBound`, a choice. -/
def levelHom (e : ℕ) (he : T.levelBound ≤ e) :
    T.crystallineThickening ⟶ levelObj T.primeNilpotentX 0 e :=
  (T.exists_levelHom.choose_spec e he).some

/-- The map on sections `ψ^♯ : Γ(T(0)_e, 𝒪) → Γ(Y, 𝒪_Y)` of the morphism `ψ`. -/
abbrev levelSectionsMap (e : ℕ) (he : T.levelBound ≤ e) :
    GlobalCrystallineSituation.crysFormRing S (levelObj T.primeNilpotentX 0 e).obj →+*
      GlobalCrystallineSituation.crysFormRing S T.crystallineThickening.obj :=
  ((GlobalCrystallineSituation.structureRingCatPresheaf S).map (T.levelHom e he).hom.op).hom

/-- `ψ^♯` is a divided power morphism. -/
theorem isDPMorphism_levelSectionsMap (e : ℕ) (he : T.levelBound ≤ e) :
    IsDPMorphism (crysDividedPowers S (levelObj T.primeNilpotentX 0 e).obj)
      (crysDividedPowers S T.crystallineThickening.obj) (T.levelSectionsMap e he) :=
  isDPMorphism_sheafRingMap (T.levelHom e he)

/-- The reduction `D → Γ(T(0)_e, 𝒪)` of the comparison of de Rham complexes at the level. -/
abbrev levelRingHom (e : ℕ) :
    (presTowerFormsData (affineSituation S T.primeNilpotentX)
        (wholeSpacePresentation S T.primeNilpotentX) 0).ring →+*
      GlobalCrystallineSituation.crysFormRing S (levelObj T.primeNilpotentX 0 e).obj :=
  formsRingHom (E := wsEnvelope T.primeNilpotentX 0)
    (exists_pow_eq_zero_wsEnvelope T.primeNilpotentX T.prime_nilpotent 0)
    (levelEnvelopeAlgHom T.primeNilpotentX 0 e)

/-- **The envelope map `a : D → D'` of `ψ`**, as a ring map: the reduction
`D → Γ(T(0)_e, 𝒪)`, then `ψ^♯`, then the identification `Γ(Y, 𝒪_Y) ≃ D'`. -/
def levelEnvelopeRingHom (e : ℕ) (he : T.levelBound ≤ e) :
    (presTowerFormsData (affineSituation S T.primeNilpotentX)
        (wholeSpacePresentation S T.primeNilpotentX) 0).ring →+*
      AdicCompletion (pAdicIdeal (A :=
        (presentationEnvelope T.affineCrystallineSituation T.liftingPresentation).object)
        T.affineCrystallineSituation.p)
        (presentationEnvelope T.affineCrystallineSituation T.liftingPresentation).object :=
  T.completedEnvelopeEquiv.symm.toRingEquiv.toRingHom.comp
    ((T.levelSectionsMap e he).comp (T.levelRingHom e))

/-- The envelope map on the image of the envelope `E(0)`. -/
theorem levelEnvelopeRingHom_of (e : ℕ) (he : T.levelBound ≤ e)
    (y : wsEnvelope T.primeNilpotentX 0) :
    T.levelEnvelopeRingHom e he (AdicCompletion.of _ _ y) =
      T.completedEnvelopeEquiv.symm
        (T.levelSectionsMap e he (envLevelMap T.primeNilpotentX 0 e y)) :=
  congrArg (fun z ↦ T.completedEnvelopeEquiv.symm (T.levelSectionsMap e he z))
    (formsRingHom_of _ _ y)

/-- The envelope map on scalars from the base. -/
theorem levelEnvelopeRingHom_algebraMap (e : ℕ) (he : T.levelBound ≤ e)
    (a : (T.affineCrystallineSituation.A : Type u)) :
    T.levelEnvelopeRingHom e he (algebraMap _ (AdicCompletion
      (pAdicIdeal (A := (wsEnvelope T.primeNilpotentX 0 : Type u)) S.p)
      (wsEnvelope T.primeNilpotentX 0)) a) =
      algebraMap _ (AdicCompletion (pAdicIdeal (A :=
        (presentationEnvelope T.affineCrystallineSituation T.liftingPresentation).object)
        T.affineCrystallineSituation.p)
        (presentationEnvelope T.affineCrystallineSituation T.liftingPresentation).object) a := by
  have h0 : algebraMap (T.affineCrystallineSituation.A : Type u) (AdicCompletion
      (pAdicIdeal (A := (wsEnvelope T.primeNilpotentX 0 : Type u)) S.p)
      (wsEnvelope T.primeNilpotentX 0)) a =
      AdicCompletion.of _ _ (algebraMap (T.affineCrystallineSituation.A : Type u)
        (wsEnvelope T.primeNilpotentX 0) a) := by
    rw [AdicCompletion.algebraMap_apply]
  have h1 : envLevelMap T.primeNilpotentX 0 e
      (algebraMap _ (wsEnvelope T.primeNilpotentX 0 : Type u) a) =
      crysBaseAppLE S (levelObj T.primeNilpotentX 0 e).obj a :=
    letI := crysTopAlgebra S (levelObj T.primeNilpotentX 0 e).obj
    (levelEnvelopeAlgHom T.primeNilpotentX 0 e).commutes a
  have h2 : T.levelSectionsMap e he (crysBaseAppLE S (levelObj T.primeNilpotentX 0 e).obj a) =
      crysBaseAppLE S T.crystallineThickening.obj a :=
    crysRingMap_crysBase S (T.levelHom e he).hom a
  have h3 : crysBaseAppLE S T.crystallineThickening.obj a =
      algebraMap (T.affineCrystallineSituation.A : Type u) Γ(T.Y, ⊤) a :=
    (congrArg (fun i : Algebra (T.affineCrystallineSituation.A : Type u) Γ(T.Y, ⊤) ↦
      @algebraMap _ _ _ _ i a) T.liftingAlgebra_eq_crysTopAlgebra).symm
  refine (congrArg (T.levelEnvelopeRingHom e he) h0).trans ?_
  refine (T.levelEnvelopeRingHom_of e he _).trans ?_
  rw [h1, h2, h3, AlgEquiv.commutes]

/-- **The envelope map `a : D → D'` of `ψ`**, as a morphism of `A`-algebras. -/
def levelEnvelopeMap (e : ℕ) (he : T.levelBound ≤ e) :
    AdicCompletion
        (pAdicIdeal (A := (tensorPowerEnvelope (affineSituation S T.primeNilpotentX)
          (wholeSpacePresentation S T.primeNilpotentX) 0).object)
          (affineSituation S T.primeNilpotentX).p)
        (tensorPowerEnvelope (affineSituation S T.primeNilpotentX)
          (wholeSpacePresentation S T.primeNilpotentX) 0).object →ₐ[
        (affineSituation S T.primeNilpotentX).A]
      AdicCompletion (pAdicIdeal (A :=
        (presentationEnvelope (affineSituation S T.primeNilpotentX) T.liftingPresentation).object)
        (affineSituation S T.primeNilpotentX).p)
        (presentationEnvelope (affineSituation S T.primeNilpotentX) T.liftingPresentation).object :=
  { T.levelEnvelopeRingHom e he with
    commutes' := T.levelEnvelopeRingHom_algebraMap e he }

/-- The envelope map is the ring map `levelEnvelopeRingHom`. -/
theorem levelEnvelopeMap_apply (e : ℕ) (he : T.levelBound ≤ e)
    (x : AdicCompletion (pAdicIdeal (A := (wsEnvelope T.primeNilpotentX 0 : Type u)) S.p)
      (wsEnvelope T.primeNilpotentX 0)) :
    T.levelEnvelopeMap e he x = T.levelEnvelopeRingHom e he x :=
  rfl

/-- **The envelope map is a divided power morphism** for the completed divided powers. -/
theorem isDPMorphism_levelEnvelopeMap (e : ℕ) (he : T.levelBound ≤ e) :
    IsDPMorphism (completionDividedPowers T.affineCrystallineSituation.p
        (tensorPowerEnvelope T.affineCrystallineSituation
          (wholeSpacePresentation S T.primeNilpotentX) 0).object.dividedPowers
        (tensorPowerEnvelope_prime_nilpotent T.affineCrystallineSituation _
          (wholeSpacePresentation_surjective S T.primeNilpotentX) 0))
      (completionDividedPowers T.affineCrystallineSituation.p
        (presentationEnvelope T.affineCrystallineSituation
          T.liftingPresentation).object.dividedPowers
        (presentationEnvelope_prime_nilpotent T.affineCrystallineSituation T.liftingPresentation
          T.surjective_liftingPresentation))
      (T.levelEnvelopeMap e he).toRingHom := by
  have hsymm : T.completedEnvelopeEquiv.symm.toRingEquiv.toRingHom =
      (completionDPMorphism _
        (presentationEnvelope T.affineCrystallineSituation
          T.liftingPresentation).object.dividedPowers
        T.affineCrystallineSituation.p (presentationEnvelope_prime_nilpotent
          T.affineCrystallineSituation T.liftingPresentation
          T.surjective_liftingPresentation)).toRingHom.comp
        T.envelopeEquiv.symm.toRingEquiv.toRingHom :=
    RingHom.ext fun x ↦ T.completedEnvelopeEquiv_symm_apply x
  let := crysTopAlgebra S (levelObj T.primeNilpotentX 0 e).obj
  have hred := isDPMorphism_completedFormsRingHom S.p (wsEnvelope T.primeNilpotentX 0).dividedPowers
    (tensorPowerEnvelope_prime_nilpotent T.affineCrystallineSituation _
      (wholeSpacePresentation_surjective S T.primeNilpotentX) 0)
    (exists_pow_eq_zero_wsEnvelope T.primeNilpotentX T.prime_nilpotent 0)
    (levelEnvelopeAlgHom T.primeNilpotentX 0 e) (isDPMorphism_levelEnvelopeAlgHom _ 0 e)
  have h : (T.levelEnvelopeMap e he).toRingHom =
      T.completedEnvelopeEquiv.symm.toRingEquiv.toRingHom.comp
        ((T.levelSectionsMap e he).comp (T.levelRingHom e)) := rfl
  rw [h, hsymm]
  exact ((completionDPMorphism _ _ _ _).isDPMorphism.comp _
    T.isDPMorphism_envelopeEquiv_symm).comp _
    ((T.isDPMorphism_levelSectionsMap e he).comp _ hred)

/-- The polynomials of the presentation of the system, carried to `Γ(Y, 𝒪_Y)` through the
envelope, the reduction to `T(0)_e` and `ψ^♯`, as a morphism of `A`-algebras. -/
def levelPolynomialMap (e : ℕ) (he : T.levelBound ≤ e) :
    MvPolynomial (Fin 1 × wholeSpaceIndex S T.primeNilpotentX)
        (T.affineCrystallineSituation.A : Type u) →ₐ[(T.affineCrystallineSituation.A : Type u)]
      Γ(T.Y, ⊤) :=
  { (T.levelSectionsMap e he).comp ((envLevelMap T.primeNilpotentX 0 e).comp
      (tensorPowerEnvelope T.affineCrystallineSituation
        (wholeSpacePresentation S T.primeNilpotentX) 0).algebraMap.toRingHom) with
    commutes' := fun a ↦ by
      have h0 : (tensorPowerEnvelope T.affineCrystallineSituation
          (wholeSpacePresentation S T.primeNilpotentX) 0).algebraMap.toRingHom
            (algebraMap _ _ a) =
          algebraMap (T.affineCrystallineSituation.A : Type u) (wsEnvelope T.primeNilpotentX 0) a :=
        RingHom.congr_fun (tensorPowerEnvelope T.affineCrystallineSituation
          (wholeSpacePresentation S T.primeNilpotentX) 0).algebraMap_comp a
      have h1 : envLevelMap T.primeNilpotentX 0 e
          (algebraMap _ (wsEnvelope T.primeNilpotentX 0 : Type u) a) =
          crysBaseAppLE S (levelObj T.primeNilpotentX 0 e).obj a :=
        letI := crysTopAlgebra S (levelObj T.primeNilpotentX 0 e).obj
        (levelEnvelopeAlgHom T.primeNilpotentX 0 e).commutes a
      have h2 : T.levelSectionsMap e he (crysBaseAppLE S (levelObj T.primeNilpotentX 0 e).obj a) =
          crysBaseAppLE S T.crystallineThickening.obj a :=
        crysRingMap_crysBase S (T.levelHom e he).hom a
      have h3 : crysBaseAppLE S T.crystallineThickening.obj a =
          algebraMap (T.affineCrystallineSituation.A : Type u) Γ(T.Y, ⊤) a :=
        (congrArg (fun i : Algebra (T.affineCrystallineSituation.A : Type u) Γ(T.Y, ⊤) ↦
          @algebraMap _ _ _ _ i a) T.liftingAlgebra_eq_crysTopAlgebra).symm
      change T.levelSectionsMap e he (envLevelMap T.primeNilpotentX 0 e
        ((tensorPowerEnvelope T.affineCrystallineSituation
          (wholeSpacePresentation S T.primeNilpotentX) 0).algebraMap.toRingHom
            (algebraMap _ _ a))) = _
      rw [h0, h1, h2, h3] }

/-- **The envelope map is compatible with the augmentations to `C`.** -/
theorem completedEnvelopeAugmentation_comp_levelEnvelopeMap (e : ℕ) (he : T.levelBound ≤ e) :
    (completedEnvelopeAugmentation (affineSituation S T.primeNilpotentX) T.liftingPresentation
        T.surjective_liftingPresentation).comp (T.levelEnvelopeMap e he).toRingHom =
      completedEnvelopeAugmentation (affineSituation S T.primeNilpotentX)
        (tensorPowerPresentation (affineSituation S T.primeNilpotentX)
          (wholeSpacePresentation S T.primeNilpotentX) 0)
        (tensorPowerPresentation_surjective (affineSituation S T.primeNilpotentX) _
          (wholeSpacePresentation_surjective S T.primeNilpotentX) 0) := by
  have hr : T.liftingPresentation.comp (T.levelPolynomialMap e he) =
      tensorPowerPresentation T.affineCrystallineSituation
          (wholeSpacePresentation S T.primeNilpotentX) 0 :=
    AlgHom.ext fun q ↦ (T.liftingPresentation_apply _).trans
      (T.toY_appTop_crysRingMap_envLevelMap T.primeNilpotentX e (T.levelHom e he) q)
  have hφr : ∀ y, (T.levelEnvelopeMap e he).toRingHom (AdicCompletion.of _ _
      ((presentationEnvelope T.affineCrystallineSituation (tensorPowerPresentation
        T.affineCrystallineSituation
          (wholeSpacePresentation S T.primeNilpotentX) 0)).algebraMap.toRingHom
          y)) =
      AdicCompletion.of _ _ ((presentationEnvelope T.affineCrystallineSituation
        T.liftingPresentation).algebraMap.toRingHom (T.levelPolynomialMap e he y)) := fun y ↦
    (T.levelEnvelopeRingHom_of e he _).trans (T.completedEnvelopeEquiv_symm_apply _)
  exact completedEnvelopeAugmentation_comp_of_algebraMap T.affineCrystallineSituation _ _
    T.liftingPresentation T.surjective_liftingPresentation (T.levelPolynomialMap e he) hr
    (T.levelEnvelopeMap e he).toRingHom (T.isDPMorphism_levelEnvelopeMap e he) hφr
/-- **[Stacks, Lemma 60.21.4, Tag 07LH] along the envelope map of `ψ`**: for a crystal in
quasi-coherent modules, the base change `M ⊗^∧_D Ω^*_D → M' ⊗^∧_{D'} Ω^*_{D'}` of its pair along
`a : D → D'` is a quasi-isomorphism. -/
theorem quasiIso_baseChangeHom_levelEnvelopeMap (Fc : QuasiCoherentCrystal S) (e : ℕ)
    (he : T.levelBound ≤ e) :
    QuasiIso ((crystalPairConnModule T.primeNilpotentX Fc).baseChangeHom
      (FormsData.Hom.ofCompletion T.affineCrystallineSituation.p
        T.affineCrystallineSituation.A _
        (presTowerPrime_nilpotent T.affineCrystallineSituation
          (wholeSpacePresentation S T.primeNilpotentX)
          (wholeSpacePresentation_surjective S T.primeNilpotentX) 0) _
        (presentationEnvelope_prime_nilpotent T.affineCrystallineSituation T.liftingPresentation
          T.surjective_liftingPresentation)
        (T.levelEnvelopeMap e he) (T.isDPMorphism_levelEnvelopeMap e he))) :=
  quasiIso_baseChangeHom_smoothPresentationOfTower T.affineCrystallineSituation
    (wholeSpacePresentation S T.primeNilpotentX)
    (wholeSpacePresentation_surjective S T.primeNilpotentX)
    (crystalPairConnModule T.primeNilpotentX Fc)
    (quasiIso_crystalPair_baseChangeHom_coprojection T.primeNilpotentX Fc)
    (crystalStratification T.primeNilpotentX Fc)
    (crystalStratification_bijective T.primeNilpotentX Fc) T.liftingPresentation
    T.surjective_liftingPresentation
    (exists_tensorPowerSurjectionOfTower T.affineCrystallineSituation _
      (wholeSpacePresentation_surjective S T.primeNilpotentX) _ T.liftingPresentation
      T.surjective_liftingPresentation)
    (T.levelEnvelopeMap e he) (T.isDPMorphism_levelEnvelopeMap e he)
    (T.completedEnvelopeAugmentation_comp_levelEnvelopeMap e he)

end Crystalline.GlobalCrystallineSituation.SmallSite.Situation07MW

end
