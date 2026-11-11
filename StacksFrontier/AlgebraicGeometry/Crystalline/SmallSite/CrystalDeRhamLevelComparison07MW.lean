module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.BaseChangeConnectionReduction
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.RowCoprojectionTransport
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CechRowLevelProjection
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalDeRhamComputesCohomology
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineDeRhamSectionsComplex
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CompletedDeRhamNilpotentReduction
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalPairDegreeConnModule
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LevelEnvelopeIdentification07MW
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.WholeSpaceLevelStabilization07MW

/-!
# The Čech rows of the de Rham complex of a crystal are the completed de Rham complexes of its pair

Let `(p, (S, I, γ), X)` be a global crystalline situation with `X` and `S` affine and `p` nilpotent
on `S` (`hA`), `T(n)_e` the system `...SmallSite.wholeSpaceSystem` of
[Stacks, Proposition 60.20.1, Tag 07JN] (default presentation), `F` a crystal in quasi-coherent
`𝒪_{X/S}`-modules with de Rham complex `K^• = F ⊗ Ω^•_{X/S}` and cosimplicial pair
`(M(•), ∇_•)` (`...SmallSite.crystalCosimplicialPair`, `∇_b` the base change of the connection of
[Stacks, Tag 07JG] along the coprojection `⦋0⦌ ⟶ ⦋b⦌`).

Past the stable level `e = ...SmallSite.wholeSpaceStableLevel hA` the tower `T(b)_•` is constant,
`lim_e K^•(T(b)_e) = K^•(T(b)_e)` (`...SmallSite.isIso_cechRowLevelProjection`), and `D̂(b)`,
`M(b)`, `Ω̂^a_{D(b)}` reduce bijectively to `Γ(T(b)_e, 𝒪)`, `F(T(b)_e)`, `Ω^a_{X/S}(T(b)_e)`.
This module assembles these reductions into an isomorphism of complexes
`M(b) ⊗^∧_{D(b)} Ω^•_{D(b)} ≅ F(T(b)_e) ⊗ Ω^•_{X/S}(T(b)_e)` (`stableLevelReduce`), compatible with
the differentials because the reduction of `∇_b` is the canonical connection of `F` over
`T(b)_e`; that compatibility is derived from its degree-zero case by base change
(`stableLevelConnection_component`, from
`Crystalline.CosimplicialCompletedModule.reduceTensor_baseChangePair_nabla`), and the degree-zero
case is the hypothesis `StableLevelBridge` here (it is proved, as
`...SmallSite.stableLevelBridge`, in
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/CrystalDeRhamCechRows07MW.lean`).

## Main results

* `stableLevelReduce`, `isIso_stableLevelReduce` — the isomorphism of complexes at the stable
  level, for every cosimplicial degree `b`.
* `rowFromZeroHom_comp_stableLevelReduce` — it carries the coprojection of the pair to the
  restriction of sections along `T(b)_e ⟶ T(0)_e`.
* `crystalDeRhamCechRowIso` — `lim_e K^•(T(b)_e) ≅ M(b) ⊗^∧_{D(b)} Ω^•_{D(b)}` (universe-lifted),
  and `cosimplicialRowCoprojection_comp_crystalDeRhamCechRowIso` — compatibly with the
  coprojections.

Everything here takes the degree-zero bridge as a hypothesis; nothing else is assumed.

## References

* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Lemma 60.21.2, Tag 07LD](https://stacks.math.columbia.edu/tag/07LD)
* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Simplicial DividedPowers
open scoped TensorProduct

universe u

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open AffineConnection

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.X] [IsAffine S.S.scheme]
  (hA : IsNilpotent (S.p : Γ(S.S.scheme, ⊤))) (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
  {F : SheafOfModules.{u} (structureSheaf S)} (hF : F.IsQuasicoherentOnSite)

/-- The crystal in quasi-coherent modules of a quasi-coherent sheaf of modules on `Cris(X/S)`. -/
abbrev quasiCoherentCrystalOf : QuasiCoherentCrystal S :=
  ⟨F, hF, isSheafCrystal_of_isQuasicoherentOnSite F hF⟩

attribute [local instance] crysTopAlgebra wsEnvelopeTopAlgebra

/-- The stable level object `T(b)_e`, `e` the stable level, as an affine-over-affine object. -/
abbrev stableLevelObject (b : ℕ) : AffineOverAffineCrystallineThickening S :=
  levelAffineObject hp b (wholeSpaceStableLevel hA)

/-- `p^{N+e}` vanishes in the envelope `E(b)` at the stable level `e`. -/
theorem natCast_pow_stableLevel_wsEnvelope (b : ℕ) :
    ((S.p ^ (_root_.Crystalline.uniformLevel (affineSituation S hp) +
      wholeSpaceStableLevel hA) : ℕ) : wsEnvelope hp b) = 0 := by
  rw [Nat.cast_pow]
  exact natCast_pow_eq_zero_wsEnvelope hA hp b le_rfl

include hA in
/-- `p` is nilpotent in the completed envelope `D̂(b)`. -/
theorem exists_pow_eq_zero_degreeRing (b : ℕ) :
    ∃ k : ℕ, (S.p : (wholeSpaceDPAlgebra hp).completedRing S.p b) ^ k = 0 :=
  ⟨_, natCast_pow_eq_zero_wholeSpaceEnvelopeRing hA hp b le_rfl⟩

/-- The ring map `D̂(b) → Γ(T(b)_e, 𝒪)` at the stable level. -/
abbrev stableLevelRingHom (b : ℕ) :
    (wholeSpaceDPAlgebra hp).completedRing S.p b →+*
      GlobalCrystallineSituation.crysFormRing S (stableLevelObject hA hp b).obj.obj :=
  formsRingHom (E := (wsEnvelope hp b : Type u))
      (exists_pow_eq_zero_wsEnvelope hp hA b)
    (levelEnvelopeAlgHom hp b (wholeSpaceStableLevel hA))

/-- The ring map of the stable level is the reduction `levelSectionsScalars` through which
`D̂(b)` acts on the sections over `T(b)_e`. -/
theorem stableLevelRingHom_eq (b : ℕ) (x : (wholeSpaceDPAlgebra hp).completedRing S.p b) :
    stableLevelRingHom hA hp b x = levelSectionsScalars hp ⦋b⦌ (wholeSpaceStableLevel hA) x := by
  obtain ⟨y, rfl⟩ := (pAdicOfEquiv S.p (exists_pow_eq_zero_wsEnvelope hp hA b)
    (wsEnvelope hp b)).surjective x
  refine (formsRingHom_of _ _ y).trans ?_
  exact congrArg (levelSectionsScalars hp ⦋b⦌ (wholeSpaceStableLevel hA))
    (pAdicOfRingEquiv_apply S.p (exists_pow_eq_zero_wsEnvelope hp hA b) y)

/-- The component `M(b) → F(T(b)_e)` at the stable level, semilinear over `stableLevelRingHom`. -/
def stableLevelComponent (b : ℕ) :
    (wholeSpaceCosimplicialModule hp (quasiCoherentCrystalOf hF)).carrier b
      →ₛₗ[stableLevelRingHom hA hp b] F.val.obj (op (stableLevelObject hA hp b).obj) where
  toFun := wholeSpaceComponent hp (quasiCoherentCrystalOf hF) ⦋b⦌ (wholeSpaceStableLevel hA)
  map_add' := map_add _
  map_smul' r m := by
    rw [stableLevelRingHom_eq]
    exact map_smulₛₗ
      (wholeSpaceComponent hp (quasiCoherentCrystalOf hF) ⦋b⦌ (wholeSpaceStableLevel hA)) r m

/-- The component at the stable level is the level-`e` component of `M(b) = lim_e F(T(b)_e)`. -/
theorem stableLevelComponent_apply (b : ℕ)
    (m : (wholeSpaceCosimplicialModule hp (quasiCoherentCrystalOf hF)).carrier b) :
    stableLevelComponent hA hp hF b m =
      wholeSpaceSectionsVal hp (quasiCoherentCrystalOf hF) m (wholeSpaceStableLevel hA) := rfl

/-- The comparison of forms `Ω̂^a_{D(b)} → Ω^a_{X/S}(T(b)_e)` at the stable level. -/
abbrev stableLevelForms (b a : ℕ) :
    (wholeSpaceDPAlgebra hp).forms S.p a b →ₛₗ[stableLevelRingHom hA hp b]
      ⋀[GlobalCrystallineSituation.crysFormRing S (stableLevelObject hA hp b).obj.obj]^a
        ↥((GlobalCrystallineSituation.crysDifferentials S).obj
          (op (stableLevelObject hA hp b).obj.obj)) :=
  formsHom (E := (wsEnvelope hp b : Type u))
      (exists_pow_eq_zero_wsEnvelope hp hA b)
    (levelEnvelopeAlgHom hp b (wholeSpaceStableLevel hA))
    (isDPMorphism_levelEnvelopeAlgHom hp b (wholeSpaceStableLevel hA)) a

/-- The comparison of one-forms `Ω̂^1_{D(b)} → Ω_{X/S}(T(b)_e)` at the stable level. -/
abbrev stableLevelOneForms (b : ℕ) :
    (wholeSpaceDPAlgebra hp).forms S.p 1 b →ₛₗ[stableLevelRingHom hA hp b]
      ↥((GlobalCrystallineSituation.crysDifferentials S).obj
        (op (stableLevelObject hA hp b).obj.obj)) :=
  formsOneHom (E := (wsEnvelope hp b : Type u))
      (exists_pow_eq_zero_wsEnvelope hp hA b)
    (levelEnvelopeAlgHom hp b (wholeSpaceStableLevel hA))
    (isDPMorphism_levelEnvelopeAlgHom hp b (wholeSpaceStableLevel hA))

/-- The canonical connection of `F` over the stable level object `T(b)_e`. -/
abbrev stableLevelConnection (b : ℕ) :=
  (ringConnection (stableLevelObject hA hp b).top_le_preimage_baseOpen
    (stableLevelObject hA hp b).isAffineOpen_baseOpen
    (bijective_crysExtensionSectionsMap_affine hF (stableLevelObject hA hp b))).toAddMonoidHom

/-- The morphism `T(b)_e ⟶ T(0)_e` of the coprojection, in the affine-over-affine subsite. -/
def stableLevelCoprojection (b : ℕ) : stableLevelObject hA hp b ⟶ stableLevelObject hA hp 0 :=
  ObjectProperty.homMk
    (((wholeSpaceSystem S hp).map (SimplexCategory.const ⦋0⦌ ⦋b⦌ 0).op).app
      (wholeSpaceStableLevel hA))

/-- The morphism of rings with forms `D̂(m) → D̂(n)` along a map `φ : ⦋m⦌ ⟶ ⦋n⦌`. -/
def wholeSpaceDegreeFormsHom {m n : ℕ} (φ : (⦋m⦌ : SimplexCategory) ⟶ ⦋n⦌) :
    FormsData.Hom (FormsData.ofDividedPowers S.p (Γ(S.S.scheme, ⊤) : Type u)
        (wsEnvelope hp m).dividedPowers)
      (FormsData.ofDividedPowers S.p (Γ(S.S.scheme, ⊤) : Type u)
        (wsEnvelope hp n).dividedPowers) where
  toRingHom := (wholeSpaceDPAlgebra hp).completedRingMap S.p φ
  psi a := (wholeSpaceDPAlgebra hp).formsMapCompleted S.p φ a
  psi_diff x := (wholeSpaceDPAlgebra hp).formsMap_differential S.p φ x
  psi_wedge a ω η := (wholeSpaceDPAlgebra hp).formsMap_wedge S.p φ a ω η
  psi_deRham a ω := (wholeSpaceDPAlgebra hp).formsMap_deRham S.p φ a ω

omit [IsAffine S.X] [IsAffine S.S.scheme] in
/-- The comparison of forms of `wholeSpaceDegreeFormsHom` is the transition map of the forms of
the cosimplicial envelope. -/
theorem wholeSpaceDegreeFormsHom_psi {m n : ℕ} (φ : (⦋m⦌ : SimplexCategory) ⟶ ⦋n⦌) (a : ℕ)
    (ω : (wholeSpaceDPAlgebra hp).forms S.p a m) :
    (wholeSpaceDegreeFormsHom hp φ).psi a ω = (wholeSpaceDPAlgebra hp).formsMap S.p φ a ω := rfl

omit [IsAffine S.X] [IsAffine S.S.scheme] in
/-- `wholeSpaceDegreeFormsHom` carries the unit zero-form to the unit zero-form. -/
theorem wholeSpaceDegreeFormsHom_psi_zero {m n : ℕ} (φ : (⦋m⦌ : SimplexCategory) ⟶ ⦋n⦌) :
    (wholeSpaceDegreeFormsHom hp φ).psi 0
        (completedUnitZeroForm S.p (Γ(S.S.scheme, ⊤) : Type u)
          (wsEnvelope hp m).dividedPowers) =
      completedUnitZeroForm S.p (Γ(S.S.scheme, ⊤) : Type u) (wsEnvelope hp n).dividedPowers :=
  completedMapDifferentialForms_completedUnitZeroForm _ _ _ _ _ _

/-- The ring maps of the stable levels are compatible with the coprojections. -/
theorem stableLevelRingHom_coprojection (b : ℕ)
    (x : (wholeSpaceDPAlgebra hp).completedRing S.p 0) :
    stableLevelRingHom hA hp b ((wholeSpaceDegreeFormsHom hp
        (SimplexCategory.const ⦋0⦌ ⦋b⦌ 0)).toRingHom x) =
      crysRingMap S (stableLevelCoprojection hA hp b).hom.hom (stableLevelRingHom hA hp 0 x) := by
  refine (stableLevelRingHom_eq hA hp b _).trans
    (Eq.trans ?_ (congrArg _ (stableLevelRingHom_eq hA hp 0 x).symm))
  exact (levelSectionsScalars_restriction hp (SimplexCategory.const ⦋0⦌ ⦋b⦌ 0)
    (wholeSpaceStableLevel hA) x).symm

section Bridge

/-- The compatibility, in degree zero, of the canonical connection of `F` over `T(0)_e` with the
connection of the pair of the crystal, read through the reductions. -/
def StableLevelBridge : Prop :=
  ∀ m, stableLevelConnection hA hp hF 0 (stableLevelComponent hA hp hF 0 m) =
    reduceTensor (stableLevelRingHom hA hp 0) (exists_pow_eq_zero_degreeRing hA hp 0)
      (stableLevelComponent hA hp hF 0) (stableLevelOneForms hA hp 0)
      (crystalPairFormsConnection hp (quasiCoherentCrystalOf hF) m)

variable {hA hp hF}

/-- **The reduction of the connection `∇_b` of the cosimplicial pair is the canonical connection
of `F` over `T(b)_e`**, given the same in degree zero. -/
theorem stableLevelConnection_component (hbridge : StableLevelBridge hA hp hF) (b : ℕ)
    (y : (wholeSpaceCosimplicialModule hp (quasiCoherentCrystalOf hF)).carrier b) :
    stableLevelConnection hA hp hF b (stableLevelComponent hA hp hF b y) =
      reduceTensor (stableLevelRingHom hA hp b) (exists_pow_eq_zero_degreeRing hA hp b)
        (stableLevelComponent hA hp hF b) (stableLevelOneForms hA hp b)
        ((crystalPairDegreeConnModule hp (quasiCoherentCrystalOf hF) b).nabla y) := by
  let k := (stableLevelCoprojection hA hp b).hom
  exact (wholeSpaceCosimplicialModule hp
    (quasiCoherentCrystalOf hF)).reduceTensor_baseChangePair_nabla
    (crystalPairFormsConnection hp _) (crystalCoprojectionBeta hp _)
    (crystalCoprojectionBeta_of_tmul hp _) (crystalPairFormsConnection_horizontal_delta hp _)
    (hasIntegrableConnection_crystalPairFormsConnection hp _) b
    (stableLevelRingHom hA hp 0) (exists_pow_eq_zero_degreeRing hA hp 0)
    (stableLevelComponent hA hp hF 0) (stableLevelOneForms hA hp 0)
    (stableLevelConnection hA hp hF 0) hbridge
    (stableLevelRingHom hA hp b) (exists_pow_eq_zero_degreeRing hA hp b)
    (stableLevelComponent hA hp hF b) (stableLevelOneForms hA hp b)
    (stableLevelConnection hA hp hF b)
    (fun r ↦ GlobalCrystallineSituation.crysD S (stableLevelObject hA hp b).obj.obj r)
    (fun r n ↦ (ringConnection _ _ _).leibniz' r n)
    (fun x ↦ formsOneHom_diff (E := (wsEnvelope hp b : Type u))
      (exists_pow_eq_zero_wsEnvelope hp hA b)
      (levelEnvelopeAlgHom hp b (wholeSpaceStableLevel hA))
      (isDPMorphism_levelEnvelopeAlgHom hp b (wholeSpaceStableLevel hA)) x)
    (restrictTensor F k) ⟨⟨crysSiteRestrict F k, map_zero _⟩, fun x y ↦ map_add _ x y⟩
    ⟨⟨restrictOmega k, map_zero _⟩, fun x y ↦ map_add _ x y⟩
    (fun x ω ↦ restrictTensor_tmul F k x ω)
    (fun x ↦ rfl)
    (fun ω ↦ formsOneHom_naturality (exists_pow_eq_zero_wsEnvelope hp hA b)
        (levelEnvelopeAlgHom hp b (wholeSpaceStableLevel hA))
        (isDPMorphism_levelEnvelopeAlgHom hp b (wholeSpaceStableLevel hA))
        (exists_pow_eq_zero_wsEnvelope hp hA 0)
        (levelEnvelopeAlgHom hp 0 (wholeSpaceStableLevel hA))
        (isDPMorphism_levelEnvelopeAlgHom hp 0 (wholeSpaceStableLevel hA)) k.hom
        (wholeSpaceDegreeFormsHom hp _)
      (stableLevelRingHom_coprojection hA hp b) ω)
    (fun x ↦ ringConnection_naturality _ _ _ _ _ _ k x) y

variable (hbridge : StableLevelBridge hA hp hF)

/-- **The reduction `M(b) ⊗^∧_{D(b)} Ω^*_{D(b)} ⟶ F(T(b)_e) ⊗ Ω^*_{X/S}(T(b)_e)`** at the stable
level, a morphism of complexes. -/
def stableLevelReduce (b : ℕ) :
    (crystalPairDegreeConnModule hp (quasiCoherentCrystalOf hF) b).complex ⟶
      affineDeRhamSectionsComplex hF (stableLevelObject hA hp b) :=
  (crystalPairDegreeConnModule hp (quasiCoherentCrystalOf hF) b).reduceComplexHom
    (stableLevelRingHom hA hp b) (exists_pow_eq_zero_degreeRing hA hp b)
    (stableLevelOneForms hA hp b) (stableLevelForms hA hp b)
    (fun a ω η ↦ formsHom_wedge (E := (wsEnvelope hp b : Type u))
      (exists_pow_eq_zero_wsEnvelope hp hA b)
      (levelEnvelopeAlgHom hp b (wholeSpaceStableLevel hA))
      (isDPMorphism_levelEnvelopeAlgHom hp b (wholeSpaceStableLevel hA)) a ω η)
    (fun a ↦ (crysDeRhamComplex S).differential a (stableLevelObject hA hp b).obj.obj)
    (fun a ω ↦ formsHom_deRham (E := (wsEnvelope hp b : Type u))
      (exists_pow_eq_zero_wsEnvelope hp hA b)
      (levelEnvelopeAlgHom hp b (wholeSpaceStableLevel hA))
      (isDPMorphism_levelEnvelopeAlgHom hp b (wholeSpaceStableLevel hA)) a ω)
    (stableLevelComponent hA hp hF b) (stableLevelConnection hA hp hF b)
    (stableLevelConnection_component hbridge b)
    (fun a ↦ extDiff (stableLevelObject hA hp b).top_le_preimage_baseOpen
      (stableLevelObject hA hp b).isAffineOpen_baseOpen
      (bijective_crysExtensionSectionsMap_affine hF _) a)
    (fun a n ω ↦ extDiff_tmul _ _ _ a n ω)
    (fun a ↦ AddMonoidHom.ext fun x ↦ extDiff_comp_extDiff _ _ _
      (injective_crysSecondExtensionSectionsMap_affine hF _) a x)

omit hbridge in
variable (hA hp hF) in
/-- The ring map of the stable level is bijective. -/
theorem bijective_stableLevelRingHom (b : ℕ) : Function.Bijective (stableLevelRingHom hA hp b) :=
  formsRingHom_bijective (E := (wsEnvelope hp b : Type u))
      (exists_pow_eq_zero_wsEnvelope hp hA b)
    (levelEnvelopeAlgHom hp b (wholeSpaceStableLevel hA)) (bijective_envLevelMap hA hp b le_rfl)

omit hbridge in
variable (hA hp hF) in
/-- The component of `M(b)` at the stable level is bijective. -/
theorem bijective_stableLevelComponent (b : ℕ) :
    Function.Bijective (stableLevelComponent hA hp hF b) :=
  bijective_wholeSpaceComponent hA hp (quasiCoherentCrystalOf hF) ⦋b⦌ le_rfl

omit hbridge in
variable (hA hp hF) in
/-- The comparison of forms at the stable level is bijective. -/
theorem bijective_stableLevelForms (b a : ℕ) : Function.Bijective (stableLevelForms hA hp b a) :=
  formsHom_bijective (E := (wsEnvelope hp b : Type u))
      (exists_pow_eq_zero_wsEnvelope hp hA b)
    (levelEnvelopeAlgHom hp b (wholeSpaceStableLevel hA))
    (isDPMorphism_levelEnvelopeAlgHom hp b (wholeSpaceStableLevel hA))
    (levelEnvelopeAlgHomInv (natCast_pow_stableLevel_wsEnvelope hA hp b))
    (isDPMorphism_levelEnvelopeAlgHomInv (natCast_pow_stableLevel_wsEnvelope hA hp b))
    (levelEnvelopeAlgHomInv_comp (natCast_pow_stableLevel_wsEnvelope hA hp b))
    (comp_levelEnvelopeAlgHomInv (natCast_pow_stableLevel_wsEnvelope hA hp b)) a

/-- **The reduction at the stable level is an isomorphism of complexes.** -/
instance isIso_stableLevelReduce (b : ℕ) : IsIso (stableLevelReduce hbridge b) :=
  (crystalPairDegreeConnModule hp (quasiCoherentCrystalOf hF) b).isIso_reduceComplexHom
    _ _ _ _ _ _ _ _ _ _ _ _ _ (bijective_stableLevelRingHom hA hp b)
    (bijective_stableLevelComponent hA hp hF b) (bijective_stableLevelForms hA hp b)

omit hbridge in
variable (hA hp hF) in
/-- **The reductions are natural along the coprojection**, on elements: the reduction of the
coprojection of `z` is the restriction of the reduction of `z` along `T(b)_e ⟶ T(0)_e`. -/
theorem reduceTensor_stableLevel_tensorMap (b a : ℕ)
    (z : (wholeSpaceCosimplicialModule hp (quasiCoherentCrystalOf hF)).obj a 0) :
    reduceTensor (stableLevelRingHom hA hp b) (exists_pow_eq_zero_degreeRing hA hp b)
        (stableLevelComponent hA hp hF b) (stableLevelForms hA hp b a)
        ((wholeSpaceCosimplicialModule hp (quasiCoherentCrystalOf hF)).tensorMap
          (SimplexCategory.const ⦋0⦌ ⦋b⦌ 0) a z) =
      restrictForms F (stableLevelCoprojection hA hp b).hom a
        (reduceTensor (stableLevelRingHom hA hp 0) (exists_pow_eq_zero_degreeRing hA hp 0)
          (stableLevelComponent hA hp hF 0) (stableLevelForms hA hp 0 a) z) :=
  (wholeSpaceCosimplicialModule hp (quasiCoherentCrystalOf hF)).reduceTensor_tensorMap
    (SimplexCategory.const ⦋0⦌ ⦋b⦌ 0) a
    (stableLevelRingHom hA hp 0) (stableLevelRingHom hA hp b)
    (exists_pow_eq_zero_degreeRing hA hp 0) (exists_pow_eq_zero_degreeRing hA hp b)
    (stableLevelComponent hA hp hF 0) (stableLevelComponent hA hp hF b)
    (stableLevelForms hA hp 0 a) (stableLevelForms hA hp b a)
    (restrictForms F (stableLevelCoprojection hA hp b).hom a)
    ⟨⟨crysSiteRestrict F (stableLevelCoprojection hA hp b).hom, map_zero _⟩,
      fun x y ↦ map_add _ x y⟩
    ⟨⟨GlobalCrystallineSituation.crysFormMap S (stableLevelCoprojection hA hp b).hom.hom,
      map_zero _⟩, fun x y ↦ map_add _ x y⟩
    (fun x ω ↦ restrictForms_tmul F _ a x ω) (fun _ ↦ rfl)
    (fun ω ↦ formsHom_naturality (exists_pow_eq_zero_wsEnvelope hp hA b)
      (levelEnvelopeAlgHom hp b (wholeSpaceStableLevel hA))
      (isDPMorphism_levelEnvelopeAlgHom hp b (wholeSpaceStableLevel hA))
      (exists_pow_eq_zero_wsEnvelope hp hA 0)
      (levelEnvelopeAlgHom hp 0 (wholeSpaceStableLevel hA))
      (isDPMorphism_levelEnvelopeAlgHom hp 0 (wholeSpaceStableLevel hA))
      (stableLevelCoprojection hA hp b).hom.hom (wholeSpaceDegreeFormsHom hp _)
      (stableLevelRingHom_coprojection hA hp b) (wholeSpaceDegreeFormsHom_psi_zero hp _) a ω) z

/-- **The reductions carry the coprojections of the pair to the restrictions of sections.** -/
theorem rowFromZeroHom_comp_stableLevelReduce (b : ℕ) :
    (crystalCosimplicialPair hp (quasiCoherentCrystalOf hF)).rowFromZeroHom b ≫
        stableLevelReduce hbridge b =
      stableLevelReduce hbridge 0 ≫
        affineDeRhamSectionsMap hF (stableLevelCoprojection hA hp b) :=
  HomologicalComplex.hom_ext _ _ fun a ↦ AddCommGrpCat.ext fun x ↦
    reduceTensor_stableLevel_tensorMap hA hp hF b a x

/-- The projection of a Čech row of the de Rham complex onto the stable level is an isomorphism,
the tower `T(b)_•` being constant past that level. -/
instance isIso_cechRowLevelProjection_stable (b : ℕ) :
    IsIso (cechRowLevelProjection (wholeSpaceSystem S hp) (crystalDeRhamSheafData hF).natComplex b
      (wholeSpaceStableLevel hA)) :=
  isIso_cechRowLevelProjection _ _ b _ fun _ ↦
    isIso_limit_π_wholeSpaceSystem hA hp _ b _ le_rfl

/-- **The row `b` of the Čech complex of the de Rham complex of `F`,
`lim_e (F ⊗ Ω^•_{X/S})(T(b)_e)`, is the completed de Rham complex `M(b) ⊗^∧_{D(b)} Ω^•_{D(b)}`
of the cosimplicial pair of the crystal**, lifted to the universe of the sheaves. -/
def crystalDeRhamCechRowIso (b : ℕ) :
    cosimplicialRowComplex ((cechCosimplicialComplex (wholeSpaceSystem S hp)).obj
        (crystalDeRhamSheafData hF).natComplex) b ≅
      (AddCommGrpCat.uliftFunctor.{u + 1, u}.mapHomologicalComplex _).obj
        ((crystalCosimplicialPair hp (quasiCoherentCrystalOf hF)).degreeDeRhamComplex b) :=
  asIso (cechRowLevelProjection (wholeSpaceSystem S hp) (crystalDeRhamSheafData hF).natComplex b
      (wholeSpaceStableLevel hA)) ≪≫
    affineDeRhamSectionsIso hF (stableLevelObject hA hp b) ≪≫
    ((AddCommGrpCat.uliftFunctor.{u + 1, u}.mapHomologicalComplex _).mapIso
      (asIso (stableLevelReduce hbridge b))).symm

/-- **The identifications of the rows carry the coprojections of the Čech complex to the
coprojections `M(0) ⊗^∧ Ω^* ⟶ M(b) ⊗^∧ Ω^*` of the pair.** -/
theorem cosimplicialRowCoprojection_comp_crystalDeRhamCechRowIso (b : ℕ) :
    cosimplicialRowCoprojection _ b ≫ (crystalDeRhamCechRowIso hbridge b).hom =
      (crystalDeRhamCechRowIso hbridge 0).hom ≫
        (AddCommGrpCat.uliftFunctor.{u + 1, u}.mapHomologicalComplex _).map
          ((crystalCosimplicialPair hp (quasiCoherentCrystalOf hF)).rowFromZeroHom b) := by
  let U := AddCommGrpCat.uliftFunctor.{u + 1, u}.mapHomologicalComplex (ComplexShape.up ℕ)
  let e := wholeSpaceStableLevel hA
  let K := (crystalDeRhamSheafData hF).natComplex
  let rfz : (crystalPairDegreeConnModule hp (quasiCoherentCrystalOf hF) 0).complex ⟶
      (crystalPairDegreeConnModule hp (quasiCoherentCrystalOf hF) b).complex :=
    (crystalCosimplicialPair hp (quasiCoherentCrystalOf hF)).rowFromZeroHom b
  let aff := affineDeRhamSectionsMap hF (stableLevelCoprojection hA hp b)
  have h1 := cosimplicialRowCoprojection_comp_cechRowLevelProjection (wholeSpaceSystem S hp) K b e
  have h2 := affineDeRhamSectionsIso_naturality hF (stableLevelCoprojection hA hp b)
  have h3 : rfz ≫ stableLevelReduce hbridge b = stableLevelReduce hbridge 0 ≫ aff :=
    rowFromZeroHom_comp_stableLevelReduce hbridge b
  have h4 : aff ≫ inv (stableLevelReduce hbridge b) = inv (stableLevelReduce hbridge 0) ≫ rfz :=
    (IsIso.eq_inv_comp _).2 ((Category.assoc _ _ _).symm.trans ((IsIso.comp_inv_eq _).2 h3.symm))
  have h5 : U.map aff ≫ U.map (inv (stableLevelReduce hbridge b)) =
      U.map (inv (stableLevelReduce hbridge 0)) ≫ U.map rfz :=
    (U.map_comp _ _).symm.trans ((congrArg U.map h4).trans (U.map_comp _ _))
  change cosimplicialRowCoprojection _ b ≫ (cechRowLevelProjection (wholeSpaceSystem S hp) K b e ≫
      (affineDeRhamSectionsIso hF (stableLevelObject hA hp b)).hom ≫
        U.map (inv (stableLevelReduce hbridge b))) =
    (cechRowLevelProjection (wholeSpaceSystem S hp) K 0 e ≫
      (affineDeRhamSectionsIso hF (stableLevelObject hA hp 0)).hom ≫
        U.map (inv (stableLevelReduce hbridge 0))) ≫ U.map rfz
  refine ((Category.assoc _ _ _).symm.trans ((Category.assoc _ _ _).symm.trans
    (congrArg (fun t ↦ t ≫ _) ((congrArg (· ≫ _) h1).trans (Category.assoc _ _ _))))).trans ?_
  refine (congrArg (fun t ↦ t ≫ U.map (inv (stableLevelReduce hbridge b)))
    (congrArg (_ ≫ ·) h2)).trans ?_
  refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·) h5))).trans ?_)
  exact (congrArg (_ ≫ ·) (Category.assoc _ _ _).symm).trans (Category.assoc _ _ _).symm

end Bridge

end Crystalline.GlobalCrystallineSituation.SmallSite

end
