module

public import StacksFrontier.AlgebraicGeometry.Crystalline.AffineObjectDifferentialFormsNaturality
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.SectionsDividedPowerRing
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.ConnectionTransport
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.DeRhamPairPolynomial
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.DeRhamPairTransport
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineBaseChangeCriterion
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ChangeBaseQuasicoherentCrystal
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrysAffineConnectionNaturality
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrysFirstOrderAffineBaseChange
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrysSecondOrderAffineBaseChange

/-!
# The de Rham complexes of a crystal on the affine objects of `Cris(X/S)`

Fix a global crystalline situation `(p, (S, I, γ), X)` with `S` affine, and a crystal `ℱ` in
quasi-coherent `𝒪_{X/S}`-modules on the small crystalline site `Cris(X/S)`.  Over an object
`T = (U, T, δ)` of `Cris(X/S)` with affine ambient scheme, the canonical connection of
[Stacks, Lemma 60.15.1, Tag 07J6] (`...SmallSite.AffineConnection.ringConnection`, at the base
open `V = S`) takes values in `ℱ(T) ⊗ Ω_{X/S}(T)`, and [Stacks, Tag 07J0]
(`affineCrysDifferentialsIso`) identifies `Ω_{X/S}(T)` with the divided power differentials
`Ω¹_{Γ(T, 𝒪_T)/Γ(S, 𝒪_S), δ}`.  Transporting the connection along that identification
(`Crystalline.Connection.transport`) puts it in the spelling of `Crystalline.DeRhamPair`, over the
divided power ring `sectionsDPRing S T`, where the de Rham complexes of modules with integrable
connection, their functoriality and the transported Tag 07LD live.

## Main definitions

* `crystalPairConnection` — the canonical connection on `ℱ(T)`, relative to
  `Ω¹_{Γ(T, 𝒪_T)/Γ(S, 𝒪_S), δ}`.
* `crystalPairRestrict` — the restriction maps of `ℱ`, semilinear over `sectionsDPRingMap`.
* `crystalDeRhamPresheaf` — the presheaf `T ↦ ℱ(T) ⊗ Ω^*_{Γ(T, 𝒪_T)/Γ(S, 𝒪_S), δ}` of de Rham
  complexes on the affine objects of `Cris(X/S)`.
* `crystalSectionsPresheaf`, `crystalDeRhamPresheafDegreeZeroIso` — its degree-zero part is
  `T ↦ ℱ(T)`.
* `bigCrystalDeRhamPresheaf` — the same for a quasi-coherent module on `CRIS(X/S)`.

## Main results

* `crystalPairConnection_apply` — the value, through `ringConnection`.
* `crystalPairConnection_isIntegrable` — integrability.
* `crystalPairConnection_isHorizontal` — the restriction maps are horizontal.
* `bijective_polyModuleMap_crystalRestrict` — the crystal property along a divided power
  polynomial presentation.
* `quasiIso_crystalDeRhamPresheaf_map` — **the row comparison**: along a morphism presenting
  `Γ(T, 𝒪_T)` as a divided power polynomial algebra over `Γ(T', 𝒪_{T'})`, the restriction map
  of de Rham complexes is a quasi-isomorphism ([Stacks, Tag 07LD], transported).
* `isQuasicoherentOnSite_restrictSheafOfModules` — the restriction of a quasi-coherent module on
  `CRIS(X/S)` to `Cris(X/S)` is quasi-coherent.

## References

* [Stacks Project, Tag 07J0](https://stacks.math.columbia.edu/tag/07J0)
* [Stacks Project, Lemma 60.15.1, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Lemma 60.19.2, Tag 07LD](https://stacks.math.columbia.edu/tag/07LD)
* [Stacks Project, Tag 07N5](https://stacks.math.columbia.edu/tag/07N5)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct
open Stacks.DeRham.DifferentialDescent

universe u

namespace Crystalline.GlobalCrystallineSituation

open SmallSite SmallSite.AffineConnection

variable {S : GlobalCrystallineSituation.{u}}

/-! ### The one-forms of an affine object, in the divided power spelling -/

/-- The sections of `Ω_{X/S}` over an object, as a module over the divided power ring of sections
of its ambient scheme. -/
instance moduleSectionsDPRingCrysDifferentials (T : Thickening S) :
    Module (sectionsDPRing S T) ↥((crysDifferentials S).obj (op T)) :=
  inferInstanceAs (Module Γ(T.thickening.target.scheme, ⊤) ↥(crysDifferentialsObj S T))

/-- **[Stacks, Tag 07J0] at the base open `V = S`**: over an object of `CRIS(X/S)` with affine
ambient scheme, the sections of `Ω_{X/S}` are the divided power differentials
`Ω¹_{Γ(T, 𝒪_T)/Γ(S, 𝒪_S), δ}`, as a linear equivalence over `Γ(T, 𝒪_T)`. -/
def crystalOneFormsEquiv [IsAffine S.S.scheme] (T : Thickening S)
    [IsAffine T.thickening.target.scheme] :
    ↥((crysDifferentials S).obj (op T)) ≃ₗ[sectionsDPRing S T]
      dividedPowerDifferentials (A := Γ(S.S.scheme, ⊤)) (sectionsDPRing S T).dividedPowers :=
  (affineCrysDifferentialsIso S T (le_preimage_top T.toBase.hom ⊤)
    (isAffineOpen_top S.S.scheme)).toLinearEquiv

/-- The identification carries `d b` to `d b`. -/
theorem crystalOneFormsEquiv_crysD [IsAffine S.S.scheme] (T : Thickening S)
    [IsAffine T.thickening.target.scheme] (b : sectionsDPRing S T) :
    crystalOneFormsEquiv T (crysD S T b) =
      oneVariableBaseProjection Γ(S.S.scheme, ⊤) (sectionsDPRing S T)
        (KaehlerDifferential.D Γ(S.S.scheme, ⊤) (sectionsDPRing S T) b) :=
  affineCrysDifferentialsIso_hom_d S T (le_preimage_top T.toBase.hom ⊤)
    (isAffineOpen_top S.S.scheme) b

/-- **The identification turns the presentation `crysPi` of `Ω_{X/S}` into the presentation of the
divided power differentials**: `e ∘ crysPi = π`. -/
theorem crystalOneFormsEquiv_crysPi [IsAffine S.S.scheme] (T : Thickening S)
    [IsAffine T.thickening.target.scheme] (x : Ω[sectionsDPRing S T⁄Γ(S.S.scheme, ⊤)]) :
    crystalOneFormsEquiv T (crysPi S T x) =
      oneVariableBaseProjection Γ(S.S.scheme, ⊤) (sectionsDPRing S T) x := by
  have hx : x ∈ Submodule.span (sectionsDPRing S T)
      (Set.range (KaehlerDifferential.D Γ(S.S.scheme, ⊤) (sectionsDPRing S T))) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, rfl⟩ := hy
    exact crystalOneFormsEquiv_crysD T b
  | zero =>
    have h0 := congrArg (crystalOneFormsEquiv T) (crysPi S T).map_zero
    exact h0.trans ((map_zero _).trans (map_zero _).symm)
  | add y z _ _ hy hz =>
    have h0 := congrArg (crystalOneFormsEquiv T) ((crysPi S T).map_add y z)
    refine h0.trans (((crystalOneFormsEquiv T).map_add _ _).trans ?_)
    rw [hy, hz, map_add]
  | smul c y _ hy =>
    rw [map_smul, ← hy]
    exact (crystalOneFormsEquiv T).map_smul c (crysPi S T y)

variable {F : SheafOfModules.{u} (SmallSite.structureSheaf S)}

/-- The sections of a sheaf of `𝒪_{X/S}`-modules on `Cris(X/S)` over an object, as a module over
the divided power ring of sections of its ambient scheme. -/
instance moduleSectionsDPRingSmallSections (T : CrystallineThickening S) :
    Module (sectionsDPRing S T.obj) (F.val.obj (op T)) :=
  inferInstanceAs (Module (GlobalCrystallineSituation.crysFormRing S T.obj) (F.val.obj (op T)))

variable [IsAffine S.S.scheme]

variable (hF : F.IsQuasicoherentOnSite)

/-! ### The canonical connection in the divided power spelling -/

/-- The value on an affine object of `Cris(X/S)` of the canonical connection of [Stacks, Tag 07J6]
of a crystal in quasi-coherent modules, relative to the presentation `crysPi` of `Ω_{X/S}`, with
the base open `V = S`. -/
abbrev crysPairConnection (T : AffineCris S) :
    Connection Γ(S.S.scheme, ⊤) (GlobalCrystallineSituation.crysFormRing S T.obj.obj)
      (crysPi S T.obj.obj) (F.val.obj (op T.obj)) :=
  ringConnection (le_preimage_top T.obj.obj.toBase.hom ⊤) (isAffineOpen_top S.S.scheme)
    (bijective_crysExtensionSectionsMap_of_isQuasicoherentOnSite F T.obj hF)

/-- **The canonical connection of a crystal in quasi-coherent modules on an affine object of
`Cris(X/S)`, in the spelling of `Crystalline.DeRhamPair`** ([Stacks, Tag 07J6]): the connection
`∇ : ℱ(T) → ℱ(T) ⊗ Ω¹_{Γ(T, 𝒪_T)/Γ(S, 𝒪_S), δ}`, `∇ s = p₁^* s - p₀^* s`, read through the
identification [Stacks, Tag 07J0] of the sections of `Ω_{X/S}` with the divided power
differentials. -/
def crystalPairConnection (T : AffineCris S) :
    Connection Γ(S.S.scheme, ⊤) (sectionsDPRing S T.obj.obj)
      (oneVariableBaseProjection Γ(S.S.scheme, ⊤) (sectionsDPRing S T.obj.obj))
      (F.val.obj (op T.obj)) :=
  Connection.transport (crysPairConnection hF T) (crystalOneFormsEquiv T.obj.obj)
    (crystalOneFormsEquiv_crysPi T.obj.obj)

/-- The value of `crystalPairConnection`: the canonical connection `ringConnection` with its
one-forms carried along [Stacks, Tag 07J0]. -/
theorem crystalPairConnection_apply (T : AffineCris S) (s : F.val.obj (op T.obj)) :
    crystalPairConnection hF T s =
      TensorProduct.map LinearMap.id (crystalOneFormsEquiv T.obj.obj).toLinearMap
        (crysPairConnection hF T s) := rfl

/-- **The canonical connection of a crystal in quasi-coherent modules on an affine object of
`Cris(X/S)` is integrable** ([Stacks, Tag 07J6]), in the form the de Rham complex
`Crystalline.oneVariableSourceDeRhamComplex` consumes. -/
theorem crystalPairConnection_isIntegrable (T : AffineCris S) :
    Connection.IsIntegrable (oneVariableBaseSource Γ(S.S.scheme, ⊤) (sectionsDPRing S T.obj.obj))
      (oneVariableBaseProjection Γ(S.S.scheme, ⊤) (sectionsDPRing S T.obj.obj))
      (Submodule.mkQ_surjective _)
      (oneVariableBaseGenerationHypothesis Γ(S.S.scheme, ⊤) (sectionsDPRing S T.obj.obj))
      (crystalPairConnection hF T) :=
  Connection.IsIntegrable.transport (B := sectionsDPRing S T.obj.obj)
    (Omega := ↥((crysDifferentials S).obj (op T.obj.obj))) _ (surjective_crysPi S T.obj.obj)
    (generationHypothesis_crysPi S T.obj.obj) _ _ _ _ _
    (ringConnection_isIntegrable (le_preimage_top T.obj.obj.toBase.hom ⊤)
      (isAffineOpen_top S.S.scheme)
      (bijective_crysExtensionSectionsMap_of_isQuasicoherentOnSite F T.obj hF)
      (bijective_crysSecondExtensionSectionsMap_of_isQuasicoherentOnSite F T.obj hF).1)

/-! ### Horizontality of the restriction maps -/

section Horizontal

variable {T T' : AffineCris S} (k : T ⟶ T')

/-- **The restriction of sections of `ℱ` along a morphism of `AffineCris S`**, semilinear over the
divided power morphism `sectionsDPRingMap` of the rings of sections. -/
def crystalPairRestrict :
    F.val.obj (op T'.obj) →ₛₗ[(sectionsDPRingMap k.hom.hom).toRingHom] F.val.obj (op T.obj) where
  toFun := crysSiteRestrict F k.hom
  map_add' := crysSiteRestrict_add F k.hom
  map_smul' c s := crysSiteRestrict_smul F k.hom c s

omit [IsAffine S.S.scheme] in
/-- `crystalPairRestrict` is the restriction map of `ℱ`. -/
theorem crystalPairRestrict_apply (s : F.val.obj (op T'.obj)) :
    crystalPairRestrict (F := F) k s = F.val.map k.hom.op s := rfl

/-- **The identification of [Stacks, Tag 07J0] is natural**: it carries the transition map of
`Ω_{X/S}` to the map of divided power differentials induced by `sectionsDPRingMap`. -/
theorem crystalOneFormsEquiv_restrictOmega
    (η : ↥((crysDifferentials S).obj (op T'.obj.obj))) :
    crystalOneFormsEquiv T.obj.obj (restrictOmega k.hom η) =
      DeRhamPair.oneFormsMap (sectionsDPRingMap k.hom.hom)
        (isDPMorphism_sectionsDPRingMap k.hom.hom) (crystalOneFormsEquiv T'.obj.obj η) := by
  have hη : η ∈ Submodule.span (GlobalCrystallineSituation.crysFormRing S T'.obj.obj)
      (Set.range (crysD S T'.obj.obj)) := by
    rw [crysD_span]; trivial
  induction hη using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, rfl⟩ := hy
    refine (congrArg _ (restrictOmega_crysD k.hom b)).trans
      ((crystalOneFormsEquiv_crysD T.obj.obj (crysRingMap S k.hom.hom b)).trans
        (Eq.trans ?_ (congrArg _ (crystalOneFormsEquiv_crysD T'.obj.obj b)).symm))
    exact (mapDifferentialsOfDPMorphism_d (A := Γ(S.S.scheme, ⊤))
      (delta := (sectionsDPRing S T'.obj.obj).dividedPowers)
      (epsilon := (sectionsDPRing S T.obj.obj).dividedPowers) (f := sectionsDPRingMap k.hom.hom)
      (hf := isDPMorphism_sectionsDPRingMap k.hom.hom) (b := b)).symm
  | zero =>
    simp only [restrictOmega, map_zero]
    exact map_zero _
  | add y z _ _ hy hz =>
    rw [restrictOmega_add, map_add, hy, hz, map_add, map_add]
  | smul c y _ hy =>
    rw [restrictOmega_smul]
    refine ((crystalOneFormsEquiv T.obj.obj).map_smul _ _).trans ?_
    rw [hy]
    exact ((DeRhamPair.oneFormsMap (sectionsDPRingMap k.hom.hom)
      (isDPMorphism_sectionsDPRingMap k.hom.hom)).map_smulₛₗ c _).symm.trans
      (congrArg _ ((crystalOneFormsEquiv T'.obj.obj).map_smul c y).symm)

/-- **The restriction maps of `ℱ` are horizontal** for the canonical connections
([Stacks, Tag 07J6]: the connection is functorial in the object). -/
theorem crystalPairConnection_isHorizontal :
    DeRhamPair.IsHorizontal (sectionsDPRingMap k.hom.hom)
      (isDPMorphism_sectionsDPRingMap k.hom.hom) (crystalPairRestrict k)
      (crystalPairConnection hF T') (crystalPairConnection hF T) :=
  DeRhamPair.isHorizontal_transport _ _ (crystalPairRestrict k) (crystalOneFormsEquiv T'.obj.obj)
    (crystalOneFormsEquiv_crysPi T'.obj.obj) (crystalOneFormsEquiv T.obj.obj)
    (crystalOneFormsEquiv_crysPi T.obj.obj) (restrictOmega k.hom)
    (crystalOneFormsEquiv_restrictOmega k) (restrictTensor F k.hom)
    (fun m η ↦ restrictTensor_tmul F k.hom m η) (crysPairConnection hF T')
    (crysPairConnection hF T) (fun m ↦ ringConnection_naturality _ _ _ _ _ _ k.hom m)

end Horizontal

/-! ### The presheaf of de Rham complexes -/

/-- **The presheaf of de Rham complexes of a crystal in quasi-coherent modules on the affine
objects of `Cris(X/S)`**: `T ↦ ℱ(T) ⊗ Ω^*_{Γ(T, 𝒪_T)/Γ(S, 𝒪_S), δ}`, the de Rham complex of the
canonical connection of [Stacks, Tag 07J6], with the maps of de Rham complexes induced by the
restriction maps, which are horizontal. -/
def crystalDeRhamPresheaf :
    (AffineCris S)ᵒᵖ ⥤ CochainComplex (ModuleCat.{u} Γ(S.S.scheme, ⊤)) ℕ where
  obj T := oneVariableSourceDeRhamComplex Γ(S.S.scheme, ⊤) (sectionsDPRing S T.unop.obj.obj)
    (crystalPairConnection hF T.unop) (crystalPairConnection_isIntegrable hF T.unop)
  map {T T'} k := DeRhamPair.deRhamMap (sectionsDPRingMap k.unop.hom.hom)
    (isDPMorphism_sectionsDPRingMap k.unop.hom.hom) (crystalPairRestrict k.unop)
    (crystalPairConnection hF T.unop) (crystalPairConnection_isIntegrable hF T.unop)
    (crystalPairConnection hF T'.unop) (crystalPairConnection_isIntegrable hF T'.unop)
    (crystalPairConnection_isHorizontal hF k.unop)
  map_id T := by
    refine HomologicalComplex.hom_ext _ _ fun p ↦ ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
    rw [HomologicalComplex.id_f, ModuleCat.hom_id, LinearMap.id_apply]
    exact DeRhamPair.termMap_eq_self _ _ (fun _ ↦ rfl) _
      (fun m ↦ crysSiteRestrict_id F T.unop.obj m) p x
  map_comp {T T' T''} k k' := by
    refine HomologicalComplex.hom_ext _ _ fun p ↦ ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
    rw [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
    exact DeRhamPair.termMap_comp_of_eq _ _ (crystalPairRestrict k.unop) _ _ _ _
      (fun b ↦ DFunLike.congr_fun (sectionsDPRingMap_comp k'.unop.hom.hom k.unop.hom.hom) b)
      (crystalPairRestrict k'.unop) (crystalPairRestrict (k ≫ k').unop)
      (fun m ↦ (crysSiteRestrict_comp F k'.unop.hom k.unop.hom m).symm) p x

/-- The value of `crystalDeRhamPresheaf` on an object. -/
theorem crystalDeRhamPresheaf_obj (T : (AffineCris S)ᵒᵖ) :
    (crystalDeRhamPresheaf hF).obj T =
      oneVariableSourceDeRhamComplex Γ(S.S.scheme, ⊤) (sectionsDPRing S T.unop.obj.obj)
        (crystalPairConnection hF T.unop) (crystalPairConnection_isIntegrable hF T.unop) := rfl

/-- The value of `crystalDeRhamPresheaf` on a morphism. -/
theorem crystalDeRhamPresheaf_map {T T' : (AffineCris S)ᵒᵖ} (k : T ⟶ T') :
    (crystalDeRhamPresheaf hF).map k =
      DeRhamPair.deRhamMap (sectionsDPRingMap k.unop.hom.hom)
        (isDPMorphism_sectionsDPRingMap k.unop.hom.hom) (crystalPairRestrict k.unop)
        (crystalPairConnection hF T.unop) (crystalPairConnection_isIntegrable hF T.unop)
        (crystalPairConnection hF T'.unop) (crystalPairConnection_isIntegrable hF T'.unop)
        (crystalPairConnection_isHorizontal hF k.unop) := rfl

/-- The components of `crystalDeRhamPresheaf` on a morphism: `m ⊗ ω ↦ k^* m ⊗ Ω_k(ω)`. -/
theorem crystalDeRhamPresheaf_map_f {T T' : (AffineCris S)ᵒᵖ} (k : T ⟶ T') (p : ℕ) :
    (((crystalDeRhamPresheaf hF).map k).f p).hom =
      DeRhamPair.termMap (sectionsDPRingMap k.unop.hom.hom)
        (isDPMorphism_sectionsDPRingMap k.unop.hom.hom) (crystalPairRestrict k.unop) p := rfl

/-! ### Degree zero -/

/-- The restriction map of `ℱ` along a morphism of `AffineCris S`, read as a map of
`Γ(S, 𝒪_S)`-modules. -/
def crystalPairRestrictScalars {T T' : AffineCris S} (k : T ⟶ T') :
    RestrictScalars Γ(S.S.scheme, ⊤) (sectionsDPRing S T'.obj.obj) (F.val.obj (op T'.obj)) →ₗ[
      Γ(S.S.scheme, ⊤)]
      RestrictScalars Γ(S.S.scheme, ⊤) (sectionsDPRing S T.obj.obj) (F.val.obj (op T.obj)) :=
  DeRhamPair.restrictScalarsMap (sectionsDPRingMap k.hom.hom) (crystalPairRestrict k)

variable (F) in
/-- **The presheaf `T ↦ ℱ(T)` on the affine objects of `Cris(X/S)`**, its values read as
`Γ(S, 𝒪_S)`-modules by restriction of scalars along the structure morphisms. -/
def crystalSectionsPresheaf : (AffineCris S)ᵒᵖ ⥤ ModuleCat.{u} Γ(S.S.scheme, ⊤) where
  obj T := restrictScalarsModuleCat Γ(S.S.scheme, ⊤) (sectionsDPRing S T.unop.obj.obj)
    (F.val.obj (op T.unop.obj))
  map k :=
    ConcreteCategory.ofHom (C := ModuleCat Γ(S.S.scheme, ⊤)) (crystalPairRestrictScalars k.unop)
  map_id T := ConcreteCategory.hom_ext _ _ fun x ↦ crysSiteRestrict_id F T.unop.obj x
  map_comp k k' := ConcreteCategory.hom_ext _ _ fun x ↦
    (crysSiteRestrict_comp F k'.unop.hom k.unop.hom x).symm

/-- **The degree-zero term of the de Rham complex of a crystal is the crystal**: the natural
isomorphism `ℱ(T) ⊗ Ω^0 = ℱ(T) ⊗ Γ(T, 𝒪_T) ≅ ℱ(T)` on the affine objects of `Cris(X/S)`. -/
def crystalDeRhamPresheafDegreeZeroIso :
    crystalDeRhamPresheaf hF ⋙ HomologicalComplex.eval _ _ 0 ≅ crystalSectionsPresheaf F :=
  NatIso.ofComponents (fun T ↦ (DeRhamPair.degreeZeroEquiv Γ(S.S.scheme, ⊤)
      (sectionsDPRing S T.unop.obj.obj) (F.val.obj (op T.unop.obj))).toModuleIso)
    (fun _k ↦ ModuleCat.hom_ext (LinearMap.ext fun x ↦ DeRhamPair.degreeZeroEquiv_termMap _ _ _ x))

/-- The degree-zero isomorphism on a pure tensor: `m ⊗ ω ↦ ω · m`. -/
theorem crystalDeRhamPresheafDegreeZeroIso_hom_app_tmul (T : (AffineCris S)ᵒᵖ)
    (m : F.val.obj (op T.unop.obj))
    (ω : ⋀[sectionsDPRing S T.unop.obj.obj]^0 (dividedPowerDifferentials
      (A := Γ(S.S.scheme, ⊤)) (sectionsDPRing S T.unop.obj.obj).dividedPowers)) :
    RestrictScalars.addEquiv Γ(S.S.scheme, ⊤) (sectionsDPRing S T.unop.obj.obj) _
        (((crystalDeRhamPresheafDegreeZeroIso hF).hom.app T).hom
          ((RestrictScalars.addEquiv Γ(S.S.scheme, ⊤) (sectionsDPRing S T.unop.obj.obj) _).symm
            (m ⊗ₜ ω))) =
      exteriorPower.zeroEquiv (sectionsDPRing S T.unop.obj.obj) _ ω • m :=
  DeRhamPair.degreeZeroEquiv_tmul _ m ω

/-! ### The row comparison along a divided power polynomial presentation -/

section Row

open DividedPowers DividedPowerPolynomial

variable {T T' : AffineCris S} (k : T ⟶ T') (W : Type u)
  (e : (DeRhamPair.polyRing (sectionsDPRing S T'.obj.obj) W : Type u) →ₐ[Γ(S.S.scheme, ⊤)]
    sectionsDPRing S T.obj.obj)
  (hfe : ∀ b, e (coefficientAlgHom Γ(S.S.scheme, ⊤) (sectionsDPRing S T'.obj.obj) W b) =
    sectionsDPRingMap k.hom.hom b)
  (e' : (sectionsDPRing S T.obj.obj : Type u) →ₐ[Γ(S.S.scheme, ⊤)]
    (DeRhamPair.polyRing (sectionsDPRing S T'.obj.obj) W : Type u))
  (hee' : ∀ c, e (e' c) = c) (he'e : ∀ q, e' (e q) = q)

omit [IsAffine S.S.scheme] in
include hfe in
/-- `e` turns the scalar action of `Γ(T', 𝒪_{T'})` on the divided power polynomial algebra into
multiplication by its image along `sectionsDPRingMap`. -/
theorem polyPresentation_smul (b : sectionsDPRing S T'.obj.obj)
    (q : setIndexedDividedPowerPolynomialAlgebra (sectionsDPRing S T'.obj.obj) W) :
    e (b • q) = sectionsDPRingMap k.hom.hom b * e q := by
  rw [Algebra.smul_def, map_mul, ← hfe]
  rfl

/-- The map `B⟨x_w⟩ ⊗_{Γ(T')} ℱ(T') → Γ(T) ⊗_{Γ(T')} ℱ(T')`, `q ⊗ m ↦ e(q) ⊗ m`, into the source
of the base change of sections of `ℱ` along `k`. -/
def polyPresentationCross :
    setIndexedDividedPowerPolynomialAlgebra (sectionsDPRing S T'.obj.obj) W ⊗[
        sectionsDPRing S T'.obj.obj] F.val.obj (op T'.obj) →+
      ringAlong k.hom.hom ⊗[crysSheafRing S T'.obj.obj] F.val.obj (op T'.obj) :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun q ↦ (TensorProduct.mk (crysSheafRing S T'.obj.obj)
        (ringAlong k.hom.hom) (F.val.obj (op T'.obj))
        (ringAlongSection k.hom.hom (e q))).toAddMonoidHom)
      (fun q q' ↦ AddMonoidHom.ext fun m ↦ by
        change ringAlongSection k.hom.hom (e (q + q')) ⊗ₜ m =
          ringAlongSection k.hom.hom (e q) ⊗ₜ m + ringAlongSection k.hom.hom (e q') ⊗ₜ m
        rw [map_add]
        exact TensorProduct.add_tmul _ _ _))
    (fun b q m ↦ by
      change ringAlongSection k.hom.hom (e (b • q)) ⊗ₜ[crysSheafRing S T'.obj.obj] m =
        ringAlongSection k.hom.hom (e q) ⊗ₜ[crysSheafRing S T'.obj.obj]
          ((b : crysSheafRing S T'.obj.obj) • m)
      rw [polyPresentation_smul k W e hfe]
      exact TensorProduct.smul_tmul (R := crysSheafRing S T'.obj.obj)
        (R' := crysSheafRing S T'.obj.obj) b (ringAlongSection k.hom.hom (e q)) m)

omit [IsAffine S.S.scheme] in
/-- `polyPresentationCross` on a pure tensor. -/
theorem polyPresentationCross_tmul
    (q : setIndexedDividedPowerPolynomialAlgebra (sectionsDPRing S T'.obj.obj) W)
    (m : F.val.obj (op T'.obj)) :
    polyPresentationCross k W e hfe (q ⊗ₜ m) = ringAlongSection k.hom.hom (e q) ⊗ₜ m := rfl

include hfe he'e in
/-- The inverse of `polyPresentationCross`, `t ⊗ m ↦ e⁻¹(t) ⊗ m`. -/
def polyPresentationCrossInv :
    ringAlong k.hom.hom ⊗[crysSheafRing S T'.obj.obj] F.val.obj (op T'.obj) →+
      setIndexedDividedPowerPolynomialAlgebra (sectionsDPRing S T'.obj.obj) W ⊗[
        sectionsDPRing S T'.obj.obj] F.val.obj (op T'.obj) :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun t ↦ (TensorProduct.mk (sectionsDPRing S T'.obj.obj)
        (setIndexedDividedPowerPolynomialAlgebra (sectionsDPRing S T'.obj.obj) W)
        (F.val.obj (op T'.obj)) (e' (siteRingAlong k.hom.hom t))).toAddMonoidHom)
      (fun t t' ↦ AddMonoidHom.ext fun m ↦ by
        change e' (siteRingAlong k.hom.hom (t + t')) ⊗ₜ m =
          e' (siteRingAlong k.hom.hom t) ⊗ₜ m + e' (siteRingAlong k.hom.hom t') ⊗ₜ m
        exact (congrArg (· ⊗ₜ[sectionsDPRing S T'.obj.obj] m)
          (map_add e' (siteRingAlong k.hom.hom t : sectionsDPRing S T.obj.obj)
            (siteRingAlong k.hom.hom t'))).trans (TensorProduct.add_tmul _ _ _)))
    (fun b t m ↦ by
      change e' (siteRingAlong k.hom.hom (b • t)) ⊗ₜ[sectionsDPRing S T'.obj.obj] m =
        e' (siteRingAlong k.hom.hom t) ⊗ₜ[sectionsDPRing S T'.obj.obj]
          ((b : sectionsDPRing S T'.obj.obj) • m)
      have hb : ∀ (b' : sectionsDPRing S T'.obj.obj) (c : sectionsDPRing S T.obj.obj),
          e' (sectionsDPRingMap k.hom.hom b' * c) = b' • e' c := fun b' c ↦ by
        rw [map_mul, ← hfe, he'e, Algebra.smul_def]
        rfl
      exact (congrArg (· ⊗ₜ[sectionsDPRing S T'.obj.obj] m)
        (hb b (siteRingAlong k.hom.hom t))).trans
        (TensorProduct.smul_tmul (R := sectionsDPRing S T'.obj.obj)
          (R' := sectionsDPRing S T'.obj.obj)
          (M := setIndexedDividedPowerPolynomialAlgebra (sectionsDPRing S T'.obj.obj) W) b
          (e' (siteRingAlong k.hom.hom t)) m))

omit [IsAffine S.S.scheme] in
/-- `polyPresentationCrossInv` on a pure tensor. -/
theorem polyPresentationCrossInv_tmul (t : ringAlong k.hom.hom) (m : F.val.obj (op T'.obj)) :
    polyPresentationCrossInv k W e hfe e' he'e (t ⊗ₜ m) = e' (siteRingAlong k.hom.hom t) ⊗ₜ m := rfl

omit [IsAffine S.S.scheme] in
/-- The linearisation `B⟨x_w⟩ ⊗_{Γ(T')} ℱ(T') → ℱ(T)` of the restriction map along the presentation
`e` is the base change of sections of `ℱ` along `k`, after `polyPresentationCross`. -/
theorem polyModuleMap_eq_crysBaseChange
    (z : setIndexedDividedPowerPolynomialAlgebra (sectionsDPRing S T'.obj.obj) W
      ⊗[sectionsDPRing S T'.obj.obj] F.val.obj (op T'.obj)) :
    DeRhamPair.polyModuleMap W (sectionsDPRingMap k.hom.hom) (crystalPairRestrict k) e hfe z =
      crysBaseChange F k.hom (polyPresentationCross k W e hfe z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul q m => rfl

omit [IsAffine S.S.scheme] in
include hee' in
/-- `polyPresentationCrossInv` is a right inverse of `polyPresentationCross`. -/
theorem polyPresentationCross_crossInv
    (w : ringAlong k.hom.hom ⊗[crysSheafRing S T'.obj.obj] F.val.obj (op T'.obj)) :
    polyPresentationCross k W e hfe (polyPresentationCrossInv k W e hfe e' he'e w) = w := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul t m =>
    exact congrArg (· ⊗ₜ[crysSheafRing S T'.obj.obj] m) (hee' (siteRingAlong k.hom.hom t))

omit [IsAffine S.S.scheme] in
/-- `polyPresentationCrossInv` is a left inverse of `polyPresentationCross`. -/
theorem polyPresentationCrossInv_cross
    (z : setIndexedDividedPowerPolynomialAlgebra (sectionsDPRing S T'.obj.obj) W
      ⊗[sectionsDPRing S T'.obj.obj] F.val.obj (op T'.obj)) :
    polyPresentationCrossInv k W e hfe e' he'e (polyPresentationCross k W e hfe z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul q m =>
    show e' (e q) ⊗ₜ m = q ⊗ₜ m
    rw [he'e]

omit [IsAffine S.S.scheme] in
include hF hee' he'e in
/-- **The crystal property along a divided power polynomial presentation**: for a crystal in
quasi-coherent modules, the linearisation `B⟨x_w⟩ ⊗_{Γ(T')} ℱ(T') → ℱ(T)`, `q ⊗ m ↦ e(q) · k^* m`,
is bijective. -/
theorem bijective_polyModuleMap_crystalRestrict :
    Function.Bijective (DeRhamPair.polyModuleMap W (sectionsDPRingMap k.hom.hom)
      (crystalPairRestrict (F := F) k) e hfe) := by
  have hL := bijective_crysBaseChange_of_isQuasicoherentOnSite F hF k.hom
    (isAffineObject_of_isAffine S T.obj) (isAffineObject_of_isAffine S T'.obj)
  refine ⟨fun z₁ z₂ h ↦ ?_, fun n ↦ ?_⟩
  · rw [polyModuleMap_eq_crysBaseChange, polyModuleMap_eq_crysBaseChange] at h
    rw [← polyPresentationCrossInv_cross (F := F) k W e hfe e' he'e z₁,
      ← polyPresentationCrossInv_cross (F := F) k W e hfe e' he'e z₂, hL.1 h]
  · obtain ⟨w, rfl⟩ := hL.2 n
    exact ⟨polyPresentationCrossInv (F := F) k W e hfe e' he'e w, by
      rw [polyModuleMap_eq_crysBaseChange, polyPresentationCross_crossInv k W e hfe e' hee' he'e]⟩

include hfe hee' he'e in
/-- **The row comparison of the Čech–de Rham double complex of a crystal**
([Stacks, Lemma 60.19.2, Tag 07LD], transported): if `k : T ⟶ T'` is a morphism of affine
objects of `Cris(X/S)` along which `Γ(T, 𝒪_T)` is a divided power polynomial algebra over
`Γ(T', 𝒪_{T'})` — an isomorphism `e : Γ(T', 𝒪_{T'})⟨x_w⟩ ≅ Γ(T, 𝒪_T)` of divided power
`Γ(S, 𝒪_S)`-algebras with `e ∘ (Γ(T') → Γ(T')⟨x_w⟩) = k^*` — then the restriction map
`ℱ(T') ⊗ Ω^*_{Γ(T')} ⟶ ℱ(T) ⊗ Ω^*_{Γ(T)}` of de Rham complexes is a quasi-isomorphism. -/
theorem quasiIso_crystalDeRhamPresheaf_map
    (he : IsDPMorphism (DeRhamPair.polyRing (sectionsDPRing S T'.obj.obj) W).dividedPowers
      (sectionsDPRing S T.obj.obj).dividedPowers e.toRingHom)
    (he' : IsDPMorphism (sectionsDPRing S T.obj.obj).dividedPowers
      (DeRhamPair.polyRing (sectionsDPRing S T'.obj.obj) W).dividedPowers e'.toRingHom) :
    QuasiIso ((crystalDeRhamPresheaf hF).map k.op) :=
  DeRhamPair.quasiIso_deRhamMap_of_dpPolynomial.{u, u} W (sectionsDPRingMap k.hom.hom)
    (isDPMorphism_sectionsDPRingMap k.hom.hom) (crystalPairRestrict k) e he hfe
    (crystalPairConnection hF T') (crystalPairConnection hF T) e' he' hee' he'e
    (bijective_polyModuleMap_crystalRestrict hF k W e hfe e' hee' he'e)
    (crystalPairConnection_isIntegrable hF T') (crystalPairConnection_isIntegrable hF T)
    (crystalPairConnection_isHorizontal hF k)

end Row

/-! ### The big-site specialisation -/

section BigSite

variable {N : SheafOfModules.{u} (crystallineStructureSheaf S)} (hN : N.IsQuasicoherentOnSite)

omit [IsAffine S.S.scheme] in
include hN in
/-- **The restriction to `Cris(X/S)` of a quasi-coherent module on `CRIS(X/S)` is quasi-coherent**
([Stacks, Tag 07IT] on both sites). -/
theorem isQuasicoherentOnSite_restrictSheafOfModules :
    (restrictSheafOfModules N).IsQuasicoherentOnSite :=
  (isQuasiCoherentCrystal_restrictSheafOfModules hN).1

/-- **The presheaf of de Rham complexes of a quasi-coherent module on `CRIS(X/S)`** on the affine
objects of `Cris(X/S)`: that of its restriction to the small site. -/
abbrev bigCrystalDeRhamPresheaf :
    (AffineCris S)ᵒᵖ ⥤ CochainComplex (ModuleCat.{u} Γ(S.S.scheme, ⊤)) ℕ :=
  crystalDeRhamPresheaf (isQuasicoherentOnSite_restrictSheafOfModules hN)

/-- The canonical connection of a quasi-coherent module on `CRIS(X/S)` on an affine object of
`Cris(X/S)`, in the spelling of `Crystalline.DeRhamPair`. -/
abbrev bigCrystalPairConnection (T : AffineCris S) :
    Connection Γ(S.S.scheme, ⊤) (sectionsDPRing S T.obj.obj)
      (oneVariableBaseProjection Γ(S.S.scheme, ⊤) (sectionsDPRing S T.obj.obj))
      ((restrictSheafOfModules N).val.obj (op T.obj)) :=
  crystalPairConnection (isQuasicoherentOnSite_restrictSheafOfModules hN) T

end BigSite

end Crystalline.GlobalCrystallineSituation
