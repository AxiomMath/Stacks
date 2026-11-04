module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackFibreLiftAutPullback
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackFibreLiftComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.RetractionDerivedPullbackCoherenceOfMap
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.RetractionDerivedPullbackNaturalityOfMap

/-!
# The comparison of the lifts of `E₀` of a lift of `w₀` and of a pullback of it

Let `x₀` be a field point of `Complexes_{X/Y}` over `Spec k`, `f : V ⟶ W` a linear map, `A_V`,
`A_W` objects of `Complexes_{X/Y}` over `T_V = Spec k[V]` and `T_W = Spec k[W]` with retractions to
`T₀`, `m_V : x₀ ⟶ A_V`, `m_W : x₀ ⟶ A_W` and `φ : A_W ⟶ A_V` a morphism lying over
`Spec k[W] ⟶ Spec k[V]` with `m_W.base ≫ φ.base = m_V.base`. Through the derived equivalences
`eD_V`, `eD_W` of the two lifts of `E₀`, the comparison `χ` of derived base change along
`𝒪_{X₀}[V] ⟶ 𝒪_{X₀}[W]` with derived pullback along `X_φ`
(`AlgebraicGeometry.Space.ComplexesSituation.fibreDataPullbackNaturality`, which is
`AlgebraicGeometry.Space.squareZeroDerivedPullbackNaturality` read along the identifications of
the derived equivalences with their generic spelling), the counits and the comparison of `φ` give
the isomorphism `e : L_f K_V ≅ K_W` of step 4 of the proof of Stacks 0DLL
(`AlgebraicGeometry.Space.ComplexesSituation.fibreDataPullbackComparison`):
`eD_W e = χ ≫ L(X_φ)^* ε_V ≫ φ ≫ ε_W⁻¹`. It carries automorphisms of `K_V` to automorphisms of
`K_W` compatibly with `φ`
(`AlgebraicGeometry.Space.ComplexesSituation.fibreDataPullbackComparison_aut`, the naturality of
`χ`).

The compatibility of `e` with the identifications with `E₀` is the coherence (`**`) of `c2` with
base change along `X_φ`
(`AlgebraicGeometry.Space.squareZeroDerivedPullbackIso_comp_coherence_of_comp`), read through the
naturality of `c2` and of the composition comparison
(`CategoryTheory.Functor.pullbackComparison_identification_eq`) and moved from the generic spelling
to the spelling of the field point (`CategoryTheory.Functor.pullbackCoherence_of_eq`, with
`AlgebraicGeometry.Space.ComplexesSituation.fibreDataDerivedEquivalence_functor_eq_V` and
`AlgebraicGeometry.Space.ComplexesSituation.fibreDataDerivedPullbackIso_heq_V`). It is
`AlgebraicGeometry.Space.ComplexesSituation.fibreDataPullbackCoherence`, an instance of
`AlgebraicGeometry.Space.squareZeroDerivedPullbackIso_comp_coherence_of_heq`, and makes `e` an
isomorphism of lifts
(`AlgebraicGeometry.Space.ComplexesSituation.fibreDataPullbackComparison_identification`).
At lifts of `w₀` this is step 4 of the proof of Stacks 0DLL
(`AlgebraicGeometry.Space.ComplexesSituation.fibreLiftAutPullback`) and the compatibility of the
classes of lifts of `E₀⟦m⟧` with pullback
(`AlgebraicGeometry.Space.ComplexesSituation.fibreLiftClassPullback`).

## References

* [Stacks Project, Tag 0DLL](https://stacks.math.columbia.edu/tag/0DLL)
-/

@[expose] public noncomputable section

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

open CategoryTheory CategoryTheory.Limits Opposite Deformation.Artin Deformation.ComplexLift
  Stacks.TensorByBaseModule

universe d u

namespace CategoryTheory.Functor

variable {CV CW YV YW Z : Type*} [Category* CV] [Category* CW] [Category* YV] [Category* YW]
  [Category* Z]

/-- **Step 4 of Stacks 0DLL for abstract functors: the comparison is an isomorphism of lifts.**
Let `c2_W : T_W ≅ F_W ⋙ P_W`, `c2_V : T_V ≅ F_V ⋙ P_V`, `χ : L ⋙ F_W ≅ F_V ⋙ P_H`,
`τ : P_V ≅ P_H ⋙ P_W` and `c : L ⋙ T_W ≅ T_V` satisfy the coherence (`**`) at `K`. For
`ε_V : F_V K ≅ E_V`, `ε_W : F_W K' ≅ E_W`, `φ : P_H E_V ⟶ E_W`, `m : P_W E_W ⟶ E₀` and
`e : L K ⟶ K'` with `F_W e = χ ≫ P_H ε_V ≫ φ ≫ ε_W⁻¹`, the identification
`c2_W ≫ P_W ε_W ≫ m` of `K'` precomposed with `T_W e` is `c` followed by the identification
`c2_V ≫ P_V ε_V ≫ (τ ≫ P_W φ ≫ m)` of `K`. -/
theorem pullbackComparison_identification_eq (L : CV ⥤ CW) (TW : CW ⥤ Z) (TV : CV ⥤ Z)
    (FV : CV ⥤ YV) (FW : CW ⥤ YW) (PH : YV ⥤ YW) (PW : YW ⥤ Z) (PV : YV ⥤ Z)
    (c2W : TW ≅ FW ⋙ PW) (c2V : TV ≅ FV ⋙ PV) (χ : L ⋙ FW ≅ FV ⋙ PH) (τ : PV ≅ PH ⋙ PW)
    (c : L ⋙ TW ≅ TV) {K : CV} {K' : CW} {EV : YV} {EW : YW} {E₀ : Z}
    (εV : FV.obj K ≅ EV) (εW : FW.obj K' ≅ EW) (φ : PH.obj EV ⟶ EW) (m : PW.obj EW ⟶ E₀)
    (e : L.obj K ⟶ K') (he : FW.map e = χ.hom.app K ≫ PH.map εV.hom ≫ φ ≫ εW.inv)
    (hcoh : c2W.hom.app (L.obj K) ≫ PW.map (χ.hom.app K) ≫ τ.inv.app (FV.obj K) =
      c.hom.app K ≫ c2V.hom.app K) :
    TW.map e ≫ (c2W.hom.app K' ≫ PW.map εW.hom ≫ m) =
      c.hom.app K ≫ (c2V.hom.app K ≫ PV.map εV.hom ≫ (τ.hom.app EV ≫ PW.map φ ≫ m)) := by
  have h1 : TW.map e ≫ c2W.hom.app K' = c2W.hom.app (L.obj K) ≫ PW.map (FW.map e) :=
    c2W.hom.naturality e
  have h2 : PV.map εV.hom ≫ τ.hom.app EV = τ.hom.app (FV.obj K) ≫ PW.map (PH.map εV.hom) :=
    τ.hom.naturality εV.hom
  have h3 : c.hom.app K ≫ c2V.hom.app K ≫ τ.hom.app (FV.obj K) =
      c2W.hom.app (L.obj K) ≫ PW.map (χ.hom.app K) := by
    rw [← reassoc_of% hcoh]
    simp
  rw [reassoc_of% h1, reassoc_of% h2, reassoc_of% h3, he]
  simp

/-- `CategoryTheory.Functor.pullbackComparison_identification_eq` with the last factor of the
identification of `K` given as a morphism `m_V = (τ', m, φ)` (`CategoryTheory.Functor.fibreComp`)
for a comparison `τ' = τ`: the form in which the comparison of a composite of morphisms of
`Complexes_{X/Y}` comes. -/
theorem pullbackComparison_identification_eq_of_fibreComp (L : CV ⥤ CW) (TW : CW ⥤ Z)
    (TV : CV ⥤ Z) (FV : CV ⥤ YV) (FW : CW ⥤ YW) (PH : YV ⥤ YW) (PW : YW ⥤ Z) (PV : YV ⥤ Z)
    (c2W : TW ≅ FW ⋙ PW) (c2V : TV ≅ FV ⋙ PV) (χ : L ⋙ FW ≅ FV ⋙ PH) (τ : PV ≅ PH ⋙ PW)
    (c : L ⋙ TW ≅ TV) {K : CV} {K' : CW} {EV : YV} {EW : YW} {E₀ : Z}
    (εV : FV.obj K ≅ EV) (εW : FW.obj K' ≅ EW) (φ : PH.obj EV ⟶ EW) (m : PW.obj EW ⟶ E₀)
    (τ' : PV ≅ PH ⋙ PW) (hτ : τ' = τ) (mV : PV.obj EV ⟶ E₀)
    (hmV : mV = Functor.fibreComp τ' m φ)
    (e : L.obj K ⟶ K') (he : FW.map e = χ.hom.app K ≫ PH.map εV.hom ≫ φ ≫ εW.inv)
    (hcoh : BaseChangePullbackCoherence L TW TV FV FW PH PW PV c2W c2V χ τ c K) :
    TW.map e ≫ (c2W.hom.app K' ≫ PW.map εW.hom ≫ m) =
      c.hom.app K ≫ (c2V.hom.app K ≫ PV.map εV.hom ≫ mV) := by
  subst hτ hmV
  exact pullbackComparison_identification_eq L TW TV FV FW PH PW PV c2W c2V χ τ' c εV εW φ m e he
    hcoh

/-- **Step 4 of Stacks 0DLL for abstract functors: the comparison carries automorphisms.** For
`χ : L ⋙ F_W ≅ F_V ⋙ P_H`, `ε_V : F_V K ≅ E_V`, `ε_W : F_W K' ≅ E_W`, an isomorphism
`φ : P_H E_V ⟶ E_W` and `e : L K ≅ K'` with `F_W e = χ ≫ P_H ε_V ≫ φ ≫ ε_W⁻¹`, the automorphism
of `E_W` induced by `e⁻¹ ∘ L α ∘ e`, after `φ`, is the pullback along `P_H` of the automorphism
of `E_V` induced by `α`, before `φ`: the naturality of `χ`. -/
theorem pullbackComparison_aut_eq (L : CV ⥤ CW) (FV : CV ⥤ YV) (FW : CW ⥤ YW) (PH : YV ⥤ YW)
    (χ : L ⋙ FW ≅ FV ⋙ PH) {K : CV} {K' : CW} {EV : YV} {EW : YW}
    (εV : FV.obj K ≅ EV) (εW : FW.obj K' ≅ EW) (φ : PH.obj EV ⟶ EW) (hφ : IsIso φ)
    (e : L.obj K ≅ K') (he : FW.map e.hom = χ.hom.app K ≫ PH.map εV.hom ≫ φ ≫ εW.inv)
    (α : K ≅ K) :
    φ ≫ (εW.symm ≪≫ FW.mapIso (e.symm ≪≫ L.mapIso α ≪≫ e) ≪≫ εW).hom =
      PH.map (εV.symm ≪≫ FV.mapIso α ≪≫ εV).hom ≫ φ := by
  have := hφ
  have hinv : FW.map e.inv = εW.hom ≫ CategoryTheory.inv φ ≫ PH.map εV.inv ≫ χ.inv.app K := by
    rw [← cancel_epi (FW.map e.hom), ← FW.map_comp, e.hom_inv_id, FW.map_id, he]
    simp
  have hχ : FW.map (L.map α.hom) ≫ χ.hom.app K = χ.hom.app K ≫ PH.map (FV.map α.hom) :=
    χ.hom.naturality α.hom
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc,
    hinv, he]
  simp only [IsIso.hom_inv_id_assoc, reassoc_of% hχ, Iso.inv_hom_id_app_assoc,
    ← PH.map_comp_assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

/-- An isomorphism `L ⋙ F'_W ≅ F'_V ⋙ P_H` read along equalities `F_W = F'_W`, `F_V = F'_V`. -/
def pullbackNaturalityOfEq (L : CV ⥤ CW) (FV FV' : CV ⥤ YV) (FW FW' : CW ⥤ YW) (PH : YV ⥤ YW)
    (hFW : FW = FW') (hFV : FV = FV') (χ' : L ⋙ FW' ≅ FV' ⋙ PH) : L ⋙ FW ≅ FV ⋙ PH :=
  Functor.isoWhiskerLeft L (eqToIso hFW) ≪≫ χ' ≪≫ Functor.isoWhiskerRight (eqToIso hFV.symm) PH

/-- **Moving the coherence (`**`) along equal functors.** If the coherence holds for
`c2'_W : T_W ≅ F'_W ⋙ P_W`, `c2'_V : T_V ≅ F'_V ⋙ P_V`, `χ' : L ⋙ F'_W ≅ F'_V ⋙ P_H`, `τ` and `c`,
and `F_W = F'_W`, `F_V = F'_V` with `c2_W`, `c2_V` heterogeneously equal to `c2'_W`, `c2'_V`, then
it holds for `c2_W`, `c2_V` and `χ'` read along the two equalities. -/
theorem pullbackCoherence_of_eq (L : CV ⥤ CW) (TW : CW ⥤ Z) (TV : CV ⥤ Z)
    (FV FV' : CV ⥤ YV) (FW FW' : CW ⥤ YW) (PH : YV ⥤ YW) (PW : YW ⥤ Z) (PV : YV ⥤ Z)
    (c2W : TW ≅ FW ⋙ PW) (c2W' : TW ≅ FW' ⋙ PW) (c2V : TV ≅ FV ⋙ PV) (c2V' : TV ≅ FV' ⋙ PV)
    (χ' : L ⋙ FW' ≅ FV' ⋙ PH) (τ : PV ≅ PH ⋙ PW) (c : L ⋙ TW ≅ TV)
    (hFW : FW = FW') (hFV : FV = FV') (h2W : HEq c2W c2W') (h2V : HEq c2V c2V') (K : CV)
    (hcoh : c2W'.hom.app (L.obj K) ≫ PW.map (χ'.hom.app K) ≫ τ.inv.app (FV'.obj K) =
      c.hom.app K ≫ c2V'.hom.app K) :
    c2W.hom.app (L.obj K) ≫
        PW.map ((pullbackNaturalityOfEq L FV FV' FW FW' PH hFW hFV χ').hom.app K) ≫
          τ.inv.app (FV.obj K) =
      c.hom.app K ≫ c2V.hom.app K := by
  subst hFW hFV
  cases h2W
  cases h2V
  simpa [pullbackNaturalityOfEq] using hcoh

/-- `χ'` read along equalities `F_W = F'_W`, `F_V = F'_V` is heterogeneously equal to `χ'`. -/
theorem pullbackNaturalityOfEq_heq (L : CV ⥤ CW) (FV FV' : CV ⥤ YV) (FW FW' : CW ⥤ YW)
    (PH : YV ⥤ YW) (hFW : FW = FW') (hFV : FV = FV') (χ' : L ⋙ FW' ≅ FV' ⋙ PH) :
    HEq (pullbackNaturalityOfEq L FV FV' FW FW' PH hFW hFV χ') χ' := by
  subst hFW hFV
  apply heq_of_eq
  ext K
  simp [pullbackNaturalityOfEq]

end CategoryTheory.Functor

/-- A morphism equal to `eqToHom`-conjugate of a morphism which is itself an `eqToHom`-conjugate of
`g`, conjugated back by `eqToHom`s, is `g`. -/
theorem CategoryTheory.eqToHom_conj_eq_of_eq_eqToHom_conj {C : Type*} [Category* C]
    {A B A' B' A'' B'' : C} (x : A ⟶ B) (y : A' ⟶ B') (g : A'' ⟶ B'') (p : A = A') (q : B' = B)
    (r : A' = A'') (s : B'' = B') (t : A'' = A) (w : B = B'')
    (hx : x = eqToHom p ≫ y ≫ eqToHom q) (hy : y = eqToHom r ≫ g ≫ eqToHom s) :
    eqToHom t ≫ x ≫ eqToHom w = g := by
  subst hx hy p q r s
  simp

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance 20000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective
  hasSheafCompose_smallEtale_forget₂_ringCat

namespace ComplexesSituation

variable {D : ComplexesSituation B S hS}

attribute [local instance] complexesCategory

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] {iΛ : Spec (.of Λ) ⟶ S}
  {x₀ : ComplexesObject D}
  {hx₀ : (complexesFunctor D ⋙ Over.post B.inclusion).obj x₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
  {hk : B.Contains (Spec (.of k))}

/-! ### The coefficient rings in the spelling of the retractions

The ring `𝒪_{X₀}[𝒪_{X₀} ⊗_k V]` at the coefficient map of the field point is, by definition, the
ring `𝒪_{X₀}[𝒪_{X₀} ⊗_k V]` at the coefficient map of the retraction data:
`AlgebraicGeometry.Space.ComplexesSituation.squareZeroCoefficientMap_eq_fieldPointCoefficientMap`.
-/

/-- A model of the derived category of `𝒪_{X₀}[𝒪_{X₀} ⊗_k U]`, in the spelling of the
retractions. -/
abbrev fibreGenericDerivedCategory {U : FGModuleCat.{u} k}
    (h : HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (coefficientRing (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) U)))) :
    HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (sqZeroExtSheafAnySite (structureSheaf B S hS (D.space x₀.T).1 (D.space x₀.T).2)
      ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS (D.space x₀.T).1)
      (structureSheaf B S hS (D.space x₀.T).1 (D.space x₀.T).2) (SheafOfModules.unit _)
      (squareZeroCoefficientMap k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
        ((D.projection x₀.T).hom ≫ yoneda.map
          (eqToHom (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk))))).obj
      ((fgSiteModule B hk).obj U).obj)))) :=
  h

/-- The model `AlgebraicGeometry.Space.ComplexesSituation.fibreGenericDerivedCategory` is the given
model. -/
theorem fibreGenericDerivedCategory_heq {U : FGModuleCat.{u} k}
    (h : HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (coefficientRing (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) U)))) :
    HEq h (fibreGenericDerivedCategory h) :=
  HEq.rfl

variable (D iΛ x₀ hx₀ hk) in
/-- The ring map `𝒪_{X₀}[U] ⟶ 𝒪_{X₀}[U']` of a linear map, in the spelling of the retractions. -/
def fibreGenericRingMap {U U' : FGModuleCat.{u} k} (f : U ⟶ U') :
    (sqZeroExtSheafAnySite (structureSheaf B S hS (D.space x₀.T).1 (D.space x₀.T).2)
      ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS (D.space x₀.T).1)
      (structureSheaf B S hS (D.space x₀.T).1 (D.space x₀.T).2) (SheafOfModules.unit _)
      (squareZeroCoefficientMap k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
        ((D.projection x₀.T).hom ≫ yoneda.map
          (eqToHom (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk))))).obj
      ((fgSiteModule B hk).obj U).obj)) ⟶ (sqZeroExtSheafAnySite
          (structureSheaf B S hS (D.space x₀.T).1 (D.space x₀.T).2)
      ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS (D.space x₀.T).1)
      (structureSheaf B S hS (D.space x₀.T).1 (D.space x₀.T).2) (SheafOfModules.unit _)
      (squareZeroCoefficientMap k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
        ((D.projection x₀.T).hom ≫ yoneda.map
          (eqToHom (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk))))).obj
      ((fgSiteModule B hk).obj U').obj)) :=
  coefficientRingMap (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) f

/-- The ring map `AlgebraicGeometry.Space.ComplexesSituation.fibreGenericRingMap` is the ring map
of the linear map. -/
theorem fibreGenericRingMap_heq {U U' : FGModuleCat.{u} k} (f : U ⟶ U') :
    HEq (coefficientRingMap (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) f)
        (fibreGenericRingMap D iΛ x₀ hx₀ hk f) :=
  HEq.rfl

variable (D iΛ x₀ hx₀ hk) in
/-- `𝒪_{X₀} ⊗_k U` in the spelling of the retractions is `𝒪_{X₀} ⊗_k U` at the coefficient map of
the field point. -/
theorem fibreGenericModule_eq (U : FGModuleCat.{u} k) :
    ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS (D.space x₀.T).1)
      (structureSheaf B S hS (D.space x₀.T).1 (D.space x₀.T).2) (SheafOfModules.unit _)
      (squareZeroCoefficientMap k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
        ((D.projection x₀.T).hom ≫ yoneda.map
          (eqToHom (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk))))).obj
      ((fgSiteModule B hk).obj U).obj) = (coefficientModule
          (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)).obj U :=
  rfl

/-! ### The comparison for morphisms of `Complexes_{X/Y}` with retractions -/

section Data

variable {V W : FGModuleCat.{u} k} (f : V ⟶ W)
  [hDV : HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (coefficientRing (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) V)))]
  [hDW : HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (coefficientRing (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) W)))]
  (AV AW : ComplexesObject D) (mW : x₀ ⟶ AW) (mV : x₀ ⟶ AV) (φ : AW ⟶ AV)
  (hb : mW.base ≫ φ.base = mV.base)
  (tV : AV.T ⟶ x₀.T) (tW : AW.T ⟶ x₀.T)
  (hbtV : mV.base ≫ tV = 𝟙 x₀.T) (hbV : IsSquareZeroClosedImmersion B S hS mV.base.left)
  (hTV : AV.T.left = squareZeroOver k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)
    ((fgSiteModule B hk).obj V))
  (hβV : eqToHom (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk).symm ≫ mV.base.left ≫
      eqToHom hTV =
    squareZeroArrow k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
      ((fgSiteModule B hk).obj V))
  (hbtW : mW.base ≫ tW = 𝟙 x₀.T) (hbW : IsSquareZeroClosedImmersion B S hS mW.base.left)
  (hTW : AW.T.left = squareZeroOver k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)
    ((fgSiteModule B hk).obj W))
  (hβW : eqToHom (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk).symm ≫ mW.base.left ≫
      eqToHom hTW =
    squareZeroArrow k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
      ((fgSiteModule B hk).obj W))
  (htφ : φ.base ≫ tV = tW)
  (hφ : eqToHom hTW.symm ≫ φ.base.left ≫ eqToHom hTV =
    squareZeroOverMap k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)
      ((fgSiteModule B hk).map f))


include hb in
/-- `X_{m_W} ≫ X_φ = X_{m_V}`, in the spelling of the base changes of the retraction data. -/
theorem fibreData_relativeMap_comp :
    D.relativeMap mW.base ≫ D.relativeMap φ.base = D.relativeMap mV.base :=
  (baseChangeMap_comp D.f mW.base φ.base).symm.trans (congrArg (baseChangeMap D.f) hb)

include htφ in
/-- `X_φ ≫ X_{t_V} = X_{t_W}`, in the spelling of the base changes of the retraction data. -/
theorem fibreData_relativeMap_comp_retraction :
    D.relativeMap φ.base ≫ D.relativeMap tV = D.relativeMap tW :=
  (baseChangeMap_comp D.f φ.base tV).symm.trans (congrArg (baseChangeMap D.f) htφ)

/-- The derived equivalence of `A_V` is the derived equivalence
`AlgebraicGeometry.Space.squareZeroDerivedEquivalence` of the retraction `X_{t_V}`. -/
theorem fibreDataDerivedEquivalence_functor_eq_V :
    (fibreDataDerivedEquivalence (hx₀ := hx₀) AV.T mV.base tV hbtV hbV hTV hβV).functor =
      (letI : HasDerivedCategory.{d} (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (sqZeroExtSheafAnySite
          (structureSheaf B S hS (D.space x₀.T).1 (D.space x₀.T).2)
      ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS (D.space x₀.T).1)
      (structureSheaf B S hS (D.space x₀.T).1 (D.space x₀.T).2) (SheafOfModules.unit _)
      (squareZeroCoefficientMap k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
        ((D.projection x₀.T).hom ≫ yoneda.map (eqToHom
            (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk))))).obj
            ((fgSiteModule B hk).obj V).obj)))) := hDV
    (squareZeroDerivedEquivalence (hq := relativelyRepresentable_baseChangeMap B S hS D.f tV)
        (IsFirstOrderThickeningHom.isThickeningHom B S hS
      (D.isFirstOrderThickeningHom_relativeMap _ hbV))
    (D.relativeMap_section_comp_retraction hbtV)
    (CoherentSituation.comp_yoneda_map_eqToHom hTV (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk)
      _ _ _ _ _ hβV (D.relativeMap_hom_comp_projection _))
    (CoherentSituation.isPullback_yoneda_map_eqToHom hTV
      (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk) _ _ _ _ (D.isPullback_relativeMap_hom tV))
    (CoherentSituation.eqToHom_conj_comp_eqToHom_conj
      (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk) hTV _ _ (congrArg CommaMorphism.left hbtV)
      _ hβV)).functor) :=
  rfl

/-- The derived equivalence of `A_W` is `AlgebraicGeometry.Space.squareZeroDerivedEquivalence` of
the retraction `X_{t_W}`. -/
theorem fibreDataDerivedEquivalence_functor_eq_W :
    (fibreDataDerivedEquivalence (hx₀ := hx₀) AW.T mW.base tW hbtW hbW hTW hβW).functor =
      (letI : HasDerivedCategory.{d} (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (sqZeroExtSheafAnySite
          (structureSheaf B S hS (D.space x₀.T).1 (D.space x₀.T).2)
      ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS (D.space x₀.T).1)
      (structureSheaf B S hS (D.space x₀.T).1 (D.space x₀.T).2) (SheafOfModules.unit _)
      (squareZeroCoefficientMap k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
        ((D.projection x₀.T).hom ≫ yoneda.map (eqToHom
            (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk))))).obj
            ((fgSiteModule B hk).obj W).obj)))) := hDW
    (squareZeroDerivedEquivalence (hq := relativelyRepresentable_baseChangeMap B S hS D.f tW)
        (IsFirstOrderThickeningHom.isThickeningHom B S hS
      (D.isFirstOrderThickeningHom_relativeMap _ hbW))
    (D.relativeMap_section_comp_retraction hbtW)
    (CoherentSituation.comp_yoneda_map_eqToHom hTW (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk)
      _ _ _ _ _ hβW (D.relativeMap_hom_comp_projection _))
    (CoherentSituation.isPullback_yoneda_map_eqToHom hTW
      (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk) _ _ _ _ (D.isPullback_relativeMap_hom tW))
    (CoherentSituation.eqToHom_conj_comp_eqToHom_conj
      (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk) hTW _ _ (congrArg CommaMorphism.left hbtW)
      _ hβW)).functor) :=
  rfl

/-- `c2` of `A_V` is `AlgebraicGeometry.Space.squareZeroDerivedPullbackIso` of the retraction
`X_{t_V}`. -/
theorem fibreDataDerivedPullbackIso_heq_V :
    HEq (fibreDataDerivedPullbackIso (hx₀ := hx₀) AV.T mV.base tV hbtV hbV hTV hβV
        (derivedExtensionOfScalarsData.{d, u + 1}
        (sqZeroExtSheafAnySiteProj ((coefficientModule
        (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)).obj V))))
      (letI : HasDerivedCategory.{d} (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (sqZeroExtSheafAnySite
          (structureSheaf B S hS (D.space x₀.T).1 (D.space x₀.T).2)
      ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS (D.space x₀.T).1)
      (structureSheaf B S hS (D.space x₀.T).1 (D.space x₀.T).2) (SheafOfModules.unit _)
      (squareZeroCoefficientMap k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
        ((D.projection x₀.T).hom ≫ yoneda.map (eqToHom
            (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk))))).obj
            ((fgSiteModule B hk).obj V).obj)))) := hDV
    squareZeroDerivedPullbackIso (hq := relativelyRepresentable_baseChangeMap B S hS D.f tV)
        (IsFirstOrderThickeningHom.isThickeningHom B S hS
      (D.isFirstOrderThickeningHom_relativeMap _ hbV))
    (D.relativeMap_section_comp_retraction hbtV)
    (CoherentSituation.comp_yoneda_map_eqToHom hTV (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk)
      _ _ _ _ _ hβV (D.relativeMap_hom_comp_projection _))
    (CoherentSituation.isPullback_yoneda_map_eqToHom hTV
      (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk) _ _ _ _ (D.isPullback_relativeMap_hom tV))
    (CoherentSituation.eqToHom_conj_comp_eqToHom_conj
      (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk) hTV _ _ (congrArg CommaMorphism.left hbtV)
      _ hβV) (derivedExtensionOfScalarsData.{d, u + 1}
          (sqZeroExtSheafAnySiteProj ((coefficientModule
          (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)).obj V)))) :=
  HEq.rfl

/-- `c2` of `A_W` is `AlgebraicGeometry.Space.squareZeroDerivedPullbackIso` of the retraction
`X_{t_W}`. -/
theorem fibreDataDerivedPullbackIso_heq_W :
    HEq (fibreDataDerivedPullbackIso (hx₀ := hx₀) AW.T mW.base tW hbtW hbW hTW hβW
        (derivedExtensionOfScalarsData.{d, u + 1}
        (sqZeroExtSheafAnySiteProj ((coefficientModule
        (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)).obj W))))
      (letI : HasDerivedCategory.{d} (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (sqZeroExtSheafAnySite
          (structureSheaf B S hS (D.space x₀.T).1 (D.space x₀.T).2)
      ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS (D.space x₀.T).1)
      (structureSheaf B S hS (D.space x₀.T).1 (D.space x₀.T).2) (SheafOfModules.unit _)
      (squareZeroCoefficientMap k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
        ((D.projection x₀.T).hom ≫ yoneda.map (eqToHom
            (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk))))).obj
            ((fgSiteModule B hk).obj W).obj)))) := hDW
    squareZeroDerivedPullbackIso (hq := relativelyRepresentable_baseChangeMap B S hS D.f tW)
        (IsFirstOrderThickeningHom.isThickeningHom B S hS
      (D.isFirstOrderThickeningHom_relativeMap _ hbW))
    (D.relativeMap_section_comp_retraction hbtW)
    (CoherentSituation.comp_yoneda_map_eqToHom hTW (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk)
      _ _ _ _ _ hβW (D.relativeMap_hom_comp_projection _))
    (CoherentSituation.isPullback_yoneda_map_eqToHom hTW
      (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk) _ _ _ _ (D.isPullback_relativeMap_hom tW))
    (CoherentSituation.eqToHom_conj_comp_eqToHom_conj
      (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk) hTW _ _ (congrArg CommaMorphism.left hbtW)
      _ hβW) (derivedExtensionOfScalarsData.{d, u + 1}
          (sqZeroExtSheafAnySiteProj ((coefficientModule
          (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)).obj W)))) :=
  HEq.rfl

omit hDV hDW in
include hb htφ hφ in
/-- The hypothesis `hg` of `χ` at the ring map `𝒪_{X₀}[V] ⟶ 𝒪_{X₀}[W]` of `f`, for a morphism
`φ : A_W ⟶ A_V` lying over `Spec k[W] ⟶ Spec k[V]`:
`AlgebraicGeometry.Space.squareZeroStructureSheafIso_naturality`. -/
theorem fibreDataStructureSheafIso_naturality :
    (letI : HasDerivedCategory.{d} (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (sqZeroExtSheafAnySite
        (structureSheaf B S hS (D.space x₀.T).1 (D.space x₀.T).2)
      ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS (D.space x₀.T).1)
      (structureSheaf B S hS (D.space x₀.T).1 (D.space x₀.T).2) (SheafOfModules.unit _)
      (squareZeroCoefficientMap k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
        ((D.projection x₀.T).hom ≫ yoneda.map (eqToHom
            (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk))))).obj
            ((fgSiteModule B hk).obj V).obj)))) := hDV
    letI : HasDerivedCategory.{d} (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (sqZeroExtSheafAnySite
        (structureSheaf B S hS (D.space x₀.T).1 (D.space x₀.T).2)
      ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS (D.space x₀.T).1)
      (structureSheaf B S hS (D.space x₀.T).1 (D.space x₀.T).2) (SheafOfModules.unit _)
      (squareZeroCoefficientMap k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
        ((D.projection x₀.T).hom ≫ yoneda.map (eqToHom
            (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk))))).obj
            ((fgSiteModule B hk).obj W).obj)))) := hDW
    (squareZeroStructureSheafIso (hq := relativelyRepresentable_baseChangeMap B S hS D.f tV)
        (IsFirstOrderThickeningHom.isThickeningHom B S hS
      (D.isFirstOrderThickeningHom_relativeMap _ hbV))
    (D.relativeMap_section_comp_retraction hbtV)
    (CoherentSituation.comp_yoneda_map_eqToHom hTV (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk)
      _ _ _ _ _ hβV (D.relativeMap_hom_comp_projection _))
    (CoherentSituation.isPullback_yoneda_map_eqToHom hTV
      (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk) _ _ _ _ (D.isPullback_relativeMap_hom tV))
    (CoherentSituation.eqToHom_conj_comp_eqToHom_conj
      (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk) hTV _ _ (congrArg CommaMorphism.left hbtV)
      _ hβV)).hom ≫
      (thickeningRetractionEquivalence B S hS
        (IsFirstOrderThickeningHom.isThickeningHom B S hS
          (D.isFirstOrderThickeningHom_relativeMap _ hbV))
        (D.relativeMap_section_comp_retraction hbtV)
        (relativelyRepresentable_baseChangeMap B S hS D.f tV) CommRingCat.{u}).functor.map
          (coefficientRingMap (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) f :
              (sqZeroExtSheafAnySite (structureSheaf B S hS (D.space x₀.T).1 (D.space x₀.T).2)
      ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS (D.space x₀.T).1)
      (structureSheaf B S hS (D.space x₀.T).1 (D.space x₀.T).2) (SheafOfModules.unit _)
      (squareZeroCoefficientMap k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
        ((D.projection x₀.T).hom ≫ yoneda.map (eqToHom
            (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk))))).obj
            ((fgSiteModule B hk).obj V).obj)) ⟶ (sqZeroExtSheafAnySite
            (structureSheaf B S hS (D.space x₀.T).1 (D.space x₀.T).2)
      ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS (D.space x₀.T).1)
      (structureSheaf B S hS (D.space x₀.T).1 (D.space x₀.T).2) (SheafOfModules.unit _)
      (squareZeroCoefficientMap k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
        ((D.projection x₀.T).hom ≫ yoneda.map (eqToHom
            (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk))))).obj
            ((fgSiteModule B hk).obj W).obj)))) =
      thickeningPushforwardRingMap (hqV := relativelyRepresentable_baseChangeMap B S hS D.f tV)
        (IsFirstOrderThickeningHom.isThickeningHom B S hS
          (D.isFirstOrderThickeningHom_relativeMap _ hbV))
        (D.relativeMap_section_comp_retraction hbtV)
        (IsFirstOrderThickeningHom.isThickeningHom B S hS
          (D.isFirstOrderThickeningHom_relativeMap _ hbW))
        (D.relativeMap_section_comp_retraction hbtW)
        (relativelyRepresentable_baseChangeMap B S hS D.f φ.base)
        (fibreData_relativeMap_comp AV AW mW mV φ hb)
        (squareZeroStructureSheafIso (hq := relativelyRepresentable_baseChangeMap B S hS D.f tW)
            (IsFirstOrderThickeningHom.isThickeningHom B S hS
      (D.isFirstOrderThickeningHom_relativeMap _ hbW))
    (D.relativeMap_section_comp_retraction hbtW)
    (CoherentSituation.comp_yoneda_map_eqToHom hTW (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk)
      _ _ _ _ _ hβW (D.relativeMap_hom_comp_projection _))
    (CoherentSituation.isPullback_yoneda_map_eqToHom hTW
      (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk) _ _ _ _ (D.isPullback_relativeMap_hom tW))
    (CoherentSituation.eqToHom_conj_comp_eqToHom_conj
      (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk) hTW _ _ (congrArg CommaMorphism.left hbtW)
      _ hβW)).hom :=
  squareZeroStructureSheafIso_naturality (hqV := relativelyRepresentable_baseChangeMap B S hS D.f
      tV) (hqW := relativelyRepresentable_baseChangeMap B S hS D.f tW)
      (IsFirstOrderThickeningHom.isThickeningHom B S hS
      (D.isFirstOrderThickeningHom_relativeMap _ hbV))
    (D.relativeMap_section_comp_retraction hbtV)
    (CoherentSituation.comp_yoneda_map_eqToHom hTV (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk)
      _ _ _ _ _ hβV (D.relativeMap_hom_comp_projection _))
    (CoherentSituation.isPullback_yoneda_map_eqToHom hTV
      (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk) _ _ _ _ (D.isPullback_relativeMap_hom tV))
    (CoherentSituation.eqToHom_conj_comp_eqToHom_conj
      (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk) hTV _ _ (congrArg CommaMorphism.left hbtV)
      _ hβV) (IsFirstOrderThickeningHom.isThickeningHom B S hS
      (D.isFirstOrderThickeningHom_relativeMap _ hbW))
    (D.relativeMap_section_comp_retraction hbtW)
    (CoherentSituation.comp_yoneda_map_eqToHom hTW (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk)
      _ _ _ _ _ hβW (D.relativeMap_hom_comp_projection _))
    (CoherentSituation.isPullback_yoneda_map_eqToHom hTW
      (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk) _ _ _ _ (D.isPullback_relativeMap_hom tW))
    (CoherentSituation.eqToHom_conj_comp_eqToHom_conj
      (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk) hTW _ _ (congrArg CommaMorphism.left hbtW)
      _ hβW)
    (relativelyRepresentable_baseChangeMap B S hS D.f φ.base)
    (fibreData_relativeMap_comp AV AW mW mV φ hb) ((fgSiteModule B hk).map f)
    (fibreData_relativeMap_comp_retraction AV AW φ tV tW htφ)
    (CoherentSituation.comp_yoneda_map_eqToHom hTV hTW _ _ _ _ _ hφ
      (D.relativeMap_hom_comp_projection φ.base))

include hb htφ hφ in
/-- **`χ` for a morphism `φ : A_W ⟶ A_V` of `Complexes_{X/Y}` lying over `Spec k[W] ⟶ Spec k[V]`**
(`AlgebraicGeometry.Space.squareZeroDerivedPullbackNaturality` at the ring map of `f`): the derived
base change along `𝒪_{X₀}[V] ⟶ 𝒪_{X₀}[W]` followed by the derived equivalence of `A_W` is the
derived equivalence of `A_V` followed by the derived pullback along `X_φ`. -/
def fibreDataPullbackNaturality :
    (derivedExtensionOfScalars.{d, d} (coefficientRingMap (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)
        f)) ⋙ (fibreDataDerivedEquivalence (hx₀ := hx₀) AW.T mW.base tW hbtW hbW hTW hβW).functor ≅
        (fibreDataDerivedEquivalence (hx₀ := hx₀) AV.T mV.base tV hbtV hbV hTV hβV).functor ⋙
        (derivedPull B S hS (hasDerivedModulePullbacks B S hS) (D.relativeMap φ.base)) :=
  Functor.pullbackNaturalityOfEq _ _ _ _ _ _
      (fibreDataDerivedEquivalence_functor_eq_W AW mW tW hbtW hbW hTW hβW)
    (fibreDataDerivedEquivalence_functor_eq_V AV mV tV hbtV hbV hTV hβV)
    (squareZeroDerivedPullbackNaturality (hDV := hDV) (hDW := hDW)
        (hqV := relativelyRepresentable_baseChangeMap B S hS D.f tV)
        (hqW := relativelyRepresentable_baseChangeMap B S hS D.f tW)
        (IsFirstOrderThickeningHom.isThickeningHom B S hS
      (D.isFirstOrderThickeningHom_relativeMap _ hbV))
    (D.relativeMap_section_comp_retraction hbtV)
    (CoherentSituation.comp_yoneda_map_eqToHom hTV (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk)
      _ _ _ _ _ hβV (D.relativeMap_hom_comp_projection _))
    (CoherentSituation.isPullback_yoneda_map_eqToHom hTV
      (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk) _ _ _ _ (D.isPullback_relativeMap_hom tV))
    (CoherentSituation.eqToHom_conj_comp_eqToHom_conj
      (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk) hTV _ _ (congrArg CommaMorphism.left hbtV)
      _ hβV) (IsFirstOrderThickeningHom.isThickeningHom B S hS
      (D.isFirstOrderThickeningHom_relativeMap _ hbW))
    (D.relativeMap_section_comp_retraction hbtW)
    (CoherentSituation.comp_yoneda_map_eqToHom hTW (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk)
      _ _ _ _ _ hβW (D.relativeMap_hom_comp_projection _))
    (CoherentSituation.isPullback_yoneda_map_eqToHom hTW
      (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk) _ _ _ _ (D.isPullback_relativeMap_hom tW))
    (CoherentSituation.eqToHom_conj_comp_eqToHom_conj
      (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk) hTW _ _ (congrArg CommaMorphism.left hbtW)
      _ hβW)
      (relativelyRepresentable_baseChangeMap B S hS D.f φ.base)
    (fibreData_relativeMap_comp AV AW mW mV φ hb)
        (fibreDataStructureSheafIso_naturality f AV AW mW mV φ hb tV tW hbtV hbV hTV hβV hbtW hbW
        hTW hβW htφ hφ))

include hb htφ hφ in
/-- **Stacks 0DLL, step 4: the comparison `e : L_f K_V ≅ K_W`** of the lift of `E₀` attached to
`m_W ≫ φ : x₀ ⟶ A_V`, base changed along `𝒪_{X₀}[V] ⟶ 𝒪_{X₀}[W]`, with the lift of `E₀` attached
to `m_W : x₀ ⟶ A_W`: the preimage under the derived equivalence of `A_W` of
`χ ≫ L(X_φ)^* ε_V ≫ φ ≫ ε_W⁻¹`
(`AlgebraicGeometry.Space.ComplexesSituation.fibreDataPullbackNaturality`, the counits of the
derived equivalences and the comparison of `φ`). -/
def fibreDataPullbackComparison :
    (derivedExtensionOfScalars.{d, d} (coefficientRingMap (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)
        f)).obj ((fibreDataDerivedEquivalence (hx₀ := hx₀) AV.T mV.base tV hbtV hbV hTV
        hβV).inverse.obj AV.E) ≅ (fibreDataDerivedEquivalence (hx₀ := hx₀) AW.T mW.base tW hbtW hbW
        hTW hβW).inverse.obj AW.E :=
  (fibreDataDerivedEquivalence (hx₀ := hx₀) AW.T mW.base tW hbtW hbW hTW
      hβW).fullyFaithfulFunctor.preimageIso
    ((fibreDataPullbackNaturality f AV AW mW mV φ hb tV tW hbtV hbV hTV hβV hbtW hbW hTW hβW htφ
        hφ).app _ ≪≫
      (derivedPull B S hS (hasDerivedModulePullbacks B S hS) (D.relativeMap φ.base)).mapIso
          ((fibreDataDerivedEquivalence (hx₀ := hx₀) AV.T mV.base tV hbtV hbV hTV hβV).counitIso.app
          AV.E) ≪≫
      @asIso _ _ _ _ φ.fibre φ.isIso_fibre ≪≫ ((fibreDataDerivedEquivalence (hx₀ := hx₀) AW.T
          mW.base tW hbtW hbW hTW hβW).counitIso.app AW.E).symm)

include hb htφ hφ in
/-- The defining equation of
`AlgebraicGeometry.Space.ComplexesSituation.fibreDataPullbackComparison`: its image under the
derived equivalence of `A_W` is `χ ≫ L(X_φ)^* ε_V ≫ φ ≫ ε_W⁻¹`. -/
theorem fibreDataPullbackComparison_hom_map :
    (fibreDataDerivedEquivalence (hx₀ := hx₀) AW.T mW.base tW hbtW hbW hTW hβW).functor.map
        (fibreDataPullbackComparison f AV AW mW mV φ hb tV tW hbtV hbV hTV hβV hbtW hbW hTW hβW htφ
        hφ).hom =
      (fibreDataPullbackNaturality f AV AW mW mV φ hb tV tW hbtV hbV hTV hβV hbtW hbW hTW hβW htφ
          hφ).hom.app _ ≫
        (derivedPull B S hS (hasDerivedModulePullbacks B S hS) (D.relativeMap φ.base)).map
            ((fibreDataDerivedEquivalence (hx₀ := hx₀) AV.T mV.base tV hbtV hbV hTV
            hβV).counitIso.app AV.E).hom ≫ φ.fibre ≫
            ((fibreDataDerivedEquivalence (hx₀ := hx₀) AW.T mW.base tW hbtW hbW hTW
            hβW).counitIso.app AW.E).inv :=
  (fibreDataDerivedEquivalence (hx₀ := hx₀) AW.T mW.base tW hbtW hbW hTW
      hβW).fullyFaithfulFunctor.map_preimage _

include hb htφ hφ in
/-- **Stacks 0DLL, step 4: the comparison carries automorphisms.** For an automorphism `α` of the
lift of `E₀` attached to `m_V`, the automorphism of the complex of `A_W` attached to
`e⁻¹ ∘ L_f α ∘ e` (`AlgebraicGeometry.Space.ComplexesSituation.fibreDataPullbackComparison`), after
the comparison of `φ`, is the derived pullback along `X_φ` of the automorphism of the complex of
`A_V` attached to `α`, before it: the naturality of `χ`. -/
theorem fibreDataPullbackComparison_aut (hK : DerivedCategory.TStructure.t.minus x₀.E)
    (α : Aut (fibreDataDerivedLift (hDer := hDV) AV mV tV hbtV hbV hTV hβV hK).K.obj) :
    φ.fibre ≫ (fibreDataComplexAut (hDer := hDW) AW mW tW hbtW hbW hTW hβW hK
        ((fibreDataPullbackComparison f AV AW mW mV φ hb tV tW hbtV hbV hTV hβV hbtW hbW hTW hβW htφ
            hφ).symm ≪≫
          (derivedExtensionOfScalars.{d, d} (coefficientRingMap
              (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) f)).mapIso α ≪≫
          fibreDataPullbackComparison f AV AW mW mV φ hb tV tW hbtV hbV hTV hβV hbtW hbW hTW hβW htφ
              hφ)).hom =
      ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap φ.base)).map
          (fibreDataComplexAut (hDer := hDV) AV mV tV hbtV hbV hTV hβV hK α).hom ≫ φ.fibre :=
  Functor.pullbackComparison_aut_eq _ _ _ _
      (fibreDataPullbackNaturality f AV AW mW mV φ hb tV tW hbtV hbV hTV hβV hbtW hbW hTW hβW htφ
      hφ) _ _ φ.fibre φ.isIso_fibre _
    (fibreDataPullbackComparison_hom_map f AV AW mW mV φ hb tV tW hbtV hbV hTV hβV hbtW hbW hTW hβW
        htφ hφ) α



/-- The derived equivalence of `A_V` is heterogeneously equal to
`AlgebraicGeometry.Space.squareZeroDerivedEquivalence` of the retraction `X_{t_V}`, at the model
`AlgebraicGeometry.Space.ComplexesSituation.fibreGenericDerivedCategory`. -/
theorem fibreDataDerivedEquivalence_functor_heq_V :
    HEq (fibreDataDerivedEquivalence (hx₀ := hx₀) AV.T mV.base tV hbtV hbV hTV hβV).functor
      (letI := fibreGenericDerivedCategory hDV
      (squareZeroDerivedEquivalence (hq := relativelyRepresentable_baseChangeMap B S hS D.f tV)
        (IsFirstOrderThickeningHom.isThickeningHom B S hS
      (D.isFirstOrderThickeningHom_relativeMap _ hbV))
    (D.relativeMap_section_comp_retraction hbtV)
    (CoherentSituation.comp_yoneda_map_eqToHom hTV (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk)
      _ _ _ _ _ hβV (D.relativeMap_hom_comp_projection _))
    (CoherentSituation.isPullback_yoneda_map_eqToHom hTV
      (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk) _ _ _ _ (D.isPullback_relativeMap_hom tV))
    (CoherentSituation.eqToHom_conj_comp_eqToHom_conj
      (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk) hTV _ _ (congrArg CommaMorphism.left hbtV)
      _ hβV)).functor) :=
  heq_of_eq (fibreDataDerivedEquivalence_functor_eq_V AV mV tV hbtV hbV hTV hβV)

/-- `c2` of `A_V` is heterogeneously equal to
`AlgebraicGeometry.Space.squareZeroDerivedPullbackIso` of the retraction `X_{t_V}`, in the spelling
of the retractions. -/
theorem fibreDataDerivedPullbackIso_heq_generic_V :
    HEq (fibreDataDerivedPullbackIso (hx₀ := hx₀) AV.T mV.base tV hbtV hbV hTV hβV
        (derivedExtensionOfScalarsData.{d, u + 1} (sqZeroExtSheafAnySiteProj
          ((coefficientModule (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)).obj V))))
      (letI := fibreGenericDerivedCategory hDV
      squareZeroDerivedPullbackIso (hq := relativelyRepresentable_baseChangeMap B S hS D.f tV)
        (IsFirstOrderThickeningHom.isThickeningHom B S hS
      (D.isFirstOrderThickeningHom_relativeMap _ hbV))
    (D.relativeMap_section_comp_retraction hbtV)
    (CoherentSituation.comp_yoneda_map_eqToHom hTV (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk)
      _ _ _ _ _ hβV (D.relativeMap_hom_comp_projection _))
    (CoherentSituation.isPullback_yoneda_map_eqToHom hTV
      (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk) _ _ _ _ (D.isPullback_relativeMap_hom tV))
    (CoherentSituation.eqToHom_conj_comp_eqToHom_conj
      (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk) hTV _ _ (congrArg CommaMorphism.left hbtV)
      _ hβV)
        (derivedExtensionOfScalarsData.{d, u + 1} (sqZeroExtSheafAnySiteProj
          ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS (D.space x₀.T).1)
      (structureSheaf B S hS (D.space x₀.T).1 (D.space x₀.T).2) (SheafOfModules.unit _)
      (squareZeroCoefficientMap k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
        ((D.projection x₀.T).hom ≫ yoneda.map
          (eqToHom (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk))))).obj
      ((fgSiteModule B hk).obj V).obj)))) :=
  HEq.rfl

/-- The derived equivalence of `A_W` is heterogeneously equal to
`AlgebraicGeometry.Space.squareZeroDerivedEquivalence` of the retraction `X_{t_W}`, at the model
`AlgebraicGeometry.Space.ComplexesSituation.fibreGenericDerivedCategory`. -/
theorem fibreDataDerivedEquivalence_functor_heq_W :
    HEq (fibreDataDerivedEquivalence (hx₀ := hx₀) AW.T mW.base tW hbtW hbW hTW hβW).functor
      (letI := fibreGenericDerivedCategory hDW
      (squareZeroDerivedEquivalence (hq := relativelyRepresentable_baseChangeMap B S hS D.f tW)
        (IsFirstOrderThickeningHom.isThickeningHom B S hS
      (D.isFirstOrderThickeningHom_relativeMap _ hbW))
    (D.relativeMap_section_comp_retraction hbtW)
    (CoherentSituation.comp_yoneda_map_eqToHom hTW (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk)
      _ _ _ _ _ hβW (D.relativeMap_hom_comp_projection _))
    (CoherentSituation.isPullback_yoneda_map_eqToHom hTW
      (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk) _ _ _ _ (D.isPullback_relativeMap_hom tW))
    (CoherentSituation.eqToHom_conj_comp_eqToHom_conj
      (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk) hTW _ _ (congrArg CommaMorphism.left hbtW)
      _ hβW)).functor) :=
  heq_of_eq (fibreDataDerivedEquivalence_functor_eq_W AW mW tW hbtW hbW hTW hβW)

/-- `c2` of `A_W` is heterogeneously equal to
`AlgebraicGeometry.Space.squareZeroDerivedPullbackIso` of the retraction `X_{t_W}`, in the spelling
of the retractions. -/
theorem fibreDataDerivedPullbackIso_heq_generic_W :
    HEq (fibreDataDerivedPullbackIso (hx₀ := hx₀) AW.T mW.base tW hbtW hbW hTW hβW
        (derivedExtensionOfScalarsData.{d, u + 1} (sqZeroExtSheafAnySiteProj
          ((coefficientModule (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)).obj W))))
      (letI := fibreGenericDerivedCategory hDW
      squareZeroDerivedPullbackIso (hq := relativelyRepresentable_baseChangeMap B S hS D.f tW)
        (IsFirstOrderThickeningHom.isThickeningHom B S hS
      (D.isFirstOrderThickeningHom_relativeMap _ hbW))
    (D.relativeMap_section_comp_retraction hbtW)
    (CoherentSituation.comp_yoneda_map_eqToHom hTW (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk)
      _ _ _ _ _ hβW (D.relativeMap_hom_comp_projection _))
    (CoherentSituation.isPullback_yoneda_map_eqToHom hTW
      (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk) _ _ _ _ (D.isPullback_relativeMap_hom tW))
    (CoherentSituation.eqToHom_conj_comp_eqToHom_conj
      (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk) hTW _ _ (congrArg CommaMorphism.left hbtW)
      _ hβW)
        (derivedExtensionOfScalarsData.{d, u + 1} (sqZeroExtSheafAnySiteProj
          ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS (D.space x₀.T).1)
      (structureSheaf B S hS (D.space x₀.T).1 (D.space x₀.T).2) (SheafOfModules.unit _)
      (squareZeroCoefficientMap k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
        ((D.projection x₀.T).hom ≫ yoneda.map
          (eqToHom (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk))))).obj
      ((fgSiteModule B hk).obj W).obj)))) :=
  HEq.rfl

include hb htφ hφ in
/-- `χ` of `φ` is heterogeneously equal to
`AlgebraicGeometry.Space.squareZeroDerivedPullbackNaturality` at the models
`AlgebraicGeometry.Space.ComplexesSituation.fibreGenericDerivedCategory` and the ring map
`AlgebraicGeometry.Space.ComplexesSituation.fibreGenericRingMap`. -/
theorem fibreDataPullbackNaturality_heq :
    HEq (fibreDataPullbackNaturality f AV AW mW mV φ hb tV tW hbtV hbV hTV hβV hbtW hbW hTW hβW htφ
        hφ)
      (squareZeroDerivedPullbackNaturality (hDV := fibreGenericDerivedCategory hDV)
        (hDW := fibreGenericDerivedCategory hDW)
        (hqV := relativelyRepresentable_baseChangeMap B S hS D.f tV)
        (hqW := relativelyRepresentable_baseChangeMap B S hS D.f tW)
        (g := fibreGenericRingMap D iΛ x₀ hx₀ hk f)
        (IsFirstOrderThickeningHom.isThickeningHom B S hS
      (D.isFirstOrderThickeningHom_relativeMap _ hbV))
    (D.relativeMap_section_comp_retraction hbtV)
    (CoherentSituation.comp_yoneda_map_eqToHom hTV (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk)
      _ _ _ _ _ hβV (D.relativeMap_hom_comp_projection _))
    (CoherentSituation.isPullback_yoneda_map_eqToHom hTV
      (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk) _ _ _ _ (D.isPullback_relativeMap_hom tV))
    (CoherentSituation.eqToHom_conj_comp_eqToHom_conj
      (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk) hTV _ _ (congrArg CommaMorphism.left hbtV)
      _ hβV)
        (IsFirstOrderThickeningHom.isThickeningHom B S hS
      (D.isFirstOrderThickeningHom_relativeMap _ hbW))
    (D.relativeMap_section_comp_retraction hbtW)
    (CoherentSituation.comp_yoneda_map_eqToHom hTW (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk)
      _ _ _ _ _ hβW (D.relativeMap_hom_comp_projection _))
    (CoherentSituation.isPullback_yoneda_map_eqToHom hTW
      (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk) _ _ _ _ (D.isPullback_relativeMap_hom tW))
    (CoherentSituation.eqToHom_conj_comp_eqToHom_conj
      (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk) hTW _ _ (congrArg CommaMorphism.left hbtW)
      _ hβW)
        (relativelyRepresentable_baseChangeMap B S hS D.f φ.base)
        (fibreData_relativeMap_comp AV AW mW mV φ hb)
        (fibreDataStructureSheafIso_naturality f AV AW mW mV φ hb tV tW hbtV hbV hTV hβV hbtW hbW
            hTW hβW htφ hφ)) :=
  Functor.pullbackNaturalityOfEq_heq _ _ _ _ _ _ _ _ _

include hb htφ hφ in
/-- **The coherence (`**`) for a morphism `φ : A_W ⟶ A_V` of `Complexes_{X/Y}`**:
`AlgebraicGeometry.Space.squareZeroDerivedPullbackIso_comp_coherence_of_comp` for `X_{m_W}`, `X_φ`
and `X_{m_V}` at the ring map of `f`, read on the derived equivalences, the identifications `c2`
and the comparison `χ` of `A_W` and `A_V`
(`AlgebraicGeometry.Space.squareZeroDerivedPullbackIso_comp_coherence_of_heq`). -/
theorem fibreDataPullbackCoherence
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (coefficientRing (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) V)))) :
    Functor.BaseChangePullbackCoherence
      (derivedExtensionOfScalars.{d, d} (coefficientRingMap
          (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) f))
      (derivedExtensionOfScalarsData.{d, u + 1} (sqZeroExtSheafAnySiteProj
        ((coefficientModule (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)).obj W))).baseChange
      (derivedExtensionOfScalarsData.{d, u + 1} (sqZeroExtSheafAnySiteProj
        ((coefficientModule (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)).obj V))).baseChange
      (fibreDataDerivedEquivalence (hx₀ := hx₀) AV.T mV.base tV hbtV hbV hTV hβV).functor
      (fibreDataDerivedEquivalence (hx₀ := hx₀) AW.T mW.base tW hbtW hbW hTW hβW).functor
      (derivedPull B S hS (hasDerivedModulePullbacks B S hS) (D.relativeMap φ.base))
      (derivedPull B S hS (hasDerivedModulePullbacks B S hS) (D.relativeMap mW.base))
      (derivedPull B S hS (hasDerivedModulePullbacks B S hS) (D.relativeMap mV.base))
      (fibreDataDerivedPullbackIso (hx₀ := hx₀) AW.T mW.base tW hbtW hbW hTW hβW
        (derivedExtensionOfScalarsData.{d, u + 1} (sqZeroExtSheafAnySiteProj
          ((coefficientModule (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)).obj W))))
      (fibreDataDerivedPullbackIso (hx₀ := hx₀) AV.T mV.base tV hbtV hbV hTV hβV
        (derivedExtensionOfScalarsData.{d, u + 1} (sqZeroExtSheafAnySiteProj
          ((coefficientModule (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)).obj V))))
      (fibreDataPullbackNaturality f AV AW mW mV φ hb tV tW hbtV hbV hTV hβV hbtW hbW hTW hβW htφ
          hφ)
      ((smallEtaleDerivedPullbackData B S hS).triangle
        (fibreData_relativeMap_comp AV AW mW mV φ hb))
      (derivedExtensionOfScalarsCompIso.{d, d, u + 1}
          (coefficientRingMap (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) f)
        (coefficientRingMap_comp_proj (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) f)) K := by
  refine squareZeroDerivedPullbackIso_comp_coherence_of_heq
    (hqV := relativelyRepresentable_baseChangeMap B S hS D.f tV)
    (hqW := relativelyRepresentable_baseChangeMap B S hS D.f tW)
    (IsFirstOrderThickeningHom.isThickeningHom B S hS
      (D.isFirstOrderThickeningHom_relativeMap _ hbV))
    (D.relativeMap_section_comp_retraction hbtV)
    (CoherentSituation.comp_yoneda_map_eqToHom hTV (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk)
      _ _ _ _ _ hβV (D.relativeMap_hom_comp_projection _))
    (CoherentSituation.isPullback_yoneda_map_eqToHom hTV
      (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk) _ _ _ _ (D.isPullback_relativeMap_hom tV))
    (CoherentSituation.eqToHom_conj_comp_eqToHom_conj
      (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk) hTV _ _ (congrArg CommaMorphism.left hbtV)
      _ hβV)
    (IsFirstOrderThickeningHom.isThickeningHom B S hS
      (D.isFirstOrderThickeningHom_relativeMap _ hbW))
    (D.relativeMap_section_comp_retraction hbtW)
    (CoherentSituation.comp_yoneda_map_eqToHom hTW (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk)
      _ _ _ _ _ hβW (D.relativeMap_hom_comp_projection _))
    (CoherentSituation.isPullback_yoneda_map_eqToHom hTW
      (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk) _ _ _ _ (D.isPullback_relativeMap_hom tW))
    (CoherentSituation.eqToHom_conj_comp_eqToHom_conj
      (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk) hTW _ _ (congrArg CommaMorphism.left hbtW)
      _ hβW)
    (relativelyRepresentable_baseChangeMap B S hS D.f φ.base)
    (fibreData_relativeMap_comp AV AW mW mV φ hb)
    (MV := (coefficientModule (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)).obj V)
    (MW := (coefficientModule (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)).obj W)
    (hDVM := hDV) (hDWM := hDW) (hDV := fibreGenericDerivedCategory hDV)
    (hDW := fibreGenericDerivedCategory hDW)
    (g := coefficientRingMap (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) f)
    (g₀ := fibreGenericRingMap D iΛ x₀ hx₀ hk f)
    (FV := (fibreDataDerivedEquivalence (hx₀ := hx₀) AV.T mV.base tV hbtV hbV hTV hβV).functor)
    (FW := (fibreDataDerivedEquivalence (hx₀ := hx₀) AW.T mW.base tW hbtW hbW hTW hβW).functor)
    (c2V := fibreDataDerivedPullbackIso (hx₀ := hx₀) AV.T mV.base tV hbtV hbV hTV hβV
        (derivedExtensionOfScalarsData.{d, u + 1} (sqZeroExtSheafAnySiteProj
          ((coefficientModule (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)).obj V))))
    (c2W := fibreDataDerivedPullbackIso (hx₀ := hx₀) AW.T mW.base tW hbtW hbW hTW hβW
        (derivedExtensionOfScalarsData.{d, u + 1} (sqZeroExtSheafAnySiteProj
          ((coefficientModule (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)).obj W))))
    (χ := fibreDataPullbackNaturality f AV AW mW mV φ hb tV tW hbtV hbV hTV hβV hbtW hbW hTW hβW htφ
        hφ)
    ?_ ?_ ?_ ?_ ?_ (fibreDataStructureSheafIso_naturality f AV AW mW mV φ hb tV tW hbtV hbV hTV hβV
        hbtW hbW hTW hβW htφ hφ) ?_ ?_ ?_ ?_ ?_ ?_ K
  · exact fibreGenericModule_eq D iΛ x₀ hx₀ hk V
  · exact fibreGenericModule_eq D iΛ x₀ hx₀ hk W
  · exact fibreGenericDerivedCategory_heq hDV
  · exact fibreGenericDerivedCategory_heq hDW
  · exact fibreGenericRingMap_heq f
  · exact fibreDataDerivedEquivalence_functor_heq_V AV mV tV hbtV hbV hTV hβV
  · exact fibreDataDerivedEquivalence_functor_heq_W AW mW tW hbtW hbW hTW hβW
  · exact fibreDataDerivedPullbackIso_heq_generic_V AV mV tV hbtV hbV hTV hβV
  · exact fibreDataDerivedPullbackIso_heq_generic_W AW mW tW hbtW hbW hTW hβW
  · exact fibreDataPullbackNaturality_heq f AV AW mW mV φ hb tV tW hbtV hbV hTV hβV hbtW hbW hTW hβW
      htφ hφ


include hb htφ hφ in
/-- For `m_W ≫ φ = m_V`, the comparison `e : L_f K_V ≅ K_W`
(`AlgebraicGeometry.Space.ComplexesSituation.fibreDataPullbackComparison`) carries the
identification of the base change of the lift of `E₀` of `m_V` to that of `m_W`. -/
theorem fibreDataPullbackComparison_identification (hm : mW ≫ φ = mV) :
    (derivedExtensionOfScalarsData.{d, u + 1} (sqZeroExtSheafAnySiteProj
          ((coefficientModule (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)).obj W))).baseChange.map
        (fibreDataPullbackComparison f AV AW mW mV φ hb tV tW hbtV hbV hTV hβV hbtW hbW hTW hβW htφ
            hφ).hom ≫
      (fibreDataIdentification AW mW tW hbtW hbW hTW hβW
        (derivedExtensionOfScalarsData.{d, u + 1} (sqZeroExtSheafAnySiteProj
          ((coefficientModule (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)).obj W)))).hom =
    (derivedExtensionOfScalarsCompIso.{d, d, u + 1}
        (coefficientRingMap (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) f)
        (coefficientRingMap_comp_proj (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) f)).hom.app _ ≫
      (fibreDataIdentification AV mV tV hbtV hbV hTV hβV
        (derivedExtensionOfScalarsData.{d, u + 1} (sqZeroExtSheafAnySiteProj
          ((coefficientModule (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)).obj V)))).hom := by
  subst hm
  exact Functor.pullbackComparison_identification_eq_of_fibreComp _ _ _ _ _ _ _ _ _ _
    (fibreDataPullbackNaturality f AV AW mW (mW ≫ φ) φ hb tV tW hbtV hbV hTV hβV hbtW hbW hTW hβW
        htφ hφ)
    ((smallEtaleDerivedPullbackData B S hS).triangle
      (fibreData_relativeMap_comp AV AW mW (mW ≫ φ) φ hb))
    _ _ _ φ.fibre mW.fibre (D.compComparison mW.base φ.base) rfl _ (ComplexesHom.comp_fibre mW φ)
    (fibreDataPullbackComparison f AV AW mW (mW ≫ φ) φ hb tV tW hbtV hbV hTV hβV hbtW hbW hTW hβW
        htφ hφ).hom
    (fibreDataPullbackComparison_hom_map f AV AW mW (mW ≫ φ) φ hb tV tW hbtV hbV hTV hβV hbtW hbW
        hTW hβW htφ hφ)
    (fibreDataPullbackCoherence f AV AW mW (mW ≫ φ) φ hb tV tW hbtV hbV hTV hβV hbtW hbW hTW hβW htφ
        hφ _)

end Data

/-! ### At lifts of the base point of the fibre -/

section Fibre

/-- The retraction of a lift of `w₀` factors through the base map of a morphism to another lift
(over another square-zero extension) and the retraction of the target. -/
theorem fibreLiftRetraction_eq_comp_of_right {M M' : SiteModule k B}
    {y : FibreLift D iΛ x₀ hx₀ hk M} {y' : FibreLift D iΛ x₀ hx₀ hk M'}
        (ψ : y.1.right ⟶ y'.1.right) :
    ψ.a.base ≫ fibreLiftRetraction y' = fibreLiftRetraction y := by
  have hw : ψ.a.base ≫ y'.1.right.iso.hom.down =
      y.1.right.iso.hom.down ≫ ((schemePointToBase D.Y x₀.T.left x₀.T.hom).map ψ.b).down :=
    congrArg ULift.down ψ.w
  have hb : ((schemePointToBase D.Y x₀.T.left x₀.T.hom).map ψ.b).down ≫
      CostructuredArrow.homMk (overMapHom x₀.T.left y'.1.right.y) rfl =
        CostructuredArrow.homMk (overMapHom x₀.T.left y.1.right.y) rfl := by
    apply CostructuredArrow.hom_ext
    change (Over.map x₀.T.left.hom).map ψ.b ≫ overMapHom x₀.T.left y'.1.right.y =
      overMapHom x₀.T.left y.1.right.y
    exact Over.OverMorphism.ext (Over.w ψ.b)
  unfold fibreLiftRetraction
  exact (((congrArg (y.1.right.iso.hom.down ≫ ·) hb.symm).trans
    (Category.assoc _ _ _).symm).trans
    ((congrArg (· ≫ CostructuredArrow.homMk (overMapHom x₀.T.left y'.1.right.y) rfl)
      hw.symm).trans (Category.assoc _ _ _))).symm

/-- The base map of a morphism of lifts of `w₀` lying over `Spec k[W] ⟶ Spec k[V]` is that map,
up to the equalities of the underlying objects of the site. -/
theorem fibreLift_base_left_conj_of_isHomLift {V W : FGModuleCat.{u} k} (f : V ⟶ W)
    {a : FibreLift D iΛ x₀ hx₀ hk ((fgSiteModule B hk).obj V)}
    {b : FibreLift D iΛ x₀ hx₀ hk ((fgSiteModule B hk).obj W)} (φ : b.1.right ⟶ a.1.right)
    (hφ : (TwoFibreProductOver.structureFunctor (complexesFunctor D) (Over.map x₀.T.left.hom)
        (baseProj D.Y) (complexesToBaseObjects D)
        (schemePointToBase D.Y x₀.T.left x₀.T.hom)).IsHomLift
      (squareZeroOverMap k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)
        ((fgSiteModule B hk).map f)) φ) :
    eqToHom (fibreLiftScheme_left_eq b).symm ≫ φ.a.base.left ≫ eqToHom (fibreLiftScheme_left_eq a) =
      squareZeroOverMap k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)
        ((fgSiteModule B hk).map f) := by
  have e1 := IsHomLift.fac' (TwoFibreProductOver.structureFunctor (complexesFunctor D)
    (Over.map x₀.T.left.hom) (baseProj D.Y) (complexesToBaseObjects D)
    (schemePointToBase D.Y x₀.T.left x₀.T.hom))
    (squareZeroOverMap k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)
      ((fgSiteModule B hk).map f)) φ
  have h3 := φ.ha
  have e4 := IsHomLift.fac' (complexesFunctor D) φ.hbase φ.a
  change φ.hbase = _ at e1
  change φ.a.base.left = _ at e4
  exact eqToHom_conj_eq_of_eq_eqToHom_conj _ _ _ _ _ _ _ _ _ e4 e1

end Fibre

/-! ### Step 4 at lifts of `w₀` -/

section Pullback

variable [hDer : ∀ V : FGModuleCat.{u} k, HasDerivedCategory.{d} (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (coefficientRing (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) V)))]

/-- **Stacks 0DLL, step 4: the comparison of the lifts of `E₀` of a lift of `w₀` and of a
pullback of it** (`AlgebraicGeometry.Space.ComplexesSituation.FibreLiftAutPullback`): for a
morphism `φ : b ⟶ a` of lifts lying over `Spec k[W] ⟶ Spec k[V]`, the comparison `e`
(`AlgebraicGeometry.Space.ComplexesSituation.fibreDataPullbackComparison`) at the morphism of the
`Complexes_{X/Y}`-components of `φ` is an isomorphism of lifts of `E₀`
(`AlgebraicGeometry.Space.ComplexesSituation.fibreDataPullbackComparison_identification`) and
carries automorphisms compatibly with `φ`
(`AlgebraicGeometry.Space.ComplexesSituation.fibreDataPullbackComparison_aut`). -/
theorem fibreLiftAutPullback (hK : DerivedCategory.TStructure.t.minus x₀.E) :
    FibreLiftAutPullback (hDer := hDer) hK := by
  intro V W f a b φ hφ hw
  have hm : b.1.hom.a ≫ φ.a = a.1.hom.a :=
    (TwoFibreProductOver.comp_a _ _).symm.trans (congrArg TwoFibreProductOver.Hom.a hw)
  have hb : b.1.hom.a.base ≫ φ.a.base = a.1.hom.a.base := congrArg (fun m => m.base) hm
  refine ⟨fibreDataPullbackComparison (hDV := hDer V) (hDW := hDer W) f a.1.right.x b.1.right.x
      b.1.hom.a a.1.hom.a φ.a hb
      (fibreLiftRetraction a) (fibreLiftRetraction b) (fibreLiftSection_comp_retraction a)
      (isSquareZeroClosedImmersion_fibreLiftSection a) (fibreLiftScheme_left_eq a)
      (fibreLiftSection_conj a) (fibreLiftSection_comp_retraction b)
      (isSquareZeroClosedImmersion_fibreLiftSection b) (fibreLiftScheme_left_eq b)
      (fibreLiftSection_conj b) (fibreLiftRetraction_eq_comp_of_right φ)
      (fibreLift_base_left_conj_of_isHomLift f φ hφ), ?_, ?_⟩
  · apply fibreDataPullbackComparison_identification (hDV := hDer V) (hDW := hDer W) (hm := hm)
  · apply fibreDataPullbackComparison_aut (hDV := hDer V) (hDW := hDer W) (hK := hK)

/-- **Stacks 0DLL: the compatibility of the classes of lifts of `E₀⟦m⟧` with pullback of lifts of
`w₀`** (`AlgebraicGeometry.Space.ComplexesSituation.FibreLiftClassPullback`): a pullback
`φ : b' ⟶ a'` of representatives gives isomorphic lifts of `E₀`
(`AlgebraicGeometry.Space.ComplexesSituation.fibreLiftAutPullback`), and the lifts of `E₀` of
isomorphic lifts of `w₀` are isomorphic
(`AlgebraicGeometry.Space.ComplexesSituation.fibreLiftDerivedLift_isomorphic`). -/
theorem fibreLiftClassPullback (hK : DerivedCategory.TStructure.t.minus x₀.E) (m : ℤ)
    (hKm : DerivedCategory.TStructure.t.minus (x₀.E⟦m⟧)) :
    FibreLiftClassPullback (hDer := hDer) hK m hKm := by
  intro V W f a b hab
  refine fibreLiftClass_eq_liftClassMap_of_isomorphic hK m hKm f a b ?_
  obtain ⟨a', b', ha, hb, φ, hcart, hw⟩ := hab
  obtain ⟨ea⟩ := Quotient.exact ((Quotient.out_eq a).trans ha.symm)
  obtain ⟨eb⟩ := Quotient.exact (hb.trans (Quotient.out_eq b).symm)
  exact ((DerivedLift.Isomorphic.baseChange _
    (fibreLiftDerivedLift_isomorphic (hDer := hDer V) ea.hom hK)).trans
      (FibreLiftAutPullback.isomorphic (fibreLiftAutPullback hK) f a' b' φ hcart.toIsHomLift
        hw)).trans (fibreLiftDerivedLift_isomorphic (hDer := hDer W) eb.hom hK)

end Pullback

end ComplexesSituation

end AlgebraicGeometry.Space

end
