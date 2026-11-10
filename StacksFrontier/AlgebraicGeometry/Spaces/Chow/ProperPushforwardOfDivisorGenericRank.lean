module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GenericFibreFieldPushout
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardPrincipalDivisorChart
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardOfDivisorChart

/-!
# The generic rank of the chart of a proper dominant morphism

Let `f : X ⟶ Y` be a proper dominant morphism of integral good algebraic spaces with
`dim_δ(X) = dim_δ(Y)`, and let `d` be a cartesian square of affine étale charts of `f` with `U → V`
finite. At every minimal prime `𝔭` of `A = Γ(V, 𝒪_V)` the ring `B = Γ(U, 𝒪_U)` has length
`[R(X) : R(Y)]` over the field `A_𝔭`. The fibre `G = U ×_V Spec κ(w)` at the point `w` of `𝔭` has
ring `B ⊗_A κ(w) = B_𝔭`, and it is also `R(X) ⊗_{R(Y)} κ(w)` by the generic fibre square of
`f` (`AlgebraicGeometry.Space.exists_isPullback_chartFibre`).
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open scoped nonZeroDivisors TensorProduct

universe u

/-! ### Pure algebra -/

namespace Stacks.Length

/-- In a cocartesian square of rings `K → F`, `K → L`, `F → T`, `L → T` with `K` and `F` fields,
`T` has the rank of `L` over `F`, and is finite over `F` if `L` is finite over `K`. -/
private theorem finite_and_finrank_eq_of_isPushout_ofHom {K F L T : Type u} [Field K] [Field F]
    [CommRing L] [CommRing T] (φ : K →+* F) (ψ : K →+* L) (β : F →+* T) (α : L →+* T)
    (h : IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom ψ) (CommRingCat.ofHom β)
      (CommRingCat.ofHom α)) :
    letI : Algebra K L := ψ.toAlgebra
    letI : Algebra F T := β.toAlgebra
    (Module.Finite K L → Module.Finite F T) ∧ Module.finrank F T = Module.finrank K L := by
  let : Algebra K F := φ.toAlgebra
  let : Algebra K L := ψ.toAlgebra
  let : Algebra F T := β.toAlgebra
  let : Algebra L T := α.toAlgebra
  let : Algebra K T := (β.comp φ).toAlgebra
  have : IsScalarTower K F T := .of_algebraMap_eq' rfl
  have : IsScalarTower K L T := .of_algebraMap_eq'
    (AlgebraicGeometry.hom_comp_eq_of_isPushout_ofHom φ ψ β α h)
  have hp : Algebra.IsPushout K F L T :=
    AlgebraicGeometry.algebraIsPushout_of_isPushout_ofHom φ ψ β α h
  exact ⟨fun _ => Module.Finite.equiv hp.out.equiv,
    by rw [← (hp.out.equiv).finrank_eq, Module.finrank_baseChange]⟩

/-- **The rank of a base change of fields.** In a cocartesian square of commutative rings
`K → F`, `K → L`, `F → T`, `L → T` with `K` and `F` fields, `T` has rank `[L : K]` over `F`. -/
theorem finrank_eq_of_isPushout_ofHom {K F L T : Type u} [Field K] [Field F] [CommRing L]
    [CommRing T] (φ : K →+* F) (ψ : K →+* L) (β : F →+* T) (α : L →+* T)
    (h : IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom ψ) (CommRingCat.ofHom β)
      (CommRingCat.ofHom α)) :
    letI : Algebra K L := ψ.toAlgebra
    letI : Algebra F T := β.toAlgebra
    Module.finrank F T = Module.finrank K L :=
  (finite_and_finrank_eq_of_isPushout_ofHom φ ψ β α h).2

/-- The length of a finite algebra over a field, for the algebra structure of a ring map, is its
rank. -/
theorem length_eq_finrank_of_ringHom {F T : Type u} [Field F] [CommRing T] (β : F →+* T)
    (hfin : letI : Algebra F T := β.toAlgebra
      Module.Finite F T) :
    letI : Algebra F T := β.toAlgebra
    Module.length F T = Module.finrank F T := by
  let : Algebra F T := β.toAlgebra
  have := hfin
  exact Module.length_eq_finrank F T

/-- **A base change of fields of a finite extension is finite.** -/
theorem finite_of_isPushout_ofHom {K F L T : Type u} [Field K] [Field F] [CommRing L]
    [CommRing T] (φ : K →+* F) (ψ : K →+* L) (β : F →+* T) (α : L →+* T)
    (h : IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom ψ) (CommRingCat.ofHom β)
      (CommRingCat.ofHom α))
    (hfin : letI : Algebra K L := ψ.toAlgebra
      Module.Finite K L) :
    letI : Algebra F T := β.toAlgebra
    Module.Finite F T :=
  (finite_and_finrank_eq_of_isPushout_ofHom φ ψ β α h).1 hfin

/-- **A cocartesian square of rings with a localization at a prime as a corner computes the
length of the localization of the other corner.** Let `A → B`, `A → K`, `B → T`, `K → T` be a
cocartesian square with `K` a localization of `A` at a prime `𝔭` which is a field. Then
`length_{A_𝔭}(B_𝔭) = length_K(T)`. -/
theorem length_localizedModule_eq_length_of_isPushout_ofHom {A B K T : Type u} [CommRing A]
    [CommRing B] [CommRing K] [CommRing T] (φ : A →+* B) (ψ : A →+* K) (β : B →+* T)
    (α : K →+* T)
    (h : IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom ψ) (CommRingCat.ofHom β)
      (CommRingCat.ofHom α)) (P : Ideal A) [P.IsPrime]
    (hloc : letI : Algebra A K := ψ.toAlgebra
      IsLocalization.AtPrime K P) :
    letI : Algebra A B := φ.toAlgebra
    letI : Algebra K T := α.toAlgebra
    Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl B) =
      Module.length K T := by
  let : Algebra A B := φ.toAlgebra
  let : Algebra A K := ψ.toAlgebra
  let : Algebra B T := β.toAlgebra
  let : Algebra K T := α.toAlgebra
  let : Algebra A T := (α.comp ψ).toAlgebra
  have : IsScalarTower A K T := .of_algebraMap_eq' rfl
  have : IsScalarTower A B T := .of_algebraMap_eq'
    (AlgebraicGeometry.hom_comp_eq_of_isPushout_ofHom φ ψ β α h).symm
  have hp : Algebra.IsPushout A K B T :=
    AlgebraicGeometry.algebraIsPushout_of_isPushout_ofHom ψ φ α β h.flip
  have := hloc
  have : IsLocalizedModule P.primeCompl (IsScalarTower.toAlgHom A B T).toLinearMap :=
    (isLocalizedModule_iff_isBaseChange P.primeCompl K _).mpr hp.out
  exact Module.length_eq_of_isLocalization_of_isLocalizedModule P.primeCompl K
    (IsScalarTower.toAlgHom A B T).toLinearMap

end Stacks.Length

namespace AlgebraicGeometry

/-- **The ring map of the canonical point `Spec κ(x) ⟶ X`** on global sections is the germ at
`x` followed by the residue map. -/
theorem Scheme.fromSpecResidueField_appTop_comp_ΓSpecIso_hom (X : Scheme.{u}) (x : X) :
    (X.fromSpecResidueField x).appTop ≫ (Scheme.ΓSpecIso (X.residueField x)).hom =
      X.presheaf.germ ⊤ x trivial ≫ X.residue x := by
  simp only [Scheme.fromSpecResidueField, Scheme.fromSpecStalk_appTop, Scheme.Hom.comp_appTop,
    Category.assoc]
  rw [Scheme.ΓSpecIso_naturality]
  simp

namespace Space

attribute [local instance] pointTopology

section GenericRank

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (hintX : IsIntegralSpace D.site D.base D.base_mem X)
    (hintY : IsIntegralSpace D.site D.base D.base_mem Y)

/-- At a generic point `w` of an affine chart of an integral algebraic space, the residue field
`κ(w)` is the localization of the ring of the chart at the prime of `w`, for the algebra
structure of the canonical point `Spec κ(w) ⟶ V`. -/
theorem isLocalization_residueField_chartPrimeAt (Z : AlgebraicSpaces D.site D.base D.base_mem)
    (hZint : IsIntegralSpace D.site D.base D.base_mem Z.1)
    (V : SmallEtale D.site D.base D.base_mem Z.1) (hV : IsAffine (chartScheme V))
    (w : chartScheme V) (hw : w ∈ genericPoints (chartScheme V)) :
    letI : Algebra (chartRing D.site D.base D.base_mem Z.1 Z.2 V)
        ((chartScheme V).residueField w) :=
      (((chartScheme V).presheaf.germ ⊤ w trivial) ≫ (chartScheme V).residue w).hom.toAlgebra
    IsLocalization.AtPrime ((chartScheme V).residueField w)
      (chartPrimeAt D.site D.base D.base_mem Z.2 V w) := by
  let : Algebra (chartRing D.site D.base D.base_mem Z.1 Z.2 V)
      ((chartScheme V).residueField w) :=
    (((chartScheme V).presheaf.germ ⊤ w trivial) ≫ (chartScheme V).residue w).hom.toAlgebra
  let := (chartGermHom D.site D.base D.base_mem Z.2 V w).toAlgebra
  have := isLocalization_stalk_chartPrimeAt D.site D.base D.base_mem Z.2 V hV w
  have hred : IsReduced (chartScheme V) :=
    (exists_atlas_iff_forall_etale D.site D.base D.base_mem Z.1 (fun T : Scheme.{u} => IsReduced T)
      Z.2).mp (IsIntegralSpace.hasEtaleLocalProperty_isReduced D.site D.base D.base_mem Z.1 hZint)
      V.obj.left V.obj.hom V.property
  have : Ring.KrullDimLE 0 ((chartScheme V).presheaf.stalk w) :=
    Ring.krullDimLE_iff.mpr (le_of_eq
      ((ringKrullDim_stalk_eq_zero_iff_mem_genericPoints _ _).mpr hw))
  have hfield : IsField ((chartScheme V).presheaf.stalk w) := Ring.KrullDimLE.isField_of_isReduced
  have hbij : Function.Bijective ((chartScheme V).residue w).hom := by
    refine ⟨fun a b hab => ?_, Ideal.Quotient.mk_surjective⟩
    have h0 : a - b ∈ IsLocalRing.maximalIdeal ((chartScheme V).presheaf.stalk w) := by
      rw [← IsLocalRing.residue_eq_zero_iff]
      change ((chartScheme V).residue w).hom (a - b) = 0
      rw [map_sub, hab, sub_self]
    have hmax : IsLocalRing.maximalIdeal ((chartScheme V).presheaf.stalk w) = ⊥ := by
      let := hfield.toField
      exact IsLocalRing.maximalIdeal_eq_bot
    rw [hmax, Ideal.mem_bot, sub_eq_zero] at h0
    exact h0
  let e : (chartScheme V).presheaf.stalk w ≃ₐ[chartRing D.site D.base D.base_mem Z.1 Z.2 V]
      (chartScheme V).residueField w :=
    { RingEquiv.ofBijective ((chartScheme V).residue w).hom hbij with
      commutes' := fun _ => rfl }
  exact IsLocalization.isLocalization_of_algEquiv
    (chartPrimeAt D.site D.base D.base_mem Z.2 V w).primeCompl e


include hintX hintY in
/-- **The generic rank of the chart of a proper dominant morphism.** Let `f : X ⟶ Y` be proper,
carrying the generic point to the generic point, between integral good algebraic spaces of the same
δ-dimension, and let `d` be a cartesian square of affine étale charts of `f`. Then at every minimal
prime `𝔭` of `A = Γ(V, 𝒪_V)`,

`length_{A_𝔭}(B_𝔭) = [R(X) : R(Y)] · length_{A_𝔭}(A_𝔭)`, `B = Γ(U, 𝒪_U)`. -/
theorem length_localizedModule_chartRing_eq_functionFieldDegree_mul {f : X ⟶ Y}
    (hfB : f ≫ sY = sX) (hf : IsProper D.site D.base D.base_mem f)
    (hdom : IsDominant D.site D.base D.base_mem f)
    (hdim : deltaDimensionClosed D sX hX Set.univ isClosed_univ =
      deltaDimensionClosed D sY hY Set.univ isClosed_univ)
    (d : ChartDiagram D.site D.base D.base_mem X Y f)
    (hd : IsPullback d.U.1.hom (yoneda.map d.g) f d.V.1.hom)
    (hU : IsAffine (chartScheme d.U)) (hV : IsAffine (chartScheme d.V))
    (P : PrimeSpectrum (chartRing D.site D.base D.base_mem Y hY.1 d.V))
    (hP : P.asIdeal ∈ minimalPrimes (chartRing D.site D.base D.base_mem Y hY.1 d.V)) :
    letI := (chartDiagramRestrict D.site D.base D.base_mem
      (X := ⟨X, hX.1⟩) (Y := ⟨Y, hY.1⟩) ⟨f⟩ d).toAlgebra
    Module.length (Localization.AtPrime P.asIdeal)
        (LocalizedModule P.asIdeal.primeCompl (chartRing D.site D.base D.base_mem X hX.1 d.U)) =
      (functionFieldDegreeAtGenericPoint D sX hX sY hY hintX f : ℕ∞) *
        Module.length (Localization.AtPrime P.asIdeal)
          (LocalizedModule P.asIdeal.primeCompl
            (chartRing D.site D.base D.base_mem Y hY.1 d.V)) := by
  classical
  have hgen := pointsMap_genericPoint_of_isDominant D.site D.base D.base_mem hX.1 hY.1 hintX hintY
    f hdom
  -- the point `w` of `P`, a generic point of `V` over the generic point of `Y`
  obtain ⟨w, hwP⟩ := (bijective_chartPrimeAt D.site D.base D.base_mem hY.1 d.V hV).2 P
  subst hwP
  have : (chartPrimeAt D.site D.base D.base_mem hY.1 d.V w).IsPrime := inferInstance
  have hwgen : w ∈ genericPoints (chartScheme d.V) :=
    (chartPrimeAt_mem_minimalPrimes_iff D.site D.base D.base_mem hY.1 d.V hV w).mp hP
  have hw : chartSchemeToPoints D.site D.base D.base_mem Y d.V w =
      pointsMap D.site D.base D.base_mem X f
        (genericPoint D.site D.base D.base_mem hX.1 hintX) := by
    rw [hgen]
    exact (chartSchemeToPoints_eq_genericPoint_iff D.site D.base D.base_mem hY.1 hintY d.V w).mpr
      hwgen
  -- the generic fibre square
  obtain ⟨g0, fp, r, h1, -, -, hsq⟩ := exists_isPullback_chartFibre D sX hX sY hY hintX hintY d hfB
    hf hgen hdim hd w hw
  have hg0 := eq_specMap_residueFieldHom D.site D.base D.base_mem hY.1 hintX.2.1 hintY.2.1 f _ h1
  obtain ⟨φ₀, hφ₀⟩ := exists_eq_specMap_of_hom_siteObject D.site D.base D.base_mem fp
  have h0 := (IsPullback.of_map_of_faithful yoneda hsq).map (BigFppfOver.toScheme D.site D.base
    D.base_mem)
  rw [show (BigFppfOver.toScheme D.site D.base D.base_mem).map g0 = _ from hg0,
    show (BigFppfOver.toScheme D.site D.base D.base_mem).map fp = _ from hφ₀] at h0
  have hpush₁ := isPushout_of_isPullback_specMap φ₀ _ h0
  have hrank₁ := Stacks.Length.finrank_eq_of_isPushout_ofHom φ₀ _ _ _ hpush₁
  have hfin₁ := Stacks.Length.finite_of_isPushout_ofHom φ₀ _ _ _ hpush₁
    (finite_residueFieldHom_genericPoint_of_hasTranscendenceDegreeAt_zero D.site D.base D.base_mem
      hX.1 hY.1 hintX hintY f hf.2.1.1 hdom
      (hasTranscendenceDegreeAt_genericPoint_eq_zero D sX sY hX hY hintX hintY f hfB hgen hdim))
  -- the fibre of the chart over `w`
  have : IsAffine ((BigFppfOver.toScheme D.site D.base D.base_mem).obj
      ((SmallEtale.toOver D.site D.base D.base_mem X).obj d.U)) := hU
  have : IsAffine ((BigFppfOver.toScheme D.site D.base D.base_mem).obj
      ((SmallEtale.toOver D.site D.base D.base_mem Y).obj d.V)) := hV
  have hpb₂ := (IsPullback.of_hasPullback d.g (fibreChartFieldPoint D d w).siteHom).map yoneda
  have hpush₂ := isPushout_appTop_of_isPullback_yoneda_fieldValuedPoint D.site D.base D.base_mem
    hpb₂
  have hψeq : (BigFppfOver.toScheme D.site D.base D.base_mem).map
      (fibreChartFieldPoint D d w).siteHom =
      (chartScheme d.V).fromSpecResidueField w :=
    map_siteFieldPointOfSchemeMap_value_left D.site D.base D.base_mem _ _ _
  set ψ : chartRing D.site D.base D.base_mem Y hY.1 d.V →+* (fibreChartFieldPoint D d w).carrier :=
    (((BigFppfOver.toScheme D.site D.base D.base_mem).map
      (fibreChartFieldPoint D d w).siteHom).appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of (fibreChartFieldPoint D d w).carrier)).hom).hom with hψ
  have hψ' :
      ψ = ((chartScheme d.V).presheaf.germ ⊤ w trivial ≫ (chartScheme d.V).residue w).hom := by
    rw [hψ]
    refine congrArg CommRingCat.Hom.hom ?_
    refine (congrArg (fun g => Scheme.Hom.appTop g ≫
      (Scheme.ΓSpecIso (CommRingCat.of (fibreChartFieldPoint D d w).carrier)).hom) hψeq).trans ?_
    exact Scheme.fromSpecResidueField_appTop_comp_ΓSpecIso_hom _ _
  let : Algebra (chartRing D.site D.base D.base_mem Y hY.1 d.V)
      (fibreChartFieldPoint D d w).carrier :=
    ψ.toAlgebra
  have hloc : IsLocalization.AtPrime (fibreChartFieldPoint D d w).carrier
      (chartPrimeAt D.site D.base D.base_mem hY.1 d.V w) := by
    have h := isLocalization_residueField_chartPrimeAt D ⟨Y, hY.1⟩ hintY d.V hV w hwgen
    let : Algebra (chartRing D.site D.base D.base_mem Y hY.1 d.V)
        ((chartScheme d.V).residueField w) :=
      (((chartScheme d.V).presheaf.germ ⊤ w trivial) ≫ (chartScheme d.V).residue w).hom.toAlgebra
    let e : (chartScheme d.V).residueField w ≃ₐ[chartRing D.site D.base D.base_mem Y hY.1 d.V]
        (fibreChartFieldPoint D d w).carrier :=
      { RingEquiv.refl _ with
        commutes' := fun a => (RingHom.congr_fun hψ' a).symm }
    exact IsLocalization.isLocalization_of_algEquiv
      (chartPrimeAt D.site D.base D.base_mem hY.1 d.V w).primeCompl e
  have hlen := Stacks.Length.length_localizedModule_eq_length_of_isPushout_ofHom
    (A := chartRing D.site D.base D.base_mem Y hY.1 d.V)
    (B := chartRing D.site D.base D.base_mem X hX.1 d.U)
    (K := (fibreChartFieldPoint D d w).carrier)
    (T := Γ((BigFppfOver.toScheme D.site D.base D.base_mem).obj (chartGenericFibre D d w), ⊤))
    ((BigFppfOver.toScheme D.site D.base D.base_mem).map d.g).appTop.hom ψ _ _ hpush₂
    (chartPrimeAt D.site D.base D.base_mem hY.1 d.V w) hloc
  have hone :
      Module.length (Localization.AtPrime (chartPrimeAt D.site D.base D.base_mem hY.1 d.V w))
        (LocalizedModule (chartPrimeAt D.site D.base D.base_mem hY.1 d.V w).primeCompl
          (chartRing D.site D.base D.base_mem Y hY.1 d.V)) = 1 := by
    rw [Module.length_eq_of_isLocalization_of_isLocalizedModule
      (chartPrimeAt D.site D.base D.base_mem hY.1 d.V w).primeCompl
      (fibreChartFieldPoint D d w).carrier
      (Algebra.linearMap (chartRing D.site D.base D.base_mem Y hY.1 d.V)
        (fibreChartFieldPoint D d w).carrier), Module.length_eq_finrank, Module.finrank_self]
    rfl
  change _ = _ *
    Module.length (Localization.AtPrime (chartPrimeAt D.site D.base D.base_mem hY.1 d.V w))
      (LocalizedModule (chartPrimeAt D.site D.base D.base_mem hY.1 d.V w).primeCompl
        (chartRing D.site D.base D.base_mem Y hY.1 d.V))
  rw [hone, mul_one]
  refine hlen.trans ?_
  refine (Stacks.Length.length_eq_finrank_of_ringHom _ hfin₁).trans ?_
  exact_mod_cast hrank₁.trans
    (functionFieldDegreeAtGenericPoint_eq_finrank D sX hX sY hY hintX f).symm

end GenericRank

end Space

end AlgebraicGeometry

end
