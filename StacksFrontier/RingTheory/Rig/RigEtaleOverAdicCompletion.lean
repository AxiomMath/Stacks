module

public import StacksFrontier.RingTheory.Rig.RigEtaleTFAE
public import StacksFrontier.RingTheory.Rig.RigSmooth

/-!
# Rig-étaleness over a Noetherian ring and over its completion

Let `R` be a Noetherian ring, `I ⊆ R` an ideal and `A = R^∧` the `I`-adic completion of `R`.
An `A`-algebra `C` which is `IC`-adically complete with `C ⧸ IC` of finite type over `A ⧸ IA` is
then also an object of the category of Stacks 0AL4 over `(R, I)`, because `R ⧸ I ≅ A ⧸ IA`.
This file shows that rig-étaleness over `(A, IA)` implies rig-étaleness over `(R, I)`.

## Main results

* `Rig.isRigEtale_of_isRigEtale_adicCompletion`: rig-étaleness over `(R^∧, IR^∧)` implies
  rig-étaleness over `(R, I)`.
* `Rig.isRigEtaleOver_comp_algebraMap_of_isRigEtaleOver`: the same statement for an algebra given
  by a ring homomorphism `R^∧ → C`, completeness and the finite-type condition included.

## References

* [Stacks Project, Tag 0AJU](https://stacks.math.columbia.edu/tag/0AJU)
* [Stacks Project, Tag 0AKG](https://stacks.math.columbia.edu/tag/0AKG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Rig

universe u

open Algebra in
/-- The naive cotangent complex of `C` over `R` is isomorphic to that over `R'`, for a ring
isomorphism `e : R ≃+* R'` compatible with the two structure maps into `C`. -/
private def naiveCotangentComplexIsoOfRingEquiv
    {R R' C : Type u} [CommRing R] [CommRing R'] [CommRing C]
    [Algebra R C] [Algebra R' C] (e : R ≃+* R')
    (he : ∀ r, algebraMap R' C (e r) = algebraMap R C r) :
    Algebra.naiveCotangentComplex R C ≅ Algebra.naiveCotangentComplex R' C := by
  letI : Algebra R R' := e.toRingHom.toAlgebra
  letI : Algebra R' R := e.symm.toRingHom.toAlgebra
  letI : IsScalarTower R R' C := IsScalarTower.of_algebraMap_eq fun r ↦ (he r).symm
  letI : IsScalarTower R' R C := IsScalarTower.of_algebraMap_eq fun r ↦ by
    change algebraMap R' C r = algebraMap R C (e.symm r)
    simpa only [e.apply_symm_apply] using he (e.symm r)
  letI : IsScalarTower R R' R := IsScalarTower.of_algebraMap_eq fun r ↦
    (e.symm_apply_apply r).symm
  letI : IsScalarTower R' R R' := IsScalarTower.of_algebraMap_eq fun r ↦
    (e.apply_symm_apply r).symm
  let P := Generators.self R C
  let Q := Generators.self R' C
  let f : P.Hom Q := P.defaultHom Q
  let g : Q.Hom P := Q.defaultHom P
  have hgf : g.comp f = Generators.Hom.id P := by
    ext x
    simp [f, g, P, Q, Generators.defaultHom, Generators.Hom.comp,
      Generators.self, Generators.σ]
  have hfg : f.comp g = Generators.Hom.id Q := by
    ext x
    simp [f, g, P, Q, Generators.defaultHom, Generators.Hom.comp,
      Generators.self, Generators.σ]
  let F := NaiveCotangent.nlMapBase C P Q f
  let G := NaiveCotangent.nlMapBase C Q P g
  have hGF : G.comp F = NaiveCotangent.ChainMap.id (NaiveCotangent.nlRestrict C P) := by
    rw [NaiveCotangent.nlMapBase_comp, hgf, NaiveCotangent.nlMapBase_id]
  have hFG : F.comp G = NaiveCotangent.ChainMap.id (NaiveCotangent.nlRestrict C Q) := by
    rw [NaiveCotangent.nlMapBase_comp, hfg, NaiveCotangent.nlMapBase_id]
  let e₁ : P.toExtension.Cotangent ≃ₗ[C] Q.toExtension.Cotangent :=
    { F.f₁ with
      invFun := G.f₁
      left_inv := fun x ↦ LinearMap.congr_fun (congrArg (·.f₁) hGF) x
      right_inv := fun x ↦ LinearMap.congr_fun (congrArg (·.f₁) hFG) x }
  let e₀ : P.toExtension.CotangentSpace ≃ₗ[C] Q.toExtension.CotangentSpace :=
    { F.f₀ with
      invFun := G.f₀
      left_inv := fun x ↦ LinearMap.congr_fun (congrArg (·.f₀) hGF) x
      right_inv := fun x ↦ LinearMap.congr_fun (congrArg (·.f₀) hFG) x }
  let dP := ModuleCat.ofHom P.toExtension.cotangentComplex
  let dQ := ModuleCat.ofHom Q.toExtension.cotangentComplex
  let rel : (ComplexShape.down ℕ).Rel 1 0 := rfl
  let eq₁ := HomologicalComplex.doubleXIso₀ dQ rel
  let eq₀ := HomologicalComplex.doubleXIso₁ dQ rel (by decide)
  let iso₁ := LinearEquiv.toModuleIso e₁
  let iso₀ := LinearEquiv.toModuleIso e₀
  let φ := HomologicalComplex.mkHomFromDouble (f := dP) rel (by decide)
    (iso₁.hom ≫ eq₁.inv) (iso₀.hom ≫ eq₀.inv)
    (by
      rw [HomologicalComplex.double_d dQ rel (by decide)]
      change (iso₁.hom ≫ eq₁.inv) ≫ eq₁.hom ≫ dQ ≫ eq₀.inv = dP ≫ iso₀.hom ≫ eq₀.inv
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [← Category.assoc, ← Category.assoc]
      exact congrArg (· ≫ eq₀.inv) <| ModuleCat.hom_ext <|
        LinearMap.ext fun x ↦ LinearMap.congr_fun F.comm x)
    (by intro k hk; simp at hk)
  haveI : ∀ n, IsIso (φ.f n) := by
    rintro (_ | _ | n)
    · dsimp [φ]
      rw [HomologicalComplex.mkHomFromDouble_f₁]
      infer_instance
    · dsimp [φ]
      rw [HomologicalComplex.mkHomFromDouble_f₀]
      infer_instance
    · exact IsZero.isIso (HomologicalComplex.isZero_double_X dP rel _ (by omega) (by omega))
        (HomologicalComplex.isZero_double_X dQ rel _ (by omega) (by omega)) (φ.f (n + 2))
  exact @asIso _ _ _ _ φ (HomologicalComplex.Hom.isIso_of_components φ)

/-- Annihilators of the homology of the naive cotangent complex do not change when the base ring
is replaced by an isomorphic one compatibly with the structure maps. -/
private theorem annihilator_homology_naiveCotangentComplex_eq_of_ringEquiv
    {R R' C : Type u} [CommRing R] [CommRing R'] [CommRing C]
    [Algebra R C] [Algebra R' C] (e : R ≃+* R')
    (he : ∀ r, algebraMap R' C (e r) = algebraMap R C r) (n : ℕ) :
    Module.annihilator C ((Algebra.naiveCotangentComplex R C).homology n) =
      Module.annihilator C ((Algebra.naiveCotangentComplex R' C).homology n) :=
  ((HomologicalComplex.homologyFunctor
    (ModuleCat C) (ComplexShape.down ℕ) n).mapIso
      (naiveCotangentComplexIsoOfRingEquiv e he)).toLinearEquiv.annihilator_eq

/-- Over a base change `R → A → C` whose ideals agree, `J = IA`, and with `R ⧸ I ≅ A ⧸ J`, an
element of `R` annihilates the homology of `NL_{(C/IC)/(R/I)}` exactly when its image in `A`
annihilates that of `NL_{(C/JC)/(A/J)}`. -/
private theorem mem_annihilator_homology_quotient_iff
    {R A C : Type u} [CommRing R] [CommRing A] [CommRing C]
    [Algebra R A] [Algebra A C] [Algebra R C] [IsScalarTower R A C]
    (I : Ideal R) (J : Ideal A) (hJ : J = I.map (algebraMap R A))
    (hbij : Function.Bijective (Ideal.quotientMap J (algebraMap R A)
      (hJ ▸ Ideal.le_comap_map))) (n : ℕ) (a : R) :
    (Ideal.Quotient.mk _ (algebraMap R C a) ∈
      Module.annihilator (C ⧸ I.map (algebraMap R C))
        ((Algebra.naiveCotangentComplex (R ⧸ I)
          (C ⧸ I.map (algebraMap R C))).homology n)) ↔
    (Ideal.Quotient.mk _ (algebraMap A C (algebraMap R A a)) ∈
      Module.annihilator (C ⧸ J.map (algebraMap A C))
        ((Algebra.naiveCotangentComplex (A ⧸ J)
          (C ⧸ J.map (algebraMap A C))).homology n)) := by
  let K := I.map (algebraMap R C)
  have hK : J.map (algebraMap A C) = K := by
    rw [hJ, Ideal.map_map, ← IsScalarTower.algebraMap_eq R A C]
  let : Algebra (A ⧸ J) (C ⧸ K) :=
    Ideal.Quotient.algebraQuotientOfLEComap (hK ▸ Ideal.le_comap_map)
  let e : (R ⧸ I) ≃+* (A ⧸ J) := RingEquiv.ofBijective
    (Ideal.quotientMap J (algebraMap R A) (hJ ▸ Ideal.le_comap_map)) hbij
  have he (r : R ⧸ I) : algebraMap (A ⧸ J) (C ⧸ K) (e r) =
      algebraMap (R ⧸ I) (C ⧸ K) r := by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    change Ideal.Quotient.mk K (algebraMap A C (algebraMap R A r)) =
      Ideal.Quotient.mk K (algebraMap R C r)
    rw [← IsScalarTower.algebraMap_apply R A C]
  have h := annihilator_homology_naiveCotangentComplex_eq_of_ringEquiv e he n
  have hsameAux (K' : Ideal C) (hK' : J.map (algebraMap A C) = K') :
      let : Algebra (A ⧸ J) (C ⧸ K') :=
        Ideal.Quotient.algebraQuotientOfLEComap (hK' ▸ Ideal.le_comap_map)
      (Ideal.Quotient.mk K' (algebraMap R C a) ∈
        Module.annihilator (C ⧸ K')
          ((Algebra.naiveCotangentComplex (A ⧸ J) (C ⧸ K')).homology n)) ↔
      (Ideal.Quotient.mk _ (algebraMap A C (algebraMap R A a)) ∈
        Module.annihilator (C ⧸ J.map (algebraMap A C))
          ((Algebra.naiveCotangentComplex (A ⧸ J)
            (C ⧸ J.map (algebraMap A C))).homology n)) := by
    subst K'
    rw [IsScalarTower.algebraMap_apply R A C]
  exact (Iff.of_eq (congrArg (fun L : Ideal (C ⧸ K) ↦
    Ideal.Quotient.mk K (algebraMap R C a) ∈ L) h)).trans (hsameAux K hK)

/-- If `A → R ⧸ K` is a surjective `R`-algebra map whose kernel is `KA`, then `R ⧸ K → A ⧸ KA` is
bijective. -/
private theorem bijective_quotientMap_of_ker_eq {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (K : Ideal R) (f : A →ₐ[R] R ⧸ K) (hf : Function.Surjective f)
    (hker : RingHom.ker f.toRingHom = K.map (algebraMap R A)) :
    Function.Bijective (Ideal.quotientMap (K.map (algebraMap R A)) (algebraMap R A)
      Ideal.le_comap_map) := by
  let q := Ideal.quotientMap (K.map (algebraMap R A)) (algebraMap R A) Ideal.le_comap_map
  let e := (Ideal.quotientEquivAlgOfEq R hker.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective hf)
  have he (x : R ⧸ K) : e (q x) = x := by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact f.commutes r
  exact ⟨fun x y h ↦ (he x).symm.trans ((congrArg e h).trans (he y)),
    fun y ↦ ⟨e y, e.injective (he _)⟩⟩

/-- For a finitely generated ideal `I`, the map `R ⧸ Iⁿ → R^∧ ⧸ IⁿR^∧` is bijective. -/
private theorem bijective_quotientMap_pow_adicCompletion
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG) (n : ℕ) :
    Function.Bijective (Ideal.quotientMap ((I ^ n).map
      (algebraMap R (AdicCompletion I R)))
      (algebraMap R (AdicCompletion I R)) Ideal.le_comap_map) := by
  have hker : RingHom.ker (AdicCompletion.evalₐ I n).toRingHom =
      (I ^ n).map (algebraMap R (AdicCompletion I R)) := by
    ext x
    have he : (AdicCompletion.evalₐ I n x = 0) ↔ AdicCompletion.eval I R n x = 0 := by
      change (Ideal.quotientEquivAlgOfEq R (by simp) (AdicCompletion.eval I R n x) = 0) ↔ _
      exact (Ideal.quotientEquivAlgOfEq R (by simp : I ^ n • ⊤ = I ^ n)).map_eq_zero_iff
    change AdicCompletion.evalₐ I n x = 0 ↔ _
    rw [he]
    have h := AdicCompletion.pow_smul_top_eq_ker_eval (M := R) (n := n) hI
    rw [Ideal.smul_top_eq_map] at h
    exact Iff.of_eq (congrArg (fun N : Submodule R (AdicCompletion I R) ↦ x ∈ N) h).symm
  exact bijective_quotientMap_of_ker_eq (I ^ n) _ (AdicCompletion.surjective_evalₐ I n) hker

/-- Let `R` be a Noetherian ring, `I ⊆ R` an ideal and `A = R^∧` its `I`-adic completion. An
`A`-algebra `C`, viewed over `R` through `R → A`, which is rig-étale over `(A, IA)` is rig-étale
over `(R, I)`. -/
public theorem isRigEtale_of_isRigEtale_adicCompletion
    {R C : Type u} [CommRing R] [IsNoetherianRing R] [CommRing C]
    (I : Ideal R) [Algebra (AdicCompletion I R) C] [Algebra R C]
    [IsScalarTower R (AdicCompletion I R) C]
    (hc : IsAdicComplete (I.map (algebraMap R C)) C)
    [Algebra.FiniteType (R ⧸ I) (C ⧸ I.map (algebraMap R C))]
    (hc' : IsAdicComplete
      ((I.map (algebraMap R (AdicCompletion I R))).map
        (algebraMap (AdicCompletion I R) C)) C)
    [Algebra.FiniteType (AdicCompletion I R ⧸ I.map (algebraMap R (AdicCompletion I R)))
      (C ⧸ (I.map (algebraMap R (AdicCompletion I R))).map
        (algebraMap (AdicCompletion I R) C))]
    (h : IsRigEtale (AdicFiniteTypeAlgebra.of
      (I := I.map (algebraMap R (AdicCompletion I R))) C hc')) :
    IsRigEtale (AdicFiniteTypeAlgebra.of (I := I) C hc) := by
  let A := AdicCompletion I R
  let J := I.map (algebraMap R A)
  let B := AdicFiniteTypeAlgebra.of (I := I) C hc
  let B' := AdicFiniteTypeAlgebra.of (I := J) C hc'
  let P := completedPolynomialPresentation I I.fg_of_isNoetherianRing B
  let P' := completedPolynomialPresentation J J.fg_of_isNoetherianRing B'
  apply ((tfae_isRigEtale B P).out 1 4).mpr
  obtain ⟨c, hc⟩ := ((tfae_isRigEtale B' P').out 1 4).mp h
  refine ⟨c, fun n hn a ha ↦ ?_⟩
  have ha' : algebraMap R A a ∈ J ^ c := by
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ ha
  have hn' := hc n hn (algebraMap R A a) ha'
  have hJ : J ^ n = (I ^ n).map (algebraMap R A) :=
    (Ideal.map_pow (algebraMap R A) I n).symm
  have hbijAux (J' : Ideal A) (hJ' : J' = (I ^ n).map (algebraMap R A)) :
      Function.Bijective (Ideal.quotientMap J' (algebraMap R A)
        (hJ' ▸ Ideal.le_comap_map)) := by
    subst J'
    exact bijective_quotientMap_pow_adicCompletion I I.fg_of_isNoetherianRing n
  have hbij := hbijAux (J ^ n) hJ
  exact ⟨(mem_annihilator_homology_quotient_iff (C := C) (I ^ n) (J ^ n) hJ hbij 1 a).mpr hn'.1,
    (mem_annihilator_homology_quotient_iff (C := C) (I ^ n) (J ^ n) hJ hbij 0 a).mpr hn'.2⟩

/-- For a finitely generated ideal `I`, the map `R ⧸ I → R^∧ ⧸ IR^∧` is bijective. -/
private theorem bijective_quotientMap_adicCompletion
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG) :
    Function.Bijective (Ideal.quotientMap (I.map (algebraMap R (AdicCompletion I R)))
      (algebraMap R (AdicCompletion I R)) Ideal.le_comap_map) := by
  exact bijective_quotientMap_of_ker_eq I _ (AdicCompletion.evalOneₐ_surjective I)
    (AdicCompletion.ker_evalOneₐ_eq_map I hI)

/-- Let `R` be a Noetherian ring, `I ⊆ R` an ideal and `φ : R^∧ → C` a ring map. If `C` is
rig-étale over `(R^∧, IR^∧)` through `φ` — complete, of finite type modulo `IR^∧`, and rig-étale —
then `C` is rig-étale over `(R, I)` through `R → R^∧ → C`. -/
public theorem isRigEtaleOver_comp_algebraMap_of_isRigEtaleOver
    {R C : Type u} [CommRing R] [IsNoetherianRing R] [CommRing C] (I : Ideal R)
    [IsNoetherianRing (AdicCompletion I R)] (φ : AdicCompletion I R →+* C)
    (h : IsRigEtaleOver φ (I.map (algebraMap R (AdicCompletion I R)))) :
    IsRigEtaleOver (φ.comp (algebraMap R (AdicCompletion I R))) I := by
  let A := AdicCompletion I R
  let J := I.map (algebraMap R A)
  let : Algebra A C := φ.toAlgebra
  let : Algebra R C := (φ.comp (algebraMap R A)).toAlgebra
  let : IsScalarTower R A C := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  obtain ⟨hc', hf', hrig'⟩ := h
  have hJC : J.map (algebraMap A C) = I.map (algebraMap R C) := by
    rw [Ideal.map_map]
    rfl
  have hc : IsAdicComplete (I.map (algebraMap R C)) C := hJC ▸ hc'
  have hft : (Ideal.quotientMap (I.map (algebraMap R C)) (algebraMap R C)
      Ideal.le_comap_map).FiniteType := by
    let q := Ideal.quotientMap J (algebraMap R A) Ideal.le_comap_map
    have hq := RingHom.FiniteType.of_surjective q
      (bijective_quotientMap_adicCompletion I I.fg_of_isNoetherianRing).2
    have hf'' : (Ideal.quotientMap (J.map (algebraMap A C)) (algebraMap A C)
        Ideal.le_comap_map).FiniteType := RingHom.finiteType_algebraMap.mpr hf'
    let e := Ideal.quotEquivOfEq hJC
    have h := (RingHom.FiniteType.of_surjective e.toRingHom e.surjective).comp (hf''.comp hq)
    convert h using 1
    ext x
    rfl
  let hf : Algebra.FiniteType (R ⧸ I) (C ⧸ I.map (algebraMap R C)) :=
    RingHom.finiteType_algebraMap.mp hft
  exact ⟨hc, hf, isRigEtale_of_isRigEtale_adicCompletion I hc hc' hrig'⟩

end Rig

end
