module

public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Saturation
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreStalk
public import StacksFrontier.AlgebraicGeometry.Perfect.BaseChangeStalk
public import StacksFrontier.AlgebraicGeometry.Perfect.TorIndependence
public import StacksFrontier.Homology.Tor.Independence
public import StacksFrontier.RingTheory.Tor.Balancing
public import StacksFrontier.RingTheory.Tor.TorOneBaseChange
import StacksFrontier.Homology.Tor.Presentation

/-!
# Tor independence after a flat base change

Let `S' ` be a base scheme, let `x : X' ⟶ S'` and `y : Y' ⟶ S'` be morphisms, and let
`zx : Z' ⟶ X'`, `zy : Z' ⟶ Y'` form a commutative square over `S'`. Base change everything
along a morphism `s : S ⟶ S'`. If `y` and `zx` are flat, then the fibre product of the two base
changes is Tor independent from `Z'` over the fibre product `X' ×_{S'} Y'`.

## Main results

* `AlgebraicGeometry.torIndependent_pullback_product_of_flat`: the fibre product of the base
  changes is Tor independent from `Z'` over `X' ×_{S'} Y'`.

## References

* [Stacks Project, Tag 0CTA](https://stacks.math.columbia.edu/tag/0CTA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace AlgebraicGeometry

/-- The fibre product of two base changes along `s : S ⟶ S'`, compared with the fibre product
of `X' ×_{S'} Y'` and `X' ×_{S'} S` over `X'`. -/
private noncomputable def pullbackProductIsoPullbackFst {S S' X' Y' : Scheme.{u}}
    (x : X' ⟶ S') (y : Y' ⟶ S') (s : S ⟶ S') :
    pullback (pullback.snd x s) (pullback.snd y s) ≅
      pullback (pullback.fst x y) (pullback.fst x s) := by
  let e₁ := pullbackSymmetry (pullback.snd x s) (pullback.snd y s)
  let e₂ := pullbackLeftPullbackSndIso y s (pullback.snd x s)
  let e₃ : pullback y (pullback.snd x s ≫ s) ≅ pullback y (pullback.fst x s ≫ x) :=
    pullback.congrHom rfl (pullback.condition (f := x) (g := s)).symm
  let e₄ := pullbackSymmetry y (pullback.fst x s ≫ x)
  let e₅ := (pullbackRightPullbackFstIso x y (pullback.fst x s)).symm
  let e₆ := pullbackSymmetry (pullback.fst x s) (pullback.fst x y)
  exact e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄ ≪≫ e₅ ≪≫ e₆

/-- An algebra equivalence from a localization at a prime, compared along the localization map
`R_r → Y_q` induced by a ring map `R → Y`. -/
private lemma localization_atPrime_algEquiv_apply
    {R Y C : Type u} [CommRing R] [CommRing Y] [CommRing C] [Algebra R Y] [Algebra R C]
    (r : Ideal R) [r.IsPrime] (q : Ideal Y) [q.IsPrime]
    [Algebra (Localization.AtPrime r) (Localization.AtPrime q)]
    (hq : r = q.comap (algebraMap R Y))
    (hloc : algebraMap (Localization.AtPrime r) (Localization.AtPrime q) =
      Localization.localRingHom r q (algebraMap R Y) hq)
    (eR : Localization.AtPrime r ≃ₐ[R] R) (eY : Localization.AtPrime q ≃+* C) (φ : Y →+* C)
    (hφ : φ.comp (algebraMap R Y) = algebraMap R C)
    (hY : ∀ y, eY (algebraMap Y (Localization.AtPrime q) y) = φ y) (z : Localization.AtPrime r) :
    eY (algebraMap (Localization.AtPrime r) (Localization.AtPrime q) z) =
      algebraMap R C (eR z) := by
  let f : Localization.AtPrime r →+* C := eY.toRingHom.comp (algebraMap _ _)
  let g : Localization.AtPrime r →+* C := (algebraMap R C).comp eR.toRingEquiv.toRingHom
  have hfg : f.comp (algebraMap R (Localization.AtPrime r)) =
      g.comp (algebraMap R (Localization.AtPrime r)) := by
    ext a
    simp [f, g, hloc, Localization.localRingHom_to_map, hY, ← hφ]
  exact DFunLike.congr_fun (IsLocalization.ringHom_ext r.primeCompl hfg) z

/-- Tor independence over a local ring is inherited by a localization of the left algebra at a
prime pulled back from its maximal ideal. -/
private lemma torIndependent_localize_left
    (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C]
    [Algebra A C] [IsScalarTower R A C]
    [IsLocalRing R] [IsLocalRing B] [IsLocalRing C]
    (M : Submonoid A) [IsLocalization M C]
    (h : Algebra.TorIndependent R A B)
    (hRC : IsLocalHom (algebraMap R C))
    (hRB : IsLocalHom (algebraMap R B)) :
    Algebra.TorIndependent R C B := by
  let r : PrimeSpectrum R := ⟨IsLocalRing.maximalIdeal R,
    IsLocalRing.maximalIdeal.isMaximal R |>.isPrime⟩
  let : (IsLocalRing.maximalIdeal C).IsPrime := (IsLocalRing.maximalIdeal.isMaximal C).isPrime
  let p : PrimeSpectrum A := ⟨Ideal.comap (algebraMap A C) (IsLocalRing.maximalIdeal C),
    Ideal.comap_isPrime (algebraMap A C) (IsLocalRing.maximalIdeal C)⟩
  let q : PrimeSpectrum B := ⟨IsLocalRing.maximalIdeal B,
    IsLocalRing.maximalIdeal.isMaximal B |>.isPrime⟩
  let : IsLocalHom (algebraMap R C) := hRC
  have hcompAC : (algebraMap A C).comp (algebraMap R A) = algebraMap R C :=
    (IsScalarTower.algebraMap_eq R A C).symm
  have hp : r.asIdeal = p.asIdeal.comap (algebraMap R A) := by
    change IsLocalRing.maximalIdeal R =
      (IsLocalRing.maximalIdeal C).comap ((algebraMap A C).comp (algebraMap R A))
    rw [hcompAC]
    exact (IsLocalRing.maximalIdeal_comap (algebraMap R C)).symm
  let : IsLocalHom (algebraMap R B) := hRB
  have hq : r.asIdeal = q.asIdeal.comap (algebraMap R B) := by
    change IsLocalRing.maximalIdeal R = (IsLocalRing.maximalIdeal B).comap (algebraMap R B)
    exact (IsLocalRing.maximalIdeal_comap (algebraMap R B)).symm
  have hRing : RingTheory.TorIndependence.TorIndependent R A B :=
    (RingTheory.TorIndependence.torIndependent_iff_isZero_tor R A B).2 h
  let : p.asIdeal.LiesOver r.asIdeal := ⟨hp⟩
  let : q.asIdeal.LiesOver r.asIdeal := ⟨hq⟩
  let : Algebra (Localization.AtPrime r.asIdeal) (Localization.AtPrime p.asIdeal) :=
    Localization.AtPrime.algebraOfLiesOver r.asIdeal p.asIdeal
  let : Algebra (Localization.AtPrime r.asIdeal) (Localization.AtPrime q.asIdeal) :=
    Localization.AtPrime.algebraOfLiesOver r.asIdeal q.asIdeal
  have hlocAll :=
    ((RingTheory.TorIndependence.torIndependent_localizations_tfae R A B).out 1 2).mp hRing
  have hloc : RingTheory.TorIndependence.TorIndependent
      (Localization.AtPrime r.asIdeal) (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal) := hlocAll r p q hp hq
  have hsat : M.saturation = p.asIdeal.primeCompl.saturation := by
    ext a
    change a ∈ M.saturation ↔ a ∈ p.asIdeal.primeCompl.saturation
    rw [IsLocalization.mem_saturation_iff_isUnit_algebraMap M C, Submonoid.mem_saturation_iff]
    constructor
    · intro ha
      refine ⟨1, ?_⟩
      have hout : algebraMap A C a ∉ IsLocalRing.maximalIdeal C :=
        IsLocalRing.notMem_maximalIdeal.mpr ha
      simpa [p, Ideal.mem_comap] using hout
    · rintro ⟨b, hb⟩
      have ha : a ∉ p.asIdeal := fun ha => hb (p.asIdeal.mul_mem_right b ha)
      have hout : algebraMap A C a ∉ IsLocalRing.maximalIdeal C := by
        simpa [p, Ideal.mem_comap] using ha
      exact IsLocalRing.notMem_maximalIdeal.mp hout
  let : IsLocalization p.asIdeal.primeCompl C := IsLocalization.of_saturation_eq M _ hsat
  let : IsLocalization q.asIdeal.primeCompl B :=
    IsLocalization.of_le_isUnit fun _ hz => IsLocalRing.notMem_maximalIdeal.mp hz
  let : IsLocalization r.asIdeal.primeCompl R :=
    IsLocalization.of_le_isUnit fun _ hz => IsLocalRing.notMem_maximalIdeal.mp hz
  let eR : Localization.AtPrime r.asIdeal ≃ₐ[R] R :=
    IsLocalization.algEquiv r.asIdeal.primeCompl (Localization.AtPrime r.asIdeal) R
  let eA : Localization.AtPrime p.asIdeal ≃ₐ[A] C :=
    IsLocalization.algEquiv p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal) C
  let eB : Localization.AtPrime q.asIdeal ≃ₐ[B] B :=
    IsLocalization.algEquiv q.asIdeal.primeCompl (Localization.AtPrime q.asIdeal) B
  have hA := localization_atPrime_algEquiv_apply r.asIdeal p.asIdeal hp rfl eR eA.toRingEquiv
    (algebraMap A C) hcompAC eA.commutes
  have hB := localization_atPrime_algEquiv_apply r.asIdeal q.asIdeal hq rfl eR eB.toRingEquiv
    (RingHom.id B) (RingHom.id_comp _) fun _ => by simp
  have hres := (torIndependent_congr (Localization.AtPrime r.asIdeal)
    (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) R C B
    eR.toRingEquiv eA.toRingEquiv eB.toRingEquiv hA hB).mp hloc
  exact (RingTheory.TorIndependence.torIndependent_iff_isZero_tor R C B).mp hres

/-- Tensoring with an algebra, read through restriction of scalars, is extension of scalars
followed by restriction of scalars. -/
private noncomputable def tensorLeftExtendRestrictIso
    (B D : Type u) [CommRing B] [CommRing D] [Algebra B D] :
    (MonoidalCategory.tensorLeft (C := ModuleCat.{u} B) (ModuleCat.of B D)) ≅
      ModuleCat.extendScalars.{u, u, u} (algebraMap B D) ⋙
        ModuleCat.restrictScalars.{u} (algebraMap B D) := by
  let eD : ModuleCat.of B D ≅
      (ModuleCat.restrictScalars.{u} (algebraMap B D)).obj (ModuleCat.of D D) := by
    let e : (↑(ModuleCat.of B D)) ≃+
        ↑((ModuleCat.restrictScalars.{u} (algebraMap B D)).obj (ModuleCat.of D D)) :=
      { toFun := fun z => z
        invFun := fun z => z
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl }
    exact (e.toLinearEquiv (by
      intro r z
      change r • z = (algebraMap B D r) • z
      rw [Algebra.smul_def, smul_eq_mul])).toModuleIso
  exact (MonoidalCategory.tensoringLeft (ModuleCat.{u} B)).mapIso eD

/-- An additive functor preserving homology carries exactness at an index to exactness at that
index. -/
private alias exactAt_mapHomologicalComplex := _root_.exactAt_mapHomologicalComplex

/-- Vanishing of the higher Tor modules of an extension of scalars against a flat algebra: if
`A → B` and `A → D` are flat and `B → D` is an `A`-algebra map, then
`Tor^B_i(B ⊗_A E, D) = 0` for `i > 0`. -/
private lemma tor_zero_of_flat_algebra_extension
    (A B D : Type u) [CommRing A] [CommRing B] [CommRing D]
    [Algebra A B] [Algebra A D] [Algebra B D] [IsScalarTower A B D]
    (hB : RingHom.Flat (algebraMap A B))
    (hD : RingHom.Flat (algebraMap A D)) (E : ModuleCat.{u} A) (i : ℕ) (hi : 0 < i) :
    IsZero (((Tor (ModuleCat.{u} B) i).obj
      ((ModuleCat.extendScalars (algebraMap A B)).obj E)).obj (ModuleCat.of B D)) := by
  let F := ModuleCat.extendScalars (algebraMap A B)
  let T := MonoidalCategory.tensorLeft (C := ModuleCat.{u} B) (ModuleCat.of B D)
  let G := F ⋙ T
  let H := ModuleCat.extendScalars (algebraMap A D) ⋙
    ModuleCat.restrictScalars.{u} (algebraMap B D)
  let eTensor := tensorLeftExtendRestrictIso B D
  let eTower : ModuleCat.extendScalars (algebraMap A D) ≅
      F ⋙ ModuleCat.extendScalars.{u, u, u} (algebraMap B D) := by
    rw [IsScalarTower.algebraMap_eq A B D]
    exact ModuleCat.extendScalarsComp (algebraMap A B) (algebraMap B D)
  let e : G ≅ H :=
    Functor.isoWhiskerLeft F eTensor ≪≫
      Functor.associator F (ModuleCat.extendScalars.{u, u, u} (algebraMap B D))
        (ModuleCat.restrictScalars.{u} (algebraMap B D)) ≪≫
      Functor.isoWhiskerRight eTower.symm (ModuleCat.restrictScalars.{u} (algebraMap B D))
  let : PreservesFiniteLimits (ModuleCat.extendScalars (algebraMap A D)) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hD
  let : PreservesColimitsOfSize.{0, 0} (ModuleCat.extendScalars (algebraMap A D)) :=
    (ModuleCat.extendRestrictScalarsAdj (algebraMap A D)).leftAdjoint_preservesColimits
  let : PreservesFiniteColimits (ModuleCat.extendScalars (algebraMap A D)) :=
    PreservesColimitsOfSize.preservesFiniteColimits _
  let : (ModuleCat.extendScalars (algebraMap A D)).Additive := by
    have : PreservesBinaryBiproducts (ModuleCat.extendScalars (algebraMap A D)) :=
      preservesBinaryBiproducts_of_preservesBinaryCoproducts _
    exact Functor.additive_of_preservesBinaryBiproducts _
  let : F.Additive := by
    have : PreservesColimitsOfSize.{0, 0} F :=
      (ModuleCat.extendRestrictScalarsAdj (algebraMap A B)).leftAdjoint_preservesColimits
    have : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBinaryCoproducts _
    exact Functor.additive_of_preservesBinaryBiproducts _
  let : (ModuleCat.extendScalars.{u, u, u} (algebraMap B D)).Additive := by
    have : PreservesColimitsOfSize.{0, 0} (ModuleCat.extendScalars.{u, u, u} (algebraMap B D)) :=
      (ModuleCat.extendRestrictScalarsAdj (algebraMap B D)).leftAdjoint_preservesColimits
    have : PreservesBinaryBiproducts (ModuleCat.extendScalars.{u, u, u} (algebraMap B D)) :=
      preservesBinaryBiproducts_of_preservesBinaryCoproducts _
    exact Functor.additive_of_preservesBinaryBiproducts _
  let : (ModuleCat.extendScalars (algebraMap A D)).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  let : (ModuleCat.restrictScalars.{u} (algebraMap B D)).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  let : H.PreservesHomology := Functor.preservesHomologyOfExact H
  let P := projectiveResolution E
  let : PreservesFiniteLimits F := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hB
  let : F.PreservesProjectiveObjects :=
    Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
      (ModuleCat.extendRestrictScalarsAdj (algebraMap A B))
  let : F.PreservesHomology := Functor.preservesHomologyOfExact F
  let Q := F.mapProjectiveResolution P
  have hP : P.complex.ExactAt i := by
    convert P.complex_exactAt_succ (i - 1) using 1; omega
  have hH : ((H.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).ExactAt i :=
    exactAt_mapHomologicalComplex (ComplexShape.down ℕ) H P.complex i hP
  let eComp := (Functor.mapHomologicalComplexCompIso (Iso.refl G) (ComplexShape.down ℕ)).app
    P.complex
  let eTot := (NatIso.mapHomologicalComplex e (ComplexShape.down ℕ)).app P.complex
  let eSeq := eTot.symm.trans eComp.symm
  have hzTQ : IsZero
      (((T.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex).homology i) := by
    have hzH : IsZero
        (((H.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).homology i) :=
      (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp hH
    have eH := (HomologicalComplex.homologyFunctor (ModuleCat.{u} B)
      (ComplexShape.down ℕ) i).mapIso eSeq
    exact IsZero.of_iso hzH eH.symm
  let eTor := Q.isoLeftDerivedObj T i
  have hz' : IsZero (((Tor (ModuleCat.{u} B) i).obj (ModuleCat.of B D)).obj (F.obj E)) :=
    IsZero.of_iso hzTQ eTor
  obtain ⟨eSymm⟩ := tor_symm_canonically_iso B i
  let eFlip := (eSymm.app (ModuleCat.of B D)).app (F.obj E)
  have eFlip' : (((Tor (ModuleCat.{u} B) i).obj (ModuleCat.of B D)).obj (F.obj E)) ≅
      (((Tor (ModuleCat.{u} B) i).obj (F.obj E)).obj (ModuleCat.of B D)) := by
    simpa [Functor.flip] using eFlip
  simpa only [F] using IsZero.of_iso hz' eFlip'.symm

/-- In a commutative square, flatness of the right-hand object
over the base and of the upper-left object over the lower-left object implies the indicated Tor
independence after arbitrary base change. -/
@[stacks 0CTA]
theorem torIndependent_pullback_product_of_flat
    {S S' X' Y' Z' : Scheme.{u}}
    (s : S ⟶ S') (x : X' ⟶ S') (y : Y' ⟶ S')
    (zx : Z' ⟶ X') (zy : Z' ⟶ Y') (hz : zx ≫ x = zy ≫ y)
    [Flat y] [Flat zx] :
    let _X := pullback x s
    let _Y := pullback y s
    let P := pullback (pullback.snd x s) (pullback.snd y s)
    let P' := pullback x y
    let pToP' : P ⟶ P' :=
      pullback.lift
        (pullback.fst (pullback.snd x s) (pullback.snd y s) ≫ pullback.fst x s)
        (pullback.snd (pullback.snd x s) (pullback.snd y s) ≫ pullback.fst y s)
        (by
          calc
            _ = pullback.fst (pullback.snd x s) (pullback.snd y s) ≫
                (pullback.fst x s ≫ x) := Category.assoc _ _ _
            _ = pullback.fst (pullback.snd x s) (pullback.snd y s) ≫
                (pullback.snd x s ≫ s) := by rw [pullback.condition]
            _ = (pullback.fst (pullback.snd x s) (pullback.snd y s) ≫
                pullback.snd x s) ≫ s := (Category.assoc _ _ _).symm
            _ = (pullback.snd (pullback.snd x s) (pullback.snd y s) ≫
                pullback.snd y s) ≫ s := by rw [pullback.condition]
            _ = pullback.snd (pullback.snd x s) (pullback.snd y s) ≫
                (pullback.snd y s ≫ s) := Category.assoc _ _ _
            _ = pullback.snd (pullback.snd x s) (pullback.snd y s) ≫
                (pullback.fst y s ≫ y) := by rw [pullback.condition]
            _ = _ := (Category.assoc _ _ _).symm)
    let zToP' : Z' ⟶ P' := pullback.lift zx zy hz
    TorIndependent pToP' zToP' := by
  intro X _Y P P' pToP' zToP'
  change ∀ (p : P) (z : Z') (h : pToP'.base p = zToP'.base z), _
  intro p z hpz
  let Q := pullback (pullback.fst x y) (pullback.fst x s)
  let e := pullbackProductIsoPullbackFst x y s
  let q : Q := e.hom.base p
  let qP := pullback.fst (pullback.fst x y) (pullback.fst x s)
  have heP' : e.hom ≫ qP = pToP' := by
    apply pullback.hom_ext
    · dsimp [qP, e, pullbackProductIsoPullbackFst, pullback.map]
      simp only [pToP', Category.assoc,
        pullback.congrHom_hom, pullback.map,
        pullbackSymmetry_hom_comp_fst_assoc,
        pullbackRightPullbackFstIso_inv_snd_fst,
        pullbackSymmetry_hom_comp_fst_assoc,
        pullback.lift_snd_assoc, pullbackLeftPullbackSndIso_hom_snd_assoc,
        pullbackSymmetry_hom_comp_snd_assoc]
      simp
    · dsimp [qP, e, pullbackProductIsoPullbackFst, pullback.map]
      simp only [pToP', Category.assoc,
        pullback.congrHom_hom, pullback.map,
        pullbackSymmetry_hom_comp_fst_assoc,
        pullbackRightPullbackFstIso_inv_snd_snd]
      simp
  have hqP : qP.base q = pToP'.base p := by
    change (e.hom ≫ qP).base p = pToP'.base p
    rw [heP']
  have hqZ : qP.base q = zToP'.base z := hqP.trans hpz
  let pX := pullback.fst (pullback.fst x y) (pullback.fst x s)
  let pY := pullback.snd (pullback.fst x y) (pullback.fst x s)
  let fQ := pullback.fst x y
  let gQ := pullback.fst x s
  let hQ := congrArg (fun k : Q ⟶ X' => k.base q) pullback.condition
  let xpt' : X' := (pX ≫ fQ).base q
  have hzmap : zToP' ≫ pullback.fst x y = zx := pullback.lift_fst zx zy hz
  have hxpt' : xpt' = zx.base z := by
    change (pullback.fst x y).base (qP.base q) = zx.base z
    rw [hqZ]
    exact congrArg (fun f : Z' ⟶ X' => f.base z) hzmap
  let R0 := X'.presheaf.stalk ((pX ≫ fQ).base q)
  let B0 := P'.presheaf.stalk (pX.base q)
  let A0 := X.presheaf.stalk (pY.base q)
  let D0 := Z'.presheaf.stalk z
  let C0 := Q.presheaf.stalk q
  let : Algebra R0 A0 :=
    ((eqToHom (congrArg X'.presheaf.stalk hQ) ≫ gQ.stalkMap (pY.base q)).hom).toAlgebra
  let : Algebra R0 B0 := (fQ.stalkMap (pX.base q)).hom.toAlgebra
  let : Algebra R0 D0 :=
    ((eqToHom (congrArg X'.presheaf.stalk hxpt') ≫ zx.stalkMap z).hom).toAlgebra
  let : Algebra B0 D0 :=
    ((eqToHom (congrArg P'.presheaf.stalk hqZ) ≫ zToP'.stalkMap z).hom).toAlgebra
  have hxTower : (algebraMap B0 D0).comp (algebraMap R0 B0) = algebraMap R0 D0 := by
    have hpointf := Scheme.Hom.stalkMap_congr_point (pullback.fst x y)
      (pX.base q) (zToP'.base z) hqZ
    rw [stalkCongr_of_eq P'.presheaf hqZ,
      stalkCongr_of_eq X'.presheaf (congrArg (pullback.fst x y).base hqZ)] at hpointf
    have hpointcomp := Scheme.Hom.stalkMap_congr_hom
      (zToP' ≫ pullback.fst x y) zx hzmap z
    rw [stalkCongr_of_eq X'.presheaf
      (congrArg (fun k : Z' ⟶ X' => k.base z) hzmap)] at hpointcomp
    rw [Scheme.Hom.stalkMap_comp] at hpointcomp
    change (zToP'.stalkMap z).hom.comp
        ((eqToHom (congrArg P'.presheaf.stalk hqZ)).hom.comp
          ((pullback.fst x y).stalkMap (qP.base q)).hom) =
      (zx.stalkMap z).hom.comp (eqToHom (congrArg X'.presheaf.stalk hxpt')).hom
    ext a
    have hpointfRing := CommRingCat.hom_ext_iff.mp hpointf
    have hpointcompRing := CommRingCat.hom_ext_iff.mp hpointcomp
    change (zToP'.stalkMap z).hom
        ((eqToHom (congrArg P'.presheaf.stalk hqZ)).hom
          (((pullback.fst x y).stalkMap (qP.base q)).hom a)) =
      (zx.stalkMap z).hom ((eqToHom (congrArg X'.presheaf.stalk hxpt')).hom a)
    have hvalf := DFunLike.congr_fun hpointfRing a
    have hval := DFunLike.congr_fun hpointcompRing
      ((eqToHom (congrArg X'.presheaf.stalk
        (congrArg (pullback.fst x y).base hqZ))).hom a)
    have hvalf' := congrArg (zToP'.stalkMap z).hom hvalf
    calc
      (zToP'.stalkMap z).hom
          ((eqToHom (congrArg P'.presheaf.stalk hqZ)).hom
            (((pullback.fst x y).stalkMap (qP.base q)).hom a)) =
      (zToP'.stalkMap z).hom
          (((pullback.fst x y).stalkMap (zToP'.base z)).hom
            ((eqToHom (congrArg X'.presheaf.stalk
              (congrArg (pullback.fst x y).base hqZ))).hom a)) := hvalf'
      _ = (zx.stalkMap z).hom ((eqToHom (congrArg X'.presheaf.stalk hxpt')).hom a) := by
        have h3 := congrArg (fun k : Z' ⟶ X' => k.base z) hzmap
        have hcast :
            ((eqToHom (congrArg X'.presheaf.stalk h3)).hom
              ((eqToHom (congrArg X'.presheaf.stalk
                (congrArg (pullback.fst x y).base hqZ))).hom a)) =
              (eqToHom (congrArg X'.presheaf.stalk hxpt')).hom a := by
          have heq : (congrArg (pullback.fst x y).base hqZ).trans h3 = hxpt' :=
            Subsingleton.elim _ _
          have hhom :
              eqToHom (congrArg X'.presheaf.stalk
                (congrArg (pullback.fst x y).base hqZ)) ≫
              eqToHom (congrArg X'.presheaf.stalk h3) =
              eqToHom (congrArg X'.presheaf.stalk hxpt') := by
            rw [CategoryTheory.eqToHom_trans]
            exact congrArg (fun h => eqToHom (congrArg X'.presheaf.stalk h)) heq
          exact congrArg (fun f : CommRingCat.Hom _ _ => f.hom a) hhom
        exact hval.trans (congrArg (zx.stalkMap z).hom hcast)
  let : IsScalarTower R0 B0 D0 := IsScalarTower.of_algebraMap_eq' hxTower.symm
  let T := TensorProduct R0 B0 A0
  let : Algebra B0 T := Algebra.TensorProduct.leftAlgebra
  let : Algebra R0 T := inferInstance
  let : IsScalarTower R0 B0 T := IsScalarTower.of_algebraMap_eq' rfl
  let : Flat (pullback.fst x y) := by infer_instance
  have hBflat : RingHom.Flat (algebraMap R0 B0) := Flat.stalkMap (pullback.fst x y) (qP.base q)
  have hDflat : RingHom.Flat (algebraMap R0 D0) := by
    change RingHom.Flat ((zx.stalkMap z).hom.comp
      (eqToHom (congrArg X'.presheaf.stalk hxpt')).hom)
    exact RingHom.Flat.comp
      (.of_bijective (ConcreteCategory.bijective_of_isIso _)) (Flat.stalkMap zx z)
  have hT : Algebra.TorIndependent B0 T D0 := by
    rw [Algebra.torIndependent_iff]
    intro i hi
    have hzero := tor_zero_of_flat_algebra_extension R0 B0 D0
      hBflat hDflat (ModuleCat.of R0 A0) i hi
    let eT := Stacks.TorOneBaseChange.tensorEquivExtendScalars B0 (ModuleCat.of R0 A0)
    let eModule : ModuleCat.of B0 T ≅
        (ModuleCat.extendScalars (algebraMap R0 B0)).obj (ModuleCat.of R0 A0) :=
      eT.toModuleIso
    exact IsZero.of_iso hzero
      (((Tor (ModuleCat.{u} B0) i).mapIso eModule).app (ModuleCat.of B0 D0)).symm
  obtain ⟨φ, hφA, hφB, M, hlocal⟩ :=
    BaseChangeStalk.pullback_stalk_isLocalization (pullback.fst x y) (pullback.fst x s) q
  let : Algebra T C0 := by
    dsimp [T, R0, B0, A0, C0, qP, Q, P']
    exact φ.toAlgebra
  let : Algebra B0 C0 := (φ.comp Algebra.TensorProduct.includeLeftRingHom).toAlgebra
  let : Algebra R0 C0 := ((algebraMap B0 C0).comp (algebraMap R0 B0)).toAlgebra
  let : IsScalarTower B0 T C0 := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower R0 B0 C0 := IsScalarTower.of_algebraMap_eq' rfl
  let : IsLocalization M C0 := hlocal
  have hmapBC : algebraMap B0 C0 = (qP.stalkMap q).hom := hφA
  have hRC : IsLocalHom (algebraMap B0 C0) := by
    rw [hmapBC]
    infer_instance
  have hRB : IsLocalHom (algebraMap B0 D0) := by
    change IsLocalHom ((eqToHom (congrArg P'.presheaf.stalk hqZ) ≫
      zToP'.stalkMap z).hom)
    infer_instance
  have hlocalTor := torIndependent_localize_left B0 T D0 C0 M hT hRC hRB
  let eStalkIso : CommRingCat.of C0 ≅ CommRingCat.of (P.presheaf.stalk p) :=
    asIso (e.hom.stalkMap p)
  let eCA : C0 ≃+* P.presheaf.stalk p :=
    RingEquiv.ofBijective eStalkIso.hom.hom
      (ConcreteCategory.bijective_of_isIso eStalkIso.hom)
  let R' := P'.presheaf.stalk (pToP'.base p)
  let eRHom := eqToHom (congrArg P'.presheaf.stalk hqP)
  let eR : B0 ≃+* R' := RingEquiv.ofBijective eRHom.hom
    (ConcreteCategory.bijective_of_isIso eRHom)
  let : Algebra R' (P.presheaf.stalk p) := (pToP'.stalkMap p).hom.toAlgebra
  let : Algebra R' D0 :=
    ((eqToHom (congrArg P'.presheaf.stalk hpz) ≫ zToP'.stalkMap z).hom).toAlgebra
  have hAcompat : ∀ a : B0,
      eCA (algebraMap B0 C0 a) = algebraMap R' (P.presheaf.stalk p) (eR a) := by
    intro a
    rw [hmapBC]
    change eStalkIso.hom.hom ((qP.stalkMap q).hom a) =
      ((pToP'.stalkMap p).hom (eRHom.hom a))
    have hmap := Scheme.Hom.stalkMap_comp e.hom qP p
    have hcmp := Scheme.Hom.stalkMap_congr_hom (e.hom ≫ qP) pToP' heP' p
    rw [stalkCongr_of_eq] at hcmp
    rotate_left
    · exact hqP
    have hpoint : (congrArg (fun k : P ⟶ P' => k.base p) heP') = hqP :=
      Subsingleton.elim _ _
    have hcmp' : (e.hom ≫ qP).stalkMap p =
        eqToHom (congrArg P'.presheaf.stalk hqP) ≫ pToP'.stalkMap p := by
      simpa [hpoint] using hcmp
    have hmap' := congrArg (fun f : CommRingCat.Hom _ _ => f.hom a) hmap
    have hcmp'' := congrArg (fun f : CommRingCat.Hom _ _ => f.hom a) hcmp'
    simpa [eStalkIso, eRHom, RingHom.comp_apply] using hmap'.symm.trans hcmp''
  have hBcompat : ∀ a : B0,
      (RingEquiv.refl D0) (algebraMap B0 D0 a) = algebraMap R' D0 (eR a) := by
    intro a
    change (((eqToHom (congrArg P'.presheaf.stalk hqZ) ≫ zToP'.stalkMap z).hom) a) =
      (((eqToHom (congrArg P'.presheaf.stalk hpz) ≫ zToP'.stalkMap z).hom) (eRHom.hom a))
    change ((eqToHom (congrArg P'.presheaf.stalk hqZ) ≫ zToP'.stalkMap z).hom a) =
      ((eqToHom (congrArg P'.presheaf.stalk hqP) ≫
        (eqToHom (congrArg P'.presheaf.stalk hpz) ≫ zToP'.stalkMap z)).hom a)
    simp only [← Category.assoc, eqToHom_trans]
  have hlocalRing : RingTheory.TorIndependence.TorIndependent B0 C0 D0 :=
    (RingTheory.TorIndependence.torIndependent_iff_isZero_tor B0 C0 D0).2 hlocalTor
  have hresult := (torIndependent_congr B0 C0 D0 R' (P.presheaf.stalk p) D0
    eR eCA (RingEquiv.refl D0) hAcompat hBcompat).mp hlocalRing
  exact (RingTheory.TorIndependence.torIndependent_iff_isZero_tor R'
    (P.presheaf.stalk p) D0).mp hresult

end AlgebraicGeometry
