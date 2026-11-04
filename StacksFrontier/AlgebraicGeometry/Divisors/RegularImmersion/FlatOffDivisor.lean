module

public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.Flat.Tensor
public import Mathlib.RingTheory.Localization.BaseChange
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Picard.RelativeEffectiveCartier
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat

/-!
# Flatness across a relative effective Cartier divisor

Let `f : X ⟶ S` be a morphism of schemes and `D ⊆ X` a relative effective Cartier divisor over
`S`.  If `f` is flat at every point outside `D`, then `f` is flat.

## Main results

* `AlgebraicGeometry.flat_of_flat_quotient_and_localization`: if `0 → B --t--> B → Q → 0` is an
  exact sequence of `A`-modules and both `Q` and the localization of `B` away from `t` are flat
  over `A`, then `B` is flat over `A`.
* `AlgebraicGeometry.notMem_supportSet_of_mem_basicOpen_of_chart`: on an affine open on which the
  divisor is the vanishing locus of a section `t`, the basic open of `t` misses the divisor.
* `AlgebraicGeometry.flat_of_flat_off_relativeEffectiveCartierDivisor`: a morphism flat at every
  point outside a relative effective Cartier divisor is flat.

## References

* [Stacks Project, Tag 062W](https://stacks.math.columbia.edu/tag/062W)
* [Stacks Project, Tag 01WS](https://stacks.math.columbia.edu/tag/01WS)
* [Stacks Project, Tag 02OO](https://stacks.math.columbia.edu/tag/02OO)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits LinearMap
open Stacks.Divisors

universe u

namespace AlgebraicGeometry


/-- Let `t ∈ B`, let `L` be the localization of `B` away from `t` and let
`0 → B --t--> B → Q → 0` be an exact sequence of `A`-modules.  If `Q` and `L` are flat over `A`,
then `B` is flat over `A`. -/
theorem flat_of_flat_quotient_and_localization
    {A B Q L : Type*} [CommRing A] [CommRing B] [AddCommGroup Q] [CommRing L]
    [Algebra A B] [Module A Q] [Algebra B L] [Algebra A L]
    [IsScalarTower A B L]
    (t : B) [IsLocalization.Away t L]
    (f : B →ₗ[A] B) (q : B →ₗ[A] Q)
    (hf : Function.Injective f) (hex : Function.Exact f q)
    (hq : Function.Surjective q)
    (hft : f = (LinearMap.mulLeft B t).restrictScalars A)
    (hQ : Module.Flat A Q) [Module.Flat A L] :
    Module.Flat A B := by
  have := hQ
  rw [Module.Flat.iff_rTensor_injective]
  intro I hI
  have hfI : Function.Injective (LinearMap.lTensor I f) := by
    exact LinearMap.lTensor_injective_of_exact_of_flat q hq f hf hex I
  let eB : TensorProduct A I B ≃ₗ[A] TensorProduct A B I :=
    TensorProduct.comm A I B
  let eL : TensorProduct A I L ≃ₗ[A] TensorProduct A L I :=
    TensorProduct.comm A I L
  have hfI' : Function.Injective (LinearMap.rTensor I f) := by
    intro x y hxy
    apply eB.symm.injective
    apply hfI
    have hcomm (z : TensorProduct A B I) :
        eB.symm (LinearMap.rTensor I f z) =
          (LinearMap.lTensor I f) (eB.symm z) := by
      refine TensorProduct.induction_on z ?_ ?_ ?_
      · simp
      · intro b i
        rfl
      · intro z₁ z₂ hz₁ hz₂
        simp [hz₁, hz₂]
    rw [← hcomm x, ← hcomm y, hxy]
  have hmul : ∀ z : TensorProduct A B I,
      LinearMap.rTensor I f z = t • z := by
    intro z
    refine TensorProduct.induction_on z ?_ ?_ ?_
    · simp
    · intro b i
      simp [hft, TensorProduct.smul_tmul']
    · intro x y hx hy
      simp [hx, hy]
  have hpow : ∀ n (z : TensorProduct A B I), t ^ n • z = 0 → z = 0 := by
    intro n
    induction n with
    | zero => intro z hz; simpa using hz
    | succ n ih =>
        intro z hz
        apply ih
        apply hfI'
        rw [hmul]
        simpa [hmul, pow_succ, mul_smul, mul_comm] using hz
  let loc : B →ₗ[B] L := (IsScalarTower.toAlgHom B B L).toLinearMap
  let locI := TensorProduct.AlgebraTensorModule.rTensor A I loc
  have : IsLocalizedModule (Submonoid.powers t) locI := by
    dsimp [locI, loc]
    infer_instance
  intro x y hxy
  have hxzero : (I.subtype.rTensor B) (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  let z := eB (x - y)
  let locA : B →ₗ[A] L := loc.restrictScalars A
  have hnat : (I.subtype.rTensor L) (eL.symm (locI z)) = 0 := by
    have hloc : eL.symm (locI z) = locA.lTensor I (x - y) := by
      show eL.symm (locI (eB (x - y))) = locA.lTensor I (x - y)
      refine TensorProduct.induction_on (x - y) ?_ ?_ ?_
      · simp [locI]
      · intro i b
        simp [locI, eB, eL, locA, loc]
      · intro a b ha hb
        simp [ha, hb]
    rw [hloc]
    have hcomm : (locA.lTensor A).comp (I.subtype.rTensor B) =
        (I.subtype.rTensor L).comp (locA.lTensor I) := by
      ext i b
      rfl
    have hcomm' := congrArg (fun F => F (x - y)) hcomm
    have hcomm'' : (I.subtype.rTensor L) (locA.lTensor I (x - y)) =
        (locA.lTensor A) ((I.subtype.rTensor B) (x - y)) := by
      simpa only [LinearMap.comp_apply] using hcomm'.symm
    rw [hxzero, map_zero] at hcomm''
    exact hcomm''
  have hloczero : locI z = 0 := by
    have hIinj : Function.Injective (I.subtype.rTensor L) :=
      (Module.Flat.iff_rTensor_injective.mp
        (inferInstance : Module.Flat A L)) hI
    have hzL : eL.symm (locI z) = 0 := hIinj hnat
    exact eL.symm.injective hzL
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff (S := Submonoid.powers t) locI).mp hloczero
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff s.1 t).mp s.2
  have hs' : t ^ n • z = 0 := by simpa [Submonoid.smul_def, hn] using hs
  have hz : z = 0 := hpow n z hs'
  have hsub : x - y = 0 := eB.injective (by simpa [z] using hz)
  exact sub_eq_zero.mp hsub

/-- The composite of an open immersion with a morphism flat at the image point is flat at the
point. -/
private theorem flat_stalkMap_comp_of_isOpenImmersion {X Y S : Scheme.{u}} (g : Y ⟶ X)
    [IsOpenImmersion g] (f : X ⟶ S) (y : Y) (h : IsFlatAt f.toLRSHom.toShHom (g y)) :
    ((g ≫ f).stalkMap y).hom.Flat := by
  rw [Scheme.Hom.stalkMap_comp]
  exact RingHom.Flat.comp (h : (f.stalkMap (g y)).hom.Flat)
    (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso (g.stalkMap y)))

/-- **Flatness on an open where the morphism is flat at every point.**  If `f` is flat at every
point of an open `U ⊆ X`, then the restriction `U ⟶ S` of `f` to `U` is flat. -/
theorem flat_restrict_open_of_flatAt
    {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens)
    (hU : ∀ x : X, x ∈ U → IsFlatAt f.toLRSHom.toShHom x) :
    Flat (U.ι ≫ f) :=
  Flat.of_stalkMap _ fun y => flat_stalkMap_comp_of_isOpenImmersion U.ι f y (hU y.1 y.2)

/-- **The basic open of a local equation misses the divisor.** If on an affine open `U` the divisor
`I` is presented as the vanishing locus of `t ∈ Γ(X, U)`, then no point of `X.basicOpen t` lies in
the support of `I`. -/
theorem notMem_supportSet_of_mem_basicOpen_of_chart
    {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.Opens)
    (hU : IsAffineOpen U) (t : Γ(X, U))
    (e : pullback I.subschemeι U.ι ≅
      Spec (.of (Γ(X, U) ⧸ Ideal.span {t})))
    (he : pullback.snd I.subschemeι U.ι ≫ hU.isoSpec.hom =
      e.hom ≫ Spec.map
        (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {t})))) :
    ∀ x : X, x ∈ X.basicOpen t → x ∉ I.supportSet := by
  intro x hx hxI
  have hxU : x ∈ U := X.basicOpen_le t hx
  let xU : U := ⟨x, hxU⟩
  have hxRange : x ∈ Set.range I.subschemeι := by
    rw [I.range_subschemeι]
    exact Scheme.IdealSheafData.mem_supportSet_iff_mem_support.mp hxI
  obtain ⟨y, hy⟩ := hxRange
  have hz := Scheme.Pullback.exists_preimage_pullback
    (f := I.subschemeι) (g := U.ι) y xU (by simpa [xU] using hy)
  let z := Classical.choose hz
  have hzU : pullback.snd I.subschemeι U.ι z = xU :=
    (Classical.choose_spec hz).2
  let m := Ideal.Quotient.mk (Ideal.span {t})
  let qSpec : Spec (.of (Γ(X, U) ⧸ Ideal.span {t})) := e.hom z
  let q : PrimeSpectrum (Γ(X, U) ⧸ Ideal.span {t}) := qSpec
  have hpoint := congrArg
    (fun k : pullback I.subschemeι U.ι ⟶ Spec (.of (Γ(X, U))) => k z) he
  have hpoint' : (Spec.map (CommRingCat.ofHom m)) qSpec = hU.isoSpec.hom xU := by
    simpa [qSpec, hzU] using hpoint.symm
  have hqIdeal : Ideal.comap m q.asIdeal = (hU.isoSpec.hom xU).asIdeal := by
    have h := congrArg (fun w : Spec (.of (Γ(X, U))) => w.asIdeal) hpoint'
    change (Spec.map (CommRingCat.ofHom m) qSpec).asIdeal =
      (hU.isoSpec.hom xU).asIdeal at h
    rw [AlgebraicGeometry.Spec.map_apply] at h
    change Ideal.comap m q.asIdeal = (hU.isoSpec.hom xU).asIdeal at h
    exact h
  have htq : m t = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.subset_span (by simp)
  have hqOpen : hU.primeIdealOf xU ∈ PrimeSpectrum.basicOpen t := by
    rw [← hU.fromSpec_preimage_basicOpen t]
    show hU.fromSpec (hU.primeIdealOf xU) ∈ X.basicOpen t
    rwa [hU.fromSpec_primeIdealOf]
  have htNot : t ∉ (hU.primeIdealOf xU).asIdeal :=
    (PrimeSpectrum.mem_basicOpen t (hU.primeIdealOf xU)).mp hqOpen
  have htmem' : t ∈ (hU.primeIdealOf xU).asIdeal := by
    show t ∈ (hU.isoSpec.hom xU).asIdeal
    rw [← hqIdeal]
    show m t ∈ q.asIdeal
    rw [htq]
    exact q.asIdeal.zero_mem
  exact htNot htmem'

/-- A morphism flat away from a relative effective Cartier divisor is flat. -/
@[stacks 062W]
theorem flat_of_flat_off_relativeEffectiveCartierDivisor
    {X S : Scheme.{u}} (f : X ⟶ S) (I : X.IdealSheafData)
    (hI : IsRelativeEffectiveCartierDivisor f I)
    (hf : ∀ x : X, x ∉ I.supportSet →
      IsFlatAt f.toLRSHom.toShHom x) :
    Flat f := by
  refine Flat.of_stalkMap f fun x => ?_
  by_cases hx : x ∈ I.supportSet
  · obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
    let Y : X.Opens := f ⁻¹ᵁ (V : S.Opens)
    have hxY : x ∈ Y := by simpa [Y] using hxV
    let j : Y.toScheme ⟶ X := Y.ι
    let IY : Y.toScheme.IdealSheafData := I.comap j
    have hIY : IsEffectiveCartierDivisor IY := by
      show IsPullbackDefined j I
      exact isPullbackDefined_of_flat j I hI.1
    have hsupp : ∀ z : Y.toScheme, j z ∈ I.supportSet → z ∈ IY.supportSet := fun z hz =>
      Scheme.IdealSheafData.mem_supportSet_iff_mem_support.mpr (by
        rw [Scheme.IdealSheafData.support_comap]
        exact Scheme.IdealSheafData.mem_supportSet_iff_mem_support.mp hz)
    obtain ⟨U, hU, hxU, t, ht, e, he⟩ :=
      (isEffectiveCartierDivisor_iff_affineLocal IY).mp hIY
        ⟨x, hxY⟩ (hsupp _ hx)
    let k : IY.subscheme ⟶ I.subscheme :=
      (I.comapIso j).hom ≫ pullback.snd j I.subschemeι
    have hk : Flat k := by
      dsimp [k]
      infer_instance
    have hkcomp : IY.subschemeι ≫ j = k ≫ I.subschemeι := by
      dsimp [k]
      rw [← Scheme.IdealSheafData.comapIso_hom_fst]
      simp only [Category.assoc, pullback.condition]
    have hflatIY : Flat (IY.subschemeι ≫ j ≫ f) := by
      rw [show IY.subschemeι ≫ j ≫ f = k ≫ I.subschemeι ≫ f by
        rw [← Category.assoc, hkcomp, Category.assoc]]
      let : Flat k := hk
      let : Flat (I.subschemeι ≫ f) := hI.2
      infer_instance
    let P := pullback IY.subschemeι U.ι
    have hflatP : Flat (pullback.fst IY.subschemeι U.ι ≫ IY.subschemeι ≫ j ≫ f) := by
      let : Flat (pullback.fst IY.subschemeι U.ι) := inferInstance
      let : Flat (IY.subschemeι ≫ j ≫ f) := hflatIY
      infer_instance
    have hflatQ : Flat
        (e.inv ≫ pullback.fst IY.subschemeι U.ι ≫ IY.subschemeι ≫ j ≫ f) := by
      let : Flat (pullback.fst IY.subschemeι U.ι ≫ IY.subschemeι ≫ j ≫ f) := hflatP
      infer_instance
    let Z : (Y.toScheme).Opens := Y.toScheme.basicOpen t
    let hZ : IsAffineOpen Z := hU.basicOpen t
    let gS : Y.toScheme ⟶ S := j ≫ f
    have hZoffX : ∀ z : Y.toScheme, z ∈ Z →
        j z ∉ I.supportSet := by
      intro z hz hzI
      exact notMem_supportSet_of_mem_basicOpen_of_chart IY U hU t e he z hz (hsupp z hzI)
    have hflatgS : ∀ z : Y.toScheme, z ∈ Z →
        IsFlatAt gS.toLRSHom.toShHom z := fun z hz =>
      flat_stalkMap_comp_of_isOpenImmersion j f z (hf (j z) (hZoffX z hz))
    have hflatZ : Flat (Z.ι ≫ gS) :=
      flat_restrict_open_of_flatAt gS Z hflatgS
    have hYV : (⊤ : (Y.toScheme).Opens) ≤ gS ⁻¹ᵁ V := by
      intro z hz
      show f (j z) ∈ V
      exact z.2
    have hZV : Z ≤ gS ⁻¹ᵁ V := le_trans (by simp) hYV
    let A := Γ(S, V)
    let B := Γ(Y.toScheme, U)
    let L := Γ(Y.toScheme, Z)
    let ψ : A →+* L := (gS.appLE V Z hZV).hom
    have hψflat : ψ.Flat := by
      let : IsAffine Z.toScheme := hZ
      have hflatφ :
          (((Z.ι ≫ gS).appLE V ⊤ (by
            intro z hz
            exact hZV z.2)).hom).Flat :=
        Flat.flat_appLE (Z.ι ≫ gS) hV (isAffineOpen_top Z.toScheme) (by
          intro z hz
          exact hZV z.2)
      have hmap : Z.topIso.symm.hom.hom.comp ψ =
          ((Z.ι ≫ gS).appLE V ⊤ (by
            intro z hz
            exact hZV z.2)).hom := by
        dsimp [ψ]
        have htop : Z.topIso.inv = Z.ι.appLE Z ⊤ (by simp) := by
          ext s
          simp only [Scheme.Opens.topIso, Scheme.Opens.ι_appLE,
            Scheme.Opens.toScheme_presheaf_map]
          congr 1
        rw [htop]
        exact congrArg CommRingCat.Hom.hom
          (Scheme.Hom.appLE_comp_appLE Z.ι gS V Z ⊤ hZV (by simp))
      apply (RingHom.Flat.comp_iff_of_bijective_left
        (ConcreteCategory.bijective_of_isIso Z.topIso.symm.hom)).mp
      rw [hmap]
      exact hflatφ
    let : Algebra A L := ψ.toAlgebra
    have hLflat : Module.Flat A L := hψflat
    let : IsLocalization.Away t L := hU.isLocalization_basicOpen t
    let Q := (B : Type u) ⧸ Ideal.span {t}
    let ρ : B →+* Q := Ideal.Quotient.mk _
    let α : A →+* B := (gS.appLE V U (by
      intro z hz
      exact hYV (Set.mem_univ z))).hom
    let β : A →+* Q := ρ.comp α
    let : Algebra A B := α.toAlgebra
    let : Algebra B Q := ρ.toAlgebra
    let : Algebra A Q := β.toAlgebra
    let : IsScalarTower A B Q := IsScalarTower.of_algebraMap_eq' rfl
    let ρcat : B ⟶ CommRingCat.of Q := CommRingCat.ofHom ρ
    let αcat : A ⟶ B := CommRingCat.ofHom α
    let βcat : A ⟶ CommRingCat.of Q := CommRingCat.ofHom β
    let gQ : Spec (.of Q) ⟶ S :=
      e.inv ≫ pullback.fst IY.subschemeι U.ι ≫ IY.subschemeι ≫ j ≫ f
    have hgQV : ⊤ ≤ gQ ⁻¹ᵁ V := by
      intro z hz
      show gS (IY.subschemeι ((pullback.fst IY.subschemeι U.ι) (e.inv z))) ∈ V
      exact hYV (Set.mem_univ _)
    have hρchart :
        e.inv ≫ pullback.snd IY.subschemeι U.ι ≫ hU.isoSpec.hom =
            Spec.map ρcat := by
      calc
        e.inv ≫ pullback.snd IY.subschemeι U.ι ≫ hU.isoSpec.hom =
            e.inv ≫ e.hom ≫ Spec.map ρcat := by rw [he]; rfl
        _ = Spec.map ρcat := by simp
    have hαchart : Spec.map αcat ≫ hV.fromSpec =
        hU.fromSpec ≫ gS :=
      IsAffineOpen.SpecMap_appLE_fromSpec gS hV hU (by
        intro z hz
        exact hYV (Set.mem_univ z))
    have hβspec : Spec.map βcat = Spec.map ρcat ≫ Spec.map αcat := by
      show Spec.map (CommRingCat.ofHom (ρ.comp α)) =
        Spec.map (CommRingCat.ofHom ρ) ≫ Spec.map (CommRingCat.ofHom α)
      rw [CommRingCat.ofHom_comp, ← Spec.map_comp]
    have hρlift : Spec.map ρcat ≫ hU.fromSpec ≫ gS = gQ := by
      calc
        Spec.map ρcat ≫ hU.fromSpec ≫ gS =
            e.inv ≫ pullback.snd IY.subschemeι U.ι ≫ hU.isoSpec.hom ≫
              hU.fromSpec ≫ gS := by
                rw [← hρchart]
                simp only [Category.assoc]
        _ = e.inv ≫ pullback.fst IY.subschemeι U.ι ≫ IY.subschemeι ≫ gS := by
          calc
            _ = e.inv ≫ pullback.snd IY.subschemeι U.ι ≫ U.ι ≫ gS := by
              simpa only [Category.assoc] using
                congrArg (fun k : U.toScheme ⟶ Y.toScheme =>
                  e.inv ≫ pullback.snd IY.subschemeι U.ι ≫ k ≫ gS)
                  (IsAffineOpen.isoSpec_hom_fromSpec hU)
            _ = e.inv ≫ pullback.fst IY.subschemeι U.ι ≫ IY.subschemeι ≫ gS := by
              simpa only [Category.assoc] using
                congrArg (fun k : P ⟶ Y.toScheme => e.inv ≫ k ≫ gS)
                  pullback.condition.symm
        _ = gQ := by simp [gQ, gS]
    let gV := (Scheme.topIso (Spec (.of Q))).inv ≫ gQ.resLE V ⊤ hgQV
    have hG : gV = Spec.map βcat ≫ hV.isoSpec.inv := by
      apply (cancel_mono (Scheme.Opens.ι V)).1
      calc
        gV ≫ Scheme.Opens.ι V = gQ := by
          simp [gV, Scheme.Hom.resLE_comp_ι]
        _ = Spec.map βcat ≫ hV.fromSpec := by
          rw [hβspec, Category.assoc, hαchart]
          exact hρlift.symm
        _ = Spec.map βcat ≫ hV.isoSpec.inv ≫ Scheme.Opens.ι V := by
          rw [IsAffineOpen.isoSpec_inv_ι hV]
    let : Flat gQ := hflatQ
    let : Flat gV := by dsimp [gV]; infer_instance
    have hQflat : Module.Flat A Q := by
      show β.Flat
      apply (Flat.SpecMap_iff (f := βcat)).mp
      have heq : Spec.map βcat = gV ≫ hV.isoSpec.hom := by
        rw [hG]
        simp
      rw [heq]
      infer_instance
    let : Module.Flat A Q := hQflat
    let : Module.Flat A L := hLflat
    have : IsScalarTower A B L := IsScalarTower.of_algebraMap_eq' (by
      show ψ = (algebraMap B L).comp α
      exact (congrArg CommRingCat.Hom.hom
        (gS.appLE_map (show U ≤ gS ⁻¹ᵁ V from fun z _ => hYV (Set.mem_univ z))
          (homOfLE (Y.toScheme.basicOpen_le t)).op)).symm)
    let fmul : B →ₗ[A] B := (LinearMap.mulLeft B t).restrictScalars A
    let qlin : B →ₗ[A] Q :=
      (Ideal.Quotient.mkₐ B (Ideal.span {t})).toLinearMap.restrictScalars A
    have hfInjective : Function.Injective fmul := by
      intro a b hab
      apply ht.left
      simpa [fmul, LinearMap.mulLeft_apply, Algebra.smul_def] using
        congrArg (fun y : B => y) hab
    have hExact : Function.Exact fmul qlin := by
      rw [LinearMap.exact_iff]
      ext b
      constructor
      · intro hb
        have hb' : b ∈ Ideal.span ({t} : Set B) :=
          (Ideal.Quotient.eq_zero_iff_mem).mp (by
            simpa [LinearMap.mem_ker, qlin] using hb)
        rcases Ideal.mem_span_singleton.mp hb' with ⟨c, hc⟩
        refine ⟨c, ?_⟩
        simp [fmul, LinearMap.mulLeft_apply, hc]
      · rintro ⟨c, rfl⟩
        simp [qlin, fmul]
    have hBflat : Module.Flat A B :=
      flat_of_flat_quotient_and_localization (L := L) t fmul qlin hfInjective hExact
        Ideal.Quotient.mk_surjective rfl hQflat
    have hαflat : α.Flat := RingHom.flat_algebraMap_iff.mpr hBflat
    have hUV : U ≤ gS ⁻¹ᵁ V := by
      intro z hz
      exact hYV (Set.mem_univ z)
    have hflatRestrict : Flat (gS.resLE V U hUV) := by
      let : IsAffine U.toScheme := hU
      let : IsAffine (Scheme.Opens.toScheme (X := S) V) := hV
      rw [HasRingHomProperty.iff_of_isAffine (P := @Flat)]
      apply (RingHom.Flat.propertyIsLocal.respectsIso.arrow_mk_iso_iff
        (arrowResLEAppIso gS V U hUV)).mpr
      exact hαflat
    let : Flat (gS.resLE V U hUV) := hflatRestrict
    have hflatUg : Flat (U.ι ≫ gS) := by
      rw [← Scheme.Hom.resLE_comp_ι gS hUV]
      infer_instance
    let i : U.toScheme ⟶ X := U.ι ≫ j
    let xU : U.toScheme := ⟨⟨x, hxY⟩, hxU⟩
    let : Flat (i ≫ f) := by
      simpa only [i, gS, Category.assoc] using hflatUg
    have hflatAt := Flat.stalkMap (i ≫ f) xU
    rw [Scheme.Hom.stalkMap_comp] at hflatAt
    exact (RingHom.Flat.comp_iff_of_bijective_left
      (ConcreteCategory.bijective_of_isIso (i.stalkMap xU))).mp hflatAt
  · exact hf x hx


end AlgebraicGeometry

end
