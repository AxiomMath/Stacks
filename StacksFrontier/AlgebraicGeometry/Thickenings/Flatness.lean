module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.Stalks
public import StacksFrontier.AlgebraicGeometry.Thickenings
public import StacksFrontier.AlgebraicGeometry.Perfect.BaseChangeStalk
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Basic
public import StacksFrontier.RingTheory.Flat.FibrewiseCriterion

/-!
# Flatness of a morphism of thickenings

In a morphism of thickenings over a finite-order thickening of bases, assume that
both closed fibres are obtained by base change. If the upper source is flat over
the thickened base and the morphism on closed fibres is flat, then the upper
morphism is flat. The upper target is flat over the thickened base at every point
reached by the upper morphism.

## Main results

* `AlgebraicGeometry.flat_of_flat_reduction` gives flatness of the upper morphism.
* `AlgebraicGeometry.flatAt_target_of_flat_reduction` gives flatness of the upper target
  over the thickened base at points in the image.

## Implementation notes

The two fibre-product assumptions are expressed by
`CategoryTheory.IsPullback`. The three thickenings, including finite order of the
base thickening, are explicit; they are `Stacks.Thickenings.IsThickening` and
`Stacks.Thickenings.IsFiniteOrderThickening` ([Stacks, Tag 04EX]). Flatness at a
point is `AlgebraicGeometry.IsFlatAt` ([Stacks, Tag 02N3]). The two independent
conclusions of the source lemma are stated separately.

Both are reduced to the local statement by `AlgebraicGeometry.Flat.of_stalkMap`,
and the local statement is the fibrewise criterion of flatness over a ring with
nilpotent ideal. The stalk of a fibre product is presented as a localization of
the tensor product of the stalks by
`AlgebraicGeometry.BaseChangeStalk.pullback_stalk_isLocalization`, which is what identifies the
stalks of the closed fibres with the base changes the hypotheses provide.

## References

* [Stacks Project, Tag 06AF](https://stacks.math.columbia.edu/tag/06AF)
* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
* [Stacks Project, Tag 02N3](https://stacks.math.columbia.edu/tag/02N3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Thickenings

namespace AlgebraicGeometry

universe u

variable {X X' Y Y' S S' : Scheme.{u}}
  {iX : X ⟶ X'} {iY : Y ⟶ Y'} {iS : S ⟶ S'}
  {f : X ⟶ Y} {f' : X' ⟶ Y'}
  {pX : X ⟶ S} {pX' : X' ⟶ S'}
  {pY : Y ⟶ S} {pY' : Y' ⟶ S'}

private theorem stalkMap_ker_localized
    {Z Z' : Scheme.{u}} (i : Z ⟶ Z') [IsClosedImmersion i] (z : Z)
    (U : Z'.Opens) (hU : IsAffineOpen U) (V : Z.Opens) (hV : IsAffineOpen V)
    (hVU : V ≤ i ⁻¹ᵁ U) (hz : z ∈ V)
    (hgsurj : Function.Surjective (i.appLE U V hVU).hom) :
    let p := hU.primeIdealOf ⟨i z, hVU hz⟩
    let _q := hV.primeIdealOf ⟨z, hz⟩
    let g := (i.appLE U V hVU).hom
    let e := (asIso (IsAffineOpen.arrowStalkMapIso i U hU V hV hVU hz).hom.left)
      |>.commRingCatIsoToRingEquiv
    Ideal.map e.toRingHom (RingHom.ker (i.stalkMap z).hom) =
      Ideal.map (algebraMap Γ(Z', U) (Localization.AtPrime p.asIdeal))
        (RingHom.ker g) := by
  classical
  dsimp only
  have hizU : i z ∈ U := hVU hz
  let p := hU.primeIdealOf ⟨i z, hizU⟩
  let q := hV.primeIdealOf ⟨z, hz⟩
  let g := (i.appLE U V hVU).hom
  have hcomap : p.asIdeal = Ideal.comap g q.asIdeal :=
    congr($(IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hz).1).symm
  let loc := Localization.localRingHom p.asIdeal q.asIdeal g hcomap
  let hArrow := IsAffineOpen.arrowStalkMapIso i U hU V hV hVU hz
  let e₁ := (asIso hArrow.hom.left).commRingCatIsoToRingEquiv
  let e₂ := (asIso hArrow.hom.right).commRingCatIsoToRingEquiv
  have hcomm (a : Z'.presheaf.stalk (i z)) :
      loc (e₁ a) = e₂ ((i.stalkMap z).hom a) := by
    have hcat := hArrow.hom.w
    change (asIso hArrow.hom.left).hom ≫ CommRingCat.ofHom loc =
      CommRingCat.ofHom (i.stalkMap z).hom ≫ (asIso hArrow.hom.right).hom at hcat
    have hfun := CommRingCat.hom_ext_iff.mp hcat
    have h := congrArg (fun φ : Z'.presheaf.stalk (i z) →+* _ => φ a) hfun
    convert h using 1 <;> rfl
  have htransport :
      Ideal.map e₁.toRingHom (RingHom.ker (i.stalkMap z).hom) = RingHom.ker loc := by
    ext w
    rw [Ideal.mem_map_iff_of_surjective e₁.toRingHom e₁.surjective]
    constructor
    · rintro ⟨a, ha, rfl⟩
      rw [RingHom.mem_ker] at ha ⊢
      change loc (e₁ a) = 0
      rw [hcomm a, ha]
      exact map_zero _
    · intro hw
      obtain ⟨a, rfl⟩ := e₁.surjective w
      refine ⟨a, ?_, rfl⟩
      apply e₂.injective
      rw [RingHom.mem_ker] at hw
      simpa [hw] using (hcomm a).symm
  have hT' : Submonoid.map g (Ideal.comap g q.asIdeal).primeCompl =
      q.asIdeal.primeCompl := Ideal.map_primeCompl_comap_of_surjective g hgsurj q.asIdeal
  have hT : Submonoid.map g p.asIdeal.primeCompl = q.asIdeal.primeCompl := by
    simpa only [hcomap] using hT'
  have hkerLoc : RingHom.ker loc =
      Ideal.map (algebraMap Γ(Z', U) (Localization.AtPrime p.asIdeal))
        (RingHom.ker g) := by
    simpa [loc, Localization.localRingHom] using
      (IsLocalization.ker_map (Localization.AtPrime q.asIdeal) g hT)
  rw [htransport, hkerLoc]

private theorem stalkCongr_eqToHom_of_eq {X : TopCat}
    (F : X.Presheaf CommRingCat) {x y : X} (h : x = y) :
    (F.stalkCongr (.of_eq h)).hom = eqToHom (congrArg F.stalk h) := by
  subst y
  simp [TopCat.Presheaf.stalkCongr]

private theorem flat_ringHom_of_ringEquiv
    {A B C D : Type*} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    (eA : A ≃+* C) (eB : B ≃+* D) (f : A →+* B) (g : C →+* D)
    (h : eB.toRingHom.comp f = g.comp eA.toRingHom) (hg : g.Flat) : f.Flat := by
  have h₁ : (g.comp eA.toRingHom).Flat :=
    (RingHom.Flat.comp_iff_of_bijective_right eA.bijective).2 hg
  rw [← h] at h₁
  exact (RingHom.Flat.comp_iff_of_bijective_left eB.bijective).1 h₁

private theorem map_ker_of_ringEquiv_square
    {A B C D : Type*} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    (eA : A ≃+* C) (eB : B ≃+* D) (f : A →+* B) (g : C →+* D)
    (h : eB.toRingHom.comp f = g.comp eA.toRingHom) :
    Ideal.map eA.toRingHom (RingHom.ker f) = RingHom.ker g := by
  ext c
  rw [Ideal.mem_map_iff_of_surjective eA.toRingHom eA.surjective]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [RingHom.mem_ker] at ha ⊢
    have hc := DFunLike.congr_fun h a
    simpa [ha] using hc.symm
  · intro hc
    obtain ⟨a, rfl⟩ := eA.surjective c
    refine ⟨a, ?_, rfl⟩
    rw [RingHom.mem_ker] at hc ⊢
    have hd := DFunLike.congr_fun h a
    apply eB.injective
    simpa [hc] using hd

private theorem nilpotent_ker_precomp_equiv
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    (e : R ≃+* A) (φ : A →+* B) (hφ : IsNilpotent (RingHom.ker φ)) :
    IsNilpotent (RingHom.ker (φ.comp e.toRingHom)) := by
  obtain ⟨n, hn⟩ := hφ
  refine ⟨n, le_bot_iff.mp ?_⟩
  rw [← RingHom.comap_ker φ e.toRingHom]
  calc
    (RingHom.ker φ).comap e.toRingHom ^ n ≤ (RingHom.ker φ ^ n).comap e.toRingHom :=
      Ideal.le_comap_pow e.toRingHom n
    _ = ⊥ := by rw [hn, Ideal.zero_eq_bot, Ideal.comap_bot_of_injective e.toRingHom e.injective]

private theorem stalkMap_ker_isNilpotent_of_finiteOrder
    {Z Z' : Scheme.{u}} {i : Z ⟶ Z'}
    (hi : IsFiniteOrderThickening i) (z : Z) :
    IsNilpotent (RingHom.ker (i.stalkMap z).hom) := by
  have : IsClosedImmersion i := hi.1
  obtain ⟨_, ⟨U, hU, rfl⟩, hiz, _⟩ :=
    Z'.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (i z)) isOpen_univ
  let V : Z.Opens := i ⁻¹ᵁ U
  let Ua : Z'.affineOpens := ⟨U, hU⟩
  have hV : IsAffineOpen V := hU.preimage i
  have hzV : z ∈ V := hiz
  let hVU : V ≤ i ⁻¹ᵁ U := le_rfl
  let g : Γ(Z', U) →+* Γ(Z, V) := (i.appLE U V hVU).hom
  have hgsurj : Function.Surjective g := by
    simpa [g, V, hVU, Scheme.Hom.appLE] using i.app_surjective U hU
  obtain ⟨n, hn⟩ := hi.2
  have hpow : (RingHom.ker g) ^ (n + 1) = ⊥ := by
    have happ : g = (i.app U).hom := by
      simp [g, V, Scheme.Hom.appLE]
    have hker : i.ker.ideal Ua = RingHom.ker g := by
      rw [Scheme.Hom.ker_apply, happ]
    have h := congrArg (fun J : Z'.IdealSheafData => J.ideal Ua) hn
    rw [Scheme.IdealSheafData.ideal_pow] at h
    simpa [Scheme.IdealSheafData.ideal_bot, hker, happ] using h
  let e₁ := (asIso (IsAffineOpen.arrowStalkMapIso i U hU V hV hVU hzV).hom.left)
    |>.commRingCatIsoToRingEquiv
  have hkerTransport := stalkMap_ker_localized i z U hU V hV hVU hzV hgsurj
  have hmapPow : Ideal.map e₁.toRingHom
        ((RingHom.ker (i.stalkMap z).hom) ^ (n + 1)) = Ideal.map e₁.toRingHom ⊥ := by
    rw [Ideal.map_pow, hkerTransport, ← Ideal.map_pow, hpow, Ideal.map_bot, Ideal.map_bot]
  exact ⟨n + 1, (Ideal.map_eq_bot_iff_of_injective e₁.injective).mp
    (hmapPow.trans Ideal.map_bot)⟩

private theorem localization_isIso_of_local
    {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra (TensorProduct R A B) C]
    [IsLocalRing A] [IsLocalRing (TensorProduct R A B)] [IsLocalRing C]
    (M : Submonoid (TensorProduct R A B)) [IsLocalization M C]
    (φ : TensorProduct R A B →+* C)
    (hφ : φ = algebraMap (TensorProduct R A B) C)
    (hleft : IsLocalHom (φ.comp Algebra.TensorProduct.includeLeftRingHom))
    (hB : Function.Surjective (algebraMap R B)) : Function.Bijective φ := by
  let : IsLocalHom φ := by
    refine ⟨fun t htu => ?_⟩
    obtain ⟨a, rfl⟩ :=
      (Algebra.TensorProduct.includeLeft_surjective
        (R := R) (T := B) A A hB) t
    change IsUnit ((φ.comp Algebra.TensorProduct.includeLeftRingHom) a) at htu
    exact (hleft.map_nonunit a htu).map
      Algebra.TensorProduct.includeLeftRingHom
  have hM : M ≤ IsUnit.submonoid (TensorProduct R A B) := by
    intro x hx
    apply (isUnit_map_iff φ x).mp
    simpa only [hφ] using (IsLocalization.map_units C ⟨x, hx⟩)
  let e : TensorProduct R A B ≃ₐ[TensorProduct R A B] C :=
    IsLocalization.atUnits (TensorProduct R A B) M hM
  rw [hφ]
  exact e.toRingEquiv.bijective

private theorem pullback_stalk_quotient_equiv
    {Z W W' : Scheme.{u}} (f : Z ⟶ W') (g : W ⟶ W')
    [IsClosedImmersion g] (t : (pullback f g).carrier) :
    let pZ : pullback f g ⟶ Z := pullback.fst f g
    let pW : pullback f g ⟶ W := pullback.snd f g
    let h : (pZ ≫ f).base t = (pW ≫ g).base t :=
      congrArg (fun k : pullback f g ⟶ W' => k.base t) pullback.condition
    let R := W'.presheaf.stalk ((pZ ≫ f).base t)
    let A := Z.presheaf.stalk (pZ.base t)
    let B := W.presheaf.stalk (pW.base t)
    let C := (pullback f g).presheaf.stalk t
    let : Algebra R A := (f.stalkMap (pZ.base t)).hom.toAlgebra
    let : Algebra R B :=
      ((eqToHom (congrArg W'.presheaf.stalk h)) ≫ g.stalkMap (pW.base t)).hom.toAlgebra
    let : Algebra A C := (pZ.stalkMap t).hom.toAlgebra
    let I : Ideal R := RingHom.ker (algebraMap R B)
    ∃ e : (A ⧸ Ideal.map (algebraMap R A) I) ≃ₐ[A] C,
      ∀ a, e (Ideal.Quotient.mk _ a) = (pZ.stalkMap t).hom a := by
  classical
  dsimp only
  let pZ : pullback f g ⟶ Z := pullback.fst f g
  let pW : pullback f g ⟶ W := pullback.snd f g
  let h : (pZ ≫ f).base t = (pW ≫ g).base t :=
    congrArg (fun k : pullback f g ⟶ W' => k.base t) pullback.condition
  let R := W'.presheaf.stalk ((pZ ≫ f).base t)
  let A := Z.presheaf.stalk (pZ.base t)
  let B := W.presheaf.stalk (pW.base t)
  let C := (pullback f g).presheaf.stalk t
  let : Algebra R A := (f.stalkMap (pZ.base t)).hom.toAlgebra
  let : Algebra R B :=
    ((eqToHom (congrArg W'.presheaf.stalk h)) ≫ g.stalkMap (pW.base t)).hom.toAlgebra
  let : Algebra A C := (pZ.stalkMap t).hom.toAlgebra
  let : Algebra B C := (pW.stalkMap t).hom.toAlgebra
  have hloc := BaseChangeStalk.pullback_stalk_isLocalization f g t
  dsimp only [pZ, pW, R, A, B, C] at hloc
  obtain ⟨φ, hφA, hφB, M, hM⟩ := hloc
  let T := TensorProduct R A B
  let : Algebra R T := Algebra.TensorProduct.leftAlgebra
  let : Algebra A T := Algebra.TensorProduct.leftAlgebra
  let : Algebra B T := Algebra.TensorProduct.rightAlgebra
  let : Algebra T C := φ.toAlgebra
  let : IsLocalization M C := hM
  let : IsScalarTower A T C := IsScalarTower.of_algebraMap_eq' (by
    ext a
    change (pZ.stalkMap t).hom a = φ (Algebra.TensorProduct.includeLeftRingHom a)
    exact (DFunLike.congr_fun hφA a).symm)
  let : IsScalarTower B T C := IsScalarTower.of_algebraMap_eq' (by
    ext b
    change (pW.stalkMap t).hom b = φ (Algebra.TensorProduct.includeRight.toRingHom b)
    exact (DFunLike.congr_fun hφB b).symm)
  let I : Ideal R := RingHom.ker (algebraMap R B)
  have hBsurj : Function.Surjective (algebraMap R B) := by
    change Function.Surjective
      (((eqToHom (congrArg W'.presheaf.stalk h)) ≫ g.stalkMap (pW.base t)).hom)
    exact (g.stalkMap_surjective (pW.base t)).comp
      (ConcreteCategory.bijective_of_isIso (eqToHom (congrArg W'.presheaf.stalk h))).2
  have : Nontrivial T := nontrivial_of_ne 0 1 fun h01 =>
    zero_ne_one (α := C) (by simpa only [map_zero, map_one] using congrArg φ h01)
  have hinc : Function.Surjective (Algebra.TensorProduct.includeLeftRingHom : A →+* T) :=
    Algebra.TensorProduct.includeLeft_surjective (R := R) (T := B) A A hBsurj
  let : IsLocalRing T := IsLocalRing.of_surjective'
    Algebra.TensorProduct.includeLeftRingHom hinc
  have hleft : IsLocalHom (φ.comp Algebra.TensorProduct.includeLeftRingHom) := by
    rw [hφA]
    infer_instance
  have hbij := localization_isIso_of_local M φ rfl hleft hBsurj
  let eT : T ≃ₐ[A] C := AlgEquiv.ofBijective
    ((Algebra.ofId T C).restrictScalars A) hbij
  let q : (R ⧸ I) ≃ₐ[R] B :=
    Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R B) hBsurj
  let eTensor : TensorProduct R A (R ⧸ I) ≃ₐ[A] T :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : (↑A) ≃ₐ[(↑A)] (↑A)) q
  let eQuot : (A ⧸ Ideal.map (algebraMap R A) I) ≃ₐ[A]
      TensorProduct R A (R ⧸ I) :=
    Algebra.TensorProduct.quotIdealMapEquivTensorQuot A I
  refine ⟨eQuot.trans (eTensor.trans eT), ?_⟩
  intro a
  change eT (eTensor (eQuot (Ideal.Quotient.mk _ a))) = (pZ.stalkMap t).hom a
  unfold eQuot
  rw [Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk]
  have ht : eTensor (a ⊗ₜ[R] (1 : R ⧸ I)) =
      Algebra.TensorProduct.includeLeftRingHom a := by
    change Algebra.TensorProduct.map
      (AlgEquiv.refl : (↑A) ≃ₐ[(↑A)] (↑A)).toAlgHom q.toAlgHom
        (a ⊗ₜ[R] (1 : R ⧸ I)) = Algebra.TensorProduct.includeLeftRingHom a
    rw [Algebra.TensorProduct.map_tmul]
    simp [Algebra.TensorProduct.includeLeftRingHom_apply]
  change (algebraMap T C) (eTensor (a ⊗ₜ[R] (1 : R ⧸ I))) =
    (pZ.stalkMap t).hom a
  rw [ht]
  change φ (Algebra.TensorProduct.includeLeftRingHom a) = (pZ.stalkMap t).hom a
  rw [← hφA]
  rfl

private theorem pullback_square_stalk_quotient_equiv
    {A A' B B' : Scheme.{u}} {iA : A ⟶ A'} {f : A ⟶ B}
    {g : A' ⟶ B'} {iB : B ⟶ B'}
    (h : IsPullback iA f g iB) [IsClosedImmersion iB] (a : A) :
    let t := h.isoPullback.hom a
    let pA := pullback.fst g iB
    let pB := pullback.snd g iB
    let z := pA.base t
    let w := pB.base t
    let hpa : z = iA a := by
      change (h.isoPullback.hom ≫ pA).base a = iA a
      rw [h.isoPullback_hom_fst]
    let hpt : (pA ≫ g).base t = (pB ≫ iB).base t :=
      congrArg (fun k : pullback g iB ⟶ B' => k.base t) pullback.condition
    let R := B'.presheaf.stalk ((pA ≫ g).base t)
    let D := A'.presheaf.stalk z
    let : Algebra R D := (g.stalkMap z).hom.toAlgebra
    let E := B.presheaf.stalk w
    let : Algebra R E :=
      ((eqToHom (congrArg B'.presheaf.stalk hpt) ≫ iB.stalkMap w).hom.toAlgebra)
    let I := RingHom.ker (algebraMap R E)
    ∃ e : (D ⧸ Ideal.map (algebraMap R D) I) ≃+* A.presheaf.stalk a,
      ∀ d, e (Ideal.Quotient.mk _ d) =
        (iA.stalkMap a).hom ((eqToHom (congrArg A'.presheaf.stalk hpa)) d) := by
  classical
  dsimp only
  let t := h.isoPullback.hom a
  let pA : pullback g iB ⟶ A' := pullback.fst g iB
  let pB : pullback g iB ⟶ B := pullback.snd g iB
  let z := pA.base t
  let w := pB.base t
  have hpa : z = iA a := by
    change (h.isoPullback.hom ≫ pA).base a = iA a
    rw [h.isoPullback_hom_fst]
  have hpt : (pA ≫ g).base t = (pB ≫ iB).base t :=
    congrArg (fun k : pullback g iB ⟶ B' => k.base t) pullback.condition
  let R := B'.presheaf.stalk ((pA ≫ g).base t)
  let D := A'.presheaf.stalk z
  let : Algebra R D := (g.stalkMap z).hom.toAlgebra
  let E := B.presheaf.stalk w
  let : Algebra R E :=
    ((eqToHom (congrArg B'.presheaf.stalk hpt) ≫ iB.stalkMap w).hom.toAlgebra)
  let I := RingHom.ker (algebraMap R E)
  let : Algebra D ((pullback g iB).presheaf.stalk t) :=
    (pA.stalkMap t).hom.toAlgebra
  have hbase := pullback_stalk_quotient_equiv g iB t
  dsimp only [pA, pB, R, D, z, w, t] at hbase
  obtain ⟨ePB, hePB⟩ := hbase
  let u := h.isoPullback.hom
  let eIso := (asIso (u.stalkMap a)).commRingCatIsoToRingEquiv
  refine ⟨ePB.toRingEquiv.trans eIso, ?_⟩
  intro d
  change eIso (ePB (Ideal.Quotient.mk _ d)) =
    (iA.stalkMap a).hom ((eqToHom (congrArg A'.presheaf.stalk hpa)) d)
  rw [hePB]
  have hu : u ≫ pA = iA := h.isoPullback_hom_fst
  have hpoint : (u ≫ pA).base a = iA a :=
    congrArg (fun k : A ⟶ A' => k.base a) hu
  have hs := (Scheme.Hom.stalkMap_comp u pA a).symm.trans
    (Scheme.Hom.stalkMap_congr_hom (u ≫ pA) iA hu a)
  have hs' : pA.stalkMap t ≫ u.stalkMap a =
      eqToHom (congrArg A'.presheaf.stalk hpa) ≫ iA.stalkMap a := by
    rw [stalkCongr_eqToHom_of_eq A'.presheaf hpoint] at hs
    change pA.stalkMap t ≫ u.stalkMap a =
      eqToHom (congrArg A'.presheaf.stalk hpa) ≫ iA.stalkMap a at hs
    exact hs
  exact congrArg (fun q : CommRingCat.Hom _ _ => q.hom d) hs'

/-- Stalk identifications along `a = b` (inverted) and `a = c` compose to the one along `b = c`. -/
private theorem eqToHom_comp_symm_equiv {X : TopCat} (F : X.Presheaf CommRingCat) {a b c : X}
    (h₁ : a = b) (h₂ : a = c) (h₃ : b = c) :
    (eqToHom (congrArg F.stalk h₂)).hom.comp
      (asIso (eqToHom (congrArg F.stalk h₁))).commRingCatIsoToRingEquiv.symm.toRingHom =
      (eqToHom (congrArg F.stalk h₃)).hom := by
  subst h₁ h₂
  ext
  simp only [eqToHom_refl, CommRingCat.hom_id, RingEquiv.toRingHom_eq_coe,
    RingHomCompTriple.comp_eq, RingHom.coe_coe, RingHom.id_apply]
  rw [RingEquiv.symm_apply_eq]
  rfl

/-- Stalk maps commute with the stalk identifications along an equality of points. -/
private theorem stalkMap_eqToHom_square {P Q : Scheme.{u}} (g : P ⟶ Q) {a c : P} {r : Q}
    (hac : a = c) (hr : g a = r) (h : r = g c) :
    (asIso (eqToHom (congrArg P.presheaf.stalk hac))).commRingCatIsoToRingEquiv.toRingHom.comp
        (g.stalkMap a).hom =
      ((g.stalkMap c).hom.comp (eqToHom (congrArg Q.presheaf.stalk h)).hom).comp
        (asIso (eqToHom (congrArg Q.presheaf.stalk hr))).commRingCatIsoToRingEquiv.toRingHom := by
  subst hac hr
  rfl

/-- Stalk maps of a closed immersion commute with the stalk identifications along equal points. -/
private theorem stalkMap_eqToHom_comp_square {S S' : Scheme.{u}} (i : S ⟶ S') {r₁ r₂ : S'}
    {w s : S} (h₁ : r₁ = i w) (h₂ : r₂ = i s) (hw : w = s) (hr : r₁ = r₂) :
    (asIso (eqToHom (congrArg S.presheaf.stalk hw))).commRingCatIsoToRingEquiv.toRingHom.comp
        (eqToHom (congrArg S'.presheaf.stalk h₁) ≫ i.stalkMap w).hom =
      (eqToHom (congrArg S'.presheaf.stalk h₂) ≫ i.stalkMap s).hom.comp
        (asIso (eqToHom (congrArg S'.presheaf.stalk hr))).commRingCatIsoToRingEquiv.toRingHom := by
  subst hw hr h₁
  rfl

/-- Pushing an ideal through a commuting square of ring homs whose bottom row is an
equivalence. -/
private theorem map_map_of_comp_eq {A B C D : Type*} [CommRing A] [CommRing B] [CommRing C]
    [CommRing D] (eA : A ≃+* C) (eB : B ≃+* D) (f : A →+* B) (g : C →+* D)
    (h : eB.toRingHom.comp f = g.comp eA.toRingHom) (I : Ideal A) :
    Ideal.map eB.toRingHom (Ideal.map f I) = Ideal.map g (Ideal.map eA.toRingHom I) := by
  rw [Ideal.map_map, Ideal.map_map, h]

/-- Passing from `D ⧸ K` to `D' ⧸ J` along an equivalence and a further identification. -/
private theorem quotientEquiv_symm_trans_mk {D D' E : Type*} [CommRing D] [CommRing D']
    [CommRing E] (K : Ideal D) (J : Ideal D') (e : D ≃+* D') (hK : Ideal.map e.toRingHom K = J)
    (eX : (D ⧸ K) ≃+* E) (m : D') :
    ((Ideal.quotientEquiv K J e hK.symm).symm.trans eX) (Ideal.Quotient.mk J m) =
      eX (Ideal.Quotient.mk K (e.symm m)) := by
  subst hK
  rw [RingEquiv.trans_apply]
  congr 1

/-- The stalk map of a flat morphism, precomposed with a stalk identification, is flat. -/
private theorem flat_eqToHom_stalkMap {X S : Scheme.{u}} (p : X ⟶ S) (hp : Flat p) (x : X)
    {r : S} (h : r = p x) : (eqToHom (congrArg S.presheaf.stalk h) ≫ p.stalkMap x).hom.Flat := by
  have hflat : (p.stalkMap x).hom.Flat := by
    let : Flat p := hp
    exact Flat.stalkMap p x
  exact (RingHom.Flat.comp_iff_of_bijective_right
    (ConcreteCategory.bijective_of_isIso (eqToHom (congrArg S.presheaf.stalk h)))).2 hflat

/-- Stalk maps of a composite, expressed through the stalk identification of the base. -/
private theorem stalkMap_comp_eq_eqToHom_comp {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    {k : X ⟶ S} (hk : f ≫ g = k) (x : X) (h : g (f x) = k x) :
    g.stalkMap (f x) ≫ f.stalkMap x = eqToHom (congrArg S.presheaf.stalk h) ≫ k.stalkMap x := by
  subst hk
  rw [Scheme.Hom.stalkMap_comp]
  exact (Category.id_comp _).symm

private theorem flat_stalk_map_of_flat_reduction
    (hiX : IsThickening iX)
    (_hiY : IsThickening iY)
    (hiS : IsFiniteOrderThickening iS)
    (hX : IsPullback iX pX pX' iS)
    (hY : IsPullback iY pY pY' iS)
    (hf : iX ≫ f' = f ≫ iY)
    (hfbase : f ≫ pY = pX)
    (hf'base : f' ≫ pY' = pX')
    (hflatX' : Flat pX') (hflatf : Flat f)
    (x' : X') : (f'.stalkMap x').hom.Flat := by
  let : IsClosedImmersion iX := hiX.1
  let : IsClosedImmersion iY := _hiY.1
  let : IsClosedImmersion iS := hiS.1
  obtain ⟨x, hx⟩ := hiX.2 x'
  have hxy : iY (f x) = f' x' := by
    have h := congrArg (fun k : X ⟶ Y' => k.base x) hf
    change f' (iX x) = iY (f x) at h
    rw [hx] at h
    exact h.symm
  let R := S'.presheaf.stalk (pY' (f' x'))
  let T := Y'.presheaf.stalk (f' x')
  let M := X'.presheaf.stalk x'
  have hR : pY' (f' x') = pX' x' := congrArg (fun k : X' ⟶ S' => k.base x') hf'base
  let : Algebra R T := (pY'.stalkMap (f' x')).hom.toAlgebra
  let : Algebra T M := (f'.stalkMap x').hom.toAlgebra
  let : Algebra R M :=
    ((eqToHom (congrArg S'.presheaf.stalk hR) ≫ pX'.stalkMap x').hom.toAlgebra)
  have hcomp := stalkMap_comp_eq_eqToHom_comp f' pY' hf'base x' hR
  let : IsScalarTower R T M := IsScalarTower.of_algebraMap_eq' (by
    ext r
    change (((eqToHom (congrArg S'.presheaf.stalk hR) ≫ pX'.stalkMap x').hom) r) =
      ((f'.stalkMap x').hom ((pY'.stalkMap (f' x')).hom r))
    exact (DFunLike.congr_fun
      (congrArg (fun q : CommRingCat.Hom _ _ => q.hom) hcomp).symm r))
  let s := pY (f x)
  have hred : pY' (f' x') = iS s := by
    calc
      pY' (f' x') = pY' (iY (f x)) := congrArg pY' hxy.symm
      _ = iS (pY (f x)) := by
        have h := congrArg (fun k : Y ⟶ S' => k.base (f x)) hY.w
        change pY' (iY (f x)) = iS (pY (f x)) at h
        exact h
  let R₀ := S.presheaf.stalk s
  let : Algebra R R₀ :=
    ((eqToHom (congrArg S'.presheaf.stalk hred) ≫ iS.stalkMap s).hom.toAlgebra)
  let I : Ideal R := RingHom.ker (algebraMap R R₀)
  have hI : IsNilpotent I := by
    let eRed := (asIso (eqToHom (congrArg S'.presheaf.stalk hred)))
      |>.commRingCatIsoToRingEquiv
    have hker := stalkMap_ker_isNilpotent_of_finiteOrder hiS s
    change IsNilpotent (RingHom.ker ((iS.stalkMap s).hom.comp eRed.toRingHom))
    exact nilpotent_ker_precomp_equiv eRed (iS.stalkMap s).hom hker
  have hflatRM : Module.Flat R M :=
    RingHom.flat_algebraMap_iff.mp (flat_eqToHom_stalkMap pX' hflatX' x' hR)
  let J_T := Ideal.map (algebraMap R T) I
  let J_M := Ideal.map (algebraMap R M) I
  have hmap : Ideal.map (algebraMap T M) J_T = J_M := by
    dsimp [J_T, J_M]
    rw [Ideal.map_map, IsScalarTower.algebraMap_eq R T M]
  have hJ : J_T • (⊤ : Submodule T M) = J_M.restrictScalars T := by
    rw [Ideal.smul_top_eq_map]
    rw [hmap]
  let qmap : (T ⧸ J_T) →+* (M ⧸ J_M) :=
    Ideal.Quotient.lift J_T ((Ideal.Quotient.mk J_M).comp (algebraMap T M)) (by
      intro a ha
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      have hm : (algebraMap T M) a ∈ Ideal.map (algebraMap T M) J_T :=
        Ideal.mem_map_of_mem _ ha
      rwa [hmap] at hm)
  let : Algebra (T ⧸ J_T) (M ⧸ J_M) := qmap.toAlgebra
  have hS : pX x = pY (f x) := by
    have h := congrArg (fun k : X ⟶ S => k.base x) hfbase
    change pY (f x) = pX x at h
    exact h.symm
  have hpx : (pullback.fst pX' iS) (hX.isoPullback.hom x) = iX x := by
    change (hX.isoPullback.hom ≫ pullback.fst pX' iS) x = iX x
    rw [hX.isoPullback_hom_fst]
  have hpxB : (pullback.snd pX' iS) (hX.isoPullback.hom x) = pX x := by
    change (hX.isoPullback.hom ≫ pullback.snd pX' iS) x = pX x
    rw [hX.isoPullback_hom_snd]
  have hpy : (pullback.fst pY' iS) (hY.isoPullback.hom (f x)) = iY (f x) := by
    change (hY.isoPullback.hom ≫ pullback.fst pY' iS) (f x) = iY (f x)
    rw [hY.isoPullback_hom_fst]
  have hpyB : (pullback.snd pY' iS) (hY.isoPullback.hom (f x)) = pY (f x) := by
    change (hY.isoPullback.hom ≫ pullback.snd pY' iS) (f x) = pY (f x)
    rw [hY.isoPullback_hom_snd]
  obtain ⟨eX, heX⟩ := pullback_square_stalk_quotient_equiv hX x
  obtain ⟨eY, heY⟩ := pullback_square_stalk_quotient_equiv hY (f x)
  let tX := hX.isoPullback.hom x
  let pAX : pullback pX' iS ⟶ X' := pullback.fst pX' iS
  let pBX : pullback pX' iS ⟶ S := pullback.snd pX' iS
  let zX := pAX.base tX
  let wX := pBX.base tX
  let hptX : pX' zX = iS wX := by
    change (pAX ≫ pX').base tX = (pBX ≫ iS).base tX
    exact congrArg (fun k : pullback pX' iS ⟶ S' => k.base tX) pullback.condition
  let RX := S'.presheaf.stalk (pX' zX)
  let DX := X'.presheaf.stalk zX
  let EX := S.presheaf.stalk wX
  let : Algebra RX DX := (pX'.stalkMap zX).hom.toAlgebra
  let : Algebra RX EX :=
    ((eqToHom (congrArg S'.presheaf.stalk hptX) ≫ iS.stalkMap wX).hom.toAlgebra)
  let IX : Ideal RX := RingHom.ker (algebraMap RX EX)
  let KX : Ideal DX := Ideal.map (algebraMap RX DX) IX
  have heX' : (DX ⧸ KX) ≃+* X.presheaf.stalk x := eX
  let tY := hY.isoPullback.hom (f x)
  let pAY : pullback pY' iS ⟶ Y' := pullback.fst pY' iS
  let pBY : pullback pY' iS ⟶ S := pullback.snd pY' iS
  let zY := pAY.base tY
  let wY := pBY.base tY
  let hptY : pY' zY = iS wY := by
    change (pAY ≫ pY').base tY = (pBY ≫ iS).base tY
    exact congrArg (fun k : pullback pY' iS ⟶ S' => k.base tY) pullback.condition
  let RY := S'.presheaf.stalk (pY' zY)
  let DY := Y'.presheaf.stalk zY
  let EY := S.presheaf.stalk wY
  let : Algebra RY DY := (pY'.stalkMap zY).hom.toAlgebra
  let : Algebra RY EY :=
    ((eqToHom (congrArg S'.presheaf.stalk hptY) ≫ iS.stalkMap wY).hom.toAlgebra)
  let IY : Ideal RY := RingHom.ker (algebraMap RY EY)
  let KY : Ideal DY := Ideal.map (algebraMap RY DY) IY
  have heY' : (DY ⧸ KY) ≃+* Y.presheaf.stalk (f x) := eY
  have hDX : zX = x' := hpx.trans hx
  have hDY : zY = f' x' := hpy.trans hxy
  have hRX : pX' zX = pY' (f' x') := by
    calc
      pX' zX = pX' (iX x) := congrArg pX' hpx
      _ = pX' x' := congrArg pX' hx
      _ = pY' (f' x') := hR.symm
  have hRY : pY' zY = pY' (f' x') := by
    calc
      pY' zY = pY' (iY (f x)) := congrArg pY' hpy
      _ = pY' (f' x') := congrArg pY' hxy
  have hEX : wX = s := by
    change (pullback.snd pX' iS) (hX.isoPullback.hom x) = pY (f x)
    rw [hpxB]
    exact hS
  have hEY : wY = s := by
    change (pullback.snd pY' iS) (hY.isoPullback.hom (f x)) = pY (f x)
    rw [hpyB]
  let eDX := (asIso (eqToHom (congrArg X'.presheaf.stalk hDX))).commRingCatIsoToRingEquiv
  let eDY := (asIso (eqToHom (congrArg Y'.presheaf.stalk hDY))).commRingCatIsoToRingEquiv
  let eRX := (asIso (eqToHom (congrArg S'.presheaf.stalk hRX))).commRingCatIsoToRingEquiv
  let eRY := (asIso (eqToHom (congrArg S'.presheaf.stalk hRY))).commRingCatIsoToRingEquiv
  let eEX := (asIso (eqToHom (congrArg S.presheaf.stalk hEX))).commRingCatIsoToRingEquiv
  let eEY := (asIso (eqToHom (congrArg S.presheaf.stalk hEY))).commRingCatIsoToRingEquiv
  let aX : RX →+* DX := (pX'.stalkMap zX).hom
  let aR : R →+* M := (pX'.stalkMap x').hom.comp
    (eqToHom (congrArg S'.presheaf.stalk hR)).hom
  have hAX : eDX.toRingHom.comp aX = aR.comp eRX.toRingHom :=
    stalkMap_eqToHom_square pX' hDX hRX hR
  let bX : RX →+* EX :=
    ((eqToHom (congrArg S'.presheaf.stalk hptX) ≫ iS.stalkMap wX).hom)
  let bR : R →+* R₀ :=
    ((eqToHom (congrArg S'.presheaf.stalk hred) ≫ iS.stalkMap s).hom)
  have hBX : eEX.toRingHom.comp bX = bR.comp eRX.toRingHom :=
    stalkMap_eqToHom_comp_square iS hptX hred hEX hRX
  have hkerX : Ideal.map eRX.toRingHom IX = I := by
    simpa [IX, I, bX, bR, RingHom.algebraMap_toAlgebra] using
      map_ker_of_ringEquiv_square eRX eEX bX bR hBX
  have hKX : Ideal.map eDX.toRingHom KX = J_M := by
    rw [show KX = Ideal.map aX IX from rfl, map_map_of_comp_eq eRX eDX aX aR hAX, hkerX]
    rfl
  let aY : RY →+* DY := (pY'.stalkMap zY).hom
  let aT : R →+* T := (pY'.stalkMap (f' x')).hom
  have hAY : eDY.toRingHom.comp aY = aT.comp eRY.toRingHom :=
    stalkMap_eqToHom_square pY' hDY hRY rfl
  let bY : RY →+* EY :=
    ((eqToHom (congrArg S'.presheaf.stalk hptY) ≫ iS.stalkMap wY).hom)
  have hBY : eEY.toRingHom.comp bY = bR.comp eRY.toRingHom :=
    stalkMap_eqToHom_comp_square iS hptY hred hEY hRY
  have hkerY : Ideal.map eRY.toRingHom IY = I := by
    simpa [IY, I, bY, bR, RingHom.algebraMap_toAlgebra] using
      map_ker_of_ringEquiv_square eRY eEY bY bR hBY
  have hKY : Ideal.map eDY.toRingHom KY = J_T := by
    rw [show KY = Ideal.map aY IY from rfl, map_map_of_comp_eq eRY eDY aY aT hAY, hkerY]
    rfl
  let eXq : (M ⧸ J_M) ≃+* X.presheaf.stalk x :=
    (Ideal.quotientEquiv KX J_M eDX hKX.symm).symm.trans eX
  let eYq : (T ⧸ J_T) ≃+* Y.presheaf.stalk (f x) :=
    (Ideal.quotientEquiv KY J_T eDY hKY.symm).symm.trans eY
  have heXq (m : M) : eXq (Ideal.Quotient.mk J_M m) =
      (iX.stalkMap x).hom ((eqToHom (congrArg X'.presheaf.stalk hpx)).hom
        (eDX.symm m)) :=
    (quotientEquiv_symm_trans_mk KX J_M eDX hKX eX m).trans (heX (eDX.symm m))
  have heYq (t : T) : eYq (Ideal.Quotient.mk J_T t) =
      (iY.stalkMap (f x)).hom ((eqToHom (congrArg Y'.presheaf.stalk hpy)).hom
        (eDY.symm t)) :=
    (quotientEquiv_symm_trans_mk KY J_T eDY hKY eY t).trans (heY (eDY.symm t))
  have hpathX := eqToHom_comp_symm_equiv X'.presheaf hDX hpx hx.symm
  have hpathY := eqToHom_comp_symm_equiv Y'.presheaf hDY hpy hxy.symm
  have hstalkSquare :
      f'.stalkMap x' ≫ eqToHom (congrArg X'.presheaf.stalk hx.symm) ≫
          iX.stalkMap x =
        eqToHom (congrArg Y'.presheaf.stalk hxy.symm) ≫
          iY.stalkMap (f x) ≫ f.stalkMap x := by
    have hp := Scheme.Hom.stalkMap_congr_point f' x' (iX x) hx.symm
    rw [stalkCongr_eqToHom_of_eq X'.presheaf hx.symm,
      stalkCongr_eqToHom_of_eq Y'.presheaf (congrArg f' hx.symm)] at hp
    have hfhx : congrArg f' hx.symm = (congrArg f' hx).symm :=
      Subsingleton.elim _ _
    have hp' : f'.stalkMap x' ≫ eqToHom (congrArg X'.presheaf.stalk hx.symm) =
        eqToHom (congrArg Y'.presheaf.stalk (congrArg f' hx).symm) ≫
          f'.stalkMap (iX x) := by
      simpa only [hfhx] using hp
    have hxy' : (iX ≫ f') x = (f ≫ iY) x :=
      congrArg (fun k : X ⟶ Y' => k.base x) hf
    have hs := Scheme.Hom.stalkMap_congr_hom (iX ≫ f') (f ≫ iY) hf x
    rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp,
      stalkCongr_eqToHom_of_eq Y'.presheaf hxy'] at hs
    have hfpoint : (congrArg f' hx).symm.trans hxy' = hxy.symm :=
      Subsingleton.elim _ _
    calc
      _ = eqToHom (congrArg Y'.presheaf.stalk (congrArg f' hx).symm) ≫
          f'.stalkMap (iX x) ≫ iX.stalkMap x := by
            exact congrArg (fun q => q ≫ iX.stalkMap x) hp'
      _ = eqToHom (congrArg Y'.presheaf.stalk (congrArg f' hx).symm) ≫
          eqToHom (congrArg Y'.presheaf.stalk hxy') ≫
            iY.stalkMap (f x) ≫ f.stalkMap x := by
              exact congrArg (fun q =>
                eqToHom (congrArg Y'.presheaf.stalk (congrArg f' hx).symm) ≫ q) hs
      _ = _ := by
        calc
          _ = (eqToHom (congrArg Y'.presheaf.stalk (congrArg f' hx).symm) ≫
              eqToHom (congrArg Y'.presheaf.stalk hxy')) ≫
                iY.stalkMap (f x) ≫ f.stalkMap x := by rw [← Category.assoc]
          _ = eqToHom (congrArg Y'.presheaf.stalk
              ((congrArg f' hx).symm.trans hxy')) ≫
                iY.stalkMap (f x) ≫ f.stalkMap x := by rw [eqToHom_trans]
          _ = _ := by congr 1
  have hquotSquare : eXq.toRingHom.comp qmap =
      (f.stalkMap x).hom.comp eYq.toRingHom := by
    apply Ideal.Quotient.ringHom_ext
    ext t
    change eXq (Ideal.Quotient.mk J_M ((algebraMap T M) t)) =
      (f.stalkMap x).hom (eYq (Ideal.Quotient.mk J_T t))
    rw [heXq, heYq]
    change ((iX.stalkMap x).hom.comp
        ((eqToHom (congrArg X'.presheaf.stalk hpx)).hom.comp eDX.symm.toRingHom))
        ((f'.stalkMap x').hom t) =
      ((f.stalkMap x).hom.comp
        ((iY.stalkMap (f x)).hom.comp
          ((eqToHom (congrArg Y'.presheaf.stalk hpy)).hom.comp eDY.symm.toRingHom))) t
    rw [hpathX, hpathY]
    exact DFunLike.congr_fun
      (CommRingCat.hom_ext_iff.mp hstalkSquare) t
  have hflatQuot :
      Module.Flat (T ⧸ J_T) (M ⧸ (J_T • (⊤ : Submodule T M))) := by
    have hflatLower : (f.stalkMap x).hom.Flat := by
      let : Flat f := hflatf
      exact Flat.stalkMap f x
    have hflatq : qmap.Flat :=
      flat_ringHom_of_ringEquiv eYq eXq qmap (f.stalkMap x).hom hquotSquare hflatLower
    have hflatN : Module.Flat (T ⧸ J_T) (M ⧸ J_M) :=
      RingHom.flat_algebraMap_iff.mp hflatq
    let : Module T (M ⧸ J_M) := Module.compHom (M ⧸ J_M)
      ((algebraMap (T ⧸ J_T) (M ⧸ J_M)).comp (Ideal.Quotient.mk J_T))
    let eT : (M ⧸ (J_T • (⊤ : Submodule T M))) ≃ₗ[T]
        (M ⧸ (J_M.restrictScalars T)) :=
      Submodule.quotEquivOfEq _ _ hJ
    let e : (M ⧸ (J_T • (⊤ : Submodule T M))) ≃ₗ[T ⧸ J_T] (M ⧸ J_M) :=
      { toFun := eT
        invFun := eT.symm
        left_inv := eT.left_inv
        right_inv := eT.right_inv
        map_add' := eT.map_add
        map_smul' := by
          intro c z
          obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
          obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective
            (J_T • (⊤ : Submodule T M)) z
          change (algebraMap (T ⧸ J_T) (M ⧸ J_M) (Ideal.Quotient.mk J_T r)) •
              (Ideal.Quotient.mk J_M m) =
            (Ideal.Quotient.mk J_T r) • (Ideal.Quotient.mk J_M m)
          rfl }
    exact (Module.Flat.equiv_iff e).mpr hflatN
  let : Module.Flat (T ⧸ J_T) (M ⧸ (J_T • (⊤ : Submodule T M))) := hflatQuot
  let : Module.Flat R M := hflatRM
  have hflatTM : Module.Flat T M :=
    (Module.flat_and_flat_localization_of_flat_quotient_of_isNilpotent.{u, u, u, u}
      (R := R) (S := T) (M := M) I hI).1
  exact (RingHom.flat_algebraMap_iff).mpr hflatTM


/-- Flatness of a morphism lifts from its reduction over a finite-order
thickening when its source is flat over the thickened base. -/
@[stacks 06AF "flatness of the upper morphism"]
public theorem flat_of_flat_reduction
    (hiX : IsThickening iX)
    (hiY : IsThickening iY)
    (hiS : IsFiniteOrderThickening iS)
    (hX : IsPullback iX pX pX' iS)
    (hY : IsPullback iY pY pY' iS)
    (hf : iX ≫ f' = f ≫ iY)
    (hfbase : f ≫ pY = pX)
    (hf'base : f' ≫ pY' = pX')
    (hflatX' : Flat pX') (hflatf : Flat f) : Flat f' :=
  Flat.of_stalkMap f' fun x' =>
    flat_stalk_map_of_flat_reduction hiX hiY hiS hX hY hf hfbase hf'base hflatX' hflatf x'

/-- The thickened target is flat over the thickened base at every point in
the image of the upper morphism. -/
@[stacks 06AF "flatness of the upper target along the image"]
public theorem flatAt_target_of_flat_reduction
    (hiX : IsThickening iX)
    (hiY : IsThickening iY)
    (hiS : IsFiniteOrderThickening iS)
    (hX : IsPullback iX pX pX' iS)
    (hY : IsPullback iY pY pY' iS)
    (hf : iX ≫ f' = f ≫ iY)
    (hfbase : f ≫ pY = pX)
    (hf'base : f' ≫ pY' = pX')
    (hflatX' : Flat pX') (hflatf : Flat f)
    (x' : X') : IsFlatAt pY'.toLRSHom.toShHom (f' x') := by
  have : Flat f' := flat_of_flat_reduction hiX hiY hiS hX hY hf hfbase hf'base
    hflatX' hflatf
  let R := S'.presheaf.stalk (pY' (f' x'))
  let T := Y'.presheaf.stalk (f' x')
  let M := X'.presheaf.stalk x'
  let h : R →+* T := (pY'.stalkMap (f' x')).hom
  let g : T →+* M := (f'.stalkMap x').hom
  have hR : pY' (f' x') = pX' x' := congrArg (fun k : X' ⟶ S' => k.base x') hf'base
  let : Algebra R T := h.toAlgebra
  let : Algebra T M := g.toAlgebra
  let : Algebra R M :=
    ((eqToHom (congrArg S'.presheaf.stalk hR) ≫ pX'.stalkMap x').hom).toAlgebra
  have hcomp := stalkMap_comp_eq_eqToHom_comp f' pY' hf'base x' hR
  let : IsScalarTower R T M := IsScalarTower.of_algebraMap_eq' (by
    ext r
    change (((eqToHom (congrArg S'.presheaf.stalk hR) ≫ pX'.stalkMap x').hom) r) =
      (g (h r))
    exact (DFunLike.congr_fun
      (congrArg (fun q : CommRingCat.Hom _ _ => q.hom) hcomp).symm r))
  have hflatM : Module.Flat R M :=
    RingHom.flat_algebraMap_iff.mp (flat_eqToHom_stalkMap pX' hflatX' x' hR)
  let : Module.FaithfullyFlat T M :=
    Flat.faithfullyFlat_stalkMap f' x'
  have hflatT : Module.Flat R T :=
    Stacks.Flatness.NilpotentFibreCriterion.flat_of_flat_of_faithfullyFlat M
  change h.Flat
  exact RingHom.flat_algebraMap_iff.mpr hflatT

end AlgebraicGeometry
