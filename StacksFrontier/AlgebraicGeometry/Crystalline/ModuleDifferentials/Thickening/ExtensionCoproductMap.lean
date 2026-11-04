module

public import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.Thickening.DiagonalKernel

/-!
# The diagonal of a coproduct of crystalline thickenings: kernel coordinates

Compatibility of the diagonal with the two coprojections, the divided power derivation
`b ↦ [s₁ b - s₀ b]` into the diagonal conormal module, and, for a divided power derivation `d` of
`X` into a module `M`, the map from the coproduct to the first-order thickening of `X` by `M` and
the resulting coordinate map on the diagonal kernel, which kills the diagonal relations.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open DividedPowerRing

universe u v w

namespace Crystalline

open DividedPowerThickening

variable {S : AffineCrystallineSituation.{u, v}}
variable {X Y : CrystallineThickening.{u, v, w} S}
variable {s₀ s₁ : X ⟶ Y}

theorem diagonalMap_s₀
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : CrystallineThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁)) (x : X.1.ring) :
    (diagonalMap h).hom.hom.toRingHom (s₀.hom.hom.toRingHom x) = x := by
  have hc : s₀ ≫ diagonalMap h = 𝟙 X :=
    BinaryCofan.IsColimit.inl_desc h (𝟙 X) (𝟙 X)
  exact congrArg (fun f : X ⟶ X => f.hom.hom.toRingHom x) hc

theorem diagonalMap_s₁
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : CrystallineThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁)) (x : X.1.ring) :
    (diagonalMap h).hom.hom.toRingHom (s₁.hom.hom.toRingHom x) = x := by
  have hc : s₁ ≫ diagonalMap h = 𝟙 X :=
    BinaryCofan.IsColimit.inr_desc h (𝟙 X) (𝟙 X)
  exact congrArg (fun f : X ⟶ X => f.hom.hom.toRingHom x) hc

theorem diagonalClass_s₀
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : CrystallineThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁)) (x : X.1.ring) :
    diagonalClass h (s₀.hom.hom.toRingHom x) = 0 := by
  have hk : diagonalClassRep h (s₀.hom.hom.toRingHom x) = 0 := by
    apply Subtype.ext
    change s₀.hom.hom.toRingHom x -
      s₀.hom.hom.toRingHom ((diagonalMap h).hom.hom.toRingHom
        (s₀.hom.hom.toRingHom x)) = 0
    rw [diagonalMap_s₀ h, sub_self]
  change Submodule.Quotient.mk (diagonalClassRep h (s₀.hom.hom.toRingHom x)) = 0
  rw [hk]
  simp

theorem diagonalClass_s₁
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : CrystallineThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁)) (x : X.1.ring) :
    diagonalClass h (s₁.hom.hom.toRingHom x) = diagonalDifference h x := by
  change Submodule.Quotient.mk
      (diagonalClassRep h (s₁.hom.hom.toRingHom x)) = _
  unfold diagonalDifference
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  change s₁.hom.hom.toRingHom x -
      s₀.hom.hom.toRingHom ((diagonalMap h).hom.hom.toRingHom
        (s₁.hom.hom.toRingHom x)) =
    s₁.hom.hom.toRingHom x - s₀.hom.hom.toRingHom x
  rw [diagonalMap_s₁ h]

noncomputable def diagonalDifferenceDerivation
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : CrystallineThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁)) :
    letI : Algebra S.A X.1.ring := X.1.fromBase.toRingHom.toAlgebra
    DividedPowerDerivation S.A X.1.ring X.1.fromBase.toRingHom
      (diagonalConormal h) := by
  letI : Algebra S.A X.1.ring := X.1.fromBase.toRingHom.toAlgebra
  let dAdd : X.1.ring →+ diagonalConormal h := {
    toFun := diagonalDifference h
    map_zero' := by
      unfold diagonalDifference
      apply congrArg Submodule.Quotient.mk
      apply Subtype.ext
      change s₁.hom.hom.toRingHom 0 - s₀.hom.hom.toRingHom 0 = 0
      rw [map_zero s₁.hom.hom.toRingHom, map_zero s₀.hom.hom.toRingHom, sub_self]
    map_add' := by
      intro x y
      rw [← diagonalClass_s₁ h (x + y), map_add s₁.hom.hom.toRingHom,
        diagonalClass_add, diagonalClass_s₁, diagonalClass_s₁]
  }
  let dLin : X.1.ring →ₗ[ℤ] diagonalConormal h := dAdd.toIntLinearMap
  let d : Derivation ℤ X.1.ring (diagonalConormal h) := Derivation.mk' dLin (by
    intro x y
    change diagonalDifference h (x * y) =
      x • diagonalDifference h y + y • diagonalDifference h x
    rw [← diagonalClass_s₁ h (x * y), map_mul s₁.hom.hom.toRingHom,
      diagonalClass_mul, diagonalClass_s₁, diagonalClass_s₁]
    change (diagonalMap h).hom.hom.toRingHom
          (s₁.hom.hom.toRingHom x) • diagonalDifference h y +
        (diagonalMap h).hom.hom.toRingHom
          (s₁.hom.hom.toRingHom y) • diagonalDifference h x = _
    rw [diagonalMap_s₁ h x, diagonalMap_s₁ h y])
  refine ⟨d, ?_, ?_⟩
  · intro a
    change diagonalDifference h (X.1.fromBase.toRingHom a) = 0
    have hb₀ : s₀.hom.hom.toRingHom (X.1.fromBase.toRingHom a) =
        Y.1.fromBase.toRingHom a :=
      congrArg (fun f : DividedPowers.DPMorphism
        S.A.dividedPowers Y.1.ring.dividedPowers => f.toRingHom a) s₀.hom.fromBase_comp
    have hb₁ : s₁.hom.hom.toRingHom (X.1.fromBase.toRingHom a) =
        Y.1.fromBase.toRingHom a :=
      congrArg (fun f : DividedPowers.DPMorphism
        S.A.dividedPowers Y.1.ring.dividedPowers => f.toRingHom a) s₁.hom.fromBase_comp
    have heq : s₁.hom.hom.toRingHom (X.1.fromBase.toRingHom a) =
        s₀.hom.hom.toRingHom (X.1.fromBase.toRingHom a) := hb₁.trans hb₀.symm
    rw [← diagonalClass_s₁ h (X.1.fromBase.toRingHom a), heq,
      diagonalClass_s₀ h]
  · intro n hn x hx
    by_cases hn1 : n = 1
    · subst n
      rw [X.1.ring.dividedPowers.dpow_one hx,
        X.1.ring.dividedPowers.dpow_zero hx, one_smul]
    · have hn2 : 2 ≤ n := by omega
      have hy : s₁.hom.hom.toRingHom x ∈ Y.1.ring.ideal :=
        (Ideal.map_le_iff_le_comap.mp s₁.hom.hom.ideal_comp) hx
      change diagonalDifference h (X.1.ring.dividedPowers.dpow n x) =
        X.1.ring.dividedPowers.dpow (n - 1) x • diagonalDifference h x
      rw [← diagonalClass_s₁ h (X.1.ring.dividedPowers.dpow n x),
        ← s₁.hom.hom.isDPMorphism.dpow_comp x hx,
        diagonalClass_dpow h n (s₁.hom.hom.toRingHom x) hn2 hy]
      change X.1.ring.dividedPowers.dpow (n - 1)
          ((diagonalMap h).hom.hom.toRingHom
            (s₁.hom.hom.toRingHom x)) • diagonalClass h (s₁.hom.hom.toRingHom x) = _
      rw [diagonalMap_s₁ h x, diagonalClass_s₁ h x]

noncomputable def firstOrderExtensionFstDPMorphism
    (D : DividedPowerRing.{u}) (M : Type v) [AddCommGroup M] [Module D M]
    [Module Dᵐᵒᵖ M] [IsCentralScalar D M] :
    DividedPowers.DPMorphism (Classical.choose (firstOrderExtension_dividedPowers D M))
      D.dividedPowers := by
  classical
  let δ := Classical.choose (firstOrderExtension_dividedPowers D M)
  let J := firstOrderExtensionIdeal D M
  let f := (TrivSqZeroExt.fstHom D D M).toRingHom
  have hcoords := (Classical.choose_spec (firstOrderExtension_dividedPowers D M)).1
  refine DividedPowers.DPMorphism.mk' (f := f) ?_
  refine ⟨?_, ?_⟩
  · rw [Ideal.map_le_iff_le_comap]
    intro z hz
    change z.1 ∈ D.ideal
    exact hz
  · intro n z hz
    have hzD : z.1 ∈ D.ideal := hz
    change D.dividedPowers.dpow n z.1 = TrivSqZeroExt.fst (δ.dpow n z)
    by_cases hn0 : n = 0
    · subst n
      rw [D.dividedPowers.dpow_zero hzD, δ.dpow_zero hz]
      rfl
    · by_cases hn1 : n = 1
      · subst n
        rw [D.dividedPowers.dpow_one hzD, δ.dpow_one hz]
        rfl
      · exact (hcoords n z (by omega) hz).1.symm

-- Quotient extensionality unfolds several nested quotient maps and needs unrestricted reduction.
theorem firstOrderExtensionFst_quotientComp
    (D : DividedPowerRing.{u}) (M : Type v) [AddCommGroup M] [Module D M]
    [Module Dᵐᵒᵖ M] [IsCentralScalar D M] :
    (Ideal.quotientMap D.ideal
      (firstOrderExtensionFstDPMorphism D M).toRingHom
      (Ideal.map_le_iff_le_comap.mp
        (firstOrderExtensionFstDPMorphism D M).ideal_comp)).comp
      (firstOrderExtensionQuotientMap D M) = RingHom.id (D ⧸ D.ideal) := by
  classical
  ext x
  change Ideal.Quotient.mk D.ideal
      ((TrivSqZeroExt.fstHom D D M).toRingHom
        (TrivSqZeroExt.inlHom D M x)) = Ideal.Quotient.mk D.ideal x
  rfl

noncomputable def firstOrderExtensionFstMap
    {S : AffineCrystallineSituation.{u, v}}
    (X : CrystallineThickening.{u, v, w} S) (M : Type w)
    [AddCommGroup M] [Module X.1.ring M] [Module X.1.ringᵐᵒᵖ M]
    [IsCentralScalar X.1.ring M] :
    firstOrderExtensionThickening X M ⟶ X.1 := by
  classical
  let f := firstOrderExtensionFstDPMorphism X.1.ring M
  let E := firstOrderExtensionThickening X M
  refine { hom := f, fromBase_comp := ?_, toQuotient_comp := ?_ }
  · apply DividedPowers.DPMorphism.ext
    funext a
    change (TrivSqZeroExt.fstHom X.1.ring X.1.ring M).toRingHom
      ((algebraMap X.1.ring (TrivSqZeroExt X.1.ring M))
        (X.1.fromBase.toRingHom a)) = X.1.fromBase.toRingHom a
    rw [TrivSqZeroExt.algebraMap_eq_inl]
    rfl
  · change (Ideal.quotientMap X.1.ring.ideal f.toRingHom
        (Ideal.map_le_iff_le_comap.mp f.ideal_comp)).comp E.toQuotient = X.1.toQuotient
    dsimp [E, firstOrderExtensionThickening]
    change ((Ideal.quotientMap X.1.ring.ideal
        (firstOrderExtensionFstDPMorphism X.1.ring M).toRingHom
        (Ideal.map_le_iff_le_comap.mp
          (firstOrderExtensionFstDPMorphism X.1.ring M).ideal_comp)).comp
        (firstOrderExtensionQuotientMap X.1.ring M)).comp X.1.toQuotient =
      X.1.toQuotient
    rw [firstOrderExtensionFst_quotientComp]
    rfl

noncomputable def firstOrderExtensionLinearMap
    {S : AffineCrystallineSituation.{u, v}}
    (X : CrystallineThickening.{u, v, w} S)
    (M N : Type w) [AddCommGroup M] [Module X.1.ring M]
    [Module X.1.ringᵐᵒᵖ M] [IsCentralScalar X.1.ring M]
    [AddCommGroup N] [Module X.1.ring N] [Module X.1.ringᵐᵒᵖ N]
    [IsCentralScalar X.1.ring N]
    (F : M →ₗ[X.1.ring] N) :
    firstOrderExtensionThickening X M ⟶ firstOrderExtensionThickening X N := by
  classical
  let δM := Classical.choose (firstOrderExtension_dividedPowers X.1.ring M)
  let δN := Classical.choose (firstOrderExtension_dividedPowers X.1.ring N)
  let f := (TrivSqZeroExt.map F).toRingHom
  let JM := firstOrderExtensionIdeal X.1.ring M
  let JN := firstOrderExtensionIdeal X.1.ring N
  have hcoordsM := (Classical.choose_spec
    (firstOrderExtension_dividedPowers X.1.ring M)).1
  have hcoordsN := (Classical.choose_spec
    (firstOrderExtension_dividedPowers X.1.ring N)).1
  have hfst (z : TrivSqZeroExt X.1.ring M) :
      (TrivSqZeroExt.map F z).fst = z.fst :=
    TrivSqZeroExt.fst_map F z
  have hsnd (z : TrivSqZeroExt X.1.ring M) :
      (TrivSqZeroExt.map F z).snd = F z.snd :=
    TrivSqZeroExt.snd_map F z
  have hfst' (z : TrivSqZeroExt X.1.ring M) : (f z).fst = z.fst := hfst z
  have hsnd' (z : TrivSqZeroExt X.1.ring M) : (f z).snd = F z.snd := hsnd z
  have hmem : ∀ z ∈ JM, f z ∈ JN := fun z hz => by
    change (TrivSqZeroExt.map F z).fst ∈ X.1.ring.ideal
    rw [hfst]
    exact hz
  have hdp : DividedPowers.IsDPMorphism δM δN f := by
    refine ⟨Ideal.map_le_iff_le_comap.mpr hmem, fun {n} z hz => ?_⟩
    have hzN : f z ∈ JN := hmem z hz
    by_cases hn0 : n = 0
    · subst n
      rw [δN.dpow_zero hzN, δM.dpow_zero hz]
      exact (map_one f).symm
    · by_cases hn1 : n = 1
      · subst n
        rw [δN.dpow_one hzN, δM.dpow_one hz]
      · have hn2 : 2 ≤ n := by omega
        have hm := hcoordsM n z hn2 hz
        have hn := hcoordsN n (f z) hn2 hzN
        apply TrivSqZeroExt.ext
        · rw [hn.1]
          change X.1.ring.dividedPowers.dpow n
              (TrivSqZeroExt.fst (TrivSqZeroExt.map F z)) =
            TrivSqZeroExt.fst (TrivSqZeroExt.map F (δM.dpow n z))
          rw [hfst z, hfst, hm.1]
        · rw [hn.2, hfst' z, hsnd' z, hsnd' (δM.dpow n z), hm.2, F.map_smul]
  let φ : DividedPowers.DPMorphism δM δN := DividedPowers.DPMorphism.mk' hdp
  let Eₘ := firstOrderExtensionThickening X M
  let Eₙ := firstOrderExtensionThickening X N
  refine { hom := φ, fromBase_comp := ?_, toQuotient_comp := ?_ }
  · apply DividedPowers.DPMorphism.ext
    funext a
    change (TrivSqZeroExt.map F).toRingHom
      ((algebraMap X.1.ring (TrivSqZeroExt X.1.ring M))
        (X.1.fromBase.toRingHom a)) =
      (algebraMap X.1.ring (TrivSqZeroExt X.1.ring N))
        (X.1.fromBase.toRingHom a)
    simp [TrivSqZeroExt.algebraMap_eq_inl]
  · dsimp only [Eₘ, Eₙ, firstOrderExtensionThickening]
    change (Ideal.quotientMap (firstOrderExtensionIdeal X.1.ring N) φ.toRingHom
      (Ideal.map_le_iff_le_comap.mp φ.ideal_comp)).comp
        ((firstOrderExtensionQuotientMap X.1.ring M).comp X.1.toQuotient) =
      (firstOrderExtensionQuotientMap X.1.ring N).comp X.1.toQuotient
    ext c
    obtain ⟨d, hd⟩ := Ideal.Quotient.mk_surjective (X.1.toQuotient c)
    change (Ideal.quotientMap (firstOrderExtensionIdeal X.1.ring N) φ.toRingHom
      (Ideal.map_le_iff_le_comap.mp φ.ideal_comp))
        (firstOrderExtensionQuotientMap X.1.ring M (X.1.toQuotient c)) =
      firstOrderExtensionQuotientMap X.1.ring N (X.1.toQuotient c)
    rw [← hd]
    simp only [firstOrderExtensionQuotientMap, Ideal.quotientMap_mk, φ]
    change Ideal.Quotient.mk (firstOrderExtensionIdeal X.1.ring N)
        (TrivSqZeroExt.map F (TrivSqZeroExt.inl d)) =
      Ideal.Quotient.mk (firstOrderExtensionIdeal X.1.ring N)
        (TrivSqZeroExt.inl d)
    rw [TrivSqZeroExt.map_inl]

noncomputable def firstOrderExtensionMapZeroCrystalline
    {S : AffineCrystallineSituation.{u, v}}
    (X : CrystallineThickening.{u, v, w} S) (M : Type w)
    [AddCommGroup M] [Module X.1.ring M] [Module X.1.ringᵐᵒᵖ M]
    [IsCentralScalar X.1.ring M] :
    X ⟶ firstOrderExtensionCrystalline X M :=
  ObjectProperty.homMk (by
    dsimp [firstOrderExtensionCrystalline]
    exact firstOrderExtensionMapZero X M)

noncomputable def firstOrderExtensionMapGraphCrystalline
    {S : AffineCrystallineSituation.{u, v}}
    (X : CrystallineThickening.{u, v, w} S) (M : Type w)
    [AddCommGroup M] [Module X.1.ring M] [Module X.1.ringᵐᵒᵖ M]
    [IsCentralScalar X.1.ring M]
    (d : DividedPowerDerivation S.A X.1.ring X.1.fromBase.toRingHom M) :
    X ⟶ firstOrderExtensionCrystalline X M :=
  ObjectProperty.homMk (by
    dsimp [firstOrderExtensionCrystalline]
    exact firstOrderExtensionMapGraph X M d)

noncomputable def diagonalExtensionCoproductMap
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : CrystallineThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁))
    (M : Type w) [AddCommGroup M] [Module X.1.ring M]
    [Module X.1.ringᵐᵒᵖ M] [IsCentralScalar X.1.ring M]
    (d : DividedPowerDerivation S.A X.1.ring
      X.1.fromBase.toRingHom M) :
    Y ⟶ firstOrderExtensionCrystalline X M :=
  BinaryCofan.IsColimit.desc h
    (firstOrderExtensionMapZeroCrystalline X M)
    (firstOrderExtensionMapGraphCrystalline X M d)

noncomputable def firstOrderExtensionFstCrystallineMap
    {S : AffineCrystallineSituation.{u, v}}
    (X : CrystallineThickening.{u, v, w} S) (M : Type w)
    [AddCommGroup M] [Module X.1.ring M] [Module X.1.ringᵐᵒᵖ M]
    [IsCentralScalar X.1.ring M] :
    firstOrderExtensionCrystalline X M ⟶ X :=
  ObjectProperty.homMk (by
    dsimp [firstOrderExtensionCrystalline]
    exact firstOrderExtensionFstMap X M)

private theorem diagonalExtensionCoproductMap_inl_comp
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : CrystallineThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁))
    (M : Type w) [AddCommGroup M] [Module X.1.ring M]
    [Module X.1.ringᵐᵒᵖ M] [IsCentralScalar X.1.ring M]
    (d : DividedPowerDerivation S.A X.1.ring
      X.1.fromBase.toRingHom M) :
    s₀ ≫ diagonalExtensionCoproductMap h M d = firstOrderExtensionMapZeroCrystalline X M :=
  BinaryCofan.IsColimit.inl_desc h _ _

private theorem diagonalExtensionCoproductMap_inr_comp
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : CrystallineThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁))
    (M : Type w) [AddCommGroup M] [Module X.1.ring M]
    [Module X.1.ringᵐᵒᵖ M] [IsCentralScalar X.1.ring M]
    (d : DividedPowerDerivation S.A X.1.ring
      X.1.fromBase.toRingHom M) :
    s₁ ≫ diagonalExtensionCoproductMap h M d = firstOrderExtensionMapGraphCrystalline X M d :=
  BinaryCofan.IsColimit.inr_desc h _ _

theorem diagonalExtensionCoproductMap_fst
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : CrystallineThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁))
    (M : Type w) [AddCommGroup M] [Module X.1.ring M]
    [Module X.1.ringᵐᵒᵖ M] [IsCentralScalar X.1.ring M]
    (d : DividedPowerDerivation S.A X.1.ring
      X.1.fromBase.toRingHom M) :
    (diagonalExtensionCoproductMap h M d ≫
      firstOrderExtensionFstCrystallineMap X M) =
      diagonalMap h := by
  have hf₀ : firstOrderExtensionMapZeroCrystalline X M ≫
      firstOrderExtensionFstCrystallineMap X M = 𝟙 X := by
    apply ObjectProperty.hom_ext
    apply DividedPowerThickening.Hom.ext
    apply DividedPowers.DPMorphism.ext
    funext x
    rfl
  have hf₁ : firstOrderExtensionMapGraphCrystalline X M d ≫
      firstOrderExtensionFstCrystallineMap X M = 𝟙 X := by
    apply ObjectProperty.hom_ext
    apply DividedPowerThickening.Hom.ext
    apply DividedPowers.DPMorphism.ext
    funext x
    rfl
  apply BinaryCofan.IsColimit.hom_ext h
  · change s₀ ≫ _ ≫ _ = s₀ ≫ diagonalMap h
    rw [← Category.assoc, diagonalExtensionCoproductMap_inl_comp, hf₀]
    exact (BinaryCofan.IsColimit.inl_desc h (𝟙 X) (𝟙 X)).symm
  · change s₁ ≫ _ ≫ _ = s₁ ≫ diagonalMap h
    rw [← Category.assoc, diagonalExtensionCoproductMap_inr_comp, hf₁]
    exact (BinaryCofan.IsColimit.inr_desc h (𝟙 X) (𝟙 X)).symm

theorem diagonalExtensionCoproductMap_inl
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : CrystallineThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁))
    (M : Type w) [AddCommGroup M] [Module X.1.ring M]
    [Module X.1.ringᵐᵒᵖ M] [IsCentralScalar X.1.ring M]
    (d : DividedPowerDerivation S.A X.1.ring
      X.1.fromBase.toRingHom M) (x : X.1.ring) :
    (diagonalExtensionCoproductMap h M d).hom.hom.toRingHom
      (s₀.hom.hom.toRingHom x) = TrivSqZeroExt.inl x :=
  congrArg (fun f : X ⟶ firstOrderExtensionCrystalline X M => f.hom.hom.toRingHom x)
    (diagonalExtensionCoproductMap_inl_comp h M d)

theorem diagonalExtensionCoproductMap_inr
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : CrystallineThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁))
    (M : Type w) [AddCommGroup M] [Module X.1.ring M]
    [Module X.1.ringᵐᵒᵖ M] [IsCentralScalar X.1.ring M]
    (d : DividedPowerDerivation S.A X.1.ring
      X.1.fromBase.toRingHom M) (x : X.1.ring) :
    (diagonalExtensionCoproductMap h M d).hom.hom.toRingHom
      (s₁.hom.hom.toRingHom x) = graphRingHom d x :=
  congrArg (fun f : X ⟶ firstOrderExtensionCrystalline X M => f.hom.hom.toRingHom x)
    (diagonalExtensionCoproductMap_inr_comp h M d)

noncomputable def diagonalKernelCoordinateMap
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : CrystallineThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁))
    (M : Type w) [AddCommGroup M] [Module X.1.ring M]
    [Module X.1.ringᵐᵒᵖ M] [IsCentralScalar X.1.ring M]
    (d : DividedPowerDerivation S.A X.1.ring
      X.1.fromBase.toRingHom M) :
    let q : Y.1.ring →+* X.1.ring := (diagonalMap h).hom.hom.toRingHom
    letI : Algebra Y.1.ring X.1.ring := q.toAlgebra
    letI : Module Y.1.ring M := Module.compHom M q
    diagonalKernel h →ₗ[Y.1.ring] M := by
  let q : Y.1.ring →+* X.1.ring := (diagonalMap h).hom.hom.toRingHom
  letI : Algebra Y.1.ring X.1.ring := q.toAlgebra
  letI : Module Y.1.ring M := Module.compHom M q
  let ψ := diagonalExtensionCoproductMap h M d
  let φ : Y.1.ring →+* TrivSqZeroExt X.1.ring M := ψ.hom.hom.toRingHom
  have hfst (y : Y.1.ring) : (φ y).fst = q y := by
    have hc := diagonalExtensionCoproductMap_fst h M d
    have he := congrArg (fun g : Y ⟶ X => g.hom.hom.toRingHom y) hc
    have hfstMap : (firstOrderExtensionFstMap X M).hom.toRingHom =
        (TrivSqZeroExt.fstHom X.1.ring X.1.ring M).toRingHom := by
      ext z
      rfl
    change (firstOrderExtensionFstMap X M).hom.toRingHom
        (ψ.hom.hom.toRingHom y) = q y at he
    rw [hfstMap] at he
    exact he
  refine {
    toFun := fun k => (φ k.1).snd
    map_add' := ?_
    map_smul' := ?_ }
  · intro k l
    change (φ (k.1 + l.1)).snd = (φ k.1).snd + (φ l.1).snd
    rw [map_add, TrivSqZeroExt.snd_add]
  · intro a k
    change (φ (a * k.1)).snd = q a • (φ k.1).snd
    rw [map_mul]
    have hkfst : (φ k.1).fst = 0 := by
      rw [hfst, RingHom.mem_ker.mp k.2]
    rw [TrivSqZeroExt.snd_mul, hkfst]
    rw [hfst]
    simp

theorem diagonalKernelCoordinateMap_killsRelations
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : CrystallineThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁))
    (M : Type w) [AddCommGroup M] [Module X.1.ring M]
    [Module X.1.ringᵐᵒᵖ M] [IsCentralScalar X.1.ring M]
    (d : DividedPowerDerivation S.A X.1.ring
      X.1.fromBase.toRingHom M) :
    let q : Y.1.ring →+* X.1.ring := (diagonalMap h).hom.hom.toRingHom
    letI : Algebra Y.1.ring X.1.ring := q.toAlgebra
    letI : Module Y.1.ring M := Module.compHom M q
    diagonalRelations h ≤ LinearMap.ker (diagonalKernelCoordinateMap h M d) := by
  classical
  let q : Y.1.ring →+* X.1.ring := (diagonalMap h).hom.hom.toRingHom
  let : Algebra Y.1.ring X.1.ring := q.toAlgebra
  let : Module Y.1.ring M := Module.compHom M q
  let ψ := diagonalExtensionCoproductMap h M d
  let φ : Y.1.ring →+* TrivSqZeroExt X.1.ring M := ψ.hom.hom.toRingHom
  let K := diagonalKernel h
  have hfst (y : Y.1.ring) : (φ y).fst = q y := by
    have hc := diagonalExtensionCoproductMap_fst h M d
    have he := congrArg (fun g : Y ⟶ X => g.hom.hom.toRingHom y) hc
    have hfstMap : (firstOrderExtensionFstMap X M).hom.toRingHom =
        (TrivSqZeroExt.fstHom X.1.ring X.1.ring M).toRingHom := by
      ext z
      rfl
    change (firstOrderExtensionFstMap X M).hom.toRingHom
        (ψ.hom.hom.toRingHom y) = q y at he
    rw [hfstMap] at he
    exact he
  let Z : Ideal Y.1.ring := {
    carrier := {y | y ∈ K ∧ (φ y).snd = 0}
    zero_mem' := by simp
    add_mem' := by
      intro a b ha hb
      refine ⟨add_mem ha.1 hb.1, ?_⟩
      change (φ (a + b)).snd = 0
      rw [map_add, TrivSqZeroExt.snd_add, ha.2, hb.2]
      simp
    smul_mem' := by
      intro a b hb
      refine ⟨K.mul_mem_left a hb.1, ?_⟩
      have hfstb : (φ b).fst = 0 := by
        rw [hfst, RingHom.mem_ker.mp hb.1]
      change (φ (a * b)).snd = 0
      rw [map_mul, TrivSqZeroExt.snd_mul, hfstb, hb.2]
      simp
  }
  have hKsq : K ^ (2 : ℕ) ≤ Z := by
    rw [pow_two, Ideal.mul_le]
    intro a ha b hb
    refine ⟨mul_mem ha hb, ?_⟩
    have hfa : (φ a).fst = 0 := by rw [hfst, RingHom.mem_ker.mp ha]
    have hfb : (φ b).fst = 0 := by rw [hfst, RingHom.mem_ker.mp hb]
    change (φ (a * b)).snd = 0
    rw [map_mul, TrivSqZeroExt.snd_mul, hfa, hfb]
    simp
  have hdpIdeal :
      secondDividedPowerIdeal Y.1.ring.dividedPowers
        (K ⊓ Y.1.ring.ideal) ≤ Z := by
    unfold secondDividedPowerIdeal
    apply Ideal.span_le.mpr
    rintro z ⟨n, hn, x, hx, rfl⟩
    rcases hx with ⟨hxK, hxJ⟩
    have hfx : (φ x).fst = 0 := by rw [hfst, RingHom.mem_ker.mp hxK]
    have hφx : φ x ∈ firstOrderExtensionIdeal X.1.ring M := by
      change (φ x).fst ∈ X.1.ring.ideal
      rw [hfx]
      exact X.1.ring.ideal.zero_mem
    have hdpmap := ψ.hom.hom.isDPMorphism.dpow_comp (n := n) x hxJ
    have hcoords := (Classical.choose_spec
      (firstOrderExtension_dividedPowers X.1.ring M)).1 n (φ x) hn hφx
    have hzero :
        (Classical.choose (firstOrderExtension_dividedPowers X.1.ring M)).dpow n
          (φ x) = 0 := by
      apply TrivSqZeroExt.ext
      · rw [hcoords.1, hfx,
          X.1.ring.dividedPowers.dpow_eval_zero (by omega : n ≠ 0)]
        simp
      · rw [hcoords.2, hfx,
          X.1.ring.dividedPowers.dpow_eval_zero (by omega : n - 1 ≠ 0)]
        simp
    have hmapzero : φ (Y.1.ring.dividedPowers.dpow n x) = 0 := by
      change ψ.hom.hom.toRingHom (Y.1.ring.dividedPowers.dpow n x) = 0
      rw [← hdpmap]
      exact hzero
    refine ⟨?_, ?_⟩
    · rw [RingHom.mem_ker]
      rw [← (diagonalMap h).hom.hom.isDPMorphism.dpow_comp (n := n) x hxJ]
      rw [RingHom.mem_ker.mp hxK,
        X.1.ring.dividedPowers.dpow_eval_zero (by omega : n ≠ 0)]
    · rw [hmapzero]
      rfl
  have hsum : K ^ (2 : ℕ) +
      secondDividedPowerIdeal Y.1.ring.dividedPowers
        (K ⊓ Y.1.ring.ideal) ≤ Z := sup_le hKsq hdpIdeal
  intro q' k hk
  change ((Submodule.subtype (K : Submodule Y.1.ring Y.1.ring)) k) ∈
    K ^ (2 : ℕ) + secondDividedPowerIdeal Y.1.ring.dividedPowers
      (K ⊓ Y.1.ring.ideal) at hk
  exact (hsum hk).2

end Crystalline

end
