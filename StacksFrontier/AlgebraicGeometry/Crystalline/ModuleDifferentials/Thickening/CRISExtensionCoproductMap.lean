module

public import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.Thickening.CRISDiagonalKernel
public import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.Thickening.ExtensionCoproductMap

/-!
# The diagonal of a coproduct in `CRIS(C/A)`: kernel coordinates

For an object `X` of the big crystalline category `CRIS(C/A)` and a coproduct `Y` of `X` with
itself in `CRIS(C/A)`: compatibility of the codiagonal with the two coprojections, the divided
power derivation `b ↦ [s₁ b - s₀ b]` into the diagonal conormal module, and, for a divided power
derivation `θ` of `X` into a module `M`, the map from the coproduct to the first-order thickening
`B ⊕ M` (an object of `CRIS(C/A)`) and the resulting coordinate map on the diagonal kernel, which
kills the diagonal relations.

These generalize the declarations of the same names in the namespace `Crystalline`, stated for
the full subcategory `Cris(C/A)`.

## References

* [Stacks Project, Tag 07HV](https://stacks.math.columbia.edu/tag/07HV)
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open DividedPowerRing

universe u v w

namespace Crystalline

namespace DividedPowerThickening

variable {S : AffineCrystallineSituation.{u, v}}
variable {X Y : DividedPowerThickening.{u, v, w} S}
variable {s₀ s₁ : X ⟶ Y}

/-- The codiagonal is a retraction of the first coprojection. -/
theorem diagonalMap_s₀
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : DividedPowerThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁)) (x : X.ring) :
    (diagonalMap h).hom.toRingHom (s₀.hom.toRingHom x) = x := by
  have hc : s₀ ≫ diagonalMap h = 𝟙 X :=
    BinaryCofan.IsColimit.inl_desc h (𝟙 X) (𝟙 X)
  exact congrArg (fun f : X ⟶ X => f.hom.toRingHom x) hc

/-- The codiagonal is a retraction of the second coprojection. -/
theorem diagonalMap_s₁
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : DividedPowerThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁)) (x : X.ring) :
    (diagonalMap h).hom.toRingHom (s₁.hom.toRingHom x) = x := by
  have hc : s₁ ≫ diagonalMap h = 𝟙 X :=
    BinaryCofan.IsColimit.inr_desc h (𝟙 X) (𝟙 X)
  exact congrArg (fun f : X ⟶ X => f.hom.toRingHom x) hc

/-- The class of an element in the image of the first coprojection vanishes. -/
theorem diagonalClass_s₀
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : DividedPowerThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁)) (x : X.ring) :
    diagonalClass h (s₀.hom.toRingHom x) = 0 := by
  have hk : diagonalClassRep h (s₀.hom.toRingHom x) = 0 := by
    apply Subtype.ext
    change s₀.hom.toRingHom x -
      s₀.hom.toRingHom ((diagonalMap h).hom.toRingHom
        (s₀.hom.toRingHom x)) = 0
    rw [diagonalMap_s₀ h, sub_self]
  change Submodule.Quotient.mk (diagonalClassRep h (s₀.hom.toRingHom x)) = 0
  rw [hk]
  simp

/-- The class of `s₁ b` is the class of `s₁ b - s₀ b`. -/
theorem diagonalClass_s₁
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : DividedPowerThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁)) (x : X.ring) :
    diagonalClass h (s₁.hom.toRingHom x) = diagonalDifference h x := by
  change Submodule.Quotient.mk
      (diagonalClassRep h (s₁.hom.toRingHom x)) = _
  unfold diagonalDifference
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  change s₁.hom.toRingHom x -
      s₀.hom.toRingHom ((diagonalMap h).hom.toRingHom
        (s₁.hom.toRingHom x)) =
    s₁.hom.toRingHom x - s₀.hom.toRingHom x
  rw [diagonalMap_s₁ h]

/-- The divided power `A`-derivation `b ↦ [s₁ b - s₀ b]` into the diagonal conormal module. -/
noncomputable def diagonalDifferenceDerivation
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : DividedPowerThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁)) :
    letI : Algebra S.A X.ring := X.fromBase.toRingHom.toAlgebra
    DividedPowerDerivation S.A X.ring X.fromBase.toRingHom
      (diagonalConormal h) := by
  letI : Algebra S.A X.ring := X.fromBase.toRingHom.toAlgebra
  let dAdd : X.ring →+ diagonalConormal h := {
    toFun := diagonalDifference h
    map_zero' := by
      unfold diagonalDifference
      apply congrArg Submodule.Quotient.mk
      apply Subtype.ext
      change s₁.hom.toRingHom 0 - s₀.hom.toRingHom 0 = 0
      rw [map_zero s₁.hom.toRingHom, map_zero s₀.hom.toRingHom, sub_self]
    map_add' := by
      intro x y
      rw [← diagonalClass_s₁ h (x + y), map_add s₁.hom.toRingHom,
        diagonalClass_add, diagonalClass_s₁, diagonalClass_s₁]
  }
  let dLin : X.ring →ₗ[ℤ] diagonalConormal h := dAdd.toIntLinearMap
  let d : Derivation ℤ X.ring (diagonalConormal h) := Derivation.mk' dLin (by
    intro x y
    change diagonalDifference h (x * y) =
      x • diagonalDifference h y + y • diagonalDifference h x
    rw [← diagonalClass_s₁ h (x * y), map_mul s₁.hom.toRingHom,
      diagonalClass_mul, diagonalClass_s₁, diagonalClass_s₁]
    change (diagonalMap h).hom.toRingHom
          (s₁.hom.toRingHom x) • diagonalDifference h y +
        (diagonalMap h).hom.toRingHom
          (s₁.hom.toRingHom y) • diagonalDifference h x = _
    rw [diagonalMap_s₁ h x, diagonalMap_s₁ h y])
  refine ⟨d, ?_, ?_⟩
  · intro a
    change diagonalDifference h (X.fromBase.toRingHom a) = 0
    have hb₀ : s₀.hom.toRingHom (X.fromBase.toRingHom a) =
        Y.fromBase.toRingHom a :=
      congrArg (fun f : DividedPowers.DPMorphism
        S.A.dividedPowers Y.ring.dividedPowers => f.toRingHom a) s₀.fromBase_comp
    have hb₁ : s₁.hom.toRingHom (X.fromBase.toRingHom a) =
        Y.fromBase.toRingHom a :=
      congrArg (fun f : DividedPowers.DPMorphism
        S.A.dividedPowers Y.ring.dividedPowers => f.toRingHom a) s₁.fromBase_comp
    have heq : s₁.hom.toRingHom (X.fromBase.toRingHom a) =
        s₀.hom.toRingHom (X.fromBase.toRingHom a) := hb₁.trans hb₀.symm
    rw [← diagonalClass_s₁ h (X.fromBase.toRingHom a), heq,
      diagonalClass_s₀ h]
  · intro n hn x hx
    by_cases hn1 : n = 1
    · subst n
      rw [X.ring.dividedPowers.dpow_one hx,
        X.ring.dividedPowers.dpow_zero hx, one_smul]
    · have hn2 : 2 ≤ n := by omega
      have hy : s₁.hom.toRingHom x ∈ Y.ring.ideal :=
        (Ideal.map_le_iff_le_comap.mp s₁.hom.ideal_comp) hx
      change diagonalDifference h (X.ring.dividedPowers.dpow n x) =
        X.ring.dividedPowers.dpow (n - 1) x • diagonalDifference h x
      rw [← diagonalClass_s₁ h (X.ring.dividedPowers.dpow n x),
        ← s₁.hom.isDPMorphism.dpow_comp x hx,
        diagonalClass_dpow h n (s₁.hom.toRingHom x) hn2 hy]
      change X.ring.dividedPowers.dpow (n - 1)
          ((diagonalMap h).hom.toRingHom
            (s₁.hom.toRingHom x)) • diagonalClass h (s₁.hom.toRingHom x) = _
      rw [diagonalMap_s₁ h x, diagonalClass_s₁ h x]

/-- The projection `B ⊕ M → B` of the first-order thickening, a morphism of `CRIS(C/A)`. -/
noncomputable def firstOrderExtensionFstMap
    {S : AffineCrystallineSituation.{u, v}}
    (X : DividedPowerThickening.{u, v, w} S) (M : Type w)
    [AddCommGroup M] [Module X.ring M] [Module X.ringᵐᵒᵖ M]
    [IsCentralScalar X.ring M] :
    firstOrderExtensionThickening X M ⟶ X := by
  classical
  let f := firstOrderExtensionFstDPMorphism X.ring M
  let E := firstOrderExtensionThickening X M
  refine { hom := f, fromBase_comp := ?_, toQuotient_comp := ?_ }
  · apply DividedPowers.DPMorphism.ext
    funext a
    change (TrivSqZeroExt.fstHom X.ring X.ring M).toRingHom
      ((algebraMap X.ring (TrivSqZeroExt X.ring M))
        (X.fromBase.toRingHom a)) = X.fromBase.toRingHom a
    rw [TrivSqZeroExt.algebraMap_eq_inl]
    rfl
  · change (Ideal.quotientMap X.ring.ideal f.toRingHom
        (Ideal.map_le_iff_le_comap.mp f.ideal_comp)).comp E.toQuotient = X.toQuotient
    dsimp [E, firstOrderExtensionThickening]
    change ((Ideal.quotientMap X.ring.ideal
        (firstOrderExtensionFstDPMorphism X.ring M).toRingHom
        (Ideal.map_le_iff_le_comap.mp
          (firstOrderExtensionFstDPMorphism X.ring M).ideal_comp)).comp
        (firstOrderExtensionQuotientMap X.ring M)).comp X.toQuotient =
      X.toQuotient
    rw [firstOrderExtensionFst_quotientComp]
    rfl

/-- The morphism `B ⊕ M → B ⊕ N` of first-order thickenings induced by a linear map `M → N`. -/
noncomputable def firstOrderExtensionLinearMap
    {S : AffineCrystallineSituation.{u, v}}
    (X : DividedPowerThickening.{u, v, w} S)
    (M N : Type w) [AddCommGroup M] [Module X.ring M]
    [Module X.ringᵐᵒᵖ M] [IsCentralScalar X.ring M]
    [AddCommGroup N] [Module X.ring N] [Module X.ringᵐᵒᵖ N]
    [IsCentralScalar X.ring N]
    (F : M →ₗ[X.ring] N) :
    firstOrderExtensionThickening X M ⟶ firstOrderExtensionThickening X N := by
  classical
  let δM := Classical.choose (firstOrderExtension_dividedPowers X.ring M)
  let δN := Classical.choose (firstOrderExtension_dividedPowers X.ring N)
  let f := (TrivSqZeroExt.map F).toRingHom
  let JM := firstOrderExtensionIdeal X.ring M
  let JN := firstOrderExtensionIdeal X.ring N
  have hcoordsM := (Classical.choose_spec
    (firstOrderExtension_dividedPowers X.ring M)).1
  have hcoordsN := (Classical.choose_spec
    (firstOrderExtension_dividedPowers X.ring N)).1
  have hfst (z : TrivSqZeroExt X.ring M) :
      (TrivSqZeroExt.map F z).fst = z.fst :=
    TrivSqZeroExt.fst_map F z
  have hsnd (z : TrivSqZeroExt X.ring M) :
      (TrivSqZeroExt.map F z).snd = F z.snd :=
    TrivSqZeroExt.snd_map F z
  have hfst' (z : TrivSqZeroExt X.ring M) : (f z).fst = z.fst := hfst z
  have hsnd' (z : TrivSqZeroExt X.ring M) : (f z).snd = F z.snd := hsnd z
  have hmem : ∀ z ∈ JM, f z ∈ JN := fun z hz => by
    change (TrivSqZeroExt.map F z).fst ∈ X.ring.ideal
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
          change X.ring.dividedPowers.dpow n
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
      ((algebraMap X.ring (TrivSqZeroExt X.ring M))
        (X.fromBase.toRingHom a)) =
      (algebraMap X.ring (TrivSqZeroExt X.ring N))
        (X.fromBase.toRingHom a)
    simp [TrivSqZeroExt.algebraMap_eq_inl]
  · dsimp only [Eₘ, Eₙ, firstOrderExtensionThickening]
    change (Ideal.quotientMap (firstOrderExtensionIdeal X.ring N) φ.toRingHom
      (Ideal.map_le_iff_le_comap.mp φ.ideal_comp)).comp
        ((firstOrderExtensionQuotientMap X.ring M).comp X.toQuotient) =
      (firstOrderExtensionQuotientMap X.ring N).comp X.toQuotient
    ext c
    obtain ⟨d, hd⟩ := Ideal.Quotient.mk_surjective (X.toQuotient c)
    change (Ideal.quotientMap (firstOrderExtensionIdeal X.ring N) φ.toRingHom
      (Ideal.map_le_iff_le_comap.mp φ.ideal_comp))
        (firstOrderExtensionQuotientMap X.ring M (X.toQuotient c)) =
      firstOrderExtensionQuotientMap X.ring N (X.toQuotient c)
    rw [← hd]
    simp only [firstOrderExtensionQuotientMap, Ideal.quotientMap_mk, φ]
    change Ideal.Quotient.mk (firstOrderExtensionIdeal X.ring N)
        (TrivSqZeroExt.map F (TrivSqZeroExt.inl d)) =
      Ideal.Quotient.mk (firstOrderExtensionIdeal X.ring N)
        (TrivSqZeroExt.inl d)
    rw [TrivSqZeroExt.map_inl]

/-- The morphism `B(1) → B ⊕ M` of `CRIS(C/A)` given by the inclusion on the first factor and
the graph of `θ` on the second. -/
noncomputable def diagonalExtensionCoproductMap
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : DividedPowerThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁))
    (M : Type w) [AddCommGroup M] [Module X.ring M]
    [Module X.ringᵐᵒᵖ M] [IsCentralScalar X.ring M]
    (d : DividedPowerDerivation S.A X.ring
      X.fromBase.toRingHom M) :
    Y ⟶ firstOrderExtensionThickening X M :=
  BinaryCofan.IsColimit.desc h
    (firstOrderExtensionMapZero X M)
    (firstOrderExtensionMapGraph X M d)

/-- The coproduct map restricts to the inclusion on the first factor. -/
private theorem diagonalExtensionCoproductMap_inl_comp
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : DividedPowerThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁))
    (M : Type w) [AddCommGroup M] [Module X.ring M]
    [Module X.ringᵐᵒᵖ M] [IsCentralScalar X.ring M]
    (d : DividedPowerDerivation S.A X.ring
      X.fromBase.toRingHom M) :
    s₀ ≫ diagonalExtensionCoproductMap h M d = firstOrderExtensionMapZero X M :=
  BinaryCofan.IsColimit.inl_desc h _ _

/-- The coproduct map restricts to the graph of `θ` on the second factor. -/
private theorem diagonalExtensionCoproductMap_inr_comp
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : DividedPowerThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁))
    (M : Type w) [AddCommGroup M] [Module X.ring M]
    [Module X.ringᵐᵒᵖ M] [IsCentralScalar X.ring M]
    (d : DividedPowerDerivation S.A X.ring
      X.fromBase.toRingHom M) :
    s₁ ≫ diagonalExtensionCoproductMap h M d = firstOrderExtensionMapGraph X M d :=
  BinaryCofan.IsColimit.inr_desc h _ _

/-- The coproduct map followed by the projection to `B` is the codiagonal. -/
theorem diagonalExtensionCoproductMap_fst
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : DividedPowerThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁))
    (M : Type w) [AddCommGroup M] [Module X.ring M]
    [Module X.ringᵐᵒᵖ M] [IsCentralScalar X.ring M]
    (d : DividedPowerDerivation S.A X.ring
      X.fromBase.toRingHom M) :
    (diagonalExtensionCoproductMap h M d ≫
      firstOrderExtensionFstMap X M) =
      diagonalMap h := by
  have hf₀ : firstOrderExtensionMapZero X M ≫
      firstOrderExtensionFstMap X M = 𝟙 X := by
    apply DividedPowerThickening.Hom.ext
    apply DividedPowers.DPMorphism.ext
    funext x
    rfl
  have hf₁ : firstOrderExtensionMapGraph X M d ≫
      firstOrderExtensionFstMap X M = 𝟙 X := by
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

/-- The coproduct map on `s₀ b` is `(b, 0)`. -/
theorem diagonalExtensionCoproductMap_inl
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : DividedPowerThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁))
    (M : Type w) [AddCommGroup M] [Module X.ring M]
    [Module X.ringᵐᵒᵖ M] [IsCentralScalar X.ring M]
    (d : DividedPowerDerivation S.A X.ring
      X.fromBase.toRingHom M) (x : X.ring) :
    (diagonalExtensionCoproductMap h M d).hom.toRingHom
      (s₀.hom.toRingHom x) = TrivSqZeroExt.inl x :=
  congrArg (fun f : X ⟶ firstOrderExtensionThickening X M => f.hom.toRingHom x)
    (diagonalExtensionCoproductMap_inl_comp h M d)

/-- The coproduct map on `s₁ b` is `(b, θ b)`. -/
theorem diagonalExtensionCoproductMap_inr
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : DividedPowerThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁))
    (M : Type w) [AddCommGroup M] [Module X.ring M]
    [Module X.ringᵐᵒᵖ M] [IsCentralScalar X.ring M]
    (d : DividedPowerDerivation S.A X.ring
      X.fromBase.toRingHom M) (x : X.ring) :
    (diagonalExtensionCoproductMap h M d).hom.toRingHom
      (s₁.hom.toRingHom x) = graphRingHom d x :=
  congrArg (fun f : X ⟶ firstOrderExtensionThickening X M => f.hom.toRingHom x)
    (diagonalExtensionCoproductMap_inr_comp h M d)

/-- The `M`-coordinate of the coproduct map, a linear map on the diagonal kernel. -/
noncomputable def diagonalKernelCoordinateMap
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : DividedPowerThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁))
    (M : Type w) [AddCommGroup M] [Module X.ring M]
    [Module X.ringᵐᵒᵖ M] [IsCentralScalar X.ring M]
    (d : DividedPowerDerivation S.A X.ring
      X.fromBase.toRingHom M) :
    let q : Y.ring →+* X.ring := (diagonalMap h).hom.toRingHom
    letI : Algebra Y.ring X.ring := q.toAlgebra
    letI : Module Y.ring M := Module.compHom M q
    diagonalKernel h →ₗ[Y.ring] M := by
  let q : Y.ring →+* X.ring := (diagonalMap h).hom.toRingHom
  letI : Algebra Y.ring X.ring := q.toAlgebra
  letI : Module Y.ring M := Module.compHom M q
  let ψ := diagonalExtensionCoproductMap h M d
  let φ : Y.ring →+* TrivSqZeroExt X.ring M := ψ.hom.toRingHom
  have hfst (y : Y.ring) : (φ y).fst = q y := by
    have hc := diagonalExtensionCoproductMap_fst h M d
    have he := congrArg (fun g : Y ⟶ X => g.hom.toRingHom y) hc
    have hfstMap : (firstOrderExtensionFstMap X M).hom.toRingHom =
        (TrivSqZeroExt.fstHom X.ring X.ring M).toRingHom := by
      ext z
      rfl
    change (firstOrderExtensionFstMap X M).hom.toRingHom
        (ψ.hom.toRingHom y) = q y at he
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

/-- The coordinate map kills `K² + (K ∩ J(1))^{[2]}`. -/
theorem diagonalKernelCoordinateMap_killsRelations
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : DividedPowerThickening.{u, v, w} S}
    {s₀ s₁ : X ⟶ Y} (h : IsColimit (BinaryCofan.mk s₀ s₁))
    (M : Type w) [AddCommGroup M] [Module X.ring M]
    [Module X.ringᵐᵒᵖ M] [IsCentralScalar X.ring M]
    (d : DividedPowerDerivation S.A X.ring
      X.fromBase.toRingHom M) :
    let q : Y.ring →+* X.ring := (diagonalMap h).hom.toRingHom
    letI : Algebra Y.ring X.ring := q.toAlgebra
    letI : Module Y.ring M := Module.compHom M q
    diagonalRelations h ≤ LinearMap.ker (diagonalKernelCoordinateMap h M d) := by
  classical
  let q : Y.ring →+* X.ring := (diagonalMap h).hom.toRingHom
  let : Algebra Y.ring X.ring := q.toAlgebra
  let : Module Y.ring M := Module.compHom M q
  let ψ := diagonalExtensionCoproductMap h M d
  let φ : Y.ring →+* TrivSqZeroExt X.ring M := ψ.hom.toRingHom
  let K := diagonalKernel h
  have hfst (y : Y.ring) : (φ y).fst = q y := by
    have hc := diagonalExtensionCoproductMap_fst h M d
    have he := congrArg (fun g : Y ⟶ X => g.hom.toRingHom y) hc
    have hfstMap : (firstOrderExtensionFstMap X M).hom.toRingHom =
        (TrivSqZeroExt.fstHom X.ring X.ring M).toRingHom := by
      ext z
      rfl
    change (firstOrderExtensionFstMap X M).hom.toRingHom
        (ψ.hom.toRingHom y) = q y at he
    rw [hfstMap] at he
    exact he
  let Z : Ideal Y.ring := {
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
      secondDividedPowerIdeal Y.ring.dividedPowers
        (K ⊓ Y.ring.ideal) ≤ Z := by
    unfold secondDividedPowerIdeal
    apply Ideal.span_le.mpr
    rintro z ⟨n, hn, x, hx, rfl⟩
    rcases hx with ⟨hxK, hxJ⟩
    have hfx : (φ x).fst = 0 := by rw [hfst, RingHom.mem_ker.mp hxK]
    have hφx : φ x ∈ firstOrderExtensionIdeal X.ring M := by
      change (φ x).fst ∈ X.ring.ideal
      rw [hfx]
      exact X.ring.ideal.zero_mem
    have hdpmap := ψ.hom.isDPMorphism.dpow_comp (n := n) x hxJ
    have hcoords := (Classical.choose_spec
      (firstOrderExtension_dividedPowers X.ring M)).1 n (φ x) hn hφx
    have hzero :
        (Classical.choose (firstOrderExtension_dividedPowers X.ring M)).dpow n
          (φ x) = 0 := by
      apply TrivSqZeroExt.ext
      · rw [hcoords.1, hfx,
          X.ring.dividedPowers.dpow_eval_zero (by omega : n ≠ 0)]
        simp
      · rw [hcoords.2, hfx,
          X.ring.dividedPowers.dpow_eval_zero (by omega : n - 1 ≠ 0)]
        simp
    have hmapzero : φ (Y.ring.dividedPowers.dpow n x) = 0 := by
      change ψ.hom.toRingHom (Y.ring.dividedPowers.dpow n x) = 0
      rw [← hdpmap]
      exact hzero
    refine ⟨?_, ?_⟩
    · rw [RingHom.mem_ker]
      rw [← (diagonalMap h).hom.isDPMorphism.dpow_comp (n := n) x hxJ]
      rw [RingHom.mem_ker.mp hxK,
        X.ring.dividedPowers.dpow_eval_zero (by omega : n ≠ 0)]
    · rw [hmapzero]
      rfl
  have hsum : K ^ (2 : ℕ) +
      secondDividedPowerIdeal Y.ring.dividedPowers
        (K ⊓ Y.ring.ideal) ≤ Z := sup_le hKsq hdpIdeal
  intro q' k hk
  change ((Submodule.subtype (K : Submodule Y.ring Y.ring)) k) ∈
    K ^ (2 : ℕ) + secondDividedPowerIdeal Y.ring.dividedPowers
      (K ⊓ Y.ring.ideal) at hk
  exact (hsum hk).2

end DividedPowerThickening

end Crystalline

end
