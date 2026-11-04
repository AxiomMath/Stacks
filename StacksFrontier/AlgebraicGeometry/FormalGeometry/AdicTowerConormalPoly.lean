module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicTowerConormal

/-!
# The polynomial algebra over the conormal algebras of an adic tower

Let `A`, `I`, `Xₙ` be as in `StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicTowerConormal`, and
let `a : ι → A` be a family of elements of `I`. Over every chart `X₀ ∩ U` (`U` affine in `Xₖ`) the
image of `aᵢ` in `Γ(Xₖ, U)` lies in the ideal `𝒥ₖ(U)` of `X₀`, so its class is a degree-one section
of the conormal algebra `Cₖ`. These classes glue to morphisms `𝒪_{X₀} ⟶ (Cₖ)₁`, they commute
pairwise, and the universal property of the symmetric algebra turns them into a unital
homomorphism `φₖ : 𝒪_{X₀}[xᵢ] ⟶ Cₖ` sending `xᵢ` to the class of `aᵢ`. The canonical maps
`Cₖ₊₁ ⟶ Cₖ` are compatible with the `φₖ`.

This is the surjection `𝓑 ⟶ 𝓕` of the second paragraph of the proof of [Stacks, Tag 089A], with
`𝓑` replaced by a polynomial algebra mapping onto it.

## References

* [Stacks Project, Tag 089A](https://stacks.math.columbia.edu/tag/089A)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.AdicTower

attribute [local instance_reducible] TopCat.Sheaf
attribute [local implicit_reducible] TopCat.Sheaf PresheafOfModules.presheaf
  SheafOfModules.toSheaf ModuleCat.restrictScalars

variable {A : Type u} [CommRing A] {I : Ideal A} {Xn : ℕ → Scheme.{u}}
  (q : ∀ n, Xn n ⟶ adicThickening A I n) (t : ∀ n, Xn n ⟶ Xn (n + 1))
  (hcart : ∀ n, IsPullback (t n) (q n) (q (n + 1)) (adicThickeningSucc A I n))
  [hci : ∀ k, IsClosedImmersion (incl t k)] [hct : ∀ k, IsClosedImmersion (t k)]
  {ι : Type u} (a : ι → A) (ha : ∀ i, a i ∈ I)

/-- The class of `aᵢ` in `𝒥ₖ/𝒥ₖ²` over a chart. -/
def genClass (k : ℕ) (i : ι) (V : (Xn k).affineOpens) :
    ((conormalAlg t k).piece 1).val.obj (op (chartOpen t k V)) :=
  (Stacks.Conormal.conormalAlgebra (incl t k)).localMap V (isClosedImmersion_resLE_incl t k V.1) 1
    ⟨genElt q k V.1 (a i), by rw [pow_one]; exact genElt_mem q t hcart k V (a i) (ha i)⟩

/-- The degree-one generator attached to `aᵢ` on the sections over a chart. -/
def genSection (k : ℕ) (i : ι) (V : (Xn k).affineOpens) :
    (SheafOfModules.unit (Xn 0).ringCatSheaf).val.obj (op (chartOpen t k V)) ⟶
      ((conormalAlg t k).piece 1).val.obj (op (chartOpen t k V)) :=
  ModuleCat.ofHom
    { toFun := fun (r : (Xn 0).ringCatSheaf.obj.obj (op (chartOpen t k V))) =>
        r • genClass q t hcart a ha k i V
      map_add' := fun r s => add_smul r s _
      map_smul' := fun c r => mul_smul c r _ }

omit hct in
/-- The generator `genSection` sends a section `r` to `r` times the class of `aᵢ`. -/
lemma genSection_apply (k : ℕ) (i : ι) (V : (Xn k).affineOpens)
    (r : (Xn 0).ringCatSheaf.obj.obj (op (chartOpen t k V))) :
    genSection q t hcart a ha k i V r = r • genClass q t hcart a ha k i V := rfl

omit hct in
/-- The classes of `aᵢ` over charts are compatible with restriction. -/
lemma genClass_restrict (k : ℕ) (i : ι) (V W : (Xn k).affineOpens)
    (h : chartOpen t k W ≤ chartOpen t k V) :
    ((conormalAlg t k).piece 1).val.map (homOfLE h).op (genClass q t hcart a ha k i V) =
      genClass q t hcart a ha k i W := by
  have hWV : W.1 ≤ V.1 := (preimage_incl_le_iff q t hcart k _ _).1 h
  exact (Stacks.Conormal.conormalAlgebra (incl t k)).localMap_naturality V W hWV h _ _ 1 _ _
    (genElt_restrict' q k hWV (a i)).symm

omit hct in
/-- The sectionwise generators `genSection` are compatible with restriction between charts. -/
lemma genSection_compatible (k : ℕ) (i : ι) :
    Stacks.BasisRestriction.IsCompatibleOnBasis (SheafOfModules.unit (Xn 0).ringCatSheaf)
      ((conormalAlg t k).piece 1) (chartOpen t k) (genSection q t hcart a ha k i) := by
  intro V W h r
  have hs := PresheafOfModules.map_smul ((conormalAlg t k).piece 1).val (homOfLE h).op r
    (genClass q t hcart a ha k i V)
  rw [genClass_restrict q t hcart a ha k i V W h] at hs
  exact hs.symm

/-- **The degree-one generator `𝒪_{X₀} ⟶ (Cₖ)₁` attached to `aᵢ`.** -/
def genHom (k : ℕ) (i : ι) : SheafOfModules.unit (Xn 0).ringCatSheaf ⟶ (conormalAlg t k).piece 1 :=
  Stacks.BasisRestriction.moduleSheafHomOfSectionHomOnBasis _ _ (chartOpen t k)
    (genSection q t hcart a ha k i) (isBasis_chartOpen q t hcart k)
    (genSection_compatible q t hcart a ha k i)

omit hct in
/-- On sections over a chart, `genHom` is the sectionwise generator `genSection`. -/
lemma genHom_app (k : ℕ) (i : ι) (V : (Xn k).affineOpens) :
    (genHom q t hcart a ha k i).val.app (op (chartOpen t k V)) = genSection q t hcart a ha k i V :=
  Stacks.BasisRestriction.moduleSheafHomOfSectionHomOnBasis_app _ _ _ _ _ _ V

/-- The morphism out of the free module on `ι` determined by the generators. -/
def genFree (k : ℕ) :
    SheafOfModules.free (R := (Xn 0).ringCatSheaf) ι ⟶ (conormalAlg t k).piece 1 :=
  Limits.Sigma.desc fun i => genHom q t hcart a ha k i

include q hcart in
omit hct in
/-- **The conormal algebras are commutative in degrees `(1, 1)`.** -/
lemma conormal_mul_comm_one (k : ℕ) (W : (Xn 0).Opens)
    (x y : ((conormalAlg t k).piece 1).val.obj (op W)) :
    ((conormalAlg t k).mul 1 1).app (op W) x y = ((conormalAlg t k).mul 1 1).app (op W) y x := by
  refine Stacks.BasisRestriction.moduleSheafSection_ext_onBasis _ (chartOpen t k)
    (isBasis_chartOpen q t hcart k) _ _ fun V hle => ?_
  rw [((conormalAlg t k).mul 1 1).naturality (homOfLE hle).op x y,
    ((conormalAlg t k).mul 1 1).naturality (homOfLE hle).op y x]
  have hV := isClosedImmersion_resLE_incl t k V.1
  obtain ⟨a', ha'⟩ := (Stacks.Conormal.conormalAlgebra (incl t k)).localMap_surjective V hV 1
    (((conormalAlg t k).piece 1).val.map (homOfLE hle).op x)
  obtain ⟨b', hb'⟩ := (Stacks.Conormal.conormalAlgebra (incl t k)).localMap_surjective V hV 1
    (((conormalAlg t k).piece 1).val.map (homOfLE hle).op y)
  have hab : (a' : Γ(Xn k, V.1)) * b' ∈ Stacks.Conormal.chartIdeal (incl t k) V ^ (1 + 1) := by
    rw [pow_add]; exact Ideal.mul_mem_mul a'.2 b'.2
  have hba : (b' : Γ(Xn k, V.1)) * a' ∈ Stacks.Conormal.chartIdeal (incl t k) V ^ (1 + 1) := by
    rw [pow_add]; exact Ideal.mul_mem_mul b'.2 a'.2
  have e1 := (Stacks.Conormal.conormalAlgebra (incl t k)).localMap_mul V hV 1 1 a' b' ⟨_, hab⟩ rfl
  have e2 := (Stacks.Conormal.conormalAlgebra (incl t k)).localMap_mul V hV 1 1 b' a' ⟨_, hba⟩ rfl
  rw [← ha', ← hb']
  exact e1.symm.trans ((congrArg _ (Subtype.ext (mul_comm _ _))).trans e2)

omit hct in
/-- The images of the generators of the free module pairwise commute in `Cₖ`. -/
lemma pairwiseCommutes_genFree (k : ℕ) :
    SheafOfModules.GradedAlgebra.PairwiseCommutes (genFree q t hcart a ha k) :=
  fun U _ _ => conormal_mul_comm_one q t hcart k U.unop _ _

/-- The universal property of the polynomial algebra `𝒪_{X₀}[xᵢ]`. -/
private abbrev polyIsUniversal (X : Scheme.{u}) (ι : Type u) :=
  (SheafOfModules.isSymmetricAlgebra_sheafifiedSymmetricAlgebra
      (Opens.grothendieckTopology ↥X) (SheafOfModules.free (R := X.ringCatSheaf) ι)).isUniversal

/-- **The unital homomorphism `φₖ : 𝒪_{X₀}[xᵢ] ⟶ Cₖ`** sending `xᵢ` to the class of `aᵢ`. -/
def polyHomTower (k : ℕ) :
    SheafOfModules.GradedAlgebra.UnitalHom (Stacks.Coherent.polyAlgebra (Xn 0) ι)
      (conormalAlg t k) :=
  (SheafOfModules.isSymmetricAlgebra_sheafifiedSymmetricAlgebra
      (Opens.grothendieckTopology ↥(Xn 0))
      (SheafOfModules.free (R := (Xn 0).ringCatSheaf) ι)).isUniversal.desc (conormalAlg t k)
    (genFree q t hcart a ha k) (pairwiseCommutes_genFree q t hcart a ha k)

omit hct in
/-- The homomorphism `φₖ` restricts to `genFree` on the degree-one generators. -/
lemma polyHomTower_extends (k : ℕ) :
    SheafOfModules.sheafifiedSymmetricGenerator (Opens.grothendieckTopology ↥(Xn 0))
        (SheafOfModules.free (R := (Xn 0).ringCatSheaf) ι) ≫
      (polyHomTower q t hcart a ha k).app 1 = genFree q t hcart a ha k :=
  (polyIsUniversal (Xn 0) ι).desc_extends _ _ _

/-- The canonical map `Cₖ₊₁ ⟶ Cₖ` sends the generator attached to `aᵢ` at level `k + 1` to the
generator attached to `aᵢ` at level `k`. -/
lemma genHom_step (k : ℕ) (i : ι) :
    genHom q t hcart a ha (k + 1) i ≫ (conormalStep t k).app 1 = genHom q t hcart a ha k i := by
  refine Stacks.BasisRestriction.moduleSheafHom_ext_onBasis _ _ (chartOpen t (k + 1))
    (isBasis_chartOpen q t hcart (k + 1)) _ _ fun V => ?_
  refine ModuleCat.hom_ext (LinearMap.ext fun (r : (Xn 0).ringCatSheaf.obj.obj
    (op (chartOpen t (k + 1) V))) => ?_)
  have h2 := congrArg (fun f => f r) (congrArg ModuleCat.Hom.hom
    (genHom_app q t hcart a ha k i ⟨t k ⁻¹ᵁ V.1, V.2.preimage _⟩))
  refine Eq.trans ?_ h2.symm
  show (stepApp t k 1).val.app (op (chartOpen t (k + 1) V))
      ((genHom q t hcart a ha (k + 1) i).val.app (op (chartOpen t (k + 1) V)) r) = _
  rw [genHom_app]
  have h1 := ((stepApp t k 1).val.app (op (chartOpen t (k + 1) V))).hom.map_smul r
    (genClass q t hcart a ha (k + 1) i V)
  have h3 := stepApp_localMap t k 1 V
    ⟨genElt q (k + 1) V.1 (a i), by rw [pow_one]; exact genElt_mem q t hcart (k + 1) V (a i) (ha i)⟩
    ⟨genElt q k (t k ⁻¹ᵁ V.1) (a i), by
      rw [pow_one]; exact genElt_mem q t hcart k ⟨_, V.2.preimage _⟩ (a i) (ha i)⟩
    (genElt_transition q t hcart k V.1 (a i)).symm
  exact h1.trans (congrArg (fun z => r • z) h3)

/-- The canonical map `Cₖ₊₁ ⟶ Cₖ` is compatible with the morphisms `genFree` out of the free module
on `ι`. -/
lemma genFree_step (k : ℕ) :
    genFree q t hcart a ha (k + 1) ≫ (conormalStep t k).app 1 = genFree q t hcart a ha k := by
  refine Limits.Sigma.hom_ext _ _ fun i => ?_
  have e (n : ℕ) : Limits.Sigma.ι (fun _ : ι => SheafOfModules.unit (Xn 0).ringCatSheaf) i ≫
      genFree q t hcart a ha n = genHom q t hcart a ha n i := Limits.Sigma.ι_desc _ _
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (conormalStep t k).app 1) (e _)).trans
    ((genHom_step q t hcart a ha k i).trans (e _).symm))

/-- **The structure maps are compatible with the canonical maps `Cₖ₊₁ ⟶ Cₖ`.** -/
lemma polyHomTower_step (k : ℕ) :
    (polyHomTower q t hcart a ha (k + 1)).comp (conormalStep t k) = polyHomTower q t hcart a ha k :=
  (polyIsUniversal (Xn 0) ι).desc_unique _ _ _ (by
    rw [SheafOfModules.GradedAlgebra.UnitalHom.comp_app]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (conormalStep t k).app 1)
      (polyHomTower_extends q t hcart a ha (k + 1))).trans (genFree_step q t hcart a ha k)))

end Stacks.AdicTower

end
