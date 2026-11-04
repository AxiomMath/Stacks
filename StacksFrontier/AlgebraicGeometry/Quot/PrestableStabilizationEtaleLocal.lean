module

public import StacksFrontier.AlgebraicGeometry.Quot.PrestableStabilization
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilies
public import StacksFrontier.AlgebraicGeometry.Quot.PrestableStabilizationTransitions
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureContractionEtaleCoveringDescent
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts

/-!
# Condition (1) of Stacks 0E8A is étale local on the base

Let `c : X ⟶ Y` be a morphism over the common base `S` of two families of curves, and let
`{φᵢ : Wᵢ ⟶ S}` be an étale covering by schemes of the site. If `c` satisfies condition (1) of
Stacks 0E8A for every base change `T ⟶ S` which factors through some `φᵢ`, then it satisfies
condition (1) for every base change. Given `T ⟶ S`, the family `{T ×_S Wᵢ ⟶ T}` is an étale
covering of `T`, and the base change of `c` to `T` becomes, after base change along each member,
a base change of `c` along `T ×_S Wᵢ ⟶ Wᵢ ⟶ S`; the conditions `c_*𝒪 = 𝒪` and `R¹c_*𝒪 = 0`
descend along étale coverings
(`AlgebraicGeometry.Space.isStructureContraction_of_isPullback_of_covering`).

## Main statements

* `AlgebraicGeometry.CurveFamily.isUniversalStructureContraction_of_etale`: condition (1) from
  condition (1) along the base changes factoring through the members of an étale covering.

## References

* [Stacks Project, Tag 0E8A](https://stacks.math.columbia.edu/tag/0E8A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

namespace CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

local notation "𝒯" => BigFppfOver.toScheme B integerBase hZ

/-- **Condition (1) of Stacks 0E8A is étale local on the base.** Let `c : X ⟶ Y` be a morphism
of families of curves over a common base `S` and `{φᵢ : Wᵢ ⟶ S}` an étale covering of `S` by
schemes of the site. If the base change of `c` along every `T ⟶ S` factoring as `T ⟶ Wᵢ ⟶ S`
has `c'_*𝒪 = 𝒪` and `R¹c'_*𝒪 = 0`, then `c` satisfies condition (1) of Stacks 0E8A. -/
theorem isUniversalStructureContraction_of_etale {X Y : CurveFamily B hZ} {hb : Y.base = X.base}
    {c : X.total ⟶ Y.total} {ι : Type u} {W : ι → BigFppfOver B integerBase hZ}
    (φ : ∀ i, W i ⟶ X.base) (hφ : ∀ i, Etale ((𝒯).map (φ i)))
    (hsurj : ∀ x : (𝒯).obj X.base, ∃ i, x ∈ Set.range ((𝒯).map (φ i)))
    (h : ∀ (i : ι) (T : BigFppfOver B integerBase hZ) (t : T ⟶ W i)
      (X' Y' : AlgebraicSpaces B integerBase hZ) (pX' : X' ⟶ X.total) (fX' : X' ⟶ schemeSpace T)
      (pY' : Y' ⟶ Y.total) (fY' : Y' ⟶ schemeSpace T) (c' : X' ⟶ Y'),
      IsPullback pX' fX' X.toBase (schemeSpaceMap (t ≫ φ i)) →
      IsPullback pY' fY' (Y.toBase ≫ eqToHom (congrArg schemeSpace hb))
        (schemeSpaceMap (t ≫ φ i)) →
      c' ≫ pY' = pX' ≫ c → c' ≫ fY' = fX' →
      Space.IsStructureContraction B integerBase hZ c') :
    X.IsUniversalStructureContraction B hZ Y hb c := by
  intro T k X' Y' pX' fX' pY' fY' c' sqX sqY hcY hcf
  have := hasPullbacks_bigFppfOver B integerBase hZ
  -- the étale covering `{Tᵢ = Wᵢ ×_S T ⟶ T}` of `T`
  let Tᵢ : ι → BigFppfOver B integerBase hZ := fun i => pullback (φ i) k
  let τ : ∀ i, Tᵢ i ⟶ T := fun i => pullback.snd (φ i) k
  let t : ∀ i, Tᵢ i ⟶ W i := fun i => pullback.fst (φ i) k
  have hτ : ∀ i, Etale ((𝒯).map (τ i)) := fun i =>
    Artin.ContractionSituation.etale_pullback_snd (φ i) k (hφ i)
  have hτsurj : ∀ x : (𝒯).obj T, ∃ i, x ∈ Set.range ((𝒯).map (τ i)) := by
    intro x
    obtain ⟨i, w, hw⟩ := hsurj (((𝒯).map k).base x)
    obtain ⟨z, -, hz⟩ := Artin.ContractionSituation.exists_pullback_point (φ i) k w x hw
    exact ⟨i, z, hz⟩
  -- the base changes `Y'ᵢ = Y' ×_T Tᵢ` and `X'ᵢ = X' ×_{Y'} Y'ᵢ`
  let Y'ᵢ : ι → AlgebraicSpaces B integerBase hZ := fun i =>
    AlgebraicSpaces.fiberProduct B integerBase hZ fY' (schemeSpaceMap (τ i))
  let p : ∀ i, Y'ᵢ i ⟶ Y' := fun i =>
    ObjectProperty.homMk (pullback.fst fY'.hom (schemeSpaceMap (τ i)).hom)
  let q : ∀ i, Y'ᵢ i ⟶ schemeSpace (Tᵢ i) := fun i =>
    ObjectProperty.homMk (pullback.snd fY'.hom (schemeSpaceMap (τ i)).hom)
  have hsq : ∀ i, IsPullback (p i) (q i) fY' (schemeSpaceMap (τ i)) := fun i =>
    AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ fY' (schemeSpaceMap (τ i))
  let X'ᵢ : ι → AlgebraicSpaces B integerBase hZ := fun i =>
    AlgebraicSpaces.fiberProduct B integerBase hZ c' (p i)
  let pX : ∀ i, X'ᵢ i ⟶ X' := fun i => ObjectProperty.homMk (pullback.fst c'.hom (p i).hom)
  let cᵢ : ∀ i, X'ᵢ i ⟶ Y'ᵢ i := fun i => ObjectProperty.homMk (pullback.snd c'.hom (p i).hom)
  have hX : ∀ i, IsPullback (pX i) (cᵢ i) c' (p i) := fun i =>
    AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ c' (p i)
  refine Space.isStructureContraction_of_isPullback_of_covering hτ hτsurj hsq hX fun i => ?_
  have hk : schemeSpaceMap (t i ≫ φ i) = schemeSpaceMap (τ i) ≫ schemeSpaceMap k := by
    rw [← schemeSpaceMap_comp, pullback.condition]
  have sqXi : IsPullback (pX i ≫ pX') (cᵢ i ≫ q i) X.toBase (schemeSpaceMap (t i ≫ φ i)) := by
    have h₁ := (hX i).paste_vert (hsq i)
    rw [hcf] at h₁
    rw [hk]
    exact h₁.paste_horiz sqX
  have sqYi : IsPullback (p i ≫ pY') (q i) (Y.toBase ≫ eqToHom (congrArg schemeSpace hb))
      (schemeSpaceMap (t i ≫ φ i)) := by
    rw [hk]
    exact (hsq i).paste_horiz sqY
  exact h i (Tᵢ i) (t i) (X'ᵢ i) (Y'ᵢ i) (pX i ≫ pX') (cᵢ i ≫ q i) (p i ≫ pY') (q i) (cᵢ i)
    sqXi sqYi (by rw [← Category.assoc, ← (hX i).w, Category.assoc, hcY, Category.assoc]) rfl

/-- **Condition (1) for a base change through a local stabilization.** Let `c : X ⟶ Y` be a
morphism of families of curves over `S`, `φ : W ⟶ S` a morphism of the site, `YW` a family of
curves over `W` with `YW = Y ×_S W` (via `r`), and `cW : X ×_S W ⟶ YW` a morphism over `W` with
`r ∘ cW` equal to `c` on `X ×_S W`. If `cW` satisfies condition (1) of Stacks 0E8A, then the base
change of `c` along every `T ⟶ W ⟶ S` has `c'_*𝒪 = 𝒪` and `R¹c'_*𝒪 = 0`. -/
theorem isStructureContraction_of_isUniversalStructureContraction_baseChangeAlong
    {X Y : CurveFamily B hZ} {hb : Y.base = X.base} {c : X.total ⟶ Y.total}
    {W : BigFppfOver B integerBase hZ} (φ : W ⟶ X.base) {YW : CurveFamily B hZ} {hY : YW.base = W}
    {r : YW.total ⟶ Y.total}
    (hr : IsPullback r (YW.toBase ≫ eqToHom (congrArg schemeSpace hY))
      (Y.toBase ≫ eqToHom (congrArg schemeSpace hb)) (schemeSpaceMap φ))
    {cW : AlgebraicSpaces.fiberProduct B integerBase hZ X.toBase (schemeSpaceMap φ) ⟶ YW.total}
    (hcW : cW ≫ YW.toBase ≫ eqToHom (congrArg schemeSpace hY) =
      ObjectProperty.homMk (pullback.snd X.toBase.hom (schemeSpaceMap φ).hom))
    (hcomm : (ObjectProperty.homMk (pullback.fst X.toBase.hom (schemeSpaceMap φ).hom) :
      AlgebraicSpaces.fiberProduct B integerBase hZ X.toBase (schemeSpaceMap φ) ⟶ X.total) ≫ c =
        cW ≫ r)
    (h1 : (X.baseChangeAlong φ).IsUniversalStructureContraction B hZ YW hY cW)
    (T : BigFppfOver B integerBase hZ) (t : T ⟶ W)
    (X' Y' : AlgebraicSpaces B integerBase hZ) (pX' : X' ⟶ X.total) (fX' : X' ⟶ schemeSpace T)
    (pY' : Y' ⟶ Y.total) (fY' : Y' ⟶ schemeSpace T) (c' : X' ⟶ Y')
    (sqX : IsPullback pX' fX' X.toBase (schemeSpaceMap (t ≫ φ)))
    (sqY : IsPullback pY' fY' (Y.toBase ≫ eqToHom (congrArg schemeSpace hb))
      (schemeSpaceMap (t ≫ φ)))
    (hcY : c' ≫ pY' = pX' ≫ c) (hcf : c' ≫ fY' = fX') :
    Space.IsStructureContraction B integerBase hZ c' := by
  have hXW := AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ X.toBase (schemeSpaceMap φ)
  rw [schemeSpaceMap_comp] at sqX sqY
  let pX'' := hXW.lift pX' (fX' ≫ schemeSpaceMap t) (by rw [sqX.w, Category.assoc])
  have sqX'' : IsPullback pX'' fX'
      (ObjectProperty.homMk (pullback.snd X.toBase.hom (schemeSpaceMap φ).hom))
      (schemeSpaceMap t) :=
    IsPullback.of_right (by rwa [hXW.lift_fst]) (hXW.lift_snd _ _ _) hXW
  let pY'' := hr.lift pY' (fY' ≫ schemeSpaceMap t) (by rw [sqY.w, Category.assoc])
  have sqY'' : IsPullback pY'' fY' (YW.toBase ≫ eqToHom (congrArg schemeSpace hY))
      (schemeSpaceMap t) :=
    IsPullback.of_right (by rwa [hr.lift_fst]) (hr.lift_snd _ _ _) hr
  have hcY'' : c' ≫ pY'' = pX'' ≫ cW := by
    apply hr.hom_ext
    · simp only [Category.assoc, pY'', pX'', hr.lift_fst, hcY, ← hcomm, hXW.lift_fst_assoc]
    · simp only [Category.assoc, pY'', pX'', hr.lift_snd, reassoc_of% hcf, hcW, hXW.lift_snd]
  exact h1 T t X' Y' pX'' fX' pY'' fY' c' sqX'' sqY'' hcY'' hcf

end CurveFamily

end AlgebraicGeometry

end
