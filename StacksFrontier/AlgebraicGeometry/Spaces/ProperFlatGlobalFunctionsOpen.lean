module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFlatGlobalFunctionsLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFlatGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ProperFlatNoetherianModel
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Basic
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeRestrictRepresentability

/-!
# The locus `κ = H⁰(X_κ, 𝒪)` of a proper flat algebraic space over an affine base is open

Let `X` be an algebraic space over `Spec A` whose structure morphism is proper, flat and of finite
presentation, and let `Spec k ⟶ Spec A` be a point with `k` a field such that
`k = H⁰(X_k, 𝒪_{X_k})`. Then there is `h ∈ A` not vanishing at that point such that
`A' = H⁰(X_{A'}, 𝒪_{X_{A'}})` for every `A`-algebra `A'` in which `h` is invertible. This is the
local form of Stacks 0E6B (a) and of Stacks 0E0R at `i = 0`.

## Main results

* `AlgebraicGeometry.Space.exists_away_bijective_algebraMap_globalFunctions_relocalizeRestrict`:
  the statement above.

## References

* [Stacks Project, Tag 0E6B](https://stacks.math.columbia.edu/tag/0E6B)
* [Stacks Project, Tag 0E0R](https://stacks.math.columbia.edu/tag/0E0R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] CategoryTheory.Limits.hasProduct_fin_succ_of_hasBinaryProducts

variable {B : BigFppfSite.{u}} {A : Type u} [CommRing A] {hA : B.Contains (Spec (.of A))}
  {X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u}

/-- `A' = H⁰(X_{A'}, 𝒪)` for the base change along a composite `Spec A' ⟶ Spec A ⟶ Spec A₀` of a
model `X ≅ X₀ ×_{Spec A₀} Spec A` is `A' = H⁰` for the base change of `X₀` along the composite. -/
theorem bijective_algebraMap_globalFunctions_relocalizeRestrict_comp_iff {A₀ : Type u}
    [CommRing A₀] {hA₀ : B.Contains (Spec (.of A₀))}
    {X₀ : (BigFppfOver B (Spec (.of A₀)) hA₀)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)
    (hX₀ : IsAlgebraicSpace B (Spec (.of A₀)) hA₀ X₀) (g₀ : B.obj hA ⟶ B.obj hA₀)
    (e : X ≅ (OverShriek.relocalizeRestrict g₀).obj X₀) (A' : Type u) [CommRing A']
    (hA' : B.Contains (Spec (.of A'))) (g : B.obj hA' ⟶ B.obj hA) :
    Function.Bijective (algebraMap A'
        (globalFunctions B (Spec (.of A')) hA' ((OverShriek.relocalizeRestrict g).obj X))) ↔
      Function.Bijective (algebraMap A'
        (globalFunctions B (Spec (.of A')) hA'
          ((OverShriek.relocalizeRestrict (g ≫ g₀)).obj X₀))) :=
  bijective_algebraMap_globalFunctions_congr B
    (isAlgebraicSpace_relocalizeRestrict B (Spec (.of A')) (Spec (.of A)) hA' hA g X hX)
    (isAlgebraicSpace_relocalizeRestrict B (Spec (.of A')) (Spec (.of A₀)) hA' hA₀ (g ≫ g₀) X₀ hX₀)
    ((OverShriek.relocalizeRestrict g).mapIso e ≪≫ OverShriek.relocalizeRestrictCompIso g g₀ X₀)

/-- The inclusion of a composite of maps lying over ring maps is `Spec` of the composite. -/
private theorem inclusion_map_comp_eq_spec_map {A₀ A' : Type u} [CommRing A₀] [CommRing A']
    {hA₀ : B.Contains (Spec (.of A₀))} {hA' : B.Contains (Spec (.of A'))}
    (g₀ : B.obj hA ⟶ B.obj hA₀) (g : B.obj hA' ⟶ B.obj hA) (φ : A₀ →+* A) (ψ : A →+* A')
    (hg₀ : B.inclusion.map g₀ = Spec.map (CommRingCat.ofHom φ))
    (hg : B.inclusion.map g = Spec.map (CommRingCat.ofHom ψ)) :
    B.inclusion.map (g ≫ g₀) = Spec.map (CommRingCat.ofHom (ψ.comp φ)) := by
  rw [Functor.map_comp, hg, hg₀, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

/-- **`A' = H⁰(X_{A'}, 𝒪)` near a point of `Spec A` where it holds on the fibre.** Let `X` be an
algebraic space over `Spec A` whose structure morphism is proper, flat and of finite
presentation, and `Spec k ⟶ Spec A` a point, `k` a field, with `k = H⁰(X_k, 𝒪_{X_k})`. Then there
is `h ∈ A` with nonzero image in `k` such that `A' = H⁰(X_{A'}, 𝒪_{X_{A'}})` for every
`A`-algebra `A'` in which `h` is invertible. -/
theorem exists_away_bijective_algebraMap_globalFunctions_relocalizeRestrict
    (hX : IsAlgebraicSpace B (Spec (.of A)) hA X) (f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hA))))
    (hprop : IsProper B (Spec (.of A)) hA f) (hflat : IsFlat B (Spec (.of A)) hA f)
    (hfp : IsFinitePresentation B (Spec (.of A)) hA f)
    (k : Type u) [Field k] [Algebra A k] (hk : B.Contains (Spec (.of k)))
    (gk : B.obj hk ⟶ B.obj hA)
    (hgk : B.inclusion.map gk = Spec.map (CommRingCat.ofHom (algebraMap A k)))
    (hbij : Function.Bijective (algebraMap k
      (globalFunctions B (Spec (.of k)) hk ((OverShriek.relocalizeRestrict gk).obj X)))) :
    ∃ h : A, algebraMap A k h ≠ 0 ∧
      ∀ (A' : Type u) [CommRing A'] [Algebra A A'] (hA' : B.Contains (Spec (.of A')))
        (g : B.obj hA' ⟶ B.obj hA),
        B.inclusion.map g = Spec.map (CommRingCat.ofHom (algebraMap A A')) →
        IsUnit (algebraMap A A' h) →
        Function.Bijective (algebraMap A'
          (globalFunctions B (Spec (.of A')) hA' ((OverShriek.relocalizeRestrict g).obj X))) := by
  obtain ⟨A₀, _, _, _, hA₀, X₀, hX₀, f₀, hprop₀, hflat₀, hfp₀, hiso⟩ :=
    exists_finiteType_model_of_isProper B hX f hprop hflat hfp
  have : IsNoetherianRing A₀ := Algebra.FiniteType.isNoetherianRing ℤ A₀
  let g₀ : B.obj hA ⟶ B.obj hA₀ :=
    ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap A₀ A)))
  obtain ⟨e⟩ := hiso g₀ rfl
  obtain ⟨W, c, hW, hcs, hce⟩ :=
    exists_isAffine_isEtale_isSurjective_chart_of_isQuasiCompact B (Spec (.of A₀)) hA₀ hX₀ f₀
      hfp₀.2.1
  let U : SmallEtale B (Spec (.of A₀)) hA₀ X₀ :=
    ⟨CostructuredArrow.mk c, presheaf_etale_of_isEtale B (Spec (.of A₀)) hA₀ hce⟩
  have hUs : IsSurjective B (Spec (.of A₀)) hA₀ U.obj.hom :=
    isSurjective_of_presheafSurjective B (Spec (.of A₀)) hA₀ c hcs
  have hUa : IsAffineChart B (Spec (.of A₀)) hA₀ X₀ U := hW
  have hsep : HasAffineIntersections B (Spec (.of A₀)) hA₀ X₀ :=
    hasAffineIntersections_of_isSeparated A₀ B hA₀ X₀ hX₀ f₀ hprop₀.1
  let V₀ := (Stacks.CechTop.cechNerve
    (show (smallEtaleRingedSite B (Spec (.of A₀)) hA₀ X₀ hX₀).C from U)).obj (op ⦋0⦌)
  let eV : V₀ ≅ U := IsLimit.conePointUniqueUpToIso
    (limit.isLimit (Discrete.functor fun _ : Fin 1 => U))
    (limitConeOfUnique (fun _ : Fin 1 => U)).isLimit
  have hw : yoneda.map ((SmallEtale.toOver B (Spec (.of A₀)) hA₀ X₀).map eV.hom) ≫ c =
      V₀.obj.hom :=
    CostructuredArrow.w eV.hom.hom
  have hps : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (Spec (.of A₀)) hA₀)).presheaf V₀.obj.hom := by
    let e' := yoneda.mapIso ((SmallEtale.toOver B (Spec (.of A₀)) hA₀ X₀).mapIso eV)
    have hw' : e'.hom ≫ c = V₀.obj.hom := hw
    rw [← hw']
    exact (MorphismProperty.cancel_left_of_respectsIso _ e'.hom c).2 hcs
  have hWa := isAffineChart_cechNerve B (Spec (.of A₀)) hA₀ X₀ hsep hUa 0
  have hRa := isAffineChart_cechNerve B (Spec (.of A₀)) hA₀ X₀ hsep hUa 1
  let := siteObjectAlgebra B A₀ (cechW hX₀ U)
  let := siteObjectAlgebra B A₀ (cechR hX₀ U)
  have hiff := fun (A' : Type u) [CommRing A'] [Algebra A₀ A'] (hA' : B.Contains (Spec (.of A')))
      (g : B.obj hA' ⟶ B.obj hA₀)
      (hg : B.inclusion.map g = Spec.map (CommRingCat.ofHom (algebraMap A₀ A'))) =>
    bijective_algebraMap_globalFunctions_relocalizeRestrict_iff B X₀ hX₀ V₀.obj.hom hps
      V₀.property (cechR₁ hX₀ U) (cechR₂ hX₀ U) (isPullback_cechNerve_one B _ hA₀ X₀ hX₀ U)
      hWa hRa g hg
  let : Algebra A₀ k := ((algebraMap A k).comp (algebraMap A₀ A)).toAlgebra
  have hk := (hiff k hk (gk ≫ g₀)
    (inclusion_map_comp_eq_spec_map g₀ gk (algebraMap A₀ A) (algebraMap A k) rfl hgk)).1
    ((bijective_algebraMap_globalFunctions_relocalizeRestrict_comp_iff hX hX₀ g₀ e k hk gk).1 hbij)
  let P₀ : Ideal A₀ := RingHom.ker (algebraMap A₀ k)
  have : P₀.IsPrime := RingHom.ker_isPrime _
  let φ : P₀.ResidueField →+* k := Ideal.ResidueField.lift P₀ (algebraMap A₀ k) le_rfl
    (fun a ha => (isUnit_iff_ne_zero.2 fun h0 => ha h0))
  let : Algebra P₀.ResidueField k := φ.toAlgebra
  have : IsScalarTower A₀ P₀.ResidueField k := IsScalarTower.of_algebraMap_eq fun a =>
    (Ideal.ResidueField.lift_algebraMap P₀ (algebraMap A₀ k) le_rfl _ a).symm
  have hκ := AlgHom.EqualizerTensorExact.of_faithfullyFlat (k := P₀.ResidueField) (N := k) hk
  obtain ⟨h₀, hh₀, hnear⟩ := exists_away_equalizerTensorExact hX₀ U f₀ hprop₀ hflat₀ hUs hUa P₀ hκ
  refine ⟨algebraMap A₀ A h₀, hh₀, fun A' _ _ hA' g hg hu => ?_⟩
  let : Algebra A₀ A' := ((algebraMap A A').comp (algebraMap A₀ A)).toAlgebra
  exact (bijective_algebraMap_globalFunctions_relocalizeRestrict_comp_iff hX hX₀ g₀ e A' hA' g).2
    ((hiff A' hA' (g ≫ g₀)
      (inclusion_map_comp_eq_spec_map g₀ g (algebraMap A₀ A) (algebraMap A A') rfl hg)).2
      (hnear A' hu))

end AlgebraicGeometry.Space

end
