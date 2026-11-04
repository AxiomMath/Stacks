module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitHigherDirectImageDegreeZeroColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitHigherDirectImageInjectiveVanishing

/-!
# Higher direct images along a limit of morphisms of schemes

Let `I` be a directed set, let `g_i : X_i ⟶ S_i` be an inverse system of quasi-compact and
quasi-separated morphisms of schemes over `I` whose transition morphisms
`f_{i'i} : X_{i'} ⟶ X_i` and `h_{i'i} : S_{i'} ⟶ S_i` are affine, and let `g : X ⟶ S` be the
limit of the `g_i`, with projections `f_i : X ⟶ X_i` and `h_i : S ⟶ S_i`. Let `(ℱ_i, φ_{i'i})` be
a system of abelian sheaves on `(X_i, f_{i'i})` and `ℱ = colim f_i⁻¹ℱ_i`. Then

`R^p g_* ℱ = colim_{i ∈ I} h_i⁻¹ R^p g_{i, *} ℱ_i`

for all `p ≥ 0` ([Stacks, Tag 0EYM]). The maps are those of the source: the base change maps on
higher direct images of the transition squares and of the projection squares, followed by the
maps `R^p g_{i', *}φ_{i'i}` and `R^p g_* ι_i`
(`Stacks.EtaleCohomology.LimitHigherDirectImage.transitionMap`,
`Stacks.EtaleCohomology.LimitHigherDirectImage.projectionMap`); they satisfy the cocycle
condition and form a cocone.

## Main results

* `Stacks.EtaleCohomology.LimitHigherDirectImage.isHigherDirectImageColimit` — the colimit
  assertion for every system with a colimit presentation, in every degree.
* `Stacks.EtaleCohomology.LimitHigherDirectImage.higherDirectImageColimit` — the cocycle condition
  of the transition maps, the cocone condition of the projection maps, and the colimit assertion.

## Implementation notes

The colimit `ℱ = colim f_i⁻¹ℱ_i` is given as a sheaf `ℱ` with maps `ι_i : f_i⁻¹ℱ_i ⟶ ℱ`
compatible with the transition maps and enjoying the universal property of the colimit
(`Stacks.EtaleCohomology.LimitHigherDirectImage.IsPullbackColimitPresentation`); such a
presentation exists
(`Stacks.EtaleCohomology.LimitHigherDirectImage.exists_isPullbackColimitPresentation`).
The colimit on `S` is expressed by the same universal property, the systems of
[Stacks, Tag 0EZL] satisfying the cocycle condition but not necessarily the identity law. The
directed set lives in the universe of the schemes.

## References

* [Stacks Project, Tag 0EYM](https://stacks.math.columbia.edu/tag/0EYM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.LimitHigherDirectImage

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I] {DX DS : Iᵒᵖ ⥤ Scheme.{u}}
  (γ : DX ⟶ DS) [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DX.map a)]
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DS.map a)] [∀ i, QuasiCompact (γ.app i)]
  [∀ i, QuasiSeparated (γ.app i)] {cX : Cone DX} {cS : Cone DS} (hcX : IsLimit cX)
  (hcS : IsLimit cS)

include hcX in
/-- **The colimit assertion, in every degree.** For every system `(ℱ_i, φ_{i'i})` of abelian
sheaves on the `X_i` and every presentation `ι_i : f_i⁻¹ℱ_i ⟶ ℱ` of `ℱ = colim f_i⁻¹ℱ_i`, the maps
`ψ_i : h_i⁻¹R^p g_{i, *}ℱ_i ⟶ R^p g_*ℱ` present `R^p g_*ℱ = colim h_i⁻¹R^p g_{i, *}ℱ_i`. -/
theorem isHigherDirectImageColimit (p : ℕ) (F : EtaleSheafSystem DX Ab.{u + 1})
    (𝓕 : Sheaf (smallEtaleTopology cX.pt) Ab.{u + 1})
    (ι : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (cX.π.app i)).obj (F.obj i) ⟶ 𝓕)
    (hι : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      (conePullbackComp cX a).inv.app (F.obj j) ≫
        (smallEtalePullbackAb (cX.π.app i)).map (F.map a) ≫ ι i = ι j)
    (hpres : IsPullbackColimitPresentation cX 𝓕 F ι) :
    IsHigherDirectImageColimit γ p cX cS hcS 𝓕 F ι :=
  isHigherDirectImageColimit_of_zero γ cX cS hcS
    (fun F _ ι hι hpres => isHigherDirectImageColimit_zero γ hcX hcS F ι hι hpres)
    (fun q G _ _ ιG hιG hG =>
      isZero_rightDerived_limitMorphism_of_injective γ hcX hcS G ιG hιG hG q)
    p F 𝓕 ι hι hpres

include hcX in
/-- Let `I` be a directed set, `g_i : X_i ⟶ S_i` an inverse system of quasi-compact and
quasi-separated morphisms of schemes with affine transition morphisms `f_{i'i}`, `h_{i'i}`,
`g : X ⟶ S` its limit with projections `f_i`, `h_i`, `(ℱ_i, φ_{i'i})` a system of abelian sheaves
on `(X_i, f_{i'i})` and `ℱ = colim f_i⁻¹ℱ_i`. Then for every `p`

* the maps `ψ_{i'i} : h_{i'i}⁻¹R^p g_{i, *}ℱ_i ⟶ R^p g_{i', *}ℱ_{i'}` satisfy the cocycle condition
  `ψ_{i''i} = ψ_{i''i'} ∘ h_{i''i'}⁻¹ψ_{i'i}`;
* the maps `ψ_i : h_i⁻¹R^p g_{i, *}ℱ_i ⟶ R^p g_*ℱ` satisfy `ψ_{i'} ∘ h_{i'}⁻¹ψ_{i'i} = ψ_i`;
* they present `R^p g_*ℱ = colim_{i ∈ I} h_i⁻¹R^p g_{i, *}ℱ_i`. -/
@[stacks 0EYM, sga "4 VII 5.11" "more general"]
theorem higherDirectImageColimit (p : ℕ) (F : EtaleSheafSystem DX Ab.{u + 1})
    (𝓕 : Sheaf (smallEtaleTopology cX.pt) Ab.{u + 1})
    (ι : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (cX.π.app i)).obj (F.obj i) ⟶ 𝓕)
    (hι : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      (conePullbackComp cX a).inv.app (F.obj j) ≫
        (smallEtalePullbackAb (cX.π.app i)).map (F.map a) ≫ ι i = ι j)
    (hpres : IsPullbackColimitPresentation cX 𝓕 F ι) :
    (∀ {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k),
        (systemPullbackComp DS Ab.{u + 1} a b).inv.app
              (((smallEtalePushforwardAb (γ.app k)).rightDerived p).obj (F.obj k)) ≫
            (systemPullback DS Ab.{u + 1} a).map (transitionMap γ p F b) ≫
              transitionMap γ p F a =
          transitionMap γ p F (a ≫ b)) ∧
      (∀ {i j : Iᵒᵖ} (a : i ⟶ j),
          (conePullbackComp cS a).inv.app
                (((smallEtalePushforwardAb (γ.app j)).rightDerived p).obj (F.obj j)) ≫
              (smallEtalePullbackAb (cS.π.app i)).map (transitionMap γ p F a) ≫
                projectionMap γ cX cS hcS p 𝓕 F ι i =
            projectionMap γ cX cS hcS p 𝓕 F ι j) ∧
        IsHigherDirectImageColimit γ p cX cS hcS 𝓕 F ι :=
  ⟨fun a b => transitionMap_comp γ p F a b,
    fun a => projectionMap_cocone γ p cX cS hcS 𝓕 F ι a (by rw [← hι a, Iso.hom_inv_id_app_assoc]),
    isHigherDirectImageColimit γ hcX hcS p F 𝓕 ι hι hpres⟩

end Stacks.EtaleCohomology.LimitHigherDirectImage
