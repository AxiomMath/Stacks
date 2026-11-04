module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.ComplexPullbackComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.ComplexSystemCohomologyColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitHigherDirectImageDimensionShift

/-!
# Higher direct images of a system of complexes along a limit of morphisms

Let `I` be a preordered set, let `g_i : X_i ⟶ S_i` be a morphism of inverse systems of schemes
over `I`, with transition morphisms `f_{i'i}` and `h_{i'i}`, let `f_i : X ⟶ X_i` be the
projections of a cone over the first system, `h_i : S ⟶ S_i` those of a limit cone over the
second and `g : X ⟶ S` the limit morphism. Let `(ℱ_i^•, φ_{i'i})` be a system of complexes of
abelian sheaves on the `X_{i, étale}` which is uniformly bounded below, `ℱ_i^n = 0` for `n < a`.

The cohomology sheaves `R^pg_{i, *}ℱ_i^• = H^p(Rg_{i, *}ℱ_i^•)` of the total right derived direct
images, with the maps

`ψ_{i'i} : h_{i'i}^{-1}R^pg_{i, *}ℱ_i^• ⟶ R^pg_{i', *}ℱ_{i'}^•`

given by the derived base change map of the transition squares followed by `R^pg_{i', *}φ_{i'i}`,
form a system of sheaves on `(S_i, h_{i'i})` in the sense of [Stacks, Tag 0EZL]: the cocycle
condition is the pasting law for the derived base change map. For a complex `ℱ^•` on `X_étale`
with maps `ι_i : f_i^{-1}ℱ_i^• ⟶ ℱ^•` compatible with the `φ_{i'i}`, the maps
`h_i^{-1}R^pg_{i, *}ℱ_i^• ⟶ R^pg_*ℱ^•` of the projection squares form a cocone over the pulled
back system. These are the system and the cocone of [Stacks, Tag 0GIV].

## Main definitions

* `Stacks.EtaleCohomology.LimitHigherDirectImage.complexHigherDirectImageSystem` — the sheaves
  `R^pg_{i, *}ℱ_i^•` with the maps `ψ_{i'i}`, as a system of sheaves on `(S_i, h_{i'i})`.
* `Stacks.EtaleCohomology.LimitHigherDirectImage.IsComplexHigherDirectImageColimit` — the
  colimit assertion `R^pg_*ℱ^• = colim_i h_i^{-1}R^pg_{i, *}ℱ_i^•` in a degree `p`.

## Main results

* `Stacks.EtaleCohomology.LimitHigherDirectImage.complexTransitionComparison_comp` and
  `Stacks.EtaleCohomology.LimitHigherDirectImage.smallEtaleComplexPullbackComparison_cone` — the
  comparisons of derived inverse images of the complexes compose along the transitions and the
  projections.
* `Stacks.EtaleCohomology.LimitHigherDirectImage.complexProjectionMap_cocone` — the maps
  `h_i^{-1}R^pg_{i, *}ℱ_i^• ⟶ R^pg_*ℱ^•` form a cocone.

## References

* [Stacks Project, Tag 0GIV](https://stacks.math.columbia.edu/tag/0GIV)
* [Stacks Project, Tag 0EZL](https://stacks.math.columbia.edu/tag/0EZL)
* [Stacks Project, Tag 0E47](https://stacks.math.columbia.edu/tag/0E47)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open CochainComplex (plusDerivedObj)

universe u

namespace Stacks.EtaleCohomology.LimitHigherDirectImage

attribute [local instance] HasDerivedCategory.standard

variable {I : Type u} [Preorder I] {DX DS : Iᵒᵖ ⥤ Scheme.{u}} (γ : DX ⟶ DS)

section System

variable (p a : ℤ) (F : EtaleComplexSystem DX) [∀ i, (F.obj i).IsStrictlyGE a]

/-- The comparison `R f_{i'i}^{-1}ℱ_i^• ⟶ ℱ_{i'}^•` attached to the transition map of a uniformly
bounded below system of complexes. -/
abbrev complexTransitionComparison {i j : Iᵒᵖ} (b : i ⟶ j) :
    (derivedPullbackAb (DX.map b)).obj (plusDerivedObj a (F.obj j)) ⟶
      plusDerivedObj a (F.obj i) :=
  smallEtaleComplexPullbackComparison a (DX.map b) (F.obj j) (F.obj i) (F.map b)

/-- **The comparisons of a system of complexes compose**, by the cocycle condition of the
system. -/
theorem complexTransitionComparison_comp {i j k : Iᵒᵖ} (b : i ⟶ j) (c : j ⟶ k) :
    complexTransitionComparison a F (b ≫ c) =
      (smallEtaleDerivedPullbackAbPlusComp' (DX.map c) (DX.map b) (DX.map (b ≫ c))
          (DX.map_comp b c)).inv.app (plusDerivedObj a (F.obj k)) ≫
        (derivedPullbackAb (DX.map b)).map (complexTransitionComparison a F c) ≫
          complexTransitionComparison a F b :=
  smallEtaleComplexPullbackComparison_paste a (DX.map c) (DX.map b) (DX.map (b ≫ c))
    (DX.map_comp b c) (F.obj k) (F.obj j) (F.obj i) (F.map c) (F.map b) (F.map (b ≫ c))
    (by rw [← systemPullbackComp_eq]; exact F.map_comp b c)

/-- **The system of higher direct images of a system of complexes**: the sheaves
`R^pg_{i, *}ℱ_i^•` on the `S_i`, with the derived base change maps of the transition squares
followed by `R^pg_{i', *}` of the transition maps of the complexes. The cocycle condition is the
pasting law for the derived base change map. -/
def complexHigherDirectImageSystem : EtaleSheafSystem DS Ab.{u + 1} where
  obj i := (homologyAb (DS.obj i) p).obj
    ((derivedPushforwardAb (γ.app i)).obj (plusDerivedObj a (F.obj i)))
  map b := derivedTransitionMap γ p b _ _ (complexTransitionComparison a F b)
  map_comp {i j k} b c := by
    rw [systemPullbackComp_eq]
    change _ = derivedBaseChangeHomologyMap (DS.map (b ≫ c)) (γ.app k) (γ.app i)
      (DX.map (b ≫ c)) (transition_comm γ (b ≫ c)) p _ _ (complexTransitionComparison a F (b ≫ c))
    rw [complexTransitionComparison_comp]
    exact (derivedBaseChangeHomologyMap_paste (γ.app k) (γ.app j) (γ.app i) (DS.map c)
      (DS.map b) (DX.map c) (DX.map b) (transition_comm γ c) (transition_comm γ b) p _ _ _ _ _
      (DS.map (b ≫ c)) (DS.map_comp b c) (DX.map (b ≫ c)) (DX.map_comp b c)
      (transition_comm γ (b ≫ c))).symm

end System

section Cocone

variable (p a : ℤ) (F : EtaleComplexSystem DX) [∀ i, (F.obj i).IsStrictlyGE a]
  (cX : Cone DX) (cS : Cone DS) (hcS : IsLimit cS)
  (𝓕 : CochainComplex (Sheaf (smallEtaleTopology cX.pt) Ab.{u + 1}) ℤ) [𝓕.IsStrictlyGE a]
  (ι : ∀ i : Iᵒᵖ, ((smallEtalePullbackAb (cX.π.app i)).mapHomologicalComplex _).obj (F.obj i) ⟶ 𝓕)

/-- **The comparisons of the cocone maps of a system of complexes compose with those of its
transition maps.** -/
theorem smallEtaleComplexPullbackComparison_cone (hι : F.IsPullbackCocone cX ι) {i j : Iᵒᵖ}
    (b : i ⟶ j) :
    smallEtaleComplexPullbackComparison a (cX.π.app j) (F.obj j) 𝓕 (ι j) =
      (smallEtaleDerivedPullbackAbPlusComp' (DX.map b) (cX.π.app i) (cX.π.app j)
          (cX.w b).symm).inv.app (plusDerivedObj a (F.obj j)) ≫
        (derivedPullbackAb (cX.π.app i)).map (complexTransitionComparison a F b) ≫
          smallEtaleComplexPullbackComparison a (cX.π.app i) (F.obj i) 𝓕 (ι i) :=
  smallEtaleComplexPullbackComparison_paste a (DX.map b) (cX.π.app i) (cX.π.app j) (cX.w b).symm
    (F.obj j) (F.obj i) 𝓕 (F.map b) (ι i) (ι j)
    (by rw [← conePullbackComp_eq]; exact hι b)

/-- **The cocone maps of [Stacks, Tag 0GIV]**: the maps `h_i^{-1}R^pg_{i, *}ℱ_i^• ⟶ R^pg_*ℱ^•`
of the projection squares, as maps out of the pulled back system. -/
abbrev complexLeg (i : Iᵒᵖ) :
    (smallEtalePullbackAb (cS.π.app i)).obj ((complexHigherDirectImageSystem γ p a F).obj i) ⟶
      (homologyAb cS.pt p).obj
        ((derivedPushforwardAb (limitMorphism γ cX cS hcS)).obj (plusDerivedObj a 𝓕)) :=
  derivedProjectionMap γ cX cS hcS p i (plusDerivedObj a (F.obj i)) (plusDerivedObj a 𝓕)
    (smallEtaleComplexPullbackComparison a (cX.π.app i) (F.obj i) 𝓕 (ι i))

/-- **The cocone maps of [Stacks, Tag 0GIV] form a cocone** over the pulled back system of
higher direct images, by the pasting law for the derived base change map. -/
theorem complexLeg_cocone (hι : F.IsPullbackCocone cX ι) {i j : Iᵒᵖ} (b : i ⟶ j) :
    (complexHigherDirectImageSystem γ p a F).pullbackDiagramMap cS (i := i) (j := j) b ≫
        complexLeg γ p a F cX cS hcS 𝓕 ι i =
      complexLeg γ p a F cX cS hcS 𝓕 ι j := by
  have h1 := derivedBaseChangeHomologyMap_paste (γ.app j) (γ.app i) (limitMorphism γ cX cS hcS)
      (DS.map b) (cS.π.app i) (DX.map b) (cX.π.app i) (transition_comm γ b)
      (limitMorphism_comp_π γ cX cS hcS i) p _ _ _ (complexTransitionComparison a F b)
      (smallEtaleComplexPullbackComparison a (cX.π.app i) (F.obj i) 𝓕 (ι i)) (cS.π.app j)
      (cS.w b).symm (cX.π.app j) (cX.w b).symm (limitMorphism_comp_π γ cX cS hcS j)
  have h2 := congrArg (derivedBaseChangeHomologyMap (cS.π.app j) (γ.app j)
      (limitMorphism γ cX cS hcS) (cX.π.app j) (limitMorphism_comp_π γ cX cS hcS j) p
      (plusDerivedObj a (F.obj j)) (plusDerivedObj a 𝓕))
    (smallEtaleComplexPullbackComparison_cone a F cX 𝓕 ι hι b)
  refine Eq.trans ?_ (h2.trans h1).symm
  rw [EtaleSheafSystem.pullbackDiagramMap, conePullbackComp_eq, Category.assoc]
  rfl

/-- **The colimit assertion of [Stacks, Tag 0GIV] in degree `p`**: the cocone maps exhibit
`R^pg_*ℱ^•` as the colimit of the pulled back system `h_i^{-1}R^pg_{i, *}ℱ_i^•`. -/
abbrev IsComplexHigherDirectImageColimit : Prop :=
  IsSystemColimit
    (fun i =>
      (smallEtalePullbackAb (cS.π.app i)).obj ((complexHigherDirectImageSystem γ p a F).obj i))
    (fun {i j} b =>
      (complexHigherDirectImageSystem γ p a F).pullbackDiagramMap cS (i := i) (j := j) b)
    ((homologyAb cS.pt p).obj
      ((derivedPushforwardAb (limitMorphism γ cX cS hcS)).obj (plusDerivedObj a 𝓕)))
    (complexLeg γ p a F cX cS hcS 𝓕 ι)

end Cocone

end Stacks.EtaleCohomology.LimitHigherDirectImage

end
