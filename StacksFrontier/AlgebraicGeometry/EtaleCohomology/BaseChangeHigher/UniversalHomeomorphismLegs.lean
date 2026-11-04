module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedGeometricStalkSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceCohomology
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.AbelianDerivedBaseChangeCriteria

/-!
# Base change along universal homeomorphisms

Consider a commutative square of schemes

```
X' <--h-- Y
|f'       |e
v         v
S  <--g-- T
```

with the base change map `(f')⁻¹ g_* ⟶ h_* e⁻¹` on abelian sheaves of the small étale sites
and its derived version `R(f')⁻¹ Rg_* ⟶ Rh_* Re⁻¹` on bounded below derived categories. If
inverse image along `f'` and along `e` is an equivalence of categories of abelian sheaves, both
comparisons are isomorphisms, with no hypothesis on `g` or `h` and no need for the square to be
cartesian. By the topological invariance of the étale site, [Stacks, Tag 03SI], this applies when
`f'` and `e` are universal homeomorphisms.

## Main results

* `Stacks.EtaleCohomology.smallEtalePullbackAb_isEquivalence_of_universalHomeomorphism` — inverse
  image of abelian sheaves along a universal homeomorphism is an equivalence.
* `Stacks.EtaleCohomology.isIso_smallEtaleBaseChangeAb_of_isEquivalence` — the underived
  comparison is invertible when both inverse images are equivalences.
* `Stacks.EtaleCohomology.isIso_smallEtaleDerivedBaseChangeAb_of_isEquivalence` — the same for
  the derived comparison.
* `Stacks.EtaleCohomology.isIso_smallEtaleDerivedBaseChangeAb_of_universalHomeomorphism` — the
  derived comparison is invertible when `f'` and `e` are universal homeomorphisms.

## References

* [Stacks Project, Tag 03SI](https://stacks.math.columbia.edu/tag/03SI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Cohomology.BaseChange

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-- **Inverse image along a universal homeomorphism is an equivalence** of categories of abelian
sheaves on the small étale sites. This is the abelian form of [Stacks, Tag 03SI], part (2),
transported to `smallEtalePullbackAb`. -/
theorem smallEtalePullbackAb_isEquivalence_of_universalHomeomorphism {X Y : Scheme.{u}}
    (f : X ⟶ Y) [UniversalHomeomorphism f] : (smallEtalePullbackAb f).IsEquivalence :=
  have := etaleAbelianInverseImage_isEquivalence_of_universalHomeomorphism.{u, u + 1} f
  Functor.isEquivalence_of_iso (smallEtalePullbackAbIsoEtaleAbelianInverseImage f).symm

section Square

variable {X' Y S T : Scheme.{u}} (f' : X' ⟶ S) (g : T ⟶ S) (h : Y ⟶ X') (e : Y ⟶ T)
  (w : h ≫ f' = e ≫ g)

/-- **The underived base change comparison is invertible when both inverse images are
equivalences.** For a commutative square `h ≫ f' = e ≫ g` such that inverse image of abelian
sheaves along `f'` and along `e` is an equivalence, the comparison `(f')⁻¹ g_* ⟶ h_* e⁻¹` is an
isomorphism. -/
theorem isIso_smallEtaleBaseChangeAb_of_isEquivalence
    [(smallEtalePullbackAb f').IsEquivalence] [(smallEtalePullbackAb e).IsEquivalence] :
    IsIso (smallEtaleBaseChangeAb f' g h e w) := by
  have := (smallEtaleAdjunctionAb f').isEquivalence_right_of_isEquivalence_left
  dsimp only [smallEtaleBaseChangeAb, Stacks.Cohomology.BaseChange.mate]
  infer_instance

/-- **The derived base change comparison is invertible when both inverse images are
equivalences.** For a commutative square `h ≫ f' = e ≫ g` such that inverse image of abelian
sheaves along `f'` and along `e` is an equivalence, the comparison `R(f')⁻¹ Rg_* ⟶ Rh_* Re⁻¹` on
bounded below derived categories is an isomorphism. -/
theorem isIso_smallEtaleDerivedBaseChangeAb_of_isEquivalence
    [(smallEtalePullbackAb f').IsEquivalence] [(smallEtalePullbackAb e).IsEquivalence] :
    IsIso (smallEtaleDerivedBaseChangeAb f' g h e w) := by
  have hτ := isIso_smallEtaleBaseChangeAb_of_isEquivalence f' g h e w
  have ue := exactUnit_isIso (smallEtalePullbackAb e)
  have hQh : ∀ K : HomotopyCategory.Plus (Sheaf (smallEtaleTopology T) Ab.{u + 1}),
      (∀ n : ℤ, Injective (K.obj.as.X n)) →
      IsIso ((smallEtaleDerivedBaseChangeAb f' g h e w).app (DerivedCategory.Plus.Qh.obj K)) := by
    intro K hK
    have hK' : ∀ n : ℤ,
        Injective (((smallEtalePullbackAb e).mapHomotopyCategoryPlus.obj K).obj.as.X n) :=
      fun n ↦ Functor.PreservesInjectiveObjects.injective_obj (hK n)
    exact isIso_derived_app_Qh_of_acyclic _ _ _ _ _ _ K inferInstance
      (NatIso.isIso_app_of_isIso _ _) inferInstance fun _ ↦ NatIso.isIso_app_of_isIso _ _
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun M ↦ ?_
  obtain ⟨n, hn⟩ := M.property
  have : M.IsGE n := (DerivedCategory.Plus.isGE_ι_obj_iff M n).1 hn
  obtain ⟨L, -, ⟨i⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso M n
  let K : HomotopyCategory.Plus (Sheaf (smallEtaleTopology T) Ab.{u + 1}) :=
    (HomotopyCategory.Plus.quotient _).obj
      ((InjectiveObject.ι (Sheaf (smallEtaleTopology T) Ab.{u + 1})).mapCochainComplexPlus.obj L)
  have j : DerivedCategory.Plus.Qh.obj K ≅ M :=
    DerivedCategory.Plus.ι.preimageIso (X := DerivedCategory.Plus.Qh.obj K)
      (Y := DerivedCategory.Plus.Q.obj ((InjectiveObject.ι _).mapCochainComplexPlus.obj L))
      ((DerivedCategory.quotientCompQhIso (Sheaf (smallEtaleTopology T) Ab.{u + 1})).app
        ((InjectiveObject.ι _).mapCochainComplexPlus.obj L).obj) ≪≫ i
  exact (NatTrans.isIso_app_iff_of_iso _ j).1 (hQh K fun _ ↦ inferInstance)

/-- **The derived base change comparison along universal homeomorphisms is invertible.** For a
commutative square `h ≫ f' = e ≫ g` of schemes in which `f'` and `e` are universal
homeomorphisms, the comparison `R(f')⁻¹ Rg_* ⟶ Rh_* Re⁻¹` on bounded below derived categories of
abelian sheaves on the small étale sites is an isomorphism. -/
theorem isIso_smallEtaleDerivedBaseChangeAb_of_universalHomeomorphism
    [UniversalHomeomorphism f'] [UniversalHomeomorphism e] :
    IsIso (smallEtaleDerivedBaseChangeAb f' g h e w) :=
  have := smallEtalePullbackAb_isEquivalence_of_universalHomeomorphism f'
  have := smallEtalePullbackAb_isEquivalence_of_universalHomeomorphism e
  isIso_smallEtaleDerivedBaseChangeAb_of_isEquivalence f' g h e w

end Square

end Stacks.EtaleCohomology

end
