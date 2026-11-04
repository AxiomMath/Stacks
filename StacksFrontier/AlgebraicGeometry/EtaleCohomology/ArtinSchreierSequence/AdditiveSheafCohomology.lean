module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.SmallEtaleAssociatedSheafRestriction
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.CategoryTheory.Sites.UniverseLiftInjective
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.CohomologyVanishesLocally

public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparisonUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.AdditiveSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.SmallEtaleGlobalCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.SmallEtaleGlobalCohomologyUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sheafification.SmallEtaleCoefficientUniverse
public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.RestrictionUnivLE

/-!
# The étale cohomology of `𝐆_a` is the cohomology of the structure sheaf

Let `X` be a scheme. The étale cohomology of the additive group `𝐆_a` on the small étale site of
`X`, computed with coefficients in `AddCommGrpCat.{max (u + 1) v}`, agrees in positive degree with
the cohomology of the structure sheaf `𝒪_X` on the underlying topological space:

  `H ^ (n + 1) (X, 𝒪_X) ≃+ H ^ (n + 1) (X_étale, 𝐆_a)`.

This is [Stacks, Tag 03P2] for the structure sheaf, read on the sheaf
`Stacks.ArtinSchreier.additiveSheaf` that the Artin–Schreier sequence of [Stacks, Tag 0A3J] is
built from.

## Main definitions

* `Stacks.ArtinSchreier.uliftAssociatedUnitIsoAdditiveSheaf`: `𝐆_a` is the universe lift of the
  associated sheaf `𝒪_Xᵃ` of the structure sheaf.
* `Stacks.ArtinSchreier.hgroupAddEquivSheafHAdditiveSheaf`: **the comparison of cohomology**.

## Main results

* `Stacks.ArtinSchreier.subsingleton_sheafH_additiveSheaf_of_isZero_hgroup_unconditional`:
  vanishing of the cohomology of `𝒪_X` in a positive degree gives vanishing of the étale
  cohomology of `𝐆_a` in that degree.

## Implementation notes

Three identifications are composed.

* `AlgebraicGeometry.hgroupIsoSmallEtaleGlobalCohomology`, which is [Stacks, Tag 03P2] for
  `𝒞 = X_étale` in the shape `Hgroup` on the Zariski side and `CategoryTheory.Sheaf.H` on the
  étale side, for the associated sheaf `𝒪_Xᵃ`, with coefficients in `AddCommGrpCat.{u}`.
* `AlgebraicGeometry.Scheme.smallEtaleSheafHUliftAddEquiv`: étale cohomology does not depend on
  the coefficient universe.
* `Stacks.ArtinSchreier.uliftAssociatedUnitIsoAdditiveSheaf`: the sections of `𝒪_Xᵃ` over an
  étale `T ⟶ X` are `Γ(T, T⁺ 𝒪_X)`, which `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso`
  identifies with `Γ(T, 𝒪_T)`, the sections of `𝐆_a`; naturality is
  `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_app_pullbackSectionsMap`.

The degree is positive because `AlgebraicGeometry.hgroupIsoSheafCohomology`, on which the first
identification rests, is.

## References

* [Stacks Project, Tag 03P2](https://stacks.math.columbia.edu/tag/03P2)
* [Stacks Project, Tag 0A3J](https://stacks.math.columbia.edu/tag/0A3J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
open AlgebraicGeometry Stacks.Sheaves.UniverseLift

universe w v u

namespace Stacks.ArtinSchreier

variable (X : Scheme.{u})

/-- On the sections over an étale `X`-scheme `U`, the universe lift of `𝒪_Xᵃ` is `𝐆_a`: the
sections of `𝒪_Xᵃ` over `U` are `Γ(U, U⁺ 𝒪_X)`, and `pullbackUnitIso` identifies them with
`Γ(U, 𝒪_U)`. -/
def uliftAssociatedUnitIsoAdditiveSheafApp (U : X.Etale) :
    (((uliftSheafFunctor.{max (u + 1) v, u} X.smallEtaleTopology).obj
      (smallEtaleAssociatedSheaf X (Scheme.unitModule X))).obj.obj (op U)) ≅
      (additiveSheaf.{u, v} X).obj.obj (op U) :=
  AddCommGrpCat.uliftFunctor.{max (u + 1) v, u}.mapIso
    (((Scheme.Modules.toPresheaf U.left).mapIso
      (Scheme.Modules.pullbackUnitIso U.hom)).app (op ⊤))

/-- **`𝐆_a` is the universe lift of the associated sheaf of the structure sheaf.** The sheaf
`𝒪_Xᵃ`, whose sections over an étale `T ⟶ X` are `Γ(T, T⁺ 𝒪_X)` with coefficients in
`AddCommGrpCat.{u}`, becomes `𝐆_a`, whose sections are `Γ(T, 𝒪_T)`, once its universe is
raised to `max (u + 1) v`. -/
def uliftAssociatedUnitIsoAdditiveSheaf :
    (uliftSheafFunctor.{max (u + 1) v, u} X.smallEtaleTopology).obj
        (smallEtaleAssociatedSheaf X (Scheme.unitModule X)) ≅ additiveSheaf.{u, v} X :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (NatIso.ofComponents (fun U ↦ uliftAssociatedUnitIsoAdditiveSheafApp.{v} X U.unop)
      (fun {U V} f ↦ by
        ext x
        exact congrArg ULift.up
          (Scheme.Modules.pullbackUnitIso_app_pullbackSectionsMap
            ((Scheme.Etale.forget X).map f.unop) x.down)))

variable [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]

/-- **The étale cohomology of `𝐆_a` is the cohomology of the structure sheaf**, in positive
degree:

  `H ^ (n + 1) (X, 𝒪_X) ≃+ H ^ (n + 1) (X_étale, 𝐆_a)`,

with étale coefficients in `AddCommGrpCat.{max (u + 1) v}` and an arbitrary `Ext` universe.

This is [Stacks, Tag 03P2] for the associated sheaf of the structure sheaf,
`AlgebraicGeometry.hgroupIsoSmallEtaleGlobalCohomology`, followed by the independence of étale
cohomology of the coefficient universe and the identification of the lifted associated sheaf
with `𝐆_a`. -/
def hgroupAddEquivSheafHAdditiveSheaf (n : ℕ) :
    Hgroup X.ringCatSheaf ⊤ (n + 1) (SheafOfModules.unit X.ringCatSheaf) ≃+
      Sheaf.H.{w} (additiveSheaf.{u, v} X) (n + 1) :=
  letI : HasExt.{u} (Sheaf (Opens.grothendieckTopology (X : Type u)) AddCommGrpCat.{u}) :=
    Stacks.Topology.hasExt_sheafOpens.{u, u} X.toTopCat
  letI : HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
    IsGrothendieckAbelian.hasExt.{u} _
  (hgroupIsoSmallEtaleGlobalCohomology X (Scheme.unitModule X) n).addCommGroupIsoToAddEquiv.trans
    ((Scheme.smallEtaleSheafHUliftAddEquiv.{u, w, v} X _ (n + 1)).trans
      ((extFunctorObj.{w} _ (n + 1)).mapIso
        (uliftAssociatedUnitIsoAdditiveSheaf.{v} X)).addCommGroupIsoToAddEquiv)

/-- `hgroupAddEquivSheafHAdditiveSheaf` on a class: the three comparisons applied in turn, the
last one being `H ^ (n + 1)` of `uliftAssociatedUnitIsoAdditiveSheaf`. -/
theorem hgroupAddEquivSheafHAdditiveSheaf_apply (n : ℕ)
    (x : Hgroup X.ringCatSheaf ⊤ (n + 1) (SheafOfModules.unit X.ringCatSheaf)) :
    letI : HasExt.{u} (Sheaf (Opens.grothendieckTopology (X : Type u)) AddCommGrpCat.{u}) :=
      Stacks.Topology.hasExt_sheafOpens.{u, u} X.toTopCat
    letI : HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
      IsGrothendieckAbelian.hasExt.{u} _
    hgroupAddEquivSheafHAdditiveSheaf.{w, v} X n x =
      Sheaf.H.map (uliftAssociatedUnitIsoAdditiveSheaf.{v} X).hom (n + 1)
        (Scheme.smallEtaleSheafHUliftAddEquiv.{u, w, v} X _ (n + 1)
          ((hgroupIsoSmallEtaleGlobalCohomology X (Scheme.unitModule X) n).hom x)) :=
  rfl

/-- **`hgroupAddEquivSheafHAdditiveSheaf` is natural.** Let `φ` be an endomorphism of `𝒪_X`, `ψ'`
an endomorphism of the associated sheaf `𝒪_Xᵃ` which `smallEtaleSectionsUnitIso` intertwines with
`φ`, and `ψ` an endomorphism of `𝐆_a` which `uliftAssociatedUnitIsoAdditiveSheaf` intertwines with
the universe lift of `ψ'`. Then the comparison carries `Hⁿ⁺¹(X, φ)` to `Hⁿ⁺¹(X_étale, ψ)`. -/
theorem hgroupAddEquivSheafHAdditiveSheaf_naturality
    (φ : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf)
    (ψ' : smallEtaleAssociatedSheaf X (Scheme.unitModule X) ⟶
      smallEtaleAssociatedSheaf X (Scheme.unitModule X))
    (ψ : additiveSheaf.{u, v} X ⟶ additiveSheaf.{u, v} X)
    (h₁ : (SheafOfModules.toSheaf X.ringCatSheaf).map φ ≫
        (smallEtaleSectionsUnitIso X (Scheme.unitModule X)).hom =
      (smallEtaleSectionsUnitIso X (Scheme.unitModule X)).hom ≫
        (smallEtaleZariskiPushforward X).map ψ')
    (h₂ : (uliftSheafFunctor.{max (u + 1) v, u} X.smallEtaleTopology).map ψ' ≫
        (uliftAssociatedUnitIsoAdditiveSheaf.{v} X).hom =
      (uliftAssociatedUnitIsoAdditiveSheaf.{v} X).hom ≫ ψ)
    (n : ℕ) (x : Hgroup X.ringCatSheaf ⊤ (n + 1) (SheafOfModules.unit X.ringCatSheaf)) :
    hgroupAddEquivSheafHAdditiveSheaf.{w, v} X n ((Hfunctor X.ringCatSheaf ⊤ (n + 1)).map φ x) =
      Sheaf.H.map ψ (n + 1) (hgroupAddEquivSheafHAdditiveSheaf.{w, v} X n x) := by
  let : HasExt.{u} (Sheaf (Opens.grothendieckTopology (X : Type u)) AddCommGrpCat.{u}) :=
    Stacks.Topology.hasExt_sheafOpens.{u, u} X.toTopCat
  let : HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
    IsGrothendieckAbelian.hasExt.{u} _
  have e₁ : (hgroupIsoSmallEtaleGlobalCohomology X (Scheme.unitModule X) n).hom
        ((Hfunctor X.ringCatSheaf ⊤ (n + 1)).map φ x) =
      Sheaf.H.map ψ' (n + 1)
        ((hgroupIsoSmallEtaleGlobalCohomology X (Scheme.unitModule X) n).hom x) :=
    ConcreteCategory.congr_hom
      (hgroupIsoSmallEtaleGlobalCohomology_hom_naturality (F := Scheme.unitModule X)
        (G := Scheme.unitModule X) φ ψ' h₁ n) x
  rw [hgroupAddEquivSheafHAdditiveSheaf_apply, hgroupAddEquivSheafHAdditiveSheaf_apply]
  refine (congrArg (fun y ↦ Sheaf.H.map (uliftAssociatedUnitIsoAdditiveSheaf.{v} X).hom (n + 1)
    (Scheme.smallEtaleSheafHUliftAddEquiv.{u, w, v} X _ (n + 1) y)) e₁).trans ?_
  rw [Scheme.smallEtaleSheafHUliftAddEquiv_naturality, ← Sheaf.H.map_comp_apply, h₂,
    Sheaf.H.map_comp_apply]

/-- **Vanishing of the cohomology of the structure sheaf in a positive degree gives vanishing of
the étale cohomology of `𝐆_a` in that degree.** It is
`Stacks.ArtinSchreier.hgroupAddEquivSheafHAdditiveSheaf` read on vanishing. -/
theorem subsingleton_sheafH_additiveSheaf_of_isZero_hgroup_unconditional (i : ℕ) (hi : 0 < i)
    (h : IsZero (Hgroup X.ringCatSheaf ⊤ i (SheafOfModules.unit X.ringCatSheaf))) :
    Subsingleton (Sheaf.H.{w} (additiveSheaf.{u, v} X) i) := by
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  rw [AddCommGrpCat.isZero_iff_subsingleton] at h
  exact (hgroupAddEquivSheafHAdditiveSheaf.{w, v} X n).toEquiv.subsingleton_congr.mp h

end Stacks.ArtinSchreier

end
