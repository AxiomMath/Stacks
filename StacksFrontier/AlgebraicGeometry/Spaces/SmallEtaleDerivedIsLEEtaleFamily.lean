module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallBaseChangeLift
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedIsoLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackBoundedAbove
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackEtale

/-!
# Cohomological amplitude is local along a jointly surjective family of étale morphisms

Let `X` be an algebraic space and `(gᵢ : Zᵢ ⟶ X)` a family of étale morphisms of algebraic spaces
which is jointly surjective on points, for instance the étale scheme charts `X_U ⟶ X` lying over
an étale covering of the base by schemes. A module on `X` vanishes as soon as its pullbacks along
every `gᵢ` do, and an object `K` of `D(𝒪_X)` has no cohomology above degree `n` if and only if
every `Lgᵢ^*K` has none.

The proof reduces to the chart criterion
`AlgebraicGeometry.Space.isZero_of_isZero_modulePullback_chartToSpace`: a surjective étale chart
`Wᵢ` of each `Zᵢ`, pushed forward along `gᵢ`, is an étale chart of `X`, and these charts are
jointly surjective on points, so they cover the final object of the small étale site
(`AlgebraicGeometry.Space.coversTop_of_pointsCover`). For complexes, an étale derived pullback
commutes with the cohomology sheaves
(`AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackHomologyIsoOfIsEtale`); the converse
direction is right t-exactness of the derived pullback
(`AlgebraicGeometry.Space.isLE_smallEtaleDerivedModulePullback_obj_of_isLE`).

## Main results

* `AlgebraicGeometry.Space.isZero_of_isZero_modulePullback_of_isEtale`: vanishing of a module is
  detected on a jointly surjective family of étale morphisms.
* `AlgebraicGeometry.Space.isLE_iff_forall_isLE_smallEtaleDerivedModulePullback_of_isEtale`:
  `K ∈ D^{≤ n}` if and only if every `Lgᵢ^*K ∈ D^{≤ n}`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 5000] SheafOfModules.instAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Vanishing of a module is local along a jointly surjective family of étale morphisms.** A
module on `X` whose pullbacks along a family of étale morphisms `gᵢ : Zᵢ ⟶ X`, jointly surjective
on points, all vanish, is zero. -/
theorem isZero_of_isZero_modulePullback_of_isEtale {X : AlgebraicSpaces B S hS} {ι : Type*}
    {Z : ι → AlgebraicSpaces B S hS} (g : ∀ i, Z i ⟶ X) (hg : ∀ i, IsEtale B S hS (g i).hom)
    (hsurj : ∀ x : points B S hS X.1, ∃ i, x ∈ Set.range (pointsMap B S hS (Z i).1 (g i).hom))
    (M : Modules.{u, u} B S hS X.1 X.2)
    (h : ∀ i, IsZero ((modulePullback B S hS (g i)).obj M)) : IsZero M := by
  choose W hW using fun i => exists_surjective_smallEtale_chart B S hS (Z i).1 (Z i).2
  let V : ι → SmallEtale B S hS X.1 := fun i =>
    (smallEtalePostcomp B S hS (g i) (hg i)).obj (W i)
  have hV : PointsCover V := by
    intro x
    obtain ⟨i, z, rfl⟩ := hsurj x
    obtain ⟨w, rfl⟩ := hW i z
    exact ⟨i, w, pointsMap_comp_apply B S hS (W i).1.hom (g i).hom w⟩
  refine isZero_of_isZero_modulePullback_chartToSpace B S hS (coversTop_of_pointsCover hV) M
    fun i => ?_
  have hc : chartToSpace B S hS X (V i) = chartToSpace B S hS (Z i) (W i) ≫ g i :=
    ObjectProperty.hom_ext _ rfl
  rw [hc]
  exact (Functor.map_isZero (modulePullback B S hS (chartToSpace B S hS (Z i) (W i))) (h i)).of_iso
    ((modulePullbackCompIso B S hS (chartToSpace B S hS (Z i) (W i)) (g i)).app M).symm

/-- **Cohomological amplitude in `D(𝒪_X)` is local along a jointly surjective family of étale
morphisms.** If `gᵢ : Zᵢ ⟶ X` are étale morphisms of algebraic spaces, jointly surjective on
points, and every `Lgᵢ^*K` has no cohomology above degree `n`, then neither has `K`. -/
theorem isLE_of_isLE_smallEtaleDerivedModulePullback_of_isEtale {X : AlgebraicSpaces B S hS}
    {ι : Type*} {Z : ι → AlgebraicSpaces B S hS} (g : ∀ i, Z i ⟶ X)
    (hg : ∀ i, IsEtale B S hS (g i).hom)
    (hsurj : ∀ x : points B S hS X.1, ∃ i, x ∈ Set.range (pointsMap B S hS (Z i).1 (g i).hom))
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) (n : ℤ)
    (h : ∀ i, ((smallEtaleDerivedModulePullback B S hS (g i)).obj K).IsLE n) :
    K.IsLE n := by
  rw [DerivedCategory.isLE_iff]
  intro m hm
  refine isZero_of_isZero_modulePullback_of_isEtale g hg hsurj _ fun i => ?_
  exact ((DerivedCategory.isLE_iff _ n).1 (h i) m hm).of_iso
    (smallEtaleDerivedModulePullbackHomologyIsoOfIsEtale (g i) (hg i) K m).symm

/-- **`K ∈ D^{≤ n}` can be checked along a jointly surjective family of étale morphisms.** For
étale morphisms of algebraic spaces `gᵢ : Zᵢ ⟶ X`, jointly surjective on points, `K` has no
cohomology above degree `n` if and only if no `Lgᵢ^*K` has. -/
theorem isLE_iff_forall_isLE_smallEtaleDerivedModulePullback_of_isEtale
    {X : AlgebraicSpaces B S hS} {ι : Type*} {Z : ι → AlgebraicSpaces B S hS}
    (g : ∀ i, Z i ⟶ X) (hg : ∀ i, IsEtale B S hS (g i).hom)
    (hsurj : ∀ x : points B S hS X.1, ∃ i, x ∈ Set.range (pointsMap B S hS (Z i).1 (g i).hom))
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) (n : ℤ) :
    K.IsLE n ↔ ∀ i, ((smallEtaleDerivedModulePullback B S hS (g i)).obj K).IsLE n :=
  ⟨fun hK i => by
    have := hK
    exact isLE_smallEtaleDerivedModulePullback_obj_of_isLE (g i) K n,
    isLE_of_isLE_smallEtaleDerivedModulePullback_of_isEtale g hg hsurj K n⟩

end AlgebraicGeometry.Space

end
