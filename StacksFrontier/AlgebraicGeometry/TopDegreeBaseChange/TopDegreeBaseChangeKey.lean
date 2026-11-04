module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TopDegreeTensorNaturality
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TopDegreeBaseChangeTranspose

/-!
# The transpose of the top-degree base change map

For a morphism of ringed spaces `h : Y ⟶ Y'` and a complex `Z` whose derived pushforward lives
in degrees `≤ d`, we construct the comparison `H^d(Rh_* Z) ⟶ h_* H^d(Z)` and compute transposes
under `h^* ⊣ h_*` of maps out of `h^* H^d(K)`. For a commutative square of ringed spaces we
construct the Leray comparison of iterated derived pushforwards and use it to compute the
transpose of the top-degree base change map.

## Main definitions

* `topDegreePushforwardMap`: The comparison `H^d(Rh_* Z) ⟶ h_* H^d(Z)`.
* `lerayComparison`: The isomorphism `Rf'_* Rh'_* ⟶ Rh_* Rf''_*` of a commutative square.

## Main results

* `homEquiv_pullbackTopDegreeIso_comp`: The transpose of a map out of a derived pullback, in
  top degree.
* `derivedAdjunction_homEquiv_derivedBaseChangeMap_comp`: The transpose of the derived base
  change map, through the Leray comparison.
* `homEquiv_topDegreeBaseChange`: The transpose of the top-degree base change map.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedBaseChange
open DerivedCategory RingedSpaceModuleAdjunction

universe u

noncomputable section

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance 10000] HasDerivedCategory.standard

section Transpose

variable {Y Y' : RingedSpace.{u, u}} (h : Y ⟶ Y') (d : ℤ)

/-- `f^* H^d(K) ≅ H^d(Lf^* K)` for `K` living in degrees `≤ d`. -/
abbrev pullbackTopDegreeIso (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y')))
    (hK : TStructure.t.IsLE K d) :
    (modulePullback h).obj ((homologyFunctor _ d).obj K) ≅
      (homologyFunctor _ d).obj ((derivedPullback h).obj K) :=
  (derivedPullbackTopDegreeIsoPullback h K d hK).symm

/-- The isomorphism `pullbackTopDegreeIso` is natural in `K`. -/
theorem pullbackTopDegreeIso_hom_naturality
    {K K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y'))} (α : K ⟶ K')
    (hK : TStructure.t.IsLE K d) (hK' : TStructure.t.IsLE K' d) :
    (modulePullback h).map ((homologyFunctor _ d).map α) ≫ (pullbackTopDegreeIso h d K' hK').hom =
      (pullbackTopDegreeIso h d K hK).hom ≫
        (homologyFunctor _ d).map ((derivedPullback h).map α) := by
  have := derivedPullbackTopDegreeIsoPullback_hom_naturality h α d hK hK'
  simp only [pullbackTopDegreeIso, Iso.symm_hom]
  rw [Iso.comp_inv_eq, Category.assoc, this, Iso.inv_hom_id_assoc]

/-- **The comparison `H^d(Rh_* Z) ⟶ h_* H^d(Z)`**, the transpose under `h^* ⊣ h_*` of the top
cohomology of the derived counit, read through `pullbackTopDegreeIso`. -/
def topDegreePushforwardMap (Z : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
    (hZ : TStructure.t.IsLE ((derivedPushforward h).obj Z) d) :
    (homologyFunctor _ d).obj ((derivedPushforward h).obj Z) ⟶
      (modulePushforward h).obj ((homologyFunctor _ d).obj Z) :=
  (modulePullbackPushforwardAdjunction h).homEquiv _ _
    ((pullbackTopDegreeIso h d _ hZ).hom ≫
      (homologyFunctor _ d).map ((derivedAdjunction h).counit.app Z))

/-- **The transpose of a map out of a derived pullback, in top degree.** -/
theorem homEquiv_pullbackTopDegreeIso_comp
    {K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y'))}
    {Z : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))}
    (φ : (derivedPullback h).obj K ⟶ Z) (hK : TStructure.t.IsLE K d)
    (hZ : TStructure.t.IsLE ((derivedPushforward h).obj Z) d) :
    (modulePullbackPushforwardAdjunction h).homEquiv _ _
        ((pullbackTopDegreeIso h d K hK).hom ≫ (homologyFunctor _ d).map φ) =
      (homologyFunctor _ d).map ((derivedAdjunction h).homEquiv _ _ φ) ≫
        topDegreePushforwardMap h d Z hZ := by
  rw [topDegreePushforwardMap, ← Adjunction.homEquiv_naturality_left, ← Category.assoc,
    pullbackTopDegreeIso_hom_naturality h d _ hK hZ, Category.assoc, ← Functor.map_comp]
  congr 3
  rw [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc,
    (derivedAdjunction h).counit_naturality, ← Category.assoc,
    (derivedAdjunction h).left_triangle_components, Category.id_comp]

/-- `topDegreePushforwardMap` is natural. -/
theorem topDegreePushforwardMap_naturality
    {Z Z' : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))} (ψ : Z ⟶ Z')
    (hZ : TStructure.t.IsLE ((derivedPushforward h).obj Z) d)
    (hZ' : TStructure.t.IsLE ((derivedPushforward h).obj Z') d) :
    (homologyFunctor _ d).map ((derivedPushforward h).map ψ) ≫ topDegreePushforwardMap h d Z' hZ' =
      topDegreePushforwardMap h d Z hZ ≫
        (modulePushforward h).map ((homologyFunctor _ d).map ψ) := by
  rw [topDegreePushforwardMap, topDegreePushforwardMap, ← Adjunction.homEquiv_naturality_left,
    ← Adjunction.homEquiv_naturality_right]
  congr 1
  rw [← Category.assoc, pullbackTopDegreeIso_hom_naturality h d _ hZ hZ', Category.assoc,
    Category.assoc, ← Functor.map_comp, ← Functor.map_comp, (derivedAdjunction h).counit_naturality]

end Transpose

section Key

/-- For an adjunction `L ⊣ R`, if the transpose of `bc` factors as `u ≫ ℓ`, and
`w ≫ ℓ' = ℓ ≫ R.map χ`, then the transpose of `bc ≫ χ` is `(u ≫ w) ≫ ℓ'`. -/
theorem homEquiv_comp_of_eq {A B : Type*} [Category A] [Category B] {L : A ⥤ B} {R : B ⥤ A}
    (adj : L ⊣ R) {a m m' : A} {b b' : B} (bc : L.obj a ⟶ b) (χ : b ⟶ b') (u : a ⟶ m)
    (ℓ : m ⟶ R.obj b) (ℓ' : m' ⟶ R.obj b') (w : m ⟶ m') (v : a ⟶ m')
    (hb : adj.homEquiv _ _ bc = u ≫ ℓ) (hn : w ≫ ℓ' = ℓ ≫ R.map χ) (hv : v = u ≫ w) :
    adj.homEquiv _ _ (bc ≫ χ) = v ≫ ℓ' := by
  rw [Adjunction.homEquiv_naturality_right, hb, Category.assoc, ← hn, hv, Category.assoc]

/-- For equal morphisms `q₁ = q₂`, the derived pushforwards along `q₁` and `q₂` of a map `ψ`
agree up to the transport isomorphisms `eqToHom`. -/
theorem derivedPushforward_map_eqToHom {X Y : RingedSpace.{u, u}} {q₁ q₂ : X ⟶ Y} (e : q₁ = q₂)
    {N N' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))} (ψ : N ⟶ N')
    (e₁ : (derivedPushforward q₁).obj N = (derivedPushforward q₂).obj N)
    (e₂ : (derivedPushforward q₁).obj N' = (derivedPushforward q₂).obj N') :
    eqToHom e₁ ≫ (derivedPushforward q₂).map ψ = (derivedPushforward q₁).map ψ ≫ eqToHom e₂ := by
  subst e; simp

variable {X'' X' Y'' Y' : RingedSpace.{u, u}} (h' : X'' ⟶ X') (f'' : X'' ⟶ Y'')
  (f' : X' ⟶ Y') (h : Y'' ⟶ Y') (sq : h' ≫ f' = f'' ≫ h)

/-- The transport `pushforwardCompTransport` of a commutative square is an isomorphism. -/
instance (N : DerivedCategory (SheafOfModules.{u} (structureSheafRing X''))) :
    IsIso (pushforwardCompTransport h' f'' f' h sq N) := by
  unfold pushforwardCompTransport; infer_instance

include sq in
/-- **The Leray comparison** `Rf'_* Rh'_* ⟶ Rh_* Rf''_*` of a commutative square, assembled
from the two composition isomorphisms. -/
def lerayComparison (N : DerivedCategory (SheafOfModules.{u} (structureSheafRing X''))) :
    (derivedPushforward f').obj ((derivedPushforward h').obj N) ⟶
      (derivedPushforward h).obj ((derivedPushforward f'').obj N) :=
  (derivedPushforwardCompIso h' f').hom.app N ≫
    inv (pushforwardCompTransport h' f'' f' h sq N)

/-- The Leray comparison `lerayComparison` is an isomorphism. -/
instance (N : DerivedCategory (SheafOfModules.{u} (structureSheafRing X''))) :
    IsIso (lerayComparison h' f'' f' h sq N) := by
  unfold lerayComparison; infer_instance

/-- The Leray comparison `lerayComparison` is natural in `N`. -/
theorem lerayComparison_naturality
    {N N' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X''))} (ψ : N ⟶ N') :
    (derivedPushforward f').map ((derivedPushforward h').map ψ) ≫
        lerayComparison h' f'' f' h sq N' =
      lerayComparison h' f'' f' h sq N ≫
        (derivedPushforward h).map ((derivedPushforward f'').map ψ) := by
  have h1 := (derivedPushforwardCompIso h' f').hom.naturality ψ
  have h2 := (derivedPushforwardCompIso f'' h).hom.naturality ψ
  simp only [Functor.comp_map] at h1 h2
  rw [lerayComparison, lerayComparison, reassoc_of% h1, Category.assoc]
  congr 1
  rw [IsIso.eq_inv_comp, ← Category.assoc, IsIso.comp_inv_eq]
  simp only [pushforwardCompTransport, Category.assoc]
  rw [reassoc_of% h2]
  congr 1
  exact derivedPushforward_map_eqToHom sq.symm ψ _ _

/-- **The transpose of the derived base change map, through the Leray comparison.** -/
theorem derivedAdjunction_homEquiv_derivedBaseChangeMap_comp
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X')))
    {N' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X''))}
    (ψ : (derivedPullback h').obj K ⟶ N') :
    (derivedAdjunction h).homEquiv _ _
        (derivedBaseChangeMap h' f'' f' h sq K ≫ (derivedPushforward f'').map ψ) =
      (derivedPushforward f').map ((derivedAdjunction h').unit.app K ≫
          (derivedPushforward h').map ψ) ≫ lerayComparison h' f'' f' h sq N' := by
  have T2 := derivedAdjunction_homEquiv_derivedBaseChangeMap h' f'' f' h sq K
  have hb : (derivedAdjunction h).homEquiv _ _ (derivedBaseChangeMap h' f'' f' h sq K) =
      (derivedPushforward f').map ((derivedAdjunction h').unit.app K) ≫
        lerayComparison h' f'' f' h sq ((derivedPullback h').obj K) := by
    unfold lerayComparison
    refine (Category.comp_id _).symm.trans ?_
    rw [← IsIso.hom_inv_id (pushforwardCompTransport h' f'' f' h sq ((derivedPullback h').obj K)),
      ← Category.assoc, T2, Category.assoc]
  exact homEquiv_comp_of_eq (derivedAdjunction h) _ _ _ _ _ _ _ hb
    (lerayComparison_naturality h' f'' f' h sq ψ) (Functor.map_comp _ _ _)

/-- **The transpose of the top-degree base change map.** -/
theorem homEquiv_topDegreeBaseChange (d : ℤ)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X')))
    {N' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X''))}
    (ψ : (derivedPullback h').obj K ⟶ N')
    (hA : TStructure.t.IsLE ((derivedPushforward f').obj K) d)
    (hZ : TStructure.t.IsLE ((derivedPushforward h).obj ((derivedPushforward f'').obj N')) d) :
    (modulePullbackPushforwardAdjunction h).homEquiv _ _
        ((pullbackTopDegreeIso h d _ hA).hom ≫ (homologyFunctor _ d).map
          (derivedBaseChangeMap h' f'' f' h sq K ≫ (derivedPushforward f'').map ψ)) =
      (homologyFunctor _ d).map ((derivedPushforward f').map
          ((derivedAdjunction h').unit.app K ≫ (derivedPushforward h').map ψ)) ≫
        (homologyFunctor _ d).map (lerayComparison h' f'' f' h sq N') ≫
        topDegreePushforwardMap h d _ hZ := by
  rw [homEquiv_pullbackTopDegreeIso_comp h d _ hA hZ,
    derivedAdjunction_homEquiv_derivedBaseChangeMap_comp, Functor.map_comp, Category.assoc]

end Key

end Stacks.AlgebraicGeometry.TopDegreeBaseChange
