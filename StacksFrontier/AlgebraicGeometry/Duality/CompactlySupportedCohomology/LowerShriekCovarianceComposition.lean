module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.LowerShriekCompositionPoints
public import StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.LowerShriekCovarianceAgreement
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.OpenImmersionPrecomposition

/-!
# The first construction of the covariance map for an open, and its agreement with the third

In Situation [Stacks, Tag 0F42] let `f : X ⟶ Y` be a morphism of `FTS_S`, `i : U ⟶ X` an open
immersion and `g = f ∘ i`. The first construction of [Stacks, Tag 0G56] of the canonical map
`Rg_!(K|_U) ⟶ Rf_! K` is `Rf_!` applied to the map `Ri_!(K|_U) ⟶ K` of [Stacks, Tag 0G4Y] (for
`U ⊆ X ⊆ X`), through `Rg_! = Rf_! ∘ Ri_!` ([Stacks, Tag 0G55]). Here `Ri_!` is computed at the
compactification `X` of `U` over `X`, and the map `Ri_!(K|_U) ⟶ K` is the one which, under
`Hom(Ri_!(K|_U), L) = Hom_U(K|_U, i^! L) = Hom_U(K|_U, L|_U)` ([Stacks, Tag 0G51] and
`i^! = i^*`, [Stacks, Tag 0AU0]), is restriction `Hom_X(K, L) ⟶ Hom_U(K|_U, L|_U)`.

## Main definitions

* `CategoryTheory.ProSeq.mapConstEquiv`: morphisms into a constant pro-object, before and after a
  fully faithful functor.
* `Stacks.Duality.UpperShriekDuality.upperShriekStdOpenIso`: `i^! = Li^*` at the standard model.
* `AlgebraicGeometry.lowerShriekOpenImmersionCounit`: the map `Ri_!(K|_U) ⟶ K` of
  [Stacks, Tag 0G4Y].
* `AlgebraicGeometry.lowerShriekOpenImmersionMapOfComposition`: **[Stacks, Tag 0G56]**,
  construction (1).

## Main results

* `UpperShriekDuality.upperShriekStdOpenIso_hom_app_comp_upperShriekStdCompIso_hom_app`:
  `(f ∘ i)^! = i^! ∘ f^!` ([Stacks, Tag 0ATX]) and `i^! = Li^*` give `(f ∘ i)^! = Li^* ∘ f^!`.
* `AlgebraicGeometry.lowerShriekOpenImmersionMapOfComposition_eq_lowerShriekOpenImmersionMap`:
  **[Stacks, Tag 0G56]**, constructions (1) and (3) agree.
* `lowerShriekOpenImmersionMapOfComposition_eq_lowerShriekOpenImmersionMapOfCompactification`:
  **[Stacks, Tag 0G56]**, constructions (1) and (2) agree.

## References

* [Stacks Project, Tag 0G56](https://stacks.math.columbia.edu/tag/0G56)
* [Stacks Project, Tag 0G55](https://stacks.math.columbia.edu/tag/0G55)
* [Stacks Project, Tag 0G4Y](https://stacks.math.columbia.edu/tag/0G4Y)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] CategoryTheory.uliftCategory

universe v u

namespace CategoryTheory.ProSeq

attribute [local instance 10000] CategoryTheory.Functor.hasLeftKanExtension_of_type
  CategoryTheory.Functor.hasPointwiseLeftKanExtension_of_type

variable {𝒟 : Type v} [Category.{v} 𝒟] {𝒟' : Type v} [Category.{v} 𝒟'] (ι : 𝒟 ⥤ 𝒟') [ι.Full]
  [ι.Faithful]

/-- For `ι` fully faithful, morphisms `P ⟶ L` into a constant pro-object are the morphisms
`ι P ⟶ ι L`: the left Kan extension along `ι` restricts back to the functor extended. -/
def mapConstEquiv (P : ProSeq 𝒟) (L : 𝒟) :
    (P ⟶ const.obj L) ≃ ((map ι).obj P ⟶ const.obj (ι.obj L)) :=
  have := Functor.hasPointwiseLeftKanExtension_of_type ι P.points
  (homConstEquiv P L).trans ((@asIso _ _ _ _ ((ι.lanUnit.app P.points).app L)
    (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit ι P.points
      (ι.obj L)).isIso_hom_app).toEquiv.trans (homConstEquiv ((map ι).obj P) (ι.obj L)).symm)

/-- `mapConstEquiv ι P L` sends `φ : P ⟶ const.obj L` to its image `mapConst ι φ` under `map ι`. -/
theorem mapConstEquiv_apply (P : ProSeq 𝒟) (L : 𝒟) (φ : P ⟶ const.obj L) :
    mapConstEquiv ι P L φ = mapConst ι φ :=
  rfl

end CategoryTheory.ProSeq

namespace Stacks.Duality.UpperShriekDuality

open TwistedInverseImageDuality

/-- Three commutative squares pasted horizontally. -/
theorem natural_chase_three {𝒞 : Type*} [Category 𝒞] {A A' B B' D D' F F' : 𝒞} (g₀ : A ⟶ A')
    (u : A ⟶ B) (u' : A' ⟶ B') (gb : B ⟶ B') (p : B ⟶ D) (p' : B' ⟶ D') (gd : D ⟶ D')
    (q : D ⟶ F) (q' : D' ⟶ F') (gf : F ⟶ F') (h₁ : g₀ ≫ u' = u ≫ gb) (h₂ : gb ≫ p' = p ≫ gd)
    (h₃ : gd ≫ q' = q ≫ gf) : g₀ ≫ u' ≫ p' ≫ q' = (u ≫ p ≫ q) ≫ gf := by
  rw [reassoc_of% h₁, reassoc_of% h₂, h₃, Category.assoc, Category.assoc]

variable {S : Scheme.{u}} [IsNoetherian S] {U X : FTS S} (i : U ⟶ X) [IsOpenImmersion i.left]

/-- **`i^! = Li^*` for an open immersion `i`** ([Stacks, Tag 0AU0]), at the compactification of
`i` by its target, at the standard model on `D^+_{Coh}`. -/
def upperShriekStdOpenIso :
    (plusCoh X.left).ι ⋙ pull i.left ≅ upperShriekStd i (openCompactification i) :=
  NatIso.ofComponents (fun N =>
      (pull i.left).mapIso ((comparison X.left).unitIso.app N.obj) ≪≫
        (pullModelConj i.left).symm.app ((comparison X.left).functor.obj N.obj) ≪≫
        (comparison U.left).inverse.mapIso
          ((ObjectProperty.ι _).mapIso
            ((upperShriekOpenIso i).symm.app ((plusCohToQCoh X.left).obj N))))
    (fun {N N'} g => by
      have h₁ := (comparison X.left).unitIso.hom.naturality g.hom
      have h₂ := (pullModelConj i.left).inv.naturality ((comparison X.left).functor.map g.hom)
      have h₃ := congrArg (fun t => (comparison U.left).inverse.map t.hom)
        ((upperShriekOpenIso i).inv.naturality ((plusCohToQCoh X.left).map g))
      dsimp only [Functor.comp_map, Functor.id_map] at h₁ h₂
      simp only [ObjectProperty.FullSubcategory.comp_hom, Functor.map_comp] at h₃
      exact natural_chase_three _ _ _ _ _ _ _ _ _ _
        (((pull i.left).map_comp _ _).symm.trans (((pull i.left).congr_map h₁).trans
          ((pull i.left).map_comp _ _))) h₂ h₃)

/-- The component of `upperShriekStdOpenIso i` at `N` is the image under `pull i.left` of the unit
of `comparison X.left`, followed by the inverse of `pullModelConj i.left` and the image under the
inverse of `comparison U.left` of the inverse of `upperShriekOpenIso i`. -/
theorem upperShriekStdOpenIso_hom_app (N : (plusCoh X.left).FullSubcategory) :
    (upperShriekStdOpenIso i).hom.app N =
      (pull i.left).map ((comparison X.left).unitIso.hom.app N.obj) ≫
        (pullModelConj i.left).inv.app ((comparison X.left).functor.obj N.obj) ≫
        (comparison U.left).inverse.map
          ((upperShriekOpenIso i).inv.app ((plusCohToQCoh X.left).obj N)).hom :=
  rfl

/-- Inverting a composite of isomorphisms, with the inverses given as morphisms. -/
theorem inv_comp_inv_of_comp_eq {𝒞 : Type*} [Category 𝒞] {x y z : 𝒞} (a : x ⟶ y) (a' : y ⟶ x)
    (b : y ⟶ z) (b' : z ⟶ y) (c : x ⟶ z) (c' : z ⟶ x) (ha : a ≫ a' = 𝟙 _) (hb : b ≫ b' = 𝟙 _)
    (hc : c' ≫ c = 𝟙 _) (H : a ≫ b = c) : b' ≫ a' = c' := by
  subst H
  rw [← Category.id_comp (b' ≫ a'), ← hc, Category.assoc, Category.assoc, reassoc_of% hb, ha,
    Category.comp_id]

/-- Two composites `P₀ ⟶ P₅` agree, given a commutative square `a₃ ≫ a₄ = d₁ ≫ c₁`, the relation
`a₂ ≫ d₁ = e ≫ b₁` for a right inverse `e` of `a₁`, `c₁ ≫ a₅ = b₂` and `b₃ = 𝟙`. -/
theorem openComp_chase {𝒞 : Type*} [Category 𝒞] {P₀ P₁ P₂ P₃ P₄ P₅ Q₁ : 𝒞}
    (a₁ : P₀ ⟶ P₁) (a₂ : P₁ ⟶ P₂) (a₃ : P₂ ⟶ P₃) (a₄ : P₃ ⟶ P₄) (a₅ : P₄ ⟶ P₅) (b₁ : P₀ ⟶ Q₁)
    (b₂ : Q₁ ⟶ P₅) (b₃ : P₅ ⟶ P₅) (d₁ : P₂ ⟶ Q₁) (c₁ : Q₁ ⟶ P₄) (e : P₁ ⟶ P₀)
    (F₁ : a₃ ≫ a₄ = d₁ ≫ c₁) (F₂ : a₂ ≫ d₁ = e ≫ b₁) (F₃ : a₁ ≫ e = 𝟙 _)
    (F₄ : c₁ ≫ a₅ = b₂) (F₅ : b₃ = 𝟙 _) :
    (a₁ ≫ a₂ ≫ a₃) ≫ a₄ ≫ a₅ = b₁ ≫ b₂ ≫ b₃ := by
  subst F₄ F₅
  rw [Category.comp_id, Category.assoc, Category.assoc, reassoc_of% F₁, reassoc_of% F₂,
    reassoc_of% F₃]

variable {Y : FTS S} (f : X ⟶ Y) (c : CompactificationOf (Over.mk f.left))

/-- **`i^! = Li^*` turns `(f ∘ i)^! = i^! ∘ f^!` into `(f ∘ i)^! = Li^* ∘ f^!`** at the standard
model on `D^+_{Coh}`: [Stacks, Tag 0ATX] at the compactification of `i` by its target and the
compactification of `f ∘ i` restricted from one of `f`, followed by `i^! = Li^*`
([Stacks, Tag 0AU0]), is the identification `g^! = i^* ∘ f^!` of the construction of upper shriek
functors. -/
theorem upperShriekStdOpenIso_hom_app_comp_upperShriekStdCompIso_hom_app
    (L : (plusCoh Y.left).FullSubcategory) :
    (upperShriekStdOpenIso i).hom.app ((upperShriekStdPlusCoh f c).obj L) ≫
        (upperShriekStdCompIso i f (openCompactification i) c (c.precompOpen i.left)).hom.app L =
      (upperShriekStdPrecompOpenIso i f c (c.precompOpen i.left)).hom.app L := by
  have hC :
      (upperShriekStdCompIso i f (openCompactification i) c (c.precompOpen i.left)).hom.app L =
      (comparison U.left).inverse.map ((upperShriek i (openCompactification i)).map
        ((upperShriekStdPlusCohCompIso f c).hom.app L)).hom ≫
      (comparison U.left).inverse.map ((upperShriekCompIso i f (openCompactification i) c
        (c.precompOpen i.left)).inv.app ((plusCohToQCohPlus Y.left).obj L)).hom.hom := by
    simp only [upperShriekStdCompIso, upperShriekCompStdIso, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, Functor.associator_inv_app,
      Iso.symm_hom, Category.id_comp, Functor.comp_map]
    exact congrArg (_ ≫ ·) (Category.id_comp _)
  have hP :
      (upperShriekStdPrecompOpenIso i f c (c.precompOpen i.left)).hom.app L =
      (pullModelConj i.left).inv.app ((upperShriek f c).obj ((plusCohToQCoh Y.left).obj L)).obj ≫
      (comparison U.left).inverse.map ((upperShriekPrecompOpenIso i f c).inv.app
        ((plusCohToQCoh Y.left).obj L)).hom ≫
      (upperShriekStdCompactificationIso (i ≫ f) (c.precompOpen i.left)
        (c.precompOpen i.left)).hom.app L := by
    simp [upperShriekStdPrecompOpenIso, upperShriekStdPullIso]
    rfl
  rw [upperShriekStdOpenIso_hom_app, hC, hP]
  set ε := (upperShriekStdPlusCohCompIso f c).hom.app L
  have F₁ := congrArg (fun t => (comparison U.left).inverse.map t.hom)
    ((upperShriekOpenIso i).inv.naturality ε)
  simp only [ObjectProperty.FullSubcategory.comp_hom, Functor.map_comp] at F₁
  have F₂ := (pullModelConj i.left).inv.naturality ε.hom
  simp only [Functor.comp_map] at F₂
  have F₃ : (pull i.left).map ((comparison X.left).unitIso.hom.app
        ((upperShriekStdPlusCoh f c).obj L).obj) ≫
        (pull i.left).map ((comparison X.left).inverse.map ε.hom) = 𝟙 _ :=
    ((pull i.left).map_comp _ _).symm.trans
      ((congrArg (pull i.left).map ((comparison X.left).unit_inverse_comp _)).trans
        ((pull i.left).map_id _))
  have H : ((upperShriekCompIso i f (openCompactification i) c (c.precompOpen i.left)).hom.app
        ((plusCohToQCohPlus Y.left).obj L)).hom ≫
      (upperShriekOpenIso i).hom.app ((upperShriek f c).obj ((plusCohToQCoh Y.left).obj L)) =
      (upperShriekPrecompOpenIso i f c).hom.app ((plusCohToQCoh Y.left).obj L) :=
    upperShriekCompIso_precompOpen_hom_app i f c ((plusCohToQCohPlus Y.left).obj L)
  have H' : (upperShriekOpenIso i).inv.app
        ((upperShriek f c).obj ((plusCohToQCoh Y.left).obj L)) ≫
      ((upperShriekCompIso i f (openCompactification i) c (c.precompOpen i.left)).inv.app
        ((plusCohToQCohPlus Y.left).obj L)).hom =
      (upperShriekPrecompOpenIso i f c).inv.app ((plusCohToQCoh Y.left).obj L) := by
    refine inv_comp_inv_of_comp_eq _ _ _ _ _ _ ?_ (Iso.hom_inv_id_app _ _)
      (Iso.inv_hom_id_app _ _) H
    exact congrArg InducedCategory.Hom.hom ((upperShriekCompIso i f (openCompactification i) c
      (c.precompOpen i.left)).hom_inv_id_app ((plusCohToQCohPlus Y.left).obj L))
  have F₄ : (comparison U.left).inverse.map ((upperShriekOpenIso i).inv.app
        ((upperShriek f c).obj ((plusCohToQCoh Y.left).obj L))).hom ≫
      (comparison U.left).inverse.map ((upperShriekCompIso i f (openCompactification i) c
        (c.precompOpen i.left)).inv.app ((plusCohToQCohPlus Y.left).obj L)).hom.hom =
      (comparison U.left).inverse.map ((upperShriekPrecompOpenIso i f c).inv.app
        ((plusCohToQCoh Y.left).obj L)).hom :=
    ((comparison U.left).inverse.map_comp _ _).symm.trans
      (congrArg (fun t => (comparison U.left).inverse.map t.hom) H')
  exact openComp_chase _ _ _ _ _ _ _ _ _ _ _ F₁.symm F₂.symm F₃ F₄
    (upperShriekStdCompactificationIso_self_hom_app (i ≫ f) (c.precompOpen i.left) L)

end Stacks.Duality.UpperShriekDuality

namespace CategoryTheory

/-- For isomorphisms `A : P ≅ Q`, `C : Q ≅ R`, `D : S ≅ R` of functors to types, `A` after the
inverse of `A ≪≫ C ≪≫ D⁻¹` is `D` followed by the inverse of `C`, on elements. -/
theorem Iso.trans_trans_symm_inv_comp_hom {𝒟 : Type*} [Category 𝒟] {P P' Q R S' : 𝒟}
    (A₁ : P ≅ P') (A₂ : P' ≅ Q) (C : Q ≅ R) (D : S' ≅ R) :
    ((A₁ ≪≫ A₂ ≪≫ C) ≪≫ D.symm).inv ≫ (A₁ ≪≫ A₂).hom = D.hom ≫ C.inv := by
  simp

/-- The inverse of the identification `Hom(A, F -) ≅ Hom(A, Q (P -))` induced by `e : P ⋙ Q ≅ F`,
restricted along `ι`, is composition with `e`. -/
theorem isoWhiskerLeft_isoWhiskerRight_coyoneda_inv_app {𝒟 : Type*} [Category 𝒟] {𝒞p : Type*}
    [Category 𝒞p] {ℬ : Type*} [Category ℬ] {𝒜s : Type*} [Category.{v} 𝒜s] (ι : 𝒟 ⥤ 𝒞p)
    (P : 𝒞p ⥤ ℬ) (Q : ℬ ⥤ 𝒜s) (F : 𝒞p ⥤ 𝒜s) (e : P ⋙ Q ≅ F) (A : 𝒜s) (L : 𝒟)
    (z : A ⟶ Q.obj (P.obj (ι.obj L))) :
    (Functor.isoWhiskerLeft ι (Functor.isoWhiskerRight e.symm (coyoneda.obj (op A)) ≪≫
      Functor.associator P Q (coyoneda.obj (op A)))).inv.app L z = z ≫ e.hom.app (ι.obj L) :=
  rfl

end CategoryTheory

namespace AlgebraicGeometry

open Stacks.Duality Stacks.Duality.TwistedInverseImageDuality Stacks.Duality.UpperShriekDuality

attribute [local instance 10000] CategoryTheory.Functor.hasLeftKanExtension_of_type
  CategoryTheory.Functor.hasPointwiseLeftKanExtension_of_type
attribute [local instance] Stacks.Cohomology.ProjectionFormulaPerfect.hasSheafifyOpens
  Stacks.Cohomology.ProjectionFormulaPerfect.wEqualsLocallyBijectiveOpens
attribute [local instance] Stacks.AssociatedSheaf.abelianModulesRingSheaf

variable {S : Scheme.{u}} [IsNoetherian S] {U X Y : FTS S}

/-- **The map `Ri_!(K|_U) ⟶ K` of [Stacks, Tag 0G4Y]** for an open immersion `i : U ⟶ X` (the
opens `U ⊆ X ⊆ X`, with `R(id)_! K = K`), `Ri_!` computed at the compactification `X` of `U`
over `X`: the morphism which, under
`Hom(Ri_!(K|_U), L) = Hom_U(K|_U, i^! L) = Hom_U(K|_U, L|_U)` ([Stacks, Tag 0G51] for `i` and
`i^! = Li^*`, [Stacks, Tag 0AU0]), corresponds to the identity of `K|_U`; composing with it is
the restriction map `Hom_X(K, L) ⟶ Hom_U(K|_U, L|_U)` of the display of [Stacks, Tag 0G4Y]
(`AlgebraicGeometry.lowerShriekHomEquiv_mapConst_lowerShriekOpenImmersionCounit`), and by
[Stacks, Tag 0G2X] it is the only such morphism. -/
def lowerShriekOpenImmersionCounit (i : U ⟶ X) [IsOpenImmersion i.left]
    (K : BoundedCoherentDerived X.left) :
    (lowerShriek i (Stacks.Duality.openCompactification i)).obj
        ((restrictBoundedCoherentLift i.left).obj K) ⟶ ProSeq.const.obj K :=
  (ProSeq.mapConstEquiv (boundedCoherentToPlusCoh X.left) _ K).symm
    ((lowerShriekHomEquiv i (Stacks.Duality.openCompactification i) _
      ((boundedCoherentToPlusCoh X.left).obj K)).symm
      ((restrictBoundedCoherentPullIso i).inv.app K ≫
        (upperShriekStdOpenIso i).hom.app ((boundedCoherentToPlusCoh X.left).obj K)))

/-- **The display of [Stacks, Tag 0G4Y] for `U ⊆ X ⊆ X`**: under the bijection of
[Stacks, Tag 0G51] for `i` and `i^! = Li^*` ([Stacks, Tag 0AU0]), composing a morphism
`ψ : K ⟶ N` with the map `Ri_!(K|_U) ⟶ K` is the restriction `ψ|_U : K|_U ⟶ N|_U`. -/
theorem lowerShriekHomEquiv_mapConst_lowerShriekOpenImmersionCounit (i : U ⟶ X)
    [IsOpenImmersion i.left] (K : BoundedCoherentDerived X.left)
    {N : (plusCoh X.left).FullSubcategory} (ψ : (boundedCoherentToPlusCoh X.left).obj K ⟶ N) :
    lowerShriekHomEquiv i (Stacks.Duality.openCompactification i)
        ((restrictBoundedCoherentLift i.left).obj K) N
        (ProSeq.mapConst (boundedCoherentToPlusCoh X.left) (lowerShriekOpenImmersionCounit i K) ≫
          ProSeq.const.map ψ) =
      (restrictBoundedCoherentPullIso i).inv.app K ≫ (pull i.left).map ψ.hom ≫
        (upperShriekStdOpenIso i).hom.app N := by
  rw [lowerShriekHomEquiv_comp_const, ← ProSeq.mapConstEquiv_apply, lowerShriekOpenImmersionCounit,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact (Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·) ((upperShriekStdOpenIso i).hom.naturality ψ).symm)

/-- **The first construction of [Stacks, Tag 0G56], at `K`**: `Rf_!` applied to the map
`Ri_!(K|_U) ⟶ K` of [Stacks, Tag 0G4Y] (`AlgebraicGeometry.lowerShriekOpenImmersionCounit`), as
the morphism `Rf_! Ri_!(K|_U) ⟶ Rf_! K` of `CategoryTheory.ProSeq.bindConstMap`, preceded by
`Rg_! = Rf_! ∘ Ri_!` ([Stacks, Tag 0G55], `AlgebraicGeometry.lowerShriekCompIso`), for any
compactification `cU` of `g = f ∘ i`. -/
def lowerShriekOpenImmersionCompMap (f : X ⟶ Y) (c : CompactificationOf (Over.mk f.left))
    (i : U ⟶ X) [IsOpenImmersion i.left] (cU : CompactificationOf (Over.mk (i ≫ f).left))
    (K : BoundedCoherentDerived X.left) :
    (lowerShriek (i ≫ f) cU).obj ((restrictBoundedCoherentLift i.left).obj K) ⟶
      (lowerShriek f c).obj K :=
  (lowerShriekCompIso i f (Stacks.Duality.openCompactification i) c cU _).inv ≫
    ProSeq.bindConstMap (lowerShriek f c) (lowerShriekOpenImmersionCounit i K)

variable {Z : FTS S} in
/-- The inverse of the isomorphism of [Stacks, Tag 0G55] on functors of points, followed by the
identification `Hom(R(g ∘ f)_! K, L) = Hom_X(K, (g ∘ f)^! L)` of [Stacks, Tag 0G51], is the
identification `Hom(Rg_! Rf_! K, L) = Hom_X(K, f^! g^! L)` followed by `f^! g^! = (g ∘ f)^!`. -/
theorem lowerShriekCompIso_inv_unop_hom_comp_lowerShriekPointsFunctorIsoStd_hom_app (f : X ⟶ Y)
    (g : Y ⟶ Z) (cf : CompactificationOf (Over.mk f.left))
    (cg : CompactificationOf (Over.mk g.left))
    (cfg : CompactificationOf (Over.mk (f ≫ g).left)) (K : BoundedCoherentDerived X.left) :
    (lowerShriekCompIso f g cf cg cfg K).inv.unop.hom ≫
        (lowerShriekPointsFunctorIsoStd (f ≫ g) cfg).hom.app (op K) =
      (lowerShriekCompPointsUpperShriekIso f g cf cg K).hom ≫
        (Functor.isoWhiskerLeft (boundedCoherentToPlusCoh Z.left)
          (Functor.isoWhiskerRight (upperShriekStdCompIso f g cf cg cfg).symm
            (coyoneda.obj (op ((boundedCoherentDerived X.left).ι.obj K))) ≪≫
            Functor.associator _ _ _)).inv :=
  Iso.trans_trans_symm_inv_comp_hom
    ((ProSeq.pointsFunctorIsoMap (boundedCoherentToPlusCoh Z.left)
      (lowerShriek (f ≫ g) cfg)).app (op K))
    (Functor.isoWhiskerLeft (boundedCoherentToPlusCoh Z.left)
      (ProSeq.pointsIsoHomConst _ ≪≫ (lowerShriekHomIso (f ≫ g) cfg).app (op K)))
    (Functor.isoWhiskerLeft (boundedCoherentToPlusCoh Z.left)
      (Functor.isoWhiskerRight (upperShriekStdCompIso f g cf cg cfg).symm
        (coyoneda.obj (op ((boundedCoherentDerived X.left).ι.obj K))) ≪≫ Functor.associator _ _ _))
    (lowerShriekCompPointsUpperShriekIso f g cf cg K)

/-- On functors of points, the first construction of [Stacks, Tag 0G56] at any compactification
`cU` of `g = f ∘ i` is the identification of the proof of [Stacks, Tag 0G55] applied to the image
of the point under `Rf_!` of `Ri_!(K|_U) ⟶ K`, followed by `i^! f^! = g^!`. -/
theorem lowerShriekPointsFunctorIsoStd_hom_app_app_lowerShriekOpenImmersionCompMap_of (f : X ⟶ Y)
    (c : CompactificationOf (Over.mk f.left)) (i : U ⟶ X) [IsOpenImmersion i.left]
    (cU : CompactificationOf (Over.mk (i ≫ f).left)) (K : BoundedCoherentDerived X.left)
    (L : BoundedCoherentDerived Y.left) (x : ((lowerShriek f c).obj K).points.obj L) :
    ((lowerShriekPointsFunctorIsoStd (i ≫ f) cU).hom.app
        (op ((restrictBoundedCoherentLift i.left).obj K))).app L
        ((lowerShriekOpenImmersionCompMap f c i cU K).unop.hom.app L x) =
      (lowerShriekCompPointsUpperShriekIso i f (Stacks.Duality.openCompactification i) c
          ((restrictBoundedCoherentLift i.left).obj K)).hom.app L
          ((ProSeq.bindConstMap (lowerShriek f c) (lowerShriekOpenImmersionCounit i K)).unop.hom.app
            L x) ≫
        (upperShriekStdCompIso i f (Stacks.Duality.openCompactification i) c cU).hom.app
          ((boundedCoherentToPlusCoh Y.left).obj L) := by
  have h₁ : (lowerShriekOpenImmersionCompMap f c i cU K).unop.hom ≫
      (lowerShriekPointsFunctorIsoStd (i ≫ f) cU).hom.app
        (op ((restrictBoundedCoherentLift i.left).obj K)) =
      (ProSeq.bindConstMap (lowerShriek f c) (lowerShriekOpenImmersionCounit i K)).unop.hom ≫
        (lowerShriekCompPointsUpperShriekIso i f (Stacks.Duality.openCompactification i) c
          ((restrictBoundedCoherentLift i.left).obj K)).hom ≫
        (Functor.isoWhiskerLeft (boundedCoherentToPlusCoh Y.left)
          (Functor.isoWhiskerRight
            (upperShriekStdCompIso i f (Stacks.Duality.openCompactification i) c cU).symm
            (coyoneda.obj (op ((boundedCoherentDerived U.left).ι.obj
              ((restrictBoundedCoherentLift i.left).obj K)))) ≪≫ Functor.associator _ _ _)).inv :=
    (Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
      (lowerShriekCompIso_inv_unop_hom_comp_lowerShriekPointsFunctorIsoStd_hom_app i f
        (Stacks.Duality.openCompactification i) c cU ((restrictBoundedCoherentLift i.left).obj K)))
  have h₂ := ConcreteCategory.congr_hom (congr_app h₁ L) x
  exact h₂.trans
    ((NatTrans.comp_app_apply _ _ _ x).trans ((NatTrans.comp_app_apply _ _ _ _).trans
      (isoWhiskerLeft_isoWhiskerRight_coyoneda_inv_app _ _ _ _
        (upperShriekStdCompIso i f (Stacks.Duality.openCompactification i) c cU) _ L _)))

/-- On functors of points, the first construction of [Stacks, Tag 0G56] is restriction
`Hom_X(K, f^! L) ⟶ Hom_U(K|_U, g^! L)`, under the identifications of [Stacks, Tag 0G51]. -/
theorem lowerShriekPointsFunctorIsoStd_hom_app_app_lowerShriekOpenImmersionCompMap (f : X ⟶ Y)
    (c : CompactificationOf (Over.mk f.left)) (i : U ⟶ X) [IsOpenImmersion i.left]
    (K : BoundedCoherentDerived X.left) (L : BoundedCoherentDerived Y.left)
    (x : ((lowerShriek f c).obj K).points.obj L) :
    ((lowerShriekPointsFunctorIsoStd (i ≫ f) (c.precompOpen i.left)).hom.app
        (op ((restrictBoundedCoherentLift i.left).obj K))).app L
        ((lowerShriekOpenImmersionCompMap f c i (c.precompOpen i.left) K).unop.hom.app L x) =
      (restrictBoundedCoherentPullIso i).inv.app K ≫
        (pull i.left).map (((lowerShriekPointsFunctorIsoStd f c).hom.app (op K)).app L x) ≫
        (upperShriekStdPrecompOpenIso i f c (c.precompOpen i.left)).hom.app
          ((boundedCoherentToPlusCoh Y.left).obj L) := by
  refine (lowerShriekPointsFunctorIsoStd_hom_app_app_lowerShriekOpenImmersionCompMap_of f c i
    (c.precompOpen i.left) K L x).trans ?_
  rw [lowerShriekCompPointsUpperShriekIso_hom_app_bindConstMap,
    lowerShriekHomEquiv_mapConst_lowerShriekOpenImmersionCounit, Category.assoc, Category.assoc]
  exact congrArg (fun t => _ ≫ _ ≫ t)
    (upperShriekStdOpenIso_hom_app_comp_upperShriekStdCompIso_hom_app i f c _)

/-- The first construction of [Stacks, Tag 0G56] at `K` is the third
(`AlgebraicGeometry.lowerShriekOpenImmersionMap`), with `Rg_!` computed at the compactification
of `g = f ∘ i` restricted from that of `f`. -/
theorem lowerShriekOpenImmersionCompMap_eq_lowerShriekOpenImmersionMap_app (f : X ⟶ Y)
    (c : CompactificationOf (Over.mk f.left)) (i : U ⟶ X) [IsOpenImmersion i.left]
    (K : BoundedCoherentDerived X.left) :
    lowerShriekOpenImmersionCompMap f c i (c.precompOpen i.left) K =
      (lowerShriekOpenImmersionMap f c i (c.precompOpen i.left)).app K := by
  rw [← lowerShriekOpenImmersionMapOfCompactification_eq_lowerShriekOpenImmersionMap]
  apply Quiver.Hom.unop_inj
  apply ObjectProperty.hom_ext
  ext L x
  apply ((((lowerShriekPointsFunctorIsoStd (i ≫ f) (c.precompOpen i.left)).app
    (op ((restrictBoundedCoherentLift i.left).obj K))).app L).toEquiv).injective
  exact (lowerShriekPointsFunctorIsoStd_hom_app_app_lowerShriekOpenImmersionCompMap
    f c i K L x).trans
    (lowerShriekPointsFunctorIsoStd_hom_app_app_lowerShriekOpenImmersionMapOfCompactification
      f c i K L x).symm

/-- In Situation [Stacks, Tag 0F42] let `f : X ⟶ Y` be a morphism of `FTS_S`, `i : U ⟶ X` an
open immersion and `g = f ∘ i`. The canonical map `Rg_!(K|_U) ⟶ Rf_! K`, functorial in `K` in
`D^b_{Coh}(𝒪_X)`, obtained from `Rg_! = Rf_! ∘ Ri_!` ([Stacks, Tag 0G55]) and `Rf_!` applied to the
map `Ri_!(K|_U) ⟶ K` of [Stacks, Tag 0G4Y] (`AlgebraicGeometry.lowerShriekOpenImmersionCompMap`),
with `Ri_!` computed at the compactification `X` of `U` over `X` and `Rg_!` at the
compactification restricted from the compactification `c` of `f`. -/
@[stacks 0G56 "construction (1): Rf_! applied to the map Ri_!(K|_U) ⟶ K of Tag 0G4Y, through \
Rg_! = Rf_! ∘ Ri_! of Tag 0G55, functorial in K"]
def lowerShriekOpenImmersionMapOfComposition (f : X ⟶ Y) (c : CompactificationOf (Over.mk f.left))
    (i : U ⟶ X) [IsOpenImmersion i.left] :
    restrictBoundedCoherentLift i.left ⋙ lowerShriek (i ≫ f) (c.precompOpen i.left) ⟶
      lowerShriek f c where
  app K := lowerShriekOpenImmersionCompMap f c i (c.precompOpen i.left) K
  naturality {K K'} k := by
    rw [lowerShriekOpenImmersionCompMap_eq_lowerShriekOpenImmersionMap_app,
      lowerShriekOpenImmersionCompMap_eq_lowerShriekOpenImmersionMap_app]
    exact (lowerShriekOpenImmersionMap f c i (c.precompOpen i.left)).naturality k

/-- `Rf_!` applied to the map `Ri_!(K|_U) ⟶ K` of [Stacks, Tag 0G4Y] through `Rg_! = Rf_! ∘ Ri_!`
is the map induced by
`Hom(Rf_! K, L) = Hom_X(K, f^! L) ⟶ Hom_U(K|_U, g^! L) = Hom(Rg_!(K|_U), L)`. -/
@[stacks 0G56 "constructions (1) and (3) give the same arrow"]
theorem lowerShriekOpenImmersionMapOfComposition_eq_lowerShriekOpenImmersionMap (f : X ⟶ Y)
    (c : CompactificationOf (Over.mk f.left)) (i : U ⟶ X) [IsOpenImmersion i.left] :
    lowerShriekOpenImmersionMapOfComposition f c i =
      lowerShriekOpenImmersionMap f c i (c.precompOpen i.left) :=
  NatTrans.ext (funext fun K => lowerShriekOpenImmersionCompMap_eq_lowerShriekOpenImmersionMap_app
    f c i K)

/-- `Rf_!` applied to the map `Ri_!(K|_U) ⟶ K` of [Stacks, Tag 0G4Y] through `Rg_! = Rf_! ∘ Ri_!`
is `Rf̄_*` applied to the map `Rj'_!(K|_U) ⟶ Rj_! K` of [Stacks, Tag 0G4Y], for the
compactification `j : X ⟶ X̄`. -/
@[stacks 0G56 "constructions (1) and (2) give the same arrow"]
theorem lowerShriekOpenImmersionMapOfComposition_eq_lowerShriekOpenImmersionMapOfCompactification
    (f : X ⟶ Y) (c : CompactificationOf (Over.mk f.left)) (i : U ⟶ X) [IsOpenImmersion i.left] :
    lowerShriekOpenImmersionMapOfComposition f c i =
      lowerShriekOpenImmersionMapOfCompactification f c i :=
  (lowerShriekOpenImmersionMapOfComposition_eq_lowerShriekOpenImmersionMap f c i).trans
    (lowerShriekOpenImmersionMapOfCompactification_eq_lowerShriekOpenImmersionMap f c i).symm

end AlgebraicGeometry

end
