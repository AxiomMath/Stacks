module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffinePointwiseRingChange
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedStalkCompositionAssembly
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TensorBaseChange.StalkLocalization
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.CoverRepresentatives
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CompIsoLeftApp

/-!
# The map of Stacks 0DJ7 along open immersions

Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a cartesian square of schemes, `K ∈ D(𝒪_X)`, `K' ∈ D(𝒪_{X'})` and `φ : L(g')^*K ⟶ K'`.  For a
second cartesian square `Z' → Z → T ← T'` mapping to the first by open immersions, the map of
Stacks 0DJ7 of the second square at the pulled-back datum is invertible at a point as soon as the
map of the first square is invertible at its image: condition (1) of Stacks 0DJ8 restricts to
opens.

## Main results

* `AlgebraicGeometry.isIso_baseChangeCohomologyMap_comp_left`: restricting the corner `X'`.
* `AlgebraicGeometry.isIso_baseChangeCohomologyMap_congr`: equal squares.
* `AlgebraicGeometry.isIso_baseChangeCohomologyMap_restrict_source`: restricting the corners `X`,
  `S`, `S'`.
* `AlgebraicGeometry.isIso_baseChangeCohomologyMap_pullDatum`: the composite statement.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open RingTheory.TorIndependence CochainComplex.DerivedExtensionScalars
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces Stacks.DerivedPullback.Composition

universe u

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X}

private theorem inv_eq_of_eq_trans {C : Type*} [Category C] {a b c : C} (X : a ≅ c) (W : a ≅ b)
    (D : b ≅ c) (h : X = W ≪≫ D) : W.inv = D.hom ≫ X.inv := by
  subst h
  simp

private theorem chase_left {C : Type*} [Category C] {P₀ P₂ P₃ P₄ P₅ P₆ P₇ : C}
    (τ : P₃ ⟶ P₃) (Einv : P₃ ⟶ P₇) (Tc : P₇ ⟶ P₆) (Dinv : P₃ ⟶ P₀) (Sc : P₀ ⟶ P₅)
    (PhK : P₅ ⟶ P₆) (Dhom : P₀ ⟶ P₃) (sc : P₀ ⟶ P₂) (tdg : P₇ ⟶ P₄) (Pinv : P₄ ⟶ P₂)
    (Phom : P₂ ⟶ P₄) (sL : P₂ ⟶ P₅) (tsφ : P₄ ⟶ P₆)
    (hτ : τ = 𝟙 _) (hT : Tc = tdg ≫ tsφ) (hS : Sc = sc ≫ sL) (h1 : Dinv ≫ Dhom = 𝟙 _)
    (hN : sL ≫ PhK = Phom ≫ tsφ) (h2 : Pinv ≫ Phom = 𝟙 _) (Xinv : P₃ ⟶ P₂)
    (hX : Xinv = Einv ≫ tdg ≫ Pinv) (hW : sc = Dhom ≫ Xinv) :
    τ ≫ Einv ≫ Tc = (Dinv ≫ Sc) ≫ PhK := by
  subst hτ hT hS hW hX
  simp only [Category.assoc, Category.id_comp, hN, reassoc_of% h1, reassoc_of% h2]

/-- **Condition (1) of Stacks 0DJ8 restricts along an open immersion into `X'`.**  For an open
immersion `j : Z' ⟶ X'`, the map of Stacks 0DJ7 of the square `Z' → X → S ← S'` at
`L(j ≫ g')^*K ≅ Lj^*L(g')^*K ⟶ Lj^*K'` is invertible at `z'` as soon as that of the original
square is invertible at `j z'`. -/
theorem isIso_baseChangeCohomologyMap_comp_left (hpb : IsPullback g' f' f g) {Z' : Scheme.{u}}
    (j : Z' ⟶ X') [IsOpenImmersion j] (K : DerivedCategory X.Modules)
    (K' : DerivedCategory X'.Modules) (φ : (derivedPullback g'.toLRSHom.toShHom).obj K ⟶ K')
    (z' : Z') (n : ℤ) (h : IsIso (baseChangeCohomologyMap f g f' g' hpb.w K K' φ (j z') n)) :
    IsIso (baseChangeCohomologyMap f g (j ≫ f') (j ≫ g')
      (by rw [Category.assoc, hpb.w, Category.assoc]) K
      ((derivedPullback j.toLRSHom.toShHom).obj K')
      ((derivedPullbackCompIsoCanonical j.toLRSHom.toShHom g'.toLRSHom.toShHom).inv.app K ≫
        (derivedPullback j.toLRSHom.toShHom).map φ) z' n) := by
  have w₄ : (j ≫ g') ≫ f = (j ≫ f') ≫ g := by rw [Category.assoc, hpb.w, Category.assoc]
  let : Algebra (S.presheaf.stalk (f (g' (j z')))) (X.presheaf.stalk (g' (j z'))) :=
    ((f.stalkMap (g' (j z'))).hom).toAlgebra
  let : Algebra (S.presheaf.stalk (f (g' (j z')))) (S'.presheaf.stalk (f' (j z'))) :=
    (baseStalkMap f g f' g' hpb.w (j z')).toAlgebra
  let : Algebra (S.presheaf.stalk (f (g' (j z')))) (X'.presheaf.stalk (j z')) :=
    (((g'.stalkMap (j z')).hom).comp ((f.stalkMap (g' (j z'))).hom)).toAlgebra
  let : Algebra (X.presheaf.stalk (g' (j z'))) (X'.presheaf.stalk (j z')) :=
    ((g'.stalkMap (j z')).hom).toAlgebra
  let : Algebra (S'.presheaf.stalk (f' (j z'))) (X'.presheaf.stalk (j z')) :=
    ((f'.stalkMap (j z')).hom).toAlgebra
  have : IsScalarTower (S.presheaf.stalk (f (g' (j z')))) (X.presheaf.stalk (g' (j z')))
      (X'.presheaf.stalk (j z')) := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower (S.presheaf.stalk (f (g' (j z')))) (S'.presheaf.stalk (f' (j z')))
      (X'.presheaf.stalk (j z')) :=
    IsScalarTower.of_algebraMap_eq' (stalkMap_square f g f' g' hpb.w (j z'))
  let : Algebra (X'.presheaf.stalk (j z')) (Z'.presheaf.stalk z') := ((j.stalkMap z').hom).toAlgebra
  let : Algebra (X.presheaf.stalk (g' (j z'))) (Z'.presheaf.stalk z') :=
    (((j ≫ g').stalkMap z').hom).toAlgebra
  let : Algebra (S'.presheaf.stalk (f' (j z'))) (Z'.presheaf.stalk z') :=
    (((j ≫ f').stalkMap z').hom).toAlgebra
  let : Algebra (S.presheaf.stalk (f (g' (j z')))) (Z'.presheaf.stalk z') :=
    ((((j ≫ g').stalkMap z').hom).comp ((f.stalkMap (g' (j z'))).hom)).toAlgebra
  have : IsScalarTower (X.presheaf.stalk (g' (j z'))) (X'.presheaf.stalk (j z'))
      (Z'.presheaf.stalk z') :=
    IsScalarTower.of_algebraMap_eq' (Stacks.ModuleSkyscraper.stalkMap_hom_comp j g' z')
  have : IsScalarTower (S'.presheaf.stalk (f' (j z'))) (X'.presheaf.stalk (j z'))
      (Z'.presheaf.stalk z') :=
    IsScalarTower.of_algebraMap_eq' (Stacks.ModuleSkyscraper.stalkMap_hom_comp j f' z')
  have : IsScalarTower (S.presheaf.stalk (f (g' (j z')))) (X.presheaf.stalk (g' (j z')))
      (Z'.presheaf.stalk z') := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower (S.presheaf.stalk (f (g' (j z')))) (S'.presheaf.stalk (f' (j z')))
      (Z'.presheaf.stalk z') :=
    IsScalarTower.of_algebraMap_eq' (stalkMap_square f g (j ≫ f') (j ≫ g') w₄ z')
  have hτ : Function.Bijective (algebraMap (X'.presheaf.stalk (j z')) (Z'.presheaf.stalk z')) :=
    ConcreteCategory.bijective_of_isIso (j.stalkMap z')
  have h₁ := (isIso_baseChangeCohomologyMap_iff_ring f g f' g' hpb.w K K' φ (j z') n).1 h
  have h₄ := isIso_ringBaseChangeCohomologyMap_target (R := S.presheaf.stalk (f (g' (j z'))))
    (R' := S'.presheaf.stalk (f' (j z'))) hτ (exists_isLocalization_stalk hpb (j z')) _ _ _ n h₁
  refine (isIso_baseChangeCohomologyMap_iff_ring f g (j ≫ f') (j ≫ g') w₄ K _ _ z' n).2 ?_
  refine (isIso_ringBaseChangeCohomologyMap_iff_of_iso (R := S.presheaf.stalk (f (g' (j z'))))
    (R' := S'.presheaf.stalk (f' (j z'))) (A := X.presheaf.stalk (g' (j z')))
    (A' := Z'.presheaf.stalk z')
    (Iso.refl _)
    ((derivedPullbackStalkIso j z').app K') _ _ ?_ n).2 h₄
  have hW0 := inv_eq_of_eq_trans _ _ _ (derivedPullbackStalkCompIso_eq j g' z')
  have hN := (derivedPullbackStalkIso j z').hom.naturality φ
  have hW1 := congrArg (fun t => NatTrans.app t K) hW0
  refine chase_left _ _ _ _ _ _ _ _ _ _ _ _ _ (CategoryTheory.Functor.map_id _ _)
    (CategoryTheory.Functor.map_comp _ _ _) (CategoryTheory.Functor.map_comp _ _ _)
    (Iso.inv_hom_id_app _ _) hN (Iso.inv_hom_id_app (derivedPullbackStalkIso j z') _)
    ((derivedPullbackStalkCompIso j g' z').inv.app K) ?_ hW1
  exact Category.assoc _ _ _

/-- **Condition (1) of Stacks 0DJ8 for equal squares.** Invertibility of
`baseChangeCohomologyMap` transports along equalities of the morphisms `f'` and `g'` and of the
comparison maps `φ`. -/
theorem isIso_baseChangeCohomologyMap_congr (f : X ⟶ S) (g : S' ⟶ S) {f'₁ f'₂ : X' ⟶ S'}
    {g'₁ g'₂ : X' ⟶ X} (hf : f'₁ = f'₂) (hg : g'₁ = g'₂) (w₁ : g'₁ ≫ f = f'₁ ≫ g)
    (w₂ : g'₂ ≫ f = f'₂ ≫ g) (K : DerivedCategory X.Modules) (K' : DerivedCategory X'.Modules)
    (φ₁ : (derivedPullback g'₁.toLRSHom.toShHom).obj K ⟶ K')
    (φ₂ : (derivedPullback g'₂.toLRSHom.toShHom).obj K ⟶ K') (hφ : HEq φ₁ φ₂)
    (x' : X') (n : ℤ) (h : IsIso (baseChangeCohomologyMap f g f'₁ g'₁ w₁ K K' φ₁ x' n)) :
    IsIso (baseChangeCohomologyMap f g f'₂ g'₂ w₂ K K' φ₂ x' n) := by
  subst hf hg
  cases eq_of_heq hφ
  exact h

/-- The local ring of `X'` at `x'` is a localization of the tensor product over the local ring
of `S` of the local rings of `X` and `S'`. -/
abbrev IsStalkLocalization (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (w : g' ≫ f = f' ≫ g) (x' : X') : Prop :=
  letI : Algebra (S.presheaf.stalk (f (g' x'))) (X.presheaf.stalk (g' x')) :=
    ((f.stalkMap (g' x')).hom).toAlgebra
  letI : Algebra (S.presheaf.stalk (f (g' x'))) (S'.presheaf.stalk (f' x')) :=
    (baseStalkMap f g f' g' w x').toAlgebra
  letI : Algebra (S.presheaf.stalk (f (g' x'))) (X'.presheaf.stalk x') :=
    (((g'.stalkMap x').hom).comp ((f.stalkMap (g' x')).hom)).toAlgebra
  letI : Algebra (X.presheaf.stalk (g' x')) (X'.presheaf.stalk x') :=
    ((g'.stalkMap x').hom).toAlgebra
  letI : Algebra (S'.presheaf.stalk (f' x')) (X'.presheaf.stalk x') :=
    ((f'.stalkMap x').hom).toAlgebra
  letI : IsScalarTower (S.presheaf.stalk (f (g' x'))) (X.presheaf.stalk (g' x'))
      (X'.presheaf.stalk x') := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower (S.presheaf.stalk (f (g' x'))) (S'.presheaf.stalk (f' x'))
      (X'.presheaf.stalk x') := IsScalarTower.of_algebraMap_eq' (stalkMap_square f g f' g' w x')
  letI := (baseChangeTensorRingMap (R := S.presheaf.stalk (f (g' x')))
    (A := X.presheaf.stalk (g' x')) (R' := S'.presheaf.stalk (f' x'))
    (A' := X'.presheaf.stalk x')).toAlgebra
  ∃ M : Submonoid (X.presheaf.stalk (g' x') ⊗[S.presheaf.stalk (f (g' x'))]
    S'.presheaf.stalk (f' x')), IsLocalization M (X'.presheaf.stalk x')

/-- `IsStalkLocalization` is transported along equalities of the morphisms `f'` and `g'`. -/
theorem IsStalkLocalization.congr (f : X ⟶ S) (g : S' ⟶ S) {f'₁ f'₂ : X' ⟶ S'}
    {g'₁ g'₂ : X' ⟶ X} (hf : f'₁ = f'₂) (hg : g'₁ = g'₂) (w₁ : g'₁ ≫ f = f'₁ ≫ g)
    (w₂ : g'₂ ≫ f = f'₂ ≫ g) (x' : X') (h : IsStalkLocalization f g f'₁ g'₁ w₁ x') :
    IsStalkLocalization f g f'₂ g'₂ w₂ x' := by
  subst hf hg
  exact h

/-- For a pullback square of schemes, the local ring of `X'` at `x'` is a localization of the
tensor product of the local rings of `X` and `S'` over the local ring of `S`. -/
theorem isStalkLocalization_of_isPullback (hpb : IsPullback g' f' f g) (x' : X') :
    IsStalkLocalization f g f' g' hpb.w x' :=
  exists_isLocalization_stalk hpb x'

/-- If `IsStalkLocalization` holds at `j z'`, then it holds at `z'` for the square obtained by
precomposing `f'` and `g'` with an open immersion `j : Z' ⟶ X'`. -/
theorem IsStalkLocalization.comp_left (w : g' ≫ f = f' ≫ g) {Z' : Scheme.{u}}
    (j : Z' ⟶ X') [IsOpenImmersion j] (z' : Z') (h : IsStalkLocalization f g f' g' w (j z')) :
    IsStalkLocalization f g (j ≫ f') (j ≫ g') (by rw [Category.assoc, w, Category.assoc])
      z' := by
  have w₄ : (j ≫ g') ≫ f = (j ≫ f') ≫ g := by rw [Category.assoc, w, Category.assoc]
  let : Algebra (S.presheaf.stalk (f (g' (j z')))) (X.presheaf.stalk (g' (j z'))) :=
    ((f.stalkMap (g' (j z'))).hom).toAlgebra
  let : Algebra (S.presheaf.stalk (f (g' (j z')))) (S'.presheaf.stalk (f' (j z'))) :=
    (baseStalkMap f g f' g' w (j z')).toAlgebra
  let : Algebra (S.presheaf.stalk (f (g' (j z')))) (X'.presheaf.stalk (j z')) :=
    (((g'.stalkMap (j z')).hom).comp ((f.stalkMap (g' (j z'))).hom)).toAlgebra
  let : Algebra (X.presheaf.stalk (g' (j z'))) (X'.presheaf.stalk (j z')) :=
    ((g'.stalkMap (j z')).hom).toAlgebra
  let : Algebra (S'.presheaf.stalk (f' (j z'))) (X'.presheaf.stalk (j z')) :=
    ((f'.stalkMap (j z')).hom).toAlgebra
  have : IsScalarTower (S.presheaf.stalk (f (g' (j z')))) (X.presheaf.stalk (g' (j z')))
      (X'.presheaf.stalk (j z')) := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower (S.presheaf.stalk (f (g' (j z')))) (S'.presheaf.stalk (f' (j z')))
      (X'.presheaf.stalk (j z')) :=
    IsScalarTower.of_algebraMap_eq' (stalkMap_square f g f' g' w (j z'))
  let : Algebra (X'.presheaf.stalk (j z')) (Z'.presheaf.stalk z') :=
    ((j.stalkMap z').hom).toAlgebra
  let : Algebra (X.presheaf.stalk (g' (j z'))) (Z'.presheaf.stalk z') :=
    (((j ≫ g').stalkMap z').hom).toAlgebra
  let : Algebra (S'.presheaf.stalk (f' (j z'))) (Z'.presheaf.stalk z') :=
    (((j ≫ f').stalkMap z').hom).toAlgebra
  let : Algebra (S.presheaf.stalk (f (g' (j z')))) (Z'.presheaf.stalk z') :=
    ((((j ≫ g').stalkMap z').hom).comp ((f.stalkMap ((j ≫ g') z')).hom)).toAlgebra
  have : IsScalarTower (X.presheaf.stalk (g' (j z'))) (X'.presheaf.stalk (j z'))
      (Z'.presheaf.stalk z') :=
    IsScalarTower.of_algebraMap_eq' (Stacks.ModuleSkyscraper.stalkMap_hom_comp j g' z')
  have : IsScalarTower (S'.presheaf.stalk (f' (j z'))) (X'.presheaf.stalk (j z'))
      (Z'.presheaf.stalk z') :=
    IsScalarTower.of_algebraMap_eq' (Stacks.ModuleSkyscraper.stalkMap_hom_comp j f' z')
  have : IsScalarTower (S.presheaf.stalk (f (g' (j z')))) (X.presheaf.stalk (g' (j z')))
      (Z'.presheaf.stalk z') := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower (S.presheaf.stalk (f (g' (j z')))) (S'.presheaf.stalk (f' (j z')))
      (Z'.presheaf.stalk z') :=
    IsScalarTower.of_algebraMap_eq' (stalkMap_square f g (j ≫ f') (j ≫ g') w₄ z')
  exact exists_isLocalization_of_bijective (R := S.presheaf.stalk (f (g' (j z'))))
    (A := X.presheaf.stalk (g' (j z'))) (R' := S'.presheaf.stalk (f' (j z')))
    (A' := X'.presheaf.stalk (j z')) (A'₂ := Z'.presheaf.stalk z')
    (ConcreteCategory.bijective_of_isIso (j.stalkMap z')) h

/-- Two composites of stalk identifications between the same points agree. -/
theorem stalkCongr_comp_eq {T : Scheme.{u}} {a b c d : T} (h₁ : a = b) (h₂ : b = d) (h₃ : a = c)
    (h₄ : c = d) :
    (T.presheaf.stalkCongr (.of_eq h₁)).hom ≫ (T.presheaf.stalkCongr (.of_eq h₂)).hom =
      (T.presheaf.stalkCongr (.of_eq h₃)).hom ≫ (T.presheaf.stalkCongr (.of_eq h₄)).hom := by
  subst h₁ h₂ h₄
  simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl,
    Category.comp_id]

private theorem inv_eq_of_eq_trans_right {C : Type*} [Category C] {a b c : C} (X : a ≅ c)
    (W : a ≅ b) (D : b ≅ c) (h : X = W ≪≫ D) : D.inv = X.inv ≫ W.hom := by
  subst h
  simp

private theorem chase_source {C : Type*} [Category C] {P₀ P₁ P₂ P₃ P₄ P₅ : C}
    (Tθ : P₀ ⟶ P₁) (tw : P₁ ⟶ P₂) (Einv : P₂ ⟶ P₄) (Dψ : P₄ ⟶ P₅) (Dinv : P₀ ⟶ P₃)
    (Dcψ : P₃ ⟶ P₅) (ι : P₅ ⟶ P₅) (Dc : P₃ ⟶ P₄) (twinv : P₂ ⟶ P₁) (Tθinv : P₁ ⟶ P₀)
    (Xinv : P₂ ⟶ P₃) (hι : ι = 𝟙 _) (hD : Dcψ = Dc ≫ Dψ) (hE : Einv = Xinv ≫ Dc)
    (hX : Xinv = twinv ≫ Tθinv ≫ Dinv) (h1 : tw ≫ twinv = 𝟙 _) (h2 : Tθ ≫ Tθinv = 𝟙 _) :
    Tθ ≫ tw ≫ Einv ≫ Dψ = (Dinv ≫ Dcψ) ≫ ι := by
  subst hι hD hE hX
  simp only [Category.assoc, Category.comp_id, reassoc_of% h1, reassoc_of% h2]

variable {X₂ S₂ S₂' Y : Scheme.{u}}

/-- **Condition (1) of Stacks 0DJ8 restricts along open immersions into `X`, `S` and `S'`.**
Let `Y → X₂ → S₂ ← S₂'` be a commutative square mapping to `X → S ← S'` by open immersions
`X₂ ⟶ X`, `S₂ ⟶ S`, `S₂' ⟶ S'`.  The map of Stacks 0DJ7 of the second square at the datum
`L(g₂')^*L(i_X)^*K ≅ L(g₂' ≫ i_X)^*K ⟶ E'` is invertible at `y` as soon as that of the square
`Y → X → S ← S'` at `ψ` is. -/
theorem isIso_baseChangeCohomologyMap_restrict_source (f : X ⟶ S) (g : S' ⟶ S)
    {f₂ : X₂ ⟶ S₂} {g₂ : S₂' ⟶ S₂} {f₂' : Y ⟶ S₂'} {g₂' : Y ⟶ X₂}
    (w₂ : g₂' ≫ f₂ = f₂' ≫ g₂) (iX : X₂ ⟶ X) (iS : S₂ ⟶ S) (iS' : S₂' ⟶ S')
    [IsOpenImmersion iX] [IsOpenImmersion iS] [IsOpenImmersion iS']
    (hf : f₂ ≫ iS = iX ≫ f) (hg : g₂ ≫ iS = iS' ≫ g) (w : (g₂' ≫ iX) ≫ f = (f₂' ≫ iS') ≫ g)
    (K : DerivedCategory X.Modules) (E' : DerivedCategory Y.Modules)
    (ψ : (derivedPullback (g₂' ≫ iX).toLRSHom.toShHom).obj K ⟶ E') (y : Y) (n : ℤ)
    (hloc : IsStalkLocalization f g (f₂' ≫ iS') (g₂' ≫ iX) w y)
    (hloc₂ : IsStalkLocalization f₂ g₂ f₂' g₂' w₂ y)
    (h : IsIso (baseChangeCohomologyMap f g (f₂' ≫ iS') (g₂' ≫ iX) w K E' ψ y n)) :
    IsIso (baseChangeCohomologyMap f₂ g₂ f₂' g₂' w₂
      ((derivedPullback iX.toLRSHom.toShHom).obj K) E'
      ((derivedPullbackCompIsoCanonical g₂'.toLRSHom.toShHom iX.toLRSHom.toShHom).hom.app K ≫
        ψ) y n) := by
  have hpt : iS (f₂ (g₂' y)) = f (iX (g₂' y)) := congrArg (fun k : X₂ ⟶ S => k (g₂' y)) hf
  -- the base square
  let : Algebra (S.presheaf.stalk (f ((g₂' ≫ iX) y))) (X.presheaf.stalk ((g₂' ≫ iX) y)) :=
    ((f.stalkMap ((g₂' ≫ iX) y)).hom).toAlgebra
  let : Algebra (S.presheaf.stalk (f ((g₂' ≫ iX) y))) (S'.presheaf.stalk ((f₂' ≫ iS') y)) :=
    (baseStalkMap f g (f₂' ≫ iS') (g₂' ≫ iX) w y).toAlgebra
  let : Algebra (S.presheaf.stalk (f ((g₂' ≫ iX) y))) (Y.presheaf.stalk y) :=
    ((((g₂' ≫ iX).stalkMap y).hom).comp ((f.stalkMap ((g₂' ≫ iX) y)).hom)).toAlgebra
  let : Algebra (X.presheaf.stalk ((g₂' ≫ iX) y)) (Y.presheaf.stalk y) :=
    (((g₂' ≫ iX).stalkMap y).hom).toAlgebra
  let : Algebra (S'.presheaf.stalk ((f₂' ≫ iS') y)) (Y.presheaf.stalk y) :=
    (((f₂' ≫ iS').stalkMap y).hom).toAlgebra
  have : IsScalarTower (S.presheaf.stalk (f ((g₂' ≫ iX) y))) (X.presheaf.stalk ((g₂' ≫ iX) y))
      (Y.presheaf.stalk y) := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower (S.presheaf.stalk (f ((g₂' ≫ iX) y))) (S'.presheaf.stalk ((f₂' ≫ iS') y))
      (Y.presheaf.stalk y) :=
    IsScalarTower.of_algebraMap_eq' (stalkMap_square f g (f₂' ≫ iS') (g₂' ≫ iX) w y)
  -- the restricted square
  let : Algebra (S₂.presheaf.stalk (f₂ (g₂' y))) (X₂.presheaf.stalk (g₂' y)) :=
    ((f₂.stalkMap (g₂' y)).hom).toAlgebra
  let : Algebra (S₂.presheaf.stalk (f₂ (g₂' y))) (S₂'.presheaf.stalk (f₂' y)) :=
    (baseStalkMap f₂ g₂ f₂' g₂' w₂ y).toAlgebra
  let : Algebra (S₂.presheaf.stalk (f₂ (g₂' y))) (Y.presheaf.stalk y) :=
    (((g₂'.stalkMap y).hom).comp ((f₂.stalkMap (g₂' y)).hom)).toAlgebra
  let : Algebra (X₂.presheaf.stalk (g₂' y)) (Y.presheaf.stalk y) :=
    ((g₂'.stalkMap y).hom).toAlgebra
  let : Algebra (S₂'.presheaf.stalk (f₂' y)) (Y.presheaf.stalk y) :=
    ((f₂'.stalkMap y).hom).toAlgebra
  have : IsScalarTower (S₂.presheaf.stalk (f₂ (g₂' y))) (X₂.presheaf.stalk (g₂' y))
      (Y.presheaf.stalk y) := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower (S₂.presheaf.stalk (f₂ (g₂' y))) (S₂'.presheaf.stalk (f₂' y))
      (Y.presheaf.stalk y) := IsScalarTower.of_algebraMap_eq' (stalkMap_square f₂ g₂ f₂' g₂' w₂ y)
  -- the maps between them
  let : Algebra (S.presheaf.stalk (f ((g₂' ≫ iX) y))) (S₂.presheaf.stalk (f₂ (g₂' y))) :=
    ((S.presheaf.stalkCongr (.of_eq hpt.symm)).hom ≫ iS.stalkMap (f₂ (g₂' y))).hom.toAlgebra
  let : Algebra (X.presheaf.stalk ((g₂' ≫ iX) y)) (X₂.presheaf.stalk (g₂' y)) :=
    ((iX.stalkMap (g₂' y)).hom).toAlgebra
  let : Algebra (S'.presheaf.stalk ((f₂' ≫ iS') y)) (S₂'.presheaf.stalk (f₂' y)) :=
    ((iS'.stalkMap (f₂' y)).hom).toAlgebra
  let : Algebra (S.presheaf.stalk (f ((g₂' ≫ iX) y))) (X₂.presheaf.stalk (g₂' y)) :=
    (((iX.stalkMap (g₂' y)).hom).comp ((f.stalkMap ((g₂' ≫ iX) y)).hom)).toAlgebra
  let : Algebra (S.presheaf.stalk (f ((g₂' ≫ iX) y))) (S₂'.presheaf.stalk (f₂' y)) :=
    ((baseStalkMap f₂ g₂ f₂' g₂' w₂ y).comp
      ((S.presheaf.stalkCongr (.of_eq hpt.symm)).hom ≫ iS.stalkMap (f₂ (g₂' y))).hom).toAlgebra
  have : IsScalarTower (S.presheaf.stalk (f ((g₂' ≫ iX) y))) (X.presheaf.stalk ((g₂' ≫ iX) y))
      (X₂.presheaf.stalk (g₂' y)) := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower (S.presheaf.stalk (f ((g₂' ≫ iX) y))) (S₂.presheaf.stalk (f₂ (g₂' y)))
      (S₂'.presheaf.stalk (f₂' y)) := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower (X.presheaf.stalk ((g₂' ≫ iX) y)) (X₂.presheaf.stalk (g₂' y))
      (Y.presheaf.stalk y) :=
    IsScalarTower.of_algebraMap_eq' (Stacks.ModuleSkyscraper.stalkMap_hom_comp g₂' iX y)
  have : IsScalarTower (S'.presheaf.stalk ((f₂' ≫ iS') y)) (S₂'.presheaf.stalk (f₂' y))
      (Y.presheaf.stalk y) :=
    IsScalarTower.of_algebraMap_eq' (Stacks.ModuleSkyscraper.stalkMap_hom_comp f₂' iS' y)
  have : IsScalarTower (S.presheaf.stalk (f ((g₂' ≫ iX) y))) (S₂.presheaf.stalk (f₂ (g₂' y)))
      (X₂.presheaf.stalk (g₂' y)) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    have e := Scheme.Hom.stalkMap_congr_hom (iX ≫ f) (f₂ ≫ iS) hf.symm (g₂' y)
    rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp] at e
    exact congrArg CommRingCat.Hom.hom (e.trans (Category.assoc _ _ _).symm)
  have : IsScalarTower (S.presheaf.stalk (f ((g₂' ≫ iX) y))) (S'.presheaf.stalk ((f₂' ≫ iS') y))
      (S₂'.presheaf.stalk (f₂' y)) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    have hpt₂ : f₂ (g₂' y) = g₂ (f₂' y) := congrArg (fun k : Y ⟶ S₂ => k y) w₂
    have hpt₅ : f (iX (g₂' y)) = g (iS' (f₂' y)) := congrArg (fun k : Y ⟶ S => k y) w
    have e1 := Scheme.Hom.stalkMap_congr_point iS (f₂ (g₂' y)) (g₂ (f₂' y)) hpt₂
    have e2 := Scheme.Hom.stalkMap_congr_hom (iS' ≫ g) (g₂ ≫ iS) hg.symm (f₂' y)
    rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp] at e2
    have key : ((S.presheaf.stalkCongr (.of_eq hpt.symm)).hom ≫ iS.stalkMap (f₂ (g₂' y))) ≫
        (S₂.presheaf.stalkCongr (.of_eq hpt₂)).hom ≫ g₂.stalkMap (f₂' y) =
        ((S.presheaf.stalkCongr (.of_eq hpt₅)).hom ≫
          g.stalkMap (iS' (f₂' y))) ≫ iS'.stalkMap (f₂' y) := by
      rw [Category.assoc, reassoc_of% e1, Category.assoc, e2]
      simp only [← Category.assoc]
      exact (stalkCongr_comp_eq hpt.symm (congrArg iS hpt₂) hpt₅
        (congrArg (fun k : S₂' ⟶ S => k (f₂' y)) hg).symm =≫ _) =≫ _
    exact congrArg CommRingCat.Hom.hom key
  have : IsIso ((S.presheaf.stalkCongr (.of_eq hpt.symm)).hom ≫ iS.stalkMap (f₂ (g₂' y))) :=
    inferInstance
  have := isLocalization_bot_of_bijective (C := S.presheaf.stalk (f ((g₂' ≫ iX) y)))
    (D := S₂.presheaf.stalk (f₂ (g₂' y))) (ConcreteCategory.bijective_of_isIso
      ((S.presheaf.stalkCongr (.of_eq hpt.symm)).hom ≫ iS.stalkMap (f₂ (g₂' y))))
  have := isLocalization_bot_of_bijective (C := X.presheaf.stalk ((g₂' ≫ iX) y))
    (D := X₂.presheaf.stalk (g₂' y)) (ConcreteCategory.bijective_of_isIso (iX.stalkMap (g₂' y)))
  have := isLocalization_bot_of_bijective (C := S'.presheaf.stalk ((f₂' ≫ iS') y))
    (D := S₂'.presheaf.stalk (f₂' y)) (ConcreteCategory.bijective_of_isIso (iS'.stalkMap (f₂' y)))
  have h₁ := (isIso_baseChangeCohomologyMap_iff_ring f g (f₂' ≫ iS') (g₂' ≫ iX) w K E' ψ y n).1 h
  have h₂ := (isIso_ringBaseChangeCohomologyMap_iff_localization
    (R := S.presheaf.stalk (f ((g₂' ≫ iX) y))) (A := X.presheaf.stalk ((g₂' ≫ iX) y))
    (R' := S'.presheaf.stalk ((f₂' ≫ iS') y)) (B := Y.presheaf.stalk y)
    (R₁ := S₂.presheaf.stalk (f₂ (g₂' y))) (A₁ := X₂.presheaf.stalk (g₂' y))
    (R'₁ := S₂'.presheaf.stalk (f₂' y)) ⊥ ⊥ ⊥ hloc hloc₂ _ _ _ n).1 h₁
  refine (isIso_baseChangeCohomologyMap_iff_ring f₂ g₂ f₂' g₂' w₂ _ E' _ y n).2 ?_
  refine (isIso_ringBaseChangeCohomologyMap_iff_of_iso (R := S₂.presheaf.stalk (f₂ (g₂' y)))
    (R' := S₂'.presheaf.stalk (f₂' y)) (A := X₂.presheaf.stalk (g₂' y))
    (A' := Y.presheaf.stalk y) ((derivedPullbackStalkIso iX (g₂' y)).app K) (Iso.refl _)
    _ _ ?_ n).2 h₂
  have hW0 := inv_eq_of_eq_trans_right _ _ _ (derivedPullbackStalkCompIso_eq g₂' iX y)
  have hW1 := congrArg (fun t => NatTrans.app t K) hW0
  refine chase_source _ _ _ _ _ _ _ _ _
    ((totalDerivedExtensionScalars.{u, u, u} (algebraMap (X₂.presheaf.stalk (g₂' y))
      (Y.presheaf.stalk y))).functor.map ((derivedPullbackStalkIso iX (g₂' y)).inv.app K))
    ((derivedPullbackStalkCompIso g₂' iX y).inv.app K)
    rfl (CategoryTheory.Functor.map_comp _ _ _) hW1 ?_ (Iso.hom_inv_id_app _ _)
    ((CategoryTheory.Functor.map_comp _ _ _).symm.trans
      ((congrArg _ (Iso.hom_inv_id_app _ _)).trans (CategoryTheory.Functor.map_id _ _)))
  exact Category.assoc _ _ _

/-- **Condition (1) of Stacks 0DJ8 restricts to opens.**  Let `Y → X₂ → S₂ ← S₂'` be a cartesian
square mapping by open immersions `Y ⟶ X'`, `X₂ ⟶ X`, `S₂ ⟶ S`, `S₂' ⟶ S'` to the cartesian
square `X' → X → S ← S'`.  If the map of Stacks 0DJ7 of the second square at `φ : L(g')^*K ⟶ K'`
is invertible at the image of `y` in degree `n`, so is that of the first square at the datum
pulled back along the morphism of squares. -/
theorem isIso_baseChangeCohomologyMap_pullDatum (sq : IsPullback g' f' f g)
    {f₂ : X₂ ⟶ S₂} {g₂ : S₂' ⟶ S₂} {f₂' : Y ⟶ S₂'} {g₂' : Y ⟶ X₂}
    (sq₂ : IsPullback g₂' f₂' f₂ g₂) (iX : X₂ ⟶ X) (iY : Y ⟶ X') (iS : S₂ ⟶ S) (iS' : S₂' ⟶ S')
    [IsOpenImmersion iX] [IsOpenImmersion iY] [IsOpenImmersion iS] [IsOpenImmersion iS']
    (hg : g₂' ≫ iX = iY ≫ g') (hf : f₂ ≫ iS = iX ≫ f) (hf' : f₂' ≫ iS' = iY ≫ f')
    (hgS : g₂ ≫ iS = iS' ≫ g)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toSheafedSpace)))
    (K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'.toSheafedSpace)))
    (φ : (derivedPullback g'.toLRSHom.toShHom).obj K ⟶ K')
    (y : Y) (n : ℤ) (h : IsIso (baseChangeCohomologyMap f g f' g' sq.w K K' φ (iY y) n)) :
    IsIso (baseChangeCohomologyMap f₂ g₂ f₂' g₂' sq₂.w
      ((derivedPullback iX.toLRSHom.toShHom).obj K) ((derivedPullback iY.toLRSHom.toShHom).obj K')
      (Stacks.Cohomology.BaseChangeCover.pullDatum g₂'.toLRSHom.toShHom iY.toLRSHom.toShHom
        iX.toLRSHom.toShHom g'.toLRSHom.toShHom (comp_toShHom_of_comm hg) K K' φ) y n) := by
  have w₅ : (g₂' ≫ iX) ≫ f = (f₂' ≫ iS') ≫ g := by
    rw [Category.assoc, ← hf, ← Category.assoc, sq₂.w, Category.assoc, hgS, Category.assoc]
  have h₄ := isIso_baseChangeCohomologyMap_comp_left sq iY K K' φ y n h
  have hφ :
      HEq ((derivedPullbackCompIsoCanonical iY.toLRSHom.toShHom g'.toLRSHom.toShHom).inv.app K ≫
        (derivedPullback iY.toLRSHom.toShHom).map φ)
        ((Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft g₂'.toLRSHom.toShHom
          iY.toLRSHom.toShHom iX.toLRSHom.toShHom g'.toLRSHom.toShHom
          (comp_toShHom_of_comm hg)).inv.app K ≫ (derivedPullback iY.toLRSHom.toShHom).map φ) := by
    rw [Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft_inv_app_comp
      g'.toLRSHom.toShHom iX.toLRSHom.toShHom iY.toLRSHom.toShHom g₂'.toLRSHom.toShHom
      (comp_toShHom_of_comm hg) K K' φ]
    exact (eqToHom_comp_heq _ _).symm
  have h₅ := isIso_baseChangeCohomologyMap_congr f g hf'.symm hg.symm _ w₅ K _ _ _ hφ y n h₄
  have hloc₅ := IsStalkLocalization.congr f g hf'.symm hg.symm _ w₅ y
    (IsStalkLocalization.comp_left sq.w iY y (isStalkLocalization_of_isPullback sq (iY y)))
  exact isIso_baseChangeCohomologyMap_restrict_source f g sq₂.w iX iS iS' hf hgS w₅ K _ _ y n
    hloc₅ (isStalkLocalization_of_isPullback sq₂ y) h₅

end AlgebraicGeometry
