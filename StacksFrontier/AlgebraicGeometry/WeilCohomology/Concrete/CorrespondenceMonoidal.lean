module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.TensorCategory
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.TensorComposition
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.TensorDiagonal
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.TensorTransport
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.TensorConstraints
public import StacksFrontier.CategoryTheory.Graded.TwistedKaroubiMonoidal
public import Mathlib.CategoryTheory.Monoidal.Linear

/-!
# The category of correspondences is symmetric monoidal

**Stacks 0FG7.** The tensor product of correspondences `c ⊗ c' = pr₁₃^* c · pr₂₄^* c'` turns the
category of correspondences `Stacks.WeilCohomology.CorrespondenceCategory k` (Stacks 0FG2) into a
symmetric monoidal category with unit `Spec k`: on objects `X ⊗ Y = X × Y`, the associativity
constraint is the usual one of products of schemes and the commutativity constraint is the factor
switch `X × Y ≅ Y × X`, both taken through the graph functor of Stacks 0FG3.

## Main results

* `Stacks.WeilCohomology.CorrespondenceCategory.monoidalCategory` and
  `Stacks.WeilCohomology.CorrespondenceCategory.symmetricCategory`: the category of
  correspondences is symmetric monoidal.
* `Stacks.WeilCohomology.CorrespondenceCategory.isGradedMonoidal` and
  `Stacks.WeilCohomology.CorrespondenceCategory.isGradedBraided`: degrees add under the tensor
  product and the constraints have degree `0`.
* `Stacks.WeilCohomology.CorrespondenceCategory.tensorHom_comp_tensorHom'`: bifunctoriality.
* `Stacks.WeilCohomology.CorrespondenceCategory.tensorHom_graphHom`: the tensor product of the
  graphs of two isomorphisms of smooth projective schemes is the graph of their product.

## Implementation notes

Bifunctoriality is `Stacks.WeilCohomology.comp_tensor`, `𝟙 ⊗ 𝟙 = 𝟙` is
`Stacks.WeilCohomology.tensor_diagonalCorr`, and the naturality of the constraints reduces, by
`Stacks.WeilCohomology.comp_graphCorr_left` and `Stacks.WeilCohomology.comp_graphCorr_right`
(composing with the graph of an isomorphism is transport along it), to the associativity, unit
and commutativity laws of `Stacks.WeilCohomology.tensor` up to transport. The coherence axioms
(pentagon, triangle, hexagons, symmetry) are the images under the graph functor of those of
`(SmoothProjectiveScheme k).FullSubcategory`, since the tensor product of graphs of isomorphisms
is the graph of the product (`tensorHom_graphHom`).

## References

* [Stacks Project, Tag 0FG7](https://stacks.math.columbia.edu/tag/0FG7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Stacks.Chow

universe u

namespace Stacks.WeilCohomology

/-! ### The tensor product of graphs of isomorphisms -/

section Graph

variable (k : Type u) [Field k] {P P' Q Q' : Scheme.{u}}
  (sP : P ⟶ (fieldChowSituation k).S) (sP' : P' ⟶ (fieldChowSituation k).S)
  (sQ : Q ⟶ (fieldChowSituation k).S) (sQ' : Q' ⟶ (fieldChowSituation k).S)
  [Smooth sP] [IsSeparated sP] [IsProper sP] [Smooth sP'] [IsSeparated sP'] [IsProper sP']
  [Smooth sQ] [IsSeparated sQ] [IsProper sQ] [Smooth sQ'] [IsSeparated sQ'] [IsProper sQ']

omit [IsProper sP] in
/-- The graph of an isomorphism is the transport of the diagonal along it. -/
theorem graphCorr_eq_corrEquivOfIso_id (ψ : Q ⟶ P) [IsIso ψ] (hψ : ψ ≫ sP = sQ) :
    graphCorr k sP sQ ψ hψ =
      corrEquivOfIso k sP sQ sQ sQ ψ (𝟙 Q) hψ (Category.id_comp _) 0 (diagonalCorr k sQ) :=
  (graphCorr_congr k sP sQ hψ _ (by simp)).trans
    (graphCorr_eq_corrEquivOfIso k sP sQ sQ ψ hψ (𝟙 Q) (Category.id_comp _))

/-- **The tensor product of the graphs of two isomorphisms is the graph of their product**:
`[Γ_ψ] ⊗ [Γ_ψ'] = [Γ_{ψ × ψ'}]`, for the canonical diagonal classes. -/
theorem tensor_graphCorr_of_isIso (ψ : Q ⟶ P) [IsIso ψ] (hψ : ψ ≫ sP = sQ) (ψ' : Q' ⟶ P')
    [IsIso ψ'] (hψ' : ψ' ≫ sP' = sQ') :
    tensor k sP sP' sQ sQ' (canonicalDiagonalClassFamily k) 0 0 (graphCorr k sP sQ ψ hψ)
        (graphCorr k sP' sQ' ψ' hψ') =
      corrCongr k (prodBase sP sP') (prodBase sQ sQ') (add_zero 0).symm
        (graphCorr k (prodBase sP sP') (prodBase sQ sQ') (prodHom sP sP' sQ sQ' ψ ψ' hψ hψ')
          (prodHom_comp_prodBase _ _ _ _ _ _ _ _)) := by
  rw [graphCorr_eq_corrEquivOfIso_id k sP sQ ψ hψ, graphCorr_eq_corrEquivOfIso_id k sP' sQ' ψ' hψ',
    ← corrEquivOfIso_tensor_canonical k sP sP' sQ sQ' sQ sQ' sQ sQ' ψ ψ' (𝟙 Q) (𝟙 Q') hψ hψ'
      (Category.id_comp _) (Category.id_comp _),
    tensor_diagonalCorr, corrEquivOfIso_corrCongr, graphCorr_eq_corrEquivOfIso_id]
  congr 1
  exact corrEquivOfIso_congr k _ _ _ _ _ _ _ _ rfl
    (prodHom_id sQ sQ') _ _

end Graph


/-! ### Generalized forms, for products given by any equal structure morphism -/

section General

variable (k : Type u) [Field k]

/-- Transport along an equality of degrees does not change a correspondence, up to `HEq`. -/
theorem corrCongr_heq {X Y : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S)
    (sY : Y ⟶ (fieldChowSituation k).S) [Smooth sX] [IsSeparated sX] [Smooth sY] [IsSeparated sY]
    {r r' : ℤ} (h : r = r') (c : Corr k sX sY r) : corrCongr k sX sY h c ≍ c := by
  subst h
  rw [corrCongr_self]

/-- A correspondence equal to the transport of another along an equality of degrees is `HEq` to
it. -/
private theorem heq_of_eq_corrCongr {X Y : Scheme.{u}} {sX : X ⟶ (fieldChowSituation k).S}
    {sY : Y ⟶ (fieldChowSituation k).S} [Smooth sX] [IsSeparated sX] [Smooth sY] [IsSeparated sY]
    {r r' : ℤ} {h : r = r'} {x : Corr k sX sY r'} {y : Corr k sX sY r}
    (e : x = corrCongr k sX sY h y) : x ≍ y :=
  (heq_of_eq e).trans (corrCongr_heq k sX sY h y)

/-- An `HEq` between correspondences of possibly different degrees is an equality up to transport
of degrees. -/
theorem eq_corrCongr_of_heq {X Y : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S)
    (sY : Y ⟶ (fieldChowSituation k).S) [Smooth sX] [IsSeparated sX] [Smooth sY] [IsSeparated sY]
    {r r' : ℤ} (h : r' = r) (x : Corr k sX sY r) (y : Corr k sX sY r') (hxy : x ≍ y) :
    x = corrCongr k sX sY h y := by
  subst h
  rw [corrCongr_self]
  exact eq_of_heq hxy

/-- Composition of correspondences does not depend on the presentation of the three schemes:
equal structure morphisms give `HEq` composites of `HEq` correspondences. -/
theorem comp_heq_comp {XX XX' YY YY' ZZ ZZ' : Scheme.{u}}
    (sXX : XX ⟶ (fieldChowSituation k).S) (sXX' : XX' ⟶ (fieldChowSituation k).S)
    (sYY : YY ⟶ (fieldChowSituation k).S) (sYY' : YY' ⟶ (fieldChowSituation k).S)
    (sZZ : ZZ ⟶ (fieldChowSituation k).S) (sZZ' : ZZ' ⟶ (fieldChowSituation k).S)
    [iX : Smooth sXX] [iX' : Smooth sXX'] [iY : Smooth sYY] [iY' : Smooth sYY']
    [iZ : Smooth sZZ] [iZ' : Smooth sZZ'] [jY : IsProper sYY] [jY' : IsProper sYY']
    (eX : XX = XX') (hX : sXX ≍ sXX') (eY : YY = YY') (hY : sYY ≍ sYY') (eZ : ZZ = ZZ')
    (hZ : sZZ ≍ sZZ') (Δ : DiagonalClassFamily k) (r s : ℤ) (x : Corr k sXX sYY r)
    (x' : Corr k sXX' sYY' r) (hx : x ≍ x') (y : Corr k sYY sZZ s) (y' : Corr k sYY' sZZ' s)
    (hy : y ≍ y') :
    comp k sXX sYY sZZ Δ r s x y ≍ comp k sXX' sYY' sZZ' Δ r s x' y' := by
  subst eX eY eZ
  obtain rfl := eq_of_heq hX
  obtain rfl := eq_of_heq hY
  obtain rfl := eq_of_heq hZ
  obtain rfl : iX = iX' := Subsingleton.elim _ _
  obtain rfl : iY = iY' := Subsingleton.elim _ _
  obtain rfl : iZ = iZ' := Subsingleton.elim _ _
  obtain rfl : jY = jY' := Subsingleton.elim _ _
  obtain rfl := eq_of_heq hx
  obtain rfl := eq_of_heq hy
  rfl

/-- The diagonal correspondence does not depend on the presentation of the scheme. -/
theorem diagonalCorr_heq {XX XX' : Scheme.{u}} (sXX : XX ⟶ (fieldChowSituation k).S)
    (sXX' : XX' ⟶ (fieldChowSituation k).S) [iX : Smooth sXX] [iX' : Smooth sXX']
    [jX : IsSeparated sXX] [jX' : IsSeparated sXX'] [qX : QuasiCompact sXX]
    [qX' : QuasiCompact sXX'] (eX : XX = XX') (hX : sXX ≍ sXX') :
    diagonalCorr k sXX ≍ diagonalCorr k sXX' := by
  subst eX
  obtain rfl := eq_of_heq hX
  obtain rfl : iX = iX' := Subsingleton.elim _ _
  obtain rfl : jX = jX' := Subsingleton.elim _ _
  obtain rfl : qX = qX' := Subsingleton.elim _ _
  rfl

/-- The graph correspondence does not depend on the presentation of the schemes. -/
theorem graphCorr_heq {XX XX' YY YY' : Scheme.{u}} (sXX : XX ⟶ (fieldChowSituation k).S)
    (sXX' : XX' ⟶ (fieldChowSituation k).S) (sYY : YY ⟶ (fieldChowSituation k).S)
    (sYY' : YY' ⟶ (fieldChowSituation k).S) [iX : Smooth sXX] [iX' : Smooth sXX']
    [jX : IsSeparated sXX] [jX' : IsSeparated sXX'] [iY : Smooth sYY] [iY' : Smooth sYY']
    [jY' : IsSeparated sYY'] [qY : QuasiCompact sYY]
    [qY' : QuasiCompact sYY'] (eX : XX = XX') (hX : sXX ≍ sXX') (eY : YY = YY')
    (hY : sYY ≍ sYY') (ψ : YY ⟶ XX) (ψ' : YY' ⟶ XX') (hψ : ψ ≫ sXX = sYY)
    (hψ' : ψ' ≫ sXX' = sYY') (h : ψ ≍ ψ') :
    graphCorr k sXX sYY ψ hψ ≍ graphCorr k sXX' sYY' ψ' hψ' := by
  subst eX eY
  obtain rfl := eq_of_heq hX
  obtain rfl := eq_of_heq hY
  obtain rfl := eq_of_heq h
  obtain rfl : iX = iX' := Subsingleton.elim _ _
  obtain rfl : jX = jX' := Subsingleton.elim _ _
  obtain rfl : iY = iY' := Subsingleton.elim _ _
  obtain rfl : qY = qY' := Subsingleton.elim _ _
  rfl

/-- The tensor product of correspondences does not depend on the presentation of the schemes. -/
theorem tensor_heq {A A' B B' C C' D D' : Scheme.{u}} (sA : A ⟶ (fieldChowSituation k).S)
    (tA : C ⟶ (fieldChowSituation k).S) (sA' : A' ⟶ (fieldChowSituation k).S)
    (tA' : C' ⟶ (fieldChowSituation k).S) (sB : B ⟶ (fieldChowSituation k).S)
    (tB : D ⟶ (fieldChowSituation k).S) (sB' : B' ⟶ (fieldChowSituation k).S)
    (tB' : D' ⟶ (fieldChowSituation k).S)
    [i₁ : Smooth sA] [j₁ : IsSeparated sA] [k₁ : IsProper sA]
    [i₂ : Smooth sA'] [j₂ : IsSeparated sA'] [k₂ : IsProper sA']
    [i₃ : Smooth sB] [j₃ : IsSeparated sB] [k₃ : IsProper sB]
    [i₄ : Smooth sB'] [j₄ : IsSeparated sB'] [k₄ : IsProper sB']
    [i₁' : Smooth tA] [j₁' : IsSeparated tA] [k₁' : IsProper tA]
    [i₂' : Smooth tA'] [j₂' : IsSeparated tA'] [k₂' : IsProper tA']
    [i₃' : Smooth tB] [j₃' : IsSeparated tB] [k₃' : IsProper tB]
    [i₄' : Smooth tB'] [j₄' : IsSeparated tB'] [k₄' : IsProper tB']
    (eA : A = C) (hA : sA ≍ tA) (eA' : A' = C') (hA' : sA' ≍ tA') (eB : B = D) (hB : sB ≍ tB)
    (eB' : B' = D') (hB' : sB' ≍ tB') (Δ : DiagonalClassFamily k) (r r' : ℤ)
    (x : Corr k sA sB r) (x' : Corr k tA tB r) (hx : x ≍ x') (y : Corr k sA' sB' r')
    (y' : Corr k tA' tB' r') (hy : y ≍ y') :
    tensor k sA sA' sB sB' Δ r r' x y ≍ tensor k tA tA' tB tB' Δ r r' x' y' := by
  subst eA eA' eB eB'
  obtain rfl := eq_of_heq hA
  obtain rfl := eq_of_heq hA'
  obtain rfl := eq_of_heq hB
  obtain rfl := eq_of_heq hB'
  congr!
  all_goals exact eq_of_heq ‹_›

/-- Transport of correspondences along isomorphisms does not depend on the presentation of the
schemes. -/
theorem corrEquivOfIso_heq {X X' Y Y' Z Z' W W' : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S)
    (tX : Z ⟶ (fieldChowSituation k).S) (sX' : X' ⟶ (fieldChowSituation k).S)
    (tX' : Z' ⟶ (fieldChowSituation k).S) (sY : Y ⟶ (fieldChowSituation k).S)
    (tY : W ⟶ (fieldChowSituation k).S) (sY' : Y' ⟶ (fieldChowSituation k).S)
    (tY' : W' ⟶ (fieldChowSituation k).S)
    [i₁ : Smooth sX] [i₂ : Smooth sX'] [i₃ : Smooth sY] [i₄ : Smooth sY']
    [i₁' : Smooth tX] [j₁' : IsSeparated tX] [i₂' : Smooth tX'] [j₂' : IsSeparated tX']
    [i₃' : Smooth tY] [j₃' : IsSeparated tY] [i₄' : Smooth tY'] [j₄' : IsSeparated tY']
    (eX : X = Z) (hX : sX ≍ tX) (eX' : X' = Z') (hX' : sX' ≍ tX') (eY : Y = W) (hY : sY ≍ tY)
    (eY' : Y' = W') (hY' : sY' ≍ tY') (φX : X' ⟶ X) [IsIso φX] (φY : Y' ⟶ Y) [IsIso φY]
    (hφX : φX ≫ sX = sX') (hφY : φY ≫ sY = sY') (ψX : Z' ⟶ Z) [IsIso ψX] (ψY : W' ⟶ W)
    [IsIso ψY] (hψX : ψX ≫ tX = tX') (hψY : ψY ≫ tY = tY') (h₁ : φX ≍ ψX) (h₂ : φY ≍ ψY)
    (r : ℤ) (c : Corr k sX' sY' r) (c' : Corr k tX' tY' r) (hc : c ≍ c') :
    corrEquivOfIso k sX sX' sY sY' φX φY hφX hφY r c ≍
      corrEquivOfIso k tX tX' tY tY' ψX ψY hψX hψY r c' := by
  subst eX eX' eY eY'
  obtain rfl := eq_of_heq hX
  obtain rfl := eq_of_heq hX'
  obtain rfl := eq_of_heq hY
  obtain rfl := eq_of_heq hY'
  obtain rfl := eq_of_heq h₁
  obtain rfl := eq_of_heq h₂
  congr!
  all_goals exact eq_of_heq ‹_›

variable {X X' Y Y' Z Z' XX YY ZZ : Scheme.{u}}
  (sX : X ⟶ (fieldChowSituation k).S) (sX' : X' ⟶ (fieldChowSituation k).S)
  (sY : Y ⟶ (fieldChowSituation k).S) (sY' : Y' ⟶ (fieldChowSituation k).S)
  (sZ : Z ⟶ (fieldChowSituation k).S) (sZ' : Z' ⟶ (fieldChowSituation k).S)
  [Smooth sX] [IsSeparated sX] [Smooth sX'] [IsSeparated sX'] [Smooth sY] [IsSeparated sY]
  [Smooth sY'] [IsSeparated sY'] [Smooth sZ] [IsSeparated sZ] [Smooth sZ'] [IsSeparated sZ']
  [IsProper sX] [IsProper sX'] [IsProper sY] [IsProper sY'] [IsProper sZ] [IsProper sZ']
  (sXX : XX ⟶ (fieldChowSituation k).S) (sYY : YY ⟶ (fieldChowSituation k).S)
  (sZZ : ZZ ⟶ (fieldChowSituation k).S) [Smooth sXX] [Smooth sYY] [IsProper sYY] [Smooth sZZ]

/-- `Stacks.WeilCohomology.comp_tensor` for products presented by any structure morphisms equal to
the products of the factors. -/
theorem comp_tensor_heq (eX : XX = Limits.pullback sX sX') (hX : sXX ≍ prodBase sX sX')
    (eY : YY = Limits.pullback sY sY') (hY : sYY ≍ prodBase sY sY')
    (eZ : ZZ = Limits.pullback sZ sZ') (hZ : sZZ ≍ prodBase sZ sZ') (r r' s s' : ℤ)
    (a : Corr k sX sY r) (a' : Corr k sX' sY' r') (b : Corr k sY sZ s) (b' : Corr k sY' sZ' s')
    (x : Corr k sXX sYY (r + r')) (hx : x ≍ tensor k sX sX' sY sY' (canonicalDiagonalClassFamily
        k) r r' a a')
    (y : Corr k sYY sZZ (s + s')) (hy : y ≍ tensor k sY sY' sZ sZ' (canonicalDiagonalClassFamily
        k) s s' b b') :
    comp k sXX sYY sZZ (canonicalDiagonalClassFamily k) (r + r') (s + s') x y ≍
      tensor k sX sX' sZ sZ' (canonicalDiagonalClassFamily k) (r + s) (r' + s') (comp k sX sY sZ
          (canonicalDiagonalClassFamily k) r s a b)
        (comp k sX' sY' sZ' (canonicalDiagonalClassFamily k) r' s' a' b') :=
  ((comp_heq_comp k sXX (prodBase sX sX') sYY (prodBase sY sY') sZZ (prodBase sZ sZ') eX hX eY hY
    eZ hZ (canonicalDiagonalClassFamily k) (r + r') (s + s') x _ hx y _ hy).trans
    (heq_of_eq (comp_tensor k sX sX' sY sY' sZ sZ' r r' s s' a a' b b'))).trans
    (corrCongr_heq k _ _ _ _)

end General

namespace CorrespondenceCategory

variable {k : Type u} [Field k]

/-! ### Homogeneous morphisms -/

/-- Two homogeneous morphisms are equal when their correspondences agree up to the identification
of degrees. -/
theorem of_eq_of_toCorr {X Y : (SmoothProjectiveScheme k).FullSubcategory} {r r' : ℤ} (h : r = r')
    (x : SmoothProjectiveCorr X Y r) (y : SmoothProjectiveCorr X Y r')
    (hxy : SmoothProjectiveCorr.toCorr X Y r x =
      corrCongr k X.obj.hom Y.obj.hom h.symm (SmoothProjectiveCorr.toCorr X Y r' y)) :
    DirectSum.of (fun i ↦ SmoothProjectiveCorr X Y i) r x =
      DirectSum.of (fun i ↦ SmoothProjectiveCorr X Y i) r' y := by
  subst h
  rw [corrCongr_self] at hxy
  exact congrArg _ ((SmoothProjectiveCorr.toCorr X Y r).injective hxy)

/-- Two homogeneous morphisms are equal when their correspondences agree up to `HEq`. -/
theorem of_eq_of_heq {X Y : (SmoothProjectiveScheme k).FullSubcategory} {r r' : ℤ} (h : r = r')
    {x : SmoothProjectiveCorr X Y r} {y : SmoothProjectiveCorr X Y r'} (hxy : x ≍ y) :
    DirectSum.of (fun i ↦ SmoothProjectiveCorr X Y i) r x =
      DirectSum.of (fun i ↦ SmoothProjectiveCorr X Y i) r' y := by
  subst h
  rw [eq_of_heq hxy]

/-- Composition in the category of correspondences is the composition of correspondences. -/
theorem comp_eq_comp {P Q R : (SmoothProjectiveScheme k).FullSubcategory} {r s : ℤ}
    (a : SmoothProjectiveCorr P Q r) (b : SmoothProjectiveCorr Q R s) :
    ((canonicalCorrespondenceCompositionData k).comp a b : Corr k P.obj.hom R.obj.hom (r + s)) =
      comp k P.obj.hom Q.obj.hom R.obj.hom (canonicalDiagonalClassFamily k) r s a b :=
  rfl

/-- The tensor product of homogeneous morphisms is the tensor product of correspondences. -/
theorem tensorCorr_heq {P Q P' Q' : (SmoothProjectiveScheme k).FullSubcategory} {r r' : ℤ}
    (a : SmoothProjectiveCorr P Q r) (a' : SmoothProjectiveCorr P' Q' r') :
    tensorCorr r r' a a' ≍ tensor k P.obj.hom P'.obj.hom Q.obj.hom Q'.obj.hom
        (canonicalDiagonalClassFamily k) r r' a a' :=
  HEq.rfl

/-- The tensor product of two composites, read in the category or on the correspondences. -/
theorem tensor_comp_heq_tensorCorr {P Q R P' Q' R' : (SmoothProjectiveScheme k).FullSubcategory}
    {r s r' s' : ℤ}
    (a : SmoothProjectiveCorr P Q r) (b : SmoothProjectiveCorr Q R s)
    (a' : SmoothProjectiveCorr P' Q' r') (b' : SmoothProjectiveCorr Q' R' s') :
    tensor k P.obj.hom P'.obj.hom R.obj.hom R'.obj.hom (canonicalDiagonalClassFamily k) (r + s)
        (r' + s')
        (comp k P.obj.hom Q.obj.hom R.obj.hom (canonicalDiagonalClassFamily k) r s a b)
        (comp k P'.obj.hom Q'.obj.hom R'.obj.hom (canonicalDiagonalClassFamily k) r' s' a' b') ≍
      tensorCorr (r + s) (r' + s') ((canonicalCorrespondenceCompositionData k).comp a b)
        ((canonicalCorrespondenceCompositionData k).comp a' b') :=
  HEq.rfl

/-- Induction on morphisms of the category of correspondences: they are sums of homogeneous
morphisms. -/
@[elab_as_elim]
theorem hom_induction {X Y : CorrespondenceCategory k} {motive : (X ⟶ Y) → Prop} (f : X ⟶ Y)
    (zero : motive 0) (add : ∀ f g, motive f → motive g → motive (f + g))
    (of : ∀ (r : ℤ) (a : SmoothProjectiveCorr X.as Y.as r),
      motive (DirectSum.of (fun i ↦ SmoothProjectiveCorr X.as Y.as i) r a)) : motive f :=
  DirectSum.induction_on (motive := motive) f zero of add

/-! ### Linearity of the tensor product of morphisms -/

/-- The tensor product of morphisms is additive in the first variable. -/
theorem tensorHom_add_left {X₁ Y₁ X₂ Y₂ : CorrespondenceCategory k} (f f' : X₁ ⟶ Y₁)
    (g : X₂ ⟶ Y₂) : tensorHom (f + f') g = tensorHom f g + tensorHom f' g := by
  simp only [tensorHom, map_add, LinearMap.add_apply]

/-- The tensor product of morphisms is additive in the second variable. -/
theorem tensorHom_add_right {X₁ Y₁ X₂ Y₂ : CorrespondenceCategory k} (f : X₁ ⟶ Y₁)
    (g g' : X₂ ⟶ Y₂) : tensorHom f (g + g') = tensorHom f g + tensorHom f g' := by
  simp only [tensorHom, map_add]

/-- The tensor product of the zero morphism with any morphism is zero. -/
theorem tensorHom_zero_left {X₁ Y₁ X₂ Y₂ : CorrespondenceCategory k} (g : X₂ ⟶ Y₂) :
    tensorHom (0 : X₁ ⟶ Y₁) g = 0 := by
  simp only [tensorHom, map_zero, LinearMap.zero_apply]

/-- The tensor product of any morphism with the zero morphism is zero. -/
theorem tensorHom_zero_right {X₁ Y₁ X₂ Y₂ : CorrespondenceCategory k} (f : X₁ ⟶ Y₁) :
    tensorHom f (0 : X₂ ⟶ Y₂) = 0 := by
  simp only [tensorHom, map_zero]

/-! ### Bifunctoriality -/

/-- Bifunctoriality on homogeneous morphisms. -/
theorem of_tensorHom_comp_of {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : CorrespondenceCategory k} {r r' s s' : ℤ}
    (a : SmoothProjectiveCorr X₁.as Y₁.as r) (a' : SmoothProjectiveCorr X₂.as Y₂.as r')
    (b : SmoothProjectiveCorr Y₁.as Z₁.as s) (b' : SmoothProjectiveCorr Y₂.as Z₂.as s') :
    tensorHom (X₁ := X₁) (Y₁ := Y₁) (X₂ := X₂) (Y₂ := Y₂)
        (DirectSum.of (fun i ↦ SmoothProjectiveCorr X₁.as Y₁.as i) r a)
        (DirectSum.of (fun i ↦ SmoothProjectiveCorr X₂.as Y₂.as i) r' a') ≫
      tensorHom (X₁ := Y₁) (Y₁ := Z₁) (X₂ := Y₂) (Y₂ := Z₂)
        (DirectSum.of (fun i ↦ SmoothProjectiveCorr Y₁.as Z₁.as i) s b)
        (DirectSum.of (fun i ↦ SmoothProjectiveCorr Y₂.as Z₂.as i) s' b') =
      tensorHom (X₁ := X₁) (Y₁ := Z₁) (X₂ := X₂) (Y₂ := Z₂)
        (DirectSum.of (fun i ↦ SmoothProjectiveCorr X₁.as Y₁.as i) r a ≫
          DirectSum.of (fun i ↦ SmoothProjectiveCorr Y₁.as Z₁.as i) s b)
        (DirectSum.of (fun i ↦ SmoothProjectiveCorr X₂.as Y₂.as i) r' a' ≫
          DirectSum.of (fun i ↦ SmoothProjectiveCorr Y₂.as Z₂.as i) s' b') := by
  rw [tensorHom_of_of, tensorHom_of_of, GradedCompositionData.of_comp_of,
    GradedCompositionData.of_comp_of, GradedCompositionData.of_comp_of, tensorHom_of_of]
  refine of_eq_of_heq (by ring) ?_
  rw [comp_eq_comp (tensorCorr r r' a a') (tensorCorr s s' b b')]
  have h := comp_tensor_heq k X₁.as.obj.hom X₂.as.obj.hom Y₁.as.obj.hom Y₂.as.obj.hom
    Z₁.as.obj.hom Z₂.as.obj.hom (X₁.as ⊗ X₂.as).obj.hom (Y₁.as ⊗ Y₂.as).obj.hom
    (Z₁.as ⊗ Z₂.as).obj.hom rfl HEq.rfl rfl HEq.rfl rfl HEq.rfl r r' s s' a a' b b'
    (tensorCorr r r' a a') (tensorCorr_heq a a') (tensorCorr s s' b b') (tensorCorr_heq b b')
  exact h.trans (tensor_comp_heq_tensorCorr a b a' b')

/-- Bifunctoriality, with the last argument arbitrary. -/
theorem of_tensorHom_comp_tensorHom {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : CorrespondenceCategory k} {r r' s : ℤ}
    (a : SmoothProjectiveCorr X₁.as Y₁.as r) (a' : SmoothProjectiveCorr X₂.as Y₂.as r')
    (b : SmoothProjectiveCorr Y₁.as Z₁.as s) (g₂ : Y₂ ⟶ Z₂) :
    tensorHom (X₁ := X₁) (Y₁ := Y₁) (X₂ := X₂) (Y₂ := Y₂)
        (DirectSum.of (fun i ↦ SmoothProjectiveCorr X₁.as Y₁.as i) r a)
        (DirectSum.of (fun i ↦ SmoothProjectiveCorr X₂.as Y₂.as i) r' a') ≫
      tensorHom (X₁ := Y₁) (Y₁ := Z₁) (X₂ := Y₂) (Y₂ := Z₂)
        (DirectSum.of (fun i ↦ SmoothProjectiveCorr Y₁.as Z₁.as i) s b) g₂ =
      tensorHom (X₁ := X₁) (Y₁ := Z₁) (X₂ := X₂) (Y₂ := Z₂)
        (DirectSum.of (fun i ↦ SmoothProjectiveCorr X₁.as Y₁.as i) r a ≫
          DirectSum.of (fun i ↦ SmoothProjectiveCorr Y₁.as Z₁.as i) s b)
        (DirectSum.of (fun i ↦ SmoothProjectiveCorr X₂.as Y₂.as i) r' a' ≫ g₂) := by
  induction g₂ using hom_induction with
  | zero => simp only [tensorHom_zero_right, Limits.comp_zero]
  | add g g' hg hg' => simp only [tensorHom_add_right, Preadditive.comp_add, hg, hg']
  | of s' b' => exact of_tensorHom_comp_of a a' b b'

/-- Bifunctoriality, with the last two arguments arbitrary. -/
theorem of_tensorHom_comp {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : CorrespondenceCategory k} {r r' : ℤ}
    (a : SmoothProjectiveCorr X₁.as Y₁.as r) (a' : SmoothProjectiveCorr X₂.as Y₂.as r')
    (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) :
    tensorHom (X₁ := X₁) (Y₁ := Y₁) (X₂ := X₂) (Y₂ := Y₂)
        (DirectSum.of (fun i ↦ SmoothProjectiveCorr X₁.as Y₁.as i) r a)
        (DirectSum.of (fun i ↦ SmoothProjectiveCorr X₂.as Y₂.as i) r' a') ≫ tensorHom g₁ g₂ =
      tensorHom (DirectSum.of (fun i ↦ SmoothProjectiveCorr X₁.as Y₁.as i) r a ≫ g₁)
        (DirectSum.of (fun i ↦ SmoothProjectiveCorr X₂.as Y₂.as i) r' a' ≫ g₂) := by
  induction g₁ using hom_induction with
  | zero => simp only [tensorHom_zero_left, Limits.comp_zero]
  | add g g' hg hg' =>
    simp only [tensorHom_add_left, Preadditive.comp_add, hg, hg']
  | of s b => exact of_tensorHom_comp_tensorHom a a' b g₂

/-- Bifunctoriality, with the last three arguments arbitrary. -/
theorem of_tensorHom_comp' {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : CorrespondenceCategory k} {r : ℤ}
    (a : SmoothProjectiveCorr X₁.as Y₁.as r) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) :
    tensorHom (X₁ := X₁) (Y₁ := Y₁) (DirectSum.of (fun i ↦ SmoothProjectiveCorr X₁.as Y₁.as i) r a)
        f₂ ≫ tensorHom g₁ g₂ =
      tensorHom (DirectSum.of (fun i ↦ SmoothProjectiveCorr X₁.as Y₁.as i) r a ≫ g₁) (f₂ ≫ g₂) := by
  induction f₂ using hom_induction with
  | zero => simp only [tensorHom_zero_right, Limits.zero_comp]
  | add f f' hf hf' =>
    simp only [tensorHom_add_right, Preadditive.add_comp, hf, hf']
  | of r' a' => exact of_tensorHom_comp a a' g₁ g₂

/-- **Bifunctoriality of the tensor product of correspondences** (Stacks 0FG7):
`(f₁ ⊗ f₂) ≫ (g₁ ⊗ g₂) = (f₁ ≫ g₁) ⊗ (f₂ ≫ g₂)`. -/
theorem tensorHom_comp_tensorHom' {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : CorrespondenceCategory k} (f₁ : X₁ ⟶ Y₁)
    (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) :
    tensorHom f₁ f₂ ≫ tensorHom g₁ g₂ = tensorHom (f₁ ≫ g₁) (f₂ ≫ g₂) := by
  induction f₁ using hom_induction with
  | zero => simp only [tensorHom_zero_left, Limits.zero_comp]
  | add f f' hf hf' => simp only [tensorHom_add_left, Preadditive.add_comp, hf, hf']
  | of r a => exact of_tensorHom_comp' a f₂ g₁ g₂

/-! ### Graphs -/

/-- An isomorphism of smooth projective schemes is an isomorphism of the underlying schemes. -/
theorem isIso_hom_left_of_isIso {P Q : (SmoothProjectiveScheme k).FullSubcategory} (u : Q ⟶ P)
    [IsIso u] :
    IsIso u.hom.left :=
  (ObjectProperty.ι _ ⋙ Over.forget _).map_isIso u

/-- The forward map of an isomorphism of smooth projective schemes is an isomorphism of the
underlying schemes. -/
instance isIso_iso_hom_hom_left {P Q : (SmoothProjectiveScheme k).FullSubcategory} (e : P ≅ Q) :
    IsIso e.hom.hom.left :=
  isIso_hom_left_of_isIso e.hom

/-- The inverse map of an isomorphism of smooth projective schemes is an isomorphism of the
underlying schemes. -/
instance isIso_iso_inv_hom_left {P Q : (SmoothProjectiveScheme k).FullSubcategory} (e : P ≅ Q) :
    IsIso e.inv.hom.left :=
  isIso_hom_left_of_isIso e.inv

/-- The graph class of a morphism of smooth projective schemes is the graph correspondence. -/
theorem graphCorrespondenceSP_eq {P Q : (SmoothProjectiveScheme k).FullSubcategory} (u : Q ⟶ P) :
    (graphCorrespondenceSP u : Corr k P.obj.hom Q.obj.hom 0) =
      graphCorr k P.obj.hom Q.obj.hom u.hom.left (Over.w u.hom) :=
  rfl

/-- **The tensor product of the graphs of two isomorphisms is the graph of their tensor
product.** -/
theorem tensorHom_graphHom {P Q P' Q' : (SmoothProjectiveScheme k).FullSubcategory} (u : Q ⟶ P)
    (v : Q' ⟶ P')
    [IsIso u] [IsIso v] :
    tensorHom (X₁ := GradedCompositionData.Obj.mk P) (Y₁ := GradedCompositionData.Obj.mk Q)
        (X₂ := GradedCompositionData.Obj.mk P') (Y₂ := GradedCompositionData.Obj.mk Q')
        (graphHom u) (graphHom v) = graphHom (u ⊗ₘ v) := by
  have := isIso_hom_left_of_isIso u
  have := isIso_hom_left_of_isIso v
  rw [graphHom, graphHom, graphHom, tensorHom_of_of]
  refine of_eq_of_heq (add_zero 0) ?_
  dsimp only
  refine (tensorCorr_heq _ _).trans ?_
  have t : tensor k P.obj.hom P'.obj.hom Q.obj.hom Q'.obj.hom (canonicalDiagonalClassFamily k) 0 0
      (graphCorrespondenceSP u) (graphCorrespondenceSP v) =
      corrCongr k (prodBase P.obj.hom P'.obj.hom) (prodBase Q.obj.hom Q'.obj.hom) (add_zero 0).symm
        (graphCorr k (prodBase P.obj.hom P'.obj.hom) (prodBase Q.obj.hom Q'.obj.hom)
          (prodHom P.obj.hom P'.obj.hom Q.obj.hom Q'.obj.hom u.hom.left v.hom.left (Over.w u.hom)
            (Over.w v.hom)) (prodHom_comp_prodBase _ _ _ _ _ _ _ _)) :=
    tensor_graphCorr_of_isIso k P.obj.hom P'.obj.hom Q.obj.hom Q'.obj.hom
      u.hom.left (Over.w u.hom) v.hom.left (Over.w v.hom)
  refine (heq_of_eq_corrCongr k t).trans ?_
  refine (graphCorr_heq k _ (P ⊗ P').obj.hom _ (Q ⊗ Q').obj.hom rfl HEq.rfl rfl HEq.rfl _
    (u ⊗ₘ v).hom.left _ (Over.w (u ⊗ₘ v).hom) HEq.rfl).trans ?_
  exact heq_of_eq (graphCorrespondenceSP_eq (u ⊗ₘ v)).symm

/-! ### Composing with the graphs of isomorphisms -/

/-- On underlying schemes, the forward map of an isomorphism followed by its inverse is the
identity. -/
theorem hom_hom_left_comp_inv_hom_left {P Q : (SmoothProjectiveScheme k).FullSubcategory}
    (e : P ≅ Q) :
    e.hom.hom.left ≫ e.inv.hom.left = 𝟙 _ := by
  rw [← Over.comp_left, ← ObjectProperty.FullSubcategory.comp_hom, e.hom_inv_id]; rfl

/-- On underlying schemes, the inverse map of an isomorphism followed by its forward map is the
identity. -/
theorem inv_hom_left_comp_hom_hom_left {P Q : (SmoothProjectiveScheme k).FullSubcategory}
    (e : P ≅ Q) :
    e.inv.hom.left ≫ e.hom.hom.left = 𝟙 _ := by
  rw [← Over.comp_left, ← ObjectProperty.FullSubcategory.comp_hom, e.inv_hom_id]; rfl

/-- **Naturality with respect to graphs of isomorphisms**: for isomorphisms `e : P ≅ P'` and
`e' : Q ≅ Q'` of smooth projective schemes and homogeneous morphisms `a : P ⟶ Q`, `b : P' ⟶ Q'`,
if the transport of `a` along `e × e'` is `b`, then `a ≫ [Γ_{e'}] = [Γ_e] ≫ b`. -/
theorem of_comp_graphIso {P P' Q Q' : (SmoothProjectiveScheme k).FullSubcategory} (e : P ≅ P')
    (e' : Q ≅ Q')
    (φ : P.obj.left ⟶ P'.obj.left) [iφ : IsIso φ] (hφ : e.hom.hom.left = φ)
    (φ' : Q.obj.left ⟶ Q'.obj.left) [iφ' : IsIso φ'] (hφ' : e'.hom.hom.left = φ')
    (wφ : φ ≫ P'.obj.hom = P.obj.hom) (wφ' : φ' ≫ Q'.obj.hom = Q.obj.hom)
    {r r' : ℤ} (h : r = r') (a : SmoothProjectiveCorr P Q r) (b : SmoothProjectiveCorr P' Q' r')
    (hab : corrEquivOfIso k P'.obj.hom P.obj.hom Q'.obj.hom Q.obj.hom φ φ' wφ wφ' r a ≍ b) :
    (DirectSum.of (fun i ↦ SmoothProjectiveCorr P Q i) r a :
        (GradedCompositionData.Obj.mk P : CorrespondenceCategory k) ⟶
          GradedCompositionData.Obj.mk Q) ≫ (graphIso e').hom =
      (graphIso e).hom ≫ (DirectSum.of (fun i ↦ SmoothProjectiveCorr P' Q' i) r' b :
        (GradedCompositionData.Obj.mk P' : CorrespondenceCategory k) ⟶
          GradedCompositionData.Obj.mk Q') := by
  subst h hφ hφ'
  obtain rfl : iφ = isIso_iso_hom_hom_left e := Subsingleton.elim _ _
  obtain rfl : iφ' = isIso_iso_hom_hom_left e' := Subsingleton.elim _ _
  rw [graphIso_hom, graphIso_hom, graphHom, graphHom,
    GradedCompositionData.of_comp_of (canonicalCorrespondenceCompositionData k)
      (X := GradedCompositionData.Obj.mk P)
      (Y := GradedCompositionData.Obj.mk Q) (Z := GradedCompositionData.Obj.mk Q') a
      (graphCorrespondenceSP e'.inv),
    GradedCompositionData.of_comp_of (canonicalCorrespondenceCompositionData k)
      (X := GradedCompositionData.Obj.mk P)
      (Y := GradedCompositionData.Obj.mk P') (Z := GradedCompositionData.Obj.mk Q')
      (graphCorrespondenceSP e.inv) b]
  refine of_eq_of_heq (by omega) ?_
  dsimp only
  rw [comp_eq_comp a (graphCorrespondenceSP e'.inv), graphCorrespondenceSP_eq,
    comp_eq_comp (graphCorrespondenceSP e.inv), graphCorrespondenceSP_eq,
    comp_graphCorr_right k P.obj.hom Q.obj.hom Q'.obj.hom
      (canonicalDiagonalClassFamily_properIntersectionFormula k)
      (canonicalDiagonalClassFamily_isoInvariant k) e'.inv.hom.left (Over.w e'.inv.hom) r a,
    comp_graphCorr_left k P.obj.hom P'.obj.hom Q'.obj.hom
      (canonicalDiagonalClassFamily_properIntersectionFormula k)
      (canonicalDiagonalClassFamily_isoInvariant k) e.inv.hom.left (Over.w e.inv.hom) r b]
  refine (corrCongr_heq k _ _ _ _).trans (HEq.trans ?_ (corrCongr_heq k _ _ _ _).symm)
  rw [← eq_of_heq hab]
  refine heq_of_eq ((corrEquivOfIso_congr k _ _ _ _ _ _ _ _
    (hom_hom_left_comp_inv_hom_left e).symm ?_ r a).trans
    (corrEquivOfIso_trans k P.obj.hom P'.obj.hom P.obj.hom Q'.obj.hom Q'.obj.hom Q.obj.hom
      e.inv.hom.left (𝟙 _) (Over.w e.inv.hom) (Category.id_comp _) e.hom.hom.left
      e'.hom.hom.left (Over.w e.hom.hom) (Over.w e'.hom.hom) r a).symm)
  rw [Category.comp_id]
  exact IsIso.inv_eq_of_hom_inv_id (inv_hom_left_comp_hom_hom_left e')

/-! ### Naturality of the constraints -/

/-- Naturality of the commutativity constraint on homogeneous morphisms. -/
theorem of_tensorHom_braiding {P₁ Q₁ P₂ Q₂ : (SmoothProjectiveScheme k).FullSubcategory} {r r' : ℤ}
    (a : SmoothProjectiveCorr P₁ Q₁ r) (b : SmoothProjectiveCorr P₂ Q₂ r') :
    (DirectSum.of (fun i ↦ SmoothProjectiveCorr (P₁ ⊗ P₂) (Q₁ ⊗ Q₂) i) (r + r')
        (tensorCorr r r' a b) :
        (GradedCompositionData.Obj.mk (P₁ ⊗ P₂) : CorrespondenceCategory k) ⟶
          GradedCompositionData.Obj.mk (Q₁ ⊗ Q₂)) ≫ (graphIso (β_ Q₁ Q₂)).hom =
      (graphIso (β_ P₁ P₂)).hom ≫
        (DirectSum.of (fun i ↦ SmoothProjectiveCorr (P₂ ⊗ P₁) (Q₂ ⊗ Q₁) i) (r' + r)
          (tensorCorr r' r b a) :
          (GradedCompositionData.Obj.mk (P₂ ⊗ P₁) : CorrespondenceCategory k) ⟶
            GradedCompositionData.Obj.mk (Q₂ ⊗ Q₁)) := by
  have hab : corrEquivOfIso k (P₂ ⊗ P₁).obj.hom (P₁ ⊗ P₂).obj.hom (Q₂ ⊗ Q₁).obj.hom
      (Q₁ ⊗ Q₂).obj.hom (Limits.pullbackSymmetry P₁.obj.hom P₂.obj.hom).hom
      (Limits.pullbackSymmetry Q₁.obj.hom Q₂.obj.hom).hom (Over.w (β_ P₁ P₂).hom.hom)
      (Over.w (β_ Q₁ Q₂).hom.hom) (r + r') (tensorCorr r r' a b) ≍ tensorCorr r' r b a := by
    refine (corrEquivOfIso_heq k (P₂ ⊗ P₁).obj.hom (prodBase P₂.obj.hom P₁.obj.hom)
    (P₁ ⊗ P₂).obj.hom (prodBase P₁.obj.hom P₂.obj.hom) (Q₂ ⊗ Q₁).obj.hom
    (prodBase Q₂.obj.hom Q₁.obj.hom) (Q₁ ⊗ Q₂).obj.hom (prodBase Q₁.obj.hom Q₂.obj.hom) rfl
        HEq.rfl rfl HEq.rfl rfl HEq.rfl rfl HEq.rfl
    (Limits.pullbackSymmetry P₁.obj.hom P₂.obj.hom).hom
    (Limits.pullbackSymmetry Q₁.obj.hom Q₂.obj.hom).hom _ _
    (Limits.pullbackSymmetry P₁.obj.hom P₂.obj.hom).hom
    (Limits.pullbackSymmetry Q₁.obj.hom Q₂.obj.hom).hom
    (pullbackSymmetry_hom_comp_base _ _) (pullbackSymmetry_hom_comp_base _ _) HEq.rfl HEq.rfl
    (r + r') _ _ (tensorCorr_heq a b)).trans ?_
    exact (heq_of_eq_corrCongr k (corrEquivOfIso_tensor_swap k P₁.obj.hom P₂.obj.hom Q₁.obj.hom
      Q₂.obj.hom r r' a b)).trans (tensorCorr_heq b a).symm
  have h1 : (β_ P₁ P₂).hom.hom.left = (Limits.pullbackSymmetry P₁.obj.hom P₂.obj.hom).hom := rfl
  have h2 : (β_ Q₁ Q₂).hom.hom.left = (Limits.pullbackSymmetry Q₁.obj.hom Q₂.obj.hom).hom := rfl
  have key := of_comp_graphIso (β_ P₁ P₂) (β_ Q₁ Q₂) _ h1 _ h2
    (Over.w (β_ P₁ P₂).hom.hom) (Over.w (β_ Q₁ Q₂).hom.hom) (add_comm r r')
    (tensorCorr r r' a b) (tensorCorr r' r b a) hab
  convert key using 0

/-- The correspondence `[Δ]` of the category of correspondences is the diagonal correspondence. -/
theorem correspondenceDiagonal_heq (P : (SmoothProjectiveScheme k).FullSubcategory) :
    correspondenceDiagonal k P ≍ diagonalCorr k P.obj.hom :=
  HEq.rfl

section Assoc

variable {P₁ P₂ P₃ Q₁ Q₂ Q₃ : (SmoothProjectiveScheme k).FullSubcategory} {r₁ r₂ r₃ : ℤ}
  (a₁ : SmoothProjectiveCorr P₁ Q₁ r₁) (a₂ : SmoothProjectiveCorr P₂ Q₂ r₂)
  (a₃ : SmoothProjectiveCorr P₃ Q₃ r₃)

/-- `(a₁ ⊗ a₂) ⊗ a₃`, read on the fibre products. -/
theorem tensorCorr_tensorCorr_heq_left :
    tensorCorr (r₁ + r₂) r₃ (tensorCorr r₁ r₂ a₁ a₂) a₃ ≍
      tensor k (prodBase P₁.obj.hom P₂.obj.hom) P₃.obj.hom (prodBase Q₁.obj.hom Q₂.obj.hom)
        Q₃.obj.hom (canonicalDiagonalClassFamily k) (r₁ + r₂) r₃
        (tensor k P₁.obj.hom P₂.obj.hom Q₁.obj.hom Q₂.obj.hom (canonicalDiagonalClassFamily k) r₁
            r₂ a₁ a₂) a₃ :=
  (tensorCorr_heq _ _).trans (tensor_heq k (P₁ ⊗ P₂).obj.hom (prodBase P₁.obj.hom P₂.obj.hom)
    P₃.obj.hom P₃.obj.hom (Q₁ ⊗ Q₂).obj.hom (prodBase Q₁.obj.hom Q₂.obj.hom) Q₃.obj.hom
    Q₃.obj.hom rfl HEq.rfl rfl HEq.rfl rfl HEq.rfl rfl HEq.rfl _ (r₁ + r₂) r₃
    (tensorCorr r₁ r₂ a₁ a₂) _ (tensorCorr_heq a₁ a₂) a₃ a₃ HEq.rfl)

/-- `a₁ ⊗ (a₂ ⊗ a₃)`, read on the fibre products. -/
theorem tensorCorr_tensorCorr_heq_right :
    tensorCorr r₁ (r₂ + r₃) a₁ (tensorCorr r₂ r₃ a₂ a₃) ≍
      tensor k P₁.obj.hom (prodBase P₂.obj.hom P₃.obj.hom) Q₁.obj.hom
        (prodBase Q₂.obj.hom Q₃.obj.hom) (canonicalDiagonalClassFamily k) r₁ (r₂ + r₃) a₁
        (tensor k P₂.obj.hom P₃.obj.hom Q₂.obj.hom Q₃.obj.hom (canonicalDiagonalClassFamily k) r₂
            r₃ a₂ a₃) :=
  (tensorCorr_heq _ _).trans (tensor_heq k P₁.obj.hom P₁.obj.hom (P₂ ⊗ P₃).obj.hom
    (prodBase P₂.obj.hom P₃.obj.hom) Q₁.obj.hom Q₁.obj.hom (Q₂ ⊗ Q₃).obj.hom
    (prodBase Q₂.obj.hom Q₃.obj.hom) rfl HEq.rfl rfl HEq.rfl rfl HEq.rfl rfl HEq.rfl _ r₁
    (r₂ + r₃) a₁ a₁ HEq.rfl (tensorCorr r₂ r₃ a₂ a₃) _ (tensorCorr_heq a₂ a₃))

/-- The associativity constraint of smooth projective schemes, on the fibre products. -/
abbrev assocLeft (P₁ P₂ P₃ : (SmoothProjectiveScheme k).FullSubcategory) :
    Limits.pullback (prodBase P₁.obj.hom P₂.obj.hom) P₃.obj.hom ⟶
      Limits.pullback P₁.obj.hom (prodBase P₂.obj.hom P₃.obj.hom) :=
  (α_ P₁ P₂ P₃).hom.hom.left

/-- The associativity constraint on the fibre products is an isomorphism. -/
instance (P₁ P₂ P₃ : (SmoothProjectiveScheme k).FullSubcategory) : IsIso (assocLeft P₁ P₂ P₃) :=
  isIso_iso_hom_hom_left (α_ P₁ P₂ P₃)

/-- The first projection after `assocLeft` is the first projection of the first factor. -/
theorem assocLeft_fst (P₁ P₂ P₃ : (SmoothProjectiveScheme k).FullSubcategory) :
    assocLeft P₁ P₂ P₃ ≫ Limits.pullback.fst _ _ =
      Limits.pullback.fst _ _ ≫ Limits.pullback.fst _ _ :=
  Over.associator_hom_left_fst P₁.obj P₂.obj P₃.obj

/-- The middle projection after `assocLeft` is the second projection of the first factor. -/
theorem assocLeft_snd_fst (P₁ P₂ P₃ : (SmoothProjectiveScheme k).FullSubcategory) :
    assocLeft P₁ P₂ P₃ ≫ Limits.pullback.snd _ _ ≫ Limits.pullback.fst _ _ =
      Limits.pullback.fst _ _ ≫ Limits.pullback.snd _ _ :=
  Over.associator_hom_left_snd_fst P₁.obj P₂.obj P₃.obj

/-- The last projection after `assocLeft` is the second projection. -/
theorem assocLeft_snd_snd (P₁ P₂ P₃ : (SmoothProjectiveScheme k).FullSubcategory) :
    assocLeft P₁ P₂ P₃ ≫ Limits.pullback.snd _ _ ≫ Limits.pullback.snd _ _ =
      Limits.pullback.snd _ _ :=
  Over.associator_hom_left_snd_snd P₁.obj P₂.obj P₃.obj

/-- Transport of `(a₁ ⊗ a₂) ⊗ a₃` along the associativity constraints is `a₁ ⊗ (a₂ ⊗ a₃)`. -/
theorem corrEquivOfIso_assocLeft_tensorCorr :
    corrEquivOfIso k (P₁ ⊗ (P₂ ⊗ P₃)).obj.hom ((P₁ ⊗ P₂) ⊗ P₃).obj.hom
      (Q₁ ⊗ (Q₂ ⊗ Q₃)).obj.hom ((Q₁ ⊗ Q₂) ⊗ Q₃).obj.hom (assocLeft P₁ P₂ P₃) (assocLeft Q₁ Q₂ Q₃)
      (Over.w (α_ P₁ P₂ P₃).hom.hom) (Over.w (α_ Q₁ Q₂ Q₃).hom.hom) (r₁ + r₂ + r₃)
      (tensorCorr (r₁ + r₂) r₃ (tensorCorr r₁ r₂ a₁ a₂) a₃) ≍
        tensorCorr r₁ (r₂ + r₃) a₁ (tensorCorr r₂ r₃ a₂ a₃) := by
  refine (corrEquivOfIso_heq k (P₁ ⊗ (P₂ ⊗ P₃)).obj.hom
    (prodBase P₁.obj.hom (prodBase P₂.obj.hom P₃.obj.hom)) ((P₁ ⊗ P₂) ⊗ P₃).obj.hom
    (prodBase (prodBase P₁.obj.hom P₂.obj.hom) P₃.obj.hom) (Q₁ ⊗ (Q₂ ⊗ Q₃)).obj.hom
    (prodBase Q₁.obj.hom (prodBase Q₂.obj.hom Q₃.obj.hom)) ((Q₁ ⊗ Q₂) ⊗ Q₃).obj.hom
    (prodBase (prodBase Q₁.obj.hom Q₂.obj.hom) Q₃.obj.hom) rfl HEq.rfl rfl HEq.rfl rfl HEq.rfl
    rfl HEq.rfl _ _ _ _ (assocLeft P₁ P₂ P₃) (assocLeft Q₁ Q₂ Q₃)
    (assocHom_comp_prodBase _ _ _ _ (assocLeft_fst P₁ P₂ P₃))
    (assocHom_comp_prodBase _ _ _ _ (assocLeft_fst Q₁ Q₂ Q₃)) HEq.rfl HEq.rfl _ _ _
    (tensorCorr_tensorCorr_heq_left a₁ a₂ a₃)).trans ?_
  refine (heq_of_eq (corrEquivOfIso_tensor_tensor k P₁.obj.hom P₂.obj.hom P₃.obj.hom
    Q₁.obj.hom Q₂.obj.hom Q₃.obj.hom (assocLeft P₁ P₂ P₃) (assocLeft_fst P₁ P₂ P₃)
    (assocLeft_snd_fst P₁ P₂ P₃) (assocLeft_snd_snd P₁ P₂ P₃) (assocLeft Q₁ Q₂ Q₃)
    (assocLeft_fst Q₁ Q₂ Q₃) (assocLeft_snd_fst Q₁ Q₂ Q₃) (assocLeft_snd_snd Q₁ Q₂ Q₃) r₁ r₂ r₃
    a₁ a₂ a₃)).trans ?_
  refine (corrCongr_heq k _ _ _ _).trans ?_
  convert (tensorCorr_tensorCorr_heq_right a₁ a₂ a₃).symm using 2

/-- Naturality of the associativity constraint on homogeneous morphisms. -/
theorem of_tensorHom_associator :
    (DirectSum.of (fun i ↦ SmoothProjectiveCorr ((P₁ ⊗ P₂) ⊗ P₃) ((Q₁ ⊗ Q₂) ⊗ Q₃) i)
        (r₁ + r₂ + r₃) (tensorCorr (r₁ + r₂) r₃ (tensorCorr r₁ r₂ a₁ a₂) a₃) :
        (GradedCompositionData.Obj.mk ((P₁ ⊗ P₂) ⊗ P₃) : CorrespondenceCategory k) ⟶
          GradedCompositionData.Obj.mk ((Q₁ ⊗ Q₂) ⊗ Q₃)) ≫ (graphIso (α_ Q₁ Q₂ Q₃)).hom =
      (graphIso (α_ P₁ P₂ P₃)).hom ≫
        (DirectSum.of (fun i ↦ SmoothProjectiveCorr (P₁ ⊗ (P₂ ⊗ P₃)) (Q₁ ⊗ (Q₂ ⊗ Q₃)) i)
          (r₁ + (r₂ + r₃)) (tensorCorr r₁ (r₂ + r₃) a₁ (tensorCorr r₂ r₃ a₂ a₃)) :
          (GradedCompositionData.Obj.mk (P₁ ⊗ (P₂ ⊗ P₃)) : CorrespondenceCategory k) ⟶
            GradedCompositionData.Obj.mk (Q₁ ⊗ (Q₂ ⊗ Q₃))) := by
  have key := of_comp_graphIso (α_ P₁ P₂ P₃) (α_ Q₁ Q₂ Q₃) (assocLeft P₁ P₂ P₃) rfl
    (assocLeft Q₁ Q₂ Q₃) rfl (Over.w (α_ P₁ P₂ P₃).hom.hom) (Over.w (α_ Q₁ Q₂ Q₃).hom.hom)
    (add_assoc r₁ r₂ r₃) _ _ (corrEquivOfIso_assocLeft_tensorCorr a₁ a₂ a₃)
  convert key using 0

end Assoc

/-- Naturality of the left unit constraint on homogeneous morphisms. -/
theorem of_tensorHom_leftUnitor {P Q : (SmoothProjectiveScheme k).FullSubcategory} {r : ℤ}
    (a : SmoothProjectiveCorr P Q r) :
    (DirectSum.of (fun i ↦ SmoothProjectiveCorr (𝟙_ _ ⊗ P) (𝟙_ _ ⊗ Q) i) (0 + r)
        (tensorCorr 0 r
            (correspondenceDiagonal k (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory))) a) :
        (GradedCompositionData.Obj.mk (𝟙_ _ ⊗ P) : CorrespondenceCategory k) ⟶
          GradedCompositionData.Obj.mk (𝟙_ _ ⊗ Q)) ≫ (graphIso (λ_ Q)).hom =
      (graphIso (λ_ P)).hom ≫
        (DirectSum.of (fun i ↦ SmoothProjectiveCorr P Q i) r a :
          (GradedCompositionData.Obj.mk P : CorrespondenceCategory k) ⟶
            GradedCompositionData.Obj.mk Q) := by
  have hab : corrEquivOfIso k P.obj.hom (𝟙_ _ ⊗ P).obj.hom Q.obj.hom (𝟙_ _ ⊗ Q).obj.hom
      (Limits.pullback.snd (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom P.obj.hom)
      (Limits.pullback.snd (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom Q.obj.hom)
      (Over.w (λ_ P).hom.hom) (Over.w (λ_ Q).hom.hom) (0 + r)
      (tensorCorr 0 r
          (correspondenceDiagonal k (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory))) a) ≍ a := by
    refine (corrEquivOfIso_heq k P.obj.hom P.obj.hom (𝟙_ _ ⊗ P).obj.hom
      (prodBase (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom P.obj.hom) Q.obj.hom
          Q.obj.hom
      (𝟙_ _ ⊗ Q).obj.hom
          (prodBase (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom Q.obj.hom) rfl
          HEq.rfl rfl HEq.rfl rfl
      HEq.rfl rfl HEq.rfl _ _ _ _ _ _ Limits.pullback.condition.symm
      Limits.pullback.condition.symm HEq.rfl HEq.rfl _ _ _
      ((tensorCorr_heq _ _).trans
          (tensor_heq k (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom
        (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom P.obj.hom P.obj.hom
        (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom
            (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom
        Q.obj.hom Q.obj.hom rfl HEq.rfl rfl HEq.rfl rfl HEq.rfl rfl HEq.rfl _ 0 r _
        (diagonalCorr k (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom)
            (correspondenceDiagonal_heq _)
        a a HEq.rfl))).trans ?_
    exact heq_of_eq_corrCongr k (corrEquivOfIso_tensor_diagonalCorr_left k P.obj.hom Q.obj.hom
      (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom r a)
  have key := of_comp_graphIso (λ_ P) (λ_ Q) _ rfl _ rfl (Over.w (λ_ P).hom.hom)
    (Over.w (λ_ Q).hom.hom) (zero_add r) _ _ hab
  convert key using 0

/-- Naturality of the right unit constraint on homogeneous morphisms. -/
theorem of_tensorHom_rightUnitor {P Q : (SmoothProjectiveScheme k).FullSubcategory} {r : ℤ}
    (a : SmoothProjectiveCorr P Q r) :
    (DirectSum.of (fun i ↦ SmoothProjectiveCorr (P ⊗ 𝟙_ _) (Q ⊗ 𝟙_ _) i) (r + 0)
        (tensorCorr r 0 a
            (correspondenceDiagonal k (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)))) :
        (GradedCompositionData.Obj.mk (P ⊗ 𝟙_ _) : CorrespondenceCategory k) ⟶
          GradedCompositionData.Obj.mk (Q ⊗ 𝟙_ _)) ≫ (graphIso (ρ_ Q)).hom =
      (graphIso (ρ_ P)).hom ≫
        (DirectSum.of (fun i ↦ SmoothProjectiveCorr P Q i) r a :
          (GradedCompositionData.Obj.mk P : CorrespondenceCategory k) ⟶
            GradedCompositionData.Obj.mk Q) := by
  have hab : corrEquivOfIso k P.obj.hom (P ⊗ 𝟙_ _).obj.hom Q.obj.hom (Q ⊗ 𝟙_ _).obj.hom
      (Limits.pullback.fst P.obj.hom (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom)
      (Limits.pullback.fst Q.obj.hom (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom)
      (Over.w (ρ_ P).hom.hom) (Over.w (ρ_ Q).hom.hom) (r + 0)
      (tensorCorr r 0 a
          (correspondenceDiagonal k (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)))) ≍ a := by
    refine (corrEquivOfIso_heq k P.obj.hom P.obj.hom (P ⊗ 𝟙_ _).obj.hom
      (prodBase P.obj.hom (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom) Q.obj.hom
          Q.obj.hom
      (Q ⊗ 𝟙_ _).obj.hom
          (prodBase Q.obj.hom (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom) rfl
          HEq.rfl rfl HEq.rfl rfl
      HEq.rfl rfl HEq.rfl _ _ _ _ _ _ rfl rfl HEq.rfl HEq.rfl _ _ _
      ((tensorCorr_heq _ _).trans (tensor_heq k P.obj.hom P.obj.hom
        (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom
            (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom
        Q.obj.hom Q.obj.hom (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom
        (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom rfl HEq.rfl rfl HEq.rfl rfl
            HEq.rfl rfl HEq.rfl
        _ r 0 a a HEq.rfl _
            (diagonalCorr k (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom)
        (correspondenceDiagonal_heq _)))).trans ?_
    exact heq_of_eq_corrCongr k (corrEquivOfIso_tensor_diagonalCorr_right k P.obj.hom Q.obj.hom
      (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom r a)
  have key := of_comp_graphIso (ρ_ P) (ρ_ Q) _ rfl _ rfl (Over.w (ρ_ P).hom.hom)
    (Over.w (ρ_ Q).hom.hom) (add_zero r) _ _ hab
  convert key using 0

/-! ### The identities -/

/-- **`𝟙 ⊗ 𝟙 = 𝟙`** in the category of correspondences. -/
theorem id_tensorHom_id (X₁ X₂ : CorrespondenceCategory k) :
    tensorHom (𝟙 X₁) (𝟙 X₂) = 𝟙 (tensorObj X₁ X₂) := by
  rw [GradedCompositionData.id_eq, GradedCompositionData.id_eq, GradedCompositionData.id_eq,
    tensorHom_of_of]
  refine of_eq_of_heq (add_zero 0) ?_
  refine (tensorCorr_heq _ _).trans ?_
  refine (heq_of_eq_corrCongr k (tensor_diagonalCorr k X₁.as.obj.hom X₂.as.obj.hom)).trans ?_
  exact diagonalCorr_heq k _ (X₁.as ⊗ X₂.as).obj.hom rfl HEq.rfl

/-! ### Naturality of the constraints for arbitrary morphisms -/

section Naturality

variable {P₁ P₂ P₃ Q₁ Q₂ Q₃ : (SmoothProjectiveScheme k).FullSubcategory}

local notation "𝐎" =>
    (GradedCompositionData.Obj.mk : ObjectProperty.FullSubcategory (SmoothProjectiveScheme k) →
  CorrespondenceCategory k)

/-- Naturality of the associativity constraint, with the first two morphisms homogeneous. -/
theorem associator_naturality_of_of_of {r₁ r₂ : ℤ} (a₁ : SmoothProjectiveCorr P₁ Q₁ r₁)
    (a₂ : SmoothProjectiveCorr P₂ Q₂ r₂) (f₃ : 𝐎 P₃ ⟶ 𝐎 Q₃) :
    tensorHom (tensorHom (X₁ := 𝐎 P₁) (Y₁ := 𝐎 Q₁) (X₂ := 𝐎 P₂) (Y₂ := 𝐎 Q₂)
        (DirectSum.of (fun i ↦ SmoothProjectiveCorr P₁ Q₁ i) r₁ a₁)
        (DirectSum.of (fun i ↦ SmoothProjectiveCorr P₂ Q₂ i) r₂ a₂)) f₃ ≫
      (associatorIso (𝐎 Q₁) (𝐎 Q₂) (𝐎 Q₃)).hom =
      (associatorIso (𝐎 P₁) (𝐎 P₂) (𝐎 P₃)).hom ≫
        tensorHom (X₁ := 𝐎 P₁) (Y₁ := 𝐎 Q₁)
          (DirectSum.of (fun i ↦ SmoothProjectiveCorr P₁ Q₁ i) r₁ a₁)
          (tensorHom (X₁ := 𝐎 P₂) (Y₁ := 𝐎 Q₂)
            (DirectSum.of (fun i ↦ SmoothProjectiveCorr P₂ Q₂ i) r₂ a₂) f₃) := by
  induction f₃ using hom_induction with
  | zero => simp only [tensorHom_zero_right, Limits.zero_comp, Limits.comp_zero]
  | add f g hf hg =>
    simp only [tensorHom_add_right, Preadditive.add_comp, Preadditive.comp_add, hf, hg]
  | of r₃ a₃ =>
    rw [tensorHom_of_of, tensorHom_of_of, tensorHom_of_of, tensorHom_of_of]
    convert of_tensorHom_associator a₁ a₂ a₃ using 0

/-- Naturality of the associativity constraint, with the first morphism homogeneous. -/
theorem associator_naturality_of {r₁ : ℤ} (a₁ : SmoothProjectiveCorr P₁ Q₁ r₁)
    (f₂ : 𝐎 P₂ ⟶ 𝐎 Q₂) (f₃ : 𝐎 P₃ ⟶ 𝐎 Q₃) :
    tensorHom (tensorHom (X₁ := 𝐎 P₁) (Y₁ := 𝐎 Q₁)
        (DirectSum.of (fun i ↦ SmoothProjectiveCorr P₁ Q₁ i) r₁ a₁) f₂) f₃ ≫
      (associatorIso (𝐎 Q₁) (𝐎 Q₂) (𝐎 Q₃)).hom =
      (associatorIso (𝐎 P₁) (𝐎 P₂) (𝐎 P₃)).hom ≫
        tensorHom (X₁ := 𝐎 P₁) (Y₁ := 𝐎 Q₁)
          (DirectSum.of (fun i ↦ SmoothProjectiveCorr P₁ Q₁ i) r₁ a₁) (tensorHom f₂ f₃) := by
  induction f₂ using hom_induction with
  | zero =>
    simp only [tensorHom_zero_right, tensorHom_zero_left, Limits.zero_comp, Limits.comp_zero]
  | add f g hf hg =>
    simp only [tensorHom_add_right, tensorHom_add_left, Preadditive.add_comp,
      Preadditive.comp_add, hf, hg]
  | of r₂ a₂ => convert associator_naturality_of_of_of a₁ a₂ f₃ using 0

/-- Naturality of the associativity constraint. -/
theorem associator_naturality' (f₁ : 𝐎 P₁ ⟶ 𝐎 Q₁) (f₂ : 𝐎 P₂ ⟶ 𝐎 Q₂) (f₃ : 𝐎 P₃ ⟶ 𝐎 Q₃) :
    tensorHom (tensorHom f₁ f₂) f₃ ≫ (associatorIso (𝐎 Q₁) (𝐎 Q₂) (𝐎 Q₃)).hom =
      (associatorIso (𝐎 P₁) (𝐎 P₂) (𝐎 P₃)).hom ≫ tensorHom f₁ (tensorHom f₂ f₃) := by
  induction f₁ using hom_induction with
  | zero =>
    simp only [tensorHom_zero_left, Limits.zero_comp, Limits.comp_zero]
  | add f g hf hg =>
    simp only [tensorHom_add_left, Preadditive.add_comp, Preadditive.comp_add, hf, hg]
  | of r₁ a₁ => convert associator_naturality_of a₁ f₂ f₃ using 0

/-- The diagonal of the composition data of correspondences is `correspondenceDiagonal`. -/
theorem diagonal_eq (P : (SmoothProjectiveScheme k).FullSubcategory) :
    (canonicalCorrespondenceCompositionData k).diagonal P = correspondenceDiagonal k P :=
  rfl

/-- Naturality of the left unit constraint. -/
theorem leftUnitor_naturality' (f : 𝐎 P₁ ⟶ 𝐎 Q₁) :
    tensorHom (𝟙 tensorUnit) f ≫ (leftUnitorIso (𝐎 Q₁)).hom = (leftUnitorIso (𝐎 P₁)).hom ≫ f := by
  induction f using hom_induction with
  | zero => simp only [tensorHom_zero_right, Limits.zero_comp, Limits.comp_zero]
  | add f g hf hg =>
    simp only [tensorHom_add_right, Preadditive.add_comp, Preadditive.comp_add, hf, hg]
  | of r a =>
    rw [GradedCompositionData.id_eq, tensorHom_of_of]
    dsimp only [tensorUnit, leftUnitorIso]
    rw [diagonal_eq]
    convert of_tensorHom_leftUnitor a using 0

/-- Naturality of the right unit constraint. -/
theorem rightUnitor_naturality' (f : 𝐎 P₁ ⟶ 𝐎 Q₁) :
    tensorHom f (𝟙 tensorUnit) ≫ (rightUnitorIso (𝐎 Q₁)).hom =
      (rightUnitorIso (𝐎 P₁)).hom ≫ f := by
  induction f using hom_induction with
  | zero => simp only [tensorHom_zero_left, Limits.zero_comp, Limits.comp_zero]
  | add f g hf hg =>
    simp only [tensorHom_add_left, Preadditive.add_comp, Preadditive.comp_add, hf, hg]
  | of r a =>
    rw [GradedCompositionData.id_eq, tensorHom_of_of]
    dsimp only [tensorUnit, rightUnitorIso]
    rw [diagonal_eq]
    convert of_tensorHom_rightUnitor a using 0

/-- Naturality of the commutativity constraint, with the first morphism homogeneous. -/
theorem braiding_naturality_of {r₁ : ℤ} (a₁ : SmoothProjectiveCorr P₁ Q₁ r₁)
    (f₂ : 𝐎 P₂ ⟶ 𝐎 Q₂) :
    tensorHom (X₁ := 𝐎 P₁) (Y₁ := 𝐎 Q₁)
        (DirectSum.of (fun i ↦ SmoothProjectiveCorr P₁ Q₁ i) r₁ a₁) f₂ ≫
      (braidingIso (𝐎 Q₁) (𝐎 Q₂)).hom =
      (braidingIso (𝐎 P₁) (𝐎 P₂)).hom ≫ tensorHom (X₂ := 𝐎 P₁) (Y₂ := 𝐎 Q₁) f₂
        (DirectSum.of (fun i ↦ SmoothProjectiveCorr P₁ Q₁ i) r₁ a₁) := by
  induction f₂ using hom_induction with
  | zero =>
    simp only [tensorHom_zero_right, tensorHom_zero_left, Limits.zero_comp, Limits.comp_zero]
  | add f g hf hg =>
    simp only [tensorHom_add_right, tensorHom_add_left, Preadditive.add_comp,
      Preadditive.comp_add, hf, hg]
  | of r₂ a₂ =>
    rw [tensorHom_of_of, tensorHom_of_of]
    convert of_tensorHom_braiding a₁ a₂ using 0

/-- Naturality of the commutativity constraint. -/
theorem braiding_naturality' (f₁ : 𝐎 P₁ ⟶ 𝐎 Q₁) (f₂ : 𝐎 P₂ ⟶ 𝐎 Q₂) :
    tensorHom f₁ f₂ ≫ (braidingIso (𝐎 Q₁) (𝐎 Q₂)).hom =
      (braidingIso (𝐎 P₁) (𝐎 P₂)).hom ≫ tensorHom f₂ f₁ := by
  induction f₁ using hom_induction with
  | zero =>
    simp only [tensorHom_zero_right, tensorHom_zero_left, Limits.zero_comp, Limits.comp_zero]
  | add f g hf hg =>
    simp only [tensorHom_add_right, tensorHom_add_left, Preadditive.add_comp,
      Preadditive.comp_add, hf, hg]
  | of r₁ a₁ => convert braiding_naturality_of a₁ f₂ using 0

end Naturality

/-! ### Coherence, through the graph functor -/

section Coherence

local notation "𝐎" =>
    (GradedCompositionData.Obj.mk : ObjectProperty.FullSubcategory (SmoothProjectiveScheme k) →
  CorrespondenceCategory k)

/-- The composite of the graphs of `f` and `g` is the graph of `g ≫ f`. -/
theorem graphHom_comp' {P Q R : (SmoothProjectiveScheme k).FullSubcategory} (f : Q ⟶ P)
    (g : R ⟶ Q) :
    (graphHom f : 𝐎 P ⟶ 𝐎 Q) ≫ (graphHom g : 𝐎 Q ⟶ 𝐎 R) = graphHom (g ≫ f) :=
  graphHom_comp f g

/-- The identity correspondence is the graph of the identity. -/
theorem id_eq_graphHom (P : (SmoothProjectiveScheme k).FullSubcategory) :
    𝟙 (𝐎 P) = graphHom (𝟙 P) :=
  (graphHom_id P).symm

/-- The pentagon identity for the associativity constraint of correspondences. -/
theorem pentagon' (W X Y Z : (SmoothProjectiveScheme k).FullSubcategory) :
    tensorHom (associatorIso (𝐎 W) (𝐎 X) (𝐎 Y)).hom (𝟙 (𝐎 Z)) ≫
        (associatorIso (𝐎 W) (tensorObj (𝐎 X) (𝐎 Y)) (𝐎 Z)).hom ≫
          tensorHom (𝟙 (𝐎 W)) (associatorIso (𝐎 X) (𝐎 Y) (𝐎 Z)).hom =
      (associatorIso (tensorObj (𝐎 W) (𝐎 X)) (𝐎 Y) (𝐎 Z)).hom ≫
        (associatorIso (𝐎 W) (𝐎 X) (tensorObj (𝐎 Y) (𝐎 Z))).hom := by
  simp only [graphIso_hom, id_eq_graphHom, tensorHom_graphHom]
  rw [graphHom_comp', graphHom_comp', graphHom_comp']
  congr 1
  simp only [id_tensorHom, tensorHom_id, Category.assoc]
  exact pentagon_inv (W := W) (X := X) (Y := Y) (Z := Z)

/-- The triangle identity for the associativity and unit constraints of correspondences. -/
theorem triangle' (X Y : (SmoothProjectiveScheme k).FullSubcategory) :
    (associatorIso (𝐎 X) tensorUnit (𝐎 Y)).hom ≫ tensorHom (𝟙 (𝐎 X)) (leftUnitorIso (𝐎 Y)).hom =
      tensorHom (rightUnitorIso (𝐎 X)).hom (𝟙 (𝐎 Y)) := by
  simp only [graphIso_hom, id_eq_graphHom, tensorHom_graphHom]
  rw [graphHom_comp']
  congr 1
  simp only [id_tensorHom, tensorHom_id]
  rw [← triangle_assoc_comp_right_inv, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The first hexagon identity for the constraints of correspondences. -/
theorem hexagon_forward' (X Y Z : (SmoothProjectiveScheme k).FullSubcategory) :
    (associatorIso (𝐎 X) (𝐎 Y) (𝐎 Z)).hom ≫ (braidingIso (𝐎 X) (tensorObj (𝐎 Y) (𝐎 Z))).hom ≫
        (associatorIso (𝐎 Y) (𝐎 Z) (𝐎 X)).hom =
      tensorHom (braidingIso (𝐎 X) (𝐎 Y)).hom (𝟙 (𝐎 Z)) ≫
        (associatorIso (𝐎 Y) (𝐎 X) (𝐎 Z)).hom ≫
          tensorHom (𝟙 (𝐎 Y)) (braidingIso (𝐎 X) (𝐎 Z)).hom := by
  simp only [graphIso_hom, id_eq_graphHom, tensorHom_graphHom]
  rw [graphHom_comp', graphHom_comp', graphHom_comp', graphHom_comp']
  congr 1
  simp only [id_tensorHom, tensorHom_id, Category.assoc]
  exact BraidedCategory.hexagon_forward_inv X Y Z

/-- The second hexagon identity for the constraints of correspondences. -/
theorem hexagon_reverse' (X Y Z : (SmoothProjectiveScheme k).FullSubcategory) :
    (associatorIso (𝐎 X) (𝐎 Y) (𝐎 Z)).inv ≫ (braidingIso (tensorObj (𝐎 X) (𝐎 Y)) (𝐎 Z)).hom ≫
        (associatorIso (𝐎 Z) (𝐎 X) (𝐎 Y)).inv =
      tensorHom (𝟙 (𝐎 X)) (braidingIso (𝐎 Y) (𝐎 Z)).hom ≫
        (associatorIso (𝐎 X) (𝐎 Z) (𝐎 Y)).inv ≫
          tensorHom (braidingIso (𝐎 X) (𝐎 Z)).hom (𝟙 (𝐎 Y)) := by
  simp only [graphIso_hom, graphIso_inv, id_eq_graphHom, tensorHom_graphHom]
  rw [graphHom_comp', graphHom_comp', graphHom_comp', graphHom_comp']
  congr 1
  simp only [id_tensorHom, tensorHom_id, Category.assoc]
  exact BraidedCategory.hexagon_reverse_inv X Y Z

/-- The commutativity constraint of correspondences is its own inverse. -/
theorem symmetry' (X Y : (SmoothProjectiveScheme k).FullSubcategory) :
    (braidingIso (𝐎 X) (𝐎 Y)).hom ≫ (braidingIso (𝐎 Y) (𝐎 X)).hom = 𝟙 (tensorObj (𝐎 X) (𝐎 Y)) := by
  simp only [graphIso_hom, id_eq_graphHom]
  rw [graphHom_comp']
  congr 1
  rw [← SymmetricCategory.braiding_swap_eq_inv_braiding X Y,
    ← SymmetricCategory.braiding_swap_eq_inv_braiding Y X, SymmetricCategory.symmetry]

end Coherence

/-! ### The symmetric monoidal structure -/

/-- The data of the monoidal structure on the category of correspondences: `X ⊗ Y = X × Y`, the
tensor product of correspondences, unit `Spec k`, and the graphs of the constraints of products
of schemes. -/
instance monoidalCategoryStruct : MonoidalCategoryStruct (CorrespondenceCategory k) where
  tensorObj := tensorObj
  whiskerLeft X _ _ f := tensorHom (𝟙 X) f
  whiskerRight f Y := tensorHom f (𝟙 Y)
  tensorHom := tensorHom
  tensorUnit := tensorUnit
  associator := associatorIso
  leftUnitor := leftUnitorIso
  rightUnitor := rightUnitorIso

/-- The monoidal product of objects is `tensorObj`. -/
theorem tensorObj_eq (X Y : CorrespondenceCategory k) : X ⊗ Y = tensorObj X Y :=
  rfl

/-- The monoidal unit is `tensorUnit`. -/
theorem tensorUnit_eq : 𝟙_ (CorrespondenceCategory k) = tensorUnit :=
  rfl

/-- The monoidal product of morphisms is `tensorHom`. -/
theorem tensorHom_eq {X₁ Y₁ X₂ Y₂ : CorrespondenceCategory k} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    f ⊗ₘ g = tensorHom f g :=
  rfl

/-- Left whiskering by `X` is the tensor product with `𝟙 X`. -/
theorem whiskerLeft_eq (X : CorrespondenceCategory k) {Y₁ Y₂ : CorrespondenceCategory k}
    (f : Y₁ ⟶ Y₂) : X ◁ f = tensorHom (𝟙 X) f :=
  rfl

/-- Right whiskering by `Y` is the tensor product with `𝟙 Y`. -/
theorem whiskerRight_eq {X₁ X₂ : CorrespondenceCategory k} (f : X₁ ⟶ X₂)
    (Y : CorrespondenceCategory k) : f ▷ Y = tensorHom f (𝟙 Y) :=
  rfl

/-- The associator is `associatorIso`. -/
theorem associator_eq (X Y Z : CorrespondenceCategory k) : α_ X Y Z = associatorIso X Y Z :=
  rfl

/-- The left unitor is `leftUnitorIso`. -/
theorem leftUnitor_eq (X : CorrespondenceCategory k) : λ_ X = leftUnitorIso X :=
  rfl

/-- The right unitor is `rightUnitorIso`. -/
theorem rightUnitor_eq (X : CorrespondenceCategory k) : ρ_ X = rightUnitorIso X :=
  rfl

/-- **Stacks Project, Tag 0FG7** (monoidal structure). The tensor product of correspondences
`c ⊗ c' = pr₁₃^* c · pr₂₄^* c'` turns the category of correspondences between smooth projective
schemes over `k` (Stacks 0FG2) into a monoidal category, with `X ⊗ Y = X × Y`, unit `Spec k`, and
as associativity constraint the usual associativity constraint of products of schemes (taken
through the graph functor of Stacks 0FG3). -/
@[stacks 0FG7]
instance monoidalCategory : MonoidalCategory (CorrespondenceCategory k) :=
  .ofTensorHom
    (id_tensorHom_id := fun X₁ X₂ ↦ id_tensorHom_id X₁ X₂)
    (id_tensorHom := fun _ _ _ _ ↦ rfl)
    (tensorHom_id := fun _ _ ↦ rfl)
    (tensorHom_comp_tensorHom := fun f₁ f₂ g₁ g₂ ↦ tensorHom_comp_tensorHom' f₁ f₂ g₁ g₂)
    (associator_naturality := by
      rintro ⟨P₁⟩ ⟨P₂⟩ ⟨P₃⟩ ⟨Q₁⟩ ⟨Q₂⟩ ⟨Q₃⟩ f₁ f₂ f₃
      simp only [tensorHom_eq, associator_eq, tensorObj_eq]
      exact associator_naturality' f₁ f₂ f₃)
    (leftUnitor_naturality := by
      rintro ⟨P⟩ ⟨Q⟩ f
      simp only [tensorHom_eq, leftUnitor_eq, tensorUnit_eq, tensorObj_eq]
      exact leftUnitor_naturality' f)
    (rightUnitor_naturality := by
      rintro ⟨P⟩ ⟨Q⟩ f
      simp only [tensorHom_eq, rightUnitor_eq, tensorUnit_eq, tensorObj_eq]
      exact rightUnitor_naturality' f)
    (pentagon := by
      rintro ⟨W⟩ ⟨X⟩ ⟨Y⟩ ⟨Z⟩
      simp only [tensorHom_eq, associator_eq, tensorObj_eq]
      exact pentagon' W X Y Z)
    (triangle := by
      rintro ⟨X⟩ ⟨Y⟩
      simp only [tensorHom_eq, associator_eq, leftUnitor_eq, rightUnitor_eq, tensorUnit_eq,
        tensorObj_eq]
      exact triangle' X Y)

/-- The braiding of the category of correspondences: the graph of the factor switch
`X × Y ≅ Y × X`. -/
instance braidedCategory : BraidedCategory (CorrespondenceCategory k) where
  braiding := braidingIso
  braiding_naturality_right := by
    rintro ⟨P⟩ ⟨Q₁⟩ ⟨Q₂⟩ f
    simp only [tensorObj_eq, whiskerLeft_eq, whiskerRight_eq]
    exact braiding_naturality' (𝟙 _) f
  braiding_naturality_left := by
    rintro ⟨P₁⟩ ⟨P₂⟩ f ⟨Q⟩
    simp only [tensorObj_eq, whiskerLeft_eq, whiskerRight_eq]
    exact braiding_naturality' f (𝟙 _)
  hexagon_forward := by
    rintro ⟨X⟩ ⟨Y⟩ ⟨Z⟩
    simp only [associator_eq, tensorObj_eq, whiskerLeft_eq, whiskerRight_eq]
    exact hexagon_forward' X Y Z
  hexagon_reverse := by
    rintro ⟨X⟩ ⟨Y⟩ ⟨Z⟩
    simp only [associator_eq, tensorObj_eq, whiskerLeft_eq, whiskerRight_eq]
    exact hexagon_reverse' X Y Z

/-- The braiding is `braidingIso`. -/
theorem braiding_eq (X Y : CorrespondenceCategory k) : β_ X Y = braidingIso X Y :=
  rfl

/-- **Stacks Project, Tag 0FG7.** The tensor product of correspondences
`c ⊗ c' = pr₁₃^* c · pr₂₄^* c'` turns the category of correspondences between smooth projective
schemes over `k` (Stacks 0FG2) into a symmetric monoidal category with unit `Spec k`: the
associativity constraint is the usual associativity constraint on products of schemes and the
commutativity constraint is the isomorphism `X × Y ⟶ Y × X` switching the factors, both taken
through the graph functor of Stacks 0FG3. -/
@[stacks 0FG7]
instance symmetricCategory : SymmetricCategory (CorrespondenceCategory k) where
  symmetry := by
    rintro ⟨X⟩ ⟨Y⟩
    simp only [tensorObj_eq]
    exact symmetry' X Y

/-! ### Degrees -/

/-- The monoidal structure of the category of correspondences is graded: the tensor product of
correspondences of degrees `r` and `s` has degree `r + s`, and the associativity and unit
constraints have degree `0`. -/
instance isGradedMonoidal : GradedCategory.IsGradedMonoidal ℚ (CorrespondenceCategory k) where
  tensorHom_mem hf hg := tensorHom_mem_grade hf hg
  associator_hom_mem X Y Z := graphIso_hom_mem_grade (α_ X.as Y.as Z.as)
  associator_inv_mem X Y Z := graphIso_inv_mem_grade (α_ X.as Y.as Z.as)
  leftUnitor_hom_mem X := graphIso_hom_mem_grade (λ_ X.as)
  leftUnitor_inv_mem X := graphIso_inv_mem_grade (λ_ X.as)
  rightUnitor_hom_mem X := graphIso_hom_mem_grade (ρ_ X.as)
  rightUnitor_inv_mem X := graphIso_inv_mem_grade (ρ_ X.as)

/-- The commutativity constraint of the category of correspondences has degree `0`. -/
instance isGradedBraided : GradedCategory.IsGradedBraided ℚ (CorrespondenceCategory k) where
  braiding_hom_mem X Y := graphIso_hom_mem_grade (β_ X.as Y.as)
  braiding_inv_mem X Y := graphIso_inv_mem_grade (β_ X.as Y.as)

/-! ### Additivity and `ℚ`-linearity of the tensor product -/

/-- The tensor product of morphisms is `ℚ`-linear in the first variable. -/
theorem tensorHom_smul_left {X₁ Y₁ X₂ Y₂ : CorrespondenceCategory k} (c : ℚ) (f : X₁ ⟶ Y₁)
    (g : X₂ ⟶ Y₂) : tensorHom (c • f) g = c • tensorHom f g := by
  simp only [tensorHom, map_smul, LinearMap.smul_apply]

/-- The tensor product of morphisms is `ℚ`-linear in the second variable. -/
theorem tensorHom_smul_right {X₁ Y₁ X₂ Y₂ : CorrespondenceCategory k} (c : ℚ) (f : X₁ ⟶ Y₁)
    (g : X₂ ⟶ Y₂) : tensorHom f (c • g) = c • tensorHom f g := by
  simp only [tensorHom, map_smul]

/-- The tensor product of correspondences is additive in each variable. -/
instance monoidalPreadditive : MonoidalPreadditive (CorrespondenceCategory k) where
  whiskerLeft_zero := by
    intros
    rw [whiskerLeft_eq, tensorHom_zero_right]
  zero_whiskerRight := by
    intros
    rw [whiskerRight_eq, tensorHom_zero_left]
  whiskerLeft_add := by
    intros
    rw [whiskerLeft_eq, whiskerLeft_eq, whiskerLeft_eq, tensorHom_add_right]
  add_whiskerRight := by
    intros
    rw [whiskerRight_eq, whiskerRight_eq, whiskerRight_eq, tensorHom_add_left]

/-- The tensor product of correspondences is `ℚ`-bilinear. -/
instance monoidalLinear : MonoidalLinear ℚ (CorrespondenceCategory k) where
  whiskerLeft_smul := by
    intros
    rw [whiskerLeft_eq, whiskerLeft_eq, tensorHom_smul_right]
  smul_whiskerRight := by
    intros
    rw [whiskerRight_eq, whiskerRight_eq, tensorHom_smul_left]

end CorrespondenceCategory

end Stacks.WeilCohomology

end
