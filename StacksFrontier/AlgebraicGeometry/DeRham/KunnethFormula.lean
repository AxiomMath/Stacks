module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksFrontier.AlgebraicGeometry.DeRham.BoxTotalKunnethIsomorphism
public import StacksFrontier.AlgebraicGeometry.DeRham.Kunneth
import StacksCore.Tactic.StacksAttribute

/-!
# The de Rham Künneth formula

Let `a : X ⟶ S` and `b : Y ⟶ S` be morphisms of schemes with `S = Spec A` affine, let
`W = X ×_S Y` with projections `p` and `q` and structure morphism `f = p ∘ a = q ∘ b`. The de
Rham complexes `Ω^•_{X/S}` and `Ω^•_{Y/S}` are `ℕ`-indexed complexes in the categories of
finite-order differential operators on `X/S` and on `Y/S`; extended by zero to `ℤ`-indexed
complexes they are inputs for the Künneth map of [Stacks, Tag 0FLR] and for its invertibility
[Stacks, Tag 0FLT]. This file assembles from those and from [Stacks, Tag 0FMA] the de Rham
Künneth map

`RΓ(X, Ω^•_{X/S}) ⊗^𝐋_A RΓ(Y, Ω^•_{Y/S}) ⟶ RΓ(X ×_S Y, Ω^•_{X ×_S Y/S})`

of [Stacks, Tag 0FMB], and proves it invertible on the three inputs that [Stacks, Tag 0FLT]
carries in this repository.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.deRhamDiffOpCochainComplex`: the relative de Rham complex
  `Ω^•_{X/S}` extended by zero to a `ℤ`-indexed complex of finite-order differential operators,
  which is the indexing the box product and the derived category use.
* `AlgebraicGeometry.Scheme.Hom.deRhamBoxTotalExtendIso`: **the isomorphism of `ℤ`-indexed
  complexes `Tot(Ω^•_{X/S} ⊠ Ω^•_{Y/S}) ≅ Ω^•_{X ×_S Y/S}`**, both sides formed from the
  extensions by zero. This is [Stacks, Tag 0FMA] transported across the extension by zero: the
  `ℤ`-indexed total complex of the box product of the two extensions is the extension of the
  `ℕ`-indexed total complex, and the latter is `Ω^•_{W/S}` by Tag 0FMA.
* `Stacks.Cohomology.BoxKunneth.deRhamGlobalKunnethMap`: **the de Rham Künneth map** of
  [Stacks, Tag 0FMB], the global Künneth map of [Stacks, Tag 0FLR] at the two de Rham complexes
  followed by derived global sections of that isomorphism.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isIso_deRhamBoxTotalRestrictionf` and
  `AlgebraicGeometry.Scheme.Hom.isIso_deRhamBoxTotalExtendHom`: in each degree the comparison of
  the `ℤ`-indexed total complex with the extension of the `ℕ`-indexed one is invertible, so the
  comparison of complexes is.
* `Stacks.Cohomology.BoxKunneth.isIso_deRhamGlobalKunnethMap`: **[Stacks, Tag 0FMB]**, granted
  the three inputs of [Stacks, Tag 0FLT].

## Implementation notes

*The `ℕ`-to-`ℤ` comparison of the total complexes.* `Ω^•_{X/S}` is `ℕ`-indexed, the de Rham
complex of a morphism of schemes being concentrated in nonnegative degrees, while the Künneth
maps of [Stacks, Tag 0G4A] and their invertibility are stated for `ℤ`-indexed complexes.
Extension by zero along `ComplexShape.embeddingUpNat` passes from one to the other, as
`Stacks.DeRhamDirectImage.deRhamCochainComplex` already does for the complex of
`a^{-1}𝒪_S`-modules. The two total complexes then have to be compared: in total degree `n` the
`ℤ`-indexed one is the coproduct of the `Ω^i_{X/S} ⊠ Ω^j_{Y/S}` over the pairs of *integers* with
`i + j = n`, of which those with a negative entry contribute a zero object, while the `ℕ`-indexed
one is the biproduct over the pairs of natural numbers. The comparison is built as a morphism out
of the `ℤ`-indexed total complex, which is determined by its components on the summands, its
compatibility with the differentials being the agreement of the two sign conventions of
[Stacks, Tag 012Z]; Mathlib's `ComplexShape.Embedding.liftExtend` turns it into a morphism into
the extension, and the invertibility is checked degreewise, the negative degrees being zero on
both sides.

*What is carried, and what each input stands for.* Nothing below is the conclusion of
[Stacks, Tag 0FMB], which is the invertibility of the de Rham Künneth map.

* `κ`, the `A`-linear global cup product on the base: the one parameter that the Künneth map of
  [Stacks, Tag 0FLR] already carries in this repository. Its step-(5) comparison is not a
  parameter, being constructed as `Stacks.Cohomology.BoxKunneth.boxTotalComparison` and unique by
  `Stacks.Cohomology.BoxKunneth.BoxTotalComparison.hom_unique`; `hstep` below is accordingly
  stated at that one datum.
* `hκ`, `hrel` and `hstep`: the three inputs of [Stacks, Tag 0FLT], namely the invertibility of
  the global cup product on the affine base, [Stacks, Tag 0FLQ] at the two inverse-image
  complexes, and the invertibility of steps (4) and (5). The implementation notes of
  `StacksFrontier/AlgebraicGeometry/DeRham/BoxTotalKunnethIsomorphism.lean` say why none of the
  three is available in this library; this file adds nothing to that discussion and carries them.
*Boundedness above is not needed here.* [Stacks, Tag 0FLT] states its left-hand complex to be
bounded, but `Stacks.Cohomology.BoxKunneth.isIso_globalBoxKunnethMap` does not consume the bound
either — it is the carried `hstep` that stands in for the part of the argument that uses it — so
no `IsStrictlyLE` hypothesis occurs below. Boundedness below is in the `ℤ`-indexed complex by
construction, `Ω^•_{X/S}` being extended by zero.

*The flatness hypotheses are stated and not consumed*, exactly as in
`Stacks.Cohomology.BoxKunneth.isIso_globalBoxKunnethMap`, to whose underscore-prefixed binders
they are passed. For the de Rham complex of a smooth morphism they hold because each `Ω^i_{X/S}`
is finite locally free by [Stacks, Tag 02G1] and a finite locally free module is flat over the
base when the morphism is flat,
`AlgebraicGeometry.VectorBundleCodimensionOne.isFlatOver_of_isFiniteLocallyFree`. That derivation
needs the flatness of a smooth morphism, [Stacks, Tag 01V9], and the stability of finite local
freeness under exterior powers without a global rank, neither of which this library has; since
the binders are not consumed, they are carried rather than discharged, and smoothness likewise.

*The derived global sections are those of the complex of `f^{-1}𝒪_S`-modules underlying the
extension by zero of `Ω^•_{W/S}`.* That is the same complex as
`Stacks.DeRhamDirectImage.deRhamCochainComplex`, which is the extension by zero of the complex of
`f^{-1}𝒪_S`-modules, up to the commutation of extension by zero with the restriction of scalars
`AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.toInverseImageModules`. That
commutation is not proved here, so the statement below is phrased with the complex it builds and
not with `deRhamCochainComplex`.

## References

* [Stacks Project, Tag 0FMB](https://stacks.math.columbia.edu/tag/0FMB)
* [Stacks Project, Tag 0FMA](https://stacks.math.columbia.edu/tag/0FMA)
* [Stacks Project, Tag 0FLT](https://stacks.math.columbia.edu/tag/0FLT)
* [Stacks Project, Tag 0FLR](https://stacks.math.columbia.edu/tag/0FLR)
* [Stacks Project, Tag 012Z](https://stacks.math.columbia.edu/tag/012Z)
* [Stacks Project, Tag 02G1](https://stacks.math.columbia.edu/tag/02G1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.GlobalKunneth
open Stacks.DeRhamDirectImage
open Stacks.DerivedTensor.RingedSite

universe u

namespace CategoryTheory.Functor

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]

/-- **The image of a pair of isomorphisms under a bifunctor**: for `F : C₁ ⥤ C₂ ⥤ D` and
isomorphisms `e₁ : X ≅ X'` and `e₂ : Y ≅ Y'` an isomorphism `F(X, Y) ≅ F(X', Y')`, obtained by
changing the two arguments in turn. -/
def bifunctorMapIso (F : C₁ ⥤ C₂ ⥤ D) {X X' : C₁} {Y Y' : C₂} (e₁ : X ≅ X') (e₂ : Y ≅ Y') :
    (F.obj X).obj Y ≅ (F.obj X').obj Y' :=
  (F.mapIso e₁).app Y ≪≫ (F.obj X').mapIso e₂

/-- The morphism underlying `bifunctorMapIso e₁ e₂` is `(F.map e₁.hom).app Y` followed by
`(F.obj X').map e₂.hom`. -/
@[simp]
theorem bifunctorMapIso_hom (F : C₁ ⥤ C₂ ⥤ D) {X X' : C₁} {Y Y' : C₂} (e₁ : X ≅ X')
    (e₂ : Y ≅ Y') :
    (F.bifunctorMapIso e₁ e₂).hom = (F.map e₁.hom).app Y ≫ (F.obj X').map e₂.hom :=
  rfl

/-- Pushing a morphism of the first argument past the comparison of a pair of isomorphisms. -/
theorem bifunctorMapIso_hom_comp_map_app (F : C₁ ⥤ C₂ ⥤ D) {X X' X'' : C₁} {Y Y' : C₂}
    (e₁ : X ≅ X') (e₂ : Y ≅ Y') (f : X' ⟶ X'') :
    (F.bifunctorMapIso e₁ e₂).hom ≫ (F.map f).app Y' =
      (F.map (e₁.hom ≫ f)).app Y ≫ (F.obj X'').map e₂.hom := by
  rw [bifunctorMapIso_hom, Category.assoc, NatTrans.naturality, ← Category.assoc,
    ← NatTrans.comp_app, ← F.map_comp]

/-- Pushing a morphism of the second argument past the comparison of a pair of isomorphisms. -/
theorem bifunctorMapIso_hom_comp_obj_map (F : C₁ ⥤ C₂ ⥤ D) {X X' : C₁} {Y Y' Y'' : C₂}
    (e₁ : X ≅ X') (e₂ : Y ≅ Y') (g : Y' ⟶ Y'') :
    (F.bifunctorMapIso e₁ e₂).hom ≫ (F.obj X').map g =
      (F.map e₁.hom).app Y ≫ (F.obj X').map (e₂.hom ≫ g) := by
  rw [bifunctorMapIso_hom, Category.assoc, ← Functor.map_comp]

/-- Pulling a morphism of the first argument past the comparison of a pair of isomorphisms. -/
theorem map_app_comp_bifunctorMapIso_hom (F : C₁ ⥤ C₂ ⥤ D) {X₀ X X' : C₁} {Y Y' : C₂}
    (e₁ : X ≅ X') (e₂ : Y ≅ Y') (f : X₀ ⟶ X) :
    (F.map f).app Y ≫ (F.bifunctorMapIso e₁ e₂).hom =
      (F.map (f ≫ e₁.hom)).app Y ≫ (F.obj X').map e₂.hom := by
  rw [bifunctorMapIso_hom, ← Category.assoc, ← NatTrans.comp_app, ← F.map_comp]

/-- Pulling a morphism of the second argument past the comparison of a pair of isomorphisms. -/
theorem obj_map_comp_bifunctorMapIso_hom (F : C₁ ⥤ C₂ ⥤ D) {X X' : C₁} {Y₀ Y Y' : C₂}
    (e₁ : X ≅ X') (e₂ : Y ≅ Y') (g : Y₀ ⟶ Y) :
    (F.obj X).map g ≫ (F.bifunctorMapIso e₁ e₂).hom =
      (F.map e₁.hom).app Y₀ ≫ (F.obj X').map (g ≫ e₂.hom) := by
  rw [bifunctorMapIso_hom, ← Category.assoc, NatTrans.naturality, Category.assoc,
    ← Functor.map_comp]

end CategoryTheory.Functor

namespace HomologicalComplex

/-- **[Stacks, Tag 012Z], the differential of the total complex of a bifunctor applied to two
`ℤ`-indexed cochain complexes, summand-wise**: on the summand `F(K^p, L^q)` of
`Tot(F(K, L))^n` it is `F(d_K, 1) + (-1)^p F(1, d_L)`. The three successor degrees are given as
hypotheses rather than as `+ 1`, so that the lemma can be used at degrees presented in another
form, such as the images of natural numbers. -/
theorem ι_mapBifunctor_d_up_ℤ {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]
    [Limits.HasZeroMorphisms C₁] [Limits.HasZeroMorphisms C₂] [Preadditive D]
    (K : CochainComplex C₁ ℤ) (L : CochainComplex C₂ ℤ) (F : C₁ ⥤ C₂ ⥤ D)
    [F.PreservesZeroMorphisms] [∀ X₁, (F.obj X₁).PreservesZeroMorphisms]
    [HasMapBifunctor K L F (ComplexShape.up ℤ)]
    (p q n p' q' n' : ℤ) (h : p + q = n) (hp : p + 1 = p') (hq : q + 1 = q') (hn : n + 1 = n') :
    ιMapBifunctor K L F (ComplexShape.up ℤ) p q n h ≫
        (mapBifunctor K L F (ComplexShape.up ℤ)).d n n' =
      (F.map (K.d p p')).app (L.X q) ≫
          ιMapBifunctor K L F (ComplexShape.up ℤ) p' q n' (by dsimp; lia) +
        p.negOnePow • ((F.obj (K.X p)).map (L.d q q') ≫
          ιMapBifunctor K L F (ComplexShape.up ℤ) p q' n' (by dsimp; lia)) := by
  subst hp hq hn
  refine (HomologicalComplex₂.ιTotal_d_up_ℤ _ p q n h).trans ?_
  rw [Functor.mapBifunctorHomologicalComplex_obj_obj_d_f,
    Functor.mapBifunctorHomologicalComplex_obj_obj_X_d]
  rfl

/-- **[Stacks, Tag 012Z], the same statement for two `ℕ`-indexed cochain complexes**: on the
summand `F(K^p, L^q)` of `Tot(F(K, L))^n` the differential is `F(d_K, 1) + (-1)^p F(1, d_L)`. -/
theorem ι_mapBifunctor_d_up_ℕ {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]
    [Limits.HasZeroMorphisms C₁] [Limits.HasZeroMorphisms C₂] [Preadditive D]
    (K : CochainComplex C₁ ℕ) (L : CochainComplex C₂ ℕ) (F : C₁ ⥤ C₂ ⥤ D)
    [F.PreservesZeroMorphisms] [∀ X₁, (F.obj X₁).PreservesZeroMorphisms]
    [HasMapBifunctor K L F (ComplexShape.up ℕ)]
    (p q n p' q' n' : ℕ) (h : p + q = n) (hp : p + 1 = p') (hq : q + 1 = q') (hn : n + 1 = n') :
    ιMapBifunctor K L F (ComplexShape.up ℕ) p q n h ≫
        (mapBifunctor K L F (ComplexShape.up ℕ)).d n n' =
      (F.map (K.d p p')).app (L.X q) ≫
          ιMapBifunctor K L F (ComplexShape.up ℕ) p' q n' (by dsimp; omega) +
        ((-1 : ℤˣ) ^ p) • ((F.obj (K.X p)).map (L.d q q') ≫
          ιMapBifunctor K L F (ComplexShape.up ℕ) p q' n' (by dsimp; omega)) := by
  subst hp hq hn
  refine (HomologicalComplex₂.ιTotal_d_up_ℕ _ p q n h).trans ?_
  rw [Functor.mapBifunctorHomologicalComplex_obj_obj_d_f,
    Functor.mapBifunctorHomologicalComplex_obj_obj_X_d]
  rfl

end HomologicalComplex

namespace AlgebraicGeometry

attribute [local instance] hasColimits_sheafOfModules_toRingCat
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace FiniteOrderDifferentialOperatorCategory

variable {X Y S : Scheme.{u}} {a : X ⟶ S} {b : Y ⟶ S}

/-- **The box product of a zero object with anything is a zero object**, the box product being
additive in its first argument. -/
theorem isZero_boxProductCurried_left {F : FiniteOrderDifferentialOperatorCategory a}
    (G : FiniteOrderDifferentialOperatorCategory b) (h : IsZero F) :
    IsZero (((boxProductCurried a b).obj F).obj G) := by
  rw [IsZero.iff_id_eq_zero, ← NatTrans.id_app, ← (boxProductCurried a b).map_id,
    (IsZero.iff_id_eq_zero F).1 h, Functor.map_zero]
  rfl

/-- **The box product of anything with a zero object is a zero object**, the box product being
additive in its second argument. -/
theorem isZero_boxProductCurried_right (F : FiniteOrderDifferentialOperatorCategory a)
    {G : FiniteOrderDifferentialOperatorCategory b} (h : IsZero G) :
    IsZero (((boxProductCurried a b).obj F).obj G) :=
  Functor.map_isZero ((boxProductCurried a b).obj F) h

end FiniteOrderDifferentialOperatorCategory

namespace Scheme.Hom

open FiniteOrderDifferentialOperatorCategory

/-- The embedding of complex shapes from `ComplexShape.up ℕ` to `ComplexShape.up ℤ` sends `n` to
`n`. -/
theorem embeddingUpNat_f (n : ℕ) : ComplexShape.embeddingUpNat.f n = (n : ℤ) := rfl

/-- The sign conventions of [Stacks, Tag 012Z] in the two indexings agree: `(-1)^n` read in `ℤ`
is `(-1)^n` read in `ℕ`. -/
theorem negOnePow_natCast (n : ℕ) : (n : ℤ).negOnePow = (-1 : ℤˣ) ^ n := by
  rw [← ComplexShape.ε_up_ℤ, ComplexShape.ε_up_ℤ_natCast, ComplexShape.ε_up_ℕ]

variable {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)

/-! ### The relative de Rham complex as a `ℤ`-indexed complex -/

/-- **The relative de Rham complex `Ω^•_{X/S}` as a `ℤ`-indexed cochain complex of finite-order
differential operators on `X/S`**: the `ℕ`-indexed complex
`AlgebraicGeometry.Scheme.Hom.deRhamDiffOpComplex`, extended by zero. This is the indexing the
box product of [Stacks, Tag 0G4A] and the derived category use, and the same passage that
`Stacks.DeRhamDirectImage.deRhamCochainComplex` makes for the complex of `a^{-1}𝒪_S`-modules. -/
abbrev deRhamDiffOpCochainComplex :
    CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ :=
  (deRhamDiffOpComplex a).extend ComplexShape.embeddingUpNat

/-- The extended de Rham complex is concentrated in nonnegative degrees. -/
instance isStrictlyGE_deRhamDiffOpCochainComplex :
    (deRhamDiffOpCochainComplex a).IsStrictlyGE 0 where
  isZero i hi := HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat i
    (fun n => by simpa using hi n)

/-- In a nonnegative degree the extended de Rham complex is `Ω^n_{X/S}`. -/
def deRhamDiffOpCochainComplexXIso (n : ℕ) :
    (deRhamDiffOpCochainComplex a).X (n : ℤ) ≅ (deRhamDiffOpComplex a).X n :=
  HomologicalComplex.extendXIso _ ComplexShape.embeddingUpNat (embeddingUpNat_f n)

/-- In a negative degree the extended de Rham complex is zero. -/
theorem isZero_deRhamDiffOpCochainComplex_X (i : ℤ) (hi : i < 0) :
    IsZero ((deRhamDiffOpCochainComplex a).X i) :=
  HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat i
    (fun n => by rw [embeddingUpNat_f]; lia)

/-- **The total complex of the box product of the two extended de Rham complexes exists**: both
are concentrated in nonnegative degrees, so in each total degree only finitely many summands
contribute. -/
instance hasMapBifunctor_deRhamDiffOpCochainComplex :
    HomologicalComplex.HasMapBifunctor (deRhamDiffOpCochainComplex a)
      (deRhamDiffOpCochainComplex b) (boxProductCurried a b) (ComplexShape.up ℤ) :=
  hasMapBifunctor_up_ℤ _ _ 0 0

/-- **`Tot(Ω^•_{X/S} ⊠ Ω^•_{Y/S})` formed from the two `ℤ`-indexed extensions**, the target of
the Künneth map of [Stacks, Tag 0FLR] at the two de Rham complexes. -/
abbrev deRhamBoxTotalCochain :
    CochainComplex (FiniteOrderDifferentialOperatorCategory (pullback.fst a b ≫ a)) ℤ :=
  HomologicalComplex.mapBifunctor (deRhamDiffOpCochainComplex a) (deRhamDiffOpCochainComplex b)
    (boxProductCurried a b) (ComplexShape.up ℤ)

/-- `Tot(Ω^•_{X/S} ⊠ Ω^•_{Y/S})`, the `ℕ`-indexed total complex of [Stacks, Tag 0FMA]: the
complex `AlgebraicGeometry.Scheme.Hom.deRhamBoxTotal`, named again as a reducible abbreviation in
the `HomologicalComplex.mapBifunctor` spelling, which is the spelling the lemmas on the summands
of a total complex are stated in. -/
abbrev deRhamBoxTotalNat :
    CochainComplex (FiniteOrderDifferentialOperatorCategory (pullback.fst a b ≫ a)) ℕ :=
  HomologicalComplex.mapBifunctor (deRhamDiffOpComplex a) (deRhamDiffOpComplex b)
    (boxProductCurried a b) (ComplexShape.up ℕ)

/-- A summand of the `ℤ`-indexed total complex with a negative index is zero, one of its two
factors being zero. -/
theorem isZero_deRhamBoxSummand (i j : ℤ) (hij : i < 0 ∨ j < 0) :
    IsZero (((boxProductCurried a b).obj ((deRhamDiffOpCochainComplex a).X i)).obj
      ((deRhamDiffOpCochainComplex b).X j)) := by
  obtain hi | hj := hij
  · exact isZero_boxProductCurried_left _ (isZero_deRhamDiffOpCochainComplex_X a i hi)
  · exact isZero_boxProductCurried_right _ (isZero_deRhamDiffOpCochainComplex_X b j hj)

/-- **In a negative degree the `ℤ`-indexed total complex is zero**: every pair of integers
summing to a negative integer has a negative entry, so every summand is zero. -/
theorem isZero_deRhamBoxTotalCochain_X (n : ℤ) (hn : n < 0) :
    IsZero ((deRhamBoxTotalCochain a b).X n) := by
  rw [IsZero.iff_id_eq_zero]
  refine HomologicalComplex.mapBifunctor.hom_ext fun i j hij => ?_
  have hij' : i + j = n := hij
  exact (isZero_deRhamBoxSummand a b i j (by lia)).eq_of_src _ _

/-! ### The comparison of the two total complexes -/

/-- The component of the comparison of the two total complexes on the summand of degree `(i, j)`:
the box product of the two identifications of the extensions in nonnegative degrees followed by
the inclusion of the `(i, j)` summand of the `ℕ`-indexed total complex, and zero on a summand
with a negative index, that summand being zero. -/
def deRhamBoxTotalComponent (n : ℕ) (i j : ℤ) (hij : i + j = (n : ℤ)) :
    ((boxProductCurried a b).obj ((deRhamDiffOpCochainComplex a).X i)).obj
        ((deRhamDiffOpCochainComplex b).X j) ⟶ (deRhamBoxTotalNat a b).X n :=
  if h : 0 ≤ i ∧ 0 ≤ j then
    ((boxProductCurried a b).bifunctorMapIso
          (HomologicalComplex.extendXIso _ ComplexShape.embeddingUpNat
            ((embeddingUpNat_f i.toNat).trans (Int.toNat_of_nonneg h.1)))
          (HomologicalComplex.extendXIso _ ComplexShape.embeddingUpNat
            ((embeddingUpNat_f j.toNat).trans (Int.toNat_of_nonneg h.2)))).hom ≫
      HomologicalComplex.ιMapBifunctor (deRhamDiffOpComplex a) (deRhamDiffOpComplex b)
        (boxProductCurried a b) (ComplexShape.up ℕ) i.toNat j.toNat n (by dsimp; lia)
  else 0

/-- On a summand whose two indices are natural numbers the component of the comparison is the box
product of the two identifications of the extensions followed by the inclusion of the summand. -/
theorem deRhamBoxTotalComponent_natCast (n p q : ℕ) (hij : (p : ℤ) + (q : ℤ) = (n : ℤ)) :
    deRhamBoxTotalComponent a b n (p : ℤ) (q : ℤ) hij =
      ((boxProductCurried a b).bifunctorMapIso (deRhamDiffOpCochainComplexXIso a p)
          (deRhamDiffOpCochainComplexXIso b q)).hom ≫
        HomologicalComplex.ιMapBifunctor (deRhamDiffOpComplex a) (deRhamDiffOpComplex b)
          (boxProductCurried a b) (ComplexShape.up ℕ) p q n (by dsimp; lia) := by
  rw [deRhamBoxTotalComponent,
    dite_eq_left ⟨Int.natCast_nonneg p, Int.natCast_nonneg q⟩]
  rfl

/-- The component of the comparison on a summand with a negative index is zero. -/
theorem deRhamBoxTotalComponent_neg (n : ℕ) (i j : ℤ) (hij : i + j = (n : ℤ))
    (h : ¬ (0 ≤ i ∧ 0 ≤ j)) : deRhamBoxTotalComponent a b n i j hij = 0 :=
  dite_eq_right h

/-- **The comparison of the two total complexes in degree `n`**, as a morphism out of the
`ℤ`-indexed one: such a morphism is determined by its components on the summands. -/
def deRhamBoxTotalRestrictionf (n : ℕ) :
    (deRhamBoxTotalCochain a b).X (n : ℤ) ⟶ (deRhamBoxTotalNat a b).X n :=
  HomologicalComplex.mapBifunctorDesc (fun i j hij => deRhamBoxTotalComponent a b n i j hij)

/-- The comparison `deRhamBoxTotalRestrictionf` restricted to the summand of indices `(i, j)` is
`deRhamBoxTotalComponent`. -/
@[reassoc]
theorem ι_deRhamBoxTotalRestrictionf (n : ℕ) (i j : ℤ) (hij : i + j = (n : ℤ)) :
    HomologicalComplex.ιMapBifunctor (deRhamDiffOpCochainComplex a)
        (deRhamDiffOpCochainComplex b) (boxProductCurried a b) (ComplexShape.up ℤ) i j
        (n : ℤ) hij ≫ deRhamBoxTotalRestrictionf a b n =
      deRhamBoxTotalComponent a b n i j hij :=
  HomologicalComplex.ι_mapBifunctorDesc _ i j hij

/-- The inverse comparison in degree `n`, as a morphism out of the `ℕ`-indexed total complex. -/
def deRhamBoxTotalRestrictionfInv (n : ℕ) :
    (deRhamBoxTotalNat a b).X n ⟶ (deRhamBoxTotalCochain a b).X (n : ℤ) :=
  HomologicalComplex.mapBifunctorDesc (fun p q (hpq : p + q = n) =>
    ((boxProductCurried a b).bifunctorMapIso (deRhamDiffOpCochainComplexXIso a p)
          (deRhamDiffOpCochainComplexXIso b q)).inv ≫
      HomologicalComplex.ιMapBifunctor (deRhamDiffOpCochainComplex a)
        (deRhamDiffOpCochainComplex b) (boxProductCurried a b) (ComplexShape.up ℤ)
        (p : ℤ) (q : ℤ) (n : ℤ) (by dsimp; lia))

/-- The inverse comparison `deRhamBoxTotalRestrictionfInv` restricted to the summand of indices
`(p, q)` is the inverse of the box product of the two identifications of the extensions followed
by the inclusion of the summand of indices `(p, q)` of the `ℤ`-indexed total complex. -/
@[reassoc]
theorem ι_deRhamBoxTotalRestrictionfInv (n p q : ℕ) (hpq : p + q = n) :
    HomologicalComplex.ιMapBifunctor (deRhamDiffOpComplex a) (deRhamDiffOpComplex b)
        (boxProductCurried a b) (ComplexShape.up ℕ) p q n hpq ≫
      deRhamBoxTotalRestrictionfInv a b n =
      ((boxProductCurried a b).bifunctorMapIso (deRhamDiffOpCochainComplexXIso a p)
          (deRhamDiffOpCochainComplexXIso b q)).inv ≫
        HomologicalComplex.ιMapBifunctor (deRhamDiffOpCochainComplex a)
          (deRhamDiffOpCochainComplex b) (boxProductCurried a b) (ComplexShape.up ℤ)
          (p : ℤ) (q : ℤ) (n : ℤ) (by dsimp; lia) :=
  HomologicalComplex.ι_mapBifunctorDesc _ p q hpq

/-- **The comparison in degree `n` is an isomorphism**: on the summands of both sides it is the
box product of two isomorphisms, and the summands of the `ℤ`-indexed total complex with a
negative index are zero. -/
instance isIso_deRhamBoxTotalRestrictionf (n : ℕ) :
    IsIso (deRhamBoxTotalRestrictionf a b n) := by
  refine ⟨deRhamBoxTotalRestrictionfInv a b n, ?_, ?_⟩
  · refine HomologicalComplex.mapBifunctor.hom_ext fun i j hij => ?_
    have hij' : i + j = (n : ℤ) := hij
    by_cases h : 0 ≤ i ∧ 0 ≤ j
    · obtain ⟨p, rfl⟩ : ∃ p : ℕ, (p : ℤ) = i := ⟨i.toNat, Int.toNat_of_nonneg h.1⟩
      obtain ⟨q, rfl⟩ : ∃ q : ℕ, (q : ℤ) = j := ⟨j.toNat, Int.toNat_of_nonneg h.2⟩
      rw [Category.comp_id, ι_deRhamBoxTotalRestrictionf_assoc,
        deRhamBoxTotalComponent_natCast, Category.assoc,
        ι_deRhamBoxTotalRestrictionfInv, Iso.hom_inv_id_assoc]
    · rw [Category.comp_id, ι_deRhamBoxTotalRestrictionf_assoc,
        deRhamBoxTotalComponent_neg a b n i j hij h, zero_comp]
      exact ((isZero_deRhamBoxSummand a b i j (by lia)).eq_of_src _ _).symm
  · refine HomologicalComplex.mapBifunctor.hom_ext fun p q hpq => ?_
    have hpq' : p + q = n := hpq
    rw [Category.comp_id, ι_deRhamBoxTotalRestrictionfInv_assoc,
      ι_deRhamBoxTotalRestrictionf, deRhamBoxTotalComponent_natCast, Iso.inv_hom_id_assoc]

/-- The identification of the extensions in nonnegative degrees carries the de Rham differential
of `Ω^•_{X/S}` to the differential of the extension. -/
theorem deRhamDiffOpCochainComplexXIso_hom_comp_d (p : ℕ) :
    (deRhamDiffOpCochainComplexXIso a p).hom ≫ (deRhamDiffOpComplex a).d p (p + 1) =
      (deRhamDiffOpCochainComplex a).d (p : ℤ) ((p + 1 : ℕ) : ℤ) ≫
        (deRhamDiffOpCochainComplexXIso a (p + 1)).hom := by
  rw [HomologicalComplex.extend_d_eq _ ComplexShape.embeddingUpNat (embeddingUpNat_f p)
    (embeddingUpNat_f (p + 1)), deRhamDiffOpCochainComplexXIso,
    deRhamDiffOpCochainComplexXIso, Category.assoc, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

/-- The comparison is compatible with the de Rham differential of the first factor. -/
theorem bifunctorMapIso_hom_comp_d_left (p q : ℕ) :
    ((boxProductCurried a b).bifunctorMapIso (deRhamDiffOpCochainComplexXIso a p)
          (deRhamDiffOpCochainComplexXIso b q)).hom ≫
        ((boxProductCurried a b).map ((deRhamDiffOpComplex a).d p (p + 1))).app
          ((deRhamDiffOpComplex b).X q) =
      ((boxProductCurried a b).map ((deRhamDiffOpCochainComplex a).d (p : ℤ)
            ((p + 1 : ℕ) : ℤ))).app ((deRhamDiffOpCochainComplex b).X (q : ℤ)) ≫
        ((boxProductCurried a b).bifunctorMapIso (deRhamDiffOpCochainComplexXIso a (p + 1))
          (deRhamDiffOpCochainComplexXIso b q)).hom := by
  rw [Functor.bifunctorMapIso_hom_comp_map_app, Functor.map_app_comp_bifunctorMapIso_hom,
    deRhamDiffOpCochainComplexXIso_hom_comp_d]

/-- The comparison is compatible with the de Rham differential of the second factor. -/
theorem bifunctorMapIso_hom_comp_d_right (p q : ℕ) :
    ((boxProductCurried a b).bifunctorMapIso (deRhamDiffOpCochainComplexXIso a p)
          (deRhamDiffOpCochainComplexXIso b q)).hom ≫
        ((boxProductCurried a b).obj ((deRhamDiffOpComplex a).X p)).map
          ((deRhamDiffOpComplex b).d q (q + 1)) =
      ((boxProductCurried a b).obj ((deRhamDiffOpCochainComplex a).X (p : ℤ))).map
          ((deRhamDiffOpCochainComplex b).d (q : ℤ) ((q + 1 : ℕ) : ℤ)) ≫
        ((boxProductCurried a b).bifunctorMapIso (deRhamDiffOpCochainComplexXIso a p)
          (deRhamDiffOpCochainComplexXIso b (q + 1))).hom := by
  rw [Functor.bifunctorMapIso_hom_comp_obj_map, Functor.obj_map_comp_bifunctorMapIso_hom,
    deRhamDiffOpCochainComplexXIso_hom_comp_d]

/-- **The comparison of the two total complexes, as a morphism of `ℕ`-indexed complexes** out of
the restriction of the `ℤ`-indexed one. The compatibility with the differentials is the agreement
of the two sign conventions of [Stacks, Tag 012Z], `(-1)^i` read in `ℤ` and in `ℕ`. -/
def deRhamBoxTotalRestrictionHom :
    (deRhamBoxTotalCochain a b).restriction ComplexShape.embeddingUpNat ⟶
      deRhamBoxTotalNat a b where
  f n := deRhamBoxTotalRestrictionf a b n
  comm' m m' hmm' := by
    obtain rfl : m + 1 = m' := hmm'
    change deRhamBoxTotalRestrictionf a b m ≫ (deRhamBoxTotalNat a b).d m (m + 1) =
      (deRhamBoxTotalCochain a b).d (m : ℤ) ((m + 1 : ℕ) : ℤ) ≫
        deRhamBoxTotalRestrictionf a b (m + 1)
    refine HomologicalComplex.mapBifunctor.hom_ext fun i j hij => ?_
    have hij' : i + j = (m : ℤ) := hij
    by_cases h : 0 ≤ i ∧ 0 ≤ j
    · obtain ⟨p, rfl⟩ : ∃ p : ℕ, (p : ℤ) = i := ⟨i.toNat, Int.toNat_of_nonneg h.1⟩
      obtain ⟨q, rfl⟩ : ∃ q : ℕ, (q : ℤ) = j := ⟨j.toNat, Int.toNat_of_nonneg h.2⟩
      have hpq : p + q = m := by lia
      conv_lhs => rw [← Category.assoc, ι_deRhamBoxTotalRestrictionf,
        deRhamBoxTotalComponent_natCast, Category.assoc,
        HomologicalComplex.ι_mapBifunctor_d_up_ℕ _ _ _ p q m (p + 1) (q + 1) (m + 1)
          hpq rfl rfl rfl]
      conv_rhs => rw [← Category.assoc, HomologicalComplex.ι_mapBifunctor_d_up_ℤ _ _ _
        (p : ℤ) (q : ℤ) (m : ℤ) ((p + 1 : ℕ) : ℤ) ((q + 1 : ℕ) : ℤ) ((m + 1 : ℕ) : ℤ) hij
        (by push_cast; ring) (by push_cast; ring) (by push_cast; ring)]
      simp only [Preadditive.comp_add, Preadditive.add_comp, Units.smul_def,
        Preadditive.comp_zsmul, Preadditive.zsmul_comp, negOnePow_natCast, Category.assoc]
      congr 1
      · rw [← Category.assoc, bifunctorMapIso_hom_comp_d_left, Category.assoc,
          ι_deRhamBoxTotalRestrictionf, deRhamBoxTotalComponent_natCast]
      · congr 1
        rw [← Category.assoc, bifunctorMapIso_hom_comp_d_right, Category.assoc,
          ι_deRhamBoxTotalRestrictionf, deRhamBoxTotalComponent_natCast]
    · rw [← Category.assoc, ι_deRhamBoxTotalRestrictionf,
        deRhamBoxTotalComponent_neg a b m i j hij h, zero_comp]
      exact ((isZero_deRhamBoxSummand a b i j (by lia)).eq_of_src _ _).symm

/-- The comparison lifts to the extension by zero: the only degree where the lifting could fail
is the lower boundary of the embedding, and there the source is zero. -/
theorem hasLift_deRhamBoxTotalRestrictionHom :
    ComplexShape.embeddingUpNat.HasLift (deRhamBoxTotalRestrictionHom a b) := by
  intro j hj i' hi'
  by_cases h : 0 ≤ i'
  · exact absurd ((embeddingUpNat_f i'.toNat).trans (Int.toNat_of_nonneg h))
      (hj.notMem hi' i'.toNat)
  · exact (isZero_deRhamBoxTotalCochain_X a b i' (by lia)).eq_of_src _ _

/-- **The comparison between the `ℤ`-indexed total complex of the box product of the two
extensions and the extension of the `ℕ`-indexed total complex.** -/
def deRhamBoxTotalExtendHom :
    deRhamBoxTotalCochain a b ⟶ (deRhamBoxTotalNat a b).extend ComplexShape.embeddingUpNat :=
  ComplexShape.embeddingUpNat.liftExtend (deRhamBoxTotalRestrictionHom a b)
    (hasLift_deRhamBoxTotalRestrictionHom a b)

/-- **The comparison is an isomorphism in every degree**: in a nonnegative degree it is the
degreewise comparison of the two total complexes, and in a negative degree both sides are
zero. -/
instance isIso_deRhamBoxTotalExtendHom_f (n : ℤ) :
    IsIso ((deRhamBoxTotalExtendHom a b).f n) := by
  by_cases h : 0 ≤ n
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, (m : ℤ) = n := ⟨n.toNat, Int.toNat_of_nonneg h⟩
    rw [deRhamBoxTotalExtendHom, ComplexShape.Embedding.isIso_liftExtend_f_iff _ _ _
      (embeddingUpNat_f m)]
    exact isIso_deRhamBoxTotalRestrictionf a b m
  · have h₁ := isZero_deRhamBoxTotalCochain_X a b n (by lia)
    have h₂ := HomologicalComplex.isZero_extend_X (deRhamBoxTotalNat a b)
      ComplexShape.embeddingUpNat n (fun k => by rw [embeddingUpNat_f]; lia)
    exact ⟨0, h₁.eq_of_src _ _, h₂.eq_of_tgt _ _⟩

/-- **The comparison of the two total complexes is an isomorphism**, being one in every
degree. -/
instance isIso_deRhamBoxTotalExtendHom : IsIso (deRhamBoxTotalExtendHom a b) :=
  HomologicalComplex.Hom.isIso_of_components _

/-- **The de Rham Künneth isomorphism for the `ℤ`-indexed complexes**

`Tot(Ω^•_{X/S} ⊠ Ω^•_{Y/S}) ≅ Ω^•_{X ×_S Y/S}`,

both sides formed from the extensions by zero: the comparison of the `ℤ`-indexed total complex
with the extension of the `ℕ`-indexed one, followed by the extension of the isomorphism of
complexes of [Stacks, Tag 0FMA]. -/
def deRhamBoxTotalExtendIso :
    deRhamBoxTotalCochain a b ≅
      (deRhamDiffOpComplex (pullback.fst a b ≫ a)).extend ComplexShape.embeddingUpNat :=
  asIso (deRhamBoxTotalExtendHom a b) ≪≫
    (ComplexShape.embeddingUpNat.extendFunctor _).mapIso (deRhamBoxTotalIso a b)

end Scheme.Hom

end AlgebraicGeometry

namespace Stacks.Cohomology.BoxKunneth

open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory

attribute [local instance 2000] HasDerivedCategory.standard

attribute [local instance] AlgebraicGeometry.hasColimits_sheafOfModules_toRingCat
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

variable {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)

/-- The isomorphism of complexes of [Stacks, Tag 0FMA], between the total complex that the
Künneth map of [Stacks, Tag 0FLR] lands in and the extension by zero of `Ω^•_{X ×_S Y/S}`. -/
def deRhamBoxTotalKunnethIso :
    boxTotal a b (deRhamDiffOpCochainComplex a) (deRhamDiffOpCochainComplex b) 0 0 ≅
      (deRhamDiffOpComplex (pullback.fst a b ≫ a)).extend ComplexShape.embeddingUpNat :=
  eqToIso (boxTotal_eq a b (deRhamDiffOpCochainComplex a) (deRhamDiffOpCochainComplex b) 0 0) ≪≫
    deRhamBoxTotalExtendIso a b

/-- **The de Rham Künneth map of [Stacks, Tag 0FMB]**

`RΓ(X, Ω^•_{X/S}) ⊗^𝐋_A RΓ(Y, Ω^•_{Y/S}) ⟶ RΓ(X ×_S Y, Ω^•_{X ×_S Y/S})`

in `D(A)` for `A = Γ(S, 𝒪_S)`: the global Künneth map of [Stacks, Tag 0FLR] at the two relative
de Rham complexes, read as `ℤ`-indexed complexes by extension by zero, followed by derived global
sections of the isomorphism `Tot(Ω^•_{X/S} ⊠ Ω^•_{Y/S}) ≅ Ω^•_{X ×_S Y/S}` of
[Stacks, Tag 0FMA]. The complexes whose derived global sections are taken are the complexes of
inverse-image modules underlying the de Rham complexes; the global cup product `κ` is the one
parameter that the map of [Stacks, Tag 0FLR] carries, its step-(5) comparison being constructed
as `Stacks.Cohomology.BoxKunneth.boxTotalComparison`. -/
@[stacks 0FMB "the map: the global Künneth map of Tag 0FLR at the two de Rham complexes, read as \
ℤ-indexed complexes by extension by zero, followed by derived global sections of the Tag 0FMA \
isomorphism; it carries the one parameter of the Tag 0FLR map, the global cup product on the \
base. The step-(5) comparison is not carried, being constructed"]
def deRhamGlobalKunnethMap (κ : GlobalCupProduct S.toRingedSpace) :
    ((tensorBase S.toRingedSpace).obj
          ((sectionsOverBase (inverseImageBaseProjection a)).obj
            (DerivedCategory.Q.obj (leftComplex a (deRhamDiffOpCochainComplex a))))).obj
        ((sectionsOverBase (inverseImageBaseProjection b)).obj
          (DerivedCategory.Q.obj (rightComplex b (deRhamDiffOpCochainComplex b)))) ⟶
      (sectionsOverBase (inverseImageBaseProjection (pullback.fst a b ≫ a))).obj
        (DerivedCategory.Q.obj
          (((toInverseImageModules (pullback.fst a b ≫ a)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj ((deRhamDiffOpComplex (pullback.fst a b ≫ a)).extend
              ComplexShape.embeddingUpNat))) :=
  globalBoxKunnethMap a b (deRhamDiffOpCochainComplex a) (deRhamDiffOpCochainComplex b) 0 0 κ ≫
    (sectionsOverBase (inverseImageBaseProjection (pullback.fst a b ≫ a))).map
      (DerivedCategory.Q.map
        (((toInverseImageModules (pullback.fst a b ≫ a)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (deRhamBoxTotalKunnethIso a b).hom))

/-- **[Stacks, Tag 0FMB].** Let `a : X ⟶ S` and `b : Y ⟶ S` be smooth morphisms of schemes with
`S = Spec A` affine and `X` and `Y` quasi-compact with affine diagonal. Then the de Rham Künneth
map

`RΓ(X, Ω^•_{X/S}) ⊗^𝐋_A RΓ(Y, Ω^•_{Y/S}) ⟶ RΓ(X ×_S Y, Ω^•_{X ×_S Y/S})`

is an isomorphism in `D(A)`.

What is proved is the specialization of [Stacks, Tag 0FLT] to the two relative de Rham complexes
together with the transport of [Stacks, Tag 0FMA] across the extension by zero, which identifies
the target of the Künneth map with `RΓ(X ×_S Y, Ω^•_{X ×_S Y/S})`. The three inputs of
[Stacks, Tag 0FLT] are carried as `hκ`, `hrel` and `hstep`, so the geometric hypotheses are not
consumed. The implementation notes of this file say what each carried input is and why the
library does not supply it. -/
@[stacks 0FMB "the isomorphism, with the identification of the target with RΓ(X ×_S Y, Ω^•) by \
Tag 0FMA transported across the extension by zero. Carried, so that the geometric hypotheses are \
not consumed: the three inputs of Tag 0FLT, namely hκ, the invertibility of the global cup \
product on the affine base, hrel, Tag 0FLQ at the two inverse-image complexes, and hstep, steps \
(4) and (5), in which the source consumes the flatness of the terms. The termwise S-flatness of \
Ω^• is stated and, as in Tag 0FLT, not consumed"]
theorem isIso_deRhamGlobalKunnethMap [IsAffine S] [CompactSpace X] [CompactSpace Y]
    [AlgebraicGeometry.Smooth a] [AlgebraicGeometry.Smooth b]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    [IsAffineHom (pullback.diagonal (terminal.from Y))]
    (_hK : ∀ n, IsFlatOver a.toLRSHom.toShHom ((deRhamDiffOpCochainComplex a).X n).module)
    (_hL : ∀ n, IsFlatOver b.toLRSHom.toShHom ((deRhamDiffOpCochainComplex b).X n).module)
    (κ : GlobalCupProduct S.toRingedSpace)
    (hκ : IsIso (κ.app
      ((derivedPushforward (inverseImageBaseProjection a)).obj
          (DerivedCategory.Q.obj (leftComplex a (deRhamDiffOpCochainComplex a))),
        (derivedPushforward (inverseImageBaseProjection b)).obj
          (DerivedCategory.Q.obj (rightComplex b (deRhamDiffOpCochainComplex b))))))
    (hrel : IsIso (Stacks.Cohomology.DerivedKunneth.kunnethMap (inverseImageBaseProjection a)
      (inverseImageBaseProjection b) (fstProjection a b) (sndProjection a b)
      (inverseImageBaseProjection (pullback.fst a b ≫ a)) (fstProjection_comp a b)
      (sndProjection_comp a b)
      (DerivedCategory.Q.obj (leftComplex a (deRhamDiffOpCochainComplex a)))
      (DerivedCategory.Q.obj (rightComplex b (deRhamDiffOpCochainComplex b)))))
    (hstep : IsIso (boxTotalDerivedComparison a b (deRhamDiffOpCochainComplex a)
      (deRhamDiffOpCochainComplex b) 0 0
      (boxTotalComparison a b (deRhamDiffOpCochainComplex a)
        (deRhamDiffOpCochainComplex b) 0 0))) :
    IsIso (deRhamGlobalKunnethMap a b κ) := by
  have hmap : IsIso (globalBoxKunnethMap a b (deRhamDiffOpCochainComplex a)
      (deRhamDiffOpCochainComplex b) 0 0 κ) :=
    isIso_globalBoxKunnethMap a b (deRhamDiffOpCochainComplex a)
      (deRhamDiffOpCochainComplex b) 0 0 _hK _hL κ hκ hrel hstep
  have hiso : IsIso ((sectionsOverBase (inverseImageBaseProjection (pullback.fst a b ≫ a))).map
      (DerivedCategory.Q.map
        (((toInverseImageModules (pullback.fst a b ≫ a)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (deRhamBoxTotalKunnethIso a b).hom))) :=
    (((sectionsOverBase (inverseImageBaseProjection (pullback.fst a b ≫ a))).mapIso
      (DerivedCategory.Q.mapIso
        (((toInverseImageModules (pullback.fst a b ≫ a)).mapHomologicalComplex
          (ComplexShape.up ℤ)).mapIso (deRhamBoxTotalKunnethIso a b))))).isIso_hom
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ hmap hiso

end Stacks.Cohomology.BoxKunneth

end
