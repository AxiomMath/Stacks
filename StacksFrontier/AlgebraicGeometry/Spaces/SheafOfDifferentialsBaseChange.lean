module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.BaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentials
import StacksCore.Tactic.StacksAttribute

/-!
# Base change of the sheaf of differentials of a morphism of algebraic spaces

Let `p : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`.  Stacks 05ZC asserts that
for a morphism `g : Y' ⟶ Y` and the base change `X' = X ×_Y Y'` with projection `g' : X' ⟶ X`,
the comparison map `c_{g'} : (g')^*Ω_{X/Y} ⟶ Ω_{X'/Y'}` of Stacks 04CX is an isomorphism, and
Stacks 05ZD asserts that for two morphisms `f : X ⟶ T` and `g : Y ⟶ T` with the same target and
the projections `p`, `q` of a fibre product `W`, the two comparison maps of Stacks 04CX exhibit
`Ω_{W/T}` as the direct sum `p^*Ω_{X/T} ⊕ q^*Ω_{Y/T}`.

Both are proved here the way the source proves them: from the case of schemes — Morphisms,
Lemmas 01V0 and 01V1, which are
`AlgebraicGeometry.Scheme.Hom.isIso_relativeDifferentialsMap_of_isPullback` and
`AlgebraicGeometry.Scheme.Hom.isIso_biprodDesc_relativeDifferentialsMap` — together with the
étale localization of Stacks 04CU.  The étale localization is the input the tree does not have:
Stacks 04CU is carried only in its étale-base half,
`AlgebraicGeometry.Space.sheafOfDifferentialsIsoOfSharpIso`, whose other half is already an
explicit hypothesis there, and nothing compares `AlgebraicGeometry.Space.sheafOfDifferentials`
with `AlgebraicGeometry.Scheme.Hom.relativeDifferentials`.  It is therefore carried as a
hypothesis, in the shape in which the source's argument delivers it and consumes nothing more:
over each étale chart of the source, the comparison map of algebraic spaces *is* the canonical
map of Stacks 01UV of a cartesian square of schemes, read through additive identifications of
the sections.  Invertibility is then the case of schemes plus the local nature of isomorphisms
of sheaves of modules.

The two predicates recording that input, `AlgebraicGeometry.Space.IsEtaleLocalBaseChangeMap`
and `AlgebraicGeometry.Space.IsEtaleLocalFibreProductMap`, take the cartesian square of
algebraic spaces as a parameter: it is the cartesianness of that square which makes the
chartwise square of schemes cartesian, and that is the only way it enters.

The comparison map of Stacks 04CX is itself not constructed in the tree — what the tree carries
is the characterizing property `AlgebraicGeometry.Space.IsSheafOfDifferentialsMap` and its
uniqueness clause `AlgebraicGeometry.Space.eq_of_isSheafOfDifferentialsMap`.  The statements
below are therefore about an arbitrary realization of the comparison map, pinned down by that
property; uniqueness is what carries the étale-local input from the realization it is stated
for to the realization in hand.

## Main definitions

* `AlgebraicGeometry.Space.IsEtaleLocalBaseChangeMap` and
  `AlgebraicGeometry.Space.IsEtaleLocalFibreProductMap` record the étale localization of
  Stacks 04CU for the two situations: over every étale chart the map in question is the
  canonical map of Stacks 01UV, respectively the map of Stacks 01V1, of a cartesian square of
  schemes.

## Main results

* `Stacks.SheafOfModules.bijective_app_of_isIso`: an isomorphism of sheaves of modules on a
  site is bijective on the sections over every object.
* `AlgebraicGeometry.Space.isIso_of_bijective_app`: a morphism of `𝒪_X`-modules on the small
  étale site which is bijective on the sections over every étale chart is an isomorphism.
* `AlgebraicGeometry.Space.isIso_of_isSheafOfDifferentialsMap_of_isPullback`:
  **Stacks 05ZC**, from the scheme case 01V0 and the étale localization of 04CU.
* `AlgebraicGeometry.Space.isIso_biprodDesc_of_isSheafOfDifferentialsMap`:
  **Stacks 05ZD**, from the scheme case 01V1 and the étale localization of 04CU.

## Implementation notes

`Stacks.SheafOfModules.bijective_app_of_isIso` and
`AlgebraicGeometry.Space.isIso_of_bijective_app` are the two halves of the local nature of
isomorphisms used here: the first reads the scheme-level conclusion on sections, the second
assembles the chartwise conclusion into an isomorphism of `𝒪_{X'}`-modules.  Both go through
the underlying sheaf of abelian groups, which reflects isomorphisms.

The identifications of sections supplied by the étale localization are asked for as additive
equivalences rather than as equivalences of types: the two sides are sections of sheaves of
modules over different rings — `𝒪_{X'}(U)` and `Γ(Z', V)` — so there is no common linear
structure to ask for, while additivity is available on both and is what makes the requirement a
statement about the modules rather than about their cardinalities.

The structure morphism of the fibre product in Stacks 05ZD is written `p ≫ f`; the cartesian
square identifies it with `q ≫ g`, and `AlgebraicGeometry.Space.IsSheafOfDifferentialsMap`
takes the structure morphism of the source as a parameter precisely so that this identification
never has to be transported along.  This is the convention of the scheme-level statement
`AlgebraicGeometry.Scheme.Hom.isIso_biprodDesc_relativeDifferentialsMap` of Stacks 01V1, whose
two summands are likewise the canonical maps for `p` and for `q` into `Ω_{W/T}`.

Binary biproducts of `𝒪_X`-modules come from the preadditive structure together with binary
products, and instance search produces them from neither; the instance is restated here for the
projections of `AlgebraicGeometry.Space.smallEtaleRingedSite`, which is the pattern
`AlgebraicGeometry.Space.smallEtaleRingedSite_hasWeakSheafify` already follows.

## References

* [Stacks Project, Tag 05ZC](https://stacks.math.columbia.edu/tag/05ZC)
* [Stacks Project, Tag 05ZD](https://stacks.math.columbia.edu/tag/05ZD)
* [Stacks Project, Tag 04CX](https://stacks.math.columbia.edu/tag/04CX), the comparison map of a
  commutative square and its characterization.
* [Stacks Project, Tag 04CU](https://stacks.math.columbia.edu/tag/04CU), the étale localization
  of the sheaf of differentials.
* [Stacks Project, Tag 01UV](https://stacks.math.columbia.edu/tag/01UV), the canonical map for
  schemes.
* [Stacks Project, Tag 01V0](https://stacks.math.columbia.edu/tag/01V0) and
  [Tag 01V1](https://stacks.math.columbia.edu/tag/01V1), the two statements for schemes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w w' v u₀ u

namespace Stacks.SheafOfModules

/-- An isomorphism of sheaves of modules on a site is bijective on the sections over every
object. -/
theorem bijective_app_of_isIso {C : Type u₀} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} {M N : _root_.SheafOfModules.{w'} R} (φ : M ⟶ N) [IsIso φ]
    (U : Cᵒᵖ) : Function.Bijective (φ.val.app U).hom := by
  have h : IsIso (((sheafToPresheaf J AddCommGrpCat.{w'}).map
      ((_root_.SheafOfModules.toSheaf R).map φ)).app U) := inferInstance
  have hb := (ConcreteCategory.isIso_iff_bijective _).1 h
  exact hb

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The `𝒪_F`-modules on the small étale site of an algebraic space have binary biproducts:
the category is preadditive and has binary products. -/
instance smallEtaleModules_hasBinaryBiproducts
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    HasBinaryBiproducts (Modules.{u, u} B S hS F hF) :=
  HasBinaryBiproducts.of_hasBinaryProducts

variable {X Y X' Y' : AlgebraicSpaces B S hS}

/-- A morphism of `𝒪_X`-modules on the small étale site of an algebraic space which is
bijective on the sections over every étale chart is an isomorphism. -/
theorem isIso_of_bijective_app {M N : Modules.{u, u} B S hS X.1 X.2} (c : M ⟶ N)
    (hbij : ∀ U : (SmallEtale B S hS X.1)ᵒᵖ, Function.Bijective (c.val.app U).hom) :
    IsIso c := by
  rw [← isIso_iff_of_reflects_iso c
      (SheafOfModules.toSheaf
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))),
    ← isIso_iff_of_reflects_iso _
      (sheafToPresheaf (smallEtaleRingedSite B S hS X.1 X.2).J AddCommGrpCat.{u}),
    NatTrans.isIso_iff_isIso_app]
  intro U
  rw [ConcreteCategory.isIso_iff_bijective]
  exact hbij U

/-! ### The étale localization of Stacks 04CU for a cartesian square -/

/-- **The étale localization of Stacks 04CU for the comparison map of a cartesian square.**
Over every étale chart `U` of `X'` the sections of `(g')^*Ω_{X/Y}` and of `Ω_{X'/Y'}` are, as
abelian groups, the sections over an open of a scheme of the two sheaves of relative
differentials of a cartesian square of schemes, and the comparison map `c` becomes the
canonical map of Stacks 01UV of that square.

This is the identification `Ω_{X/Y}|_{U_étale} = Ω_{U/V}` of Stacks 04CU, applied to the two
columns of the square and read on sections.  The cartesian square of algebraic spaces is a
parameter because it is what makes the square of schemes over a chart cartesian. -/
def IsEtaleLocalBaseChangeMap (g' : X' ⟶ X) (p' : X' ⟶ Y') (p : X ⟶ Y) (g : Y' ⟶ Y)
    (_h : IsPullback g' p' p g)
    (c : (modulePullback B S hS g').obj (sheafOfDifferentials B S hS p) ⟶
      sheafOfDifferentials B S hS p') : Prop :=
  ∀ U : (SmallEtale B S hS X'.1)ᵒᵖ,
    ∃ (Z' Z W' W : Scheme.{u}) (k : Z' ⟶ Z) (r' : Z' ⟶ W') (r : Z ⟶ W) (l : W' ⟶ W)
      (hk : IsPullback k r' r l) (V : Z'.Opens)
      (α : ((modulePullback B S hS g').obj (sheafOfDifferentials B S hS p)).val.obj U ≃+
        ((Scheme.Modules.pullback k).obj (Scheme.Hom.relativeDifferentials r)).val.obj (op V))
      (β : (sheafOfDifferentials B S hS p').val.obj U ≃+
        (Scheme.Hom.relativeDifferentials r').val.obj (op V)),
      ∀ x, β ((c.val.app U).hom x) =
        ((Scheme.Hom.relativeDifferentialsMap k r r' l hk.w).val.app (op V)).hom (α x)

/-- **The étale localization of Stacks 04CU for the two comparison maps of a fibre product.**
Over every étale chart `U` of `W` the sections of `p^*Ω_{X/T} ⊕ q^*Ω_{Y/T}` and of `Ω_{W/T}`
are, as abelian groups, the sections over an open of a scheme of the corresponding modules of a
cartesian square of schemes, and the map `c` becomes the map of Stacks 01V1 of that square. -/
def IsEtaleLocalFibreProductMap {W T : AlgebraicSpaces B S hS} (p : W ⟶ X) (q : W ⟶ Y)
    (f : X ⟶ T) (g : Y ⟶ T) (_h : IsPullback p q f g)
    (c : ((modulePullback B S hS p).obj (sheafOfDifferentials B S hS f) ⊞
        (modulePullback B S hS q).obj (sheafOfDifferentials B S hS g)) ⟶
      sheafOfDifferentials B S hS (p ≫ f)) : Prop :=
  ∀ U : (SmallEtale B S hS W.1)ᵒᵖ,
    ∃ (Z Z₁ Z₂ Zb : Scheme.{u}) (k₁ : Z ⟶ Z₁) (k₂ : Z ⟶ Z₂) (r₁ : Z₁ ⟶ Zb) (r₂ : Z₂ ⟶ Zb)
      (hk : IsPullback k₁ k₂ r₁ r₂) (V : Z.Opens)
      (α : (((modulePullback B S hS p).obj (sheafOfDifferentials B S hS f) ⊞
          (modulePullback B S hS q).obj (sheafOfDifferentials B S hS g))).val.obj U ≃+
        (((Scheme.Modules.pullback k₁).obj (Scheme.Hom.relativeDifferentials r₁) ⊞
          (Scheme.Modules.pullback k₂).obj
            (Scheme.Hom.relativeDifferentials r₂))).val.obj (op V))
      (β : (sheafOfDifferentials B S hS (p ≫ f)).val.obj U ≃+
        (Scheme.Hom.relativeDifferentials (k₁ ≫ r₁)).val.obj (op V)),
      ∀ x, β ((c.val.app U).hom x) =
        ((biprod.desc
            (Scheme.Hom.relativeDifferentialsMap k₁ r₁ (k₁ ≫ r₁) (𝟙 Zb)
              (Category.comp_id (k₁ ≫ r₁)).symm)
            (Scheme.Hom.relativeDifferentialsMap k₂ r₂ (k₁ ≫ r₁) (𝟙 Zb)
              (hk.w.symm.trans (Category.comp_id (k₁ ≫ r₁)).symm))).val.app (op V)).hom (α x)

/-! ### The two statements -/

/-- A map is bijective if, up to bijections of source and target, it is a bijective map. -/
private theorem bijective_of_comp_equiv_eq {A B C D E₁ E₂ : Type*} [EquivLike E₁ A C]
    [EquivLike E₂ B D] {F : A → B} {G : C → D} (α : E₁) (β : E₂) (hG : Function.Bijective G)
    (h : ∀ x, β (F x) = G (α x)) : Function.Bijective F := by
  have : Function.Bijective fun x => β (F x) := by
    simp only [h]
    exact hG.comp (EquivLike.bijective α)
  exact (Function.Bijective.of_comp_iff' (EquivLike.bijective β) _).1 this

/-- **Stacks 05ZC.**  Let `p : X ⟶ Y` be a morphism of algebraic spaces over `S`, let
`g : Y' ⟶ Y` be a morphism and let `X'`, with its projections `g' : X' ⟶ X` and `p' : X' ⟶ Y'`,
be the base change of `p` by `g`.  Then the comparison map
`c_{g'} : (g')^*Ω_{X/Y} ⟶ Ω_{X'/Y'}` of Stacks 04CX is an isomorphism.

The map is named by the characterizing property of Stacks 04CX, which determines it uniquely by
`AlgebraicGeometry.Space.eq_of_isSheafOfDifferentialsMap`; that uniqueness carries the
étale-local input from the realization `c₀` it is stated for to the realization `c` in hand.
The proof is the source's: over an étale chart the comparison map is the canonical map of a
cartesian square of schemes, which is an isomorphism by Morphisms, Lemma 01V0, and an
isomorphism on the sections over every chart is an isomorphism. -/
@[stacks 05ZC "granted, as `hetale`, the étale localization of 04CU: over each étale chart the
  comparison map is the canonical map 01UV of a cartesian square of schemes.  The scheme case
  01V0 is applied, not granted"]
theorem isIso_of_isSheafOfDifferentialsMap_of_isPullback (g' : X' ⟶ X) (p' : X' ⟶ Y')
    (p : X ⟶ Y) (g : Y' ⟶ Y) (h : IsPullback g' p' p g)
    (c c₀ : (modulePullback B S hS g').obj (sheafOfDifferentials B S hS p) ⟶
      sheafOfDifferentials B S hS p')
    (hc : IsSheafOfDifferentialsMap B S hS g' p p' c)
    (hc₀ : IsSheafOfDifferentialsMap B S hS g' p p' c₀)
    (hetale : IsEtaleLocalBaseChangeMap B S hS g' p' p g h c₀) :
    IsIso c := by
  rw [eq_of_isSheafOfDifferentialsMap B S hS g' p p' hc hc₀]
  refine isIso_of_bijective_app B S hS c₀ fun U => ?_
  obtain ⟨Z', Z, W', W, k, r', r, l, hk, V, α, β, hcomp⟩ := hetale U
  have hiso : IsIso (Scheme.Hom.relativeDifferentialsMap k r r' l hk.w) :=
    Scheme.Hom.isIso_relativeDifferentialsMap_of_isPullback k r' r l hk
  have hb := @Stacks.SheafOfModules.bijective_app_of_isIso _ _ _ _ _ _ _ hiso (op V)
  exact bijective_of_comp_equiv_eq α β hb hcomp

/-- **Stacks 05ZD.**  Let `f : X ⟶ T` and `g : Y ⟶ T` be morphisms of algebraic spaces over `S`
with the same target and let `p : W ⟶ X`, `q : W ⟶ Y` be the projections of a fibre product of
`f` and `g`.  The two comparison maps of Stacks 04CX exhibit `Ω_{W/T}` as the direct sum
`p^*Ω_{X/T} ⊕ q^*Ω_{Y/T}`.

Both summands are named by the characterizing property of Stacks 04CX for the square they come
from — the one with top edge `p` and right edge `f`, and the one with top edge `q` and right
edge `g`, both with left edge the structure morphism `p ≫ f` of `W` — so the conclusion is
about the two comparison maps and not about some decomposition of `Ω_{W/T}`.  As for
Stacks 05ZC the étale localization of Stacks 04CU is granted and Morphisms, Lemma 01V1 is
applied. -/
@[stacks 05ZD "granted, as `hetale`, the étale localization of 04CU: over each étale chart the
  map `p^*Ω_{X/T} ⊕ q^*Ω_{Y/T} ⟶ Ω_{W/T}` is the map 01V1 of a cartesian square of schemes.
  The scheme case 01V1 is applied, not granted"]
theorem isIso_biprodDesc_of_isSheafOfDifferentialsMap {W T : AlgebraicSpaces B S hS}
    (p : W ⟶ X) (q : W ⟶ Y) (f : X ⟶ T) (g : Y ⟶ T) (h : IsPullback p q f g)
    (a a₀ : (modulePullback B S hS p).obj (sheafOfDifferentials B S hS f) ⟶
      sheafOfDifferentials B S hS (p ≫ f))
    (b b₀ : (modulePullback B S hS q).obj (sheafOfDifferentials B S hS g) ⟶
      sheafOfDifferentials B S hS (p ≫ f))
    (ha : IsSheafOfDifferentialsMap B S hS p f (p ≫ f) a)
    (ha₀ : IsSheafOfDifferentialsMap B S hS p f (p ≫ f) a₀)
    (hb : IsSheafOfDifferentialsMap B S hS q g (p ≫ f) b)
    (hb₀ : IsSheafOfDifferentialsMap B S hS q g (p ≫ f) b₀)
    (hetale : IsEtaleLocalFibreProductMap B S hS p q f g h (biprod.desc a₀ b₀)) :
    IsIso (biprod.desc a b) := by
  rw [eq_of_isSheafOfDifferentialsMap B S hS p f (p ≫ f) ha ha₀,
    eq_of_isSheafOfDifferentialsMap B S hS q g (p ≫ f) hb hb₀]
  refine isIso_of_bijective_app B S hS (biprod.desc a₀ b₀) fun U => ?_
  obtain ⟨Z, Z₁, Z₂, Zb, k₁, k₂, r₁, r₂, hk, V, α, β, hcomp⟩ := hetale U
  have hiso : IsIso (biprod.desc
      (Scheme.Hom.relativeDifferentialsMap k₁ r₁ (k₁ ≫ r₁) (𝟙 Zb)
        (Category.comp_id (k₁ ≫ r₁)).symm)
      (Scheme.Hom.relativeDifferentialsMap k₂ r₂ (k₁ ≫ r₁) (𝟙 Zb)
        (hk.w.symm.trans (Category.comp_id (k₁ ≫ r₁)).symm))) :=
    Scheme.Hom.isIso_biprodDesc_relativeDifferentialsMap k₁ k₂ r₁ r₂ hk
  have hbij := @Stacks.SheafOfModules.bijective_app_of_isIso _ _ _ _ _ _ _ hiso (op V)
  exact bijective_of_comp_equiv_eq α β hbij hcomp

end AlgebraicGeometry.Space

end
