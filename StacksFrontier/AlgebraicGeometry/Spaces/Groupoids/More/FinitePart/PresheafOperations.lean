module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.GroupoidTranslate
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.Presheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.Restriction

/-!
# The operations of Stacks 04PI as morphisms of the finite part

Let `f : X ⟶ Y` be a separated morphism of algebraic spaces over a scheme `S`. A section of the
fibre product `(X/Y)_fin ×_Y (X/Y)_fin` over an object `T` of the site is a pair of sections of
the finite part over `T` with the same image in `Y`, that is, a pair of open subspaces of
`T ×_Y X` finite over `T` and lying over one and the same `a : T ⟶ Y`. This file turns the four
operations of Stacks 04PI and the addition of its `F₂`-algebra, each defined on such a pair,
into morphisms of presheaves
`(X/Y)_fin ×_Y (X/Y)_fin ⟶ (X/Y)_fin` over `Y`.

What makes this possible is that the operations commute with restriction of the base: the
restriction maps of the finite part are base change of pairs, so an operation which commutes
with base change is natural, and the morphism is determined by its values on sections.

## Main definitions

* `AlgebraicGeometry.Space.FinitePartPresheaf.fibrewiseMap`: the morphism of presheaves induced
  by an operation on the sections over a fixed morphism to `Y` which commutes with restriction.
* `AlgebraicGeometry.Space.FinitePartPresheaf.star₁Map`,
  `AlgebraicGeometry.Space.FinitePartPresheaf.star₂Map`,
  `AlgebraicGeometry.Space.FinitePartPresheaf.star₃Map`,
  `AlgebraicGeometry.Space.FinitePartPresheaf.star₄Map` and
  `AlgebraicGeometry.Space.FinitePartPresheaf.addMap`: the four operations of Stacks 04PI and
  the addition of the `F₂`-algebra, as morphisms of presheaves.

## Main results

* `AlgebraicGeometry.Space.FinitePartPresheaf.sections_star₁Map` and its three companions, and
  `AlgebraicGeometry.Space.FinitePartPresheaf.sections_addMap`: the value of each morphism on a
  section of the fibre product is the corresponding operation on the two components.
* `AlgebraicGeometry.Space.FinitePartPresheaf.star₁Map_comp_baseMap` and its companions: each
  of these morphisms lies over `Y`.
* `AlgebraicGeometry.Space.FinitePartFibre.toPair_restrict`: the restriction of a section of
  the finite part is the base change of its pair.

## Implementation notes

The construction is the one of
`AlgebraicGeometry.Space.mapOfPullbackSquare`: the morphism is given on sections through the
identification of the sections of the finite part with pairs of Stacks 04PC, and naturality is
`AlgebraicGeometry.Space.FiniteOpenSubspace.IsBaseChange.unique` applied to the base change
which `AlgebraicGeometry.Space.FinitePartPresheaf.map_isBaseChange` supplies.

The operations are fed in through
`AlgebraicGeometry.Space.FinitePartPresheaf.isPairingBaseChangeCompatible_of_restrict`, which
converts the statement that an operation commutes with the restriction of
`AlgebraicGeometry.Space.FinitePartFibre.restrict` into the statement that the corresponding
pairing of pairs commutes with `AlgebraicGeometry.Space.baseChangePair`. The two restrictions
agree because the pair of a restricted section is the base change of its pair.

## References

* [Stacks Project, Tag 04PI](https://stacks.math.columbia.edu/tag/04PI)
* [Stacks Project, Tag 04PC](https://stacks.math.columbia.edu/tag/04PC)
* [Stacks Project, Tag 04PD](https://stacks.math.columbia.edu/tag/04PD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

namespace FinitePartFibre

variable {B S hS f} {T T' : AlgebraicSpaces B S hS} {a : T ⟶ Y}

/-- Two sections of the finite part over `T` lying over `a` with the same pair are equal. -/
theorem ext_toPair {Z W : FinitePartFibre B S hS f a} (h : Z.toPair = W.toPair) : Z = W :=
  (equivFiniteOpenSubspace (B := B) (f := f) a).injective (Subtype.ext h)

/-- The pair of the section of the finite part built from a pair `p` over `a` is `p`. -/
@[simp]
theorem toPair_ofPair {p : FiniteOpenSubspace B S hS f T} (h : p.toBase = a) :
    (ofPair h).toPair = p :=
  congrArg Subtype.val ((equivFiniteOpenSubspace (B := B) (f := f) a).right_inv ⟨p, h⟩)

/-- The restriction of a section of the finite part is the base change of its pair. -/
theorem toPair_restrict (Z : FinitePartFibre B S hS f a) (h : T' ⟶ T) :
    (Z.restrict h).toPair = baseChangePair B S hS f Z.toPair h := rfl

end FinitePartFibre

namespace FinitePartPresheaf

variable {B S hS f} (P : FinitePartPresheaf B S hS f) (hf : IsSeparated B S hS f.hom)

/-- The two components of a section of `(X/Y)_fin ×_Y (X/Y)_fin` have the same image in `Y`. -/
theorem sections_snd_toBase_eq_fst (T : BigFppfOver B S hS)
    (z : (Limits.pullback P.baseMap P.baseMap).obj (op T)) :
    (P.sections T ((Limits.pullback.snd P.baseMap P.baseMap).app (op T) z)).toBase =
      (P.sections T ((Limits.pullback.fst P.baseMap P.baseMap).app (op T) z)).toBase := by
  apply ObjectProperty.hom_ext
  rw [← P.baseMap_spec, ← P.baseMap_spec]
  exact congrArg yonedaEquiv.symm
    (congrArg (fun m : Limits.pullback P.baseMap P.baseMap ⟶ Y.obj => m.app (op T) z)
      Limits.pullback.condition).symm

/-- The pair of a restricted section is the base change of its pair. -/
theorem sections_map_eq_baseChangePair {T T' : (BigFppfOver B S hS)ᵒᵖ} (k : T ⟶ T')
    (p : P.toFunctor.obj T) :
    P.sections T'.unop (P.toFunctor.map k p) =
      baseChangePair B S hS f (P.sections T.unop p) (schemeSpaceMap k.unop) :=
  eq_baseChangePair B S hS f (P.map_isBaseChange k.unop p)

variable
  (opr : ∀ {T : AlgebraicSpaces B S hS} (p q : FiniteOpenSubspace B S hS f T),
    q.toBase = p.toBase → FiniteOpenSubspace B S hS f T)

/-- A pairing of pairs of Stacks 04PC over a common morphism to `Y` is compatible with base
change when it commutes with the base change of pairs. -/
def IsPairingBaseChangeCompatible : Prop :=
  ∀ {T T' : AlgebraicSpaces B S hS} (p q : FiniteOpenSubspace B S hS f T)
    (hpq : q.toBase = p.toBase) (h : T' ⟶ T),
    baseChangePair B S hS f (opr p q hpq) h =
      opr (baseChangePair B S hS f p h) (baseChangePair B S hS f q h)
        (by rw [baseChangePair_toBase, baseChangePair_toBase, hpq])

variable (hopr : IsPairingBaseChangeCompatible opr)

/-- A pairing of pairs of Stacks 04PC which is compatible with base change defines a morphism
of presheaves from the fibre product of the finite part with itself over `Y`. -/
def pairingMap : Limits.pullback P.baseMap P.baseMap ⟶ P.toFunctor where
  app T := ↾fun z => (P.sections T.unop).symm
    (opr (P.sections T.unop ((Limits.pullback.fst P.baseMap P.baseMap).app T z))
      (P.sections T.unop ((Limits.pullback.snd P.baseMap P.baseMap).app T z))
      (P.sections_snd_toBase_eq_fst T.unop z))
  naturality := by
    have key : ∀ {T₀ : AlgebraicSpaces B S hS} (p p' q q' : FiniteOpenSubspace B S hS f T₀)
        (_ : p = p') (_ : q = q') (h : q.toBase = p.toBase) (h' : q'.toBase = p'.toBase),
        opr p q h = opr p' q' h' := by
      rintro T₀ p p' q q' rfl rfl h h'
      rfl
    intro T T' k
    ext z
    apply (P.sections T'.unop).injective
    change P.sections T'.unop ((P.sections T'.unop).symm (opr _ _ _)) =
      P.sections T'.unop (P.toFunctor.map k ((P.sections T.unop).symm (opr _ _ _)))
    rw [Equiv.apply_symm_apply, P.sections_map_eq_baseChangePair k,
      Equiv.apply_symm_apply, hopr]
    refine key _ _ _ _ ?_ ?_ _ _
    · rw [← P.sections_map_eq_baseChangePair k]
      exact congrArg (P.sections T'.unop)
        (NatTrans.naturality_apply (Limits.pullback.fst P.baseMap P.baseMap) k z)
    · rw [← P.sections_map_eq_baseChangePair k]
      exact congrArg (P.sections T'.unop)
        (NatTrans.naturality_apply (Limits.pullback.snd P.baseMap P.baseMap) k z)

/-- The pair of the value of the pairing morphism. -/
theorem sections_pairingMap (T : BigFppfOver B S hS)
    (z : (Limits.pullback P.baseMap P.baseMap).obj (op T)) :
    P.sections T ((pairingMap P opr hopr).app (op T) z) =
      opr (P.sections T ((Limits.pullback.fst P.baseMap P.baseMap).app (op T) z))
        (P.sections T ((Limits.pullback.snd P.baseMap P.baseMap).app (op T) z))
        (P.sections_snd_toBase_eq_fst T z) :=
  Equiv.apply_symm_apply _ _

/-- A pairing morphism out of the fibre product is a morphism over `Y` as soon as the pairing
keeps the morphism to `Y` of its first argument. -/
theorem pairingMap_comp_baseMap
    (hbase : ∀ {T : AlgebraicSpaces B S hS} (p q : FiniteOpenSubspace B S hS f T)
      (hpq : q.toBase = p.toBase), (opr p q hpq).toBase = p.toBase) :
    pairingMap P opr hopr ≫ P.baseMap =
      Limits.pullback.fst P.baseMap P.baseMap ≫ P.baseMap := by
  ext T z
  apply yonedaEquiv.symm.injective
  change yonedaEquiv.symm (P.baseMap.app T ((pairingMap P opr hopr).app T z)) =
    yonedaEquiv.symm (P.baseMap.app T ((Limits.pullback.fst P.baseMap P.baseMap).app T z))
  rw [P.baseMap_spec, P.baseMap_spec, sections_pairingMap]
  exact congrArg (fun m : schemeSpace T.unop ⟶ Y => m.hom) (hbase _ _ _)

/-- A fibrewise operation on the sections of the finite part which commutes with restriction
gives a pairing of pairs of Stacks 04PC compatible with base change. -/
theorem isPairingBaseChangeCompatible_of_restrict
    (opr : ∀ {T : AlgebraicSpaces B S hS} {a : T ⟶ Y}, FinitePartFibre B S hS f a →
      FinitePartFibre B S hS f a → FinitePartFibre B S hS f a)
    (hres : ∀ {T T' : AlgebraicSpaces B S hS} {a : T ⟶ Y} (h : T' ⟶ T)
      (Z₁ Z₂ : FinitePartFibre B S hS f a),
      (opr Z₁ Z₂).restrict h = opr (Z₁.restrict h) (Z₂.restrict h)) :
    IsPairingBaseChangeCompatible (fun p _ hpq =>
      (opr (FinitePartFibre.ofPair (rfl : p.toBase = p.toBase))
        (FinitePartFibre.ofPair hpq)).toPair) := by
  intro T T' p q hpq h
  have hW₁ : (FinitePartFibre.ofPair (rfl : p.toBase = p.toBase)).restrict h =
      FinitePartFibre.ofPair
        (rfl : (baseChangePair B S hS f p h).toBase = h ≫ p.toBase) :=
    FinitePartFibre.ext_toPair (by
      rw [FinitePartFibre.toPair_restrict, FinitePartFibre.toPair_ofPair]
      exact (FinitePartFibre.toPair_ofPair _).symm)
  have hW₂ : (FinitePartFibre.ofPair hpq).restrict h =
      FinitePartFibre.ofPair
        (show (baseChangePair B S hS f q h).toBase = h ≫ p.toBase by
          rw [baseChangePair_toBase, hpq]) :=
    FinitePartFibre.ext_toPair (by simp [FinitePartFibre.toPair_restrict])
  calc baseChangePair B S hS f
        (opr (FinitePartFibre.ofPair (rfl : p.toBase = p.toBase))
          (FinitePartFibre.ofPair hpq)).toPair h
      = ((opr (FinitePartFibre.ofPair (rfl : p.toBase = p.toBase))
          (FinitePartFibre.ofPair hpq)).restrict h).toPair :=
        (FinitePartFibre.toPair_restrict _ _).symm
    _ = (opr ((FinitePartFibre.ofPair (rfl : p.toBase = p.toBase)).restrict h)
          ((FinitePartFibre.ofPair hpq).restrict h)).toPair := by rw [hres]
    _ = _ := by
        rw [hW₁, hW₂]
        rfl

/-- The morphism of presheaves from the fibre product of the finite part with itself over `Y`
given on sections by a fibrewise operation which commutes with restriction. -/
def fibrewiseMap
    (opr : ∀ {T : AlgebraicSpaces B S hS} {a : T ⟶ Y}, FinitePartFibre B S hS f a →
      FinitePartFibre B S hS f a → FinitePartFibre B S hS f a)
    (hres : ∀ {T T' : AlgebraicSpaces B S hS} {a : T ⟶ Y} (h : T' ⟶ T)
      (Z₁ Z₂ : FinitePartFibre B S hS f a),
      (opr Z₁ Z₂).restrict h = opr (Z₁.restrict h) (Z₂.restrict h)) :
    Limits.pullback P.baseMap P.baseMap ⟶ P.toFunctor :=
  pairingMap P _ (isPairingBaseChangeCompatible_of_restrict opr hres)

/-- On sections, the morphism induced by a fibrewise operation is that operation. -/
theorem sections_fibrewiseMap
    (opr : ∀ {T : AlgebraicSpaces B S hS} {a : T ⟶ Y}, FinitePartFibre B S hS f a →
      FinitePartFibre B S hS f a → FinitePartFibre B S hS f a)
    (hres : ∀ {T T' : AlgebraicSpaces B S hS} {a : T ⟶ Y} (h : T' ⟶ T)
      (Z₁ Z₂ : FinitePartFibre B S hS f a),
      (opr Z₁ Z₂).restrict h = opr (Z₁.restrict h) (Z₂.restrict h))
    (T : BigFppfOver B S hS) (z : (Limits.pullback P.baseMap P.baseMap).obj (op T)) :
    P.sections T ((fibrewiseMap P opr hres).app (op T) z) =
      (opr (FinitePartFibre.ofPair rfl)
        (FinitePartFibre.ofPair (P.sections_snd_toBase_eq_fst T z))).toPair :=
  Equiv.apply_symm_apply _ _

/-- The morphism induced by a fibrewise operation is a morphism over `Y`. -/
theorem fibrewiseMap_comp_baseMap
    (opr : ∀ {T : AlgebraicSpaces B S hS} {a : T ⟶ Y}, FinitePartFibre B S hS f a →
      FinitePartFibre B S hS f a → FinitePartFibre B S hS f a)
    (hres : ∀ {T T' : AlgebraicSpaces B S hS} {a : T ⟶ Y} (h : T' ⟶ T)
      (Z₁ Z₂ : FinitePartFibre B S hS f a),
      (opr Z₁ Z₂).restrict h = opr (Z₁.restrict h) (Z₂.restrict h)) :
    fibrewiseMap P opr hres ≫ P.baseMap =
      Limits.pullback.fst P.baseMap P.baseMap ≫ P.baseMap :=
  pairingMap_comp_baseMap P _ (isPairingBaseChangeCompatible_of_restrict opr hres)
    fun _ _ _ => rfl

/-- **Stacks 04PI, the operation `⋆₁`.** The morphism of presheaves
`⋆₁ : (X/Y)_fin ×_Y (X/Y)_fin ⟶ (X/Y)_fin` sending a pair of sections over a common morphism
to `Y` to the union `Z₁ ∪ Z₂`. -/
@[stacks 04PI "star_1_as_a_morphism_of_sheaves"]
def star₁Map : Limits.pullback P.baseMap P.baseMap ⟶ P.toFunctor :=
  fibrewiseMap P (fun Z₁ Z₂ => FinitePartFibre.star₁ hf Z₁ Z₂)
    (fun h Z₁ Z₂ => FinitePartFibre.restrict_star₁ hf Z₁ Z₂ h)

/-- **Stacks 04PI, the operation `⋆₁`.** On sections, `⋆₁` is the union `Z₁ ∪ Z₂`. -/
@[stacks 04PI "star_1_morphism_on_sections"]
theorem sections_star₁Map (T : BigFppfOver B S hS)
    (z : (Limits.pullback P.baseMap P.baseMap).obj (op T)) :
    P.sections T ((star₁Map P hf).app (op T) z) =
      (FinitePartFibre.star₁ hf (FinitePartFibre.ofPair rfl)
        (FinitePartFibre.ofPair (P.sections_snd_toBase_eq_fst T z))).toPair :=
  sections_fibrewiseMap P _ _ T z

/-- **Stacks 04PI, the operation `⋆₁`.** It is a morphism over `Y`. -/
@[stacks 04PI "star_1_is_a_morphism_over_the_base"]
theorem star₁Map_comp_baseMap :
    star₁Map P hf ≫ P.baseMap = Limits.pullback.fst P.baseMap P.baseMap ≫ P.baseMap :=
  fibrewiseMap_comp_baseMap P _ _

/-- **Stacks 04PI, the operation `⋆₂`.** The morphism of presheaves
`⋆₂ : (X/Y)_fin ×_Y (X/Y)_fin ⟶ (X/Y)_fin` sending a pair of sections over a common morphism
to `Y` to the intersection `Z₁ ∩ Z₂`. -/
@[stacks 04PI "star_2_as_a_morphism_of_sheaves"]
def star₂Map : Limits.pullback P.baseMap P.baseMap ⟶ P.toFunctor :=
  fibrewiseMap P (fun Z₁ Z₂ => FinitePartFibre.star₂ hf Z₁ Z₂)
    (fun h Z₁ Z₂ => FinitePartFibre.restrict_star₂ hf Z₁ Z₂ h)

/-- **Stacks 04PI, the operation `⋆₂`.** On sections, `⋆₂` is the intersection `Z₁ ∩ Z₂`. -/
@[stacks 04PI "star_2_morphism_on_sections"]
theorem sections_star₂Map (T : BigFppfOver B S hS)
    (z : (Limits.pullback P.baseMap P.baseMap).obj (op T)) :
    P.sections T ((star₂Map P hf).app (op T) z) =
      (FinitePartFibre.star₂ hf (FinitePartFibre.ofPair rfl)
        (FinitePartFibre.ofPair (P.sections_snd_toBase_eq_fst T z))).toPair :=
  sections_fibrewiseMap P _ _ T z

/-- **Stacks 04PI, the operation `⋆₂`.** It is a morphism over `Y`. -/
@[stacks 04PI "star_2_is_a_morphism_over_the_base"]
theorem star₂Map_comp_baseMap :
    star₂Map P hf ≫ P.baseMap = Limits.pullback.fst P.baseMap P.baseMap ≫ P.baseMap :=
  fibrewiseMap_comp_baseMap P _ _

/-- **Stacks 04PI, the operation `⋆₃`.** The morphism of presheaves
`⋆₃ : (X/Y)_fin ×_Y (X/Y)_fin ⟶ (X/Y)_fin` sending a pair of sections over a common morphism
to `Y` to the difference `Z₁ ∖ Z₂`. -/
@[stacks 04PI "star_3_as_a_morphism_of_sheaves"]
def star₃Map : Limits.pullback P.baseMap P.baseMap ⟶ P.toFunctor :=
  fibrewiseMap P (fun Z₁ Z₂ => FinitePartFibre.star₃ hf Z₁ Z₂)
    (fun h Z₁ Z₂ => FinitePartFibre.restrict_star₃ hf Z₁ Z₂ h)

/-- **Stacks 04PI, the operation `⋆₃`.** On sections, `⋆₃` is the difference `Z₁ ∖ Z₂`. -/
@[stacks 04PI "star_3_morphism_on_sections"]
theorem sections_star₃Map (T : BigFppfOver B S hS)
    (z : (Limits.pullback P.baseMap P.baseMap).obj (op T)) :
    P.sections T ((star₃Map P hf).app (op T) z) =
      (FinitePartFibre.star₃ hf (FinitePartFibre.ofPair rfl)
        (FinitePartFibre.ofPair (P.sections_snd_toBase_eq_fst T z))).toPair :=
  sections_fibrewiseMap P _ _ T z

/-- **Stacks 04PI, the operation `⋆₃`.** It is a morphism over `Y`. -/
@[stacks 04PI "star_3_is_a_morphism_over_the_base"]
theorem star₃Map_comp_baseMap :
    star₃Map P hf ≫ P.baseMap = Limits.pullback.fst P.baseMap P.baseMap ≫ P.baseMap :=
  fibrewiseMap_comp_baseMap P _ _

/-- **Stacks 04PI, the operation `⋆₄`.** The morphism of presheaves
`⋆₄ : (X/Y)_fin ×_Y (X/Y)_fin ⟶ (X/Y)_fin` sending a pair of sections over a common morphism
to `Y` to the difference `Z₂ ∖ Z₁`. -/
@[stacks 04PI "star_4_as_a_morphism_of_sheaves"]
def star₄Map : Limits.pullback P.baseMap P.baseMap ⟶ P.toFunctor :=
  fibrewiseMap P (fun Z₁ Z₂ => FinitePartFibre.star₄ hf Z₁ Z₂)
    (fun h Z₁ Z₂ => FinitePartFibre.restrict_star₄ hf Z₁ Z₂ h)

/-- **Stacks 04PI, the operation `⋆₄`.** On sections, `⋆₄` is the difference `Z₂ ∖ Z₁`. -/
@[stacks 04PI "star_4_morphism_on_sections"]
theorem sections_star₄Map (T : BigFppfOver B S hS)
    (z : (Limits.pullback P.baseMap P.baseMap).obj (op T)) :
    P.sections T ((star₄Map P hf).app (op T) z) =
      (FinitePartFibre.star₄ hf (FinitePartFibre.ofPair rfl)
        (FinitePartFibre.ofPair (P.sections_snd_toBase_eq_fst T z))).toPair :=
  sections_fibrewiseMap P _ _ T z

/-- **Stacks 04PI, the operation `⋆₄`.** It is a morphism over `Y`. -/
@[stacks 04PI "star_4_is_a_morphism_over_the_base"]
theorem star₄Map_comp_baseMap :
    star₄Map P hf ≫ P.baseMap = Limits.pullback.fst P.baseMap P.baseMap ≫ P.baseMap :=
  fibrewiseMap_comp_baseMap P _ _

/-- **Stacks 04PI.** The addition of the `F₂`-algebra as a morphism of presheaves
`(X/Y)_fin ×_Y (X/Y)_fin ⟶ (X/Y)_fin`. -/
@[stacks 04PI "addition_as_a_morphism_of_sheaves"]
def addMap : Limits.pullback P.baseMap P.baseMap ⟶ P.toFunctor :=
  fibrewiseMap P (fun Z₁ Z₂ => FinitePartFibre.add hf Z₁ Z₂)
    (fun h Z₁ Z₂ => FinitePartFibre.restrict_add hf Z₁ Z₂ h)

/-- **Stacks 04PI.** On sections, the addition is `⋆₁(⋆₃(s, s'), ⋆₄(s, s'))`. -/
@[stacks 04PI "addition_morphism_on_sections"]
theorem sections_addMap (T : BigFppfOver B S hS)
    (z : (Limits.pullback P.baseMap P.baseMap).obj (op T)) :
    P.sections T ((addMap P hf).app (op T) z) =
      (FinitePartFibre.add hf (FinitePartFibre.ofPair rfl)
        (FinitePartFibre.ofPair (P.sections_snd_toBase_eq_fst T z))).toPair :=
  sections_fibrewiseMap P _ _ T z

/-- **Stacks 04PI.** The addition of the `F₂`-algebra is a morphism over `Y`. -/
@[stacks 04PI "addition_is_a_morphism_over_the_base"]
theorem addMap_comp_baseMap :
    addMap P hf ≫ P.baseMap = Limits.pullback.fst P.baseMap P.baseMap ≫ P.baseMap :=
  fibrewiseMap_comp_baseMap P _ _

end FinitePartPresheaf

end AlgebraicGeometry.Space

end
