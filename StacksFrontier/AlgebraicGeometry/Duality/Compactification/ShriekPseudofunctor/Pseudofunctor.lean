module

public import StacksFrontier.AlgebraicGeometry.Duality.Compactification.ShriekPseudofunctor.Cocycle
public import StacksFrontier.AlgebraicGeometry.NagataCompactification.Basic
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Exceptional inverse image is a pseudofunctor (Tag 0ATY): the pseudofunctor

* `Stacks.Duality.upperShriekPseudofunctor` — the pseudofunctor
  `LocallyDiscrete (FTS S)ᵒᵖ ⥤ᵖ Cat`, built with `CategoryTheory.LocallyDiscrete.mkPseudofunctor`
  from `X ↦ D⁺_QCoh(𝒪_X)`, `f ↦ f^!`, the compositor of [Stacks, Tag 0ATX] and the unit
  determined by it; its axioms are `Stacks.Duality.shriekMapComp_assoc`,
  `Stacks.Duality.shriekMapComp_id_left` and `Stacks.Duality.shriekMapComp_id_right`.
* `Stacks.Duality.exists_upperShriekPseudofunctor` — the statement of [Stacks, Tag 0ATY].

## References

* [Stacks Project, Tag 0ATY](https://stacks.math.columbia.edu/tag/0ATY)
* [Stacks Project, Tag 0ATX](https://stacks.math.columbia.edu/tag/0ATX)
* [Stacks Project, Tag 0AA0](https://stacks.math.columbia.edu/tag/0AA0)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

universe u

/-! ### The pseudofunctor -/

namespace Stacks.Duality

open CategoryTheory.Bicategory

variable (S : Scheme.{u}) [IsNoetherian S]

variable {S} in
/-- **Every morphism of `FTS S` has a compactification**: Nagata's theorem, More on Flatness,
Theorem 0F41, for the separated morphism of finite type `f` with quasi-compact quasi-separated
target. -/
theorem nonempty_compactificationOf {X Y : FTS S} (f : X ⟶ Y) :
    Nonempty (CompactificationOf (Over.mk f.left)) := by
  have : QuasiCompact f.left := quasiCompact_of_compactSpace _
  obtain ⟨j, -⟩ := hasCompactification_of_compactSpace_quasiSeparatedSpace f.left
  exact ⟨j⟩

variable {S} in
/-- A chosen compactification of each morphism of `FTS S`; which one does not matter, by
[Stacks, Tag 0AA0]. -/
noncomputable def chosenCompactification {X Y : FTS S} (f : X ⟶ Y) :
    CompactificationOf (Over.mk f.left) :=
  Classical.choice (nonempty_compactificationOf f)

variable {S} in
/-- `X` itself, as a compactification of the identity of `X`. -/
noncomputable def idCompactification (X : FTS S) :
    CompactificationOf (Over.mk (𝟙 X : X ⟶ X).left) :=
  CompactificationOf.ofFactorization X.left (𝟙 X.left) (𝟙 X.left) (Category.comp_id _)

variable {S} in
/-- **`(𝟙_X)^! ≅ id`** on `D⁺_QCoh(𝒪_X)`, for the compactification `X` of the identity: the
twisted inverse image and the derived pullback along the identity are the identity. -/
noncomputable def upperShriekPlusAtModelIdIso (X : FTS S) :
    upperShriekPlusAtModel (idCompactification X) ≅ 𝟭 _ :=
  liftIsoOf (isBoundedBelowQuasiCoherentAtModel X.left)
      (isBoundedBelow_compactificationUpperShriek_obj (idCompactification X))
      (F₂ := ObjectProperty.ι (isBoundedBelowQuasiCoherentAtModel X.left)) (fun K => K.property)
      ((isoWhiskerLeft (ObjectProperty.ι (isBoundedBelowQuasiCoherentAtModel X.left))
        (isoWhiskerRight (idN X.left) (pb (𝟙 X.left)) ≪≫ Functor.leftUnitor _ ≪≫
          quasiCoherentDerivedPullbackIdIso X.left _) ≪≫ Functor.rightUnitor _ :
        compactificationUpperShriek (𝟙 X) (idCompactification X) ≅ _)) ≪≫
    NatIso.ofComponents (fun K => ObjectProperty.isoMk _ (Iso.refl _)) (fun _ =>
      ObjectProperty.hom_ext _ (by simp))

variable {S} in
/-- **`(𝟙_X)^! ≅ id`** on `D⁺_QCoh(𝒪_X)` for the chosen compactification of the identity, through
the comparison of [Stacks, Tag 0AA0] with the compactification `X` of the identity. -/
noncomputable def chosenUpperShriekPlusIdIso (X : FTS S) :
    upperShriekPlusAtModel (chosenCompactification (𝟙 X)) ≅ 𝟭 _ :=
  basePlusIsoAPI (chosenCompactification (𝟙 X)) (idCompactification X) ≪≫
      upperShriekPlusAtModelIdIso X

local notation "cc" => chosenCompactification

variable {S} in
/-- The category `D⁺_QCoh(𝒪_X)` of an object of `(FTS S)ᵒᵖ`, as an object of `Cat`. -/
abbrev shriekObj (X : (FTS S)ᵒᵖ) : Cat.{u, u + 1} :=
  Cat.of (quasiCoherentDerivedCategoryPlusAtModel X.unop.left)

variable {S} in
/-- `f^! : D⁺_QCoh(𝒪_Y) ⥤ D⁺_QCoh(𝒪_X)` at the chosen compactification, as a morphism of `Cat`. -/
abbrev shriekMap {X Y : (FTS S)ᵒᵖ} (f : X ⟶ Y) : shriekObj X ⟶ shriekObj Y :=
  (upperShriekPlusAtModel (cc f.unop)).toCatHom

variable {S} in
/-- The isomorphism `(g ∘ f)^! ≅ f^! ∘ g^!` of [Stacks, Tag 0ATX], as a 2-isomorphism of `Cat`. -/
abbrev shriekMapComp {X Y Z : (FTS S)ᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    shriekMap (f ≫ g) ≅ shriekMap f ≫ shriekMap g :=
  Cat.Hom.isoMk (upperShriekCompIsoAtModelPlus (cc (g.unop ≫ f.unop)) (cc g.unop) (cc f.unop))

variable {S} in
/-- The unit `(𝟙_X)^! ≅ id` determined by the compositor of `𝟙_X`, as a 2-isomorphism of `Cat`. -/
abbrev shriekMapId (X : (FTS S)ᵒᵖ) : shriekMap (𝟙 X) ≅ 𝟙 _ :=
  Cat.Hom.isoMk (unitOf
    (upperShriekCompIsoAtModelPlus (g := 𝟙 X.unop) (h := 𝟙 X.unop) (cc (𝟙 X.unop)) (cc (𝟙 X.unop))
      (cc (𝟙 X.unop)))
    (chosenUpperShriekPlusIdIso X.unop))

variable {S} in
/-- **The cocycle condition (d)** of a pseudofunctor for `f ↦ f^!`. -/
theorem shriekMapComp_assoc {A B C D : (FTS S)ᵒᵖ} (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) :
    (shriekMapComp (f ≫ g) h).hom ≫ (shriekMapComp f g).hom ▷ shriekMap h ≫
        (α_ (shriekMap f) (shriekMap g) (shriekMap h)).hom ≫
          shriekMap f ◁ (shriekMapComp g h).inv ≫ (shriekMapComp f (g ≫ h)).inv =
      eqToHom (by simp) :=
  (catAssoc (isBoundedBelowQuasiCoherentAtModel D.unop.left)
    (isBoundedBelow_compactificationUpperShriek_obj (cc h.unop))
    (isBoundedBelow_compactificationUpperShriek_obj (cc (h.unop ≫ g.unop)))
    (isBoundedBelow_compactificationUpperShriek_obj (cc (h.unop ≫ g.unop ≫ f.unop)))
    (upperShriekCompIsoAtModel (cc (h.unop ≫ g.unop ≫ f.unop)) (cc h.unop) (cc (g.unop ≫ f.unop)))
    (upperShriekCompIsoAtModelPlus (cc (g.unop ≫ f.unop)) (cc g.unop) (cc f.unop))
    (upperShriekCompIsoAtModel (f := h.unop ≫ g.unop) (g := f.unop) (cc (h.unop ≫ g.unop ≫ f.unop))
      (cc (h.unop ≫ g.unop)) (cc f.unop))
    (upperShriekCompIsoAtModel (cc (h.unop ≫ g.unop)) (cc h.unop) (cc g.unop))
    (upperShriekCompIsoAtModel_cocycle (cc (h.unop ≫ g.unop ≫ f.unop)) (cc h.unop)
      (cc (g.unop ≫ f.unop)) (cc g.unop) (cc f.unop) (cc (h.unop ≫ g.unop)))).trans
    (eqToHom_refl _ _).symm

variable {S} in
/-- **The left unit condition (b)** of a pseudofunctor for `f ↦ f^!`. -/
theorem shriekMapComp_id_left {A B : (FTS S)ᵒᵖ} (f : A ⟶ B) :
    (shriekMapComp (𝟙 A) f).hom ≫ (shriekMapId A).hom ▷ shriekMap f ≫
        (λ_ (shriekMap f)).hom = eqToHom (by simp) :=
  (catLeft (isBoundedBelowQuasiCoherentAtModel B.unop.left)
    (isBoundedBelow_compactificationUpperShriek_obj (cc f.unop))
    (upperShriekCompIsoAtModelPlus (g := 𝟙 A.unop) (h := 𝟙 A.unop) (cc (𝟙 A.unop)) (cc (𝟙 A.unop))
      (cc (𝟙 A.unop)))
    (chosenUpperShriekPlusIdIso A.unop)
    (upperShriekCompIsoAtModel (f := f.unop) (g := 𝟙 A.unop) (cc f.unop) (cc f.unop)
        (cc (𝟙 A.unop)))
    (upperShriekCompIsoAtModel_cocycle (f := f.unop) (g := 𝟙 A.unop) (h := 𝟙 A.unop) (cc f.unop)
      (cc f.unop) (cc (𝟙 A.unop)) (cc (𝟙 A.unop)) (cc (𝟙 A.unop)) (cc f.unop))).trans
    (eqToHom_refl _ _).symm

variable {S} in
/-- **The right unit condition (c)** of a pseudofunctor for `f ↦ f^!`. -/
theorem shriekMapComp_id_right {A B : (FTS S)ᵒᵖ} (f : A ⟶ B) :
    (shriekMapComp f (𝟙 B)).hom ≫ shriekMap f ◁ (shriekMapId B).hom ≫
        (ρ_ (shriekMap f)).hom = eqToHom (by simp) :=
  (catRight (isBoundedBelowQuasiCoherentAtModel B.unop.left)
    (isBoundedBelow_compactificationUpperShriek_obj (cc f.unop))
    (isBoundedBelow_compactificationUpperShriek_obj (cc (𝟙 B.unop)))
    (upperShriekCompIsoAtModel (f := 𝟙 B.unop) (g := 𝟙 B.unop) (cc (𝟙 B.unop)) (cc (𝟙 B.unop))
      (cc (𝟙 B.unop)))
    (chosenUpperShriekPlusIdIso B.unop)
    (upperShriekCompIsoAtModel (f := 𝟙 B.unop) (g := f.unop) (cc f.unop) (cc (𝟙 B.unop))
        (cc f.unop))
    (upperShriekCompIsoAtModel_cocycle (f := 𝟙 B.unop) (g := 𝟙 B.unop) (h := f.unop) (cc f.unop)
      (cc (𝟙 B.unop)) (cc f.unop) (cc (𝟙 B.unop)) (cc f.unop) (cc (𝟙 B.unop)))).trans
    (eqToHom_refl _ _).symm

/-- **[Stacks, Tag 0ATY]: exceptional inverse image is a pseudofunctor.** In Situation 0F42 (a
Noetherian base `S` and the category `FTS S` of schemes separated and of finite type over `S`),
the constructions of [Stacks, Tag 0AA0] and [Stacks, Tag 0ATX] define a pseudofunctor from
`FTS S`, contravariantly, into the 2-category of categories: an object `X` goes to
`D⁺_QCoh(𝒪_X)`, a morphism `f` to the functor `f^!` of [Stacks, Tag 0AA0] at a chosen
compactification (`Stacks.Duality.shriekMap`), a composable pair to the canonical isomorphism
`(g ∘ f)^! ≅ f^! ∘ g^!` of [Stacks, Tag 0ATX] (`Stacks.Duality.shriekMapComp`, the lift to
`D⁺_QCoh` of `Stacks.Duality.upperShriekCompIsoAtModel`), and an object to the unit
`(𝟙_X)^! ≅ id` determined by the compositor of `𝟙_X` (`Stacks.Duality.shriekMapId`). The four
conditions of Categories, Definition 003N: (a) all are isomorphisms (they are `Iso`s);
(d) the cocycle condition, `Stacks.Duality.shriekMapComp_assoc`, which is the source's proof
`Stacks.Duality.upperShriekCompIsoAtModel_cocycle`; (b), (c) the unit conditions,
`Stacks.Duality.shriekMapComp_id_left` and `Stacks.Duality.shriekMapComp_id_right`. -/
@[sga "5 III 6.1"]
noncomputable def upperShriekPseudofunctor :
    LocallyDiscrete (FTS S)ᵒᵖ ⥤ᵖ Cat.{u, u + 1} :=
  LocallyDiscrete.mkPseudofunctor shriekObj shriekMap shriekMapId shriekMapComp
    shriekMapComp_assoc shriekMapComp_id_left shriekMapComp_id_right

/-- The pseudofunctor sends `X` to `D⁺_QCoh(𝒪_X)`. -/
theorem upperShriekPseudofunctor_obj (X : (FTS S)ᵒᵖ) :
    (upperShriekPseudofunctor S).obj ⟨X⟩ =
      Cat.of (quasiCoherentDerivedCategoryPlusAtModel X.unop.left) := rfl

/-- The pseudofunctor sends `f` to `f^!` of [Stacks, Tag 0AA0] at the chosen compactification. -/
theorem upperShriekPseudofunctor_map {X Y : (FTS S)ᵒᵖ} (f : X ⟶ Y) :
    ((upperShriekPseudofunctor S).map ⟨f⟩).toFunctor = upperShriekPlusAtModel (cc f.unop) := rfl

/-- The compositor of the pseudofunctor is the canonical isomorphism of [Stacks, Tag 0ATX]. -/
theorem upperShriekPseudofunctor_mapComp {X Y Z : (FTS S)ᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Cat.Hom.toNatIso ((upperShriekPseudofunctor S).mapComp ⟨f⟩ ⟨g⟩) =
      upperShriekCompIsoAtModelPlus (cc (g.unop ≫ f.unop)) (cc g.unop) (cc f.unop) := rfl

/-- **[Stacks, Tag 0ATY]**: in Situation 0F42 the constructions of [Stacks, Tag 0AA0] and
[Stacks, Tag 0ATX] define a pseudofunctor from `FTS S` into the 2-category of categories: there
is a pseudofunctor `(FTS S)ᵒᵖ ⥤ᵖ Cat` whose value at `X` is `D⁺_QCoh(𝒪_X)`, whose value at `f`
is the upper shriek functor `f^!` of [Stacks, Tag 0AA0] (at a compactification of `f`, which
exists by More on Flatness, Theorem 0F41; by [Stacks, Tag 0AA0] the choice does not matter up to
canonical isomorphism), and whose compositor at `f`, `g` is the canonical isomorphism
`(g ∘ f)^! ≅ f^! ∘ g^!` of [Stacks, Tag 0ATX]. It is `Stacks.Duality.upperShriekPseudofunctor`;
the axioms of a pseudofunctor are the conditions (a)–(d) of Categories, Definition 003N. -/
@[stacks 0ATY "the full statement: Stacks.Duality.upperShriekPseudofunctor is a pseudofunctor \
  LocallyDiscrete (FTS S)^op -> Cat (Mathlib's Pseudofunctor, i.e. Categories 003N with \
  conditions (a) invertibility, (b), (c) unit laws and (d) cocycle condition as its axioms) over \
  a Noetherian S, with object X |-> D^+_QCoh(O_X), morphism f |-> f^! of Stacks 0AA0 (the \
  functor Stacks.Duality.compactificationUpperShriek of a compactification of f, read in \
  D^+_QCoh, Stacks 0A9I; compactifications exist by Stacks 0F41) and compositor the canonical \
  isomorphism (g o f)^! = f^! o g^! of Stacks 0ATX (Stacks.Duality.upperShriekCompIsoAtModel). The \
  cocycle condition (d) is the source's proof, Stacks.Duality.upperShriekCompIsoAtModel_cocycle: a \
  choice Zbar over T, Ybar over Zbar, Xbar over Ybar (0F41, 0A9Z), the squares A, B, C, and \
  gamma_{A+B} = gamma_A o gamma_B (0ATR), gamma_{B+C} = gamma_C o gamma_B (0ATQ), gamma_A and \
  gamma_C commuting by naturality. The unit (1_X)^! = id, which the source does not specify, is \
  the one determined by the compositor of 1_X, and (b), (c) follow from (d). Nothing is assumed"]
theorem exists_upperShriekPseudofunctor :
    ∃ P : LocallyDiscrete (FTS S)ᵒᵖ ⥤ᵖ Cat.{u, u + 1},
      ∃ hobj : ∀ X : (FTS S)ᵒᵖ,
          P.obj ⟨X⟩ = Cat.of (quasiCoherentDerivedCategoryPlusAtModel X.unop.left),
        (∀ {X Y : (FTS S)ᵒᵖ} (f : X ⟶ Y),
          eqToHom (hobj X).symm ≫ P.map ⟨f⟩ ≫ eqToHom (hobj Y) =
            (upperShriekPlusAtModel (cc f.unop)).toCatHom) ∧
        (∀ {X Y Z : (FTS S)ᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z),
          HEq (Cat.Hom.toNatIso (P.mapComp ⟨f⟩ ⟨g⟩))
            (upperShriekCompIsoAtModelPlus (cc (g.unop ≫ f.unop)) (cc g.unop) (cc f.unop))) :=
  ⟨upperShriekPseudofunctor S, fun _ => rfl, fun f => by simp; rfl, fun _ _ => HEq.rfl⟩

end Stacks.Duality

end
