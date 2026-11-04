module

public import StacksFrontier.AlgebraicGeometry.Conormal.RestrictSquareMap
public import StacksFrontier.AlgebraicGeometry.Conormal.RestrictIdealSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSquareComparisonUnit
public import StacksFrontier.AlgebraicGeometry.Thickenings.ConormalSequenceIdealForm
public import StacksFrontier.AlgebraicGeometry.Thickenings.UniversalConormalGeneratorsSupplement
public import StacksFrontier.CategoryTheory.SquareMapComposition

/-!
# The conormal map of two vertically stacked squares of ringed spaces composes

Let
```
A₀ --i₀--→ B₀
|          |
f₁         k₁
↓          ↓
A₁ --i₁--→ B₁
|          |
f₂         k₂
↓          ↓
A₂ --i₂--→ B₂
```
be two commutative squares of ringed spaces stacked vertically.
`Stacks.ClosedImmersion.conormalSheafMap` attaches to each of them a map of conormal sheaves, and
to the outer rectangle one as well; this file proves that the outer rectangle's map is the
comparison of inverse images for `f₁` and `f₂`, followed by the inverse image along `f₁` of the
lower square's map, followed by the upper square's map.

The corresponding statement for the **ideal** sheaves is
`Stacks.ClosedImmersion.idealSheafMap_comp` of
`StacksFrontier/AlgebraicGeometry/Thickenings/ConormalSequenceIdealForm.lean`, and the statement
for the conormal sheaves of **immersions of schemes** is
`Stacks.Immersion.immersionConormalSheafMap_comp`; neither gives this one.  The schemes-side law
is stated at `Stacks.Conormal.conormalSheaf`, the conormal sheaf of the coborder lift of an
immersion, so it says nothing about `Stacks.ClosedImmersion.conormalSheafMap` of a square of
arbitrary morphisms of ringed spaces, which is what the reduction of part (2) of
[Stacks Project, Tag 04G2] to a pair of ambient opens needs.

## Main results

* `RingedSpaceModuleAdjunction.modulePullbackSquareIso_paste`: **the square comparisons of two
  vertically stacked squares of ringed spaces paste.**  This is the ringed-space counterpart of
  `AlgebraicGeometry.Space.squarePullbackCompIso_paste`, and the content this file had to add.
* `Stacks.ClosedImmersion.conormalSheafMap_comp`: **the composition law**, one instantiation of
  `Stacks.CategoryTheory.square_map_comp` whose five hypotheses are the pasting above,
  `Stacks.ClosedImmersion.idealSheafMap_comp`, and three instances of
  `Stacks.ClosedImmersion.conormalSheafMap_eq`.

The coherences of `RingedSpaceModuleAdjunction.modulePullbackComp` that the pasting consumes are
proved on the way: `RingedSpaceModuleAdjunction.modulePullbackComp_assoc_hom` and
`…_assoc_hom_eqToHom` (associativity at the level of natural transformations),
`RingedSpaceModuleAdjunction.modulePullbackComp_whiskerLeft_hom_comp_whiskerRight_inv`, and the
two transports `RingedSpaceModuleAdjunction.modulePullbackComp_hom_whiskerRight_eqToHom` and
`…_whiskerLeft_eqToHom` along an equality of one of the two morphisms.

## Implementation notes

The spaces-side pasting is proved from six lemmas about
`AlgebraicGeometry.Space.modulePullbackCompIso`, and this file is their ringed-space mirror —
with the direction of the composition comparison reversed, since
`RingedSpaceModuleAdjunction.modulePullbackComp f g` goes `(f ≫ g)^* ≅ g^* ⋙ f^*` while
`AlgebraicGeometry.Space.modulePullbackCompIso f g` goes the other way.  Every `.hom` of the
spaces-side mirror is therefore an `.inv` here and conversely.  The associativity coherence itself
is not re-proved: it is
`RingedSpaceModuleAdjunction.modulePullbackComp_assoc` of
`StacksFrontier/AlgebraicGeometry/Conormal/RestrictSquareMap.lean`, read at one module and lifted to
natural transformations by `CategoryTheory.NatTrans.ext`.

**One thing has to be done here that the spaces-side mirror does not do, and it is what makes the
proof go through at all.**  Composition of morphisms of ringed spaces is definitionally
associative, so `(a ≫ b) ≫ c` and `a ≫ b ≫ c` are convertible; but they are not *syntactically*
equal, and therefore neither are `modulePullback ((a ≫ b) ≫ c)` and
`modulePullback (a ≫ b ≫ c)`.  A composite of natural transformations that passes from one
spelling to the other is accepted by the elaborator and by the kernel, and is then **not
type-correct at the `implicit` transparency level**, which is the level at which `rw` checks its
motive and `simp` its congruences: every subsequent tactic on such a goal fails, reporting the
mismatch rather than anything about the step it was asked to take.  Each of
`rw [Category.assoc]`, `simp only [Category.assoc]` and a further `rw` with any of the lemmas
below is rejected on a goal that contains one such junction.

The fix is to make the junction syntactic by naming it: every statement here that crosses the two
bracketings carries an explicit
`CategoryTheory.eqToHom (congrArg RingedSpaceModuleAdjunction.modulePullback (Category.assoc …))`,
whose recorded source and target are the two spellings.  Those transports are identities —
`RingedSpaceModuleAdjunction.modulePullback_eqToHom_assoc` — so the bridged statements are proved
from the unbridged ones by `CategoryTheory.Category.id_comp` and nothing else; and at the end of
the pasting the whole chain of transports collapses by `CategoryTheory.eqToHom_trans`.

## References

* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.RingedSpace

universe u

namespace RingedSpaceModuleAdjunction

/-- **Whiskering cancels a composite of the two directions of an isomorphism, the forward map
first.**  `AlgebraicGeometry.Space.whiskerLeft_inv_hom_cancel` read at the inverse isomorphism;
it is a declaration of its own only because the two spellings `e.symm.inv` and `e.hom` are
convertible but not syntactically equal, so that lemma cannot be rewritten with. -/
theorem whiskerLeft_hom_inv_assoc {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) {G H : D ⥤ E} (e : G ≅ H) {T : C ⥤ E} (h : F ⋙ G ⟶ T) :
    Functor.whiskerLeft F e.hom ≫ Functor.whiskerLeft F e.inv ≫ h = h :=
  AlgebraicGeometry.Space.whiskerLeft_inv_hom_cancel F e.symm h

section Coherence

variable {A B C D : RingedSpace.{u, u}}

/-- **The transport of the inverse image along the associativity of three morphisms of ringed
spaces is the identity.**  Composition of morphisms of ringed spaces is definitionally
associative, so the two bracketings of a triple composite are convertible and the transport
between their inverse images is an identity morphism.

It is named because `CategoryTheory.eqToHom` of this equality, unlike an identity morphism, has
the two *different* spellings as its recorded source and target, which is what lets a composite
pass from one to the other while staying type-correct at the transparency level at which the
tactics check their motives.  The module documentation records the measurement. -/
theorem modulePullback_eqToHom_assoc (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) :
    eqToHom (congrArg modulePullback (Category.assoc a b c)) =
      𝟙 (modulePullback ((a ≫ b) ≫ c)) :=
  eqToHom_refl _ _

/-- `RingedSpaceModuleAdjunction.modulePullback_eqToHom_assoc` for the associativity read
backwards. -/
theorem modulePullback_eqToHom_assoc_symm (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) :
    eqToHom (congrArg modulePullback (Category.assoc a b c).symm) =
      𝟙 (modulePullback (a ≫ b ≫ c)) :=
  eqToHom_refl _ _

/-- **The associativity coherence of the pullback composition comparison, at the level of natural
transformations.**  `RingedSpaceModuleAdjunction.modulePullbackComp_assoc`, which is stated at one
module, read as an equality of natural transformations. -/
theorem modulePullbackComp_assoc_hom (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) :
    (modulePullbackComp a (b ≫ c)).hom ≫
        Functor.whiskerRight (modulePullbackComp b c).hom (modulePullback a) =
      (modulePullbackComp (a ≫ b) c).hom ≫
        Functor.whiskerLeft (modulePullback c) (modulePullbackComp a b).hom := by
  refine NatTrans.ext (funext fun M => ?_)
  simpa using modulePullbackComp_assoc a b c M

/-- **`RingedSpaceModuleAdjunction.modulePullbackComp_assoc_hom` with the two bracketings of the
triple composite joined by an explicit transport.**  This is the form a rewrite can use; see the
module documentation. -/
@[reassoc]
theorem modulePullbackComp_assoc_hom_eqToHom (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) :
    (modulePullbackComp a (b ≫ c)).hom ≫
        Functor.whiskerRight (modulePullbackComp b c).hom (modulePullback a) =
      eqToHom (congrArg modulePullback (Category.assoc a b c).symm) ≫
        (modulePullbackComp (a ≫ b) c).hom ≫
          Functor.whiskerLeft (modulePullback c) (modulePullbackComp a b).hom :=
  (modulePullbackComp_assoc_hom a b c).trans
    (Category.id_comp _).symm

/-- Whiskering the two directions of the pullback composition comparison by a further inverse
image cancels. -/
theorem whiskerRight_modulePullbackComp_hom_inv (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) :
    Functor.whiskerRight (modulePullbackComp b c).hom (modulePullback a) ≫
        Functor.whiskerRight (modulePullbackComp b c).inv (modulePullback a) =
      𝟙 (modulePullback (b ≫ c) ⋙ modulePullback a) := by
  rw [← Functor.whiskerRight_comp, Iso.hom_inv_id, Functor.whiskerRight_id']

/-- The associativity coherence with the comparison along the inner pair inverted: the comparison
along the outer pair, followed by the inverse image along `c` of the comparison of `a` and `b` and
then by the inverse of the comparison of `b` and `c`, is the comparison of `a` with `b ≫ c`. -/
theorem modulePullbackComp_hom_whiskerLeft_whiskerRight_inv (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) :
    (modulePullbackComp (a ≫ b) c).hom ≫
        Functor.whiskerLeft (modulePullback c) (modulePullbackComp a b).hom ≫
          Functor.whiskerRight (modulePullbackComp b c).inv (modulePullback a) =
      (modulePullbackComp a (b ≫ c)).hom :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg
          (fun t => t ≫ Functor.whiskerRight (modulePullbackComp b c).inv (modulePullback a))
          (modulePullbackComp_assoc_hom a b c)).symm.trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun t => (modulePullbackComp a (b ≫ c)).hom ≫ t)
            (whiskerRight_modulePullbackComp_hom_inv a b c)).trans
          (Category.comp_id _))))

/-- **The composite of the comparison of `a` and `b` with the inverse of the comparison of `b` and
`c`.**  It is the inverse of the comparison along the outer pair followed by the comparison of `a`
with `b ≫ c`, the two bracketings of the triple composite joined by an explicit transport.

This is the ringed-space mirror of
`AlgebraicGeometry.Space.modulePullbackCompIso_inv_comp_whiskerRight_hom`, and it is the step of
the pasting that turns the lower square's comparison into the outer rectangle's. -/
@[reassoc]
theorem modulePullbackComp_whiskerLeft_hom_comp_whiskerRight_inv
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) :
    Functor.whiskerLeft (modulePullback c) (modulePullbackComp a b).hom ≫
        Functor.whiskerRight (modulePullbackComp b c).inv (modulePullback a) =
      (modulePullbackComp (a ≫ b) c).inv ≫
        eqToHom (congrArg modulePullback (Category.assoc a b c)) ≫
          (modulePullbackComp a (b ≫ c)).hom :=
  ((modulePullbackComp (a ≫ b) c).inv_hom_id_assoc
        (Functor.whiskerLeft (modulePullback c) (modulePullbackComp a b).hom ≫
          Functor.whiskerRight (modulePullbackComp b c).inv (modulePullback a))).symm.trans
    (congrArg (fun t => (modulePullbackComp (a ≫ b) c).inv ≫ t)
      ((modulePullbackComp_hom_whiskerLeft_whiskerRight_inv a b c).trans
        (Category.id_comp _).symm))

/-- The pullback composition comparison transported along an equality of the inner morphism. -/
@[reassoc]
theorem modulePullbackComp_hom_whiskerRight_eqToHom (a : A ⟶ B) {b b' : B ⟶ D} (p : b = b') :
    (modulePullbackComp a b).hom ≫
        Functor.whiskerRight (eqToHom (congrArg modulePullback p)) (modulePullback a) =
      eqToHom (congrArg modulePullback (congrArg (fun h : B ⟶ D => a ≫ h) p)) ≫
        (modulePullbackComp a b').hom := by
  subst p
  simp

/-- The pullback composition comparison transported along an equality of the outer morphism. -/
@[reassoc]
theorem modulePullbackComp_hom_whiskerLeft_eqToHom {a a' : A ⟶ B} (p : a = a') (b : B ⟶ D) :
    (modulePullbackComp a b).hom ≫
        Functor.whiskerLeft (modulePullback b) (eqToHom (congrArg modulePullback p)) =
      eqToHom (congrArg modulePullback (congrArg (fun h : A ⟶ B => h ≫ b) p)) ≫
        (modulePullbackComp a' b).hom := by
  subst p
  simp

end Coherence

section Paste

variable {A₀ A₁ A₂ B₀ B₁ B₂ : RingedSpace.{u, u}}
    {i₀ : A₀ ⟶ B₀} {i₁ : A₁ ⟶ B₁} {i₂ : A₂ ⟶ B₂} {f₁ : A₀ ⟶ A₁} {k₁ : B₀ ⟶ B₁}
    {f₂ : A₁ ⟶ A₂} {k₂ : B₁ ⟶ B₂}

/-- **The square comparisons of two vertically stacked squares of ringed spaces paste.**  The
comparison of the outer rectangle, read backwards and followed by the inverse image along `i₀` of
the composition comparison of the two right-hand verticals, is the composition comparison of the
two left-hand verticals followed by the comparisons of the lower and then the upper square.

Only the three commutativities are used: nothing is assumed about closedness, immersions or
quasi-coherence, since `RingedSpaceModuleAdjunction.modulePullbackSquareIso` is defined for
arbitrary morphisms of ringed spaces.

This is the hypothesis `hpaste` of `Stacks.CategoryTheory.square_map_comp` at the geometric
instance, and the ringed-space counterpart of
`AlgebraicGeometry.Space.squarePullbackCompIso_paste`. -/
theorem modulePullbackSquareIso_paste (commA : i₀ ≫ k₁ = f₁ ≫ i₁) (commB : i₁ ≫ k₂ = f₂ ≫ i₂)
    (comm : i₀ ≫ k₁ ≫ k₂ = (f₁ ≫ f₂) ≫ i₂) :
    (modulePullbackSquareIso (f₁ ≫ f₂) (k₁ ≫ k₂) i₀ i₂ comm).inv ≫
        Functor.whiskerRight (modulePullbackComp k₁ k₂).hom (modulePullback i₀) =
      Functor.whiskerLeft (modulePullback i₂) (modulePullbackComp f₁ f₂).hom ≫
        Functor.whiskerRight (modulePullbackSquareIso f₂ k₂ i₁ i₂ commB).inv
            (modulePullback f₁) ≫
          Functor.whiskerLeft (modulePullback k₂)
            (modulePullbackSquareIso f₁ k₁ i₀ i₁ commA).inv := by
  rw [modulePullbackSquareIso_inv, modulePullbackSquareIso_inv, modulePullbackSquareIso_inv,
    Functor.whiskerRight_comp, Functor.whiskerRight_comp, Functor.whiskerLeft_comp,
    Functor.whiskerLeft_comp]
  simp only [Category.assoc, modulePullbackCongr, eqToIso.hom]
  conv_rhs =>
    rw [modulePullbackComp_whiskerLeft_hom_comp_whiskerRight_inv_assoc f₁ f₂ i₂,
      modulePullbackComp_hom_whiskerRight_eqToHom_assoc f₁ commB.symm,
      modulePullbackComp_assoc_hom_eqToHom_assoc f₁ i₁ k₂,
      whiskerLeft_hom_inv_assoc,
      modulePullbackComp_hom_whiskerLeft_eqToHom_assoc commA.symm k₂]
  conv_lhs => rw [modulePullbackComp_assoc_hom_eqToHom i₀ k₁ k₂]
  simp only [eqToHom_trans_assoc]

end Paste

end RingedSpaceModuleAdjunction

namespace Stacks.ClosedImmersion

open RingedSpaceModuleAdjunction

/-- **The conormal maps of two vertically stacked commutative squares of ringed spaces compose.**
For the outer rectangle the map is the comparison of inverse images of `f₁` and `f₂`, followed by
the inverse image along `f₁` of the lower square's map, followed by the upper square's map.

Only the three commutativities are used: nothing is assumed about closedness, immersions or
quasi-coherence, since `Stacks.ClosedImmersion.conormalSheafMap` is defined for arbitrary
morphisms of ringed spaces.

The proof is one instantiation of `Stacks.CategoryTheory.square_map_comp`, proved at variables:
the canonical map of each of the three squares is its square comparison read at the ideal sheaf of
the bottom ambient followed by the inverse image of the square's ideal-sheaf map
(`Stacks.ClosedImmersion.conormalSheafMap_eq`), the three comparisons paste
(`RingedSpaceModuleAdjunction.modulePullbackSquareIso_paste`), and the three ideal-sheaf maps
compose (`Stacks.ClosedImmersion.idealSheafMap_comp`).

The commutativity of the outer rectangle is a **separate hypothesis** rather than assembled from
the two others, for the reason the module documentation of
`StacksFrontier/AlgebraicGeometry/Spaces/KernelIdealSquareMapComposition.lean` records: a consumer
meets it at whichever spelling its own statement fixes, and deriving it here would force that
spelling. -/
theorem conormalSheafMap_comp {A₀ A₁ A₂ B₀ B₁ B₂ : RingedSpace.{u, u}}
    {i₀ : A₀ ⟶ B₀} {i₁ : A₁ ⟶ B₁} {i₂ : A₂ ⟶ B₂} {f₁ : A₀ ⟶ A₁} {k₁ : B₀ ⟶ B₁}
    {f₂ : A₁ ⟶ A₂} {k₂ : B₁ ⟶ B₂}
    (commA : i₀ ≫ k₁ = f₁ ≫ i₁) (commB : i₁ ≫ k₂ = f₂ ≫ i₂)
    (comm : i₀ ≫ k₁ ≫ k₂ = (f₁ ≫ f₂) ≫ i₂) :
    conormalSheafMap comm =
      (modulePullbackComp f₁ f₂).hom.app (conormalSheaf i₂) ≫
        (modulePullback f₁).map (conormalSheafMap commB) ≫ conormalSheafMap commA :=
  Stacks.CategoryTheory.square_map_comp (modulePullback i₀) (modulePullback i₁)
    (modulePullback i₂) (modulePullback f₁) (modulePullback f₂)
    (modulePullback (f₁ ≫ f₂)) (modulePullback k₁) (modulePullback k₂)
    (modulePullback (k₁ ≫ k₂))
    (modulePullbackSquareIso f₁ k₁ i₀ i₁ commA).symm
    (modulePullbackSquareIso f₂ k₂ i₁ i₂ commB).symm
    (modulePullbackSquareIso (f₁ ≫ f₂) (k₁ ≫ k₂) i₀ i₂ comm).symm
    (modulePullbackComp f₁ f₂).symm (modulePullbackComp k₁ k₂).symm
    (modulePullbackSquareIso_paste commA commB comm)
    (idealSheafMap commA) (idealSheafMap commB) (idealSheafMap comm)
    (idealSheafMap_comp commA commB comm)
    (conormalSheafMap_eq comm) (conormalSheafMap_eq commA) (conormalSheafMap_eq commB)

end Stacks.ClosedImmersion

end
