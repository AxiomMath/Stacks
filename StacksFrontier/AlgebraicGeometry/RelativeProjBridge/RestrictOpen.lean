module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksFrontier.AlgebraicGeometry.Constructions.RelativeProjSectionRings
public import StacksFrontier.AlgebraicGeometry.RelativeProjBridge.Basic

/-!
# Restricting a sheaf-level graded algebra to an open of the base

A quasi-coherent graded `𝒪_X`-algebra in the sense of Situation 01NN can be read over an open
`W` of `X`: its homogeneous pieces are restricted to `W` and its multiplication and unit are the
ones it already has over the opens of `X` that lie in `W`. This file performs that restriction,
for both graded-algebra substrates of this repository and for
`Stacks.RelativeProj.Situation`, and records the coherences a consumer needs.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.restrictOpen`: **the
  restriction of a sheaf-level graded algebra to an open of the base.**
* `Stacks.AlgebraicGeometry.RelativeProjBridge.restrictGradedAlgebra`: the same operation on
  `SheafOfModules.GradedAlgebra`, the substrate `Stacks.RelativeProj.Situation` records.
* `Stacks.RelativeProj.Situation.restrictOpen`: **the restriction of a Situation 01NN datum to
  an open of its base.**

## Main results

* `…SheafGradedAlgebra.restrictOpen_sectionRing` and `…restrictOpen_grading`: **the graded ring
  of sections of the restriction over an open `V` of `W` is, on the nose, the graded ring of
  sections of the original algebra over `W.ι ''ᵁ V`.** Both are equalities, not comparison maps:
  the carrier, the grading, the graded-ring structure and the ring structure are all the same
  term.
* `…SheafGradedAlgebra.restrictOpen_toGradedAlgebra_ring` and
  `…restrictOpen_toGradedAlgebra_grading`: the same at the affine-open substrate
  `Stacks.AlgebraicGeometry.RelativeProj.GradedAlgebra` that the glueing consumes.
* `…SheafGradedAlgebra.restrictOpen_strHom`: the structure map of the restriction is the
  structure map of the algebra over the image open.
* `Stacks.RelativeProj.Situation.restrictOpen_base`,
  `…restrictOpen_sectionPieces` and `…restrictOpen_sectionRing`: the same for a Situation.

## Implementation notes

**The whole construction is definitional, and that is the point.** Mathlib's
`AlgebraicGeometry.Scheme.Modules.restrictFunctor` along an open immersion is *not* the pullback
functor but a pushforward along the image functor on opens, built precisely so that
`Γ(M.restrict f, V) = Γ(M, f ''ᵁ V)` holds by `rfl`
(`AlgebraicGeometry.Scheme.Modules.restrict_obj`) and so that the restriction maps agree by `rfl`
too (`AlgebraicGeometry.Scheme.Modules.restrict_map`). Restricting along `W.ι` therefore changes
no section group and no restriction map, only reindexes the opens; so every axiom of
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra` is the corresponding axiom of
the original algebra at the open `W.ι ''ᵁ V`, with no transport, and all the coherences below
are `rfl`.

**The one place where something happens is the scalar action.** `restrictFunctor` restricts
scalars along `(W.ι.appIso V).inv : Γ(W, V) ⟶ Γ(X, W.ι ''ᵁ V)`, so an `𝒪_W`-scalar acts on a
restricted section through that map. For `W.ι` the map is the identity, but only up to
`AlgebraicGeometry.Scheme.Opens.ι_appIso`, which is not a `rfl`. The three lemmas that cross
that step are `appIso_ι_inv`, `appIso_ι_inv_apply` and `restrictOpen_smul`, and
`restrictOpen_strHom` is the only result below that needs one of them. The two bilinearity
axioms of the multiplication need no such step: they are stated for *some* scalar, so the
original algebra's axiom at `(W.ι.appIso V).inv r` is already the required statement, which is
why `restrictOpen` itself is free of the comparison.

**Negative pieces.** `AlgebraicGeometry.Scheme.Modules.restrictFunctor` carries no `Additive`
instance, so vanishing is transported along
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` to the pullback functor, which
does.

## References

* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)

## Not done here

No tag is registered. Situation 01NN is a datum, not an assertion, and this file only reads an
existing datum over a smaller base; the registrations of 01NN already sit on the two structures
and on their graded rings of local sections.

Nothing here compares the relative homogeneous spectrum of the restriction with the fibre
product `W ×_X Proj_X(A)`. What the file supplies is the equality of the graded data chart by
chart, which is what makes such a comparison statable at all; the comparison itself is the
open-immersion case of base change of relative `Proj` and needs the glueing.

**The equality of the charts themselves is not stated.** From `restrictOpen_grading` a consumer
gets `AlgebraicGeometry.Proj ((A.restrictOpen W).grading V) = AlgebraicGeometry.Proj
(A.grading (W.ι ''ᵁ V))` by congruence. Stating it as a `rfl` lemma here does not elaborate:
the kernel comparison of two `AlgebraicGeometry.Proj` of graded section rings exhausts the
heartbeat budget in `whnf`, which is the cost recorded in the transparency note of
`StacksFrontier/AlgebraicGeometry/RelativeProjBridge/SectionRing.lean`.

No pullback along a general morphism of bases is constructed: the construction below is
definitional exactly because `W.ι` is an open immersion, and nothing in it survives the
passage to an arbitrary `g : X' ⟶ X`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace Stacks.AlgebraicGeometry.RelativeProjBridge

universe u

variable {X : Scheme.{u}}

/-! ### The scalar action on a restricted sheaf of modules -/

/-- The comparison isomorphism of `AlgebraicGeometry.Scheme.Hom.appIso` at the inclusion of an
open is the identity, as a morphism of rings of sections. This is
`AlgebraicGeometry.Scheme.Opens.ι_appIso` read on the inverse. -/
public theorem appIso_ι_inv (W : X.Opens) (V : W.toScheme.Opens) :
    (W.ι.appIso V).inv = 𝟙 Γ(X, W.ι ''ᵁ V) := by
  rw [Scheme.Opens.ι_appIso]
  rfl

/-- `appIso_ι_inv` on an element. -/
public theorem appIso_ι_inv_apply (W : X.Opens) (V : W.toScheme.Opens)
    (r : Γ(W.toScheme, V)) : (W.ι.appIso V).inv r = r := by
  rw [appIso_ι_inv]
  rfl

/-- **The scalar action on a restricted sheaf of modules is the original one.** An `𝒪_W`-scalar
acts on a section of `M` over `W.ι ''ᵁ V` through `(W.ι.appIso V).inv`, which is the identity. -/
public theorem restrictOpen_smul {M : X.Modules} (W : X.Opens) (V : W.toScheme.Opens)
    (r : Γ(W.toScheme, V)) (x : Γ((Scheme.Modules.restrictFunctor W.ι).obj M, V)) :
    r • x = (M.smul (U := W.ι ''ᵁ V) r).asHom.hom x := by
  change (M.smul (U := W.ι ''ᵁ V) ((W.ι.appIso V).inv r)).asHom.hom x = _
  rw [appIso_ι_inv_apply]

namespace SheafGradedAlgebra

variable (A : SheafGradedAlgebra X)

/-! ### The restriction -/

/-- **The restriction of a sheaf-level graded algebra to an open of the base.** The homogeneous
pieces are restricted along the inclusion of `W`, and the multiplication and the unit over an
open `V` of `W` are those of `A` over the image of `V` in `X`.

Every axiom is the corresponding axiom of `A` at that image open: restriction along an open
immersion changes no section group and no restriction map. -/
public def restrictOpen (W : X.Opens) : SheafGradedAlgebra W.toScheme where
  piece n := (Scheme.Modules.restrictFunctor W.ι).obj (A.piece n)
  mul i j :=
    { app V := (A.mul i j).app (W.ι ''ᵁ V)
      map_smul_left V r x y := (A.mul i j).map_smul_left _ ((W.ι.appIso V).inv r) x y
      map_smul_right V r x y := (A.mul i j).map_smul_right _ ((W.ι.appIso V).inv r) x y
      naturality h x y := (A.mul i j).naturality (W.ι.image_mono h) x y }
  one V := A.one (W.ι ''ᵁ V)
  one_res h := A.one_res (W.ι.image_mono h)
  mul_assoc i j k V a b c := A.mul_assoc i j k (W.ι ''ᵁ V) a b c
  one_mul i V a := A.one_mul i (W.ι ''ᵁ V) a
  mul_one i V a := A.mul_one i (W.ι ''ᵁ V) a
  mul_comm i j V a b := A.mul_comm i j (W.ι ''ᵁ V) a b
  negative_isZero n hn :=
    .of_iso ((Scheme.Modules.pullback W.ι).map_isZero (A.negative_isZero n hn))
      ((Scheme.Modules.restrictFunctorIsoPullback W.ι).app (A.piece n))
  isQuasicoherent _ := inferInstance

/-- The homogeneous piece of degree `n` of the restriction is the restriction of the piece of
`A` of degree `n`. -/
@[simp]
public theorem restrictOpen_piece (W : X.Opens) (n : ℤ) :
    (A.restrictOpen W).piece n = (Scheme.Modules.restrictFunctor W.ι).obj (A.piece n) := rfl

/-- The multiplication of the restriction over an open `V` of `W` is that of `A` over the image
of `V`. -/
@[simp]
public theorem restrictOpen_mul_app (W : X.Opens) (i j : ℤ) (V : W.toScheme.Opens) :
    ((A.restrictOpen W).mul i j).app V = (A.mul i j).app (W.ι ''ᵁ V) := rfl

/-- The unit of the restriction over an open `V` of `W` is that of `A` over the image of `V`. -/
@[simp]
public theorem restrictOpen_one (W : X.Opens) (V : W.toScheme.Opens) :
    (A.restrictOpen W).one V = A.one (W.ι ''ᵁ V) := rfl

/-! ### The graded rings of sections of the restriction -/

/-- The homogeneous sections of the restriction over an open of `W` are those of `A` over the
image of that open. -/
public theorem restrictOpen_sectionPieces (W : X.Opens) (V : W.toScheme.Opens) (n : ℕ) :
    (A.restrictOpen W).sectionPieces V n = A.sectionPieces (W.ι ''ᵁ V) n := rfl

/-- **The graded ring of sections of the restriction over an open of `W` is the graded ring of
sections of `A` over the image of that open.** An equality of types, the two graded-ring
structures being the same term. -/
public theorem restrictOpen_sectionRing (W : X.Opens) (V : W.toScheme.Opens) :
    (A.restrictOpen W).sectionRing V = A.sectionRing (W.ι ''ᵁ V) := rfl

/-- **The internal gradings agree.** This is what makes the relative homogeneous spectrum of the
restriction computable from that of `A`. -/
public theorem restrictOpen_grading (W : X.Opens) (V : W.toScheme.Opens) :
    (A.restrictOpen W).grading V = A.grading (W.ι ''ᵁ V) := rfl

/-- The structure map of the restriction over an open of `W` is the structure map of `A` over
the image open, read through the scalar comparison of the restriction. -/
public theorem restrictOpen_strHom_inv (W : X.Opens) (V : W.toScheme.Opens)
    (r : Γ(W.toScheme, V)) :
    (A.restrictOpen W).strHom V r = A.strHom (W.ι ''ᵁ V) ((W.ι.appIso V).inv r) := rfl

/-- **The structure map of the restriction over an open of `W` is the structure map of `A` over
the image open.** -/
public theorem restrictOpen_strHom (W : X.Opens) (V : W.toScheme.Opens)
    (r : Γ(W.toScheme, V)) :
    (A.restrictOpen W).strHom V r = A.strHom (W.ι ''ᵁ V) r := by
  rw [restrictOpen_strHom_inv, appIso_ι_inv_apply]

/-! ### The restriction at the affine-open substrate -/

/-- An affine open of `W` has affine image in `X`, so it is an object of the small affine
Zariski site of `X`. -/
public def affineImage (W : X.Opens) (V : W.toScheme.AffineZariskiSite) :
    X.AffineZariskiSite :=
  ⟨W.ι ''ᵁ V.toOpens, V.2.image_of_isOpenImmersion W.ι⟩

/-- The open underlying `affineImage W V` is the image of `V` in `X`. -/
@[simp]
public theorem affineImage_toOpens (W : X.Opens) (V : W.toScheme.AffineZariskiSite) :
    (affineImage W V).toOpens = W.ι ''ᵁ V.toOpens := rfl

/-- The graded ring that the restriction records over an affine open of `W` is the one `A`
records over its image. -/
public theorem restrictOpen_toGradedAlgebra_ring (W : X.Opens)
    (V : W.toScheme.AffineZariskiSite) :
    (A.restrictOpen W).toGradedAlgebra.ring V = A.toGradedAlgebra.ring (affineImage W V) := rfl

/-- The grading that the restriction records over an affine open of `W` is the one `A` records
over its image. -/
public theorem restrictOpen_toGradedAlgebra_grading (W : X.Opens)
    (V : W.toScheme.AffineZariskiSite) :
    (A.restrictOpen W).toGradedAlgebra.grading V =
      A.toGradedAlgebra.grading (affineImage W V) := rfl

end SheafGradedAlgebra

/-! ### The restriction of the other graded-algebra substrate -/

/-- **The restriction of a sheaf of graded algebras to an open of the base**, on the
`SheafOfModules.GradedAlgebra` substrate that `Stacks.RelativeProj.Situation` records. As for
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.restrictOpen`, every axiom is
the axiom of the original algebra at the image open. -/
public def restrictGradedAlgebra (A : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf)
    (W : X.Opens) : SheafOfModules.GradedAlgebra.{u, u} W.toScheme.ringCatSheaf where
  piece n := (Scheme.Modules.restrictFunctor W.ι).obj (A.piece n)
  mul i j :=
    { app V := (A.mul i j).app (op (W.ι ''ᵁ V.unop))
      map_smul_left V r x y :=
        (A.mul i j).map_smul_left _ ((W.ι.appIso V.unop).inv r) x y
      map_smul_right V r x y :=
        (A.mul i j).map_smul_right _ ((W.ι.appIso V.unop).inv r) x y
      naturality f x y := (A.mul i j).naturality (W.ι.opensFunctor.op.map f) x y }
  one := PresheafOfModules.sectionsMk (fun V => A.one.eval (op (W.ι ''ᵁ V.unop)))
    (fun {_ _} f => A.one.property (W.ι.opensFunctor.op.map f))
  mul_assoc i j k V x y z := A.mul_assoc i j k (op (W.ι ''ᵁ V.unop)) x y z
  one_mul i V x := A.one_mul i (op (W.ι ''ᵁ V.unop)) x
  mul_one i V x := A.mul_one i (op (W.ι ''ᵁ V.unop)) x

/-- The homogeneous piece of degree `n` of `restrictGradedAlgebra A W` is the restriction of
the piece of `A` of degree `n`. -/
@[simp]
public theorem restrictGradedAlgebra_piece
    (A : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf) (W : X.Opens) (n : ℤ) :
    (restrictGradedAlgebra A W).piece n =
      (Scheme.Modules.restrictFunctor W.ι).obj (A.piece n) := rfl

/-- The multiplication of `restrictGradedAlgebra A W` over an open `V` of `W` is that of `A`
over the image of `V`. -/
@[simp]
public theorem restrictGradedAlgebra_mul_app
    (A : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf) (W : X.Opens) (i j : ℤ)
    (V : (Opens W.toScheme)ᵒᵖ) :
    ((restrictGradedAlgebra A W).mul i j).app V = (A.mul i j).app (op (W.ι ''ᵁ V.unop)) := rfl

/-- The unit section of `restrictGradedAlgebra A W` over an open `V` of `W` is that of `A` over
the image of `V`. -/
@[simp]
public theorem restrictGradedAlgebra_one_eval
    (A : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf) (W : X.Opens)
    (V : (Opens W.toScheme)ᵒᵖ) :
    (restrictGradedAlgebra A W).one.eval V = A.one.eval (op (W.ι ''ᵁ V.unop)) := rfl

end Stacks.AlgebraicGeometry.RelativeProjBridge

namespace Stacks.RelativeProj.Situation

open Stacks.AlgebraicGeometry.RelativeProjBridge

universe u

/-- **The restriction of a Situation 01NN datum to an open of its base.** The base becomes the
open subscheme and the graded algebra is restricted along its inclusion; commutativity,
vanishing in negative degrees and quasi-coherence are inherited pointwise. -/
public def restrictOpen (s : Situation.{u}) (W : s.base.Opens) : Situation.{u} where
  base := W.toScheme
  algebra := restrictGradedAlgebra s.algebra W
  mul_comm i j V a b := s.mul_comm i j (op (W.ι ''ᵁ V.unop)) a b
  negative_isZero n hn :=
    .of_iso
      ((AlgebraicGeometry.Scheme.Modules.pullback W.ι).map_isZero (s.negative_isZero n hn))
      ((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback W.ι).app
        (s.algebra.piece n))
  isQuasicoherent n :=
    haveI : ((s.algebra.piece n : s.base.Modules)).IsQuasicoherent := s.isQuasicoherent n
    AlgebraicGeometry.Scheme.Modules.isQuasicoherent_restrictFunctor W.ι
      (s.algebra.piece n : s.base.Modules)

/-- The base of the restricted situation is the open subscheme `W`. -/
@[simp]
public theorem restrictOpen_base (s : Situation.{u}) (W : s.base.Opens) :
    (s.restrictOpen W).base = W.toScheme := rfl

/-- The graded algebra of the restricted situation is `restrictGradedAlgebra s.algebra W`. -/
@[simp]
public theorem restrictOpen_algebra (s : Situation.{u}) (W : s.base.Opens) :
    (s.restrictOpen W).algebra = restrictGradedAlgebra s.algebra W := rfl

/-- The homogeneous sections of the restricted situation over an open of `W` are those of `s`
over the image of that open. -/
public theorem restrictOpen_sectionPieces (s : Situation.{u}) (W : s.base.Opens)
    (V : W.toScheme.Opens) (n : ℕ) :
    (s.restrictOpen W).sectionPieces V n = s.sectionPieces (W.ι ''ᵁ V) n := rfl

/-- The underlying additive group of the graded section ring of the restricted situation over an
open of `W` is that of `s` over the image of that open. -/
public theorem restrictOpen_sectionRing (s : Situation.{u}) (W : s.base.Opens)
    (V : W.toScheme.Opens) :
    (s.restrictOpen W).sectionRing V = s.sectionRing (W.ι ''ᵁ V) := rfl

end Stacks.RelativeProj.Situation

end
