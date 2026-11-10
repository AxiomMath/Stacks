module

public import StacksFrontier.AlgebraicGeometry.ProjF1Dehomogenization.Chart
public import StacksFrontier.AlgebraicGeometry.ProjF1Dehomogenization.UnitAlgebra
public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.GenerationNecessary
public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.TwistComparison
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The trivialization datum of a quotient pair, constructed

`Stacks.AlgebraicGeometry.ProjF1Dehomogenization.dehomogenize` turns a quotient pair of Tag 01O4
together with a *trivialization datum* — a multiplicative unital family out of the homogeneous
sections of the pair's tensor algebra over one open — into a ring homomorphism out of the
homogeneous section ring of the base, and
`Stacks.AlgebraicGeometry.ProjF1Dehomogenization.toRelativeProjOfPair` turns that into a morphism
into relative `Proj`. Every one of those declarations takes the trivialization datum as a
hypothesis, and `Stacks.AlgebraicGeometry.ProjF1Dehomogenization.Universal` reduced producing one
to naming a concrete sheaf of graded algebras on the test scheme carrying a map out of the pair's
invertible sheaf `ℒ`. That algebra is constructed here, and with it the datum.

The algebra is `g_*𝒪_X` in every degree, for an arbitrary morphism of schemes `g : X ⟶ T` into
the test scheme, with the multiplication of `𝒪_X`. Its sections over an open `W` of `T` are
`Γ(X, g⁻¹W)`, a commutative ring, on which `Γ(T, W)` acts through the structure map of `g`; so
every law of the graded algebra is a law of `𝒪_X` read at `g⁻¹W`, and the whole construction is
the unit graded algebra of `UnitAlgebra` reindexed along `g`. A map `κ : ℒ ⟶ g_*𝒪_X` is, by the
pullback–pushforward adjunction, a trivialization `g^*ℒ ⟶ 𝒪_X` of the pulled-back invertible
sheaf: exactly the datum a chart of relative `Proj` is built on.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjF1Dehomogenization.pushforwardUnit`: the direct image `g_*𝒪_X`,
  as a sheaf of modules on the test scheme.
* `Stacks.AlgebraicGeometry.ProjF1Dehomogenization.pushforwardUnitGradedAlgebra`: **the concrete
  graded algebra.** `g_*𝒪_X` in every degree, with the multiplication of `𝒪_X`.
* `Stacks.AlgebraicGeometry.ProjF1Dehomogenization.pushforwardUnitDatum`: its trivialization
  datum over an open of the test scheme, for any ring homomorphism out of `Γ(X, g⁻¹W)`.
* `Stacks.AlgebraicGeometry.ProjF1Dehomogenization.datumOfTrivialization`: **the trivialization
  datum of a quotient pair**, from a morphism `g : X ⟶ T`, a map `κ : ℒ ⟶ g_*𝒪_X` and a ring
  homomorphism out of `Γ(X, g⁻¹f⁻¹U)`.
* `Stacks.AlgebraicGeometry.ProjF1Dehomogenization.pairSectionOne`: the section of `ℒ` over
  `f⁻¹U` that a degree-one homogeneous section of the algebra over `U` induces.
* `Stacks.AlgebraicGeometry.ProjF1Dehomogenization.toRelativeProjOfTrivialization`: **the chart
  morphism into relative `Proj`** that a trivialized pair classifies, with the unit hypothesis
  in the form the formula below gives it.

## Main results

* `Stacks.AlgebraicGeometry.ProjF1Dehomogenization.datumOfTrivialization_pairPieceHom_one`:
  **the degree-one coefficient is the trivialization of the induced section.** The coefficient
  that `toRelativeProjOfPair` requires to be a unit is `φ (κ (ψ₁ s))` and nothing else, so
  invertibility of it is a statement about one section of `ℒ` and the chosen trivialization —
  which is what makes the hypothesis of the chart checkable on a cover.
* `Stacks.AlgebraicGeometry.ProjF1Dehomogenization.datumOfTrivialization_toFun_one`: the same
  before `ψ` is applied, at an arbitrary degree-one section of the tensor algebra.
* `Stacks.AlgebraicGeometry.ProjF1Dehomogenization.toRelativeProjOfTrivialization_comp_toBase`:
  the chart morphism lies over the affine open of the base it was built on.

## Implementation notes

**The graded algebra is the unit graded algebra reindexed, field for field, and that is why it
costs nothing.** `(Scheme.Modules.pushforward g).obj M` has `Γ(-, W) = Γ(M, g⁻¹W)` on the nose
(`AlgebraicGeometry.Scheme.Modules.pushforward_obj_obj` is `rfl`), and the scalar action of
`Γ(T, W)` is the action of `Γ(X, g⁻¹W)` through the structure map, by `Module.compHom`. So each
field of `SheafOfModules.BilinearMap` and of `SheafOfModules.GradedAlgebra` for `g_*𝒪_X` at `W`
is the corresponding field of `unitMul`/`unitGradedAlgebra` at `g⁻¹W`, applied with the scalar
left as a hole for unification to fill with the structure map's value. No spelling of the
structure map appears anywhere below, and no `rw` on a morphism of sheaves of modules occurs.

**`pushforwardUnitDatum` cannot be `unitDatum` reindexed, although its three fields can.**
`GradedSectionAlgebraHom` is a structure applied to the graded algebra, and the two graded
algebras are distinct terms however defeq their components are, so the ambient type does not
match; the fields are written out instead, each delegating to the corresponding law of `φ`
exactly as `unitDatum` does.

**The degree-one formula is the universal property applied once.** `datumOfGenerator` is
`GradedSectionAlgebraHom.precomp` of the canonical unital homomorphism
`SheafOfModules.GradedAlgebra.IsTensorAlgebra.descAny`, whose defining property
`descAny_extends` says that composing with the degree-one generator gives `κ`. Since the
generator is an isomorphism onto the degree-one piece —
`Stacks.AlgebraicGeometry.ProjRepresentsF1.tensorGeneratorIso`, which is the bundle's
`tensorPieceIso_one` — the degree-one component of `descAny` *is* the inverse of that
isomorphism followed by `κ`, and the formula follows by evaluating at a section.

## References

* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)

## Not done here

No project tag is attached. What this file supplies is one of the three inputs that the label
`01O4 "represents_f1"` still waits on — the trivialization datum, which two files previously
recorded as missing, and with it the first morphism into relative `Proj` that a quotient pair
produces with no datum assumed. The other two inputs are untouched. **The cover is not
constructed here**, and the shape of what is missing is sharp: `toRelativeProjOfTrivialization`
asks, for a point of the test scheme, for an affine open `U` of the base, a degree-one section
`s` over it, and a `g : X ⟶ T` through which `ℒ` is trivialized and `pairSectionOne s` becomes a
unit. The pair's `degreeOneSurjective` says `f^*𝒜₁ ⟶ ℒ` is an epimorphism, which by
`Stacks.SheafOfModules.StalkEpiMono.exists_sections_of_epi` yields local sections of `f^*𝒜₁`;
turning those into sections of `𝒜₁` over an open of the *base* needs the stalk of `f^*𝒜₁` to be
generated by the pulled-back germs, which this library does not state — the same gap
`StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.Locus` records. Bijectivity on
strict-equivalence classes is untouched.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ProjRepresentsF1
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj

namespace Stacks.AlgebraicGeometry.ProjF1Dehomogenization

universe u

section Pushforward

variable {X T : Scheme.{u}} (g : X ⟶ T)

/-! ### The direct image of the structure sheaf, as a sheaf of modules -/

/-- The direct image `g_*𝒪_X` of the structure sheaf along a morphism of schemes, as a sheaf of
modules on the target. Its sections over `W` are `Γ(X, g⁻¹W)`. -/
@[ega "II 1.1.1" "partial", sga "3 VIIA 1.1"]
public def pushforwardUnit : T.Modules :=
  (Scheme.Modules.pushforward g).obj (SheafOfModules.unit X.ringCatSheaf)

/-- A local section of `g_*𝒪_X` over `W`, read as a section of the structure sheaf of `X` over
`g⁻¹W`. This is the identity function; it exists so that the ring structure of `Γ(X, g⁻¹W)` can
be named where instance search does not find it through the direct image. -/
public def ofPushforwardUnit {W : T.Opensᵒᵖ} (x : (pushforwardUnit g).val.obj W) :
    X.ringCatSheaf.obj.obj (op (g ⁻¹ᵁ W.unop)) := x

/-- The inverse identification of `ofPushforwardUnit`, also the identity function. -/
public def toPushforwardUnit {W : T.Opensᵒᵖ}
    (x : X.ringCatSheaf.obj.obj (op (g ⁻¹ᵁ W.unop))) : (pushforwardUnit g).val.obj W := x

/-- Reading the section `toPushforwardUnit g x` of `g_*𝒪_X` back in `Γ(X, g⁻¹W)` returns `x`. -/
@[simp]
public theorem ofPushforwardUnit_toPushforwardUnit {W : T.Opensᵒᵖ}
    (x : X.ringCatSheaf.obj.obj (op (g ⁻¹ᵁ W.unop))) :
    ofPushforwardUnit g (toPushforwardUnit g x) = x :=
  rfl

/-- A section of `g_*𝒪_X` read in `Γ(X, g⁻¹W)` and back is the original section. -/
@[simp]
public theorem toPushforwardUnit_ofPushforwardUnit {W : T.Opensᵒᵖ}
    (x : (pushforwardUnit g).val.obj W) :
    toPushforwardUnit g (ofPushforwardUnit g x) = x :=
  rfl

/-! ### The graded algebra which is the direct image in every degree -/

/-- Multiplication on `g_*𝒪_X`: the multiplication of the structure sheaf of `X`, read at the
inverse image of each open. Each law is the corresponding law of `unitMul` on `X`, the scalar
being the image of the given one under the structure map of `g`. -/
public def pushforwardUnitMul :
    SheafOfModules.BilinearMap (pushforwardUnit g) (pushforwardUnit g) (pushforwardUnit g) where
  app W := (unitMul X.ringCatSheaf (isCommutativeRingSheaf_scheme X)).app (op (g ⁻¹ᵁ W.unop))
  map_smul_left W _ x y :=
    (unitMul X.ringCatSheaf (isCommutativeRingSheaf_scheme X)).map_smul_left
      (op (g ⁻¹ᵁ W.unop)) _ x y
  map_smul_right W _ x y :=
    (unitMul X.ringCatSheaf (isCommutativeRingSheaf_scheme X)).map_smul_right
      (op (g ⁻¹ᵁ W.unop)) _ x y
  naturality _ x y :=
    (unitMul X.ringCatSheaf (isCommutativeRingSheaf_scheme X)).naturality _ x y

/-- The product under `pushforwardUnitMul g` of two sections of `g_*𝒪_X` over `W` is their
product in `Γ(X, g⁻¹W)`. -/
@[simp]
public theorem ofPushforwardUnit_pushforwardUnitMul_app (W : T.Opensᵒᵖ)
    (x y : (pushforwardUnit g).val.obj W) :
    ofPushforwardUnit g ((pushforwardUnitMul g).app W x y) =
      ofPushforwardUnit g x * ofPushforwardUnit g y :=
  rfl

/-- The unit of `g_*𝒪_X`: the unit section of the structure sheaf of `X`, over every inverse
image. -/
public def pushforwardUnitOne : (pushforwardUnit g).sections :=
  PresheafOfModules.sectionsMk (M := (pushforwardUnit g).val)
    (fun _ => toPushforwardUnit g 1)
    (by intro _ _ _; exact PresheafOfModules.unit_map_one X.ringCatSheaf.obj _)

/-- The section `pushforwardUnitOne g` over `W` is the unit of `Γ(X, g⁻¹W)`. -/
@[simp]
public theorem ofPushforwardUnit_pushforwardUnitOne_eval (W : T.Opensᵒᵖ) :
    ofPushforwardUnit g ((pushforwardUnitOne g).eval W) = 1 :=
  rfl

/-- **The base acts on the direct image through the structure map of `g`.** A scalar `r ∈ Γ(T, U)`
acting on a section of `g_*𝒪_X` that reads as the unit of `Γ(X, g⁻¹U)` gives `g^♯ r`; the module
structure of a direct image is restriction of scalars along `g^♯`, so this is that restriction
read on the unit.

Stated at a section assumed to read as `1` rather than at `pushforwardUnitOne` itself, because
the sections of a degree-zero piece reach this lemma under several definitionally equal spellings
of their type — `Γ(pushforwardUnit g, U)`, `(pushforwardUnit g).val.obj (op U)` and
`((pushforwardUnitGradedAlgebra g).piece 0).val.obj (op U)` — and only the first carries the
scalar action that instance search finds. A hypothesis discharged by `rfl` at the call site costs
the caller nothing and lets the statement be applied at any of them. -/
public theorem ofPushforwardUnit_smul_of_eq_one (U : T.Opens) (r : Γ(T, U))
    (x : Γ(pushforwardUnit g, U)) (hx : ofPushforwardUnit g x = 1) :
    ofPushforwardUnit g (r • x) = (g.app U).hom r := by
  change (show X.ringCatSheaf.obj.obj (op (g ⁻¹ᵁ U)) from (g.app U).hom r)
      * ofPushforwardUnit g x = _
  rw [hx, mul_one]

/-- **The concrete graded algebra on the test scheme.** `g_*𝒪_X` in every degree, with the
multiplication of `𝒪_X` and its unit in degree zero.

This is the sheaf of graded algebras that `datumOfGenerator` descends a trivialization datum
from; a map out of the pair's invertible sheaf into its degree-one piece is a trivialization of
the pullback of that sheaf along `g`. -/
public def pushforwardUnitGradedAlgebra : SheafOfModules.GradedAlgebra.{u, u} T.ringCatSheaf where
  piece _ := pushforwardUnit g
  mul _ _ := pushforwardUnitMul g
  one := pushforwardUnitOne g
  mul_assoc i j k W x y z :=
    (unitGradedAlgebra X.ringCatSheaf (isCommutativeRingSheaf_scheme X)).mul_assoc i j k
      (op (g ⁻¹ᵁ W.unop)) x y z
  one_mul i W x :=
    (unitGradedAlgebra X.ringCatSheaf (isCommutativeRingSheaf_scheme X)).one_mul i
      (op (g ⁻¹ᵁ W.unop)) x
  mul_one i W x :=
    (unitGradedAlgebra X.ringCatSheaf (isCommutativeRingSheaf_scheme X)).mul_one i
      (op (g ⁻¹ᵁ W.unop)) x

/-- The degree-`n` piece of `pushforwardUnitGradedAlgebra g` is `g_*𝒪_X`, for every `n`. -/
@[simp]
public theorem pushforwardUnitGradedAlgebra_piece (n : ℤ) :
    (pushforwardUnitGradedAlgebra g).piece n = pushforwardUnit g :=
  rfl

/-- The trivialization datum of `g_*𝒪_X` attached to a ring homomorphism out of its ring of
sections over one open: in every degree it is that one homomorphism. -/
public def pushforwardUnitDatum {B : Type u} [CommRing B] {W : T.Opensᵒᵖ}
    (φ : X.ringCatSheaf.obj.obj (op (g ⁻¹ᵁ W.unop)) →+* B) :
    GradedSectionAlgebraHom (pushforwardUnitGradedAlgebra g) W B where
  toFun _ := (φ : X.ringCatSheaf.obj.obj (op (g ⁻¹ᵁ W.unop)) →+ B).comp
    (ofUnitHom X.ringCatSheaf (op (g ⁻¹ᵁ W.unop)))
  map_gmul _ _ _ _ := φ.map_mul _ _
  map_gone := φ.map_one

/-- In every degree `n`, `pushforwardUnitDatum g φ` sends a section `x` of `g_*𝒪_X` over `W` to
`φ x`, with `x` read in `Γ(X, g⁻¹W)`. -/
@[simp]
public theorem pushforwardUnitDatum_toFun {B : Type u} [CommRing B] {W : T.Opensᵒᵖ}
    (φ : X.ringCatSheaf.obj.obj (op (g ⁻¹ᵁ W.unop)) →+* B) (n : ℤ)
    (x : (pushforwardUnit g).val.obj W) :
    (pushforwardUnitDatum g φ).toFun n x = φ (ofPushforwardUnit g x) :=
  rfl

end Pushforward

/-! ### The trivialization datum of a quotient pair -/

section Pair

variable {S : Scheme.{u}} (A : SheafGradedAlgebra.{u} S) (TA : TensorAlgebras.{u})
  {T : Scheme.{u}} {f : T ⟶ S} (P : F1Pair A TA f) (U : S.Opens)
  {X : Scheme.{u}} (g : X ⟶ T) {B : Type u} [CommRing B]

/-- **The trivialization datum of a quotient pair.** From a morphism `g : X ⟶ T` of schemes, a
map `κ : ℒ ⟶ g_*𝒪_X` — equivalently, by the pullback–pushforward adjunction, a trivialization
`g^*ℒ ⟶ 𝒪_X` — and a ring homomorphism out of `Γ(X, g⁻¹f⁻¹U)`, the multiplicative unital family
on the homogeneous sections of the pair's tensor algebra over `f⁻¹U` that
`dehomogenize` and `toRelativeProjOfPair` consume.

This is `datumOfGenerator` at the graded algebra `g_*𝒪_X`: the first trivialization datum this
library constructs. -/
public def datumOfTrivialization (κ : P.L ⟶ pushforwardUnit g)
    (φ : X.ringCatSheaf.obj.obj (op (g ⁻¹ᵁ (f ⁻¹ᵁ U))) →+* B) :
    GradedSectionAlgebraHom (TA T P.L).tensor (op (f ⁻¹ᵁ U)) B :=
  datumOfGenerator A TA P U (pushforwardUnitGradedAlgebra g) κ (pushforwardUnitDatum g φ)

/-- **In degree one the datum is the trivialization itself.** The degree-one component of the
canonical unital homomorphism out of the tensor algebra is the inverse of the degree-one
generator followed by `κ`, so the datum sends a degree-one section of the tensor algebra to the
image under `φ` of its trivialization. -/
public theorem datumOfTrivialization_toFun_one (κ : P.L ⟶ pushforwardUnit g)
    (φ : X.ringCatSheaf.obj.obj (op (g ⁻¹ᵁ (f ⁻¹ᵁ U))) →+* B)
    (y : ((TA T P.L).tensor.piece 1).val.obj (op (f ⁻¹ᵁ U))) :
    (datumOfTrivialization A TA P U g κ φ).toFun 1 y =
      φ (ofPushforwardUnit g (κ.val.app (op (f ⁻¹ᵁ U))
        ((tensorGeneratorIso TA T P.L).inv.val.app (op (f ⁻¹ᵁ U)) y))) := by
  have hdesc : ((TA T P.L).tensor_isTensorAlgebra.descAny
      (pushforwardUnitGradedAlgebra g) κ).app 1 =
      (tensorGeneratorIso TA T P.L).inv ≫ κ :=
    (Iso.eq_inv_comp (tensorGeneratorIso TA T P.L)).mpr
      ((TA T P.L).tensor_isTensorAlgebra.descAny_extends (pushforwardUnitGradedAlgebra g) κ)
  exact congrArg (fun m : (TA T P.L).tensor.piece 1 ⟶ pushforwardUnit g =>
    φ (ofPushforwardUnit g (m.val.app (op (f ⁻¹ᵁ U)) y))) hdesc

/-- The section of `ℒ` over `f⁻¹U` that a degree-one homogeneous section of the graded algebra
over `U` induces: the pair's graded map in degree one, read through the identification of the
degree-one piece of the tensor algebra with `ℒ`. -/
public def pairSectionOne (s : A.sectionPieces U 1) : (P.L).val.obj (op (f ⁻¹ᵁ U)) :=
  (tensorGeneratorIso TA T P.L).inv.val.app (op (f ⁻¹ᵁ U)) ((P.ψ 1).val.app (op U) s)

/-- **The coefficient the chart inverts, computed.** The degree-one coefficient of the
dehomogenization at a trivialization datum built from `g`, `κ` and `φ` is the image under `φ` of
the trivialization of the section of `ℒ` induced by `s`.

So the hypothesis of `toRelativeProjOfPair` — that this coefficient is a unit — says exactly
that `κ` carries the induced section of `ℒ` to a unit of `Γ(X, g⁻¹f⁻¹U)` after `φ`, which is a
statement about one section of an invertible sheaf and is therefore checkable on a cover. -/
public theorem datumOfTrivialization_pairPieceHom_one (κ : P.L ⟶ pushforwardUnit g)
    (φ : X.ringCatSheaf.obj.obj (op (g ⁻¹ᵁ (f ⁻¹ᵁ U))) →+* B) (s : A.sectionPieces U 1) :
    pairPieceHom A TA P U (datumOfTrivialization A TA P U g κ φ) 1 s =
      φ (ofPushforwardUnit g (κ.val.app (op (f ⁻¹ᵁ U)) (pairSectionOne A TA P U s))) :=
  datumOfTrivialization_toFun_one A TA P U g κ φ ((P.ψ 1).val.app (op U) s)

/-! ### The chart morphism a trivialization classifies -/

/-- The restriction map to global sections, for a morphism whose inverse image of `f⁻¹U` is all
of `X`. This is the ring homomorphism `datumOfTrivialization` is fed when `g` is the inclusion of
an open of the test scheme contained in `f⁻¹U`. -/
public def restrictPreimageTop (h : g ⁻¹ᵁ (f ⁻¹ᵁ U) = ⊤) :
    Γ(X, g ⁻¹ᵁ (f ⁻¹ᵁ U)) →+* Γ(X, ⊤) :=
  (X.presheaf.map (homOfLE (le_of_eq h.symm)).op).hom

/-- **The morphism into relative `Proj` that a trivialized pair classifies on a chart.** Given a
morphism `g : X ⟶ T` into the test scheme, a map `κ : ℒ ⟶ g_*𝒪_X`, a ring homomorphism `φ` out of
`Γ(X, g⁻¹f⁻¹U)`, and a degree-one homogeneous section `s` of the algebra over an affine open `U`
of the base whose induced section of `ℒ` becomes a unit, the dehomogenization at the
trivialization datum of `s` is a morphism `X ⟶ Proj_S(𝒜)`.

This is `toRelativeProjOfPair` at the datum constructed above; the hypothesis is the one
`datumOfTrivialization_pairPieceHom_one` computes. -/
public def toRelativeProjOfTrivialization (hU : IsAffineOpen U) (κ : P.L ⟶ pushforwardUnit g)
    (φ : Γ(X, g ⁻¹ᵁ (f ⁻¹ᵁ U)) →+* Γ(X, ⊤)) {s : A.sectionPieces U 1}
    (hu : IsUnit (φ (ofPushforwardUnit g (κ.val.app (op (f ⁻¹ᵁ U))
      (pairSectionOne A TA P U s))))) :
    X ⟶ (relativeProj A).scheme :=
  toRelativeProjOfPair A TA P U (datumOfTrivialization A TA P U g κ φ) hU
    (s := s) ((datumOfTrivialization_pairPieceHom_one A TA P U g κ φ s).symm ▸ hu)

/-- The chart morphism lies over the affine open of the base it was built on. -/
public theorem toRelativeProjOfTrivialization_comp_toBase (hU : IsAffineOpen U)
    (κ : P.L ⟶ pushforwardUnit g) (φ : Γ(X, g ⁻¹ᵁ (f ⁻¹ᵁ U)) →+* Γ(X, ⊤))
    {s : A.sectionPieces U 1}
    (hu : IsUnit (φ (ofPushforwardUnit g (κ.val.app (op (f ⁻¹ᵁ U))
      (pairSectionOne A TA P U s))))) :
    toRelativeProjOfTrivialization A TA P U g hU κ φ hu ≫ (relativeProj A).toBase =
      fromOfPair A TA P U (datumOfTrivialization A TA P U g κ φ)
          ((datumOfTrivialization_pairPieceHom_one A TA P U g κ φ s).symm ▸ hu) ≫
        projInclusionToOpen A U hU ≫ U.ι :=
  toRelativeProjOfPair_comp_toBase A TA P U (datumOfTrivialization A TA P U g κ φ) hU _

end Pair

end Stacks.AlgebraicGeometry.ProjF1Dehomogenization

end
