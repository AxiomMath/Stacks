module

public import StacksFrontier.AlgebraicGeometry.ProjF1Dehomogenization.Trivialization
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.Scheme
public import StacksFrontier.AlgebraicGeometry.SymmetricAlgebraFunctorial.Basic

/-!
# Dehomogenizing the symmetric algebra at a trivialized quotient

Let `T` be a scheme, `F` an `𝒪_T`-module, `g : X ⟶ T` a morphism and `U ⊆ T` an open. A morphism

`κ : F ⟶ g_*𝒪_X`

is, by the pullback–pushforward adjunction, a trivialized quotient of `F` on `X`: in the
situation of Tag 0B3V it is a surjection `q : F ⟶ 𝓛` followed by a trivialization of `g^*𝓛`.
**This file turns such a `κ` into the ring homomorphism**

`Γ(U, Sym F) ⟶ B`

out of the graded ring of homogeneous sections of the symmetric algebra, for any commutative ring
`B` receiving `Γ(X, g⁻¹U)` — the "dehomogenization" `a ↦ κ(a)/κ(s)ⁿ` of the source's proof, once
a trivializing section has been inverted in `B`.

That ring homomorphism is exactly what the chart construction
`Stacks.AlgebraicGeometry.ProjF1DegreeOneChart.toRelativeProjOfIsUnit` consumes, so this is the
source half of a morphism into `Proj_T(Sym F) = 𝐏(F)` over `U`.

## Why this does not go through `F1Pair`

`Stacks.AlgebraicGeometry.ProjF1Dehomogenization.dehomogenize` is the same construction for a
`Stacks.AlgebraicGeometry.ProjRepresentsF1.F1Pair`, whose graded map is indexed by the *tensor*
algebra of the invertible sheaf and which therefore drags in
`Stacks.AlgebraicGeometry.ProjRepresentsF1.TensorAlgebras`. For the symmetric algebra none of
that is needed: `AlgebraicGeometry.Scheme.Modules.isSymmetricAlgebra_symmetricAlgebra` is the
universal property of `Sym F` over an **arbitrary** scheme, with no quasi-coherence and no
affineness, and `g_*𝒪_X` in every degree is a perfectly good commutative target
(`Stacks.AlgebraicGeometry.ProjF1Dehomogenization.pushforwardUnitGradedAlgebra`). So the graded
map is produced by `desc` rather than assumed, and the whole construction is unconditional.

## Main definitions

* `Stacks.SymmetricDehomogenize.gradedHom`: **the graded algebra map `Sym F ⟶ g_*𝒪_X`** that `κ`
  induces, by the universal property of the symmetric algebra.
* `Stacks.SymmetricDehomogenize.datum`: that map followed by a ring homomorphism out of
  `Γ(X, g⁻¹U)`, as a `Stacks.AlgebraicGeometry.ProjF1Dehomogenization.GradedSectionAlgebraHom`.
* `Stacks.SymmetricDehomogenize.dehomogenize`: **the ring homomorphism
  `Γ(U, Sym F) ⟶ B`.**

## Main results

* `Stacks.SymmetricDehomogenize.pairwiseCommutes_pushforwardUnit`: the commuting hypothesis of
  the universal property holds for *every* `κ : F ⟶ g_*𝒪_X`, because `𝒪_X` is commutative. So
  `gradedHom` needs no hypothesis at all.
* `Stacks.SymmetricDehomogenize.gradedHom_degree_one`: **the normalization.** In degree one the
  graded map is `κ`, read through the degree-one generator of `Sym F`. This is what ties the
  dehomogenization to the quotient it came from.
* `Stacks.SymmetricDehomogenize.dehomogenize_of`: its value on a homogeneous section.
* `Stacks.SymmetricDehomogenize.dehomogenize_of_one`: that value in degree one, written as `φ`
  of `κ` of the section — the form in which the invertibility hypothesis of the chart is
  checked.
* `Stacks.SymmetricDehomogenize.dehomogenize_strHom`: the dehomogenization of the degree-zero
  multiple of the unit, read through the degree-zero component of the graded map.
* `Stacks.SymmetricDehomogenize.gradedHom_app_zero_smul_one`: that component computed — in degree
  zero the graded map **is the structure map of `g`**, and `κ` does not appear in it.
* `Stacks.SymmetricDehomogenize.dehomogenize_strHom_app`: **the degree-zero clause.** The
  degree-zero multiple of the unit attached to a function on the base is sent to `φ` of its
  image under `g`, with `κ` not appearing. This is the hypothesis `hψ0` of
  `Stacks.RelativeProj.Situation.exists_hom_relativeProjToBase`, which is what places the
  classified morphism over `U`.

## Implementation notes

**The degree bookkeeping is the existing one.** `GradedSectionAlgebraHom.map_gmul` is indexed by
`i + j` in `ℤ` while the graded ring of sections is graded by `ℕ`, and `((i + j : ℕ) : ℤ)` is
definitionally `(i : ℤ) + (j : ℤ)`; so `pieceHom_mul` below transfers by `Eq.trans` and a
`congrArg`, exactly as `ProjF1Dehomogenization.pairPieceHom_mul` does, and no transport along an
equality of degrees appears.

**`schemeSheafGradedAlgebra` and `symmetricAlgebra` are the same data.** `piece`, `mul` and `one`
of the former are the latter's by `rfl` (`Stacks.SymGraded.schemeSheafGradedAlgebra_piece`,
`schemeSheafGradedAlgebra_mul_app`, and the `one U := A.one.eval (op U)` field of
`toSheafGradedAlgebra`), so a `GradedSectionAlgebraHom` for `symmetricAlgebra` is applied
directly to the section pieces of `schemeSheafGradedAlgebra` with no comparison map.

**`ofPushforwardUnit` is the identity function** and appears only so that the ring structure of
`Γ(X, g⁻¹U)` can be named where instance search does not see it through the direct image; its
presence in the statements below is bookkeeping, not a comparison.

No `@[stacks]` attribute is attached. This is the source half of the classifying morphism of
Tag 01NA — a construction feeding that tag's statement, not an assertion of it — and Tag 0B3V's
bijection is not reached here.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01NA](https://stacks.math.columbia.edu/tag/01NA)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules
open Stacks.AlgebraicGeometry.ProjF1Dehomogenization
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.SymGraded

universe u

namespace Stacks.SymmetricDehomogenize

variable {X T : Scheme.{u}} (g : X ⟶ T) (F : T.Modules)

/-- **The commuting hypothesis of the symmetric algebra's universal property holds for every map
into `g_*𝒪_X`.** Multiplication in `g_*𝒪_X` is the multiplication of the structure sheaf of `X`,
which is commutative, so nothing is required of `κ`. -/
theorem pairwiseCommutes_pushforwardUnit (κ : F ⟶ pushforwardUnit g) :
    SheafOfModules.GradedAlgebra.PairwiseCommutes
      (A := pushforwardUnitGradedAlgebra g) κ :=
  fun W _ _ => isCommutativeRingSheaf_scheme X (op (g ⁻¹ᵁ W.unop)) _ _

variable (κ : F ⟶ pushforwardUnit g)

/-- **The graded algebra map `Sym F ⟶ g_*𝒪_X` induced by `κ`**, by the universal property of the
symmetric algebra. -/
def gradedHom :
    SheafOfModules.GradedAlgebra.UnitalHom (Scheme.Modules.symmetricAlgebra T F)
      (pushforwardUnitGradedAlgebra g) :=
  (isSymmetricAlgebra_symmetricAlgebra T F).isUniversal.desc
    (pushforwardUnitGradedAlgebra g) κ (pairwiseCommutes_pushforwardUnit g F κ)

/-- **The normalization: in degree one the graded map is `κ`.** -/
theorem gradedHom_degree_one :
    symmetricAlgebraGen T F ≫ (gradedHom g F κ).app 1 = κ :=
  (isSymmetricAlgebra_symmetricAlgebra T F).isUniversal.desc_extends _ _ _

variable (U : T.Opens) {B : Type u} [CommRing B]
  (φ : X.ringCatSheaf.obj.obj (op (g ⁻¹ᵁ U)) →+* B)

/-- **The trivialization datum of `Sym F` at `κ` and `φ`**: in each degree, the graded map
followed by `φ`. -/
def datum : GradedSectionAlgebraHom (Scheme.Modules.symmetricAlgebra T F) (op U) B :=
  GradedSectionAlgebraHom.precomp (gradedHom g F κ) (pushforwardUnitDatum g φ)

/-- In degree `n`, the trivialization datum sends a section `x` of the degree-`n` piece of `Sym F`
to `φ` of its image under the graded map. -/
@[simp]
theorem datum_toFun (n : ℤ)
    (x : ((Scheme.Modules.symmetricAlgebra T F).piece n).val.obj (op U)) :
    (datum g F κ U φ).toFun n x =
      φ (ofPushforwardUnit g (((gradedHom g F κ).app n).val.app (op U) x)) :=
  rfl

/-! ### The ring homomorphism out of the graded ring of sections -/

variable (hqc : IsQuasicoherentPieces F)

/-- The degree-`n` component, on the section pieces of the graded ring, indexed by `ℕ`. -/
def pieceHom (n : ℕ) : (schemeSheafGradedAlgebra F hqc).sectionPieces U n →+ B :=
  (datum g F κ U φ).toFun (n : ℤ)

/-- `pieceHom` in degree `n` is the degree-`n` component of the trivialization datum. -/
theorem pieceHom_apply (n : ℕ) (x : (schemeSheafGradedAlgebra F hqc).sectionPieces U n) :
    pieceHom g F κ U φ hqc n x = (datum g F κ U φ).toFun (n : ℤ) x :=
  rfl

/-- The unit law. -/
theorem pieceHom_one :
    pieceHom g F κ U φ hqc 0 ((schemeSheafGradedAlgebra F hqc).one U) = 1 :=
  (datum g F κ U φ).map_gone

/-- The product law. Both sides read `((i + j : ℕ) : ℤ)` as `(i : ℤ) + (j : ℤ)`, which is
definitional. -/
theorem pieceHom_mul (i j : ℕ) (x : (schemeSheafGradedAlgebra F hqc).sectionPieces U i)
    (y : (schemeSheafGradedAlgebra F hqc).sectionPieces U j) :
    pieceHom g F κ U φ hqc (i + j)
        (((schemeSheafGradedAlgebra F hqc).mul (i : ℤ) (j : ℤ)).app U x y) =
      pieceHom g F κ U φ hqc i x * pieceHom g F κ U φ hqc j y :=
  (datum g F κ U φ).map_gmul (i : ℤ) (j : ℤ) x y

/-- **The dehomogenization of `Sym F` at a trivialized quotient**: the ring homomorphism out of
the graded ring of homogeneous sections of `Sym F` over `U` whose restriction to each degree is
the graded map followed by `φ`. -/
def dehomogenize : (schemeSheafGradedAlgebra F hqc).sectionRing U →+* B :=
  DirectSum.toSemiring (pieceHom g F κ U φ hqc) (pieceHom_one g F κ U φ hqc)
    (fun {i j} x y => pieceHom_mul g F κ U φ hqc i j x y)

/-- On a homogeneous section `x` of degree `n`, the dehomogenization is the degree-`n` component
of the trivialization datum applied to `x`. -/
@[simp]
theorem dehomogenize_of {n : ℕ} (x : (schemeSheafGradedAlgebra F hqc).sectionPieces U n) :
    dehomogenize g F κ U φ hqc
        (DirectSum.of ((schemeSheafGradedAlgebra F hqc).sectionPieces U) n x) =
      (datum g F κ U φ).toFun (n : ℤ) x :=
  DirectSum.toSemiring_of _ _ _ n x

/-- **The degree-one coefficient, computed.** On the degree-one homogeneous section attached to a
section `m` of `F` by the generator of `Sym F`, the dehomogenization is `φ` of the trivialization
`κ m`. So the invertibility hypothesis of the chart — that this coefficient is a unit — says
exactly that `κ` carries `m` to a unit of `Γ(X, g⁻¹U)` after `φ`, which is a statement about one
section of `F` and is therefore checkable on a cover. -/
@[simp]
theorem dehomogenize_of_one (m : F.val.obj (op U)) :
    dehomogenize g F κ U φ hqc
        (DirectSum.of ((schemeSheafGradedAlgebra F hqc).sectionPieces U) 1
          ((symmetricAlgebraGen T F).val.app (op U) m)) =
      φ (ofPushforwardUnit g (κ.val.app (op U) m)) :=
  (dehomogenize_of g F κ U φ hqc ((symmetricAlgebraGen T F).val.app (op U) m)).trans
    (congrArg (fun n : F ⟶ pushforwardUnit g =>
      φ (ofPushforwardUnit g (n.val.app (op U) m))) (gradedHom_degree_one g F κ))

/-- **The degree-zero clause.** On the degree-zero multiple of the unit attached to a function on
the base, the dehomogenization is `φ` of that function's image under `g`; `κ` does not appear.
This is what places the classified morphism over `U`. -/
theorem dehomogenize_strHom (r : Γ(T, U)) :
    dehomogenize g F κ U φ hqc ((schemeSheafGradedAlgebra F hqc).strHom U r) =
      φ (ofPushforwardUnit g
        (((gradedHom g F κ).app 0).val.app (op U) (r • (schemeSheafGradedAlgebra F hqc).one U))) :=
  dehomogenize_of g F κ U φ hqc (r • (schemeSheafGradedAlgebra F hqc).one U)

/-- **In degree zero the graded map is the structure map of `g`, with `κ` nowhere in it.** The
degree-zero piece of `Sym F` is generated over `Γ(T, U)` by the unit, a unital homomorphism
preserves that unit, and the module structure of `g_*𝒪_X` is restriction of scalars along `g^♯`;
so on `r • 1` the graded map is `g^♯ r`.

This is the clause that places the classified morphism over `U`: it is what turns
`dehomogenize_strHom` into `dehomogenize_strHom_app` below, and the latter is the hypothesis
`hψ0` of `Stacks.RelativeProj.Situation.exists_hom_relativeProjToBase`. -/
theorem gradedHom_app_zero_smul_one (r : Γ(T, U)) :
    ofPushforwardUnit g
        (((gradedHom g F κ).app 0).val.app (op U)
          (r • (schemeSheafGradedAlgebra F hqc).one U)) = (g.app U).hom r := by
  have hΦ := (ConcreteCategory.hom (((gradedHom g F κ).app 0).val.app (op U))).map_smul
  refine (congrArg (ofPushforwardUnit g)
    (hΦ r ((schemeSheafGradedAlgebra F hqc).one U))).trans ?_
  exact ofPushforwardUnit_smul_of_eq_one g U r _
    (congrArg (ofPushforwardUnit g) ((gradedHom g F κ).map_one (op U)))

/-- **The degree-zero clause of the dehomogenization.** On the degree-zero multiple of the unit
attached to `r ∈ Γ(T, U)`, the dehomogenization is `φ` of `g^♯ r`: it does not depend on `κ` at
all, so the morphism the chart classifies lies over `U`. -/
theorem dehomogenize_strHom_app (r : Γ(T, U)) :
    dehomogenize g F κ U φ hqc ((schemeSheafGradedAlgebra F hqc).strHom U r) =
      φ ((g.app U).hom r) :=
  (dehomogenize_strHom g F κ U φ hqc r).trans
    (congrArg φ (gradedHom_app_zero_smul_one g F κ U hqc r))

end Stacks.SymmetricDehomogenize

end
