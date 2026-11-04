module

public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.PullbackIsos
public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.TensorLaurent
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.GluedRepresents
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple

/-!
# Tag 01O4's pairs against Section 01NS's quadruples

Tag 01O4's functor `F1` and Section 01NS's functor `F_d` at `d = 1` are two writings of the same
functor, and before this file nothing in the library mentioned both: no declaration related
`Stacks.AlgebraicGeometry.ProjRepresentsF1.F1Pair` to
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple`. The two differ in three respects,
and this file reduces the comparison to one of them.

1. **The graded algebra on the base.** A pair is taken over a
   `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra`, a quadruple over a
   `SheafOfModules.GradedAlgebra`. The comparison is
   `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.situationAlgebra`, already in the library.
2. **The graded algebra of `L`.** A pair's `ψ` lands in the tensor algebra `T(L)`, a quadruple's
   in the Laurent algebra `⨁_{n ∈ ℤ} L^{⊗ n}`. The comparison is
   `Stacks.AlgebraicGeometry.ProjRepresentsF1.tensorToLaurent`, an isomorphism in every
   nonnegative degree.
3. **The direction.** A pair's `ψ` is written through the pullback–pushforward adjunction, as
   maps `A_n ⟶ f_*T(L)_n`; a quadruple's is written directly, as maps `f^*A_n ⟶ L^{⊗ n}`. The
   adjoint transpose is `Stacks.AlgebraicGeometry.ProjRepresentsF1.F1Pair.pullbackMap`, and the
   two adjunctions involved — `AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction`
   and `Stacks.RingedSpace.pullbackAdjunction` of the underlying morphism of ringed spaces — are
   the same adjunction, by `rfl`.

With 1–3 in hand a pair determines a family of morphisms in precisely the shape of
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting.app` — that is
`F1Pair.laurentApp` below — and the surjectivity conditions of the two tags become the same
condition, which is `F1Pair.epi_laurentApp_one`. In a negative degree the family carries no
information at all: its source is a zero object, because a `SheafGradedAlgebra` vanishes in
negative degrees and pullback preserves zero objects.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjRepresentsF1.F1Pair.laurentApp`: **the family of morphisms
  `f^*A_i ⟶ L^{⊗ i}` a pair determines**, in the shape `Twisting.app` has at `d = 1`.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.Quadruple.tensorPsi`: **the family of morphisms
  `A_n ⟶ f_*T(L)_n` a quadruple determines** in each nonnegative degree, in the shape `F1Pair.ψ`
  has. This is the same comparison read backwards.

## Main results

* `Stacks.AlgebraicGeometry.ProjRepresentsF1.epi_pullbackMap_one`: a pair's degree-one
  surjectivity is epimorphy of the adjoint transpose `f^*A_1 ⟶ T(L)_1` itself, the degree-one
  identification of the tensor algebra being an isomorphism.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.F1Pair.epi_laurentApp_one`: **the degree-one
  surjectivity condition of Tag 01O4's pair is the degree-one surjectivity condition of Section
  01NS's quadruple**, `Quadruple.epi_app_one`, for the family `laurentApp`.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.isZero_pullbackPiece_of_neg`: in a negative degree
  the source of `Twisting.app` is a zero object, so the family is determined there.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.epi_isoHom_comp_comp_isoHom` and
  `epi_of_epi_comp_isoHom`: the two epimorphism manipulations the comparison needs, each stated
  in an arbitrary category with every object and morphism free.

## Implementation notes

**The invertibility of a pair's `L` is a field, and the Laurent algebra takes it as an
instance.** Every statement below that mentions `laurent P.L` therefore opens with
`letI := P.invertible`, which is the idiom the fields of
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple` itself use. The declarations that do
not need the pair — `isZero_pullbackPiece_of_neg`, `epi_pullbackMap_one` — are stated without
it.

**`epi_of_epi_comp_iso` is proved here rather than found.** Cancelling an isomorphism on the
right of an epimorphism is not in the library in this form: `CategoryTheory.epi_of_epi` cancels
on the *left*, concluding epimorphy of the second factor. The three `eqToHom`s that occur are
given their `IsIso` instances by hand through `eqToIso`, which instance search does not do.

## References

* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)

## Not done here

**No project tag is attached, and the pair a quadruple determines is not built.** The quadruple a
pair determines is `Stacks.AlgebraicGeometry.ProjRepresentsF1.F1Pair.quadruple`, in
`StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.QuadrupleFromPair`: of the three fields of
`Twisting` the family `laurentApp` built here supplies `app`, `Quadruple.epi_app_one` is
`F1Pair.epi_laurentApp_one` below, and the two remaining clauses are `laurentApp_app_mul` and
`laurentApp_app_one` there. What Tag 01O4 asserts is representability, so the converse
construction — the pair a quadruple determines, of which `quadrupleTensorPsi` below is the map —
and the two directions being mutually inverse are still owed.

-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.RingedSpace

namespace Stacks.AlgebraicGeometry.ProjRepresentsF1

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

/-! ### Cancelling an isomorphism on the right of an epimorphism -/

/-- An epimorphism with an isomorphism cancelled on the right is an epimorphism. -/
public theorem epi_of_epi_comp_isoHom {C : Type*} [Category C] {X Y Z : C} (u : X ⟶ Y)
    (e : Y ≅ Z) (h : Epi (u ≫ e.hom)) : Epi u := by
  have e' : u = (u ≫ e.hom) ≫ e.inv := by
    rw [Category.assoc, e.hom_inv_id, Category.comp_id]
  rw [e']
  exact @epi_comp _ _ _ _ _ _ h _ inferInstance

/-- **An epimorphism between two isomorphisms is an epimorphism.** Every object and every
morphism is free, so that the statement is applied with `exact` and the `Category` instance is
taken from the goal; the same statement at the sheaf-of-modules spelling is not found by
instance search, the invertibility and the composition reaching the `Category` instance by two
different routes. -/
public theorem epi_isoHom_comp_comp_isoHom {C : Type*} [Category C] {W X Y Z : C} (a : W ≅ X)
    (b : X ⟶ Y) (c : Y ≅ Z) (hb : Epi b) : Epi (a.hom ≫ b ≫ c.hom) := by
  have := hb
  infer_instance

variable {S T : Scheme.{u}} (A : SheafGradedAlgebra.{u} S) (TA : TensorAlgebras.{u})
  (f : T ⟶ S)

/-! ### Negative degrees carry no information -/

/-- **In a negative degree the source of `Twisting.app` is a zero object.** A graded algebra of
Situation 01NN vanishes in negative degrees and pullback carries a zero object to a zero object,
so a quadruple's `ψ` is determined there, and so is the family a pair determines. -/
public theorem isZero_pullbackPiece_of_neg {n : ℤ} (hn : n < 0) :
    IsZero ((Scheme.Modules.pullback f).obj ((situationAlgebra A).piece n)) :=
  isZero_pullback_obj f (A.negative_isZero n hn)

/-! ### The family a degreewise map into the tensor algebra determines -/

section Family

variable (L : T.Modules) [Stacks.SheafOfModules.IsInvertible T.presheaf T.ringCatSheaf.2 L]

/-- **The family of morphisms `f^*A_i ⟶ L^{⊗ i}` determined by a degreewise family
`f^*A_i ⟶ T(L)_i`**, in precisely the shape the field `app` of
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting` has at `d = 1`: the comparison of the
tensor algebra of `L` with its Laurent algebra, precomposed with the degree bookkeeping
`i * 1 = i`. -/
public def laurentAppOf
    (φ : ∀ n : ℤ, (Scheme.Modules.pullback f).obj (A.piece n) ⟶ (TA T L).tensor.piece n)
    (i : ℤ) :
    (pullbackFunctor (ringedSpaceHom f)).obj ((situationAlgebra A).piece (i * 1)) ⟶
      (laurent L).piece i :=
  eqToHom (congrArg (fun k : ℤ => (pullbackFunctor (ringedSpaceHom f)).obj (A.piece k))
      (mul_one i)) ≫
    φ i ≫ (tensorToLaurent L (TA T L)).app i

/-- **A degreewise family with epimorphic degree-one component gives an epimorphic degree-one
component of the Laurent family**, the two differing by the degree bookkeeping `1 * 1 = 1` and
by the comparison of the two graded algebras of `L`, which is an isomorphism in degree one. -/
public theorem epi_laurentAppOf_one
    (φ : ∀ n : ℤ, (Scheme.Modules.pullback f).obj (A.piece n) ⟶ (TA T L).tensor.piece n)
    (h : Epi (φ 1)) : Epi (laurentAppOf A TA f L φ 1) :=
  have : IsIso ((tensorToLaurent L (TA T L)).app 1) :=
    isIso_tensorToLaurent_app L (TA T L) 1 Int.one_nonneg
  epi_isoHom_comp_comp_isoHom
    (eqToIso (congrArg
      (fun k : ℤ => (pullbackFunctor (ringedSpaceHom f)).obj (A.piece k)) (mul_one (1 : ℤ))))
    (φ 1) (asIso ((tensorToLaurent L (TA T L)).app 1)) h

end Family

/-! ### The degree-one surjectivity conditions are the same condition -/

/-- **A pair's degree-one surjectivity is epimorphy of its adjoint transpose in degree one.**
The clause `F1Pair.degreeOneSurjective` asks for epimorphy of that transpose composed with the
degree-one identification of the tensor algebra and the identification of the first tensor power
with `L`; both of those are isomorphisms. -/
public theorem epi_pullbackMap_one (P : F1Pair A TA f) : Epi (P.pullbackMap A TA 1) :=
  epi_of_epi_comp_isoHom _
    ((TA T P.L).tensorPieceIso 1 ≪≫ eqToIso (by rfl : SheafOfModules.tensorPower
      (Opens.grothendieckTopology ↥T) P.L 1 = P.L))
    P.degreeOneSurjective

namespace F1Pair

/-- **The family of morphisms `f^*A_i ⟶ L^{⊗ i}` determined by a pair of Tag 01O4**, in
precisely the shape the field `app` of
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting` has at `d = 1`. -/
public def laurentApp (P : F1Pair A TA f) (i : ℤ) :
    letI := P.invertible
    (pullbackFunctor (ringedSpaceHom f)).obj ((situationAlgebra A).piece (i * 1)) ⟶
      (laurent P.L).piece i :=
  letI := P.invertible
  laurentAppOf A TA f P.L (P.pullbackMap A TA) i

/-- **The degree-one surjectivity condition of Tag 01O4's pair is the degree-one surjectivity
condition of Section 01NS's quadruple.** `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.`
`Quadruple.epi_app_one` asks for epimorphy of `ψ_1`, and for the family a pair determines that is
`F1Pair.degreeOneSurjective`. -/
public theorem epi_laurentApp_one (P : F1Pair A TA f) :
    letI := P.invertible
    Epi (P.laurentApp A TA f 1) :=
  let := P.invertible
  epi_laurentAppOf_one A TA f P.L (P.pullbackMap A TA) (epi_pullbackMap_one A TA f P)

end F1Pair

/-! ### The comparison read backwards -/

/-- **The family of morphisms `A_n ⟶ f_*T(L)_n` determined by a quadruple of Section 01NS** in
each nonnegative degree, in precisely the shape the field `ψ` of
`Stacks.AlgebraicGeometry.ProjRepresentsF1.F1Pair` has: the quadruple's `ψ` read back through
the isomorphism `Tⁿ(L) ≅ L^{⊗ n}` and transposed across the pullback-pushforward adjunction.

Only the nonnegative degrees are covered, because the tensor algebra vanishes in the others. -/
public def quadrupleTensorPsi
    (Q : RelativeProjQcohSheaf.Quadruple f (situationAlgebra A) 1) (n : ℕ) :
    A.piece (n : ℤ) ⟶
      (Scheme.Modules.pushforward f).obj ((TA T Q.L).tensor.piece (n : ℤ)) :=
  letI := Q.isInvertible
  (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
    (eqToHom (congrArg (fun k : ℤ => (pullbackFunctor (ringedSpaceHom f)).obj (A.piece k))
        (mul_one (n : ℤ)).symm) ≫
      Q.twisting.app (n : ℤ) ≫ (tensorPieceIsoLaurentPiece Q.L (TA T Q.L) n).inv)

end Stacks.AlgebraicGeometry.ProjRepresentsF1

end
