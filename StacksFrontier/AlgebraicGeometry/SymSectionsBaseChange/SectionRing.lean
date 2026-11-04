module

public import StacksFrontier.AlgebraicGeometry.SymSectionsBaseChange.Unit
public import StacksFrontier.AlgebraicGeometry.RelativeProjBridge.SectionRing

/-!
# The graded ring of sections of `Sym(E)` over an affine open IS a symmetric algebra

Let `X` be a scheme, `E` a quasi-coherent `𝒪_X`-module and `V` an affine open of `X`. This file
proves

`Γ(V, Sym(E)) ≅ Sym_{Γ(X, V)}(Γ(E, V))`

as **graded `Γ(X, V)`-algebras**, where the left-hand side is
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.sectionRing` of
`Stacks.SymGraded.schemeSheafGradedAlgebra E` — the graded ring Situation 01NN forms out of the
sheaf-level data and the relative homogeneous spectrum is built from.

This is one of the three inputs of Tag 0B3V's sixth label named in the `Not done here` section
of `Stacks.ProjBundleBaseChangeReduction`: the identification of `Γ(W, Sym(E'))` with the
symmetric algebra of `Γ(W, E')` over `Γ(X', W)`.

## Main definitions

* `Stacks.SymGraded.AffinePieces.sectionAlgebra`: the `Γ(X, V)`-algebra structure on the graded
  ring of sections, through
  `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.strHom`.
* `Stacks.SymGraded.AffinePieces.gradedSectionsRingEquiv`: the degreewise identification,
  assembled over the degrees: `(⨁ n : ℕ, Sym^n_{Γ(X, V)}(Γ(E, V))) ≃+* Γ(V, Sym(E))`.
* `Stacks.SymGraded.AffinePieces.symSectionRingEquiv` and `symSectionAlgEquiv`: **the
  identification**, as a ring isomorphism and as a `Γ(X, V)`-algebra isomorphism
  `Γ(V, Sym(E)) ≅ Sym_{Γ(X, V)}(Γ(E, V))`.

## Main results

* `Stacks.SymGraded.AffinePieces.pieceSectionsEquiv_mul` and `pieceSectionsEquiv_one`: the
  sheafification unit is multiplicative and unital — this is what makes the degreewise
  identification of `StacksDraft.AlgebraicGeometry.F3.SymSectionsBaseChange.Unit` an
  identification of *rings*, and it needs no new work: it is
  `Stacks.GradedAlgebra.sheafifyMul_unit` and `sheafify_one_eval`.
* `Stacks.SymGraded.AffinePieces.symSectionRingEquiv_of`: **the characterizing equation.** On the
  degree-`n` summand the isomorphism is the inverse of the sheafification unit, followed by the
  inclusion of `Sym^n` into `Sym`. A `def` producing data is pinned down by this.
* `Stacks.SymGraded.AffinePieces.mem_symmetricPower_symSectionRingEquiv`: **it is an isomorphism
  of graded rings**: a section is homogeneous of degree `n` exactly when its image lies in
  `Sym^n_{Γ(X, V)}(Γ(E, V))`.

## Implementation notes

**Multiplicativity is proved on the source and transported, not on the target.** The map built
first is `gradedSectionsRingEquiv`, out of the *external* direct sum
`⨁ n : ℕ, Sym^n_{Γ(X, V)}(Γ(E, V))`, because `DirectSum.toSemiring` turns a family of additive
maps into a ring homomorphism out of the direct sum given only the unit and the product of two
*homogeneous* elements, and because the remaining identification is then available:
`DirectSum.decomposeRingEquiv` at the internal grading of the symmetric algebra
(`SymmetricAlgebra.gradedAlgebra`). Proving multiplicativity directly for a map *out of*
`Γ(V, Sym(E))` would need a decomposition of a general section, which is exactly what the direct
sum provides. The hand-rolled route — a double `DirectSum.induction_on` with
`rw [add_mul, map_add, ...]` — exceeds the heartbeat budget at `isDefEq`, because the ring
instance on the section ring of a *concrete* `Stacks.SymGraded.schemeSheafGradedAlgebra` is a
`DirectSum.GCommRing` that `rw`'s motive has to unify through. `DirectSum.toSemiring` never
mentions it.

**A statement must not name `GradedMonoid.GMul.mul` at the symmetric powers.** Writing
`DirectSum.of (fun n : ℕ => SymPow.symmetricPower n R M) (i + j) (GradedMonoid.GMul.mul a b)` in
a statement elaborates `GMul.mul` at the wrong instance and reports its type as a subtype of a
*sum* of membership predicates; and `DirectSum.of_mul_of` without an explicit `A :=` fails
higher-order unification and asks for `DecidableEq (SymmetricAlgebra R M → Prop)`. Both are
avoided below by letting the obligation's own expected type supply the family, which is why
multiplicativity is discharged inside `DirectSum.toSemiring` rather than stated first.

**The degree casts are discharged by definitional equality and never rewritten.** The section
ring is `ℕ`-graded and the sheaf-level pieces are `ℤ`-indexed, so the product of the degree-`i`
and degree-`j` summands is stated at `((i + j : ℕ) : ℤ)` on one side and at `(i : ℤ) + (j : ℤ)`
on the other. `Nat.cast` into `ℤ` is `Int.ofNat` and `Int.add` reduces on constructors, so the
two are definitionally equal; every such step below is an `exact` or a `show`, never a `rw`,
which would fail on the syntactic mismatch.

**Every hypothesis the proof consumes is in the signature.** Affineness of `V` enters only
through `Stacks.SymGraded.AffinePieces.pieceSectionsEquiv`, and quasi-coherence of `E` only
through that and through `Stacks.SymGraded.IsQuasicoherentPieces`; the quasi-coherence of the
pieces is carried as the explicit argument `hqc` rather than derived, so that the isomorphism is
about the same `Stacks.SymGraded.schemeSheafGradedAlgebra` term a consumer holds.

## References

* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)

## Not done here

**No tag is attached.** Tag 0B3V's sixth label is the base projection of a
base-change comparison of projective bundles; this file is one of its three inputs and carries no
labelled assertion of any tag. Nothing here mentions a morphism of bases.

Nothing here is said about a non-affine open: for a general `V` the sheafification unit is
neither injective nor surjective on sections and there is no such identification.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge
open scoped DirectSum

namespace Stacks.SymGraded.AffinePieces

universe u

variable {X : Scheme.{u}} (E : X.Modules) {V : X.Opens} (hV : IsAffineOpen V)

/-! ### Multiplicativity of the sheafification unit -/

variable (hqc : IsQuasicoherentPieces E)

/-- **The sheafification unit is multiplicative.** This is
`Stacks.GradedAlgebra.sheafifyMul_unit` at the sectionwise symmetric algebra: the product of two
unit-images is the unit-image of the product. -/
theorem pieceSectionsEquiv_mul [E.IsQuasicoherent] (i j : ℤ)
    (x : gradedPiece (R := Γ(X, V)) Γ(E, V) i) (y : gradedPiece (R := Γ(X, V)) Γ(E, V) j) :
    ((schemeSheafGradedAlgebra E hqc).mul i j).app V
        (pieceSectionsEquiv E hV i x) (pieceSectionsEquiv E hV j y) =
      pieceSectionsEquiv E hV (i + j) (symMulₗ Γ(E, V) i j x y) :=
  (sitePresheafAlgebra E.val).sheafifyMul_unit (𝟙 X.ringCatSheaf.obj) i j (op V) x y

/-- **The sheafification unit carries the unit to the unit.** -/
theorem pieceSectionsEquiv_one [E.IsQuasicoherent] :
    (schemeSheafGradedAlgebra E hqc).one V =
      pieceSectionsEquiv E hV ((0 : ℕ) : ℤ) (oneG Γ(E, V)) :=
  (sitePresheafAlgebra E.val).sheafify_one_eval (𝟙 X.ringCatSheaf.obj) (op V)

/-- The sheafification unit is `Γ(X, V)`-linear, being the component of a morphism of presheaves
of `𝒪_X`-modules. The target is spelled
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.sectionPieces`: at the
spelling `Γ((Scheme.Modules.symmetricAlgebra X E).piece n, V)` instance search does **not**
find the
`Γ(X, V)`-action, because `Scheme.Modules` is a `def` and the piece of a bare
`SheafOfModules.GradedAlgebra` is not one. -/
theorem pieceSectionsEquiv_smul [E.IsQuasicoherent] (n : ℕ) (r : Γ(X, V))
    (x : gradedPiece (R := Γ(X, V)) Γ(E, V) (n : ℤ))
    (y : (schemeSheafGradedAlgebra E hqc).sectionPieces V n)
    (hy : y = pieceSectionsEquiv E hV (n : ℤ) x) :
    r • y = pieceSectionsEquiv E hV (n : ℤ) (r • x) := by
  subst hy
  exact ((PresheafOfModules.Hom.app
    (PresheafOfModules.sheafifyUnit (𝟙 X.ringCatSheaf.obj)
      (siteGradedPiece E.val (n : ℤ))) (op V)).hom.map_smul r x).symm

/-! ### The graded ring of sections -/

/-- **Multiplication by the structure map of a degree-`0` function is the action of that
function**, on the whole graded ring of sections and not only on a homogeneous summand. This is
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.strHom_mul_apply` read through
extensionality of a direct sum. -/
theorem strHom_mul_eq_smul {S : Scheme.{u}} (A : SheafGradedAlgebra S) (U : S.Opens)
    (r : Γ(S, U)) (x : A.sectionRing U) : A.strHom U r * x = r • x :=
  DFinsupp.ext fun n => A.strHom_mul_apply U r x n

/-- The structure map is multiplication of the unit by a function. -/
theorem smul_one_eq_strHom {S : Scheme.{u}} (A : SheafGradedAlgebra S) (U : S.Opens)
    (r : Γ(S, U)) : r • (1 : A.sectionRing U) = A.strHom U r :=
  ((mul_one (A.strHom U r)).symm.trans (strHom_mul_eq_smul A U r 1)).symm

/-- **The `Γ(S, U)`-algebra structure on the graded ring of sections of a sheaf-level graded
algebra**, whose underlying module structure is the *direct sum's own*, and whose structure map is
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.strHom`
(`algebraMap_sectionRingAlgebra`).

**It must be built this way and not as `(A.strHom U).toAlgebra`, for the following reason**: the
direct sum `⨁ n, Γ(A.piece n, U)` already carries a `Γ(S, U)`-module structure, pointwise in the
summands, and that is the one instance search finds when elaborating `· ⊗[Γ(S, U)] ·`. The module
structure underlying `(A.strHom U).toAlgebra` is a *different* term — the two are not
definitionally equal, and `Module Γ(S, U) (A.sectionRing U)` found by `inferInstance` is
provably not syntactically `Algebra.toModule` for it — so with that algebra structure in scope
`Γ(S', W) ⊗[Γ(S, U)] A.sectionRing U` has **no `Semiring` instance at all** and the base-change
isomorphism below is not even statable. `Algebra.ofModule'` keeps the pointwise module and
proves compatibility instead, which is exactly `strHom_mul_eq_smul`. -/
@[instance_reducible]
def sectionRingAlgebra {S : Scheme.{u}} (A : SheafGradedAlgebra S) (U : S.Opens) :
    Algebra Γ(S, U) (A.sectionRing U) :=
  Algebra.ofModule'
    (fun r x => by rw [smul_one_eq_strHom]; exact strHom_mul_eq_smul A U r x)
    (fun r x => by rw [mul_comm, smul_one_eq_strHom]; exact strHom_mul_eq_smul A U r x)

/-- The algebra map of `sectionRingAlgebra A U` is the structure morphism `A.strHom U`. -/
theorem algebraMap_sectionRingAlgebra {S : Scheme.{u}} (A : SheafGradedAlgebra S) (U : S.Opens)
    (r : Γ(S, U)) :
    letI := sectionRingAlgebra A U
    algebraMap Γ(S, U) (A.sectionRing U) r = A.strHom U r :=
  let := sectionRingAlgebra A U
  smul_one_eq_strHom A U r

/-- The `Γ(X, V)`-algebra structure on the graded ring of sections of `Sym(E)`. -/
@[instance_reducible]
def sectionAlgebra : Algebra Γ(X, V) ((schemeSheafGradedAlgebra E hqc).sectionRing V) :=
  sectionRingAlgebra (schemeSheafGradedAlgebra E hqc) V

/-- The forward map of `Stacks.SymGraded.AffinePieces.gradedSectionsRingEquiv`: on the degree-`n`
summand, the sheafification unit. -/
def ofGradedSections [E.IsQuasicoherent] :
    (⨁ n : ℕ, SymPow.symmetricPower n Γ(X, V) Γ(E, V)) →+
      (schemeSheafGradedAlgebra E hqc).sectionRing V :=
  DirectSum.toAddMonoid fun n =>
    (DirectSum.of ((schemeSheafGradedAlgebra E hqc).sectionPieces V) n).comp
      (pieceSectionsEquiv E hV (n : ℤ)).toAddMonoidHom

/-- The backward map, on the degree-`n` summand the inverse of the sheafification unit. -/
def toGradedSections [E.IsQuasicoherent] :
    (schemeSheafGradedAlgebra E hqc).sectionRing V →+
      ⨁ n : ℕ, SymPow.symmetricPower n Γ(X, V) Γ(E, V) :=
  DirectSum.toAddMonoid fun n =>
    (DirectSum.of (fun n : ℕ => SymPow.symmetricPower n Γ(X, V) Γ(E, V)) n).comp
      (pieceSectionsEquiv E hV (n : ℤ)).symm.toAddMonoidHom

/-- On the degree-`n` summand, `ofGradedSections` is the degree-`n` `pieceSectionsEquiv`. -/
@[simp]
theorem ofGradedSections_of [E.IsQuasicoherent] (n : ℕ)
    (x : SymPow.symmetricPower n Γ(X, V) Γ(E, V)) :
    ofGradedSections E hV hqc
        (DirectSum.of (fun n : ℕ => SymPow.symmetricPower n Γ(X, V) Γ(E, V)) n x) =
      DirectSum.of ((schemeSheafGradedAlgebra E hqc).sectionPieces V) n
        (pieceSectionsEquiv E hV (n : ℤ) x) :=
  DirectSum.toAddMonoid_of
    (fun n : ℕ =>
      (DirectSum.of ((schemeSheafGradedAlgebra E hqc).sectionPieces V) n).comp
        (pieceSectionsEquiv E hV (n : ℤ)).toAddMonoidHom) n x

/-- On the degree-`n` summand, `toGradedSections` is the inverse of the degree-`n`
`pieceSectionsEquiv`. -/
@[simp]
theorem toGradedSections_of [E.IsQuasicoherent] (n : ℕ)
    (x : (schemeSheafGradedAlgebra E hqc).sectionPieces V n) :
    toGradedSections E hV hqc
        (DirectSum.of ((schemeSheafGradedAlgebra E hqc).sectionPieces V) n x) =
      DirectSum.of (fun n : ℕ => SymPow.symmetricPower n Γ(X, V) Γ(E, V)) n
        ((pieceSectionsEquiv E hV (n : ℤ)).symm x) :=
  DirectSum.toAddMonoid_of
    (fun n : ℕ =>
      (DirectSum.of (fun n : ℕ => SymPow.symmetricPower n Γ(X, V) Γ(E, V)) n).comp
        (pieceSectionsEquiv E hV (n : ℤ)).symm.toAddMonoidHom) n x

/-- **The degreewise identification, assembled over the degrees and multiplicatively.** The
external direct sum of the symmetric powers of `Γ(E, V)` is the graded ring of sections of
`Sym(E)` over `V`. -/
def gradedSectionsAddEquiv [E.IsQuasicoherent] :
    (⨁ n : ℕ, SymPow.symmetricPower n Γ(X, V) Γ(E, V)) ≃+
      (schemeSheafGradedAlgebra E hqc).sectionRing V where
  toFun := ofGradedSections E hV hqc
  invFun := toGradedSections E hV hqc
  left_inv := fun x => DFunLike.congr_fun
    (show (toGradedSections E hV hqc).comp (ofGradedSections E hV hqc) = AddMonoidHom.id _ from by
      refine DirectSum.addHom_ext fun n x => ?_
      exact ((congrArg (toGradedSections E hV hqc)
          (ofGradedSections_of E hV hqc n x)).trans
        (toGradedSections_of E hV hqc n _)).trans
          (congrArg _ ((pieceSectionsEquiv E hV (n : ℤ)).symm_apply_apply x))) x
  right_inv := fun x => DFunLike.congr_fun
    (show (ofGradedSections E hV hqc).comp (toGradedSections E hV hqc) = AddMonoidHom.id _ from by
      refine DirectSum.addHom_ext fun n x => ?_
      exact ((congrArg (ofGradedSections E hV hqc)
          (toGradedSections_of E hV hqc n x)).trans
        (ofGradedSections_of E hV hqc n _)).trans
          (congrArg _ ((pieceSectionsEquiv E hV (n : ℤ)).apply_symm_apply x))) x
  map_add' x y := map_add (ofGradedSections E hV hqc) x y

/-- The degreewise identification as a **ring** homomorphism, by `DirectSum.toSemiring`: a family
of additive maps that carries the graded unit to the unit and the graded product of two
homogeneous elements to the product is a ring homomorphism out of the direct sum. -/
def ofGradedSectionsRingHom [E.IsQuasicoherent] :
    (⨁ n : ℕ, SymPow.symmetricPower n Γ(X, V) Γ(E, V)) →+*
      (schemeSheafGradedAlgebra E hqc).sectionRing V :=
  DirectSum.toSemiring
    (fun n => (DirectSum.of ((schemeSheafGradedAlgebra E hqc).sectionPieces V) n).comp
      (pieceSectionsEquiv E hV (n : ℤ)).toAddMonoidHom)
    (by
      refine Eq.symm ((DirectSum.one_def
        ((schemeSheafGradedAlgebra E hqc).sectionPieces V)).trans ?_)
      exact congrArg _ (pieceSectionsEquiv_one E hV hqc))
    (fun {i j} a b => by
      refine Eq.symm ((DirectSum.of_mul_of
        (A := (schemeSheafGradedAlgebra E hqc).sectionPieces V)
        (pieceSectionsEquiv E hV (i : ℤ) a) (pieceSectionsEquiv E hV (j : ℤ) b)).trans ?_)
      refine DirectSum.of_eq_of_gradedMonoid_eq
        ((schemeSheafGradedAlgebra E hqc).gradedMonoid_ext V rfl (heq_of_eq ?_))
      refine ((schemeSheafGradedAlgebra E hqc).gMul_def V
        (pieceSectionsEquiv E hV (i : ℤ) a) (pieceSectionsEquiv E hV (j : ℤ) b)).trans ?_
      exact (pieceSectionsEquiv_mul E hV hqc (i : ℤ) (j : ℤ) a b).trans rfl)

/-- The degreewise identification is multiplicative. -/
theorem ofGradedSections_mul [E.IsQuasicoherent]
    (x y : ⨁ n : ℕ, SymPow.symmetricPower n Γ(X, V) Γ(E, V)) :
    ofGradedSections E hV hqc (x * y) =
      ofGradedSections E hV hqc x * ofGradedSections E hV hqc y :=
  map_mul (ofGradedSectionsRingHom E hV hqc) x y

/-- The degreewise identification as a ring isomorphism. -/
def gradedSectionsRingEquiv [E.IsQuasicoherent] :
    (⨁ n : ℕ, SymPow.symmetricPower n Γ(X, V) Γ(E, V)) ≃+*
      (schemeSheafGradedAlgebra E hqc).sectionRing V :=
  { gradedSectionsAddEquiv E hV hqc with
    map_mul' := ofGradedSections_mul E hV hqc }

/-- **`Γ(V, Sym(E))` is the symmetric algebra of `Γ(E, V)` over `Γ(X, V)`**, for `V` an affine
open and `E` a quasi-coherent module: the graded ring of sections of `Sym(E)` over `V` is the
symmetric algebra of the sections of `E` over `V`. -/
def symSectionRingEquiv [E.IsQuasicoherent] :
    (schemeSheafGradedAlgebra E hqc).sectionRing V ≃+*
      SymmetricAlgebra Γ(X, V) Γ(E, V) :=
  (gradedSectionsRingEquiv E hV hqc).symm.trans
    (DirectSum.decomposeRingEquiv
      (fun n : ℕ => SymPow.symmetricPower n Γ(X, V) Γ(E, V))).symm

/-- The isomorphism, unfolded: the inverse of the degreewise identification followed by the
decomposition of the symmetric algebra into its symmetric powers. -/
theorem symSectionRingEquiv_apply [E.IsQuasicoherent]
    (x : (schemeSheafGradedAlgebra E hqc).sectionRing V) :
    symSectionRingEquiv E hV hqc x =
      (DirectSum.decomposeRingEquiv
        (fun n : ℕ => SymPow.symmetricPower n Γ(X, V) Γ(E, V))).symm
          (toGradedSections E hV hqc x) := rfl

/-- **The characterizing equation**: on the degree-`n` summand the isomorphism is the inverse of
the sheafification unit, followed by the inclusion of `Sym^n` into `Sym`. -/
theorem symSectionRingEquiv_of [E.IsQuasicoherent] (n : ℕ)
    (x : (schemeSheafGradedAlgebra E hqc).sectionPieces V n) :
    symSectionRingEquiv E hV hqc
        (DirectSum.of ((schemeSheafGradedAlgebra E hqc).sectionPieces V) n x) =
      ((pieceSectionsEquiv E hV (n : ℤ)).symm x : SymmetricAlgebra Γ(X, V) Γ(E, V)) := by
  rw [symSectionRingEquiv_apply, toGradedSections_of]
  exact DirectSum.decompose_symm_of _ _

/-- **The isomorphism respects the grading**: a section of `Sym(E)` over `V` is homogeneous of
degree `n` exactly when its image lies in the `n`-th symmetric power. So this is an isomorphism
of **graded** rings and not merely of rings. -/
theorem mem_symmetricPower_symSectionRingEquiv [E.IsQuasicoherent] (n : ℕ)
    (x : (schemeSheafGradedAlgebra E hqc).sectionRing V) :
    symSectionRingEquiv E hV hqc x ∈ SymPow.symmetricPower n Γ(X, V) Γ(E, V) ↔
      x ∈ (schemeSheafGradedAlgebra E hqc).grading V n := by
  refine ⟨fun hx => ⟨pieceSectionsEquiv E hV (n : ℤ) ⟨_, hx⟩,
    (symSectionRingEquiv E hV hqc).injective <| (symSectionRingEquiv_of E hV hqc n _).trans <|
      congrArg _ ((pieceSectionsEquiv E hV (n : ℤ)).symm_apply_apply ⟨_, hx⟩)⟩, ?_⟩
  rintro ⟨y, rfl⟩
  rw [symSectionRingEquiv_of]
  exact ((pieceSectionsEquiv E hV (n : ℤ)).symm y).2

/-- **The identification is one of `Γ(X, V)`-algebras.** The structure map of the graded ring of
sections — a function times the unit — is carried to the structure map of the symmetric
algebra. -/
def symSectionAlgEquiv [E.IsQuasicoherent] :
    letI := sectionAlgebra E hqc (V := V)
    (schemeSheafGradedAlgebra E hqc).sectionRing V ≃ₐ[Γ(X, V)]
      SymmetricAlgebra Γ(X, V) Γ(E, V) :=
  letI := sectionAlgebra E hqc (V := V)
  { symSectionRingEquiv E hV hqc with
    commutes' := fun r => by
      have hone : r • (schemeSheafGradedAlgebra E hqc).one V =
          pieceSectionsEquiv E hV ((0 : ℕ) : ℤ) (r • oneG Γ(E, V)) :=
        pieceSectionsEquiv_smul E hV hqc 0 r (oneG Γ(E, V))
          ((schemeSheafGradedAlgebra E hqc).one V) (pieceSectionsEquiv_one E hV hqc)
      change symSectionRingEquiv E hV hqc
          (algebraMap Γ(X, V) ((schemeSheafGradedAlgebra E hqc).sectionRing V) r) =
        algebraMap Γ(X, V) _ r
      rw [algebraMap_sectionRingAlgebra (schemeSheafGradedAlgebra E hqc) V r]
      rw [SheafGradedAlgebra.strHom_apply, symSectionRingEquiv_of, hone,
        AddEquiv.symm_apply_apply]
      change r • (1 : SymmetricAlgebra Γ(X, V) Γ(E, V)) = algebraMap Γ(X, V) _ r
      rw [Algebra.algebraMap_eq_smul_one] }

end Stacks.SymGraded.AffinePieces

end
