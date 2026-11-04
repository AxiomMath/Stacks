module

public import StacksFrontier.AlgebraicGeometry.RelativeProjBridge.SectionModule
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.GluedRepresents

/-!
# Situation 01NN's graded module, read as a right graded module over a sheaf of graded algebras

Let `S` be a scheme and `𝒜` a quasi-coherent graded `𝒪_S`-algebra (Situation 01NN). A graded
`𝒜`-module in that situation is a
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedModule`: a family of quasi-coherent
`𝒪_S`-modules `ℳ_n`, `n : ℤ`, with an `𝒪_S`-bilinear **left** action
`𝒜_i ⊗ ℳ_j ⟶ ℳ_{i + j}` of the homogeneous pieces of `𝒜`.

The constructions of Tag 01O6 and of Section 27.15 — the sheaf `ℳ̃_T` attached to a quadruple,
the twisting `ψ`, the balancing relations — are all phrased for the vocabulary of Tag 0FQZ,
`SheafOfModules.GradedModule` over a `SheafOfModules.GradedAlgebra`, which carries a **right**
action `ℳ_n ⊗ 𝒜_i ⟶ ℳ_{n + i}`. This file supplies the forgetful reading that crosses between
them, the module-side mirror of
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.situationAlgebra`.

## The flip

The two actions differ in the order of the two factors and therefore in the spelling of the
resulting degree: a left action in degrees `(i, n)` lands in `ℳ_{i + n}` and a right action in
degrees `(n, i)` lands in `ℳ_{n + i}`. Addition of integers is not definitionally commutative, so
the reading transports every value along `i + n = n + i`; `pieceCast` is that transport, the
identity function presented through `cast`, so that it disappears on a reflexivity proof.

Commutativity of `𝒜` is what makes the flip legitimate, and it is used: the associativity law of
a right graded module compares the two bracketings of `x · a · b` with `a` of degree `i` and `b`
of degree `j`, while the law of a left graded module compares `b · (a · x)` with `(b a) · x`, so
the two products `a b` and `b a` have to be identified. That is the `mul_comm` field of
Situation 01NN, which `situationAlgebra` forgets but which is available on `𝒜` itself.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.pieceCast`: transport of a homogeneous local
  section of `ℳ` along an equality of degrees.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.situationModule`: **Situation 01NN's graded
  `𝒜`-module, read as a right graded module over `situationAlgebra 𝒜` in the sense of Tag
  0FQZ.** This is the form the sheaf of Tag 01O6 and the assertions of Tag 01O7 quantify over.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.situationModule_piece`: the homogeneous pieces
  are unchanged.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.situationModule_smul_app`: the right action is
  the left action with its factors exchanged and its degree transported.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.isQuasicoherent_situationModule_piece`: every
  homogeneous piece of the reading is quasi-coherent, which is what makes a morphism out of its
  pullback over an affine base recoverable from a linear map on global sections.

## Implementation notes

`pieceCast` is defined by `cast` along `congrArg`, not as an `eqToHom` of the category of
`𝒪_S`-modules, for one reason: `cast` on a reflexivity proof reduces to the identity by iota, so
every law below is proved by `subst` on the equality of degrees followed by `rfl`. The five laws
of `SheafOfModules.GradedModule` are then each one `HEq.trans` or one `Eq.trans` away from the
corresponding law of `SheafGradedModule`.

Three of the five laws are heterogeneous equalities, which is what makes the transport invisible
in them: `pieceCast_heq` says the transport of a section is heterogeneously equal to the section,
so it may simply be dropped. The two homogeneous laws — linearity in each variable — are instead
discharged by `pieceCast_smul`, the transport being `Γ(S, U)`-linear.

## References

* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 0FQZ](https://stacks.math.columbia.edu/tag/0FQZ)
* [Stacks Project, Tag 01O6](https://stacks.math.columbia.edu/tag/01O6)
* [Stacks Project, Tag 01O7](https://stacks.math.columbia.edu/tag/01O7)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProjBridge

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

variable {S : Scheme.{u}} {A : SheafGradedAlgebra S}

/-- **Transport of a homogeneous local section along an equality of degrees.** It is the identity
function, presented through `cast` so that a reflexivity proof makes it reduce away. -/
def pieceCast (M : SheafGradedModule A) {i j : ℤ} (h : i = j) (U : S.Opens) :
    Γ(M.piece i, U) →+ Γ(M.piece j, U) :=
  cast (congrArg (fun k => Γ(M.piece i, U) →+ Γ(M.piece k, U)) h) (AddMonoidHom.id _)

/-- The transport of a section is heterogeneously equal to the section. -/
theorem pieceCast_heq (M : SheafGradedModule A) {i j : ℤ} (h : i = j) (U : S.Opens)
    (x : Γ(M.piece i, U)) : HEq (pieceCast M h U x) x := by
  subst h; rfl

/-- The transport is `Γ(S, U)`-linear. -/
theorem pieceCast_smul (M : SheafGradedModule A) {i j : ℤ} (h : i = j) (U : S.Opens)
    (r : Γ(S, U)) (x : Γ(M.piece i, U)) :
    pieceCast M h U (r • x) = r • pieceCast M h U x := by
  subst h; rfl

/-- The transport commutes with restriction. -/
theorem pieceCast_naturality (M : SheafGradedModule A) {i j : ℤ} (h : i = j)
    {U V : S.Opens} (hUV : U ≤ V) (x : Γ(M.piece i, V)) :
    (M.piece j).presheaf.map (homOfLE hUV).op (pieceCast M h V x)
      = pieceCast M h U ((M.piece i).presheaf.map (homOfLE hUV).op x) := by
  subst h; rfl

/-- The left action is unchanged by transporting its second argument along an equality of
degrees. -/
theorem smul_pieceCast_heq (M : SheafGradedModule A) (k : ℤ) {p q : ℤ} (h : p = q)
    (U : S.Opens) (z : Γ(A.piece k, U)) (x : Γ(M.piece p, U)) :
    HEq ((M.smul k q).app U z (pieceCast M h U x)) ((M.smul k p).app U z x) := by
  subst h; rfl

/-- The left action of two heterogeneously equal homogeneous scalars agrees. -/
theorem smul_congr_heq (M : SheafGradedModule A) {p q : ℤ} (hpq : p = q) (n : ℤ)
    (U : S.Opens) {b : Γ(A.piece p, U)} {b' : Γ(A.piece q, U)} (hb : HEq b b')
    (x : Γ(M.piece n, U)) :
    HEq ((M.smul p n).app U b x) ((M.smul q n).app U b' x) := by
  subst hpq
  rw [eq_of_heq hb]

/-- **Situation 01NN's graded `𝒜`-module, read as a right graded module over
`situationAlgebra 𝒜`** in the sense of Tag 0FQZ: the same homogeneous pieces, with the left
action of the homogeneous pieces of `𝒜` read as a right action by exchanging the two factors and
transporting the degree along `i + n = n + i`.

This is the module-side mirror of
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.situationAlgebra`, and it is the form in which
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartDegreewiseFamily` feeds the module to the
sheaf `ℳ̃_T` of Tag 01O6; the comparison of property (1) of Tag 01O7 built in
`StacksFrontier/AlgebraicGeometry/RelativeProjQuadrupleTilde/` reads a graded module of
`Stacks.RelativeProj.Situation` through `SheafOfModules.LeftGradedModule.toGradedModule` instead.
Quasi-coherence of the pieces
and their vanishing in low degrees are forgotten, as they are on the algebra side; the
commutativity of `𝒜` is used in the associativity law and is not recorded in the result. -/
def situationModule (M : SheafGradedModule A) :
    SheafOfModules.GradedModule.{u, u, u} (situationAlgebra A) where
  piece := M.piece
  smul n i U :=
    AddMonoidHom.compr₂ ((M.smul i n).app U.unop).flip
      (pieceCast M (Int.add_comm i n) U.unop)
  smul_smul_left n i U r x y :=
    (congrArg (pieceCast M (Int.add_comm i n) U.unop)
        ((M.smul i n).map_smul_right U.unop r y x)).trans
      (pieceCast_smul M (Int.add_comm i n) U.unop r _)
  smul_smul_right n i U r x y :=
    (congrArg (pieceCast M (Int.add_comm i n) U.unop)
        ((M.smul i n).map_smul_left U.unop r y x)).trans
      (pieceCast_smul M (Int.add_comm i n) U.unop r _)
  smul_naturality := fun n i {_U _V} f x y =>
    (pieceCast_naturality M (Int.add_comm i n) (leOfHom f.unop) _).trans
      (congrArg (pieceCast M (Int.add_comm i n) _)
        ((M.smul i n).naturality (leOfHom f.unop) y x))
  smul_mul n i j U x y z :=
    HEq.trans (pieceCast_heq M (Int.add_comm j (n + i)) U.unop _)
      (HEq.trans (smul_pieceCast_heq M j (Int.add_comm i n) U.unop z _)
        (HEq.symm (HEq.trans (pieceCast_heq M (Int.add_comm (i + j) n) U.unop _)
          (HEq.trans
            (smul_congr_heq M (Int.add_comm i j) n U.unop (A.mul_comm i j U.unop y z) x)
            (M.mul_smul j i n U.unop z y x)))))
  smul_one n U x :=
    HEq.trans (pieceCast_heq M (Int.add_comm 0 n) U.unop _) (M.one_smul n U.unop x)

/-- The homogeneous pieces of the reading are the homogeneous pieces of the module. -/
@[simp]
theorem situationModule_piece (M : SheafGradedModule A) (n : ℤ) :
    (situationModule M).piece n = M.piece n := rfl

/-- **The right action of the reading is the left action with its factors exchanged**, its value
transported along `i + n = n + i`. -/
theorem situationModule_smul_app (M : SheafGradedModule A) (n i : ℤ) (U : S.Opens)
    (x : Γ(M.piece n, U)) (y : Γ(A.piece i, U)) :
    (situationModule M).smul n i (op U) x y
      = pieceCast M (Int.add_comm i n) U ((M.smul i n).app U y x) := rfl

/-- Transport of a scalar multiple of a homogeneous local section along an equality of
degrees. -/
theorem heq_smul (M : SheafGradedModule A) (U : S.Opens) {p q : ℤ} (h : p = q) (r : Γ(S, U))
    {z : M.sectionModulePieces U p} {y : M.sectionModulePieces U q} (hzy : HEq z y) :
    HEq (r • z) (r • y) := by
  subst h
  rw [eq_of_heq hzy]

/-- **The degree-`0` scalar of a function multiplies a homogeneous section of the module by
acting on it**: the structure map of the graded ring of sections carries `r` to an element of the
section ring whose action on the degree-`k` summand is the action of `r` on homogeneous sections.

This is the module mirror of
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.coe_ofGrading_smul`, and it is
what turns the `Γ(S, 𝒪_S)`-module structure on the homogeneous sections of `ℳ` into an action of
the degree-zero part of the graded ring of sections of `𝒜` — the form in which the linearity of
the canonical map to shifted global sections on `Proj` is stated. -/
theorem strHom_smul_of (M : SheafGradedModule A) (U : S.Opens) {k : ℤ} (r : Γ(S, U))
    (x : M.sectionModulePieces U k) :
    A.strHom U r • DirectSum.of (M.sectionModulePieces U) k x
      = DirectSum.of (M.sectionModulePieces U) k (r • x) := by
  have h1 : A.strHom U r • DirectSum.of (M.sectionModulePieces U) k x
      = DirectSum.of (M.sectionModulePieces U) (((0 : ℕ) : ℤ) + k)
        ((M.smul ((0 : ℕ) : ℤ) k).app U (r • A.one U) x) :=
    M.of_smul_of U (i := 0) (r • A.one U) x
  have h2 : (M.smul ((0 : ℕ) : ℤ) k).app U (r • A.one U) x
      = r • (M.smul ((0 : ℕ) : ℤ) k).app U (A.one U) x :=
    (M.smul ((0 : ℕ) : ℤ) k).map_smul_left U r (A.one U) x
  have h3 : HEq ((M.smul ((0 : ℕ) : ℤ) k).app U (A.one U) x) x := M.one_smul k U x
  refine h1.trans ?_
  rw [h2]
  exact DirectSum.of_eq_of_gradedMonoid_eq
    (Sigma.ext (Int.zero_add k) (heq_smul M U (Int.zero_add k) r h3))

/-- **Every homogeneous piece of the reading is quasi-coherent.** This is the `isQuasicoherent`
field of a `SheafGradedModule`, which the reading forgets; it is what makes a morphism out of the
pullback of a piece over an affine base recoverable from a `Γ(S, 𝒪_S)`-linear map on global
sections, by `Stacks.AlgebraicGeometry.AffineHomRecovery.homEquiv`. -/
theorem isQuasicoherent_situationModule_piece (M : SheafGradedModule A) (n : ℤ) :
    ((situationModule M).piece n).IsQuasicoherent :=
  M.isQuasicoherent n

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
