module

public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.ProjF1Dehomogenization.UnitAlgebra
public import StacksFrontier.AlgebraicGeometry.RelativeProjGradedIdeal.NonnegTruncationMul
public import StacksFrontier.AlgebraicGeometry.RelativeProjMapDomain.Hom
public import StacksFrontier.AlgebraicGeometry.TotalDirectImage.DerivedUpperBound

/-!
# The tail truncation `𝒪_S ⊕ ⨁_{n ≥ d₀} A_n` of a sheaf of graded algebras

Let `S` be a scheme and `A` a sheaf of `ℤ`-graded `𝒪_S`-algebras. This file constructs, at an
arbitrary positive cut `d₀`, the **tail truncation**

`𝒪_S ⊕ ⨁_{n ≥ d₀} A_n`

as a quasi-coherent, commutative, nonnegatively graded `𝒪_S`-algebra — a
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra S`, which is what the relative
`Proj` of Situation [Stacks, Tag 01NN] consumes — together with its comparison homomorphism into
the nonnegative truncation `A_{≥ 0}` of the same `A`, which is an isomorphism in every degree
`≥ d₀`.

That is the shape of the algebra `𝒜' = 𝒪_{S'} ⊕ ⨁_{d ≥ d₀} 𝒜'_d` of [Stacks, Tag 0D4F] (3), and
the comparison is the map the source's clauses (4) and (5) are proved through: applied to
`A = ⨁_{n ∈ ℤ} (f')_* (ℒ')^{⊗ n}`, the nonnegative truncation is
`Stacks.RelativeAmple.directImageAlgebra` and the comparison feeds [Stacks, Tag 07ZJ].

## Main definitions

* `Stacks.AlgebraicGeometry.SectionAlgebra.unitActionBilinear`: the action of `𝒪_S` on a sheaf of
  modules, read as an `𝒪_S`-bilinear map out of the free sheaf of rank one.
* `Stacks.AlgebraicGeometry.SectionAlgebra.tailPiece`, `…tailMul`, `…tailOne`: the pieces, the
  multiplication and the unit of the tail truncation.
* `Stacks.AlgebraicGeometry.SectionAlgebra.tailTruncation`: **`𝒪_S ⊕ ⨁_{n ≥ d₀} A_n` as a
  `SheafOfModules.GradedAlgebra S.ringCatSheaf`**, and `…tailSheafGradedAlgebra` the same as
  sheaf-level graded algebra data on `S`.
* `Stacks.AlgebraicGeometry.SectionAlgebra.tailComparison`: **the comparison
  `𝒪_S ⊕ ⨁_{n ≥ d₀} A_n ⟶ A_{≥ 0}`**, as a
  `Stacks.AlgebraicGeometry.RelativeProjMapDomain.SheafGradedAlgebraHom`.

## Main results

* `…tailMul_assoc`, `…tailMul_one_mul`, `…tailMul_mul_one`, `…tailMul_comm`: the laws of the tail
  truncation.
* `…vanishesInNegativeDegrees_tailTruncation` and `…isQuasicoherent_tailPiece`: the two further
  requirements of Situation [Stacks, Tag 01NN], the first with no hypothesis on `A`.
* `…tailComp_mul` and `…tailComp_one`: the comparison is multiplicative and unital.
* `…isIso_tailCompApp`: **the comparison is an isomorphism in every degree `≥ d₀`.**

## Implementation notes

**Why the tail truncation costs what `NonnegTruncation` did not.** The implementation notes of
`StacksFrontier/AlgebraicGeometry/RelativeProjGradedIdeal/NonnegTruncation.lean` explain why its cut
is at `0` and its pieces are defined by a match on the constructors of `ℤ`: writing them as
`if 0 ≤ n then A.piece n else 0` would make the *type* of a local section depend on a proof,
while matching makes `(↑a + ↑b : ℤ)` reduce to `↑(a + b)`, so that every law in the nonnegative
branch is literally the corresponding law of `A` and no transport appears anywhere. At a
**variable** cut nothing reduces: `tailPiece A d₀ n` is `A.piece n` only propositionally, by
`tailPiece_eq_piece`, so `tailMul` carries a transport in each of its three arguments and the
laws become identities between nested transports. `HEq` is insensitive to a transport —
`heq_eqToHom_app_of_eq` — which is why the laws of a `SheafOfModules.GradedAlgebra` being `HEq`
costs nothing here; what the transports do cost is the four bookkeeping lemmas of the section
"Transport bookkeeping for the laws" and one extra `eqToHom` at every use.

`tailMul` is assembled from `Stacks.BilinearMap.compLeft`, `compRight` and `postcomp`, so its
bilinearity and naturality are free: only the four bilinear maps themselves have to be named, and
they are `ProjF1Dehomogenization.unitMul` in the degree-zero corner, `unitActionBilinear` in the
degree-zero row and column, `A.mul` when both degrees are `≥ d₀` — their sum is then `≥ d₀`
again, which is why the cut must be positive — and
`Stacks.AlgebraicGeometry.NonnegTruncation.zeroBilinear` in every remaining bidegree.

**Why associativity is eight declarations.** Heartbeats are spent per declaration, and the eight
substantive branches of `tailMul_assoc` are independent; with all of them in one proof the later
ones died of a timeout that reads like a unification blowup. Splitting them gives each its own
budget. For the same reason every degree side-condition is written `show <prop> by omega` rather
than as a bare `by omega`: an explicit type stops the elaborator re-unifying the two spellings of
a piece at every step. The nine branches of `tailComp_mul` are split for the same reason.

**The comparison, and why its multiplicativity is a homogeneous equality.** `tailComparison`
compares the tail truncation at `d₀` with the nonnegative truncation of the same `A`: the two
differ only in the band `0 < n < d₀`, where the first is a zero object. Its degreewise component
is the unit map `𝒪_S ⟶ A_0` of `A` — `SheafOfModules.unitHomEquiv.symm A.one`, whose value on a
local section `x` is `x • 1_A` — in degree zero, a transport in a degree `≥ d₀`, and the zero
morphism in between. Unlike the laws of the truncation itself, multiplicativity equates two
sections of the *same* piece, so it is a genuine equality; but its two sides carry the transports
of both truncations, and the cheapest route is to prove the `HEq` with the bookkeeping lemmas
already in place and then apply `eq_of_heq`. The transports on the nonnegative side are stripped
by `Stacks.AlgebraicGeometry.NonnegTruncation.heq_mul_app_of_nonneg`, whose proof settles both
`Int` constructors and is then `rfl`.

**`heq_eqToHom_app_of_eq` is a restatement, deliberately.**
`Stacks.TensorSheafWorld.heq_eqToHom_val_app` says the same thing for two members of *one*
`ℤ`-indexed family and
`Stacks.AlgebraicGeometry.DifferentialGradedAxiomB.sheaf_eqToHom_apply_heq` for the sheaves of
modules of a ringed site. Neither applies here: the transports of a truncation are between the
pieces of *two different* families, the truncation and the algebra it truncates.

## References

* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 07ZJ](https://stacks.math.columbia.edu/tag/07ZJ)
* [Stacks Project, Tag 0D4F](https://stacks.math.columbia.edu/tag/0D4F)

## Not done here

No Stacks tag is claimed; the tail truncation at a variable cut is not the subject of one.

`tailComparison` is a homomorphism of graded algebras, an isomorphism in the degrees `≥ d₀`
(`isIso_tailCompApp`), and nothing more: its degree-zero component is not shown to be a
monomorphism, and no kernel or cokernel of any component is identified. None of that is needed by
`PolarizedFamily.AdmissibleDeformation.IsTruncatedSectionAlgebra` of
`StacksFrontier/AlgebraicGeometry/ProjectiveDeformation/Basic.lean`, which is what it was built for.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.SheafSymmetricAlgebra
open scoped ZeroObject

universe u

namespace Stacks.AlgebraicGeometry.SectionAlgebra

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

/-! ### The tail truncation of a sheaf of graded algebras -/

variable {S : Scheme.{u}}

/-! ### The action of the structure sheaf, as a bilinear map -/

/-- **The action of `𝒪_S` on a sheaf of modules, read as an `𝒪_S`-bilinear map out of the free
sheaf of rank one.**  Biadditivity is `add_smul` and `smul_add`, linearity in the first variable
is `mul_smul`, linearity in the second needs the product of the structure sheaf to commute, and
naturality is the semilinearity of the restriction maps of a presheaf of modules.

This is the multiplication of the degree-zero row and column of a graded algebra whose
degree-zero piece is the structure sheaf; the degree-zero *corner* is
`Stacks.AlgebraicGeometry.ProjF1Dehomogenization.unitMul`. -/
def unitActionBilinear (M : SheafOfModules.{u} S.ringCatSheaf) :
    SheafOfModules.BilinearMap (SheafOfModules.unit S.ringCatSheaf) M M where
  app U := AddMonoidHom.mk'
    (fun x => AddMonoidHom.mk' (fun y => ProjF1Dehomogenization.ofUnit _ x • y)
      (fun y z => smul_add _ y z))
    (fun x z => AddMonoidHom.ext fun y => add_smul _ _ y)
  map_smul_left U r x y := mul_smul r (ProjF1Dehomogenization.ofUnit _ x) y
  map_smul_right U r x y := by
    change ProjF1Dehomogenization.ofUnit _ x • (r • y)
      = r • (ProjF1Dehomogenization.ofUnit _ x • y)
    rw [← mul_smul, ← mul_smul,
      ProjF1Dehomogenization.isCommutativeRingSheaf_scheme S U
        (ProjF1Dehomogenization.ofUnit _ x) r]
  naturality {U V} f x y := PresheafOfModules.map_smul M.val f _ y

/-- On sections over `U`, the unit action sends `x` and `y` to `x • y`, with `x` read in the
structure sheaf. -/
theorem unitActionBilinear_app (M : SheafOfModules.{u} S.ringCatSheaf) (U : (S.Opens)ᵒᵖ)
    (x : (SheafOfModules.unit S.ringCatSheaf).val.obj U) (y : M.val.obj U) :
    (unitActionBilinear M).app U x y = ProjF1Dehomogenization.ofUnit _ x • y :=
  rfl

/-! ### Two transport facts -/

/-- **A local section transported along an equality of sheaves of modules is heterogeneously
equal to itself.**  `Stacks.TensorSheafWorld.heq_eqToHom_val_app` says this for two members of
one `ℤ`-indexed family and
`Stacks.AlgebraicGeometry.DifferentialGradedAxiomB.sheaf_eqToHom_apply_heq` for the sheaves of
modules of a ringed site; it is restated here for two arbitrary sheaves of modules over the
structure sheaf of a scheme, which is the spelling the truncation below transports in — its
transports are between the pieces of *two different* families, the truncation and the algebra it
truncates, so neither of those two forms applies. -/
theorem heq_eqToHom_app_of_eq {M N : SheafOfModules.{u} S.ringCatSheaf} (h : M = N)
    (U : (S.Opens)ᵒᵖ) (x : M.val.obj U) : HEq ((eqToHom h).val.app U x) x := by
  cases h
  rfl

/-- Transport cancels its own inverse, on local sections. -/
theorem eqToHom_app_eqToHom_app {M N : SheafOfModules.{u} S.ringCatSheaf} (h : M = N)
    (h' : N = M) (U : (S.Opens)ᵒᵖ) (x : M.val.obj U) :
    (eqToHom h').val.app U ((eqToHom h).val.app U x) = x := by
  cases h
  rfl

/-- **The scalar action respects a heterogeneous equality of local sections.** -/
theorem heq_smul_of_heq {M N : SheafOfModules.{u} S.ringCatSheaf} (h : M = N)
    {U : (S.Opens)ᵒᵖ} {x : M.val.obj U} {y : N.val.obj U} (hxy : HEq x y)
    (r : S.ringCatSheaf.obj.obj U) : HEq (r • x) (r • y) := by
  cases h
  rw [eq_of_heq hxy]

/-- Two zero local sections of sheaves of modules known to be equal are heterogeneously equal.
This is the shape every degenerate branch of the laws below takes; the two sides live in the
pieces of degrees that agree only propositionally. -/
theorem heq_of_eq_zero_of_eq {M N : SheafOfModules.{u} S.ringCatSheaf} (h : M = N)
    {U : (S.Opens)ᵒᵖ} {x : M.val.obj U} {y : N.val.obj U} (hx : x = 0) (hy : y = 0) :
    HEq x y := by
  cases h
  exact heq_of_eq (hx.trans hy.symm)

/-! ### The tail truncation `𝒪_S ⊕ ⨁_{n ≥ d₀} A_n` -/

section Tail

variable (A : SheafOfModules.GradedAlgebra.{u, u} S.ringCatSheaf) (d₀ : ℕ)

/-- **The homogeneous pieces of the tail truncation `𝒪_S ⊕ ⨁_{n ≥ d₀} A_n`**: the structure
sheaf in degree zero, the pieces of `A` in degrees `≥ d₀`, and zero objects elsewhere.

Unlike `Stacks.AlgebraicGeometry.NonnegTruncation.piece`, whose cut is at `0` and which
therefore matches on the constructors of `ℤ`, the cut here is at a *variable* `d₀`; nothing
reduces, and the price is the transports recorded in the implementation notes. -/
def tailPiece (n : ℤ) : SheafOfModules.{u} S.ringCatSheaf :=
  if n = 0 then SheafOfModules.unit S.ringCatSheaf
  else if (d₀ : ℤ) ≤ n then A.piece n else (0 : S.Modules)

/-- In degree zero the truncation is the structure sheaf. -/
theorem tailPiece_eq_unit {n : ℤ} (h : n = 0) :
    tailPiece A d₀ n = SheafOfModules.unit S.ringCatSheaf := by
  subst h
  exact ite_eq_left rfl

/-- In a degree `≥ d₀` the truncation is `A`, the cut being positive. -/
theorem tailPiece_eq_piece (hd : 0 < d₀) {n : ℤ} (hn : (d₀ : ℤ) ≤ n) :
    tailPiece A d₀ n = A.piece n := by
  have h0 : ¬ n = 0 := by omega
  unfold tailPiece
  rw [ite_eq_right h0, ite_eq_left hn]

/-- Outside `{0} ∪ [d₀, ∞)` the truncation is a zero object. -/
theorem tailPiece_eq_zero {n : ℤ} (h0 : n ≠ 0) (hn : ¬ (d₀ : ℤ) ≤ n) :
    tailPiece A d₀ n = (0 : S.Modules) := by
  unfold tailPiece
  rw [ite_eq_right h0, ite_eq_right hn]

/-- **Every local section of a piece outside `{0} ∪ [d₀, ∞)` vanishes.** -/
theorem eq_zero_of_tailPiece {n : ℤ} (h0 : n ≠ 0) (hn : ¬ (d₀ : ℤ) ≤ n) (U : (S.Opens)ᵒᵖ)
    (x : (tailPiece A d₀ n).val.obj U) : x = 0 := by
  have hz0 : IsZero (C := S.Modules) (0 : S.Modules) := isZero_zero _
  refine NonnegTruncation.eq_zero_of_isZero (M := tailPiece A d₀ n) ?_ U x
  rw [tailPiece_eq_zero A d₀ h0 hn]
  exact hz0

/-- The piece in a degree `≥ d₀` is isomorphic to the piece of `A`, which is the equality
`tailPiece_eq_piece` read as a transport. -/
theorem heq_tail_app (hd : 0 < d₀) {n : ℤ} (hn : (d₀ : ℤ) ≤ n) (U : (S.Opens)ᵒᵖ)
    (x : (tailPiece A d₀ n).val.obj U) :
    HEq ((eqToHom (tailPiece_eq_piece A d₀ hd hn)).val.app U x) x :=
  heq_eqToHom_app_of_eq _ U x

/-- The degree-zero piece is the structure sheaf, read as a transport. -/
theorem heq_unit_app {n : ℤ} (h : n = 0) (U : (S.Opens)ᵒᵖ)
    (x : (tailPiece A d₀ n).val.obj U) :
    HEq ((eqToHom (tailPiece_eq_unit A d₀ h)).val.app U x) x :=
  heq_eqToHom_app_of_eq _ U x

/-! #### The multiplication -/

/-- **The multiplication of the tail truncation.**  In the degree-zero corner it is the product
of the structure sheaf (`ProjF1Dehomogenization.unitMul`); in the degree-zero row and column it
is the action of the structure sheaf on a piece of `A` (`unitActionBilinear`); when both degrees
are `≥ d₀` it is the multiplication of `A`, the sum of two such degrees being `≥ d₀` again; and
in every remaining bidegree it is the zero bilinear map. -/
def tailMul (hd : 0 < d₀) (i j : ℤ) :
    SheafOfModules.BilinearMap (tailPiece A d₀ i) (tailPiece A d₀ j) (tailPiece A d₀ (i + j)) :=
  if hi : i = 0 then
    if hj : j = 0 then
      (((ProjF1Dehomogenization.unitMul S.ringCatSheaf
            (ProjF1Dehomogenization.isCommutativeRingSheaf_scheme S)).compLeft
          (eqToHom (tailPiece_eq_unit A d₀ hi)).val).compRight
        (eqToHom (tailPiece_eq_unit A d₀ hj)).val).postcomp
      (eqToHom (tailPiece_eq_unit A d₀ (by omega : i + j = 0)).symm).val
    else if hjt : (d₀ : ℤ) ≤ j then
      (((unitActionBilinear (A.piece j)).compLeft
          (eqToHom (tailPiece_eq_unit A d₀ hi)).val).compRight
        (eqToHom (tailPiece_eq_piece A d₀ hd hjt)).val).postcomp
      (eqToHom ((congrArg A.piece (by omega : j = i + j)).trans
        (tailPiece_eq_piece A d₀ hd (by omega : (d₀ : ℤ) ≤ i + j)).symm)).val
    else
      NonnegTruncation.zeroBilinear _ _ _
  else if hit : (d₀ : ℤ) ≤ i then
    if hj : j = 0 then
      ((((unitActionBilinear (A.piece i)).flip).compLeft
          (eqToHom (tailPiece_eq_piece A d₀ hd hit)).val).compRight
        (eqToHom (tailPiece_eq_unit A d₀ hj)).val).postcomp
      (eqToHom ((congrArg A.piece (by omega : i = i + j)).trans
        (tailPiece_eq_piece A d₀ hd (by omega : (d₀ : ℤ) ≤ i + j)).symm)).val
    else if hjt : (d₀ : ℤ) ≤ j then
      (((A.mul i j).compLeft
          (eqToHom (tailPiece_eq_piece A d₀ hd hit)).val).compRight
        (eqToHom (tailPiece_eq_piece A d₀ hd hjt)).val).postcomp
      (eqToHom (tailPiece_eq_piece A d₀ hd (by omega : (d₀ : ℤ) ≤ i + j)).symm).val
    else
      NonnegTruncation.zeroBilinear _ _ _
  else
    NonnegTruncation.zeroBilinear _ _ _

variable (hd : 0 < d₀)

/-- The product of two degree-zero sections is their product in the structure sheaf. -/
theorem tailMul_app_zz {i j : ℤ} (hi : i = 0) (hj : j = 0) (hij : i + j = 0)
    (U : (S.Opens)ᵒᵖ) (x : (tailPiece A d₀ i).val.obj U) (y : (tailPiece A d₀ j).val.obj U) :
    (tailMul A d₀ hd i j).app U x y =
      (eqToHom (tailPiece_eq_unit A d₀ hij).symm).val.app U
        ((ProjF1Dehomogenization.unitMul S.ringCatSheaf
            (ProjF1Dehomogenization.isCommutativeRingSheaf_scheme S)).app U
          ((eqToHom (tailPiece_eq_unit A d₀ hi)).val.app U x)
          ((eqToHom (tailPiece_eq_unit A d₀ hj)).val.app U y)) := by
  unfold tailMul
  rw [dite_eq_left hi, dite_eq_left hj]
  rfl

/-- A degree-zero section acts on a tail section by the action of the structure sheaf. -/
theorem tailMul_app_zt {i j : ℤ} (hi : i = 0) (hj : ¬ j = 0) (hjt : (d₀ : ℤ) ≤ j)
    (hji : j = i + j) (hijt : (d₀ : ℤ) ≤ i + j)
    (U : (S.Opens)ᵒᵖ) (x : (tailPiece A d₀ i).val.obj U) (y : (tailPiece A d₀ j).val.obj U) :
    (tailMul A d₀ hd i j).app U x y =
      (eqToHom ((congrArg A.piece hji).trans
          (tailPiece_eq_piece A d₀ hd hijt).symm)).val.app U
        (ProjF1Dehomogenization.ofUnit _ ((eqToHom (tailPiece_eq_unit A d₀ hi)).val.app U x) •
          (eqToHom (tailPiece_eq_piece A d₀ hd hjt)).val.app U y) := by
  unfold tailMul
  rw [dite_eq_left hi, dite_eq_right hj, dite_eq_left hjt]
  rfl

/-- A tail section is acted on by a degree-zero section on the right by the same action. -/
theorem tailMul_app_tz {i j : ℤ} (hi : ¬ i = 0) (hit : (d₀ : ℤ) ≤ i) (hj : j = 0)
    (hij : i = i + j) (hijt : (d₀ : ℤ) ≤ i + j)
    (U : (S.Opens)ᵒᵖ) (x : (tailPiece A d₀ i).val.obj U) (y : (tailPiece A d₀ j).val.obj U) :
    (tailMul A d₀ hd i j).app U x y =
      (eqToHom ((congrArg A.piece hij).trans
          (tailPiece_eq_piece A d₀ hd hijt).symm)).val.app U
        (ProjF1Dehomogenization.ofUnit _ ((eqToHom (tailPiece_eq_unit A d₀ hj)).val.app U y) •
          (eqToHom (tailPiece_eq_piece A d₀ hd hit)).val.app U x) := by
  unfold tailMul
  rw [dite_eq_right hi, dite_eq_left hit, dite_eq_left hj]
  rfl

/-- The product of two tail sections is their product in `A`. -/
theorem tailMul_app_tt {i j : ℤ} (hi : ¬ i = 0) (hit : (d₀ : ℤ) ≤ i) (hj : ¬ j = 0)
    (hjt : (d₀ : ℤ) ≤ j) (hijt : (d₀ : ℤ) ≤ i + j)
    (U : (S.Opens)ᵒᵖ) (x : (tailPiece A d₀ i).val.obj U) (y : (tailPiece A d₀ j).val.obj U) :
    (tailMul A d₀ hd i j).app U x y =
      (eqToHom (tailPiece_eq_piece A d₀ hd hijt).symm).val.app U
        ((A.mul i j).app U ((eqToHom (tailPiece_eq_piece A d₀ hd hit)).val.app U x)
          ((eqToHom (tailPiece_eq_piece A d₀ hd hjt)).val.app U y)) := by
  unfold tailMul
  rw [dite_eq_right hi, dite_eq_left hit, dite_eq_right hj, dite_eq_left hjt]
  rfl

/-- A product whose left degree is outside `{0} ∪ [d₀, ∞)` vanishes. -/
theorem tailMul_app_eq_zero_left {i j : ℤ} (hi : ¬ i = 0) (hit : ¬ (d₀ : ℤ) ≤ i)
    (U : (S.Opens)ᵒᵖ) (x : (tailPiece A d₀ i).val.obj U) (y : (tailPiece A d₀ j).val.obj U) :
    (tailMul A d₀ hd i j).app U x y = 0 := by
  unfold tailMul
  rw [dite_eq_right hi, dite_eq_right hit]
  rfl

/-- A product whose right degree is outside `{0} ∪ [d₀, ∞)` vanishes, the left degree being
zero. -/
theorem tailMul_app_eq_zero_right_zero {i j : ℤ} (hi : i = 0) (hj : ¬ j = 0)
    (hjt : ¬ (d₀ : ℤ) ≤ j)
    (U : (S.Opens)ᵒᵖ) (x : (tailPiece A d₀ i).val.obj U) (y : (tailPiece A d₀ j).val.obj U) :
    (tailMul A d₀ hd i j).app U x y = 0 := by
  unfold tailMul
  rw [dite_eq_left hi, dite_eq_right hj, dite_eq_right hjt]
  rfl

/-- A product whose right degree is outside `{0} ∪ [d₀, ∞)` vanishes, the left degree being in
the tail. -/
theorem tailMul_app_eq_zero_right_tail {i j : ℤ} (hi : ¬ i = 0) (hit : (d₀ : ℤ) ≤ i)
    (hj : ¬ j = 0) (hjt : ¬ (d₀ : ℤ) ≤ j)
    (U : (S.Opens)ᵒᵖ) (x : (tailPiece A d₀ i).val.obj U) (y : (tailPiece A d₀ j).val.obj U) :
    (tailMul A d₀ hd i j).app U x y = 0 := by
  unfold tailMul
  rw [dite_eq_right hi, dite_eq_left hit, dite_eq_right hj, dite_eq_right hjt]
  rfl

/-- A product one of whose degrees is outside `{0} ∪ [d₀, ∞)` vanishes. -/
theorem tailMul_app_eq_zero {i j : ℤ}
    (h : (i ≠ 0 ∧ ¬ (d₀ : ℤ) ≤ i) ∨ (j ≠ 0 ∧ ¬ (d₀ : ℤ) ≤ j))
    (U : (S.Opens)ᵒᵖ) (x : (tailPiece A d₀ i).val.obj U) (y : (tailPiece A d₀ j).val.obj U) :
    (tailMul A d₀ hd i j).app U x y = 0 := by
  rcases h with ⟨hi, hit⟩ | ⟨hj, hjt⟩
  · exact tailMul_app_eq_zero_left A d₀ hd hi hit U x y
  · by_cases hi : i = 0
    · exact tailMul_app_eq_zero_right_zero A d₀ hd hi hj hjt U x y
    · by_cases hit : (d₀ : ℤ) ≤ i
      · exact tailMul_app_eq_zero_right_tail A d₀ hd hi hit hj hjt U x y
      · exact tailMul_app_eq_zero_left A d₀ hd hi hit U x y

/-- A product with a vanishing left factor vanishes. -/
theorem tailMul_app_zero_left {i j : ℤ} (U : (S.Opens)ᵒᵖ)
    {x : (tailPiece A d₀ i).val.obj U} (hx : x = 0) (y : (tailPiece A d₀ j).val.obj U) :
    (tailMul A d₀ hd i j).app U x y = 0 := by
  rw [hx, map_zero, AddMonoidHom.zero_apply]

/-- A product with a vanishing right factor vanishes. -/
theorem tailMul_app_zero_right {i j : ℤ} (U : (S.Opens)ᵒᵖ)
    (x : (tailPiece A d₀ i).val.obj U) {y : (tailPiece A d₀ j).val.obj U} (hy : y = 0) :
    (tailMul A d₀ hd i j).app U x y = 0 := by
  rw [hy, map_zero]

/-! #### Transport bookkeeping for the laws -/

/-- Two transported local sections are heterogeneously equal as soon as their arguments are.
This strips the transports that `tailMul` carries from both sides of a law. -/
theorem heq_eqToHom_app_congr {M N M' N' : SheafOfModules.{u} S.ringCatSheaf} (h : M = N)
    (h' : M' = N') (U : (S.Opens)ᵒᵖ) (a : M.val.obj U) (b : M'.val.obj U) (hab : HEq a b) :
    HEq ((eqToHom h).val.app U a) ((eqToHom h').val.app U b) := by
  cases h
  cases h'
  exact hab

/-- Two successive transports leave a local section heterogeneously unchanged. -/
theorem heq_eqToHom_app_two {M N P : SheafOfModules.{u} S.ringCatSheaf} (h : M = N) (h' : N = P)
    (U : (S.Opens)ᵒᵖ) (x : M.val.obj U) :
    HEq ((eqToHom h').val.app U ((eqToHom h).val.app U x)) x :=
  (heq_eqToHom_app_of_eq h' U _).trans (heq_eqToHom_app_of_eq h U x)

/-- Multiplication in `A` respects a heterogeneous equality in the left variable across an
equality of degrees. -/
theorem heq_mul_app_left {i i' j : ℤ} (h : i = i') (U : (S.Opens)ᵒᵖ)
    {x : (A.piece i).val.obj U} {x' : (A.piece i').val.obj U} (hx : HEq x x')
    (y : (A.piece j).val.obj U) :
    HEq ((A.mul i j).app U x y) ((A.mul i' j).app U x' y) := by
  subst h
  rw [eq_of_heq hx]

/-- Multiplication in `A` respects a heterogeneous equality in the right variable across an
equality of degrees. -/
theorem heq_mul_app_right {i j j' : ℤ} (h : j = j') (U : (S.Opens)ᵒᵖ)
    (x : (A.piece i).val.obj U) {y : (A.piece j).val.obj U} {y' : (A.piece j').val.obj U}
    (hy : HEq y y') :
    HEq ((A.mul i j).app U x y) ((A.mul i j').app U x y') := by
  subst h
  rw [eq_of_heq hy]

/-! #### Associativity -/

/-- Both sides of associativity vanish as soon as one of the three degrees lies outside
`{0} ∪ [d₀, ∞)`. -/
theorem heq_tailMul_assoc_of_eq_zero (i j k : ℤ) (U : (S.Opens)ᵒᵖ)
    (x : (tailPiece A d₀ i).val.obj U) (y : (tailPiece A d₀ j).val.obj U)
    (z : (tailPiece A d₀ k).val.obj U)
    (h : (i ≠ 0 ∧ ¬ (d₀ : ℤ) ≤ i) ∨ (j ≠ 0 ∧ ¬ (d₀ : ℤ) ≤ j) ∨ (k ≠ 0 ∧ ¬ (d₀ : ℤ) ≤ k)) :
    HEq ((tailMul A d₀ hd (i + j) k).app U ((tailMul A d₀ hd i j).app U x y) z)
      ((tailMul A d₀ hd i (j + k)).app U x ((tailMul A d₀ hd j k).app U y z)) := by
  refine heq_of_eq_zero_of_eq (congrArg (tailPiece A d₀) (add_assoc i j k)) ?_ ?_
  · rcases h with hh | hh | hh
    · exact tailMul_app_zero_left A d₀ hd U
        (tailMul_app_eq_zero A d₀ hd (Or.inl hh) U x y) z
    · exact tailMul_app_zero_left A d₀ hd U
        (tailMul_app_eq_zero A d₀ hd (Or.inr hh) U x y) z
    · exact tailMul_app_eq_zero A d₀ hd (Or.inr hh) U _ z
  · rcases h with hh | hh | hh
    · exact tailMul_app_eq_zero A d₀ hd (Or.inl hh) U x _
    · exact tailMul_app_zero_right A d₀ hd U x
        (tailMul_app_eq_zero A d₀ hd (Or.inl hh) U y z)
    · exact tailMul_app_zero_right A d₀ hd U x
        (tailMul_app_eq_zero A d₀ hd (Or.inr hh) U y z)

/-! #### The eight substantive branches of associativity

Each is stated separately: the eight proofs are independent, and keeping them in one
declaration spends one heartbeat budget on all of them at once. -/

/-- `(0, 0, 0)`: associativity of the product of the structure sheaf. -/
theorem heq_tailMul_assoc_zzz {i j k : ℤ} (hi : i = 0) (hj : j = 0) (hk : k = 0) (U : (S.Opens)ᵒᵖ)
    (x : (tailPiece A d₀ i).val.obj U) (y : (tailPiece A d₀ j).val.obj U)
    (z : (tailPiece A d₀ k).val.obj U) :
    HEq ((tailMul A d₀ hd (i + j) k).app U ((tailMul A d₀ hd i j).app U x y) z)
      ((tailMul A d₀ hd i (j + k)).app U x ((tailMul A d₀ hd j k).app U y z)) := by
  rw [tailMul_app_zz A d₀ hd hi hj (show i + j = 0 by omega) U x y,
    tailMul_app_zz A d₀ hd (show i + j = 0 by omega) hk
      (show i + j + k = 0 by omega) U _ z,
    tailMul_app_zz A d₀ hd hj hk (show j + k = 0 by omega) U y z,
    tailMul_app_zz A d₀ hd hi (show j + k = 0 by omega)
      (show i + (j + k) = 0 by omega) U x _,
    eqToHom_app_eqToHom_app, eqToHom_app_eqToHom_app]
  exact heq_eqToHom_app_congr _ _ U _ _
    (heq_of_eq (mul_assoc (ProjF1Dehomogenization.ofUnit _ _)
      (ProjF1Dehomogenization.ofUnit _ _) (ProjF1Dehomogenization.ofUnit _ _)))

/-- `(0, 0, tail)`: `(a * b) • s = a • (b • s)`. -/
theorem heq_tailMul_assoc_zzt {i j k : ℤ} (hi : i = 0) (hj : j = 0) (hk : ¬ k = 0)
    (hkt : (d₀ : ℤ) ≤ k) (U : (S.Opens)ᵒᵖ)
    (x : (tailPiece A d₀ i).val.obj U) (y : (tailPiece A d₀ j).val.obj U)
    (z : (tailPiece A d₀ k).val.obj U) :
    HEq ((tailMul A d₀ hd (i + j) k).app U ((tailMul A d₀ hd i j).app U x y) z)
      ((tailMul A d₀ hd i (j + k)).app U x ((tailMul A d₀ hd j k).app U y z)) := by
  rw [tailMul_app_zz A d₀ hd hi hj (show i + j = 0 by omega) U x y,
    tailMul_app_zt A d₀ hd (show i + j = 0 by omega) hk hkt
      (show k = i + j + k by omega) (show (d₀ : ℤ) ≤ i + j + k by omega) U _ z,
    tailMul_app_zt A d₀ hd hj hk hkt (show k = j + k by omega)
      (show (d₀ : ℤ) ≤ j + k by omega) U y z,
    tailMul_app_zt A d₀ hd hi (show ¬ j + k = 0 by omega)
      (show (d₀ : ℤ) ≤ j + k by omega) (show j + k = i + (j + k) by omega)
      (show (d₀ : ℤ) ≤ i + (j + k) by omega) U x _,
    eqToHom_app_eqToHom_app, ProjF1Dehomogenization.ofUnit_unitMul_app]
  refine heq_eqToHom_app_congr _ _ U _ _ ?_
  refine (heq_of_eq (mul_smul _ _ _)).trans
    (heq_smul_of_heq (congrArg A.piece (show k = j + k by omega)) ?_ _)
  exact (heq_eqToHom_app_two _ _ U _).symm

/-- `(0, tail, 0)`: the two scalars commute. -/
theorem heq_tailMul_assoc_ztz {i j k : ℤ} (hi : i = 0) (hj : ¬ j = 0) (hjt : (d₀ : ℤ) ≤ j)
    (hk : k = 0) (U : (S.Opens)ᵒᵖ)
    (x : (tailPiece A d₀ i).val.obj U) (y : (tailPiece A d₀ j).val.obj U)
    (z : (tailPiece A d₀ k).val.obj U) :
    HEq ((tailMul A d₀ hd (i + j) k).app U ((tailMul A d₀ hd i j).app U x y) z)
      ((tailMul A d₀ hd i (j + k)).app U x ((tailMul A d₀ hd j k).app U y z)) := by
  rw [tailMul_app_zt A d₀ hd hi hj hjt (show j = i + j by omega)
      (show (d₀ : ℤ) ≤ i + j by omega) U x y,
    tailMul_app_tz A d₀ hd (show ¬ i + j = 0 by omega)
      (show (d₀ : ℤ) ≤ i + j by omega) hk (show i + j = i + j + k by omega)
      (show (d₀ : ℤ) ≤ i + j + k by omega) U _ z,
    tailMul_app_tz A d₀ hd hj hjt hk (show j = j + k by omega)
      (show (d₀ : ℤ) ≤ j + k by omega) U y z,
    tailMul_app_zt A d₀ hd hi (show ¬ j + k = 0 by omega)
      (show (d₀ : ℤ) ≤ j + k by omega) (show j + k = i + (j + k) by omega)
      (show (d₀ : ℤ) ≤ i + (j + k) by omega) U x _]
  refine heq_eqToHom_app_congr _ _ U _ _ ?_
  refine (heq_smul_of_heq (congrArg A.piece (show i + j = j by omega))
    (heq_eqToHom_app_two _ _ U _) _).trans ?_
  refine (heq_of_eq ?_).trans
    (heq_smul_of_heq (congrArg A.piece (show j = j + k by omega))
      (heq_eqToHom_app_two _ _ U _).symm _)
  rw [← mul_smul, ← mul_smul,
    ProjF1Dehomogenization.isCommutativeRingSheaf_scheme S U _ _]

/-- `(0, tail, tail)`: linearity of the multiplication of `A` in the left variable. -/
theorem heq_tailMul_assoc_ztt {i j k : ℤ} (hi : i = 0) (hj : ¬ j = 0) (hjt : (d₀ : ℤ) ≤ j)
    (hk : ¬ k = 0) (hkt : (d₀ : ℤ) ≤ k) (U : (S.Opens)ᵒᵖ)
    (x : (tailPiece A d₀ i).val.obj U) (y : (tailPiece A d₀ j).val.obj U)
    (z : (tailPiece A d₀ k).val.obj U) :
    HEq ((tailMul A d₀ hd (i + j) k).app U ((tailMul A d₀ hd i j).app U x y) z)
      ((tailMul A d₀ hd i (j + k)).app U x ((tailMul A d₀ hd j k).app U y z)) := by
  rw [tailMul_app_zt A d₀ hd hi hj hjt (show j = i + j by omega)
      (show (d₀ : ℤ) ≤ i + j by omega) U x y,
    tailMul_app_tt A d₀ hd (show ¬ i + j = 0 by omega)
      (show (d₀ : ℤ) ≤ i + j by omega) hk hkt
      (show (d₀ : ℤ) ≤ i + j + k by omega) U _ z,
    tailMul_app_tt A d₀ hd hj hjt hk hkt (show (d₀ : ℤ) ≤ j + k by omega) U y z,
    tailMul_app_zt A d₀ hd hi (show ¬ j + k = 0 by omega)
      (show (d₀ : ℤ) ≤ j + k by omega) (show j + k = i + (j + k) by omega)
      (show (d₀ : ℤ) ≤ i + (j + k) by omega) U x _,
    eqToHom_app_eqToHom_app]
  refine heq_eqToHom_app_congr _ _ U _ _ ?_
  exact (heq_mul_app_left A (show i + j = j by omega) U
      (heq_eqToHom_app_two _ _ U _) _).trans
    (heq_of_eq ((A.mul j k).map_smul_left U _ _ _))

/-- `(tail, 0, 0)`: the two scalars commute again. -/
theorem heq_tailMul_assoc_tzz {i j k : ℤ} (hi : ¬ i = 0) (hit : (d₀ : ℤ) ≤ i) (hj : j = 0)
    (hk : k = 0) (U : (S.Opens)ᵒᵖ)
    (x : (tailPiece A d₀ i).val.obj U) (y : (tailPiece A d₀ j).val.obj U)
    (z : (tailPiece A d₀ k).val.obj U) :
    HEq ((tailMul A d₀ hd (i + j) k).app U ((tailMul A d₀ hd i j).app U x y) z)
      ((tailMul A d₀ hd i (j + k)).app U x ((tailMul A d₀ hd j k).app U y z)) := by
  rw [tailMul_app_tz A d₀ hd hi hit hj (show i = i + j by omega)
      (show (d₀ : ℤ) ≤ i + j by omega) U x y,
    tailMul_app_tz A d₀ hd (show ¬ i + j = 0 by omega)
      (show (d₀ : ℤ) ≤ i + j by omega) hk (show i + j = i + j + k by omega)
      (show (d₀ : ℤ) ≤ i + j + k by omega) U _ z,
    tailMul_app_zz A d₀ hd hj hk (show j + k = 0 by omega) U y z,
    tailMul_app_tz A d₀ hd hi hit (show j + k = 0 by omega)
      (show i = i + (j + k) by omega) (show (d₀ : ℤ) ≤ i + (j + k) by omega) U x _,
    eqToHom_app_eqToHom_app, ProjF1Dehomogenization.ofUnit_unitMul_app]
  refine heq_eqToHom_app_congr _ _ U _ _ ?_
  refine (heq_smul_of_heq (congrArg A.piece (show i + j = i by omega))
    (heq_eqToHom_app_two _ _ U _) _).trans (heq_of_eq ?_)
  rw [← mul_smul, ProjF1Dehomogenization.isCommutativeRingSheaf_scheme S U _ _]

/-- `(tail, 0, tail)`: the two linearity laws of the multiplication of `A`. -/
theorem heq_tailMul_assoc_tzt {i j k : ℤ} (hi : ¬ i = 0) (hit : (d₀ : ℤ) ≤ i) (hj : j = 0)
    (hk : ¬ k = 0) (hkt : (d₀ : ℤ) ≤ k) (U : (S.Opens)ᵒᵖ)
    (x : (tailPiece A d₀ i).val.obj U) (y : (tailPiece A d₀ j).val.obj U)
    (z : (tailPiece A d₀ k).val.obj U) :
    HEq ((tailMul A d₀ hd (i + j) k).app U ((tailMul A d₀ hd i j).app U x y) z)
      ((tailMul A d₀ hd i (j + k)).app U x ((tailMul A d₀ hd j k).app U y z)) := by
  rw [tailMul_app_tz A d₀ hd hi hit hj (show i = i + j by omega)
      (show (d₀ : ℤ) ≤ i + j by omega) U x y,
    tailMul_app_tt A d₀ hd (show ¬ i + j = 0 by omega)
      (show (d₀ : ℤ) ≤ i + j by omega) hk hkt
      (show (d₀ : ℤ) ≤ i + j + k by omega) U _ z,
    tailMul_app_zt A d₀ hd hj hk hkt (show k = j + k by omega)
      (show (d₀ : ℤ) ≤ j + k by omega) U y z,
    tailMul_app_tt A d₀ hd hi hit (show ¬ j + k = 0 by omega)
      (show (d₀ : ℤ) ≤ j + k by omega)
      (show (d₀ : ℤ) ≤ i + (j + k) by omega) U x _]
  refine heq_eqToHom_app_congr _ _ U _ _ ?_
  refine (heq_mul_app_left A (show i + j = i by omega) U
    (heq_eqToHom_app_two _ _ U _) _).trans ?_
  refine (heq_of_eq ((A.mul i k).map_smul_left U _ _ _)).trans ?_
  refine HEq.trans ?_ (heq_mul_app_right A (show k = j + k by omega) U _
    (heq_eqToHom_app_two _ _ U _).symm)
  exact heq_of_eq ((A.mul i k).map_smul_right U _ _ _).symm

/-- `(tail, tail, 0)`: linearity of the multiplication of `A` in the right variable. -/
theorem heq_tailMul_assoc_ttz {i j k : ℤ} (hi : ¬ i = 0) (hit : (d₀ : ℤ) ≤ i) (hj : ¬ j = 0)
    (hjt : (d₀ : ℤ) ≤ j) (hk : k = 0) (U : (S.Opens)ᵒᵖ)
    (x : (tailPiece A d₀ i).val.obj U) (y : (tailPiece A d₀ j).val.obj U)
    (z : (tailPiece A d₀ k).val.obj U) :
    HEq ((tailMul A d₀ hd (i + j) k).app U ((tailMul A d₀ hd i j).app U x y) z)
      ((tailMul A d₀ hd i (j + k)).app U x ((tailMul A d₀ hd j k).app U y z)) := by
  rw [tailMul_app_tt A d₀ hd hi hit hj hjt (show (d₀ : ℤ) ≤ i + j by omega) U x y,
    tailMul_app_tz A d₀ hd (show ¬ i + j = 0 by omega)
      (show (d₀ : ℤ) ≤ i + j by omega) hk (show i + j = i + j + k by omega)
      (show (d₀ : ℤ) ≤ i + j + k by omega) U _ z,
    tailMul_app_tz A d₀ hd hj hjt hk (show j = j + k by omega)
      (show (d₀ : ℤ) ≤ j + k by omega) U y z,
    tailMul_app_tt A d₀ hd hi hit (show ¬ j + k = 0 by omega)
      (show (d₀ : ℤ) ≤ j + k by omega)
      (show (d₀ : ℤ) ≤ i + (j + k) by omega) U x _,
    eqToHom_app_eqToHom_app]
  refine heq_eqToHom_app_congr _ _ U _ _ ?_
  exact (heq_of_eq ((A.mul i j).map_smul_right U _ _ _).symm).trans
    (heq_mul_app_right A (show j = j + k by omega) U _
      (heq_eqToHom_app_two _ _ U _).symm)

/-- `(tail, tail, tail)`: associativity of `A`. -/
theorem heq_tailMul_assoc_ttt {i j k : ℤ} (hi : ¬ i = 0) (hit : (d₀ : ℤ) ≤ i) (hj : ¬ j = 0)
    (hjt : (d₀ : ℤ) ≤ j) (hk : ¬ k = 0) (hkt : (d₀ : ℤ) ≤ k) (U : (S.Opens)ᵒᵖ)
    (x : (tailPiece A d₀ i).val.obj U) (y : (tailPiece A d₀ j).val.obj U)
    (z : (tailPiece A d₀ k).val.obj U) :
    HEq ((tailMul A d₀ hd (i + j) k).app U ((tailMul A d₀ hd i j).app U x y) z)
      ((tailMul A d₀ hd i (j + k)).app U x ((tailMul A d₀ hd j k).app U y z)) := by
  rw [tailMul_app_tt A d₀ hd hi hit hj hjt (show (d₀ : ℤ) ≤ i + j by omega) U x y,
    tailMul_app_tt A d₀ hd (show ¬ i + j = 0 by omega)
      (show (d₀ : ℤ) ≤ i + j by omega) hk hkt
      (show (d₀ : ℤ) ≤ i + j + k by omega) U _ z,
    tailMul_app_tt A d₀ hd hj hjt hk hkt (show (d₀ : ℤ) ≤ j + k by omega) U y z,
    tailMul_app_tt A d₀ hd hi hit (show ¬ j + k = 0 by omega)
      (show (d₀ : ℤ) ≤ j + k by omega)
      (show (d₀ : ℤ) ≤ i + (j + k) by omega) U x _,
    eqToHom_app_eqToHom_app, eqToHom_app_eqToHom_app]
  exact heq_eqToHom_app_congr _ _ U _ _ (A.mul_assoc i j k U _ _ _)

/-- **Associativity of the tail truncation.**  Eight of the twenty-seven branches are
substantive — those in which each of the three degrees is either `0` or `≥ d₀` — and each is one
of: associativity of the product of the structure sheaf, a scalar-action identity, one of the two
linearity laws of the multiplication of `A`, or the associativity of `A` itself.  In the
remaining nineteen a factor lies in a zero piece and both sides vanish. -/
theorem tailMul_assoc (i j k : ℤ) (U : (S.Opens)ᵒᵖ) (x : (tailPiece A d₀ i).val.obj U)
    (y : (tailPiece A d₀ j).val.obj U) (z : (tailPiece A d₀ k).val.obj U) :
    HEq ((tailMul A d₀ hd (i + j) k).app U ((tailMul A d₀ hd i j).app U x y) z)
      ((tailMul A d₀ hd i (j + k)).app U x ((tailMul A d₀ hd j k).app U y z)) := by
  by_cases h : (i ≠ 0 ∧ ¬ (d₀ : ℤ) ≤ i) ∨ (j ≠ 0 ∧ ¬ (d₀ : ℤ) ≤ j) ∨ (k ≠ 0 ∧ ¬ (d₀ : ℤ) ≤ k)
  · exact heq_tailMul_assoc_of_eq_zero A d₀ hd i j k U x y z h
  by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> by_cases hk : k = 0
  · exact heq_tailMul_assoc_zzz A d₀ hd hi hj hk U x y z
  · exact heq_tailMul_assoc_zzt A d₀ hd hi hj hk (by omega) U x y z
  · exact heq_tailMul_assoc_ztz A d₀ hd hi hj (by omega) hk U x y z
  · exact heq_tailMul_assoc_ztt A d₀ hd hi hj (by omega) hk (by omega) U x y z
  · exact heq_tailMul_assoc_tzz A d₀ hd hi (by omega) hj hk U x y z
  · exact heq_tailMul_assoc_tzt A d₀ hd hi (by omega) hj hk (by omega) U x y z
  · exact heq_tailMul_assoc_ttz A d₀ hd hi (by omega) hj (by omega) hk U x y z
  · exact heq_tailMul_assoc_ttt A d₀ hd hi (by omega) hj (by omega) hk (by omega) U x y z

/-! #### The unit, and the unit and commutativity laws -/

/-- **The unit of the tail truncation**: the unit section of the structure sheaf, read in the
degree-zero piece. -/
def tailOne : (tailPiece A d₀ 0).sections :=
  SheafOfModules.sectionsMap (eqToHom (tailPiece_eq_unit A d₀ rfl).symm)
    (ProjF1Dehomogenization.unitSections S.ringCatSheaf)

/-- The section of `tailOne` over `U` is the unit section of the structure sheaf over `U`,
transported to the degree-zero piece. -/
theorem tailOne_eval (U : (S.Opens)ᵒᵖ) :
    (tailOne A d₀).eval U =
      (eqToHom (tailPiece_eq_unit A d₀ rfl).symm).val.app U
        ((ProjF1Dehomogenization.unitSections S.ringCatSheaf).eval U) :=
  rfl

/-- **The unit is a left identity.** -/
theorem tailMul_one_mul (i : ℤ) (U : (S.Opens)ᵒᵖ) (x : (tailPiece A d₀ i).val.obj U) :
    HEq ((tailMul A d₀ hd 0 i).app U ((tailOne A d₀).eval U) x) x := by
  by_cases hi : i = 0
  · rw [tailOne_eval, tailMul_app_zz A d₀ hd rfl hi (show (0 : ℤ) + i = 0 by omega) U _ x,
      eqToHom_app_eqToHom_app]
    refine (heq_eqToHom_app_of_eq _ U _).trans ?_
    exact (heq_of_eq (_root_.one_mul (ProjF1Dehomogenization.ofUnit _
      ((eqToHom (tailPiece_eq_unit A d₀ hi)).val.app U x)))).trans
      (heq_eqToHom_app_of_eq _ U x)
  · by_cases hit : (d₀ : ℤ) ≤ i
    · rw [tailOne_eval, tailMul_app_zt A d₀ hd rfl hi hit (show i = 0 + i by omega)
        (show (d₀ : ℤ) ≤ 0 + i by omega) U _ x, eqToHom_app_eqToHom_app]
      refine (heq_eqToHom_app_of_eq _ U _).trans ?_
      exact (heq_of_eq (one_smul _ _)).trans (heq_eqToHom_app_of_eq _ U x)
    · exact heq_of_eq_zero_of_eq (congrArg (tailPiece A d₀) (zero_add i))
        (tailMul_app_eq_zero A d₀ hd (Or.inr ⟨hi, hit⟩) U _ x)
        (eq_zero_of_tailPiece A d₀ hi hit U x)

/-- **The unit is a right identity.** -/
theorem tailMul_mul_one (i : ℤ) (U : (S.Opens)ᵒᵖ) (x : (tailPiece A d₀ i).val.obj U) :
    HEq ((tailMul A d₀ hd i 0).app U x ((tailOne A d₀).eval U)) x := by
  by_cases hi : i = 0
  · rw [tailOne_eval, tailMul_app_zz A d₀ hd hi rfl (show i + (0 : ℤ) = 0 by omega) U x _,
      eqToHom_app_eqToHom_app]
    refine (heq_eqToHom_app_of_eq _ U _).trans ?_
    exact (heq_of_eq (_root_.mul_one (ProjF1Dehomogenization.ofUnit _
      ((eqToHom (tailPiece_eq_unit A d₀ hi)).val.app U x)))).trans
      (heq_eqToHom_app_of_eq _ U x)
  · by_cases hit : (d₀ : ℤ) ≤ i
    · rw [tailOne_eval, tailMul_app_tz A d₀ hd hi hit rfl (show i = i + 0 by omega)
        (show (d₀ : ℤ) ≤ i + 0 by omega) U x _, eqToHom_app_eqToHom_app]
      refine (heq_eqToHom_app_of_eq _ U _).trans ?_
      exact (heq_of_eq (one_smul _ _)).trans (heq_eqToHom_app_of_eq _ U x)
    · exact heq_of_eq_zero_of_eq (congrArg (tailPiece A d₀) (add_zero i))
        (tailMul_app_eq_zero A d₀ hd (Or.inl ⟨hi, hit⟩) U x _)
        (eq_zero_of_tailPiece A d₀ hi hit U x)

/-- **The multiplication of the tail truncation commutes**, given that the multiplication of `A`
does.  In the degree-zero corner this is commutativity of the structure sheaf; in the degree-zero
row and column the two products are the *same* scalar action and the law is reflexivity; when
both degrees are `≥ d₀` it is the hypothesis. -/
theorem tailMul_comm (hcomm : IsCommutative A) (i j : ℤ) (U : (S.Opens)ᵒᵖ)
    (a : (tailPiece A d₀ i).val.obj U) (b : (tailPiece A d₀ j).val.obj U) :
    HEq ((tailMul A d₀ hd i j).app U a b) ((tailMul A d₀ hd j i).app U b a) := by
  by_cases h : (i ≠ 0 ∧ ¬ (d₀ : ℤ) ≤ i) ∨ (j ≠ 0 ∧ ¬ (d₀ : ℤ) ≤ j)
  · exact heq_of_eq_zero_of_eq (congrArg (tailPiece A d₀) (add_comm i j))
      (tailMul_app_eq_zero A d₀ hd h U a b) (tailMul_app_eq_zero A d₀ hd h.symm U b a)
  by_cases hi : i = 0 <;> by_cases hj : j = 0
  · rw [tailMul_app_zz A d₀ hd hi hj (show i + j = 0 by omega) U a b,
      tailMul_app_zz A d₀ hd hj hi (show j + i = 0 by omega) U b a]
    exact heq_eqToHom_app_congr _ _ U _ _
      (heq_of_eq (ProjF1Dehomogenization.isCommutativeRingSheaf_scheme S U _ _))
  · rw [tailMul_app_zt A d₀ hd hi hj (by omega) (show j = i + j by omega)
        (show (d₀ : ℤ) ≤ i + j by omega) U a b,
      tailMul_app_tz A d₀ hd hj (by omega) hi (show j = j + i by omega)
        (show (d₀ : ℤ) ≤ j + i by omega) U b a]
    exact heq_eqToHom_app_congr _ _ U _ _ HEq.rfl
  · rw [tailMul_app_tz A d₀ hd hi (by omega) hj (show i = i + j by omega)
        (show (d₀ : ℤ) ≤ i + j by omega) U a b,
      tailMul_app_zt A d₀ hd hj hi (by omega) (show i = j + i by omega)
        (show (d₀ : ℤ) ≤ j + i by omega) U b a]
    exact heq_eqToHom_app_congr _ _ U _ _ HEq.rfl
  · rw [tailMul_app_tt A d₀ hd hi (by omega) hj (by omega) (show (d₀ : ℤ) ≤ i + j by omega) U a b,
      tailMul_app_tt A d₀ hd hj (by omega) hi (by omega) (show (d₀ : ℤ) ≤ j + i by omega) U b a]
    exact heq_eqToHom_app_congr _ _ U _ _ (hcomm i j U _ _)

/-! #### The tail truncation as a sheaf of graded algebras -/

/-- **The tail truncation `𝒪_S ⊕ ⨁_{n ≥ d₀} A_n` of a sheaf of graded algebras**, at a positive
cut `d₀`. -/
def tailTruncation : SheafOfModules.GradedAlgebra.{u, u} S.ringCatSheaf where
  piece := tailPiece A d₀
  mul := tailMul A d₀ hd
  one := tailOne A d₀
  mul_assoc := tailMul_assoc A d₀ hd
  one_mul := tailMul_one_mul A d₀ hd
  mul_one := tailMul_mul_one A d₀ hd

/-- The degree-`n` piece of the tail truncation is `tailPiece A d₀ n`. -/
theorem tailTruncation_piece (n : ℤ) : (tailTruncation A d₀ hd).piece n = tailPiece A d₀ n := rfl

/-- **Commutativity is inherited by the tail truncation.** -/
theorem isCommutative_tailTruncation (hcomm : IsCommutative A) :
    IsCommutative (tailTruncation A d₀ hd) :=
  tailMul_comm A d₀ hd hcomm

/-- **The tail truncation is concentrated in nonnegative degrees**, with no hypothesis on `A`:
a negative degree is neither `0` nor `≥ d₀`. -/
theorem vanishesInNegativeDegrees_tailTruncation :
    VanishesInNegativeDegrees (tailTruncation A d₀ hd) :=
  fun n hn U x => eq_zero_of_tailPiece A d₀ (by omega) (by omega) U x

/-- **Every piece of the tail truncation is quasi-coherent** as soon as every piece of `A` is:
the degree-zero piece is the structure sheaf, the tail pieces are those of `A`, and the rest are
zero objects. -/
theorem isQuasicoherent_tailPiece (hqc : ∀ n : ℤ, ((A.piece n : S.Modules)).IsQuasicoherent)
    (n : ℤ) : (((tailTruncation A d₀ hd).piece n : S.Modules)).IsQuasicoherent := by
  change (((tailPiece A d₀ n) : S.Modules)).IsQuasicoherent
  by_cases h0 : n = 0
  · rw [tailPiece_eq_unit A d₀ h0]
    exact Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit S
  · by_cases hnt : (d₀ : ℤ) ≤ n
    · rw [tailPiece_eq_piece A d₀ hd hnt]
      exact hqc n
    · rw [tailPiece_eq_zero A d₀ h0 hnt]
      exact _root_.AlgebraicGeometry.isQuasicoherent_zero S

/-- **The tail truncation as sheaf-level graded algebra data on `S`**, the input of the relative
`Proj` construction of Situation [Stacks, Tag 01NN]. -/
def tailSheafGradedAlgebra (hcomm : IsCommutative A)
    (hqc : ∀ n : ℤ, ((A.piece n : S.Modules)).IsQuasicoherent) :
    SheafGradedAlgebra S :=
  toSheafGradedAlgebra (tailTruncation A d₀ hd) (isCommutative_tailTruncation A d₀ hd hcomm)
    (vanishesInNegativeDegrees_tailTruncation A d₀ hd) (isQuasicoherent_tailPiece A d₀ hd hqc)

/-- The degree-`n` piece of `tailSheafGradedAlgebra` is `tailPiece A d₀ n`. -/
theorem tailSheafGradedAlgebra_piece (hcomm : IsCommutative A)
    (hqc : ∀ n : ℤ, ((A.piece n : S.Modules)).IsQuasicoherent) (n : ℤ) :
    (tailSheafGradedAlgebra A d₀ hd hcomm hqc).piece n = tailPiece A d₀ n :=
  rfl

/-! #### Multiples of the unit of `A` -/

/-- **A multiple of the unit of `A` multiplies on the left by acting.**  In bidegree `(0, j)` the
product of `a · 1_A` with a section of `A_j` is `a` acting on that section; the two sides live in
the degree-`0 + j` and degree-`j` pieces, which agree only propositionally. -/
theorem heq_mul_one_smul {j : ℤ} (U : (S.Opens)ᵒᵖ) (a : S.ringCatSheaf.obj.obj U)
    (b : (A.piece j).val.obj U) :
    HEq ((A.mul 0 j).app U (a • A.one.eval U) b) (a • b) := by
  rw [(A.mul 0 j).map_smul_left]
  exact heq_smul_of_heq (congrArg A.piece (show (0 : ℤ) + j = j by omega)) (A.one_mul j U b) a

/-- **A multiple of the unit of `A` multiplies on the right by acting.** -/
theorem heq_mul_smul_one {i : ℤ} (U : (S.Opens)ᵒᵖ) (a : S.ringCatSheaf.obj.obj U)
    (b : (A.piece i).val.obj U) :
    HEq ((A.mul i 0).app U b (a • A.one.eval U)) (a • b) := by
  rw [(A.mul i 0).map_smul_right]
  exact heq_smul_of_heq (congrArg A.piece (show i + (0 : ℤ) = i by omega)) (A.mul_one i U b) a

/-! #### The comparison into the nonnegative truncation

`tailPiece A d₀` and `Stacks.AlgebraicGeometry.NonnegTruncation.piece A` differ only in the band
`0 < n < d₀`, where the first is a zero object and the second is `A.piece n`.  Outside it the two
are compared degreewise: in degree zero the structure sheaf maps to `A_0` by the unit map of `A`,
and in a degree `≥ d₀` the two pieces are equal.  That degreewise morphism is multiplicative, so
it is a homomorphism of sheaf-level graded algebras, and it is an isomorphism in every degree
`≥ d₀`. -/

/-- **The comparison morphism `𝒪_S ⊕ ⨁_{n ≥ d₀} A_n ⟶ A_{≥0}` in each degree**: the unit map
`𝒪_S ⟶ A_0` of `A` in degree zero, the transport `tailPiece_eq_piece` in a degree `≥ d₀`, and
the zero morphism in between, where the source is a zero object. -/
def tailCompApp (n : ℤ) : tailPiece A d₀ n ⟶ NonnegTruncation.piece A n :=
  if hn : n = 0 then
    eqToHom (tailPiece_eq_unit A d₀ hn) ≫ (A.piece 0).unitHomEquiv.symm A.one ≫
      eqToHom (congrArg (NonnegTruncation.piece A) hn.symm)
  else if hnt : (d₀ : ℤ) ≤ n then
    eqToHom ((tailPiece_eq_piece A d₀ hd hnt).trans
      (NonnegTruncation.piece_of_nonneg A (show (0 : ℤ) ≤ n by omega)).symm)
  else 0

/-- In degree zero the comparison sends a section of the structure sheaf to its multiple of the
unit of `A`. -/
theorem tailCompApp_app_zero {n : ℤ} (hn : n = 0) (U : (S.Opens)ᵒᵖ)
    (x : (tailPiece A d₀ n).val.obj U) :
    (tailCompApp A d₀ hd n).val.app U x =
      (eqToHom (congrArg (NonnegTruncation.piece A) hn.symm)).val.app U
        (ProjF1Dehomogenization.ofUnit _
          ((eqToHom (tailPiece_eq_unit A d₀ hn)).val.app U x) • A.one.eval U) := by
  unfold tailCompApp
  rw [dite_eq_left hn]
  rfl

/-- In a degree `≥ d₀` the comparison is the transport of `tailPiece_eq_piece`. -/
theorem tailCompApp_eq_eqToHom {n : ℤ} (hn : ¬ n = 0) (hnt : (d₀ : ℤ) ≤ n)
    (hn0 : (0 : ℤ) ≤ n) :
    tailCompApp A d₀ hd n =
      eqToHom ((tailPiece_eq_piece A d₀ hd hnt).trans
        (NonnegTruncation.piece_of_nonneg A hn0).symm) := by
  unfold tailCompApp
  rw [dite_eq_right hn, dite_eq_left hnt]

/-- In a degree `≥ d₀` the comparison is the transport of `tailPiece_eq_piece`, on sections. -/
theorem tailCompApp_app_tail {n : ℤ} (hn : ¬ n = 0) (hnt : (d₀ : ℤ) ≤ n) (hn0 : (0 : ℤ) ≤ n)
    (U : (S.Opens)ᵒᵖ) (x : (tailPiece A d₀ n).val.obj U) :
    (tailCompApp A d₀ hd n).val.app U x =
      (eqToHom ((tailPiece_eq_piece A d₀ hd hnt).trans
        (NonnegTruncation.piece_of_nonneg A hn0).symm)).val.app U x := by
  rw [tailCompApp_eq_eqToHom A d₀ hd hn hnt hn0]

/-- **The comparison is an isomorphism in every degree `≥ d₀`**, being a transport there. -/
theorem isIso_tailCompApp {n : ℤ} (hn : ¬ n = 0) (hnt : (d₀ : ℤ) ≤ n) (hn0 : (0 : ℤ) ≤ n) :
    IsIso (tailCompApp A d₀ hd n) := by
  rw [tailCompApp_eq_eqToHom A d₀ hd hn hnt hn0]
  infer_instance

/-- Outside `{0} ∪ [d₀, ∞)` the comparison kills every local section, the source being a zero
object. -/
theorem tailCompApp_app_eq_zero {n : ℤ} (hn : ¬ n = 0) (hnt : ¬ (d₀ : ℤ) ≤ n)
    (U : (S.Opens)ᵒᵖ) (x : (tailPiece A d₀ n).val.obj U) :
    (tailCompApp A d₀ hd n).val.app U x = 0 := by
  rw [eq_zero_of_tailPiece A d₀ hn hnt U x]
  exact map_zero _

/-! ##### The nine branches of multiplicativity

Each is stated separately, for the reason the eight branches of `tailMul_assoc` are: the proofs
are independent, and one declaration would spend a single heartbeat budget on all of them. -/

/-- `(0, 0)`: the unit map is multiplicative, by the unit law of `A` and its two linearity
laws. -/
theorem tailComp_mul_zz {i j : ℤ} (hi : i = 0) (hj : j = 0) (U : (S.Opens)ᵒᵖ)
    (x : (tailPiece A d₀ i).val.obj U) (y : (tailPiece A d₀ j).val.obj U) :
    (tailCompApp A d₀ hd (i + j)).val.app U ((tailMul A d₀ hd i j).app U x y) =
      (NonnegTruncation.mul A i j).app U ((tailCompApp A d₀ hd i).val.app U x)
        ((tailCompApp A d₀ hd j).val.app U y) := by
  rw [tailMul_app_zz A d₀ hd hi hj (show i + j = 0 by omega) U x y,
    tailCompApp_app_zero A d₀ hd (show i + j = 0 by omega) U,
    eqToHom_app_eqToHom_app, ProjF1Dehomogenization.ofUnit_unitMul_app,
    tailCompApp_app_zero A d₀ hd hi U x, tailCompApp_app_zero A d₀ hd hj U y]
  refine eq_of_heq (HEq.trans ?_ (NonnegTruncation.heq_mul_app_of_nonneg A
    (show (0 : ℤ) ≤ i by omega) (show (0 : ℤ) ≤ j by omega) U _ _).symm)
  exact (((heq_eqToHom_app_of_eq _ U _).trans (heq_of_eq (mul_smul _ _ _))).trans
      (heq_mul_one_smul A U _ _).symm).trans
    ((heq_mul_app_left A hi U (heq_eqToHom_app_two _ _ U _) _).trans
      (heq_mul_app_right A hj U _ (heq_eqToHom_app_two _ _ U _))).symm

/-- `(0, tail)`: a degree-zero section acts, and the action is the product with its multiple of
the unit. -/
theorem tailComp_mul_zt {i j : ℤ} (hi : i = 0) (hj : ¬ j = 0) (hjt : (d₀ : ℤ) ≤ j)
    (U : (S.Opens)ᵒᵖ) (x : (tailPiece A d₀ i).val.obj U) (y : (tailPiece A d₀ j).val.obj U) :
    (tailCompApp A d₀ hd (i + j)).val.app U ((tailMul A d₀ hd i j).app U x y) =
      (NonnegTruncation.mul A i j).app U ((tailCompApp A d₀ hd i).val.app U x)
        ((tailCompApp A d₀ hd j).val.app U y) := by
  rw [tailMul_app_zt A d₀ hd hi hj hjt (show j = i + j by omega)
      (show (d₀ : ℤ) ≤ i + j by omega) U x y,
    tailCompApp_app_tail A d₀ hd (show ¬ i + j = 0 by omega)
      (show (d₀ : ℤ) ≤ i + j by omega) (show (0 : ℤ) ≤ i + j by omega) U,
    tailCompApp_app_zero A d₀ hd hi U x,
    tailCompApp_app_tail A d₀ hd hj hjt (show (0 : ℤ) ≤ j by omega) U y]
  refine eq_of_heq (HEq.trans ?_ (NonnegTruncation.heq_mul_app_of_nonneg A
    (show (0 : ℤ) ≤ i by omega) (show (0 : ℤ) ≤ j by omega) U _ _).symm)
  exact ((heq_eqToHom_app_two _ _ U _).trans (heq_mul_one_smul A U _ _).symm).trans
    ((heq_mul_app_left A hi U (heq_eqToHom_app_two _ _ U _) _).trans
      (heq_mul_app_right A (show j = j by omega) U _
        ((heq_eqToHom_app_two _ _ U y).trans (heq_eqToHom_app_of_eq _ U y).symm))).symm

/-- `(tail, 0)`: the same, with the degree-zero section on the right. -/
theorem tailComp_mul_tz {i j : ℤ} (hi : ¬ i = 0) (hit : (d₀ : ℤ) ≤ i) (hj : j = 0)
    (U : (S.Opens)ᵒᵖ) (x : (tailPiece A d₀ i).val.obj U) (y : (tailPiece A d₀ j).val.obj U) :
    (tailCompApp A d₀ hd (i + j)).val.app U ((tailMul A d₀ hd i j).app U x y) =
      (NonnegTruncation.mul A i j).app U ((tailCompApp A d₀ hd i).val.app U x)
        ((tailCompApp A d₀ hd j).val.app U y) := by
  rw [tailMul_app_tz A d₀ hd hi hit hj (show i = i + j by omega)
      (show (d₀ : ℤ) ≤ i + j by omega) U x y,
    tailCompApp_app_tail A d₀ hd (show ¬ i + j = 0 by omega)
      (show (d₀ : ℤ) ≤ i + j by omega) (show (0 : ℤ) ≤ i + j by omega) U,
    tailCompApp_app_tail A d₀ hd hi hit (show (0 : ℤ) ≤ i by omega) U x,
    tailCompApp_app_zero A d₀ hd hj U y]
  refine eq_of_heq (HEq.trans ?_ (NonnegTruncation.heq_mul_app_of_nonneg A
    (show (0 : ℤ) ≤ i by omega) (show (0 : ℤ) ≤ j by omega) U _ _).symm)
  exact ((heq_eqToHom_app_two _ _ U _).trans (heq_mul_smul_one A U _ _).symm).trans
    ((heq_mul_app_left A (show i = i by omega) U
        ((heq_eqToHom_app_two _ _ U x).trans (heq_eqToHom_app_of_eq _ U x).symm) _).trans
      (heq_mul_app_right A hj U _ (heq_eqToHom_app_two _ _ U _))).symm

/-- `(tail, tail)`: both factors are sections of `A` and the two multiplications are the same
one, read through the transports. -/
theorem tailComp_mul_tt {i j : ℤ} (hi : ¬ i = 0) (hit : (d₀ : ℤ) ≤ i) (hj : ¬ j = 0)
    (hjt : (d₀ : ℤ) ≤ j)
    (U : (S.Opens)ᵒᵖ) (x : (tailPiece A d₀ i).val.obj U) (y : (tailPiece A d₀ j).val.obj U) :
    (tailCompApp A d₀ hd (i + j)).val.app U ((tailMul A d₀ hd i j).app U x y) =
      (NonnegTruncation.mul A i j).app U ((tailCompApp A d₀ hd i).val.app U x)
        ((tailCompApp A d₀ hd j).val.app U y) := by
  rw [tailMul_app_tt A d₀ hd hi hit hj hjt (show (d₀ : ℤ) ≤ i + j by omega) U x y,
    tailCompApp_app_tail A d₀ hd (show ¬ i + j = 0 by omega)
      (show (d₀ : ℤ) ≤ i + j by omega) (show (0 : ℤ) ≤ i + j by omega) U,
    tailCompApp_app_tail A d₀ hd hi hit (show (0 : ℤ) ≤ i by omega) U x,
    tailCompApp_app_tail A d₀ hd hj hjt (show (0 : ℤ) ≤ j by omega) U y]
  refine eq_of_heq (HEq.trans ?_ (NonnegTruncation.heq_mul_app_of_nonneg A
    (show (0 : ℤ) ≤ i by omega) (show (0 : ℤ) ≤ j by omega) U _ _).symm)
  exact (heq_eqToHom_app_two _ _ U _).trans
    ((heq_mul_app_left A (show i = i by omega) U
        ((heq_eqToHom_app_two _ _ U x).trans (heq_eqToHom_app_of_eq _ U x).symm) _).trans
      (heq_mul_app_right A (show j = j by omega) U _
        ((heq_eqToHom_app_two _ _ U y).trans (heq_eqToHom_app_of_eq _ U y).symm))).symm

/-- A left degree outside `{0} ∪ [d₀, ∞)`: both sides vanish, the left factor being a section of
a zero piece. -/
theorem tailComp_mul_null_left {i j : ℤ} (hi : ¬ i = 0) (hit : ¬ (d₀ : ℤ) ≤ i)
    (U : (S.Opens)ᵒᵖ) (x : (tailPiece A d₀ i).val.obj U) (y : (tailPiece A d₀ j).val.obj U) :
    (tailCompApp A d₀ hd (i + j)).val.app U ((tailMul A d₀ hd i j).app U x y) =
      (NonnegTruncation.mul A i j).app U ((tailCompApp A d₀ hd i).val.app U x)
        ((tailCompApp A d₀ hd j).val.app U y) := by
  rw [tailMul_app_eq_zero_left A d₀ hd hi hit U x y,
    tailCompApp_app_eq_zero A d₀ hd hi hit U x, map_zero, map_zero,
    AddMonoidHom.zero_apply]

/-- A right degree outside `{0} ∪ [d₀, ∞)`: both sides vanish, the right factor being a section
of a zero piece. -/
theorem tailComp_mul_null_right {i j : ℤ} (hj : ¬ j = 0) (hjt : ¬ (d₀ : ℤ) ≤ j)
    (U : (S.Opens)ᵒᵖ) (x : (tailPiece A d₀ i).val.obj U) (y : (tailPiece A d₀ j).val.obj U) :
    (tailCompApp A d₀ hd (i + j)).val.app U ((tailMul A d₀ hd i j).app U x y) =
      (NonnegTruncation.mul A i j).app U ((tailCompApp A d₀ hd i).val.app U x)
        ((tailCompApp A d₀ hd j).val.app U y) := by
  rw [tailMul_app_eq_zero A d₀ hd (Or.inr ⟨hj, hjt⟩) U x y,
    tailCompApp_app_eq_zero A d₀ hd hj hjt U y, map_zero, map_zero]

/-- **The comparison is multiplicative.**  Four of the nine branches are substantive — those in
which each degree is either `0` or `≥ d₀` — and each is one of: multiplicativity of the unit map,
one of the two linearity laws of the multiplication of `A` together with its unit law, or the
transport of the multiplication of `A` itself.  In the remaining five a factor lies in a zero
piece and both sides vanish. -/
theorem tailComp_mul (i j : ℤ) (U : (S.Opens)ᵒᵖ) (x : (tailPiece A d₀ i).val.obj U)
    (y : (tailPiece A d₀ j).val.obj U) :
    (tailCompApp A d₀ hd (i + j)).val.app U ((tailMul A d₀ hd i j).app U x y) =
      (NonnegTruncation.mul A i j).app U ((tailCompApp A d₀ hd i).val.app U x)
        ((tailCompApp A d₀ hd j).val.app U y) := by
  by_cases hit : i ≠ 0 ∧ ¬ (d₀ : ℤ) ≤ i
  · exact tailComp_mul_null_left A d₀ hd hit.1 hit.2 U x y
  by_cases hjt : j ≠ 0 ∧ ¬ (d₀ : ℤ) ≤ j
  · exact tailComp_mul_null_right A d₀ hd hjt.1 hjt.2 U x y
  by_cases hi : i = 0 <;> by_cases hj : j = 0
  · exact tailComp_mul_zz A d₀ hd hi hj U x y
  · exact tailComp_mul_zt A d₀ hd hi hj (by omega) U x y
  · exact tailComp_mul_tz A d₀ hd hi (by omega) hj U x y
  · exact tailComp_mul_tt A d₀ hd hi (by omega) hj (by omega) U x y

/-- **The comparison carries the unit to the unit**: the unit section of the structure sheaf is
sent to `1 · 1_A`. -/
theorem tailComp_one (U : (S.Opens)ᵒᵖ) :
    (tailCompApp A d₀ hd 0).val.app U ((tailOne A d₀).eval U) =
      (NonnegTruncation.one A).eval U := by
  rw [tailOne_eval, tailCompApp_app_zero A d₀ hd (show (0 : ℤ) = 0 by omega) U,
    eqToHom_app_eqToHom_app, ProjF1Dehomogenization.ofUnit_unitSections_eval, one_smul]
  exact eq_of_heq (heq_eqToHom_app_of_eq _ U _)

/-- **The comparison `𝒪_S ⊕ ⨁_{n ≥ d₀} A_n ⟶ A_{≥0}`**, as a homomorphism of sheaf-level graded
algebras on `S`.  This is the inclusion of the tail truncation into the nonnegative truncation of
`A`: the unit map of `A` in degree zero, the identification of the pieces in the degrees `≥ d₀`,
and the zero morphism in the band between, where the source vanishes. -/
def tailComparison (hcomm : IsCommutative A)
    (hqc : ∀ n : ℤ, ((A.piece n : S.Modules)).IsQuasicoherent) :
    RelativeProjMapDomain.SheafGradedAlgebraHom (tailSheafGradedAlgebra A d₀ hd hcomm hqc)
      (NonnegTruncation.nonnegSheafGradedAlgebra A hcomm hqc) where
  app n := tailCompApp A d₀ hd n
  app_mul i j U a b := tailComp_mul A d₀ hd i j (op U) a b
  app_one U := tailComp_one A d₀ hd (op U)

/-- The degree-`n` component of `tailComparison` is `tailCompApp A d₀ hd n`. -/
theorem tailComparison_app (hcomm : IsCommutative A)
    (hqc : ∀ n : ℤ, ((A.piece n : S.Modules)).IsQuasicoherent) (n : ℤ) :
    (tailComparison A d₀ hd hcomm hqc).app n = tailCompApp A d₀ hd n :=
  rfl

end Tail

end Stacks.AlgebraicGeometry.SectionAlgebra

end
