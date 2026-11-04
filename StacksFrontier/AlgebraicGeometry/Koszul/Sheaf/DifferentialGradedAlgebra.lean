module

public import StacksFrontier.AlgebraicGeometry.Koszul.Sheaf.GradedCommutativity
public import StacksFrontier.AlgebraicGeometry.Koszul.Sheaf.SheafifiedDifferential
public import StacksCore.Tactic.StacksAttribute

/-!
# The Koszul complex of a sheaf of modules as a sheaf of differential graded algebras

Let `F` be a sheaf of modules on a ringed site and let `φ` be an `O`-linear map `F → O`, read on
sections as a `PresheafOfModules.ExteriorFunctional`. Stacks tag 062K attaches to `φ` the
*Koszul complex* `K_•(φ)`: the exterior algebra `⋀(F)` of Section 17.21, graded as usual, together
with the derivation whose value on a degree-one local section `e` is `φ(e)`. This file assembles
that datum into a `SheafOfModules.DifferentialGradedAlgebra`.

## Main definitions

* `SheafOfModules.koszulCochainComplex`: **the Koszul complex of `φ` as a cochain complex of
  sheaves of modules**, with `⋀^(-n)(F)` in degree `n`.
* `SheafOfModules.koszulDifferentialGradedAlgebra`: **`K_•(φ)`**, the Koszul complex as a sheaf of
  differential graded algebras.
* `SheafOfModules.ringedSpaceKoszulDifferentialGradedAlgebra`: the same for a sheaf of modules on
  a ringed space, which is the form Stacks tag 062K is stated in.

## Main results

* `SheafOfModules.koszulCochainComplex_X` and `koszulCochainComplex_d`: the terms and the
  differential of the complex.
* `SheafOfModules.koszulD_gradedCast`: the differential does not see a transport of its source
  along an equality of degrees.
* `SheafOfModules.koszulLeibniz`: **the graded Leibniz rule in the exact shape the `leibniz`
  axiom of `SheafOfModules.DifferentialGradedAlgebra` demands**, which is
  `SheafOfModules.koszulD_mul` read through the negated grading.
* `SheafOfModules.koszulDifferentialGradedAlgebra_toGradedAlgebra`: **the underlying graded
  algebra of `K_•(φ)` is `⋀(F)`**, with its grading negated; `⋀(F)` is the exterior algebra of
  `F` by `SheafOfModules.isExteriorAlgebra_sheafifiedExteriorAlgebra`, which is item (1) of
  Stacks tag 062K.
* `SheafOfModules.koszulDifferentialGradedAlgebra_d_exteriorGenerator`: **item (2) of Stacks tag
  062K**, `d e = φ(e)`, stated for the assembled algebra.
* `SheafOfModules.IsKoszulDerivation`: the property of being a graded derivation of `⋀(F)`, and
  `SheafOfModules.isKoszulDerivation_koszulD`: the Koszul differential is one.
* `SheafOfModules.koszulD_unique` and `SheafOfModules.existsUnique_koszulDerivation`: **the
  uniqueness clause of Stacks tag 062K item (2)**, that the Koszul differential is the only graded
  derivation of `⋀(F)` whose value on a degree-one local section `e` is `φ(e)`.

## Implementation notes

**The exterior grading is negated.** The underlying complex of a
`SheafOfModules.DifferentialGradedAlgebra` is a `CochainComplex`, whose differential goes from
degree `n` to degree `n + 1`, while the Koszul differential *lowers* the exterior degree. So
degree `n` of the complex is the exterior piece of degree `-n`, and the multiplication and the
unit come from `SheafOfModules.GradedAlgebra.negate`. The sign is unaffected: the `leibniz` axiom
asks for `Int.negOnePow n` where the exterior grading asks for `Int.negOnePow (-n)`, and those are
equal by `Int.negOnePow_neg`.

**Three transports appear in the `leibniz` axiom and none of them is `rfl`.** The reindexed
multiplication of degrees `n` and `i` lands in the exterior piece of degree `-n + -i`, whereas
degree `n + i` of the complex is the piece of degree `-(n + i)`; the axiom then transports along
`n + 1 + i = n + i + 1` and `n + (i + 1) = n + i + 1`, in the *cochain* grading. So each term of
the axiom carries a transport inside the negated family composed with one in the exterior family,
and the proof reduces them to a single transport in the exterior family with
`SheafOfModules.gradedCast_comp` and `gradedCast_trans`. Equality proofs with the same endpoints
are definitionally equal, so once the endpoints agree with those of
`SheafOfModules.koszulD_mul` the two statements are interchangeable by `exact`.

**Uniqueness of the differential is proved by induction on a sectionwise exterior form, not by
a decomposition of the sheaf.** Stacks tag 062K specifies the differential as *the* derivation
extending `φ`, and `SheafOfModules.existsUnique_koszulDerivation` is that statement. Two
morphisms out of a sheafification which agree on the unit images of local sections are equal
(`PresheafOfModules.sheafification_hom_ext_apply`), so it is enough to compare the two
derivations on the unit image of a sectionwise exterior form of degree `m`; and such a form is
built from scalars, sums and left multiplication by a degree-one generator, which is
`Submodule.pow_induction_on_left'`. This is the shape of the ring-level argument
`Koszul.HomologicalDifferentialGradedExteriorAlgebra.differential_unique`, carried out one degree
at a time because the Leibniz rule relates the degrees rather than ignoring them. No
decomposition of `⋀(F)` into its homogeneous pieces is needed, and none is available.

**The source says *commutative* differential graded algebra, and the notion this library has is
`SheafOfModules.DifferentialGradedAlgebra`, which is Stacks tag 0FRF's and carries no
commutativity axiom.** Graded commutativity of `⋀(F)` is therefore not a field to be filled here
but a statement of its own, and it is
`SheafOfModules.sheafifiedExteriorMul_comm` in
`StacksFrontier.AlgebraicGeometry.Koszul.Sheaf.GradedCommutativity`.

## References

* [Stacks Project, Tag 062K](https://stacks.math.columbia.edu/tag/062K)
* [Stacks Project, Tag 0FRF](https://stacks.math.columbia.edu/tag/0FRF)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf Opposite PresheafOfModules Stacks Stacks.GradedAlgebra

open scoped ExteriorAlgebra

universe v u w

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (F : SheafOfModules.{w} (toRingCat J Osharp))
  (φ : PresheafOfModules.ExteriorFunctional.{v, u, w, w} F.val)

/-- **The Koszul differential does not see a transport of its source along an equality of
degrees.** Two equality proofs with the same endpoints are definitionally equal, so the
differential out of degree `p` precomposed with a transport from degree `p'` is the differential
out of degree `p'`. -/
theorem koszulD_gradedCast {p p' q : ℤ} (hp : p' = p) (h : q + 1 = p) (h' : q + 1 = p')
    (U : Cᵒᵖ) (z : ((sheafifiedExteriorAlgebra J F).piece p').val.obj U) :
    (koszulD J F φ h).val.app U
        (gradedCast (fun t => ((sheafifiedExteriorAlgebra J F).piece t).val.obj U) hp z) =
      (koszulD J F φ h').val.app U z := by
  subst hp; rfl

/-- **The Koszul complex `K_•(φ)` of a functional on a sheaf of modules, as a cochain complex of
sheaves of modules.** Degree `n` is the exterior piece of degree `-n`, so that the Koszul
differential, which lowers the exterior degree by one, raises the degree of the complex by one. -/
noncomputable def koszulCochainComplex :
    CochainComplex (SheafOfModules.{w} (toRingCat J Osharp)) ℤ :=
  CochainComplex.of (fun n => (sheafifiedExteriorAlgebra J F).piece (-n))
    (fun n => koszulD J F φ (show -(n + 1) + 1 = -n by ring))
    (fun n => koszulD_comp_koszulD J F φ _ _)

/-- Degree `n` of the Koszul complex is the exterior piece of degree `-n`. -/
@[simp]
theorem koszulCochainComplex_X (n : ℤ) :
    (koszulCochainComplex J F φ).X n = (sheafifiedExteriorAlgebra J F).piece (-n) := rfl

/-- The differential of the Koszul complex from degree `n` to degree `n + 1` is the Koszul
differential out of the exterior piece of degree `-n`. -/
@[simp]
theorem koszulCochainComplex_d (n : ℤ) :
    (koszulCochainComplex J F φ).d n (n + 1) =
      koszulD J F φ (show -(n + 1) + 1 = -n by ring) :=
  CochainComplex.of_d (fun m => (sheafifiedExteriorAlgebra J F).piece (-m))
    (fun m => koszulD J F φ (show -(m + 1) + 1 = -m by ring)) n

/-- **The graded Leibniz rule for the Koszul differential, in the shape the `leibniz` axiom of a
sheaf of differential graded algebras asks for.** The two sides are `SheafOfModules.koszulD_mul`
at the exterior degrees `-n` and `-i`, with each of its two transports obtained by composing the
axiom's transport in the negated family with the one the reindexed multiplication carries. -/
theorem koszulLeibniz (n i : ℤ) (U : Cᵒᵖ)
    (x : ((sheafifiedExteriorAlgebra J F).piece (-n)).val.obj U)
    (y : ((sheafifiedExteriorAlgebra J F).piece (-i)).val.obj U) :
    (koszulD J F φ (show -(n + i + 1) + 1 = -(n + i) by ring)).val.app U
        (((sheafifiedExteriorAlgebra J F).negate.mul n i).app U x y) =
      gradedCast (fun t => ((sheafifiedExteriorAlgebra J F).piece (-t)).val.obj U)
          (add_right_comm n 1 i)
          (((sheafifiedExteriorAlgebra J F).negate.mul (n + 1) i).app U
            ((koszulD J F φ (show -(n + 1) + 1 = -n by ring)).val.app U x) y) +
        (Int.negOnePow n : ℤ) •
          gradedCast (fun t => ((sheafifiedExteriorAlgebra J F).piece (-t)).val.obj U)
            (add_assoc n i 1).symm
            (((sheafifiedExteriorAlgebra J F).negate.mul n (i + 1)).app U x
              ((koszulD J F φ (show -(i + 1) + 1 = -i by ring)).val.app U y)) := by
  rw [GradedAlgebra.negate_mul_app, GradedAlgebra.negate_mul_app,
    GradedAlgebra.negate_mul_app,
    koszulD_gradedCast J F φ (neg_add n i).symm _ (show -(n + i + 1) + 1 = -n + -i by ring),
    gradedCast_comp (fun s : ℤ => (((sheafifiedExteriorAlgebra J F).piece s).val.obj U : Type w))
      (fun t : ℤ => -t) (add_right_comm n 1 i),
    gradedCast_comp (fun s : ℤ => (((sheafifiedExteriorAlgebra J F).piece s).val.obj U : Type w))
      (fun t : ℤ => -t) (add_assoc n i 1).symm,
    gradedCast_trans (fun s : ℤ => (((sheafifiedExteriorAlgebra J F).piece s).val.obj U : Type w)),
    gradedCast_trans (fun s : ℤ => (((sheafifiedExteriorAlgebra J F).piece s).val.obj U : Type w)),
    show ((Int.negOnePow n : ℤ)) = ((Int.negOnePow (-n) : ℤ)) from by rw [Int.negOnePow_neg]]
  exact koszulD_mul J F φ (show -(n + 1) + 1 = -n by ring) (show -(i + 1) + 1 = -i by ring)
    (show -(n + i + 1) + 1 = -n + -i by ring) (show -(n + 1) + -i = -(n + i + 1) by ring)
    (show -n + -(i + 1) = -(n + i + 1) by ring) U x y

/-- **The Koszul complex `K_•(φ)` of an `O`-module map `φ : F → O`, as a sheaf of differential
graded algebras.** This is Stacks tag 062K. Its underlying graded algebra is the exterior algebra
`⋀(F)` of Section 17.21, read with the grading negated because the complex of a sheaf of
differential graded algebras is a cochain complex while the Koszul differential lowers the
exterior degree; that is
`SheafOfModules.koszulDifferentialGradedAlgebra_toGradedAlgebra`, and `⋀(F)` has the universal
property of the exterior algebra on `F` by
`SheafOfModules.isExteriorAlgebra_sheafifiedExteriorAlgebra`, which is item (1) of the tag. Its
differential is the Koszul differential of `φ`, which is the unique graded derivation of `⋀(F)`
taking a degree-one local section `e` to `φ(e)`
(`SheafOfModules.existsUnique_koszulDerivation`), which is item (2). The tag calls the result a
*commutative* differential graded algebra; `SheafOfModules.DifferentialGradedAlgebra` is Stacks
tag 0FRF's notion and carries no commutativity axiom, and graded commutativity of `⋀(F)` is
`SheafOfModules.sheafifiedExteriorMul_comm`.

`SheafOfModules.ringedSpaceKoszulDifferentialGradedAlgebra` is the specialization to a ringed
space, which is the generality the tag is stated in. -/
@[stacks 062K, sga "3 III 4.6.1" "Koszul complex"]
noncomputable def koszulDifferentialGradedAlgebra :
    DifferentialGradedAlgebra.{w, w} (toRingCat J Osharp) where
  complex := koszulCochainComplex J F φ
  mul n i := (sheafifiedExteriorAlgebra J F).negate.mul n i
  one := (sheafifiedExteriorAlgebra J F).negate.one
  mul_assoc := (sheafifiedExteriorAlgebra J F).negate.mul_assoc
  one_mul := (sheafifiedExteriorAlgebra J F).negate.one_mul
  mul_one := (sheafifiedExteriorAlgebra J F).negate.mul_one
  leibniz n i U x y := by
    rw [koszulCochainComplex_d, koszulCochainComplex_d, koszulCochainComplex_d]
    exact koszulLeibniz J F φ n i U x y

/-- The underlying cochain complex of `K_•(φ)` is `SheafOfModules.koszulCochainComplex`. -/
@[simp]
theorem koszulDifferentialGradedAlgebra_complex :
    (koszulDifferentialGradedAlgebra J F φ).complex = koszulCochainComplex J F φ := rfl

/-- **The underlying graded algebra of `K_•(φ)` is the exterior algebra `⋀(F)`**, read with its
grading negated. This is item (1) of Stacks tag 062K: `⋀(F)` has the universal property of the
exterior algebra on `F` by
`SheafOfModules.isExteriorAlgebra_sheafifiedExteriorAlgebra`. -/
theorem koszulDifferentialGradedAlgebra_toGradedAlgebra :
    (koszulDifferentialGradedAlgebra J F φ).toGradedAlgebra =
      (sheafifiedExteriorAlgebra J F).negate := rfl

/-- **Item (2) of Stacks tag 062K for the assembled algebra:** the differential of `K_•(φ)` out of
degree `-1`, which is the exterior piece of degree one, takes a local section `e` of `F` to
`φ(e)`. -/
theorem koszulDifferentialGradedAlgebra_d_exteriorGenerator (U : Cᵒᵖ) (e : F.val.obj U) :
    (sheafifiedExteriorPieceZeroIso J F).hom.val.app U
        (((koszulDifferentialGradedAlgebra J F φ).complex.d (-1) 0).val.app U
          ((sheafifiedExteriorGenerator J F).val.app U e)) = φ.dual U e := by
  rw [show ((koszulDifferentialGradedAlgebra J F φ).complex.d (-1) 0) =
      koszulD J F φ (show (0 : ℤ) + 1 = 1 by norm_num) from
    koszulCochainComplex_d J F φ (-1)]
  exact koszulD_exteriorGenerator J F φ U e

/-! ### Uniqueness of the differential -/

variable
  (D : ∀ p q : ℤ, q + 1 = p →
    ((sheafifiedExteriorAlgebra J F).piece p ⟶ (sheafifiedExteriorAlgebra J F).piece q))

/-- **A graded derivation of `⋀(F)`**: a family of morphisms lowering the exterior degree by
one which satisfies the signed Leibniz rule on homogeneous local sections, in the form
`SheafOfModules.koszulD_mul` takes. This is the property Stacks tag 062K's phrase "derivation"
names, and it is the `leibniz` axiom of a sheaf of differential graded algebras read through the
negated grading. -/
abbrev IsKoszulDerivation
    (D : ∀ p q : ℤ, q + 1 = p →
      ((sheafifiedExteriorAlgebra J F).piece p ⟶ (sheafifiedExteriorAlgebra J F).piece q)) :
    Prop :=
  ∀ {p q p' q' n : ℤ} (hp : p' + 1 = p) (hq : q' + 1 = q) (hn : n + 1 = p + q)
    (hA : p' + q = n) (hB : p + q' = n) (U : Cᵒᵖ)
    (x : ((sheafifiedExteriorAlgebra J F).piece p).val.obj U)
    (y : ((sheafifiedExteriorAlgebra J F).piece q).val.obj U),
    (D (p + q) n hn).val.app U (((sheafifiedExteriorAlgebra J F).mul p q).app U x y) =
      gradedCast (fun t => ((sheafifiedExteriorAlgebra J F).piece t).val.obj U) hA
          (((sheafifiedExteriorAlgebra J F).mul p' q).app U ((D p p' hp).val.app U x) y) +
        (Int.negOnePow p : ℤ) •
          gradedCast (fun t => ((sheafifiedExteriorAlgebra J F).piece t).val.obj U) hB
            (((sheafifiedExteriorAlgebra J F).mul p q').app U x ((D q q' hq).val.app U y))

variable
  (D : ∀ p q : ℤ, q + 1 = p →
    ((sheafifiedExteriorAlgebra J F).piece p ⟶ (sheafifiedExteriorAlgebra J F).piece q))

/-- Any two local sections of `⋀(F)` in a negative degree are equal. -/
private theorem eq_of_neg_sheafifiedExteriorAlgebra {q : ℤ} (hq : q < 0) (U : Cᵒᵖ)
    (a b : ((sheafifiedExteriorAlgebra J F).piece q).val.obj U) : a = b :=
  (exteriorPiece_eq_zero_of_neg_sheafifiedExteriorAlgebra J F q hq U a).trans
    (exteriorPiece_eq_zero_of_neg_sheafifiedExteriorAlgebra J F q hq U b).symm

/-- **A graded derivation extending `φ` agrees with the Koszul differential on the unit image of
a sectionwise exterior form.** This is the induction behind uniqueness: a sectionwise exterior
form of degree `m` is built from scalars, sums and left multiplication by a degree-one generator
(`Submodule.pow_induction_on_left'`); in a negative degree the target has no nonzero sections, a
sum is handled by additivity, and a product `e ∧ z` by the Leibniz rule for the two derivations
at the degrees `1` and `m`, the hypothesis on the generator and the inductive hypothesis.

The degree of the section is named independently of `m`, which is what lets the product case be
read at the degree `1 + m`. -/
theorem koszulD_eq_on_exteriorUnit
    (hgen : ∀ (U : Cᵒᵖ) (e : F.val.obj U),
      (D 1 0 (by norm_num)).val.app U
          (exteriorUnit J F 1 U (PresheafOfModules.Hom.app (exteriorAlgebraGen F.val) U e)) =
        (koszulD J F φ (show (0 : ℤ) + 1 = 1 by norm_num)).val.app U
          (exteriorUnit J F 1 U (PresheafOfModules.Hom.app (exteriorAlgebraGen F.val) U e)))
    (hleib : IsKoszulDerivation J F D) (U : Cᵒᵖ) (m : ℕ)
    {z : ExteriorAlgebra ((Osharp.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj U)
      (F.val.obj U)}
    (hz : z ∈ ⋀[((Osharp.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj U)]^m (F.val.obj U)) :
    ∀ (pp qq : ℤ), pp = (m : ℤ) → ∀ (hh : qq + 1 = pp)
      (s : (exteriorAlgebraPiece pp F.val).obj U),
      exteriorAlgebraPieceVal pp F.val U s = z →
      (D pp qq hh).val.app U (exteriorUnit J F pp U s) =
        (koszulD J F φ hh).val.app U (exteriorUnit J F pp U s) := by
  induction hz using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    intro pp qq hpp hh s _
    exact eq_of_neg_sheafifiedExteriorAlgebra J F (by omega) U _ _
  | add x y i hx hy ihx ihy =>
    intro pp qq hpp hh s hs
    subst hpp
    have hsplit : s = (⟨x, hx⟩ : (exteriorAlgebraPiece ((i : ℕ) : ℤ) F.val).obj U) + ⟨y, hy⟩ :=
      exteriorAlgebraPieceVal_injective _ F.val U hs
    subst hsplit
    have hadd : exteriorUnit J F ((i : ℕ) : ℤ) U
          ((⟨x, hx⟩ : (exteriorAlgebraPiece ((i : ℕ) : ℤ) F.val).obj U) + ⟨y, hy⟩) =
        exteriorUnit J F ((i : ℕ) : ℤ) U ⟨x, hx⟩ + exteriorUnit J F ((i : ℕ) : ℤ) U ⟨y, hy⟩ :=
      map_add _ _ _
    rw [hadd, map_add, map_add,
      ihx ((i : ℕ) : ℤ) qq rfl hh ⟨x, hx⟩ rfl, ihy ((i : ℕ) : ℤ) qq rfl hh ⟨y, hy⟩ rfl]
  | mem_mul mm hmm i x hx ih =>
    intro pp qq hpp hh s hs
    obtain ⟨e, rfl⟩ := hmm
    obtain rfl : pp = 1 + (i : ℤ) := by omega
    have hsplit : s = ((exteriorAlgebraGradedAlgebra F.val).mul 1 ((i : ℕ) : ℤ)).app U
        (PresheafOfModules.Hom.app (exteriorAlgebraGen F.val) U e) ⟨x, hx⟩ :=
      exteriorAlgebraPieceVal_injective _ F.val U (by
        rw [hs, exteriorAlgebraGradedAlgebra_mul,
          exteriorAlgebraPieceVal_mul F.val 1 ((i : ℕ) : ℤ) U
            (PresheafOfModules.Hom.app (exteriorAlgebraGen F.val) U e) ⟨x, hx⟩,
          exteriorAlgebraPieceVal_gen F.val U e])
    subst hsplit
    have hunit : exteriorUnit J F (1 + ((i : ℕ) : ℤ)) U
          (((exteriorAlgebraGradedAlgebra F.val).mul 1 ((i : ℕ) : ℤ)).app U
            (PresheafOfModules.Hom.app (exteriorAlgebraGen F.val) U e) ⟨x, hx⟩) =
        ((sheafifiedExteriorAlgebra J F).mul 1 ((i : ℕ) : ℤ)).app U
          (exteriorUnit J F 1 U (PresheafOfModules.Hom.app (exteriorAlgebraGen F.val) U e))
          (exteriorUnit J F ((i : ℕ) : ℤ) U ⟨x, hx⟩) :=
      ((exteriorAlgebraGradedAlgebra F.val).sheafify_mul_unit
        (𝟙 (toRingCat J Osharp).obj) 1 ((i : ℕ) : ℤ) U
        (PresheafOfModules.Hom.app (exteriorAlgebraGen F.val) U e) ⟨x, hx⟩).symm
    have hp0 : (0 : ℤ) + 1 = 1 := by norm_num
    have hqi : ((i : ℕ) : ℤ) - 1 + 1 = ((i : ℕ) : ℤ) := by ring
    have hA : (0 : ℤ) + ((i : ℕ) : ℤ) = qq := by omega
    have hB : (1 : ℤ) + (((i : ℕ) : ℤ) - 1) = qq := by omega
    rw [hunit]
    refine (hleib hp0 hqi hh hA hB U _ _).trans ?_
    refine Eq.trans ?_ (koszulD_mul J F φ hp0 hqi hh hA hB U _ _).symm
    rw [hgen U e, ih ((i : ℕ) : ℤ) (((i : ℕ) : ℤ) - 1) rfl hqi ⟨x, hx⟩ rfl]

/-- **Uniqueness of the Koszul differential, the second half of Stacks tag 062K item (2):** a
graded derivation of `⋀(F)` whose value on a degree-one local section `e` is `φ(e)` is the Koszul
differential. In a negative degree both sides land in a piece with no nonzero sections; in a
nonnegative degree two morphisms out of a sheafification agreeing on unit images are equal
(`PresheafOfModules.sheafification_hom_ext_apply`), and they do agree by
`SheafOfModules.koszulD_eq_on_exteriorUnit`. -/
theorem koszulD_unique
    (hgen : ∀ (U : Cᵒᵖ) (e : F.val.obj U),
      (sheafifiedExteriorPieceZeroIso J F).hom.val.app U
          ((D 1 0 (by norm_num)).val.app U ((sheafifiedExteriorGenerator J F).val.app U e)) =
        φ.dual U e)
    (hleib : IsKoszulDerivation J F D) {p q : ℤ} (h : q + 1 = p) :
    D p q h = koszulD J F φ h := by
  have hgen' : ∀ (U : Cᵒᵖ) (e : F.val.obj U),
      (D 1 0 (by norm_num)).val.app U
          (exteriorUnit J F 1 U (PresheafOfModules.Hom.app (exteriorAlgebraGen F.val) U e)) =
        (koszulD J F φ (show (0 : ℤ) + 1 = 1 by norm_num)).val.app U
          (exteriorUnit J F 1 U (PresheafOfModules.Hom.app (exteriorAlgebraGen F.val) U e)) := by
    intro U e
    have hinj : ∀ a b : ((sheafifiedExteriorAlgebra J F).piece 0).val.obj U,
        (sheafifiedExteriorPieceZeroIso J F).hom.val.app U a =
          (sheafifiedExteriorPieceZeroIso J F).hom.val.app U b → a = b := by
      intro a b hab
      rw [← SheafOfModules.iso_inv_hom_app_apply (sheafifiedExteriorPieceZeroIso J F) U a,
        ← SheafOfModules.iso_inv_hom_app_apply (sheafifiedExteriorPieceZeroIso J F) U b, hab]
    refine hinj _ _ ?_
    rw [← sheafifiedExteriorGenerator_apply, hgen U e]
    exact (koszulD_exteriorGenerator J F φ U e).symm
  rcases lt_or_ge p 0 with hp | hp
  · refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
      ModuleCat.hom_ext (LinearMap.ext fun s => ?_))
    exact eq_of_neg_sheafifiedExteriorAlgebra J F (by omega) U _ _
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, p = (k : ℤ) := ⟨p.toNat, (Int.toNat_of_nonneg hp).symm⟩
    refine sheafification_hom_ext_apply (𝟙 (toRingCat J Osharp).obj) fun U s => ?_
    exact koszulD_eq_on_exteriorUnit J F φ D hgen' hleib U k
      (s : ↥(ExteriorAlgebra.intPiece _ _ ((k : ℕ) : ℤ))).2 ((k : ℕ) : ℤ) q rfl h s rfl

variable {D}

/-- **The Koszul differential is a graded derivation of `⋀(F)`.** -/
theorem isKoszulDerivation_koszulD :
    IsKoszulDerivation J F (fun _ _ h => koszulD J F φ h) :=
  fun hp hq hn hA hB U x y => koszulD_mul J F φ hp hq hn hA hB U x y

/-- **Stacks tag 062K item (2) in full:** there is exactly one graded derivation of `⋀(F)` whose
value on a degree-one local section `e` of `⋀(F)`, that is, on a local section of `F`, is `φ(e)`;
and it is the Koszul differential. -/
theorem existsUnique_koszulDerivation :
    ∃! D : ∀ p q : ℤ, q + 1 = p →
        ((sheafifiedExteriorAlgebra J F).piece p ⟶ (sheafifiedExteriorAlgebra J F).piece q),
      (∀ (U : Cᵒᵖ) (e : F.val.obj U),
          (sheafifiedExteriorPieceZeroIso J F).hom.val.app U
              ((D 1 0 (by norm_num)).val.app U
                ((sheafifiedExteriorGenerator J F).val.app U e)) = φ.dual U e) ∧
        IsKoszulDerivation J F D := by
  refine ⟨fun _ _ h => koszulD J F φ h,
    ⟨fun U e => koszulD_exteriorGenerator J F φ U e, isKoszulDerivation_koszulD J F φ⟩,
    fun D hD => ?_⟩
  funext p q h
  exact koszulD_unique J F φ D hD.1 hD.2 h

/-! ### The ringed-space case -/

section RingedSpace

open AlgebraicGeometry TopologicalSpace RingedSpaceModuleAdjunction

/-- **The Koszul complex of a functional on a sheaf of modules on a ringed space**, as a sheaf of
differential graded algebras. Stacks tag 062K is stated for a ringed space; this is the previous
definition at the site of open subsets, with no hypothesis added, exactly as
`SheafOfModules.ringedSpaceTensorExteriorSymmetricAlgebras` is. -/
@[sga "6 IX 1.8" "more general"]
noncomputable def ringedSpaceKoszulDifferentialGradedAlgebra (X : RingedSpace.{w, w})
    (F : SheafOfModules.{w} (structureSheafRing X))
    (φ : PresheafOfModules.ExteriorFunctional.{w, w, w, w} F.val) :
    DifferentialGradedAlgebra.{w, w} (structureSheafRing X) :=
  koszulDifferentialGradedAlgebra (Opens.grothendieckTopology X.carrier) F φ

end RingedSpace

end SheafOfModules

end
