module

public import StacksFrontier.AlgebraicGeometry.Koszul.Sheaf.DegreeNegation
public import StacksFrontier.AlgebraicGeometry.Koszul.Sheaf.GradedLeibniz
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExteriorSymmetricConstruction
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedRelativeTensorUnitor

/-!
# The Koszul differential on the exterior algebra of a sheaf of modules

Let `F` be a sheaf of modules on a ringed site and let `φ` be a functional on it, that is, an
`O`-linear map `F → O` read on sections (`PresheafOfModules.ExteriorFunctional`). The exterior
algebra `⋀(F)` of Section 17.21 is `SheafOfModules.sheafifiedExteriorAlgebra`, the degreewise
sheafification of the *sectionwise* exterior algebra `U ↦ ⋀_{O(U)}(F(U))`, and the Koszul
differential of `φ` on the sectionwise algebra is
`PresheafOfModules.exteriorKoszulD`. This file sheafifies that differential and proves the three
laws Stacks tag 062K asks of it: it squares to zero, its value on a degree-one local section `e`
is `φ(e)`, and it satisfies the graded Leibniz rule.

## Main definitions

* `SheafOfModules.exteriorUnit`: the image of a local section of a sectionwise exterior power
  under the sheafification unit, i.e. a local section of `⋀(F)`.
* `SheafOfModules.koszulD`: **the Koszul differential of `φ` on `⋀(F)`**, from the piece of
  degree `p` to the piece of degree `q`, for any pair of degrees with `q + 1 = p`.

## Main results

* `SheafOfModules.koszulD_exteriorUnit`: the differential on a unit image is the unit image of
  the sectionwise differential. This pins `koszulD` down, by
  `PresheafOfModules.sheafification_hom_ext_apply`, and everything else is deduced from it.
* `SheafOfModules.koszulD_restrict`: the differential read on local lifts.
* `SheafOfModules.koszulD_comp_koszulD`: **the differential squares to zero.**
* `SheafOfModules.koszulD_exteriorGenerator`: **the defining equation `d e = φ(e)`** of Stacks
  tag 062K, with the degree-zero piece of `⋀(F)` identified with the structure sheaf by
  `SheafOfModules.sheafifiedExteriorPieceZeroIso`; and
  `SheafOfModules.sheafifiedExteriorGenerator_apply`, which reads the degree-one generator on a
  local section.
* `PresheafOfModules.exteriorKoszulDOf_mul`: the sectionwise graded Leibniz rule in the
  homogeneous form, with the two terms transported into the degree of the differential's target.
* `SheafOfModules.koszulD_mul`: **the graded Leibniz rule on local sections of `⋀(F)`**, in every
  pair of degrees.

## Implementation notes

**Every law is checked on local lifts and concluded by separatedness.** A local section of a
piece of `⋀(F)` is not a sectionwise exterior form; it only becomes one after restriction along a
covering sieve, namely `Stacks.liftSieve`, which is covering by `Stacks.liftSieve_mem`. So each
law is proved by restricting both sides along such a sieve, where
`Stacks.GradedAlgebra.sheafify_mul_restrict` and `SheafOfModules.koszulD_restrict` turn both sides
into unit images of sectionwise sections, and then appealing to
`Stacks.eq_of_isSeparated`. The sectionwise identity that remains is the Leibniz rule of
`StacksFrontier.AlgebraicGeometry.Koszul.Sheaf.GradedLeibniz`. This is the pattern of
`Stacks.GradedAlgebra.sheafify` itself and of
`SheafOfModules.tensorMulLeftSection_eq`.

**The Leibniz rule is stated with the five degrees unconstrained.** Writing it with the degrees
`p`, `q`, `p - 1`, `q - 1` and `p + q - 1` substituted would force every consumer to transport
along the arithmetic identities relating those expressions to the ones it has. Instead the
degrees are named independently and the identities relating them are hypotheses, so a consumer
discharges them by `omega` at its own spelling. The two transports that remain are the honest
ones: the product of degrees `p - 1` and `q` lands in degree `p - 1 + q`, which is the degree
`p + q - 1` of the differential's target only up to an equality of integers, and
`SheafOfModules.gradedCast` carries it there.

**The `rw` tactic cannot see through `SheafOfModules.sheafifiedExteriorAlgebra`.** It is a
semireducible `def`, and `rw` runs at `instances` transparency, so a hypothesis produced by a
lemma about `Stacks.GradedAlgebra.sheafify` is not syntactically about the exterior algebra.
Every such hypothesis below therefore carries an explicit type ascription in the spelling the
goal uses, and the steps that join them are `Eq.trans` and `congrArg`, which unify at default
transparency.

## References

* [Stacks Project, Tag 062K](https://stacks.math.columbia.edu/tag/062K)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf Opposite PresheafOfModules Stacks Stacks.GradedAlgebra

universe v u w

/-! ## Sectionwise exterior powers: transports, sums and integer multiples -/

namespace PresheafOfModules

section Sectionwise

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  (F : PresheafOfModules.{max w w} (O ⋙ forget₂ _ RingCat))

/-- The value of a local section does not see a transport along an equality of degrees. -/
theorem exteriorAlgebraPieceVal_gradedCast {m n : ℤ} (h : m = n) (X : Cᵒᵖ)
    (s : (exteriorAlgebraPiece m F).obj X) :
    exteriorAlgebraPieceVal n F X
        (SheafOfModules.gradedCast (fun t => (exteriorAlgebraPiece t F).obj X) h s) =
      exteriorAlgebraPieceVal m F X s := by
  subst h; rfl

/-- The value of a sum of local sections is the sum of their values. -/
theorem exteriorAlgebraPieceVal_add (n : ℤ) (X : Cᵒᵖ)
    (s t : (exteriorAlgebraPiece n F).obj X) :
    exteriorAlgebraPieceVal n F X (s + t) =
      exteriorAlgebraPieceVal n F X s + exteriorAlgebraPieceVal n F X t := rfl

/-- The value of an integer multiple of a local section is that multiple of its value. -/
theorem exteriorAlgebraPieceVal_zsmul (n : ℤ) (X : Cᵒᵖ) (c : ℤ)
    (s : (exteriorAlgebraPiece n F).obj X) :
    exteriorAlgebraPieceVal n F X (c • s) = c • exteriorAlgebraPieceVal n F X s := rfl

/-- **The graded Leibniz rule for the sectionwise Koszul differential, in the homogeneous form
the differential-graded-algebra axiom takes.** The product of a section of degree `p` and one of
degree `q` lies in degree `p + q`, and its differential in degree `n`; the two terms of the rule
naturally live in degrees `p' + q` and `p + q'` and are transported into degree `n`. All five
degrees are named independently, the identities relating them being hypotheses. -/
theorem exteriorKoszulDOf_mul (φ : ExteriorFunctional.{v, u, w, w} F)
    {p q p' q' n : ℤ} (hp : p' + 1 = p) (hq : q' + 1 = q) (hn : n + 1 = p + q)
    (hA : p' + q = n) (hB : p + q' = n) (X : Cᵒᵖ)
    (x : (exteriorAlgebraPiece p F).obj X) (y : (exteriorAlgebraPiece q F).obj X) :
    Hom.app (exteriorKoszulDOf φ hn) X ((exteriorAlgebraMul F p q).app X x y) =
      SheafOfModules.gradedCast (fun t => (exteriorAlgebraPiece t F).obj X) hA
          ((exteriorAlgebraMul F p' q).app X (Hom.app (exteriorKoszulDOf φ hp) X x) y) +
        (Int.negOnePow p : ℤ) •
          SheafOfModules.gradedCast (fun t => (exteriorAlgebraPiece t F).obj X) hB
            ((exteriorAlgebraMul F p q').app X x (Hom.app (exteriorKoszulDOf φ hq) X y)) := by
  refine exteriorAlgebraPieceVal_injective n F X ?_
  rw [exteriorAlgebraPieceVal_exteriorKoszulDOf_mul φ p q hn X x y _
      (exteriorAlgebraPieceVal_mul F p q X x y),
    exteriorAlgebraPieceVal_add F n X _ _, exteriorAlgebraPieceVal_zsmul F n X _ _,
    exteriorAlgebraPieceVal_gradedCast F hA X _, exteriorAlgebraPieceVal_gradedCast F hB X _,
    exteriorAlgebraPieceVal_mul F p' q X _ _, exteriorAlgebraPieceVal_mul F p q' X _ _,
    exteriorAlgebraPieceVal_exteriorKoszulDOf φ hp X x,
    exteriorAlgebraPieceVal_exteriorKoszulDOf φ hq X y]

end Sectionwise

end PresheafOfModules

/-! ## The sheafified Koszul differential -/

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (F : SheafOfModules.{w} (toRingCat J Osharp))
  (φ : PresheafOfModules.ExteriorFunctional.{v, u, w, w} F.val)

/-- **A local section of `⋀(F)` coming from a sectionwise exterior form**: the image of a local
section of the sectionwise exterior power of degree `n` under the sheafification unit. Every
local section of `⋀(F)` is of this form after restriction along a covering sieve, which is what
`Stacks.liftSieve_mem` says. -/
noncomputable abbrev exteriorUnit (n : ℤ) (X : Cᵒᵖ)
    (s : (exteriorAlgebraPiece n F.val).obj X) :
    ((sheafifiedExteriorAlgebra J F).piece n).val.obj X :=
  Hom.app (sheafifyUnit (𝟙 (toRingCat J Osharp).obj) (exteriorAlgebraPiece n F.val)) X s

variable {J F}

/-- The unit image of a sum is the sum of the unit images. -/
theorem exteriorUnit_add (n : ℤ) (X : Cᵒᵖ) (s t : (exteriorAlgebraPiece n F.val).obj X) :
    exteriorUnit J F n X (s + t) = exteriorUnit J F n X s + exteriorUnit J F n X t :=
  map_add _ _ _

/-- The unit image of an integer multiple is that multiple of the unit image. -/
theorem exteriorUnit_zsmul (n : ℤ) (X : Cᵒᵖ) (c : ℤ)
    (s : (exteriorAlgebraPiece n F.val).obj X) :
    exteriorUnit J F n X (c • s) = c • exteriorUnit J F n X s :=
  map_zsmul _ _ _

variable (J F)

/-- **The Koszul differential of a functional `φ` on the exterior algebra `⋀(F)` of a sheaf of
modules**, from the homogeneous piece of degree `p` to the one of degree `q`, for degrees with
`q + 1 = p`. It is the sheafification of the sectionwise Koszul differential, which is contraction
of the exterior algebra of the sections by `φ`. -/
noncomputable def koszulD {p q : ℤ} (h : q + 1 = p) :
    (sheafifiedExteriorAlgebra J F).piece p ⟶ (sheafifiedExteriorAlgebra J F).piece q :=
  (PresheafOfModules.sheafification (𝟙 (toRingCat J Osharp).obj)).map
    (PresheafOfModules.exteriorKoszulDOf φ h)

/-- **The Koszul differential of `⋀(F)` on a unit image** is the unit image of the sectionwise
Koszul differential. Since the unit images of local sections determine a morphism out of a
sheafification, this characterizes `SheafOfModules.koszulD`. -/
theorem koszulD_exteriorUnit {p q : ℤ} (h : q + 1 = p) (X : Cᵒᵖ)
    (s : (exteriorAlgebraPiece p F.val).obj X) :
    (koszulD J F φ h).val.app X (exteriorUnit J F p X s) =
      exteriorUnit J F q X (Hom.app (PresheafOfModules.exteriorKoszulDOf φ h) X s) :=
  PresheafOfModules.unit_naturality_apply _ X s

/-- **The Koszul differential of `⋀(F)` read on a local lift.** If a local section of the piece
of degree `p` restricts to the unit image of a sectionwise exterior form `s`, then its
differential restricts to the unit image of the sectionwise differential of `s`. -/
theorem koszulD_restrict {p q : ℤ} (h : q + 1 = p) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (b : ((sheafifiedExteriorAlgebra J F).piece p).val.obj X)
    (s : (exteriorAlgebraPiece p F.val).obj Y)
    (hs : exteriorUnit J F p Y s = ((sheafifiedExteriorAlgebra J F).piece p).val.map f b) :
    ((sheafifiedExteriorAlgebra J F).piece q).val.map f ((koszulD J F φ h).val.app X b) =
      exteriorUnit J F q Y (Hom.app (PresheafOfModules.exteriorKoszulDOf φ h) Y s) := by
  rw [← PresheafOfModules.naturality_apply, ← hs, koszulD_exteriorUnit]

/-- **The Koszul differential of `⋀(F)` squares to zero.** -/
theorem koszulD_comp_koszulD {p q r : ℤ} (h : q + 1 = p) (h' : r + 1 = q) :
    koszulD J F φ h ≫ koszulD J F φ h' = 0 := by
  refine sheafification_hom_ext_apply (𝟙 (toRingCat J Osharp).obj) fun X s => ?_
  change (koszulD J F φ h').val.app X ((koszulD J F φ h).val.app X (exteriorUnit J F p X s)) = _
  rw [koszulD_exteriorUnit, koszulD_exteriorUnit, ← PresheafOfModules.comp_app_apply,
    PresheafOfModules.exteriorKoszulDOf_comp_exteriorKoszulDOf]
  simp
  rfl

/-- **The degree-one generator of `⋀(F)` on a local section** is the unit image of the
sectionwise degree-one generator. -/
theorem sheafifiedExteriorGenerator_apply (U : Cᵒᵖ) (e : F.val.obj U) :
    (sheafifiedExteriorGenerator J F).val.app U e =
      exteriorUnit J F 1 U (Hom.app (exteriorAlgebraGen F.val) U e) := by
  refine Eq.trans (congrArg (fun t => ((exteriorAlgebraGradedAlgebra F.val).sheafifyGen
      (𝟙 (toRingCat J Osharp).obj) (exteriorAlgebraGen F.val)).val.app U t)
      (PresheafOfModules.sheafifyCounitIso_inv_apply (𝟙 (toRingCat J Osharp).obj) F U e)) ?_
  exact (exteriorAlgebraGradedAlgebra F.val).sheafifyGen_unit _ _ U e

/-- **The defining equation of the Koszul differential, Stacks tag 062K item (2):** on a
degree-one local section `e` of `⋀(F)`, that is, on a local section of `F`, the differential takes
the value `φ(e)`. The target is the degree-zero piece of `⋀(F)`, identified with the structure
sheaf by `SheafOfModules.sheafifiedExteriorPieceZeroIso`. -/
theorem koszulD_exteriorGenerator (U : Cᵒᵖ) (e : F.val.obj U) :
    (sheafifiedExteriorPieceZeroIso J F).hom.val.app U
        ((koszulD J F φ (show (0 : ℤ) + 1 = 1 by norm_num)).val.app U
          ((sheafifiedExteriorGenerator J F).val.app U e)) = φ.dual U e := by
  rw [sheafifiedExteriorGenerator_apply, koszulD_exteriorUnit]
  refine (PresheafOfModules.sheafifyCounitIso_map_comp_apply (𝟙 (toRingCat J Osharp).obj)
    (SheafOfModules.unit (toRingCat J Osharp)) (exteriorAlgebraPieceZeroIso F.val).hom
    U _).trans ?_
  refine (exteriorAlgebraPieceZeroIso_hom_apply F.val U _).trans ?_
  rw [exteriorAlgebraPieceVal_exteriorKoszulDOf φ _ U _, exteriorAlgebraPieceVal_gen,
    Koszul.contraction, CliffordAlgebra.contractLeft_ι]
  exact ExteriorAlgebra.algebraMap_leftInverse
    (R := (Osharp.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj U) (F.val.obj U) (φ.dual U e)

/-- **The graded Leibniz rule for the Koszul differential of `⋀(F)`.** On local sections `x` of
degree `p` and `y` of degree `q` the differential of the product is the product of `d x` with `y`
plus `(-1) ^ p` times the product of `x` with `d y`, each transported into the target degree of
the differential. The five degrees are named independently and the arithmetic identities relating
them are hypotheses, so no consumer has to transport the statement itself. -/
theorem koszulD_mul {p q p' q' n : ℤ} (hp : p' + 1 = p) (hq : q' + 1 = q) (hn : n + 1 = p + q)
    (hA : p' + q = n) (hB : p + q' = n) (U : Cᵒᵖ)
    (x : ((sheafifiedExteriorAlgebra J F).piece p).val.obj U)
    (y : ((sheafifiedExteriorAlgebra J F).piece q).val.obj U) :
    (koszulD J F φ hn).val.app U (((sheafifiedExteriorAlgebra J F).mul p q).app U x y) =
      gradedCast (fun t => ((sheafifiedExteriorAlgebra J F).piece t).val.obj U) hA
          (((sheafifiedExteriorAlgebra J F).mul p' q).app U
            ((koszulD J F φ hp).val.app U x) y) +
        (Int.negOnePow p : ℤ) •
          gradedCast (fun t => ((sheafifiedExteriorAlgebra J F).piece t).val.obj U) hB
            (((sheafifiedExteriorAlgebra J F).mul p q').app U x
              ((koszulD J F φ hq).val.app U y)) := by
  refine Stacks.eq_of_isSeparated ((sheafifiedExteriorAlgebra J F).piece n)
    (J.intersection_covering (Stacks.liftSieve_mem _ (exteriorAlgebraPiece p F.val) x)
      (Stacks.liftSieve_mem _ (exteriorAlgebraPiece q F.val) y)) ?_
  rintro Y f ⟨⟨x₀, hx₀⟩, ⟨y₀, hy₀⟩⟩
  have hx : exteriorUnit J F p (op Y) x₀ =
    ((sheafifiedExteriorAlgebra J F).piece p).val.map f.op x := hx₀
  have hy : exteriorUnit J F q (op Y) y₀ =
    ((sheafifiedExteriorAlgebra J F).piece q).val.map f.op y := hy₀
  have hxy := ((exteriorAlgebraGradedAlgebra F.val).sheafify_mul_restrict
    (𝟙 (toRingCat J Osharp).obj) p q f.op x y x₀ y₀ hx hy).symm
  have hdx := (koszulD_restrict J F φ hp f.op x x₀ hx).symm
  have hdy := (koszulD_restrict J F φ hq f.op y y₀ hy).symm
  have hR1 : ((sheafifiedExteriorAlgebra J F).piece (p' + q)).val.map f.op
        (((sheafifiedExteriorAlgebra J F).mul p' q).app U
          ((koszulD J F φ hp).val.app U x) y) =
      exteriorUnit J F (p' + q) (op Y)
        ((exteriorAlgebraMul F.val p' q).app (op Y)
          (Hom.app (PresheafOfModules.exteriorKoszulDOf φ hp) (op Y) x₀) y₀) :=
    (exteriorAlgebraGradedAlgebra F.val).sheafify_mul_restrict
      (𝟙 (toRingCat J Osharp).obj) p' q f.op _ y _ y₀ hdx hy
  have hR2 : ((sheafifiedExteriorAlgebra J F).piece (p + q')).val.map f.op
        (((sheafifiedExteriorAlgebra J F).mul p q').app U x
          ((koszulD J F φ hq).val.app U y)) =
      exteriorUnit J F (p + q') (op Y)
        ((exteriorAlgebraMul F.val p q').app (op Y) x₀
          (Hom.app (PresheafOfModules.exteriorKoszulDOf φ hq) (op Y) y₀)) :=
    (exteriorAlgebraGradedAlgebra F.val).sheafify_mul_restrict
      (𝟙 (toRingCat J Osharp).obj) p q' f.op x _ x₀ _ hx hdy
  have hkey : Hom.app (PresheafOfModules.exteriorKoszulDOf φ hn) (op Y)
        ((exteriorAlgebraMul F.val p q).app (op Y) x₀ y₀) =
      gradedCast (fun t => (exteriorAlgebraPiece t F.val).obj (op Y)) hA
          ((exteriorAlgebraMul F.val p' q).app (op Y)
            (Hom.app (PresheafOfModules.exteriorKoszulDOf φ hp) (op Y) x₀) y₀) +
        (Int.negOnePow p : ℤ) •
          gradedCast (fun t => (exteriorAlgebraPiece t F.val).obj (op Y)) hB
            ((exteriorAlgebraMul F.val p q').app (op Y) x₀
              (Hom.app (PresheafOfModules.exteriorKoszulDOf φ hq) (op Y) y₀)) :=
    PresheafOfModules.exteriorKoszulDOf_mul F.val φ hp hq hn hA hB (op Y) x₀ y₀
  have hmid : exteriorUnit J F n (op Y)
        (gradedCast (fun t => (exteriorAlgebraPiece t F.val).obj (op Y)) hA
            ((exteriorAlgebraMul F.val p' q).app (op Y)
              (Hom.app (PresheafOfModules.exteriorKoszulDOf φ hp) (op Y) x₀) y₀) +
          (Int.negOnePow p : ℤ) •
            gradedCast (fun t => (exteriorAlgebraPiece t F.val).obj (op Y)) hB
              ((exteriorAlgebraMul F.val p q').app (op Y) x₀
                (Hom.app (PresheafOfModules.exteriorKoszulDOf φ hq) (op Y) y₀))) =
      gradedCast (fun t => ((sheafifiedExteriorAlgebra J F).piece t).val.obj (op Y)) hA
          (exteriorUnit J F (p' + q) (op Y)
            ((exteriorAlgebraMul F.val p' q).app (op Y)
              (Hom.app (PresheafOfModules.exteriorKoszulDOf φ hp) (op Y) x₀) y₀)) +
        (Int.negOnePow p : ℤ) •
          gradedCast (fun t => ((sheafifiedExteriorAlgebra J F).piece t).val.obj (op Y)) hB
            (exteriorUnit J F (p + q') (op Y)
              ((exteriorAlgebraMul F.val p q').app (op Y) x₀
                (Hom.app (PresheafOfModules.exteriorKoszulDOf φ hq) (op Y) y₀))) := by
    rw [exteriorUnit_add, exteriorUnit_zsmul,
      gradedCast_dependent (Y := fun t => (exteriorAlgebraPiece t F.val).obj (op Y))
        (Z := fun t => ((sheafifiedExteriorAlgebra J F).piece t).val.obj (op Y))
        (fun t s => exteriorUnit J F t (op Y) s) hA,
      gradedCast_dependent (Y := fun t => (exteriorAlgebraPiece t F.val).obj (op Y))
        (Z := fun t => ((sheafifiedExteriorAlgebra J F).piece t).val.obj (op Y))
        (fun t s => exteriorUnit J F t (op Y) s) hB]
  have hRHS := restriction_gradedCast_add_zsmul
    (fun t => (sheafifiedExteriorAlgebra J F).piece t) hA hB f.op (Int.negOnePow p : ℤ)
    (((sheafifiedExteriorAlgebra J F).mul p' q).app U ((koszulD J F φ hp).val.app U x) y)
    (((sheafifiedExteriorAlgebra J F).mul p q').app U x ((koszulD J F φ hq).val.app U y))
  refine (koszulD_restrict J F φ hn f.op _ _ hxy).trans
    ((congrArg (fun s => exteriorUnit J F n (op Y) s) hkey).trans (hmid.trans ?_))
  rw [← hR1, ← hR2]
  exact hRHS.symm

end SheafOfModules

end
