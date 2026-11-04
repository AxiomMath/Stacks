module

public import StacksFrontier.AlgebraicGeometry.TwistTensor.GradedLaurentMul
public import StacksFrontier.AlgebraicGeometry.TwistTensor.TensorUnitUniqueInvLaw
public import StacksFrontier.AlgebraicGeometry.TwistTensor.ThetaIntegerBidegree
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.HyperplaneTwistSequence

/-!
# Transport of the integer tensor powers along an isomorphism is multiplicative

`Stacks.AlgebraicGeometry.HyperplaneTwistSequence.tensorPowModuleIsoOfIsoInt X N N' e` carries the
integer tensor powers of an invertible `𝒪_X`-module `N` to those of an isomorphic `N'`, in every
integer degree.  **This file proves that the family is multiplicative in an arbitrary integer
bidegree**, which is what makes it an isomorphism of `ℤ`-graded `𝒪_X`-algebras
`⨁_{n ∈ ℤ} N^{⊗ n} ≅ ⨁_{n ∈ ℤ} N'^{⊗ n}` rather than a degreewise family of isomorphisms.

## Main results

* `Stacks.AlgebraicGeometry.TensorPowCongrInt.tensorPowModuleIsoOfIsoInt_mul`: **the bidegree
  square in an arbitrary integer bidegree** — the addition law `Stacks.Ample.tensorPowModuleAddIso`
  of the powers of `N` at `(n, m)`, followed by the transport in the degree `n + m`, is the
  transports in the degrees `n` and `m` on the two factors, followed by the addition law of the
  powers of `N'`.
* `Stacks.AlgebraicGeometry.TensorPowCongrInt.tensorPowModuleIsoOfIsoInt_one_eq`: the degree one
  value of the family is `N^{⊗ 1} ≅ N ≅ N' ≅ N'^{⊗ 1}`, which is what lets the bidegree `(n, 1)`
  column be read with `e` itself on the second factor.
* `Stacks.AlgebraicGeometry.TensorPowCongrInt.tensorPowModuleIsoOfIsoInt_mul_add_eq_zero`: the
  inverse-law square, at every bidegree summing to zero.
* `Stacks.AlgebraicGeometry.TensorPowCongrInt.tensorPowModuleInvIsoRight`: the powers in the
  degrees `n` and `-n` are tensor inverses, for an arbitrary invertible module on an arbitrary
  scheme.

## The route

It is the chase of
`StacksFrontier/AlgebraicGeometry/TwistTensor/ThetaIntegerBidegree.lean`, which runs it for the
comparison of the tensor powers of `𝒪_{U_d}(d)` with the `d`-divisible twists.  Both families here
are tensor powers, so the two associativity constraints the chase needs are one lemma,
`Stacks.AlgebraicGeometry.ThetaMul.tensorPowModuleAddIso_assoc_int`, applied to `N` and to `N'`.

What is new is the square at a bidegree summing to zero, the one face no arrangement of
`Stacks.AlgebraicGeometry.ThetaMul.square_step` and `Stacks.Monoidal.square_step_left` reaches
from the nonnegative degrees.  In a negative degree the transport is *defined* as the comparison
of two tensor inverses, `Stacks.AlgebraicGeometry.ProjTwistTensorPow.isoOfTensorUnitIso`, and the
identity that characterises it is
`Stacks.AlgebraicGeometry.TensorUnitInvLaw.isoOfTensorUnitIso_whiskerRight`.  That identity *is*
the square at `(-(k+1), k+1)`, once the degree zero value of the family — the identification
`N^{⊗ 0} ≅ 𝒪_X ≅ N'^{⊗ 0}` — is read into it.

Note which object plays the common tensor inverse: in `tensorPowModuleIsoOfIsoNegSucc` it is
`N^{⊗ (k+1)}`, the power of the *source* module, and the inverse law of `N'^{⊗ -(k+1)}` against it
is the one that goes through the nonnegative-degree transport
`Stacks.RelativeVeryAmple.tensorPowModuleIsoOfIso`.  So the negative half of the square is tied to
the nonnegative half by construction, and that is why the chase closes.

## Implementation notes

**The degree one value is not definitional.** `tensorPowModuleIsoOfIso` is defined by a recursion
whose step splits `N^{⊗ (n+1)}` as `N^{⊗ n} ⊗ N^{⊗ 1}`, so in the degree one the recursion
produces `N^{⊗ 0} ⊗ N^{⊗ 1}` with the zeroth power still present; identifying the result with `e`
is the left unit law of the addition law.  The bidegree `(n, 1)` column at a natural number `n` is
therefore proved first with the recursion's own second factor
(`tensorPowModuleIsoOfIsoInt_mul_one_natCast_aux`), and the degree one value is read off its
instance at `n = 0`.

**The degrees are spelled in several ways.** `((n + 1 : ℕ) : ℤ)` and `(n : ℤ) + 1` are equal and
not syntactically equal, and `Int.negSucc k` and `-((k + 1 : ℕ) : ℤ)` likewise; the recursions of
`tensorPowModuleIsoOfIsoInt` are stated at the first spelling of each pair and the chase runs at
the second.  `tensorPowModuleIsoOfIsoInt_congr` and `tensorPowModuleIsoOfIsoInt_mul_of_eq` move
between them, exactly as `Stacks.AlgebraicGeometry.ThetaMul.thetaInt_congr` and
`thetaInt_mul_of_eq` do in the model.

The monoidal structure is `Stacks.AlgebraicGeometry.ThetaMul.schemeMonoidal`, the strict structure
of Stacks Tag 01CA on `X.Modules`, brought in as a local instance: there is no global monoidal
instance on the modules of a scheme.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry
open Stacks.Ample Stacks.RelativeVeryAmple
open Stacks.AlgebraicGeometry.HyperplaneTwistSequence
open Stacks.AlgebraicGeometry.ThetaMul

namespace Stacks.AlgebraicGeometry.TensorPowCongrInt

attribute [local instance] Stacks.AlgebraicGeometry.ThetaMul.schemeMonoidal
  Stacks.AlgebraicGeometry.ThetaMul.strictSchemeMonoidal

/-! ### Free-shape bookkeeping lemmas

Each of these is the one monoidal step of a square below, with every object and morphism taken as
a variable.  At the tensor powers the degrees `n + 0`, `0 + n` and `n` are three spellings of one
object, so a rewrite inside the concrete composite does not fire. -/

/-- Cancelling an isomorphism against its inverse at the head of a composite, with the composite
given as an equation rather than rewritten in place. -/
theorem hom_inv_cancel_free {D : Type*} [Category D] {A B E : D}
    (i : A ≅ B) {m : A ⟶ E} {t : B ⟶ E} (hm : t = i.inv ≫ m) : i.hom ≫ t = m := by
  rw [hm, Iso.hom_inv_id_assoc]

/-- `CategoryTheory.MonoidalCategory.tensorHom_def_assoc` with its four arguments taken
explicitly, which converts the whiskered form the characterising identity is stated in to the
tensor-product-of-morphisms form a bidegree square is stated in.  Supplying them as a `rw` or
inside a `refine` instead leaves the four objects as metavariables and the unifier does not
terminate on them: 200 000 heartbeats there, against 0.5 s here. -/
private theorem whisker_to_tensorHom {D : Type*} [Category D] [MonoidalCategory D]
    {A A' B B' Y : D} (u : A ⟶ A') (g : B ⟶ B') (rest : A' ⊗ B' ⟶ Y) (t : A ⊗ B ⟶ Y)
    (h : u ▷ B ≫ A' ◁ g ≫ rest = t) : (u ⊗ₘ g) ≫ rest = t :=
  (MonoidalCategory.tensorHom_def_assoc u g rest).trans h

/-- **The bidegree `(n, 0)` square out of the two right unit laws.**  Each family's multiplication
read into the degree zero is the right unitor, and the degree zero value of the comparison is
`z ≫ w`, the two identifications of the zeroth powers with the unit object. -/
theorem zero_right_free {D : Type*} [Category D] [MonoidalCategory D]
    {P T A A' Zn Zn' : D} (f : P ⟶ T) (z : A ⟶ 𝟙_ D) (w : 𝟙_ D ⟶ A') (z' : A' ⟶ 𝟙_ D)
    (mu : P ⊗ A ⟶ Zn) (cz : Zn ⟶ P) (mu' : T ⊗ A' ⟶ Zn') (cz' : Zn' ⟶ T) (czi : T ⟶ Zn')
    (hRU : P ◁ z ≫ (ρ_ P).hom = mu ≫ cz)
    (hRU' : T ◁ z' ≫ (ρ_ T).hom = mu' ≫ cz')
    (hw : w ≫ z' = 𝟙 (𝟙_ D)) (hc : cz' ≫ czi = 𝟙 Zn') :
    mu ≫ cz ≫ f ≫ czi = (f ⊗ₘ (z ≫ w)) ≫ mu' := by
  have h0 : (f ⊗ₘ (z ≫ w)) ≫ (T ◁ z') = f ⊗ₘ z := by
    rw [← MonoidalCategory.id_tensorHom, MonoidalCategory.tensorHom_comp_tensorHom]
    simp only [Category.assoc, Category.comp_id, hw]
  have key : (f ⊗ₘ (z ≫ w)) ≫ mu' ≫ cz' = P ◁ z ≫ (ρ_ P).hom ≫ f := by
    rw [← hRU', ← Category.assoc, h0, MonoidalCategory.tensorHom_def']
    simp only [Category.assoc]
    rw [MonoidalCategory.rightUnitor_naturality]
  have h := congrArg (fun y ↦ y ≫ czi) key
  simp only [Category.assoc] at h
  rw [hc, Category.comp_id] at h
  rw [h, ← Category.assoc (P ◁ z) (ρ_ P).hom (f ≫ czi), hRU]
  simp only [Category.assoc]

/-- **The degree one value out of the bidegree `(0, 1)` column and the two left unit laws.**  Each
family's multiplication read into the degree zero on the *left* is the left unitor, so the column
at `(0, 1)` collapses to an identity between the two candidate comparisons in the degree one. -/
theorem one_eq_free {D : Type*} [Category D] [MonoidalCategory D]
    {A A' B B' Zn Zn' : D} (z : A ⟶ 𝟙_ D) (w : 𝟙_ D ⟶ A') (z' : A' ⟶ 𝟙_ D)
    (gg c1 : B ⟶ B') (mu : A ⊗ B ⟶ Zn) (cz : Zn ⟶ B) (mu' : A' ⊗ B' ⟶ Zn') (cz' : Zn' ⟶ B')
    (czi : B' ⟶ Zn')
    (hLU : z ▷ B ≫ (λ_ B).hom = mu ≫ cz)
    (hLU' : z' ▷ B' ≫ (λ_ B').hom = mu' ≫ cz')
    (hw : w ≫ z' = 𝟙 (𝟙_ D)) (hc : czi ≫ cz' = 𝟙 B') (i : A ⊗ B ≅ B) (hi : i.hom = mu ≫ cz)
    (hcol : mu ≫ cz ≫ c1 ≫ czi = ((z ≫ w) ⊗ₘ gg) ≫ mu') :
    c1 = gg := by
  have h0 : ((z ≫ w) ⊗ₘ gg) ≫ (z' ▷ B') = z ⊗ₘ gg := by
    rw [← MonoidalCategory.tensorHom_id, MonoidalCategory.tensorHom_comp_tensorHom]
    simp only [Category.assoc, Category.comp_id, hw]
  have key : ((z ≫ w) ⊗ₘ gg) ≫ mu' ≫ cz' = mu ≫ cz ≫ gg := by
    rw [← hLU', ← Category.assoc, h0, MonoidalCategory.tensorHom_def]
    simp only [Category.assoc]
    rw [MonoidalCategory.leftUnitor_naturality, ← Category.assoc (z ▷ B) (λ_ B).hom gg, hLU]
    simp only [Category.assoc]
  have h := congrArg (fun y ↦ y ≫ cz') hcol
  simp only [Category.assoc] at h
  rw [hc, Category.comp_id] at h
  refine (Iso.cancel_iso_hom_left i c1 gg).mp ?_
  rw [hi]
  simp only [Category.assoc]
  rw [h, key]

/-- **The inverse-law identity read as a bidegree square.**  `hgate` is the characterising identity
of the comparison of two tensor inverses; composing it with the two inverses of the target family's
transport into the degree zero turns it into the multiplicativity square at that bidegree. -/
theorem inv_law_square_free {D : Type*} [Category D] {A Zp Z0 Un Qp Zp' Z0' : D}
    (mu : A ⟶ Zp) (cz : Zp ⟶ Z0) (zh : Z0 ⟶ Un)
    (tp : A ⟶ Qp) (mu' : Qp ⟶ Zp') (cz' : Zp' ⟶ Z0') (zh' : Z0' ⟶ Un)
    (zhi : Un ⟶ Z0') (czi : Z0' ⟶ Zp')
    (hgate : tp ≫ mu' ≫ cz' ≫ zh' = mu ≫ cz ≫ zh)
    (h1 : zh' ≫ zhi = 𝟙 Z0') (h2 : cz' ≫ czi = 𝟙 Zp') :
    mu ≫ cz ≫ zh ≫ zhi ≫ czi = tp ≫ mu' := by
  have h := congrArg (fun y ↦ y ≫ zhi ≫ czi) hgate
  simp only [Category.assoc] at h
  rw [← h, ← Category.assoc zh' zhi czi, h1, Category.id_comp, h2, Category.comp_id]

/-! ### The two inverse laws of the integer tensor powers -/

variable (X : Scheme.{u})

/-- **The tensor powers of an invertible `𝒪_X`-module in the degrees `n` and `-n` are tensor
inverses**, `L^{⊗ n} ⊗ L^{⊗ (-n)} ≅ 𝒪_X`.  This is the addition law
`Stacks.Ample.tensorPowModuleAddIso` of [Stacks, Tag 01CU] at the bidegree `(n, -n)`, reindexed to
the degree `0`, where the power is the structure sheaf.

The mirror of `Stacks.AlgebraicGeometry.ThetaMul.tensorPowModuleInvIsoLeft`, whose two exponents
are in the opposite order, and the general form of the two copies of this statement that exist at
the twists of `Proj 𝒮` only (`Stacks.AlgebraicGeometry.ThetaMul.DegreeOpen.tensorPowModuleInvIso`
and `Stacks.AlgebraicGeometry.ThetaGlobal.tensorPowModuleInvIso`). -/
def tensorPowModuleInvIsoRight (L : X.Modules) [IsInvertibleModule X L] (n : ℤ) :
    tensorPowModule X L n ⊗ tensorPowModule X L (-n) ≅ 𝟙_ X.Modules :=
  tensorPowModuleAddIso X L n (-n) ≪≫
    tensorPowModuleCongr X L (show n + -n = 0 from by ring) ≪≫ tensorPowModuleZeroIso X L

/-! ### The transport family, degree by degree -/

variable {X}
variable (N N' : X.Modules) [IsInvertibleModule X N] [IsInvertibleModule X N'] (e : N ≅ N')

/-- In a nonnegative degree the integer transport is
`Stacks.RelativeVeryAmple.tensorPowModuleIsoOfIso`, by definition. -/
theorem tensorPowModuleIsoOfIsoInt_natCast (n : ℕ) :
    tensorPowModuleIsoOfIsoInt X N N' e ((n : ℕ) : ℤ) = tensorPowModuleIsoOfIso X N N' e n :=
  rfl

/-- The degree zero value of the transport: the two identifications of the zeroth tensor powers
with the structure sheaf. -/
theorem tensorPowModuleIsoOfIsoInt_zero :
    tensorPowModuleIsoOfIsoInt X N N' e 0 =
      tensorPowModuleZeroIso X N ≪≫ (tensorPowModuleZeroIso X N').symm :=
  rfl

/-- **The transport commutes with the reindexing along an equality of degrees.** -/
theorem tensorPowModuleIsoOfIsoInt_congr {a b : ℤ} (h : b = a) :
    (tensorPowModuleIsoOfIsoInt X N N' e b).hom =
      (tensorPowModuleCongr X N h).hom ≫ (tensorPowModuleIsoOfIsoInt X N N' e a).hom ≫
        (tensorPowModuleCongr X N' h.symm).hom := by
  cases h
  rw [tensorPowModuleCongr_hom, tensorPowModuleCongr_hom, eqToHom_refl, eqToHom_refl,
    Category.id_comp, Category.comp_id]

/-- A value of the transport at `b`, written as a conjugate by the reindexings along `h : b = a`,
is the value at `a` itself. -/
private theorem isoOfIsoInt_hom_eq_of_congr {a b : ℤ} (h : b = a)
    {Y : tensorPowModule X N a ⟶ tensorPowModule X N' a}
    (hY : (tensorPowModuleIsoOfIsoInt X N N' e b).hom =
      (tensorPowModuleCongr X N h).hom ≫ Y ≫ (tensorPowModuleCongr X N' h.symm).hom) :
    (tensorPowModuleIsoOfIsoInt X N N' e a).hom = Y := by
  have h2 := tensorPowModuleIsoOfIsoInt_congr N N' e h
  rw [hY] at h2
  exact (Iso.cancel_iso_hom_left (tensorPowModuleCongr X N h) _ _).mp
    ((Iso.cancel_iso_hom_right _ _ (tensorPowModuleCongr X N' h.symm)).mp h2.symm)

/-- In a negative degree the integer transport is `tensorPowModuleIsoOfIsoNegSucc`, the comparison
of two tensor inverses, with the two reindexings of `Int.negSucc k` as `-(k+1)` cancelled. -/
theorem tensorPowModuleIsoOfIsoInt_negSucc (k : ℕ) :
    (tensorPowModuleIsoOfIsoInt X N N' e (-((k + 1 : ℕ) : ℤ))).hom =
      (tensorPowModuleIsoOfIsoNegSucc X N N' e k).hom := by
  have hd : (Int.negSucc k) = -((k + 1 : ℕ) : ℤ) := by push_cast; rfl
  exact isoOfIsoInt_hom_eq_of_congr N N' e hd rfl

/-! ### The squares -/

/-- **The multiplicativity square transported along equalities of the two degrees.** -/
theorem tensorPowModuleIsoOfIsoInt_mul_of_eq {p q p' q' : ℤ} (hp : p = p') (hq : q = q')
    (H : (tensorPowModuleAddIso X N p q).hom ≫
          (tensorPowModuleIsoOfIsoInt X N N' e (p + q)).hom =
        ((tensorPowModuleIsoOfIsoInt X N N' e p).hom ⊗ₘ
            (tensorPowModuleIsoOfIsoInt X N N' e q).hom) ≫
          (tensorPowModuleAddIso X N' p q).hom) :
    (tensorPowModuleAddIso X N p' q').hom ≫
        (tensorPowModuleIsoOfIsoInt X N N' e (p' + q')).hom =
      ((tensorPowModuleIsoOfIsoInt X N N' e p').hom ⊗ₘ
          (tensorPowModuleIsoOfIsoInt X N N' e q').hom) ≫
        (tensorPowModuleAddIso X N' p' q').hom := by
  cases hp; cases hq; exact H

/-- **Multiplicativity in the bidegree `(n, 0)`, for an arbitrary integer `n`.**  This is the right
unit law: both multiplications agree with the right unitor of Stacks Tag 01CA on the
identification of the zeroth power with the structure sheaf, and the degree zero value of the
transport *is* the pair of those identifications.  Nothing is needed about the value in the degree
`n`, which is why no sign condition appears. -/
theorem tensorPowModuleIsoOfIsoInt_mul_zero (n : ℤ) :
    (tensorPowModuleAddIso X N n 0).hom ≫
        (tensorPowModuleIsoOfIsoInt X N N' e (n + 0)).hom =
      ((tensorPowModuleIsoOfIsoInt X N N' e n).hom ⊗ₘ
          (tensorPowModuleIsoOfIsoInt X N N' e 0).hom) ≫
        (tensorPowModuleAddIso X N' n 0).hom := by
  rw [tensorPowModuleIsoOfIsoInt_congr N N' e (show n + 0 = n from by omega),
    tensorPowModuleIsoOfIsoInt_zero]
  exact zero_right_free (tensorPowModuleIsoOfIsoInt X N N' e n).hom
    (tensorPowModuleZeroIso X N).hom (tensorPowModuleZeroIso X N').inv
    (tensorPowModuleZeroIso X N').hom
    (tensorPowModuleAddIso X N n 0).hom
    (tensorPowModuleCongr X N (show n + 0 = n from by omega)).hom
    (tensorPowModuleAddIso X N' n 0).hom
    (tensorPowModuleCongr X N' (show n + 0 = n from by omega)).hom
    (tensorPowModuleCongr X N' (show n = n + 0 from by omega)).hom
    (tensorPowModuleAddIso_zero_right_int X N n)
    (tensorPowModuleAddIso_zero_right_int X N' n)
    (tensorPowModuleZeroIso X N').inv_hom_id
    (tensorPowModuleCongr_comp X N' _ _)

/-- **The bidegree `(n, 1)` column at a natural number `n`, with the recursion's own second
factor.**  `Stacks.RelativeVeryAmple.tensorPowModuleIsoOfIso` is defined by a recursion whose step
splits the `(n+1)`-st power as `N^{⊗ n} ⊗ N^{⊗ 1}` and applies the transport to the first factor
and `N^{⊗ 1} ≅ N ≅ N' ≅ N'^{⊗ 1}` to the second; this is that definition, with the two reindexings
of `((n+1 : ℕ) : ℤ)` as `(n : ℤ) + 1` cancelled.

It is the column the chase needs, except that the second factor is the recursion's rather than the
degree one value of the family itself; the two are identified by
`tensorPowModuleIsoOfIsoInt_one_eq`, which is this statement at `n = 0`. -/
theorem tensorPowModuleIsoOfIsoInt_mul_one_natCast_aux (n : ℕ) :
    (tensorPowModuleAddIso X N (n : ℤ) 1).hom ≫
        (tensorPowModuleIsoOfIsoInt X N N' e ((n : ℤ) + 1)).hom =
      ((tensorPowModuleIsoOfIsoInt X N N' e (n : ℤ)).hom ⊗ₘ
          (tensorPowModuleOneIso X N ≪≫ e ≪≫ (tensorPowModuleOneIso X N').symm).hom) ≫
        (tensorPowModuleAddIso X N' (n : ℤ) 1).hom := by
  have hd : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
  have hdef : (tensorPowModuleIsoOfIsoInt X N N' e ((n + 1 : ℕ) : ℤ)).hom =
      (tensorPowModuleCongr X N hd).hom ≫
        ((tensorPowModuleAddIso X N (n : ℤ) 1).inv ≫
          (tensorModulesMapIso X (tensorPowModuleIsoOfIso X N N' e n)
            (tensorPowModuleOneIso X N ≪≫ e ≪≫ (tensorPowModuleOneIso X N').symm)).hom ≫
          (tensorPowModuleAddIso X N' (n : ℤ) 1).hom) ≫
        (tensorPowModuleCongr X N' hd.symm).hom := rfl
  have h3 := isoOfIsoInt_hom_eq_of_congr N N' e hd hdef
  exact (hom_inv_cancel_free (tensorPowModuleAddIso X N (n : ℤ) 1) h3).trans
    (congrArg (fun y ↦ y ≫ (tensorPowModuleAddIso X N' (n : ℤ) 1).hom)
      (Stacks.AlgebraicGeometry.ThetaMul.tensorModulesMapIso_hom X
        (tensorPowModuleIsoOfIso X N N' e n)
        (tensorPowModuleOneIso X N ≪≫ e ≪≫ (tensorPowModuleOneIso X N').symm)))

/-- **The degree one value of the transport** is `N^{⊗ 1} ≅ N ≅ N' ≅ N'^{⊗ 1}`.

The recursion defining `tensorPowModuleIsoOfIso` produces, in the degree one, the transport in the
degree zero on a first factor `N^{⊗ 0}` that is still present; this reads it off, the
identification being the left unit law
`Stacks.AlgebraicGeometry.ThetaMul.tensorPowModuleAddIso_zero_left_int` of the addition law. -/
theorem tensorPowModuleIsoOfIsoInt_one_eq :
    (tensorPowModuleIsoOfIsoInt X N N' e 1).hom =
      (tensorPowModuleOneIso X N ≪≫ e ≪≫ (tensorPowModuleOneIso X N').symm).hom := by
  have hcol := tensorPowModuleIsoOfIsoInt_mul_one_natCast_aux N N' e 0
  rw [show (((0 : ℕ) : ℤ)) = (0 : ℤ) from by omega] at hcol
  rw [tensorPowModuleIsoOfIsoInt_zero,
    tensorPowModuleIsoOfIsoInt_congr N N' e (show (0 : ℤ) + 1 = 1 from by omega)] at hcol
  exact one_eq_free (tensorPowModuleZeroIso X N).hom (tensorPowModuleZeroIso X N').inv
    (tensorPowModuleZeroIso X N').hom
    (tensorPowModuleOneIso X N ≪≫ e ≪≫ (tensorPowModuleOneIso X N').symm).hom
    (tensorPowModuleIsoOfIsoInt X N N' e 1).hom
    (tensorPowModuleAddIso X N 0 1).hom
    (tensorPowModuleCongr X N (show (0 : ℤ) + 1 = 1 from by omega)).hom
    (tensorPowModuleAddIso X N' 0 1).hom
    (tensorPowModuleCongr X N' (show (0 : ℤ) + 1 = 1 from by omega)).hom
    (tensorPowModuleCongr X N' (show (1 : ℤ) = 0 + 1 from by omega)).hom
    (tensorPowModuleAddIso_zero_left_int X N 1)
    (tensorPowModuleAddIso_zero_left_int X N' 1)
    (tensorPowModuleZeroIso X N').inv_hom_id
    (tensorPowModuleCongr_comp X N' _ _)
    (tensorPowModuleAddIso X N 0 1 ≪≫
      tensorPowModuleCongr X N (show (0 : ℤ) + 1 = 1 from by omega)) rfl
    hcol

/-- **The bidegree `(n, 1)` column at a natural number `n`**, with the degree one value of the
family itself on the second factor. -/
theorem tensorPowModuleIsoOfIsoInt_mul_one_natCast (n : ℕ) :
    (tensorPowModuleAddIso X N (n : ℤ) 1).hom ≫
        (tensorPowModuleIsoOfIsoInt X N N' e ((n : ℤ) + 1)).hom =
      ((tensorPowModuleIsoOfIsoInt X N N' e (n : ℤ)).hom ⊗ₘ
          (tensorPowModuleIsoOfIsoInt X N N' e 1).hom) ≫
        (tensorPowModuleAddIso X N' (n : ℤ) 1).hom := by
  rw [tensorPowModuleIsoOfIsoInt_one_eq]
  exact tensorPowModuleIsoOfIsoInt_mul_one_natCast_aux N N' e n

/-- **The multiplicativity square in the bidegree `(p, b + c)`, read at the `(A, BC)` corner of the
associativity diagram in the tridegree `(p, b, c)`.**  The two sides differ only by where the
transport between the two spellings `p + (b + c)` and `p + b + c` of the total degree sits.  The
second form is what `Stacks.AlgebraicGeometry.ThetaMul.square_step` produces and what
`Stacks.Monoidal.square_step_left` consumes, because the associativity constraints of both
families carry that transport. -/
theorem tensorPowModuleIsoOfIsoInt_mul_corner_iff (p b c : ℤ) :
    ((tensorPowModuleAddIso X N p (b + c)).hom ≫
          (tensorPowModuleIsoOfIsoInt X N N' e (p + (b + c))).hom =
        ((tensorPowModuleIsoOfIsoInt X N N' e p).hom ⊗ₘ
            (tensorPowModuleIsoOfIsoInt X N N' e (b + c)).hom) ≫
          (tensorPowModuleAddIso X N' p (b + c)).hom) ↔
      (((tensorPowModuleAddIso X N p (b + c)).hom ≫
              (tensorPowModuleCongr X N (show p + (b + c) = p + b + c from by ring)).hom) ≫
            (tensorPowModuleIsoOfIsoInt X N N' e (p + b + c)).hom =
        ((tensorPowModuleIsoOfIsoInt X N N' e p).hom ⊗ₘ
            (tensorPowModuleIsoOfIsoInt X N N' e (b + c)).hom) ≫
          (tensorPowModuleAddIso X N' p (b + c)).hom ≫
            (tensorPowModuleCongr X N'
              (show p + (b + c) = p + b + c from by ring)).hom) :=
  Iff.trans
    (Iff.of_eq (congrArg (fun z ↦ z = ((tensorPowModuleIsoOfIsoInt X N N' e p).hom ⊗ₘ
        (tensorPowModuleIsoOfIsoInt X N N' e (b + c)).hom) ≫
          (tensorPowModuleAddIso X N' p (b + c)).hom)
      (congrArg (fun z ↦ (tensorPowModuleAddIso X N p (b + c)).hom ≫ z)
        (tensorPowModuleIsoOfIsoInt_congr N N' e
          (show p + (b + c) = p + b + c from by ring)))))
    (Stacks.AlgebraicGeometry.ThetaMul.absorb_iff _ _ _ _ _ _ _ (tensorPowModuleCongr_comp X N' _ _)
      (tensorPowModuleCongr_comp X N' _ _))

/-- **The upward induction step**: the bidegree `(n, i)` square and the `(·, 1)` columns at `n + i`
and at `i` give the bidegree `(n, i + 1)` square. -/
private theorem mul_succ_step (n i : ℤ)
    (ih : (tensorPowModuleAddIso X N n i).hom ≫
        (tensorPowModuleIsoOfIsoInt X N N' e (n + i)).hom =
      ((tensorPowModuleIsoOfIsoInt X N N' e n).hom ⊗ₘ
          (tensorPowModuleIsoOfIsoInt X N N' e i).hom) ≫
        (tensorPowModuleAddIso X N' n i).hom)
    (h1 : (tensorPowModuleAddIso X N (n + i) 1).hom ≫
        (tensorPowModuleIsoOfIsoInt X N N' e (n + i + 1)).hom =
      ((tensorPowModuleIsoOfIsoInt X N N' e (n + i)).hom ⊗ₘ
          (tensorPowModuleIsoOfIsoInt X N N' e 1).hom) ≫
        (tensorPowModuleAddIso X N' (n + i) 1).hom)
    (h2 : (tensorPowModuleAddIso X N i 1).hom ≫
        (tensorPowModuleIsoOfIsoInt X N N' e (i + 1)).hom =
      ((tensorPowModuleIsoOfIsoInt X N N' e i).hom ⊗ₘ
          (tensorPowModuleIsoOfIsoInt X N N' e 1).hom) ≫
        (tensorPowModuleAddIso X N' i 1).hom) :
    (tensorPowModuleAddIso X N n (i + 1)).hom ≫
        (tensorPowModuleIsoOfIsoInt X N N' e (n + (i + 1))).hom =
      ((tensorPowModuleIsoOfIsoInt X N N' e n).hom ⊗ₘ
          (tensorPowModuleIsoOfIsoInt X N N' e (i + 1)).hom) ≫
        (tensorPowModuleAddIso X N' n (i + 1)).hom :=
  (tensorPowModuleIsoOfIsoInt_mul_corner_iff N N' e n i 1).mpr
    (square_step (tensorPowModuleAddIso_assoc_int X N n i 1)
      (tensorPowModuleAddIso_assoc_int X N' n i 1) ih h1 h2)

/-- **Multiplicativity in a bidegree of natural numbers**, at the integer spelling of the two
exponents.  The induction is on the second exponent, with the bidegree `(n, 0)` square as base case
and `Stacks.AlgebraicGeometry.ThetaMul.square_step` as step, fed with the associativity constraint
in the tridegree `(a, b, 1)` for each of `N` and `N'` and with the bidegree `(k, 1)` column. -/
theorem tensorPowModuleIsoOfIsoInt_mul_natCast (a : ℕ) : ∀ b : ℕ,
    (tensorPowModuleAddIso X N (a : ℤ) (b : ℤ)).hom ≫
        (tensorPowModuleIsoOfIsoInt X N N' e ((a : ℤ) + (b : ℤ))).hom =
      ((tensorPowModuleIsoOfIsoInt X N N' e (a : ℤ)).hom ⊗ₘ
          (tensorPowModuleIsoOfIsoInt X N N' e (b : ℤ)).hom) ≫
        (tensorPowModuleAddIso X N' (a : ℤ) (b : ℤ)).hom
  | 0 =>
      tensorPowModuleIsoOfIsoInt_mul_of_eq N N' e rfl
        (show (0 : ℤ) = ((0 : ℕ) : ℤ) from by omega)
        (tensorPowModuleIsoOfIsoInt_mul_zero N N' e (a : ℤ))
  | (b + 1) =>
      tensorPowModuleIsoOfIsoInt_mul_of_eq N N' e rfl
        (show (b : ℤ) + 1 = ((b + 1 : ℕ) : ℤ) from by push_cast; ring)
        (mul_succ_step N N' e (a : ℤ) (b : ℤ)
          (tensorPowModuleIsoOfIsoInt_mul_natCast a b)
          (tensorPowModuleIsoOfIsoInt_mul_of_eq N N' e
            (show ((a + b : ℕ) : ℤ) = (a : ℤ) + (b : ℤ) from by push_cast; ring) rfl
            (tensorPowModuleIsoOfIsoInt_mul_one_natCast N N' e (a + b)))
          (tensorPowModuleIsoOfIsoInt_mul_one_natCast N N' e b))

/-- **The characterising identity of the transport in a negative degree.**
`tensorPowModuleIsoOfIsoNegSucc` is
`Stacks.AlgebraicGeometry.ProjTwistTensorPow.isoOfTensorUnitIso` of the two inverse laws of
`N^{⊗ (k+1)}` carried by `N^{⊗ -(k+1)}` and by `N'^{⊗ -(k+1)}`, and
`Stacks.AlgebraicGeometry.TensorUnitInvLaw.isoOfTensorUnitIso_whiskerRight` says it carries the
second law back to the first. -/
private theorem negSucc_gate (k : ℕ) :
    (tensorPowModuleIsoOfIsoNegSucc X N N' e k).hom ▷
          tensorPowModule X N ((k + 1 : ℕ) : ℤ) ≫
        ((tensorModulesMapIso X (Iso.refl _)
              (tensorPowModuleIsoOfIso X N N' e (k + 1))).hom ≫
          (tensorPowModuleAddIso X N' (-((k + 1 : ℕ) : ℤ)) ((k + 1 : ℕ) : ℤ)).hom ≫
          (tensorPowModuleCongr X N'
            (show -((k + 1 : ℕ) : ℤ) + ((k + 1 : ℕ) : ℤ) = 0 from by ring)).hom ≫
          (tensorPowModuleZeroIso X N').hom) =
      (tensorPowModuleAddIso X N (-((k + 1 : ℕ) : ℤ)) ((k + 1 : ℕ) : ℤ)).hom ≫
        (tensorPowModuleCongr X N
          (show -((k + 1 : ℕ) : ℤ) + ((k + 1 : ℕ) : ℤ) = 0 from by ring)).hom ≫
        (tensorPowModuleZeroIso X N).hom :=
  Stacks.AlgebraicGeometry.TensorUnitInvLaw.isoOfTensorUnitIso_whiskerRight X _ _ _
    (tensorPowModuleAddIso X N (-((k + 1 : ℕ) : ℤ)) ((k + 1 : ℕ) : ℤ) ≪≫
      tensorPowModuleCongr X N
        (show -((k + 1 : ℕ) : ℤ) + ((k + 1 : ℕ) : ℤ) = 0 from by ring) ≪≫
      tensorPowModuleZeroIso X N)
    (tensorModulesMapIso X (Iso.refl _) (tensorPowModuleIsoOfIso X N N' e (k + 1)) ≪≫
      tensorPowModuleAddIso X N' (-((k + 1 : ℕ) : ℤ)) ((k + 1 : ℕ) : ℤ) ≪≫
      tensorPowModuleCongr X N'
        (show -((k + 1 : ℕ) : ℤ) + ((k + 1 : ℕ) : ℤ) = 0 from by ring) ≪≫
      tensorPowModuleZeroIso X N')

/-- **The inverse-law square for the transport**, in the bidegree `(-(k+1), k+1)`: the transports
in the two degrees, tensored together, carry the inverse law of the powers of `N` to the inverse
law of the powers of `N'`.  This is the one face of the multiplicativity statement that no
arrangement of `Stacks.AlgebraicGeometry.ThetaMul.square_step` and
`Stacks.Monoidal.square_step_left` reaches from the nonnegative degrees. -/
theorem tensorPowModuleIsoOfIsoInt_mul_neg_succ (k : ℕ) :
    (tensorPowModuleAddIso X N (-((k + 1 : ℕ) : ℤ)) ((k + 1 : ℕ) : ℤ)).hom ≫
        (tensorPowModuleIsoOfIsoInt X N N' e
          (-((k + 1 : ℕ) : ℤ) + ((k + 1 : ℕ) : ℤ))).hom =
      ((tensorPowModuleIsoOfIsoInt X N N' e (-((k + 1 : ℕ) : ℤ))).hom ⊗ₘ
          (tensorPowModuleIsoOfIsoInt X N N' e ((k + 1 : ℕ) : ℤ)).hom) ≫
        (tensorPowModuleAddIso X N' (-((k + 1 : ℕ) : ℤ)) ((k + 1 : ℕ) : ℤ)).hom := by
  have hgate : ((tensorPowModuleIsoOfIsoInt X N N' e (-((k + 1 : ℕ) : ℤ))).hom ⊗ₘ
        (tensorPowModuleIsoOfIsoInt X N N' e ((k + 1 : ℕ) : ℤ)).hom) ≫
      ((tensorPowModuleAddIso X N' (-((k + 1 : ℕ) : ℤ)) ((k + 1 : ℕ) : ℤ)).hom ≫
        (tensorPowModuleCongr X N'
          (show -((k + 1 : ℕ) : ℤ) + ((k + 1 : ℕ) : ℤ) = 0 from by ring)).hom ≫
        (tensorPowModuleZeroIso X N').hom) =
      (tensorPowModuleAddIso X N (-((k + 1 : ℕ) : ℤ)) ((k + 1 : ℕ) : ℤ)).hom ≫
        (tensorPowModuleCongr X N
          (show -((k + 1 : ℕ) : ℤ) + ((k + 1 : ℕ) : ℤ) = 0 from by ring)).hom ≫
        (tensorPowModuleZeroIso X N).hom := by
    rw [tensorPowModuleIsoOfIsoInt_negSucc, tensorPowModuleIsoOfIsoInt_natCast]
    refine whisker_to_tensorHom _ _ _ _ ?_
    have h := negSucc_gate N N' e k
    rw [Stacks.AlgebraicGeometry.ThetaMul.tensorModulesMapIso_hom, Iso.refl_hom,
      MonoidalCategory.id_tensorHom] at h
    exact h
  rw [tensorPowModuleIsoOfIsoInt_congr N N' e
      (show -((k + 1 : ℕ) : ℤ) + ((k + 1 : ℕ) : ℤ) = 0 from by ring),
    tensorPowModuleIsoOfIsoInt_zero]
  exact inv_law_square_free _ _ _ _ _ _ _ _ _ hgate
    (tensorPowModuleZeroIso X N').hom_inv_id (tensorPowModuleCongr_comp X N' _ _)

/-- **The inverse-law square at every bidegree summing to zero with a nonnegative second
exponent.**  In the degree zero it is the right unit law
`tensorPowModuleIsoOfIsoInt_mul_zero`, and otherwise it is
`tensorPowModuleIsoOfIsoInt_mul_neg_succ`. -/
theorem tensorPowModuleIsoOfIsoInt_mul_add_eq_zero (p q : ℤ) (hq : 0 ≤ q) (hpq : p + q = 0) :
    (tensorPowModuleAddIso X N p q).hom ≫
        (tensorPowModuleIsoOfIsoInt X N N' e (p + q)).hom =
      ((tensorPowModuleIsoOfIsoInt X N N' e p).hom ⊗ₘ
          (tensorPowModuleIsoOfIsoInt X N N' e q).hom) ≫
        (tensorPowModuleAddIso X N' p q).hom := by
  obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hq
  cases j with
  | zero =>
      exact tensorPowModuleIsoOfIsoInt_mul_of_eq N N' e (show (0 : ℤ) = p from by omega)
        (show (0 : ℤ) = ((0 : ℕ) : ℤ) from by omega)
        (tensorPowModuleIsoOfIsoInt_mul_zero N N' e 0)
  | succ i =>
      exact tensorPowModuleIsoOfIsoInt_mul_of_eq N N' e
        (show -(((i + 1 : ℕ)) : ℤ) = p from by omega) rfl
        (tensorPowModuleIsoOfIsoInt_mul_neg_succ N N' e i)

/-- **Multiplicativity in the bidegree `(k, 1)` for an arbitrary integer `k`.**  In a nonnegative
degree this is `tensorPowModuleIsoOfIsoInt_mul_one_natCast`.  In a negative degree `k = -(a+1)` it
is `Stacks.Monoidal.square_step_left` applied to the associativity diagram in the tridegree
`(-(a+1), 1, a)`, whose other three squares are the two inverse-law squares at `(-a, a)` and at
`(-(a+1), a+1)` and the natural-number square at `(1, a)`. -/
theorem tensorPowModuleIsoOfIsoInt_mul_one (k : ℤ) :
    (tensorPowModuleAddIso X N k 1).hom ≫
        (tensorPowModuleIsoOfIsoInt X N N' e (k + 1)).hom =
      ((tensorPowModuleIsoOfIsoInt X N N' e k).hom ⊗ₘ
          (tensorPowModuleIsoOfIsoInt X N N' e 1).hom) ≫
        (tensorPowModuleAddIso X N' k 1).hom := by
  by_cases hk : 0 ≤ k
  · obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    exact tensorPowModuleIsoOfIsoInt_mul_one_natCast N N' e j
  · obtain ⟨a, rfl⟩ : ∃ a : ℕ, k = -((a : ℤ) + 1) := ⟨(-k - 1).toNat, by omega⟩
    exact Stacks.Monoidal.square_step_left_of_mono
      (Stacks.Monoidal.mono_iso_hom (tensorPowModuleAddIso X N' (-((a : ℤ) + 1) + 1) (a : ℤ)))
      (tensorPowModuleInvIsoRight X N (a : ℤ))
      (tensorPowModuleAddIso_assoc_int X N (-((a : ℤ) + 1)) 1 (a : ℤ))
      (tensorPowModuleAddIso_assoc_int X N' (-((a : ℤ) + 1)) 1 (a : ℤ))
      (tensorPowModuleIsoOfIsoInt_mul_add_eq_zero N N' e (-((a : ℤ) + 1) + 1) (a : ℤ)
        (by omega) (by ring))
      (tensorPowModuleIsoOfIsoInt_mul_of_eq N N' e
        (show (((1 : ℕ)) : ℤ) = 1 from by omega) rfl
        (tensorPowModuleIsoOfIsoInt_mul_natCast N N' e 1 a))
      ((tensorPowModuleIsoOfIsoInt_mul_corner_iff N N' e (-((a : ℤ) + 1)) 1 (a : ℤ)).mp
        (tensorPowModuleIsoOfIsoInt_mul_add_eq_zero N N' e (-((a : ℤ) + 1)) (1 + (a : ℤ))
          (by omega) (by ring)))

/-- **Multiplicativity of the transport of the integer tensor powers along an isomorphism of
invertible `𝒪_X`-modules, in an arbitrary integer bidegree**: the addition law
`Stacks.Ample.tensorPowModuleAddIso` of the powers of `N` at `(n, m)`, followed by the transport in
the degree `n + m`, is the transports in the degrees `n` and `m` on the two factors, followed by
the addition law of the powers of `N'`.  Both degrees are arbitrary integers.

This is the statement that makes
`Stacks.AlgebraicGeometry.HyperplaneTwistSequence.tensorPowModuleIsoOfIsoInt` an isomorphism of
`ℤ`-graded `𝒪_X`-algebras `⨁_{n ∈ ℤ} N^{⊗ n} ≅ ⨁_{n ∈ ℤ} N'^{⊗ n}` rather than a degreewise family
of isomorphisms.

The induction is over `ℤ` in the second degree, with the bidegree `(n, 0)` square as base case,
`Stacks.AlgebraicGeometry.ThetaMul.square_step` upwards and `Stacks.Monoidal.square_step_left`
downwards, both fed with `Stacks.AlgebraicGeometry.ThetaMul.tensorPowModuleAddIso_assoc_int` in the
tridegree `(n, m, 1)` for each of `N` and `N'` and with the bidegree `(k, 1)` column
`tensorPowModuleIsoOfIsoInt_mul_one`. -/
theorem tensorPowModuleIsoOfIsoInt_mul (n m : ℤ) :
    (tensorPowModuleAddIso X N n m).hom ≫
        (tensorPowModuleIsoOfIsoInt X N N' e (n + m)).hom =
      ((tensorPowModuleIsoOfIsoInt X N N' e n).hom ⊗ₘ
          (tensorPowModuleIsoOfIsoInt X N N' e m).hom) ≫
        (tensorPowModuleAddIso X N' n m).hom := by
  induction m using Int.induction_on with
  | zero => exact tensorPowModuleIsoOfIsoInt_mul_zero N N' e n
  | succ i ih =>
      exact mul_succ_step N N' e n (i : ℤ) ih
        (tensorPowModuleIsoOfIsoInt_mul_one N N' e (n + (i : ℤ)))
        (tensorPowModuleIsoOfIsoInt_mul_one N N' e (i : ℤ))
  | pred i ih =>
      exact Stacks.Monoidal.square_step_left_of_mono
        (Stacks.Monoidal.mono_iso_hom (tensorPowModuleAddIso X N' (n + (-(i : ℤ) - 1)) 1))
        (tensorPowModuleInvIsoRight X N 1)
        (tensorPowModuleAddIso_assoc_int X N n (-(i : ℤ) - 1) 1)
        (tensorPowModuleAddIso_assoc_int X N' n (-(i : ℤ) - 1) 1)
        (tensorPowModuleIsoOfIsoInt_mul_one N N' e (n + (-(i : ℤ) - 1)))
        (tensorPowModuleIsoOfIsoInt_mul_one N N' e (-(i : ℤ) - 1))
        ((tensorPowModuleIsoOfIsoInt_mul_corner_iff N N' e n (-(i : ℤ) - 1) 1).mp
          (tensorPowModuleIsoOfIsoInt_mul_of_eq N N' e rfl
            (show -(i : ℤ) = -(i : ℤ) - 1 + 1 from by omega) ih))

end Stacks.AlgebraicGeometry.TensorPowCongrInt

end
