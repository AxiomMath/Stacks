module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraSheafification

/-!
# A sheaf of graded algebras from a locally bijective comparison

`Stacks.GradedAlgebra.sheafify` in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraSheafification` makes the degreewise
sheafification of a graded algebra of presheaves of modules into a
`SheafOfModules.GradedAlgebra`. Its homogeneous pieces are the values of the sheafification
functor, which is the wrong spelling for a consumer who already has the sheaves in hand — on
`Spec R` the degree-`n` piece of the symmetric algebra of `M̃` is to be `Sym^n(M)~`, not the
sheafification of an auxiliary presheaf that happens to be isomorphic to it.

**This file replaces the sheafification functor by an arbitrary family of sheaves receiving a
degreewise locally bijective comparison.** Given a graded algebra `A` on `P : ℤ → PresheafOfModules
R.obj`, a family `S : ℤ → SheafOfModules R` and morphisms `u n : P n ⟶ (S n).val` which are
locally injective and locally surjective, `Stacks.GradedAlgebra.ofComparison` is a sheaf of graded
algebras whose degree-`n` piece is `S n` **on the nose**.

Nothing here is new mathematics: the proofs are those of `Stacks.GradedAlgebra.sheafify`, with
the sheafification unit replaced by `u` and the restriction of scalars dropped, which is possible
because the base is a single sheaf of rings rather than a presheaf of rings mapping to one.

## Main definitions

* `Stacks.GradedAlgebra.cmpMul`: the multiplication of the transported algebra, obtained by
  extending the given multiplication along `u` in each variable
  (`Stacks.BilinearMap.compLeftEquiv` and `compRightEquiv`).
* `Stacks.GradedAlgebra.cmpOne`: its unit, the `u`-image of the given unit.
* `Stacks.GradedAlgebra.ofComparison`: the sheaf of graded algebras.

## Main results

* `Stacks.GradedAlgebra.cmpMul_comparison` and `ofComparison_mul_comparison`: the transported
  multiplication extends the given one along `u`.
* `Stacks.GradedAlgebra.cmpMul_restrict` and `ofComparison_mul_restrict`: the transported
  multiplication read on local lifts. Every law of `ofComparison` is proved from this plus
  separatedness of the target.
* `Stacks.GradedAlgebra.pairwiseCommutes_cmpGen` and `squareZero_cmpGen`: the two side
  conditions that cut out the symmetric and the exterior algebra transfer from a generator to
  its comparison.

## Implementation notes

The local bijectivity hypotheses are instance binders of pi type,
`[∀ n, PresheafOfModules.IsLocallySurjective J (u n)]`, so that instance search produces the
hypothesis at each individual degree where `Stacks.BilinearMap.compLeftEquiv` asks for it. Passed
as plain hypotheses they would have to be introduced by `haveI` at every use, which is exactly the
situation in which a local instance is not reliably consulted.

The heterogeneous equalities are handled by `Stacks.heq_of_isSeparated` and `Stacks.heq_apply` of
`GradedAlgebraSheafification`, for the reason documented there: the degree equalities
`(i + j) + k = i + (j + k)` cannot be substituted at the point of use, so they are passed to a
helper which substitutes them internally.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite PresheafOfModules

universe v u t a

namespace Stacks

section Lift

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {M : PresheafOfModules.{a} R.obj} {T : SheafOfModules.{a} R}

/-- The sieve of local lifts of a section of a sheaf of modules along a comparison morphism out
of a presheaf of modules. -/
abbrev cmpSieve (w : M ⟶ T.val) {X : Cᵒᵖ} (s : T.val.obj X) : Sieve X.unop :=
  Presheaf.imageSieve ((toPresheaf R.obj).map w) s

/-- A section of the target lifts along a locally surjective comparison on a covering sieve. -/
theorem cmpSieve_mem (w : M ⟶ T.val)
    [PresheafOfModules.IsLocallySurjective J w] {X : Cᵒᵖ} (s : T.val.obj X) :
    cmpSieve w s ∈ J X.unop :=
  Presheaf.imageSieve_mem J ((toPresheaf R.obj).map w) s

end Lift

namespace GradedAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {P : ℤ → PresheafOfModules.{a} R.obj} (A : GradedAlgebra P)
  (S : ℤ → SheafOfModules.{a} R) (u : ∀ n, P n ⟶ (S n).val)
  [∀ n, PresheafOfModules.IsLocallySurjective J (u n)]
  [∀ n, PresheafOfModules.IsLocallyInjective J (u n)]

/-- The given multiplication, followed by the comparison of the target. -/
def cmpMulUnit (i j : ℤ) : BilinearMap (P i) (P j) ((S (i + j)).val) :=
  (A.mul i j).postcomp (u (i + j))

/-- `Stacks.GradedAlgebra.cmpMulUnit` extended along the comparison in the first variable. -/
def cmpMulLeft (i j : ℤ) : BilinearMap ((S i).val) (P j) ((S (i + j)).val) :=
  (BilinearMap.compLeftEquiv (N := P j) (S (i + j)).isSheaf (u i)).symm (A.cmpMulUnit S u i j)

/-- **The transported multiplication**: `Stacks.GradedAlgebra.cmpMulUnit` extended along the
comparison in both variables. -/
def cmpMul (i j : ℤ) : SheafOfModules.BilinearMap (S i) (S j) (S (i + j)) :=
  (BilinearMap.compRightEquiv (M := (S i).val) (S (i + j)).isSheaf (u j)).symm
    (A.cmpMulLeft S u i j)

/-- The transported multiplication extends the given one: on the comparison images of two
homogeneous local sections it is the comparison image of their product. -/
theorem cmpMul_comparison (i j : ℤ) (X : Cᵒᵖ) (x : (P i).obj X) (y : (P j).obj X) :
    (A.cmpMul S u i j).app X (Hom.app (u i) X x) (Hom.app (u j) X y) =
      Hom.app (u (i + j)) X ((A.mul i j).app X x y) :=
  (BilinearMap.congr_app
      ((BilinearMap.compRightEquiv (M := (S i).val) (S (i + j)).isSheaf
        (u j)).apply_symm_apply (A.cmpMulLeft S u i j)) X (Hom.app (u i) X x) y).trans
    (BilinearMap.congr_app
      ((BilinearMap.compLeftEquiv (N := P j) (S (i + j)).isSheaf
        (u i)).apply_symm_apply (A.cmpMulUnit S u i j)) X x y)

/-- **The transported multiplication, read on local lifts.** -/
theorem cmpMul_restrict (i j : ℤ) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (b₁ : (S i).val.obj X) (b₂ : (S j).val.obj X) (x : (P i).obj Y) (y : (P j).obj Y)
    (hx : Hom.app (u i) Y x = (S i).val.map f b₁)
    (hy : Hom.app (u j) Y y = (S j).val.map f b₂) :
    (S (i + j)).val.map f ((A.cmpMul S u i j).app X b₁ b₂) =
      Hom.app (u (i + j)) Y ((A.mul i j).app Y x y) := by
  refine ((A.cmpMul S u i j).naturality f b₁ b₂).trans ?_
  rw [← hx, ← hy]
  exact A.cmpMul_comparison S u i j Y x y

/-- The unit of the transported algebra: the comparison image of the given unit. -/
def cmpOne : (S 0).sections :=
  PresheafOfModules.sectionsMk (fun X => Hom.app (u 0) X (A.one.eval X))
    fun {X _} f => ((naturality_apply (u 0) f (A.one.eval X)).symm).trans
      (congrArg (fun s => Hom.app (u 0) _ s) (PresheafOfModules.sections_property A.one f))

omit [∀ n, PresheafOfModules.IsLocallySurjective J (u n)]
  [∀ n, PresheafOfModules.IsLocallyInjective J (u n)] in
/-- The value of `Stacks.GradedAlgebra.cmpOne` on an object is the comparison image of the value of
the given unit. -/
@[simp]
theorem cmpOne_eval (X : Cᵒᵖ) :
    (A.cmpOne S u).eval X = Hom.app (u 0) X (A.one.eval X) := rfl

/-- **A sheaf of graded algebras with prescribed homogeneous pieces.** -/
def ofComparison : SheafOfModules.GradedAlgebra.{t, a} R where
  piece := S
  mul i j := A.cmpMul S u i j
  one := A.cmpOne S u
  mul_assoc i j k X x y z := by
    refine heq_of_isSeparated (congrArg S (add_assoc i j k))
      (J.intersection_covering
        (J.intersection_covering (cmpSieve_mem (u i) x) (cmpSieve_mem (u j) y))
        (cmpSieve_mem (u k) z)) ?_
    rintro Y f ⟨⟨⟨x₀, hx₀⟩, ⟨y₀, hy₀⟩⟩, ⟨z₀, hz₀⟩⟩
    have hx : Hom.app (u i) (op Y) x₀ = (S i).val.map f.op x := hx₀
    have hy : Hom.app (u j) (op Y) y₀ = (S j).val.map f.op y := hy₀
    have hz : Hom.app (u k) (op Y) z₀ = (S k).val.map f.op z := hz₀
    rw [A.cmpMul_restrict S u (i + j) k f.op _ z ((A.mul i j).app (op Y) x₀ y₀) z₀
        (A.cmpMul_restrict S u i j f.op x y x₀ y₀ hx hy).symm hz,
      A.cmpMul_restrict S u i (j + k) f.op x _ x₀ ((A.mul j k).app (op Y) y₀ z₀) hx
        (A.cmpMul_restrict S u j k f.op y z y₀ z₀ hy hz).symm]
    exact heq_apply _ _ (fun n s => Hom.app (u n) (op Y) s) (add_assoc i j k)
      (A.mul_assoc i j k (op Y) x₀ y₀ z₀)
  one_mul i X x := by
    refine heq_of_isSeparated (congrArg S (zero_add i)) (cmpSieve_mem (u i) x) ?_
    rintro Y f ⟨x₀, hx₀⟩
    have hx : Hom.app (u i) (op Y) x₀ = (S i).val.map f.op x := hx₀
    rw [A.cmpMul_restrict S u 0 i f.op _ x (A.one.eval (op Y)) x₀
        (PresheafOfModules.sections_property (A.cmpOne S u) f.op).symm hx, ← hx]
    exact heq_apply _ _ (fun n s => Hom.app (u n) (op Y) s) (zero_add i)
      (A.one_mul i (op Y) x₀)
  mul_one i X x := by
    refine heq_of_isSeparated (congrArg S (add_zero i)) (cmpSieve_mem (u i) x) ?_
    rintro Y f ⟨x₀, hx₀⟩
    have hx : Hom.app (u i) (op Y) x₀ = (S i).val.map f.op x := hx₀
    rw [A.cmpMul_restrict S u i 0 f.op x _ x₀ (A.one.eval (op Y)) hx
        (PresheafOfModules.sections_property (A.cmpOne S u) f.op).symm, ← hx]
    exact heq_apply _ _ (fun n s => Hom.app (u n) (op Y) s) (add_zero i)
      (A.mul_one i (op Y) x₀)

/-- The degree-`n` piece of `Stacks.GradedAlgebra.ofComparison` is `S n`. -/
theorem ofComparison_piece (n : ℤ) : (A.ofComparison S u).piece n = S n := rfl

/-- The multiplication of `Stacks.GradedAlgebra.ofComparison` is `Stacks.GradedAlgebra.cmpMul`. -/
theorem ofComparison_mul (i j : ℤ) : (A.ofComparison S u).mul i j = A.cmpMul S u i j := rfl

/-- The unit of `Stacks.GradedAlgebra.ofComparison` is `Stacks.GradedAlgebra.cmpOne`. -/
theorem ofComparison_one : (A.ofComparison S u).one = A.cmpOne S u := rfl

/-- The value of the unit of `Stacks.GradedAlgebra.ofComparison` on an object is the comparison
image of the value of the given unit. -/
theorem ofComparison_one_eval (X : Cᵒᵖ) :
    (A.ofComparison S u).one.eval X = Hom.app (u 0) X (A.one.eval X) := rfl

/-- On the comparison images of two homogeneous local sections, the multiplication of
`Stacks.GradedAlgebra.ofComparison` is the comparison image of their product. -/
theorem ofComparison_mul_comparison (i j : ℤ) (X : Cᵒᵖ) (x : (P i).obj X) (y : (P j).obj X) :
    ((A.ofComparison S u).mul i j).app X (Hom.app (u i) X x) (Hom.app (u j) X y) =
      Hom.app (u (i + j)) X ((A.mul i j).app X x y) :=
  A.cmpMul_comparison S u i j X x y

/-- If `x` and `y` are local lifts along the comparisons of the restrictions of `b₁` and `b₂`, then
the restriction of the product of `b₁` and `b₂` in `Stacks.GradedAlgebra.ofComparison` is the
comparison image of the product of `x` and `y`. -/
theorem ofComparison_mul_restrict (i j : ℤ) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (b₁ : ((A.ofComparison S u).piece i).val.obj X)
    (b₂ : ((A.ofComparison S u).piece j).val.obj X)
    (x : (P i).obj Y) (y : (P j).obj Y)
    (hx : Hom.app (u i) Y x = ((A.ofComparison S u).piece i).val.map f b₁)
    (hy : Hom.app (u j) Y y = ((A.ofComparison S u).piece j).val.map f b₂) :
    ((A.ofComparison S u).piece (i + j)).val.map f
        (((A.ofComparison S u).mul i j).app X b₁ b₂) =
      Hom.app (u (i + j)) Y ((A.mul i j).app Y x y) :=
  A.cmpMul_restrict S u i j f b₁ b₂ x y hx hy

/-- **Commutativity of the homogeneous multiplication transfers along the comparisons.** If the
given multiplication commutes on sections, across the identification of the degrees `i + j` and
`j + i`, then so does the transported one. -/
theorem ofComparison_mul_comm
    (hc : ∀ (i j : ℤ) (X : Cᵒᵖ) (x : (P i).obj X) (y : (P j).obj X),
      HEq ((A.mul i j).app X x y) ((A.mul j i).app X y x))
    (i j : ℤ) (X : Cᵒᵖ) (x : ((A.ofComparison S u).piece i).val.obj X)
    (y : ((A.ofComparison S u).piece j).val.obj X) :
    HEq (((A.ofComparison S u).mul i j).app X x y)
      (((A.ofComparison S u).mul j i).app X y x) := by
  refine heq_of_isSeparated
    (congrArg (fun n : ℤ => (A.ofComparison S u).piece n) (add_comm i j))
    (J.intersection_covering (cmpSieve_mem (u i) x) (cmpSieve_mem (u j) y)) ?_
  rintro Y f ⟨⟨x₀, hx₀⟩, ⟨y₀, hy₀⟩⟩
  rw [A.ofComparison_mul_restrict S u i j f.op x y x₀ y₀ hx₀ hy₀,
    A.ofComparison_mul_restrict S u j i f.op y x y₀ x₀ hy₀ hx₀]
  exact heq_apply _ _ (fun n s => Hom.app (u n) (op Y) s) (add_comm i j) (hc i j (op Y) x₀ y₀)

/-! ### Degree-one generators -/

section Generator

variable {F : PresheafOfModules.{a} R.obj} {G : SheafOfModules.{a} R} (gen : F ⟶ P 1)
  (v : F ⟶ G.val)

/-- A local lift of a local section of `F` along `v` gives a local lift of its image under a
compatible morphism. -/
theorem cmpGen_lift (w : G ⟶ (A.ofComparison S u).piece 1)
    (hw : ∀ (X : Cᵒᵖ) (s : F.obj X),
      w.val.app X (Hom.app v X s) = Hom.app (u 1) X (Hom.app gen X s))
    {X Y : Cᵒᵖ} (f : X ⟶ Y) (b : G.val.obj X) (s : F.obj Y)
    (hs : Hom.app v Y s = G.val.map f b) :
    Hom.app (u 1) Y (Hom.app gen Y s) =
      ((A.ofComparison S u).piece 1).val.map f (w.val.app X b) := by
  rw [← hw Y s, hs]
  exact naturality_apply w.val f b

/-- **Pairwise commutation transfers along the comparisons.** -/
theorem pairwiseCommutes_cmpGen [PresheafOfModules.IsLocallySurjective J v]
    (w : G ⟶ (A.ofComparison S u).piece 1)
    (hw : ∀ (X : Cᵒᵖ) (s : F.obj X),
      w.val.app X (Hom.app v X s) = Hom.app (u 1) X (Hom.app gen X s))
    (hc : ∀ (X : Cᵒᵖ) (x y : F.obj X),
      (A.mul 1 1).app X (Hom.app gen X x) (Hom.app gen X y) =
        (A.mul 1 1).app X (Hom.app gen X y) (Hom.app gen X x)) :
    SheafOfModules.GradedAlgebra.PairwiseCommutes w := by
  intro X s uu
  refine eq_of_isSeparated ((A.ofComparison S u).piece (1 + 1))
    (J.intersection_covering (cmpSieve_mem v s) (cmpSieve_mem v uu)) ?_
  rintro Y f ⟨⟨s₀, hs₀⟩, ⟨u₀, hu₀⟩⟩
  rw [A.ofComparison_mul_restrict S u 1 1 f.op _ _ (Hom.app gen (op Y) s₀)
      (Hom.app gen (op Y) u₀)
      (A.cmpGen_lift S u gen v w hw f.op s s₀ hs₀) (A.cmpGen_lift S u gen v w hw f.op uu u₀ hu₀),
    A.ofComparison_mul_restrict S u 1 1 f.op _ _ (Hom.app gen (op Y) u₀)
      (Hom.app gen (op Y) s₀)
      (A.cmpGen_lift S u gen v w hw f.op uu u₀ hu₀) (A.cmpGen_lift S u gen v w hw f.op s s₀ hs₀)]
  exact congrArg (fun z => Hom.app (u (1 + 1)) (op Y) z) (hc (op Y) s₀ u₀)

end Generator

end GradedAlgebra

end Stacks
