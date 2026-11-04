module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UngradedRealizationModule
public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.GradedPullback
public import StacksFrontier.AlgebraicGeometry.AffineGradedAlgebra.Basic

/-!
# `𝓑 = f^* B̃`, the sheaf of graded algebras of [Stacks, Tag 0897]

Let `A` be a commutative ring, `B` a graded `A`-algebra with grading `𝒜 : ℕ → Submodule A B` and
`f : X ⟶ Spec A` a morphism of schemes. [Stacks, Tag 0897] works with the sheaf of graded
`𝒪_X`-algebras `𝓑 = f^* B̃`, where `B̃` is the quasi-coherent sheaf of graded algebras on `Spec A`
attached to `B`. This file constructs `𝓑` from `Stacks.SpecGraded.specGradedAlgebra` on `Spec A`
and `Stacks.Conormal.gradedPullback` along `f`, and shows that its homogeneous multiplication is
commutative, its pieces are quasi-coherent, and it vanishes in negative degrees.

The grading of `B` is indexed by `ℕ`, as in the source, while a `SheafOfModules.GradedAlgebra` is
`ℤ`-graded; `Stacks.AlgebraicGeometry.GradedProperCohomology.intExtend` extends the grading by
the zero submodule in negative degrees, so that `B̃` is concentrated in nonnegative degrees.

## Main definitions

* `Stacks.AlgebraicGeometry.GradedProperCohomology.intExtend`: the `ℤ`-extension of an
  `ℕ`-indexed grading.
* `Stacks.AlgebraicGeometry.GradedProperCohomology.specGradedAlg`: **`B̃`**, on `Spec A`.
* `Stacks.AlgebraicGeometry.GradedProperCohomology.pullbackGradedAlg`: **`𝓑 = f^* B̃`**, on `X`.

## Main results

* `isZero_pullbackGradedAlg_piece_of_neg` and
  `isQuasicoherent_pullbackGradedAlg_piece`: `𝓑` vanishes in negative degrees and its pieces are
  quasi-coherent.
* `isCommutative_pullbackGradedAlg`: the homogeneous multiplication of `𝓑` is commutative.

These three properties are what make the relative spectrum `Spec_X(𝓑)` exist.

## References

* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped TensorProduct

universe u

namespace Stacks.AlgebraicGeometry.GradedProperCohomology

variable {A : Type u} [CommRing A] {B : Type u} [CommRing B] [Algebra A B]

/-- **The `ℤ`-extension of an `ℕ`-indexed grading**: the given submodule in nonnegative degrees
and the zero submodule in negative ones. It is defined by a match on `Int`, so that its value at
a natural number is the given submodule by `rfl`. -/
def intExtend (𝒜 : ℕ → Submodule A B) : ℤ → Submodule A B
  | .ofNat n => 𝒜 n
  | .negSucc _ => ⊥

variable (𝒜 : ℕ → Submodule A B)

/-- The `ℤ`-extension of a grading is the zero submodule in negative degrees. -/
theorem intExtend_neg {n : ℤ} (hn : n < 0) : intExtend 𝒜 n = ⊥ := by
  match n with
  | .ofNat k => exact absurd hn (not_lt.mpr (Int.natCast_nonneg k))
  | .negSucc k => rfl

variable [_root_.GradedAlgebra 𝒜]

/-- The `ℤ`-extension of a grading of an algebra is again multiplicative and unital. -/
instance instGradedMonoidIntExtend : SetLike.GradedMonoid (intExtend 𝒜) where
  one_mem := SetLike.one_mem_graded 𝒜
  mul_mem := by
    intro i j x y hx hy
    match i, j with
    | .ofNat a, .ofNat b => exact SetLike.mul_mem_graded (A := 𝒜) hx hy
    | .ofNat _, .negSucc _ =>
        rw [show y = 0 from (Submodule.mem_bot A).1 hy, mul_zero]
        exact Submodule.zero_mem _
    | .negSucc _, _ =>
        rw [show x = 0 from (Submodule.mem_bot A).1 hx, zero_mul]
        exact Submodule.zero_mem _

/-- **`B̃`**, the sheaf of graded `𝒪_{Spec A}`-algebras attached to the graded `A`-algebra `B`:
its degree-`n` homogeneous piece is the associated sheaf of `𝒜ₙ`. -/
def specGradedAlg : _root_.SheafOfModules.GradedAlgebra.{u, u} (Spec (.of A)).ringCatSheaf :=
  Stacks.SpecGraded.specGradedAlgebra (R := CommRingCat.of A) (S := B) (intExtend 𝒜)

/-- `B̃` vanishes in negative degrees. -/
theorem isZero_specGradedAlg_piece_of_neg {n : ℤ} (hn : n < 0) :
    IsZero ((specGradedAlg 𝒜).piece n) :=
  Stacks.SpecGraded.isZero_specGradedAlgebra_piece (R := CommRingCat.of A) (S := B)
    (intExtend 𝒜) (intExtend_neg 𝒜 hn)

/-! ### The global section named by a homogeneous element -/

/-- **The global section of `B̃ₖ` named by a homogeneous element of degree `k` of `B`.** -/
abbrev specSection {k : ℕ} (b : ↥(𝒜 k)) : ((specGradedAlg 𝒜).piece (k : ℤ)).val.sections :=
  Stacks.SpecGraded.homogeneousSection (R := CommRingCat.of A) (S := B) (intExtend 𝒜) b

/-! ### Pulling a global section back -/

/-- Restricting the pullback of a section is the pullback of that section to the smaller open. -/
theorem pullbackSection_restrict {Z Y : Scheme.{u}} (g : Z ⟶ Y) (N : Y.Modules) (U : Y.Opens)
    {V W : Z.Opens} (hV : V ≤ g ⁻¹ᵁ U) (hWV : W ≤ V) (a : N.val.obj (op U)) :
    (((Scheme.Modules.pullback g).obj N).val.map (homOfLE hWV).op)
        (Scheme.Modules.pullbackSection g N U V hV a) =
      Scheme.Modules.pullbackSection g N U W (hWV.trans hV) a := by
  exact (PresheafOfModules.map_comp_apply ((Scheme.Modules.pullback g).obj N).val
    (homOfLE hV).op (homOfLE hWV).op _).symm

/-- **A global section of a module pulls back to a global section of its pullback.** -/
def pullbackSections {Z Y : Scheme.{u}} (g : Z ⟶ Y) (N : Y.Modules) (s : N.val.sections) :
    ((Scheme.Modules.pullback g).obj N).val.sections :=
  PresheafOfModules.sectionsMk
    (fun V => Scheme.Modules.pullbackSection g N ⊤ V.unop le_top (s.eval (op ⊤)))
    (fun {V W} h => by
      refine Eq.trans ?_ (pullbackSection_restrict g N ⊤ (le_top (a := V.unop))
        (leOfHom h.unop) (s.eval (op ⊤)))
      exact congrArg (fun φ : V ⟶ W => (((Scheme.Modules.pullback g).obj N).val.map φ)
          (Scheme.Modules.pullbackSection g N ⊤ V.unop le_top (s.eval (op ⊤))))
        (Subsingleton.elim h (homOfLE (leOfHom h.unop)).op))

/-- The value of the pulled-back global section on an open `V` is the pullback to `V` of the
value of the section on `⊤`. -/
theorem pullbackSections_eval {Z Y : Scheme.{u}} (g : Z ⟶ Y) (N : Y.Modules)
    (s : N.val.sections) (V : (Opens ↥Z)ᵒᵖ) :
    (pullbackSections g N s).eval V =
      Scheme.Modules.pullbackSection g N ⊤ V.unop le_top (s.eval (op ⊤)) := rfl

/-- Pulling a section back is additive in the section. -/
theorem pullbackSection_add {Z Y : Scheme.{u}} (g : Z ⟶ Y) (N : Y.Modules) (U : Y.Opens)
    {V : Z.Opens} (hV : V ≤ g ⁻¹ᵁ U) (a a' : N.val.obj (op U)) :
    Scheme.Modules.pullbackSection g N U V hV (a + a') =
      Scheme.Modules.pullbackSection g N U V hV a +
        Scheme.Modules.pullbackSection g N U V hV a' := by
  show (((Scheme.Modules.pullback g).obj N).val.map (homOfLE hV).op).hom
      ((((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app N).val.app (op U)).hom
        (a + a')) = _
  rw [map_add]
  exact map_add (((Scheme.Modules.pullback g).obj N).val.map (homOfLE hV).op).hom _ _

/-- **Transport along an equality of degrees commutes with pulling a section back.** -/
theorem castHom_pullbackSection {Z Y : Scheme.{u}} (g : Z ⟶ Y) (N : ℤ → Y.Modules)
    {d d' : ℤ} (h : d = d') (U : Y.Opens) {V : Z.Opens} (hV : V ≤ g ⁻¹ᵁ U)
    (z : (N d).val.obj (op U)) :
    _root_.SheafOfModules.castHom (fun e => (Scheme.Modules.pullback g).obj (N e)) h (op V)
        (Scheme.Modules.pullbackSection g (N d) U V hV z) =
      Scheme.Modules.pullbackSection g (N d') U V hV
        (_root_.SheafOfModules.castHom N h (op U) z) := by
  subst h; rfl

/-- **Transport along an equality of degrees commutes with restriction.** -/
theorem castHom_naturality {Z : Scheme.{u}} (N : ℤ → Z.Modules) {d d' : ℤ} (h : d = d')
    {U V : (Opens ↥Z)ᵒᵖ} (φ : U ⟶ V) (z : (N d).val.obj U) :
    ((N d').val.map φ) (_root_.SheafOfModules.castHom N h U z) =
      _root_.SheafOfModules.castHom N h V (((N d).val.map φ) z) := by
  subst h; rfl

variable {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- **`𝓑 = f^* B̃`**, the sheaf of graded `𝒪_X`-algebras of [Stacks, Tag 0897]. -/
def pullbackGradedAlg : _root_.SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf :=
  Stacks.Conormal.gradedPullback f (specGradedAlg 𝒜)

/-- The homogeneous multiplication of `f^* B̃` is commutative, which is what lets the relative
spectrum `Spec_X(f^* B̃)` be formed. -/
instance isCommutative_pullbackGradedAlg : (pullbackGradedAlg 𝒜 f).IsCommutative :=
  ⟨Stacks.Conormal.gradedPullback_mul_comm f (specGradedAlg 𝒜)
    (Stacks.SpecGraded.specGradedAlgebra_mul_comm (R := CommRingCat.of A) (S := B)
      (intExtend 𝒜))⟩

/-- **`f^* B̃` vanishes in negative degrees.** -/
theorem isZero_pullbackGradedAlg_piece_of_neg (n : ℤ) (hn : n < 0) :
    IsZero ((pullbackGradedAlg 𝒜 f).piece n) :=
  Stacks.Conormal.gradedPullback_isZero f (specGradedAlg 𝒜)
    (isZero_specGradedAlg_piece_of_neg 𝒜 hn)

/-- **The pieces of `f^* B̃` are quasi-coherent** ([Stacks, Tag 01BG]): those of `B̃` are
associated sheaves, and the pullback of a quasi-coherent module is quasi-coherent. -/
theorem isQuasicoherent_pullbackGradedAlg_piece (n : ℤ) :
    ((pullbackGradedAlg 𝒜 f).piece n).IsQuasicoherent :=
  Stacks.Conormal.gradedPullback_isQuasicoherent f (specGradedAlg 𝒜)
    (fun n => Stacks.SpecGraded.isQuasicoherent_specGradedAlgebra_piece
      (R := CommRingCat.of A) (S := B) (intExtend 𝒜) n) n

end Stacks.AlgebraicGeometry.GradedProperCohomology

end
