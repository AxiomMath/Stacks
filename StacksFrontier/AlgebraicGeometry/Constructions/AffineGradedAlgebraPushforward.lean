module

public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence.Basic
public import StacksFrontier.AlgebraicGeometry.Constructions.AffineGradedAlgebraSheaf
public import StacksFrontier.AlgebraicGeometry.Constructions.GradedAlgebraToAlgebraSheaf
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LeftGradedModuleRealization
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The pushforward of the structure sheaf of `Spec B` and the sheaf of graded algebras `B̃`

Let `A` be a commutative ring, `B` an `A`-algebra graded by `A`-submodules, and
`f : Spec B ⟶ Spec A` the morphism of affine schemes induced by the structure map.
`Stacks.AffineGradedAlgebra.algebraSheaf` is the sheaf of graded `𝒪_{Spec A}`-algebras whose
degree-`n` piece is the associated sheaf `(𝒞 n)~`, and `Stacks.RelativeSpec.gradedAlgebraSheaf`
reads its ungraded realization as a sheaf of commutative `𝒪_{Spec A}`-algebras. **This file
constructs the canonical morphism from that algebra sheaf to `f_* 𝒪_{Spec B}`**, which is the
affine graded case of the comparison of [Stacks, Tag 01LX] (3).

The underlying-module comparison is `AlgebraicGeometry.pushforwardTildeIso`, [Stacks, Tag 01I9]:
pushing the associated sheaf of a `B`-module forward along `f` gives the associated sheaf of its
restriction of scalars. What this file supplies is that the comparison **respects the
multiplication and the unit**, which [Stacks, Tag 01I9] says nothing about.

## Main definitions

* `Stacks.AffineGradedAlgebra.pieceToPushforward`: **the degreewise comparison**, from the
  associated sheaf of the degree-`n` piece of `B` to the pushforward `f_* 𝒪_{Spec B}`. It is
  `AlgebraicGeometry.pushforwardTildeNatTrans` at `B` as a `B`-module, precomposed with the
  inclusion of the graded piece.
* `Stacks.AffineGradedAlgebra.pieceSec`: the same comparison on sections over an open, with its
  target read as the *ring* of sections of `f_* 𝒪_{Spec B}` rather than the module underlying
  it.
* `Stacks.AffineGradedAlgebra.totalRingSec`: the comparison on the direct sum of the homogeneous
  components over an open, as a ring homomorphism.
* `Stacks.AffineGradedAlgebra.ungradedSheafHom`: **the comparison as a morphism of sheaves of
  rings** out of the ungraded realization of the graded algebra sheaf.
* `Stacks.AffineGradedAlgebra.toPushforwardAlgebra`: **the comparison as a morphism of sheaves
  of commutative `𝒪_{Spec A}`-algebras**.
* `Stacks.AffineGradedAlgebra.gradedTildeToPushforwardAlgebra` and
  `gradedTildeOfToPushforwardAlgebra`: the same morphism for `B̃`, the sheaf of graded algebras
  of an `ℕ`-graded algebra, in the two spellings of the base used by [Stacks, Tag 0897].

## Main results

* `Stacks.AffineGradedAlgebra.pieceToPushforward_toOpen`: the degreewise comparison over an
  arbitrary open is normalized by the canonical maps from the underlying modules — it sends the
  section of `(𝒞 n)~` represented by `x` to the section of `𝒪_{Spec B}` represented by the same
  `x`.
* `Stacks.AffineGradedAlgebra.pieceSec_mul` and `pieceSec_one`: **the degreewise comparison
  carries the homogeneous multiplication and the unit of the graded algebra sheaf to the
  multiplication and the unit of `𝒪_{Spec B}`**, in every pair of degrees and on arbitrary local
  sections.
* `Stacks.AffineGradedAlgebra.commSheafHom_structureMap`: the comparison is compatible with the
  two structure morphisms.

## Implementation notes

**The ring reading of the target.** The sections of `f_* 𝒪_{Spec B}` over `U` carry a
multiplication only as a commutative ring, not as the `𝒪_{Spec A}`-module underlying it, and the
two readings of the same type are not interchangeable for instance search: `a • s` resolves only
in the module reading and `a * s` only in the ring one. Every statement here is therefore made
in the ring reading `pushforwardSections`, and the identity
`Stacks.AffineGradedAlgebra.pieceSec_smul` — `a • s = f^#(a) * s` — holds by `rfl`.

**The canonical map `B → Γ(Spec B, V)`.** `Stacks.AffineBaseChange.toOpenₗ` of `B` over itself
*is* the ring-side structure map `Stacks.AffineGradedAlgebra.toSpecOpen`, by `rfl`, because
`AlgebraicGeometry.tildeSelf` is `Iso.refl`.

**Degrees are indexed by `ℤ` throughout**, as in [Stacks, Tag 0FQZ]. No vanishing in negative
degrees is assumed and no `ℕ`-indexed coproduct appears; the `ℕ`-graded case enters only through
`Stacks.AffineGradedAlgebra.gradedTilde`, where the grading of [Stacks, Tag 0897]'s `B` is
extended to `ℤ` by zero.

**The comparison is not an isomorphism in general.** [Stacks, Tag 01LX] (3) asserts that the
canonical map is an *isomorphism*. This needs `B` to be the internal direct sum of the `𝒞 n`, a
hypothesis `SetLike.GradedMonoid` does not supply and `B̃` does not carry. Under that hypothesis
it is `Stacks.AffineGradedAlgebra.isIso_toPushforwardAlgebra`.

## References

* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 01LM](https://stacks.math.columbia.edu/tag/01LM)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open scoped TensorProduct

universe u

namespace Stacks.AffineGradedAlgebra

variable (R : CommRingCat.{u}) (B : Type u) [CommRing B] [Algebra R B]

/-- The structural ring map of an `R`-algebra, as a morphism of `CommRingCat`. -/
def specAlgebraMap : R ⟶ CommRingCat.of B := CommRingCat.ofHom (algebraMap R B)

/-- The morphism of affine schemes `Spec B ⟶ Spec R` induced by the structure map. -/
@[ega "IV 1.9.2"]
abbrev specOfAlgebra : Spec (CommRingCat.of B) ⟶ Spec R := Spec.map (specAlgebraMap R B)

/-- The canonical ring map from `B` to the sections of `𝒪_{Spec B}` over an open. -/
def toSpecOpen (V : (Spec (CommRingCat.of B)).Opens) :
    CommRingCat.of B ⟶ (Spec (CommRingCat.of B)).presheaf.obj (op V) :=
  (Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫
    (Spec (CommRingCat.of B)).presheaf.map (homOfLE (le_top (a := V))).op

/-- `Spec B`, read as a sheaf of `𝒪_{Spec R}`-modules by pushing the structure sheaf of
`Spec B` forward along `Spec B ⟶ Spec R`. -/
abbrev pushforwardModule : (Spec R).Modules :=
  (Scheme.Modules.pushforward (specOfAlgebra R B)).obj
    (AlgebraicGeometry.tilde (ModuleCat.of (CommRingCat.of B) B))

variable {R B}
variable (𝒞 : ℤ → Submodule R B)

/-- The inclusion of a graded piece of `B` into `B`, read as an `R`-linear map into the
restriction of scalars of `B` over itself. -/
def pieceIncl (n : ℤ) : pieceModule 𝒞 n ⟶
    (ModuleCat.restrictScalars (specAlgebraMap R B).hom).obj
      (ModuleCat.of (CommRingCat.of B) B) :=
  ConcreteCategory.ofHom (C := ModuleCat R)
    { toFun x := (x : B)
      map_add' _ _ := rfl
      map_smul' r x := Algebra.smul_def r (x : B) }

/-- **The degreewise comparison**: the associated sheaf of the degree-`n` piece of `B` maps to
the pushforward of the structure sheaf of `Spec B`. -/
def pieceToPushforward (n : ℤ) : pieceSheaf 𝒞 n ⟶ pushforwardModule R B :=
  AlgebraicGeometry.tilde.map (pieceIncl 𝒞 n) ≫
    (AlgebraicGeometry.pushforwardTildeNatTrans R (CommRingCat.of B)
      (specAlgebraMap R B)).app (ModuleCat.of (CommRingCat.of B) B)

/-- The degreewise comparison on global sections sends the section of `(𝒞 n)~` represented by
`x` to the section of `𝒪_{Spec B}` represented by `x` itself. -/
theorem pieceToPushforward_toOpen_top (n : ℤ) (x : ↥(𝒞 n)) :
    (pieceToPushforward 𝒞 n).val.app (op ⊤)
        (AffineBaseChange.toOpenₗ (pieceModule 𝒞 n) ⊤ x) =
      AffineBaseChange.toOpenₗ (ModuleCat.of (CommRingCat.of B) B) ⊤ (x : B) := by
  have h1 := congrArg (fun g => g.hom x)
    (AlgebraicGeometry.tilde.toOpen_map_app (pieceIncl 𝒞 n) (⊤ : (Spec R).Opens))
  have h2 := AlgebraicGeometry.pushforwardTildeNatTrans_app_toOpen R (CommRingCat.of B)
    (specAlgebraMap R B) (ModuleCat.of (CommRingCat.of B) B) (x : B)
  exact (congrArg
    (((AlgebraicGeometry.pushforwardTildeNatTrans R (CommRingCat.of B)
      (specAlgebraMap R B)).app (ModuleCat.of (CommRingCat.of B) B)).val.app (op ⊤)) h1).trans h2

/-- The degreewise comparison over an arbitrary open sends the section of `(𝒞 n)~` represented
by `x` to the section of `𝒪_{Spec B}` represented by `x` itself. -/
theorem pieceToPushforward_toOpen (n : ℤ) (U : (Spec R).Opens) (x : ↥(𝒞 n)) :
    (pieceToPushforward 𝒞 n).val.app (op U)
        (AffineBaseChange.toOpenₗ (pieceModule 𝒞 n) U x) =
      AffineBaseChange.toOpenₗ (ModuleCat.of (CommRingCat.of B) B)
        (specOfAlgebra R B ⁻¹ᵁ U) (x : B) :=
  have hres := AffineBaseChange.toOpenₗ_res (pieceModule 𝒞 n) (homOfLE (le_top (a := U))) x
  have hnat := PresheafOfModules.naturality_apply (pieceToPushforward 𝒞 n).val
    (homOfLE (le_top (a := U))).op (AffineBaseChange.toOpenₗ (pieceModule 𝒞 n) ⊤ x)
  have hres2 := AffineBaseChange.toOpenₗ_res (ModuleCat.of (CommRingCat.of B) B)
    (homOfLE (le_top (a := specOfAlgebra R B ⁻¹ᵁ U))) (x : B)
  ((congrArg (fun y => (pieceToPushforward 𝒞 n).val.app (op U) y) hres).symm.trans hnat).trans
    ((congrArg (fun y => (pushforwardModule R B).val.map (homOfLE (le_top (a := U))).op y)
      (pieceToPushforward_toOpen_top 𝒞 n x)).trans hres2)

/-! ### The comparison on sections, read in the ring of sections -/

section Sections

variable (R B)

/-- The ring of sections of `𝒪_{Spec B}` over the preimage of an open of `Spec R`: the
sections of `f_* 𝒪_{Spec B}` over that open. -/
abbrev pushforwardSections (U : (Spec R).Opens) : CommRingCat.{u} :=
  (Spec (CommRingCat.of B)).presheaf.obj (op (specOfAlgebra R B ⁻¹ᵁ U))

end Sections

/-- **The degreewise comparison on sections**, with its target read as the *ring* of sections
of `f_* 𝒪_{Spec B}` rather than as the module underlying it. The two are the same type, so this
is `Stacks.AffineGradedAlgebra.pieceToPushforward` itself. -/
def pieceSec (n : ℤ) (U : (Spec R).Opens) (y : Γ(pieceSheaf 𝒞 n, U)) :
    pushforwardSections R B U :=
  ((pieceToPushforward 𝒞 n).val.app (op U)).hom y

/-- The degreewise comparison on sections is additive. -/
theorem pieceSec_add (n : ℤ) (U : (Spec R).Opens) (y y' : Γ(pieceSheaf 𝒞 n, U)) :
    pieceSec 𝒞 n U (y + y') = pieceSec 𝒞 n U y + pieceSec 𝒞 n U y' :=
  map_add ((pieceToPushforward 𝒞 n).val.app (op U)).hom y y'

/-- The degreewise comparison on sections carries the action of a section `a` of `𝒪_{Spec R}` to
multiplication by the image of `a` in the sections of `𝒪_{Spec B}`. -/
theorem pieceSec_smul (n : ℤ) (U : (Spec R).Opens) (a : Γ(Spec R, U))
    (y : Γ(pieceSheaf 𝒞 n, U)) :
    pieceSec 𝒞 n U (a • y) = (specOfAlgebra R B).app U a * pieceSec 𝒞 n U y :=
  LinearMap.map_smul ((pieceToPushforward 𝒞 n).val.app (op U)).hom a y

/-- The degreewise comparison on sections sends the section of `(𝒞 n)~` represented by `x` to the
section of `𝒪_{Spec B}` represented by `x` itself. -/
theorem pieceSec_toOpen (n : ℤ) (U : (Spec R).Opens) (x : ↥(𝒞 n)) :
    pieceSec 𝒞 n U (AffineBaseChange.toOpenₗ (pieceModule 𝒞 n) U x) =
      (toSpecOpen B (specOfAlgebra R B ⁻¹ᵁ U)).hom (x : B) :=
  pieceToPushforward_toOpen 𝒞 n U x

/-! ### The multiplicativity law on base-changed sections -/

/-- The degreewise comparison read on the base-change presheaf `U ↦ 𝒪(U) ⊗_R 𝒞 n`, as an
additive map into the ring of sections of `f_* 𝒪_{Spec B}`. -/
def pieceBaseSec (n : ℤ) (U : (Spec R).Opens) :
    (piecePresheaf 𝒞 n).obj (op U) →+ pushforwardSections R B U :=
  AddMonoidHom.mk'
    (fun y => pieceSec 𝒞 n U (PresheafOfModules.Hom.app (pieceCmp 𝒞 n) (op U) y))
    fun y y' => by
      refine Eq.trans (congrArg (pieceSec 𝒞 n U) ?_) (pieceSec_add 𝒞 n U _ _)
      exact map_add ((pieceCmp 𝒞 n).app (op U)).hom y y'

/-- `Stacks.AffineGradedAlgebra.pieceBaseSec` is `Stacks.AffineGradedAlgebra.pieceSec` applied
after the sheafification comparison `Stacks.AffineGradedAlgebra.pieceCmp`. -/
theorem pieceBaseSec_apply (n : ℤ) (U : (Spec R).Opens) (y : (piecePresheaf 𝒞 n).obj (op U)) :
    pieceBaseSec 𝒞 n U y =
      pieceSec 𝒞 n U (PresheafOfModules.Hom.app (pieceCmp 𝒞 n) (op U) y) := rfl

/-- The degreewise comparison on base-changed sections sends `0` to `0`. -/
theorem pieceBaseSec_zero (n : ℤ) (U : (Spec R).Opens) :
    pieceBaseSec 𝒞 n U (0 : Γ(Spec R, U) ⊗[R] ↥(𝒞 n)) = 0 := map_zero _

/-- The degreewise comparison on base-changed sections is additive. -/
theorem pieceBaseSec_add (n : ℤ) (U : (Spec R).Opens)
    (y y' : Γ(Spec R, U) ⊗[R] ↥(𝒞 n)) :
    pieceBaseSec 𝒞 n U (y + y') = pieceBaseSec 𝒞 n U y + pieceBaseSec 𝒞 n U y' :=
  map_add _ y y'

/-- The degreewise comparison on `a ⊗ x` is the product of the structural image of `a` and the
section of `𝒪_{Spec B}` represented by `x`. -/
theorem pieceBaseSec_tmul (n : ℤ) (U : (Spec R).Opens) (a : Γ(Spec R, U)) (x : ↥(𝒞 n)) :
    pieceBaseSec 𝒞 n U (a ⊗ₜ[R] x) =
      (specOfAlgebra R B).app U a *
        (toSpecOpen B (specOfAlgebra R B ⁻¹ᵁ U)).hom (x : B) := by
  show pieceSec 𝒞 n U (a • AffineBaseChange.toOpenₗ (pieceModule 𝒞 n) U x) = _
  rw [pieceSec_smul, pieceSec_toOpen]

/-- The unit of the base-changed graded algebra goes to `1`. -/
theorem pieceBaseSec_one (hone : (1 : B) ∈ 𝒞 0) (U : (Spec R).Opens) :
    pieceBaseSec 𝒞 0 U ((1 : Γ(Spec R, U)) ⊗ₜ[R] oneEl 𝒞 hone) = 1 := by
  rw [pieceBaseSec_tmul, show ((oneEl 𝒞 hone : ↥(𝒞 0)) : B) = 1 from rfl, map_one, map_one,
    mul_one]

/-- **The degreewise comparison is multiplicative on base-changed sections**: it carries the
graded multiplication `Stacks.AffineGradedAlgebra.mulSec` to the multiplication of sections of
`𝒪_{Spec B}`. -/
theorem pieceBaseSec_mul
    (hmul : ∀ (i j : ℤ) ⦃x y : B⦄, x ∈ 𝒞 i → y ∈ 𝒞 j → x * y ∈ 𝒞 (i + j))
    (i j : ℤ) (U : (Spec R).Opens)
    (y : (piecePresheaf 𝒞 i).obj (op U)) (z : (piecePresheaf 𝒞 j).obj (op U)) :
    pieceBaseSec 𝒞 (i + j) U (mulSec 𝒞 hmul (op U) i j y z) =
      pieceBaseSec 𝒞 i U y * pieceBaseSec 𝒞 j U z := by
  induction y using TensorProduct.induction_on with
  | zero =>
      have h : mulSec 𝒞 hmul (op U) i j 0 z = 0 := by
        rw [map_zero]
        rfl
      rw [h, pieceBaseSec_zero, pieceBaseSec_zero, zero_mul]
  | tmul a x =>
      induction z using TensorProduct.induction_on with
      | zero =>
          rw [show mulSec 𝒞 hmul (op U) i j (a ⊗ₜ[R] x) 0 = 0 from map_zero _,
            pieceBaseSec_zero, pieceBaseSec_zero, mul_zero]
      | tmul b w =>
          rw [mulSec_tmul, pieceBaseSec_tmul, pieceBaseSec_tmul, pieceBaseSec_tmul,
            show ((mulₗ 𝒞 hmul i j x w : ↥(𝒞 (i + j))) : B) = (x : B) * (w : B) from rfl,
            map_mul, map_mul]
          ring
      | add z z' hz hz' =>
          rw [show mulSec 𝒞 hmul (op U) i j (a ⊗ₜ[R] x) (z + z') =
                mulSec 𝒞 hmul (op U) i j (a ⊗ₜ[R] x) z +
                  mulSec 𝒞 hmul (op U) i j (a ⊗ₜ[R] x) z' from map_add _ z z',
            pieceBaseSec_add, hz, hz', pieceBaseSec_add, mul_add]
  | add y y' hy hy' =>
      have h : mulSec 𝒞 hmul (op U) i j (y + y') z =
          mulSec 𝒞 hmul (op U) i j y z + mulSec 𝒞 hmul (op U) i j y' z := by
        rw [map_add]
        rfl
      rw [h, pieceBaseSec_add, hy, hy', pieceBaseSec_add, add_mul]

/-! ### The multiplicativity law on sheaf sections -/

/-- Restriction in the ring of sections of `f_* 𝒪_{Spec B}`. -/
abbrev pushforwardRestrict {U V : (Spec R).Opens} (h : V ≤ U) :
    pushforwardSections R B U ⟶ pushforwardSections R B V :=
  (Spec (CommRingCat.of B)).presheaf.map (homOfLE (fun _ hx => h hx)).op

/-- Restriction in the module `f_* 𝒪_{Spec B}` is restriction in its ring of sections. -/
theorem pushforwardModule_map {U V : (Spec R).Opens} (f : V ⟶ U)
    (s : pushforwardSections R B U) :
    (pushforwardModule R B).val.map f.op s = (pushforwardRestrict (B := B) f.le).hom s := rfl

/-- The degreewise comparison commutes with restriction. -/
theorem pieceSec_restrict (n : ℤ) {U V : (Spec R).Opens} (f : V ⟶ U)
    (y : Γ(pieceSheaf 𝒞 n, U)) :
    pieceSec 𝒞 n V ((pieceSheaf 𝒞 n).val.map f.op y) =
      (pushforwardRestrict (B := B) f.le).hom (pieceSec 𝒞 n U y) :=
  PresheafOfModules.naturality_apply (pieceToPushforward 𝒞 n).val f.op y

/-- If a base-changed section maps to the restriction of a section `s`, the restriction of the
comparison of `s` is the comparison of the base-changed section. -/
private theorem pieceSec_restrict_eq_pieceBaseSec (n : ℤ) {U V : (Spec R).Opens} (f : V ⟶ U)
    (s : Γ(pieceSheaf 𝒞 n, U)) (s₀ : (piecePresheaf 𝒞 n).obj (op V))
    (h : PresheafOfModules.Hom.app (pieceCmp 𝒞 n) (op V) s₀ = (pieceSheaf 𝒞 n).val.map f.op s) :
    (pushforwardRestrict (B := B) f.le).hom (pieceSec 𝒞 n U s) = pieceBaseSec 𝒞 n V s₀ :=
  (pieceSec_restrict 𝒞 n f s).symm.trans (congrArg (pieceSec 𝒞 n V) h.symm)

/-- **The degreewise comparison is multiplicative**, in every pair of degrees and on arbitrary
local sections: it carries the homogeneous multiplication of
`Stacks.AffineGradedAlgebra.algebraSheaf` to the multiplication of sections of `𝒪_{Spec B}`. -/
theorem pieceSec_mul
    (hmul : ∀ (i j : ℤ) ⦃x y : B⦄, x ∈ 𝒞 i → y ∈ 𝒞 j → x * y ∈ 𝒞 (i + j))
    (hone : (1 : B) ∈ 𝒞 0) (i j : ℤ) (U : (Spec R).Opens)
    (x : Γ(pieceSheaf 𝒞 i, U)) (y : Γ(pieceSheaf 𝒞 j, U)) :
    pieceSec 𝒞 (i + j) U (((algebraSheaf 𝒞 hmul hone).mul i j).app (op U) x y) =
      pieceSec 𝒞 i U x * pieceSec 𝒞 j U y := by
  refine eq_of_isSeparated (pushforwardModule R B)
    ((Opens.grothendieckTopology (Spec R : TopCat)).intersection_covering
      (cmpSieve_mem (pieceCmp 𝒞 i) x) (cmpSieve_mem (pieceCmp 𝒞 j) y)) ?_
  rintro V f ⟨⟨x₀, hx₀⟩, ⟨y₀, hy₀⟩⟩
  have hrest := Stacks.GradedAlgebra.ofComparison_mul_restrict (presheafAlgebra 𝒞 hmul hone)
    (pieceSheaf 𝒞) (pieceCmp 𝒞) i j f.op x y x₀ y₀ hx₀ hy₀
  have hL := pieceSec_restrict_eq_pieceBaseSec 𝒞 (i + j) f
    (((algebraSheaf 𝒞 hmul hone).mul i j).app (op U) x y) _ hrest.symm
  have hRi := pieceSec_restrict_eq_pieceBaseSec 𝒞 i f x x₀ hx₀
  have hRj := pieceSec_restrict_eq_pieceBaseSec 𝒞 j f y y₀ hy₀
  rw [pushforwardModule_map, pushforwardModule_map, hL, map_mul, hRi, hRj]
  exact pieceBaseSec_mul 𝒞 hmul i j V x₀ y₀

/-- **The degreewise comparison carries the unit of `algebraSheaf` to `1`.** -/
theorem pieceSec_one
    (hmul : ∀ (i j : ℤ) ⦃x y : B⦄, x ∈ 𝒞 i → y ∈ 𝒞 j → x * y ∈ 𝒞 (i + j))
    (hone : (1 : B) ∈ 𝒞 0) (U : (Spec R).Opens) :
    pieceSec 𝒞 0 U ((algebraSheaf 𝒞 hmul hone).one.eval (op U)) = 1 := by
  rw [algebraSheaf_one_eval]
  exact pieceBaseSec_one 𝒞 hone U

/-! ### The comparison out of the ungraded realization -/

section Ungraded

variable (hmul : ∀ (i j : ℤ) ⦃x y : B⦄, x ∈ 𝒞 i → y ∈ 𝒞 j → x * y ∈ 𝒞 (i + j))
  (hone : (1 : B) ∈ 𝒞 0)

/-- The degreewise comparison on sections, as an additive map. -/
def pieceSecHom (n : ℤ) (U : (Spec R).Opens) :
    Γ(pieceSheaf 𝒞 n, U) →+ pushforwardSections R B U :=
  AddMonoidHom.mk' (pieceSec 𝒞 n U) (pieceSec_add 𝒞 n U)

/-- The comparison on the direct sum of the homogeneous components over an open, as an additive
map into the sections of `f_* 𝒪_{Spec B}`. -/
def totalAddSec (U : (Spec R).Opens) :
    (algebraSheaf 𝒞 hmul hone).toPresheafGradedAlgebra.Total (op U) →+
      pushforwardSections R B U :=
  DirectSum.toAddMonoid fun n => pieceSecHom 𝒞 n U

/-- On the homogeneous component of degree `n`, `Stacks.AffineGradedAlgebra.totalAddSec` is the
degreewise comparison `Stacks.AffineGradedAlgebra.pieceSec`. -/
theorem totalAddSec_incl (n : ℤ) (U : (Spec R).Opens)
    (y : ((algebraSheaf 𝒞 hmul hone).piece n).val.obj (op U)) :
    totalAddSec 𝒞 hmul hone U
        ((algebraSheaf 𝒞 hmul hone).toPresheafGradedAlgebra.incl n y) =
      pieceSec 𝒞 n U y :=
  DirectSum.toAddMonoid_of (fun n => pieceSecHom 𝒞 n U) n y

/-- The comparison on the direct sum of the homogeneous components sends `1` to `1`. -/
theorem totalAddSec_one (U : (Spec R).Opens) : totalAddSec 𝒞 hmul hone U 1 = 1 := by
  rw [Stacks.GradedAlgebra.one_eq_incl, totalAddSec_incl]
  exact pieceSec_one 𝒞 hmul hone U

/-- The comparison on the direct sum of the homogeneous components is multiplicative. -/
theorem totalAddSec_mul (U : (Spec R).Opens)
    (a b : (algebraSheaf 𝒞 hmul hone).toPresheafGradedAlgebra.Total (op U)) :
    totalAddSec 𝒞 hmul hone U (a * b) =
      totalAddSec 𝒞 hmul hone U a * totalAddSec 𝒞 hmul hone U b := by
  induction a using Stacks.GradedAlgebra.incl_induction with
  | zero => rw [zero_mul, map_zero, zero_mul]
  | incl i x =>
      induction b using Stacks.GradedAlgebra.incl_induction with
      | zero => rw [mul_zero, map_zero, mul_zero]
      | incl j y =>
          rw [Stacks.GradedAlgebra.incl_mul_incl, totalAddSec_incl, totalAddSec_incl,
            totalAddSec_incl]
          exact pieceSec_mul 𝒞 hmul hone i j U x y
      | add b b' hb hb' => rw [mul_add, map_add, map_add, hb, hb', mul_add]
  | add a a' ha ha' => rw [add_mul, map_add, map_add, ha, ha', add_mul]

/-- **The comparison on the direct sum of the homogeneous components over an open, as a ring
homomorphism.** -/
def totalRingSec (U : (Spec R).Opens) :
    (algebraSheaf 𝒞 hmul hone).toPresheafGradedAlgebra.Total (op U) →+*
      pushforwardSections R B U where
  toFun := totalAddSec 𝒞 hmul hone U
  map_zero' := map_zero (totalAddSec 𝒞 hmul hone U)
  map_add' := map_add (totalAddSec 𝒞 hmul hone U)
  map_one' := totalAddSec_one 𝒞 hmul hone U
  map_mul' := totalAddSec_mul 𝒞 hmul hone U

/-- The comparison out of the direct sum commutes with restriction. -/
theorem totalAddSec_restrict {U V : (Spec R).Opens} (g : V ⟶ U)
    (a : (algebraSheaf 𝒞 hmul hone).toPresheafGradedAlgebra.Total (op U)) :
    totalAddSec 𝒞 hmul hone V
        ((algebraSheaf 𝒞 hmul hone).toPresheafGradedAlgebra.totalRestrict g.op a) =
      (pushforwardRestrict (B := B) g.le).hom (totalAddSec 𝒞 hmul hone U a) := by
  induction a using Stacks.GradedAlgebra.incl_induction with
  | zero => simp only [map_zero]
  | incl i x =>
      rw [Stacks.GradedAlgebra.totalRestrict_incl, totalAddSec_incl, totalAddSec_incl]
      exact pieceSec_restrict 𝒞 i g x
  | add a a' ha ha' => simp only [map_add, ha, ha']

/-- **The comparison as a morphism of presheaves of rings** out of the direct sum of the
homogeneous components of `B̃`. -/
def totalPresheafHom :
    (algebraSheaf 𝒞 hmul hone).toPresheafGradedAlgebra.totalPresheaf ⟶
      (Stacks.RelativeSpec.AlgebraSheaf.ringSheaf
        (AffineAlgebraEquivalence.pushforwardAlgebra (specOfAlgebra R B))).obj where
  app W := RingCat.ofHom (totalRingSec 𝒞 hmul hone W.unop)
  naturality _ _ f := RingCat.hom_ext (RingHom.ext fun a =>
    totalAddSec_restrict 𝒞 hmul hone f.unop a)

/-- **The comparison as a morphism of sheaves of rings**: the ungraded realization of `B̃` maps
to `f_* 𝒪_{Spec B}`. This is `totalPresheafHom` extended across the sheafification, which is
possible because the target is a sheaf. -/
def ungradedSheafHom :
    (algebraSheaf 𝒞 hmul hone).ungradedSheaf ⟶
      Stacks.RelativeSpec.AlgebraSheaf.ringSheaf
        (AffineAlgebraEquivalence.pushforwardAlgebra (specOfAlgebra R B)) :=
  (algebraSheaf 𝒞 hmul hone).toPresheafGradedAlgebra.totalSheafLift
    (Opens.grothendieckTopology (Spec R : TopCat)) _ (totalPresheafHom 𝒞 hmul hone)

/-- The morphism of sheaves of rings is the comparison on the direct sum: on the image of a
section of the direct sum of the homogeneous components over an open it is
`Stacks.AffineGradedAlgebra.totalRingSec`. -/
theorem ungradedSheafHom_totalUnit (U : (Spec R).Opens)
    (a : (algebraSheaf 𝒞 hmul hone).toPresheafGradedAlgebra.Total (op U)) :
    ((ungradedSheafHom 𝒞 hmul hone).hom.app (op U)).hom
        ((algebraSheaf 𝒞 hmul hone).toPresheafGradedAlgebra.totalUnit
          (Opens.grothendieckTopology (Spec R : TopCat)) (op U) a) =
      totalRingSec 𝒞 hmul hone U a :=
  congrArg (fun φ => RingCat.Hom.hom (NatTrans.app φ (op U)) a)
    (Stacks.GradedAlgebra.toTotalSheaf_totalSheafLift
      (algebraSheaf 𝒞 hmul hone).toPresheafGradedAlgebra
      (Opens.grothendieckTopology (Spec R : TopCat)) _ (totalPresheafHom 𝒞 hmul hone))

/-- The comparison out of the direct sum is semilinear over the sections of the structure
sheaf. -/
theorem totalAddSec_smul (U : (Spec R).Opens)
    (r : (Spec R).ringCatSheaf.obj.obj (op U))
    (a : (algebraSheaf 𝒞 hmul hone).toPresheafGradedAlgebra.Total (op U)) :
    totalAddSec 𝒞 hmul hone U (r • a) =
      ((specOfAlgebra R B).app U).hom r * totalAddSec 𝒞 hmul hone U a := by
  induction a using Stacks.GradedAlgebra.incl_induction with
  | zero => rw [smul_zero, map_zero, mul_zero]
  | incl i x =>
      rw [← Stacks.GradedAlgebra.incl_smul, totalAddSec_incl, totalAddSec_incl]
      exact pieceSec_smul 𝒞 i U r x
  | add a a' ha ha' =>
      rw [smul_add, map_add, ha, ha', map_add, mul_add]

/-- The comparison out of the direct sum carries the structure map `r ↦ r · 1` to the
structural map of sections. -/
theorem totalAddSec_structureMap (U : (Spec R).Opens)
    (r : (Spec R).ringCatSheaf.obj.obj (op U)) :
    totalAddSec 𝒞 hmul hone U
        ((algebraSheaf 𝒞 hmul hone).toPresheafGradedAlgebra.structureMap (op U) r) =
      ((specOfAlgebra R B).app U).hom r := by
  have h : (algebraSheaf 𝒞 hmul hone).toPresheafGradedAlgebra.structureMap (op U) r =
      r • (1 : (algebraSheaf 𝒞 hmul hone).toPresheafGradedAlgebra.Total (op U)) := rfl
  rw [h, totalAddSec_smul, totalAddSec_one, mul_one]

/-! ### The morphism of sheaves of commutative algebras -/

variable (hc : ∀ (i j : ℤ) (W : ((Spec R).Opens)ᵒᵖ)
  (a : ((algebraSheaf 𝒞 hmul hone).piece i).val.obj W)
  (b : ((algebraSheaf 𝒞 hmul hone).piece j).val.obj W),
  HEq (((algebraSheaf 𝒞 hmul hone).mul i j).app W a b)
    (((algebraSheaf 𝒞 hmul hone).mul j i).app W b a))

/-- `Stacks.AffineGradedAlgebra.ungradedSheafHom`, read as a morphism of sheaves of *commutative*
rings. The source is the lift to `CommRingCat` of the ungraded realization, which keeps the
carrier and the ring operations, so this changes nothing but the ambient category. -/
def commSheafHom :
    (Stacks.RelativeSpec.gradedAlgebraSheaf (Spec R) (algebraSheaf 𝒞 hmul hone) hc).right ⟶
      (AffineAlgebraEquivalence.pushforwardAlgebra (specOfAlgebra R B)).right :=
  ObjectProperty.homMk
    { app W := @CommRingCat.ofHom
        ((algebraSheaf 𝒞 hmul hone).ungradedSheaf.obj.obj W)
        ((AffineAlgebraEquivalence.pushforwardAlgebra
          (specOfAlgebra R B)).right.obj.obj W)
        (Stacks.CommRingSheaf.commRing _
          ((algebraSheaf 𝒞 hmul hone).mul_comm_ungradedSheaf hc W))
        inferInstance ((ungradedSheafHom 𝒞 hmul hone).hom.app W).hom
      naturality := fun W W' g => by
        ext x
        exact congrArg (fun φ => RingCat.Hom.hom φ x)
          ((ungradedSheafHom 𝒞 hmul hone).hom.naturality g) }

/-- **The comparison is compatible with the two structure morphisms**: the structure map
`r ↦ r · 1` of the ungraded realization of `B̃`, followed by the comparison, is the structural
map `Γ(Spec R, U) → Γ(Spec B, f⁻¹U)`. -/
theorem commSheafHom_structureMap (U : (Spec R).Opens) (r : Γ(Spec R, U)) :
    ((commSheafHom 𝒞 hmul hone hc).hom.app (op U)).hom
        (((Stacks.RelativeSpec.gradedAlgebraSheaf (Spec R)
          (algebraSheaf 𝒞 hmul hone) hc).hom.hom.app (op U)).hom r) =
      ((specOfAlgebra R B).app U).hom r := by
  have hstr : (((Stacks.RelativeSpec.gradedAlgebraSheaf (Spec R)
        (algebraSheaf 𝒞 hmul hone) hc).hom.hom.app (op U)).hom r) =
      (algebraSheaf 𝒞 hmul hone).toPresheafGradedAlgebra.totalUnit
        (Opens.grothendieckTopology (Spec R : TopCat)) (op U)
        ((algebraSheaf 𝒞 hmul hone).toPresheafGradedAlgebra.structureMap (op U) r) := rfl
  rw [hstr]
  exact (ungradedSheafHom_totalUnit 𝒞 hmul hone U _).trans
    (totalAddSec_structureMap 𝒞 hmul hone U r)

/-- **Leg (i) of [Stacks, Tag 01LX] in the affine graded case, as a morphism**: the canonical
map from the sheaf of commutative `𝒪_{Spec R}`-algebras presented by a graded `R`-algebra to the
pushforward `f_* 𝒪_{Spec B}` of the structure sheaf of `Spec B` along `f : Spec B ⟶ Spec R`.

It is not an isomorphism in general: the module underlying the source is the sheafification of
the direct sum of the `(𝒞 n)~` (`Stacks.RelativeSpec.gradedDirectSumIsoUnderlyingModule`), and
comparing that with `f_* 𝒪_{Spec B}` needs `B` to be the internal direct sum `⨁ n, 𝒞 n`. That is
not implied by the hypotheses carried here, nor by the `SetLike.GradedMonoid` of
`Stacks.AffineGradedAlgebra.gradedTilde`: for `𝒞 n = ⊤` in every degree `n ≥ 0` the hypotheses
hold and the source has a copy of `B` in every nonnegative degree, so the comparison is not
injective. Under `DirectSum.IsInternal` it is invertible:
`Stacks.AffineGradedAlgebra.isIso_toPushforwardAlgebra`. -/
def toPushforwardAlgebra :
    Stacks.RelativeSpec.gradedAlgebraSheaf (Spec R) (algebraSheaf 𝒞 hmul hone) hc ⟶
      AffineAlgebraEquivalence.pushforwardAlgebra (specOfAlgebra R B) :=
  Under.homMk (commSheafHom 𝒞 hmul hone hc) (by
    refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun W => CommRingCat.hom_ext
      (RingHom.ext fun r => ?_)))
    exact commSheafHom_structureMap 𝒞 hmul hone hc W.unop r)

end Ungraded

/-! ### The case of `B̃` -/

section Nat

variable {R : CommRingCat.{u}} {B : Type u} [CommRing B] [Algebra R B]
  (𝒜 : ℕ → Submodule R B) [SetLike.GradedMonoid 𝒜]

/-- **Leg (i) of [Stacks, Tag 01LX] for `B̃`**: the canonical morphism of sheaves of commutative
`𝒪_{Spec R}`-algebras from the algebra sheaf presented by `B̃` to the pushforward
`f_* 𝒪_{Spec B}` along `f : Spec B ⟶ Spec R`. -/
def gradedTildeToPushforwardAlgebra :
    Stacks.RelativeSpec.gradedAlgebraSheaf (Spec R) (gradedTilde 𝒜) (gradedTilde_mul_comm 𝒜) ⟶
      AffineAlgebraEquivalence.pushforwardAlgebra (specOfAlgebra R B) :=
  toPushforwardAlgebra (intPiece 𝒜) (mul_mem_intPiece 𝒜) (one_mem_intPiece 𝒜)
    (gradedTilde_mul_comm 𝒜)

/-- The morphism for `B̃` is degreewise the comparison
`Stacks.AffineGradedAlgebra.pieceToPushforward`: on the image in the ungraded realization of a
local section of the degree-`n` piece `(𝒜 n)~` it is that section read in `𝒪_{Spec B}`. -/
theorem gradedTildeToPushforwardAlgebra_ungradedIncl (n : ℤ) (U : (Spec R).Opens)
    (y : ((gradedTilde 𝒜).piece n).val.obj (op U)) :
    ((gradedTildeToPushforwardAlgebra 𝒜).right.hom.app (op U)).hom
        ((gradedTilde 𝒜).ungradedIncl n y) =
      pieceSec (intPiece 𝒜) n U y :=
  (ungradedSheafHom_totalUnit (intPiece 𝒜) (mul_mem_intPiece 𝒜) (one_mem_intPiece 𝒜) U _).trans
    (totalAddSec_incl (intPiece 𝒜) (mul_mem_intPiece 𝒜) (one_mem_intPiece 𝒜) n U y)

end Nat

/-- **Leg (i) of [Stacks, Tag 01LX] for `B̃` over a bare commutative ring**, which is the shape
in which [Stacks, Tag 0897] uses it. -/
abbrev gradedTildeOfToPushforwardAlgebra (A : Type u) [CommRing A] {B : Type u} [CommRing B]
    [Algebra A B] (𝒜 : ℕ → Submodule A B) [SetLike.GradedMonoid 𝒜] :
    Stacks.RelativeSpec.gradedAlgebraSheaf (Spec (CommRingCat.of A)) (gradedTildeOf A 𝒜)
        (gradedTilde_mul_comm (R := CommRingCat.of A) 𝒜) ⟶
      AffineAlgebraEquivalence.pushforwardAlgebra (specOfAlgebra (CommRingCat.of A) B) :=
  gradedTildeToPushforwardAlgebra (R := CommRingCat.of A) 𝒜

end Stacks.AffineGradedAlgebra

end
