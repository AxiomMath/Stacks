module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedForgetColimits
public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.GradedPullback
public import StacksFrontier.AlgebraicGeometry.Constructions.AffineGradedAlgebraSheaf

/-!
# Homogeneous elements of a graded algebra as global sections of `f^* B̃`

Let `A` be a commutative ring, `B` an `ℕ`-graded `A`-algebra with pieces `𝒜 n`, and
`f : X ⟶ Spec A` a morphism of schemes. The sheaf of graded `𝒪_{Spec A}`-algebras attached to
`B` is `Stacks.AffineGradedAlgebra.gradedTildeOf A 𝒜` — the `B̃` of [Stacks, Tag 0897] — and
`𝓑 = f^* B̃` is `Stacks.Conormal.gradedPullback f (gradedTildeOf A 𝒜)`, the graded algebra that
statement works over.

**This file turns a homogeneous element of `B` into a global section of the corresponding
homogeneous piece of `f^* B̃`**, and proves that the resulting map is additive, unital and
multiplicative. It is the `f^* B̃` analogue of
`Stacks.Cohomology.FormalFunctions.gradedReesSection`, which does the same for the Rees algebra
`⨁ₙ ℐⁿ` of an ideal sheaf; through `SheafOfModules.GradedModule.smulSectionsHom` — already
stated over an arbitrary sheaf of graded algebras — it is what makes the *ring* `B` act on the
homogeneous pieces of an arbitrary graded `f^* B̃`-module.

## Main definitions

* `Stacks.AffineBaseChange.tildeGlobalSection`: the global section of `Ñ` determined by an
  element of `N`, namely `AlgebraicGeometry.tilde.toOpen` read over every open.
* `Stacks.AffineGradedAlgebra.algebraSheafSection`: the global section of the degree-`n` piece
  of `Stacks.AffineGradedAlgebra.algebraSheaf` determined by an element of the degree-`n` piece
  of `B`.
* `Stacks.AffineGradedAlgebra.gradedTildePullbackSection`: **the global section of
  `(f^* B̃)ₙ` determined by an element of `𝒜 n`.**

## Main results

* `Stacks.PresheafOfModules.eval_bilin_of_top`: a bilinear identity between global sections of
  presheaves of modules on a space holds everywhere as soon as it holds over `⊤`.
* `Stacks.RingedSpace.eval_pullbackSectionsUnit_add`, `eval_pullbackSectionsUnit_congr` and
  `eval_mul_pullbackSectionsUnit`: the global section of `f^*M` obtained from a global section
  of `M` is additive in it, depends on it only through its value over `⊤`, and the sections so
  obtained multiply as those of `M` do.
* `Stacks.AffineGradedAlgebra.algebraSheaf_one_toOpen` and `algebraSheaf_mul_toOpen`: the unit
  and the multiplication of `algebraSheaf` read on `toOpen`-images.
* `Stacks.AffineGradedAlgebra.eval_gradedTildePullbackSection_add`,
  `eval_gradedTildePullbackSection_one` and `eval_mul_gradedTildePullbackSection`:
  **`a ↦ gradedTildePullbackSection a` is additive, unital and multiplicative.** These are the
  three laws that `SheafOfModules.GradedModule.smulSectionsHom_eval_add`,
  `smulSectionsHom_one` and `smulSectionsHom_comp` ask of a system of global homogeneous
  sections of the algebra.

## Implementation notes

The only arithmetic input is at the level of the base-change presheaf of `B`, where the
multiplication is `a ⊗ x, b ⊗ y ↦ ab ⊗ xy` on the nose
(`Stacks.AffineGradedAlgebra.mulSec_tmul`): the two lemmas `algebraSheaf_one_toOpen` and
`algebraSheaf_mul_toOpen` read the unit and the multiplication of `algebraSheaf` on
`toOpen`-images by instantiating the comparison at `1 ⊗ x`, exactly as
`Stacks.SymGraded.symAlgebra_mul_toOpen` does for the symmetric algebra. Compatibility of the
section with restriction is free: `Stacks.AffineBaseChange.toOpenₗ_res` holds by definition.

Passing to the pullback is where the `⊤`-to-everywhere step enters. The identification of the
multiplication of `f^* B̃` that the library has,
`Stacks.RingedSpace.pullbackGradedAlgebra_mul_pullbackUnit`, is stated over the *preimage* of an
open of the target, so it says nothing directly about an open of `X` which is not such a
preimage. What repairs this is that `⊤` is a preimage — of `⊤` — and that the two sides of each
law are global sections, hence determined over any open by restriction from `⊤`. That is
`eval_bilin_of_top`: the multiplication of a sheaf of graded algebras commutes with restriction,
being a bilinear map of presheaves of modules, so a bilinear identity between global sections
has to be checked over `⊤` alone.

No degree transport appears in the multiplicativity statement. The multiplication of `B̃` in
degrees `k` and `l` lands in degree `(k : ℤ) + (l : ℤ)`, which is *definitionally*
`((k + l : ℕ) : ℤ)` because `Int.add` of two `Int.ofNat`s reduces to `Int.ofNat` of the sum; and
for the same reason the product `Stacks.AffineGradedAlgebra.mulₗ` of two homogeneous elements is
definitionally their `GradedMonoid.GMul.mul`. This is why the multiplicativity statement below
is a plain equality while its Rees counterpart
`Stacks.Cohomology.FormalFunctions.castHom_mul_gradedReesSection` carries a
`SheafOfModules.castHom`: there the degrees compared are `(k : ℤ) + (l : ℤ)` and `(m : ℤ)` for
an *arbitrary* `m` with `k + l = m`.

Every mention of `Stacks.AffineGradedAlgebra.intPiece` below passes `R` explicitly. The family
`𝒜` is indexed by submodules over the bare ring `A` while `B̃` is built over
`CommRingCat.of A`, and `R` is not determined by unification from `ℕ → Submodule A B`; leaving
it to be inferred leaves a metavariable in the type of the piece, and the defeq check against
`Stacks.AffineGradedAlgebra.gradedTilde_piece` then unfolds the whole graded-algebra structure
and exhausts the heartbeat budget.

Nothing here carries a `@[stacks]` attribute. `B̃` and its pullback are constructions the proof
of [Stacks, Tag 0897] names in passing rather than the content of a tag, and the tags of the
pieces they are assembled from ([Stacks, Tag 01I8] for the associated sheaf, [Stacks, Tag 0FQW]
for a sheaf of graded algebras) are registered where those are defined.

## References

* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct

universe u

/-! ### A bilinear identity between global sections, checked over `⊤` -/

namespace Stacks.PresheafOfModules

variable {Z : TopCat.{u}} {R : (Opens Z)ᵒᵖ ⥤ RingCat.{u}}
  {M N P : _root_.PresheafOfModules.{u} R}

/-- **A bilinear identity between global sections holds everywhere as soon as it holds over
`⊤`.** A bilinear map of presheaves of modules commutes with restriction, and a global section
is the restriction of its value over `⊤`. -/
theorem eval_bilin_of_top (β : Stacks.BilinearMap M N P) (r : M.sections) (s : N.sections)
    (t : P.sections)
    (h : β.app (op ⊤) (r.eval (op ⊤)) (s.eval (op ⊤)) = t.eval (op ⊤))
    (V : Opens Z) : β.app (op V) (r.eval (op V)) (s.eval (op V)) = t.eval (op V) := by
  let g : (op (⊤ : Opens Z) : (Opens Z)ᵒᵖ) ⟶ op V := (homOfLE (le_top : V ≤ ⊤)).op
  have h1 : β.app (op V) (r.eval (op V)) (s.eval (op V)) =
      β.app (op V) (M.map g (r.eval (op ⊤))) (N.map g (s.eval (op ⊤))) := by
    rw [_root_.PresheafOfModules.sections_property r g,
      _root_.PresheafOfModules.sections_property s g]
  exact h1.trans ((β.naturality g (r.eval (op ⊤)) (s.eval (op ⊤))).symm.trans
    ((congrArg _ h).trans (_root_.PresheafOfModules.sections_property t g)))

end Stacks.PresheafOfModules

/-! ### Global sections of a pullback -/

namespace Stacks.RingedSpace

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- The value over `⊤` of the global section of `f^*M` attached to a global section of `M`. -/
theorem eval_pullbackSectionsUnit_top (M : SheafOfModules.{u} (structureRingSheaf Y))
    (t : M.sections) :
    (pullbackSectionsUnit f M t).eval (op ⊤) = pullbackUnit f M (op ⊤) (t.eval (op ⊤)) :=
  pullbackSectionsUnit_eval f M t ⊤

/-- Equal values of `f^*M` over `⊤` have equal restrictions to every open. -/
private theorem map_top_congr (M : SheafOfModules.{u} (structureRingSheaf Y))
    {m m' : ((pullbackFunctor f).obj M).val.obj (op (⊤ : Opens X.carrier))} (h : m = m')
    (V : Opens X.carrier) :
    ((pullbackFunctor f).obj M).val.map (homOfLE (le_top : V ≤ ⊤)).op m =
      ((pullbackFunctor f).obj M).val.map (homOfLE (le_top : V ≤ ⊤)).op m' :=
  congrArg _ h

/-- The global section of `f^*M` attached to a global section of `M` depends on the latter only
through its value over `⊤`. -/
theorem eval_pullbackSectionsUnit_congr (M : SheafOfModules.{u} (structureRingSheaf Y))
    {t t' : M.sections} (h : t.eval (op ⊤) = t'.eval (op ⊤)) (V : Opens X.carrier) :
    (pullbackSectionsUnit f M t).eval (op V) = (pullbackSectionsUnit f M t').eval (op V) :=
  map_top_congr f M (congrArg (pullbackUnit f M (op ⊤)) h) V

/-- **The global section of `f^*M` attached to a global section of `M` is additive in that
section**, read on values. -/
theorem eval_pullbackSectionsUnit_add (M : SheafOfModules.{u} (structureRingSheaf Y))
    {t t₁ t₂ : M.sections} (h : t.eval (op ⊤) = t₁.eval (op ⊤) + t₂.eval (op ⊤))
    (V : Opens X.carrier) :
    (pullbackSectionsUnit f M t).eval (op V) =
      (pullbackSectionsUnit f M t₁).eval (op V) + (pullbackSectionsUnit f M t₂).eval (op V) := by
  have h1 : pullbackUnitTop f M t = pullbackUnitTop f M t₁ + pullbackUnitTop f M t₂ :=
    (congrArg (pullbackUnit f M (op ⊤)) h).trans
      (pullbackUnit_add f M (op ⊤) (t₁.eval (op ⊤)) (t₂.eval (op ⊤)))
  exact (map_top_congr f M h1 V).trans (map_add _ _ _)

/-- **The global sections of `f^*A` attached to global sections of a sheaf of graded algebras
`A` multiply as those of `A` do.** The hypothesis is the corresponding identity in `A`, needed
over `⊤` alone. -/
theorem eval_mul_pullbackSectionsUnit
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Y)) (i j : ℤ)
    (r : (A.piece i).sections) (s : (A.piece j).sections) (t : (A.piece (i + j)).sections)
    (h : (A.mul i j).app (op ⊤) (r.eval (op ⊤)) (s.eval (op ⊤)) = t.eval (op ⊤))
    (V : Opens X.carrier) :
    ((pullbackGradedAlgebra f A).mul i j).app (op V)
        ((pullbackSectionsUnit f (A.piece i) r).eval (op V))
        ((pullbackSectionsUnit f (A.piece j) s).eval (op V)) =
      (pullbackSectionsUnit f (A.piece (i + j)) t).eval (op V) := by
  refine Stacks.PresheafOfModules.eval_bilin_of_top ((pullbackGradedAlgebra f A).mul i j) _ _ _
    ?_ V
  rw [eval_pullbackSectionsUnit_top f (A.piece i) r,
    eval_pullbackSectionsUnit_top f (A.piece j) s,
    eval_pullbackSectionsUnit_top f (A.piece (i + j)) t]
  exact (pullbackGradedAlgebra_mul_pullbackUnit f A i j ⊤ (r.eval (op ⊤)) (s.eval (op ⊤))).trans
    (congrArg (pullbackUnit f (A.piece (i + j)) (op ⊤)) h)

end Stacks.RingedSpace

/-! ### Global sections of the associated sheaf of a module -/

namespace Stacks.AffineBaseChange

variable {R : CommRingCat.{u}}

/-- **The global section of `Ñ` determined by an element of `N`**: the image of that element
under `AlgebraicGeometry.tilde.toOpen`, over every open. Compatibility with restriction is
`Stacks.AffineBaseChange.toOpenₗ_res`, which holds by definition. -/
def tildeGlobalSection (N : ModuleCat.{u} R) (x : N) : (tilde N).val.sections :=
  _root_.PresheafOfModules.sectionsMk (fun U => toOpenₗ N U.unop x) fun {_ _} _ => rfl

/-- Over an open `U`, the section `tildeGlobalSection N x` evaluates to the image of `x` under
`AlgebraicGeometry.tilde.toOpen`. -/
@[simp]
theorem tildeGlobalSection_eval (N : ModuleCat.{u} R) (x : N) (U : ((Spec R).Opens)ᵒᵖ) :
    (tildeGlobalSection N x).eval U = toOpenₗ N U.unop x := rfl

end Stacks.AffineBaseChange

namespace Stacks.AffineGradedAlgebra

open Stacks.AffineBaseChange

/-! ### The unit, the multiplication and the section map of `algebraSheaf` -/

variable {R : CommRingCat.{u}} {B : Type u} [CommRing B] [Algebra R B] (𝒞 : ℤ → Submodule R B)
  (hmul : ∀ (i j : ℤ) ⦃x y : B⦄, x ∈ 𝒞 i → y ∈ 𝒞 j → x * y ∈ 𝒞 (i + j))
  (hone : (1 : B) ∈ 𝒞 0)

/-- **The unit of `algebraSheaf` is the `toOpen`-image of the unit of `B`.** -/
theorem algebraSheaf_one_toOpen (U : ((Spec R).Opens)ᵒᵖ) :
    (algebraSheaf 𝒞 hmul hone).one.eval U =
      toOpenₗ (pieceModule 𝒞 0) U.unop (oneEl 𝒞 hone) := by
  have h := algebraSheaf_one_eval 𝒞 hmul hone U
  rwa [toTilde_app, toTildeₗ_tmul, one_smul] at h

/-- **The multiplication of `algebraSheaf` on `toOpen`-images is the `toOpen`-image of the
product in `B`.** -/
theorem algebraSheaf_mul_toOpen (i j : ℤ) (U : ((Spec R).Opens)ᵒᵖ) (x : ↥(𝒞 i)) (y : ↥(𝒞 j)) :
    ((algebraSheaf 𝒞 hmul hone).mul i j).app U
        (toOpenₗ (pieceModule 𝒞 i) U.unop x) (toOpenₗ (pieceModule 𝒞 j) U.unop y) =
      toOpenₗ (pieceModule 𝒞 (i + j)) U.unop (mulₗ 𝒞 hmul i j x y) := by
  have h := algebraSheaf_mul_toTilde 𝒞 hmul hone i j U
    ((1 : Γ(Spec R, U.unop)) ⊗ₜ[R] x) ((1 : Γ(Spec R, U.unop)) ⊗ₜ[R] y)
  rwa [toTilde_app, toTildeₗ_tmul, one_smul, toTilde_app, toTildeₗ_tmul, one_smul,
    toTilde_app, mulSec_tmul, _root_.one_mul (1 : Γ(Spec R, U.unop)), toTildeₗ_tmul,
    one_smul] at h

/-- **The global section of the degree-`n` piece of `algebraSheaf` determined by a homogeneous
element of degree `n` of `B`.** -/
def algebraSheafSection (n : ℤ) (x : ↥(𝒞 n)) : ((algebraSheaf 𝒞 hmul hone).piece n).sections :=
  tildeGlobalSection (pieceModule 𝒞 n) x

/-- Over an open `U`, the section `algebraSheafSection 𝒞 hmul hone n x` evaluates to the image
of `x` under `AlgebraicGeometry.tilde.toOpen`. -/
@[simp]
theorem algebraSheafSection_eval (n : ℤ) (x : ↥(𝒞 n)) (U : ((Spec R).Opens)ᵒᵖ) :
    (algebraSheafSection 𝒞 hmul hone n x).eval U = toOpenₗ (pieceModule 𝒞 n) U.unop x := rfl

/-- The section attached to the unit of `B` is the unit of `algebraSheaf`. -/
theorem algebraSheafSection_one_eval (U : ((Spec R).Opens)ᵒᵖ) :
    (algebraSheafSection 𝒞 hmul hone 0 (oneEl 𝒞 hone)).eval U =
      (algebraSheaf 𝒞 hmul hone).one.eval U :=
  (algebraSheaf_one_toOpen 𝒞 hmul hone U).symm

/-- The sections attached to two homogeneous elements multiply to the one attached to their
product. -/
theorem eval_mul_algebraSheafSection (i j : ℤ) (U : ((Spec R).Opens)ᵒᵖ) (x : ↥(𝒞 i))
    (y : ↥(𝒞 j)) :
    ((algebraSheaf 𝒞 hmul hone).mul i j).app U
        ((algebraSheafSection 𝒞 hmul hone i x).eval U)
        ((algebraSheafSection 𝒞 hmul hone j y).eval U) =
      (algebraSheafSection 𝒞 hmul hone (i + j) (mulₗ 𝒞 hmul i j x y)).eval U :=
  algebraSheaf_mul_toOpen 𝒞 hmul hone i j U x y

/-! ### The section map of `f^* B̃` -/

section Nat

variable (A : Type u) [CommRing A] {Bg : Type u} [CommRing Bg] [Algebra A Bg]
  (𝒜 : ℕ → Submodule A Bg) [SetLike.GradedMonoid 𝒜]

/-- **The global section of `B̃ₙ` determined by a homogeneous element of degree `n` of `B`.** -/
def gradedTildeSection {n : ℕ} (a : ↥(𝒜 n)) :
    ((gradedTildeOf A 𝒜).piece (n : ℤ)).sections :=
  algebraSheafSection (intPiece (R := CommRingCat.of A) 𝒜)
    (mul_mem_intPiece (R := CommRingCat.of A) 𝒜) (one_mem_intPiece (R := CommRingCat.of A) 𝒜)
    (n : ℤ) a

variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))

/-- **The global section of `(f^* B̃)ₙ` determined by a homogeneous element of degree `n` of
`B`.** This is the `f^* B̃` analogue of
`Stacks.Cohomology.FormalFunctions.gradedReesSection`: through
`SheafOfModules.GradedModule.smulSectionsHom` it is what makes the ring `B` act on the
homogeneous pieces of a graded `f^* B̃`-module. -/
def gradedTildePullbackSection {n : ℕ} (a : ↥(𝒜 n)) :
    ((Stacks.Conormal.gradedPullback f (gradedTildeOf A 𝒜)).piece (n : ℤ)).sections :=
  Stacks.RingedSpace.pullbackSectionsUnit f.toLRSHom.toShHom
    ((gradedTildeOf A 𝒜).piece (n : ℤ)) (gradedTildeSection A 𝒜 a)

/-- **`a ↦ gradedTildePullbackSection a` is additive.** -/
theorem eval_gradedTildePullbackSection_add {n : ℕ} (a a' : ↥(𝒜 n)) (V : Opens X.carrier) :
    (gradedTildePullbackSection A 𝒜 f (a + a')).eval (op V) =
      (gradedTildePullbackSection A 𝒜 f a).eval (op V) +
        (gradedTildePullbackSection A 𝒜 f a').eval (op V) :=
  Stacks.RingedSpace.eval_pullbackSectionsUnit_add f.toLRSHom.toShHom
    ((gradedTildeOf A 𝒜).piece (n : ℤ))
    (map_add (toOpenₗ (pieceModule (intPiece (R := CommRingCat.of A) 𝒜) (n : ℤ)) ⊤) a a') V

/-- The global section attached to the zero element vanishes. -/
theorem eval_gradedTildePullbackSection_zero {n : ℕ} (V : Opens X.carrier) :
    (gradedTildePullbackSection A 𝒜 f (0 : ↥(𝒜 n))).eval (op V) = 0 := by
  have h := eval_gradedTildePullbackSection_add A 𝒜 f (0 : ↥(𝒜 n)) 0 V
  rw [add_zero] at h
  exact add_left_cancel (h.symm.trans (add_zero _).symm)

/-- **`a ↦ gradedTildePullbackSection a` is unital**: the section attached to the unit of `B` is
the unit of `f^* B̃`. -/
theorem eval_gradedTildePullbackSection_one (V : Opens X.carrier) :
    (gradedTildePullbackSection A 𝒜 f
        (GradedMonoid.GOne.one (A := fun n => ↥(𝒜 n)) : ↥(𝒜 0))).eval (op V) =
      (Stacks.Conormal.gradedPullback f (gradedTildeOf A 𝒜)).one.eval (op V) :=
  Stacks.RingedSpace.eval_pullbackSectionsUnit_congr f.toLRSHom.toShHom
    ((gradedTildeOf A 𝒜).piece 0)
    (algebraSheafSection_one_eval (intPiece (R := CommRingCat.of A) 𝒜)
      (mul_mem_intPiece (R := CommRingCat.of A) 𝒜)
      (one_mem_intPiece (R := CommRingCat.of A) 𝒜) (op ⊤)) V

/-- **Transporting the attached section along an equality of degrees.** Two homogeneous elements
of equal degrees with the same underlying element of `B` have the same attached section, up to
the transport identifying the two degrees. -/
theorem castHom_gradedTildePullbackSection {m m' : ℕ} (e : m = m') (a : ↥(𝒜 m)) (a' : ↥(𝒜 m'))
    (ha : (a : Bg) = (a' : Bg)) (h : (m : ℤ) = (m' : ℤ)) (V : Opens X.carrier) :
    _root_.SheafOfModules.castHom
        (Stacks.Conormal.gradedPullback f (gradedTildeOf A 𝒜)).piece h (op V)
        ((gradedTildePullbackSection A 𝒜 f a).eval (op V)) =
      (gradedTildePullbackSection A 𝒜 f a').eval (op V) := by
  subst e
  obtain rfl : a = a' := Subtype.ext ha
  obtain rfl : h = rfl := Subsingleton.elim h rfl
  exact _root_.SheafOfModules.castHom_rfl _ (op V) _

/-- **`a ↦ gradedTildePullbackSection a` is multiplicative.** No degree transport appears: the
product of a section of degree `k` and one of degree `l` has degree `(k : ℤ) + (l : ℤ)`, which
is definitionally `((k + l : ℕ) : ℤ)`. -/
theorem eval_mul_gradedTildePullbackSection {k l : ℕ} (a : ↥(𝒜 k)) (a' : ↥(𝒜 l))
    (V : Opens X.carrier) :
    ((Stacks.Conormal.gradedPullback f (gradedTildeOf A 𝒜)).mul (k : ℤ) (l : ℤ)).app (op V)
        ((gradedTildePullbackSection A 𝒜 f a).eval (op V))
        ((gradedTildePullbackSection A 𝒜 f a').eval (op V)) =
      (gradedTildePullbackSection A 𝒜 f
        (GradedMonoid.GMul.mul (A := fun n => ↥(𝒜 n)) a a')).eval (op V) :=
  Stacks.RingedSpace.eval_mul_pullbackSectionsUnit f.toLRSHom.toShHom (gradedTildeOf A 𝒜)
    (k : ℤ) (l : ℤ) (gradedTildeSection A 𝒜 a) (gradedTildeSection A 𝒜 a')
    (gradedTildeSection A 𝒜 (GradedMonoid.GMul.mul (A := fun n => ↥(𝒜 n)) a a'))
    (eval_mul_algebraSheafSection (intPiece (R := CommRingCat.of A) 𝒜)
      (mul_mem_intPiece (R := CommRingCat.of A) 𝒜)
      (one_mem_intPiece (R := CommRingCat.of A) 𝒜) (k : ℤ) (l : ℤ) (op ⊤) a a') V

end Nat

end Stacks.AffineGradedAlgebra

end
