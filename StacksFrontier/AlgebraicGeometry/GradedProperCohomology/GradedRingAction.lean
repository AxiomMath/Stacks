module

public import Mathlib.Algebra.Module.Hom
public import Mathlib.Algebra.Module.RingHom
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.CohomologyGradedReesFinite
public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.CohomologyLinear

/-!
# The action of a graded ring on the graded cohomology of a graded module

[Stacks, Tag 0897] part (1) asserts that for `B` a finitely generated graded `A`-algebra and `F`
a quasi-coherent graded `f^* B̃`-module of finite type the graded `B`-module `⨁ₙ Hᵖ(X, Fₙ)` is a
finite `B`-module. **This file puts that `B`-module structure on `⨁ₙ Hᵖ(X, Fₙ)`**, for an
arbitrary sheaf of graded `𝒪_X`-algebras `𝓑` together with the datum that makes `B` act on it: a
family of global homogeneous sections of `𝓑` indexed by the homogeneous elements of `B`,
additive, unital and multiplicative.

The sum is taken over **all** integer degrees, matching
`Stacks.AlgebraicGeometry.GradedProperCohomology.gradedCohomologySum`, so no hypothesis on the
degrees in which `F` is concentrated is needed. For that reason the action is not built as a
`DirectSum.Gmodule` — that would ask for one index type for the ring and for the module — but as
a ring homomorphism into `AddMonoid.End`, read as a module structure by `Module.compHom`.

## Main definitions

* `HomogeneousSections`: the datum. A homogeneous element of degree `k` of `B` names a global
  section of `𝓑ₖ`, additively in the element, carrying `1` to the unit of `𝓑` and a product to
  the product.
* `HomogeneousSections.actHom`: **the action of a homogeneous element of `B` on a graded
  `𝓑`-module**, as a morphism `Fₙ ⟶ Fₘ` with `m = n + k`. The target degree is an argument,
  supplied together with a proof that it equals `n + k`: that is what keeps the degree
  bookkeeping out of the identities proved below.
* `HomogeneousSections.actSum`: the endomorphism of `⨁ₙ Hᵖ(X, Fₙ)` a homogeneous element induces.
* `HomogeneousSections.actRingHom`: **the ring homomorphism
  `B →+* AddMonoid.End (⨁ₙ Hᵖ(X, Fₙ))`**.
* `HomogeneousSections.gradedCohomologyModule`: **the `B`-module structure on
  `⨁ₙ Hᵖ(X, Fₙ)`.**

## Main results

* `HomogeneousSections.actHom_one` and `actHom_comp`: the unit and associativity laws for the
  action, obtained from `SheafOfModules.GradedModule.smulSectionsHom_one` and
  `smulSectionsHom_comp` together with the unital and multiplicative laws of the datum.
* `HomogeneousSections.smul_of`: **the action on a generator.** A homogeneous element of degree
  `k` carries the degree-`n` summand to the degree-`n + k` summand by `Hᵖ(X, −)` of `actHom`.
  This is the characterisation of the module structure that every computation with it goes
  through.

## References

* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 0FQZ](https://stacks.math.columbia.edu/tag/0FQZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology.AffineBase
open scoped DirectSum AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.GradedProperCohomology

/-- **The datum by which a graded ring `B` acts on a graded `𝓑`-module**: every homogeneous
element of degree `k` of `B` names a global section of the degree-`k` piece of `𝓑`, additively in
the element, carrying the unit of `B` to the unit of `𝓑` and a product to the product.

The multiplicative law is stated with the two factors of `𝓑` in the order `l, k` and the
resulting element of `B` in the order `k, l`: that is the order in which the composite
`Fₙ ⟶ F_{n+l} ⟶ F_{n+l+k}` of the actions of `b'` and then `b` is read, and it is what makes the
ring homomorphism of `HomogeneousSections.actRingHom` multiplicative on the nose. -/
structure HomogeneousSections {X : Scheme.{u}}
    (𝓑 : _root_.SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf)
    {A : Type u} [CommRing A] {B : Type u} [CommRing B] [Algebra A B]
    (𝒜 : ℕ → Submodule A B) [_root_.GradedAlgebra 𝒜] where
  /-- The global section of `𝓑ₖ` named by a homogeneous element of degree `k`. -/
  sec : ∀ {k : ℕ}, ↥(𝒜 k) → ((𝓑.piece (k : ℤ)).val.sections)
  /-- It is additive in the element. -/
  eval_add : ∀ {k : ℕ} (b b' : ↥(𝒜 k)) (U : (Opens ↥X)ᵒᵖ),
    (sec (b + b')).eval U = (sec b).eval U + (sec b').eval U
  /-- The unit of `B` names the unit of `𝓑`. -/
  eval_one : ∀ U : (Opens ↥X)ᵒᵖ,
    (sec (GradedMonoid.GOne.one (A := fun n : ℕ => ↥(𝒜 n)))).eval U = 𝓑.one.eval U
  /-- A product of homogeneous elements names the product of the sections. -/
  castHom_mul : ∀ {k l : ℕ} (b : ↥(𝒜 k)) (b' : ↥(𝒜 l)) (U : (Opens ↥X)ᵒᵖ),
    _root_.SheafOfModules.castHom 𝓑.piece
        (by push_cast; ring : (l : ℤ) + (k : ℤ) = ((k + l : ℕ) : ℤ)) U
        ((𝓑.mul (l : ℤ) (k : ℤ)).app U ((sec b').eval U) ((sec b).eval U)) =
      (sec (GradedMonoid.GMul.mul (A := fun n : ℕ => ↥(𝒜 n)) b b')).eval U

namespace HomogeneousSections

open _root_.SheafOfModules.GradedModule

variable {X : Scheme.{u}} {𝓑 : _root_.SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf}
  {A : Type u} [CommRing A] {B : Type u} [CommRing B] [Algebra A B]
  {𝒜 : ℕ → Submodule A B} [_root_.GradedAlgebra 𝒜]
  (S : HomogeneousSections 𝓑 𝒜) (M : _root_.SheafOfModules.GradedModule.{u, u, u} 𝓑)

/-! ### The action on a graded module -/

/-- **The action of a homogeneous element of degree `k` of `B` on a graded `𝓑`-module**, as a
morphism `Fₙ ⟶ Fₘ`. The target degree is an argument, supplied together with a proof that it
equals `n + k`. -/
def actHom {k : ℕ} (b : ↥(𝒜 k)) (n : ℤ) {m : ℤ} (hm : n + (k : ℤ) = m) :
    M.piece n ⟶ M.piece m :=
  smulSectionsHom M n (k : ℤ) (S.sec b) ≫ pieceCast M hm

/-- Following the action by a transport of degrees is again an action, with a different target
degree. -/
theorem actHom_comp_pieceCast {k : ℕ} (b : ↥(𝒜 k)) (n : ℤ) {m m' : ℤ}
    (hm : n + (k : ℤ) = m) (e : m = m') :
    S.actHom M b n hm ≫ pieceCast M e = S.actHom M b n (hm.trans e) := by
  show (smulSectionsHom M n (k : ℤ) (S.sec b) ≫ pieceCast M hm) ≫ pieceCast M e =
    smulSectionsHom M n (k : ℤ) (S.sec b) ≫ pieceCast M (hm.trans e)
  rw [Category.assoc, pieceCast_pieceCast]

/-- Preceding the action by a transport of degrees is again an action, with a different source
degree. -/
theorem pieceCast_comp_actHom {k : ℕ} (b : ↥(𝒜 k)) {n n' : ℤ} (e : n = n') {m : ℤ}
    (hm : n' + (k : ℤ) = m) (hm' : n + (k : ℤ) = m) :
    pieceCast M e ≫ S.actHom M b n' hm = S.actHom M b n hm' := by
  subst e
  rw [pieceCast_rfl, Category.id_comp]

/-- The action is additive in the acting element. -/
theorem actHom_add {k : ℕ} (b b' : ↥(𝒜 k)) (n : ℤ) {m : ℤ} (hm : n + (k : ℤ) = m) :
    S.actHom M (b + b') n hm = S.actHom M b n hm + S.actHom M b' n hm := by
  show smulSectionsHom M n (k : ℤ) (S.sec (b + b')) ≫ pieceCast M hm =
    (smulSectionsHom M n (k : ℤ) (S.sec b) ≫ pieceCast M hm) +
      (smulSectionsHom M n (k : ℤ) (S.sec b') ≫ pieceCast M hm)
  rw [smulSectionsHom_eval_add M n (k : ℤ) (S.eval_add b b'), Preadditive.add_comp]

/-- **The unit of `B` acts by the identity**, up to the transport identifying the source and
target degrees. -/
theorem actHom_one (n : ℤ) {m : ℤ} (hm : n + ((0 : ℕ) : ℤ) = m) (hn : n = m) :
    S.actHom M (GradedMonoid.GOne.one (A := fun j : ℕ => ↥(𝒜 j))) n hm = pieceCast M hn := by
  have h1 : smulSectionsHom M n ((0 : ℕ) : ℤ)
        (S.sec (GradedMonoid.GOne.one (A := fun j : ℕ => ↥(𝒜 j)))) ≫
      pieceCast M (add_zero n) = 𝟙 (M.piece n) := by
    rw [smulSectionsHom_congr M n ((0 : ℕ) : ℤ) S.eval_one]
    exact smulSectionsHom_one M n
  calc S.actHom M (GradedMonoid.GOne.one (A := fun j : ℕ => ↥(𝒜 j))) n hm
      = smulSectionsHom M n ((0 : ℕ) : ℤ)
          (S.sec (GradedMonoid.GOne.one (A := fun j : ℕ => ↥(𝒜 j)))) ≫
          pieceCast M (add_zero n) ≫ pieceCast M hn := by
        rw [pieceCast_pieceCast]; exact rfl
    _ = (smulSectionsHom M n ((0 : ℕ) : ℤ)
          (S.sec (GradedMonoid.GOne.one (A := fun j : ℕ => ↥(𝒜 j)))) ≫
          pieceCast M (add_zero n)) ≫ pieceCast M hn := (Category.assoc _ _ _).symm
    _ = pieceCast M hn := by rw [h1, Category.id_comp]

/-- **The action is associative**: acting by `b'` and then by `b` is acting by their product. -/
theorem actHom_comp {k l : ℕ} (b : ↥(𝒜 k)) (b' : ↥(𝒜 l)) (n : ℤ) {m₁ m₂ : ℤ}
    (h1 : n + (l : ℤ) = m₁) (h2 : m₁ + (k : ℤ) = m₂) (h3 : n + ((k + l : ℕ) : ℤ) = m₂) :
    S.actHom M b' n h1 ≫ S.actHom M b m₁ h2 =
      S.actHom M (GradedMonoid.GMul.mul (A := fun j : ℕ => ↥(𝒜 j)) b b') n h3 := by
  have hnij : n + (l : ℤ) + (k : ℤ) = m₂ := by rw [h1, h2]
  calc S.actHom M b' n h1 ≫ S.actHom M b m₁ h2
      = smulSectionsHom M n (l : ℤ) (S.sec b') ≫ pieceCast M h1 ≫ S.actHom M b m₁ h2 :=
        Category.assoc _ _ _
    _ = smulSectionsHom M n (l : ℤ) (S.sec b') ≫ S.actHom M b (n + (l : ℤ)) hnij := by
        rw [S.pieceCast_comp_actHom M b h1 h2 hnij]
    _ = smulSectionsHom M n (l : ℤ) (S.sec b') ≫
          smulSectionsHom M (n + (l : ℤ)) (k : ℤ) (S.sec b) ≫ pieceCast M hnij := rfl
    _ = S.actHom M (GradedMonoid.GMul.mul (A := fun j : ℕ => ↥(𝒜 j)) b b') n h3 :=
        smulSectionsHom_comp M (by push_cast; ring) h3 hnij (S.sec b') (S.sec b)
          (S.sec (GradedMonoid.GMul.mul (A := fun j : ℕ => ↥(𝒜 j)) b b'))
          (S.castHom_mul b b')

/-! ### The action on the graded cohomology -/

variable (p : ℕ)

/-- The summands of the graded cohomology `⨁ₙ Hᵖ(X, Fₙ)`. -/
abbrev cohPiece (n : ℤ) : Type u := (cohomologyOf X p (pieceModule M n) : Type u)

/-- `Hᵖ(X, −)` of a morphism of `𝒪_X`-modules, as an additive map. -/
abbrev cohAddHom {N P : X.Modules} (φ : N ⟶ P) :
    (cohomologyOf X p N : Type u) →+ (cohomologyOf X p P : Type u) :=
  (((moduleGlobalSections X).rightDerived p).map φ).hom.toAddMonoidHom

/-- `Hᵖ(X, −)` of a composite, read on elements. -/
theorem cohAddHom_comp {N P Q : X.Modules} (φ : N ⟶ P) (ψ : P ⟶ Q)
    (y : (cohomologyOf X p N : Type u)) :
    cohAddHom p (φ ≫ ψ) y = cohAddHom p ψ (cohAddHom p φ y) := by
  show (((moduleGlobalSections X).rightDerived p).map (φ ≫ ψ)).hom y = _
  rw [CategoryTheory.Functor.map_comp]
  rfl

/-- `Hᵖ(X, −)` is additive, read on elements. -/
theorem cohAddHom_add {N P : X.Modules} (φ ψ : N ⟶ P) (y : (cohomologyOf X p N : Type u)) :
    cohAddHom p (φ + ψ) y = cohAddHom p φ y + cohAddHom p ψ y := by
  show (((moduleGlobalSections X).rightDerived p).map (φ + ψ)).hom y = _
  rw [CategoryTheory.Functor.map_add]
  rfl

/-- `Hᵖ(X, −)` sends the identity to the identity, read on elements. -/
theorem cohAddHom_id {N : X.Modules} (y : (cohomologyOf X p N : Type u)) :
    cohAddHom p (𝟙 N) y = y := by
  show (((moduleGlobalSections X).rightDerived p).map (𝟙 N)).hom y = _
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- A summand transported along an equality of degrees is the same summand. -/
theorem of_cohAddHom_pieceCast {n m : ℤ} (e : n = m) (x : cohPiece M p n) :
    DirectSum.of (fun j : ℤ => cohPiece M p j) m (cohAddHom p (pieceCast M e) x) =
      DirectSum.of (fun j : ℤ => cohPiece M p j) n x := by
  subst e
  refine congrArg (DirectSum.of (fun j : ℤ => cohPiece M p j) n) ?_
  rw [pieceCast_rfl]
  exact cohAddHom_id p x

/-- **The endomorphism of `⨁ₙ Hᵖ(X, Fₙ)` induced by a homogeneous element of `B`.** -/
def actSum {k : ℕ} (b : ↥(𝒜 k)) : AddMonoid.End (gradedCohomologySum M p) :=
  DirectSum.toAddMonoid fun n : ℤ =>
    (DirectSum.of (fun j : ℤ => cohPiece M p j) (n + (k : ℤ))).comp
      (cohAddHom p (S.actHom M b n rfl))

/-- **The induced endomorphism on a generator.** -/
theorem actSum_of {k : ℕ} (b : ↥(𝒜 k)) (n : ℤ) (x : cohPiece M p n) :
    S.actSum M p b (DirectSum.of (fun j : ℤ => cohPiece M p j) n x) =
      DirectSum.of (fun j : ℤ => cohPiece M p j) (n + (k : ℤ))
        (cohAddHom p (S.actHom M b n rfl) x) :=
  DirectSum.toAddMonoid_of _ n x

/-- The endomorphism induced by a sum is the sum of the endomorphisms. -/
theorem actSum_add {k : ℕ} (b b' : ↥(𝒜 k)) :
    S.actSum M p (b + b') = S.actSum M p b + S.actSum M p b' := by
  refine DirectSum.addHom_ext fun n x => ?_
  show S.actSum M p (b + b') (DirectSum.of (fun j : ℤ => cohPiece M p j) n x) =
    S.actSum M p b (DirectSum.of (fun j : ℤ => cohPiece M p j) n x) +
      S.actSum M p b' (DirectSum.of (fun j : ℤ => cohPiece M p j) n x)
  rw [S.actSum_of, S.actSum_of, S.actSum_of, S.actHom_add]
  exact (congrArg _ (cohAddHom_add p _ _ x)).trans (map_add _ _ _)

/-- **The unit of `B` induces the identity.** -/
theorem actSum_one :
    S.actSum M p (GradedMonoid.GOne.one (A := fun j : ℕ => ↥(𝒜 j))) = 1 := by
  refine DirectSum.addHom_ext fun n x => ?_
  show S.actSum M p (GradedMonoid.GOne.one (A := fun j : ℕ => ↥(𝒜 j)))
      (DirectSum.of (fun j : ℤ => cohPiece M p j) n x) =
    DirectSum.of (fun j : ℤ => cohPiece M p j) n x
  refine (S.actSum_of M p _ n x).trans ?_
  rw [S.actHom_one M n rfl (show n = n + ((0 : ℕ) : ℤ) by push_cast; ring)]
  exact of_cohAddHom_pieceCast M p _ x

/-- **A product of homogeneous elements induces the composite of the endomorphisms.** -/
theorem actSum_mul {k l : ℕ} (b : ↥(𝒜 k)) (b' : ↥(𝒜 l)) :
    S.actSum M p (GradedMonoid.GMul.mul (A := fun j : ℕ => ↥(𝒜 j)) b b') =
      S.actSum M p b * S.actSum M p b' := by
  refine DirectSum.addHom_ext fun n x => ?_
  have hdeg : n + ((k + l : ℕ) : ℤ) = n + (l : ℤ) + (k : ℤ) := by push_cast; ring
  have h2 : S.actHom M b' n (rfl : n + (l : ℤ) = n + (l : ℤ)) ≫
        S.actHom M b (n + (l : ℤ)) rfl =
      S.actHom M (GradedMonoid.GMul.mul (A := fun j : ℕ => ↥(𝒜 j)) b b') n rfl ≫
        pieceCast M hdeg := by
    rw [S.actHom_comp_pieceCast M _ n rfl hdeg]
    exact S.actHom_comp M b b' n rfl rfl hdeg
  show S.actSum M p (GradedMonoid.GMul.mul (A := fun j : ℕ => ↥(𝒜 j)) b b')
      (DirectSum.of (fun j : ℤ => cohPiece M p j) n x) =
    S.actSum M p b (S.actSum M p b' (DirectSum.of (fun j : ℤ => cohPiece M p j) n x))
  rw [S.actSum_of, S.actSum_of, S.actSum_of,
    ← (congrArg (fun y => cohAddHom p y x) h2).symm.trans (cohAddHom_comp p _ _ x)]
  exact (of_cohAddHom_pieceCast M p hdeg _).symm.trans (congrArg _ (cohAddHom_comp p _ _ x).symm)

/-! ### The module structure -/

/-- The homogeneous actions of degree `k`, as an additive map. -/
def actCompHom (k : ℕ) : ↥(𝒜 k) →+ AddMonoid.End (gradedCohomologySum M p) :=
  AddMonoidHom.mk' (fun b => S.actSum M p b) fun b b' => S.actSum_add M p b b'

/-- The additive map `⨁ₖ 𝒜ₖ →+ End(⨁ₙ Hᵖ(X, Fₙ))` assembled from the homogeneous actions. -/
def actAddHom : (⨁ k : ℕ, ↥(𝒜 k)) →+ AddMonoid.End (gradedCohomologySum M p) :=
  DirectSum.toAddMonoid (S.actCompHom M p)

/-- On a homogeneous element `b ∈ 𝒜ₖ`, `actAddHom` is the homogeneous action `actSum` of `b`. -/
theorem actAddHom_of {k : ℕ} (b : ↥(𝒜 k)) :
    S.actAddHom M p (DirectSum.of (fun j : ℕ => ↥(𝒜 j)) k b) = S.actSum M p b :=
  DirectSum.toAddMonoid_of (S.actCompHom M p) k b

/-- The ring homomorphism `⨁ₖ 𝒜ₖ →+* End(⨁ₙ Hᵖ(X, Fₙ))`. -/
def actRingHomDirectSum : (⨁ k : ℕ, ↥(𝒜 k)) →+* AddMonoid.End (gradedCohomologySum M p) where
  toFun := S.actAddHom M p
  map_zero' := map_zero _
  map_add' := map_add _
  map_one' := by
    rw [DirectSum.one_def, S.actAddHom_of M p]
    exact S.actSum_one M p
  map_mul' z z' := by
    induction z using DirectSum.induction_on with
    | zero => rw [zero_mul, map_zero, zero_mul]
    | of k b =>
        induction z' using DirectSum.induction_on with
        | zero => rw [mul_zero, map_zero, mul_zero]
        | of l b' =>
            rw [DirectSum.of_mul_of, S.actAddHom_of M p, S.actAddHom_of M p, S.actAddHom_of M p]
            exact S.actSum_mul M p b b'
        | add w w' hw hw' => rw [mul_add, map_add, map_add, hw, hw', mul_add]
    | add w w' hw hw' => rw [add_mul, map_add, map_add, hw, hw', add_mul]

/-- **The ring homomorphism `B →+* End(⨁ₙ Hᵖ(X, Fₙ))`** through which `B` acts: the
decomposition of `B` into its homogeneous parts, followed by the homogeneous actions. -/
def actRingHom : B →+* AddMonoid.End (gradedCohomologySum M p) :=
  (S.actRingHomDirectSum M p).comp (DirectSum.decomposeRingEquiv 𝒜).toRingHom

/-- **The `B`-module structure on the graded cohomology `⨁ₙ Hᵖ(X, Fₙ)`.** -/
@[instance_reducible]
def gradedCohomologyModule : Module B (gradedCohomologySum M p) :=
  Module.compHom _ (S.actRingHom M p)

/-- **The action on a generator.** A homogeneous element of degree `k` carries the degree-`n`
summand to the degree-`n + k` summand by `Hᵖ(X, −)` of `actHom`. This is the characterisation of
the module structure of `HomogeneousSections.gradedCohomologyModule`. -/
theorem smul_of {k : ℕ} (b : ↥(𝒜 k)) (n : ℤ) (x : cohPiece M p n) :
    letI := S.gradedCohomologyModule M p
    (b : B) • DirectSum.of (fun j : ℤ => cohPiece M p j) n x =
      DirectSum.of (fun j : ℤ => cohPiece M p j) (n + (k : ℤ))
        (cohAddHom p (S.actHom M b n rfl) x) := by
  show S.actRingHom M p (b : B) (DirectSum.of (fun j : ℤ => cohPiece M p j) n x) = _
  rw [show S.actRingHom M p (b : B) =
      S.actAddHom M p (DirectSum.decompose 𝒜 (b : B)) from rfl,
    DirectSum.decompose_coe, S.actAddHom_of M p]
  exact S.actSum_of M p b n x

end HomogeneousSections

end Stacks.AlgebraicGeometry.GradedProperCohomology

end
