module

public import StacksFrontier.AlgebraicGeometry.FormalFunctions.CohomologyGradedReesFinite
public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.BaseLinearity
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The graded `B`-module `⨁ₙ Hᵖ(X, ℱₙ)` of a graded `𝓑`-module

[Stacks, Tag 0897] part (1) asserts that *the graded `B`-module `H^p(X, ℱ)` is a finite
`B`-module*.  Its conclusion therefore speaks of a `B`-module structure on
`⨁ₙ H^p(X, ℱₙ)`, and that structure is not an extra hypothesis: it is the action induced by
the action of `𝓑` on `ℱ` through functoriality of cohomology, once `𝓑` is known to be
`f^* B̃`.  This file constructs it.

The only thing the construction uses from `𝓑 = f^* B̃` is the resulting graded ring map
`B → ⨁ₖ Γ(X, 𝓑ₖ)`, i.e. the global homogeneous section of `𝓑ₖ` attached to a homogeneous
element of `B` of degree `k`.  That datum is packaged as
`Stacks.AlgebraicGeometry.GradedProperCohomology.HomogeneousSectionAssignment`.

Given it, a homogeneous `b` of degree `k` acts on `ℱₙ` by multiplication by its section
followed by the transport `n + k = m`, which is `actHom`; applying `H^p(X, −)` and summing
over the degrees gives an additive endomorphism `actSum` of `⨁ₙ H^p(X, ℱₙ)`, and the graded
laws `actHom_add`, `actHom_zero`, `actHom_one` and `actHom_comp` make `b ↦ actSum b` a ring
homomorphism `B →+* AddMonoid.End (⨁ₙ H^p(X, ℱₙ))`, hence a `B`-module structure.

This is the general form of the construction that
`Stacks.Cohomology.FormalFunctions.cohomologyGradedModule` carries out for the Rees algebra
`B = ⨁ₙ Iⁿ` of an ideal, where the graded module is indexed by `ℕ` on both sides; here the algebra
is an arbitrary `ℕ`-graded finitely generated `A`-algebra and the module is `ℤ`-graded, which is
the shape of [Stacks, Tag 0897]. The degreewise identities are proved from the generic lemmas of
`SheafOfModules.GradedModule` (`smulSectionsHom_congr`, `smulSectionsHom_eval_add`,
`smulSectionsHom_eval_zero`, `smulSectionsHom_one`, `smulSectionsHom_comp`).

## Main definitions

* `HomogeneousSectionAssignment`: the global homogeneous sections of `𝓑` attached to the
  homogeneous elements of `B`.
* `cohoMap`: `H^p(X, −)` on a morphism, as a homomorphism of additive groups.
* `actHom`: the action of a homogeneous element of `B` on the pieces of `ℱ`.
* `actSum`, `actAddHom`, `actRingHom`: that action on `⨁ₙ H^p(X, ℱₙ)`, degreewise, over
  `⨁ₖ 𝒜ₖ`, and over `B`.
* `gradedCohomologyModule`: **the graded `B`-module `⨁ₙ H^p(X, ℱₙ)`** of [Stacks, Tag 0897]
  part (1).
* `reesHomogeneousSections`: the `HomogeneousSectionAssignment` datum for the Rees algebra.

## Main results

* `actHom_add`, `actHom_zero`, `actHom_one`, `actHom_comp`: the graded module laws of the
  action on the pieces.
* `actSum_add`, `actSum_zero`, `actSum_one`, `actSum_mul`: the same laws on the graded
  cohomology.
* `gradedCohomologyModule_smul_of`: the action of a homogeneous element on a homogeneous
  class, which is what pins the module structure down.

## Implementation notes

The acting ring is `ℕ`-graded and the module is `ℤ`-graded, so `DirectSum.Gmodule` does not
apply without a `VAdd ℕ ℤ` instance; the ring homomorphism is therefore assembled by hand
from `DirectSum.toAddMonoid` and `DirectSum.decomposeRingEquiv`, and the degree bookkeeping
is carried by `SheafOfModules.GradedModule.pieceCast` exactly as in the Rees case.

No `@[stacks]` attribute is attached: this is the construction of the object whose finiteness
[Stacks, Tag 0897] part (1) asserts, not that assertion.

## References

* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 0FQZ](https://stacks.math.columbia.edu/tag/0FQZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules.GradedModule
open scoped AlgebraicGeometry ModuleCat.Algebra

universe u

namespace Stacks.AlgebraicGeometry.GradedProperCohomology

attribute [local instance] HasDerivedCategory.standard

variable {X : Scheme.{u}}
  {𝓑 : _root_.SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf}

/-! ### A ring map into the additive endomorphisms is a module structure -/

/-- A ring homomorphism into the additive endomorphisms of an abelian group is a module
structure on that group. -/
@[instance_reducible, ega "0 13.6.6"]
def moduleOfRingHom {R M : Type*} [Ring R] [AddCommGroup M] (φ : R →+* AddMonoid.End M) :
    Module R M where
  smul r x := φ r x
  one_smul x := by
    change φ 1 x = x
    rw [map_one]; rfl
  mul_smul r s x := by
    change φ (r * s) x = φ r (φ s x)
    rw [map_mul]; rfl
  smul_zero r := map_zero (φ r)
  smul_add r x y := map_add (φ r) x y
  add_smul r s x := by
    change φ (r + s) x = φ r x + φ s x
    rw [map_add]; rfl
  zero_smul x := by
    change φ 0 x = 0
    rw [map_zero]; rfl

/-! ### The global homogeneous sections attached to the homogeneous elements of `B` -/

/-- **The global homogeneous sections of `𝓑` attached to the homogeneous elements of `B`.**
This is the part of the source's `𝓑 = f^* B̃` that the graded `B`-action on the cohomology
uses: a degree-preserving, additive, multiplicative and unital assignment of a global section
of `𝓑ₖ` to each homogeneous element of `B` of degree `k`. -/
structure HomogeneousSectionAssignment {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (𝒜 : ℕ → Submodule A B) [_root_.GradedAlgebra 𝒜]
    (𝓑 : _root_.SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf) where
  /-- The global section of `𝓑ₖ` attached to a homogeneous element of degree `k`. -/
  sect {k : ℕ} : ↥(𝒜 k) → (𝓑.piece (k : ℤ)).val.sections
  /-- The assignment is additive. -/
  eval_add {k : ℕ} (b b' : ↥(𝒜 k)) (U : (TopologicalSpace.Opens X)ᵒᵖ) :
    (sect (b + b')).eval U = (sect b).eval U + (sect b').eval U
  /-- The zero element is sent to the zero section. -/
  eval_zero {k : ℕ} (U : (TopologicalSpace.Opens X)ᵒᵖ) :
    (sect (0 : ↥(𝒜 k))).eval U = 0
  /-- The unit is sent to the unit section. -/
  eval_one (U : (TopologicalSpace.Opens X)ᵒᵖ) :
    (sect (GradedMonoid.GOne.one (A := fun k : ℕ => ↥(𝒜 k)))).eval U = 𝓑.one.eval U
  /-- The assignment is multiplicative: the product of the sections attached to two
  homogeneous elements is the section attached to any homogeneous element whose underlying
  element of `B` is their product. -/
  castHom_mul {k l m : ℕ} (b : ↥(𝒜 k)) (b' : ↥(𝒜 l)) (c : ↥(𝒜 m))
      (hc : (c : B) = (b : B) * (b' : B)) (hkl : (k : ℤ) + (l : ℤ) = (m : ℤ))
      (U : (TopologicalSpace.Opens X)ᵒᵖ) :
    _root_.SheafOfModules.castHom 𝓑.piece hkl U
        ((𝓑.mul (k : ℤ) (l : ℤ)).app U ((sect b).eval U) ((sect b').eval U)) =
      (sect c).eval U

/-! ### Cohomology as an additive functor -/

/-- `Hᵖ(X, −)` on a morphism of module sheaves, as a homomorphism of additive groups. -/
def cohoMap (p : ℕ) {N N' : X.Modules} (φ : N ⟶ N') :
    ↥(cohomologyOf X p N) →+ ↥(cohomologyOf X p N') :=
  (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived p).map
    φ).hom.toAddMonoidHom

/-- `cohoMap p φ` is the map induced by `φ` on `Hᵖ`. -/
theorem cohoMap_apply (p : ℕ) {N N' : X.Modules} (φ : N ⟶ N') (x : ↥(cohomologyOf X p N)) :
    cohoMap p φ x =
      (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived p).map φ).hom x := rfl

/-- `Hᵖ(X, −)` sends the identity to the identity. -/
theorem cohoMap_id (p : ℕ) (N : X.Modules) (x : ↥(cohomologyOf X p N)) :
    cohoMap p (𝟙 N) x = x := by
  rw [cohoMap_apply, CategoryTheory.Functor.map_id]
  rfl

/-- `Hᵖ(X, −)` sends a composite to the composite of the induced maps. -/
theorem cohoMap_comp (p : ℕ) {N N' N'' : X.Modules} (φ : N ⟶ N') (ψ : N' ⟶ N'')
    (x : ↥(cohomologyOf X p N)) :
    cohoMap p ψ (cohoMap p φ x) = cohoMap p (φ ≫ ψ) x := by
  rw [cohoMap_apply, cohoMap_apply, cohoMap_apply, CategoryTheory.Functor.map_comp]
  rfl

/-- `Hᵖ(X, −)` is additive on morphisms. -/
theorem cohoMap_add (p : ℕ) {N N' : X.Modules} (φ ψ : N ⟶ N') (x : ↥(cohomologyOf X p N)) :
    cohoMap p (φ + ψ) x = cohoMap p φ x + cohoMap p ψ x := by
  rw [cohoMap_apply, cohoMap_apply, cohoMap_apply, CategoryTheory.Functor.map_add]
  rfl

/-- `Hᵖ(X, −)` sends the zero morphism to zero. -/
theorem cohoMap_zero (p : ℕ) {N N' : X.Modules} (x : ↥(cohomologyOf X p N)) :
    cohoMap p (0 : N ⟶ N') x = 0 := by
  rw [cohoMap_apply, CategoryTheory.Functor.map_zero]
  rfl

/-! ### The action of a homogeneous element on the pieces of a graded module -/

section Act

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] {𝒜 : ℕ → Submodule A B}
  [_root_.GradedAlgebra 𝒜] (σ : HomogeneousSectionAssignment 𝒜 𝓑)
  (F : _root_.SheafOfModules.GradedModule 𝓑)

/-- **The action of a homogeneous element of degree `k` of `B` on a graded `𝓑`-module**, as a
morphism `ℱₙ ⟶ ℱₘ`. -/
def actHom {k : ℕ} (b : ↥(𝒜 k)) (n : ℤ) {m : ℤ} (hm : n + (k : ℤ) = m) :
    F.piece n ⟶ F.piece m :=
  smulSectionsHom F n (k : ℤ) (σ.sect b) ≫ pieceCast F hm

/-- Following the action by a transport of degrees is again an action. -/
theorem actHom_comp_pieceCast {k : ℕ} (b : ↥(𝒜 k)) (n : ℤ) {m m' : ℤ}
    (hm : n + (k : ℤ) = m) (e : m = m') :
    actHom σ F b n hm ≫ pieceCast F e = actHom σ F b n (hm.trans e) := by
  rw [actHom, actHom, Category.assoc, pieceCast_pieceCast]

/-- The action is additive in the acting element. -/
theorem actHom_add {k : ℕ} (b b' : ↥(𝒜 k)) (n : ℤ) {m : ℤ} (hm : n + (k : ℤ) = m) :
    actHom σ F (b + b') n hm = actHom σ F b n hm + actHom σ F b' n hm := by
  rw [actHom, actHom, actHom, smulSectionsHom_eval_add F n (k : ℤ) (σ.eval_add b b'),
    Preadditive.add_comp]

/-- The zero element acts by zero. -/
theorem actHom_zero {k : ℕ} (n : ℤ) {m : ℤ} (hm : n + (k : ℤ) = m) :
    actHom σ F (0 : ↥(𝒜 k)) n hm = 0 := by
  rw [actHom, smulSectionsHom_eval_zero F n (k : ℤ) (σ.eval_zero), Limits.zero_comp]

/-- Preceding the action by a transport of degrees is again an action. -/
theorem pieceCast_comp_actHom {k : ℕ} (b : ↥(𝒜 k)) {n n' : ℤ} (e : n = n')
    {m : ℤ} (hm : n' + (k : ℤ) = m) (hm' : n + (k : ℤ) = m) :
    pieceCast F e ≫ actHom σ F b n' hm = actHom σ F b n hm' := by
  subst e
  rw [pieceCast_rfl, Category.id_comp]

/-- **The unit of `B` acts by the identity**, up to the transport identifying the source and
target degrees. -/
theorem actHom_one (n : ℤ) {m : ℤ} (hm : n + ((0 : ℕ) : ℤ) = m) (hn : n = m) :
    actHom σ F (GradedMonoid.GOne.one (A := fun j : ℕ => ↥(𝒜 j))) n hm = pieceCast F hn := by
  have h1 : smulSectionsHom F n ((0 : ℕ) : ℤ)
        (σ.sect (GradedMonoid.GOne.one (A := fun j : ℕ => ↥(𝒜 j)))) ≫
      pieceCast F (add_zero n) = 𝟙 (F.piece n) := by
    rw [smulSectionsHom_congr F n ((0 : ℕ) : ℤ) σ.eval_one]
    exact smulSectionsHom_one F n
  calc actHom σ F (GradedMonoid.GOne.one (A := fun j : ℕ => ↥(𝒜 j))) n hm
      = smulSectionsHom F n ((0 : ℕ) : ℤ)
          (σ.sect (GradedMonoid.GOne.one (A := fun j : ℕ => ↥(𝒜 j)))) ≫
          pieceCast F (add_zero n) ≫ pieceCast F hn := by
        rw [pieceCast_pieceCast]; exact rfl
    _ = (smulSectionsHom F n ((0 : ℕ) : ℤ)
          (σ.sect (GradedMonoid.GOne.one (A := fun j : ℕ => ↥(𝒜 j)))) ≫
          pieceCast F (add_zero n)) ≫ pieceCast F hn := (Category.assoc _ _ _).symm
    _ = pieceCast F hn := by rw [h1, Category.id_comp]

/-- **The action of `B` is associative**: acting by `b` and then by `b'` is acting by any
homogeneous element whose underlying element of `B` is the product. -/
theorem actHom_comp {k l m : ℕ} (b : ↥(𝒜 k)) (b' : ↥(𝒜 l)) (c : ↥(𝒜 m))
    (hc : (c : B) = (b : B) * (b' : B)) (hkl : (k : ℤ) + (l : ℤ) = (m : ℤ))
    (n : ℤ) {m₁ m₂ : ℤ}
    (h1 : n + (k : ℤ) = m₁) (h2 : m₁ + (l : ℤ) = m₂) (h3 : n + (m : ℤ) = m₂) :
    actHom σ F b n h1 ≫ actHom σ F b' m₁ h2 = actHom σ F c n h3 := by
  have hnij : n + (k : ℤ) + (l : ℤ) = m₂ := by rw [h1, h2]
  calc actHom σ F b n h1 ≫ actHom σ F b' m₁ h2
      = smulSectionsHom F n (k : ℤ) (σ.sect b) ≫ pieceCast F h1 ≫ actHom σ F b' m₁ h2 :=
        Category.assoc _ _ _
    _ = smulSectionsHom F n (k : ℤ) (σ.sect b) ≫ actHom σ F b' (n + (k : ℤ)) hnij := by
        rw [pieceCast_comp_actHom σ F b' h1 h2 hnij]
    _ = smulSectionsHom F n (k : ℤ) (σ.sect b) ≫
          smulSectionsHom F (n + (k : ℤ)) (l : ℤ) (σ.sect b') ≫ pieceCast F hnij := rfl
    _ = actHom σ F c n h3 :=
        smulSectionsHom_comp F hkl h3 hnij (σ.sect b) (σ.sect b') (σ.sect c)
          (σ.castHom_mul b b' c hc hkl)

/-! ### The graded `B`-module `⨁ₙ Hᵖ(X, ℱₙ)` -/

variable (p : ℕ)

/-- Transport along an equality of degrees does not change a class in the graded cohomology. -/
theorem of_cohoMap_pieceCast {i j : ℤ} (e : i = j)
    (y : ↥(cohomologyOf X p (pieceModule F i))) :
    DirectSum.of (fun n : ℤ => ↥(cohomologyOf X p (pieceModule F n))) j
        (cohoMap p (pieceCast F e) y) =
      DirectSum.of (fun n : ℤ => ↥(cohomologyOf X p (pieceModule F n))) i y := by
  subst e
  rw [pieceCast_rfl]
  exact congrArg (DirectSum.of (fun n : ℤ => ↥(cohomologyOf X p (pieceModule F n))) i)
    (cohoMap_id p _ y)

/-- **The action of a homogeneous element of degree `k` of `B` on `⨁ₙ Hᵖ(X, ℱₙ)`.** -/
def actSum {k : ℕ} (b : ↥(𝒜 k)) : gradedCohomologySum F p →+ gradedCohomologySum F p :=
  DirectSum.toAddMonoid fun n : ℤ =>
    (DirectSum.of (fun m : ℤ => ↥(cohomologyOf X p (pieceModule F m)))
      (n + (k : ℤ))).comp (cohoMap p (actHom σ F b n rfl))

/-- A homogeneous `b` of degree `k` sends a class in `Hᵖ(X, ℱₙ)` to the class in
`Hᵖ(X, ℱₙ₊ₖ)` obtained by applying `Hᵖ(X, −)` to `actHom σ F b n rfl`. -/
theorem actSum_of {k : ℕ} (b : ↥(𝒜 k)) (n : ℤ)
    (x : ↥(cohomologyOf X p (pieceModule F n))) :
    actSum σ F p b (DirectSum.of (fun m : ℤ => ↥(cohomologyOf X p (pieceModule F m))) n x) =
      DirectSum.of (fun m : ℤ => ↥(cohomologyOf X p (pieceModule F m))) (n + (k : ℤ))
        (cohoMap p (actHom σ F b n rfl) x) :=
  DirectSum.toAddMonoid_of (fun j : ℤ =>
    (DirectSum.of (fun m : ℤ => ↥(cohomologyOf X p (pieceModule F m)))
      (j + (k : ℤ))).comp (cohoMap p (actHom σ F b j rfl))) n x

/-- The action is additive in the acting element. -/
theorem actSum_add {k : ℕ} (b b' : ↥(𝒜 k)) :
    actSum σ F p (b + b') = actSum σ F p b + actSum σ F p b' := by
  refine DirectSum.addHom_ext fun n x => ?_
  rw [AddMonoidHom.add_apply, actSum_of, actSum_of, actSum_of, actHom_add]
  exact (congrArg _ (cohoMap_add p _ _ x)).trans (map_add _ _ _)

/-- The zero element acts by zero. -/
theorem actSum_zero {k : ℕ} : actSum σ F p (0 : ↥(𝒜 k)) = 0 := by
  refine DirectSum.addHom_ext fun n x => ?_
  rw [actSum_of, actHom_zero]
  exact (congrArg _ (cohoMap_zero p x)).trans (map_zero _)

/-- **The unit of `B` acts by the identity.** -/
theorem actSum_one :
    actSum σ F p (GradedMonoid.GOne.one (A := fun j : ℕ => ↥(𝒜 j))) =
      AddMonoidHom.id (gradedCohomologySum F p) := by
  refine DirectSum.addHom_ext fun n x => ?_
  have hn : n = n + ((0 : ℕ) : ℤ) := by push_cast; ring
  rw [actSum_of, actHom_one σ F n rfl hn, of_cohoMap_pieceCast]
  rfl

/-- **The action of `B` is multiplicative.** -/
theorem actSum_mul {k l m : ℕ} (b : ↥(𝒜 k)) (b' : ↥(𝒜 l)) (c : ↥(𝒜 m))
    (hc : (c : B) = (b : B) * (b' : B)) (hkl : (k : ℤ) + (l : ℤ) = (m : ℤ)) :
    actSum σ F p c = (actSum σ F p b).comp (actSum σ F p b') := by
  refine DirectSum.addHom_ext fun n x => ?_
  have h3 : n + (m : ℤ) = n + (l : ℤ) + (k : ℤ) := by rw [← hkl]; ring
  have hcomp := actHom_comp σ F b' b c (hc.trans (mul_comm _ _)) (by rw [← hkl]; ring) n rfl rfl h3
  rw [AddMonoidHom.comp_apply, actSum_of, actSum_of, actSum_of, ← of_cohoMap_pieceCast F p h3]
  refine congrArg _ ((cohoMap_comp p _ _ x).trans ?_)
  exact (congrArg (fun φ => cohoMap p φ x)
    ((actHom_comp_pieceCast σ F c n rfl h3).trans hcomp.symm)).trans (cohoMap_comp p _ _ x).symm

/-! ### The ring homomorphism and the module structure -/

/-- The action of `⨁ₖ 𝒜ₖ` on `⨁ₙ Hᵖ(X, ℱₙ)`, as a homomorphism into the additive
endomorphisms. -/
def actAddHom : (DirectSum ℕ fun k : ℕ => ↥(𝒜 k)) →+ AddMonoid.End (gradedCohomologySum F p) :=
  DirectSum.toAddMonoid fun k : ℕ =>
    { toFun := fun b : ↥(𝒜 k) => actSum σ F p b
      map_zero' := actSum_zero σ F p
      map_add' := fun b b' => actSum_add σ F p b b' }

/-- On a homogeneous element `b` of degree `k`, `actAddHom` is `actSum σ F p b`. -/
theorem actAddHom_of (k : ℕ) (b : ↥(𝒜 k)) :
    actAddHom σ F p (DirectSum.of (fun j : ℕ => ↥(𝒜 j)) k b) = actSum σ F p b :=
  DirectSum.toAddMonoid_of (fun k : ℕ =>
    { toFun := fun b : ↥(𝒜 k) => actSum σ F p b
      map_zero' := actSum_zero σ F p
      map_add' := fun b b' => actSum_add σ F p b b' }) k b

/-- The action of `⨁ₖ 𝒜ₖ` is multiplicative. -/
theorem actAddHom_mul (u v : DirectSum ℕ fun k : ℕ => ↥(𝒜 k)) :
    actAddHom σ F p (u * v) = actAddHom σ F p u * actAddHom σ F p v := by
  induction u using DirectSum.induction_on with
  | zero => rw [zero_mul, map_zero, zero_mul]
  | of k b =>
      induction v using DirectSum.induction_on with
      | zero => rw [mul_zero, map_zero, mul_zero]
      | of l b' =>
          rw [DirectSum.of_mul_of, actAddHom_of, actAddHom_of, actAddHom_of]
          exact actSum_mul σ F p b b'
            (GradedMonoid.GMul.mul (A := fun j : ℕ => ↥(𝒜 j)) b b') rfl (by push_cast; ring)
      | add v v' hv hv' => rw [mul_add, map_add, hv, hv', map_add, mul_add]
  | add u u' hu hu' => rw [add_mul, map_add, hu, hu', map_add, add_mul]

/-- **The action of `B` on `⨁ₙ Hᵖ(X, ℱₙ)`**, as a ring homomorphism into the additive
endomorphisms. -/
def actRingHom : B →+* AddMonoid.End (gradedCohomologySum F p) where
  toFun b := actAddHom σ F p (DirectSum.decomposeRingEquiv 𝒜 b)
  map_one' := by
    rw [map_one]
    change actAddHom σ F p (1 : DirectSum ℕ fun k : ℕ => ↥(𝒜 k)) = 1
    rw [show (1 : DirectSum ℕ fun k : ℕ => ↥(𝒜 k)) = DirectSum.of (fun j : ℕ => ↥(𝒜 j)) 0
      (GradedMonoid.GOne.one (A := fun j : ℕ => ↥(𝒜 j))) from rfl, actAddHom_of]
    exact actSum_one σ F p
  map_mul' x y := by
    rw [map_mul]
    exact actAddHom_mul σ F p _ _
  map_zero' := by rw [map_zero, map_zero]
  map_add' x y := by rw [map_add, map_add]

/-- **The graded `B`-module `⨁ₙ Hᵖ(X, ℱₙ)` of [Stacks, Tag 0897] part (1)**, with the action
induced by the action of `𝓑` on the graded module `ℱ` through functoriality of cohomology. -/
@[instance_reducible]
def gradedCohomologyModule : Module B (gradedCohomologySum F p) :=
  moduleOfRingHom (actRingHom σ F p)

/-- The action of a homogeneous element on a homogeneous class. -/
theorem gradedCohomologyModule_smul_of {k : ℕ} (b : ↥(𝒜 k)) (n : ℤ)
    (x : ↥(cohomologyOf X p (pieceModule F n))) :
    letI := gradedCohomologyModule σ F p
    (b : B) • (DirectSum.of (fun m : ℤ => ↥(cohomologyOf X p (pieceModule F m))) n x) =
      DirectSum.of (fun m : ℤ => ↥(cohomologyOf X p (pieceModule F m))) (n + (k : ℤ))
        (cohoMap p (actHom σ F b n rfl) x) := by
  show actRingHom σ F p (b : B) _ = _
  show actAddHom σ F p (DirectSum.decomposeRingEquiv 𝒜 (b : B)) _ = _
  rw [show DirectSum.decomposeRingEquiv 𝒜 (b : B)
      = DirectSum.of (fun j : ℕ => ↥(𝒜 j)) k b from DirectSum.decompose_coe 𝒜 b,
    actAddHom_of]
  exact actSum_of σ F p b n x

end Act

/-! ### The Rees algebra: the homogeneous sections of `⨁ₙ ℐⁿ` -/

section Rees

open Stacks.Blowup Stacks.Cohomology.FormalFunctions

variable {A : Type u} [CommRing A] (I : Ideal A) (Y : Over (Spec (.of A)))

/-- The underlying element of `Iᵏ⁺ˡ` of a homogeneous element of the Rees algebra whose image
in `reesAlgebra I` is a product of homogeneous elements is the product of their underlying
elements. This is `reesElt_mul` for an arbitrary homogeneous element of the right degree, which
is the form `HomogeneousSectionAssignment` asks multiplicativity in. -/
theorem reesElt_of_coe_mul {k l m : ℕ} (b : ↥(reesGrading I k)) (b' : ↥(reesGrading I l))
    (c : ↥(reesGrading I m))
    (hc : (c : ↥(reesAlgebra I)) = (b : ↥(reesAlgebra I)) * (b' : ↥(reesAlgebra I)))
    (hkl : (k : ℤ) + (l : ℤ) = (m : ℤ)) :
    reesElt I c = reesElt I b * reesElt I b' := by
  have hm : k + l = m := by exact_mod_cast hkl
  have hprod : ((c : ↥(reesAlgebra I)) : Polynomial A) =
      Polynomial.monomial (k + l)
        ((((b : ↥(reesAlgebra I)) : Polynomial A).coeff k) *
          (((b' : ↥(reesAlgebra I)) : Polynomial A).coeff l)) := by
    rw [hc, Subalgebra.coe_mul, coe_eq_monomial I b.2, coe_eq_monomial I b'.2,
      Polynomial.monomial_mul_monomial]
    simp
  rw [reesElt, reesElt, reesElt, coe_reesGradingEquivPow_symm, coe_reesGradingEquivPow_symm,
    coe_reesGradingEquivPow_symm, hprod, hm, Polynomial.coeff_monomial, ite_eq_left rfl]

/-- **The global homogeneous sections of `𝓑 = ⨁ₙ ℐⁿ` attached to the homogeneous elements of
the Rees algebra `B = ⨁ₙ Iⁿ`**, as a `HomogeneousSectionAssignment`. -/
def reesHomogeneousSections :
    HomogeneousSectionAssignment (reesGrading I) (baseReesAlgebra I Y) where
  sect := gradedReesSection I Y
  eval_add := eval_gradedReesSection_add I Y
  eval_zero := eval_gradedReesSection_zero I Y
  eval_one := eval_gradedReesSection_one I Y
  castHom_mul b b' c hc hkl U :=
    castHom_mul_gradedReesSection I Y b b' c (reesElt_of_coe_mul I b b' c hc hkl) hkl U

end Rees

end Stacks.AlgebraicGeometry.GradedProperCohomology

end
