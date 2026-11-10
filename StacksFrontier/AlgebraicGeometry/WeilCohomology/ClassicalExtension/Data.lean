module

public import StacksFrontier.Algebra.GradedModule.ExternallyGradedRing
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalExtension.Components
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilData
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# A classical Weil cohomology theory on all smooth projective schemes

A classical Weil cohomology theory `H^*` (Stacks 0FGV) is defined on smooth projective
varieties. Every smooth projective scheme `X` over `k` is the disjoint union of its connected
components `X_1, …, X_n`, which are smooth projective varieties
(`StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalExtension.Components`), and Stacks 0FH2
uses that "every smooth projective scheme is canonically a disjoint union of smooth projective
varieties" to pass from the varieties to all smooth projective schemes. This file makes that
passage: it extends `H^*` to the data (D0), (D1), (D2), (D3) of Section 45.9 (Tag 0FHA) on the
category of all smooth projective schemes over `k`, by

* (D0) `F(1) = F`;
* (D1) `H^*(X) = ∏_i H^*(X_i)`, graded by `H^n(X) = ∏_i H^n(X_i)`, with pullback along
  `f : X ⟶ Y` given on the factor `X_i` by pullback along the restriction `X_i ⟶ Y_j` of `f`
  to `X_i` and the component `Y_j` it maps into;
* (D2) `γ(α) = (γ(α|_{X_i}))_i`, for `α|_{X_i}` the restriction of `α` to the open subscheme
  `X_i`, which is its Gysin pullback along the inclusion;
* (D3) `∫_X a = ∑_i ∫_{X_i} a_i` for `X` nonempty and equidimensional.

The axioms (A), (B), (C) for these data are proved in the other files of this directory.

## Main definitions

* `Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.totalH`: the total cohomology
  `⨁_n H^n(V)` of a smooth projective variety, an `F`-algebra.
* `Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.pullTotal`: pullback on it.
* `Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.extH`, `extGrade`, `extPull`: the
  extended cohomology, its grading and its pullbacks.
* `Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.extCycleClass`,
  `Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.extTrace`: the extended cycle class and
  trace maps.
* `Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.toWeilData`: the data (D0)–(D3).

## Implementation notes

The components are indexed by `Fin n` (`SmoothProjectiveScheme.Idx`) rather than by the
type of connected components, which lives in the universe of the schemes: the product
`∏_i H^*(X_i)` then lies in the universe of the coefficient field, as (D1) requires.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry DirectSum Stacks.Chow

universe u v

namespace Stacks.WeilCohomology

open SmoothProjectiveScheme

namespace ClassicalWeilCohomologyTheory

variable {k : Type u} [Field k] [IsAlgClosed k] {F : Type v} [Field F] [CharZero F]
  (T : ChowClassicalWeilCohomologyTheory.{u, v, v} k F)

/-! ### Cohomology of a variety as an algebra -/

/-- The total cohomology `H^*(V) = ⨁_n H^n(V)` of a smooth projective variety, an `F`-algebra. -/
abbrev totalH (V : (SmoothProjective k).FullSubcategory) : Type v :=
  ⨁ n, (T.H V).piece n

/-- Pullback `f^* : H^*(V') → H^*(V)` on total cohomology, an `F`-algebra homomorphism. -/
def pullTotal {V V' : (SmoothProjective k).FullSubcategory} (f : V ⟶ V') :
    T.totalH V' →ₐ[F] T.totalH V :=
  ExternallyGradedAlgebra.totalMap (T.pullback f) (T.pullback_one f) (T.pullback_mul f)

/-- Pullback on total cohomology acts on the summand `H^n(V')` as `f^* : H^n(V') → H^n(V)`. -/
@[simp]
theorem pullTotal_lof {V V' : (SmoothProjective k).FullSubcategory} (f : V ⟶ V') (n : ℤ)
    (a : (T.H V').piece n) :
    T.pullTotal f (lof F ℤ (T.H V').piece n a) = lof F ℤ (T.H V).piece n (T.pullback f n a) :=
  ExternallyGradedAlgebra.totalMap_of _ _ _ n a

/-- Pullback along the identity is the identity on total cohomology. -/
theorem pullTotal_id (V : (SmoothProjective k).FullSubcategory) :
    T.pullTotal (𝟙 V) = AlgHom.id F _ :=
  DirectSum.algHom_ext' F _ fun n ↦ LinearMap.ext fun a ↦ by
    simp [T.pullback_id]

/-- Pullback on total cohomology is contravariantly functorial: `(f ≫ g)^* = f^* ∘ g^*`. -/
theorem pullTotal_comp {V V' V'' : (SmoothProjective k).FullSubcategory} (f : V ⟶ V')
    (g : V' ⟶ V'') : T.pullTotal (f ≫ g) = (T.pullTotal f).comp (T.pullTotal g) :=
  DirectSum.algHom_ext' F _ fun n ↦ LinearMap.ext fun a ↦ by
    simp [T.pullback_comp]

/-- Pullback on total cohomology preserves the degree-`n` part. -/
theorem pullTotal_mem_grade {V V' : (SmoothProjective k).FullSubcategory} (f : V ⟶ V')
    {n : ℤ} {x : T.totalH V'} (hx : x ∈ (T.H V').grade n) : T.pullTotal f x ∈ (T.H V).grade n :=
  ExternallyGradedAlgebra.totalMap_mem_grade _ _ _ n hx

/-- Graded commutativity of the cohomology of a variety, on total cohomology. -/
theorem totalH_mul_eq (V : (SmoothProjective k).FullSubcategory) (i j : ℤ) (a b : T.totalH V)
    (ha : a ∈ (T.H V).grade i) (hb : b ∈ (T.H V).grade j) :
    a * b = (Int.negOnePow (i * j) : ℤ) • (b * a) := by
  obtain ⟨a, rfl⟩ := ha
  obtain ⟨b, rfl⟩ := hb
  rw [lof_eq_of, lof_eq_of, of_mul_of, of_mul_of, ← Int.cast_smul_eq_zsmul F, ← of_smul,
    DifferentialGraded.intCast_negOnePow]
  exact of_eq_of_gradedMonoid_eq (Sigma.ext (add_comm i j)
    ((T.gradedComm V).graded_comm i j a b))

/-! ### The extended cohomology -/

/-- **The cohomology `H^*(X) = ∏_i H^*(X_i)`** of a smooth projective scheme `X` with connected
components `X_i`. -/
abbrev extH (X : (SmoothProjectiveScheme k).FullSubcategory) : Type v :=
  ∀ i : Idx X, T.totalH (compAt X i)

/-- The grading `H^n(X) = ∏_i H^n(X_i)`. -/
abbrev extGrade (X : (SmoothProjectiveScheme k).FullSubcategory) (n : ℤ) : Submodule F (T.extH X) :=
  GradedAlgebra.piGrade (fun i ↦ (T.H (compAt X i)).grade) n

/-- An element of `H^*(X)` has degree `n` if and only if each of its components does. -/
theorem mem_extGrade {X : (SmoothProjectiveScheme k).FullSubcategory} {n : ℤ} {x : T.extH X} :
    x ∈ T.extGrade X n ↔ ∀ i, x i ∈ (T.H (compAt X i)).grade n :=
  GradedAlgebra.mem_piGrade _

/-- The grading `H^n(X) = ∏_i H^n(X_i)` makes `H^*(X)` a graded algebra. -/
instance (X : (SmoothProjectiveScheme k).FullSubcategory) : _root_.GradedAlgebra (T.extGrade X) :=
  GradedAlgebra.pi _

/-- Pullback along two morphisms into components which agree as morphisms into `X` agree. -/
theorem pullTotal_congr {X : (SmoothProjectiveScheme k).FullSubcategory}
    {V : (SmoothProjective k).FullSubcategory}
    {j j' : Idx X} (h : j = j') (φ : V ⟶ compAt X j) (φ' : V ⟶ compAt X j')
    (hφ : φ.hom.left ≫ (compOpens X (idxEquiv X j)).ι =
      φ'.hom.left ≫ (compOpens X (idxEquiv X j')).ι) (a : T.extH X) :
    T.pullTotal φ (a j) = T.pullTotal φ' (a j') := by
  subst h
  rw [comp_hom_ext' X hφ]

/-- **Pullback `f^* : H^*(Y) → H^*(X)`**: on the factor of the component `X_i`, pullback along
the restriction `X_i ⟶ Y_j` of `f`. -/
def extPull {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) :
    T.extH Y →ₐ[F] T.extH X :=
  AlgHom.pi fun i ↦ (T.pullTotal (resIdx f i)).comp (Pi.evalAlgHom F _ (idxMap f i))

/-- The component of `f^* a` at `X_i` is the pullback of the component of `a` at the component
of `Y` into which `X_i` maps. -/
@[simp]
theorem extPull_apply {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) (a : T.extH Y)
    (i : Idx X) : T.extPull f a i = T.pullTotal (resIdx f i) (a (idxMap f i)) :=
  rfl

/-- Pullback along the identity is the identity on `H^*(X)`. -/
theorem extPull_id (X : (SmoothProjectiveScheme k).FullSubcategory) :
    T.extPull (𝟙 X) = AlgHom.id F _ := by
  refine AlgHom.ext fun a ↦ funext fun i ↦ ?_
  rw [extPull_apply, AlgHom.id_apply, ← AlgHom.id_apply (R := F) (a i), ← T.pullTotal_id]
  exact T.pullTotal_congr (idxMap_id i) (resIdx (𝟙 X) i) (𝟙 _) (by simp) a

/-- Pullback on `H^*` is contravariantly functorial: `(f ≫ g)^* = f^* ∘ g^*`. -/
theorem extPull_comp {X Y Z : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) (g : Y ⟶ Z) :
    T.extPull (f ≫ g) = (T.extPull f).comp (T.extPull g) := by
  refine AlgHom.ext fun a ↦ funext fun i ↦ ?_
  rw [extPull_apply, AlgHom.comp_apply, extPull_apply, extPull_apply, ← AlgHom.comp_apply,
    ← T.pullTotal_comp]
  exact T.pullTotal_congr (idxMap_comp f g i) (resIdx (f ≫ g) i)
    (resIdx f i ≫ resIdx g (idxMap f i)) (by simp) a

/-- Pullback `f^* : H^*(Y) → H^*(X)` preserves the degree-`n` part. -/
theorem extPull_mem_extGrade {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) {n : ℤ}
    {a : T.extH Y} (ha : a ∈ T.extGrade Y n) : T.extPull f a ∈ T.extGrade X n :=
  T.mem_extGrade.2 fun _ ↦ T.pullTotal_mem_grade _ (T.mem_extGrade.1 ha _)

/-- Graded commutativity of `H^*(X)`: for `a` of degree `i` and `b` of degree `j`,
`a * b = (-1)^{ij} b * a`. -/
theorem extH_mul_eq (X : (SmoothProjectiveScheme k).FullSubcategory) (i j : ℤ) (a b : T.extH X)
    (ha : a ∈ T.extGrade X i) (hb : b ∈ T.extGrade X j) :
    a * b = (Int.negOnePow (i * j) : ℤ) • (b * a) :=
  funext fun c ↦ T.totalH_mul_eq _ i j _ _ (T.mem_extGrade.1 ha c) (T.mem_extGrade.1 hb c)

/-! ### Cycle classes -/

/-- The restriction `α ↦ α|_{X_i}` of cycle classes to a component, the Gysin map of the
inclusion. -/
def restrictChow (X : (SmoothProjectiveScheme k).FullSubcategory) (i : Idx X) (r : ℤ) :
    codimensionChowGroup k X.obj.hom r →+
      codimensionChowGroup k ((SmoothProjective.toSchemeCat k).obj (compAt X i)).obj.hom r :=
  codimensionGysin ((SmoothProjective.toSchemeCat k).obj (compAt X i)).obj.hom X.obj.hom
    (Over.w (compAtι X i).hom) r

/-- The cycle class map `γ(α) = (γ(α|_{X_i}))_i` into `∏_i H^*(X_i)`, untwisted. -/
def extCycleClassUntw (X : (SmoothProjectiveScheme k).FullSubcategory) (r : ℤ) :
    codimensionChowGroup k X.obj.hom r →+ T.extH X :=
  AddMonoidHom.pi fun i ↦ (lof F ℤ (T.H (compAt X i)).piece (2 * r)).toAddMonoidHom.comp
    ((T.cycleClass (compAt X i) r).comp (restrictChow X i r))

/-- The component of the untwisted cycle class of `α` at `X_i` is `γ(α|_{X_i})` in degree `2r`. -/
@[simp]
theorem extCycleClassUntw_apply (X : (SmoothProjectiveScheme k).FullSubcategory) (r : ℤ)
    (α : codimensionChowGroup k X.obj.hom r) (i : Idx X) :
    T.extCycleClassUntw X r α i =
      lof F ℤ (T.H (compAt X i)).piece (2 * r)
        (T.cycleClass (compAt X i) r (restrictChow X i r α)) :=
  rfl

/-- The untwisted cycle class of a codimension-`r` cycle class has degree `2r`. -/
theorem extCycleClassUntw_mem (X : (SmoothProjectiveScheme k).FullSubcategory) (r : ℤ)
    (α : codimensionChowGroup k X.obj.hom r) : T.extCycleClassUntw X r α ∈ T.extGrade X (2 * r) :=
  T.mem_extGrade.2 fun _ ↦ ⟨_, rfl⟩

/-- The coordinate `F(m) = F` on the twists, `F(1)` being `F`. -/
abbrev twistCoord (V : Type v) [AddCommGroup V] [Module F V] (m : ℤ) :
    tateTwist F F V m ≃ₗ[F] V :=
  tateTwistCoordinates (LinearEquiv.refl F F) m

/-- **The cycle class map `γ : CH^r(X) → H^{2r}(X)(r)`**. -/
def extCycleClass (X : (SmoothProjectiveScheme k).FullSubcategory) (r : ℤ) :
    codimensionChowGroup k X.obj.hom r →+ tateTwist F F (T.extGrade X (2 * r)) r :=
  (twistCoord (T.extGrade X (2 * r)) r).symm.toAddMonoidHom.comp
    (AddMonoidHom.mk' (fun α ↦ ⟨T.extCycleClassUntw X r α, T.extCycleClassUntw_mem X r α⟩)
      fun α β ↦ Subtype.ext (map_add _ α β))

/-! ### Trace maps -/

/-- The components of a nonempty equidimensional `X` of dimension `d` have dimension `d`. -/
theorem dimension_compAt {X : (SmoothProjectiveScheme k).FullSubcategory} {d : ℕ}
    (hX : IsNonemptyEquidimensional X d) (i : Idx X) : T.dimension (compAt X i) = d := by
  have h := T.dimension_eq (compAt X i)
  have : Nonempty (compAt X i).obj.left := by
    obtain ⟨x, hx⟩ := _root_.ConnectedComponents.surjective_coe (idxEquiv X i)
    exact ⟨⟨x, hx⟩⟩
  have : LocallyOfFiniteType (compAt X i).obj.hom :=
    inferInstanceAs (LocallyOfFiniteType ((compOpens X (idxEquiv X i)).ι ≫ X.obj.hom))
  rw [topologicalKrullDim_eq_of_relativeDimension (compAt X i).obj.hom
    (RelativeDimension.comp_isOpenImmersion _ _ hX.relativeDimension)] at h
  exact_mod_cast h.symm

/-- The untwisted trace `a ↦ ∑_i ∫_{X_i} a_i` on the degree-`2d` parts. -/
def extTraceUntw (X : (SmoothProjectiveScheme k).FullSubcategory) {d : ℕ}
    (hX : IsNonemptyEquidimensional X d) :
    T.extH X →ₗ[F] F :=
  ∑ i, (T.integration (compAt X i)).toLinearMap ∘ₗ
    ExternallyGraded.degreeCast (R := F) (X := (T.H (compAt X i)).piece)
      (by rw [T.dimension_compAt hX i]) ∘ₗ
    component F ℤ (T.H (compAt X i)).piece (2 * (d : ℤ)) ∘ₗ LinearMap.proj i

/-- **The trace map `∫_X : H^{2d}(X)(d) → F`**, `∫_X a = ∑_i ∫_{X_i} a_i`. -/
def extTrace (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ)
    (hX : IsNonemptyEquidimensional X d) :
    tateTwist F F (T.extGrade X (2 * (d : ℤ))) d →ₗ[F] F :=
  (T.extTraceUntw X hX ∘ₗ (T.extGrade X (2 * (d : ℤ))).subtype) ∘ₗ
    (twistCoord (T.extGrade X (2 * (d : ℤ))) d).toLinearMap

/-! ### The data -/

/-- **The data (D0)–(D3) of Section 45.9 (Tag 0FHA) given by a classical Weil cohomology
theory**, on all smooth projective schemes over `k`. -/
abbrev toWeilData : WeilData k F where
  tate := F
  finrank_tate := Module.finrank_self F
  H := T.extH
  grade := T.extGrade
  graded_comm X := T.extH_mul_eq X
  pull f := T.extPull f
  pull_id := T.extPull_id
  pull_comp := T.extPull_comp
  pull_grade f _ _ ha := T.extPull_mem_extGrade f ha
  cycleClass := T.extCycleClass
  trace := T.extTrace

end ClassicalWeilCohomologyTheory

end Stacks.WeilCohomology

end
