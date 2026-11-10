module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.CategoryTheory.Triangulated.TriangleShift
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.BigOperators.Finprod

/-!
# Building an object out of a semi-orthogonal family by killing morphisms

Let `C` be a pretriangulated category, linear over a field `k`, and let `P₀, …, P_{N-1}` be
objects of `C` such that

* every nonzero endomorphism of `Pₐ` is an isomorphism, `Pₐ ≠ 0`, and `Hom(Pₐ, Pₐ[m]) = 0` for
  `m ≠ 0`;
* `Hom(P_b, Pₐ[j]) = 0` for all `j` whenever `b < a`;
* the `Pₐ` detect a class `QC` of objects: an object of `QC` receiving no nonzero morphism from
  any shift of any `Pₐ` is zero.

If an object `Y` of `QC` has finite-dimensional total `Hom` from each `Pₐ` (measured, more
generally, through a fully faithful shift-compatible functor, see `Probe`), then `Y` lies in
every class of objects which contains the zero objects and the shifts of the `Pₐ` and is closed
under extensions. The proof kills the morphisms out of `P₀` one at a time by cones, then those
out of `P₁`, and so on; the semi-orthogonality makes each stage leave the earlier ones killed,
and the detection hypothesis shows that what remains at the end is zero. This is the argument
by which an exceptional collection generating a triangulated category generates it by finitely
many extensions.

## Main definitions

* `Stacks.Triangulated.ProbeKilling.Probe`: an object `P` together with a fully faithful,
  additive, shift-compatible functor `G` and an isomorphism `G P ≅ U`; the morphisms
  `P ⟶ Y[j]` are then measured as the `k`-vector spaces `U ⟶ (G Y)[j]`.
* `Stacks.Triangulated.ProbeKilling.Probe.FT`: the total dimension of these spaces is finite.
* `Stacks.Triangulated.ProbeKilling.Probe.Orth`: every morphism from a shift of `P` vanishes.

## Main results

* `Stacks.Triangulated.ProbeKilling.mem_of_probes`: the statement above.

## Implementation notes

The measuring functor `G` is part of the data so that finiteness can be read on morphism spaces
whose `k`-linear structure is the ambient one, without asking `G` to be `k`-linear: the
morphisms `P ⟶ Y[j]` and `U ⟶ (G Y)[j]` correspond bijectively through `G`, the bijections
carry composition with a morphism to composition with its image, and only exactness and
vanishing are ever transported along them. Dimensions are only taken on the `U`-side, where
every map in sight is a composition and hence `k`-linear. With `G` the identity functor and
`U = P` this is the plain statement about `Hom(P, Y[j])`.
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

namespace Stacks.Triangulated.ProbeKilling

universe w v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-! ### Exactness of the morphisms out of a fixed object along a triangle -/

section Exactness

variable {T : Triangle C} (hT : T ∈ distTriang C) {Q : C}

/-- Absorb a sign in the factorisation of a morphism through `f`. -/
private theorem exists_eq_comp_of_eq_comp_smul {D : Type*} [Category D] [Preadditive D]
    {X Y Z : D} {f : Y ⟶ Z} {g : X ⟶ Z} (ε : ℤˣ)
    (hex : ∃ h : X ⟶ Y, g = h ≫ (ε • f)) : ∃ h : X ⟶ Y, g = h ≫ f := by
  obtain ⟨h, hh⟩ := hex
  exact ⟨ε • h, by rw [hh, Linear.comp_units_smul, Linear.units_smul_comp]⟩

include hT in
/-- Exactness at the second vertex of a shifted distinguished triangle. -/
theorem exists_eq_comp_mor₁ (n : ℤ) (g : Q ⟶ T.obj₂⟦n⟧) (hg : g ≫ T.mor₂⟦n⟧' = 0) :
    ∃ h : Q ⟶ T.obj₁⟦n⟧, g = h ≫ T.mor₁⟦n⟧' := by
  refine exists_eq_comp_of_eq_comp_smul n.negOnePow ?_
  exact Triangle.coyoneda_exact₂ _ (Triangle.shift_distinguished T hT n) g (by
    change g ≫ (n.negOnePow • T.mor₂⟦n⟧') = 0
    rw [Linear.comp_units_smul, hg, smul_zero])

include hT in
/-- Exactness at the third vertex of a shifted distinguished triangle, with the connecting
morphism landing in `T.obj₁[n + 1]`. -/
theorem exists_eq_comp_mor₂ (n n' : ℤ) (hn : n + 1 = n') (g : Q ⟶ T.obj₃⟦n⟧)
    (hg : g ≫ T.mor₃⟦n⟧' ≫ (shiftFunctorAdd' C 1 n n' (by omega)).inv.app T.obj₁ = 0) :
    ∃ h : Q ⟶ T.obj₂⟦n⟧, g = h ≫ T.mor₂⟦n⟧' := by
  have hg' : g ≫ T.mor₃⟦n⟧' = 0 := by
    simpa using hg =≫ (shiftFunctorAdd' C 1 n n' (by omega)).hom.app T.obj₁
  refine exists_eq_comp_of_eq_comp_smul n.negOnePow ?_
  exact Triangle.coyoneda_exact₃ _ (Triangle.shift_distinguished T hT n) g (by
    change g ≫ (n.negOnePow • (T.mor₃⟦n⟧' ≫ (shiftFunctorComm C 1 n).hom.app T.obj₁)) = 0
    rw [Linear.comp_units_smul, ← Category.assoc, hg', zero_comp, smul_zero])

include hT in
/-- Exactness at the first vertex, shifted by `n'`, of a distinguished triangle. -/
theorem exists_eq_comp_mor₃ (n n' : ℤ) (hn : n + 1 = n') (g : Q ⟶ T.obj₁⟦n'⟧)
    (hg : g ≫ T.mor₁⟦n'⟧' = 0) :
    ∃ h : Q ⟶ T.obj₃⟦n⟧,
      g = h ≫ T.mor₃⟦n⟧' ≫ (shiftFunctorAdd' C 1 n n' (by omega)).inv.app T.obj₁ := by
  have hR : (Triangle.shiftFunctor C n).obj T.rotate ∈ distTriang C :=
    Triangle.shift_distinguished _ (rot_of_distTriang T hT) n
  let e := (shiftFunctorAdd' C 1 n n' (by omega)).app T.obj₁
  have hnat : e.hom ≫ (T.mor₁⟦(1 : ℤ)⟧')⟦n⟧' =
      T.mor₁⟦n'⟧' ≫ (shiftFunctorAdd' C 1 n n' (by omega)).hom.app T.obj₂ :=
    ((shiftFunctorAdd' C 1 n n' (by omega)).hom.naturality T.mor₁).symm
  obtain ⟨h, hh⟩ : ∃ h : Q ⟶ T.obj₃⟦n⟧, g ≫ e.hom = h ≫ (n.negOnePow • T.mor₃⟦n⟧') :=
    Triangle.coyoneda_exact₃ _ hR (g ≫ e.hom) (by
      change (g ≫ e.hom) ≫ (n.negOnePow • ((-T.mor₁⟦(1 : ℤ)⟧')⟦n⟧' ≫
        (shiftFunctorComm C 1 n).hom.app T.obj₂)) = 0
      rw [Functor.map_neg, Preadditive.neg_comp, smul_neg, Preadditive.comp_neg,
        Linear.comp_units_smul, Category.assoc, ← Category.assoc e.hom, hnat, Category.assoc,
        ← Category.assoc g, hg, zero_comp, smul_zero, neg_zero])
  refine ⟨n.negOnePow • h, ?_⟩
  rw [show g = (g ≫ e.hom) ≫ e.inv by simp, hh, Linear.comp_units_smul, Linear.units_smul_comp,
    Linear.units_smul_comp, Category.assoc]
  rfl

include hT in
/-- The composite of the two maps around the second vertex vanishes. -/
theorem mor₁_shift_comp_mor₂_shift (n : ℤ) : T.mor₁⟦n⟧' ≫ T.mor₂⟦n⟧' = 0 := by
  rw [← Functor.map_comp, comp_distTriang_mor_zero₁₂ _ hT, Functor.map_zero]

include hT in
/-- The composite of the two maps around the third vertex vanishes. -/
theorem mor₂_shift_comp_mor₃_shift (n n' : ℤ) (hn : n + 1 = n') :
    T.mor₂⟦n⟧' ≫ T.mor₃⟦n⟧' ≫ (shiftFunctorAdd' C 1 n n' (by omega)).inv.app T.obj₁ = 0 := by
  rw [← Category.assoc, ← Functor.map_comp, comp_distTriang_mor_zero₂₃ _ hT, Functor.map_zero,
    zero_comp]

include hT in
/-- The composite of the two maps around the first vertex, shifted by `n'`, vanishes. -/
theorem mor₃_shift_comp_mor₁_shift (n n' : ℤ) (hn : n + 1 = n') :
    (T.mor₃⟦n⟧' ≫ (shiftFunctorAdd' C 1 n n' (by omega)).inv.app T.obj₁) ≫ T.mor₁⟦n'⟧' = 0 := by
  have hnat := (shiftFunctorAdd' C 1 n n' (by omega)).inv.naturality T.mor₁
  dsimp at hnat
  rw [Category.assoc, ← hnat, ← Category.assoc, ← Functor.map_comp,
    comp_distTriang_mor_zero₃₁ _ hT, Functor.map_zero, zero_comp]

end Exactness

/-! ### Probes -/

/-- A *probe*: an object `P` of `C`, an additive, fully faithful, shift-compatible endofunctor
`G` of `C`, and an isomorphism `G P ≅ U`. The morphisms `P ⟶ Y[j]` are read through `G` as
morphisms `U ⟶ (G Y)[j]`, and it is on those that dimensions are taken. -/
structure Probe (C : Type u) [Category.{v} C] [Preadditive C] [HasShift C ℤ] where
  /-- The object whose morphisms into shifts are to be killed. -/
  P : C
  /-- The object out of which the morphisms are measured. -/
  U : C
  /-- The measuring functor. -/
  G : C ⥤ C
  /-- The measuring functor commutes with the shifts. -/
  [commShift : G.CommShift ℤ]
  /-- The measuring functor is additive. -/
  [additive : G.Additive]
  /-- The measuring functor is fully faithful. -/
  ff : G.FullyFaithful
  /-- The measuring functor carries `P` to `U`. -/
  ι : G.obj P ≅ U

attribute [instance] Probe.commShift Probe.additive

namespace Probe

variable (p : Probe C)

/-- The morphisms `P ⟶ Y[j]` read as morphisms `U ⟶ (G Y)[j]`. -/
noncomputable def read (Y : C) (j : ℤ) : (p.P ⟶ Y⟦j⟧) ≃ (p.U ⟶ (p.G.obj Y)⟦j⟧) :=
  p.ff.homEquiv.trans (p.ι.homFromEquiv.trans ((p.G.commShiftIso j).app Y).homToEquiv)

omit [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] in
/-- The reading of `g : P ⟶ Y[j]` is `ι⁻¹ ≫ G g ≫ (G (Y[j]) ≅ (G Y)[j])`. -/
theorem read_apply (Y : C) (j : ℤ) (g : p.P ⟶ Y⟦j⟧) :
    p.read Y j g = p.ι.inv ≫ p.G.map g ≫ ((p.G.commShiftIso j).app Y).hom := by
  simp [read]

/-- A morphism between shifted objects, transported by the measuring functor. -/
noncomputable def tr {Y Y' : C} {j j' : ℤ} (m : Y⟦j⟧ ⟶ Y'⟦j'⟧) :
    (p.G.obj Y)⟦j⟧ ⟶ (p.G.obj Y')⟦j'⟧ :=
  ((p.G.commShiftIso j).app Y).inv ≫ p.G.map m ≫ ((p.G.commShiftIso j').app Y').hom

omit [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] in
/-- Reading a composite `g ≫ m` is reading `g` followed by the transport of `m`. -/
theorem read_comp {Y Y' : C} {j j' : ℤ} (g : p.P ⟶ Y⟦j⟧) (m : Y⟦j⟧ ⟶ Y'⟦j'⟧) :
    p.read Y' j' (g ≫ m) = p.read Y j g ≫ p.tr m := by
  simp [read_apply, tr]

omit [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] in
/-- Transport of morphisms between shifted objects is compatible with composition. -/
theorem tr_comp {Y Y' Y'' : C} {j j' j'' : ℤ} (m : Y⟦j⟧ ⟶ Y'⟦j'⟧) (m' : Y'⟦j'⟧ ⟶ Y''⟦j''⟧) :
    p.tr m ≫ p.tr m' = p.tr (m ≫ m') := by
  simp [tr]

omit [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] in
/-- The transport of the zero morphism is zero. -/
theorem tr_zero {Y Y' : C} {j j' : ℤ} : p.tr (0 : Y⟦j⟧ ⟶ Y'⟦j'⟧) = 0 := by
  simp [tr]

omit [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] in
/-- The reading of the zero morphism is zero. -/
theorem read_zero (Y : C) (j : ℤ) : p.read Y j 0 = 0 := by
  simp [read_apply]

omit [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] in
/-- A morphism `P ⟶ Y[j]` reads as zero if and only if it is zero. -/
theorem read_eq_zero_iff (Y : C) (j : ℤ) (g : p.P ⟶ Y⟦j⟧) : p.read Y j g = 0 ↔ g = 0 := by
  rw [← p.read_zero Y j]
  exact (p.read Y j).injective.eq_iff

omit [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] in
/-- The morphisms `P ⟶ Y[j]` form a subsingleton if and only if the morphisms `U ⟶ (G Y)[j]`
do. -/
theorem subsingleton_iff (Y : C) (j : ℤ) :
    Subsingleton (p.P ⟶ Y⟦j⟧) ↔ Subsingleton (p.U ⟶ (p.G.obj Y)⟦j⟧) :=
  (p.read Y j).subsingleton_congr

/-- Finiteness of the total dimension of the morphism spaces `U ⟶ (G Y)[j]`. -/
def FT (k : Type w) [Field k] [Linear k C] (Y : C) : Prop :=
  (∀ j : ℤ, Module.Finite k (p.U ⟶ (p.G.obj Y)⟦j⟧)) ∧
    {j : ℤ | Nontrivial (p.U ⟶ (p.G.obj Y)⟦j⟧)}.Finite

/-- Every morphism from a shift of `P` to `Y` vanishes. -/
def Orth (Y : C) : Prop := ∀ j : ℤ, Subsingleton (p.P ⟶ Y⟦j⟧)

end Probe

/-! ### Linear algebra along the transported long exact sequence -/

section LinearAlgebra

variable (k : Type w) [Field k] [Linear k C] (p : Probe C)

/-- Composition with a transported morphism, as a `k`-linear map. -/
noncomputable def Probe.post {Y Y' : C} {j j' : ℤ} (m : Y⟦j⟧ ⟶ Y'⟦j'⟧) :
    (p.U ⟶ (p.G.obj Y)⟦j⟧) →ₗ[k] (p.U ⟶ (p.G.obj Y')⟦j'⟧) :=
  Linear.rightComp k p.U (p.tr m)

omit [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] in
/-- Composing the reading of `g` with the transport of `m` is the reading of `g ≫ m`. -/
theorem Probe.post_read {Y Y' : C} {j j' : ℤ} (m : Y⟦j⟧ ⟶ Y'⟦j'⟧) (g : p.P ⟶ Y⟦j⟧) :
    p.post k m (p.read Y j g) = p.read Y' j' (g ≫ m) :=
  (p.read_comp g m).symm

omit [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] in
/-- Exactness of the plain sequence of morphisms out of `P` gives exactness of the transported
one. -/
theorem Probe.exact_post {A B D : C} {i j l : ℤ} (m₁ : A⟦i⟧ ⟶ B⟦j⟧) (m₂ : B⟦j⟧ ⟶ D⟦l⟧)
    (hzero : m₁ ≫ m₂ = 0) (hex : ∀ g : p.P ⟶ B⟦j⟧, g ≫ m₂ = 0 → ∃ h, g = h ≫ m₁) :
    Function.Exact (p.post k m₁) (p.post k m₂) := by
  intro x
  obtain ⟨g, rfl⟩ := (p.read B j).surjective x
  constructor
  · intro hx
    rw [p.post_read k, p.read_eq_zero_iff] at hx
    obtain ⟨h, rfl⟩ := hex g hx
    exact ⟨p.read A i h, p.post_read k m₁ h⟩
  · rintro ⟨y, hy⟩
    obtain ⟨h, rfl⟩ := (p.read A i).surjective y
    rw [← hy, p.post_read k, p.post_read k, Category.assoc, hzero, Limits.comp_zero, p.read_zero]

end LinearAlgebra

/-! ### Shifting the measured object -/

section Shift

variable (k : Type w) [Field k] [Linear k C] (p : Probe C)

omit [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] in
/-- Finiteness of a family of morphism spaces out of a fixed object is invariant under
reindexing along isomorphisms. -/
theorem finite_family_of_iso {U : C} {W W' : ℤ → C} (m : ℤ) (e : ∀ j, W' j ≅ W (j + m))
    (hfin : ∀ j, Module.Finite k (U ⟶ W j)) (hsupp : {j : ℤ | Nontrivial (U ⟶ W j)}.Finite) :
    (∀ j, Module.Finite k (U ⟶ W' j)) ∧ {j : ℤ | Nontrivial (U ⟶ W' j)}.Finite := by
  refine ⟨fun j => ?_, ?_⟩
  · have := hfin (j + m)
    exact Module.Finite.of_surjective (Linear.rightComp k U (e j).inv) fun f =>
      ⟨f ≫ (e j).hom, by simp [Linear.rightComp]⟩
  · refine (hsupp.preimage (f := fun j => j + m) (fun a _ b _ h => by simpa using h)).subset ?_
    intro j hj
    change Nontrivial (U ⟶ W (j + m))
    exact ((e j).homToEquiv.nontrivial_congr).1 hj

/-- `G (Y[m])[j] ≅ (G Y)[m + j]`. -/
noncomputable def Probe.shiftIso (Y : C) (m j : ℤ) :
    (p.G.obj (Y⟦m⟧))⟦j⟧ ≅ (p.G.obj Y)⟦j + m⟧ :=
  (shiftFunctor C j).mapIso ((p.G.commShiftIso m).app Y) ≪≫
    ((shiftFunctorAdd' C m j (j + m) (by omega)).app (p.G.obj Y)).symm

omit [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] in
/-- Finiteness of the total dimension is preserved by shifting the measured object. -/
theorem Probe.FT.shift {Y : C} (h : p.FT k Y) (m : ℤ) : p.FT k (Y⟦m⟧) :=
  finite_family_of_iso k m (p.shiftIso Y m) h.1 h.2

omit [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] in
/-- Orthogonality to all shifts of `P` is preserved by shifting the measured object. -/
theorem Probe.Orth.shift {Y : C} (h : p.Orth Y) (m : ℤ) : p.Orth (Y⟦m⟧) := fun j =>
  (((shiftFunctorAdd' C m j (j + m) (by omega)).app Y).homToEquiv.subsingleton_congr).1 (h _)

omit [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] in
/-- An object orthogonal to all shifts of `P` has finite total dimension. -/
theorem Probe.FT.of_orth {Y : C} (h : p.Orth Y) : p.FT k Y := by
  have hs : ∀ j, Subsingleton (p.U ⟶ (p.G.obj Y)⟦j⟧) := fun j => (p.subsingleton_iff Y j).1 (h j)
  refine ⟨fun j => ?_, ?_⟩
  · have := hs j
    exact Module.Finite.of_surjective (0 : k →ₗ[k] _) fun x => ⟨0, Subsingleton.elim _ _⟩
  · refine Set.finite_empty.subset fun j hj => ?_
    have := hs j
    exact (not_nontrivial _ hj).elim

end Shift

/-! ### Two out of three along a distinguished triangle -/

section TwoOutOfThree

variable (k : Type w) [Field k] [Linear k C] (p : Probe C)

/-- Exactness of the transported sequence at the third vertex of a distinguished triangle. -/
private theorem exact_post_mor₂ {T : Triangle C} (hT : T ∈ distTriang C) (j : ℤ) :
    Function.Exact (p.post k (T.mor₂⟦j⟧'))
      (p.post k (T.mor₃⟦j⟧' ≫ (shiftFunctorAdd' C 1 j (j + 1) (by omega)).inv.app T.obj₁)) :=
  p.exact_post k _ _ (mor₂_shift_comp_mor₃_shift hT j (j + 1) rfl)
    (fun g hg => exists_eq_comp_mor₂ hT j (j + 1) rfl g hg)

include p in
/-- If every morphism from a shift of `P` into the first and second vertex of a distinguished
triangle vanishes, the same holds for the third. -/
theorem Probe.Orth.obj₃ {T : Triangle C} (hT : T ∈ distTriang C) (h₁ : p.Orth T.obj₁)
    (h₂ : p.Orth T.obj₂) : p.Orth T.obj₃ := by
  intro j
  refine subsingleton_of_forall_eq 0 fun g => ?_
  obtain ⟨h, rfl⟩ := exists_eq_comp_mor₂ hT j (j + 1) rfl g ((h₁ (j + 1)).elim _ _)
  rw [(h₂ j).elim h 0, zero_comp]

/-- Finiteness of the total dimension along the first two vertices gives it along the third. -/
theorem Probe.FT.obj₃ {T : Triangle C} (hT : T ∈ distTriang C) (h₁ : p.FT k T.obj₁)
    (h₂ : p.FT k T.obj₂) : p.FT k T.obj₃ := by
  have hex := exact_post_mor₂ k p hT
  refine ⟨fun j => ?_, ?_⟩
  · have := h₁.1 (j + 1)
    have := h₂.1 j
    let δ := p.post k (T.mor₃⟦j⟧' ≫ (shiftFunctorAdd' C 1 j (j + 1) (by omega)).inv.app T.obj₁)
    have hex' : Function.Exact (p.post k (T.mor₂⟦j⟧')) δ.rangeRestrict := by
      intro x
      rw [← hex j x]
      simp [δ, Subtype.ext_iff]
    exact Module.Finite.of_exact hex' (LinearMap.surjective_rangeRestrict δ)
  · refine ((h₂.2.union (h₁.2.preimage (f := fun j => j + 1)
      (fun a _ b _ h => by simpa using h)))).subset ?_
    intro j hj
    by_contra hcon
    simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_preimage, not_or,
      not_nontrivial_iff_subsingleton] at hcon
    obtain ⟨h2, h1⟩ := hcon
    have key : ∀ x : p.U ⟶ (p.G.obj T.obj₃)⟦j⟧, x = 0 := fun x => by
      obtain ⟨y, hy⟩ := (hex j x).1 (Subsingleton.elim _ _)
      rw [← hy, Subsingleton.elim y 0, map_zero]
    have := subsingleton_of_forall_eq (0 : p.U ⟶ _) key
    exact not_nontrivial _ hj

end TwoOutOfThree

/-! ### The killing step -/

section Kill

variable (k : Type w) [Field k] [Linear k C] (p : Probe C)

omit [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] in
/-- `Hom(P, P[-j₀][j])` vanishes for `j ≠ j₀`, as soon as `P` has no self-morphisms in nonzero
degrees. -/
theorem subsingleton_shift_shift (hself : ∀ m : ℤ, m ≠ 0 → Subsingleton (p.P ⟶ p.P⟦m⟧))
    (j₀ j : ℤ) (hj : j ≠ j₀) : Subsingleton (p.P ⟶ (p.P⟦-j₀⟧)⟦j⟧) :=
  (((shiftFunctorAdd' C (-j₀) j (j - j₀) (by omega)).app p.P).homToEquiv.subsingleton_congr).1
    (hself _ (by omega))

/-- **The killing step.** If `Hom(P, Y[j₀]) ≠ 0`, the cone `Z` of a suitable morphism
`P[-j₀] ⟶ Y` has the same morphism spaces from `P` as `Y` in every degree but `j₀`, and a
strictly smaller one in degree `j₀`. -/
theorem exists_kill
    (hdiv : ∀ e : p.P ⟶ p.P, e ≠ 0 → IsIso e) (hP : ¬ IsZero p.P)
    (hself : ∀ m : ℤ, m ≠ 0 → Subsingleton (p.P ⟶ p.P⟦m⟧))
    (Y : C) (hY : p.FT k Y) (j₀ : ℤ) (hj₀ : Nontrivial (p.U ⟶ (p.G.obj Y)⟦j₀⟧)) :
    ∃ (Z : C) (φ : p.P⟦-j₀⟧ ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ (p.P⟦-j₀⟧)⟦(1 : ℤ)⟧),
      Triangle.mk φ g h ∈ distTriang C ∧
      (∀ j : ℤ, j ≠ j₀ → Nonempty ((p.U ⟶ (p.G.obj Y)⟦j⟧) ≃ₗ[k] (p.U ⟶ (p.G.obj Z)⟦j⟧))) ∧
      Module.Finite k (p.U ⟶ (p.G.obj Z)⟦j₀⟧) ∧
      Module.finrank k (p.U ⟶ (p.G.obj Z)⟦j₀⟧) < Module.finrank k (p.U ⟶ (p.G.obj Y)⟦j₀⟧) := by
  classical
  -- a nonzero morphism `P ⟶ Y[j₀]`
  obtain ⟨y, hy⟩ := exists_ne (0 : p.U ⟶ (p.G.obj Y)⟦j₀⟧)
  set g₀ := (p.read Y j₀).symm y with hg₀
  have hg₀ne : g₀ ≠ 0 := by
    intro h
    apply hy
    rw [← (p.read Y j₀).apply_symm_apply y, ← hg₀, h, p.read_zero]
  -- its adjoint `φ : P[-j₀] ⟶ Y`
  let adj := (shiftEquiv' C (-j₀) j₀ (by omega)).toAdjunction
  let φ : p.P⟦-j₀⟧ ⟶ Y := (adj.homEquiv p.P Y).symm g₀
  let ηi : p.P ≅ (p.P⟦-j₀⟧)⟦j₀⟧ := (shiftEquiv' C (-j₀) j₀ (by omega)).unitIso.app p.P
  let η : p.P ⟶ (p.P⟦-j₀⟧)⟦j₀⟧ := ηi.hom
  have hg₀φ : g₀ = η ≫ φ⟦j₀⟧' :=
    ((adj.homEquiv p.P Y).apply_symm_apply g₀).symm.trans (adj.homEquiv_unit p.P Y φ)
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle φ
  -- injectivity of composition with `φ[j₀]` on `Hom(P, P[-j₀][j₀])`
  have hinj : ∀ e : p.P ⟶ (p.P⟦-j₀⟧)⟦j₀⟧, e ≫ φ⟦j₀⟧' = 0 → e = 0 := by
    intro e he
    by_contra hne
    have he' : e ≫ ηi.inv ≠ 0 := by
      intro h0
      apply hne
      simpa [η] using h0 =≫ η
    have := hdiv _ he'
    apply hg₀ne
    have h1 : (e ≫ ηi.inv) ≫ g₀ = 0 := by
      rw [hg₀φ, Category.assoc, ← Category.assoc ηi.inv, Iso.inv_hom_id, Category.id_comp, he]
    rw [← cancel_epi (e ≫ ηi.inv), h1, Limits.comp_zero]
  -- the long exact sequence, transported
  let α : ∀ j : ℤ, _ := fun j => p.post k (φ⟦j⟧')
  let β : ∀ j : ℤ, _ := fun j => p.post k (g⟦j⟧')
  let δ : ∀ j : ℤ, _ := fun j =>
    p.post k (h⟦j⟧' ≫ (shiftFunctorAdd' C 1 j (j + 1) (by omega)).inv.app (p.P⟦-j₀⟧))
  have ex₂ : ∀ j, Function.Exact (α j) (β j) := fun j =>
    p.exact_post k _ _ (mor₁_shift_comp_mor₂_shift hT j)
      (fun g' hg' => exists_eq_comp_mor₁ hT j g' hg')
  have ex₃ : ∀ j, Function.Exact (β j) (δ j) := exact_post_mor₂ k p hT
  have ex₁ : ∀ j, Function.Exact (δ j) (α (j + 1)) := fun j =>
    p.exact_post k _ _ (mor₃_shift_comp_mor₁_shift hT j (j + 1) rfl)
      (fun g' hg' => exists_eq_comp_mor₃ hT j (j + 1) rfl g' hg')
  -- the vertex `P[-j₀]` is invisible outside degree `j₀`
  have hF : ∀ j, j ≠ j₀ → Subsingleton (p.U ⟶ (p.G.obj (p.P⟦-j₀⟧))⟦j⟧) := fun j hj =>
    (p.subsingleton_iff _ j).1 (subsingleton_shift_shift p hself j₀ j hj)
  -- `α j₀` is injective
  have hαinj : Function.Injective (α j₀) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨e, rfl⟩ := (p.read _ j₀).surjective x
    change p.post k (φ⟦j₀⟧') (p.read _ j₀ e) = 0 at hx
    rw [p.post_read k, p.read_eq_zero_iff] at hx
    rw [hinj e hx, p.read_zero]
  -- `β j` is injective for `j ≠ j₀`
  have hβinj : ∀ j, j ≠ j₀ → Function.Injective (β j) := by
    intro j hj
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨z, hz⟩ := (ex₂ j x).1 hx
    rw [← hz, (hF j hj).elim z 0, map_zero]
  -- `β j` is surjective for every `j`
  have hβsurj : ∀ j, Function.Surjective (β j) := by
    intro j x
    have hδ : δ j x = 0 := by
      by_cases hj : j + 1 = j₀
      · subst hj
        exact hαinj (((ex₁ j (δ j x)).2 ⟨x, rfl⟩).trans (map_zero _).symm)
      · exact (hF (j + 1) hj).elim _ _
    exact (ex₃ j x).1 hδ
  have := hY.1 j₀
  refine ⟨Z, φ, g, h, hT, fun j hj => ⟨LinearEquiv.ofBijective (β j) ⟨hβinj j hj, hβsurj j⟩⟩,
    Module.Finite.of_surjective (β j₀) (hβsurj j₀), ?_⟩
  · have hrk := LinearMap.finrank_range_add_finrank_ker (β j₀)
    rw [LinearMap.range_eq_top.2 (hβsurj j₀), finrank_top] at hrk
    -- the kernel of `β j₀` contains the nonzero image of `η`
    have hker : 0 < Module.finrank k (LinearMap.ker (β j₀)) := by
      rw [Module.finrank_pos_iff_exists_ne_zero (R := k)]
      refine ⟨⟨α j₀ (p.read _ j₀ η), (ex₂ j₀ _).2 ⟨_, rfl⟩⟩, ?_⟩
      intro h0
      have h1 := hαinj ((congrArg Subtype.val h0).trans (map_zero (α j₀)).symm)
      rw [p.read_eq_zero_iff] at h1
      apply hP
      rw [IsZero.iff_id_eq_zero, ← ηi.hom_inv_id]
      change η ≫ ηi.inv = 0
      rw [h1, zero_comp]
    omega

end Kill

/-! ### The induction -/

section Main

variable (k : Type w) [Field k] [Linear k C]

/-- The total dimension of the morphism spaces measured by a probe. -/
noncomputable def Probe.totalDim (p : Probe C) (Y : C) : ℕ :=
  ∑ᶠ j : ℤ, Module.finrank k (p.U ⟶ (p.G.obj Y)⟦j⟧)

omit [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] in
/-- If `Y` has finite total dimension, and the morphism spaces measured on `Z` agree in dimension
with those on `Y` away from degree `j₀` and are strictly smaller in degree `j₀`, then the total
dimension of `Z` is strictly smaller than that of `Y`. -/
theorem Probe.totalDim_lt (p : Probe C) {Y Z : C} (hY : p.FT k Y) (j₀ : ℤ)
    (hZ : ∀ j : ℤ, j ≠ j₀ → Nonempty ((p.U ⟶ (p.G.obj Y)⟦j⟧) ≃ₗ[k] (p.U ⟶ (p.G.obj Z)⟦j⟧)))
    (hlt : Module.finrank k (p.U ⟶ (p.G.obj Z)⟦j₀⟧) <
      Module.finrank k (p.U ⟶ (p.G.obj Y)⟦j₀⟧)) :
    p.totalDim k Z < p.totalDim k Y := by
  classical
  have hj₀ : j₀ ∈ hY.2.toFinset := by
    have := hY.1 j₀
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, ← Module.finrank_pos_iff (R := k)]
    omega
  have hsubY : Function.support (fun j : ℤ => Module.finrank k (p.U ⟶ (p.G.obj Y)⟦j⟧)) ⊆
      hY.2.toFinset := by
    intro j hj
    rw [Finset.mem_coe, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    have := hY.1 j
    exact Module.nontrivial_of_finrank_pos (R := k) (Nat.pos_of_ne_zero hj)
  have hsubZ : Function.support (fun j : ℤ => Module.finrank k (p.U ⟶ (p.G.obj Z)⟦j⟧)) ⊆
      hY.2.toFinset := by
    intro j hj
    rcases eq_or_ne j j₀ with rfl | hjj
    · exact hj₀
    · obtain ⟨e⟩ := hZ j hjj
      apply hsubY
      simpa [Function.mem_support, e.finrank_eq] using hj
  unfold Probe.totalDim
  rw [finsum_eq_sum_of_support_subset _ hsubY, finsum_eq_sum_of_support_subset _ hsubZ]
  refine Finset.sum_lt_sum (fun j _ => ?_) ⟨j₀, hj₀, hlt⟩
  rcases eq_or_ne j j₀ with rfl | hjj
  · exact hlt.le
  · exact (hZ j hjj).some.finrank_eq.ge

/-- **Building an object out of a semi-orthogonal family.** Let `p₀, …, p_{N-1}` be probes whose
objects `Pₐ` have only isomorphisms as nonzero endomorphisms, are nonzero, have no
self-morphisms in nonzero degrees, satisfy `Hom(P_b, Pₐ[j]) = 0` for `b < a`, and have
finite total measured `Hom` from `p_b` for `a ≤ b`. Suppose the `Pₐ` detect the objects of a
class `QC` closed under cones of morphisms out of shifts of the `Pₐ`. Then every object of `QC`
with finite total measured `Hom` from every `pₐ` lies in each class `S` containing the zero
objects and the shifts of the `Pₐ` and closed under extensions. -/
theorem mem_of_probes (N : ℕ) (p : ℕ → Probe C) (QC S : ObjectProperty C)
    (hQC : ∀ T ∈ distTriang C, QC T.obj₁ → QC T.obj₂ → QC T.obj₃)
    (hQCP : ∀ a < N, ∀ m : ℤ, QC ((p a).P⟦m⟧))
    (hS : ∀ T ∈ distTriang C, S T.obj₁ → S T.obj₃ → S T.obj₂)
    (hS0 : ∀ Y : C, IsZero Y → S Y)
    (hSP : ∀ a < N, ∀ m : ℤ, S ((p a).P⟦m⟧))
    (hdiv : ∀ a < N, ∀ e : (p a).P ⟶ (p a).P, e ≠ 0 → IsIso e)
    (hP : ∀ a < N, ¬ IsZero (p a).P)
    (hself : ∀ a < N, ∀ m : ℤ, m ≠ 0 → Subsingleton ((p a).P ⟶ (p a).P⟦m⟧))
    (horth : ∀ a < N, ∀ b < a, (p b).Orth (p a).P)
    (hfin : ∀ a < N, ∀ b < N, a ≤ b → (p b).FT k (p a).P)
    (hgen : ∀ Y : C, QC Y → (∀ a < N, (p a).Orth Y) → IsZero Y)
    (Y : C) (hY : QC Y) (hFT : ∀ a < N, (p a).FT k Y) : S Y := by
  -- `claim a`: objects of `QC` with finite measured `Hom` from every probe and no morphisms from
  -- the shifts of `P_b`, `b < a`, lie in `S`
  suffices claim : ∀ c : ℕ, ∀ a, a + c = N → ∀ Y : C, QC Y → (∀ b < N, (p b).FT k Y) →
      (∀ b < a, (p b).Orth Y) → S Y from
    claim N 0 (by omega) Y hY hFT (fun b hb => absurd hb (Nat.not_lt_zero b))
  intro c
  induction c with
  | zero =>
    intro a ha Y hY _ hO
    exact hS0 Y (hgen Y hY fun b hb => hO b (by omega))
  | succ c ih =>
    intro a ha
    have haN : a < N := by omega
    -- strong induction on the total dimension measured by `p a`
    suffices H : ∀ d : ℕ, ∀ Y : C, (p a).totalDim k Y = d → QC Y → (∀ b < N, (p b).FT k Y) →
        (∀ b < a, (p b).Orth Y) → S Y from
      fun Y hY hF hO => H _ Y rfl hY hF hO
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ihd =>
      intro Y hd hY hF hO
      by_cases hall : ∀ j : ℤ, Subsingleton ((p a).U ⟶ ((p a).G.obj Y)⟦j⟧)
      · -- nothing to kill: move on to the next probe
        refine ih (a + 1) (by omega) Y hY hF fun b hb => ?_
        rcases Nat.lt_succ_iff_lt_or_eq.1 hb with hb | rfl
        · exact hO b hb
        · exact fun j => ((p b).subsingleton_iff Y j).2 (hall j)
      · push Not at hall
        obtain ⟨j₀, hj₀⟩ := hall
        obtain ⟨Z, φ, g, h, hT, hZiso, hZfin, hZlt⟩ :=
          exists_kill k (p a) (hdiv a haN) (hP a haN) (hself a haN) Y (hF a haN) j₀ hj₀
        have hZ : S Z := by
          refine ihd _ (hd ▸ (p a).totalDim_lt k (hF a haN) j₀ hZiso hZlt) Z rfl
            (hQC _ hT (hQCP a haN _) hY) (fun b hb => ?_) (fun b hb => ?_)
          · -- the first vertex: from `hfin` when `a ≤ b`, from orthogonality when `b < a`
            have hFb : (p b).FT k ((p a).P⟦-j₀⟧) := by
              rcases lt_or_ge b a with hba | hab
              · exact Probe.FT.of_orth k (p b) (Probe.Orth.shift (p b) (horth a haN b hba) _)
              · exact Probe.FT.shift k (p b) (hfin a haN b hb hab) _
            exact Probe.FT.obj₃ k (p b) hT hFb (hF b hb)
          · exact Probe.Orth.obj₃ (p b) hT (Probe.Orth.shift (p b) (horth a haN b hb) _)
              (hO b hb)
        exact hS _ hT (hSP a haN _) hZ

end Main

end Stacks.Triangulated.ProbeKilling
