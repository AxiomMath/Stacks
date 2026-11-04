module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Data.Int.ConditionallyCompleteOrder

@[expose] public section

/-
# Problem Description

This problem concerns derived categories and inverse systems of abelian groups
(Stacks Project, Section 15.88; this is Stacks Tag 0CQ9 / Lemma 15.88.11).

We work with the following objects.

1. The index category `N`: the directed set of (positive) integers ordered by the
   usual ordering, regarded as a category.  An *inverse system* indexed by `N` is a
   functor on `Nᵒᵖ`.  In Lean we use `ℕ` (which is `0`-indexed); this only shifts the
   indexing and does not change the mathematics.

2. Inverse systems of abelian groups `Ab(N)`: the category of functors
   `Nᵒᵖ ⥤ Ab`.  An object is a family of abelian groups `(A_n)` together with
   transition homomorphisms `A_{n+1} → A_n`; a morphism is a family of homomorphisms
   commuting with the transition maps.  This is an abelian category (a functor category
   into an abelian category is abelian).  In Lean, `Ab` is `AddCommGrpCat` and
   `Ab(N)` is `ℕᵒᵖ ⥤ AddCommGrpCat`.

3. The derived categories `D(Ab)` and `D(Ab(N))`: the (Verdier) localizations of the
   homotopy categories of cochain complexes at the quasi-isomorphisms.  These are
   `DerivedCategory AddCommGrpCat` and `DerivedCategory (ℕᵒᵖ ⥤ AddCommGrpCat)`.

4. The componentwise (evaluation) functor `ev_n : D(Ab(N)) ⥤ D(Ab)` for an index `n`.
   It is induced by the exact additive functor `Ab(N) ⥤ Ab`, `(A_n) ↦ A_n`, i.e. the
   evaluation functor `(evaluation Nᵒᵖ Ab).obj n`.  Since evaluation is exact it lifts
   to derived categories via `Functor.mapDerivedCategory`.  The transition maps of an
   inverse system induce, for each morphism `f : a ⟶ b` of `Nᵒᵖ`, a natural
   transformation `ev_a ⟶ ev_b` of functors `D(Ab(N)) ⥤ D(Ab)`; this is `evTrans f`
   below, the derived image of the evaluation natural transformation.

5. An *inverse system of objects of `D(Ab)`* is a functor `Nᵒᵖ ⥤ D(Ab)` (Definition 5
   of the problem).  Note this is *not* the same as an object of `D(Ab(N))`, because
   `D(Ab)` is not abelian and the transition maps live only in the derived category.

# Main Statement (Stacks Tag 0CQ9 / Lemma 15.88.11)

Every inverse system `K : Nᵒᵖ ⥤ D(Ab)` of objects of `D(Ab)` lifts to an object
`M` of `D(Ab(N))`: there is `M ∈ D(Ab(N))` and isomorphisms `ψ_n : ev_n(M) ≅ K_n`
in `D(Ab)` compatible with all transition maps, i.e. for every morphism `f : a ⟶ b`
in `Nᵒᵖ` the square

```
  ev_a(M)  --evTrans f-->  ev_b(M)
    |                         |
  ψ_a                       ψ_b
    v                         v
   K_a    --- K.map f --->   K_b
```

commutes in `D(Ab)`.  Here the top arrow is the transition morphism in `D(Ab)`
induced by the object `M` of `D(Ab(N))` (evaluation of `M`), and the bottom arrow is
the given transition morphism of the inverse system `K`.

No claim of functoriality or uniqueness of the lift `M` is made; the statement asserts
only existence of `M` together with compatible isomorphisms.
-/

open CategoryTheory

namespace Stacks.InverseSystem.AbelianGroupDerivedLift

universe u

/-- `Ab(N)`, the category of inverse systems of abelian groups indexed by `ℕ`, that is,
functors `ℕᵒᵖ ⥤ Ab`. -/
abbrev AbN : Type (u + 1) := ℕᵒᵖ ⥤ Ab.{u}

/-- `Ab` admits a derived category (we use the standard model). -/
noncomputable instance instHasDerivedCategoryAb : HasDerivedCategory Ab.{u} :=
  HasDerivedCategory.standard _

/-- `Ab(N)` admits a derived category (we use the standard model). -/
noncomputable instance instHasDerivedCategoryAbN : HasDerivedCategory AbN.{u} :=
  HasDerivedCategory.standard _

/-- The componentwise functor `ev_n : D(Ab(N)) ⥤ D(Ab)` at the index `n`.
It is the derived functor of the exact additive evaluation functor
`(evaluation Nᵒᵖ Ab).obj n : Ab(N) ⥤ Ab`. -/
noncomputable abbrev evD (n : ℕᵒᵖ) : DerivedCategory AbN.{u} ⥤ DerivedCategory Ab.{u} :=
  ((evaluation ℕᵒᵖ Ab.{u}).obj n).mapDerivedCategory

/-- The transition natural transformation `ev_a ⟶ ev_b` of functors
`D(Ab(N)) ⥤ D(Ab)` induced by a morphism `f : a ⟶ b` of `Nᵒᵖ`.  It is the image in
the derived categories of the evaluation natural transformation
`(evaluation Nᵒᵖ Ab).map f`.  Applied to an object `M` of `D(Ab(N))` it produces the
transition morphism `ev_a(M) → ev_b(M)` in `D(Ab)` coming from the inverse-system
structure of `M`. -/
noncomputable def evTrans {a b : ℕᵒᵖ} (f : a ⟶ b) : evD.{u} a ⟶ evD.{u} b :=
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso AbN.{u} (ComplexShape.up ℤ))
    (((evaluation ℕᵒᵖ Ab.{u}).obj a).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (((evaluation ℕᵒᵖ Ab.{u}).obj b).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (evD a) (evD b)
    (Functor.whiskerRight
      (NatTrans.mapHomologicalComplex ((evaluation ℕᵒᵖ Ab.{u}).map f) (ComplexShape.up ℤ))
      DerivedCategory.Q)

@[simp]
theorem evTrans_id (a : ℕᵒᵖ) : evTrans (𝟙 a) = 𝟙 (evD.{u} a) := by
  unfold evTrans
  rw [(evaluation ℕᵒᵖ Ab.{u}).map_id, NatTrans.mapHomologicalComplex_id,
    Functor.whiskerRight_id']
  exact Localization.liftNatTrans_id _ _ _ _

@[simp]
theorem evTrans_comp {a b c : ℕᵒᵖ} (g : a ⟶ b) (h : b ⟶ c) :
    evTrans.{u} (g ≫ h) = evTrans g ≫ evTrans h := by
  unfold evTrans
  rw [(evaluation ℕᵒᵖ Ab.{u}).map_comp, NatTrans.mapHomologicalComplex_comp,
    Functor.whiskerRight_comp]
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso AbN.{u} (ComplexShape.up ℤ))
  intro X
  simp [Localization.liftNatTrans_app]

/-- The value of `evTrans f` on an object in the image of `Q`, expressed via
`Functor.mapDerivedCategoryFactors`: it is the degree-wise evaluation chain map of `f`,
conjugated by the comparison isomorphisms.  This lets one compute with `evTrans` without
unfolding the underlying `Localization.liftNatTrans`. -/
theorem evTrans_app_Q_obj {a b : ℕᵒᵖ} (f : a ⟶ b) (X : CochainComplex AbN.{u} ℤ) :
    (evTrans f).app (DerivedCategory.Q.obj X) =
      ((Functor.mapDerivedCategoryFactors ((evaluation ℕᵒᵖ Ab.{u}).obj a)).app X).hom ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
            ((evaluation ℕᵒᵖ Ab.{u}).map f) (ComplexShape.up ℤ)).app X) ≫
          ((Functor.mapDerivedCategoryFactors ((evaluation ℕᵒᵖ Ab.{u}).obj b)).app X).inv := by
  rw [evTrans, Localization.liftNatTrans_app]
  rfl

/-- To check that a family of isomorphisms `ψ n : ev_n(M) ≅ K_n` is compatible with all
transition maps of the inverse system `K`, it suffices to check compatibility with the
successor maps `op (n+1) ⟶ op n`. -/
theorem comm_of_comm_succ {M : DerivedCategory AbN.{u}} {K : ℕᵒᵖ ⥤ DerivedCategory Ab.{u}}
    (ψ : ∀ n, (evD n).obj M ≅ K.obj n)
    (hsucc : ∀ n : ℕ,
      (evTrans (homOfLE (Nat.le_succ n)).op).app M ≫ (ψ (Opposite.op n)).hom
        = (ψ (Opposite.op (n+1))).hom ≫ K.map (homOfLE (Nat.le_succ n)).op) :
    ∀ ⦃a b : ℕᵒᵖ⦄ (f : a ⟶ b), (evTrans f).app M ≫ (ψ b).hom = (ψ a).hom ≫ K.map f := by
  have hom_eq : ∀ {x y : ℕᵒᵖ} (f g : x ⟶ y), f = g := fun _ _ => Subsingleton.elim _ _
  -- the compatibility square holds for every `op m ⟶ op k` with `k ≤ m`, by induction on `m`
  have P_op : ∀ (k m : ℕ) (h : k ≤ m),
      (evTrans ((homOfLE h).op : (Opposite.op m : ℕᵒᵖ) ⟶ Opposite.op k)).app M
          ≫ (ψ (Opposite.op k)).hom
        = (ψ (Opposite.op m)).hom ≫ K.map ((homOfLE h).op) := by
    intro k m h
    induction m, h using Nat.le_induction with
    | base =>
      rw [hom_eq (homOfLE (le_refl k)).op (𝟙 _), evTrans_id, K.map_id, NatTrans.id_app,
        Category.id_comp, Category.comp_id]
    | succ m hkm ih =>
      rw [hom_eq (homOfLE (hkm.trans (Nat.le_succ m))).op
        ((homOfLE (Nat.le_succ m)).op ≫ (homOfLE hkm).op), evTrans_comp, NatTrans.comp_app,
        Category.assoc, ih, ← Category.assoc, hsucc m, K.map_comp, Category.assoc]
  intro a b f
  obtain ⟨a', rfl⟩ : ∃ a', Opposite.op a' = a := ⟨a.unop, rfl⟩
  obtain ⟨b', rfl⟩ : ∃ b', Opposite.op b' = b := ⟨b.unop, rfl⟩
  rw [hom_eq f (homOfLE (leOfHom f.unop)).op]
  exact P_op b' a' (leOfHom f.unop)

-- Construction toolkit for the lift.

namespace Construction

open DerivedCategory

-- the definitional identifications of `liftDeg`/`liftCpx` with the chosen complexes `cpx`
-- are only reducible-transparency defeq
set_option backward.isDefEq.respectTransparency false

variable (K : ℕᵒᵖ ⥤ DerivedCategory Ab.{u})

/-- The successor transition morphism `K(op (n+1)) ⟶ K(op n)` of the system. -/
noncomputable def succMap (n : ℕ) : K.obj (Opposite.op (n+1)) ⟶ K.obj (Opposite.op n) :=
  K.map (homOfLE (Nat.le_succ n)).op

/-- A "stage" of the inductive construction: a cochain complex of abelian groups
together with an isomorphism `Q(C) ≅ K(op n)` in the derived category. -/
structure Stage (n : ℕ) where
  /-- The chosen cochain complex of abelian groups representing `K (op n)`. -/
  C : CochainComplex Ab.{u} ℤ
  /-- The isomorphism in `D(Ab)` identifying `Q C` with `K (op n)`. -/
  ψ : Q.obj C ≅ K.obj (Opposite.op n)

/-- The base stage at `n = 0`: choose a complex representing `K(op 0)`. -/
noncomputable def baseStage : Stage K 0 :=
  ⟨Q.objPreimage (K.obj (Opposite.op 0)), Q.objObjPreimageIso (K.obj (Opposite.op 0))⟩

/-- One step of the inductive construction on top of a stage `s` at `n`: a stage at `n+1`,
an honest chain map down to the stage `s`, and the square it makes commute in `D(Ab)`. -/
structure StepData (n : ℕ) (s : Stage K n) where
  /-- The stage at `n+1`. -/
  next : Stage K (n+1)
  /-- The chain map from the complex at `n+1` down to the complex of `s`. -/
  hom : next.C ⟶ s.C
  /-- The chain map realizes the transition morphism of `K` in `D(Ab)`. -/
  w : Q.map hom ≫ s.ψ.hom = next.ψ.hom ≫ succMap K n

/-- The inductive step.  Given a stage at `n`, produce a stage at `n+1` together with an
honest chain map to the stage at `n` realizing the transition map in `D(Ab)`. -/
noncomputable def stepData (n : ℕ) (s : Stage K n) : StepData K n s := by
  classical
  -- the target object of the new stage in the derived category
  let Knext := K.obj (Opposite.op (n+1))
  -- a complex representing it, and the representing isomorphism
  let C0 : CochainComplex Ab.{u} ℤ := Q.objPreimage Knext
  let ψ0 : Q.obj C0 ≅ Knext := Q.objObjPreimageIso Knext
  -- the composite morphism  Q(C0) ⟶ Knext ⟶ K(op n) ⟶ Q(s.C)  in D(Ab)
  let φ : Q.obj C0 ⟶ Q.obj s.C := ψ0.hom ≫ succMap K n ≫ s.ψ.inv
  -- represent φ by a right roof:  φ = inv (Q sec) ≫ Q g'
  have hrf := DerivedCategory.right_fac φ
  let X' : CochainComplex Ab.{u} ℤ := hrf.choose
  let sec : X' ⟶ C0 := hrf.choose_spec.choose
  have hiso : IsIso (Q.map sec) := hrf.choose_spec.choose_spec.choose
  let g' : X' ⟶ s.C := hrf.choose_spec.choose_spec.choose_spec.choose
  have hfac : φ = inv (Q.map sec) ≫ Q.map g' :=
    hrf.choose_spec.choose_spec.choose_spec.choose_spec
  -- the new stage
  refine ⟨⟨X', (asIso (Q.map sec)) ≪≫ ψ0⟩, g', ?_⟩
  -- prove the commuting square
  have hQg : Q.map g' = Q.map sec ≫ φ := by
    rw [hfac]
    simp
  rw [hQg]
  change (Q.map sec ≫ (ψ0.hom ≫ succMap K n ≫ s.ψ.inv)) ≫ s.ψ.hom
      = ((asIso (Q.map sec)) ≪≫ ψ0).hom ≫ succMap K n
  simp only [Iso.trans_hom, asIso_hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The recursively defined family of stages. -/
noncomputable def stage : (n : ℕ) → Stage K n
  | 0 => baseStage K
  | (n+1) => (stepData K n (stage n)).next

/-- The chosen representing complex at index `n`. -/
noncomputable def cpx (n : ℕ) : CochainComplex Ab.{u} ℤ :=
  (stage K n).C

/-- The representing isomorphism `Q(cpx n) ≅ K(op n)`. -/
noncomputable def psi (n : ℕ) : Q.obj (cpx K n) ≅ K.obj (Opposite.op n) := (stage K n).ψ

/-- The chosen complex at `0` is the one picked by the base stage. -/
theorem cpx_zero : cpx K 0 = (baseStage K).C := rfl

/-- The chosen complex at `n+1` is the one produced by the inductive step at `n`. -/
theorem cpx_succ (n : ℕ) : cpx K (n+1) = (stepData K n (stage K n)).next.C := rfl

/-- The representing isomorphism at `0` is the one picked by the base stage. -/
theorem psi_zero : psi K 0 = (baseStage K).ψ := rfl

/-- The representing isomorphism at `n+1` is the one produced by the inductive step. -/
theorem psi_succ (n : ℕ) : psi K (n+1) = (stepData K n (stage K n)).next.ψ := rfl

/-- The honest chain map `cpx (n+1) ⟶ cpx n` realizing the transition map. -/
noncomputable def cpxSuccMap (n : ℕ) : cpx K (n+1) ⟶ cpx K n :=
  (stepData K n (stage K n)).hom

/-- The commuting square for the successor transition. -/
@[reassoc]
theorem Q_map_cpxSuccMap_comp_psi (n : ℕ) :
    Q.map (cpxSuccMap K n) ≫ (psi K n).hom = (psi K (n+1)).hom ≫ succMap K n :=
  (stepData K n (stage K n)).w

/-- The degree-`i` piece of the inverse system of complexes: the functor `ℕᵒᵖ ⥤ Ab`
sending `op n` to `(cpx n).X i`, with transition maps the degree-`i` parts of
`cpxSuccMap`. -/
noncomputable def liftDeg (i : ℤ) : AbN.{u} :=
  Functor.ofOpSequence (X := fun n => (cpx K n).X i) (fun n => (cpxSuccMap K n).f i)

/-- The value of `liftDeg K i` at `op n` is the degree-`i` part of the chosen complex
`cpx K n`. -/
@[simp]
theorem liftDeg_obj (i : ℤ) (n : ℕ) : (liftDeg K i).obj (Opposite.op n) = (cpx K n).X i :=
  rfl

/-- The transition map of `liftDeg K i` from `op (n+1)` to `op n` is the degree-`i` part of
`cpxSuccMap K n`. -/
@[simp]
theorem liftDeg_map_succ (i : ℤ) (n : ℕ) :
    (liftDeg K i).map (homOfLE (Nat.le_succ n)).op = (cpxSuccMap K n).f i := by
  simp only [liftDeg, Functor.ofOpSequence_map_homOfLE_succ]

/-- The inverse system of cochain complexes packaged as a single cochain complex in the
abelian category `Ab(N)` of inverse systems. -/
noncomputable def liftCpx : CochainComplex AbN.{u} ℤ where
  X i := liftDeg K i
  d i j := NatTrans.ofOpSequence (F := liftDeg K i) (G := liftDeg K j)
      (fun n => (cpx K n).d i j) (by
        intro n
        simp only [liftDeg_map_succ]
        exact (cpxSuccMap K n).comm i j)
  shape i j h := by
    apply NatTrans.ext
    funext n
    rw [NatTrans.ofOpSequence_app, Limits.zero_app,
      (cpx K (Opposite.unop n)).shape i j h]
  d_comp_d' i j k _ _ := by
    apply NatTrans.ext
    funext n
    rw [NatTrans.comp_app, NatTrans.ofOpSequence_app, NatTrans.ofOpSequence_app,
      Limits.zero_app, (cpx K (Opposite.unop n)).d_comp_d i j k]

/-- The degree-`i` part of `liftCpx K` is the inverse system `liftDeg K i`. -/
@[simp]
theorem liftCpx_X (i : ℤ) : (liftCpx K).X i = liftDeg K i := rfl

/-- The component at `op n` of the differential of `liftCpx K` is the differential of the
chosen complex `cpx K n`. -/
@[simp]
theorem liftCpx_d_app (i j : ℤ) (n : ℕ) :
    ((liftCpx K).d i j).app (Opposite.op n) = (cpx K n).d i j := rfl

/-- Evaluating the inverse system of complexes `liftCpx` at index `op n` recovers the
chosen complex `cpx K n` on the nose. -/
@[simp]
theorem eval_liftCpx (n : ℕ) :
    (((evaluation ℕᵒᵖ Ab.{u}).obj (Opposite.op n)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (liftCpx K) = cpx K n := by
  rfl

/-- The honest chain map obtained by evaluating the successor transition natural
transformation `eval(op (n+1)) ⟶ eval(op n)` on the inverse system of complexes
`liftCpx K` is exactly the chain map `cpxSuccMap K n`. -/
@[simp]
theorem evalMap_succ_liftCpx (n : ℕ) :
    (NatTrans.mapHomologicalComplex
        ((evaluation ℕᵒᵖ Ab.{u}).map (homOfLE (Nat.le_succ n)).op) (ComplexShape.up ℤ)).app
        (liftCpx K)
      = cpxSuccMap K n := by
  apply HomologicalComplex.hom_ext
  intro i
  change ((evaluation ℕᵒᵖ Ab.{u}).map (homOfLE (Nat.le_succ n)).op).app ((liftCpx K).X i)
      = (cpxSuccMap K n).f i
  exact liftDeg_map_succ K i n

end Construction

/-- The comparison isomorphism `(evD (op n)).obj (Q (liftCpx K)) ≅ Q (cpx K n)`, obtained
from `Functor.mapDerivedCategoryFactors` (the natural iso `Q ⋙ F.mapDerivedCategory ≅
F.mapHomologicalComplex ⋙ Q`) applied at the object `liftCpx K`, using `eval_liftCpx`. -/
noncomputable def evDQIso (K : ℕᵒᵖ ⥤ DerivedCategory Ab.{u}) (n : ℕ) :
    (evD (Opposite.op n)).obj (DerivedCategory.Q.obj (Construction.liftCpx K)) ≅
      DerivedCategory.Q.obj (Construction.cpx K n) :=
  ((Functor.mapDerivedCategoryFactors ((evaluation ℕᵒᵖ Ab.{u}).obj (Opposite.op n))).app
    (Construction.liftCpx K)) ≪≫
      DerivedCategory.Q.mapIso (eqToIso (Construction.eval_liftCpx K n))

/-- The lifting isomorphism `ev_n(Q(liftCpx K)) ≅ K_n`: the comparison isomorphism
`evDQIso` followed by the chosen representing isomorphism `psi`. -/
noncomputable def liftIso (K : ℕᵒᵖ ⥤ DerivedCategory Ab.{u}) (n : ℕᵒᵖ) :
    (evD n).obj (DerivedCategory.Q.obj (Construction.liftCpx K)) ≅ K.obj n :=
  evDQIso K n.unop ≪≫ Construction.psi K n.unop

-- works around the isDefEq-transparency change (eval_liftCpx / succMap are definitional)
set_option backward.isDefEq.respectTransparency false in
/-- The lifting isomorphisms `liftIso` are compatible with the successor transition maps of
the inverse system: this is the commuting square produced by the inductive construction,
transported along the comparison isomorphisms. -/
theorem liftIso_succ_comm (K : ℕᵒᵖ ⥤ DerivedCategory Ab.{u}) (n : ℕ) :
    (evTrans (homOfLE (Nat.le_succ n)).op).app
          (DerivedCategory.Q.obj (Construction.liftCpx K))
        ≫ (liftIso K (Opposite.op n)).hom
      = (liftIso K (Opposite.op (n+1))).hom ≫ K.map (homOfLE (Nat.le_succ n)).op := by
  rw [evTrans_app_Q_obj]
  simp only [liftIso, evDQIso, Iso.trans_hom, Category.assoc, Iso.inv_hom_id_assoc]
  rw [Iso.cancel_iso_hom_left, Construction.evalMap_succ_liftCpx]
  simpa [Construction.succMap, Construction.eval_liftCpx] using
    Construction.Q_map_cpxSuccMap_comp_psi K n

/-- **Stacks Tag 0CQ9 / Lemma 15.88.11.**
Every inverse system `K : Nᵒᵖ ⥤ D(Ab)` of objects of the derived category `D(Ab)`
lifts to an object `M` of `D(Ab(N))`: there exist an object `M` of `D(Ab(N))` and,
for every index `n`, an isomorphism `ψ n : ev_n(M) ≅ K_n` in `D(Ab)`, such that for
every morphism `f : a ⟶ b` of `Nᵒᵖ` the square
`ev_a(M) → ev_b(M) → K_b` and `ev_a(M) → K_a → K_b` commutes, i.e. the isomorphisms
`ψ` are compatible with the transition maps (the induced transition maps `evTrans f`
of `M` on the source, the given transition maps `K.map f` of the system on the
target). -/
@[stacks 0CQ9]
theorem exists_lift_of_inverseSystem (K : ℕᵒᵖ ⥤ DerivedCategory Ab.{u}) :
    ∃ (M : DerivedCategory AbN.{u}) (ψ : ∀ n, (evD n).obj M ≅ K.obj n),
      ∀ ⦃a b : ℕᵒᵖ⦄ (f : a ⟶ b),
        (evTrans f).app M ≫ (ψ b).hom = (ψ a).hom ≫ K.map f :=
  ⟨_, liftIso K, comm_of_comm_succ _ (liftIso_succ_comm K)⟩

end Stacks.InverseSystem.AbelianGroupDerivedLift
