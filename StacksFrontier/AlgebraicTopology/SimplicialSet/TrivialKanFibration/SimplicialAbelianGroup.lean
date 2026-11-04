module

public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.Refinements
public import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence
public import Mathlib.AlgebraicTopology.DoldKan.PInfty
public import StacksFrontier.AlgebraicTopology.SimplicialObject.ChainHomotopy
public import StacksFrontier.AlgebraicTopology.SimplicialSet.KanFibration
public import StacksFrontier.AlgebraicTopology.SimplicialSet.TrivialKanFibration

/-!
# Trivial Kan fibrations and quasi-isomorphisms of simplicial abelian groups

Let `f : X ⟶ Y` be a homomorphism of simplicial abelian groups, and write
`s = AlgebraicTopology.alternatingFaceMapComplex AddCommGrpCat` for the Moore complex functor,
with `s(Z)ₙ = Zₙ` and differential `∑ᵢ (-1)ⁱ dᵢ`. This file relates three conditions on `f`: that
its underlying morphism of simplicial *sets* be a homotopy equivalence, that `s(f)` be a
quasi-isomorphism, and — together with termwise surjectivity, every `X_n → Y_n` being onto — that
the underlying morphism of simplicial sets be a trivial Kan fibration, that is, have the right
lifting property with respect to every boundary inclusion `∂Δ[n].ι : ∂Δ[n] ⟶ Δ[n]`.

## Main results

* `SimplicialObject.trivialKanFibrations_whiskerRight_forget_of_surjective_of_quasiIso`:
  a termwise surjective homomorphism of simplicial abelian groups which is a quasi-isomorphism on
  associated chain complexes is a trivial Kan fibration of underlying simplicial sets.
* `AlgebraicTopology.quasiIso_alternatingFaceMapComplex_map_of_homotopyEquivalences_forget`:
  a morphism of simplicial abelian groups whose underlying morphism of simplicial sets is a
  homotopy equivalence induces a quasi-isomorphism of Moore complexes.

## References

* [Stacks, Tag 08NL](https://stacks.math.columbia.edu/tag/08NL)
* [Stacks, Tag 08NZ](https://stacks.math.columbia.edu/tag/08NZ)
* [Stacks, Tag 08P0](https://stacks.math.columbia.edu/tag/08P0)
* [Stacks, Tag 08P1](https://stacks.math.columbia.edu/tag/08P1)
* [Stacks, Tag 08P2](https://stacks.math.columbia.edu/tag/08P2)
* [Stacks, Tag 019C](https://stacks.math.columbia.edu/tag/019C)
* [Stacks, Tag 019N](https://stacks.math.columbia.edu/tag/019N)
* [Stacks, Tag 019T](https://stacks.math.columbia.edu/tag/019T)
* [Stacks, Tag 019Y](https://stacks.math.columbia.edu/tag/019Y)
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.SimplicialObject AlgebraicTopology
  HomotopicalAlgebra SSet SSet.modelCategoryQuillen Simplicial

universe u

/-! ### Elements, and identities of homomorphisms of abelian groups applied to them -/

namespace SimplicialAbelianGroup

/-- A composite of homomorphisms of abelian groups which vanishes, applied to an element. -/
private lemma comp_hom_apply_eq_zero {A B C : AddCommGrpCat.{u}} {g : A ⟶ B} {h : B ⟶ C}
    (H : g ≫ h = 0) (a : A) : h.hom (g.hom a) = 0 := by
  simpa using ConcreteCategory.congr_hom H a

/-- The homomorphism `ℤ → M` sending `1` to `z`: an element of an abelian group, read as a
morphism. -/
private def gen {M : AddCommGrpCat.{u}} (z : M) : AddCommGrpCat.of (ULift.{u} ℤ) ⟶ M :=
  AddCommGrpCat.ofHom (AddMonoidHom.mk' (fun t : ULift.{u} ℤ => t.down • z)
    (fun a b => add_zsmul z a.down b.down))

private lemma gen_apply {M : AddCommGrpCat.{u}} (z : M) (t : ULift.{u} ℤ) :
    (gen z).hom t = t.down • z := rfl

private lemma gen_apply_one {M : AddCommGrpCat.{u}} (z : M) :
    (gen z).hom (ULift.up (1 : ℤ)) = z := one_zsmul z

private lemma gen_comp {M N : AddCommGrpCat.{u}} (z : M) (u : M ⟶ N) :
    gen z ≫ u = gen (u.hom z) := by
  ext t
  rw [AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply, gen_apply, gen_apply, map_zsmul]

private lemma gen_zero {M : AddCommGrpCat.{u}} : gen (0 : M) = 0 := by
  ext t
  rw [gen_apply, smul_zero]
  rfl

/-- A morphism `θ : ℤ → M` whose composite with `u : M ⟶ N` is the element `z` of `N`, read as a
morphism, exhibits `z` in the image of `u`. -/
private lemma exists_apply_eq_of_comp_eq_gen {M N : AddCommGrpCat.{u}} {u : M ⟶ N} {z : N}
    (θ : AddCommGrpCat.of (ULift.{u} ℤ) ⟶ M) (h : θ ≫ u = gen z) : ∃ a : M, u.hom a = z :=
  ⟨θ.hom (ULift.up (1 : ℤ)), by rw [← gen_apply_one z, ← h]; rfl⟩

/-- An element whose reading as a morphism vanishes is zero. -/
private lemma eq_zero_of_gen_eq_zero {M : AddCommGrpCat.{u}} {z : M} (h : gen z = 0) : z = 0 := by
  rw [← gen_apply_one z, h]
  simp

/-! ### Homology classes of cycles -/

section Homology

variable {C D : ChainComplex AddCommGrpCat.{u} ℕ}

private lemma d_apply_eq_zero_of_map {n : ℕ} (u : C ⟶ D) (z : C.X n)
    (hz : (C.d n ((ComplexShape.down ℕ).next n)).hom z = 0) :
    (D.d n ((ComplexShape.down ℕ).next n)).hom ((u.f n).hom z) = 0 := by
  rw [← ConcreteCategory.comp_apply, u.comm, ConcreteCategory.comp_apply, hz, map_zero]

private lemma gen_comp_d {n : ℕ} (z : C.X n)
    (hz : (C.d n ((ComplexShape.down ℕ).next n)).hom z = 0) :
    gen z ≫ C.d n ((ComplexShape.down ℕ).next n) = 0 := by
  rw [gen_comp, hz, gen_zero]

/-- The homology class of a cycle `z`, as a homomorphism `ℤ → Hₙ(C)`. -/
private noncomputable def clsHom (C : ChainComplex AddCommGrpCat.{u} ℕ) {n : ℕ} (z : C.X n)
    (hz : (C.d n ((ComplexShape.down ℕ).next n)).hom z = 0) :
    AddCommGrpCat.of (ULift.{u} ℤ) ⟶ C.homology n :=
  C.liftCycles (gen z) _ rfl (gen_comp_d z hz) ≫ C.homologyπ n

/-- The homology class of a cycle is natural in the complex. -/
private lemma clsHom_comp_homologyMap (u : C ⟶ D) {n : ℕ} (z : C.X n)
    (hz : (C.d n ((ComplexShape.down ℕ).next n)).hom z = 0) :
    clsHom C z hz ≫ HomologicalComplex.homologyMap u n
      = clsHom D ((u.f n).hom z) (d_apply_eq_zero_of_map u z hz) := by
  have hu := d_apply_eq_zero_of_map u z hz
  have h : C.liftCycles (gen z) _ rfl (gen_comp_d z hz) ≫ HomologicalComplex.cyclesMap u n
      = D.liftCycles (gen ((u.f n).hom z)) _ rfl (gen_comp_d _ hu) := by
    rw [← cancel_mono (D.iCycles n), Category.assoc, HomologicalComplex.cyclesMap_i,
      ← Category.assoc, HomologicalComplex.liftCycles_i, HomologicalComplex.liftCycles_i, gen_comp]
  rw [clsHom, clsHom, Category.assoc, HomologicalComplex.homologyπ_naturality,
    ← Category.assoc, h]

/-- The class of a cycle depends only on the cycle. -/
private lemma clsHom_congr (C : ChainComplex AddCommGrpCat.{u} ℕ) {n : ℕ} {z z' : C.X n}
    (h : z = z') (hz : (C.d n ((ComplexShape.down ℕ).next n)).hom z = 0)
    (hz' : (C.d n ((ComplexShape.down ℕ).next n)).hom z' = 0) :
    clsHom C z hz = clsHom C z' hz' := by
  subst h; rfl

/-- Every homology class is the class of a cycle. -/
private lemma exists_clsHom_eq (C : ChainComplex AddCommGrpCat.{u} ℕ) (n : ℕ)
    (ξ : C.homology n) :
    ∃ (z : C.X n) (hz : (C.d n ((ComplexShape.down ℕ).next n)).hom z = 0),
      clsHom C z hz = gen ξ := by
  obtain ⟨c, hc⟩ := (AddCommGrpCat.epi_iff_surjective (C.homologyπ n)).mp inferInstance ξ
  have hz : (C.d n ((ComplexShape.down ℕ).next n)).hom ((C.iCycles n).hom c) = 0 :=
    comp_hom_apply_eq_zero (C.iCycles_d n ((ComplexShape.down ℕ).next n)) c
  refine ⟨_, hz, ?_⟩
  have h : C.liftCycles (gen ((C.iCycles n).hom c)) _ rfl (gen_comp_d _ hz) = gen c := by
    rw [← cancel_mono (C.iCycles n), HomologicalComplex.liftCycles_i, gen_comp]
  rw [clsHom, h, gen_comp, hc]

/-- The class of a boundary vanishes. -/
private lemma clsHom_eq_zero_of_boundary (C : ChainComplex AddCommGrpCat.{u} ℕ) {n : ℕ}
    (b : C.X (n + 1)) (z : C.X n) (hb : (C.d (n + 1) n).hom b = z)
    (hz : (C.d n ((ComplexShape.down ℕ).next n)).hom z = 0) :
    clsHom C z hz = 0 := by
  rw [clsHom]
  exact C.liftCycles_homologyπ_eq_zero_of_boundary (gen z) _ rfl (gen b)
    (by rw [gen_comp, hb])

/-- A cycle whose class vanishes is a boundary. -/
private lemma exists_boundary_of_clsHom_eq_zero (C : ChainComplex AddCommGrpCat.{u} ℕ) {n : ℕ}
    (z : C.X n) (hz : (C.d n ((ComplexShape.down ℕ).next n)).hom z = 0)
    (h : clsHom C z hz = 0) :
    ∃ b : C.X (n + 1), (C.d (n + 1) n).hom b = z := by
  obtain ⟨A', π, hπ, x₁, hx₁⟩ :=
    (C.comp_homologyπ_eq_zero_iff_up_to_refinements (n + 1) n (ChainComplex.prev ℕ n)
      (C.liftCycles (gen z) _ rfl (gen_comp_d z hz))).mp h
  obtain ⟨a, ha⟩ := (AddCommGrpCat.epi_iff_surjective π).mp hπ (ULift.up (1 : ℤ))
  refine ⟨x₁.hom a, ?_⟩
  have key : π ≫ gen z = (x₁ ≫ C.d (n + 1) n) := by
    rw [← HomologicalComplex.liftCycles_i (K := C) (gen z) _ rfl (gen_comp_d z hz),
      ← Category.assoc, hx₁, Category.assoc, HomologicalComplex.toCycles_i]
  have h := ConcreteCategory.congr_hom key a
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, ha, gen_apply_one] at h
  exact h.symm

/-- A cycle whose class is killed by an isomorphism on homology is a boundary. -/
private lemma exists_boundary_of_isIso_homologyMap (u : C ⟶ D) {n : ℕ}
    [IsIso (HomologicalComplex.homologyMap u n)] (z : C.X n)
    (hz : (C.d n ((ComplexShape.down ℕ).next n)).hom z = 0)
    (h : clsHom C z hz ≫ HomologicalComplex.homologyMap u n = 0) :
    ∃ b : C.X (n + 1), (C.d (n + 1) n).hom b = z := by
  refine exists_boundary_of_clsHom_eq_zero C z hz ?_
  rw [← cancel_mono (HomologicalComplex.homologyMap u n), zero_comp]
  exact h

end Homology

/-! ### Simplicial identities and naturality, applied to elements -/

section Simplicial

variable {X Y : SimplicialObject AddCommGrpCat.{u}}

private lemma δ_δ_apply {l : ℕ} (a : X _⦋l + 2⦌) {j k : Fin (l + 3)} (hjk : j < k) :
    (X.δ (k.pred (Fin.ne_zero_of_lt hjk))).hom ((X.δ j).hom a)
      = (X.δ (j.castPred (Fin.ne_last_of_lt hjk))).hom ((X.δ k).hom a) := by
  obtain ⟨j, rfl⟩ := j.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hjk)
  obtain ⟨k, rfl⟩ := k.eq_succ_of_ne_zero (Fin.ne_zero_of_lt hjk)
  rw [Fin.pred_succ, Fin.castPred_castSucc]
  exact (ConcreteCategory.congr_hom (X.δ_comp_δ (by grind)) a).symm

/-! ### Compatible families of faces -/

/-- The case `(j, k) = (0, i + 1)` of the compatibility `dⱼ x_k = d_{k - 1} x_j` (`j < k`) of a
family of `(l + 1)`-simplices: `dᵢ x₀ = d₀ x_{i + 1}`. -/
private lemma compat_zero_succ {l : ℕ} {x : Fin (l + 3) → X _⦋l + 1⦌}
    (hx : ∀ (j k : Fin (l + 3)) (hjk : j < k),
      (X.δ (k.pred (Fin.ne_zero_of_lt hjk))).hom (x j)
        = (X.δ (j.castPred (Fin.ne_last_of_lt hjk))).hom (x k))
    (i : Fin (l + 2)) : (X.δ i).hom (x 0) = (X.δ 0).hom (x i.succ) := by
  simpa only [Fin.pred_succ, Fin.castPred_zero] using hx 0 i.succ (Fin.succ_pos i)

/-- **Subtracting the faces of a horn filler annihilates the remaining datum.** If the faces
`dⱼ v` of an element `v` are the members `x j` of a compatible family for every `j ≠ 0`, then
*every* face of `x 0 - d₀ v` vanishes. -/
private lemma δ_apply_sub_eq_zero {l : ℕ} {x : Fin (l + 3) → X _⦋l + 1⦌}
    (hx : ∀ (j k : Fin (l + 3)) (hjk : j < k),
      (X.δ (k.pred (Fin.ne_zero_of_lt hjk))).hom (x j)
        = (X.δ (j.castPred (Fin.ne_last_of_lt hjk))).hom (x k))
    {v : X _⦋l + 2⦌} (hv : ∀ (j : Fin (l + 3)), j ≠ 0 → (X.δ j).hom v = x j) (i : Fin (l + 2)) :
    (X.δ i).hom (x 0 - (X.δ 0).hom v) = 0 := by
  have hv' : (X.δ i).hom ((X.δ 0).hom v) = (X.δ 0).hom ((X.δ i.succ).hom v) :=
    compat_zero_succ (x := fun j => (X.δ j).hom v) (fun _ _ hjk => δ_δ_apply v hjk) i
  rw [map_sub, compat_zero_succ hx i, ← hv i.succ (Fin.succ_ne_zero i), hv', sub_self]

end Simplicial

/-! ### Normalization: the Dold–Kan projection -/

section Normalization

variable {X Y : SimplicialObject AddCommGrpCat.{u}}

/-- The faces `dᵢ` with `i ≥ 1` vanish on the image of the Dold–Kan projection. -/
private lemma pInfty_comp_δ_succ {l : ℕ} (i : Fin (l + 1)) :
    (DoldKan.PInfty.f (l + 1) : X _⦋l + 1⦌ ⟶ X _⦋l + 1⦌) ≫ X.δ i.succ = 0 := by
  rw [DoldKan.PInfty_f]
  exact DoldKan.HigherFacesVanish.of_P (l + 1) l i le_add_self

/-- On the image of the Dold–Kan projection the differential is the zeroth face map. -/
private lemma pInfty_comp_d (l : ℕ) :
    (DoldKan.PInfty.f (l + 1) : X _⦋l + 1⦌ ⟶ X _⦋l + 1⦌)
        ≫ (AlternatingFaceMapComplex.obj X).d (l + 1) l
      = (DoldKan.PInfty.f (l + 1) : X _⦋l + 1⦌ ⟶ X _⦋l + 1⦌) ≫ X.δ 0 := by
  rw [AlternatingFaceMapComplex.obj_d_eq, Preadditive.comp_sum, Fin.sum_univ_succ]
  simp [pInfty_comp_δ_succ]

/-- The Dold–Kan projection fixes an element of `Xₙ` all of whose faces `dᵢ` with `i ≥ 1`
vanish. -/
private lemma pInfty_apply_eq_self {l : ℕ} (x : X _⦋l + 1⦌)
    (hx : ∀ i : Fin (l + 1), (X.δ i.succ).hom x = 0) :
    ((DoldKan.PInfty.f (l + 1) : X _⦋l + 1⦌ ⟶ X _⦋l + 1⦌)).hom x = x := by
  have hv : DoldKan.HigherFacesVanish (l + 1) (gen x) := fun j _ => by
    rw [gen_comp, hx j, gen_zero]
  have key : gen x ≫ DoldKan.PInfty.f (l + 1) = gen x := by
    rw [DoldKan.PInfty_f]
    exact hv.comp_P_eq_self
  have h : ((DoldKan.PInfty.f (l + 1) : X _⦋l + 1⦌ ⟶ X _⦋l + 1⦌)).hom
      ((gen x).hom (ULift.up (1 : ℤ))) = (gen x).hom (ULift.up (1 : ℤ)) :=
    ConcreteCategory.congr_hom key _
  rwa [gen_apply_one] at h

/-- The faces `dᵢ` with `i ≥ 1` of an element fixed by the Dold–Kan projection vanish. -/
private lemma δ_succ_apply_eq_zero_of_pInfty {l : ℕ} (x : X _⦋l + 1⦌)
    (hx : ((DoldKan.PInfty.f (l + 1) : X _⦋l + 1⦌ ⟶ X _⦋l + 1⦌)).hom x = x)
    (i : Fin (l + 1)) : (X.δ i.succ).hom x = 0 := by
  have h := comp_hom_apply_eq_zero (pInfty_comp_δ_succ (X := X) i) x
  rwa [hx] at h

/-- On an element fixed by the Dold–Kan projection the differential is the zeroth face map. -/
private lemma d_apply_eq_δ_zero_apply_of_pInfty {l : ℕ} (x : X _⦋l + 1⦌)
    (hx : ((DoldKan.PInfty.f (l + 1) : X _⦋l + 1⦌ ⟶ X _⦋l + 1⦌)).hom x = x) :
    ((AlternatingFaceMapComplex.obj X).d (l + 1) l).hom x = (X.δ 0).hom x := by
  have := ConcreteCategory.congr_hom (pInfty_comp_d (X := X) l) x
  rwa [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hx] at this

/-- An element all of whose faces vanish is a cycle. -/
private lemma d_apply_eq_zero {l : ℕ} (z : X _⦋l + 1⦌)
    (hz : ∀ i : Fin (l + 2), (X.δ i).hom z = 0) :
    ((AlternatingFaceMapComplex.obj X).d (l + 1) l).hom z = 0 := by
  rw [d_apply_eq_δ_zero_apply_of_pInfty z (pInfty_apply_eq_self z fun i => hz i.succ), hz 0]

/-- The Dold–Kan projection is idempotent. -/
private lemma pInfty_apply_pInfty_apply {n : ℕ} (x : X _⦋n⦌) :
    ((DoldKan.PInfty.f n : X _⦋n⦌ ⟶ X _⦋n⦌)).hom
        ((DoldKan.PInfty.f n : X _⦋n⦌ ⟶ X _⦋n⦌).hom x)
      = (DoldKan.PInfty.f n : X _⦋n⦌ ⟶ X _⦋n⦌).hom x :=
  ConcreteCategory.congr_hom (DoldKan.PInfty_f_idem n) x

/-- The image of a normalized element under a homomorphism of simplicial abelian groups is
normalized. -/
private lemma pInfty_apply_map (f : X ⟶ Y) {n : ℕ} (x : X _⦋n⦌)
    (hx : ((DoldKan.PInfty.f n : X _⦋n⦌ ⟶ X _⦋n⦌)).hom x = x) :
    ((DoldKan.PInfty.f n : Y _⦋n⦌ ⟶ Y _⦋n⦌)).hom ((f.app _).hom x) = (f.app _).hom x := by
  rw [← ConcreteCategory.comp_apply, DoldKan.PInfty_f_naturality, ConcreteCategory.comp_apply,
    hx]

/-- **A normalized boundary is the boundary of a normalized element**: if `z` is normalized and is
the boundary of `b`, then it is the boundary of the normalization of `b`. -/
private lemma d_pInfty_apply {n : ℕ} (b : X _⦋n + 1⦌) {z : X _⦋n⦌}
    (hb : ((AlternatingFaceMapComplex.obj X).d (n + 1) n).hom b = z)
    (hz : ((DoldKan.PInfty.f n : X _⦋n⦌ ⟶ X _⦋n⦌)).hom z = z) :
    ((AlternatingFaceMapComplex.obj X).d (n + 1) n).hom
        ((DoldKan.PInfty.f (n + 1) : X _⦋n + 1⦌ ⟶ X _⦋n + 1⦌).hom b) = z := by
  rw [← ConcreteCategory.comp_apply, (DoldKan.PInfty (X := X)).comm, ConcreteCategory.comp_apply,
    hb, hz]

end Normalization

/-! ### The kernel of a termwise surjective homomorphism is acyclic -/

section Kernel

variable {X Y : SimplicialObject AddCommGrpCat.{u}}

/-- The simplicial abelian group of kernels of the components of a homomorphism `f : X ⟶ Y` of
simplicial abelian groups. -/
@[implicit_reducible]
private def kerObj (f : X ⟶ Y) : SimplicialObject AddCommGrpCat.{u} where
  obj n := AddCommGrpCat.of (f.app n).hom.ker
  map {n m} g := AddCommGrpCat.ofHom
    { toFun := fun a => ⟨(X.map g).hom a.1, by
        have h : (f.app m).hom ((X.map g).hom a.1) = (Y.map g).hom ((f.app n).hom a.1) :=
          NatTrans.naturality_apply f g a.1
        simp [h, AddMonoidHom.mem_ker.mp a.2]⟩
      map_zero' := by apply Subtype.ext; simp
      map_add' := fun a b => by apply Subtype.ext; simp }
  map_id n := by ext a; simp
  map_comp _ _ := by ext a; simp

/-- The inclusion of the kernel of `f` into `X`. -/
@[implicit_reducible]
private def kerι (f : X ⟶ Y) : kerObj f ⟶ X where
  app n := AddCommGrpCat.ofHom (f.app n).hom.ker.subtype
  naturality _ _ _ := rfl

private lemma kerι_app_apply (f : X ⟶ Y) {n : SimplexCategoryᵒᵖ} (a : (kerObj f).obj n) :
    ((kerι f).app n).hom a = a.1 :=
  rfl

/-- The short complex `0 → s(Ker f) → s(X) → s(Y) → 0` of associated chain complexes. -/
@[implicit_reducible]
private noncomputable def kerSeq (f : X ⟶ Y) : ShortComplex (ChainComplex AddCommGrpCat.{u} ℕ) :=
  ShortComplex.mk ((alternatingFaceMapComplex AddCommGrpCat.{u}).map (kerι f))
    ((alternatingFaceMapComplex AddCommGrpCat.{u}).map f) (by
      rw [← Functor.map_comp, show kerι f ≫ f = 0 from by
          ext n a
          rw [NatTrans.comp_app, AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply, kerι_app_apply]
          exact AddMonoidHom.mem_ker.mp a.property,
        Functor.map_zero])

private lemma kerSeq_shortExact (f : X ⟶ Y)
    (hf : ∀ n : SimplexCategoryᵒᵖ, Function.Surjective (f.app n).hom) :
    (kerSeq f).ShortExact := by
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
  intro i
  have hepi : Epi ((kerSeq f).map
      (HomologicalComplex.eval AddCommGrpCat.{u} (ComplexShape.down ℕ) i)).g := by
    dsimp only [kerSeq, ShortComplex.map_g, HomologicalComplex.eval_map,
      alternatingFaceMapComplex_map_f]
    exact (AddCommGrpCat.epi_iff_surjective _).mpr (hf _)
  have hmono : Mono ((kerSeq f).map
      (HomologicalComplex.eval AddCommGrpCat.{u} (ComplexShape.down ℕ) i)).f := by
    dsimp only [kerSeq, ShortComplex.map_f, HomologicalComplex.eval_map,
      alternatingFaceMapComplex_map_f]
    rw [AddCommGrpCat.mono_iff_injective]
    intro a b hab
    rw [kerι_app_apply, kerι_app_apply] at hab
    exact Subtype.ext hab
  have hexact : ((kerSeq f).map
      (HomologicalComplex.eval AddCommGrpCat.{u} (ComplexShape.down ℕ) i)).Exact := by
    rw [ShortComplex.ab_exact_iff]
    intro a ha
    dsimp only [kerSeq, ShortComplex.map_f, ShortComplex.map_g, HomologicalComplex.eval_map,
      alternatingFaceMapComplex_map_f] at ha ⊢
    exact ⟨⟨a, AddMonoidHom.mem_ker.mpr ha⟩, rfl⟩
  exact { mono_f := hmono, epi_g := hepi, exact := hexact }

private lemma kerObj_exactAt (f : X ⟶ Y)
    (hf : ∀ n : SimplexCategoryᵒᵖ, Function.Surjective (f.app n).hom)
    [QuasiIso ((alternatingFaceMapComplex AddCommGrpCat.{u}).map f)] (n : ℕ) :
    (AlternatingFaceMapComplex.obj (kerObj f)).ExactAt n := by
  have hS := kerSeq_shortExact f hf
  have hij : (ComplexShape.down ℕ).Rel (n + 1) n := by simp
  have hiso : ∀ m, IsIso (HomologicalComplex.homologyMap (kerSeq f).g m) := fun m =>
    (_root_.quasiIsoAt_iff_isIso_homologyMap
      ((alternatingFaceMapComplex AddCommGrpCat.{u}).map f) m).mp inferInstance
  rw [show (AlternatingFaceMapComplex.obj (kerObj f)) = (kerSeq f).X₁ from rfl,
    HomologicalComplex.exactAt_iff_isZero_homology]
  have h2 : HomologicalComplex.homologyMap (kerSeq f).f n = 0 :=
    (hS.homology_exact₂ n).mono_g_iff.mp inferInstance
  have h3 : hS.δ (n + 1) n hij = 0 := zero_of_epi_comp _ (hS.comp_δ (n + 1) n hij)
  have : Epi (hS.δ (n + 1) n hij) := (hS.homology_exact₁ (n + 1) n hij).epi_f h2
  rw [Limits.IsZero.iff_id_eq_zero, ← cancel_epi (hS.δ (n + 1) n hij), Category.comp_id, h3,
    zero_comp]

/-- A cycle in the chain complex associated to `Ker(f)` is a boundary there. -/
private lemma exists_kerObj_d_eq (f : X ⟶ Y)
    (hf : ∀ n : SimplexCategoryᵒᵖ, Function.Surjective (f.app n).hom)
    [QuasiIso ((alternatingFaceMapComplex AddCommGrpCat.{u}).map f)] {m : ℕ}
    (k : (kerObj f) _⦋m⦌)
    (hk : ((AlternatingFaceMapComplex.obj (kerObj f)).d m
      ((ComplexShape.down ℕ).next m)).hom k = 0) :
    ∃ c : (kerObj f) _⦋m + 1⦌,
      ((AlternatingFaceMapComplex.obj (kerObj f)).d (m + 1) m).hom c = k := by
  have h := ((AlternatingFaceMapComplex.obj (kerObj f)).exactAt_iff' (m + 1) m
    ((ComplexShape.down ℕ).next m) (by simp) rfl).mp (kerObj_exactAt f hf m)
  rw [ShortComplex.ab_exact_iff] at h
  exact h k hk

/-- **The kernel of a termwise surjective quasi-isomorphism is acyclic**: a cycle of the
associated chain complex which lies in `Ker(f)` is the boundary of an element of `Ker(f)`. -/
private lemma exists_ker_boundary (f : X ⟶ Y)
    (hf : ∀ n : SimplexCategoryᵒᵖ, Function.Surjective (f.app n).hom)
    [QuasiIso ((alternatingFaceMapComplex AddCommGrpCat.{u}).map f)] {m : ℕ} (x : X _⦋m⦌)
    (hx : (f.app _).hom x = 0)
    (hxd : ((AlternatingFaceMapComplex.obj X).d m
      ((ComplexShape.down ℕ).next m)).hom x = 0) :
    ∃ b : X _⦋m + 1⦌, (f.app _).hom b = 0 ∧
      ((AlternatingFaceMapComplex.obj X).d (m + 1) m).hom b = x := by
  have hι : ∀ (p q : ℕ) (c : (kerObj f) _⦋p⦌),
      (((AlternatingFaceMapComplex.obj (kerObj f)).d p q).hom c).val
        = ((AlternatingFaceMapComplex.obj X).d p q).hom c.val := fun p q c =>
    ConcreteCategory.congr_hom
      (((alternatingFaceMapComplex AddCommGrpCat.{u}).map (kerι f)).comm p q).symm c
  have hcycle : ((AlternatingFaceMapComplex.obj (kerObj f)).d m
      ((ComplexShape.down ℕ).next m)).hom ⟨x, hx⟩ = 0 := Subtype.ext ((hι _ _ _).trans hxd)
  obtain ⟨c, hc⟩ := exists_kerObj_d_eq f hf ⟨x, hx⟩ hcycle
  exact ⟨c.val, AddMonoidHom.mem_ker.mp c.2, (hι _ _ c).symm.trans (congrArg Subtype.val hc)⟩

/-- An element of `Ker(f)ₘ` which is a cycle fixed by the Dold–Kan projection is `d₀ z` for an
element `z` of `Ker(f)_{m + 1}` whose other faces vanish. -/
private lemma exists_normalized (f : X ⟶ Y)
    (hf : ∀ n : SimplexCategoryᵒᵖ, Function.Surjective (f.app n).hom)
    [QuasiIso ((alternatingFaceMapComplex AddCommGrpCat.{u}).map f)] {m : ℕ} (x : X _⦋m⦌)
    (hx : (f.app _).hom x = 0)
    (hxd : ((AlternatingFaceMapComplex.obj X).d m
      ((ComplexShape.down ℕ).next m)).hom x = 0)
    (hxP : ((DoldKan.PInfty.f m : X _⦋m⦌ ⟶ X _⦋m⦌)).hom x = x) :
    ∃ z : X _⦋m + 1⦌, (f.app _).hom z = 0 ∧ (∀ i : Fin (m + 1), (X.δ i.succ).hom z = 0) ∧
      (X.δ 0).hom z = x := by
  obtain ⟨b, hb0, hbd⟩ := exists_ker_boundary f hf x hx hxd
  refine ⟨(DoldKan.PInfty.f (m + 1) : X _⦋m + 1⦌ ⟶ X _⦋m + 1⦌).hom b, ?_, ?_, ?_⟩
  · rw [← ConcreteCategory.comp_apply, ← DoldKan.PInfty_f_naturality,
      ConcreteCategory.comp_apply, hb0, map_zero]
  · intro i
    simpa using ConcreteCategory.congr_hom (pInfty_comp_δ_succ (X := X) i) b
  · rw [← ConcreteCategory.comp_apply, ← (DoldKan.PInfty.comm (m + 1) m).symm.trans
      (pInfty_comp_d (X := X) m), ConcreteCategory.comp_apply, hbd, hxP]

end Kernel

/-! ### The faces of a morphism out of the boundary of a simplex -/

section Boundary

variable {X Y : SimplicialObject AddCommGrpCat.{u}}

/-- The two ways of including a `2`-codimensional face of `Δ[n + 2]` into its boundary agree. -/
private lemma δ_comp_boundary_ι {n : ℕ} {j k : Fin (n + 3)} (hjk : j < k) :
    stdSimplex.δ (k.pred (Fin.ne_zero_of_lt hjk)) ≫ boundary.ι.{u} j
      = stdSimplex.δ (j.castPred (Fin.ne_last_of_lt hjk)) ≫ boundary.ι.{u} k := by
  rw [← cancel_mono (Subcomplex.ι _), Category.assoc, Category.assoc, boundary.ι_ι,
    boundary.ι_ι]
  obtain ⟨j, rfl⟩ := j.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hjk)
  obtain ⟨k, rfl⟩ := k.eq_succ_of_ne_zero (Fin.ne_zero_of_lt hjk)
  rw [Fin.pred_succ, Fin.castPred_castSucc]
  exact (stdSimplex.δ_comp_δ (by grind)).symm

/-- The compatibility satisfied by the faces of a morphism out of `∂Δ[n + 2]`:
`dᵢ x_j = d_{j - 1} xᵢ` for `i < j`. -/
private lemma δ_yonedaEquivObj_boundary_ι {n : ℕ}
    (t : (∂Δ[n + 2] : SSet.{u}) ⟶ X ⋙ forget AddCommGrpCat.{u}) {j k : Fin (n + 3)}
    (hjk : j < k) :
    (X.δ (k.pred (Fin.ne_zero_of_lt hjk))).hom
        (yonedaEquivObj X (n + 1) (boundary.ι j ≫ t))
      = (X.δ (j.castPred (Fin.ne_last_of_lt hjk))).hom
        (yonedaEquivObj X (n + 1) (boundary.ι k ≫ t)) := by
  rw [δ_yonedaEquivObj, δ_yonedaEquivObj, ← Category.assoc, ← Category.assoc,
    δ_comp_boundary_ι hjk]

/-- The faces of a morphism out of `∂Δ[l + 2]`, translated by the faces of an element `w`, are
again compatible. -/
private lemma δ_apply_sub_compat {l : ℕ}
    (t : (∂Δ[l + 2] : SSet.{u}) ⟶ X ⋙ forget AddCommGrpCat.{u}) (w : X _⦋l + 2⦌)
    {j k : Fin (l + 3)} (hjk : j < k) :
    (X.δ (k.pred (Fin.ne_zero_of_lt hjk))).hom
        (yonedaEquivObj X (l + 1) (boundary.ι j ≫ t) - (X.δ j).hom w)
      = (X.δ (j.castPred (Fin.ne_last_of_lt hjk))).hom
        (yonedaEquivObj X (l + 1) (boundary.ι k ≫ t) - (X.δ k).hom w) := by
  rw [map_sub, map_sub, δ_yonedaEquivObj_boundary_ι t hjk, δ_δ_apply w hjk]

/-- The faces of a morphism out of `∂Δ[m + 1]`, translated by the faces of an element `w`, are the
faces of a morphism out of the horn `Λ[m + 1, 0]`. -/
private lemma isCompatible_sub {m : ℕ}
    (t : (∂Δ[m + 1] : SSet.{u}) ⟶ X ⋙ forget AddCommGrpCat.{u}) (w : X _⦋m + 1⦌) :
    horn.IsCompatible (i := (0 : Fin (m + 2))) (fun j _ => (yonedaEquivObj X m).symm
      (yonedaEquivObj X m (boundary.ι j ≫ t) - (X.δ j).hom w)) := by
  obtain _ | l := m
  · simp
  · rw [horn.isCompatible_iff]
    intro j k _ _ hjk
    exact (yonedaEquivObj X l).injective (by
      simpa only [← δ_yonedaEquivObj, Equiv.apply_symm_apply] using δ_apply_sub_compat t w hjk)

end Boundary

/-! ### The lifting problem, on elements -/

section Lifting

variable {X Y : SimplicialObject AddCommGrpCat.{u}}

/-- **The lifting problem, on elements.** Let `f : X ⟶ Y` be termwise surjective and a
quasi-isomorphism on associated chain complexes, let `t : ∂Δ[m + 1] ⟶ X` be a morphism out of the
boundary — that is, a family of faces `xⱼ ∈ X _⦋m⦌` satisfying `dᵢ x_j = d_{j - 1} xᵢ` for `i < j`
— and let `y ∈ Y _⦋m + 1⦌` be such that `dⱼ y = f xⱼ` for every `j`. Then there is an
`a ∈ X _⦋m + 1⦌` with `dⱼ a = xⱼ` for every `j` and `f a = y`. -/
private lemma exists_δ_apply_eq (f : X ⟶ Y)
    (hf : ∀ n : SimplexCategoryᵒᵖ, Function.Surjective (f.app n).hom)
    [QuasiIso ((alternatingFaceMapComplex AddCommGrpCat.{u}).map f)] {m : ℕ}
    (t : (∂Δ[m + 1] : SSet.{u}) ⟶ X ⋙ forget AddCommGrpCat.{u}) (y : Y _⦋m + 1⦌)
    (ht : ∀ j : Fin (m + 2),
      (f.app _).hom (yonedaEquivObj X m (boundary.ι j ≫ t)) = (Y.δ j).hom y) :
    ∃ a : X _⦋m + 1⦌,
      (∀ j : Fin (m + 2), (X.δ j).hom a = yonedaEquivObj X m (boundary.ι j ≫ t)) ∧
        (f.app _).hom a = y := by
  have hδ : ∀ (i : Fin (m + 2)) (a : X _⦋m + 1⦌),
      (f.app _).hom ((X.δ i).hom a) = (Y.δ i).hom ((f.app _).hom a) :=
    fun _ a => NatTrans.naturality_apply f _ a
  have hfib : Fibration (Functor.whiskerRight f (forget AddCommGrpCat.{u})) :=
    CategoryTheory.SimplicialObject.fibration_whiskerRight_forget_of_surjective
      (Functor.whiskerRight f (forget₂ AddCommGrpCat.{u} AddGrpCat.{u})) hf
  obtain ⟨w, hw⟩ := hf (Opposite.op ⦋m + 1⦌) y
  obtain ⟨x, hx⟩ : ∃ x : Fin (m + 2) → X _⦋m⦌,
      ∀ j, x j = yonedaEquivObj X m (boundary.ι j ≫ t) - (X.δ j).hom w := ⟨_, fun _ => rfl⟩
  have hker : ∀ j, (f.app _).hom (x j) = 0 := fun j => by
    rw [hx, map_sub, ht j, hδ j w, hw, sub_self]
  have hcompat : horn.IsCompatible (i := (0 : Fin (m + 2)))
      (fun j _ => (yonedaEquivObj X m).symm (x j)) := by
    simpa only [hx] using isCompatible_sub t w
  obtain ⟨φ, hφδ, hφ0⟩ := hcompat.exists_lift
    (Functor.whiskerRight f (forget AddCommGrpCat.{u})) ((yonedaEquivObj Y (m + 1)).symm 0)
    (fun j _ => (yonedaEquivObj Y m).injective (by
      rw [← app_yonedaEquivObj, Equiv.apply_symm_apply, ← δ_yonedaEquivObj,
        Equiv.apply_symm_apply, map_zero]
      exact hker j))
  obtain ⟨v, hvdef⟩ : ∃ v : X _⦋m + 1⦌, v = yonedaEquivObj X (m + 1) φ := ⟨_, rfl⟩
  have hv0 : (f.app _).hom v = 0 := by
    rw [hvdef, app_yonedaEquivObj, hφ0, Equiv.apply_symm_apply]
  have hv : ∀ (j : Fin (m + 2)), j ≠ 0 → (X.δ j).hom v = x j := fun j hj => by
    rw [hvdef, δ_yonedaEquivObj, hφδ j hj, Equiv.apply_symm_apply]
  have hzker : (f.app _).hom (x 0 - (X.δ 0).hom v) = 0 := by
    rw [map_sub, hker 0, hδ 0 v, hv0, map_zero, sub_zero]
  obtain ⟨hzP, hzd⟩ : ((DoldKan.PInfty.f m : X _⦋m⦌ ⟶ X _⦋m⦌)).hom (x 0 - (X.δ 0).hom v)
        = x 0 - (X.δ 0).hom v ∧
      ((AlternatingFaceMapComplex.obj X).d m ((ComplexShape.down ℕ).next m)).hom
        (x 0 - (X.δ 0).hom v) = 0 := by
    obtain _ | l := m
    · exact ⟨by rw [DoldKan.PInfty_f_0]; rfl, by
        rw [ChainComplex.next_nat_zero, HomologicalComplex.shape _ _ _ (by simp)]; simp⟩
    · have hfaces := δ_apply_sub_eq_zero
        (fun _ _ hjk => by simp only [hx]; exact δ_apply_sub_compat t w hjk) hv
      exact ⟨pInfty_apply_eq_self _ fun i => hfaces i.succ, by
        rw [ChainComplex.next_nat_succ]; exact d_apply_eq_zero _ hfaces⟩
  obtain ⟨ζ, hζ0, hζδ, hζd⟩ := exists_normalized f hf _ hzker hzd hzP
  refine ⟨w + v + ζ, fun j => ?_, ?_⟩
  · rw [map_add, map_add]
    induction j using Fin.cases with
    | zero => rw [hζd, hx]; abel
    | succ i => rw [hζδ i, hv i.succ (Fin.succ_ne_zero i), hx]; abel
  · rw [map_add, map_add, hw, hv0, hζ0, add_zero, add_zero]

end Lifting

/-! ### Functors preserve homotopy equivalences -/

/-- A functor carries homotopic morphisms of simplicial objects to homotopic morphisms. -/
private lemma homotopic_whiskering {A : Type*} [Category A] {B : Type*} [Category B] (F : A ⥤ B)
    {U V : SimplicialObject A} {p q : U ⟶ V}
    (h : Relation.EqvGen (fun p q : U ⟶ V => Nonempty (Homotopy p q)) p q) :
    Relation.EqvGen (fun p q : U ⋙ F ⟶ V ⋙ F => Nonempty (Homotopy p q))
      (((SimplicialObject.whiskering A B).obj F).map p)
      (((SimplicialObject.whiskering A B).obj F).map q) :=
  Relation.EqvGen.map _ (fun _ _ hpq => ⟨hpq.some.whiskerRight F⟩) h

/-- **A functor carries a homotopy equivalence of simplicial objects to a homotopy
equivalence.** -/
private lemma homotopyEquivalences_whiskering {A : Type*} [Category A] {B : Type*} [Category B]
    (F : A ⥤ B) {U V : SimplicialObject A} {a : U ⟶ V}
    (ha : SimplicialObject.homotopyEquivalences A a) :
    SimplicialObject.homotopyEquivalences B
      (((SimplicialObject.whiskering A B).obj F).map a) := by
  obtain ⟨b, hab, hba⟩ := ha
  refine ⟨((SimplicialObject.whiskering A B).obj F).map b, ?_, ?_⟩
  · simpa [Functor.map_comp] using homotopic_whiskering F hab
  · simpa [Functor.map_comp] using homotopic_whiskering F hba

/-! ### The free simplicial abelian group on the underlying simplicial set -/

section Free

variable {X Y : SimplicialObject AddCommGrpCat.{u}}

/-- `ℤ[X]`: the simplicial abelian group of free abelian groups on the degrees of the underlying
simplicial set of `X`. -/
@[implicit_reducible]
private def freeObj (X : SimplicialObject AddCommGrpCat.{u}) :
    SimplicialObject AddCommGrpCat.{u} :=
  (X ⋙ forget AddCommGrpCat.{u}) ⋙ AddCommGrpCat.free

/-- `ℤ[f]`, the map of free simplicial abelian groups induced by a map of simplicial sets. -/
@[implicit_reducible]
private def freeMap (f : X ⟶ Y) : freeObj X ⟶ freeObj Y :=
  Functor.whiskerRight (Functor.whiskerRight f (forget AddCommGrpCat.{u})) AddCommGrpCat.free

/-- Two homomorphisms out of a free abelian group agreeing on the generators agree. -/
private lemma free_hom_ext {α : Type u} {M : AddCommGrpCat.{u}}
    {g h : AddCommGrpCat.of (FreeAbelianGroup α) ⟶ M}
    (H : ∀ x : α, g.hom (FreeAbelianGroup.of x) = h.hom (FreeAbelianGroup.of x)) : g = h :=
  AddCommGrpCat.hom_ext (FreeAbelianGroup.lift_ext _ _ H)

/-- The evaluation `[m] ↦ m` of a free abelian group commutes with a homomorphism `u`. -/
private lemma lift_id_map_of {M N : AddCommGrpCat.{u}} (u : M ⟶ N) (x : M) :
    FreeAbelianGroup.lift (fun y : N => y) (FreeAbelianGroup.map u.hom (FreeAbelianGroup.of x))
      = u.hom (FreeAbelianGroup.lift (fun y : M => y) (FreeAbelianGroup.of x)) := by
  simp

/-- The evaluation `[m] ↦ m` sends `[x] - [0]` to `x`. -/
private lemma lift_id_of_sub_of_zero {M : AddCommGrpCat.{u}} (x : M) :
    FreeAbelianGroup.lift (fun y : M => y) (FreeAbelianGroup.of x - FreeAbelianGroup.of 0) = x := by
  simp

/-- The counit `ε_X : ℤ[X] ⟶ X`, `[x] ↦ x`. -/
@[implicit_reducible]
private def counit (X : SimplicialObject AddCommGrpCat.{u}) : freeObj X ⟶ X where
  app n := AddCommGrpCat.ofHom (FreeAbelianGroup.lift (fun x : X.obj n => x))
  naturality _ _ φ :=
    free_hom_ext fun x => lift_id_map_of (X.map φ) x

/-- The counit is natural: `ε_X ≫ f = ℤ[f] ≫ ε_Y`. -/
private lemma counit_naturality (f : X ⟶ Y) : counit X ≫ f = freeMap f ≫ counit Y :=
  NatTrans.ext (funext fun n => free_hom_ext fun x => (lift_id_map_of (f.app n) x).symm)

/-- The section `σ : Xₙ → ℤ[X]ₙ`, `x ↦ [x] - [0]`, of the counit. It is a map of simplicial sets,
not a homomorphism. -/
@[implicit_reducible]
private def sec {X : SimplicialObject AddCommGrpCat.{u}} {n : SimplexCategoryᵒᵖ} (x : X.obj n) :
    (freeObj X).obj n :=
  FreeAbelianGroup.of x - FreeAbelianGroup.of 0

private lemma sec_zero {n : SimplexCategoryᵒᵖ} : sec (0 : X.obj n) = 0 := sub_self _

/-- `[x] - [0]` commutes with every homomorphism of abelian groups, a homomorphism carrying `0`
to `0`. -/
private lemma freeAbelianGroup_map_sub_of_zero {M N : AddCommGrpCat.{u}} (u : M ⟶ N) (x : M) :
    FreeAbelianGroup.map u.hom (FreeAbelianGroup.of x - FreeAbelianGroup.of 0)
      = FreeAbelianGroup.of (u.hom x) - FreeAbelianGroup.of 0 := by
  rw [map_sub, FreeAbelianGroup.map_of_apply, FreeAbelianGroup.map_of_apply, map_zero]

/-- `σ` commutes with the face maps. -/
private lemma δ_apply_sec {n : ℕ} (i : Fin (n + 2)) (x : X _⦋n + 1⦌) :
    ((freeObj X).δ i).hom (sec x) = sec ((X.δ i).hom x) :=
  freeAbelianGroup_map_sub_of_zero (X.δ i) x

/-- `σ` is a section of the counit. -/
private lemma counit_app_sec {n : SimplexCategoryᵒᵖ} (x : X.obj n) :
    ((counit X).app n).hom (sec x) = x :=
  lift_id_of_sub_of_zero x

/-- `σ` is natural: `ℤ[f] ∘ σ = σ ∘ f`. -/
private lemma freeMap_app_sec (f : X ⟶ Y) {n : SimplexCategoryᵒᵖ} (x : X.obj n) :
    ((freeMap f).app n).hom (sec x) = sec ((f.app n).hom x) :=
  freeAbelianGroup_map_sub_of_zero (f.app n) x

end Free

/-! ### The section `σ` on cycles and boundaries -/

section Sec

variable {X : SimplicialObject AddCommGrpCat.{u}}

/-- **`σ` carries a normalized cycle to a cycle.** -/
private lemma d_apply_sec_eq_zero {n : ℕ} (x : X _⦋n⦌)
    (hxP : ((DoldKan.PInfty.f n : X _⦋n⦌ ⟶ X _⦋n⦌)).hom x = x)
    (hxd : ((AlternatingFaceMapComplex.obj X).d n ((ComplexShape.down ℕ).next n)).hom x = 0) :
    ((AlternatingFaceMapComplex.obj (freeObj X)).d n
      ((ComplexShape.down ℕ).next n)).hom (sec x) = 0 := by
  cases n with
  | zero =>
    rw [ChainComplex.next_nat_zero,
      (AlternatingFaceMapComplex.obj (freeObj X)).shape 0 0 (by simp)]
    simp
  | succ l =>
    rw [ChainComplex.next_nat_succ] at hxd
    have hfaces : ∀ i : Fin (l + 2), (X.δ i).hom x = 0 := by
      refine Fin.cases ?_ (fun j => δ_succ_apply_eq_zero_of_pInfty x hxP j)
      rw [← d_apply_eq_δ_zero_apply_of_pInfty x hxP]
      exact hxd
    rw [ChainComplex.next_nat_succ]
    refine d_apply_eq_zero _ fun i => ?_
    rw [δ_apply_sec, hfaces i, sec_zero]

/-- `σ` commutes with the differential on a normalized element. -/
private lemma d_apply_sec {l : ℕ} (b : X _⦋l + 1⦌)
    (hb : ((DoldKan.PInfty.f (l + 1) : X _⦋l + 1⦌ ⟶ X _⦋l + 1⦌)).hom b = b) :
    ((AlternatingFaceMapComplex.obj (freeObj X)).d (l + 1) l).hom (sec b)
      = sec (((AlternatingFaceMapComplex.obj X).d (l + 1) l).hom b) := by
  have hfaces : ∀ i : Fin (l + 1), ((freeObj X).δ i.succ).hom (sec b) = 0 := fun i => by
    rw [δ_apply_sec, δ_succ_apply_eq_zero_of_pInfty b hb i, sec_zero]
  rw [d_apply_eq_δ_zero_apply_of_pInfty (sec b) (pInfty_apply_eq_self _ hfaces),
    δ_apply_sec, d_apply_eq_δ_zero_apply_of_pInfty b hb]

/-- **`σ` carries a normalized boundary to a boundary**: if the normalized element `z` is the
boundary of `b`, then `σ(z)` is the boundary of `σ` of the normalization of `b`. -/
private lemma d_apply_sec_pInfty_apply {n : ℕ} (b : X _⦋n + 1⦌) {z : X _⦋n⦌}
    (hb : ((AlternatingFaceMapComplex.obj X).d (n + 1) n).hom b = z)
    (hz : ((DoldKan.PInfty.f n : X _⦋n⦌ ⟶ X _⦋n⦌)).hom z = z) :
    ((AlternatingFaceMapComplex.obj (freeObj X)).d (n + 1) n).hom
        (sec ((DoldKan.PInfty.f (n + 1) : X _⦋n + 1⦌ ⟶ X _⦋n + 1⦌).hom b)) = sec z := by
  rw [d_apply_sec _ (pInfty_apply_pInfty_apply b), d_pInfty_apply b hb hz]

end Sec

/-! ### Normalized representatives of homology classes -/

/-- The Dold–Kan projection induces the identity on homology. -/
private lemma homologyMap_pInfty (X : SimplicialObject AddCommGrpCat.{u}) (n : ℕ) :
    HomologicalComplex.homologyMap (DoldKan.PInfty (X := X)) n = 𝟙 _ := by
  rw [(DoldKan.homotopyPInftyToId X).homologyMap_eq n, HomologicalComplex.homologyMap_id]

/-- **Every homology class of the Moore complex is the class of a normalized cycle**: of an
element fixed by the Dold–Kan projection, hence one all of whose faces `dᵢ` with `i ≥ 1`
vanish. -/
private lemma exists_pInfty_rep (X : SimplicialObject AddCommGrpCat.{u}) (n : ℕ)
    (ξ : (AlternatingFaceMapComplex.obj X).homology n) :
    ∃ (x : X _⦋n⦌) (_hxP : ((DoldKan.PInfty.f n : X _⦋n⦌ ⟶ X _⦋n⦌)).hom x = x)
      (hxd : ((AlternatingFaceMapComplex.obj X).d n
        ((ComplexShape.down ℕ).next n)).hom x = 0),
      clsHom (AlternatingFaceMapComplex.obj X) x hxd = gen ξ := by
  obtain ⟨z, hz, hcls⟩ := exists_clsHom_eq (AlternatingFaceMapComplex.obj X) n ξ
  refine ⟨_, pInfty_apply_pInfty_apply z, d_apply_eq_zero_of_map (DoldKan.PInfty (X := X)) z hz,
    ?_⟩
  rw [← clsHom_comp_homologyMap (DoldKan.PInfty (X := X)) z hz, homologyMap_pInfty,
    Category.comp_id, hcls]

/-! ### The comparison of `s(f)` with `s(ℤ[f])` -/

section Comparison

variable {X Y : SimplicialObject AddCommGrpCat.{u}}

/-- `s` is a functor: the Moore complex of a composite is the composite of the Moore
complexes. -/
private lemma alternatingFaceMapComplex_map_comp {U V W : SimplicialObject AddCommGrpCat.{u}}
    (a : U ⟶ V) (b : V ⟶ W) :
    AlternatingFaceMapComplex.map (a ≫ b)
      = AlternatingFaceMapComplex.map a ≫ AlternatingFaceMapComplex.map b :=
  (alternatingFaceMapComplex AddCommGrpCat.{u}).map_comp a b

/-- The naturality square `ε_X ≫ f = ℤ[f] ≫ ε_Y`, on homology. -/
private lemma homologyMap_counit_naturality (f : X ⟶ Y) (n : ℕ) :
    HomologicalComplex.homologyMap (AlternatingFaceMapComplex.map (counit X)) n
        ≫ HomologicalComplex.homologyMap (AlternatingFaceMapComplex.map f) n
      = HomologicalComplex.homologyMap (AlternatingFaceMapComplex.map (freeMap f)) n
        ≫ HomologicalComplex.homologyMap (AlternatingFaceMapComplex.map (counit Y)) n := by
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    ← alternatingFaceMapComplex_map_comp, ← alternatingFaceMapComplex_map_comp,
    counit_naturality f]

/-- **`σ` is a section of the counit on homology classes**: the class of `σ(x)` in `H_n(s(ℤ[X]))`
is carried to the class of `x` by `H_n(s(ε_X))`. -/
private lemma clsHom_sec_comp_homologyMap_counit {n : ℕ} (x : X _⦋n⦌)
    (hxP : ((DoldKan.PInfty.f n : X _⦋n⦌ ⟶ X _⦋n⦌)).hom x = x)
    (hxd : ((AlternatingFaceMapComplex.obj X).d n ((ComplexShape.down ℕ).next n)).hom x = 0) :
    clsHom (AlternatingFaceMapComplex.obj (freeObj X)) (sec x) (d_apply_sec_eq_zero x hxP hxd)
        ≫ HomologicalComplex.homologyMap (AlternatingFaceMapComplex.map (counit X)) n
      = clsHom (AlternatingFaceMapComplex.obj X) x hxd := by
  rw [clsHom_comp_homologyMap]
  exact clsHom_congr _ (counit_app_sec x) _ hxd

/-- **`σ` carries a class killed by `f` to zero**: if the normalized cycle `x` of `s(X)` has
`f(x)` a boundary of `s(Y)`, then `H_n(s(ℤ[f]))` kills the class of `σ(x)`. -/
private lemma clsHom_sec_comp_homologyMap_freeMap_eq_zero (f : X ⟶ Y) {n : ℕ} (x : X _⦋n⦌)
    (hxP : ((DoldKan.PInfty.f n : X _⦋n⦌ ⟶ X _⦋n⦌)).hom x = x)
    (hxd : ((AlternatingFaceMapComplex.obj X).d n ((ComplexShape.down ℕ).next n)).hom x = 0)
    (b : Y _⦋n + 1⦌)
    (hb : ((AlternatingFaceMapComplex.obj Y).d (n + 1) n).hom b = (f.app _).hom x) :
    clsHom (AlternatingFaceMapComplex.obj (freeObj X)) (sec x) (d_apply_sec_eq_zero x hxP hxd)
        ≫ HomologicalComplex.homologyMap (AlternatingFaceMapComplex.map (freeMap f)) n = 0 := by
  rw [clsHom_comp_homologyMap]
  refine clsHom_eq_zero_of_boundary _
    (sec ((DoldKan.PInfty.f (n + 1) : Y _⦋n + 1⦌ ⟶ Y _⦋n + 1⦌).hom b)) _ ?_ _
  rw [d_apply_sec_pInfty_apply b hb (pInfty_apply_map f x hxP), AlternatingFaceMapComplex.map_f]
  exact (freeMap_app_sec f x).symm

/-- **`s(ℤ[f])` is a quasi-isomorphism** when the underlying morphism of simplicial sets of `f` is
a homotopy equivalence. -/
private lemma isIso_homologyMap_freeMap (f : X ⟶ Y)
    (hf : SimplicialObject.homotopyEquivalences (Type u)
      (Functor.whiskerRight f (forget AddCommGrpCat.{u}))) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (AlternatingFaceMapComplex.map (freeMap f)) n) := by
  have hfe : SimplicialObject.homotopyEquivalences AddCommGrpCat.{u} (freeMap f) :=
    homotopyEquivalences_whiskering AddCommGrpCat.free hf
  have hfree : QuasiIso (AlternatingFaceMapComplex.map (freeMap f)) := by
    obtain ⟨e, he⟩ := AlgebraicTopology.homotopyEquivalences_alternatingFaceMapComplex_map hfe
    rw [show AlternatingFaceMapComplex.map (freeMap f) = e.hom from he.symm]
    infer_instance
  exact (quasiIsoAt_iff_isIso_homologyMap _ n).mp (hfree.quasiIsoAt n)

/-- **Surjectivity of `H_n(s(f))`**, when `H_n(s(ℤ[f]))` is bijective. -/
private lemma surjective_homologyMap (f : X ⟶ Y) (n : ℕ)
    [IsIso (HomologicalComplex.homologyMap (AlternatingFaceMapComplex.map (freeMap f)) n)] :
    Function.Surjective
      (HomologicalComplex.homologyMap (AlternatingFaceMapComplex.map f) n).hom := fun ξ => by
  obtain ⟨y, hyP, hyd, hycls⟩ := exists_pInfty_rep Y n ξ
  refine exists_apply_eq_of_comp_eq_gen
    (clsHom (AlternatingFaceMapComplex.obj (freeObj Y)) (sec y) (d_apply_sec_eq_zero y hyP hyd)
      ≫ inv (HomologicalComplex.homologyMap (AlternatingFaceMapComplex.map (freeMap f)) n)
      ≫ HomologicalComplex.homologyMap (AlternatingFaceMapComplex.map (counit X)) n) ?_
  rw [Category.assoc, Category.assoc, homologyMap_counit_naturality f n,
    IsIso.inv_hom_id_assoc, clsHom_sec_comp_homologyMap_counit y hyP hyd, hycls]

/-- **Injectivity of `H_n(s(f))`**, when `H_n(s(ℤ[f]))` is bijective. -/
private lemma injective_homologyMap (f : X ⟶ Y) (n : ℕ)
    [IsIso (HomologicalComplex.homologyMap (AlternatingFaceMapComplex.map (freeMap f)) n)] :
    Function.Injective
      (HomologicalComplex.homologyMap (AlternatingFaceMapComplex.map f) n).hom := by
  rw [injective_iff_map_eq_zero]
  intro γ hγ
  obtain ⟨x, hxP, hxd, hxcls⟩ := exists_pInfty_rep X n γ
  have hfx := clsHom_comp_homologyMap (AlternatingFaceMapComplex.map f) x hxd
  rw [hxcls, gen_comp, hγ, gen_zero] at hfx
  obtain ⟨b, hb⟩ := exists_boundary_of_clsHom_eq_zero (AlternatingFaceMapComplex.obj Y) _ _
    hfx.symm
  obtain ⟨c, hc⟩ := exists_boundary_of_isIso_homologyMap
    (AlternatingFaceMapComplex.map (freeMap f)) (sec x) (d_apply_sec_eq_zero x hxP hxd)
    (clsHom_sec_comp_homologyMap_freeMap_eq_zero f x hxP hxd b hb)
  refine eq_zero_of_gen_eq_zero (M := (AlternatingFaceMapComplex.obj X).homology n) ?_
  rw [← hxcls, ← clsHom_sec_comp_homologyMap_counit x hxP hxd,
    clsHom_eq_zero_of_boundary _ c _ hc _, zero_comp]

end Comparison

end SimplicialAbelianGroup

namespace CategoryTheory.SimplicialObject

open SimplicialAbelianGroup in
/-- **Stacks 08P1**.
If `f : X ⟶ Y` is a
morphism of simplicial abelian groups such that `X_n → Y_n` is surjective for every `n` and such
that `s(X) → s(Y)` is a quasi-isomorphism of associated chain complexes, then the induced
morphism of underlying simplicial sets has the right lifting property with respect to all boundary
inclusions `∂Δ[n].ι : ∂Δ[n] ⟶ Δ[n]`. -/
@[stacks 08P1 "trivial Kan fibrations are the class `SSet.trivialKanFibrations` of Tag 08NL, \
  the right lifting class of the boundary inclusions, the source's surjectivity of `X₀ → Y₀` \
  being its case `n = 0`; the associated chain complex is `s`, Mathlib's \
  `alternatingFaceMapComplex`, the hypothesis being equivalent to the one for the normalized \
  complex `N` by Tag 019C"]
public theorem trivialKanFibrations_whiskerRight_forget_of_surjective_of_quasiIso
    {X Y : SimplicialObject AddCommGrpCat.{u}} (f : X ⟶ Y)
    (hf : ∀ n : SimplexCategoryᵒᵖ, Function.Surjective (f.app n).hom)
    [QuasiIso ((alternatingFaceMapComplex AddCommGrpCat.{u}).map f)] :
    SSet.trivialKanFibrations (Functor.whiskerRight f (forget AddCommGrpCat.{u})) := by
  intro A B p hp
  obtain ⟨n⟩ := hp
  -- the boundary inclusion's own source and target are also named `X` and `Y`; discard them so
  -- that `X` and `Y` again denote the two simplicial abelian groups
  clear X Y
  refine ⟨fun {t u} sq ↦ ?_⟩
  obtain _ | m := n
  · obtain ⟨a, ha⟩ := hf (Opposite.op ⦋0⦌) (yonedaEquivObj Y 0 u)
    exact ⟨⟨{ l := (yonedaEquivObj X 0).symm a
              fac_left := boundary.hom_ext₀
              fac_right := (yonedaEquivObj Y 0).injective (by
                rw [← app_yonedaEquivObj, Equiv.apply_symm_apply]; exact ha) }⟩⟩
  -- the square says that the faces of `t` and the element of `Y _⦋m + 1⦌` given by `u` satisfy the
  -- hypothesis of `exists_δ_apply_eq`, whose conclusion is the filler
  obtain ⟨a, haδ, haf⟩ := exists_δ_apply_eq f hf t (yonedaEquivObj Y (m + 1) u) (fun j => by
    rw [app_yonedaEquivObj, δ_yonedaEquivObj]
    congr 1
    rw [Category.assoc, sq.w, ← Category.assoc, boundary.ι_ι])
  exact ⟨⟨{ l := (yonedaEquivObj X (m + 1)).symm a
            fac_left := boundary.hom_ext fun j => by
              rw [← Category.assoc, boundary.ι_ι]
              exact (yonedaEquivObj X m).injective (by
                rw [← δ_yonedaEquivObj, Equiv.apply_symm_apply]; exact haδ j)
            fac_right := (yonedaEquivObj Y (m + 1)).injective (by
              rw [← app_yonedaEquivObj, Equiv.apply_symm_apply]; exact haf) }⟩⟩

end CategoryTheory.SimplicialObject

namespace AlgebraicTopology

open SimplicialAbelianGroup in
/-- **Stacks 08P2**.
Let `f : X ⟶ Y` be a morphism of simplicial
abelian groups whose underlying morphism of simplicial sets `X ⋙ forget ⟶ Y ⋙ forget` is a
homotopy equivalence, i.e. admits a morphism of simplicial sets back whose two composites with
it are homotopic to the identities ([Stacks, Tag 019N]). Then the induced morphism
`s(X) ⟶ s(Y)` of Moore complexes is a quasi-isomorphism. -/
@[stacks 08P2 "the homotopy equivalence is asked of the underlying simplicial sets, \
  `SimplicialObject.homotopyEquivalences (Type u)` (Tag 019N at `C = Type u`) applied to \
  `Functor.whiskerRight f (forget AddCommGrpCat)`; the associated chain complex is `s`, \
  Mathlib's `alternatingFaceMapComplex`, so that the conclusion is verbatim the hypothesis of \
  08P1, the version for the normalized complex `N` being equivalent to it by Tag 019C"]
public theorem quasiIso_alternatingFaceMapComplex_map_of_homotopyEquivalences_forget
    {X Y : SimplicialObject AddCommGrpCat.{u}} (f : X ⟶ Y)
    (hf : SimplicialObject.homotopyEquivalences (Type u)
      (Functor.whiskerRight f (forget AddCommGrpCat.{u}))) :
    QuasiIso ((alternatingFaceMapComplex AddCommGrpCat.{u}).map f) := by
  suffices h : ∀ n : ℕ, IsIso (HomologicalComplex.homologyMap
      (AlternatingFaceMapComplex.map f) n) from ⟨fun n =>
        (quasiIsoAt_iff_isIso_homologyMap _ n).mpr (h n)⟩
  intro n
  have := isIso_homologyMap_freeMap f hf n
  have _hm : Mono (HomologicalComplex.homologyMap (AlternatingFaceMapComplex.map f) n) :=
    (AddCommGrpCat.mono_iff_injective _).mpr (injective_homologyMap f n)
  have _he : Epi (HomologicalComplex.homologyMap (AlternatingFaceMapComplex.map f) n) :=
    (AddCommGrpCat.epi_iff_surjective _).mpr (surjective_homologyMap f n)
  exact isIso_of_mono_of_epi _

end AlgebraicTopology
