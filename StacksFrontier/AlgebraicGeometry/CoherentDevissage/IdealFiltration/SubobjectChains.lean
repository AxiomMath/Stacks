module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Abelian.CommSq
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.Topology.Sheaves.Abelian
public import StacksCore.CategoryTheory.Abelian.Subobject
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFiniteFreeSummand.TensorDualEndomorphism
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomSlice
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.DevissageFiltration
public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.SupportSeparation
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.IdealPowerSupport
public import StacksFrontier.AlgebraicGeometry.IrreducibleDevissage.GenericIdealPushforward
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Defs
public import StacksFrontier.AlgebraicGeometry.PushforwardCoherent
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Immersion
public import StacksFrontier.Topology.Noetherian.Defs

/-!
# Quotients of subobjects and concatenation of finite chains

Auxiliary results for [Stacks, Tag 01YF]: the image of the top subobject in a short exact
sequence, the invariance of a quotient of two comparable subobjects under pullback along an
epimorphism and pushforward along a monomorphism, the concatenation of two finite chains, and
the splitting of the last summand off a finite coproduct.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.DevissageNoetherian (isClosed_supp_of_isCoherent
  isZero_of_supp_eq_empty)
open Stacks.AlgebraicGeometry.IrreducibleDevissage (supp_subset_of_epi)
open Stacks.AlgebraicGeometry.RegularIdealSheaf (kernelSubmodule definingIdealOfHom
  mem_definingIdealOfHom)
open Stacks.SheafOfModules.OnSpace (sheafHom)

universe u

namespace Stacks.AlgebraicGeometry.CoherentDevissage

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

/-! ### Subobjects, their images, preimages and quotients -/

/-- In a short exact sequence the image of the top subobject under the first map is the kernel
subobject of the second. -/
theorem map_top_eq_kernelSubobject
    {C : Type u} [Category C] [Abelian C]
    (S : ShortComplex C) (hS : S.ShortExact) (hf : Mono S.f) :
    (Subobject.map S.f).obj ⊤ = kernelSubobject S.g := by
  let k : S.X₁ ⟶ kernel S.g := kernel.lift S.g S.f S.zero
  let l : kernel S.g ⟶ S.X₁ := hS.fIsKernel.lift
    (KernelFork.ofι (kernel.ι S.g) (kernel.condition S.g))
  have hk : k ≫ kernel.ι S.g = S.f := by simp [k]
  have hl : l ≫ S.f = kernel.ι S.g := by
    change hS.fIsKernel.lift (KernelFork.ofι (kernel.ι S.g) (kernel.condition S.g)) ≫
      S.f = kernel.ι S.g
    simpa using hS.fIsKernel.fac
      (KernelFork.ofι (kernel.ι S.g) (kernel.condition S.g)) WalkingParallelPair.zero
  let e : S.X₁ ≅ kernel S.g :=
    { hom := k
      inv := l
      hom_inv_id := by
        apply (cancel_mono S.f).mp
        calc
          (k ≫ l) ≫ S.f = k ≫ kernel.ι S.g := by rw [Category.assoc, hl]
          _ = S.f := hk
          _ = 𝟙 _ ≫ S.f := by simp
      inv_hom_id := by
        apply (cancel_mono (kernel.ι S.g)).mp
        calc
          (l ≫ k) ≫ kernel.ι S.g = l ≫ S.f := by rw [Category.assoc, hk]
          _ = kernel.ι S.g := hl
          _ = 𝟙 _ ≫ kernel.ι S.g := by simp }
  rw [Subobject.map_top, kernelSubobject]
  exact Subobject.mk_eq_mk_of_comm S.f (kernel.ι S.g) e hk

/-- Pulling two comparable subobjects back along an epimorphism does not change the quotient:
the comparison square is a pullback, so the induced map of cokernels is a monomorphism, and it
is an epimorphism because the pullback projection is. -/
def cokernelPullbackIso {C : Type u} [Category C] [Abelian C]
    {F Q : C} (q : F ⟶ Q) [Epi q]
    (B D : Subobject Q) (hBD : B ≤ D) :
    cokernel (Subobject.ofLE ((Subobject.pullback q).obj B) ((Subobject.pullback q).obj D)
      ((Subobject.pullback q).monotone hBD)) ≅
      cokernel (Subobject.ofLE B D hBD) := by
  let PB := (Subobject.pullback q).obj B
  let PD := (Subobject.pullback q).obj D
  let t : (PB : C) ⟶ (PD : C) :=
    Subobject.ofLE PB PD ((Subobject.pullback q).monotone hBD)
  let v : (B : C) ⟶ (D : C) := Subobject.ofLE B D hBD
  let pB := Subobject.pullbackπ q B
  let pD := Subobject.pullbackπ q D
  have ht : t ≫ PD.arrow = PB.arrow := by
    simp [t, PB, PD]
  have hp : t ≫ pD = pB ≫ v := by
    apply (cancel_mono D.arrow).mp
    calc
      (t ≫ pD) ≫ D.arrow = t ≫ (PD.arrow ≫ q) := by
        rw [Category.assoc, (Subobject.isPullback q D).w]
      _ = PB.arrow ≫ q := by rw [← Category.assoc, ht]
      _ = pB ≫ B.arrow := (Subobject.isPullback q B).w.symm
      _ = pB ≫ (v ≫ D.arrow) := by rw [Subobject.ofLE_arrow]
      _ = (pB ≫ v) ≫ D.arrow := by simp [Category.assoc]
  have houter : IsPullback (t ≫ PD.arrow) pB q (v ≫ D.arrow) := by
    rw [ht, Subobject.ofLE_arrow]
    exact (Subobject.isPullback q B).flip
  have hsquare : IsPullback t pB pD v :=
    houter.of_right hp (Subobject.isPullback q D).flip
  let β := cokernel.map t v pB pD hp
  haveI : Epi (pullback.fst D.arrow q) := Abelian.epi_pullback_of_epi_g D.arrow q
  let e := (Subobject.isPullback q D).isoPullback
  have heq : e.hom ≫ pullback.fst D.arrow q = pD := by
    simp [e, pD]
  have hproj : Epi pD := by
    rw [← heq]
    infer_instance
  have hcomp : cokernel.π t ≫ β = pD ≫ cokernel.π v := by
    change cokernel.π t ≫ cokernel.desc t (pD ≫ cokernel.π v) _ = pD ≫ cokernel.π v
    exact cokernel.π_desc _ _ _
  have : Mono β := Abelian.mono_cokernel_map_of_isPullback hsquare
  have : Epi β := epi_of_epi_fac hcomp
  have : IsIso β := isIso_of_mono_of_epi β
  exact asIso β

/-- The underlying object of a subobject is unchanged by pushing it forward along a
monomorphism. -/
def subobjectMapObjIso {C : Type u} [Category C]
    {A B : C} (f : A ⟶ B) [Mono f] (P : Subobject A) :
    (P : C) ≅ ((Subobject.map f).obj P : C) :=
  ((MonoOver.forget B ⋙ Over.forget B).mapIso
    ((Subobject.lowerCompRepresentativeIso (MonoOver.map f)).app P)).symm

/-- The comparison isomorphism of `subobjectMapObjIso` is compatible with the inclusions into
the ambient objects. -/
theorem subobjectMapObjIso_hom_arrow {C : Type u} [Category C]
    {A B : C} (f : A ⟶ B) [Mono f] (P : Subobject A) :
    (subobjectMapObjIso f P).hom ≫ ((Subobject.map f).obj P).arrow = P.arrow ≫ f := by
  let U : MonoOver B ⥤ C := MonoOver.forget B ⋙ Over.forget B
  let M : MonoOver A ⥤ MonoOver B := MonoOver.map f
  let e := Subobject.lowerCompRepresentativeIso M
  have hw := MonoOver.w (e.hom.app P)
  let θ := U.mapIso (e.app P)
  change θ.inv ≫ ((Subobject.lower M ⋙ Subobject.representative).obj P).arrow =
    ((Subobject.representative ⋙ M).obj P).arrow
  rw [hw.symm]
  have hθhom : θ.hom = (e.hom.app P).hom.left := rfl
  rw [← hθhom, ← Category.assoc, θ.inv_hom_id, Category.id_comp]

/-- Pushing two comparable subobjects forward along a monomorphism does not change the
quotient. -/
def cokernelMapIso {C : Type u} [Category C] [Abelian C]
    {A B : C} (f : A ⟶ B) [Mono f] (P Q : Subobject A) (hPQ : P ≤ Q) :
    cokernel (Subobject.ofLE ((Subobject.map f).obj P) ((Subobject.map f).obj Q)
      ((Subobject.map f).monotone hPQ)) ≅
      cokernel (Subobject.ofLE P Q hPQ) := by
  let v : (P : C) ⟶ (Q : C) := Subobject.ofLE P Q hPQ
  let v' : ((Subobject.map f).obj P : C) ⟶ ((Subobject.map f).obj Q : C) :=
    Subobject.ofLE ((Subobject.map f).obj P) ((Subobject.map f).obj Q)
      ((Subobject.map f).monotone hPQ)
  let p := subobjectMapObjIso f P
  let q := subobjectMapObjIso f Q
  have hcomm : v ≫ q.hom = p.hom ≫ v' := by
    apply (cancel_mono ((Subobject.map f).obj Q).arrow).mp
    calc
      (v ≫ q.hom) ≫ ((Subobject.map f).obj Q).arrow =
          v ≫ (q.hom ≫ ((Subobject.map f).obj Q).arrow) := by rw [Category.assoc]
      _ = v ≫ (Q.arrow ≫ f) := by rw [subobjectMapObjIso_hom_arrow]
      _ = (v ≫ Q.arrow) ≫ f := by rw [Category.assoc]
      _ = P.arrow ≫ f := by rw [Subobject.ofLE_arrow]
      _ = p.hom ≫ ((Subobject.map f).obj P).arrow :=
        (subobjectMapObjIso_hom_arrow f P).symm
      _ = (p.hom ≫ v') ≫ ((Subobject.map f).obj Q).arrow := by
        rw [Category.assoc, Subobject.ofLE_arrow]
  exact (cokernel.mapIso v v' p q hcomm).symm

/-! ### Concatenating two finite chains -/

/-- The concatenation of a chain of length `m` with a chain of length `n`, as a chain of length
`m + n`: the first `m + 1` terms are those of the first chain and the remaining `n` are the
terms of the second chain after its initial one. -/
def appendFinSequence {α : Type u} {m n : ℕ}
    (f : Fin (m + 1) → α) (g : Fin (n + 1) → α) : Fin (m + n + 1) → α :=
  fun j => Fin.append f (fun k => g k.succ)
    (Fin.cast (by omega : m + n + 1 = m + 1 + n) j)

/-- The source of a step inside the first block. -/
private theorem appendFinSequence_castAdd_castSucc {α : Type u} {m n : ℕ}
    (f : Fin (m + 1) → α) (g : Fin (n + 1) → α) (j : Fin m) :
    appendFinSequence f g (Fin.castAdd n j).castSucc = f j.castSucc := by
  unfold appendFinSequence
  have h : Fin.cast (by omega : m + n + 1 = m + 1 + n)
      (Fin.castAdd n j).castSucc = Fin.castAdd n j.castSucc := by
    apply Fin.ext
    simp [Fin.val_cast, Fin.val_castAdd]
  rw [h, Fin.append_left]

/-- The target of a step inside the first block. -/
private theorem appendFinSequence_castAdd_succ {α : Type u} {m n : ℕ}
    (f : Fin (m + 1) → α) (g : Fin (n + 1) → α) (j : Fin m) :
    appendFinSequence f g (Fin.castAdd n j).succ = f j.succ := by
  unfold appendFinSequence
  have h : Fin.cast (by omega : m + n + 1 = m + 1 + n)
      (Fin.castAdd n j).succ = Fin.castAdd n j.succ := by
    apply Fin.ext
    simp [Fin.val_cast, Fin.val_castAdd]
  rw [h, Fin.append_left]

/-- The source of the junction step is the last term of the first chain. -/
private theorem appendFinSequence_natAdd_zero_castSucc {α : Type u} {m n : ℕ}
    (f : Fin (m + 1) → α) (g : Fin (n + 1) → α) (hn : 0 < n) :
    appendFinSequence f g (Fin.natAdd m (⟨0, hn⟩ : Fin n)).castSucc = f (Fin.last m) := by
  unfold appendFinSequence
  have h : Fin.cast (by omega : m + n + 1 = m + 1 + n)
      (Fin.natAdd m (⟨0, hn⟩ : Fin n)).castSucc = Fin.castAdd n (Fin.last m) := by
    apply Fin.ext
    simp [Fin.val_castAdd]
  rw [h, Fin.append_left]

/-- The target of the junction step is the second term of the second chain. -/
private theorem appendFinSequence_natAdd_zero_succ {α : Type u} {m n : ℕ}
    (f : Fin (m + 1) → α) (g : Fin (n + 1) → α) (hn : 0 < n) :
    appendFinSequence f g (Fin.natAdd m (⟨0, hn⟩ : Fin n)).succ =
      g (⟨0, hn⟩ : Fin n).succ := by
  unfold appendFinSequence
  have h : Fin.cast (by omega : m + n + 1 = m + 1 + n)
      (Fin.natAdd m (⟨0, hn⟩ : Fin n)).succ =
        Fin.natAdd (m + 1) (⟨0, hn⟩ : Fin n) := by
    apply Fin.ext
    simp
  rw [h, Fin.append_right]

/-- The source of a step strictly inside the second block. -/
private theorem appendFinSequence_natAdd_castSucc {α : Type u} {m n : ℕ}
    (f : Fin (m + 1) → α) (g : Fin (n + 1) → α) (k : Fin n) (hk : 0 < k.val) :
    appendFinSequence f g (Fin.natAdd m k).castSucc = g k.castSucc := by
  unfold appendFinSequence
  let l : Fin n := ⟨k.val - 1, by omega⟩
  have hls : l.succ = k.castSucc := by
    apply Fin.ext
    simp [l]
    omega
  have h : Fin.cast (by omega : m + n + 1 = m + 1 + n)
      (Fin.natAdd m k.castSucc) = Fin.natAdd (m + 1) l := by
    apply Fin.ext
    simp [Fin.val_cast, Fin.val_natAdd, l]
    omega
  rw [← Fin.natAdd_castSucc, h, Fin.append_right, hls]

/-- The target of a step inside the second block. -/
private theorem appendFinSequence_natAdd_succ {α : Type u} {m n : ℕ}
    (f : Fin (m + 1) → α) (g : Fin (n + 1) → α) (k : Fin n) :
    appendFinSequence f g (Fin.natAdd m k).succ = g k.succ := by
  unfold appendFinSequence
  have h : Fin.cast (by omega : m + n + 1 = m + 1 + n)
      (Fin.natAdd m k).succ = Fin.natAdd (m + 1) k := by
    apply Fin.ext
    simp [Fin.val_cast, Fin.val_natAdd]
    omega
  rw [h, Fin.append_right]

/-- The concatenation of two monotone chains whose junction matches is monotone. -/
theorem appendFinSequence_monotone {α : Type u} [Preorder α] {m n : ℕ}
    (f : Fin (m + 1) → α) (g : Fin (n + 1) → α)
    (hf : ∀ j : Fin m, f j.castSucc ≤ f j.succ)
    (hg : ∀ j : Fin n, g j.castSucc ≤ g j.succ)
    (hjoin : f (Fin.last m) = g 0) (hn : 0 < n) :
    Monotone (appendFinSequence f g) := by
  apply Fin.monotone_iff_le_succ.mpr
  intro j
  refine Fin.addCases (fun k => ?_) (fun k => ?_) j
  · rw [appendFinSequence_castAdd_castSucc, appendFinSequence_castAdd_succ]
    exact hf k
  · by_cases hk : k.val = 0
    · obtain rfl : k = ⟨0, hn⟩ := Fin.ext hk
      rw [appendFinSequence_natAdd_zero_castSucc, appendFinSequence_natAdd_zero_succ]
      exact hjoin.trans_le (hg ⟨0, hn⟩)
    · rw [appendFinSequence_natAdd_castSucc _ _ _ (Nat.pos_of_ne_zero hk),
        appendFinSequence_natAdd_succ]
      exact hg k

/-- On the first block the concatenation is the first chain. -/
theorem appendFinSequence_left {α : Type u} {m n : ℕ}
    (f : Fin (m + 1) → α) (g : Fin (n + 1) → α) (j : Fin (m + 1)) :
    appendFinSequence f g
      (Fin.cast (by omega : m + 1 + n = m + n + 1) (Fin.castAdd n j)) = f j := by
  unfold appendFinSequence
  simp [Fin.append_left]

/-- On the second block the concatenation is the second chain, shifted past its initial
term. -/
theorem appendFinSequence_right {α : Type u} {m n : ℕ}
    (f : Fin (m + 1) → α) (g : Fin (n + 1) → α) (j : Fin n) :
    appendFinSequence f g
      (Fin.cast (by omega : m + 1 + n = m + n + 1) (Fin.natAdd (m + 1) j)) = g j.succ := by
  unfold appendFinSequence
  simp [Fin.append_right]

/-- The source of a step inside the first block. -/
theorem appendFinSequence_left_castSucc {α : Type u} {m n : ℕ}
    (f : Fin (m + 1) → α) (g : Fin (n + 1) → α) (j : Fin m) :
    appendFinSequence f g (Fin.castAdd n j).castSucc = f j.castSucc :=
  appendFinSequence_castAdd_castSucc f g j

/-- The target of a step inside the first block. -/
theorem appendFinSequence_left_succ {α : Type u} {m n : ℕ}
    (f : Fin (m + 1) → α) (g : Fin (n + 1) → α) (j : Fin m) :
    appendFinSequence f g (Fin.castAdd n j).succ = f j.succ :=
  appendFinSequence_castAdd_succ f g j

/-- The source of the junction step is the last term of the first chain. -/
theorem appendFinSequence_right_castSucc_zero {α : Type u} {m n : ℕ}
    (f : Fin (m + 1) → α) (g : Fin (n + 1) → α) (hn : 0 < n) :
    appendFinSequence f g (Fin.natAdd m (⟨0, hn⟩ : Fin n)).castSucc = f (Fin.last m) :=
  appendFinSequence_natAdd_zero_castSucc f g hn

/-- The target of the junction step is the second term of the second chain. -/
theorem appendFinSequence_right_succ_zero {α : Type u} {m n : ℕ}
    (f : Fin (m + 1) → α) (g : Fin (n + 1) → α) (hn : 0 < n) :
    appendFinSequence f g (Fin.natAdd m (⟨0, hn⟩ : Fin n)).succ =
      g (⟨0, hn⟩ : Fin n).succ :=
  appendFinSequence_natAdd_zero_succ f g hn

/-- The source of a step strictly inside the second block. -/
theorem appendFinSequence_right_castSucc {α : Type u} {m n : ℕ}
    (f : Fin (m + 1) → α) (g : Fin (n + 1) → α) (k : Fin n) (hk : 0 < k.val) :
    appendFinSequence f g (Fin.natAdd m k).castSucc = g k.castSucc :=
  appendFinSequence_natAdd_castSucc f g k hk

/-- The target of a step inside the second block. -/
theorem appendFinSequence_right_step {α : Type u} {m n : ℕ}
    (f : Fin (m + 1) → α) (g : Fin (n + 1) → α) (k : Fin n) :
    appendFinSequence f g (Fin.natAdd m k).succ = g k.succ :=
  appendFinSequence_natAdd_succ f g k

/-- A coproduct of `n + 1` copies of an object splits off its last summand. -/
def coproductFinSuccIso {C : Type u} [Category C]
    [HasFiniteCoproducts C] (P : C) (n : ℕ) :
    (∐ fun _ : Fin (n + 1) => P) ≅ ((∐ fun _ : Fin n => P) ⨿ P) := by
  let A := ∐ fun _ : Fin n => P
  let B := ∐ fun _ : Fin (n + 1) => P
  let f : B ⟶ A ⨿ P := Sigma.desc (fun j =>
    Fin.lastCases (coprod.inr : P ⟶ A ⨿ P)
      (fun k => Sigma.ι (fun _ : Fin n => P) k ≫ coprod.inl) j)
  let g : A ⨿ P ⟶ B := coprod.desc
    (Sigma.desc (fun k => Sigma.ι (fun _ : Fin (n + 1) => P) k.castSucc))
    (Sigma.ι (fun _ : Fin (n + 1) => P) (Fin.last n))
  refine { hom := f, inv := g, hom_inv_id := ?_, inv_hom_id := ?_ }
  · apply Sigma.hom_ext
    intro j
    induction j using Fin.lastCases with
    | last => simp [f, g, coprod.inr_desc]
    | cast k => simp [f, g, coprod.inl_desc]
  · apply coprod.hom_ext
    · apply Sigma.hom_ext
      intro k
      simp [f, g, coprod.inl_desc]
    · simp [f, g, coprod.inr_desc]
      rfl

end Stacks.AlgebraicGeometry.CoherentDevissage

end

end
