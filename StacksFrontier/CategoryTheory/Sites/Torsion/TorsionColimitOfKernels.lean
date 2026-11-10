module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Abelian

/-!
# A locally torsion abelian sheaf is the colimit of its `n`-torsion subsheaves

Let `𝓕` be a sheaf of abelian groups on a site and let `M` be a multiplicatively closed set of
positive integers. Write `𝓕[n]` for the kernel of multiplication by `n` on `𝓕`. For `n ∣ m`
there is an inclusion `𝓕[n] ⟶ 𝓕[m]`. Suppose every local section of `𝓕` is, locally, killed
by some `n ∈ M`. Then

`𝓕 = colim_{n ∈ M} 𝓕[n]`,

the colimit being over `M` ordered by divisibility.

This is the first step of the proofs of Stacks 0F1H and 0F1I: *"Write
`𝓕 = colim 𝓕[n]` where the colimit is over the multiplicative system of integers invertible
in `K`."* There `M` is the set of positive integers prime to the exponential characteristic of
`K`. A sheaf whose stalks are torsion of orders invertible in `K` is exactly one satisfying the
hypothesis for that `M` (`Stacks.Torsion.IsPrimeToCharacteristicTorsion`).

## Main definitions

* `Stacks.Torsion.DvdIndex M` — `M` ordered by divisibility, a directed set.
* `Stacks.Torsion.torsionKernels 𝓕 M` — the system `n ↦ 𝓕[n] = ker(n : 𝓕 ⟶ 𝓕)`.
* `Stacks.Torsion.torsionKernelsCocone 𝓕 M` — the inclusions `𝓕[n] ⟶ 𝓕`.

## Main results

* `Stacks.Torsion.isColimitTorsionKernelsCocone` — **if every local section of `𝓕` is locally
  killed by an element of `M`, the inclusions `𝓕[n] ⟶ 𝓕` exhibit `𝓕` as the colimit of the
  `𝓕[n]`.**

## References

* [Stacks Project, Tag 0F1H](https://stacks.math.columbia.edu/tag/0F1H)
* [Stacks Project, Tag 0F1I](https://stacks.math.columbia.edu/tag/0F1I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace Stacks.Torsion

/-! ### The index set -/

/-- A multiplicatively closed set of natural numbers `M`, ordered by divisibility. -/
def DvdIndex (M : Submonoid ℕ) : Type := M

namespace DvdIndex

variable {M : Submonoid ℕ}

/-- The element of `M` underlying an index. -/
def toSubmonoid (n : DvdIndex M) : M := n

/-- The natural number underlying an index. -/
def val (n : DvdIndex M) : ℕ := (n.toSubmonoid : ℕ)

/-- The index attached to an element of `M`. -/
def mk (n : M) : DvdIndex M := n

/-- The natural number underlying `mk n` is `n`. -/
@[simp] theorem val_mk (n : M) : (mk n).val = n := rfl

/-- The divisibility preorder: `a ≤ b` when `a.val ∣ b.val`. -/
instance : Preorder (DvdIndex M) where
  le a b := a.val ∣ b.val
  le_refl _ := dvd_refl _
  le_trans _ _ _ := dvd_trans

/-- `a ≤ b` if and only if `a.val` divides `b.val`. -/
theorem le_iff {a b : DvdIndex M} : a ≤ b ↔ a.val ∣ b.val := Iff.rfl

/-- The index set is nonempty, as it contains `1`. -/
instance : Nonempty (DvdIndex M) := ⟨mk 1⟩

/-- `M` is directed under divisibility: `a` and `b` both divide `a * b`. -/
instance : IsDirected (DvdIndex M) (· ≤ ·) where
  directed a b :=
    ⟨mk (a.toSubmonoid * b.toSubmonoid), dvd_mul_right a.val b.val, dvd_mul_left b.val a.val⟩

end DvdIndex

/-! ### The system of `n`-torsion subsheaves -/

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝓕 : Sheaf J AddCommGrpCat.{w}) (M : Submonoid ℕ)

/-- The transition map `𝓕[n] ⟶ 𝓕[m]` for `n ∣ m`: the inclusion `𝓕[n] ⟶ 𝓕` lands in the
kernel of multiplication by `m`. -/
def torsionKernelsMap {n m : ℕ} (h : n ∣ m) : kernel (n • 𝟙 𝓕) ⟶ kernel (m • 𝟙 𝓕) :=
  kernel.lift _ (kernel.ι _) (by
    obtain ⟨k, rfl⟩ := h
    have hc := kernel.condition (n • 𝟙 𝓕)
    rw [Preadditive.comp_nsmul, Category.comp_id] at hc ⊢
    rw [mul_comm, mul_smul, hc, smul_zero])

/-- The transition map `𝓕[n] ⟶ 𝓕[m]` commutes with the inclusions into `𝓕`. -/
@[reassoc (attr := simp)]
theorem torsionKernelsMap_ι {n m : ℕ} (h : n ∣ m) :
    torsionKernelsMap 𝓕 h ≫ kernel.ι (m • 𝟙 𝓕) = kernel.ι (n • 𝟙 𝓕) :=
  kernel.lift_ι _ _ _

/-- **The system `n ↦ 𝓕[n]`** of kernels of multiplication by `n`, over `M` ordered by
divisibility. -/
def torsionKernels : DvdIndex M ⥤ Sheaf J AddCommGrpCat.{w} where
  obj n := kernel (n.val • 𝟙 𝓕)
  map h := torsionKernelsMap 𝓕 (DvdIndex.le_iff.1 (leOfHom h))
  map_id _ := (cancel_mono (kernel.ι _)).1 (by simp)
  map_comp _ _ := (cancel_mono (kernel.ι _)).1 (by simp)

/-- **The inclusions `𝓕[n] ⟶ 𝓕`**, a cocone over the system of `n`-torsion subsheaves. -/
@[simps]
def torsionKernelsCocone : Cocone (torsionKernels 𝓕 M) where
  pt := 𝓕
  ι :=
    { app n := kernel.ι (n.val • 𝟙 𝓕)
      naturality _ _ h := by simp [torsionKernels] }

/-- A section killed by `n` lies in the image of the inclusion `𝓕[n] ⟶ 𝓕`. -/
theorem exists_kernel_ι_app_eq {U : Cᵒᵖ} (n : ℕ) (y : 𝓕.obj.obj U) (hy : n • y = 0) :
    ∃ z : (kernel (n • 𝟙 𝓕)).obj.obj U, (kernel.ι (n • 𝟙 𝓕)).hom.app U z = y := by
  let G : Sheaf J AddCommGrpCat.{w} ⥤ AddCommGrpCat.{w} :=
    sheafToPresheaf J AddCommGrpCat.{w} ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj U
  have hy' : y ∈ (G.map (n • 𝟙 𝓕)).hom.ker := by
    rwa [Functor.map_nsmul, CategoryTheory.Functor.map_id]
  refine ⟨(PreservesKernel.iso G (n • 𝟙 𝓕)).inv
    ((AddCommGrpCat.kernelIsoKer (G.map (n • 𝟙 𝓕))).inv ⟨y, hy'⟩), ?_⟩
  change ((PreservesKernel.iso G (n • 𝟙 𝓕)).inv ≫ G.map (kernel.ι (n • 𝟙 𝓕))) _ = y
  rw [PreservesKernel.iso_inv_ι]
  change ((AddCommGrpCat.kernelIsoKer (G.map (n • 𝟙 𝓕))).inv ≫ kernel.ι _) ⟨y, hy'⟩ = y
  rw [AddCommGrpCat.kernelIsoKer_inv_comp_ι]
  rfl

attribute [local instance] IsFiltered.isConnected in
/-- **A locally `M`-torsion abelian sheaf is the colimit of its `n`-torsion subsheaves**: if every
local section of `𝓕` is, on a covering sieve, killed by an element of `M`, then the inclusions
`𝓕[n] ⟶ 𝓕` for `n ∈ M` exhibit `𝓕` as the colimit of the system of the `𝓕[n]` over `M` ordered
by divisibility. -/
theorem isColimitTorsionKernelsCocone
    [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [J.HasSheafCompose (forget AddCommGrpCat.{w})]
    [Balanced (Sheaf J AddCommGrpCat.{w})]
    [HasColimitsOfShape (DvdIndex M) (Sheaf J AddCommGrpCat.{w})]
    [(colim : (DvdIndex M ⥤ Sheaf J AddCommGrpCat.{w}) ⥤ _).PreservesMonomorphisms]
    (h𝓕 : ∀ (U : C) (x : 𝓕.obj.obj (op U)), ∃ R : Sieve U, R ∈ J U ∧
      ∀ (V : C) (f : V ⟶ U), R f → ∃ n ∈ M, n • 𝓕.obj.map f.op x = 0) :
    Nonempty (IsColimit (torsionKernelsCocone 𝓕 M)) := by
  let D := torsionKernels 𝓕 M
  let c := torsionKernelsCocone 𝓕 M
  have : ∀ n, Mono (c.ι.app n) := fun n => equalizer.ι_mono
  have := NatTrans.mono_of_mono_app c.ι
  have hmono : Mono (colimit.desc D c) :=
    colim.map_mono' c.ι (colimit.isColimit D) (isColimitConstCocone (DvdIndex M) 𝓕) _
      (fun j => (colimit.ι_desc c j).trans (Category.comp_id _).symm)
  have hepi : Epi (colimit.desc D c) := by
    rw [← Sheaf.isLocallySurjective_iff_epi']
    refine ⟨fun {U} x => ?_⟩
    obtain ⟨R, hR, hRx⟩ := h𝓕 U x
    refine J.superset_covering (fun V f hf => ?_) hR
    obtain ⟨n, hn, hx⟩ := hRx V f hf
    obtain ⟨z, hz⟩ := exists_kernel_ι_app_eq 𝓕 n _ hx
    exact ⟨(colimit.ι D (DvdIndex.mk ⟨n, hn⟩)).hom.app _ z,
      (congrArg (fun φ : D.obj (DvdIndex.mk ⟨n, hn⟩) ⟶ 𝓕 => φ.hom.app (op V) z)
        (colimit.ι_desc c (DvdIndex.mk ⟨n, hn⟩))).trans hz⟩
  have : IsIso ((colimit.isColimit D).desc c) := isIso_of_mono_of_epi (colimit.desc D c)
  exact ⟨IsColimit.ofPointIso (colimit.isColimit D)⟩

end Stacks.Torsion

end
