module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitPresheafIsColimit

/-!
# The sections of `colim_F 𝒪_X` over a quasi-compact open

Let `p` be a prime and let `X` be a scheme in characteristic `p`. The sheaf of rings
`colim_F 𝒪_X` of Stacks Tag 0EXB is a colimit formed in the category of sheaves of rings, so it
is the *sheafification* of the presheaf `V ↦ colim_j 𝒪_X(V)`
(`AlgebraicGeometry.toFrobeniusColimitRingSheaf`, which is locally bijective). This file shows
that no sheafification is needed over a quasi-compact open of a quasi-separated scheme: there

`(colim_F 𝒪_X)(U) = colim_j 𝒪_X(U)`,

spelled elementwise as the two statements that every section comes from a stage and that two
sections of `𝒪_X(U)` with the same image agree after enough Frobenius twists. These are the
inputs that turn a trivialisation of a finite locally free `colim_F 𝒪_X`-module into transition
matrices over `𝒪_X` at one finite stage.

## Main results

* `AlgebraicGeometry.exists_pow_eq_of_frobeniusStructureSheafι_app_eq`: **two sections of
  `𝒪_X(U)` with the same image in `(colim_F 𝒪_X)(U)`, for `U` quasi-compact, have equal
  `p ^ k`-th powers for some `k`.**
* `AlgebraicGeometry.exists_frobeniusStructureSheafι_app_eq`: **every section of
  `colim_F 𝒪_X` over a quasi-compact open of a quasi-separated scheme is the image of a section
  of `𝒪_X` at some finite stage.**

Both are preceded by their counterparts for the presheaf colimit
(`AlgebraicGeometry.exists_frobeniusRingPresheafι_app_eq` and
`AlgebraicGeometry.exists_pow_eq_of_frobeniusRingPresheafι_app_eq`), which hold over every open
and are the filtered-colimit-of-rings statements evaluated objectwise.

## Implementation notes

The 009F machinery of `StacksFrontier.Topology.Sheaves.Limits.FilteredColimitSections` is *not*
used: it is stated for the sheafification map of a diagram of `Type`-valued sheaves, and
matching it with `AlgebraicGeometry.toFrobeniusColimitRingSheaf` would mean identifying a
sheafification formed in `RingCat` with one formed in `Type`. Instead the two statements are
proved directly from the local injectivity and local surjectivity of that comparison, which are
already instances, together with quasi-compactness: a covering sieve on a quasi-compact open is
refined by a finite family of affine opens, the finitely many local stages and exponents are
replaced by their maximum, and the resulting family glues by the sheaf condition for `𝒪_X`. The
pairwise intersections of the members are quasi-compact because they are intersections of affine
opens in a quasi-separated space, which is where that hypothesis enters; the injectivity
statement needs no quasi-separatedness at all.

Sections are spelled `Γ(X, V)` and restriction `X.presheaf.map`, while the morphisms of the
colimit diagram live over `AlgebraicGeometry.Scheme.ringSheafOnOpens`, a re-typing of the same
sheaf of rings. The two spellings are definitionally equal but not syntactically so, so `rw` with
`map_pow` fires only after a `show` that names the `X.presheaf` spelling.

## References

* [Stacks Project, Tag 0EXB](https://stacks.math.columbia.edu/tag/0EXB)
* [Stacks Project, Tag 009F](https://stacks.math.columbia.edu/tag/009F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Frobenius TopologicalSpace

universe u

namespace AlgebraicGeometry

variable (X : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hX : IsInCharacteristic X p)

/-! ### The presheaf colimit -/

/-- The Frobenius endomorphism `AlgebraicGeometry.frobeniusRingSheafHom` raises a section over
`U` to its `p`-th power. -/
lemma frobeniusRingSheafHom_app_apply (U : X.Opens) (a : Γ(X, U)) :
    (frobeniusRingSheafHom X p hX).hom.app (op U) a = a ^ p :=
  frobeniusPresheafHom_app_apply X p hX U a

/-- The transition from stage `n` to stage `n + d` raises a section to its `p ^ d`-th power. -/
lemma frobeniusRingPresheafDiagram_map_app_apply (n d : ℕ) (V : X.Opens) (a : Γ(X, V)) :
    ((frobeniusRingPresheafDiagram X p hX).map
        (homOfLE (Nat.le_add_right n d) : n ⟶ n + d)).app (op V) a = a ^ p ^ d := by
  induction d with
  | zero =>
      rw [Subsingleton.elim (homOfLE (Nat.le_add_right n 0) : n ⟶ n + 0) (𝟙 n),
        CategoryTheory.Functor.map_id]
      change a = a ^ p ^ 0
      simp
  | succ d ih =>
      have hstep := frobeniusRingPresheafDiagram_map_succ X p hX (n + d)
      have h1 : ((frobeniusRingPresheafDiagram X p hX).map
            (homOfLE (Nat.le_add_right n (d + 1)) : n ⟶ n + (d + 1))).app (op V) a
          = (frobeniusRingSheafHom X p hX).hom.app (op V)
              (((frobeniusRingPresheafDiagram X p hX).map
                (homOfLE (Nat.le_add_right n d) : n ⟶ n + d)).app (op V) a) := by
        rw [Subsingleton.elim (homOfLE (Nat.le_add_right n (d + 1)) : n ⟶ n + (d + 1))
          ((homOfLE (Nat.le_add_right n d) : n ⟶ n + d) ≫
            homOfLE (Nat.le_add_right (n + d) 1)), CategoryTheory.Functor.map_comp, hstep]
        rfl
      rw [h1, ih, frobeniusRingSheafHom_app_apply, ← pow_mul, ← pow_succ]

/-- A section of the presheaf colimit over any open comes from a finite stage. -/
lemma exists_frobeniusRingPresheafι_app_eq (V : X.Opens)
    (s : ToType ((frobeniusRingPresheaf X p hX).obj (op V))) :
    ∃ (n : ℕ) (a : Γ(X, V)), (frobeniusRingPresheafι X p hX n).app (op V) a = s := by
  have h0 : PreservesFilteredColimitsOfSize.{0, 0} (forget RingCat.{u}) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  obtain ⟨n, a, ha⟩ := Concrete.isColimit_exists_rep
    (frobeniusRingPresheafDiagram X p hX ⋙
      (evaluation (Opens (X : TopCat))ᵒᵖ RingCat.{u}).obj (op V))
    (isColimitOfPreserves ((evaluation (Opens (X : TopCat))ᵒᵖ RingCat.{u}).obj (op V))
      (colimit.isColimit (frobeniusRingPresheafDiagram X p hX))) s
  exact ⟨n, a, ha⟩

/-- Two sections of `𝒪_X(V)` with the same image at a stage of the presheaf colimit agree after
enough Frobenius twists. -/
lemma exists_pow_eq_of_frobeniusRingPresheafι_app_eq (V : X.Opens) (n : ℕ) (a b : Γ(X, V))
    (h : (frobeniusRingPresheafι X p hX n).app (op V) a
       = (frobeniusRingPresheafι X p hX n).app (op V) b) :
    ∃ k : ℕ, a ^ p ^ k = b ^ p ^ k := by
  have h0 : PreservesFilteredColimitsOfSize.{0, 0} (forget RingCat.{u}) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  obtain ⟨k, f, g, hfg⟩ := Concrete.isColimit_exists_of_rep_eq
    (frobeniusRingPresheafDiagram X p hX ⋙
      (evaluation (Opens (X : TopCat))ᵒᵖ RingCat.{u}).obj (op V))
    (isColimitOfPreserves ((evaluation (Opens (X : TopCat))ᵒᵖ RingCat.{u}).obj (op V))
      (colimit.isColimit (frobeniusRingPresheafDiagram X p hX))) a b h
  obtain ⟨d, rfl⟩ : ∃ d, k = n + d := ⟨k - n, by have := leOfHom f; omega⟩
  refine ⟨d, ?_⟩
  rw [Subsingleton.elim f (homOfLE (Nat.le_add_right n d))] at hfg
  rw [Subsingleton.elim g (homOfLE (Nat.le_add_right n d))] at hfg
  rw [← frobeniusRingPresheafDiagram_map_app_apply X p hX n d V a,
    ← frobeniusRingPresheafDiagram_map_app_apply X p hX n d V b]
  exact hfg

/-- Passing from stage `n` to stage `n + d` of the presheaf colimit raises a section to its
`p ^ d`-th power. -/
lemma frobeniusRingPresheafι_pow_app (n d : ℕ) (V : X.Opens) (a : Γ(X, V)) :
    (frobeniusRingPresheafι X p hX (n + d)).app (op V) (a ^ p ^ d)
      = (frobeniusRingPresheafι X p hX n).app (op V) a := by
  have hw := colimit.w (frobeniusRingPresheafDiagram X p hX)
    (homOfLE (Nat.le_add_right n d) : n ⟶ n + d)
  have h := ConcreteCategory.congr_hom (congrArg (fun q ↦ NatTrans.app q (op V)) hw) a
  simp only [NatTrans.comp_app] at h
  rw [← frobeniusRingPresheafDiagram_map_app_apply X p hX n d V a]
  exact h

/-! ### The sheaf colimit -/

/-- The stage-`n` coprojection of sheaves of rings factors through the presheaf colimit. -/
lemma frobeniusStructureSheafι_hom_app (n : ℕ) (V : X.Opens) (a : Γ(X, V)) :
    (frobeniusStructureSheafι X p hX n).hom.app (op V) a
      = (toFrobeniusColimitRingSheaf X p hX).app (op V)
          ((frobeniusRingPresheafι X p hX n).app (op V) a) := by
  have h := frobeniusRingPresheafι_comp_toFrobeniusColimitRingSheaf X p hX n
  have h2 := ConcreteCategory.congr_hom (congrArg (fun q ↦ NatTrans.app q (op V)) h) a
  simp only [NatTrans.comp_app] at h2
  exact h2.symm

/-- Passing from stage `n` to stage `n + d` of `colim_F 𝒪_X` raises a section to its `p ^ d`-th
power. -/
lemma frobeniusStructureSheafι_pow_app (n d : ℕ) (V : X.Opens) (a : Γ(X, V)) :
    (frobeniusStructureSheafι X p hX (n + d)).hom.app (op V) (a ^ p ^ d)
      = (frobeniusStructureSheafι X p hX n).hom.app (op V) a := by
  rw [frobeniusStructureSheafι_hom_app, frobeniusStructureSheafι_hom_app,
    frobeniusRingPresheafι_pow_app]

/-- Restriction commutes with the stage-`n` coprojection. -/
lemma frobeniusStructureSheafι_hom_app_res (n : ℕ) {V V' : X.Opens} (h : V' ≤ V) (a : Γ(X, V)) :
    (frobeniusStructureSheafι X p hX n).hom.app (op V') (X.presheaf.map (homOfLE h).op a)
      = (frobeniusColimitRingSheaf X p hX).obj.map (homOfLE h).op
          ((frobeniusStructureSheafι X p hX n).hom.app (op V) a) :=
  NatTrans.naturality_apply (frobeniusStructureSheafι X p hX n).hom (homOfLE h).op a

omit [Fact p.Prime] in
/-- Raising an equality of `p ^ k`-th powers to a higher exponent. -/
private lemma pow_pow_eq_of_le {R : Type*} [Monoid R] {x y : R} {k K : ℕ} (hk : k ≤ K)
    (h : x ^ p ^ k = y ^ p ^ k) : x ^ p ^ K = y ^ p ^ K := by
  have hK : p ^ K = p ^ k * p ^ (K - k) := by
    rw [← pow_add]; congr 1; omega
  rw [hK, pow_mul, pow_mul, h]

/-- A quasi-compact open covered pointwise by opens `W i` is covered by finitely many of them. -/
private lemma exists_finset_le_iSup {U : X.Opens} (hU : IsCompact (U : Set X))
    (W : ↥(U : Set X) → X.Opens) (hW : ∀ i, (i : X) ∈ W i) :
    ∃ t : Finset (U : Set X), U ≤ ⨆ i : (t : Finset (U : Set X)), W i.1 := by
  obtain ⟨t, ht⟩ := hU.elim_finite_subcover (fun i ↦ (W i : Set X)) (fun i ↦ (W i).isOpen)
    (fun x hx ↦ Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hW ⟨x, hx⟩⟩)
  refine ⟨t, fun x hx ↦ ?_⟩
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (ht hx)
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i, hi⟩, hxi⟩

/-- **Two sections of `𝒪_X` over a quasi-compact open with the same image in `colim_F 𝒪_X` agree
after enough Frobenius twists.** -/
theorem exists_pow_eq_of_frobeniusStructureSheafι_app_eq (U : X.Opens)
    (hU : IsCompact (U : Set X)) (n : ℕ) (a b : Γ(X, U))
    (h : (frobeniusStructureSheafι X p hX n).hom.app (op U) a
       = (frobeniusStructureSheafι X p hX n).hom.app (op U) b) :
    ∃ k : ℕ, a ^ p ^ k = b ^ p ^ k := by
  classical
  rw [frobeniusStructureSheafι_hom_app, frobeniusStructureSheafι_hom_app] at h
  have hsieve : ∀ x ∈ U, ∃ (V : Opens (X : TopCat)) (g : V ⟶ U),
      (Presheaf.equalizerSieve ((frobeniusRingPresheafι X p hX n).app (op U) a)
        ((frobeniusRingPresheafι X p hX n).app (op U) b)).arrows g ∧ x ∈ V :=
    Presheaf.equalizerSieve_mem (Opens.grothendieckTopology (X : TopCat))
      (toFrobeniusColimitRingSheaf X p hX) ((frobeniusRingPresheafι X p hX n).app (op U) a)
      ((frobeniusRingPresheafι X p hX n).app (op U) b) h
  choose W f hWmem hWmem' using fun i : (U : Set X) ↦ hsieve i.1 i.2
  have hres : ∀ i : (U : Set X),
      (frobeniusRingPresheafι X p hX n).app (op (W i))
          (X.ringSheafOnOpens.obj.map (f i).op a)
        = (frobeniusRingPresheafι X p hX n).app (op (W i))
          (X.ringSheafOnOpens.obj.map (f i).op b) := by
    intro i
    exact (NatTrans.naturality_apply (frobeniusRingPresheafι X p hX n) (f i).op a).trans
      ((hWmem i).trans
        (NatTrans.naturality_apply (frobeniusRingPresheafι X p hX n) (f i).op b).symm)
  choose k hk using fun i ↦ exists_pow_eq_of_frobeniusRingPresheafι_app_eq X p hX (W i) n
    (X.ringSheafOnOpens.obj.map (f i).op a) (X.ringSheafOnOpens.obj.map (f i).op b) (hres i)
  obtain ⟨t, ht⟩ := exists_finset_le_iSup X hU W hWmem'
  refine ⟨t.sup k, ?_⟩
  refine TopCat.Sheaf.eq_of_locally_eq' (F := X.ringSheafOnOpens)
    (fun i : (t : Finset (U : Set X)) ↦ W i.1) U (fun i ↦ f i.1) ht _ _ ?_
  · intro i
    change X.presheaf.map (f i.1).op (a ^ p ^ t.sup k) = X.presheaf.map (f i.1).op (b ^ p ^ t.sup k)
    rw [map_pow, map_pow]
    exact pow_pow_eq_of_le p (Finset.le_sup i.2) (hk i.1)

/-- **A section of `colim_F 𝒪_X` over a quasi-compact open comes from a finite stage.** The
affine opens inside the given open cover it, finitely many suffice because it is quasi-compact,
and their pairwise intersections are quasi-compact because `X` is quasi-separated; so the local
preimages can be raised to one common stage, where they agree on the overlaps and glue. -/
theorem exists_frobeniusStructureSheafι_app_eq [QuasiSeparatedSpace X] (U : X.Opens)
    (hU : IsCompact (U : Set X))
    (s : ToType ((frobeniusColimitRingSheaf X p hX).obj.obj (op U))) :
    ∃ (n : ℕ) (a : Γ(X, U)), (frobeniusStructureSheafι X p hX n).hom.app (op U) a = s := by
  classical
  have himg : ∀ x ∈ U, ∃ (V : Opens (X : TopCat)) (g : V ⟶ U),
      (Presheaf.imageSieve (toFrobeniusColimitRingSheaf X p hX) s).arrows g ∧ x ∈ V :=
    Presheaf.imageSieve_mem (Opens.grothendieckTopology (X : TopCat))
      (toFrobeniusColimitRingSheaf X p hX) s
  have hrefine : ∀ i : (U : Set X), ∃ W : X.Opens, IsAffineOpen W ∧ (i : X) ∈ W ∧
      ∃ h : W ≤ U, ∃ t : ToType ((frobeniusRingPresheaf X p hX).obj (op W)),
        (toFrobeniusColimitRingSheaf X p hX).app (op W) t
          = (frobeniusColimitRingSheaf X p hX).obj.map (homOfLE h).op s := by
    intro i
    obtain ⟨V, g, hg, hiV⟩ := himg i.1 i.2
    obtain ⟨W, hWaff, hiW, hWV⟩ := exists_isAffineOpen_mem_and_subset hiV
    have hWU : W ≤ U := le_trans hWV g.le
    have hg' := (Presheaf.imageSieve (toFrobeniusColimitRingSheaf X p hX) s).downward_closed
      hg (homOfLE (show W ≤ V from hWV))
    rw [Subsingleton.elim (homOfLE (show W ≤ V from hWV) ≫ g) (homOfLE hWU)] at hg'
    exact ⟨W, hWaff, hiW, hWU, hg'⟩
  choose W hWaff hWmem hWU tt htt using hrefine
  choose nn aa haa using fun i ↦ exists_frobeniusRingPresheafι_app_eq X p hX (W i) (tt i)
  obtain ⟨tfin, hcover⟩ := exists_finset_le_iSup X hU W hWmem
  set n := tfin.sup nn with hn
  have hstage : ∀ i ∈ tfin, (frobeniusStructureSheafι X p hX n).hom.app (op (W i))
      (aa i ^ p ^ (n - nn i))
      = (frobeniusColimitRingSheaf X p hX).obj.map (homOfLE (hWU i)).op s := by
    intro i hi
    have hle : nn i ≤ n := Finset.le_sup hi
    have he : nn i + (n - nn i) = n := by omega
    rw [frobeniusStructureSheafι_hom_app,
      show (frobeniusRingPresheafι X p hX n).app (op (W i)) (aa i ^ p ^ (n - nn i))
        = (frobeniusRingPresheafι X p hX (nn i + (n - nn i))).app (op (W i))
          (aa i ^ p ^ (n - nn i)) by rw [he],
      frobeniusRingPresheafι_pow_app, haa i]
    exact htt i
  have hcompact : ∀ i j : (U : Set X), IsCompact ((W i ⊓ W j : X.Opens) : Set X) :=
    fun i j ↦ QuasiSeparatedSpace.inter_isCompact _ _ (W i).isOpen (hWaff i).isCompact
      (W j).isOpen (hWaff j).isCompact
  have hoverlap : ∀ i ∈ tfin, ∀ j ∈ tfin, ∃ k : ℕ,
      (X.presheaf.map (homOfLE (inf_le_left : W i ⊓ W j ≤ W i)).op
          (aa i ^ p ^ (n - nn i))) ^ p ^ k
        = (X.presheaf.map (homOfLE (inf_le_right : W i ⊓ W j ≤ W j)).op
          (aa j ^ p ^ (n - nn j))) ^ p ^ k := by
    intro i hi j hj
    refine exists_pow_eq_of_frobeniusStructureSheafι_app_eq X p hX (W i ⊓ W j)
      (hcompact i j) n _ _ ?_
    rw [frobeniusStructureSheafι_hom_app_res, frobeniusStructureSheafι_hom_app_res,
      hstage i hi, hstage j hj, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    rfl
  choose! kk hkk using hoverlap
  set K := tfin.sup (fun i ↦ tfin.sup (fun j ↦ kk i j)) with hK
  have hcompat : TopCat.Presheaf.IsCompatible X.ringSheafOnOpens.obj
      (fun i : (tfin : Finset (U : Set X)) ↦ W i.1)
      (fun i ↦ (aa i.1 ^ p ^ (n - nn i.1)) ^ p ^ K) := by
    intro i j
    have hle : kk i.1 j.1 ≤ K :=
      le_trans (Finset.le_sup (f := fun j ↦ kk i.1 j) j.2)
        (Finset.le_sup (f := fun i ↦ tfin.sup (fun j ↦ kk i j)) i.2)
    have h := pow_pow_eq_of_le p hle (hkk i.1 i.2 j.1 j.2)
    change X.presheaf.map (TopologicalSpace.Opens.infLELeft (W i.1) (W j.1)).op
          ((aa i.1 ^ p ^ (n - nn i.1)) ^ p ^ K)
        = X.presheaf.map (TopologicalSpace.Opens.infLERight (W i.1) (W j.1)).op
          ((aa j.1 ^ p ^ (n - nn j.1)) ^ p ^ K)
    rw [Subsingleton.elim (TopologicalSpace.Opens.infLELeft (W i.1) (W j.1))
        (homOfLE inf_le_left),
      Subsingleton.elim (TopologicalSpace.Opens.infLERight (W i.1) (W j.1))
        (homOfLE inf_le_right)]
    simp only [map_pow] at h ⊢
    exact h
  obtain ⟨b, hb, -⟩ := TopCat.Sheaf.existsUnique_gluing' (F := X.ringSheafOnOpens)
    (fun i : (tfin : Finset (U : Set X)) ↦ W i.1) U (fun i ↦ homOfLE (hWU i.1)) hcover
    (fun i ↦ (aa i.1 ^ p ^ (n - nn i.1)) ^ p ^ K) hcompat
  refine ⟨n + K, b, ?_⟩
  refine TopCat.Sheaf.eq_of_locally_eq' (F := frobeniusColimitRingSheaf X p hX)
    (fun i : (tfin : Finset (U : Set X)) ↦ W i.1) U (fun i ↦ homOfLE (hWU i.1)) hcover _ _ ?_
  intro i
  refine Eq.trans (frobeniusStructureSheafι_hom_app_res X p hX (n + K) (hWU i.1) b).symm ?_
  rw [show X.presheaf.map (homOfLE (hWU i.1)).op b = (aa i.1 ^ p ^ (n - nn i.1)) ^ p ^ K from
      hb i, frobeniusStructureSheafι_pow_app]
  exact hstage i.1 i.2

end AlgebraicGeometry

end
