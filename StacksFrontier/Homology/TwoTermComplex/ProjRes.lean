module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.ConcreteCategory
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Data.Int.Star
public import Mathlib.Data.Int.SuccPred
public import Mathlib.Tactic.LinearCombination
public import StacksCore.LinearAlgebra.Matrix.CommSemiring

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Termwise-surjective projective resolutions of complexes

For a cochain complex `M` of `R`-modules with `M^i = 0` for `i > 0` and `M^0` projective, this
file constructs a termwise-surjective projective resolution `p : F → M`: a quasi-isomorphism
from a complex `F` of projective modules, strictly bounded above by `0`, with every `p^i`
surjective, `F^0 = M^0` and `p^0 = id`. The resolution is built as a tower of projective covers
and then assembled into a complex.

## Implementation notes

Forgetting the normalizations `F^0 = M^0` and `p^0 = id`, a `ProjRes M` is the data of a
`ProjectiveResolutionComplex M 0` together with termwise surjectivity, so its existence is the
case `a = 0`, `C = ModuleCat R` of
`ProjectiveResolutionLemma.exists_epiResolution_of_strictlyLE` in
`StacksFrontier.Algebra.Homology.Resolution.ProjectiveResolution`; the tower and its assembly below
are what produce the two normalizations.
-/

open CategoryTheory Limits ZeroObject

namespace TwoTermComplexExt

universe u v

variable {R : Type u} [Ring R]

/-- A termwise-surjective projective resolution of a complex `M`: a quasi-isomorphism
`p : F ⟶ M` from a complex `F` of projective modules strictly bounded above by `0`, with every
`p^i` an epimorphism, `F^0 = M^0` and `p^0` the identity. -/
structure ProjRes (M : CochainComplex (ModuleCat.{v} R) ℤ) where
  /-- The resolving complex. -/
  F : CochainComplex (ModuleCat.{v} R) ℤ
  /-- The resolution map. -/
  p : F ⟶ M
  /-- Every term of `F` is projective. -/
  proj : ∀ i, Projective (F.X i)
  /-- `F` is strictly bounded above by `0` (`F^i = 0` for `i > 0`). -/
  strictLE : F.IsStrictlyLE 0
  /-- `p` is a quasi-isomorphism. -/
  qis : QuasiIso p
  /-- `p` is termwise surjective (an epimorphism in each degree). -/
  epi : ∀ i, Epi (p.f i)
  /-- Normalization: `F^0 = M^0`. -/
  X0 : F.X 0 = M.X 0
  /-- Normalization: `p^0` is the identity (under `X0`). -/
  p0 : HomologicalComplex.Hom.f p 0 = eqToHom X0

/-- The resolving complex `F` of a `ProjRes` is K-projective. -/
theorem ProjRes.isKProjective {M : CochainComplex (ModuleCat.{v} R) ℤ} (P : ProjRes M) :
    P.F.IsKProjective := by
  have := P.strictLE
  have := P.proj
  exact CochainComplex.isKProjective_of_projective P.F 0

/-- The image of the resolution map `p` in the derived category is an isomorphism. -/
theorem ProjRes.isIso_Q_map_p [HasDerivedCategory (ModuleCat.{v} R)]
    {M : CochainComplex (ModuleCat.{v} R) ℤ} (P : ProjRes M) :
    IsIso (DerivedCategory.Q.map P.p) := by
  have := P.qis
  infer_instance


/-- One step of the resolution tower over the data `dF : Fn ⟶ Fnext`, `pF : Fn ⟶ Mn`,
`dM : Mnext ⟶ Mn`: a projective module `Fnew` with a differential to `Fn` and an augmentation
to `Mnext`, covering the pairs `(f, m)` with `dF f = 0` and `pF f = dM m`. -/
structure ProjResStepData (Fn Fnext Mn Mnext : ModuleCat.{v} R)
    (dF : Fn ⟶ Fnext) (pF : Fn ⟶ Mn) (dM : Mnext ⟶ Mn) where
  /-- The new module of the step. -/
  Fnew : ModuleCat.{v} R
  /-- `Fnew` is projective. -/
  proj : Projective Fnew
  /-- The differential out of `Fnew`. -/
  dFnew : Fnew ⟶ Fn
  /-- The augmentation of `Fnew`. -/
  pnew : Fnew ⟶ Mnext
  /-- The composite of the two differentials vanishes. -/
  dFnew_comp_dF : dFnew ≫ dF = 0
  /-- Chain identity `dFnew ≫ pF = pnew ≫ dM`. -/
  chain : dFnew ≫ pF = pnew ≫ dM
  /-- Every pair `(f, m)` with `dF f = 0` and `pF f = dM m` is of the form
  `(dFnew x, pnew x)`. -/
  cover : ∀ (f : Fn) (m : Mnext), dF f = 0 → pF f = dM m →
      ∃ x : Fnew, dFnew x = f ∧ pnew x = m

/-- Given morphisms `dF : Fn ⟶ Fnext`, `pF : Fn ⟶ Mn` and `dM : Mnext ⟶ Mn` of `R`-modules,
there is a resolution step over them. -/
theorem projRes_step [Small.{v} R] (Fn Fnext Mn Mnext : ModuleCat.{v} R)
    (dF : Fn ⟶ Fnext) (pF : Fn ⟶ Mn) (dM : Mnext ⟶ Mn) :
    Nonempty (ProjResStepData Fn Fnext Mn Mnext dF pF dM) := by
  set φ : (Fn ⊞ Mnext) ⟶ (Fnext ⊞ Mn) :=
    biprod.lift (biprod.fst ≫ dF) (biprod.fst ≫ pF - biprod.snd ≫ dM) with hφ
  set Z := kernel φ with hZ
  set Fnew := Projective.over Z with hFnew
  set q : Fnew ⟶ Z := Projective.π Z with hq
  have hker : kernel.ι φ ≫ φ = 0 := kernel.condition φ
  have hfst : kernel.ι φ ≫ biprod.fst ≫ dF = 0 := by
    have h1 : kernel.ι φ ≫ φ ≫ biprod.fst = 0 := by rw [reassoc_of% hker]; simp
    rw [hφ] at h1
    simpa only [biprod.lift_fst] using h1
  have hsnd : kernel.ι φ ≫ (biprod.fst ≫ pF - biprod.snd ≫ dM) = 0 := by
    have h2 : kernel.ι φ ≫ φ ≫ biprod.snd = 0 := by rw [reassoc_of% hker]; simp
    rw [hφ] at h2
    simpa only [biprod.lift_snd] using h2
  refine ⟨⟨Fnew, inferInstance, q ≫ kernel.ι φ ≫ biprod.fst,
    q ≫ kernel.ι φ ≫ biprod.snd, ?_, ?_, ?_⟩⟩
  · rw [Category.assoc, Category.assoc, hfst, comp_zero]
  · have hpq : kernel.ι φ ≫ biprod.fst ≫ pF = kernel.ι φ ≫ biprod.snd ≫ dM := by
      rw [← sub_eq_zero]
      simpa only [Preadditive.comp_sub] using hsnd
    rw [Category.assoc, Category.assoc, Category.assoc, Category.assoc, hpq]
  · intro f m hf hfm
    set w : (Fn ⊞ Mnext : ModuleCat.{v} R) :=
      (biprod.inl : Fn ⟶ Fn ⊞ Mnext) f + (biprod.inr : Mnext ⟶ Fn ⊞ Mnext) m with hw
    have hwfst : (biprod.fst : (Fn ⊞ Mnext : ModuleCat.{v} R) ⟶ Fn) w = f := by
      simp only [hw, map_add, ← ModuleCat.comp_apply, biprod.inl_fst, biprod.inr_fst]
      simp
    have hwsnd : (biprod.snd : (Fn ⊞ Mnext : ModuleCat.{v} R) ⟶ Mnext) w = m := by
      simp only [hw, map_add, ← ModuleCat.comp_apply, biprod.inl_snd, biprod.inr_snd]
      simp
    have hφw : φ w = 0 := by
      have decomp : ∀ (y : (Fnext ⊞ Mn : ModuleCat.{v} R)), y =
          (biprod.inl : Fnext ⟶ Fnext ⊞ Mn) ((biprod.fst : (Fnext ⊞ Mn : ModuleCat.{v} R) ⟶ Fnext)
              y)
          + (biprod.inr : Mn ⟶ Fnext ⊞ Mn) ((biprod.snd : (Fnext ⊞ Mn : ModuleCat.{v} R) ⟶ Mn)
              y) := by
        intro y
        symm
        rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← LinearMap.add_apply, ←
            ModuleCat.hom_add,
          biprod.total, ModuleCat.hom_id, LinearMap.id_apply]
      have hc1 : (biprod.fst : (Fnext ⊞ Mn : ModuleCat.{v} R) ⟶ Fnext) (φ w) = 0 := by
        rw [← ModuleCat.comp_apply, hφ, biprod.lift_fst, ModuleCat.comp_apply, hwfst, hf]
      have hc2 : (biprod.snd : (Fnext ⊞ Mn : ModuleCat.{v} R) ⟶ Mn) (φ w) = 0 := by
        rw [← ModuleCat.comp_apply, hφ, biprod.lift_snd]
        have hfm' : pF f - dM m = 0 := by rw [hfm, sub_self]
        rw [show (biprod.fst ≫ pF - biprod.snd ≫ dM : (Fn ⊞ Mnext : ModuleCat.{v} R) ⟶ Mn) w
            = (biprod.fst ≫ pF : (Fn ⊞ Mnext : ModuleCat.{v} R) ⟶ Mn) w
              - (biprod.snd ≫ dM) w from by simp]
        rw [ModuleCat.comp_apply, ModuleCat.comp_apply, hwfst, hwsnd, hfm']
      rw [decomp (φ w), hc1, hc2, map_zero, map_zero, add_zero]
    obtain ⟨z, hz⟩ : ∃ z : (kernel φ : ModuleCat.{v} R), (kernel.ι φ) z = w :=
      ⟨(ModuleCat.kernelIsoKer φ).inv ⟨w, hφw⟩, by
        rw [← ModuleCat.comp_apply, ModuleCat.kernelIsoKer_inv_kernel_ι]; rfl⟩
    have hqsurj : Function.Surjective (ConcreteCategory.hom q) :=
      (ModuleCat.epi_iff_surjective q).mp (Projective.π_epi Z)
    obtain ⟨x, hx⟩ := hqsurj z
    refine ⟨x, ?_, ?_⟩
    · rw [ModuleCat.comp_apply, ModuleCat.comp_apply, hx, hz, hwfst]
    · rw [ModuleCat.comp_apply, ModuleCat.comp_apply, hx, hz, hwsnd]

/-- Level-`n` datum of the downward projective resolution tower of `M`: the modules
`Gc = G n` and `Gn = G (n+1)` with augmentations to `M^{-n}` and `M^{-(n+1)}`, the differential
`dn : G (n+1) ⟶ G n`, a differential `dprev` out of `G n`, and the chain, complex and cover
identities relating them. -/
private structure TwrCell (M : CochainComplex (ModuleCat.{v} R) ℤ) (n : ℕ) where
  /-- The module at degree `-n` (= `G n`). -/
  Gc : ModuleCat.{v} R
  /-- `Gc` is projective. -/
  hGc : Projective Gc
  /-- Augmentation `pp n : G n ⟶ M^{-n}`. -/
  ppc : Gc ⟶ M.X (-(n : ℤ))
  /-- The module at degree `-(n+1)` (= `G (n+1)`). -/
  Gn : ModuleCat.{v} R
  /-- `Gn` is projective. -/
  hGn : Projective Gn
  /-- Augmentation `pp (n+1) : G (n+1) ⟶ M^{-(n+1)}`. -/
  ppn : Gn ⟶ M.X (-((n + 1 : ℕ) : ℤ))
  /-- The differential `dG n : G (n+1) ⟶ G n`. -/
  dn : Gn ⟶ Gc
  /-- The previous-level module (= `G (n-1)`; junk at `n = 0`). -/
  Gprev : ModuleCat.{v} R
  /-- The differential into the previous level (= `dG (n-1)`; `0` at `n = 0`). -/
  dprev : Gc ⟶ Gprev
  /-- Chain identity `dG n ≫ pp n = pp (n+1) ≫ d_M`. -/
  chain : dn ≫ ppc = ppn ≫ M.d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ))
  /-- Complex identity `dG n ≫ dG (n-1) = 0`. -/
  complex : dn ≫ dprev = 0
  /-- Cover/surjectivity onto relative cycles producing level `n+1`. -/
  cover : ∀ (f : Gc) (m : M.X (-((n + 1 : ℕ) : ℤ))),
      dprev f = 0 → ppc f = M.d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) m →
      ∃ x : Gn, dn x = f ∧ ppn x = m

/-- For a complex `M` with `M^0` projective there are projective modules `G n` with
`G 0 = M^0`, morphisms `pp n : G n ⟶ M^{-n}` with `pp 0` an isomorphism, and morphisms
`dG n : G (n+1) ⟶ G n` such that:
* `dG (n+1) ≫ dG n = 0`;
* `dG n ≫ pp n = pp (n+1) ≫ M.d (-(n+1)) (-n)`;
* for `f : G 0` and `m : M^{-1}` with `pp 0 f = d_M m` there is `x : G 1` with `dG 0 x = f`
  and `pp 1 x = m`;
* for `f : G (n+1)` and `m : M^{-n-2}` with `dG n f = 0` and `pp (n+1) f = d_M m` there is
  `x : G (n+2)` with `dG (n+1) x = f` and `pp (n+2) x = m`. -/
theorem projRes_tower [Small.{v} R] (M : CochainComplex (ModuleCat.{v} R) ℤ)
    (hM0 : Projective (M.X 0)) :
    ∃ (G : ℕ → ModuleCat.{v} R)
      (_ : ∀ n, Projective (G n))
      (pp : ∀ n, G n ⟶ M.X (-(n : ℤ)))
      (dG : ∀ n, G (n+1) ⟶ G n),
      G 0 = M.X 0 ∧
      (∀ n, dG (n+1) ≫ dG n = 0) ∧
      (∀ n, dG n ≫ pp n = pp (n+1) ≫ M.d (-((n : ℤ)+1)) (-(n : ℤ))) ∧
      (∀ (f : G 0) (m : M.X (-(1:ℤ))),
          pp 0 f = M.d (-1) 0 m → ∃ x : G 1, dG 0 x = f ∧ pp 1 x = m) ∧
      (∀ n (f : G (n+1)) (m : M.X (-((n : ℤ)+2))),
          dG n f = 0 → pp (n+1) f = M.d (-((n : ℤ)+2)) (-((n : ℤ)+1)) m →
          ∃ x : G (n+2), dG (n+1) x = f ∧ pp (n+2) x = m) ∧
      IsIso (pp 0) := by
  let step : ∀ n : ℕ, TwrCell M n → TwrCell M (n + 1) := fun n c =>
    let P := (projRes_step c.Gn c.Gc (M.X (-((n + 1 : ℕ) : ℤ))) (M.X (-((n + 1 + 1 : ℕ) : ℤ)))
        c.dn c.ppn (M.d (-((n + 1 + 1 : ℕ) : ℤ)) (-((n + 1 : ℕ) : ℤ)))).some
    { Gc := c.Gn, hGc := c.hGn, ppc := c.ppn,
      Gn := P.Fnew, hGn := P.proj, ppn := P.pnew, dn := P.dFnew,
      Gprev := c.Gc, dprev := c.dn,
      chain := P.chain, complex := P.dFnew_comp_dF, cover := P.cover }
  let base : TwrCell M 0 :=
    let P := (projRes_step (M.X 0) (M.X 0) (M.X (-((0 : ℕ) : ℤ))) (M.X (-((0 + 1 : ℕ) : ℤ)))
        (0 : M.X 0 ⟶ M.X 0) (eqToHom (by norm_num) : M.X 0 ⟶ M.X (-((0 : ℕ) : ℤ)))
        (M.d (-((0 + 1 : ℕ) : ℤ)) (-((0 : ℕ) : ℤ)))).some
    { Gc := M.X 0, hGc := hM0, ppc := eqToHom (by norm_num),
      Gn := P.Fnew, hGn := P.proj, ppn := P.pnew, dn := P.dFnew,
      Gprev := M.X 0, dprev := 0,
      chain := P.chain, complex := P.dFnew_comp_dF, cover := P.cover }
  let cell : ∀ n : ℕ, TwrCell M n := fun n => Nat.rec base step n
  refine ⟨fun n => (cell n).Gc, fun n => (cell n).hGc, fun n => (cell n).ppc,
    fun n => (cell n).dn, rfl, fun n => (cell (n + 1)).complex, fun n => (cell n).chain,
    ?_, ?_, ?_⟩
  · intro f m hf
    exact (cell 0).cover f m (by change (0 : (cell 0).Gc ⟶ (cell 0).Gprev) f = 0; simp) hf
  · intro n f m hf hfm
    exact (cell (n + 1)).cover f m hf hfm
  · show IsIso (eqToHom (show M.X 0 = M.X (-((0:ℕ):ℤ)) by norm_num))
    infer_instance

namespace ProjResAssemble

variable (M : CochainComplex (ModuleCat.{v} R) ℤ)
  (G : ℕ → ModuleCat.{v} R)
  (pp : ∀ n, G n ⟶ M.X (-(n : ℤ)))
  (dG : ∀ n, G (n + 1) ⟶ G n)

/-- The `ℤ`-indexed object family of `F`: `M.X 0` in degree `0`, `G (-i)` for `i < 0`,
the zero object for `i > 0`. -/
noncomputable def obj (i : ℤ) : ModuleCat.{v} R :=
  if 0 < i then 0 else if i = 0 then M.X 0 else G (-i).toNat

/-- The degree-`0` object of the assembled complex is `M.X 0`. -/
@[simp]
theorem obj_zero : obj M G 0 = M.X 0 := by simp [obj]
/-- In negative degree `i` the assembled complex has object `G (-i)`. -/
theorem obj_neg (i : ℤ) (h : i < 0) : obj M G i = G (-i).toNat := by
  have h1 : ¬ 0 < i := by omega
  have h2 : i ≠ 0 := by omega
  simp [obj, h1, h2]
/-- In positive degree the object of the assembled complex is zero. -/
theorem isZero_obj_pos (i : ℤ) (h : 0 < i) : IsZero (obj M G i) := by
  have : obj M G i = 0 := by simp [obj, h]
  rw [this]; exact isZero_zero _

/-- The differential `F.d i (i+1)`: zero into the zero objects (degree `≥ 0`), the
augmentation-glued `dG 0 ≫ pp 0` from degree `-1` into degree `0`, and the transported
`dG` for degree `≤ -2`. -/
noncomputable def d (i : ℤ) : obj M G i ⟶ obj M G (i+1) :=
  if h : 0 < i + 1 then 0
  else if h0 : i + 1 = 0 then
    eqToHom (by rw [obj_neg M G i (by omega)]; congr 1; omega : obj M G i = G 1) ≫
      dG 0 ≫ pp 0 ≫ eqToHom ((obj_zero M G).symm.trans (by rw [h0]) : M.X 0 = obj M G (i+1))
  else
    eqToHom (obj_neg M G i (by omega)) ≫
      eqToHom (show G (-i).toNat = G ((-(i+1)).toNat + 1) by congr 1; omega) ≫
      dG (-(i+1)).toNat ≫
      eqToHom (obj_neg M G (i+1) (by omega)).symm

/-- The augmentation components `p.f i : F.X i ⟶ M.X i`. -/
noncomputable def homApp (i : ℤ) : obj M G i ⟶ M.X i :=
  if h : 0 < i then 0
  else if h0 : i = 0 then
    eqToHom (by subst h0; exact obj_zero M G : obj M G i = M.X i)
  else
    eqToHom (obj_neg M G i (by omega)) ≫ pp (-i).toNat ≫
      eqToHom (show M.X (-(((-i).toNat : ℤ))) = M.X i by congr 1; omega)

/-- The degree-`0` augmentation component is the identification `obj M G 0 = M.X 0`. -/
@[simp]
theorem homApp_zero : homApp M G pp 0 = eqToHom (obj_zero M G) := by
  unfold homApp; rw [dite_eq_right (by norm_num : ¬ (0:ℤ) < 0), dite_eq_left rfl]

/-- Congruence for an `ℕ`-indexed family of morphisms at provably-equal indices. -/
theorem hom_congr {A B : ℕ → ModuleCat.{v} R} (f : ∀ n, A n ⟶ B n) (a b : ℕ) (h : a = b) :
    f a = eqToHom (by rw [h]) ≫ f b ≫ eqToHom (by rw [h]) := by subst h; simp

/-- Congruence for `M.d` at provably-equal indices. -/
theorem Md_congr (a b a' b' : ℤ) (ha : a = a') (hb : b = b') :
    M.d a b = eqToHom (by rw [ha]) ≫ M.d a' b' ≫ eqToHom (by rw [hb]) := by subst ha hb; simp

/-- If `a₁ = a₂ + 1`, then `dG a₁ ≫ eqToHom e ≫ dG a₂ = 0`. -/
theorem dG_comp_eqToHom_comp_dG_eq_zero (hcomplex : ∀ n, dG (n + 1) ≫ dG n = 0)
    (a₁ a₂ : ℕ) (ha : a₁ = a₂ + 1) (e : G a₁ = G (a₂ + 1)) : dG a₁ ≫ eqToHom e ≫ dG a₂ = 0 := by
  subst ha; simp only [eqToHom_refl, Category.id_comp]; exact hcomplex a₂

/-- Consecutive differentials of the assembled complex compose to zero. -/
theorem d_comp_d (hcomplex : ∀ n, dG (n + 1) ≫ dG n = 0) (i : ℤ) :
    d M G pp dG i ≫ d M G pp dG (i+1) = 0 := by
  unfold d
  by_cases h : 0 < i + 1
  · rw [dite_eq_left h]; simp
  · rw [dite_eq_right h]
    by_cases h0 : i + 1 = 0
    · rw [dite_eq_left h0]
      have hp : 0 < (i+1) + 1 := by omega
      rw [dite_eq_left hp]; simp
    · rw [dite_eq_right h0]
      by_cases h2 : 0 < (i+1) + 1
      · rw [dite_eq_left h2]; simp
      · rw [dite_eq_right h2]
        by_cases h02 : (i+1) + 1 = 0
        · rw [dite_eq_left h02]
          simp only [Category.assoc, eqToHom_trans_assoc]
          have e1 : (-(i+1)).toNat = 1 := by omega
          have key : dG (-(i+1)).toNat ≫
              eqToHom (show G (-(i+1)).toNat = G (0+1) by rw [e1]) ≫ dG 0 = 0 :=
            dG_comp_eqToHom_comp_dG_eq_zero G dG hcomplex _ _ (by omega) _
          slice_lhs 2 4 => rw [key]
          simp
        · rw [dite_eq_right h02]
          simp only [Category.assoc, eqToHom_trans_assoc]
          have key : dG (-(i+1)).toNat ≫
              eqToHom (show G (-(i+1)).toNat = G ((-(i+1+1)).toNat + 1) by congr 1; omega) ≫
              dG (-(i+1+1)).toNat = 0 :=
            dG_comp_eqToHom_comp_dG_eq_zero G dG hcomplex _ _ (by omega) _
          slice_lhs 2 4 => rw [key]
          simp

/-- The resolving complex `F`. -/
noncomputable def complex (hcomplex : ∀ n, dG (n + 1) ≫ dG n = 0) :
    CochainComplex (ModuleCat.{v} R) ℤ :=
  CochainComplex.of (obj M G) (d M G pp dG) (d_comp_d M G pp dG hcomplex)

/-- The differential of `complex` from degree `i` to `i + 1` is `d M G pp dG i`. -/
@[simp]
theorem complex_d (hcomplex : ∀ n, dG (n + 1) ≫ dG n = 0) (i : ℤ) :
    (complex M G pp dG hcomplex).d i (i+1) = d M G pp dG i :=
  CochainComplex.of_d (obj M G) (d M G pp dG) i

/-- The differential of `complex` from degree `i` to a degree `j` with `i + 1 = j`. -/
theorem complex_d_of_add_one_eq (hcomplex : ∀ n, dG (n + 1) ≫ dG n = 0) (i j : ℤ) (h : i + 1 = j) :
    (complex M G pp dG hcomplex).d i j
      = d M G pp dG i ≫ eqToHom (by rw [← h] : obj M G (i+1) = obj M G j) := by
  subst h; rw [complex_d]; simp

/-- The chain identity `dG n ≫ pp n = pp (n+1) ≫ M.d` remains valid after transporting all
four objects along equalities. -/
theorem comm_of_chain_of_eq (n : ℕ)
    (hc : dG n ≫ pp n = pp (n + 1) ≫ M.d (-((n : ℤ) + 1)) (-(n : ℤ)))
    (A A' B B' : ModuleCat.{v} R)
    (eA : A = G (n + 1)) (eA' : A' = G n)
    (eB : B = M.X (-((n : ℤ) + 1))) (eB' : B' = M.X (-(n : ℤ)))
    (md : B ⟶ B') (hmd : md = eqToHom eB ≫ M.d (-((n : ℤ) + 1)) (-(n : ℤ)) ≫ eqToHom eB'.symm)
    (ppA : A ⟶ B) (hppA : ppA = eqToHom eA ≫ pp (n + 1) ≫ eqToHom eB.symm)
    (ppA' : A' ⟶ B') (hppA' : ppA' = eqToHom eA' ≫ pp n ≫ eqToHom eB'.symm)
    (dd : A ⟶ A') (hdd : dd = eqToHom eA ≫ dG n ≫ eqToHom eA'.symm) :
    ppA ≫ md = dd ≫ ppA' := by
  subst eA eA' eB eB' hmd hppA hppA' hdd
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]; exact hc.symm

/-- The augmentation chain map `p : F ⟶ M`. -/
noncomputable def hom (hcomplex : ∀ n, dG (n + 1) ≫ dG n = 0)
    (hM_pos : ∀ i, 0 < i → IsZero (M.X i))
    (hchain : ∀ n, dG n ≫ pp n = pp (n + 1) ≫ M.d (-((n : ℤ) + 1)) (-(n : ℤ))) :
    (complex M G pp dG hcomplex) ⟶ M where
  f i := homApp M G pp i
  comm' i j hij := by
    simp only [ComplexShape.up_Rel] at hij
    subst hij
    change homApp M G pp i ≫ M.d i (i+1)
      = (complex M G pp dG hcomplex).d i (i+1) ≫ homApp M G pp (i+1)
    rw [complex_d]
    by_cases hipos : 0 < i
    · apply (isZero_obj_pos M G i hipos).eq_of_src
    · by_cases hi0 : i = 0
      · subst hi0
        apply (hM_pos 1 (by norm_num)).eq_of_tgt
      · by_cases hin1 : i = -1
        · subst hin1
          unfold homApp d
          rw [dite_eq_right (by norm_num : ¬ (0:ℤ) < -1),
              dite_eq_right (by norm_num : ¬ (-1:ℤ) = 0)]
          rw [dite_eq_right (by norm_num : ¬ (0:ℤ) < -1 + 1),
              dite_eq_left (by norm_num : (-1:ℤ) + 1 = 0)]
          rw [dite_eq_right (by norm_num : ¬ (0:ℤ) < -1 + 1),
              dite_eq_left (by norm_num : (-1:ℤ) + 1 = 0)]
          have hc := hchain 0
          rw [hom_congr pp ((-(-1:ℤ)).toNat) 1 (by norm_num)]
          rw [Md_congr M (-1) (-1+1) (-((0:ℤ)+1)) (-(0:ℤ)) (by norm_num) (by norm_num)]
          simp only [Category.assoc, eqToHom_refl,
            Category.id_comp, Category.comp_id]
          exact hc.symm
        · have hi2 : i ≤ -2 := by omega
          set n := (-(i+1)).toNat with hn
          have hi1 : i = -((n:ℤ)+1) := by omega
          have hi2' : i + 1 = -(n:ℤ) := by omega
          refine comm_of_chain_of_eq M G pp dG n (hchain n)
            (obj M G i) (obj M G (i+1)) (M.X i) (M.X (i+1))
            ((obj_neg M G i (by omega)).trans (by congr 1; try omega))
            ((obj_neg M G (i+1) (by omega)).trans (by congr 1; try omega))
            (by rw [hi1]) (by rw [hi2'])
            (M.d i (i+1)) ?_ (homApp M G pp i) ?_ (homApp M G pp (i+1)) ?_ (d M G pp dG i) ?_
          · rw [Md_congr M i (i+1) (-((n:ℤ)+1)) (-(n:ℤ)) hi1 hi2']
          · unfold homApp
            rw [dite_eq_right (by omega : ¬ 0 < i), dite_eq_right (by omega : i ≠ 0)]
            rw [hom_congr pp (-i).toNat (n+1) (by omega)]
            simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
          · unfold homApp
            rw [dite_eq_right (by omega : ¬ 0 < i + 1), dite_eq_right (by omega : i + 1 ≠ 0)]
          · unfold d
            rw [dite_eq_right (by omega : ¬ 0 < i + 1), dite_eq_right (by omega : ¬ i + 1 = 0)]
            rw [hom_congr dG (-(i+1)).toNat n (by omega)]
            simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]

end ProjResAssemble

/-- From the tower data there are a complex `F` of projective modules strictly bounded above
by `0` and a chain map `p : F ⟶ M` with `F^0 = M^0` and `p^0` the identity, together with
isomorphisms `eF n : F.X (-n) ≅ G n` under which `p.f (-n)` corresponds to `pp n` and the
differential `F.d (-(n+1)) (-n)` corresponds to `dG n`. -/
theorem projRes_assembleFP (M : CochainComplex (ModuleCat.{v} R) ℤ)
    (hM_pos : ∀ i, 0 < i → IsZero (M.X i))
    (G : ℕ → ModuleCat.{v} R)
    (hGproj : ∀ n, Projective (G n))
    (pp : ∀ n, G n ⟶ M.X (-(n : ℤ)))
    (dG : ∀ n, G (n + 1) ⟶ G n)
    (hG0 : G 0 = M.X 0)
    (hpp0 : IsIso (pp 0))
    (hcomplex : ∀ n, dG (n + 1) ≫ dG n = 0)
    (hchain : ∀ n, dG n ≫ pp n = pp (n + 1) ≫ M.d (-((n : ℤ) + 1)) (-(n : ℤ))) :
    ∃ (F : CochainComplex (ModuleCat.{v} R) ℤ) (p : F ⟶ M)
      (hX0 : F.X 0 = M.X 0),
      (∀ i, Projective (F.X i)) ∧
      F.IsStrictlyLE 0 ∧
      HomologicalComplex.Hom.f p 0 = eqToHom hX0 ∧
      (∃ (eF : ∀ n : ℕ, F.X (-(n : ℤ)) ≅ G n),
        (∀ n, (eF n).hom ≫ pp n = HomologicalComplex.Hom.f p (-(n : ℤ))) ∧
        (∀ n, (eF (n+1)).hom ≫ dG n ≫ (eF n).inv
            = F.d (-((n : ℤ)+1)) (-(n : ℤ)))) := by
  classical
  let F := ProjResAssemble.complex M G pp dG hcomplex
  let p := ProjResAssemble.hom M G pp dG hcomplex hM_pos hchain
  have hX0 : F.X 0 = M.X 0 := ProjResAssemble.obj_zero M G
  refine ⟨F, p, hX0, ?_, ?_, ?_, ?_⟩
  · intro i
    show Projective (ProjResAssemble.obj M G i)
    by_cases hi : 0 < i
    · exact (ProjResAssemble.isZero_obj_pos M G i hi).projective
    · by_cases hi0 : i = 0
      · subst hi0
        rw [ProjResAssemble.obj_zero, ← hG0]
        exact hGproj 0
      · rw [ProjResAssemble.obj_neg M G i (by omega)]
        exact hGproj _
  · rw [CochainComplex.isStrictlyLE_iff]
    exact ProjResAssemble.isZero_obj_pos M G
  · show ProjResAssemble.homApp M G pp 0 = eqToHom hX0
    rw [ProjResAssemble.homApp_zero]
  · let eF : ∀ n : ℕ, F.X (-(n : ℤ)) ≅ G n := fun n =>
      match n with
      | 0 => eqToIso (show F.X (-((0:ℕ):ℤ)) = M.X 0 by
                show ProjResAssemble.obj M G (-((0:ℕ):ℤ)) = M.X 0
                rw [show (-((0:ℕ):ℤ)) = 0 by norm_num]; exact ProjResAssemble.obj_zero M G) ≪≫
              (asIso (pp 0)).symm
      | (m+1) => eqToIso (show F.X (-(((m+1):ℕ):ℤ)) = G (m+1) by
                show ProjResAssemble.obj M G (-(((m+1):ℕ):ℤ)) = G (m+1)
                rw [ProjResAssemble.obj_neg M G _ (by omega)]; congr 1; try omega)
    refine ⟨eF, ?_, ?_⟩
    · intro n
      cases n with
      | zero =>
        show (eF 0).hom ≫ pp 0 = ProjResAssemble.homApp M G pp 0
        rw [ProjResAssemble.homApp_zero]
        show (_ ≫ _) ≫ pp 0 = _
        simp only [Iso.symm_hom, asIso_inv, eqToIso.hom, Category.assoc,
          IsIso.inv_hom_id, Category.comp_id]
      | succ m =>
        show (eF (m+1)).hom ≫ pp (m+1) = ProjResAssemble.homApp M G pp (-(((m+1):ℕ):ℤ))
        show (eqToIso _).hom ≫ pp (m+1) = _
        unfold ProjResAssemble.homApp
        rw [dite_eq_right (by omega : ¬ 0 < (-(((m+1):ℕ):ℤ))),
            dite_eq_right (by omega : (-(((m+1):ℕ):ℤ)) ≠ 0),
            ProjResAssemble.hom_congr pp ((-(-(((m+1):ℕ):ℤ))).toNat) (m+1) (by omega)]
        simp only [eqToIso.hom, eqToHom_refl,
          Category.id_comp, Category.comp_id]
    · intro n
      rw [ProjResAssemble.complex_d_of_add_one_eq M G pp dG hcomplex
        (-((n:ℤ)+1)) (-(n:ℤ)) (by ring)]
      cases n with
      | zero =>
        show (eF 1).hom ≫ dG 0 ≫ (eF 0).inv
          = ProjResAssemble.d M G pp dG (-(((0:ℕ):ℤ)+1)) ≫ _
        show (eqToIso _).hom ≫ dG 0 ≫ (_ ≪≫ _).inv = _
        unfold ProjResAssemble.d
        rw [dite_eq_right (by norm_num : ¬ (0:ℤ) < -(((0:ℕ):ℤ)+1) + 1),
            dite_eq_left (by norm_num : -(((0:ℕ):ℤ)+1) + 1 = 0)]
        simp only [Iso.trans_inv, Iso.symm_inv, asIso_hom, eqToIso.inv, eqToIso.hom,
           eqToHom_refl, Category.id_comp, Category.comp_id]
      | succ m =>
        show (eF (m+2)).hom ≫ dG (m+1) ≫ (eF (m+1)).inv
          = ProjResAssemble.d M G pp dG (-(((m+1:ℕ):ℤ)+1)) ≫ _
        show (eqToIso _).hom ≫ dG (m+1) ≫ (eqToIso _).inv = _
        unfold ProjResAssemble.d
        rw [dite_eq_right (by omega : ¬ (0:ℤ) < -(((m+1:ℕ):ℤ)+1) + 1),
            dite_eq_right (by omega : ¬ -(((m+1:ℕ):ℤ)+1) + 1 = 0),
            ProjResAssemble.hom_congr dG ((-(-(((m+1:ℕ):ℤ)+1)+1)).toNat) (m+1) (by omega)]
        simp only [eqToIso.hom, eqToIso.inv,
          eqToHom_refl, Category.id_comp, Category.comp_id]

/-- If `g0 : G (k+1)` maps to a cycle `z` of `M` in degree `-(k+1)`, then `z` lifts to a cycle
of the tower. -/
private theorem exists_cycle_lift_of_preimage (M : CochainComplex (ModuleCat.{v} R) ℤ)
    (G : ℕ → ModuleCat.{v} R)
    (pp : ∀ n, G n ⟶ M.X (-(n : ℤ)))
    (dG : ∀ n, G (n + 1) ⟶ G n)
    (hpp0 : IsIso (pp 0))
    (hcomplex : ∀ n, dG (n + 1) ≫ dG n = 0)
    (hchain : ∀ n, dG n ≫ pp n = pp (n + 1) ≫ M.d (-((n : ℤ) + 1)) (-(n : ℤ)))
    (hcover : ∀ n (f : G (n + 1)) (m : M.X (-((n : ℤ) + 2))),
        dG n f = 0 → pp (n + 1) f = M.d (-((n : ℤ) + 2)) (-((n : ℤ) + 1)) m →
        ∃ x : G (n + 2), dG (n + 1) x = f ∧ pp (n + 2) x = m)
    (k : ℕ) (z : M.X (-((k : ℤ) + 1))) (hz : M.d (-((k : ℤ) + 1)) (-(k : ℤ)) z = 0)
    (g0 : G (k + 1)) (hg0 : pp (k + 1) g0 = z) :
    ∃ g : G (k + 1), dG k g = 0 ∧ pp (k + 1) g = z := by
  have hker : pp k (dG k g0) = 0 := by
    rwa [← ConcreteCategory.comp_apply, hchain, ConcreteCategory.comp_apply, hg0]
  match k, z, hz, g0, hg0, hker with
  | 0, z, hz, g0, hg0, hker =>
    have hinj : Function.Injective (pp 0) :=
      (ModuleCat.mono_iff_injective _).mp inferInstance
    exact ⟨g0, hinj (by rw [hker, map_zero]), hg0⟩
  | (j+1), z, hz, g0, hg0, hker =>
    have hci : dG j (dG (j+1) g0) = 0 := by
      rw [← ModuleCat.comp_apply, hcomplex]
      rfl
    obtain ⟨y, hy1, hy2⟩ :=
      hcover j (dG (j+1) g0) 0 hci (by rw [hker, map_zero])
    refine ⟨g0 - y, ?_, ?_⟩
    · rw [map_sub, hy1, sub_self]
    · rw [map_sub, hg0, hy2, sub_zero]

/-- Every component `p.f i` of a chain map `p : F ⟶ M` identified with the tower data
through `eF` is an epimorphism. -/
theorem projRes_epi (M : CochainComplex (ModuleCat.{v} R) ℤ)
    (hM_pos : ∀ i, 0 < i → IsZero (M.X i))
    (G : ℕ → ModuleCat.{v} R)
    (pp : ∀ n, G n ⟶ M.X (-(n : ℤ)))
    (dG : ∀ n, G (n + 1) ⟶ G n)
    (hpp0 : IsIso (pp 0))
    (hcomplex : ∀ n, dG (n + 1) ≫ dG n = 0)
    (hchain : ∀ n, dG n ≫ pp n = pp (n + 1) ≫ M.d (-((n : ℤ) + 1)) (-(n : ℤ)))
    (hcover0 : ∀ (f : G 0) (m : M.X (-(1 : ℤ))),
        pp 0 f = M.d (-1) 0 m → ∃ x : G 1, dG 0 x = f ∧ pp 1 x = m)
    (hcover : ∀ n (f : G (n + 1)) (m : M.X (-((n : ℤ) + 2))),
        dG n f = 0 → pp (n + 1) f = M.d (-((n : ℤ) + 2)) (-((n : ℤ) + 1)) m →
        ∃ x : G (n + 2), dG (n + 1) x = f ∧ pp (n + 2) x = m)
    (F : CochainComplex (ModuleCat.{v} R) ℤ) (p : F ⟶ M)
    (hX0 : F.X 0 = M.X 0)
    (hp0 : HomologicalComplex.Hom.f p 0 = eqToHom hX0)
    (eF : ∀ n : ℕ, F.X (-(n : ℤ)) ≅ G n)
    (heF_p : ∀ n, (eF n).hom ≫ pp n = HomologicalComplex.Hom.f p (-(n : ℤ))) :
    ∀ i, Epi (HomologicalComplex.Hom.f p i) := by
  have hsurj : ∀ n, Function.Surjective (pp n) := by
    have hMdd : ∀ (i j k : ℤ) (x : M.X i), M.d j k (M.d i j x) = 0 := by
      intro i j k x
      rw [← ModuleCat.comp_apply, HomologicalComplex.d_comp_d]
      rfl
    intro n
    induction n with
    | zero =>
      exact (ModuleCat.epi_iff_surjective _).mp inferInstance
    | succ k ih =>
      intro m
      match k, ih, m with
      | 0, ih, m =>
        obtain ⟨f₀, hf₀⟩ := ih (M.d (-(((0:ℕ):ℤ)+1)) (-((0:ℕ):ℤ)) m)
        obtain ⟨x, -, hx2⟩ := hcover0 f₀ m hf₀
        exact ⟨x, hx2⟩
      | (j+1), ih, m =>
        obtain ⟨f₀, hf₀⟩ := ih (M.d (-(((j+1:ℕ):ℤ)+1)) (-((j+1:ℕ):ℤ)) m)
        obtain ⟨fc, hfc1, hfc2⟩ := exists_cycle_lift_of_preimage M G pp dG hpp0 hcomplex hchain
          hcover j _ (hMdd _ _ _ m) f₀ hf₀
        obtain ⟨x, -, hx2⟩ := hcover j fc m hfc1 hfc2
        exact ⟨x, hx2⟩
  intro i
  rcases lt_trichotomy i 0 with hi | hi | hi
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = -(n : ℤ) := ⟨(-i).toNat, by omega⟩
    rw [← heF_p n]
    have : Epi (pp n) := (ModuleCat.epi_iff_surjective _).mpr (hsurj n)
    exact epi_comp _ _
  · subst hi
    rw [hp0]
    infer_instance
  · exact ⟨fun g h _ => (hM_pos i hi).eq_of_src g h⟩

private lemma homologyπ_eq_zero_of_iCycles_eq_d (D : CochainComplex (ModuleCat.{v} R) ℤ)
    (i : ℤ) (kc : D.cycles i) (b : D.X (i - 1)) (hkc : D.iCycles i kc = D.d (i - 1) i b) :
    D.homologyπ i kc = 0 := by
  have h1 : D.iCycles i (D.toCycles (i - 1) i b) = D.d (i - 1) i b := by
    rw [← ConcreteCategory.comp_apply, D.toCycles_i]
  have hmono : Function.Injective (D.iCycles i) :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  rw [hmono (hkc.trans h1.symm), ← ConcreteCategory.comp_apply, D.toCycles_comp_homologyπ]
  rfl

private lemma exists_toCycles_eq_of_homologyπ_eq_zero (D : CochainComplex (ModuleCat.{v} R) ℤ)
    (i : ℤ) (lc : D.cycles i) (h : D.homologyπ i lc = 0) :
    ∃ b : D.X (i - 1), D.toCycles (i - 1) i b = lc := by
  let T : ShortComplex (ModuleCat.{v} R) :=
    { X₁ := D.X (i - 1), X₂ := D.cycles i, X₃ := D.homology i,
      f := D.toCycles (i - 1) i, g := D.homologyπ i,
      zero := D.toCycles_comp_homologyπ (i - 1) i }
  exact (ShortComplex.moduleCat_exact_iff T).mp
    (T.exact_of_g_is_cokernel (D.homologyIsCokernel (i - 1) i (by simp))) lc h

private lemma d_iCycles_apply_eq_zero (D : CochainComplex (ModuleCat.{v} R) ℤ) (i : ℤ)
    (kc : D.cycles i) : D.d i (i + 1) (D.iCycles i kc) = 0 := by
  rw [← ConcreteCategory.comp_apply, D.iCycles_d]
  rfl


/-- Abstract homology-iso criterion via element-level surjectivity/injectivity for
cochain complexes of modules. If, at degree `i`, every `L`-cycle is hit (modulo an
`L`-boundary) by a `K`-cycle (`hsurj`), and every `K`-cycle whose `φ`-image is an
`L`-boundary is itself a `K`-boundary (`hinj`), then `homologyMap φ i` is an
isomorphism. -/
private lemma homologyMap_isIso_of_surj_inj
    {K L : CochainComplex (ModuleCat.{v} R) ℤ} (φ : K ⟶ L) (i : ℤ)
    (hsurj : ∀ (z : L.X i), L.d i (i + 1) z = 0 →
        ∃ (c : K.X i), K.d i (i + 1) c = 0 ∧
          ∃ (m : L.X (i - 1)), HomologicalComplex.Hom.f φ i c - z = L.d (i - 1) i m)
    (hinj : ∀ (c : K.X i), K.d i (i + 1) c = 0 →
        (∃ m : L.X (i - 1), HomologicalComplex.Hom.f φ i c = L.d (i - 1) i m) →
        ∃ b : K.X (i - 1), c = K.d (i - 1) i b) :
    IsIso (HomologicalComplex.homologyMap φ i) := by
  have hnext : (ComplexShape.up ℤ).next i = i + 1 := by simp
  have hcm : ∀ (kc : K.cycles i),
      L.iCycles i (HomologicalComplex.cyclesMap φ i kc)
        = HomologicalComplex.Hom.f φ i (K.iCycles i kc) := fun kc => by
    rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i, ConcreteCategory.comp_apply]
  have hnat : ∀ (kc : K.cycles i),
      HomologicalComplex.homologyMap φ i (K.homologyπ i kc)
        = L.homologyπ i (HomologicalComplex.cyclesMap φ i kc) := fun kc => by
    rw [← ConcreteCategory.comp_apply, HomologicalComplex.homologyπ_naturality,
      ConcreteCategory.comp_apply]
  have hmono : Mono (HomologicalComplex.homologyMap φ i) := by
    rw [ModuleCat.mono_iff_injective, injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨kc, rfl⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ i)).mp inferInstance a
    rw [hnat kc] at ha
    obtain ⟨m, hm⟩ := exists_toCycles_eq_of_homologyπ_eq_zero L i _ ha
    have hL2 : L.iCycles i (HomologicalComplex.cyclesMap φ i kc) = L.d (i - 1) i m := by
      rw [← hm, ← ConcreteCategory.comp_apply, L.toCycles_i]
    obtain ⟨b, hb⟩ := hinj _ (d_iCycles_apply_eq_zero K i kc) ⟨m, by rw [← hcm kc, hL2]⟩
    exact homologyπ_eq_zero_of_iCycles_eq_d K i kc b hb
  have hepi : Epi (HomologicalComplex.homologyMap φ i) := by
    rw [ModuleCat.epi_iff_surjective]
    intro y
    obtain ⟨lc, rfl⟩ := (ModuleCat.epi_iff_surjective (L.homologyπ i)).mp inferInstance y
    obtain ⟨c, hc0, m, hm⟩ := hsurj _ (d_iCycles_apply_eq_zero L i lc)
    have hc0' : (ConcreteCategory.hom ((forget₂ (ModuleCat.{v} R) Ab).map (K.d i (i+1)))) c = 0 :=
      hc0
    let kc : K.cycles i := K.cyclesMk c (i+1) hnext hc0'
    have hkc : K.iCycles i kc = c := K.i_cyclesMk c (i+1) hnext hc0'
    refine ⟨K.homologyπ i kc, ?_⟩
    rw [hnat kc]
    have hdiff : L.iCycles i (HomologicalComplex.cyclesMap φ i kc - lc) = L.d (i-1) i m := by
      rwa [map_sub, hcm kc, hkc]
    have := homologyπ_eq_zero_of_iCycles_eq_d L i _ m hdiff
    rwa [map_sub, sub_eq_zero] at this
  exact isIso_of_mono_of_epi _

/-- In a tower resolving `M` by surjections, every cycle of `M` in degree `-(k+1)` lifts to a
cycle of the tower. -/
theorem exists_cycle_lift_of_surjective (M : CochainComplex (ModuleCat.{v} R) ℤ)
    (G : ℕ → ModuleCat.{v} R)
    (pp : ∀ n, G n ⟶ M.X (-(n : ℤ)))
    (dG : ∀ n, G (n + 1) ⟶ G n)
    (hpp0 : IsIso (pp 0))
    (hcomplex : ∀ n, dG (n + 1) ≫ dG n = 0)
    (hchain : ∀ n, dG n ≫ pp n = pp (n + 1) ≫ M.d (-((n : ℤ) + 1)) (-(n : ℤ)))
    (hcover : ∀ n (f : G (n + 1)) (m : M.X (-((n : ℤ) + 2))),
        dG n f = 0 → pp (n + 1) f = M.d (-((n : ℤ) + 2)) (-((n : ℤ) + 1)) m →
        ∃ x : G (n + 2), dG (n + 1) x = f ∧ pp (n + 2) x = m)
    (hsurjpp : ∀ n, Function.Surjective (pp n)) (k : ℕ) (z : M.X (-((k : ℤ) + 1)))
    (hz : M.d (-((k : ℤ) + 1)) (-(k : ℤ)) z = 0) :
    ∃ g : G (k + 1), dG k g = 0 ∧ pp (k + 1) g = z := by
  obtain ⟨g0, hg0⟩ := hsurjpp (k+1) z
  exact exists_cycle_lift_of_preimage M G pp dG hpp0 hcomplex hchain hcover k z hz g0 hg0

/-- A termwise epimorphic chain map `p : F ⟶ M` identified with the tower data through `eF`
is a quasi-isomorphism in each negative degree `i`. -/
theorem projRes_homologyIso_neg (M : CochainComplex (ModuleCat.{v} R) ℤ)
    (G : ℕ → ModuleCat.{v} R)
    (pp : ∀ n, G n ⟶ M.X (-(n : ℤ)))
    (dG : ∀ n, G (n + 1) ⟶ G n)
    (hpp0 : IsIso (pp 0))
    (hcomplex : ∀ n, dG (n + 1) ≫ dG n = 0)
    (hchain : ∀ n, dG n ≫ pp n = pp (n + 1) ≫ M.d (-((n : ℤ) + 1)) (-(n : ℤ)))
    (hcover : ∀ n (f : G (n + 1)) (m : M.X (-((n : ℤ) + 2))),
        dG n f = 0 → pp (n + 1) f = M.d (-((n : ℤ) + 2)) (-((n : ℤ) + 1)) m →
        ∃ x : G (n + 2), dG (n + 1) x = f ∧ pp (n + 2) x = m)
    (F : CochainComplex (ModuleCat.{v} R) ℤ) (p : F ⟶ M)
    (eF : ∀ n : ℕ, F.X (-(n : ℤ)) ≅ G n)
    (heF_p : ∀ n, (eF n).hom ≫ pp n = HomologicalComplex.Hom.f p (-(n : ℤ)))
    (heF_d : ∀ n, (eF (n+1)).hom ≫ dG n ≫ (eF n).inv
            = F.d (-((n : ℤ)+1)) (-(n : ℤ)))
    (hepi : ∀ i, Epi (HomologicalComplex.Hom.f p i))
    (i : ℤ) (hi : i < 0) :
    QuasiIsoAt p i := by
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hsurjpp : ∀ n, Function.Surjective (pp n) := fun n => by
    have : Epi ((eF n).hom ≫ pp n) := heF_p n ▸ hepi _
    exact (ModuleCat.epi_iff_surjective _).mp (epi_of_epi (eF n).hom (pp n))
  obtain ⟨k, hk⟩ : ∃ k : ℕ, i = -((k:ℤ)+1) :=
    ⟨(-i-1).toNat, by
      have : ((-i-1).toNat : ℤ) = -i-1 := Int.toNat_of_nonneg (by omega)
      omega⟩
  subst hk
  have e1 : (-((k:ℤ)+1)) + 1 = -(k:ℤ) := by ring
  have hpf : ∀ (c : F.X (-((k:ℤ)+1))),
      HomologicalComplex.Hom.f p (-((k:ℤ)+1)) c
        = pp (k+1) ((eF (k+1)).hom (c : F.X (-((k+1:ℕ):ℤ)))) := fun c =>
    (ConcreteCategory.congr_hom (heF_p (k+1)) (c : F.X (-((k+1:ℕ):ℤ)))).symm
  have hFd1 : ∀ (c : F.X (-((k:ℤ)+1))),
      F.d (-((k:ℤ)+1)) (-(k:ℤ)) c
        = (eF k).inv (dG k ((eF (k+1)).hom (c : F.X (-((k+1:ℕ):ℤ))))) := fun c =>
    (ConcreteCategory.congr_hom (heF_d k) (c : F.X (-((k+1:ℕ):ℤ)))).symm
  have hFd2 : ∀ (b : F.X (-((k:ℤ)+2))),
      F.d (-((k:ℤ)+2)) (-((k:ℤ)+1)) b
        = (eF (k+1)).inv (dG (k+1) ((eF (k+2)).hom (b : F.X (-((k+2:ℕ):ℤ))))) := fun b =>
    (ConcreteCategory.congr_hom (heF_d (k+1)) (b : F.X (-((k+2:ℕ):ℤ)))).symm
  have hhi : ∀ (g : G (k+1)), (eF (k+1)).hom ((eF (k+1)).inv g) = g := by simp
  have hih : ∀ (c : F.X (-((k+1:ℕ):ℤ))),
      (eF (k+1)).inv ((eF (k+1)).hom c) = c := by simp
  have hhi2 : ∀ (x : G (k+2)), (eF (k+2)).hom ((eF (k+2)).inv x) = x := by simp
  apply homologyMap_isIso_of_surj_inj p (-((k:ℤ)+1))
  · intro z hz
    rw [e1] at hz
    obtain ⟨g, hg, hppg⟩ :=
      exists_cycle_lift_of_surjective M G pp dG hpp0 hcomplex hchain hcover hsurjpp k z hz
    refine ⟨(eF (k+1)).inv g, ?_, 0, ?_⟩
    · rw [e1, hFd1, hhi, hg, map_zero]
    · rw [hpf, hhi, hppg, sub_self, map_zero]
  · intro c hc ⟨m, hmeq⟩
    rw [e1, hFd1] at hc
    have hg0 : dG k ((eF (k+1)).hom (c : F.X (-((k+1:ℕ):ℤ)))) = 0 := by
      simpa using congrArg (eF k).hom hc
    rw [hpf] at hmeq
    obtain ⟨x, hx, -⟩ := hcover k _ m hg0 hmeq
    refine ⟨(eF (k+2)).inv x, ?_⟩
    have hcomp : F.d (-((k:ℤ)+2)) (-((k:ℤ)+1)) ((eF (k+2)).inv x) = c := by
      rw [hFd2, hhi2, hx, hih]
    exact hcomp.symm

/-- A chain map `p : F ⟶ M` identified with the tower data through `eF`, with `F` strictly
bounded above by `0` and `p^0` the identity, is a quasi-isomorphism in degree `0`. -/
theorem projRes_homologyIso_zero (M : CochainComplex (ModuleCat.{v} R) ℤ)
    (G : ℕ → ModuleCat.{v} R)
    (pp : ∀ n, G n ⟶ M.X (-(n : ℤ)))
    (dG : ∀ n, G (n + 1) ⟶ G n)
    (hcover0 : ∀ (f : G 0) (m : M.X (-(1 : ℤ))),
        pp 0 f = M.d (-1) 0 m → ∃ x : G 1, dG 0 x = f ∧ pp 1 x = m)
    (F : CochainComplex (ModuleCat.{v} R) ℤ) (p : F ⟶ M)
    (hX0 : F.X 0 = M.X 0)
    (hstrict : F.IsStrictlyLE 0)
    (hp0 : HomologicalComplex.Hom.f p 0 = eqToHom hX0)
    (eF : ∀ n : ℕ, F.X (-(n : ℤ)) ≅ G n)
    (heF_p : ∀ n, (eF n).hom ≫ pp n = HomologicalComplex.Hom.f p (-(n : ℤ)))
    (heF_d : ∀ n, (eF (n+1)).hom ≫ dG n ≫ (eF n).inv
            = F.d (-((n : ℤ)+1)) (-(n : ℤ))) :
    QuasiIsoAt p 0 := by
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hFstrict : ∀ i, 0 < i → IsZero (F.X i) := by
    rwa [← CochainComplex.isStrictlyLE_iff]
  have hpiso : IsIso (HomologicalComplex.Hom.f p 0) := by rw [hp0]; infer_instance
  have hpinv : ∀ (z : M.X 0),
      HomologicalComplex.Hom.f p 0 ((inv (HomologicalComplex.Hom.f p 0)) z) = z := fun z =>
    ConcreteCategory.congr_hom (IsIso.inv_hom_id (HomologicalComplex.Hom.f p 0)) z
  have hpf0 : ∀ (c : F.X 0),
      HomologicalComplex.Hom.f p 0 c = pp 0 ((eF 0).hom (c : F.X (-((0:ℕ):ℤ)))) := fun c =>
    (ConcreteCategory.congr_hom (heF_p 0) (c : F.X (-((0:ℕ):ℤ)))).symm
  have hFd : ∀ (b : F.X (-(1:ℤ))),
      F.d (-(1:ℤ)) 0 b
        = (eF 0).inv (dG 0 ((eF 1).hom (b : F.X (-((1:ℕ):ℤ))))) := fun b =>
    (ConcreteCategory.congr_hom (heF_d 0) (b : F.X (-((1:ℕ):ℤ)))).symm
  have hih0 : ∀ (c : F.X (-((0:ℕ):ℤ))),
      (eF 0).inv ((eF 0).hom c) = c := by simp
  have hhi1 : ∀ (x : G 1), (eF 1).hom ((eF 1).inv x) = x := by simp
  have hFd01' : (F.d 0 (0+1) : F.X 0 ⟶ F.X (0+1)) = 0 :=
    (hFstrict (0+1) (by norm_num)).eq_zero_of_tgt _
  apply homologyMap_isIso_of_surj_inj p 0
  · intro z _hz
    refine ⟨(inv (HomologicalComplex.Hom.f p 0)) z, ?_, 0, ?_⟩
    · rw [hFd01']; rfl
    · rw [hpinv, sub_self, map_zero]
  · intro c _hc ⟨m, hmeq⟩
    rw [hpf0] at hmeq
    obtain ⟨x, hx, -⟩ :=
      hcover0 ((eF 0).hom (c : F.X (-((0:ℕ):ℤ)))) (m : M.X (-(1:ℤ))) hmeq
    refine ⟨(eF 1).inv x, ?_⟩
    have hcomp : F.d (-(1:ℤ)) 0 ((eF 1).inv x) = c := by
      rw [hFd, hhi1, hx, hih0]
    exact hcomp.symm

/-- A termwise epimorphic chain map `p : F ⟶ M` identified with the tower data through `eF`,
with `F` strictly bounded above by `0` and `p^0` the identity, is a quasi-isomorphism. -/
theorem projRes_qis (M : CochainComplex (ModuleCat.{v} R) ℤ)
    (hM_pos : ∀ i, 0 < i → IsZero (M.X i))
    (G : ℕ → ModuleCat.{v} R)
    (pp : ∀ n, G n ⟶ M.X (-(n : ℤ)))
    (dG : ∀ n, G (n + 1) ⟶ G n)
    (hpp0 : IsIso (pp 0))
    (hcomplex : ∀ n, dG (n + 1) ≫ dG n = 0)
    (hchain : ∀ n, dG n ≫ pp n = pp (n + 1) ≫ M.d (-((n : ℤ) + 1)) (-(n : ℤ)))
    (hcover0 : ∀ (f : G 0) (m : M.X (-(1 : ℤ))),
        pp 0 f = M.d (-1) 0 m → ∃ x : G 1, dG 0 x = f ∧ pp 1 x = m)
    (hcover : ∀ n (f : G (n + 1)) (m : M.X (-((n : ℤ) + 2))),
        dG n f = 0 → pp (n + 1) f = M.d (-((n : ℤ) + 2)) (-((n : ℤ) + 1)) m →
        ∃ x : G (n + 2), dG (n + 1) x = f ∧ pp (n + 2) x = m)
    (F : CochainComplex (ModuleCat.{v} R) ℤ) (p : F ⟶ M)
    (hX0 : F.X 0 = M.X 0)
    (hstrict : F.IsStrictlyLE 0)
    (hp0 : HomologicalComplex.Hom.f p 0 = eqToHom hX0)
    (eF : ∀ n : ℕ, F.X (-(n : ℤ)) ≅ G n)
    (heF_p : ∀ n, (eF n).hom ≫ pp n = HomologicalComplex.Hom.f p (-(n : ℤ)))
    (heF_d : ∀ n, (eF (n+1)).hom ≫ dG n ≫ (eF n).inv
            = F.d (-((n : ℤ)+1)) (-(n : ℤ)))
    (hepi : ∀ i, Epi (HomologicalComplex.Hom.f p i)) :
    QuasiIso p := by
  rw [quasiIso_iff]
  intro i
  have hMle : M.IsStrictlyLE 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro j hj
    exact hM_pos j (by omega)
  rcases lt_trichotomy i 0 with hi | hi | hi
  · exact projRes_homologyIso_neg M G pp dG hpp0 hcomplex hchain
      hcover F p eF heF_p heF_d hepi i hi
  · subst hi
    exact projRes_homologyIso_zero M G pp dG
      hcover0 F p hX0 hstrict hp0 eF heF_p heF_d
  · have hMex : M.ExactAt i := CochainComplex.exactAt_of_isLE M 0 i (by omega)
    rw [quasiIsoAt_iff_exactAt' p i hMex]
    exact CochainComplex.exactAt_of_isLE F 0 i (by omega)


/-- The tower data for `M` give a termwise-surjective projective resolution of `M`. -/
theorem projRes_of_tower (M : CochainComplex (ModuleCat.{v} R) ℤ)
    (hM_pos : ∀ i, 0 < i → IsZero (M.X i))
    (G : ℕ → ModuleCat.{v} R)
    (hGproj : ∀ n, Projective (G n))
    (pp : ∀ n, G n ⟶ M.X (-(n : ℤ)))
    (dG : ∀ n, G (n + 1) ⟶ G n)
    (hG0 : G 0 = M.X 0)
    (hpp0 : IsIso (pp 0))
    (hcomplex : ∀ n, dG (n + 1) ≫ dG n = 0)
    (hchain : ∀ n, dG n ≫ pp n = pp (n + 1) ≫ M.d (-((n : ℤ) + 1)) (-(n : ℤ)))
    (hcover0 : ∀ (f : G 0) (m : M.X (-(1 : ℤ))),
        pp 0 f = M.d (-1) 0 m → ∃ x : G 1, dG 0 x = f ∧ pp 1 x = m)
    (hcover : ∀ n (f : G (n + 1)) (m : M.X (-((n : ℤ) + 2))),
        dG n f = 0 → pp (n + 1) f = M.d (-((n : ℤ) + 2)) (-((n : ℤ) + 1)) m →
        ∃ x : G (n + 2), dG (n + 1) x = f ∧ pp (n + 2) x = m) :
    Nonempty (ProjRes M) := by
  obtain ⟨F, p, hX0, hproj, hstrict, hp0, eF, heF_p, heF_d⟩ :=
    projRes_assembleFP M hM_pos G hGproj pp dG hG0 hpp0 hcomplex hchain
  have hepi : ∀ i, Epi (HomologicalComplex.Hom.f p i) :=
    projRes_epi M hM_pos G pp dG hpp0 hcomplex hchain hcover0 hcover
      F p hX0 hp0 eF heF_p
  have hqis : QuasiIso p :=
    projRes_qis M hM_pos G pp dG hpp0 hcomplex hchain hcover0 hcover
      F p hX0 hstrict hp0 eF heF_p heF_d hepi
  exact ⟨{ F := F, p := p, proj := hproj, strictLE := hstrict,
           qis := hqis, epi := hepi, X0 := hX0, p0 := hp0 }⟩

/-- A cochain complex `M` of `R`-modules with `M^i = 0` for `i > 0` and `M^0` projective admits
a termwise-surjective projective resolution. -/
theorem exists_projRes [Small.{v} R] (M : CochainComplex (ModuleCat.{v} R) ℤ)
    (hM_pos : ∀ i, 0 < i → IsZero (M.X i)) (hM0 : Projective (M.X 0)) :
    Nonempty (ProjRes M) := by
  obtain ⟨G, hGproj, pp, dG, hG0, hcomplex, hchain, hcover0, hcover, hpp0⟩ := projRes_tower M hM0
  exact projRes_of_tower M hM_pos G hGproj pp dG hG0 hpp0 hcomplex hchain hcover0 hcover

end TwoTermComplexExt
