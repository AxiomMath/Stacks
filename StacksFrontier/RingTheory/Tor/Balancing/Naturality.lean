module

public import StacksFrontier.RingTheory.Tor.Balancing.Horseshoe

/-!
# Naturality in the first variable and the balancing of `Tor`

Naturality of `Tor_iso_Tor'.app` in `M`, proved by induction along the dimension shift,
and the resulting isomorphisms `Tor_iso_Tor'` and `tor_symm_canonically_iso`
(Stacks, Tag 00M3).

This is part of the split of `StacksFrontier.RingTheory.Tor.Balancing`.
-/

@[expose] public section

open LinearMap Submodule

universe u

-- `Tor_iso_Tor'.fromLeftDerivedZero_natTrans`, `Tor_iso_Tor'.zeroIso`,
-- `lesShift.phi_preservesZeroMorphisms` and `lesShift.comp_naturality` rewrite through
-- `ModuleCat`/`Functor.leftDerived` bundling, which only unfolds with relaxed defeq transparency.
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

variable (R : Type u) [CommRing R]

open HomologicalComplex HomologicalComplex.HomologySequence Limits CategoryTheory.ComposableArrows

/-! ### Naturality in the first variable

`Tor_iso_Tor'.naturality` is proved by induction on `i`, following the recursion of `app` through
`zeroIso`, `oneIso` and the dimension shift. A map `f : M ⟶ M'` is lifted to a morphism of the
two syzygy short exact sequences by `overMap` and `syzygyMap`, and the inductive step is the
naturality of `torShift` and `tor'Shift` in `M` along `syzygyMap f`. -/

/-- Lift of `f : M ⟶ M'` to chosen projective covers (`Projective.factorThru`). -/
noncomputable def Tor_iso_Tor'.overMap {M M' : ModuleCat.{u} R} (f : M ⟶ M') :
    Projective.over M ⟶ Projective.over M' :=
  Projective.factorThru (Projective.π M ≫ f) (Projective.π M')

/-- `overMap f` lifts `f` over the projective covers: `overMap f ≫ π' = π ≫ f`. -/
theorem Tor_iso_Tor'.overMap_comm {M M' : ModuleCat.{u} R} (f : M ⟶ M') :
    Tor_iso_Tor'.overMap R f ≫ Projective.π M' = Projective.π M ≫ f :=
  Projective.factorThru_comp _ _

/-- Lift of `f : M ⟶ M'` to syzygies. -/
noncomputable def Tor_iso_Tor'.syzygyMap {M M' : ModuleCat.{u} R} (f : M ⟶ M') :
    Tor_iso_Tor'.syzygy R M ⟶ Tor_iso_Tor'.syzygy R M' :=
  Limits.kernel.lift (Projective.π M')
    (Limits.kernel.ι (Projective.π M) ≫ Tor_iso_Tor'.overMap R f) (by
      rw [Category.assoc, Tor_iso_Tor'.overMap_comm, ← Category.assoc, Limits.kernel.condition,
        Limits.zero_comp])

/-- `syzygyMap f` is compatible with the syzygy inclusions:
`syzygyMap f ≫ kernel.ι = kernel.ι ≫ overMap f`. -/
theorem Tor_iso_Tor'.syzygyMap_comm {M M' : ModuleCat.{u} R} (f : M ⟶ M') :
    Tor_iso_Tor'.syzygyMap R f ≫ Limits.kernel.ι (Projective.π M')
      = Limits.kernel.ι (Projective.π M) ≫ Tor_iso_Tor'.overMap R f :=
  Limits.kernel.lift_ι _ _ _

/-- Naturality of `zeroIso` in `M`. -/
theorem Tor_iso_Tor'.naturality_zero {M M' : ModuleCat.{u} R} (f : M ⟶ M') :
    (Tor (ModuleCat.{u} R) 0).map f ≫ (Tor_iso_Tor'.zeroIso R M').hom
      = (Tor_iso_Tor'.zeroIso R M).hom ≫ (Tor' (ModuleCat.{u} R) 0).map f := by
  refine NatTrans.ext (funext fun N => ?_)
  simp only [NatTrans.comp_app, Tor_iso_Tor'.zeroIso, NatIso.ofComponents_hom_app,
    Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.leftDerivedZeroIsoSelf_hom,
    Tor_map, Tor'_map_app]
  have hL : (NatTrans.leftDerived ((MonoidalCategory.tensoringLeft (ModuleCat.{u} R)).map f) 0).app
      N
        ≫ (MonoidalCategory.tensorLeft M').fromLeftDerivedZero.app N
      = (MonoidalCategory.tensorLeft M).fromLeftDerivedZero.app N
        ≫ ((MonoidalCategory.tensoringLeft (ModuleCat.{u} R)).map f).app N := by
    have h := NatTrans.congr_app
      (Tor_iso_Tor'.fromLeftDerivedZero_natTrans
        ((MonoidalCategory.tensoringLeft (ModuleCat.{u} R)).map f)) N
    simpa only [NatTrans.comp_app] using h
  have hR := (MonoidalCategory.tensorRight N).leftDerivedZeroIsoSelf.inv.naturality f
  rw [reassoc_of% hL]
  exact congrArg _ hR

section tor'ShiftMAux
open CategoryTheory.Limits MonoidalCategory

/-- Chain lift of `syzygyMap f` over the chosen `K`-resolutions. -/
noncomputable def Tor_iso_Tor'.hsbA {M M' : ModuleCat.{u} R} (f : M ⟶ M') :
    (Tor_iso_Tor'.hsResK R M).complex ⟶ (Tor_iso_Tor'.hsResK R M').complex :=
  ProjectiveResolution.lift (Tor_iso_Tor'.syzygyMap R f)
    (Tor_iso_Tor'.hsResK R M) (Tor_iso_Tor'.hsResK R M')

/-- Chain lift of `f` over the chosen `M`-resolutions. -/
noncomputable def Tor_iso_Tor'.hsbC {M M' : ModuleCat.{u} R} (f : M ⟶ M') :
    (Tor_iso_Tor'.hsResM R M).complex ⟶ (Tor_iso_Tor'.hsResM R M').complex :=
  ProjectiveResolution.lift f (Tor_iso_Tor'.hsResM R M) (Tor_iso_Tor'.hsResM R M')

/-- `overMap f`, with codomain `(syzygySC M').X₂`. -/
noncomputable def Tor_iso_Tor'.hsbOverMap {M M' : ModuleCat.{u} R} (f : M ⟶ M') :
    (Tor_iso_Tor'.syzygySC R M).X₂ ⟶ (Tor_iso_Tor'.syzygySC R M').X₂ :=
  Tor_iso_Tor'.overMap R f

/-- The retyped lift still lifts `f`: `hsbOverMap f ≫ π' = π ≫ f`. -/
theorem Tor_iso_Tor'.hsbOverMap_comm {M M' : ModuleCat.{u} R} (f : M ⟶ M') :
    Tor_iso_Tor'.hsbOverMap R f ≫ Projective.π M' = Projective.π M ≫ f :=
  Tor_iso_Tor'.overMap_comm R f

/-- The right-hand side that the off-diagonal `t_{n+1}` must lift through `d^{K'}_{n+1}`.
`RHS_n = τ^M_n ≫ a_n + d^M_{n+1} ≫ t_n - c_{n+1} ≫ τ^{M'}_n : Q_{n+1}(M) → Q_n(K')`. -/
noncomputable def Tor_iso_Tor'.hsbRHS {M M' : ModuleCat.{u} R} (f : M ⟶ M') (n : ℕ)
    (t : (Tor_iso_Tor'.hsResM R M).complex.X n ⟶ (Tor_iso_Tor'.hsResK R M').complex.X n) :
    (Tor_iso_Tor'.hsResM R M).complex.X (n + 1) ⟶ (Tor_iso_Tor'.hsResK R M').complex.X n :=
  Tor_iso_Tor'.hsTau R M n ≫ (Tor_iso_Tor'.hsbA R f).f n
    + (Tor_iso_Tor'.hsResM R M).complex.d (n + 1) n ≫ t
    - (Tor_iso_Tor'.hsbC R f).f (n + 1) ≫ Tor_iso_Tor'.hsTau R M' n

/-- The augmentation-level discrepancy `δ = s₀^M ≫ overMap f - c₀ ≫ s₀^{M'} : Q_0(M) → P₀(M')`,
which lands in `K' = ker π_{M'}`. -/
theorem Tor_iso_Tor'.hsbS0disc_comp_π_eq_zero {M M' : ModuleCat.{u} R} (f : M ⟶ M') :
    (Tor_iso_Tor'.hsS0 R M ≫ Tor_iso_Tor'.hsbOverMap R f
        - (Tor_iso_Tor'.hsbC R f).f 0 ≫ Tor_iso_Tor'.hsS0 R M')
      ≫ Projective.π M' = 0 := by
  have hC0 : (Tor_iso_Tor'.hsbC R f).f 0 ≫ (Tor_iso_Tor'.hsResM R M').π.f 0
      = (Tor_iso_Tor'.hsResM R M).π.f 0 ≫ f :=
    ProjectiveResolution.lift_commutes_zero f _ _
  rw [Preadditive.sub_comp, Category.assoc, Tor_iso_Tor'.hsbOverMap_comm,
    ← Category.assoc, Tor_iso_Tor'.hsS0_spec, Category.assoc, Tor_iso_Tor'.hsS0_spec, hC0, sub_self]

/-- The base off-diagonal map `t_0 : Q_0(M) → Q_0(K')`, lifting the kernel factorization of `δ`
through the augmentation `ε^{K'} = (hsResK M').π.f 0`. -/
noncomputable def Tor_iso_Tor'.hsbT0 {M M' : ModuleCat.{u} R} (f : M ⟶ M') :
    (Tor_iso_Tor'.hsResM R M).complex.X 0 ⟶ (Tor_iso_Tor'.hsResK R M').complex.X 0 :=
  haveI : Epi ((Tor_iso_Tor'.hsResK R M').π.f 0) := by infer_instance
  Projective.factorThru
    (Limits.kernel.lift (Projective.π M')
      (Tor_iso_Tor'.hsS0 R M ≫ Tor_iso_Tor'.hsbOverMap R f
        - (Tor_iso_Tor'.hsbC R f).f 0 ≫ Tor_iso_Tor'.hsS0 R M')
      (Tor_iso_Tor'.hsbS0disc_comp_π_eq_zero R f))
    ((Tor_iso_Tor'.hsResK R M').π.f 0)

/-- `t_0 ≫ ε^{K'} ≫ ι' = s₀^M ≫ overMap f - c₀ ≫ s₀^{M'}`. -/
theorem Tor_iso_Tor'.hsbT0_spec {M M' : ModuleCat.{u} R} (f : M ⟶ M') :
    Tor_iso_Tor'.hsbT0 R f ≫ (Tor_iso_Tor'.hsResK R M').π.f 0
        ≫ Limits.kernel.ι (Projective.π M')
      = Tor_iso_Tor'.hsS0 R M ≫ Tor_iso_Tor'.hsbOverMap R f
        - (Tor_iso_Tor'.hsbC R f).f 0 ≫ Tor_iso_Tor'.hsS0 R M' := by
  have : Epi ((Tor_iso_Tor'.hsResK R M').π.f 0) := by infer_instance
  rw [Tor_iso_Tor'.hsbT0, ← Category.assoc, Projective.factorThru_comp, Limits.kernel.lift_ι]

/-- Base invariant: `RHS_0(t_0) ≫ ε^{K'} = 0`, so `t_1` can be lifted through `d^{K'}_1`. -/
theorem Tor_iso_Tor'.hsbVanish_zero {M M' : ModuleCat.{u} R} (f : M ⟶ M') :
    Tor_iso_Tor'.hsbRHS R f 0 (Tor_iso_Tor'.hsbT0 R f) ≫ (Tor_iso_Tor'.hsResK R M').π.f 0 = 0 := by
  have hA0 : (Tor_iso_Tor'.hsbA R f).f 0 ≫ (Tor_iso_Tor'.hsResK R M').π.f 0
      = (Tor_iso_Tor'.hsResK R M).π.f 0 ≫ Tor_iso_Tor'.syzygyMap R f :=
    ProjectiveResolution.lift_commutes_zero (Tor_iso_Tor'.syzygyMap R f) _ _
  have hC1 : (Tor_iso_Tor'.hsbC R f).f 1 ≫ (Tor_iso_Tor'.hsResM R M').complex.d 1 0
      = (Tor_iso_Tor'.hsResM R M).complex.d 1 0 ≫ (Tor_iso_Tor'.hsbC R f).f 0 :=
    (Tor_iso_Tor'.hsbC R f).comm 1 0
  simp only [Tor_iso_Tor'.hsbRHS, show Tor_iso_Tor'.hsTau R M 0 = Tor_iso_Tor'.hsTau0 R M from rfl,
    show Tor_iso_Tor'.hsTau R M' 0 = Tor_iso_Tor'.hsTau0 R M' from rfl]
  rw [← cancel_mono (Limits.kernel.ι (Projective.π M')), Limits.zero_comp]
  simp only [Preadditive.sub_comp, Preadditive.add_comp, Category.assoc]
  rw [show (Tor_iso_Tor'.hsbA R f).f 0 ≫ (Tor_iso_Tor'.hsResK R M').π.f 0
        ≫ Limits.kernel.ι (Projective.π M')
      = ((Tor_iso_Tor'.hsResK R M).π.f 0 ≫ Tor_iso_Tor'.syzygyMap R f)
        ≫ Limits.kernel.ι (Projective.π M') by rw [← Category.assoc, hA0]]
  rw [Category.assoc, Tor_iso_Tor'.syzygyMap_comm]
  rw [show Tor_iso_Tor'.hsTau0 R M ≫ (Tor_iso_Tor'.hsResK R M).π.f 0
          ≫ Limits.kernel.ι (Projective.π M) ≫ Tor_iso_Tor'.overMap R f
        = (Tor_iso_Tor'.hsTau0 R M ≫ (Tor_iso_Tor'.hsResK R M).π.f 0
            ≫ Limits.kernel.ι (Projective.π M)) ≫ Tor_iso_Tor'.overMap R f by
      simp only [Category.assoc]]
  rw [Tor_iso_Tor'.hsTau0_spec]
  rw [Tor_iso_Tor'.hsbT0_spec]
  simp only [Tor_iso_Tor'.hsbOverMap]
  rw [Tor_iso_Tor'.hsTau0_spec]
  simp only [ Preadditive.comp_sub, Preadditive.comp_neg, Preadditive.neg_comp,
    Category.assoc]
  rw [← Category.assoc ((Tor_iso_Tor'.hsbC R f).f 1) ((Tor_iso_Tor'.hsResM R M').complex.d 1 0)
    (Tor_iso_Tor'.hsS0 R M'), hC1]
  simp only [ Category.assoc]
  abel

/-- The general `hsTau` relation at index `n+1`:
`τ_{n+1} ≫ d^K_{n+1,n} = -(d^M_{n+2,n+1} ≫ τ_n)`. -/
theorem Tor_iso_Tor'.hsTau_rel (M : ModuleCat.{u} R) (n : ℕ) :
    Tor_iso_Tor'.hsTau R M (n + 1)
        ≫ (Tor_iso_Tor'.hsResK R M).complex.d (n + 1) n
      = -((Tor_iso_Tor'.hsResM R M).complex.d (n + 2) (n + 1)
          ≫ Tor_iso_Tor'.hsTau R M n) := by
  cases n with
  | zero =>
    change (Tor_iso_Tor'.hsTauAux R M 0).fst ≫ _ = _
    exact (Tor_iso_Tor'.hsSC0_exact R M).liftFromProjective_comp _ _
  | succ m =>
    change (Tor_iso_Tor'.hsTauAux R M (m + 1)).fst ≫ _ = _
    exact (Tor_iso_Tor'.hsSCsucc_exact R M m).liftFromProjective_comp _ _

/-- Recursion data for the off-diagonal `t`: at level `n` it carries `t_n`, `t_{n+1}`, and the
chain relation `t_{n+1} ≫ d^{K'}_{n+1,n} = RHS_n(t_n)`. -/
def Tor_iso_Tor'.hsbStep {M M' : ModuleCat.{u} R} (f : M ⟶ M') (n : ℕ) : Type _ :=
  Σ' (t : (Tor_iso_Tor'.hsResM R M).complex.X n ⟶ (Tor_iso_Tor'.hsResK R M').complex.X n)
     (t' : (Tor_iso_Tor'.hsResM R M).complex.X (n + 1)
        ⟶ (Tor_iso_Tor'.hsResK R M').complex.X (n + 1)),
    t' ≫ (Tor_iso_Tor'.hsResK R M').complex.d (n + 1) n = Tor_iso_Tor'.hsbRHS R f n t

/-- The maps `t_n`, `t_{n+1}` and the chain relation between them, constructed inductively. -/
noncomputable def Tor_iso_Tor'.hsbAux {M M' : ModuleCat.{u} R} (f : M ⟶ M') :
    (n : ℕ) → Tor_iso_Tor'.hsbStep R f n
  | 0 =>
    let t1 := (Tor_iso_Tor'.hsSC0_exact R M').liftFromProjective
      (Tor_iso_Tor'.hsbRHS R f 0 (Tor_iso_Tor'.hsbT0 R f)) (Tor_iso_Tor'.hsbVanish_zero R f)
    ⟨Tor_iso_Tor'.hsbT0 R f, t1,
      (Tor_iso_Tor'.hsSC0_exact R M').liftFromProjective_comp _ _⟩
  | (n + 1) =>
    let prev := Tor_iso_Tor'.hsbAux f n
    have hvan : Tor_iso_Tor'.hsbRHS R f (n + 1) prev.snd.fst
          ≫ (Tor_iso_Tor'.hsResK R M').complex.d (n + 1) n = 0 := by
      have hrel := prev.snd.snd
      have hAchain : (Tor_iso_Tor'.hsbA R f).f (n + 1)
            ≫ (Tor_iso_Tor'.hsResK R M').complex.d (n + 1) n
          = (Tor_iso_Tor'.hsResK R M).complex.d (n + 1) n ≫ (Tor_iso_Tor'.hsbA R f).f n :=
        (Tor_iso_Tor'.hsbA R f).comm (n + 1) n
      have hCchain : (Tor_iso_Tor'.hsbC R f).f (n + 2)
            ≫ (Tor_iso_Tor'.hsResM R M').complex.d (n + 2) (n + 1)
          = (Tor_iso_Tor'.hsResM R M).complex.d (n + 2) (n + 1) ≫ (Tor_iso_Tor'.hsbC R f).f (n + 1)
              :=
        (Tor_iso_Tor'.hsbC R f).comm (n + 2) (n + 1)
      have hτM := Tor_iso_Tor'.hsTau_rel R M n
      have hτMp := Tor_iso_Tor'.hsTau_rel R M' n
      have hdd : (Tor_iso_Tor'.hsResM R M).complex.d (n + 2) (n + 1)
            ≫ (Tor_iso_Tor'.hsResM R M).complex.d (n + 1) n = 0 :=
        HomologicalComplex.d_comp_d _ _ _ _
      simp only [Tor_iso_Tor'.hsbRHS, Preadditive.sub_comp, Preadditive.add_comp, Category.assoc]
      rw [hAchain, hrel, hτMp]
      simp only [Tor_iso_Tor'.hsbRHS]
      rw [show Tor_iso_Tor'.hsTau R M (n + 1)
              ≫ (Tor_iso_Tor'.hsResK R M).complex.d (n + 1) n ≫ (Tor_iso_Tor'.hsbA R f).f n
            = (Tor_iso_Tor'.hsTau R M (n + 1) ≫ (Tor_iso_Tor'.hsResK R M).complex.d (n + 1) n)
              ≫ (Tor_iso_Tor'.hsbA R f).f n by simp only [Category.assoc], hτM]
      simp only [Preadditive.comp_sub, Preadditive.comp_add, Preadditive.comp_neg,
        Preadditive.neg_comp, Category.assoc]
      rw [show (Tor_iso_Tor'.hsbC R f).f (n + 2)
              ≫ (Tor_iso_Tor'.hsResM R M').complex.d (n + 2) (n + 1) ≫ Tor_iso_Tor'.hsTau R M' n
            = ((Tor_iso_Tor'.hsbC R f).f (n + 2)
              ≫ (Tor_iso_Tor'.hsResM R M').complex.d (n + 2) (n + 1)) ≫ Tor_iso_Tor'.hsTau R M' n
            by simp only [Category.assoc], hCchain]
      rw [show (Tor_iso_Tor'.hsResM R M).complex.d (n + 2) (n + 1)
              ≫ (Tor_iso_Tor'.hsResM R M).complex.d (n + 1) n ≫ prev.fst
            = ((Tor_iso_Tor'.hsResM R M).complex.d (n + 2) (n + 1)
              ≫ (Tor_iso_Tor'.hsResM R M).complex.d (n + 1) n) ≫ prev.fst
            by simp only [Category.assoc],
        hdd]
      simp only [Category.assoc, Limits.zero_comp]
      abel
    let t2 := (Tor_iso_Tor'.hsSCsucc_exact R M' n).liftFromProjective
      (Tor_iso_Tor'.hsbRHS R f (n + 1) prev.snd.fst) hvan
    ⟨prev.snd.fst, t2, (Tor_iso_Tor'.hsSCsucc_exact R M' n).liftFromProjective_comp _ _⟩

/-- The off-diagonal sequence `t_n : Q_n(M) → Q_n(K')`. -/
noncomputable def Tor_iso_Tor'.hsbT {M M' : ModuleCat.{u} R} (f : M ⟶ M') : (n : ℕ) →
    ((Tor_iso_Tor'.hsResM R M).complex.X n ⟶ (Tor_iso_Tor'.hsResK R M').complex.X n)
  | 0 => Tor_iso_Tor'.hsbT0 R f
  | (n + 1) => (Tor_iso_Tor'.hsbAux R f n).snd.fst

/-- `(hsbAux n).1 = t_n`. -/
theorem Tor_iso_Tor'.hsbAux_fst {M M' : ModuleCat.{u} R} (f : M ⟶ M') (n : ℕ) :
    (Tor_iso_Tor'.hsbAux R f n).1 = Tor_iso_Tor'.hsbT R f n := by
  cases n with
  | zero => rfl
  | succ m => rfl

/-- The chain relation: `t_{n+1} ≫ d^{K'}_{n+1,n} = RHS_n(t_n)`. -/
theorem Tor_iso_Tor'.hsbT_rel {M M' : ModuleCat.{u} R} (f : M ⟶ M') (n : ℕ) :
    Tor_iso_Tor'.hsbT R f (n + 1) ≫ (Tor_iso_Tor'.hsResK R M').complex.d (n + 1) n
      = Tor_iso_Tor'.hsbRHS R f n (Tor_iso_Tor'.hsbT R f n) := by
  change (Tor_iso_Tor'.hsbAux R f n).snd.fst ≫ _ = _
  rw [← Tor_iso_Tor'.hsbAux_fst R f n]
  exact (Tor_iso_Tor'.hsbAux R f n).snd.snd

/-- The degreewise middle map `b_n = [[a_n, t_n],[0, c_n]] : Q_n(P₀(M)) → Q_n(P₀(M'))`. -/
noncomputable def Tor_iso_Tor'.hsbBf {M M' : ModuleCat.{u} R} (f : M ⟶ M') (n : ℕ) :
    Tor_iso_Tor'.hsXP R M n ⟶ Tor_iso_Tor'.hsXP R M' n :=
  Limits.biprod.desc
    (Limits.biprod.lift ((Tor_iso_Tor'.hsbA R f).f n) 0)
    (Limits.biprod.lift (Tor_iso_Tor'.hsbT R f n) ((Tor_iso_Tor'.hsbC R f).f n))

/-- The chain-map square for `b`: `b_{n+1} ≫ d^{P'}_n = d^P_n ≫ b_n`. -/
theorem Tor_iso_Tor'.hsbBf_comm {M M' : ModuleCat.{u} R} (f : M ⟶ M') (n : ℕ) :
    Tor_iso_Tor'.hsbBf R f (n + 1) ≫ Tor_iso_Tor'.hsDP R M' n
      = Tor_iso_Tor'.hsDP R M n ≫ Tor_iso_Tor'.hsbBf R f n := by
  have htr := Tor_iso_Tor'.hsbT_rel R f n
  simp only [Tor_iso_Tor'.hsbRHS] at htr
  apply Limits.biprod.hom_ext' <;> apply Limits.biprod.hom_ext <;>
    simp only [Tor_iso_Tor'.hsbBf, Tor_iso_Tor'.hsDP, Limits.biprod.inl_desc_assoc,
      Limits.biprod.inr_desc_assoc, Limits.biprod.lift_desc,
       Preadditive.add_comp,
      Category.assoc, Limits.biprod.lift_fst, Limits.biprod.lift_snd,
       Limits.zero_comp, Limits.comp_zero, add_zero, zero_add]
  · exact (Tor_iso_Tor'.hsbA R f).comm (n + 1) n
  · rw [htr]; abel
  · exact (Tor_iso_Tor'.hsbC R f).comm (n + 1) n

/-- The middle chain map `b : Q_•(P₀(M)) ⟶ Q_•(P₀(M'))`. -/
noncomputable def Tor_iso_Tor'.hsbB {M M' : ModuleCat.{u} R} (f : M ⟶ M') :
    Tor_iso_Tor'.hsQP R M ⟶ Tor_iso_Tor'.hsQP R M' where
  f n := Tor_iso_Tor'.hsbBf R f n
  comm' i j hij := by
    obtain rfl : i = j + 1 := hij.symm
    simp only [Tor_iso_Tor'.hsQP, ChainComplex.of_d]
    exact Tor_iso_Tor'.hsbBf_comm R f j

/-- `comm₁₂` for the horseshoe SC-morphism: `a ≫ α' = α ≫ b` (degreewise `inl`-compatibility). -/
theorem Tor_iso_Tor'.hsbB_comm_alpha {M M' : ModuleCat.{u} R} (f : M ⟶ M') :
    Tor_iso_Tor'.hsbA R f ≫ Tor_iso_Tor'.hsAlpha R M'
      = Tor_iso_Tor'.hsAlpha R M ≫ Tor_iso_Tor'.hsbB R f := by
  apply HomologicalComplex.hom_ext
  intro n
  simp only [Tor_iso_Tor'.hsAlpha, Tor_iso_Tor'.qiAlpha, Tor_iso_Tor'.hsbB,
    HomologicalComplex.comp_f, Tor_iso_Tor'.hsbBf]
  apply Limits.biprod.hom_ext <;>
    simp []

/-- `comm₂₃` for the horseshoe SC-morphism: `b ≫ β' = β ≫ c` (degreewise `snd`-compatibility). -/
theorem Tor_iso_Tor'.hsbB_comm_beta {M M' : ModuleCat.{u} R} (f : M ⟶ M') :
    Tor_iso_Tor'.hsbB R f ≫ Tor_iso_Tor'.hsBeta R M'
      = Tor_iso_Tor'.hsBeta R M ≫ Tor_iso_Tor'.hsbC R f := by
  apply HomologicalComplex.hom_ext
  intro n
  simp only [Tor_iso_Tor'.hsBeta, Tor_iso_Tor'.qiBeta, Tor_iso_Tor'.hsbB,
    HomologicalComplex.comp_f, Tor_iso_Tor'.hsbBf]
  apply Limits.biprod.hom_ext' <;>
    simp []

/-- The strict morphism of horseshoe short exact sequences of complexes `hsSCcplx M ⟶ hsSCcplx M'`
lifting `(syzygyMap f, overMap f, f)`. -/
noncomputable def Tor_iso_Tor'.hsbHom {M M' : ModuleCat.{u} R} (f : M ⟶ M') :
    Tor_iso_Tor'.hsSCcplx R M ⟶ Tor_iso_Tor'.hsSCcplx R M' where
  τ₁ := Tor_iso_Tor'.hsbA R f
  τ₂ := Tor_iso_Tor'.hsbB R f
  τ₃ := Tor_iso_Tor'.hsbC R f
  comm₁₂ := Tor_iso_Tor'.hsbB_comm_alpha R f
  comm₂₃ := Tor_iso_Tor'.hsbB_comm_beta R f

/-- The induced strict morphism of the tensored horseshoe short exact sequences of complexes
`oneIso_S M N ⟶ oneIso_S M' N`. -/
noncomputable def Tor_iso_Tor'.hsbΦ {M M' : ModuleCat.{u} R} (f : M ⟶ M') (N : ModuleCat.{u} R) :
    Tor_iso_Tor'.oneIso_S R M N ⟶ Tor_iso_Tor'.oneIso_S R M' N :=
  ((tensorRight N).mapHomologicalComplex (ComplexShape.down ℕ)).mapShortComplex.map
    (Tor_iso_Tor'.hsbHom R f)

/-- Transport of `(Tor'(j+2)).map f` through the `resM` `isoLeftDerivedObj`. -/
theorem Tor_iso_Tor'.hsbR_sq {M M' : ModuleCat.{u} R} (f : M ⟶ M') (N : ModuleCat.{u} R)
    (n : ℕ) :
    ((Tor' (ModuleCat.{u} R) n).map f).app N ≫
        ((Tor_iso_Tor'.horseshoe R M').resM.isoLeftDerivedObj (tensorRight N) n).hom
      = ((Tor_iso_Tor'.horseshoe R M).resM.isoLeftDerivedObj (tensorRight N) n).hom ≫
        HomologicalComplex.homologyMap (Tor_iso_Tor'.hsbΦ R f N).τ₃ n := by
  have h := ProjectiveResolution.isoLeftDerivedObj_hom_naturality f
    (Tor_iso_Tor'.horseshoe R M).resM (Tor_iso_Tor'.horseshoe R M').resM
    (Tor_iso_Tor'.hsbC R f) (ProjectiveResolution.lift_commutes_zero f _ _) (tensorRight N) n
  rw [show ((Tor' (ModuleCat.{u} R) n).map f).app N
        = ((tensorRight N).leftDerived n).map f from rfl]
  exact h

/-- Transport of `(Tor'(j+1)).map (syzygyMap f)` through the `resK` `isoLeftDerivedObj`. -/
theorem Tor_iso_Tor'.hsbL_sq {M M' : ModuleCat.{u} R} (f : M ⟶ M') (N : ModuleCat.{u} R)
    (n : ℕ) :
    ((Tor' (ModuleCat.{u} R) n).map (Tor_iso_Tor'.syzygyMap R f)).app N ≫
        ((Tor_iso_Tor'.horseshoe R M').resK.isoLeftDerivedObj (tensorRight N) n).hom
      = ((Tor_iso_Tor'.horseshoe R M).resK.isoLeftDerivedObj (tensorRight N) n).hom ≫
        HomologicalComplex.homologyMap (Tor_iso_Tor'.hsbΦ R f N).τ₁ n := by
  have h := ProjectiveResolution.isoLeftDerivedObj_hom_naturality (Tor_iso_Tor'.syzygyMap R f)
    (Tor_iso_Tor'.horseshoe R M).resK (Tor_iso_Tor'.horseshoe R M').resK
    (Tor_iso_Tor'.hsbA R f) (ProjectiveResolution.lift_commutes_zero (Tor_iso_Tor'.syzygyMap R f) _
        _)
    (tensorRight N) n
  rw [show ((Tor' (ModuleCat.{u} R) n).map (Tor_iso_Tor'.syzygyMap R f)).app N
        = ((tensorRight N).leftDerived n).map (Tor_iso_Tor'.syzygyMap R f) from rfl]
  exact h

end tor'ShiftMAux

section naturalityOneAux
open CategoryTheory.Limits MonoidalCategory CategoryTheory.ShortComplex

/-- The morphism of syzygy sequences `(syzygyMap f, overMap f, f) : syzygySC M ⟶ syzygySC M'`. -/
noncomputable def Tor_iso_Tor'.synSES {M M' : ModuleCat.{u} R} (f : M ⟶ M') :
    Tor_iso_Tor'.syzygySC R M ⟶ Tor_iso_Tor'.syzygySC R M' where
  τ₁ := Tor_iso_Tor'.syzygyMap R f
  τ₂ := Tor_iso_Tor'.overMap R f
  τ₃ := f
  comm₁₂ := Tor_iso_Tor'.syzygyMap_comm R f
  comm₂₃ := Tor_iso_Tor'.overMap_comm R f

/-- The induced map on the common kernel functor `oneKer M ⟶ oneKer M'`. -/
noncomputable def Tor_iso_Tor'.oneKerMap {M M' : ModuleCat.{u} R} (f : M ⟶ M') :
    Tor_iso_Tor'.oneKer R M ⟶ Tor_iso_Tor'.oneKer R M' :=
  Limits.kernel.map
    ((tensoringLeft (ModuleCat.{u} R)).map (Limits.kernel.ι (Projective.π M)))
    ((tensoringLeft (ModuleCat.{u} R)).map (Limits.kernel.ι (Projective.π M')))
    ((tensoringLeft (ModuleCat.{u} R)).map (Tor_iso_Tor'.syzygyMap R f))
    ((tensoringLeft (ModuleCat.{u} R)).map (Tor_iso_Tor'.overMap R f))
    (by rw [← Functor.map_comp, ← Functor.map_comp, Tor_iso_Tor'.syzygyMap_comm])

/-- `oneKerMap f` is compatible with the kernel inclusions, componentwise at `N`. -/
private theorem Tor_iso_Tor'.oneKerMap_app_ι_comp {M M' : ModuleCat.{u} R} (f : M ⟶ M')
    (N : ModuleCat.{u} R) :
    (Tor_iso_Tor'.oneKerMap R f).app N ≫ (Limits.kernel.ι (Tor_iso_Tor'.oneIsoTK_η R M')).app N
      = (Limits.kernel.ι (Tor_iso_Tor'.oneIsoTK_η R M)).app N ≫
        ((tensoringLeft (ModuleCat.{u} R)).map (Tor_iso_Tor'.syzygyMap R f)).app N := by
  have h : Tor_iso_Tor'.oneKerMap R f ≫ Limits.kernel.ι (Tor_iso_Tor'.oneIsoTK_η R M')
      = Limits.kernel.ι (Tor_iso_Tor'.oneIsoTK_η R M) ≫
        (tensoringLeft (ModuleCat.{u} R)).map (Tor_iso_Tor'.syzygyMap R f) := by
    dsimp only [Tor_iso_Tor'.oneKerMap, Tor_iso_Tor'.oneIsoTK_η]
    exact Limits.kernel.lift_ι _ _ _
  simpa only [NatTrans.comp_app] using congrArg (fun t => NatTrans.app t N) h

/-- The morphism of `Tor`-side tensored syzygy sequences of complexes induced by `f`. -/
noncomputable def Tor_iso_Tor'.oneIsoTK_Φ {M M' : ModuleCat.{u} R} (f : M ⟶ M')
    (N : ModuleCat.{u} R) :
    Tor_iso_Tor'.oneIsoTK_S R M N ⟶ Tor_iso_Tor'.oneIsoTK_S R M' N :=
  (lesShift.phi R (projectiveResolution N).complex).mapShortComplex.map
    (Tor_iso_Tor'.synSES R f)

/-- Transport of `(Tor 1).map f` through `e1`. -/
theorem Tor_iso_Tor'.oneIsoTK_R_sq {M M' : ModuleCat.{u} R} (f : M ⟶ M')
    (N : ModuleCat.{u} R) :
    ((Tor (ModuleCat.{u} R) 1).map f).app N ≫ (Tor_iso_Tor'.oneIsoTK_e1 R M' N).hom
      = (Tor_iso_Tor'.oneIsoTK_e1 R M N).hom ≫
        HomologicalComplex.homologyMap (Tor_iso_Tor'.oneIsoTK_Φ R f N).τ₃ 1 := by
  dsimp only [Tor_iso_Tor'.oneIsoTK_e1, Tor_iso_Tor'.oneIsoTK_Φ]
  rw [show ((Tor (ModuleCat.{u} R) 1).map f).app N
        = (NatTrans.leftDerived ((tensoringLeft (ModuleCat.{u} R)).map f) 1).app N from rfl]
  rw [ProjectiveResolution.leftDerived_app_eq ((tensoringLeft (ModuleCat.{u} R)).map f)
      (projectiveResolution N) 1]
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

/-- Naturality of `e3` in `M` on the `Tor` side. -/
theorem Tor_iso_Tor'.oneIsoTK_e3_sq {M M' : ModuleCat.{u} R} (f : M ⟶ M') (N : ModuleCat.{u} R) :
    HomologicalComplex.homologyMap (Tor_iso_Tor'.oneIsoTK_Φ R f N).τ₃ 1 ≫
        (Tor_iso_Tor'.oneIsoTK_e3 R M' N).hom
      = (Tor_iso_Tor'.oneIsoTK_e3 R M N).hom ≫
        Limits.kernel.map _ _ (HomologicalComplex.homologyMap (Tor_iso_Tor'.oneIsoTK_Φ R f N).τ₁ 0)
          (HomologicalComplex.homologyMap (Tor_iso_Tor'.oneIsoTK_Φ R f N).τ₂ 0)
          (by rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp];
              congr 1; exact (Tor_iso_Tor'.oneIsoTK_Φ R f N).comm₁₂.symm) := by
  apply (cancel_mono (Limits.kernel.ι
    (HomologicalComplex.homologyMap (Tor_iso_Tor'.oneIsoTK_S R M' N).f 0))).mp
  rw [Category.assoc, Category.assoc, Tor_iso_Tor'.oneIsoTK_e3_hom_ι,
    Limits.kernel.lift_ι, ← Category.assoc, Tor_iso_Tor'.oneIsoTK_e3_hom_ι]
  have hrel : (ComplexShape.down ℕ).Rel 1 0 := by simp [ComplexShape.down_Rel]
  exact (HomologicalComplex.HomologySequence.δ_naturality (Tor_iso_Tor'.oneIsoTK_Φ R f N)
    (Tor_iso_Tor'.oneIsoTK_S_shortExact R M N) (Tor_iso_Tor'.oneIsoTK_S_shortExact R M' N)
    1 0 hrel).symm

/-- Naturality of `p` in `M` on the `Tor` side. -/
theorem Tor_iso_Tor'.oneIsoTK_p_sq {M M' : ModuleCat.{u} R} (f : M ⟶ M') (N : ModuleCat.{u} R) :
    HomologicalComplex.homologyMap (Tor_iso_Tor'.oneIsoTK_Φ R f N).τ₁ 0 ≫
        (Tor_iso_Tor'.oneIsoTK_p R M' N).hom
      = (Tor_iso_Tor'.oneIsoTK_p R M N).hom ≫
        ((tensoringLeft (ModuleCat.{u} R)).map (Tor_iso_Tor'.syzygyMap R f)).app N := by
  have hτ₁ : HomologicalComplex.homologyMap (Tor_iso_Tor'.oneIsoTK_Φ R f N).τ₁ 0
      = ((projectiveResolution N).isoLeftDerivedObj
            (tensorLeft (Tor_iso_Tor'.syzygy R M)) 0).inv ≫
          (NatTrans.leftDerived ((tensoringLeft (ModuleCat.{u} R)).map (Tor_iso_Tor'.syzygyMap R
              f)) 0).app N ≫
          ((projectiveResolution N).isoLeftDerivedObj
            (tensorLeft (Tor_iso_Tor'.syzygy R M')) 0).hom := by
    have h := ProjectiveResolution.leftDerived_app_eq
      ((tensoringLeft (ModuleCat.{u} R)).map (Tor_iso_Tor'.syzygyMap R f))
      (projectiveResolution N) 0
    rw [show HomologicalComplex.homologyMap (Tor_iso_Tor'.oneIsoTK_Φ R f N).τ₁ 0
          = (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) 0).map
              ((NatTrans.mapHomologicalComplex
                ((tensoringLeft (ModuleCat.{u} R)).map (Tor_iso_Tor'.syzygyMap R f))
                (ComplexShape.down ℕ)).app (projectiveResolution N).complex) from rfl]
    conv_rhs => rw [h]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  dsimp only [Tor_iso_Tor'.oneIsoTK_p]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Functor.leftDerivedZeroIsoSelf_hom,
    Category.assoc]
  rw [hτ₁]
  rw [Category.assoc, Category.assoc, Iso.hom_inv_id_assoc]
  have hfd := Tor_iso_Tor'.fromLeftDerivedZero_natTrans
    ((tensoringLeft (ModuleCat.{u} R)).map (Tor_iso_Tor'.syzygyMap R f))
  have hfd' := congrArg (fun t => NatTrans.app t N) hfd
  simp only [NatTrans.comp_app] at hfd'
  rw [hfd']

/-- Naturality of `e4 ≫ e5` in `M` on the `Tor` side. -/
theorem Tor_iso_Tor'.oneIsoTK_e45_sq {M M' : ModuleCat.{u} R} (f : M ⟶ M') (N : ModuleCat.{u} R) :
    Limits.kernel.map _ _ (HomologicalComplex.homologyMap (Tor_iso_Tor'.oneIsoTK_Φ R f N).τ₁ 0)
          (HomologicalComplex.homologyMap (Tor_iso_Tor'.oneIsoTK_Φ R f N).τ₂ 0)
          (by rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp];
              congr 1; exact (Tor_iso_Tor'.oneIsoTK_Φ R f N).comm₁₂.symm) ≫
        ((Tor_iso_Tor'.oneIsoTK_e4 R M' N).hom ≫ (Tor_iso_Tor'.oneIsoTK_e5 R M' N).hom)
      = ((Tor_iso_Tor'.oneIsoTK_e4 R M N).hom ≫ (Tor_iso_Tor'.oneIsoTK_e5 R M N).hom) ≫
        (Tor_iso_Tor'.oneKerMap R f).app N := by
  apply (cancel_mono ((Limits.kernel.ι (Tor_iso_Tor'.oneIsoTK_η R M')).app N)).mp
  simp only [Category.assoc]
  rw [Tor_iso_Tor'.oneKerMap_app_ι_comp]
  simp only [Tor_iso_Tor'.oneIsoTK_e5_hom_ι_assoc, Tor_iso_Tor'.oneIsoTK_e5_hom_ι,
    Tor_iso_Tor'.oneIsoTK_e4_hom_ι_assoc, Tor_iso_Tor'.oneIsoTK_e4_hom_ι]
  rw [← Category.assoc, Limits.kernel.lift_ι]
  simp only [Category.assoc]
  rw [Tor_iso_Tor'.oneIsoTK_p_sq R f N]

/-- Naturality in `M` of the `Tor`-side kernel description, at each `N`. -/
theorem Tor_iso_Tor'.oneIsoTK_comp_sq {M M' : ModuleCat.{u} R} (f : M ⟶ M') (N : ModuleCat.{u} R) :
    ((Tor (ModuleCat.{u} R) 1).map f).app N ≫ (Tor_iso_Tor'.oneIsoTK_comp R M' N).hom
      = (Tor_iso_Tor'.oneIsoTK_comp R M N).hom ≫ (Tor_iso_Tor'.oneKerMap R f).app N := by
  simp only [Tor_iso_Tor'.oneIsoTK_comp, Iso.trans_hom, Category.assoc]
  rw [← Category.assoc (((Tor (ModuleCat.{u} R) 1).map f).app N),
    Tor_iso_Tor'.oneIsoTK_R_sq]
  simp only [Category.assoc]
  rw [← Category.assoc (HomologicalComplex.homologyMap (Tor_iso_Tor'.oneIsoTK_Φ R f N).τ₃ 1),
    Tor_iso_Tor'.oneIsoTK_e3_sq]
  simp only [Category.assoc]
  rw [Tor_iso_Tor'.oneIsoTK_e45_sq]
  simp only [Category.assoc]

/-- Naturality in `M` of the `Tor`-side kernel description, as an equality of natural
transformations. -/
theorem Tor_iso_Tor'.oneIso_torKer_sq {M M' : ModuleCat.{u} R} (f : M ⟶ M') :
    (Tor (ModuleCat.{u} R) 1).map f ≫ (Tor_iso_Tor'.oneIso_torKer R M').hom
      = (Tor_iso_Tor'.oneIso_torKer R M).hom ≫ Tor_iso_Tor'.oneKerMap R f := by
  refine NatTrans.ext (funext fun N => ?_)
  simp only [NatTrans.comp_app, Tor_iso_Tor'.oneIso_torKer, NatIso.ofComponents_hom_app]
  exact Tor_iso_Tor'.oneIsoTK_comp_sq R f N

/-- Naturality of `p` in `M` on the `Tor'` side. -/
theorem Tor_iso_Tor'.oneIso_p_sq {M M' : ModuleCat.{u} R} (f : M ⟶ M') (N : ModuleCat.{u} R) :
    HomologicalComplex.homologyMap (Tor_iso_Tor'.hsbΦ R f N).τ₁ 0 ≫
        (Tor_iso_Tor'.oneIso_p R M' N).hom
      = (Tor_iso_Tor'.oneIso_p R M N).hom ≫
        (tensorRight N).map (Tor_iso_Tor'.syzygyMap R f) := by
  have hτ₁ : HomologicalComplex.homologyMap (Tor_iso_Tor'.hsbΦ R f N).τ₁ 0
      = ((Tor_iso_Tor'.horseshoe R M).resK.isoLeftDerivedObj (tensorRight N) 0).inv ≫
          ((Tor' (ModuleCat.{u} R) 0).map (Tor_iso_Tor'.syzygyMap R f)).app N ≫
          ((Tor_iso_Tor'.horseshoe R M').resK.isoLeftDerivedObj (tensorRight N) 0).hom := by
    have h := Tor_iso_Tor'.hsbL_sq R f N 0
    rw [Iso.eq_inv_comp]
    exact h.symm
  dsimp only [Tor_iso_Tor'.oneIso_p]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Functor.leftDerivedZeroIsoSelf_hom,
    Category.assoc]
  rw [hτ₁]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  have hldz := (Functor.leftDerivedZeroIsoSelf (tensorRight N)).hom.naturality
    (Tor_iso_Tor'.syzygyMap R f)
  simp only [Functor.leftDerivedZeroIsoSelf_hom] at hldz
  rw [show ((Tor' (ModuleCat.{u} R) 0).map (Tor_iso_Tor'.syzygyMap R f)).app N
        = ((tensorRight N).leftDerived 0).map (Tor_iso_Tor'.syzygyMap R f) from rfl]
  rw [hldz]

/-- Transport of `(Tor' 1).map f` through `oneIso_e1`. -/
theorem Tor_iso_Tor'.oneIso_R_sq {M M' : ModuleCat.{u} R} (f : M ⟶ M') (N : ModuleCat.{u} R) :
    ((Tor' (ModuleCat.{u} R) 1).map f).app N ≫ (Tor_iso_Tor'.oneIso_e1 R M' N).hom
      = (Tor_iso_Tor'.oneIso_e1 R M N).hom ≫
        HomologicalComplex.homologyMap (Tor_iso_Tor'.hsbΦ R f N).τ₃ 1 :=
  Tor_iso_Tor'.hsbR_sq R f N 1

/-- Naturality of `e3` in `M` on the `Tor'` side. -/
theorem Tor_iso_Tor'.oneIso_e3_sq {M M' : ModuleCat.{u} R} (f : M ⟶ M') (N : ModuleCat.{u} R) :
    HomologicalComplex.homologyMap (Tor_iso_Tor'.hsbΦ R f N).τ₃ 1 ≫
        (Tor_iso_Tor'.oneIso_e3 R M' N).hom
      = (Tor_iso_Tor'.oneIso_e3 R M N).hom ≫
        Limits.kernel.map _ _ (HomologicalComplex.homologyMap (Tor_iso_Tor'.hsbΦ R f N).τ₁ 0)
          (HomologicalComplex.homologyMap (Tor_iso_Tor'.hsbΦ R f N).τ₂ 0)
          (by rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp];
              congr 1; exact (Tor_iso_Tor'.hsbΦ R f N).comm₁₂.symm) := by
  apply (cancel_mono (Limits.kernel.ι
    (HomologicalComplex.homologyMap (Tor_iso_Tor'.oneIso_S R M' N).f 0))).mp
  rw [Category.assoc, Category.assoc, Tor_iso_Tor'.oneIso_e3_hom_ι,
    Limits.kernel.lift_ι, ← Category.assoc, Tor_iso_Tor'.oneIso_e3_hom_ι]
  have hrel : (ComplexShape.down ℕ).Rel 1 0 := by simp [ComplexShape.down_Rel]
  exact (HomologicalComplex.HomologySequence.δ_naturality (Tor_iso_Tor'.hsbΦ R f N)
    (Tor_iso_Tor'.oneIso_S_shortExact R M N) (Tor_iso_Tor'.oneIso_S_shortExact R M' N)
    1 0 hrel).symm

/-- Naturality of `e4 ≫ e5` in `M` on the `Tor'` side. -/
theorem Tor_iso_Tor'.oneIso_e45_sq {M M' : ModuleCat.{u} R} (f : M ⟶ M') (N : ModuleCat.{u} R) :
    Limits.kernel.map _ _ (HomologicalComplex.homologyMap (Tor_iso_Tor'.hsbΦ R f N).τ₁ 0)
          (HomologicalComplex.homologyMap (Tor_iso_Tor'.hsbΦ R f N).τ₂ 0)
          (by rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp];
              congr 1; exact (Tor_iso_Tor'.hsbΦ R f N).comm₁₂.symm) ≫
        ((Tor_iso_Tor'.oneIso_e4 R M' N).hom ≫ (Tor_iso_Tor'.oneIso_e5 R M' N).hom)
      = ((Tor_iso_Tor'.oneIso_e4 R M N).hom ≫ (Tor_iso_Tor'.oneIso_e5 R M N).hom) ≫
        (Tor_iso_Tor'.oneKerMap R f).app N := by
  apply (cancel_mono ((Limits.kernel.ι (Tor_iso_Tor'.oneIsoTK_η R M')).app N)).mp
  simp only [Category.assoc]
  rw [Tor_iso_Tor'.oneKerMap_app_ι_comp]
  simp only [Tor_iso_Tor'.oneIso_e5_hom_ι_assoc, Tor_iso_Tor'.oneIso_e5_hom_ι,
    Tor_iso_Tor'.oneIso_e4_hom_ι_assoc, Tor_iso_Tor'.oneIso_e4_hom_ι]
  rw [← Category.assoc, Limits.kernel.lift_ι]
  simp only [Category.assoc]
  rw [Tor_iso_Tor'.oneIso_p_sq R f N]
  rfl

/-- Naturality in `M` of the `Tor'`-side kernel description, at each `N`. -/
theorem Tor_iso_Tor'.oneIso_tor'Ker_comp_sq {M M' : ModuleCat.{u} R} (f : M ⟶ M')
    (N : ModuleCat.{u} R) :
    ((Tor' (ModuleCat.{u} R) 1).map f).app N ≫ (Tor_iso_Tor'.oneIso_tor'Ker_comp R M' N).hom
      = (Tor_iso_Tor'.oneIso_tor'Ker_comp R M N).hom ≫ (Tor_iso_Tor'.oneKerMap R f).app N := by
  simp only [Tor_iso_Tor'.oneIso_tor'Ker_comp, Iso.trans_hom, Category.assoc]
  rw [← Category.assoc (((Tor' (ModuleCat.{u} R) 1).map f).app N),
    Tor_iso_Tor'.oneIso_R_sq]
  simp only [Category.assoc]
  rw [← Category.assoc (HomologicalComplex.homologyMap (Tor_iso_Tor'.hsbΦ R f N).τ₃ 1),
    Tor_iso_Tor'.oneIso_e3_sq]
  simp only [Category.assoc]
  rw [Tor_iso_Tor'.oneIso_e45_sq]
  simp only [Category.assoc]

/-- Naturality in `M` of the `Tor'`-side kernel description, as an equality of natural
transformations. -/
theorem Tor_iso_Tor'.oneIso_tor'Ker_sq {M M' : ModuleCat.{u} R} (f : M ⟶ M') :
    (Tor' (ModuleCat.{u} R) 1).map f ≫ (Tor_iso_Tor'.oneIso_tor'Ker R M').hom
      = (Tor_iso_Tor'.oneIso_tor'Ker R M).hom ≫ Tor_iso_Tor'.oneKerMap R f := by
  refine NatTrans.ext (funext fun N => ?_)
  simp only [NatTrans.comp_app, Tor_iso_Tor'.oneIso_tor'Ker, NatIso.ofComponents_hom_app]
  exact Tor_iso_Tor'.oneIso_tor'Ker_comp_sq R f N

/-- Naturality in `M` of the inverse of the `Tor'`-side kernel description. -/
theorem Tor_iso_Tor'.oneIso_tor'Ker_sq_inv {M M' : ModuleCat.{u} R} (f : M ⟶ M') :
    Tor_iso_Tor'.oneKerMap R f ≫ (Tor_iso_Tor'.oneIso_tor'Ker R M').inv
      = (Tor_iso_Tor'.oneIso_tor'Ker R M).inv ≫ (Tor' (ModuleCat.{u} R) 1).map f := by
  exact (CommSq.vert_inv ⟨Tor_iso_Tor'.oneIso_tor'Ker_sq R f⟩).w

end naturalityOneAux

/-- Naturality of `oneIso` in `M`. -/
theorem Tor_iso_Tor'.naturality_one {M M' : ModuleCat.{u} R} (f : M ⟶ M') :
    (Tor (ModuleCat.{u} R) 1).map f ≫ (Tor_iso_Tor'.oneIso R M').hom
      = (Tor_iso_Tor'.oneIso R M).hom ≫ (Tor' (ModuleCat.{u} R) 1).map f := by
  simp only [Tor_iso_Tor'.oneIso, Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, Tor_iso_Tor'.oneIso_torKer_sq, Category.assoc,
    Tor_iso_Tor'.oneIso_tor'Ker_sq_inv, ← Category.assoc]

/-- Naturality in `M` of the dimension shift `tor'Shift`: for `f : M ⟶ M'` with induced morphism
of syzygy sequences `(syzygyMap f, overMap f, f)`,
`(Tor' (j+2)).map f ≫ (tor'Shift R j M').hom
  = (tor'Shift R j M).hom ≫ (Tor' (j+1)).map (syzygyMap f)`. -/
theorem Tor_iso_Tor'.tor'Shift_naturality_M (j : ℕ) {M M' : ModuleCat.{u} R} (f : M ⟶ M') :
    (Tor' (ModuleCat.{u} R) (j + 2)).map f ≫ (Tor_iso_Tor'.tor'Shift R j M').hom
      = (Tor_iso_Tor'.tor'Shift R j M).hom
        ≫ (Tor' (ModuleCat.{u} R) (j + 1)).map (Tor_iso_Tor'.syzygyMap R f) := by
  refine NatTrans.ext (funext fun N => ?_)
  simp only [NatTrans.comp_app, Tor_iso_Tor'.tor'Shift, NatIso.ofComponents_hom_app,
    Tor_iso_Tor'.tor'Shift_comp, Tor_iso_Tor'.tor'Shift_δIso, Iso.trans_hom, Iso.symm_hom,
    ShortComplex.ShortExact.δIso, asIso_hom, Category.assoc]
  have hrel : (ComplexShape.down ℕ).Rel (j + 2) (j + 1) := by simp [ComplexShape.down_Rel]
  have hδ := HomologicalComplex.HomologySequence.δ_naturality (Tor_iso_Tor'.hsbΦ R f N)
    (Tor_iso_Tor'.oneIso_S_shortExact R M N) (Tor_iso_Tor'.oneIso_S_shortExact R M' N)
    (j + 2) (j + 1) hrel
  have hM := Tor_iso_Tor'.hsbR_sq R f N (j + 2)
  have hK := Tor_iso_Tor'.hsbL_sq R f N (j + 1)
  have hKinv : HomologicalComplex.homologyMap (Tor_iso_Tor'.hsbΦ R f N).τ₁ (j + 1) ≫
        ((Tor_iso_Tor'.horseshoe R M').resK.isoLeftDerivedObj
          (MonoidalCategory.tensorRight N) (j + 1)).inv
      = ((Tor_iso_Tor'.horseshoe R M).resK.isoLeftDerivedObj
          (MonoidalCategory.tensorRight N) (j + 1)).inv ≫
        ((Tor' (ModuleCat.{u} R) (j + 1)).map (Tor_iso_Tor'.syzygyMap R f)).app N := by
    exact (CommSq.vert_inv ⟨hK⟩).w
  rw [← Category.assoc (((Tor' (ModuleCat.{u} R) (j + 2)).map f).app N), hM]
  have hinner : HomologicalComplex.homologyMap (Tor_iso_Tor'.hsbΦ R f N).τ₃ (j + 2) ≫
        (Tor_iso_Tor'.oneIso_S_shortExact R M' N).δ (j + 2) (j + 1) hrel ≫
        ((Tor_iso_Tor'.horseshoe R M').resK.isoLeftDerivedObj
          (MonoidalCategory.tensorRight N) (j + 1)).inv
      = (Tor_iso_Tor'.oneIso_S_shortExact R M N).δ (j + 2) (j + 1) hrel ≫
        ((Tor_iso_Tor'.horseshoe R M).resK.isoLeftDerivedObj
          (MonoidalCategory.tensorRight N) (j + 1)).inv ≫
        ((Tor' (ModuleCat.{u} R) (j + 1)).map (Tor_iso_Tor'.syzygyMap R f)).app N := by
    rw [← Category.assoc, ← hδ, Category.assoc, hKinv]
  rw [Category.assoc, hinner]

/-- Naturality of `app (j+2)` in `M`, given naturality of `app (j+1)` at `syzygyMap f`. -/
theorem Tor_iso_Tor'.naturality_succ (j : ℕ) {M M' : ModuleCat.{u} R} (f : M ⟶ M')
    (ih : (Tor (ModuleCat.{u} R) (j + 1)).map (Tor_iso_Tor'.syzygyMap R f)
            ≫ (Tor_iso_Tor'.app R (j + 1) (Tor_iso_Tor'.syzygy R M')).hom
          = (Tor_iso_Tor'.app R (j + 1) (Tor_iso_Tor'.syzygy R M)).hom
            ≫ (Tor' (ModuleCat.{u} R) (j + 1)).map (Tor_iso_Tor'.syzygyMap R f)) :
     (Tor (ModuleCat.{u} R) (j + 2)).map f ≫ (Tor_iso_Tor'.app R (j + 2) M').hom
      = (Tor_iso_Tor'.app R (j + 2) M).hom ≫ (Tor' (ModuleCat.{u} R) (j + 2)).map f := by
  change (Tor (ModuleCat.{u} R) (j + 2)).map f
      ≫ ((Tor_iso_Tor'.torShift R j M').hom ≫ (Tor_iso_Tor'.app R (j+1) (Tor_iso_Tor'.syzygy R
          M')).hom
          ≫ (Tor_iso_Tor'.tor'Shift R j M').inv)
      = ((Tor_iso_Tor'.torShift R j M).hom ≫ (Tor_iso_Tor'.app R (j+1) (Tor_iso_Tor'.syzygy R
          M)).hom
          ≫ (Tor_iso_Tor'.tor'Shift R j M).inv) ≫ (Tor' (ModuleCat.{u} R) (j + 2)).map f
  have : Module.Flat R (Tor_iso_Tor'.syzygySC R M).X₂ := Tor_iso_Tor'.torShift_flat_mid R M
  have : Module.Flat R (Tor_iso_Tor'.syzygySC R M').X₂ := Tor_iso_Tor'.torShift_flat_mid R M'
  have hA : (Tor (ModuleCat.{u} R) (j + 2)).map f ≫ (Tor_iso_Tor'.torShift R j M').hom
      = (Tor_iso_Tor'.torShift R j M).hom
        ≫ (Tor (ModuleCat.{u} R) (j + 1)).map (Tor_iso_Tor'.syzygyMap R f) := by
    refine NatTrans.ext (funext fun N => ?_)
    have h := lesShift.comp_naturality_S R (Tor_iso_Tor'.syzygySC_shortExact R M)
      (Tor_iso_Tor'.syzygySC_shortExact R M') j (Tor_iso_Tor'.synSES R f) N
    simpa only [NatTrans.comp_app, Tor_iso_Tor'.torShift, Tor_iso_Tor'.lesShift00M3,
      NatIso.ofComponents_hom_app, Tor_iso_Tor'.synSES] using h
  have hChom := Tor_iso_Tor'.tor'Shift_naturality_M R j f
  have hC : (Tor' (ModuleCat.{u} R) (j + 1)).map (Tor_iso_Tor'.syzygyMap R f)
        ≫ (Tor_iso_Tor'.tor'Shift R j M').inv
      = (Tor_iso_Tor'.tor'Shift R j M).inv ≫ (Tor' (ModuleCat.{u} R) (j + 2)).map f := by
    exact (CommSq.vert_inv ⟨hChom⟩).w
  rw [← Category.assoc, hA, Category.assoc, Category.assoc, reassoc_of% ih, Category.assoc, hC]

/-- Naturality in the first variable `M` of the per-`M` balancing isomorphism
`Tor_iso_Tor'.app`: the comparison commutes with `(Tor C i).map f` and `(Tor' C i).map f` for
every `f : M ⟶ M'`. -/
theorem Tor_iso_Tor'.naturality (i : ℕ) {M M' : ModuleCat.{u} R} (f : M ⟶ M') :
    (Tor (ModuleCat.{u} R) i).map f ≫ (Tor_iso_Tor'.app R i M').hom
      = (Tor_iso_Tor'.app R i M).hom ≫ (Tor' (ModuleCat.{u} R) i).map f := by
  induction i generalizing M M' with
  | zero => exact Tor_iso_Tor'.naturality_zero R f
  | succ j ih =>
      match j with
      | 0 => exact Tor_iso_Tor'.naturality_one R f
      | (k + 1) => exact Tor_iso_Tor'.naturality_succ R k f (ih _)

/-- The balancing of `Tor`: deriving the second variable agrees with deriving the first. -/
@[ega "0 11.6.5" "(iii)", ega "III 6.3.4" "special case"]
noncomputable def Tor_iso_Tor' (i : ℕ) :
    Tor (ModuleCat.{u} R) i ≅ Tor' (ModuleCat.{u} R) i :=
  NatIso.ofComponents (fun M => Tor_iso_Tor'.app R i M)
    (fun f => Tor_iso_Tor'.naturality R i f)

/-- For every `i ≥ 0` the two functors `(M, N) ↦ Tor_i^R(M, N)` and `(M, N) ↦ Tor_i^R(N, M)` are
canonically isomorphic: there is a natural isomorphism between the bifunctor
`Tor (ModuleCat R) i` and the swap bifunctor `(Tor (ModuleCat R) i).flip` in the functor category
`ModuleCat R ⥤ ModuleCat R ⥤ ModuleCat R`. -/
@[stacks 00M3,
  ega "III 6.3.5" "(i), special case",
  ega "III 6.5.5" "S = X = Y = Spec R",
  ega "III 6.7.13" "special case"]
theorem tor_symm_canonically_iso (i : ℕ) :
    Nonempty (Tor (ModuleCat.{u} R) i ≅ (Tor (ModuleCat.{u} R) i).flip) :=
  ⟨(Tor_iso_Tor' R i).trans (torFlip_iso_Tor' R i).symm⟩
