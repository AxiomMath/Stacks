module


public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Topology.Sheaves.Skyscraper
public import Mathlib.Geometry.RingedSpace.Basic
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar
public import StacksFrontier.Topology.Sheaves.Skyscraper.Modules
public import StacksFrontier.CategoryTheory.Abelian.Projective.Horseshoe
public import Std.Tactic.BVDecide.Normalize.Prop
public import StacksFrontier.CategoryTheory.Abelian.Projective.Horseshoe
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.FlatModuleSheavesAndStalks.StalkTensor

/-!
# Flatness and `Tor_1` over a ring, and the skyscraper realization of stalk modules

This file proves the per-ring fact that a module over a commutative ring is flat iff its first
`Tor` against every module vanishes (`OXModule.module_flat_iff_tor1`), via the horseshoe
construction and the long exact sequence of left-derived functors.  It then constructs, for a
point `x` and an `O_{X,x}`-module `N`, the skyscraper presheaf of `O_X`-modules
`OXModule.skyscraperPOM x N` and computes the stalk at `x` of its sheafification
(`OXModule.sheafify_skyscraperPOM_stalk_iso`).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory TopCat

universe u

namespace OXModule

variable {X : AlgebraicGeometry.RingedSpace.{u, u}}

attribute [local instance] sectionModule sectionPresheafModule stalkModule

/-! ## Stalk-wise reduction: the per-ring heart and the realization lemma

The main theorem is reduced (via `flat_iff_flat_stalk`) to a purely
*module-theoretic* statement over each local ring `O_{X,x}`:

  `F` flat  ↔  `∀ x, F_x` flat  ↔  `∀ x, ∀ N, Tor₁^{O_{X,x}}(F_x, N) = 0`
                                  ↔  `∀ G, ∀ x, Tor₁^{O_{X,x}}(F_x, G_x) = 0`
                                  =   `∀ G, Tor1IsZero F G`.

Two ingredients are needed beyond the correctness lemma `flat_iff_flat_stalk`:

* (HEART) the classical per-ring fact that an `R`-module is flat iff its first
  Tor against *every* module vanishes (`module_flat_iff_tor1`); and
* (REALIZATION) the fact that, for a fixed point `x`, *every* `O_{X,x}`-module
  `N` arises as the stalk `G_x` of some `O_X`-module `G` — concretely the
  skyscraper sheaf at `x` with value `N` (`exists_oxModule_stalk_iso`).  This is
  what lets us convert the `∀ N` quantifier (needed to test flatness of `F_x`)
  into the `∀ G` quantifier appearing in the statement. -/

/-! ## Per-ring heart (classical "flat ↔ Tor₁ vanishes")
For a commutative ring `R` and an `R`-module `M`, `M` is flat iff the first
(categorical) Tor of `M` with every `R`-module `N` is the zero module.

*Argument.*  `(⇒)` If `M` is flat then `- ⊗_R M` is exact, so the functor
`(tensoringLeft (ModuleCat R)).obj N` whose left-derived functor computes
`Tor` is already exact in the relevant degree; equivalently a flat module is an
acyclic object for the Tor bifunctor, so all higher Tor vanish, in particular
`Tor₁(M, N) = 0`.  Concretely: pick a short exact sequence
`0 → K → P → N → 0` with `P` projective (free); the long exact sequence of Tor
gives `Tor₁(M,N) ↪ K ⊗ M → P ⊗ M`, and the second map is injective because `M`
is flat (`Module.Flat.rTensor_preserves_injective_linearMap` /
`Module.Flat.iff_rTensor_exact`), forcing `Tor₁(M,N) = 0`.
`(⇐)` Conversely, vanishing of `Tor₁(M, -)` makes `- ⊗ M` left exact (the
connecting map `Tor₁(M,N) → K ⊗ M` is `0`, so `K ⊗ M → P ⊗ M` is injective for
all `K ↪ P`), which is flatness via
`Module.Flat.iff_rTensor_preserves_injective_linearMap`.

This is the classical result; Mathlib has the exactness/injectivity
characterizations of `Module.Flat` (`Module.Flat.iff_rTensor_exact`,
`Module.Flat.iff_rTensor_preserves_injective_linearMap`,
`Module.Flat.rTensor_preserves_injective_linearMap`) and the basic Tor API
(`CategoryTheory.Tor`, `isZero_Tor_succ_of_projective`, the long exact sequence
of a left-derived functor `Functor.leftDerived`), but *not* this packaged
equivalence (it is an explicit `TODO` in `Mathlib.RingTheory.Flat.CategoryTheory`).
It must be assembled from those pieces. -/

/-! ### Homological core of the reverse direction (LES of left-derived functors)

For an additive, right-exact `F` on `ModuleCat R` and a mono `f : A ⟶ B`,
vanishing of `(F.leftDerived 1).obj (cokernel f)` forces `(F.leftDerived 0).map f`
to be mono.  This is the only genuinely hard, not-pre-packaged piece; it is
isolated below into the single unproved lemma
`exists_exact_leftDerived_segment_of_mono` (the long-exact-sequence segment via
the horseshoe lemma), from which `additive_mono_of_isZero_leftDerived_one`
follows by short glue (zero source ⇒ left map zero ⇒ right map mono). -/

/-! ## Horseshoe construction

For a mono `f : A ⟶ B` in `ModuleCat R` the horseshoe construction is the case
`C := ModuleCat R`, `S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)` of the
construction in an arbitrary abelian category, which is `CategoryTheory.ShortComplex.horseshoe`
in `StacksFrontier/CategoryTheory/Abelian/Projective/Horseshoe.lean`.  That file carries the whole
development — the shear family `sₙ` with its cross-term identity, the twisted lower-triangular
differential, the middle complex with its degreewise splitting, and the augmentation — so none of
it is restated here; `exists_horseshoe_complex_split_covering` below reads the data off it. -/

/-- A short complex of chain complexes is *degreewise split* if each of its
degree-`i` components admits a `ShortComplex.Splitting`. -/
@[sga "4½ Etat_0 1.2.4" "special case"]
def DegreewiseSplit {R : Type u} [CommRing R]
    (S : ShortComplex (ChainComplex (ModuleCat.{u} R) ℕ)) : Prop :=
  ∀ i, Nonempty (ShortComplex.mk (S.f.f i) (S.g.f i)
    (by rw [← HomologicalComplex.comp_f, S.zero]; simp)).Splitting

/-- A degreewise-split short complex of chain complexes is short exact. -/
theorem shortExact_of_degreewiseSplit {R : Type u} [CommRing R]
    (S : ShortComplex (ChainComplex (ModuleCat.{u} R) ℕ))
    (hsplit : ∀ i, Nonempty (ShortComplex.mk (S.f.f i) (S.g.f i)
      (by rw [← HomologicalComplex.comp_f, S.zero]; simp)).Splitting) :
    S.ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  exact (hsplit i).some.shortExact

/-- An additive functor carries a degreewise-split short complex of chain
complexes (via `F.mapHomologicalComplex`) to another degreewise-split one. -/
theorem degreewiseSplit_map {R : Type u} [CommRing R]
    {D : Type*} [Category D] [Abelian D]
    (F : ModuleCat.{u} R ⥤ D) [F.Additive]
    (S : ShortComplex (ChainComplex (ModuleCat.{u} R) ℕ))
    (hsplit : ∀ i, Nonempty (ShortComplex.mk (S.f.f i) (S.g.f i)
      (by rw [← HomologicalComplex.comp_f, S.zero]; simp)).Splitting) :
    ∀ i, Nonempty (ShortComplex.mk ((S.map (F.mapHomologicalComplex _)).f.f i)
      ((S.map (F.mapHomologicalComplex _)).g.f i)
      (by rw [← HomologicalComplex.comp_f,
        (S.map (F.mapHomologicalComplex _)).zero]; simp)).Splitting := by
  intro i
  obtain ⟨sp⟩ := hsplit i
  exact ⟨sp.map F⟩

/-- **Horseshoe — construction leaf (decomposition point 1a/1b/1d).**
For a monomorphism `f : A ⟶ B` in `ModuleCat R`, there exist projective
resolutions `PA` of `A` and `PC` of `cokernel f`, a chain complex `T` (which is
*degreewise projective* `hTproj` and *has homology* `hThom`), chain maps
`ι : PA.complex ⟶ T` and `p : T ⟶ PC.complex` with `ι ≫ p = 0`, and an
augmentation `πT : T ⟶ single₀.obj B`, such that:
* `ShortComplex.mk ι p w` is degreewise split (`Splitting`);
* `ι` covers `f` and `p` covers `cokernel.π f` on the augmentations.

This is the *construction* half of Weibel's Horseshoe Lemma (Lemma 2.2.8): take
`PA := ProjectiveResolution.of A`, `PC := ProjectiveResolution.of (cokernel f)`,
set `T_n := (PA.complex)_n ⊞ (PC.complex)_n` (degreewise projective, biproduct),
`ι := biprod.inl`-degreewise, `p := biprod.snd`-degreewise (giving the `Splitting`
for free), and equip `T` with the *twisted lower-triangular* differential
`[[d_A, sₙ],[0, d_C]]` (the family `sₙ : (PC.complex)_n ⟶ (PA.complex)_{n-1}` built
inductively by `Projective.factorThru` along the relevant epis) and the
augmentation `πT = (f ∘ ε_A, σ)` with `σ` lifting `ε_C` along the epi
`cokernel.π f`.  It does NOT assert that `πT` is a quasi-iso — that acyclicity is
isolated in `horseshoe_augmentation_quasiIso` below. -/
theorem exists_horseshoe_complex_split_covering
    (R : Type u) [CommRing R]
    {A B : ModuleCat.{u} R} (f : A ⟶ B) [Mono f] :
    ∃ (PA : ProjectiveResolution A) (PC : ProjectiveResolution (cokernel f))
      (T : ChainComplex (ModuleCat.{u} R) ℕ)
      (_ : ∀ n, Projective (T.X n))
      (_ : ∀ i, HomologicalComplex.HasHomology T i)
      (ι : PA.complex ⟶ T) (p : T ⟶ PC.complex)
      (w : ι ≫ p = 0)
      (πT : T ⟶ (ChainComplex.single₀ (ModuleCat.{u} R)).obj B),
      (∀ i, Nonempty (ShortComplex.mk (ι.f i) (p.f i)
        (by rw [← HomologicalComplex.comp_f, w]; simp)).Splitting) ∧
      (ι ≫ πT = PA.π ≫ (ChainComplex.single₀ (ModuleCat.{u} R)).map f) ∧
      (p ≫ PC.π = πT ≫ (ChainComplex.single₀ (ModuleCat.{u} R)).map (cokernel.π f)) := by
  classical
  let S : ShortComplex (ModuleCat.{u} R) :=
    ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hS : S.ShortExact := ⟨S.exact_of_g_is_cokernel (cokernelIsCokernel f)⟩
  let PA : ProjectiveResolution S.X₁ := ProjectiveResolution.of A
  let PC : ProjectiveResolution S.X₃ := ProjectiveResolution.of (cokernel f)
  exact ⟨PA, PC, ShortComplex.HorseshoeAux.Tcx PA PC hS,
    ShortComplex.HorseshoeAux.Tcx_proj PA PC hS, fun _ => inferInstance,
    ShortComplex.HorseshoeAux.iota PA PC hS, ShortComplex.HorseshoeAux.proj PA PC hS,
    ShortComplex.HorseshoeAux.iota_comp_proj PA PC hS,
    ShortComplex.HorseshoeAux.aug PA PC hS,
    fun n => ⟨ShortComplex.HorseshoeAux.splitting PA PC hS n⟩,
    ShortComplex.HorseshoeAux.iota_comp_aug PA PC hS,
    ShortComplex.HorseshoeAux.proj_comp_π PA PC hS⟩

/-- **Horseshoe — acyclicity leaf (decomposition point 1c).**
Given the construction output of `exists_horseshoe_complex_split_covering` — a
degreewise-split short complex of complexes `PA.complex --ι--> T --p--> PC.complex`
(`split`) with `PA`, `PC` projective resolutions and the covering conditions —
the augmentation `πT : T ⟶ single₀.obj B` is a `QuasiIso`, i.e. `T` resolves `B`.

*Why true.*  The splitting makes `0 → PA.complex → T → PC.complex → 0` a short
exact sequence of chain complexes; its homology long exact sequence
(`ShortComplex.ShortExact.homology_exact₁/₂/₃`) together with the fact that
`PA`, `PC` are resolutions (homology concentrated in degree `0`, equal to `A`,
`coker f`) and the original short exact sequence `0 → A → B → coker f → 0` forces
`H_n(T) = 0` for `n > 0` and `H_0(T) ≅ B` via `πT`.  This is the genuine
"the middle of the horseshoe is acyclic" content. -/
theorem horseshoe_augmentation_quasiIso
    (R : Type u) [CommRing R]
    {A B : ModuleCat.{u} R} (f : A ⟶ B) [Mono f]
    (PA : ProjectiveResolution A) (PC : ProjectiveResolution (cokernel f))
    (T : ChainComplex (ModuleCat.{u} R) ℕ)
    (hThom : ∀ i, HomologicalComplex.HasHomology T i)
    (ι : PA.complex ⟶ T) (p : T ⟶ PC.complex)
    (w : ι ≫ p = 0)
    (πT : T ⟶ (ChainComplex.single₀ (ModuleCat.{u} R)).obj B)
    (split : ∀ i, Nonempty (ShortComplex.mk (ι.f i) (p.f i)
      (by rw [← HomologicalComplex.comp_f, w]; simp)).Splitting)
    (hιcov : ι ≫ πT = PA.π ≫ (ChainComplex.single₀ (ModuleCat.{u} R)).map f)
    (hpcov : p ≫ PC.π = πT ≫ (ChainComplex.single₀ (ModuleCat.{u} R)).map (cokernel.π f)) :
    QuasiIso πT := by
  -- SANITY CHECK PASSED
  have := hThom
  -- SES of complexes from the degreewise splitting
  have hSE₁ : (ShortComplex.mk ι p w).ShortExact :=
    shortExact_of_degreewiseSplit (ShortComplex.mk ι p w) split
  -- object SES `0 → A → B → coker f → 0`, mapped through `single₀`
  have hObjSE : (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).ShortExact := by
    refine { exact := ?_, mono_f := inferInstance, epi_g := inferInstance }
    exact ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f)
  have hSE₂ : ((ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).map
      (ChainComplex.single₀ (ModuleCat.{u} R))).ShortExact := hObjSE.map_of_exact _
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  match i with
  | 0 =>
    -- `H₀(πT)` is an iso by the short five lemma applied to the bottom of the two
    -- homology long exact sequences (the connecting maps vanish since `H₁(PC) = 0`
    -- and `H₁(single₀ (coker f)) = 0`).
    let φ : ShortComplex.mk ι p w ⟶
        (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).map
          (ChainComplex.single₀ (ModuleCat.{u} R)) :=
      { τ₁ := PA.π, τ₂ := πT, τ₃ := PC.π, comm₁₂ := hιcov.symm, comm₂₃ := hpcov.symm }
    set hf0 := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) 0 with
        hhf0
    have hτ₂ : (hf0.mapShortComplex.map φ).τ₂ = HomologicalComplex.homologyMap πT 0 := rfl
    rw [← hτ₂]
    have hExact₁ : (hf0.mapShortComplex.obj (ShortComplex.mk ι p w)).Exact :=
      hSE₁.homology_exact₂ 0
    have hExact₂ : (hf0.mapShortComplex.obj
        ((ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).map
          (ChainComplex.single₀ (ModuleCat.{u} R)))).Exact := hSE₂.homology_exact₂ 0
    have hzC : IsZero (((ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).map
        (ChainComplex.single₀ (ModuleCat.{u} R))).X₃.homology 1) :=
      HomologicalComplex.isZero_single_obj_homology (ComplexShape.down ℕ) 0 _ 1 (by norm_num)
    have hMonoF : Mono (hf0.mapShortComplex.obj
        ((ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).map
          (ChainComplex.single₀ (ModuleCat.{u} R)))).f := by
      have hex := hSE₂.homology_exact₁ 1 0 (by simp [ComplexShape.down])
      exact hex.mono_g (hzC.eq_zero_of_src _)
    have hEpiG : Epi (hf0.mapShortComplex.obj (ShortComplex.mk ι p w)).g :=
      ShortComplex.HorseshoeAux.epi_homologyMap_g_zero hSE₁
    have := PA.quasiIso
    have := PC.quasiIso
    have hτ₁ : IsIso (hf0.mapShortComplex.map φ).τ₁ := by
      change IsIso (HomologicalComplex.homologyMap PA.π 0); infer_instance
    have hτ₃ : IsIso (hf0.mapShortComplex.map φ).τ₃ := by
      change IsIso (HomologicalComplex.homologyMap PC.π 0); infer_instance
    exact ShortComplex.HorseshoeAux.shortFive hExact₁ hExact₂ hMonoF hEpiG
      (hf0.mapShortComplex.map φ) hτ₁ hτ₃
  | (n+1) =>
    -- In positive degree both `T` and `single₀ B` are acyclic, so the map is an
    -- iso between zero objects.  `H_{n+1}(T) = 0` from the homology LES sandwiched
    -- between `H_{n+1}(PA) = 0` and `H_{n+1}(PC) = 0` (both resolutions).
    have hPA : IsZero (PA.complex.homology (n+1)) := by
      rw [← HomologicalComplex.exactAt_iff_isZero_homology]; exact PA.complex_exactAt_succ n
    have hPC : IsZero (PC.complex.homology (n+1)) := by
      rw [← HomologicalComplex.exactAt_iff_isZero_homology]; exact PC.complex_exactAt_succ n
    have hT : IsZero (T.homology (n+1)) :=
      ShortComplex.HorseshoeAux.isZero_X₂ (hSE₁.homology_exact₂ (n+1)) hPA hPC
    have hSB : IsZero (((ChainComplex.single₀ (ModuleCat.{u} R)).obj B).homology (n+1)) :=
      HomologicalComplex.isZero_single_obj_homology (ComplexShape.down ℕ) 0 B (n+1) (by norm_num)
    exact IsZero.isIso hT hSB _

/-- **Horseshoe lemma (decomposition point — the genuine hard core).**
For a monomorphism `f : A ⟶ B` in `ModuleCat R`, the short exact sequence
`0 → A --f--> B --cokernel.π f--> coker f → 0` lifts to a *degreewise-split* short
exact sequence of projective resolutions
`0 → P_•(A) --ι--> P_•(B) --p--> P_•(coker f) → 0`, where the chain maps `ι`, `p`
cover `f` and `cokernel.π f` respectively (compatibility with the augmentations
`π`).  This is Weibel's Horseshoe Lemma (Lemma 2.2.8); it is NOT pre-packaged in
Mathlib.

The output is packaged so that the consuming glue lemma
`exists_exact_leftDerived_segment_of_mono` can:
* form the short complex of complexes `ShortComplex.mk ι p w` (its three terms are
  *definitionally* `PA.complex`, `PB.complex`, `PC.complex`);
* obtain its `ShortComplex.ShortExact` from the supplied `Splitting`
  (`ShortComplex.Splitting.shortExact`), which an additive `F` preserves;
* identify `homologyMap (F.map ι) 0` with `(F.leftDerived 0).map f` via
  `Functor.leftDerived_map_eq` (this uses the covering condition `hιcov`).

CONSTRUCTION PLAN:
  - `PA := ProjectiveResolution.of A`, `PC := ProjectiveResolution.of (cokernel f)`
    (or any chosen resolutions).
  - `(PB.complex)ₙ := (PA.complex)ₙ ⊞ (PC.complex)ₙ`; `ι := biprod.inl`-degreewise,
    `p := biprod.snd`-degreewise — this gives the `Splitting` for free.
  - Twisted lower-triangular differential `[[d_A, sₙ],[0, d_C]]` with
    `sₙ : (PC.complex)ₙ ⟶ (PA.complex)_{n-1}` built inductively by
    `Projective.factorThru` along the epi; augmentation `ε_B = (f ∘ ε_A, σ)` with
    `σ` lifting `ε_C` along the epi `cokernel.π f`.
  - Prove `d ∘ d = 0` and `QuasiIso PB.π` (the latter via the homology LES of the
    already-split SES of complexes — `homology_exact₁/₂/₃`), making `PB` a genuine
    `ProjectiveResolution B`. -/
theorem exists_split_projResolution_ses_of_mono
    (R : Type u) [CommRing R]
    {A B : ModuleCat.{u} R} (f : A ⟶ B) [Mono f] :
    ∃ (PA : ProjectiveResolution A) (PB : ProjectiveResolution B)
      (PC : ProjectiveResolution (cokernel f))
      (ι : PA.complex ⟶ PB.complex) (p : PB.complex ⟶ PC.complex)
      (w : ι ≫ p = 0),
      (∀ i, Nonempty (ShortComplex.mk (ι.f i) (p.f i)
        (by rw [← HomologicalComplex.comp_f, w]; simp)).Splitting) ∧
      (ι ≫ PB.π = PA.π ≫ (ChainComplex.single₀ (ModuleCat.{u} R)).map f) ∧
      (p ≫ PC.π = PB.π ≫ (ChainComplex.single₀ (ModuleCat.{u} R)).map (cokernel.π f)) := by
  -- SANITY CHECK PASSED
  -- Horseshoe construction, decomposed into two leaves:
  --   (1) `exists_horseshoe_complex_split_covering`: build the middle complex `T`
  --       on the degreewise biproduct, with the split maps `ι = inl`, `p = snd`,
  --       its augmentation `πT`, the `Splitting`, and the two covering conditions.
  --       Degreewise projectivity + `HasHomology` come along.  (Does NOT yet claim
  --       `πT` is a quasi-iso — that is leaf 2.)
  --   (2) `horseshoe_augmentation_quasiIso`: the homology-LES argument showing the
  --       constructed augmentation `πT` is a `QuasiIso`, so `T` resolves `B`.
  -- Assembly: package `T, πT, quasiIso` into `PB : ProjectiveResolution B`.
  obtain ⟨PA, PC, T, hTproj, hThom, ι, p, w, πT, hsplit, hιcov, hpcov⟩ :=
    exists_horseshoe_complex_split_covering R f
  have : ∀ i, HomologicalComplex.HasHomology T i := hThom
  have hqi : QuasiIso πT :=
    horseshoe_augmentation_quasiIso R f PA PC T hThom ι p w πT hsplit hιcov hpcov
  refine ⟨PA, ProjectiveResolution.mk T hTproj πT hqi, PC, ι, p, w, hsplit, hιcov, hpcov⟩

/-- **LES-segment glue (decomposition point — generic transport, no horseshoe).**
Given the output of the horseshoe lemma — a degreewise-split short exact sequence
of projective resolutions `0 → P_A --ι--> P_B --p--> P_C → 0` (`split`) whose
first map `ι` covers `f` (`hιcov`) — the exact homology segment
`H₁(F P_C) --δ--> H₀(F P_A) --H₀(F ι)--> H₀(F P_B)` (obtained from
`ShortComplex.ShortExact.homology_exact₁` after applying the additive `F`)
transports, across `ProjectiveResolution.isoLeftDerivedObj` (three instances) and
`Functor.leftDerived_map_eq` (identifying `H₀(F ι)` with `(F.leftDerived 0).map f`),
to the desired exact segment
`(F.leftDerived 1).obj (cokernel f) --δ'--> (F.leftDerived 0).obj A --(F.leftDerived 0).map f-->
(F.leftDerived 0).obj B`.

This contains NO horseshoe construction: it is the pure homological-algebra
transport.  The steps:
* `homology_exact₁` is applied at chain degrees `(i,j) = (1,0)` (already done in
  the caller, supplied here as the `Exact` hypothesis `hExact` after restating);
* assemble the iso of short complexes from the three `isoLeftDerivedObj`s plus
  `leftDerived_map_eq` (using `hιcov`), then `ShortComplex.exact_of_iso`.
NOTE: `PC` resolves `cokernel f`, so `(F.leftDerived 1).obj (cokernel f)` is the
`isoLeftDerivedObj` image of `H₁(F P_C)`; the existential `δ'` is `hFSE.δ 1 0 _`
conjugated by the relevant isos. -/
theorem exact_leftDerived_segment_of_split_projResolution_ses
    (R : Type u) [CommRing R]
    (F : ModuleCat.{u} R ⥤ ModuleCat.{u} R) [F.Additive] [PreservesFiniteColimits F]
    {A B : ModuleCat.{u} R} (f : A ⟶ B) [Mono f]
    (PA : ProjectiveResolution A) (PB : ProjectiveResolution B)
    (PC : ProjectiveResolution (cokernel f))
    (ι : PA.complex ⟶ PB.complex) (p : PB.complex ⟶ PC.complex)
    (w0 : ι ≫ p = 0)
    (split : ∀ i, Nonempty (ShortComplex.mk (ι.f i) (p.f i)
      (by rw [← HomologicalComplex.comp_f, w0]; simp)).Splitting)
    (hιcov : ι ≫ PB.π = PA.π ≫ (ChainComplex.single₀ (ModuleCat.{u} R)).map f) :
    ∃ δ : (F.leftDerived 1).obj (cokernel f) ⟶ (F.leftDerived 0).obj A,
      ∃ w : δ ≫ (F.leftDerived 0).map f = 0,
         (ShortComplex.mk δ ((F.leftDerived 0).map f) w).Exact := by
  -- SANITY CHECK PASSED
  set Shat : ShortComplex (ChainComplex (ModuleCat.{u} R) ℕ) := ShortComplex.mk ι p w0 with hShat
  have hSE : Shat.ShortExact := shortExact_of_degreewiseSplit Shat split
  set G := F.mapHomologicalComplex (ComplexShape.down ℕ) with hG
  have : G.Additive := inferInstanceAs (F.mapHomologicalComplex _).Additive
  have hsplitG := degreewiseSplit_map F Shat split
  have hFSE : (Shat.map G).ShortExact := shortExact_of_degreewiseSplit (Shat.map G) hsplitG
  have hrel : (ComplexShape.down ℕ).Rel 1 0 := by simp [ComplexShape.down_Rel]
  have hExact := hFSE.homology_exact₁ 1 0 hrel
  have hmid := Functor.leftDerived_map_eq F 0 f ι hιcov
  set e1 := PC.isoLeftDerivedObj F 1 with he1
  set e2 := PA.isoLeftDerivedObj F 0 with he2
  set e3 := PB.isoLeftDerivedObj F 0 with he3
  let boundary := hFSE.δ 1 0 hrel
  let homologyMap := HomologicalComplex.homologyMap (Shat.map G).f 0
  have homologyMap_eq : (F.mapHomologicalComplex (ComplexShape.down ℕ) ⋙
      HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) 0).map ι =
      homologyMap := rfl
  have midMap_eq : (F.leftDerived 0).map f = e2.hom ≫ homologyMap ≫ e3.inv :=
    hmid.trans (congrArg (fun morphism => e2.hom ≫ morphism ≫ e3.inv) homologyMap_eq)
  set δ : (F.leftDerived 1).obj (cokernel f) ⟶ (F.leftDerived 0).obj A :=
    e1.hom ≫ hFSE.δ 1 0 hrel ≫ e2.inv with hδ
  have hw : δ ≫ (F.leftDerived 0).map f = 0 := by
    have tailZero : boundary ≫ homologyMap ≫ e3.inv = 0 :=
      (Category.assoc boundary homologyMap e3.inv).symm.trans
        ((congrArg (fun morphism => morphism ≫ e3.inv) (hFSE.δ_comp 1 0 hrel)).trans zero_comp)
    exact (congrArg₂ (· ≫ ·) hδ midMap_eq).trans
      ((Category.assoc e1.hom (boundary ≫ e2.inv) (e2.hom ≫ homologyMap ≫ e3.inv)).trans
        ((congrArg (fun morphism => e1.hom ≫ morphism)
          (Category.assoc boundary e2.inv (e2.hom ≫ homologyMap ≫ e3.inv))).trans
          ((congrArg (fun morphism => e1.hom ≫ boundary ≫ morphism)
            (e2.inv_hom_id_assoc (homologyMap ≫ e3.inv))).trans
            ((congrArg (fun morphism => e1.hom ≫ morphism) tailZero).trans comp_zero))))
  refine ⟨δ, hw, ?_⟩
  refine ShortComplex.exact_of_iso ?_ hExact
  set e1' : (Shat.map G).X₃.homology 1 ≅ (F.leftDerived 1).obj (cokernel f) := e1.symm with he1eq
  set e2' : (Shat.map G).X₁.homology 0 ≅ (F.leftDerived 0).obj A := e2.symm with he2eq
  set e3' : (Shat.map G).X₂.homology 0 ≅ (F.leftDerived 0).obj B := e3.symm with he3eq
  have he1 : e1'.hom = e1.inv := by rw [he1eq]; exact Iso.symm_hom e1
  have he2 : e2'.hom = e2.inv := by rw [he2eq]; exact Iso.symm_hom e2
  have he3 : e3'.hom = e3.inv := by rw [he3eq]; exact Iso.symm_hom e3
  refine ShortComplex.isoMk e1' e2' e3' ?_ ?_
  · exact (congrArg₂ (· ≫ ·) he1 hδ).trans
      ((e1.inv_hom_id_assoc (boundary ≫ e2.inv)).trans
        (congrArg (fun morphism => boundary ≫ morphism) he2.symm))
  · exact (congrArg₂ (· ≫ ·) he2 midMap_eq).trans
      ((e2.inv_hom_id_assoc (homologyMap ≫ e3.inv)).trans
        (congrArg (fun morphism => homologyMap ≫ morphism) he3.symm))

/-- **Exact segment of the left-derived long exact sequence.**
For an additive, right-exact functor `F` on `ModuleCat R` and a monomorphism
`f : A ⟶ B`, there is a connecting morphism
`δ : (F.leftDerived 1).obj (cokernel f) ⟶ (F.leftDerived 0).obj A` making the
short complex
`(F.leftDerived 1).obj (cokernel f) --δ--> (F.leftDerived 0).obj A --(F.leftDerived 0).map f-->
(F.leftDerived 0).obj B`
exact (at the middle term `(F.leftDerived 0).obj A`).

This is the long exact sequence of left-derived functors associated to the short
exact sequence `0 → A → B → coker f → 0`.  It is assembled from two decomposition
points: the **horseshoe lemma** `exists_split_projResolution_ses_of_mono` (the
genuinely hard construction of a degreewise-split SES of projective resolutions
covering `f`), and the **generic transport** glue
`exact_leftDerived_segment_of_split_projResolution_ses` (apply the additive `F`,
`ShortComplex.ShortExact.homology_exact₁` at chain-degree `0`, transport across
`ProjectiveResolution.isoLeftDerivedObj` / `Functor.leftDerived_map_eq`). -/
theorem exists_exact_leftDerived_segment_of_mono
    (R : Type u) [CommRing R]
    (F : ModuleCat.{u} R ⥤ ModuleCat.{u} R) [F.Additive] [PreservesFiniteColimits F]
    {A B : ModuleCat.{u} R} (f : A ⟶ B) [Mono f] :
    ∃ δ : (F.leftDerived 1).obj (cokernel f) ⟶ (F.leftDerived 0).obj A,
      ∃ w : δ ≫ (F.leftDerived 0).map f = 0,
        (ShortComplex.mk δ ((F.leftDerived 0).map f) w).Exact := by
  -- SANITY CHECK PASSED
  -- Obtain the degreewise-split SES of projective resolutions covering `f`
  -- (horseshoe lemma), then run the generic LES-segment transport glue.
  obtain ⟨PA, PB, PC, ι, p, w0, hsplit, hιcov, _⟩ :=
    exists_split_projResolution_ses_of_mono R f
  exact exact_leftDerived_segment_of_split_projResolution_ses
    R F f PA PB PC ι p w0 hsplit hιcov

theorem additive_mono_of_isZero_leftDerived_one
    (R : Type u) [CommRing R]
    (F : ModuleCat.{u} R ⥤ ModuleCat.{u} R) [F.Additive] [PreservesFiniteColimits F]
    {A B : ModuleCat.{u} R} (f : A ⟶ B) [Mono f]
    (h : IsZero ((F.leftDerived 1).obj (cokernel f))) :
    Mono ((F.leftDerived 0).map f) := by
  -- SANITY CHECK PASSED
  -- Obtain the exact segment `(L₁F)(coker f) --δ--> (L₀F)A --(L₀F)f--> (L₀F)B`.
  obtain ⟨δ, w, hSexact⟩ := exists_exact_leftDerived_segment_of_mono R F f
  -- The left term `(L₁F)(coker f)` is a zero object (hypothesis `h`), so `δ = 0`.
  have hδ : δ = 0 := h.eq_zero_of_src δ
  -- An exact short complex whose left map is `0` has its right map mono.
  -- `ShortComplex.Exact.mono_g` needs the left map to be zero.
  exact hSexact.mono_g hδ

/-- **Dictionary lemma (reverse direction, gluing).**
If for every monomorphism `f` in `ModuleCat R` the morphism
`((tensoringLeft (ModuleCat R)).obj M).map f` (i.e. `(F.leftDerived 0)`-image,
after the `leftDerivedZeroIsoSelf` identification) is a monomorphism, then `M` is
flat.

*Argument.*  By `Module.Flat.iff_rTensor_preserves_injective_linearMap` it
suffices that `LinearMap.rTensor M g` is injective for every injective linear map
`g : N →ₗ[R] N'`.  Package `g` as a monomorphism `f := ModuleCat.ofHom g` in
`ModuleCat R` (`ModuleCat.mono_iff_injective`); the functor
`(tensoringLeft (ModuleCat R)).obj M` sends `f` to (the `ModuleCat` packaging of)
`rTensor M g` up to the standard monoidal identification, and
`ModuleCat.mono_iff_injective` turns the mono hypothesis back into injectivity of
`rTensor M g`. -/
@[ega "0 6.1.1" "tensor exact ⇒ flat", sga "4 V 1.1" "partial"]
theorem module_flat_of_tensoringLeft_map_mono (R : Type u) [CommRing R]
    (M : ModuleCat.{u} R)
    (H : ∀ {A B : ModuleCat.{u} R} (f : A ⟶ B), Mono f →
      Mono (((tensoringLeft (ModuleCat.{u} R)).obj M).map f)) :
    Module.Flat R M := by
  -- SANITY CHECK PASSED
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro N N' _ _ _ _ g hg
  have hmono : Mono (ModuleCat.ofHom g) := (ModuleCat.mono_iff_injective _).mpr hg
  have hres := H (ModuleCat.ofHom g) hmono
  rw [ModuleCat.mono_iff_injective] at hres
  exact hres

@[ega "0 10.1.3" "c ⇒ d",
  ega "0 10.2.1" "a ⇒ Tor₁^A(M",
  ega "0 6.1.1" "(a) ⇔ (c)",
  ega "III 6.5.8" "Affine case",
  sga "1 IV 4.3" "(iii) ⇒ (iv)",
  sga "1 IV 5.2" "(i) ⇔ (ii), special case",
  sga "1 IV 5.5" "(i)⇒(ii)",
  sga "6 I 5.1.1" "Case m = n",
  sga "7 VIII 1.2" "special case"]
theorem module_flat_iff_tor1 (R : Type u) [CommRing R] (M : ModuleCat.{u} R) :
    Module.Flat R M ↔
      ∀ N : ModuleCat.{u} R, IsZero (((Tor (ModuleCat.{u} R) 1).obj M).obj N) := by
  constructor
  · -- (⇒) If `M` is flat, the functor `M ⊗ -` (`tensoringLeft.obj M`) is an exact
    -- functor, hence all its higher left-derived functors vanish.
    intro hM N
    -- `(Tor _ 1).obj M).obj N = ((tensoringLeft _).obj M).leftDerived 1 .obj N`
    -- `tensoringLeft.obj M` is additive, preserves finite colimits always, and
    -- preserves finite limits because `M` is flat; so it is exact and its first
    -- left-derived functor is zero.
    set F : ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
      (MonoidalCategory.tensoringLeft (ModuleCat.{u} R)).obj M with hF
    change IsZero ((F.leftDerived 1).obj N)
    -- general fact: an additive functor that is exact (preserves finite limits and
    -- colimits) has vanishing higher left-derived functors.
    have key : ∀ (n : ℕ) (X : ModuleCat.{u} R), IsZero ((F.leftDerived (n + 1)).obj X) := by
      intro n X
      let P : ProjectiveResolution X := (HasProjectiveResolutions.out X).out.some
      rw [(P.isoLeftDerivedObj F (n + 1)).isZero_iff, HomologicalComplex.homologyFunctor_obj,
        ← HomologicalComplex.exactAt_iff_isZero_homology, HomologicalComplex.exactAt_iff]
      have hP : (P.complex).ExactAt (n + 1) := ProjectiveResolution.complex_exactAt_succ P n
      rw [HomologicalComplex.exactAt_iff] at hP
      exact ShortComplex.exact_of_iso (Iso.refl _) (hP.map_of_preservesLeftHomologyOf F)
    exact key 0 N
  · -- (⇐) Vanishing of `Tor₁(M, -)` forces `M ⊗ -` to be left exact, i.e. `M` flat.
    intro H
    -- Reduce flatness to: `tensoringLeft.obj M` preserves monomorphisms.
    apply module_flat_of_tensoringLeft_map_mono R M
    intro A B f hf
    -- The functor whose left-derived computes `Tor`.
    set F : ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
      (tensoringLeft (ModuleCat.{u} R)).obj M with hF
    -- `F.leftDerived 0 ≅ F` (right-exact additive functor).
    have ε : F.leftDerived 0 ≅ F := Functor.leftDerivedZeroIsoSelf F
    -- The hypothesis `H` at `N := cokernel f` gives `Tor₁(M, coker f) = 0`,
    -- definitionally `(F.leftDerived 1).obj (cokernel f)`.
    have h1 : IsZero ((F.leftDerived 1).obj (cokernel f)) := H (cokernel f)
    -- Homological core: `(F.leftDerived 0).map f` is mono.
    have hmono0 : Mono ((F.leftDerived 0).map f) :=
      additive_mono_of_isZero_leftDerived_one R F f h1
    -- Transport along the natural iso `ε : F.leftDerived 0 ≅ F` to get `Mono (F.map f)`.
    have hiB : IsIso (ε.hom.app B) := NatIso.isIso_app_of_isIso ε.hom B
    have hiA : IsIso (ε.hom.app A) := NatIso.isIso_app_of_isIso ε.hom A
    -- Naturality square: `(F.leftDerived 0).map f ≫ ε.hom.app B = ε.hom.app A ≫ F.map f`.
    have hnat : (F.leftDerived 0).map f ≫ ε.hom.app B = ε.hom.app A ≫ F.map f :=
      ε.hom.naturality f
    have hmB : Mono (ε.hom.app B) := IsIso.mono_of_iso _
    -- `(F.leftDerived 0).map f ≫ ε.hom.app B` is mono (mono ≫ iso).
    have hcomp0 : Mono ((F.leftDerived 0).map f ≫ ε.hom.app B) :=
      @mono_comp _ _ _ _ _ ((F.leftDerived 0).map f) hmono0 (ε.hom.app B) hmB
    -- Rewrite via naturality: `ε.hom.app A ≫ F.map f` is mono.
    have hcomp : Mono (ε.hom.app A ≫ F.map f) := hnat ▸ hcomp0
    -- Cancel the iso `ε.hom.app A` on the left: `F.map f` is mono.
    have hfac : F.map f = inv (ε.hom.app A) ≫ (ε.hom.app A ≫ F.map f) := by
      rw [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
    have hminv : Mono (inv (ε.hom.app A)) := IsIso.mono_of_iso _
    rw [hfac]
    exact @mono_comp _ _ _ _ _ (inv (ε.hom.app A)) hminv (ε.hom.app A ≫ F.map f) hcomp

open Classical in
/-- **Realization of stalk modules (skyscraper sheaf).**
For a fixed point `x` and an arbitrary `O_{X,x}`-module `N`, there is an
`O_X`-module `G` whose stalk at `x` is isomorphic to `N`.

*Argument.*  Take `G` to be the skyscraper sheaf at `x` with value `N`, viewed
as an `O_X`-module via the stalk ring map `O_X(U) → O_{X,x}` for `U ∋ x`.  Its
stalk at `x` is the filtered colimit over open neighborhoods `U ∋ x` of the
constant value `N`, with identity transition maps, hence canonically `N`.

The carrier object of the skyscraper presheaf-of-modules at `x` with value
`N`: over an open `U` containing `x` it is `N` with `O_X(U)`-action restricted
along the germ ring map `O_X(U) → O_{X,x}`; elsewhere it is the zero module.
(Validated, proof-complete building block for the skyscraper realization.) -/
noncomputable def skyscraperObj (x : X.carrier) (N : ModuleCat.{u} (X.presheaf.stalk x))
    (U : (TopologicalSpace.Opens X.carrier)ᵒᵖ) :
    ModuleCat.{u} ((X.presheaf ⋙ forget₂ CommRingCat RingCat).obj U) :=
  if h : x ∈ U.unop then
    (ModuleCat.restrictScalars (X.presheaf.germ U.unop x h).hom).obj N
  else
    ModuleCat.of _ PUnit.{u+1}

/-- Compatibility of germs of the structure sheaf: for `i : U ⟶ V` (i.e.
`V ⊆ U`) and `x ∈ V`, the germ at `U` factors as the germ at `V` precomposed
with the restriction `O_X(U) → O_X(V)`.  (Validated, proof-complete.) -/
theorem structure_germ_comp (x : X.carrier)
    {U V : (TopologicalSpace.Opens X.carrier)ᵒᵖ} (i : U ⟶ V) (hV : x ∈ V.unop) :
    (X.presheaf.germ U.unop x ((leOfHom i.unop) hV)).hom =
      ((X.presheaf.germ V.unop x hV).hom).comp ((X.presheaf.map i).hom) := by
  have h := X.presheaf.germ_res i.unop x hV
  have e : i.unop.op = i := rfl
  rw [e] at h
  rw [← CommRingCat.hom_comp, h]

/-- The transition map of the skyscraper presheaf-of-modules.  On the open sets
containing `x` it is the canonical change-of-scalars identification built from
`structure_germ_comp` and `ModuleCat.restrictScalarsComp'`; otherwise it is the
zero map (the target sits over the zero module).  (Validated, proof-complete.) -/
noncomputable def skyscraperMap (x : X.carrier) (N : ModuleCat.{u} (X.presheaf.stalk x))
    {U V : (TopologicalSpace.Opens X.carrier)ᵒᵖ} (i : U ⟶ V) :
    skyscraperObj x N U ⟶ (ModuleCat.restrictScalars
      (RingCat.Hom.hom ((X.presheaf ⋙ forget₂ CommRingCat RingCat).map i))).obj
        (skyscraperObj x N V) := by
  classical
  by_cases hV : x ∈ V.unop
  · have hU : x ∈ U.unop := (leOfHom i.unop) hV
    have eU : skyscraperObj x N U =
        (ModuleCat.restrictScalars (X.presheaf.germ U.unop x hU).hom).obj N := by
      rw [skyscraperObj, dite_eq_left hU]
    have eV : skyscraperObj x N V =
        (ModuleCat.restrictScalars (X.presheaf.germ V.unop x hV).hom).obj N := by
      rw [skyscraperObj, dite_eq_left hV]
    refine eqToHom eU ≫ ?_ ≫
      (ModuleCat.restrictScalars
        (RingCat.Hom.hom ((X.presheaf ⋙ forget₂ CommRingCat RingCat).map i))).map
          (eqToHom eV.symm)
    exact (ModuleCat.restrictScalarsComp' ((X.presheaf.map i).hom)
      (X.presheaf.germ V.unop x hV).hom (X.presheaf.germ U.unop x hU).hom
      (structure_germ_comp x i hV)).hom.app N
  · exact 0

/-- The forward component of the change-of-scalars coherence iso
`restrictScalarsComp'App` is the canonical `eqToHom` cast (it is built from
`AddEquiv.refl`, hence the identity on underlying types).  Used to collapse the
skyscraper transition maps to `eqToHom`s in the coherence proofs. -/
theorem restrictScalarsComp'App_hom_eqToHom
    {R₁ R₂ R₃ : Type u} [Ring R₁] [Ring R₂] [Ring R₃]
    (f : R₁ →+* R₂) (g : R₂ →+* R₃) (gf : R₁ →+* R₃) (h : gf = g.comp f)
    (M : ModuleCat R₃) :
    (ModuleCat.restrictScalarsComp'App f g gf h M).hom = eqToHom (by subst h; rfl) := by
  subst h; rfl

/-- The inverse component of the identity change-of-scalars iso
`restrictScalarsId'App` is the canonical `eqToHom` cast (built from
`AddEquiv.refl`). -/
theorem restrictScalarsId'App_inv_eqToHom
    {R : Type u} [Ring R] (f : R →+* R) (h : f = RingHom.id R) (M : ModuleCat R) :
    (ModuleCat.restrictScalarsId'App f h M).inv = eqToHom (by subst h; rfl) := by
  subst h; rfl

/-- Morphisms into the restriction of scalars of `skyscraperObj x N U` are equal when `x ∉ U`. -/
private theorem hom_ext_restrictScalars_skyscraperObj_of_not_mem (x : X.carrier)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) {U : (TopologicalSpace.Opens X.carrier)ᵒᵖ}
    (hU : x ∉ U.unop) {R : Type u} [Ring R]
    (f : R →+* (X.presheaf ⋙ forget₂ CommRingCat RingCat).obj U) {M : ModuleCat.{u} R}
    (a b : M ⟶ (ModuleCat.restrictScalars f).obj (skyscraperObj x N U)) : a = b := by
  have : skyscraperObj x N U = ModuleCat.of _ PUnit.{u+1} := by
    rw [skyscraperObj, dite_eq_right hU]
  have : Subsingleton ((ModuleCat.restrictScalars f).obj (skyscraperObj x N U)) := by
    rw [this]
    exact inferInstanceAs (Subsingleton PUnit.{u+1})
  exact ModuleCat.hom_ext (LinearMap.ext fun y => Subsingleton.elim _ _)

/-- **Coherence (LEAF 1a): identity law for the skyscraper transition maps.**
This is the `map_id` field needed to assemble `skyscraperObj`/`skyscraperMap`
into a `PresheafOfModules`.  By the case split in `skyscraperMap`:
* on `x ∈ U` the map is built from `structure_germ_comp x (𝟙 U)` (which reduces
  the germ factorization to `germ_U = germ_U ∘ 𝟙`) and the `restrictScalarsComp'`
  coherence iso; unfolding shows it equals the canonical `restrictScalarsId'.inv`
  component — this is `restrictScalarsId'`/`restrictScalarsComp'`/`eqToHom`
  coherence (`eqToHom_map`, `eqToHom_trans`, `eqToHom_app`);
* on `x ∉ U` the codomain is the zero module `PUnit`, so both sides are forced
  equal by `Subsingleton` of homs into `PUnit` (`Subsingleton.elim`).
Routine but verbose; no deep content. -/
theorem skyscraperMap_id (x : X.carrier) (N : ModuleCat.{u} (X.presheaf.stalk x))
    (U : (TopologicalSpace.Opens X.carrier)ᵒᵖ) :
    skyscraperMap x N (𝟙 U) =
      (ModuleCat.restrictScalarsId'
        (RingCat.Hom.hom ((X.presheaf ⋙ forget₂ CommRingCat RingCat).map (𝟙 U)))
        (by simp)).inv.app (skyscraperObj x N U) := by
  classical
  rw [skyscraperMap]
  by_cases hU : x ∈ U.unop
  · rw [dite_eq_left hU]
    -- Both the `restrictScalarsComp'`/`restrictScalarsId'` coherence isos are
    -- `AddEquiv.refl`-based, hence `eqToHom` casts; collapse the whole composite
    -- to a single `eqToHom` between equal objects (`eqToHom_trans`).
    simp only [ModuleCat.restrictScalarsId'_inv_app, ModuleCat.restrictScalarsComp'_hom_app,
      restrictScalarsComp'App_hom_eqToHom, restrictScalarsId'App_inv_eqToHom, eqToHom_map,
      eqToHom_trans]
  · rw [dite_eq_right hU]
    exact hom_ext_restrictScalars_skyscraperObj_of_not_mem x N hU _ _ _

/-- **Coherence (LEAF 1b): composition law for the skyscraper transition maps.**
This is the `map_comp` field needed to assemble `skyscraperObj`/`skyscraperMap`
into a `PresheafOfModules`.  By the case split in `skyscraperMap`:
* on `x ∈ U` (hence `x ∈ V`, `x ∈ W` whenever they appear) it follows from
  `structure_germ_comp` applied along `i` and `j` and the associativity/coherence
  of `restrictScalarsComp'` (the germ factorizes as
  `germ_U = germ_W ∘ R.map j ∘ R.map i`);
* whenever the target sits over a `PUnit` zero module both sides agree by
  `Subsingleton`.
Routine but verbose; no deep content. -/
theorem skyscraperMap_comp (x : X.carrier) (N : ModuleCat.{u} (X.presheaf.stalk x))
    {U V W : (TopologicalSpace.Opens X.carrier)ᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) :
    skyscraperMap x N (i ≫ j) =
      skyscraperMap x N i ≫
        (ModuleCat.restrictScalars
            (RingCat.Hom.hom ((X.presheaf ⋙ forget₂ CommRingCat RingCat).map i))).map
            (skyscraperMap x N j) ≫
          (ModuleCat.restrictScalarsComp'
                  (RingCat.Hom.hom ((X.presheaf ⋙ forget₂ CommRingCat RingCat).map i))
                  (RingCat.Hom.hom ((X.presheaf ⋙ forget₂ CommRingCat RingCat).map j))
                  (RingCat.Hom.hom ((X.presheaf ⋙ forget₂ CommRingCat RingCat).map (i ≫ j)))
                  (by simp)).inv.app
            (skyscraperObj x N W) := by
  classical
  by_cases hW : x ∈ W.unop
  · have hV : x ∈ V.unop := (leOfHom j.unop) hW
    have hU : x ∈ U.unop := (leOfHom i.unop) hV
    have hinv : ∀ {R₁ R₂ R₃ : Type u} [Ring R₁] [Ring R₂] [Ring R₃]
        (f : R₁ →+* R₂) (g : R₂ →+* R₃) (gf : R₁ →+* R₃) (h : gf = g.comp f)
        (M : ModuleCat R₃),
        (ModuleCat.restrictScalarsComp'App f g gf h M).inv = eqToHom (by subst h; rfl) := by
      intro R₁ R₂ R₃ _ _ _ f g gf h M; subst h; rfl
    rw [skyscraperMap, skyscraperMap, skyscraperMap]
    rw [dite_eq_left hW, dite_eq_left hV, dite_eq_left hW]
    simp only [ ModuleCat.restrictScalarsComp'_inv_app,
      ModuleCat.restrictScalarsComp'_hom_app, restrictScalarsComp'App_hom_eqToHom,
      eqToHom_map, eqToHom_trans,
       eqToHom_trans_assoc]
    rw [hinv]
    simp only [eqToHom_trans]
  · rw [skyscraperMap]
    rw [dite_eq_right hW]
    exact hom_ext_restrictScalars_skyscraperObj_of_not_mem x N hW _ _ _

/-- The skyscraper presheaf-of-modules at `x` with value `N`: assembled from the
verified `skyscraperObj`/`skyscraperMap` building blocks plus the two coherence
leaves `skyscraperMap_id`/`skyscraperMap_comp`.  Sheafifying this (via
`OXModule.sheafify`) yields the `O_X`-module realizing `N` as a stalk. -/
noncomputable def skyscraperPOM (x : X.carrier) (N : ModuleCat.{u} (X.presheaf.stalk x)) :
    PresheafOfModules.{u} ((ringSheaf X).obj) :=
  PresheafOfModules.mk (skyscraperObj x N) (fun {_ _} i => skyscraperMap x N i)
    (skyscraperMap_id x N) (fun {_ _ _} i j => skyscraperMap_comp x N i j)

/-! **(LEAF 3a) Sheafification preserves stalks, `O_{X,x}`-linearly (obligation O1).**
The sheafification unit `skyscraperPOM x N ⟶ (sheafify.obj (skyscraperPOM x N)).val`
of `PresheafOfModules.sheafification (𝟙 _)` is a stalkwise isomorphism at every
point: it induces an `O_{X,x}`-linear isomorphism between the stalk of the
sheafified module and the stalk of the original presheaf-of-modules.

*Justification.* The underlying
type/`AddCommGrp`-valued presheaf morphism of the unit is precisely the
sheafification unit for the open-cover Grothendieck topology of `X.carrier`; for
that site the unit is a local isomorphism, and `TopCat.Presheaf.stalkFunctor x`
inverts local isomorphisms (stalks are filtered colimits over `OpenNhds x`, and
local injectivity + local surjectivity become genuine bijectivity in the germ
colimit). The unit is a morphism *in* `PresheafOfModules`, so each component is
`O_X(U)`-linear; the induced colimit map is therefore `O_{X,x}`-linear because
the `O_{X,x}`-action factors through the germs `O_X(U) → O_{X,x}`.  Mathlib API:
`TopCat.Presheaf.stalkFunctor`, the local-iso/stalk-iso facts in
`Mathlib.Topology.Sheaves.Stalks`, transported across `PresheafOfModules.toPresheaf`. -/

noncomputable def sheafify_skyscraperPOM_stalkIso_O1
    (x : X.carrier) (N : ModuleCat.{u} (X.presheaf.stalk x)) :
    (sheafify.obj (skyscraperPOM x N)).stalk x ≅
      ModuleCat.of (X.presheaf.stalk x)
        ↑(TopCat.Presheaf.stalk (skyscraperPOM x N).presheaf x) :=
  (sheafifyStalkLinearEquiv x (skyscraperPOM x N)).symm.toModuleIso

/-- The underlying `AddCommGrp`-valued presheaf of the skyscraper PoM has value
(the underlying group of) `N` on every open containing `x`. -/
theorem skyscraperPOM_presheaf_obj_eq (x : X.carrier)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) (W : (TopologicalSpace.Opens X.carrier)ᵒᵖ)
    (h : x ∈ W.unop) :
    (skyscraperPOM x N).presheaf.obj W = AddCommGrpCat.of N := by
  change (forget₂ (ModuleCat _) AddCommGrpCat).obj (skyscraperObj x N W) = _
  rw [skyscraperObj, dite_eq_left h]
  rfl

/-- On opens containing `x`, the transition maps of the skyscraper PoM are, under
the canonical `= AddCommGrpCat.of N` identifications, the identity. -/
theorem skyscraperPOM_presheaf_map_eq (x : X.carrier)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) {W₁ W₂ : (TopologicalSpace.Opens X.carrier)ᵒᵖ}
    (j : W₁ ⟶ W₂) (h₂ : x ∈ W₂.unop) :
    (skyscraperPOM x N).presheaf.map j =
      eqToHom (skyscraperPOM_presheaf_obj_eq x N W₁ ((leOfHom j.unop) h₂)) ≫
        eqToHom (skyscraperPOM_presheaf_obj_eq x N W₂ h₂).symm := by
  change (forget₂ (ModuleCat _) AddCommGrpCat).map (skyscraperMap x N j) = _
  rw [skyscraperMap, dite_eq_left h₂]
  simp only [ restrictScalarsComp'App_hom_eqToHom,
    ModuleCat.restrictScalarsComp'_hom_app, eqToHom_map, eqToHom_trans]
  rfl

/-- **(LEAF 3b) Constant filtered colimit: the skyscraper stalk is `N` (abelian-group level).**
The underlying `AddCommGrp`-valued presheaf of `skyscraperPOM x N` is, on every
neighbourhood `U ∋ x`, the underlying group of `N` (the value of `skyscraperObj`
on opens containing `x` is `(restrictScalars (germ U)).obj N`, whose underlying
type/group is that of `N`), and `structure_germ_comp` makes every transition map
of the `OpenNhds x`-diagram the identity on `N`.  Hence the stalk at `x` — the
filtered colimit over the (nonempty, filtered) category `OpenNhds x` of this
constant diagram — is `N` as an abelian group.

*Justification.* Constant filtered
colimit (`Limits.colimitConstCone` / `IsColimit.coconePointUniqueUpToIso`), cf.
`skyscraperPresheafStalkOfSpecializes p₀ A (specializes_refl p₀)`.  The germ map
`N → stalk` for `U ∋ x` is the comparison iso. -/
noncomputable def sheafify_skyscraperPOM_stalkIso_skyscraper_addEquiv
    (x : X.carrier) (N : ModuleCat.{u} (X.presheaf.stalk x)) :
    ↑(TopCat.Presheaf.stalk (skyscraperPOM x N).presheaf x) ≃+ N := by
  set P := (skyscraperPOM x N).presheaf with hP
  -- membership of x in every neighbourhood appearing in the stalk diagram
  have hmem : ∀ (U : (TopologicalSpace.OpenNhds x)ᵒᵖ),
      x ∈ ((TopologicalSpace.OpenNhds.inclusion x).op.obj U).unop :=
    fun U => U.unop.2
  -- the value identification on the diagram objects
  let eU : ∀ (U : (TopologicalSpace.OpenNhds x)ᵒᵖ),
      ((TopologicalSpace.OpenNhds.inclusion x).op ⋙ P).obj U = AddCommGrpCat.of N :=
    fun U => skyscraperPOM_presheaf_obj_eq x N _ (hmem U)
  -- the colimit cocone with point N, all legs the canonical identifications
  let c : CategoryTheory.Limits.Cocone
      ((TopologicalSpace.OpenNhds.inclusion x).op ⋙ P) :=
    { pt := AddCommGrpCat.of N
      ι :=
        { app := fun U => eqToHom (eU U)
          naturality := by
            intro U V i
            simp only [Functor.comp_obj, Functor.const_obj_obj, Functor.comp_map,
              Functor.const_obj_map, Category.comp_id]
            rw [skyscraperPOM_presheaf_map_eq x N _ (hmem V)]
            simp only [eqToHom_trans] } }
  -- the desc gives the forward map; the germ at any U gives a section
  refine (?_ : (TopCat.Presheaf.stalk P x) ≅ AddCommGrpCat.of N).addCommGroupIsoToAddEquiv
  refine
    { hom := CategoryTheory.Limits.colimit.desc _ c
      inv := eqToHom (eU (Opposite.op ⊤)).symm ≫
        TopCat.Presheaf.germ P
          ((TopologicalSpace.OpenNhds.inclusion x).obj (⊤ : TopologicalSpace.OpenNhds x))
          x (hmem (Opposite.op ⊤))
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply TopCat.Presheaf.stalk_hom_ext
    intro U hxU
    let objectIso := eqToIso (eU (Opposite.op ⟨U, hxU⟩))
    let topIso := eqToIso (eU (Opposite.op ⊤))
    let germU := TopCat.Presheaf.germ P U x hxU
    let germTop := TopCat.Presheaf.germ P
      ((TopologicalSpace.OpenNhds.inclusion x).obj (⊤ : TopologicalSpace.OpenNhds x))
      x (hmem (Opposite.op ⊤))
    have hgd : germU ≫ CategoryTheory.Limits.colimit.desc _ c = objectIso.hom :=
      CategoryTheory.Limits.colimit.ι_desc c (Opposite.op ⟨U, hxU⟩)
    have hle : U ≤ (TopologicalSpace.OpenNhds.inclusion x).obj
        (⊤ : TopologicalSpace.OpenNhds x) := le_top
    have hmap : P.map (homOfLE hle).op = topIso.hom ≫ objectIso.inv :=
      skyscraperPOM_presheaf_map_eq x N (homOfLE hle).op hxU
    have hres : topIso.hom ≫ objectIso.inv ≫ germU = germTop :=
      (Category.assoc topIso.hom objectIso.inv germU).symm.trans
        ((congrArg (fun morphism => morphism ≫ germU) hmap).symm.trans
          (TopCat.Presheaf.germ_res P (homOfLE hle) x hxU))
    have topGerm : topIso.inv ≫ germTop = objectIso.inv ≫ germU :=
      (congrArg (fun morphism => topIso.inv ≫ morphism) hres).symm.trans
        (topIso.inv_hom_id_assoc (objectIso.inv ≫ germU))
    exact (Category.assoc germU (CategoryTheory.Limits.colimit.desc _ c)
      (topIso.inv ≫ germTop)).symm.trans
        ((congrArg (fun morphism => morphism ≫ topIso.inv ≫ germTop) hgd).trans
          ((congrArg (fun morphism => objectIso.hom ≫ morphism) topGerm).trans
            ((objectIso.hom_inv_id_assoc germU).trans (Category.comp_id germU).symm)))
  · let topIso := eqToIso (eU (Opposite.op ⊤))
    let germTop := TopCat.Presheaf.germ P
      ((TopologicalSpace.OpenNhds.inclusion x).obj (⊤ : TopologicalSpace.OpenNhds x))
      x (hmem (Opposite.op ⊤))
    have hgd : germTop ≫ CategoryTheory.Limits.colimit.desc _ c = topIso.hom :=
      CategoryTheory.Limits.colimit.ι_desc c (Opposite.op ⊤)
    exact (Category.assoc topIso.inv germTop (CategoryTheory.Limits.colimit.desc _ c)).trans
      ((congrArg (fun morphism => topIso.inv ≫ morphism) hgd).trans topIso.inv_hom_id)

/-- Characterization of the forward map of
`sheafify_skyscraperPOM_stalkIso_skyscraper_addEquiv` on a germ: it sends the germ
of `n` over a neighbourhood `U ∋ x` to the value `n`, under the canonical
identification `skyscraperPOM_presheaf_obj_eq`. -/
theorem sheafify_skyscraperPOM_stalkIso_skyscraper_addEquiv_germ
    (x : X.carrier) (N : ModuleCat.{u} (X.presheaf.stalk x))
    (U : (TopologicalSpace.Opens X.carrier)ᵒᵖ) (hx : x ∈ U.unop)
    (n : (skyscraperPOM x N).presheaf.obj U) :
    sheafify_skyscraperPOM_stalkIso_skyscraper_addEquiv x N
        (TopCat.Presheaf.germ (skyscraperPOM x N).presheaf U.unop x hx n) =
      (eqToHom (skyscraperPOM_presheaf_obj_eq x N U hx)) n := by
  have key : TopCat.Presheaf.germ (skyscraperPOM x N).presheaf U.unop x hx ≫
      AddCommGrpCat.ofHom
        (sheafify_skyscraperPOM_stalkIso_skyscraper_addEquiv x N).toAddMonoidHom =
      eqToHom (skyscraperPOM_presheaf_obj_eq x N U hx) := by
    exact CategoryTheory.Limits.colimit.ι_desc
      (F := (TopologicalSpace.OpenNhds.inclusion x).op ⋙ (skyscraperPOM x N).presheaf) _
      (Opposite.op (⟨U.unop, hx⟩ : TopologicalSpace.OpenNhds x))
  have happ := ConcreteCategory.congr_hom key n
  exact (ConcreteCategory.comp_apply
    (TopCat.Presheaf.germ (skyscraperPOM x N).presheaf U.unop x hx)
    (AddCommGrpCat.ofHom
      (sheafify_skyscraperPOM_stalkIso_skyscraper_addEquiv x N).toAddMonoidHom) n).symm.trans happ

/-- Casting along `P = (restrictScalars f).obj M` (at the level of underlying types)
turns the `R`-action into the `f`-twisted `S`-action. -/
theorem cast_smul_restrictScalars {R S : Type u} [Ring R] [Ring S]
    (f : R →+* S) (M : ModuleCat.{u} S) (P : ModuleCat.{u} R)
    (hP : P = (ModuleCat.restrictScalars f).obj M)
    (hT : (↑P : Type u) = ↑M) (s : R) (n : (↑P : Type u)) :
    cast hT (s • n) = f s • cast hT n := by
  subst hP
  exact ModuleCat.restrictScalars.smul_def f s n

/-- The canonical identification `skyscraperPOM_presheaf_obj_eq` intertwines the
`O_X(U)`-action on `skyscraperObj` (via `restrictScalars` along the germ) with the
`O_{X,x}`-action on `N`: applying the leg to `s • n` equals scaling `n` by the germ
of `s`. -/
theorem skyscraperPOM_leg_smul
    (x : X.carrier) (N : ModuleCat.{u} (X.presheaf.stalk x))
    (U : (TopologicalSpace.Opens X.carrier)ᵒᵖ) (hx : x ∈ U.unop)
    (s : (X.presheaf ⋙ forget₂ CommRingCat RingCat).obj U) (n : skyscraperObj x N U) :
    (eqToHom (skyscraperPOM_presheaf_obj_eq x N U hx)) (s • n) =
      (ConcreteCategory.hom (X.presheaf.germ U.unop x hx)) s •
        (eqToHom (skyscraperPOM_presheaf_obj_eq x N U hx)) n := by
  -- The leg `eqToHom` is the underlying identity; turn both applications into `cast`s.
  have hcast : ∀ {A B : AddCommGrpCat.{u}} (h : A = B) (y : A),
      (ConcreteCategory.hom (eqToHom h)) y
        = cast (congrArg (fun Z : AddCommGrpCat.{u} => (↑Z : Type u)) h) y := by
    intro A B h y; subst h; simp
  have hsky : skyscraperObj x N U = (ModuleCat.restrictScalars
      (X.presheaf.germ U.unop x hx).hom).obj N := by
    rw [skyscraperObj, dite_eq_left hx]
  have castScalar := cast_smul_restrictScalars (X.presheaf.germ U.unop x hx).hom N
    (skyscraperObj x N U) hsky
    (congrArg (fun group : AddCommGrpCat.{u} => (↑group : Type u))
      (skyscraperPOM_presheaf_obj_eq x N U hx)) s n
  exact (hcast (skyscraperPOM_presheaf_obj_eq x N U hx) (s • n)).trans
    (castScalar.trans
      (congrArg (fun value : N => X.presheaf.germ U.unop x hx s • value)
        (hcast (skyscraperPOM_presheaf_obj_eq x N U hx) n).symm))

noncomputable def sheafify_skyscraperPOM_stalkIso_skyscraper
    (x : X.carrier) (N : ModuleCat.{u} (X.presheaf.stalk x)) :
    ModuleCat.of (X.presheaf.stalk x)
        ↑(TopCat.Presheaf.stalk (skyscraperPOM x N).presheaf x) ≅ N :=
  LinearEquiv.toModuleIso
    { sheafify_skyscraperPOM_stalkIso_skyscraper_addEquiv x N with
      map_smul' := by
        intro r m
        obtain ⟨W₀, hxW₀, n₀, rfl⟩ := TopCat.Presheaf.exists_germ_eq (skyscraperPOM x N).presheaf m
        obtain ⟨V, hxV, s₀, rfl⟩ := TopCat.Presheaf.exists_germ_eq (X.presheaf) r
        -- common neighbourhood W = W₀ ⊓ V
        have hxW : x ∈ W₀ ⊓ V := ⟨hxW₀, hxV⟩
        -- restrict the representatives to W
        have hgn : TopCat.Presheaf.germ (skyscraperPOM x N).presheaf (W₀ ⊓ V) x hxW
              (((skyscraperPOM x N).presheaf.map (CategoryTheory.homOfLE (inf_le_left)).op) n₀) =
            TopCat.Presheaf.germ (skyscraperPOM x N).presheaf W₀ x hxW₀ n₀ :=
          TopCat.Presheaf.germ_res_apply (skyscraperPOM x N).presheaf
            (CategoryTheory.homOfLE (inf_le_left : W₀ ⊓ V ≤ W₀)) x hxW n₀
        have hgs : TopCat.Presheaf.germ (X.presheaf) (W₀ ⊓ V) x hxW
              ((ConcreteCategory.hom (X.presheaf.map (CategoryTheory.homOfLE (inf_le_right)).op))
                  s₀) =
            TopCat.Presheaf.germ (X.presheaf) V x hxV s₀ :=
          TopCat.Presheaf.germ_res_apply (X.presheaf)
            (CategoryTheory.homOfLE (inf_le_right : W₀ ⊓ V ≤ V)) x hxW s₀
        rw [← hgn, ← hgs]
        let restrictedScalar : X.presheaf.obj (Opposite.op (W₀ ⊓ V)) :=
          (X.presheaf.map (homOfLE inf_le_right).op) s₀
        let restrictedSection : skyscraperObj x N (Opposite.op (W₀ ⊓ V)) :=
          (skyscraperPOM x N).restrictₛₗ (homOfLE inf_le_left).op n₀
        exact (congrArg (sheafify_skyscraperPOM_stalkIso_skyscraper_addEquiv x N)
          (PresheafOfModules.germ_smul (R := X.presheaf) (skyscraperPOM x N) x
            (W₀ ⊓ V) hxW restrictedScalar restrictedSection).symm).trans
          ((sheafify_skyscraperPOM_stalkIso_skyscraper_addEquiv_germ x N
            (Opposite.op (W₀ ⊓ V)) hxW (restrictedScalar • restrictedSection)).trans
            ((skyscraperPOM_leg_smul x N (Opposite.op (W₀ ⊓ V)) hxW
              restrictedScalar restrictedSection).trans
              (congrArg (fun value : N =>
                X.presheaf.germ (W₀ ⊓ V) x hxW restrictedScalar • value)
                (sheafify_skyscraperPOM_stalkIso_skyscraper_addEquiv_germ x N
                  (Opposite.op (W₀ ⊓ V)) hxW restrictedSection).symm))) }

/-- **Stalk computation (LEAF 2): the sheafified skyscraper has stalk `N` at `x`.**
Assembled from the three leaves `sheafify_skyscraperPOM_stalkIso_O1` (O1,
sheafification preserves stalks), `sheafify_skyscraperPOM_stalkIso_skyscraper_addEquiv`
(constant-colimit skyscraper stalk `= N` at the abelian-group level) and
`sheafify_skyscraperPOM_stalkIso_skyscraper` (`O_{X,x}`-linearity glue), by
composing the O1 iso with the skyscraper-stalk iso. -/
noncomputable def sheafify_skyscraperPOM_stalk_iso
    (x : X.carrier) (N : ModuleCat.{u} (X.presheaf.stalk x)) :
    (sheafify.obj (skyscraperPOM x N)).stalk x ≅ N :=
  sheafify_skyscraperPOM_stalkIso_O1 x N ≪≫
    sheafify_skyscraperPOM_stalkIso_skyscraper x N

end OXModule
