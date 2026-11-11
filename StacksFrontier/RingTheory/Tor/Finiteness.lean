module

public import StacksCore.Tactic.StacksAttribute
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Mon
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
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.TotallySplit

/-!
# Tor of finite modules over a Noetherian ring is finite

Let `R` be a Noetherian ring and let `M` and `N` be finite `R`-modules. Then
`Tor_p^R(M, N)` is a finite `R`-module for every `p`.

Here `Tor_p^R(M, N)` is the object `((Tor (ModuleCat R) p).obj M).obj N` of the abelian
monoidal category `ModuleCat R`, the `p`-th left derived functor of the tensor product, with its
canonical `Module R` instance. Mathlib indexes `Tor` by `ℕ`; for `p < 0` the module
`Tor_p^R(M, N)` is zero and so trivially finite.

A finite module over a Noetherian ring has a finite free cover whose kernel is again finite, so
iterating this step gives a projective resolution of `N` by finite free modules. Tensoring it
with `M` gives a complex of finite modules whose homology computes `Tor_p^R(M, N)`.

We also show that the maps `H_i(F ⊗ N) ⟶ H_i(G ⊗ N)` induced by a lift of a module map to free
resolutions do not depend on the lift.

## Main definitions

* `syzResolution`: the projective resolution of a finite module `N` over a Noetherian ring by
  finite free modules.
* `FreeResolution`: a projective resolution all of whose terms are free.
* `FreeResolution.torMap`: the map on homology induced by tensoring a chain map of free
  resolutions with `N`.

## Main results

* `exists_finite_projectiveResolution`: a finite module over a Noetherian ring has a projective
  resolution all of whose terms are finite.
* `tor_finite_of_noetherian`: `Tor_p^R(M, N)` is a finite `R`-module.
* `torMap_independent_of_lift`: the map induced on homology by a lift of `φ` does not depend on
  the lift.
* `FreeResolution.isIso_torMap_of_isLift`, `FreeResolution.torMap_eq_id_of_isLift`: the induced
  map is an isomorphism when `φ` is, and the identity when `φ` is the identity.
* `FreeResolution.torMap_isLift_properties`: the three assertions together (Stacks 00LZ).

## References

* [Stacks Project, Tag 0AZ4](https://stacks.math.columbia.edu/tag/0AZ4)
* [Stacks Project, Tag 00LZ](https://stacks.math.columbia.edu/tag/00LZ)
-/

@[expose] public section

open CategoryTheory

universe u

/-- The target of an epimorphism of `R`-modules with finite source is finite. -/
private theorem finite_of_epi {R : Type u} [CommRing R] {A B : ModuleCat.{u} R} (f : A ⟶ B)
    [Epi f] [Module.Finite R A] : Module.Finite R B :=
  .of_surjective f.hom ((ModuleCat.epi_iff_surjective _).mp inferInstance)

/-- Over a Noetherian ring, the homology in degree `n` of a chain complex of `R`-modules whose
term `K.X n` is finite is finite. -/
theorem homology_finite_of_term_finite {R : Type u} [CommRing R] [IsNoetherianRing R]
    (K : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) [K.HasHomology n]
    [Module.Finite R (K.X n)] : Module.Finite R (K.homology n) := by
  have : Module.Finite R (K.cycles n) :=
    .of_injective (K.iCycles n).hom ((ModuleCat.mono_iff_injective _).mp inferInstance)
  exact finite_of_epi (K.homologyπ n)

/-- A finite module over a Noetherian ring has a finite free cover with finite kernel: an
epimorphism `π : R^k ↠ M` whose kernel is again a finite `R`-module. -/
@[sga "3 VIIB 1.4.3" "special case", sga "6 I 1.3" "partial"]
theorem exists_finite_free_cover {R : Type u} [CommRing R] [IsNoetherianRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] :
    ∃ (k : ℕ) (π : ModuleCat.of R (Fin k → R) ⟶ M),
      Epi π ∧ Module.Finite R (LinearMap.ker π.hom) := by
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := M)
  refine ⟨k, ModuleCat.ofHom (Fintype.linearCombination R s), ?_, ?_⟩
  · rw [ModuleCat.epi_iff_surjective, ← LinearMap.range_eq_top]
    exact (Fintype.range_linearCombination R s).trans hs
  · exact .of_injective (Submodule.subtype _) (Submodule.injective_subtype _)

/-! ### The finite-free syzygy iteration -/

section SyzygyConstruction

open CategoryTheory.Limits CategoryTheory.Category

/-- A bundled finite free cover of `M`: an epimorphism from a finite free module with
finite kernel. -/
structure FiniteFreeCover {R : Type u} [CommRing R] (M : ModuleCat.{u} R) where
  /-- the rank of the free module -/
  k : ℕ
  /-- the covering map -/
  π : ModuleCat.of R (Fin k → R) ⟶ M
  /-- the covering map is an epimorphism -/
  epi : Epi π
  /-- the kernel of the covering map is finite -/
  finKer : Module.Finite R (LinearMap.ker π.hom)

attribute [instance] FiniteFreeCover.epi FiniteFreeCover.finKer

/-- A choice of finite free cover of a finite module over a Noetherian ring. -/
@[sga "3 VIIB 1.4.3" "special case"]
noncomputable def chooseCover {R : Type u} [CommRing R] [IsNoetherianRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] : FiniteFreeCover M :=
  let h := exists_finite_free_cover M
  { k := h.choose
    π := h.choose_spec.choose
    epi := h.choose_spec.choose_spec.left
    finKer := h.choose_spec.choose_spec.right }

variable {R : Type u} [CommRing R]

/-- The categorical kernel of a finite free cover is a finite module. -/
theorem finite_kernel_cover {M : ModuleCat.{u} R} (c : FiniteFreeCover M) :
    Module.Finite R (kernel c.π : ModuleCat.{u} R) := by
  have : Module.Finite R (ModuleCat.of R (LinearMap.ker c.π.hom)) := c.finKer
  exact finite_of_epi (ModuleCat.kernelIsoKer c.π).inv

variable [IsNoetherianRing R]

/-- The sequence of finite modules in the syzygy iteration: `M₀ = N`, and
`Mₙ₊₁ = kernel (cover Mₙ)`, packaged together with their finiteness. -/
noncomputable def syz (N : ModuleCat.{u} R) (hN : Module.Finite R N) :
    ℕ → Σ' (M : ModuleCat.{u} R), Module.Finite R M
  | 0 => ⟨N, hN⟩
  | n + 1 =>
    let prev := syz N hN n
    haveI := prev.snd
    ⟨(kernel (chooseCover prev.fst).π : ModuleCat.{u} R), finite_kernel_cover _⟩

/-- The finite free cover used at stage `n` of the syzygy iteration. -/
noncomputable def syzCov (N : ModuleCat.{u} R) (hN : Module.Finite R N) (n : ℕ) :
    FiniteFreeCover (syz N hN n).1 :=
  haveI := (syz N hN n).snd
  chooseCover (syz N hN n).fst

/-- The `n`-th term of the resolution: the finite free module `Fin kₙ → R`. -/
noncomputable def syzX (N : ModuleCat.{u} R) (hN : Module.Finite R N) (n : ℕ) :
    ModuleCat.{u} R := ModuleCat.of R (Fin (syzCov N hN n).k → R)

/-- The differential `dₙ : Xₙ₊₁ ⟶ Xₙ`, namely `coverₙ₊₁` followed by the
kernel inclusion `kernel coverₙ ↪ Xₙ`. -/
noncomputable def syzD (N : ModuleCat.{u} R) (hN : Module.Finite R N) (n : ℕ) :
    syzX N hN (n+1) ⟶ syzX N hN n :=
  (syzCov N hN (n+1)).π ≫ kernel.ι (syzCov N hN n).π

set_option backward.isDefEq.respectTransparency false in
/-- Consecutive differentials of the syzygy iteration compose to zero. -/
theorem syzD_comp_syzD (N : ModuleCat.{u} R) (hN : Module.Finite R N) (n : ℕ) :
    syzD N hN (n+1) ≫ syzD N hN n = 0 := by
  simp [syzD]

/-- The finite-free chain complex assembled from the syzygy iteration. -/
noncomputable def syzComplex (N : ModuleCat.{u} R) (hN : Module.Finite R N) :
    ChainComplex (ModuleCat.{u} R) ℕ :=
  ChainComplex.of (syzX N hN) (syzD N hN) (syzD_comp_syzD N hN)

/-- The differential of `syzComplex` from degree `n + 1` to degree `n` is
`syzD`. -/
theorem syzComplex_d (N : ModuleCat.{u} R) (hN : Module.Finite R N) (n : ℕ) :
    (syzComplex N hN).d (n+1) n = syzD N hN n :=
  ChainComplex.of_d (syzX N hN) (syzD N hN) n

/-- Every term of `syzComplex` is projective, being finite free. -/
instance syzComplex_projective (N : ModuleCat.{u} R) (hN : Module.Finite R N) (n : ℕ) :
    Projective ((syzComplex N hN).X n) :=
  inferInstanceAs (Projective (ModuleCat.of R (Fin (syzCov N hN n).k → R)))

/-- For an epimorphism `q` onto `kernel p` and a monomorphism `j`, the short
complex with maps `q ≫ kernel.ι p` and `p ≫ j` is exact. -/
theorem exact_cover_dmono {C : Type*} [Category C] [Abelian C] {P A B Q : C}
    (p : P ⟶ A) (j : A ⟶ B) [Mono j] (q : Q ⟶ kernel p) [Epi q] :
    (ShortComplex.mk (q ≫ kernel.ι p) (p ≫ j)
      (by rw [Category.assoc, ← Category.assoc (kernel.ι p), kernel.condition,
        zero_comp, comp_zero])).Exact := by
  have htarget : (ShortComplex.mk (kernel.ι p) (p ≫ j)
      (by rw [← Category.assoc, kernel.condition, zero_comp])).Exact := by
    apply ShortComplex.exact_of_f_is_kernel
    refine KernelFork.IsLimit.ofι _ _
      (fun {W'} g' eq' => kernel.lift p g'
        ((cancel_mono j).mp (by rw [Category.assoc]; simpa using eq')))
      ?_ ?_
    · simp
    · intro W' g' eq' m hm
      exact (cancel_mono (kernel.ι p)).mp (by simpa using hm)
  let α : ShortComplex.mk (q ≫ kernel.ι p) (p ≫ j)
      (by rw [Category.assoc, ← Category.assoc (kernel.ι p), kernel.condition,
        zero_comp, comp_zero]) ⟶
        ShortComplex.mk (kernel.ι p) (p ≫ j)
          (by rw [← Category.assoc, kernel.condition, zero_comp]) :=
    { τ₁ := q, τ₂ := 𝟙 _, τ₃ := 𝟙 _ }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono α).mpr htarget

set_option backward.isDefEq.respectTransparency false in
/-- The syzygy complex is exact in every positive degree. -/
theorem syzComplex_exactAt_succ (N : ModuleCat.{u} R) (hN : Module.Finite R N) (n : ℕ) :
    (syzComplex N hN).ExactAt (n+1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n+1+1) (n+1) n (by simp) (by simp)]
  refine ShortComplex.exact_of_iso ?_ (exact_cover_dmono (syzCov N hN (n+1)).π
    (kernel.ι (syzCov N hN n).π) (syzCov N hN (n+2)).π)
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
  · simp only [Iso.refl_hom, id_comp, comp_id]
    exact syzComplex_d N hN (n+1)
  · simp only [Iso.refl_hom, id_comp, comp_id]
    exact syzComplex_d N hN n

set_option backward.isDefEq.respectTransparency false in
/-- The augmentation `π : syzComplex ⟶ single₀ N`, given by the cover `cover₀`. -/
noncomputable def syzAug (N : ModuleCat.{u} R) (hN : Module.Finite R N) :
    syzComplex N hN ⟶ (ChainComplex.single₀ (ModuleCat.{u} R)).obj N :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨(syzCov N hN 0).π, by
      rw [syzComplex_d N hN 0]
      change ((syzCov N hN 1).π ≫ kernel.ι (syzCov N hN 0).π) ≫ (syzCov N hN 0).π = 0
      rw [Category.assoc, kernel.condition, comp_zero]⟩

set_option backward.isDefEq.respectTransparency false in
/-- In degree `0` the augmentation `syzAug` is the cover `cover₀`. -/
theorem syzAug_f_zero (N : ModuleCat.{u} R) (hN : Module.Finite R N) :
    (syzAug N hN).f 0 = (syzCov N hN 0).π := by
  simp [syzAug, ChainComplex.toSingle₀Equiv]

set_option backward.isDefEq.respectTransparency false in
/-- The augmentation `syzAug` is a quasi-isomorphism: the syzygy complex resolves
`N`. -/
theorem syzAug_quasiIso (N : ModuleCat.{u} R) (hN : Module.Finite R N) :
    QuasiIso (syzAug N hN) := by
  rw [quasiIso_iff]
  intro n
  cases n with
  | zero =>
    rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
    · refine (ShortComplex.exact_and_epi_g_iff_of_iso ?_).mpr
        ⟨exact_cover_dmono (syzCov N hN 0).π (𝟙 _) (syzCov N hN 1).π, ?_⟩
      · exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
          (by simp only [Iso.refl_hom, id_comp, comp_id]; exact syzComplex_d N hN 0)
          (by simp only [Iso.refl_hom, id_comp, comp_id]; exact (syzAug_f_zero N hN).symm)
      · simpa only [comp_id] using (syzCov N hN 0).epi
    all_goals rfl
  | succ m =>
    rw [quasiIsoAt_iff_exactAt']
    · exact syzComplex_exactAt_succ N hN m
    · exact ChainComplex.exactAt_succ_single_obj _ _

/-- The finite-free projective resolution of `N`. -/
@[sga "6 VI 1.6"]
noncomputable def syzResolution (N : ModuleCat.{u} R) (hN : Module.Finite R N) :
    ProjectiveResolution N where
  complex := syzComplex N hN
  π := syzAug N hN
  quasiIso := syzAug_quasiIso N hN

/-- Every term of the syzygy resolution is a finite `R`-module. -/
theorem syzResolution_finite (N : ModuleCat.{u} R) (hN : Module.Finite R N) (n : ℕ) :
    Module.Finite R ((syzResolution N hN).complex.X n) :=
  inferInstanceAs (Module.Finite R (Fin (syzCov N hN n).k → R))

end SyzygyConstruction

/-- Over a Noetherian ring, a finite module `N` admits a projective resolution
all of whose terms are finite. -/
@[sga "2 VIII 1.2" "partial", sga "6 I 5.0" "partial", sga "6 VI 1.6" "partial"]
theorem exists_finite_projectiveResolution {R : Type u} [CommRing R] [IsNoetherianRing R]
    (N : ModuleCat.{u} R) [hN : Module.Finite R N] :
    ∃ P : ProjectiveResolution N, ∀ n : ℕ, Module.Finite R (P.complex.X n) :=
  ⟨syzResolution N hN, syzResolution_finite N hN⟩

/-- Let `R` be a Noetherian ring and let `M`, `N` be finite
`R`-modules. Then `Tor_p^R(M, N)` is a finite `R`-module for every `p`. -/
@[stacks 0AZ4,
  ega "III 6.5.13" "special case",
  ega "III 6.7.9" "special case",
  ega "III 7.4.7" "(i), special case"]
theorem tor_finite_of_noetherian (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M N : ModuleCat.{u} R) [Module.Finite R M] [Module.Finite R N] (p : ℕ) :
    Module.Finite R (((Tor (ModuleCat.{u} R) p).obj M).obj N) := by
  obtain ⟨P, hPfin⟩ := exists_finite_projectiveResolution N
  set F : ModuleCat.{u} R ⥤ ModuleCat.{u} R := (MonoidalCategory.tensoringLeft _).obj M
  have hiso : ((Tor (ModuleCat.{u} R) p).obj M).obj N ≅
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) p).obj
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex) :=
    P.isoLeftDerivedObj F p
  set K := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  have : Module.Finite R (K.X p) := by
    have := hPfin p
    exact inferInstanceAs (Module.Finite R (TensorProduct R M (P.complex.X p)))
  have : Module.Finite R ((HomologicalComplex.homologyFunctor (ModuleCat.{u} R)
      (ComplexShape.down ℕ) p).obj K) :=
    homology_finite_of_term_finite K p
  exact finite_of_epi hiso.inv

/-!
### Well-definedness of the maps induced on Tor by a lift

A *free resolution* of an `R`-module `M` is a projective resolution all of whose terms are free.
A chain map `α : F.complex ⟶ G.complex` between free resolutions of `M₁` and `M₂` *lifts* a
module map `φ : M₁ ⟶ M₂` when it is compatible with the augmentations, and it then induces maps
`H_i(F ⊗ N) ⟶ H_i(G ⊗ N)` for every `R`-module `N`, which do not depend on the lift since any
two lifts of `φ` are chain homotopic.
-/

@[expose] public section

open CategoryTheory

/-- A **free resolution** of an `R`-module `M`: a projective resolution all of whose
terms are free `R`-modules. -/
@[ega "0 11.4.1" "special case"]
structure FreeResolution {R : Type} [CommRing R] (M : ModuleCat R) where
  /-- The underlying projective resolution. -/
  proj : ProjectiveResolution M
  /-- Each term of the resolution is a free `R`-module. -/
  free : ∀ n, Module.Free R (proj.complex.X n)

namespace FreeResolution

variable {R : Type} [CommRing R]

/-- The underlying chain complex of the free resolution. -/
abbrev complex {M : ModuleCat R} (F : FreeResolution M) : ChainComplex (ModuleCat R) ℕ :=
  F.proj.complex

/-- The augmentation map of the free resolution. -/
@[ega "0 11.4.1" "special case"]
abbrev π {M : ModuleCat R} (F : FreeResolution M) :
    F.complex ⟶ (ChainComplex.single₀ (ModuleCat R)).obj M :=
  F.proj.π

/-- A chain map `α : F.complex ⟶ G.complex` **lifts** the module map `φ : M₁ ⟶ M₂` if it
is compatible with the augmentation maps, i.e. it induces `φ` on
`M₁ = H₀(F) → M₂ = H₀(G)`. -/
def IsLift {M₁ M₂ : ModuleCat R} (F : FreeResolution M₁) (G : FreeResolution M₂)
    (φ : M₁ ⟶ M₂) (α : F.complex ⟶ G.complex) : Prop :=
  α ≫ G.π = F.π ≫ (ChainComplex.single₀ (ModuleCat R)).map φ

/-- `α` lifts `φ` if and only if
`α ≫ G.π = F.π ≫ (ChainComplex.single₀ (ModuleCat R)).map φ`. -/
lemma isLift_iff {M₁ M₂ : ModuleCat R} {F : FreeResolution M₁} {G : FreeResolution M₂}
    {φ : M₁ ⟶ M₂} {α : F.complex ⟶ G.complex} :
    IsLift F G φ α ↔ α ≫ G.π = F.π ≫ (ChainComplex.single₀ (ModuleCat R)).map φ :=
  Iff.rfl

/-- The identity chain map `𝟙 F.complex` is a lift of the identity module map `𝟙 M`. -/
lemma IsLift.id {M : ModuleCat R} (F : FreeResolution M) : IsLift F F (𝟙 M) (𝟙 F.complex) := by
  simp [isLift_iff]

/-- Lifts compose: if `α` lifts `φ` and `β` lifts `ψ`, then `α ≫ β` lifts `φ ≫ ψ`. -/
lemma IsLift.comp {M₁ M₂ M₃ : ModuleCat R} {F : FreeResolution M₁} {G : FreeResolution M₂}
    {H : FreeResolution M₃} {φ : M₁ ⟶ M₂} {ψ : M₂ ⟶ M₃} {α : F.complex ⟶ G.complex}
    {β : G.complex ⟶ H.complex} (hα : IsLift F G φ α) (hβ : IsLift G H ψ β) :
    IsLift F H (φ ≫ ψ) (α ≫ β) := by
  rw [isLift_iff] at *
  rw [Category.assoc, hβ, ← Category.assoc, hα, Category.assoc, Functor.map_comp]

/-- The functor `_ ⊗ N` on chain complexes of `R`-modules. -/
noncomputable def tensorChainFunctor (N : ModuleCat R) :
    ChainComplex (ModuleCat R) ℕ ⥤ ChainComplex (ModuleCat R) ℕ :=
  (MonoidalCategory.tensorRight N).mapHomologicalComplex (ComplexShape.down ℕ)

/-- The map on `i`-th homology induced by tensoring a chain map of free resolutions with
`N`. When `α` lifts `φ : M₁ ⟶ M₂`, this is the map `H_i(F ⊗ N) ⟶ H_i(G ⊗ N)`. -/
noncomputable def torMap {M₁ M₂ : ModuleCat R} (F : FreeResolution M₁) (G : FreeResolution M₂)
    (N : ModuleCat R) (α : F.complex ⟶ G.complex) (i : ℕ) :
    ((tensorChainFunctor N).obj F.complex).homology i ⟶
      ((tensorChainFunctor N).obj G.complex).homology i :=
  HomologicalComplex.homologyMap ((tensorChainFunctor N).map α) i

/-- The induced map `torMap F F N (𝟙 F.complex) i` is the identity. -/
@[simp]
lemma torMap_id {M : ModuleCat R} (F : FreeResolution M) (N : ModuleCat R) (i : ℕ) :
    torMap F F N (𝟙 F.complex) i = 𝟙 _ := by
  simp [torMap]

/-- `torMap` is functorial in the chain map. -/
@[reassoc]
lemma torMap_comp {M₁ M₂ M₃ : ModuleCat R}
    (F : FreeResolution M₁) (G : FreeResolution M₂) (H : FreeResolution M₃)
    (N : ModuleCat R) (α : F.complex ⟶ G.complex) (β : G.complex ⟶ H.complex) (i : ℕ) :
    torMap F H N (α ≫ β) i = torMap F G N α i ≫ torMap G H N β i := by
  rw [torMap, Functor.map_comp, HomologicalComplex.homologyMap_comp]; rfl

/-- A canonical lift, on chain complexes, of the inverse of an isomorphism `φ`. -/
noncomputable def liftInv {M₁ M₂ : ModuleCat R} (F : FreeResolution M₁) (G : FreeResolution M₂)
    (φ : M₁ ⟶ M₂) [IsIso φ] : G.complex ⟶ F.complex :=
  ProjectiveResolution.lift (inv φ) G.proj F.proj

/-- The chain map `liftInv F G φ` lifts `inv φ`. -/
lemma isLift_liftInv {M₁ M₂ : ModuleCat R} (F : FreeResolution M₁) (G : FreeResolution M₂)
    (φ : M₁ ⟶ M₂) [IsIso φ] : IsLift G F (inv φ) (liftInv F G φ) :=
  ProjectiveResolution.lift_commutes (inv φ) G.proj F.proj

end FreeResolution

open FreeResolution in
/-- The induced map on homology is independent of the choice of the lift: two chain maps
`α, β : F.complex ⟶ G.complex` both lifting `φ : M₁ ⟶ M₂` induce equal maps
`H_i(F ⊗ N) ⟶ H_i(G ⊗ N)`. This is the first assertion of Stacks Tag 00LZ; the full lemma is
`FreeResolution.torMap_isLift_properties`. -/
theorem torMap_independent_of_lift {R : Type} [CommRing R] {M₁ M₂ : ModuleCat R}
    (F : FreeResolution M₁) (G : FreeResolution M₂) (N : ModuleCat R) {φ : M₁ ⟶ M₂}
    (α β : F.complex ⟶ G.complex) (hα : IsLift F G φ α) (hβ : IsLift F G φ β) (i : ℕ) :
    torMap F G N α i = torMap F G N β i :=
  (Functor.mapHomotopy (MonoidalCategory.tensorRight N)
    (ProjectiveResolution.liftHomotopy (P := F.proj) (Q := G.proj) φ α β hα hβ)).homologyMap_eq i

namespace FreeResolution

variable {R : Type} [CommRing R]

/-- If `α : F.complex ⟶ F.complex` lifts `𝟙 M`, then `torMap F F N α i = 𝟙 _`. -/
theorem torMap_eq_id_of_isLift {M : ModuleCat R} (F : FreeResolution M) (N : ModuleCat R)
    {α : F.complex ⟶ F.complex} (hα : IsLift F F (𝟙 M) α) (i : ℕ) :
    torMap F F N α i = 𝟙 _ := by
  rw [torMap_independent_of_lift F F N α (𝟙 F.complex) hα (IsLift.id F) i, torMap_id]

/-- If `α` lifts an isomorphism `φ`, then `torMap F G N α i` is an isomorphism. -/
theorem isIso_torMap_of_isLift {M₁ M₂ : ModuleCat R} (F : FreeResolution M₁)
    (G : FreeResolution M₂) (N : ModuleCat R) {φ : M₁ ⟶ M₂} [IsIso φ]
    {α : F.complex ⟶ G.complex} (hα : IsLift F G φ α) (i : ℕ) :
    IsIso (torMap F G N α i) := by
  have hγ := isLift_liftInv F G φ
  exact ⟨⟨torMap G F N (liftInv F G φ) i,
    by rw [← torMap_comp, torMap_eq_id_of_isLift F N (by simpa using hα.comp hγ)],
    by rw [← torMap_comp, torMap_eq_id_of_isLift G N (by simpa using hγ.comp hα)]⟩⟩

/-- Let `F` and `G` be free resolutions of `M₁` and `M₂`, let `φ : M₁ ⟶ M₂` and let `N` be a
module. Then the maps `H_i(α) : H_i(F ⊗ N) ⟶ H_i(G ⊗ N)` induced by chain maps `α` lifting `φ`
are independent of the choice of `α`; if `φ` is an isomorphism, so are all the maps `H_i(α)`;
and if `F = G` and `φ` is the identity, all the maps `H_i(α)` are the identity. -/
@[stacks 00LZ "All three assertions: independence of the lift, the isomorphism case, and the \
  identity case (`M₁ = M₂`, `F = G`, `φ = 𝟙`)."]
theorem torMap_isLift_properties {M₁ M₂ : ModuleCat R} (F : FreeResolution M₁)
    (G : FreeResolution M₂) (N : ModuleCat R) (φ : M₁ ⟶ M₂) :
    (∀ (α β : F.complex ⟶ G.complex), IsLift F G φ α → IsLift F G φ β → ∀ i,
        torMap F G N α i = torMap F G N β i) ∧
      (IsIso φ → ∀ (α : F.complex ⟶ G.complex), IsLift F G φ α → ∀ i,
        IsIso (torMap F G N α i)) ∧
      (∀ (α : F.complex ⟶ F.complex), IsLift F F (𝟙 M₁) α → ∀ i, torMap F F N α i = 𝟙 _) :=
  ⟨fun α β hα hβ i => torMap_independent_of_lift F G N α β hα hβ i,
    fun _ _ hα i => isIso_torMap_of_isLift F G N hα i,
    fun _ hα i => torMap_eq_id_of_isLift F N hα i⟩

end FreeResolution
