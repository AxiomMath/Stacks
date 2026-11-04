module

public import StacksCore.LinearAlgebra.Matrix.CommSemiring
public import StacksCore.Tactic.StacksAttribute
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import Mathlib.CategoryTheory.Abelian.Ext
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Module.StablyFree.Basic

/-!
# `Ext` groups of finite modules over a Noetherian ring are finite

(Stacks Tag 08YR.) Let $R$ be a Noetherian (commutative, unital) ring. Let $M$ and
$N$ be finite (i.e. finitely generated) $R$-modules. Then for every integer $i$, the
$R$-module $\operatorname{Ext}^i_R(M, N)$ is a finite $R$-module.

## Definitions

1. Finite (finitely generated) module: an $R$-module $M$ is finite if there are
   finitely many $m_1, \dots, m_n \in M$ generating $M$, equivalently there is a
   surjection $R^{\oplus n} \twoheadrightarrow M$. In Mathlib this is `Module.Finite`.

2. Noetherian ring: a commutative ring in which every ideal is finitely generated,
   equivalently satisfying the ascending chain condition on ideals. In Mathlib this is
   `IsNoetherianRing`.

3. Ext modules: $\operatorname{Ext}^i_R(M, N)$ is the $i$-th right derived functor of
   $\operatorname{Hom}_R(-, N)$ applied to $M$. In Mathlib, working in the abelian
   $R$-linear category `ModuleCat R` (which has enough projectives), the bifunctor
   `CategoryTheory.Ext R (ModuleCat R) i : (ModuleCat R)ᵒᵖ ⥤ (ModuleCat R) ⥤ ModuleCat R`
   sends `(M, N)` to an object of `ModuleCat R`, i.e. an $R$-module, namely
   $\operatorname{Ext}^i_R(M, N)$.
-/

@[expose] public section
-- needed file-wide: `dlin_dlin`, `cplx_d`, `dlin_exact` and `quasiIsoAt_piAug_zero` all
-- reason through `ModuleCat.of`/`ModuleCat.ofHom` around the free modules `Fin n → R`, and
-- their `rw`/`simp` steps only fire when defeq unfolds that bundling.
set_option backward.isDefEq.respectTransparency false

-- ## Implementation notes
--
-- - "Finite $R$-module" means finitely generated $R$-module (Stacks convention),
--   formalized as `Module.Finite R _`.
-- - The ring $R$ is commutative throughout.
-- - The phrase "for all $i$" ranges over all integers. For $i < 0$ the module
--   $\operatorname{Ext}^i_R(M, N)$ is $0$, hence trivially finite; the content of the
--   statement concerns $i \geq 0$. We therefore quantify over `i : ℕ`, which captures
--   the entire content (the $i < 0$ case is vacuous/trivial). Mathlib's `Ext` is
--   indexed by `ℕ` for exactly this reason.
--
-- ## Proof Sketch (for reference)
--
-- Since $R$ is Noetherian and $M$ is finite, $M$ admits a resolution by finite free
-- $R$-modules. Applying $\operatorname{Hom}_R(-, N)$ yields a complex whose degree-$i$
-- term is $\cong N^{\oplus n_i}$, a finite $R$-module. Each $\operatorname{Ext}^i_R(M,N)$
-- is a subquotient of $N^{\oplus n_i}$; over a Noetherian ring, submodules and quotients
-- of finite modules are finite.

open CategoryTheory

/-!
## Main results

* `exists_finiteFree_resolution`: a finite module over a Noetherian ring has a projective
  resolution by finite free modules, namely `FFRes.projRes`.
* `ext_finite_of_finiteFree_resolution`: given such a resolution of `M`, `Ext^i_R(M, N)` is
  finite for every finite `N`.
* `ext_finite_of_noetherian`: the combination of the two.
-/

/-! ## Finiteness transfer through `isoExt` -/

/-- If `N` is finite and the degree-`j` term of a chain complex `P` is finite and free,
then the degree-`j` term of the `Hom(P, N)` cochain complex is a finite `R`-module. -/
@[ega "0 7.8.1" "Hom_A(M, special case", ega "IV 2.5.8.1" "(ii), special case"]
theorem degterm_finite (R : Type) [CommRing R]
    (N : ModuleCat.{0} R) [Module.Finite R N]
    (P : ChainComplex (ModuleCat R) ℕ) (j : ℕ)
    [Module.Finite R (P.X j)] [Module.Free R (P.X j)] :
    Module.Finite R ((P.linearYonedaObj R N).X j) := by
  rw [ChainComplex.linearYonedaObj_X]
  have hfin : Module.Finite R (P.X j →ₗ[R] N) := Module.Finite.linearMap R R (P.X j) N
  exact Module.Finite.equiv (ModuleCat.homLinearEquiv (M := P.X j) (N := N)).symm

/-- If `K.X j` is finite over a Noetherian ring, then `K.homology j` is finite. -/
@[sga "4½ Rapport 4.11" "more general"]
theorem homology_finite (R : Type) [CommRing R] [IsNoetherianRing R]
    {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat R) c) (j : ι) [K.HasHomology j]
    [Module.Finite R (K.X j)] :
    Module.Finite R (K.homology j) := by
  have hXN : IsNoetherian R (K.X j) := isNoetherian_of_isNoetherianRing_of_finite R (K.X j)
  have hcyc : Module.Finite R (K.cycles j) :=
    Module.Finite.of_injective (ModuleCat.Hom.hom (K.iCycles j))
      ((ModuleCat.mono_iff_injective _).mp inferInstance)
  exact Module.Finite.of_surjective (ModuleCat.Hom.hom (K.homologyπ j))
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)

/-- Given a projective resolution `P` of `M` whose degree-`i` term is finite and free,
`Ext^i_R(M, N)` is finite for `N` finite over a Noetherian ring `R`. -/
theorem ext_finite_of_finiteFree_resolution (R : Type) [CommRing R] [IsNoetherianRing R]
    {M : ModuleCat.{0} R} (N : ModuleCat.{0} R) [Module.Finite R N]
    (P : ProjectiveResolution M) (i : ℕ)
    [Module.Finite R (P.complex.X i)] [Module.Free R (P.complex.X i)] :
    Module.Finite R (((Ext R (ModuleCat R) i).obj (Opposite.op M)).obj N) := by
  have hX : Module.Finite R ((P.complex.linearYonedaObj R N).X i) :=
    degterm_finite R N P.complex i
  have hH : Module.Finite R ((P.complex.linearYonedaObj R N).homology i) :=
    homology_finite R (P.complex.linearYonedaObj R N) i
  exact Module.Finite.equiv (P.isoExt i N).symm.toLinearEquiv

/-! ## Existence of a finite free resolution -/

namespace FFRes

variable (R : Type) [CommRing R] [IsNoetherianRing R]

/-- A finite free cover of `K`: a rank `n`, a surjection `R^n ↠ K`, and its surjectivity. -/
structure FFCover (K : ModuleCat.{0} R) where
  /-- The rank of the free module. -/
  n : ℕ
  /-- The covering map. -/
  p : (Fin n → R) →ₗ[R] K
  /-- The covering map is surjective. -/
  surj : Function.Surjective p

/-- A chosen finite free cover of a finite module. -/
noncomputable def mkFFCover (K : ModuleCat.{0} R) [Module.Finite R K] : FFCover R K :=
  ⟨(Module.Finite.exists_fin' R K).choose,
   (Module.Finite.exists_fin' R K).choose_spec.choose,
   (Module.Finite.exists_fin' R K).choose_spec.choose_spec⟩

/-- The iterated syzygy data: `syzygyData M m` is the `m`-th kernel in the tower of finite
free covers of `M`, together with its finiteness. -/
noncomputable def syzygyData (M : ModuleCat.{0} R) [Module.Finite R M] :
    ℕ → Σ' (K : ModuleCat.{0} R), Module.Finite R K
  | 0 => ⟨M, inferInstance⟩
  | (m+1) =>
    let prev := syzygyData M m
    haveI : Module.Finite R prev.fst := prev.snd
    ⟨ModuleCat.of R (LinearMap.ker (mkFFCover R prev.fst).p), inferInstance⟩

variable (M : ModuleCat.{0} R) [Module.Finite R M]

/-- The `m`-th syzygy module of `M`. -/
noncomputable def syzygy (m : ℕ) : ModuleCat.{0} R := (syzygyData R M m).fst
/-- Each syzygy module is finite. -/
instance instFinSyzygy (m : ℕ) : Module.Finite R (syzygy R M m) := (syzygyData R M m).snd
/-- The chosen finite free cover of the `m`-th syzygy module. -/
noncomputable def cov (m : ℕ) : FFCover R (syzygy R M m) := mkFFCover R (syzygy R M m)
/-- The degree-`m` term of the resolution: the finite free module covering the `m`-th
syzygy. -/
noncomputable def freeTerm (m : ℕ) : ModuleCat.{0} R := ModuleCat.of R (Fin (cov R M m).n → R)
/-- The covering surjection `freeTerm m ↠ syzygy m`. -/
noncomputable def pmap (m : ℕ) : (Fin (cov R M m).n → R) →ₗ[R] (syzygy R M m) :=
  (cov R M m).p
/-- The covering map `pmap m` is surjective. -/
theorem pmap_surj (m : ℕ) : Function.Surjective (pmap R M m) := (cov R M m).surj

/-- The differential `freeTerm (m+1) → freeTerm m`: cover the kernel of `pmap m` and
include. -/
noncomputable def dlin (m : ℕ) :
    (Fin (cov R M (m+1)).n → R) →ₗ[R] (Fin (cov R M m).n → R) :=
  (LinearMap.ker (pmap R M m)).subtype ∘ₗ (pmap R M (m+1))

/-- The image of `dlin m` lies in the kernel of `pmap m`. -/
theorem pmap_dlin (m : ℕ) (x : Fin (cov R M (m + 1)).n → R) :
    (pmap R M m) (dlin R M m x) = 0 :=
  (pmap R M (m+1) x).property

/-- Consecutive differentials compose to zero. -/
theorem dlin_dlin (m : ℕ) (y : Fin (cov R M (m + 2)).n → R) :
    dlin R M m (dlin R M (m+1) y) = 0 := by
  show (LinearMap.ker (pmap R M m)).subtype ((pmap R M (m+1)) (dlin R M (m+1) y)) = 0
  rw [pmap_dlin R M (m+1) y, map_zero]

/-- The chain complex of finite free modules built from the tower of syzygies. -/
noncomputable def cplx : ChainComplex (ModuleCat.{0} R) ℕ :=
  ChainComplex.of (fun n => freeTerm R M n) (fun n => ModuleCat.ofHom (dlin R M n))
    (fun n => by
      ext y
      simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
        ModuleCat.hom_zero, LinearMap.zero_apply]
      exact dlin_dlin R M n y)

/-- The differential of `cplx` in degree `n + 1` is `dlin n`. -/
theorem cplx_d (n : ℕ) :
    (cplx R M).d (n+1) n = ModuleCat.ofHom (dlin R M n) := by
  simp only [cplx, ChainComplex.of_d]

/-- The complex has homology in every degree. -/
instance instHasHom (n : ℕ) : (cplx R M).HasHomology n := by
  unfold cplx
  infer_instance

/-- Every term of the complex is finite. -/
instance instFinite (n : ℕ) : Module.Finite R ((cplx R M).X n) := by
  change Module.Finite R (Fin (cov R M n).n → R)
  infer_instance

/-- Every term of the complex is free. -/
instance instFree (n : ℕ) : Module.Free R ((cplx R M).X n) := by
  change Module.Free R (Fin (cov R M n).n → R)
  infer_instance

/-- Anything killed by `pmap m` is the image under `dlin m` of an element of the next term. -/
private theorem exists_dlin_eq_of_pmap_eq_zero (m : ℕ) (x : Fin (cov R M m).n → R)
    (hx : pmap R M m x = 0) : ∃ y, dlin R M m y = x := by
  obtain ⟨y, hy⟩ := pmap_surj R M (m+1) (⟨x, hx⟩ : LinearMap.ker (pmap R M m))
  exact ⟨y, congrArg Subtype.val hy⟩

/-- The complex is exact at the linear level: anything killed by `dlin n` is in the image of
`dlin (n+1)`. -/
theorem dlin_exact (n : ℕ) (x : Fin (cov R M (n + 1)).n → R) (hx : dlin R M n x = 0) :
    ∃ y, dlin R M (n+1) y = x :=
  exists_dlin_eq_of_pmap_eq_zero R M (n+1) x
    (Submodule.subtype_injective _ (hx.trans (map_zero _).symm))

/-- The complex is exact in every positive degree. -/
theorem cplx_exactAt_succ (n : ℕ) : (cplx R M).ExactAt (n+1) := by
  rw [HomologicalComplex.exactAt_iff' (cplx R M) (n+2) (n+1) n (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  intro x₂ hx₂
  have hg : ((cplx R M).sc' (n+2) (n+1) n).g = ModuleCat.ofHom (dlin R M n) := cplx_d R M n
  have hf : ((cplx R M).sc' (n+2) (n+1) n).f = ModuleCat.ofHom (dlin R M (n+1)) :=
    cplx_d R M (n+1)
  rw [hg] at hx₂
  simp only [ModuleCat.hom_ofHom] at hx₂
  obtain ⟨y, hy⟩ := dlin_exact R M n x₂ hx₂
  exact ⟨y, by rw [hf]; exact hy⟩

/-- The augmentation `freeTerm 0 ⟶ M`. -/
noncomputable def augMap : (cplx R M).X 0 ⟶ M := ModuleCat.ofHom (pmap R M 0)

/-- The augmentation kills the image of the first differential. -/
theorem augMap_cond : (cplx R M).d 1 0 ≫ augMap R M = 0 := by
  rw [cplx_d]
  ext x
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
    ModuleCat.hom_zero, LinearMap.zero_apply, augMap]
  exact pmap_dlin R M 0 x

/-- The augmentation as a map of chain complexes into `M` placed in degree `0`. -/
noncomputable def piAug : cplx R M ⟶ (ChainComplex.single₀ (ModuleCat R)).obj M :=
  (ChainComplex.toSingle₀Equiv (cplx R M) M).symm ⟨augMap R M, augMap_cond R M⟩

/-- The augmented complex is exact in degree `0`. -/
theorem aug_exact :
    (ShortComplex.mk ((cplx R M).d 1 0) (augMap R M) (augMap_cond R M)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro x₂ hx₂
  obtain ⟨y, hy⟩ := exists_dlin_eq_of_pmap_eq_zero R M 0 x₂ hx₂
  have hd : ((cplx R M).d 1 0) y = (dlin R M 0) y := by rw [cplx_d]; rfl
  exact ⟨y, hd.trans hy⟩

/-- The augmentation is an epimorphism. -/
instance augMap_epi : Epi (augMap R M) :=
  (ModuleCat.epi_iff_surjective _).mpr (pmap_surj R M 0)

/-- The augmentation is a quasi-isomorphism in degree `0`. -/
theorem quasiIsoAt_piAug_zero : QuasiIsoAt (piAug R M) 0 := by
  rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
  · exact ⟨aug_exact R M, augMap_epi R M⟩
  all_goals rfl

/-- The augmentation is a quasi-isomorphism. -/
@[ega "0 11.9.2" "special case"]
instance instQuasiIso : QuasiIso (piAug R M) := by
  rw [quasiIso_iff]
  intro i
  cases i with
  | zero => exact quasiIsoAt_piAug_zero R M
  | succ n =>
    rw [quasiIsoAt_iff_exactAt' (piAug R M) (n+1) (ChainComplex.exactAt_succ_single_obj M n)]
    exact cplx_exactAt_succ R M n

/-- Every term of the complex is projective, being finite free. -/
instance instProj (n : ℕ) : Projective ((cplx R M).X n) :=
  ModuleCat.projective_of_free (M := (cplx R M).X n) (Module.Free.chooseBasis R _)

/-- The finite free complex, with its augmentation, as a projective resolution of `M`. -/
noncomputable def projRes : ProjectiveResolution M :=
  { complex := cplx R M
    π := piAug R M }

end FFRes

/-- Over a Noetherian ring, every finite module has a projective resolution whose terms are
finite free modules. -/
@[ega "0 11.9.2" "special case",
  ega "IV 12.3.2" "(i), special case",
  sga "2 VIII 1.2" "partial",
  sga "4 IX 2.3" "partial",
  sga "6 I 5.0" "partial",
  sga "6 VI 1.6" "partial"]
theorem exists_finiteFree_resolution (R : Type) [CommRing R] [IsNoetherianRing R]
    (M : ModuleCat.{0} R) [Module.Finite R M] :
    ∃ P : ProjectiveResolution M,
      (∀ n, Module.Finite R (P.complex.X n)) ∧ (∀ n, Module.Free R (P.complex.X n)) :=
  ⟨FFRes.projRes R M, FFRes.instFinite R M, FFRes.instFree R M⟩

/-! ## Main theorem -/

/-- For a Noetherian ring `R` and finite `R`-modules `M`, `N`, each `Ext^i_R(M, N)` is a
finite `R`-module. -/
@[stacks 08YR, ega "III 4.5.1" "special case", sga "6 I 3.7" "Clause b), special case"]
theorem ext_finite_of_noetherian (R : Type) [CommRing R] [IsNoetherianRing R]
    (M N : ModuleCat.{0} R) [Module.Finite R M] [Module.Finite R N] (i : ℕ) :
    Module.Finite R (((Ext R (ModuleCat R) i).obj (Opposite.op M)).obj N) := by
  obtain ⟨P, hfin, hfree⟩ := exists_finiteFree_resolution R M
  exact ext_finite_of_finiteFree_resolution R N P i

-- ===== merged from StacksDraft.Ch10.Sec71.Tag00LV =====

/-!
# Annihilators of `Ext` groups

Fix a commutative ring $R$ and two $R$-modules $M$ and $N$.

Ext groups are defined via a free resolution $F_\bullet \to M$ of $M$: applying the
contravariant functor $\operatorname{Hom}_R(-, N)$ to the truncated complex
$\ldots \to F_2 \to F_1 \to F_0 \to 0$ yields a cochain complex, and
$\operatorname{Ext}^i_R(M, N)$ is its $i$-th cohomology (Stacks Tag 00LP, 00LT).
Each $\operatorname{Ext}^i_R(M, N)$ inherits a natural $R$-module structure (since $R$
is commutative, multiplication by $x \in R$ is an $R$-module endomorphism).

# Main Statement (Stacks Tag 00LV)

Let $x \in R$. If either $xN = 0$ or $xM = 0$, then $x$ annihilates
$\operatorname{Ext}^i_R(M, N)$ for every $i$; that is, $x \cdot \xi = 0$ for all
$\xi \in \operatorname{Ext}^i_R(M, N)$ and all $i$.

For $i < 0$ the statement is vacuous since $\operatorname{Ext}^i_R(M, N) = 0$, so we
index Ext by $i \in \mathbb{N}$ (the nonnegative degrees) without loss.

## Implementation notes

Mathlib's `Ext R C i : Cᵒᵖ ⥤ C ⥤ ModuleCat R` is the $R$-linear Ext functor on an
$R$-linear abelian category $C$ with enough projectives. Taking `C = ModuleCat R` realizes
the module Ext groups together with their canonical $R$-module structure. The hypothesis
$xN = 0$ is stated as `x ∈ Module.annihilator R N`.
-/

@[expose] public section


open CategoryTheory


universe u u₁ v₁ u₂ v₂

/-- The $i$-th Ext group $\operatorname{Ext}^i_R(M, N)$ as an $R$-module, computed via
the $R$-linear `Ext` functor on the category of $R$-modules. -/
noncomputable def extModule {R : Type u} [CommRing R] (M N : ModuleCat.{u} R) (i : ℕ) :
    ModuleCat.{u} R :=
  ((Ext R (ModuleCat R) i).obj (Opposite.op M)).obj N

/-- `extModule M N i` is the value of the `Ext` functor at `(M, N)`. -/
theorem extModule_def {R : Type u} [CommRing R] (M N : ModuleCat.{u} R) (i : ℕ) :
    extModule M N i = ((Ext R (ModuleCat R) i).obj (Opposite.op M)).obj N :=
  rfl

variable {R : Type u} [CommRing R]

/-- If `x` annihilates `P`, then `x • 𝟙 P = 0`. -/
theorem smul_id_eq_zero {P : ModuleCat.{u} R} {x : R} (hP : x ∈ Module.annihilator R P) :
    x • 𝟙 P = (0 : P ⟶ P) := by
  ext p; exact Module.mem_annihilator.mp hP p

/-- The `i`-th homology map of `r • 𝟙` on `Hom_R(P_•, N)` is `r • 𝟙`. -/
theorem homologyMap_smul_id {M : ModuleCat.{u} R} (N : ModuleCat.{u} R) (i : ℕ)
    (r : R) (P : ProjectiveResolution M) :
    HomologicalComplex.homologyMap (C := ModuleCat R)
        (r • 𝟙 (P.complex.linearYonedaObj R N)) i
      = r • 𝟙 (HomologicalComplex.homology (P.complex.linearYonedaObj R N) i) := by
  rw [HomologicalComplex.homologyMap]
  have h : (HomologicalComplex.shortComplexFunctor (ModuleCat R) (ComplexShape.up ℕ) i).map
      (r • 𝟙 (P.complex.linearYonedaObj R N))
      = r • 𝟙 ((HomologicalComplex.shortComplexFunctor (ModuleCat R) (ComplexShape.up ℕ) i).obj
          (P.complex.linearYonedaObj R N)) := by
    ext <;> simp <;> rfl
  rw [h, ShortComplex.homologyMap_smul, ShortComplex.homologyMap_id]
  rfl

/-- For `β : F ⟶ G` between additive functors and a projective resolution `P` of `X`,
`(NatTrans.leftDerived β n).app X` is the homology map of
`(β.mapHomologicalComplex _).app P.complex`, conjugated by `P.isoLeftDerivedObj`.
This is naturality of `isoLeftDerivedObj` in the functor. -/
theorem leftDerived_isoLeftDerivedObj_app
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    [Abelian C] [HasProjectiveResolutions C] [Abelian D]
    {F G : C ⥤ D} [F.Additive] [G.Additive] (β : F ⟶ G) (n : ℕ) {X : C}
    (P : ProjectiveResolution X) :
    (NatTrans.leftDerived β n).app X
      = (P.isoLeftDerivedObj F n).hom
        ≫ HomologicalComplex.homologyMap
            ((NatTrans.mapHomologicalComplex β (ComplexShape.down ℕ)).app P.complex) n
        ≫ (P.isoLeftDerivedObj G n).inv :=
  P.leftDerived_app_eq β n


/-- Let `Ψ` be the endomorphism of the complex `F(P_•)`, with `F = Hom_R(-, N)ᵒᵖ`,
corresponding to an endomorphism `f` of `Hom_R(P_•, N)`. Then the `unop` of the
`isoLeftDerivedObj`-conjugated homology map of `Ψ` is the `isoExt`-conjugated homology map
of `f`. -/
theorem isoExt_unop_conj_bridge {M : ModuleCat.{u} R} (N : ModuleCat.{u} R) (i : ℕ)
    (P : ProjectiveResolution M)
    (f : P.complex.linearYonedaObj R N ⟶ P.complex.linearYonedaObj R N)
    (Ψ : (((linearYoneda R (ModuleCat R)).obj N).rightOp.mapHomologicalComplex
        (ComplexShape.down ℕ)).obj P.complex ⟶
      (((linearYoneda R (ModuleCat R)).obj N).rightOp.mapHomologicalComplex
        (ComplexShape.down ℕ)).obj P.complex)
    (hΨ : (HomologicalComplex.opFunctor (ModuleCat R) (ComplexShape.down ℕ).symm).map f.op = Ψ) :
    ((P.isoLeftDerivedObj (((linearYoneda R (ModuleCat R)).obj N).rightOp) i).hom
          ≫ HomologicalComplex.homologyMap Ψ i
          ≫ (P.isoLeftDerivedObj (((linearYoneda R (ModuleCat R)).obj N).rightOp) i).inv).unop
      = (P.isoExt i N).hom ≫ HomologicalComplex.homologyMap f i ≫ (P.isoExt i N).inv := by
  rw [ProjectiveResolution.isoExt]
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv]
  rw [unop_comp, unop_comp, Iso.unop_hom, Iso.unop_inv, Category.assoc]
  let Φ := (((linearYoneda R (ModuleCat R)).obj N).rightOp.mapHomologicalComplex
      (ComplexShape.down ℕ)).obj P.complex
  have hcore : (HomologicalComplex.homologyMap Ψ i).unop
      = (Φ.homologyUnop i).inv ≫ HomologicalComplex.homologyMap f i ≫ (Φ.homologyUnop i).hom := by
    have nat := HomologicalComplex.homologyOp_hom_naturality f i (K := Φ.unop) (L := Φ.unop)
    rw [hΨ] at nat
    have nat2 := congrArg Quiver.Hom.unop nat
    simp only [unop_comp, Quiver.Hom.unop_op] at nat2
    have hunop : Φ.homologyUnop i = (Φ.unop.homologyOp i).unop := rfl
    rw [hunop, Iso.unop_hom, Iso.unop_inv]
    have hii : (Φ.unop.homologyOp i).inv.unop ≫ (Φ.unop.homologyOp i).hom.unop = 𝟙 _ := by
      rw [← unop_comp, Iso.hom_inv_id, unop_id]
    rw [← nat2, ← Category.assoc, hii]
    exact (Category.id_comp _).symm
  rw [hcore]
  simp only [Category.assoc]
  rfl

/-- Naturality of the comparison isomorphism `isoExt` with respect to multiplication by a
scalar `r` on the second argument. -/
theorem isoExt_smul_id_naturality {M : ModuleCat.{u} R} (N : ModuleCat.{u} R)
    (i : ℕ) (r : R) (P : ProjectiveResolution M) :
    ((Ext R (ModuleCat R) i).obj (Opposite.op M)).map (r • 𝟙 N)
      = (P.isoExt i N).hom
          ≫ HomologicalComplex.homologyMap (r • 𝟙 (P.complex.linearYonedaObj R N)) i
          ≫ (P.isoExt i N).inv := by
  have hExt : ((Ext R (ModuleCat R) i).obj (Opposite.op M)).map (r • 𝟙 N)
      = ((P.isoLeftDerivedObj (((linearYoneda R (ModuleCat R)).obj N).rightOp) i).hom
          ≫ HomologicalComplex.homologyMap
              ((NatTrans.mapHomologicalComplex
                (NatTrans.rightOp ((linearYoneda R (ModuleCat R)).map (r • 𝟙 N)))
                (ComplexShape.down ℕ)).app P.complex) i
          ≫ (P.isoLeftDerivedObj (((linearYoneda R (ModuleCat R)).obj N).rightOp) i).inv).unop := by
    have e1 : ((Ext R (ModuleCat R) i).obj (Opposite.op M)).map (r • 𝟙 N)
        = ((NatTrans.leftDerived
            (NatTrans.rightOp ((linearYoneda R (ModuleCat R)).map (r • 𝟙 N))) i).app M).unop := rfl
    rw [e1, leftDerived_isoLeftDerivedObj_app
      (NatTrans.rightOp ((linearYoneda R (ModuleCat R)).map (r • 𝟙 N))) i P]
  rw [hExt, isoExt_unop_conj_bridge N i P (r • 𝟙 (P.complex.linearYonedaObj R N))
    ((NatTrans.mapHomologicalComplex
      (NatTrans.rightOp ((linearYoneda R (ModuleCat R)).map (r • 𝟙 N)))
      (ComplexShape.down ℕ)).app P.complex) (by ext n : 1; rfl)]

/-- `Ext^i_R(M, -)` is an `R`-linear functor. -/
instance ext_obj_op_linear (M : ModuleCat.{u} R) (i : ℕ) :
    Functor.Linear R ((Ext R (ModuleCat R) i).obj (Opposite.op M)) := by
  rw [Functor.linear_iff]
  intro N r
  let P := ProjectiveResolution.of M
  rw [isoExt_smul_id_naturality N i r P, homologyMap_smul_id N i r P,
    Linear.smul_comp, Category.id_comp, Linear.comp_smul, Iso.hom_inv_id]

/-- The endomorphism of `extModule M N i` induced by `x • 𝟙 M` in the contravariant slot of
`Ext` is multiplication by `x`. It is stated with `(x • 𝟙 M).op`, since there is no
`Linear R (ModuleCat R)ᵒᵖ` instance. -/
theorem ext_map_op_smul_app (M N : ModuleCat.{u} R) (x : R) (i : ℕ) :
    ((Ext R (ModuleCat R) i).map ((x • 𝟙 M).op)).app N = x • 𝟙 (extModule M N i) := by
  let P := ProjectiveResolution.of M
  have hExt : ((Ext R (ModuleCat R) i).map ((x • 𝟙 M).op)).app N
      = ((P.isoLeftDerivedObj (((linearYoneda R (ModuleCat R)).obj N).rightOp) i).hom
          ≫ ((((linearYoneda R (ModuleCat R)).obj N).rightOp.mapHomologicalComplex
              (ComplexShape.down ℕ)) ⋙
              HomologicalComplex.homologyFunctor (ModuleCat R)ᵒᵖ (ComplexShape.down ℕ) i).map
                (x • 𝟙 P.complex)
          ≫ (P.isoLeftDerivedObj (((linearYoneda R (ModuleCat R)).obj N).rightOp) i).inv).unop := by
    have e1 : ((Ext R (ModuleCat R) i).map ((x • 𝟙 M).op)).app N
        = (((((linearYoneda R (ModuleCat R)).obj N).rightOp.leftDerived i)).map (x • 𝟙 M)).unop :=
            rfl
    rw [e1]
    congr 1
    have hnat := ProjectiveResolution.isoLeftDerivedObj_hom_naturality
      (x • 𝟙 M) P P (x • 𝟙 P.complex) (by simp [Linear.smul_comp, Linear.comp_smul])
      (((linearYoneda R (ModuleCat R)).obj N).rightOp) i
    rw [← Category.assoc, ← hnat, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  set Θ := ((((linearYoneda R (ModuleCat R)).obj N).rightOp.mapHomologicalComplex
      (ComplexShape.down ℕ))).map (x • 𝟙 P.complex)
  have hmid : ((((linearYoneda R (ModuleCat R)).obj N).rightOp.mapHomologicalComplex
      (ComplexShape.down ℕ)) ⋙
        HomologicalComplex.homologyFunctor (ModuleCat R)ᵒᵖ (ComplexShape.down ℕ) i).map
          (x • 𝟙 P.complex) = HomologicalComplex.homologyMap Θ i := rfl
  have hΘeq : (HomologicalComplex.opFunctor (ModuleCat R) (ComplexShape.down ℕ).symm).map
      ((x • 𝟙 (P.complex.linearYonedaObj R N)).op) = Θ := by
    ext n : 2
    apply Quiver.Hom.unop_inj
    simp only [HomologicalComplex.opFunctor_map_f, Quiver.Hom.unop_op]
    show (x • 𝟙 ((P.complex.linearYonedaObj R N).X n)) = ((linearYoneda R (ModuleCat R)).obj
        N).map ((x • 𝟙 (P.complex.X n)).op)
    simp only [linearYoneda]
    ext f
    simp [Linear.leftComp]
    rfl
  rw [hExt, hmid, isoExt_unop_conj_bridge N i P _ Θ hΘeq, homologyMap_smul_id N i x P,
    Linear.smul_comp, Category.id_comp, Linear.comp_smul, Iso.hom_inv_id]
  rfl

/-- **Stacks 00LV**.
If `x` annihilates `N` or `x` annihilates `M`, then `x` annihilates every Ext group
$\operatorname{Ext}^i_R(M, N)$. -/
@[stacks 00LV]
theorem ext_annihilated (M N : ModuleCat.{u} R) (x : R)
    (h : x ∈ Module.annihilator R N ∨ x ∈ Module.annihilator R M) (i : ℕ) :
    ∀ ξ : extModule M N i, x • ξ = 0 := by
  intro ξ
  show (x • 𝟙 (extModule M N i)).hom ξ = 0
  suffices hP : x • 𝟙 (extModule M N i) = 0 by rw [hP]; rfl
  have hmap : x • 𝟙 (extModule M N i)
      = ((Ext R (ModuleCat R) i).obj (Opposite.op M)).map (x • 𝟙 N) := by
    rw [Functor.map_smul, CategoryTheory.Functor.map_id]; rfl
  rcases h with hN | hM
  · rw [hmap, smul_id_eq_zero hN]
    rw [show (0 : N ⟶ N) = (0 : R) • 𝟙 N by rw [zero_smul]]
    rw [Functor.map_smul, zero_smul]
  · rw [← ext_map_op_smul_app M N x i, smul_id_eq_zero hM]
    rw [show (0 : M ⟶ M).op = ((0 : R) • 𝟙 M).op by rw [zero_smul]]
    rw [ext_map_op_smul_app M N (0 : R) i, zero_smul]

-- ===== merged from StacksDraft.Ch10.Sec77.Tag0G8T =====

/-!
# Projectivity of a finite module over a Noetherian ring from vanishing of `Ext¹`

Let $R$ be a Noetherian (commutative) ring and let $P$ be a finite $R$-module. If
$\operatorname{Ext}^1_R(P, M) = 0$ for every finite $R$-module $M$, then $P$ is a projective
$R$-module. This is Stacks tag 0G8T (Lemma 10.77.3). The content is that over a Noetherian
ring it suffices to test the vanishing of $\operatorname{Ext}^1_R(P, -)$ against *finite*
modules $M$ only, rather than against all $R$-modules.

## Conventions

An $R$-module $M$ is *finite* if it is finitely generated, i.e. there is a surjection
$R^{\oplus n} \to M$ for some $n$; in Mathlib this is `Module.Finite R M`. A ring $R$ is
*Noetherian* if every ideal is finitely generated, equivalently $R$ satisfies the ascending
chain condition on ideals; in Mathlib this is `IsNoetherianRing R`. A standard consequence is
that submodules of finite modules over a Noetherian ring are again finite.

An $R$-module $P$ is *projective* if $\operatorname{Hom}_R(P, -)$ is exact, equivalently if
$P$ is a direct summand of a free module, equivalently if $P$ satisfies the lifting property
against surjections; in Mathlib this is `Module.Projective R P`.

$\operatorname{Ext}^1_R(P, M)$, the first right derived functor of
$\operatorname{Hom}_R(-, M)$, is taken as a categorical `Ext` group of the abelian category
`ModuleCat R`, namely `CategoryTheory.Abelian.Ext (ModuleCat.of R P) (ModuleCat.of R M) 1`,
the additive group of degree-$1$ extensions. Its vanishing is expressed as that group being a
`Subsingleton`.

## Outline of the argument

Choose a surjection $R^{\oplus n} \twoheadrightarrow P$ and let $M$ be its kernel. Since $R$
is Noetherian and $R^{\oplus n}$ is finite, $M$ is finite too, so by hypothesis
$\operatorname{Ext}^1_R(P, M) = 0$ and the short exact sequence
$0 \to M \to R^{\oplus n} \to P \to 0$ splits. Hence $P$ is a direct summand of the free
module $R^{\oplus n}$, and therefore projective.
-/

@[expose] public section

open CategoryTheory

/-- If the extension class of a short exact sequence in an abelian category vanishes,
then the sequence splits. -/
private lemma splitting_of_extClass_eq_zero {C : Type*} [Category C] [Abelian C]
    [CategoryTheory.HasExt C] {S : ShortComplex C}
    (hS : S.ShortExact) (h0 : hS.extClass = 0) : Nonempty S.Splitting := by
  obtain ⟨x₂, hx₂⟩ := Abelian.Ext.contravariant_sequence_exact₁ hS S.X₁
    (Abelian.Ext.mk₀ (𝟙 S.X₁)) (n₁ := 1) (by norm_num)
    (by rw [h0, Abelian.Ext.zero_comp])
  set r : S.X₂ ⟶ S.X₁ := Abelian.Ext.homEquiv₀ x₂ with hr
  have hx₂' : x₂ = Abelian.Ext.mk₀ r := by
    rw [hr, ← Abelian.Ext.homEquiv₀_symm_apply, Equiv.symm_apply_apply]
  rw [hx₂', Abelian.Ext.mk₀_comp_mk₀] at hx₂
  have hfr : S.f ≫ r = 𝟙 S.X₁ := by
    have := congrArg Abelian.Ext.homEquiv₀ hx₂
    rwa [← Abelian.Ext.homEquiv₀_symm_apply, ← Abelian.Ext.homEquiv₀_symm_apply,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
  exact ⟨ShortComplex.Splitting.ofExactOfRetraction S hS.exact r hfr hS.epi_g⟩

/-- Stacks tag 0G8T (Lemma 10.77.3): a finite module `P` over a Noetherian ring `R` is
projective as soon as `Ext¹_R(P, M)` vanishes for every finite `R`-module `M`. -/
@[stacks 0G8T, ega "0 17.2.1" "n = 0", ega "0 17.2.8" "special case"]
theorem projective_of_ext_one_eq_zero {R : Type} [CommRing R] [IsNoetherianRing R]
    (P : Type) [AddCommGroup P] [Module R P] [Module.Finite R P]
    (h : ∀ (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M],
      Subsingleton (Abelian.Ext (C := ModuleCat R) (ModuleCat.of R P) (ModuleCat.of R M) 1)) :
    Module.Projective R P := by
  -- Choose a surjection `f : (Fin n → R) → P` from a finite free module.
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R P
  -- The kernel `K` of `f`.
  set K : Submodule R (Fin n → R) := LinearMap.ker f
  -- `K` is a finite module over the Noetherian ring `R`.
  have : Module.Finite R K := by infer_instance
  -- Build the short complex `0 → K → (Fin n → R) → P → 0` in `ModuleCat R`.
  set g : ModuleCat.of R (Fin n → R) ⟶ ModuleCat.of R P := ModuleCat.ofHom f with hg
  set ι : ModuleCat.of R K ⟶ ModuleCat.of R (Fin n → R) :=
    ModuleCat.ofHom K.subtype with hι
  have hzero : ι ≫ g = 0 := by
    apply ModuleCat.hom_ext
    ext x
    simp [hι, hg]
  set S : ShortComplex (ModuleCat R) := ShortComplex.mk ι g hzero with hS_def
  -- `S` is short exact.
  have hmono : Mono S.f := by
    rw [hS_def, ModuleCat.mono_iff_injective]
    simp [hι]
  have hepi : Epi S.g := by
    rw [hS_def, ModuleCat.epi_iff_surjective]
    simpa [hg] using hf
  have hexact : S.Exact := by
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    apply le_antisymm
    · rintro x ⟨y, rfl⟩
      simp
    · intro x hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hSE : S.ShortExact := ShortComplex.ShortExact.mk hexact
  -- The extension class lives in `Ext (of P) (of K) 1`, which is subsingleton, so it is 0.
  have hsub : Subsingleton (Abelian.Ext (C := ModuleCat R) S.X₃ S.X₁ 1) := h K
  have h0 : hSE.extClass = 0 := Subsingleton.elim _ _
  -- Hence the sequence splits.
  obtain ⟨split⟩ := splitting_of_extClass_eq_zero hSE h0
  -- The categorical section gives a linear section of `f`.
  set i : P →ₗ[R] (Fin n → R) := (split.s).hom with hi
  have hfi : f ∘ₗ i = LinearMap.id := by
    refine LinearMap.ext fun x => ?_
    have hx := LinearMap.congr_fun
      (congrArg (fun m => (ModuleCat.Hom.hom m)) split.s_g) x
    simp only [hi, ModuleCat.hom_comp, LinearMap.comp_apply,
      ModuleCat.hom_id, LinearMap.id_coe, id_eq] at hx ⊢
    exact hx
  -- `P` is a retract of the free module, hence projective.
  exact Module.Projective.of_split i f hfi
