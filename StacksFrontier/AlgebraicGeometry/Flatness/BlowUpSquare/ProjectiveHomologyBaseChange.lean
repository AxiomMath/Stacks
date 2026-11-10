module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.LocalProperties.Projective
public import Mathlib.RingTheory.LocalRing.Module
public import StacksFrontier.AlgebraicGeometry.FiberRank.Basic
public import StacksFrontier.Homology.Eta.Cohomology
public import StacksFrontier.Homology.Eta.Complex
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Homology.HomComplex.Evaluation.TensorHomRestrictKFlat
public import StacksFrontier.Homology.TorAmplitude.FaithfullyFlat
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Cohomology of complexes of projective modules under base change

Let `R` be a ring and `P^•` a bounded above complex of projective `R`-modules whose cohomology
modules are projective.  Then `P^•` is homotopy equivalent to the complex of its cohomology
modules with zero differentials, so the cohomology of `F(P^•)` is `F(H^n(P^•))` for every
additive functor `F`; in particular the cohomology of `P^•` commutes with every base change.  If
the terms of `P^•` are finite projective, its cohomology is finite projective as soon as it is
free at every maximal ideal: descending through the degrees, the cokernel of each differential
is finite projective, so the cohomology is a direct summand of a finitely presented module.

For the décalage `η_f M^•` of a complex of `f`-torsion-free modules whose cohomology has no
`f`-torsion, More on Algebra, Tag 0F7P identifies the cohomology of `η_f M^•` with that of
`M^•`.  Finally, the fibre rank at a point `z` of `Spec B` of the sheaf associated with
`B ⊗_A P`, for `P` finite projective over `A`, is the fibre rank of `P̃` at the image of `z`.

## Main results

* `CochainComplex.mapHomologyIsoOfProjective`: the cohomology of a bounded above complex of
  projectives with projective cohomology commutes with every additive functor.
* `CochainComplex.finite_projective_homology_of_free_localization`: a bounded above complex of
  finite projective modules whose cohomology is free at every maximal ideal has finite
  projective cohomology.
* `Stacks.Decalage.Cohomology.nonempty_etaHomologyLinearEquiv_of_isSMulRegular`: the décalage of
  a complex of `f`-torsion-free modules whose cohomology has no `f`-torsion has the same
  cohomology, by Tag 0F7P.
* `AlgebraicGeometry.fiberRank_tilde_extendScalars`: fibre ranks of base changes of finite
  projective modules.

## References

* [Stacks Project, Tag 0F7P](https://stacks.math.columbia.edu/tag/0F7P)
* [Stacks Project, Tag 0GTA](https://stacks.math.columbia.edu/tag/0GTA)
-/

@[expose] public noncomputable section

open CategoryTheory Limits
open scoped TensorProduct

universe u

namespace CochainComplex

variable {C D : Type*} [Category* C] [Abelian C] [Category* D] [Abelian D]

/-- The complex of the cohomology objects of `K`, with zero differentials. -/
def homologyComplex (K : CochainComplex C ℤ) : CochainComplex C ℤ where
  X i := K.homology i
  d _ _ := 0

/-- The term of `K.homologyComplex` in degree `i` is the cohomology object `K.homology i`. -/
@[simp] lemma homologyComplex_X (K : CochainComplex C ℤ) (i : ℤ) :
    K.homologyComplex.X i = K.homology i := rfl

/-- The differentials of `K.homologyComplex` are zero. -/
@[simp] lemma homologyComplex_d (K : CochainComplex C ℤ) (i j : ℤ) :
    K.homologyComplex.d i j = 0 := rfl

/-- The terms of `K.homologyComplex` are projective when the cohomology objects of `K` are. -/
instance (K : CochainComplex C ℤ) [∀ i, Projective (K.homology i)] (i : ℤ) :
    Projective (K.homologyComplex.X i) :=
  inferInstanceAs (Projective (K.homology i))

/-- When every cohomology object is projective, the map from the complex of cohomology objects
to `K` given by a choice of sections of the projections from the cycles onto the cohomology. -/
def homologyComplexSection (K : CochainComplex C ℤ) [∀ i, Projective (K.homology i)] :
    K.homologyComplex ⟶ K where
  f i := Projective.factorThru (𝟙 (K.homology i)) (K.homologyπ i) ≫ K.iCycles i
  comm' i j _ := by
    rw [homologyComplex_d, zero_comp, Category.assoc, HomologicalComplex.iCycles_d, comp_zero]

/-- The chosen map from the complex of cohomology objects is a quasi-isomorphism. -/
lemma quasiIso_homologyComplexSection (K : CochainComplex C ℤ)
    [∀ i, Projective (K.homology i)] : QuasiIso K.homologyComplexSection := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hπ := K.homologyComplex.isIso_homologyπ (i - 1) i (by simp) rfl
  have hι := K.homologyComplex.isIso_iCycles i (i + 1) (by simp) rfl
  have heq : K.homologyComplex.homologyπ i ≫ HomologicalComplex.homologyMap
      K.homologyComplexSection i = K.homologyComplex.iCycles i := by
    rw [HomologicalComplex.homologyπ_naturality]
    have hc : HomologicalComplex.cyclesMap K.homologyComplexSection i =
        K.homologyComplex.iCycles i ≫ Projective.factorThru (𝟙 (K.homology i)) (K.homologyπ i) := by
      apply (cancel_mono (K.iCycles i)).mp
      rw [HomologicalComplex.cyclesMap_i]
      exact (Category.assoc _ _ _).symm
    rw [hc, Category.assoc]
    exact (congrArg (K.homologyComplex.iCycles i ≫ ·)
      (Projective.factorThru_comp (𝟙 (K.homology i)) (K.homologyπ i))).trans
      (Category.comp_id _)
  have : IsIso (K.homologyComplex.homologyπ i ≫
      HomologicalComplex.homologyMap K.homologyComplexSection i) := heq ▸ hι
  exact IsIso.of_isIso_comp_left (K.homologyComplex.homologyπ i) _

/-- **The cohomology of a bounded above complex of projectives with projective cohomology commutes
with every additive functor.**  Such a complex is K-projective, as is the complex of its
cohomology objects, so the quasi-isomorphism between them is a homotopy equivalence, which every
additive functor preserves. -/
def mapHomologyIsoOfProjective (K : CochainComplex C ℤ) (b : ℤ) [K.IsStrictlyLE b]
    [∀ i, Projective (K.X i)] [∀ i, Projective (K.homology i)] (F : C ⥤ D) [F.Additive]
    (n : ℤ) :
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homology n ≅ F.obj (K.homology n) := by
  have : K.homologyComplex.IsStrictlyLE b := by
    rw [isStrictlyLE_iff]
    intro i hi
    exact (K.sc i).isZero_homology_of_isZero_X₂ (K.isZero_of_isStrictlyLE b i hi)
  have := K.isKProjective_of_projective b
  have := K.homologyComplex.isKProjective_of_projective b
  have := K.quasiIso_homologyComplexSection
  let h := ((IsKProjective.quasiIso_iff K.homologyComplexSection).mp this).choose
  let L := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K.homologyComplex
  have hd (i j : ℤ) : L.d i j = 0 := F.map_zero _ _
  exact ((F.mapHomotopyEquiv h).toHomologyIso n).symm ≪≫
    (L.isoHomologyπ (n - 1) n (by simp) (hd _ _)).symm ≪≫ L.iCyclesIso n (n + 1) (by simp) (hd _ _)

end CochainComplex

namespace Module

variable {R : Type u} [CommRing R] {X₀ X₁ X₂ : Type u} [AddCommGroup X₀] [Module R X₀]
  [AddCommGroup X₁] [Module R X₁] [AddCommGroup X₂] [Module R X₂]

/-- A submodule of a projective module with projective quotient is projective, being a direct
summand. -/
theorem projective_submodule_of_projective_quotient [Module.Projective R X₂]
    (N : Submodule R X₂) (hQ : Module.Projective R (X₂ ⧸ N)) : Module.Projective R N := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property N.mkQ LinearMap.id
    (Submodule.mkQ_surjective _)
  let ρ : X₂ →ₗ[R] N :=
    (LinearMap.id - s ∘ₗ N.mkQ).codRestrict N fun x => by
      rw [← Submodule.Quotient.mk_eq_zero]
      change N.mkQ (x - s (N.mkQ x)) = 0
      rw [map_sub, ← LinearMap.comp_apply _ s, hs, LinearMap.id_apply, sub_self]
  have hρ : ρ ∘ₗ N.subtype = LinearMap.id := by
    ext ⟨y, hy⟩
    change y - s (N.mkQ y) = y
    rw [show N.mkQ y = 0 from (Submodule.Quotient.mk_eq_zero _).mpr hy, map_zero, sub_zero]
  exact Module.Projective.of_split N.subtype ρ hρ

/-- The cohomology `ker g ⧸ im f` of a complex `X₀ → X₁ → X₂` injects into `X₁ ⧸ im f`. -/
theorem injective_mapQ_subtype_ker (f : X₀ →ₗ[R] X₁) (g : X₁ →ₗ[R] X₂) :
    Function.Injective (((LinearMap.range f).submoduleOf (LinearMap.ker g)).mapQ
      (LinearMap.range f) (LinearMap.ker g).subtype fun _ h => h) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  induction z using Submodule.Quotient.induction_on with
  | H x =>
    have hz' : (Submodule.Quotient.mk (x : X₁) : X₁ ⧸ LinearMap.range f) = 0 := hz
    exact (Submodule.Quotient.mk_eq_zero _).mpr
      ((Submodule.Quotient.mk_eq_zero (LinearMap.range f)).mp hz')

/-- For a complex `X₀ → X₁ → X₂`, the sequence `ker g ⧸ im f → X₁ ⧸ im f → im g` is exact. -/
theorem exact_mapQ_subtype_ker_liftQ_rangeRestrict (f : X₀ →ₗ[R] X₁) (g : X₁ →ₗ[R] X₂)
    (hfg : g ∘ₗ f = 0) :
    Function.Exact (((LinearMap.range f).submoduleOf (LinearMap.ker g)).mapQ
      (LinearMap.range f) (LinearMap.ker g).subtype fun _ h => h)
      ((LinearMap.range f).liftQ g.rangeRestrict
        (by rwa [LinearMap.ker_rangeRestrict, LinearMap.range_le_ker_iff])) := by
  intro y
  induction y using Submodule.Quotient.induction_on with
  | H x =>
    refine ⟨fun hx => ⟨Submodule.Quotient.mk ⟨x, congrArg Subtype.val hx⟩, rfl⟩, ?_⟩
    rintro ⟨z, hz⟩
    rw [← hz]
    induction z using Submodule.Quotient.induction_on with
    | H z => exact Subtype.ext z.2

/-- **The descending step.**  Let `X₀ → X₁ → X₂` be a complex with `X₀`, `X₁` finite, `X₁`, `X₂`
projective and `X₂ ⧸ im g` projective.  If its cohomology is free at every maximal ideal, then
the cohomology is finite projective and so is `X₁ ⧸ im f`: the image of `g` is a direct summand
of `X₂`, so `X₁ ⧸ im f` is the direct sum of the cohomology and the image of `g`. -/
theorem projective_homology_and_quotient_of_free_localization
    (f : X₀ →ₗ[R] X₁) (g : X₁ →ₗ[R] X₂) (hfg : g ∘ₗ f = 0)
    [Module.Finite R X₀] [Module.Finite R X₁] [Module.Projective R X₁] [Module.Projective R X₂]
    (hQ : Module.Projective R (X₂ ⧸ LinearMap.range g))
    (hH : ∀ (m : Ideal R) (_ : m.IsMaximal), Module.Free (Localization.AtPrime m)
      (LocalizedModule m.primeCompl
        (LinearMap.ker g ⧸ (LinearMap.range f).submoduleOf (LinearMap.ker g)))) :
    (Module.Finite R (LinearMap.ker g ⧸ (LinearMap.range f).submoduleOf (LinearMap.ker g)) ∧
      Module.Projective R (LinearMap.ker g ⧸ (LinearMap.range f).submoduleOf (LinearMap.ker g))) ∧
      Module.Projective R (X₁ ⧸ LinearMap.range f) := by
  set H := LinearMap.ker g ⧸ (LinearMap.range f).submoduleOf (LinearMap.ker g)
  have := projective_submodule_of_projective_quotient (LinearMap.range g) hQ
  let e : X₁ ⧸ LinearMap.range f →ₗ[R] LinearMap.range g :=
    (LinearMap.range f).liftQ g.rangeRestrict
      (by rwa [LinearMap.ker_rangeRestrict, LinearMap.range_le_ker_iff])
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property g.rangeRestrict LinearMap.id
    g.surjective_rangeRestrict
  let l : LinearMap.range g →ₗ[R] X₁ ⧸ LinearMap.range f := (LinearMap.range f).mkQ ∘ₗ σ
  have hl : e ∘ₗ l = LinearMap.id := by
    ext y
    exact congrArg Subtype.val (LinearMap.congr_fun hσ y)
  let ι : H →ₗ[R] X₁ ⧸ LinearMap.range f :=
    ((LinearMap.range f).submoduleOf (LinearMap.ker g)).mapQ (LinearMap.range f)
      (LinearMap.ker g).subtype fun _ h => h
  have hι : Function.Injective ι := injective_mapQ_subtype_ker f g
  have hexact : Function.Exact ι e := exact_mapQ_subtype_ker_liftQ_rangeRestrict f g hfg
  have : Module.FinitePresentation R X₁ := Module.finitePresentation_of_projective R X₁
  have : Module.FinitePresentation R (X₁ ⧸ LinearMap.range f) :=
    Module.finitePresentation_of_surjective (LinearMap.range f).mkQ
      (Submodule.mkQ_surjective _) (by
        rw [Submodule.ker_mkQ, LinearMap.range_eq_map]
        exact Module.Finite.fg_top.map f)
  have : Module.FinitePresentation R H :=
    Module.finitePresentation_of_split_exact ι e l hl hι hexact
  have hHproj : Module.Projective R H :=
    Module.projective_of_localization_maximal fun m hm => by
      have := hH m hm
      infer_instance
  obtain ⟨eq, -, -⟩ := hexact.splitSurjectiveEquiv hι ⟨l, hl⟩
  exact ⟨⟨inferInstance, hHproj⟩, .of_equiv eq.symm⟩

end Module

namespace CochainComplex

variable {R : Type u} [CommRing R]

/-- The cohomology of a complex of modules is the explicit quotient `ker dⁱ / im dⁱ⁻¹`. -/
def homologyLinearEquiv (K : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    K.homology (i + 1) ≃ₗ[R] (LinearMap.ker (K.d (i + 1) (i + 1 + 1)).hom ⧸
      (LinearMap.range (K.d i (i + 1)).hom).submoduleOf
        (LinearMap.ker (K.d (i + 1) (i + 1 + 1)).hom)) :=
  (K.homologyIsoSc' i (i + 1) (i + 1 + 1) (by simp) (by simp) ≪≫
    (K.sc' i (i + 1) (i + 1 + 1)).moduleCatHomologyIso).toLinearEquiv ≪≫ₗ
    Submodule.quotEquivOfEq _ _ (by
      ext ⟨x, hx⟩
      exact ⟨fun ⟨y, hy⟩ => ⟨y, congrArg Subtype.val hy⟩, fun ⟨y, hy⟩ => ⟨y, Subtype.ext hy⟩⟩)

/-- If the cokernel of `dⁱ⁺¹` is projective, then the explicit cohomology `ker dⁱ⁺¹ / im dⁱ` of a
complex of finite projective modules free at every maximal ideal is finite projective, and so is
the cokernel of `dⁱ`. -/
theorem finite_projective_homology_and_quotient_of_free_localization
    (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : ∀ i, Module.Finite R (K.X i) ∧ Module.Projective R (K.X i))
    (hH : ∀ i (m : Ideal R) (_ : m.IsMaximal), Module.Free (Localization.AtPrime m)
      (LocalizedModule m.primeCompl (K.homology i))) (i : ℤ)
    (hQ : Module.Projective R (K.X (i + 1 + 1) ⧸ LinearMap.range (K.d (i + 1) (i + 1 + 1)).hom)) :
    (Module.Finite R (LinearMap.ker (K.d (i + 1) (i + 1 + 1)).hom ⧸
        (LinearMap.range (K.d i (i + 1)).hom).submoduleOf
          (LinearMap.ker (K.d (i + 1) (i + 1 + 1)).hom)) ∧
      Module.Projective R (LinearMap.ker (K.d (i + 1) (i + 1 + 1)).hom ⧸
        (LinearMap.range (K.d i (i + 1)).hom).submoduleOf
          (LinearMap.ker (K.d (i + 1) (i + 1 + 1)).hom))) ∧
      Module.Projective R (K.X (i + 1) ⧸ LinearMap.range (K.d i (i + 1)).hom) := by
  have := (hK i).1
  have := (hK (i + 1)).1
  have := (hK (i + 1)).2
  have := (hK (i + 1 + 1)).2
  refine Module.projective_homology_and_quotient_of_free_localization (K.d i (i + 1)).hom
    (K.d (i + 1) (i + 1 + 1)).hom (by rw [← ModuleCat.hom_comp, K.d_comp_d, ModuleCat.hom_zero]) hQ
    fun m hm => ?_
  have := hH (i + 1) m hm
  exact Module.Free.of_equiv (IsLocalizedModule.mapEquiv m.primeCompl
    (LocalizedModule.mkLinearMap m.primeCompl _) (LocalizedModule.mkLinearMap m.primeCompl _)
    (Localization.AtPrime m) (K.homologyLinearEquiv i))

/-- **The cohomology of a bounded above complex of finite projective modules which is free at
every maximal ideal is finite projective.**  Descending induction on the degree shows that the
cokernel of every differential is projective, by
`Module.projective_homology_and_quotient_of_free_localization`. -/
theorem finite_projective_homology_of_free_localization (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (b : ℤ) [K.IsStrictlyLE b] (hK : ∀ i, Module.Finite R (K.X i) ∧ Module.Projective R (K.X i))
    (hH : ∀ i (m : Ideal R) (_ : m.IsMaximal), Module.Free (Localization.AtPrime m)
      (LocalizedModule m.primeCompl (K.homology i))) (n : ℤ) :
    Module.Finite R (K.homology n) ∧ Module.Projective R (K.homology n) := by
  have step := K.finite_projective_homology_and_quotient_of_free_localization hK hH
  have key : ∀ j i : ℤ, i + 1 = j →
      Module.Projective R (K.X j ⧸ LinearMap.range (K.d i j).hom) := by
    have hz : ∀ j i : ℤ, b < j → i + 1 = j →
        Module.Projective R (K.X j ⧸ LinearMap.range (K.d i j).hom) := by
      intro j i hj _
      have : Subsingleton (K.X j) :=
        ModuleCat.subsingleton_of_isZero (K.isZero_of_isStrictlyLE b j hj)
      have : Subsingleton (K.X j ⧸ LinearMap.range (K.d i j).hom) :=
        (Submodule.mkQ_surjective _).subsingleton
      infer_instance
    intro j
    refine Int.inductionOn' j (b + 1) (fun i hi => hz _ i (by omega) hi)
      (fun k _ _ i hi => hz _ i (by omega) hi) fun k _ ih i hi => ?_
    obtain rfl : k = i + 1 + 1 := by omega
    rw [show i + 1 + 1 - 1 = i + 1 by omega]
    exact (step i (ih (i + 1) rfl)).2
  obtain ⟨i, rfl⟩ : ∃ i, n = i + 1 := ⟨n - 1, by omega⟩
  obtain ⟨⟨hfin, hproj⟩, -⟩ := step i (key _ _ rfl)
  exact ⟨Module.Finite.equiv (K.homologyLinearEquiv i).symm,
    Module.Projective.of_equiv (K.homologyLinearEquiv i).symm⟩

/-- Extension of scalars of a finite projective module is finite projective. -/
theorem finite_projective_extendScalars {A B : Type u} [CommRing A] [CommRing B] (ψ : A →+* B)
    (P : ModuleCat.{u} A) (h : Module.Finite A P ∧ Module.Projective A P) :
    Module.Finite B ((ModuleCat.extendScalars ψ).obj P) ∧
      Module.Projective B ((ModuleCat.extendScalars ψ).obj P) := by
  obtain ⟨_, _⟩ := h
  let := ψ.toAlgebra
  change Module.Finite B (B ⊗[A] P) ∧ Module.Projective B (B ⊗[A] P)
  exact ⟨inferInstance, inferInstance⟩

/-- **Base change of a module that is finite free at a prime.**  If `P` becomes finite free over
the localization of `A` at the inverse image of a prime `q` of `B`, then `B ⊗_A P` becomes finite
free of the same rank over the localization of `B` at `q`. -/
@[ega "III 7.9.1" "more general"]
theorem free_finite_finrank_extendScalars_extendScalars {A B : Type u} [CommRing A] [CommRing B]
    (ψ : A →+* B) (P : ModuleCat.{u} A) (q : Ideal B) [q.IsPrime]
    (Lp : Type u) [CommRing Lp] [Algebra A Lp] [IsLocalization.AtPrime Lp (q.comap ψ)]
    (Lq : Type u) [CommRing Lq] [Algebra B Lq] [IsLocalization.AtPrime Lq q]
    (hfree : Module.Free Lp ((ModuleCat.extendScalars (algebraMap A Lp)).obj P))
    (hfin : Module.Finite Lp ((ModuleCat.extendScalars (algebraMap A Lp)).obj P)) :
    Module.Free Lq ((ModuleCat.extendScalars (algebraMap B Lq)).obj
        ((ModuleCat.extendScalars ψ).obj P)) ∧
      Module.Finite Lq ((ModuleCat.extendScalars (algebraMap B Lq)).obj
        ((ModuleCat.extendScalars ψ).obj P)) ∧
      Module.finrank Lq ((ModuleCat.extendScalars (algebraMap B Lq)).obj
        ((ModuleCat.extendScalars ψ).obj P)) =
        Module.finrank Lp ((ModuleCat.extendScalars (algebraMap A Lp)).obj P) := by
  set p := q.comap ψ
  have hle : p.primeCompl ≤ q.primeCompl.comap ψ := fun a ha => ha
  let ψ' : Lp →+* Lq := IsLocalization.map Lq ψ hle
  have heq : ψ'.comp (algebraMap A Lp) = (algebraMap B Lq).comp ψ := IsLocalization.map_comp hle
  have hLq : Nontrivial Lq := IsLocalization.AtPrime.nontrivial Lq q
  have hLp : Nontrivial Lp := IsLocalization.AtPrime.nontrivial Lp p
  let e : (ModuleCat.extendScalars (algebraMap B Lq)).obj ((ModuleCat.extendScalars ψ).obj P) ≅
      (ModuleCat.extendScalars ψ').obj ((ModuleCat.extendScalars (algebraMap A Lp)).obj P) :=
    ((ModuleCat.extendScalarsComp ψ (algebraMap B Lq)).app P).symm ≪≫
      eqToIso (congrArg (fun φ => (ModuleCat.extendScalars φ).obj P) heq.symm) ≪≫
      (ModuleCat.extendScalarsComp (algebraMap A Lp) ψ').app P
  have h1 : Module.Free Lq ((ModuleCat.extendScalars ψ').obj
      ((ModuleCat.extendScalars (algebraMap A Lp)).obj P)) :=
    Stacks.DerivedTensorHomDiagonal.free_extendScalars ψ' _
  have h2 : Module.Finite Lq ((ModuleCat.extendScalars ψ').obj
      ((ModuleCat.extendScalars (algebraMap A Lp)).obj P)) :=
    Stacks.DerivedTensorHomDiagonal.finite_extendScalars ψ' _
  have h3 : Module.finrank Lq ((ModuleCat.extendScalars ψ').obj
      ((ModuleCat.extendScalars (algebraMap A Lp)).obj P)) =
      Module.finrank Lp ((ModuleCat.extendScalars (algebraMap A Lp)).obj P) := by
    let := ψ'.toAlgebra
    exact Module.finrank_baseChange
  exact ⟨Module.Free.of_equiv e.toLinearEquiv.symm, Module.Finite.equiv e.toLinearEquiv.symm,
    e.toLinearEquiv.finrank_eq.trans h3⟩

end CochainComplex

namespace Stacks.Decalage.Cohomology

open EtaPow

variable {A : Type u} [CommRing A]

/-- The complex of `f`-torsion-free modules underlying a cochain complex of modules on which `f`
acts regularly. -/
def FTFComplex.ofCochainComplex (f : A) (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (hK : ∀ i, IsSMulRegular (K.X i) f) : FTFComplex A f where
  M i := K.X i
  d i := (K.d i (i + 1)).hom
  d_comp_d i := by
    rw [← ModuleCat.hom_comp, K.d_comp_d, ModuleCat.hom_zero]
  tf := hK

/-- The differential of the décalage in degree `i` is `EtaComplex.etaDifferential`. -/
theorem etaObject_d_apply (f : A) (K : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ)
    (x : EtaComplex.term f K i) :
    ((EtaComplex.etaObject f K).d i (i + 1)).hom x = EtaComplex.etaDifferential f K i x := by
  rw [EtaComplex.etaObject_d]
  rfl

/-- The cocycles of the décalage, read in the ambient localization. -/
def etaCyclesEquiv (f : A) (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (hK : ∀ i, IsSMulRegular (K.X i) f) (j : ℤ) :
    LinearMap.ker ((EtaComplex.etaObject f K).d (j + 1) (j + 1 + 1)).hom ≃ₗ[A]
      Zeta (FTFComplex.ofCochainComplex f K hK) j where
  toFun x := ⟨(show EtaComplex.term f K (j + 1) from x.1).1,
    (show EtaComplex.term f K (j + 1) from x.1).2,
    congrArg Subtype.val
      ((etaObject_d_apply f K (j + 1) x.1).symm.trans (LinearMap.mem_ker.mp x.2))⟩
  invFun z := ⟨(⟨z.1, z.2.1⟩ : EtaComplex.term f K (j + 1)),
    LinearMap.mem_ker.mpr ((etaObject_d_apply f K (j + 1) _).trans (Subtype.ext z.2.2))⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- The cohomology of the décalage is the quotient of its cocycles by its coboundaries, both
read in the ambient localization. -/
def etaHomologyLinearEquiv (f : A) (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (hK : ∀ i, IsSMulRegular (K.X i) f) (j : ℤ) :
    (EtaComplex.etaObject f K).homology (j + 1) ≃ₗ[A]
      Heta (FTFComplex.ofCochainComplex f K hK) j :=
  (EtaComplex.etaObject f K).homologyLinearEquiv j ≪≫ₗ
    Submodule.Quotient.equiv _ _ (etaCyclesEquiv f K hK j) (by
      ext z
      rw [Submodule.mem_map_equiv]
      change ((((etaCyclesEquiv f K hK j).symm z).1 : EtaComplex.term f K (j + 1)) ∈
          LinearMap.range ((EtaComplex.etaObject f K).d j (j + 1)).hom) ↔
        z.1 ∈
          Beta (FTFComplex.ofCochainComplex f K hK) j
      constructor
      · rintro ⟨y, hy⟩
        exact ⟨(y : EtaComplex.term f K j).1, (y : EtaComplex.term f K j).2,
          congrArg Subtype.val ((etaObject_d_apply f K j y).symm.trans hy)⟩
      · rintro ⟨y, hy, hyz⟩
        exact ⟨(⟨y, hy⟩ : EtaComplex.term f K j),
          (etaObject_d_apply f K j _).trans (Subtype.ext hyz)⟩)

/-- **The cohomology of the décalage when there is no torsion.**  If the cohomology of a complex
of `f`-torsion-free modules has no `f`-torsion, the décalage has the same cohomology: by More on
Algebra, Tag 0F7P its cohomology is the quotient by the `f`-torsion. -/
theorem nonempty_etaHomologyLinearEquiv_of_isSMulRegular (f : A)
    (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (hK : ∀ i, IsSMulRegular (K.X i) f) (n : ℤ) (hH : IsSMulRegular (K.homology n) f) :
    Nonempty ((EtaComplex.etaObject f K).homology n ≃ₗ[A] K.homology n) := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  let C := FTFComplex.ofCochainComplex f K hK
  let e₀ : Hcohom C j ≃ₗ[A] K.homology (j + 1) := (K.homologyLinearEquiv j).symm
  have hker : LinearMap.ker (etaCohomologyMap C j) = ⊥ := by
    rw [eq_bot_iff]
    intro ξ hξ
    rw [mem_ker_etaCohomologyMap_iff] at hξ
    have h : f • e₀ ξ = f • 0 := by rw [← map_smul, hξ, map_zero, smul_zero]
    exact (Submodule.mem_bot A).mpr (e₀.injective ((hH h).trans e₀.map_zero.symm))
  exact ⟨etaHomologyLinearEquiv f K hK j ≪≫ₗ (etaCohomologyEquiv C j).symm ≪≫ₗ
    Submodule.quotEquivOfEqBot _ hker ≪≫ₗ e₀⟩

end Stacks.Decalage.Cohomology

namespace AlgebraicGeometry

open AlgebraicGeometry.Scheme.Modules (fiberRank)

/-- **The fibre rank of `M̃` at a prime where `M` localizes to a finite free module** is the rank
of that localization: the stalk of `M̃` is the base change of `M` to the stalk of the structure
sheaf. -/
@[ega "III 7.9.1" "more general"]
theorem fiberRank_tilde_eq_finrank_extendScalars {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
    (p : PrimeSpectrum R) :
    letI : Algebra R ((Spec R).presheaf.stalk p) := StructureSheaf.stalkAlgebra R p
    Module.Free ((Spec R).presheaf.stalk p)
        ((ModuleCat.extendScalars (algebraMap R ((Spec R).presheaf.stalk p))).obj M) →
      Module.Finite ((Spec R).presheaf.stalk p)
        ((ModuleCat.extendScalars (algebraMap R ((Spec R).presheaf.stalk p))).obj M) →
      fiberRank (tilde M) p = Module.finrank ((Spec R).presheaf.stalk p)
        ((ModuleCat.extendScalars (algebraMap R ((Spec R).presheaf.stalk p))).obj M) := by
  intro hfree _
  let A := (Spec R).presheaf.stalk p
  let N := TopCat.Presheaf.stalk (moduleStructurePresheaf R M).presheaf p
  let : Algebra R A := StructureSheaf.stalkAlgebra R p
  have : IsLocalization.AtPrime A p.asIdeal := StructureSheaf.IsLocalization.to_stalk R p
  let f : M →ₗ[R] N := (tilde.toStalk M p).hom
  let : Module A N :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := structurePresheafInCommRingCat R) (moduleStructurePresheaf R M) p
  have : IsScalarTower R A N := .of_algebraMap_smul fun _ _ => rfl
  have : IsLocalizedModule p.asIdeal.primeCompl f :=
    tilde.instIsLocalizedModuleCarrierCarrierOfCarrierStalkAbPresheafPrimeComplAsIdealHomToStalk M p
  let eBase : A ⊗[R] M ≃ₗ[A] N := (IsLocalizedModule.isBaseChange p.asIdeal.primeCompl A f).equiv
  let e : (ModuleCat.extendScalars (algebraMap R A)).obj M ≃ₗ[A] N :=
    (StacksDraft.TorAmplitude.FaithfullyFlat.extendScalarsCarrierEquiv R A M).trans eBase
  have : Module.Free A N := Module.Free.of_equiv e
  let x : Spec R := p
  have : Nontrivial A := inferInstanceAs (Nontrivial ((Spec R).presheaf.stalk x))
  let κ := (Spec R).residueField x
  let : Algebra A κ := ((Spec R).residue x).hom.toAlgebra
  change Module.finrank κ (κ ⊗[A] N) = _
  rw [e.finrank_eq]
  exact Module.finrank_baseChange

/-- A finite projective module becomes finite free after extension of scalars to a stalk of the
spectrum. -/
theorem free_finite_extendScalars_stalk {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
    [Module.Finite R M] [Module.Projective R M] (p : PrimeSpectrum R) :
    letI : Algebra R ((Spec R).presheaf.stalk p) := StructureSheaf.stalkAlgebra R p
    Module.Free ((Spec R).presheaf.stalk p)
        ((ModuleCat.extendScalars (algebraMap R ((Spec R).presheaf.stalk p))).obj M) ∧
      Module.Finite ((Spec R).presheaf.stalk p)
        ((ModuleCat.extendScalars (algebraMap R ((Spec R).presheaf.stalk p))).obj M) := by
  let A := (Spec R).presheaf.stalk p
  let : Algebra R A := StructureSheaf.stalkAlgebra R p
  let x : Spec R := p
  have : IsLocalRing A := (Spec R).isLocalRing x
  let e := StacksDraft.TorAmplitude.FaithfullyFlat.extendScalarsCarrierEquiv R A M
  have : Module.Free A (A ⊗[R] M) := Module.free_of_flat_of_isLocalRing
  exact ⟨Module.Free.of_equiv e.symm, Module.Finite.equiv e.symm⟩

/-- **The fibre rank of the pullback of a finite projective module along a morphism of affine
schemes.**  The fibre rank of `(B ⊗_A P)^~` at a point `z` of `Spec B` is the fibre rank of `P̃`
at the image of `z` in `Spec A`. -/
theorem fiberRank_tilde_extendScalars {A B : CommRingCat.{u}} (φ : A ⟶ B) (P : ModuleCat.{u} A)
    [Module.Finite A P] [Module.Projective A P] (z : PrimeSpectrum B) :
    fiberRank (tilde ((ModuleCat.extendScalars φ.hom).obj P)) z =
      fiberRank (tilde P) (PrimeSpectrum.comap φ.hom z) := by
  let Lq := (Spec B).presheaf.stalk z
  let Lp := (Spec A).presheaf.stalk (PrimeSpectrum.comap φ.hom z)
  let : Algebra B Lq := StructureSheaf.stalkAlgebra B z
  let : Algebra A Lp := StructureSheaf.stalkAlgebra A (PrimeSpectrum.comap φ.hom z)
  have : IsLocalization.AtPrime Lq z.asIdeal := StructureSheaf.IsLocalization.to_stalk B z
  have : IsLocalization.AtPrime Lp (z.asIdeal.comap φ.hom) :=
    StructureSheaf.IsLocalization.to_stalk A (PrimeSpectrum.comap φ.hom z)
  obtain ⟨hfree, hfin⟩ := free_finite_extendScalars_stalk P (PrimeSpectrum.comap φ.hom z)
  obtain ⟨hfree', hfin', hrank⟩ :=
    CochainComplex.free_finite_finrank_extendScalars_extendScalars φ.hom P z.asIdeal Lp Lq
      hfree hfin
  rw [fiberRank_tilde_eq_finrank_extendScalars _ z hfree' hfin',
    fiberRank_tilde_eq_finrank_extendScalars _ _ hfree hfin, hrank]

end AlgebraicGeometry

end
