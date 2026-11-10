module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
public import StacksFrontier.AlgebraicGeometry.QuasiRegular.Basic
public import StacksFrontier.AlgebraicGeometry.QuasiRegular.StalkGenerators
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Basic
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
public import StacksFrontier.Topology.Sheaves.Modules.SupportedSectionsSheaf
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Characterization.ConormalSheaves

/-!
# Quasi-regular ideal sheaves: finite type and symmetric words

Finite type of a quasi-regular ideal sheaf, cotangent bases from local generators, and the
words, monomials and polynomial maps presenting the symmetric powers of a generated ideal.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.RingTheory.QuasiRegular
open scoped BigOperators
universe u v

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local implicit_reducible] SheafOfModules.toSheaf PresheafOfModules.presheaf
open Stacks.AlgebraicGeometry.RegularIdealSheaf.Conormal in
attribute [local implicit_reducible] quotientPresheaf quotientSheaf gradedPresheaf
attribute [local implicit_reducible] PresheafOfModules.freeObj ModuleCat.free
  CategoryTheory.Functor.sheafPushforwardContinuous

namespace Stacks.AlgebraicGeometry.RegularIdealSheaf.Conormal

private noncomputable def generatingSectionsOver (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule) (U : Opens X) {r : ℕ}
    (f : Fin r → X.presheaf.obj (op U))
    (hgen : IsGeneratedByOn X J U f) :
    (J.toSheafOfModules.over U).GeneratingSections where
  I := ULift.{u} (Fin r)
  s i := sectionOver X J U ⟨f i.down, mem_of_isGeneratedByOn X J U f hgen i.down⟩
  epi := by
    apply Preadditive.epi_of_cancel_zero
    intro N φ hφ
    apply hom_eq_zero_of_generators X J U f hgen φ
    intro i V
    have he := congrArg (fun p => (N.freeHomEquiv p ⟨i⟩).val V) hφ
    simp only [SheafOfModules.freeHomEquiv_comp_apply, Equiv.apply_symm_apply] at he
    change φ.val.app V
      ((sectionOver X J U ⟨f i, mem_of_isGeneratedByOn X J U f hgen i⟩).val V) = 0 at he
    exact he

private lemma isFiniteType_of_local_generators (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule)
    (h : ∀ x : X, ∃ (U : Opens X) (_ : x ∈ U) (r : ℕ)
      (f : Fin r → X.presheaf.obj (op U)), IsGeneratedByOn X J U f) :
    J.toSheafOfModules.IsFiniteType := by
  classical
  choose U hx r f hf using h
  let q : J.toSheafOfModules.LocalGeneratorsData :=
    { I := X
      X := U
      coversTop := (Opens.coversTop_iff X U).2 (by
        change iSup U = ⊤
        apply top_unique
        intro x _
        exact (Opens.mem_iSup).mpr ⟨x, hx x⟩)
      generators x := generatingSectionsOver X J (U x) (f x) (hf x) }
  refine { exists_localGeneratorsData := ⟨q, ?_⟩ }
  constructor
  intro x
  exact ⟨inferInstanceAs (Finite (ULift.{u} (Fin (r x))))⟩

private lemma mem_ideal_iff_cokernel_π_eq_zero (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule)
    (V : (Opens X)ᵒᵖ) (s : X.presheaf.obj V) :
    s ∈ J.obj V ↔ (Limits.cokernel.π J.ι).val.app V s = 0 := by
  let R := (sheafCompose (Opens.grothendieckTopology X)
    (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf
  let E := SheafOfModules.forget R ⋙ PresheafOfModules.evaluation R.obj V
  let S := ShortComplex.mk J.ι (Limits.cokernel.π J.ι) (Limits.cokernel.condition J.ι)
  have hk := Limits.isLimitForkMapOfIsLimit' E (Limits.cokernel.condition J.ι)
    (Abelian.monoIsKernelOfCokernel _ (Limits.colimit.isColimit _))
  have he : (S.map E).Exact := (S.map E).exact_of_f_is_kernel hk
  constructor
  · intro hs
    exact congrArg (fun φ => φ.val.app V ⟨s, hs⟩) (Limits.cokernel.condition J.ι)
  · intro hs
    obtain ⟨t, ht⟩ := (ShortComplex.moduleCat_exact_iff (S.map E)).mp he s hs
    exact ht ▸ t.property

lemma exists_one_mem_of_notMem_support (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule) (x : X)
    (hx : x ∉ idealQuotientSupport X J) :
    ∃ U : Opens X, x ∈ U ∧ (1 : X.presheaf.obj (op U)) ∈ J.obj (op U) := by
  let F : RingedSpace.ModuleSheaf.{u} X :=
    ⟨(idealQuotient X J).val, (idealQuotient X J).isSheaf⟩
  let q := Limits.cokernel.π J.ι
  have hz : F.sectionGerm ⊤ x trivial
      (q.val.app (op ⊤) (1 : X.presheaf.obj (op ⊤))) = 0 := by
    by_contra hn
    exact hx ⟨_, hn⟩
  obtain ⟨U, hxU, i, hi⟩ := (F.sectionGerm_eq_zero_iff ⊤ x trivial _).mp hz
  refine ⟨U, hxU, (mem_ideal_iff_cokernel_π_eq_zero X J (op U) 1).mpr ?_⟩
  change (idealQuotient X J).val.map i.op
    (q.val.app (op ⊤) (1 : X.presheaf.obj (op ⊤))) = 0 at hi
  have hi2 : q.val.app (op U)
      ((X.presheaf.map i.op) (1 : X.presheaf.obj (op ⊤))) = 0 :=
    (PresheafOfModules.naturality_apply q.val i.op (1 : X.presheaf.obj (op ⊤))).trans hi
  simpa only [map_one] using hi2

lemma isGeneratedByOn_one (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule) (U : Opens X)
    (h : (1 : X.presheaf.obj (op U)) ∈ J.obj (op U)) :
    IsGeneratedByOn X J U (fun _ : Fin 1 => 1) := by
  intro V hVU
  apply le_antisymm
  · have h1 := mem_generatedIdealOn X U (fun _ : Fin 1 => 1) 0
    have hV := (generatedIdealOn X U (fun _ : Fin 1 => 1)).toSubmodule.map_mem
      (homOfLE hVU).op h1
    change (X.presheaf.map (homOfLE hVU).op) 1 ∈ _ at hV
    rw [map_one] at hV
    have htop : (generatedIdealOn X U (fun _ : Fin 1 => 1)).obj (op V) = ⊤ :=
      (Ideal.eq_top_iff_one _).mpr hV
    rw [htop]
    exact le_top
  · exact generatedIdealOn_le X U (fun _ : Fin 1 => 1) J (fun _ => h) (op V)

lemma isFiniteType_of_isQuasiRegularIdealSheaf (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule)
    (h : IsQuasiRegularIdealSheaf X J) : J.toSheafOfModules.IsFiniteType := by
  apply isFiniteType_of_local_generators X J
  intro x
  by_cases hx : x ∈ idealQuotientSupport X J
  · obtain ⟨U, hxU, r, f, _, hf⟩ := h x hx
    exact ⟨U, hxU, r, f, hf⟩
  · obtain ⟨U, hxU, hU⟩ := exists_one_mem_of_notMem_support X J x hx
    exact ⟨U, hxU, 1, fun _ => 1, isGeneratedByOn_one X J U hU⟩

/-- The value on `U` of a section of the restriction of the ideal sheaf to `U`. -/
private noncomputable def generatorOfSections (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule) (U : Opens X)
    (t : (J.toSheafOfModules.over U).sections) : J.obj (op U) :=
  t.val (op (Over.mk (𝟙 U)))

/-- A section of the restriction of the ideal sheaf to `U` is the restriction of its
value on `U`: the category `Over U` has a terminal object. -/
private lemma sections_over_val (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule) (U : Opens X)
    (t : (J.toSheafOfModules.over U).sections) (V : (Over U)ᵒᵖ) :
    J.toSheafOfModules.val.map V.unop.hom.op (generatorOfSections X J U t) = t.val V :=
  t.property ((Over.homMk V.unop.hom (by simp) : V.unop ⟶ Over.mk (𝟙 U)).op)

/-- The inclusion of an ideal subsheaf commutes with restriction. -/
private lemma ideal_ι_app_map (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule) {Y Z : (Opens X)ᵒᵖ} (h : Y ⟶ Z)
    (z : J.obj Y) :
    J.ι.val.app Z (J.toSheafOfModules.val.map h z) =
      X.presheaf.map h z.val := rfl

/-- The composite `J ⟶ O_X ⟶ O_X / W` kills a section of `J.over U` whose value on `U`
restricts into `W`. Stated with `W` abstract so that the rewrite below never has to
traverse the infimum defining a generated subsheaf. -/
private lemma cokernel_π_app_sections_over (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule) (U : Opens X)
    (W : (Stacks.RingedSpace.structureSheafModule X).Submodule)
    (t : (J.toSheafOfModules.over U).sections) (V : (Over U)ᵒᵖ)
    (h : X.presheaf.map V.unop.hom.op (generatorOfSections X J U t).val ∈
      W.obj (op V.unop.left)) :
    (Limits.cokernel.π W.ι).val.app (op V.unop.left)
      (J.ι.val.app (op V.unop.left) (t.val V)) = 0 := by
  rw [← sections_over_val X J U t V, ideal_ι_app_map]
  exact (mem_ideal_iff_cokernel_π_eq_zero X W (op V.unop.left) _).mp h

/-- **Generating sections generate**, stated against an abstract ideal subsheaf `W` so
that no defeq check has to unfold the infimum defining the generated subsheaf. If every
generating section of `J.over U` lies in `W` over every open above `U`, then `J` agrees
with `W` below `U`. -/
private lemma le_of_generatingSections (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule) (U : Opens X)
    (σ : (J.toSheafOfModules.over U).GeneratingSections) {m : ℕ} (e : Fin m ≃ σ.I)
    (W : (Stacks.RingedSpace.structureSheafModule X).Submodule)
    (hs : ∀ (k : Fin m) (V : (Over U)ᵒᵖ),
      (Limits.cokernel.π W.ι).val.app (op V.unop.left)
        (J.ι.val.app (op V.unop.left) ((σ.s (e k)).val V)) = 0)
    (V : Opens X) (hVU : V ≤ U) : J.obj (op V) ≤ W.obj (op V) := by
  have hzero : (J.ι ≫ Limits.cokernel.π W.ι).over U = 0 := by
    apply (cancel_epi σ.π).mp
    apply (SheafOfModules.freeHomEquiv _).injective
    funext i
    obtain ⟨k, rfl⟩ := e.surjective i
    apply PresheafOfModules.sections_ext
    intro Y
    simp only [SheafOfModules.freeHomEquiv_comp_apply, Equiv.apply_symm_apply]
    have hr : (0 : J.toSheafOfModules.over U ⟶
        (Limits.cokernel W.ι).over U).val.app Y ((σ.s (e k)).val Y) = 0 := rfl
    refine Eq.trans ?_ hr.symm
    exact hs k Y
  intro s hsJ
  apply (mem_ideal_iff_cokernel_π_eq_zero X W (op V) s).mpr
  have h := congrArg (fun (ψ : J.toSheafOfModules.over U ⟶
      (Limits.cokernel W.ι).over U) =>
    ψ.val.app (op (Over.mk (homOfLE hVU))) ⟨s, hsJ⟩) hzero
  have hr : (0 : J.toSheafOfModules.over U ⟶
      (Limits.cokernel W.ι).over U).val.app (op (Over.mk (homOfLE hVU)))
      ⟨s, hsJ⟩ = 0 := rfl
  exact h.trans hr

/-- Generating sections of `J` over `U` generate it in the sense of
`IsGeneratedByOn`. This is the converse of `generatingSectionsOver`. -/
private lemma isGeneratedByOn_of_generatingSections (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule) (U : Opens X)
    (σ : (J.toSheafOfModules.over U).GeneratingSections) {m : ℕ} (e : Fin m ≃ σ.I) :
    IsGeneratedByOn X J U
      (fun k => (generatorOfSections X J U (σ.s (e k))).val) := by
  classical
  have hmem : ∀ (k : Fin m) (V : (Over U)ᵒᵖ),
      (Limits.cokernel.π (generatedIdealOn X U
        (fun k => (generatorOfSections X J U (σ.s (e k))).val)).ι).val.app
          (op V.unop.left)
          (J.ι.val.app (op V.unop.left) ((σ.s (e k)).val V)) = 0 := fun k V =>
    cokernel_π_app_sections_over X J U _ (σ.s (e k)) V
      ((generatedIdealOn X U
        (fun k => (generatorOfSections X J U (σ.s (e k))).val)).toSubmodule.map_mem
          V.unop.hom.op (mem_generatedIdealOn X U _ k))
  intro V hVU
  refine le_antisymm (le_of_generatingSections X J U σ e _ hmem V hVU) ?_
  exact generatedIdealOn_le X U _ J
    (fun k => (generatorOfSections X J U (σ.s (e k))).property) (op V)

private lemma polynomialQuasiRegularCanonicalMap_monomial {R : Type u} [CommRing R]
    {r : ℕ} (f : Fin r → R) (e : Fin r →₀ ℕ) (a : R) :
    associatedGradedMap f
      (MvPolynomial.monomial e (Ideal.Quotient.mk (Jid f) a)) = imgTargetLin f e a := by
  unfold associatedGradedMap
  change quasiRegularCanonicalMap f
    ((MvPolynomial.monomial e (Ideal.Quotient.mk (Jid f) a)) ⊗ₜ[qrRbar f]
      ((Submodule.quotEquivOfEq (Jid f : Submodule R R)
        (Jid f • (⊤ : Submodule R R)) (by simp) : qrRbar f →ₗ[R] qrMbar R f) 1)) = _
  have h : MvPolynomial.monomial e (Ideal.Quotient.mk (Jid f) a) =
      Ideal.Quotient.mk (Jid f) a • MvPolynomial.monomial e (1 : qrRbar f) := by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [h, TensorProduct.smul_tmul]
  change quasiRegularCanonicalMap f (srcMono f e (a * 1)) = _
  rw [mul_one, canonicalMap_srcMono]

/-- The generators `f i` span the ideal `Jid f`, viewed as an `R`-module. -/
private lemma span_range_generators_eq_top {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R) :
    Submodule.span R (Set.range (fun i : Fin r =>
      (⟨f i, Ideal.subset_span (Set.mem_range_self i)⟩ : Jid f))) = ⊤ := by
  apply Submodule.map_injective_of_injective (Submodule.injective_subtype (Jid f))
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]
  rfl

lemma cotangent_generators_span {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin r → R) :
    Submodule.span (qrRbar f) (Set.range (fun i : Fin r =>
      (Jid f).toCotangent ⟨f i, Ideal.subset_span (Set.mem_range_self i)⟩)) = ⊤ := by
  apply Submodule.span_eq_top_of_span_eq_top R
  change Submodule.span R (Set.range ((Jid f).toCotangent ∘ fun i : Fin r =>
    (⟨f i, Ideal.subset_span (Set.mem_range_self i)⟩ : Jid f))) = ⊤
  rw [Set.range_comp, ← Submodule.map_span, span_range_generators_eq_top, Submodule.map_top,
    Ideal.toCotangent_range]

private lemma conormalSymmetricToGradedMap_isIso_iff_locallyInjective
    (X : RingedSpace.{u}) (J : (Stacks.RingedSpace.structureSheafModule X).Submodule) (n : ℕ) :
    IsIso (conormalSymmetricToGradedMap X J n) ↔
      PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology X)
        (canonicalPresheafMap X J n) := by
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf _)]
  change IsIso ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
    ((PresheafOfModules.toPresheaf _).map (canonicalPresheafMap X J n))) ↔ _
  rw [← GrothendieckTopology.W_iff, GrothendieckTopology.W_iff_isLocallyBijective]
  have hs : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf _).map (canonicalPresheafMap X J n)) := by
    apply Presheaf.isLocallySurjective_of_surjective
    intro U
    exact Construction.canonicalMap_surjective (sectionIdeal X J U) n
  exact and_iff_left hs

lemma conormalSymmetricToGradedMap_isIso_iff_local_kernel
    (X : RingedSpace.{u}) (J : (Stacks.RingedSpace.structureSheafModule X).Submodule) (n : ℕ) :
    IsIso (conormalSymmetricToGradedMap X J n) ↔
      ∀ (U : Opens X) (z : Construction.SymmetricPower (sectionIdeal X J (op U)) n),
        Construction.canonicalMap (sectionIdeal X J (op U)) n z = 0 →
        ∀ (x : X), x ∈ U → ∃ (V : Opens X) (_ : x ∈ V) (i : V ⟶ U),
          Construction.symmetricMap _ _ (X.presheaf.map i.op).hom
            (sectionIdeal_map X J i.op) n z = 0 := by
  rw [conormalSymmetricToGradedMap_isIso_iff_locallyInjective]
  constructor
  · intro h U z hz x hx
    have hs := Presheaf.equalizerSieve_mem (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf _).map (canonicalPresheafMap X J n))
      z 0 (by exact hz.trans (map_zero _).symm)
    obtain ⟨V, i, hV, hxV⟩ := hs x hx
    refine ⟨V, hxV, i, ?_⟩
    change Construction.symmetricMap _ _ _ _ n z =
      Construction.symmetricMap _ _ _ _ n 0 at hV
    exact hV.trans (map_zero _)
  · intro h
    constructor
    intro U z w hzw x hx
    change Construction.canonicalMap _ n z = Construction.canonicalMap _ n w at hzw
    obtain ⟨V, hxV, i, hi⟩ := h U.unop (z - w)
      ((map_sub (Construction.canonicalMap (sectionIdeal X J U) n) z w).trans
        (sub_eq_zero.mpr hzw)) x hx
    refine ⟨V, i, ?_, hxV⟩
    change Construction.symmetricMap _ _ _ _ n z = Construction.symmetricMap _ _ _ _ n w
    exact sub_eq_zero.mp
      ((map_sub (Construction.symmetricMap (sectionIdeal X J U) (sectionIdeal X J (op V))
        (X.presheaf.map i.op).hom (sectionIdeal_map X J i.op) n) z w).symm.trans hi)

private noncomputable def idealToTarget {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin r → R) : Jid f →ₗ[R] Target R f :=
  (DirectSum.lof R ℕ (fun n => Tcomp R f n) 1).comp
    ((Tsub R f 1).mkQ.comp (Submodule.inclusion (by simp [JpowM])))

private noncomputable def cotangentToTarget {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin r → R) : (Jid f).Cotangent →ₗ[qrRbar f] Target R f :=
  (Ideal.Cotangent.lift (R := R) (I := Jid f) (M := Target R f)
    (idealToTarget f) (by
    intro x y
    change (DirectSum.lof R ℕ (fun n => Tcomp R f n) 1) _ = 0
    rw [← map_zero (DirectSum.lof R ℕ (fun n => Tcomp R f n) 1)]
    congr 1
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    change (x : R) * y ∈ JpowM R f (1 + 1)
    simpa [JpowM, pow_two] using Ideal.mul_mem_mul x.property y.property
    )).extendScalarsOfSurjective Ideal.Quotient.mk_surjective

private lemma target_mk_eq_of_val_eq {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin r → R) {n m : ℕ} (h : n = m)
    (a : JpowM R f n) (b : JpowM R f m) (hab : a.val = b.val) :
    (DirectSum.lof R ℕ (fun k => Tcomp R f k) n) (Submodule.Quotient.mk a) =
      (DirectSum.lof R ℕ (fun k => Tcomp R f k) m) (Submodule.Quotient.mk b) := by
  subst m
  exact congrArg (fun z => (DirectSum.lof R ℕ (fun k => Tcomp R f k) n)
    (Submodule.Quotient.mk z)) (Subtype.ext hab)

private lemma cotangentToTarget_generator {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin r → R) (i : Fin r) :
    cotangentToTarget f ((Jid f).toCotangent
      ⟨f i, Ideal.subset_span (Set.mem_range_self i)⟩) =
      associatedGradedMap f (MvPolynomial.X i) := by
  rw [MvPolynomial.X, ← map_one (Ideal.Quotient.mk (Jid f)),
    polynomialQuasiRegularCanonicalMap_monomial]
  change (DirectSum.lof R ℕ (fun n => Tcomp R f n) 1)
    (Submodule.Quotient.mk ⟨f i, _⟩) = imgTargetLin f (Finsupp.single i 1) 1
  have he : qrMdeg (Finsupp.single i 1) = 1 := by simp [qrMdeg]
  apply target_mk_eq_of_val_eq f he.symm
  change f i = fpow f (Finsupp.single i 1) • (1 : R)
  simp [fpow, Finsupp.single_apply]

@[sga "1 II 4.14" "(ii)"]
lemma cotangent_generators_linearIndependent {R : Type u} [CommRing R]
    {r : ℕ} (f : Fin r → R)
    (hf : Function.Injective (associatedGradedMap f)) :
    LinearIndependent (qrRbar f) (fun i : Fin r =>
      (Jid f).toCotangent ⟨f i, Ideal.subset_span (Set.mem_range_self i)⟩) := by
  intro a b hab
  have ht := congrArg (cotangentToTarget f) hab
  have hp : associatedGradedMap f (MvPolynomial.sumSMulX a) =
      associatedGradedMap f (MvPolynomial.sumSMulX b) := by
    simpa only [MvPolynomial.sumSMulX, Finsupp.linearCombination_apply,
      map_finsuppSum, map_smul, cotangentToTarget_generator] using ht
  have h := hf hp
  ext i
  simpa only [MvPolynomial.coeff_sumSMulX] using
    congrArg (fun p => p.coeff (Finsupp.single i 1)) h

@[sga "1 II 4.14" "(ii), special case"]
noncomputable def cotangentBasis {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin r → R)
    (hf : Function.Injective (associatedGradedMap f)) :
    Module.Basis (Fin r) (qrRbar f) (Jid f).Cotangent :=
  Module.Basis.mk (cotangent_generators_linearIndependent f hf)
    (cotangent_generators_span f).ge

private noncomputable def idealSheafOfStalkIdeals (X : RingedSpace.{u})
    (I : ∀ x : X, Ideal (X.presheaf.stalk x)) :
    (Stacks.RingedSpace.structureSheafModule X).Submodule where
  obj U :=
    { carrier := {s | ∀ (x : X) (hx : x ∈ U.unop), X.presheaf.germ U.unop x hx s ∈ I x}
      zero_mem' := by
        intro x hx
        exact Eq.mpr (congrArg (fun z => z ∈ I x)
          (map_zero (ConcreteCategory.hom (X.presheaf.germ U.unop x hx)))) (I x).zero_mem
      add_mem' := by
        intro a b ha hb x hx
        exact Eq.mpr (congrArg (fun z => z ∈ I x)
          (map_add (ConcreteCategory.hom (X.presheaf.germ U.unop x hx)) a b))
          ((I x).add_mem (ha x hx) (hb x hx))
      smul_mem' := by
        intro a s hs x hx
        change X.presheaf.obj U at a s
        change X.presheaf.germ U.unop x hx (a * s) ∈ I x
        rw [map_mul]
        exact (I x).mul_mem_left _ (hs x hx) }
  map {U V} i s hs x hx := by
    change X.presheaf.germ V.unop x hx (X.presheaf.map i s) ∈ I x
    exact Eq.mpr (congrArg (fun z => z ∈ I x)
      (X.presheaf.germ_res_apply' i x hx s)) (hs x (leOfHom i.unop hx))
  isSheaf {U} s hs x hx := by
    obtain ⟨V, i, hi, hxV⟩ := hs x hx
    have h := hi x hxV
    change X.presheaf.germ V x hxV (X.presheaf.map i.op s) ∈ I x at h
    exact Eq.mp (congrArg (fun z => z ∈ I x)
      (X.presheaf.germ_res_apply i x hxV s)) h

lemma germ_mem_span_of_isGeneratedByOn (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule) (U V : Opens X)
    {r : ℕ} (f : Fin r → X.presheaf.obj (op U))
    (hgen : IsGeneratedByOn X J U f) (hVU : V ≤ U)
    (s : X.presheaf.obj (op V)) (hs : s ∈ J.obj (op V)) (x : X) (hx : x ∈ V) :
    X.presheaf.germ V x hx s ∈
      Jid (fun i => X.presheaf.germ U x (hVU hx) (f i)) := by
  classical
  let I : ∀ x : X, Ideal (X.presheaf.stalk x) := fun x =>
    if h : x ∈ U then Jid (fun i => X.presheaf.germ U x h (f i)) else ⊤
  have hle : generatedIdealOn X U f ≤ idealSheafOfStalkIdeals X I := by
    apply generatedIdealOn_le
    intro i y hy
    simp only [I, dite_eq_left hy]
    exact Ideal.subset_span (Set.mem_range_self i)
  have hs' : s ∈ (idealSheafOfStalkIdeals X I).obj (op V) :=
    hle _ ((hgen V hVU) ▸ hs)
  simpa only [I, dite_eq_left (hVU hx)] using hs' x hx

lemma exists_sections_of_finite_germs (X : RingedSpace.{u}) (x : X)
    (U : Opens X) (hx : x ∈ U) {r : ℕ} (a : Fin r → X.presheaf.stalk x) :
    ∃ (V : Opens X) (_hVU : V ≤ U) (hxV : x ∈ V)
      (b : Fin r → X.presheaf.obj (op V)),
      ∀ i, X.presheaf.germ V x hxV (b i) = a i := by
  induction r generalizing U with
  | zero => exact ⟨U, le_rfl, hx, Fin.elim0, fun i => i.elim0⟩
  | succ r ih =>
    obtain ⟨W, hWU, hxW, b₀, hb₀⟩ := X.presheaf.exists_le_germ_eq (a 0) hx
    obtain ⟨V, hVW, hxV, b, hb⟩ := ih W hxW (fun i => a i.succ)
    refine ⟨V, hVW.trans hWU, hxV,
      Fin.cons (X.presheaf.map (homOfLE hVW).op b₀) b, ?_⟩
    intro i
    refine Fin.cases ?_ (fun j => hb j) i
    simpa only [Fin.cons_zero, TopCat.Presheaf.germ_res_apply] using hb₀

lemma exists_local_linearCombination_of_germ_mem_span (X : RingedSpace.{u})
    (U V : Opens X) {r : ℕ} (f : Fin r → X.presheaf.obj (op U))
    (s : X.presheaf.obj (op V)) (x : X) (hxU : x ∈ U) (hxV : x ∈ V)
    (hs : X.presheaf.germ V x hxV s ∈
      Jid (fun i => X.presheaf.germ U x hxU (f i))) :
    ∃ (W : Opens X) (_ : x ∈ W) (iU : W ⟶ U) (iV : W ⟶ V)
      (a : Fin r → X.presheaf.obj (op W)),
      ∑ i, a i * X.presheaf.map iU.op (f i) = X.presheaf.map iV.op s := by
  classical
  obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.mp hs
  obtain ⟨C, hC, hxC, b, hb⟩ :=
    exists_sections_of_finite_germs X x (U ⊓ V) ⟨hxU, hxV⟩ a
  let jU : C ⟶ U := homOfLE (hC.trans inf_le_left)
  let t : X.presheaf.obj (op C) := ∑ i, b i * X.presheaf.map jU.op (f i)
  have ht : X.presheaf.germ C x hxC t = X.presheaf.germ V x hxV s := by
    simpa only [t, map_sum, map_mul, hb, TopCat.Presheaf.germ_res_apply] using ha
  obtain ⟨W, hxW, jC, jV, hj⟩ := X.presheaf.germ_eq x hxC hxV t s ht
  refine ⟨W, hxW, jC ≫ jU, jV, fun i => X.presheaf.map jC.op (b i), ?_⟩
  simpa only [t, map_sum, map_mul, op_comp, Functor.map_comp,
    CommRingCat.comp_apply] using hj

lemma exists_local_linearCombination_of_isGeneratedByOn (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule) (U V : Opens X)
    {r : ℕ} (f : Fin r → X.presheaf.obj (op U))
    (hgen : IsGeneratedByOn X J U f) (hVU : V ≤ U)
    (s : X.presheaf.obj (op V)) (hs : s ∈ J.obj (op V)) (x : X) (hx : x ∈ V) :
    ∃ (W : Opens X) (_ : x ∈ W) (iU : W ⟶ U) (iV : W ⟶ V)
      (a : Fin r → X.presheaf.obj (op W)),
      ∑ i, a i * X.presheaf.map iU.op (f i) = X.presheaf.map iV.op s :=
  exists_local_linearCombination_of_germ_mem_span X U V f s x (hVU hx) hx
    (germ_mem_span_of_isGeneratedByOn X J U V f hgen hVU s hs x hx)

namespace Construction
variable {R : Type u} [CommRing R] (I : Ideal R)

noncomputable def wordClass (n : ℕ) :
    MultilinearMap R (fun _ : Fin n => I) (SymmetricPower I n) where
  toFun a := Submodule.Quotient.mk (word I a)
  map_update_add' := by
    intro d a i x y
    have hd : d = instDecidableEqFin n := Subsingleton.elim _ _
    subst d
    have h := (Submodule.Quotient.mk_eq_zero (relations I n)).2
      (Submodule.subset_span (SymmetricRelation.add (I := I) a i x y))
    simpa only [Submodule.Quotient.mk_sub, sub_eq_zero, sub_eq_iff_eq_add,
      zero_add, add_comm] using h
  map_update_smul' := by
    intro d a i r x
    have hd : d = instDecidableEqFin n := Subsingleton.elim _ _
    subst d
    have h := (Submodule.Quotient.mk_eq_zero (relations I n)).2
      (Submodule.subset_span (SymmetricRelation.smul (I := I) a i r x))
    simpa only [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul, sub_eq_zero] using h

lemma wordClass_perm {n : ℕ} (a : Fin n → I) (σ : Equiv.Perm (Fin n)) :
    wordClass I n (a ∘ σ) = wordClass I n a := by
  have h := (Submodule.Quotient.mk_eq_zero (relations I n)).2
    (Submodule.subset_span (SymmetricRelation.perm (I := I) a σ))
  exact sub_eq_zero.mp h

private lemma wordClass_eq_zero_of_one_mem {n : ℕ} (hI : (1 : R) ∈ I)
    (z : SymmetricPower I n) : z = 0 := by
  have h : (1 : R) • z = 0 := symmetricPower_torsion I n (a := ⟨1, hI⟩)
  simpa only [one_smul] using h

private lemma span_wordClass_eq_top (n : ℕ) :
    Submodule.span R (Set.range (wordClass I n)) = ⊤ := by
  apply top_unique
  intro z hz
  clear hz
  induction z using Submodule.Quotient.induction_on with | _ z =>
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => exact Submodule.add_mem _ ha hb
  | single a r =>
    have h : Finsupp.single a r = r • word I a := by simp [word]
    rw [h, Submodule.Quotient.mk_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self a))

lemma span_generatorWord_eq_top {r : ℕ} (f : Fin r → I)
    (hf : Submodule.span R (Set.range f) = ⊤) (n : ℕ) :
    Submodule.span R (Set.range (fun t : Fin n → Fin r => wordClass I n (f ∘ t))) = ⊤ := by
  classical
  rw [← span_wordClass_eq_top I n]
  apply le_antisymm
  · apply Submodule.span_mono
    rintro _ ⟨t, rfl⟩
    exact Set.mem_range_self _
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    have ha : ∀ j, ∃ c : Fin r → R, ∑ i, c i • f i = a j := by
      intro j
      apply (Submodule.mem_span_range_iff_exists_fun R).mp
      rw [hf]
      trivial
    choose c hc using ha
    have he : a = fun j => ∑ i, c j i • f i := funext (fun j => (hc j).symm)
    rw [he, MultilinearMap.map_sum]
    apply Submodule.sum_mem
    intro t _
    rw [MultilinearMap.map_smul_univ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self t))

end Construction

noncomputable def tupleExponent {r n : ℕ} (t : Fin n → Fin r) : Fin r →₀ ℕ :=
  ∑ j, Finsupp.single (t j) 1

lemma tupleExponent_eq_iff {r n : ℕ} (a b : Fin n → Fin r) :
    tupleExponent a = tupleExponent b ↔ ∃ σ : Equiv.Perm (Fin n), b ∘ σ = a := by
  classical
  constructor
  · intro h
    have hc : ∀ i, Fintype.card {j // a j = i} = Fintype.card {j // b j = i} := by
      intro i
      have h' := congrArg (fun e : Fin r →₀ ℕ => e i) h
      simpa only [tupleExponent, Finsupp.finsetSum_apply, Finsupp.single_apply,
        Fintype.card_subtype, Finset.sum_boole, Nat.cast_id] using h'
    let e : ∀ i, {j // a j = i} ≃ {j // b j = i} :=
      fun i => Fintype.equivOfCardEq (hc i)
    let σ := (Equiv.sigmaFiberEquiv a).symm.trans
      ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv b))
    refine ⟨σ, funext (fun j => ?_)⟩
    exact (e (a j) ⟨j, rfl⟩).property
  · rintro ⟨σ, rfl⟩
    exact Equiv.sum_comp σ (fun j => Finsupp.single (b j) 1)

private lemma tupleExponent_degree {r n : ℕ} (t : Fin n → Fin r) :
    qrMdeg (tupleExponent t) = n := by
  classical
  simp only [qrMdeg, tupleExponent, Finsupp.finsetSum_apply]
  rw [Finset.sum_comm]
  simp

private lemma fpow_tupleExponent {R : Type u} [CommRing R] {r n : ℕ}
    (f : Fin r → R) (t : Fin n → Fin r) : fpow f (tupleExponent t) = ∏ j, f (t j) := by
  classical
  simp only [fpow, tupleExponent, Finsupp.finsetSum_apply, ← Finset.prod_pow_eq_pow_sum]
  rw [Finset.prod_comm]
  simp [Finsupp.single_apply]

noncomputable abbrev idealGenerator {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin r → R) (i : Fin r) : Jid f :=
  ⟨f i, Ideal.subset_span (Set.mem_range_self i)⟩

lemma span_idealGenerator_eq_top {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin r → R) : Submodule.span R (Set.range (idealGenerator f)) = ⊤ :=
  span_range_generators_eq_top f

private noncomputable def monomialWord {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin r → R) (n : ℕ) (e : Fin r →₀ ℕ) : Construction.SymmetricPower (Jid f) n :=
  if h : ∃ t : Fin n → Fin r, tupleExponent t = e then
    Construction.wordClass (Jid f) n (idealGenerator f ∘ h.choose) else 0

private lemma monomialWord_tupleExponent {R : Type u} [CommRing R] {r n : ℕ}
    (f : Fin r → R) (t : Fin n → Fin r) :
    monomialWord f n (tupleExponent t) =
      Construction.wordClass (Jid f) n (idealGenerator f ∘ t) := by
  classical
  let h : ∃ s : Fin n → Fin r, tupleExponent s = tupleExponent t := ⟨t, rfl⟩
  rw [monomialWord, dite_eq_left h]
  change Construction.wordClass (Jid f) n (idealGenerator f ∘ h.choose) = _
  obtain ⟨σ, hσ⟩ := (tupleExponent_eq_iff h.choose t).mp h.choose_spec
  rw [← hσ]
  exact Construction.wordClass_perm (Jid f) (idealGenerator f ∘ t) σ

private noncomputable def polynomialToWord {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin r → R) (n : ℕ) :
    MvPolynomial (Fin r) (qrRbar f) →ₗ[qrRbar f] Construction.SymmetricPower (Jid f) n :=
  (MvPolynomial.basisMonomials (Fin r) (qrRbar f)).constr (qrRbar f) (monomialWord f n)

private lemma polynomialToWord_monomial {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin r → R) (n : ℕ) (e : Fin r →₀ ℕ) :
    polynomialToWord f n (MvPolynomial.monomial e 1) = monomialWord f n e := by
  change (MvPolynomial.basisMonomials (Fin r) (qrRbar f)).constr (qrRbar f)
    (monomialWord f n) ((MvPolynomial.basisMonomials (Fin r) (qrRbar f)) e) = _
  exact Module.Basis.constr_basis _ _ _ _

noncomputable def tupleWordMap {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin r → R) (n : ℕ) :
    ((Fin n → Fin r) →₀ qrRbar f) →ₗ[qrRbar f] Construction.SymmetricPower (Jid f) n :=
  Finsupp.linearCombination _ (fun t =>
    Construction.wordClass (Jid f) n (idealGenerator f ∘ t))

noncomputable def tuplePolynomialMap {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin r → R) (n : ℕ) :
    ((Fin n → Fin r) →₀ qrRbar f) →ₗ[qrRbar f] MvPolynomial (Fin r) (qrRbar f) :=
  Finsupp.linearCombination _ (fun t => MvPolynomial.monomial (tupleExponent t) 1)

private lemma polynomialToWord_tuplePolynomialMap {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin r → R) (n : ℕ) (w : (Fin n → Fin r) →₀ qrRbar f) :
    polynomialToWord f n (tuplePolynomialMap f n w) = tupleWordMap f n w := by
  induction w using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simpa only [map_add] using congrArg₂ (· + ·) ha hb
  | single t c =>
    simp only [tuplePolynomialMap, tupleWordMap, Finsupp.linearCombination_single,
      map_smul, polynomialToWord_monomial, monomialWord_tupleExponent]

private lemma tupleWordMap_surjective {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin r → R) (n : ℕ) : Function.Surjective (tupleWordMap f n) := by
  apply LinearMap.range_eq_top.mp
  rw [tupleWordMap, Finsupp.range_linearCombination]
  exact Submodule.span_eq_top_of_span_eq_top R _ _ <|
    Construction.span_generatorWord_eq_top (Jid f) (idealGenerator f)
      (span_idealGenerator_eq_top f) n

noncomputable def gradedPieceToTarget {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin r → R) (n : ℕ) :
    Construction.GradedPiece (Jid f) n →ₗ[qrRbar f] Target R f :=
  ((DirectSum.lof R ℕ (fun k => Tcomp R f k) n).comp
    (Submodule.mapQ _ _ (Submodule.inclusion (show Jid f ^ n ≤ JpowM R f n by
      simp [JpowM])) (by
      intro a ha
      change (a : R) ∈ JpowM R f (n + 1)
      simpa [JpowM] using ha))).extendScalarsOfSurjective Ideal.Quotient.mk_surjective

noncomputable def canonicalMapOverQuotient {R : Type u} [CommRing R]
    (I : Ideal R) (n : ℕ) :
    Construction.SymmetricPower I n →ₗ[R ⧸ I] Construction.GradedPiece I n :=
  (Construction.canonicalMap I n).extendScalarsOfSurjective Ideal.Quotient.mk_surjective

lemma polynomialCanonicalMap_tuple {R : Type u} [CommRing R] {r n : ℕ}
    (f : Fin r → R) (t : Fin n → Fin r) :
    associatedGradedMap f
      (MvPolynomial.monomial (tupleExponent t) 1) =
    gradedPieceToTarget f n (canonicalMapOverQuotient (Jid f) n
      (Construction.wordClass (Jid f) n (idealGenerator f ∘ t))) := by
  rw [← map_one (Ideal.Quotient.mk (Jid f)),
    polynomialQuasiRegularCanonicalMap_monomial]
  symm
  have hw : canonicalMapOverQuotient (Jid f) n
      (Construction.wordClass (Jid f) n (idealGenerator f ∘ t)) =
      Construction.productClass (Jid f) n (idealGenerator f ∘ t) :=
    Construction.productMap_word (Jid f) (idealGenerator f ∘ t)
  rw [hw]
  dsimp only [gradedPieceToTarget, canonicalMapOverQuotient,
    LinearMap.extendScalarsOfSurjective_apply]
  change (DirectSum.lof R ℕ (fun k => Tcomp R f k) n)
    (Submodule.Quotient.mk ⟨∏ j, f (t j), _⟩) = imgTargetLin f (tupleExponent t) 1
  apply target_mk_eq_of_val_eq f (tupleExponent_degree t).symm
  change (∏ j, f (t j)) = fpow f (tupleExponent t) • (1 : R)
  simp only [fpow_tupleExponent, smul_eq_mul, mul_one]

lemma polynomialCanonicalMap_tuplePolynomialMap {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin r → R) (n : ℕ) (w : (Fin n → Fin r) →₀ qrRbar f) :
    associatedGradedMap f (tuplePolynomialMap f n w) =
      gradedPieceToTarget f n (canonicalMapOverQuotient (Jid f) n (tupleWordMap f n w)) := by
  induction w using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simpa only [map_add] using congrArg₂ (· + ·) ha hb
  | single t c =>
    simp only [tuplePolynomialMap, tupleWordMap, Finsupp.linearCombination_single, map_smul]
    congr 1
    exact polynomialCanonicalMap_tuple f t

lemma canonicalMap_injective_of_polynomialCanonicalMap_injective
    {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)
    (hf : Function.Injective (associatedGradedMap f)) (n : ℕ) :
    Function.Injective (Construction.canonicalMap (Jid f) n) := by
  have hz : ∀ z, Construction.canonicalMap (Jid f) n z = 0 → z = 0 := by
    intro z hz
    obtain ⟨w, rfl⟩ := tupleWordMap_surjective f n z
    have h : associatedGradedMap f (tuplePolynomialMap f n w) = 0 := by
      rw [polynomialCanonicalMap_tuplePolynomialMap]
      change gradedPieceToTarget f n (Construction.canonicalMap (Jid f) n _) = 0
      rw [hz, map_zero]
    have hp : tuplePolynomialMap f n w = 0 := hf (h.trans (map_zero _).symm)
    rw [← polynomialToWord_tuplePolynomialMap, hp, map_zero]
  intro a b hab
  apply sub_eq_zero.mp
  apply hz
  simpa only [map_sub, sub_eq_zero] using hab

lemma conormalSymmetricToGradedMap_isIso_of_local_kernel_on_support
    (X : RingedSpace.{u}) (J : (Stacks.RingedSpace.structureSheafModule X).Submodule) (n : ℕ)
    (h : ∀ (U : Opens X) (z : Construction.SymmetricPower (sectionIdeal X J (op U)) n),
      Construction.canonicalMap (sectionIdeal X J (op U)) n z = 0 →
      ∀ (x : X), x ∈ U → x ∈ idealQuotientSupport X J →
      ∃ (V : Opens X) (_ : x ∈ V) (i : V ⟶ U),
        Construction.symmetricMap _ _ (X.presheaf.map i.op).hom
          (sectionIdeal_map X J i.op) n z = 0) :
    IsIso (conormalSymmetricToGradedMap X J n) := by
  apply (conormalSymmetricToGradedMap_isIso_iff_local_kernel X J n).mpr
  intro U z hz x hx
  by_cases hxS : x ∈ idealQuotientSupport X J
  · exact h U z hz x hx hxS
  · obtain ⟨W, hxW, hW⟩ := exists_one_mem_of_notMem_support X J x hxS
    have h1 : (1 : X.presheaf.obj (op (U ⊓ W))) ∈ J.obj (op (U ⊓ W)) := by
      have h' := J.toSubmodule.map_mem (homOfLE (show U ⊓ W ≤ W from inf_le_right)).op hW
      change X.presheaf.map (homOfLE inf_le_right).op 1 ∈ _ at h'
      simpa only [map_one] using h'
    exact ⟨U ⊓ W, ⟨hx, hxW⟩, homOfLE inf_le_left,
      Construction.wordClass_eq_zero_of_one_mem _ h1 _⟩

private lemma exists_local_cotangentBasis_of_isQuasiRegularIdealSheaf
    (X : RingedSpace.{u}) (J : (Stacks.RingedSpace.structureSheafModule X).Submodule)
    (h : IsQuasiRegularIdealSheaf X J) (x : X)
    (hx : x ∈ idealQuotientSupport X J) :
    ∃ (U : Opens X) (_ : x ∈ U) (r : ℕ) (f : Fin r → X.presheaf.obj (op U)),
      IsGeneratedByOn X J U f ∧
      ∀ y : X.restrict U.isOpenEmbedding,
        Nonempty (Module.Basis (Fin r)
          (qrRbar (QuasiRegular.germSequence (X.restrict U.isOpenEmbedding)
            (fun i => sectionOnRestriction X U (f i)) y))
          (Jid (QuasiRegular.germSequence (X.restrict U.isOpenEmbedding)
            (fun i => sectionOnRestriction X U (f i)) y)).Cotangent) := by
  obtain ⟨U, hxU, r, f, hqr, hgen⟩ := h x hx
  refine ⟨U, hxU, r, f, hgen, fun y => ?_⟩
  exact ⟨cotangentBasis _ ((quasiRegularMap_isIso_iff _ _).mp hqr y).1⟩

lemma coefficients_mem_of_sum_mem_square {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin r → R)
    (hf : Function.Injective (associatedGradedMap f))
    (a : Fin r → R) (ha : ∑ i, a i * f i ∈ Jid f ^ 2) : ∀ i, a i ∈ Jid f := by
  have hs : (Jid f).toCotangent (∑ i, a i • idealGenerator f i) = 0 := by
    apply (Ideal.toCotangent_eq_zero _ _).mpr
    simpa only [Submodule.coe_sum, Submodule.coe_smul, smul_eq_mul] using ha
  have hs' : ∑ i, (Ideal.Quotient.mk (Jid f) (a i)) •
      (Jid f).toCotangent (idealGenerator f i) = 0 := by
    change ∑ i, (algebraMap R (R ⧸ Jid f) (a i)) •
      (Jid f).toCotangent (idealGenerator f i) = 0
    simpa only [map_sum, map_smul, algebraMap_smul] using hs
  have hli := cotangent_generators_linearIndependent f hf
  intro i
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  exact (linearIndependent_iff').mp hli Finset.univ
    (fun i => Ideal.Quotient.mk (Jid f) (a i)) hs' i (Finset.mem_univ i)

private lemma coefficients_mem_generatedIdeal_of_sum_mem_square (X : RingedSpace.{u})
    {r : ℕ} (f : Fin r → X.presheaf.obj (op (⊤ : Opens X)))
    (hf : IsIso (QuasiRegular.quasiRegularMap X f).hom)
    (U : Opens X) (a : Fin r → X.presheaf.obj (op U))
    (ha : ∑ i, a i * X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (f i) ∈
      sectionIdeal X (QuasiRegular.generatedIdeal X f) (op U) ^ 2) :
    ∀ i, a i ∈ (QuasiRegular.generatedIdeal X f).obj (op U) := by
  intro i
  apply ((QuasiRegular.quasiRegularMap X f).ideal_sections U (a i)).mpr
  intro x hx
  have hI : sectionIdeal X (QuasiRegular.generatedIdeal X f) (op U) ≤
      (Jid (QuasiRegular.germSequence X f x)).comap (X.presheaf.germ U x hx).hom := by
    intro s hs
    exact ((QuasiRegular.quasiRegularMap X f).ideal_sections U s).mp hs x hx
  have h := Construction.map_pow_mem _ _ _ hI ha
  have hs : ∑ j, (X.presheaf.germ U x hx (a j)) *
      QuasiRegular.germSequence X f x j ∈ Jid (QuasiRegular.germSequence X f x) ^ 2 := by
    simpa only [map_sum, map_mul, TopCat.Presheaf.germ_res_apply,
      QuasiRegular.germSequence] using h
  exact coefficients_mem_of_sum_mem_square _
    ((quasiRegularMap_isIso_iff X f).mp hf x).1 _ hs i

end Stacks.AlgebraicGeometry.RegularIdealSheaf.Conormal

end
