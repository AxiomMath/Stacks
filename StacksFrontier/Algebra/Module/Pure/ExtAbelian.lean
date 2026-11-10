module

public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import StacksFrontier.Algebra.Module.Pure.ExtResolution

/-!
# Pure extensions as extension groups in an abelian category

Let `T : Mod_A ⥤ 𝒞` be a fully faithful additive functor into an abelian category which carries
universally exact sequences of `A`-modules to exact sequences, universally injective maps to
monomorphisms and pure injective modules to injective objects. Then a pure injective resolution
`N ⟶ Iᐧ` is carried by `T` to an injective resolution of `T N` in `𝒞`, and the pure extension
modules are the extension groups in `𝒞`:

`Pext^i_A(M, N) ≅ Ext^i_𝒞(T M, T N)`,

naturally in `M` and `N`. The class of a cocycle `f : M → Iⁱ` of `Hom_A(M, Iᐧ)` goes to the class
of the cocycle `T f : T M ⟶ T Iⁱ` of the injective resolution `T Iᐧ`.

## Main definitions

* `Module.injectiveResolutionOfPure` — the image under `T` of a pure injective resolution, as an
  injective resolution in `𝒞`.
* `Module.pureExtAddEquivExt` — `Pext^i_A(M, N) ≃+ Ext^i_𝒞(T M, T N)` for every `i`.

## Main results

* `Module.pureExtAddEquivExt_naturality_left`, `Module.pureExtAddEquivExt_naturality_right` —
  naturality in the two variables. The action of `Pext` in the first variable is precomposition
  on `Hom_A(-, Iᐧ)`, and in the second variable it is postcomposition with any comparison map of
  the chosen pure injective resolutions lying over the given module map (such maps exist and are
  unique up to homotopy by [Stacks, Tag 0704]); the squares commute for every such comparison map.

## References

* [Stacks Project, Tag 0705](https://stacks.math.columbia.edu/tag/0705)
* [Stacks Project, Tag 0708](https://stacks.math.columbia.edu/tag/0708)
* [Stacks Project, Tag 0709](https://stacks.math.columbia.edu/tag/0709)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe w u v t s

namespace Module

variable {A : Type u} [CommRing A] {C : Type t} [Category.{s} C] [Abelian C]
  (T : ModuleCat.{v} A ⥤ C) [T.Additive]
  (hinj : ∀ I : ModuleCat.{v} A, Module.PureInjective A I → CategoryTheory.Injective (T.obj I))
  (hmono : ∀ {X Y : ModuleCat.{v} A} (f : X ⟶ Y), UniversallyInjective f.hom → Mono (T.map f))
  (hexact : ∀ {X Y Z : ModuleCat.{v} A} (f : X ⟶ Y) (g : Y ⟶ Z) (w : T.map f ≫ T.map g = 0),
    Function.Exact f.hom g.hom →
    (∀ (Q : Type v) [AddCommGroup Q] [Module A Q],
      Function.Exact (f.hom.rTensor Q) (g.hom.rTensor Q)) →
    (ShortComplex.mk (T.map f) (T.map g) w).Exact)

section Resolution

/-- The augmentation of a pure injective resolution, composed with the first differential, is
zero, as a statement about morphisms of modules. -/
lemma ofHom_augmentation_comp_d {N : ModuleCat.{v} A} {I : CochainComplex (ModuleCat.{v} A) ℕ}
    {η : N →ₗ[A] I.X 0} (hI : PureInjectiveResolution.IsPureInjectiveResolution I η) :
    ModuleCat.ofHom η ≫ I.d 0 1 = 0 :=
  ModuleCat.hom_ext hI.exact_zero.linearMap_comp_eq_zero

include hinj hmono hexact in
/-- The image `T N ⟶ T Iᐧ` of a pure injective resolution `N ⟶ Iᐧ`, as an injective resolution
in `𝒞`. -/
def injectiveResolutionOfPure {N : ModuleCat.{v} A} {I : CochainComplex (ModuleCat.{v} A) ℕ}
    {η : N →ₗ[A] I.X 0} (hI : PureInjectiveResolution.IsPureInjectiveResolution I η) :
    InjectiveResolution (T.obj N) where
  cocomplex := (T.mapHomologicalComplex _).obj I
  injective n := hinj _ (hI.pureInjective n)
  ι := (CochainComplex.fromSingle₀Equiv _ _).symm ⟨T.map (ModuleCat.ofHom η), by
    change T.map _ ≫ T.map (I.d 0 1) = 0
    rw [← T.map_comp, ofHom_augmentation_comp_d hI, T.map_zero]⟩
  quasiIso := ⟨fun n ↦ by
    cases n with
    | zero =>
      rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
      · refine (ShortComplex.exact_and_mono_f_iff_of_iso ?_).2
          ⟨hexact (ModuleCat.ofHom η) (I.d 0 1)
            (by rw [← T.map_comp, ofHom_augmentation_comp_d hI, T.map_zero])
            hI.exact_zero hI.baseChange_exact_zero,
            hmono _ hI.universallyInjective_augmentation⟩
        exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
          (by simp only [Functor.mapHomologicalComplex_obj_X, Functor.mapHomologicalComplex_obj_d,
                CochainComplex.fromSingle₀Equiv, Equiv.symm_mk, Equiv.coe_fn_mk, ModuleCat.of_coe,
                Iso.refl_hom, HomologicalComplex.shortComplexFunctor'_map_τ₂,
                HomologicalComplex.mkHomFromSingle_f, CochainComplex.single₀_obj_zero,
                CochainComplex.single₀ObjXSelf, Category.id_comp]
              exact (Category.id_comp _).trans (Category.comp_id _).symm)
          ((Category.id_comp _).trans (Category.comp_id _).symm)
      all_goals first | rfl |
        exact HomologicalComplex.shape ((T.mapHomologicalComplex _).obj I) 0 0 (by decide)
    | succ n =>
      rw [quasiIsoAt_iff_exactAt _ (n + 1) (CochainComplex.exactAt_succ_single_obj _ _),
        HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)]
      exact hexact (I.d n (n + 1)) (I.d (n + 1) (n + 2)) _ (hI.exact n)
        (fun Q _ _ ↦ hI.baseChange_exact Q n)⟩

/-- The degree-zero component of the augmentation of `Module.injectiveResolutionOfPure` is `T`
applied to the augmentation `N ⟶ I⁰`. -/
lemma injectiveResolutionOfPure_ι_f_zero {N : ModuleCat.{v} A}
    {I : CochainComplex (ModuleCat.{v} A) ℕ} {η : N →ₗ[A] I.X 0}
    (hI : PureInjectiveResolution.IsPureInjectiveResolution I η) :
    (injectiveResolutionOfPure T hinj hmono hexact hI).ι.f 0 = T.map (ModuleCat.ofHom η) :=
  CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

end Resolution

end Module

namespace CategoryTheory.InjectiveResolution

variable {C : Type*} [Category* C] [Abelian C] [HasExt.{w} C] {X Y : C} (R : InjectiveResolution Y)

/-- The class `R.extMk f` of a degree-zero cocycle `f : X ⟶ R⁰` vanishes only when `f` does. -/
lemma extMk_zero_eq_zero_iff (f : X ⟶ R.cocomplex.X 0) (hf : f ≫ R.cocomplex.d 0 1 = 0) :
    R.extMk f 1 rfl hf = 0 ↔ f = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by subst h; exact R.extMk_zero 1 rfl⟩
  simp only [← R.extEquivCohomologyClass.apply_eq_iff_eq,
    extEquivCohomologyClass_extMk, extEquivCohomologyClass_zero,
    CochainComplex.HomComplex.CohomologyClass.mk_eq_zero_iff] at h
  rw [CochainComplex.HomComplex.Cocycle.fromSingleMk_mem_coboundaries_iff _ _ _ _ _ (-1)
    (by simp)] at h
  obtain ⟨g, hg⟩ := h
  have hz : g = 0 :=
    (CochainComplex.isZero_of_isStrictlyGE R.cochainComplex 0 (-1) (by simp)).eq_of_tgt _ _
  rw [hz, zero_comp] at hg
  exact (cancel_mono _).1 (hg.symm.trans zero_comp.symm)

end CategoryTheory.InjectiveResolution

namespace Module

variable {A : Type u} [CommRing A] {C : Type t} [Category.{s} C] [Abelian C]
  (T : ModuleCat.{v} A ⥤ C) [T.Additive]
  (hinj : ∀ I : ModuleCat.{v} A, Module.PureInjective A I → CategoryTheory.Injective (T.obj I))
  (hmono : ∀ {X Y : ModuleCat.{v} A} (f : X ⟶ Y), UniversallyInjective f.hom → Mono (T.map f))
  (hexact : ∀ {X Y Z : ModuleCat.{v} A} (f : X ⟶ Y) (g : Y ⟶ Z) (w : T.map f ≫ T.map g = 0),
    Function.Exact f.hom g.hom →
    (∀ (Q : Type v) [AddCommGroup Q] [Module A Q],
      Function.Exact (f.hom.rTensor Q) (g.hom.rTensor Q)) →
    (ShortComplex.mk (T.map f) (T.map g) w).Exact)

section Ext

variable [HasExt.{w} C] (hT : T.FullyFaithful)
  {M N : ModuleCat.{v} A} {I : CochainComplex (ModuleCat.{v} A) ℕ} {η : N →ₗ[A] I.X 0}
  (hI : PureInjectiveResolution.IsPureInjectiveResolution I η)

/-- A cocycle of `Hom_A(M, Iᐧ)` in degree `n`, read as a morphism of modules `M ⟶ Iⁿ`. -/
def cocycleHom (n : ℕ) (f : LinearMap.ker ((homComplex M I).d n (n + 1)).hom) : M ⟶ I.X n :=
  ModuleCat.ofHom (show M →ₗ[A] I.X n from f.1)

/-- The underlying linear map of `Module.cocycleHom n f` is the cocycle `f` itself. -/
lemma cocycleHom_hom (n : ℕ) (f : LinearMap.ker ((homComplex M I).d n (n + 1)).hom) :
    (cocycleHom n f).hom = (show M →ₗ[A] I.X n from f.1) := rfl

/-- A cocycle of `Hom_A(M, Iᐧ)` is killed by the differential of `Iᐧ`. -/
lemma cocycleHom_comp_d (n : ℕ) (f : LinearMap.ker ((homComplex M I).d n (n + 1)).hom) :
    cocycleHom n f ≫ I.d n (n + 1) = 0 :=
  ModuleCat.hom_ext ((LinearMap.congr_fun (homComplex_d (↑M) I n) f.1).symm.trans f.2)

/-- `Module.cocycleHom n` sends a sum of cocycles to the sum of the morphisms. -/
lemma cocycleHom_add (n : ℕ) (f g : LinearMap.ker ((homComplex M I).d n (n + 1)).hom) :
    cocycleHom n (f + g) = cocycleHom n f + cocycleHom n g := rfl

/-- `Module.cocycleHom n` sends the zero cocycle to the zero morphism. -/
lemma cocycleHom_zero (n : ℕ) :
    cocycleHom n (0 : LinearMap.ker ((homComplex M I).d n (n + 1)).hom) = 0 := rfl

/-- `Module.cocycleHom n` is injective. -/
lemma cocycleHom_injective (n : ℕ) :
    Function.Injective (cocycleHom (M := M) (I := I) n) :=
  fun _ _ h ↦ Subtype.ext (congrArg ModuleCat.Hom.hom h)

include hinj hmono hexact in
/-- The class in `Ext^n_𝒞(T M, T N)` of the cocycle `T f` of the injective resolution `T Iᐧ` of
`T N`, for a cocycle `f : M → Iⁿ` of `Hom_A(M, Iᐧ)`. -/
def cyclesToExt (n : ℕ) :
    LinearMap.ker ((homComplex M I).d n (n + 1)).hom →+ Ext (T.obj M) (T.obj N) n where
  toFun f := (injectiveResolutionOfPure T hinj hmono hexact hI).extMk
    (T.map (cocycleHom n f)) (n + 1) rfl (by
      change _ ≫ T.map (I.d n (n + 1)) = 0
      rw [← T.map_comp, cocycleHom_comp_d, T.map_zero])
  map_zero' := by
    simp only [cocycleHom_zero, T.map_zero]
    exact (injectiveResolutionOfPure T hinj hmono hexact hI).extMk_zero (n + 1) rfl
  map_add' f g := by
    simp only [cocycleHom_add, T.map_add]
    exact ((injectiveResolutionOfPure T hinj hmono hexact hI).add_extMk _ _ _ _ _ _).symm

/-- `Module.cyclesToExt` sends a cocycle `f` to the class of the cocycle `T f` of the injective
resolution `Module.injectiveResolutionOfPure`. -/
lemma cyclesToExt_apply (n : ℕ) (f : LinearMap.ker ((homComplex M I).d n (n + 1)).hom) :
    cyclesToExt T hinj hmono hexact hI n f =
      (injectiveResolutionOfPure T hinj hmono hexact hI).extMk
        (T.map (cocycleHom n f)) (n + 1) rfl (by
          change _ ≫ T.map (I.d n (n + 1)) = 0
          rw [← T.map_comp, cocycleHom_comp_d, T.map_zero]) := rfl

/-- If `g : F M ⟶ F Iⁿ` composed with `F dⁿ` is `F z`, for a fully faithful functor `F`, then the
preimage of `g` is sent by the differential of `Hom_A(M, Iᐧ)` to `z`. -/
private lemma homComplex_d_preimage {D : Type*} [Category D] {F : ModuleCat.{v} A ⥤ D}
    (hF : F.FullyFaithful) {n : ℕ} (g : F.obj M ⟶ F.obj (I.X n)) (z : M ⟶ I.X (n + 1))
    (h : g ≫ F.map (I.d n (n + 1)) = F.map z) :
    ((homComplex M I).d n (n + 1)).hom (hF.preimage g).hom = z.hom := by
  have hg : hF.preimage g ≫ I.d n (n + 1) = z :=
    hF.map_injective (by rwa [F.map_comp, hF.map_preimage])
  exact (LinearMap.congr_fun (homComplex_d (↑M) I n) _).trans (congrArg ModuleCat.Hom.hom hg)

include hT in
/-- Every class of `Ext^n_𝒞(T M, T N)` is the class of a cocycle of `Hom_A(M, Iᐧ)`. -/
lemma cyclesToExt_surjective (n : ℕ) :
    Function.Surjective (cyclesToExt T hinj hmono hexact hI (M := M) n) := by
  intro e
  obtain ⟨f', hf', rfl⟩ :=
    (injectiveResolutionOfPure T hinj hmono hexact hI).extMk_surjective e (n + 1) rfl
  let f'' : T.obj M ⟶ T.obj (I.X n) := f'
  refine ⟨⟨(hT.preimage f'').hom, LinearMap.mem_ker.2 ?_⟩, ?_⟩
  · exact homComplex_d_preimage hT f'' 0 (by rwa [T.map_zero])
  · rw [cyclesToExt_apply]
    congr 1
    exact hT.map_preimage f''

include hT in
/-- The class of a cocycle `f : M → Iⁿ` vanishes exactly when `f` is the differential of a
cochain `M → Iⁿ⁻¹`; in degree zero, where the incoming differential of `Hom_A(M, Iᐧ)` is zero,
exactly when `f = 0`. -/
lemma cyclesToExt_eq_zero_iff (n : ℕ) (f : LinearMap.ker ((homComplex M I).d n (n + 1)).hom) :
    cyclesToExt T hinj hmono hexact hI n f = 0 ↔
      ∃ y : (homComplex M I).X (n - 1), ((homComplex M I).d (n - 1) n).hom y = f.1 := by
  rw [cyclesToExt_apply]
  cases n with
  | zero =>
    refine (InjectiveResolution.extMk_zero_eq_zero_iff _ _ _).trans ?_
    have hd : (homComplex M I).d (0 - 1) 0 = 0 := HomologicalComplex.shape _ _ _ (by decide)
    constructor
    · intro h
      refine ⟨0, ?_⟩
      have h' : cocycleHom 0 f = cocycleHom 0 0 :=
        hT.map_injective (h.trans (T.map_zero _ _).symm)
      rw [map_zero, cocycleHom_injective 0 h']
      rfl
    · rintro ⟨y, hy⟩
      have hf : f = 0 := by
        apply Subtype.ext
        rw [← hy, hd]
        rfl
      subst hf
      exact T.map_zero _ _
  | succ p =>
    refine (InjectiveResolution.extMk_eq_zero_iff _ _ _ _ _ p rfl).trans ?_
    constructor
    · rintro ⟨g, hg⟩
      let g' : T.obj M ⟶ T.obj (I.X p) := g
      exact ⟨(hT.preimage g').hom, homComplex_d_preimage hT g' _ hg⟩
    · rintro ⟨y, hy⟩
      refine ⟨T.map (ModuleCat.ofHom (show M →ₗ[A] I.X p from y)), ?_⟩
      change T.map _ ≫ T.map (I.d p (p + 1)) = _
      rw [← T.map_comp]
      congr 1
      apply ModuleCat.hom_ext
      exact (LinearMap.congr_fun (homComplex_d (↑M) I p) y).symm.trans hy

/-! ### Cohomology classes of `Hom_A(M, Iᐧ)` -/

/-- For the complex shape `ComplexShape.up ℕ`, the index before `n` is `n - 1`. -/
lemma prev_up_nat (n : ℕ) : (ComplexShape.up ℕ).prev n = n - 1 := by
  cases n <;> simp

/-- The inclusion of the degree-`n` cocycles of `Hom_A(M, Iᐧ)`, as a morphism of modules. -/
abbrev cocycleInclusion (M : ModuleCat.{v} A) (I : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ) :
    ModuleCat.of A (LinearMap.ker ((homComplex M I).d n (n + 1)).hom) ⟶ (homComplex M I).X n :=
  ModuleCat.ofHom (LinearMap.ker ((homComplex M I).d n (n + 1)).hom).subtype

/-- A cocycle of `Hom_A(M, Iᐧ)` as an element of the abstract cycles of the complex. -/
def cocycleLift (M : ModuleCat.{v} A) (I : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ) :
    ModuleCat.of A (LinearMap.ker ((homComplex M I).d n (n + 1)).hom) ⟶
      (homComplex M I).cycles n :=
  (homComplex M I).liftCycles (cocycleInclusion M I n) (n + 1) (by simp) (by
      apply ModuleCat.hom_ext
      ext f
      exact f.2)

/-- `Module.cocycleLift` followed by the inclusion of the cycles is the inclusion of the
cocycles. -/
@[reassoc (attr := simp)]
lemma cocycleLift_i (M : ModuleCat.{v} A) (I : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ) :
    cocycleLift M I n ≫ (homComplex M I).iCycles n = cocycleInclusion M I n :=
  HomologicalComplex.liftCycles_i _ _ _ _ _

/-- The cohomology class of a cocycle of `Hom_A(M, Iᐧ)`, as a map of modules from the cocycles to
the cohomology in degree `n`. -/
def cocycleClass (M : ModuleCat.{v} A) (I : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ) :
    ModuleCat.of A (LinearMap.ker ((homComplex M I).d n (n + 1)).hom) ⟶
      (homComplex M I).homology n :=
  cocycleLift M I n ≫ (homComplex M I).homologyπ n

/-- The cohomology of `Hom_A(M, Iᐧ)` in degree `n` in the explicit form
`ker dⁿ / im dⁿ⁻¹`. -/
def homologyAddEquivQuotient (M : ModuleCat.{v} A) (I : CochainComplex (ModuleCat.{v} A) ℕ)
    (n : ℕ) :
    (homComplex M I).homology n ≃+
      (LinearMap.ker ((homComplex M I).sc' (n - 1) n (n + 1)).g.hom ⧸
        LinearMap.range ((homComplex M I).sc' (n - 1) n (n + 1)).moduleCatToCycles) :=
  ((homComplex M I).homologyIsoSc' (n - 1) n (n + 1) (prev_up_nat n) (by simp) ≪≫
    ((homComplex M I).sc' (n - 1) n (n + 1)).moduleCatHomologyIso).toLinearEquiv.toAddEquiv

/-- `Module.cocycleLift` followed by the identification of the cycles in degree `n` with the
kernel of the differential `dⁿ` is the identity. -/
lemma cocycleLift_comp_cyclesIso (M : ModuleCat.{v} A) (I : CochainComplex (ModuleCat.{v} A) ℕ)
    (n : ℕ) :
    cocycleLift M I n ≫
      ((homComplex M I).cyclesIsoSc' (n - 1) n (n + 1) (prev_up_nat n) (by simp)).hom ≫
        ((homComplex M I).sc' (n - 1) n (n + 1)).moduleCatCyclesIso.hom =
      𝟙 (ModuleCat.of A (LinearMap.ker ((homComplex M I).d n (n + 1)).hom)) := by
  apply (cancel_mono ((homComplex M I).sc' (n - 1) n (n + 1)).moduleCatLeftHomologyData.i).1
  simp only [Category.assoc, ShortComplex.moduleCatCyclesIso_hom_i,
    HomologicalComplex.cyclesIsoSc'_hom_iCycles]
  exact (cocycleLift_i M I n).trans (Category.id_comp _).symm

/-- `Module.cocycleClass` followed by the identification of the cohomology in degree `n` with
`ker dⁿ / im dⁿ⁻¹` is the projection of the cocycles onto this quotient. -/
lemma cocycleClass_comp_iso (M : ModuleCat.{v} A) (I : CochainComplex (ModuleCat.{v} A) ℕ)
    (n : ℕ) :
    cocycleClass M I n ≫
      ((homComplex M I).homologyIsoSc' (n - 1) n (n + 1) (prev_up_nat n) (by simp) ≪≫
        ((homComplex M I).sc' (n - 1) n (n + 1)).moduleCatHomologyIso).hom =
      ((homComplex M I).sc' (n - 1) n (n + 1)).moduleCatLeftHomologyData.π := by
  simp only [cocycleClass, Iso.trans_hom, Category.assoc,
    HomologicalComplex.π_homologyIsoSc'_hom_assoc, ShortComplex.π_moduleCatCyclesIso_hom]
  simp only [← Category.assoc]
  rw [Category.assoc (cocycleLift M I n), cocycleLift_comp_cyclesIso]
  exact Category.id_comp _

/-- In the explicit description `ker dⁿ / im dⁿ⁻¹`, the class of a cocycle is its residue class
modulo the coboundaries. -/
lemma homologyAddEquivQuotient_cocycleClass (M : ModuleCat.{v} A)
    (I : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ)
    (f : LinearMap.ker ((homComplex M I).d n (n + 1)).hom) :
    homologyAddEquivQuotient M I n ((cocycleClass M I n).hom f) =
      Submodule.Quotient.mk (p := LinearMap.range
        ((homComplex M I).sc' (n - 1) n (n + 1)).moduleCatToCycles) f :=
  congrArg (fun φ ↦ φ.hom f) (cocycleClass_comp_iso M I n)

/-- Every cohomology class of `Hom_A(M, Iᐧ)` is the class of a cocycle. -/
lemma cocycleClass_surjective (M : ModuleCat.{v} A) (I : CochainComplex (ModuleCat.{v} A) ℕ)
    (n : ℕ) : Function.Surjective (cocycleClass M I n).hom := by
  intro x
  obtain ⟨f, hf⟩ := Submodule.Quotient.mk_surjective _ (homologyAddEquivQuotient M I n x)
  exact ⟨f, (homologyAddEquivQuotient M I n).injective
    ((homologyAddEquivQuotient_cocycleClass M I n f).trans hf)⟩

/-- Precomposition with `g : M' ⟶ M` on cocycles. -/
def cocyclePrecomp {M M' : ModuleCat.{v} A} (g : M' ⟶ M) (I : CochainComplex (ModuleCat.{v} A) ℕ)
    (n : ℕ) :
    ModuleCat.of A (LinearMap.ker ((homComplex M I).d n (n + 1)).hom) ⟶
      ModuleCat.of A (LinearMap.ker ((homComplex M' I).d n (n + 1)).hom) :=
  ModuleCat.ofHom (((homComplexPrecomp g.hom I).f n).hom.restrict (fun f hf ↦ by
    rw [LinearMap.mem_ker] at hf ⊢
    have h := congrArg (fun φ ↦ φ.hom f) ((homComplexPrecomp g.hom I).comm n (n + 1))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    rw [h, hf, map_zero]))

/-- The class of a cocycle is natural for a map of complexes `Hom_A(M, Iᐧ) ⟶ Hom_A(M', Jᐧ)`
inducing `ψ` on cocycles. -/
private lemma cocycleClass_comp_homologyMap {M M' : ModuleCat.{v} A}
    {I J : CochainComplex (ModuleCat.{v} A) ℕ} (φ : homComplex M I ⟶ homComplex M' J) (n : ℕ)
    (ψ : ModuleCat.of A (LinearMap.ker ((homComplex M I).d n (n + 1)).hom) ⟶
      ModuleCat.of A (LinearMap.ker ((homComplex M' J).d n (n + 1)).hom))
    (hψ : ψ ≫ cocycleInclusion M' J n = cocycleInclusion M I n ≫ φ.f n) :
    cocycleClass M I n ≫ HomologicalComplex.homologyMap φ n = ψ ≫ cocycleClass M' J n := by
  dsimp only [cocycleClass]
  rw [Category.assoc, HomologicalComplex.homologyπ_naturality, ← Category.assoc,
    ← Category.assoc]
  congr 1
  apply (cancel_mono ((homComplex M' J).iCycles n)).1
  simp only [Category.assoc, HomologicalComplex.cyclesMap_i, cocycleLift_i, cocycleLift_i_assoc]
  exact hψ.symm

/-- The class of a cocycle is natural in the first variable. -/
lemma cocycleClass_naturality_left {M M' : ModuleCat.{v} A} (g : M' ⟶ M)
    (I : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ) :
    cocycleClass M I n ≫ HomologicalComplex.homologyMap (homComplexPrecomp g.hom I) n =
      cocyclePrecomp g I n ≫ cocycleClass M' I n := by
  exact cocycleClass_comp_homologyMap _ n _ rfl

/-- Postcomposition with a map of complexes `F : Iᐧ ⟶ Jᐧ` on cocycles. -/
def cocyclePostcomp (M : ModuleCat.{v} A) {I J : CochainComplex (ModuleCat.{v} A) ℕ} (F : I ⟶ J)
    (n : ℕ) :
    ModuleCat.of A (LinearMap.ker ((homComplex M I).d n (n + 1)).hom) ⟶
      ModuleCat.of A (LinearMap.ker ((homComplex M J).d n (n + 1)).hom) :=
  ModuleCat.ofHom (((homComplexPostcomp M F).f n).hom.restrict (fun f hf ↦ by
    rw [LinearMap.mem_ker] at hf ⊢
    have h := congrArg (fun φ ↦ φ.hom f) ((homComplexPostcomp M F).comm n (n + 1))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    rw [h, hf, map_zero]))

/-- The class of a cocycle is natural in the second variable. -/
lemma cocycleClass_naturality_right (M : ModuleCat.{v} A)
    {I J : CochainComplex (ModuleCat.{v} A) ℕ} (F : I ⟶ J) (n : ℕ) :
    cocycleClass M I n ≫ HomologicalComplex.homologyMap (homComplexPostcomp M F) n =
      cocyclePostcomp M F n ≫ cocycleClass M J n := by
  exact cocycleClass_comp_homologyMap _ n _ rfl

/-- A cocycle has zero class exactly when it is a coboundary. -/
lemma cocycleClass_eq_zero_iff (M : ModuleCat.{v} A) (I : CochainComplex (ModuleCat.{v} A) ℕ)
    (n : ℕ) (f : LinearMap.ker ((homComplex M I).d n (n + 1)).hom) :
    (cocycleClass M I n).hom f = 0 ↔
      ∃ y : (homComplex M I).X (n - 1), ((homComplex M I).d (n - 1) n).hom y = f.1 := by
  rw [← (homologyAddEquivQuotient M I n).map_eq_zero_iff, homologyAddEquivQuotient_cocycleClass]
  exact (Submodule.Quotient.mk_eq_zero _).trans
    ⟨fun ⟨y, hy⟩ ↦ ⟨y, congrArg Subtype.val hy⟩, fun ⟨y, hy⟩ ↦ ⟨y, Subtype.ext hy⟩⟩

include hT in
/-- The canonical map from the cohomology of `Hom_A(M, Iᐧ)` to `Ext_𝒞(T M, T N)`, sending the
class of a cocycle `f` to the class of the cocycle `T f` of the injective resolution `T Iᐧ`. -/
def homologyToExt (n : ℕ) : (homComplex M I).homology n →+ Ext (T.obj M) (T.obj N) n :=
  AddMonoidHom.liftOfRightInverse (cocycleClass M I n).hom.toAddMonoidHom
    (Function.surjInv (cocycleClass_surjective M I n))
    (Function.rightInverse_surjInv (cocycleClass_surjective M I n))
    ⟨cyclesToExt T hinj hmono hexact hI n, fun f hf ↦ by
      rw [AddMonoidHom.mem_ker] at hf ⊢
      exact (cyclesToExt_eq_zero_iff T hinj hmono hexact hT hI n f).2
        ((cocycleClass_eq_zero_iff M I n f).1 hf)⟩

/-- The canonical map sends the class of a cocycle `f` to the class of `T f`. -/
lemma homologyToExt_cocycleClass (n : ℕ) (f : LinearMap.ker ((homComplex M I).d n (n + 1)).hom) :
    homologyToExt T hinj hmono hexact hT hI n ((cocycleClass M I n).hom f) =
      cyclesToExt T hinj hmono hexact hI n f :=
  AddMonoidHom.liftOfRightInverse_comp_apply _ _ _ _ f

/-- `Module.homologyToExt` is bijective. -/
lemma homologyToExt_bijective (n : ℕ) :
    Function.Bijective (homologyToExt T hinj hmono hexact hT hI (M := M) n) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, fun e ↦ ?_⟩
  · obtain ⟨f, rfl⟩ := cocycleClass_surjective M I n x
    rw [homologyToExt_cocycleClass] at hx
    exact (cocycleClass_eq_zero_iff M I n f).2
      ((cyclesToExt_eq_zero_iff T hinj hmono hexact hT hI n f).1 hx)
  · obtain ⟨f, rfl⟩ := cyclesToExt_surjective T hinj hmono hexact hT hI n e
    exact ⟨_, homologyToExt_cocycleClass T hinj hmono hexact hT hI n f⟩

/-- The cohomology of `Hom_A(M, Iᐧ)` is `Ext_𝒞(T M, T N)`, for every pure injective resolution
`N ⟶ Iᐧ`: the class of a cocycle `f` corresponds to the class of `T f`. -/
def homologyAddEquivExt (n : ℕ) : (homComplex M I).homology n ≃+ Ext (T.obj M) (T.obj N) n :=
  AddEquiv.ofBijective (homologyToExt T hinj hmono hexact hT hI n)
    (homologyToExt_bijective T hinj hmono hexact hT hI n)

/-- `Module.homologyAddEquivExt` sends the class of a cocycle `f` to the class of `T f`. -/
lemma homologyAddEquivExt_cocycleClass (n : ℕ)
    (f : LinearMap.ker ((homComplex M I).d n (n + 1)).hom) :
    homologyAddEquivExt T hinj hmono hexact hT hI n ((cocycleClass M I n).hom f) =
      cyclesToExt T hinj hmono hexact hI n f :=
  homologyToExt_cocycleClass T hinj hmono hexact hT hI n f

/-- Precomposition with `g : M' ⟶ M` on the cohomology of
`Hom_A(-, Iᐧ)` corresponds to composition with the degree-zero class of `T g`. -/
lemma homologyAddEquivExt_naturality_left {M' : ModuleCat.{v} A} (g : M' ⟶ M) (n : ℕ)
    (x : (homComplex M I).homology n) :
    homologyAddEquivExt T hinj hmono hexact hT hI n
        ((HomologicalComplex.homologyMap (homComplexPrecomp g.hom I) n).hom x) =
      (Ext.mk₀ (T.map g)).comp (homologyAddEquivExt T hinj hmono hexact hT hI n x)
        (zero_add n) := by
  obtain ⟨f, rfl⟩ := cocycleClass_surjective M I n x
  have h := congrArg (fun φ ↦ φ.hom f) (cocycleClass_naturality_left g I n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [h, homologyAddEquivExt_cocycleClass, homologyAddEquivExt_cocycleClass, cyclesToExt_apply,
    cyclesToExt_apply]
  refine Eq.trans ?_ (InjectiveResolution.mk₀_comp_extMk _ _ _ _ _ _).symm
  congr 1
  exact T.map_comp _ _

/-- For `g : N ⟶ N'`, pure injective resolutions
`N ⟶ Iᐧ` and `N' ⟶ Jᐧ` and any map of complexes `F : Iᐧ ⟶ Jᐧ` lying over `g`, postcomposition
with `F` on the cohomology of `Hom_A(M, -)` corresponds to composition with the degree-zero class
of `T g`. -/
lemma homologyAddEquivExt_naturality_right {N' : ModuleCat.{v} A}
    {J : CochainComplex (ModuleCat.{v} A) ℕ} {η' : N' →ₗ[A] J.X 0}
    (hJ : PureInjectiveResolution.IsPureInjectiveResolution J η') (g : N ⟶ N') (F : I ⟶ J)
    (hF : (F.f 0).hom.comp η = η'.comp g.hom) (n : ℕ) (x : (homComplex M I).homology n) :
    homologyAddEquivExt T hinj hmono hexact hT hJ n
        ((HomologicalComplex.homologyMap (homComplexPostcomp M F) n).hom x) =
      (homologyAddEquivExt T hinj hmono hexact hT hI n x).comp (Ext.mk₀ (T.map g))
        (add_zero n) := by
  obtain ⟨f, rfl⟩ := cocycleClass_surjective M I n x
  have h := congrArg (fun φ ↦ φ.hom f) (cocycleClass_naturality_right M F n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  let φ : (injectiveResolutionOfPure T hinj hmono hexact hI).Hom
      (injectiveResolutionOfPure T hinj hmono hexact hJ) (T.map g) :=
    { hom := (T.mapHomologicalComplex _).map F
      ι_f_zero_comp_hom_f_zero := by
        rw [injectiveResolutionOfPure_ι_f_zero, injectiveResolutionOfPure_ι_f_zero,
          CochainComplex.single₀_map_f_zero]
        change T.map _ ≫ T.map (F.f 0) = T.map g ≫ T.map _
        rw [← T.map_comp, ← T.map_comp]
        congr 1
        exact ModuleCat.hom_ext hF }
  rw [h, homologyAddEquivExt_cocycleClass, homologyAddEquivExt_cocycleClass, cyclesToExt_apply,
    cyclesToExt_apply]
  refine Eq.trans ?_ (InjectiveResolution.extMk_comp_mk₀ _ _ _ _ φ).symm
  congr 1
  exact T.map_comp _ _

end Ext

/-! ### The pure extension modules -/

section PureExt

/-- The pure injective resolution chosen in the definition of `Module.pureExt`. -/
def pureExtResolution (N : Type v) [AddCommGroup N] [Module A N] :
    CochainComplex (ModuleCat.{v} A) ℕ :=
  Classical.choose (PureInjectiveResolution.exists_pureInjectiveResolution A N)

/-- The augmentation of the pure injective resolution chosen in the definition of
`Module.pureExt`. -/
def pureExtAugmentation (N : Type v) [AddCommGroup N] [Module A N] :
    N →ₗ[A] (pureExtResolution (A := A) N).X 0 :=
  Classical.choose (Classical.choose_spec
    (PureInjectiveResolution.exists_pureInjectiveResolution A N))

/-- `Module.pureExtResolution N`, with the augmentation `Module.pureExtAugmentation N`, is a pure
injective resolution of `N`. -/
lemma isPureInjectiveResolution_pureExtResolution (N : Type v) [AddCommGroup N] [Module A N] :
    PureInjectiveResolution.IsPureInjectiveResolution (pureExtResolution (A := A) N)
      (pureExtAugmentation N) :=
  Classical.choose_spec (Classical.choose_spec
    (PureInjectiveResolution.exists_pureInjectiveResolution A N))

/-- `Pext^n_A(M, N)` is, by definition, the `n`-th cohomology of `Hom_A(M, Iᐧ)` for the chosen
pure injective resolution `N ⟶ Iᐧ`. -/
lemma pureExt_eq_homology (M N : Type v) [AddCommGroup M] [Module A M] [AddCommGroup N]
    [Module A N] (n : ℕ) :
    Module.pureExt (A := A) M N n = (homComplex M (pureExtResolution (A := A) N)).homology n :=
  rfl

variable [HasExt.{w} C] (hT : T.FullyFaithful)

/-- `Pext^n_A(M, N) = Ext^n_𝒞(T M, T N)`, for every `n`, for a fully faithful additive functor
`T` from `A`-modules to an abelian category which carries universally exact sequences to exact
ones, universally injective maps to monomorphisms and pure injective modules to injective
objects. The class of a cocycle `f : M → Iⁿ` of the chosen pure injective resolution `N ⟶ Iᐧ`
goes to the class of the cocycle `T f` of the injective resolution `T N ⟶ T Iᐧ`. -/
def pureExtAddEquivExt (M N : ModuleCat.{v} A) (n : ℕ) :
    Module.pureExt (A := A) M N n ≃+ Ext (T.obj M) (T.obj N) n :=
  homologyAddEquivExt T hinj hmono hexact hT (isPureInjectiveResolution_pureExtResolution N) n

/-- `Module.pureExtAddEquivExt` on the class of a cocycle of the chosen resolution. -/
lemma pureExtAddEquivExt_cocycleClass (M N : ModuleCat.{v} A) (n : ℕ)
    (f : LinearMap.ker ((homComplex M (pureExtResolution (A := A) N)).d n (n + 1)).hom) :
    pureExtAddEquivExt T hinj hmono hexact hT M N n
        ((cocycleClass M (pureExtResolution (A := A) N) n).hom f) =
      cyclesToExt T hinj hmono hexact (isPureInjectiveResolution_pureExtResolution N) n f :=
  homologyAddEquivExt_cocycleClass T hinj hmono hexact hT _ n f

/-- Naturality of `Pext^n_A(M, N) = Ext^n_𝒞(T M, T N)` in `M`: the action of `g : M' ⟶ M` on
`Pext^n_A(-, N)` is precomposition on `Hom_A(-, Iᐧ)`, and it corresponds to composition with the
degree-zero class of `T g`. -/
lemma pureExtAddEquivExt_naturality_left {M M' : ModuleCat.{v} A} (N : ModuleCat.{v} A)
    (g : M' ⟶ M) (n : ℕ) (x : Module.pureExt (A := A) M N n) :
    pureExtAddEquivExt T hinj hmono hexact hT M' N n
        ((HomologicalComplex.homologyMap
          (homComplexPrecomp g.hom (pureExtResolution (A := A) N)) n).hom x) =
      (Ext.mk₀ (T.map g)).comp (pureExtAddEquivExt T hinj hmono hexact hT M N n x)
        (zero_add n) :=
  homologyAddEquivExt_naturality_left T hinj hmono hexact hT _ g n x

/-- Naturality of `Pext^n_A(M, N) = Ext^n_𝒞(T M, T N)` in `N`: the action of `g : N ⟶ N'` on
`Pext^n_A(M, -)` is postcomposition with a map `F` of the chosen pure injective resolutions lying
over `g` (one exists, and any two are homotopic, by [Stacks, Tag 0704]); for every such `F` it
corresponds to composition with the degree-zero class of `T g`. -/
lemma pureExtAddEquivExt_naturality_right (M : ModuleCat.{v} A) {N N' : ModuleCat.{v} A}
    (g : N ⟶ N') (F : pureExtResolution (A := A) N ⟶ pureExtResolution (A := A) N')
    (hF : (F.f 0).hom.comp (pureExtAugmentation N) = (pureExtAugmentation N').comp g.hom)
    (n : ℕ) (x : Module.pureExt (A := A) M N n) :
    pureExtAddEquivExt T hinj hmono hexact hT M N' n
        ((HomologicalComplex.homologyMap (homComplexPostcomp M F) n).hom x) =
      (pureExtAddEquivExt T hinj hmono hexact hT M N n x).comp (Ext.mk₀ (T.map g))
        (add_zero n) :=
  homologyAddEquivExt_naturality_right T hinj hmono hexact hT _ _ g F hF n x

/-- A map of the chosen pure injective resolutions lying over a given map of modules exists
([Stacks, Tag 0704]). -/
lemma exists_pureExtResolution_hom {N N' : ModuleCat.{v} A} (g : N ⟶ N') :
    ∃ F : pureExtResolution (A := A) N ⟶ pureExtResolution (A := A) N',
      (F.f 0).hom.comp (pureExtAugmentation N) = (pureExtAugmentation N').comp g.hom := by
  have hI := isPureInjectiveResolution_pureExtResolution (A := A) N
  exact PureInjectiveResolution.exists_comparison_map g.hom _ _ _ _
    { injective_augmentation := hI.injective_augmentation
      universallyInjective_augmentation := hI.universallyInjective_augmentation
      exact_zero := hI.exact_zero
      baseChange_exact_zero := hI.baseChange_exact_zero
      exact := hI.exact
      baseChange_exact := hI.baseChange_exact }
    (isPureInjectiveResolution_pureExtResolution N')

end PureExt

end Module

end
