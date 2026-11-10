module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleInjectiveSectionsPowExact
public import StacksFrontier.CategoryTheory.Abelian.PowExact
public import StacksFrontier.Homology.Perfect.ZModPrimePowerReduction
public import Mathlib.CategoryTheory.Abelian.ShortExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CanonicalCompactSupportFrobenius
import all StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicObjects

/-!
# The `p`-torsion of a flat sheaf of `ℤ/pᵐℤ`-modules and its cohomology

Let `p` be a prime, `m ≥ 1`, and let `F` be a flat sheaf of `ℤ/pᵐℤ`-modules on the small étale
site of a scheme, flatness being the exactness of `F --p^(m-a)--> F --p^a--> F`
(`CategoryTheory.Abelian.PowExact`).  Its `p`-torsion `F[p] ≅ F / pF` is the sheaf of
`ℤ/pℤ`-modules `Hom_{ℤ/pᵐℤ}(ℤ/pℤ, F)`, the coextension of scalars of `F`.  This file shows that
taking `p`-torsion of an injective resolution `F → I` gives a resolution `F[p] → I[p]`, so
that the cohomology of `F[p]` is computed by the `p`-torsion of the complex `Γ(I)`.  Together
with `Stacks.ZModPrimePower.isPerfect_of_bounded_reduction` this proves that the cohomology of
`F` is perfect as soon as the cohomology of `F / pF` is finite and bounded, the perfectness
input of [Tag 03V2] and [Tag 03V3].

## References

* [Stacks Project, Tag 03V2](https://stacks.math.columbia.edu/tag/03V2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

open Stacks.ZModPrimePower

/-! ### Exactness on sections -/

section Sections

variable {Λ : Type} [Ring Λ] {X : Scheme.{u}}

/-- **A short complex of sheaves of modules on the small étale site which is exact on the
sections over every object is exact.** -/
theorem shortComplex_exact_of_sections (S : ShortComplex (EtaleModules.{u, 0} Λ X))
    (h : ∀ (U : X.Etaleᵒᵖ) (x : S.X₂.obj.obj U), S.g.hom.app U x = 0 →
      ∃ y : S.X₁.obj.obj U, S.f.hom.app U y = x) : S.Exact := by
  let P := S.map (sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  have hpre : P.Exact := by
    apply (ShortComplex.exact_iff_isZero_homology _).mpr
    apply (IsZero.iff_id_eq_zero _).mpr
    apply NatTrans.ext
    funext V
    have hV : (P.map ((CategoryTheory.evaluation _ _).obj V)).Exact := by
      rw [ShortComplex.moduleCat_exact_iff]
      exact h V
    let ev := (CategoryTheory.evaluation (X.Etaleᵒᵖ) (ModuleCat.{u + 1} Λ)).obj V
    exact (((P.map ev).exact_iff_isZero_homology.mp hV).of_iso
      (P.mapHomologyIso ev).symm).eq_of_src _ _
  have hmap := hpre.map (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  refine (ShortComplex.exact_iff_of_iso ?_).1 hmap
  let ε := (sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).counit
  exact ShortComplex.isoMk (asIso (ε.app S.X₁)) (asIso (ε.app S.X₂)) (asIso (ε.app S.X₃))
    (ε.naturality S.f).symm (ε.naturality S.g).symm

end Sections

/-! ### Flatness of injective sheaves -/

section PowExact

variable {p : ℕ} [Fact p.Prime] {m : ℕ} {X : Scheme.{u}}

omit [Fact p.Prime] in
/-- Every sheaf of `ℤ/pᵐℤ`-modules is killed by `p^m`. -/
theorem etaleModules_pow_nsmul_id (F : EtaleModules.{u, 0} (ZMod (p ^ m)) X) :
    (p ^ m) • 𝟙 F = 0 := by
  apply Sheaf.hom_ext
  ext V x
  change (p ^ m) • x = 0
  exact pow_nsmul_eq_zero x

/-- **An injective sheaf of `ℤ/pᵐℤ`-modules is flat**: `I --p^(m-a)--> I --p^a--> I` is exact,
because it is so on sections. -/
theorem powExact_of_injective (I : EtaleModules.{u, 0} (ZMod (p ^ m)) X) [Injective I] :
    PowExact p m I := by
  refine powExact_of_exact (etaleModules_pow_nsmul_id I) (fun a ha => ?_)
  exact shortComplex_exact_of_sections _ fun U x hx =>
    isPowExact_sections_of_injective I U.unop a ha x hx

end PowExact

/-! ### The `N`-torsion functor -/

section Torsion

variable (p : ℕ) (m : ℕ) (X : Scheme.{u})

/-- The reduction `ℤ/pᵐℤ → ℤ/pℤ`, for `m ≥ 1`. -/
abbrev torsionCoeff [NeZero m] : ZMod (p ^ m) →+* ZMod p :=
  ZMod.castHom (dvd_pow_self p (NeZero.ne m)) (ZMod p)

variable {p m} (N : ℕ) (hN : N ∣ p ^ m)

/-- The `N`-torsion `F[N] = Hom_{ℤ/pᵐℤ}(ℤ/Nℤ, F)` of a sheaf of `ℤ/pᵐℤ`-modules, for `N ∣ pᵐ`,
as a sheaf of `ℤ/pᵐℤ`-modules: coextension of scalars to `ℤ/Nℤ` followed by restriction of
scalars. -/
abbrev etaleModuleTorsion :
    EtaleModules.{u, 0} (ZMod (p ^ m)) X ⥤ EtaleModules.{u, 0} (ZMod (p ^ m)) X :=
  etaleModuleCoextendScalars (ZMod.castHom hN (ZMod N)) X ⋙
    etaleModuleRestrictScalars (ZMod.castHom hN (ZMod N)) X

/-- The inclusion `F[N] ⟶ F`, `φ ↦ φ(1)`: the counit of restriction of scalars. -/
abbrev etaleModuleTorsionι : etaleModuleTorsion X N hN ⟶ 𝟭 _ :=
  (etaleModuleCoextendScalarsAdj (ZMod.castHom hN (ZMod N)) X).counit

variable {X N hN}

/-- An element of a module killed by `N`, as a `ℤ/pᵐℤ`-linear map out of `ℤ/Nℤ`. -/
def torsionElementHom {M : ModuleCat.{u + 1} (ZMod (p ^ m))} (x : M) (hx : N • x = 0) :
    (ModuleCat.coextendScalars (ZMod.castHom hN (ZMod N))).obj M :=
  (ModuleCat.CoextendScalars.equiv _ _).symm
    { toFun := ZMod.lift N ⟨zmultiplesHom M x, by simpa using hx⟩
      map_add' := map_add _
      map_smul' := fun c r => ZMod.map_smul (ZMod.lift N ⟨zmultiplesHom M x, by simpa using hx⟩)
        c r }

/-- The linear map `ℤ/Nℤ → M` underlying `torsionElementHom x hx` sends `1` to `x`. -/
lemma torsionElementHom_one {M : ModuleCat.{u + 1} (ZMod (p ^ m))} (x : M) (hx : N • x = 0) :
    ModuleCat.CoextendScalars.equiv _ _ (torsionElementHom (hN := hN) x hx) (1 : ZMod N) = x := by
  have : ZMod.lift N ⟨zmultiplesHom M x, by simpa using hx⟩ (1 : ZMod N) = x := by
    rw [← Int.cast_one, ZMod.lift_coe]
    simp
  exact this

/-- An additive map out of `ℤ/Nℤ` is determined by its value at `1`. -/
private lemma zmod_addMonoidHom_ext {M : Type*} [AddCommGroup M] (f g : ZMod N →+ M)
    (h : f 1 = g 1) : f = g := by
  ext r
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective r
  rw [← zsmul_one, map_zsmul, map_zsmul, h]

/-- The value at `1` of an additive map out of `ℤ/Nℤ` is killed by `N`. -/
lemma zmod_addMonoidHom_smul_one {M : Type*} [AddCommGroup M] (f : ZMod N →+ M) :
    N • f 1 = 0 := by
  rw [← map_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_self, map_zero]

/-- An element of the coextension `Hom(ℤ/Nℤ, M)` is determined by its value at `1`. -/
lemma coextendScalars_ext_one {M : ModuleCat.{u + 1} (ZMod (p ^ m))}
    (φ ψ : (ModuleCat.coextendScalars (ZMod.castHom hN (ZMod N))).obj M)
    (h : ModuleCat.CoextendScalars.equiv _ _ φ (1 : ZMod N) =
      ModuleCat.CoextendScalars.equiv _ _ ψ (1 : ZMod N)) : φ = ψ := by
  refine ModuleCat.CoextendScalars.ext (LinearMap.ext fun r => ?_)
  have := zmod_addMonoidHom_ext (N := N)
    ((ModuleCat.CoextendScalars.equiv _ _ φ).toAddMonoidHom : ZMod N →+ M)
    ((ModuleCat.CoextendScalars.equiv _ _ ψ).toAddMonoidHom : ZMod N →+ M) h
  exact DFunLike.congr_fun this r

/-- **`F[N] ⟶ F` is the `N`-torsion of `F`.** -/
theorem isTorsionKernel_etaleModuleTorsionι (F : EtaleModules.{u, 0} (ZMod (p ^ m)) X) :
    IsTorsionKernel N ((etaleModuleTorsionι X N hN).app F) := by
  have hzero : ((etaleModuleTorsionι X N hN).app F) ≫ (N • 𝟙 F) = 0 := by
    apply Sheaf.hom_ext
    ext U φ
    exact zmod_addMonoidHom_smul_one (N := N)
      ((ModuleCat.CoextendScalars.equiv _ _ φ).toAddMonoidHom : ZMod N →+ _)
  have hex : (ShortComplex.mk _ _ hzero).Exact := by
    refine shortComplex_exact_of_sections _ (fun U x hx => ?_)
    exact ⟨torsionElementHom (hN := hN) x hx, torsionElementHom_one (hN := hN) x hx⟩
  have hmono : Mono ((etaleModuleTorsionι X N hN).app F) := by
    refine ⟨fun g h hgh => ?_⟩
    apply Sheaf.hom_ext
    ext U x
    exact coextendScalars_ext_one _ _ (congrArg (fun k => k.hom.app U x) hgh)
  exact ⟨hmono, hzero, fun T t ht => ⟨hex.lift t ht, hex.lift_f t ht⟩⟩

end Torsion

/-! ### Exactness of the coextension on flat short exact sequences -/

section Exactness

variable {p : ℕ} [Fact p.Prime] {m : ℕ} {X : Scheme.{u}} {N : ℕ} (hN : N ∣ p ^ m)

/-- Coextension of scalars of étale sheaves of modules is an additive functor. -/
instance etaleModuleCoextendScalars_additive {Λ Λ' : Type} [CommRing Λ] [CommRing Λ']
    (ρ : Λ →+* Λ') (X : Scheme.{u}) : (etaleModuleCoextendScalars ρ X).Additive :=
  (etaleModuleCoextendScalarsAdj ρ X).right_adjoint_additive

/-- Restriction of scalars of étale sheaves of modules is a faithful functor. -/
instance etaleModuleRestrictScalars_faithful {Λ Λ' : Type} [CommRing Λ] [CommRing Λ']
    (ρ : Λ →+* Λ') (X : Scheme.{u}) : (etaleModuleRestrictScalars ρ X).Faithful where
  map_injective {F G} f g h := by
    apply Sheaf.hom_ext
    ext U x
    exact congrArg (fun k => k.hom.app U x) h

omit [Fact p.Prime] in
/-- **Coextension of scalars to `ℤ/p^aℤ` is exact on a short exact sequence with flat first
term**, for `a ≤ m`. -/
theorem shortExact_map_coextendScalars {a : ℕ} (ha : a ≤ m) (hNa : N = p ^ a)
    (S : ShortComplex (EtaleModules.{u, 0} (ZMod (p ^ m)) X))
    (hS : S.ShortExact) (h₁ : PowExact p m S.X₁) :
    (S.map (etaleModuleCoextendScalars (ZMod.castHom hN (ZMod N)) X)).ShortExact := by
  refine CategoryTheory.ShortExact.reflects_shortExact_of_faithful
    (etaleModuleRestrictScalars (ZMod.castHom hN (ZMod N)) X) ?_
  let ι := etaleModuleTorsionι X N hN
  let ε : (S.map (etaleModuleCoextendScalars (ZMod.castHom hN (ZMod N)) X)).map
      (etaleModuleRestrictScalars (ZMod.castHom hN (ZMod N)) X) ⟶ S :=
    { τ₁ := ι.app S.X₁
      τ₂ := ι.app S.X₂
      τ₃ := ι.app S.X₃
      comm₁₂ := ι.naturality S.f
      comm₂₃ := ι.naturality S.g }
  have h (F : EtaleModules.{u, 0} (ZMod (p ^ m)) X) :
      IsTorsionKernel (p ^ a) ((etaleModuleTorsionι X N hN).app F) := by
    rw [← hNa]
    exact isTorsionKernel_etaleModuleTorsionι _
  exact PowExact.torsion_shortExact hS h₁ (etaleModules_pow_nsmul_id _) ha ε (h _) (h _) (h _)

omit [Fact p.Prime] in
/-- **Coextension of scalars to `ℤ/p^aℤ` carries a quasi-isomorphism between bounded below
complexes of flat sheaves to a quasi-isomorphism.** -/
theorem quasiIso_map_coextendScalars {a : ℕ} (ha : a ≤ m) (hNa : N = p ^ a)
    {K L : CochainComplex (EtaleModules.{u, 0} (ZMod (p ^ m)) X) ℤ}
    (φ : K ⟶ L) [QuasiIso φ] (b : ℤ) [K.IsStrictlyGE b] [L.IsStrictlyGE b]
    (hK : ∀ n, PowExact p m (K.X n)) (hL : ∀ n, PowExact p m (L.X n)) :
    QuasiIso (((etaleModuleCoextendScalars (ZMod.castHom hN (ZMod N)) X).mapHomologicalComplex
      (ComplexShape.up ℤ)).map φ) := by
  let G := etaleModuleCoextendScalars (ZMod.castHom hN (ZMod N)) X
  have : (CochainComplex.mappingCone φ).IsStrictlyGE (b - 1) :=
    CochainComplex.isStrictlyGE_mappingCone φ b b _ (by omega) (by omega)
  have hc := Functor.RightAcyclicCriterion.map_acyclic G (PowExact p m)
    (fun hZ => PowExact.of_isZero hZ)
    (fun S hS h₁ h₂ => ⟨PowExact.of_shortExact hS h₁ h₂ (etaleModules_pow_nsmul_id _),
      shortExact_map_coextendScalars hN ha hNa S hS h₁⟩)
    (CochainComplex.mappingCone φ) (b - 1) (Functor.acyclic_mappingCone φ inferInstance)
    (fun n => by
      have heq : (CochainComplex.mappingCone φ).X n =
          (K.X ((ComplexShape.up ℤ).next n) ⊞ L.X n) := dite_eq_left (by simp)
      rw [heq]
      exact (hK _).biprod (hL n))
  apply Functor.quasiIso_of_acyclic_mappingCone
  intro i
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (hc i).isZero_homology.of_iso
    (((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) i).mapIso
      (CochainComplex.mappingCone.mapHomologicalComplexIso φ G)).symm)

end Exactness

/-! ### The cohomology of the `p`-torsion -/

section Cohomology

/-- In modules, a `p`-torsion kernel is injective with image the `p`-torsion. -/
lemma IsTorsionKernel.moduleCat {R : Type*} [Ring R] {n : ℕ} {A M : ModuleCat.{u + 1} R}
    {e : A ⟶ M} (h : IsTorsionKernel n e) :
    Function.Injective e.hom ∧
      LinearMap.range e.hom = LinearMap.ker (n • LinearMap.id : M →ₗ[R] M) := by
  refine ⟨(ModuleCat.mono_iff_injective e).1 h.mono, le_antisymm ?_ ?_⟩
  · rintro _ ⟨x, rfl⟩
    change n • e x = 0
    exact congrArg (fun k => k.hom x) h.comp_eq_zero
  · intro y hy
    let K := LinearMap.ker (n • LinearMap.id : M →ₗ[R] M)
    let t : ModuleCat.of R K ⟶ M := ModuleCat.ofHom K.subtype
    obtain ⟨s, hs⟩ := h.exists_lift t (by
      ext z
      exact z.2)
    exact ⟨s.hom ⟨y, hy⟩, congrArg (fun k => k.hom ⟨y, hy⟩) hs⟩

attribute [local instance] HasDerivedCategory.standard

variable {p : ℕ} [Fact p.Prime] {m : ℕ} {Z S : Scheme.{u}} (f : Z ⟶ S)

/-- The functor `Γ(S, f_* -)` with coefficients `Λ`. -/
abbrev directImageSections (Λ : Type) [Ring Λ] :
    EtaleModules.{u, 0} Λ Z ⥤ ModuleCat.{u + 1} Λ :=
  etaleModuleDirectImage.{u, 0} Λ f ⋙ etaleModuleGlobalSections.{u, 0} Λ S

/-- `RΓ(S, Rf_* F)` for a sheaf `F` of `Λ`-modules on `Z`, in `D(Λ)`. -/
abbrev derivedDirectImageSections (Λ : Type) [Ring Λ] (F : EtaleModules.{u, 0} Λ Z) :
    DerivedCategory (ModuleCat.{u + 1} Λ) :=
  DerivedCategory.Plus.ι.obj ((etaleModuleDerivedGlobalSections.{u, 0} Λ S).obj
    ((etaleModuleDerivedDirectImage.{u, 0} Λ f).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))

/-- `RΓ(S, Rf_* F)` is computed by `Γ(S, f_* I)` for an injective resolution `I` of `F`. -/
def derivedDirectImageSectionsIso (Λ : Type) [Ring Λ] (F : EtaleModules.{u, 0} Λ Z)
    (R : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor _ 0).obj F)) :
    derivedDirectImageSections f Λ F ≅
      DerivedCategory.Q.obj (((directImageSections f Λ).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj R.cocomplex) :=
  DerivedCategory.Plus.ι.mapIso ((Functor.rightDerivedFunctorPlusCompIso
      (etaleModuleDirectImage.{u, 0} Λ f) (etaleModuleGlobalSections.{u, 0} Λ S)).app _).symm ≪≫
    (directImageSections f Λ).rightDerivedFunctorPlusInjectiveResolutionIso F R

/-- A functor preserving zero morphisms maps a complex that is strictly `≥ n` to one that is
strictly `≥ n`. -/
private lemma isStrictlyGE_mapHomologicalComplex_obj {C D : Type*} [Category C] [Category D]
    [HasZeroMorphisms C] [HasZeroMorphisms D] (G : C ⥤ D) [G.PreservesZeroMorphisms]
    (K : CochainComplex C ℤ) (n : ℤ) [K.IsStrictlyGE n] :
    CochainComplex.IsStrictlyGE ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) n := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  exact G.map_isZero (K.isZero_of_isStrictlyGE n i hi)

omit [Fact p.Prime] in
/-- A flat sheaf placed in degree `0` has flat terms. -/
lemma powExact_single_X {F : EtaleModules.{u, 0} (ZMod (p ^ m)) Z} (hF : PowExact p m F) (n : ℤ) :
    PowExact p m (((CochainComplex.singleFunctor _ 0).obj F).X n) := by
  obtain rfl | hn := eq_or_ne n 0
  · have e := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F
    intro a ha T x hx
    obtain ⟨T', π, hπ, y, hy⟩ := hF a ha (x ≫ e.hom) (by
      rw [Category.assoc, ← nsmul_id_comp, ← Category.assoc, hx, zero_comp])
    refine ⟨T', π, hπ, y ≫ e.inv, ?_⟩
    rw [← cancel_mono e.hom, Category.assoc, hy, Category.assoc, Category.assoc, nsmul_id_comp,
      e.inv_hom_id_assoc]
  · exact PowExact.of_isZero (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn)

/-- The `p^a`-torsion `Hom(ℤ/p^aℤ, I)` of an injective resolution of a flat sheaf `F` is an
injective resolution of the `p^a`-torsion of `F`. -/
noncomputable def coextendScalarsInjectiveResolution {N : ℕ} (hN : N ∣ p ^ m) {a : ℕ}
    (ha : a ≤ m) (hNa : N = p ^ a) {F : EtaleModules.{u, 0} (ZMod (p ^ m)) Z}
    (hF : PowExact p m F)
    (R : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor _ 0).obj F))
    [R.cocomplex.IsStrictlyGE 0] :
    CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor _ 0).obj
      ((etaleModuleCoextendScalars (ZMod.castHom hN (ZMod N)) Z).obj F)) where
  cocomplex := ((etaleModuleCoextendScalars (ZMod.castHom hN (ZMod N)) Z).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj R.cocomplex
  boundedBelow := ⟨0, by
    rw [CochainComplex.isStrictlyGE_iff]
    intro n hn
    exact (etaleModuleCoextendScalars (ZMod.castHom hN (ZMod N)) Z).map_isZero
      (R.cocomplex.isZero_of_isStrictlyGE 0 n hn)⟩
  injective n := by
    have : (etaleModuleRestrictScalars (ZMod.castHom hN (ZMod N)) Z).PreservesMonomorphisms :=
      preservesMonomorphisms_of_preservesLimitsOfShape _
    exact (etaleModuleCoextendScalarsAdj (ZMod.castHom hN (ZMod N)) Z).map_injective _
      (R.injective n)
  ι := ((HomologicalComplex.singleMapHomologicalComplex
      (etaleModuleCoextendScalars (ZMod.castHom hN (ZMod N)) Z) (ComplexShape.up ℤ) 0).inv.app F) ≫
    ((etaleModuleCoextendScalars (ZMod.castHom hN (ZMod N)) Z).mapHomologicalComplex
      (ComplexShape.up ℤ)).map R.ι
  quasiIso := by
    have := quasiIso_map_coextendScalars hN ha hNa R.ι 0 (powExact_single_X hF)
      (fun n => powExact_of_injective _)
    infer_instance

/-- The functor `Γ(S, f_* -)` preserves finite limits. -/
instance directImageSections_preservesFiniteLimits (Λ : Type) [Ring Λ] :
    PreservesFiniteLimits (directImageSections f Λ) := by
  have : (etaleModuleDirectImage.{u, 0} Λ f).IsRightAdjoint :=
    (etaleModuleInverseImageAdj.{u, 0} Λ f).isRightAdjoint
  have : (etaleModuleGlobalSections.{u, 0} Λ S).IsRightAdjoint :=
    (constantSheafΓAdj S.smallEtaleTopology (ModuleCat.{u + 1} Λ)).isRightAdjoint
  exact comp_preservesFiniteLimits _ _

/-- **The cohomology of a flat sheaf and of its `p^a`-torsion** (the input of [Tag 03V2]).
Let `F` be a flat sheaf of `ℤ/pᵐℤ`-modules on `Z`, `f : Z ⟶ S` and `a ≤ m`.  Then
`RΓ(S, Rf_* F)` is represented by a bounded below complex `J` of flat `ℤ/pᵐℤ`-modules whose
`p^a`-torsion `J[p^a] ≅ J / p^a J` computes `RΓ(S, Rf_*(F[p^a]))`, the cohomology with
`ℤ/p^aℤ` coefficients of the `p^a`-torsion `F[p^a] = Hom(ℤ/p^aℤ, F) ≅ F / p^a F`. -/
theorem derivedDirectImageSections_reduction {N : ℕ} (hN : N ∣ p ^ m) {a : ℕ} (ha : a ≤ m)
    (hNa : N = p ^ a) {F : EtaleModules.{u, 0} (ZMod (p ^ m)) Z} (hF : PowExact p m F) :
    ∃ J : CochainComplex (ModuleCat.{u + 1} (ZMod (p ^ m))) ℤ, J.IsStrictlyGE 0 ∧
      (∀ n, IsPowExact p m (J.X n)) ∧
      Nonempty (derivedDirectImageSections f _ F ≅ DerivedCategory.Q.obj J) ∧
      ∀ i, Nonempty ((torsionComplex p J a).homology i ≅
        (ModuleCat.restrictScalars (ZMod.castHom hN (ZMod N))).obj
          ((DerivedCategory.homologyFunctor _ i).obj (derivedDirectImageSections f (ZMod N)
            ((etaleModuleCoextendScalars (ZMod.castHom hN (ZMod N)) Z).obj F)))) := by
  obtain ⟨R, -, hR⟩ := CochainComplex.exists_injectiveResolution_isStrictlyGE 0
    ((CochainComplex.singleFunctor (EtaleModules.{u, 0} (ZMod (p ^ m)) Z) 0).obj F)
  let R' := coextendScalarsInjectiveResolution hN ha hNa hF R
  let G := directImageSections f (ZMod (p ^ m))
  let G' := directImageSections f (ZMod N)
  let J := (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj R.cocomplex
  let J' := (G'.mapHomologicalComplex (ComplexShape.up ℤ)).obj R'.cocomplex
  have hJ : ∀ n, IsPowExact p m (J.X n) := fun n => by
    have := R.injective n
    exact (isPowExact_sections_of_injective
      ((etaleModuleDirectImage.{u, 0} _ f).obj (R.cocomplex.X n)) (⊤_ S.Etale)).of_addEquiv
      ((Sheaf.ΓNatIsoSheafSections S.smallEtaleTopology _ terminalIsTerminal).app
        _).symm.toLinearEquiv.toAddEquiv
  have hk : ∀ n, IsTorsionKernel (p ^ a)
      (G.map ((etaleModuleTorsionι Z N hN).app (R.cocomplex.X n))) := fun n => by
    rw [← hNa]
    exact (isTorsionKernel_etaleModuleTorsionι _).map G
  let e := (G.mapHomologicalComplex (ComplexShape.up ℤ)).map
    ((NatTrans.mapHomologicalComplex (etaleModuleTorsionι Z N hN) (ComplexShape.up ℤ)).app
      R.cocomplex)
  let e₁ := torsionComplexIsoOfRange p J (c := a) e (fun n => (IsTorsionKernel.moduleCat (hk n)).1)
    (fun n => (IsTorsionKernel.moduleCat (hk n)).2)
  let Ni : etaleModuleTorsion Z N hN ⋙ G ≅
      etaleModuleCoextendScalars (ZMod.castHom hN (ZMod N)) Z ⋙ G' ⋙
        ModuleCat.restrictScalars (ZMod.castHom hN (ZMod N)) :=
    Functor.isoWhiskerLeft (etaleModuleCoextendScalars (ZMod.castHom hN (ZMod N)) Z ⋙
      etaleModuleDirectImage.{u, 0} (ZMod N) f)
      (etaleModuleGlobalSectionsRestrictScalars (ZMod.castHom hN (ZMod N)) S).symm
  let e₂ : ((etaleModuleTorsion Z N hN ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      R.cocomplex ≅ ((ModuleCat.restrictScalars (ZMod.castHom hN (ZMod N))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj J' :=
    (NatIso.mapHomologicalComplex Ni (ComplexShape.up ℤ)).app R.cocomplex
  refine ⟨J, isStrictlyGE_mapHomologicalComplex_obj G _ 0, hJ,
    ⟨derivedDirectImageSectionsIso f _ F R⟩, fun i => ⟨?_⟩⟩
  let e₃ := (J'.sc i).mapHomologyIso (ModuleCat.restrictScalars (ZMod.castHom hN (ZMod N)))
  let e₄ : J'.homology i ≅ (DerivedCategory.homologyFunctor _ i).obj
      (derivedDirectImageSections f (ZMod N)
        ((etaleModuleCoextendScalars (ZMod.castHom hN (ZMod N)) Z).obj F)) :=
    ((DerivedCategory.homologyFunctorFactors _ i).app J').symm ≪≫
      (DerivedCategory.homologyFunctor _ i).mapIso (derivedDirectImageSectionsIso f _ _ R').symm
  exact (HomologicalComplex.homologyMapIso e₁ i).symm ≪≫ HomologicalComplex.homologyMapIso e₂ i ≪≫
    e₃ ≪≫ (ModuleCat.restrictScalars (ZMod.castHom hN (ZMod N))).mapIso e₄

end Cohomology

/-! ### The geometric fibre over a finite field -/

section FieldBaseChange

attribute [local instance] HasDerivedCategory.standard

variable {Λ : Type} [Ring Λ]

/-- The derived image of a complex concentrated in degree `0` is the single complex on the
sheaf. -/
def plusQSingleIso {X : Scheme.{u}} (F : EtaleModules.{u, 0} Λ X) :
    DerivedCategory.Plus.Q.obj (⟨(CochainComplex.singleFunctor _ 0).obj F,
      CochainComplex.plus_singleFunctor_obj F⟩ : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)) ≅
      (DerivedCategory.Plus.singleFunctor _ 0).obj F :=
  ((DerivedCategory.Plus.quotientCompQhIso _).app _).symm ≪≫
    ((DerivedCategory.Plus.singleFunctorIsoCompQh _ 0).app F).symm

variable {k : Type u} [Field k] (Y : Over (Spec (.of k))) (kbar : Type u) [Field kbar]
  [Algebra k kbar]

/-- The restriction to `Y_k̄` of a sheaf placed in degree `0` is the single complex on its
inverse image. -/
def fieldBaseChangeRestrictionSingleIso (F : EtaleModules.{u, 0} Λ Y.left) :
    fieldBaseChangeRestriction.{u, 0} Λ Y kbar ⟨(CochainComplex.singleFunctor _ 0).obj F,
      CochainComplex.plus_singleFunctor_obj F⟩ ≅
      (DerivedCategory.Plus.singleFunctor _ 0).obj
        ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).obj F) :=
  DerivedCategory.Plus.Q.mapIso (ObjectProperty.isoMk _
      (X := (etaleModuleInverseImage.{u, 0} Λ
          (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
        ⟨(CochainComplex.singleFunctor _ 0).obj F, CochainComplex.plus_singleFunctor_obj F⟩)
      (Y := ⟨(CochainComplex.singleFunctor _ 0).obj
        ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).obj F),
        CochainComplex.plus_singleFunctor_obj _⟩)
      ((HomologicalComplex.singleMapHomologicalComplex
        (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)) (ComplexShape.up ℤ)
          0).app F)) ≪≫ plusQSingleIso _

variable (p : ℕ) [Fact p.Prime] (m : ℕ) [NeZero m]

omit [Fact p.Prime] [NeZero m] in
/-- The flat sheaf `F₀` on `Y`, restricted to `Y_k̄`, is flat. -/
lemma powExact_fieldBaseChange {F₀ : EtaleModules.{u, 0} (ZMod (p ^ m)) Y.left}
    (hF : PowExact p m F₀) :
    PowExact p m ((etaleModuleInverseImage.{u, 0} _ (fieldBaseChangeProj Y kbar)).obj F₀) := by
  have := etaleModuleInverseImage_preservesFiniteLimits.{u, 0} (ZMod (p ^ m))
    (fieldBaseChangeProj Y kbar)
  have : PreservesFiniteColimits (etaleModuleInverseImage.{u, 0} (ZMod (p ^ m))
      (fieldBaseChangeProj Y kbar)) :=
    have := (etaleModuleInverseImageAdj.{u, 0} (ZMod (p ^ m))
      (fieldBaseChangeProj Y kbar)).isLeftAdjoint
    inferInstance
  exact hF.map _ (etaleModules_pow_nsmul_id F₀)

/-- **[W1] The cohomology of `Y_k̄` with coefficients in a flat sheaf and in its `p`-torsion.** -/
theorem fieldBaseChangeCohomology_reduction {F₀ : EtaleModules.{u, 0} (ZMod (p ^ m)) Y.left}
    (hF : PowExact p m F₀) :
    ∃ J : CochainComplex (ModuleCat.{u + 1} (ZMod (p ^ m))) ℤ, J.IsStrictlyGE 0 ∧
      (∀ n, IsPowExact p m (J.X n)) ∧
      Nonempty (DerivedCategory.Plus.ι.obj ((etaleModuleDerivedGlobalSections.{u, 0} _
        (Spec (.of kbar))).obj ((etaleModuleDerivedDirectImage.{u, 0} _
          (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, 0} _ Y kbar ⟨(CochainComplex.singleFunctor _ 0).obj F₀,
            CochainComplex.plus_singleFunctor_obj F₀⟩))) ≅ DerivedCategory.Q.obj J) ∧
      ∀ i, Nonempty ((torsionComplex p J 1).homology i ≅
        (ModuleCat.restrictScalars (torsionCoeff p m)).obj
          ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ZMod p)) i).obj
            (derivedDirectImageSections (pullback.snd Y.hom (specAlgebraMap k kbar)) (ZMod p)
            ((etaleModuleCoextendScalars (torsionCoeff p m) _).obj
              ((etaleModuleInverseImage.{u, 0} _ (fieldBaseChangeProj Y kbar)).obj F₀))))) := by
  obtain ⟨J, hJ₀, hJ, ⟨e⟩, hh⟩ := derivedDirectImageSections_reduction
    (pullback.snd Y.hom (specAlgebraMap k kbar)) (dvd_pow_self p (NeZero.ne m))
    (Nat.one_le_iff_ne_zero.2 (NeZero.ne m)) (pow_one p).symm
    (powExact_fieldBaseChange Y kbar p m hF)
  refine ⟨J, hJ₀, hJ, ⟨?_ ≪≫ e⟩, hh⟩
  exact DerivedCategory.Plus.ι.mapIso ((etaleModuleDerivedGlobalSections.{u, 0} _
    (Spec (.of kbar))).mapIso ((etaleModuleDerivedDirectImage.{u, 0} _
      (pullback.snd Y.hom (specAlgebraMap k kbar))).mapIso
      (fieldBaseChangeRestrictionSingleIso Y kbar F₀)))

/-- **Perfectness of `RΓ(Y_k̄, F)` for a flat sheaf `F` of `ℤ/pᵐℤ`-modules** whose `p`-torsion
`F[p] ≅ F / pF` has finite cohomology vanishing above `b` on `Y_k̄`. -/
theorem isPerfect_fieldBaseChangeCohomology_of_reduction
    {F₀ : EtaleModules.{u, 0} (ZMod (p ^ m)) Y.left} (hF : PowExact p m F₀) (b : ℤ)
    (hb : ∀ i, b < i → IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ZMod p)) i).obj
      (derivedDirectImageSections (pullback.snd Y.hom (specAlgebraMap k kbar)) (ZMod p)
        ((etaleModuleCoextendScalars (torsionCoeff p m) _).obj
          ((etaleModuleInverseImage.{u, 0} _ (fieldBaseChangeProj Y kbar)).obj F₀)))))
    (hf : ∀ i, Module.Finite (ZMod p)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ZMod p)) i).obj
        (derivedDirectImageSections (pullback.snd Y.hom (specAlgebraMap k kbar)) (ZMod p)
          ((etaleModuleCoextendScalars (torsionCoeff p m) _).obj
            ((etaleModuleInverseImage.{u, 0} _ (fieldBaseChangeProj Y kbar)).obj F₀))))) :
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, 0} _ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, 0} _ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, 0} _ Y kbar ⟨(CochainComplex.singleFunctor _ 0).obj F₀,
            CochainComplex.plus_singleFunctor_obj F₀⟩)))) := by
  obtain ⟨J, hJ₀, hJ, ⟨e⟩, hh⟩ := fieldBaseChangeCohomology_reduction Y kbar p m hF
  obtain ⟨P, a, b', h₁, h₂, h₃, h₄, ⟨e'⟩⟩ := isPerfect_of_bounded_reduction J hJ 0 b
    (fun i hi => by
      rw [HomologicalComplex.exactAt_iff_isZero_homology]
      obtain ⟨e'⟩ := hh i
      exact ((ModuleCat.restrictScalars (torsionCoeff p m)).map_isZero (hb i hi)).of_iso e')
    (fun i => by
      obtain ⟨e'⟩ := hh i
      have := hf i
      have : Finite ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ZMod p)) i).obj
        (derivedDirectImageSections (pullback.snd Y.hom (specAlgebraMap k kbar)) (ZMod p)
          ((etaleModuleCoextendScalars (torsionCoeff p m) _).obj
            ((etaleModuleInverseImage.{u, 0} _ (fieldBaseChangeProj Y kbar)).obj F₀)))) :=
        Module.finite_of_finite (ZMod p)
      have hfin : Finite ((torsionComplex p J 1).homology i) :=
        @Finite.of_equiv _ _ this
          ((ModuleCat.restrictScalars (torsionCoeff p m)).mapIso (Iso.refl _) ≪≫
            e'.symm).toLinearEquiv.toEquiv
      infer_instance)
  exact ⟨P, a, b', h₁, h₂, h₃, h₄, ⟨e ≪≫ e'⟩⟩

end FieldBaseChange

end Stacks.EtaleCohomology
