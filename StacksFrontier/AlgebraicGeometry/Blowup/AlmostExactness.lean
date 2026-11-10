module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.IProjective
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.BlowUp
import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic
import StacksFrontier.AlgebraicGeometry.Divisors.RelativeAssassinTwo.AffineOpen
public import StacksFrontier.AlgebraicGeometry.Groupoids.IdealSheafComap
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.SchemeTheoretic
import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.AffineSections

/-!
# Almost exactness of pullback to a blowup

Let `A` be a commutative ring, `I ⊆ A` an ideal, and `b : Bl_I(Spec A) → Spec A` the blowup of
`Spec A` in `I`. Pullback along `b` is right exact but not left exact, and this file bounds the
failure of left exactness for a short exact sequence of modules killed by `I ^ n`.

Let `0 → K → L → M → 0` be a short exact sequence of `A / I ^ n`-modules with `M` finite and
projective relative to the ideal `I ^ c / I ^ n`, where `c ≤ n`. Relative projectivity means
that multiplication by every element of `I ^ c` on `M` factors through a projective module, and
such a factorization lifts to a retraction of `K → L` up to that scalar. After pullback to the
blowup the exceptional ideal is generated locally by a single element coming from `I`, so the
kernel of the pulled-back map `K̃ → L̃` is killed by the `c`-th power of the exceptional ideal:
scheme-theoretically it is supported on the `c`-th thickening of the exceptional divisor.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.annihilatorIdeal` — the ideal sheaf of the
  scheme-theoretic support of a module, assembled from the annihilators of its sections over
  the affine opens.
* `AlgebraicGeometry.blowUpModule` — the pullback to the blowup of the quasi-coherent sheaf
  associated to a module killed by a power of the ideal.

## Main results

* `AlgebraicGeometry.exceptionalIdeal_pow_le_annihilator_kernel` — the kernel of the pulled-back
  map is annihilated by the `c`-th power of the exceptional ideal.
* `AlgebraicGeometry.Scheme.Modules.annihilatorIdeal_eq_schemeTheoreticSupport` and
  `AlgebraicGeometry.Scheme.Modules.coe_support_annihilatorIdeal` — for a quasi-coherent module
  of finite type the annihilator ideal sheaf is the ideal sheaf of the scheme-theoretic support,
  and the closed subset it cuts out is the support of the module.

## Implementation notes

Modules annihilated by `I ^ n` are presented as modules over `A / I ^ n`, which is what lets
the relative projectivity hypothesis be stated for the extended ideal `I ^ c / I ^ n`.
Everything is checked on an affine open of the blowup, where pullback of an associated sheaf is
extension of scalars (Stacks 01I9) and the sections of the exceptional ideal are the image of
the sections of `I`; the comparison of sections used for that reduction is
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso`, together with its naturality in the
module, `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso_natural`.

## References

* [Stacks Project, Tag 05JU](https://stacks.math.columbia.edu/tag/05JU)
* [Stacks Project, Tag 0GA8](https://stacks.math.columbia.edu/tag/0GA8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry

universe u

/-- The ideal sheaf of the scheme-theoretic support of a module: over an affine open it is the
annihilator of the sections of the module. -/
def Scheme.Modules.annihilatorIdeal {X : Scheme.{u}} (F : X.Modules) : X.IdealSheafData :=
  Scheme.IdealSheafData.ofIdeals fun U => Module.annihilator Γ(X, U.1) Γ(F, U.1)

/-- For a quasi-coherent module of finite type the annihilator ideal sheaf is exactly the ideal
sheaf of the scheme-theoretic support of [Stacks, Tag 05JU]: in that case the annihilators of
the sections over the affine opens are already compatible with localization, so the largest
ideal sheaf they contain has them as its components. -/
theorem Scheme.Modules.annihilatorIdeal_eq_schemeTheoreticSupport {X : Scheme.{u}}
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    Scheme.Modules.annihilatorIdeal F = Scheme.Modules.schemeTheoreticSupport F :=
  le_antisymm
    (Scheme.IdealSheafData.le_def.2 fun U =>
      (Scheme.IdealSheafData.ideal_ofIdeals_le _ U).trans
        (Scheme.Modules.schemeTheoreticSupport_ideal F U).ge)
    (Scheme.IdealSheafData.le_ofIdeals_iff.2 fun U =>
      (Scheme.Modules.schemeTheoreticSupport_ideal F U).le)

/-- The annihilator ideal sheaf of a quasi-coherent module of finite type cuts out its support:
the closed subset underlying the annihilator ideal sheaf is the support of the module. This is
[Stacks, Tag 05JU], part (4), read off the annihilator ideal sheaf. -/
theorem Scheme.Modules.coe_support_annihilatorIdeal {X : Scheme.{u}} (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] :
    ((Scheme.Modules.annihilatorIdeal F).support : Set X) = SheafOfModules.supp F := by
  rw [Scheme.Modules.annihilatorIdeal_eq_schemeTheoreticSupport F]
  exact (Scheme.Modules.supp_eq_support_schemeTheoreticSupport F).symm

/-- **The retraction up to a scalar supplied by relative projectivity.** Let
`0 → K → L → M → 0` be a short exact sequence of `R`-modules and let `a : R` be a scalar whose
action on `M` factors through a projective module. Then multiplication by `a` on `K` factors
through the inclusion `K → L`, i.e. the inclusion admits a retraction up to `a`.

The projective module lifts along `L → M`, and the difference between multiplication by `a` on
`L` and that lift lands in the image of `K`; the retraction is that difference read in `K`.

This is the algebraic step of [Stacks, Tag 0GA8], and the only place relative projectivity of
the quotient is used. It is stated for a bare short exact sequence of modules so that it can be
fed to an arbitrary additive functor rather than only to the pullback along a blowup; see
`Stacks.LocalCohomology.UniformityIII.exists_resScalarRetraction`. -/
theorem exists_scalar_retraction_of_projective_factorization
    {R : Type u} [CommRing R]
    {K L M : Type u} [AddCommGroup K] [Module R K]
      [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M]
    (i : K →ₗ[R] L) (q : L →ₗ[R] M)
    (hzero : q.comp i = 0) (hexact : LinearMap.range i = LinearMap.ker q)
    (hq : Function.Surjective q) (hi : Function.Injective i) (a : R)
    (hfac : ∃ (P : Type u) (_ : AddCommGroup P) (_ : Module R P)
      (_ : Module.Projective R P) (α : M →ₗ[R] P) (β : P →ₗ[R] M),
        (LinearMap.lsmul R M) a = β.comp α)
    : ∃ h : L →ₗ[R] K, (LinearMap.lsmul R K) a = h.comp i := by
  classical
  obtain ⟨P, _, _, _, α, β, hαβ⟩ := hfac
  obtain ⟨βlift, hβlift⟩ := Module.projective_lifting_property q β hq
  have hqt : q.comp ((LinearMap.lsmul R L) a - βlift.comp (α.comp q)) = 0 := by
    ext x
    have hβx := LinearMap.congr_fun hβlift (α (q x))
    have hαx := LinearMap.congr_fun hαβ (q x)
    simp only [LinearMap.comp_apply] at hβx
    simp only [LinearMap.comp_apply, LinearMap.lsmul_apply] at hαx
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.lsmul_apply,
      LinearMap.comp_apply, map_sub, map_smul]
    rw [hβx, ← hαx]
    simp
  have hval (x : L) :
      ((LinearMap.lsmul R L) a - βlift.comp (α.comp q)) x ∈ LinearMap.range i := by
    rw [hexact, LinearMap.mem_ker]
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using LinearMap.congr_fun hqt x
  let t : L →ₗ[R] LinearMap.range i :=
    ((LinearMap.lsmul R L) a - βlift.comp (α.comp q)).codRestrict _ hval
  let e : K ≃ₗ[R] LinearMap.range i := LinearEquiv.ofInjective i hi
  let h : L →ₗ[R] K := e.symm.toLinearMap.comp t
  have hfactor : i.comp h = (LinearMap.range i).subtype.comp t := by
    ext x
    change i (e.symm (t x)) = (t x).1
    exact congrArg Subtype.val (e.apply_symm_apply (t x))
  refine ⟨h, ?_⟩
  ext x
  apply hi
  have hqi : q (i x) = 0 := by
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using LinearMap.congr_fun hzero x
  have ht : (t (i x)).val = i (a • x) := by
    simp only [t, LinearMap.codRestrict_apply, LinearMap.sub_apply,
      LinearMap.lsmul_apply, LinearMap.comp_apply]
    simp [hqi]
  have hx := LinearMap.congr_fun hfactor (i x)
  change i (h (i x)) = (t (i x)).val at hx
  rw [ht] at hx
  exact hx.symm

private alias exists_scalar_factorization_through_mono :=
  exists_scalar_retraction_of_projective_factorization

/-- In a short exact sequence `0 → K → L → M → 0` of `R`-modules, if multiplication by `a` on
`M` factors through a projective module then multiplication by `a` on `K` factors through
`K → L`. -/
private theorem exists_scalar_retraction_of_shortExact {R : Type u} [CommRing R]
    {K L M : ModuleCat.{u} R} {f : K ⟶ L} {g : L ⟶ M} {w : f ≫ g = 0}
    (hExact : (ShortComplex.mk f g w).ShortExact) (a : R)
    (hfac : ∃ (P : Type u) (_ : AddCommGroup P) (_ : Module R P)
      (_ : Module.Projective R P) (α : M →ₗ[R] P) (β : P →ₗ[R] M),
        (LinearMap.lsmul R M) a = β.comp α) :
    ∃ h : L →ₗ[R] K, (LinearMap.lsmul R K) a = h.comp f.hom :=
  exists_scalar_factorization_through_mono f.hom g.hom
    (by ext x; exact congrArg (fun z : K ⟶ M => z.hom x) w)
    ((ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp hExact.exact)
    ((ModuleCat.epi_iff_surjective g).mp hExact.epi_g)
    ((ModuleCat.mono_iff_injective f).mp hExact.mono_f) a hfac

private lemma factorization_kills_kernel_after_tensor
    {R T : Type u} [CommRing R] [CommRing T] [Algebra R T]
    {K L : ModuleCat.{u} R} (f : K ⟶ L) (a : R)
    (h : L →ₗ[R] K) (hfac : LinearMap.lsmul R K a = h.comp f.hom) :
    ∀ x : (ModuleCat.extendScalars (algebraMap R T)).obj K,
      ((ModuleCat.extendScalars (algebraMap R T)).map f).hom x = 0 →
      (algebraMap R T a) • x = 0 := by
  classical
  intro x hx
  let F : ModuleCat.{u} R ⥤ ModuleCat.{u} T :=
    ModuleCat.extendScalars (algebraMap R T)
  let : Algebra R T := (algebraMap R T).toAlgebra
  have hcomm : F.map (ModuleCat.ofHom (LinearMap.lsmul R K a)) =
      ModuleCat.ofHom (LinearMap.lsmul T (F.obj K) (algebraMap R T a)) := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro k
    change (1 : T) ⊗ₜ[R, algebraMap R T] (a • k) =
      LinearMap.lsmul T (F.obj K) (algebraMap R T a)
        ((1 : T) ⊗ₜ[R, algebraMap R T] k)
    rw [TensorProduct.tmul_smul]
    rfl
  have hh' : F.map (ModuleCat.ofHom (LinearMap.lsmul R K a)) =
      F.map f ≫ F.map (ModuleCat.ofHom h) := by
    simpa only [ModuleCat.ofHom_comp, ModuleCat.ofHom_hom, Functor.map_comp] using
      congrArg (fun q : K →ₗ[R] K => F.map (ModuleCat.ofHom q)) hfac
  have hhx := congrArg (fun q : F.obj K ⟶ F.obj K =>
    (ConcreteCategory.hom q) x) hh'
  rw [hcomm] at hhx
  change (algebraMap R T a) • x =
    (F.map (ModuleCat.ofHom h)).hom ((F.map f).hom x) at hhx
  rwa [hx, map_zero] at hhx

private lemma scalar_kills_kernel_after_tensor
    {R T : Type u} [CommRing R] [CommRing T] [Algebra R T]
    {K L M : ModuleCat.{u} R} (f : K ⟶ L) (g : L ⟶ M)
    (w : f ≫ g = 0) (hExact : (ShortComplex.mk f g w).ShortExact)
    (a : R) (hfac : Module.IsIProjective R (Ideal.span {a}) M) :
    ∀ x : (ModuleCat.extendScalars (algebraMap R T)).obj K,
      ((ModuleCat.extendScalars (algebraMap R T)).map f).hom x = 0 →
      (algebraMap R T a) • x = 0 := by
  obtain ⟨h, hh⟩ := exists_scalar_retraction_of_shortExact hExact a
    (hfac a (Ideal.subset_span (Set.mem_singleton a)))
  exact factorization_kills_kernel_after_tensor f a h hh

private lemma quotient_factorization_kills_kernel_after_tensor
    {A Q T : Type u} [CommRing A] [CommRing Q] [CommRing T]
    (q : A →+* Q) [Algebra A T]
    (K L : ModuleCat.{u} Q) (f : K ⟶ L) (a : A)
    (h : L →ₗ[Q] K)
    (hfac : LinearMap.lsmul Q K (q a) = h.comp f.hom) :
    ∀ x : (ModuleCat.extendScalars (algebraMap A T)).obj
        ((ModuleCat.restrictScalars q).obj K),
      ((ModuleCat.extendScalars (algebraMap A T)).map
          ((ModuleCat.restrictScalars q).map f)).hom x = 0 →
      (algebraMap A T a) • x = 0 := by
  let hA : ((ModuleCat.restrictScalars q).obj L) →ₗ[A]
      (ModuleCat.restrictScalars q).obj K :=
    { toFun := h
      map_add' := h.map_add
      map_smul' := fun a x => h.map_smul (q a) x }
  have hfacA : LinearMap.lsmul A ((ModuleCat.restrictScalars q).obj K) a =
      hA.comp ((ModuleCat.restrictScalars q).map f).hom := by
    ext x
    exact LinearMap.congr_fun hfac x
  exact factorization_kills_kernel_after_tensor
    ((ModuleCat.restrictScalars q).map f) a hA hfacA

private lemma affineSectionsLinearEquiv_natural {X : Scheme.{u}}
    {F G : X.Modules} (φ : F ⟶ G) {U : X.Opens} (hUaff : IsAffineOpen U)
    [IsOpenImmersion hUaff.fromSpec] (s : Γ(F.restrict hUaff.fromSpec, ⊤)) :
    affineSectionsLinearEquiv G hUaff
        (((Scheme.Modules.restrictFunctor hUaff.fromSpec).map φ).app ⊤ s) =
      φ.app U (affineSectionsLinearEquiv F hUaff s) := by
  have hU : hUaff.fromSpec ''ᵁ (⊤ : (Spec Γ(X, U)).Opens) = U := by
    rw [Scheme.Hom.image_top_eq_opensRange, hUaff.opensRange_fromSpec]
  have h := φ.val.naturality (eqToHom hU.symm).op
  exact (congrArg (fun q => (ConcreteCategory.hom q) s) h).symm

private def affineRestrictedSectionsMap {X : Scheme.{u}} {F G : X.Modules}
    (φ : F ⟶ G) {U : X.Opens} (hUaff : IsAffineOpen U) [IsOpenImmersion hUaff.fromSpec] :
  Γ(F.restrict hUaff.fromSpec, ⊤) →ₗ[Γ(X, U)]
      Γ(G.restrict hUaff.fromSpec, ⊤) := by
  let R := Γ(X, U)
  let e := Scheme.ΓSpecIso R
  let ψ := (Scheme.Modules.restrictFunctor hUaff.fromSpec).map φ
  refine { toFun := fun s => ψ.app ⊤ s, map_add' := ?_, map_smul' := ?_ }
  · intro x y
    exact map_add (ψ.app ⊤).hom x y
  · intro r x
    change ψ.app ⊤ ((e.inv r) • x) = (e.inv r) • ψ.app ⊤ x
    exact Scheme.Modules.Hom.app_smul ψ (e.inv r) x

private lemma affineSectionsModuleIso_hom_natural {X : Scheme.{u}}
    {F G : X.Modules} (φ : F ⟶ G) {U : X.Opens} (hUaff : IsAffineOpen U)
    [IsOpenImmersion hUaff.fromSpec] :
    (affineSectionsLinearEquiv F hUaff).toModuleIso.hom ≫
        ModuleCat.ofHom (Scheme.Modules.sectionsLinearMap φ U) =
        ModuleCat.ofHom (affineRestrictedSectionsMap φ hUaff) ≫
        (affineSectionsLinearEquiv G hUaff).toModuleIso.hom := by
  ext s
  change φ.app U (affineSectionsLinearEquiv F hUaff s) =
    affineSectionsLinearEquiv G hUaff
      (((Scheme.Modules.restrictFunctor hUaff.fromSpec).map φ).app ⊤ s)
  exact (affineSectionsLinearEquiv_natural φ hUaff s).symm

/-- The pullback to the blowup of the quasi-coherent sheaf associated to a
module killed by `I ^ n`. -/
public noncomputable abbrev blowUpModule {A : Type u} [CommRing A]
    (I : Ideal A) (n : ℕ) (N : ModuleCat.{u} (A ⧸ I ^ n)) :
    (blowUp (Scheme.IdealSheafData.ofIdealTop
      (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom I))).Modules :=
  (Scheme.Modules.pullback
    (blowUpToBase (Scheme.IdealSheafData.ofIdealTop
      (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom I)))).obj
      ((tilde.functor (.of A)).obj
        ((ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ n))).obj N))

private lemma smul_eq_zero_of_iso_kernel
    {R : Type u} [Ring R] {K L K' L' : ModuleCat.{u} R}
    (f : K ⟶ L) (f' : K' ⟶ L') (eK : K ≅ K') (eL : L ≅ L')
    (hcomm : eK.hom ≫ f' = f ≫ eL.hom) (a : R)
    (hkill : ∀ z : K, f.hom z = 0 → a • z = 0)
    (y : K') (hy : f'.hom y = 0) : a • y = 0 := by
  let z := eK.inv.hom y
  have he : eK.hom.hom z = y :=
    congrArg (fun t => t.hom y) eK.inv_hom_id
  have hz : f.hom z = 0 := by
    apply eL.toLinearEquiv.injective
    have hh := congrArg (fun t => t.hom z) hcomm
    change f'.hom (eK.hom.hom z) = eL.hom.hom (f.hom z) at hh
    change eL.hom.hom (f.hom z) = eL.hom.hom 0
    simpa only [he, hy, map_zero] using hh.symm
  have hh := congrArg (fun t => eK.hom.hom t) (hkill z hz)
  simpa only [map_smul, map_zero, he] using hh

/-- The global sections of the sheaf on `Spec A` associated to a module `N` over `q : A →+* Q`
are `N`, as modules over `Γ(Spec A, ⊤) ≅ A`. -/
private def tildeΓLinearEquiv {A Q : Type u} [CommRing A] [CommRing Q] (q : A →+* Q)
    (N : ModuleCat.{u} Q) :
    Γ((tilde.functor (.of A)).obj ((ModuleCat.restrictScalars q).obj N), ⊤) ≃ₗ[
      Γ(Spec (CommRingCat.of A), ⊤)]
      (ModuleCat.restrictScalars (q.comp (Scheme.ΓSpecIso (.of A)).hom.hom)).obj N :=
  let η := (tilde.toTildeΓNatIso (R := CommRingCat.of A)).app
    ((ModuleCat.restrictScalars q).obj N)
  { toFun := η.inv.hom
    invFun := η.hom.hom
    left_inv x := congrArg (fun h => h x) (Iso.inv_hom_id η)
    right_inv x := congrArg (fun h => h x) (Iso.hom_inv_id η)
    map_add' x y := η.inv.hom.map_add x y
    map_smul' r x := by
      let R : Type u := Γ(Spec (CommRingCat.of A), (⊤ : (Spec (CommRingCat.of A)).Opens))
      let γ : R →+* A := (Scheme.ΓSpecIso (.of A)).hom.hom
      let F := (tilde.functor (.of A)).obj ((ModuleCat.restrictScalars q).obj N)
      let : Algebra A R := (Scheme.ΓSpecIso (.of A)).inv.hom.toAlgebra
      let : Module A Γ(F, ⊤) :=
        ((tilde.functor (CommRingCat.of A) ⋙ moduleSpecΓFunctor).obj
          ((ModuleCat.restrictScalars q).obj N)).isModule
      let : IsScalarTower A R Γ(F, ⊤) := IsScalarTower.of_compHom A R Γ(F, ⊤)
      let : Module A N := ((ModuleCat.restrictScalars q).obj N).isModule
      have hγ : algebraMap A R (γ r) = r := by
        change ((Scheme.ΓSpecIso (.of A)).inv.hom.comp
          (Scheme.ΓSpecIso (.of A)).hom.hom) r = r
        exact congrArg (fun h : CommRingCat.of R ⟶ CommRingCat.of R => h.hom r)
          (Iso.hom_inv_id (Scheme.ΓSpecIso (.of A)))
      have hs : (γ r : A) • x = r • x := by
        rw [← IsScalarTower.algebraMap_smul (R := A) (A := R) (γ r) x, hγ]
      change η.inv.hom (r • x) = (γ r : A) • η.inv.hom x
      rw [← hs]
      exact η.inv.hom.map_smul (γ r) x }

private theorem tildeΓLinearEquiv_inv_comp {A Q : Type u} [CommRing A] [CommRing Q] (q : A →+* Q)
    {K L : ModuleCat.{u} Q} (f : K ⟶ L) :
    (tildeΓLinearEquiv q K).toModuleIso.inv ≫ ModuleCat.ofHom
      (Scheme.Modules.sectionsLinearMap
        ((tilde.functor (.of A)).map ((ModuleCat.restrictScalars q).map f)) ⊤) =
      (ModuleCat.restrictScalars (q.comp (Scheme.ΓSpecIso (.of A)).hom.hom)).map f ≫
        (tildeΓLinearEquiv q L).toModuleIso.inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  ext x
  exact congrArg (fun k => k.hom x) ((tilde.toTildeΓNatIso (R := CommRingCat.of A)).inv.naturality
    ((ModuleCat.restrictScalars q).map f))

private theorem baseChange_comp_sectionsLinearMap_pullback_tilde {A Q : Type u} [CommRing A]
    [CommRing Q] (q : A →+* Q) {K L : ModuleCat.{u} Q} (f : K ⟶ L) {Y : Scheme.{u}}
    (p : Y ⟶ Spec (.of A)) {V : Y.Opens} (hV : IsAffineOpen V) (hVU : V ≤ p ⁻¹ᵁ ⊤) :
    (((ModuleCat.extendScalars (p.appLE ⊤ V hVU).hom).mapIso
        (tildeΓLinearEquiv q K).toModuleIso).symm ≪≫
      affinePullbackSectionsBaseChangeIso p _ (isAffineOpen_top _) hV hVU).hom ≫
      ModuleCat.ofHom (Scheme.Modules.sectionsLinearMap ((Scheme.Modules.pullback p).map
        ((tilde.functor (.of A)).map ((ModuleCat.restrictScalars q).map f))) V) =
    (ModuleCat.extendScalars (p.appLE ⊤ V hVU).hom).map
        ((ModuleCat.restrictScalars (q.comp (Scheme.ΓSpecIso (.of A)).hom.hom)).map f) ≫
      (((ModuleCat.extendScalars (p.appLE ⊤ V hVU).hom).mapIso
        (tildeΓLinearEquiv q L).toModuleIso).symm ≪≫
      affinePullbackSectionsBaseChangeIso p _ (isAffineOpen_top _) hV hVU).hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, Category.assoc,
    affinePullbackSectionsBaseChangeIso_natural]
  rw [← Functor.map_comp_assoc, tildeΓLinearEquiv_inv_comp, Functor.map_comp_assoc]

/-- **Tag 0GA8 over an affine open.** Let `0 → K → L → M → 0` be a short exact sequence of
`Q`-modules for `q : A →+* Q`, and let `r : Γ(Spec A, ⊤)` act on `M` through a projective
module. For `p : Y ⟶ Spec A` and an affine open `V` of `Y`, the image of `r` kills the sections
over `V` of the kernel of the pulled-back map `K̃ → L̃`. -/
private theorem appLE_smul_kernel_sections_eq_zero {A Q : Type u} [CommRing A] [CommRing Q]
    (q : A →+* Q) {K L M : ModuleCat.{u} Q} {f : K ⟶ L} {g : L ⟶ M} {w : f ≫ g = 0}
    (hExact : (ShortComplex.mk f g w).ShortExact) (r : Γ(Spec (.of A), ⊤))
    (hfac : ∃ (P : Type u) (_ : AddCommGroup P) (_ : Module Q P)
      (_ : Module.Projective Q P) (α : M →ₗ[Q] P) (β : P →ₗ[Q] M),
        LinearMap.lsmul Q M (q ((Scheme.ΓSpecIso (.of A)).hom.hom r)) = β.comp α)
    {Y : Scheme.{u}} (p : Y ⟶ Spec (.of A)) {V : Y.Opens} (hV : IsAffineOpen V)
    (hVU : V ≤ p ⁻¹ᵁ ⊤)
    (x : Γ(kernel ((Scheme.Modules.pullback p).map
      ((tilde.functor (.of A)).map ((ModuleCat.restrictScalars q).map f))), V)) :
    (p.appLE ⊤ V hVU).hom r • x = 0 := by
  let χ := (Scheme.Modules.pullback p).map
    ((tilde.functor (.of A)).map ((ModuleCat.restrictScalars q).map f))
  let : Algebra Γ(Spec (.of A), ⊤) Γ(Y, V) := (p.appLE ⊤ V hVU).hom.toAlgebra
  obtain ⟨h, hh⟩ := exists_scalar_retraction_of_shortExact hExact _ hfac
  have hyχ : χ.app V ((kernel.ι χ).app V x) = 0 :=
    congrArg (fun t : kernel χ ⟶ _ => (t.app V).hom x) (kernel.condition χ)
  have hkill : (p.appLE ⊤ V hVU).hom r • (kernel.ι χ).app V x = 0 :=
    smul_eq_zero_of_iso_kernel
      ((ModuleCat.extendScalars (p.appLE ⊤ V hVU).hom).map
        ((ModuleCat.restrictScalars (q.comp (Scheme.ΓSpecIso (.of A)).hom.hom)).map f))
      (ModuleCat.ofHom (Scheme.Modules.sectionsLinearMap χ V)) _ _
      (baseChange_comp_sectionsLinearMap_pullback_tilde q f p hV hVU) _
      (quotient_factorization_kills_kernel_after_tensor _ K L f r h hh) _ hyχ
  have hκmono : Function.Injective (AddCommGrpCat.Hom.hom ((kernel.ι χ).app V)) := by
    have hm : Mono (kernel.ι χ).mapPresheaf := Functor.map_mono _ (kernel.ι χ)
    have hmV := (NatTrans.mono_iff_mono_app _).mp hm (Opposite.op V)
    have hmV' : Mono ((kernel.ι χ).app V) := by
      simpa only [Scheme.Modules.mapPresheaf_app] using hmV
    exact (AddCommGrpCat.mono_iff_injective _).mp hmV'
  have hκzero : (kernel.ι χ).app V ((p.appLE ⊤ V hVU).hom r • x) = 0 := by
    rwa [Scheme.Modules.Hom.app_smul]
  exact hκmono (by simpa using hκzero)

/-- In a short exact sequence over `A ⧸ I ^ n` whose quotient is finite and
`I ^ c / I ^ n`-projective, the kernel of the pulled-back first map is
annihilated by the ideal of the `c`-th exceptional thickening. -/
@[stacks 0GA8]
public theorem exceptionalIdeal_pow_le_annihilator_kernel
    {A : Type u} [CommRing A] (I : Ideal A) (n c : ℕ) (_hcn : c ≤ n)
    (K L M : ModuleCat.{u} (A ⧸ I ^ n))
    (f : K ⟶ L) (g : L ⟶ M) (w : f ≫ g = 0)
    (hExact : (ShortComplex.mk f g w).ShortExact)
    [Module.Finite (A ⧸ I ^ n) M]
    (hM : Module.IsIProjective (A ⧸ I ^ n)
      (Ideal.map (Ideal.Quotient.mk (I ^ n)) (I ^ c)) M) :
    (exceptionalIdeal (Scheme.IdealSheafData.ofIdealTop
      (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom I))) ^ c ≤
      Scheme.Modules.annihilatorIdeal
        (kernel ((Scheme.Modules.pullback
          (blowUpToBase (Scheme.IdealSheafData.ofIdealTop
            (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom I)))).map
              ((tilde.functor (.of A)).map
              ((ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ n))).map f)))) := by
  classical
  let q : A →+* A ⧸ I ^ n := Ideal.Quotient.mk (I ^ n)
  let J : (Spec (CommRingCat.of A)).IdealSheafData := Scheme.IdealSheafData.ofIdealTop
    (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom I)
  let p : blowUp J ⟶ Spec (CommRingCat.of A) := blowUpToBase J
  let H := kernel ((Scheme.Modules.pullback p).map
    ((tilde.functor (.of A)).map ((ModuleCat.restrictScalars q).map f)))
  change (exceptionalIdeal J) ^ c ≤ Scheme.Modules.annihilatorIdeal H
  rw [Scheme.Modules.annihilatorIdeal, Scheme.IdealSheafData.le_ofIdeals_iff]
  intro V
  change ((exceptionalIdeal J) ^ c).ideal V ≤
    Module.annihilator Γ((blowUp J), V.1) Γ(H, V.1)
  rw [Scheme.IdealSheafData.ideal_pow, exceptionalIdeal]
  change ((J.comap p).ideal V) ^ c ≤
    Module.annihilator Γ((blowUp J), V.1) Γ(H, V.1)
  rw [Stacks.IdealSheaf.ideal_comap_appLE J p
    ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of A))⟩ V (by simp)]
  rw [← Ideal.map_pow]
  apply Ideal.map_le_iff_le_comap.mpr
  intro r hr
  have htop : (Spec (CommRingCat.of A)).presheaf.map
      (homOfLE (show (⊤ : (Spec (CommRingCat.of A)).Opens) ≤ ⊤ from le_top)).op =
      𝟙 _ := by
    rw [show homOfLE (show (⊤ : (Spec (CommRingCat.of A)).Opens) ≤ ⊤ from le_top) = 𝟙 _ from
      Subsingleton.elim _ _]
    simp
  have hr' : r ∈ (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom I) ^ c := by
    simpa [J, Scheme.IdealSheafData.ofIdealTop_ideal, htop] using hr
  rw [← Ideal.map_pow] at hr'
  obtain ⟨a, ha, har⟩ := (Ideal.mem_map_iff_of_surjective (Scheme.ΓSpecIso (.of A)).inv.hom
    fun r => ⟨(Scheme.ΓSpecIso (.of A)).hom r, by simp⟩).mp hr'
  have hγr : (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom r = a := by
    rw [← har]
    simp
  rw [Ideal.mem_comap]
  refine Module.mem_annihilator.mpr fun x =>
    appLE_smul_kernel_sections_eq_zero q hExact r ?_ p V.2 (by simp) x
  rw [hγr]
  exact hM (q a) (Ideal.mem_map_of_mem q ha)

end AlgebraicGeometry

end
