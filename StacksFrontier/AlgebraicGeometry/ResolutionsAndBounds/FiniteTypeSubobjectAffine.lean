module

public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.RingTheory.Localization.Away.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.FiniteTilde
public import StacksFrontier.AlgebraicGeometry.CardinalGeneration.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentBaseChange
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness
public import StacksFrontier.RingTheory.Module.LocallyFree.SheafBridge

/-!
# Finite-type quasi-coherent subobjects over an affine scheme

Let `H` be a quasi-coherent module on an affine scheme and let `U` be a quasi-compact open on
which `H` is of finite type. This file produces a quasi-coherent submodule `K ≤ H` of finite
type whose inclusion becomes an isomorphism after restriction to `U`. This is the affine case
of the argument of [Stacks, Tag 01PF]; the globalisation to an arbitrary scheme is not treated
here.

## Main results

* `AlgebraicGeometry.exists_finiteTypeQuasicoherentSubobject_isIso_restrict_of_spec`: the
  statement above for `Spec R`.
* `AlgebraicGeometry.exists_finiteTypeQuasicoherentSubobject_isIso_restrict_of_isAffine`: the
  same statement for an arbitrary affine scheme, obtained by transport along `Scheme.isoSpec`.
* `AlgebraicGeometry.mono_restrictFunctor_map`: restriction along an open immersion preserves
  monomorphisms.
* `AlgebraicGeometry.surjective_app_of_eq_basicOpen`: a criterion for a morphism of
  quasi-coherent modules on `Spec R` to be surjective on the sections over a standard open.
* `AlgebraicGeometry.isIso_restrictFunctor_map_of_pow_smul_mem_range`: a monomorphism of
  quasi-coherent modules on `Spec R` whose image on global sections exhausts the target up to
  powers of finitely many elements covering `U` restricts to an isomorphism over `U`.
* `AlgebraicGeometry.module_finite_localizedModule_of_isFiniteType`: if `M̃` is of finite type
  on an open containing `D(a)`, then `M_a` is a finite `R_a`-module.
* `AlgebraicGeometry.exists_fg_forall_exists_pow_smul_mem`: the underlying algebra, that a
  module whose localization at `a` is finite over `R_a` has a finitely generated submodule
  containing a power of `a` times every element.

## Implementation notes

Write `N := Γ(H, ⊤)`. Quasi-coherence makes `H` isomorphic to `Ñ` and makes the restriction map
`N → Γ(H, D(a))` a localization at `a`
(`Stacks.AlgebraicGeometry.QuasicoherentBaseChange.specIsLocalizedModule`); the whole argument
is run through that dictionary, so no section of `H` is ever computed. Quasi-compactness of `U`
gives finitely many standard opens `D(a i) ≤ U` covering `U`, and finite type of `H|_U` makes
each `N_{a i}` a finite `R_{a i}`-module; the submodule `K` is `Ñ'` for `N' ≤ N` a finitely
generated submodule with `N'_{a i} = N_{a i}` for every `i`.

That the inclusion is an isomorphism over `U` is checked with
`Stacks.AlgebraicGeometry.CardinalGeneration.isIso_of_mono_of_locallySurjective`: on sections
over a standard open `D(b) ≤ D(a i)` the inclusion is surjective because `a i` acts invertibly
there (`AlgebraicGeometry.Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen`) and because
`N'` already contains a power of `a i` times every element of `N`.

The finiteness of `N_{a i}` is read off `AlgebraicGeometry.tilde_isFiniteType_iff` on
`Spec R_{a i}`, transported along `bridge_N_iso`, which identifies the restriction of `Ñ` to
`D(a)` with the sheaf associated with `N_a` over `Spec R_a`.

The affine statement is deduced from the one on a spectrum by restricting along the two
directions of `Scheme.isoSpec`; the two restriction functors are inverse to one another up to
the natural isomorphisms `Scheme.Modules.restrictFunctorComp` and
`Scheme.Modules.restrictFunctorId`, and the open `U` corresponds to its image under the
isomorphism, the two restrictions to it being compared through the isomorphism of open
subschemes supplied by `AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq`.

## References

* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
* [Stacks Project, Tag 01PB](https://stacks.math.columbia.edu/tag/01PB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange
open Stacks.AlgebraicGeometry.CardinalGeneration
open Stacks.AlgebraicGeometry.CoherentTFAE

universe u

namespace AlgebraicGeometry

/-! ### The algebra -/

/-- If the localization `N_a` is a finite `R_a`-module, then `N` has a finitely generated
submodule `P` such that every element of `N` has a power of `a` times it in `P`. -/
theorem exists_fg_forall_exists_pow_smul_mem {R : Type u} [CommRing R] {N : Type u}
    [AddCommGroup N] [Module R N] (a : R)
    (h : Module.Finite (Localization.Away a) (LocalizedModule (Submonoid.powers a) N)) :
    ∃ P : Submodule R N, P.FG ∧ ∀ y : N, ∃ k : ℕ, a ^ k • y ∈ P := by
  classical
  set p : Submonoid R := Submonoid.powers a with hp
  set f : N →ₗ[R] LocalizedModule p N := LocalizedModule.mkLinearMap p N with hf
  obtain ⟨t, htfin, htspan⟩ := Submodule.fg_def.mp (Module.finite_def.mp h)
  have hrep : ∀ x : LocalizedModule p N, ∃ (m : N) (s : p), IsLocalizedModule.mk' f m s = x :=
    fun x ↦ by
      obtain ⟨⟨m, s⟩, hms⟩ := IsLocalizedModule.mk'_surjective p f x
      exact ⟨m, s, hms⟩
  choose m s hms using hrep
  refine ⟨Submodule.span R (m '' t), Submodule.fg_span (htfin.image m), fun y ↦ ?_⟩
  have hkey : (Submodule.span R (m '' t)).localized' (Localization.Away a) p f = ⊤ := by
    rw [eq_top_iff, ← htspan, Submodule.span_le]
    exact fun x hx ↦ ⟨m x, Submodule.subset_span ⟨x, hx, rfl⟩, s x, hms x⟩
  have hy : f y ∈ (Submodule.span R (m '' t)).localized₀ p f := by
    rw [← Submodule.restrictScalars_localized' (S := Localization.Away a), hkey]
    trivial
  obtain ⟨w, hw, c, hc⟩ := hy
  rw [IsLocalizedModule.mk'_eq_iff] at hc
  have hcy : f ((c : R) • y) = f w := by
    rw [map_smul, ← Submonoid.smul_def]
    exact hc.symm
  obtain ⟨d, hd⟩ := (IsLocalizedModule.eq_iff_exists p f).mp hcy
  obtain ⟨i, hi⟩ := d.2
  obtain ⟨j, hj⟩ := c.2
  refine ⟨i + j, ?_⟩
  have hi' : a ^ i = (d : R) := hi
  have hj' : a ^ j = (c : R) := hj
  have hsmul : a ^ (i + j) • y = (d : R) • w := by
    rw [pow_add, hi', hj', mul_smul]
    exact hd
  rw [hsmul]
  exact Submodule.smul_mem _ _ hw

/-! ### Finiteness of the localized module -/

/-- If `M̃` is of finite type after restriction to an open `U` containing the standard open
`D(a)`, then the localization `M_a` is a finite `R_a`-module. -/
theorem module_finite_localizedModule_of_isFiniteType {R : CommRingCat.{u}}
    (M : ModuleCat.{u} R) (a : R) (U : (Spec R).Opens)
    (hU : PrimeSpectrum.basicOpen a ≤ U) (h : ((tilde M).restrict U.ι).IsFiniteType) :
    Module.Finite (Localization.Away a) (LocalizedModule (Submonoid.powers a) M) := by
  have hle : specBasicOpen (R : Type u) a ≤ U := hU
  have hOI : IsOpenImmersion ((Spec R).homOfLE hle) :=
    AlgebraicGeometry.instIsOpenImmersionHomOfLE (Spec R) hle
  have h1 : (((tilde M).restrict U.ι).restrict ((Spec R).homOfLE hle)).IsFiniteType :=
    isFiniteType_restrict ((Spec R).homOfLE hle) ((tilde M).restrict U.ι)
  have hcomp : (specBasicOpen (R : Type u) a).ι = (Spec R).homOfLE hle ≫ U.ι :=
    (Scheme.homOfLE_ι (Spec R) hle).symm
  have e1 : (tilde M).restrict (specBasicOpen (R : Type u) a).ι ≅
      ((tilde M).restrict U.ι).restrict ((Spec R).homOfLE hle) :=
    (Scheme.Modules.restrictFunctorCongr hcomp).app (tilde M) ≪≫
      (Scheme.Modules.restrictFunctorComp ((Spec R).homOfLE hle) U.ι).app (tilde M)
  have h2 : ((tilde M).restrict (specBasicOpen (R : Type u) a).ι).IsFiniteType :=
    Stacks.SheafOfModules.isFiniteType_of_iso.{u} e1.symm
  have h3 : ((bridge_specAwayEquiv (R : Type u) a).functor.obj
      ((tilde M).restrict (specBasicOpen (R : Type u) a).ι)).IsFiniteType :=
    @isFiniteType_restrict _ ((specBasicOpen (R : Type u) a).toScheme)
      (AlgebraicGeometry.basicOpenIsoSpecAway (R := R) a).inv
      (@IsOpenImmersion.of_isIso _ _ _ (Iso.isIso_inv _))
      ((tilde M).restrict (specBasicOpen (R : Type u) a).ι) h2
  refine (tilde_isFiniteType_iff (R := CommRingCat.of (Localization.Away a))
    (ModuleCat.of (Localization.Away a)
      (LocalizedModule (Submonoid.powers a) (M : Type u)))).mp ?_
  exact Stacks.SheafOfModules.isFiniteType_of_iso.{u} (bridge_N_iso (R : Type u) (M : Type u) a)

/-! ### Surjectivity on sections over a standard open -/

/-- A point of an open of `Spec R` has a standard open neighbourhood inside it. -/
private theorem exists_basicOpen_le {R : CommRingCat.{u}} (y : Spec R) (G : (Spec R).Opens)
    (hy : y ∈ G) :
    ∃ (b : R) (V : (Spec R).Opens), V = PrimeSpectrum.basicOpen b ∧ y ∈ V ∧ V ≤ G := by
  obtain ⟨-, ⟨-, ⟨b, rfl⟩, rfl⟩, hyb, hbG⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hy G.2
  exact ⟨b, PrimeSpectrum.basicOpen b, rfl, hyb, hbG⟩

/-- Let `φ : K ⟶ H` be a morphism of modules on `Spec R` with `H` quasi-coherent, and let `V`
be a standard open `D(b)` contained in another standard open `D(c)`. If every element of
`Γ(H, ⊤)` has a power of `c` times it in the image of `φ` on global sections, then `φ` is
surjective on the sections over `V`. -/
theorem surjective_app_of_eq_basicOpen {R : CommRingCat.{u}} {K H : (Spec R).Modules}
    [H.IsQuasicoherent] (φ : K ⟶ H) (b c : R) {V : (Spec R).Opens}
    (hV : V = PrimeSpectrum.basicOpen b) (hVc : V ≤ PrimeSpectrum.basicOpen c)
    (hgen : ∀ y : Γ(H, ⊤), ∃ k : ℕ, c ^ k • y ∈ Set.range (φ.app ⊤)) :
    Function.Surjective (φ.app V) := by
  classical
  have hsmul : ∀ (r : R) (x : Γ(K, V)), φ.app V (r • x) = r • φ.app V x := fun r x ↦ by
    rw [Scheme.Modules.smul_Spec_def, Scheme.Modules.smul_Spec_def, Scheme.Modules.Hom.app_smul]
  have hloc : IsLocalizedModule.Away b (specRestrictₗ H (le_top (a := V))) :=
    specIsLocalizedModule H b hV
  intro z
  obtain ⟨⟨y, s⟩, hs⟩ := IsLocalizedModule.surj (Submonoid.powers b)
    (specRestrictₗ H (le_top (a := V))) z
  obtain ⟨k, w, hw⟩ := hgen y
  obtain ⟨m, hm⟩ := s.2
  have hm' : b ^ m = (s : R) := hm
  have hs' : (s : R) • z = H.presheaf.map (homOfLE (le_top (a := V))).op y := hs
  set r : R := c ^ k * (s : R) with hr
  have hrfac : r = c ^ k * b ^ m := by rw [hr, hm']
  have hVb : V ≤ PrimeSpectrum.basicOpen b := hV.le
  have hunit : ∀ M : (Spec R).Modules,
      IsUnit (algebraMap R (Module.End R Γ(M, V)) r) := fun M ↦ by
    rw [hrfac, map_mul, map_pow, map_pow]
    exact ((Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen (M := M) c hVc).pow k).mul
      ((Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen (M := M) b hVb).pow m)
  have h1 : r • z = φ.app V (K.presheaf.map (homOfLE (le_top (a := V))).op w) := by
    calc r • z = c ^ k • ((s : R) • z) := by rw [hr, mul_smul]
      _ = c ^ k • H.presheaf.map (homOfLE (le_top (a := V))).op y := by rw [hs']
      _ = H.presheaf.map (homOfLE (le_top (a := V))).op (c ^ k • y) :=
            (Scheme.Modules.map_smul_Spec _ _ _).symm
      _ = H.presheaf.map (homOfLE (le_top (a := V))).op (φ.app ⊤ w) := by rw [hw]
      _ = φ.app V (K.presheaf.map (homOfLE (le_top (a := V))).op w) :=
            (app_map φ (homOfLE (le_top (a := V))) w).symm
  obtain ⟨x, hx⟩ := ((Module.End.isUnit_iff _).mp (hunit K)).2
    (K.presheaf.map (homOfLE (le_top (a := V))).op w)
  refine ⟨x, ((Module.End.isUnit_iff _).mp (hunit H)).1 ?_⟩
  show r • φ.app V x = r • z
  rw [← hsmul, show r • x = K.presheaf.map (homOfLE (le_top (a := V))).op w from hx, h1]

/-! ### The local isomorphism criterion -/

/-- Restriction along an open immersion preserves monomorphisms: it is injective on sections
over every open, and the forgetful functor to presheaves of abelian groups is faithful. -/
theorem mono_restrictFunctor_map {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    {M N : Y.Modules} (φ : M ⟶ N) [Mono φ] :
    Mono ((Scheme.Modules.restrictFunctor f).map φ) := by
  apply Functor.mono_of_mono_map (F := Scheme.Modules.toPresheaf X)
  have hall : ∀ W, Mono (((Scheme.Modules.toPresheaf X).map
      ((Scheme.Modules.restrictFunctor f).map φ)).app W) := fun W ↦ by
    rw [AddCommGrpCat.mono_iff_injective]
    exact injective_app_of_mono φ _
  exact NatTrans.mono_of_mono_app _

/-- Let `φ : K ⟶ H` be a monomorphism of modules on `Spec R` with `H` quasi-coherent, let `U`
be an open covered by the standard opens `D(a i)`, and suppose every element of `Γ(H, ⊤)` has a
power of each `a i` times it in the image of `φ` on global sections. Then `φ` restricts to an
isomorphism over `U`. -/
theorem isIso_restrictFunctor_map_of_pow_smul_mem_range {R : CommRingCat.{u}}
    {K H : (Spec R).Modules} [H.IsQuasicoherent] (φ : K ⟶ H) [Mono φ] (U : (Spec R).Opens)
    {ι : Type*} (a : ι → R) (hcover : U ≤ ⨆ i, PrimeSpectrum.basicOpen (a i))
    (hgen : ∀ (i : ι) (y : Γ(H, ⊤)), ∃ k : ℕ, a i ^ k • y ∈ Set.range (φ.app ⊤)) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map φ) := by
  have hmono : Mono ((Scheme.Modules.restrictFunctor U.ι).map φ) :=
    mono_restrictFunctor_map U.ι φ
  refine isIso_of_mono_of_locallySurjective _ ?_
  intro W s x hx
  have hximg : U.ι x ∈ U.ι ''ᵁ W := by
    have h : x ∈ U.ι ⁻¹ᵁ (U.ι ''ᵁ W) := by rw [Scheme.Hom.preimage_image_eq]; exact hx
    exact h
  have hxU : U.ι x ∈ U := by
    have h : U.ι x ∈ U.ι.opensRange := ⟨x, rfl⟩
    rwa [Scheme.Opens.opensRange_ι] at h
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcover hxU)
  obtain ⟨b, V, hVb, hxV, hVsub⟩ := exists_basicOpen_le (U.ι x)
    ((U.ι ''ᵁ W) ⊓ PrimeSpectrum.basicOpen (a i)) ⟨hximg, hi⟩
  have hWU : U.ι ''ᵁ W ≤ U :=
    (U.ι.image_le_opensRange W).trans (Scheme.Opens.opensRange_ι U).le
  have hVU : V ≤ U := le_trans (le_trans hVsub inf_le_left) hWU
  have himg : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hVU]
  refine ⟨U.ι ⁻¹ᵁ V, fun y hy ↦ ?_, hxV, ?_⟩
  · have h : y ∈ U.ι ⁻¹ᵁ (U.ι ''ᵁ W) := (le_trans hVsub inf_le_left) hy
    rwa [Scheme.Hom.preimage_image_eq] at h
  · have hsurj : Function.Surjective
        (φ.app (U.ι ''ᵁ (U.ι ⁻¹ᵁ V))) := by
      refine surjective_app_of_eq_basicOpen φ b (a i) (himg.trans hVb) ?_ (hgen i)
      exact le_trans (le_of_eq himg) (le_trans hVsub inf_le_right)
    exact hsurj _

/-! ### Standard open covers of a quasi-compact open -/

/-- A quasi-compact open of `Spec R` is covered by finitely many standard opens contained in
it.

The ring is a `CommRingCat` and the index of the cover an arbitrary finite type;
`AlgebraicGeometry.exists_finite_basicOpen_cover_of_isCompact` is the variant for a bare
`CommRing` which moreover indexes the cover by `Fin n` and gives the covering as an equality of
opens rather than as an inequality. -/
theorem exists_finite_basicOpen_cover_of_isCompact' {R : CommRingCat.{u}} (U : (Spec R).Opens)
    (hU : IsCompact U.1) :
    ∃ (ι : Type u) (_ : Finite ι) (a : ι → R),
      (∀ i, PrimeSpectrum.basicOpen (a i) ≤ U) ∧ U ≤ ⨆ i, PrimeSpectrum.basicOpen (a i) := by
  classical
  have hsub : U.1 ⊆ ⋃ VV : {V : (Spec R).Opens //
      (∃ b : R, V = PrimeSpectrum.basicOpen b) ∧ V ≤ U}, (VV.1 : Set (Spec R)) := by
    intro y hy
    obtain ⟨b, V, hVb, hyV, hVU⟩ := exists_basicOpen_le y U hy
    exact Set.mem_iUnion.mpr ⟨⟨V, ⟨b, hVb⟩, hVU⟩, hyV⟩
  obtain ⟨t, ht⟩ := hU.elim_finite_subcover
    (fun VV : {V : (Spec R).Opens // (∃ b : R, V = PrimeSpectrum.basicOpen b) ∧ V ≤ U} ↦
      (VV.1 : Set (Spec R))) (fun VV ↦ VV.1.2) hsub
  choose b hb using fun VV : {V : (Spec R).Opens //
    (∃ b : R, V = PrimeSpectrum.basicOpen b) ∧ V ≤ U} ↦ VV.2.1
  refine ⟨{VV : {V : (Spec R).Opens // (∃ b : R, V = PrimeSpectrum.basicOpen b) ∧ V ≤ U} //
    VV ∈ t}, inferInstance, fun i ↦ b i.1, fun i ↦ ?_, fun y hy ↦ ?_⟩
  · rw [← hb i.1]
    exact i.1.2.2
  · obtain ⟨VV, hVVt, hyVV⟩ := Set.mem_iUnion₂.mp (ht hy)
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨VV, hVVt⟩, ?_⟩
    rw [← hb VV]
    exact hyVV

/-! ### Comparison maps on global sections -/

/-- `tilde.map` is compatible with the canonical map from a module to the sections of its
associated sheaf. -/
private theorem tildeMap_app_toOpen {R : CommRingCat.{u}} {M N : ModuleCat.{u} R} (f : M ⟶ N)
    (V : (Spec R).Opens) (x : M) :
    (tilde.map f).app V (tilde.toOpen M V x) = tilde.toOpen N V (f x) :=
  congr($(tilde.toOpen_map_app f V) x)

/-- The counit of the tilde-Gamma adjunction undoes the canonical map on global sections. -/
private theorem fromTildeΓ_app_top_toOpen {R : CommRingCat.{u}} (M : (Spec R).Modules)
    (x : Γ(M, ⊤)) : M.fromTildeΓ.app ⊤ (tilde.toOpen _ ⊤ x) = x := by
  have h : tilde.toOpen ((modulesSpecToSheaf.obj M).presheaf.obj (op ⊤)) ⊤ ≫
      (modulesSpecToSheaf.map M.fromTildeΓ).1.app (op ⊤) = 𝟙 _ := by
    rw [Scheme.Modules.toOpen_fromTildeΓ_app]
    exact (modulesSpecToSheaf.obj M).1.map_id _
  exact congr($h x)

/-- The subobject given by a monomorphism from a quasi-coherent module of finite type is
quasi-coherent and of finite type. -/
private theorem subobject_mk_isQuasicoherent_and_isFiniteType {X : Scheme.{u}} {A H : X.Modules}
    (f : A ⟶ H) [Mono f] [A.IsQuasicoherent] (hA : A.IsFiniteType) :
    ((Subobject.mk f : Subobject H) : X.Modules).IsQuasicoherent ∧
      ((Subobject.mk f : Subobject H) : X.Modules).IsFiniteType :=
  ⟨(SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (Subobject.underlyingIso f).symm inferInstance,
    Stacks.SheafOfModules.isFiniteType_of_iso.{u} (Subobject.underlyingIso f).symm⟩

/-! ### The affine case of Stacks 01PF -/

/-- **The affine case of [Stacks, Tag 01PF].** Let `H` be a quasi-coherent module on `Spec R`
and let `U` be a quasi-compact open on which `H` is of finite type. Then `H` has a
quasi-coherent subobject of finite type whose inclusion restricts to an isomorphism over `U`. -/
theorem exists_finiteTypeQuasicoherentSubobject_isIso_restrict_of_spec
    {R : CommRingCat.{u}} (H : (Spec R).Modules) [H.IsQuasicoherent]
    (U : (Spec R).Opens) (hU : IsCompact U.1) [(H.restrict U.ι).IsFiniteType] :
    ∃ K : CategoryTheory.Subobject H, (K : (Spec R).Modules).IsQuasicoherent ∧
      (K : (Spec R).Modules).IsFiniteType ∧
      CategoryTheory.IsIso ((Scheme.Modules.restrictFunctor U.ι).map K.arrow) := by
  classical
  obtain ⟨ι, hιfin, a, hale, hacover⟩ := exists_finite_basicOpen_cover_of_isCompact' U hU
  have hιfin' : Finite ι := hιfin
  have htildeft :
      ((tilde ((modulesSpecToSheaf.obj H).presheaf.obj (op ⊤))).restrict U.ι).IsFiniteType :=
    Stacks.SheafOfModules.isFiniteType_of_iso.{u}
      ((Scheme.Modules.restrictFunctor U.ι).mapIso (asIso H.fromTildeΓ)).symm
  have hfin : ∀ i : ι, Module.Finite (Localization.Away (a i))
      (LocalizedModule (Submonoid.powers (a i))
        ((modulesSpecToSheaf.obj H).presheaf.obj (op ⊤))) := fun i ↦
    module_finite_localizedModule_of_isFiniteType
      ((modulesSpecToSheaf.obj H).presheaf.obj (op ⊤)) (a i) U (hale i) htildeft
  choose P hPfg hPmem using fun i : ι ↦ exists_fg_forall_exists_pow_smul_mem (a i) (hfin i)
  set Q : Submodule R ((modulesSpecToSheaf.obj H).presheaf.obj (op ⊤)) := ⨆ i, P i with hQdef
  have hQfg : Q.FG := Submodule.fg_iSup P hPfg
  have hQmem : ∀ (i : ι) (y : (modulesSpecToSheaf.obj H).presheaf.obj (op ⊤)),
      ∃ k : ℕ, a i ^ k • y ∈ Q := fun i y ↦ by
    obtain ⟨k, hk⟩ := hPmem i y
    exact ⟨k, le_iSup P i hk⟩
  have hQfinite : Module.Finite R Q := Module.Finite.iff_fg.mpr hQfg
  have hinclmono : Mono (ModuleCat.ofHom Q.subtype) := by
    rw [ModuleCat.mono_iff_injective]
    exact Subtype.val_injective
  have hmono1 : Mono (tilde.map (ModuleCat.ofHom Q.subtype)) := by
    have hm : Mono ((tilde.functor R).map (ModuleCat.ofHom Q.subtype)) := inferInstance
    exact hm
  have hmonoε : Mono H.fromTildeΓ := by
    have hiso : IsIso H.fromTildeΓ := inferInstance
    infer_instance
  have hmonoφ : Mono (tilde.map (ModuleCat.ofHom Q.subtype) ≫ H.fromTildeΓ) :=
    mono_comp (tilde.map (ModuleCat.ofHom Q.subtype)) H.fromTildeΓ
  have hft : (tilde (ModuleCat.of R Q)).IsFiniteType :=
    (tilde_isFiniteType_iff (ModuleCat.of R Q)).mpr hQfinite
  have hsub := subobject_mk_isQuasicoherent_and_isFiniteType
    (tilde.map (ModuleCat.ofHom Q.subtype) ≫ H.fromTildeΓ) hft
  refine ⟨Subobject.mk (tilde.map (ModuleCat.ofHom Q.subtype) ≫ H.fromTildeΓ),
    hsub.1, hsub.2, ?_⟩
  refine isIso_restrictFunctor_map_of_pow_smul_mem_range _ U a hacover ?_
  intro i y
  obtain ⟨k, hk⟩ := hQmem i y
  refine ⟨k, (Subobject.underlyingIso
    (tilde.map (ModuleCat.ofHom Q.subtype) ≫ H.fromTildeΓ)).inv.app ⊤
      (tilde.toOpen (ModuleCat.of R Q) ⊤ ⟨a i ^ k • y, hk⟩), ?_⟩
  have harrow := congrArg
    (fun g : tilde (ModuleCat.of R Q) ⟶ H ↦ g.app ⊤)
    (Subobject.underlyingIso_arrow (tilde.map (ModuleCat.ofHom Q.subtype) ≫ H.fromTildeΓ))
  refine (congr($harrow (tilde.toOpen (ModuleCat.of R Q) ⊤ ⟨a i ^ k • y, hk⟩))).trans ?_
  show H.fromTildeΓ.app ⊤ ((tilde.map (ModuleCat.ofHom Q.subtype)).app ⊤
    (tilde.toOpen (ModuleCat.of R Q) ⊤ ⟨a i ^ k • y, hk⟩)) = a i ^ k • y
  rw [tildeMap_app_toOpen]
  exact fromTildeΓ_app_top_toOpen H _

/-! ### Transport along an isomorphism of schemes -/

/-- The restrictions of `U` and of its image `e.hom ''ᵁ U` to open subschemes are isomorphic
compatibly with `e`. -/
private theorem exists_iso_opens_ι_comp {Z W : Scheme.{u}} (e : Z ≅ W)
    [IsOpenImmersion e.hom] (U : Z.Opens) :
    ∃ κ : (U : Scheme.{u}) ≅ (e.hom ''ᵁ U : Scheme.{u}),
      κ.hom ≫ (e.hom ''ᵁ U).ι = U.ι ≫ e.hom := by
  have hrange : Set.range (U.ι ≫ e.hom).base = Set.range (e.hom ''ᵁ U).ι.base := by
    simp [Set.range_comp, Scheme.Opens.range_ι]
  exact ⟨_, IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hrange⟩

/-- Finite type of a restriction is carried along an isomorphism of schemes. -/
private theorem isFiniteType_restrict_image_of_iso {Z W : Scheme.{u}} (e : Z ≅ W)
    [IsOpenImmersion e.hom] [IsOpenImmersion e.inv] (H : Z.Modules) (U : Z.Opens)
    (h : (H.restrict U.ι).IsFiniteType) :
    (((Scheme.Modules.restrictFunctor e.inv).obj H).restrict (e.hom ''ᵁ U).ι).IsFiniteType := by
  obtain ⟨κ, hκfac⟩ := exists_iso_opens_ι_comp e U
  have hOIκi : IsOpenImmersion κ.inv := IsOpenImmersion.of_isIso _
  have h' : κ.hom ≫ (e.hom ''ᵁ U).ι ≫ e.inv = U.ι := by
    rw [← Category.assoc, hκfac, Category.assoc, e.hom_inv_id, Category.comp_id]
  have hfac2 : (e.hom ''ᵁ U).ι ≫ e.inv = κ.inv ≫ U.ι := by
    rw [← h', Iso.inv_hom_id_assoc]
  have hres : ((H.restrict U.ι).restrict κ.inv).IsFiniteType :=
    isFiniteType_restrict κ.inv (H.restrict U.ι)
  have iso : ((Scheme.Modules.restrictFunctor e.inv).obj H).restrict (e.hom ''ᵁ U).ι ≅
      (H.restrict U.ι).restrict κ.inv :=
    ((Scheme.Modules.restrictFunctorComp (e.hom ''ᵁ U).ι e.inv).app H).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr hfac2).app H ≪≫
      (Scheme.Modules.restrictFunctorComp κ.inv U.ι).app H
  exact Stacks.SheafOfModules.isFiniteType_of_iso.{u} iso.symm

/-- Transport of a finite-type quasi-coherent subobject along an isomorphism of schemes. -/
private theorem transport_along_iso {Z W : Scheme.{u}} (e : Z ≅ W)
    [IsOpenImmersion e.hom] [IsOpenImmersion e.inv] (H : Z.Modules) (U : Z.Opens)
    (K' : Subobject ((Scheme.Modules.restrictFunctor e.inv).obj H))
    (hqc : (K' : W.Modules).IsQuasicoherent) (hft : (K' : W.Modules).IsFiniteType)
    (hiso : IsIso ((Scheme.Modules.restrictFunctor (e.hom ''ᵁ U).ι).map K'.arrow)) :
    ∃ K : Subobject H, (K : Z.Modules).IsQuasicoherent ∧ (K : Z.Modules).IsFiniteType ∧
      IsIso ((Scheme.Modules.restrictFunctor U.ι).map K.arrow) := by
  have η : Scheme.Modules.restrictFunctor e.inv ⋙ Scheme.Modules.restrictFunctor e.hom ≅
      𝟭 Z.Modules :=
    (Scheme.Modules.restrictFunctorComp e.hom e.inv).symm ≪≫
      Scheme.Modules.restrictFunctorCongr e.hom_inv_id ≪≫ Scheme.Modules.restrictFunctorId
  set ψ : (Scheme.Modules.restrictFunctor e.hom).obj (K' : W.Modules) ⟶ H :=
    (Scheme.Modules.restrictFunctor e.hom).map K'.arrow ≫ (η.app H).hom with hψ
  have hm1 : Mono ((Scheme.Modules.restrictFunctor e.hom).map K'.arrow) :=
    mono_restrictFunctor_map e.hom K'.arrow
  have hm2 : Mono (η.app H).hom := by
    have hi : IsIso (η.app H).hom := inferInstance
    infer_instance
  have hmonoψ : Mono ψ := by
    rw [hψ]
    exact mono_comp _ _
  obtain ⟨κ, hκfac⟩ := exists_iso_opens_ι_comp e U
  have α : Scheme.Modules.restrictFunctor e.hom ⋙ Scheme.Modules.restrictFunctor U.ι ≅
      Scheme.Modules.restrictFunctor (e.hom ''ᵁ U).ι ⋙ Scheme.Modules.restrictFunctor κ.hom :=
    (Scheme.Modules.restrictFunctorComp U.ι e.hom).symm ≪≫
      Scheme.Modules.restrictFunctorCongr hκfac.symm ≪≫
      Scheme.Modules.restrictFunctorComp κ.hom (e.hom ''ᵁ U).ι
  have hmapiso : IsIso ((Scheme.Modules.restrictFunctor (e.hom ''ᵁ U).ι ⋙
      Scheme.Modules.restrictFunctor κ.hom).map K'.arrow) := by
    have hi := hiso
    exact Functor.map_isIso (Scheme.Modules.restrictFunctor κ.hom) _
  have h1 : IsIso ((Scheme.Modules.restrictFunctor e.hom ⋙
      Scheme.Modules.restrictFunctor U.ι).map K'.arrow) :=
    (NatIso.isIso_map_iff α K'.arrow).mpr hmapiso
  have h2 : IsIso ((Scheme.Modules.restrictFunctor U.ι).map ψ) := by
    rw [hψ, Functor.map_comp]
    have h1' : IsIso ((Scheme.Modules.restrictFunctor U.ι).map
      ((Scheme.Modules.restrictFunctor e.hom).map K'.arrow)) := h1
    have h3 : IsIso ((Scheme.Modules.restrictFunctor U.ι).map (η.app H).hom) :=
      Functor.map_isIso _ _
    infer_instance
  have hft' : ((Scheme.Modules.restrictFunctor e.hom).obj (K' : W.Modules)).IsFiniteType :=
    isFiniteType_restrict e.hom (K' : W.Modules)
  have hsub := subobject_mk_isQuasicoherent_and_isFiniteType ψ hft'
  refine ⟨Subobject.mk ψ, hsub.1, hsub.2, ?_⟩
  have heq : (Subobject.mk ψ).arrow = (Subobject.underlyingIso ψ).hom ≫ ψ :=
    (Iso.hom_inv_id_assoc (Subobject.underlyingIso ψ) (Subobject.mk ψ).arrow).symm.trans
      (congrArg (fun g ↦ (Subobject.underlyingIso ψ).hom ≫ g)
        (Subobject.underlyingIso_arrow ψ))
  rw [heq, Functor.map_comp]
  have h4 : IsIso ((Scheme.Modules.restrictFunctor U.ι).map
    (Subobject.underlyingIso ψ).hom) := Functor.map_isIso _ _
  have h5 := h2
  infer_instance

/-- **The affine case of [Stacks, Tag 01PF].** Let `H` be a quasi-coherent module on an affine
scheme `Z` and let `U` be a quasi-compact open on which `H` is of finite type. Then `H` has a
quasi-coherent subobject of finite type whose inclusion restricts to an isomorphism over `U`. -/
theorem exists_finiteTypeQuasicoherentSubobject_isIso_restrict_of_isAffine
    {Z : Scheme.{u}} [IsAffine Z] (H : Z.Modules) [H.IsQuasicoherent]
    (U : Z.Opens) (hU : IsCompact U.1) [(H.restrict U.ι).IsFiniteType] :
    ∃ K : CategoryTheory.Subobject H, (K : Z.Modules).IsQuasicoherent ∧
      (K : Z.Modules).IsFiniteType ∧
      CategoryTheory.IsIso ((Scheme.Modules.restrictFunctor U.ι).map K.arrow) := by
  have hOIh : IsOpenImmersion Z.isoSpec.hom := IsOpenImmersion.of_isIso _
  have hOIi : IsOpenImmersion Z.isoSpec.inv := IsOpenImmersion.of_isIso _
  have hcont : Continuous Z.isoSpec.hom.base := Z.isoSpec.hom.base.hom.continuous
  have hU'c : IsCompact (Z.isoSpec.hom ''ᵁ U).1 := hU.image hcont
  have hqc' : ((Scheme.Modules.restrictFunctor Z.isoSpec.inv).obj H).IsQuasicoherent :=
    inferInstance
  have hft' : (((Scheme.Modules.restrictFunctor Z.isoSpec.inv).obj H).restrict
      (Z.isoSpec.hom ''ᵁ U).ι).IsFiniteType :=
    isFiniteType_restrict_image_of_iso Z.isoSpec H U inferInstance
  obtain ⟨K', hqc, hft, hiso⟩ :=
    exists_finiteTypeQuasicoherentSubobject_isIso_restrict_of_spec
      ((Scheme.Modules.restrictFunctor Z.isoSpec.inv).obj H) (Z.isoSpec.hom ''ᵁ U) hU'c
  exact transport_along_iso Z.isoSpec H U K' hqc hft hiso

end AlgebraicGeometry
