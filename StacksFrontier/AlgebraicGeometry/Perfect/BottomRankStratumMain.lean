module

public import StacksFrontier.AlgebraicGeometry.Perfect.BottomRankBaseChange
public import StacksFrontier.Topology.Sheaves.Modules.InvertibleAndOperators.Annihilator
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.SheafHomOnSections
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# The bottom rank stratum of a perfect complex

Let `X` be a scheme, `E` a perfect object of `D(𝒪_X)` of Tor amplitude in `[a, b]`, and `r` a
natural number. There is a locally closed subscheme `j : Z ⟶ X` such that

1. `H^a(Lj^* E)` is a finite locally free `𝒪_Z`-module of rank `r`, and
2. a morphism `f : Y ⟶ X` factors through `Z` if and only if `H^a(L(g ∘ f)^* E)` is finite
   locally free of rank `r` for every `g : Y' ⟶ Y`.

Moreover `j` is of finite presentation, and

3. if `f` factors as `Y ⟶ Z ⟶ X` through `g`, then `H^a(Lf^* E) ≅ g^* H^a(Lj^* E)`;
4. if `β_a(x) ≤ r` for every `x ∈ X`, then `j` is a closed immersion, a morphism `f : Y ⟶ X`
   factors through `Z` exactly when `H^a(Lf^* E)` is finite locally free of rank `r`, and for
   `r = 1` exactly when `𝒪_Y ⟶ SheafHom(H^a(Lf^* E), H^a(Lf^* E))` is injective.

This is [stacks 0BDL], `AlgebraicGeometry.BottomRankStratum.exists_isBottomRankStratum`.

The stratum is the one glued from the rank `r` Fitting strata of the dual cokernels of the
bottom differentials of local finite free models of `E`
(`AlgebraicGeometry.BottomRankStratum.exists_mono_factorsThrough_iff`), and the properties of `j`
are local on `X`, where they are those of a Fitting stratum. For the last equivalence, on an
affine piece `Spec T` over a chart whose bottom term is free of rank `β_a(x) ≤ 1`, the module
`H^a(Lf^* E)` is the sheaf associated to the kernel of the base changed bottom differential
`d_T`; the elements of `T` killing that kernel are the sections of the annihilator of
`H^a(Lf^* E)` over `Spec T`, and a linear map out of a free module of rank one has a kernel with
zero annihilator exactly when it vanishes.

## Main results

* `Stacks.SheafOfModules.mono_scalarAction_iff`: the scalar action of `𝒪_X` on the endomorphism
  sheaf of `F` is a monomorphism exactly when the annihilator of `F` has no nonzero sections.
* `LinearMap.forall_smul_ker_eq_zero_iff`: a linear map out of a free module of rank one into a
  projective module has a kernel with zero annihilator exactly when it vanishes.
* `AlgebraicGeometry.BottomRankStratum.exists_isBottomRankStratum`: [stacks 0BDL].

## References

* [The Stacks Project, Lemma 36.31.4 (0BDL)](https://stacks.math.columbia.edu/tag/0BDL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.SheafOfModules

attribute [local implicit_reducible] SheafOfModules.unit PresheafOfModules.unit
  PresheafOfModules.presheaf TopCat.Sheaf structureSheafRing ModuleCat.restrictScalars

attribute [local instance_reducible] CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

variable (X : RingedSpace.{u, u}) (F : _root_.SheafOfModules.{u} (structureSheafRing X))
  (H : SheafHom X.sheaf F F)

/-- The scalar action of the structure sheaf on the endomorphism sheaf of `F` is a monomorphism
exactly when the annihilator of `F` has no nonzero local sections. -/
theorem mono_scalarAction_iff :
    Mono (scalarAction X F H) ↔ ∀ (U : (Opens X.carrier)ᵒᵖ) (r : (structureSheafRing X).obj.obj U),
      r ∈ (annihilatorSheaf X F).toSubmodule.obj U → r = 0 := by
  constructor
  · intro hm U r hr
    have h0 : (annihilatorSheaf X F).ι = 0 :=
      (cancel_mono (scalarAction X F H)).1
        ((annihilatorSheaf_ι_scalarAction X F H).trans zero_comp.symm)
    exact congrArg (fun g => (g.val.app U).hom ⟨r, hr⟩) h0
  · intro h
    refine Preadditive.mono_of_cancel_zero _ fun {A} g hg => ?_
    obtain ⟨l, hl⟩ := KernelFork.IsLimit.lift' (annihilatorSheafIsKernel X F H) g hg
    have hl' : l ≫ (annihilatorSheaf X F).ι = g := hl
    rw [← hl']
    ext U x
    exact h U _ ((l.val.app U).hom x).2

end Stacks.SheafOfModules

namespace AlgebraicGeometry.BottomRankStratum

section Ring

variable {T M N : Type u} [CommRing T] [AddCommGroup M] [Module T M] [AddCommGroup N]
  [Module T N]

/-- A module with a basis of `r` elements is finite locally free of rank `r`. -/
theorem isFiniteLocallyFreeOfRank_of_basis {r : ℕ} (b : Module.Basis (Fin r) T M) :
    Module.IsFiniteLocallyFreeOfRank T M r := by
  refine ⟨PUnit.{u + 1}, fun _ ↦ 1, ?_, fun _ ↦ ⟨?_⟩⟩
  · rw [show Set.range (fun _ : PUnit.{u + 1} ↦ (1 : T)) = {1} from Set.range_const,
      Ideal.span_singleton_one]
  · exact b.ofIsLocalizedModule (Localization.Away (1 : T)) (Submonoid.powers (1 : T))
      (LocalizedModule.mkLinearMap (Submonoid.powers (1 : T)) M)

/-- **A linear map out of a free module of rank one has a kernel with zero annihilator exactly
when it vanishes.** If `L` vanishes its kernel is free of rank one; conversely, for every linear
form `φ` on the projective target, `φ (L e)` kills the kernel, `e` being the basis vector. -/
theorem _root_.LinearMap.forall_smul_ker_eq_zero_iff [Module.Projective T N]
    (b : Module.Basis (Fin 1) T M) (L : M →ₗ[T] N) :
    (∀ t : T, (∀ m ∈ LinearMap.ker L, t • m = 0) → t = 0) ↔ L = 0 := by
  have hm : ∀ m : M, b.repr m 0 • b 0 = m := fun m => by
    conv_rhs => rw [← b.sum_repr m]
    simp
  constructor
  · intro h
    have hL : L (b 0) = 0 := by
      refine (Module.forall_dual_apply_eq_zero_iff T (L (b 0))).1 fun φ => h _ fun m hm' => ?_
      have h0 : φ (L m) = 0 := by rw [LinearMap.mem_ker.1 hm', map_zero]
      rw [← hm m, map_smul, map_smul, smul_eq_mul] at h0
      rw [← hm m, smul_smul, mul_comm, h0, zero_smul]
    exact b.ext fun i => by rw [Subsingleton.elim i 0, hL, LinearMap.zero_apply]
  · rintro rfl t ht
    simpa using congrArg (fun m => b.repr m 0) (ht (b 0) (by simp))

/-- **A linear map out of a free module of rank at most one over a nonzero ring whose kernel has
zero annihilator has a kernel free of rank one.** -/
theorem _root_.LinearMap.isFiniteLocallyFreeOfRank_ker_of_forall_smul_eq_zero [Nontrivial T]
    [Module.Projective T N] {n : ℕ} (hn : n ≤ 1) (b : Module.Basis (Fin n) T M) (L : M →ₗ[T] N)
    (h : ∀ t : T, (∀ m ∈ LinearMap.ker L, t • m = 0) → t = 0) :
    Module.IsFiniteLocallyFreeOfRank T (LinearMap.ker L) 1 := by
  obtain rfl | rfl : n = 0 ∨ n = 1 := by omega
  · exact absurd (h 1 fun m _ => b.ext_elem fun i => i.elim0) one_ne_zero
  · have hL := (LinearMap.forall_smul_ker_eq_zero_iff b L).1 h
    exact isFiniteLocallyFreeOfRank_of_basis
      (b.map (LinearEquiv.ofTop _ (by rw [hL, LinearMap.ker_zero])).symm)

end Ring

section Annihilator

variable {Y : Scheme.{u}}

/-- Membership in the annihilator of an `𝒪_Y`-module, in terms of sections over smaller opens. -/
theorem mem_annihilatorSheaf_iff (F : Y.Modules) (U : Y.Opens) (r : Γ(Y, U)) :
    r ∈ (Stacks.SheafOfModules.annihilatorSheaf Y.toRingedSpace F).toSubmodule.obj (op U) ↔
      ∀ (V : Y.Opens) (hVU : V ≤ U) (m : Γ(F, V)), Y.presheaf.map (homOfLE hVU).op r • m = 0 :=
  ⟨fun h V hVU m => h (op V) (homOfLE hVU).op m, fun h V f m => h V.unop f.unop.le m⟩

/-- A section of the structure sheaf vanishing on a neighbourhood of every point vanishes. -/
theorem eq_zero_of_forall_exists_map_eq_zero (U : Y.Opens) (r : Γ(Y, U))
    (h : ∀ y ∈ U, ∃ (V : Y.Opens) (hVU : V ≤ U), y ∈ V ∧ Y.presheaf.map (homOfLE hVU).op r = 0) :
    r = 0 := by
  refine TopCat.Presheaf.section_ext Y.sheaf U r 0 fun y hy => ?_
  obtain ⟨V, hVU, hyV, hV⟩ := h y hy
  change Y.presheaf.germ U y hy r = Y.presheaf.germ U y hy 0
  rw [← Y.presheaf.germ_res_apply (homOfLE hVU) y hyV, hV, map_zero, map_zero]

/-- An element of `R` killing an `R`-module `M` kills every section of `M~`. -/
theorem tilde_smul_eq_zero {R : CommRingCat.{u}} (M : ModuleCat.{u} R) (t : R)
    (ht : ∀ m : M, t • m = 0) (U : (Spec R).Opens) (x : Γ(tilde M, U)) : t • x = 0 := by
  apply Subtype.ext
  funext p
  change (algebraMap R (Localization.AtPrime p.val.asIdeal) t) • x.val p = 0
  rw [algebraMap_smul]
  induction x.val p using LocalizedModule.induction_on with
  | h m s => simp [LocalizedModule.smul'_mk, ht]

variable {T : CommRingCat.{u}} (w : Spec T ⟶ Y) [IsOpenImmersion w] {F : Y.Modules}
  {M : ModuleCat.{u} T}

/-- An element of `T` killing `M` gives a section of the annihilator of `F` over the image of
`Spec T`, when `F` restricts to `M~` on `Spec T`. -/
theorem mem_annihilatorSheaf_of_smul_eq_zero (e : F.restrict w ≅ tilde M) (t : T)
    (ht : ∀ m : M, t • m = 0) :
    (w.appIso ⊤).inv ((Scheme.ΓSpecIso T).inv t) ∈
      (Stacks.SheafOfModules.annihilatorSheaf Y.toRingedSpace F).toSubmodule.obj
        (op (w ''ᵁ ⊤)) := by
  rw [mem_annihilatorSheaf_iff]
  intro V hV m
  obtain ⟨V', rfl⟩ : ∃ V', w ''ᵁ V' = V := ⟨w ⁻¹ᵁ V, by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right]
    exact hV.trans (w.image_le_opensRange ⊤)⟩
  have h1 := ConcreteCategory.congr_hom
    (show (w.appIso ⊤).inv ≫ Y.presheaf.map (homOfLE hV).op =
        (Spec T).presheaf.map (homOfLE le_top).op ≫ (w.appIso V').inv from
      (Scheme.Hom.appIso_inv_naturality w (homOfLE le_top).op).symm)
    ((Scheme.ΓSpecIso T).inv t)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h1
  rw [h1, ← Iso.inv_hom_id_apply (F.restrictAppIso w V') m,
    ← Scheme.Modules.smul_restrictAppIso_hom_apply]
  suffices hs : (Spec T).presheaf.map (homOfLE le_top).op ((Scheme.ΓSpecIso T).inv t) •
      (F.restrictAppIso w V').inv m = 0 by
    rw [hs, map_zero]
  apply (ConcreteCategory.bijective_of_isIso (e.hom.app V')).1
  rw [map_zero, Scheme.Modules.Hom.app_smul]
  exact tilde_smul_eq_zero M t ht V' _

/-- A section of the annihilator of `F` over the image of `Spec T` kills `M`, when `F` restricts
to `M~` on `Spec T`. -/
theorem smul_eq_zero_of_mem_annihilatorSheaf (e : F.restrict w ≅ tilde M) (r : Γ(Y, w ''ᵁ ⊤))
    (hr : r ∈ (Stacks.SheafOfModules.annihilatorSheaf Y.toRingedSpace F).toSubmodule.obj
      (op (w ''ᵁ ⊤))) (m : M) :
    (Scheme.ΓSpecIso T).hom ((w.appIso ⊤).hom r) • m = 0 := by
  have hrt : r = (w.appIso ⊤).inv ((Spec T).presheaf.map (homOfLE le_top).op
      ((Scheme.ΓSpecIso T).inv ((Scheme.ΓSpecIso T).hom ((w.appIso ⊤).hom r)))) := by
    simp
  let m' : Γ(F.restrict w, ⊤) := e.inv.app ⊤ (tilde.toOpen M ⊤ m)
  have hx := (mem_annihilatorSheaf_iff F _ r).1 hr (w ''ᵁ ⊤) le_rfl
    ((F.restrictAppIso w ⊤).hom m')
  simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply] at hx
  rw [hrt, ← Scheme.Modules.smul_restrictAppIso_hom_apply] at hx
  have hx' := congrArg (e.hom.app ⊤)
    ((ConcreteCategory.bijective_of_isIso (F.restrictAppIso w ⊤).hom).1
      (hx.trans (map_zero _).symm))
  have hem : e.hom.app ⊤ m' = tilde.toOpen M ⊤ m := by
    change (e.inv.app ⊤ ≫ e.hom.app ⊤) _ = _
    rw [← Scheme.Modules.Hom.comp_app, e.inv_hom_id]
    rfl
  rw [Scheme.Modules.Hom.app_smul, map_zero, hem] at hx'
  apply (ConcreteCategory.bijective_of_isIso (tilde.toOpen M ⊤)).1
  rwa [map_zero, map_smul]

end Annihilator

section Pieces

variable {X : Scheme.{u}} {E : DerivedCategory X.Modules} {a : ℤ}

/-- **Affine pieces over a chart.** Around a point of an open `U` whose image lies in a chart,
there is an affine open inside `U` on which the morphism factors through the chart. -/
theorem exists_affine_piece {Y : Scheme.{u}} (f : Y ⟶ X) (c : Chart E a) (U : Y.Opens) (y : Y)
    (hyU : y ∈ U) (hy : f.base y ∈ Set.range c.ι.base) :
    ∃ (T : CommRingCat.{u}) (w : Spec T ⟶ Y) (_ : IsOpenImmersion w) (ψ : c.R ⟶ T),
      y ∈ Set.range w.base ∧ w ''ᵁ ⊤ ≤ U ∧ w ≫ f = Spec.map ψ ≫ c.ι := by
  have hz : (⟨y, hyU⟩ : U.toScheme) ∈ Set.range (pullback.fst (U.ι ≫ f) c.ι).base := by
    rwa [IsOpenImmersion.range_pullbackFst]
  obtain ⟨z, hz⟩ := hz
  obtain ⟨V, hzV⟩ := TopologicalSpace.Opens.mem_iSup.mp
    ((iSup_affineOpens_eq_top (pullback (U.ι ≫ f) c.ι)).ge (Set.mem_univ z))
  have : IsOpenImmersion V.2.fromSpec := V.2.isOpenImmersion_fromSpec
  obtain ⟨p, hp⟩ : z ∈ Set.range V.2.fromSpec.base := by
    rwa [V.2.range_fromSpec]
  refine ⟨Γ(pullback (U.ι ≫ f) c.ι, V.1), V.2.fromSpec ≫ pullback.fst _ _ ≫ U.ι, inferInstance,
    Spec.preimage (V.2.fromSpec ≫ pullback.snd _ _), ⟨p, ?_⟩, ?_, ?_⟩
  · simp only [Scheme.Hom.comp_apply, hp, hz]
    rfl
  · simp only [Scheme.Hom.comp_image]
    exact U.ι_image_le _
  · rw [Spec.map_preimage, Category.assoc, Category.assoc, pullback.condition, Category.assoc]

/-- On an affine piece over a chart, the bottom cohomology of the derived pullback restricts to the
sheaf associated to the kernel of the base changed bottom differential. -/
def chartPieceIso {Y : Scheme.{u}} (f : Y ⟶ X) (c : Chart E a) {T : CommRingCat.{u}}
    (w : Spec T ⟶ Y) [IsOpenImmersion w] (ψ : c.R ⟶ T) (h : w ≫ f = Spec.map ψ ≫ c.ι) :
    (pullbackHomology E a f).restrict w ≅ tilde (c.kernel ψ) :=
  (pullbackHomologyRestrictIso E a w f).symm ≪≫ eqToIso (by rw [h]) ≪≫ c.pullbackHomologyIso ψ

end Pieces

section Main

variable {X : Scheme.{u}}

/-- When `β_a ≤ 1` everywhere and `H^a(Lf^* E)` is finite locally free of rank one, the scalar
action `𝒪_Y ⟶ SheafHom(H^a(Lf^* E), H^a(Lf^* E))` is a monomorphism. -/
theorem mono_scalarAction_of_isFiniteLocallyFreeOfRank_one {E : DerivedCategory X.Modules}
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E) {a : ℤ} (b : ℤ)
    (htor : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X.toRingedSpace E a b)
    (hβ : ∀ x : X, DerivedFibreBetti.derivedFiberBetti X E
      (Scheme.Modules.isPseudoCoherent_of_isPerfect E hE) a x ≤ 1)
    {Y : Scheme.{u}} (f : Y ⟶ X)
    (hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (pullbackHomology E a f) 1) :
    Mono (Stacks.SheafOfModules.scalarAction Y.toRingedSpace (pullbackHomology E a f)
      (Stacks.Cohomology.SheafHomComplex.sheafHom Y.sheaf _ _)) := by
  refine (Stacks.SheafOfModules.mono_scalarAction_iff _ _ _).2 fun U s hs => ?_
  let U' : Y.Opens := U.unop
  have hf : IsUniversallyFreeBottom E a 1 f :=
    isUniversallyFreeBottom_of_isFiniteLocallyFreeOfRank 1 hE b htor hβ f hF
  refine eq_zero_of_forall_exists_map_eq_zero U' s fun y hy => ?_
  obtain ⟨T, w, hw, c, ψ, hyw, hwf, hd, ⟨eM⟩⟩ :=
    exists_piece hE b htor (U'.ι ≫ f) (hf.comp _) ⟨y, hy⟩
  let w' := w ≫ U'.ι
  have hle : w' ''ᵁ ⊤ ≤ U' := by
    simpa only [w', Scheme.Hom.comp_image] using U'.ι_image_le _
  refine ⟨w' ''ᵁ ⊤, hle, ?_, ?_⟩
  · obtain ⟨q, hq⟩ := hyw
    refine ⟨q, trivial, ?_⟩
    change U'.ι.base (w.base q) = y
    rw [hq]
    rfl
  have hmem : Y.presheaf.map (homOfLE hle).op s ∈
      (Stacks.SheafOfModules.annihilatorSheaf Y.toRingedSpace
        (pullbackHomology E a f)).toSubmodule.obj (op (w' ''ᵁ ⊤)) := by
    rw [mem_annihilatorSheaf_iff]
    intro V hV m
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    exact (mem_annihilatorSheaf_iff _ U' s).1 hs V (hV.trans hle) m
  have hw'f : w' ≫ f = Spec.map ψ ≫ c.ι := by
    simpa only [w', Category.assoc] using hwf
  have ht := smul_eq_zero_of_mem_annihilatorSheaf w' (chartPieceIso f c w' ψ hw'f) _ hmem
  let := ψ.hom.toAlgebra
  have ht0 := (LinearMap.forall_smul_ker_eq_zero_iff
    ((Module.Basis.ofEquivFun eM).baseChange T) (c.d.hom.baseChange T)).2
    (congrArg ModuleCat.Hom.hom hd) _ fun m hm => congrArg Subtype.val (ht ⟨m, hm⟩)
  rw [← Iso.hom_inv_id_apply (w'.appIso ⊤) (Y.presheaf.map (homOfLE hle).op s),
    ← Iso.hom_inv_id_apply (Scheme.ΓSpecIso T) ((w'.appIso ⊤).hom _), ht0, map_zero, map_zero]

/-- When `β_a ≤ 1` everywhere and the scalar action
`𝒪_Y ⟶ SheafHom(H^a(Lf^* E), H^a(Lf^* E))` is a monomorphism, `H^a(Lf^* E)` is finite locally
free of rank one. -/
theorem isFiniteLocallyFreeOfRank_one_of_mono_scalarAction {E : DerivedCategory X.Modules}
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E) {a : ℤ} (b : ℤ)
    (htor : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X.toRingedSpace E a b)
    (hβ : ∀ x : X, DerivedFibreBetti.derivedFiberBetti X E
      (Scheme.Modules.isPseudoCoherent_of_isPerfect E hE) a x ≤ 1)
    {Y : Scheme.{u}} (f : Y ⟶ X)
    (hm : Mono (Stacks.SheafOfModules.scalarAction Y.toRingedSpace (pullbackHomology E a f)
      (Stacks.Cohomology.SheafHomComplex.sheafHom Y.sheaf _ _))) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (pullbackHomology E a f) 1 := by
  have hann := (Stacks.SheafOfModules.mono_scalarAction_iff _ _ _).1 hm
  rw [← Scheme.Modules.isFiniteLocallyFreeOfRank_iff]
  refine isFiniteLocallyFreeOfRank_of_forall_exists_openImmersion _ 1 fun y => ?_
  let c := chartAt hE b htor (f.base y)
  obtain ⟨T, w, hw, ψ, hyw, -, hwf⟩ :=
    exists_affine_piece f c ⊤ y trivial (mem_range_chartAt hE b htor _)
  refine ⟨Spec T, w, hw, hyw, ?_⟩
  obtain ⟨p, -⟩ := hyw
  have : Nontrivial T := PrimeSpectrum.nontrivial p
  obtain ⟨eM⟩ := nonempty_chartAt_X_equiv hE b htor (f.base y) a
  let := ψ.hom.toAlgebra
  have hFLF : Module.IsFiniteLocallyFreeOfRank T (LinearMap.ker (c.d.hom.baseChange T)) 1 := by
    refine LinearMap.isFiniteLocallyFreeOfRank_ker_of_forall_smul_eq_zero (hβ _)
      ((Module.Basis.ofEquivFun eM).baseChange T) _ fun t ht => ?_
    have h0 := hann _ _ (mem_annihilatorSheaf_of_smul_eq_zero w (chartPieceIso f c w ψ hwf) t
      fun m => Subtype.ext (ht m.1 m.2))
    exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso T).inv).1
      (((ConcreteCategory.bijective_of_isIso (w.appIso ⊤).inv).1
        (h0.trans (map_zero _).symm)).trans (map_zero _).symm)
  exact ((c.isFiniteLocallyFreeOfRank_pullbackHomology_iff ψ 1).2 hFLF).of_iso
    (eqToIso (by rw [hwf]) ≪≫ pullbackHomologyRestrictIso E a w f)

/-- **The bottom rank stratum of a perfect complex.** Let `E` be perfect of Tor amplitude in
`[a, b]` and `r` a natural number. There is a locally closed immersion `j : Z ⟶ X` with
`H^a(Lj^* E)` finite locally free of rank `r`, through which a morphism `f : Y ⟶ X` factors
exactly when `H^a(L(g ∘ f)^* E)` is finite locally free of rank `r` for every `g : Y' ⟶ Y`
(`IsBottomRankStratum`). The morphism `j` is of finite presentation, and
`H^a(L(g ∘ j)^* E) ≅ g^* H^a(Lj^* E)` for every `g : Y ⟶ Z`. If `β_a ≤ r` everywhere, then `j` is
a closed immersion, a morphism `f` factors through `Z` exactly when `H^a(Lf^* E)` is finite
locally free of rank `r`, and, when `r = 1`, exactly when the scalar action
`𝒪_Y ⟶ SheafHom(H^a(Lf^* E), H^a(Lf^* E))` is a monomorphism. -/
@[stacks 0BDL]
theorem exists_isBottomRankStratum (E : DerivedCategory X.Modules)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E) (a b : ℤ)
    (htor : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X.toRingedSpace E a b) (r : ℕ) :
    ∃ (Z : Scheme.{u}) (j : Z ⟶ X), IsBottomRankStratum E a r j ∧ FinitePresentation j ∧
      (∀ (Y : Scheme.{u}) (g : Y ⟶ Z), Nonempty (pullbackHomology E a (g ≫ j) ≅
        (Scheme.Modules.pullback g).obj (pullbackHomology E a j))) ∧
      ((∀ x : X, DerivedFibreBetti.derivedFiberBetti X E
          (Scheme.Modules.isPseudoCoherent_of_isPerfect E hE) a x ≤ r) →
        IsClosedImmersion j ∧
        (∀ (Y : Scheme.{u}) (f : Y ⟶ X), (∃ g : Y ⟶ Z, g ≫ j = f) ↔
          SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (pullbackHomology E a f) r) ∧
        (r = 1 → ∀ (Y : Scheme.{u}) (f : Y ⟶ X), (∃ g : Y ⟶ Z, g ≫ j = f) ↔
          Mono (Stacks.SheafOfModules.scalarAction Y.toRingedSpace (pullbackHomology E a f)
            (Stacks.Cohomology.SheafHomComplex.sheafHom Y.sheaf _ _)))) := by
  obtain ⟨Z, j, hmono, hj⟩ := exists_mono_factorsThrough_iff (E := E) (a := a) r hE b htor
  have hjF : IsUniversallyFreeBottom E a r j := (hj Z j).1 ⟨𝟙 _, Category.id_comp _⟩
  have hprop := fun (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
      (h : ∀ x : X, P ((chartAt hE b htor x).stratum r).hom) =>
    prop_of_forall_chartAt r hE b htor P j hj h
  have hLFP : IsZariskiLocalAtTarget @LocallyOfFinitePresentation.{u} :=
    @HasRingHomProperty.instIsZariskiLocalAtTarget @LocallyOfFinitePresentation _
      instHasRingHomPropertyLocallyOfFinitePresentationFinitePresentation
  have hQC : IsZariskiLocalAtTarget @QuasiCompact.{u} :=
    @HasAffineProperty.instIsZariskiLocalAtTarget @QuasiCompact _
      instHasAffinePropertyQuasiCompactCompactSpaceCarrierCarrierCommRingCat
  have hQS : IsZariskiLocalAtTarget @QuasiSeparated.{u} :=
    @HasAffineProperty.instIsZariskiLocalAtTarget @QuasiSeparated _
      instHasAffinePropertyQuasiSeparatedQuasiSeparatedSpaceCarrierCarrierCommRingCat
  refine ⟨Z, j, ⟨hprop @IsImmersion fun x => isImmersion_fittingRankStratum _ r, hjF.self, hj⟩,
    ⟨@hprop @LocallyOfFinitePresentation hLFP fun x =>
        (finitePresentation_fittingRankStratum _ r).1,
      @hprop @QuasiCompact hQC fun x => (finitePresentation_fittingRankStratum _ r).2.1,
      @hprop @QuasiSeparated hQS fun x => (finitePresentation_fittingRankStratum _ r).2.2⟩,
    fun Y g => nonempty_pullbackHomology_comp_iso_of_isUniversallyFreeBottom hE b htor j hjF g,
    fun hβ => ?_⟩
  have hab : ∀ (Y : Scheme.{u}) (f : Y ⟶ X), (∃ g : Y ⟶ Z, g ≫ j = f) ↔
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (pullbackHomology E a f) r := by
    intro Y f
    rw [hj]
    exact ⟨IsUniversallyFreeBottom.self,
      isUniversallyFreeBottom_of_isFiniteLocallyFreeOfRank r hE b htor hβ f⟩
  refine ⟨hprop @IsClosedImmersion fun x =>
      isClosedImmersion_fittingRankStratum_of_isGeneratedByNear _ r fun y =>
        ((chartAt hE b htor x).isGeneratedByNear_dualCoker_iff _ r y).2 (hβ _), hab, ?_⟩
  rintro rfl Y f
  rw [hab]
  exact ⟨mono_scalarAction_of_isFiniteLocallyFreeOfRank_one hE b htor hβ f,
    isFiniteLocallyFreeOfRank_one_of_mono_scalarAction hE b htor hβ f⟩

end Main

end AlgebraicGeometry.BottomRankStratum

end
