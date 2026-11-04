module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RelationsKernel
public import StacksFrontier.AlgebraicGeometry.AmpleWire.UnitStalk
public import StacksFrontier.AlgebraicGeometry.Divisors.CanonicalSectionNonvanishing
public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorInvertibleSheaf
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.Basic
public import StacksFrontier.AlgebraicGeometry.PicardBaseChange.PuncturedSpectrumCompletion
public import StacksFrontier.AlgebraicGeometry.Properties.NormalDepthTwo
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.DominatingBlowup
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.OfModification

/-!
# Maps from the structure sheaf to the sheaf of an exceptional divisor

Let `A` be a Noetherian normal local domain of dimension two, `f : X ⟶ Spec(A)` a modification
and `E` an effective Cartier divisor on `X` whose support lies over the closed point. This file
proves the step of the proof of [Stacks, Tag 0EA2] which identifies the maps `𝒪_X ⟶ 𝒪_X(E)`:

* `AlgebraicGeometry.DualizingDivisor.exists_eq_smul_canonicalHom`: every `𝒪_X`-linear map
  `𝒪_X ⟶ 𝒪_X(E)` is `a • s_E` for some `a ∈ A`, where `s_E` is the canonical map
  (`canonicalHom`, the map corresponding to the canonical section `1_E`) and `A` acts through
  `A ⟶ Γ(X, 𝒪_X)` (`modulesLinear`);
* `AlgebraicGeometry.DualizingDivisor.eq_zero_of_smul_canonicalHom_eq_zero`: `a • s_E = 0`
  forces `a = 0`.

The argument is the Hartogs-type one of the source: over `V = f⁻¹(U)`, `U` the punctured
spectrum, `E` is empty and `Γ(V, 𝒪_X) = Γ(U, 𝒪) = A` (`f` is an isomorphism over `U` and `A` has
depth two); so over `V` a map `𝒪_X ⟶ 𝒪_X(E)` is a multiple `a • s_E`, and two sections of
`𝒪_X(E) = SheafHom(ℐ_E, 𝒪_X)` agreeing over the dense open `V` of the integral scheme `X` agree,
since their values on sections of `ℐ_E` are functions on `X`.

## References

* [Stacks Project, Tag 0EA2](https://stacks.math.columbia.edu/tag/0EA2)
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite IsLocalRing

universe u

namespace AlgebraicGeometry.DualizingDivisor

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsNormalDomain A]

/-- **`Γ(f⁻¹(U), 𝒪_X) = A`** for a modification `f : X ⟶ Spec(A)` of a two-dimensional
Noetherian normal local domain, `U` the punctured spectrum: `f` is an isomorphism over `U`, and
`Γ(U, 𝒪) = A` because `A` has depth two. -/
theorem bijective_baseRingToSections_preimage_puncturedSpectrum (hdim : ringKrullDim A = 2)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) (hf : IsModification f) :
    Function.Bijective
      (baseRingToSections A (Over.mk f) (op (f ⁻¹ᵁ Stacks.puncturedSpectrum A))) := by
  have : IsIso (f ∣_ Stacks.puncturedSpectrum A) :=
    (VanishingSituation.ofModification A hdim f hf).isIso_morphismRestrict_puncturedSpectrumOpen
  have hdepth : (2 : ℕ∞) ≤ Module.depth A (maximalIdeal A) A :=
    Stacks.NormalDepth.two_le_depth_of_isIntegrallyClosed A (by rw [hdim])
  have := Stacks.AlgebraicGeometry.PicardBaseChange.isIso_puncturedSpectrum_ι_appTop A hdepth
  have hiso : IsIso (f.appTop ≫ X.presheaf.map
      (homOfLE (le_top : f ⁻¹ᵁ Stacks.puncturedSpectrum A ≤ ⊤)).op) := by
    have h : f.appTop ≫ (f ⁻¹ᵁ Stacks.puncturedSpectrum A).ι.appTop =
        (Stacks.puncturedSpectrum A).ι.appTop ≫ (f ∣_ Stacks.puncturedSpectrum A).appTop := by
      rw [← Scheme.Hom.comp_appTop, ← morphismRestrict_ι, Scheme.Hom.comp_appTop]
    have : IsIso (f.appTop ≫ (f ⁻¹ᵁ Stacks.puncturedSpectrum A).ι.appTop) := by
      rw [h]
      exact IsIso.comp_isIso' inferInstance
        (inferInstanceAs (IsIso (Scheme.Γ.map (f ∣_ Stacks.puncturedSpectrum A).op)))
    have e : f.appTop ≫ X.presheaf.map
        (homOfLE (le_top : f ⁻¹ᵁ Stacks.puncturedSpectrum A ≤ ⊤)).op =
        (f.appTop ≫ X.presheaf.map (homOfLE (x := (f ⁻¹ᵁ Stacks.puncturedSpectrum A).ι ''ᵁ ⊤)
          le_top).op) ≫ X.presheaf.map
            (eqToHom (f ⁻¹ᵁ Stacks.puncturedSpectrum A).ι_image_top.symm).op := by
      rw [Category.assoc, ← Functor.map_comp]
      rfl
    rw [e]
    exact IsIso.comp_isIso' this inferInstance
  exact ConcreteCategory.bijective_of_isIso
    ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop ≫ X.presheaf.map
      (homOfLE (le_top : f ⁻¹ᵁ Stacks.puncturedSpectrum A ≤ ⊤)).op)

/-- The ring of sections over the empty open is zero. -/
theorem subsingleton_presheaf_obj_of_eq_bot {Y : Scheme.{u}} (W : Y.Opens) (hW : W = ⊥) :
    Subsingleton Γ(Y, W) := by
  subst hW
  exact CommRingCat.subsingleton_of_isTerminal Y.sheaf.isTerminalOfEmpty

/-- Over an open missing the support of `E`, the ideal `ℐ_E` contains `1`. -/
theorem exists_idealInclusion_eq_unitSection {X : Scheme.{u}} (E : X.IdealSheafData)
    (W : X.Opens) (hW : ∀ x ∈ W, x ∉ E.support) :
    ∃ b, ((Stacks.Divisors.idealInclusion E).val.app (op W)).hom b =
      Stacks.SheafOfModules.unitSection X.toRingedSpace W := by
  rw [Stacks.Divisors.exists_idealInclusion_eq_unitSection_iff]
  have h : E.subschemeι ⁻¹ᵁ W = ⊥ := by
    ext y
    simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
    intro hy
    have hmem := Set.mem_range_self (f := E.subschemeι) y
    rw [E.range_subschemeι] at hmem
    exact hW _ hy hmem
  have := subsingleton_presheaf_obj_of_eq_bot _ h
  exact Subsingleton.elim _ _

section DivisorSections

open Stacks.SheafOfModules Stacks.Divisors

variable {X : Scheme.{u}} (E : X.IdealSheafData)

/-- The value of a global section of `𝒪_X(E) = SheafHom(ℐ_E, 𝒪_X)` on a section of `ℐ_E`
commutes with restriction. -/
theorem dualEval_sections_restrict (σ : (invertibleSheaf' E).sections)
    {W₁ W₂ : X.Opens} (h : W₂ ≤ W₁) (y : (negativeTwist' E).val.obj (op W₁)) :
    X.presheaf.map (homOfLE h).op (dualEval (L := negativeTwist' E) (σ.val (op W₁)) y) =
      dualEval (L := negativeTwist' E) (σ.val (op W₂))
        (((negativeTwist' E).val.map (homOfLE h).op).hom y) := by
  have key := dualApp_resSection (L := negativeTwist' E) (σ.val (op W₁))
    (op (Over.mk (homOfLE h))) y
  change dualEval (L := negativeTwist' E)
    (((invertibleSheaf' E).val.map (homOfLE h).op).hom (σ.val (op W₁))) _ = _ at key
  rw [PresheafOfModules.sections_property] at key
  exact key.symm

omit [IsNoetherianRing A] in
/-- The preimage of the punctured spectrum under a modification is nonempty: it contains every
point over the generic point. -/
theorem nonempty_preimage_puncturedSpectrum (hdim : ringKrullDim A = 2) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) (hf : IsModification f) :
    Nonempty (f ⁻¹ᵁ Stacks.puncturedSpectrum A) := by
  have := hf.isProper
  have : IsDominant f := IsBirational.isDominant hf.isBirational
  have hbot : (⊥ : Ideal A) ≠ maximalIdeal A := by
    intro h
    have hfield : IsField A := (IsLocalRing.isField_iff_maximalIdeal_eq).2 h.symm
    rw [ringKrullDim_eq_zero_of_isField hfield] at hdim
    exact absurd hdim (by decide)
  obtain ⟨x, hx⟩ := (inferInstance : Surjective f).surj ⟨⊥, Ideal.isPrime_bot⟩
  refine ⟨⟨x, ?_⟩⟩
  show f x ≠ closedPoint A
  rw [hx]
  exact fun h => hbot (congrArg PrimeSpectrum.asIdeal h)

/-- **Every global section of `𝒪_X(E)` is a base multiple of the canonical one**, read on the
sections of `ℐ_E`: there is `a ∈ A` such that the section sends `y ∈ ℐ_E(W)` to `a · y` for every
open `W`. -/
theorem sections_eq_smul_idealInclusion (hdim : ringKrullDim A = 2) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) (hf : IsModification f) (E : X.IdealSheafData)
    (hE : ∀ x : X, x ∈ E.support → f x = closedPoint A) (σ : (invertibleSheaf' E).sections) :
    ∃ a : A, ∀ (W : X.Opens) (y : (negativeTwist' E).val.obj (op W)),
      dualEval (L := negativeTwist' E) (σ.val (op W)) y =
        @HMul.hMul Γ(X, W) Γ(X, W) Γ(X, W) instHMul (baseRingToSections A (Over.mk f) (op W) a)
          (((idealInclusion E).val.app (op W)).hom y) := by
  have : IsIntegral X := hf.source_isIntegral
  set V := f ⁻¹ᵁ Stacks.puncturedSpectrum A
  have hVE : ∀ x ∈ V, x ∉ E.support := fun x hx hxE => hx (hE x hxE)
  obtain ⟨y₁, hy₁⟩ := exists_idealInclusion_eq_unitSection E V hVE
  obtain ⟨a, ha⟩ := (bijective_baseRingToSections_preimage_puncturedSpectrum hdim f hf).2
    (dualEval (L := negativeTwist' E) (σ.val (op V)) y₁)
  refine ⟨a, ?_⟩
  -- restriction of base scalars
  have hres : ∀ {W₁ W₂ : X.Opens} (h : W₂ ≤ W₁),
      X.presheaf.map (homOfLE h).op (baseRingToSections A (Over.mk f) (op W₁) a) =
        baseRingToSections A (Over.mk f) (op W₂) a := by
    intro W₁ W₂ h
    show (X.presheaf.map (homOfLE le_top).op ≫ X.presheaf.map (homOfLE h).op) _ = _
    rw [← Functor.map_comp]
    rfl
  -- restriction of the ideal inclusion
  have hι : ∀ {W₁ W₂ : X.Opens} (h : W₂ ≤ W₁) (y : (negativeTwist' E).val.obj (op W₁)),
      X.presheaf.map (homOfLE h).op (((idealInclusion E).val.app (op W₁)).hom y) =
        ((idealInclusion E).val.app (op W₂)).hom
          (((negativeTwist' E).val.map (homOfLE h).op).hom y) := by
    intro W₁ W₂ h y
    exact (PresheafOfModules.naturality_apply (idealInclusion E).val (homOfLE h).op y).symm
  -- inside `V`
  have hV : ∀ (W : X.Opens) (hW : W ≤ V) (y : (negativeTwist' E).val.obj (op W)),
      dualEval (L := negativeTwist' E) (σ.val (op W)) y =
        @HMul.hMul Γ(X, W) Γ(X, W) Γ(X, W) instHMul (baseRingToSections A (Over.mk f) (op W) a)
          (((idealInclusion E).val.app (op W)).hom y) := by
    intro W hW y
    let y₁' : (negativeTwist' E).val.obj (op W) :=
      ((negativeTwist' E).val.map (homOfLE hW).op).hom y₁
    let c : (structureSheafRing X.toRingedSpace).obj.obj (op W) :=
      ((idealInclusion E).val.app (op W)).hom y
    have hy : y = c • y₁' := by
      apply Stacks.SheafOfModules.injective_app_kernel_ι
      refine Eq.trans ?_ (((idealInclusion E).val.app (op W)).hom.map_smul c y₁').symm
      show _ = c • ((idealInclusion E).val.app (op W)).hom y₁'
      rw [← hι hW y₁, hy₁]
      show _ = @HMul.hMul Γ(X, W) Γ(X, W) Γ(X, W) instHMul c (X.presheaf.map (homOfLE hW).op 1)
      rw [map_one, mul_one]
    conv_lhs => rw [hy]
    refine (dualApp_smul (L := negativeTwist' E) (σ.val (op W)) (op (Over.mk (𝟙 W))) c y₁').trans ?_
    show @HMul.hMul Γ(X, W) Γ(X, W) Γ(X, W) instHMul c
      (dualEval (L := negativeTwist' E) (σ.val (op W)) y₁') = _
    rw [← dualEval_sections_restrict E σ hW y₁, ← ha, hres]
    exact mul_comm (G := Γ(X, W)) _ _
  intro W y
  by_cases hne : Nonempty (W ⊓ V : X.Opens)
  · apply map_injective_of_isIntegral X (homOfLE (inf_le_left : W ⊓ V ≤ W))
    refine (dualEval_sections_restrict E σ inf_le_left y).trans
      ((hV _ inf_le_right _).trans ?_)
    refine Eq.trans ?_
      ((X.presheaf.map (homOfLE (inf_le_left : W ⊓ V ≤ W)).op).hom.map_mul _ _).symm
    exact congrArg₂ (@HMul.hMul Γ(X, W ⊓ V) Γ(X, W ⊓ V) Γ(X, W ⊓ V) instHMul)
      (hres inf_le_left).symm (hι inf_le_left y).symm
  · have hW : W = ⊥ := by
      ext x
      simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      intro hx
      obtain ⟨v⟩ := nonempty_preimage_puncturedSpectrum hdim f hf
      obtain ⟨z, hz⟩ := nonempty_preirreducible_inter W.isOpen V.isOpen ⟨x, hx⟩ ⟨v.1, v.2⟩
      exact hne ⟨⟨z, hz⟩⟩
    have := subsingleton_presheaf_obj_of_eq_bot W hW
    exact Subsingleton.elim (α := Γ(X, W)) _ _

/-- A component of a section of `𝒪_X(E)` is the value of its restriction. -/
theorem dualApp_eq_dualEval {X : Scheme.{u}} (E : X.IdealSheafData) {W : X.Opens}
    (lam : (invertibleSheaf' E).val.obj (op W))
    (V' : (Over W)ᵒᵖ) (g : (negativeTwist' E).val.obj (op V'.unop.left)) :
    dualApp lam V' g = dualEval (((invertibleSheaf' E).val.map V'.unop.hom.op).hom lam) g := rfl

/-- Two global sections of `𝒪_X(E)` with the same values on all sections of `ℐ_E` agree. -/
theorem sections_ext {X : Scheme.{u}} (E : X.IdealSheafData)
    {σ τ : (invertibleSheaf' E).sections}
    (h : ∀ (W : X.Opens) (y : (negativeTwist' E).val.obj (op W)),
      dualEval (L := negativeTwist' E) (σ.val (op W)) y =
        dualEval (L := negativeTwist' E) (τ.val (op W)) y) : σ = τ := by
  apply Subtype.ext
  funext W
  refine PresheafOfModules.hom_ext fun V' => ModuleCat.hom_ext (LinearMap.ext fun y => ?_)
  show dualApp (L := negativeTwist' E) (σ.val (op W.unop)) V' y =
    dualApp (L := negativeTwist' E) (τ.val (op W.unop)) V' y
  refine (dualApp_eq_dualEval E _ V' y).trans (Eq.trans ?_ (dualApp_eq_dualEval E _ V' y).symm)
  rw [PresheafOfModules.sections_property, PresheafOfModules.sections_property]
  exact h _ y

/-- `𝒪_X(E)` as an object of `X.Modules`. -/
abbrev divisorSheaf {X : Scheme.{u}} (E : X.IdealSheafData) : X.Modules := invertibleSheaf' E

/-- The canonical map `𝒪_X ⟶ 𝒪_X(E)`. -/
def canonicalHom {X : Scheme.{u}} (E : X.IdealSheafData) :
    Stacks.Ample.unitModule X ⟶ divisorSheaf E :=
  (SheafOfModules.unitHomEquiv (R := X.ringCatSheaf) (invertibleSheaf' E)).symm
    (canonicalSection' E)

omit [IsLocalRing A] [IsNoetherianRing A] [IsNormalDomain A] in
/-- The action of `a ∈ A` on a morphism of `𝒪_X`-modules is multiplication by the image of `a`
on sections. -/
theorem smul_val_app (Y : Over (Spec (.of A))) {M N : Y.left.Modules} (g : M ⟶ N)
    (a : A) (W : Y.left.Opensᵒᵖ) (x : M.val.obj W) :
    letI := modulesLinear A Y
    ((a • g).val.app W).hom x = baseRingToSections A Y W a • (g.val.app W).hom x := by
  let := modulesLinear A Y
  show (g.val.app W).hom (baseRingToSections A Y W a • x) = _
  exact (g.val.app W).hom.map_smul _ x

/-- The canonical map sends `1` to the canonical section. -/
theorem canonicalHom_val_app_one {X : Scheme.{u}} (E : X.IdealSheafData) (W : X.Opens) :
    ((canonicalHom E).val.app (op W)).hom (1 : X.ringCatSheaf.obj.obj (op W)) =
      (canonicalSection' E).val (op W) :=
  congrArg (fun σ : (invertibleSheaf' E).sections => σ.val (op W))
    ((SheafOfModules.unitHomEquiv (R := X.ringCatSheaf) (invertibleSheaf' E)).apply_symm_apply
      (canonicalSection' E))

omit [IsLocalRing A] [IsNoetherianRing A] [IsNormalDomain A] in
/-- The value of `a • s_E` on a section `y` of `ℐ_E` is `a · y`. -/
theorem dualEval_smul_canonicalHom (Y : Over (Spec (.of A))) (E : Y.left.IdealSheafData) (a : A)
    (W : Y.left.Opens) (y : (negativeTwist' E).val.obj (op W)) :
    letI := modulesLinear A Y
    dualEval (L := negativeTwist' E)
      (((a • canonicalHom E).val.app (op W)).hom (1 : Y.left.ringCatSheaf.obj.obj (op W))) y =
      @HMul.hMul Γ(Y.left, W) Γ(Y.left, W) Γ(Y.left, W) instHMul
        (baseRingToSections A Y (op W) a) (((idealInclusion E).val.app (op W)).hom y) := by
  let := modulesLinear A Y
  have h1 := smul_val_app Y (canonicalHom E) a (op W) (1 : Y.left.ringCatSheaf.obj.obj (op W))
  rw [canonicalHom_val_app_one] at h1
  refine (congrArg (fun z : (invertibleSheaf' E).val.obj (op W) =>
    dualEval (L := negativeTwist' E) z y) h1).trans ?_
  show @HMul.hMul Γ(Y.left, W) Γ(Y.left, W) Γ(Y.left, W) instHMul
    (Y.left.presheaf.map (𝟙 (op W)) (baseRingToSections A Y (op W) a)) _ = _
  rw [Y.left.presheaf.map_id]
  rfl

/-- **Every map `𝒪_X ⟶ 𝒪_X(E)` is `a • s_E`** (step of the proof of [Stacks, Tag 0EA2]). -/
theorem exists_eq_smul_canonicalHom (hdim : ringKrullDim A = 2) (Y : Over (Spec (.of A)))
    (hY : IsModification Y.hom) (E : Y.left.IdealSheafData)
    (hE : ∀ x : Y.left, x ∈ E.support → Y.hom x = closedPoint A)
    (g : Stacks.Ample.unitModule Y.left ⟶ divisorSheaf E) :
    letI := modulesLinear A Y
    ∃ a : A, g = a • canonicalHom E := by
  let := modulesLinear A Y
  obtain ⟨a, ha⟩ := sections_eq_smul_idealInclusion hdim Y.hom hY E hE
    (SheafOfModules.unitHomEquiv (R := Y.left.ringCatSheaf) _ g)
  exact ⟨a, (SheafOfModules.unitHomEquiv (R := Y.left.ringCatSheaf) _).injective
    (sections_ext E fun W y => (ha W y).trans (dualEval_smul_canonicalHom Y E a W y).symm)⟩

/-- **`a • s_E = 0` only for `a = 0`**: over the preimage of the punctured spectrum `s_E` sends a
section to itself, and `A ⟶ Γ(f⁻¹(U), 𝒪_X)` is injective. -/
theorem eq_zero_of_smul_canonicalHom_eq_zero (hdim : ringKrullDim A = 2)
    (Y : Over (Spec (.of A))) (hY : IsModification Y.hom) (E : Y.left.IdealSheafData)
    (hE : ∀ x : Y.left, x ∈ E.support → Y.hom x = closedPoint A) (a : A) :
    letI := modulesLinear A Y
    a • canonicalHom E = 0 → a = 0 := by
  let := modulesLinear A Y
  intro h
  set V := Y.hom ⁻¹ᵁ Stacks.puncturedSpectrum A
  have hVE : ∀ x ∈ V, x ∉ E.support := fun x hx hxE => hx (hE x hxE)
  obtain ⟨y₁, hy₁⟩ := exists_idealInclusion_eq_unitSection E V hVE
  have h1 := dualEval_smul_canonicalHom Y E a V y₁
  rw [h, hy₁] at h1
  apply (bijective_baseRingToSections_preimage_puncturedSpectrum hdim Y.hom hY).1
  refine Eq.trans ?_ (map_zero (baseRingToSections A Y (op V))).symm
  refine Eq.trans ?_ h1.symm
  exact (mul_one (M := Γ(Y.left, V)) _).symm

end DivisorSections

end AlgebraicGeometry.DualizingDivisor
