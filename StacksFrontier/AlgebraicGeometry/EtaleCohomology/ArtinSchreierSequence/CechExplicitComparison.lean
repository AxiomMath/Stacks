module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.CechFrobenius
public import StacksFrontier.AlgebraicGeometry.Modules.AlternatingCechModuleQuasiIso
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFamily.CurveCechCohomology
public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType.Basis

/-!
# The Čech complex of `V ↦ Γ((S ×_S X) ×_X V)` is the explicit Čech complex of `𝒪_X`

Let `f : X ⟶ Spec A` and let `U` be a family of opens of `X`. The Čech complex
`Stacks.ArtinSchreier.baseCech f U` of `Γ(Spec A)`-modules, built from Mathlib's
`CategoryTheory.cechComplexFunctor` and the presheaf `V ↦ Γ((S ×_S X) ×_X V)`, is isomorphic to
the explicit `A`-linear Čech complex `Stacks.Cech.cechModuleComplex` of `𝒪_X`, read over
`Γ(Spec A)` through `Γ(Spec A) ≅ A`. Restriction of a function on `V` to the open subscheme
`(S ×_S X) ×_X V ≅ V` identifies the terms.

## Main definitions

* `Stacks.ArtinSchreier.fibreSections`: `Γ(X, W) ⟶ Γ((S ×_S X) ×_X V)` for `V ≤ W`.
* `Stacks.ArtinSchreier.explicitCechIso`: the isomorphism of complexes.

## Main results

* `Stacks.ArtinSchreier.free_finite_homology_baseCech`: freeness and finiteness of the
  cohomology of the explicit complex pass to `baseCech f U`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
open Stacks.CategoryTheory.CechComplex
open Stacks.AlgebraicGeometry.CurveCechCohomology (unitModule)

universe u

namespace Stacks.ArtinSchreier

section Sections

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- `a.appTop` is `a.appLE ⊤ ⊤`. -/
theorem appTop_eq_appLE {Y Z : Scheme.{u}} (a : Y ⟶ Z) :
    a.appTop = a.appLE ⊤ ⊤ (Scheme.Hom.preimage_top a).ge :=
  (Scheme.Hom.appLE_eq_app a).symm

/-- `g.appLE U ⊤ e` followed by `f.appTop` is `(f ≫ g).appLE U ⊤`. -/
theorem appLE_comp_appTop {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens)
    (e : ⊤ ≤ g ⁻¹ᵁ U) :
    g.appLE U ⊤ e ≫ f.appTop = (f ≫ g).appLE U ⊤
      ((Scheme.Hom.preimage_top f).ge.trans ((Opens.map f.base).monotone e)) := by
  rw [appTop_eq_appLE f, Scheme.Hom.appLE_comp_appLE]

/-- The open immersion `(S ×_S X) ×_X V ⟶ X`. -/
abbrev openFibreIncl (V : X.Opens) : pullback (pullback.snd (𝟙 S) f) V.ι ⟶ X :=
  pullback.snd (pullback.snd (𝟙 S) f) V.ι ≫ V.ι

/-- For `V ≤ W`, the preimage of `W` under `(S ×_S X) ×_X V ⟶ X` is everything. -/
theorem le_preimage_openFibreIncl {V W : X.Opens} (h : V ≤ W) :
    ⊤ ≤ openFibreIncl f V ⁻¹ᵁ W := by
  intro z _
  have hm : V.ι (pullback.snd (pullback.snd (𝟙 S) f) V.ι z) ∈ ((V : X.Opens) : Set X) :=
    (Scheme.Opens.range_ι V) ▸ Set.mem_range_self _
  exact h hm

/-- **Restriction of a function on `W ⊇ V` to `(S ×_S X) ×_X V`.** -/
def fibreSections {V W : X.Opens} (h : V ≤ W) :
    Γ(X, W) ⟶ Γ(pullback (pullback.snd (𝟙 S) f) V.ι, ⊤) :=
  (openFibreIncl f V).appLE W ⊤ (le_preimage_openFibreIncl f h)

/-- Equal morphisms of schemes have equal `appLE` maps. -/
theorem appLE_eq_of_eq {Y Z : Scheme.{u}} {a b : Y ⟶ Z} (hab : a = b) (W : Z.Opens)
    (V : Y.Opens) (e : V ≤ a ⁻¹ᵁ W) : a.appLE W V e = b.appLE W V (hab ▸ e) := by
  subst hab
  rfl

/-- For `V' ≤ V`, the map `(S ×_S X) ×_X V' ⟶ (S ×_S X) ×_X V` commutes with the open immersions
into `X`. -/
theorem pullbackOpenMap_comp_openFibreIncl {V' V : X.Opens} (hV : V' ≤ V) :
    pullbackOpenMap (pullback.snd (𝟙 S) f) hV ≫ openFibreIncl f V = openFibreIncl f V' := by
  rw [← Category.assoc, pullbackOpenMap_snd, Category.assoc, Scheme.homOfLE_ι]

/-- Restricting functions commutes with the transition maps. -/
theorem map_fibreSections {V' V W' W : X.Opens} (hV : V' ≤ V) (hW : W' ≤ W) (h : V ≤ W)
    (h' : V' ≤ W') :
    X.presheaf.map (homOfLE hW).op ≫ fibreSections f h' =
      fibreSections f h ≫ (pullbackOpenMap (pullback.snd (𝟙 S) f) hV).appTop := by
  rw [fibreSections, fibreSections, Scheme.Hom.map_appLE, appLE_comp_appTop]
  exact appLE_eq_of_eq (pullbackOpenMap_comp_openFibreIncl f hV).symm _ _ _

/-- Restriction of a function on `V` to `(S ×_S X) ×_X V` is an isomorphism. -/
instance isIso_fibreSections_refl (V : X.Opens) : IsIso (fibreSections f (le_refl V)) := by
  have e : fibreSections f (le_refl V) =
      V.ι.appLE V ⊤ V.ι_preimage_self.ge ≫ (pullback.snd (pullback.snd (𝟙 S) f) V.ι).appTop :=
    (appLE_comp_appTop _ _ _ _).symm
  rw [e]
  have : IsIso (pullback.snd (pullback.snd (𝟙 S) f) V.ι).appTop :=
    (inferInstance : IsIso ((pullback.snd (pullback.snd (𝟙 S) f) V.ι).app ⊤))
  exact IsIso.comp_isIso

/-- `fibreSections f h` is an isomorphism when `V = W`. -/
theorem isIso_fibreSections {V W : X.Opens} (h : V ≤ W) (heq : V = W) :
    IsIso (fibreSections f h) := by
  subst heq
  exact isIso_fibreSections_refl f V

/-- `fibreSections f h` is bijective when `V = W`. -/
theorem bijective_fibreSections {V W : X.Opens} (h : V ≤ W) (heq : V = W) :
    Function.Bijective (fibreSections f h) := by
  have := isIso_fibreSections f h heq
  exact ConcreteCategory.bijective_of_isIso _

/-- On the structure map, restricting is the pullback of functions from the base. -/
theorem appLE_comp_fibreSections {V W : X.Opens} (h : V ≤ W) (e : W ≤ f ⁻¹ᵁ ⊤) :
    f.appLE ⊤ W e ≫ fibreSections f h =
      (pullback.fst (pullback.snd (𝟙 S) f) V.ι ≫ pullback.fst (𝟙 S) f).appTop := by
  rw [fibreSections, Scheme.Hom.appLE_comp_appLE, appTop_eq_appLE]
  refine appLE_eq_of_eq ?_ _ _ _
  show (pullback.snd (pullback.snd (𝟙 S) f) V.ι ≫ V.ι) ≫ f = _
  rw [← pullback.condition, Category.assoc, ← pullback.condition, Category.comp_id]

end Sections

section Explicit

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) {ι : Type}
  (U : ι → X.Opens)

/-- The family `U`, indexed in the universe of `X`. -/
abbrev liftCover : ULift.{u} ι → X.Opens := fun i => U i.down

/-- `Γ(Spec A) ≅ A`, as a ring homomorphism. -/
abbrev specΓHom (A : Type u) [CommRing A] : Γ(Spec (.of A), ⊤) →+* A :=
  (Scheme.ΓSpecIso (.of A)).hom.hom

/-- **The explicit Čech complex of `𝒪_X`**, as a complex of `Γ(Spec A)`-modules. -/
abbrev explicitCech : CochainComplex (ModuleCat.{u} Γ(Spec (.of A), ⊤)) ℕ :=
  ((ModuleCat.restrictScalars.{u} (specΓHom A)).mapHomologicalComplex _).obj
    (Stacks.Cech.cechModuleComplex f (liftCover U) (unitModule X))

/-- The intersection `U_{x₀} ∩ ⋯ ∩ U_{xₙ₋₁}` is contained in the corresponding intersection of
`liftCover U`. -/
theorem inter_le_cechInter {n : ℕ} (x : Fin n → ι) :
    inter U x ≤ CechCochains.inter (liftCover U) (ULift.up ∘ x) :=
  (inter_eq_iInf U x).le

/-- `toSpecΓ A` is a left inverse of `specΓHom A`. -/
theorem toSpecΓ_specΓHom (b : Γ(Spec (.of A), ⊤)) :
    (toSpecΓ (CommRingCat.of A)).hom (specΓHom A b) = b :=
  congrArg (fun φ => φ.hom b) (Scheme.ΓSpecIso (.of A)).hom_inv_id

/-- Restricting to `(S ×_S X) ×_X V` the image of a function `b` on `Spec A` in `Γ(X, W)` gives the
pullback of `b` along `(S ×_S X) ×_X V ⟶ S`. -/
theorem fibreSections_baseRingHom {V W : X.Opens} (h : V ≤ W) (b : Γ(Spec (.of A), ⊤)) :
    (fibreSections f h).hom ((Stacks.Cech.baseRingHom f W).hom (specΓHom A b)) =
      (pullback.fst (pullback.snd (𝟙 _) f) V.ι ≫ pullback.fst (𝟙 _) f).appTop.hom b := by
  rw [Stacks.Cech.baseRingHom_eq_appLE f W (le_top.trans (Scheme.Hom.preimage_top f).ge)]
  show (f.appLE ⊤ W (le_top.trans (Scheme.Hom.preimage_top f).ge) ≫ fibreSections f h).hom
    ((toSpecΓ (CommRingCat.of A)).hom (specΓHom A b)) = _
  rw [appLE_comp_fibreSections, toSpecΓ_specΓHom]

/-- The value of an explicit cochain at a tuple, as a function. -/
def cochainVal {p : ℕ} (s : (explicitCech f U).X p) (i : Fin (p + 1) → ULift.{u} ι) :
    Γ(X, CechCochains.inter (liftCover U) i) :=
  (show CechCochains.Cochain (liftCover U) (unitModule X).presheaf p from s) i

/-- The value of `b • s` is the image of `b` under `Γ(Spec A) ⟶ Γ(X, ·)` times the value of `s`. -/
theorem cochainVal_smul {p : ℕ} (b : Γ(Spec (.of A), ⊤)) (s : (explicitCech f U).X p)
    (i : Fin (p + 1) → ULift.{u} ι) :
    cochainVal f U (b • s) i =
      (Stacks.Cech.baseRingHom f _).hom (specΓHom A b) * cochainVal f U s i :=
  rfl

/-- The value of a sum of cochains is the sum of the values. -/
theorem cochainVal_add {p : ℕ} (s t : (explicitCech f U).X p) (i : Fin (p + 1) → ULift.{u} ι) :
    cochainVal f U (s + t) i = cochainVal f U s i + cochainVal f U t i :=
  rfl

/-- The component of the comparison at a tuple `x`. -/
def explicitComponent (p : ℕ) (x : Fin (p + 1) → ι) :
    (explicitCech f U).X p ⟶ (baseSectionsPresheaf f).obj (op (inter U x)) :=
  ModuleCat.ofHom (X := (explicitCech f U).X p)
      (Y := (baseSectionsPresheaf f).obj (op (inter U x)))
    { toFun := fun s => (fibreSections f (inter_le_cechInter U x)).hom
        (cochainVal f U s (ULift.up ∘ x))
      map_add' := fun s t => map_add (fibreSections f (inter_le_cechInter U x)).hom
        (cochainVal f U s (ULift.up ∘ x)) (cochainVal f U t (ULift.up ∘ x))
      map_smul' := fun b s =>
        (congrArg (fibreSections f (inter_le_cechInter U x)).hom
          (cochainVal_smul f U b s (ULift.up ∘ x))).trans
          ((map_mul _ _ _).trans (congrArg (· * _) (fibreSections_baseRingHom f _ b))) }

/-- `explicitComponent` restricts the value of a cochain at `x` to `(S ×_S X) ×_X U_x`. -/
theorem explicitComponent_apply (p : ℕ) (x : Fin (p + 1) → ι) (s : (explicitCech f U).X p) :
    (explicitComponent f U p x).hom s = (fibreSections f (inter_le_cechInter U x)).hom
      (cochainVal f U s (ULift.up ∘ x)) :=
  rfl

/-- The comparison in degree `p`. -/
def explicitToBaseCechF (p : ℕ) : (explicitCech f U).X p ⟶ (baseCech f U).X p :=
  lift U (baseSectionsPresheaf f) (explicitComponent f U p)

/-- The `x`-component of `explicitToBaseCechF f U p s` is `explicitComponent f U p x s`. -/
theorem π_explicitToBaseCechF_apply (p : ℕ) (x : Fin (p + 1) → ι) (s : (explicitCech f U).X p) :
    π U (baseSectionsPresheaf f) p x ((explicitToBaseCechF f U p).hom s) =
      (explicitComponent f U p x).hom s :=
  congrArg (fun φ => φ.hom s) (lift_comp_π U (baseSectionsPresheaf f) (explicitComponent f U p) x)

/-- The value of the differential of an explicit cochain at `y` is the alternating sum of the
restrictions of its values at the faces of `y`. -/
theorem cochainVal_d {p : ℕ} (s : (explicitCech f U).X p) (y : Fin (p + 2) → ULift.{u} ι) :
    cochainVal f U (((explicitCech f U).d p (p + 1)).hom s) y =
      ∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
        (X.presheaf.map (homOfLE (CechCochains.inter_le_omit (liftCover U) y j)).op).hom
          (cochainVal f U s (y ∘ j.succAbove)) := by
  rw [Functor.mapHomologicalComplex_obj_d, Stacks.Cech.cechModuleComplex_d]
  rfl

/-- The components `explicitToBaseCechF` commute with the differentials. -/
theorem explicitToBaseCechF_comm (p : ℕ) :
    explicitToBaseCechF f U p ≫ (baseCech f U).d p (p + 1) =
      (explicitCech f U).d p (p + 1) ≫ explicitToBaseCechF f U (p + 1) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun s => baseCech_ext f U fun y => ?_)
  show π U (baseSectionsPresheaf f) (p + 1) y
      ((baseCech f U).d p (p + 1) ((explicitToBaseCechF f U p).hom s)) =
    π U (baseSectionsPresheaf f) (p + 1) y ((explicitToBaseCechF f U (p + 1)).hom
      (((explicitCech f U).d p (p + 1)).hom s))
  rw [π_explicitToBaseCechF_apply f U (p + 1), explicitComponent_apply, cochainVal_d, map_sum,
    π_d_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, π_explicitToBaseCechF_apply, explicitComponent_apply]
  congr 1
  exact (congrArg (fun φ => φ.hom (cochainVal f U s ((ULift.up ∘ y) ∘ j.succAbove)))
    (map_fibreSections f (interMap U y j.succAbove).le
    (CechCochains.inter_le_omit (liftCover U) (ULift.up ∘ y) j) (inter_le_cechInter U _)
    (inter_le_cechInter U y))).symm

/-- Each component `explicitToBaseCechF f U p` is bijective. -/
theorem bijective_explicitToBaseCechF (p : ℕ) :
    Function.Bijective (explicitToBaseCechF f U p).hom := by
  have hb : ∀ x : Fin (p + 1) → ι, Function.Bijective
      (fibreSections f (inter_le_cechInter U x)).hom :=
    fun x => bijective_fibreSections f _ (inter_eq_iInf U x)
  constructor
  · intro s t hst
    refine funext fun i => (hb (ULift.down ∘ i)).1 ?_
    have h := congrArg (π U (baseSectionsPresheaf f) p (ULift.down ∘ i)) hst
    rwa [π_explicitToBaseCechF_apply, π_explicitToBaseCechF_apply, explicitComponent_apply,
      explicitComponent_apply] at h
  · intro z
    let s : CechCochains.Cochain (liftCover U) (unitModule X).presheaf p :=
      fun i => Function.surjInv (hb (ULift.down ∘ i)).2
        (π U (baseSectionsPresheaf f) p (ULift.down ∘ i) z)
    refine ⟨show (explicitCech f U).X p from s, baseCech_ext f U fun x => ?_⟩
    rw [π_explicitToBaseCechF_apply, explicitComponent_apply]
    exact Function.surjInv_eq (hb x).2 _

/-- **The comparison of the explicit Čech complex of `𝒪_X` with `baseCech f U`.** -/
def explicitToBaseCech : explicitCech f U ⟶ baseCech f U where
  f := explicitToBaseCechF f U
  comm' := by
    rintro p _ rfl
    exact explicitToBaseCechF_comm f U p

/-- The comparison `explicitToBaseCech f U` is an isomorphism of complexes. -/
instance isIso_explicitToBaseCech : IsIso (explicitToBaseCech f U) := by
  have : ∀ p, IsIso ((explicitToBaseCech f U).f p) := fun p =>
    (ConcreteCategory.isIso_iff_bijective _).2 (bijective_explicitToBaseCechF f U p)
  exact HomologicalComplex.Hom.isIso_of_components _

/-- `Γ(Spec A) ≃ A`. -/
abbrev specΓEquiv (A : Type u) [CommRing A] : Γ(Spec (.of A), ⊤) ≃+* A :=
  (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv

/-- A free finite `A`-module is free and finite over `Γ(Spec A)` by restriction of scalars along
`Γ(Spec A) ≅ A`. -/
theorem free_finite_restrictScalars (M : ModuleCat.{u} A) (hfree : Module.Free A M)
    (hfin : Module.Finite A M) :
    Module.Free Γ(Spec (.of A), ⊤) ((ModuleCat.restrictScalars.{u} (specΓHom A)).obj M) ∧
      Module.Finite Γ(Spec (.of A), ⊤) ((ModuleCat.restrictScalars.{u} (specΓHom A)).obj M) := by
  let : Module Γ(Spec (.of A), ⊤) M :=
    ((ModuleCat.restrictScalars.{u} (specΓHom A)).obj M).isModule
  have h : ∀ (c : A) (x : M), (specΓEquiv A).symm c • x = c • x := fun c x => by
    show specΓHom A ((specΓEquiv A).symm c) • x = c • x
    rw [show specΓHom A ((specΓEquiv A).symm c) = c from (specΓEquiv A).apply_symm_apply c]
  let b := (Module.Free.chooseBasis A M).mapCoeffs (specΓEquiv A).symm h
  exact ⟨Module.Free.of_basis b, Module.Finite.of_basis b⟩

/-- **Free and finite cohomology of the explicit Čech complex of `𝒪_X` over `A` gives free and
finite cohomology of `baseCech f U` over `Γ(Spec A)`.** -/
theorem free_finite_homology_baseCech (q : ℕ)
    (hfree : Module.Free A ((Stacks.Cech.cechModuleComplex f (liftCover U)
      (unitModule X)).homology q))
    (hfin : Module.Finite A ((Stacks.Cech.cechModuleComplex f (liftCover U)
      (unitModule X)).homology q)) :
    Module.Free Γ(Spec (.of A), ⊤) ((baseCech f U).homology q) ∧
      Module.Finite Γ(Spec (.of A), ⊤) ((baseCech f U).homology q) := by
  let e : (baseCech f U).homology q ≅ (ModuleCat.restrictScalars.{u} (specΓHom A)).obj
      ((Stacks.Cech.cechModuleComplex f (liftCover U)
        (unitModule X)).homology q) :=
    (HomologicalComplex.homologyFunctor _ _ q).mapIso (asIso (explicitToBaseCech f U)).symm ≪≫
      ShortComplex.mapHomologyIso ((Stacks.Cech.cechModuleComplex f (liftCover U)
        (unitModule X)).sc q) (ModuleCat.restrictScalars.{u} (specΓHom A))
  obtain ⟨h1, h2⟩ := free_finite_restrictScalars _ hfree hfin
  exact ⟨Module.Free.of_equiv e.symm.toLinearEquiv, Module.Finite.equiv e.symm.toLinearEquiv⟩

end Explicit

section Cocycles

variable {X S : Scheme.{u}} (f : X ⟶ S) {ι : Type} (U : ι → X.Opens)

/-- **A basis of free cohomology is represented by cocycles.** If `Hᵠ(baseCech f U)` is free of
finite rank, there are cocycles whose classes form a basis, so that the map
`Γ(S)ʳ ⟶ Hᵠ`, `b ↦ ∑ bᵢ [zᵢ]`, is an isomorphism. -/
theorem exists_cocycles_isIso (q : ℕ)
    [Module.Free Γ(S, ⊤) ((baseCech f U).homology q)]
    [Module.Finite Γ(S, ⊤) ((baseCech f U).homology q)] :
    ∃ (r : ℕ) (z : Fin r → (baseCech f U).X q) (hz : ∀ i, (baseCech f U).d q (q + 1) (z i) = 0),
      IsIso ((baseCech f U).liftCycles (moduleBasisMapDeg f U z) (q + 1) (by simp)
        (moduleBasisMapDeg_comp_d f U z hz) ≫ (baseCech f U).homologyπ q) := by
  classical
  let K := baseCech f U
  let bs := (Module.Free.chooseBasis Γ(S, ⊤) (K.homology q)).reindex (Fintype.equivFin _)
  have hπ : Function.Surjective (K.homologyπ q).hom :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  choose c hc using fun i => hπ (bs i)
  let z : Fin _ → K.X q := fun i => (K.iCycles q).hom (c i)
  have hz : ∀ i, K.d q (q + 1) (z i) = 0 := fun i => by
    show (K.iCycles q ≫ K.d q (q + 1)).hom (c i) = 0
    rw [K.iCycles_d]
    rfl
  refine ⟨_, z, hz, ?_⟩
  set L := K.liftCycles (moduleBasisMapDeg f U z) (q + 1) (by simp)
    (moduleBasisMapDeg_comp_d f U z hz)
  have hΦ : ∀ i, (L ≫ K.homologyπ q).hom (Pi.single i 1) = bs i := by
    intro i
    have h1 : L.hom (Pi.single i 1) = c i := by
      apply (ModuleCat.mono_iff_injective (K.iCycles q)).1 inferInstance
      show (L ≫ K.iCycles q).hom _ = _
      rw [K.liftCycles_i]
      exact moduleBasisMapDeg_single f U z i
    show (K.homologyπ q).hom (L.hom (Pi.single i 1)) = _
    rw [h1, hc]
  have hlin : (L ≫ K.homologyπ q).hom = bs.equivFun.symm.toLinearMap :=
    (Pi.basisFun Γ(S, ⊤) (Fin _)).ext fun i => by
      rw [Pi.basisFun_apply, hΦ, LinearEquiv.coe_coe, eq_comm, LinearEquiv.symm_apply_eq,
        Module.Basis.equivFun_apply, Module.Basis.repr_self, Finsupp.single_eq_pi_single]
  refine (ConcreteCategory.isIso_iff_bijective _).2 ?_
  show Function.Bijective (L ≫ K.homologyπ q).hom
  rw [hlin]
  exact bs.equivFun.symm.bijective

end Cocycles

section BaseChange

open Stacks.AlgebraicGeometry.ProperFlatGlobalSections in
/-- **From the alternating Čech model of `𝒪_X` over `A` to `baseCech` of a base change.** If
`A ⟶ A'` makes `X'` the base change of `X ⟶ Spec A`, and the base change to `A'` of the
`A`-linear alternating Čech model of `𝒪_X` for a finite affine cover `U` has free cohomology of
finite rank in degree `q`, then so has `baseCech f' (g⁻¹ U)` over `Γ(Spec A')`. -/
theorem free_finite_homology_baseCech_of_isPullback {A A' : Type u} [CommRing A] [CommRing A']
    (φ : A →+* A') {X X' : Scheme.{u}} {f : X ⟶ Spec (.of A)} [IsSeparated f]
    {f' : X' ⟶ Spec (.of A')} {g : X' ⟶ X}
    (hsq : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
    {ι : Type} [Finite ι] [LinearOrder ι] (U : ι → X.Opens)
    (hU : (⊤ : X.Opens) = ⨆ i, liftCover U i) (hUaff : ∀ i, IsAffineOpen (U i)) (q : ℕ)
    (hfree : Module.Free A' ((((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (baseAlternatingCechComplex f (liftCover U) hU
        (unitModule X))).homology (q : ℤ)))
    (hfin : Module.Finite A' ((((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (baseAlternatingCechComplex f (liftCover U) hU
        (unitModule X))).homology (q : ℤ))) :
    Module.Free Γ(Spec (.of A'), ⊤) ((baseCech f' (fun i => g ⁻¹ᵁ U i)).homology q) ∧
      Module.Finite Γ(Spec (.of A'), ⊤) ((baseCech f' (fun i => g ⁻¹ᵁ U i)).homology q) := by
  have : (unitModule X).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isQuasicoherent_unit
  let U' : ι → X'.Opens := fun i => g ⁻¹ᵁ U i
  let hU' := top_eq_iSup_preimage g (liftCover U) hU
  let e : (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (baseAlternatingCechComplex f (liftCover U) hU
        (unitModule X))).homology (q : ℤ) ≅
      (Stacks.Cech.cechModuleComplex f' (liftCover U')
        (SheafOfModules.unit X'.ringCatSheaf)).homology q :=
    (HomologicalComplex.homologyFunctor _ _ (q : ℤ)).mapIso
        (baseAlternatingCechComplexBaseChangeIso φ hsq (unitModule X)
          (liftCover U) hU (fun i => hUaff i.down) ≪≫
        baseAlternatingCechComplexMapIso f' (liftCover U') hU'
          (Stacks.AlgebraicGeometry.AffineBaseChange.pullbackUnitIso g) ≪≫
        baseAlternatingCechComplexIsoExtend f' (liftCover U') hU'
          (SheafOfModules.unit X'.ringCatSheaf)) ≪≫
      (Stacks.Cech.alternatingCechModuleComplex f' (liftCover U')
          (SheafOfModules.unit X'.ringCatSheaf)).extendHomologyIso ComplexShape.embeddingUpNat
          (j := q) (j' := (q : ℤ)) rfl ≪≫
      Stacks.Cech.alternatingCechModuleHomologyIso f' (liftCover U')
        (SheafOfModules.unit X'.ringCatSheaf) q
  exact free_finite_homology_baseCech f' U' q (Module.Free.of_equiv e.toLinearEquiv)
    (Module.Finite.equiv e.toLinearEquiv)

end BaseChange

end Stacks.ArtinSchreier

end
