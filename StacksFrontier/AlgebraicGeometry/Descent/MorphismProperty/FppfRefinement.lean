module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.MorphismProperty.FaithfullyFlatRing
public import StacksFrontier.AlgebraicGeometry.Descent.MorphismProperty.StandardFppfRefinement
public import StacksFrontier.CategoryTheory.Sites.Hypercover.ZeroOver

/-!
# Descent of morphism properties along an fppf refinement

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of schemes and suppose the singleton family
consisting of `f` is refined by an fppf covering of `Y`. Then flatness, local finite type and
local finite presentation all descend from the composite `f ≫ g` to `g`.

## Main results

* `AlgebraicGeometry.flat_of_comp_of_fppf_refinement`: descent of flatness.
* `AlgebraicGeometry.locallyOfFiniteType_of_comp_of_fppf_refinement`: descent of the locally
  finite type property.
* `AlgebraicGeometry.locallyOfFinitePresentation_of_comp_of_fppf_refinement`: descent of the
  locally finite presentation property.

## Implementation notes

An fppf covering is represented by a zero-hypercover for Mathlib's fppf precoverage, and the
assertion that it refines the singleton family consisting of `f` is a morphism of
pre-zero-hypercovers.

Flatness is checked on stalks: the stalk of the refining cover is faithfully flat over the
stalk of `Y`, so the stalk of `Y` is a pure submodule of the stalk of `X`, and flatness of
the composite descends. The two finiteness properties are checked on affine opens, where
`AlgebraicGeometry.exists_standardFppfCovering_through_affineOpens` replaces `f` by a finite
standard fppf covering and reduces the statement to its ring-theoretic counterpart.

## References

* [Stacks Project, Tag 06NB](https://stacks.math.columbia.edu/tag/06NB)
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry

section Flat

open TensorProduct

universe u₁ u₂ u₃

/-- If `A` is flat over `R`, contains `S` as an `S`-pure submodule in the sense that
`1 ⊗ -` is injective on every `S`-module, and `S` sits between them, then `S` is flat
over `R`. -/
private theorem flat_of_pure_extension
    {R : Type u₁} {S : Type u₂} {A : Type u₃} [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
    [Module.Flat R A]
    (hpure : ∀ {M : Type (max u₁ u₂)} [AddCommGroup M] [Module S M]
      (x y : M), (1 : A) ⊗ₜ[S] x = (1 : A) ⊗ₜ[S] y → x = y) :
    Module.Flat R S := by
  rw [Module.Flat.iff_lTensor_injectiveₛ]
  intro P _ _ I
  let uI : S ⊗[R] I →ₗ[R] A ⊗[R] I :=
    TensorProduct.map (IsScalarTower.toAlgHom R S A).toLinearMap (LinearMap.id)
  let uP : S ⊗[R] P →ₗ[R] A ⊗[R] P :=
    TensorProduct.map (IsScalarTower.toAlgHom R S A).toLinearMap (LinearMap.id)
  have huI : Function.Injective uI := by
    let e := TensorProduct.AlgebraTensorModule.cancelBaseChange R S A A I
    have hh : Function.Injective (fun x : S ⊗[R] I ↦ e ((1 : A) ⊗ₜ[S] x)) :=
      e.injective.comp fun x y ↦ hpure x y
    have heq (x : S ⊗[R] I) : e ((1 : A) ⊗ₜ[S] x) = uI x := by
      induction x using TensorProduct.induction_on with
      | zero => simp [uI]
      | add x y hx hy => simp only [tmul_add, map_add, hx, hy]
      | tmul s i => simp [e, uI, Algebra.smul_def,
          TensorProduct.AlgebraTensorModule.cancelBaseChange]
    simpa only [heq] using hh
  have hsq (x : S ⊗[R] I) :
      uP ((LinearMap.lTensor S I.subtype) x) = (LinearMap.lTensor A I.subtype) (uI x) := by
    induction x using TensorProduct.induction_on with
    | zero => simp [uI, uP]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul s i => simp [uI, uP]
  intro x y hxy
  apply huI
  apply Module.Flat.lTensor_preserves_injective_linearMap I.subtype I.injective_subtype
  rw [← hsq, ← hsq, hxy]

/-- If `S → D` is faithfully flat and factors through `A`, then `1 ⊗ -` is injective on
every `S`-module after base change to `A`. -/
@[ega "0 6.6.1" "(a)"]
private theorem pure_of_faithfullyFlat_factor
    {S A D : Type*} [CommRing S] [CommRing A] [CommRing D]
    [Algebra S A] [Algebra S D] [Algebra A D] [IsScalarTower S A D]
    [Module.FaithfullyFlat S D]
    (M : Type*) [AddCommGroup M] [Module S M] :
    Function.Injective (fun x : M ↦ (1 : A) ⊗ₜ[S] x) := by
  intro x y hxy
  apply sub_eq_zero.mp
  have hmap : (1 : D) ⊗ₜ[S] x = (1 : D) ⊗ₜ[S] y := by
    simpa using congrArg (TensorProduct.map (IsScalarTower.toAlgHom S A D).toLinearMap
      (LinearMap.id : M →ₗ[S] M)) hxy
  have hz : (1 : D) ⊗ₜ[S] (x - y) = 0 := by rw [tmul_sub, hmap, sub_self]
  exact (Module.FaithfullyFlat.one_tmul_eq_zero_iff S M (x - y)).mp hz

/-- **Stacks Project, Tag 06NB (flat).** If `f ≫ g` is flat and the singleton family
consisting of `f` is refined by an fppf covering of `Y`, then `g` is flat. -/
@[stacks 06NB "flat"]
theorem flat_of_comp_of_fppf_refinement
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [Flat (f ≫ g)]
    (h : ∃ 𝒰 : Y.Cover.{v} Scheme.fppfPrecoverage,
      Nonempty (𝒰.toPreZeroHypercover.Hom (PreZeroHypercover.singleton f))) :
    Flat g := by
  rw [Flat.iff_flat_stalkMap]
  intro y
  obtain ⟨𝒰, ⟨φ⟩⟩ := h
  have hdata := (Scheme.presieve₀_mem_precoverage_iff 𝒰.toPreZeroHypercover).mp
    (by simpa [Scheme.fppfPrecoverage] using 𝒰.mem₀)
  obtain ⟨i, x, hxy⟩ := hdata.1 y
  let k : 𝒰.X i ⟶ X := φ.h₀ i
  have hfy : f (k x) = y :=
    calc
      f (k x) = (k ≫ f) x := by simp
      _ = (𝒰.f i) x := congrArg (fun q : 𝒰.X i ⟶ Y ↦ q x) (φ.w₀ i)
      _ = y := hxy
  rw [← hfy]
  let C : Type u := ↑(Z.presheaf.stalk (g (f (k x))))
  let B : Type u := ↑(Y.presheaf.stalk (f (k x)))
  let A : Type u := ↑(X.presheaf.stalk (k x))
  let D : Type u := ↑((𝒰.X i).presheaf.stalk x)
  let α : C →+* B := (g.stalkMap (f (k x))).hom
  let β : B →+* A := (f.stalkMap (k x)).hom
  let δ : C →+* A := ((f ≫ g).stalkMap (k x)).hom
  let ρ : A →+* D := (k.stalkMap x).hom
  let e : (Y.presheaf.stalk (f (k x))) ≅ (Y.presheaf.stalk ((𝒰.f i) x)) :=
    Y.presheaf.stalkCongr (.of_eq (φ.w₀ i ▸ rfl))
  let σ : B →+* D := (e.hom ≫ (𝒰.f i).stalkMap x).hom
  have hcomp : δ = β.comp α := by
    dsimp [δ, β, α]
    simp only [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp]
  have hfactor : σ = ρ.comp β := by
    have hs := Scheme.Hom.stalkMap_congr_hom (k ≫ f) (𝒰.f i) (φ.w₀ i) x
    rw [Scheme.Hom.stalkMap_comp] at hs
    show (e.hom ≫ (𝒰.f i).stalkMap x).hom = _
    exact congrArg CommRingCat.Hom.hom hs.symm
  let _ : Algebra C B := α.toAlgebra
  let _ : Algebra B A := β.toAlgebra
  let _ : Algebra C A := δ.toAlgebra
  let _ : Algebra A D := ρ.toAlgebra
  let _ : Algebra B D := σ.toAlgebra
  have hscalarC : IsScalarTower C B A := .of_algebraMap_eq (RingHom.congr_fun hcomp)
  have hscalarB : IsScalarTower B A D := .of_algebraMap_eq (RingHom.congr_fun hfactor)
  have : Module.Flat C A := RingHom.flat_algebraMap_iff.mp (Flat.stalkMap (f ≫ g) (k x))
  have hflatσ : σ.Flat := by
    have : Flat (𝒰.f i) := (hdata.2 i).1
    show ((𝒰.f i).stalkMap x).hom.comp e.hom.hom |>.Flat
    exact (RingHom.Flat.comp_iff_of_bijective_right
      ((ConcreteCategory.isIso_iff_bijective _).mp inferInstance)).mpr (Flat.stalkMap (𝒰.f i) x)
  have : Module.Flat B D := RingHom.flat_algebraMap_iff.mp hflatσ
  have : IsLocalHom (algebraMap B D) :=
    inferInstanceAs (IsLocalHom (e.hom ≫ (𝒰.f i).stalkMap x).hom)
  have : Module.FaithfullyFlat B D := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hpure : ∀ {M : Type u} [AddCommGroup M] [Module B M]
      (a b : M), (1 : A) ⊗ₜ[B] a = (1 : A) ⊗ₜ[B] b → a = b := by
    intro M _ _ a b hab
    exact pure_of_faithfullyFlat_factor (S := B) (A := A) (D := D) M hab
  show α.Flat
  exact RingHom.flat_algebraMap_iff.mpr (flat_of_pure_extension (R := C) (S := B) (A := A) hpure)

end Flat

/-- Every point `y` of `Y` lies in an affine open mapping into an affine open of `Z`. -/
private theorem exists_affineOpens_le_preimage {Y Z : Scheme.{u}} (g : Y ⟶ Z) (y : Y) :
    ∃ (W : Z.affineOpens) (V : Y.affineOpens), y ∈ V.1 ∧ V.1 ≤ g ⁻¹ᵁ W.1 := by
  obtain ⟨W, hW, hyW, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens
    (show g y ∈ (⊤ : Z.Opens) from Set.mem_univ _)
  obtain ⟨V, hV, hyV, hVW⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
    (show y ∈ g ⁻¹ᵁ W from hyW)
  exact ⟨⟨W, hW⟩, ⟨V, hV⟩, hyV, hVW⟩

/-- The ring map of `appTop` of `resLE` of a composite factors through the `resLE`s. -/
private theorem resLE_comp_appTop_hom_apply {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {U : X.Opens} {V : Y.Opens} {W : Z.Opens} (hU : U ≤ f ⁻¹ᵁ V) (e : V ≤ g ⁻¹ᵁ W)
    (hUW : U ≤ (f ≫ g) ⁻¹ᵁ W) (x : Γ(W.toScheme, ⊤)) :
    ((f ≫ g).resLE W U hUW).appTop.hom x =
      (f.resLE V U hU).appTop.hom ((g.resLE W V e).appTop.hom x) := by
  rw [← Scheme.Hom.resLE_comp_resLE f hU g e]
  simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]

/-- **Stacks Project, Tag 06NB (locally finite type).** If `f ≫ g` is locally of finite type
and the singleton family consisting of `f` is refined by an fppf covering of `Y`, then `g` is
locally of finite type. -/
@[stacks 06NB "locally_finite_type"]
theorem locallyOfFiniteType_of_comp_of_fppf_refinement
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [LocallyOfFiniteType (f ≫ g)]
    (h : ∃ 𝒰 : Y.Cover.{v} Scheme.fppfPrecoverage,
      Nonempty (𝒰.toPreZeroHypercover.Hom (PreZeroHypercover.singleton f))) :
    LocallyOfFiniteType g := by
  rw [HasRingHomProperty.iff_exists_appLE (P := @LocallyOfFiniteType)
    (RingHom.finiteType_stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.finiteType_holdsForLocalizationAway).left]
  intro y
  obtain ⟨W', V', hyV, hVW⟩ := exists_affineOpens_le_preimage g y
  let q : V'.1.toScheme ⟶ W'.1.toScheme := g.resLE W'.1 V'.1 hVW
  obtain ⟨n, U, hU, T, t, hstd, hcompTop, hflat, hpres⟩ :=
    exists_standardFppfCovering_through_affineOpens f h V'
  have _ : IsAffine V'.1.toScheme := V'.2
  have _ : IsAffine W'.1.toScheme := W'.2
  have hUW (i : Fin n) : (U i).1 ≤ (f ≫ g) ⁻¹ᵁ W'.1 := fun _ hx ↦ hVW (hU i hx)
  have hsourceFT (i : Fin n) :
      ((f ≫ g).resLE W'.1 (U i).1 (hUW i)).appTop.hom.FiniteType := by
    have _ : IsAffine (U i).1.toScheme := (U i).2
    exact HasRingHomProperty.appTop (P := @LocallyOfFiniteType) _ inferInstance
  have htiFT (i : Fin n) : (t i).appTop.hom.FiniteType := by
    have hcomp : ((t i).appTop.hom.comp
        (f.resLE V'.1 (U i).1 (hU i)).appTop.hom).FiniteType := by
      rw [← hcompTop i]
      let c := t i ≫ f.resLE V'.1 (U i).1 (hU i)
      have _ : IsAffine (T i) := hstd.affine_source i
      have : LocallyOfFinitePresentation c := (hstd.finite_presentation i).1
      exact RingHom.FiniteType.of_finitePresentation c.finitePresentation_appTop
    exact RingHom.FiniteType.of_comp_finiteType hcomp
  have hcomponentFT (i : Fin n) :
      ((t i ≫ (f ≫ g).resLE W'.1 (U i).1 (hUW i)).appTop.hom).FiniteType := by
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] using (htiFT i).comp (hsourceFT i)
  have hcomm :
      RingHom.pi (fun i => (t i ≫ (f ≫ g).resLE W'.1 (U i).1 (hUW i)).appTop.hom) =
      (RingHom.pi (fun i => (t i ≫ f.resLE V'.1 (U i).1 (hU i)).appTop.hom)).comp
        q.appTop.hom := by
    ext x i
    show ((t i ≫ (f ≫ g).resLE W'.1 (U i).1 (hUW i)).appTop.hom) x =
      ((t i ≫ f.resLE V'.1 (U i).1 (hU i)).appTop.hom) ((q.appTop.hom) x)
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
    exact congrArg _ (resLE_comp_appTop_hom_apply f g (hU i) hVW (hUW i) x)
  exact ⟨W', V', hyV, hVW,
    (RingHom.finiteType_respectsIso.arrow_mk_iso_iff (arrowResLEAppIso g W'.1 V'.1 hVW)).mp
      (RingHom.finiteType_of_comp_of_faithfullyFlat_of_finitePresentation
        (hcomm ▸ RingHom.FiniteType.pi _ hcomponentFT) hflat hpres)⟩

/-- **Stacks Project, Tag 06NB (locally finite presentation).** If `f ≫ g` is locally of
finite presentation and the singleton family consisting of `f` is refined by an fppf covering
of `Y`, then `g` is locally of finite presentation. -/
@[stacks 06NB "locally_finite_presentation"]
theorem locallyOfFinitePresentation_of_comp_of_fppf_refinement
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [LocallyOfFinitePresentation (f ≫ g)]
    (h : ∃ 𝒰 : Y.Cover.{v} Scheme.fppfPrecoverage,
      Nonempty (𝒰.toPreZeroHypercover.Hom (PreZeroHypercover.singleton f))) :
    LocallyOfFinitePresentation g := by
  rw [HasRingHomProperty.iff_exists_appLE
    (P := @LocallyOfFinitePresentation)
    ((RingHom.finitePresentation_stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.finitePresentation_holdsForLocalizationAway).left)]
  intro y
  obtain ⟨W, V, hyV, e⟩ := exists_affineOpens_le_preimage g y
  refine ⟨W, V, hyV, e, ?_⟩
  obtain ⟨n, U, hU, T, t, hcover, hcomp, hff, hfp⟩ :=
    exists_standardFppfCovering_through_affineOpens f h V
  have _ : IsAffine (W.1.toScheme) := W.2
  have _ : IsAffine (V.1.toScheme) := V.2
  have _ : ∀ i, IsAffine ((U i).1.toScheme) := fun i => (U i).2
  have _ : ∀ i, IsAffine (T i) := hcover.affine_source
  have eU (i : Fin n) : (U i).1 ≤ (f ≫ g) ⁻¹ᵁ W.1 := fun _ hx ↦ e (hU i hx)
  let cToA := RingHom.pi fun i ↦ ((f ≫ g).resLE W.1 (U i).1 (eU i)).appTop.hom
  let cToB := (g.resLE W.1 V.1 e).appTop.hom
  let bToA := RingHom.pi fun i ↦ (f.resLE V.1 (U i).1 (hU i)).appTop.hom
  let aToB' := RingHom.pi fun i ↦ (t i).appTop.hom.comp (Pi.evalRingHom _ i)
  let bToB' := RingHom.pi fun i ↦ (t i ≫ f.resLE V.1 (U i).1 (hU i)).appTop.hom
  have hCA : cToA.FinitePresentation :=
    RingHom.FinitePresentation.pi _ fun _ ↦ Scheme.Hom.finitePresentation_appTop _
  have hCAeq : cToA = bToA.comp cToB := by
    ext x i
    exact resLE_comp_appTop_hom_apply f g (hU i) e (eU i) x
  have hBAft : bToA.FiniteType := RingHom.FiniteType.of_comp_finiteType
    (RingHom.FiniteType.of_finitePresentation (hCAeq ▸ hCA))
  have hBB'eq : bToB' = aToB'.comp bToA := by
    ext x i
    show (t i ≫ f.resLE V.1 (U i).1 (hU i)).appTop.hom x =
      (t i).appTop.hom ((f.resLE V.1 (U i).1 (hU i)).appTop.hom x)
    exact RingHom.congr_fun (hcomp i) x
  refine (RingHom.finitePresentation_respectsIso.arrow_mk_iso_iff
    (arrowResLEAppIso g W.1 V.1 e)).mp
    (RingHom.finitePresentation_of_comp_of_faithfullyFlat cToB bToB' ?_ hff hfp)
  rw [hBB'eq, RingHom.comp_assoc, ← hCAeq]
  exact (RingHom.FinitePresentation.of_comp_finiteType bToA (hBB'eq ▸ hfp) hBAft).comp hCA

end AlgebraicGeometry
