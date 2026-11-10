module

public import Mathlib.AlgebraicGeometry.Fiber
public import StacksFrontier.AlgebraicGeometry.Pullback.AffineOpens
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.PullbackStalk
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.SupportClosure
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Fibre
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finite
public import StacksFrontier.AlgebraicGeometry.CoherentKernel.Basic
public import StacksFrontier.Topology.Sheaves.Modules.FiniteType

/-!
# Sections modulo the ideal of a point of the base, read on the fibre

Let `S` be affine, `s ∈ S` a point such that `Γ(S, 𝒪_S) → κ(s)` is surjective with kernel `J`,
`f : X ⟶ S` a morphism and `F` a quasi-coherent `𝒪_X`-module. For an affine open `U ⊆ X`, the
quotient `Γ(U, F)/J Γ(U, F)` is the module of sections of the restriction of `F` to the fibre
`X_s` over `U ∩ X_s`, by the base change of sections over affine opens. Over a locally Noetherian
fibre this turns injectivity questions modulo `J` into questions about associated points.

## Main results

* `AlgebraicGeometry.mem_smul_top_iff_pullbackSection_fiberι_eq_zero`: a section lies in
  `J · Γ(U, F)` exactly when its pullback to the fibre vanishes.
* `AlgebraicGeometry.mem_smul_top_of_map_mem_smul_top`: for `f` locally of finite type and
  affine opens `x ∈ W ⊆ U` such that every associated point of `F|_{X_s}` in `U` generalizes `x`,
  restriction `Γ(U, F)/J → Γ(W, F)/J` is injective.
* `AlgebraicGeometry.exists_opens_associatedPoints_fiber_specializes`: for `f` quasi-compact and
  locally of finite type and `F` of finite type, there is an open neighbourhood of `x` in which
  every associated point of `F|_{X_s}` generalizes `x`.

## References

* [Stacks Project, Tag 05U7](https://stacks.math.columbia.edu/tag/05U7)
* [Stacks Project, Tag 05AF](https://stacks.math.columbia.edu/tag/05AF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TensorProduct
open scoped ChangeOfRings

universe u

namespace AlgebraicGeometry

/-- **The kernel of a base change along a pushout of a surjection.** Let `R → T` be surjective with
kernel `J`, let `C` be the pushout of `T` and an `R`-algebra `B`, and let `E` be a `B`-module.
Then `1 ⊗ e` vanishes in `C ⊗_B E` exactly when `e ∈ J • E`. -/
theorem one_tmul_eq_zero_iff_mem_smul_top_of_isPushout {R T B C E : Type*} [CommRing R]
    [CommRing T] [CommRing B] [CommRing C] [Algebra R T] [Algebra R B] [Algebra B C]
    [Algebra T C] [Algebra R C] [IsScalarTower R B C] [IsScalarTower R T C]
    [Algebra.IsPushout R T B C] (hsurj : Function.Surjective (algebraMap R T))
    [AddCommGroup E] [Module B E] [Module R E] [IsScalarTower R B E] (e : E) :
    (1 : C) ⊗ₜ[B] e = 0 ↔ e ∈ RingHom.ker (algebraMap R T) • (⊤ : Submodule R E) := by
  have h1 : (1 : C) ⊗ₜ[B] e = 0 ↔ (1 : T) ⊗ₜ[R] e = 0 := by
    rw [← (Algebra.IsPushout.cancelBaseChange R T B C E).map_eq_zero_iff,
      Algebra.IsPushout.cancelBaseChange_tmul]
  let eT : (R ⧸ RingHom.ker (algebraMap R T)) ≃ₐ[R] T :=
    Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R T) hsurj
  have h2 : (1 : T) ⊗ₜ[R] e = 0 ↔ (1 : R ⧸ RingHom.ker (algebraMap R T)) ⊗ₜ[R] e = 0 := by
    rw [← (TensorProduct.congr eT.toLinearEquiv (LinearEquiv.refl R E)).map_eq_zero_iff,
      TensorProduct.congr_tmul, AlgEquiv.toLinearEquiv_apply, map_one, LinearEquiv.refl_apply]
  rw [h1, h2, ← (TensorProduct.quotTensorEquivQuotSMul E _).map_eq_zero_iff,
    TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero]

/-- `AlgebraicGeometry.one_tmul_eq_zero_iff_mem_smul_top_of_isPushout` for an isomorphism out of
an extension of scalars, whose module structure on `C ⊗_B E` is only definitionally the one
coming from the algebra structure. -/
theorem extendScalarsIso_one_tmul_eq_zero_iff {R T B C E N : Type u} [CommRing R]
    [CommRing T] [CommRing B] [CommRing C] [Algebra R T] [Algebra R B] [inst : Algebra B C]
    [Algebra T C] [Algebra R C] [IsScalarTower R B C] [IsScalarTower R T C]
    [Algebra.IsPushout R T B C] (hsurj : Function.Surjective (algebraMap R T))
    [AddCommGroup E] [Module B E] [Module R E] [IsScalarTower R B E] [AddCommGroup N]
    [Module C N] (f : B →+* C) (hf : inst = f.toAlgebra)
    (e : (ModuleCat.extendScalars f).obj (ModuleCat.of B E) ≅ ModuleCat.of C N) (x : E) :
    e.hom ((1 : C) ⊗ₜ[B, f] x) = 0 ↔ x ∈ RingHom.ker (algebraMap R T) • (⊤ : Submodule R E) := by
  subst hf
  let : Algebra B C := f.toAlgebra
  rw [← one_tmul_eq_zero_iff_mem_smul_top_of_isPushout (B := B) (C := C) hsurj x]
  exact e.toLinearEquiv.map_eq_zero_iff

/-- **Sections vanishing on the fibre.** Let `S` be affine, let `s ∈ S` be a point such that
`Γ(S, 𝒪_S) → κ(s)` is surjective with kernel `J`, let `f : X ⟶ S` be a morphism and let `F` be a
quasi-coherent `𝒪_X`-module. For an affine open `U ⊆ X`, a section `e` of `F` over `U` lies in
`J · Γ(F, U)` exactly when its pullback to the fibre `X_s` vanishes. -/
theorem mem_smul_top_iff_pullbackSection_fiberι_eq_zero {X S : Scheme.{u}} [IsAffine S]
    (f : X ⟶ S) (s : S) (hsurj : Function.Surjective (S.fromSpecResidueField s).appTop.hom)
    (F : X.Modules) [F.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U) (e : Γ(F, U)) :
    letI : Module Γ(S, ⊤) Γ(F, U) := Module.compHom _ (f.appLE ⊤ U (by simp)).hom
    e ∈ RingHom.ker (S.fromSpecResidueField s).appTop.hom • (⊤ : Submodule Γ(S, ⊤) Γ(F, U)) ↔
      Scheme.Modules.pullbackSection (f.fiberι s) F U (f.fiberι s ⁻¹ᵁ U) le_rfl e = 0 := by
  set g := S.fromSpecResidueField s with hg
  set ι := f.fiberι s with hι
  set p := f.fiberToSpecResidueField s with hp
  have H : IsPullback ι p f g := IsPullback.of_hasPullback f g
  have hUle : U ≤ f ⁻¹ᵁ ⊤ := le_top.trans (by simp)
  have hTle : (⊤ : (Spec (S.residueField s)).Opens) ≤ g ⁻¹ᵁ ⊤ := le_top.trans (by simp)
  have hU' : ι ⁻¹ᵁ U = ι ⁻¹ᵁ U ⊓ p ⁻¹ᵁ ⊤ := by simp
  have hUsaff : IsAffineOpen (ι ⁻¹ᵁ U) :=
    IsAffineOpen.inf_preimage_of_isPullback H (isAffineOpen_top S) hU hUle (isAffineOpen_top _)
      hTle hU'
  let : Algebra Γ(S, ⊤) Γ(X, U) := (f.appLE ⊤ U hUle).hom.toAlgebra
  let : Algebra Γ(S, ⊤) Γ(Spec (S.residueField s), ⊤) := (g.appLE ⊤ ⊤ hTle).hom.toAlgebra
  let : Algebra Γ(X, U) Γ(f.fiber s, ι ⁻¹ᵁ U) :=
    (ι.appLE U (ι ⁻¹ᵁ U) (hU'.le.trans inf_le_left)).hom.toAlgebra
  let : Algebra Γ(Spec (S.residueField s), ⊤) Γ(f.fiber s, ι ⁻¹ᵁ U) :=
    (p.appLE ⊤ (ι ⁻¹ᵁ U) (hU'.le.trans inf_le_right)).hom.toAlgebra
  let : Algebra Γ(S, ⊤) Γ(f.fiber s, ι ⁻¹ᵁ U) :=
    (f.appLE ⊤ U hUle ≫ ι.appLE U (ι ⁻¹ᵁ U) (hU'.le.trans inf_le_left)).hom.toAlgebra
  have hw := (isPushout_appLE_of_isPullback H (isAffineOpen_top S) hU hUle (isAffineOpen_top _)
    hTle hU').w
  have : IsScalarTower Γ(S, ⊤) Γ(X, U) Γ(f.fiber s, ι ⁻¹ᵁ U) := .of_algebraMap_eq' rfl
  have : IsScalarTower Γ(S, ⊤) Γ(Spec (S.residueField s), ⊤) Γ(f.fiber s, ι ⁻¹ᵁ U) :=
    .of_algebraMap_eq' congr($(hw).hom)
  have : Algebra.IsPushout Γ(S, ⊤) Γ(Spec (S.residueField s), ⊤) Γ(X, U)
      Γ(f.fiber s, ι ⁻¹ᵁ U) :=
    algebra_isPushout_appLE_of_isPullback H (isAffineOpen_top S) hU hUle (isAffineOpen_top _)
      hTle hU' (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  let : Module Γ(S, ⊤) Γ(F, U) := Module.compHom _ (f.appLE ⊤ U hUle).hom
  have : IsScalarTower Γ(S, ⊤) Γ(X, U) Γ(F, U) :=
    ⟨fun a a' m => mul_smul ((f.appLE ⊤ U hUle).hom a) a' m⟩
  have halg : algebraMap Γ(S, ⊤) Γ(Spec (S.residueField s), ⊤) = g.appTop.hom :=
    congrArg CommRingCat.Hom.hom (Scheme.Hom.appLE_eq_app g)
  have hsurj' : Function.Surjective (algebraMap Γ(S, ⊤) Γ(Spec (S.residueField s), ⊤)) := by
    rwa [halg]
  change e ∈ RingHom.ker g.appTop.hom • (⊤ : Submodule Γ(S, ⊤) Γ(F, U)) ↔ _
  rw [← halg, ← affinePullbackSectionsBaseChangeIso_one_tmul ι F hU hUsaff le_rfl e]
  exact (extendScalarsIso_one_tmul_eq_zero_iff (R := Γ(S, ⊤))
    (T := Γ(Spec (S.residueField s), ⊤)) (B := Γ(X, U)) (C := Γ(f.fiber s, ι ⁻¹ᵁ U))
    (E := Γ(F, U)) (N := Γ((Scheme.Modules.pullback ι).obj F, ι ⁻¹ᵁ U)) hsurj' _ rfl
    (affinePullbackSectionsBaseChangeIso ι F hU hUsaff le_rfl) e).symm

/-- Pulling a section back commutes with restriction. -/
theorem Scheme.Modules.pullbackSection_map {X Y : Scheme.{u}} (f : Y ⟶ X) (F : X.Modules)
    {U U' : X.Opens} (hU' : U' ≤ U) {V V' : Y.Opens} (h : V ≤ f ⁻¹ᵁ U) (h' : V' ≤ f ⁻¹ᵁ U')
    (hV : V' ≤ V) (a : Γ(F, U)) :
    ((Scheme.Modules.pullback f).obj F).presheaf.map (homOfLE hV).op
        (Scheme.Modules.pullbackSection f F U V h a) =
      Scheme.Modules.pullbackSection f F U' V' h' (F.presheaf.map (homOfLE hU').op a) := by
  change ((Scheme.Modules.pullback f).obj F).val.map (homOfLE hV).op
      (((Scheme.Modules.pullback f).obj F).val.map (homOfLE h).op _) =
    ((Scheme.Modules.pullback f).obj F).val.map (homOfLE h').op
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F).val.app (Opposite.op U')
        (F.val.map (homOfLE hU').op a))
  have hn : ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F).val.app
        (Opposite.op U') (F.val.map (homOfLE hU').op a) =
      ((Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj F)).val.map
        (homOfLE hU').op
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F).val.app (Opposite.op U) a) :=
    PresheafOfModules.naturality_apply _ _ a
  rw [hn]
  change _ = ((Scheme.Modules.pullback f).obj F).val.map (homOfLE h').op
    (((Scheme.Modules.pullback f).obj F).val.map (homOfLE (f.preimage_mono hU')).op _)
  set y := ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F).val.app (Opposite.op U) a
  change (((Scheme.Modules.pullback f).obj F).presheaf.map (homOfLE h).op ≫
      ((Scheme.Modules.pullback f).obj F).presheaf.map (homOfLE hV).op) y =
    (((Scheme.Modules.pullback f).obj F).presheaf.map (homOfLE (f.preimage_mono hU')).op ≫
      ((Scheme.Modules.pullback f).obj F).presheaf.map (homOfLE h').op) y
  rw [← Functor.map_comp, ← Functor.map_comp]
  rfl

/-- **Injectivity of restriction modulo the base ideal.** Let `S` be affine, let `s ∈ S` be a point
such that `Γ(S, 𝒪_S) → κ(s)` is surjective with kernel `J`, let `f : X ⟶ S` be locally of finite
type, let `F` be a quasi-coherent `𝒪_X`-module, and let `x ∈ X` lie over `s`. Let `W ⊆ U` be affine
opens containing `x` such that every associated point of the restriction of `F` to the fibre `X_s`
lying in `U` generalizes `x`. Then a section of `F` over `U` whose restriction to `W` lies in
`J · Γ(F, W)` already lies in `J · Γ(F, U)`. -/
theorem mem_smul_top_of_map_mem_smul_top {X S : Scheme.{u}} [IsAffine S] (f : X ⟶ S)
    [LocallyOfFiniteType f] (x : X)
    (hsurj : Function.Surjective (S.fromSpecResidueField (f x)).appTop.hom)
    (F : X.Modules) [F.IsQuasicoherent] {U W : X.Opens} (hU : IsAffineOpen U)
    (hW : IsAffineOpen W) (hWU : W ≤ U) (hxW : x ∈ W)
    (hAss : ∀ z : f.fiber (f x), z ∈ Stacks.Divisors.associatedPoints
      ((Scheme.Modules.pullback (f.fiberι (f x))).obj F) → f.fiberι (f x) z ∈ U →
        f.fiberι (f x) z ⤳ x) (e : Γ(F, U)) :
    letI : Module Γ(S, ⊤) Γ(F, U) := Module.compHom _ (f.appLE ⊤ U (by simp)).hom
    letI : Module Γ(S, ⊤) Γ(F, W) := Module.compHom _ (f.appLE ⊤ W (by simp)).hom
    F.presheaf.map (homOfLE hWU).op e ∈
        RingHom.ker (S.fromSpecResidueField (f x)).appTop.hom •
          (⊤ : Submodule Γ(S, ⊤) Γ(F, W)) →
      e ∈ RingHom.ker (S.fromSpecResidueField (f x)).appTop.hom •
        (⊤ : Submodule Γ(S, ⊤) Γ(F, U)) := by
  intro he
  rw [mem_smul_top_iff_pullbackSection_fiberι_eq_zero f (f x) hsurj F hU e]
  rw [mem_smul_top_iff_pullbackSection_fiberι_eq_zero f (f x) hsurj F hW] at he
  set ι := f.fiberι (f x) with hι
  set Fs := (Scheme.Modules.pullback ι).obj F with hFs
  have : IsLocallyNoetherian (f.fiber (f x)) :=
    isLocallyNoetherian_fiber_of_locallyOfFiniteType f _
  have : Fs.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback _ F
  have hιxs : ι (f.asFiber x) = x := f.fiberι_asFiber x
  have hWU' : ι ⁻¹ᵁ W ≤ ι ⁻¹ᵁ U := fun z hz => hWU hz
  have hinj := restriction_injective_of_associatedPoints_inter_subset Fs hWU' (by
    rintro z ⟨hzass, hzU⟩
    have hspec : z ⤳ f.asFiber x := by
      rw [← ι.isEmbedding.specializes_iff, hιxs]
      exact hAss z hzass hzU
    have hxs : f.asFiber x ∈ ι ⁻¹ᵁ W := by
      change ι (f.asFiber x) ∈ W
      rwa [hιxs]
    exact hspec.mem_open (ι ⁻¹ᵁ W).isOpen hxs)
  apply hinj
  rw [Scheme.Modules.pullbackSection_map ι F hWU le_rfl le_rfl hWU', he]
  exact (map_zero _).symm

/-- **Shrinking around a point so that the fibre has no associated point not generalizing it.**
Let `f : X ⟶ S` be quasi-compact and locally of finite type, let `F` be a quasi-coherent
`𝒪_X`-module of finite type and let `x ∈ X`. There is an open neighbourhood `X₀` of `x` such that
every associated point of the restriction of `F` to the fibre of `f` through `x` which lies in
`X₀` generalizes `x`. -/
theorem exists_opens_associatedPoints_fiber_specializes {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [QuasiCompact f] (F : X.Modules) [F.IsQuasicoherent]
    [F.IsFiniteType] (x : X) :
    ∃ X₀ : X.Opens, x ∈ X₀ ∧ ∀ z : f.fiber (f x), z ∈ Stacks.Divisors.associatedPoints
      ((Scheme.Modules.pullback (f.fiberι (f x))).obj F) → f.fiberι (f x) z ∈ X₀ →
        f.fiberι (f x) z ⤳ x := by
  classical
  set ι := f.fiberι (f x) with hι
  set Fs := (Scheme.Modules.pullback ι).obj F with hFs
  have : IsLocallyNoetherian (f.fiber (f x)) :=
    isLocallyNoetherian_fiber_of_locallyOfFiniteType f _
  have : Fs.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback _ F
  have : Fs.IsFiniteType := SheafOfModules.pullback_isFiniteType ι.toLRSHom.toShHom F
  have : Fs.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isQuasicoherent_isFiniteType Fs
  have hfin : (Stacks.Divisors.associatedPoints Fs).Finite := by
    simpa using associatedPoints_inter_finite Fs ⊤ isCompact_univ
  set E : Set X := ι '' {z | z ∈ Stacks.Divisors.associatedPoints Fs ∧ ¬ ι z ⤳ x} with hE
  have hEfin : E.Finite := (hfin.subset fun z hz => hz.1).image _
  refine ⟨⟨(closure E)ᶜ, isClosed_closure.isOpen_compl⟩, ?_, ?_⟩
  · change x ∉ closure E
    rw [← Set.biUnion_of_singleton E, hEfin.closure_biUnion]
    simp only [Set.mem_iUnion, not_exists]
    rintro _ ⟨z, hz, rfl⟩ hxz
    exact hz.2 (specializes_iff_mem_closure.mpr hxz)
  · intro z hz hzX₀
    by_contra hns
    exact hzX₀ (subset_closure ⟨z, ⟨hz, hns⟩, rfl⟩)

end AlgebraicGeometry
