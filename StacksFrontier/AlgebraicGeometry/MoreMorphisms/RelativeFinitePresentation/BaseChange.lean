module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.FinitePresentationRel.BaseChange
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.AffineSections
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeFinitePresentation.AffinePullback
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.RelativeFinitePresentation.Affine
public import StacksFrontier.AlgebraicGeometry.Size.Pullback

/-!
# Base change of relative finite presentation

Let `f : X ⟶ S` be locally of finite type, let `M` be a quasi-coherent module on `X` that is
finitely presented relative to `S`, and let `g : S' ⟶ S` be arbitrary. Then the pullback of `M`
to the fibre product `X ×_S S'` is finitely presented relative to `S'`.

The affine step is the base-change theorem for relatively finitely presented modules: if
`M` is finitely presented relative to `R` over `B`, then `R' ⊗_R M` is finitely presented
relative to `R'` over `B ⊗_R R'`. The scheme statement follows by covering the fibre product
with the affine opens `p₁⁻¹ U ⊓ p₂⁻¹ V'` cut out by compatible affine opens `U` of `X` and `V'`
of `S'`, whose rings of functions form the pushout of the corresponding rings of functions.

## Main results

* `AlgebraicGeometry.isFinitelyPresentedRelative_baseChange`: relative finite presentation is
  stable under arbitrary base change.

## Implementation notes

The affine opens of the fibre product used as charts are the intersections
`pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V'`; their affineness is
`AlgebraicGeometry.isAffineOpen_inf_preimage`. That the corresponding square of rings of
functions is a pushout is read off the pullback square of the restricted morphisms through
`AlgebraicGeometry.isPushout_appTop_of_isPullback`, after replacing global sections of the open
subschemes by sections over the opens with `Scheme.Opens.topIso`. The affine computation itself
is `AlgebraicGeometry.finitePresentationRel_pullback_specMap_of_baseChange`.

## References

* [Stacks Project, Tag 09TA](https://stacks.math.columbia.edu/tag/09TA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- Taking sections over `⊤` of the restriction of a morphism to `U ≤ f ⁻¹ᵁ V` agrees, through
the identifications of global sections of the open subschemes with sections over the opens, with
`Scheme.Hom.appLE`. -/
private theorem appTop_resLE_topIso {Y X : Scheme.{u}} (f : X ⟶ Y)
    (V : Y.Opens) (U : X.Opens) (h : U ≤ f ⁻¹ᵁ V) :
    (f.resLE V U h).appTop ≫ U.topIso.hom = V.topIso.hom ≫ f.appLE V U h := by
  rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, Category.assoc, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- If `A` is the pushout of `B` and `R'` over `R` and `N` is finitely presented relative to `R`
over `B`, then `A ⊗[B] N` is finitely presented relative to `R'` over `A`. -/
private theorem finitePresentationRel_tensor_of_isPushout {R B R' A : Type u} [CommRing R]
    [CommRing B] [CommRing R'] [CommRing A] [Algebra R B] [Algebra R R'] [Algebra R A]
    [Algebra B A] [Algebra R' A] [IsScalarTower R B A] [IsScalarTower R R' A]
    [Algebra.IsPushout R B R' A]
    [Algebra.FiniteType R B] (N : Type u) [AddCommGroup N] [Module B N]
    (hN : Module.FinitePresentationRel R B N) :
    Module.FinitePresentationRel R' A (TensorProduct B A N) := by
  let T := TensorProduct R B R'
  let : Algebra R' T := Algebra.TensorProduct.rightAlgebra
  let : Algebra B T := Algebra.TensorProduct.leftAlgebra
  let ePush : T ≃ₐ[B] A := Algebra.IsPushout.equiv R B R' A
  let ePushR' : T ≃ₐ[R'] A :=
    { toRingEquiv := ePush.toRingEquiv
      commutes' := by
        intro r
        change ePush (1 ⊗ₜ[R] r) = algebraMap R' A r
        rw [Algebra.IsPushout.equiv_tmul]
        simp }
  let eModule := TensorProduct.congr ePush.toLinearEquiv (LinearEquiv.refl B N)
  have heModule : ∀ (a : T) (x : TensorProduct B T N),
      eModule (a • x) = ePushR' a • eModule x := by
    intro a x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp [smul_add, hx, hy]
    | tmul b n => simp [eModule, ePushR', TensorProduct.smul_tmul']
  exact Module.FinitePresentationRel.of_semilinearEquiv ePushR' eModule.toAddEquiv heModule
    (finitePresentation_relative_baseChange R B R' N hN).2

/-- Sections over an affine open `W ≤ p ⁻¹ᵁ U` of the pullback of a quasi-coherent module `M`
are finitely presented relative to `R` once the sections of the pullback of `M|_U` along
`Spec Γ(Y, W) ⟶ Spec Γ(X, U)` are. -/
private theorem finitePresentationRel_sections_pullback {Y X : Scheme.{u}} (p : Y ⟶ X)
    (M : X.Modules) [M.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U)
    {W : Y.Opens} (hW : IsAffineOpen W) (hWU : W ≤ p ⁻¹ᵁ U)
    (R : Type u) [CommRing R] [Algebra R Γ(Y, W)]
    (h : Module.FinitePresentationRel R Γ(Y, W)
      ((moduleSpecΓFunctor (R := .of Γ(Y, W))).obj
        ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (p.appLE U W hWU).hom))).obj
          ((Scheme.Modules.restrictFunctor hU.fromSpec).obj M)))) :
    Module.FinitePresentationRel R Γ(Y, W) Γ((Scheme.Modules.pullback p).obj M, W) := by
  let H := (Scheme.Modules.pullback p).obj M
  have : H.IsQuasicoherent := Stacks.Modules.isQuasicoherent_pullback _ M ‹M.IsQuasicoherent›
  let k := Spec.map (CommRingCat.ofHom (p.appLE U W hWU).hom)
  have hmaps : k ≫ hU.fromSpec = hW.fromSpec ≫ p :=
    IsAffineOpen.SpecMap_appLE_fromSpec p hU hW hWU
  let eSource :
      (Scheme.Modules.pullback k).obj ((Scheme.Modules.restrictFunctor hU.fromSpec).obj M) ≅
      (Scheme.Modules.pullback (k ≫ hU.fromSpec)).obj M :=
    ((Scheme.Modules.pullback k).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback hU.fromSpec).app M)) ≪≫
      (Scheme.Modules.pullbackComp k hU.fromSpec).app M
  let eTarget : (Scheme.Modules.restrictFunctor hW.fromSpec).obj H ≅
      (Scheme.Modules.pullback (hW.fromSpec ≫ p)).obj M :=
    ((Scheme.Modules.restrictFunctorIsoPullback hW.fromSpec).app H) ≪≫
      (Scheme.Modules.pullbackComp hW.fromSpec p).app M
  let eChart : ((moduleSpecΓFunctor (R := .of Γ(Y, W))).obj
      ((Scheme.Modules.restrictFunctor hW.fromSpec).obj H)) ≃ₗ[Γ(Y, W)] Γ(H, W) :=
    affineSectionsLinearEquiv H hW
  exact Module.FinitePresentationRel.of_linearEquiv
    (((moduleSpecΓFunctor (R := .of Γ(Y, W))).mapIso
      (eSource ≪≫ (Scheme.Modules.pullbackCongr hmaps).app M ≪≫ eTarget.symm)).toLinearEquiv.trans
        eChart) h

/-- The chart `p₁⁻¹ U ⊓ p₂⁻¹ V'` of the fibre product is affine for affine opens `U ≤ f⁻¹ V` and
`V' ≤ g⁻¹ V` with `V` affine. -/
private theorem isAffineOpen_inf_preimage_of_le_preimage_of_isAffineOpen
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) {V : S.Opens} (hV : IsAffineOpen V)
    {U : X.Opens} (hU : IsAffineOpen U) (hUV : U ≤ f ⁻¹ᵁ V)
    {V' : S'.Opens} (hV' : IsAffineOpen V') (hV'V : V' ≤ g ⁻¹ᵁ V) :
    IsAffineOpen (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V') := by
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  have : IsAffine V'.toScheme := hV'
  exact isAffineOpen_inf_preimage f g hUV hV'V

/-- Base change of relative finite presentation on one chart: over compatible affine opens `V`
of `S`, `U` of `X` and `V'` of `S'`, the sections of the pullback of `M` over the affine open
`p₁⁻¹ U ⊓ p₂⁻¹ V'` of the fibre product are finitely presented relative to `Γ(S', V')`. -/
private theorem finitePresentationRel_pullback_affine
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [LocallyOfFiniteType f]
    (M : X.Modules) [M.IsQuasicoherent]
    (V : S.Opens) (hV : IsAffineOpen V)
    (U : X.Opens) (hU : IsAffineOpen U) (hUV : U ≤ f ⁻¹ᵁ V)
    (V' : S'.Opens) (hV' : IsAffineOpen V') (hV'V : V' ≤ g ⁻¹ᵁ V)
    (hM : letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
      Module.FinitePresentationRel Γ(S, V) Γ(X, U) Γ(M, U)) :
    let W := pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V'
    letI : Algebra Γ(S', V') Γ(pullback f g, W) :=
      ((pullback.snd f g).appLE V' W (by simp [W])).hom.toAlgebra
    Module.FinitePresentationRel Γ(S', V') Γ(pullback f g, W)
      Γ(((Scheme.Modules.pullback (pullback.fst f g)).obj M), W) := by
  classical
  let : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  let : Algebra Γ(S, V) Γ(S', V') := (g.appLE V V' hV'V).hom.toAlgebra
  let R := Γ(S, V)
  let B := Γ(X, U)
  let R' := Γ(S', V')
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  have : IsAffine V'.toScheme := hV'
  let W := pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V'
  have hW : IsAffineOpen W :=
    isAffineOpen_inf_preimage_of_le_preimage_of_isAffineOpen f g hV hU hUV hV' hV'V
  have hWU : W ≤ pullback.fst f g ⁻¹ᵁ U := inf_le_left
  have hWV : W ≤ pullback.snd f g ⁻¹ᵁ V' := inf_le_right
  let A := Γ(pullback f g, W)
  let : Algebra R' Γ(pullback f g, W) :=
    ((pullback.snd f g).appLE V' W hWV).hom.toAlgebra
  let : Algebra B A := ((pullback.fst f g).appLE U W hWU).hom.toAlgebra
  have : Algebra.FiniteType R B := f.finiteType_appLE hV hU hUV
  let GS : (Spec (.of B)).Modules := (Scheme.Modules.restrictFunctor hU.fromSpec).obj M
  have : GS.IsQuasicoherent := Scheme.Modules.isQuasicoherent_restrictFunctor hU.fromSpec M
  let N : ModuleCat B := ModuleCat.of B Γ(M, U)
  let eGS : (moduleSpecΓFunctor (R := .of B)).obj GS ≃ₗ[B] N := by
    change Γ(M.restrict hU.fromSpec, ⊤) ≃ₗ[B] Γ(M, U)
    exact affineSectionsLinearEquiv M hU
  let eSheaf : (tilde.functor (R := .of B)).obj N ≅ GS :=
    (tilde.functor (R := .of B)).mapIso eGS.symm.toModuleIso ≪≫
      @asIso _ _ _ _ (Scheme.Modules.fromTildeΓ (R := .of B) GS)
        (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent GS)
  have hN : Module.FinitePresentationRel R B N := hM
  let fU := f.resLE V U hUV
  let gV := g.resLE V V' hV'V
  let fW := (pullback.fst f g).resLE U W hWU
  let gW := (pullback.snd f g).resLE V' W hWV
  have hres : IsPullback fW gW fU gV :=
    Scheme.Hom.isPullback_resLE (IsPullback.of_hasPullback f g) hV'V hUV (UY := W) rfl
  have hpush1 := (isPushout_appTop_of_isPullback hres).of_iso V.topIso U.topIso V'.topIso W.topIso
    (appTop_resLE_topIso f V U hUV) (appTop_resLE_topIso g V V' hV'V)
    (appTop_resLE_topIso (pullback.fst f g) U W hWU)
    (appTop_resLE_topIso (pullback.snd f g) V' W hWV)
  let : Algebra R A := (algebraMap B A).comp (algebraMap R B) |>.toAlgebra
  have : IsScalarTower R B A := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  have : IsScalarTower R R' A := IsScalarTower.of_algebraMap_eq fun r => by
    simpa [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom] using
      congrArg (fun k : CommRingCat.Hom R A => k.hom r) hpush1.w
  have : Algebra.IsPushout R B R' A := by
    apply CommRingCat.isPushout_iff_isPushout.mp
    simpa [R, B, R', A, RingHom.algebraMap_toAlgebra] using hpush1
  exact finitePresentationRel_sections_pullback (pullback.fst f g) M hU hW hWU R'
    (finitePresentationRel_pullback_specMap_of_baseChange GS N eSheaf
      (finitePresentationRel_tensor_of_isPushout N hN))

/-- **Stacks Project, Tag 09TA.** Relative finite presentation of a quasi-coherent module is
stable under arbitrary base change: if `M` on `X` is finitely presented relative to `f : X ⟶ S`,
then its pullback to `X ×_S S'` is finitely presented relative to `S'`. -/
@[stacks 09TA]
theorem isFinitelyPresentedRelative_baseChange
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [LocallyOfFiniteType f] (M : X.Modules) [M.IsQuasicoherent]
    (hM : IsFinitelyPresentedRelative f M) :
    IsFinitelyPresentedRelative (pullback.snd f g)
      ((Scheme.Modules.pullback (pullback.fst f g)).obj M) := by
  classical
  obtain ⟨J, V, hVcover, hVaff, hMcharts⟩ := hM
  choose I U hUcover hUaff hUrel using hMcharts
  let J' := Σ j : J, {V' : S'.affineOpens // (V' : S'.Opens) ≤ g ⁻¹ᵁ V j}
  let V'out : J' → S'.Opens := fun j => j.2.1.1
  refine ⟨J', V'out, ?_, fun j => j.2.1.2, ?_⟩
  · apply le_antisymm le_top
    intro y _
    have hycover : g.base y ∈ ⨆ j, V j := by
      rw [hVcover]
      simp
    obtain ⟨j, hyj⟩ := TopologicalSpace.Opens.mem_iSup.mp hycover
    obtain ⟨Vopen, hV'aff, hyV', hV'V⟩ := exists_isAffineOpen_mem_and_subset
      (X := S') (x := y) (U := g ⁻¹ᵁ V j) (by simpa using hyj)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨j, ⟨⟨Vopen, hV'aff⟩, fun _ hx => hV'V hx⟩⟩, hyV'⟩
  · rintro ⟨j0, ⟨⟨Vopen, hVopen⟩, hV'V⟩⟩
    have hUV : ∀ i, U j0 i ≤ f ⁻¹ᵁ V j0 := fun i => (le_iSup (U j0) i).trans (hUcover j0).le
    let Uout : I j0 → (pullback f g).Opens := fun i =>
      pullback.fst f g ⁻¹ᵁ U j0 i ⊓ pullback.snd f g ⁻¹ᵁ Vopen
    have hcover : (⨆ i, Uout i) = (pullback.snd f g) ⁻¹ᵁ Vopen := by
      apply le_antisymm
      · exact iSup_le fun _ _ hx => hx.2
      · intro z hz
        have hxV : (pullback.fst f g).base z ∈ f ⁻¹ᵁ V j0 := by
          have hcond := congrArg (fun k : pullback f g ⟶ S => k.base z)
            (pullback.condition (f := f) (g := g))
          change f.base ((pullback.fst f g).base z) =
            g.base ((pullback.snd f g).base z) at hcond
          change f.base ((pullback.fst f g).base z) ∈ V j0
          rw [hcond]
          exact hV'V hz
        obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp ((hUcover j0).ge hxV)
        exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi, hz⟩
    refine ⟨I j0, Uout, ?_, ?_, ?_⟩
    · simpa [V'out] using hcover
    · exact fun i => isAffineOpen_inf_preimage_of_le_preimage_of_isAffineOpen f g (hVaff j0)
        (hUaff j0 i) (hUV i) hVopen hV'V
    · exact fun i => finitePresentationRel_pullback_affine f g M (V j0) (hVaff j0)
        (U j0 i) (hUaff j0 i) (hUV i) Vopen hVopen hV'V (hUrel j0 i)

end AlgebraicGeometry
