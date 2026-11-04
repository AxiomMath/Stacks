module

public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.Coherence
public import StacksFrontier.AlgebraicGeometry.CoherentImage.Basic
public import StacksFrontier.AlgebraicGeometry.Etale.TopologicalProperties.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Pullback
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PowerAnnihilated
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.DeformationFiniteOrder.Etale
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Topological
public import StacksFrontier.AlgebraicGeometry.Scheme.IdealSheafComapMul

/-!
# Flat pullback is an equivalence on coherent adic systems

**Stacks 0EHQ.** Let `f : X ⟶ Y` be a morphism of Noetherian schemes, let `𝒥 ⊆ 𝒪_Y` be a
quasi-coherent sheaf of ideals cutting out the closed subscheme `Z ⊆ Y`, and let
`ℐ = f^{-1}𝒥 𝒪_X` cut out the scheme-theoretic inverse image `Z' = f^{-1}Z`. If `f` is flat and
the induced morphism `Z' ⟶ Z` is an isomorphism, then the pullback functor of Stacks 0887

`f^* : Coh(Y, 𝒥) ⟶ Coh(X, ℐ)`

is an equivalence.

The proof runs the source's argument in the opposite direction, through the *right* adjoint.
Write `Z_n ⊆ Y` and `Z'_n ⊆ X` for the `n`-th infinitesimal neighbourhoods, that is the closed
subschemes cut out by `𝒥 ⁿ` and `ℐ ⁿ`. Since inverse image commutes with powers of ideal sheaves
(`Stacks.IdealSheaf.comap_pow`) one has `Z'_n = f^{-1}Z_n`, and the inclusion `Z ⊆ Z_n` is a
finite-order thickening. A flat morphism whose base change along a finite-order thickening of the
target is an isomorphism is itself an isomorphism — this is the isomorphism case of Stacks 06AG,
obtained here from the étale and topological cases already available: an isomorphism is étale,
universally injective and surjective, all three properties deform, and an étale universally
injective morphism is an open immersion (Stacks 025G), hence an isomorphism once surjective. So
`Z'_n ⟶ Z_n` is an isomorphism for every `n`.

Consequently, for every `n`, direct image along `f` is an equivalence from the coherent
`𝒪_X`-modules annihilated by `ℐ ⁿ` onto the coherent `𝒪_Y`-modules annihilated by `𝒥 ⁿ`: both
categories are identified by Stacks 087T with the coherent modules on `Z'_n`, resp. `Z_n`, and
those two schemes agree. Taking the union over `n` gives an equivalence `f_*` on the
`ℐ`-power-torsion coherent modules.

Membership in `Coh(X, ℐ)` is then recast in a form that transports along that equivalence. The
quotient clause `F_{n+1} / ℐ ⁿ⁺¹F_{n+1} ≅ F_n` says exactly that precomposition with the
transition `F_{n+1} ⟶ F_n` is a bijection on maps into every coherent module annihilated by
`ℐ ⁿ⁺¹` (`Stacks.Coherent.isCoherentAdicSystem_iff_precomp_bijective`): the "only if" direction
is the universal property of the quotient, and the "if" direction produces the isomorphism from
the two factorisations. Both clauses of that reformulation are statements about annihilated
objects and maps between them, so termwise direct image lifts to a functor
`Coh(X, ℐ) ⟶ Coh(Y, 𝒥)` which is an equivalence. Finally `f^*` is left adjoint to it, and a left
adjoint of an equivalence is an equivalence.

## Main definitions

* `Stacks.Coherent.coherentAnnihilatedBy` — the coherent modules annihilated by `I ^ n`.
* `Stacks.Coherent.coherentIdealPowerTorsion` — the coherent modules annihilated by some power.
* `Stacks.Coherent.coherentIdealPowerTorsionPushforward` — direct image on those.
* `Stacks.Coherent.coherentAdicPushforward` — **the inverse equivalence
  `Coh(X, ℐ) ⟶ Coh(Y, 𝒥)`**, termwise direct image.

## Main results

* `Stacks.Coherent.isIso_of_flat_of_isIso_pullbackSnd` — the isomorphism case of Stacks 06AG.
* `Stacks.Coherent.isIso_subschemeMap_pow` — `Z'_n ⟶ Z_n` is an isomorphism.
* `Stacks.Coherent.pushforwardCoherentAnnihilatedEquivalence` — the levelwise equivalence.
* `Stacks.Coherent.isCoherentAdicSystem_iff_precomp_bijective` — the reformulation of
  membership in `Coh(X, ℐ)` that transports along an equivalence.
* `Stacks.Coherent.coherentAdicPushforward_isEquivalence` — termwise direct image is an
  equivalence.
* `Stacks.Coherent.coherentAdicPullback_isEquivalence` — **[Stacks, Tag 0EHQ].**

## Implementation notes

The hypothesis "the induced morphism `Z' ⟶ Z` is an isomorphism" is
`IsIso ((𝒥.comapIso f).hom ≫ pullback.snd f 𝒥.subschemeι)`: the second projection of the
cartesian square defining `f^{-1}Z`, transported along Mathlib's canonical identification
`Scheme.IdealSheafData.comapIso` of `(𝒥.comap f).subscheme` with that fibre product. By
`AlgebraicGeometry.Scheme.IdealSheafData.comapIso_hom_snd` this composite is
`Scheme.IdealSheafData.subschemeMap`, so the hypothesis is equally the statement that the
canonical morphism of subschemes is invertible.

Indices are shifted as everywhere in this directory: term `n` of a system represents the
source's `F_{n+1}` and is annihilated by `ℐ ⁿ⁺¹`.

## References

* [Stacks Project, Tag 0EHQ](https://stacks.math.columbia.edu/tag/0EHQ)
* [Stacks Project, Tag 0887](https://stacks.math.columbia.edu/tag/0887)
* [Stacks Project, Tag 087T](https://stacks.math.columbia.edu/tag/087T)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
* [Stacks Project, Tag 06AG](https://stacks.math.columbia.edu/tag/06AG)
* [Stacks Project, Tag 025G](https://stacks.math.columbia.edu/tag/025G)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Coherent

open Stacks.Algebraization Stacks.AlgebraicGeometry.Tag087TCoherentImage

/-! The zero morphism out of a sheaf of modules presented without `Scheme.Modules` is supplied by
the `local instance` of `CoherentAdicSystem.PullbackIdealPower`, reactivated here rather than
restated: instance search does not see through `AlgebraicGeometry.Scheme.Modules`, a semireducible
definition, to find the zero morphisms of `X.Modules` for a source presented as a bare
`SheafOfModules X.ringCatSheaf`. -/

attribute [local instance] Stacks.Algebraization.zeroHomOfSheafOfModules

/-! ### The isomorphism case of Stacks 06AG -/

/-- **A flat morphism whose base change along a finite-order thickening of the target is an
isomorphism is an isomorphism.** This is the isomorphism case of [Stacks, Tag 06AG], assembled
from the cases already available: being étale deforms along a cartesian finite-order deformation
(`Stacks.Thickenings.CartesianFiniteOrderDeformationDiagram.etale_iff`), surjectivity and
universal injectivity deform along a morphism of thickenings, and an étale universally injective
morphism is an open immersion ([Stacks, Tag 025G]), hence an isomorphism when surjective. -/
public theorem isIso_of_flat_of_isIso_pullbackSnd {X Y Z : Scheme.{u}} (f : X ⟶ Y) (i : Z ⟶ Y)
    [Flat f] (hi : Stacks.Thickenings.IsFiniteOrderThickening i)
    [IsIso (pullback.snd f i)] : IsIso f := by
  have _ : IsClosedImmersion i := hi.1
  have _ : Surjective i := ⟨hi.isThickening.2⟩
  have hiX : Stacks.Thickenings.IsThickening (pullback.fst f i) :=
    ⟨inferInstance, (inferInstance : Surjective (pullback.fst f i)).surj⟩
  let D : Stacks.Thickenings.CartesianFiniteOrderDeformationDiagram.{u} :=
    { S := Z
      S' := Y
      iS := i
      iS_finiteOrder := hi
      X := pullback f i
      X' := X
      iX := pullback.fst f i
      iX_thickening := hiX
      Y := Z
      Y' := Y
      iY := i
      iY_thickening := hi.isThickening
      pX := pullback.snd f i
      pX' := f
      pY := 𝟙 Z
      pY' := 𝟙 Y
      f := pullback.snd f i
      f' := f
      f_over_S := by simp
      f'_over_S' := by simp
      f_thickening_comm := pullback.condition.symm
      X_cartesian := IsPullback.of_hasPullback f i
      Y_cartesian := IsPullback.of_vert_isIso ⟨by simp⟩
      X'_flat := inferInstance }
  have hEt : Etale f := D.etale_iff.mp (inferInstance : Etale (pullback.snd f i))
  let φ : Arrow.mk (pullback.fst f i) ⟶ Arrow.mk i :=
    Arrow.homMk (pullback.snd f i) f pullback.condition.symm
  have hUI : UniversallyInjective f :=
    (Stacks.Thickenings.universallyInjective_left_iff_right hiX hi.isThickening φ).mp
      (inferInstance : UniversallyInjective (pullback.snd f i))
  have hSurj : Surjective f :=
    (Stacks.Thickenings.surjective_left_iff_right hiX hi.isThickening φ).mp
      (inferInstance : Surjective (pullback.snd f i))
  exact (isIso_iff_isOpenImmersion_and_surjective f).mpr
    ⟨isOpenImmersion_of_etale_universallyInjective f, hSurj⟩

/-- The inverse image of the kernel ideal sheaf of a morphism along that same morphism is zero:
the kernel is the direct image of the zero ideal sheaf, and inverse image is the lower adjoint of
direct image. -/
public theorem comap_ker_self_eq_bot {X Y : Scheme.{u}} (f : X ⟶ Y) : f.ker.comap f = ⊥ := by
  refine le_antisymm ?_ bot_le
  rw [← Scheme.IdealSheafData.map_bot f]
  exact Scheme.IdealSheafData.comap_map_le _ _

/-- The inclusion of the closed subscheme cut out by `𝒥` into the one cut out by a power of `𝒥`
is a finite-order thickening: its kernel ideal sheaf is the inverse image of `𝒥` along the larger
subscheme's inclusion, whose `(n+1)`-st power is the inverse image of `𝒥 ⁿ⁺¹`, and that vanishes
because `𝒥 ⁿ⁺¹` is the kernel of the inclusion it is pulled back along. -/
public theorem isFiniteOrderThickening_inclusion_pow {Y : Scheme.{u}} (J : Y.IdealSheafData)
    (n : ℕ) (h : J ^ (n + 1) ≤ J) :
    Stacks.Thickenings.IsFiniteOrderThickening (Scheme.IdealSheafData.inclusion h) := by
  have hsq : IsPullback (Scheme.IdealSheafData.inclusion h) (𝟙 J.subscheme)
      (J ^ (n + 1)).subschemeι J.subschemeι :=
    IsPullback.of_vert_isIso_mono ⟨by simp⟩
  have hker : (Scheme.IdealSheafData.inclusion h).ker =
      J.comap (J ^ (n + 1)).subschemeι := by
    rw [← hsq.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
      Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, Scheme.IdealSheafData.ker_subschemeι]
  have hb : (J ^ (n + 1)).comap (J ^ (n + 1)).subschemeι = ⊥ := by
    have h0 := comap_ker_self_eq_bot (J ^ (n + 1)).subschemeι
    rwa [Scheme.IdealSheafData.ker_subschemeι] at h0
  refine ⟨inferInstance, n, ?_⟩
  rw [hker, ← Stacks.IdealSheaf.comap_pow, hb]

/-- The base change of a flat morphism along the inclusion of the `n`-th infinitesimal
neighbourhood is an isomorphism as soon as its base change along the closed subscheme itself
is. -/
public theorem isIso_pullbackSnd_subschemeι_pow {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    (J : Y.IdealSheafData) [IsIso (pullback.snd f J.subschemeι)] (n : ℕ) :
    IsIso (pullback.snd f (J ^ (n + 1)).subschemeι) := by
  have h : J ^ (n + 1) ≤ J :=
    Scheme.IdealSheafData.le_def.mpr fun U => Ideal.pow_le_self (by omega)
  have hsq : IsPullback
      (pullback.fst (pullback.snd f (J ^ (n + 1)).subschemeι)
          (Scheme.IdealSheafData.inclusion h) ≫
        pullback.fst f (J ^ (n + 1)).subschemeι)
      (pullback.snd (pullback.snd f (J ^ (n + 1)).subschemeι)
        (Scheme.IdealSheafData.inclusion h)) f J.subschemeι := by
    have hp := (IsPullback.of_hasPullback (pullback.snd f (J ^ (n + 1)).subschemeι)
      (Scheme.IdealSheafData.inclusion h)).paste_horiz
      (IsPullback.of_hasPullback f (J ^ (n + 1)).subschemeι)
    simpa only [Scheme.IdealSheafData.inclusion_subschemeι] using hp
  have _ : IsIso (pullback.snd (pullback.snd f (J ^ (n + 1)).subschemeι)
      (Scheme.IdealSheafData.inclusion h)) := by
    rw [← hsq.isoPullback_hom_snd]
    infer_instance
  exact isIso_of_flat_of_isIso_pullbackSnd (pullback.snd f (J ^ (n + 1)).subschemeι)
    (Scheme.IdealSheafData.inclusion h) (isFiniteOrderThickening_inclusion_pow J n h)

/-- **The `n`-th infinitesimal neighbourhoods are identified.** If `f` is flat and the induced
morphism of closed subschemes is an isomorphism, then so is the induced morphism between the
subschemes cut out by the `(n+1)`-st powers. -/
public theorem isIso_subschemeMap_pow {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    (J : Y.IdealSheafData)
    [IsIso ((J.comapIso f).hom ≫ pullback.snd f J.subschemeι)] (n : ℕ) :
    IsIso (((J ^ (n + 1)).comapIso f).hom ≫
      pullback.snd f (J ^ (n + 1)).subschemeι) := by
  have _ : IsIso (pullback.snd f J.subschemeι) :=
    (isIso_comp_left_iff (J.comapIso f).hom _).mp inferInstance
  have _ := isIso_pullbackSnd_subschemeι_pow f J n
  infer_instance

/-! ### Coherent modules annihilated by a power of the ideal -/

/-- The coherent sheaves of modules annihilated by `I ^ n`. -/
public abbrev coherentAnnihilatedBy {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ) :
    ObjectProperty X.Modules :=
  fun M => M.IsCoherent ∧ idealPowerMultiple I n M = ⊥

/-- Annihilation by the ideal of the subscheme cut out by `I ^ n` is annihilation by `I ^ n`. -/
public theorem annihilatedByKer_subschemeι_pow_iff {X : Scheme.{u}} (I : X.IdealSheafData)
    (n : ℕ) (M : X.Modules) :
    AnnihilatedByKer (I ^ n).subschemeι M ↔ idealPowerMultiple I n M = ⊥ := by
  rw [idealPowerMultiple_eq_bot_iff_affine_sections_annihilated]
  exact ⟨fun h U r hr x => h U r (by rwa [Scheme.IdealSheafData.ker_subschemeι]) x,
    fun h U a ha m => h U a (by rwa [Scheme.IdealSheafData.ker_subschemeι] at ha) m⟩

/-- The property `coherentAnnihilatedBy` is 087T's annihilated-coherent property for the ideal
sheaf `I ^ n`. -/
public theorem coherentAnnihilatedBy_eq {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ) :
    (fun M : X.Modules => M.IsCoherent ∧ AnnihilatedByKer (I ^ n).subschemeι M) =
      coherentAnnihilatedBy I n :=
  funext fun M => propext
    (and_congr_right' (annihilatedByKer_subschemeι_pow_iff I n M))

/-- Coherence and annihilation by `I ^ n` are invariant under isomorphism. -/
public theorem coherentAnnihilatedBy_of_iso {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ)
    {M N : X.Modules} (e : M ≅ N) (hM : coherentAnnihilatedBy I n M) :
    coherentAnnihilatedBy I n N := by
  have _ : M.IsCoherent := hM.1
  refine ⟨Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso e.symm, ?_⟩
  have hM2 := hM.2
  rw [idealPowerMultiple_eq_bot_iff_affine_sections_annihilated] at hM2 ⊢
  intro U a ha m
  have h := hM2 U a ha ((e.inv.app U) m)
  apply_fun (e.hom.app U) at h
  simpa only [Scheme.Modules.Hom.app_smul, map_zero, ← ConcreteCategory.comp_apply,
    ← Scheme.Modules.Hom.comp_app, Iso.inv_hom_id, Scheme.Modules.Hom.id_app,
    CategoryTheory.id_apply] using h

/-- Annihilation by a power may always be weakened to a larger power. -/
public theorem coherentAnnihilatedBy_mono {X : Scheme.{u}} (I : X.IdealSheafData) {m n : ℕ}
    (hmn : m ≤ n) {M : X.Modules} (hM : coherentAnnihilatedBy I m M) :
    coherentAnnihilatedBy I n M :=
  ⟨hM.1, idealPowerMultiple_eq_bot_of_le hM.2 hmn⟩

/-! ### Direct image on annihilated coherent modules -/

/-- Along an isomorphism, direct image is an equivalence of the coherent modules: the
annihilation condition of [Stacks, Tag 087T] is vacuous because the kernel ideal sheaf of an
isomorphism is zero. -/
public def coherentPushforwardEquivalenceOfIsIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] :
    Σ e : CoherentModulesOn X ≌ CoherentModulesOn Y,
      e.functor ⋙ ObjectProperty.ι (fun M : Y.Modules => M.IsCoherent) ≅
        ObjectProperty.ι (fun M : X.Modules => M.IsCoherent) ⋙ Scheme.Modules.pushforward f := by
  let E := coherentPushforwardEquivalence f
  have h : (fun M : Y.Modules => M.IsCoherent ∧ AnnihilatedByKer f M) =
      (fun M : Y.Modules => M.IsCoherent) := by
    funext M
    refine propext ⟨fun hM => hM.1, fun hM => ⟨hM, ?_⟩⟩
    intro U a ha m
    rw [Scheme.Hom.ker_eq_bot_of_isIso, Scheme.IdealSheafData.ideal_bot] at ha
    rw [Ideal.mem_bot.mp ha, zero_smul]
  exact ⟨E.1.trans (ObjectProperty.fullSubcategoryCongr h), E.2⟩

/-- **Direct image is an equivalence from the coherent modules annihilated by the ideal of
`f^{-1}Z` onto those annihilated by the ideal of `Z`.** Both are identified with the coherent
modules on the respective closed subscheme by [Stacks, Tag 087T], and the two subschemes are
identified by hypothesis. -/
public def pushforwardAnnihilatedEquivalence {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) (J : Y.IdealSheafData)
    [IsIso ((J.comapIso f).hom ≫ pullback.snd f J.subschemeι)] :
    Σ e : CoherentAnnihilatedModules (J.comap f).subschemeι ≌
      CoherentAnnihilatedModules J.subschemeι,
      e.functor ⋙ ObjectProperty.ι _ ≅
        ObjectProperty.ι _ ⋙ Scheme.Modules.pushforward f := by
  have _ : IsLocallyNoetherian (J.comap f).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (J.comap f).subschemeι
  have _ : IsLocallyNoetherian J.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian J.subschemeι
  let g := (J.comapIso f).hom ≫ pullback.snd f J.subschemeι
  let A := coherentPushforwardEquivalence (J.comap f).subschemeι
  let B := coherentPushforwardEquivalence J.subschemeι
  let G := coherentPushforwardEquivalenceOfIsIso g
  have hg : g ≫ J.subschemeι = (J.comap f).subschemeι ≫ f := by
    simp [g]
  refine ⟨(A.1.symm.trans G.1).trans B.1, ?_⟩
  exact
    Functor.isoWhiskerLeft (A.1.inverse ⋙ G.1.functor) B.2 ≪≫
    Functor.isoWhiskerLeft A.1.inverse
      (Functor.isoWhiskerRight G.2 (Scheme.Modules.pushforward J.subschemeι)) ≪≫
    Functor.isoWhiskerLeft (A.1.inverse ⋙ ObjectProperty.ι _)
      (Scheme.Modules.pushforwardComp g J.subschemeι) ≪≫
    Functor.isoWhiskerLeft (A.1.inverse ⋙ ObjectProperty.ι _)
      (Scheme.Modules.pushforwardCongr hg) ≪≫
    Functor.isoWhiskerLeft (A.1.inverse ⋙ ObjectProperty.ι _)
      (Scheme.Modules.pushforwardComp (J.comap f).subschemeι f).symm ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft A.1.inverse A.2.symm)
      (Scheme.Modules.pushforward f) ≪≫
    Functor.isoWhiskerRight A.1.counitIso
      (ObjectProperty.ι _ ⋙ Scheme.Modules.pushforward f)

/-- **The levelwise equivalence.** For every `n`, direct image along a flat `f` inducing an
isomorphism of closed subschemes is an equivalence from the coherent `𝒪_X`-modules annihilated
by `ℐ ⁿ⁺¹` onto the coherent `𝒪_Y`-modules annihilated by `𝒥 ⁿ⁺¹`. -/
public def pushforwardCoherentAnnihilatedEquivalence {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [Flat f] (J : Y.IdealSheafData)
    [IsIso ((J.comapIso f).hom ≫ pullback.snd f J.subschemeι)] (n : ℕ) :
    Σ e : (coherentAnnihilatedBy (J.comap f) (n + 1)).FullSubcategory ≌
      (coherentAnnihilatedBy J (n + 1)).FullSubcategory,
      e.functor ⋙ ObjectProperty.ι _ ≅
        ObjectProperty.ι _ ⋙ Scheme.Modules.pushforward f := by
  have _ := isIso_subschemeMap_pow f J n
  let E := pushforwardAnnihilatedEquivalence f (J ^ (n + 1))
  have hs : (fun M : X.Modules => M.IsCoherent ∧
      AnnihilatedByKer ((J ^ (n + 1)).comap f).subschemeι M) =
      coherentAnnihilatedBy (J.comap f) (n + 1) := by
    rw [Stacks.IdealSheaf.comap_pow]
    exact coherentAnnihilatedBy_eq (J.comap f) (n + 1)
  have ht : (fun M : Y.Modules => M.IsCoherent ∧
      AnnihilatedByKer (J ^ (n + 1)).subschemeι M) =
      coherentAnnihilatedBy J (n + 1) :=
    coherentAnnihilatedBy_eq J (n + 1)
  refine ⟨((ObjectProperty.fullSubcategoryCongr hs).symm.trans E.1).trans
    (ObjectProperty.fullSubcategoryCongr ht), ?_⟩
  exact Functor.isoWhiskerLeft (ObjectProperty.fullSubcategoryCongr hs).inverse E.2

/-- Direct image preserves coherence and annihilation by the corresponding power. -/
public theorem coherentAnnihilatedBy_pushforward {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [Flat f] (J : Y.IdealSheafData)
    [IsIso ((J.comapIso f).hom ≫ pullback.snd f J.subschemeι)] (n : ℕ) (M : X.Modules)
    (hM : coherentAnnihilatedBy (J.comap f) (n + 1) M) :
    coherentAnnihilatedBy J (n + 1) ((Scheme.Modules.pushforward f).obj M) :=
  let E := pushforwardCoherentAnnihilatedEquivalence f J n
  coherentAnnihilatedBy_of_iso J (n + 1) (E.2.app ⟨M, hM⟩)
    (E.1.functor.obj ⟨M, hM⟩).property

/-- **Direct image is bijective on morphisms between annihilated coherent modules**, because the
levelwise equivalence is fully faithful and its forward functor is direct image. -/
public theorem pushforward_map_bijective_of_annihilated {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y) [Flat f] (J : Y.IdealSheafData)
    [IsIso ((J.comapIso f).hom ≫ pullback.snd f J.subschemeι)] (n : ℕ) {M N : X.Modules}
    (hM : coherentAnnihilatedBy (J.comap f) (n + 1) M)
    (hN : coherentAnnihilatedBy (J.comap f) (n + 1) N) :
    Function.Bijective ((Scheme.Modules.pushforward f).map :
      (M ⟶ N) → ((Scheme.Modules.pushforward f).obj M ⟶
        (Scheme.Modules.pushforward f).obj N)) := by
  let E := pushforwardCoherentAnnihilatedEquivalence f J n
  let H : ((coherentAnnihilatedBy (J.comap f) (n + 1)).ι ⋙
      Scheme.Modules.pushforward f).FullyFaithful :=
    (E.1.fullyFaithfulFunctor.comp (ObjectProperty.fullyFaithfulι _)).ofIso E.2
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · exact congrArg (fun k : (⟨M, hM⟩ : (coherentAnnihilatedBy
      (J.comap f) (n + 1)).FullSubcategory) ⟶ ⟨N, hN⟩ => k.hom)
      (H.map_injective (X := ⟨M, hM⟩) (Y := ⟨N, hN⟩)
        (f := ObjectProperty.homMk a) (g := ObjectProperty.homMk b) hab)
  · exact ⟨(H.preimage (X := ⟨M, hM⟩) (Y := ⟨N, hN⟩) a).hom,
      H.map_preimage (X := ⟨M, hM⟩) (Y := ⟨N, hN⟩) a⟩

/-- **Direct image is essentially surjective on annihilated coherent modules.** -/
public theorem exists_pushforward_iso_of_annihilated {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [Flat f] (J : Y.IdealSheafData)
    [IsIso ((J.comapIso f).hom ≫ pullback.snd f J.subschemeι)] (n : ℕ) (N : Y.Modules)
    (hN : coherentAnnihilatedBy J (n + 1) N) :
    ∃ M : X.Modules, coherentAnnihilatedBy (J.comap f) (n + 1) M ∧
      Nonempty ((Scheme.Modules.pushforward f).obj M ≅ N) :=
  let E := pushforwardCoherentAnnihilatedEquivalence f J n
  let M := E.1.inverse.obj ⟨N, hN⟩
  ⟨M.obj, M.property, ⟨(E.2.app M).symm ≪≫
    (ObjectProperty.ι _).mapIso (E.1.counitIso.app ⟨N, hN⟩)⟩⟩

/-! ### Direct image on power-torsion coherent modules -/

/-- The coherent sheaves of modules annihilated by *some* positive power of `I`. -/
public abbrev coherentIdealPowerTorsion {X : Scheme.{u}} (I : X.IdealSheafData) :
    ObjectProperty X.Modules :=
  fun M => ∃ n : ℕ, coherentAnnihilatedBy I (n + 1) M

/-- Direct image on the power-torsion coherent modules. -/
public def coherentIdealPowerTorsionPushforward {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [Flat f] (J : Y.IdealSheafData)
    [IsIso ((J.comapIso f).hom ≫ pullback.snd f J.subschemeι)] :
    (coherentIdealPowerTorsion (J.comap f)).FullSubcategory ⥤
      (coherentIdealPowerTorsion J).FullSubcategory :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ Scheme.Modules.pushforward f)
    (fun M => by
      obtain ⟨n, hn⟩ := M.property
      exact ⟨n, coherentAnnihilatedBy_pushforward f J n M.obj hn⟩)

/-- Two power-torsion coherent modules are annihilated by one common positive power. -/
private theorem exists_coherentAnnihilatedBy_of_torsion {X : Scheme.{u}} {I : X.IdealSheafData}
    {M N : X.Modules} (hM : coherentIdealPowerTorsion I M) (hN : coherentIdealPowerTorsion I N) :
    ∃ k : ℕ, coherentAnnihilatedBy I (k + 1) M ∧ coherentAnnihilatedBy I (k + 1) N :=
  let ⟨m, hm⟩ := hM
  let ⟨n, hn⟩ := hN
  ⟨max m n, coherentAnnihilatedBy_mono _ (Nat.add_le_add_right (le_max_left m n) 1) hm,
    coherentAnnihilatedBy_mono _ (Nat.add_le_add_right (le_max_right m n) 1) hn⟩

/-- **Direct image is an equivalence on power-torsion coherent modules.** Two objects are put
under one common exponent and the levelwise statements apply. -/
public theorem coherentIdealPowerTorsionPushforward_isEquivalence {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y) [Flat f] (J : Y.IdealSheafData)
    [IsIso ((J.comapIso f).hom ≫ pullback.snd f J.subschemeι)] :
    (coherentIdealPowerTorsionPushforward f J).IsEquivalence := by
  let R := coherentIdealPowerTorsionPushforward f J
  have hb {M N : (coherentIdealPowerTorsion (J.comap f)).FullSubcategory} :
      Function.Bijective (R.map : (M ⟶ N) → (R.obj M ⟶ R.obj N)) := by
    obtain ⟨k, hm, hn⟩ := exists_coherentAnnihilatedBy_of_torsion M.property N.property
    have H := pushforward_map_bijective_of_annihilated f J k hm hn
    refine ⟨fun a b hab => ?_, fun a => ?_⟩
    · exact ObjectProperty.hom_ext _ (H.1 (congrArg (fun k => k.hom) hab))
    · obtain ⟨b, hb⟩ := H.2 a.hom
      exact ⟨ObjectProperty.homMk b, ObjectProperty.hom_ext _ hb⟩
  refine ⟨⟨fun {_ _} => hb.1⟩, ⟨fun {_ _} => hb.2⟩, ⟨fun N => ?_⟩⟩
  obtain ⟨n, hn⟩ := N.property
  obtain ⟨M, hM, ⟨e⟩⟩ := exists_pushforward_iso_of_annihilated f J n N.obj hn
  exact ⟨⟨M, n, hM⟩, ⟨ObjectProperty.isoMk _ e⟩⟩

/-- Annihilation of the direct image by `𝒥 ⁿ⁺¹` is equivalent to annihilation of the module by
`ℐ ⁿ⁺¹`, for a power-torsion coherent module. -/
public theorem coherentAnnihilatedBy_pushforward_iff {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [Flat f] (J : Y.IdealSheafData)
    [IsIso ((J.comapIso f).hom ≫ pullback.snd f J.subschemeι)] (n : ℕ)
    (M : (coherentIdealPowerTorsion (J.comap f)).FullSubcategory) :
    coherentAnnihilatedBy J (n + 1) ((Scheme.Modules.pushforward f).obj M.obj) ↔
      coherentAnnihilatedBy (J.comap f) (n + 1) M.obj := by
  refine ⟨fun h => ?_, coherentAnnihilatedBy_pushforward f J n M.obj⟩
  obtain ⟨N, hN, ⟨e⟩⟩ := exists_pushforward_iso_of_annihilated f J n _ h
  let R := coherentIdealPowerTorsionPushforward f J
  have _ : R.IsEquivalence := coherentIdealPowerTorsionPushforward_isEquivalence f J
  let N' : (coherentIdealPowerTorsion (J.comap f)).FullSubcategory := ⟨N, n, hN⟩
  let e' : R.obj N' ≅ R.obj M := ObjectProperty.isoMk _ e
  exact coherentAnnihilatedBy_of_iso (J.comap f) (n + 1)
    ((ObjectProperty.ι _).mapIso (R.preimageIso e')) hN

/-! ### Membership in `Coh(X, ℐ)` through precomposition bijectivity -/

/-- Every term of the completion of a coherent sheaf is coherent and annihilated by the
corresponding power, which is [Stacks, Tag 0880] read at the level of a single term. -/
public theorem coherentAnnihilatedBy_idealPowerQuotient {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (n : ℕ) (M : X.Modules) (hM : M.IsCoherent) :
    coherentAnnihilatedBy I (n + 1) (idealPowerQuotient I (n + 1) M) := by
  let F := (completionFunctor X I).obj ⟨M, hM⟩
  have h : coherentAnnihilatedBy I (n + 1) (F.obj.obj (op n)) :=
    ⟨F.property.1 n, F.property.2.1 n⟩
  simpa only [F, completionFunctor_obj] using h

/-- Precomposition with the quotient projection is a bijection onto the maps out of `M` that
kill `I ^ n M`; if the target is annihilated by `I ^ n` every map does. -/
public theorem quotientProjection_comp_bijective {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ)
    {M N : X.Modules} (hN : idealPowerMultiple I n N = ⊥) :
    Function.Bijective (fun g : idealPowerQuotient I n M ⟶ N =>
      cokernel.π (C := X.Modules) (idealPowerMultiple I n M).ι ≫ g) := by
  have hzero : ∀ φ : M ⟶ N, (idealPowerMultiple I n M).ι ≫ φ = 0 := by
    intro φ
    rw [submodule_ι_comp_eq_zero_iff]
    intro U x hx
    have hann := (idealPowerMultiple_le_iff I n M
      (Scheme.Modules.kernelSubmodule φ)).mpr ?_
    · exact hann U hx
    · intro V
      refine Submodule.smul_le.mpr fun a ha m _ => ?_
      have h := affine_sections_annihilated_of_idealPowerMultiple_eq_bot hN V ha
        ((φ.app V) m)
      show (φ.app V) (a • m) = 0
      rwa [Scheme.Modules.Hom.app_smul]
  refine ⟨fun g h hh => (cancel_epi _).mp hh, fun φ => ?_⟩
  exact ⟨cokernel.desc (C := X.Modules) _ φ (hzero φ), cokernel.π_desc _ _ _⟩

/-- **The quotient clause of a coherent adic system, as a bijectivity statement.** A map
`φ : M ⟶ N` out of a coherent `M` onto a coherent `N` annihilated by `I ^ (n+1)` identifies `N`
with `M / I ^ (n+1) M`, compatibly with the quotient projection, exactly when precomposition
with `φ` is bijective on maps into every coherent module annihilated by `I ^ (n+1)`. -/
public theorem exists_quotientIso_iff_comp_bijective {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (n : ℕ) {M N : X.Modules} (hM : M.IsCoherent)
    (hN : coherentAnnihilatedBy I (n + 1) N) (φ : M ⟶ N) :
    (∃ e : idealPowerQuotient I (n + 1) M ≅ N,
      cokernel.π (C := X.Modules) (idealPowerMultiple I (n + 1) M).ι ≫ e.hom = φ) ↔
    ∀ T : X.Modules, coherentAnnihilatedBy I (n + 1) T →
      Function.Bijective (fun g : N ⟶ T => φ ≫ g) := by
  constructor
  · rintro ⟨e, he⟩ T hT
    have _ : Epi φ := by rw [← he]; infer_instance
    refine ⟨fun a b hab => (cancel_epi φ).mp hab, fun g => ?_⟩
    obtain ⟨k, hk⟩ := (quotientProjection_comp_bijective I (n + 1) hT.2).2 g
    refine ⟨e.inv ≫ k, ?_⟩
    rw [← he]
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hk
  · intro hf
    let Q := idealPowerQuotient I (n + 1) M
    let π : M ⟶ Q := cokernel.π (C := X.Modules) (idealPowerMultiple I (n + 1) M).ι
    obtain ⟨d, hd⟩ := (quotientProjection_comp_bijective I (n + 1) hN.2).2 φ
    change π ≫ d = φ at hd
    obtain ⟨v, hv⟩ := (hf Q (coherentAnnihilatedBy_idealPowerQuotient I n M hM)).2 π
    change φ ≫ v = π at hv
    have h₁ : d ≫ v = 𝟙 Q := by
      apply (cancel_epi π).mp
      rw [← Category.assoc, hd, hv, Category.comp_id]
    have h₂ : v ≫ d = 𝟙 N := by
      apply (hf N hN).1
      show φ ≫ (v ≫ d) = φ ≫ 𝟙 N
      rw [← Category.assoc, hv, hd, Category.comp_id]
    exact ⟨⟨d, v, h₁, h₂⟩, hd⟩

/-- **Membership in `Coh(X, ℐ)`, reformulated.** An inverse system is a coherent adic system
along `I` exactly when every term is coherent and annihilated by the corresponding power, and
precomposition with each transition map is bijective on maps into every coherent module
annihilated by that power. -/
public theorem isCoherentAdicSystem_iff_precomp_bijective {X : Scheme.{u}}
    [IsLocallyNoetherian X] (I : X.IdealSheafData) (F : ℕᵒᵖ ⥤ X.Modules) :
    IsCoherentAdicSystem I F ↔
      (∀ n : ℕ, coherentAnnihilatedBy I (n + 1) (F.obj (op n))) ∧
      (∀ n : ℕ, ∀ T : X.Modules, coherentAnnihilatedBy I (n + 1) T →
        Function.Bijective (fun g : F.obj (op n) ⟶ T =>
          F.map (homOfLE (Nat.le_succ n)).op ≫ g)) := by
  refine ⟨fun h => ⟨fun n => ⟨h.1 n, h.2.1 n⟩, fun n => ?_⟩, fun ⟨h, hf⟩ =>
    ⟨fun n => (h n).1, fun n => (h n).2,
      fun n => (exists_quotientIso_iff_comp_bijective I n (h (n + 1)).1 (h n) _).mpr (hf n)⟩⟩
  exact (exists_quotientIso_iff_comp_bijective I n (h.1 (n + 1))
    ⟨h.1 n, h.2.1 n⟩ _).mp (h.2.2 n)

/-! ### Transport of the reformulation -/

/-- A commutative square of maps whose vertical legs are bijections has one horizontal leg
bijective exactly when the other is. -/
public theorem bijective_iff_of_commSquare {A B C D : Type*} (f : A → B) (g : C → D)
    (a : A → C) (b : B → D) (ha : Function.Bijective a) (hb : Function.Bijective b)
    (h : ∀ x, b (f x) = g (a x)) :
    Function.Bijective f ↔ Function.Bijective g := by
  rw [← Function.Bijective.of_comp_iff' hb f, show b ∘ f = g ∘ a from funext h,
    Function.Bijective.of_comp_iff g ha]

/-- Bijectivity of precomposition is unchanged by an isomorphism of the target. -/
public theorem precompBijective_iff_of_isoTarget {C : Type*} [Category* C] {M N T T' : C}
    (φ : M ⟶ N) (e : T ≅ T') :
    Function.Bijective (fun g : N ⟶ T => φ ≫ g) ↔
      Function.Bijective (fun g : N ⟶ T' => φ ≫ g) :=
  bijective_iff_of_commSquare _ _
    (Iso.homCongr (Iso.refl N) e) (Iso.homCongr (Iso.refl M) e)
    (Iso.homCongr (Iso.refl N) e).bijective
    (Iso.homCongr (Iso.refl M) e).bijective (by intro g; simp)

/-- Bijectivity of precomposition is unchanged by an isomorphism of the arrow being
precomposed. -/
public theorem precompBijective_iff_of_arrowIso {C : Type*} [Category* C] {M N M' N' T : C}
    (φ : M ⟶ N) (ψ : M' ⟶ N') (eM : M ≅ M') (eN : N ≅ N')
    (h : φ ≫ eN.hom = eM.hom ≫ ψ) :
    Function.Bijective (fun k : N ⟶ T => φ ≫ k) ↔
      Function.Bijective (fun k : N' ⟶ T => ψ ≫ k) := by
  have hh : eM.inv ≫ φ = ψ ≫ eN.inv := by
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id,
      Category.comp_id] using congrArg (fun k => eM.inv ≫ k ≫ eN.inv) h
  exact bijective_iff_of_commSquare _ _
    (Iso.homCongr eN (Iso.refl T)) (Iso.homCongr eM (Iso.refl T))
    (Iso.homCongr eN (Iso.refl T)).bijective
    (Iso.homCongr eM (Iso.refl T)).bijective
    (by intro k; simpa using congrArg (fun a => a ≫ k) hh)

/-- A functor bijective on the two relevant hom-sets turns bijectivity of precomposition into
bijectivity of precomposition with the image arrow. -/
public theorem precomp_map_bijective_iff {C D : Type*} [Category* C] [Category* D] (R : C ⥤ D)
    {M N T : C} (φ : M ⟶ N)
    (hN : Function.Bijective (R.map : (N ⟶ T) → (R.obj N ⟶ R.obj T)))
    (hM : Function.Bijective (R.map : (M ⟶ T) → (R.obj M ⟶ R.obj T))) :
    Function.Bijective (fun g : N ⟶ T => φ ≫ g) ↔
      Function.Bijective (fun g : R.obj N ⟶ R.obj T => R.map φ ≫ g) :=
  bijective_iff_of_commSquare _ _ R.map R.map hN hM (fun g => R.map_comp φ g)

/-- Being a coherent adic system is invariant under isomorphism of inverse systems. -/
public theorem isCoherentAdicSystem_of_iso {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) {F G : ℕᵒᵖ ⥤ X.Modules} (e : F ≅ G)
    (hF : IsCoherentAdicSystem I F) : IsCoherentAdicSystem I G := by
  rw [isCoherentAdicSystem_iff_precomp_bijective] at hF ⊢
  exact ⟨fun n => coherentAnnihilatedBy_of_iso I (n + 1) (e.app (op n)) (hF.1 n),
    fun n T hT => (precompBijective_iff_of_arrowIso _ _ (e.app (op (n + 1))) (e.app (op n))
      (e.hom.naturality (homOfLE (Nat.le_succ n)).op)).mp (hF.2 n T hT)⟩

/-- Direct image is bijective on morphisms between power-torsion coherent modules. -/
public theorem pushforward_map_bijective_of_torsion {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [Flat f] (J : Y.IdealSheafData)
    [IsIso ((J.comapIso f).hom ≫ pullback.snd f J.subschemeι)] {M N : X.Modules}
    (hM : coherentIdealPowerTorsion (J.comap f) M)
    (hN : coherentIdealPowerTorsion (J.comap f) N) :
    Function.Bijective ((Scheme.Modules.pushforward f).map :
      (M ⟶ N) → ((Scheme.Modules.pushforward f).obj M ⟶
        (Scheme.Modules.pushforward f).obj N)) := by
  obtain ⟨k, hm, hn⟩ := exists_coherentAnnihilatedBy_of_torsion hM hN
  exact pushforward_map_bijective_of_annihilated f J k hm hn

/-- The precomposition clause transports along direct image. -/
public theorem pushforward_transition_bijective_iff {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [Flat f] (J : Y.IdealSheafData)
    [IsIso ((J.comapIso f).hom ≫ pullback.snd f J.subschemeι)] (n : ℕ) {M N : X.Modules}
    (hM : coherentIdealPowerTorsion (J.comap f) M)
    (hN : coherentIdealPowerTorsion (J.comap f) N) (a : M ⟶ N) :
    (∀ T : X.Modules, coherentAnnihilatedBy (J.comap f) (n + 1) T →
      Function.Bijective (fun g : N ⟶ T => a ≫ g)) ↔
    (∀ T : Y.Modules, coherentAnnihilatedBy J (n + 1) T →
      Function.Bijective (fun g : (Scheme.Modules.pushforward f).obj N ⟶ T =>
        (Scheme.Modules.pushforward f).map a ≫ g)) := by
  have hh (T : X.Modules) (hT : coherentAnnihilatedBy (J.comap f) (n + 1) T) :=
    precomp_map_bijective_iff (Scheme.Modules.pushforward f) a
      (pushforward_map_bijective_of_torsion f J hN ⟨n, hT⟩)
      (pushforward_map_bijective_of_torsion f J hM ⟨n, hT⟩)
  refine ⟨fun h T hT => ?_, fun h T hT =>
    (hh T hT).mpr (h _ (coherentAnnihilatedBy_pushforward f J n T hT))⟩
  obtain ⟨S, hS, ⟨e⟩⟩ := exists_pushforward_iso_of_annihilated f J n T hT
  exact (precompBijective_iff_of_isoTarget _ e).mp ((hh S hS).mp (h S hS))

/-- **Termwise direct image detects coherent adic systems.** For a system of power-torsion
coherent `𝒪_X`-modules, the termwise direct image is a coherent adic system along `𝒥` exactly
when the system itself is one along `ℐ`. -/
public theorem isCoherentAdicSystem_pushforward_iff {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [Flat f] (J : Y.IdealSheafData)
    [IsIso ((J.comapIso f).hom ≫ pullback.snd f J.subschemeι)] (F : ℕᵒᵖ ⥤ X.Modules)
    (hF : ∀ n, coherentIdealPowerTorsion (J.comap f) (F.obj n)) :
    IsCoherentAdicSystem J (F ⋙ Scheme.Modules.pushforward f) ↔
      IsCoherentAdicSystem (J.comap f) F := by
  rw [isCoherentAdicSystem_iff_precomp_bijective, isCoherentAdicSystem_iff_precomp_bijective]
  exact and_congr
    (forall_congr' fun n => coherentAnnihilatedBy_pushforward_iff f J n ⟨F.obj (op n), hF (op n)⟩)
    (forall_congr' fun n => (pushforward_transition_bijective_iff f J n
      (hF (op (n + 1))) (hF (op n)) (F.map (homOfLE (Nat.le_succ n)).op)).symm)

/-! ### The inverse equivalence -/

/-- A coherent adic system, viewed as a system of power-torsion coherent modules. -/
public def coherentAdicToTorsionSystems {X : Scheme.{u}} (I : X.IdealSheafData) :
    CoherentAdicSystems I ⥤ ℕᵒᵖ ⥤ (coherentIdealPowerTorsion I).FullSubcategory where
  obj F := ObjectProperty.lift _ F.obj (fun n =>
    ⟨n.unop, F.property.1 n.unop, F.property.2.1 n.unop⟩)
  map a :=
    { app n := ObjectProperty.homMk (a.hom.app n)
      naturality _ _ i := ObjectProperty.hom_ext _ (a.hom.naturality i) }

/-- The passage to systems of power-torsion coherent modules is fully faithful. -/
public def coherentAdicToTorsionSystemsFullyFaithful {X : Scheme.{u}} (I : X.IdealSheafData) :
    (coherentAdicToTorsionSystems I).FullyFaithful where
  preimage a := ObjectProperty.homMk
    { app n := (a.app n).hom
      naturality _ _ i := congrArg (fun k => k.hom) (a.naturality i) }
  map_preimage a := by ext n; rfl
  preimage_map a := by ext n; rfl

/-- **Termwise direct image as a functor `Coh(X, ℐ) ⟶ Coh(Y, 𝒥)`.** -/
public def coherentAdicPushforward {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [Flat f] (J : Y.IdealSheafData)
    [IsIso ((J.comapIso f).hom ≫ pullback.snd f J.subschemeι)] :
    CoherentAdicSystems (J.comap f) ⥤ CoherentAdicSystems J :=
  ObjectProperty.lift _
    (ObjectProperty.ι _ ⋙ (Functor.whiskeringRight _ _ _).obj (Scheme.Modules.pushforward f))
    (fun F => (isCoherentAdicSystem_pushforward_iff f J F.obj
      (fun n => ⟨n.unop, F.property.1 n.unop, F.property.2.1 n.unop⟩)).mpr F.property)

/-- **Termwise direct image is an equivalence `Coh(X, ℐ) ≌ Coh(Y, 𝒥)`.** Full faithfulness is
inherited from the equivalence on power-torsion coherent modules, whiskered over `ℕᵒᵖ`; essential
surjectivity transports a system along the inverse of that equivalence and recognises the result
as a coherent adic system by `isCoherentAdicSystem_pushforward_iff`. -/
public theorem coherentAdicPushforward_isEquivalence {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [Flat f] (J : Y.IdealSheafData)
    [IsIso ((J.comapIso f).hom ≫ pullback.snd f J.subschemeι)] :
    (coherentAdicPushforward f J).IsEquivalence := by
  let R := coherentIdealPowerTorsionPushforward f J
  have _ : R.IsEquivalence := coherentIdealPowerTorsionPushforward_isEquivalence f J
  let A := coherentAdicPushforward f J
  let H := coherentAdicToTorsionSystems (J.comap f) ⋙
    (Functor.whiskeringRight _ _ _).obj R ⋙
      (Functor.whiskeringRight _ _ _).obj (ObjectProperty.ι (coherentIdealPowerTorsion J))
  let hH : H.FullyFaithful :=
    (coherentAdicToTorsionSystemsFullyFaithful (J.comap f)).comp
      (((Functor.FullyFaithful.ofFullyFaithful R).whiskeringRight ℕᵒᵖ).comp
        ((ObjectProperty.fullyFaithfulι (coherentIdealPowerTorsion J)).whiskeringRight ℕᵒᵖ))
  let e : H ≅ A ⋙ ObjectProperty.ι _ := NatIso.ofComponents (fun F => Iso.refl _)
    (by intro F G a; simp only [Iso.refl_hom]; rfl)
  let hA := (hH.ofIso e).ofCompFaithful
  refine ⟨hA.faithful, hA.full, ⟨fun G => ?_⟩⟩
  let G' := (coherentAdicToTorsionSystems J).obj G
  let F' := G' ⋙ R.asEquivalence.inverse
  let F := F' ⋙ ObjectProperty.ι (coherentIdealPowerTorsion (J.comap f))
  let e' : F ⋙ Scheme.Modules.pushforward f ≅ G.obj :=
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft G' R.asEquivalence.counitIso)
      (ObjectProperty.ι (coherentIdealPowerTorsion J))
  have hF : IsCoherentAdicSystem (J.comap f) F :=
    (isCoherentAdicSystem_pushforward_iff f J F (fun n => (F'.obj n).property)).mp
      (isCoherentAdicSystem_of_iso J e'.symm G.property)
  exact ⟨⟨F, hF⟩, ⟨ObjectProperty.isoMk _ e'⟩⟩

/-! ### Stacks 0EHQ -/

/-- **[Stacks, Tag 0EHQ].** Let `f : X ⟶ Y` be a flat morphism of Noetherian schemes, let
`𝒥 ⊆ 𝒪_Y` be a quasi-coherent sheaf of ideals cutting out `Z ⊆ Y`, and let
`ℐ = 𝒥.comap f ⊆ 𝒪_X` cut out the scheme-theoretic inverse image `Z' = f^{-1}Z`. If the induced
morphism `Z' ⟶ Z` is an isomorphism, then the pullback functor

`f^* : Coh(Y, 𝒥) ⟶ Coh(X, ℐ)`

of [Stacks, Tag 0887] is an equivalence.

The functor is left adjoint to the termwise direct image `coherentAdicPushforward`, which is an
equivalence, and a left adjoint of an equivalence is an equivalence. -/
@[stacks 0EHQ]
public theorem coherentAdicPullback_isEquivalence {X Y : Scheme.{u}} [IsNoetherian X]
    [IsNoetherian Y] (f : X ⟶ Y) [Flat f] (J : Y.IdealSheafData)
    [IsIso ((J.comapIso f).hom ≫ pullback.snd f J.subschemeι)] :
    (coherentAdicPullback f J).IsEquivalence := by
  let R := coherentAdicPushforward f J
  have _ : R.IsEquivalence := coherentAdicPushforward_isEquivalence f J
  let adj : coherentAdicPullback f J ⊣ R :=
    ((Scheme.Modules.pullbackPushforwardAdjunction f).whiskerRight ℕᵒᵖ).restrictFullyFaithful
      (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
      (Iso.refl _) (Iso.refl _)
  exact Functor.isEquivalence_of_iso
    (R.asEquivalence.symm.toAdjunction.leftAdjointUniq adj)

end Stacks.Coherent

end
