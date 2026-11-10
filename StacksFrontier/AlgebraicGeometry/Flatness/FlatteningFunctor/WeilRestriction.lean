module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationCokernel
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCoherentImage.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.GermSourceAndTarget.Flat
public import StacksFrontier.AlgebraicGeometry.FinitePresentationWitness.Basic
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.IsoLocusAffineTests
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Scheme.Immersion.BaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Weil restriction of a closed subscheme

Let `f : X ⟶ S` be a morphism of schemes and `i : Y ⟶ X` a closed subscheme of `X`.  The *Weil
restriction* `f_* Y` is the subfunctor of the final functor on schemes over `S` recording where
`Y` becomes all of `X`: a scheme `T` over `S` is a section exactly when the base change
`Y_T ⟶ X_T` of `i` is an isomorphism.  When `f` is of finite presentation, flat and pure, Tag
07AI asserts that this functor is represented by a closed immersion into `S`, of finite
presentation as soon as `Y ⟶ S` is.

The source's proof is three lines: let `I` be the ideal sheaf of `Y` in `X` and
`u : 𝒪_X ⟶ 𝒪_X/I` the surjection; then `Y_T ⟶ X_T` is an isomorphism exactly when `u_T` is, so
the statement is Tag 05PF for `u`.  Carrying that out is what this file does.

`𝒪_X/I` is spelled `i_* 𝒪_Y`, and `u` is `SheafOfModules.unitToPushforwardObjUnit`; the two agree
because `cokernel (I ⟶ 𝒪_X) ≅ i_* 𝒪_Y` for a closed immersion, which is
`Stacks.Flatness.WeilRestriction.quotientIsoPushforwardUnit` below — `u` is an epimorphism, so it
is the cokernel of its own kernel, and its kernel is the ideal sheaf.  This spelling is forced:
nothing in the library builds `𝒪_X/I` as a quotient of `𝒪_X` by an `IdealSheafData`.

The equivalence `Y_T ⟶ X_T` iso `↔` `u_T` iso is proved as a chain of four reformulations.  Since
`u` is the cokernel of `κ : I ⟶ 𝒪_X` and pulling back preserves cokernels, `u_T` is an
isomorphism exactly when `κ_T = 0`; transposing across `g^* ⊣ g_*` for `g : X_T ⟶ X` turns that
into vanishing of the canonical map `g^* I ⟶ 𝒪_{X_T}`, hence of its image, which is the
inverse-image ideal of Tag 01HQ; Tag 01JU identifies that image with the ideal sheaf of the base
change `Y_T ⟶ X_T`; and a closed immersion with vanishing ideal sheaf is an isomorphism.

## Main definitions

* `Stacks.Flatness.WeilRestriction.closedSubschemeBaseChange` is the base change `Y_T ⟶ X_T` of
  `i`.
* `Stacks.Flatness.WeilRestriction.situation` is the module-map situation of Tag 05MH attached to
  `u : 𝒪_X ⟶ i_* 𝒪_Y`.
* `Stacks.Flatness.weilRestrictionFunctor` is the Weil restriction functor itself, whose value at
  `T` is the proposition that `Y_T ⟶ X_T` is an isomorphism.

## Main results

* `WeilRestriction.isIsomorphismAfterBaseChange_iff_isIso_closedSubschemeBaseChange`: `u_T` is
  an isomorphism exactly when `Y_T ⟶ X_T` is.
* `Stacks.Flatness.weilRestriction_representableBy_closedImmersion_of_affineTests` and
  `Stacks.Flatness.finitePresentation_hom_of_representableBy_weilRestrictionFunctor`: the two
  assertions of Tag 07AI.

## Implementation notes

The equivalence "`Y_T ⟶ X_T` is an isomorphism if and only if `u_T` is" is proved for an
arbitrary scheme `T` over `S`, as
`Stacks.Flatness.WeilRestriction.isIsomorphismAfterBaseChange_iff_isIso_closedSubschemeBaseChange`;
Tag 07AI then follows from Tag 05PF applied to `u`.

## References

* [Stacks Project, Tag 01HQ](https://stacks.math.columbia.edu/tag/01HQ)
* [Stacks Project, Tag 01JU](https://stacks.math.columbia.edu/tag/01JU)
* [Stacks Project, Tag 05PF](https://stacks.math.columbia.edu/tag/05PF)
* [Stacks Project, Tag 07AI](https://stacks.math.columbia.edu/tag/07AI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Flatness.WeilRestriction

variable {Y X S : Scheme.{u}}

/-! ### The surjection `u : 𝒪_X ⟶ 𝒪_X/I` -/

/-- The base change `Y_T ⟶ X_T` of a morphism `i : Y ⟶ X` of schemes over `S` along a scheme `T`
over `S`.  This is the morphism whose being an isomorphism the Weil restriction records. -/
@[sga "1 I 5.5" "more general"]
abbrev closedSubschemeBaseChange (i : Y ⟶ X) (f : X ⟶ S) (T : Over S) :
    pullback (i ≫ f) T.hom ⟶ pullback f T.hom :=
  ((Over.pullback T.hom).map (Over.homMk i (by simp) : Over.mk (i ≫ f) ⟶ Over.mk f)).left

/-- **The surjection `u : 𝒪_X ⟶ 𝒪_X/I` of the source's proof**, spelled as the structure-sheaf map
`𝒪_X ⟶ i_* 𝒪_Y` of `i : Y ⟶ X`, as a morphism in `X.Modules`.

The ascription to `AlgebraicGeometry.Scheme.Modules` is load-bearing: the kernel and cokernel of
`u` must be formed in `X.Modules` so that `AlgebraicGeometry.Scheme.Modules.pullback` applies to
them. The ringed-space spelling is definitionally equal but not interchangeable at the
transparency the elaborator uses for implicit arguments. -/
abbrev structureQuotientMap (i : Y ⟶ X) :
    (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶
      (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Y.ringCatSheaf) :=
  SheafOfModules.unitToPushforwardObjUnit (structureSheafHom i.toLRSHom.toShHom)

/-- The structure-sheaf map `u : 𝒪_X ⟶ i_* 𝒪_Y` of a closed immersion is an epimorphism; for a
closed immersion cutting out `Y` by `I` this is the surjection `𝒪_X ⟶ 𝒪_X/I` of the source. -/
instance epi_structureQuotientMap (i : Y ⟶ X) [IsClosedImmersion i] :
    Epi (structureQuotientMap i) :=
  have hclosed : Stacks.ClosedImmersion.IsClosedImmersion i.toLRSHom.toShHom :=
    ((Stacks.AlgebraicGeometry.ClosedImmersionTFAE.closedImmersion_tfae i).out 1 6).mp
      (show AlgebraicGeometry.IsClosedImmersion i from inferInstance)
  hclosed.structureSheafMap_epi

/-- **`u : 𝒪_X ⟶ i_* 𝒪_Y` presents its target as the cokernel of the ideal sheaf.**  For a closed
immersion `u` is an epimorphism, and an epimorphism in an abelian category is the cokernel of its
own kernel. -/
def epiIsCokernelOfKernelStructureSheafHom (i : Y ⟶ X) [IsClosedImmersion i] :
    IsColimit (CokernelCofork.ofπ
      (structureQuotientMap i)
      (kernel.condition (structureQuotientMap i))) :=
  Abelian.epiIsCokernelOfKernel
    (KernelFork.ofι (kernel.ι (structureQuotientMap i))
      (kernel.condition (structureQuotientMap i)))
    (kernelIsKernel _)

/-- **The direct image of the structure sheaf along a closed immersion is the quotient by the
ideal sheaf.**  The map `u : 𝒪_X ⟶ i_* 𝒪_Y` is the cokernel of its own kernel, and its kernel is
the ideal sheaf; so `i_* 𝒪_Y` is `𝒪_X/I`. -/
def quotientIsoPushforwardUnit (i : Y ⟶ X) [IsClosedImmersion i] :
    cokernel (kernel.ι (structureQuotientMap i)) ≅
      (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Y.ringCatSheaf) :=
  (cokernelIsCokernel (kernel.ι (structureQuotientMap i))).coconePointUniqueUpToIso
    (epiIsCokernelOfKernelStructureSheafHom i)

/-- The quotient map onto `𝒪_X/I` is `u` itself, read through
`Stacks.Flatness.WeilRestriction.quotientIsoPushforwardUnit`. -/
theorem cokernelπ_comp_quotientIsoPushforwardUnit (i : Y ⟶ X) [IsClosedImmersion i] :
    cokernel.π (kernel.ι (structureQuotientMap i)) ≫ (quotientIsoPushforwardUnit i).hom =
      structureQuotientMap i :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel _)
    (epiIsCokernelOfKernelStructureSheafHom i) WalkingParallelPair.one

/-- **The situation of Tag 05MH attached to a closed subscheme.**  The structure morphism `f`,
with the surjection `u : 𝒪_X ⟶ i_* 𝒪_Y = 𝒪_X/I` cutting out `Y`. -/
def situation (i : Y ⟶ X) (f : X ⟶ S) [IsClosedImmersion i] :
    ModuleMapBaseChangeSituation.{u} where
  S := S
  X := X
  f := f
  F := SheafOfModules.unit X.ringCatSheaf
  G := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Y.ringCatSheaf)
  hom := structureQuotientMap i
  isQuasicoherentF := Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X
  isQuasicoherentG :=
    AlgebraicGeometry.ClosedImmersionCoherentImage.isQuasicoherent_pushforward_unit i

/-- The base of the situation attached to `i` and `f` is `S`. -/
@[simp]
theorem situation_S (i : Y ⟶ X) (f : X ⟶ S) [IsClosedImmersion i] : (situation i f).S = S := rfl

/-- The structure morphism of the situation attached to `i` and `f` is `f`. -/
@[simp]
theorem situation_f (i : Y ⟶ X) (f : X ⟶ S) [IsClosedImmersion i] : (situation i f).f = f := rfl

/-! ### The equivalence of the source's proof -/

/-- A functor preserving the cokernel of `k` and the zero morphism inverts the image of
`cokernel.π k` exactly when it kills `k`: the image of the projection is again a cokernel
projection, and a cokernel projection is invertible exactly when the map is zero. -/
theorem isIso_map_cokernelπ_iff_map_eq_zero {C D : Type*} [Category C] [Category D]
    [HasZeroMorphisms C] [HasZeroMorphisms D] {A B : C} (k : A ⟶ B) [HasCokernel k]
    (F : C ⥤ D) (hF : F.PreservesZeroMorphisms)
    (hcolim : PreservesColimit (parallelPair k 0) F) [HasCokernel (F.map k)] :
    IsIso (F.map (cokernel.π k)) ↔ F.map k = 0 := by
  have hcomp := PreservesCokernel.π_iso_hom (G := F) (f := k)
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have : IsIso (cokernel.π (F.map k)) := by
      rw [← hcomp]
      infer_instance
    exact eq_zero_of_mono_cokernel (F.map k)
  · have hcompIso : IsIso (F.map (cokernel.π k) ≫ (PreservesCokernel.iso F k).hom) := by
      rw [hcomp]
      exact cokernel.π_of_zero h
    exact (isIso_comp_right_iff _ _).mp hcompIso

/-- **A closed immersion with vanishing ideal sheaf is an isomorphism, and conversely.**  If the
inclusion of the ideal sheaf is zero then `u : 𝒪_X ⟶ i_* 𝒪_Y` is a monomorphism, hence — being
an epimorphism — invertible, so the kernel of `i` on sections is trivial and `i.ker = ⊥`. -/
theorem kernelι_structureSheafHom_eq_zero_iff_isIso (i : Y ⟶ X) [IsClosedImmersion i] :
    kernel.ι (structureQuotientMap i) = 0 ↔ IsIso i := by
  refine ⟨fun hk ↦ ?_, fun hi ↦ ?_⟩
  · have hmono : Mono (structureQuotientMap i) :=
      CategoryTheory.Abelian.mono_of_kernel_ι_eq_zero _ hk
    have hiso : IsIso (structureQuotientMap i) := isIso_of_mono_of_epi _
    refine IsClosedImmersion.isIso_iff_ker_eq_bot.mpr (Scheme.IdealSheafData.ext ?_)
    funext U
    rw [Scheme.Hom.ker_apply]
    change RingHom.ker (CommRingCat.Hom.hom (i.app U)) = ⊥
    rw [← RingHom.injective_iff_ker_eq_bot]
    intro a b hab
    exact ((ConcreteCategory.isIso_iff_bijective (Scheme.Modules.Hom.app
      (structureQuotientMap i) U)).mp ((Scheme.Modules.Hom.isIso_iff_isIso_app.mp hiso) U)).1 hab
  · have hiso : IsIso (structureQuotientMap i) := by
      refine Scheme.Modules.Hom.isIso_iff_isIso_app.2 fun U ↦ ?_
      have hiapp : Function.Bijective (CommRingCat.Hom.hom (i.app U)) :=
        (ConcreteCategory.isIso_iff_bijective (i.app U)).mp inferInstance
      refine (ConcreteCategory.isIso_iff_bijective
        (Scheme.Modules.Hom.app (structureQuotientMap i) U)).mpr
          ⟨fun _ _ hab ↦ hiapp.1 hab, fun b ↦ ?_⟩
      change Γ(Y, i ⁻¹ᵁ U) at b
      exact hiapp.2 b
    have hmono : Mono (structureQuotientMap i) := IsIso.mono_of_iso _
    exact (isZero_kernel_of_mono (structureQuotientMap i)).eq_of_src _ _

section Bridge

variable (i : Y ⟶ X) (f : X ⟶ S) [IsClosedImmersion i] (T : Over S)

/-- Pulling back `u` to `X_T` inverts it exactly when it kills the inclusion of the ideal sheaf:
`u` is the cokernel of that inclusion, and the pullback functor, being a left adjoint, preserves
cokernels. -/
theorem isIsomorphismAfterBaseChange_iff_map_kernelι_eq_zero :
    (situation i f).IsIsomorphismAfterBaseChange T ↔
      (Scheme.Modules.pullback (pullback.fst f T.hom)).map
        (kernel.ι (structureQuotientMap i)) = 0 := by
  have hpcs : PreservesColimitsOfSize.{0, 0}
      (Scheme.Modules.pullback (pullback.fst f T.hom)) :=
    (Scheme.Modules.pullbackPushforwardAdjunction
      (pullback.fst f T.hom)).leftAdjoint_preservesColimits
  -- `Functor.map_comp` and the factorization of `u` are composed as terms, with `Eq.trans`,
  -- rather than by rewriting: the composite straddles the two spellings of the category of
  -- modules, so neither side matches a stated goal at `implicit` transparency.
  have hmap : (Scheme.Modules.pullback (pullback.fst f T.hom)).map (structureQuotientMap i) =
      (Scheme.Modules.pullback (pullback.fst f T.hom)).map
          (cokernel.π (kernel.ι (structureQuotientMap i))) ≫
        (Scheme.Modules.pullback (pullback.fst f T.hom)).map
          (quotientIsoPushforwardUnit i).hom :=
    (congrArg (Scheme.Modules.pullback (pullback.fst f T.hom)).map
        (cokernelπ_comp_quotientIsoPushforwardUnit i)).symm.trans
      ((Scheme.Modules.pullback (pullback.fst f T.hom)).map_comp
        (cokernel.π (kernel.ι (structureQuotientMap i))) (quotientIsoPushforwardUnit i).hom)
  have hiso : IsIso ((Scheme.Modules.pullback (pullback.fst f T.hom)).map
      (quotientIsoPushforwardUnit i).hom) :=
    ((Scheme.Modules.pullback (pullback.fst f T.hom)).mapIso
      (quotientIsoPushforwardUnit i)).isIso_hom
  -- `key` is elaborated with no expected type on purpose, so that its instance arguments are
  -- synthesized canonically rather than fixed by unification against a goal `rw` has rebuilt.
  have hpz : (Scheme.Modules.pullback (pullback.fst f T.hom)).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  have hpc : PreservesColimit (parallelPair (kernel.ι (structureQuotientMap i)) 0)
      (Scheme.Modules.pullback (pullback.fst f T.hom)) :=
    hpcs.preservesColimitsOfShape.preservesColimit
  have key := isIso_map_cokernelπ_iff_map_eq_zero (kernel.ι (structureQuotientMap i))
    (Scheme.Modules.pullback (pullback.fst f T.hom)) hpz hpc
  change IsIso ((Scheme.Modules.pullback (pullback.fst f T.hom)).map
    (structureQuotientMap i)) ↔ _
  rw [hmap, isIso_comp_right_iff]
  exact key

omit [IsClosedImmersion i] in
/-- Vanishing of the pullback of the ideal-sheaf inclusion is vanishing of the canonical map
`g^* I ⟶ 𝒪_{X_T}` of Tag 01HQ: the two differ by the canonical identification of the pulled-back
structure sheaf with the structure sheaf, which is an isomorphism. -/
theorem map_kernelι_eq_zero_iff_pullbackIdealMap_eq_zero :
    (Scheme.Modules.pullback (pullback.fst f T.hom)).map
        (kernel.ι (structureQuotientMap i)) = 0 ↔
      Stacks.ClosedImmersion.pullbackIdealMap (pullback.fst f T.hom).toLRSHom
        (Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom) (kernel.ι _) = 0 := by
  have hadjr : (SheafOfModules.pushforward
      (structureSheafHom (pullback.fst f T.hom).toLRSHom.toShHom)).IsRightAdjoint :=
    modulePushforward_isRightAdjoint _
  have hfinal : (RingedSpaceModuleAdjunction.opensMap
      (pullback.fst f T.hom).toLRSHom.toShHom).Final :=
    CategoryTheory.final_of_representablyFlat _
  have hmul : (Scheme.Modules.pullback (pullback.fst f T.hom)).map
        (kernel.ι (structureQuotientMap i)) ≫
      SheafOfModules.pullbackObjUnitToUnit
        (structureSheafHom (pullback.fst f T.hom).toLRSHom.toShHom) =
      Stacks.ClosedImmersion.pullbackIdealMap (pullback.fst f T.hom).toLRSHom
        (Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom) (kernel.ι _) := rfl
  exact ⟨fun h ↦ hmul.symm.trans ((congrArg (· ≫ SheafOfModules.pullbackObjUnitToUnit
      (structureSheafHom (pullback.fst f T.hom).toLRSHom.toShHom)) h).trans zero_comp),
    fun h ↦ (cancel_mono (SheafOfModules.pullbackObjUnitToUnit
      (structureSheafHom (pullback.fst f T.hom).toLRSHom.toShHom))).1
      (hmul.trans (h.trans zero_comp.symm))⟩

/-- A morphism in an abelian category vanishes exactly when the inclusion of its image does. -/
theorem abelianImageι_eq_zero_iff {A : Type*} [Category A] [Abelian A] {M N : A} (m : M ⟶ N) :
    Abelian.image.ι m = 0 ↔ m = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← Abelian.image.fac m, h, comp_zero]
  · refine (cancel_epi (Abelian.factorThruImage m)).1 ?_
    rw [Abelian.image.fac m, h, comp_zero]

/-- **Tag 01JU in the form the equivalence needs.**  The inverse-image ideal of `I` under
`g : X_T ⟶ X` is the ideal sheaf of the base change `Y ×_X X_T ⟶ X_T` of `i`, so one of the two
inclusions into `𝒪_{X_T}` vanishes exactly when the other does. -/
theorem pullbackIdealInclusion_eq_zero_iff_kernelι_eq_zero :
    Stacks.ClosedImmersion.pullbackIdealInclusion (pullback.fst f T.hom).toLRSHom
        (Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom) (kernel.ι _) = 0 ↔
      kernel.ι (structureQuotientMap (pullback.snd i (pullback.fst f T.hom))) = 0 := by
  obtain ⟨e, he, -⟩ := Stacks.ClosedImmersion.existsUnique_idealSheaf_pullbackSnd_iso_pullbackIdeal
    i (pullback.fst f T.hom) (Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom)
    (kernel.ι _) (Iso.refl _) rfl
  exact ⟨fun h ↦ he.symm.trans ((congrArg (e.hom ≫ ·) h).trans comp_zero),
    fun h ↦ (cancel_epi e.hom).1 (he.trans (h.trans comp_zero.symm))⟩

omit [IsClosedImmersion i] in
/-- The base change of `i` along `T` is an isomorphism exactly when the projection
`Y ×_X X_T ⟶ X_T` is: the two differ by the canonical identification of `Y ×_X (X ×_S T)` with
`Y ×_S T`. -/
theorem isIso_closedSubschemeBaseChange_iff_isIso_pullbackSnd :
    IsIso (closedSubschemeBaseChange i f T) ↔ IsIso (pullback.snd i (pullback.fst f T.hom)) := by
  have hp : closedSubschemeBaseChange i f T =
      (pullbackRightPullbackFstIso f T.hom i).inv ≫
        pullback.snd i (pullback.fst f T.hom) := by
    refine pullback.hom_ext ?_ ?_ <;>
      simp [closedSubschemeBaseChange, Over.pullback,
        pullbackRightPullbackFstIso_inv_snd_fst, pullbackRightPullbackFstIso_inv_snd_snd]
  rw [hp, isIso_comp_left_iff]

/-- **The equivalence of the source's proof.**  For a scheme `T` over `S`, the base change
`u_T` of `u : 𝒪_X ⟶ 𝒪_X/I` is an isomorphism exactly when the base change `Y_T ⟶ X_T` of the
closed immersion is. -/
theorem isIsomorphismAfterBaseChange_iff_isIso_closedSubschemeBaseChange :
    (situation i f).IsIsomorphismAfterBaseChange T ↔ IsIso (closedSubschemeBaseChange i f T) := by
  rw [isIsomorphismAfterBaseChange_iff_map_kernelι_eq_zero i f T,
    map_kernelι_eq_zero_iff_pullbackIdealMap_eq_zero i f T,
    ← abelianImageι_eq_zero_iff (Stacks.ClosedImmersion.pullbackIdealMap
      (pullback.fst f T.hom).toLRSHom
      (Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom) (kernel.ι _)),
    show Abelian.image.ι (Stacks.ClosedImmersion.pullbackIdealMap
          (pullback.fst f T.hom).toLRSHom
          (Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom) (kernel.ι _)) =
        Stacks.ClosedImmersion.pullbackIdealInclusion (pullback.fst f T.hom).toLRSHom
          (Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom) (kernel.ι _) from rfl,
    pullbackIdealInclusion_eq_zero_iff_kernelι_eq_zero i f T,
    kernelι_structureSheafHom_eq_zero_iff_isIso (pullback.snd i (pullback.fst f T.hom)),
    isIso_closedSubschemeBaseChange_iff_isIso_pullbackSnd i f T]

end Bridge

/-! ### Discharging the hypotheses of Tag 05PF -/

/-- The quotient `𝒪_X/I` is of finite presentation when the closed immersion is: the ideal sheaf
is then of finite type by Tag 01TV, the structure sheaf is of finite presentation, and the
cokernel of a map from a finite-type module to a finitely presented one is finitely presented. -/
theorem isFinitePresentation_pushforwardUnit (i : Y ⟶ X) [IsClosedImmersion i]
    (hi : AlgebraicGeometry.FinitePresentation i) :
    ((Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit Y.ringCatSheaf)).IsFinitePresentation := by
  have hideal : (kernel (structureQuotientMap i)).IsFiniteType :=
    AlgebraicGeometry.finitePresentation_iff_isFiniteType_idealSheaf i |>.mp hi
  exact (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso
    (quotientIsoPushforwardUnit i) (Stacks.SheafOfModules.isFinitePresentation_cokernel _)

/-- A flat morphism of schemes is flat over its target with the structure sheaf of its source as
coefficients, which is the flatness hypothesis of Tag 05PF for `u`. -/
theorem isFlatOver_structureSheafUnit (f : X ⟶ S) [Flat f] :
    AlgebraicGeometry.IsFlatOver f.toLRSHom.toShHom (SheafOfModules.unit X.ringCatSheaf) :=
  fun x ↦ (AlgebraicGeometry.MorphismOfGerms.flat_stalkMap_iff_isFlatOverAt_unit f x).1
    (Flat.stalkMap f x)

end Stacks.Flatness.WeilRestriction

namespace Stacks.Flatness

variable {Y X S : Scheme.{u}}

open Stacks.Flatness.WeilRestriction

/-- **The Weil restriction functor of a closed subscheme.**  For a closed subscheme `i : Y ⟶ X`
of a scheme over `S`, this is the subfunctor of the final functor on schemes over `S` whose
sections over `T` record that the base change `Y_T ⟶ X_T` is an isomorphism — the functor
`F = f_* Y` of Tag 07AI, with its two values `{*}` and `∅` spelled as a proposition. -/
def weilRestrictionFunctor (i : Y ⟶ X) (f : X ⟶ S) [IsClosedImmersion i] :
    (Over S)ᵒᵖ ⥤ Type where
  obj T := PLift (IsIso (closedSubschemeBaseChange i f T.unop))
  map g := ↾fun h ↦ ⟨(isIsomorphismAfterBaseChange_iff_isIso_closedSubschemeBaseChange i f _).1
    ((situation i f).isIsomorphismAfterBaseChange_of_hom g.unop
      ((isIsomorphismAfterBaseChange_iff_isIso_closedSubschemeBaseChange i f _).2 h.down))⟩
  map_id T := by ext h; exact Subsingleton.elim _ _
  map_comp g h := by ext x; exact Subsingleton.elim _ _

/-- The Weil restriction functor takes at most one value at each test scheme: it is a subfunctor
of the final functor. As `AlgebraicGeometry.Scheme.Modules` is a `def`, the instance is restated
at this ascription. -/
instance subsingleton_weilRestrictionFunctor_obj (i : Y ⟶ X) (f : X ⟶ S) [IsClosedImmersion i]
    (T : (Over S)ᵒᵖ) : Subsingleton ((weilRestrictionFunctor i f).obj T) :=
  inferInstanceAs (Subsingleton (PLift (IsIso (closedSubschemeBaseChange i f T.unop))))

/-- The isomorphism functor of the situation attached to a closed subscheme takes at most one
value at each test scheme, at the ascription this file uses for its test schemes. -/
instance subsingleton_situation_isomorphismFunctor_obj (i : Y ⟶ X) (f : X ⟶ S)
    [IsClosedImmersion i] (T : (Over S)ᵒᵖ) :
    Subsingleton ((situation i f).isomorphismFunctor.obj T) :=
  inferInstanceAs
    (Subsingleton (PLift ((situation i f).IsIsomorphismAfterBaseChange T.unop)))

/-- The Weil restriction functor is the isomorphism functor of `u : 𝒪_X ⟶ 𝒪_X/I`.  This is the
source's equivalence, packaged as a natural isomorphism; the components are bijections of
subsingletons, so naturality is automatic. -/
def weilRestrictionFunctorIsoIsomorphismFunctor (i : Y ⟶ X) (f : X ⟶ S) [IsClosedImmersion i] :
    weilRestrictionFunctor i f ≅ (situation i f).isomorphismFunctor :=
  NatIso.ofComponents
    (fun T ↦ Equiv.toIso
      { toFun := fun h ↦
          ⟨(isIsomorphismAfterBaseChange_iff_isIso_closedSubschemeBaseChange i f _).2 h.down⟩
        invFun := fun h ↦
          ⟨(isIsomorphismAfterBaseChange_iff_isIso_closedSubschemeBaseChange i f _).1 h.down⟩
        left_inv := fun _ ↦ Subsingleton.elim _ _
        right_inv := fun _ ↦ Subsingleton.elim _ _ })
    fun _ ↦ by ext x; exact Subsingleton.elim _ _

/-- Representability transports along the natural isomorphism with the isomorphism functor. -/
def representableByWeilRestrictionFunctor {i : Y ⟶ X} {f : X ⟶ S} [IsClosedImmersion i]
    {W : Over S} (e : (situation i f).isomorphismFunctor.RepresentableBy W) :
    (weilRestrictionFunctor i f).RepresentableBy W where
  homEquiv {T} := e.homEquiv.trans
    ((weilRestrictionFunctorIsoIsomorphismFunctor i f).app (op T)).toEquiv.symm
  homEquiv_comp _ _ := Subsingleton.elim _ _

/-- **Stacks Project, Tag 07AI.** The Weil restriction `f_* Y` of a closed subscheme `Y` of `X`
along a morphism `f : X ⟶ S` which is of finite presentation, flat and pure is represented by a
closed immersion `Z ⟶ S`.

By the equivalence
`Stacks.Flatness.WeilRestriction.isIsomorphismAfterBaseChange_iff_isIso_closedSubschemeBaseChange`
the functor is the isomorphism functor of the surjection `u : 𝒪_X ⟶ 𝒪_X/I` cutting out `Y`, whose
hypotheses in Tag 05PF are exactly the ones assumed here: `𝒪_X` is of finite type and of finite
presentation over itself, it is flat over `S` because `f` is flat, and it is pure relative to `S`
because `X` is. -/
@[stacks 07AI "representability by a closed immersion"]
theorem weilRestriction_representableBy_closedImmersion_of_affineTests
    (i : Y ⟶ X) (f : X ⟶ S) [IsClosedImmersion i]
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f] [Flat f]
    (hpure : AlgebraicGeometry.IsSchemePureRelative f) :
    ∃ W : Over S, IsClosedImmersion W.hom ∧
      Nonempty ((weilRestrictionFunctor i f).RepresentableBy W) := by
  have hlfp : LocallyOfFinitePresentation (situation i f).f :=
    inferInstanceAs (LocallyOfFinitePresentation f)
  have hlft : LocallyOfFiniteType (situation i f).f := inferInstanceAs (LocallyOfFiniteType f)
  have hqcf : QuasiCompact (situation i f).f := inferInstanceAs (QuasiCompact f)
  have hqsf : QuasiSeparated (situation i f).f := inferInstanceAs (QuasiSeparated f)
  have hft : (situation i f).F.IsFiniteType := AlgebraicGeometry.structureSheaf_isFiniteType X
  have hqc : (situation i f).F.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X
  have hfp : (situation i f).F.IsFinitePresentation :=
    inferInstanceAs (SheafOfModules.unit X.ringCatSheaf).IsFinitePresentation
  have hepi : Epi (situation i f).hom := epi_structureQuotientMap i
  obtain ⟨W, hW, hrep⟩ :=
    isomorphismFunctor_representableBy_closedImmersion_of_affineTests (situation i f)
      (isFlatOver_structureSheafUnit f) hpure
  exact ⟨W, hW, hrep.map representableByWeilRestrictionFunctor⟩

/-- **Stacks Project, Tag 07AI.** If the closed subscheme `Y` is of finite presentation over `S`,
every closed immersion representing the Weil restriction `f_* Y` is of finite presentation.

The quotient `𝒪_X/I` is then of finite presentation, by Tag 01TV and
`Stacks.Flatness.WeilRestriction.isFinitePresentation_pushforwardUnit`, which is the hypothesis
Tag 05PF's second assertion needs; the assertion itself is
`Stacks.Flatness.finitePresentation_hom_of_representableBy_isomorphismFunctor`, and needs no
flattening ideal.  Unlike the first assertion this one constructs no representative: it applies
to any representing closed immersion, and such a one exists by the first assertion. -/
@[stacks 07AI "finite presentation of the representing closed immersion",
  sga "3 VIB 6.2.3" "(ii)",
  sga "3 VIB 6.5.2" "special case",
  sga "3 XI 6.8" "special case"]
theorem finitePresentation_hom_of_representableBy_weilRestrictionFunctor
    (i : Y ⟶ X) (f : X ⟶ S) [IsClosedImmersion i]
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (hY : AlgebraicGeometry.FinitePresentation (i ≫ f))
    {Z : Scheme.{u}} (p : Z ⟶ S) [AlgebraicGeometry.IsClosedImmersion p]
    (e : (weilRestrictionFunctor i f).RepresentableBy (Over.mk p)) :
    AlgebraicGeometry.FinitePresentation p := by
  have hlft : LocallyOfFiniteType (situation i f).f := inferInstanceAs (LocallyOfFiniteType f)
  have hqcf : QuasiCompact (situation i f).f := inferInstanceAs (QuasiCompact f)
  have hft : (situation i f).F.IsFiniteType := AlgebraicGeometry.structureSheaf_isFiniteType X
  have hGfp : (situation i f).G.IsFinitePresentation :=
    isFinitePresentation_pushforwardUnit i (AlgebraicGeometry.finitePresentation_of_comp i f hY)
  have hci : AlgebraicGeometry.IsClosedImmersion (show Z ⟶ (situation i f).S from p) :=
    inferInstanceAs (AlgebraicGeometry.IsClosedImmersion p)
  exact finitePresentation_hom_of_representableBy_isomorphismFunctor (situation i f) p
    (e.ofIso (weilRestrictionFunctorIsoIsomorphismFunctor i f))

end Stacks.Flatness

end
