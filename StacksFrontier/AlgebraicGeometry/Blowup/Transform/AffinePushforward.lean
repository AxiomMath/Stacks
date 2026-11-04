module

public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeIso.Reduction
public import StacksFrontier.AlgebraicGeometry.AffineQcohUnit.Equivalence
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.BlowUp
public import StacksFrontier.AlgebraicGeometry.QcohLimits.RestrictScalars
public import StacksFrontier.AlgebraicGeometry.StrictTransform.Quasicoherent
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison

/-!
# Strict transforms and direct images along an affine morphism

Let `S` be a scheme, let `b : S' ⟶ S` be a morphism and let `E` be a quasi-coherent ideal sheaf
on `S'`; the motivating case is `b` the blowup of `S` in a closed subscheme and `E` the
exceptional ideal. Let `g : X ⟶ Y` be an affine morphism of schemes over `S`, let `F` be a
quasi-coherent `𝒪_X`-module, and let `g' : X ×_S S' ⟶ Y ×_S S'` be the base change of `g`. This
file proves that `g'_*` of the strict transform of `F` is the strict transform of `g_* F`.

The argument is the one of the Stacks Project. Direct image along an affine morphism commutes
with the base change `pr_Y^*`, so `g'_* pr_X^* F = pr_Y^* g_* F`; direct image along an affine
morphism is right exact on quasi-coherent modules, so applying `g'_*` to the quotient map onto
the strict transform of `F` again gives an epimorphism; that epimorphism is an isomorphism away
from the inverse image of `Supp E`, because direct image commutes with restriction to an open of
the target, and its target has no sections supported on the inverse image of `Supp E`, because a
section of a direct image supported there is a section supported on the preimage. The universal
property of the strict transform, `Stacks.StrictTransform.exists_iso`, then identifies the two.

## Main definitions

* `AlgebraicGeometry.baseChangeInducedMap`: the morphism `X ×_S S' ⟶ Y ×_S S'` induced by `g`.
* `AlgebraicGeometry.baseChangePushforwardIso`: the base-change isomorphism
  `pr_Y^* g_* F ≅ g'_* pr_X^* F` of [Stacks, Tag 02KG].
* `AlgebraicGeometry.sheafPushforwardIso`: the comparison `g'_* (strict transform of `F`) ≅`
  (strict transform of `g_* F`), for an arbitrary `b` and `E`.
* `AlgebraicGeometry.strictTransformSheafPushforwardIso`: tag 080G, that comparison for the
  blowup of an ideal sheaf and its exceptional ideal.

## Main results

* `AlgebraicGeometry.isPullback_baseChangeInducedMap`: the square formed by `g`, its base change
  and the two first projections is cartesian, so `AlgebraicGeometry.baseChangeInducedMap` is again
  affine.
* `AlgebraicGeometry.epi_pushforward_map_of_isAffineHom`: direct image along an affine morphism
  carries an epimorphism of quasi-coherent modules to an epimorphism.
* `AlgebraicGeometry.exists_sheafPushforwardIso`: the comparison isomorphism together with its
  compatibility with the two quotient maps.
* `AlgebraicGeometry.isIso_restrictFunctor_map_pushforward_map`: restriction to an open of the
  target commutes with direct image, so a morphism that is an isomorphism over the preimage of
  that open has direct image an isomorphism over it.
* `AlgebraicGeometry.supportedSections_pushforward_eq_zero`: a direct image has no nonzero
  sections supported in a subset of the target as soon as the original has none supported in its
  preimage.
* `AlgebraicGeometry.isIso_restrictFunctor_map_unit_of_section`: the unit `M ⟶ g_* g^* M` of a
  morphism with fully faithful direct image is an isomorphism over any open of the target that
  factors through `g`.

The last three are stated for an arbitrary morphism of schemes, with no affineness and no
quasi-coherence; they are the inputs the universal property of the strict transform needs
whenever the comparison morphism is a direct image, and are used again for tag 080E in
`StacksFrontier/AlgebraicGeometry/Blowup/Transform/InverseImageCentre.lean`.

## Implementation notes

The construction is given for an arbitrary `b : S' ⟶ S` and an arbitrary quasi-coherent ideal
sheaf `E` on `S'` whose support has retrocompact complement, which is how
`Stacks.StrictTransform` states the strict transform; the blowup of tag 080G is the instance
`b := AlgebraicGeometry.blowUpToBase I`, `E := AlgebraicGeometry.exceptionalIdeal I`, where the
retrocompactness hypothesis is discharged by
`Stacks.StrictTransform.quasiCompact_ι_compl_support_exceptionalIdeal`.

Right exactness of the direct image is used only through
`AlgebraicGeometry.epi_pushforward_map_of_isAffineHom`, which is weaker than preservation of
cokernels and suffices for the universal property. It is obtained from [Stacks, Tag 01SB]: direct
image is an equivalence from quasi-coherent `𝒪_X`-modules onto quasi-coherent `g_* 𝒪_X`-modules,
the inclusion of the latter into all `g_* 𝒪_X`-modules preserves epimorphisms because they are
closed under cokernels, and restriction of scalars preserves finite colimits because it is
compatible with the forgetful functor to sheaves of abelian groups.

## References

* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 080D](https://stacks.math.columbia.edu/tag/080D)
* [Stacks Project, Tag 080G](https://stacks.math.columbia.edu/tag/080G)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules Stacks.StrictTransform
open Stacks.AlgebraicGeometry.AffineQcohEquivalence Stacks.AlgebraicGeometry.AffineQcohPushforward
open Stacks.AlgebraicGeometry.QcohLimits

universe u

namespace AlgebraicGeometry

/-! ### Right exactness of the direct image along an affine morphism -/

/-- The inclusion of a full subcategory closed under cokernels preserves epimorphisms: a
morphism is an epimorphism exactly when its cokernel vanishes, and the inclusion preserves both
cokernels and the zero object. -/
private lemma preservesEpimorphisms_ι {C : Type*} [Category* C] [Abelian C]
    (P : ObjectProperty C) [P.IsClosedUnderCokernels] : P.ι.PreservesEpimorphisms where
  preserves {_ _} f hf := by
    have := P.preservesCokernels_ι f
    have hz : IsZero (cokernel f) :=
      CokernelCofork.IsColimit.isZero_of_epi (colimit.isColimit (parallelPair f 0))
    exact Preadditive.epi_of_isZero_cokernel _
      (IsZero.of_iso (P.ι.map_isZero hz) (PreservesCokernel.iso P.ι f).symm)

/-- Restriction of scalars along a morphism of sheaves of rings preserves finite colimits: it
becomes the identity after passing to the underlying sheaves of abelian groups, and that passage
both preserves and reflects finite colimits. -/
private lemma restrictScalars_preservesFiniteColimits {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {R R' : Sheaf J RingCat.{u}} (α : R ⟶ R') :
    PreservesFiniteColimits (SheafOfModules.restrictScalars.{u} α) := by
  have h : PreservesFiniteColimits
      (SheafOfModules.restrictScalars.{u} α ⋙ SheafOfModules.toSheaf R) := by
    show PreservesFiniteColimits (SheafOfModules.toSheaf.{u} R')
    exact ModuleSheafCohomology.toSheaf_preservesFiniteColimits _ R'
  have h2 : PreservesFiniteColimits (SheafOfModules.toSheaf.{u} R) :=
    ModuleSheafCohomology.toSheaf_preservesFiniteColimits _ R
  exact preservesFiniteColimits_of_reflects_of_preserves
    (SheafOfModules.restrictScalars.{u} α) (SheafOfModules.toSheaf R)

/-- Restriction of scalars along `h.toRingCatSheafHom` is additive. -/
private instance restrictScalars_additive_toRingCatSheafHom {X Y : Scheme.{u}} (h : X ⟶ Y) :
    (SheafOfModules.restrictScalars.{u} h.toRingCatSheafHom).Additive :=
  SheafOfModules.instAdditiveRestrictScalars.{u, u, u, u} h.toRingCatSheafHom

/-- Restriction of scalars along `h.toRingCatSheafHom` preserves finite colimits. -/
private instance restrictScalars_preservesFiniteColimits_toRingCatSheafHom {X Y : Scheme.{u}}
    (h : X ⟶ Y) :
    PreservesFiniteColimits (SheafOfModules.restrictScalars.{u} h.toRingCatSheafHom) :=
  restrictScalars_preservesFiniteColimits _

/-- For an affine morphism `h : X ⟶ Y`, the quasi-coherent `h_* 𝒪_X`-modules are closed under
cokernels: by **Stacks Project, Tag 01SB** quasi-coherence over `h_* 𝒪_X` is quasi-coherence of
the restriction of scalars to `𝒪_Y`, which commutes with cokernels. -/
private lemma pushforwardQuasicoherent_isClosedUnderCokernels {X Y : Scheme.{u}} (h : X ⟶ Y)
    [IsAffineHom h] :
    (SheafOfModules.isQuasicoherent
      (pushforwardRing h.base X.ringCatSheaf)).IsClosedUnderCokernels where
  cokernels_le := by
    rintro _ ⟨φ, c, hc, hA, hB⟩
    have := (affine_isQuasicoherent_restrictScalars_iff h _).mpr hA
    have := (affine_isQuasicoherent_restrictScalars_iff h _).mpr hB
    refine (SheafOfModules.isQuasicoherent (pushforwardRing h.base X.ringCatSheaf)).prop_of_iso
      (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel φ) hc) ?_
    refine (affine_isQuasicoherent_restrictScalars_iff h (cokernel φ)).mp ?_
    exact (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
      (PreservesCokernel.iso (SheafOfModules.restrictScalars.{u} h.toRingCatSheafHom) φ).symm
      (Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel
        ((SheafOfModules.restrictScalars.{u} h.toRingCatSheafHom).map φ))

/-- **Direct image along an affine morphism is right exact on quasi-coherent modules**, in the
form needed here: it carries an epimorphism of quasi-coherent modules to an epimorphism. Direct
image factors as the equivalence of **Stacks Project, Tag 01SB** onto quasi-coherent
`h_* 𝒪_X`-modules, their inclusion into all `h_* 𝒪_X`-modules, and restriction of scalars; all
three preserve epimorphisms. -/
lemma epi_pushforward_map_of_isAffineHom {X Y : Scheme.{u}} (h : X ⟶ Y) [IsAffineHom h]
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N) [Epi φ] :
    Epi ((Scheme.Modules.pushforward h).map φ) := by
  have := pushforwardQuasicoherent_isClosedUnderCokernels h
  have := preservesEpimorphisms_ι
    (SheafOfModules.isQuasicoherent (pushforwardRing h.base X.ringCatSheaf))
  have := Stacks.AlgebraicGeometry.AffineQcohUnit.isEquivalence_affineQuasicoherentPushforward h
  have hpe : (SheafOfModules.restrictScalars.{u} h.toRingCatSheafHom).PreservesEpimorphisms :=
    inferInstance
  let MQ : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory := ⟨M, inferInstance⟩
  let NQ : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory := ⟨N, inferInstance⟩
  let φQ : MQ ⟶ NQ := ⟨φ⟩
  have : Epi φQ :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.epi_of_epi_map
      (f := φQ) (inferInstanceAs (Epi φ))
  have e2 : Epi ((SheafOfModules.isQuasicoherent
      (pushforwardRing h.base X.ringCatSheaf)).ι.map
        ((affineQuasicoherentPushforward h).map φQ)) := inferInstance
  exact @Functor.PreservesEpimorphisms.preserves _ _ _ _ _ hpe _ _ _ e2

/-! ### Direct images and sections supported on a subset -/

/-- Restriction to an open `V` of the target commutes with direct image, so a morphism whose
restriction to the preimage of `V` is an isomorphism has direct image whose restriction to `V`
is an isomorphism. -/
lemma isIso_restrictFunctor_map_pushforward_map {X Y : Scheme.{u}} (h : X ⟶ Y)
    (V : Y.Opens) {W : X.Opens} (hW : h ⁻¹ᵁ V = W) {M N : X.Modules} (q : M ⟶ N)
    (hq : IsIso ((restrictFunctor W.ι).map q)) :
    IsIso ((restrictFunctor V.ι).map ((Scheme.Modules.pushforward h).map q)) := by
  subst hW
  have hqV : IsIso ((restrictFunctor (h ⁻¹ᵁ V).ι ⋙
      Scheme.Modules.pushforward (h ∣_ V)).map q) := by
    show IsIso ((Scheme.Modules.pushforward (h ∣_ V)).map
      ((restrictFunctor (h ⁻¹ᵁ V).ι).map q))
    infer_instance
  exact (NatIso.isIso_map_iff
    (Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso h V) q).mpr hqV

/-- **The unit of `g^* ⊣ g_*` is an isomorphism over an open the morphism has a section over.**
If `g : X ⟶ Y` has fully faithful direct image and an open `V` of `Y` factors through `g`, then
`M ⟶ g_* g^* M` becomes an isomorphism after restriction to `V`.

Fully faithfulness of `g_*` makes `g^*` of the unit an isomorphism; pulling that back along the
section `h : V ⟶ X` and using `h ≫ g = ι_V` identifies the result with `ι_V^*` of the unit,
which is its restriction to `V`. -/
lemma isIso_restrictFunctor_map_unit_of_section {X Y : Scheme.{u}} (g : X ⟶ Y)
    [(Scheme.Modules.pushforward g).Full] [(Scheme.Modules.pushforward g).Faithful]
    (V : Y.Opens) (h : V.toScheme ⟶ X) (hh : h ≫ g = V.ι) (M : Y.Modules) :
    IsIso ((restrictFunctor V.ι).map
      ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M)) := by
  have h1 : IsIso (((Scheme.Modules.pullback g) ⋙ Scheme.Modules.pullback h).map
      ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M)) := by
    show IsIso ((Scheme.Modules.pullback h).map ((Scheme.Modules.pullback g).map _))
    infer_instance
  have h2 : IsIso ((Scheme.Modules.pullback V.ι).map
      ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M)) :=
    (NatIso.isIso_map_iff (Scheme.Modules.pullbackComp h g ≪≫ Scheme.Modules.pullbackCongr hh)
      ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M)).mp h1
  exact (NatIso.isIso_map_iff (restrictFunctorIsoPullback V.ι)
    ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M)).mpr h2

/-- A section of a direct image `h_* T` over `U` supported in a subset `Z` of the target is, as
a section of `T` over `h^{-1}(U)`, supported in `h^{-1}(Z)`; so if `T` has no nonzero sections
supported in `h^{-1}(Z)` then `h_* T` has none supported in `Z`. -/
lemma supportedSections_pushforward_eq_zero {X Y : Scheme.{u}} (h : X ⟶ Y) (Z : Set Y)
    {Z' : Set X} (hZ' : h.base ⁻¹' Z = Z') (T : X.Modules)
    (hT : ∀ (W : X.Opens) (t : Γ(T, W)),
      t ∈ (supportedSectionsSubmodule Z' T).toSubmodule.obj (op W) → t = 0)
    (U : Y.Opens) (s : Γ((Scheme.Modules.pushforward h).obj T, U))
    (hs : s ∈ (supportedSectionsSubmodule Z
      ((Scheme.Modules.pushforward h).obj T)).toSubmodule.obj (op U)) :
    s = 0 := by
  subst hZ'
  rw [mem_supportedSectionsSubmodule_iff Z ((Scheme.Modules.pushforward h).obj T) U s] at hs
  refine hT (h ⁻¹ᵁ U) s ((mem_supportedSectionsSubmodule_iff
    (h.base ⁻¹' Z) T (h ⁻¹ᵁ U) s).mpr fun x hx hxZ ↦ ?_)
  obtain ⟨W, hxW, i, j, heq⟩ :=
    ((Scheme.Modules.pushforward h).obj T).presheaf.germ_eq (h.base x) hx hx s 0
      ((hs (h.base x) hx hxZ).trans (map_zero _).symm)
  have hpre : h ⁻¹ᵁ W ≤ h ⁻¹ᵁ U := Scheme.Hom.preimage_mono h i.le
  have hres : T.val.presheaf.map (homOfLE hpre).op s = 0 := by
    have h1 : (Opens.map h.base).map i = homOfLE hpre := Subsingleton.elim _ _
    have h2 : (Opens.map h.base).map j = homOfLE hpre := Subsingleton.elim _ _
    rw [Scheme.Modules.pushforward_obj_presheaf_map, Scheme.Modules.pushforward_obj_presheaf_map,
      h1, h2] at heq
    exact heq.trans (map_zero _)
  refine (TopCat.Presheaf.germ_res_apply T.val.presheaf (homOfLE hpre) x hxW s).symm.trans ?_
  rw [hres, map_zero]

/-! ### The base change of an affine morphism over the base -/

variable {X Y S S' : Scheme.{u}} (g : X ⟶ Y) (f : Y ⟶ S) (b : S' ⟶ S) (E : S'.IdealSheafData)

/-- The morphism `X ×_S S' ⟶ Y ×_S S'` induced by a morphism `g : X ⟶ Y` over `S`. -/
def baseChangeInducedMap : baseChange (g ≫ f) b ⟶ baseChange f b :=
  pullback.lift (pullback.fst (g ≫ f) b ≫ g) (pullback.snd (g ≫ f) b)
    (by rw [Category.assoc, pullback.condition])

/-- Composing `AlgebraicGeometry.baseChangeInducedMap` with the projection to `Y` gives the
projection to `X` followed by `g`. -/
lemma baseChangeInducedMap_fst :
    baseChangeInducedMap g f b ≫ pullback.fst f b = pullback.fst (g ≫ f) b ≫ g :=
  pullback.lift_fst _ _ _

/-- `AlgebraicGeometry.baseChangeInducedMap` is a morphism over `S'`. -/
lemma baseChangeInducedMap_snd :
    baseChangeInducedMap g f b ≫ pullback.snd f b = pullback.snd (g ≫ f) b :=
  pullback.lift_snd _ _ _

/-- The square formed by `g`, `AlgebraicGeometry.baseChangeInducedMap` and the two projections to
`X` and `Y` is cartesian: it is the top square of the two pasted base-change squares whose
composite is the base change of `g ≫ f`. -/
lemma isPullback_baseChangeInducedMap :
    IsPullback (pullback.fst (g ≫ f) b) (baseChangeInducedMap g f b) g (pullback.fst f b) := by
  refine IsPullback.flip (IsPullback.of_right ?_ (baseChangeInducedMap_fst g f b)
    (IsPullback.of_hasPullback f b).flip)
  rw [baseChangeInducedMap_snd]
  exact (IsPullback.of_hasPullback (g ≫ f) b).flip

/-- The base change of an affine morphism over the base is affine. -/
instance isAffineHom_baseChangeInducedMap [IsAffineHom g] :
    IsAffineHom (baseChangeInducedMap g f b) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (isPullback_baseChangeInducedMap g f b)
    inferInstance

/-- The inverse image under `AlgebraicGeometry.baseChangeInducedMap` of the complement of
`pr_{S'}^{-1}(Supp E)` in `Y ×_S S'` is its counterpart in `X ×_S S'`, both projections to `S'`
being the same morphism up to `AlgebraicGeometry.baseChangeInducedMap`. -/
lemma preimage_exceptionalComplement_baseChangeInducedMap :
    baseChangeInducedMap g f b ⁻¹ᵁ exceptionalComplement f b E =
      exceptionalComplement (g ≫ f) b E := by
  rw [show exceptionalComplement f b E = pullback.snd f b ⁻¹ᵁ E.support.compl from rfl,
    ← Scheme.Hom.comp_preimage, baseChangeInducedMap_snd]

/-- The inverse image under `AlgebraicGeometry.baseChangeInducedMap` of `pr_{S'}^{-1}(Supp E)` in
`Y ×_S S'`, written as the complement of the open complement, is its counterpart in
`X ×_S S'`. -/
private lemma preimage_compl_exceptionalComplement_baseChangeInducedMap :
    (baseChangeInducedMap g f b).base ⁻¹' ((exceptionalComplement f b E : Set (baseChange f b)))ᶜ =
      exceptionalPreimage (g ≫ f) b E := by
  rw [Set.preimage_compl,
    show (baseChangeInducedMap g f b).base ⁻¹'
        ((exceptionalComplement f b E : Set (baseChange f b))) =
      ((baseChangeInducedMap g f b ⁻¹ᵁ exceptionalComplement f b E : (baseChange (g ≫ f) b).Opens) :
        Set (baseChange (g ≫ f) b)) from rfl,
    preimage_exceptionalComplement_baseChangeInducedMap g f b E,
    ← exceptionalPreimage_eq_compl (g ≫ f) b E]

/-- **Stacks Project, Tag 02KG** for the cartesian square of
`AlgebraicGeometry.isPullback_baseChangeInducedMap`: the base-change morphism
`pr_Y^* g_* F ⟶ g'_* pr_X^* F` is an isomorphism, `g` being affine and `F` quasi-coherent. -/
def baseChangePushforwardIso [IsAffineHom g] (F : X.Modules) [F.IsQuasicoherent] :
    (Scheme.Modules.pullback (pullback.fst f b)).obj ((Scheme.Modules.pushforward g).obj F) ≅
      (Scheme.Modules.pushforward (baseChangeInducedMap g f b)).obj
        ((Scheme.Modules.pullback (pullback.fst (g ≫ f) b)).obj F) :=
  have := Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom
    (isPullback_baseChangeInducedMap g f b) F
  asIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans
    (isPullback_baseChangeInducedMap g f b).w).app F)

/-! ### The comparison of the strict transform with the direct image -/

/-- **Direct image along an affine morphism commutes with strict transform**: the direct image
along `g'` of the quotient map onto the strict transform of `F`, composed with the base-change
isomorphism, is the quotient map onto the strict transform of `g_* F`.

This is the universal property `Stacks.StrictTransform.exists_iso` applied to that composite:
it is an epimorphism by `AlgebraicGeometry.epi_pushforward_map_of_isAffineHom`, it becomes an
isomorphism away from `pr_{S'}^{-1}(Supp E)` by
`AlgebraicGeometry.isIso_restrictFunctor_map_pushforward_map`, and its target has no sections
supported there by `AlgebraicGeometry.supportedSections_pushforward_eq_zero`. -/
lemma exists_sheafPushforwardIso [IsAffineHom g]
    [QuasiCompact (Scheme.Opens.ι E.support.compl)] (F : X.Modules) [F.IsQuasicoherent] :
    ∃ e : sheaf f b E ((Scheme.Modules.pushforward g).obj F) ≅
        (Scheme.Modules.pushforward (baseChangeInducedMap g f b)).obj (sheaf (g ≫ f) b E F),
      π f b E ((Scheme.Modules.pushforward g).obj F) ≫ e.hom =
        (baseChangePushforwardIso g f b F).hom ≫
          (Scheme.Modules.pushforward (baseChangeInducedMap g f b)).map (π (g ≫ f) b E F) := by
  have hepi : Epi ((Scheme.Modules.pushforward (baseChangeInducedMap g f b)).map
      (π (g ≫ f) b E F)) :=
    epi_pushforward_map_of_isAffineHom _ _
  have hres : IsIso ((restrictFunctor (exceptionalComplement f b E).ι).map
      ((Scheme.Modules.pushforward (baseChangeInducedMap g f b)).map (π (g ≫ f) b E F))) :=
    isIso_restrictFunctor_map_pushforward_map _ _
      (preimage_exceptionalComplement_baseChangeInducedMap g f b E) _
      (isIso_restrictFunctor_map_π (g ≫ f) b E F)
  have hiso : IsIso ((restrictFunctor (exceptionalComplement f b E).ι).map
      ((baseChangePushforwardIso g f b F).hom ≫
        (Scheme.Modules.pushforward (baseChangeInducedMap g f b)).map (π (g ≫ f) b E F))) := by
    rw [Functor.map_comp]
    infer_instance
  have hmono : Mono ((restrictAdjunction (exceptionalComplement f b E).ι).unit.app
      ((Scheme.Modules.pushforward (baseChangeInducedMap g f b)).obj (sheaf (g ≫ f) b E F))) :=
    mono_unit_app_of_supportedSections_eq_zero _ _ fun U s hs ↦
      supportedSections_pushforward_eq_zero _ _
        (preimage_compl_exceptionalComplement_baseChangeInducedMap g f b E) _
        (supportedSections_sheaf_eq_zero (g ≫ f) b E F) U s hs
  exact exists_iso f b E ((Scheme.Modules.pushforward g).obj F) _

/-- **Direct image along an affine morphism commutes with strict transform.** For `g : X ⟶ Y`
an affine morphism over `S` and `F` a quasi-coherent `𝒪_X`-module, the direct image along the
base change `g' : X ×_S S' ⟶ Y ×_S S'` of the strict transform of `F` is the strict transform of
`g_* F`. -/
def sheafPushforwardIso [IsAffineHom g] [QuasiCompact (Scheme.Opens.ι E.support.compl)]
    (F : X.Modules) [F.IsQuasicoherent] :
    (Scheme.Modules.pushforward (baseChangeInducedMap g f b)).obj (sheaf (g ≫ f) b E F) ≅
      sheaf f b E ((Scheme.Modules.pushforward g).obj F) :=
  (exists_sheafPushforwardIso g f b E F).choose.symm

/-- **Stacks Project, Tag 080G.** Let `b : S' ⟶ S` be the blowup of `S` in a closed subscheme
cut out by the quasi-coherent ideal sheaf `I`, let `g : X ⟶ Y` be an affine morphism of schemes
over `S`, let `F` be a quasi-coherent `𝒪_X`-module and let `g' : X ×_S S' ⟶ Y ×_S S'` be the
base change of `g`. Then `g'_*` of the strict transform of `F` relative to `b` is the strict
transform of `g_* F`. -/
@[stacks 080G]
def strictTransformSheafPushforwardIso {X Y S : Scheme.{u}}
    (g : X ⟶ Y) (f : Y ⟶ S) (I : S.IdealSheafData)
    (F : X.Modules) [IsAffineHom g] [F.IsQuasicoherent] :
    let g' : Stacks.StrictTransform.baseChange (g ≫ f) (blowUpToBase I) ⟶
        Stacks.StrictTransform.baseChange f (blowUpToBase I) :=
      pullback.lift
        (pullback.fst (g ≫ f) (blowUpToBase I) ≫ g)
        (pullback.snd (g ≫ f) (blowUpToBase I))
        (by rw [Category.assoc]; exact pullback.condition)
    (Scheme.Modules.pushforward g').obj
        (Stacks.StrictTransform.sheaf (g ≫ f) (blowUpToBase I) (exceptionalIdeal I) F) ≅
      Stacks.StrictTransform.sheaf f (blowUpToBase I) (exceptionalIdeal I)
        ((Scheme.Modules.pushforward g).obj F) :=
  sheafPushforwardIso g f (blowUpToBase I) (exceptionalIdeal I) F

end AlgebraicGeometry

end
