module

public import StacksFrontier.Deformation.ToposThickening.ExtensionPushoutComparison
public import StacksFrontier.Deformation.ToposThickening.ObstructionCompatibility
public import StacksFrontier.Deformation.ToposThickening.ThickeningComplexBoundaryPushout
public import StacksFrontier.Deformation.ToposThickening.ThickeningComplexTrivialization

/-!
# Stacks 08MM: the boundary of `ξ_{F'₁}` is the obstruction class `o(F, K₃, c₃)`

Let `(Sh(C), O)` be a ringed topos, `F` an `O`-module and
`(Sh(D₁), O'₁) ⟶ (Sh(D₂), O'₂) ⟶ (Sh(D₃), O'₃)` a complex of first order thickenings of
`(Sh(C), O)` (Stacks 08ML). Let `(Kₖ, cₖ)` be pairs with `cₖ : Iₖ ⊗_O F ⟶ Kₖ`, let
`0 ⟶ K₃ ⟶ K₂ ⟶ K₁ ⟶ 0` be a short exact sequence of `O`-modules compatible with the `cₖ`
through the two squares of the remark, and let `F'₂` be an extension of `F` by `K₂` over `O'₂` as
in Stacks 08MB with `c_{F'₂} = c₂`. Remark **Stacks 08MM** claims that the boundary
`∂ : Ext¹_O(F, K₁) ⟶ Ext²_O(F, K₃)` of the short exact sequence carries the class `ξ_{F'₁}` of
Stacks 08MI of the extension `F'₁` that Stacks 08MJ produces from `F'₂`, formed with the canonical
splitting `π` of Stacks 08ML, to the obstruction class `o(F, K₃, c₃)` of Stacks 08MF.

This file proves the claim under exactly those hypotheses.

## Main results

* `Deformation.ToposThickening.splittingRingHom_trivializationOfBaseSplitting`: the splitting
  `O ⟶ O'` of the structure map supplied by the trivialization built from a section `s` of the
  structure map is `s` again.
* `Deformation.ToposThickening.FirstOrderThickeningComplex`
  `.upper_ringMapH_comp_lower_ringMapH_eq_trivialization`: for the canonical trivialization
  `π = S.trivialization hS` of Stacks 08ML, the composite `O'₃ ⟶ O'₂ ⟶ O'₁` is
  `O'₃ ⟶ O ⟶ O'₁` through the splitting that `π` supplies.
* `Deformation.ToposThickening.MorphismOfFirstOrderThickenings.PushoutExtensionData`
  `.f_comp_comparisonMap` and `.comparisonMap_comp_g`: the canonical map `F'₂ ⟶ F'₁` of
  Stacks 08MJ is a map of extensions, `K₂ ⟶ K₁` on kernel modules and the identity on `F`.
* `Deformation.ToposThickening.FirstOrderThickeningComplex`
  `.boundary_underlyingExtensionClass_eq_obstructionClass`: **Stacks 08MM** for every extension
  `F'₁` over `O'₁` receiving a map of extensions from `F'₂` which is `K₂ ⟶ K₁` on kernel modules
  and the identity on `F`.
* `Deformation.ToposThickening.FirstOrderThickeningComplex`
  `.boundary_underlyingExtensionClass_extensionOne_eq_obstructionClass`: **Stacks 08MM** for
  `F'₁` the extension that Stacks 08MJ constructs from `F'₂`
  (`Deformation.ToposThickening.MorphismOfFirstOrderThickenings.PushoutExtensionData`
  `.extensionOne`).

## Implementation notes

The proof follows the source's. The extension `E'₃` (`F'₂` read over `O'₃` through
`O'₃ ⟶ O'₂`, with `c_{E'₃} = c₃ ≫ (K₃ ⟶ K₂)` by
`Deformation.ToposThickening.MorphismOfFirstOrderThickenings.restrictedExtension_actionMap`), a
presentation of the obstruction class at `O'₃` mapping to it, and the comparison map from that
presentation to `F'₁` are all constructed by
`Deformation.ToposThickening.FirstOrderThickeningComplex`
`.boundary_underlyingExtensionClass_of_pushout`
(`StacksFrontier/Deformation/ToposThickening/ThickeningComplexBoundaryPushout.lean`), which takes
the trivialization `π` of `O'₁` together with the factorization of `O'₃ ⟶ O'₁` through it; where
the source enlarges `K₃` into an injective module to make the action map injective, that proof
takes a common refinement of `E'₃` with an extension whose action map is already injective, the
obstruction class being computed by any presentation. Here `π` is the canonical trivialization
`S.trivialization hS` of Stacks 08ML
(`StacksFrontier/Deformation/ToposThickening/ThickeningComplexTrivialization.lean`), and the
factorization is proved for it: the trivialization is built from the canonical map
`S.splitting hS : O ⟶ O'₁`, through which `O'₃ ⟶ O'₁` factors by Stacks 08ML, and
`splittingRingHom_trivializationOfBaseSplitting` shows that the splitting it supplies back is
that map.

As in the ringed-space form of the claim
(`AlgebraicGeometry.RingedSpaceThickening.boundary_underlyingExtensionClass_eq_obstructionClass`),
the version for an arbitrary `F'₁` receiving a map from `F'₂` omits `c₁` and the first square:
they are the input of Stacks 08MJ, and once `F'₁` and the map are given the identity of classes
does not use them. The version for the extension of Stacks 08MJ takes both, as the remark does.

The construction of the `O'₁`-module structure on the pushout in Stacks 08MJ narrows the
universe of sections on the site of the thickenings to `max v₂ u₂` (see the implementation notes
of `StacksFrontier/Deformation/ToposThickening/ExtensionPushout.lean`), so the second version is
stated at that universe; the base ringed topos is unconstrained.

## References

* [Stacks Project, Tag 08MM](https://stacks.math.columbia.edu/tag/08MM)
* [Stacks Project, Tag 08ML](https://stacks.math.columbia.edu/tag/08ML)
* [Stacks Project, Tag 08MJ](https://stacks.math.columbia.edu/tag/08MJ)
* [Stacks Project, Tag 08MI](https://stacks.math.columbia.edu/tag/08MI)
* [Stacks Project, Tag 08MF](https://stacks.math.columbia.edu/tag/08MF)
* [Stacks Project, Tag 08MB](https://stacks.math.columbia.edu/tag/08MB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor inverseImageCommRingFunctor
  commRingImageAdjunction pushforwardCommRingFunctor_isEquivalence)

universe v u w v' u' w' v₂ u₂ e

namespace Deformation.ToposThickening

section Splitting

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  {i : RingedToposHom X Y}

/-- **The splitting supplied by the trivialization built from a section is that section.** Let
`s : O ⟶ O'` be a section of the structure map of a first order thickening, read on the topos of
the thickening. The trivialization `trivializationOfBaseSplitting` built from `s` supplies, by
Stacks 08MG, a splitting `O ⟶ O'` of the structure map; it is `s`.

The retraction of that trivialization has direct image `i⁻¹` and structure map
`O ≅ i⁻¹i_*O ⟶ i⁻¹O'`, the inverse of the counit followed by `i⁻¹s`; the splitting of Stacks 08MG
is the map whose direct image along the retraction is the structure map of the retraction
precomposed with the comparison `i⁻¹i_*O ≅ O` of the round trip, and on underlying sheaves of
sets that comparison is the counit. -/
theorem splittingRingHom_trivializationOfBaseSplitting (hi : FirstOrderThickening i)
    (s : (pushforwardCommRingFunctor i.toToposHom).obj X.O ⟶ Y.O) (hs : s ≫ i.fSharp = 𝟙 _) :
    splittingRingHom i hi (trivializationOfBaseSplitting i hi.equiv s hs) =
      (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map s := by
  have : i.toToposHom.pushforward.IsEquivalence := hi.equiv
  let π := trivializationOfBaseSplitting i hi.equiv s hs
  have hj : π.retraction.toToposHom.pushforward.IsEquivalence := by
    change i.toToposHom.inverseImage.IsEquivalence
    exact i.toToposHom.adj.isEquivalence_left_of_isEquivalence_right
  have := pushforwardCommRingFunctor_isEquivalence π.retraction.toToposHom hj
  have : (pushforwardCommRingFunctor i.toToposHom).IsEquivalence :=
    pushforwardCommRingFunctor_isEquivalence i.toToposHom hi.equiv
  unfold splittingRingHom
  congr 1
  apply (pushforwardCommRingFunctor π.retraction.toToposHom).map_injective
  unfold splittingFromTrivialization
  dsimp only
  have hcancel : ∀ {A B : Sheaf Y.J CommRingCat.{w'}} (f : A ⟶ B),
      Sheaf.homEquiv.symm f.hom = f := fun _ ↦ rfl
  rw [hcancel, Functor.FullyFaithful.map_preimage]
  have hε : IsIso ((commRingImageAdjunction i.toToposHom).counit.app X.O) := inferInstance
  have h1 : X.forgetRing.map π.retraction.fSharp =
      inv (X.forgetRing.map ((commRingImageAdjunction i.toToposHom).counit.app X.O)) ≫
        i.toToposHom.inverseImage.map (Y.forgetRing.map s) := by
    refine (X.forgetRing.map_comp
      (inv ((commRingImageAdjunction i.toToposHom).counit.app X.O))
      ((inverseImageCommRingFunctor i.toToposHom).map s)).trans ?_
    rw [Functor.map_inv]
    exact congrArg (fun m => inv (X.forgetRing.map
      ((commRingImageAdjunction i.toToposHom).counit.app X.O)) ≫ m)
      (Stacks.Sheaves.ToposPullback.underlyingRingSheaf_map_pullbackCommRingSheafMap X.J _ s)
  have hid : i.toToposHom.inverseImage.map (Y.forgetRing.map s) ≫
      i.toToposHom.inverseImage.map (Y.forgetRing.map i.fSharp) = 𝟙 _ := by
    rw [← i.toToposHom.inverseImage.map_comp, ← Y.forgetRing.map_comp, hs,
      CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  have hc : X.forgetRing.map (π.retraction.comp i).fSharp =
      inv (X.forgetRing.map ((commRingImageAdjunction i.toToposHom).counit.app X.O)) := by
    refine (AlgebraicGeometry.RingedToposHom.comp_fSharp_forget _ _).trans ?_
    refine (congrArg (fun m => m ≫ i.toToposHom.inverseImage.map (Y.forgetRing.map i.fSharp))
      h1).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun m => inv (X.forgetRing.map
      ((commRingImageAdjunction i.toToposHom).counit.app X.O)) ≫ m) hid).trans ?_
    exact Category.comp_id _
  have : IsIso (π.retraction.comp i).fSharp := by
    have : IsIso (X.forgetRing.map (π.retraction.comp i).fSharp) := by
      rw [hc]
      have h := Functor.map_isIso X.forgetRing
        ((commRingImageAdjunction i.toToposHom).counit.app X.O)
      exact @IsIso.inv_isIso _ _ _ _ _ h
    exact isIso_of_reflects_iso _ X.forgetRing
  have hβ : (Stacks.Sheaves.ToposPushforward.pushforwardCommRingCompIso i.toToposHom
      π.retraction.toToposHom X.O ≪≫ (asIso (π.retraction.comp i).fSharp).symm).hom =
      (commRingImageAdjunction i.toToposHom).counit.app X.O := by
    apply X.forgetRing.map_injective
    refine (X.forgetRing.map_comp _ _).trans ?_
    rw [Stacks.Sheaves.ToposPushforward.pushforwardCommRingCompIso_hom_forget]
    refine (Category.id_comp _).trans ?_
    change X.forgetRing.map (inv (π.retraction.comp i).fSharp) = _
    rw [Functor.map_inv]
    refine IsIso.inv_eq_of_hom_inv_id ?_
    rw [hc]
    exact @IsIso.inv_hom_id _ _ _ _ _ (Functor.map_isIso X.forgetRing
      ((commRingImageAdjunction i.toToposHom).counit.app X.O))
  exact (congrArg (fun m => m ≫ π.retraction.fSharp) hβ).trans
    (IsIso.hom_inv_id_assoc (I := hε) _ _)

end Splitting

namespace FirstOrderThickeningComplex

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  {i : RingedToposHom X Y} (S : FirstOrderThickeningComplex i) (hS : S.IsComplex)

/-- The splitting `O ⟶ O'₁` supplied by the canonical trivialization of Stacks 08ML is the
canonical map `S.splitting hS` through which `O'₃ ⟶ O'₁` factors. -/
theorem splittingRingHom_trivialization :
    splittingRingHom i S.lower.first (S.trivialization hS) =
      (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map (S.splitting hS) :=
  splittingRingHom_trivializationOfBaseSplitting S.lower.first (S.splitting hS)
    (S.splitting_comp_fSharp hS)

/-- **The composite `O'₃ ⟶ O'₂ ⟶ O'₁` factors through the canonical splitting.** On underlying
sheaves of rings, the composite of the two morphisms of a complex of first order thickenings is
`O'₃ ⟶ O ⟶ O'₁`, with `O ⟶ O'₁` the splitting supplied by the canonical trivialization
`S.trivialization hS` of Stacks 08ML. -/
theorem upper_ringMapH_comp_lower_ringMapH_eq_trivialization :
    S.upper.ringMapH ≫ S.lower.ringMapH =
      S.whole.ringMap₂ ≫ splittingRingHom i S.lower.first (S.trivialization hS) := by
  rw [S.splittingRingHom_trivialization hS]
  change (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map S.h₃₂ ≫
      (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map S.lower.hSharp =
    (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map S.fSharp₃ ≫ _
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    S.fSharp₃_comp_splitting hS]
  rfl

section Boundary

variable [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasSheafify Y.J AddCommGrpCat.{w'}] [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
  [HasExt.{e} (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)))]
  [HasExt.{e} (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf S.O₃))]

/-- **Stacks Project, Tag 08MM.** Let `(Sh(C), O)` be a ringed topos, `F` an `O`-module and
`O'₃ ⟶ O'₂ ⟶ O'₁` a complex of first order thickenings of `(Sh(C), O)` (Stacks 08ML), presented
on one site. Let `cₖ : Iₖ ⊗_O F ⟶ Kₖ` be maps and `0 ⟶ K₃ ⟶ K₂ ⟶ K₁ ⟶ 0` a short exact sequence
of `O`-modules for which the second square `hc₃₂` of the remark commutes. Let `F'₂` be an
extension `0 ⟶ K₂ ⟶ F'₂ ⟶ F ⟶ 0` over `O'₂` as in Stacks 08MB with `c_{F'₂} = c₂`, and let
`F'₁` be the extension over `O'₁` that the functoriality of Stacks 08MJ produces from it. That
functoriality carries `F'₂` to an extension of `F` by `K₁` over `O'₁` together with a map of
extensions `u` from `F'₂`, which is `K₂ ⟶ K₁` on kernel modules and the identity on `F`; the
statement is made for every extension `F'₁` receiving such a map, so in particular for the one
of Stacks 08MJ (`boundary_underlyingExtensionClass_extensionOne_eq_obstructionClass`).

Then the boundary map `∂ : Ext¹_O(F, K₁) ⟶ Ext²_O(F, K₃)` of `0 ⟶ K₃ ⟶ K₂ ⟶ K₁ ⟶ 0` — Yoneda
composition with the class of that sequence — sends the class `ξ_{F'₁}` of Stacks 08MI, formed
with the canonical splitting `π = S.trivialization hS` of Stacks 08ML, to the obstruction class
`o(F, K₃, c₃)` of Stacks 08MF.

The map `c₁` and the first compatibility square of the remark are what make Stacks 08MJ
applicable; once `F'₁` and `u` are given they are not needed for the identity of classes, so they
are not hypotheses here. They are hypotheses of the version for the extension that Stacks 08MJ
constructs. -/
@[stacks 08MM]
theorem boundary_underlyingExtensionClass_eq_obstructionClass
    (F K₁ K₂ K₃ : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)))
    (k₃₂ : K₃ ⟶ K₂) (k₂₁ : K₂ ⟶ K₁) (hk : k₃₂ ≫ k₂₁ = 0)
    (hK : (ShortComplex.mk k₃₂ k₂₁ hk).ShortExact)
    (c₂ : ((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).obj S.lower.second.I).obj F ⟶
      K₂)
    (c₃ : ((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).obj S.third.I).obj F ⟶ K₃)
    (hc₃₂ : c₃ ≫ k₃₂ =
      ((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).map S.idealMap₃₂).app F ≫ c₂)
    (E₂ : Abelian.YonedaExtension
      ((structureRestrict (reshapeHom i S.lower.O₂ S.lower.fSharp₂)).obj F)
      ((structureRestrict (reshapeHom i S.lower.O₂ S.lower.fSharp₂)).obj K₂) 0)
    (hE₂ : (extensionActionMap S.lower.second E₂).1 = c₂)
    (E₁ : Abelian.YonedaExtension ((structureRestrict i).obj F)
      ((structureRestrict i).obj K₁) 0)
    (u : E₂.Z.left ⟶ (S.lower.restrictedExtension E₁).Z.left)
    (hu : E₂.f ≫ u =
      (structureRestrict (reshapeHom i S.lower.O₂ S.lower.fSharp₂)).map k₂₁ ≫
        (S.lower.restrictedExtension E₁).f)
    (hug : u ≫ (S.lower.restrictedExtension E₁).g = E₂.g) :
    (underlyingExtensionClass i S.lower.first (S.trivialization hS) F K₁ E₁).comp hK.extClass
        (by decide) =
      existenceObstructionClass S.third F K₃ c₃ :=
  S.boundary_underlyingExtensionClass_of_pushout hS (S.trivialization hS)
    (S.upper_ringMapH_comp_lower_ringMapH_eq_trivialization hS) F K₁ K₂ K₃ c₂ c₃ k₃₂ k₂₁ hk hK
    hc₃₂ E₂ hE₂ E₁ u hu hug

end Boundary

end FirstOrderThickeningComplex

section PushoutExtension

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v₂, u₂, max v₂ u₂}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{max v₂ u₂})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{max v₂ u₂} RingCat.{max v₂ u₂})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{max v₂ u₂}]
  [HasSheafify Y.J AddCommGrpCat.{max v₂ u₂}]
  [HasWeakSheafify Y.J AddCommGrpCat.{max v₂ u₂}]
  {i : RingedToposHom X Y}

namespace MorphismOfFirstOrderThickenings.PushoutExtensionData

variable {D : MorphismOfFirstOrderThickenings i} (dat : D.PushoutExtensionData)
  (E₂ : Abelian.YonedaExtension ((SheafOfModules.restrictScalars D.ringMap₂).obj dat.F)
    ((SheafOfModules.restrictScalars D.ringMap₂).obj dat.K₂) 0)
  (hE₂ : (extensionActionMap D.second E₂).1 = dat.c₂)

/-- **The canonical map of Stacks 08MJ is the map of kernel modules on kernel modules**: the
canonical map `F'₂ ⟶ F'₁`, read over `O'₂` along `h^♯`, restricts to `κ : K₂ ⟶ K₁`. -/
theorem f_comp_comparisonMap :
    E₂.f ≫ dat.comparisonMap E₂ hE₂ =
      (SheafOfModules.restrictScalars D.ringMap₂).map dat.kernelMap ≫
        (D.restrictedExtension (dat.extensionOne E₂ hE₂)).f :=
  SheafOfModules.hom_ext <| PresheafOfModules.hom_ext fun U ↦ ModuleCat.hom_ext <|
    LinearMap.ext fun k ↦ dat.comparisonSection_f E₂ hE₂ U k

/-- **The canonical map of Stacks 08MJ is the identity on `F`**: the canonical map `F'₂ ⟶ F'₁`,
read over `O'₂` along `h^♯`, commutes with the two quotient maps onto `F`. -/
theorem comparisonMap_comp_g :
    dat.comparisonMap E₂ hE₂ ≫ (D.restrictedExtension (dat.extensionOne E₂ hE₂)).g = E₂.g :=
  SheafOfModules.hom_ext <| PresheafOfModules.hom_ext fun U ↦ ModuleCat.hom_ext <|
    LinearMap.ext fun x ↦ dat.extQuotOne_comparisonSection E₂ hE₂ U x

end MorphismOfFirstOrderThickenings.PushoutExtensionData

namespace FirstOrderThickeningComplex

variable (S : FirstOrderThickeningComplex i) (hS : S.IsComplex)
  [HasExt.{e} (SheafOfModules.{max v₂ u₂} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)))]
  [HasExt.{e} (SheafOfModules.{max v₂ u₂} (Stacks.SheafOfModules.Tensor.ringSheaf S.O₃))]

/-- **Stacks Project, Tag 08MM**, for the extension `F'₁` that Stacks 08MJ constructs. Let
`(Sh(C), O)` be a ringed topos, `F` an `O`-module and `O'₃ ⟶ O'₂ ⟶ O'₁` a complex of first order
thickenings of `(Sh(C), O)` (Stacks 08ML), presented on one site. Let `(Kₖ, cₖ)`,
`k = 1, 2, 3`, be pairs of an `O`-module `Kₖ` and a map `cₖ : Iₖ ⊗_O F ⟶ Kₖ`, and let
`0 ⟶ K₃ ⟶ K₂ ⟶ K₁ ⟶ 0` be a short exact sequence of `O`-modules making the two squares `hc₂₁`
and `hc₃₂` of the remark commute. Let `F'₂` be an extension `0 ⟶ K₂ ⟶ F'₂ ⟶ F ⟶ 0` of
`O'₂`-modules as in Stacks 08MB with `c_{F'₂} = c₂`, and let `F'₁` be the extension of
`O'₁`-modules that the functoriality of Stacks 08MJ produces from it
(`MorphismOfFirstOrderThickenings.PushoutExtensionData.extensionOne`, built on the data
`(F, K₁, K₂, c₁, c₂, K₂ ⟶ K₁)` and the first square).

Then the boundary map `∂ : Ext¹_O(F, K₁) ⟶ Ext²_O(F, K₃)` of `0 ⟶ K₃ ⟶ K₂ ⟶ K₁ ⟶ 0` sends the
class `ξ_{F'₁}` of Stacks 08MI, formed with the canonical splitting `π = S.trivialization hS` of
Stacks 08ML, to the obstruction class `o(F, K₃, c₃)` of Stacks 08MF. -/
@[stacks 08MM]
theorem boundary_underlyingExtensionClass_extensionOne_eq_obstructionClass
    (F K₁ K₂ K₃ :
      SheafOfModules.{max v₂ u₂} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)))
    (c₁ : ((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).obj S.lower.first.I).obj F ⟶
      K₁)
    (c₂ : ((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).obj S.lower.second.I).obj F ⟶
      K₂)
    (c₃ : ((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).obj S.third.I).obj F ⟶ K₃)
    (k₃₂ : K₃ ⟶ K₂) (k₂₁ : K₂ ⟶ K₁) (hk : k₃₂ ≫ k₂₁ = 0)
    (hK : (ShortComplex.mk k₃₂ k₂₁ hk).ShortExact)
    (hc₂₁ : c₂ ≫ k₂₁ =
      ((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).map S.idealMap₂₁).app F ≫ c₁)
    (hc₃₂ : c₃ ≫ k₃₂ =
      ((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).map S.idealMap₃₂).app F ≫ c₂)
    (E₂ : Abelian.YonedaExtension
      ((structureRestrict (reshapeHom i S.lower.O₂ S.lower.fSharp₂)).obj F)
      ((structureRestrict (reshapeHom i S.lower.O₂ S.lower.fSharp₂)).obj K₂) 0)
    (hE₂ : (extensionActionMap S.lower.second E₂).1 = c₂) :
    (underlyingExtensionClass i S.lower.first (S.trivialization hS) F K₁
        ((S.lower.pushoutDataOfPushout c₂ c₁ k₂₁ hc₂₁).extensionOne E₂ hE₂)).comp
        hK.extClass (by decide) =
      existenceObstructionClass S.third F K₃ c₃ :=
  S.boundary_underlyingExtensionClass_eq_obstructionClass hS F K₁ K₂ K₃ k₃₂ k₂₁ hk hK c₂ c₃
    hc₃₂ E₂ hE₂ _ ((S.lower.pushoutDataOfPushout c₂ c₁ k₂₁ hc₂₁).comparisonMap E₂ hE₂)
    ((S.lower.pushoutDataOfPushout c₂ c₁ k₂₁ hc₂₁).f_comp_comparisonMap E₂ hE₂)
    ((S.lower.pushoutDataOfPushout c₂ c₁ k₂₁ hc₂₁).comparisonMap_comp_g E₂ hE₂)

end FirstOrderThickeningComplex

end PushoutExtension

end Deformation.ToposThickening

end
