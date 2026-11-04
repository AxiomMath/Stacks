module

public import StacksFrontier.AlgebraicGeometry.ProEtale.ConstructibleComplexes

/-!
# Sheaves of `Λ`-modules and sheaves of modules over the constant coefficient ring sheaf

Let `X` be a scheme and `Λ` a commutative ring. On the small pro-étale site of `X` there are two
descriptions of a sheaf of `Λ`-modules: as an object of `Sheaf (Scheme.ProEt.topology X)
(ModuleCat Λ)`, and as a sheaf of modules over the constant coefficient ring sheaf `Λ̲` of
`AlgebraicGeometry.ProEtale.constantCoefficientRingedSite`. This file proves that the two are
**equivalent categories**, the comparison functors being the two already in the library:

* `AlgebraicGeometry.ProEtale.moduleSheafOverConstantCoefficientsFunctor`, the sheafification of
  the presheaf of modules over the constant *presheaf* of coefficient rings, and
* `AlgebraicGeometry.ProEtale.toCoefficientModuleSheaf`, which takes the sections over the
  terminal object of the site and restricts scalars along `Λ → Λ̲(⊤)`.

## Main results

* `AlgebraicGeometry.ProEtale.isSheaf_modulePresheafOverConstantCoefficients`: the presheaf of
  modules over the constant presheaf of coefficient rings attached to a sheaf of `Λ`-modules is
  a sheaf.
* `AlgebraicGeometry.ProEtale.isIso_modulePresheafOverConstantCoefficients_unit`: hence the
  sheafification unit at it is an isomorphism.
* `AlgebraicGeometry.ProEtale.modulePresheafOverConstantCoefficientsFunctorFullyFaithful`: the
  presheaf-level reading is fully faithful.
* `AlgebraicGeometry.ProEtale.constantCoefficientRingMap_app_eq`: the comparison
  `Λ̲₀ ⟶ Λ̲` over an object of the site factors through the sections over the terminal object; this
  is what identifies the two `Λ`-actions below.
* `AlgebraicGeometry.ProEtale.toCoefficientModuleSheafCompModulePresheafIso`: reading
  `AlgebraicGeometry.ProEtale.toCoefficientModuleSheaf` back at the presheaf level is restriction
  of scalars along that comparison, i.e. the right adjoint of
  `CategoryTheory.PresheafOfModules.sheafificationAdjunction`.
* `AlgebraicGeometry.ProEtale.toCoefficientModuleSheaf_full` and
  `AlgebraicGeometry.ProEtale.toCoefficientModuleSheaf_faithful`: hence that reading is fully
  faithful.
* `AlgebraicGeometry.ProEtale.constantCoefficientsCounitIso`,
  `AlgebraicGeometry.ProEtale.coefficientModuleSheafUnitIsoApp`,
  `AlgebraicGeometry.ProEtale.moduleSheafOverConstantCoefficientsFunctor_essSurj` and
  `AlgebraicGeometry.ProEtale.toCoefficientModuleSheaf_essSurj`: the two functors are mutually
  inverse on objects, up to isomorphism.
* `AlgebraicGeometry.ProEtale.constantCoefficientsAdjunction` and
  `AlgebraicGeometry.ProEtale.constantCoefficientsUnitIso`: the change of coefficients is left
  adjoint to that reading, and the unit of the adjunction is an isomorphism.
* `AlgebraicGeometry.ProEtale.moduleSheafOverConstantCoefficientsFunctor_isEquivalence`,
  `AlgebraicGeometry.ProEtale.toCoefficientModuleSheaf_isEquivalence` and
  `AlgebraicGeometry.ProEtale.coefficientModuleSheafEquivalence`: **the equivalence
  `SheafOfModules Λ̲ ≌ Sheaf (Scheme.ProEt.topology X) (ModuleCat Λ)`.**
* `AlgebraicGeometry.ProEtale.toCoefficientModuleSheaf_additive`: it is additive, which is what
  carries the identification to complexes and hence to the derived categories.

## Implementation notes

The mathematics is the general fact that for a locally bijective comparison `α : R₀ ⟶ R` from a
presheaf of rings to a sheaf of rings, the sheafification functor
`CategoryTheory.PresheafOfModules.sheafification α` has a fully faithful right adjoint
(`CategoryTheory.PresheafOfModules.sheafificationAdjunction`, whose counit Mathlib already knows
to be an isomorphism), and that its unit is an isomorphism on a presheaf of modules whose
underlying presheaf is already a sheaf. Here `R₀` is the *constant* presheaf of coefficient
rings, so a presheaf of `R₀`-modules is nothing but a presheaf of `Λ`-modules read through
`ULift.ringEquiv`, and the sheaves among them are exactly the objects of
`Sheaf (Scheme.ProEt.topology X) (ModuleCat Λ)`.

No point of the site, no stalk, no weak contractibility and no clopen decomposition enters: the
modules of sections are literally unchanged by either functor, only the ring acting on them
changes. In particular nothing here needs `Λ` to be Noetherian or `X` to be weakly contractible.

The one computation is `AlgebraicGeometry.ProEtale.constantCoefficientRingMap_app_eq`. The
`Λ`-action that `AlgebraicGeometry.ProEtale.toCoefficientModuleSheaf` puts on the sections over
an object `U` factors as `Λ ≃ ULift Λ → Λ̲(⊤) → Λ̲(U)`, while the one coming from the constant
presheaf of rings is `Λ ≃ ULift Λ → Λ̲(U)`; these agree because `CategoryTheory.toSheafify` is
natural and the restriction maps of a constant presheaf are identities. Both actions therefore
live on the same abelian group, and every isomorphism below is the identity on sections.

The sheaf condition for the presheaf of modules needs no size hypothesis, unlike its counterpart
`AlgebraicGeometry.isSheaf_modulePresheafOverConstantCoefficients` on the small étale site: the
module sections there are at an arbitrary universe `w`, while here they are at
`max (u + 1) r w`, which already contains both universes of the small pro-étale site.

Nothing here is tagged. This is infrastructure: the Stacks project uses the identification
silently, and the statements it is needed for — Stacks 093S part (3) for modules, and the
reduction steps of Stacks 09C5 — carry their own tags elsewhere. See
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/LocallyConstantModules/Morphisms.lean` for the
place where the absence of this equivalence was blocking a registration.

## References

* [Stacks Project, Tag 03TR](https://stacks.math.columbia.edu/tag/03TR)
* [Stacks Project, Tag 093S](https://stacks.math.columbia.edu/tag/093S)
* [Stacks Project, Tag 09C5](https://stacks.math.columbia.edu/tag/09C5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u r w

namespace AlgebraicGeometry.ProEtale

attribute [local instance] SheafOfModules.hasSheafify_commRingCat
  Stacks.hasSheafCompose_forget₂_commRingCat
  SheafOfModules.wEqualsLocallyBijective_commRingCat
  GrothendieckTopology.hasSheafify_addCommGrpCat
  SheafOfModules.wEqualsLocallyBijective_addCommGrpCat

variable (X : Scheme.{u}) (Λ : Type r) [CommRing Λ]

/-! ### The sheafification unit -/

/-- The presheaf of modules over the constant presheaf of coefficient rings attached to a sheaf
of `Λ`-modules is a sheaf: restriction of scalars along `ULift.ringEquiv` does not change the
underlying presheaf of abelian groups, which is the given sheaf composed with the forgetful
functor. -/
theorem isSheaf_modulePresheafOverConstantCoefficients
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) r w} Λ)) :
    Presheaf.IsSheaf (Scheme.ProEt.topology X)
      ((modulePresheafOverConstantCoefficientsFunctor.{u, r, w} X Λ).obj F).presheaf := by
  show Presheaf.IsSheaf (Scheme.ProEt.topology X)
    (F.obj ⋙ forget₂ (ModuleCat.{max (u + 1) r w} Λ) AddCommGrpCat.{max (u + 1) r w})
  exact GrothendieckTopology.HasSheafCompose.isSheaf F.obj F.property

/-- The unit of the sheafification adjunction for presheaves of modules is an isomorphism at the
presheaf of modules attached to a sheaf of `Λ`-modules, that presheaf being a sheaf already. -/
instance isIso_modulePresheafOverConstantCoefficients_unit
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) r w} Λ)) :
    IsIso ((PresheafOfModules.sheafificationAdjunction.{max (u + 1) r w}
      (constantCoefficientRingMap.{u, r, w} X Λ)).unit.app
        ((modulePresheafOverConstantCoefficientsFunctor.{u, r, w} X Λ).obj F)) := by
  rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf
    ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of (ULift.{max (u + 1) w} Λ))))]
  rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
  exact isIso_toSheafify _ (isSheaf_modulePresheafOverConstantCoefficients.{u, r, w} X Λ F)

/-! ### The presheaf-level reading is fully faithful -/

/-- **The presheaf-level change of coefficients is fully faithful.** On the sections over every
object of the site it is restriction of scalars along the ring isomorphism `ULift.ringEquiv`, so
it changes neither the underlying map nor what it means for it to be linear. -/
def modulePresheafOverConstantCoefficientsFunctorFullyFaithful :
    (modulePresheafOverConstantCoefficientsFunctor.{u, r, w} X Λ).FullyFaithful where
  preimage {M N} ψ := ObjectProperty.homMk
    { app := fun U => ModuleCat.ofHom
        { toFun := fun x => (ψ.app U).hom x
          map_add' := fun x y => map_add (ψ.app U).hom x y
          map_smul' := fun c x => (ψ.app U).hom.map_smul (ULift.up c) x }
      naturality := fun U V f => by
        ext x
        exact PresheafOfModules.naturality_apply ψ f x }
  map_preimage ψ := by ext U x; rfl
  preimage_map f := by ext U x; rfl

/-- The presheaf-level reading of a sheaf of `Λ`-modules as a presheaf of modules over the
constant presheaf of coefficient rings is faithful. -/
instance modulePresheafOverConstantCoefficientsFunctor_faithful :
    (modulePresheafOverConstantCoefficientsFunctor.{u, r, w} X Λ).Faithful :=
  (modulePresheafOverConstantCoefficientsFunctorFullyFaithful.{u, r, w} X Λ).faithful

/-- The presheaf-level reading of a sheaf of `Λ`-modules as a presheaf of modules over the
constant presheaf of coefficient rings is full. -/
instance modulePresheafOverConstantCoefficientsFunctor_full :
    (modulePresheafOverConstantCoefficientsFunctor.{u, r, w} X Λ).Full :=
  (modulePresheafOverConstantCoefficientsFunctorFullyFaithful.{u, r, w} X Λ).full

/-! ### The two `Λ`-actions on the sections agree -/

/-- **The comparison from the constant presheaf of coefficient rings factors through the sections
over the terminal object.** Composing `Λ ≃ ULift Λ → Λ̲(⊤)` with the restriction to an object `U`
of the site gives the comparison at `U`. The reason is that `CategoryTheory.toSheafify` is
natural and the restriction maps of a constant presheaf are identities. -/
theorem constantCoefficientRingMap_app_eq (U : X.ProEtᵒᵖ) :
    ((constantCoefficientRingMap.{u, r, w} X Λ).app U).hom =
      ((Stacks.SheafOfModules.Tensor.ringSheaf
            (constantCoefficientRingedSite.{u, r, w} X Λ).O).obj.map
          ((terminalIsTerminal (C := X.ProEt)).op.to U)).hom.comp
        ((toCoefficientSections.{u, r, w} X Λ).comp
          (ULift.ringEquiv.{r, max (u + 1) w} (R := Λ)).toRingHom) := by
  have hnat := (toSheafify (Scheme.ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{max (u + 1) w} Λ)))).naturality
    ((terminalIsTerminal (C := X.ProEt)).op.to U)
  ext x
  exact ConcreteCategory.congr_hom hnat x

/-! ### The right adjoint, read at the presheaf level -/

/-- The presheaf of modules underlying the reading of a sheaf of modules over the constant
coefficient ring sheaf as a sheaf of `Λ`-modules is restriction of scalars along
`AlgebraicGeometry.ProEtale.constantCoefficientRingMap`: both are the sections of the given
sheaf, and the two actions of the constant presheaf of coefficient rings on them agree by
`AlgebraicGeometry.ProEtale.constantCoefficientRingMap_app_eq`. -/
def toCoefficientModulePresheafIsoApp
    (N : RingedSite.Modules.{u + 1, u, max (u + 1) r w}
      (constantCoefficientRingedSite.{u, r, w} X Λ)) :
    (modulePresheafOverConstantCoefficientsFunctor.{u, r, w} X Λ).obj
        ((toCoefficientModuleSheaf.{u, r, w} X Λ).obj N) ≅
      (PresheafOfModules.restrictScalars.{max (u + 1) r w}
        (constantCoefficientRingMap.{u, r, w} X Λ)).obj N.val :=
  PresheafOfModules.isoMk
    (fun U =>
      (ModuleCat.restrictScalarsComp'App
          (ULift.ringEquiv.{r, max (u + 1) w} (R := Λ)).toRingHom
          (toCoefficientSections.{u, r, w} X Λ)
          ((toCoefficientSections.{u, r, w} X Λ).comp
            (ULift.ringEquiv.{r, max (u + 1) w} (R := Λ)).toRingHom)
          rfl _).symm ≪≫
        (ModuleCat.restrictScalarsComp'App
          ((toCoefficientSections.{u, r, w} X Λ).comp
            (ULift.ringEquiv.{r, max (u + 1) w} (R := Λ)).toRingHom)
          ((Stacks.SheafOfModules.Tensor.ringSheaf
              (constantCoefficientRingedSite.{u, r, w} X Λ).O).obj.map
            ((terminalIsTerminal (C := X.ProEt)).op.to U)).hom
          ((constantCoefficientRingMap.{u, r, w} X Λ).app U).hom
          (constantCoefficientRingMap_app_eq.{u, r, w} X Λ U) _).symm)
    (fun U V f => by ext x; rfl)

/-- **Reading a sheaf of modules over the constant coefficient ring sheaf as a sheaf of
`Λ`-modules and then back at the presheaf level is restriction of scalars.** This identifies
`AlgebraicGeometry.ProEtale.toCoefficientModuleSheaf`, followed by the presheaf-level change of
coefficients, with the right adjoint of
`CategoryTheory.PresheafOfModules.sheafificationAdjunction`. -/
def toCoefficientModuleSheafCompModulePresheafIso :
    toCoefficientModuleSheaf.{u, r, w} X Λ ⋙
        modulePresheafOverConstantCoefficientsFunctor.{u, r, w} X Λ ≅
      SheafOfModules.forget.{max (u + 1) r w}
          (Stacks.SheafOfModules.Tensor.ringSheaf (constantCoefficientRingedSite.{u, r, w} X Λ).O) ⋙
        PresheafOfModules.restrictScalars.{max (u + 1) r w}
          (constantCoefficientRingMap.{u, r, w} X Λ) :=
  NatIso.ofComponents (toCoefficientModulePresheafIsoApp.{u, r, w} X Λ)
    (fun _ => by ext U x; rfl)

/-! ### The equivalence -/

/-- Reading a sheaf of modules over the constant coefficient ring sheaf as a sheaf of
`Λ`-modules is faithful: followed by the presheaf-level reading it is the forgetful functor
followed by restriction of scalars, by
`AlgebraicGeometry.ProEtale.toCoefficientModuleSheafCompModulePresheafIso`. -/
instance toCoefficientModuleSheaf_faithful :
    (toCoefficientModuleSheaf.{u, r, w} X Λ).Faithful :=
  Functor.Faithful.of_comp_iso
    (toCoefficientModuleSheafCompModulePresheafIso.{u, r, w} X Λ)

/-- Reading a sheaf of modules over the constant coefficient ring sheaf as a sheaf of
`Λ`-modules is full: followed by the faithful presheaf-level reading it is the forgetful functor
followed by restriction of scalars, by
`AlgebraicGeometry.ProEtale.toCoefficientModuleSheafCompModulePresheafIso`. -/
instance toCoefficientModuleSheaf_full :
    (toCoefficientModuleSheaf.{u, r, w} X Λ).Full :=
  Functor.Full.of_comp_faithful_iso
    (toCoefficientModuleSheafCompModulePresheafIso.{u, r, w} X Λ)

/-- **The counit of the equivalence.** A sheaf of modules over the constant coefficient ring
sheaf is recovered from the sheaf of `Λ`-modules of its sections: the comparison is the counit of
`CategoryTheory.PresheafOfModules.sheafificationAdjunction`, which Mathlib knows to be an
isomorphism, transported along
`AlgebraicGeometry.ProEtale.toCoefficientModuleSheafCompModulePresheafIso`. -/
def constantCoefficientsCounitIso :
    toCoefficientModuleSheaf.{u, r, w} X Λ ⋙
        moduleSheafOverConstantCoefficientsFunctor.{u, r, w} X Λ ≅
      𝟭 (RingedSite.Modules.{u + 1, u, max (u + 1) r w}
        (constantCoefficientRingedSite.{u, r, w} X Λ)) :=
  (Functor.associator (toCoefficientModuleSheaf.{u, r, w} X Λ)
      (modulePresheafOverConstantCoefficientsFunctor.{u, r, w} X Λ)
      (PresheafOfModules.sheafification.{max (u + 1) r w}
        (constantCoefficientRingMap.{u, r, w} X Λ))).symm ≪≫
    Functor.isoWhiskerRight (toCoefficientModuleSheafCompModulePresheafIso.{u, r, w} X Λ)
      (PresheafOfModules.sheafification.{max (u + 1) r w}
        (constantCoefficientRingMap.{u, r, w} X Λ)) ≪≫
    asIso (PresheafOfModules.sheafificationAdjunction.{max (u + 1) r w}
      (constantCoefficientRingMap.{u, r, w} X Λ)).counit

/-- **The change of coefficients is essentially surjective.** Every sheaf of modules over the
constant coefficient ring sheaf comes from the sheaf of `Λ`-modules of its sections. -/
instance moduleSheafOverConstantCoefficientsFunctor_essSurj :
    (moduleSheafOverConstantCoefficientsFunctor.{u, r, w} X Λ).EssSurj :=
  ⟨fun N => ⟨(toCoefficientModuleSheaf.{u, r, w} X Λ).obj N,
    ⟨(constantCoefficientsCounitIso.{u, r, w} X Λ).app N⟩⟩⟩

/-- A sheaf of `Λ`-modules is recovered from its reading over the constant coefficient ring
sheaf. At the presheaf level the comparison is the sheafification unit, invertible because the
presheaf of modules is already a sheaf, followed by
`AlgebraicGeometry.ProEtale.toCoefficientModuleSheafCompModulePresheafIso`; it descends along the
fully faithful presheaf-level reading. -/
def coefficientModuleSheafUnitIsoApp
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) r w} Λ)) :
    (toCoefficientModuleSheaf.{u, r, w} X Λ).obj
        ((moduleSheafOverConstantCoefficientsFunctor.{u, r, w} X Λ).obj F) ≅ F :=
  ((modulePresheafOverConstantCoefficientsFunctorFullyFaithful.{u, r, w} X Λ).preimageIso
    (Y := (toCoefficientModuleSheaf.{u, r, w} X Λ).obj
      ((moduleSheafOverConstantCoefficientsFunctor.{u, r, w} X Λ).obj F))
    (asIso ((PresheafOfModules.sheafificationAdjunction.{max (u + 1) r w}
        (constantCoefficientRingMap.{u, r, w} X Λ)).unit.app
          ((modulePresheafOverConstantCoefficientsFunctor.{u, r, w} X Λ).obj F)) ≪≫
      ((toCoefficientModuleSheafCompModulePresheafIso.{u, r, w} X Λ).app
        ((moduleSheafOverConstantCoefficientsFunctor.{u, r, w} X Λ).obj F)).symm)).symm

/-- **Reading a sheaf of modules over the constant coefficient ring sheaf as a sheaf of
`Λ`-modules is essentially surjective.** -/
instance toCoefficientModuleSheaf_essSurj :
    (toCoefficientModuleSheaf.{u, r, w} X Λ).EssSurj :=
  ⟨fun F => ⟨(moduleSheafOverConstantCoefficientsFunctor.{u, r, w} X Λ).obj F,
    ⟨coefficientModuleSheafUnitIsoApp.{u, r, w} X Λ F⟩⟩⟩

/-- **Reading a sheaf of modules over the constant coefficient ring sheaf as a sheaf of
`Λ`-modules is an equivalence of categories.** -/
instance toCoefficientModuleSheaf_isEquivalence :
    (toCoefficientModuleSheaf.{u, r, w} X Λ).IsEquivalence where

/-- **The change of coefficients is left adjoint to the reading of a sheaf of modules over the
constant coefficient ring sheaf as a sheaf of `Λ`-modules.** This is the sheafification
adjunction for presheaves of modules, restricted along the fully faithful presheaf-level
reading. -/
def constantCoefficientsAdjunction :
    moduleSheafOverConstantCoefficientsFunctor.{u, r, w} X Λ ⊣
      toCoefficientModuleSheaf.{u, r, w} X Λ :=
  Adjunction.restrictFullyFaithful
    (PresheafOfModules.sheafificationAdjunction.{max (u + 1) r w}
      (constantCoefficientRingMap.{u, r, w} X Λ))
    (modulePresheafOverConstantCoefficientsFunctorFullyFaithful.{u, r, w} X Λ)
    (Functor.FullyFaithful.id _)
    (Functor.rightUnitor (moduleSheafOverConstantCoefficientsFunctor.{u, r, w} X Λ)).symm
    (Functor.leftUnitor (SheafOfModules.forget.{max (u + 1) r w}
        (Stacks.SheafOfModules.Tensor.ringSheaf (constantCoefficientRingedSite.{u, r, w} X Λ).O) ⋙
      PresheafOfModules.restrictScalars.{max (u + 1) r w}
        (constantCoefficientRingMap.{u, r, w} X Λ)) ≪≫
      (toCoefficientModuleSheafCompModulePresheafIso.{u, r, w} X Λ).symm)

/-- **The change of coefficients is an equivalence of categories.** -/
instance moduleSheafOverConstantCoefficientsFunctor_isEquivalence :
    (moduleSheafOverConstantCoefficientsFunctor.{u, r, w} X Λ).IsEquivalence :=
  (constantCoefficientsAdjunction.{u, r, w} X Λ).isEquivalence_left_of_isEquivalence_right

/-- **The unit of the equivalence**, as a natural isomorphism. -/
def constantCoefficientsUnitIso :
    𝟭 (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) r w} Λ)) ≅
      moduleSheafOverConstantCoefficientsFunctor.{u, r, w} X Λ ⋙
        toCoefficientModuleSheaf.{u, r, w} X Λ :=
  asIso (constantCoefficientsAdjunction.{u, r, w} X Λ).unit

/-- **Reading a sheaf of modules over the constant coefficient ring sheaf as a sheaf of
`Λ`-modules is additive.** It is an equivalence between additive categories, hence preserves
binary products and the zero object. Its quasi-inverse
`AlgebraicGeometry.ProEtale.moduleSheafOverConstantCoefficientsFunctor` is already known to be
additive; this is what the two readings need in order to agree on complexes, and so on the
derived categories. -/
instance toCoefficientModuleSheaf_additive :
    (toCoefficientModuleSheaf.{u, r, w} X Λ).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- **The equivalence `SheafOfModules Λ̲ ≌ Sheaf (Scheme.ProEt.topology X) (ModuleCat Λ)`.** A
sheaf of modules over the constant coefficient ring sheaf on the small pro-étale site of `X` is
the same thing as a sheaf of `Λ`-modules; the functor is
`AlgebraicGeometry.ProEtale.toCoefficientModuleSheaf`, which takes the sections over the terminal
object of the site and restricts scalars, and its quasi-inverse is
`AlgebraicGeometry.ProEtale.moduleSheafOverConstantCoefficientsFunctor`, which sheafifies the
constant action. -/
def coefficientModuleSheafEquivalence :
    RingedSite.Modules.{u + 1, u, max (u + 1) r w}
        (constantCoefficientRingedSite.{u, r, w} X Λ) ≌
      Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) r w} Λ) :=
  (toCoefficientModuleSheaf.{u, r, w} X Λ).asEquivalence

end AlgebraicGeometry.ProEtale

end
