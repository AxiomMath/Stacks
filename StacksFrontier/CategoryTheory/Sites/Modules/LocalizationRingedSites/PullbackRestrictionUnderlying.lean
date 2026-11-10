module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectImageRestrictScalars
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorBilinEquivApply
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorToposCompBilinear
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.PullbackToposSquare

/-!
# Stacks 04IX on underlying sheaves of sets: the comparison is the inverse of the unit of 03CZ

Let `(C, O)` be a ringed site and `U` an object of `C`. The isomorphism of Stacks 04IX
`AlgebraicGeometry.RingedSite.localizationPullbackToposIsoRestriction` identifies the pullback of
sheaves of modules along the localization morphism at `U` with restriction to the slice site. Its
construction has two halves: the inverse-image half
`Stacks.Sheaves.ToposPullback.restrictionModuleIso`, which is the identity on sections, and the
extension-of-scalars half, which is the counit of Stacks 03CZ for the structure map of the
localization.

This file exhibits that comparison as a **transpose**, which is what makes it readable on
underlying sheaves of sets: on sections it is then the inverse of the unit of Stacks 03CZ, the
morphism that the base change of bilinear pairings of Stacks 03EL carries a local section through
(`Stacks.SheafOfModules.pairingApp_pullbackTensorBilinEquiv`).

## How the computation goes

The counit of the extension-restriction adjunction has no formula of its own. What it has is
`CategoryTheory.Adjunction.homEquiv_counit`: the comparison, being
`extendScalars.map (restrictionModuleIso.hom.app Z)` followed by that counit, is the *inverse
transpose* of `restrictionModuleIso.hom.app Z`. Transposing forwards,

`unit ≫ restrictScalars.map (comparison) = restrictionModuleIso.hom.app Z`,

which is `unit_comp_restrictScalars_map_localizationPullbackIsoRestriction` below. Its right-hand
side is the identity on underlying sheaves of sets
(`moduleSheafFunctor_map_restrictionModuleIso_hom_app`), restriction of scalars does not change
what a morphism does on a section, and the retyping of Stacks 03CZ that Stacks 04IX for a
localization is built over is the identity on underlying sheaves of sets too
(`moduleSheafFunctor_map_localizationRestrictScalars_eq_hom_app`).

## What is left

The last step — reading the transpose identity
`unit_comp_restrictScalars_map_localizationPullbackIsoRestriction` on underlying sheaves of sets
and transporting it from the localization morphism of the modules development to the two-field
localization morphism of ringed topoi — is not here. Every ingredient it needs is: the transpose
identity, the formula
`localizationExtendRestrictAdjunction_unit_app` for the unit of the retyped adjunction, the fact
`moduleSheafFunctor_map_localizationRestrictScalars_eq_hom_app` that the retyping is the identity
on underlying sheaves of sets, the fact
`moduleSheafFunctor_map_restrictionModuleIso_hom_app` that the inverse-image identification is,
and `localizationPullbackToposIsoRestriction_eq` for the transport. What defeats the assembly is
the elaborator: a term that applies `Sheaf.moduleSheafFunctor` to the unit of Stacks 03CZ and
composes the result with anything spells the slice ringed site both as a ringed site and as a
ringed topos, and that conversion is not taken inside the 200000-heartbeat budget even though
each spelling crossing is `rfl` on its own (`(X.over U).ringedTopos.J = X.J.over U` and
`inverseImageRingSheaf … = commRingSheaf …` are both instant).

## Implementation notes

The comparison of Stacks 04IX comes in two presentations: one for the four-field morphism of
ringed topoi of the modules development
(`AlgebraicGeometry.RingedSite.localizationPullbackIsoRestriction`) and one for the two-field
morphism of Stacks 01D3 part (2)
(`AlgebraicGeometry.RingedSite.localizationPullbackToposIsoRestriction`), the second being the
first preceded by a transport along the equality of the two presentations. That transport is *not*
the identity on underlying sheaves of sets — extension of scalars is taken along the two structure
maps, which are equal and not definitionally equal — so it cannot be discharged by conversion. It
has to be removed by stating the computation with the morphism of ringed topoi as a variable and
substituting the equality.

Everything is assembled in term mode. The two spellings of the slice ringed site — `X.over U` read
as a ringed site and read as a ringed topos — agree definitionally but not at the `implicit`
transparency level, so a `rewrite` on a goal mentioning both reports that its own target is not
type-correct and fails to find patterns that are visibly present.

## Main results

* `Stacks.SheafOfModules.pairingOfTensorHom_comp`: the pairing of a morphism out of an objectwise
  tensor product, postcomposed with a morphism of sheaves of modules.
* `AlgebraicGeometry.RingedSite.unit_comp_restrictScalars_map_localizationPullbackIsoRestriction`:
  the comparison of Stacks 04IX is the transpose of the inverse-image identification.
* `AlgebraicGeometry.RingedSite.localizationPullbackToposIsoRestriction_eq`: the comparison of
  Stacks 04IX for the two-field localization morphism of ringed topoi written out as the composite
  of its two transports and the comparison for the localization morphism of the modules
  development.

## References

* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf MonoidalCategory
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
  Stacks.Sheaves.RingedToposModules

/-! ## Two bookkeeping identities in an arbitrary category -/

namespace Stacks.Sheaves.ToposPullback

section Bookkeeping

variable {D : Type*} [Category* D]

/-- Two identities inserted into a composite of two morphisms, as the associator and the right
unitor of a composite of natural isomorphisms insert them, cancel. -/
theorem comp_id_comp_comp_id {A B E : D} (α : A ⟶ B) (β : B ⟶ E) :
    α ≫ 𝟙 B ≫ β ≫ 𝟙 E = α ≫ β := by
  rw [Category.id_comp, Category.comp_id]

/-- **The transpose of an inverse transpose.** The unit followed by the right adjoint of
`F ρ ≫ ε` is `ρ`: this is `CategoryTheory.Equiv.apply_symm_apply` for
`CategoryTheory.Adjunction.homEquiv`, stated at the two composites it is definitionally equal to
so that a consumer never has to unfold `homEquiv`. -/
theorem unit_comp_map_comp_counit {E : Type*} [Category* E] {F : D ⥤ E} {G : E ⥤ D}
    (adj : F ⊣ G) {P : D} {N : E} (ρ : P ⟶ G.obj N) :
    adj.unit.app P ≫ G.map (F.map ρ ≫ adj.counit.app N) = ρ :=
  (adj.homEquiv P N).apply_symm_apply ρ

end Bookkeeping

end Stacks.Sheaves.ToposPullback

/-! ## The pairing of a morphism out of an objectwise tensor product, postcomposed -/

namespace Stacks.SheafOfModules

section Pairing

universe w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]

omit [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- Two morphisms out of a binary product of sheaves of types agree as soon as they agree on
every pair of local sections. This is the two-factor companion of
`Stacks.SheafOfModules.hom_ext_prodProd`. -/
theorem hom_ext_prod {A B E : Sheaf J (Type w)} {m m' : A ⨯ B ⟶ E}
    (h : ∀ (V : Cᵒᵖ) (a : (sectionsFunctor J V).obj A) (b : (sectionsFunctor J V).obj B),
      (sectionsFunctor J V).map m (Functor.prodObjMk a b) =
        (sectionsFunctor J V).map m' (Functor.prodObjMk a b)) :
    m = m' := by
  refine Sheaf.hom_ext_sections fun V s ↦ ?_
  have e : s = Functor.prodObjMk (P := sectionsFunctor J V)
      ((sectionsFunctor J V).map Limits.prod.fst s)
      ((sectionsFunctor J V).map Limits.prod.snd s) := by simp
  rw [e]
  exact h V _ _

variable {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  {hO : Presheaf.IsSheaf J (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf O)}
  {A B N N' : SheafOfModules.{w} (commRingSheaf J O hO)}

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- **The pairing of a morphism out of an objectwise tensor product is natural in the target.**
Postcomposing the morphism with a morphism of sheaves of modules postcomposes the pairing with its
underlying morphism of sheaves of sets.

Both sides are determined by their values on a pair of local sections, where each is the value of
the morphism on a pure tensor carried through the second morphism. -/
theorem pairingOfTensorHom_comp (t : A.val ⊗ B.val ⟶ N.val) (m : N ⟶ N') :
    pairingOfTensorHom (hO := hO) (t ≫ m.val) =
      pairingOfTensorHom (hO := hO) t ≫ (moduleSheafFunctor (commRingSheaf J O hO)).map m := by
  refine hom_ext_prod fun V a b ↦ ?_
  refine (pairingApp_pairingOfTensorHom (hO := hO) (t ≫ m.val) V a b).trans ?_
  refine Eq.trans ?_ ((sectionsFunctor J V).map_comp_apply (pairingOfTensorHom (hO := hO) t)
    ((moduleSheafFunctor (commRingSheaf J O hO)).map m) (Functor.prodObjMk a b)).symm
  exact congrArg
    ((sectionsFunctor J V).map ((moduleSheafFunctor (commRingSheaf J O hO)).map m))
    (pairingApp_pairingOfTensorHom (hO := hO) t V a b).symm

end Pairing

end Stacks.SheafOfModules

/-! ## Stacks 04IX on underlying sheaves of sets -/

namespace AlgebraicGeometry.RingedSite

universe u

variable (X : RingedSite.{u, u, u}) (U : X.C)
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(X.J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget RingCat.{u})]
  [(X.J.over U).HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [(X.J.over U).HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasWeakSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(X.J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget RingCat.{u})] [(X.J.over U).HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [(X.J.over U).HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasWeakSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The two presentations of the localization morphism of ringed topoi agree.** The four-field
morphism of the modules development attached to the two-field localization morphism of ringed
topoi by `AlgebraicGeometry.RingedToposHom.toModulesHom` *is* the localization morphism
`AlgebraicGeometry.RingedSite.localizationMorphism` of the modules development. -/
theorem toModulesHom_localizationRingedToposHom :
    (X.localizationRingedToposHom U).toModulesHom = X.localizationMorphism U :=
  ((X.localizationRingedToposHom U).toModulesHom_eq_toRingedToposModulesHom).trans
    (X.toRingedToposModulesHom_localizationRingedToposHom U)

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- `AlgebraicGeometry.RingedSite.localizationPullbackToposIsoRestriction` written out as the
composite of its three factors: the two transports between the presentations of a morphism of
ringed topoi, and Stacks 04IX for the localization morphism of the modules development. This is
the form a statement about its effect on sections is proved against. -/
theorem localizationPullbackToposIsoRestriction_eq :
    X.localizationPullbackToposIsoRestriction U =
      eqToIso (congrArg (fun h ↦ h.pullbackModules)
          ((X.localizationRingedToposHom U).toModulesHom_eq_toRingedToposModulesHom)) ≪≫
        eqToIso (congrArg (fun h ↦ h.pullbackModules)
          (X.toRingedToposModulesHom_localizationRingedToposHom U)) ≪≫
        X.localizationPullbackIsoRestriction U :=
  rfl

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The comparison of Stacks 04IX for the localization morphism of the modules development is
`extendScalars` of the inverse-image identification of Stacks 03D2 followed by the counit of
Stacks 03CZ: the two identities that the associator and the right unitor contribute to
`localizationPullbackIsoRestriction_eq` cancel. -/
theorem localizationPullbackIsoRestriction_hom_app
    (Z : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (X.localizationPullbackIsoRestriction U).hom.app Z =
      (X.localizationExtendScalars U).map
          ((restrictionModuleIso (X.J.over U) X.J (Over.forget U)
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).hom.app Z) ≫
        (X.localizationExtendRestrictCounitIso U).hom.app
          ((SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).obj Z) :=
  (congrArg (fun (i : (X.localizationMorphism U).pullbackModules ≅
        SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U) ↦ i.hom.app Z)
      (X.localizationPullbackIsoRestriction_eq U)).trans
    (Stacks.Sheaves.ToposPullback.comp_id_comp_comp_id
      ((X.localizationExtendScalars U).map
        ((restrictionModuleIso (X.J.over U) X.J (Over.forget U)
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).hom.app Z))
      ((X.localizationExtendRestrictCounitIso U).hom.app
        ((SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).obj Z)))

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **The comparison of Stacks 04IX is the transpose of the inverse-image identification.** The
comparison is `extendScalars` of `Stacks.Sheaves.ToposPullback.restrictionModuleIso` followed by
the counit of Stacks 03CZ for the structure map of the localization, which is exactly an inverse
transpose; so transposing it forwards gives the inverse-image identification back.

The counit has no description of its own, and this transposition is the only handle on it. -/
theorem unit_comp_restrictScalars_map_localizationPullbackIsoRestriction
    (Z : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (X.localizationExtendRestrictAdjunction U).unit.app
          ((inverseImageModules (X.localizationMorphism U).toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf X.ringedTopos.O)).obj Z) ≫
        (X.localizationRestrictScalars U).map
          ((X.localizationPullbackIsoRestriction U).hom.app Z) =
      (restrictionModuleIso (X.J.over U) X.J (Over.forget U)
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).hom.app Z := by
  have h1 := congrArg (fun m ↦ (X.localizationExtendRestrictAdjunction U).unit.app
          ((inverseImageModules (X.localizationMorphism U).toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf X.ringedTopos.O)).obj Z) ≫
      (X.localizationRestrictScalars U).map m)
    (X.localizationPullbackIsoRestriction_hom_app U Z)
  have h2 := Stacks.Sheaves.ToposPullback.unit_comp_map_comp_counit
    (P := ((inverseImageModules (X.localizationMorphism U).toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf X.ringedTopos.O)).obj Z))
    (N := (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).obj Z)
    (X.localizationExtendRestrictAdjunction U)
    ((restrictionModuleIso (X.J.over U) X.J (Over.forget U)
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).hom.app Z)
  exact h1.trans h2

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(X.J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [(X.J.over U).HasSheafCompose (forget AddCommGrpCat.{u})] in
/-- The unit of `AlgebraicGeometry.RingedSite.localizationExtendRestrictAdjunction` is the unit of
Stacks 03CZ for the structure map of the localization followed by the transport of the right
adjoint that the adjunction is retyped along. -/
theorem localizationExtendRestrictAdjunction_unit_app
    (M : SheafOfModules.{u} (inverseImageRingSheaf (X.localizationMorphism U).toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf X.ringedTopos.O))) :
    (X.localizationExtendRestrictAdjunction U).unit.app M =
      (Stacks.SheafOfModules.pullbackExtendAdj (X.localizationMorphism U)).unit.app M ≫
        (eqToIso (X.localizationRestrictScalars_eq U)).hom.app
          ((X.localizationExtendScalars U).obj M) :=
  congrArg (fun α ↦ NatTrans.app α M)
    (Adjunction.ofNatIsoRight_unit
      (Stacks.SheafOfModules.pullbackExtendAdj (X.localizationMorphism U))
      (eqToIso (X.localizationRestrictScalars_eq U)))

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(X.J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [(X.J.over U).HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasWeakSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The transport of the right adjoint that
`AlgebraicGeometry.RingedSite.localizationExtendRestrictAdjunction` is retyped along is the
identity on underlying sheaves of sets: restriction of scalars along either of the two equal
structure maps has the same underlying sheaf of sets. -/
theorem moduleSheafFunctor_map_localizationRestrictScalars_eq_hom_app
    (Y : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).ringedTopos.O)) :
    (moduleSheafFunctor (commRingSheaf (X.over U).ringedTopos.J
          (inverseImageStructureCommRing (X.localizationMorphism U))
          (Stacks.SheafOfModules.isSheaf_inverseImageStructureCommRing
            (X.localizationMorphism U)))).map
        ((eqToIso (X.localizationRestrictScalars_eq U)).hom.app Y) = 𝟙 _ := by
  have h1 := congrArg (moduleSheafFunctor (commRingSheaf (X.over U).ringedTopos.J
          (inverseImageStructureCommRing (X.localizationMorphism U))
          (Stacks.SheafOfModules.isSheaf_inverseImageStructureCommRing
            (X.localizationMorphism U)))).map
    (eqToHom_app (X.localizationRestrictScalars_eq U) Y)
  exact (h1.trans (eqToHom_map _ _)).trans (eqToHom_refl _ _)

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(X.J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(X.J.over U).HasSheafCompose (forget RingCat.{u})]
  [(X.J.over U).HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasWeakSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The inverse-image identification of Stacks 03D2 for the localization at `U` is the identity
on underlying sheaves of sets.** `Stacks.Sheaves.ToposPullback.restrictionModuleIso` is the
identity map on sections; its content is only that the transported module structure agrees with
the original one.

The inverse image of the structure sheaf is spelled as the source ring of the extension of scalars
of Stacks 03CZ, which is the spelling the base change of bilinear pairings of Stacks 03EL states
its units at. -/
theorem moduleSheafFunctor_map_restrictionModuleIso_hom_app
    (Z : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (moduleSheafFunctor (commRingSheaf (X.over U).ringedTopos.J
          (inverseImageStructureCommRing (X.localizationMorphism U))
          (Stacks.SheafOfModules.isSheaf_inverseImageStructureCommRing
            (X.localizationMorphism U)))).map
        ((restrictionModuleIso (X.J.over U) X.J (Over.forget U)
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).hom.app Z) = 𝟙 _ :=
  Sheaf.hom_ext_sections fun _ _ ↦ rfl

end AlgebraicGeometry.RingedSite

end
