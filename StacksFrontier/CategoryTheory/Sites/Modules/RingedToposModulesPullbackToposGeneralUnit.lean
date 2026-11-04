module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraUnitEssentiallySmall
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LowerShriekForgetLocalized
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafPullbackUnitSections
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposModulesPullbackToposGeneral
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSiteHomGeneralPushforwardUnderlying

/-!
# The two constructions of Stacks 03LU along a morphism of ringed sites agree

Let `f : X ⟶ Y` be a morphism of ringed sites at independent universes
(`AlgebraicGeometry.RingedSite.HomGeneral`).  The library carries **two** identifications
`f^*𝒪_Y ≅ 𝒪_X` of Stacks 03LU for it, and they are taken along the two different presentations
of its pullback of sheaves of modules that
`AlgebraicGeometry.RingedSite.HomGeneral.pullbackModulesToposIsoGeneral` compares:

* `SheafOfModules.pullbackObjUnitToUnit` at `f^♯`, for the *site-presented* pullback
  `AlgebraicGeometry.RingedToposSiteHom.pullbackToposGeneral`.  It is Mathlib's, and it is
  characterised only as an adjoint transpose, by
  `SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit`.
* `Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso`, for the pullback
  `Stacks.Sheaves.RingedToposModules.pullbackModules` of the modules development along the
  four-field morphism of ringed topoi.  It is built by corepresentability and characterised by
  `Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso_hom_comp`.

`AlgebraicGeometry.RingedSite.HomGeneral.pullbackModulesToposIsoGeneral_hom_app_unit` is the
statement that the two correspond under that comparison.  It is what lets a coherence proved for
one pullback be read at the other — in particular the right unit coherence of Stacks 03EL at the
associated-module functor of a big site, which is what asked for it.

## Main results

* `AlgebraicGeometry.RingedSite.HomGeneral.pullbackModulesToposIsoGeneral_hom_app_unit`: **the
  comparison of the two pullbacks carries the corepresentability identification of Stacks 03LU to
  Mathlib's adjoint-transpose one.**
* `AlgebraicGeometry.RingedSite.HomGeneral.homEquiv_pullbackModulesToposIsoGeneral_hom_app_unit`:
  the transposes of the two agree, which is the half of it that is pure adjunction calculus.
* `AlgebraicGeometry.RingedSite.HomGeneral.pushforwardModulesToposIsoGeneral_inv_app_val_app`:
  the comparison of the two **pushforwards** is the identity on local sections.

## Implementation notes

**The proof is transposition, twice over, and one equality of global sections.**  Both
identifications are pinned by their transposes along Stacks 03D7, and the two transposes are
taken along two different adjunctions with the *same* left adjoint up to the comparison.
`Stacks.SheafOfModules.homEquiv_leftAdjointUniq_hom_app_comp` converts one into the other and
`CategoryTheory.Adjunction.homEquiv_ofNatIsoRight_apply` absorbs the comparison of the two
pushforwards, which reduces everything to an equality of two morphisms out of the unit object.
Such a morphism is its value on the unit section (`SheafOfModules.unitHomEquiv`), and both values
are the unit section of `𝒪_X` over `u(W)`: on one side because `f^♯` is a morphism of sheaves of
*rings*, on the other by
`Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso_inv_adjunct_val_app_one` and
`CategoryTheory.Sheaf.unitTerminalHomEquiv_id_app_apply`.  The comparison isomorphism itself is
never inverted and no tensor product is computed.

**The seams, and why the proof is a chain of terms.** The structure sheaf of a ringed topos is
reached as `Stacks.SheafOfModules.Tensor.ringSheaf` and as
`Stacks.SheafOfModules.Tensor.ringSheaf`, and its pullback as
`AlgebraicGeometry.RingedToposSiteHom.pullbackToposGeneral` and as `SheafOfModules.pullback` of
`f^♯`; the pairs agree by `rfl` but are not syntactically equal, so a goal carrying two of them is
not type-correct at `implicit` transparency and `rw` refuses it.  Each crossing is therefore paid
in term position — by `Eq.trans`, `congrArg` and `exact`, where elaboration runs at default
transparency — and the two evaluations on the unit section are **separate private lemmas** rather
than `have`s inside one proof, since the cost of a `have` is counted on top of the enclosing
elaboration.  Nothing here raises a compiler limit or disables a linter.

The continuity of the underlying functor is restated as a `local instance` at the spelling
instance search keys on, as in
`StacksFrontier/AlgebraicGeometry/FormalGeometry/DerivedCompletionRinged/Pushforward.lean`:
`AlgebraicGeometry.RingedSite.HomGeneral.toRingedToposSiteHom` does not unfold at instance
transparency, so the field is not found at that spelling.

## References

* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open Stacks.Sheaves.RingedToposModules Stacks.Sheaves.ToposPullback
  Stacks.Sheaves.ToposPushforward
universe uX vX uY vY w

/-! ### The two spellings of the direct image agree, at independent universes

`Stacks.Sheaves.GradedAlgebraEssentiallySmall.moduleSheafFunctor_map_pushforwardModulesIso_hom_app`
is stated for two ringed topoi in the same universes; the morphisms of ringed sites of this file
have sources and targets in unrelated universes, so the comparison is restated here for them. -/

namespace Stacks.Sheaves.GradedAlgebraEssentiallySmall

open AlgebraicGeometry Stacks.PresheafOfModules.ChangeOfRings Stacks.Sheaves.GradedAlgebraPullback

universe v u₁ v' u' w'

/-- **The comparison between the two spellings of the direct image of sheaves of modules is the
identity on underlying sheaves of sets, for ringed topoi in independent universes.**

This generalizes
`Stacks.Sheaves.GradedAlgebraEssentiallySmall.moduleSheafFunctor_map_pushforwardModulesIso_hom_app`
to a source `RingedTopos.{v, u₁, w}` and a target `RingedTopos.{v', u', w'}` in unrelated
universes. The argument is the same: neither the whiskered comparison of inverse images nor the
transport along the equality of the two restrictions of scalars changes the underlying sheaf of
sets. -/
public theorem moduleSheafFunctor_map_pushforwardModulesIso_hom_app_of_universes
    {X : RingedTopos.{v, u₁, w}} {Y : RingedTopos.{v', u', w'}}
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
    [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
    [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
    [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
    (f : AlgebraicGeometry.RingedToposHom X Y)
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
        (f.pushforwardModulesIso.hom.app N) =
      CategoryTheory.CategoryStruct.id (f.toToposHom.pushforward.obj
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N)) := by
  have h1 : f.pushforwardModulesIso.hom.app N =
      (CategoryTheory.Functor.isoWhiskerRight
          (pullbackRestrictScalarsIso f.toToposHom.pushforward f.ringFsharpInverseImage)
          (SheafOfModules.restrictScalars
            (ringUnit f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))).hom.app N ≫
        (eqToIso f.pushforwardModules_eq).hom.app N :=
    NatTrans.comp_app _ _ N
  have h3 : (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
        ((eqToIso f.pushforwardModules_eq).hom.app N) =
      CategoryTheory.CategoryStruct.id (f.toToposHom.pushforward.obj
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N)) := by
    rw [eqToIso.hom, CategoryTheory.eqToHom_app, CategoryTheory.eqToHom_map]
    exact eqToHom_refl _ _
  exact (congrArg (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
      h1).trans
    (((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map_comp _ _).trans
      ((congrArg₂ (fun p q => p ≫ q)
          (moduleSheafFunctor_map_pullbackRestrictScalarsIso_hom_app f.toToposHom.pushforward
            f.ringFsharpInverseImage
            (ringUnit f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) N) h3).trans
        (Category.id_comp (CategoryTheory.CategoryStruct.id
          (f.toToposHom.pushforward.obj
            (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N))))))

end Stacks.Sheaves.GradedAlgebraEssentiallySmall

open Stacks.Sheaves.GradedAlgebraEssentiallySmall
  (moduleSheafFunctor_map_pushforwardModulesIso_hom_app_of_universes)

namespace AlgebraicGeometry.RingedSite

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [EssentiallySmall.{w} Y.C] [LocallySmall.{w} X.C]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (f : HomGeneral X Y)

/-- Continuity of the functor underlying the site-presented morphism of ringed topoi attached to
a morphism of ringed sites, in the shape instance search keys on. -/
local instance HomGeneral.isContinuous_toRingedToposSiteHom_u :
    f.toRingedToposSiteHom.u.IsContinuous (toRingedTopos Y).J (toRingedTopos X).J :=
  f.toRingedToposSiteHom.isContinuous

/-! ### The comparison of the two pushforwards is the identity on sections -/

/-! ### The two identifications of Stacks 03LU -/

omit [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- Mathlib's identification `f^*𝒪_Y ≅ 𝒪_X` of Stacks 03LU transposes to `f^♯`, read at the
`AlgebraicGeometry.RingedToposSiteHom.pullbackPushforwardAdjunctionToposGeneral` spelling of the
adjunction of Stacks 03D7.  This is
`SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit`; the restatement
pays the crossing between that adjunction and `SheafOfModules.pullbackPushforwardAdjunction` of
`f^♯` in term position, where elaboration runs at default transparency. -/
public theorem HomGeneral.homEquiv_pullbackObjUnitToUnitGeneral :
    f.toRingedToposSiteHom.pullbackPushforwardAdjunctionToposGeneral.homEquiv
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos Y).O))
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos X).O))
        (SheafOfModules.pullbackObjUnitToUnit f.toRingedToposSiteHom.fSharpRing) =
      SheafOfModules.unitToPushforwardObjUnit f.toRingedToposSiteHom.fSharpRing :=
  SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _

/-- **The transpose of Mathlib's identification of Stacks 03LU, conjugated to the pullback of the
modules development.**  Composing it with the comparison of the two pullbacks and transposing
along Stacks 03D7 for the modules development gives `f^♯`, up to the comparison of the two
pushforwards.

The comparison of the two pullbacks is a `CategoryTheory.Adjunction.leftAdjointUniq` of an
`CategoryTheory.Adjunction.ofNatIsoRight`, so
`Stacks.SheafOfModules.homEquiv_leftAdjointUniq_hom_app_comp` turns the transposition along the
one adjunction into the transposition along the other, and
`CategoryTheory.Adjunction.homEquiv_ofNatIsoRight_apply` peels off the comparison of the
pushforwards. -/
public theorem HomGeneral.homEquiv_pullbackModulesToposIsoGeneral_hom_app_unit :
    (pullbackAdjPushforwardModules f.toRingedToposHom.toRingedToposModulesHom).homEquiv
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos Y).O))
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos X).O))
        ((Adjunction.leftAdjointUniq
              ((pullbackAdjPushforwardModules
                f.toRingedToposHom.toRingedToposModulesHom).ofNatIsoRight
                  f.pushforwardModulesToposIsoGeneral)
              f.toRingedToposSiteHom.pullbackPushforwardAdjunctionToposGeneral).hom.app
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos Y).O)) ≫
          SheafOfModules.pullbackObjUnitToUnit f.toRingedToposSiteHom.fSharpRing) =
      SheafOfModules.unitToPushforwardObjUnit f.toRingedToposSiteHom.fSharpRing ≫
        f.pushforwardModulesToposIsoGeneral.inv.app
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos X).O)) := by
  have h1 := Stacks.SheafOfModules.homEquiv_leftAdjointUniq_hom_app_comp
    ((pullbackAdjPushforwardModules
      f.toRingedToposHom.toRingedToposModulesHom).ofNatIsoRight
        f.pushforwardModulesToposIsoGeneral)
    f.toRingedToposSiteHom.pullbackPushforwardAdjunctionToposGeneral
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos Y).O))
    (SheafOfModules.pullbackObjUnitToUnit f.toRingedToposSiteHom.fSharpRing)
  rw [Adjunction.homEquiv_ofNatIsoRight_apply,
    HomGeneral.homEquiv_pullbackObjUnitToUnitGeneral] at h1
  exact (Iso.eq_comp_inv
    (f.pushforwardModulesToposIsoGeneral.app
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos X).O)))).mpr h1

omit [EssentiallySmall.{w} Y.C] [LocallySmall.{w} X.C] [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The value on the unit section of the transpose of Mathlib's identification of Stacks 03LU: it
is the unit section, `f^♯` being a morphism of sheaves of rings.  Hoisted out of
`pullbackModulesToposIsoGeneral_hom_app_unit` for the reason recorded at the head of this
file. -/
private theorem HomGeneral.unitToPushforwardObjUnit_comp_inv_val_app_one
    (W : (toRingedTopos Y).Cᵒᵖ) :
    (SheafOfModules.unitToPushforwardObjUnit f.toRingedToposSiteHom.fSharpRing ≫
        f.pushforwardModulesToposIsoGeneral.inv.app
          (SheafOfModules.unit
            (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos X).O))).val.app W
        (1 : (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos Y).O).obj.obj W) =
      (1 : (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos X).O).obj.obj (f.u.op.obj W)) :=
  (HomGeneral.pushforwardModulesToposIsoGeneral_inv_app_val_app f
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos X).O)) W
        ((SheafOfModules.unitToPushforwardObjUnit f.toRingedToposSiteHom.fSharpRing).val.app W
          (1 : (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos Y).O).obj.obj W))).trans
    ((SheafOfModules.unitToPushforwardObjUnit_val_app_apply
        f.toRingedToposSiteHom.fSharpRing
          (1 : (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos Y).O).obj.obj W)).trans
      (map_one (ConcreteCategory.hom (f.toRingedToposSiteHom.fSharpRing.hom.app W))))

omit [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})] [EssentiallySmall.{w} Y.C]
  [LocallySmall.{w} X.C] [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The value on the unit section of the transpose of the corepresentability identification of
Stacks 03LU: it is the unit section, by
`Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso_inv_adjunct_val_app_one` and
`CategoryTheory.Sheaf.unitTerminalHomEquiv_id_app_apply`.  Hoisted out for the same reason. -/
private theorem HomGeneral.pushforward_map_unitTerminalHomEquiv_id_app_one
    (W : (toRingedTopos Y).Cᵒᵖ) :
    (f.toRingedToposHom.toRingedToposModulesHom.toToposHom.pushforward.map
          ((Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos X).O).unitTerminalHomEquiv
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos X).O))
            (𝟙 (SheafOfModules.unit
              (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos X).O))))).hom.app W
        (f.toRingedToposHom.toRingedToposModulesHom.toToposHom.pushforwardTerminalSection.hom.app W
          (terminalSheafSection (toRingedTopos Y).J W)) =
      (1 : (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos X).O).obj.obj (f.u.op.obj W)) :=
  unitTerminalHomEquiv_id_app_apply (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos X).O)
    (f.u.op.obj W) _

omit [EssentiallySmall.{w} Y.C] [LocallySmall.{w} X.C] in
/-- **The two transposes of Stacks 03LU agree.**  Both morphisms `𝒪_Y ⟶ f_*𝒪_X` are the unit
section, so they are equal by `SheafOfModules.unitHomEquiv`. -/
public theorem
    HomGeneral.unitToPushforwardObjUnit_comp_inv_eq_homEquiv_pullbackModulesObjUnitIso_inv :
    SheafOfModules.unitToPushforwardObjUnit f.toRingedToposSiteHom.fSharpRing ≫
        f.pushforwardModulesToposIsoGeneral.inv.app
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos X).O)) =
      (pullbackAdjPushforwardModules f.toRingedToposHom.toRingedToposModulesHom).homEquiv
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos Y).O))
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos X).O))
        (pullbackModulesObjUnitIso f.toRingedToposHom.toRingedToposModulesHom).inv := by
  refine (SheafOfModules.unitHomEquiv _).injective (Subtype.ext (funext fun W => ?_))
  rw [SheafOfModules.unitHomEquiv_apply_coe, SheafOfModules.unitHomEquiv_apply_coe,
    pullbackModulesObjUnitIso_inv_adjunct_val_app_one]
  exact (HomGeneral.unitToPushforwardObjUnit_comp_inv_val_app_one f W).trans
    (HomGeneral.pushforward_map_unitTerminalHomEquiv_id_app_one f W).symm

/-- **The two constructions of Stacks 03LU along a morphism of ringed sites agree.**  The
comparison `AlgebraicGeometry.RingedSite.HomGeneral.pullbackModulesToposIsoGeneral` of the two
pullbacks of sheaves of modules carries the corepresentability identification
`Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso` of `f^*𝒪_Y ≅ 𝒪_X` to Mathlib's
adjoint-transpose one, `SheafOfModules.pullbackObjUnitToUnit` at `f^♯`.

Both are pinned by their transposes along Stacks 03D7, those two transposes are compared by
`homEquiv_pullbackModulesToposIsoGeneral_hom_app_unit`, and they agree because both are the unit
section of `𝒪_X`. -/
@[stacks 03LU "the corepresentability construction of `f^*𝒪_Y ≅ 𝒪_X` for the pullback of the
modules development and Mathlib's adjoint-transpose construction for the site-presented pullback
agree under the comparison of the two pullbacks, for a morphism of ringed sites at independent
universes"]
public theorem HomGeneral.pullbackModulesToposIsoGeneral_hom_app_unit :
    f.pullbackModulesToposIsoGeneral.hom.app
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos Y).O)) ≫
        SheafOfModules.pullbackObjUnitToUnit f.toRingedToposSiteHom.fSharpRing =
      (pullbackModulesObjUnitIso f.toRingedToposHom.toRingedToposModulesHom).inv :=
  ((pullbackAdjPushforwardModules f.toRingedToposHom.toRingedToposModulesHom).homEquiv
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos Y).O))
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos X).O))).injective
      ((HomGeneral.homEquiv_pullbackModulesToposIsoGeneral_hom_app_unit f).trans
        (HomGeneral.unitToPushforwardObjUnit_comp_inv_eq_homEquiv_pullbackModulesObjUnitIso_inv f))

end AlgebraicGeometry.RingedSite

end
