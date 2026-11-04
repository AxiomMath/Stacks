module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalizedPullbackQuasicoherentOfHom
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigEtaleAssociatedModule
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigEtaleAssociatedModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigEtaleModuleCounit
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigEtaleModuleUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigEtaleSpaceSiteOfBigFppf
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfModuleCounit
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfModuleHigherDirectImage
public import StacksFrontier.CategoryTheory.Adjunction.RestrictEquivalence

/-!
# Clauses (2) to (7) of Stacks 0DGN

Let `X` be an algebraic space and `𝓕` a quasi-coherent `𝒪_X`-module.  For the rule
`𝓕ᵃ : (f : Y ⟶ X) ↦ Γ(Y, f^*𝓕)` of
`StacksFrontier/AlgebraicGeometry/Spaces/Topologies/BigEtaleAssociatedModule.lean`, this file proves
`𝓕ᵃ ≅ π_X^*𝓕` on `(Spaces/X)_étale` and `𝓕ᵃ ≅ a_X^*𝓕` on `(Spaces/X)_fppf`, that `π_X^*` and
`a_X^*` are equivalences onto the quasi-coherent modules of the big sites, that
`ε_{X,*}a_X^*𝓕 ≅ π_X^*𝓕` and `𝓕 ≅ a_{X,*}a_X^*𝓕`, and that `R^iε_{X,*}(a_X^*𝓕)` and
`R^ia_{X,*}(a_X^*𝓕)` vanish for `i > 0`.

## Main results

* `AlgebraicGeometry.BigEtaleSpaceSite.associatedPresheafIsoPullback`: **clause (2)**.
* `AlgebraicGeometry.BigFppfSpaceSite.nonempty_associatedPresheaf_iso_pullback`: **clause (3)**.
* `AlgebraicGeometry.BigEtaleSpaceSite.quasicoherentPullbackEquivalence`: **clause (4)**.
* `AlgebraicGeometry.BigFppfSpaceSite.quasicoherentPullbackEquivalence`: **clause (5)**.
* `AlgebraicGeometry.BigFppfSpaceSite.pushforward_pullback_of_quasicoherent`: **clause (6)**.
* `AlgebraicGeometry.BigFppfSpaceSite.isZero_rightDerived_pushforward_pullback_of_quasicoherent`:
  **clause (7)**.

## Implementation notes

Clauses (4) to (7) are stated for `𝒪_X`-modules on the spaces-étale ringed site of `X`, whose
sections lie in `Type (u + 1)`: a quasi-coherent module on the big sites need not be `u`-small,
so the transport `ι` from the small étale site of charts enters only clauses (2) and (3).
Clause (3) is deduced from clauses (2) and (6), and clause (4) from clauses (5) and (6) through
the big fppf site `AlgebraicGeometry.BigEtaleSpaceSite.bigFppfSpaceSite`.

## References

* [Stacks Project, Tag 0DGN](https://stacks.math.columbia.edu/tag/0DGN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor Opposite

universe v w₀ w₁ w₂ w₃ u

namespace CategoryTheory.Functor

/-!
### Conjugation as a map of abelian groups

The restriction maps of `𝓕ᵃ` are conjugations by a comparison of functors in the sense of
`CategoryTheory.Functor.conjHom`, and they have to be *additive* maps between *bundled* abelian
groups.  Both the additivity and the bundling are settled here, in the abstract, for a reason
that is purely practical: identifying the group structure that `AddCommGrpCat.of` puts on a Hom
type with the one `CategoryTheory.Preadditive` puts on it is cheap for the kernel when the
categories are variables and extremely expensive when they are the module categories of
algebraic spaces.  Stating every step abstractly means the concrete construction only ever
*applies* these results.
-/

section ConjHomAdditive

variable {C : Type w₀} {D₀ : Type w₁} {D₁ : Type w₂} {D₂ : Type w₃}
  [Category.{v} C] [Category.{v} D₀] [Category.{v} D₁] [Category.{v} D₂]

variable [Preadditive D₀] [Preadditive D₁] [Preadditive D₂]

/-- **Conjugation commutes with a coherent change of comparison.**  Let `e : P₂ ≅ P₁ ⋙ L` and
`e' : Q₂ ≅ Q₁ ⋙ L` be comparisons and `l₁ : Q₁ ≅ P₁`, `l₂ : Q₂ ≅ P₂` isomorphisms compatible with
them.  Then conjugating by `e` and then by `l₂` is conjugating by `l₁` and then by `e'`: both are
conjugation by `l₂ ≪≫ e`.  This is what makes a family of conjugations by the `l`'s an
isomorphism of the presheaves of Hom groups built from `e` and from `e'`. -/
theorem conjGrpHom_comp_conjGrpHom_of_coherence
    {P₁ Q₁ : C ⥤ D₁} {P₂ Q₂ : C ⥤ D₂} {L : D₁ ⥤ D₂} [L.Additive]
    (e : P₂ ≅ P₁ ⋙ L) (e' : Q₂ ≅ Q₁ ⋙ L) (l₁ : Q₁ ≅ P₁) (l₂ : Q₂ ≅ P₂)
    (h : ∀ M, l₂.hom.app M ≫ e.hom.app M = e'.hom.app M ≫ L.map (l₁.hom.app M)) (M N : C) :
    conjGrpHom e M N ≫ conjGrpHom (l₂ ≪≫ (rightUnitor P₂).symm) M N =
      conjGrpHom (l₁ ≪≫ (rightUnitor P₁).symm) M N ≫ conjGrpHom e' M N := by
  rw [← conjGrpHom_comp e (l₂ ≪≫ (rightUnitor P₂).symm) (l₂ ≪≫ e) (rightUnitor L).symm
      (by ext M; simp),
    ← conjGrpHom_comp (l₁ ≪≫ (rightUnitor P₁).symm) e' (l₂ ≪≫ e) (leftUnitor L).symm
      (by ext M; simp [h M])]

end ConjHomAdditive

end CategoryTheory.Functor

namespace AlgebraicGeometry

/-- **Stacks 0DGN (7): the higher direct images of `a_X^*𝓕` along `ε_X` and `a_X` vanish.**  For a
quasi-coherent `𝒪_X`-module `𝓕` on the spaces-étale site of an algebraic space `X` of a big fppf
site, `R^iε_{X,*}(a_X^*𝓕) = 0` and `R^ia_{X,*}(a_X^*𝓕) = 0` for every `i > 0`. -/
theorem BigFppfSpaceSite.isZero_rightDerived_pushforward_pullback_of_quasicoherent
    {S : Scheme.{u}} (T : BigFppfSpaceSite S) (E : BigEtaleSpaceSite S)
    (h : T.schemeSite = E.fppfSite) (X : T.Spaces)
    (F : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem X).O))
    [F.IsQuasicoherentOnSite] (i : ℕ) (hi : 0 < i) :
    Limits.IsZero
      (((fppfToBigEtaleRingedHom T E h X).toRingedToposSiteHom.pushforwardTopos.rightDerived i).obj
        ((fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom.pullbackTopos.obj F)) ∧
    Limits.IsZero
      (((fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom.pushforwardTopos.rightDerived
          i).obj ((fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom.pullbackTopos.obj F)) :=
  ⟨isZero_rightDerived_fppfToBigEtale_pushforward_pullback E h F i hi,
    isZero_rightDerived_pushforward_pullback F i hi⟩

/-- **Stacks 0DGN (6): `ε_{X,*}a_X^*𝓕 = π_X^*𝓕` and `a_{X,*}a_X^*𝓕 = 𝓕`.**  For a quasi-coherent
`𝒪_X`-module `𝓕` on the spaces-étale site of an algebraic space `X` of a big fppf site, the
direct image along `ε_X` of `a_X^*𝓕` is `π_X^*𝓕` (with `𝓕` read on the spaces-étale site of `X`
as an object of the big étale site `E`), and the unit `𝓕 ⟶ a_{X,*}a_X^*𝓕` is an isomorphism. -/
theorem BigFppfSpaceSite.pushforward_pullback_of_quasicoherent
    {S : Scheme.{u}} (T : BigFppfSpaceSite S) (E : BigEtaleSpaceSite S)
    (h : T.schemeSite = E.fppfSite) (X : T.Spaces)
    (F : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem X).O))
    [F.IsQuasicoherentOnSite] :
    Nonempty ((fppfToBigEtaleRingedHom T E h X).toRingedToposSiteHom.pushforwardTopos.obj
        ((fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom.pullbackTopos.obj F) ≅
      (BigEtaleSpaceSite.spacesEtaleRestrictionRingedSiteHom E
        (etaleSpace T E h X)).toRingedToposSiteHom.pullbackTopos.obj
          ((toEtaleSpaceModules T E h X).obj F)) ∧
    IsIso ((fppfToSpacesEtaleRingedSiteHom T
      X).toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos.unit.app F) :=
  ⟨nonempty_fppfToBigEtale_pushforward_pullback_iso T E h X F,
    isIso_unit_app_of_isQuasicoherentOnSite F⟩

/-- **Stacks 0DGN (4): `𝓕 ↦ 𝓕ᵃ = π_X^*𝓕` is an equivalence between quasi-coherent
`𝒪_X`-modules and quasi-coherent modules on `((Spaces/X)_étale, 𝒪)`.**  For an algebraic space
`X` of a big étale site, the adjunction `π_X^* ⊣ π_{X,*}` restricts to an equivalence between
the quasi-coherent `𝒪_X`-modules on the spaces-étale site of `X` and the quasi-coherent modules
on the big étale ringed site of `X`: `π_X^*` preserves quasi-coherence (Stacks 03DO), its unit is
invertible, and every quasi-coherent module on `(Spaces/X)_étale` is `π_X^*𝓗` with `𝓗`
quasi-coherent, so the counit is invertible and `π_{X,*}` preserves quasi-coherence.

The modules of `X` are read, as in clauses (5), (6) and (7), on the spaces-étale ringed site with
sections in `Type (u + 1)`.  The transport `ι` from the small étale site of charts is fully
faithful with essential image the modules with `u`-small sections
(`AlgebraicGeometry.Space.toSpacesEtaleModules_full_faithful_essImage`), and quasi-coherent
modules on `(Spaces/X)_étale` need not be that small; this is why `𝓕ᵃ` is compared with modules
read through `ι` only in clauses (2) and (3). -/
noncomputable def BigEtaleSpaceSite.quasicoherentPullbackEquivalence
    {S : Scheme.{u}} (E : BigEtaleSpaceSite S) (X : E.Spaces) :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (Space.spacesEtaleRingedSite E.fppfSite S E.fppf_mem X).O)).FullSubcategory ≌
      (SheafOfModules.isQuasicoherentOnSite.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (E.bigEtaleRingedSite X).O)).FullSubcategory :=
  let adj := (BigEtaleSpaceSite.spacesEtaleRestrictionRingedSiteHom E
    X).toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos
  haveI := BigEtaleSpaceSite.isIso_spacesEtaleRestriction_unit E X
  adj.restrictEquivalence
    (fun F hF ↦ haveI := hF
      BigEtaleSpaceSite.isQuasicoherentOnSite_spacesEtaleRestriction_pullbackTopos E X F)
    (fun G hG ↦ haveI := hG
      (BigEtaleSpaceSite.isIso_spacesEtaleRestriction_counit_app_of_isQuasicoherentOnSite E X
        G).2)
    (fun F _ ↦ inferInstance)
    (fun {G G'} g hG hG' _ ↦ by
      haveI := hG; haveI := hG'
      haveI :=
        (BigEtaleSpaceSite.isIso_spacesEtaleRestriction_counit_app_of_isQuasicoherentOnSite E X G).1
      haveI :=
        (BigEtaleSpaceSite.isIso_spacesEtaleRestriction_counit_app_of_isQuasicoherentOnSite E X
          G').1
      rw [(IsIso.eq_inv_comp _).2 (adj.counit_naturality g).symm]
      infer_instance)

/-- The functor of the equivalence of Stacks 0DGN (4) is `π_X^*`. -/
theorem BigEtaleSpaceSite.quasicoherentPullbackEquivalence_functor_comp_ι
    {S : Scheme.{u}} (E : BigEtaleSpaceSite S) (X : E.Spaces) :
    (quasicoherentPullbackEquivalence E X).functor ⋙ ObjectProperty.ι _ =
      ObjectProperty.ι _ ⋙
        (spacesEtaleRestrictionRingedSiteHom E X).toRingedToposSiteHom.pullbackTopos :=
  rfl

/-- **The pullback along `a_X` of a quasi-coherent module is quasi-coherent** (Stacks 03DO):
every object of `(Spaces/X)_fppf` maps to `X`, which is an object of the spaces-étale site. -/
theorem BigFppfSpaceSite.isQuasicoherentOnSite_pullbackTopos_of_isQuasicoherentOnSite
    {S : Scheme.{u}} (T : BigFppfSpaceSite S) (X : T.Spaces)
    (F : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem X).O))
    [hF : F.IsQuasicoherentOnSite] :
    ((fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom.pullbackTopos.obj
      F).IsQuasicoherentOnSite :=
  Stacks.Sheaves.LocalizedPullback.isQuasicoherentOnSite_pullbackTopos_ofHom
    (fppfToSpacesEtaleRingedSiteHom T X)
    (fun A ↦ ⟨Space.SpacesEtale.final T.schemeSite S T.scheme_mem X, ⟨Over.homMk A.hom⟩⟩) hF

/-- **Stacks 0DGN (5): `𝓕 ↦ 𝓕ᵃ = a_X^*𝓕` is an equivalence between quasi-coherent
`𝒪_X`-modules and quasi-coherent modules on `((Spaces/X)_fppf, 𝒪)`.**  For an algebraic space
`X` of a big fppf site, the adjunction `a_X^* ⊣ a_{X,*}` restricts to an equivalence between the
quasi-coherent `𝒪_X`-modules on the spaces-étale site of `X` and the quasi-coherent modules on
the big fppf ringed site of `X`: both functors preserve quasi-coherence, the unit is invertible
on quasi-coherent modules by clause (6) and the counit by Stacks 03DX.

The modules of `X` are read, as in clauses (6) and (7), on the spaces-étale ringed site with
sections in `Type (u + 1)`.  The transport `ι` from the small étale site of charts is fully
faithful with essential image the modules with `u`-small sections
(`AlgebraicGeometry.Space.toSpacesEtaleModules_full_faithful_essImage`), and quasi-coherent
modules on `(Spaces/X)_fppf` need not be that small; this is why `𝓕ᵃ` is compared with modules
read through `ι` only in clauses (2) and (3). -/
noncomputable def BigFppfSpaceSite.quasicoherentPullbackEquivalence
    {S : Scheme.{u}} (T : BigFppfSpaceSite S) (X : T.Spaces) :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem X).O)).FullSubcategory ≌
      (SheafOfModules.isQuasicoherentOnSite.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (bigFppfRingedSite T X).O)).FullSubcategory :=
  let adj :=
    (fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos
  adj.restrictEquivalence
    (fun F hF ↦ haveI := hF; isQuasicoherentOnSite_pullbackTopos_of_isQuasicoherentOnSite T X F)
    (fun H hH ↦ haveI := hH; isQuasicoherentOnSite_pushforward_of_isQuasicoherentOnSite H)
    (fun F hF ↦ haveI := hF; isIso_unit_app_of_isQuasicoherentOnSite F)
    (fun {H H'} g hH hH' _ ↦ by
      haveI := hH; haveI := hH'
      haveI := isIso_counit_app_of_isQuasicoherentOnSite H
      haveI := isIso_counit_app_of_isQuasicoherentOnSite H'
      rw [(IsIso.eq_inv_comp _).2 (adj.counit_naturality g).symm]
      infer_instance)

/-- The functor of the equivalence of Stacks 0DGN (5) is `a_X^*`. -/
theorem BigFppfSpaceSite.quasicoherentPullbackEquivalence_functor_comp_ι
    {S : Scheme.{u}} (T : BigFppfSpaceSite S) (X : T.Spaces) :
    (quasicoherentPullbackEquivalence T X).functor ⋙ ObjectProperty.ι _ =
      ObjectProperty.ι _ ⋙
        (fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom.pullbackTopos :=
  rfl

/-- The restriction maps of `𝓕ᵃ` on the big étale site, as conjugations. -/
theorem BigEtaleSpaceSite.associatedPresheaf_map_eq {S : Scheme.{u}}
    (T : BigEtaleSpaceSite S) (X : T.Spaces)
    (F : Space.Modules.{u, u} T.fppfSite S T.fppf_mem X.1 X.2) {Y Y' : Over X} (m : Y' ⟶ Y) :
    (T.associatedPresheaf X F).map m.op =
      conjGrpHom (Space.modulePullbackTriangle T.fppfSite S T.fppf_mem (Over.w m))
        (SheafOfModules.unit _ : Space.Modules.{u, u} T.fppfSite S T.fppf_mem X.1 X.2) F := rfl

/-- The inverse of the equivalence of slices induced by the identity equivalence is isomorphic
to the identity functor. -/
def _root_.CategoryTheory.Over.postEquivReflInverseIso {C : Type w₀} [Category.{v} C] (X : C) :
    (Over.postEquiv (X := X) (CategoryTheory.Equivalence.refl (C := C))).inverse ≅ 𝟭 (Over X) :=
  NatIso.ofComponents
    (fun Y ↦ Over.isoMk (Iso.refl Y.left) ((Category.id_comp _).trans (Category.comp_id _).symm))
    (fun _ ↦ Over.OverMorphism.ext ((Category.comp_id _).trans (Category.id_comp _).symm))

/-- The underlying presheaf of abelian groups of the pushforward `f_*M` of a module along a
morphism of ringed topoi is the underlying presheaf of `M` precomposed with `u.op`. -/
theorem RingedToposSiteHom.pushforwardTopos_obj_val_presheaf {X Y : RingedTopos.{u, u, u}}
    [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (f : RingedToposSiteHom X Y)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (f.pushforwardTopos.obj M).val.presheaf = f.u.op ⋙ M.val.presheaf :=
  rfl

/-- **Stacks 0DGN (2): `𝓕ᵃ = π_X^*𝓕` on `(Spaces/X)_étale`.**  For a quasi-coherent
`𝒪_X`-module `𝓕` on the small étale site of an algebraic space `X` of a big étale site, the
presheaf `𝓕ᵃ : (f : Y ⟶ X) ↦ Γ(Y, f^*𝓕)` is isomorphic, as a presheaf of abelian groups on
`(Spaces/X)_étale`, to the underlying presheaf of `π_X^*𝓕`.

Here `𝓕` is read on the spaces-étale site of `X` through the transport `ι`
(`AlgebraicGeometry.Space.toSpacesEtaleModules`), which is fully faithful with essential image the
modules with `u`-small sections
(`AlgebraicGeometry.Space.toSpacesEtaleModules_full_faithful_essImage`). The component at
`(f : Y ⟶ X)` sends `α : f^*𝒪_X ⟶ f^*𝓕` to its image under `ι`, transported through
`f_{small}^*(ι𝓕) ≅ ι(f^*𝓕)` and `f_{small}^*(ι𝓕) ≅ i_f^*π_X^*(ι𝓕)`, evaluated at `1`. -/
noncomputable def BigEtaleSpaceSite.associatedPresheafIsoPullback {S : Scheme.{u}}
    (T : BigEtaleSpaceSite S) (X : T.Spaces)
    (F : Space.Modules.{u, u} T.fppfSite S T.fppf_mem X.1 X.2) [F.IsQuasicoherentOnSite] :
    T.associatedPresheaf X F ≅ ((BigEtaleSpaceSite.spacesEtaleRestrictionRingedSiteHom T
      X).toRingedToposSiteHom.pullbackTopos.obj
        ((Space.toSpacesEtaleModules T.fppfSite S T.fppf_mem X).obj F)).val.presheaf :=
  NatIso.ofComponents (fun Y ↦ (associatedSectionsAddEquiv T F Y.unop).toAddCommGrpIso)
    (fun {_ Y₂} m ↦ (eq_whisker (associatedPresheaf_map_eq T X F m.unop) _).trans
      (AddCommGrpCat.comp_toAddCommGrpIso_hom _ _ _ _ fun α ↦
        associatedSectionsAddEquiv_naturality T F m.unop α))

/-- **Stacks 0DGN (3): `𝓕ᵃ = a_X^*𝓕` on `(Spaces/X)_fppf`.**  For a quasi-coherent `𝒪_X`-module
`𝓕` on the small étale site of an algebraic space `X` of a big fppf site `T`, the presheaf
`𝓕ᵃ : (f : Y ⟶ X) ↦ Γ(Y, f^*𝓕)` on the category `Over X` underlying `(Spaces/X)_fppf` is
isomorphic, as a presheaf of abelian groups, to the underlying presheaf of `a_X^*𝓕`.

Here `𝓕` is read on the spaces-étale site of `X` through the transport `ι`
(`AlgebraicGeometry.Space.toSpacesEtaleModules`), which is fully faithful with essential image
the modules with `u`-small sections.  The statement is that an isomorphism exists: it is obtained
from clause (2) and the isomorphism `ε_{X,*}a_X^*𝓕 ≅ π_X^*𝓕` of clause (6), which is itself
stated as an existence, both applied to the big étale site
`AlgebraicGeometry.BigFppfSpaceSite.bigEtaleSpaceSite` built on the algebraic spaces of `T`. -/
theorem BigFppfSpaceSite.nonempty_associatedPresheaf_iso_pullback
    {S : Scheme.{u}} (T : BigFppfSpaceSite S) (X : T.Spaces)
    (F : Space.Modules.{u, u} T.schemeSite S T.scheme_mem X.1 X.2)
    [hF : F.IsQuasicoherentOnSite] :
    Nonempty (Space.associatedPresheaf F ≅
      ((fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom.pullbackTopos.obj
        ((Space.toSpacesEtaleModules T.schemeSite S T.scheme_mem X).obj F)).val.presheaf) := by
  obtain ⟨E, h⟩ : ∃ E : BigEtaleSpaceSite S, T.schemeSite = E.fppfSite :=
    ⟨T.bigEtaleSpaceSite, T.bigEtaleSpaceSite_fppfSite.symm⟩
  cases E with
  | mk eSchemeSite eSchemeMem eFppfSite eFppfMem eInitial eInitialSmall eInitialEtale eBound
      eOrdinal eOrdinalLim eInitialBounded eIsSite eRepresentative =>
    change T.schemeSite = eFppfSite at h
    cases h
    let E' : BigEtaleSpaceSite S := ⟨eSchemeSite, eSchemeMem, T.schemeSite, eFppfMem, eInitial,
      eInitialSmall, eInitialEtale, eBound, eOrdinal, eOrdinalLim, eInitialBounded, eIsSite,
      eRepresentative⟩
    have := Space.isQuasicoherentOnSite_toSpacesEtaleModules T.schemeSite S T.scheme_mem X F
    obtain ⟨e6⟩ := nonempty_fppfToBigEtale_pushforward_pullback_iso T E' rfl X
      ((Space.toSpacesEtaleModules T.schemeSite S T.scheme_mem X).obj F)
    have e2 := @BigEtaleSpaceSite.associatedPresheafIsoPullback S E' (etaleSpace T E' rfl X) F hF
    have e6' := (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).mapIso e6
    refine ⟨e2 ≪≫ e6'.symm ≪≫ eqToIso (RingedToposSiteHom.pushforwardTopos_obj_val_presheaf
      (fppfToBigEtaleRingedHom T E' rfl X).toRingedToposSiteHom
      ((fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom.pullbackTopos.obj
          ((Space.toSpacesEtaleModules T.schemeSite S T.scheme_mem X).obj F))) ≪≫ ?_⟩
    exact Functor.isoWhiskerRight (NatIso.op (Over.postEquivReflInverseIso X :
      (fppfToBigEtaleRingedHom T E' rfl X).toRingedToposSiteHom.u ≅ 𝟭 _)).symm
        ((fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom.pullbackTopos.obj
          ((Space.toSpacesEtaleModules T.schemeSite S T.scheme_mem X).obj F)).val.presheaf ≪≫
      Functor.leftUnitor _

end AlgebraicGeometry

end
