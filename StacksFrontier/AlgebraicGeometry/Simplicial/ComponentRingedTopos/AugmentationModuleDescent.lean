module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.AugmentationCartesianModule
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentSheafify
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringDegreeZeroFaithful
public import StacksFrontier.CategoryTheory.Sites.Simplicial.RingedToposMorphism
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackModulesDescent
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CartesianModuleUnderlying
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationCartesian
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringSituationDescent

/-!
# Descent of sheaves of modules along a ringed augmentation

Let `S` be a simplicial-site situation, `a` an augmentation of `S` towards a site `(D, K)` and
`A` a ringed augmentation of Stacks 0D9D, with morphism of ringed topoi
`a : (Sh(C_total), O) ⟶ (Sh(D), O_D)`. Stacks 0D9Z says that for a hypercovering the pullback
`a^* : Mod(O_D) ⟶ Mod(O)` is fully faithful with essential image the cartesian `O`-modules, with
`a_*` as quasi-inverse. The source proves it by observing that the structure map of `a` is the
identification `O = a^{-1}O_D`, so that `a^*` is `a^{-1}`, and quoting the statement for sheaves
of sets, Stacks 0D8E.

Two of the clauses are obtained here, in the same shape as the clauses of Stacks 0D8E that the
development has: every sheaf of modules in the essential image of `a^*` is cartesian, and, for a
hypercovering, `a^*` is faithful. The second is proved from faithfulness of the inverse image
`a^{-1}` on sheaves of sets, which for a hypercovering is Stacks 0D8E (1).

## Main results

* `CategoryTheory.SimplicialSiteSituation.isCartesianModule_of_iso`: a sheaf of `O`-modules
  isomorphic to a cartesian one is cartesian.
* `CategoryTheory.SimplicialSiteSituation.RingedAugmentation.isCartesianModule_of_mem_essImage`:
  **Stacks 0D9Z**, the inclusion of the essential image of `a^*` in the cartesian `O`-modules.
* `CategoryTheory.SimplicialSiteSituation.RingedAugmentation`
  `.faithful_pullbackModules_of_faithful_inverseImage`: faithfulness of `a^*` for any ringed
  augmentation whose inverse image on sheaves of sets is faithful.
* `CategoryTheory.SimplicialSiteSituation.RingedAugmentation.faithful_pullbackModules`:
  **Stacks 0D9Z**, faithfulness of `a^*` for a hypercovering.

## Implementation notes

The condition `O = a^{-1}O_D` of Stacks 0D9W enters as invertibility of the inverse-image form
of the structure map of `a`, which is what makes
`AlgebraicGeometry.RingedToposHom.pullbackUnderlyingIsoOfIsIso` available: the underlying sheaf
of sets of `a^*M` is then `a^{-1}` of the underlying sheaf of `M`, naturally in `M`. Since the
underlying sheaf of a sheaf of modules is a faithful functor, faithfulness of `a^*` follows from
faithfulness of `a^{-1}`.

Faithfulness of `a^{-1}` is not a property of an arbitrary augmentation, so the tagged statement
is the one the source makes: for the ringed augmentation of a hypercovering of the final
presheaf, where the inverse image of the morphism of topoi of Stacks 0D70 is faithful by
`CategoryTheory.SimplicialSemiRepresentable.faithful_situationTotalInverseImage`, which is
Stacks 0D8E (1). The general criterion, at an arbitrary ringed augmentation whose structure map
is invertible, is kept separately as `faithful_pullbackModules_of_faithful_inverseImage`; it is
what the slice-site analogue Stacks 0DA4 consumes.

The remaining two clauses — that `a^*` is full, and that every cartesian `O`-module lies in its
essential image, so that `a_*` is a quasi-inverse — are not proved here, and no `0D9Z`
attribute is placed on anything asserting them. They rest on the corresponding clauses of
Stacks 0D8E, which the development does not have either.

Sheaves of modules are formed at the site universe, as in
`StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/CartesianModule.lean`, and the
two sheafification instances the pullback of modules asks of the total site are supplied
locally, as in that file.

## References

* [Stacks Project, Tag 0D9Z](https://stacks.math.columbia.edu/tag/0D9Z)
* [Stacks Project, Tag 0D8E](https://stacks.math.columbia.edu/tag/0D8E)
* [Stacks Project, Tag 0D9W](https://stacks.math.columbia.edu/tag/0D9W)
* [Stacks Project, Tag 0D7H](https://stacks.math.columbia.edu/tag/0D7H)
* [Stacks Project, Tag 07TF](https://stacks.math.columbia.edu/tag/07TF)
* [Stacks Project, Section 85.10 (Tag 0D9D)](https://stacks.math.columbia.edu/tag/0D9D)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace CategoryTheory.SimplicialSiteSituation

/-- Abelian sheaves on the total site are sheafifiable at the site universe, the total category
being small there. -/
local instance hasWeakSheafifyTotalModuleDescent (S : SimplicialSiteSituation.{u}) :
    HasWeakSheafify S.totalTopology AddCommGrpCat.{u} :=
  (GrothendieckTopology.hasSheafify_addCommGrpCat.{u, u, u} S.totalTopology).1

/-- On the total site at the site universe, the maps inverted by sheafification of abelian
sheaves are exactly the locally bijective ones. -/
local instance wEqualsLocallyBijectiveTotalModuleDescent (S : SimplicialSiteSituation.{u}) :
    S.totalTopology.WEqualsLocallyBijective AddCommGrpCat.{u} :=
  letI : HasSheafify ((equivSmallModel.{u} (S.totalCategory : Type u)).inverse.inducedTopology
      S.totalTopology) AddCommGrpCat.{u} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{u, u, u} _
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u, u, u + 1, u}
    S.totalTopology

attribute [local instance] hasWeakSheafifyComponent

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

/-- A sheaf of `O`-modules on the total site isomorphic to a cartesian one is cartesian: the
transitions of the two are conjugate by the isomorphism, through naturality of
`CategoryTheory.SimplicialSiteSituation.moduleFiberTransition`. -/
theorem isCartesianModule_of_iso
    {F F' : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology)) O)}
    (e : F ≅ F')
    (h : S.IsModuleFiberTransitionIso O F) : S.IsModuleFiberTransitionIso O F' := by
  intro m n φ
  have := h φ
  have h1 : IsIso (((componentRingedToposHom S O m).toModulesHom.pullbackModules ⋙
      (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules).map e.hom) :=
    (((componentRingedToposHom S O m).toModulesHom.pullbackModules ⋙
      (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules).mapIso e).isIso_hom
  have h2 : IsIso ((componentRingedToposHom S O n).toModulesHom.pullbackModules.map e.hom) :=
    ((componentRingedToposHom S O n).toModulesHom.pullbackModules.mapIso e).isIso_hom
  have hnat := (S.moduleFiberTransition O φ).naturality e.hom
  have hrw : (S.moduleFiberTransition O φ).app F' =
      inv (((componentRingedToposHom S O m).toModulesHom.pullbackModules ⋙
            (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules).map e.hom) ≫
        (S.moduleFiberTransition O φ).app F ≫
          (componentRingedToposHom S O n).toModulesHom.pullbackModules.map e.hom := by
    rw [← hnat, IsIso.inv_hom_id_assoc]
  rw [hrw]
  infer_instance

namespace RingedAugmentation

section General

variable {S : SimplicialSiteSituation.{u}} {D : Cat.{u, u}} {K : GrothendieckTopology D}
  {a : Augmentation S D K} (A : RingedAugmentation S D K a)

/-- **Stacks 0D9Z, the inclusion of the essential image in the cartesian modules.** Every sheaf
of `O`-modules on the total site isomorphic to a pullback `a^*F` along the ringed augmentation is
a cartesian `O`-module.

This is Stacks 0D7H (3) together with invariance of the cartesian condition under isomorphism. -/
@[stacks 0D9Z "the essential image of a^* consists of cartesian O-modules. Faithfulness of a^* \
is `faithful_pullbackModules`; fullness of a^*, and essential surjectivity onto the cartesian \
O-modules making a_* a quasi-inverse, are not proved"]
theorem isCartesianModule_of_mem_essImage
    {F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf A.O)}
    (hF : A.totalRingedHom.toModulesHom.pullbackModules.essImage F) :
    S.IsModuleFiberTransitionIso A.O F := by
  obtain ⟨G, ⟨e⟩⟩ := hF
  exact isCartesianModule_of_iso S A.O e (A.isCartesianModule_pullbackModules G)

/-- **The pullback of sheaves of modules along a ringed augmentation is faithful as soon as the
inverse image on sheaves of sets is.** The pullback `a^* : Mod(O_D) ⥤ Mod(O)` along a ringed
augmentation whose structure map is the identification `O = a^{-1}O_D` of Stacks 0D9W is
faithful whenever `a^{-1}` is.

Invertibility of the structure map makes the underlying sheaf of sets of `a^*M` the inverse image
of the underlying sheaf of `M`, naturally in `M`, and the underlying sheaf of a sheaf of modules
is a faithful functor. -/
theorem faithful_pullbackModules_of_faithful_inverseImage
    [IsIso A.totalRingedHom.fSharpInverseImage]
    (hfaithful : A.totalRingedHom.toToposHom.inverseImage.Faithful) :
    A.totalRingedHom.toModulesHom.pullbackModules.Faithful := by
  have := hfaithful
  have : (Sheaf.moduleSheafFunctor
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := A.augmentationRingedTopos.J))
      A.augmentationRingedTopos.O)).Faithful := Functor.Faithful.comp _ _
  have : (Sheaf.moduleSheafFunctor
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := A.augmentationRingedTopos.J))
        A.augmentationRingedTopos.O) ⋙
      A.totalRingedHom.toToposHom.inverseImage).Faithful := Functor.Faithful.comp _ _
  have : (A.totalRingedHom.toModulesHom.pullbackModules ⋙
      Sheaf.moduleSheafFunctor
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (S.totalRingedTopos A.O).J))
        (S.totalRingedTopos A.O).O)).Faithful :=
    Functor.Faithful.of_iso
      (RingedToposHom.pullbackUnderlyingIsoOfIsIso.{u} A.totalRingedHom).symm
  exact Functor.Faithful.of_comp A.totalRingedHom.toModulesHom.pullbackModules
    (Sheaf.moduleSheafFunctor
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (S.totalRingedTopos A.O).J))
      (S.totalRingedTopos A.O).O))

/-- **The structure sheaf of a ringed augmentation whose structure map is the identification
`O = a^{-1}O_D` is cartesian.** Its underlying sheaf of sets is then the inverse image of the
underlying sheaf of `O_D`, which is cartesian by Stacks 0D7H (1). -/
theorem isCartesianSheaf_underlyingO [hiso : IsIso A.totalRingedHom.fSharpInverseImage] :
    S.IsCartesianSheaf ((sheafCompose S.totalTopology (forget CommRingCat.{u})).obj A.O) :=
  isCartesianSheaf_of_iso S
    ((sheafCompose S.totalTopology (forget CommRingCat.{u})).mapIso
      (@asIso _ _ _ _ A.totalRingedHom.fSharpInverseImage hiso))
    (Augmentation.isCartesianSheaf_totalMorphismOfTopoi_inverseImage S D K a
      ((sheafCompose K (forget CommRingCat.{u})).obj A.OD))

/-- **The pullback of sheaves of modules along a ringed augmentation is full as soon as the
inverse image on sheaves of sets is fully faithful.** The pullback `a^* : Mod(O_D) ⥤ Mod(O)` along
a ringed augmentation whose structure map is the identification `O = a^{-1}O_D` of Stacks 0D9W is
full whenever `a^{-1}` is fully faithful.

Invertibility of the structure map makes the pullback the Stacks 03D2 inverse image of modules
followed by an equivalence, and the first factor is transport along `a^{-1}`. -/
theorem full_pullbackModules_of_full_inverseImage
    [IsIso A.totalRingedHom.fSharpInverseImage]
    (hfull : A.totalRingedHom.toToposHom.inverseImage.Full)
    (hfaithful : A.totalRingedHom.toToposHom.inverseImage.Faithful) :
    A.totalRingedHom.toModulesHom.pullbackModules.Full :=
  have := hfull
  have := hfaithful
  RingedToposHom.full_pullbackModules A.totalRingedHom

/-- **The pullback of sheaves of modules along a ringed augmentation is fully faithful as soon as
the inverse image on sheaves of sets is.** -/
def fullyFaithfulPullbackModules_of_fullyFaithful_inverseImage
    [IsIso A.totalRingedHom.fSharpInverseImage]
    (hfull : A.totalRingedHom.toToposHom.inverseImage.Full)
    (hfaithful : A.totalRingedHom.toToposHom.inverseImage.Faithful) :
    A.totalRingedHom.toModulesHom.pullbackModules.FullyFaithful :=
  haveI := full_pullbackModules_of_full_inverseImage A hfull hfaithful
  haveI := faithful_pullbackModules_of_faithful_inverseImage A hfaithful
  Functor.FullyFaithful.ofFullyFaithful _

/-- **Every cartesian sheaf of `O`-modules is a pullback along the ringed augmentation**, as soon
as every cartesian sheaf of sets is an inverse image along `a^{-1}`.

The underlying sheaf of sets of a cartesian sheaf of modules is cartesian by
`CategoryTheory.SimplicialSiteSituation.isCartesianSheaf_moduleSheaf`, the structure sheaf being
cartesian because the structure map of `a` is the identification `O = a^{-1}O_D`; so it is an
inverse image, and a sheaf of modules whose underlying sheaf of sets is an inverse image is a
pullback by
`AlgebraicGeometry.RingedToposHom.essImage_pullbackModules_of_essImage_moduleSheaf`. -/
theorem essImage_pullbackModules_of_isCartesianModule
    [IsIso A.totalRingedHom.fSharpInverseImage]
    (hfull : A.totalRingedHom.toToposHom.inverseImage.Full)
    (hfaithful : A.totalRingedHom.toToposHom.inverseImage.Faithful)
    (hsurj : ∀ G : Sheaf S.totalTopology (Type u), S.IsCartesianSheaf G →
      A.totalRingedHom.toToposHom.inverseImage.essImage G)
    {F : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) A.O))}
    (hF : S.IsModuleFiberTransitionIso A.O F) :
    A.totalRingedHom.toModulesHom.pullbackModules.essImage F :=
  have := hfull
  have := hfaithful
  RingedToposHom.essImage_pullbackModules_of_essImage_moduleSheaf A.totalRingedHom F
    (hsurj _ (S.isCartesianSheaf_moduleSheaf A.O (A.isCartesianSheaf_underlyingO) hF))

end General

section Hypercovering

open Stacks.CategoryTheory.Hypercovering SimplicialSemiRepresentable

variable {C : Type u} [SmallCategory C] [HasEqualizers C] [HasPullbacks C] {P : Pretopology C}
  (H : HypercoveringOfTerminal.{u, u, u} P)
  (A : RingedAugmentation (situation P.toGrothendieck H.toSimplicialObject) (Cat.of C)
    P.toGrothendieck (situationAugmentation P.toGrothendieck H.toSimplicialObject))

/-- **Stacks 0D9Z, the faithfulness half.** Let `C` be a site with equalizers and fibre products,
`K` a hypercovering of its final presheaf, and `a` the augmentation of the total site of `K`
towards `C`. For a ringed augmentation along `a` whose structure map is the identification
`O = a^{-1}O_C` of Stacks 0D9W, the pullback `a^* : Mod(O_C) ⥤ Mod(O)` of sheaves of modules is
faithful.

Because the structure map is that identification, the underlying sheaf of sets of `a^*M` is the
inverse image of the underlying sheaf of `M`; faithfulness then descends from Stacks 0D8E (1),
faithfulness of `a^{-1}` on sheaves of sets. -/
@[stacks 0D9Z "a^* on sheaves of modules is faithful, for a ringed augmentation of a \
hypercovering whose structure map is the identification O = a^{-1}O_C. The essential-image \
inclusion is `isCartesianModule_of_mem_essImage`; fullness of a^*, and essential surjectivity \
onto the cartesian O-modules making a_* a quasi-inverse, are not proved"]
theorem faithful_pullbackModules [IsIso A.totalRingedHom.fSharpInverseImage] :
    A.totalRingedHom.toModulesHom.pullbackModules.Faithful :=
  faithful_pullbackModules_of_faithful_inverseImage A (faithful_situationTotalInverseImage P H)

/-- **Stacks 0D9Z, the fullness half.** For a ringed augmentation of a hypercovering whose
structure map is the identification `O = a^{-1}O_C` of Stacks 0D9W, the pullback
`a^* : Mod(O_C) ⥤ Mod(O)` of sheaves of modules is full.

Because the structure map is that identification, the pullback of modules is the Stacks 03D2
inverse image of modules followed by an equivalence; fullness then descends from Stacks 0D8E (1),
full faithfulness of `a^{-1}` on sheaves of sets. -/
@[stacks 0D9Z "a^* on sheaves of modules is full, for a ringed augmentation of a hypercovering \
whose structure map is the identification O = a^{-1}O_C"]
theorem full_pullbackModules [IsIso A.totalRingedHom.fSharpInverseImage] :
    A.totalRingedHom.toModulesHom.pullbackModules.Full :=
  full_pullbackModules_of_full_inverseImage A (full_situationTotalInverseImage P H)
    (faithful_situationTotalInverseImage P H)

/-- **Stacks 0D9Z, full faithfulness of `a^*` on sheaves of modules.** -/
@[stacks 0D9Z "a^* on sheaves of modules is fully faithful, for a ringed augmentation of a \
hypercovering whose structure map is the identification O = a^{-1}O_C"]
def fullyFaithfulPullbackModules [IsIso A.totalRingedHom.fSharpInverseImage] :
    A.totalRingedHom.toModulesHom.pullbackModules.FullyFaithful :=
  fullyFaithfulPullbackModules_of_fullyFaithful_inverseImage A
    (full_situationTotalInverseImage P H) (faithful_situationTotalInverseImage P H)

/-- **Stacks 0D9Z, essential surjectivity onto the cartesian `O`-modules.** For a ringed
augmentation of a hypercovering whose structure map is the identification `O = a^{-1}O_C` of
Stacks 0D9W, every cartesian sheaf of `O`-modules on the total site is a pullback `a^*M`.

The underlying sheaf of sets of a cartesian sheaf of modules is cartesian, hence an inverse image
by Stacks 0D8E (1); and a sheaf of modules whose underlying sheaf of sets is an inverse image is a
pullback. -/
@[stacks 0D9Z "every cartesian O-module is an a^*M, for a ringed augmentation of a hypercovering \
whose structure map is the identification O = a^{-1}O_C"]
theorem essImage_pullbackModules [IsIso A.totalRingedHom.fSharpInverseImage]
    {F : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
      (J := (situation P.toGrothendieck H.toSimplicialObject).totalTopology) A.O))}
    (hF : (situation P.toGrothendieck H.toSimplicialObject).IsModuleFiberTransitionIso A.O F) :
    A.totalRingedHom.toModulesHom.pullbackModules.essImage F :=
  essImage_pullbackModules_of_isCartesianModule A (full_situationTotalInverseImage P H)
    (faithful_situationTotalInverseImage P H)
    (fun G hG => essImage_situationTotalInverseImage_of_isCartesianSheaf P H G hG) hF

/-- **Stacks 0D9Z, the essential image of `a^*` is exactly the cartesian `O`-modules.** One
inclusion is `isCartesianModule_of_mem_essImage`, which is Stacks 0D7H (3); the other is
`essImage_pullbackModules`. -/
@[stacks 0D9Z "the essential image of a^* on sheaves of modules is exactly the cartesian \
O-modules, for a ringed augmentation of a hypercovering whose structure map is the \
identification O = a^{-1}O_C"]
theorem mem_essImage_pullbackModules_iff_isCartesianModule
    [IsIso A.totalRingedHom.fSharpInverseImage]
    (F : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
      (J := (situation P.toGrothendieck H.toSimplicialObject).totalTopology) A.O))) :
    A.totalRingedHom.toModulesHom.pullbackModules.essImage F ↔
      (situation P.toGrothendieck H.toSimplicialObject).IsModuleFiberTransitionIso A.O F :=
  ⟨isCartesianModule_of_mem_essImage A, essImage_pullbackModules H A⟩

/-- **Stacks 0D9Z, `a_*` is a quasi-inverse on `Mod(O_C)`.** The unit `M ⟶ a_*a^*M` of the
adjunction of Stacks 03D7 is an isomorphism for every sheaf of `O_C`-modules: a fully faithful
left adjoint has invertible unit. -/
@[stacks 0D9Z "M = a_* a^* M on sheaves of modules, for a ringed augmentation of a hypercovering \
whose structure map is the identification O = a^{-1}O_C"]
theorem isIso_pullbackAdjPushforwardModules_unit
    [IsIso A.totalRingedHom.fSharpInverseImage] :
    IsIso (RingedToposHom.pullbackAdjPushforwardModules A.totalRingedHom).unit :=
  have := full_pullbackModules H A
  have := faithful_pullbackModules H A
  Adjunction.unit_isIso_of_L_fully_faithful
    (RingedToposHom.pullbackAdjPushforwardModules A.totalRingedHom)

/-- **Stacks 0D9Z, `a_*` is a quasi-inverse on the cartesian `O`-modules.** The counit
`a^*a_*F ⟶ F` of the adjunction of Stacks 03D7 is an isomorphism at every cartesian sheaf of
`O`-modules: a fully faithful left adjoint has invertible counit exactly on its essential image,
which by `mem_essImage_pullbackModules_iff_isCartesianModule` is the cartesian `O`-modules. -/
@[stacks 0D9Z "a^* a_* F = F for a cartesian O-module F, for a ringed augmentation of a \
hypercovering whose structure map is the identification O = a^{-1}O_C"]
theorem isIso_pullbackAdjPushforwardModules_counit_app
    [IsIso A.totalRingedHom.fSharpInverseImage]
    {F : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
      (J := (situation P.toGrothendieck H.toSimplicialObject).totalTopology) A.O))}
    (hF : (situation P.toGrothendieck H.toSimplicialObject).IsModuleFiberTransitionIso A.O F) :
    IsIso ((RingedToposHom.pullbackAdjPushforwardModules A.totalRingedHom).counit.app F) :=
  have := full_pullbackModules H A
  have := faithful_pullbackModules H A
  ((RingedToposHom.pullbackAdjPushforwardModules
    A.totalRingedHom).isIso_counit_app_iff_mem_essImage).mpr (essImage_pullbackModules H A hF)

end Hypercovering

end RingedAugmentation

end CategoryTheory.SimplicialSiteSituation

end
