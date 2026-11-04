module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.AugmentationModuleDescent
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringObjectDescent

/-!
# Descent of sheaves of modules along the augmentation of a hypercovering of an object

Let `C` be a site with fibre products, let `O_C` be a sheaf of commutative rings on it, let `X`
be an object of `C` and set `O_X = O_C|_{C/X}`. Let `K` be a hypercovering of `X` in the sense of
Stacks 01G5. The site `C/X` has a final object and fibre products, and `K` is a simplicial
semi-representable object of it, so the simplicial-site apparatus applies with `C/X` in place of
`C`: the total site `(C/K)_total` carries the pulled-back structure sheaf `O = a⁻¹O_X`, and the
augmentation becomes a morphism of ringed topoi
`a : (Sh((C/K)_total), O) ⟶ (Sh(C/X), O_X)`, which is the ringed variant over an object of
Remarks 0D9V and 0D9X.

Stacks 0DA4 asserts that `a^* : Mod(O_X) ⟶ Mod(O)` is fully faithful with essential image the
cartesian `O`-modules, with `a_*` as quasi-inverse. This file proves, for a hypercovering of `X`,
the two clauses that follow from the *degree-zero* condition on `K` alone, in the same shape as
the clauses of Stacks 0D8K that the development carries for sheaves of sets and of abelian
groups:

* `a^*` is faithful, and
* every sheaf of modules in the essential image of `a^*` is cartesian.

The input for the first is cover density of the degree-zero localization functor
`j_0 : (C/X)/K_0 ⥤ C/X`. The degree-zero clause of Stacks 01G5 makes every object of `C/X`
covered by objects admitting a morphism over `X` to a component of `K_0`
(`CategoryTheory.SimplicialSemiRepresentable.degreeZeroSieveOver_mem`), and every such object,
with that morphism, lies in the image of `j_0`; restriction along a continuous cover-dense functor
is faithful by Stacks 04D9. Restriction of the inverse image of the total augmentation to
simplicial degree zero is the inverse image of the degree-zero component augmentation
(Stacks 0D70, compatibility (b)), which by Stacks 0D8B is that restriction, so the inverse image
of the total augmentation is faithful as well. Faithfulness of `a^*` on sheaves of modules then
follows because the structure map of `a` is the identification `O = a⁻¹O_X` of Stacks 0D9X.

The second clause is Stacks 0D7H (3) together with invariance of the cartesian condition under
isomorphism.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.inverseImageRingedAugmentation`: the ringed
  augmentation of Stacks 0D9D whose structure sheaf on the total site is the inverse image of a
  given sheaf of commutative rings on the augmentation site.
* `CategoryTheory.SimplicialSemiRepresentable.hypercoveringObjectRingedAugmentation`:
  **Stacks 0D9X**, that ringed augmentation for the total site of a hypercovering of `X` over the
  slice site `C/X`, with structure sheaf the restriction of `O_C`.

## Main results

* `CategoryTheory.SimplicialSiteSituation.Augmentation.faithful_inverseImage_of_component`: the
  inverse image of the total augmentation of a simplicial-site situation is faithful as soon as
  the inverse image of one of its component augmentations is.
* `CategoryTheory.SimplicialSemiRepresentable.isCoverDense_sliceForgetZero_over`: the degree-zero
  localization functor of a hypercovering of `X` is cover dense over `C/X`.
* `CategoryTheory.SimplicialSemiRepresentable.faithful_situationTotalInverseImage_over`: the
  inverse image `a^{-1}` on sheaves of sets, as Stacks 0D70 constructs it from the
  simplicial-site situation of `C/X`, is faithful.
* `CategoryTheory.SimplicialSemiRepresentable.faithful_pullbackModules_over`: **Stacks 0DA4**,
  faithfulness of `a^*` on sheaves of modules.
* `CategoryTheory.SimplicialSemiRepresentable.isCartesianModule_of_mem_essImage_over`:
  **Stacks 0DA4**, the inclusion of the essential image of `a^*` in the cartesian `O`-modules.

## Implementation notes

The two remaining clauses of Stacks 0DA4 — that `a^*` is full, and that every cartesian
`O`-module lies in its essential image, so that `a_*` is a quasi-inverse — are *not* proved here,
and no `0DA4` attribute is placed on anything asserting them. They are the corresponding clauses
of Stacks 0D9Z and of Stacks 0D8K, which the development does not carry either: both need the
higher conditions on a hypercovering, and the degree-zero condition used here does not supply
them. For the constant simplicial object on a covering the degree-zero condition holds while
`a^*` is faithful and not full. The attributes are therefore part-scoped to the two clauses
proved.

The structure sheaf of the total site is the inverse image of `O_X` along the total augmentation,
with the unit of `a⁻¹ ⊣ a_*` as the structure map. That is the reading of Stacks 0D9X in which
the structure map is invertible on the nose:
`inverseImageRingedAugmentation_fSharpInverseImage` computes its inverse-image form to be the
identity, and invertibility of the structure map is exactly the hypothesis under which
`CategoryTheory.SimplicialSiteSituation.RingedAugmentation`
`.faithful_pullbackModules_of_faithful_inverseImage` turns faithfulness of `a^{-1}` into
faithfulness of `a^*`.

Faithfulness of the total inverse image is deduced from the degree-zero *component*
augmentation rather than from restriction along `j_total`. The morphism of topoi that Stacks 0D70
attaches to a simplicial-site situation is built as the descent of the inverse images along the
component augmentations, and the comparison of that construction with the cocontinuous
pushforward along `j_total` — which is what
`CategoryTheory.SimplicialSemiRepresentable.faithful_totalInverseImage_over` of Stacks 0D8K is
stated for — is not available in the development; the comparison in a single simplicial degree
is, namely `CategoryTheory.SimplicialSemiRepresentable.componentInverseImageIso` of
Stacks 0D8B.

Sheaves of modules are formed at the site universe, as in
`StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/CartesianModule.lean`. The three
sheafification instances this needs are stated for an arbitrary simplicial-site situation and
attached as local instances for the whole file; the same three are supplied as file-local
instances in
`StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/AugmentationModuleDescent.lean`,
and being local there they are not visible here.

## References

* [Stacks Project, Tag 0DA4](https://stacks.math.columbia.edu/tag/0DA4)
* [Stacks Project, Tag 0D9Z](https://stacks.math.columbia.edu/tag/0D9Z)
* [Stacks Project, Tag 0D9X](https://stacks.math.columbia.edu/tag/0D9X)
* [Stacks Project, Tag 0D9V](https://stacks.math.columbia.edu/tag/0D9V)
* [Stacks Project, Tag 0D8K](https://stacks.math.columbia.edu/tag/0D8K)
* [Stacks Project, Tag 0D8B](https://stacks.math.columbia.edu/tag/0D8B)
* [Stacks Project, Tag 0D70](https://stacks.math.columbia.edu/tag/0D70)
* [Stacks Project, Tag 0D7H](https://stacks.math.columbia.edu/tag/0D7H)
* [Stacks Project, Section 85.10 (Tag 0D9D)](https://stacks.math.columbia.edu/tag/0D9D)
* [Stacks Project, Tag 01G5](https://stacks.math.columbia.edu/tag/01G5)
* [Stacks Project, Tag 04D9](https://stacks.math.columbia.edu/tag/04D9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial AlgebraicGeometry
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.CategoryTheory.Hypercovering

universe u

namespace CategoryTheory.SimplicialSiteSituation

/-- Abelian sheaves on the total site of a simplicial-site situation are sheafifiable at the
site universe, the total category being small there. -/
theorem objectModuleDescentHasWeakSheafifyTotal (S : SimplicialSiteSituation.{u}) :
    HasWeakSheafify S.totalTopology AddCommGrpCat.{u} :=
  (GrothendieckTopology.hasSheafify_addCommGrpCat.{u, u, u} S.totalTopology).1

/-- On the total site at the site universe, the maps inverted by sheafification of abelian
sheaves are exactly the locally bijective ones. -/
theorem objectModuleDescentWEqualsLocallyBijectiveTotal (S : SimplicialSiteSituation.{u}) :
    S.totalTopology.WEqualsLocallyBijective AddCommGrpCat.{u} :=
  let : HasSheafify ((equivSmallModel.{u} (S.totalCategory : Type u)).inverse.inducedTopology
      S.totalTopology) AddCommGrpCat.{u} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{u, u, u} _
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u, u, u + 1, u}
    S.totalTopology

/-- Abelian sheaves on a simplicial component are sheafifiable at the site universe, the
component being small there. -/
alias objectModuleDescentHasWeakSheafifyComponent :=
  CategoryTheory.SimplicialSiteSituation.hasWeakSheafifyComponent

end CategoryTheory.SimplicialSiteSituation

attribute [local instance]
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentHasWeakSheafifyTotal
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentWEqualsLocallyBijectiveTotal
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentHasWeakSheafifyComponent

namespace CategoryTheory.SimplicialSiteSituation

/-! ### The ringed augmentation with the pulled-back structure sheaf -/

variable (S : SimplicialSiteSituation.{u}) (D : Cat.{u, u}) (K : GrothendieckTopology D)
  (a : Augmentation S D K)

/-- **Stacks 0D9W, the structure sheaf of the total site.** The ringed augmentation of
Stacks 0D9D attached to a sheaf of commutative rings `O_D` on the augmentation site by taking
`O = a⁻¹O_D` on the total site and the unit of `a⁻¹ ⊣ a_*` as the structure map. -/
def inverseImageRingedAugmentation (OD : Sheaf K CommRingCat.{u}) :
    RingedAugmentation S D K a where
  O := (inverseImageCommRingFunctor (Augmentation.totalMorphismOfTopoi S D K a)).obj OD
  OD := OD
  aSharp := (commRingImageAdjunction (Augmentation.totalMorphismOfTopoi S D K a)).unit.app OD

/-- The structure map of the ringed augmentation with the pulled-back structure sheaf is, in
inverse-image form, the identity: it is the adjunct of the unit of `a⁻¹ ⊣ a_*`. -/
theorem inverseImageRingedAugmentation_fSharpInverseImage (OD : Sheaf K CommRingCat.{u}) :
    (inverseImageRingedAugmentation S D K a OD).totalRingedHom.fSharpInverseImage = 𝟙 _ := by
  have h : (inverseImageRingedAugmentation S D K a OD).totalRingedHom.fSharpInverseImage =
      ((commRingImageAdjunction (Augmentation.totalMorphismOfTopoi S D K a)).homEquiv OD
        ((inverseImageCommRingFunctor
          (Augmentation.totalMorphismOfTopoi S D K a)).obj OD)).symm
        ((commRingImageAdjunction
          (Augmentation.totalMorphismOfTopoi S D K a)).unit.app OD) := rfl
  rw [h, Adjunction.homEquiv_counit, Adjunction.left_triangle_components]
  rfl

/-- The structure map of the ringed augmentation with the pulled-back structure sheaf is
invertible, being the identity. -/
instance isIso_inverseImageRingedAugmentation_fSharpInverseImage
    (OD : Sheaf K CommRingCat.{u}) :
    IsIso (inverseImageRingedAugmentation S D K a OD).totalRingedHom.fSharpInverseImage := by
  rw [inverseImageRingedAugmentation_fSharpInverseImage]
  exact IsIso.id _

/-! ### Faithfulness of the inverse image of the total augmentation -/

/-- **The inverse image of the total augmentation is faithful as soon as the inverse image of
one of the component augmentations is.** Restriction to a simplicial degree takes the inverse
image of the total augmentation to the inverse image of the augmentation of that degree
(Stacks 0D70, compatibility (b)), and a functor whose composite with another is faithful is
itself faithful. -/
theorem Augmentation.faithful_inverseImage_of_component (n : SimplexCategory)
    (h : (componentAugmentation S D K a n).inverseImage.Faithful) :
    (Augmentation.totalMorphismOfTopoi S D K a).inverseImage.Faithful :=
  have : (Augmentation.inverseImage S D K a ⋙ S.restrict n).Faithful :=
    @Functor.Faithful.of_iso _ _ _ _ _ _ h
      (Augmentation.restrictCompInverseImageIso S D K a n).symm
  Functor.Faithful.of_comp (Augmentation.inverseImage S D K a) (S.restrict n)

end CategoryTheory.SimplicialSiteSituation

namespace CategoryTheory.SimplicialSemiRepresentable

variable {C : Type u} [SmallCategory C]

/-! ### Cover density of the degree-zero localization functor -/

/-- An arrow whose source admits a morphism to a component of `K_0` factors through the image of
the degree-zero localization functor: its source, with that morphism, is an object of `C/K_0`. -/
theorem degreeZeroSieve_le_coverByImage_sliceForget
    (K : SimplicialObject (FormalCoproduct.{u} C)) (X : C) :
    degreeZeroSieve K X ≤ Sieve.coverByImage (sliceForget K (op ⦋0⦌)) X := by
  rintro V g ⟨i, ⟨p⟩⟩
  exact ⟨⟨⟨i, Over.mk p⟩, 𝟙 V, g, Category.id_comp g⟩⟩

variable [HasPullbacks C] (P : Pretopology C) {X : C}
  (K : SimplicialObject (FormalCoproduct.{u} (Over X)))

/-- The degree-zero localization functor `j_0 : (C/X)/K_0 ⥤ C/X` of a hypercovering of `X` is
cover dense: every object of `C/X` is covered by objects admitting a morphism over `X` to a
component of `K_0`, and each of those, with that morphism, is an object of `(C/X)/K_0`. -/
theorem isCoverDense_sliceForgetZero_over
    (hK : IsCoveringOver P (terminal.from (K.obj (op ⦋0⦌)))) :
    (sliceForget K (op ⦋0⦌)).IsCoverDense (P.toGrothendieck.over X) :=
  ⟨fun V => GrothendieckTopology.superset_covering _
    (degreeZeroSieve_le_coverByImage_sliceForget K V) (degreeZeroSieveOver_mem P K hK V)⟩

/-- Restriction along the degree-zero localization functor of a hypercovering of `X` is
faithful: that functor is continuous and cover dense, and restriction along such a functor is
faithful by Stacks 04D9. -/
theorem faithful_degreeZeroInverseImage_over
    (hK : IsCoveringOver P (terminal.from (K.obj (op ⦋0⦌)))) :
    (localizationMorphism (P.toGrothendieck.over X) K ⦋0⦌).inverseImage.Faithful :=
  let := isCoverDense_sliceForgetZero_over P K hK
  sheafPushforwardContinuous_faithful_of_isCoverDense (sliceForget K (op ⦋0⦌))
    ((situation (P.toGrothendieck.over X) K).componentTopology ⦋0⦌)
    (P.toGrothendieck.over X) (Type u)

/-- The inverse image of the degree-zero component augmentation of a hypercovering of `X` is
faithful. By Stacks 0D8B that functor is isomorphic to restriction along `j_0`. -/
theorem faithful_componentAugmentationZeroInverseImage_over
    (hK : IsCoveringOver P (terminal.from (K.obj (op ⦋0⦌)))) :
    (SimplicialSiteSituation.Augmentation.componentAugmentation
      (situation (P.toGrothendieck.over X) K) (Cat.of (Over X)) (P.toGrothendieck.over X)
      (situationAugmentation (P.toGrothendieck.over X) K) ⦋0⦌).inverseImage.Faithful :=
  @Functor.Faithful.of_iso _ _ _ _ _ _ (faithful_degreeZeroInverseImage_over P K hK)
    (componentInverseImageIso (P.toGrothendieck.over X) K ⦋0⦌).symm

/-- **Stacks 0D8K (1), the faithfulness half**, for the inverse image of the total augmentation
as Stacks 0D70 constructs it from the simplicial-site situation of `C/X`. Restriction to
simplicial degree zero carries it to the inverse image of the degree-zero component
augmentation, which is faithful. -/
theorem faithful_situationTotalInverseImage_over (hK : IsHypercovering P K) :
    (SimplicialSiteSituation.Augmentation.totalMorphismOfTopoi
      (situation (P.toGrothendieck.over X) K) (Cat.of (Over X)) (P.toGrothendieck.over X)
      (situationAugmentation (P.toGrothendieck.over X) K)).inverseImage.Faithful :=
  SimplicialSiteSituation.Augmentation.faithful_inverseImage_of_component _ _ _ _ ⦋0⦌
    (faithful_componentAugmentationZeroInverseImage_over P K hK.1)

/-! ### Descent of modules along the augmentation of a hypercovering of an object -/

variable (OC : Sheaf P.toGrothendieck CommRingCat.{u})

/-- **Stacks 0D9X.** The ringed augmentation of the total site of a hypercovering of `X` over
the slice site `C/X`: the slice site carries the restriction `O_X = O_C|_{C/X}` of a sheaf of
commutative rings on `C`, the total site carries `O = a⁻¹O_X`, and the structure map is the unit
of `a⁻¹ ⊣ a_*`. -/
abbrev hypercoveringObjectRingedAugmentation :
    SimplicialSiteSituation.RingedAugmentation
      (situation (P.toGrothendieck.over X) K) (Cat.of (Over X)) (P.toGrothendieck.over X)
      (situationAugmentation (P.toGrothendieck.over X) K) :=
  SimplicialSiteSituation.inverseImageRingedAugmentation _ _ _ _ (OC.over X)

/-- **Stacks 0DA4, the faithfulness half.** Let `C` be a site with fibre products, `X` an object
of it, `O_C` a sheaf of commutative rings on `C` and `K` a hypercovering of `X`. With
`O_X = O_C|_{C/X}` and `O = a⁻¹O_X`, the pullback `a^* : Mod(O_X) ⥤ Mod(O)` of sheaves of
modules along the augmentation of the total site of `K` over `C/X` is faithful. -/
@[stacks 0DA4 "a^* on sheaves of modules is faithful. The essential-image inclusion is \
`isCartesianModule_of_mem_essImage_over`; fullness of a^*, and essential surjectivity onto the \
cartesian O-modules making a_* a quasi-inverse, are not proved"]
theorem faithful_pullbackModules_over (hK : IsHypercovering P K) :
    (hypercoveringObjectRingedAugmentation P K
      OC).totalRingedHom.toModulesHom.pullbackModules.Faithful :=
  SimplicialSiteSituation.RingedAugmentation.faithful_pullbackModules_of_faithful_inverseImage
    (hypercoveringObjectRingedAugmentation P K OC)
    (faithful_situationTotalInverseImage_over P K hK)

/-- **Stacks 0DA4, the inclusion of the essential image in the cartesian modules.** In the
situation above, every sheaf of `O`-modules on the total site isomorphic to a pullback `a^*F` is
a cartesian `O`-module.

This is Stacks 0D7H (3) together with invariance of the cartesian condition under
isomorphism, and uses no condition on `K`. -/
@[stacks 0DA4 "the essential image of a^* consists of cartesian O-modules. Faithfulness of a^* \
is `faithful_pullbackModules_over`; fullness of a^*, and essential surjectivity onto the \
cartesian O-modules making a_* a quasi-inverse, are not proved"]
theorem isCartesianModule_of_mem_essImage_over
    {F : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
      (J := (situation (P.toGrothendieck.over X) K).totalTopology))
      (hypercoveringObjectRingedAugmentation P K OC).O)}
    (hF : (hypercoveringObjectRingedAugmentation P K
      OC).totalRingedHom.toModulesHom.pullbackModules.essImage F) :
    (situation (P.toGrothendieck.over X) K).IsModuleFiberTransitionIso
      (hypercoveringObjectRingedAugmentation P K OC).O F :=
  SimplicialSiteSituation.RingedAugmentation.isCartesianModule_of_mem_essImage
    (hypercoveringObjectRingedAugmentation P K OC) hF

/-- **Stacks 0DA4, the fullness half.** In the situation above, the pullback
`a^* : Mod(O_X) ⥤ Mod(O)` of sheaves of modules is full.

Because the structure map of `a` is the identification `O = a⁻¹O_X`, the pullback of modules is
the Stacks 03D2 inverse image of modules followed by an equivalence; fullness then descends from
Stacks 0D8K (1), full faithfulness of `a⁻¹` on sheaves of sets over `C/X`. -/
@[stacks 0DA4 "a^* on sheaves of modules is full"]
theorem full_pullbackModules_over (hK : IsHypercovering P K) :
    (hypercoveringObjectRingedAugmentation P K
      OC).totalRingedHom.toModulesHom.pullbackModules.Full :=
  SimplicialSiteSituation.RingedAugmentation.full_pullbackModules_of_full_inverseImage
    (hypercoveringObjectRingedAugmentation P K OC)
    (full_situationTotalInverseImage_over P K hK)
    (faithful_situationTotalInverseImage_over P K hK)

/-- **Stacks 0DA4, full faithfulness of `a^*` on sheaves of modules.** -/
@[stacks 0DA4 "a^* on sheaves of modules is fully faithful"]
def fullyFaithfulPullbackModulesOver (hK : IsHypercovering P K) :
    (hypercoveringObjectRingedAugmentation P K
      OC).totalRingedHom.toModulesHom.pullbackModules.FullyFaithful :=
  haveI := full_pullbackModules_over P K OC hK
  haveI := faithful_pullbackModules_over P K OC hK
  Functor.FullyFaithful.ofFullyFaithful _

/-- **Stacks 0DA4, essential surjectivity onto the cartesian `O`-modules.** In the situation
above, every cartesian sheaf of `O`-modules on the total site is a pullback `a^*M`.

The underlying sheaf of sets of a cartesian sheaf of modules is cartesian — the structure sheaf
itself being cartesian because it is `a⁻¹O_X` — hence an inverse image by Stacks 0D8K (1); and a
sheaf of modules whose underlying sheaf of sets is an inverse image is a pullback. -/
@[stacks 0DA4 "every cartesian O-module is an a^*M"]
theorem essImage_pullbackModules_over (hK : IsHypercovering P K)
    {F : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
      (J := (situation (P.toGrothendieck.over X) K).totalTopology)
      (hypercoveringObjectRingedAugmentation P K OC).O))}
    (hF : (situation (P.toGrothendieck.over X) K).IsModuleFiberTransitionIso
      (hypercoveringObjectRingedAugmentation P K OC).O F) :
    (hypercoveringObjectRingedAugmentation P K
      OC).totalRingedHom.toModulesHom.pullbackModules.essImage F :=
  SimplicialSiteSituation.RingedAugmentation.essImage_pullbackModules_of_isCartesianModule
    (hypercoveringObjectRingedAugmentation P K OC)
    (full_situationTotalInverseImage_over P K hK)
    (faithful_situationTotalInverseImage_over P K hK)
    (fun G hG => essImage_situationTotalInverseImage_of_isCartesianSheaf_over P K hK G hG) hF

/-- **Stacks 0DA4, the essential image of `a^*` is exactly the cartesian `O`-modules.** One
inclusion is `isCartesianModule_of_mem_essImage_over`, which is Stacks 0D7H (3); the other is
`essImage_pullbackModules_over`. -/
@[stacks 0DA4 "the essential image of a^* on sheaves of modules is exactly the cartesian \
O-modules"]
theorem mem_essImage_pullbackModules_iff_isCartesianModule_over (hK : IsHypercovering P K)
    (F : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
      (J := (situation (P.toGrothendieck.over X) K).totalTopology)
      (hypercoveringObjectRingedAugmentation P K OC).O))) :
    (hypercoveringObjectRingedAugmentation P K
      OC).totalRingedHom.toModulesHom.pullbackModules.essImage F ↔
      (situation (P.toGrothendieck.over X) K).IsModuleFiberTransitionIso
        (hypercoveringObjectRingedAugmentation P K OC).O F :=
  ⟨isCartesianModule_of_mem_essImage_over P K OC, essImage_pullbackModules_over P K OC hK⟩

/-- **Stacks 0DA4, `a_*` is a quasi-inverse on `Mod(O_X)`.** The unit `M ⟶ a_*a^*M` of the
adjunction of Stacks 03D7 is an isomorphism for every sheaf of `O_X`-modules: a fully faithful
left adjoint has invertible unit. -/
@[stacks 0DA4 "M = a_* a^* M on sheaves of modules"]
theorem isIso_pullbackAdjPushforwardModules_unit_over (hK : IsHypercovering P K) :
    IsIso (RingedToposHom.pullbackAdjPushforwardModules
      (hypercoveringObjectRingedAugmentation P K OC).totalRingedHom).unit :=
  have := full_pullbackModules_over P K OC hK
  have := faithful_pullbackModules_over P K OC hK
  Adjunction.unit_isIso_of_L_fully_faithful
    (RingedToposHom.pullbackAdjPushforwardModules
      (hypercoveringObjectRingedAugmentation P K OC).totalRingedHom)

/-- **Stacks 0DA4, `a_*` is a quasi-inverse on the cartesian `O`-modules.** The counit
`a^*a_*F ⟶ F` of the adjunction of Stacks 03D7 is an isomorphism at every cartesian sheaf of
`O`-modules: a fully faithful left adjoint has invertible counit exactly on its essential image,
which by `mem_essImage_pullbackModules_iff_isCartesianModule_over` is the cartesian
`O`-modules. -/
@[stacks 0DA4 "a^* a_* F = F for a cartesian O-module F"]
theorem isIso_pullbackAdjPushforwardModules_counit_app_over (hK : IsHypercovering P K)
    {F : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
      (J := (situation (P.toGrothendieck.over X) K).totalTopology)
      (hypercoveringObjectRingedAugmentation P K OC).O))}
    (hF : (situation (P.toGrothendieck.over X) K).IsModuleFiberTransitionIso
      (hypercoveringObjectRingedAugmentation P K OC).O F) :
    IsIso ((RingedToposHom.pullbackAdjPushforwardModules
      (hypercoveringObjectRingedAugmentation P K OC).totalRingedHom).counit.app F) :=
  have := full_pullbackModules_over P K OC hK
  have := faithful_pullbackModules_over P K OC hK
  ((RingedToposHom.pullbackAdjPushforwardModules
    (hypercoveringObjectRingedAugmentation P K
      OC).totalRingedHom).isIso_counit_app_iff_mem_essImage).mpr
    (essImage_pullbackModules_over P K OC hK hF)

/-- The site of the ringed topos that the total site of a hypercovering of `X` is augmented over
is the slice site `C/X`, carrying the localization of the topology of `C`. -/
theorem hypercoveringObjectRingedAugmentation_augmentationRingedTopos_J :
    (hypercoveringObjectRingedAugmentation P K OC).augmentationRingedTopos.J =
      P.toGrothendieck.over X :=
  rfl

/-- The structure sheaf of the ringed topos that the total site of a hypercovering of `X` is
augmented over is `O_X = O_C|_{C/X}`. So sheaves of modules on that ringed topos really are the
sheaves of `O_X`-modules on `C/X`. -/
theorem hypercoveringObjectRingedAugmentation_augmentationRingedTopos_O :
    (hypercoveringObjectRingedAugmentation P K OC).augmentationRingedTopos.O = OC.over X :=
  rfl

end CategoryTheory.SimplicialSemiRepresentable

end
