module

public import StacksFrontier.CategoryTheory.Sites.Hypercovering.FromSimplicialObject
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringObjectDescent
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Construction.PresheafObjects
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringEssSurjAb
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringLocallyFull

/-!
# Descent along a hypercovering by a simplicial object of the site

Let `C` be a site with fibre products given by a pretopology `J`, let `X` be an object of `C`,
let `U` be a simplicial object of `C` and let `a : U ⟶ X` be an augmentation, that is, a
morphism of simplicial objects towards the constant simplicial object on `X`. The augmentation
is a *hypercovering of `X` in `C`* when

1. `{U₀ ⟶ X}` is a covering of `C`,
2. `{U₁ ⟶ U₀ ×_X U₀}` is a covering of `C`, and
3. `{U_{n+1} ⟶ (cosk_n sk_n U)_{n+1}}` is a covering of `C` for every `n ≥ 1`,

the coskeleton in the last clause being formed in the slice category `C/X`.

Such an augmentation gives a simplicial semi-representable object `n ↦ {U_n ⟶ X}` over `X` with
exactly one summand in every degree, and the three conditions above say precisely that this
object is a hypercovering of `X` in the sense of Stacks 01G5. Attached to it are the total site
`(C/U)_total` and the augmentation morphism of topoi `a : Sh((C/U)_total) ⟶ Sh(C/X)` given by the
degree-zero localization functor `j_total`. This file shows that `a^{-1}` is fully faithful with
essential image the cartesian sheaves, for sheaves of sets and for sheaves of abelian groups, with
`a_*` as quasi-inverse.

## Main definitions

* `Stacks.CategoryTheory.Hypercovering.IsHypercoveringAugmentation`: the three conditions above.
* `CategoryTheory.SimplicialSemiRepresentable.totalSituation` and
  `CategoryTheory.SimplicialSemiRepresentable.augmentationMorphismOfTopoi`: the total site
  `(C/U)_total` and the augmentation morphism of topoi towards `Sh(C/X)`.
* `CategoryTheory.SimplicialSemiRepresentable.abelianInverseImage`: the inverse image
  `a^{-1} : Ab(C/X) ⥤ Ab((C/U)_total)`.
* `CategoryTheory.SimplicialSemiRepresentable.fullyFaithfulInverseImageAugmented'` and
  `CategoryTheory.SimplicialSemiRepresentable.fullyFaithfulAbelianInverseImageAugmented'`: `a^{-1}`
  is fully faithful on sheaves of sets and on sheaves of abelian groups.

## Main results

* `Stacks.CategoryTheory.Hypercovering.isHypercoveringAugmentation_iff_isHypercovering`: a
  hypercovering augmentation is exactly one whose associated simplicial semi-representable
  object over `X` is a hypercovering of `X`.
* `CategoryTheory.SimplicialSemiRepresentable.isIso_unit_augmented'` and
  `CategoryTheory.SimplicialSemiRepresentable.isIso_abelianUnit_augmented'`: the unit
  `E ⟶ a_* a^{-1} E` is an isomorphism.
* `CategoryTheory.SimplicialSemiRepresentable.mem_essImage_iff_isCartesianSheaf_augmented'` and
  `CategoryTheory.SimplicialSemiRepresentable.mem_essImage_iff_isCartesianAbSheaf_augmented'`: the
  essential image of `a^{-1}` is exactly the cartesian sheaves.
* `CategoryTheory.SimplicialSemiRepresentable.isIso_counit_app_augmented'` and
  `CategoryTheory.SimplicialSemiRepresentable.isIso_abelianCounit_app_augmented'`: the counit
  `a^{-1} a_* F ⟶ F` is an isomorphism at every cartesian sheaf `F`.

## References

* [Stacks Project, Tag 0DA8](https://stacks.math.columbia.edu/tag/0DA8)
* [Stacks Project, Tag 09X8](https://stacks.math.columbia.edu/tag/09X8)
* [Stacks Project, Tag 0D8K](https://stacks.math.columbia.edu/tag/0D8K)
* [Stacks Project, Tag 0D8E](https://stacks.math.columbia.edu/tag/0D8E)
* [Stacks Project, Tag 0GM9](https://stacks.math.columbia.edu/tag/0GM9)
* [Stacks Project, Tag 01G5](https://stacks.math.columbia.edu/tag/01G5)
* [Stacks Project, Tag 07TF](https://stacks.math.columbia.edu/tag/07TF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe w v u

namespace Stacks.CategoryTheory.Hypercovering

/-! ### Hypercovering augmentations -/

section Augmentation

variable {C : Type u} [Category.{v} C] [HasPullbacks C] {X : C}

/-- An augmentation `a : U ⟶ X` of a simplicial object `U` of the site given by
the pretopology `J` is a *hypercovering of `X` in `C`* when `{U₀ ⟶ X}` is a covering, the
canonical morphism `U₁ ⟶ U₀ ×_X U₀` generates a covering, and the canonical morphism
`U_{n+1} ⟶ (cosk_n sk_n U)_{n+1}` generates a covering for every `n ≥ 1`, the coskeleton being
formed in the slice category `C/X`. -/
@[stacks 09X8 "the definition of the section: an augmentation of a simplicial object of the site \
is a hypercovering of `X` in `C` when the three displayed families are coverings"]
def IsHypercoveringAugmentation (J : Pretopology C) (U : SimplicialObject C)
    (a : U ⟶ (SimplicialObject.const C).obj X) : Prop :=
  Presieve.singleton (a.app (op ⦋0⦌)) ∈ J X ∧
    Presieve.singleton (oneSimplexToFiberProduct U a) ∈
      J (pullback (a.app (op ⦋0⦌)) (a.app (op ⦋0⦌))) ∧
    ∀ n : ℕ, 1 ≤ n → Presieve.singleton (matchingMap U a n) ∈
      J ((((SimplicialObject.cosk n).obj (Over.lift U a)).obj (op ⦋n + 1⦌)).left)

variable (J : Pretopology C) (U : SimplicialObject C)
  (a : U ⟶ (SimplicialObject.const C).obj X)

/-- An augmentation is a hypercovering of `X` in `C` exactly when the simplicial
semi-representable object `n ↦ {U_n ⟶ X}` over `X` that it determines is a hypercovering of `X`
in the sense of Stacks 01G5. -/
theorem isHypercoveringAugmentation_iff_isHypercovering :
    IsHypercoveringAugmentation J U a ↔
      IsHypercovering J (associatedSimplicialObject.{w} U a) :=
  (isHypercovering_associatedSimplicialObject_iff U a J).symm

/-- A hypercovering augmentation determines a hypercovering of `X` in the sense of
Stacks 01G5. -/
theorem IsHypercoveringAugmentation.isHypercovering
    (h : IsHypercoveringAugmentation J U a) :
    IsHypercovering J (associatedSimplicialObject.{w} U a) :=
  (isHypercoveringAugmentation_iff_isHypercovering J U a).mp h

/-- The degree-zero clause of a hypercovering augmentation: the unique morphism from
`{U₀ ⟶ X}` to the terminal semi-representable object over `X` is covering. -/
theorem IsHypercoveringAugmentation.isCoveringOver_terminal
    (h : IsHypercoveringAugmentation J U a) :
    IsCoveringOver J
      (terminal.from ((associatedSimplicialObject.{w} U a).obj (op ⦋0⦌))) :=
  (h.isHypercovering J U a).1

end Augmentation

end Stacks.CategoryTheory.Hypercovering

namespace CategoryTheory.SimplicialSemiRepresentable

open Stacks.CategoryTheory.Hypercovering

variable {C : Type u} [SmallCategory C] [HasPullbacks C] (P : Pretopology C) {X : C}
  (U : SimplicialObject C) (a : U ⟶ (SimplicialObject.const C).obj X)

/-! ### The total site and the augmentation morphism of topoi -/

/-- The total site `(C/U)_total` of Stacks 09X8: the simplicial-site situation attached, over the
localized site `C/X`, to the simplicial semi-representable object `n ↦ {U_n ⟶ X}`. -/
abbrev totalSituation : SimplicialSiteSituation.{u} :=
  situation (P.toGrothendieck.over X) (associatedSimplicialObject.{u} U a)

/-- The augmentation morphism of topoi `a : Sh((C/U)_total) ⟶ Sh(C/X)` of Stacks 09X8, given by
the degree-zero localization functor `j_total`. -/
abbrev augmentationMorphismOfTopoi :
    MorphismOfTopoi (Sheaf (totalSituation P U a).totalTopology (Type u))
      (Sheaf (P.toGrothendieck.over X) (Type u)) :=
  totalLocalizationMorphism (P.toGrothendieck.over X) (associatedSimplicialObject.{u} U a)

/-- The inverse image `a^{-1} : Ab(C/X) ⥤ Ab((C/U)_total)` on sheaves of abelian groups, as in
Stacks 09WM (2): restriction along `j_total`. -/
abbrev abelianInverseImage :
    Sheaf (P.toGrothendieck.over X) Ab.{u} ⥤
      Sheaf (totalSituation P U a).totalTopology Ab.{u} :=
  (totalForget (associatedSimplicialObject.{u} U a)).sheafPushforwardContinuous Ab.{u}
    ((totalSituation P U a).totalTopology) (P.toGrothendieck.over X)

/-- The adjunction `a^{-1} ⊣ a_*` on sheaves of abelian groups. -/
abbrev abelianAdjunction :
    abelianInverseImage P U a ⊣
      (totalForget (associatedSimplicialObject.{u} U a)).sheafPushforwardCocontinuous Ab.{u}
        ((totalSituation P U a).totalTopology) (P.toGrothendieck.over X) :=
  abelianTotalAdjunction (P.toGrothendieck.over X) (associatedSimplicialObject.{u} U a)

/-- The localization functor `j_total : (C/U)_total ⥤ C/X` of the total site of a hypercovering
augmentation is cover dense. -/
theorem isCoverDense_totalForget_augmented (h : IsHypercoveringAugmentation P U a) :
    (totalForget (associatedSimplicialObject.{u} U a)).IsCoverDense (P.toGrothendieck.over X) :=
  isCoverDense_totalForget_over P (associatedSimplicialObject.{u} U a)
    (h.isCoveringOver_terminal P U a)

/-! ### Local fullness and essential surjectivity over `C/X` -/

/-- The localization functor `j_total : (C/U)_total ⥤ C/X` of the total site of a hypercovering
augmentation is locally full for the topology of `C/X`. -/
theorem isLocallyFull_totalForget_augmented (h : IsHypercoveringAugmentation P U a) :
    (totalForget (associatedSimplicialObject.{u} U a)).IsLocallyFull
      (P.toGrothendieck.over X) :=
  isLocallyFull_totalForget_over P (associatedSimplicialObject.{u} U a)
    (h.isHypercovering P U a)

/-- A property of a topology and a simplicial object over `C/X` that holds for all
hypercoverings of the terminal object of `C/X` holds for the topology of `C/X` and the simplicial
object attached to a hypercovering augmentation. -/
private theorem of_forall_hypercoveringOfTerminal (h : IsHypercoveringAugmentation P U a)
    (Φ : GrothendieckTopology (Over X) → SimplicialObject (FormalCoproduct.{u} (Over X)) → Prop)
    (hΦ : ∀ [HasFiniteLimits (Over X)]
      (H : HypercoveringOfTerminal.{u, u, u} (P.toGrothendieck.over X).toPretopology),
      Φ (P.toGrothendieck.over X).toPretopology.toGrothendieck H.toSimplicialObject) :
    Φ (P.toGrothendieck.over X) (associatedSimplicialObject.{u} U a) := by
  have : HasFiniteLimits (Over X) := hasFiniteLimits_of_hasTerminal_and_pullbacks
  obtain ⟨H, hH⟩ := exists_hypercoveringOfTerminal_over_of_isHypercovering P
    (associatedSimplicialObject.{u} U a) (h.isHypercovering P U a)
  rw [← (Pretopology.gi (C := Over X)).l_u_eq (P.toGrothendieck.over X), ← hH]
  exact hΦ H

/-- Every cartesian sheaf of sets on the total site `(C/U)_total` of a hypercovering
augmentation is isomorphic to an inverse image along the augmentation. -/
theorem essImage_of_isCartesianSheaf_augmented (h : IsHypercoveringAugmentation P U a) :
    ∀ F : Sheaf (totalSituation P U a).totalTopology (Type u),
      (totalSituation P U a).IsCartesianSheaf F →
        (augmentationMorphismOfTopoi P U a).inverseImage.essImage F :=
  of_forall_hypercoveringOfTerminal P U a h
    (fun J K ↦ ∀ F : Sheaf (situation J K).totalTopology (Type u),
      (situation J K).IsCartesianSheaf F → (totalLocalizationMorphism J K).inverseImage.essImage F)
    fun H F hF ↦ essImage_of_isCartesianSheaf _ H F hF

/-- Every cartesian sheaf of abelian groups on the total site `(C/U)_total` of a
hypercovering augmentation is isomorphic to an inverse image along the augmentation. -/
theorem essImage_of_isCartesianAbSheaf_augmented (h : IsHypercoveringAugmentation P U a) :
    ∀ F : Sheaf (totalSituation P U a).totalTopology Ab.{u},
      (totalSituation P U a).IsCartesianAbSheaf F → (abelianInverseImage P U a).essImage F :=
  of_forall_hypercoveringOfTerminal P U a h
    (fun J K ↦ ∀ F : Sheaf (situation J K).totalTopology Ab.{u},
      (situation J K).IsCartesianAbSheaf F →
        ((totalForget K).sheafPushforwardContinuous Ab.{u}
          (situation J K).totalTopology J).essImage F)
    fun H F hF ↦ essImage_of_isCartesianAbSheaf _ H F hF

/-! ### Part (1): sheaves of sets -/

/-- For a hypercovering `a : U ⟶ X` of `X` in `C` the inverse image
`a^{-1} : Sh(C/X) ⥤ Sh((C/U)_total)` of the augmentation is faithful. -/
@[stacks 0DA8 "part (1): a^{-1} on sheaves of sets is faithful"]
theorem faithful_inverseImage_augmented (h : IsHypercoveringAugmentation P U a) :
    (augmentationMorphismOfTopoi P U a).inverseImage.Faithful :=
  faithful_inverseImage_of_isCoverDense (P.toGrothendieck.over X)
    (associatedSimplicialObject.{u} U a) (isCoverDense_totalForget_augmented P U a h)

/-- For a hypercovering `a : U ⟶ X` of `X` in `C` such that `j_total` is locally full for
the topology of `C/X`, the inverse image `a^{-1} : Sh(C/X) ⥤ Sh((C/U)_total)` is full. -/
@[stacks 0DA8 "part (1): a^{-1} on sheaves of sets is full, carrying local fullness of j_total"]
theorem full_inverseImage_augmented (h : IsHypercoveringAugmentation P U a)
    (hlf : (totalForget (associatedSimplicialObject.{u} U a)).IsLocallyFull
      (P.toGrothendieck.over X)) :
    (augmentationMorphismOfTopoi P U a).inverseImage.Full :=
  full_inverseImage_of_isLocallyFull (P.toGrothendieck.over X)
    (associatedSimplicialObject.{u} U a) (isCoverDense_totalForget_augmented P U a h) hlf

/-- For a hypercovering `a : U ⟶ X` of `X` in `C` the inverse image
`a^{-1} : Sh(C/X) ⥤ Sh((C/U)_total)` is full. -/
@[stacks 0DA8 "part (1): a^{-1} on sheaves of sets is full"]
theorem full_inverseImage_augmented' (h : IsHypercoveringAugmentation P U a) :
    (augmentationMorphismOfTopoi P U a).inverseImage.Full :=
  full_inverseImage_augmented P U a h (isLocallyFull_totalForget_augmented P U a h)

/-- For a hypercovering `a : U ⟶ X` of `X` in `C` such that `j_total` is locally full,
the inverse image `a^{-1} : Sh(C/X) ⥤ Sh((C/U)_total)` is fully faithful. -/
@[stacks 0DA8 "part (1): a^{-1} on sheaves of sets is fully faithful, carrying local fullness"]
def fullyFaithfulInverseImageAugmented (h : IsHypercoveringAugmentation P U a)
    (hlf : (totalForget (associatedSimplicialObject.{u} U a)).IsLocallyFull
      (P.toGrothendieck.over X)) :
    (augmentationMorphismOfTopoi P U a).inverseImage.FullyFaithful :=
  fullyFaithfulInverseImage (P.toGrothendieck.over X) (associatedSimplicialObject.{u} U a)
    (isCoverDense_totalForget_augmented P U a h) hlf

/-- For a hypercovering `a : U ⟶ X` of `X` in `C` the inverse image
`a^{-1} : Sh(C/X) ⥤ Sh((C/U)_total)` is fully faithful. -/
@[stacks 0DA8 "part (1): a^{-1} on sheaves of sets is fully faithful"]
def fullyFaithfulInverseImageAugmented' (h : IsHypercoveringAugmentation P U a) :
    (augmentationMorphismOfTopoi P U a).inverseImage.FullyFaithful :=
  fullyFaithfulInverseImage (P.toGrothendieck.over X) (associatedSimplicialObject.{u} U a)
    (isCoverDense_totalForget_augmented P U a h)
    (isLocallyFull_totalForget_augmented P U a h)

/-- For a hypercovering augmentation such that `j_total` is locally full, the canonical map
`E ⟶ a_* a^{-1} E` is an isomorphism for every sheaf of sets `E` on `C/X`. -/
@[stacks 0DA8 "part (1): E = a_* a^{-1} E on sheaves of sets, carrying local fullness"]
theorem isIso_unit_augmented (h : IsHypercoveringAugmentation P U a)
    (hlf : (totalForget (associatedSimplicialObject.{u} U a)).IsLocallyFull
      (P.toGrothendieck.over X)) :
    IsIso (augmentationMorphismOfTopoi P U a).adj.unit :=
  isIso_unit_of_isLocallyFull (P.toGrothendieck.over X)
    (associatedSimplicialObject.{u} U a) (isCoverDense_totalForget_augmented P U a h) hlf

/-- For a hypercovering augmentation, the canonical map `E ⟶ a_* a^{-1} E` is an
isomorphism for every sheaf of sets `E` on `C/X`. -/
@[stacks 0DA8 "part (1): E = a_* a^{-1} E on sheaves of sets"]
theorem isIso_unit_augmented' (h : IsHypercoveringAugmentation P U a) :
    IsIso (augmentationMorphismOfTopoi P U a).adj.unit :=
  isIso_unit_augmented P U a h (isLocallyFull_totalForget_augmented P U a h)

/-- Every sheaf of sets on `(C/U)_total` isomorphic to an inverse image along the
augmentation is cartesian. -/
@[stacks 0DA8 "part (1): the essential image of a^{-1} consists of cartesian sheaves of sets"]
theorem isCartesianSheaf_of_mem_essImage_augmented
    {F : Sheaf (totalSituation P U a).totalTopology (Type u)}
    (hF : (augmentationMorphismOfTopoi P U a).inverseImage.essImage F) :
    (totalSituation P U a).IsCartesianSheaf F :=
  isCartesianSheaf_of_mem_essImage (P.toGrothendieck.over X)
    (associatedSimplicialObject.{u} U a) hF

/-- If every cartesian sheaf of sets on `(C/U)_total` lies in the essential image of
`a^{-1}`, then the essential image of `a^{-1}` is exactly the cartesian sheaves of sets. -/
@[stacks 0DA8 "part (1): essential image = cartesian sheaves of sets, carrying surjectivity"]
theorem mem_essImage_iff_isCartesianSheaf_augmented
    (hsurj : ∀ G : Sheaf (totalSituation P U a).totalTopology (Type u),
      (totalSituation P U a).IsCartesianSheaf G →
        (augmentationMorphismOfTopoi P U a).inverseImage.essImage G)
    (F : Sheaf (totalSituation P U a).totalTopology (Type u)) :
    (augmentationMorphismOfTopoi P U a).inverseImage.essImage F ↔
      (totalSituation P U a).IsCartesianSheaf F :=
  ⟨fun hF ↦ isCartesianSheaf_of_mem_essImage_augmented P U a hF, hsurj F⟩

/-- For a hypercovering augmentation, the essential image of
`a^{-1} : Sh(C/X) ⥤ Sh((C/U)_total)` is exactly the cartesian sheaves of sets. -/
@[stacks 0DA8 "part (1): the essential image of a^{-1} is exactly the cartesian sheaves of sets"]
theorem mem_essImage_iff_isCartesianSheaf_augmented' (h : IsHypercoveringAugmentation P U a)
    (F : Sheaf (totalSituation P U a).totalTopology (Type u)) :
    (augmentationMorphismOfTopoi P U a).inverseImage.essImage F ↔
      (totalSituation P U a).IsCartesianSheaf F :=
  ⟨fun hF ↦ isCartesianSheaf_of_mem_essImage_augmented P U a hF,
    essImage_of_isCartesianSheaf_augmented P U a h F⟩

/-- For a hypercovering augmentation such that `j_total` is locally full and every cartesian
sheaf of sets on `(C/U)_total` lies in the essential image of `a^{-1}`, the canonical map
`a^{-1} a_* F ⟶ F` is an isomorphism for every cartesian sheaf of sets `F` on `(C/U)_total`. -/
@[stacks 0DA8 "part (1): a^{-1} a_* F = F for cartesian F, carrying the two clauses of 0D8E"]
theorem isIso_counit_app_augmented (h : IsHypercoveringAugmentation P U a)
    (hlf : (totalForget (associatedSimplicialObject.{u} U a)).IsLocallyFull
      (P.toGrothendieck.over X))
    (hsurj : ∀ G : Sheaf (totalSituation P U a).totalTopology (Type u),
      (totalSituation P U a).IsCartesianSheaf G →
        (augmentationMorphismOfTopoi P U a).inverseImage.essImage G)
    {F : Sheaf (totalSituation P U a).totalTopology (Type u)}
    (hF : (totalSituation P U a).IsCartesianSheaf F) :
    IsIso ((augmentationMorphismOfTopoi P U a).adj.counit.app F) :=
  (isIso_counit_app_iff_mem_essImage_of_isLocallyFull (P.toGrothendieck.over X)
    (associatedSimplicialObject.{u} U a) (isCoverDense_totalForget_augmented P U a h) hlf
    F).mpr (hsurj F hF)

/-- For a hypercovering augmentation, the canonical map `a^{-1} a_* F ⟶ F` is an
isomorphism for every cartesian sheaf of sets `F` on `(C/U)_total`. -/
@[stacks 0DA8 "part (1): a^{-1} a_* F = F for a cartesian sheaf of sets F"]
theorem isIso_counit_app_augmented' (h : IsHypercoveringAugmentation P U a)
    {F : Sheaf (totalSituation P U a).totalTopology (Type u)}
    (hF : (totalSituation P U a).IsCartesianSheaf F) :
    IsIso ((augmentationMorphismOfTopoi P U a).adj.counit.app F) :=
  isIso_counit_app_augmented P U a h (isLocallyFull_totalForget_augmented P U a h)
    (essImage_of_isCartesianSheaf_augmented P U a h) hF

/-! ### Part (2): sheaves of abelian groups -/

/-- For a hypercovering `a : U ⟶ X` of `X` in `C` the inverse image
`a^{-1} : Ab(C/X) ⥤ Ab((C/U)_total)` of the augmentation is faithful. -/
@[stacks 0DA8 "part (2): a^{-1} on abelian sheaves is faithful"]
theorem faithful_abelianInverseImage_augmented (h : IsHypercoveringAugmentation P U a) :
    (abelianInverseImage P U a).Faithful :=
  faithful_abelianInverseImage_of_isCoverDense (P.toGrothendieck.over X)
    (associatedSimplicialObject.{u} U a) (isCoverDense_totalForget_augmented P U a h)

/-- For a hypercovering `a : U ⟶ X` of `X` in `C` such that `j_total` is locally full,
the inverse image `a^{-1} : Ab(C/X) ⥤ Ab((C/U)_total)` is full. -/
@[stacks 0DA8 "part (2): a^{-1} on abelian sheaves is full, carrying local fullness of j_total"]
theorem full_abelianInverseImage_augmented (h : IsHypercoveringAugmentation P U a)
    (hlf : (totalForget (associatedSimplicialObject.{u} U a)).IsLocallyFull
      (P.toGrothendieck.over X)) :
    (abelianInverseImage P U a).Full :=
  full_abelianInverseImage_of_isLocallyFull (P.toGrothendieck.over X)
    (associatedSimplicialObject.{u} U a) (isCoverDense_totalForget_augmented P U a h) hlf

/-- For a hypercovering `a : U ⟶ X` of `X` in `C` the inverse image
`a^{-1} : Ab(C/X) ⥤ Ab((C/U)_total)` is full. -/
@[stacks 0DA8 "part (2): a^{-1} on abelian sheaves is full"]
theorem full_abelianInverseImage_augmented' (h : IsHypercoveringAugmentation P U a) :
    (abelianInverseImage P U a).Full :=
  full_abelianInverseImage_augmented P U a h (isLocallyFull_totalForget_augmented P U a h)

/-- For a hypercovering `a : U ⟶ X` of `X` in `C` such that `j_total` is locally full,
the inverse image `a^{-1} : Ab(C/X) ⥤ Ab((C/U)_total)` is fully faithful. -/
@[stacks 0DA8 "part (2): a^{-1} on abelian sheaves is fully faithful, carrying local fullness"]
def fullyFaithfulAbelianInverseImageAugmented (h : IsHypercoveringAugmentation P U a)
    (hlf : (totalForget (associatedSimplicialObject.{u} U a)).IsLocallyFull
      (P.toGrothendieck.over X)) :
    (abelianInverseImage P U a).FullyFaithful :=
  fullyFaithfulAbelianInverseImage (P.toGrothendieck.over X)
    (associatedSimplicialObject.{u} U a) (isCoverDense_totalForget_augmented P U a h) hlf

/-- For a hypercovering `a : U ⟶ X` of `X` in `C` the inverse image
`a^{-1} : Ab(C/X) ⥤ Ab((C/U)_total)` is fully faithful. -/
@[stacks 0DA8 "part (2): a^{-1} on abelian sheaves is fully faithful"]
def fullyFaithfulAbelianInverseImageAugmented' (h : IsHypercoveringAugmentation P U a) :
    (abelianInverseImage P U a).FullyFaithful :=
  fullyFaithfulAbelianInverseImage (P.toGrothendieck.over X)
    (associatedSimplicialObject.{u} U a) (isCoverDense_totalForget_augmented P U a h)
    (isLocallyFull_totalForget_augmented P U a h)

/-- For a hypercovering augmentation such that `j_total` is locally full, the canonical map
`E ⟶ a_* a^{-1} E` is an isomorphism for every sheaf of abelian groups `E` on `C/X`. -/
@[stacks 0DA8 "part (2): E = a_* a^{-1} E on abelian sheaves, carrying local fullness"]
theorem isIso_abelianUnit_augmented (h : IsHypercoveringAugmentation P U a)
    (hlf : (totalForget (associatedSimplicialObject.{u} U a)).IsLocallyFull
      (P.toGrothendieck.over X)) :
    IsIso (abelianAdjunction P U a).unit :=
  isIso_abelianUnit_of_isLocallyFull (P.toGrothendieck.over X)
    (associatedSimplicialObject.{u} U a) (isCoverDense_totalForget_augmented P U a h) hlf

/-- For a hypercovering augmentation, the canonical map `E ⟶ a_* a^{-1} E` is an
isomorphism for every sheaf of abelian groups `E` on `C/X`. -/
@[stacks 0DA8 "part (2): E = a_* a^{-1} E on abelian sheaves"]
theorem isIso_abelianUnit_augmented' (h : IsHypercoveringAugmentation P U a) :
    IsIso (abelianAdjunction P U a).unit :=
  isIso_abelianUnit_augmented P U a h (isLocallyFull_totalForget_augmented P U a h)

/-- Every sheaf of abelian groups on `(C/U)_total` isomorphic to an inverse image along the
augmentation is cartesian. -/
@[stacks 0DA8 "part (2): the essential image of a^{-1} consists of cartesian abelian sheaves"]
theorem isCartesianAbSheaf_of_mem_essImage_augmented
    {F : Sheaf (totalSituation P U a).totalTopology Ab.{u}}
    (hF : (abelianInverseImage P U a).essImage F) :
    (totalSituation P U a).IsCartesianAbSheaf F :=
  isCartesianAbSheaf_of_mem_essImage (P.toGrothendieck.over X)
    (associatedSimplicialObject.{u} U a) hF

/-- If every cartesian sheaf of abelian groups on `(C/U)_total` lies in the essential image
of `a^{-1}`, then the essential image of `a^{-1}` is exactly the cartesian abelian sheaves. -/
@[stacks 0DA8 "part (2): essential image = cartesian abelian sheaves, carrying surjectivity"]
theorem mem_essImage_iff_isCartesianAbSheaf_augmented
    (hsurj : ∀ G : Sheaf (totalSituation P U a).totalTopology Ab.{u},
      (totalSituation P U a).IsCartesianAbSheaf G → (abelianInverseImage P U a).essImage G)
    (F : Sheaf (totalSituation P U a).totalTopology Ab.{u}) :
    (abelianInverseImage P U a).essImage F ↔
      (totalSituation P U a).IsCartesianAbSheaf F :=
  ⟨fun hF ↦ isCartesianAbSheaf_of_mem_essImage_augmented P U a hF, hsurj F⟩

/-- For a hypercovering augmentation, the essential image of
`a^{-1} : Ab(C/X) ⥤ Ab((C/U)_total)` is exactly the cartesian abelian sheaves. -/
@[stacks 0DA8 "part (2): the essential image of a^{-1} is exactly the cartesian abelian sheaves"]
theorem mem_essImage_iff_isCartesianAbSheaf_augmented' (h : IsHypercoveringAugmentation P U a)
    (F : Sheaf (totalSituation P U a).totalTopology Ab.{u}) :
    (abelianInverseImage P U a).essImage F ↔
      (totalSituation P U a).IsCartesianAbSheaf F :=
  ⟨fun hF ↦ isCartesianAbSheaf_of_mem_essImage_augmented P U a hF,
    essImage_of_isCartesianAbSheaf_augmented P U a h F⟩

/-- For a hypercovering augmentation such that `j_total` is locally full and every cartesian
sheaf of abelian groups on `(C/U)_total` lies in the essential image of `a^{-1}`, the canonical
map `a^{-1} a_* F ⟶ F` is an isomorphism for every cartesian sheaf of abelian groups `F`. -/
@[stacks 0DA8 "part (2): a^{-1} a_* F = F for cartesian F, carrying the two clauses of 0D8E"]
theorem isIso_abelianCounit_app_augmented (h : IsHypercoveringAugmentation P U a)
    (hlf : (totalForget (associatedSimplicialObject.{u} U a)).IsLocallyFull
      (P.toGrothendieck.over X))
    (hsurj : ∀ G : Sheaf (totalSituation P U a).totalTopology Ab.{u},
      (totalSituation P U a).IsCartesianAbSheaf G → (abelianInverseImage P U a).essImage G)
    {F : Sheaf (totalSituation P U a).totalTopology Ab.{u}}
    (hF : (totalSituation P U a).IsCartesianAbSheaf F) :
    IsIso ((abelianAdjunction P U a).counit.app F) :=
  (isIso_abelianCounit_app_iff_mem_essImage_of_isLocallyFull (P.toGrothendieck.over X)
    (associatedSimplicialObject.{u} U a) (isCoverDense_totalForget_augmented P U a h) hlf
    F).mpr (hsurj F hF)

/-- For a hypercovering augmentation, the canonical map `a^{-1} a_* F ⟶ F` is an
isomorphism for every cartesian sheaf of abelian groups `F` on `(C/U)_total`. -/
@[stacks 0DA8 "part (2): a^{-1} a_* F = F for a cartesian abelian sheaf F"]
theorem isIso_abelianCounit_app_augmented' (h : IsHypercoveringAugmentation P U a)
    {F : Sheaf (totalSituation P U a).totalTopology Ab.{u}}
    (hF : (totalSituation P U a).IsCartesianAbSheaf F) :
    IsIso ((abelianAdjunction P U a).counit.app F) :=
  isIso_abelianCounit_app_augmented P U a h (isLocallyFull_totalForget_augmented P U a h)
    (essImage_of_isCartesianAbSheaf_augmented P U a h) hF

end CategoryTheory.SimplicialSemiRepresentable

end
