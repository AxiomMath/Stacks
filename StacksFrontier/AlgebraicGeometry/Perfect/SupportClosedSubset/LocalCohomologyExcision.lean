module

public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.SupportedSectionsRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ClosedSubsetPushforward
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.LocalCohomologySheaves
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CompositeRightDerivedFunctors
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.LocalizationIsomorphisms
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen
public import StacksFrontier.Topology.Sheaves.Modules.SupportedSectionsOpenImmersion
import StacksCore.Tactic.StacksAttribute

/-!
# Excision for sheaf local cohomology

Let `X` be a scheme, let `T ⊆ X` be a subset and let `U ⊆ X` be an open subscheme.  Sheaf local
cohomology with supports in `T` is local on `X`:

`ℋ ⁿ_T(ℱ)|_U ≅ ℋ ⁿ_{U ∩ T}(ℱ|_U)`,

naturally in the `𝒪_X`-module `ℱ`.  That is `localCohomologyRestrictNatIso`, the main result.
No closedness assumption on `T` is needed.

Both sides are read on the ambient scheme, as the direct image along the inclusion of the
support: the functor `ℋ ⁿ_T` appearing here is `localCohomologyOn`, the `n`-th right derived
functor of the *subsheaf of sections supported on `T`*, an endofunctor of `Mod(𝒪_X)`.  This is
the shape a Gysin-type construction consumes — the local cohomology sheaf of [Stacks, Tag 0G6N]
lives on the closed subset, and only its direct image is a sheaf on `X` — and it is also what
makes the statement sayable: the two sides of an excision statement for the sheaves on the
supports would live on two different presentations of `U ∩ T` as a space, whereas here both
sides are sheaves of modules on `U`.  No faithfulness is lost, the direct image along the
inclusion of the support being fully faithful ([Stacks, Tag 08KS],
`Stacks.SheafOfModules.SupportedSections.fullyFaithfulModulePushforwardClosedSubset`), so a
comparison of the direct images is a comparison of the local cohomology sheaves themselves; and
for closed `T` the identification of `localCohomologyOn` with that direct image is
`localCohomologyOnIso`.

## Main definitions and results

* `supportedSectionsOn` and `localCohomologyOn`: the subsheaf `H_T` of sections supported on `T`
  and its right derived functors `ℋ ⁿ_T`, as endofunctors of `X.Modules`.
* `restrictFunctor_eq_jStar`: restriction of modules along the inclusion of an open subscheme
  *is* the restriction `j^*` of `ExtensionByZeroModules`.  This is an equality of functors, not
  merely an isomorphism, and it is what carries the homological properties of `j^*` — in
  particular that it preserves injective objects — into the scheme vocabulary.
* `restrictFunctor_preservesInjectiveObjects` ([Stacks, Tag 01E1]) and
  `restrictFunctor_preservesHomology`: restriction to an open subscheme preserves injective
  objects and is exact.
* `supportedSectionsRestrictNatIso`: **excision in degree zero**, as a natural isomorphism
  `H_T(-)|_U ≅ H_{U ∩ T}((-)|_U)` of functors `X.Modules ⥤ U.Modules`.  The underlying
  comparison of subsheaves is
  `Stacks.Perfect.SupportedSectionsRestriction.exists_supportedSectionsRestrictIso`; what is
  added here is that it is natural, which holds because both subsheaves are subsheaves of
  `ℱ|_U`.
* `localCohomologyRestrictNatIso`: **excision for sheaf local cohomology in every degree.**
* `localCohomologyRestrict`, `localCohomologyRestrictInv` and the round-trip identities
  `localCohomologyRestrictInv_app_localCohomologyRestrict_app`,
  `localCohomologyRestrict_app_localCohomologyRestrictInv_app`: the transport of a local
  cohomology class between `ℋ ⁿ_T(ℱ)` over an open of `U` and `ℋ ⁿ_{U ∩ T}(ℱ|_U)` over that
  open, on sections, which is what a consumer working on a chart uses.
* `restrict_sections_eq`, `chartOpen`, `ι_image_chartOpen` and `restrict_sections_eq_of_le`: the
  dictionary between opens of `U` and opens of `X` contained in `U`, in which the left-hand side
  of the comparison is literally the sections of `ℋ ⁿ_T(ℱ)` over an open of `X`.
* `localCohomologyOnIso`: for closed `T`, `localCohomologyOn` *is* the direct image of the local
  cohomology sheaf `Stacks.Cohomology.SupportedComplexes.localCohomologySheafFunctor` of
  [Stacks, Tag 0G6N].  So the comparison above is excision for the local cohomology sheaves
  themselves, not for some functor that merely agrees with them in degree zero.

## Implementation notes

The proof is the standard one, through two comparisons of derived functors:

* `Stacks.Cohomology.ModuleComparison.rightDerivedCompIso` moves the restriction *out* of a right
  derived functor, using only that restriction is exact: deriving `H_T` and then restricting is
  deriving the composite `H_T(-)|_U`.
* `Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso` ([Stacks, Tag 015Z]) moves the
  restriction *in*, using that restriction is exact and preserves injective objects: deriving
  `H_{U ∩ T}((-)|_U)` is restricting and then deriving `H_{U ∩ T}`.

Composed along the degree-zero comparison `supportedSectionsRestrictNatIso`, these give the
result.  The mathematical content is therefore exactly the degree-zero statement together with
the fact that restriction to an open subscheme preserves injective objects, i.e. that the
restriction of an injective resolution is again one.

**Why `restrictFunctor_eq_jStar` is an equality.** The two restrictions differ only in the
change-of-rings morphism: `ExtensionByZeroModules.jStar` uses the identity of the restricted
sheaf of rings, while `AlgebraicGeometry.Scheme.Modules.restrictFunctor` uses the inverse of
`AlgebraicGeometry.Scheme.Hom.appIso`, which for the inclusion of an open subscheme is the
identity by `AlgebraicGeometry.Scheme.Opens.ι_appIso`.  The source and target categories are
definitionally equal, so the two functors can be compared at all, and recording an equality
rather than an isomorphism means the instances transport by rewriting.

**Two names for one category.**  `AlgebraicGeometry.Scheme.Modules` is a `def` with its own
`Category` instance, so `X.Modules` and `SheafOfModules (structureSheafRing X.toRingedSpace)`
are definitionally equal but carry different *syntactic* category and preadditive instances; a
statement mixing them has a different composition in each half, and instance search then finds
neither `Additive` instance.  This is why `supportedSectionsOn` exists: it is
`Stacks.SheafOfModules.SupportedSections.supportedSectionsFunctor` with its type ascribed at the
`X.Modules` spelling, which is the spelling of `restrictFunctor` and of a consumer working on a
scheme, and `supportedSectionsOn_additive` is the `Additive` instance at that spelling.
Everything below is stated in that one spelling.

## References

* [Stacks Project, Tag 0G6N](https://stacks.math.columbia.edu/tag/0G6N)
* [Stacks Project, Tag 01E1](https://stacks.math.columbia.edu/tag/01E1)
* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules.SupportedSections
open scoped AlgebraicGeometry

universe u

namespace Stacks.Perfect.LocalCohomologyExcision

attribute [local implicit_reducible] CategoryTheory.Functor.sheafPushforwardContinuous

/-! ### Sections with support and local cohomology on a scheme -/

/-- **`H_T`, the subsheaf of sections supported on `T`**, as an endofunctor of `X.Modules`.

This is `Stacks.SheafOfModules.SupportedSections.supportedSectionsFunctor` of the underlying
ringed space, with its type written at the `X.Modules` spelling of the category of
`𝒪_X`-modules; see the module docstring for why the spelling matters. -/
def supportedSectionsOn (X : Scheme.{u}) (T : Set X) : X.Modules ⥤ X.Modules :=
  supportedSectionsFunctor X.toRingedSpace T

/-- Taking sections supported on `T` is additive. -/
instance supportedSectionsOn_additive (X : Scheme.{u}) (T : Set X) :
    (supportedSectionsOn X T).Additive :=
  inferInstanceAs (supportedSectionsFunctor X.toRingedSpace T).Additive

/-- **`ℋ ⁿ_T`, sheaf local cohomology with supports in `T`**, read on `X` as the direct image
along the inclusion of the support: the `n`-th right derived functor of `H_T`. -/
def localCohomologyOn (X : Scheme.{u}) (T : Set X) (n : ℕ) : X.Modules ⥤ X.Modules :=
  (supportedSectionsOn X T).rightDerived n

/-! ### Restriction to an open subscheme, homologically -/

variable {X : Scheme.{u}} (T : Set X) (U : X.Opens)

/-- **Restriction of modules to an open subscheme is the restriction `j^*` of extension by
zero.**  Both are a pushforward of sheaves of modules along the functor of images of opens; the
change-of-rings morphism is the identity on one side and `appIso⁻¹` on the other, and the latter
is the identity for the inclusion of an open subscheme. -/
theorem restrictFunctor_eq_jStar :
    Scheme.Modules.restrictFunctor U.ι =
      ExtensionByZeroModules.jStar (X := X.toRingedSpace.carrier) U
        (structureSheafRing X.toRingedSpace) := by
  unfold Scheme.Modules.restrictFunctor ExtensionByZeroModules.jStar
  congr 1
  ext V : 3
  show (forget₂ CommRingCat RingCat).map (U.ι.appIso V.unop).inv = _
  rw [U.ι_appIso]
  exact (forget₂ CommRingCat RingCat).map_id _

/-- **[Stacks, Tag 01E1]: restriction to an open subscheme preserves injective objects.**  This
is `Stacks.Cohomology.HigherDirectImage.jStar_preservesInjectiveObjects` read through
`restrictFunctor_eq_jStar`. -/
@[stacks 01E1 "restriction of modules to an open subscheme preserves injective objects"]
instance restrictFunctor_preservesInjectiveObjects :
    (Scheme.Modules.restrictFunctor U.ι).PreservesInjectiveObjects := by
  rw [restrictFunctor_eq_jStar]
  exact Stacks.Cohomology.HigherDirectImage.jStar_preservesInjectiveObjects U _

/-- Restriction to an open subscheme preserves finite colimits, being a left adjoint. -/
instance restrictFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (Scheme.Modules.restrictFunctor U.ι) :=
  inferInstance

/-- Restriction to an open subscheme preserves homology, being exact. -/
instance restrictFunctor_preservesHomology :
    (Scheme.Modules.restrictFunctor U.ι).PreservesHomology :=
  Functor.preservesHomologyOfExact _

/-! ### Excision in degree zero -/

/-- The inclusions `H_T(ℱ)|_U ⟶ ℱ|_U` of the restricted subsheaf of sections with support, as a
natural transformation. -/
def restrictedSupportedSectionsι :
    supportedSectionsOn X T ⋙ Scheme.Modules.restrictFunctor U.ι ⟶
      Scheme.Modules.restrictFunctor U.ι where
  app F := (Scheme.Modules.restrictFunctor U.ι).map (supportedSectionsSheafι T F)
  naturality F G f :=
    (((Scheme.Modules.restrictFunctor U.ι).map_comp
          ((supportedSectionsOn X T).map f) (supportedSectionsSheafι T G)).symm.trans
        (congrArg (Scheme.Modules.restrictFunctor U.ι).map
          (supportedSectionsSheafι_naturality T f))).trans
      ((Scheme.Modules.restrictFunctor U.ι).map_comp (supportedSectionsSheafι T F) f)

/-- The inclusions `H_{U ∩ T}(ℱ|_U) ⟶ ℱ|_U` of the subsheaf of sections with support in the
preimage of `T`, as a natural transformation. -/
def supportedSectionsιRestricted :
    Scheme.Modules.restrictFunctor U.ι ⋙ supportedSectionsOn U.toScheme (U.ι ⁻¹' T) ⟶
      Scheme.Modules.restrictFunctor U.ι where
  app F := supportedSectionsSheafι (U.ι ⁻¹' T) ((Scheme.Modules.restrictFunctor U.ι).obj F)
  naturality _ _ f :=
    supportedSectionsSheafι_naturality (U.ι ⁻¹' T) ((Scheme.Modules.restrictFunctor U.ι).map f)

/-- **Excision for the subsheaf of sections with support, as a natural isomorphism.**  The
subsheaf of sections of `ℱ` supported on `T`, restricted to `U`, is the subsheaf of sections of
`ℱ|_U` supported on `U ∩ T`.

The comparison at a single module is
`Stacks.Perfect.SupportedSectionsRestriction.exists_supportedSectionsRestrictIso`; what is added
here is that it is natural, which holds because both sides sit inside `ℱ|_U` compatibly with the
comparison and the inclusion of the second is a monomorphism. -/
def supportedSectionsRestrictNatIso :
    supportedSectionsOn X T ⋙ Scheme.Modules.restrictFunctor U.ι ≅
      Scheme.Modules.restrictFunctor U.ι ⋙ supportedSectionsOn U.toScheme (U.ι ⁻¹' T) :=
  NatIso.ofComponents
    (fun F => (SupportedSectionsRestriction.exists_supportedSectionsRestrictIso T U F).choose)
    (natIsoOfMonoOver_naturality (restrictedSupportedSectionsι T U)
      (supportedSectionsιRestricted T U)
      (fun _ => supportedSectionsSheafι_mono (U.ι ⁻¹' T) _)
      (fun F => (SupportedSectionsRestriction.exists_supportedSectionsRestrictIso T U F).choose)
      (fun F =>
        (SupportedSectionsRestriction.exists_supportedSectionsRestrictIso T U F).choose_spec))

/-! ### Excision for sheaf local cohomology -/

/-- **Excision for sheaf local cohomology.**  For a scheme `X`, a subset `T ⊆ X`, an open
subscheme `U ⊆ X` and a degree `n`, local cohomology with supports in `T` is local on `X`:

`ℋ ⁿ_T(ℱ)|_U ≅ ℋ ⁿ_{U ∩ T}(ℱ|_U)`,

naturally in the `𝒪_X`-module `ℱ`.  Here `ℋ ⁿ_T` is `localCohomologyOn`, the `n`-th right
derived functor of the subsheaf of sections supported on `T`, that is, the direct image along
the inclusion of the support of the local cohomology sheaf of [Stacks, Tag 0G6N], so that both
sides are sheaves of modules on `U`.

No closedness assumption on `T` is needed. -/
def localCohomologyRestrictNatIso (n : ℕ) :
    localCohomologyOn X T n ⋙ Scheme.Modules.restrictFunctor U.ι ≅
      Scheme.Modules.restrictFunctor U.ι ⋙ localCohomologyOn U.toScheme (U.ι ⁻¹' T) n :=
  Stacks.Cohomology.ModuleComparison.rightDerivedCompIso (supportedSectionsOn X T)
      (Scheme.Modules.restrictFunctor U.ι) _ (supportedSectionsRestrictNatIso T U) n ≪≫
    Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso
      (Scheme.Modules.restrictFunctor U.ι) (supportedSectionsOn U.toScheme (U.ι ⁻¹' T)) n

/-! ### Transporting a class -/

/-- The excision comparison at a module: the map `ℋ ⁿ_T(ℱ)|_U ⟶ ℋ ⁿ_{U ∩ T}(ℱ|_U)`. -/
def localCohomologyRestrict (n : ℕ) (F : X.Modules) :
    (Scheme.Modules.restrictFunctor U.ι).obj ((localCohomologyOn X T n).obj F) ⟶
      (localCohomologyOn U.toScheme (U.ι ⁻¹' T) n).obj
        ((Scheme.Modules.restrictFunctor U.ι).obj F) :=
  (localCohomologyRestrictNatIso T U n).hom.app F

/-- The inverse excision comparison at a module: the map
`ℋ ⁿ_{U ∩ T}(ℱ|_U) ⟶ ℋ ⁿ_T(ℱ)|_U`. -/
def localCohomologyRestrictInv (n : ℕ) (F : X.Modules) :
    (localCohomologyOn U.toScheme (U.ι ⁻¹' T) n).obj
        ((Scheme.Modules.restrictFunctor U.ι).obj F) ⟶
      (Scheme.Modules.restrictFunctor U.ι).obj ((localCohomologyOn X T n).obj F) :=
  (localCohomologyRestrictNatIso T U n).inv.app F

/-- Applying an isomorphism of modules and then its inverse on sections is the identity. -/
private theorem val_app_inv_val_app_hom {A B : X.Modules} (e : A ≅ B) (V : (X.Opens)ᵒᵖ)
    (s : A.val.obj V) : e.inv.val.app V (e.hom.val.app V s) = s :=
  congrArg (fun φ : A ⟶ A => φ.val.app V s) e.hom_inv_id

/-- **Transporting a local cohomology class from `X` to the chart `U` and back.**  On the
sections over an open `V` of `U` — which are the sections of `ℋ ⁿ_T(ℱ)` over the corresponding
open `U.ι ''ᵁ V` of `X`, by `AlgebraicGeometry.Scheme.Modules.restrictAppIso` — the two
comparisons are mutually inverse. -/
theorem localCohomologyRestrictInv_app_localCohomologyRestrict_app (n : ℕ) (F : X.Modules)
    (V : (U.toScheme.Opens)ᵒᵖ)
    (s : ((Scheme.Modules.restrictFunctor U.ι).obj
      ((localCohomologyOn X T n).obj F)).val.obj V) :
    (localCohomologyRestrictInv T U n F).val.app V
        ((localCohomologyRestrict T U n F).val.app V s) = s :=
  val_app_inv_val_app_hom ((localCohomologyRestrictNatIso T U n).app F) V s

/-- **Transporting a local cohomology class from the chart `U` to `X` and back.** -/
theorem localCohomologyRestrict_app_localCohomologyRestrictInv_app (n : ℕ) (F : X.Modules)
    (V : (U.toScheme.Opens)ᵒᵖ)
    (s : ((localCohomologyOn U.toScheme (U.ι ⁻¹' T) n).obj
      ((Scheme.Modules.restrictFunctor U.ι).obj F)).val.obj V) :
    (localCohomologyRestrict T U n F).val.app V
        ((localCohomologyRestrictInv T U n F).val.app V s) = s :=
  val_app_inv_val_app_hom ((localCohomologyRestrictNatIso T U n).app F).symm V s

/-! ### Reading the comparison over an open of the ambient scheme -/

/-- Sections of a restricted module over an open of `U` are sections of the module over the
corresponding open of `X`.  This holds by definition — it is
`AlgebraicGeometry.Scheme.Modules.restrictAppIso`, which is `Iso.refl` — and is recorded so that
the two sides of the excision comparison can be read as sections over opens of `X`. -/
theorem restrict_sections_eq (M : X.Modules) (V : U.toScheme.Opens) :
    Γ((Scheme.Modules.restrictFunctor U.ι).obj M, V) = Γ(M, U.ι ''ᵁ V) :=
  rfl

/-- The open of the subscheme `U` corresponding to an open `V ≤ U` of `X`: its preimage. -/
def chartOpen {V : X.Opens} (_hV : V ≤ U) : U.toScheme.Opens :=
  U.ι ⁻¹ᵁ V

/-- The open of `X` underlying `chartOpen U hV` is `V` again, because `V` is contained in the
range of the inclusion of `U`. -/
@[simp]
theorem ι_image_chartOpen {V : X.Opens} (hV : V ≤ U) : U.ι ''ᵁ chartOpen U hV = V := by
  refine TopologicalSpace.Opens.ext ?_
  show U.ι.base '' (U.ι.base ⁻¹' (V : Set X)) = (V : Set X)
  rw [Set.image_preimage_eq_inter_range]
  exact Set.inter_eq_self_of_subset_left (by simpa [Scheme.Opens.range_ι] using hV)

/-- Over an open `V ≤ U` of the ambient scheme the two sides of the excision comparison are
sections of `ℋ ⁿ_T(ℱ)` over `V` and sections of `ℋ ⁿ_{U ∩ T}(ℱ|_U)` over the corresponding open
of `U`. -/
theorem restrict_sections_eq_of_le (n : ℕ) (F : X.Modules) {V : X.Opens} (hV : V ≤ U) :
    Γ((Scheme.Modules.restrictFunctor U.ι).obj ((localCohomologyOn X T n).obj F),
        chartOpen U hV) =
      Γ((localCohomologyOn X T n).obj F, V) :=
  congrArg (fun W : X.Opens => Γ((localCohomologyOn X T n).obj F, W)) (ι_image_chartOpen U hV)

/-! ### This is the local cohomology sheaf of Tag 0G6N -/

/-- **`localCohomologyOn` is the direct image of the local cohomology sheaf of
[Stacks, Tag 0G6N].**  For a *closed* `T`, deriving the subsheaf of sections supported on `T` is
deriving the local cohomology sheaf `ℋ ⁿ_T` on `T` and pushing it forward to `X`: the two
degree-zero functors agree by
`supportedSectionsOnClosedFunctor_comp_modulePushforward_iso` of
`Stacks.SheafOfModules.SupportedSections`, and the direct image along the inclusion of a closed
subset is exact ([Stacks, Tag 08KS]), so it commutes with right derived functors.

This is what entitles `localCohomologyRestrictNatIso` to be read as excision for the local
cohomology sheaves themselves, and not merely for a derived functor that happens to agree with
them in degree zero. -/
def localCohomologyOnIso (X : Scheme.{u}) (T : Set X) (hT : IsClosed T) (n : ℕ) :
    letI := Stacks.Cohomology.SupportedComplexes.pushforward_preservesFiniteLimits
      X.toRingedSpace T
    letI := Stacks.Cohomology.SupportedComplexes.pushforward_preservesFiniteColimits
      X.toRingedSpace T hT
    Stacks.Cohomology.SupportedComplexes.localCohomologySheafFunctor X.toRingedSpace T hT n ⋙
        modulePushforward
          (Stacks.Cohomology.SupportedComplexes.closedSubsetInclusion X.toRingedSpace T) ≅
      localCohomologyOn X T n :=
  letI := Stacks.Cohomology.SupportedComplexes.pushforward_preservesFiniteLimits
    X.toRingedSpace T
  letI := Stacks.Cohomology.SupportedComplexes.pushforward_preservesFiniteColimits
    X.toRingedSpace T hT
  Stacks.Cohomology.ModuleComparison.rightDerivedCompIso
    (supportedSectionsOnClosedFunctor X.toRingedSpace T hT)
    (modulePushforward
      (Stacks.Cohomology.SupportedComplexes.closedSubsetInclusion X.toRingedSpace T))
    (supportedSectionsFunctor X.toRingedSpace T)
    (supportedSectionsOnClosedFunctor_comp_modulePushforward_iso X.toRingedSpace T hT) n

end Stacks.Perfect.LocalCohomologyExcision

end
