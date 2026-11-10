module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ShortExactFunctorsTriangle
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.OpenClosedSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The open-closed triangle in the derived category of sheaves of modules

Let `X` be a scheme, let `i : Z ⟶ X` be a closed immersion and let `j : U ⟶ X` be an open
immersion whose image is the complement of the image of `i`, and let `Λ` be a ring.  For every
object `K` of `D(X_étale, Λ)` there is a distinguished triangle
`j_! j^{-1} K ⟶ K ⟶ i_* i^{-1} K ⟶ (j_! j^{-1} K)[1]`,
the first two arrows being the counit of `j_! ⊣ j^{-1}` and the unit of `i^{-1} ⊣ i_*` induced
on the derived category.

The short exact sequence of sheaves of `Λ`-modules underlying it, the module-coefficient form of
Stacks Tag 095L, is proved here as well, by the argument of the abelian case: the inverse images
to `Z` and to `U` jointly reflect isomorphisms, and after each of them the sequence splits.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleEtaleDirectImage`: the direct image `j_*` of sheaves of
  `Λ`-modules along an étale morphism, right adjoint to restriction.
* `Stacks.EtaleCohomology.etaleModuleInverseImageRestrictionIso`: for an étale morphism the
  inverse image along base change is restriction.
* `Stacks.EtaleCohomology.etaleModuleInverseImageSheafFiberIso`: the stalk of an inverse image
  at a geometric point is the stalk at the image geometric point.
* `Stacks.EtaleCohomology.etaleModuleExtensionByZeroOfRestriction` and
  `Stacks.EtaleCohomology.etaleModuleDirectImageOfInverseImage`: the endofunctors `j_! j^{-1}`
  and `i_* i^{-1}` of sheaves of `Λ`-modules.

## Main results

* `Stacks.EtaleCohomology.shortExact_etaleModuleExtensionByZero_directImage`: **Stacks Project,
  Tag 095L** for module coefficients, the short exact sequence
  `0 → j_! j^{-1} ℱ → ℱ → i_* i^{-1} ℱ → 0`.
* `Stacks.EtaleCohomology.exists_distTriang_etaleModuleExtensionByZero_directImage`: **Stacks
  Project, Tag 0GKL**, the distinguished triangle
  `j_! j^{-1} K ⟶ K ⟶ i_* i^{-1} K ⟶ (j_! j^{-1} K)[1]` in `D(X_étale, Λ)`.

## Implementation notes

All four functors are exact, so their derived versions are obtained by applying them to any
complex representing `K`; that is `CategoryTheory.Functor.mapDerivedCategory`, and it is why no
right or left derived functor appears.  Exactness of `j_!` for module coefficients is Tag 03S5 in
the form `Stacks.EtaleCohomology.etaleModuleExtensionByZero_preservesFiniteLimits`; restriction
is exact because it is simultaneously the right adjoint of `j_!` and the left adjoint of the
direct image `j_*` built here from the cocontinuous structure of composition with `j`.

Right exactness of `i_* i^{-1}` is read off the short exact sequence: the component
`ℱ ⟶ i_* i^{-1} ℱ` of the unit is an epimorphism, so
`CategoryTheory.Functor.preservesEpimorphisms_of_epi_natTrans_app_from_id` applies, and a functor
between abelian categories preserving kernels and epimorphisms preserves homology.

The joint reflection of isomorphisms is the stalkwise argument of the abelian case at the
coefficient category `ModuleCat Λ`: the residue geometric points of `Z` and of `U`, pushed
forward to `X`, form a conservative family of points of `X_étale`, and
`CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.jointlyReflectIsomorphisms` turns
conservativity for sheaves of sets into joint reflection at any concrete coefficient category
with the right exactness properties, `ModuleCat Λ` among them.  Unlike the abelian case no
comparison with the Kan-extension construction of the inverse image is needed, the module-valued
inverse image `Stacks.EtaleCohomology.etaleModuleInverseImage` being the abstract left adjoint
that Mathlib's `CategoryTheory.GrothendieckTopology.Point.sheafFiberComapIso` speaks about.

The existence of a derived category with hom sets in a fixed universe is an instance hypothesis
`[HasDerivedCategory.{w} _]`, as throughout Mathlib; `HasDerivedCategory.standard` supplies it.

## References

* [Stacks Project, Tag 0GKL](https://stacks.math.columbia.edu/tag/0GKL)
* [Stacks Project, Tag 095L](https://stacks.math.columbia.edu/tag/095L)
* [Stacks Project, Tag 03S5](https://stacks.math.columbia.edu/tag/03S5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale

universe w u v r

namespace Stacks.EtaleCohomology

/-! ### Filtered colimits of modules in the coefficient universe -/

/-- The forgetful functor from `Λ`-modules in the coefficient universe of sheaves on a small
étale site preserves filtered colimits of that size: it is the passage to abelian groups, which
preserves all colimits of that size, followed by the forgetful functor of abelian groups. -/
theorem preservesFilteredColimits_forget_moduleCat (Λ : Type r) [Ring Λ] :
    PreservesFilteredColimitsOfSize.{v, v} (forget (ModuleCat.{v} Λ)) :=
  have : PreservesColimitsOfSize.{v, v}
      (forget₂ (ModuleCat.{v} Λ) AddCommGrpCat.{v}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{v, r, v, v} Λ
  Limits.comp_preservesFilteredColimits
    (forget₂ (ModuleCat.{v} Λ) AddCommGrpCat.{v}) (forget AddCommGrpCat.{v})

attribute [local instance] preservesFilteredColimits_forget_moduleCat

/-! ### The direct image along an étale morphism -/

section EtaleDirectImage

variable (Λ : Type r) [Ring Λ] {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]

/-- Restriction of sheaves of `Λ`-modules preserves all colimits, being the left adjoint of the
direct image along `j`. -/
instance etaleModuleRestriction_preservesColimits :
    PreservesColimits (etaleModuleRestriction.{u, r} Λ j) :=
  (etaleModuleEtaleDirectImageAdj.{u, r} Λ j).leftAdjoint_preservesColimits

/-- Restriction of sheaves of `Λ`-modules preserves all limits, being the right adjoint of
extension by zero.  With the preservation of colimits this says that restriction is exact. -/
instance etaleModuleRestriction_preservesLimits :
    PreservesLimits (etaleModuleRestriction.{u, r} Λ j) :=
  (etaleModuleExtensionByZeroAdj.{u, r} Λ j).rightAdjoint_preservesLimits

section Mono

variable [Mono j]

end Mono

end EtaleDirectImage

/-! ### Sections over an empty object -/

/-- A sheaf of `Λ`-modules on the small étale site has zero sections over an object whose
underlying scheme is empty. -/
theorem isZero_moduleSections_of_isEmpty (Λ : Type r) [Ring Λ] {X : Scheme.{u}}
    (F : EtaleModules.{u, r} Λ X) (V : X.Etale) (hV : IsEmpty V.left) :
    IsZero (F.obj.obj (op V)) :=
  (F.isTerminalOfBotCover V (bot_mem_smallEtaleTopology_of_isEmpty V hV)).isZero

/-- A sheaf of `Λ`-modules on the small étale site all of whose modules of sections vanish is
zero. -/
theorem isZero_of_forall_isZero_moduleSections (Λ : Type r) [Ring Λ] {X : Scheme.{u}}
    (F : EtaleModules.{u, r} Λ X) (hF : ∀ V : X.Etale, IsZero (F.obj.obj (op V))) :
    IsZero F :=
  IsZero.of_full_of_faithful_of_isZero (sheafToPresheaf _ _) F
    ((Functor.isZero_iff _).2 fun V ↦ hF V.unop)

/-! ### Full faithfulness of the direct image along a closed immersion -/

/-- The direct image along a closed immersion is fully faithful on sheaves of `Λ`-modules: base
change along a closed immersion is cover dense and locally full. -/
def etaleModuleDirectImageFullyFaithful (Λ : Type r) [Ring Λ] {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] : (etaleModuleDirectImage.{u, r} Λ i).FullyFaithful :=
  Functor.FullyFaithful.ofFullyFaithful _

/-- For a closed immersion `i`, the unit `ℱ ⟶ i_* i^{-1} ℱ` becomes invertible after applying
`i^{-1}`. -/
theorem isIso_etaleModuleInverseImage_map_unit (Λ : Type r) [Ring Λ] {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (F : EtaleModules.{u, r} Λ X) :
    IsIso ((etaleModuleInverseImage.{u, r} Λ i).map
      ((etaleModuleInverseImageAdj.{u, r} Λ i).unit.app F)) := by
  have ff := etaleModuleDirectImageFullyFaithful.{u, r} Λ i
  have := ff.full
  have := ff.faithful
  infer_instance

/-! ### The short exact sequence of a closed subscheme and its open complement -/

section Complementary

variable (Λ : Type r) [Ring Λ] {Z U X : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X) [Etale j]
  (hij : Set.range j.base = (Set.range i.base)ᶜ)

include hij

/-- Restricting to `U` a direct image from `Z` gives zero: the sections of such a restriction
over an étale `U`-scheme are sections over an empty scheme. -/
theorem isZero_etaleModuleRestriction_etaleModuleDirectImage (G : EtaleModules.{u, r} Λ Z) :
    IsZero ((etaleModuleRestriction.{u, r} Λ j).obj
      ((etaleModuleDirectImage.{u, r} Λ i).obj G)) :=
  isZero_of_forall_isZero_moduleSections Λ _ fun W ↦
    isZero_moduleSections_of_isEmpty Λ G _
      (isEmpty_smallEtaleBaseChange_smallEtaleCompose i j hij W)

/-- The inverse image to `Z` of an extension by zero from `U` is zero: by the two adjunctions it
receives no nonzero map, restricting to `U` a direct image from `Z` already vanishing. -/
theorem isZero_etaleModuleInverseImage_extensionByZero (G : EtaleModules.{u, r} Λ U) :
    IsZero ((etaleModuleInverseImage.{u, r} Λ i).obj
      ((etaleModuleExtensionByZero.{u, r} Λ j).obj G)) :=
  (IsZero.iff_id_eq_zero _).2 <|
    ((etaleModuleInverseImageAdj.{u, r} Λ i).homEquiv _ _).injective
      (((etaleModuleExtensionByZeroAdj.{u, r} Λ j).homEquiv _ _).injective
        ((isZero_etaleModuleRestriction_etaleModuleDirectImage Λ i j hij _).eq_of_tgt _ _))

/-- The composite `j_! j^{-1} ℱ ⟶ ℱ ⟶ i_* i^{-1} ℱ` of the two canonical maps is zero: under the
adjunction `j_! ⊣ j^{-1}` it corresponds to a map into `j^{-1} i_* i^{-1} ℱ`, which is zero. -/
theorem etaleModuleExtensionByZero_counit_comp_inverseImage_unit
    (F : EtaleModules.{u, r} Λ X) :
    (etaleModuleExtensionByZeroAdj.{u, r} Λ j).counit.app F ≫
      (etaleModuleInverseImageAdj.{u, r} Λ i).unit.app F = 0 :=
  ((etaleModuleExtensionByZeroAdj.{u, r} Λ j).homEquiv _ _).injective
    ((isZero_etaleModuleRestriction_etaleModuleDirectImage Λ i j hij _).eq_of_tgt _ _)

omit hij [Etale j] in
/-- A map of sheaves of `Λ`-modules on `X_étale` that becomes invertible after `i^{-1}` and after
`j^{-1}` has invertible stalk at every geometric point of the family `complementPoint`. -/
theorem isIso_moduleSheafFiber_map_complementPoint {F G : EtaleModules.{u, r} Λ X} (γ : F ⟶ G)
    [IsIso ((etaleModuleInverseImage.{u, r} Λ i).map γ)]
    [IsIso ((etaleModuleInverseImage.{u, r} Λ j).map γ)] (a : Z ⊕ U) :
    IsIso (((pointSmallEtale
      (complementPoint i j a)).ulift.{max (u + 1) r}).sheafFiber.map γ) := by
  cases a with
  | inl z =>
    refine (NatIso.isIso_map_iff
      (etaleModuleInverseImageSheafFiberIso.{u, r} Λ i (residueGeometricPoint Z z)) γ).mp ?_
    change IsIso (((pointSmallEtale
      (residueGeometricPoint Z z)).ulift.{max (u + 1) r}).sheafFiber.map
        ((etaleModuleInverseImage.{u, r} Λ i).map γ))
    infer_instance
  | inr w =>
    refine (NatIso.isIso_map_iff
      (etaleModuleInverseImageSheafFiberIso.{u, r} Λ j (residueGeometricPoint U w)) γ).mp ?_
    change IsIso (((pointSmallEtale
      (residueGeometricPoint U w)).ulift.{max (u + 1) r}).sheafFiber.map
        ((etaleModuleInverseImage.{u, r} Λ j).map γ))
    infer_instance

omit [Etale j] in
/-- Inverse image to the closed part and inverse image to the open part jointly reflect
isomorphisms of sheaves of `Λ`-modules on the small étale site of `X`.

The residue geometric points of `Z` and of `U`, pushed forward to `X`, form a conservative family
of points of `X_étale`, and the stalk of an inverse image at such a point is the stalk of the
original sheaf there. -/
theorem isIso_of_isIso_etaleModuleInverseImage {F G : EtaleModules.{u, r} Λ X} (γ : F ⟶ G)
    [IsIso ((etaleModuleInverseImage.{u, r} Λ i).map γ)]
    [IsIso ((etaleModuleInverseImage.{u, r} Λ j).map γ)] : IsIso γ := by
  have hP : (ObjectProperty.ofObj (fun a ↦ (pointSmallEtale
      (complementPoint i j a)).ulift.{max (u + 1) r})).IsConservativeFamilyOfPoints :=
    Scheme.isConservative_pointSmallEtale_ulift _ (iUnion_range_complementPoint i j hij)
  have happ : ∀ p : (ObjectProperty.ofObj (fun a ↦ (pointSmallEtale
      (complementPoint i j a)).ulift.{max (u + 1) r})).FullSubcategory,
      IsIso (p.obj.sheafFiber.map γ) := by
    rintro ⟨_, ⟨a⟩⟩
    exact isIso_moduleSheafFiber_map_complementPoint Λ i j γ a
  exact (hP.jointlyReflectIsomorphisms (ModuleCat.{max (u + 1) r} Λ)).isIso γ

end Complementary

/-- **Stacks Project, Tag 095L** for module coefficients.  Let `X` be a scheme, let `i : Z ⟶ X`
be a closed immersion and let `j : U ⟶ X` be an open immersion whose image is the complement of
the image of `i`, and let `Λ` be a ring.  For every sheaf `ℱ` of `Λ`-modules on the small étale
site of `X` the counit of `j_! ⊣ j^{-1}` and the unit of `i^{-1} ⊣ i_*` form a short exact
sequence
`0 → j_! j^{-1} ℱ → ℱ → i_* i^{-1} ℱ → 0`
of sheaves of `Λ`-modules on `X_étale`. -/
@[stacks 095L "module coefficients", sga "4 IV 14.6" "(14.6.1)", sga "4 VIII 6.5" "partial"]
theorem shortExact_etaleModuleExtensionByZero_directImage (Λ : Type r) [Ring Λ]
    {Z U X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]
    (hij : Set.range j.base = (Set.range i.base)ᶜ) (F : EtaleModules.{u, r} Λ X) :
    ∃ h : (etaleModuleExtensionByZeroAdj.{u, r} Λ j).counit.app F ≫
        (etaleModuleInverseImageAdj.{u, r} Λ i).unit.app F = 0,
      (ShortComplex.mk ((etaleModuleExtensionByZeroAdj.{u, r} Λ j).counit.app F)
        ((etaleModuleInverseImageAdj.{u, r} Λ i).unit.app F) h).ShortExact := by
  refine ⟨etaleModuleExtensionByZero_counit_comp_inverseImage_unit Λ i j hij F, ?_⟩
  let L : (b : Bool) → EtaleModules.{u, r} Λ X ⥤
      EtaleModules.{u, r} Λ (if b then U else Z) := fun
    | false => etaleModuleInverseImage.{u, r} Λ i
    | true => etaleModuleInverseImage.{u, r} Λ j
  have _ : ∀ b, PreservesFiniteLimits (L b) := fun b ↦ by
    cases b <;> exact etaleModuleInverseImage_preservesFiniteLimits.{u, r} Λ _
  have _ : ∀ b, PreservesFiniteColimits (L b) := fun b ↦ by
    cases b <;> exact etaleModuleInverseImage_preservesFiniteColimits.{u, r} Λ _
  have hL : JointlyReflectIsomorphisms L := ⟨fun γ hγ ↦
    have _ : IsIso ((etaleModuleInverseImage.{u, r} Λ i).map γ) := hγ false
    have _ : IsIso ((etaleModuleInverseImage.{u, r} Λ j).map γ) := hγ true
    isIso_of_isIso_etaleModuleInverseImage Λ i j hij γ⟩
  refine (hL.shortExact_iff _).2 fun b ↦ ?_
  cases b
  · exact (ShortComplex.Splitting.ofIsZeroOfIsIso _
      (isZero_etaleModuleInverseImage_extensionByZero Λ i j hij _)
      (isIso_etaleModuleInverseImage_map_unit.{u, r} Λ i F)).shortExact
  · exact (ShortComplex.Splitting.ofIsIsoOfIsZero _
      ((NatIso.isIso_map_iff (etaleModuleInverseImageRestrictionIso.{u, r} Λ j)
        ((etaleModuleExtensionByZeroAdj.{u, r} Λ j).counit.app F)).mpr
          (isIso_etaleModuleRestriction_map_counit.{u, r} Λ j F))
      (IsZero.of_iso (isZero_etaleModuleRestriction_etaleModuleDirectImage Λ i j hij _)
        ((etaleModuleInverseImageRestrictionIso.{u, r} Λ j).app _))).shortExact

/-! ### The two endofunctors -/

/-- The endofunctor `i_* i^{-1}` of sheaves of `Λ`-modules on the small étale site of `X`, for a
morphism of schemes `i : Z ⟶ X`: take the inverse image to `Z`, then push forward. -/
abbrev etaleModuleDirectImageOfInverseImage (Λ : Type r) [Ring Λ] {Z X : Scheme.{u}}
    (i : Z ⟶ X) : EtaleModules.{u, r} Λ X ⥤ EtaleModules.{u, r} Λ X :=
  etaleModuleInverseImage.{u, r} Λ i ⋙ etaleModuleDirectImage.{u, r} Λ i

/-- The composite `i_* i^{-1}` is additive, preserving binary products: the inverse image
preserves finite limits and the direct image preserves all limits, being a right adjoint. -/
instance etaleModuleDirectImageOfInverseImage_additive (Λ : Type r) [Ring Λ]
    {Z X : Scheme.{u}} (i : Z ⟶ X) :
    (etaleModuleDirectImageOfInverseImage.{u, r} Λ i).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The composite `i_* i^{-1}` is left exact: the inverse image preserves finite limits and the
direct image, being a right adjoint, preserves all limits. -/
instance etaleModuleDirectImageOfInverseImage_preservesFiniteLimits (Λ : Type r) [Ring Λ]
    {Z X : Scheme.{u}} (i : Z ⟶ X) :
    PreservesFiniteLimits (etaleModuleDirectImageOfInverseImage.{u, r} Λ i) :=
  have := etaleModuleInverseImage_preservesFiniteLimits.{u, r} Λ i
  have : PreservesLimits (etaleModuleDirectImage.{u, r} Λ i) :=
    (etaleModuleInverseImageAdj.{u, r} Λ i).rightAdjoint_preservesLimits
  comp_preservesFiniteLimits _ _

/-- The composite `j_! j^{-1}` is exact: restriction is exact and extension by zero is exact by
Tag 03S5 for module coefficients. -/
instance etaleModuleExtensionByZeroOfRestriction_preservesFiniteLimits (Λ : Type r) [Ring Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] :
    PreservesFiniteLimits (etaleModuleExtensionByZeroOfRestriction.{u, r} Λ j) :=
  comp_preservesFiniteLimits _ _

/-- The composite `j_! j^{-1}` preserves finite colimits, both factors doing so. -/
instance etaleModuleExtensionByZeroOfRestriction_preservesFiniteColimits (Λ : Type r) [Ring Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] :
    PreservesFiniteColimits (etaleModuleExtensionByZeroOfRestriction.{u, r} Λ j) :=
  comp_preservesFiniteColimits _ _

/-! ### Exactness of `i_* i^{-1}` -/

section Epi

variable (Λ : Type r) [Ring Λ] {Z U X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
  (j : U ⟶ X) [IsOpenImmersion j] (hij : Set.range j.base = (Set.range i.base)ᶜ)

include hij

/-- Each component `ℱ ⟶ i_* i^{-1} ℱ` of the unit of `i^{-1} ⊣ i_*` is an epimorphism: it is the
right-hand map of the short exact sequence of Tag 095L for module coefficients. -/
theorem epi_etaleModuleInverseImageAdj_unit_app (F : EtaleModules.{u, r} Λ X) :
    Epi ((etaleModuleInverseImageAdj.{u, r} Λ i).unit.app F) :=
  (shortExact_etaleModuleExtensionByZero_directImage.{u, r} Λ i j hij F).choose_spec.epi_g

/-- The composite `i_* i^{-1}` preserves epimorphisms: the unit of `i^{-1} ⊣ i_*` is a natural
transformation from the identity functor with epimorphic components. -/
theorem etaleModuleDirectImageOfInverseImage_preservesEpimorphisms_of_range_eq_compl :
    (etaleModuleDirectImageOfInverseImage.{u, r} Λ i).PreservesEpimorphisms :=
  Functor.preservesEpimorphisms_of_epi_natTrans_app_from_id
    (etaleModuleInverseImageAdj.{u, r} Λ i).unit
    (epi_etaleModuleInverseImageAdj_unit_app.{u, r} Λ i j hij)

end Epi

section ClosedImmersion

variable (Λ : Type r) [Ring Λ] {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- The composite `i_* i^{-1}` along a closed immersion preserves epimorphisms.  The open
complement of the image of `i` is an open subscheme of `X` whose inclusion has exactly the
complementary range, so the short exact sequence of Tag 095L applies. -/
instance etaleModuleDirectImageOfInverseImage_preservesEpimorphisms :
    (etaleModuleDirectImageOfInverseImage.{u, r} Λ i).PreservesEpimorphisms := by
  let V : X.Opens := ⟨(Set.range i.base)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  exact etaleModuleDirectImageOfInverseImage_preservesEpimorphisms_of_range_eq_compl.{u, r}
    Λ i V.ι (by simp [V])

/-- The composite `i_* i^{-1}` along a closed immersion is right exact: it preserves kernels,
being left exact, and it preserves epimorphisms, so it preserves homology and therefore finite
colimits.  Together with left exactness this says that `i_* i^{-1}` is exact. -/
instance etaleModuleDirectImageOfInverseImage_preservesFiniteColimits :
    PreservesFiniteColimits (etaleModuleDirectImageOfInverseImage.{u, r} Λ i) :=
  have := Functor.preservesHomology_of_preservesEpis_and_kernels
    (etaleModuleDirectImageOfInverseImage.{u, r} Λ i)
  Functor.preservesFiniteColimits_of_preservesHomology _

end ClosedImmersion

/-! ### The distinguished triangle -/

/-- **Stacks Project, Tag 0GKL.**  Let `X` be a scheme, let `i : Z ⟶ X` be a closed immersion and
let `j : U ⟶ X` be an open immersion whose image is the complement of the image of `i`, and let
`Λ` be a ring.  For every object `K` of the derived category `D(X_étale, Λ)` of sheaves of
`Λ`-modules on the small étale site of `X` there is a distinguished triangle
`j_! j^{-1} K ⟶ K ⟶ i_* i^{-1} K ⟶ (j_! j^{-1} K)[1]`,
whose first arrow is the counit of `j_! ⊣ j^{-1}` and whose second arrow is the unit of
`i^{-1} ⊣ i_*`, both induced on the derived category by exactness of the four functors
involved. -/
@[stacks 0GKL]
theorem exists_distTriang_etaleModuleExtensionByZero_directImage (Λ : Type r) [Ring Λ]
    {Z U X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]
    (hij : Set.range j.base = (Set.range i.base)ᶜ)
    [HasDerivedCategory.{w} (EtaleModules.{u, r} Λ X)]
    (K : DerivedCategory (EtaleModules.{u, r} Λ X)) :
    ∃ δ : (etaleModuleDirectImageOfInverseImage.{u, r} Λ i).mapDerivedCategory.obj K ⟶
        ((etaleModuleExtensionByZeroOfRestriction.{u, r} Λ j).mapDerivedCategory.obj K)⟦(1 : ℤ)⟧,
      Triangle.mk
        (((etaleModuleExtensionByZeroOfRestriction.{u, r} Λ j).mapDerivedCategoryTransToId
          (etaleModuleExtensionByZeroAdj.{u, r} Λ j).counit).app K)
        (((etaleModuleDirectImageOfInverseImage.{u, r} Λ i).mapDerivedCategoryTransFromId
          (etaleModuleInverseImageAdj.{u, r} Λ i).unit).app K) δ ∈
        distTriang (DerivedCategory (EtaleModules.{u, r} Λ X)) :=
  DerivedCategory.exists_distTriang_of_natTrans_shortExact
    (etaleModuleExtensionByZeroOfRestriction.{u, r} Λ j)
    (etaleModuleDirectImageOfInverseImage.{u, r} Λ i)
    (etaleModuleExtensionByZeroAdj.{u, r} Λ j).counit
    (etaleModuleInverseImageAdj.{u, r} Λ i).unit
    (etaleModuleExtensionByZero_counit_comp_inverseImage_unit Λ i j hij)
    (fun F ↦ (shortExact_etaleModuleExtensionByZero_directImage.{u, r} Λ i j hij F).choose_spec) K

end Stacks.EtaleCohomology

end
