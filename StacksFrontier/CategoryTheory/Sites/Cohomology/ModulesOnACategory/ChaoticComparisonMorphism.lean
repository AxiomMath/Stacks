module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.DerivedAdjunction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.BrownRepresentability
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.ChaoticModelTransport
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The comparison morphism between a topology and the chaotic topology, on modules

Let `C` be a category carrying a Grothendieck topology `τ = J`, let `τ'` be the chaotic topology
on `C`, and let `O` be a `τ`-sheaf of rings.  The identity functor of `C` is a morphism of ringed
sites `ε : (C_τ, O_τ) ⟶ (C_τ', O_τ')`.  Every presheaf is a `τ'`-sheaf, so a module on
`(C_τ', O_τ')` is the same thing as a presheaf of `O`-modules; under that dictionary the two
functors attached to `ε` are the forgetful functor `ε_*`, which reads a `τ`-sheaf of modules as a
presheaf of modules, and `τ`-sheafification `ε^*`.

This file constructs `ε_*`, `ε^*` and their adjunction, records the exactness of `ε^*` and the
identity `ε^* ∘ ε_* = id`, and then passes to the unbounded derived categories.  Since `ε^*` is
exact it descends directly to `Lε^*`; `ε_*` is only left exact, so it acquires a genuine total
right derived functor `Rε_*`, computed by K-injective resolutions.  The derived functors are
again adjoint, and the identity `ε^* ∘ Rε_* = id` survives, so `Rε_*` is fully faithful.

Finally, for a full subcategory of `D(O)` which is stable under isomorphism and on which the unit
`M ⟶ Rε_*(ε^*M)` is invertible, `ε^*` lands in the full subcategory of `D(C_τ, O_τ)` cut out by
`Rε_*K` lying in the given one, and `Rε_*` restricts to an equivalence between the two.

## Main definitions

* `Stacks.ModulesOnACategory.ChaoticComparison.epsilonPushforward`: `ε_*`, a `τ`-sheaf of
  `O`-modules read as a presheaf of modules.
* `Stacks.ModulesOnACategory.ChaoticComparison.epsilonPullback`: `ε^*`, `τ`-sheafification.
* `Stacks.ModulesOnACategory.ChaoticComparison.epsilonAdjunction`: the adjunction `ε^* ⊣ ε_*`.
* `Stacks.ModulesOnACategory.ChaoticComparison.epsilonCounitIso`: the identity `ε^* ∘ ε_* = id`.
* `Stacks.ModulesOnACategory.ChaoticComparison.derivedEpsilonPushforward`: the total right
  derived functor `Rε_* : D(C_τ, O_τ) ⥤ D(O)`, with its comparison map
  `derivedEpsilonPushforwardUnit`.
* `Stacks.ModulesOnACategory.ChaoticComparison.derivedEpsilonAdjunction`: the derived adjunction
  `Lε^* ⊣ Rε_*`.
* `Stacks.ModulesOnACategory.ChaoticComparison.derivedPushforwardPullbackIso`: the identity
  `ε^* ∘ Rε_* = id`.
* `Stacks.ModulesOnACategory.ChaoticComparison.pushforwardProperty`: the property of an object
  `K` of `D(C_τ, O_τ)` that `Rε_*K` satisfies a given property of objects of `D(O)`.
* `Stacks.ModulesOnACategory.ChaoticComparison.restrictedPullback` and
  `restrictedPushforward`: the restrictions of `ε^*` and `Rε_*` to those full subcategories.

## Main results

* `Stacks.ModulesOnACategory.ChaoticComparison.epsilonPullback_preservesFiniteLimits` and
  `epsilonPullback_preservesFiniteColimits`: `ε^*` is exact.
* `Stacks.ModulesOnACategory.ChaoticComparison.derivedEpsilonPushforwardFullyFaithful`: `Rε_*`
  is fully faithful.
* `Stacks.ModulesOnACategory.ChaoticComparison.pushforwardProperty_mapDerivedCategory_obj`: if
  the unit is invertible at `M`, then `Rε_*(ε^*M)` again satisfies the property `M` does.
* `Stacks.ModulesOnACategory.ChaoticComparison.restrictedEquivalence`: `Rε_*` restricts to an
  equivalence from the objects `K` with `Rε_*K` in the given subcategory onto that subcategory.
* `Stacks.ModulesOnACategory.ChaoticComparison.chaoticEpsilonEquivalence`: when `τ` is itself the
  chaotic topology, `ε^*` and `ε_*` are already mutually inverse equivalences, which is the
  dictionary identifying modules on `(C_τ', O_τ')` with presheaves of modules.

## Implementation notes

`ε_*` is `SheafOfModules.forget` followed by restriction of scalars along the identity of `O`, the
latter inserted so that `ε_*` is literally the right adjoint of sheafification and the adjunction
is Mathlib's `PresheafOfModules.sheafificationAdjunction`; no new construction is needed at the
level of modules.  That the counit of this adjunction is invertible is the statement that a sheaf
of modules is its own sheafification, and it is what makes `ε_*` fully faithful.

The derived functor `Rε_*` is the total right derived functor of `ε_*` along the localization
`DerivedCategory.Qh` of the homotopy category.  It exists because sheaves of modules form a
Grothendieck abelian category, so every cochain complex admits a K-injective resolution, and
`ε_*` is additive.  The derived adjunction is not formal: it needs `Rε_*` to stay a right derived
functor after post-composition with `Lε^*`, which again comes from K-injective resolutions, and
this is supplied by `Stacks.DerivedFunctor.derivedAdjunction`.

The identity `ε^* ∘ Rε_* = id` is obtained by comparing two right derived functors of one and the
same functor.  Post-composing the comparison map of `Rε_*` with `Lε^*` exhibits `Rε_* ⋙ Lε^*` as
a right derived functor of `ε_*` followed by `Lε^*`, and the counit isomorphism identifies that
composite with the localization functor itself, of which the identity functor is visibly a right
derived functor; uniqueness of right derived functors then gives the isomorphism.

The restriction statements are phrased for an arbitrary property `P` of objects of `D(O)` which
is stable under isomorphism, rather than for the subcategory `QC(O)` of tag 0GYV specifically, so
that they apply to `Stacks.ModulesOnACategory.QuasiCoherentEquivalence.IsQC` for any choice of
base-change data, and to any other such subcategory.  The hypothesis that the unit is invertible
on `P` is an input here: establishing it for `QC(O)` is where the source's acyclicity assumption
on K-flat complexes enters, and that assumption is not formalized in this file.

The module universe is `max u v r w` for an arbitrary `w`, which is the universe in which
`PresheafOfModules` and `SheafOfModules` over the site are Grothendieck abelian and therefore the
one in which both derived categories exist with morphism types in the module universe; the
universes of the site, of its morphisms and of the section rings are independent.

## References

* [Stacks Project, Section 21.42](https://stacks.math.columbia.edu/tag/0EWK)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
* [Stacks Project, Tag 0GZS](https://stacks.math.columbia.edu/tag/0GZS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.ModulesOnACategory.ChaoticComparison

universe w u v r

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{r})
  [HasSheafify J AddCommGrpCat.{max u v r w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r w}]

/-! ### The comparison morphism on modules -/

/-- `ε_*` on modules: a `τ`-sheaf of `O`-modules read as a module on the chaotic site, that is as
a presheaf of modules.  Restriction of scalars along the identity of `O` is inserted so that this
is literally the right adjoint of `τ`-sheafification. -/
abbrev epsilonPushforward :
    SheafOfModules.{max u v r w} R ⥤ PresheafOfModules.{max u v r w} R.obj :=
  SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)

/-- `ε^*` on modules: `τ`-sheafification of a presheaf of modules, that is of a module on the
chaotic site. -/
abbrev epsilonPullback :
    PresheafOfModules.{max u v r w} R.obj ⥤ SheafOfModules.{max u v r w} R :=
  PresheafOfModules.sheafification (𝟙 R.obj)

/-- `ε^*` is left adjoint to `ε_*`: a map of presheaves of modules into a sheaf of modules is the
same thing as a map from the sheafification. -/
def epsilonAdjunction : epsilonPullback.{w} R ⊣ epsilonPushforward.{w} R :=
  PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)

/-- `ε^*` preserves finite limits. -/
instance epsilonPullback_preservesFiniteLimits :
    PreservesFiniteLimits (epsilonPullback.{w} R) :=
  inferInstance

/-- `ε^*` preserves finite colimits, being a left adjoint. -/
instance epsilonPullback_preservesFiniteColimits :
    PreservesFiniteColimits (epsilonPullback.{w} R) :=
  inferInstance

/-- `ε^*` is additive, being exact. -/
instance epsilonPullback_additive : (epsilonPullback.{w} R).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- `ε_*` is additive: it is the identity on underlying abelian-group-valued presheaves. -/
instance epsilonPushforward_additive : (epsilonPushforward.{w} R).Additive :=
  inferInstance

/-- `ε_*` is full. -/
instance epsilonPushforward_full : (epsilonPushforward.{w} R).Full :=
  inferInstance

/-- `ε_*` is faithful. -/
instance epsilonPushforward_faithful : (epsilonPushforward.{w} R).Faithful :=
  inferInstance

/-- **The identity `ε^* ∘ ε_* = id`.**  A sheaf of modules is its own sheafification, so the
counit of the adjunction is an isomorphism. -/
def epsilonCounitIso :
    epsilonPushforward.{w} R ⋙ epsilonPullback.{w} R ≅ 𝟭 (SheafOfModules.{max u v r w} R) :=
  asIso (epsilonAdjunction.{w} R).counit

/-! ### The two derived categories -/

/-- Sheaves of modules on a site form a Grothendieck abelian category, with the site, ring and
module universes independent. -/
@[sga "4 II 6.7"]
instance sheafOfModules_isGrothendieckAbelian :
    IsGrothendieckAbelian.{max u v r w} (SheafOfModules.{max u v r w} R) :=
  Stacks.SheafOfModules.sheafModulesGrothendieck.{u, v, r, w} J R

/-- The derived category of `τ`-sheaves of `O`-modules, in the small-Hom model: its morphism
types lie in the module universe. -/
instance sheafOfModules_hasDerivedCategory :
    HasDerivedCategory.{max u v r w} (SheafOfModules.{max u v r w} R) :=
  Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian _

/-- Every cochain complex of `τ`-sheaves of `O`-modules admits a quasi-isomorphism into a
K-injective complex, the category being Grothendieck abelian. -/
theorem exists_quasiIso_isKInjective
    (K : CochainComplex (SheafOfModules.{max u v r w} R) ℤ) :
    ∃ (I : CochainComplex (SheafOfModules.{max u v r w} R) ℤ) (q : K ⟶ I),
      I.IsKInjective ∧ QuasiIso q :=
  Stacks.DerivedFunctor.exists_quasiIso_isKInjective K

/-! ### The derived functors and their adjunction -/

/-- `ε_*` has a pointwise total right derived functor on the whole unbounded derived category,
computed by K-injective resolutions. -/
instance epsilonPushforward_hasPointwiseRightDerivedFunctor :
    ((epsilonPushforward.{w} R).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).HasPointwiseRightDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{max u v r w} R) (ComplexShape.up ℤ)) :=
  Stacks.DerivedFunctor.hasPointwiseRightDerivedFunctor_of_exists_isKInjective _
    (exists_quasiIso_isKInjective.{w} R)

/-- **`Rε_* : D(C_τ, O_τ) ⥤ D(O)`**, the total right derived functor of `ε_*`.  Unlike `ε^*`, the
functor `ε_*` is only left exact, so this is a genuine derived functor and not the degreewise
extension of `ε_*`. -/
def derivedEpsilonPushforward :
    DerivedCategory (SheafOfModules.{max u v r w} R) ⥤
      DerivedCategory (PresheafOfModules.{max u v r w} R.obj) :=
  ((epsilonPushforward.{w} R).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{max u v r w} R) (ComplexShape.up ℤ))

/-- The comparison map `Q(ε_*X^•) ⟶ Rε_*(QX^•)` exhibiting `Rε_*` as the right derived functor
of `ε_*`. -/
def derivedEpsilonPushforwardUnit :
    (epsilonPushforward.{w} R).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ derivedEpsilonPushforward.{w} R :=
  ((epsilonPushforward.{w} R).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{max u v r w} R) (ComplexShape.up ℤ))

/-- `Rε_*`, with its comparison map, is the right derived functor of `ε_*`. -/
instance derivedEpsilonPushforward_isRightDerivedFunctor :
    (derivedEpsilonPushforward.{w} R).IsRightDerivedFunctor
      (derivedEpsilonPushforwardUnit.{w} R)
      (HomotopyCategory.quasiIso (SheafOfModules.{max u v r w} R) (ComplexShape.up ℤ)) :=
  inferInstanceAs (Functor.IsRightDerivedFunctor _
    (((epsilonPushforward.{w} R).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh _) _)

/-- **The derived adjunction `Lε^* ⊣ Rε_*`.**  Since `ε^*` is exact, `Lε^*` is its degreewise
extension `Functor.mapDerivedCategory`; the adjunction with the total right derived functor of
`ε_*` holds because `Rε_*` remains a right derived functor after post-composition with `Lε^*`,
K-injective resolutions computing both. -/
def derivedEpsilonAdjunction :
    (epsilonPullback.{w} R).mapDerivedCategory ⊣ derivedEpsilonPushforward.{w} R :=
  Stacks.DerivedFunctor.derivedAdjunction (epsilonAdjunction.{w} R)
    (derivedEpsilonPushforward.{w} R) (derivedEpsilonPushforwardUnit.{w} R)
    (exists_quasiIso_isKInjective.{w} R)

/-- The functor of which `Rε_* ⋙ Lε^*` is a right derived functor is the localization functor
itself: degreewise, `ε^* ∘ ε_*` is the identity. -/
def pushforwardPullbackSourceIso :
    ((epsilonPushforward.{w} R).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh) ⋙ (epsilonPullback.{w} R).mapDerivedCategory ≅
      DerivedCategory.Qh (C := SheafOfModules.{max u v r w} R) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (epsilonPullback.{w} R).mapDerivedCategoryFactorsh ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso (epsilonCounitIso.{w} R) (ComplexShape.up ℤ) ≪≫
        Stacks.ModulesOnACategory.mapHomotopyCategoryIdIso
          (SheafOfModules.{max u v r w} R)) _ ≪≫
    Functor.leftUnitor _

/-- **The identity `ε^* ∘ Rε_* = id`.**  Both `Rε_* ⋙ Lε^*` and the identity functor are right
derived functors of the localization functor, so they are canonically isomorphic. -/
def derivedPushforwardPullbackIso :
    derivedEpsilonPushforward.{w} R ⋙ (epsilonPullback.{w} R).mapDerivedCategory ≅
      𝟭 (DerivedCategory (SheafOfModules.{max u v r w} R)) :=
  letI := Stacks.DerivedFunctor.isRightDerivedFunctor_comp_mapDerivedCategory
    (epsilonPushforward.{w} R) (derivedEpsilonPushforward.{w} R)
    (derivedEpsilonPushforwardUnit.{w} R) (epsilonPullback.{w} R)
    (exists_quasiIso_isKInjective.{w} R)
  letI := Functor.isRightDerivedFunctor_of_inverts
    (HomotopyCategory.quasiIso (SheafOfModules.{max u v r w} R) (ComplexShape.up ℤ))
    (𝟭 (DerivedCategory (SheafOfModules.{max u v r w} R)))
    (Functor.rightUnitor (DerivedCategory.Qh (C := SheafOfModules.{max u v r w} R)))
  Functor.rightDerivedNatIso _ _
    (Functor.whiskerRight (derivedEpsilonPushforwardUnit.{w} R)
        (epsilonPullback.{w} R).mapDerivedCategory ≫ (Functor.associator _ _ _).hom)
    (Functor.rightUnitor (DerivedCategory.Qh (C := SheafOfModules.{max u v r w} R))).inv
    (HomotopyCategory.quasiIso (SheafOfModules.{max u v r w} R) (ComplexShape.up ℤ))
    (pushforwardPullbackSourceIso.{w} R)

/-- The counit of the derived adjunction is an isomorphism. -/
instance isIso_derivedEpsilonAdjunction_counit :
    IsIso (derivedEpsilonAdjunction.{w} R).counit :=
  (derivedEpsilonAdjunction.{w} R).isIso_counit_of_iso
    (derivedPushforwardPullbackIso.{w} R)

/-- **`Rε_*` is fully faithful**, being a right adjoint whose composition with its left adjoint is
the identity. -/
def derivedEpsilonPushforwardFullyFaithful :
    (derivedEpsilonPushforward.{w} R).FullyFaithful :=
  (derivedEpsilonAdjunction.{w} R).fullyFaithfulROfCompIsoId
    (derivedPushforwardPullbackIso.{w} R)

/-- The functor `Rε_*` is full. -/
instance derivedEpsilonPushforward_full : (derivedEpsilonPushforward.{w} R).Full :=
  (derivedEpsilonPushforwardFullyFaithful.{w} R).full

/-- The functor `Rε_*` is faithful. -/
instance derivedEpsilonPushforward_faithful : (derivedEpsilonPushforward.{w} R).Faithful :=
  (derivedEpsilonPushforwardFullyFaithful.{w} R).faithful

/-! ### Restriction to a subcategory on which the unit is invertible -/

section Restriction

variable (P : ObjectProperty (DerivedCategory (PresheafOfModules.{max u v r w} R.obj)))

/-- The property of an object `K` of `D(C_τ, O_τ)` that `Rε_*K` satisfies a given property of
objects of `D(O)`.  For `P` the cartesian condition of tag 0GYV this is the condition cutting out
the subcategory of `D(C_τ, O_τ)` appearing in tag 0GZS. -/
abbrev pushforwardProperty : ObjectProperty (DerivedCategory (SheafOfModules.{max u v r w} R)) :=
  fun K => P ((derivedEpsilonPushforward.{w} R).obj K)

variable [P.IsClosedUnderIsomorphisms]
  (hP : ∀ M, P M → IsIso ((derivedEpsilonAdjunction.{w} R).unit.app M))

include hP in
/-- **`ε^*` lands in the subcategory cut out by `Rε_*`.**  If the unit is invertible at `M`, then
`Rε_*(ε^*M)` is isomorphic to `M` and therefore satisfies whatever isomorphism-stable property
`M` does. -/
theorem pushforwardProperty_mapDerivedCategory_obj (M : DerivedCategory
    (PresheafOfModules.{max u v r w} R.obj)) (hM : P M) :
    pushforwardProperty.{w} R P ((epsilonPullback.{w} R).mapDerivedCategory.obj M) :=
  have := hP M hM
  P.prop_of_iso (asIso ((derivedEpsilonAdjunction.{w} R).unit.app M)) hM

/-- `ε^*` as a functor from the full subcategory of `D(O)` on which the unit is invertible to the
full subcategory of `D(C_τ, O_τ)` cut out by `Rε_*`. -/
abbrev restrictedPullback :
    P.FullSubcategory ⥤ (pushforwardProperty.{w} R P).FullSubcategory :=
  (pushforwardProperty.{w} R P).lift (P.ι ⋙ (epsilonPullback.{w} R).mapDerivedCategory)
    (fun X => pushforwardProperty_mapDerivedCategory_obj.{w} R P hP X.obj X.2)

/-- `Rε_*` as a functor from the full subcategory of `D(C_τ, O_τ)` it cuts out to the given full
subcategory of `D(O)`. -/
abbrev restrictedPushforward :
    (pushforwardProperty.{w} R P).FullSubcategory ⥤ P.FullSubcategory :=
  P.lift ((pushforwardProperty.{w} R P).ι ⋙ derivedEpsilonPushforward.{w} R) (fun X => X.2)

/-- The restriction of `Rε_*` to the full subcategories is full. -/
instance restrictedPushforward_full : (restrictedPushforward.{w} R P).Full := inferInstance

/-- The restriction of `Rε_*` to the full subcategories is faithful. -/
instance restrictedPushforward_faithful : (restrictedPushforward.{w} R P).Faithful :=
  inferInstance

include hP in
/-- The restriction of `Rε_*` is essentially surjective: every `M` in the subcategory is the image
of `ε^*M`, the unit being invertible there. -/
theorem restrictedPushforward_essSurj : (restrictedPushforward.{w} R P).EssSurj where
  mem_essImage X := by
    have := hP X.obj X.2
    exact ⟨⟨(epsilonPullback.{w} R).mapDerivedCategory.obj X.obj,
        pushforwardProperty_mapDerivedCategory_obj.{w} R P hP X.obj X.2⟩,
      ⟨P.fullyFaithfulι.preimageIso
        (asIso ((derivedEpsilonAdjunction.{w} R).unit.app X.obj)).symm⟩⟩

include hP in
/-- The restriction of `Rε_*` is an equivalence: it is fully faithful because `Rε_*` is, and
essentially surjective because the unit is invertible on the subcategory. -/
theorem restrictedPushforward_isEquivalence :
    (restrictedPushforward.{w} R P).IsEquivalence :=
  let := restrictedPushforward_essSurj.{w} R P hP
  { }

/-- **`Rε_*` restricts to an equivalence** from the full subcategory of `D(C_τ, O_τ)` consisting
of the objects `K` with `Rε_*K` in a given isomorphism-stable full subcategory of `D(O)` onto that
subcategory, as soon as the unit `M ⟶ Rε_*(ε^*M)` is invertible there. -/
def restrictedEquivalence :
    (pushforwardProperty.{w} R P).FullSubcategory ≌ P.FullSubcategory :=
  letI := restrictedPushforward_isEquivalence.{w} R P hP
  (restrictedPushforward.{w} R P).asEquivalence

/-- The restrictions of `ε^*` and `Rε_*` to the two full subcategories are again adjoint: the
derived adjunction `Lε^* ⊣ Rε_*` restricted along the two fully faithful inclusions. -/
def restrictedAdjunction : restrictedPullback.{w} R P hP ⊣ restrictedPushforward.{w} R P :=
  (derivedEpsilonAdjunction.{w} R).restrictFullyFaithful (iC := P.ι)
    (iD := (pushforwardProperty.{w} R P).ι) P.fullyFaithfulι
    (pushforwardProperty.{w} R P).fullyFaithfulι (Iso.refl _) (Iso.refl _)

/-- **`ε^*` and `Rε_*` are mutually quasi-inverse equivalences** between a full subcategory of
`D(O)` stable under isomorphism on which the unit `M ⟶ Rε_*(ε^*M)` is invertible and the full
subcategory of `D(C_τ, O_τ)` of the objects `K` with `Rε_*K` in it: the restricted adjunction
`ε^* ⊣ Rε_*` is an adjoint equivalence, `Rε_*` being an equivalence there.  The functor of this
equivalence is `ε^*` and its inverse is `Rε_*`, both on the nose. -/
def pullbackPushforwardEquivalence :
    P.FullSubcategory ≌ (pushforwardProperty.{w} R P).FullSubcategory :=
  letI := restrictedPushforward_isEquivalence.{w} R P hP
  (restrictedAdjunction.{w} R P hP).toEquivalence

/-- The functor of `pullbackPushforwardEquivalence` is the restriction of `ε^*`. -/
theorem pullbackPushforwardEquivalence_functor :
    (pullbackPushforwardEquivalence.{w} R P hP).functor = restrictedPullback.{w} R P hP :=
  rfl

/-- The inverse of `pullbackPushforwardEquivalence` is the restriction of `Rε_*`. -/
theorem pullbackPushforwardEquivalence_inverse :
    (pullbackPushforwardEquivalence.{w} R P hP).inverse = restrictedPushforward.{w} R P :=
  rfl

end Restriction

/-! ### The chaotic topology -/

section Chaotic

variable (R₀ : Sheaf (⊥ : GrothendieckTopology C) RingCat.{r})
  [HasSheafify (⊥ : GrothendieckTopology C) AddCommGrpCat.{max u v r w}]
  [(⊥ : GrothendieckTopology C).WEqualsLocallyBijective AddCommGrpCat.{max u v r w}]

/-- For the chaotic topology the unit of `ε^* ⊣ ε_*` is an isomorphism: every presheaf is already
a sheaf, so sheafification does nothing. -/
instance isIso_chaoticEpsilonAdjunction_unit : IsIso (epsilonAdjunction.{w} R₀).unit := by
  have hadj : epsilonAdjunction.{w} R₀ =
      PresheafOfModules.sheafificationAdjunction (𝟙 R₀.obj) := rfl
  rw [hadj, NatTrans.isIso_iff_isIso_app]
  intro P
  rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf.{max u v r w} R₀.obj),
    PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
  exact isIso_toSheafify _ (Presheaf.isSheaf_bot P.presheaf)

/-- **Modules on the chaotic site are presheaves of modules.**  For the chaotic topology both the
unit and the counit of `ε^* ⊣ ε_*` are isomorphisms, so `ε^*` and `ε_*` are mutually inverse
equivalences.  This is the dictionary under which the chaotic side of the comparison morphism is
read as presheaves of modules. -/
def chaoticEpsilonEquivalence :
    PresheafOfModules.{max u v r w} R₀.obj ≌ SheafOfModules.{max u v r w} R₀ :=
  (epsilonAdjunction.{w} R₀).toEquivalence

end Chaotic

end Stacks.ModulesOnACategory.ChaoticComparison

end
