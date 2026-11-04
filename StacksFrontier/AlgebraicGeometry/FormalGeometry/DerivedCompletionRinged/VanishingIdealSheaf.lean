module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.Products
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BaseRingLinear
public import StacksFrontier.Homology.DerivedComplete.CompleteIdeal

/-!
# The sheaf of ideals of derived completeness

Let `(𝒞, 𝒪)` be a ringed site and let `K ∈ D(𝒪)`. [Stacks, Tag 0998] asserts that the rule
sending an object `U` of `𝒞` to the set of sections `f ∈ 𝒪(U)` with `T(K|_U, f) = 0` is a sheaf
of ideals in `𝒪`. This file proves that the value at each object is an ideal.

## Main definitions

* `AlgebraicGeometry.RingedSite.IsDerivedCompleteAtSection`: the condition `T(K|_U, f) = 0` on
  a section `f` of `𝒪` over `U`, which is the condition the predicate of [Stacks, Tag 0999]
  tests at the local sections of a sheaf of ideals.
* `AlgebraicGeometry.RingedSite.derivedCompleteIdealAt`: the ideal of `𝒪(U)` of sections
  satisfying that condition.

## Main results

* `AlgebraicGeometry.RingedSite.mem_derivedCompleteIdealAt_iff`: membership in
  `derivedCompleteIdealAt` is the condition `T(K|_U, f) = 0`; so the condition is closed under
  addition and under multiplication by an arbitrary section of `𝒪(U)`.
* `AlgebraicGeometry.RingedSite.isDerivedComplete_iff_forall_isDerivedCompleteAtSection`: the
  predicate of [Stacks, Tag 0999] is the sectionwise condition at every local section of the
  sheaf of ideals.

## Implementation notes

The condition `T(K|_U, f) = 0` is expressed, as in [Stacks, Tag 0999], by the invertibility of
the Milnor difference `1 - f·shift` on the countable product of copies of `K|_U` in the derived
category of sheaves of modules on the slice site at `U`, with `f` acting through multiplication
by a section over the terminal object `U ⟶ U` of that site. Tag 0999's predicate
`AlgebraicGeometry.RingedSite.IsDerivedComplete` carries the four class-valued side conditions
— additivity and exactness of restriction to the slice site, and countable products in the
derived category there — as explicit existentials; all four are proved
(`Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits`,
`Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits` and
`AlgebraicGeometry.RingedSite.hasProductsOfShape_nat_derivedCategory_over`), so the sectionwise
condition here installs them instead of quantifying over them. All four are propositions, so the
two spellings agree, which is what
`isDerivedComplete_iff_forall_isDerivedCompleteAtSection` records.

That the condition is an ideal in `f` is the purely algebraic
`derivedCompleteIdeal` of `StacksFrontier/Homology/DerivedComplete/CompleteIdeal.lean`, pulled back
along the ring map `Stacks.SheafOfModules.terminalSectionRingHom` which sends a section of `𝒪`
over `U` to multiplication by it. In particular neither the closure under addition nor the
closure under multiplication needs the exact sequence
`0 → 𝒪_{f+g} → 𝒪_{f(f+g)} ⊕ 𝒪_{g(f+g)} → 𝒪_{gf(f+g)} → 0` of the source's proof, nor
[Stacks, Tag 0997].

### Where Tag 0998 is completed

The sheaf of ideals itself is not constructed here, and no `@[stacks 0998]` attribute is
attached below. Two inputs are needed beyond the objectwise statement, both comparing the
condition over `U` with the condition over `V` for a morphism `a : V ⟶ U` of the site, and both
are proved, for a `RingedSite.{u, u, u}`:

1. **Restriction stability**, that is `T(K|_U, f) = 0 → T(K|_V, f|_V) = 0`, which is what makes
   the ideals `derivedCompleteIdealAt` into a subpresheaf of `𝒪`. This is
   `AlgebraicGeometry.RingedSite.IsDerivedCompleteAtSection.restrict` of
   `VanishingIdealSheafRestriction.lean`; `derivedCompleteIdealAt_le_comap` there is the same
   statement read as an inclusion of ideals.
2. **The sheaf condition**, that is locality of `T(K|_U, f) = 0` in `U`, whose verification the
   source omits. This is `AlgebraicGeometry.RingedSite.IsDerivedCompleteAtSection.of_sieve` of
   `VanishingIdealSheafCondition.lean`, and the sheaf of ideals assembled from the two is
   `AlgebraicGeometry.RingedSite.derivedCompleteIdealSheaf` there, which carries the unscoped
   `@[stacks 0998]`.

Restriction stability rests on one statement,
`Stacks.Cohomology.Localization.preservesProducts_mapDerivedCategory_overMap` of
`StacksFrontier/CategoryTheory/Sites/Cohomology/Localization/RestrictionDerivedProducts.lean`:
the functor of derived categories induced by the restriction `SheafOfModules.overMap 𝒪 a`
between two slice sites preserves countable products. That is what the product hypothesis of
`isDerivedCompleteAt_map_of_center` and of
`AlgebraicGeometry.RingedSite.isDerivedCompleteAt_map_of_smul_id` asks for. It is proved from
the AB4*-free `CategoryTheory.Functor.preservesProducts_mapDerivedCategory_of_isKInjective` of
`StacksFrontier/Homology/DerivedCategory/KInjectiveProductsFunctor.lean`, whose three inputs for
the restriction are: that it preserves countable products of sheaves of modules, being a right
adjoint (`SheafOfModules.pullbackPushforwardAdjunction`, with
`PresheafOfModules.isRightAdjoint_pushforward_of_univLE` supplied by name, instance search not
finding it for the `overMap` spelling); that it carries K-injective complexes to K-injective
complexes (`Stacks.Cohomology.Localization.isKInjective_overMap`, [Stacks, Tag 08FI]); and that
a termwise product of K-injective complexes computes the product in the derived category
(`Stacks.InverseSystem.isIso_piComparison_Q_of_isKInjective`, [Stacks, Tag 0BK6]).
`Stacks.Cohomology.Localization.preservesProducts_mapDerivedCategory_overFunctor` is the same
statement for the restriction `SheafOfModules.overFunctor` from the site itself.

The sheaf condition needs the reflection of isomorphisms in `D(𝒪_U)` along the covering, which
is `Stacks.SheafOfModules.isIso_of_coversTop_mapDerivedCategory` of
`StacksFrontier/CategoryTheory/Sites/Cohomology/Slice/DerivedIsomorphismLocality.lean`
([Stacks, Tag 08JJ], its locality step) says that a morphism of `D(Mod(R))` is an isomorphism as
soon as its restriction to the slice over each member of a family covering the *final* object is
one — which is the right shape here, because a covering sieve of `U` in `𝒞` is a family covering
the final object `Over.mk (𝟙 U)` of `𝒞/U`. The other half, that the restriction to a slice
preserves the countable power in the derived category, is what the note of
`StacksFrontier/AlgebraicGeometry/FormalGeometry/DerivedCompletionRinged/Pushforward.lean` records
as the missing input of the locality of the Milnor condition, and it is the statement proved
above.

The assembly of those two into the sheaf condition is
`AlgebraicGeometry.RingedSite.IsDerivedCompleteAtSection.of_sieve`: the per-section form of the
core of `AlgebraicGeometry.RingedSite.restrict_isDerivedComplete`, which carries
`T(K|_V, f|_V) = 0` across `CategoryTheory.Over.iteratedSliceEquiv` to the condition on
`(𝒞/U)/W` for `W` the object `Over.mk a` of `𝒞/U`; the covering family of the final object of
`𝒞/U` built from a covering sieve of `U`
(`CategoryTheory.GrothendieckTopology.coversTop_over_of_mem`); and the packaging of the result,
with the restriction stability above, as a `SheafOfModules.Submodule (SheafOfModules.unit 𝒪)`.

The reverse inclusion of [Stacks, Tag 099C] is thereby unblocked: the note in
`StacksFrontier/AlgebraicGeometry/FormalGeometry/DerivedCompletionRinged/RestrictScalars.lean`
reduces it to Tag 0998, and the reduction runs through
`AlgebraicGeometry.RingedSite.extendIdeal_le`, which consumes a *sheaf* of ideals — the
objectwise `derivedCompleteIdealAt` below, even with its restriction stability, is not enough
for it, but `AlgebraicGeometry.RingedSite.derivedCompleteIdealSheaf` is. That inclusion is still
not proved.

## References

* [Stacks Project, Tag 0998](https://stacks.math.columbia.edu/tag/0998)
* [Stacks Project, Tag 0999](https://stacks.math.columbia.edu/tag/0999)
* [Stacks Project, Tag 08FI](https://stacks.math.columbia.edu/tag/08FI)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
* [Stacks Project, Tag 0BK6](https://stacks.math.columbia.edu/tag/0BK6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped IsMulCommutative

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, v, max u v})

section Slice

variable (U : X.C)

/-- The rings of sections of the structure sheaf of a slice site are commutative, being rings of
sections of the structure sheaf of the ringed site. -/
theorem isMulCommutative_over (W : (Over U)ᵒᵖ) :
    IsMulCommutative ((((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U).obj.obj W) :=
  inferInstanceAs (IsMulCommutative (X.O.obj.obj (op W.unop.left)))

attribute [local instance] isMulCommutative_over

/-- The sheaves of modules on the slice site at `U` form a category linear over the centre of
itself, by the tautological ring map. -/
@[instance_reducible]
def overCatCenterLinear :
    Linear
      (CatCenter
        (SheafOfModules.{max u v} (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U)))
      (SheafOfModules.{max u v} (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U)) :=
  Linear.ofRingMorphism (RingHom.id _)

/-- Restriction of sheaves of modules to the slice site at `U` preserves finite limits. -/
theorem overFunctor_preservesFiniteLimits :
    PreservesFiniteLimits
      (SheafOfModules.overFunctor.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U) :=
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits U

/-- Restriction of sheaves of modules to the slice site at `U` preserves finite colimits. -/
theorem overFunctor_preservesFiniteColimits :
    PreservesFiniteColimits
      (SheafOfModules.overFunctor.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U) :=
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits U

attribute [local instance] overCatCenterLinear overFunctor_preservesFiniteLimits
  overFunctor_preservesFiniteColimits hasProductsOfShape_nat_derivedCategory_over

/-- Multiplication by a section of `𝒪` over `U` on the sheaves of modules of the slice site at
`U`, as a ring map into the centre of that category: the section is read as a section over the
terminal object `U ⟶ U` of the slice site. -/
def overTerminalRingHom :
    ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj.obj (op U) →+*
      CatCenter
        (SheafOfModules.{max u v} (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U)) :=
  Stacks.SheafOfModules.terminalSectionRingHom
    (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U) (Over.mk (𝟙 U)) Over.mkIdTerminal

/-- `overTerminalRingHom X U f` is the endomorphism of the identity functor given by
multiplication by `f`, read as a section over the terminal object `U ⟶ U` of the slice site. -/
@[simp]
theorem overTerminalRingHom_apply
    (f : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj.obj (op U)) :
    overTerminalRingHom X U f =
      Stacks.SheafOfModules.terminalSectionToEnd
        (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U) (Over.mk (𝟙 U))
        Over.mkIdTerminal f :=
  rfl

end Slice

section Section

attribute [local instance] isMulCommutative_over overCatCenterLinear
  overFunctor_preservesFiniteLimits overFunctor_preservesFiniteColimits
  hasProductsOfShape_nat_derivedCategory_over

variable
  (K : DerivedCategory (SheafOfModules.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
  (U : X.C)

/-- **The condition `T(K|_U, f) = 0`** on a section `f` of `𝒪` over `U`: the restriction of `K`
to the slice site at `U` is derived complete at `f`, in the sense that the Milnor difference
`1 - f·shift` is invertible on the countable product of copies of `K|_U` in `D(𝒪_U)`. This is
the membership condition of the sheaf of ideals of [Stacks, Tag 0998], and the condition the
predicate of [Stacks, Tag 0999] tests at the local sections of a sheaf of ideals. -/
def IsDerivedCompleteAtSection
    (f : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj.obj (op U)) : Prop :=
  IsDerivedCompleteAt
    ((SheafOfModules.overFunctor.{max u v}
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapDerivedCategory.obj K)
    (overTerminalRingHom X U f)

/-- **The ideal of sections of `𝒪` over `U` with `T(K|_U, f) = 0`.** This is the value at `U` of
the sheaf of ideals of [Stacks, Tag 0998]; that the value *is* an ideal is the purely algebraic
`derivedCompleteIdeal`, pulled back along multiplication by a section. -/
def derivedCompleteIdealAt :
    Ideal (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj.obj (op U)) :=
  (derivedCompleteIdeal
      ((SheafOfModules.overFunctor.{max u v}
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapDerivedCategory.obj K)).comap
    (overTerminalRingHom X U)

/-- Membership in `derivedCompleteIdealAt` is the condition `T(K|_U, f) = 0`. -/
@[simp]
theorem mem_derivedCompleteIdealAt_iff
    (f : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj.obj (op U)) :
    f ∈ derivedCompleteIdealAt X K U ↔ IsDerivedCompleteAtSection X K U f :=
  mem_derivedCompleteIdeal_iff

/-- **`T(K|_U, -) = 0` is closed under addition.** -/
theorem IsDerivedCompleteAtSection.add
    {f g : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj.obj (op U)}
    (hf : IsDerivedCompleteAtSection X K U f) (hg : IsDerivedCompleteAtSection X K U g) :
    IsDerivedCompleteAtSection X K U (f + g) := by
  rw [← mem_derivedCompleteIdealAt_iff] at hf hg ⊢
  exact Ideal.add_mem _ hf hg

/-- **`T(K|_U, -) = 0` is closed under multiplication** by an arbitrary section of `𝒪` over
`U`. This is the first half of the proof of [Stacks, Tag 0998], obtained with no appeal to
[Stacks, Tag 0997]. -/
theorem IsDerivedCompleteAtSection.mul_left
    (g : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj.obj (op U))
    {f : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj.obj (op U)}
    (hf : IsDerivedCompleteAtSection X K U f) :
    IsDerivedCompleteAtSection X K U (g * f) := by
  rw [← mem_derivedCompleteIdealAt_iff] at hf ⊢
  exact Ideal.mul_mem_left _ g hf

/-- `T(K|_U, 0) = 0`. -/
theorem IsDerivedCompleteAtSection.zero : IsDerivedCompleteAtSection X K U 0 := by
  rw [← mem_derivedCompleteIdealAt_iff]
  exact Ideal.zero_mem _

end Section

section Compare

attribute [local instance] isMulCommutative_over overCatCenterLinear
  overFunctor_preservesFiniteLimits overFunctor_preservesFiniteColimits
  hasProductsOfShape_nat_derivedCategory_over

variable
  (K : DerivedCategory (SheafOfModules.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))

/-- **The predicate of [Stacks, Tag 0999] is the sectionwise condition `T(K|_U, f) = 0` at every
local section `f` of the sheaf of ideals.** The predicate quantifies over witnesses of the four
class-valued side conditions; all four are propositions and all four are proved, so the two
spellings agree. -/
theorem isDerivedComplete_iff_forall_isDerivedCompleteAtSection
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) :
    IsDerivedComplete.{u, v, max u v, max u v} X I K ↔
      ∀ (U : X.C) (f : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj.obj (op U)),
        f ∈ I.toSubmodule.obj (op U) → IsDerivedCompleteAtSection X K U f := by
  refine ⟨fun h U f hf => ?_, fun h U f hf => ⟨inferInstance,
    overFunctor_preservesFiniteLimits X U, overFunctor_preservesFiniteColimits X U,
    hasProductsOfShape_nat_derivedCategory_over.{u, v, max u v} X U, h U f hf⟩⟩
  obtain ⟨_, _, _, _, hc⟩ := h U f hf
  exact hc

end Compare

end AlgebraicGeometry.RingedSite

end
