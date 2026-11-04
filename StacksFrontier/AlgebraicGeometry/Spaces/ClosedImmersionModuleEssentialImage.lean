module

public import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsAlongSurjection
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardEssentialImageDirect.ModuleDescent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardEssentialSurjectivity
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionAnnihilatedModuleSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionKerIdealFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModuleEssentialImageUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModulePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackGeometricFibre

/-!
# The essential image of the direct image of modules along a closed immersion

Let `i : Z ⟶ X` be a closed immersion of algebraic spaces over a scheme `S` contained in a big
fppf site `B`, and let `ℐ = ker(i♯) ⊆ 𝒪_X` be the ideal cutting out `Z`. The essential-image
clause of the space-level [Stacks, Tag 08KS] asserts that an `𝒪_X`-module is a direct image
along `i` exactly when `ℐ` annihilates it. The inclusion `essImage i_* ⊆ {𝒢 | ℐ𝒢 = 0}` is
`AlgebraicGeometry.Space.annihilatedByKerIdeal_of_essImage_modulePushforward`; this file proves
the **reverse inclusion**, so the clause is now complete.

The second half of the file keeps an earlier, purely topos-theoretic treatment of the same clause,
written for a closed immersion `f : X ⟶ Y` and conditional on a set-level input. It is retained
because it is the interface to the general theory of
`Stacks.Sheaves.PushforwardEssentialImage`, and because it packages the clause as an equivalence
of categories onto the annihilated modules — a form the unconditional results below do not
provide.

## Main definitions

* `AlgebraicGeometry.Space.modulePushforwardAnnihilated`: direct image as a functor from all
  `𝒪_X`-modules to the `𝒪_Y`-modules annihilated by `𝓘`, the lift of
  `AlgebraicGeometry.Space.modulePushforward` along
  `AlgebraicGeometry.Space.annihilatedByKerIdeal_modulePushforward`. Its restriction to the
  quasi-coherent, resp. coherent, modules is
  `AlgebraicGeometry.Space.quasicoherentModulePushforward`, resp.
  `AlgebraicGeometry.Space.coherentModulePushforward`.
* `AlgebraicGeometry.Space.isEquivalence_modulePushforwardAnnihilated_of_moduleSheafEssImage`:
  that functor is an equivalence onto the annihilated modules, granted the set-level input.

## Main results

* `AlgebraicGeometry.Space.essImage_modulePushforward_of_annihilatedByKerIdeal`: an `𝒪_X`-module
  annihilated by `ℐ` is a direct image along `i`.
* `AlgebraicGeometry.Space.essImage_modulePushforward_iff`: hence an `𝒪_X`-module is a direct
  image along `i` exactly when `ℐ` annihilates it.
* `AlgebraicGeometry.Space.isEmbedding_smallToposMorphismTypeU`: the morphism of small étale
  topoi of a closed immersion is an embedding of topoi in the sense of Stacks 08LU. This is
  unconditional.
* `AlgebraicGeometry.Space.fullyFaithfulModulePushforwardAnnihilated`: the lift above is fully
  faithful. This is unconditional.
* `AlgebraicGeometry.Space.isClosedImmersionTopoi_of_isClosedSubtopos`: the morphism of small
  étale topoi is a closed immersion of topoi as soon as its set-level essential image is a closed
  subtopos; the embedding clause is supplied.
* `AlgebraicGeometry.Space.essSurj_moduleDirectImage_of_moduleSheafEssImage` and
  `AlgebraicGeometry.Space.essSurj_moduleDirectImage_of_isClosedSubtopos`: the hypothesis `hsurj`
  of `AlgebraicGeometry.Space.essImage_modulePushforward_iff_of_essSurj`, discharged from each of
  the two set-level inputs.
* `AlgebraicGeometry.Space.essImage_modulePushforward_iff_of_moduleSheafEssImage` and
  `AlgebraicGeometry.Space.essImage_modulePushforward_iff_of_isClosedSubtopos`: the
  essential-image assertion of Stacks 04CJ, part (3), on all modules, from each of them.
* `AlgebraicGeometry.Space.essSurj_modulePushforwardAnnihilated_of_moduleSheafEssImage`: the same
  thing read as essential surjectivity of the functor above.

## The proof

Membership of the essential image of the direct image is invertibility of the unit
`η_𝒢 : 𝒢 ⟶ i_*i^*𝒢` of the adjunction of Stacks 03LU, because the direct image is fully
faithful
(`AlgebraicGeometry.Space.essImage_modulePushforward_iff_isIso_modulePullbackAdjunction_unit`).
Invertibility of a map of `𝒪_X`-modules is tested on the fibres at the geometric points of `X`,
which are a conservative family (`AlgebraicGeometry.Space.isIso_of_isIso_geometricModuleStalk`),
and the two kinds of geometric point are treated separately.

*Off the closed subspace.* Both `𝒢` and `i_*i^*𝒢` are annihilated by `ℐ` — the latter by
Stacks 04CJ, part (3) — and an `ℐ`-annihilated module has vanishing fibre at every geometric
point missing the point set of `Z`
(`AlgebraicGeometry.Space.subsingleton_sheafModuleFiber_of_annihilatedByKerIdeal_of_notMem`).
A map between two modules with at most one element is invertible.

*On the closed subspace.* A geometric point of `X` lying on `Z` comes from a geometric point `z̄`
of `Z` (`AlgebraicGeometry.Space.exists_geometricPoint_map_eq_of_mem_range`). There the counit of
the adjunction is invertible (Stacks 04CJ, part (2)), so the triangle identity makes `i^*η_𝒢`
invertible, and the functorial form of Stacks 05VQ
(`AlgebraicGeometry.Space.modulePullbackFiberIso`) turns that into invertibility of
`𝒪_{Z, z̄} ⊗_{𝒪_{X, x̄}} (η_𝒢)_{x̄}`. The homomorphism of stalk rings is surjective for a closed
immersion and its kernel annihilates the fibres of both modules
(`AlgebraicGeometry.Space.smul_eq_zero_of_mem_ker_smallEtaleStalkPullbackRingMap`), so extension
of scalars along it reflects the invertibility
(`Stacks.ModuleCat.isIso_of_isIso_extendScalars_map`): the unit is invertible on the fibre at
`x̄` itself.

## The conditional, topos-theoretic route

The declarations of the second half go through the general theory instead, replacing the
hypothesis `hsurj` of `AlgebraicGeometry.Space.essImage_modulePushforward_iff_of_essSurj` — which
*is* essential surjectivity of the Stacks 03D1 direct image on modules, so assumes what the
assertion asserts — by a strictly weaker one about sheaves of **sets**. The replacement hypothesis
comes in two grades, both purely topos-theoretic:

* the closed-subtopos clause of Stacks 08M0, part (2) for the morphism of small étale topoi of
  Stacks 03G2, part (3), that is `IsClosedSubtopos` of the essential image of its direct image on
  sheaves of sets. The embedding clause of Stacks 08M0 is *not* assumed: it is available, being
  part (1) of Stacks 04E5
  (`AlgebraicGeometry.Space.fullyFaithfulSmallEtalePushforwardOfIsClosedImmersion`), and
  `AlgebraicGeometry.Space.isEmbedding_smallToposMorphismTypeU` records it;
* weaker still, that the underlying sheaf of sets of every sheaf of `f_*𝒪_X`-modules lie in the
  essential image of the direct image on sheaves of sets. This is all the argument consumes, and
  it is what the closed-subtopos clause is spent on.

Only `AlgebraicGeometry.Space.essImage_modulePushforward_of_annihilatedByKerIdeal` and
`AlgebraicGeometry.Space.essImage_modulePushforward_iff` are tagged. Each conditional result is
conditional on an input that holds the whole geometric content of its own route, and that input is
named in the implementation notes.

## Implementation notes

**The input the conditional route still wants.** Every conditional statement below is conditional
on `IsClosedSubtopos (AlgebraicGeometry.Space.SmallEtale.topology B S hS Y.1)`
`(AlgebraicGeometry.Space.smallToposMorphismTypeU B S hS f).pushforward.essImage`, or on the
weaker set-level statement derived from it. That is the closed-subtopos clause of Stacks 08M0,
part (2), equivalently the essential-image assertion of Stacks 04E5, part (1); it is proved
nowhere in this tree. `IsClosedSubtopos` is constructed only for the Zariski site of a ringed
space, in `Stacks.ClosedSubtopos.isClosedSubtopos_essImage_pushforward`, which does not apply to
the small étale topos of an algebraic space. Discharging it needs the subterminal sheaf cut out by
the open complement `Y ∖ X` — which exists as a space,
`AlgebraicGeometry.Space.closedImmersionComplement` — together with both halves of the
identification of the closed complement of that subterminal sheaf with the essential image.

Those two halves are exactly the hypotheses `h04FX` and `h04CA` of
`AlgebraicGeometry.Space.smallEtalePushforward_essImage_iff`, which are not discharged for
sheaves of sets. The abelian analogue *is* discharged, by
`AlgebraicGeometry.Space.smallEtalePushforward_essImage_iff_abelian_of_isClosedImmersion`, so the
geometry is available for abelian sheaves; but it does not transfer, for two independent reasons.
First, it describes the essential image on sheaves of abelian groups, and the conditional
argument needs it on sheaves of sets, the underlying sheaf of a sheaf of modules carrying no
additive structure that the direct image on sets is known to respect. Second, and decisively, the
abelian statement is at `AddCommGrpCat.{u + 1}` and the conditional set-level statement at
`Type (max (u + 1) v)`, while `AlgebraicGeometry.Space.smallToposMorphismTypeU` — the morphism of
topoi the modules development consumes, and the one whose topos is the one a ringed topos in the
sense of Stacks 01D3 declares — is at `Type u`. No choice of the free universe brings either down
to `Type u`. This is why the essential-image clause is proved above by the fibrewise route
instead, which touches none of it.

**Why the target of the conditional statements is all annihilated modules.** Stacks 08AM asserts
an equivalence onto the *coherent* `𝒪_Y`-modules annihilated by `𝓘`, and
`AlgebraicGeometry.Space.coherentModulePushforward` has the annihilated modules for target
instead, its coherence being blocked as the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModulePushforward` record. Essential
surjectivity of that functor as it stands is therefore not the assertion of Stacks 08AM and is
false in general: an infinite direct sum of copies of `𝒪_Y/𝓘` is annihilated by `𝓘` and is not
the direct image of a coherent module. So no conditional statement below is about
`AlgebraicGeometry.Space.coherentModulePushforward`; they are about the lift
`AlgebraicGeometry.Space.modulePushforwardAnnihilated` on all modules, which is the assertion of
Stacks 04CJ, part (3) with the quasi-coherence of the source dropped — costing nothing, since
full faithfulness and essential surjectivity restrict to any full subcategory of the source. To
get from there to Stacks 08AM two further inputs are needed: that `f_*` of a coherent module is
coherent, which is the closed-immersion case of Stacks 07UH,
`AlgebraicGeometry.Space.isCoherent_modulePushforward_of_isFinite`; and the converse, that a
module whose direct image is coherent is itself coherent, which is stated nowhere.

**Why the set-level hypothesis is the sharper one.** The proof of
`Stacks.Sheaves.PushforwardEssentialImage.essSurj_pushforwardModuleFunctor` spends its
closed-immersion hypothesis in exactly two places: the embedding clause, to invert the ring-level
counit, and the closed-subtopos clause, through
`Stacks.Sheaves.PushforwardEssentialImage.moduleSheaf_mem_essImage_pushforward`, to put the
underlying sheaf of sets of a module over `f_*𝒪_X` in the essential image of the direct image on
sets. Here the first is available and the second is the only hypothesis, in the form
`Stacks.Sheaves.PushforwardEssentialImage.essImage_pushforwardModuleFunctor` consumes it — so
`AlgebraicGeometry.Space.essSurj_moduleDirectImage_of_moduleSheafEssImage` assumes strictly less
than `hsurj` does: the same sheaves, with their module structure forgotten.

No comparison is needed to recognise `AlgebraicGeometry.Space.structureRingSheafDirectImage` and
`AlgebraicGeometry.Space.moduleDirectImage` as the general direct images of
`Stacks.Sheaves.ToposPushforward` at `AlgebraicGeometry.Space.smallToposMorphismTypeU`: the
direct image of sheaves of sets of that morphism of topoi *is*
`AlgebraicGeometry.Space.smallEtaleDirectImage`, so the two agree by definition, as
`AlgebraicGeometry.Space.essImage_modulePushforward_iff_of_essSurj` already relies on.

## References

* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 04CJ](https://stacks.math.columbia.edu/tag/04CJ)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 05VQ](https://stacks.math.columbia.edu/tag/05VQ)
* [Stacks Project, Tag 04K5](https://stacks.math.columbia.edu/tag/04K5)
* [Stacks Project, Tag 08AM](https://stacks.math.columbia.edu/tag/08AM)
* [Stacks Project, Tag 08M0](https://stacks.math.columbia.edu/tag/08M0)
* [Stacks Project, Tag 08M3](https://stacks.math.columbia.edu/tag/08M3)
* [Stacks Project, Tag 04E5](https://stacks.math.columbia.edu/tag/04E5)
* [Stacks Project, Tag 08LU](https://stacks.math.columbia.edu/tag/08LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v₁ v₂ u₁ u₂ u

namespace Stacks

/-- **The inverse image of a unit whose counit is invertible is invertible.** For an adjunction
`L ⊣ R` and an object `A` at which the counit of the adjunction is invertible on `L.obj A`, the
map `L.map (η_A)` is invertible: the triangle identity makes it a left factor of an identity
whose right factor is invertible. -/
theorem isIso_leftAdjoint_map_unit_app {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (A : C)
    (h : IsIso (adj.counit.app (L.obj A))) : IsIso (L.map (adj.unit.app A)) := by
  have := h
  have hid : IsIso (𝟙 (L.obj A)) := inferInstance
  have hcomp : IsIso (L.map (adj.unit.app A) ≫ adj.counit.app (L.obj A)) :=
    (adj.left_triangle_components A) ▸ hid
  exact IsIso.of_isIso_comp_right _ (adj.counit.app (L.obj A))

/-- A functor carries an isomorphism to an isomorphism, with the hypothesis as an explicit
argument rather than an instance. The explicit form is what is usable when the ambient category
of the morphism is spelled differently from the source of the functor. -/
theorem isIso_functor_map {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) {A A' : C} (g : A ⟶ A') (hg : IsIso g) : IsIso (F.map g) :=
  have := hg
  inferInstance

/-- Transport of invertibility of the image of a morphism along an isomorphism of functors, with
the hypothesis as an explicit argument rather than an instance. -/
theorem isIso_map_of_natIso_of_isIso {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] {L R : C ⥤ D} (e : L ≅ R) {A A' : C} (g : A ⟶ A')
    (hg : IsIso (L.map g)) : IsIso (R.map g) := by
  have h : R.map g = e.inv.app A ≫ L.map g ≫ e.hom.app A' := by
    symm
    rw [e.hom.naturality]
    simp only [← Category.assoc, e.inv_hom_id_app, Category.id_comp]
  have := hg
  rw [h]
  infer_instance

end Stacks

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Unconditional

variable {Z X : AlgebraicSpaces B S hS}

/-- **The inverse image of the unit is invertible.** For a closed immersion `i : Z ⟶ X` of
algebraic spaces and any `𝒪_X`-module `𝒢`, the inverse image `i^*η_𝒢` of the unit of the
adjunction of Stacks 03LU is an isomorphism.

The counit is an isomorphism by Stacks 04CJ, part (2), and the triangle identity
`i^*(η_𝒢) ≫ ε_{i^*𝒢} = 𝟙` then exhibits `i^*η_𝒢` as a left factor of an isomorphism whose right
factor is one. -/
theorem isIso_modulePullback_map_modulePullbackAdjunction_unit (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) (M : Modules.{u, u} B S hS X.1 X.2) :
    IsIso ((modulePullback B S hS i).map ((modulePullbackAdjunction B S hS i).unit.app M)) :=
  Stacks.isIso_leftAdjoint_map_unit_app (modulePullbackAdjunction B S hS i) M
    (isIso_modulePullbackAdjunction_counit B S hS i hi ((modulePullback B S hS i).obj M))

/-- **The unit is invertible on the fibre at a geometric point of the closed subspace.** For a
closed immersion `i : Z ⟶ X` of algebraic spaces, an `𝒪_X`-module `𝒢` annihilated by the ideal
cutting out `Z`, and a geometric point `z̄` of `Z`, the unit of the adjunction of Stacks 03LU is
an isomorphism on the fibre at the image of `z̄`.

The inverse image of the unit is invertible, the functorial form of Stacks 05VQ identifies the
fibre of an inverse image with the base change of the fibre at the image point, and extension of
scalars along the surjective homomorphism of stalk rings reflects isomorphisms between modules
annihilated by its kernel. -/
theorem isIso_sheafModuleFiber_map_unit_of_mem_range (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : AnnihilatedByKerIdeal B S hS i M) (z : GeometricPoint B S hS Z.1) :
    IsIso ((Stacks.sheafModuleFiber
      (etaleSitePoint B S hS X.1 (geometricPointMap i.hom z) X.2)
      (structureRingSheaf B S hS X)).map ((modulePullbackAdjunction B S hS i).unit.app M)) := by
  have htgt : IsIso ((ModuleCat.extendScalars (smallEtaleStalkPullbackRingMap B S hS i z)).map
      ((Stacks.sheafModuleFiberOfCommRing
        (etaleSitePoint B S hS X.1 (geometricPointMap i.hom z) X.2)
        (smallEtaleRingedTopos B S hS X).O).map
          ((modulePullbackAdjunction B S hS i).unit.app M))) :=
    Stacks.isIso_map_of_natIso_of_isIso (modulePullbackFiberIso B S hS i z)
      ((modulePullbackAdjunction B S hS i).unit.app M)
      (Stacks.isIso_functor_map
        (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS Z.1 z Z.2)
          (smallEtaleRingedTopos B S hS Z).O)
        ((modulePullback B S hS i).map ((modulePullbackAdjunction B S hS i).unit.app M))
        (isIso_modulePullback_map_modulePullbackAdjunction_unit B S hS i hi M))
  refine isIso_sheafModuleFiber_map_of_isIso_moduleStalkFunctor_map B S hS _ _ ?_
  refine Stacks.ModuleCat.isIso_of_isIso_extendScalars_map
    (smallEtaleStalkPullbackRingMap B S hS i z)
    (surjective_smallEtaleStalkPullbackRingMap_of_isClosedImmersion B S hS i z hi) _
    (fun a ha m ↦ smul_eq_zero_of_mem_ker_smallEtaleStalkPullbackRingMap B S hS i hi z M hM
      a ha m)
    (fun a ha n ↦ smul_eq_zero_of_mem_ker_smallEtaleStalkPullbackRingMap B S hS i hi z
      ((modulePushforward B S hS i).obj ((modulePullback B S hS i).obj M))
      (annihilatedByKerIdeal_modulePushforward B S hS i ((modulePullback B S hS i).obj M))
      a ha n) htgt

/-- The missing inclusion of the essential-image clause of Stacks 08KS for algebraic spaces.
For a closed immersion `i : Z ⟶ X` of algebraic spaces over `S`, every `𝒪_X`-module annihilated
by the ideal `ℐ = ker(i♯)` cutting out `Z` is isomorphic to a direct image along `i`.

The tag is carried by the next statement, which assembles this with the other inclusion into the
clause whole. -/
theorem essImage_modulePushforward_of_annihilatedByKerIdeal (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : AnnihilatedByKerIdeal B S hS i M) :
    (modulePushforward B S hS i).essImage M := by
  refine (essImage_modulePushforward_iff_isIso_modulePullbackAdjunction_unit B S hS i hi M).2 ?_
  refine isIso_of_isIso_geometricModuleStalk B S hS X.1 X.2 (structureRingSheaf B S hS X)
    ((modulePullbackAdjunction B S hS i).unit.app M) fun x ↦ ?_
  by_cases hx : x.image ∈ Set.range (pointsMap B S hS Z.1 i.hom)
  · obtain ⟨z, rfl⟩ := exists_geometricPoint_map_eq_of_mem_range B S hS i hi x hx
    exact isIso_sheafModuleFiber_map_unit_of_mem_range B S hS i hi M hM z
  · exact Stacks.isIso_of_subsingleton
      (subsingleton_sheafModuleFiber_of_annihilatedByKerIdeal_of_notMem B S hS i hi M hM x hx)
      (subsingleton_sheafModuleFiber_of_annihilatedByKerIdeal_of_notMem B S hS i hi
        ((modulePushforward B S hS i).obj ((modulePullback B S hS i).obj M))
        (annihilatedByKerIdeal_modulePushforward B S hS i ((modulePullback B S hS i).obj M))
        x hx) _

/-- **The essential-image clause of Stacks 08KS for algebraic spaces.** For a closed immersion
`i : Z ⟶ X` of algebraic spaces over `S`, an `𝒪_X`-module is isomorphic to a direct image along
`i` exactly when the ideal `ℐ = ker(i♯)` cutting out `Z` annihilates it.

This is the one statement carrying the tag for the essential-image clause on the algebraic-space
substrate: it states the clause as the source does, so neither inclusion does. The forward one is
`AlgebraicGeometry.Space.essImage_modulePushforward_le_annihilatedByKerIdeal` of
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionModulePushforwardExactness.lean`, in its
containment form, and the reverse one is the previous statement. -/
@[stacks 08KS "essential image of the direct image: exactly the annihilated modules"]
theorem essImage_modulePushforward_iff (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom)
    (M : Modules.{u, u} B S hS X.1 X.2) :
    (modulePushforward B S hS i).essImage M ↔ AnnihilatedByKerIdeal B S hS i M :=
  ⟨annihilatedByKerIdeal_of_essImage_modulePushforward B S hS i,
    essImage_modulePushforward_of_annihilatedByKerIdeal B S hS i hi M⟩

end Unconditional

section Conditional

variable {X Y : AlgebraicSpaces B S hS}

/-! ### The embedding clause, and the lift to the annihilated modules -/

/-- **Stacks 08LU for the morphism of small étale topoi of a closed immersion.** The morphism of
topoi of Stacks 03G2, part (3) attached to a closed immersion `f : X ⟶ Y` of algebraic spaces is
an embedding of topoi: its direct image on sheaves of sets is fully faithful.

This is part (1) of Stacks 04E5,
`AlgebraicGeometry.Space.fullyFaithfulSmallEtalePushforwardOfIsClosedImmersion`, read as the
first clause of the definition of a closed immersion of topoi. The tag `04E5` is carried there
and the tag `08LU` by the definition itself, so none is carried here. -/
theorem isEmbedding_smallToposMorphismTypeU (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom) :
    (smallToposMorphismTypeU B S hS f).IsEmbedding :=
  ⟨(fullyFaithfulSmallEtalePushforwardOfIsClosedImmersion B S hS f hf).full,
    (fullyFaithfulSmallEtalePushforwardOfIsClosedImmersion B S hS f hf).faithful⟩

/-- Direct image as a functor `Mod(𝒪_X) ⥤ {𝓕 ∈ Mod(𝒪_Y) | 𝓘𝓕 = 0}`, the lift of
`AlgebraicGeometry.Space.modulePushforward` along
`AlgebraicGeometry.Space.annihilatedByKerIdeal_modulePushforward`.

This is the functor whose essential surjectivity is the essential-image assertion of Stacks 04CJ,
part (3). `AlgebraicGeometry.Space.quasicoherentModulePushforward` and
`AlgebraicGeometry.Space.coherentModulePushforward` are its restrictions to the quasi-coherent,
resp. coherent, modules; the source's quasi-coherence hypothesis is not needed for either half of
the equivalence, which is why it is dropped here. -/
def modulePushforwardAnnihilated (f : X ⟶ Y) :
    Modules.{u, u} B S hS X.1 X.2 ⥤ (annihilatedByKerIdeal B S hS f).FullSubcategory :=
  (annihilatedByKerIdeal B S hS f).lift (modulePushforward B S hS f)
    fun M ↦ annihilatedByKerIdeal_modulePushforward B S hS f M

/-- Composing `AlgebraicGeometry.Space.modulePushforwardAnnihilated` with the inclusion of the
annihilated modules is direct image. This holds by definition: the functor *is* that lift. -/
def modulePushforwardAnnihilatedCompIso (f : X ⟶ Y) :
    modulePushforwardAnnihilated B S hS f ⋙
        ObjectProperty.ι (annihilatedByKerIdeal B S hS f) ≅
      modulePushforward B S hS f :=
  Iso.refl _

/-- **Stacks 04CJ, part (3), the full-faithfulness assertion with the source unrestricted.**
Direct image along a closed immersion of algebraic spaces is fully faithful as a functor from all
`𝒪_X`-modules to the `𝒪_Y`-modules annihilated by the ideal cutting out `X`.

It is fully faithful into all `𝒪_Y`-modules by
`AlgebraicGeometry.Space.fullyFaithfulModulePushforward`, and a full subcategory inclusion is
fully faithful. The tag is carried by
`AlgebraicGeometry.Space.fullyFaithfulQuasicoherentModulePushforward`, of which this is the
restriction-free form. -/
def fullyFaithfulModulePushforwardAnnihilated (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom) :
    (modulePushforwardAnnihilated B S hS f).FullyFaithful :=
  have := (fullyFaithfulModulePushforward B S hS f hf).full
  have := (fullyFaithfulModulePushforward B S hS f hf).faithful
  have : (modulePushforwardAnnihilated B S hS f).Faithful :=
    Functor.Faithful.of_comp_iso (modulePushforwardAnnihilatedCompIso B S hS f)
  have : (modulePushforwardAnnihilated B S hS f).Full :=
    Functor.Full.of_comp_faithful_iso (modulePushforwardAnnihilatedCompIso B S hS f)
  Functor.FullyFaithful.ofFullyFaithful _

/-! ### The essential image, from the set-level input -/

/-- **The hypothesis `hsurj` of
`AlgebraicGeometry.Space.essImage_modulePushforward_iff_of_essSurj`, from sheaves of sets.** If
the underlying sheaf of sets of every sheaf of `f_*𝒪_X`-modules lies in the essential image of
the direct image on sheaves of sets, then the Stacks 03D1 direct image of modules
`Mod(𝒪_X) ⥤ Mod(f_*𝒪_X)` is essentially surjective.

This is
`Stacks.Sheaves.PushforwardEssentialImage.essImage_pushforwardModuleFunctor`, whose two instance
hypotheses are full faithfulness of the direct image on sheaves of sets, available from
`AlgebraicGeometry.Space.isEmbedding_smallToposMorphismTypeU`. The hypothesis assumes strictly
less than its conclusion: the same sheaves, with their module structure forgotten. -/
theorem essSurj_moduleDirectImage_of_moduleSheafEssImage (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom)
    (hsets : ∀ M : SheafOfModules.{u} (structureRingSheafDirectImage B S hS f),
      (smallToposMorphismTypeU B S hS f).pushforward.essImage
        (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheafDirectImage B S hS f) M))
    (M : SheafOfModules.{u} (structureRingSheafDirectImage B S hS f)) :
    (moduleDirectImage B S hS f).essImage M :=
  have := (isEmbedding_smallToposMorphismTypeU B S hS f hf).full
  have := (isEmbedding_smallToposMorphismTypeU B S hS f hf).faithful
  Stacks.Sheaves.PushforwardEssentialImage.essImage_pushforwardModuleFunctor
    (f := smallToposMorphismTypeU B S hS f) (O := structureRingSheaf B S hS X) M (hsets M)

/-- **The essential-image assertion of Stacks 04CJ, part (3) on all modules, from sheaves of
sets.** An `𝒪_Y`-module is a direct image along the closed immersion `f` exactly when the ideal
cutting out `X` annihilates it — provided the underlying sheaf of sets of every sheaf of
`f_*𝒪_X`-modules is a direct image of sheaves of sets.

The forward implication is unconditional, being
`AlgebraicGeometry.Space.annihilatedByKerIdeal_of_essImage_modulePushforward`; `hsets` holds the
whole content of the converse, so **no tag is carried here.** For the same statement with no
hypothesis beyond the closed immersion, proved by the fibrewise route rather than through the
topos theory, see `AlgebraicGeometry.Space.essImage_modulePushforward_iff` above. -/
theorem essImage_modulePushforward_iff_of_moduleSheafEssImage (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom)
    (hsets : ∀ M : SheafOfModules.{u} (structureRingSheafDirectImage B S hS f),
      (smallToposMorphismTypeU B S hS f).pushforward.essImage
        (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheafDirectImage B S hS f) M))
    (G : Modules.{u, u} B S hS Y.1 Y.2) :
    (modulePushforward B S hS f).essImage G ↔ AnnihilatedByKerIdeal B S hS f G :=
  essImage_modulePushforward_iff_of_essSurj B S hS f hf
    (essSurj_moduleDirectImage_of_moduleSheafEssImage B S hS f hf hsets) G

/-- **Essential surjectivity of the direct image onto the annihilated modules, from sheaves of
sets.** Granted `hsets`, every `𝒪_Y`-module annihilated by the ideal cutting out `X` is a direct
image along `f`, that is, `AlgebraicGeometry.Space.modulePushforwardAnnihilated` is essentially
surjective.

Membership of the essential image of the lift is membership of the essential image of direct
image itself, the lift being a lift along a full subcategory inclusion; the latter is
`AlgebraicGeometry.Space.essImage_modulePushforward_iff_of_moduleSheafEssImage`. -/
theorem essSurj_modulePushforwardAnnihilated_of_moduleSheafEssImage (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom)
    (hsets : ∀ M : SheafOfModules.{u} (structureRingSheafDirectImage B S hS f),
      (smallToposMorphismTypeU B S hS f).pushforward.essImage
        (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheafDirectImage B S hS f) M)) :
    (modulePushforwardAnnihilated B S hS f).EssSurj where
  mem_essImage G := by
    obtain ⟨M, ⟨e⟩⟩ := (essImage_modulePushforward_iff_of_moduleSheafEssImage B S hS f hf hsets
      G.obj).2 G.property
    exact ⟨M, ⟨ObjectProperty.isoMk _ e⟩⟩

/-- **Stacks 04CJ, part (3) as an equivalence, granted `hsets`.** Direct image along a closed
immersion of algebraic spaces is an equivalence from all `𝒪_X`-modules onto the `𝒪_Y`-modules
annihilated by the ideal cutting out `X`.

Full faithfulness is unconditional
(`AlgebraicGeometry.Space.fullyFaithfulModulePushforwardAnnihilated`) and essential surjectivity
is `AlgebraicGeometry.Space.essSurj_modulePushforwardAnnihilated_of_moduleSheafEssImage`. This is
the shape in which Stacks 08BC consumes Stacks 08AM, with the coherence of both sides still
missing; **no tag is carried.** -/
theorem isEquivalence_modulePushforwardAnnihilated_of_moduleSheafEssImage (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom)
    (hsets : ∀ M : SheafOfModules.{u} (structureRingSheafDirectImage B S hS f),
      (smallToposMorphismTypeU B S hS f).pushforward.essImage
        (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheafDirectImage B S hS f) M)) :
    (modulePushforwardAnnihilated B S hS f).IsEquivalence :=
  have := (fullyFaithfulModulePushforwardAnnihilated B S hS f hf).full
  have := (fullyFaithfulModulePushforwardAnnihilated B S hS f hf).faithful
  have := essSurj_modulePushforwardAnnihilated_of_moduleSheafEssImage B S hS f hf hsets
  Functor.IsEquivalence.mk

/-! ### The essential image, from the closed-subtopos clause of Stacks 08M0 -/

/-- **Stacks 08M0, part (2) for the morphism of small étale topoi, granted its closed-subtopos
clause.** The morphism of topoi of Stacks 03G2, part (3) attached to a closed immersion of
algebraic spaces is a closed immersion of topoi as soon as the essential image of its direct
image on sheaves of sets is a closed subtopos.

Only the closed-subtopos clause is assumed: the embedding clause is part (1) of Stacks 04E5, by
`AlgebraicGeometry.Space.isEmbedding_smallToposMorphismTypeU`. The hypothesis `hcl` is the input
this topos-theoretic route is missing; see the implementation notes. -/
theorem isClosedImmersionTopoi_of_isClosedSubtopos (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom)
    (hcl : IsClosedSubtopos (SmallEtale.topology B S hS Y.1)
      (smallToposMorphismTypeU B S hS f).pushforward.essImage) :
    MorphismOfTopoi.IsClosedImmersion (smallToposMorphismTypeU B S hS f) :=
  ⟨isEmbedding_smallToposMorphismTypeU B S hS f hf, hcl⟩

/-- **The hypothesis `hsurj` of
`AlgebraicGeometry.Space.essImage_modulePushforward_iff_of_essSurj`, from the closed-subtopos
clause.** If the essential image of the direct image on sheaves of sets is a closed subtopos, the
Stacks 03D1 direct image of modules `Mod(𝒪_X) ⥤ Mod(f_*𝒪_X)` is essentially surjective.

This is `Stacks.Sheaves.PushforwardEssentialImage.essSurj_pushforwardModuleFunctor`, the
closed-immersion hypothesis of which is assembled by
`AlgebraicGeometry.Space.isClosedImmersionTopoi_of_isClosedSubtopos`. The route through
`AlgebraicGeometry.Space.essSurj_moduleDirectImage_of_moduleSheafEssImage` assumes less; this one
is the form in which the general theory states the input. -/
theorem essSurj_moduleDirectImage_of_isClosedSubtopos (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom)
    (hcl : IsClosedSubtopos (SmallEtale.topology B S hS Y.1)
      (smallToposMorphismTypeU B S hS f).pushforward.essImage)
    (M : SheafOfModules.{u} (structureRingSheafDirectImage B S hS f)) :
    (moduleDirectImage B S hS f).essImage M :=
  Stacks.Sheaves.PushforwardEssentialImage.essSurj_pushforwardModuleFunctor
    (smallToposMorphismTypeU B S hS f) (structureRingSheaf B S hS X)
    (isClosedImmersionTopoi_of_isClosedSubtopos B S hS f hf hcl) M

/-- **The essential-image assertion of Stacks 04CJ, part (3) on all modules, from the
closed-subtopos clause.** An `𝒪_Y`-module is a direct image along the closed immersion `f` exactly
when the ideal cutting out `X` annihilates it — provided the essential image of the direct image
on sheaves of sets is a closed subtopos.

`hcl` holds the whole remaining content of this route, so **no tag is carried here**; it is the
input named in the implementation notes. For the same statement with no hypothesis beyond the
closed immersion, proved by the fibrewise route, see
`AlgebraicGeometry.Space.essImage_modulePushforward_iff` above. -/
theorem essImage_modulePushforward_iff_of_isClosedSubtopos (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom)
    (hcl : IsClosedSubtopos (SmallEtale.topology B S hS Y.1)
      (smallToposMorphismTypeU B S hS f).pushforward.essImage)
    (G : Modules.{u, u} B S hS Y.1 Y.2) :
    (modulePushforward B S hS f).essImage G ↔ AnnihilatedByKerIdeal B S hS f G :=
  essImage_modulePushforward_iff_of_essSurj B S hS f hf
    (essSurj_moduleDirectImage_of_isClosedSubtopos B S hS f hf hcl) G

/-- **The set-level input, from the closed-subtopos clause.** If the essential image of the direct
image on sheaves of sets is a closed subtopos, the underlying sheaf of sets of every sheaf of
`f_*𝒪_X`-modules lies in it.

This is `Stacks.Sheaves.PushforwardEssentialImage.moduleSheaf_mem_essImage_pushforward`, which
uses the closed-subtopos clause alone, and it is what makes the hypothesis of
`AlgebraicGeometry.Space.essSurj_moduleDirectImage_of_moduleSheafEssImage` the weaker of the
two. -/
theorem moduleSheafEssImage_of_isClosedSubtopos (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom)
    (hcl : IsClosedSubtopos (SmallEtale.topology B S hS Y.1)
      (smallToposMorphismTypeU B S hS f).pushforward.essImage)
    (M : SheafOfModules.{u} (structureRingSheafDirectImage B S hS f)) :
    (smallToposMorphismTypeU B S hS f).pushforward.essImage
      (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheafDirectImage B S hS f) M) :=
  Stacks.Sheaves.PushforwardEssentialImage.moduleSheaf_mem_essImage_pushforward
    (isClosedImmersionTopoi_of_isClosedSubtopos B S hS f hf hcl) M

end Conditional

end AlgebraicGeometry.Space

end
