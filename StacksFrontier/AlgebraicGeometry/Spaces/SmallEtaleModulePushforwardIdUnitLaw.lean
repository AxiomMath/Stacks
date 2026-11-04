module

public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsIdComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardIdIso
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardUnitLaws
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleBaseChangeUnitors

/-!
# The unit law of Stacks 03LU for the direct image, at a pair of identities

Stacks 03LU attaches to a morphism `f : X ⟶ Y` of algebraic spaces the direct image `f_*` of
`𝒪`-modules and the comparison `AlgebraicGeometry.Space.modulePushforwardCompIso` of
`f_* ∘ g_*` with `(f ≫ g)_*`, and to an identity the identification
`AlgebraicGeometry.Space.modulePushforwardIdIso` of `(𝟙 X)_*` with the identity functor.  This
file proves the compatibility of those two data at a pair of identities:

  `(𝟙 X)_* ∘ (𝟙 X)_* ≅ (𝟙 X)_*` at a module `M` is the direct image along `𝟙 X` of
  `(𝟙 X)_* ≅ 𝟭` at `M`.

`AlgebraicGeometry.Space.modulePushforwardCoherenceOfIdIso` does not supply it:  it takes for
the `idIso` field of `AlgebraicGeometry.Space.ModulePushforwardCoherence` the *normalisation*
`CategoryTheory.Functor.idIsoOfCompIso` of a given isomorphism `(𝟙 X)_* ≅ 𝟭` against the
comparison at `(𝟙 X, 𝟙 X)`, and that normalisation is exactly the device by which it obtains
both unit laws from the associativity coherence alone, with no compatibility asked of the input.
So the pseudofunctoriality data of 03LU holds for an isomorphism that need not be the one
carrying the tag, and the two agree precisely when the statement above does.
`AlgebraicGeometry.Space.idIsoOfCompIso_modulePushforwardIdIso_eq` is that agreement.

## The reduction

The direct image of `𝒪`-modules is the direct image of sheaves of sets with scalars restricted
along `AlgebraicGeometry.Space.structureSharp`, and both comparisons of 03LU are built from
their sheaf-of-sets counterparts:
`AlgebraicGeometry.Space.modulePushforwardCompIso` from the comparison
`AlgebraicGeometry.Space.smallToposMorphismTypeU_comp` of Stacks 03G2, part (3), and
`AlgebraicGeometry.Space.modulePushforwardIdIso` from
`AlgebraicGeometry.Space.smallEtaleDirectImageIdIso`.  A morphism of sheaves of modules is
determined by the underlying morphism of sheaves of sets
(`Stacks.Sheaves.RingedToposModules.hom_ext_moduleSheafFunctor`), so the statement reduces to
the same unit law for sheaves of sets, which is also absent and is proved here as
`AlgebraicGeometry.Space.smallToposMorphismTypeU_comp_id_id_hom_app`.

That one reduces in turn, and this is the only step with geometric content.  The small étale
direct image is the spaces-étale direct image conjugated by the comparison equivalence of
Stacks 03G1, and conjugation by an equivalence carries a unit law to a unit law — that is
`CategoryTheory.Equivalence.transportCompApp_of_idIso`, the companion of the cocycle statement
`CategoryTheory.Equivalence.transportCompApp_assoc` that
`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardAssoc` proves.  On the
spaces-étale site the direct image is precomposition with the base-change functor of Stacks
03G2, part (1), so its unit law is the site-level coherence
`AlgebraicGeometry.Space.spacesBaseChange_id_comp` read at one chart and mapped through a
sheaf.  Nothing else is needed:  the base-change coherence is available, and so is the
associativity of every comparison in the chain.

## Main results

* `CategoryTheory.Equivalence.transportCompApp_of_idIso`: conjugating by an equivalence
  preserves the unit law of a composition comparison of an endofunctor.
* `AlgebraicGeometry.Space.spacesBaseChange_comp_id_id_inv_app` and
  `AlgebraicGeometry.Space.spacesBaseChange_pushforward_compTypeU_id_hom_app`: the unit law on
  the spaces-étale site and on its sheaves of sets at the universe of the structure rings.
* `AlgebraicGeometry.Space.smallEtaleDirectImageIdIso_hom_app`: the identification of the small
  étale direct image along an identity with the identity functor is the conjugate of the
  spaces-étale one, the Kan-extension detour it is defined through cancelling.
* `AlgebraicGeometry.Space.smallToposMorphismTypeU_comp_id_id_hom_app`: **the unit law of
  Stacks 03G2, part (3), at a pair of identities**, for sheaves of sets.
* `AlgebraicGeometry.Space.modulePushforwardCompIso_id_id_hom_app`: **the unit law of Stacks
  03LU at a pair of identities**, for `𝒪`-modules.
* `AlgebraicGeometry.Space.idIsoOfCompIso_modulePushforwardIdIso_eq`: the normalisation
  `CategoryTheory.Functor.idIsoOfCompIso` of `AlgebraicGeometry.Space.modulePushforwardIdIso`
  against the comparison at `(𝟙 X, 𝟙 X)` is that isomorphism itself.
* `AlgebraicGeometry.Space.modulePushforwardCoherence_idIso` and
  `AlgebraicGeometry.Space.modulePushforwardCoherence_modulePullbackIdIso`: **the identity data
  of the pseudofunctoriality of 03LU that this repository constructs are the identifications
  that carry the tag**, for the direct and for the inverse image.  This is the form a consumer
  of `AlgebraicGeometry.Space.ModulePushforwardCoherence` wants: its unit coherences, such as
  `AlgebraicGeometry.Space.ModulePushforwardCoherence.modulePullbackCompIso_id_left`, become
  statements about `AlgebraicGeometry.Space.modulePullbackIdIso` itself.

## Implementation notes

**The identity is left written `𝟙 X ≫ 𝟙 X` wherever the composition comparison puts it
there.**  Composition in `AlgebraicGeometry.Space.AlgebraicSpaces` is unital by definitional
unfolding, so the two spellings are interchangeable; but replacing `𝟙 X ≫ 𝟙 X` by `𝟙 X` inside
the *type of a component* makes the kernel evaluate a direct image of sheaves of modules and
exhausts its budget, while the same identification between two *functors*, or between two
*isomorphisms of functors*, is free.  Every statement below therefore keeps whichever spelling
the comparison it mentions produces, and each conversion is left to the elaborator at a place
where only functors meet — which is why
`CategoryTheory.Equivalence.transportCompApp_of_idIso` is stated with `P : p ⋙ p ≅ p`, at a
plain endofunctor, rather than with a third functor and an equality.

**The passage to underlying sheaves of sets is taken only after the composition comparison has
been replaced by its transported form.**
`AlgebraicGeometry.Space.modulePushforwardCompIso_eq_compIsoCongr` is an equality of
isomorphisms and rewriting with it is free, whereas carrying that same equality *through*
`CategoryTheory.Sheaf.moduleSheafFunctor` — by `congrArg`, by the repository's own
`AlgebraicGeometry.Space.moduleSheafFunctor_map_congr`, or by `rewrite` inside the image — is a
kernel deterministic timeout with no elaboration error.  So the proof of the main result
rewrites at the level of isomorphisms first and descends to sheaves of sets afterwards, and the
descent is split into
`AlgebraicGeometry.Space.moduleSheafFunctor_map_compIsoCongr_id_id_hom_app` and
`AlgebraicGeometry.Space.compIsoCongr_pushforwardModulesCompAt_id_id_hom_app` so that no single
declaration mentions the transported comparison more than twice.

**`AlgebraicGeometry.Space.smallEtaleDirectImageIdIso` is defined through the right Kan
extension along the comparison functor of Stacks 03G1 and not through the quasi-inverse of the
comparison equivalence.**  The two are identified by
`AlgebraicGeometry.Space.smallEtaleComparisonRanIso`, and
`AlgebraicGeometry.Space.restriction_map_ranIso_inv_comp_counitIso` says that restricting that
identification and following it by the counit of the equivalence is the counit of the
Kan-extension adjunction.  Together with naturality of the spaces-étale unit law the detour
cancels, which is `AlgebraicGeometry.Space.smallEtaleDirectImageIdIso_hom_app`, and from there
on only the equivalence appears.

**The spaces-étale unit laws of
`StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleBaseChangeUnitors` are stated for
sheaves valued in `Type (u + 1)`, in the orientation
`CategoryTheory.LocallyDiscrete.mkPseudofunctorOfLeftAdjoints` asks for.**  The direct image of
`𝒪`-modules is indexed by sheaves valued in `Type u`, so those statements do not apply, and the
two below are not derived from them: both come from the site-level coherence
`AlgebraicGeometry.Space.spacesBaseChange_id_comp`, which is universe-free, the passage to
sheaves being the one `rfl` that the direct image is precomposition with the base-change
functor.

No `stacks` tag is registered.  This is an engine lemma — a step of part (2) of [Stacks
Project, Tag 04G2] and a compatibility between two data of [Stacks Project, Tag 03LU] — and
neither source states it; 03LU's own assertions are registered where those data are
constructed.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory.Equivalence

universe v₀ w₀ u₀ t₀

variable {A₀ : Type u₀} [Category.{v₀} A₀] {B₀ : Type t₀} [Category.{w₀} B₀]

/-- **Conjugating by an equivalence preserves the unit law of a composition comparison.**  Let
`p` be an endofunctor of `A₀` with a composition comparison `P : p ⋙ p ≅ p` and an isomorphism
`v : p ≅ 𝟭` for which `P` is the image under `p` of `v`.  Then the conjugate of `P` by an
equivalence `e : A₀ ≌ B₀`, which is
`CategoryTheory.Equivalence.transportCompApp`, is the image under the conjugate of `p` of the
conjugate of `v`.

The conjugate of `v` appears in the only form the conjugation makes available: the image under
`e.functor` of a component of `v`, followed by the counit of `e`.  The proof is naturality of
the inverse unit of `e` at a component of `v`, together with the triangle identity
`CategoryTheory.Equivalence.unitInv_app_inverse` which identifies the inverse unit at an object
of the image of `e.inverse` with the inverse image of the counit. -/
theorem transportCompApp_of_idIso (e : A₀ ≌ B₀) {p : A₀ ⥤ A₀} (P : p ⋙ p ≅ p)
    (v : p ≅ 𝟭 A₀) (hv : ∀ N, P.hom.app N = p.map (v.hom.app N)) (G : B₀) :
    transportCompApp e e e P G =
      (e.inverse ⋙ p ⋙ e.functor).map
        (e.functor.map (v.hom.app (e.inverse.obj G)) ≫ e.counitIso.hom.app G) := by
  have hnat := e.unitIso.inv.naturality (v.hom.app (e.inverse.obj G))
  simp only [Functor.comp_map, Functor.id_map, Functor.id_obj, Functor.comp_obj] at hnat
  have hu : e.unitIso.inv.app (e.inverse.obj G) =
      e.inverse.map (e.counitIso.hom.app G) := e.unitInv_app_inverse G
  simp only [transportCompApp, hv, ← CategoryTheory.Functor.map_comp]
  rw [← hnat, hu, ← CategoryTheory.Functor.map_comp]
  rfl

end CategoryTheory.Equivalence

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : AlgebraicSpaces B S hS}

/-! ### The spaces-étale site -/

/-- **Stacks 03G2, the unit law at a pair of identities, on the sites.**  The composition
isomorphism of part (2) for base change along `𝟙 X` twice is the identification of part (1) of
base change along `𝟙 X` with the identity functor, read at the base change of the chart.

This is the unit coherence `AlgebraicGeometry.Space.spacesBaseChange_id_comp` at `p = 𝟙 X`,
read at one chart:  there the right unitor is an identity and the transport along
`𝟙 X ≫ 𝟙 X = 𝟙 X` is too, so the coherence says that the two morphisms below are mutually
inverse. -/
theorem spacesBaseChange_comp_id_id_inv_app (X : AlgebraicSpaces B S hS)
    (V : SpacesEtale B S hS X) :
    (spacesBaseChange_comp B S hS (𝟙 X) (𝟙 X)).inv.app V =
      (spacesBaseChange_id B S hS X).inv.app
        ((spacesBaseChange B S hS (𝟙 X)).functor.obj V) := by
  have key : (spacesBaseChange_comp B S hS (𝟙 X) (𝟙 X)).inv.app V ≫
      ((spacesBaseChange_id B S hS X).hom.app
          ((spacesBaseChange B S hS (𝟙 X)).functor.obj V) ≫
        𝟙 ((spacesBaseChange B S hS (𝟙 X)).functor.obj V)) =
      𝟙 ((spacesBaseChange B S hS (𝟙 X)).functor.obj V) :=
    NatTrans.congr_app (spacesBaseChange_id_comp B S hS (𝟙 X)) V
  exact (Iso.comp_hom_eq_id ((spacesBaseChange_id B S hS X).app _)).1
    ((congrArg (fun t ↦ (spacesBaseChange_comp B S hS (𝟙 X) (𝟙 X)).inv.app V ≫ t)
      (Category.comp_id _)).symm.trans key)

/-- **Stacks 03G2, the unit law at a pair of identities, on spaces-étale sheaves of sets** at
the universe of the structure rings:  the composition comparison of the direct images along
`𝟙 X` twice is the direct image along `𝟙 X` of the identification of that direct image with the
identity functor.

The direct image is precomposition with the base-change functor, so both sides are the sheaf
applied to a morphism of charts, and the two morphisms of charts agree by
`AlgebraicGeometry.Space.spacesBaseChange_comp_id_id_inv_app`. -/
theorem spacesBaseChange_pushforward_compTypeU_id_hom_app (X : AlgebraicSpaces B S hS)
    (A₀ : Sheaf (SpacesEtale.topology B S hS X) (Type u)) :
    (spacesBaseChange_pushforward_compTypeU B S hS (𝟙 X) (𝟙 X)).hom.app A₀ =
      (spacesDirectImage B S hS (𝟙 X)).map
        ((spacesDirectImageIdIso B S hS X).hom.app A₀) := by
  apply ObjectProperty.hom_ext
  refine NatTrans.ext (funext fun V ↦ ?_)
  have e1 : ((spacesBaseChange_pushforward_compTypeU B S hS (𝟙 X) (𝟙 X)).hom.app A₀).hom.app V =
      A₀.obj.map ((spacesBaseChange_comp B S hS (𝟙 X) (𝟙 X)).inv.app V.unop).op := rfl
  have e2 : (((spacesDirectImage B S hS (𝟙 X)).map
        ((spacesDirectImageIdIso B S hS X).hom.app A₀)).hom.app V) =
      A₀.obj.map ((spacesBaseChange_id B S hS X).inv.app
        ((spacesBaseChange B S hS (𝟙 X)).functor.obj V.unop)).op := rfl
  rw [e1, e2, spacesBaseChange_comp_id_id_inv_app]

/-! ### The small étale site -/

/-- **The identification of the small étale direct image along an identity with the identity
functor is the conjugate of the spaces-étale one.**  It is defined through the right Kan
extension along the comparison functor of Stacks 03G1, and that detour cancels:  the
comparison `AlgebraicGeometry.Space.smallEtaleComparisonRanIso` of the Kan extension with the
quasi-inverse of the comparison equivalence passes through the spaces-étale unit law by
naturality, and `AlgebraicGeometry.Space.restriction_map_ranIso_inv_comp_counitIso` then turns
the counit of the Kan-extension adjunction into the counit of the equivalence. -/
theorem smallEtaleDirectImageIdIso_hom_app (X : AlgebraicSpaces B S hS)
    (G : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) :
    (smallEtaleDirectImageIdIso B S hS X).hom.app G =
      (smallEtaleComparisonRestriction B S hS X).map
          ((spacesDirectImageIdIso B S hS X).hom.app
            ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G)) ≫
        (smallEtaleComparisonRestriction B S hS X).asEquivalence.counitIso.hom.app G := by
  have hnat := (spacesDirectImageIdIso B S hS X).hom.naturality
    ((smallEtaleComparisonRanIso B S hS X).hom.app G)
  simp only [Functor.id_map, Functor.id_obj] at hnat
  have hinner : ((spacesDirectImage B S hS (𝟙 X)).map
          ((smallEtaleComparisonRanIso B S hS X).hom.app G) ≫
        (spacesDirectImageIdIso B S hS X).hom.app
          ((smallEtaleComparisonRan B S hS X).obj G)) ≫
        (smallEtaleComparisonRanIso B S hS X).inv.app G =
      (spacesDirectImageIdIso B S hS X).hom.app
        ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G) := by
    rw [hnat, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  have hA : (smallEtaleDirectImageIdIso B S hS X).hom.app G =
      (smallEtaleComparisonRestriction B S hS X).map
          ((spacesDirectImage B S hS (𝟙 X)).map
            ((smallEtaleComparisonRanIso B S hS X).hom.app G)) ≫
        ((smallEtaleComparisonRestriction B S hS X).map
            ((spacesDirectImageIdIso B S hS X).hom.app
              ((smallEtaleComparisonRan B S hS X).obj G)) ≫
          (comparisonAdjunction B S hS X).counit.app G) := rfl
  rw [hA, ← restriction_map_ranIso_inv_comp_counitIso B S hS X G, ← Category.assoc,
    ← CategoryTheory.Functor.map_comp]
  exact (Category.assoc _ _ _).symm.trans
    (congrArg
      (fun t ↦ t ≫ (smallEtaleComparisonRestriction B S hS X).asEquivalence.counitIso.hom.app G)
      (((smallEtaleComparisonRestriction B S hS X).map_comp _ _).symm.trans
        (congrArg (smallEtaleComparisonRestriction B S hS X).map hinner)))

/-- **Stacks 03G2, part (3), the unit law at a pair of identities.**  The comparison of the
small étale direct images of sheaves of sets along `𝟙 X` twice is the direct image along `𝟙 X`
of the identification of that direct image with the identity functor.

The small étale direct image is the spaces-étale one conjugated by the comparison equivalence
of Stacks 03G1, the conjugated comparison is
`CategoryTheory.Equivalence.transportCompApp`, and
`CategoryTheory.Equivalence.transportCompApp_of_idIso` carries the spaces-étale unit law
`AlgebraicGeometry.Space.spacesBaseChange_pushforward_compTypeU_id_hom_app` across the
conjugation. -/
theorem smallToposMorphismTypeU_comp_id_id_hom_app (X : AlgebraicSpaces B S hS)
    (G : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) :
    (smallToposMorphismTypeU_comp B S hS (𝟙 X) (𝟙 X)).hom.app G =
      (smallEtaleDirectImage B S hS (𝟙 X)).map
        ((smallEtaleDirectImageIdIso B S hS X).hom.app G) := by
  rw [smallEtaleDirectImageIdIso_hom_app]
  exact Equivalence.transportCompApp_of_idIso
    (smallEtaleToposEquivTypeU B S hS X)
    (spacesBaseChange_pushforward_compTypeU B S hS (𝟙 X) (𝟙 X))
    (spacesDirectImageIdIso B S hS X)
    (spacesBaseChange_pushforward_compTypeU_id_hom_app B S hS X) G

/-! ### `𝒪`-modules -/

section Reducible

/- The two spellings of the category of `𝒪_X`-modules are definitionally equal through
`AlgebraicGeometry.Space.smallEtaleRingedSite`, the only link in the chain that is not an
abbreviation; collapsing them is what lets the identity functor of the one be read as the
identity functor of the other. -/
attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

/-- **On underlying sheaves of sets the unit law for the direct image of `𝒪`-modules along an
identity is the unit law for the direct image of sheaves of sets.**  This is the inverse half
`AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePushforwardIdIso_inv_app` read forwards:
two isomorphisms with the same inverse have the same forward map. -/
theorem moduleSheafFunctor_map_modulePushforwardIdIso_hom_app (X : AlgebraicSpaces B S hS)
    (M : Modules.{u, u} B S hS X.1 X.2) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
        ((modulePushforwardIdIso B S hS X).hom.app M) =
      (smallEtaleDirectImageIdIso B S hS X).hom.app
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj M) :=
  (Iso.inv_eq_inv
      ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).mapIso
        ((modulePushforwardIdIso B S hS X).app M))
      ((smallEtaleDirectImageIdIso B S hS X).app
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj M))).1
    (moduleSheafFunctor_map_modulePushforwardIdIso_inv_app B S hS X M)

end Reducible

/-- **The unit law of Stacks 03LU at a pair of identities, on underlying sheaves of sets**, for
the transported form of the composition comparison that
`AlgebraicGeometry.Space.modulePushforwardCompIso_eq_compIsoCongr` identifies it with.

The three ingredients are:  that transported comparison is the geometric comparison on
underlying sheaves of sets, by
`AlgebraicGeometry.Space.moduleSheafFunctor_map_compIsoCongr_hom_app`; the geometric comparison
obeys the unit law, by
`AlgebraicGeometry.Space.smallToposMorphismTypeU_comp_id_id_hom_app`; and the direct image of
`𝒪`-modules is the direct image of sheaves of sets on underlying sheaves, by
`AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePushforward_map`. -/
theorem moduleSheafFunctor_map_compIsoCongr_id_id_hom_app (X : AlgebraicSpaces B S hS)
    (M : Modules.{u, u} B S hS X.1 X.2) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
        ((CategoryTheory.Functor.compIsoCongr
          (pushforwardModules_eq_modulePushforward B S hS (𝟙 X))
          (pushforwardModules_eq_modulePushforward B S hS (𝟙 X))
          (pushforwardModules_eq_modulePushforward B S hS (𝟙 X ≫ 𝟙 X))
          (pushforwardModulesCompAt B S hS (𝟙 X) (𝟙 X))).hom.app M) =
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
        ((modulePushforward B S hS (𝟙 X)).map
          ((modulePushforwardIdIso B S hS X).hom.app M)) :=
  ((moduleSheafFunctor_map_compIsoCongr_hom_app B S hS (𝟙 X) (𝟙 X) M).trans
      (smallToposMorphismTypeU_comp_id_id_hom_app B S hS X
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj M))).trans
    ((congrArg (smallEtaleDirectImage B S hS (𝟙 X)).map
        (moduleSheafFunctor_map_modulePushforwardIdIso_hom_app B S hS X M).symm).trans
      (moduleSheafFunctor_map_modulePushforward_map B S hS (𝟙 X)
        ((modulePushforwardIdIso B S hS X).hom.app M)).symm)

/-- **The unit law of Stacks 03LU at a pair of identities**, for the transported form of the
composition comparison.  A morphism of sheaves of modules is determined by the underlying
morphism of sheaves of sets, so this is
`AlgebraicGeometry.Space.moduleSheafFunctor_map_compIsoCongr_id_id_hom_app`. -/
theorem compIsoCongr_pushforwardModulesCompAt_id_id_hom_app (X : AlgebraicSpaces B S hS)
    (M : Modules.{u, u} B S hS X.1 X.2) :
    (CategoryTheory.Functor.compIsoCongr
          (pushforwardModules_eq_modulePushforward B S hS (𝟙 X))
          (pushforwardModules_eq_modulePushforward B S hS (𝟙 X))
          (pushforwardModules_eq_modulePushforward B S hS (𝟙 X ≫ 𝟙 X))
          (pushforwardModulesCompAt B S hS (𝟙 X) (𝟙 X))).hom.app M =
      (modulePushforward B S hS (𝟙 X)).map
        ((modulePushforwardIdIso B S hS X).hom.app M) :=
  Stacks.Sheaves.RingedToposModules.hom_ext_moduleSheafFunctor
    (R := structureRingSheaf B S hS X)
    (moduleSheafFunctor_map_compIsoCongr_id_id_hom_app B S hS X M)

/-- **The unit law of Stacks 03LU for the direct image of `𝒪`-modules at a pair of
identities:** the composition comparison `(𝟙 X)_* ∘ (𝟙 X)_* ≅ (𝟙 X)_*` at a module is the
direct image along `𝟙 X` of the identification `(𝟙 X)_* ≅ 𝟭` at that module.

This is the compatibility that `AlgebraicGeometry.Space.modulePushforwardCoherenceOfIdIso` asks
nothing of, and the whole difference between the `idIso` field of the coherence it builds and
`AlgebraicGeometry.Space.modulePushforwardIdIso`. -/
theorem modulePushforwardCompIso_id_id_hom_app (X : AlgebraicSpaces B S hS)
    (M : Modules.{u, u} B S hS X.1 X.2) :
    (modulePushforwardCompIso B S hS (𝟙 X) (𝟙 X)).hom.app M =
      (modulePushforward B S hS (𝟙 X)).map
        ((modulePushforwardIdIso B S hS X).hom.app M) := by
  rw [modulePushforwardCompIso_eq_compIsoCongr]
  exact compIsoCongr_pushforwardModulesCompAt_id_id_hom_app B S hS X M

section ReducibleCoherence

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

/-- **The normalisation of the unit law of Stacks 03LU against the composition comparison at a
pair of identities is that unit law itself.**  So the `idIso` field of
`AlgebraicGeometry.Space.modulePushforwardCoherenceOfIdIso` applied to
`AlgebraicGeometry.Space.modulePushforwardIdIso` is `modulePushforwardIdIso`:  the
pseudofunctoriality data of 03LU that the repository constructs is the data of the
identifications that carry the tag, and not of a correction of them. -/
theorem idIsoOfCompIso_modulePushforwardIdIso_eq (X : AlgebraicSpaces B S hS) :
    Functor.idIsoOfCompIso (modulePushforwardCompIso B S hS (𝟙 X) (𝟙 X))
        (modulePushforwardIdIso B S hS X) =
      modulePushforwardIdIso B S hS X := by
  refine Iso.ext (NatTrans.ext (funext fun M ↦ ?_))
  rw [Functor.idIsoOfCompIso_hom_app, modulePushforwardCompIso_id_id_hom_app,
    ← Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- **The identity datum of the pseudofunctoriality of Stacks 03LU that this repository
constructs is the identification `AlgebraicGeometry.Space.modulePushforwardIdIso` that carries
the tag.**  `AlgebraicGeometry.Space.modulePushforwardCoherence` is
`AlgebraicGeometry.Space.modulePushforwardCoherenceOfIdIso` applied to that identification, so
its `idIso` field is the normalisation of it, and
`AlgebraicGeometry.Space.idIsoOfCompIso_modulePushforwardIdIso_eq` says the normalisation
changes nothing. -/
theorem modulePushforwardCoherence_idIso (X : AlgebraicSpaces B S hS) :
    (modulePushforwardCoherence B S hS).idIso X = modulePushforwardIdIso B S hS X :=
  idIsoOfCompIso_modulePushforwardIdIso_eq B S hS X

/-- **The unit law for the inverse image supplied by the pseudofunctoriality of Stacks 03LU is
the identification `AlgebraicGeometry.Space.modulePullbackIdIso` that carries the tag.**  Both
are the adjoint transpose of a unit law for the direct image, and those agree by
`AlgebraicGeometry.Space.modulePushforwardCoherence_idIso`.

This is what makes the unit coherences of
`AlgebraicGeometry.Space.ModulePushforwardCoherence` — for instance
`AlgebraicGeometry.Space.ModulePushforwardCoherence.modulePullbackCompIso_id_left` — available
for the tagged identification, which is the spelling the consumers of Stacks 04G2 use. -/
theorem modulePushforwardCoherence_modulePullbackIdIso (X : AlgebraicSpaces B S hS) :
    (modulePushforwardCoherence B S hS).modulePullbackIdIso X =
      modulePullbackIdIso B S hS X :=
  congrArg (Adjunction.leftAdjointIdIso (modulePullbackAdjunction B S hS (𝟙 X)))
    (modulePushforwardCoherence_idIso B S hS X)

end ReducibleCoherence

end AlgebraicGeometry.Space

end
