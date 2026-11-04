module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.LerayForDerivedSections

/-!
# The Leray comparison for derived sections along a composite

Let `i : Z ⟶ X` and `p : X ⟶ Y` be morphisms of ringed spaces and let `V ⊆ Y` be open.  There are
two routes from derived sections over `(p ∘ i)⁻¹ V` to derived sections over `V` of a derived
pushforward along `p ∘ i`:

* the Leray comparison `Stacks.Cohomology.DerivedSectionsLeray.lerayComparison` for `i ≫ p` at
  `V`, read through the composition isomorphism
  `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCompIso`,
  `Ri_* ⋙ Rp_* ≅ R(i ≫ p)_*`, of Tag 079W;
* the Leray comparison for `i` *relative to `p`* — the same construction with sections over `V`
  on `Y` replaced by sections over `p⁻¹ V`, read as `Γ(V, 𝒪_Y)`-modules — followed by the Leray
  comparison for `p` at `V`.

`Stacks.Cohomology.DerivedSectionsLeray.lerayComparison_comp` proves that the two routes agree.

## Main definitions

* `Stacks.Cohomology.DerivedSectionsLeray.preimageSectionsPushforwardIso` — the identification
  `Γ(p⁻¹ V, i_* ℱ) = Γ((p ∘ i)⁻¹ V, ℱ)` of `Γ(V, 𝒪_Y)`-modules, which holds on the nose.
* `Stacks.Cohomology.DerivedSectionsLeray.lerayCompositeUnit` and
  `Stacks.Cohomology.DerivedSectionsLeray.lerayCompositeComparison` — the relative Leray unit
  `Γ((p ∘ i)⁻¹ V, -) ⟶ Qh ⋙ (Ri_* ⋙ RΓ(p⁻¹ V, -))` and the comparison of derived functors it
  induces.
* `Stacks.Cohomology.DerivedSectionsLeray.derivedPreimageSectionsCompIso` — the resulting natural
  isomorphism `Ri_* ⋙ RΓ(p⁻¹ V, -) ≅ RΓ((p ∘ i)⁻¹ V, -)`.

## Main results

* `Stacks.Cohomology.DerivedSectionsLeray.lerayComparison_comp` — **the composite coherence**: the
  Leray comparison for `i ≫ p` at `V`, followed by the composition isomorphism for derived
  pushforward, is the relative Leray comparison for `i` followed by the Leray comparison for `p`.
* `Stacks.Cohomology.DerivedSectionsLeray.isIso_lerayCompositeComparison` — the relative Leray
  comparison is an isomorphism, which is Tag 0D5W for `i` with sections over `p⁻¹ V` as the
  target.
* `Stacks.Cohomology.DerivedSectionsLeray.lerayComparison_fac_app` and
  `Stacks.Cohomology.DerivedSectionsLeray.lerayCompositeComparison_fac_app` — the pointwise
  factorizations through the derived-functor units that characterize the two comparisons.

## Implementation notes

`lerayComparison i W` lands in `D(Γ(W, 𝒪_X))` for an open `W ⊆ X`, so for `W = p⁻¹ V` its
target ring is `Γ(p⁻¹ V, 𝒪_X)` rather than `Γ(V, 𝒪_Y)`. The relative comparison
`lerayCompositeComparison` is built from the same three pieces as `lerayComparison` — an
identification of degreewise functors, the unit of the derived functor on the middle space, and
the unit of `Ri_*` — with `Stacks.Cohomology.DerivedSectionsLeray.preimageSections` for `p` in
place of `Stacks.Cohomology.DerivedSectionsLeray.sectionsOverOpen`, so that everything is over
`Γ(V, 𝒪_Y)`.

## References

* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 0D5T](https://stacks.math.columbia.edu/tag/0D5T)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
  (derivedPushforward derivedPushforwardUnit derivedPushforwardCompIso)
open Stacks.Cohomology.DerivedPushforwardComposition
  (derivedPushforwardCompUnit derivedPushforwardCompUnit_app
    derivedPushforwardCompUnit_comp_derivedPushforwardCompIso)

namespace Stacks.Cohomology.DerivedSectionsLeray

universe u

attribute [local instance] HasDerivedCategory.standard

variable {Z X Y : RingedSpace.{u, u}} (i : Z ⟶ X) (p : X ⟶ Y) (V : Opens Y.carrier)

/-! ### The relative Leray comparison -/

/-- **Sections over `p⁻¹ V` of a direct image are sections over `(p ∘ i)⁻¹ V`.**  The
identification `Γ(p⁻¹ V, i_* ℱ) = Γ((p ∘ i)⁻¹ V, ℱ)`, both sides read as `Γ(V, 𝒪_Y)`-modules by
restriction of scalars. It is the identity natural transformation. -/
def preimageSectionsPushforwardIso :
    modulePushforward i ⋙ preimageSections p V ≅ preimageSections (i ≫ p) V :=
  Iso.refl _

/-- The canonical transformation from termwise sections over `(p ∘ i)⁻¹ V` to the composite
`Ri_* ⋙ RΓ(p⁻¹ V, -)`: the identification `Γ(p⁻¹ V, i_* -) = Γ((p ∘ i)⁻¹ V, -)`, followed by the
unit of `RΓ(p⁻¹ V, -)` and then the unit of `Ri_*`.  This is `lerayUnit` with sections over an
open of `Y` replaced by sections over its inverse image in `X`. -/
def lerayCompositeUnit :
    homotopyPreimageSections (i ≫ p) V ⟶
      DerivedCategory.Qh ⋙ (derivedPushforward i ⋙ derivedPreimageSections p V) :=
  Functor.whiskerRight
      (Functor.mapHomotopyCategoryCompIso (preimageSectionsPushforwardIso i p V)
        (ComplexShape.up ℤ)).inv DerivedCategory.Qh ≫
    Functor.whiskerLeft ((modulePushforward i).mapHomotopyCategory (ComplexShape.up ℤ))
      (derivedPreimageSectionsUnit p V) ≫
    Functor.whiskerRight (derivedPushforwardUnit i) (derivedPreimageSections p V)

/-- **The relative Leray comparison** `RΓ((p ∘ i)⁻¹ V, -) ⟶ RΓ(p⁻¹ V, -) ∘ Ri_*`, the
transformation induced by `lerayCompositeUnit` through the universal property of the right derived
functor of sections over `(p ∘ i)⁻¹ V`. -/
def lerayCompositeComparison :
    derivedPreimageSections (i ≫ p) V ⟶ derivedPushforward i ⋙ derivedPreimageSections p V :=
  (derivedPreimageSections (i ≫ p) V).rightDerivedDesc (derivedPreimageSectionsUnit (i ≫ p) V)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Z)) (ComplexShape.up ℤ)) _
    (lerayCompositeUnit i p V)

/-! ### The factorizations characterizing the two comparisons -/

/-- The equation characterizing the relative Leray comparison, pointwise: composing it with the
unit of `RΓ((p ∘ i)⁻¹ V, -)` recovers `lerayCompositeUnit`. -/
theorem lerayCompositeComparison_fac_app
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing Z)) (ComplexShape.up ℤ)) :
    (derivedPreimageSectionsUnit (i ≫ p) V).app K ≫
        (lerayCompositeComparison i p V).app (DerivedCategory.Qh.obj K) =
      (lerayCompositeUnit i p V).app K :=
  (derivedPreimageSections (i ≫ p) V).rightDerived_fac_app
    (derivedPreimageSectionsUnit (i ≫ p) V)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Z)) (ComplexShape.up ℤ)) _
    (lerayCompositeUnit i p V) K

/-- `lerayCompositeComparison_fac_app` with a further morphism `g` appended. -/
theorem lerayCompositeComparison_fac_app_comp
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing Z)) (ComplexShape.up ℤ))
    {T : DerivedCategory (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V)))}
    (g : (derivedPushforward i ⋙ derivedPreimageSections p V).obj
      (DerivedCategory.Qh.obj K) ⟶ T) :
    (derivedPreimageSectionsUnit (i ≫ p) V).app K ≫
        (lerayCompositeComparison i p V).app (DerivedCategory.Qh.obj K) ≫ g =
      (lerayCompositeUnit i p V).app K ≫ g := by
  rw [← Category.assoc, lerayCompositeComparison_fac_app]

/-- The equation characterizing the Leray comparison of
`Stacks.Cohomology.DerivedSectionsLeray.lerayComparison`, pointwise: composing it with the unit of
`RΓ(f⁻¹ W, -)` recovers `lerayUnit`.  This is `lerayComparison_fac` evaluated at an object. -/
theorem lerayComparison_fac_app {X' Y' : RingedSpace.{u, u}} (f : X' ⟶ Y')
    (W : Opens Y'.carrier)
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X')) (ComplexShape.up ℤ)) :
    (derivedPreimageSectionsUnit f W).app K ≫
        (lerayComparison f W).app (DerivedCategory.Qh.obj K) =
      (lerayUnit f W).app K :=
  (derivedPreimageSections f W).rightDerived_fac_app (derivedPreimageSectionsUnit f W)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X'))
      (ComplexShape.up ℤ)) _ (lerayUnit f W) K

/-- `lerayComparison_fac_app` with a further morphism `g` appended. -/
theorem lerayComparison_fac_app_comp {X' Y' : RingedSpace.{u, u}} (f : X' ⟶ Y')
    (W : Opens Y'.carrier)
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X')) (ComplexShape.up ℤ))
    {T : DerivedCategory (ModuleCat.{u} ((structureSheafRing Y').obj.obj (op W)))}
    (g : (derivedPushforward f ⋙ derivedSectionsOverOpen Y' W).obj
      (DerivedCategory.Qh.obj K) ⟶ T) :
    (derivedPreimageSectionsUnit f W).app K ≫
        (lerayComparison f W).app (DerivedCategory.Qh.obj K) ≫ g =
      (lerayUnit f W).app K ≫ g := by
  rw [← Category.assoc, lerayComparison_fac_app]

/-! ### The two ingredients supplied by the pushforward and sections units -/

/-- **The unit of `R(i ≫ p)_*`, read through the composition isomorphism, is the composition
unit.** The unit of `R(i ≫ p)_*` followed by the inverse of the composition isomorphism
`Ri_* ⋙ Rp_* ≅ R(i ≫ p)_*` is `derivedPushforwardCompUnit`. -/
theorem derivedPushforwardUnit_comp_derivedPushforwardCompIso_inv
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing Z)) (ComplexShape.up ℤ)) :
    (derivedPushforwardUnit (i ≫ p)).app K ≫
        (derivedPushforwardCompIso i p).inv.app (DerivedCategory.Qh.obj K) =
      (derivedPushforwardCompUnit i p (derivedPushforward i) (derivedPushforward p)
        (derivedPushforwardUnit i) (derivedPushforwardUnit p)).app K := by
  rw [← derivedPushforwardCompUnit_comp_derivedPushforwardCompIso i p K, Category.assoc,
    Iso.hom_inv_id_app]
  exact Category.comp_id _

/-- Naturality of the unit of `RΓ(U, -)` with respect to a map `φ` of complexes, with a further
morphism `g` appended. -/
theorem derivedSectionsOverOpenUnit_naturality_comp {W : RingedSpace.{u, u}}
    (U : Opens W.carrier)
    {K L : HomotopyCategory (SheafOfModules.{u} (structureSheafRing W)) (ComplexShape.up ℤ)}
    (φ : K ⟶ L) {T : DerivedCategory (ModuleCat.{u} ((structureSheafRing W).obj.obj (op U)))}
    (g : (derivedSectionsOverOpen W U).obj (DerivedCategory.Qh.obj L) ⟶ T) :
    (derivedSectionsOverOpenUnit W U).app K ≫
        (derivedSectionsOverOpen W U).map (DerivedCategory.Qh.map φ) ≫ g =
      DerivedCategory.Qh.map
          (((sectionsOverOpen W U).mapHomotopyCategory (ComplexShape.up ℤ)).map φ) ≫
        (derivedSectionsOverOpenUnit W U).app L ≫ g := by
  simpa only [Category.assoc, Functor.comp_map] using
    congrArg (· ≫ g) ((derivedSectionsOverOpenUnit W U).naturality φ).symm

/-! ### The two routes written out degreewise -/

/-- The first route, expanded: the Leray unit for `i ≫ p` followed by the composition isomorphism
is the identification of degreewise sections, the unit of `RΓ(V, -)`, the degreewise comparison of
pushforwards, and then the two pushforward units. -/
private theorem lerayUnit_comp_derivedPushforwardCompIso_inv_app
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing Z)) (ComplexShape.up ℤ)) :
    (lerayUnit (i ≫ p) V).app K ≫
        (derivedSectionsOverOpen Y V).map
          ((derivedPushforwardCompIso i p).inv.app (DerivedCategory.Qh.obj K)) =
      DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso (pushforwardPreimageSectionsIso (i ≫ p) V)
            (ComplexShape.up ℤ)).inv.app K) ≫
        (derivedSectionsOverOpenUnit Y V).app
            (((modulePushforward (i ≫ p)).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
          (derivedSectionsOverOpen Y V).map
              (DerivedCategory.Qh.map
                ((Functor.mapHomotopyCategoryCompIso (modulePushforwardComp i p)
                  (ComplexShape.up ℤ)).inv.app K)) ≫
            (derivedSectionsOverOpen Y V).map
                ((derivedPushforwardUnit p).app
                  (((modulePushforward i).mapHomotopyCategory (ComplexShape.up ℤ)).obj K)) ≫
              (derivedSectionsOverOpen Y V).map
                ((derivedPushforward p).map ((derivedPushforwardUnit i).app K)) := by
  dsimp only [lerayUnit, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  simp only [Category.assoc]
  rw [← (derivedSectionsOverOpen Y V).map_comp,
    derivedPushforwardUnit_comp_derivedPushforwardCompIso_inv i p K,
    derivedPushforwardCompUnit_app i p (derivedPushforward i) (derivedPushforward p)
      (derivedPushforwardUnit i) (derivedPushforwardUnit p) K]
  simp only [Functor.map_comp]

/-- The second route, expanded: the relative Leray unit followed by the Leray comparison for `p`
is the two identifications of degreewise sections, the unit of `RΓ(V, -)`, and then the two
pushforward units. -/
private theorem lerayCompositeUnit_comp_lerayComparison_app
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing Z)) (ComplexShape.up ℤ)) :
    (lerayCompositeUnit i p V).app K ≫
        (lerayComparison p V).app ((derivedPushforward i).obj (DerivedCategory.Qh.obj K)) =
      DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso (pushforwardPreimageSectionsIso (i ≫ p) V)
            (ComplexShape.up ℤ)).inv.app K) ≫
        (derivedSectionsOverOpenUnit Y V).app
            (((modulePushforward (i ≫ p)).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
          (derivedSectionsOverOpen Y V).map
              (DerivedCategory.Qh.map
                ((Functor.mapHomotopyCategoryCompIso (modulePushforwardComp i p)
                  (ComplexShape.up ℤ)).inv.app K)) ≫
            (derivedSectionsOverOpen Y V).map
                ((derivedPushforwardUnit p).app
                  (((modulePushforward i).mapHomotopyCategory (ComplexShape.up ℤ)).obj K)) ≫
              (derivedSectionsOverOpen Y V).map
                ((derivedPushforward p).map ((derivedPushforwardUnit i).app K)) := by
  have hn : (derivedPreimageSections p V).map ((derivedPushforwardUnit i).app K) ≫
        (lerayComparison p V).app ((derivedPushforward i).obj (DerivedCategory.Qh.obj K)) =
      (lerayComparison p V).app (DerivedCategory.Qh.obj
          (((modulePushforward i).mapHomotopyCategory (ComplexShape.up ℤ)).obj K)) ≫
        (derivedSectionsOverOpen Y V).map
          ((derivedPushforward p).map ((derivedPushforwardUnit i).app K)) :=
    (lerayComparison p V).naturality _
  dsimp only [lerayCompositeUnit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  simp only [Category.assoc]
  rw [hn, lerayComparison_fac_app_comp p V
    (((modulePushforward i).mapHomotopyCategory (ComplexShape.up ℤ)).obj K)]
  dsimp only [lerayUnit, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  simp only [Category.assoc]
  rw [derivedSectionsOverOpenUnit_naturality_comp]
  simp only [← DerivedCategory.Qh.map_comp_assoc]
  rfl

/-! ### The composite coherence -/

/-- **The Leray comparison is compatible with a composite of two morphisms.**  For
`i : Z ⟶ X`, `p : X ⟶ Y` of ringed spaces and an open `V ⊆ Y`, the Leray comparison for `i ≫ p`
at `V`, followed by the composition isomorphism `Ri_* ⋙ Rp_* ≅ R(i ≫ p)_*` of Tag 079W, equals
the relative Leray comparison for `i` followed by the Leray comparison for `p` at `V`.  Both sides
are transformations
`RΓ((p ∘ i)⁻¹ V, -) ⟶ Ri_* ⋙ Rp_* ⋙ RΓ(V, -)` of functors `D(𝒪_Z) ⥤ D(Γ(V, 𝒪_Y))`. -/
theorem lerayComparison_comp :
    lerayComparison (i ≫ p) V ≫
        Functor.whiskerRight (derivedPushforwardCompIso i p).inv
          (derivedSectionsOverOpen Y V) =
      lerayCompositeComparison i p V ≫
        Functor.whiskerLeft (derivedPushforward i) (lerayComparison p V) := by
  apply (derivedPreimageSections (i ≫ p) V).rightDerived_ext
    (derivedPreimageSectionsUnit (i ≫ p) V)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Z)) (ComplexShape.up ℤ))
  ext K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  rw [lerayComparison_fac_app_comp (i ≫ p) V K, lerayCompositeComparison_fac_app_comp i p V K]
  exact (lerayUnit_comp_derivedPushforwardCompIso_inv_app i p V K).trans
    (lerayCompositeUnit_comp_lerayComparison_app i p V K).symm

/-- **Tag 0D5W for a morphism relative to a second one.**  The relative Leray comparison
`RΓ((p ∘ i)⁻¹ V, -) ⟶ RΓ(p⁻¹ V, -) ∘ Ri_*` is an isomorphism, with no hypothesis on `i` or `p`. -/
theorem isIso_lerayCompositeComparison : IsIso (lerayCompositeComparison i p V) := by
  have := isIso_lerayComparison (i ≫ p) V
  have := isIso_lerayComparison p V
  have : IsIso (lerayCompositeComparison i p V ≫
      Functor.whiskerLeft (derivedPushforward i) (lerayComparison p V)) := by
    rw [← lerayComparison_comp i p V]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    (Functor.whiskerLeft (derivedPushforward i) (lerayComparison p V))

/-- The natural isomorphism `RΓ(p⁻¹ V, -) ∘ Ri_* ≅ RΓ((p ∘ i)⁻¹ V, -)` carried by the relative
Leray comparison. -/
def derivedPreimageSectionsCompIso :
    derivedPushforward i ⋙ derivedPreimageSections p V ≅ derivedPreimageSections (i ≫ p) V :=
  have := isIso_lerayCompositeComparison i p V
  (asIso (lerayCompositeComparison i p V)).symm

end Stacks.Cohomology.DerivedSectionsLeray

end
