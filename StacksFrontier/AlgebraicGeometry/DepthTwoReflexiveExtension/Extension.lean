module

public import StacksFrontier.AlgebraicGeometry.DepthTwoReflexiveExtension.Restrict
public import StacksFrontier.AlgebraicGeometry.Divisors.HartogsExtension.Basic

/-!
# The depth-two extension equivalence from two hypotheses

Let `X` be an integral locally Noetherian scheme and `U ⊆ X` an open such that the structure sheaf
has depth at least two at every point outside `U`. Assuming that a coherent reflexive module has
depth at least two wherever the structure sheaf does (part (1) of
[Stacks, Tag 0EBI](https://stacks.math.columbia.edu/tag/0EBI)), and that direct image along `U.ι`
preserves coherence and reflexivity, restriction to `U` is an equivalence from the coherent
reflexive modules on `X` to those on `U`, with direct image as inverse, and both functors are the
pullback and pushforward along `U.ι` after inclusion into all modules. This is
`Stacks.AlgebraicGeometry.ReflexiveExtensionGate.DepthTwoExtension X U`.

## Main definitions

* `StructureDepthTwoOff X U`: the structure sheaf has depth at least two at every point outside
  `U`.
* `ReflexiveDepthTwo X`: every coherent reflexive module has depth at least two at every point
  where the structure sheaf does.
* `liftAdjunctionOfObjectProperties`: an adjunction between categories lifts to full
  subcategories that both functors preserve.
* `depthTwoExtension_of_pushforward`: an inhabitant of `DepthTwoExtension X U`, given
  `StructureDepthTwoOff X U`, `ReflexiveDepthTwo X` and the preservation of coherence and
  reflexivity by direct image along `U.ι`.

## Main results

* `isIso_unit_of_structureDepthTwo`: on a locally Noetherian scheme, the unit of the
  pullback--pushforward adjunction along `U.ι` is invertible at a coherent reflexive module, given
  `StructureDepthTwoOff X U` and `ReflexiveDepthTwo X`.

## References

* [Stacks Project, Tag 0EBJ](https://stacks.math.columbia.edu/tag/0EBJ)
* [Stacks Project, Tag 0EBI](https://stacks.math.columbia.edu/tag/0EBI)
* [Stacks Project, Tag 0E9I](https://stacks.math.columbia.edu/tag/0E9I)
* [Stacks Project, Tag 0EBF](https://stacks.math.columbia.edu/tag/0EBF)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.AlgebraicGeometry.ReflexiveExtensionGate

universe u

namespace Stacks.AlgebraicGeometry.DepthTwoReflexiveExtension

/-- Lifting an adjunction to full subcategories cut out by properties that both functors
preserve. -/
noncomputable def liftAdjunctionOfObjectProperties
    {C D : Type*} [Category C] [Category D]
    {P : ObjectProperty C} {Q : ObjectProperty D}
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    (hF : ∀ A : P.FullSubcategory, Q (F.obj A.obj))
    (hG : ∀ B : Q.FullSubcategory, P (G.obj B.obj)) :
    (Q.lift (P.ι ⋙ F) hF) ⊣ (P.lift (Q.ι ⋙ G) hG) := by
  let homEquiv (A : P.FullSubcategory) (B : Q.FullSubcategory) :
      ((Q.lift (P.ι ⋙ F) hF).obj A ⟶ B) ≃
        (A ⟶ (P.lift (Q.ι ⋙ G) hG).obj B) :=
    { toFun := fun f => ObjectProperty.homMk (adj.homEquiv A.obj B.obj f.hom)
      invFun := fun g => ObjectProperty.homMk ((adj.homEquiv A.obj B.obj).symm g.hom)
      left_inv := fun f => ObjectProperty.hom_ext _ ((adj.homEquiv A.obj B.obj).left_inv f.hom)
      right_inv := fun g =>
        ObjectProperty.hom_ext _ ((adj.homEquiv A.obj B.obj).right_inv g.hom) }
  exact Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv
      homEquiv_naturality_left_symm := fun f g =>
        ObjectProperty.hom_ext _ (adj.homEquiv_naturality_left_symm f.hom g.hom)
      homEquiv_naturality_right := fun f g =>
        ObjectProperty.hom_ext _ (adj.homEquiv_naturality_right f.hom g.hom) }

variable (X : Scheme.{u}) (U : X.Opens)

/-- The structure sheaf of `X` has depth at least two at every point outside `U`. -/
abbrev StructureDepthTwoOff : Prop :=
  ∀ x : X, x ∉ (U : Set X) →
    (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)

/-- Every coherent reflexive module on `X` has depth at least two at every point where the
structure sheaf does. -/
abbrev ReflexiveDepthTwo : Prop :=
  ∀ (G : X.Modules), G.IsCoherent → IsReflexive G → ∀ x : X,
    (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x) →
      let : Module (X.presheaf.stalk x)
          (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          G.val x
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x)

/-- On a locally Noetherian scheme, the unit of the restriction--direct-image adjunction along
`U.ι` is invertible at a coherent reflexive module, given that the structure sheaf has depth at
least two off `U` (`StructureDepthTwoOff X U`) and that coherent reflexive modules have depth at
least two wherever the structure sheaf does (`ReflexiveDepthTwo X`). -/
theorem isIso_unit_of_structureDepthTwo [IsLocallyNoetherian X]
    (hdepth : StructureDepthTwoOff X U) (hEBI : ReflexiveDepthTwo X)
    (F : X.Modules) (hc : F.IsCoherent) (hr : IsReflexive F) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app F) :=
  AlgebraicGeometry.isIso_unit_restrict_pushforward_of_depth_ge_two X F U
    fun x hx => hEBI F hc hr x (hdepth x hx)

/-- On an integral locally Noetherian scheme, restriction to `U` is an equivalence of the
coherent reflexive modules with direct image as inverse, both functors being the pullback and
pushforward along `U.ι` (`DepthTwoExtension X U`). It takes as hypotheses that the structure sheaf
has depth at least two off `U` (`hdepth`), that coherent reflexive modules have depth at least two
wherever the structure sheaf does (`hEBI`), and that direct image along `U.ι` preserves coherence
and reflexivity (`hpush`). -/
noncomputable def depthTwoExtension_of_pushforward [IsIntegral X] [IsLocallyNoetherian X]
    (hdepth : StructureDepthTwoOff X U) (hEBI : ReflexiveDepthTwo X)
    (hpush : ∀ G : U.toScheme.Modules, G.IsCoherent → IsReflexive G →
      ((Scheme.Modules.pushforward U.ι).obj G).IsCoherent ∧
        IsReflexive ((Scheme.Modules.pushforward U.ι).obj G)) :
    DepthTwoExtension X U := by
  classical
  let : IsLocallyNoetherian U.toScheme := isLocallyNoetherian_of_isOpenImmersion U.ι
  set P := reflexiveCoherentProperty X with hP
  set Q := reflexiveCoherentProperty U.toScheme with hQ
  have hL (A : P.FullSubcategory) : Q ((Scheme.Modules.pullback U.ι).obj A.obj) := by
    let : A.obj.IsCoherent := A.property.1
    refine ⟨isCoherent_of_iso ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app A.obj)
        (AlgebraicGeometry.Modules.isCoherent_restrict A.obj U),
      isReflexive_of_iso ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app A.obj)
        (isReflexive_restrict U A.obj A.property.1 A.property.2)⟩
  have hR (B : Q.FullSubcategory) : P ((Scheme.Modules.pushforward U.ι).obj B.obj) :=
    hpush B.obj B.property.1 B.property.2
  let adj := Scheme.Modules.pullbackPushforwardAdjunction U.ι
  let adjP := liftAdjunctionOfObjectProperties adj hL hR
  have hunit (A : P.FullSubcategory) : IsIso (adjP.unit.app A) := by
    have heq : P.ι.map (adjP.unit.app A) = adj.unit.app A.obj := by
      simp [adjP, liftAdjunctionOfObjectProperties, Adjunction.mkOfHomEquiv_unit_app,
        adj.homEquiv_unit]
    have : IsIso (P.ι.map (adjP.unit.app A)) := by
      rw [heq]
      exact isIso_unit_of_structureDepthTwo X U hdepth hEBI A.obj A.property.1 A.property.2
    exact isIso_of_reflects_iso _ P.ι
  have hcounit (B : Q.FullSubcategory) : IsIso (adjP.counit.app B) := by
    have : IsIso adj.counit := adj.isIso_counit_of_iso
      ((Functor.isoWhiskerLeft (Scheme.Modules.pushforward U.ι)
        (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm).trans
          (Scheme.Modules.restrictFunctorAdjCounitIso U.ι))
    have heq : Q.ι.map (adjP.counit.app B) = adj.counit.app B.obj := by
      simp [adjP, liftAdjunctionOfObjectProperties, Adjunction.mkOfHomEquiv_counit_app,
        adj.homEquiv_counit]
    have : IsIso (Q.ι.map (adjP.counit.app B)) := by
      rw [heq]
      infer_instance
    exact isIso_of_reflects_iso _ Q.ι
  let (A : P.FullSubcategory) : IsIso (adjP.unit.app A) := hunit A
  let (B : Q.FullSubcategory) : IsIso (adjP.counit.app B) := hcounit B
  exact ⟨adjP.toEquivalence,
    Q.liftCompιIso (P.ι ⋙ Scheme.Modules.pullback U.ι) hL,
    P.liftCompιIso (Q.ι ⋙ Scheme.Modules.pushforward U.ι) hR⟩

end Stacks.AlgebraicGeometry.DepthTwoReflexiveExtension

end
