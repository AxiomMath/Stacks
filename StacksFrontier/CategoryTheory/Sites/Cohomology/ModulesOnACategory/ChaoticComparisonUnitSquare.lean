module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.ChaoticComparisonSliceSheafification

/-!
# The unit square of the chaotic comparison over an object of `C`

Let `C` carry a Grothendieck topology `τ`, let `τ'` be the chaotic topology, `O` a `τ`-sheaf of
rings and `ε : (C_τ, O_τ) ⟶ (C_τ', O_τ')` the comparison morphism, so that `ε^*` is
`τ`-sheafification of presheaves of `O`-modules and `ε_*` the forgetful functor. Fix an object `U`
of `C` and write `G = (-|_U)` for restriction along `C/U ⥤ C`.

With `η` the unit of `Lε^* ⊣ Rε_*`, `η'` that of `Lε_U^* ⊣ Rε_{U*}`,
`ρ = ChaoticComparisonLeray.derivedRestrictionPushforwardIso` and
`α = ChaoticComparisonSliceSheafification.derivedSheafifyRestrictionIso`, this file proves

`G(η_M) ≫ ρ(Lε^*M) = η'_{G M} ≫ Rε_{U*}(α_M)`.

Equivalently `ρ` is the mate of `α` along the two derived adjunctions, by
`CategoryTheory.mateEquiv_eq_of_unit`.

Under derived sections over the terminal object `id_U` of `C/U` three of the four edges are
invertible: `ρ` and `α` are isomorphisms, and `isIso_rGamma_unit_derivedRestriction` is the third,
by hypothesis (2) of Stacks 0GZS. So the fourth is, and `MorphismsOverAnObject.derivedSectionsIso`
identifies it with `RΓ(U, η_M)`. With `cartesianEquivalenceOfSectionwise` this gives Stacks 0GZS
from its hypothesis (2) alone.

## Main results

* `Stacks.ModulesOnACategory.ChaoticComparison.htpyUnitSquare`: the unit square read on homotopy
  categories, which is the underived sheafification unit square applied in each degree.
* `Stacks.ModulesOnACategory.ChaoticComparison.derivedUnitSquare`: the identity above.
* `Stacks.ModulesOnACategory.ChaoticComparison.isIso_rGamma_unit_of_isLocallyKFlatAcyclic`: under
  hypothesis (2) of Stacks 0GZS the `ε`-unit at a cartesian object becomes invertible on derived
  sections over every object of `C`.
* `Stacks.ModulesOnACategory.ChaoticComparison.cartesianEquivalenceOfLocallyKFlatAcyclic`:
  Stacks 0GZS, the equivalence between cartesian objects and `QC(O)`, under the hypotheses of the
  source.

## Implementation notes

The identity is not formal: `ρ` comes from the uniqueness of right derived functors while `α` is
lifted from a degreewise comparison, and the unit of `Lε^* ⊣ Rε_*` is not the localization of the
underived one. By `CategoryTheory.Localization.natTrans_ext` it is checked at the objects `Qh X`,
where it reduces to the underived square
`ChaoticComparisonSliceSheafification.unit_comp_map_sheafifyRestrictionHom` in each degree. The
diagram chase is done on variables, in `unitSquareChase`, so that the elaborator does not unfold
the derived-category construction.

The objects and the morphisms of `C` and the section rings of `O` lie in three independent
universes `u`, `v` and `r`, and the module sections in `max u v r w` for a free `w`, the universe
at which the sheaves of modules on the site and on each slice form a Grothendieck abelian category.

## References

* [Stacks Project, Tag 0GZS](https://stacks.math.columbia.edu/tag/0GZS)
* [Stacks Project, Tag 0D6G](https://stacks.math.columbia.edu/tag/0D6G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.ModulesOnACategory.MorphismsOverAnObject
open Stacks.Sites.OverModules (overRingPresheaf restrictionFunctor)
open Stacks.ModulesOnACategory.QuasiCoherentEquivalence
open Stacks.ModulesOnACategory.PullbackQuasiCoherentBaseChange (baseChangeDataOfComm)

namespace Stacks.ModulesOnACategory.ChaoticComparison

/-! ### The rearrangement, on variables -/

section Chase

universe v₁ u₁

/-- A diagram chase: if `k` has a retraction `k'` and the nine squares `hρ`, …, `hsq` commute, then
`g ≫ r = n ≫ a`. -/
private theorem unitSquareChase {D : Type u₁} [Category.{v₁} D]
    {A B T T' Y Z₁ Z₂ W₁ W₂ V N N₁ N₂ S : D}
    (g : A ⟶ B) (r : B ⟶ T) (n : A ⟶ N) (a : N ⟶ T) (k : T ⟶ T') (k' : T' ⟶ T)
    (d : B ⟶ Y) (r' : Y ⟶ T') (c₁ : A ⟶ Z₁) (c₂ : Z₁ ⟶ Y)
    (p₁ : Z₁ ⟶ W₁) (p₂ : W₁ ⟶ W₂) (p₃ : W₂ ⟶ V) (p₄ : V ⟶ T')
    (q₁ : A ⟶ Z₂) (q₂ : Z₂ ⟶ W₁) (m₁ : N ⟶ N₁) (m₂ : N₁ ⟶ N₂) (m₃ : N₂ ⟶ V)
    (n' : Z₂ ⟶ N₁) (s₁ : Z₂ ⟶ S) (s₂ : S ⟶ N₂) (t : S ⟶ W₂)
    (hk : k ≫ k' = 𝟙 T)
    (hρ : r ≫ k = d ≫ r')
    (hunit : g ≫ d = c₁ ≫ c₂)
    (hfac : c₂ ≫ r' = p₁ ≫ p₂ ≫ p₃ ≫ p₄)
    (hψ : c₁ ≫ p₁ = q₁ ≫ q₂)
    (hα : a ≫ k = m₁ ≫ m₂ ≫ m₃ ≫ p₄)
    (hη : n ≫ m₁ = q₁ ≫ n')
    (hunit' : n' ≫ m₂ = s₁ ≫ s₂)
    (hβ : s₂ ≫ m₃ = t ≫ p₃)
    (hsq : q₂ ≫ p₂ = s₁ ≫ t) :
    g ≫ r = n ≫ a := by
  have : IsSplitMono k := .mk' ⟨k', hk⟩
  rw [← cancel_mono k, Category.assoc, Category.assoc, hρ, hα, reassoc_of% hunit, hfac,
    reassoc_of% hψ, reassoc_of% hsq, ← reassoc_of% hβ, ← reassoc_of% hunit', ← reassoc_of% hη]

/-- An identity `l ≫ 𝟙 = e ≫ F.map c` persists after inserting a second identity on the left and
composing `c` with an identity on the right. -/
private theorem comp_ids_of_comp_id {D : Type u₁} [Category.{v₁} D] {E : Type u₁}
    [Category.{v₁} E] (F : D ⥤ E) {X : E} {Z W : D} (l : X ⟶ F.obj W) (e : X ⟶ F.obj Z)
    (c : Z ⟶ W) (h : l ≫ 𝟙 (F.obj W) = e ≫ F.map c) :
    l ≫ 𝟙 (F.obj W) ≫ 𝟙 (F.obj W) = e ≫ F.map (c ≫ 𝟙 W) := by
  rw [Category.id_comp, Category.comp_id c, h]


/-- Moving the inverse of a natural isomorphism `e` across an identity: from
`(e.inv.app Z₀ ≫ c) ≫ r = w` it follows that `c ≫ r = e.hom.app Z₀ ≫ w`. -/
private theorem facOfFac {D₀ E₀ : Type u₁} [Category.{v₁} D₀] [Category.{v₁} E₀]
    {F₁ F₂ : D₀ ⥤ E₀} (e : F₁ ≅ F₂) (Z₀ : D₀) {C₀ T₀ : E₀} (c : F₁.obj Z₀ ⟶ C₀) (r : C₀ ⟶ T₀)
    (w : F₂.obj Z₀ ⟶ T₀) (h : (e.inv.app Z₀ ≫ c) ≫ r = w) :
    c ≫ r = e.hom.app Z₀ ≫ w := by
  rw [← h, ← Category.assoc, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]

/-- Cancelling a morphism `j'` with right inverse `j` off the tail of a four-fold composite. -/
private theorem compCancelTail {D₀ : Type u₁} [Category.{v₁} D₀] {A₀ B₁ B₂ B₃ B₄ C₀ : D₀}
    (a₁ : A₀ ⟶ B₁) (a₂ : B₁ ⟶ B₂) (a₃ : B₂ ⟶ B₃) (a₄ : B₃ ⟶ B₄) (j' : B₄ ⟶ C₀) (j : C₀ ⟶ B₄)
    (hj : j' ≫ j = 𝟙 B₄) {f : A₀ ⟶ C₀} (hf : f = a₁ ≫ a₂ ≫ a₃ ≫ a₄ ≫ j') :
    f ≫ j = a₁ ≫ a₂ ≫ a₃ ≫ a₄ := by
  rw [hf]; simp only [Category.assoc, hj, Category.comp_id]

/-- A functor on a four-fold composite. -/
private theorem mapComp₄ {D₀ E₀ : Type u₁} [Category.{v₁} D₀] [Category.{v₁} E₀] (F : D₀ ⥤ E₀)
    {A₀ B₁ B₂ B₃ B₄ : D₀} (a₁ : A₀ ⟶ B₁) (a₂ : B₁ ⟶ B₂) (a₃ : B₂ ⟶ B₃) (a₄ : B₃ ⟶ B₄) :
    F.map (a₁ ≫ a₂ ≫ a₃ ≫ a₄) = F.map a₁ ≫ F.map a₂ ≫ F.map a₃ ≫ F.map a₄ := by
  simp only [Functor.map_comp]

/-- A functor takes an isomorphism to one. -/
private theorem mapHomInvId {D₀ E₀ : Type u₁} [Category.{v₁} D₀] [Category.{v₁} E₀]
    (F : D₀ ⥤ E₀) {A₀ B₀ : D₀} (e : A₀ ≅ B₀) : F.map e.hom ≫ F.map e.inv = 𝟙 (F.obj A₀) := by
  rw [← F.map_comp, e.hom_inv_id, F.map_id]

/-- A functor preserves an identity between two composites. -/
private theorem map_comp_eq_map_comp {D₀ E₀ : Type*} [Category D₀] [Category E₀]
    (F : D₀ ⥤ E₀) {A₀ B₀ B₀' C₀ : D₀} {f₁ : A₀ ⟶ B₀} {g₁ : B₀ ⟶ C₀} {f₂ : A₀ ⟶ B₀'}
    {g₂ : B₀' ⟶ C₀} (h : f₁ ≫ g₁ = f₂ ≫ g₂) : F.map f₁ ≫ F.map g₁ = F.map f₂ ≫ F.map g₂ := by
  rw [← F.map_comp, ← F.map_comp, h]

end Chase

/-! ### The unit square on homotopy categories -/

section UnitSquare

universe w u v r

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{r})
  [HasSheafify J AddCommGrpCat.{max u v r w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r w}]
  (U : C) [HasSheafify (J.over U) AddCommGrpCat.{max u v r w}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v r w}]

/-- The complex-level counterpart of `ChaoticComparisonLeray.htpyComparison`: the comparison of
the two composites `ε_* ⋙ (-|_U)` and `(-|_U) ⋙ ε_{U*}` applied degreewise.  The two underived
composites are one functor, so both halves have identity components. -/
def cplxComparison :
    (epsilonPushforward.{w} R).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (restrictionFunctor.{v, u, r, max u v r w} R.obj U).mapHomologicalComplex
            (ComplexShape.up ℤ) ≅
      (sheafRestriction.{w} R U).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (sliceEpsilonPushforward.{w} R U).mapHomologicalComplex (ComplexShape.up ℤ) :=
  Functor.mapHomologicalComplexCompIso
      (Iso.refl (epsilonPushforward.{w} R ⋙ restrictionFunctor.{v, u, r, max u v r w} R.obj U))
      (ComplexShape.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (sheafRestriction.{w} R U ⋙ sliceEpsilonPushforward.{w} R U))
      (ComplexShape.up ℤ)).symm

/-- The complex-level counterpart of `htpySheafifyComparison`: the sheafification square applied
degreewise, with the second half splitting `(ε^* ⋙ (-|_U))` and so having identity
components. -/
def cplxSheafifyComparison :
    (restrictionFunctor.{v, u, r, max u v r w} R.obj U).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (sliceEpsilonPullback.{w} R U).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (epsilonPullback.{w} R).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (sheafRestriction.{w} R U).mapHomologicalComplex (ComplexShape.up ℤ) :=
  Functor.mapHomologicalComplexCompIso (sheafifyRestrictionIso.{w} R U) (ComplexShape.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (epsilonPullback.{w} R ⋙ sheafRestriction.{w} R U)) (ComplexShape.up ℤ)).symm

omit [HasSheafify J AddCommGrpCat.{max u v r w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r w}]
  [HasSheafify (J.over U) AddCommGrpCat.{max u v r w}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v r w}] in
/-- `htpyComparison` at the class of a complex is the class of `cplxComparison`. -/
theorem htpyComparison_hom_app
    (Y : HomotopyCategory (SheafOfModules.{max u v r w} R) (ComplexShape.up ℤ)) :
    (htpyComparison.{w} R U).hom.app Y =
      (HomotopyCategory.quotient (PresheafOfModules.{max u v r w} (overRingPresheaf R.obj U))
          (ComplexShape.up ℤ)).map ((cplxComparison.{w} R U).hom.app Y.as) :=
  ((HomotopyCategory.quotient (PresheafOfModules.{max u v r w} (overRingPresheaf R.obj U))
    (ComplexShape.up ℤ)).map_comp _ _).symm

/-- `htpySheafifyComparison` at the class of a complex is the class of
`cplxSheafifyComparison`. -/
theorem htpySheafifyComparison_hom_app
    (X : HomotopyCategory (PresheafOfModules.{max u v r w} R.obj) (ComplexShape.up ℤ)) :
    (htpySheafifyComparison.{w} R U).hom.app X =
      (HomotopyCategory.quotient (SheafOfModules.{max u v r w} (overRingSheaf R U))
          (ComplexShape.up ℤ)).map ((cplxSheafifyComparison.{w} R U).hom.app X.as) :=
  ((HomotopyCategory.quotient (SheafOfModules.{max u v r w} (overRingSheaf R U))
    (ComplexShape.up ℤ)).map_comp _ _).symm

/-- **The sheafification unit square on complexes.**  The restriction to `C/U` of the unit of the
adjunction induced on complexes, followed by `cplxComparison`, is the unit of the induced
adjunction on the localized site followed by `ε_{U*}` of `cplxSheafifyComparison`. -/
theorem cplxUnitSquare (K : CochainComplex (PresheafOfModules.{max u v r w} R.obj) ℤ) :
    ((restrictionFunctor.{v, u, r, max u v r w} R.obj U).mapHomologicalComplex
        (ComplexShape.up ℤ)).map
          ((Adjunction.mapHomologicalComplexAdjunction (epsilonAdjunction.{w} R)
            (ComplexShape.up ℤ)).unit.app K) ≫
        (cplxComparison.{w} R U).hom.app
          (((epsilonPullback.{w} R).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) =
      (Adjunction.mapHomologicalComplexAdjunction
            (epsilonAdjunction.{w} (overRingSheaf R U)) (ComplexShape.up ℤ)).unit.app
          (((restrictionFunctor.{v, u, r, max u v r w} R.obj U).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) ≫
        ((sliceEpsilonPushforward.{w} R U).mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((cplxSheafifyComparison.{w} R U).hom.app K) :=
  HomologicalComplex.hom_ext _ _ fun n =>
    comp_ids_of_comp_id (sliceEpsilonPushforward.{w} R U) _ _ _
      (unit_comp_map_sheafifyRestrictionHom.{w} R U (K.X n))

/-- **The sheafification unit square on homotopy categories**: the image of `cplxUnitSquare`
under the quotient. -/
theorem htpyUnitSquare
    (X : HomotopyCategory (PresheafOfModules.{max u v r w} R.obj) (ComplexShape.up ℤ)) :
    ((restrictionFunctor.{v, u, r, max u v r w} R.obj U).mapHomotopyCategory
        (ComplexShape.up ℤ)).map
          ((Adjunction.mapHomotopyCategoryAdjunction (epsilonAdjunction.{w} R)
            (ComplexShape.up ℤ)).unit.app X) ≫
        (htpyComparison.{w} R U).hom.app
          (((epsilonPullback.{w} R).mapHomotopyCategory (ComplexShape.up ℤ)).obj X) =
      (Adjunction.mapHomotopyCategoryAdjunction (epsilonAdjunction.{w} (overRingSheaf R U))
            (ComplexShape.up ℤ)).unit.app
          (((restrictionFunctor.{v, u, r, max u v r w} R.obj U).mapHomotopyCategory
              (ComplexShape.up ℤ)).obj X) ≫
        ((sliceEpsilonPushforward.{w} R U).mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((htpySheafifyComparison.{w} R U).hom.app X) := by
  rw [htpyComparison_hom_app, htpySheafifyComparison_hom_app]
  exact map_comp_eq_map_comp
    (HomotopyCategory.quotient (PresheafOfModules.{max u v r w} (overRingPresheaf R.obj U))
      (ComplexShape.up ℤ)) (cplxUnitSquare.{w} R U X.as)

/-! ### The unit square on derived categories -/

/-- **The unit square of the chaotic comparison over `U`.**  With `G = (-|_U)`, `η` the unit of
`Lε^* ⊣ Rε_*`, `η'` that of `Lε_U^* ⊣ Rε_{U*}`, `ρ = derivedRestrictionPushforwardIso` and
`α = derivedSheafifyRestrictionIso`,

`G(η_M) ≫ ρ(Lε^*M) = η'_{G M} ≫ Rε_{U*}(α_M)`.

Equivalently `ρ` is the mate of `α` along the two derived adjunctions, by
`CategoryTheory.mateEquiv_eq_of_unit`. -/
theorem derivedUnitSquare (M : DMod.{w} R.obj) :
    (derivedRestriction.{w} R.obj U).map ((derivedEpsilonAdjunction.{w} R).unit.app M) ≫
        (derivedRestrictionPushforwardIso.{w} R U).hom.app
          ((epsilonPullback.{w} R).mapDerivedCategory.obj M) =
      (derivedEpsilonAdjunction.{w} (overRingSheaf R U)).unit.app
          ((derivedRestriction.{w} R.obj U).obj M) ≫
        (sliceDerivedEpsilonPushforward.{w} R U).map
          ((derivedSheafifyRestrictionIso.{w} R U).hom.app M) := by
  have key :
      (Functor.whiskerRight (derivedEpsilonAdjunction.{w} R).unit
            (derivedRestriction.{w} R.obj U) ≫
          Functor.whiskerLeft (epsilonPullback.{w} R).mapDerivedCategory
            (derivedRestrictionPushforwardIso.{w} R U).hom :
        derivedRestriction.{w} R.obj U ⟶
          (epsilonPullback.{w} R).mapDerivedCategory ⋙
            (sheafRestriction.{w} R U).mapDerivedCategory ⋙
              sliceDerivedEpsilonPushforward.{w} R U) =
      Functor.whiskerLeft (derivedRestriction.{w} R.obj U)
          (derivedEpsilonAdjunction.{w} (overRingSheaf R U)).unit ≫
        Functor.whiskerRight (derivedSheafifyRestrictionIso.{w} R U).hom
          (sliceDerivedEpsilonPushforward.{w} R U) := by
    refine Localization.natTrans_ext DerivedCategory.Qh
      (HomotopyCategory.quasiIso (PresheafOfModules.{max u v r w} R.obj)
          (ComplexShape.up ℤ)) fun X => ?_
    change (derivedRestriction.{w} R.obj U).map
          ((derivedEpsilonAdjunction.{w} R).unit.app (DerivedCategory.Qh.obj X)) ≫
        (derivedRestrictionPushforwardIso.{w} R U).hom.app
          ((epsilonPullback.{w} R).mapDerivedCategory.obj (DerivedCategory.Qh.obj X)) =
      (derivedEpsilonAdjunction.{w} (overRingSheaf R U)).unit.app
          ((derivedRestriction.{w} R.obj U).obj (DerivedCategory.Qh.obj X)) ≫
        (sliceDerivedEpsilonPushforward.{w} R U).map
          ((derivedSheafifyRestrictionIso.{w} R U).hom.app (DerivedCategory.Qh.obj X))
    have hu := Stacks.DerivedFunctor.derivedAdjunction_unit_app (epsilonAdjunction.{w} R)
      (derivedEpsilonPushforward.{w} R) (derivedEpsilonPushforwardUnit.{w} R)
      (exists_quasiIso_isKInjective.{w} R) X
    have hunit' := Stacks.DerivedFunctor.derivedAdjunction_unit_app
      (epsilonAdjunction.{w} (overRingSheaf R U))
      (derivedEpsilonPushforward.{w} (overRingSheaf R U))
      (derivedEpsilonPushforwardUnit.{w} (overRingSheaf R U))
      (exists_quasiIso_isKInjective.{w} (overRingSheaf R U))
      (((restrictionFunctor.{v, u, r, max u v r w} R.obj U).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj X)
    have hunit := map_comp_eq_map_comp (derivedRestriction.{w} R.obj U) hu
    have hρ := ((derivedRestrictionPushforwardIso.{w} R U).hom.naturality
      ((epsilonPullback.{w} R).mapDerivedCategoryFactorsh.hom.app X)).symm
    have hψ :=
        (restrictionFunctor.{v, u, r, max u v r w} R.obj
            U).mapDerivedCategoryFactorsh.hom.naturality
      ((Adjunction.mapHomotopyCategoryAdjunction (epsilonAdjunction.{w} R)
        (ComplexShape.up ℤ)).unit.app X)
    have hη := ((derivedEpsilonAdjunction.{w} (overRingSheaf R U)).unit.naturality
      ((restrictionFunctor.{v, u, r, max u v r w} R.obj U).mapDerivedCategoryFactorsh.hom.app
          X)).symm
    have hβ := ((sliceDerivedEpsilonPushforwardUnit.{w} R U).naturality
      ((htpySheafifyComparison.{w} R U).hom.app X)).symm
    have hsq := map_comp_eq_map_comp DerivedCategory.Qh (htpyUnitSquare.{w} R U X)
    have hfac := facOfFac
        (restrictionFunctor.{v, u, r, max u v r w} R.obj U).mapDerivedCategoryFactorsh
      (((epsilonPushforward.{w} R).mapHomotopyCategory (ComplexShape.up ℤ)).obj
        (((epsilonPullback.{w} R).mapHomotopyCategory (ComplexShape.up ℤ)).obj X)) _ _ _
      (derivedRestrictionPushforwardIso_fac.{w} R U
        (((epsilonPullback.{w} R).mapHomotopyCategory (ComplexShape.up ℤ)).obj X))
    have hαw := compCancelTail _ _ _ _ _ _
      (mapHomInvId (sheafRestriction.{w} R U).mapDerivedCategory
        ((epsilonPullback.{w} R).mapDerivedCategoryFactorsh.app X).symm)
      ((derivedSheafifyRestrictionIso_fac.{w} R U X).trans
        (derivedSheafifyRestrictionComparison_hom_app.{w} R U X))
    have hα := (((sliceDerivedEpsilonPushforward.{w} R U).map_comp _ _).symm.trans
        (congrArg (sliceDerivedEpsilonPushforward.{w} R U).map hαw)).trans
      (mapComp₄ (sliceDerivedEpsilonPushforward.{w} R U) _ _ _ _)
    have hk := mapHomInvId (sliceDerivedEpsilonPushforward.{w} R U)
      ((sheafRestriction.{w} R U).mapDerivedCategory.mapIso
        ((epsilonPullback.{w} R).mapDerivedCategoryFactorsh.app X))
    exact unitSquareChase _ _ _ _ _ _ _ _ _ _ _
      (DerivedCategory.Qh.map ((htpyComparison.{w} R U).hom.app
        (((epsilonPullback.{w} R).mapHomotopyCategory (ComplexShape.up ℤ)).obj X)))
      ((sliceDerivedEpsilonPushforwardUnit.{w} R U).app
        (((sheafRestriction.{w} R U).mapHomotopyCategory (ComplexShape.up ℤ)).obj
          (((epsilonPullback.{w} R).mapHomotopyCategory (ComplexShape.up ℤ)).obj X)))
      ((sliceDerivedEpsilonPushforward.{w} R U).map
        ((sheafRestriction.{w} R U).mapDerivedCategoryFactorsh.inv.app
          (((epsilonPullback.{w} R).mapHomotopyCategory (ComplexShape.up ℤ)).obj X)))
      _ _ _ _ _ _ _ _ _ hk hρ hunit hfac hψ hα hη hunit' hβ hsq
  exact NatTrans.congr_app key M

end UnitSquare

/-! ### Stacks 0GZS from its own hypothesis (2) -/

section Closing

universe w u v r

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{r})
  [HasSheafify J AddCommGrpCat.{max u v r w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r w}]
  [∀ X : C, HasSheafify (J.over X) AddCommGrpCat.{max u v r w}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{max u v r w}]
  (hO : ∀ (V : Cᵒᵖ) (x y : R.obj.obj V), x * y = y * x)

/-- **Hypothesis (2) of Stacks 0GZS gives the sectionwise comparison on `C`.**  Granting
hypothesis (2), for every cartesian `M` and every object `U` of `C` the `ε`-unit at `M` becomes
invertible on derived sections over `U`. -/
theorem isIso_rGamma_unit_of_isLocallyKFlatAcyclic
    (h2 : IsLocallyKFlatAcyclic.{w} R hO) (M : DMod.{w} R.obj)
    (hM : IsQC.{w} (baseChangeDataOfComm.{r, v, u, w} R.obj hO) M) (U : C) :
    IsIso ((RGamma.{w} R.obj (Opposite.op U)).map
      ((derivedEpsilonAdjunction.{w} R).unit.app M)) := by
  have hsq :
      (RGamma.{w} (overRingPresheaf R.obj U) (Opposite.op (Over.mk (𝟙 U)))).map
            ((derivedRestriction.{w} R.obj U).map
              ((derivedEpsilonAdjunction.{w} R).unit.app M)) ≫
          (RGamma.{w} (overRingPresheaf R.obj U) (Opposite.op (Over.mk (𝟙 U)))).map
            ((derivedRestrictionPushforwardIso.{w} R U).hom.app
              ((epsilonPullback.{w} R).mapDerivedCategory.obj M)) =
        (RGamma.{w} (overRingPresheaf R.obj U) (Opposite.op (Over.mk (𝟙 U)))).map
            ((derivedEpsilonAdjunction.{w} (overRingSheaf R U)).unit.app
              ((derivedRestriction.{w} R.obj U).obj M)) ≫
          (RGamma.{w} (overRingPresheaf R.obj U) (Opposite.op (Over.mk (𝟙 U)))).map
            ((sliceDerivedEpsilonPushforward.{w} R U).map
              ((derivedSheafifyRestrictionIso.{w} R U).hom.app M)) :=
    map_comp_eq_map_comp _ (derivedUnitSquare.{w} R U M)
  have hunit' : IsIso
      ((RGamma.{w} (overRingPresheaf R.obj U) (Opposite.op (Over.mk (𝟙 U)))).map
        ((derivedEpsilonAdjunction.{w} (overRingSheaf R U)).unit.app
          ((derivedRestriction.{w} R.obj U).obj M))) :=
    isIso_rGamma_unit_derivedRestriction.{w} R hO h2 M hM U
  have hα : IsIso ((RGamma.{w} (overRingPresheaf R.obj U)
      (Opposite.op (Over.mk (𝟙 U)))).map
        ((sliceDerivedEpsilonPushforward.{w} R U).map
          ((derivedSheafifyRestrictionIso.{w} R U).hom.app M))) := inferInstance
  have : IsIso ((RGamma.{w} (overRingPresheaf R.obj U)
      (Opposite.op (Over.mk (𝟙 U)))).map
        ((derivedRestrictionPushforwardIso.{w} R U).hom.app
          ((epsilonPullback.{w} R).mapDerivedCategory.obj M))) := inferInstance
  have : IsIso ((RGamma.{w} (overRingPresheaf R.obj U)
        (Opposite.op (Over.mk (𝟙 U)))).map
          ((derivedEpsilonAdjunction.{w} (overRingSheaf R U)).unit.app
            ((derivedRestriction.{w} R.obj U).obj M)) ≫
      (RGamma.{w} (overRingPresheaf R.obj U) (Opposite.op (Over.mk (𝟙 U)))).map
        ((sliceDerivedEpsilonPushforward.{w} R U).map
          ((derivedSheafifyRestrictionIso.{w} R U).hom.app M))) :=
    IsIso.comp_isIso' hunit' hα
  exact (NatIso.isIso_map_iff (derivedSectionsIso.{w} R.obj U) _).1
    (IsIso.of_isIso_fac_right hsq)

/-- Let `C` carry a Grothendieck topology `τ`, let `τ'` be the chaotic topology on `C` and let `O`
be a `τ`-sheaf of rings with commuting sections. Assume hypothesis (2) of the source: for every
object `U` of `C` and every K-flat complex `M^•` of `O(U)`-modules the canonical map
`M^• ⟶ RΓ((C/U)_τ, (M^• ⊗_{O(U)} O_U)^#)` is a quasi-isomorphism. Then `ε^*` and `Rε_*` are
mutually quasi-inverse equivalences between `QC(O)` and the full subcategory of `D(C_τ, O_τ)`
consisting of the objects `K` with `Rε_*K` in `QC(O)`.

Hypothesis (1) of the source, that `τ'` is the chaotic topology, is structural here: a module on
`(C_τ', O_τ')` *is* a presheaf of `O`-modules, `ε_*` is the forgetful functor and `ε^*` is
`τ`-sheafification. Hypothesis (2) is `IsLocallyKFlatAcyclic`, read on the localized site
`(C/U, τ)`. The commutativity `hO` gives the canonical base-change datum
`Stacks.ModulesOnACategory.PullbackQuasiCoherentBaseChange.baseChangeDataOfComm`; the cartesian
condition does not depend on the choice of datum.

The objects and the morphisms of `C` and the section rings lie in independent universes `u`, `v`
and `r`, and the modules in `max u v r w`; the site therefore need not be small, as is the case
for the associated affine site of a category fibred in groupoids (Stacks 0H0J). -/
@[stacks 0GZS]
def cartesianEquivalenceOfLocallyKFlatAcyclic (h2 : IsLocallyKFlatAcyclic.{w} R hO) :
    (IsCartesianPushforward.{w} R
          (baseChangeDataOfComm.{r, v, u, w} R.obj hO)).FullSubcategory ≌
      QC.{w} (baseChangeDataOfComm.{r, v, u, w} R.obj hO) :=
  cartesianEquivalenceOfSectionwise.{w} R (baseChangeDataOfComm.{r, v, u, w} R.obj hO)
    (fun M hM V => isIso_rGamma_unit_of_isLocallyKFlatAcyclic.{w} R hO h2 M hM V.unop)

/-- The equivalence of Stacks 0GZS is realized by `Rε_*`. -/
theorem cartesianEquivalenceOfLocallyKFlatAcyclic_functor
    (h2 : IsLocallyKFlatAcyclic.{w} R hO) :
    (cartesianEquivalenceOfLocallyKFlatAcyclic.{w} R hO h2).functor =
      restrictedPushforward.{w} R
        (IsQC.{w} (baseChangeDataOfComm.{r, v, u, w} R.obj hO)) :=
  rfl

/-- Under hypothesis (2) of Stacks 0GZS the unit `M ⟶ Rε_*(ε^*M)` of the derived adjunction is
invertible at every cartesian object `M`. -/
theorem isIso_unit_of_isLocallyKFlatAcyclic (h2 : IsLocallyKFlatAcyclic.{w} R hO)
    (M : DMod.{w} R.obj) (hM : IsQC.{w} (baseChangeDataOfComm.{r, v, u, w} R.obj hO) M) :
    IsIso ((derivedEpsilonAdjunction.{w} R).unit.app M) :=
  QuasiCoherentEquivalence.RGamma_jointly_conservative.{w} _
    (fun V => isIso_rGamma_unit_of_isLocallyKFlatAcyclic.{w} R hO h2 M hM V.unop)

end Closing

end Stacks.ModulesOnACategory.ChaoticComparison

end
