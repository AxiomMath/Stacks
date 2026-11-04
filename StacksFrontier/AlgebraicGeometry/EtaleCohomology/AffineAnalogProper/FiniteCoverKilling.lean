module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AffineAnalogProper.IntegralCoverVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AffineAnalogProper.RestrictionThroughUnit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitCohomologyRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FirstCohomologyKilling.BoundaryRestriction
public import StacksFrontier.AlgebraicGeometry.PartTwoResidue.Complete

/-!
# Killing a cohomology class on a closed subscheme by a finite surjective cover

Let `X` be an affine scheme, `Z ⊂ X` a closed subscheme, `M` a finite abelian group, `q ≥ 1` and
`ξ ∈ H^q_ét(Z, M)`. There is a finite surjective morphism `X' ⟶ X` of finite presentation such
that `ξ` pulls back to zero on `X' ×_X Z`. This is part (2) of [Stacks, Tag 09ZD].

The proof is the one of the Stacks project. Part (1) of the same tag gives an integral surjective
`X'' ⟶ X` such that every closed subscheme of `X''` has no higher cohomology with constant finite
coefficients, so `ξ` dies on the closed subscheme `X'' ×_X Z` of `X''`. By [Stacks, Tag 09YZ],
`X''` is the limit of a directed inverse system of schemes `X'_i` finite and of finite
presentation over `X`; base change along `Z ⟶ X` makes `X'' ×_X Z` the limit of the affine system
`X'_i ×_X Z`, and by [Stacks, Tag 03Q6] (`exists_le_restriction_eq_zero`) the class already dies
on some `X'_i ×_X Z`.

## Main results

* `Stacks.EtaleCohomology.etaleCohomologyRestrictionMap_eq_zero_iff` — a class restricts to zero
  exactly when its image under the exact inverse-image functor vanishes.
* `Stacks.EtaleCohomology.etaleCohomologyRestrictionMap_restrictionMap_eq_zero_iff` — restricting
  in two steps kills the same classes as restricting along the composite.
* `Stacks.EtaleCohomology.exists_isFinite_restriction_eq_zero_of_isIntegralHom` — a class which
  dies on the base change of an integral morphism dies on the base change of a finite stage of
  finite presentation through which it factors.
* `Stacks.EtaleCohomology.exists_isFinite_surjective_restriction_eq_zero_of_iso_constantSheaf` —
  Stacks 09ZD (2) for a sheaf isomorphic to a constant sheaf.
* `Stacks.EtaleCohomology.exists_isFinite_surjective_restriction_constantSheaf_eq_zero` —
  **Stacks 09ZD (2)**.

## References

* [Stacks Project, Tag 09ZD](https://stacks.math.columbia.edu/tag/09ZD)
* [Stacks Project, Tag 09YZ](https://stacks.math.columbia.edu/tag/09YZ)
* [Stacks Project, Tag 03Q6](https://stacks.math.columbia.edu/tag/03Q6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

section Restriction

variable {X Y Z : Scheme.{u}}

/-- Composing with the `Ext⁰` class of an isomorphism does not change whether a class is zero. -/
private theorem comp_mk₀_eq_zero_iff_of_isIso {C : Type*} [Category C] [Abelian C]
    [HasExt.{u + 1} C] {A B D : C} (f : A ⟶ B) [IsIso f] {n : ℕ} (y : Ext.{u + 1} B D n) :
    (Ext.mk₀ f).comp y (zero_add n) = 0 ↔ y = 0 :=
  ⟨fun h => (Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso f n).1
    (h.trans (map_zero _).symm), fun h => by rw [h, Ext.comp_zero]⟩

/-- **A class restricts to zero exactly when its inverse image vanishes.** The restriction map
is the image under the exact inverse-image functor followed by precomposition with the
constant-sheaf comparison, an isomorphism. -/
theorem etaleCohomologyRestrictionMap_eq_zero_iff (a : Y ⟶ X)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) {q : ℕ} (x : Sheaf.H.{u + 1} F q) :
    etaleCohomologyRestrictionMap.{u, 0, u + 1} a F q x = 0 ↔
      x.mapExactFunctor (etaleAbelianInverseImage.{u, 0} a) = 0 := by
  rw [etaleCohomologyRestrictionMap_apply]
  exact comp_mk₀_eq_zero_iff_of_isIso
    ((etaleAbelianInverseImageConstantIso.{u, 0} a).app (AddCommGrpCat.of (ULift ℤ))).inv _

/-- **Restriction in two steps.** The restriction along `a` of a class, restricted further along
`b`, vanishes exactly when the restriction along `b ≫ a` does. -/
theorem etaleCohomologyRestrictionMap_restrictionMap_eq_zero_iff (a : Y ⟶ X) (b : Z ⟶ Y)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) {q : ℕ} (x : Sheaf.H.{u + 1} F q) :
    etaleCohomologyRestrictionMap.{u, 0, u + 1} b _ q
        (etaleCohomologyRestrictionMap.{u, 0, u + 1} a F q x) = 0 ↔
      etaleCohomologyRestrictionMap.{u, 0, u + 1} (b ≫ a) F q x = 0 := by
  rw [etaleCohomologyRestrictionMap_eq_zero_iff, etaleCohomologyRestrictionMap_eq_zero_iff,
    etaleCohomologyRestrictionMap_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    ← mapExactFunctor_etaleAbelianInverseImage_comp_eq_zero_iff a b x]
  exact comp_mk₀_eq_zero_iff_of_isIso
    ((etaleAbelianInverseImage.{u, 0} b).map
      ((etaleAbelianInverseImageConstantIso.{u, 0} a).app (AddCommGrpCat.of (ULift ℤ))).inv) _

/-- A class restricts to zero when the inverse image of the sheaf has vanishing cohomology in
that degree. -/
theorem etaleCohomologyRestrictionMap_eq_zero_of_iso (a : Y ⟶ X)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) {q : ℕ} (x : Sheaf.H.{u + 1} F q)
    {G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (e : G ≅ (etaleAbelianInverseImage.{u, 0} a).obj F) (h : Subsingleton (Sheaf.H.{u + 1} G q)) :
    etaleCohomologyRestrictionMap.{u, 0, u + 1} a F q x = 0 :=
  (Stacks.CohomologyVanishing.subsingleton_ext_of_iso_target e q h).elim _ _

end Restriction

/-- **A class killed on the base change of an integral morphism is killed at a finite stage.**
Let `Y` be affine, `g : Y_Z ⟶ Y` a closed immersion, `π : X' ⟶ Y` integral, `G` an abelian
sheaf on `Y_Z` and `ξ ∈ H^q(Y_Z, G)` restricting to zero on `X' ×_Y Y_Z`. Then there is a finite
morphism of finite presentation `π' : Y' ⟶ Y` through which `π` factors and such that `ξ`
restricts to zero on `Y' ×_Y Y_Z`.

Write `X' = lim X'_i` with `X'_i` finite of finite presentation over `Y` (Stacks 09YZ); base change
along `g` presents `X' ×_Y Y_Z` as the limit of the affine system `X'_i ×_Y Y_Z`, and Stacks 03Q6
moves the vanishing to a stage. -/
theorem exists_isFinite_restriction_eq_zero_of_isIntegralHom
    {Y YZ X' : Scheme.{u}} [IsAffine Y] (g : YZ ⟶ Y) [IsClosedImmersion g]
    (π : X' ⟶ Y) [IsIntegralHom π]
    (G : Sheaf YZ.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) (ξ : Sheaf.H.{u + 1} G q)
    (hξ : etaleCohomologyRestrictionMap.{u, 0, u + 1} (pullback.snd π g) G q ξ = 0) :
    ∃ (Y' : Scheme.{u}) (π' : Y' ⟶ Y), IsFinite π' ∧ FinitePresentation π' ∧
      (∃ h : X' ⟶ Y', h ≫ π' = π) ∧
      etaleCohomologyRestrictionMap.{u, 0, u + 1} (pullback.snd π' g) G q ξ = 0 := by
  let P := (Stacks.AlgebraicGeometry.Tag0817PartTwo.nonempty_integralLimitPresentation π).some
  let := P.indexPreorder
  have := P.indexNonempty
  have := P.indexDirected
  have : IsAffine YZ := isAffine_of_isAffineHom g
  let L : Over Y ⥤ Over YZ := Over.pullback g
  let c₀ := Over.liftCone P.diagram P.structureMap (Cone.mk X' P.limitCone) π
    (fun j => (P.compatible j).symm)
  let D : P.indexTypeᵒᵖ ⥤ Scheme.{u} := Over.lift P.diagram P.structureMap ⋙ L ⋙ Over.forget YZ
  let c : Cone D := (Over.forget YZ).mapCone (L.mapCone c₀)
  have hc : IsLimit c := isLimitOfPreserves (Over.forget YZ)
    (isLimitOfPreserves L (Over.isLimitLiftCone _ _ _ _ _ P.isLimit))
  have hD : ∀ j, IsAffine (D.obj j) := fun j => by
    have := P.stageFinite j
    have : IsAffine (((Functor.const P.indexTypeᵒᵖ).obj Y).obj j) := inferInstanceAs (IsAffine Y)
    have : IsAffine (P.diagram.obj j) := isAffine_of_isAffineHom (P.structureMap.app j)
    exact inferInstanceAs (IsAffine (pullback (P.structureMap.app j) g))
  have hDmap : ∀ {i j : P.indexTypeᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a) := fun {i j} a => by
    have := hD i
    have := hD j
    exact isAffineHom_of_isAffine _
  let i₀ : P.indexType := Classical.arbitrary _
  let q₀ : D.obj (op i₀) ⟶ YZ := pullback.snd (P.structureMap.app (op i₀)) g
  have hc₀ : c.π.app (op i₀) ≫ q₀ = pullback.snd π g := Over.w (L.map (c₀.π.app (op i₀)))
  have h₀ : etaleCohomologyRestrictionMap.{u, 0, u + 1} (c.π.app (op i₀)) _ q
      (etaleCohomologyRestrictionMap.{u, 0, u + 1} q₀ G q ξ) = 0 := by
    rwa [etaleCohomologyRestrictionMap_restrictionMap_eq_zero_iff, hc₀]
  obtain ⟨i, hi, hres⟩ := LimitSiteBridge.exists_le_restriction_eq_zero D c hc i₀ _ q _ h₀
  have hDq : D.map (homOfLE hi).op ≫ q₀ = pullback.snd (P.structureMap.app (op i)) g :=
    Over.w (L.map ((Over.lift P.diagram P.structureMap).map (homOfLE hi).op))
  rw [etaleCohomologyRestrictionMap_restrictionMap_eq_zero_iff, hDq] at hres
  exact ⟨P.diagram.obj (op i), P.structureMap.app (op i), P.stageFinite _,
    P.stageFinitePresentation _, ⟨P.limitCone.app (op i), (P.compatible _).symm⟩, hres⟩

/-- **Stacks 09ZD (2) for a sheaf isomorphic to a constant sheaf.** Let `Y` be affine,
`g : Y_Z ⟶ Y` a closed immersion, `M` a finite abelian group, `G ≅ M̲` on `Y_Z`, `q ≥ 1` and
`ξ ∈ H^q(Y_Z, G)`. There is a finite surjective `π : Y' ⟶ Y` of finite presentation such that `ξ`
restricts to zero on `Y' ×_Y Y_Z`. -/
theorem exists_isFinite_surjective_restriction_eq_zero_of_iso_constantSheaf
    {Y YZ : Scheme.{u}} [IsAffine Y] (g : YZ ⟶ Y) [IsClosedImmersion g]
    (M : AddCommGrpCat.{u + 1}) [Finite M] (G : Sheaf YZ.smallEtaleTopology AddCommGrpCat.{u + 1})
    (e : G ≅ (constantSheaf YZ.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M) (q : ℕ)
    (hq : 0 < q) (ξ : Sheaf.H.{u + 1} G q) :
    ∃ (Y' : Scheme.{u}) (π : Y' ⟶ Y), IsFinite π ∧ Surjective π ∧ FinitePresentation π ∧
      etaleCohomologyRestrictionMap.{u, 0, u + 1} (pullback.snd π g) G q ξ = 0 := by
  obtain ⟨X'', π'', hint, hsurj, hvan⟩ := exists_isIntegralHom_surjective_forall_subsingleton_H Y
  have : IsClosedImmersion (pullback.fst π'' g) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback π'' g).flip
      ‹IsClosedImmersion g›
  have h0 : etaleCohomologyRestrictionMap.{u, 0, u + 1} (pullback.snd π'' g) G q ξ = 0 :=
    etaleCohomologyRestrictionMap_eq_zero_of_iso _ G ξ
      (((etaleAbelianInverseImageConstantIso.{u, 0} (pullback.snd π'' g)).app M).symm ≪≫
        (etaleAbelianInverseImage.{u, 0} (pullback.snd π'' g)).mapIso e.symm)
      (hvan _ (pullback.fst π'' g) M q hq)
  obtain ⟨Y', π, hfin, hfp, ⟨h, hh⟩, hres⟩ :=
    exists_isFinite_restriction_eq_zero_of_isIntegralHom g π'' G q ξ h0
  have : Surjective (h ≫ π) := hh ▸ hsurj
  exact ⟨Y', π, hfin, Surjective.of_comp h π, hfp, hres⟩

/-- **Stacks Project, Tag 09ZD, part (2).** Let `X` be an affine scheme, `i : Z ⟶ X` a closed
immersion, `M` a finite abelian group, `q ≥ 1` and `ξ ∈ H^q_ét(Z, M)`. There is a finite
surjective morphism `π : X' ⟶ X` of finite presentation such that `ξ` pulls back to zero in
`H^q_ét(X' ×_X Z, M)`. -/
theorem exists_isFinite_surjective_restriction_constantSheaf_eq_zero
    (X : Scheme.{u}) [IsAffine X] (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i]
    (M : AddCommGrpCat.{u + 1}) [Finite M] (q : ℕ) (hq : 0 < q)
    (ξ : Sheaf.H.{u + 1} ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M) q) :
    ∃ (X' : Scheme.{u}) (π : X' ⟶ X), IsFinite π ∧ Surjective π ∧ FinitePresentation π ∧
      etaleCohomologyRestrictionMap.{u, 0, u + 1} (pullback.snd π i) _ q ξ = 0 :=
  exists_isFinite_surjective_restriction_eq_zero_of_iso_constantSheaf i M _ (Iso.refl _) q hq ξ

end Stacks.EtaleCohomology

end
