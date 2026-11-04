module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.EulerCharacteristicComparison
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.SchemeIsoDegree
public import StacksFrontier.AlgebraicGeometry.Picard.TorsionSmoothProjectiveCurve.Degree

/-!
# The degree on the Picard group is invariant under isomorphisms of curves

Let `e : Y ⟶ X` be an isomorphism of schemes and `f : X ⟶ Spec k` proper of dimension at most
one. Pullback along `e` identifies `Pic(X)` with `Pic(Y)`
(`Stacks.Picard.ofSchemeAddEquivOfIso`), and it preserves the degree of
`Stacks.Picard.ofSchemeDegree`, `Y` being a curve over `k` through `e ≫ f`.

## Main results

* `Stacks.Picard.ofSchemeDegree_schemePullbackClass_of_isIso`: the degree is invariant under
  pullback along an isomorphism of curves.
* `AlgebraicGeometry.invertibleCurveDegree_eq_of_bijective_algebraMap`: the degree does not
  change when the ground field is replaced by an isomorphic one, for instance `k` by the residue
  field of the unique point of `Spec k`.

## References

* [Stacks Project, Tag 0AYR](https://stacks.math.columbia.edu/tag/0AYR)
* [Stacks Project, Tag 0C1Z](https://stacks.math.columbia.edu/tag/0C1Z)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Picard

/-- **The degree is invariant under pullback along an isomorphism of curves.** -/
theorem ofSchemeDegree_schemePullbackClass_of_isIso (k : Type u) [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (e : Y ⟶ X) [IsIso e] [IsProper (e ≫ f)]
    (hX : topologicalKrullDim X ≤ 1) (hY : topologicalKrullDim Y ≤ 1) (c : ofScheme X) :
    ofSchemeDegree k (e ≫ f) hY (schemePullbackClass e c) = ofSchemeDegree k f hX c := by
  obtain ⟨L, hL, rfl⟩ : ∃ (L : X.Modules)
      (hL : Stacks.SheafOfModules.IsInvertible X.presheaf
        (Stacks.RingedSpace.structureIsSheaf X.toRingedSpace) L),
      Stacks.SheafOfModules.picardClass X.presheaf
        (Stacks.RingedSpace.structureIsSheaf X.toRingedSpace) L hL = c :=
    ⟨_, _, classOf_picardRepresentative X.toRingedSpace c⟩
  show ofSchemeDegree k (e ≫ f) hY (pullbackClass e.toLRSHom.toShHom _) = _
  rw [pullbackClass_classOf e.toLRSHom.toShHom L hL]
  refine (ofSchemeDegree_picardClass k (e ≫ f) hY _ _).trans
    (Eq.trans ?_ (ofSchemeDegree_picardClass k f hX L hL).symm)
  unfold invertibleCurveDegree
  congr 1
  · exact finsum_congr fun n => by
      rw [show (Stacks.RingedSpace.pullbackFunctor e.toLRSHom.toShHom).obj L =
        (Scheme.Modules.pullback e).obj L from rfl,
        finrank_cohomologyOverField_pullback k e f L n]
  · exact finsum_congr fun n => by rw [finrank_cohomologyOverField_unit_pushforward k e f n]

end Stacks.Picard

namespace AlgebraicGeometry

/-- **The degree over an isomorphic ground field.** Let `κ` be a field extension of `k` whose
structure map is bijective, and let `Z` be proper of dimension at most one over `κ`, hence over
`k`. Then the degree of an invertible module is the same over `k` and over `κ`. -/
theorem invertibleCurveDegree_eq_of_bijective_algebraMap (k κ : Type u) [Field k] [Field κ]
    [Algebra k κ] (hbij : Function.Bijective (algebraMap k κ)) {Z : Scheme.{u}}
    (f : Z ⟶ Spec (.of k)) (g : Z ⟶ Spec (.of κ)) [IsProper f] [IsProper g]
    (hcompat : ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom =
      ((Scheme.ΓSpecIso (.of κ)).inv ≫ g.appTop).hom.comp (algebraMap k κ))
    (hdim : topologicalKrullDim Z ≤ 1) (L : Z.Modules)
    [SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 L] :
    invertibleCurveDegree k f hdim L = invertibleCurveDegree κ g hdim L := by
  have h1 : Module.finrank k κ = 1 := by
    rw [← (AlgEquiv.ofBijective (Algebra.ofId k κ) hbij).toLinearEquiv.finrank_eq]
    exact Module.finrank_self k
  have hF : ∀ (F : Z.Modules) (n : ℕ), Module.finrank k (cohomologyOverField k f F n) =
      Module.finrank κ (cohomologyOverField κ g F n) := fun F n => by
    rw [finrank_cohomologyOverField_eq_finrank_mul k κ f g hcompat F n, h1, one_mul]
  unfold invertibleCurveDegree
  congr 1
  · exact finsum_congr fun n => by rw [hF]
  · exact finsum_congr fun n => congrArg _ (congrArg _ (hF _ n))

end AlgebraicGeometry

end
