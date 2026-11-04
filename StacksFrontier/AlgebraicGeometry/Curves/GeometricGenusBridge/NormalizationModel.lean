module

public import StacksFrontier.AlgebraicGeometry.Curves.GeometricGenusModel
public import StacksFrontier.AlgebraicGeometry.Curves.ModelBaseChange
public import StacksFrontier.AlgebraicGeometry.Curves.ModelNormalization
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GeometricGenusIrreducible
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GeometricGenusNormalizationBound
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.SeparableDegreeFibres
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.IrreducibleSeparablyClosed
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.RegularSmooth

/-!
# The genus of the normalization is the geometric genus of Definition 0BYF

Let `K` be an algebraically closed field and let `C` be a proper curve over `K` (an integral
separated scheme of finite type and dimension one, proper over `K`). [Stacks, Tag 0BYF] defines
the geometric genus of `C` as the genus of a nonsingular projective model of `(C_L)_red` over an
extension field `L/K`, which is `AlgebraicGeometry.geometricGenusOfModel`. This file proves that
for every such `L` and every such model, that number is the genus of the normalization of `C`
over `K`, which is the quantity `AlgebraicGeometry.geometricGenus` sums over the one-dimensional
geometric components of a proper scheme.

## Main results

* `AlgebraicGeometry.genus_normalizationOverField_eq_geometricGenusOfModel`: for `K`
  algebraically closed, `C` a proper curve over `K`, `L/K` any field extension and `M` any
  nonsingular projective model of `(C_L)_red` over `L`,
  `genus (C^ν / K) = geometricGenusOfModel K L c M`.

## Proof

Over `K` itself, the normalization `C^ν` of `C_K ≅ C` is a nonsingular projective model of
`(C_K)_red` ([Stacks, Tag 0BY4] (1),
`AlgebraicGeometry.exists_nonsingularProjectiveModel_iso_normalization_reducedBaseChange'`), and
it is smooth over `K`, a perfect field, being regular. A smooth model over `K` base changes to a
model over `L`, and any model over `L` is isomorphic to it over `L` ([Stacks, Tag 0BY4] (4),
`AlgebraicGeometry.exists_iso_pullback_of_smooth_model`, which rests on the uniqueness of the
model, [Stacks, Tag 0BY1]). The genus is invariant under extension of the ground field
([Stacks, Tag 0BY9]).

## References

* [Stacks Project, Tag 0BYF](https://stacks.math.columbia.edu/tag/0BYF)
* [Stacks Project, Tag 0BY4](https://stacks.math.columbia.edu/tag/0BY4)
* [Stacks Project, Tag 0BY1](https://stacks.math.columbia.edu/tag/0BY1)
* [Stacks Project, Tag 0BY9](https://stacks.math.columbia.edu/tag/0BY9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **For a proper curve over an algebraically closed field, the genus of its normalization is
its geometric genus in the sense of [Stacks, Tag 0BYF].** Let `K` be algebraically closed, `C` a
proper curve over `K`, `L/K` a field extension and `M` a nonsingular projective model of
`(C_L)_red` over `L`. Then the genus of the normalization of `C` over `K` equals the genus of
`M`, that is `geometricGenusOfModel K L c M`.

The curve `C` is geometrically irreducible over `K`, being irreducible over a separably closed
field (`AlgebraicGeometry.geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed`); this is
the instance the definition of `geometricGenusOfModel` asks for. -/
theorem genus_normalizationOverField_eq_geometricGenusOfModel (K : Type u) [Field K]
    [IsAlgClosed K] {C : Scheme.{u}} (c : C ⟶ Spec (.of K)) [IsCurve K c] [IsProper c]
    (L : Type u) [Field L] [Algebra K L] :
    haveI : GeometricallyIrreducible c :=
      geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed K C c
    ∀ M : NonsingularProjectiveModel L (reducedBaseChange K L c)
        (reducedBaseChangeStructureMap K L c),
      genus (normalizationOverField K c ≫ c) = geometricGenusOfModel K L c M := by
  have : GeometricallyIrreducible c :=
    geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed K C c
  intro M
  -- the model over `K` given by the normalization of `C_K`
  obtain ⟨M₀, e₀, he₀⟩ :=
    exists_nonsingularProjectiveModel_iso_normalization_reducedBaseChange' K K c
  have : IsCurve K M₀.structureMap := M₀.isCurve
  have : IsProper M₀.structureMap := M₀.isProper_structureMap
  have hsm : Smooth M₀.structureMap :=
    smooth_of_isRegular_over_perfectField M₀.structureMap M₀.isRegular
  -- the genus of `M₀` is the genus of the normalization of `C`
  have hs : Spec.map (CommRingCat.ofHom (algebraMap K K)) = 𝟙 (Spec (.of K)) := by simp
  have : IsIso (Spec.map (CommRingCat.ofHom (algebraMap K K))) := by rw [hs]; infer_instance
  have hC : genus (normalizationOverField K
      (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap K K)))) ≫
        pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap K K)))) =
      genus (normalizationOverField K c ≫ c) :=
    genus_normalizationOverField_eq_of_isIso _ c
      (pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap K K))))
      (by rw [pullback.condition, hs, Category.comp_id])
  have h₀ : genus M₀.structureMap = genus (normalizationOverField K c ≫ c) := by
    rw [← hC, he₀, genus_comp_iso_eq K M₀.structureMap e₀]
  -- every model over `L` is the base change of `M₀`
  obtain ⟨e, he⟩ := exists_iso_pullback_of_smooth_model K K L c M₀ M hsm
  rw [geometricGenusOfModel_eq_genus, ← he, genus_comp_iso_eq L,
    genus_pullback_snd_eq K L (algebraMap K L) M₀.structureMap, h₀]

end AlgebraicGeometry

end
