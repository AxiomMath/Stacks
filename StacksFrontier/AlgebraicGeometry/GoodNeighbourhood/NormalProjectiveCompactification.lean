module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.QuasiProjectiveOverAmpleBase
public import StacksFrontier.AlgebraicGeometry.HProjective.QuasiProjective
public import StacksFrontier.AlgebraicGeometry.AmpleWire.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteMorphismProjective.Projective
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.Composition
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.HProjective
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.Basic
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.FiniteType
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.RelativeNormal
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffineQuasiFinite
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A normal projective compactification of a normal affine variety

Let `k` be a field and `X` an affine scheme of finite type over `k` which is normal. Then `X` is
an open subscheme of a normal scheme `X̄` which is projective over `k`, in the sense of a closed
immersion into some `ℙⁿ_k`. This is the first step of the construction of Artin's good
neighbourhoods (SGA 4, Exposé XI, 3.3): the projective closure of `X`, replaced by its
normalization so that its singular locus has codimension at least two.

## The construction

* `X` is affine, so `X ⟶ Spec k` is quasi-affine of finite type and therefore quasi-projective
  ([Stacks, Tag 0B3H]). Over the affine base `Spec k` it is H-quasi-projective
  ([Stacks, Tag 087S] (2)): there is a quasi-compact immersion `i : X ⟶ ℙⁿ_k`.
* `X̄` is the normalization of `ℙⁿ_k` in `X` along `i`. The morphism `X ⟶ X̄` is an open
  immersion because `i` is separated and quasi-finite (Mathlib's form of [Stacks, Tag 03GW]). `X̄`
  is normal because `X` is, and `X̄ ⟶ ℙⁿ_k` is finite because `ℙⁿ_k` is Nagata
  ([Stacks, Tags 035A and 03GR]).
* A finite morphism is projective ([Stacks, Tag 0B3I]). A composite of projective morphisms over a
  quasi-compact quasi-separated base is projective ([Stacks, Tag 0C4P]). Over `Spec k`, which
  carries an ample invertible sheaf, projective implies H-projective ([Stacks, Tag 087S] (1)).

## Main results

* `AlgebraicGeometry.exists_isOpenImmersion_isProjectiveMorphism_isNormal`: the compactification.

## References

* SGA 4, Tome 3, Exposé XI, Proposition 3.3.
* [Stacks Project, Tag 0B3H](https://stacks.math.columbia.edu/tag/0B3H)
* [Stacks Project, Tag 087S](https://stacks.math.columbia.edu/tag/087S)
* [Stacks Project, Tag 03GR](https://stacks.math.columbia.edu/tag/03GR)
* [Stacks Project, Tag 0B3I](https://stacks.math.columbia.edu/tag/0B3I)
* [Stacks Project, Tag 0C4P](https://stacks.math.columbia.edu/tag/0C4P)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **A normal affine variety has a normal projective compactification.** Let `k` be a field and
let `X` be a normal affine scheme of finite type over `k`. Then there are a normal scheme `X̄`, an
open immersion `j : X ⟶ X̄` and an H-projective morphism `p̄ : X̄ ⟶ Spec k` with `j ≫ p̄ = p`.
If `X` is integral, so is `X̄`. -/
@[ega "IV 21.14.4" "Compactification step"]
theorem exists_isOpenImmersion_isProjectiveMorphism_isNormal (k : Type u) [Field k]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsAffine X] [LocallyOfFiniteType p] [IsNormal X] :
    ∃ (Xbar : Scheme.{u}) (j : X ⟶ Xbar) (pbar : Xbar ⟶ Spec (.of k)),
      IsOpenImmersion j ∧ j ≫ pbar = p ∧ IsProjectiveMorphism pbar ∧ IsNormal Xbar ∧
        (IsIntegral X → IsIntegral Xbar) := by
  -- a quasi-compact immersion into projective space
  have hqp : IsQuasiProjective p :=
    Stacks.HProjective.isQuasiProjective_of_isQuasiAffineHom p inferInstance
  obtain ⟨n, i, hi, hiqc, hip⟩ := isHQuasiProjective_of_isQuasiProjective p
    (Stacks.Ample.unitModule (Spec (.of k)))
    (Stacks.Ample.isAmple_unitModule_of_isAffine (Spec (.of k))) hqp
  have : IsImmersion i := hi
  have : QuasiCompact i := hiqc
  have : IsNoetherian X := by
    have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
    exact {}
  have hcomp : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite :=
    fun V hV => by
      have : IsNoetherian V :=
        { toIsLocallyNoetherian := inferInstance
          toCompactSpace := isCompact_iff_compactSpace.mp hV }
      exact finite_irreducibleComponents_of_isNoetherian
  -- the normalization of `ℙⁿ_k` in `X`
  let P := projectiveSpaceOver n (Spec (.of k))
  let π : P ⟶ Spec (.of k) := P ↘ Spec (.of k)
  have hπ : i ≫ π = p := hip
  have : LocallyOfFiniteType π := inferInstance
  have hNagata : IsNagataScheme P := isNagataScheme_of_locallyOfFiniteType_over_field k π
  have : LocallyOfFiniteType (i ≫ π) := hπ ▸ inferInstance
  have : LocallyOfFiniteType i := locallyOfFiniteType_of_comp i π
  have : IsReduced X := inferInstance
  have hfin : IsFinite i.fromNormalization :=
    isFinite_fromNormalization_of_locallyOfFiniteType i hNagata
  have hopen : IsOpenImmersion i.toNormalization := inferInstance
  -- projectivity
  have hπproj : IsProjectiveMorphism π := ⟨n, 𝟙 _, inferInstance, Category.id_comp _⟩
  have hproj : IsProjective (i.fromNormalization ≫ π) :=
    (Stacks.FiniteMorphismProjective.isProjective_of_isFinite i.fromNormalization).comp
      hπproj.isProjective
  refine ⟨i.normalization, i.toNormalization, i.fromNormalization ≫ π, hopen, ?_,
    isProjectiveMorphism_of_isProjective _ (Stacks.Ample.unitModule (Spec (.of k)))
      (Stacks.Ample.isAmple_unitModule_of_isAffine (Spec (.of k))) hproj,
    isNormal_normalization i hcomp, fun _ => inferInstance⟩
  rw [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization, hπ]

end AlgebraicGeometry

end
