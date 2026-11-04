module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Data.ENat.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.DerivedCategoryOfTorsionSheaves
public import StacksCore.Tactic.StacksAttribute

/-!
# Cohomological dimension of a scheme and of a morphism of schemes

The cohomological dimension `cd(X)` of a quasi-compact, quasi-separated scheme is the least
extended natural number above which étale cohomology vanishes for every torsion abelian
sheaf. It is the smallest `d ∈ {0, 1, 2, …} ∪ {∞}` such that `H^q_ét(X, F) = 0` for all
`q > d` and every abelian torsion sheaf `F` on `X_ét`.

Relatively, the cohomological dimension `cd(f)` of a quasi-compact, quasi-separated morphism
of schemes `f : X ⟶ Y` is the smallest `d ∈ {0, 1, 2, …} ∪ {∞}` such that the higher direct
images `R^i f_* F` vanish for all `i > d` and every abelian torsion sheaf `F` on `X_ét`. For
`Y` the spectrum of a field, or more generally whenever the global sections of `Y_ét` compute
cohomology, this specialises to the absolute notion.

## Main definitions

* `AlgebraicGeometry.Scheme.IsEtaleCohomologyBound` says that all torsion abelian sheaves
  have vanishing étale cohomology above a given degree.
* `AlgebraicGeometry.Scheme.etaleCohomologicalDimension` is the least such bound, allowing
  infinity.
* `AlgebraicGeometry.Scheme.Hom.IsEtaleHigherDirectImageBound` says that all torsion abelian
  sheaves on the source have vanishing higher direct images above a given degree.
* `AlgebraicGeometry.Scheme.Hom.etaleCohomologicalDimension` is the least such bound, allowing
  infinity.

## Main results

* `AlgebraicGeometry.Scheme.etaleCohomologicalDimension_le` compares the dimension with any
  bound, and `AlgebraicGeometry.Scheme.etaleCohomologicalDimension_le_iff` says the
  comparison is an equivalence — so the infimum is attained, which is
  `AlgebraicGeometry.Scheme.isEtaleCohomologyBound_etaleCohomologicalDimension`.
* `AlgebraicGeometry.Scheme.Hom.isZero_rightDerived_etaleAbelianDirectImage` is the vanishing
  `R^i f_* F = 0` for torsion `F` and `i > cd(f)`, and
  `AlgebraicGeometry.Scheme.Hom.etaleCohomologicalDimension_le` says that `cd(f)` is least
  with that property. As in the absolute case the two combine into the equivalence
  `AlgebraicGeometry.Scheme.Hom.etaleCohomologicalDimension_le_iff`, the infimum being
  attained by
  `AlgebraicGeometry.Scheme.Hom.isEtaleHigherDirectImageBound_etaleCohomologicalDimension`.

## Implementation notes

The small étale site is Mathlib's `AlgebraicGeometry.Scheme.smallEtaleTopology`. Torsion is
the intrinsic, locally annihilated condition of Tag 0DD7,
`Stacks.Torsion.torsionSheafProperty`. Vanishing of an abelian cohomology group is expressed
by `Subsingleton`. The `sInf` of all bounds gives infinity when no finite bound exists, and
is attained because the predicate holds at `⊤`. The fixed universe for abelian sheaves and
their cohomology is the universe of objects of the small étale site.

The higher direct image `R^i f_*` is the right derived functor, in the sense of injective
resolutions, of the direct image `Stacks.EtaleCohomology.etaleAbelianDirectImage` of abelian
sheaves on the small étale sites; this is the same functor whose base change maps are studied
in Tag 0F02. The injective resolutions exist because abelian sheaves on a small étale site
form a Grothendieck abelian category. Vanishing of a sheaf is `CategoryTheory.Limits.IsZero`.

## References

* [Stacks Project, Tag 0F0Q](https://stacks.math.columbia.edu/tag/0F0Q)
* [Stacks Project, Tag 0F0Z](https://stacks.math.columbia.edu/tag/0F0Z)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- The least `d` with `Q a n` for all `a` satisfying `T a` and all `n > d` is attained, and
lies below `d` exactly when `d` is such a bound. -/
private theorem sInf_le_iff_forall_lt {α : Type*} {T : α → Prop} {Q : α → ℕ → Prop} (d : ℕ∞) :
    sInf {d : ℕ∞ | ∀ a, T a → ∀ n : ℕ, d < (n : ℕ∞) → Q a n} ≤ d ↔
      ∀ a, T a → ∀ n : ℕ, d < (n : ℕ∞) → Q a n := by
  refine ⟨fun h a ha n hn => ?_, fun h => sInf_le h⟩
  exact csInf_mem (s := {d : ℕ∞ | ∀ a, T a → ∀ n : ℕ, d < (n : ℕ∞) → Q a n})
    ⟨⊤, fun _ _ _ hn => by simp at hn⟩ a ha n (h.trans_lt hn)

/-- A bound for étale cohomology of all torsion abelian sheaves on `X`. -/
public abbrev IsEtaleCohomologyBound (X : Scheme.{u})
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (d : ℕ∞) : Prop :=
  ∀ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}),
    Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F →
      ∀ q : ℕ, d < (q : ℕ∞) → Subsingleton (Sheaf.H.{u + 1, u + 1} F q)

/-- **Stacks Project, Tag 0F0Q.** The least degree above which the étale cohomology
of every torsion abelian sheaf on a quasi-compact, quasi-separated scheme vanishes. -/
@[stacks 0F0Q]
public def etaleCohomologicalDimension (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})] : ℕ∞ :=
  sInf {d : ℕ∞ | IsEtaleCohomologyBound X d}

/-- The cohomological dimension is no greater than any étale cohomology bound. -/
public theorem etaleCohomologicalDimension_le (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (d : ℕ∞) (hd : IsEtaleCohomologyBound X d) :
    etaleCohomologicalDimension X ≤ d :=
  sInf_le hd

/-- The cohomological dimension itself is an étale cohomology bound. -/
public theorem isEtaleCohomologyBound_etaleCohomologicalDimension
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})] :
    IsEtaleCohomologyBound X (etaleCohomologicalDimension X) :=
  (sInf_le_iff_forall_lt _).1 le_rfl

/-- A number bounds the cohomological dimension exactly when it bounds the
cohomology of every torsion abelian sheaf. -/
public theorem etaleCohomologicalDimension_le_iff
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (d : ℕ∞) :
    etaleCohomologicalDimension X ≤ d ↔ IsEtaleCohomologyBound X d :=
  sInf_le_iff_forall_lt d

end AlgebraicGeometry.Scheme

/-! ### The cohomological dimension of a morphism

The relative version: the higher direct images `R^i f_*` of a torsion abelian sheaf on the
small étale site of the source vanish above `cd(f)`, and `cd(f)` is least with that property.
-/

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
  [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}]

/-- A bound for the higher direct images along `f` of all torsion abelian sheaves on the small
étale site of the source. -/
public abbrev IsEtaleHigherDirectImageBound (d : ℕ∞) : Prop :=
  ∀ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}),
    Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F →
      ∀ i : ℕ, d < (i : ℕ∞) →
        Limits.IsZero
          (((Stacks.EtaleCohomology.etaleAbelianDirectImage.{u, u + 1} f).rightDerived i).obj F)

/-- **Stacks Project, Tag 0F0Z.** The cohomological dimension `cd(f)` of a quasi-compact,
quasi-separated morphism of schemes `f : X ⟶ Y`: the smallest `d ∈ {0, 1, 2, …} ∪ {∞}` such
that `R^i f_* F = 0` for every abelian torsion sheaf `F` on `X_ét` and every `i > d`. -/
@[stacks 0F0Z]
public def etaleCohomologicalDimension [QuasiCompact f] [QuasiSeparated f] : ℕ∞ :=
  sInf {d : ℕ∞ | IsEtaleHigherDirectImageBound f d}

/-- The cohomological dimension of a morphism is no greater than any bound for the higher
direct images of torsion abelian sheaves. -/
public theorem etaleCohomologicalDimension_le [QuasiCompact f] [QuasiSeparated f] (d : ℕ∞)
    (hd : IsEtaleHigherDirectImageBound f d) :
    etaleCohomologicalDimension f ≤ d :=
  sInf_le hd

/-- The cohomological dimension of a morphism is itself a bound for the higher direct images
of torsion abelian sheaves: the infimum is attained, since `⊤` is such a bound. -/
public theorem isEtaleHigherDirectImageBound_etaleCohomologicalDimension
    [QuasiCompact f] [QuasiSeparated f] :
    IsEtaleHigherDirectImageBound f (etaleCohomologicalDimension f) :=
  (sInf_le_iff_forall_lt _).1 le_rfl

/-- **The defining vanishing property of `cd(f)`.** The higher direct image `R^i f_* F` of a
torsion abelian sheaf `F` on the small étale site of the source vanishes in every degree `i`
exceeding the cohomological dimension of `f`. -/
public theorem isZero_rightDerived_etaleAbelianDirectImage
    [QuasiCompact f] [QuasiSeparated f]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F)
    (i : ℕ) (hi : etaleCohomologicalDimension f < (i : ℕ∞)) :
    Limits.IsZero
      (((Stacks.EtaleCohomology.etaleAbelianDirectImage.{u, u + 1} f).rightDerived i).obj F) :=
  isEtaleHigherDirectImageBound_etaleCohomologicalDimension f F hF i hi

/-- A number bounds the cohomological dimension of a morphism exactly when it bounds the
degrees in which the higher direct images of torsion abelian sheaves can be nonzero. -/
public theorem etaleCohomologicalDimension_le_iff [QuasiCompact f] [QuasiSeparated f] (d : ℕ∞) :
    etaleCohomologicalDimension f ≤ d ↔ IsEtaleHigherDirectImageBound f d :=
  sInf_le_iff_forall_lt d

end AlgebraicGeometry.Scheme.Hom

end
