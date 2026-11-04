module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.LocalTorsionColimitOfConstructibles
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.SpecializationClosedSupportColimit
import StacksCore.Tactic.StacksAttribute

/-!
# Torsion étale sheaves supported in a specialization-closed set

Let `X` be a Noetherian scheme and let `E ⊆ X` be stable under specialization. A torsion abelian
sheaf on the small étale site of `X` whose support lies in `E` is a filtered colimit of
constructible abelian sheaves, each of whose supports lies in a closed subset of `E`. This is
Stacks 0F0N (1); part (2) is
`AlgebraicGeometry.exists_isFilteredColimit_isConstructibleModuleSheaf_isClosed_support`.

## Main results

* `exists_isFilteredColimit_isConstructibleAbelianSheaf_isClosed_support_of_torsion`: a torsion
  abelian sheaf supported in a specialization-closed `E` is a filtered colimit of constructible
  abelian sheaves with supports in closed subsets of `E` (Stacks 0F0N (1)).

## Implementation notes

Torsion is the local notion `Stacks.Torsion.torsionSheafProperty` (Stacks 0DD7), the same one at
which `AlgebraicGeometry.exists_isFilteredColimit_isConstructibleAbelianSheaf_of_qcqs`
(Stacks 03SA (2)) is stated.

## References

* [Stacks Project, Tag 0F0N](https://stacks.math.columbia.edu/tag/0F0N)
* [Stacks Project, Tag 03SA](https://stacks.math.columbia.edu/tag/03SA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Let `X` be a Noetherian scheme and let `E ⊆ X` be stable under specialization. A torsion
abelian sheaf `F` on the small étale site of `X` whose support is contained in `E` is a filtered
colimit of constructible abelian sheaves, each of whose supports is contained in a closed subset
of `E`. Here torsion is the local condition `Stacks.Torsion.torsionSheafProperty`. -/
@[stacks 0F0N "part (1), torsion abelian sheaves, torsion in the local sense of Stacks 0DD7",
  sga "4½ Arcata 4.3.3" "more general"]
public theorem exists_isFilteredColimit_isConstructibleAbelianSheaf_isClosed_support_of_torsion
    (B : BigEtaleSite.{u}) (X : B.Scheme) [IsNoetherian X.obj]
    (E : Set X.obj) (hE : StableUnderSpecialization E)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty (SmallEtale.topology B X.obj X.property) F)
    (hsupp : supportSheaf B X.obj X.property F ⊆ E) :
    ∃ (I : Type (u + 1)) (_ : SmallCategory I) (_ : IsFiltered I)
      (D : I ⥤ Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
      (ι : D ⟶ (Functor.const I).obj F), Nonempty (IsColimit (Cocone.mk F ι)) ∧
        ∀ i, IsConstructibleAbelianSheaf B X (D.obj i) ∧
          ∃ Z : Set X.obj, IsClosed Z ∧ Z ⊆ E ∧
            supportSheaf B X.obj X.property (D.obj i) ⊆ Z := by
  have hNoeth := (AlgebraicGeometry.isNoetherian_iff X.obj).mp (inferInstance : IsNoetherian X.obj)
  let : CompactSpace X.obj := hNoeth.2
  let : IsLocallyNoetherian X.obj := hNoeth.1
  let : QuasiSeparatedSpace X.obj := IsLocallyNoetherian.quasiSeparatedSpace
  exact exists_isFilteredColimit_isConstructibleAbelianSheaf_isClosed_support B X
    (fun G hG => exists_isFilteredColimit_isConstructibleAbelianSheaf_of_qcqs B X G hG)
    E hE F hF hsupp

end AlgebraicGeometry

end
