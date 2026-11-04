module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StrictlyHenselianVanishing
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.StrictlyHenselianVanishing

/-!
# Étale cohomology of a strictly henselian local scheme on the small étale site of a scheme

The spectrum of a strictly henselian local ring has no higher étale cohomology. This file
states and proves that for abelian sheaves on `AlgebraicGeometry.Scheme.smallEtaleTopology`,
the small étale site of a bare scheme, rather than on the size-bounded small étale site cut
out of a chosen big étale site.

## Main results

* `AlgebraicGeometry.Scheme.hasSheafify_smallEtaleTopology_succ`: abelian sheafification is
  available on the small étale site of a scheme with coefficients in the successor of the
  scheme universe.
* `Stacks.StrictlyHenselian.projective_constantSheaf_smallEtaleTopology`: over a strictly
  henselian local ring the constant abelian sheaf on the integers is a projective object.
* `Stacks.StrictlyHenselian.subsingleton_etaleCohomology_smallEtaleTopology`: hence the
  positive-degree étale cohomology of every abelian sheaf vanishes.

## References

* [Stacks Project, Tag 03QO](https://stacks.math.columbia.edu/tag/03QO)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.Scheme

/-- Abelian sheaves on the small étale site of a scheme can be sheafified with coefficients in
the successor of the scheme universe. -/
public instance hasSheafify_smallEtaleTopology_succ (S : Scheme.{u}) :
    HasSheafify S.smallEtaleTopology AddCommGrpCat.{u + 1} := by
  let B := BigEtaleSite.containing S
  let hS := BigEtaleSite.contains_containing S
  let : ∀ X : (S.Etale)ᵒᵖ,
      HasLimitsOfShape (StructuredArrow X (SmallEtale.toEtaleSite B S hS).op)
        AddCommGrpCat.{u + 1} :=
    fun _ ↦ hasLimitsOfShape_of_essentiallySmall.{u} _ _
  exact Functor.IsDenseSubsite.hasSheafify_of_isEquivalence
    (SmallEtale.topology B S hS) S.smallEtaleTopology (SmallEtale.toEtaleSite B S hS)

end AlgebraicGeometry.Scheme

namespace Stacks.StrictlyHenselian

open AlgebraicGeometry

/-- On the small étale site of the spectrum of a strictly henselian local ring, the constant
abelian sheaf on the integers is projective. -/
public theorem projective_constantSheaf_smallEtaleTopology
    (R : Type u) [CommRing R] [StrictlyHenselianLocalRing R] :
    Projective ((constantSheaf (Spec (.of R)).smallEtaleTopology
      AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift ℤ))) := by
  let S : Scheme.{u} := Spec (.of R)
  let B := BigEtaleSite.containing S
  let hS : B.Contains S := BigEtaleSite.contains_containing S
  let G := SmallEtale.toEtaleSite B S hS
  let J := SmallEtale.topology B S hS
  let K := S.smallEtaleTopology
  let A := AddCommGrpCat.{u + 1}
  let : ∀ X : (S.Etale)ᵒᵖ, HasLimitsOfShape (StructuredArrow X G.op) A :=
    fun _ ↦ hasLimitsOfShape_of_essentiallySmall.{u} _ _
  let hterm := SmallEtale.finalIsTerminal B S hS
  let : PreservesFiniteColimits (Sheaf.Γ J A) :=
    globalSections_preservesFiniteColimits B R hS
  let : Functor.PreservesEpimorphisms
      ((sheafSections J A).obj (op (SmallEtale.final B S hS))) :=
    Functor.PreservesEpimorphisms.of_iso (Sheaf.ΓNatIsoSheafSections J A hterm)
  have hPJ : Projective ((constantSheaf J A).obj (AddCommGrpCat.of (ULift ℤ))) :=
    (constantSheafAdj J A hterm).map_projective _ (projective_ulift_int.{u + 1})
  have hci : MorphismProperty.ContainsIdentities (@Etale : MorphismProperty Scheme.{u}) :=
    ⟨fun _ => inferInstance⟩
  have hT' : IsTerminal (G.obj (SmallEtale.final B S hS)) :=
    MorphismProperty.Over.mkIdTerminal _ _
  exact Projective.of_iso
    ((equivCommuteConstant J A K G hterm hT').app (AddCommGrpCat.of (ULift ℤ)))
    ((Functor.IsDenseSubsite.sheafEquiv J K G A).toAdjunction.map_projective _ hPJ)

/-- Positive-degree étale cohomology of an abelian sheaf on the small étale site of the
spectrum of a strictly henselian local ring vanishes. -/
@[stacks 03QO "vanishing of positive-degree étale cohomology, on the small étale site"]
public theorem subsingleton_etaleCohomology_smallEtaleTopology
    (R : Type u) [CommRing R] [StrictlyHenselianLocalRing R]
    [HasExt.{w} (Sheaf (Spec (.of R)).smallEtaleTopology AddCommGrpCat.{u + 1})]
    (F : Sheaf (Spec (.of R)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (p : ℕ) (hp : 1 ≤ p) :
    Subsingleton (Sheaf.H.{w, u + 1} F p) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by lia : p ≠ 0)
  have := projective_constantSheaf_smallEtaleTopology R
  exact CategoryTheory.Abelian.Ext.subsingleton_of_projective _ _ n

end Stacks.StrictlyHenselian

end
