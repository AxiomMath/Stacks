module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BasePasting
public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionOfRightDerivedFunctors
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusResolution
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.AbelianDerivedBaseChangeCriteria

/-!
# Invertibility of a descended base change comparison at a complex computing both sides

Let

```
A --G'--> C
|         |
F         F'
v         v
B --G-->  D
```

be a square of additive functors between abelian categories with a transformation
`τ : F ⋙ G ⟶ G' ⋙ F'`, and suppose that the derived functor of `G` is computed degreewise
(`e : G ⋙ Qh ≅ Qh ⋙ RG`, as for an exact `G`).  The comparison
`Stacks.Cohomology.BaseChange.derived F F' G G' τ e : RF ⋙ RG ⟶ RG' ⋙ RF'` is characterized by its
value after the derived-functor unit of `RF`.  This file records the consequence that is used to
prove such a comparison invertible: at a bounded below complex `K` of `A` whose terms are right
acyclic for `F`, whose images under `G'` are right acyclic for `F'`, and at whose terms `τ` is
invertible, the comparison is invertible at `K` — provided the derived functor of `G'` is also
computed degreewise at `K`.  For `K` a single object placed in degree zero the hypotheses are
conditions on that object alone.

This is Leray's acyclicity lemma ([Stacks, Tag 015E]) applied twice, to `F` at `K` and to `F'`
at `G'K`: both sides of the comparison are then computed by the complexes `G(F K)` and
`F'(G' K)`, between which the comparison is `τ` applied degreewise.

## Main results

* `Stacks.Cohomology.BaseChange.isIso_derived_app_Qh_of_degreewise`: the comparison is invertible
  at `K` when the terms of `K` are right acyclic for `F`, their images under `G'` are right acyclic
  for `F'`, `τ` is invertible at every term, and the unit of `RG'` is invertible at `K`; this is
  `Stacks.Cohomology.BaseChange.isIso_derived_app_Qh_of_acyclic` with its three unit hypotheses
  supplied by Leray's acyclicity lemma.
* `Stacks.Cohomology.BaseChange.isIso_derived_app_single_of_rightAcyclic`: the same at a single
  object `X` in degree zero, from right acyclicity of `X` for `F` and of `G' X` for `F'` and
  invertibility of `τ` at `X`.

## References

* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
* [Stacks Project, Tag 0736](https://stacks.math.columbia.edu/tag/0736)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.BaseChange

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [EnoughInjectives A] [EnoughInjectives B] [EnoughInjectives C]
  (F : A ⥤ B) (F' : C ⥤ D) (G : B ⥤ D) (G' : A ⥤ C)
  [F.Additive] [F'.Additive] [G.Additive] [G'.Additive]
  (τ : F ⋙ G ⟶ G' ⋙ F')
  (e : G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ≅
    DerivedCategory.Plus.Qh ⋙ G.rightDerivedFunctorPlus)

/-- **The comparison is invertible at a complex computing both sides.**  If every term of `K` is
right acyclic for `F`, every `G'`-image of a term is right acyclic for `F'`, `τ` is invertible at
every term and the unit of `RG'` is invertible at `K`, then `derived F F' G G' τ e` is invertible
at the image of `K`. -/
theorem isIso_derived_app_Qh_of_degreewise (K : HomotopyCategory.Plus A)
    (hF : ∀ n : ℤ, F.rightAcyclic (K.obj.as.X n))
    (hτ : ∀ n : ℤ, IsIso (τ.app (K.obj.as.X n)))
    (hac : ∀ n : ℤ, F'.rightAcyclic (G'.obj (K.obj.as.X n)))
    [IsIso (G'.rightDerivedFunctorPlusUnit.app K)] :
    IsIso ((derived F F' G G' τ e).app (DerivedCategory.Plus.Qh.obj K)) :=
  isIso_derived_app_Qh_of_acyclic F F' G G' τ e K
    (Functor.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic F K hF) inferInstance
    (Functor.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic F' _ hac) hτ

/-- **The comparison is invertible at an object computing both sides.**  If `X` is right acyclic
for `F`, `G' X` is right acyclic for `F'` and `τ` is invertible at `X`, then
`derived F F' G G' τ e` is invertible at `X` placed in degree zero, provided the derived functor
of `G'` is computed degreewise (for instance, `G'` exact). -/
theorem isIso_derived_app_single_of_rightAcyclic [IsIso G'.rightDerivedFunctorPlusUnit] (X : A)
    (hF : F.rightAcyclic X) (hτ : IsIso (τ.app X)) (hac : F'.rightAcyclic (G'.obj X)) :
    IsIso ((derived F F' G G' τ e).app ((DerivedCategory.Plus.singleFunctor A 0).obj X)) := by
  let K := (HomotopyCategory.Plus.singleFunctor A 0).obj X
  let i : K.obj.as.X 0 ≅ X := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X
  have hz : ∀ n : ℤ, n ≠ 0 → IsZero (K.obj.as.X n) := fun n hn =>
    HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 X n hn
  have : IsIso (G'.rightDerivedFunctorPlusUnit.app K) := NatIso.isIso_app_of_isIso _ K
  have h := isIso_derived_app_Qh_of_degreewise F F' G G' τ e K
    (fun n => by
      rcases eq_or_ne n 0 with rfl | hn
      · exact F.rightAcyclic.prop_of_iso i.symm hF
      · have : Injective (K.obj.as.X n) := (hz n hn).injective
        exact Functor.rightAcyclic_of_injective _ _)
    (fun n => by
      rcases eq_or_ne n 0 with rfl | hn
      · exact (NatTrans.isIso_app_iff_of_iso τ i).2 hτ
      · exact ⟨⟨0, (Functor.map_isZero _ (hz n hn)).eq_of_src _ _,
          (Functor.map_isZero _ (hz n hn)).eq_of_src _ _⟩⟩)
    (fun n => by
      rcases eq_or_ne n 0 with rfl | hn
      · exact F'.rightAcyclic.prop_of_iso (G'.mapIso i).symm hac
      · have : Injective (G'.obj (K.obj.as.X n)) :=
          (Functor.map_isZero G' (hz n hn)).injective
        exact Functor.rightAcyclic_of_injective _ _)
  exact (NatTrans.isIso_app_iff_of_iso (derived F F' G G' τ e)
    ((Functor.singleFunctorPlusIsoCompQh (A := A) 0).app X)).2 h

end Stacks.Cohomology.BaseChange

end
