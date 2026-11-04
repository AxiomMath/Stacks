module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkExactnessCriterion

/-!
# Acyclicity of a complex of abelian étale sheaves is tested on the geometric stalks

Let `B` be a big étale site containing a scheme `S`. A complex of abelian sheaves on the small
étale site of `S` is acyclic as soon as, at every geometric point of `S`, the induced complex of
stalks is exact in every degree. This upgrades the short-complex criterion of Stacks 03PU,
`AlgebraicGeometry.exact_iff_etaleStalk_exact`, to a statement about an arbitrary homological
complex, which is the form needed to transfer the acyclicity of a resolution from its stalks to
the sheaves themselves.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.exact_of_forall_etaleStalkSheafFiber_exact` — a short complex of abelian
  sheaves whose complexes of geometric stalks are all exact is exact.
* `AlgebraicGeometry.acyclic_of_etaleStalk_exact` — a homological complex of abelian sheaves all
  of whose short complexes become exact at every geometric stalk is acyclic.
* `AlgebraicGeometry.additive_etaleStalkSheafFiber` — the stalk functor at a geometric point is
  additive, so it may be applied degreewise to a homological complex.

## Implementation notes

Exactness at a degree is by definition the exactness of the short complex
`CategoryTheory.HomologicalComplex.sc` there, and that short complex commutes with applying an
additive functor degreewise: `((F.mapHomologicalComplex c).obj K).sc i` and `(K.sc i).map F` are
definitionally equal. The hypothesis is therefore phrased with `ShortComplex.map`, which needs
only that the stalk functor preserves zero morphisms, and a user holding the acyclicity of the
degreewise image complex may feed it in directly.

The reflection step itself is the joint faithfulness of the geometric stalk functors,
`AlgebraicGeometry.jointlyFaithful_etaleStalkSheafFiber`: a sheaf all of whose geometric stalks
vanish vanishes, applied to the homology of the short complex.

## References

* [Stacks Project, Tag 03PU](https://stacks.math.columbia.edu/tag/03PU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry

section Acyclicity

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 03PU.** A short complex of abelian sheaves on the small étale site of `S` whose
complex of stalks at every geometric point of `S` is exact is itself exact. -/
public theorem exact_of_forall_etaleStalkSheafFiber_exact
    (T : ShortComplex (Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{max (u + 1) v}))
    (h : ∀ s : GeometricPoint S,
      (T.map ((geometricPointSitePoint B S hS s).sheafFiber
        (A := AddCommGrpCat.{max (u + 1) v}))).Exact) :
    T.Exact := by
  have : AB5OfSize.{u, u} AddCommGrpCat.{max (u + 1) v} :=
    AB5OfSize_of_univLE.{u, u, max (u + 1) v, max (u + 1) v} _
  rw [T.exact_iff_isZero_homology, IsZero.iff_id_eq_zero]
  apply (jointlyFaithful_etaleStalkSheafFiber.{u, v} B S hS).map_injective
  intro s
  have hz : IsZero (((geometricPointSitePoint B S hS s).sheafFiber
      (A := AddCommGrpCat.{max (u + 1) v})).obj T.homology) :=
    (Iso.isZero_iff (T.mapHomologyIso _)).1 ((T.map _).exact_iff_isZero_homology.1 (h s))
  simpa using hz.eq_of_src (𝟙 _) 0

/-- **Stacks 03PU** for a homological complex: a complex of abelian sheaves on the small étale
site of `S` whose short complexes all become exact at every geometric stalk is acyclic. -/
public theorem acyclic_of_etaleStalk_exact
    {ι : Type w} {c : ComplexShape ι}
    (K : HomologicalComplex
      (Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{max (u + 1) v}) c)
    (h : ∀ (s : GeometricPoint S) (i : ι),
      ((K.sc i).map ((geometricPointSitePoint B S hS s).sheafFiber
        (A := AddCommGrpCat.{max (u + 1) v}))).Exact) :
    K.Acyclic := fun i =>
  (K.exactAt_iff i).2
    (exact_of_forall_etaleStalkSheafFiber_exact.{u, v} B S hS _ fun s => h s i)

/-- The stalk functor at a geometric point of `S` is additive: it preserves finite colimits,
hence binary biproducts. -/
public theorem additive_etaleStalkSheafFiber (s : GeometricPoint S) :
    ((geometricPointSitePoint B S hS s).sheafFiber
      (A := AddCommGrpCat.{max (u + 1) v})).Additive := by
  have : AB5OfSize.{u, u} AddCommGrpCat.{max (u + 1) v} :=
    AB5OfSize_of_univLE.{u, u, max (u + 1) v, max (u + 1) v} _
  have hbip : PreservesBinaryBiproducts ((geometricPointSitePoint B S hS s).sheafFiber
      (A := AddCommGrpCat.{max (u + 1) v})) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

end Acyclicity

end AlgebraicGeometry

end
