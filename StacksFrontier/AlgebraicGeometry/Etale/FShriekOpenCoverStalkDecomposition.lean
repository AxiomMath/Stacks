module

public import StacksFrontier.Algebra.Category.Grp.DirectSumCoproduct
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekOpenCoverFiberPoints
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekStalkDecomposition

/-!
# The stalks of the Čech complex of an open covering

Let `f : X ⟶ Y` be a locally quasi-finite morphism of a big étale site, let `U : I → Opens X` be a
family of open subschemes of `X`, let `F` be an abelian sheaf on the small étale site of `X` and
let `s` be a geometric point of `Y`. The stalk at `s` of the degree-`p` term

`⊕_{i₀…i_p} f_{i₀…i_p,!}(F|_{X_{i₀…i_p}})`

of the Čech complex of Stacks 0F5H is the coproduct, over the geometric fibre of `f` over `s`, of
the stalks of `F` at the geometric points of that fibre, the stalk at `x` appearing once for every
tuple `(i₀, …, i_p)` of indices of opens containing `x`. The degree-zero term `f_! F` is the case
of the empty tuple, which is Stacks 0F5F part (1) itself.

## Main definitions

* `AlgebraicGeometry.SmallEtale.OpenCoverShriek.cechSummandStalkIso` — the stalk of the summand
  `f_{i₀…i_p,!}(F|_{X_{i₀…i_p}})` is the coproduct of the stalks of `F` over the part of the
  geometric fibre lying in `X_{i₀…i_p}`.
* `AlgebraicGeometry.SmallEtale.OpenCoverShriek.cechStalkZeroIso` — the degree-zero case.
* `AlgebraicGeometry.SmallEtale.OpenCoverShriek.cechStalkSuccIso` — the case of positive degree.
* `AlgebraicGeometry.SmallEtale.OpenCoverShriek.cechStalkIso` — **the stalk decomposition of the
  Čech complex**, in every degree.

## Implementation notes

Only the degree-`p` *object* is described, not the differential; the two together are the inputs
of `AlgebraicGeometry.SmallEtale.OpenCoverShriek.cechComplexObj_acyclic_of_stalkDecomposition`.

Taking the stalk of a term commutes with its direct sum for two unrelated reasons: evaluation at
`F` is a limit-and-colimit-preserving functor on the functor category in which the Čech complex of
Stacks 0F5H lives, and the stalk functor at a point of a site is a left adjoint. The summands are
then rewritten one at a time by Stacks 0F5F part (1), and the resulting iterated coproduct is
flattened and reindexed by
`AlgebraicGeometry.SmallEtale.OpenCoverShriek.coverFiberTupleEquiv`.

## References

* [Stacks Project, Tag 0F5H](https://stacks.math.columbia.edu/tag/0F5H)
* [Stacks Project, Tag 0F5F](https://stacks.math.columbia.edu/tag/0F5F)
* [Stacks Project, Tag 0F6S](https://stacks.math.columbia.edu/tag/0F6S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.SmallEtale.OpenCoverShriek

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  {I : Type (max (u + 1) v)} (U : I → (B.inclusion.obj X).Opens)
  (s : GeometricPoint Y.obj)
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})

/-- **Stacks 0F5F, part (1), for one summand of the Čech complex.** The stalk at `s` of the
summand `f_{i₀…i_p,!}(F|_{X_{i₀…i_p}})` belonging to a tuple of indices is the coproduct of the
stalks of `F` over the part of the geometric fibre of `f` lying in the intersection
`X_{i₀…i_p}`. -/
public def cechSummandStalkIso {n : ℕ} (t : Fin n → I) :
    ((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
        (A := AddCommGrpCat.{max (u + 1) v})).obj ((cechFamily.{u, v} B f U n t).obj F) ≅
      ∐ fun y : GeometricFiberPoint B (openSchemeι B (coverOpen B U t) ≫ f) s =>
        fiberPointStalk.{u, v} B f s F
          (openFiberPoint B (openSchemeι B (coverOpen B U t)) f s y) :=
  fShriekStalkIso.{u, v} B (openSchemeι B (coverOpen B U t) ≫ f) s _ ≪≫
    AddCommGrpCat.directSumCoproductIso.{u, max (u + 1) v} _ ≪≫
      Sigma.whiskerEquiv (Equiv.refl _) fun y =>
        (openFiberStalkIso.{u, v} B (openSchemeι B (coverOpen B U t)) f F s y).symm

/-- **Stacks 0F5F, part (1), read on the Čech complex.** The stalk at `s` of the degree-zero term
`f_! F` of the Čech complex is the coproduct of the stalks of `F` over the geometric fibre of `f`
over `s`, indexed by the empty tuple of covering indices at each point of the fibre. -/
public def cechStalkZeroIso :
    ((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
        (A := AddCommGrpCat.{max (u + 1) v})).obj ((cechComplexObj.{u, v} B f U F).X 0) ≅
      ∐ fun q : Σ x : GeometricFiberPoint B f s,
          Fin 0 → fiberPointCoverIndex.{u, v} B f U s x =>
        fiberPointStalk.{u, v} B f s F q.1 :=
  fShriekStalkIso.{u, v} B f s F ≪≫
    AddCommGrpCat.directSumCoproductIso.{u, max (u + 1) v}
      (fun x : GeometricFiberPoint B f s => fiberPointStalk.{u, v} B f s F x) ≪≫
    Sigma.whiskerEquiv
      (f := fun x : GeometricFiberPoint B f s => fiberPointStalk.{u, v} B f s F x)
      (g := fun q : Σ x : GeometricFiberPoint B f s,
          Fin 0 → fiberPointCoverIndex.{u, v} B f U s x =>
        fiberPointStalk.{u, v} B f s F q.1)
      (Equiv.sigmaUnique _ _).symm fun _ => Iso.refl _

/-- **The stalk of a Čech term of positive degree.** The stalk at `s` of the degree-`p + 1` term
`⊕_{i₀…i_{p+1}} f_{i₀…i_{p+1},!}(F|_{X_{i₀…i_{p+1}}})` of the Čech complex is the coproduct, over
the geometric fibre of `f` over `s`, of the stalks of `F` at the points of that fibre, the stalk
at `x` appearing once for every tuple of `p + 2` indices of opens containing `x`. -/
public def cechStalkSuccIso (n : ℕ) :
    ((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
        (A := AddCommGrpCat.{max (u + 1) v})).obj ((cechComplexObj.{u, v} B f U F).X (n + 1)) ≅
      ∐ fun q : Σ x : GeometricFiberPoint B f s,
          Fin (n + 1) → fiberPointCoverIndex.{u, v} B f U s x =>
        fiberPointStalk.{u, v} B f s F q.1 := by
  have hcol : HasColimitsOfShape (Discrete (Fin (n + 1) → I))
      (Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max (u + 1) v}) :=
    Sheaf.instHasColimitsOfShape
  exact ((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
        (A := AddCommGrpCat.{max (u + 1) v})).mapIso
      (PreservesCoproduct.iso ((evaluation _ _).obj F) (cechFamily.{u, v} B f U (n + 1))) ≪≫
    PreservesCoproduct.iso ((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
        (A := AddCommGrpCat.{max (u + 1) v}))
      (fun t => (cechFamily.{u, v} B f U (n + 1) t).obj F) ≪≫
    Sigma.whiskerEquiv (Equiv.refl _)
      (fun t => (cechSummandStalkIso.{u, v} B f U s F t).symm) ≪≫
    sigmaSigmaIso (fun t : Fin (n + 1) → I =>
        GeometricFiberPoint B (openSchemeι B (coverOpen B U t) ≫ f) s)
      (fun t y => fiberPointStalk.{u, v} B f s F
        (openFiberPoint B (openSchemeι B (coverOpen B U t)) f s y)) ≪≫
    Sigma.whiskerEquiv
      (f := fun p : Σ t : Fin (n + 1) → I,
          GeometricFiberPoint B (openSchemeι B (coverOpen B U t) ≫ f) s =>
        fiberPointStalk.{u, v} B f s F
          (openFiberPoint B (openSchemeι B (coverOpen B U p.1)) f s p.2))
      (g := fun q : Σ x : GeometricFiberPoint B f s,
          Fin (n + 1) → fiberPointCoverIndex.{u, v} B f U s x =>
        fiberPointStalk.{u, v} B f s F q.1)
      (coverFiberTupleEquiv.{u, v} B f s U (n + 1)) fun _ => Iso.refl _

/-- **The stalk decomposition of the Čech complex of an open covering.** In every degree `p`, the
stalk at a geometric point `s` of `Y` of the degree-`p` term of the Čech complex of Stacks 0F5H is
the coproduct, over the geometric fibre of `f` over `s`, of the stalks of `F` at the points of
that fibre, the stalk at `x` appearing once for every tuple of `p` indices of opens containing
`x`. -/
public def cechStalkIso (n : ℕ) :
    (∐ fun q : Σ x : GeometricFiberPoint B f s,
        Fin n → fiberPointCoverIndex.{u, v} B f U s x =>
      fiberPointStalk.{u, v} B f s F q.1) ≅
      ((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
        (A := AddCommGrpCat.{max (u + 1) v})).obj ((cechComplexObj.{u, v} B f U F).X n) :=
  match n with
  | 0 => (cechStalkZeroIso.{u, v} B f U s F).symm
  | n + 1 => (cechStalkSuccIso.{u, v} B f U s F n).symm

end AlgebraicGeometry.SmallEtale.OpenCoverShriek

end
