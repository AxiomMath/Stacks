module

public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.OnARingedSpace
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.RestrictOpenDerivedTensor
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.LocallyBoundedPullback
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.Restriction
import StacksCore.Tactic.StacksAttribute

/-!
# A locally bounded complex of flat modules is K-flat

Let `(W, 𝒪_W)` be a ringed space and `ℱ^•` a complex of `𝒪_W`-modules which is *locally
bounded* — every point has an open neighbourhood outside finitely many degrees of which the
complex restricts to zero — and whose terms are flat.  Then `ℱ^•` is K-flat.

[Stacks, Tag 06YQ] gives this for a complex bounded above, and a locally bounded complex need
not be bounded above: on `W = ⨆_n Spec k` a complex may be bounded on each member of a cover
with no global bound.  What closes the gap is that K-flatness is tested by the acyclicity of a
total tensor complex, and acyclicity is local on the space.

## Main results

* `Stacks.Cohomology.LocallyBoundedKFlat.acyclic_of_acyclic_restrict`: **acyclicity of a
  complex of `𝒪_W`-modules is local on an open cover of `W`.**
* `Stacks.Cohomology.LocallyBoundedKFlat.restrictTotalTensorIso`: **the total tensor complex
  commutes with restriction to an open subspace**, `(Tot(K ⊗_{𝒪_W} L))|_U ≅
  Tot(K|_U ⊗_{𝒪_U} L|_U)`.
* `Stacks.Cohomology.LocallyBoundedKFlat.kFlat_of_isLocallyBounded_of_flat`: **a locally
  bounded complex of flat `𝒪_W`-modules is K-flat.**

## Implementation notes

Both local statements are about restriction to an *open subspace*, `restrictFunctor`, and not
about restriction to a slice site: that is the spelling at which the comparison of the tensor
product with restriction ([Stacks, Tag 01CU]) and the colimit preservation the total complex
needs are already assembled, in
`StacksFrontier/Topology/Sheaves/Cohomology/KFlat/RestrictOpenDerivedTensor.lean`.  The vanishing
criterion, on the other hand, is local on the *site* — it is
`Stacks.SheafOfModules.isZero_of_coversTop` — and `isZero_restrict_iff` is the one crossing
between the two spellings, got from
`Stacks.Cohomology.RelativeMayerVietoris.modulePullbackOpenInclusionIso` and
`Stacks.Cohomology.DerivedOpenImmersion.isZero_modulePullback_ofRestrict_iff`.  It is also what
connects `Stacks.SheafOfModules.OnSpace.IsBoundedOn`, which is phrased on the slice, to the
bound the open-subspace statement consumes.

`restrictTotalTensorIso` is `CategoryTheory.Functor.mapBifunctorTotalIso` at the data
`RestrictOpenDerivedTensor.lean` collects; the derived-category consequence of the same data is
`Stacks.Cohomology.RestrictOpenDerivedTensor.derivedTensorRestrictNatIso`, which is about
`⊗^𝐋` on arbitrary objects and so cannot supply the complex-level statement needed here.

## References

* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [Stacks Project, Tag 06YN](https://stacks.math.columbia.edu/tag/06YN)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.HigherDirectImage
open Stacks.Cohomology.RestrictOpenDerivedTensor
open AlgebraicGeometry.RingedSpace.KFlatDerivedPullback (KFlat)

universe u

namespace Stacks.Cohomology.LocallyBoundedKFlat

variable (W : RingedSpace.{u, u})

/-- **Vanishing on an open subspace is vanishing on the slice over that open.**  The two
restrictions of a sheaf of modules to an open `U` — to the open subspace `(U, 𝒪_W|_U)` and to
the slice site `Opens W / U` — vanish together.

This is the one crossing between the two spellings of restriction used below: the first is
where the tensor product's compatibility with restriction lives, the second is where the
locality of vanishing lives. -/
theorem isZero_restrict_iff (U : Opens W.carrier)
    (M : RingedSpace.KFlatDerivedPullback.Modules W) :
    IsZero ((restrictFunctor W U).obj M) ↔ IsZero (M.over U) :=
  (Iso.isZero_iff
      ((Stacks.Cohomology.RelativeMayerVietoris.modulePullbackOpenInclusionIso W U).app M)).trans
    (Stacks.Cohomology.DerivedOpenImmersion.isZero_modulePullback_ofRestrict_iff W U M)

/-- A restricted complex is exact at `n` iff the restriction of its `n`-th cohomology vanishes. -/
private theorem exactAt_restrict_iff (U : Opens W.carrier)
    (K : CochainComplex (RingedSpace.KFlatDerivedPullback.Modules W) ℤ) (n : ℤ) :
    (((restrictFunctor W U).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).ExactAt n ↔
      IsZero ((restrictFunctor W U).obj (K.homology n)) :=
  (HomologicalComplex.exactAt_iff_isZero_homology _ n).trans
    (Iso.isZero_iff ((StacksDraft.DerivedCategoryHomology.mapHomologicalComplexHomologyIso
      (restrictFunctor W U) (ComplexShape.up ℤ) n).app K))

/-- **Acyclicity of a complex of `𝒪_W`-modules is local on an open cover of `W`.**  If
`⨆ i, V i = ⊤` and each restriction `K^•|_{V i}` is acyclic, then `K^•` is acyclic.

Restriction to an open subspace is exact, so it commutes with the formation of cohomology
(`StacksDraft.DerivedCategoryHomology.mapHomologicalComplexHomologyIso`); the hypothesis
therefore says that each cohomology sheaf of `K^•` restricts to zero on every member of the
cover, and vanishing of a sheaf of modules is local on the site
(`Stacks.SheafOfModules.isZero_of_coversTop`). -/
theorem acyclic_of_acyclic_restrict {ι : Type*} (V : ι → Opens W.carrier) (hV : iSup V = ⊤)
    (K : CochainComplex (RingedSpace.KFlatDerivedPullback.Modules W) ℤ)
    (h : ∀ i : ι, (((restrictFunctor W (V i)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K).Acyclic) :
    K.Acyclic := by
  have hcov : (Opens.grothendieckTopology W.carrier).CoversTop V :=
    (Opens.coversTop_iff _ V).2 hV
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  refine Stacks.SheafOfModules.isZero_of_coversTop hcov _ fun i => ?_
  exact (isZero_restrict_iff W (V i) _).1 ((exactAt_restrict_iff W (V i) K n).1 (h i n))

/-- **The total tensor complex commutes with restriction to an open subspace:**

`(Tot(K^• ⊗_{𝒪_W} L^•))|_U ≅ Tot(K^•|_U ⊗_{𝒪_U} L^•|_U)`.

`CategoryTheory.Functor.mapBifunctorTotalIso` at the data of
`StacksFrontier/Topology/Sheaves/Cohomology/KFlat/RestrictOpenDerivedTensor.lean`: the underived
comparison of [Stacks, Tag 01CU] with its two naturality squares, and the preservation by
restriction of the antidiagonal coproducts the total complex is built from. -/
def restrictTotalTensorIso (U : Opens W.carrier)
    (K L : CochainComplex (RingedSpace.KFlatDerivedPullback.Modules W) ℤ) :
    ((restrictFunctor W U).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (CochainComplex.KFlatBifunctor.totalComplex
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} W.sheaf) K L) ≅
      CochainComplex.KFlatBifunctor.totalComplex
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} (restrictToOpen W U).sheaf)
        (((restrictFunctor W U).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
        (((restrictFunctor W U).mapHomologicalComplex (ComplexShape.up ℤ)).obj L) :=
  letI := fun n : ℤ => restrictFunctor_preservesAntidiagonalCoproducts W U n
  Functor.mapBifunctorTotalIso
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} W.sheaf)
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} (restrictToOpen W U).sheaf)
    (restrictFunctor W U) (restrictFunctor W U) (restrictFunctor W U)
    (restrictTensorIso W U) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
    (fun f N => restrictTensorIso_naturality_left W U f N)
    (fun M {_ _} g => restrictTensorIso_naturality_right W U M g) K L

/-- **A locally bounded complex of flat `𝒪_W`-modules is K-flat.**  This is [Stacks, Tag 06YQ]
with its boundedness hypothesis localized: the complex is only assumed bounded on each member
of some open cover of `W`, which is strictly weaker than being bounded above.

For an acyclic `L^•`, the total complex `Tot(L^• ⊗_{𝒪_W} ℱ^•)` has to be acyclic, and by
`acyclic_of_acyclic_restrict` it is enough that each of its restrictions be.  On an open `V` on
which `ℱ^•` is bounded, `restrictTotalTensorIso` identifies that restriction with
`Tot(L^•|_V ⊗_{𝒪_V} ℱ^•|_V)`; there `ℱ^•|_V` is bounded above with flat terms
(`Stacks.Cohomology.TorAmplitude.isFlat_restrictModules`, [Stacks, Tag 0E8J] on an open
subspace) hence K-flat by [Stacks, Tag 06YQ], and `L^•|_V` is acyclic because restriction is
exact. -/
@[stacks 06YQ "with the boundedness hypothesis localized: a complex of flat O_W-modules which \
is merely LOCALLY bounded — bounded on each member of some open cover of W, which a complex \
with no global bound above can be — is K-flat. The source states it for a complex bounded \
above, which is this statement at the one-member cover W = W"]
theorem kFlat_of_isLocallyBounded_of_flat
    (F : CochainComplex (RingedSpace.KFlatDerivedPullback.Modules W) ℤ)
    (hF : Stacks.SheafOfModules.OnSpace.IsLocallyBounded W F)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := W.sheaf) (F.X i)) :
    KFlat W F := by
  classical
  choose V hxV hVb using hF
  choose s hs using hVb
  intro L hL
  refine acyclic_of_acyclic_restrict W V (eq_top_iff.2 fun x _ => ?_) _ fun x => ?_
  · exact Opens.mem_iSup.2 ⟨x, hxV x⟩
  · -- the restriction of `F` to `V x` is bounded above by the largest element of `s x`
    have hbd : ∃ n : ℤ, CochainComplex.IsStrictlyLE
        (((restrictFunctor W (V x)).mapHomologicalComplex (ComplexShape.up ℤ)).obj F) n := by
      refine ⟨(insert 0 (s x)).max' ⟨0, Finset.mem_insert_self 0 _⟩,
        (CochainComplex.isStrictlyLE_iff _ _).2 fun i hi => ?_⟩
      refine (isZero_restrict_iff W (V x) (F.X i)).2 (hs x i fun hmem => ?_)
      exact absurd ((insert 0 (s x)).le_max' i (Finset.mem_insert_of_mem hmem)) (by omega)
    -- its terms are again flat, and the restriction of `L` is again acyclic
    have hfl : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
        (O := (restrictToOpen W (V x)).sheaf)
        ((((restrictFunctor W (V x)).mapHomologicalComplex (ComplexShape.up ℤ)).obj F).X i) :=
      fun i => Stacks.Cohomology.TorAmplitude.isFlat_restrictModules W (V x) (F.X i) (hflat i)
    have hLres : (((restrictFunctor W (V x)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L).Acyclic :=
      fun n => (exactAt_restrict_iff W (V x) L n).2
        (Functor.map_isZero _ ((HomologicalComplex.exactAt_iff_isZero_homology _ n).1 (hL n)))
    have hkf := AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.kFlat_of_boundedAbove_of_flat
      (restrictToOpen W (V x)) _ hbd hfl _ hLres
    exact fun n => HomologicalComplex.ExactAt.of_iso (hkf n)
      (restrictTotalTensorIso W (V x) L F).symm

end Stacks.Cohomology.LocallyBoundedKFlat

end
