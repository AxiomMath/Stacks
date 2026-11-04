module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.InternalHomSiteVariance.FirstVariable
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# Left exactness of internal Hom in the first argument, at a free ring universe

Let `(C, O)` be a ringed site and let `G` be a sheaf of `O`-modules. Part (1) of Stacks 0GMY
says that an exact sequence `F₁ → F₂ → F₃ → 0` of `O`-modules induces an exact sequence

`0 → Hom_O(F₃, G) → Hom_O(F₂, G) → Hom_O(F₁, G)`.

The proof is the one of the source: internal Hom in the first variable sends colimits to
limits (Stacks 03EN), hence cokernels to kernels, and a right-exact additive functor to an
opposite abelian category carries a right-exact sequence to a left-exact one. The colimit
statement is `Stacks.SheafOfModules.InternalHom.sheafInternalHomFunctor_preservesColimitsOfShape`
of `StacksFrontier.AlgebraicGeometry.InternalHomSiteVariance.FirstVariable`.

The two declarations below carry the tag for part (1). They are stated for
`AlgebraicGeometry.RingedSite.{u, v, w}` with the ring universe `w` free, which is the
generality of the source and the generality at which part (2) is stated
(`Stacks.SheafOfModules.InternalHom.internalHomSecondFunctor_exact` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomLeftExact`, tagged in
`StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.InternalHomSecondVariable`).
In particular they apply to `AlgebraicGeometry.Space.smallEtaleRingedSite`, a
`RingedSite.{u + 1, u, u}`, whose ring universe `u` is not `max (u + 1) u`.

## Main results

* `Stacks.SheafOfModules.InternalHom.ringedSite_sheafInternalHomObjMapLeft_mono_of_epi`:
  precomposition along an epimorphism is a monomorphism of internal Hom sheaves, which is the
  initial zero of the target sequence.
* `Stacks.SheafOfModules.InternalHom.ringedSite_sheafInternalHomObjMapLeft_exact_of_exact_epi`:
  the image sequence is exact at its middle term.

## Implementation notes

The internal Hom sheaf is `Stacks.SheafOfModules.InternalHom.sheafInternalHomObj`, whose sheaf
of rings is spelled `Stacks.SheafOfModules.Tensor.ringSheaf X.O`, the one declaration the
several former spellings of that sheaf of rings -- among them the deleted
`AlgebraicGeometry.RingedSite.ringSheaf` -- have been merged onto. The same statements over
`Stacks.SheafOfModules.InternalHom.siteSheafInternalHom`, whose sheaf of rings is spelled
`Stacks.SheafOfModules.TensorColimits.underlyingRingSheaf`, are
`Stacks.SheafOfModules.InternalHom.ringedSite_sheafInternalHomMapLeft_mono_of_epi` and
`..._exact_of_exact_epi` of
`StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.InternalHomFirstVariable`;
those are pinned to `w = max u v` and are untagged. The pin there is not a property of internal
Hom but of the file `siteSheafInternalHom` is declared in: its variable block carries the
sheafification data the tensor statements of that file need, at `max u v`. Freeing it is what
the deterministic kernel timeout in
`Stacks.SheafOfModules.InternalHom.sheafCurryIso_natural_left` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomTensorCurrying` measures; routing part
(1) through `sheafInternalHomObj`, which no tensor statement consumes, reaches the general
statement without touching that proof.

Sheaves of modules form an abelian category once abelian sheaves on the site can be
sheafified. At these universes that follows from the site being essentially small in the module
universe, which is a fact about the site rather than a hypothesis on the sequence, and it is
supplied by the three `local instance`s below. They are stated at explicitly written universe
levels rather than left to inference, which is what keeps `w` out of them: the module universe
is `max u v` and the sheafification data never mentions the ring universe at all.

The witness that the image composite vanishes is bundled into the exactness claim rather than
assumed, so that no preservation hypothesis beyond the one proved in Stacks 03EN is imposed on
the functor.

## References

* [Stacks Project, Tag 0GMY](https://stacks.math.columbia.edu/tag/0GMY)
* [Stacks Project, Tag 03EN](https://stacks.math.columbia.edu/tag/03EN)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.SheafOfModules.InternalHom

open AlgebraicGeometry

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

universe v u w

variable (X : RingedSite.{u, v, w})

/-- The site is essentially small in the module universe, which is what makes abelian sheaves
on it sheafifiable and hence sheaves of modules over it an abelian category. -/
local instance essentiallySmall_ringedSite : EssentiallySmall.{max u v} X.C :=
  essentiallySmallSelf.{max u v, v, u} X.C

/-- Presheaves of abelian groups in the universe `max u v` on the site admit sheafification. -/
local instance hasSheafify_ringedSite : HasSheafify X.J AddCommGrpCat.{max u v} :=
  hasSheafifyEssentiallySmallSite.{v, max u v, u, max (u + 1) (v + 1), max u v} X.J _

/-- On the site, a morphism of presheaves of abelian groups in the universe `max u v` is
inverted by sheafification if and only if it is locally bijective. -/
local instance wEqualsLocallyBijective_ringedSite :
    X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{v, max u v, u,
    max (u + 1) (v + 1), max u v} X.J

private theorem sheafInternalHomFunctor_preservesZeroMorphisms
    (G : _root_.SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (sheafInternalHomFunctor X.J X.O G).PreservesZeroMorphisms := by
  refine ⟨fun A B => ?_⟩
  show (sheafInternalHomObjMapLeft X.J X.O (G := G) (0 : A ⟶ B)).op = 0
  apply Quiver.Hom.unop_inj
  apply _root_.SheafOfModules.hom_ext
  apply _root_.PresheafOfModules.hom_ext
  intro U
  have hrestr : (restrFun X.O.obj U.unop).map (0 : A.val ⟶ B.val) = 0 := by
    apply _root_.PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    rfl
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  show ((restrFun X.O.obj U.unop).map (0 : A.val ⟶ B.val) ≫ t) = 0
  exact (congrArg (fun φ => φ ≫ t) hrestr).trans zero_comp

/-- **Stacks 0GMY, part (1).** Precomposition along an epimorphism is a monomorphism of
internal Hom sheaves, which is the initial zero of the target sequence. -/
@[stacks 0GMY "exact_first_argument", ega "0 4.1.5" "Injectivity of Hom(F"]
theorem ringedSite_sheafInternalHomObjMapLeft_mono_of_epi
    {F₁ F G : _root_.SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (g : F₁ ⟶ F) [Epi g] :
    Mono (sheafInternalHomObjMapLeft X.J X.O (G := G) g) := by
  let H := sheafInternalHomFunctor X.J X.O G
  have : H.PreservesZeroMorphisms := sheafInternalHomFunctor_preservesZeroMorphisms X G
  let k := kernel.ι g
  have hk : IsColimit (CokernelCofork.ofπ g (kernel.condition g)) :=
    Abelian.epiIsCokernelOfKernel (KernelFork.ofι k (kernel.condition g)) (kernelIsKernel g)
  have : PreservesColimit (parallelPair k 0) H := inferInstance
  exact (op_epi_iff _).1
    (epi_of_isColimit_cofork ((CokernelCofork.ofπ g (kernel.condition g)).mapIsColimit hk H))

/-- **Stacks 0GMY, part (1).** A right-exact sequence of sheaves of modules becomes exact at
the middle term after applying internal Hom in the first argument. -/
@[stacks 0GMY "exact_first_argument"]
theorem ringedSite_sheafInternalHomObjMapLeft_exact_of_exact_epi
    (S : ShortComplex (_root_.SheafOfModules.{max u v}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (G : _root_.SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hS : S.Exact) [Epi S.g] :
    ∃ h : sheafInternalHomObjMapLeft X.J X.O (G := G) S.g ≫
        sheafInternalHomObjMapLeft X.J X.O (G := G) S.f = 0,
      (ShortComplex.mk (sheafInternalHomObjMapLeft X.J X.O (G := G) S.g)
        (sheafInternalHomObjMapLeft X.J X.O (G := G) S.f) h).Exact := by
  let H := sheafInternalHomFunctor X.J X.O G
  have : H.PreservesZeroMorphisms := sheafInternalHomFunctor_preservesZeroMorphisms X G
  have : PreservesColimit (parallelPair S.f 0) H := inferInstance
  refine ⟨?_, ?_⟩
  · show (S.map H).unop.f ≫ (S.map H).unop.g = 0
    exact (S.map H).unop.zero
  · show (S.map H).unop.Exact
    exact (hS.map_of_epi_of_preservesCokernel H inferInstance inferInstance).unop

end Stacks.SheafOfModules.InternalHom

end
