module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomVariance
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Left exactness of internal Hom in the second argument

Let `(C, O)` be a ringed site and let `F` be a sheaf of `O`-modules. Part (2) of Stacks 0GMY
says that an exact sequence `0 → G → G₁ → G₂` of `O`-modules induces an exact sequence

`0 → Hom_O(F, G) → Hom_O(F, G₁) → Hom_O(F, G₂)`.

The proof is the one of the source: internal Hom in the second variable commutes with limits
(Stacks 03EN), hence with kernels, and a left-exact additive functor between abelian
categories carries a left-exact sequence to a left-exact sequence.

## Main results

* `Stacks.SheafOfModules.InternalHom.internalHomSecondFunctor_map_mono`: postcomposition by a
  monomorphism is a monomorphism of internal Hom sheaves, which is the initial zero of the
  target sequence.
* `Stacks.SheafOfModules.InternalHom.internalHomSecondFunctor_exact`: the image sequence is
  exact at its middle term.

## Implementation notes

The leading zero of each sequence of the source is expressed by a monomorphism, and the maps
of the target sequence are the canonical postcomposition maps of
`internalHomSecondFunctor`. The witness that the image composite vanishes is bundled into the
exactness claim rather than assumed, so that no preservation hypothesis beyond the one proved
in Stacks 03EN is imposed on the functor.

Sheaves of modules over the structure sheaf of a ringed site form an abelian category once
abelian sheaves on the site can be sheafified. At the universes in play that comes from the
site being essentially small in the module universe, which `essentiallySmallSelf` supplies;
the sheafification and local-bijectivity instances are then those of an essentially small
site. These are facts about the site, not hypotheses on the sequence.

Only part (2) of Stacks 0GMY is proved here. Part (1), left exactness in the first argument,
is `StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.InternalHomFirstVariable`,
  which builds the sheaf-level
analogue of `Stacks.PresheafOfModules.InternalHom.internalHomFunctor` that part (1) needs.
The tag for the two declarations below is recorded in
`StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.InternalHomSecondVariable`,
which is where the `StacksCore.Tactic.StacksAttribute` import lives.

## References

* [Stacks Project, Tag 0GMY](https://stacks.math.columbia.edu/tag/0GMY)
* [Stacks Project, Tag 03EN](https://stacks.math.columbia.edu/tag/03EN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

namespace Stacks.SheafOfModules.InternalHom

universe u v w m

variable (X : RingedSite.{u, v, w})
variable (F : _root_.SheafOfModules.{max u v w m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- Postcomposition by a monomorphism is a monomorphism of internal Hom sheaves. -/
@[sga "4 V 6.0" "6.0"]
theorem internalHomSecondFunctor_map_mono
    {G G₁ : _root_.SheafOfModules.{max u v w m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (g : _root_.SheafOfModules.Hom G G₁)
    [@Mono (_root_.SheafOfModules.{max u v w m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (inferInstance : Category.{max u v w m} _) G G₁ g] :
    Mono ((internalHomSecondFunctor.{v, u, w, m} X.J X.O F).map g) :=
  Functor.map_mono (internalHomSecondFunctor.{v, u, w, m} X.J X.O F) g

/-- **Stacks 0GMY, part (2).** A left-exact sequence of sheaves of modules stays exact at the
middle term after applying internal Hom in the second argument. -/
@[sga "4 V 6.0" "6.0"]
theorem internalHomSecondFunctor_exact
    (S : ShortComplex.{max u v w m, max (m + 1) (u + 1) (v + 1) (w + 1)}
      (_root_.SheafOfModules.{max u v w m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hS : S.Exact) [Mono S.f] :
    ∃ h : (internalHomSecondFunctor.{v, u, w, m} X.J X.O F).map S.f ≫
        (internalHomSecondFunctor.{v, u, w, m} X.J X.O F).map S.g = 0,
      (ShortComplex.mk
        ((internalHomSecondFunctor.{v, u, w, m} X.J X.O F).map S.f)
        ((internalHomSecondFunctor.{v, u, w, m} X.J X.O F).map S.g) h).Exact := by
  let H := internalHomSecondFunctor.{v, u, w, m} X.J X.O F
  let : EssentiallySmall.{max u v w m} X.C :=
    essentiallySmallSelf.{max u v w m, v, u} X.C
  let : HasSheafify X.J AddCommGrpCat.{max u v w m} :=
    hasSheafifyEssentiallySmallSite.{v, max u v w m, u,
      max (u + 1) (v + 1) (w + 1) (m + 1), max u v w m} X.J _
  let : X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w m} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{v,
      max u v w m, u, max (u + 1) (v + 1) (w + 1) (m + 1), max u v w m} X.J
  let : Abelian
      (_root_.SheafOfModules.{max u v w m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
    inferInstance
  have : H.PreservesZeroMorphisms := inferInstance
  exact ⟨by rw [← H.map_comp, S.zero, H.map_zero],
    hS.map_of_mono_of_preservesKernel H inferInstance inferInstance⟩

end Stacks.SheafOfModules.InternalHom

end
