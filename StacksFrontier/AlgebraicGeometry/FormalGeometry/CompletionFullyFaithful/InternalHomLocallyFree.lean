module

public import StacksFrontier.AlgebraicGeometry.Modules.DualFiniteLocallyFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreePowerSheaf
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Sheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFinite
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.InternalHom
import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.SheafHomLocallyFree

/-!
# The internal hom of two finite locally free coherent modules is finite locally free

Let `X` be a scheme and let `𝒢`, `ℱ` be finite locally free `𝒪_X`-modules. Then the internal hom
`SheafHom(𝒢, ℱ)` is again finite locally free, with no assumption that the ranks of `𝒢` and `ℱ`
be constant.

The argument is local and does not go through the ranks. Around a point of `X` choose an open
`U` on which `𝒢|_U` is free on a finite index set `I` and `ℱ|_U` is free on a finite index set
`J`: such a `U` is obtained by intersecting a trivializing open for `𝒢` with one for `ℱ`, which
is harmless because freeness on `U` restricts to freeness on any smaller open. Internal hom
commutes with restriction to `U` (Tag 0E8H) and turns the finite coproduct `𝒪_U^{⊕I}` in its
first variable into a finite product, which in an additive category is again that coproduct
(Tag 03EN); so `SheafHom(𝒢, ℱ)|_U` is a coproduct of `I` copies of `ℱ|_U`, hence a coproduct of
`I × J` copies of `𝒪_U`.

## Main results

* `Stacks.AlgebraicGeometry.SheafHomLocallyFree.isFiniteLocallyFree_internalHomCoherent`
  (imported): the internal hom `Stacks.Algebraization.internalHomCoherent` of two finite locally
  free coherent modules on a locally Noetherian scheme is finite locally free, in the class
  spelling `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree`.
* `Stacks.Algebraization.isFiniteLocallyFree_scheme_internalHomCoherent`: the same statement in
  the pointwise spelling `AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree`.
* `Stacks.AlgebraicGeometry.SheafHomLocallyFree.isFiniteLocallyFree_sheafHomFunctor`
  (imported): the underlying statement about `Stacks.Algebraization.sheafHomFunctor`, with no
  coherence and no Noetherian hypothesis.

## Implementation notes

Both local inputs are read off results already stated for a ringed site, at the ringed site
`Stacks.AlgebraicGeometry.ReflexiveModules.schemeRingedSite X` of the opens of `X`: that internal
hom commutes with restriction is `sheafInternalHomOverIso`, the sheaf form of Tag 0E8H, and that
internal hom out of a finite free module is a finite coproduct of copies of the target is
`freeSheafInternalHomIso`, both read on the slice site over `U`. No computation with local
sections and no local dual basis enters. This is the same route as
`Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFree_dualSheaf`, which is the case
`ℱ = 𝒪_X` of the present statement, with the target kept general and the extra trivialization of
`ℱ` supplied by `Stacks.Algebraization.freeIsoOverOfLE`.

The rank-indexed results of the library require a constant rank and so do not apply: the index
sets of a local free presentation vary from one member of the covering to another. What replaces
them is `AlgebraicGeometry.SheafOfModules.isFiniteLocallyFree_of_forall_exists_iso_free_over`,
which assembles finite local freeness from free restrictions on a neighbourhood of every point
and so never names a global rank. The index set used at a point is the product of the two the
local presentations of `𝒢` and `ℱ` provide there.

Shrinking a trivializing open uses `SheafOfModules.overMap`, restriction between two slice
sites. Its preservation of coproducts indexed by a finite type is not available from an
adjunction on a site without binary products, and is obtained instead from additivity, exactly as
`Stacks.SheafOfModules.SliceFinite.preservesColimitsOfShape_discrete_overFunctor` does for
restriction from the ambient site.

## References

* [Stacks Project, Tag 0FA7](https://stacks.math.columbia.edu/tag/0FA7)
* [Stacks Project, Tag 0E8H](https://stacks.math.columbia.edu/tag/0E8H)
* [Stacks Project, Tag 03EN](https://stacks.math.columbia.edu/tag/03EN)
* [Stacks Project, Tag 01CQ](https://stacks.math.columbia.edu/tag/01CQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
open Stacks.SheafOfModules.InternalHom
open Stacks.AlgebraicGeometry.InternalHomLocalKernel
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace Stacks.Algebraization

variable {X : Scheme.{u}}

/-! ### Shrinking a trivializing open -/

/-- Restriction of sheaves of modules between two slice sites is additive: on morphisms it is
precomposition with a functor followed by restriction of scalars. -/
public instance additive_overMap {U V : X.Opens} (f : V ⟶ U) :
    (SheafOfModules.overMap.{u} X.ringCatSheaf f).Additive where
  map_add := by intros; rfl

/-- Restriction between two slice sites preserves coproducts indexed by a finite type: it is an
additive functor between preadditive categories, hence preserves finite biproducts, and a finite
biproduct in a preadditive category is a finite coproduct. -/
public instance preservesColimitsOfShape_discrete_overMap {U V : X.Opens} (f : V ⟶ U)
    (I : Type u) [Finite I] :
    PreservesColimitsOfShape (Discrete I) (SheafOfModules.overMap.{u} X.ringCatSheaf f) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin I
  have := (inferInstance :
    PreservesFiniteCoproducts (SheafOfModules.overMap.{u} X.ringCatSheaf f)).preserves n
  exact preservesColimitsOfShape_of_equiv (Discrete.equivalence e.symm) _

/-- **Freeness on an open restricts to any smaller open.** If the restriction of `M` to the
slice site over `U` is free on a finite index set `I`, then so is its restriction to the slice
site over any `V ≤ U`.

Restricting from the slice over `U` to the slice over `V` is `SheafOfModules.overMap`, which
sends the structure sheaf to the structure sheaf and preserves `I`-indexed coproducts, hence
sends a free sheaf to the free sheaf on the same index set, and composes with restriction from
`X` to restriction from `X`. -/
public def freeIsoOverOfLE {U V : X.Opens} (f : V ⟶ U) (M : X.Modules) {I : Type u} [Finite I]
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U) :
    SheafOfModules.free (R := X.ringCatSheaf.over V) I ≅ M.over V :=
  SheafOfModules.mapFreeIso (SheafOfModules.overMap.{u} X.ringCatSheaf f) I
      (SheafOfModules.overMapUnitIso f).symm ≪≫
    (SheafOfModules.overMap.{u} X.ringCatSheaf f).mapIso e ≪≫
    (SheafOfModules.overFunctorMap.{u} X.ringCatSheaf f).app M

/-- A finite locally free sheaf of modules is free on a finite index set on the slice site over
some open neighbourhood of any given point: read off a member of a local free presentation
through that point. -/
public theorem exists_iso_free_over_of_isFiniteLocallyFree (M : X.Modules)
    (hM : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M) (x : X) :
    ∃ (U : X.Opens) (_ : x ∈ U) (I : Type u) (_ : Finite I),
      Nonempty (SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U) := by
  obtain ⟨q, hq, hqf⟩ := hM.exists_isFiniteLocallyFreeData
  obtain ⟨i, hxi⟩ := ((Opens.coversTop_iff _ q.X).1 q.coversTop).exists_mem x
  have hiso : IsIso (q.generators i).π := hq.isIso i
  have hfin : Finite (q.generators i).I := (hqf.isFiniteType i).finite
  exact ⟨q.X i, hxi, (q.generators i).I, hfin, ⟨asIso (q.generators i).π⟩⟩

/-! ### The internal hom on a trivializing open -/

/-- **The internal hom of two free modules on finite index sets is free on their product**, read
on the slice site of the opens of `X` over `U`: if the restrictions of `G` and `F` to `U` are
free on finite index sets `I` and `J`, then the restriction of `SheafHom(G, F)` to `U` is free on
`I × J`.

The restriction of the internal hom is the internal hom of the restrictions, by Tag 0E8H;
internal hom out of `𝒪_U^{⊕I}` is the `I`-fold coproduct of the target, by Tag 03EN together
with the computation of internal hom out of `𝒪_U`; and an `I`-fold coproduct of `𝒪_U^{⊕J}` is an
`I × J`-fold coproduct of `𝒪_U`. -/
public theorem nonempty_freeIsoInternalHomOver (U : X.Opens) (G F : X.Modules) {I J : Type u}
    [Finite I] [Finite J]
    (eG : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ G.over U)
    (eF : SheafOfModules.free (R := X.ringCatSheaf.over U) J ≅ F.over U) :
    Nonempty (SheafOfModules.free (R := X.ringCatSheaf.over U) ((_ : I) × J) ≅
      ((sheafHomFunctor X G).obj F).over U) := by
  obtain ⟨h⟩ := SheafOfModules.nonempty_iso_free_coprod (O := X.ringCatSheaf.over U)
    (P := fun _ : I => F.over U) (fun _ : I => J) fun _ => ⟨eF.symm⟩
  exact ⟨(AlgebraicGeometry.InternalHomLocalKernel.sheafInternalHomOverIso
      (schemeRingedSite X) U G F ≪≫
    ((sheafInternalHomFunctor ((Opens.grothendieckTopology ↥X).over U) (X.sheaf.over U)
        (F.over U)).mapIso eG).unop ≪≫
    freeSheafInternalHomIso (X.sheaf.over U) (F.over U) I ≪≫ h).symm⟩

/-! ### The global statement -/

/-- **The internal hom of two finite locally free coherent modules is finite locally free**, in
the pointwise spelling `AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree`. -/
public theorem isFiniteLocallyFree_scheme_internalHomCoherent {X : Scheme.{u}}
    [IsLocallyNoetherian X]
    (G F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (hG : AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree G.obj)
    (hF : AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree F.obj) :
    AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree (internalHomCoherent X G F).obj :=
  (Scheme.Modules.isFiniteLocallyFree_iff _).2
    (Stacks.AlgebraicGeometry.SheafHomLocallyFree.isFiniteLocallyFree_internalHomCoherent G F
      ((Scheme.Modules.isFiniteLocallyFree_iff _).1 hG)
      ((Scheme.Modules.isFiniteLocallyFree_iff _).1 hF))

end Stacks.Algebraization

end

