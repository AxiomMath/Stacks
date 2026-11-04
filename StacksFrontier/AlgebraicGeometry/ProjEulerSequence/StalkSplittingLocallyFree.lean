module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerShortExact
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.StalkSplitting

/-!
# A short exact sequence with locally free quotient splits on every stalk

Let `O♯` be a sheaf of commutative rings on a topological space `X` and let

`0 ⟶ E ⟶ F ⟶ G ⟶ 0`

be a short exact sequence of sheaves of `O♯`-modules. Short exactness is a stalkwise condition,
so at every point `y` the stalk modules form a short exact sequence of `O_y`-modules; whether it
splits is then a question about the single module `G_y`. If `G` is locally free — in particular
if it is finite locally free of any rank — a trivialization of `G` on a neighbourhood of `y`
exhibits `G_y` as a free `O_y`-module on the index set of that trivialization, hence as a
projective module. A projective module lifts along surjections, so the surjection `F_y ⟶ G_y`
admits a section, and a section of a short exact sequence in a balanced category is a splitting.

This generalizes `Stacks.AlgebraicGeometry.ProjEulerSequence.stalkSplittingOfShortExactUnit`
from the unit sheaf of modules, free of rank one on the germ of the unit section, to an arbitrary
locally free quotient: only the source of the projectivity changes, since the rank of the free
module plays no role in the lifting argument.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjEulerSequence.stalkFreeSection`: a section of the stalk of the
  second arrow, chosen by the projectivity of the stalk of the third term.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.stalkSplittingOfProjectiveStalk`: the splitting of
  the stalk complex produced by that section.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.stalkSplittingOfShortExactLocallyFree`: **a short
  exact sequence of sheaves of modules whose third term is locally free splits on every stalk.**
* `Stacks.AlgebraicGeometry.ProjEulerSequence.prodEquivOfShortExactLocallyFree`: **for such a
  sequence the stalk of the middle term is the product of the stalks of the outer terms.**

## Main results

* `Stacks.AlgebraicGeometry.ProjEulerSequence.projective_stalk_of_isLocallyFree`: the stalk of a
  locally free sheaf of modules is a projective module over the stalk of the sheaf of rings.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.projective_stalk_of_isFiniteLocallyFreeOfRank`: the
  same for a sheaf of modules of a fixed finite rank, whose class does not imply local freeness
  by instance search.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.stalkMapL_stalkFreeSection`: the defining property
  of the chosen section.

## Implementation notes

Everything is phrased through `Stacks.AlgebraicGeometry.ProjEulerSequence.ringSheafOfComm`, the
sheaf of rings underlying a sheaf of commutative rings spelled as `sheafCompose` of the
forgetful functor: `CategoryTheory.ShortComplex.map` needs
`CategoryTheory.Functor.PreservesZeroMorphisms` of the stalk functor and instance search for it
fails at the `CategoryTheory.Sheaf.toRingCat` spelling of the same sheaf. The trivialization
machinery is stated at two further definitionally equal spellings,
`CategoryTheory.Sheaf.toRingCat` and `LocallyFreeRank.toRingSheaf`, which are reconciled here by
making them reducible for instance search and unification rather than by transporting along an
isomorphism.

Two rings act on the stalk of a sheaf of modules: the `CommRingCat`-valued stalk of the sheaf of
commutative rings, over which both `PresheafOfModules.stalkMapL` and the freeness of the stalk of
a locally free sheaf are stated, and the `RingCat`-valued one, over which the stalk functor on
sheaves of modules is linear and hence over which the section must be presented to
`CategoryTheory.ShortComplex.Splitting.ofExactOfSection`. The lifting argument therefore runs
over the former, and its outcome is carried back by
`Stacks.AlgebraicGeometry.ProjEulerSequence.stalkRingLinearOfCommLinear`, which keeps the
underlying function and only changes the ring the linearity is recorded over.

The module structure on the stalk also has two spellings — `LocallyFreeRank.instModuleStalkF`,
over which the trivialization of a locally free sheaf of modules produces a basis, and Mathlib's
`PresheafOfModules` stalk-module instance, over which `PresheafOfModules.stalkMapL` is linear —
and they are definitionally but not reducibly equal. A hypothesis of projectivity therefore
elaborates at the first and is wanted at the second, which instance search does not bridge; it is
passed to `Module.projective_lifting_property` as the named instance argument `h`, where the
ordinary definitional unfolding of an explicit argument settles it.

The section is extracted from the existential produced by
`Module.projective_lifting_property` by `Exists.choose`, with its defining property a separate
theorem: a `def` producing data may not destructure an existential, since `Exists.casesOn`
eliminates only into `Prop`.

Local freeness, and not finite local freeness, is the hypothesis of the splitting, because a free
module of any rank is projective. The two finiteness refinements enter differently: the class
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree` yields
`SheafOfModules.IsLocallyFree` by instance search, so the splitting applies to it directly, while
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank` does not — the rank cannot be
inferred from the sheaf of modules — and is served by the second projectivity theorem.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf TopologicalSpace Opposite
open AlgebraicGeometry

namespace Stacks.AlgebraicGeometry.ProjEulerSequence

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose LocallyFreeRank.toRingSheaf

section LocallyFree

variable {X : TopCat.{u}} (Oc : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u})

/-- **The stalk of a locally free sheaf of modules is a projective module** over the stalk of the
sheaf of commutative rings: a trivialization on a neighbourhood of the point identifies the stalk
with the free module on the index set of that trivialization. -/
theorem projective_stalk_of_isLocallyFree (M : SheafOfModules.{u} (ringSheafOfComm Oc))
    [hM : M.IsLocallyFree] (y : ↥X) :
    Module.Projective (ToType (TopCat.Presheaf.stalk Oc.obj y))
      (ToType (TopCat.Presheaf.stalk M.val.presheaf y)) := by
  obtain ⟨q, hq⟩ := hM.exists_isLocallyFreeData
  have hmem : y ∈ ⨆ i, q.X i := by
    rw [(Opens.coversTop_iff X q.X).mp q.coversTop]; trivial
  rw [Opens.mem_iSup] at hmem
  obtain ⟨i, hi⟩ := hmem
  obtain ⟨e⟩ := LocallyFreeRank.Trivialization.stalk_linearEquiv_finsupp X Oc M y hi
    (Stacks.SheafOfModules.TopWedge.trivializationOfGenerators M q hq i)
  exact Module.Projective.of_basis (Finsupp.basisSingleOne.map e.symm)

/-- **The stalk of a sheaf of modules which is finite locally free of rank `r` is a projective
module.** A fixed finite rank is not an instance-level refinement of local freeness, since the
rank cannot be inferred from the sheaf of modules, so this is stated separately. -/
theorem projective_stalk_of_isFiniteLocallyFreeOfRank
    (M : SheafOfModules.{u} (ringSheafOfComm Oc)) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r] (y : ↥X) :
    Module.Projective (ToType (TopCat.Presheaf.stalk Oc.obj y))
      (ToType (TopCat.Presheaf.stalk M.val.presheaf y)) :=
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree M r
  projective_stalk_of_isLocallyFree Oc M y

end LocallyFree

section Split

variable {X : TopCat.{u}} (Oc : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u})
  {E F G : SheafOfModules.{u} (ringSheafOfComm Oc)}

/-- **The stalk of the second arrow admits a section** when the stalk of the third term is
projective: the stalk map is surjective, and a projective module lifts the identity along a
surjection. -/
theorem exists_stalkFreeSection {f : E ⟶ F} {g : F ⟶ G} (hfg : f ≫ g = 0)
    (hSE : (ShortComplex.mk f g hfg).ShortExact) (y : ↥X)
    (hproj : Module.Projective (ToType (TopCat.Presheaf.stalk Oc.obj y))
      (ToType (TopCat.Presheaf.stalk G.val.presheaf y))) :
    ∃ s : ToType (TopCat.Presheaf.stalk G.val.presheaf y)
        →ₗ[ToType (TopCat.Presheaf.stalk Oc.obj y)]
        ToType (TopCat.Presheaf.stalk F.val.presheaf y),
      ∀ m, PresheafOfModules.stalkMapL y g.val (s m) = m := by
  have hsurj : Function.Surjective (PresheafOfModules.stalkMapL y g.val) :=
    (ModuleCat.epi_iff_surjective _).mp (shortExact_map_stalkFunctor Oc hfg hSE y).epi_g
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (h := hproj)
    (PresheafOfModules.stalkMapL y g.val) LinearMap.id hsurj
  exact ⟨s, fun m => congrArg (fun φ : _ →ₗ[_] _ => φ m) hs⟩

/-- The chosen section of the stalk of the second arrow. -/
def stalkFreeSection {f : E ⟶ F} {g : F ⟶ G} (hfg : f ≫ g = 0)
    (hSE : (ShortComplex.mk f g hfg).ShortExact) (y : ↥X)
    (hproj : Module.Projective (ToType (TopCat.Presheaf.stalk Oc.obj y))
      (ToType (TopCat.Presheaf.stalk G.val.presheaf y))) :
    ToType (TopCat.Presheaf.stalk G.val.presheaf y)
      →ₗ[ToType (TopCat.Presheaf.stalk Oc.obj y)]
      ToType (TopCat.Presheaf.stalk F.val.presheaf y) :=
  (exists_stalkFreeSection Oc hfg hSE y hproj).choose

/-- The defining property of `stalkFreeSection`: the stalk of the second arrow undoes it. -/
theorem stalkMapL_stalkFreeSection {f : E ⟶ F} {g : F ⟶ G} (hfg : f ≫ g = 0)
    (hSE : (ShortComplex.mk f g hfg).ShortExact) (y : ↥X)
    (hproj : Module.Projective (ToType (TopCat.Presheaf.stalk Oc.obj y))
      (ToType (TopCat.Presheaf.stalk G.val.presheaf y)))
    (m : ToType (TopCat.Presheaf.stalk G.val.presheaf y)) :
    PresheafOfModules.stalkMapL y g.val (stalkFreeSection Oc hfg hSE y hproj m) = m :=
  (exists_stalkFreeSection Oc hfg hSE y hproj).choose_spec m

/-- **A short exact sequence of sheaves of modules whose third term has projective stalk at `y`
splits on the stalk at `y`.** The section of the stalk of the second arrow provided by
projectivity is a splitting of the stalk complex, which is short exact. -/
def stalkSplittingOfProjectiveStalk {f : E ⟶ F} {g : F ⟶ G} (hfg : f ≫ g = 0)
    (hSE : (ShortComplex.mk f g hfg).ShortExact) (y : ↥X)
    (hproj : Module.Projective (ToType (TopCat.Presheaf.stalk Oc.obj y))
      (ToType (TopCat.Presheaf.stalk G.val.presheaf y))) :
    ((ShortComplex.mk f g hfg).map
      (AlgebraicGeometry.SheafOfModules.stalkFunctor (ringSheafOfComm Oc) y)).Splitting :=
  ShortComplex.Splitting.ofExactOfSection _ (shortExact_map_stalkFunctor Oc hfg hSE y).exact
    (ModuleCat.ofHom (stalkRingLinearOfCommLinear y (stalkFreeSection Oc hfg hSE y hproj)))
    (ModuleCat.hom_ext (LinearMap.ext fun m =>
      stalkMapL_stalkFreeSection Oc hfg hSE y hproj m))
    (shortExact_map_stalkFunctor Oc hfg hSE y).mono_f

/-- **A short exact sequence of sheaves of modules whose third term is locally free splits on
every stalk.** The stalk of a locally free sheaf of modules is free, hence projective. -/
def stalkSplittingOfShortExactLocallyFree [G.IsLocallyFree] {f : E ⟶ F} {g : F ⟶ G}
    (hfg : f ≫ g = 0) (hSE : (ShortComplex.mk f g hfg).ShortExact) (y : ↥X) :
    ((ShortComplex.mk f g hfg).map
      (AlgebraicGeometry.SheafOfModules.stalkFunctor (ringSheafOfComm Oc) y)).Splitting :=
  stalkSplittingOfProjectiveStalk Oc hfg hSE y (projective_stalk_of_isLocallyFree Oc G y)

/-- **The stalk of the middle term of a short exact sequence with locally free third term is the
product of the stalks of the outer terms**, linearly over the stalk of the sheaf of rings. This
is the pointwise splitting read through `prodEquivOfStalkSplitting`. -/
def prodEquivOfShortExactLocallyFree [G.IsLocallyFree] {f : E ⟶ F} {g : F ⟶ G}
    (hfg : f ≫ g = 0) (hSE : (ShortComplex.mk f g hfg).ShortExact) (y : ↥X) :
    ToType (TopCat.Presheaf.stalk F.val.presheaf y)
      ≃ₗ[ToType (TopCat.Presheaf.stalk Oc.obj y)]
      (ToType (TopCat.Presheaf.stalk E.val.presheaf y) ×
        ToType (TopCat.Presheaf.stalk G.val.presheaf y)) :=
  prodEquivOfStalkSplitting Oc hfg y (stalkSplittingOfShortExactLocallyFree Oc hfg hSE y)

end Split

end Stacks.AlgebraicGeometry.ProjEulerSequence

end
