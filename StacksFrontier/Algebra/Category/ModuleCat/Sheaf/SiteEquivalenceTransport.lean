module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence

/-!
# Transporting sheaves of modules along an equivalence of sites

An equivalence of sites `e : C' ≌ C` which is continuous in both directions carries a sheaf of
rings `R` on `C` to its direct image on `C'`, and identifies the categories of sheaves of modules
over the two. This file holds that transport, with the two underlying categories allowed to live
in *different* universes.

The universe independence is the reason this is its own module. The same-universe specialisations
are what the finite-presentation and quasi-coherence arguments of
`StacksFrontier/AlgebraicGeometry/Topologies/QuasicoherentSiteEquivalence.lean` need — those go
through the internal Hom sheaf, which is an endofunctor of the module category only when the two
sites share a universe pair — while the construction itself needs no such restriction. Keeping
the construction here lets both the same-universe development and the universe-independent one
use the same declarations instead of each carrying its own copy.

## Main definitions

* `Stacks.SheafOfModules.reindexRing`: the sheaf of rings transported along `e`, i.e. its direct
  image under `e.functor`.
* `Stacks.SheafOfModules.reindexBackSharp`: the structure map of the inverse transport, the
  counit of `e` identifying `R` with the direct image under `e.inverse` of `reindexRing`.
* `Stacks.SheafOfModules.reindexEquivalence`: **transporting along an equivalence of sites is an
  equivalence of the categories of sheaves of modules.** Its functor is the direct image along
  `e.functor` with the identity structure map, its inverse the direct image along `e.inverse`
  with structure map `reindexBackSharp`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.SheafOfModules

universe w m u₁ v₁ u₂ v₂

variable {C : Type u₁} [Category.{v₁} C] {C' : Type u₂} [Category.{v₂} C']
  {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}

/-- The sheaf of rings transported along an equivalence of sites `e : C' ≌ C`, that is, the
direct image of the sheaf of rings `R` under `e.functor`. -/
abbrev reindexRing (J' : GrothendieckTopology C') (e : C' ≌ C)
    [e.functor.IsContinuous J' J] (R : Sheaf J RingCat.{w}) : Sheaf J' RingCat.{w} :=
  (e.functor.sheafPushforwardContinuous RingCat.{w} J' J).obj R

variable (e : C' ≌ C) [e.functor.IsContinuous J' J] [e.inverse.IsContinuous J J']
  (R : Sheaf J RingCat.{w})

/-- The structure map of the inverse of an equivalence of ringed sites: the counit of `e`
identifies `R` with the direct image under `e.inverse` of the transported sheaf of rings. -/
def reindexBackSharp : R ⟶ (e.inverse.sheafPushforwardContinuous RingCat.{w} J J').obj
    (reindexRing J' e R) :=
  ObjectProperty.homMk (Functor.whiskerRight (NatTrans.op e.counit) R.obj)

/-- **Transporting along an equivalence of sites is an equivalence of the categories of sheaves
of modules.** The two underlying categories may live in different universes. -/
noncomputable def reindexEquivalence :
    SheafOfModules.{m} R ≌ SheafOfModules.{m} (reindexRing J' e R) :=
  SheafOfModules.pushforwardPushforwardEquivalence (J := J') (K := J)
    e (𝟙 (reindexRing J' e R)) (reindexBackSharp e R) (by rfl) (by
      ext A : 2
      change 𝟙 _ ≫ R.obj.map _ ≫ R.obj.map _ = 𝟙 _
      rw [Category.id_comp, ← R.obj.map_comp, ← R.obj.map_id]
      congr 1
      simp [← op_comp])

end Stacks.SheafOfModules

end
