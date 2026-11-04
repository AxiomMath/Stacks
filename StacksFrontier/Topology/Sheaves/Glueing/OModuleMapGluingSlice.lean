module

public import StacksFrontier.Topology.Sheaves.Glueing.OModuleMapGluing
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Gluing morphisms of sheaves of modules given over the members of an open cover

Let `X` be a topological space, let `R` be a sheaf of rings on `X` and let `M`, `N` be sheaves of
`R`-modules. `TopCat.Sheaf.existsUnique_hom_of_localModuleHom` glues morphisms `M ⟶ N` from local
data, but its local data is the bespoke structure `Stacks.TopCat.Sheaf.LocalModuleHom` — a family
of `R(V)`-linear maps on sections indexed by the opens `V` contained in a fixed open `U` — rather
than a morphism `M.over U ⟶ N.over U` of sheaves of modules over the slice sheaf of rings. The
two are the same data, and this file constructs the crossing and the gluing theorem it unlocks.

That the crossing is a one-liner is not an accident: `CategoryTheory.SheafOfModules.overFunctor`
is pushforward along `CategoryTheory.Over.forget U`, so the sections of `M.over U` over an object
`V ⟶ U` of the slice site *are* the sections of `M` over `V`, and an open `V ≤ U` is such an
object. No transport and no reindexing occur, which is exactly why
`Stacks.TopCat.Sheaf.LocalModuleHom` was phrased with opens of `X` in the first place.

## Main definitions

* `Stacks.SheafOfModules.localModuleHomOfOver`: **the local morphism data of a morphism over an
  open subset**, read off a morphism `M.over U ⟶ N.over U` of sheaves of modules on the slice
  site. This is the construction needed to glue morphisms given as
  slice morphisms; the nearest other one,
  `Stacks.AlgebraicGeometry.ModuleHomGlue.localModuleHomOfHom`, starts from a *global* morphism
  and is therefore useless for gluing.

## Main results

* `Stacks.SheafOfModules.existsUnique_hom_of_over`: **morphisms of sheaves of modules over the
  members of an open covering, agreeing on overlaps, glue to a unique global morphism** whose
  restriction to each member is the given one. The sheaf of rings is arbitrary, so this applies in
  particular to the Frobenius colimit `colim_F 𝒪_X` of [Stacks, Tag 0EXB], which is not the
  structure sheaf of any ringed space in this development.
* `Stacks.SheafOfModules.overMap_map_eq_of_isBasis`: **agreement of two slice restrictions over
  the members of a basis is agreement over every open**, so that a glueing stated with the
  compatibility over all opens can be fed one available only over a basis.

## Implementation notes

The compatibility hypothesis is stated on *components*: for every open `W` contained in both `V i`
and `V j`, the two morphisms have the same map on sections over `W`. This is the form
`TopCat.Sheaf.existsUnique_hom_of_localModuleHom` consumes and, as its own docstring explains, it
avoids requiring the overlaps to belong to the covering family. Stating it instead as an equality
of morphisms over `V i ⊓ V j` would need the two restriction functors to be compared, which is a
transport that the component form does not incur.

The uniqueness clause is what makes the statement usable for the existence half of a cartesian
square of Hom-sets: a glued morphism is pinned down by its restrictions, so an equation between
glued morphisms can be checked locally. Separatedness on its own — two morphisms agreeing on a
covering are equal — is `Stacks.SheafOfModules.SliceRestriction.overFunctor_map_injective`, at
the same generality and for an arbitrary site.

## References

* [Stacks Project, Tag 00AN](https://stacks.math.columbia.edu/tag/00AN)
* [Stacks Project, Tag 04TN](https://stacks.math.columbia.edu/tag/04TN)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.SheafOfModules

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology (X : TopCat)) RingCat.{u}}
  {M N : _root_.SheafOfModules.{u} R}

/-- **The local morphism data of a morphism of sheaves of modules given over an open subset.**

A morphism `φ : M.over U ⟶ N.over U` on the slice site `Opens(X)/U` has, for each object `V ⟶ U`
of that site, a map on sections `M(V) ⟶ N(V)` linear over `R(V)`; taking the objects of the form
`V ≤ U` and forgetting the rest is precisely a `Stacks.TopCat.Sheaf.LocalModuleHom`. Naturality is
naturality of `φ` at the morphism of the slice site given by an inclusion `W ≤ V`.

This is the construction `Stacks.TopCat.Sheaf.existsUnique_hom_of_localModuleHom` needs in order
to be applied to morphisms produced as slice restrictions. -/
noncomputable def localModuleHomOfOver (U : Opens (X : TopCat)) (φ : M.over U ⟶ N.over U) :
    TopCat.Sheaf.LocalModuleHom M.val N.val U where
  app V hV := φ.val.app (op (Over.mk (homOfLE hV)))
  naturality {V W} hV hWV s :=
    PresheafOfModules.naturality_apply φ.val
      (Over.homMk (homOfLE hWV) : Over.mk (homOfLE (hWV.trans hV)) ⟶ Over.mk (homOfLE hV)).op s

variable {ι : Type u}

/-- **Morphisms of sheaves of modules given over the members of an open covering and agreeing on
overlaps glue to a unique global morphism.**

The sheaf of rings `R` is arbitrary — in particular it need not be the structure sheaf of a ringed
space — and the only hypothesis on the covering is that the opens cover the whole space. The
restriction of the glued morphism to the member `V i` is the given morphism `φ i` on the nose, as
a morphism of sheaves of modules over the slice sheaf of rings, because
`CategoryTheory.SheafOfModules.overFunctor` is a pushforward and so acts on a morphism by
reindexing its components.

This is `TopCat.Sheaf.existsUnique_hom_of_localModuleHom` read through
`Stacks.SheafOfModules.localModuleHomOfOver`; the sheaf condition it needs on the target is the
`isSheaf` field of `N`. -/
@[ega "0 3.3.2" "special case"]
theorem existsUnique_hom_of_over (V : ι → Opens (X : TopCat)) (hV : ⨆ i, V i = ⊤)
    (φ : ∀ i, M.over (V i) ⟶ N.over (V i))
    (hφ : ∀ (i j : ι) (W : Opens (X : TopCat)) (hWi : W ≤ V i) (hWj : W ≤ V j),
      (φ i).val.app (op (Over.mk (homOfLE hWi))) =
        (φ j).val.app (op (Over.mk (homOfLE hWj)))) :
    ∃! ψ : M ⟶ N, ∀ i, (_root_.SheafOfModules.overFunctor R (V i)).map ψ = φ i := by
  obtain ⟨ψ, hψ, huniq⟩ := TopCat.Sheaf.existsUnique_hom_of_localModuleHom V hV M.val N.val
    N.isSheaf (fun i => localModuleHomOfOver (V i) (φ i)) hφ
  refine ⟨⟨ψ⟩, fun i => ?_, fun χ hχ => ?_⟩
  · refine _root_.SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun W => ?_)
    exact hψ i W.unop.left (leOfHom W.unop.hom)
  · refine _root_.SheafOfModules.hom_ext (huniq χ.val fun i W hW => ?_)
    exact congrArg (fun t : M.over (V i) ⟶ N.over (V i) =>
      t.val.app (op (Over.mk (homOfLE hW)))) (hχ i)

end Stacks.SheafOfModules

namespace TopCat.Sheaf.LocalModuleHom

variable {X : TopCat.{u}} {𝒪 : (Opens (X : TopCat))ᵒᵖ ⥤ RingCat.{u}}
  {M N : PresheafOfModules.{u} 𝒪}

/-- **Two local morphism data agreeing on the members of a basis agree on every open.**

If `f` is given on the opens below `U`, `g` on the opens below `U'`, and the two maps on sections
coincide over every *basis* open below both, then they coincide over every open below both. Only
the sheaf condition on the target is used: a section of `N` over `V` is determined by its
restrictions to the basis opens inside `V`, which cover `V`, and both maps commute with those
restrictions.

This is the form in which `Stacks.SheafOfModules.existsUnique_hom_of_over` can be fed a
compatibility that is only available over a distinguished basis — the basic opens of an affine
scheme, say, which is the only place where the almost blowup square of [Stacks, Example 0EVH] is
again a two-generator square. -/
theorem app_eq_of_isBasis
    (hN : CategoryTheory.Presheaf.IsSheaf
      (Opens.grothendieckTopology (X : TopCat)) N.presheaf)
    {B : Set (Opens (X : TopCat))} (hB : Opens.IsBasis B)
    {U U' : Opens (X : TopCat)} (f : TopCat.Sheaf.LocalModuleHom M N U)
    (g : TopCat.Sheaf.LocalModuleHom M N U')
    (h : ∀ W ∈ B, ∀ (hWU : W ≤ U) (hWU' : W ≤ U'), f.app W hWU = g.app W hWU')
    {V : Opens (X : TopCat)} (hVU : V ≤ U) (hVU' : V ≤ U') :
    f.app V hVU = g.app V hVU' := by
  ext s
  have hcov : V ≤ ⨆ k : {W : Opens (X : TopCat) // W ∈ B ∧ W ≤ V}, (k : Opens (X : TopCat)) := by
    intro x hx
    obtain ⟨W, hWB, hxW, hWV⟩ := Opens.isBasis_iff_nbhd.mp hB hx
    exact Opens.mem_iSup.mpr ⟨⟨W, hWB, hWV⟩, hxW⟩
  refine TopCat.Sheaf.eq_of_locally_eq_of_isSheafPresheaf hN
    (fun k : {W : Opens (X : TopCat) // W ∈ B ∧ W ≤ V} => (k : Opens (X : TopCat)))
    (fun k => k.2.2) hcov fun k => ?_
  rw [← f.naturality hVU k.2.2 s, ← g.naturality hVU' k.2.2 s,
    h k.1 k.2.1 (k.2.2.trans hVU) (k.2.2.trans hVU')]

end TopCat.Sheaf.LocalModuleHom

namespace Stacks.SheafOfModules

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology (X : TopCat)) RingCat.{u}}
  {M N : _root_.SheafOfModules.{u} R} {ι : Type u}

/-- **Morphisms of sheaves of modules given over the members of an open covering and agreeing over
the members of a basis glue to a unique global morphism.**

This is `Stacks.SheafOfModules.existsUnique_hom_of_over` with its compatibility hypothesis
weakened from *every* open below two members of the covering to the members of a prescribed basis
`B` below two members. The two are equivalent, by
`TopCat.Sheaf.LocalModuleHom.app_eq_of_isBasis`: the basis opens inside an open `W` cover it, both
components commute with restriction, and the target is a sheaf.

It is the form the trivialising-cover argument for [Stacks, Tag 0EXD] needs. There the covering of
`Spec A` is by basic opens `D(g)` and the local solutions are produced over the spectra of the
localisations `A_g`; their agreement is available only over a basic open `D(h)` below two members,
because only over a basic open is the almost blowup square of [Stacks, Example 0EVH] again a
two-generator square, namely the one over `A_h`. Over an arbitrary open below two members there is
no local square at all, and so no local uniqueness to appeal to. -/
@[ega "0 3.3.2" "special case"]
theorem existsUnique_hom_of_over_of_isBasis
    {B : Set (Opens (X : TopCat))} (hB : Opens.IsBasis B)
    (V : ι → Opens (X : TopCat)) (hV : ⨆ i, V i = ⊤)
    (φ : ∀ i, M.over (V i) ⟶ N.over (V i))
    (hφ : ∀ (i j : ι) (W : Opens (X : TopCat)), W ∈ B → ∀ (hWi : W ≤ V i) (hWj : W ≤ V j),
      (φ i).val.app (op (Over.mk (homOfLE hWi))) =
        (φ j).val.app (op (Over.mk (homOfLE hWj)))) :
    ∃! ψ : M ⟶ N, ∀ i, (_root_.SheafOfModules.overFunctor R (V i)).map ψ = φ i :=
  existsUnique_hom_of_over V hV φ fun i j _W hWi hWj =>
    TopCat.Sheaf.LocalModuleHom.app_eq_of_isBasis N.isSheaf hB
      (localModuleHomOfOver (V i) (φ i)) (localModuleHomOfOver (V j) (φ j))
      (fun W' hW'B => hφ i j W' hW'B) hWi hWj

/-- **The top component of a slice restriction is the component at the smaller open.**

`CategoryTheory.SheafOfModules.overMap R (homOfLE h)` is pushforward along
`CategoryTheory.Over.map (homOfLE h)`, so it acts on a morphism by reindexing its components; the
object `W ≤ W` of the slice site at `W` is reindexed to the object `W ≤ V`. Both sides are
literally the same map on sections, so this holds by `rfl` and is `exact`-only: the two sides
spell their common type differently. -/
theorem overMap_map_val_app_le {V W : Opens (X : TopCat)} (h : W ≤ V)
    (φ : M.over V ⟶ N.over V) :
    ((_root_.SheafOfModules.overMap R (homOfLE h)).map φ).val.app
        (op (Over.mk (homOfLE (le_refl W)))) = φ.val.app (op (Over.mk (homOfLE h))) :=
  rfl

/-- Equal slice restrictions to `W` have equal components at the object `W ≤ V`. -/
private theorem app_eq_of_overMap_map_eq {V V' W : Opens (X : TopCat)} {hWV : W ≤ V}
    {hWV' : W ≤ V'} {φ : M.over V ⟶ N.over V} {φ' : M.over V' ⟶ N.over V'}
    (h : (_root_.SheafOfModules.overMap R (homOfLE hWV)).map φ =
      (_root_.SheafOfModules.overMap R (homOfLE hWV')).map φ') :
    φ.val.app (op (Over.mk (homOfLE hWV))) = φ'.val.app (op (Over.mk (homOfLE hWV'))) :=
  congrArg (fun t => t.val.app (op (Over.mk (homOfLE (le_refl W))))) h

/-- **Morphisms of sheaves of modules given over the members of an open covering whose slice
restrictions to the members of a basis agree glue to a unique global morphism.**

This is `Stacks.SheafOfModules.existsUnique_hom_of_over_of_isBasis` with the compatibility
hypothesis in the form a consumer actually has it: an equality of *morphisms* over the smaller
open, rather than of their maps on sections. The slice restriction is Mathlib's
`CategoryTheory.SheafOfModules.overMap`, whose compatibility with
`CategoryTheory.SheafOfModules.overFunctor` is `CategoryTheory.SheafOfModules.overFunctorMap`, and
the passage to components is `Stacks.SheafOfModules.overMap_map_val_app_le`.

Note that the two sides of the hypothesis are morphisms between objects that are only
*definitionally* equal — the slice restriction of `M.over (V i)` and of `M.over (V j)` to `W` are
both the restriction of `M` to `W`, reindexed in two ways — so the equation typechecks without
any transport. -/
@[ega "0 3.3.2" "special case"]
theorem existsUnique_hom_of_overMap_eq_of_isBasis
    {B : Set (Opens (X : TopCat))} (hB : Opens.IsBasis B)
    (V : ι → Opens (X : TopCat)) (hV : ⨆ i, V i = ⊤)
    (φ : ∀ i, M.over (V i) ⟶ N.over (V i))
    (hφ : ∀ (i j : ι) (W : Opens (X : TopCat)), W ∈ B → ∀ (hWi : W ≤ V i) (hWj : W ≤ V j),
      (_root_.SheafOfModules.overMap R (homOfLE hWi)).map (φ i) =
        (_root_.SheafOfModules.overMap R (homOfLE hWj)).map (φ j)) :
    ∃! ψ : M ⟶ N, ∀ i, (_root_.SheafOfModules.overFunctor R (V i)).map ψ = φ i :=
  existsUnique_hom_of_over_of_isBasis hB V hV φ fun i j W hWB hWi hWj =>
    app_eq_of_overMap_map_eq (hφ i j W hWB hWi hWj)

/-- **Two morphisms over two opens whose slice restrictions to the basis opens below both agree
have the same slice restriction to every open below both.**

This is `TopCat.Sheaf.LocalModuleHom.app_eq_of_isBasis` read on morphisms rather than on
components, and it is what lets a glueing statement whose compatibility hypothesis quantifies over
*every* open below two members of the covering be fed a compatibility available only over the
members of a prescribed basis — the basic opens of an affine scheme, say.  In particular it unlocks
the glueings stated in the `CategoryTheory.SheafOfModules.overMap` form, which are the ones a
consumer in the transition-functor spelling of [Stacks, Tag 0EXE] has.

Only the sheaf condition on the target is used:  a component of the slice restriction over an
object `T ≤ W` of the slice site at `W` *is* the component of the original morphism over `T ≤ V`,
by definition -- that is `Stacks.SheafOfModules.overMap_map_val_app_le` at the top object, and here
the identification is left to the elaborator -- and a section of `N` over an open is determined by
its restrictions to the basis opens inside it. -/
theorem overMap_map_eq_of_isBasis
    {B : Set (Opens (X : TopCat))} (hB : Opens.IsBasis B) {V V' : Opens (X : TopCat)}
    (φ : M.over V ⟶ N.over V) (φ' : M.over V' ⟶ N.over V')
    (h : ∀ W ∈ B, ∀ (hWV : W ≤ V) (hWV' : W ≤ V'),
      (_root_.SheafOfModules.overMap R (homOfLE hWV)).map φ =
        (_root_.SheafOfModules.overMap R (homOfLE hWV')).map φ')
    {W : Opens (X : TopCat)} (hWV : W ≤ V) (hWV' : W ≤ V') :
    (_root_.SheafOfModules.overMap R (homOfLE hWV)).map φ =
      (_root_.SheafOfModules.overMap R (homOfLE hWV')).map φ' := by
  refine _root_.SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun T => ?_)
  exact TopCat.Sheaf.LocalModuleHom.app_eq_of_isBasis N.isSheaf hB
    (localModuleHomOfOver V φ) (localModuleHomOfOver V' φ')
    (fun W' hW'B hW'V hW'V' => app_eq_of_overMap_map_eq (h W' hW'B hW'V hW'V'))
    ((leOfHom T.unop.hom).trans hWV) ((leOfHom T.unop.hom).trans hWV')

end Stacks.SheafOfModules

end
