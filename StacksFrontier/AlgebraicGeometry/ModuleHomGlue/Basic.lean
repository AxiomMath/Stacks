module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.Topology.Sheaves.Glueing.OModuleMapGluing

/-!
# Glueing morphisms of sheaves of modules on a scheme over an open cover

A compatible family of morphisms of `𝒪_X`-modules given on the members of an open cover of a
scheme `X` assembles to a single morphism, and to only one. This is the **existence half** of the
locality of morphisms of `AlgebraicGeometry.Scheme.Modules`; the separation half is
`Stacks.AlgebraicGeometry.TwistUnique.hom_ext_of_cover`, and together they say that the morphisms
between two sheaves of modules form a sheaf on `X`.

Everything is stated for an arbitrary open cover of an arbitrary scheme: **no quasi-coherence, no
affineness and no finiteness hypothesis appears**, and only the target has to be a sheaf, which it
is by definition of `AlgebraicGeometry.Scheme.Modules`.

## What was already here

The sheaf-theoretic content is *not* proved here. `TopCat.Sheaf.existsUnique_hom_of_localModuleHom`
in `StacksFrontier/Topology/Sheaves/Glueing/OModuleMapGluing.lean` already glues morphisms of
presheaves of `𝒪`-modules over an open cover of a topological space, for an arbitrary presheaf of
rings `𝒪` and with only the target assumed to be a sheaf. This file is the transport of that
statement to `AlgebraicGeometry.Scheme.Modules`, which is `SheafOfModules X.ringCatSheaf`: the
`𝒪` there is `X.ringCatSheaf.obj` and the sheaf hypothesis on the target is `M.isSheaf`.

## Main definitions

* `Stacks.AlgebraicGeometry.ModuleHomGlue.localModuleHomOfApp`: local morphism data on an open `U`
  of `X`, built from a family of maps on sections `Γ(M, V) ⟶ Γ(N, V)` for the opens `V ≤ U`, their
  `Γ(X, V)`-linearity and their compatibility with restriction. This is the `Γ`-idiom shape of
  `TopCat.Sheaf.LocalModuleHom`.
* `Stacks.AlgebraicGeometry.ModuleHomGlue.localModuleHomOfHom`: the local morphism data cut out of
  a global morphism, the direction that needs no sheaf condition.

## Main results

* `Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_cover`: **morphisms of sheaves of
  modules on a scheme glue over an open cover.** A family of local morphisms on the members of a
  cover agreeing on all overlaps comes from exactly one morphism `M ⟶ N`.
* `Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_cover_app`: the same statement with
  the local data and the conclusion written on sections, in the `Γ(M, V)` idiom and
  `AlgebraicGeometry.Scheme.Modules.Hom.app`. This is the form a consumer supplies and consumes.

## Implementation notes

The compatibility hypothesis is stated over *every* open `V` of `X` contained in both `U i` and
`U j`, inherited from `TopCat.Sheaf.LocalModuleHom`: an overlap of two members of the cover is a
single open of `X` and is never required to belong to the covering family. The index of the cover
lands in `Type u`, the same universe as the scheme, which is what the underlying gluing statement
asks for.

The scalar rings are the sections of the structure sheaf read in `RingCat`, since that is where
the module structures on the sections of a `PresheafOfModules` are registered, but the `Γ(X, V)`
spelling of `AlgebraicGeometry.Scheme.Modules` elaborates against them: Mathlib's own
`Module Γ(X, U) Γ(M, U)` instance is the `RingCat`-side one. So `localModuleHomOfApp` can take its
linearity hypothesis in the `Γ` idiom and hand a `ModuleCat` morphism to `LocalModuleHom`.

## No tag is claimed

No `stacks` attribute is attached. This is infrastructure, not an assertion of any tag: it is the
named input to Tag 07ZG's assertion (3), but that assertion is not reached from here — it also
needs a `Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData`, which nothing in this repository
constructs.

## References

* [Stacks Project, Tag 00AN](https://stacks.math.columbia.edu/tag/00AN)
* [Stacks Project, Tag 04TN](https://stacks.math.columbia.edu/tag/04TN)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry

namespace Stacks.AlgebraicGeometry.ModuleHomGlue

universe u

variable {X : Scheme.{u}}

/-- **Local morphism data on an open `U`, given on sections.** A family of maps on sections
`Γ(M, V) ⟶ Γ(N, V)` indexed by the opens `V ≤ U`, linear over `Γ(X, V)` and compatible with the
restriction maps, is the same thing as a morphism `M|_U ⟶ N|_U` of sheaves of modules on `U`; it is
recorded as a `TopCat.Sheaf.LocalModuleHom`, which indexes it by the opens of `X` inside `U` rather
than by the opens of the subspace. -/
public def localModuleHomOfApp {M N : X.Modules} (U : X.Opens)
    (g : ∀ V : X.Opens, V ≤ U → (Γ(M, V) ⟶ Γ(N, V)))
    (hsmul : ∀ (V : X.Opens) (hV : V ≤ U) (r : Γ(X, V)) (s : Γ(M, V)),
      g V hV (r • s) = r • g V hV s)
    (hres : ∀ (V W : X.Opens) (hV : V ≤ U) (hWV : W ≤ V) (s : Γ(M, V)),
      g W (hWV.trans hV) (M.presheaf.map (homOfLE hWV).op s) =
        N.presheaf.map (homOfLE hWV).op (g V hV s)) :
    TopCat.Sheaf.LocalModuleHom M.val N.val U where
  app V hV := ModuleCat.ofHom
    { toFun := g V hV
      map_add' := fun x y => map_add _ x y
      map_smul' := hsmul V hV }
  naturality hV hWV s := hres _ _ hV hWV s

/-- The local morphism data cut out of a global morphism by forgetting everything outside `U`.
This direction uses no sheaf condition: it is just the naturality of `φ`. -/
public def localModuleHomOfHom {M N : X.Modules} (φ : M ⟶ N) (U : X.Opens) :
    TopCat.Sheaf.LocalModuleHom M.val N.val U where
  app V _ := φ.val.app (op V)
  naturality _ hWV s := PresheafOfModules.app_resLE φ.val hWV s

/-- **Morphisms of sheaves of modules on a scheme glue over an open cover.** Let `U` be an open
cover of a scheme `X` and let `M`, `N` be sheaves of `𝒪_X`-modules. A family of local morphisms
`M|_{U i} ⟶ N|_{U i}` which agree on every open contained in two members of the cover comes from
exactly one morphism `M ⟶ N`.

Only the target's sheaf condition is used, and it is part of the definition of
`AlgebraicGeometry.Scheme.Modules`; there is no hypothesis on `X`, on the cover or on `M` and `N`
beyond that. -/
public theorem existsUnique_hom_of_cover {M N : X.Modules} {ι : Type u} {U : ι → X.Opens}
    (hU : ⨆ i, U i = ⊤)
    (f : ∀ i, TopCat.Sheaf.LocalModuleHom M.val N.val (U i))
    (hf : ∀ (i j : ι) (V : X.Opens) (hVi : V ≤ U i) (hVj : V ≤ U j),
      (f i).app V hVi = (f j).app V hVj) :
    ∃! φ : M ⟶ N, ∀ (i : ι) (V : X.Opens) (hV : V ≤ U i),
      φ.val.app (op V) = (f i).app V hV := by
  obtain ⟨ψ, hψ, huniq⟩ :=
    TopCat.Sheaf.existsUnique_hom_of_localModuleHom U hU M.val N.val N.isSheaf f hf
  exact ⟨⟨ψ⟩, hψ, fun φ' hφ' => SheafOfModules.hom_ext (huniq φ'.val hφ')⟩

/-- **The gluing of morphisms of sheaves of modules, on sections.** The same statement as
`Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_cover`, with the local data given as
maps on sections which are linear and compatible with restriction, and with the conclusion read
through `AlgebraicGeometry.Scheme.Modules.Hom.app`.

Unconditional: `X` is an arbitrary scheme, `U` an arbitrary open cover, and `M` and `N` arbitrary
sheaves of `𝒪_X`-modules. -/
public theorem existsUnique_hom_of_cover_app {M N : X.Modules} {ι : Type u} {U : ι → X.Opens}
    (hU : ⨆ i, U i = ⊤)
    (g : ∀ (i : ι) (V : X.Opens), V ≤ U i → (Γ(M, V) ⟶ Γ(N, V)))
    (hsmul : ∀ (i : ι) (V : X.Opens) (hV : V ≤ U i) (r : Γ(X, V)) (s : Γ(M, V)),
      g i V hV (r • s) = r • g i V hV s)
    (hres : ∀ (i : ι) (V W : X.Opens) (hV : V ≤ U i) (hWV : W ≤ V) (s : Γ(M, V)),
      g i W (hWV.trans hV) (M.presheaf.map (homOfLE hWV).op s) =
        N.presheaf.map (homOfLE hWV).op (g i V hV s))
    (hg : ∀ (i j : ι) (V : X.Opens) (hVi : V ≤ U i) (hVj : V ≤ U j), g i V hVi = g j V hVj) :
    ∃! φ : M ⟶ N, ∀ (i : ι) (V : X.Opens) (hV : V ≤ U i), φ.app V = g i V hV := by
  obtain ⟨φ, hφ, huniq⟩ := existsUnique_hom_of_cover hU
    (fun i => localModuleHomOfApp (U i) (g i) (hsmul i) (hres i))
    (fun i j V hVi hVj =>
      ModuleCat.hom_ext (LinearMap.ext fun s => congr($(hg i j V hVi hVj) s)))
  refine ⟨φ, fun i V hV => ?_, fun φ' hφ' => huniq φ' fun i V hV => ?_⟩
  · ext s
    exact congr($(hφ i V hV) s)
  · exact ModuleCat.hom_ext (LinearMap.ext fun s => congr($(hφ' i V hV) s))

end Stacks.AlgebraicGeometry.ModuleHomGlue

end
