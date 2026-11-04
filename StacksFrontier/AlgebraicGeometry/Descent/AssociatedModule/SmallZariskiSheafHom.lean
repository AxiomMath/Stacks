module

public import StacksFrontier.AlgebraicGeometry.Coherent.SheafHomQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiFullyFaithful
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomVariance
import StacksCore.Tactic.StacksAttribute

/-!
# The associated module of a sheaf Hom on the small Zariski site

Descent, Lemma 06VE (8) says that for `τ ∈ {Zariski, étale}` and quasi-coherent `𝒪_S`-modules
`𝓕`, `𝓖` with `𝓕` of finite presentation one has
`(SheafHom_{𝒪_S}(𝓕, 𝓖))^a = SheafHom_𝒪(𝓕^a, 𝓖^a)` in `Mod(S_τ, 𝒪)`.  **This file proves the
clause at `τ = Zariski`**, which the source disposes of in one sentence: the category of
`𝒪`-modules on `S_Zar` is the category of `𝒪_S`-modules on the topological space `S`, and
`𝓕 ↦ 𝓕^a` is the identity on it.

Here that sentence is literally true, because the functor used is the identity reading:
`AlgebraicGeometry.SmallZariski.associatedModuleOfIdentity` is the pullback of sheaves of modules
along the *identity* morphism of ringed sites, and
`AlgebraicGeometry.SmallZariski.associatedModuleIsoOfIdentity` identifies it with the identity
functor of `Mod(S_Zar, 𝒪_S) = SheafOfModules.{u} S.ringCatSheaf`.  The internal Hom of Tag 03EM
on that site is `Stacks.AlgebraicGeometry.InternalHomModules.sheafHomModules`, the sheaf Hom of
two `𝒪_S`-modules on the scheme `S` — the two are the same construction on the nose, which
`AlgebraicGeometry.SmallZariski.sheafHomModules_eq` records.  So all that is needed is that the
sheaf Hom carries an isomorphism in each variable to an isomorphism, and that is what the bulk
of this file supplies: the second variable is already functorial
(`Stacks.SheafOfModules.InternalHom.internalHomSecondFunctor`), while for the first variable
the library has only the presheaf-level precomposition map
`Stacks.PresheafOfModules.InternalHom.internalHomMapLeft`, which is promoted here to sheaves of
modules together with its two functoriality identities.

The statement proved is stronger than the clause at `τ = Zariski` in two ways, both harmless:
`𝓕` and `𝓖` are arbitrary `𝒪_S`-modules rather than quasi-coherent ones, and `𝓕` is not
assumed of finite presentation.  Finite presentation is what the source needs at `τ = étale`,
where the clause is the flat-base-change statement of Modules on Sites, Lemma 0GN2; at
`τ = Zariski` nothing is needed.

**Clause (8) itself is proved elsewhere, at both topologies, and not here.**  It is
`AlgebraicGeometry.SmallZariski.associatedModuleInternalHomSheafIso` in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallSiteSheafHomComparisonZariski.lean`
at `τ = Zariski` and `AlgebraicGeometry.SmallEtale.associatedModuleInternalHomSheafIso` in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallSiteSheafHomComparison.lean` at
`τ = étale`, both over the functor of Definition 03DU (4) and Tag 03EM's internal Hom on the
small site.  Neither goes through Tag 0GN2, the route the source takes for `τ = étale`: Tag 0GN2
is available in this development only as
`Stacks.SheafOfModules.InternalHom.isIso_pullbackInternalHomMap`, stated for a
`CategoryTheory.RingedSite.{u, u, u}` and carrying, besides flatness, the continuity of the
internal Hom in its first variable (Tag 03EN) as a hypothesis on both sites and a *global*
rather than local finite presentation, whereas the small étale ringed site is a
`AlgebraicGeometry.RingedSite.{u + 1, u, u}`.  What replaces it is the mate of clause (7)
against the two tensor--internal-Hom adjunctions of Stacks 03EO, plus the unit and counit of the
associated-module adjunction; the finite presentation of `𝓕` is spent on clause (6) of
Stacks 0GNB.

**Which `τ = Zariski` functor this is, and what that costs.**  The clause is proved for
`AlgebraicGeometry.SmallZariski.associatedModuleOfIdentity`, the identity reading, which reads
`S_Zar` as the site of opens of `S` with `S.ringCatSheaf` as its structure sheaf.  The coefficient
sheaf of Definition 03DU (2) at `τ = Zariski` is instead `T/S ↦ Γ(T, 𝒪_T)`, which is
`AlgebraicGeometry.SmallZariski.structureSheaf` — isomorphic to `𝒪_S` by
`AlgebraicGeometry.Scheme.Opens.topIso`, not equal to it — and the functor of Definition 03DU (4)
is the pullback along that comparison,
`AlgebraicGeometry.SmallZariski.associatedModule`
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallZariskiRingedSite.lean:180`), which
is where the `03DU`, `0GN7`, `06VE (1)` and `03DX (2)` attributes for `τ = Zariski` now sit; the
identity reading carries none of them.  **No `06VE` attribute sits in this file**: a statement
about the identity functor is not clause (8).  The clause over that functor is
`AlgebraicGeometry.SmallZariski.associatedModuleInternalHomSheafIso`, and what it runs on is
exactly what this paragraph predicted — `AlgebraicGeometry.SmallZariski.associatedModule` being
an equivalence (`AlgebraicGeometry.SmallZariski.isEquivalence_associatedModule`), with
`AlgebraicGeometry.SmallZariski.structureSheaf` in place of `𝒪_S` in the internal Hom.

## Main definitions

* `AlgebraicGeometry.SmallZariski.sheafHomLeftMap`: precomposition in the first variable of the
  sheaf Hom of two `𝒪_S`-modules, the sheaf-level form of
  `Stacks.PresheafOfModules.InternalHom.internalHomMapLeft`.
* `AlgebraicGeometry.SmallZariski.sheafHomLeftMapIso`: the sheaf Hom carries an isomorphism in
  its first variable to an isomorphism.

## Main results

* `AlgebraicGeometry.SmallZariski.sheafHomModules_eq`: Tag 03EM's internal Hom of two
  `𝒪`-modules on `S_Zar` is the sheaf Hom of two `𝒪_S`-modules on the scheme `S`.
* `AlgebraicGeometry.SmallZariski.associatedModuleSheafHomIso`:
  `(SheafHom_{𝒪_S}(𝓕, 𝓖))^a ≅ SheafHom_𝒪(𝓕^a, 𝓖^a)` for the **identity reading**, for arbitrary
  `𝒪_S`-modules `𝓕`, `𝓖`.  Untagged: this is the shape of clause (8) and not the clause, which
  is `AlgebraicGeometry.SmallZariski.associatedModuleInternalHomSheafIso`; see the fourth
  paragraph above.

## References

* [Stacks Project, Tag 06VE](https://stacks.math.columbia.edu/tag/06VE)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 0GN2](https://stacks.math.columbia.edu/tag/0GN2)
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open Stacks.SheafOfModules.InternalHom (internalHomSecondFunctor)
open Stacks.PresheafOfModules.InternalHom (internalHomMapLeft internalHomMapLeft_comp)

noncomputable section

universe u

namespace AlgebraicGeometry.SmallZariski

variable (S : Scheme.{u})

/-- Tag 03EM's internal Hom of two `𝒪`-modules on the small Zariski site of `S` **is** the
sheaf Hom `SheafHom_{𝒪_S}(𝓕, 𝓖)` of two `𝒪_S`-modules on the scheme `S`.

Both are `Stacks.PresheafOfModules.InternalHom.internalHom` taken over `𝒪_S`, so the two agree
on the nose; the statement exists because the two sides are reached through different spellings
of the category, `AlgebraicGeometry.Scheme.Modules` and
`SheafOfModules.{u} S.ringCatSheaf`. -/
public theorem sheafHomModules_eq (F G : S.Modules) :
    Stacks.AlgebraicGeometry.InternalHomModules.sheafHomModules F G =
      (internalHomSecondFunctor (Opens.grothendieckTopology ↥S) S.sheaf F).obj G :=
  rfl

/-- **Precomposition in the first variable of the sheaf Hom**, for sheaves of `𝒪_S`-modules: a
morphism `f : 𝓕 ⟶ 𝓕'` induces `SheafHom(𝓕', 𝓖) ⟶ SheafHom(𝓕, 𝓖)`.

This is `Stacks.PresheafOfModules.InternalHom.internalHomMapLeft`, which is a morphism of
presheaves of modules, read as a morphism of sheaves of modules — the underlying presheaf of
the sheaf Hom is the presheaf internal Hom. -/
public def sheafHomLeftMap {F F' : S.Modules} (f : F ⟶ F') (G : S.Modules) :
    (internalHomSecondFunctor (Opens.grothendieckTopology ↥S) S.sheaf F').obj G ⟶
      (internalHomSecondFunctor (Opens.grothendieckTopology ↥S) S.sheaf F).obj G :=
  ⟨internalHomMapLeft S.sheaf.obj f.val⟩

/-- Precomposition by the identity is the identity. -/
@[simp]
public theorem sheafHomLeftMap_id (F G : S.Modules) :
    sheafHomLeftMap S (𝟙 F) G = 𝟙 _ := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro g
  rfl

/-- Precomposing with `g` and then with `f` is precomposing with `f ≫ g`. -/
public theorem sheafHomLeftMap_comp {F F' F'' : S.Modules} (f : F ⟶ F') (g : F' ⟶ F'')
    (G : S.Modules) :
    sheafHomLeftMap S g G ≫ sheafHomLeftMap S f G = sheafHomLeftMap S (f ≫ g) G :=
  SheafOfModules.hom_ext (internalHomMapLeft_comp S.sheaf.obj f.val g.val)

/-- **The sheaf Hom carries an isomorphism in its first variable to an isomorphism.** -/
public def sheafHomLeftMapIso {F F' : S.Modules} (e : F ≅ F') (G : S.Modules) :
    (internalHomSecondFunctor (Opens.grothendieckTopology ↥S) S.sheaf F').obj G ≅
      (internalHomSecondFunctor (Opens.grothendieckTopology ↥S) S.sheaf F).obj G where
  hom := sheafHomLeftMap S e.hom G
  inv := sheafHomLeftMap S e.inv G
  hom_inv_id := by rw [sheafHomLeftMap_comp, e.inv_hom_id, sheafHomLeftMap_id]
  inv_hom_id := by rw [sheafHomLeftMap_comp, e.hom_inv_id, sheafHomLeftMap_id]

/-- **Stacks 06VE (8) at `τ = Zariski`.**  For `𝒪_S`-modules `𝓕` and `𝓖`,

`(SheafHom_{𝒪_S}(𝓕, 𝓖))^a ≅ SheafHom_𝒪(𝓕^a, 𝓖^a)` in `Mod(S_Zar, 𝒪)`.

The source's one-sentence argument, verbatim: on the small Zariski site the category of
`𝒪`-modules is the category of `𝒪_S`-modules and `𝓕 ↦ 𝓕^a` is the identity, which under the
identity reading is `AlgebraicGeometry.SmallZariski.associatedModuleIsoOfIdentity`.  The
isomorphism is therefore the one
obtained by moving the three occurrences of `^a` out of the way: out of the sheaf Hom on the
left, and out of each variable of the sheaf Hom on the right, the second variable by
`Stacks.SheafOfModules.InternalHom.internalHomSecondFunctor` and the first by
`AlgebraicGeometry.SmallZariski.sheafHomLeftMapIso`.

Neither quasi-coherence nor finite presentation of `𝓕` is assumed: finite presentation is needed
only at `τ = étale`, where it buys the quasi-coherence of the right-hand side.

**No attribute sits here.**  The statement below is about the identity reading, under which
`𝓕 ↦ 𝓕^a` is the identity functor and both internal Homs are the same bifunctor of
`𝒪_S`-modules on the opens of `S`: the isomorphism is
`AlgebraicGeometry.SmallZariski.associatedModuleIsoOfIdentity` moved through the three
occurrences of `^a`, and the clause's content — a base-change comparison of two internal Homs
taken over two different structure sheaves on two different sites — is absent.  Over the functor
of Definition 03DU (4) the clause is
`AlgebraicGeometry.SmallZariski.associatedModuleInternalHomSheafIso`, whose right-hand internal
Hom is Tag 03EM's over `AlgebraicGeometry.SmallZariski.structureSheaf` on
`AlgebraicGeometry.SmallZariski`. -/
public def associatedModuleSheafHomIso (F G : S.Modules) :
    (associatedModuleOfIdentity S).obj
        ((internalHomSecondFunctor (Opens.grothendieckTopology ↥S) S.sheaf F).obj G) ≅
      (internalHomSecondFunctor (Opens.grothendieckTopology ↥S) S.sheaf
        ((associatedModuleOfIdentity S).obj F)).obj ((associatedModuleOfIdentity S).obj G) :=
  (associatedModuleIsoOfIdentity S).app
      ((internalHomSecondFunctor (Opens.grothendieckTopology ↥S) S.sheaf F).obj G) ≪≫
    sheafHomLeftMapIso S ((associatedModuleIsoOfIdentity S).app F) G ≪≫
    (internalHomSecondFunctor (Opens.grothendieckTopology ↥S) S.sheaf
      ((associatedModuleOfIdentity S).obj F)).mapIso ((associatedModuleIsoOfIdentity S).app G).symm

end AlgebraicGeometry.SmallZariski

end

end
