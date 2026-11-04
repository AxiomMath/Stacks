module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.LocalSectionRestrict
public import StacksFrontier.AlgebraicGeometry.SymmetricDehomogenize.Restriction

/-!
# The local section of a projective bundle is compatible with shrinking the open

`Stacks.RelativeProj.homOfLE_comp_localSection` reduces the compatibility of
`Stacks.RelativeProj.localSection` with shrinking an affine open `V` of the base to `W ⊆ V` to a
single equation of ring homomorphisms out of `Γ(V, Sym F)`, its hypothesis `hres`. **This file
discharges that equation**, from one equation of morphisms of sheaves of modules on `X`.

## What the reduction now is

`Stacks.RelativeProj.localDehomogenize V q e` is
`Stacks.SymmetricDehomogenize.dehomogenize` for the inclusion `V.ι`, the trivialized quotient
`Stacks.RelativeProj.trivializedQuotientHom V q e` and the identification
`Stacks.RelativeProj.preimageSelfTopRingHom V`. Since `X.homOfLE hWV ≫ V.ι = W.ι`,
`Stacks.SymmetricDehomogenize.dehomogenize_comp_resRingHom` applies, and it asks for exactly two
things:

* that the two trivialized quotients are related by restriction of functions along
  `X.homOfLE hWV`, which is the hypothesis `hκ` below; and
* that restriction of global functions from `V` to `W` carries `preimageSelfTopRingHom V` to
  `preimageSelfTopRingHom W` composed with the structure map of `X.homOfLE hWV`, which is
  `Stacks.RelativeProj.preimageSelfTop_comp_appTop` below — a pure structure-sheaf identity,
  both sides being one `AlgebraicGeometry.Scheme.Hom.appLE` of `X.homOfLE hWV` factored in two
  ways.

So the whole of the restriction compatibility of the local section now rests on `hκ`: **one
equation between two morphisms `F ⟶ (W.ι)_*𝒪_W`**, with no `Proj`, no graded ring and no chart
in it. That is `Stacks.RelativeProj.homOfLE_comp_localSection_of_trivializedQuotientHom_res`.

## The restricted trivialization

`hκ`'s right-hand side needs a trivialization of `𝓛` over `W`, and the natural one is the
restriction of the trivialization over `V`. Nothing in this repository restricted an `over`-site
trivialization along an inclusion of opens, but Mathlib does it in one line:
`SheafOfModules.overMap` is the restriction functor between the two restricted sites,
`SheafOfModules.overFunctorMap` says that restricting to `V` and then to `W` is restricting to
`W`, and `SheafOfModules.overMapUnitIso` says the unit object goes to the unit object (it is
`Iso.refl`). `Stacks.RelativeProj.overRestrictIsoUnit` is their composite. No passage to the
`restrict` spelling of a trivialization — Mathlib's
`AlgebraicGeometry.Scheme.Modules.overEquiv` and
`Stacks.AlgebraicGeometry.ProjInvertibleLocus.restrictIsoUnitOfOverIsoUnit` — is needed for it.

## Main definitions

* `Stacks.RelativeProj.overRestrictIsoUnit`: **the restriction of an `over`-site trivialization
  along an inclusion of opens.**

## Main results

* `Stacks.RelativeProj.preimageSelfTop_comp_appTop`: the structure-sheaf identity that the
  comparison of the two dehomogenizations needs.
* `Stacks.RelativeProj.localDehomogenize_res`: **`hres`**, the hypothesis of
  `Stacks.RelativeProj.localChartMap_comp_projInclusionMap` and
  `Stacks.RelativeProj.homOfLE_comp_localSection`, from the restriction compatibility of the
  trivialized quotient alone.
* `Stacks.RelativeProj.homOfLE_comp_localSection_of_trivializedQuotientHom_res`: **the local
  section over `V`, restricted to an affine open `W ⊆ V`, is the local section over `W`** — given
  that one equation of morphisms of sheaves of modules. The trivialization over `W` in the
  conclusion is arbitrary, by `Stacks.RelativeProj.localSection_congr`.

## Where `hκ` is discharged

`StacksFrontier/AlgebraicGeometry/ProjectiveBundle/TrivializedQuotientRestrict.lean` proves `hκ`,
and with it `Stacks.RelativeProj.homOfLE_comp_localSection_eq`: the restriction compatibility of
the local section with no hypothesis left. The route is not the one this file's first version
priced. The comparison of
`Stacks.AlgebraicGeometry.ProjInvertibleLocus.restrictIsoUnitOfOverIsoUnit` at `V` and at `W`
through `AlgebraicGeometry.Scheme.Modules.overMapCompOverEquiv` is not needed: the second way
recorded below — that `e ↦ restrictIsoUnitOfOverIsoUnit W L e` is surjective, because
`AlgebraicGeometry.Scheme.Modules.overEquiv W` is an equivalence — is the one that works, and it
removes the `over` site from the problem entirely rather than carrying it through. It is
`Stacks.AlgebraicGeometry.ProjInvertibleLocus.exists_overIsoUnit_restrictIsoUnitOfOverIsoUnit_eq`.
The claim below that its round-trip identity cannot be proved by `rw` or `simp` is correct, and
the categorical algebra is written out by hand — once, in an arbitrary category, as
`Stacks.CategoryTheory.trans_symm_trans_symm_trans`.

`Stacks.RelativeProj.overRestrictIsoUnit` of this file is therefore unused: the restricted
trivialization that `hκ` is checked against lives on the open subscheme, not on the restricted
site, and is
`Stacks.AlgebraicGeometry.ProjInvertibleLocus.restrictTrivializationOfLE`.

## Implementation notes

`preimageSelfTop_comp_appTop` is stated as an equation of morphisms of commutative rings rather
than pointwise, because that is the form in which both sides are normalized by
`AlgebraicGeometry.Scheme.homOfLE_app` and `AlgebraicGeometry.Scheme.homOfLE_appLE` to a single
restriction map of `X`; the two resulting morphisms of opens of `X` are then equal because the
homomorphisms of a poset category are a subsingleton.

`AlgebraicGeometry.Scheme.homOfLE_ι` is a theorem and not a definitional equality, which is why
`Stacks.AlgebraicGeometry.ProjF1Dehomogenization.pushforwardUnitRes` takes the composition law as
a hypothesis; `X.homOfLE_ι hWV` is supplied at every call site here.

No `@[stacks]` attribute is attached. Tag 0B3V is the bijection between the sections of
`π : 𝐏(F) ⟶ X` and the invertible quotients of `F`; the compatibility of a local construction
with shrinking the open it is built over is not a covering part of it.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01NS](https://stacks.math.columbia.edu/tag/01NS)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules
open Stacks.AlgebraicGeometry.ProjF1Dehomogenization
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.SymGraded
open Stacks.SymmetricDehomogenize

universe u

namespace Stacks.RelativeProj

variable {X : Scheme.{u}} {F L : X.Modules} [F.IsQuasicoherent]

/-- **The identification `Γ(V, (V.ι)⁻¹V) ≅ Γ(V, ⊤)` followed by restriction of global functions
to `W` is the structure map of `X.homOfLE hWV` followed by the identification over `W`.** Both
sides are one `AlgebraicGeometry.Scheme.Hom.appLE` of `X.homOfLE hWV`, factored in two ways; the
two factorizations become the same restriction map of `X` under
`AlgebraicGeometry.Scheme.homOfLE_app`, the homomorphisms of opens being a subsingleton.

This is the hypothesis on the two `φ`s of
`Stacks.SymmetricDehomogenize.dehomogenize_comp_resRingHom`. -/
public theorem preimageSelfTop_comp_appTop {W V : X.Opens} (hWV : W ≤ V) :
    (V.toScheme.presheaf.map
        (homOfLE (by simp : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V)).op) ≫
      (X.homOfLE hWV).appTop =
    (X.homOfLE hWV).appLE (V.ι ⁻¹ᵁ V) (W.ι ⁻¹ᵁ W)
        (preimage_le_preimage_of_comp V.ι (X.homOfLE hWV) (X.homOfLE_ι hWV) hWV) ≫
      W.toScheme.presheaf.map
        (homOfLE (by simp : (⊤ : W.toScheme.Opens) ≤ W.ι ⁻¹ᵁ W)).op := by
  simp only [Scheme.homOfLE_app, Scheme.homOfLE_appLE, Scheme.Opens.toScheme_presheaf_map,
    Scheme.Opens.toScheme_presheaf_obj, TopologicalSpace.Opens.map_top, ← Functor.map_comp]
  exact congrArg X.presheaf.map (Subsingleton.elim _ _)

/-- **The ring equation `hres`**: the dehomogenization of `Sym F` over `V` at a trivialized
quotient, followed by restriction of global functions to `W`, is restriction of homogeneous
sections followed by the dehomogenization over `W` — given that the two trivialized quotients
are related by restriction of functions along `X.homOfLE hWV`.

This is the one hypothesis of `Stacks.RelativeProj.localChartMap_comp_projInclusionMap` and of
`Stacks.RelativeProj.homOfLE_comp_localSection`. -/
public theorem localDehomogenize_res {W V : X.Opens} (hWV : W ≤ V) (q : F ⟶ L)
    (e : L.over V ≅ SheafOfModules.unit (X.ringCatSheaf.over V))
    (e'' : L.over W ≅ SheafOfModules.unit (X.ringCatSheaf.over W))
    (hκ : trivializedQuotientHom V q e ≫
        pushforwardUnitRes V.ι (X.homOfLE hWV) (X.homOfLE_ι hWV) =
      trivializedQuotientHom W q e'') :
    (X.homOfLE hWV).appTop.hom.comp (localDehomogenize V q e) =
      (localDehomogenize W q e'').comp
        ((schemeSheafGradedAlgebra F
          (isQuasicoherentPieces_of_isQuasicoherent F)).resRingHom hWV) :=
  dehomogenize_comp_resRingHom V.ι (X.homOfLE hWV) (X.homOfLE_ι hWV) F
    (isQuasicoherentPieces_of_isQuasicoherent F) _ _ hκ hWV
    (preimageSelfTopRingHom V) (preimageSelfTopRingHom W) (X.homOfLE hWV).appTop.hom
    fun z => congrArg (fun φ : Γ(V.toScheme, V.ι ⁻¹ᵁ V) ⟶ Γ(W.toScheme, ⊤) => φ.hom z)
      (preimageSelfTop_comp_appTop hWV)

section Trivialization

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf

/-- **The restriction of an `over`-site trivialization along an inclusion of opens.** A module
trivial on the restricted site of `V` is trivial on the restricted site of any `W ⊆ V`:
`SheafOfModules.overFunctorMap` identifies the iterated restriction with the restriction to `W`,
and `SheafOfModules.overMapUnitIso` carries the unit object to the unit object. -/
public def overRestrictIsoUnit {W V : X.Opens} (M : X.Modules) (hWV : W ≤ V)
    (e : M.over V ≅ SheafOfModules.unit (X.ringCatSheaf.over V)) :
    M.over W ≅ SheafOfModules.unit (X.ringCatSheaf.over W) :=
  ((SheafOfModules.overFunctorMap X.ringCatSheaf (homOfLE hWV)).app M).symm ≪≫
    (SheafOfModules.overMap X.ringCatSheaf (homOfLE hWV)).mapIso e ≪≫
    SheafOfModules.overMapUnitIso (R := X.ringCatSheaf) (homOfLE hWV)

/-- **The local section of `π : 𝐏(F) ⟶ X` over `V`, restricted to an affine open `W ⊆ V`, is the
local section over `W`** — given that the trivialized quotient over `V`, followed by restriction
of functions along `X.homOfLE hWV`, is the trivialized quotient over `W` for *some*
trivialization there. The trivialization in the conclusion is arbitrary, by
`Stacks.RelativeProj.localSection_congr`.

This is the agreement on overlaps that a gluing argument consumes, with its hypothesis moved off
the graded ring of homogeneous sections and onto one equation of morphisms of sheaves of modules
on `X`. -/
public theorem homOfLE_comp_localSection_of_trivializedQuotientHom_res {W V : X.Opens}
    (q : F ⟶ L) (e : L.over V ≅ SheafOfModules.unit (X.ringCatSheaf.over V))
    (e' : L.over W ≅ SheafOfModules.unit (X.ringCatSheaf.over W)) (hWV : W ≤ V)
    (hW : IsAffineOpen W) (hV : IsAffineOpen V)
    (hq : Function.Surjective (q.val.app (op V)))
    (hq' : Function.Surjective (q.val.app (op W)))
    (e'' : L.over W ≅ SheafOfModules.unit (X.ringCatSheaf.over W))
    (hκ : trivializedQuotientHom V q e ≫
        pushforwardUnitRes V.ι (X.homOfLE hWV) (X.homOfLE_ι hWV) =
      trivializedQuotientHom W q e'') :
    X.homOfLE hWV ≫ localSection V q e hV hq = localSection W q e' hW hq' :=
  homOfLE_comp_localSection W V q e e' hWV hW hV hq hq' e''
    (localDehomogenize_res hWV q e e'' hκ)

end Trivialization

end Stacks.RelativeProj

end
