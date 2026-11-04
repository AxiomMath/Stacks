module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.AffineTildeCounit

/-!
# The two tilde functors over an affine open, crossed, and the unit they share

Conclusion (b) of [Stacks, Tag 0EX3] presents its endofunctor `Φ` over an affine open `V` of the
base through `AlgebraicGeometry.tilde.functor` on `Spec Γ(V, ⊤)`, pulled back along the composite
`(f' ∣_ V) ≫ V.isoSpec`; the computation of the right-hand end of conclusion (c) uses
`Stacks.Coherent.affineTilde` on `V` itself, pulled back along `f' ∣_ V`. This file records the
crossing of the two, and the one value of it conclusion (c) needs: at the base ring the crossing
lands on the structure sheaf, through the identification of a quasi-coherent module with the
module of its sections.

That spelling of the unit is the one the right-hand end of the computation produces, by
`…TopDegreeBaseChange.unitToPushforwardUnit_comp_pushforwardUnitIsoAffineTilde_inv`. Writing the
Eilenberg-Watts module of `Φ` through it — rather than through `AlgebraicGeometry.tildeSelf`,
which is the other canonical choice — is what lets the two computations of conclusion (c) meet
with no further coherence: the comparison of the Eilenberg-Watts presentation with the geometry
is free to use any identification of that module, because
`…TopDegreeBaseChange.bijective_fromExtendScalarsComp` takes it as an arbitrary isomorphism.

## Main definitions

All in the namespace `Stacks.AlgebraicGeometry.TopDegreeBaseChange`.

* `pullbackTildeIsoPullbackAffineTilde`: **the crossing**, `((f' ∣_ V) ≫ V.isoSpec)^* M~ ≅
  (f' ∣_ V)^* (affineTilde V M)`, for an arbitrary module `M` over the functions on `V` and with
  no hypothesis on `f'` or on the ambient base.
* `pullbackTildeUnitIso`: **the crossing at the base ring is the structure sheaf**,
  `((f' ∣_ V) ≫ V.isoSpec)^* Γ(V, ⊤)~ ≅ 𝒪_{f'⁻¹(V)}`, written through
  `Stacks.Coherent.affineTildeObjSectionsIso`.

## Main results

* `pullbackTildeIsoPullbackAffineTilde_naturality`: **the crossing is natural**, which is what
  carries a map of modules over the functions on `V` from one spelling to the other.

## Implementation notes

*The crossing is the first two factors of `…TopDegreeBaseChange.pullbackTildeSectionsIso`.* That
isomorphism, which the right-hand end of the computation of conclusion (c) uses, is defined as
the crossing followed by the pullback of `affineTilde` applied to
`sectionsIsoPushforwardUnitSections`; it is written in terms of the crossing rather than
repeating it, so that the unit and the general module are handled by one declaration and the
naturality is available there.

*Why the crossing is an isomorphism of functors and not of objects.* Naturality is the whole use
made of it, and at the functor level it is free — `CategoryTheory.NatIso.naturality_1`. Built
object by object it would have to be proved.

*Why `Stacks.Coherent.affineTilde` of the base ring is the sections of the structure sheaf by
`rfl`.* `(SheafOfModules.evaluation Z.ringCatSheaf (op ⊤)).obj (Scheme.unitModule Z)` and
`ModuleCat.of Γ(Z, ⊤) Γ(Z, ⊤)` are the same term, so the identification of the structure sheaf
with the module associated to its sections is already an isomorphism at the spelling the
Eilenberg-Watts presentation produces, and no transport intervenes.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open scoped ChangeOfRings

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

/-- **Pulling back along `(f' ∣_ V) ≫ V.isoSpec` is restricting to `V` and then pulling back
along `f' ∣_ V`.** The two routes from the modules on `Spec Γ(V, ⊤)` to those on `f'⁻¹(V)` agree,
by `AlgebraicGeometry.Scheme.Modules.pullbackComp` and the identification of restriction along an
open immersion with pullback along it.

It is stated as an isomorphism of **functors** so that the crossing below is natural with no
further work: naturality is what carries a map of modules over the functions on `V` across the
two spellings, and that is the whole use made of it. -/
def pullbackIsoRestrictPullback {X' Y' : Scheme.{u}} (f' : X' ⟶ Y') (V : Y'.Opens)
    [IsAffine (V : Scheme)] :
    Scheme.Modules.pullback ((f' ∣_ V) ≫ (V : Scheme).isoSpec.hom) ≅
      Scheme.Modules.restrictFunctor (V : Scheme).isoSpec.hom ⋙
        Scheme.Modules.pullback (f' ∣_ V) :=
  (Scheme.Modules.pullbackComp (f' ∣_ V) (V : Scheme).isoSpec.hom).symm ≪≫
    (Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback (V : Scheme).isoSpec.hom)
      (Scheme.Modules.pullback (f' ∣_ V))).symm

/-- **The two tilde functors over an affine open of the base, crossed.** For a morphism
`f' : X' ⟶ Y'`, an affine open `V` of `Y'` and a module `M` over the functions on `V`, the
pullback of `M~` along `(f' ∣_ V) ≫ V.isoSpec` is the pullback along `f' ∣_ V` of the module
`Stacks.Coherent.affineTilde` associates to `M` on `V` itself. Neither `Y'` nor `f'` carries a
hypothesis; only `V` is affine.

This is `pullbackIsoRestrictPullback` at `M~`, so it is natural in `M`. -/
def pullbackTildeIsoPullbackAffineTilde {X' Y' : Scheme.{u}} (f' : X' ⟶ Y') (V : Y'.Opens)
    [IsAffine (V : Scheme)] (M : ModuleCat.{u} Γ((V : Scheme), ⊤)) :
    (Scheme.Modules.pullback ((f' ∣_ V) ≫ (V : Scheme).isoSpec.hom)).obj
        ((AlgebraicGeometry.tilde.functor (CommRingCat.of Γ((V : Scheme), ⊤))).obj M) ≅
      (Scheme.Modules.pullback (f' ∣_ V)).obj ((Stacks.Coherent.affineTilde (V : Scheme)).obj M) :=
  (pullbackIsoRestrictPullback f' V).app
    ((AlgebraicGeometry.tilde.functor (CommRingCat.of Γ((V : Scheme), ⊤))).obj M)

/-- **The crossing carries the pullback of a map of tilde modules to the pullback of the map of
`affineTilde` modules.** This is the naturality of `pullbackIsoRestrictPullback`, read at the
image of a map under `AlgebraicGeometry.tilde.functor`. -/
theorem pullbackTildeIsoPullbackAffineTilde_naturality {X' Y' : Scheme.{u}} (f' : X' ⟶ Y')
    (V : Y'.Opens) [IsAffine (V : Scheme)] {M N : ModuleCat.{u} Γ((V : Scheme), ⊤)}
    (ψ : M ⟶ N) :
    (pullbackTildeIsoPullbackAffineTilde f' V M).inv ≫
        (Scheme.Modules.pullback ((f' ∣_ V) ≫ (V : Scheme).isoSpec.hom)).map
          ((AlgebraicGeometry.tilde.functor (CommRingCat.of Γ((V : Scheme), ⊤))).map ψ) ≫
        (pullbackTildeIsoPullbackAffineTilde f' V N).hom =
      (Scheme.Modules.pullback (f' ∣_ V)).map
        ((Stacks.Coherent.affineTilde (V : Scheme)).map ψ) :=
  NatIso.naturality_1 (pullbackIsoRestrictPullback f' V)
    ((AlgebraicGeometry.tilde.functor (CommRingCat.of Γ((V : Scheme), ⊤))).map ψ)

/-- **At the base ring the crossing lands on the structure sheaf.** The pullback of
`Γ(V, ⊤)~` along `(f' ∣_ V) ≫ V.isoSpec` is `𝒪_{f'⁻¹(V)}`, through the crossing, the
identification `Stacks.Coherent.affineTildeObjSectionsIso` of the structure sheaf of `V` with the
module associated to its global sections, and
`AlgebraicGeometry.Scheme.Modules.pullbackUnitIso`.

This is the spelling of the Eilenberg-Watts unitor that the right-hand end of the computation of
conclusion (c) of [Stacks, Tag 0EX3] produces. -/
def pullbackTildeUnitIso {X' Y' : Scheme.{u}} (f' : X' ⟶ Y') (V : Y'.Opens)
    [IsAffine (V : Scheme)] :
    (Scheme.Modules.pullback ((f' ∣_ V) ≫ (V : Scheme).isoSpec.hom)).obj
        ((AlgebraicGeometry.tilde.functor (CommRingCat.of Γ((V : Scheme), ⊤))).obj
          (ModuleCat.of Γ((V : Scheme), ⊤) Γ((V : Scheme), ⊤))) ≅
      Scheme.unitModule (f' ⁻¹ᵁ V : Scheme) :=
  pullbackTildeIsoPullbackAffineTilde f' V
      (ModuleCat.of Γ((V : Scheme), ⊤) Γ((V : Scheme), ⊤)) ≪≫
    (Scheme.Modules.pullback (f' ∣_ V)).mapIso
      (Stacks.Coherent.affineTildeObjSectionsIso (V : Scheme)
        (Scheme.unitModule (V : Scheme)) inferInstance) ≪≫
    Scheme.Modules.pullbackUnitIso (f' ∣_ V)

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
