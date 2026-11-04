module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.RingedToposGlobalSections07MS

/-!
# The base change map (07MT) of [Stacks, Tag 07MS] on global sections

In the situation of [Stacks, Tag 07MJ] with `S = Spec(A)` and `S' = Spec(A')` affine, let `F'` be
an `𝒪_{X'/S'}`-module and `F = f_cris^*F'` its pullback. This file defines the base change map

`RΓ(Cris(X'/S'), F') ⊗^L_{A'} A ⟶ RΓ(Cris(X/S), F)`   (07MT)

in `D(A)` of [Stacks, Tag 07MS], the sheaf-level base change map
`L(S ⟶ S')^* Rτ_{X'/S', *}F' ⟶ Rτ_{X/S, *}F` (`crisSheafBaseChangeMap`) on global sections. It is
the composite of

1. `RΓ(Cris(X'/S'), F') = RΓ(S', Rτ_{X'/S', *}F')`, the Leray identification of
   [Stacks, Tag 0D6H] for `τ_{X'/S'}` (`tauDerivedGlobalSectionsIso`), tensored up;
2. the canonical map `RΓ(S', K) ⊗^L_{A'} A ⟶ RΓ(S, L(S ⟶ S')^*K)` at `K = Rτ_{X'/S', *}F'`
   (`zariskiBaseChangeGlobalSectionsMap`), the transpose across `- ⊗^L_{A'} A ⊣ res` of
   `RΓ(S', -)` of the unit `K ⟶ R(S ⟶ S')_*L(S ⟶ S')^*K`;
3. `RΓ(S, -)` of the sheaf-level base change map;
4. `RΓ(S, Rτ_{X/S, *}F) = RΓ(Cris(X/S), F)`, again [Stacks, Tag 0D6H].

## Main definitions

* `crisGlobalBaseChangeMap`: the base change map (07MT).

## Main results

* `crisGlobalBaseChangeMap_eq`: its factorization through the sheaf-level base change map.

## References

* [Stacks Project, Tag 07MS](https://stacks.math.columbia.edu/tag/07MS)
* [Stacks Project, Tag 07MJ](https://stacks.math.columbia.edu/tag/07MJ)
* [Stacks Project, Tag 0D6H](https://stacks.math.columbia.edu/tag/0D6H)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u wS wS' wA wA'

attribute [local instance 10000] HasDerivedCategory.standard

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S S' : GlobalCrystallineSituation.{u}}
  [HasDerivedCategory.{wS} (ModuleSheaf S)] [HasDerivedCategory.{wS'} (ModuleSheaf S')]
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))]
  [HasDerivedCategory.{wA'} (ModuleCat.{u + 1} Γ(S'.S.scheme, ⊤))]
  (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
  (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber)

/-- **The base change map (07MT) on global sections**

`RΓ(Cris(X'/S'), F') ⊗^L_{A'} A ⟶ RΓ(Cris(X/S), F)`   in `D(A)`,

`A = Γ(S, 𝒪_S)`, `A' = Γ(S', 𝒪_{S'})`, for an `𝒪_{X'/S'}`-module `F'`, its pullback
`F = f_cris^*F'` (`crisModuleInverseImage`) and an arbitrary morphism `g : X ⟶ X'` over a
morphism of divided power bases `f`. It is `RΓ(S, -)` of the sheaf-level base change map
`crisSheafBaseChangeMap`, preceded by the canonical map
`RΓ(S', K) ⊗^L_{A'} A ⟶ RΓ(S, L(S ⟶ S')^*K)` at `K = Rτ_{X'/S', *}F'` and read through
`RΓ(S, Rτ_*-) = RΓ(Cris, -)` at both ends. -/
@[stacks 07MS "the base change map RΓ(Cris(X'/S'), F') ⊗^L_{A'} A ⟶ RΓ(Cris(X/S), F) of (07MT)
in D(A), the sheaf-level base change map read on global sections, for an arbitrary g : X ⟶ X'"]
def crisGlobalBaseChangeMap (F' : ModuleSheaf S') :
    (derivedBaseChangeTensor f).obj
        (DerivedCategory.Plus.ι.obj ((derivedModuleGlobalSections S').obj F')) ⟶
      DerivedCategory.Plus.ι.obj
        ((derivedModuleGlobalSections S).obj ((crisModuleInverseImage f g h).obj F')) :=
  (derivedBaseChangeTensor f).map (tauDerivedGlobalSectionsIso S' F').inv ≫
    zariskiBaseChangeGlobalSectionsMap f (tauDerivedDirectImage S' F') ≫
      (zariskiDerivedGlobalSections S.S.scheme).map (crisSheafBaseChangeMap f g h F') ≫
        (tauDerivedGlobalSectionsIso S ((crisModuleInverseImage f g h).obj F')).hom

/-- **(07MT) is the sheaf-level base change map on global sections**: the factorization of
`crisGlobalBaseChangeMap` through `crisSheafBaseChangeMap`. -/
theorem crisGlobalBaseChangeMap_eq (F' : ModuleSheaf S') :
    crisGlobalBaseChangeMap f g h F' =
      (derivedBaseChangeTensor f).map (tauDerivedGlobalSectionsIso S' F').inv ≫
        zariskiBaseChangeGlobalSectionsMap f (tauDerivedDirectImage S' F') ≫
          (zariskiDerivedGlobalSections S.S.scheme).map (crisSheafBaseChangeMap f g h F') ≫
            (tauDerivedGlobalSectionsIso S ((crisModuleInverseImage f g h).obj F')).hom :=
  rfl

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
