module

public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.AffineComparison
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.PushforwardAffine
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A quasi-coherent module on an affine scheme is the module of its global sections

On an affine scheme `Z`, a quasi-coherent `𝒪_Z`-module `N` is isomorphic to the module associated
to its global sections: `Γ(N, ⊤)~ ≅ N`. For the direct image of the structure sheaf along an
affine morphism `q : P ⟶ Z` this gives `Γ(q_* 𝒪_P, ⊤)~ ≅ q_* 𝒪_P`, the identification
`h_* 𝒪_{Y''} ≅ R''~` in the proof of conclusion (c) of [Stacks, Tag 0EX3].

## Main definitions

* `Stacks.Coherent.affineTildeObjSectionsIso`: a quasi-coherent module on an affine scheme is the
  module associated to its global sections.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.pushforwardUnitIsoAffineTilde`: for an affine
  morphism `q : P ⟶ Z` with `Z` affine, `q_* 𝒪_P` is the module associated to `Γ(q_* 𝒪_P, ⊤)`.

## Implementation notes

The isomorphism `Γ(N, ⊤)~ ≅ N` is the counit of `Stacks.Coherent.affineTildeAdjunction` at `N`.
It is constructed as the preimage of the unit isomorphism `Stacks.Coherent.affineTildeSectionsIso`
under the fully faithful functor of global sections on quasi-coherent modules,
`Stacks.Coherent.affineQuasicoherentSectionsFullyFaithful`, which avoids identifying the essential
image of `affineTilde` with the quasi-coherent modules.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01I7](https://stacks.math.columbia.edu/tag/01I7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace Stacks.Coherent

/-- For an affine scheme `Z` and a quasi-coherent `𝒪_Z`-module `N`, the isomorphism
`Γ(N, ⊤)~ ≅ N` between the module associated to the global sections of `N` and `N`. -/
def affineTildeObjSectionsIso (Z : Scheme.{u}) [IsAffine Z] (N : Z.Modules)
    (hN : N.IsQuasicoherent) :
    (affineTilde Z).obj ((SheafOfModules.evaluation Z.ringCatSheaf (op ⊤)).obj N) ≅ N :=
  (ObjectProperty.ι (SheafOfModules.isQuasicoherent Z.ringCatSheaf)).mapIso
    ((affineQuasicoherentSectionsFullyFaithful Z).preimageIso
      (X := ⟨(affineTilde Z).obj ((SheafOfModules.evaluation Z.ringCatSheaf (op ⊤)).obj N),
        affineTilde_quasicoherent Z _⟩)
      (Y := ⟨N, hN⟩)
      (affineTildeSectionsIso Z
        ((SheafOfModules.evaluation Z.ringCatSheaf (op ⊤)).obj N)).symm)

end Stacks.Coherent

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

/-- For an affine morphism `q : P ⟶ Z` into an affine scheme `Z`, the isomorphism
`Γ(q_* 𝒪_P, ⊤)~ ≅ q_* 𝒪_P` between the module associated to the global sections of the direct
image of the structure sheaf and that direct image. -/
@[ega "I 9.2.1" "special case", ega "II 1.2.6" "special case", sga "3 I 4.2" "special case"]
def pushforwardUnitIsoAffineTilde {P Z : Scheme.{u}} [IsAffine Z] (q : P ⟶ Z) [IsAffineHom q] :
    (Stacks.Coherent.affineTilde Z).obj
        ((SheafOfModules.evaluation Z.ringCatSheaf (op ⊤)).obj
          ((Scheme.Modules.pushforward q).obj (Scheme.unitModule P))) ≅
      (Scheme.Modules.pushforward q).obj (Scheme.unitModule P) :=
  Stacks.Coherent.affineTildeObjSectionsIso Z _
    (Stacks.Modules.isQuasicoherent_pushforward_of_isAffineHom q _ inferInstance)

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
