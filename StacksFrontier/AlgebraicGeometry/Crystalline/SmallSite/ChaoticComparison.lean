module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.RightDerivedEdgeIso
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineCohomology
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineGlobalFlat
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.StandardCoverAcyclicity

/-!
# The cohomology of the chaotic subsite of thickenings of the whole space

Fix a global crystalline situation `(p, (S, I, γ), X)` of [Stacks, Tag 07MF] with `X` and `S`
affine, and let `𝒞 ⊆ Cris(X/S)` be the full subcategory of divided power thickenings `(X, T, δ)`
of the whole of `X`, endowed with the chaotic topology of [Stacks, Tag 07GE].  Let
`u = wholeToAffineSubsite : 𝒞 ⥤ AffineCris(X/S)` and let `f_* = (-)|_𝒞` be the direct image of
abelian sheaves along it.

For a locally quasi-coherent sheaf `F` of `𝒪_{X/S}`-modules on `Cris(X/S)` this file proves

`H^j(𝒞, F|_𝒞) ≅ H^j(Cris(X/S), F)` for every `j`,

both sides being read on the abelian sheaf `SmallSite.abelianSheaf F` of the coefficient universe
`u + 1`.

## Main definitions

Everything below lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `lowerShriekToWhole`, `adjunctionLowerShriekToWhole`: the left adjoint `g_!` of `f_*` and the
  adjunction.
* `gammaRestrictAffineToWholeIso`: the isomorphism `Γ(𝒞, f_* -) ≅ Γ(AffineCris(X/S), -)`.
* `lerayRightDerivedGlobalSectionsIso`: the isomorphism
  `R^j Γ(𝒞, f_* F) ≅ R^j Γ(AffineCris(X/S), F)` for an abelian sheaf `F` on `AffineCris(X/S)`
  whose higher direct images vanish in the degrees `1, …, j`.
* `chaoticCohomologyComparisonIso`: the isomorphism `H^j(𝒞, F|_𝒞) ≅ H^j(Cris(X/S), F)` for a
  locally quasi-coherent `𝒪_{X/S}`-module `F`.
* `chaoticCohomologyIso`: the same isomorphism on the underlying cohomology groups.

## References

* [Stacks Project, Tag 07JK](https://stacks.math.columbia.edu/tag/07JK)
* [Stacks Project, Tag 07JJ](https://stacks.math.columbia.edu/tag/07JJ)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
* [Stacks Project, Tag 07GE](https://stacks.math.columbia.edu/tag/07GE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.X] [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))

/-- **The left adjoint `g_!` of the restriction `(-)|_𝒞` to the chaotic subsite**, on abelian
sheaves. -/
abbrev lowerShriekToWhole :
    Sheaf (chaoticTopology S) AddCommGrpCat.{u + 1} ⥤
      Sheaf (affineTopology S) AddCommGrpCat.{u + 1} :=
  (wholeToAffineSubsite (S := S)).sheafPullback AddCommGrpCat.{u + 1}
    (chaoticTopology S) (affineTopology S)

/-- The adjunction `g_! ⊣ (-)|_𝒞` on abelian sheaves. -/
abbrev adjunctionLowerShriekToWhole :
    lowerShriekToWhole (S := S) ⊣ restrictAffineToWhole S :=
  (wholeToAffineSubsite (S := S)).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
    (chaoticTopology S) (affineTopology S)

include hp in
/-- **Restriction to the chaotic subsite does not change global sections**,
`Γ(𝒞, F|_𝒞) ≅ Γ(AffineCris(X/S), F)`, naturally in the abelian sheaf `F` on `AffineCris(X/S)`. -/
def gammaRestrictAffineToWholeIso :
    restrictAffineToWhole S ⋙ chaoticGlobalSections S ≅ affineGlobalSections S :=
  Adjunction.rightAdjointUniq
    ((constantSheafΓAdj (chaoticTopology S) AddCommGrpCat.{u + 1}).comp
      adjunctionLowerShriekToWhole)
    (Adjunction.ofNatIsoLeft (constantSheafΓAdj (affineTopology S) AddCommGrpCat.{u + 1})
      (constantSheafCompLowerShriekIso hp).symm)

include hp in
/-- **The Leray comparison for the restriction to the chaotic subsite.**  For an abelian sheaf `F`
on `AffineCris(X/S)` whose higher direct images along `(-)|_𝒞` vanish in the degrees `1, …, j`,

`R^j Γ(𝒞, F|_𝒞) ≅ R^j Γ(AffineCris(X/S), F)`. -/
def lerayRightDerivedGlobalSectionsIso (F : Sheaf (affineTopology S) AddCommGrpCat.{u + 1})
    (j : ℕ) (hF : ∀ q, 1 ≤ q → q ≤ j → IsZero ((higherDirectImageToWhole S q).obj F)) :
    ((chaoticGlobalSections S).rightDerived j).obj ((restrictAffineToWhole S).obj F) ≅
      ((affineGlobalSections S).rightDerived j).obj F :=
  haveI := SmallSite.preservesInjectiveObjects_restrictAffineToWhole hp
  Stacks.Cohomology.RightDerivedEdgeIso.edgeAppIso (restrictAffineToWhole S)
      (chaoticGlobalSections S) F j hF ≪≫
    (Functor.rightDerivedIsoOfNatIso (gammaRestrictAffineToWholeIso hp) j).app F

include hp in
/-- In Situation [Stacks, Tag 07MF] with `X` and `S` affine, let
`𝒞 ⊆ Cris(X/S)` be the full subcategory of divided power thickenings `(X, T, δ)` of the whole of
`X` with the chaotic topology of [Stacks, Tag 07GE].  Then for every locally quasi-coherent sheaf
`F` of `𝒪_{X/S}`-modules on `Cris(X/S)` and every degree `j`,

`H^j(𝒞, F|_𝒞) ≅ H^j(Cris(X/S), F)`.

Both sides are read on the abelian sheaf `SmallSite.abelianSheaf F` of the coefficient universe
`u + 1`. -/
@[stacks 07JK "for the abelian sheaf SmallSite.abelianSheaf F of the coefficient universe u + 1 \
attached to a locally quasi-coherent sheaf F of 𝒪_{X/S}-modules, which is the generality in which \
the input [Stacks, Tag 07JJ] holds"]
def chaoticCohomologyComparisonIso (F : SheafOfModules.{u} (structureSheaf S))
    (hF : IsLocallyQuasiCoherent F) (j : ℕ) :
    (chaoticCohomologyFunctor S j).obj ((restrictToWhole S).obj (abelianSheaf F)) ≅
      (cohomologyFunctor S j).obj (abelianSheaf F) :=
  ((chaoticRightDerivedGlobalSectionsIso S j).app
      ((restrictAffineToWhole S).obj ((restrictToAffine S).obj (abelianSheaf F)))).symm ≪≫
    lerayRightDerivedGlobalSectionsIso hp ((restrictToAffine S).obj (abelianSheaf F)) j
      (fun q h1 _ => isZero_higherDirectImageToWhole_of_vanishing07JJ S
        (vanishing07JJ_abelianSheaf F hF) q h1) ≪≫
    (affineRightDerivedGlobalSectionsIso S j).app ((restrictToAffine S).obj (abelianSheaf F)) ≪≫
    affineCohomologyIso S (abelianSheaf F) j

include hp in
/-- **The comparison `chaoticCohomologyComparisonIso` on the cohomology groups**: the group
`H^j(𝒞, F|_𝒞)` is isomorphic to `H^j(Cris(X/S), F)`. -/
def chaoticCohomologyIso (F : SheafOfModules.{u} (structureSheaf S))
    (hF : IsLocallyQuasiCoherent F) (j : ℕ) :
    AddCommGrpCat.of (chaoticCohomology S ((restrictToWhole S).obj (abelianSheaf F)) j) ≅
      AddCommGrpCat.of (cohomology S (abelianSheaf F) j) :=
  chaoticCohomologyComparisonIso hp F hF j

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
