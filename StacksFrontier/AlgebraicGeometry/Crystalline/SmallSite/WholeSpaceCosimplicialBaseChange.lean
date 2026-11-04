module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.WholeSpaceCosimplicialModule
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineBaseChangeSmall
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.QuasicoherentImpliesLocal
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.WholeSpaceSystemAffine

/-!
# The sections of a crystal in one cosimplicial degree are the base change of another's

The double complex of the proof of [Stacks, Proposition 60.21.3, Tag 07LG] carries a completed
connection on `M(b) = lim_e Γ((X, T(b)_e, δ(b)), ℱ)` in each cosimplicial degree, obtained from
the connection of degree zero through the identification `M(b) ≅ D̂(b) ⊗̂_{D̂} M`. This file
proves that identification one level at a time: for every cosimplicial map `φ : ⦋m⦌ ⟶ ⦋n⦌` and
every level `e`,

`Γ(T(n)_e, 𝒪) ⊗_{Γ(T(m)_e, 𝒪)} Γ(T(m)_e, ℱ) ≅ Γ(T(n)_e, ℱ)`.

This is the base change of ambient sections of a crystal on `Cris(X/S)` along a morphism of the
site (`...SmallSite.bijective_crysAmbientBaseChange`), applied to the cosimplicial transition
`...SmallSite.wholeSpaceTrans`, whose source and target have affine ambient schemes
(`...SmallSite.isAffine_target_wholeSpaceSystem`). The passage to the limit over the levels is
not made here.

## Main results

Everything is in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `bijective_wholeSpaceCosimplicialBaseChange` — **the identification at a level**, for a
  crystal whose restriction to the ambient scheme is quasi-coherent.
* `bijective_wholeSpaceCosimplicialBaseChange_of_isQuasicoherentOnSite` — the same with the
  crystal condition read off [Stacks, Lemma 60.14.2, Tag 07IT].
* `bijective_wholeSpaceLevelBaseChange` — the case `m = 0`: the sections in cosimplicial degree
  `n` at a level are the base change of the sections in degree `0` at that level.
* `isQuasicoherent_ambientWholeSpaceSystem` — the quasi-coherence instance those three carry,
  supplied from hypothesis (1) of [Stacks, Tag 07JN].

## References

* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Proposition 60.20.1, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
* [Stacks Project, Lemma 60.14.2, Tag 07IT](https://stacks.math.columbia.edu/tag/07IT)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite Simplicial
open scoped AlgebraicGeometry TensorProduct

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open Crystalline CohomologyRestriction

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.X] [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
  [WholeSpacePresentation S hp] (F : SheafOfModules.{u} (structureSheaf S))

/-- **The ambient scheme of every object of the cosimplicial system is affine.** -/
local instance isAffineTargetWholeSpaceSystem (k l : ℕ) :
    IsAffine (((wholeSpaceSystem S hp).obj (op ⦋k⦌)).obj l).obj.thickening.target.scheme :=
  isAffine_target_wholeSpaceSystem hp k l

/-- **The sections of a crystal over the cosimplicial degree `n` of the system of
[Stacks, Proposition 60.20.1, Tag 07JN] at a level are the base change of its sections over the
degree `m` at that level.**

For `φ : ⦋m⦌ ⟶ ⦋n⦌` and a level `e` the cosimplicial transition
`...SmallSite.wholeSpaceTrans` is a morphism `T(n)_e ⟶ T(m)_e` of `Cris(X/S)` whose two objects
have affine ambient schemes, so `...SmallSite.bijective_crysAmbientBaseChange` applies:

`Γ(T(n)_e, 𝒪) ⊗_{Γ(T(m)_e, 𝒪)} Γ(T(m)_e, ℱ_{T(m)_e}) ≅ Γ(T(n)_e, ℱ_{T(n)_e})`. -/
theorem bijective_wholeSpaceCosimplicialBaseChange {m n : ℕ}
    (φ : (⦋m⦌ : SimplexCategory) ⟶ ⦋n⦌) (e : ℕ)
    [(ambientSchemeOf (((wholeSpaceSystem S hp).obj (op ⦋m⦌)).obj e).obj
      (moduleRestrictionSheaf F
        (((wholeSpaceSystem S hp).obj (op ⦋m⦌)).obj e))).IsQuasicoherent]
    (hcrys : IsSheafCrystal F) :
    Function.Bijective (ambientBaseChangeTensorFun (wholeSpaceTrans hp φ e).hom
      (moduleRestrictionSheaf F (((wholeSpaceSystem S hp).obj (op ⦋m⦌)).obj e))
      (moduleRestrictionSheaf F (((wholeSpaceSystem S hp).obj (op ⦋n⦌)).obj e))
      (moduleFMapSheaf F (wholeSpaceTrans hp φ e))) :=
  bijective_crysAmbientBaseChange F (wholeSpaceTrans hp φ e) hcrys

/-- **The base change identification at a level, from quasi-coherence on the site**, given that
quasi-coherent sheaves on the site are crystals ([Stacks, Lemma 60.14.2, Tag 07IT]). -/
theorem bijective_wholeSpaceCosimplicialBaseChange_of_isQuasicoherentOnSite {m n : ℕ}
    (φ : (⦋m⦌ : SimplexCategory) ⟶ ⦋n⦌) (e : ℕ)
    [(ambientSchemeOf (((wholeSpaceSystem S hp).obj (op ⦋m⦌)).obj e).obj
      (moduleRestrictionSheaf F
        (((wholeSpaceSystem S hp).obj (op ⦋m⦌)).obj e))).IsQuasicoherent]
    (h07IT : ∀ G : SheafOfModules.{u} (structureSheaf S),
      G.IsQuasicoherentOnSite → IsSheafCrystal G)
    (hFq : F.IsQuasicoherentOnSite) :
    Function.Bijective (ambientBaseChangeTensorFun (wholeSpaceTrans hp φ e).hom
      (moduleRestrictionSheaf F (((wholeSpaceSystem S hp).obj (op ⦋m⦌)).obj e))
      (moduleRestrictionSheaf F (((wholeSpaceSystem S hp).obj (op ⦋n⦌)).obj e))
      (moduleFMapSheaf F (wholeSpaceTrans hp φ e))) :=
  bijective_wholeSpaceCosimplicialBaseChange hp F φ e (h07IT F hFq)

/-- **The case `m = 0`**: the sections of a crystal over the cosimplicial degree `n` at a level
are the base change of its sections over the degree `0` at that level, along a cosimplicial map
`φ : ⦋0⦌ ⟶ ⦋n⦌`. -/
theorem bijective_wholeSpaceLevelBaseChange {n : ℕ}
    (φ : (⦋0⦌ : SimplexCategory) ⟶ ⦋n⦌) (e : ℕ)
    [(ambientSchemeOf (((wholeSpaceSystem S hp).obj (op ⦋0⦌)).obj e).obj
      (moduleRestrictionSheaf F
        (((wholeSpaceSystem S hp).obj (op ⦋0⦌)).obj e))).IsQuasicoherent]
    (hcrys : IsSheafCrystal F) :
    Function.Bijective (ambientBaseChangeTensorFun (wholeSpaceTrans hp φ e).hom
      (moduleRestrictionSheaf F (((wholeSpaceSystem S hp).obj (op ⦋0⦌)).obj e))
      (moduleRestrictionSheaf F (((wholeSpaceSystem S hp).obj (op ⦋n⦌)).obj e))
      (moduleFMapSheaf F (wholeSpaceTrans hp φ e))) :=
  bijective_wholeSpaceCosimplicialBaseChange hp F φ e hcrys

/-- **The restriction of a locally quasi-coherent sheaf to the ambient scheme of an object of
the cosimplicial system is quasi-coherent** (hypothesis (1) of [Stacks, Tag 07JN]). -/
theorem isQuasicoherent_ambientWholeSpaceSystem (hF : IsLocallyQuasiCoherent F) (k l : ℕ) :
    (ambientSchemeOf (((wholeSpaceSystem S hp).obj (op ⦋k⦌)).obj l).obj
      (moduleRestrictionSheaf F
        (((wholeSpaceSystem S hp).obj (op ⦋k⦌)).obj l))).IsQuasicoherent :=
  isQuasicoherent_ambientSchemeOf F hF _

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
