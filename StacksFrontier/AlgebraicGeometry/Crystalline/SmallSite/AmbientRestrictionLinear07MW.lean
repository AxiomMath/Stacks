module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalDeRhamLinear07MW
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.Formula07MK

/-!
# The restriction `G ↦ G_T` on sheaves of `A`-modules

Fix a global crystalline situation `(p, (S, I, γ), X)` of [Stacks, Tag 07MF], write
`A = Γ(S, 𝒪_S)`, and let `(U, T, δ)` be an object of `Cris(X/S)`.  The restriction
`G ↦ G_T : Ab(Cris(X/S)) ⥤ Ab(T_Zar)` of [Stacks, Tag 07IQ] is
`...SmallSite.CrystallineThickening.abelianAmbientRestriction`.  This file lifts it to sheaves of
`A`-modules (`...SmallSite.BaseModuleSheaf`), and applies it to the `A`-linear de Rham complex
`...SmallSite.crystalDeRhamLinearComplex` of a crystal in quasi-coherent modules, giving the
restricted complex `K_T` as a complex of sheaves of `A`-modules on `T_Zar`.  The action of `A` on
`G_T(W) = G(A|_W)` is the one of `G`, i.e. through `Γ(S, 𝒪_S) ⟶ Γ(W, 𝒪_T)`.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `CrystallineThickening.linearAmbientRestriction A` — **`G ↦ G_T` on sheaves of `A`-modules**,
  `Stacks.ModuleCatLift.moduleLift` of `abelianAmbientRestriction A`.
* `CrystallineThickening.crystalDeRhamLinearAmbientComplex A hF` — the restriction `K_T` of the
  `A`-linear de Rham complex.

## Main results

* `CrystallineThickening.linearAmbientRestriction_comp_forget` — forgetting the `A`-action after
  `linearAmbientRestriction A` is `abelianAmbientRestriction A` after forgetting it, on the nose.
* `CrystallineThickening.crystalDeRhamLinearAmbientComplex_forget` — the abelian complex
  underlying `K_T` is `abelianAmbientRestriction A` applied to the abelian complex underlying the
  `A`-linear de Rham complex, on the nose.

## References

* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
* [Stacks Project, Tag 07MW](https://stacks.math.columbia.edu/tag/07MW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening

variable {S : GlobalCrystallineSituation.{u}} (A : CrystallineThickening S)

/-- Forgetting the `A`-action carries sheaves of `A`-modules on `T_Zar` to abelian sheaves. -/
instance instHasSheafComposeForget₂Ambient :
    (Opens.grothendieckTopology A.obj.thickening.target.scheme).HasSheafCompose
      (forget₂ (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) AddCommGrpCat.{u + 1}) :=
  Stacks.ModuleSheaf.hasSheafCompose_forget₂.{u + 1} _ _

/-- Forgetting the `A`-action on sheaves of `A`-modules on `T_Zar` is additive. -/
instance instAdditiveForgetAmbient : (sheafCompose (Opens.grothendieckTopology
    A.obj.thickening.target.scheme)
      (forget₂ (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) AddCommGrpCat.{u + 1})).Additive where
  map_add := by intros; rfl

/-- **The restriction `G ↦ G_T` on sheaves of `A`-modules**: the abelian sheaf underlying
`linearAmbientRestriction A G` is `abelianAmbientRestriction A` of the abelian sheaf underlying
`G`, with the action of `A` carried along. -/
def linearAmbientRestriction :
    BaseModuleSheaf S ⥤ Sheaf (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) :=
  Stacks.ModuleCatLift.moduleLift.{u + 1} Γ(S.S.scheme, ⊤) (smallTopology S) _
    (abelianAmbientRestriction A)

/-- Forgetting the `A`-action after `linearAmbientRestriction A` is `abelianAmbientRestriction A`
after forgetting it, on the nose. -/
theorem linearAmbientRestriction_comp_forget :
    linearAmbientRestriction A ⋙ sheafCompose _
        (forget₂ (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) AddCommGrpCat.{u + 1}) =
      baseForget S ⋙ abelianAmbientRestriction A :=
  rfl

/-- `G ↦ G_T` on sheaves of `A`-modules is additive. -/
instance additive_linearAmbientRestriction : (linearAmbientRestriction A).Additive where
  map_add := by intros; rfl

variable {F : SheafOfModules.{u} (structureSheaf S)} (hF : F.IsQuasicoherentOnSite)

/-- **The restriction `K_T` of the `A`-linear de Rham complex** of a crystal in quasi-coherent
modules to the small Zariski site of the ambient scheme `T` of `A`, as a complex of sheaves of
`A`-modules. -/
def crystalDeRhamLinearAmbientComplex :
    CochainComplex (Sheaf (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))) ℤ :=
  ((linearAmbientRestriction A).mapHomologicalComplex _).obj (crystalDeRhamLinearComplex hF)

/-- The abelian complex underlying `K_T` is `abelianAmbientRestriction A` applied to the abelian
complex underlying the `A`-linear de Rham complex, on the nose. -/
theorem crystalDeRhamLinearAmbientComplex_forget :
    ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))
        AddCommGrpCat.{u + 1})).mapHomologicalComplex _).obj
        (crystalDeRhamLinearAmbientComplex A hF) =
      ((abelianAmbientRestriction A).mapHomologicalComplex _).obj
        (((baseForget S).mapHomologicalComplex _).obj (crystalDeRhamLinearComplex hF)) :=
  rfl

end Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening

end

end
