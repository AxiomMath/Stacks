module

public import StacksFrontier.AlgebraicGeometry.Quot.RelativeDerivedHomZariskiInputs

/-!
# The sheaf property of the relative Hom presheaves along the Zariski cone

Along the cone `AlgebraicGeometry.Space.zarCone f T h₀` of base changes over the opens of the
test scheme `Z₀`, the relative Hom presheaves of modules
`W ↦ Hom((κ W)^*N, (κ W)^*N')` are sheaves on the opens of `Z₀`
(`AlgebraicGeometry.Space.ZarConeRelHomIsSheaf`).  This is the hypothesis `hsh` of
`CategoryTheory.PullbackData.existsUnique_relHomMap_glue` at the underived datum
`AlgebraicGeometry.Space.modulePullbackDataTopos` and the cone `zarCone f T h₀`.

Nothing here is registered.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (T : SchemesOver Y)
  {Z₀ : BigFppfOver B S hS} (h₀ : Z₀ ⟶ T.left)

/-- **The relative Hom presheaves of modules along the Zariski cone are sheaves**: for all modules
`N`, `N'` on `X_{T_{Z₀}}`, the presheaf `W ↦ Hom(N|_{X_{T_W}}, N'|_{X_{T_W}})` on the opens of
`Z₀` is a sheaf.  This is the hypothesis `hsh` of
`CategoryTheory.PullbackData.existsUnique_relHomMap_glue` at `modulePullbackDataTopos` and
`zarCone f T h₀`. -/
def ZarConeRelHomIsSheaf : Prop :=
  ∀ N N' : Modules.{u, u} B S hS (baseChangeSpace f (restrictTest T h₀)).1
      (baseChangeSpace f (restrictTest T h₀)).2,
    ((modulePullbackDataTopos B S hS).relHomOpens (modulePullbackDataTopos_isCoherent B S hS)
      (zarCone f T h₀) N N').IsSheaf

end AlgebraicGeometry.Space

end
