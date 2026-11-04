module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CoheratorCanonical
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CoheratorFlatPullback
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.InternalHomModulePullback
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeInternalHom

/-!
# Flat pullback of the quasi-coherent internal Hom (Stacks 0GQP)

Let `f : 𝒳 → 𝒴` be a flat morphism of algebraic stacks, `F` an `𝒪_𝒴`-module of finite
presentation and `G` a quasi-coherent `𝒪_𝒴`-module. **Stacks 0GQP** says that
`f^* hom(F, G) = hom(f^* F, f^* G)`, with `hom(F, G) = Q(SheafHom_{𝒪_𝒴}(F, G))` the quasi-coherent
internal Hom of **Stacks 0GQN**.

The proof is the source's:

* `f^* SheafHom_{𝒪_𝒴}(F, G) = SheafHom_{𝒪_𝒳}(f^* F, f^* G)`
  (`AlgebraicGeometry.Stack.AlgebraicStacks.fppfModulesPullbackInternalHomIso`); as the source
  remarks (Stacks 06TX), flatness of `f` is not used here, and neither is finite presentation;
* `SheafHom_{𝒪_𝒴}(F, G)` lies in `LQCoh^fbc(𝒪_𝒴)` (the membership clause of Stacks 0GQN, which
  uses that `F` is of finite presentation and `G` quasi-coherent), so **Stacks 0GQJ** applies to
  it: `f^* Q_𝒴 = Q_𝒳 f^*` on `LQCoh^fbc`, and here flatness of `f` is used.

The coherator of `hom(F, G)` is the one of `Mod(𝒪_𝒳)`,
`AlgebraicGeometry.Stack.AlgebraicStacks.coherator` (Stacks 0781), while Stacks 0GQJ is stated for
the coherator of `LQCoh^fbc(𝒪_𝒳)` (Stacks 0778); on `LQCoh^fbc(𝒪_𝒳)` the two are right adjoints of
the same inclusion of `QCoh(𝒪_𝒳)` and so agree
(`AlgebraicGeometry.Stack.AlgebraicStacks.coheratorLqcohFbcIso`).

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentHomFlatPullbackIso`: **Stacks 0GQP**.

## References

* [Stacks Project, Tag 0GQP](https://stacks.math.columbia.edu/tag/0GQP)
* [Stacks Project, Tag 0GQN](https://stacks.math.columbia.edu/tag/0GQN)
* [Stacks Project, Tag 0GQJ](https://stacks.math.columbia.edu/tag/0GQJ)
* [Stacks Project, Tag 0GN2](https://stacks.math.columbia.edu/tag/0GN2)
* [Stacks Project, Tag 06TX](https://stacks.math.columbia.edu/tag/06TX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

/-- On `LQCoh^fbc(𝒪_𝒳)` the coherator of `Mod(𝒪_𝒳)` (Stacks 0781) is the coherator of
`LQCoh^fbc(𝒪_𝒳)` (Stacks 0778): both are right adjoint to the inclusion of `QCoh(𝒪_𝒳)`. -/
def coheratorLqcohFbcIso (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).ι ⋙ coherator B S hS 𝒳 ≅
      lqcohFbcCoherator B E h S hS 𝒳 :=
  Adjunction.rightAdjointUniq
    ((lqcohSheafFbcCoheratorAdjunction B S hS 𝒳 E h).ofNatIsoLeft (Iso.refl _))
    (lqcohFbcCoheratorAdjunction B E h S hS 𝒳)

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)

/-- **Stacks 0GQP.** Let `f : 𝒳 ⟶ 𝒴` be a flat morphism of algebraic stacks, `F` an
`𝒪_𝒴`-module of finite presentation and `G` a quasi-coherent `𝒪_𝒴`-module. Then
`f^* hom(F, G) = hom(f^* F, f^* G)`, with `hom` the quasi-coherent internal Hom
`hom(F, G) = Q(SheafHom_{𝒪_𝒴}(F, G))` of Stacks 0GQN.

The isomorphism is the composite of `f^* Q_𝒴 = Q_𝒳 f^*` (Stacks 0GQJ, at
`SheafHom_{𝒪_𝒴}(F, G)`, which lies in `LQCoh^fbc(𝒪_𝒴)` by Stacks 0GQN) with `Q_𝒳` of
`f^* SheafHom_{𝒪_𝒴}(F, G) = SheafHom_{𝒪_𝒳}(f^* F, f^* G)`. -/
@[stacks 0GQP]
def quasicoherentHomFlatPullbackIso (hf : AlgebraicStacks.IsFlat B S hS f)
    (F G : Stack.fppfModules B S hS 𝒴) [F.IsFinitePresentationOnSite]
    (hG : G.IsQuasicoherentOnSite) :
    (quasicoherentPullback B S hS f).obj (quasicoherentHom B S hS 𝒴 F G) ≅
      quasicoherentHom B S hS 𝒳 ((fppfModulesPullback B S hS f).obj F)
        ((fppfModulesPullback B S hS f).obj G) :=
  letI := isIso_lqcohFbcCoheratorPullbackComparison B E h S hS f hf
  let A : (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒴).FullSubcategory :=
    ⟨fppfInternalHom B S hS 𝒴 F G,
      lqcohSheafFbcFppfModules_fppfInternalHom_of_isQuasicoherentOnSite B E h S hS 𝒴 F G hG⟩
  (quasicoherentPullback B S hS f).mapIso ((coheratorLqcohFbcIso B E h S hS 𝒴).app A) ≪≫
    (asIso (lqcohFbcCoheratorPullbackComparison B E h S hS f)).app A ≪≫
    ((coheratorLqcohFbcIso B E h S hS 𝒳).app
      ((lqcohSheafFbcFppfModulesPullback B E h S hS f).obj A)).symm ≪≫
    (coherator B S hS 𝒳).mapIso (fppfModulesPullbackInternalHomIso B S hS f F G)

end AlgebraicGeometry.Stack.AlgebraicStacks

end
