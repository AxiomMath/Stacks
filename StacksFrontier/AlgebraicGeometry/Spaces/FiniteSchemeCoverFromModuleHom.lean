module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteSchemeCoverFromAlgebraHom
public import StacksFrontier.AlgebraicGeometry.Spaces.SymmetricAlgebraSheafQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.SymmetricAlgebraSheafUngradedLift

/-!
# A finite and finitely presented cover from a module map reaching the integral cover

Let `π : Y ⟶ X` be an integral surjective morphism from a scheme to a quasi-compact and
quasi-separated algebraic space, finite étale over a quasi-compact dense open `U` and factoring
Zariski locally through an affine étale chart `V`. Then finitely many sections of `π_* 𝒪_Y` over
two étale charts have the following property: every morphism `𝒢 ⟶ π_* 𝒪_Y` from a quasi-coherent
module of finite presentation whose image contains them gives a finite and finitely presented
scheme cover of `X`, finite étale over `U`, factoring Zariski locally through `V`.

The algebra is the symmetric algebra `Sym(𝒢)`, which is quasi-coherent, of finite presentation and
has few sections, and the morphism of algebras is the extension
`AlgebraicGeometry.Space.SymAlgSheaf.algebraLift` of the morphism of modules; its image contains
that of `𝒢 ⟶ π_* 𝒪_Y` in degree one. This reduces the proof of Stacks 0GUN to producing such a
module map (`AlgebraicGeometry.Space.exists_finiteSchemeCover_of_algebraHom` does the rest).

## Main results

* `AlgebraicGeometry.Space.exists_finiteSchemeCover_of_moduleHom`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology

/-- **A finite and finitely presented cover from a module map reaching the integral cover.**
See the module documentation. -/
theorem exists_finiteSchemeCover_of_moduleHom (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    {Y : BigFppfOver B S hS} (π : yoneda.obj Y ⟶ X.1) (hπint : IsIntegralHom B S hS π)
    (hπsurj : IsSurjective B S hS π) (U : Subfunctor X.1) (hU : IsOpenSubspace B S hS U)
    (hUqc : IsQuasiCompactSpace B S hS U.toFunctor)
    (hUdense : Dense (Set.range (pointsMap B S hS U.toFunctor U.ι)))
    (hπUfin : IsFinite B S hS (pullback.fst U.ι π)) (hπUet : IsEtale B S hS (pullback.fst U.ι π))
    {V : BigFppfOver B S hS} (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (p : yoneda.obj V ⟶ X.1) (hp : IsEtale B S hS p) (hpsurj : IsSurjective B S hS p)
    (hfac : FactorsZariskiLocallyThrough B S hS p Y π) :
    ∃ (Vs Us : SmallEtale B S hS X.1) (_ : IsAffine (chartScheme Vs))
      (_ : IsAffine (chartScheme Us))
      (s : Finset ((pushforwardAlgebra B S hS (Over.mk (ObjectProperty.homMk π :
        (⟨yoneda.obj Y, isAlgebraicSpace_yoneda B S hS Y⟩ : AlgebraicSpaces B S hS) ⟶
          X))).right.obj.obj (op Vs)))
      (s' : Finset ((pushforwardAlgebra B S hS (Over.mk (ObjectProperty.homMk π :
        (⟨yoneda.obj Y, isAlgebraicSpace_yoneda B S hS Y⟩ : AlgebraicSpaces B S hS) ⟶
          X))).right.obj.obj (op Us))),
      ∀ (G : SheafOfModules.{u} (structureRingSheaf B S hS X)), G.IsQuasicoherentOnSite →
        SheafOfModules.IsFinitePresentationOnSite G →
        ∀ γ : G ⟶ AlgebraSheaf.underlyingModule (pushforwardAlgebra B S hS
          (Over.mk (ObjectProperty.homMk π :
            (⟨yoneda.obj Y, isAlgebraicSpace_yoneda B S hS Y⟩ : AlgebraicSpaces B S hS) ⟶ X))),
          (∀ x ∈ s, ∃ y, γ.val.app (op Vs) y = x) →
          (∀ x ∈ s', ∃ y, γ.val.app (op Us) y = x) →
          ∃ (Y' : BigFppfOver B S hS) (f : yoneda.obj Y' ⟶ X.1),
            IsFiniteSchemeCoverFiniteEtaleOverDenseOpen B S hS Y' f U ∧
              FactorsZariskiLocallyThrough B S hS p Y' f := by
  obtain ⟨Vs, Us, hVs, hUs, s, s', h⟩ := exists_finiteSchemeCover_of_algebraHom B S hS hZ X hXqc
    hXqs π hπint hπsurj U hU hUqc hUdense hπUfin hπUet hV p hp hpsurj hfac
  refine ⟨Vs, Us, hVs, hUs, s, s', fun G hG hfp γ hs hs' => ?_⟩
  refine h ⟨symmetricAlgebraSheaf B S hS X G, isQuasicoherent_symmetricAlgebraSheaf B S hS X G hG⟩
    (sectionsBelowCutoff_symmetricAlgebraSheaf B S hS X G hG hfp)
    (isFinitePresentation_symmetricAlgebraSheaf B S hS X G hG hfp)
    (SymAlgSheaf.algebraLift B S hS X _ G γ) ?_ ?_ <;> intro x hx <;>
  (first
    | have ⟨y, hy⟩ := hs x hx
    | have ⟨y, hy⟩ := hs' x hx) <;>
  exact ⟨_, (SymAlgSheaf.algebraLift_ungradedIncl_gen B S hS X _ G γ _ y).trans hy⟩


end AlgebraicGeometry.Space

end
