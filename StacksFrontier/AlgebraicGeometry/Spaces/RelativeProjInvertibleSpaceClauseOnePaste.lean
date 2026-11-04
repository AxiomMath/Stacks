module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOneAssembly

/-!
# The paste of clause (1) of Stacks 0D2Z over the binders of the source square

`…InvertibleTwistingRestriction.modulePullback_map_comp_eq_of_squares` takes the source square of
clause (1) at a scheme point as a hypothesis `p^*(e ≫ i ≫ m) ≫ J = K ≫ Φ` at free variables; an
instance must then match the source square
`…InvertibleTwistingRestriction.clauseOneSourceShaped_square` against that pattern, which invents
metavariables for every object and morphism of the square.  This file restates the paste with the
binders of `…InvertibleTwistingRestriction.clauseOneSourceShaped_square` themselves, so that an
instance supplies exactly the arguments of the source square and nothing is matched.

## Main results

* `…InvertibleTwistingRestriction.modulePullback_map_comp_eq_of_shaped_squares`: **the paste of
  the source, middle and target squares of clause (1), over the binders of the source square.**

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

/-- **The point identity of clause (1) of Stacks 0D2Z pasted from three squares, over the binders
of the source square.**  Over the site `B`, the binders and hypotheses are literally those of
`…InvertibleTwistingRestriction.clauseOneSourceShaped_square` (whose conclusion is the source
square `A^*PL ≫ J = K ≫ (c^*φ)^a`, with `PL = pre₁ ≫ pre₂ ≫ r^*ψ_P`).  Over a site `B₂ = B`, let
`a = e ≫ i ≫ m : G ⟶ H` and `b : G ⟶ I` be the two legs, `χ = J₂ ≫ Θ ≫ T₂` the chart map, with
the middle square `Φ₂ ≫ Θ = Ψ` and the target square `K₂ ≫ Ψ ≫ T₂ = p^*b`.  Then, for leaves
heterogeneously equal to those of the source square, `p^*a ≫ χ = p^*b`. -/
theorem modulePullback_map_comp_eq_of_shaped_squares {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {T F : BigFppfOver B S hS} {L P : AlgebraicSpaces B S hS}
    {b' : representedAlgebraicSpace B S hS F ⟶ P} {Ms Tm : Modules.{u, u} B S hS P.1 P.2}
    {N Ns : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj F).ringCatSheaf).FullSubcategory}
    {ψP : Ms ⟶ Tm}
    {E₀ : (modulePullback B S hS b').obj Tm ≅
      ((representedQuasicoherentSchemeEquivalence B S hS F).functor.obj N).obj}
    {Es : (modulePullback B S hS b').obj Ms ≅
      ((representedQuasicoherentSchemeEquivalence B S hS F).functor.obj Ns).obj}
    {φ : Ns ⟶ N}
    (hE : (modulePullback B S hS b').map ψP ≫ E₀.hom =
      Es.hom ≫ ((representedQuasicoherentSchemeEquivalence B S hS F).functor.map φ).hom)
    {A : (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ : AlgebraicSpaces B S hS) ⟶ L}
    {r : L ⟶ P} {c : T ⟶ F} {hab : A ≫ r = representedSpaceMap B S hS c ≫ b'}
    (J : (modulePullback B S hS A).obj ((modulePullback B S hS r).obj Tm) ≅
      ((representedQuasicoherentSchemeEquivalence B S hS T).functor.obj
        (quasicoherentPullbackObj B S hS c N)).obj)
    (hJ : J = modulePullbackCompTransportIso A r (representedSpaceMap B S hS c) b' hab Tm ≪≫
      (modulePullback B S hS (representedSpaceMap B S hS c)).mapIso E₀ ≪≫
        modulePullbackRepresentedQuasicoherentIso B S hS c N)
    {X₀ X₁ : Modules.{u, u} B S hS L.1 L.2}
    {pre₁ : X₀ ⟶ X₁} {pre₂ : X₁ ⟶ (modulePullback B S hS r).obj Ms}
    (PL : X₀ ⟶ (modulePullback B S hS r).obj Tm)
    (hPL : PL = pre₁ ≫ pre₂ ≫ (modulePullback B S hS r).map ψP)
    {A' : (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ : AlgebraicSpaces B S hS) ⟶ L}
    {hab' : A' ≫ r = representedSpaceMap B S hS c ≫ b'}
    (K : (modulePullback B S hS A).obj X₀ ⟶
      ((representedQuasicoherentSchemeEquivalence B S hS T).functor.obj
        (quasicoherentPullbackObj B S hS c Ns)).obj)
    {κ : (modulePullback B S hS A).obj X₀ ⟶
      (modulePullback B S hS A).obj ((modulePullback B S hS r).obj Ms)}
    {τ : (modulePullback B S hS A).obj ((modulePullback B S hS r).obj Ms) ⟶
      (modulePullback B S hS (representedSpaceMap B S hS c)).obj
        ((modulePullback B S hS b').obj Ms)}
    {μ : (modulePullback B S hS (representedSpaceMap B S hS c)).obj
        ((modulePullback B S hS b').obj Ms) ⟶
      (modulePullback B S hS (representedSpaceMap B S hS c)).obj
        ((representedQuasicoherentSchemeEquivalence B S hS F).functor.obj Ns).obj}
    {ρ : (modulePullback B S hS (representedSpaceMap B S hS c)).obj
        ((representedQuasicoherentSchemeEquivalence B S hS F).functor.obj Ns).obj ⟶
      ((representedQuasicoherentSchemeEquivalence B S hS T).functor.obj
        (quasicoherentPullbackObj B S hS c Ns)).obj}
    (hK : K = κ ≫ τ ≫ μ ≫ ρ)
    {κ₀ : X₀ ⟶ (modulePullback B S hS r).obj Ms}
    (hκ : HEq κ ((modulePullback B S hS A').map κ₀))
    (hτ : HEq τ
      (modulePullbackCompTransportIso A' r (representedSpaceMap B S hS c) b' hab' Ms).hom)
    (hμ : μ = (modulePullback B S hS (representedSpaceMap B S hS c)).map Es.hom)
    (hρ : ρ = (modulePullbackRepresentedQuasicoherentIso B S hS c Ns).hom)
    (hA : A' = A) (hκ₀ : κ₀ = pre₁ ≫ pre₂)
    {B₂ : BigFppfSite.{u}} (hB : B = B₂) {S₂ : Scheme.{u}} (hSS : S = S₂)
    {hS₂ : B₂.Contains S₂}
    {Y₂ X₂ : AlgebraicSpaces B₂ S₂ hS₂} (p₂ : Y₂ ⟶ X₂)
    {G₂ M₂ N₂ H₂ I₂ : Modules.{u, u} B₂ S₂ hS₂ X₂.1 X₂.2}
    {E₂ F₂ C₂ : Modules.{u, u} B₂ S₂ hS₂ Y₂.1 Y₂.2}
    (a₂ : G₂ ⟶ H₂) {e₂ : G₂ ⟶ M₂} {i₂ : M₂ ⟶ N₂} {m₂ : N₂ ⟶ H₂} (ha : a₂ = e₂ ≫ i₂ ≫ m₂)
    (b₂ : G₂ ⟶ I₂)
    (χ₂ : (modulePullback B₂ S₂ hS₂ p₂).obj H₂ ⟶ (modulePullback B₂ S₂ hS₂ p₂).obj I₂)
    {J₂ : (modulePullback B₂ S₂ hS₂ p₂).obj H₂ ⟶ E₂} {Θ₂ : E₂ ⟶ F₂}
    {T₂ : F₂ ⟶ (modulePullback B₂ S₂ hS₂ p₂).obj I₂} (hχ : χ₂ = J₂ ≫ Θ₂ ≫ T₂)
    {K₂ : (modulePullback B₂ S₂ hS₂ p₂).obj G₂ ⟶ C₂} {Φ₂ : C₂ ⟶ E₂} {Ψ₂ : C₂ ⟶ F₂}
    (hsch : Φ₂ ≫ Θ₂ = Ψ₂) (htgt : K₂ ≫ Ψ₂ ≫ T₂ = (modulePullback B₂ S₂ hS₂ p₂).map b₂)
    (hY : HEq (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ : AlgebraicSpaces B S hS) Y₂)
    (hX : HEq L X₂) (hp : HEq A p₂) (hG : HEq X₀ G₂) (hM : HEq X₁ M₂)
    (hN : HEq ((modulePullback B S hS r).obj Ms) N₂)
    (hH : HEq ((modulePullback B S hS r).obj Tm) H₂)
    (hEo : HEq ((representedQuasicoherentSchemeEquivalence B S hS T).functor.obj
      (quasicoherentPullbackObj B S hS c N)).obj E₂)
    (hC : HEq ((representedQuasicoherentSchemeEquivalence B S hS T).functor.obj
      (quasicoherentPullbackObj B S hS c Ns)).obj C₂)
    (he : HEq pre₁ e₂) (hi : HEq pre₂ i₂) (hm : HEq ((modulePullback B S hS r).map ψP) m₂)
    (hJ₂ : HEq J.hom J₂) (hK₂ : HEq K K₂)
    (hΦ : HEq ((representedQuasicoherentSchemeEquivalence B S hS T).functor.map
      (quasicoherentPullbackMap B S hS c φ)).hom Φ₂) :
    (modulePullback B₂ S₂ hS₂ p₂).map a₂ ≫ χ₂ = (modulePullback B₂ S₂ hS₂ p₂).map b₂ := by
  have hsrc := clauseOneSourceShaped_square hE J hJ PL hPL K hK hκ hτ hμ hρ hA hκ₀
  subst hPL
  exact modulePullback_map_comp_eq_of_squares hB hSS hsrc p₂ a₂ ha b₂ χ₂ hχ hsch htgt
    hY hX hp hG hM hN hH hEo hC he hi hm hJ₂ hK₂ hΦ

end AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

end
