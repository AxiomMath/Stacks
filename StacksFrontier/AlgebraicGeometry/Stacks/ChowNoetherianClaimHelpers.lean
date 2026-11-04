module

public import StacksFrontier.AlgebraicGeometry.Stacks.ChowRelativeSections
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowSubstackGerbe
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowLemmaSchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeOverOpenSubscheme
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.IntegralQuasiSeparatedStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeInertiaSetoidTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.SecondRelativeDiagonalInertia

/-!
# Immersions, gerbes and quasi-compact inertia for algebraic stacks

* `isImmersion_of_twoIso`: being an immersion depends on a 1-morphism of algebraic stacks only up
  to 2-isomorphism.
* `isGerbeOver_algebraicSpaceStackMap_of_isIso`: the 1-morphism induced by an isomorphism of
  algebraic spaces is a gerbe.
* `isQuasiCompactMorphism_inertiaProjection_of_isQuasiSeparated`: an algebraic stack
  quasi-separated over an algebraic space has quasi-compact inertia.

## References

* [Stacks Project, Tag 0CQ8](https://stacks.math.columbia.edu/tag/0CQ8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory Opposite

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Being an immersion depends on a 1-morphism only up to 2-isomorphism**: the 2-commutative
square with identities as horizontal sides transports representability and the relative property
of Stacks 04XB (`AlgebraicGeometry.Stack.relativeProperty_of_equivalences`). -/
theorem isImmersion_of_twoIso {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} {f g : 𝒳 ⟶ 𝒴} (e : f ≅ g)
    (h : IsImmersion B S hS f) : IsImmersion B S hS g := by
  have ha : Functor.IsEquivalence (BasedFunctor.id 𝒳.val.val).toFunctor :=
    inferInstanceAs (Functor.IsEquivalence (𝟭 𝒳.val.val.obj))
  have hb : Functor.IsEquivalence (BasedFunctor.id 𝒴.val.val).toFunctor :=
    inferInstanceAs (Functor.IsEquivalence (𝟭 𝒴.val.val.obj))
  let e' : f.hom ≅ g.hom := Bicategory.InducedBicategory.isoHom e
  let α := twoIsoHomIso B S hS e'
  exact ⟨(isRepresentableByAlgebraicSpaces_iff_of_equivalences B S hS g.hom.hom f.hom.hom
      (BasedFunctor.id _) (BasedFunctor.id _) α).1 h.1,
    relativeProperty_of_equivalences B S hS (fun _ _ k => Space.IsImmersion B S hS k.hom)
      g.hom.hom f.hom.hom (BasedFunctor.id _) (BasedFunctor.id _) α h.2⟩

/-- **The 1-morphism induced by an isomorphism of algebraic spaces is a gerbe.** Its inverse
followed by it is the identity, a gerbe, and the inverse is an equivalence of the underlying
categories, its two composites being identities on the nose. -/
theorem isGerbeOver_algebraicSpaceStackMap_of_isIso {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (t : X ⟶ Y) [IsIso t] :
    IsGerbeOver B S hS (algebraicSpaceStackMap.{u, w} B S hS hX hY t) := by
  have h₁ : algebraicSpaceStackMap.{u, w} B S hS hY hX (inv t) ≫
      algebraicSpaceStackMap.{u, w} B S hS hX hY t = 𝟙 _ := by
    rw [← algebraicSpaceStackMap_comp_eq, IsIso.inv_hom_id, algebraicSpaceStackMap_id_eq]
  have h₂ : algebraicSpaceStackMap.{u, w} B S hS hX hY t ≫
      algebraicSpaceStackMap.{u, w} B S hS hY hX (inv t) = 𝟙 _ := by
    rw [← algebraicSpaceStackMap_comp_eq, IsIso.hom_inv_id, algebraicSpaceStackMap_id_eq]
  have hu : (CatFiberedInGroupoids.homFunctor
      (algebraicSpaceStackMap.{u, w} B S hS hY hX (inv t)).hom).IsEquivalence := by
    refine (CategoryTheory.Equivalence.mk (CatFiberedInGroupoids.homFunctor
      (algebraicSpaceStackMap.{u, w} B S hS hY hX (inv t)).hom)
      (CatFiberedInGroupoids.homFunctor (algebraicSpaceStackMap.{u, w} B S hS hX hY t).hom)
      (eqToIso ?_) (eqToIso ?_)).isEquivalence_functor
    · exact (congrArg (fun m => CatFiberedInGroupoids.homFunctor m.hom) h₁).symm
    · exact congrArg (fun m => CatFiberedInGroupoids.homFunctor m.hom) h₂
  exact isGerbeOver_of_isEquivalence_comp B S hS _ _ (𝟙 _) hu (eqToIso h₁)
    (CategoryTheory.isGerbeOver_id _ (algebraicSpaceStack.{u, w} B S hS Y hY).val.property)

/-- **The inertia of an algebraic stack quasi-separated over an algebraic space is
quasi-compact.** Let `f : 𝒳 ⟶ Y` be a quasi-separated 1-morphism to an algebraic space. The
fibres of `Y` are thin (Stacks 02ZX), so the absolute inertia of `𝒳` is the relative inertia of
`f`, on the nose over `𝒳`; the relative inertia is `𝒳 ×_{Δ_f, 𝒳 ×_Y 𝒳, Δ_f} 𝒳` over `𝒳`
(Stacks 034H), whose projection is a base change of the quasi-compact `Δ_f`. This is the step
"`𝒳` is quasi-separated, hence its inertia is quasi-compact" of the proof of Stacks 0CQ8, without
passing through absolute quasi-separatedness. -/
theorem isQuasiCompactMorphism_inertiaProjection_of_isQuasiSeparated
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (hf : IsQuasiSeparated B S hS f) :
    IsQuasiCompactMorphism.{u, w} B S hS (inertiaProjectionAlgebraicStacks B S hS 𝒳) := by
  have hrel : Stack.IsQuasiCompact B S hS (relativeInertiaProjection B S hS f).hom :=
    @relativeProperty_of_equivalences B S hS _ _ _ _ (Space.quasiCompactProperty B S hS)
      (relativeInertiaProjection B S hS f).hom.hom
      (twoFibreProductSquareAlgebraicStacks B S hS
        (relativeDiagonalAlgebraicStacks B S hS f)
        (relativeDiagonalAlgebraicStacks B S hS f)).fst.hom.hom
      (relativeInertiaToSecondRelativeDiagonal B S hS f.hom).hom
      (BasedFunctor.id 𝒳.val.val) (eqToIso rfl)
      (isEquivalence_relativeInertiaToSecondRelativeDiagonal B S hS f.hom)
      (Stack.isEquivalence_basedFunctorId B S hS 𝒳.val)
      (relativeProperty_baseChange.{u, u, u + 1} B S hS (Space.quasiCompactProperty B S hS)
        𝒳.val (twoFibreProductAlgebraicStack B S hS f f).val 𝒳.val
        (relativeDiagonalAlgebraicStacks B S hS f).hom
        (relativeDiagonalAlgebraicStacks B S hS f).hom
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
          (relativeDiagonalAlgebraicStacks B S hS f).hom
          (relativeDiagonalAlgebraicStacks B S hS f).hom)
        (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
          (relativeDiagonalAlgebraicStacks B S hS f).hom
          (relativeDiagonalAlgebraicStacks B S hS f).hom)
        hf.1)
  have hset := isFiberedInSetoids_of_isRepresentableByAlgebraicSpace B S hS _
    (isRepresentableByAlgebraicSpace_fibredCategory B S hS Y hY)
  have habs : Stack.IsQuasiCompact B S hS (inertiaProjectionAlgebraicStacks B S hS 𝒳).hom :=
    @relativeProperty_of_equivalences B S hS _ _ _ _ (Space.quasiCompactProperty B S hS)
      (inertiaProjectionAlgebraicStacks B S hS 𝒳).hom.hom
      (relativeInertiaProjection B S hS f).hom.hom
      (ofAbsoluteInertia B S hS f hset).hom.hom
      (BasedFunctor.id 𝒳.val.val) (eqToIso rfl)
      (isEquivalence_ofAbsoluteInertia B S hS f hset)
      (Stack.isEquivalence_basedFunctorId B S hS 𝒳.val) hrel
  exact (isQuasiCompact_iff_baseChange_quasiCompact B S hS
    (inertiaProjectionAlgebraicStacks B S hS 𝒳)
    (isRepresentableByAlgebraicSpaces_inertiaProjection_of_isAlgebraicStack.{u, u, u + 1, w}
      B S hS 𝒳.val 𝒳.property)).1 habs

end AlgebraicGeometry.Stack.AlgebraicStacks

end
