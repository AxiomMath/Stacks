module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartRespectsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Stacks.IntegralAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.IsomPresheafFiniteType
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalFiniteType
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeInertiaBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRelocalize
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.ValuativeUniquenessSeparated
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.DiagonalFibre
public import StacksFrontier.CategoryTheory.Sites.Stack.SlicePointIsomPresheaf

/-!
# The inertia projections are locally of finite type (Stacks 050Q)

Let `S` be a scheme contained in a big fppf site `B`. For an algebraic stack `𝒳` over `S` the
forgetful 1-morphism `π : I_𝒳 ⟶ 𝒳` of the inertia of `𝒳`, and for a 1-morphism `f : 𝒳 ⟶ 𝒴` of
algebraic stacks over `S` the forgetful 1-morphism `π : I_{𝒳/𝒴} ⟶ 𝒳` of the relative inertia,
are locally of finite type, in the relative sense of Properties of Stacks, Section 04XB. These
are the two finiteness assertions of Stacks 050Q; the representability of the two projections by
algebraic spaces is `StacksFrontier/AlgebraicGeometry/Stacks/InertiaProjectionRepresentable.lean`
and `StacksFrontier/AlgebraicGeometry/Stacks/RelativeInertiaProjectionRepresentable.lean`, and the
algebraicity of `I_𝒳` and `I_{𝒳/𝒴}` is
`StacksFrontier/AlgebraicGeometry/Stacks/InertiaAlgebraic.lean`.

The proof is the source's: each inertia is a second 2-fibre product of a diagonal, so each
projection is a base change of that diagonal.

1. The absolute diagonal `Δ : 𝒳 ⟶ 𝒳 × 𝒳` is locally of finite type. Its base change along a
   scheme-valued point of `𝒳 × 𝒳` over `U` is the presheaf of vertical morphisms between the two
   components of that point (`CategoryTheory.TwoFibreProductOver.DiagonalFibre.equivalenceOver`),
   which is the isomorphism sheaf `Isom(x, y)` of the two values at the terminal object
   (`CategoryTheory.Functor.vertHomPresheafIsoIsomPresheafOfPoint`); and that sheaf is locally of
   finite type over `U` by Stacks 04XR.
2. By Stacks 034H (1) the inertia is the second 2-fibre product `𝒳 ×_{Δ, 𝒳 × 𝒳, Δ} 𝒳` of the
   diagonal and `π` is the first projection of the canonical square over the cospan `(Δ, Δ)`,
   hence a base change of `Δ`; so Stacks 045C carries local finite type to `π`, transported along
   that equivalence of sources by Stacks 0457.
3. The relative half is step 2 verbatim with the relative diagonal
   `Δ_f : 𝒳 ⟶ 𝒳 ×_{f, 𝒴, f} 𝒳` in place of `Δ`: the relative inertia is the second 2-fibre
   product `𝒳 ×_{Δ_f, 𝒳 ×_𝒴 𝒳, Δ_f} 𝒳` and `π : I_{𝒳/𝒴} ⟶ 𝒳` is the first projection of the
   canonical square over the cospan `(Δ_f, Δ_f)`. The input replacing step 1 is part (2) of
   Stacks 04XS, the theorem named
   `isLocallyOfFiniteType_relativeDiagonal_of_isAlgebraicStack` in this namespace, which holds
   for an arbitrary 1-morphism of algebraic stacks.

## Main results

* `AlgebraicGeometry.Stack.isLocallyOfFiniteType_diagonal_of_isAlgebraicStack`: step 1, the
  absolute diagonal of an algebraic stack is locally of finite type.
* `AlgebraicGeometry.Stack.isLocallyOfFiniteType_inertiaProjection`: **Stacks 050Q**, the inertia
  projection of an algebraic stack is locally of finite type.
* `AlgebraicGeometry.Stack.isLocallyOfFiniteType_relativeInertiaProjection`: **Stacks 050Q**, the
  relative inertia projection of a 1-morphism of algebraic stacks is locally of finite type.

## Implementation notes

Step 2 is the proof of `AlgebraicGeometry.Stack.isQuasiCompact_inertiaProjection` with the
property changed, and step 1 is the proof of Stacks 0CXI
(`AlgebraicGeometry.Stack.isLocallyOfFiniteType_diagonal`) with its limit-preservation input
replaced by Stacks 04XR; neither needs any hypothesis on the property beyond the fact that it
respects isomorphisms, which for being locally of finite type comes from stability under base
change.

Step 3 reuses the comparison 1-morphisms of
`StacksFrontier/AlgebraicGeometry/Stacks/SecondRelativeDiagonalInertia.lean`, namely
`CategoryTheory.TwoFibreProductOver.ofRelativeInertia` at the `w` field of `f`, where the
absolute half uses them at the degenerate `𝒳.p ⋙ 𝟭 _ = 𝒳.p`. It needs no hypothesis on `f`
beyond `𝒳` and `𝒴` being algebraic stacks, since part (2) of Stacks 04XS needs none.

Local finite type in the sense of Section 04XB is `AlgebraicGeometry.Stack.IsLocallyOfFiniteType`,
the longhand quantifier, rather than `AlgebraicGeometry.Stack.HasRelativeProperty` at
`AlgebraicGeometry.Space.locallyOfFiniteTypeProperty`: the longhand form carries no instance
argument and no proof of representability, and Stacks 045C and Stacks 0457 are stated for it.

The passage between the property of the representing algebraic space read over `U` and read over
`S` is Stacks 04SG, in the form `AlgebraicGeometry.Stack.prop_algebraicSpaceMap_iff` followed by
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_relocalizeToYoneda_iff`, exactly as in Stacks
0CXI. The structural morphism Stacks 04XR speaks of is the one to the terminal presheaf while the
one left after that passage goes to the representable presheaf of `Over.mk (𝟙 U)`; the two are
compared by `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_of_isTerminal`.

The universes are those Stacks 04XR is stated at, `CatFiberedInGroupoids.{u, u, u + 1, u + 1}`,
which are the universes of the 2-category `AlgebraicGeometry.Stack.AlgebraicStacks`.

## References

* [Stacks Project, Tag 050Q](https://stacks.math.columbia.edu/tag/050Q)
* [Stacks Project, Tag 034H](https://stacks.math.columbia.edu/tag/034H)
* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XR](https://stacks.math.columbia.edu/tag/04XR)
* [Stacks Project, Tag 04XS](https://stacks.math.columbia.edu/tag/04XS)
* [Stacks Project, Tag 0CXI](https://stacks.math.columbia.edu/tag/0CXI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The absolute diagonal of an algebraic stack is locally of finite type**, in the sense of
Properties of Stacks, Section 04XB.

The base change of `Δ : 𝒳 ⟶ 𝒳 × 𝒳` along a scheme-valued point of `𝒳 × 𝒳` over `U` is the
presheaf of vertical morphisms between the two components of that point, that is the isomorphism
sheaf `Isom(x, y)` of their values at the terminal object; and `Isom(x, y) ⟶ U` is locally of
finite type by Stacks 04XR. -/
theorem isLocallyOfFiniteType_diagonal_of_isAlgebraicStack
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val) :
    IsLocallyOfFiniteType B S hS (diagonal.{u, u, u + 1} B S hS 𝒳) := by
  classical
  intro U y hy F hF hE
  have hri : (Space.locallyOfFiniteTypeProperty B S hS).RespectsIso :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
      (P := Space.locallyOfFiniteTypeProperty B S hS)
  refine (prop_algebraicSpaceMap_iff B S hS (Space.locallyOfFiniteTypeProperty B S hS)
    U F hF).mpr ?_
  refine (Space.holdsOnEveryEtaleChart_relocalizeToYoneda_iff B U.left.1 S U.left.2 hS U.hom
    (@AlgebraicGeometry.LocallyOfFiniteType.{u}) F).mpr ?_
  have hp := 𝒳.isFiberedInGroupoids
  have hfib : 𝒳.val.p.IsFibered := hp.isFibered
  -- the representing presheaf is the isomorphism sheaf of the two components of the point
  obtain ⟨e⟩ := (TwoFibreProductOver.DiagonalFibre.nonempty_equivalenceOver_fst_iff hp hy F).mp hE
  have eF : F ≅ (Over.iteratedSliceBackward U).op ⋙ 𝒳.val.p.isomPresheaf
      (Functor.sliceValue 𝒳.val.p U (TwoFibreProductOver.DiagonalFibre.Y₁' y)
        (TwoFibreProductOver.DiagonalFibre.h1' hy))
      (Functor.sliceValue 𝒳.val.p U (TwoFibreProductOver.DiagonalFibre.Y₂' y)
        (TwoFibreProductOver.DiagonalFibre.h2' hy)) :=
    ((Functor.whiskeringRight _ _ _).obj uliftFunctor.{u, u}).preimageIso
      (e.symm.trans (Functor.isoWhiskerRight
        (Functor.vertHomPresheafIsoIsomPresheafOfPoint 𝒳.val.p hp U y hy) uliftFunctor.{u, u}))
  -- Stacks 04XR for that isomorphism sheaf
  have hterm : Space.IsLocallyOfFiniteType B U.left.1 U.left.2 (terminal.from F) :=
    (Space.isLocallyOfFiniteType_terminal_iff_of_iso B U.left.1 U.left.2 eF).mpr
      (isLocallyOfFiniteType_isomPresheaf B S hS 𝒳 h𝒳 U _ _)
  exact Space.holdsOnEveryEtaleChart_of_isTerminal B U.left.1 U.left.2 terminalIsTerminal
    (Over.mkIdTerminal.isTerminalObj yoneda _) _ _ hterm

/-- The comparison functor from the relative inertia to the second 2-fibre product is an
equivalence. -/
private theorem isEquivalence_ofRelativeInertia
    {𝒞 𝒮 𝒮' : Type*} [Category 𝒞] [Category 𝒮] [Category 𝒮']
    {p𝒮 : 𝒮 ⥤ 𝒞} {p𝒮' : 𝒮' ⥤ 𝒞} {G : 𝒮 ⥤ 𝒮'} (hG : G ⋙ p𝒮' = p𝒮) :
    Functor.IsEquivalence (TwoFibreProductOver.ofRelativeInertia hG) :=
  (CategoryTheory.Equivalence.mk (TwoFibreProductOver.ofRelativeInertia hG)
    (TwoFibreProductOver.toRelativeInertia hG)
    (eqToIso (TwoFibreProductOver.ofRelativeInertia_comp_toRelativeInertia hG).symm)
    (TwoFibreProductOver.unitIso hG).symm).isEquivalence_functor

/-- A morphism `π : 𝒢 ⟶ 𝒳` is locally of finite type if, up to an equivalence of sources, it is
the first projection of the canonical 2-fibre product square over the cospan `(Δ, Δ)` with `Δ`
locally of finite type. -/
private theorem isLocallyOfFiniteType_of_equivalence_twoFibreProductSquare
    {𝒳 𝒵 𝒢 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (Δ : 𝒳 ⟶ 𝒵)
    (hΔ : IsLocallyOfFiniteType.{u, u, u + 1} B S hS Δ) (π : 𝒢 ⟶ 𝒳)
    (a : 𝒢.val ⥤ᵇ (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} Δ Δ).pt.val)
    (ha : Functor.IsEquivalence a.toFunctor)
    (α : BasedFunctor.comp a
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} Δ Δ).fst.hom ≅
      BasedFunctor.comp π.hom (BasedFunctor.id 𝒳.val)) :
    IsLocallyOfFiniteType.{u, u, u + 1} B S hS π := by
  have := ha
  have : Functor.IsEquivalence (BasedFunctor.id 𝒳.val).toFunctor :=
    inferInstanceAs (Functor.IsEquivalence (𝟭 𝒳.val.obj))
  exact relativeProperty_of_equivalences B S hS (Space.locallyOfFiniteTypeProperty B S hS)
    π.hom _ a (BasedFunctor.id 𝒳.val) α
    (relativeProperty_baseChange.{u, u, u + 1} B S hS (Space.locallyOfFiniteTypeProperty B S hS)
      𝒳 𝒵 𝒳 Δ Δ _
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} _ _) hΔ)

/-- **Stacks 050Q, local finite type of the inertia projection.** The forgetful 1-morphism
`π : I_𝒳 ⟶ 𝒳` of the inertia of an algebraic stack `𝒳` over `S` is locally of finite type, in
the sense of Properties of Stacks, Section 04XB.

By Stacks 034H (1) the inertia is the 2-fibre product `𝒳 ×_{Δ, 𝒳 × 𝒳, Δ} 𝒳`, and under that
identification `π` is the first projection of the canonical 2-fibre product square over the
cospan `(Δ, Δ)`, hence a base change of `Δ`. So this is Stacks 045C applied to
`AlgebraicGeometry.Stack.isLocallyOfFiniteType_diagonal_of_isAlgebraicStack` and transported
along that equivalence of sources by Stacks 0457. -/
@[stacks 050Q "local finite type of the absolute inertia projection"]
theorem isLocallyOfFiniteType_inertiaProjection (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    IsLocallyOfFiniteType B S hS (inertiaProjectionAlgebraicStacks.{u, w} B S hS 𝒳).hom := by
  have hG : 𝒳.val.val.p ⋙ 𝟭 (BigFppfOver B S hS) = 𝒳.val.val.p := Functor.comp_id _
  exact isLocallyOfFiniteType_of_equivalence_twoFibreProductSquare B S hS _
    (isLocallyOfFiniteType_diagonal_of_isAlgebraicStack.{u, w} B S hS 𝒳.val 𝒳.property) _
    ⟨TwoFibreProductOver.ofRelativeInertia hG,
      TwoFibreProductOver.ofRelativeInertia_comp_structureFunctor hG⟩
    (isEquivalence_ofRelativeInertia hG) (Iso.refl _)

/-- **Stacks 050Q, local finite type of the relative inertia projection.** The forgetful
1-morphism `π : I_{𝒳/𝒴} ⟶ 𝒳` of the relative inertia of a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic
stacks over `S` is locally of finite type, in the sense of Properties of Stacks, Section 04XB.

By Stacks 034H (1) the relative inertia is the 2-fibre product `𝒳 ×_{Δ_f, 𝒳 ×_𝒴 𝒳, Δ_f} 𝒳`, and
under that identification `π` is the first projection of the canonical 2-fibre product square
over the cospan `(Δ_f, Δ_f)`, hence a base change of the relative diagonal. So this is Stacks
045C applied to part (2) of Stacks 04XS, transported along that equivalence of sources by
Stacks 0457. -/
@[stacks 050Q "local finite type of the relative inertia projection"]
theorem isLocallyOfFiniteType_relativeInertiaProjection
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) :
    IsLocallyOfFiniteType B S hS (relativeInertiaProjection B S hS f).hom := by
  exact isLocallyOfFiniteType_of_equivalence_twoFibreProductSquare B S hS _
    (isLocallyOfFiniteType_relativeDiagonal_of_isAlgebraicStack.{u, w} B S hS f).choose_spec _
    ⟨TwoFibreProductOver.ofRelativeInertia f.hom.hom.w,
      TwoFibreProductOver.ofRelativeInertia_comp_structureFunctor f.hom.hom.w⟩
    (isEquivalence_ofRelativeInertia f.hom.hom.w) (Iso.refl _)

end AlgebraicGeometry.Stack

end
