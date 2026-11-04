module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.ModuliSeparation.QuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Stacks.ModuliSeparation.DiagonalDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.ModuliSeparation.ChangeOfBaseUniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Stacks.ModuliSeparation.SpaceSeparationBridge
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAbsolute
public import StacksFrontier.AlgebraicGeometry.Spaces.Separated
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversalHomeomorphism

/-!
# Separation of the target of a universal homeomorphism (Stacks 0DUY)

Stacks 0DUY: let `𝒳` be an algebraic stack with finite inertia and `f : 𝒳 ⟶ M` the moduli space of
the Keel–Mori theorem (Stacks 0DUT); if `𝒳` is quasi-separated, so is `M`, and if `𝒳` is separated,
so is `M`. The proof uses one property of `f`, that it is a universal homeomorphism, which is part
of the conclusion of Stacks 0DUT. It is proved here for every universal homeomorphism `f` from an
algebraic stack to an algebraic space, which is the source's statement with its hypothesis
weakened; the finiteness of inertia is not used.

The proof is the source's. Write `Δ_𝒳` and `Δ_M` for the diagonals; then
`Δ_M ∘ f = (f × f) ∘ Δ_𝒳`, and `f × f` is a universal homeomorphism.

* Quasi-separatedness: `Δ_M` is quasi-compact because `Δ_𝒳` is and `f` is surjective. It is
  tested on fibre products of affine schemes over `M` (Stacks 0AHR), which are covered by
  quasi-compact fibre products over `𝒳` (Stacks 075S); see
  `AlgebraicGeometry.Stack.isAbsolutelyQuasiSeparated_of_universalHomeomorphism`.
* Separatedness: `Δ_𝒳` is proper, hence universally closed, hence so is `Δ_M ∘ f`, hence `Δ_M`
  (Stacks 0CQK), and `M` is separated by Stacks 04Y0 (in the form Stacks 04YS). Both notions are
  absolute, i.e. over `Spec ℤ`; the argument is run over the terminal scheme after Construction A
  of Stacks 04X5, along which universal closedness is carried
  (`AlgebraicGeometry.Stack.universallyClosed_constructionAHom`).

## Main results

* `AlgebraicGeometry.Stack.isAbsolutelySeparated_of_universalHomeomorphism`: part (2).
* `isAbsolutelyQuasiSeparated_and_isAbsolutelySeparated_of_universalHomeomorphism`, in the
  namespace `AlgebraicGeometry.Stack`: **Stacks 0DUY**, parts (1) and (2).

## Implementation notes

Part (3) of the source reads "Add more here, for example relative versions of the above" and
asserts nothing. The absolute separation properties of Stacks 050D and Stacks 03BS are those of
`AlgebraicGeometry.Stack.AlgebraicStacks.IsAbsolutelyQuasiSeparated`,
`...IsAbsolutelySeparated`, `AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated` and
`AlgebraicGeometry.Space.IsAbsolutelySeparated`, all of which read the property over the terminal
scheme and take its containment in the site as the parameter `hZ`. The universal homeomorphism is
`AlgebraicGeometry.Stack.AlgebraicStacks.UniversalHomeomorphism` (Stacks 0CI7).

## References

* [Stacks Project, Tag 0DUY](https://stacks.math.columbia.edu/tag/0DUY)
* [Stacks Project, Tag 0DUT](https://stacks.math.columbia.edu/tag/0DUT)
* [Stacks Project, Tag 04Y0](https://stacks.math.columbia.edu/tag/04Y0)
* [Stacks Project, Tag 0AHR](https://stacks.math.columbia.edu/tag/0AHR)
* [Stacks Project, Tag 0CQK](https://stacks.math.columbia.edu/tag/0CQK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A universal homeomorphism of algebraic stacks is universally closed (Stacks 0513): its base
changes are homeomorphisms on points. -/
theorem universallyClosed_of_universalHomeomorphism {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (hf : AlgebraicStacks.UniversalHomeomorphism B S hS f) :
    AlgebraicStacks.UniversallyClosed B S hS f := fun 𝒵 g => by
  let := pointTopology B S hS (twoFibreProductSquareAlgebraicStacks B S hS g f).pt.val
  let := pointTopology B S hS 𝒵.val
  exact (hf 𝒵 g).isClosedMap

/-- A universal homeomorphism of algebraic stacks is surjective: its base change along the
identity is a homeomorphism on points, and it factors that base change up to a 2-isomorphism. -/
theorem isSurjective_of_universalHomeomorphism {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (hf : AlgebraicStacks.UniversalHomeomorphism B S hS f) :
    IsSurjective B S hS f := by
  set C := twoFibreProductSquareAlgebraicStacks B S hS (𝟙 𝒴) f
  have hsurj : Function.Surjective (AlgebraicStacks.pointsMap B S hS C.fst) := by
    let := pointTopology B S hS C.pt.val
    let := pointTopology B S hS 𝒴.val
    exact (hf 𝒴 (𝟙 𝒴)).surjective
  have h := AlgebraicStacks.pointsMap_eq_of_hom₂ B S hS C.iso.hom
  rw [Category.comp_id, AlgebraicStacks.pointsMap_comp] at h
  rw [h] at hsurj
  exact hsurj.of_comp

variable (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **Stacks 0DUY, part (2).** The target of a universal homeomorphism out of a separated
algebraic stack is separated. Let `f : 𝒳 ⟶ M` be a universal homeomorphism (Stacks 0CI7) from an
algebraic stack over `S` to an algebraic space over `S`. If `𝒳` is separated (Stacks 050D
part (7)), then `M` is separated (Stacks 03BS part (1)).

Everything is read over the terminal scheme: Construction A of Stacks 04X5 carries `𝒳` and the
stack of `M` there, and `f` to a 1-morphism which is still universally closed
(`AlgebraicGeometry.Stack.universallyClosed_constructionAHom`) and surjective. The relative
diagonal of `𝒳` there is proper, hence universally closed, so the relative diagonal of the stack
of `M` is universally closed by Stacks 0CQK
(`AlgebraicGeometry.Stack.AlgebraicStacks.universallyClosed_relativeDiagonal_of_comp`). That stack
is represented by the lower-shriek extension of `M`, which is therefore separated over the
terminal scheme (Stacks 04YS, 04Y0), that is, `M` is separated. -/
theorem isAbsolutelySeparated_of_universalHomeomorphism
    {𝒳 : AlgebraicStacks.{u, w} B S hS} {M : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hM : IsAlgebraicSpace B S hS M) (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS M hM)
    (hf : AlgebraicStacks.UniversalHomeomorphism B S hS f)
    (h𝒳 : AlgebraicStacks.IsAbsolutelySeparated.{u, w} B S hS hZ 𝒳) :
    Space.IsAbsolutelySeparated B S hS hZ M := by
  let γ : B.obj hS ⟶ B.obj hZ := ⟨terminal.from S⟩
  let 𝓜 := algebraicSpaceStack.{u, w} B S hS M hM
  let f' := constructionAHom B S (⊤_ Scheme.{u}) hS hZ γ f
  have hUC : AlgebraicStacks.UniversallyClosed B (⊤_ Scheme.{u}) hZ f' :=
    universallyClosed_constructionAHom B S (⊤_ Scheme.{u}) hS hZ γ f
      (universallyClosed_of_universalHomeomorphism B S hS f hf)
  have hsurj : IsSurjective B (⊤_ Scheme.{u}) hZ f' :=
    (pointsMap_surjective_changeBaseFunctor_iff B S (⊤_ Scheme.{u}) hS hZ γ
      𝒳.val.isFiberedInGroupoids 𝓜.val.isFiberedInGroupoids f.hom.hom).2
      (isSurjective_of_universalHomeomorphism B S hS f hf)
  have hΔ𝒳 : AlgebraicStacks.UniversallyClosed B (⊤_ Scheme.{u}) hZ
      (relativeDiagonalAlgebraicStacks B (⊤_ Scheme.{u}) hZ
        (f' ≫ structureMorphism B (⊤_ Scheme.{u}) hZ
          (changeBaseAlgebraicStack B S (⊤_ Scheme.{u}) hS hZ γ 𝓜))) := by
    rw [comp_structureMorphism]
    exact AlgebraicStacks.universallyClosed_relativeDiagonalAlgebraicStacks_of_isSeparated B
      (⊤_ Scheme.{u}) hZ _ h𝒳
  have hΔ𝓜 := AlgebraicStacks.universallyClosed_relativeDiagonal_of_comp B (⊤_ Scheme.{u}) hZ
    f' _ hUC hsurj hΔ𝒳
  exact isSeparatedOver_of_universallyClosed_relativeDiagonal_of_equivalenceOver.{u, w}
    B (⊤_ Scheme.{u}) hZ (isAlgebraicSpace_viewOver B S (⊤_ Scheme.{u}) hS hZ γ M hM)
    (PresheafOfCategories.relocalizeElementsEquivalenceOver γ M) hΔ𝓜

/-- **Stacks 0DUY.** Let `f : 𝒳 ⟶ M` be a universal homeomorphism (Stacks 0CI7) from an algebraic
stack over `S` to an algebraic space over `S` — for instance the moduli space of the Keel–Mori
theorem (Stacks 0DUT) of an algebraic stack with finite inertia, which is a universal
homeomorphism. Then
1. if `𝒳` is quasi-separated, then `M` is quasi-separated;
2. if `𝒳` is separated, then `M` is separated.

Both properties are absolute (Stacks 050D parts (7), (8) and Stacks 03BS parts (1), (3)). Part (3)
of the source ("Add more here") asserts nothing. -/
@[stacks 0DUY]
theorem isAbsolutelyQuasiSeparated_and_isAbsolutelySeparated_of_universalHomeomorphism
    {𝒳 : AlgebraicStacks.{u, w} B S hS} {M : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hM : IsAlgebraicSpace B S hS M) (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS M hM)
    (hf : AlgebraicStacks.UniversalHomeomorphism B S hS f) :
    (AlgebraicStacks.IsAbsolutelyQuasiSeparated.{u, w} B S hS hZ 𝒳 →
        Space.IsAbsolutelyQuasiSeparated B S hS hZ M) ∧
      (AlgebraicStacks.IsAbsolutelySeparated.{u, w} B S hS hZ 𝒳 →
        Space.IsAbsolutelySeparated B S hS hZ M) :=
  ⟨isAbsolutelyQuasiSeparated_of_universalHomeomorphism B S hS hZ hM f hf,
    isAbsolutelySeparated_of_universalHomeomorphism B S hS hZ hM f hf⟩

/-- **Stacks 0DUY for the model-independent universal homeomorphism.** The statement of
`isAbsolutelyQuasiSeparated_and_isAbsolutelySeparated_of_universalHomeomorphism` above, with `f`
a universal homeomorphism in the sense of
`AlgebraicGeometry.Stack.UniversalHomeomorphism`, which tests every 2-fibre product and so in
particular the canonical one. -/
theorem isAbsolutelyQuasiSeparated_and_isAbsolutelySeparated_of_universalHomeomorphism_anyModel
    {𝒳 : AlgebraicStacks.{u, w} B S hS} {M : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hM : IsAlgebraicSpace B S hS M) (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS M hM)
    (hf : UniversalHomeomorphism B S hS f) :
    (AlgebraicStacks.IsAbsolutelyQuasiSeparated.{u, w} B S hS hZ 𝒳 →
        Space.IsAbsolutelyQuasiSeparated B S hS hZ M) ∧
      (AlgebraicStacks.IsAbsolutelySeparated.{u, w} B S hS hZ 𝒳 →
        Space.IsAbsolutelySeparated B S hS hZ M) :=
  isAbsolutelyQuasiSeparated_and_isAbsolutelySeparated_of_universalHomeomorphism B S hS hZ hM f
    (fun 𝒵 g => hf 𝒵 g (twoFibreProductSquareAlgebraicStacks B S hS g f)
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS g f))

end AlgebraicGeometry.Stack

end
