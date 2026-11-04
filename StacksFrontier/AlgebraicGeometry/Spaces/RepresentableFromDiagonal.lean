module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableByAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableProperty

/-!
# Representability by algebraic spaces read off the diagonal

Let `S` be a scheme contained in a big fppf site `B` and let `F` be a presheaf of sets on the
big fppf site of `S` whose diagonal `Δ_F : F ⟶ F ⨯ F` is representable by algebraic spaces.
Then *every* morphism `f : X ⟶ F` whose source is an algebraic space over `S` is representable
by algebraic spaces.

The reason is the identity `h_U ×_F X = (h_U ⨯ X) ×_{F ⨯ F} F`: the fibre product of a
scheme-valued point of `F` with `X` is a base change of `Δ_F` along `ξ ⨯ f`, so it maps to the
algebraic space `h_U ⨯ X` by a morphism representable by algebraic spaces, and Stacks 02YS then
makes it an algebraic space.

## Main results

* `CategoryTheory.Limits.isPullback_diag_prodMap` is the identity above as a cartesian square,
  in an arbitrary category with binary products.
* `AlgebraicGeometry.Space.isRepresentableByAlgebraicSpaces_of_diagonal` is the consequence for
  presheaves on the big fppf site.
* `AlgebraicGeometry.Space.isAlgebraicSpace_of_representableDiagonal_of_representableCriterion`
  applies it to turn the hypotheses of condition (5) of Stacks 04S6 into the hypotheses of its
  condition (3). It is stated with condition (3) itself as a hypothesis, so it does not prove
  either condition; what it does prove is that condition (3) implies condition (5).

## Implementation notes

**No Stacks tag attribute is placed.** Representability of a morphism out of an algebraic
space deduced from representability of the diagonal is used by Chapter 80 (Bootstrap), and no
tag has been identified whose statement is exactly
`AlgebraicGeometry.Space.isRepresentableByAlgebraicSpaces_of_diagonal`: it is *not* Stacks 046K,
which runs the other way (from a representable surjective flat atlas to representability of the
diagonal *by schemes*). The declarations are therefore left unregistered — see the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/LocallySurjectiveFlatPresentation.lean`, which does the
same for Stacks 04S1.

The last declaration carries condition (3) of Stacks 04S6 as a hypothesis and must not be
tagged with the 04S6 part (5) key: a hypothesis-carried conclusion is not a landing of the
part. It is recorded here because the implication it proves — that condition (3) suffices for
condition (5), the converse of the reduction the source performs with Stacks 046K — is the step
that lets a proof of condition (3) discharge condition (5) without repeating any of its work.

The product `h_U ⨯ X` is shown to be an algebraic space inline rather than as a separate
declaration, to avoid colliding with any `isAlgebraicSpace_prod` a concurrent file may add.

## References

* [Stacks Project, Tag 02YQ](https://stacks.math.columbia.edu/tag/02YQ)
* [Stacks Project, Tag 02YS](https://stacks.math.columbia.edu/tag/02YS)
* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]

/-- A fibre product of `f : X ⟶ Z` and `g : Y ⟶ Z` is a base change of the diagonal of `Z`
along `prod.map f g : X ⨯ Y ⟶ Z ⨯ Z`. -/
lemma isPullback_diag_prodMap {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {p : W ⟶ X} {q : W ⟶ Y}
    (h : IsPullback p q f g) :
    IsPullback (p ≫ f) (prod.lift p q) (diag Z) (prod.map f g) := by
  have hw : (p ≫ f) ≫ diag Z = prod.lift p q ≫ prod.map f g := by
    refine prod.hom_ext ?_ ?_
    · simp
    · simp [h.w]
  have key₁ : ∀ s : PullbackCone (diag Z) (prod.map f g),
      s.fst = (s.snd ≫ prod.fst) ≫ f := by
    intro s
    have := s.condition =≫ (prod.fst : Z ⨯ Z ⟶ Z)
    simpa using this
  have key₂ : ∀ s : PullbackCone (diag Z) (prod.map f g),
      s.fst = (s.snd ≫ prod.snd) ≫ g := by
    intro s
    have := s.condition =≫ (prod.snd : Z ⨯ Z ⟶ Z)
    simpa using this
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk hw
    (fun s => h.lift (s.snd ≫ prod.fst) (s.snd ≫ prod.snd)
      (by rw [← key₁ s]; exact key₂ s))
    (fun s => ?_) (fun s => ?_) (fun s m hm₁ hm₂ => ?_))
  · rw [← Category.assoc, h.lift_fst]
    exact (key₁ s).symm
  · exact prod.hom_ext (by simp) (by simp)
  · refine h.hom_ext ?_ ?_
    · rw [h.lift_fst]
      have := hm₂ =≫ (prod.fst : X ⨯ Y ⟶ X)
      simpa using this
    · rw [h.lift_snd]
      have := hm₂ =≫ (prod.snd : X ⨯ Y ⟶ Y)
      simpa using this

end CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- If the diagonal of a presheaf `F` on the big fppf site of `S` is representable by algebraic
spaces, then every morphism to `F` whose source is an algebraic space over `S` is representable
by algebraic spaces.

For a scheme-valued point `ξ : h_U ⟶ F`, the fibre product `h_U ×_F X` is a base change of
`Δ_F` along `ξ ⨯ f`, hence the morphism `h_U ×_F X ⟶ h_U ⨯ X` is representable by algebraic
spaces (Stacks 03Y0). Both `h_U` and `X` are algebraic spaces and the final object of the site
represents one, so `h_U ⨯ X` is an algebraic space (Stacks 02X2); Stacks 02YS then makes
`h_U ×_F X` an algebraic space. -/
theorem isRepresentableByAlgebraicSpaces_of_diagonal
    {F X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hdiag : IsRepresentableByAlgebraicSpaces B S hS (diag F))
    (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ F) :
    IsRepresentableByAlgebraicSpaces B S hS f := by
  intro U ξ
  have hU : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
  have hprod : IsAlgebraicSpace B S hS (yoneda.obj U ⨯ X) := by
    have hT : IsTerminal (Over.mk (𝟙 (B.obj hS)) : BigFppfOver B S hS) := Over.mkIdTerminal
    have hYT : IsAlgebraicSpace B S hS (yoneda.obj (Over.mk (𝟙 (B.obj hS)))) :=
      isAlgebraicSpace_yoneda B S hS _
    have hYTterm : IsTerminal (yoneda.obj (Over.mk (𝟙 (B.obj hS)) : BigFppfOver B S hS)) :=
      hT.isTerminalObj yoneda _
    have hp : IsAlgebraicSpace B S hS
        (pullback (hYTterm.from (yoneda.obj U)) (hYTterm.from X)) :=
      isAlgebraicSpace_pullback B S hS _ _ hU hX hYT
    exact isAlgebraicSpace_of_iso B S hS
      ((limit.isLimit (pair (yoneda.obj U) X)).conePointUniqueUpToIso
        (isProductOfIsTerminalIsPullback _ _ _ _ hYTterm
          (pullbackIsPullback _ _))).symm hp
  have hsq : IsPullback (pullback.fst ξ f ≫ ξ)
      (prod.lift (pullback.fst ξ f) (pullback.snd ξ f)) (diag F) (prod.map ξ f) :=
    isPullback_diag_prodMap (IsPullback.of_hasPullback ξ f)
  have hrep : IsRepresentableByAlgebraicSpaces B S hS
      (prod.lift (pullback.fst ξ f) (pullback.snd ξ f)) :=
    isRepresentableByAlgebraicSpaces_of_isPullback B S hS _ _ (diag F) (prod.map ξ f) hsq hdiag
  exact AlgebraicGeometry.isAlgebraicSpace_of_isRepresentableByAlgebraicSpaces B S hS _ hrep
    hprod

/-- **The implication (3) ⟹ (5) of Stacks 04S6**, which is the converse of the reduction the
source performs with Stacks 046K.

Condition (5) of Stacks 04S6 asks for a sheaf `F` with `Δ_F` representable by algebraic spaces
together with an algebraic space `X` and a surjective, flat, locally finitely presented
`f : X ⟶ F`. Condition (3) asks instead that `f` itself be representable by algebraic spaces.
`AlgebraicGeometry.Space.isRepresentableByAlgebraicSpaces_of_diagonal` supplies exactly that
from the diagonal, so the criterion of condition (3) — carried here as the hypothesis
`hcrit` — applies verbatim.

This declaration proves neither condition. It is deliberately untagged: its conclusion is
carried by its hypothesis, and tagging it would register a part of Stacks 04S6 that is not
proved. -/
theorem isAlgebraicSpace_of_representableDiagonal_of_representableCriterion
    (hcrit : ∀ {G Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : Y ⟶ G),
      Presheaf.IsSheaf (BigFppfOver.topology B S hS) G →
      IsAlgebraicSpace B S hS Y →
      ∀ hg : IsRepresentableByAlgebraicSpaces B S hS g,
        IsSurjective B S hS g →
        HasProperty B S hS (fun ⦃_ _⦄ φ => IsFlat B S hS φ.hom) g hg →
        HasProperty B S hS
          (fun ⦃_ _⦄ φ => IsLocallyOfFinitePresentation B S hS φ.hom) g hg →
        IsAlgebraicSpace B S hS G)
    {F X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (hdiag : IsRepresentableByAlgebraicSpaces B S hS (diag F))
    (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ F)
    (hsurj : IsSurjective B S hS f)
    (hflat : ∀ (T : BigFppfOver B S hS) (ξ : yoneda.obj T ⟶ F),
      IsFlat B S hS (pullback.fst ξ f))
    (hlfp : ∀ (T : BigFppfOver B S hS) (ξ : yoneda.obj T ⟶ F),
      IsLocallyOfFinitePresentation B S hS (pullback.fst ξ f)) :
    IsAlgebraicSpace B S hS F :=
  hcrit f hF hX (isRepresentableByAlgebraicSpaces_of_diagonal B S hS hdiag hX f) hsurj
    hflat hlfp

end AlgebraicGeometry.Space

end
