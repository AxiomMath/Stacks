module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentHomDescentExtensionByZero
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentHomDescentTriangle
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentMayerVietorisStageCover
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentPerfectInduction
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentSituationIso
public import StacksFrontier.Topology.Sheaves.Cohomology.MayerVietoris.ExtSequence

/-!
# The union step of Stacks 0DI7 through the Mayer--Vietoris triangle

For a ringed space covered by two opens `U` and `V`, every object `E` of the derived category
sits in the distinguished triangle of Stacks 08BU

  `j_{U∩V!}(E|_{U∩V}) ⟶ j_{U!}(E|_U) ⊕ j_{V!}(E|_V) ⟶ E ⟶ j_{U∩V!}(E|_{U∩V})[1]`.

This file reads that triangle at the concrete derived functors `D(j^*) ⋙ D(j_!)` and uses it
for the union step of the induction of Stacks 08DR in the proof of Stacks 0DI7: the conclusion of
0DI7 for the shifts of a first argument, on the restrictions to two quasi-compact opens `U₀`, `V₀`
of `X₀` and to their intersection, gives it on the restriction to `U₀ ∪ V₀`. On `U₀ ∪ V₀` the
triangle has third vertex the restriction of the first argument, and the conclusion at an
extension by zero `j_{A!}(E|_A)` is the conclusion on `A`.

## Main results

* `Stacks.ExtensionByZero.exists_distTriang_derivedExtensionRestriction`: the triangle of
  Stacks 08BU at the concrete derived functors of extension by zero of a restriction.
* `Stacks.ExtensionByZero.derivedExtensionRestrictionShiftIso`: extension by zero of the
  restriction commutes with the shift.
* `AlgebraicGeometry.RelativeDescentSituation.restrictHomDescent_shift_sup`: **the union step.**

## References

* [Stacks Project, Tag 08BU](https://stacks.math.columbia.edu/tag/08BU)
* [Stacks Project, Tag 0DI7](https://stacks.math.columbia.edu/tag/0DI7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TopologicalSpace Opposite
open AlgebraicGeometry

universe u

namespace Stacks.ExtensionByZero

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

/-- **The Mayer--Vietoris triangle of Stacks 08BU at the concrete derived functors.** For two
opens `U` and `V` covering `X` and an object `E` of `D(𝒪_X)` there is a distinguished triangle
`j_{U∩V!}(E|_{U∩V}) ⟶ j_{U!}(E|_U) ⊕ j_{V!}(E|_V) ⟶ E ⟶ j_{U∩V!}(E|_{U∩V})[1]`. -/
theorem exists_distTriang_derivedExtensionRestriction (U V : Opens X) (hUV : U ⊔ V = ⊤)
    (E : DerivedCategory (SheafOfModules.{u} O)) :
    ∃ (f : (derivedExtensionRestriction O (U ⊓ V)).obj E ⟶
        (derivedExtensionRestriction O U).obj E ⊞ (derivedExtensionRestriction O V).obj E)
      (g : (derivedExtensionRestriction O U).obj E ⊞ (derivedExtensionRestriction O V).obj E ⟶
        E)
      (h : E ⟶ ((derivedExtensionRestriction O (U ⊓ V)).obj E)⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang (DerivedCategory (SheafOfModules.{u} O)) := by
  obtain ⟨iU, iV, δ, -, -, hT⟩ := distinguished_extensionRestriction_triangle O U V hUV
    (derivedExtensionRestriction O U) (derivedExtensionRestriction O V)
    (derivedExtensionRestriction O (U ⊓ V))
    (derivedExtensionRestrictionFactorsh O U).inv
    (derivedExtensionRestrictionFactorsh O V).inv
    (derivedExtensionRestrictionFactorsh O (U ⊓ V)).inv
  exact ⟨_, _, _, hT E⟩

/-- Extension by zero of the restriction to an open commutes with the shift. -/
def derivedExtensionRestrictionShiftIso (U : Opens X)
    (E : DerivedCategory (SheafOfModules.{u} O)) (n : ℤ) :
    (derivedExtensionRestriction O U).obj (E⟦n⟧) ≅
      ((derivedExtensionRestriction O U).obj E)⟦n⟧ :=
  ((derivedExtensionRestriction O U).commShiftIso n).app E

end Stacks.ExtensionByZero

namespace AlgebraicGeometry.RelativeDescentSituation

open Stacks.ExtensionByZero Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

attribute [local instance 10000] HasDerivedCategory.standard

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] (D : RelativeDescentSituation.{u, u} I)

/-- The conclusion of Stacks 0DI7 on a quasi-compact open depends only on the isomorphism class
of the first argument. -/
theorem restrictHomDescent_of_iso_fst
    {M M' : DerivedCategory (SheafOfModules.{u} (structureSheafRing D.X₀.left.toRingedSpace))}
    (e : M ≅ M') (L : DerivedCategory (SheafOfModules.{u}
      (structureSheafRing D.X₀.left.toRingedSpace)))
    (U₀ : D.X₀.left.Opens) (hU₀ : IsCompact (U₀ : Set D.X₀.left))
    (h : D.RestrictHomDescent M L U₀ hU₀) : D.RestrictHomDescent M' L U₀ hU₀ :=
  (D.restrict U₀ hU₀).homDescent_of_iso_fst _
    ((derivedPullback U₀.ι.toLRSHom.toShHom).mapIso e) h

/-- The preimage of a quasi-compact open `U₀ ⊆ W₀` in `W₀` is quasi-compact. -/
theorem isCompact_preimage_ι {X : Scheme.{u}} {U₀ W₀ : X.Opens}
    (hU₀ : IsCompact (U₀ : Set X)) (hUW : U₀ ≤ W₀) :
    IsCompact ((W₀.ι ⁻¹ᵁ U₀ : (W₀ : Scheme.{u}).Opens) : Set W₀.toScheme) := by
  refine (W₀.ι.isOpenEmbedding.isInducing.isCompact_preimage_iff ?_).2 hU₀
  rw [Scheme.Opens.range_ι]
  exact hUW

/-- The conclusion of Stacks 0DI7 for all shifts of a first argument passes to biproducts. -/
theorem homDescent_shift_biprod (X Y L : DerivedCategory (SheafOfModules.{u}
      (structureSheafRing D.X₀.left.toRingedSpace)))
    (hX : ∀ n : ℤ, D.HomDescent (X⟦n⟧) L) (hY : ∀ n : ℤ, D.HomDescent (Y⟦n⟧) L) (n : ℤ) :
    D.HomDescent ((X ⊞ Y)⟦n⟧) L := by
  have : PreservesBinaryBiproducts (shiftFunctor (DerivedCategory (SheafOfModules.{u}
      (structureSheafRing D.X₀.left.toRingedSpace))) n) :=
    preservesBinaryBiproducts_of_preservesBinaryProducts _
  exact D.homDescent_of_iso_fst L ((shiftFunctor _ n).mapBiprod X Y).symm
    (D.homDescent_biprod L _ _ (hX n) (hY n))

variable (K₀ L₀ : DerivedCategory (SheafOfModules.{u}
  (structureSheafRing D.X₀.left.toRingedSpace)))

/-- The conclusion of Stacks 0DI7, on `U₀ ∪ V₀`, at the extension by zero from the open cut out
by a quasi-compact `U₀ ≤ U₀ ∪ V₀` of the shifted restriction of the first argument. -/
theorem homDescent_restrict_derivedExtensionRestriction_shift {U₀ W₀ : D.X₀.left.Opens}
    (hU₀ : IsCompact (U₀ : Set D.X₀.left)) (hW₀ : IsCompact (W₀ : Set D.X₀.left))
    (hUW : U₀ ≤ W₀) (n : ℤ) (h : D.RestrictHomDescent (K₀⟦n⟧) L₀ U₀ hU₀) :
    (D.restrict W₀ hW₀).HomDescent
      (((derivedExtensionRestriction
        (structureSheafRing (D.restrict W₀ hW₀).X₀.left.toRingedSpace) (W₀.ι ⁻¹ᵁ U₀)).obj
          ((derivedPullback W₀.ι.toLRSHom.toShHom).obj K₀))⟦n⟧)
      ((derivedPullback W₀.ι.toLRSHom.toShHom).obj L₀) := by
  have hA := isCompact_preimage_ι hU₀ hUW
  have h₁ := (D.restrictHomDescent_restrict_iff (K₀⟦n⟧) L₀ hU₀ hW₀ hA hUW).2 h
  have h₂ := (D.restrict W₀ hW₀).restrictHomDescent_of_iso_fst
    (((derivedPullback W₀.ι.toLRSHom.toShHom).commShiftIso n).app K₀) _ _ hA h₁
  have h₃ := ((D.restrict W₀ hW₀).homDescent_derivedExtensionRestriction_iff
    (W₀.ι ⁻¹ᵁ U₀) hA _ _).2 h₂
  exact (D.restrict W₀ hW₀).homDescent_of_iso_fst _
    (derivedExtensionRestrictionShiftIso _ _ _ n) h₃

/-- **The union step of the induction of Stacks 08DR for Stacks 0DI7.** If the conclusion of
the tag holds for every shift of the first argument on the restrictions to quasi-compact opens
`U₀`, `V₀` and `U₀ ∩ V₀`, then it holds for every shift of the first argument on the restriction
to `U₀ ∪ V₀`. The Mayer--Vietoris triangle of Stacks 08BU on `U₀ ∪ V₀` exhibits the restriction
of the first argument as the third vertex of a triangle whose other vertices are extensions by
zero from the three opens. -/
theorem restrictHomDescent_shift_sup (U₀ V₀ : D.X₀.left.Opens)
    (hU₀ : IsCompact (U₀ : Set D.X₀.left)) (hV₀ : IsCompact (V₀ : Set D.X₀.left))
    (hinf : IsCompact ((U₀ ⊓ V₀ : D.X₀.left.Opens) : Set D.X₀.left))
    (hsup : IsCompact ((U₀ ⊔ V₀ : D.X₀.left.Opens) : Set D.X₀.left))
    (hU : ∀ n : ℤ, D.RestrictHomDescent (K₀⟦n⟧) L₀ U₀ hU₀)
    (hV : ∀ n : ℤ, D.RestrictHomDescent (K₀⟦n⟧) L₀ V₀ hV₀)
    (hC : ∀ n : ℤ, D.RestrictHomDescent (K₀⟦n⟧) L₀ (U₀ ⊓ V₀) hinf) (n : ℤ) :
    D.RestrictHomDescent (K₀⟦n⟧) L₀ (U₀ ⊔ V₀) hsup := by
  obtain ⟨f, g, h, hT⟩ := exists_distTriang_derivedExtensionRestriction
    (structureSheafRing (D.restrict (U₀ ⊔ V₀) hsup).X₀.left.toRingedSpace)
    (D.restrictSupOpenLeft U₀ V₀) (D.restrictSupOpenRight U₀ V₀)
    (D.restrictSupOpenLeft_sup_restrictSupOpenRight U₀ V₀)
    ((derivedPullback (U₀ ⊔ V₀).ι.toLRSHom.toShHom).obj K₀)
  have h₁ : ∀ m : ℤ, (D.restrict (U₀ ⊔ V₀) hsup).HomDescent
      ((Triangle.mk f g h).obj₁⟦m⟧) ((derivedPullback (U₀ ⊔ V₀).ι.toLRSHom.toShHom).obj L₀) :=
    fun m => D.homDescent_restrict_derivedExtensionRestriction_shift K₀ L₀ hinf hsup
      (inf_le_left.trans le_sup_left) m (hC m)
  have h₂ : ∀ m : ℤ, (D.restrict (U₀ ⊔ V₀) hsup).HomDescent
      ((Triangle.mk f g h).obj₂⟦m⟧) ((derivedPullback (U₀ ⊔ V₀).ι.toLRSHom.toShHom).obj L₀) :=
    fun m => (D.restrict (U₀ ⊔ V₀) hsup).homDescent_shift_biprod _ _ _
      (fun k => D.homDescent_restrict_derivedExtensionRestriction_shift K₀ L₀ hU₀ hsup le_sup_left
        k (hU k))
      (fun k => D.homDescent_restrict_derivedExtensionRestriction_shift K₀ L₀ hV₀ hsup le_sup_right
        k (hV k)) m
  exact (D.restrict (U₀ ⊔ V₀) hsup).homDescent_of_iso_fst _
    (((derivedPullback (U₀ ⊔ V₀).ι.toLRSHom.toShHom).commShiftIso n).app K₀).symm
    ((D.restrict (U₀ ⊔ V₀) hsup).homDescent_shift_obj₃ _ _ hT h₁ h₂ n)

/-- **The induction of Stacks 08DR for Stacks 0DI7, run on the shifts of the first argument.**
If the conclusion of the tag holds for every shift of `K₀` on the restriction to every affine open
of `X₀` lying over an affine open of `S₀`, then it holds for `K₀` and `L₀` themselves. -/
theorem homDescent_of_restrictHomDescent_shift_isAffineOpenOverAffine
    (haffine : ∀ (V₀ : D.X₀.left.Opens) (hV₀ : IsAffineOpen V₀),
      D.IsAffineOpenOverAffine V₀ → ∀ n : ℤ, D.RestrictHomDescent (K₀⟦n⟧) L₀ V₀ hV₀.isCompact) :
    D.HomDescent K₀ L₀ := by
  have : QuasiSeparated D.X₀.hom := D.finitePresentation.quasiSeparated
  have : QuasiSeparatedSpace (D.descent.system.obj (op D.descent.base)) :=
    D.descent.quasiSeparated D.descent.base
  have : QuasiSeparatedSpace D.X₀.left := quasiSeparatedSpace_of_quasiSeparated D.X₀.hom
  have hT := D.isCompact_top_X₀
  have hall : ∀ (W : D.X₀.left.Opens) (h : IsCompact (W : Set D.X₀.left)) (n : ℤ),
      D.RestrictHomDescent (K₀⟦n⟧) L₀ W h := by
    intro W hW
    refine _root_.Stacks.AlgebraicGeometry.CompactOpenInduction.of_isCompact_of_basis
      (P := fun W => ∀ (h : IsCompact (W : Set D.X₀.left)) (n : ℤ),
        D.RestrictHomDescent (K₀⟦n⟧) L₀ W h)
      (Q := fun W => D.IsAffineOpenOverAffine W) D.isAffineOpenOverAffine_bot
      (fun _ _ hle hQ => D.isAffineOpenOverAffine_mono hle hQ)
      D.exists_isAffineOpen_isAffineOpenOverAffine (fun V hV hQ _ => haffine V hV hQ) ?_
      W hW hW
    intro U V hU hV hVQ hPU hPV hPinf hsupc
    have hinf : IsCompact ((U ⊓ V : D.X₀.left.Opens) : Set D.X₀.left) :=
      QuasiSeparatedSpace.inter_isCompact (U : Set D.X₀.left) (V : Set D.X₀.left) U.isOpen hU
        V.isOpen hV.isCompact
    exact D.restrictHomDescent_shift_sup K₀ L₀ U V hU hV.isCompact hinf hsupc (hPU hU)
      (hPV hV.isCompact) (hPinf hinf)
  exact D.homDescent_of_iso_fst L₀ ((shiftFunctorZero _ ℤ).app K₀)
    (D.homDescent_of_restrictHomDescent_top (K₀⟦(0 : ℤ)⟧) L₀ hT (hall ⊤ hT 0))

end AlgebraicGeometry.RelativeDescentSituation

end
