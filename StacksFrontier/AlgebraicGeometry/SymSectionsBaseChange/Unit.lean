module

public import StacksFrontier.AlgebraicGeometry.SymGenDegreeOne.Sections
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.Scheme
public import StacksFrontier.AlgebraicGeometry.FromSpecImageTop

/-!
# The sections of a homogeneous piece of `Sym(E)` over an affine open, as an equivalence

Let `X` be a scheme, `E` a quasi-coherent `𝒪_X`-module and `V` an affine open of `X`. The
degree-`n` piece of `AlgebraicGeometry.Scheme.Modules.symmetricAlgebra X E` is the
sheafification of the sectionwise
symmetric power `U ↦ Sym^n_{Γ(X, U)}(Γ(E, U))`, and
`Stacks.SymGraded.AffinePieces.surjective_sheafifyUnit_image_top` says the sheafification unit is
**surjective** on the sections over `V`. **This file supplies the injectivity half and packages
the two as an equivalence**

`Sym^n_{Γ(X, V)}(Γ(E, V)) ≃ Γ(Sym^n(E), V)`.

That identification is the missing input of Tag 0B3V's sixth label recorded at
`Stacks.ProjBundleBaseChangeReduction` — "the identification of `Γ(W, Sym(E'))` with the
symmetric algebra of `Γ(W, E')` over `Γ(X', W)` is absent as a statement" — in its degreewise
form.

## Main results

* `Stacks.PresheafOfModules.injective_sheafifyUnit_app_iff`: **the injectivity criterion.** For a
  locally bijective `u : P ⟶ N` with `N` a sheaf of modules, the sheafification unit of `P` is
  injective on the sections over `Z` if and only if `u` is. This is the statement the
  `Not done here` of `StacksDraft.AlgebraicGeometry.F3.SymGenDegreeOne.Unit` records as provable
  by the same square as its surjective counterpart and not needed by its own consumers.
* `Stacks.PresheafOfModules.injective_sheafifyUnit_app_of_surjective`: injectivity of the unit on
  sections transfers along a locally bijective morphism **that is surjective on the sections over
  the object in question**. Unlike for surjectivity, local bijectivity alone does not suffice;
  see the implementation notes.
* `Stacks.SymGraded.AffinePieces.injective_sheafifyUnit_image_top` and
  `bijective_sheafifyUnit_image_top`: **the sheafification unit of the sectionwise degree-`n`
  symmetric power is injective, hence bijective, on the sections over an affine open.**
* `Stacks.SymGraded.AffinePieces.pieceSectionsEquiv`: **the identification**
  `Sym^n_{Γ(X, V)}(Γ(E, V)) ≃+ Γ(Sym^n(E), V)`, for `n : ℤ` and `V` affine, together with
  `pieceSectionsEquiv_apply`, which says it is the sheafification unit.

## Implementation notes

**The three steps are the three steps of `surjective_sheafifyUnit_image_top`, with one of them
replaced.** Writing `P` for the base-change presheaf of `Sym^n_{Γ(X, V)}(Γ(E, V))` on
`Spec Γ(X, V)` and `Q` for the restriction along `fromSpec` of the sectionwise symmetric power:

1. the unit of `P` is injective over `⊤`, by the criterion at
   `Stacks.AffineBaseChange.toTilde` and `Stacks.AffineBaseChange.injective_toTildeₗ_basicOpen`
   at `1`, since `D(1) = ⊤`;
2. the unit of `Q` is injective over `⊤`;
3. the unit of the sectionwise symmetric power on `X` is injective over `fromSpec ''ᵁ ⊤`, by the
   criterion again, at the restriction along `fromSpec` of that unit.

**Step 2 is where injectivity and surjectivity genuinely differ.** For surjectivity, local
bijectivity of `v : P ⟶ Q` alone carries surjectivity of the unit of `P` over `Z` to
surjectivity of the unit of `Q` over `Z`
(`Stacks.PresheafOfModules.surjective_sheafifyUnit_app_of_isLocallyBijective`): the naturality
square `ψ_v ∘ unit_P = unit_Q ∘ v` has `ψ_v` bijective, so a preimage under `unit_Q` is produced
as `v x`. For injectivity that square gives only that `unit_Q` is injective *on the image of
`v`*, so surjectivity of `v` on the sections over `Z` is needed, and it is available here:
`Stacks.SymGraded.AffinePieces.bijective_toPieceₗ_basicOpen` at `g = 1` is bijectivity of
`toPiece` over `D(1) = ⊤`.

**The equivalence is additive and not linear.** The sheafification unit is a morphism of
presheaves of modules over `𝒪_X`, so its component at `V` is `Γ(X, V)`-linear; but the two sides
of `pieceSectionsEquiv` carry their `Γ(X, V)`-module structures through different routes —
`Stacks.SymGraded.gradedPiece` directly, and `Γ(Sym^n(E), V)` through
`PresheafOfModules.restrictScalars` along the identity — and the consumer of this file is a
*ring* isomorphism of graded rings of sections, which needs only the additive structure. The
linear form is therefore not stated.

## References

* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)

## Not done here

**No tag is claimed.** This is one assertion of Tag 01CG over an affine base. Nothing here is
about the multiplication of
`Sym(E)`; that is in the sibling file
`StacksDraft.AlgebraicGeometry.F3.SymSectionsBaseChange.SectionRing`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ImmersionRestrict
open scoped TensorProduct

namespace Stacks.PresheafOfModules

universe v u t a

section Unit

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{t}} {R : Sheaf J RingCat.{t}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{a}] [HasWeakSheafify J AddCommGrpCat.{a}]

/-- The sheafification of a locally bijective morphism is bijective on the sections over `Z`. -/
private theorem bijective_sheafification_map_app {P Q : _root_.PresheafOfModules.{a} R₀}
    (u : P ⟶ Q) (hinj : _root_.PresheafOfModules.IsLocallyInjective J u)
    (hsurj : _root_.PresheafOfModules.IsLocallySurjective J u) (Z : Cᵒᵖ) :
    Function.Bijective fun x =>
      _root_.PresheafOfModules.Hom.app
        (((_root_.PresheafOfModules.sheafification.{a} α).map u).val) Z x := by
  have := hinj
  have := hsurj
  have := isIso_sheafification_map_of_isLocallyBijective α u
  have : IsIso ((( _root_.PresheafOfModules.sheafification.{a} α).map u).val) :=
    inferInstanceAs (IsIso ((SheafOfModules.forget R).map
      ((_root_.PresheafOfModules.sheafification.{a} α).map u)))
  exact bijective_hom_app (((_root_.PresheafOfModules.sheafification.{a} α).map u).val) Z

/-- **Injectivity of the sheafification unit on the sections over one object, from a locally
bijective comparison with a sheaf.** For `u : P ⟶ N` locally bijective with `N` a sheaf of
modules, the unit of `P` is injective on the sections over `Z` precisely when `u` is. This is the
injective half of `Stacks.PresheafOfModules.surjective_sheafifyUnit_app_iff`, by the same
commuting square. -/
theorem injective_sheafifyUnit_app_iff {P : _root_.PresheafOfModules.{a} R₀}
    (N : SheafOfModules.{a} R)
    (u : P ⟶ (SheafOfModules.forget R ⋙ _root_.PresheafOfModules.restrictScalars α).obj N)
    (hinj : _root_.PresheafOfModules.IsLocallyInjective J u)
    (hsurj : _root_.PresheafOfModules.IsLocallySurjective J u) (Z : Cᵒᵖ) :
    (Function.Injective fun x =>
        _root_.PresheafOfModules.Hom.app (_root_.PresheafOfModules.sheafifyUnit α P) Z x) ↔
      (Function.Injective fun x => _root_.PresheafOfModules.Hom.app u Z x) := by
  have hpsi := bijective_sheafification_map_app α u hinj hsurj Z
  have hN := bijective_sheafifyUnit_forget α N Z
  have hnat := fun x => _root_.PresheafOfModules.unit_naturality_apply (α := α) u Z x
  exact ⟨fun h x y hxy ↦ h (hpsi.1 ((hnat x).trans ((congrArg _ hxy).trans (hnat y).symm))),
    fun h x y hxy ↦ h (hN.1 ((hnat x).symm.trans ((congrArg _ hxy).trans (hnat y))))⟩

/-- **Injectivity of the sheafification unit on sections transfers along a locally bijective
morphism that is surjective on those sections.** No sheaf is involved. The surjectivity
hypothesis cannot be dropped: naturality of the unit gives injectivity of the unit of `Q` only on
the image of `v`. -/
theorem injective_sheafifyUnit_app_of_surjective
    {P Q : _root_.PresheafOfModules.{a} R₀} (v : P ⟶ Q)
    (hinj : _root_.PresheafOfModules.IsLocallyInjective J v)
    (hsurj : _root_.PresheafOfModules.IsLocallySurjective J v) (Z : Cᵒᵖ)
    (hv : Function.Surjective fun x => _root_.PresheafOfModules.Hom.app v Z x)
    (hP : Function.Injective fun x =>
      _root_.PresheafOfModules.Hom.app (_root_.PresheafOfModules.sheafifyUnit α P) Z x) :
    Function.Injective fun x =>
      _root_.PresheafOfModules.Hom.app (_root_.PresheafOfModules.sheafifyUnit α Q) Z x := by
  have hpsi := bijective_sheafification_map_app α v hinj hsurj Z
  have hnat := fun x => _root_.PresheafOfModules.unit_naturality_apply (α := α) v Z x
  intro s t hst
  obtain ⟨x, hx⟩ := hv s
  obtain ⟨y, hy⟩ := hv t
  subst hx
  subst hy
  exact congrArg _ (hP (hpsi.1 ((hnat x).trans (hst.trans (hnat y).symm))))

end Unit

end Stacks.PresheafOfModules

namespace Stacks.SymGraded.AffinePieces

universe u

/-- **The comparison with the associated sheaf is injective on global sections.** `D(1)` is all of
`Spec R`, so this is `Stacks.AffineBaseChange.injective_toTildeₗ_basicOpen` at `1`. -/
theorem injective_toTilde_top {R : CommRingCat.{u}} (N : ModuleCat.{u} R) :
    Function.Injective fun x => PresheafOfModules.Hom.app (AffineBaseChange.toTilde N)
      (op (⊤ : (Spec R).Opens)) x := by
  rw [show (⊤ : (Spec R).Opens) = AffineBaseChange.specBasicOpen (1 : R) from
    PrimeSpectrum.basicOpen_one.symm]
  exact AffineBaseChange.injective_toTildeₗ_basicOpen N 1

/-- **The comparison `toPiece` is bijective on global sections.** `D(1)` is all of
`Spec Γ(X, V)`, so this is `Stacks.SymGraded.AffinePieces.bijective_toPieceₗ_basicOpen` at
`1`. -/
theorem bijective_toPiece_top {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent]
    {V : X.Opens} (hV : IsAffineOpen V) (n : ℤ) :
    Function.Bijective fun x => PresheafOfModules.Hom.app (toPiece E hV n)
      (op (⊤ : (Spec Γ(X, V)).Opens)) x := by
  rw [show (⊤ : (Spec Γ(X, V)).Opens) = AffineBaseChange.specBasicOpen (1 : Γ(X, V)) from
    PrimeSpectrum.basicOpen_one.symm]
  exact bijective_toPieceₗ_basicOpen E hV n 1

variable {X : Scheme.{u}} (E : X.Modules) {V : X.Opens} (hV : IsAffineOpen V) (n : ℤ)

/-- The sheafification unit of the base-change presheaf of `Sym^n_{Γ(X, V)}(Γ(E, V))` is
injective on the global sections of `Spec Γ(X, V)`. -/
theorem injective_sheafifyUnit_affineBaseChange [E.IsQuasicoherent] :
    Function.Injective fun x => PresheafOfModules.Hom.app
      (PresheafOfModules.sheafifyUnit (𝟙 (Spec Γ(X, V)).ringCatSheaf.obj)
        (AffineBaseChange.presheaf (pieceAt E V n))) (op (⊤ : (Spec Γ(X, V)).Opens)) x := by
  refine (Stacks.PresheafOfModules.injective_sheafifyUnit_app_iff
    (𝟙 (Spec Γ(X, V)).ringCatSheaf.obj) (tilde (pieceAt E V n))
    (AffineBaseChange.toTilde (pieceAt E V n))
    (AffineBaseChange.isLocallyInjective_toTilde (pieceAt E V n))
    (AffineBaseChange.isLocallySurjective_toTilde (pieceAt E V n)) (op ⊤)).2 ?_
  exact injective_toTilde_top _

/-- The sheafification unit of the restriction along `fromSpec` of the sectionwise degree-`n`
symmetric power is injective on the global sections of `Spec Γ(X, V)`. -/
theorem injective_sheafifyUnit_presheafRestrict [E.IsQuasicoherent] :
    Function.Injective fun x => PresheafOfModules.Hom.app
      (PresheafOfModules.sheafifyUnit (𝟙 (Spec Γ(X, V)).ringCatSheaf.obj)
        ((presheafRestrict hV.fromSpec).obj (siteGradedPiece E.val n)))
      (op (⊤ : (Spec Γ(X, V)).Opens)) x :=
  Stacks.PresheafOfModules.injective_sheafifyUnit_app_of_surjective _
    (toPiece E hV n) (isLocallyInjective_toPiece E hV n) (isLocallySurjective_toPiece E hV n)
    (op ⊤) (bijective_toPiece_top E hV n).2 (injective_sheafifyUnit_affineBaseChange E n)

/-- **The sheafification unit of the sectionwise degree-`n` symmetric power is injective on the
sections over an affine open.** -/
theorem injective_sheafifyUnit_image_top [E.IsQuasicoherent] (W : X.Opens)
    (hW : hV.fromSpec ''ᵁ (⊤ : (Spec Γ(X, V)).Opens) = W) :
    Function.Injective fun x => PresheafOfModules.Hom.app
      (PresheafOfModules.sheafifyUnit (𝟙 X.ringCatSheaf.obj) (siteGradedPiece E.val n))
      (op W) x := by
  subst hW
  have hunitinj := Stacks.AlgebraicGeometry.SheafifyRestrict.isLocallyInjective_sheafifyUnit
    (siteGradedPiece E.val n)
  have hunitsurj := Stacks.AlgebraicGeometry.SheafifyRestrict.isLocallySurjective_sheafifyUnit
    (siteGradedPiece E.val n)
  exact (Stacks.PresheafOfModules.injective_sheafifyUnit_app_iff
    (𝟙 (Spec Γ(X, V)).ringCatSheaf.obj)
    ((Scheme.Modules.restrictFunctor hV.fromSpec).obj
      ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (siteGradedPiece E.val n)))
    ((presheafRestrict hV.fromSpec).map
      (PresheafOfModules.sheafifyUnit (𝟙 X.ringCatSheaf.obj) (siteGradedPiece E.val n)))
    (isLocallyInjective_presheafRestrict_map hV.fromSpec
      (PresheafOfModules.sheafifyUnit (𝟙 X.ringCatSheaf.obj) (siteGradedPiece E.val n)))
    (isLocallySurjective_presheafRestrict_map hV.fromSpec
      (PresheafOfModules.sheafifyUnit (𝟙 X.ringCatSheaf.obj) (siteGradedPiece E.val n)))
    (op ⊤)).1 (injective_sheafifyUnit_presheafRestrict E hV n)

/-- **The sheafification unit of the sectionwise degree-`n` symmetric power is bijective on the
sections over an affine open.** -/
theorem bijective_sheafifyUnit_image_top [E.IsQuasicoherent] (W : X.Opens)
    (hW : hV.fromSpec ''ᵁ (⊤ : (Spec Γ(X, V)).Opens) = W) :
    Function.Bijective fun x => PresheafOfModules.Hom.app
      (PresheafOfModules.sheafifyUnit (𝟙 X.ringCatSheaf.obj) (siteGradedPiece E.val n))
      (op W) x :=
  ⟨injective_sheafifyUnit_image_top E hV n W hW,
    surjective_sheafifyUnit_image_top E hV n W hW⟩

/-! ### The identification of the sections -/

/-- The sheafification unit at an open `V`, as an additive map
`Sym^n_{Γ(X, V)}(Γ(E, V)) →+ Γ(Sym^n(E), V)`. No affineness is needed to state it. -/
def pieceSectionsAddHom :
    gradedPiece (R := Γ(X, V)) Γ(E, V) n →+
      Γ((Scheme.Modules.symmetricAlgebra X E).piece n, V) :=
  (PresheafOfModules.Hom.app
    (PresheafOfModules.sheafifyUnit (𝟙 X.ringCatSheaf.obj) (siteGradedPiece E.val n))
      (op V)).hom.toAddMonoidHom

/-- **`Γ(Sym^n(E), V)` is `Sym^n_{Γ(X, V)}(Γ(E, V))` for `V` affine and `E` quasi-coherent**, by
the sheafification unit. -/
def pieceSectionsEquiv [E.IsQuasicoherent] :
    gradedPiece (R := Γ(X, V)) Γ(E, V) n ≃+
      Γ((Scheme.Modules.symmetricAlgebra X E).piece n, V) :=
  AddEquiv.ofBijective (pieceSectionsAddHom E n)
    (bijective_sheafifyUnit_image_top E hV n V (hV.fromSpec_image_top))

/-- **The identification is the sheafification unit.** This is the property that characterizes
`Stacks.SymGraded.AffinePieces.pieceSectionsEquiv`: it is not some isomorphism of the two sides
but the canonical map between them. -/
@[simp]
theorem pieceSectionsEquiv_apply [E.IsQuasicoherent]
    (x : gradedPiece (R := Γ(X, V)) Γ(E, V) n) :
    pieceSectionsEquiv E hV n x =
      PresheafOfModules.Hom.app
        (PresheafOfModules.sheafifyUnit (𝟙 X.ringCatSheaf.obj) (siteGradedPiece E.val n))
        (op V) x := rfl

end Stacks.SymGraded.AffinePieces

end
