module

public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupDeRhamTriangleInputs
public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupFormsShortExact

/-!
# The blowup square of de Rham complexes is short exact

Let `f : X ⟶ S` be smooth and let `i : Z ⟶ X` be a closed immersion with `Z` smooth over `S`;
write `b : X' ⟶ X` for the blowing up along `Z`, `j : E ⟶ X'` for its exceptional divisor and
`p : E ⟶ Z` for the projection onto the centre. The canonical maps of Section 07HX form a
commutative square of complexes of `f^{-1}𝒪_S`-modules
(`Stacks.DeRham.BlowupTriangle.blowupShortComplex`), and this file proves that

`0 ⟶ Ω^•_{X/S} ⟶ b_*Ω^•_{X'/S} ⊕ i_*Ω^•_{Z/S} ⟶ b_*j_*Ω^•_{E/S} ⟶ 0`

is short exact, for a centre of any codimension. This is the input of [Stacks, Tag 0FUV] which,
in the source, is supplied by clauses (1) and (2) of [Stacks, Tag 0FUU].

In degree `a ≥ 0` the four maps are, as arrows, the restrictions of coefficients to the base of
the maps of sheaves of `𝒪`-modules of `Stacks.DeRham.shortExact_blowupFormsSquare`, which gives
the short exactness of the corresponding sequence of `𝒪_X`-modules; restricting the coefficients
is exact. In negative degrees all terms vanish.

## Main results

* `Stacks.DeRham.BlowupTriangle.shortExact_blowupShortComplex`: the sequence above is short
  exact.

## Implementation notes

The identification of the components with maps of `𝒪`-modules is made as equalities in the arrow
category, checked on sections; the categories of modules involved are spelled `Modules` and
`ModuleSheaves`, which agree only at default transparency, and stating the identifications for
arrows with the categories fixed by type ascriptions keeps the kernel's checks cheap. Short
exactness of the sequence of a commutative square depends on the square only through its four
arrows (`Stacks.DeRham.BlowupTriangle.shortExact_shortComplex_congr`).

## References

* [Stacks Project, Tag 0FUV](https://stacks.math.columbia.edu/tag/0FUV)
* [Stacks Project, Tag 0FUU](https://stacks.math.columbia.edu/tag/0FUU)
* [Stacks Project, Section 07HX](https://stacks.math.columbia.edu/tag/07HX)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction Stacks.DeRhamDirectImage Stacks.DeRhamSmooth

universe u

attribute [-instance] CategoryTheory.catToReflQuiver

namespace Stacks.DeRham.BlowupTriangle

variable {S : Scheme.{u}}

section Generalities

variable {Y Y' : Scheme.{u}}

/-- Pushing forward along the coefficient-space morphism of `g` a module with its coefficients
restricted to the base is restricting the coefficients of its direct image along `g`. -/
lemma modulePushforward_relativeBase_obj (g : Y' ⟶ Y) (s : Y ⟶ S) (N : Y'.Modules) :
    (modulePushforward (relativeBase g s)).obj
        ((modulePushforward (toInverseImageBase (g ≫ s))).obj N) =
      (modulePushforward (toInverseImageBase s)).obj
        ((Scheme.Modules.pushforward g).obj N) :=
  (modulePushforward_comp_obj _ _ _).trans
    ((congrArg (fun h => (modulePushforward h).obj N)
      (Stacks.DeRhamPullback.toInverseImageBase_relativeBase g s)).trans
      (modulePushforward_comp_obj _ _ _).symm)

/-- A term of the direct image of the extended de Rham complex is the restriction to the base of
the direct image of the sheaf of forms. -/
lemma pushforward_deRhamCochainComplex_X_eq (g : Y' ⟶ Y) (s : Y ⟶ S) (k : ℕ) :
    (((modulePushforward (relativeBase g s)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (deRhamCochainComplex (g ≫ s))).X k =
      (modulePushforward (toInverseImageBase s)).obj
        ((Scheme.Modules.pushforward g).obj (Scheme.Hom.relativeDifferentialForms (g ≫ s) k)) :=
  (congrArg (modulePushforward (relativeBase g s)).obj
    (deRhamCochainComplex_X_eq (g ≫ s) k)).trans (modulePushforward_relativeBase_obj g s _)

/-- The direct images of the forms of a scheme along the two sides of a commutative square
agree. -/
lemma pushforward_pushforward_relativeDifferentialForms_eq {E W W' X : Scheme.{u}}
    {g₁ : E ⟶ W} {h₁ : W ⟶ X} {g₂ : E ⟶ W'} {h₂ : W' ⟶ X} (hw : g₁ ≫ h₁ = g₂ ≫ h₂)
    {π₁ π₂ : E ⟶ S} (hπ : π₁ = π₂) (k : ℤ) :
    (Scheme.Modules.pushforward h₁).obj ((Scheme.Modules.pushforward g₁).obj
        (Scheme.Hom.relativeDifferentialForms π₁ k)) =
      (Scheme.Modules.pushforward h₂).obj ((Scheme.Modules.pushforward g₂).obj
        (Scheme.Hom.relativeDifferentialForms π₂ k)) := by
  subst hπ
  show (Scheme.Modules.pushforward (g₁ ≫ h₁)).obj _ =
    (Scheme.Modules.pushforward (g₂ ≫ h₂)).obj _
  rw [hw]

/-- Restricting the coefficients to the base is faithful. -/
lemma modulePushforward_toInverseImageBase_map_injective (s : Y ⟶ S) {M N : Y.Modules}
    {φ ψ : M ⟶ N}
    (h : (modulePushforward (toInverseImageBase s)).map φ =
      (modulePushforward (toInverseImageBase s)).map ψ) : φ = ψ := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
    ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
  exact congrArg (fun χ => χ.val.app U x) h

/-- **Short exactness of the sequence of a commutative square only depends on its four maps as
arrows**, that is, up to equalities of the corners. -/
lemma shortExact_shortComplex_congr {C : Type*} [Category C] [Abelian C]
    {A B D E A' B' D' E' : C} {t : A ⟶ B} {l : A ⟶ D} {r : B ⟶ E} {b : D ⟶ E}
    {t' : A' ⟶ B'} {l' : A' ⟶ D'} {r' : B' ⟶ E'} {b' : D' ⟶ E'}
    (ht : Arrow.mk t = Arrow.mk t') (hl : Arrow.mk l = Arrow.mk l')
    (hr : Arrow.mk r = Arrow.mk r') (hb : Arrow.mk b = Arrow.mk b')
    (w : t ≫ r = l ≫ b) (w' : t' ≫ r' = l' ≫ b')
    (h : (CommSq.mk w').shortComplex.ShortExact) : (CommSq.mk w).shortComplex.ShortExact := by
  obtain rfl : A = A' := congrArg Arrow.left ht
  obtain rfl : B = B' := congrArg Arrow.right ht
  obtain rfl : D = D' := congrArg Arrow.right hl
  obtain rfl : E = E' := congrArg Arrow.right hr
  obtain rfl := Arrow.mk_inj _ _ |>.1 ht
  obtain rfl := Arrow.mk_inj _ _ |>.1 hl
  obtain rfl := Arrow.mk_inj _ _ |>.1 hr
  obtain rfl := Arrow.mk_inj _ _ |>.1 hb
  exact h

/-- `shortExact_shortComplex_congr`, for the commutativity of the square. -/
lemma comm_congr {C : Type*} [Category C]
    {A B D E A' B' D' E' : C} {t : A ⟶ B} {l : A ⟶ D} {r : B ⟶ E} {b : D ⟶ E}
    {t' : A' ⟶ B'} {l' : A' ⟶ D'} {r' : B' ⟶ E'} {b' : D' ⟶ E'}
    (ht : Arrow.mk t = Arrow.mk t') (hl : Arrow.mk l = Arrow.mk l')
    (hr : Arrow.mk r = Arrow.mk r') (hb : Arrow.mk b = Arrow.mk b')
    (w : t ≫ r = l ≫ b) : t' ≫ r' = l' ≫ b' := by
  obtain rfl : A = A' := congrArg Arrow.left ht
  obtain rfl : B = B' := congrArg Arrow.right ht
  obtain rfl : D = D' := congrArg Arrow.right hl
  obtain rfl : E = E' := congrArg Arrow.right hr
  obtain rfl := Arrow.mk_inj _ _ |>.1 ht
  obtain rfl := Arrow.mk_inj _ _ |>.1 hl
  obtain rfl := Arrow.mk_inj _ _ |>.1 hr
  obtain rfl := Arrow.mk_inj _ _ |>.1 hb
  exact w

end Generalities

/-! ### The blowup square, degreewise -/

section Square

variable {X Z : Scheme.{u}} (f : X ⟶ S) (i : Z ⟶ X) [IsClosedImmersion i]

/-- The direct images `b_*j_*Ω^k_{E/S}` and `i_*p_*Ω^k_{E/S}` of the forms of the exceptional
divisor agree. -/
lemma blowupExceptionalForms_eq (k : ℤ) :
    (Scheme.Modules.pushforward (blowupMap i)).obj
        ((Scheme.Modules.pushforward (exceptionalInclusion i)).obj
          (Scheme.Hom.relativeDifferentialForms (exceptionalInclusion i ≫ blowupMap i ≫ f) k)) =
      (Scheme.Modules.pushforward i).obj
        ((Scheme.Modules.pushforward (exceptionalProjection i)).obj
          (Scheme.Hom.relativeDifferentialForms (exceptionalStructure f i) k)) :=
  pushforward_pushforward_relativeDifferentialForms_eq (exceptionalInclusion_comp_blowupMap i)
    (exceptionalInclusion_comp f i) k

/-- The map `b_*Ω^k_{X'/S} ⟶ b_*j_*Ω^k_{E/S} = i_*p_*Ω^k_{E/S}` of sheaves of `𝒪_X`-modules:
the direct image along `b` of the comparison map on direct images of forms along `j`. -/
def blowupFormsSquareRight (k : ℤ) :
    (Scheme.Modules.pushforward (blowupMap i)).obj
        (Scheme.Hom.relativeDifferentialForms (blowupMap i ≫ f) k) ⟶
      (Scheme.Modules.pushforward i).obj ((Scheme.Modules.pushforward (exceptionalProjection i)).obj
        (Scheme.Hom.relativeDifferentialForms (exceptionalStructure f i) k)) :=
  (Scheme.Modules.pushforward (blowupMap i)).map
      (Scheme.Hom.formsDirectImageComparison (exceptionalInclusion i) (blowupMap i ≫ f) k) ≫
    eqToHom (blowupExceptionalForms_eq f i k)

/-- The term of `j_*Ω^•_{E/S}` in degree `k ≥ 0` is the restriction to the base of
`j_*Ω^k_{E/S}`. -/
lemma inclusionPushforward_X_eq (k : ℕ) :
    (((modulePushforward (coefficientInclusion f i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (deRhamCochainComplex (exceptionalStructure f i))).X k =
      (modulePushforward (toInverseImageBase (blowupMap i ≫ f))).obj
        ((Scheme.Modules.pushforward (exceptionalInclusion i)).obj
          (Scheme.Hom.relativeDifferentialForms (exceptionalInclusion i ≫ blowupMap i ≫ f) k)) :=
  (congrArg (modulePushforward (coefficientInclusion f i)).obj
    (deRhamCochainComplex_X_eq (exceptionalStructure f i) k)).trans
    ((modulePushforward_comp_obj _ _ _).trans
      ((congrArg (fun g => (modulePushforward g).obj
        (Scheme.Hom.relativeDifferentialForms (exceptionalStructure f i) k))
        (toInverseImageBase_comp_coefficientInclusion f i)).trans
        ((modulePushforward_comp_obj _ _ _).symm.trans
          (congrArg (fun π => (RingedSpaceModuleAdjunction.modulePushforward
            (toInverseImageBase (blowupMap i ≫ f))).obj
              ((Scheme.Modules.pushforward (exceptionalInclusion i)).obj
                (Scheme.Hom.relativeDifferentialForms π k)))
            (exceptionalInclusion_comp f i).symm))))

/-- The term of `b_*j_*Ω^•_{E/S}` in degree `k ≥ 0` is the restriction to the base of
`i_*p_*Ω^k_{E/S}`. -/
lemma exceptionalPushforward_X_eq (k : ℕ) :
    (((modulePushforward (coefficientBlowup f i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
      (((modulePushforward (coefficientInclusion f i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (deRhamCochainComplex (exceptionalStructure f i)))).X k =
      (modulePushforward (toInverseImageBase f)).obj
        ((Scheme.Modules.pushforward i).obj
          ((Scheme.Modules.pushforward (exceptionalProjection i)).obj
          (Scheme.Hom.relativeDifferentialForms (exceptionalStructure f i) k))) :=
  (congrArg (modulePushforward (coefficientBlowup f i)).obj
    (inclusionPushforward_X_eq f i k)).trans
    ((modulePushforward_relativeBase_obj (blowupMap i) f _).trans
      (congrArg (modulePushforward (toInverseImageBase f)).obj
        (blowupExceptionalForms_eq f i k)))

/-- Comparing a value with the comparison map on direct images of forms, on sections, reduces to
comparing it with the corresponding component of the graded homomorphism of Section 07HX. -/
private lemma heq_val_app_formsDirectImageComparison {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (s : Y ⟶ S) (k : ℕ) (U : (Y.Opens)ᵒᵖ) (x' : ((Scheme.Hom.deRhamComplex s).X k).val.obj U)
    {α : Type u} {a : α}
    (h : HEq a (((Scheme.Hom.deRhamFormsPushforwardHom g s (g ≫ s) (𝟙 S)
      (Category.comp_id _).symm).app k).val.app U x')) :
    HEq a ((Scheme.Hom.formsDirectImageComparison g s k).val.app U x') :=
  h.trans (heq_of_eq
    (congrArg (fun φ => φ.val.app U x') (formsDirectImageComparison_eq g s k)).symm)

/-- The canonical map of de Rham complexes in degree `k ≥ 0` is the restriction to the base of the
comparison map on direct images of forms. -/
lemma arrow_mk_chain_f {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) (s : Y ⟶ S) (k : ℕ) :
    Arrow.mk (show (show ModuleSheaves (inverseImageBase s) from (deRhamCochainComplex s).X k) ⟶
        (((modulePushforward (relativeBase g s)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (deRhamCochainComplex (g ≫ s))).X k from (chain g s).f k) =
      Arrow.mk ((modulePushforward (toInverseImageBase s)).map
        (Scheme.Hom.formsDirectImageComparison g s k)) := by
  refine arrow_mk_eq_of_val_app_heq (deRhamCochainComplex_X_eq s k)
    (pushforward_deRhamCochainComplex_X_eq g s k) ((chain g s).f k)
    ((modulePushforward (toInverseImageBase s)).map
      (Scheme.Hom.formsDirectImageComparison g s k)) (fun U x x' hx => ?_)
  exact heq_val_app_formsDirectImageComparison g s k U x' (chain_f_apply_heq g s k U x x' hx)

/-- The inverse of `exceptionalSquareIso` is the identity on sections, up to the transport. -/
lemma exceptionalSquareIso_inv_f_apply_heq
    (L : CochainComplex (ModuleSheaves (inverseImageBase (exceptionalStructure f i))) ℤ) (n : ℤ)
    (U : (X.Opens)ᵒᵖ)
    (z : ((((modulePushforward (coefficientCentre f i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
      (((modulePushforward (coefficientProjection f i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L)).X n).val.obj U) :
    HEq (((exceptionalSquareIso f i L).inv.f n).val.app U z) z :=
  (exceptionalSquareIso_hom_f_apply_heq f i L n U _).symm.trans (heq_of_eq (congrArg
    (fun φ => φ.val.app U z)
    (HomologicalComplex.congr_hom (exceptionalSquareIso f i L).inv_hom_id n)))

/-- The term of `b_*j_*Ω^•_{E/S}` in degree `k ≥ 0` is the restriction to the base of
`b_*j_*Ω^k_{E/S}`. -/
lemma exceptionalPushforward_X_eq' (k : ℕ) :
    (((modulePushforward (coefficientBlowup f i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
      (((modulePushforward (coefficientInclusion f i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (deRhamCochainComplex (exceptionalStructure f i)))).X k =
      (modulePushforward (toInverseImageBase f)).obj
        ((Scheme.Modules.pushforward (blowupMap i)).obj
          ((Scheme.Modules.pushforward (exceptionalInclusion i)).obj
            (Scheme.Hom.relativeDifferentialForms (exceptionalInclusion i ≫ blowupMap i ≫ f) k))) :=
  (congrArg (modulePushforward (coefficientBlowup f i)).obj
    (inclusionPushforward_X_eq f i k)).trans (modulePushforward_relativeBase_obj (blowupMap i) f _)

/-- `b_*` of the canonical map `Ω^•_{X'/S} ⟶ j_*Ω^•_{E/S}` in degree `k ≥ 0` is the restriction to
the base of `b_*` of the comparison map on direct images of forms along `j`. -/
lemma arrow_mk_pushforward_inclusionChain_f' (k : ℕ) :
    Arrow.mk (show (show ModuleSheaves (inverseImageBase f) from
        (((modulePushforward (coefficientBlowup f i)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (deRhamCochainComplex (blowupMap i ≫ f))).X k) ⟶
        (((modulePushforward (coefficientBlowup f i)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (((modulePushforward (coefficientInclusion f i)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (deRhamCochainComplex (exceptionalStructure f i)))).X k from
        (((modulePushforward (coefficientBlowup f i)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (inclusionChain f i)).f k) =
      Arrow.mk ((modulePushforward (toInverseImageBase f)).map
        ((Scheme.Modules.pushforward (blowupMap i)).map
          (Scheme.Hom.formsDirectImageComparison (exceptionalInclusion i) (blowupMap i ≫ f)
            k))) := by
  refine arrow_mk_eq_of_val_app_heq (pushforward_deRhamCochainComplex_X_eq (blowupMap i) f k)
    (exceptionalPushforward_X_eq' f i k) _
    ((modulePushforward (toInverseImageBase f)).map
      ((Scheme.Modules.pushforward (blowupMap i)).map
        (Scheme.Hom.formsDirectImageComparison (exceptionalInclusion i) (blowupMap i ≫ f) k)))
    (fun U x x' hx => ?_)
  exact heq_val_app_formsDirectImageComparison (exceptionalInclusion i) (blowupMap i ≫ f) k _ x'
    (inclusionChain_f_apply_heq f i k _ x x' hx)

/-- Composing with an `eqToHom` does not change a morphism as an arrow. -/
lemma arrow_mk_comp_eqToHom {C : Type*} [Category C] {A B B' : C} (φ : A ⟶ B) (h : B = B') :
    Arrow.mk (φ ≫ eqToHom h) = Arrow.mk φ := by
  subst h
  simp

/-- `b_*` of the canonical map `Ω^•_{X'/S} ⟶ j_*Ω^•_{E/S}` in degree `k ≥ 0` is the restriction to
the base of `blowupFormsSquareRight`. -/
lemma arrow_mk_pushforward_inclusionChain_f (k : ℕ) :
    Arrow.mk (show (show ModuleSheaves (inverseImageBase f) from
        (((modulePushforward (coefficientBlowup f i)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (deRhamCochainComplex (blowupMap i ≫ f))).X k) ⟶
        (((modulePushforward (coefficientBlowup f i)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (((modulePushforward (coefficientInclusion f i)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (deRhamCochainComplex (exceptionalStructure f i)))).X k from
        (((modulePushforward (coefficientBlowup f i)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (inclusionChain f i)).f k) =
      Arrow.mk ((modulePushforward (toInverseImageBase f)).map
        (blowupFormsSquareRight f i k)) :=
  (arrow_mk_pushforward_inclusionChain_f' f i k).trans (congrArg
    (fun a : Arrow X.Modules => Arrow.mk
      ((modulePushforward (toInverseImageBase f)).map a.hom))
    (arrow_mk_comp_eqToHom _ (blowupExceptionalForms_eq f i k))).symm

/-- The map `i_*Ω^•_{Z/S} ⟶ b_*j_*Ω^•_{E/S}` in degree `k ≥ 0` is the restriction to the base of
`i_*` of the comparison map on direct images of forms along `p`. -/
lemma arrow_mk_centreToExceptionalChain_f (k : ℕ) :
    Arrow.mk (show (show ModuleSheaves (inverseImageBase f) from
        (((modulePushforward (coefficientCentre f i)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (deRhamCochainComplex (i ≫ f))).X k) ⟶
        (((modulePushforward (coefficientBlowup f i)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (((modulePushforward (coefficientInclusion f i)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (deRhamCochainComplex (exceptionalStructure f i)))).X k from
        (centreToExceptionalChain f i).f k) =
      Arrow.mk ((modulePushforward (toInverseImageBase f)).map
        ((Scheme.Modules.pushforward i).map
          (Scheme.Hom.formsDirectImageComparison (exceptionalProjection i) (i ≫ f) k))) := by
  refine arrow_mk_eq_of_val_app_heq (pushforward_deRhamCochainComplex_X_eq i f k)
    (exceptionalPushforward_X_eq f i k) _
    ((modulePushforward (toInverseImageBase f)).map
      ((Scheme.Modules.pushforward i).map
        (Scheme.Hom.formsDirectImageComparison (exceptionalProjection i) (i ≫ f) k)))
    (fun U x x' hx => ?_)
  unfold centreToExceptionalChain
  refine HEq.trans (heq_of_eq (comp_f_val_app _ _ _ _ _)) ?_
  refine (exceptionalSquareIso_inv_f_apply_heq f i _ _ _ _).trans ?_
  exact heq_val_app_formsDirectImageComparison (exceptionalProjection i) (i ≫ f) k _ x'
    (chain_f_apply_heq (exceptionalProjection i) (i ≫ f) k _ x x' hx)

end Square

/-! ### Short exactness -/

variable {X Z : Scheme.{u}} (f : X ⟶ S) (i : Z ⟶ X) [IsClosedImmersion i]

/-- Restricting the coefficients to the base is exact. -/
lemma preservesFiniteColimits_modulePushforward_toInverseImageBase :
    PreservesFiniteColimits
      (modulePushforward (toInverseImageBase f)) :=
  Stacks.ClosedImmersion.preservesFiniteColimits_modulePushforward _
    (isClosedEmbedding_toInverseImageBase_base f)

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose SheafedSpace.sheaf
  AlgebraicGeometry.RingedSpace.inverseImage in
/-- **The blowup square of de Rham complexes is short exact**: for a closed immersion `i : Z ⟶ X`
of schemes smooth over `S`, of any codimension, the sequence
`0 ⟶ Ω^•_{X/S} ⟶ b_*Ω^•_{X'/S} ⊕ i_*Ω^•_{Z/S} ⟶ b_*j_*Ω^•_{E/S} ⟶ 0` of complexes of
`f^{-1}𝒪_S`-modules is short exact. In degree `a ≥ 0` it is the restriction to the base of the
short exact sequence of `Stacks.DeRham.shortExact_blowupFormsSquare`, restriction of
coefficients being exact; in negative degrees it is zero. -/
theorem shortExact_blowupShortComplex [Smooth f] [Smooth (i ≫ f)] :
    (blowupShortComplex f i).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n => ?_
  refine ShortComplex.shortExact_of_iso
    (CommSq.mapShortComplexIso (HomologicalComplex.eval _ (ComplexShape.up ℤ) n)
      (CommSq.mk (C := CochainComplex (ModuleSheaves (inverseImageBase f)) ℤ)
        (chain_comp_inclusionChain f i))).symm ?_
  obtain ⟨k, rfl⟩ | ⟨k, rfl⟩ : (∃ k : ℕ, n = k) ∨ ∃ k : ℕ, n = Int.negSucc k := by
    rcases n with k | k
    · exact Or.inl ⟨k, rfl⟩
    · exact Or.inr ⟨k, rfl⟩
  · have := preservesFiniteColimits_modulePushforward_toInverseImageBase f
    have : PreservesLimitsOfSize.{0, 0}
        (modulePushforward (toInverseImageBase f)) :=
      (modulePullbackPushforwardAdjunction (toInverseImageBase f)).rightAdjoint_preservesLimits
    have : (modulePushforward (toInverseImageBase f)).Additive :=
      Functor.additive_of_preserves_binary_products _
    have ht := arrow_mk_chain_f (blowupMap i) f k
    have hl := arrow_mk_chain_f i f k
    have hr := arrow_mk_pushforward_inclusionChain_f f i k
    have hb := arrow_mk_centreToExceptionalChain_f f i k
    have hw := HomologicalComplex.congr_hom (chain_comp_inclusionChain f i) k
    have w₀ : Scheme.Hom.formsDirectImageComparison (blowupMap i) f k ≫
        blowupFormsSquareRight f i k = Scheme.Hom.formsDirectImageComparison i f k ≫
          (Scheme.Modules.pushforward i).map
            (Scheme.Hom.formsDirectImageComparison (exceptionalProjection i) (i ≫ f) k) := by
      refine modulePushforward_toInverseImageBase_map_injective f ?_
      refine (Functor.map_comp _ _ _).trans (Eq.trans ?_ (Functor.map_comp _ _ _).symm)
      exact comm_congr ht hl hr hb hw
    exact shortExact_shortComplex_congr ht hl hr hb hw
      ((CommSq.mk w₀).map (modulePushforward (toInverseImageBase f))).w
      (CommSq.shortExact_shortComplex_map
        (modulePushforward (toInverseImageBase f)) (CommSq.mk w₀)
        (Stacks.DeRham.shortExact_blowupFormsSquare f i k w₀))
  · have hz {Y : Scheme.{u}} (s : Y ⟶ S) :
        IsZero ((deRhamCochainComplex s).X (Int.negSucc k)) :=
      (deRhamCochainComplex s).isZero_of_isStrictlyGE 0 (Int.negSucc k) (by omega)
    have hB := (modulePushforward (coefficientBlowup f i)).map_isZero (hz (blowupMap i ≫ f))
    have hD := (modulePushforward (coefficientCentre f i)).map_isZero (hz (i ≫ f))
    have hE := (modulePushforward (coefficientBlowup f i)).map_isZero
      ((modulePushforward (coefficientInclusion f i)).map_isZero (hz (exceptionalStructure f i)))
    exact @CommSq.shortExact_shortComplex_of_horiz_isIso _ _ _ _ _ _ _ _ _ _ _ _
      (isIso_of_source_target_iso_zero _ (hz f).isoZero hB.isoZero)
      (isIso_of_source_target_iso_zero _ hD.isoZero hE.isoZero)

end Stacks.DeRham.BlowupTriangle

end
