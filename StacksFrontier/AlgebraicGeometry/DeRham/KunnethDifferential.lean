module

public import StacksFrontier.AlgebraicGeometry.DeRham.DifferentialGradedAlgebra.Basic
public import StacksFrontier.AlgebraicGeometry.DeRham.KunnethWedgeSection

/-!
# The degreewise de Rham Künneth isomorphism is compatible with the differentials

Let `a : X ⟶ S` and `b : Y ⟶ S` be morphisms of schemes and let `W = X ×_S Y`. The degreewise
isomorphism `Tot(Ω^•_{X/S} ⊠ Ω^•_{Y/S})^n ≅ Ω^n_{W/S}` of
`AlgebraicGeometry.Scheme.Hom.deRhamBoxTotalDegreeIso` commutes with the differentials:

`d ≫ iso = iso ≫ d`.

The mathematics is the graded Leibniz rule. On the `(p, q)` summand of the total complex the
comparison is `ω ⊗ η ↦ pr₁^*ω ∧ pr₂^*η`, the differential of the total complex is
`d₁ + (-1)^p d₂` by the sign convention of [Stacks, Tag 012Z], the de Rham differential commutes
with pullback of forms, and
`d (pr₁^*ω ∧ pr₂^*η) = pr₁^*(dω) ∧ pr₂^*η + (-1)^p pr₁^*ω ∧ pr₂^*(dη)`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.deRhamBoxWedgeHom`: the restriction of the degreewise Künneth
  comparison to the `(p, q)` summand of `Tot(Ω^•_{X/S} ⊠ Ω^•_{Y/S})`, typed on the term of the
  double complex.

## Main results

* `AlgebraicGeometry.Scheme.Hom.deRhamBoxWedgeHom_comp_deRhamDiffOpDifferential`: **the graded
  Leibniz rule on the `(p, q)` summand**, as an identity of differential operators.
* `AlgebraicGeometry.Scheme.Hom.deRhamBoxTotal_d_comp_deRhamBoxTotalDegreeIso`: **the degreewise
  de Rham Künneth isomorphism commutes with the differentials.**

## Implementation notes

Two spellings of the same object occur throughout: `(Ω^p_{X/S} ⊠ Ω^q_{Y/S})` as the term
`((Ω^•_{X/S} ⊠ Ω^•_{Y/S}).X p).X q` of the double complex, which is the spelling the total complex
and its differentials are stated in, and as
`AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.boxProductObj`, which is the spelling
the box product of two operators and the extensionality principle for maps out of an external
tensor product are stated in. They are definitionally equal, but the equality is expensive for
the kernel to recheck, and it must be rechecked at every occurrence inside an instance argument
— in particular inside the scalar multiplication on morphisms, where the additive group of
morphisms depends on the source object. So `deRhamBoxWedgeHom` is declared in the
double-complex spelling, every statement involving `+` or `•` of morphisms is written entirely in
that spelling, and each passage to the `boxProductObj` spelling is isolated in a declaration of
its own. This is why the chain of equalities is split into many small lemmas rather than written
as one tactic block: the budget is per declaration.

For the same reason every step is `Eq.trans` or `congrArg` rather than `rewrite`: a rewrite
across the two spellings cannot build its motive, as recorded in
`StacksFrontier.AlgebraicGeometry.DeRham.KunnethDegreewise`.

## References

* [Stacks Project, Tag 0FMA](https://stacks.math.columbia.edu/tag/0FMA)
* [Stacks Project, Tag 012Z](https://stacks.math.columbia.edu/tag/012Z)
* [Stacks Project, Tag 0FKM](https://stacks.math.columbia.edu/tag/0FKM)
* [Stacks Project, Tag 0FM2](https://stacks.math.columbia.edu/tag/0FM2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.FibreProductAffineChart
open Stacks.Tag01VSPullbackTensor
open scoped TensorProduct

universe u

/-- **The sign `(-1)^p` of [Stacks, Tag 012Z] moves out of a composition.** The action of the
unit group of `ℤ` on the morphisms of a preadditive category is the action of `ℤ` through the
coercion, and composition is `ℤ`-linear in each variable. -/
theorem CategoryTheory.Preadditive.units_neg_one_pow_smul_comp {C : Type*} [Category C]
    [Preadditive C] {F G H : C} (p : ℕ) (M : F ⟶ G) (N : G ⟶ H) :
    (((-1 : ℤˣ) ^ p) • M) ≫ N = ((-1 : ℤ) ^ p) • (M ≫ N) :=
  Eq.trans (congrArg (fun z : ℤ => (z • M) ≫ N)
      (show (((-1 : ℤˣ) ^ p : ℤˣ) : ℤ) = (-1 : ℤ) ^ p by simp))
    (Preadditive.zsmul_comp _ _ _)

namespace AlgebraicGeometry

attribute [local instance] hasColimits_sheafOfModules_toRingCat
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace FiniteOrderDifferentialOperatorCategory

variable {X Y S : Scheme.{u}} {a : X ⟶ S} {b : Y ⟶ S}

/-- **Two finite-order differential operators out of `F ⊠ G` into an arbitrary quasi-coherent
module which agree on the sections attached to pairs of local sections over every affine chart are
equal.** This is
`AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.hom_ext_of_externalTensorSection` with
the target no longer required to be an external tensor product: the argument only uses that the
source is one. -/
theorem hom_ext_of_externalTensorSection_target
    {F : FiniteOrderDifferentialOperatorCategory a}
    {G : FiniteOrderDifferentialOperatorCategory b}
    {Z : FiniteOrderDifferentialOperatorCategory (pullback.fst a b ≫ a)}
    (P Q : boxProductObj F G ⟶ Z)
    (h : ∀ (c : Chart a b) (s : Γ(F.module, c.left)) (t : Γ(G.module, c.right))
      (h₁ : c.ι.opensRange ≤ pullback.fst a b ⁻¹ᵁ c.left)
      (h₂ : c.ι.opensRange ≤ pullback.snd a b ⁻¹ᵁ c.right),
      P.1 (op c.ι.opensRange)
          (externalTensorSection a b F.module G.module s t c.ι.opensRange h₁ h₂) =
        Q.1 (op c.ι.opensRange)
          (externalTensorSection a b F.module G.module s t c.ι.opensRange h₁ h₂)) :
    P = Q := by
  obtain ⟨k, hk⟩ := P.2
  obtain ⟨l, hl⟩ := Q.2
  refine Subtype.ext (globalDiffOp_ext_of_chart_sections_overBase a b (max k l) P.1 Q.1
    (isGlobalDiffOpOfOrder_of_le _ (Nat.le_max_left k l) _ hk)
    (isGlobalDiffOpOfOrder_of_le _ (Nat.le_max_right k l) _ hl) fun c x ↦ ?_)
  have h₁ : c.ι.opensRange ≤ pullback.fst a b ⁻¹ᵁ c.left := c.opensRange_ι.le.trans inf_le_left
  have h₂ : c.ι.opensRange ≤ pullback.snd a b ⁻¹ᵁ c.right := c.opensRange_ι.le.trans inf_le_right
  exact c.ext_of_externalTensorSection_of_eq F.module G.module
    (by rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_comp_of_isIso]) h₁ h₂
    (P.1 (op c.ι.opensRange)) (Q.1 (op c.ι.opensRange)) (fun s t ↦ h c s t h₁ h₂) x

end FiniteOrderDifferentialOperatorCategory

namespace Scheme.Hom

open FiniteOrderDifferentialOperatorCategory

/-! ### Reading the de Rham differential of a scheme morphism in three spellings -/

variable {Z T : Scheme.{u}} (c : Z ⟶ T)

/-- The de Rham differential read as a finite-order differential operator acts on local sections
as the differential of the relative de Rham complex. -/
theorem deRhamDiffOpDifferential_apply (p : ℕ) (U : (Z.Opens)ᵒᵖ)
    (s : (relativeDifferentialForms c (p : ℤ)).val.obj U) :
    (deRhamDiffOpDifferential c p).1 U s = ((deRhamComplex c).d p (p + 1)).val.app U s :=
  (congrArg (fun z : (deRhamComplex c).X p ⟶ (deRhamComplex c).X (p + 1) => z.val.app U s)
    (deRhamComplex_d c p)).symm

/-- The arrow of the de Rham complex of finite-order differential operators acts on local
sections as the differential of the relative de Rham complex. -/
theorem deRhamDiffOpComplex_d_apply (p : ℕ) (U : (Z.Opens)ᵒᵖ)
    (s : (relativeDifferentialForms c (p : ℤ)).val.obj U) :
    ((deRhamDiffOpComplex c).d p (p + 1)).1 U s =
      ((deRhamComplex c).d p (p + 1)).val.app U s :=
  (congrArg (fun z : deRhamDiffOpTerm c p ⟶ deRhamDiffOpTerm c (p + 1) => z.1 U s)
    (deRhamDiffOpComplex_d c p)).trans (deRhamDiffOpDifferential_apply c p U s)

/-- Transporting a differential form along an equality of degrees is the reindexing isomorphism of
the relative de Rham complex. -/
theorem eqToHom_exteriorPower_val_app {m m' : ℕ} (h : m = m') (U : (Z.Opens)ᵒᵖ)
    (x : (relativeDifferentialForms c (m : ℤ)).val.obj U) :
    (eqToHom (congrArg (fun k : ℕ => (deRhamAlgebras c).exteriorPower k) h)).val.app U x =
      ((deRhamComplex c).XIsoOfEq h).hom.val.app U x := by
  subst h; rfl

/-- Transporting a differential form along the reflexivity of its degree does nothing. -/
theorem eqToHom_exteriorPower_val_app_rfl (m : ℕ) (U : (Z.Opens)ᵒᵖ)
    (x : (relativeDifferentialForms c (m : ℤ)).val.obj U) :
    (eqToHom (congrArg (fun k : ℕ => (deRhamAlgebras c).exteriorPower k)
      (rfl : m = m))).val.app U x = x := rfl

/-- **The graded Leibniz rule for the relative de Rham complex of a morphism of schemes**:
`d (ω ∧ η) = dω ∧ η + (-1)^p ω ∧ dη` on arbitrary local sections of `Ω^p` and `Ω^q`. This is
[Stacks, Tag 0FM2] read at the chosen de Rham differential of [Stacks, Tag 0FKM]. -/
theorem deRhamComplex_d_formProduct (p q : ℕ) (U : (Z.Opens)ᵒᵖ)
    (ω : (relativeDifferentialForms c (p : ℤ)).val.obj U)
    (η : (relativeDifferentialForms c (q : ℤ)).val.obj U) :
    ((deRhamComplex c).d (p + q) (p + q + 1)).val.app U
        (SheafOfModules.formProduct (deRhamAlgebras c) p q U ω η) =
      ((deRhamComplex c).XIsoOfEq (show p + 1 + q = p + q + 1 by omega)).hom.val.app U
          (SheafOfModules.formProduct (deRhamAlgebras c) (p + 1) q U
            (((deRhamComplex c).d p (p + 1)).val.app U ω) η) +
        (-1 : ℤ) ^ p •
          ((deRhamComplex c).XIsoOfEq (show p + (q + 1) = p + q + 1 by omega)).hom.val.app U
            (SheafOfModules.formProduct (deRhamAlgebras c) p (q + 1) U ω
              (((deRhamComplex c).d q (q + 1)).val.app U η)) :=
  SheafOfModules.d_formProduct (deRhamAlgebras c)
    (SheafOfModules.deRhamDifferential (deRhamAlgebras c)) p q U ω η

/-! ### The Künneth comparison on one summand -/

variable {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)

/-- The index `(p, q)` of the antidiagonal of `m`, as an element of the index type of the
degree-`m` term of a total complex. -/
abbrev deRhamBoxIndexMk (p q m : ℕ) (h : p + q = m) : deRhamBoxIndex m := ⟨(p, q), h⟩

/-- **The restriction of the degreewise de Rham Künneth comparison to the `(p, q)` summand**: the
comparison of [Stacks, Tag 01CI] in each factor followed by the wedge-product component
`ω ⊗ η ↦ pr₁^*ω ∧ pr₂^*η`, read as a differential operator of order zero out of the term of the
double complex in degree `(p, q)`. -/
noncomputable def deRhamBoxWedgeHom (m p q : ℕ) (h : p + q = m) :
    ((deRhamBoxDoubleComplex a b).X p).X q ⟶
      (deRhamDiffOpComplex (pullback.fst a b ≫ a)).X m :=
  homOrderZeroAddMonoidHom _ _
    ((deRhamBoxSummandIso a b m (deRhamBoxIndexMk p q m h)).inv ≫
      SheafOfModules.prodWedgeHomOfEq (deRhamBoxAlgebrasLeft a b) (deRhamBoxAlgebrasRight a b)
        (deRhamAlgebras (pullback.fst a b ≫ a)) (deRhamBoxLeftMap a b) (deRhamBoxRightMap a b)
        p q m h)

/-- The degreewise Künneth comparison restricted to the `(p, q)` summand of the total complex is
`AlgebraicGeometry.Scheme.Hom.deRhamBoxWedgeHom`. -/
theorem ιTotal_comp_deRhamBoxTotalDegreeIso_wedgeHom (m p q : ℕ) (h : p + q = m) :
    (deRhamBoxDoubleComplex a b).ιTotal (ComplexShape.up ℕ) p q m h ≫
        (deRhamBoxTotalDegreeIso a b m).hom = deRhamBoxWedgeHom a b m p q h :=
  ιTotal_comp_deRhamBoxTotalDegreeIso_wedge a b m (deRhamBoxIndexMk p q m h)

/-- **`AlgebraicGeometry.Scheme.Hom.deRhamBoxWedgeHom` on a pure external tensor section is the
wedge product of the two pullbacks**, with its degree transported along `p + q = m`. -/
theorem deRhamBoxWedgeHom_externalTensorSection (m p q : ℕ) (h : p + q = m)
    {U : X.Opens} {V : Y.Opens} (ω : Γ(relativeDifferentialForms a (p : ℤ), U))
    (η : Γ(relativeDifferentialForms b (q : ℤ), V)) (W : (pullback a b).Opens)
    (hW₁ : W ≤ pullback.fst a b ⁻¹ᵁ U) (hW₂ : W ≤ pullback.snd a b ⁻¹ᵁ V) :
    (deRhamBoxWedgeHom a b m p q h).1 (op W)
        (externalTensorSection a b (relativeDifferentialForms a (p : ℤ))
          (relativeDifferentialForms b (q : ℤ)) ω η W hW₁ hW₂) =
      (eqToHom (congrArg (fun k : ℕ =>
          (deRhamAlgebras (pullback.fst a b ≫ a)).exteriorPower k) h)).val.app (op W)
        (SheafOfModules.formProduct (deRhamAlgebras (pullback.fst a b ≫ a)) p q (op W)
          ((relativeDifferentialForms (pullback.fst a b ≫ a) (p : ℤ)).presheaf.map
            (homOfLE hW₁).op (deRhamBoxLeftPullback a b (p : ℤ) U ω))
          ((relativeDifferentialForms (pullback.fst a b ≫ a) (q : ℤ)).presheaf.map
            (homOfLE hW₂).op (deRhamBoxRightPullback a b (q : ℤ) V η))) :=
  congrArg ((eqToHom (congrArg (fun k : ℕ =>
      (deRhamAlgebras (pullback.fst a b ≫ a)).exteriorPower k) h)).val.app (op W))
    (prodWedgeHom_deRhamBoxSummandIso_inv_externalTensorSection a b m
      (deRhamBoxIndexMk p q m h) ω η W hW₁ hW₂)

/-! ### The de Rham differential of a pulled-back form, restricted to an open of the product -/

/-- **The pullback along `pr₁` of the differential of a form, restricted to an open of the fibre
product, is the differential of the restricted pullback.** -/
theorem deRhamComplex_d_deRhamBoxLeftPullback_restrict (p : ℕ) {U : X.Opens}
    (ω : Γ(relativeDifferentialForms a (p : ℤ), U)) (W : (pullback a b).Opens)
    (hW₁ : W ≤ pullback.fst a b ⁻¹ᵁ U) :
    (relativeDifferentialForms (pullback.fst a b ≫ a) ((p : ℤ) + 1)).presheaf.map
        (homOfLE hW₁).op
        (deRhamBoxLeftPullback a b ((p : ℤ) + 1) U
          (((deRhamComplex a).d p (p + 1)).val.app (op U) ω)) =
      ((deRhamComplex (pullback.fst a b ≫ a)).d p (p + 1)).val.app (op W)
        ((relativeDifferentialForms (pullback.fst a b ≫ a) (p : ℤ)).presheaf.map
          (homOfLE hW₁).op (deRhamBoxLeftPullback a b (p : ℤ) U ω)) := by
  refine Eq.trans (congrArg
    ((relativeDifferentialForms (pullback.fst a b ≫ a) ((p : ℤ) + 1)).presheaf.map
      (homOfLE hW₁).op)
    (deRhamComplex_d_relativeDifferentialFormsPullback (pullback.fst a b) a
      (pullback.fst a b ≫ a) (𝟙 S) (Category.comp_id (pullback.fst a b ≫ a)).symm
      p U ω).symm) ?_
  exact (PresheafOfModules.naturality_apply
    ((deRhamComplex (pullback.fst a b ≫ a)).d p (p + 1)).val (homOfLE hW₁).op _).symm

/-- **The pullback along `pr₂` of the differential of a form, restricted to an open of the fibre
product, is the differential of the restricted pullback.** -/
theorem deRhamComplex_d_deRhamBoxRightPullback_restrict (q : ℕ) {V : Y.Opens}
    (η : Γ(relativeDifferentialForms b (q : ℤ), V)) (W : (pullback a b).Opens)
    (hW₂ : W ≤ pullback.snd a b ⁻¹ᵁ V) :
    (relativeDifferentialForms (pullback.fst a b ≫ a) ((q : ℤ) + 1)).presheaf.map
        (homOfLE hW₂).op
        (deRhamBoxRightPullback a b ((q : ℤ) + 1) V
          (((deRhamComplex b).d q (q + 1)).val.app (op V) η)) =
      ((deRhamComplex (pullback.fst a b ≫ a)).d q (q + 1)).val.app (op W)
        ((relativeDifferentialForms (pullback.fst a b ≫ a) (q : ℤ)).presheaf.map
          (homOfLE hW₂).op (deRhamBoxRightPullback a b (q : ℤ) V η)) := by
  refine Eq.trans (congrArg
    ((relativeDifferentialForms (pullback.fst a b ≫ a) ((q : ℤ) + 1)).presheaf.map
      (homOfLE hW₂).op)
    (deRhamComplex_d_relativeDifferentialFormsPullback (pullback.snd a b) b
      (pullback.fst a b ≫ a) (𝟙 S)
      ((IsPullback.of_hasPullback a b).w.symm.trans
        (Category.comp_id (pullback.fst a b ≫ a)).symm) q V η).symm) ?_
  exact (PresheafOfModules.naturality_apply
    ((deRhamComplex (pullback.fst a b ≫ a)).d q (q + 1)).val (homOfLE hW₂).op _).symm

/-! ### The three terms of the Leibniz rule on a pure external tensor section -/

section Leibniz

variable (p q : ℕ) {U : X.Opens} {V : Y.Opens}
  (ω : Γ(relativeDifferentialForms a (p : ℤ), U))
  (η : Γ(relativeDifferentialForms b (q : ℤ), V))
  (W : (pullback a b).Opens) (hW₁ : W ≤ pullback.fst a b ⁻¹ᵁ U)
  (hW₂ : W ≤ pullback.snd a b ⁻¹ᵁ V)

/-- **The left-hand side of the Leibniz rule on a pure external tensor section**: the Künneth
comparison followed by the de Rham differential of the fibre product carries the section attached
to `ω` and `η` to `d (pr₁^*ω ∧ pr₂^*η)`. -/
theorem deRhamBoxWedgeHom_comp_d_apply :
    (deRhamBoxWedgeHom a b (p + q) p q rfl ≫
          (deRhamDiffOpComplex (pullback.fst a b ≫ a)).d (p + q) (p + q + 1)).1 (op W)
        (externalTensorSection a b (relativeDifferentialForms a (p : ℤ))
          (relativeDifferentialForms b (q : ℤ)) ω η W hW₁ hW₂) =
      ((deRhamComplex (pullback.fst a b ≫ a)).d (p + q) (p + q + 1)).val.app (op W)
        (SheafOfModules.formProduct (deRhamAlgebras (pullback.fst a b ≫ a)) p q (op W)
          ((relativeDifferentialForms (pullback.fst a b ≫ a) (p : ℤ)).presheaf.map
            (homOfLE hW₁).op (deRhamBoxLeftPullback a b (p : ℤ) U ω))
          ((relativeDifferentialForms (pullback.fst a b ≫ a) (q : ℤ)).presheaf.map
            (homOfLE hW₂).op (deRhamBoxRightPullback a b (q : ℤ) V η))) := by
  refine Eq.trans (congrArg
    (((deRhamDiffOpComplex (pullback.fst a b ≫ a)).d (p + q) (p + q + 1)).1 (op W))
    ((deRhamBoxWedgeHom_externalTensorSection a b (p + q) p q rfl ω η W hW₁ hW₂).trans
      (eqToHom_exteriorPower_val_app_rfl (pullback.fst a b ≫ a) (p + q) (op W) _))) ?_
  exact deRhamDiffOpComplex_d_apply (pullback.fst a b ≫ a) (p + q) (op W) _

/-- **The first differential of the double complex on a pure external tensor section**: `d ⊠ 1`
carries the section attached to `ω` and `η` to the section attached to `dω` and `η`. -/
theorem d_f_apply_externalTensorSection :
    (((deRhamBoxDoubleComplex a b).d p (p + 1)).f q).1 (op W)
        (externalTensorSection a b (relativeDifferentialForms a (p : ℤ))
          (relativeDifferentialForms b (q : ℤ)) ω η W hW₁ hW₂) =
      externalTensorSection a b (relativeDifferentialForms a ((p + 1 : ℕ) : ℤ))
        (relativeDifferentialForms b (q : ℤ))
        (((deRhamComplex a).d p (p + 1)).val.app (op U) ω) η W hW₁ hW₂ :=
  (congrArg (fun T => T.1 (op W)
      (externalTensorSection a b (relativeDifferentialForms a (p : ℤ))
        (relativeDifferentialForms b (q : ℤ)) ω η W hW₁ hW₂))
    (deRhamBoxDoubleComplex_d_f a b p q)).trans
    ((boxHom_externalTensorSection (deRhamDiffOpDifferential a p)
        (𝟙 (deRhamDiffOpTerm b q)) ω η W hW₁ hW₂).trans
      (congrArg (fun z => externalTensorSection a b
          (relativeDifferentialForms a ((p + 1 : ℕ) : ℤ))
          (relativeDifferentialForms b (q : ℤ)) z η W hW₁ hW₂)
        (deRhamDiffOpDifferential_apply a p (op U) ω)))

/-- **The second differential of the double complex on a pure external tensor section**: `1 ⊠ d`
carries the section attached to `ω` and `η` to the section attached to `ω` and `dη`. -/
theorem X_d_apply_externalTensorSection :
    ((((deRhamBoxDoubleComplex a b).X p).d q (q + 1)).1 (op W)
        (externalTensorSection a b (relativeDifferentialForms a (p : ℤ))
          (relativeDifferentialForms b (q : ℤ)) ω η W hW₁ hW₂)) =
      externalTensorSection a b (relativeDifferentialForms a (p : ℤ))
        (relativeDifferentialForms b ((q + 1 : ℕ) : ℤ)) ω
        (((deRhamComplex b).d q (q + 1)).val.app (op V) η) W hW₁ hW₂ :=
  (congrArg (fun T => T.1 (op W)
      (externalTensorSection a b (relativeDifferentialForms a (p : ℤ))
        (relativeDifferentialForms b (q : ℤ)) ω η W hW₁ hW₂))
    (deRhamBoxDoubleComplex_X_d a b p q)).trans
    ((boxHom_externalTensorSection (𝟙 (deRhamDiffOpTerm a p))
        (deRhamDiffOpDifferential b q) ω η W hW₁ hW₂).trans
      (congrArg (fun z => externalTensorSection a b
          (relativeDifferentialForms a (p : ℤ))
          (relativeDifferentialForms b ((q + 1 : ℕ) : ℤ)) ω z W hW₁ hW₂)
        (deRhamDiffOpDifferential_apply b q (op V) η)))

/-- **The Künneth comparison on the section attached to `dω` and `η`** is `d(pr₁^*ω) ∧ pr₂^*η`,
because the pullback of forms commutes with the de Rham differential. -/
theorem deRhamBoxWedgeHom_externalTensorSection_dLeft :
    (deRhamBoxWedgeHom a b (p + q + 1) (p + 1) q
          (show p + 1 + q = p + q + 1 by omega)).1 (op W)
        (externalTensorSection a b (relativeDifferentialForms a ((p + 1 : ℕ) : ℤ))
          (relativeDifferentialForms b (q : ℤ))
          (((deRhamComplex a).d p (p + 1)).val.app (op U) ω) η W hW₁ hW₂) =
      ((deRhamComplex (pullback.fst a b ≫ a)).XIsoOfEq
          (show p + 1 + q = p + q + 1 by omega)).hom.val.app (op W)
        (SheafOfModules.formProduct (deRhamAlgebras (pullback.fst a b ≫ a)) (p + 1) q (op W)
          (((deRhamComplex (pullback.fst a b ≫ a)).d p (p + 1)).val.app (op W)
            ((relativeDifferentialForms (pullback.fst a b ≫ a) (p : ℤ)).presheaf.map
              (homOfLE hW₁).op (deRhamBoxLeftPullback a b (p : ℤ) U ω)))
          ((relativeDifferentialForms (pullback.fst a b ≫ a) (q : ℤ)).presheaf.map
            (homOfLE hW₂).op (deRhamBoxRightPullback a b (q : ℤ) V η))) := by
  refine Eq.trans (deRhamBoxWedgeHom_externalTensorSection a b (p + q + 1) (p + 1) q
    (show p + 1 + q = p + q + 1 by omega)
    (((deRhamComplex a).d p (p + 1)).val.app (op U) ω) η W hW₁ hW₂) ?_
  refine Eq.trans (congrArg
    (fun z => (eqToHom (congrArg (fun k : ℕ =>
          (deRhamAlgebras (pullback.fst a b ≫ a)).exteriorPower k)
        (show p + 1 + q = p + q + 1 by omega))).val.app (op W)
      (SheafOfModules.formProduct (deRhamAlgebras (pullback.fst a b ≫ a)) (p + 1) q (op W) z
        ((relativeDifferentialForms (pullback.fst a b ≫ a) (q : ℤ)).presheaf.map
          (homOfLE hW₂).op (deRhamBoxRightPullback a b (q : ℤ) V η))))
    (deRhamComplex_d_deRhamBoxLeftPullback_restrict a b p ω W hW₁)) ?_
  exact eqToHom_exteriorPower_val_app (pullback.fst a b ≫ a)
    (show p + 1 + q = p + q + 1 by omega) (op W) _

/-- **The Künneth comparison on the section attached to `ω` and `dη`** is `pr₁^*ω ∧ d(pr₂^*η)`,
because the pullback of forms commutes with the de Rham differential. -/
theorem deRhamBoxWedgeHom_externalTensorSection_dRight :
    (deRhamBoxWedgeHom a b (p + q + 1) p (q + 1)
          (show p + (q + 1) = p + q + 1 by omega)).1 (op W)
        (externalTensorSection a b (relativeDifferentialForms a (p : ℤ))
          (relativeDifferentialForms b ((q + 1 : ℕ) : ℤ)) ω
          (((deRhamComplex b).d q (q + 1)).val.app (op V) η) W hW₁ hW₂) =
      ((deRhamComplex (pullback.fst a b ≫ a)).XIsoOfEq
          (show p + (q + 1) = p + q + 1 by omega)).hom.val.app (op W)
        (SheafOfModules.formProduct (deRhamAlgebras (pullback.fst a b ≫ a)) p (q + 1) (op W)
          ((relativeDifferentialForms (pullback.fst a b ≫ a) (p : ℤ)).presheaf.map
            (homOfLE hW₁).op (deRhamBoxLeftPullback a b (p : ℤ) U ω))
          (((deRhamComplex (pullback.fst a b ≫ a)).d q (q + 1)).val.app (op W)
            ((relativeDifferentialForms (pullback.fst a b ≫ a) (q : ℤ)).presheaf.map
              (homOfLE hW₂).op (deRhamBoxRightPullback a b (q : ℤ) V η)))) := by
  refine Eq.trans (deRhamBoxWedgeHom_externalTensorSection a b (p + q + 1) p (q + 1)
    (show p + (q + 1) = p + q + 1 by omega) ω
    (((deRhamComplex b).d q (q + 1)).val.app (op V) η) W hW₁ hW₂) ?_
  refine Eq.trans (congrArg
    (fun z => (eqToHom (congrArg (fun k : ℕ =>
          (deRhamAlgebras (pullback.fst a b ≫ a)).exteriorPower k)
        (show p + (q + 1) = p + q + 1 by omega))).val.app (op W)
      (SheafOfModules.formProduct (deRhamAlgebras (pullback.fst a b ≫ a)) p (q + 1) (op W)
        ((relativeDifferentialForms (pullback.fst a b ≫ a) (p : ℤ)).presheaf.map
          (homOfLE hW₁).op (deRhamBoxLeftPullback a b (p : ℤ) U ω)) z))
    (deRhamComplex_d_deRhamBoxRightPullback_restrict a b q η W hW₂)) ?_
  exact eqToHom_exteriorPower_val_app (pullback.fst a b ≫ a)
    (show p + (q + 1) = p + q + 1 by omega) (op W) _

/-- **The first term of the Leibniz rule on a pure external tensor section**: the first
differential of the double complex followed by the Künneth comparison carries the section attached
to `ω` and `η` to `d(pr₁^*ω) ∧ pr₂^*η`. -/
theorem d_comp_deRhamBoxWedgeHom_apply :
    (((deRhamBoxDoubleComplex a b).d p (p + 1)).f q ≫
          deRhamBoxWedgeHom a b (p + q + 1) (p + 1) q
            (show p + 1 + q = p + q + 1 by omega)).1 (op W)
        (externalTensorSection a b (relativeDifferentialForms a (p : ℤ))
          (relativeDifferentialForms b (q : ℤ)) ω η W hW₁ hW₂) =
      ((deRhamComplex (pullback.fst a b ≫ a)).XIsoOfEq
          (show p + 1 + q = p + q + 1 by omega)).hom.val.app (op W)
        (SheafOfModules.formProduct (deRhamAlgebras (pullback.fst a b ≫ a)) (p + 1) q (op W)
          (((deRhamComplex (pullback.fst a b ≫ a)).d p (p + 1)).val.app (op W)
            ((relativeDifferentialForms (pullback.fst a b ≫ a) (p : ℤ)).presheaf.map
              (homOfLE hW₁).op (deRhamBoxLeftPullback a b (p : ℤ) U ω)))
          ((relativeDifferentialForms (pullback.fst a b ≫ a) (q : ℤ)).presheaf.map
            (homOfLE hW₂).op (deRhamBoxRightPullback a b (q : ℤ) V η))) :=
  (congrArg ((deRhamBoxWedgeHom a b (p + q + 1) (p + 1) q
        (show p + 1 + q = p + q + 1 by omega)).1 (op W))
    (d_f_apply_externalTensorSection a b p q ω η W hW₁ hW₂)).trans
    (deRhamBoxWedgeHom_externalTensorSection_dLeft a b p q ω η W hW₁ hW₂)

/-- **The second term of the Leibniz rule on a pure external tensor section**: the second
differential of the double complex followed by the Künneth comparison carries the section attached
to `ω` and `η` to `pr₁^*ω ∧ d(pr₂^*η)`. -/
theorem X_d_comp_deRhamBoxWedgeHom_apply :
    ((((deRhamBoxDoubleComplex a b).X p).d q (q + 1) ≫
          deRhamBoxWedgeHom a b (p + q + 1) p (q + 1)
            (show p + (q + 1) = p + q + 1 by omega)).1 (op W)
        (externalTensorSection a b (relativeDifferentialForms a (p : ℤ))
          (relativeDifferentialForms b (q : ℤ)) ω η W hW₁ hW₂)) =
      ((deRhamComplex (pullback.fst a b ≫ a)).XIsoOfEq
          (show p + (q + 1) = p + q + 1 by omega)).hom.val.app (op W)
        (SheafOfModules.formProduct (deRhamAlgebras (pullback.fst a b ≫ a)) p (q + 1) (op W)
          ((relativeDifferentialForms (pullback.fst a b ≫ a) (p : ℤ)).presheaf.map
            (homOfLE hW₁).op (deRhamBoxLeftPullback a b (p : ℤ) U ω))
          (((deRhamComplex (pullback.fst a b ≫ a)).d q (q + 1)).val.app (op W)
            ((relativeDifferentialForms (pullback.fst a b ≫ a) (q : ℤ)).presheaf.map
              (homOfLE hW₂).op (deRhamBoxRightPullback a b (q : ℤ) V η)))) :=
  (congrArg ((deRhamBoxWedgeHom a b (p + q + 1) p (q + 1)
        (show p + (q + 1) = p + q + 1 by omega)).1 (op W))
    (X_d_apply_externalTensorSection a b p q ω η W hW₁ hW₂)).trans
    (deRhamBoxWedgeHom_externalTensorSection_dRight a b p q ω η W hW₁ hW₂)

end Leibniz

/-! ### The Leibniz rule on one summand, and the chain-map property -/

/-- **The graded Leibniz rule on the `(p, q)` summand of `Tot(Ω^•_{X/S} ⊠ Ω^•_{Y/S})`.** The
Künneth comparison of the summand followed by the de Rham differential of `X ×_S Y / S` is the
sum of the two differentials of the double complex followed by the Künneth comparison of the
target summands, the second with the sign `(-1)^p` of [Stacks, Tag 012Z]. Both operators carry
the section attached to a local `p`-form `ω` on `X` and a local `q`-form `η` on `Y` to
`d(pr₁^*ω) ∧ pr₂^*η + (-1)^p pr₁^*ω ∧ d(pr₂^*η)`. -/
theorem deRhamBoxWedgeHom_comp_deRhamDiffOpDifferential (n p q : ℕ) (hpq : p + q = n)
    (h₁ : p + 1 + q = n + 1) (h₂ : p + (q + 1) = n + 1) :
    deRhamBoxWedgeHom a b n p q hpq ≫
        (deRhamDiffOpComplex (pullback.fst a b ≫ a)).d n (n + 1) =
      ((deRhamBoxDoubleComplex a b).d p (p + 1)).f q ≫
          deRhamBoxWedgeHom a b (n + 1) (p + 1) q h₁ +
        (-1 : ℤ) ^ p • (((deRhamBoxDoubleComplex a b).X p).d q (q + 1) ≫
          deRhamBoxWedgeHom a b (n + 1) p (q + 1) h₂) := by
  subst hpq
  refine hom_ext_of_externalTensorSection_target _ _ fun c ω η h₁ h₂ => ?_
  refine Eq.trans (deRhamBoxWedgeHom_comp_d_apply a b p q ω η c.ι.opensRange h₁ h₂) ?_
  refine Eq.trans (deRhamComplex_d_formProduct (pullback.fst a b ≫ a) p q
    (op c.ι.opensRange) _ _) ?_
  exact congrArg₂ (· + ·) (d_comp_deRhamBoxWedgeHom_apply a b p q ω η c.ι.opensRange h₁ h₂).symm
    (congrArg ((-1 : ℤ) ^ p • ·)
      (X_d_comp_deRhamBoxWedgeHom_apply a b p q ω η c.ι.opensRange h₁ h₂).symm)

/-- The first differential of the double complex followed by the degreewise Künneth isomorphism,
restricted to the `(p + 1, q)` summand. -/
theorem d_f_ιTotal_comp_deRhamBoxTotalDegreeIso (n p q : ℕ) (h : p + 1 + q = n + 1) :
    (((deRhamBoxDoubleComplex a b).d p (p + 1)).f q ≫
        (deRhamBoxDoubleComplex a b).ιTotal (ComplexShape.up ℕ) (p + 1) q (n + 1) h) ≫
        (deRhamBoxTotalDegreeIso a b (n + 1)).hom =
      ((deRhamBoxDoubleComplex a b).d p (p + 1)).f q ≫
        deRhamBoxWedgeHom a b (n + 1) (p + 1) q h :=
  (Category.assoc _ _ _).trans
    (whisker_eq _ (ιTotal_comp_deRhamBoxTotalDegreeIso_wedgeHom a b (n + 1) (p + 1) q h))

/-- The signed second differential of the double complex followed by the degreewise Künneth
isomorphism, restricted to the `(p, q + 1)` summand. -/
theorem X_d_ιTotal_comp_deRhamBoxTotalDegreeIso (n p q : ℕ) (h : p + (q + 1) = n + 1) :
    (((-1 : ℤˣ) ^ p) • (((deRhamBoxDoubleComplex a b).X p).d q (q + 1) ≫
        (deRhamBoxDoubleComplex a b).ιTotal (ComplexShape.up ℕ) p (q + 1) (n + 1) h)) ≫
        (deRhamBoxTotalDegreeIso a b (n + 1)).hom =
      ((-1 : ℤ) ^ p) • (((deRhamBoxDoubleComplex a b).X p).d q (q + 1) ≫
        deRhamBoxWedgeHom a b (n + 1) p (q + 1) h) :=
  (CategoryTheory.Preadditive.units_neg_one_pow_smul_comp p _ _).trans
    (congrArg (((-1 : ℤ) ^ p) • ·)
      ((Category.assoc _ _ _).trans
        (whisker_eq _ (ιTotal_comp_deRhamBoxTotalDegreeIso_wedgeHom a b (n + 1) p (q + 1) h))))

/-- The differential of the total complex restricted to the `(p, q)` summand, followed by the
degreewise Künneth isomorphism: by [Stacks, Tag 012Z] the differential is `d₁ + (-1)^p d₂`. -/
theorem ιTotal_comp_deRhamBoxTotal_d_eq (n p q : ℕ) (hpq : p + q = n) :
    (deRhamBoxDoubleComplex a b).ιTotal (ComplexShape.up ℕ) p q n hpq ≫
        ((deRhamBoxTotal a b).d n (n + 1) ≫ (deRhamBoxTotalDegreeIso a b (n + 1)).hom) =
      (((deRhamBoxDoubleComplex a b).d p (p + 1)).f q ≫
            (deRhamBoxDoubleComplex a b).ιTotal (ComplexShape.up ℕ) (p + 1) q (n + 1)
              (by dsimp; omega) +
          ((-1 : ℤˣ) ^ p) • (((deRhamBoxDoubleComplex a b).X p).d q (q + 1) ≫
            (deRhamBoxDoubleComplex a b).ιTotal (ComplexShape.up ℕ) p (q + 1) (n + 1)
              (by dsimp; omega))) ≫
        (deRhamBoxTotalDegreeIso a b (n + 1)).hom :=
  (Category.assoc _ _ _).symm.trans
    (eq_whisker (HomologicalComplex₂.ιTotal_d_up_ℕ (deRhamBoxDoubleComplex a b) p q n hpq) _)

/-- Composition in the category of finite-order differential operators is additive in its first
argument, applied to the two summands of the differential of the total complex. -/
theorem ιTotal_deRhamBoxTotal_d_add_comp (n p q : ℕ) (h₁ : p + 1 + q = n + 1)
    (h₂ : p + (q + 1) = n + 1) :
    (((deRhamBoxDoubleComplex a b).d p (p + 1)).f q ≫
          (deRhamBoxDoubleComplex a b).ιTotal (ComplexShape.up ℕ) (p + 1) q (n + 1) h₁ +
        ((-1 : ℤˣ) ^ p) • (((deRhamBoxDoubleComplex a b).X p).d q (q + 1) ≫
          (deRhamBoxDoubleComplex a b).ιTotal (ComplexShape.up ℕ) p (q + 1) (n + 1) h₂)) ≫
        (deRhamBoxTotalDegreeIso a b (n + 1)).hom =
      (((deRhamBoxDoubleComplex a b).d p (p + 1)).f q ≫
            (deRhamBoxDoubleComplex a b).ιTotal (ComplexShape.up ℕ) (p + 1) q (n + 1) h₁) ≫
          (deRhamBoxTotalDegreeIso a b (n + 1)).hom +
        (((-1 : ℤˣ) ^ p) • (((deRhamBoxDoubleComplex a b).X p).d q (q + 1) ≫
            (deRhamBoxDoubleComplex a b).ιTotal (ComplexShape.up ℕ) p (q + 1) (n + 1) h₂)) ≫
          (deRhamBoxTotalDegreeIso a b (n + 1)).hom :=
  Preadditive.add_comp _ _ _ _ _ _

/-- The two summands of the differential of the total complex, each followed by the degreewise
Künneth isomorphism, are the two differentials of the double complex followed by the Künneth
comparison of the target summand. -/
theorem ιTotal_deRhamBoxTotal_d_summands (n p q : ℕ) (h₁ : p + 1 + q = n + 1)
    (h₂ : p + (q + 1) = n + 1) :
    (((deRhamBoxDoubleComplex a b).d p (p + 1)).f q ≫
            (deRhamBoxDoubleComplex a b).ιTotal (ComplexShape.up ℕ) (p + 1) q (n + 1) h₁) ≫
          (deRhamBoxTotalDegreeIso a b (n + 1)).hom +
        (((-1 : ℤˣ) ^ p) • (((deRhamBoxDoubleComplex a b).X p).d q (q + 1) ≫
            (deRhamBoxDoubleComplex a b).ιTotal (ComplexShape.up ℕ) p (q + 1) (n + 1) h₂)) ≫
          (deRhamBoxTotalDegreeIso a b (n + 1)).hom =
      ((deRhamBoxDoubleComplex a b).d p (p + 1)).f q ≫
          deRhamBoxWedgeHom a b (n + 1) (p + 1) q h₁ +
        ((-1 : ℤ) ^ p) • (((deRhamBoxDoubleComplex a b).X p).d q (q + 1) ≫
          deRhamBoxWedgeHom a b (n + 1) p (q + 1) h₂) :=
  congrArg₂ (· + ·)
    (d_f_ιTotal_comp_deRhamBoxTotalDegreeIso a b n p q h₁)
    (X_d_ιTotal_comp_deRhamBoxTotalDegreeIso a b n p q h₂)

/-- The differential of the total complex restricted to the `(p, q)` summand, followed by the
degreewise Künneth isomorphism, with the composition distributed over the two summands of
`d₁ + (-1)^p d₂`. -/
theorem ιTotal_comp_deRhamBoxTotal_d_add (n p q : ℕ) (hpq : p + q = n)
    (h₁ : p + 1 + q = n + 1) (h₂ : p + (q + 1) = n + 1) :
    (deRhamBoxDoubleComplex a b).ιTotal (ComplexShape.up ℕ) p q n hpq ≫
        ((deRhamBoxTotal a b).d n (n + 1) ≫ (deRhamBoxTotalDegreeIso a b (n + 1)).hom) =
      (((deRhamBoxDoubleComplex a b).d p (p + 1)).f q ≫
            (deRhamBoxDoubleComplex a b).ιTotal (ComplexShape.up ℕ) (p + 1) q (n + 1) h₁) ≫
          (deRhamBoxTotalDegreeIso a b (n + 1)).hom +
        (((-1 : ℤˣ) ^ p) • (((deRhamBoxDoubleComplex a b).X p).d q (q + 1) ≫
            (deRhamBoxDoubleComplex a b).ιTotal (ComplexShape.up ℕ) p (q + 1) (n + 1) h₂)) ≫
          (deRhamBoxTotalDegreeIso a b (n + 1)).hom :=
  (ιTotal_comp_deRhamBoxTotal_d_eq a b n p q hpq).trans
    (ιTotal_deRhamBoxTotal_d_add_comp a b n p q h₁ h₂)

/-- The differential of the total complex followed by the degreewise Künneth isomorphism,
restricted to the `(p, q)` summand: by [Stacks, Tag 012Z] it is `d₁ + (-1)^p d₂` followed by the
Künneth comparison of the two target summands. -/
theorem ιTotal_comp_deRhamBoxTotal_d (n p q : ℕ) (hpq : p + q = n)
    (h₁ : p + 1 + q = n + 1) (h₂ : p + (q + 1) = n + 1) :
    (deRhamBoxDoubleComplex a b).ιTotal (ComplexShape.up ℕ) p q n hpq ≫
        ((deRhamBoxTotal a b).d n (n + 1) ≫ (deRhamBoxTotalDegreeIso a b (n + 1)).hom) =
      ((deRhamBoxDoubleComplex a b).d p (p + 1)).f q ≫
          deRhamBoxWedgeHom a b (n + 1) (p + 1) q h₁ +
        ((-1 : ℤ) ^ p) • (((deRhamBoxDoubleComplex a b).X p).d q (q + 1) ≫
          deRhamBoxWedgeHom a b (n + 1) p (q + 1) h₂) :=
  (ιTotal_comp_deRhamBoxTotal_d_add a b n p q hpq h₁ h₂).trans
    (ιTotal_deRhamBoxTotal_d_summands a b n p q h₁ h₂)

/-- The degreewise Künneth isomorphism followed by the de Rham differential of `X ×_S Y / S`,
restricted to the `(p, q)` summand. -/
theorem ιTotal_comp_deRhamBoxTotalDegreeIso_comp_d (n p q : ℕ) (hpq : p + q = n) :
    (deRhamBoxDoubleComplex a b).ιTotal (ComplexShape.up ℕ) p q n hpq ≫
        ((deRhamBoxTotalDegreeIso a b n).hom ≫
          (deRhamDiffOpComplex (pullback.fst a b ≫ a)).d n (n + 1)) =
      deRhamBoxWedgeHom a b n p q hpq ≫
        (deRhamDiffOpComplex (pullback.fst a b ≫ a)).d n (n + 1) :=
  (Category.assoc _ _ _).symm.trans
    (eq_whisker (ιTotal_comp_deRhamBoxTotalDegreeIso_wedgeHom a b n p q hpq) _)

/-- The differential of the total complex followed by the degreewise Künneth isomorphism,
restricted to the `(p, q)` summand, is the Künneth comparison of the summand followed by the de
Rham differential of `X ×_S Y / S`. This is the graded Leibniz rule
`AlgebraicGeometry.Scheme.Hom.deRhamBoxWedgeHom_comp_deRhamDiffOpDifferential` read on the
total complex. -/
theorem ιTotal_comp_deRhamBoxTotal_d_comp_wedgeHom (n p q : ℕ) (hpq : p + q = n)
    (h₁ : p + 1 + q = n + 1) (h₂ : p + (q + 1) = n + 1) :
    (deRhamBoxDoubleComplex a b).ιTotal (ComplexShape.up ℕ) p q n hpq ≫
        ((deRhamBoxTotal a b).d n (n + 1) ≫ (deRhamBoxTotalDegreeIso a b (n + 1)).hom) =
      deRhamBoxWedgeHom a b n p q hpq ≫
        (deRhamDiffOpComplex (pullback.fst a b ≫ a)).d n (n + 1) :=
  (ιTotal_comp_deRhamBoxTotal_d a b n p q hpq h₁ h₂).trans
    (deRhamBoxWedgeHom_comp_deRhamDiffOpDifferential a b n p q hpq h₁ h₂).symm

/-- The degreewise Künneth isomorphism commutes with the differentials after restriction to the
`(p, q)` summand of the total complex. -/
theorem ιTotal_comp_deRhamBoxTotal_d_comm (n p q : ℕ) (hpq : p + q = n)
    (h₁ : p + 1 + q = n + 1) (h₂ : p + (q + 1) = n + 1) :
    (deRhamBoxDoubleComplex a b).ιTotal (ComplexShape.up ℕ) p q n hpq ≫
        ((deRhamBoxTotal a b).d n (n + 1) ≫ (deRhamBoxTotalDegreeIso a b (n + 1)).hom) =
      (deRhamBoxDoubleComplex a b).ιTotal (ComplexShape.up ℕ) p q n hpq ≫
        ((deRhamBoxTotalDegreeIso a b n).hom ≫
          (deRhamDiffOpComplex (pullback.fst a b ≫ a)).d n (n + 1)) :=
  (ιTotal_comp_deRhamBoxTotal_d_comp_wedgeHom a b n p q hpq h₁ h₂).trans
    (ιTotal_comp_deRhamBoxTotalDegreeIso_comp_d a b n p q hpq).symm

/-- **The degreewise de Rham Künneth isomorphism of [Stacks, Tag 0FMA] commutes with the
differentials.** A morphism out of a term of a total complex is determined by its restrictions to
the summands, and on the `(p, q)` summand the identity is the graded Leibniz rule. -/
theorem deRhamBoxTotal_d_comp_deRhamBoxTotalDegreeIso (n : ℕ) :
    (deRhamBoxTotal a b).d n (n + 1) ≫ (deRhamBoxTotalDegreeIso a b (n + 1)).hom =
      (deRhamBoxTotalDegreeIso a b n).hom ≫
        (deRhamDiffOpComplex (pullback.fst a b ≫ a)).d n (n + 1) :=
  HomologicalComplex₂.total.hom_ext (ComplexShape.up ℕ)
    (K := deRhamBoxDoubleComplex a b) fun p q hpq =>
      ιTotal_comp_deRhamBoxTotal_d_comm a b n p q hpq
        ((Nat.add_right_comm p 1 q).trans (congrArg (· + 1) (hpq : p + q = n)))
        ((Nat.add_assoc p q 1).symm.trans (congrArg (· + 1) (hpq : p + q = n)))

end Scheme.Hom

end AlgebraicGeometry

end
