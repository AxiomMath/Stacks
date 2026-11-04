module

public import StacksFrontier.AlgebraicGeometry.AffineClosedUnion.Basic
public import Mathlib.AlgebraicGeometry.Cover.Directed

/-!
# The scheme-theoretic union of two closed subschemes is a pushout

Let `X` be a scheme and let `I₁`, `I₂` be two quasi-coherent ideal sheaves on `X` whose
intersection is zero, so that the scheme-theoretic union of the two closed subschemes they cut
out is the whole of `X`. This file proves that the square

```
X(I₁ ⊔ I₂) ---> X(I₁)
    |             |
    v             v
  X(I₂) --------> X
```

is *cocartesian* in the category of all schemes, where `X(I)` denotes
`AlgebraicGeometry.Scheme.IdealSheafData.subscheme`.

`StacksFrontier.AlgebraicGeometry.AffineClosedUnion.Basic` proves the affine case: over
`X = Spec A` with `I₁`, `I₂` cut out by ideals `I` and `J` with `I ⊓ J = ⊥`, the ring `A` is the
fibre product `A ⧸ I ×_{A ⧸ (I + J)} A ⧸ J`, and hence `Spec A` is the pushout. Here that
statement is globalised, and the globalisation really is *local on `X`*: over an affine open `U`
every object of the span is `Spec (Γ(X, U) ⧸ ...)`, by Mathlib's
`AlgebraicGeometry.Scheme.IdealSheafData.glueDataObj`, so the affine case applies verbatim, and
the resulting morphisms out of the affine opens of `X` are glued with
`AlgebraicGeometry.Scheme.OpenCover.glueMorphismsOfLocallyDirected` over the *locally directed*
cover `AlgebraicGeometry.Scheme.directedAffineCover` of all affine opens. Because that cover is
locally directed, gluing asks only for compatibility with the inclusions `U ≤ V` of affine opens;
no condition on a fibre product of two affine opens, which is not affine, is ever needed.

The pay-off is the reduced case of [Stacks, Tag 09NL] for two pieces: a scheme covered set
theoretically by two *affine* closed subschemes is affine, because it is then the pushout of a
span of affine schemes along a closed immersion, and such a pushout is `Spec` of a fibre product
of rings by `Stacks.AffineClosedUnion.isPushout_affineModel`. The hypothesis actually used is
`I₁ ⊓ I₂ = ⊥`; reducedness of `X` enters only through
`Stacks.AffineClosedUnion.ker_inf_ker_eq_bot` (the sheaf-level form of [Stacks, Tag 09NW]),
which turns a set-theoretic covering into that hypothesis.

## Main results

* `Stacks.AffineClosedUnion.isPushout_glueDataObjι`: the affine-local pushout square, over an
  affine open `U` of `X`.
* `Stacks.AffineClosedUnion.hom_ext_of_inf_eq_bot`: two closed subschemes meeting in the zero
  ideal sheaf are *jointly epimorphic* — a morphism out of `X` is determined by its restrictions
  to them.
* `Stacks.AffineClosedUnion.isPushout_subschemeι`: the global cocartesian square.
* `Stacks.AffineClosedUnion.isAffine_of_inf_eq_bot`: if both closed subschemes are affine and
  the two ideal sheaves meet in zero, then `X` is affine.
* `Stacks.AffineClosedUnion.isAffine_of_isClosedImmersion_union`: the reduced two-piece case of
  [Stacks, Tag 09NL], stated for two closed immersions whose ranges cover a reduced `X`.

## Implementation notes

`Stacks.AffineClosedUnion.chart` is `AlgebraicGeometry.Scheme.IdealSheafData.subschemeCover.f`
with its source spelled `glueDataObj U` instead of as a projection of the cover. The two are
definitionally equal, but the projection form forces the elaborator to unfold `subschemeCover`
before the composite with `glueDataObjMap` typechecks, which makes `rw` motives fail; naming the
object once removes that friction from every proof below.

`Stacks.AffineClosedUnion.glueDataObjMap_chart` is the one piece of plumbing that was genuinely
missing: the affine charts `Spec (Γ(X, U) ⧸ I(U))` of the closed subscheme are compatible with
shrinking `U`. Mathlib has the companion statements for the inclusion into `X`
(`glueDataObjMap_glueDataObjι`) and for a containment of ideal sheaves
(`subSchemeCover_map_inclusion`) but not this one; it follows by cancelling the monomorphism
`subschemeι`.

## References

* [Stacks Project, Tag 09NL](https://stacks.math.columbia.edu/tag/09NL)
* [Stacks Project, Tag 09NW](https://stacks.math.columbia.edu/tag/09NW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.IdealSheafData

universe u

namespace Stacks.AffineClosedUnion

variable {X : Scheme.{u}}

section Charts

variable (I : X.IdealSheafData)

/-- The affine chart `Spec (Γ(X, U) ⧸ I(U)) ⟶ X(I)` of the closed subscheme cut out by `I`,
associated to an affine open `U` of `X`. This is Mathlib's `subschemeCover.f` with its source
named, so that composites with `glueDataObjMap` and `glueDataObjHom` are syntactically
well-typed. -/
noncomputable def chart (U : X.affineOpens) : I.glueDataObj U ⟶ I.subscheme :=
  I.subschemeCover.f U

/-- The affine charts of a closed subscheme sit over the affine opens of `X`. -/
@[reassoc (attr := simp)]
theorem chart_subschemeι (U : X.affineOpens) :
    chart I U ≫ I.subschemeι = I.glueDataObjι U ≫ U.1.ι :=
  I.subschemeCover_map_subschemeι U

/-- The affine charts of a closed subscheme are jointly epimorphic. -/
theorem subscheme_hom_ext {T : Scheme.{u}} (u v : I.subscheme ⟶ T)
    (H : ∀ U : X.affineOpens, chart I U ≫ u = chart I U ≫ v) : u = v :=
  I.subschemeCover.openCover.hom_ext u v H

/-- The affine charts are compatible with a containment of ideal sheaves. -/
@[reassoc (attr := simp)]
theorem chart_inclusion {I J : X.IdealSheafData} (hIJ : I ≤ J) (U : X.affineOpens) :
    chart J U ≫ inclusion hIJ = glueDataObjHom hIJ U ≫ chart I U :=
  subSchemeCover_map_inclusion hIJ U

/-- **The chart compatibility that Mathlib does not have.** The affine charts of the closed
subscheme cut out by `I` are compatible with shrinking the affine open; this is the companion of
`glueDataObjMap_glueDataObjι`, for the chart maps into the subscheme rather than into `X`. -/
@[reassoc (attr := simp)]
theorem glueDataObjMap_chart {U V : X.affineOpens} (h : U ≤ V) :
    I.glueDataObjMap h ≫ chart I V = chart I U :=
  (cancel_mono I.subschemeι).mp <| by
    rw [Category.assoc, chart_subschemeι, glueDataObjMap_glueDataObjι_assoc, X.homOfLE_ι,
      chart_subschemeι]

/-- The affine opens of `X` are jointly epimorphic. -/
theorem affine_hom_ext {T : Scheme.{u}} (u v : X ⟶ T)
    (H : ∀ U : X.affineOpens, U.1.ι ≫ u = U.1.ι ≫ v) : u = v :=
  X.directedAffineCover.hom_ext u v H

end Charts

section AffineLocal

variable (I I₁ I₂ : X.IdealSheafData)

/-- The closed immersion `Spec (Γ(X, U) ⧸ I(U)) ⟶ U` becomes the `Spec` of the quotient map once
`U` is identified with `Spec Γ(X, U)`. -/
theorem glueDataObjι_isoSpec_hom (U : X.affineOpens) :
    I.glueDataObjι U ≫ U.2.isoSpec.hom =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U))) :=
  (Iso.eq_comp_inv _).mp rfl

/-- The ideals cut out on an affine open by two ideal sheaves meeting in zero meet in zero. -/
theorem ideal_inf_eq_bot (h : I₁ ⊓ I₂ = ⊥) (U : X.affineOpens) :
    I₁.ideal U ⊓ I₂.ideal U = ⊥ :=
  congrFun (congrArg Scheme.IdealSheafData.ideal h) U

/-- **The affine-local pushout square.** Over an affine open `U` of `X`, if the two ideal sheaves
meet in zero then `U` is the pushout of the span of the three affine charts. This is the affine
case `Stacks.AffineClosedUnion.isPushout_specMap_quotientMk` read through Mathlib's `glueDataObj`
charts. -/
theorem isPushout_glueDataObjι (U : X.affineOpens) (hb : I₁.ideal U ⊓ I₂.ideal U = ⊥) :
    IsPushout (glueDataObjHom (le_sup_left : I₁ ≤ I₁ ⊔ I₂) U)
      (glueDataObjHom (le_sup_right : I₂ ≤ I₁ ⊔ I₂) U)
      (I₁.glueDataObjι U) (I₂.glueDataObjι U) :=
  (isPushout_specMap_quotientMk (I₁.ideal U) (I₂.ideal U) hb).of_iso'
    (Iso.refl _) (Iso.refl _) (Iso.refl _) U.2.isoSpec rfl rfl
    ((Category.id_comp _).trans (glueDataObjι_isoSpec_hom I₁ U).symm)
    ((Category.id_comp _).trans (glueDataObjι_isoSpec_hom I₂ U).symm)

end AffineLocal

section JointlyEpi

variable (I₁ I₂ : X.IdealSheafData)

/-- **Two closed subschemes meeting in the zero ideal sheaf are jointly epimorphic.** A morphism
out of `X` is determined by its restrictions to them. The proof is local on `X`: over an affine
open the two charts are jointly epimorphic because that open is their pushout. -/
theorem hom_ext_of_inf_eq_bot (h : I₁ ⊓ I₂ = ⊥) {T : Scheme.{u}} (u v : X ⟶ T)
    (h₁ : I₁.subschemeι ≫ u = I₁.subschemeι ≫ v)
    (h₂ : I₂.subschemeι ≫ u = I₂.subschemeι ≫ v) : u = v := by
  refine affine_hom_ext u v fun U ↦ ?_
  refine (isPushout_glueDataObjι I₁ I₂ U (ideal_inf_eq_bot I₁ I₂ h U)).hom_ext ?_ ?_ <;>
    simp only [← chart_subschemeι_assoc, h₁, h₂]

end JointlyEpi

section Descent

variable (I₁ I₂ : X.IdealSheafData) (h : I₁ ⊓ I₂ = ⊥) {T : Scheme.{u}}
  (a : I₁.subscheme ⟶ T) (b : I₂.subscheme ⟶ T)
  (w : inclusion (le_sup_left : I₁ ≤ I₁ ⊔ I₂) ≫ a =
    inclusion (le_sup_right : I₂ ≤ I₁ ⊔ I₂) ≫ b)

/-- The descent of a pair of compatible morphisms to an affine open of `X`, obtained from the
affine-local pushout square. -/
noncomputable def localDesc (U : X.affineOpens) : U.1.toScheme ⟶ T :=
  (isPushout_glueDataObjι I₁ I₂ U (ideal_inf_eq_bot I₁ I₂ h U)).desc
    (chart I₁ U ≫ a) (chart I₂ U ≫ b) <| by
      rw [← chart_inclusion_assoc, ← chart_inclusion_assoc, w]

/-- The local descent restricts to `a` on the affine chart of the first closed subscheme. -/
@[reassoc (attr := simp)]
theorem glueDataObjι_localDesc_left (U : X.affineOpens) :
    I₁.glueDataObjι U ≫ localDesc I₁ I₂ h a b w U = chart I₁ U ≫ a :=
  IsPushout.inl_desc _ _ _ _

/-- The local descent restricts to `b` on the affine chart of the second closed subscheme. -/
@[reassoc (attr := simp)]
theorem glueDataObjι_localDesc_right (U : X.affineOpens) :
    I₂.glueDataObjι U ≫ localDesc I₁ I₂ h a b w U = chart I₂ U ≫ b :=
  IsPushout.inr_desc _ _ _ _

/-- The local descents are compatible with shrinking the affine open. This is the only
compatibility a locally directed cover asks for. -/
theorem homOfLE_localDesc {U V : X.affineOpens} (hUV : U ≤ V) :
    X.homOfLE hUV ≫ localDesc I₁ I₂ h a b w V = localDesc I₁ I₂ h a b w U :=
  by refine (isPushout_glueDataObjι I₁ I₂ U (ideal_inf_eq_bot I₁ I₂ h U)).hom_ext ?_ ?_ <;>
    simp [← glueDataObjMap_glueDataObjι_assoc]

/-- The global descent of a pair of compatible morphisms out of the two closed subschemes, glued
from the local descents over the locally directed cover of `X` by all of its affine opens. -/
noncomputable def globalDesc : X ⟶ T :=
  X.directedAffineCover.glueMorphismsOfLocallyDirected (localDesc I₁ I₂ h a b w)
    fun {U V} hUV ↦ by
      rw [show Scheme.Cover.trans X.directedAffineCover hUV = X.homOfLE (leOfHom hUV) from
        Scheme.directedAffineCover_trans (leOfHom hUV)]
      exact homOfLE_localDesc I₁ I₂ h a b w (leOfHom hUV)

/-- The global descent restricts to the local descent on each affine open of `X`. -/
@[reassoc (attr := simp)]
theorem ι_globalDesc (U : X.affineOpens) :
    U.1.ι ≫ globalDesc I₁ I₂ h a b w = localDesc I₁ I₂ h a b w U :=
  X.directedAffineCover.map_glueMorphismsOfLocallyDirected _ _ U

/-- The global descent restricts to `a` on the first closed subscheme. -/
@[reassoc (attr := simp)]
theorem subschemeι_globalDesc_left : I₁.subschemeι ≫ globalDesc I₁ I₂ h a b w = a :=
  subscheme_hom_ext I₁ _ _ fun U ↦ by simp

/-- The global descent restricts to `b` on the second closed subscheme. -/
@[reassoc (attr := simp)]
theorem subschemeι_globalDesc_right : I₂.subschemeι ≫ globalDesc I₁ I₂ h a b w = b :=
  subscheme_hom_ext I₂ _ _ fun U ↦ by simp

end Descent

section Pushout

variable (I₁ I₂ : X.IdealSheafData)

/-- **The global cocartesian square, and the globalisation of the affine case of
[Stacks, Tag 09NL].** If two quasi-coherent ideal sheaves on `X` meet in zero — equivalently, the
scheme-theoretic union of the two closed subschemes they cut out is the whole of `X` — then `X`
is the pushout of `X(I₁) ← X(I₁ ⊔ I₂) → X(I₂)` in the category of all schemes. -/
theorem isPushout_subschemeι (h : I₁ ⊓ I₂ = ⊥) :
    IsPushout (inclusion (le_sup_left : I₁ ≤ I₁ ⊔ I₂))
      (inclusion (le_sup_right : I₂ ≤ I₁ ⊔ I₂)) I₁.subschemeι I₂.subschemeι := by
  have hsq : inclusion (le_sup_left : I₁ ≤ I₁ ⊔ I₂) ≫ I₁.subschemeι =
      inclusion (le_sup_right : I₂ ≤ I₁ ⊔ I₂) ≫ I₂.subschemeι := by
    rw [inclusion_subschemeι, inclusion_subschemeι]
  refine IsPushout.of_isColimit
    (PushoutCocone.isColimitAux' (PushoutCocone.mk _ _ hsq) fun s ↦ ?_)
  exact ⟨globalDesc I₁ I₂ h s.inl s.inr s.condition,
    subschemeι_globalDesc_left I₁ I₂ h s.inl s.inr s.condition,
    subschemeι_globalDesc_right I₁ I₂ h s.inl s.inr s.condition, fun hm₁ hm₂ ↦
      hom_ext_of_inf_eq_bot I₁ I₂ h _ _ (by rwa [subschemeι_globalDesc_left])
        (by rwa [subschemeι_globalDesc_right])⟩

/-- The inclusion of closed subschemes induced by a containment of ideal sheaves is a closed
immersion. -/
instance isClosedImmersion_inclusion {I J : X.IdealSheafData} (hIJ : I ≤ J) :
    IsClosedImmersion (inclusion hIJ) :=
  have : IsClosedImmersion (inclusion hIJ ≫ I.subschemeι) := by
    rw [inclusion_subschemeι]; infer_instance
  IsClosedImmersion.of_comp_isClosedImmersion _ I.subschemeι

/-- **The two-piece case of [Stacks, Tag 09NL] in ideal-sheaf form.** If two quasi-coherent ideal
sheaves on `X` meet in zero and both closed subschemes they cut out are affine, then `X` is
affine: it is the pushout of a span of affine schemes along a closed immersion, and such a
pushout is the `Spec` of a fibre product of rings. -/
theorem isAffine_of_inf_eq_bot (h : I₁ ⊓ I₂ = ⊥)
    [IsAffine I₁.subscheme] [IsAffine I₂.subscheme] : IsAffine X := by
  have : IsAffine (I₁ ⊔ I₂).subscheme :=
    isAffine_of_isAffineHom (inclusion (le_sup_left : I₁ ≤ I₁ ⊔ I₂))
  exact (IsAffine.iff_of_isIso ((isPushout_affineModel _ _).isoIsPushout _ _
    (isPushout_subschemeι I₁ I₂ h)).hom).mp inferInstance

end Pushout

section Reduced

variable {Z₁ Z₂ : Scheme.{u}}

/-- The closed subscheme cut out by the kernel of a closed immersion is isomorphic to its source,
so it is affine whenever the source is. -/
theorem isAffine_ker_subscheme (i : Z₁ ⟶ X) [IsClosedImmersion i] [IsAffine Z₁] :
    IsAffine i.ker.subscheme :=
  (IsAffine.iff_of_isIso i.toImage).mp inferInstance

/-- **The reduced two-piece case of [Stacks, Tag 09NL].** A reduced scheme which is set
theoretically the union of two affine closed subschemes is affine.

Reducedness is used exactly once, through `Stacks.AffineClosedUnion.ker_inf_ker_eq_bot` (the
sheaf-level form of [Stacks, Tag 09NW]), to turn the set-theoretic covering into the hypothesis
`i₁.ker ⊓ i₂.ker = ⊥` of `Stacks.AffineClosedUnion.isAffine_of_inf_eq_bot`. -/
theorem isAffine_of_isClosedImmersion_union [IsReduced X] (i₁ : Z₁ ⟶ X) (i₂ : Z₂ ⟶ X)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsAffine Z₁] [IsAffine Z₂]
    (hcov : Set.range i₁.base ∪ Set.range i₂.base = Set.univ) : IsAffine X :=
  have := isAffine_ker_subscheme i₁
  have := isAffine_ker_subscheme i₂
  isAffine_of_inf_eq_bot i₁.ker i₂.ker (ker_inf_ker_eq_bot i₁ i₂ hcov)

end Reduced

end Stacks.AffineClosedUnion

end
