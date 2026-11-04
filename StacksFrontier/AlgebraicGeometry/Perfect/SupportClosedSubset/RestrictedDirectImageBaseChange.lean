module

public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.PushforwardRestrictSections

/-!
# The comparison of a restricted direct image, read on sections

For an open `U` of a scheme `Z` and an open immersion `g : X' ⟶ Z`,
`Stacks.Perfect.PushforwardRestrict`'s `restrictPushforwardRestrictIso` identifies
`g^*((U → Z)_*(M|_U))` with `(X' ∩ U → X')_*((g^*M)|_{X' ∩ U})`.  Read in the vocabulary of
[Stacks, Tag 0G7I] the two sides are the term `F_{i₀…i_p}` of the extended alternating Čech
complex restricted along `g` and the corresponding term of the complex of the restricted
equations, so the comparison is what the base change of that complex along an open immersion is
assembled from.  This file packages the comparison in that vocabulary — `restrictedFunctor` for
the term, with the index open on `X'` given as data rather than as `g ⁻¹ᵁ U`, which is how the
restricted equations present it — and computes what it does to a section: it restricts the
section along `restrictImage_eq`, the equality of the two spellings of `U ∩ g(V)`.

## Main definitions

* `restrictedFunctor`: the direct image of a restriction to an open, as a functor of the
  coefficient module, in the spelling of
  `AlgebraicGeometry.ExtendedAlternatingCech.restrictedModule`.
* `restrictedSection`: the canonical reading of a section of `(U → Z)_*(M|_U)` over `V` as a
  section of `M` over `U ∩ V`.
* `restrictedRestrictIso`: the comparison `g^*((U → Z)_*(M|_U)) ≅ (A → X')_*((g^*M)|_A)`,
  natural in the coefficient module, for an open `A` of `X'` presented by an equality
  `g ⁻¹ᵁ U = A`.

## Main results

* `restrictedSection_restrictedRestrictIso`: **the comparison on sections.**  Reading the image
  of a section under the comparison is restricting the section along `restrictImage_eq`.

## Implementation notes

The comparison is the composite of the comparison of the two models of a direct image of a
restriction (`restrictedFunctorIso`, which turns `Scheme.Modules.pullback` into
`Scheme.Modules.restrictFunctor`), the termwise locality `restrictPushforwardRestrictIso` of
`PushforwardRestrictOpen`, the same model comparison on `X'`, and a transport along the given
equality of opens.  Its section formula inherits the cost structure that shapes
`PushforwardRestrictSections`: identifying `Γ(G.obj M, V)` with `Γ(M, O)` for a stack `G` of
restrictions and direct images costs a sizeable fraction of the heartbeat budget, and the two
ends of `restrictPushforwardRestrictIso` cannot both be crossed twice in one declaration.  So the
composite is grouped from the left, each factor is pulled out by `trans_hom_app_app` in its own
declaration, and the two accumulated restriction maps are collapsed only at the end, by
`collapseStep`, where both sides are already in the `Γ(M, -)` spelling and the rewrite is free.
The index open of the restricted picture is taken as data so that the transport can be removed by
`cases` before any of this happens.

## References

* [Stacks Project, Tag 0G7U](https://stacks.math.columbia.edu/tag/0G7U)
* [Stacks Project, Tag 0G7I](https://stacks.math.columbia.edu/tag/0G7I)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace Stacks.Perfect.PushforwardRestrict

section Model

variable {Z : Scheme.{u}}

/-- The direct image of a restriction to an open, as a functor of the coefficient module, in the
spelling of `AlgebraicGeometry.ExtendedAlternatingCech.restrictedModule`. -/
public def restrictedFunctor (U : Z.Opens) : Z.Modules ⥤ Z.Modules :=
  Scheme.Modules.pullback U.ι ⋙ Scheme.Modules.pushforward U.ι

/-- The direct image of a restriction, written with `Scheme.Modules.restrictFunctor`, agrees with
`restrictedFunctor`. -/
public def restrictedFunctorIso (U : Z.Opens) :
    Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pushforward U.ι ≅
      restrictedFunctor U :=
  Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback U.ι)
    (Scheme.Modules.pushforward U.ι)

end Model


section Generic

variable {Y : Scheme.{u}} (A : Y.Opens) (N : Y.Modules) (V : Y.Opens)

/-- The canonical reading of a section of `(A → Y)_*(N|_A)` on `V` as a section of `N` on
`A ∩ V`. -/
public def restrictedSection (z : Γ((restrictedFunctor A).obj N, V)) :
    Γ(N, A.ι ''ᵁ (A.ι ⁻¹ᵁ V)) :=
  ((restrictedFunctorIso A).inv.app N).app V z

/-- The reading of a section cancels the comparison of the two models of the direct image. -/
public theorem restrictedSection_restrictedFunctorIso_hom
    (w : Γ((Scheme.Modules.pushforward A.ι).obj
      ((Scheme.Modules.restrictFunctor A.ι).obj N), V)) :
    restrictedSection A N V (((restrictedFunctorIso A).hom.app N).app V w) = w := by
  have h : (restrictedFunctorIso A).hom.app N ≫ (restrictedFunctorIso A).inv.app N = 𝟙 _ :=
    (restrictedFunctorIso A).hom_inv_id_app N
  change ((restrictedFunctorIso A).hom.app N ≫ (restrictedFunctorIso A).inv.app N).app V w = w
  rw [h]
  rfl

end Generic

section TwoOpens

variable {Z X' : Scheme.{u}} (U : Z.Opens) (g : X' ⟶ Z) [IsOpenImmersion g] (M : Z.Modules)

/-- The comparison of the two models of the direct image, restricted along `g`. -/
public def restrictedRestrictFactor₀ :
    restrictedFunctor U ⋙ Scheme.Modules.restrictFunctor g ≅
      Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pushforward U.ι ⋙
        Scheme.Modules.restrictFunctor g :=
  Functor.isoWhiskerRight (restrictedFunctorIso U).symm (Scheme.Modules.restrictFunctor g)

/-- The two spellings of `U ∩ g(V)` the comparison compares the sections on. -/
public theorem restrictImage_eq {A : X'.Opens} (hA : g ⁻¹ᵁ U = A)
    (V : X'.Opens) :
    g ''ᵁ (A.ι ''ᵁ (A.ι ⁻¹ᵁ V)) = U.ι ''ᵁ (U.ι ⁻¹ᵁ (g ''ᵁ V)) := by
  cases hA
  exact (comparisonOpen_eq₈ U g V).trans (comparisonOpen_eqUpTo₇ U g V)

/-- The first two factors of the comparison. -/
public def restrictedRestrictChain₂ :
    restrictedFunctor U ⋙ Scheme.Modules.restrictFunctor g ≅
      Scheme.Modules.restrictFunctor g ⋙ Scheme.Modules.restrictFunctor (g ⁻¹ᵁ U).ι ⋙
        Scheme.Modules.pushforward (g ⁻¹ᵁ U).ι :=
  restrictedRestrictFactor₀ U g ≪≫ restrictPushforwardRestrictIso U g

/-- **Termwise locality of a direct image along an open immersion**, with the index open of the
restricted picture spelled `g ⁻¹ᵁ U`. -/
public def restrictedRestrictIsoAux :
    restrictedFunctor U ⋙ Scheme.Modules.restrictFunctor g ≅
      Scheme.Modules.restrictFunctor g ⋙ restrictedFunctor (g ⁻¹ᵁ U) :=
  restrictedRestrictChain₂ U g ≪≫
    Functor.isoWhiskerLeft (Scheme.Modules.restrictFunctor g)
      (restrictedFunctorIso (g ⁻¹ᵁ U))

variable (V : X'.Opens)

/-- The first factor of the comparison reads the section in the `restrictFunctor` model. -/
public theorem restrictedRestrictFactor₀_app_apply
    (z : Γ((restrictedFunctor U).obj M, g ''ᵁ V)) :
    ((restrictedRestrictFactor₀ U g).hom.app M).app V z =
      restrictedSection U M (g ''ᵁ V) z := rfl

/-- The first two factors of the comparison, one factor at a time. -/
public theorem restrictedRestrictChain₂_app_apply_eq_factors
    (z : Γ((restrictedFunctor U).obj M, g ''ᵁ V)) :
    ((restrictedRestrictChain₂ U g).hom.app M).app V z =
      ((restrictPushforwardRestrictIso U g).hom.app M).app V
        (((restrictedRestrictFactor₀ U g).hom.app M).app V z) :=
  trans_hom_app_app (restrictedRestrictFactor₀ U g) (restrictPushforwardRestrictIso U g) M V z

/-- The first factor rewritten inside the second. -/
public theorem restrictedRestrictChain₂_app_apply_eq_factor
    (z : Γ((restrictedFunctor U).obj M, g ''ᵁ V)) :
    ((restrictPushforwardRestrictIso U g).hom.app M).app V
        (((restrictedRestrictFactor₀ U g).hom.app M).app V z) =
      ((restrictPushforwardRestrictIso U g).hom.app M).app V
        (restrictedSection U M (g ''ᵁ V) z) :=
  congrArg (fun y => ((restrictPushforwardRestrictIso U g).hom.app M).app V y)
    (restrictedRestrictFactor₀_app_apply U g M V z)

/-- **The first two factors of the comparison, on sections.** -/
public theorem restrictedRestrictChain₂_app_apply
    (z : Γ((restrictedFunctor U).obj M, g ''ᵁ V)) :
    ((restrictedRestrictChain₂ U g).hom.app M).app V z =
      ((comparisonFactor₈ U g).hom.app M).app V
        (M.presheaf.map (eqToHom (comparisonOpen_eqUpTo₇ U g V)).op
          (restrictedSection U M (g ''ᵁ V) z)) :=
  (restrictedRestrictChain₂_app_apply_eq_factors U g M V z).trans
    ((restrictedRestrictChain₂_app_apply_eq_factor U g M V z).trans
      (restrictPushforwardRestrictIso_app_apply_eq_factor₈ U g V M _))

/-- The comparison applied to a section, as its last factor applied to the first two. -/
public theorem restrictedRestrictIsoAux_app_apply_eq_factors
    (z : Γ((restrictedFunctor U).obj M, g ''ᵁ V)) :
    ((restrictedRestrictIsoAux U g).hom.app M).app V z =
      ((Functor.isoWhiskerLeft (Scheme.Modules.restrictFunctor g)
          (restrictedFunctorIso (g ⁻¹ᵁ U))).hom.app M).app V
        (((restrictedRestrictChain₂ U g).hom.app M).app V z) :=
  trans_hom_app_app (restrictedRestrictChain₂ U g)
    (Functor.isoWhiskerLeft (Scheme.Modules.restrictFunctor g)
      (restrictedFunctorIso (g ⁻¹ᵁ U))) M V z

/-- Reading the section cancels the last factor of the comparison. -/
public theorem restrictedSection_restrictedRestrictIsoAux_eq_chain₂
    (z : Γ((restrictedFunctor U).obj M, g ''ᵁ V)) :
    restrictedSection (g ⁻¹ᵁ U) ((Scheme.Modules.restrictFunctor g).obj M) V
        (((restrictedRestrictIsoAux U g).hom.app M).app V z) =
      ((restrictedRestrictChain₂ U g).hom.app M).app V z :=
  (congrArg (restrictedSection (g ⁻¹ᵁ U) ((Scheme.Modules.restrictFunctor g).obj M) V)
      (restrictedRestrictIsoAux_app_apply_eq_factors U g M V z)).trans
    (restrictedSection_restrictedFunctorIso_hom (g ⁻¹ᵁ U)
      ((Scheme.Modules.restrictFunctor g).obj M) V _)

/-- **The comparison, read on a section**, as the two accumulated restriction maps. -/
public theorem restrictedSection_restrictedRestrictIsoAux_eq_maps
    (z : Γ((restrictedFunctor U).obj M, g ''ᵁ V)) :
    restrictedSection (g ⁻¹ᵁ U) ((Scheme.Modules.restrictFunctor g).obj M) V
        (((restrictedRestrictIsoAux U g).hom.app M).app V z) =
      M.presheaf.map (eqToHom (comparisonOpen_eq₈ U g V)).op
        (M.presheaf.map (eqToHom (comparisonOpen_eqUpTo₇ U g V)).op
          (restrictedSection U M (g ''ᵁ V) z)) :=
  (restrictedSection_restrictedRestrictIsoAux_eq_chain₂ U g M V z).trans
    ((restrictedRestrictChain₂_app_apply U g M V z).trans
      (comparisonFactor₈_app_apply_restricted U g V M _))

/-- **The comparison of a restricted direct image, read on a section.**  It restricts the
section along the equality `restrictImage_eq` of the two spellings of `U ∩ g(V)`. -/
public theorem restrictedSection_restrictedRestrictIsoAux
    (z : Γ((restrictedFunctor U).obj M, g ''ᵁ V)) :
    restrictedSection (g ⁻¹ᵁ U) ((Scheme.Modules.restrictFunctor g).obj M) V
        (((restrictedRestrictIsoAux U g).hom.app M).app V z) =
      M.presheaf.map (eqToHom (restrictImage_eq U g rfl V)).op
        (restrictedSection U M (g ''ᵁ V) z) :=
  (restrictedSection_restrictedRestrictIsoAux_eq_maps U g M V z).trans
    (collapseStep M (comparisonOpen_eqUpTo₇ U g V) (comparisonOpen_eq₈ U g V)
      (restrictImage_eq U g rfl V) _)

/-- The same comparison, with the index open on `X'` given as data. -/
public def restrictedRestrictIso {A : X'.Opens} (hA : g ⁻¹ᵁ U = A) :
    restrictedFunctor U ⋙ Scheme.Modules.restrictFunctor g ≅
      Scheme.Modules.restrictFunctor g ⋙ restrictedFunctor A :=
  restrictedRestrictIsoAux U g ≪≫
    eqToIso (congrArg (fun B : X'.Opens =>
      Scheme.Modules.restrictFunctor g ⋙ restrictedFunctor B) hA)

/-- **The comparison of a restricted direct image, read on a section**, with the index open on
`X'` given as data. -/
public theorem restrictedSection_restrictedRestrictIso {A : X'.Opens}
    (hA : g ⁻¹ᵁ U = A) (z : Γ((restrictedFunctor U).obj M, g ''ᵁ V)) :
    restrictedSection A ((Scheme.Modules.restrictFunctor g).obj M) V
        (((restrictedRestrictIso U g hA).hom.app M).app V z) =
      M.presheaf.map (eqToHom (restrictImage_eq U g hA V)).op
        (restrictedSection U M (g ''ᵁ V) z) := by
  cases hA
  exact restrictedSection_restrictedRestrictIsoAux U g M V z

end TwoOpens

end Stacks.Perfect.PushforwardRestrict

end
