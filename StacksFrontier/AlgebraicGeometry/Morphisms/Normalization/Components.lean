module

public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
public import StacksFrontier.AlgebraicGeometry.Limits.SigmaIntegralHom
public import StacksFrontier.AlgebraicGeometry.Limits.SigmaIrreducibleComponents
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Stability
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.IntegralBirational
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal
public import StacksFrontier.AlgebraicGeometry.NormalizationBirational.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.SigmaPoints

/-!
# Normalization of the irreducible components

Let `X` be a scheme whose quasi-compact opens have finitely many irreducible components. Each
irreducible component of `X`, with its reduced induced closed subscheme structure, is an integral
scheme and so has a normalization, and the coproduct of those normalizations, with its canonical
morphism to `X`, is the normalization of `X`.

## Main definitions

* `AlgebraicGeometry.Scheme.reducedComponent` is an irreducible component of `X` with its reduced
  induced closed subscheme structure, and `AlgebraicGeometry.Scheme.reducedComponentι` is its
  closed immersion into `X`.
* `AlgebraicGeometry.Scheme.reducedComponentToReduction` factors that closed immersion through
  the reduction of `X`, and `AlgebraicGeometry.Scheme.reducedComponentsToReduction` assembles
  those factors into a morphism from the coproduct of the components.
* `AlgebraicGeometry.Scheme.sigmaNormalizationReducedComponent` is the coproduct of the
  normalizations of the reduced irreducible components, and
  `AlgebraicGeometry.Scheme.sigmaNormalizationToReduction` is its canonical morphism to the
  reduction of `X`.

## Main results

* `AlgebraicGeometry.Scheme.exists_iso_normalizationScheme_sigma_reducedComponent` is Tag 0CDV:
  the coproduct of the normalizations of the reduced irreducible components, with its canonical
  morphism to `X`, is the normalization of `X`.
* `AlgebraicGeometry.Scheme.exists_iso_sigma_isIntegral_isNormal_normalizationScheme` is part (1)
  of Tag 035Q: the normalization of `X` is a disjoint union of integral normal schemes.
* `AlgebraicGeometry.Scheme.isIntegral_reducedComponent`: a reduced irreducible component is an
  integral scheme, so it has a normalization.
* `AlgebraicGeometry.Scheme.isGenericPoint_reducedComponentι`: the generic point of a reduced
  irreducible component is the generic point of that component of `X`.
* `AlgebraicGeometry.Scheme.finite_setOf_irreducibleComponents_inter_nonempty`: only finitely
  many irreducible components of `X` meet an open set with finitely many irreducible components.
* `AlgebraicGeometry.Scheme.isBirational_reducedComponentsToReduction`: the coproduct of the
  reduced irreducible components is birational over the reduction of `X`.
* `AlgebraicGeometry.Scheme.exists_iso_normalizationScheme_of_isIntegralHom_of_isBirational`: an
  integral morphism onto `X` from a normal scheme which is birational over every quasi-compact
  open *is* the normalization of `X`.

## Implementation notes

`AlgebraicGeometry.Scheme.reducedComponent` is the *reduced* induced structure on an irreducible
component, cut out by the vanishing ideal sheaf of the component. It is not Mathlib's
`AlgebraicGeometry.Scheme.irreducibleComponent`, which carries a different, generally non-reduced,
closed subscheme structure and is defined only for a locally Noetherian scheme.

The source reduces to the case of a reduced `X` and then invokes Tag 035Q part (3). The reduction
is unavoidable: the morphism from the coproduct of the components is birational only over the
reduction, since the local ring of a non-reduced `X` at a generic point is not a field. So the
whole argument is carried out over `X.nilradical.subscheme` and transported along the
isomorphism of Tag 035O at the end.

Part (3) of Tag 035Q is applied not to the coproduct of the components but to the coproduct of
their *normalizations*. That source is already normal, so Tag 0H7D makes its own normalization
morphism an isomorphism, which is what identifies it with the normalization of `X`. Applying
part (3) to the coproduct of the components instead would leave the separate task of showing
that normalization commutes with coproducts, and that is not formal: the pushforward along an
infinite disjoint union is a product rather than a sum, so it would need the same local
finiteness bookkeeping all over again.

Integrality of the morphism from the coproduct is `AlgebraicGeometry.isIntegralHom_sigmaDesc`,
whose local-finiteness hypothesis is supplied by
`AlgebraicGeometry.Scheme.finite_setOf_irreducibleComponents_inter_nonempty`.

## References

* [Stacks Project, Tag 0CDV](https://stacks.math.columbia.edu/tag/0CDV)
* [Stacks Project, Tag 035O](https://stacks.math.columbia.edu/tag/035O)
* [Stacks Project, Tag 035Q](https://stacks.math.columbia.edu/tag/035Q)
* [Stacks Project, Tag 0H7D](https://stacks.math.columbia.edu/tag/0H7D)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-! ### The reduced irreducible components -/

/-- An irreducible component of `X`, regarded as a closed subset. -/
abbrev componentCloseds (Z : irreducibleComponents X) : Closeds X :=
  ⟨(Z : Set X), isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩

/-- An irreducible component of `X` with its reduced induced closed subscheme structure. -/
@[ega "IV 13.1.2" "partial", sga "4 IX 5.6" "The schemes Y_i"]
abbrev reducedComponent (Z : irreducibleComponents X) : Scheme.{u} :=
  (IdealSheafData.vanishingIdeal (X.componentCloseds Z)).subscheme

/-- The closed immersion of a reduced irreducible component of `X` into `X`. -/
abbrev reducedComponentι (Z : irreducibleComponents X) : X.reducedComponent Z ⟶ X :=
  (IdealSheafData.vanishingIdeal (X.componentCloseds Z)).subschemeι

/-- The underlying set of a reduced irreducible component is the component itself. -/
@[simp] theorem range_reducedComponentι (Z : irreducibleComponents X) :
    Set.range (X.reducedComponentι Z) = (Z : Set X) :=
  IdealSheafData.range_subschemeι_vanishingIdeal _

/-- A reduced irreducible component is an irreducible scheme. -/
instance irreducibleSpace_reducedComponent (Z : irreducibleComponents X) :
    IrreducibleSpace (X.reducedComponent Z) :=
  IdealSheafData.irreducibleSpace_subscheme X _
    ((X.range_reducedComponentι Z).symm ▸ Z.2.1)

/-- A reduced irreducible component is an integral scheme: it is reduced by construction and
irreducible because its underlying space is an irreducible component of `X`. -/
@[ega "II 6.5.1" "partial"]
instance isIntegral_reducedComponent (Z : irreducibleComponents X) :
    IsIntegral (X.reducedComponent Z) :=
  isIntegral_of_irreducibleSpace_of_isReduced _

/-- Every point of a reduced irreducible component lies in that component. -/
theorem reducedComponentι_mem (Z : irreducibleComponents X) (w : X.reducedComponent Z) :
    X.reducedComponentι Z w ∈ (Z : Set X) := by
  rw [← X.range_reducedComponentι Z]
  exact ⟨w, rfl⟩

/-- The generic point of a reduced irreducible component of `X` is the generic point of the
corresponding irreducible component of `X`. -/
theorem isGenericPoint_reducedComponentι (Z : irreducibleComponents X) :
    IsGenericPoint (X.reducedComponentι Z (genericPoint (X.reducedComponent Z)))
      (Z : Set X) := by
  have h := (X.reducedComponentι Z).isClosedEmbedding.closure_image_eq
    ({genericPoint (X.reducedComponent Z)} : Set (X.reducedComponent Z))
  rw [Set.image_singleton, genericPoint_closure, Set.image_univ,
    X.range_reducedComponentι Z] at h
  exact h

/-- A reduced irreducible component of `X` has finitely many irreducible components on each of
its opens, so it has a normalization: it is an irreducible scheme, so each of its opens is
preirreducible. -/
theorem finite_irreducibleComponents_reducedComponent (Z : irreducibleComponents X) :
    ∀ U : (X.reducedComponent Z).Opens, IsCompact (U : Set (X.reducedComponent Z)) →
      (irreducibleComponents U).Finite :=
  fun U _ ↦ finite_irreducibleComponents_isOpen_of_irreducibleSpace U.2

/-! ### Factoring through the reduction -/

/-- A reduced irreducible component of `X`, as a closed subscheme of the reduction of `X`: the
component is reduced, so its closed immersion into `X` factors through the reduction. -/
def reducedComponentToReduction (Z : irreducibleComponents X) :
    X.reducedComponent Z ⟶ X.nilradical.subscheme :=
  Classical.choose (existsUnique_lift_nilradical_subschemeι (X.reducedComponentι Z))

/-- The closed immersion of a reduced irreducible component of `X` is its closed immersion into
the reduction of `X` followed by the closed immersion of the reduction. -/
@[simp]
theorem reducedComponentToReduction_subschemeι (Z : irreducibleComponents X) :
    X.reducedComponentToReduction Z ≫ X.nilradical.subschemeι = X.reducedComponentι Z :=
  (Classical.choose_spec
    (existsUnique_lift_nilradical_subschemeι (X.reducedComponentι Z))).1

/-- The morphism from a reduced irreducible component of `X` to the reduction of `X` is a closed
immersion. -/
instance isClosedImmersion_reducedComponentToReduction (Z : irreducibleComponents X) :
    IsClosedImmersion (X.reducedComponentToReduction Z) := by
  have : IsClosedImmersion (X.reducedComponentToReduction Z ≫ X.nilradical.subschemeι) := by
    rw [X.reducedComponentToReduction_subschemeι Z]; infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ X.nilradical.subschemeι

/-- A point of a reduced irreducible component of `X`, viewed in the reduction of `X` and then
in `X`, lies in that component. -/
theorem subschemeι_reducedComponentToReduction_mem (Z : irreducibleComponents X)
    (w : X.reducedComponent Z) :
    X.nilradical.subschemeι (X.reducedComponentToReduction Z w) ∈ (Z : Set X) := by
  rw [← Scheme.Hom.comp_apply, X.reducedComponentToReduction_subschemeι Z]
  exact X.reducedComponentι_mem Z w

/-- A point of the reduction of `X` is a generic point of an irreducible component exactly when
its image in `X` is: the closed immersion of the reduction is a homeomorphism. -/
theorem mem_genericPoints_subschemeι_nilradical_iff {x : X.nilradical.subscheme} :
    X.nilradical.subschemeι x ∈ genericPoints X ↔
      x ∈ genericPoints X.nilradical.subscheme := by
  refine ⟨fun h ↦ ?_, mem_genericPoints_subschemeι_nilradical X⟩
  have hx : X.homeomorphNilradicalSubscheme x ∈ genericPoints X := h
  simpa using mem_genericPoints_of_generalizingMap
    X.homeomorphNilradicalSubscheme.symm.isOpenEmbedding.generalizingMap hx

/-! ### Local finiteness of the family of irreducible components -/

/-- Only finitely many irreducible components of `X` meet an open set that has finitely many
irreducible components: the trace of a component on the open set is an irreducible component of
it, and distinct components leave distinct traces. -/
theorem finite_setOf_irreducibleComponents_inter_nonempty {V : Set X} (hV : IsOpen V)
    (hfin : (irreducibleComponents V).Finite) :
    {Z : irreducibleComponents X | ((Z : Set X) ∩ V).Nonempty}.Finite := by
  classical
  have : Finite (irreducibleComponents V) := hfin.to_subtype
  have htrace (Z : {Z : irreducibleComponents X | ((Z : Set X) ∩ V).Nonempty}) :
      (Subtype.val ⁻¹' (Z.1 : Set X) : Set V) ∈ irreducibleComponents V := by
    refine preimage_mem_irreducibleComponents Z.1.2 hV.isOpenEmbedding_subtypeVal ?_
    obtain ⟨x, hxZ, hxV⟩ := Z.2
    exact ⟨x, hxZ, ⟨x, hxV⟩, rfl⟩
  have hinj : Function.Injective fun Z : {Z : irreducibleComponents X |
      ((Z : Set X) ∩ V).Nonempty} ↦ (⟨Subtype.val ⁻¹' (Z.1 : Set X), htrace Z⟩ :
        irreducibleComponents V) := by
    intro Z W h
    have himg : (Z.1 : Set X) ∩ V = (W.1 : Set X) ∩ V := by
      have := congrArg (fun S : irreducibleComponents V ↦ Subtype.val '' (S : Set V)) h
      simpa [Set.image_preimage_eq_inter_range] using this
    have key (A B : irreducibleComponents X) (hAV : ((A : Set X) ∩ V).Nonempty)
        (hEq : (A : Set X) ∩ V = (B : Set X) ∩ V) : (A : Set X) ⊆ (B : Set X) := by
      refine (subset_closure_inter_of_isPreirreducible_of_isOpen A.2.1.2 hV hAV).trans ?_
      rw [hEq]
      exact closure_minimal Set.inter_subset_left
        (isClosed_of_mem_irreducibleComponents B.1 B.2)
    exact Subtype.ext (Subtype.ext (Set.Subset.antisymm (key Z.1 W.1 Z.2 himg)
      (key W.1 Z.1 (himg ▸ Z.2) himg.symm)))
  have : Finite {Z : irreducibleComponents X | ((Z : Set X) ∩ V).Nonempty} :=
    Finite.of_injective _ hinj
  exact Set.toFinite _

/-! ### The coproduct of the reduced irreducible components -/

/-- The canonical morphism to the reduction of `X` from the coproduct of the reduced irreducible
components of `X`. -/
def reducedComponentsToReduction :
    (∐ fun Z : irreducibleComponents X ↦ X.reducedComponent Z) ⟶ X.nilradical.subscheme :=
  Sigma.desc X.reducedComponentToReduction

/-- The value at a point of a summand of the morphism to the reduction of `X` from the coproduct
of the reduced irreducible components. -/
@[simp]
theorem reducedComponentsToReduction_sigmaι (Z : irreducibleComponents X)
    (w : X.reducedComponent Z) :
    X.reducedComponentsToReduction
        (Sigma.ι (fun Z : irreducibleComponents X ↦ X.reducedComponent Z) Z w) =
      X.reducedComponentToReduction Z w := by
  rw [← Scheme.Hom.comp_apply, reducedComponentsToReduction, Sigma.ι_desc]

/-- The generic point of a reduced irreducible component of `X`, read in the reduction of `X` and
then in `X`, is the generic point of that component of `X`. -/
theorem isGenericPoint_reducedComponentToReduction (Z : irreducibleComponents X) :
    IsGenericPoint (X.nilradical.subschemeι
        (X.reducedComponentToReduction Z (genericPoint (X.reducedComponent Z))))
      (Z : Set X) := by
  rw [← Scheme.Hom.comp_apply, X.reducedComponentToReduction_subschemeι Z]
  exact X.isGenericPoint_reducedComponentι Z

/-- The generic point of a reduced irreducible component of `X` is a generic point of an
irreducible component of the reduction of `X`. -/
theorem mem_genericPoints_reducedComponentToReduction (Z : irreducibleComponents X) :
    X.reducedComponentToReduction Z (genericPoint (X.reducedComponent Z)) ∈
      genericPoints X.nilradical.subscheme := by
  have h : closure {X.nilradical.subschemeι (X.reducedComponentToReduction Z
      (genericPoint (X.reducedComponent Z)))} ∈ irreducibleComponents X := by
    rw [X.isGenericPoint_reducedComponentToReduction Z]
    exact Z.2
  exact X.mem_genericPoints_subschemeι_nilradical_iff.1 h

/-- The generic point of a summand is a generic point of an irreducible component of the
coproduct of the reduced irreducible components of `X`. -/
theorem mem_genericPoints_sigmaι_genericPoint (Z : irreducibleComponents X) :
    Sigma.ι (fun Z : irreducibleComponents X ↦ X.reducedComponent Z) Z
        (genericPoint (X.reducedComponent Z)) ∈
      genericPoints (∐ fun Z : irreducibleComponents X ↦ X.reducedComponent Z : Scheme.{u}) :=
  (mem_genericPoints_sigmaι_iff _ Z _).2
    (by rw [genericPoints_eq_singleton]; exact Set.mem_singleton _)

/-- Every generic point of an irreducible component of the coproduct of the reduced irreducible
components of `X` is the generic point of one of the summands. -/
theorem exists_eq_sigmaι_genericPoint
    {s : (∐ fun Z : irreducibleComponents X ↦ X.reducedComponent Z : Scheme.{u})}
    (hs : s ∈ genericPoints
      (∐ fun Z : irreducibleComponents X ↦ X.reducedComponent Z : Scheme.{u})) :
    ∃ Z : irreducibleComponents X,
      Sigma.ι (fun Z : irreducibleComponents X ↦ X.reducedComponent Z) Z
        (genericPoint (X.reducedComponent Z)) = s := by
  obtain ⟨Z, w, rfl⟩ := exists_sigmaι_eq _ s
  refine ⟨Z, ?_⟩
  have hw : w ∈ genericPoints (X.reducedComponent Z) :=
    (mem_genericPoints_sigmaι_iff _ Z w).1 hs
  rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hw
  rw [hw]

/-- **The coproduct of the reduced irreducible components of `X` is birational over the reduction
of `X`.** Its generic points are the generic points of the components, which the morphism matches
bijectively with the generic points of the reduction, and at such a point both local rings are
the residue field there: the one on the reduction because the reduction is reduced, and the
closed immersion of the component is surjective on stalks. -/
theorem isBirational_reducedComponentsToReduction :
    IsBirational X.reducedComponentsToReduction := by
  have hRred : IsReduced X.nilradical.subscheme := by
    simpa only [IdealSheafData.vanishingIdeal_top] using
      IdealSheafData.isReduced_subscheme_vanishingIdeal (X := X) ⊤
  have hinj : Function.Injective X.nilradical.subschemeι :=
    X.nilradical.subschemeι.isClosedEmbedding.injective
  refine isBirational_of_bijOn_of_isIso_stalkMap _ ⟨?_, ?_, ?_⟩ ?_
  · intro s hs
    obtain ⟨Z, rfl⟩ := X.exists_eq_sigmaι_genericPoint hs
    rw [X.reducedComponentsToReduction_sigmaι]
    exact X.mem_genericPoints_reducedComponentToReduction Z
  · intro s hs t ht hst
    obtain ⟨Z, rfl⟩ := X.exists_eq_sigmaι_genericPoint hs
    obtain ⟨Z', rfl⟩ := X.exists_eq_sigmaι_genericPoint ht
    rw [X.reducedComponentsToReduction_sigmaι, X.reducedComponentsToReduction_sigmaι] at hst
    have hZ : (Z : Set X) = (Z' : Set X) := by
      rw [← X.isGenericPoint_reducedComponentToReduction Z,
        ← X.isGenericPoint_reducedComponentToReduction Z', hst]
    obtain rfl : Z = Z' := Subtype.ext hZ
    rfl
  · intro η hη
    have hpη : X.nilradical.subschemeι η ∈ genericPoints X :=
      X.mem_genericPoints_subschemeι_nilradical_iff.2 hη
    set Z : irreducibleComponents X :=
      genericPoints.component ⟨X.nilradical.subschemeι η, hpη⟩ with hZdef
    refine ⟨Sigma.ι (fun Z : irreducibleComponents X ↦ X.reducedComponent Z) Z
      (genericPoint (X.reducedComponent Z)),
      X.mem_genericPoints_sigmaι_genericPoint Z, ?_⟩
    rw [X.reducedComponentsToReduction_sigmaι]
    refine hinj ((X.isGenericPoint_reducedComponentToReduction Z).eq ?_)
    exact genericPoints.isGenericPoint ⟨X.nilradical.subschemeι η, hpη⟩
  · intro s hs
    obtain ⟨Z, rfl⟩ := X.exists_eq_sigmaι_genericPoint hs
    have hmem : closure {X.reducedComponentToReduction Z
        (genericPoint (X.reducedComponent Z))} ∈
          irreducibleComponents X.nilradical.subscheme :=
      X.mem_genericPoints_reducedComponentToReduction Z
    have hfield : IsField (X.nilradical.subscheme.presheaf.stalk
        (X.reducedComponentToReduction Z (genericPoint (X.reducedComponent Z)))) :=
      isField_stalk_of_closure_mem_irreducibleComponents _ _ hmem
    let : Field (X.nilradical.subscheme.presheaf.stalk
      (X.reducedComponentToReduction Z (genericPoint (X.reducedComponent Z)))) := hfield.toField
    have hiso : IsIso ((X.reducedComponentToReduction Z).stalkMap
        (genericPoint (X.reducedComponent Z))) := by
      refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨RingHom.injective _, ?_⟩
      exact SurjectiveOnStalks.stalkMap_surjective (X.reducedComponentToReduction Z) _
    have hopen : IsIso ((Sigma.ι (fun Z : irreducibleComponents X ↦ X.reducedComponent Z)
        Z).stalkMap (genericPoint (X.reducedComponent Z))) :=
      (IsOpenImmersion.iff_isIso_stalkMap.mp inferInstance).2 _
    have hcongr := Scheme.Hom.stalkMap_congr_hom
      (Sigma.ι (fun Z : irreducibleComponents X ↦ X.reducedComponent Z) Z ≫
        X.reducedComponentsToReduction)
      (X.reducedComponentToReduction Z)
      (Sigma.ι_desc X.reducedComponentToReduction Z)
      (genericPoint (X.reducedComponent Z))
    rw [Scheme.Hom.stalkMap_comp] at hcongr
    have hcomp : IsIso (X.reducedComponentsToReduction.stalkMap
        (Sigma.ι (fun Z : irreducibleComponents X ↦ X.reducedComponent Z) Z
          (genericPoint (X.reducedComponent Z))) ≫
        (Sigma.ι (fun Z : irreducibleComponents X ↦ X.reducedComponent Z) Z).stalkMap
          (genericPoint (X.reducedComponent Z))) := by
      rw [hcongr]
      exact IsIso.comp_isIso' (Iso.isIso_hom _) hiso
    exact IsIso.of_isIso_comp_right _
      ((Sigma.ι (fun Z : irreducibleComponents X ↦ X.reducedComponent Z) Z).stalkMap
        (genericPoint (X.reducedComponent Z)))

/-! ### An integral birational morphism from a normal scheme is the normalization -/

/-- An integral morphism onto `X` from a normal scheme which is birational over every
quasi-compact open of `X` *is* the normalization of `X`.

Tag 035Q part (3) identifies the normalization of `X` with the normalization of the source, and
Tag 0H7D makes the latter's normalization morphism an isomorphism because the source is
normal. -/
@[ega "IV 17.15.14.1" "(i)"]
theorem exists_iso_normalizationScheme_of_isIntegralHom_of_isBirational {X Y : Scheme.{u}}
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (α : Y ⟶ X) [IsIntegralHom α] [IsNormal Y]
    (hcomponents : ∀ U : X.Opens, IsCompact (U : Set X) →
      (irreducibleComponents (α ⁻¹ᵁ U)).Finite)
    (hbirational : ∀ U : X.Opens, IsCompact (U : Set X) → IsBirational (α ∣_ U)) :
    ∃ e : Y ≅ X.normalizationScheme hX, e.hom ≫ X.normalization hX = α := by
  obtain ⟨hY, g, e, hg, he⟩ :=
    exists_normalizationFactorization_of_integral_of_birational hX α hcomponents hbirational
  have hiso : IsIso (Y.normalization hY) :=
    (Y.isIso_normalization_iff_isNormal hY).2 inferInstance
  have hinv : e.inv ≫ X.normalization hX = Y.normalization hY ≫ α := by
    rw [← hg, ← he]; simp
  refine ⟨(asIso (Y.normalization hY)).symm ≪≫ e.symm, ?_⟩
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_inv, Category.assoc, hinv,
    IsIso.inv_hom_id_assoc]

/-! ### The coproduct of the normalizations of the components -/

/-- The normalization morphism of a scheme is integral: it is the structural morphism from a
relative normalization. -/
theorem isIntegralHom_normalization
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    IsIntegralHom (X.normalization hX) := by
  have := quasiCompactFromGenericPointResidueFields X hX
  have := quasiSeparatedFromGenericPointResidueFields X
  exact inferInstanceAs
    (IsIntegralHom (fromGenericPointResidueFields X).fromNormalization)

/-- The coproduct of the normalizations of the reduced irreducible components of `X`. -/
abbrev sigmaNormalizationReducedComponent : Scheme.{u} :=
  ∐ fun Z : irreducibleComponents X ↦ (X.reducedComponent Z).normalizationScheme
    (X.finite_irreducibleComponents_reducedComponent Z)

/-- The canonical morphism to the reduction of `X` from the coproduct of the normalizations of
the reduced irreducible components of `X`. -/
@[sga "3 X 5.14.0"]
def sigmaNormalizationToReduction :
    X.sigmaNormalizationReducedComponent ⟶ X.nilradical.subscheme :=
  Sigma.desc fun Z ↦ (X.reducedComponent Z).normalization
    (X.finite_irreducibleComponents_reducedComponent Z) ≫ X.reducedComponentToReduction Z

/-- The coproduct of the normalizations of the reduced irreducible components of `X` is a normal
scheme. -/
instance isNormal_sigmaNormalizationReducedComponent :
    IsNormal X.sigmaNormalizationReducedComponent :=
  isNormal_sigma _ fun Z ↦ (X.reducedComponent Z).isNormal_normalizationScheme _

/-- The canonical morphism to the reduction of `X` from the coproduct of the normalizations of
the reduced irreducible components is integral: each summand is integral over `X`, and only
finitely many summands meet any affine open of the reduction, because only finitely many
irreducible components of `X` meet a quasi-compact open. -/
theorem isIntegralHom_sigmaNormalizationToReduction
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    IsIntegralHom X.sigmaNormalizationToReduction := by
  have hsummand : ∀ Z : irreducibleComponents X, IsIntegralHom
      ((X.reducedComponent Z).normalization
        (X.finite_irreducibleComponents_reducedComponent Z) ≫
          X.reducedComponentToReduction Z) := by
    intro Z
    have := (X.reducedComponent Z).isIntegralHom_normalization
      (X.finite_irreducibleComponents_reducedComponent Z)
    infer_instance
  refine isIntegralHom_sigmaDesc _ fun U hU ↦ ?_
  have hVopen : IsOpen (X.homeomorphNilradicalSubscheme ''
      (U : Set X.nilradical.subscheme)) :=
    X.homeomorphNilradicalSubscheme.isOpen_image.mpr U.2
  have hVc : IsCompact (X.homeomorphNilradicalSubscheme ''
      (U : Set X.nilradical.subscheme)) :=
    hU.isCompact.image X.homeomorphNilradicalSubscheme.continuous
  refine Set.Finite.subset
    (X.finite_setOf_irreducibleComponents_inter_nonempty hVopen (hX ⟨_, hVopen⟩ hVc)) ?_
  intro Z hZ
  obtain ⟨w, hw⟩ := (Opens.ne_bot_iff_nonempty _).1 hZ
  exact ⟨_, X.subschemeι_reducedComponentToReduction_mem Z _, ⟨_, hw, rfl⟩⟩

/-- The canonical morphism to the reduction of `X` from the coproduct of the normalizations of
the reduced irreducible components is birational: it is the coproduct of the birational
normalization morphisms of the components followed by the birational morphism from the coproduct
of the components themselves. -/
theorem isBirational_sigmaNormalizationToReduction :
    IsBirational X.sigmaNormalizationToReduction := by
  have heq : X.sigmaNormalizationToReduction =
      (Sigma.desc fun Z : irreducibleComponents X ↦
        (X.reducedComponent Z).normalization
          (X.finite_irreducibleComponents_reducedComponent Z) ≫
        Sigma.ι (fun Z : irreducibleComponents X ↦ X.reducedComponent Z) Z) ≫
        X.reducedComponentsToReduction := by
    refine Sigma.hom_ext _ _ fun Z ↦ ?_
    simp [sigmaNormalizationToReduction, reducedComponentsToReduction]
  rw [heq]
  exact IsBirational.comp
    (isBirational_sigmaMap _ fun Z ↦ (X.reducedComponent Z).isBirational_normalization _)
    X.isBirational_reducedComponentsToReduction

/-- **Stacks Project, Tag 0CDV.** Let `X` be a scheme whose quasi-compact opens have finitely
many irreducible components, and give each irreducible component of `X` its reduced induced
closed subscheme structure. Then the coproduct of the normalizations of those components, with
its canonical morphism to `X`, is the normalization of `X`. -/
@[stacks 0CDV]
theorem exists_iso_normalizationScheme_sigma_reducedComponent
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    ∃ e : (∐ fun Z : irreducibleComponents X ↦ (X.reducedComponent Z).normalizationScheme
        (X.finite_irreducibleComponents_reducedComponent Z)) ≅ X.normalizationScheme hX,
      e.hom ≫ X.normalization hX =
        Sigma.desc fun Z : irreducibleComponents X ↦
          (X.reducedComponent Z).normalization
            (X.finite_irreducibleComponents_reducedComponent Z) ≫ X.reducedComponentι Z := by
  have := X.isIntegralHom_sigmaNormalizationToReduction hX
  have hβbir := X.isBirational_sigmaNormalizationToReduction
  have hcomponents : ∀ U : X.nilradical.subscheme.Opens,
      IsCompact (U : Set X.nilradical.subscheme) →
      (irreducibleComponents (X.sigmaNormalizationToReduction ⁻¹ᵁ U)).Finite := by
    intro U hUc
    exact finite_irreducibleComponents_of_isCompact_sigma _ _
      (X.sigmaNormalizationToReduction.isCompact_preimage hUc)
  obtain ⟨e₁, he₁⟩ := exists_iso_normalizationScheme_of_isIntegralHom_of_isBirational
    (X.finite_irreducibleComponents_reduction hX) X.sigmaNormalizationToReduction
    hcomponents fun U _ ↦ hβbir.morphismRestrict U
  obtain ⟨e₂, he₂⟩ := X.exists_normalizationScheme_iso_reduction hX
  have hinv : e₂.inv ≫ X.normalization hX =
      X.nilradical.subscheme.normalization (X.finite_irreducibleComponents_reduction hX) ≫
        X.nilradical.subschemeι := by
    rw [← he₂]; simp
  refine ⟨e₁ ≪≫ e₂.symm, ?_⟩
  rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, hinv, ← Category.assoc, he₁]
  refine Sigma.hom_ext _ _ fun Z ↦ ?_
  simp [sigmaNormalizationToReduction]

/-- **Stacks Project, Tag 035Q.** The normalization of a scheme whose quasi-compact opens have
finitely many irreducible components is a disjoint union of integral normal schemes: it is
isomorphic to the coproduct of the normalizations of its reduced irreducible components, and
each of those is integral and normal. -/
@[stacks 035Q "normalization_disjoint_union_of_integral_normal"]
theorem exists_iso_sigma_isIntegral_isNormal_normalizationScheme
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    ∃ (ι : Type u) (Y : ι → Scheme.{u})
        (_ : ∀ i, IsNormal (Y i)) (_ : ∀ i, IsIntegral (Y i)),
      Nonempty (X.normalizationScheme hX ≅ ∐ Y) := by
  obtain ⟨e, -⟩ := X.exists_iso_normalizationScheme_sigma_reducedComponent hX
  exact ⟨irreducibleComponents X,
    fun Z ↦ (X.reducedComponent Z).normalizationScheme
      (X.finite_irreducibleComponents_reducedComponent Z),
    fun Z ↦ (X.reducedComponent Z).isNormal_normalizationScheme _,
    fun _ ↦ inferInstance, ⟨e.symm⟩⟩

end AlgebraicGeometry.Scheme

end
