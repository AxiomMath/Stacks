module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.ResidueFieldMap
public import StacksFrontier.AlgebraicGeometry.Morphisms.ProperComplementExtension
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.CompletelyDecomposed
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Assembling a proper completely decomposed cover by Noetherian induction

Let `S` be a Noetherian scheme and let `P` be a property of morphisms into `S` which holds for
morphisms out of the empty scheme and is inherited by a binary coproduct of two morphisms that
have it. Suppose that over every *integral* closed subscheme `Z ⊆ S` one can find a proper
morphism `g : T ⟶ Z` which has `P` after composing with `Z ⊆ S` and which is an isomorphism
over a dense open of `Z`. Then there is a single proper, **completely decomposed** morphism
`S' ⟶ S` with `P`.

The induction is the one in the Stacks project's proof of
[Tag 0H59](https://stacks.math.columbia.edu/tag/0H59): one runs Noetherian induction over the
closed subsets of `S`, splits a reducible closed subset into two strictly smaller ones and takes
the coproduct of the two covers obtained, and on an irreducible closed subset uses the given
cover over the reduced induced structure, patching the complement of the dense open — a strictly
smaller closed subset — by the induction hypothesis. The morphism produced is only completely
decomposed, not surjective-with-trivial-residue-field-extension on the nose, because that is all
the splitting argument gives; and completely decomposed is exactly what the application needs.

In the Stacks project this bookkeeping is interleaved with the cycle-theoretic content of
Tag 0H59 (generic flatness, flattening by a blowing up, and uniqueness of extensions of relative
cycles). Here it is isolated, so that `P` may be instantiated later with "the pullback of the
given relative cycle lies in the image of the cycle class map of Tag 0H58" once the inputs of
the integral case are available. See the implementation notes for what those are.

## Main results

* `AlgebraicGeometry.IsCompletelyDecomposed.surjective`: a completely decomposed morphism is
  surjective.
* `AlgebraicGeometry.isCompletelyDecomposed_coprod_desc`: a binary coproduct of two morphisms to
  a common target is completely decomposed as soon as every point of the target is covered with
  trivial residue field extension by one of the two.
* `AlgebraicGeometry.exists_isIso_residueFieldMap_of_isIso_morphismRestrict`: a point lying in an
  open over which a morphism is an isomorphism lifts to a point with trivial residue field
  extension.
* `AlgebraicGeometry.isIso_residueFieldMap_of_mem_isIso_morphismRestrict`: the same for a point
  of the source whose image lies in such an open.
* `AlgebraicGeometry.genericPoint_image_of_isIso_morphismRestrict`: a morphism of irreducible
  schemes which is an isomorphism over a dense open carries the generic point to the generic
  point.
* `AlgebraicGeometry.isNoetherian_source_of_isProper`: the source of a proper morphism with
  Noetherian target is Noetherian.
* `AlgebraicGeometry.exists_isProper_isCompletelyDecomposed_of_integral_case`: the statement
  described above.

## Implementation notes

Completely decomposed is `AlgebraicGeometry.IsCompletelyDecomposed`: every point of the target
is the image of a point at which the residue field map is an isomorphism. It is not a morphism
property in the `MorphismProperty` sense here, so the coproduct step is proved by hand from the
two injections, which are open immersions and therefore induce isomorphisms on residue fields.

Closed subsets of `S` are indexed by `TopologicalSpace.Closeds S`, which is well-founded for the
reverse order on a Noetherian space, and the reduced induced closed subscheme structure on such a
subset is the subscheme cut out by its vanishing ideal sheaf
(`AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal`). The induction hypothesis is therefore
indexed by closed subsets of `S` rather than by closed subschemes, and the integral case receives
an ideal sheaf whose subscheme happens to be integral rather than a closed subset.

The integral case of Tag 0H59 is not proved here: it asks, for `S` integral with function field
`K` and `α` a relative `r`-cycle on `X/S`, for a `U`-admissible blowing up of `S` after which the
closures of the components of `α_K` become flat, and it is
`Stacks.Chow.exists_isProper_pullbackInCycleClassImage_of_isIntegral`, in
`StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.CycleClassProperCover`, where Tag 0H59 is
assembled.

## References

* [Stacks Project, Tag 0H59](https://stacks.math.columbia.edu/tag/0H59)
* [Stacks Project, Tag 0GTI](https://stacks.math.columbia.edu/tag/0GTI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Completely decomposed morphisms are surjective -/

/-- A completely decomposed morphism is surjective on points: by definition every point of the
target is the image of a point of the source, the condition on residue fields being extra. -/
theorem IsCompletelyDecomposed.surjective {X Y : Scheme.{u}} {f : X ⟶ Y}
    (hf : IsCompletelyDecomposed f) : Function.Surjective f :=
  fun y => (hf y).imp fun _ h => h.1

/-- A completely decomposed morphism is surjective, as the morphism property. -/
theorem IsCompletelyDecomposed.toSurjective {X Y : Scheme.{u}} {f : X ⟶ Y}
    (hf : IsCompletelyDecomposed f) : Surjective f :=
  ⟨hf.surjective⟩

/-! ### Points with trivial residue field extension -/

section ResidueField

variable {X Y S : Scheme.{u}}

/-- Transporting triviality of the residue field extension along an equality of morphisms. -/
private theorem isIso_residueFieldMap_congr {f g : X ⟶ Y} (e : f = g) (x : X)
    (h : IsIso (g.residueFieldMap x)) : IsIso (f.residueFieldMap x) :=
  e ▸ h

/-- Triviality of the residue field extension at a point in the image of an open immersion is
detected after precomposing with that open immersion, because an open immersion induces
isomorphisms on residue fields and these cancel.

The same statement is `AlgebraicGeometry.isIso_residueFieldMap_of_comp_isOpenImmersion`, which
is not used here because its module is about seminormalization and nothing else in it is
needed. -/
private theorem isIso_residueFieldMap_cancel_isOpenImmersion
    (j : X ⟶ Y) [IsOpenImmersion j] (f : Y ⟶ S) (x : X)
    (h : IsIso ((j ≫ f).residueFieldMap x)) : IsIso (f.residueFieldMap (j x)) := by
  rw [Scheme.residueFieldMap_comp] at h
  have hcomp : IsIso (f.residueFieldMap (j x) ≫ j.residueFieldMap x) := h
  exact IsIso.of_isIso_comp_right (f.residueFieldMap (j x)) (j.residueFieldMap x)

/-- A point of the preimage of an open over which a morphism restricts to an isomorphism has
trivial residue field extension. -/
private theorem isIso_residueFieldMap_preimage_ι (f : X ⟶ S) (U : S.Opens) [IsIso (f ∣_ U)]
    (y : (f ⁻¹ᵁ U).toScheme) : IsIso (f.residueFieldMap ((f ⁻¹ᵁ U).ι y)) := by
  refine isIso_residueFieldMap_cancel_isOpenImmersion (f ⁻¹ᵁ U).ι f y ?_
  rw [← morphismRestrict_ι, Scheme.residueFieldMap_comp]
  exact IsIso.comp_isIso'
    (inferInstance : IsIso (U.ι.residueFieldMap ((f ∣_ U) y)))
    (inferInstance : IsIso ((f ∣_ U).residueFieldMap y))

/-- A point of the target lying in an open over which a morphism restricts to an isomorphism
lifts to a point with trivial residue field extension. -/
theorem exists_isIso_residueFieldMap_of_isIso_morphismRestrict
    (f : X ⟶ S) (U : S.Opens) [IsIso (f ∣_ U)] (s : S) (hs : s ∈ U) :
    ∃ x : X, f x = s ∧ IsIso (f.residueFieldMap x) := by
  let x := inv (f ∣_ U) (⟨s, hs⟩ : U)
  have hxy : (f ∣_ U) x = (⟨s, hs⟩ : U) := by
    show (inv (f ∣_ U) ≫ f ∣_ U) _ = _
    rw [IsIso.inv_hom_id]
    rfl
  refine ⟨(f ⁻¹ᵁ U).ι x, ?_, ?_⟩
  · show ((f ⁻¹ᵁ U).ι ≫ f) x = s
    rw [← morphismRestrict_ι]
    show U.ι ((f ∣_ U) x) = s
    rw [hxy]
    rfl
  · exact isIso_residueFieldMap_preimage_ι f U x

/-- A point whose image lies in an open over which a morphism restricts to an isomorphism has
trivial residue field extension. -/
theorem isIso_residueFieldMap_of_mem_isIso_morphismRestrict
    (f : X ⟶ S) (U : S.Opens) [IsIso (f ∣_ U)] (x : X) (hx : f x ∈ U) :
    IsIso (f.residueFieldMap x) := by
  exact isIso_residueFieldMap_preimage_ι f U (⟨x, hx⟩ : (f ⁻¹ᵁ U).toScheme)

end ResidueField

/-! ### Completely decomposed morphisms out of a binary coproduct -/

section Coprod

variable {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- A point of the target covered with trivial residue field extension by one of two morphisms
is covered with trivial residue field extension by the morphism out of their coproduct. -/
theorem exists_isIso_residueFieldMap_coprod_desc (s : S)
    (h : (∃ x : X, f x = s ∧ IsIso (f.residueFieldMap x)) ∨
      ∃ y : Y, g y = s ∧ IsIso (g.residueFieldMap y)) :
    ∃ z : (X ⨿ Y : Scheme.{u}), coprod.desc f g z = s ∧
      IsIso ((coprod.desc f g).residueFieldMap z) := by
  rcases h with ⟨x, hx, hi⟩ | ⟨y, hy, hi⟩
  · refine ⟨(coprod.inl : X ⟶ X ⨿ Y) x, ?_, ?_⟩
    · show (coprod.inl ≫ coprod.desc f g) x = s
      simpa only [coprod.inl_desc] using hx
    · exact isIso_residueFieldMap_cancel_isOpenImmersion coprod.inl (coprod.desc f g) x
        (isIso_residueFieldMap_congr (coprod.inl_desc f g) x hi)
  · refine ⟨(coprod.inr : Y ⟶ X ⨿ Y) y, ?_, ?_⟩
    · show (coprod.inr ≫ coprod.desc f g) y = s
      simpa only [coprod.inr_desc] using hy
    · exact isIso_residueFieldMap_cancel_isOpenImmersion coprod.inr (coprod.desc f g) y
        (isIso_residueFieldMap_congr (coprod.inr_desc f g) y hi)

/-- The morphism out of a binary coproduct determined by two morphisms to a common target is
completely decomposed as soon as every point of the target is covered with trivial residue field
extension by one of the two. -/
theorem isCompletelyDecomposed_coprod_desc
    (h : ∀ s : S, (∃ x : X, f x = s ∧ IsIso (f.residueFieldMap x)) ∨
      ∃ y : Y, g y = s ∧ IsIso (g.residueFieldMap y)) :
    IsCompletelyDecomposed (coprod.desc f g) :=
  fun s => exists_isIso_residueFieldMap_coprod_desc f g s (h s)

/-- A morphism which is an isomorphism over an open `U` together with a morphism covering the
complement of `U` with trivial residue field extensions describe a completely decomposed
morphism out of the coproduct. -/
theorem isCompletelyDecomposed_coprod_desc_of_isIso_morphismRestrict (U : S.Opens)
    [IsIso (f ∣_ U)]
    (h : ∀ s : S, s ∉ U → ∃ y : Y, g y = s ∧ IsIso (g.residueFieldMap y)) :
    IsCompletelyDecomposed (coprod.desc f g) := by
  refine isCompletelyDecomposed_coprod_desc f g fun s => ?_
  by_cases hs : s ∈ U
  · exact Or.inl (exists_isIso_residueFieldMap_of_isIso_morphismRestrict f U s hs)
  · exact Or.inr (h s hs)

end Coprod

/-! ### Generic points -/

section GenericPoint

variable {X S : Scheme.{u}} [IrreducibleSpace X] (g : X ⟶ S) (U : S.Opens) [IsIso (g ∣_ U)]

/-- If a morphism from an irreducible scheme is an isomorphism over a nonempty open `U`, then
the image of the generic point lies in `U`. -/
theorem genericPoint_mem_of_isIso_morphismRestrict (hU : (U : Set S).Nonempty) :
    g (genericPoint X) ∈ U := by
  obtain ⟨s, hs⟩ := hU
  obtain ⟨x, hx, -⟩ := exists_isIso_residueFieldMap_of_isIso_morphismRestrict g U s hs
  have hn : ((g ⁻¹ᵁ U : X.Opens) : Set X).Nonempty := ⟨x, show g x ∈ U from hx ▸ hs⟩
  exact ((genericPoint_spec X).mem_open_set_iff (g ⁻¹ᵁ U).isOpen).2
    (by simpa only [Set.univ_inter] using hn)

/-- A morphism of irreducible schemes which is an isomorphism over a dense open carries the
generic point to the generic point. -/
theorem genericPoint_image_of_isIso_morphismRestrict [IrreducibleSpace S]
    (hU : Dense (U : Set S)) : g (genericPoint X) = genericPoint S := by
  have hrange : (U : Set S) ⊆ Set.range g := fun s hs =>
    (exists_isIso_residueFieldMap_of_isIso_morphismRestrict g U s hs).imp fun _ h => h.1
  have hg := (genericPoint_spec X).image g.continuous
  rw [Set.image_univ, (hU.mono hrange).closure_eq] at hg
  exact hg.eq (genericPoint_spec S)

end GenericPoint

/-! ### Noetherian induction -/

/-- The source of a proper morphism with Noetherian target is Noetherian. -/
theorem isNoetherian_source_of_isProper {T S : Scheme.{u}} [IsNoetherian S]
    (g : T ⟶ S) [IsProper g] : IsNoetherian T :=
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian g
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace g
  ⟨⟩

/-- Noetherian induction over the closed subsets of a Noetherian space in which the inductive
step only has to be taken on *irreducible* closed subsets, the empty set and unions of two
closed subsets being handled separately. A reducible nonempty closed subset is the union of two
strictly smaller closed subsets. -/
@[ega "0 2.2.2" "special case"]
private theorem closeds_induction_on_irreducible {T : Type u} [TopologicalSpace T]
    [NoetherianSpace T] (P : Closeds T → Prop) (empty : P ⊥)
    (union : ∀ C D, P C → P D → P (C ⊔ D))
    (irreducible : ∀ C : Closeds T, IsIrreducible (C : Set T) →
      (∀ D : Closeds T, D < C → P D) → P C) : ∀ C, P C := by
  intro C
  induction C using WellFoundedLT.induction with
  | ind C ih =>
    by_cases hC : C = ⊥
    · exact hC ▸ empty
    have hn : (C : Set T).Nonempty :=
      Set.nonempty_iff_ne_empty.2 fun h => hC (SetLike.coe_injective h)
    by_cases hirr : IsPreirreducible (C : Set T)
    · exact irreducible C ⟨hn, hirr⟩ ih
    rw [isPreirreducible_iff_isClosed_union_isClosed] at hirr
    push Not at hirr
    obtain ⟨A, B, hA, hB, hcov, hnA, hnB⟩ := hirr
    let D : Closeds T := ⟨(C : Set T) ∩ A, C.isClosed.inter hA⟩
    let E : Closeds T := ⟨(C : Set T) ∩ B, C.isClosed.inter hB⟩
    have hD : D < C :=
      lt_of_le_not_ge Set.inter_subset_left fun h => hnA fun x hx => (h hx).2
    have hE : E < C :=
      lt_of_le_not_ge Set.inter_subset_left fun h => hnB fun x hx => (h hx).2
    have he : D ⊔ E = C := by
      refine SetLike.coe_injective ?_
      show (C : Set T) ∩ A ∪ (C : Set T) ∩ B = C
      rw [← Set.inter_union_distrib_left, Set.inter_eq_left.mpr hcov]
    exact he ▸ union D E (ih D hD) (ih E hE)

/-- **The Noetherian induction in the proof of Stacks Project, Lemma 0H59.** Let `S` be a
Noetherian scheme and let `P` be a property of morphisms into `S` which holds for morphisms out
of the empty scheme and is inherited by binary coproducts. Assume that for every closed
subscheme `Z ⊆ S` cut out by an ideal sheaf and *integral* there is a proper morphism
`g : T ⟶ Z` such that `g` composed with `Z ⊆ S` has `P` and such that `g` is an isomorphism over
a dense open of `Z`. Then there is a proper, completely decomposed morphism `S' ⟶ S` with `P`.

This is the first, second and last paragraphs of the source's proof, with the third paragraph —
the integral case, which in the source is generic flatness followed by flattening along a
blowing up — taken as the hypothesis `hintegral`. The source does the induction over closed
subschemes of `S`; here it runs over closed subsets, each equipped with its reduced induced
structure, which is what makes the integral case available.

The two reductions in the source are: a closed subset that is not irreducible splits into two
strictly smaller closed subsets, and the covers obtained over the two pieces are glued by taking
their coproduct, which is still proper; and over an irreducible closed subset the hypothesis
gives a cover which is an isomorphism over a dense open, so that only the complement of that
open — again a strictly smaller closed subset — is left to the induction hypothesis. -/
theorem exists_isProper_isCompletelyDecomposed_of_integral_case {S : Scheme.{u}} [IsNoetherian S]
    (P : ∀ {T : Scheme.{u}}, (T ⟶ S) → Prop)
    (hempty : ∀ {T : Scheme.{u}} (g : T ⟶ S), IsEmpty T → P g)
    (hcoprod : ∀ {T₁ T₂ : Scheme.{u}} (g₁ : T₁ ⟶ S) (g₂ : T₂ ⟶ S), P g₁ → P g₂ →
      P (coprod.desc g₁ g₂))
    (hintegral : ∀ I : S.IdealSheafData, IsIntegral I.subscheme →
      ∃ (T : Scheme.{u}) (g : T ⟶ I.subscheme), IsProper g ∧ P (g ≫ I.subschemeι) ∧
        ∃ U : I.subscheme.Opens, Dense (U : Set I.subscheme) ∧ IsIso (g ∣_ U)) :
    ∃ (T : Scheme.{u}) (g : T ⟶ S),
      IsProper g ∧ P g ∧ IsCompletelyDecomposed g := by
  classical
  -- The statement being proved by induction over the closed subsets of `S`: a proper morphism
  -- with `P` whose points with trivial residue field extension cover the closed subset.
  let Q (C : Closeds S) : Prop :=
    ∃ (T : Scheme.{u}) (g : T ⟶ S), IsProper g ∧ P g ∧
      ∀ s ∈ C, ∃ t : T, g t = s ∧ IsIso (g.residueFieldMap t)
  have hQ : ∀ C, Q C := by
    refine closeds_induction_on_irreducible Q ?_ ?_ ?_
    · -- The empty closed subset: the empty closed subscheme of `S` will do.
      exact ⟨(⊤ : S.IdealSheafData).subscheme, (⊤ : S.IdealSheafData).subschemeι,
        inferInstance, hempty _ ((Scheme.Hom.ker_eq_top_iff_isEmpty _).mp
          (⊤ : S.IdealSheafData).ker_subschemeι), fun s hs => False.elim hs⟩
    · -- A union: take the coproduct of the two covers.
      rintro C D ⟨T₁, g₁, hp₁, hP₁, hc₁⟩ ⟨T₂, g₂, hp₂, hP₂, hc₂⟩
      have := hp₁
      have := hp₂
      exact ⟨T₁ ⨿ T₂, coprod.desc g₁ g₂, isProper_coprodDesc g₁ g₂, hcoprod _ _ hP₁ hP₂,
        fun s hs => exists_isIso_residueFieldMap_coprod_desc g₁ g₂ s (hs.imp (hc₁ s) (hc₂ s))⟩
    · -- An irreducible closed subset: use the integral case over its reduced induced structure
      -- and the induction hypothesis on the complement of the dense open.
      intro C hC ih
      let I := Scheme.IdealSheafData.vanishingIdeal C
      have hrange : Set.range I.subschemeι = (C : Set S) :=
        Scheme.IdealSheafData.range_subschemeι_vanishingIdeal C
      have : IrreducibleSpace I.subscheme :=
        Scheme.IdealSheafData.irreducibleSpace_subscheme S I (hrange ▸ hC)
      obtain ⟨T, g, hp, hP, U, hU, hUiso⟩ :=
        hintegral I (isIntegral_of_irreducibleSpace_of_isReduced _)
      have := hp
      have := hUiso
      -- The image of the complement of `U` is a strictly smaller closed subset of `S`.
      let D : Closeds S := ⟨I.subschemeι '' (U : Set I.subscheme)ᶜ,
        I.subschemeι.isClosedEmbedding.isClosedMap _ U.isOpen.isClosed_compl⟩
      have hmem : ∀ t : I.subscheme, I.subschemeι t ∈ C := fun t => by
        show I.subschemeι t ∈ (C : Set S)
        rw [← hrange]
        exact ⟨t, rfl⟩
      have hDC : D < C := by
        refine lt_of_le_not_ge (fun s hs => ?_) fun h => ?_
        · obtain ⟨t, -, rfl⟩ := hs
          exact hmem t
        · obtain ⟨t, ht⟩ := hU.nonempty
          obtain ⟨t', ht', he⟩ := h (hmem t)
          exact ht' ((I.subschemeι.isClosedEmbedding.injective he).symm ▸ ht)
      obtain ⟨T', g', hp', hP', hc'⟩ := ih D hDC
      have := hp'
      refine ⟨T ⨿ T', coprod.desc (g ≫ I.subschemeι) g', isProper_coprodDesc _ _,
        hcoprod _ _ hP hP', fun s hs => ?_⟩
      obtain ⟨t, rfl⟩ : s ∈ Set.range I.subschemeι := hrange ▸ hs
      refine exists_isIso_residueFieldMap_coprod_desc (g ≫ I.subschemeι) g' _ ?_
      by_cases ht : t ∈ U
      · obtain ⟨z, hz, hzg⟩ := exists_isIso_residueFieldMap_of_isIso_morphismRestrict g U t ht
        refine Or.inl ⟨z, congrArg I.subschemeι hz, ?_⟩
        rw [Scheme.residueFieldMap_comp]
        exact IsIso.comp_isIso'
          (isIso_residueFieldMap_of_isPreimmersion I.subschemeι _) hzg
      · exact Or.inr (hc' _ ⟨t, ht, rfl⟩)
  obtain ⟨T, g, hp, hP, hc⟩ := hQ ⊤
  exact ⟨T, g, hp, hP, fun s => hc s (Set.mem_univ s)⟩

end AlgebraicGeometry

end
