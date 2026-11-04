module

public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleBasics.NormalCrossings.FibrePowerBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleBasics.NormalCrossings.FibrePowerDecomposition
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleBasics.NormalCrossings.StrictNormalization

/-!
# The distinct locus of a strict normal crossings divisor is covered by component intersections

Let `D` be a strict normal crossings divisor on a locally Noetherian scheme `X`, let
`ν : D^ν ⟶ D` be the normalization of the closed subscheme cut out by `D`, and let
`Z_{n+1} ⊆ D^ν ×_D ⋯ ×_D D^ν` be the complement of the fat diagonal in the `(n + 1)`-fold fibre
power. This file shows that `Z_{n+1}` is covered by opens, each of which is isomorphic over `X`
to the scheme-theoretic intersection of `n + 1` distinct irreducible components of `D`.

## Main definitions

* `AlgebraicGeometry.openImmersionPreimageIsoOfSubsetRange`: an open immersion restricts to an
  isomorphism from the preimage of an open contained in its range onto that open.

## Main results

* `AlgebraicGeometry.exists_tupleOpens_cover_fibrePowerDistinctOpens`: the general statement. If
  `ν₀ : Y ⟶ S` is covered by opens that map to `T` by closed immersions with pairwise disjoint
  ranges, and `S ⟶ T` is a monomorphism, then the complement of the fat diagonal in the
  `(n + 1)`-fold fibre power of `ν₀` is covered by opens indexed by injective tuples, the one
  indexed by `t` being isomorphic over `T` to the closed subscheme cut out by `⨆ k, I (t k)`.
* `Stacks.Divisors.iSup_componentIdeal_eq_componentIntersection_image`: the supremum of the
  component ideals along a tuple is the component intersection along the image of the tuple.
* `Stacks.Divisors.exists_componentIntersection_cover_normalizationDistinct`: the statement for a
  strict normal crossings divisor.

## Implementation notes

The fibre power of `ν₀` is taken over `S`, while the ideal sheaves cutting out the components live
on the ambient scheme `T`. The two are matched by
`AlgebraicGeometry.fibrePowerMonoIso`, which identifies the fibre powers of `ν₀` and of `ν₀ ≫ m`
when `m` is a monomorphism, and by
`AlgebraicGeometry.fibrePowerDistinctLocus_mono`, which says that identification carries one fat
diagonal to the other. Everything else is the decomposition of the fibre power of `ν₀ ≫ m` into
tuple opens supplied by
`AlgebraicGeometry.exists_iso_fibrePowerTupleOpens`, transported along that identification.

The transport uses only one geometric fact,
`AlgebraicGeometry.openImmersionPreimageIsoOfSubsetRange`: an open immersion restricts to an
isomorphism onto any open contained in its range. It is applied twice, once for the identification
of the fat diagonal complements and once for the identification of a tuple open with its preimage.

The index type of the cover is the type of injective tuples rather than the type of all tuples,
because a non-injective tuple indexes an open that misses the fat diagonal complement entirely,
and because the statement asks for intersections of `n + 1` *distinct* components.

## References

* [Stacks Project, Tag 0CBR](https://stacks.math.columbia.edu/tag/0CBR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

/-- An open immersion `f : X ⟶ Y` restricts to an isomorphism from the preimage of an open `U` of
`Y` onto `U`, provided `U` is contained in the range of `f`. -/
public noncomputable def openImmersionPreimageIsoOfSubsetRange {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (U : Y.Opens) (hU : (U : Set Y) ⊆ Set.range f.base) :
    (f ⁻¹ᵁ U).toScheme ≅ U.toScheme :=
  IsOpenImmersion.isoOfRangeEq ((f ⁻¹ᵁ U).ι ≫ f) U.ι (by
    dsimp
    rw [Set.range_comp, Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    exact Set.image_preimage_eq_inter_range.trans (Set.inter_eq_self_of_subset_left hU))

/-- The restriction of an open immersion to the preimage of an open contained in its range is
compatible with the two inclusions. -/
@[reassoc]
public theorem openImmersionPreimageIsoOfSubsetRange_hom_ι {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (U : Y.Opens) (hU : (U : Set Y) ⊆ Set.range f.base) :
    (openImmersionPreimageIsoOfSubsetRange f U hU).hom ≫ U.ι = (f ⁻¹ᵁ U).ι ≫ f :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

section TupleCover

variable {Y S T : Scheme.{u}} (ν₀ : Y ⟶ S) (m : S ⟶ T) [Mono m]
  {ι : Type v} {A : ι → Scheme.{u}} (ε : ∀ i, A i ⟶ Y) [∀ i, IsOpenImmersion (ε i)]

/-- The complement of the fat diagonal in the `(n + 1)`-fold fibre power of `ν₀ : Y ⟶ S` is
covered by opens indexed by the injective `(n + 1)`-tuples of indices, the open indexed by `t`
being isomorphic, compatibly with the morphisms to `T`, to the closed subscheme of `T` cut out by
`⨆ k, I (t k)`.

Here `m : S ⟶ T` is a monomorphism, the family `ε` is an open cover of `Y` with pairwise disjoint
ranges, and `A i` is isomorphic over `T` to the closed subscheme cut out by `I i`. -/
public theorem exists_tupleOpens_cover_fibrePowerDistinctOpens
    [∀ i, IsClosedImmersion (ε i ≫ ν₀ ≫ m)]
    (hcover : ∀ y : Y, ∃ i, y ∈ Set.range (ε i).base)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Set.range (ε i).base) (Set.range (ε j).base))
    (I : ι → T.IdealSheafData)
    (hI : ∀ i, ∃ e : A i ≅ (I i).subscheme, e.hom ≫ (I i).subschemeι = ε i ≫ ν₀ ≫ m)
    (n : ℕ) (U : (fibrePower ν₀ (n + 1)).Opens)
    (hU : (U : Set (fibrePower ν₀ (n + 1))) = fibrePowerDistinctLocus ν₀ (n + 1)) :
    ∃ V : {t : Fin (n + 1) → ι // Function.Injective t} → U.toScheme.Opens,
      iSup V = ⊤ ∧
      ∀ a, ∃ e : (V a).toScheme ≅ (⨆ k, I (a.1 k)).subscheme,
        e.hom ≫ (⨆ k, I (a.1 k)).subschemeι =
          (V a).ι ≫ U.ι ≫ fibrePowerProj ν₀ (n + 1) ≫ m := by
  -- the identification of the fibre power of `ν₀ ≫ m` with that of `ν₀`
  set E := fibrePowerMonoIso ν₀ m n with hE
  -- the fat diagonal complement, pulled back to the fibre power of `ν₀ ≫ m`
  set W : (fibrePower (ν₀ ≫ m) (n + 1)).Opens := E.hom ⁻¹ᵁ U with hW
  have hWset : (W : Set (fibrePower (ν₀ ≫ m) (n + 1)))
      = fibrePowerDistinctLocus (ν₀ ≫ m) (n + 1) := by
    rw [fibrePowerDistinctLocus_mono ν₀ m n, ← hU]
    rfl
  have hsub : (U : Set (fibrePower ν₀ (n + 1))) ⊆ Set.range E.hom.base := by
    exact fun x _ => E.hom.surjective x
  set F := openImmersionPreimageIsoOfSubsetRange E.hom U hsub with hF
  have hFι : F.hom ≫ U.ι = W.ι ≫ E.hom :=
    openImmersionPreimageIsoOfSubsetRange_hom_ι E.hom U hsub
  set G : U.toScheme ⟶ fibrePower (ν₀ ≫ m) (n + 1) := F.inv ≫ W.ι with hG
  have hFinv : Set.range F.inv.base = Set.univ := by
    exact Set.range_eq_univ.2 F.inv.surjective
  have hGrange : Set.range G.base = (W : Set (fibrePower (ν₀ ≫ m) (n + 1))) := by
    rw [hG, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hFinv, Set.image_univ,
      Scheme.Opens.range_ι]
  have hGproj : G ≫ fibrePowerProj (ν₀ ≫ m) (n + 1)
      = U.ι ≫ fibrePowerProj ν₀ (n + 1) ≫ m := by
    rw [hG, ← fibrePowerMonoIso_hom_proj ν₀ m n, ← hE, Category.assoc, ← reassoc_of% hFι]
    simp
  -- the opens of the cover
  have hPsub : ∀ a : {t : Fin (n + 1) → ι // Function.Injective t},
      (fibrePowerTupleOpens (ν₀ ≫ m) ε (n + 1) a.1 :
        Set (fibrePower (ν₀ ≫ m) (n + 1))) ⊆ Set.range G.base := by
    intro a
    rw [hGrange, hWset]
    exact fibrePowerTupleOpens_subset_distinctLocus (ν₀ ≫ m) ε hdisj (n + 1) a.1 a.2
  refine ⟨fun a => G ⁻¹ᵁ fibrePowerTupleOpens (ν₀ ≫ m) ε (n + 1) a.1, ?_, ?_⟩
  · refine TopologicalSpace.Opens.ext ?_
    rw [TopologicalSpace.Opens.coe_top, TopologicalSpace.Opens.coe_iSup, Set.eq_univ_iff_forall]
    intro z
    rw [Set.mem_iUnion]
    have hzW : G.base z ∈ (W : Set (fibrePower (ν₀ ≫ m) (n + 1))) := by
      rw [← hGrange]; exact ⟨z, rfl⟩
    have hzd : G.base z ∈ fibrePowerDistinctLocus (ν₀ ≫ m) (n + 1) := hWset ▸ hzW
    obtain ⟨t, ht⟩ := exists_mem_fibrePowerTupleOpens (ν₀ ≫ m) ε hcover (n + 1) (G.base z)
    exact ⟨⟨t, injective_of_mem_fibrePowerDistinctLocus (ν₀ ≫ m) ε (n + 1) t _ ht hzd⟩, ht⟩
  · intro a
    obtain ⟨e₂, h₂⟩ := exists_iso_fibrePowerTupleOpens (ν₀ ≫ m) ε I hI (n + 1) a.1
    refine ⟨(openImmersionPreimageIsoOfSubsetRange G
      (fibrePowerTupleOpens (ν₀ ≫ m) ε (n + 1) a.1) (hPsub a)).trans e₂, ?_⟩
    rw [Iso.trans_hom, Category.assoc, h₂, ← hGproj,
      ← openImmersionPreimageIsoOfSubsetRange_hom_ι_assoc G
        (fibrePowerTupleOpens (ν₀ ≫ m) ε (n + 1) a.1) (hPsub a)
        (fibrePowerProj (ν₀ ≫ m) (n + 1))]

end TupleCover

end AlgebraicGeometry

namespace Stacks.Divisors

open AlgebraicGeometry

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (D : X.IdealSheafData)

omit [IsLocallyNoetherian X] in
/-- The supremum of the component ideals along a tuple of irreducible components is the
scheme-theoretic intersection of the components in the image of the tuple. -/
public theorem iSup_componentIdeal_eq_componentIntersection_image
    [DecidableEq (irreducibleComponents D.subscheme)] {k : ℕ}
    (t : Fin k → irreducibleComponents D.subscheme) :
    ⨆ i, componentIdeal D (t i) = componentIntersection D (Finset.image t Finset.univ) := by
  simp only [componentIntersection]
  refine le_antisymm (iSup_le fun i => ?_) (iSup₂_le fun C hC => ?_)
  · exact le_iSup₂_of_le (t i) (Finset.mem_image_of_mem t (Finset.mem_univ i)) le_rfl
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hC
    exact le_iSup (fun i => componentIdeal D (t i)) i

/-- **Stacks Project, Tag 0CBR.** For a strict normal crossings divisor the scheme `Z_{n+1}`, the
complement of the fat diagonal in the `(n + 1)`-fold fibre power of the normalization of the
divisor, is covered by open subschemes, each isomorphic over the ambient scheme to the
scheme-theoretic intersection of `n + 1` distinct irreducible components of the divisor. -/
public theorem exists_componentIntersection_cover_normalizationDistinct
    (h : IsStrictNormalCrossingsDivisor D) (n : ℕ) :
    ∃ (ι : Type u) (V : ι → (normalizationDistinct D (n + 1)).Opens),
      iSup V = ⊤ ∧
      ∀ a : ι, ∃ J : Finset (irreducibleComponents D.subscheme), J.card = n + 1 ∧
        ∃ e : (V a).toScheme ≅ (componentIntersection D J).subscheme,
          e.hom ≫ (componentIntersection D J).subschemeι =
            (V a).ι ≫ normalizationDistinctToAmbient D (n + 1) := by
  classical
  obtain ⟨ε, hεopen, hεcomp, hεcover, hεdisj⟩ :=
    exists_componentCover_divisorNormalization_of_isStrictNormalCrossingsDivisor D h
  have : ∀ C, IsOpenImmersion (ε C) := hεopen
  have : ∀ C, IsClosedImmersion (ε C ≫ divisorNormalization D ≫ D.subschemeι) := by
    intro C
    rw [hεcomp C]
    infer_instance
  obtain ⟨V, hVtop, hV⟩ := exists_tupleOpens_cover_fibrePowerDistinctOpens
    (divisorNormalization D) D.subschemeι ε hεcover hεdisj (componentIdeal D)
    (fun C => ⟨Iso.refl _, by simpa using (hεcomp C).symm⟩) n
    (normalizationDistinctOpens D (n + 1)) rfl
  refine ⟨{t : Fin (n + 1) → irreducibleComponents D.subscheme // Function.Injective t},
    V, hVtop, fun a => ⟨Finset.image a.1 Finset.univ, ?_, ?_⟩⟩
  · simp [Finset.card_image_of_injective _ a.2]
  · rw [← iSup_componentIdeal_eq_componentIntersection_image D a.1]
    exact hV a

end Stacks.Divisors

end
