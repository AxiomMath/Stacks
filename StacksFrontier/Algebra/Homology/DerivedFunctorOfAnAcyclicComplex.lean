module

public import StacksFrontier.Algebra.Homology.RightDerivedCoEdgeIso
public import StacksFrontier.Homology.CompositeCollapse
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The derived functor of a complex of acyclic objects with acyclic cohomology

Let `T : D ⥤ E` be an additive, left exact functor between abelian categories, and let
`K : CochainComplex D ℕ` be a cochain complex all of whose terms *and* all of whose cohomology
objects are `T`-acyclic in the sense of `Stacks.RightDerivedComp.acyclic`.  Then the canonical
comparison

  `Hⁿ (T K) ⟶ T (Hⁿ K)`

of `Stacks.Cohomology.RightDerivedCoEdge.homologyToMapHomology` is an isomorphism in every
degree.  This is the degeneration step of the Leray spectral sequence, obtained without any
spectral sequence: for `T = Γ(Y, -)` and `K` an acyclic resolution it says that the cohomology of
the complex of sections computes the sections of the cohomology.

The proof writes `Zⁿ = ker dⁿ` and `Bⁿ = im dⁿ⁻¹` and runs the two short exact sequences

  `0 ⟶ Zⁿ ⟶ Kⁿ ⟶ Bⁿ⁺¹ ⟶ 0`,    `0 ⟶ Bⁿ ⟶ Zⁿ ⟶ Hⁿ ⟶ 0`

alternately through the two-out-of-three property `Stacks.RightDerivedComp.acyclic_shortExact` of
the `T`-acyclic objects.  An `ℕ`-indexed cochain complex has no incoming differential in degree
zero, so `Z⁰ = H⁰` is acyclic to start with; the first sequence then makes `Bⁿ⁺¹` acyclic from
`Zⁿ` and `Kⁿ`, and the second makes `Zⁿ⁺¹` acyclic from `Bⁿ⁺¹` and `Hⁿ⁺¹`.  Acyclicity of `Bⁿ`
is more than vanishing: it also makes `T` keep both sequences short exact, and that exactness is
exactly the statement that `T (Hⁿ K)` is a cokernel of `T (Kⁿ⁻¹) ⟶ T (Zⁿ)`, which is what
invertibility of the comparison amounts to.  Left exactness of `T` enters only through
`Stacks.Cohomology.RightDerivedCoEdge.isIso_mapCycles`, the identification `T (Zⁿ) ≅ Zⁿ (T K)`.

## Main definitions

* `Stacks.Cohomology.RightDerivedCoEdge.boundariesToCycles`: the inclusion `Bʲ ⟶ Zʲ` of the
  boundaries into the cycles, with the boundaries presented as `Kⁱ / Zⁱ`.
* `Stacks.Cohomology.RightDerivedCoEdge.homologyIsoMapHomologyOfAcyclic`: the comparison of the
  main result, as an isomorphism.

## Main results

* `Stacks.Cohomology.RightDerivedCoEdge.shortExact_cycles`,
  `Stacks.Cohomology.RightDerivedCoEdge.shortExact_boundaries`: the two short exact sequences
  `0 ⟶ Zⁱ ⟶ Kⁱ ⟶ Bʲ ⟶ 0` and `0 ⟶ Bʲ ⟶ Zʲ ⟶ Hʲ ⟶ 0`.
* `Stacks.Cohomology.RightDerivedCoEdge.isIso_homologyToMapHomology_of_isColimit`: the comparison
  `Hⁱ (T K) ⟶ T (Hⁱ K)` is invertible as soon as `T` applied to the projection `Zⁱ ⟶ Hⁱ` is a
  cokernel of `T` applied to `Kʲ ⟶ Zⁱ`.
* `Stacks.Cohomology.RightDerivedCoEdge.acyclic_cycles`: the cycles of a complex of acyclic
  objects with acyclic cohomology are acyclic.
* `Stacks.Cohomology.RightDerivedCoEdge.isIso_homologyToMapHomology_of_acyclic`: **a left exact
  functor commutes with the cohomology of a complex of acyclic objects with acyclic cohomology.**

## References

* [Stacks Project, Tag 015D](https://stacks.math.columbia.edu/tag/015D)
* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits Stacks.RightDerivedComp

universe w v₁ v₂ u₁ u₂

namespace Stacks.Cohomology.RightDerivedCoEdge

variable {ι : Type w} {c : ComplexShape ι}
  {D : Type u₁} [Category.{v₁} D] [Abelian D]
  {E : Type u₂} [Category.{v₂} E] [Abelian E]

/-! ### The boundaries of a homological complex -/

section Boundaries

variable (K : HomologicalComplex D c)

/-- The inclusion of the cycles in degree `i` is killed by the comparison `Kⁱ ⟶ Zʲ` of the
differential `dⁱ` with the cycles in degree `j`, because it is killed by `dⁱ` itself. -/
@[reassoc]
lemma iCycles_comp_toCycles (i j : ι) : K.iCycles i ≫ K.toCycles i j = 0 := by
  rw [← cancel_mono (K.iCycles j), Category.assoc, HomologicalComplex.toCycles_i,
    HomologicalComplex.iCycles_d, zero_comp]

/-- **The cycles in degree `i` are the kernel of `Kⁱ ⟶ Zʲ`.**  They are the kernel of `dⁱ`, and
`Zʲ ⟶ Kʲ` is a monomorphism through which `dⁱ` factors. -/
def cyclesIsKernelToCycles (i j : ι) (hij : c.Rel i j) :
    IsLimit (KernelFork.ofι (K.iCycles i) (iCycles_comp_toCycles K i j)) :=
  isKernelOfComp (K.iCycles j) (K.d i j) (K.cyclesIsKernel i j (c.next_eq' hij))
    (iCycles_comp_toCycles K i j) (K.toCycles_i i j)

/-- **The short exact sequence `0 ⟶ Zⁱ ⟶ Kⁱ ⟶ Bʲ ⟶ 0`** presenting the boundaries in degree `j`
as the quotient of `Kⁱ` by the cycles in degree `i`: the inclusion of the cycles is a
monomorphism and the quotient is its cokernel. -/
lemma shortExact_cycles (i : ι) :
    (ShortComplex.mk (K.iCycles i) (cokernel.π (K.iCycles i))
      (cokernel.condition (K.iCycles i))).ShortExact :=
  ⟨ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)⟩

/-- **The inclusion `Bʲ ⟶ Zʲ` of the boundaries into the cycles**, with the boundaries in degree
`j` presented as the quotient `Kⁱ / Zⁱ`: the comparison `Kⁱ ⟶ Zʲ` of the differential with the
cycles kills `Zⁱ`, hence factors through that quotient. -/
def boundariesToCycles (i j : ι) : cokernel (K.iCycles i) ⟶ K.cycles j :=
  cokernel.desc _ (K.toCycles i j) (iCycles_comp_toCycles K i j)

/-- The composite of the projection `Kⁱ ⟶ Kⁱ / Zⁱ` with `boundariesToCycles` is the map
`Kⁱ ⟶ Zʲ` induced by the differential. -/
@[reassoc (attr := simp)]
lemma π_comp_boundariesToCycles (i j : ι) :
    cokernel.π (K.iCycles i) ≫ boundariesToCycles K i j = K.toCycles i j :=
  cokernel.π_desc _ _ _

/-- The boundaries are a subobject of the cycles: `Kⁱ ⟶ Zʲ` has `Zⁱ ⟶ Kⁱ` as its kernel, so the
induced map out of `Kⁱ / Zⁱ` is a monomorphism. -/
lemma mono_boundariesToCycles (i j : ι) (hij : c.Rel i j) : Mono (boundariesToCycles K i j) :=
  (ShortComplex.exact_of_f_is_kernel
    (ShortComplex.mk (K.iCycles i) (K.toCycles i j) (iCycles_comp_toCycles K i j))
    (cyclesIsKernelToCycles K i j hij)).mono_cokernelDesc

/-- The boundaries in degree `j` map to zero in the cohomology in degree `j`. -/
@[reassoc]
lemma boundariesToCycles_comp_homologyπ (i j : ι) :
    boundariesToCycles K i j ≫ K.homologyπ j = 0 := by
  rw [← cancel_epi (cokernel.π (K.iCycles i)), comp_zero, π_comp_boundariesToCycles_assoc,
    HomologicalComplex.toCycles_comp_homologyπ]

/-- **The cohomology in degree `j` is the cokernel of the boundaries inside the cycles.**  It is
the cokernel of `Kⁱ ⟶ Zʲ`, and `Kⁱ ⟶ Bʲ` is an epimorphism through which that map factors. -/
def homologyIsCokernelBoundaries (i j : ι) (hij : c.Rel i j) :
    IsColimit (CokernelCofork.ofπ (K.homologyπ j) (boundariesToCycles_comp_homologyπ K i j)) :=
  isCokernelOfComp (cokernel.π (K.iCycles i)) (K.toCycles i j)
    (K.homologyIsCokernel i j (c.prev_eq' hij)) _ (π_comp_boundariesToCycles K i j)

/-- **The short exact sequence `0 ⟶ Bʲ ⟶ Zʲ ⟶ Hʲ ⟶ 0`** exhibiting the cohomology in degree `j`
as the cycles modulo the boundaries. -/
@[sga "4½ Etat_0 1.3.2" "partial"]
lemma shortExact_boundaries (i j : ι) (hij : c.Rel i j) :
    (ShortComplex.mk (boundariesToCycles K i j) (K.homologyπ j)
      (boundariesToCycles_comp_homologyπ K i j)).ShortExact :=
  have := mono_boundariesToCycles K i j hij
  ⟨ShortComplex.exact_of_g_is_cokernel _ (homologyIsCokernelBoundaries K i j hij)⟩

end Boundaries

/-! ### Invertibility of the comparison on cohomology -/

/-- **The comparison `Hⁱ (T K) ⟶ T (Hⁱ K)` is invertible as soon as `T` preserves the
presentation of `Hⁱ K` as a cokernel**: the source is the cokernel of the boundaries of `T K`
inside its cycles, and left exactness of `T` identifies the latter with `T (Zⁱ K)`.  This
generalizes `Stacks.Cohomology.RightDerivedCoEdge.isIso_homologyToMapHomology`, where the
cokernel is preserved because `T` preserves all finite colimits. -/
theorem isIso_homologyToMapHomology_of_isColimit (T : D ⥤ E) [T.Additive]
    [PreservesFiniteLimits T] (K : HomologicalComplex D c) (i j : ι)
    (hc : IsColimit (CokernelCofork.ofπ (T.map (K.homologyπ i))
      (show T.map (K.toCycles j i) ≫ T.map (K.homologyπ i) = 0 by
        rw [← T.map_comp, HomologicalComplex.toCycles_comp_homologyπ, T.map_zero]))) :
    IsIso (homologyToMapHomology T K i) := by
  have w : T.map (K.toCycles j i) ≫ (mapCyclesIso T K i).hom ≫
      ((T.mapHomologicalComplex c).obj K).homologyπ i = 0 := by
    rw [← toCycles_comp_mapCyclesIso_inv T K j i, Category.assoc, Iso.inv_hom_id_assoc,
      HomologicalComplex.toCycles_comp_homologyπ]
  have hπ : T.map (K.homologyπ i) ≫ hc.desc (CokernelCofork.ofπ _ w) =
      (mapCyclesIso T K i).hom ≫ ((T.mapHomologicalComplex c).obj K).homologyπ i :=
    Cofork.IsColimit.π_desc hc
  have hepi : Epi (T.map (K.homologyπ i)) := epi_of_isColimit_cofork hc
  refine ⟨hc.desc (CokernelCofork.ofπ _ w), ?_, ?_⟩
  · rw [← cancel_epi (((T.mapHomologicalComplex c).obj K).homologyπ i),
      homologyπ_comp_homologyToMapHomology_assoc, Category.comp_id, hπ, Iso.inv_hom_id_assoc]
  · rw [← cancel_epi (T.map (K.homologyπ i)), Category.comp_id, ← Category.assoc, hπ,
      Category.assoc, homologyπ_comp_homologyToMapHomology, Iso.hom_inv_id_assoc]

/-! ### Acyclicity of the cycles -/

section Acyclic

variable [EnoughInjectives D] (T : D ⥤ E) [T.Additive] [PreservesFiniteLimits T]

omit [PreservesFiniteLimits T] in
/-- `T`-acyclicity only depends on the isomorphism class of an object. -/
lemma acyclic_of_iso {X Y : D} (e : X ≅ Y) (h : acyclic T X) : acyclic T Y :=
  fun n hn => (h n hn).of_iso ((T.rightDerived n).mapIso e).symm

/-- **The outer two of three `T`-acyclic objects in a short exact sequence force the middle
one**, and the sequence stays short exact under `T`.  This is the first part of
[Stacks, Tag 015D] in Mathlib's `ℕ`-indexing, the companion of
`Stacks.RightDerivedComp.acyclic_shortExact`. -/
lemma acyclic_shortExact_X₂ (S : ShortComplex D) (hS : S.ShortExact)
    (h₁ : acyclic T S.X₁) (h₃ : acyclic T S.X₃) :
    acyclic T S.X₂ ∧ (S.map T).ShortExact := by
  let _ := HasDerivedCategory.standard D
  let _ := HasDerivedCategory.standard E
  obtain ⟨h₂, hse⟩ := (Functor.rightAcyclic_and_shortExact_map_of_shortExact T S hS).1
    ((rightAcyclic_iff_acyclic T S.X₁).2 h₁) ((rightAcyclic_iff_acyclic T S.X₃).2 h₃)
  exact ⟨(rightAcyclic_iff_acyclic T S.X₂).1 h₂, hse⟩

variable (K : CochainComplex D ℕ) (hX : ∀ q, acyclic T (K.X q))
  (hH : ∀ q, acyclic T (K.homology q))

include hX hH in
/-- **The cycles of a complex of `T`-acyclic objects with `T`-acyclic cohomology are
`T`-acyclic.**  In degree zero the cycles *are* the cohomology, there being no incoming
differential; and `0 ⟶ Zⁿ ⟶ Kⁿ ⟶ Bⁿ⁺¹ ⟶ 0` followed by `0 ⟶ Bⁿ⁺¹ ⟶ Zⁿ⁺¹ ⟶ Hⁿ⁺¹ ⟶ 0`
propagates acyclicity upwards. -/
lemma acyclic_cycles (n : ℕ) : acyclic T (K.cycles n) := by
  induction n with
  | zero => exact acyclic_of_iso T (CochainComplex.isoHomologyπ₀ K).symm (hH 0)
  | succ n ih =>
    exact (acyclic_shortExact_X₂ T _ (shortExact_boundaries K n (n + 1) rfl)
      (acyclic_shortExact T _ (shortExact_cycles K n) ih (hX n)).1 (hH (n + 1))).1

include hX hH in
/-- **The boundaries of a complex of `T`-acyclic objects with `T`-acyclic cohomology are
`T`-acyclic**, and `T` keeps the presentation `Bⁿ⁺¹ = Kⁿ / Zⁿ` of the boundaries as a quotient
exact, so that `T (Kⁿ) ⟶ T (Bⁿ⁺¹)` is still an epimorphism. -/
lemma acyclic_boundaries (n : ℕ) :
    acyclic T (cokernel (K.iCycles n)) ∧ Epi (T.map (cokernel.π (K.iCycles n))) :=
  have h := acyclic_shortExact T _ (shortExact_cycles K n) (acyclic_cycles T K hX hH n) (hX n)
  ⟨h.1, h.2.epi_g⟩

include hX hH in
/-- **A left exact functor commutes with the cohomology of a complex of acyclic objects with
acyclic cohomology.**  The comparison `Hⁿ (T K) ⟶ T (Hⁿ K)` is an isomorphism in every degree.

This is the degeneration step of the Leray spectral sequence: the `E₂` page is concentrated in
the column `p = 0` precisely because `T` preserves the two short exact sequences that compute the
cohomology of `K`, and then the edge morphism `Hⁿ ⟶ E₂^{0,n}` is invertible. -/
theorem isIso_homologyToMapHomology_of_acyclic (n : ℕ) :
    IsIso (homologyToMapHomology T K n) := by
  obtain _ | n := n
  · exact isIso_homologyToMapHomology_zero T K
  · obtain ⟨hB, hepi⟩ := acyclic_boundaries T K hX hH n
    have hTH : IsColimit (CokernelCofork.ofπ (T.map (K.homologyπ (n + 1)))
        (show T.map (boundariesToCycles K n (n + 1)) ≫ T.map (K.homologyπ (n + 1)) = 0 by
          rw [← T.map_comp, boundariesToCycles_comp_homologyπ, T.map_zero])) :=
      (acyclic_shortExact_X₂ T _ (shortExact_boundaries K n (n + 1) rfl) hB
        (hH (n + 1))).2.gIsCokernel
    exact isIso_homologyToMapHomology_of_isColimit T K (n + 1) n
      (isCokernelEpiComp hTH (T.map (cokernel.π (K.iCycles n)))
        (by rw [← T.map_comp, π_comp_boundariesToCycles]))

include hX hH in
/-- `isIso_homologyToMapHomology_of_acyclic` as an isomorphism `Hⁿ (T K) ≅ T (Hⁿ K)`. -/
def homologyIsoMapHomologyOfAcyclic (n : ℕ) :
    ((T.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homology n ≅
      T.obj (K.homology n) :=
  have := isIso_homologyToMapHomology_of_acyclic T K hX hH n
  asIso (homologyToMapHomology T K n)

end Acyclic

end Stacks.Cohomology.RightDerivedCoEdge

end
