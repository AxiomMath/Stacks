module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DisjointUnionIso
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DisjointUnionTrace
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DimensionInduction
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CycleClassCupVanishingGeneral
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RealizationBlockAction
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# Cohomology classes extended by zero from an open and closed subscheme

Let `W` be data (D0)–(D3) of Section 45.9 (Tag 0FHA) satisfying (A), (B) and (C), with
coefficient field of characteristic zero, and let `j : V ⟶ X` be an open and closed immersion of
smooth projective schemes over `k`. By Stacks 0FHJ, `H^*(X) = H^*(V) × H^*(X ∖ V)`, so a class
`u ∈ H^*(V)` has a unique *extension by zero* `j_!u ∈ H^*(X)`: the class restricting to `u` on `V`
and to `0` on `X ∖ V` (`WeilData.extendByZero`). This file develops the calculus of these
extensions:

* `pull_extendByZero_self`, `pull_extendByZero_of_disjoint`: `j^*j_!u = u`, and `i^*j_!u = 0`
  when `i` lands in `X ∖ V`;
* `extendByZero_mem`: `j_!` preserves degrees;
* `eq_zero_of_pull_eq_zero`, `sum_extendByZero_pull`: a class is determined by its restrictions
  to a finite cover by open and closed subschemes, and is the sum of the extensions of its
  restrictions to a finite disjoint such cover;
* `extendByZero_comp`: extensions along composites compose;
* `traceProj_extendByZero_mul`: `∫_X j_!u ∪ b = ∫_V u ∪ j^*b` for `X`, `V` equidimensional of the
  same dimension (Stacks 0FHP);
* `pull_fst_extendByZero_mul_pull_snd_extendByZero`:
  `pr₁^*j_!u ∪ pr₂^*j'_!u' = (j × j')_!(pr₁^*u ∪ pr₂^*u')`.

## References

* [Stacks Project, Tag 0FHJ](https://stacks.math.columbia.edu/tag/0FHJ)
* [Stacks Project, Tag 0FHP](https://stacks.math.columbia.edu/tag/0FHP)
* [Stacks Project, Tag 0FHL](https://stacks.math.columbia.edu/tag/0FHL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u w

namespace Stacks.WeilCohomology

namespace SmoothProjectiveScheme

variable {k : Type u} [Field k]

/-- The product `j × j' : V × V' ⟶ X × X'` of two open immersions is an open immersion. -/
instance {V X V' X' : (SmoothProjectiveScheme k).FullSubcategory} (j : V ⟶ X) (j' : V' ⟶ X')
    [IsOpenImmersion j.hom.left] [IsOpenImmersion j'.hom.left] :
    IsOpenImmersion (prodLift (fst V V' ≫ j) (snd V V' ≫ j')).hom.left :=
  MorphismProperty.pullbackMap (P := @IsOpenImmersion) (f := V.obj.hom) (g := V'.obj.hom)
    (f' := X.obj.hom) (g' := X'.obj.hom) (i₁ := j.hom.left) (i₂ := j'.hom.left) inferInstance
    inferInstance (Over.w j.hom).symm (Over.w j'.hom).symm

/-- The product `j × j' : V × V' ⟶ X × X'` of two closed immersions is a closed immersion. -/
instance {V X V' X' : (SmoothProjectiveScheme k).FullSubcategory} (j : V ⟶ X) (j' : V' ⟶ X')
    [IsClosedImmersion j.hom.left] [IsClosedImmersion j'.hom.left] :
    IsClosedImmersion (prodLift (fst V V' ≫ j) (snd V V' ≫ j')).hom.left :=
  haveI : MorphismProperty.IsStableUnderComposition @IsClosedImmersion :=
    ⟨fun _ _ hf hg ↦ by have := hf; have := hg; infer_instance⟩
  MorphismProperty.pullbackMap (P := @IsClosedImmersion) (f := V.obj.hom) (g := V'.obj.hom)
    (f' := X.obj.hom) (g' := X'.obj.hom) (i₁ := j.hom.left) (i₂ := j'.hom.left) inferInstance
    inferInstance (Over.w j.hom).symm (Over.w j'.hom).symm

/-- The image of `j × j'` is the set of points whose two projections lie in the images of `j` and
`j'`. -/
theorem range_prodLift_comp {V X V' X' : (SmoothProjectiveScheme k).FullSubcategory} (j : V ⟶ X)
    (j' : V' ⟶ X') :
    Set.range (prodLift (fst V V' ≫ j) (snd V V' ≫ j')).hom.left =
      (fst X X').hom.left ⁻¹' Set.range j.hom.left ∩
        (snd X X').hom.left ⁻¹' Set.range j'.hom.left :=
  Scheme.Pullback.range_map (f := V.obj.hom) (g := V'.obj.hom) X.obj.hom X'.obj.hom j.hom.left
    j'.hom.left (𝟙 _) ((Category.comp_id _).trans (Over.w j.hom).symm)
    ((Category.comp_id _).trans (Over.w j'.hom).symm)

/-- A morphism whose image lies in the image of an open immersion `ι` factors through `ι`. -/
theorem exists_comp_eq_of_range_subset {U C X : (SmoothProjectiveScheme k).FullSubcategory}
    (i : U ⟶ X) (ι : C ⟶ X) [IsOpenImmersion ι.hom.left]
    (h : Set.range i.hom.left ⊆ Set.range ι.hom.left) : ∃ g : U ⟶ C, g ≫ ι = i :=
  ⟨ObjectProperty.homMk (Over.homMk (U := U.obj) (V := C.obj)
      (IsOpenImmersion.lift ι.hom.left i.hom.left h) (by
        rw [← Over.w ι.hom, ← Category.assoc, IsOpenImmersion.lift_fac, Over.w i.hom])),
    hom_ext_left (IsOpenImmersion.lift_fac _ _ _)⟩

/-- The underlying map of points of a composite. -/
theorem comp_hom_left_apply {U V X : (SmoothProjectiveScheme k).FullSubcategory} (f : U ⟶ V)
    (g : V ⟶ X) (p : U.obj.left) : (f ≫ g).hom.left p = g.hom.left (f.hom.left p) :=
  rfl

/-- A point of an open and closed subscheme `U` is in the image of its inclusion. -/
theorem mem_range_clopenι {X : (SmoothProjectiveScheme k).FullSubcategory} {U : X.obj.left.Opens}
    (hU : IsClopen (U : Set X.obj.left)) {y : X.obj.left} (hy : y ∈ U) :
    y ∈ Set.range (clopenι X U hU).hom.left :=
  (Scheme.Opens.range_ι U).ge hy

/-- The image of a composite. -/
theorem range_comp_hom_left {U V X : (SmoothProjectiveScheme k).FullSubcategory} (f : U ⟶ V)
    (g : V ⟶ X) : Set.range (f ≫ g).hom.left = g.hom.left '' Set.range f.hom.left := by
  rw [← Set.range_comp]
  rfl

/-- The complement `X ∖ j(V)` of the image of a closed immersion `j : V ⟶ X`, an open
subscheme. -/
def complOpen {V X : (SmoothProjectiveScheme k).FullSubcategory} (j : V ⟶ X)
    [IsClosedImmersion j.hom.left] : X.obj.left.Opens :=
  ⟨(Set.range j.hom.left)ᶜ, j.hom.left.isClosedEmbedding.isClosed_range.isOpen_compl⟩

/-- The complement of the image of an open and closed immersion is open and closed. -/
theorem isClopen_complOpen {V X : (SmoothProjectiveScheme k).FullSubcategory} (j : V ⟶ X)
    [IsOpenImmersion j.hom.left] [IsClosedImmersion j.hom.left] :
    IsClopen (complOpen j : Set X.obj.left) :=
  ⟨j.hom.left.isOpenEmbedding.isOpen_range.isClosed_compl, (complOpen j).isOpen⟩

/-- The inclusion of the complement `X ∖ j(V)` of an open and closed immersion. -/
def complι {V X : (SmoothProjectiveScheme k).FullSubcategory} (j : V ⟶ X)
    [IsOpenImmersion j.hom.left]
    [IsClosedImmersion j.hom.left] : clopenObj X (complOpen j) (isClopen_complOpen j) ⟶ X :=
  clopenι X (complOpen j) (isClopen_complOpen j)

/-- `X` is the disjoint union of `j(V)` and its complement. -/
def isColimitCompl {V X : (SmoothProjectiveScheme k).FullSubcategory} (j : V ⟶ X)
    [IsOpenImmersion j.hom.left]
    [IsClosedImmersion j.hom.left] : IsColimit (BinaryCofan.mk j (complι j)) :=
  isColimitOfIsColimitMapCofan (nonempty_isColimit_binaryCofanMk_of_isCompl j.hom.left
    (complOpen j).ι (by
      rw [Scheme.Opens.opensRange_ι, isCompl_iff, disjoint_iff, codisjoint_iff]
      constructor
      · ext x
        simp [complOpen]
      · ext x
        simp only [TopologicalSpace.Opens.coe_sup, Set.mem_union, SetLike.mem_coe,
          Scheme.Hom.coe_opensRange, TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
        exact em _)).some

/-- The image of the complement inclusion is the complement of the image. -/
theorem range_complι {V X : (SmoothProjectiveScheme k).FullSubcategory} (j : V ⟶ X)
    [IsOpenImmersion j.hom.left] [IsClosedImmersion j.hom.left] :
    Set.range (complι j).hom.left = (Set.range j.hom.left)ᶜ := by
  change Set.range (complOpen j).ι = _
  rw [Scheme.Opens.range_ι]
  rfl

/-- A point of the complement of `j(V)` is not mapped into the image of `j`. -/
private theorem complι_hom_left_apply_notMem_range
    {V X : (SmoothProjectiveScheme k).FullSubcategory} (j : V ⟶ X)
    [IsOpenImmersion j.hom.left] [IsClosedImmersion j.hom.left]
    (p : (clopenObj X (complOpen j) (isClopen_complOpen j)).obj.left) :
    (complι j).hom.left p ∉ Set.range j.hom.left :=
  (range_complι j).le ⟨p, rfl⟩

/-- The inclusion of the complement of an open and closed immersion is an open immersion. -/
instance {V X : (SmoothProjectiveScheme k).FullSubcategory} (j : V ⟶ X) [IsOpenImmersion j.hom.left]
    [IsClosedImmersion j.hom.left] : IsOpenImmersion (complι j).hom.left :=
  inferInstanceAs (IsOpenImmersion (complOpen j).ι)

/-- The inclusion of the complement of an open and closed immersion is a closed immersion. -/
instance {V X : (SmoothProjectiveScheme k).FullSubcategory} (j : V ⟶ X) [IsOpenImmersion j.hom.left]
    [IsClosedImmersion j.hom.left] : IsClosedImmersion (complι j).hom.left :=
  isClosedImmersion_ι_of_isClopen (isClopen_complOpen j)

end SmoothProjectiveScheme

namespace WeilData

open SmoothProjectiveScheme

variable {k : Type u} [Field k] {F : Type w} [Field F] [CharZero F] {W : WeilData k F}
  (hA : W.PoincareDuality) (hB : W.Kunneth) (hC : W.CycleClassAxiom hA.perfectPairing)

/-- **Extension by zero** `j_! : H^*(V) → H^*(X)` along an open and closed immersion
`j : V ⟶ X`: the class restricting to `u` on `V` and to `0` on the complement (Stacks 0FHJ). -/
def extendByZero {V X : (SmoothProjectiveScheme k).FullSubcategory} (j : V ⟶ X)
    [IsOpenImmersion j.hom.left] [IsClosedImmersion j.hom.left] : W.H V →ₗ[F] W.H X :=
  (LinearEquiv.ofBijective ((W.pull j).toLinearMap.prod (W.pull (complι j)).toLinearMap)
    (pullbackPair_bijective_of_isColimit hA hB hC (isColimitCompl j))).symm.toLinearMap ∘ₗ
    LinearMap.inl F _ _

/-- The extension by zero restricts to the class on `V` and to `0` on the complement. -/
theorem pull_extendByZero_and {V X : (SmoothProjectiveScheme k).FullSubcategory} (j : V ⟶ X)
    [IsOpenImmersion j.hom.left] [IsClosedImmersion j.hom.left] (x : W.H V) :
    W.pull j (extendByZero hA hB hC j x) = x ∧
      W.pull (complι j) (extendByZero hA hB hC j x) = 0 :=
  Prod.ext_iff.1 ((LinearEquiv.ofBijective ((W.pull j).toLinearMap.prod
    (W.pull (complι j)).toLinearMap)
    (pullbackPair_bijective_of_isColimit hA hB hC (isColimitCompl j))).apply_symm_apply (x, 0))

include hA hB hC in
/-- A class vanishing on `j(V)` and on its complement vanishes (Stacks 0FHJ). -/
theorem eq_zero_of_pull_eq_zero_of_pull_complι_eq_zero
    {V X : (SmoothProjectiveScheme k).FullSubcategory}
    (j : V ⟶ X) [IsOpenImmersion j.hom.left] [IsClosedImmersion j.hom.left] {a : W.H X}
    (h₁ : W.pull j a = 0) (h₂ : W.pull (complι j) a = 0) : a = 0 :=
  (pullbackPair_bijective_of_isColimit hA hB hC (isColimitCompl j)).1
    (Prod.ext (h₁.trans (map_zero (W.pull j)).symm) (h₂.trans (map_zero (W.pull (complι j))).symm))

variable {hA hB hC}

/-- A class on `D` vanishes if its restrictions along all maps into `D` whose composite with `c`
lands in, respectively avoids, the image of `j` vanish. -/
private theorem eq_zero_of_pull_eq_zero_of_range (hA : W.PoincareDuality) (hB : W.Kunneth)
    (hC : W.CycleClassAxiom hA.perfectPairing)
    {D X V : (SmoothProjectiveScheme k).FullSubcategory} (c : D ⟶ X) (j : V ⟶ X)
    [IsOpenImmersion j.hom.left] [IsClosedImmersion j.hom.left] {a : W.H D}
    (h₁ : ∀ {U : (SmoothProjectiveScheme k).FullSubcategory} (g : U ⟶ D),
      Set.range (g ≫ c).hom.left ⊆ Set.range j.hom.left → W.pull g a = 0)
    (h₂ : ∀ {U : (SmoothProjectiveScheme k).FullSubcategory} (g : U ⟶ D),
      Disjoint (Set.range (g ≫ c).hom.left) (Set.range j.hom.left) → W.pull g a = 0) :
    a = 0 := by
  let O : D.obj.left.Opens := c.hom.left ⁻¹ᵁ j.hom.left.opensRange
  have hO : IsClopen (O : Set D.obj.left) :=
    ⟨j.hom.left.isClosedEmbedding.isClosed_range.preimage c.hom.left.continuous, O.isOpen⟩
  have : IsClosedImmersion (clopenι D O hO).hom.left := isClosedImmersion_ι_of_isClopen hO
  refine eq_zero_of_pull_eq_zero_of_pull_complι_eq_zero hA hB hC (clopenι D O hO)
    (h₁ _ ?_) (h₂ _ (Set.disjoint_left.2 ?_))
  · rintro _ ⟨p, rfl⟩
    rw [comp_hom_left_apply, clopenι_hom_left]
    exact p.2
  · rintro _ ⟨p, rfl⟩ hp
    rw [comp_hom_left_apply] at hp
    exact complι_hom_left_apply_notMem_range _ p (mem_range_clopenι hO hp)

/-- The extension by zero `j_!u` restricts to `u` on `V`: `j^*j_!u = u`. -/
theorem pull_extendByZero_self {V X : (SmoothProjectiveScheme k).FullSubcategory} (j : V ⟶ X)
    [IsOpenImmersion j.hom.left] [IsClosedImmersion j.hom.left] (x : W.H V) :
    W.pull j (extendByZero hA hB hC j x) = x :=
  (pull_extendByZero_and hA hB hC j x).1

/-- If the image of `i` is disjoint from the image of `j`, then `i^*j_!u = 0`. -/
theorem pull_extendByZero_of_disjoint {U V X : (SmoothProjectiveScheme k).FullSubcategory}
    (i : U ⟶ X) (j : V ⟶ X) [IsOpenImmersion j.hom.left] [IsClosedImmersion j.hom.left]
    (hdisj : Disjoint (Set.range i.hom.left) (Set.range j.hom.left)) (x : W.H V) :
    W.pull i (extendByZero hA hB hC j x) = 0 := by
  obtain ⟨g, rfl⟩ := exists_comp_eq_of_range_subset i (complι j) (by
    rw [range_complι]
    exact fun y hy hy' ↦ Set.disjoint_left.1 hdisj hy hy')
  rw [← pull_pull, (pull_extendByZero_and hA hB hC j x).2, map_zero]

/-- Extension by zero preserves degrees: if `u ∈ H^n(V)` then `j_!u ∈ H^n(X)`. -/
theorem extendByZero_mem {V X : (SmoothProjectiveScheme k).FullSubcategory} (j : V ⟶ X)
    [IsOpenImmersion j.hom.left] [IsClosedImmersion j.hom.left] {n : ℤ} {x : W.H V}
    (hx : x ∈ W.grade V n) :
    extendByZero hA hB hC j x ∈ W.grade X n := by
  set y := extendByZero hA hB hC j x
  have hy : (DirectSum.decompose (W.grade X) y n : W.H X) = y := by
    refine sub_eq_zero.1 (eq_zero_of_pull_eq_zero_of_pull_complι_eq_zero hA hB hC j ?_ ?_)
    · rw [map_sub, ← pull_decompose, pull_extendByZero_self, DirectSum.decompose_of_mem_same _ hx,
        sub_self]
    · rw [map_sub, ← pull_decompose, (pull_extendByZero_and hA hB hC j x).2]
      simp
  rw [← hy]
  exact (DirectSum.decompose (W.grade X) y n).2

include hA hB hC in
/-- A class is determined by its restrictions to a finite cover by open and closed subschemes. -/
theorem eq_zero_of_pull_eq_zero {X : (SmoothProjectiveScheme k).FullSubcategory} {ι : Type*}
    (S : Finset ι) {V : ι → (SmoothProjectiveScheme k).FullSubcategory} (j : ∀ s, V s ⟶ X)
    [∀ s, IsOpenImmersion (j s).hom.left] [∀ s, IsClosedImmersion (j s).hom.left]
    (hcover : ∀ x : X.obj.left, ∃ s ∈ S, x ∈ Set.range (j s).hom.left) {a : W.H X}
    (h : ∀ s ∈ S, W.pull (j s) a = 0) : a = 0 := by
  classical
  let U : Finset ι → X.obj.left.Opens := fun T ↦
    ⟨⋃ s ∈ T, Set.range (j s).hom.left,
      isOpen_biUnion fun s _ ↦ (j s).hom.left.isOpenEmbedding.isOpen_range⟩
  have hU : ∀ T, IsClopen (U T : Set X.obj.left) := fun T ↦
    ⟨isClosed_biUnion_finset fun s _ ↦ (j s).hom.left.isClosedEmbedding.isClosed_range,
      (U T).isOpen⟩
  have key : ∀ T, T ⊆ S → W.pull (clopenι X (U T) (hU T)) a = 0 := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _
      have : IsEmpty (clopenObj X (U ∅) (hU ∅)).obj.left := ⟨fun p ↦ by simpa [U] using p.2⟩
      have := subsingleton_of_isEmpty hB.kunnethIsomorphism hC.pullback hC.mul hC.point
        (clopenObj X (U ∅) (hU ∅))
      exact Subsingleton.elim _ _
    | insert s T hsT ih =>
      intro hS
      have hT := ih (subset_trans (Finset.subset_insert _ _) hS)
      have : IsClosedImmersion (clopenι X (U (insert s T)) (hU _)).hom.left :=
        isClosedImmersion_ι_of_isClopen (hU _)
      obtain ⟨g, hg⟩ := exists_comp_eq_of_range_subset (j s) (clopenι X (U (insert s T)) (hU _))
        (fun y hy ↦ mem_range_clopenι (hU _) (Set.mem_biUnion (Finset.mem_insert_self s T) hy))
      have hgl : g.hom.left ≫ (clopenι X (U (insert s T)) (hU _)).hom.left = (j s).hom.left :=
        congrArg (fun φ ↦ φ.hom.left) hg
      have : IsOpenImmersion (g.hom.left ≫ (clopenι X (U (insert s T)) (hU _)).hom.left) := by
        rw [hgl]; infer_instance
      have : IsClosedImmersion (g.hom.left ≫ (clopenι X (U (insert s T)) (hU _)).hom.left) := by
        rw [hgl]; infer_instance
      have : IsOpenImmersion g.hom.left := IsOpenImmersion.of_comp _ (clopenι X _ (hU _)).hom.left
      have : IsClosedImmersion g.hom.left :=
        IsClosedImmersion.of_comp_isClosedImmersion _ (clopenι X _ (hU _)).hom.left
      refine eq_zero_of_pull_eq_zero_of_pull_complι_eq_zero hA hB hC g ?_ ?_
      · rw [pull_pull, hg]
        exact h s (hS (Finset.mem_insert_self s T))
      · rw [pull_pull]
        obtain ⟨g', hg'⟩ := exists_comp_eq_of_range_subset (complι g ≫ clopenι X _ (hU _))
          (clopenι X (U T) (hU T)) (by
            rintro _ ⟨p, rfl⟩
            refine mem_range_clopenι (hU T) ?_
            have hp : (clopenι X _ (hU (insert s T))).hom.left ((complι g).hom.left p) ∈
                U (insert s T) := by
              rw [clopenι_hom_left]
              exact ((complι g).hom.left p).2
            change _ ∈ ⋃ t ∈ insert s T, _ at hp
            rw [Finset.set_biUnion_insert] at hp
            rcases hp with ⟨v, hv⟩ | hp
            · exfalso
              refine complι_hom_left_apply_notMem_range g p ⟨v,
                (clopenι X _ (hU (insert s T))).hom.left.isOpenEmbedding.injective ?_⟩
              rw [← comp_hom_left_apply, hg]
              exact hv
            · rw [comp_hom_left_apply]
              exact hp)
        rw [← hg', ← pull_pull, hT, map_zero]
  obtain ⟨g, hg⟩ := exists_comp_eq_of_range_subset (𝟙 X) (clopenι X (U S) (hU S)) (by
    rintro _ ⟨y, rfl⟩
    refine mem_range_clopenι (hU S) ?_
    obtain ⟨s, hs, hy⟩ := hcover ((𝟙 X : X ⟶ X).hom.left y)
    exact Set.mem_biUnion hs hy)
  have ha : a = W.pull (𝟙 X) a := by
    rw [W.pull_id]
    rfl
  rw [ha, ← hg, ← pull_pull, key S subset_rfl, map_zero]

/-- A class is the sum of the extensions of its restrictions to a finite disjoint cover by open
and closed subschemes. -/
theorem sum_extendByZero_pull {X : (SmoothProjectiveScheme k).FullSubcategory} {ι : Type*}
    (S : Finset ι) {V : ι → (SmoothProjectiveScheme k).FullSubcategory} (j : ∀ s, V s ⟶ X)
    [∀ s, IsOpenImmersion (j s).hom.left] [∀ s, IsClosedImmersion (j s).hom.left]
    (hcover : ∀ x : X.obj.left, ∃ s ∈ S, x ∈ Set.range (j s).hom.left)
    (hdisj : ∀ s ∈ S, ∀ t ∈ S, s ≠ t →
      Disjoint (Set.range (j s).hom.left) (Set.range (j t).hom.left)) (a : W.H X) :
    ∑ s ∈ S, extendByZero hA hB hC (j s) (W.pull (j s) a) = a := by
  classical
  refine (sub_eq_zero.1 (eq_zero_of_pull_eq_zero (hA := hA) (hB := hB) (hC := hC) S j hcover
    fun t ht ↦ ?_)).symm
  rw [map_sub, map_sum, Finset.sum_eq_single t
    (fun s hs hst ↦ pull_extendByZero_of_disjoint _ _ (hdisj s hs t ht hst).symm _)
    (fun h ↦ absurd ht h), pull_extendByZero_self, sub_self]

/-- Extension by zero along a composite of open and closed immersions is the composite of the
extensions: `(i ≫ j)_!u = j_!(i_!u)`. -/
theorem extendByZero_comp {U V X : (SmoothProjectiveScheme k).FullSubcategory} (i : U ⟶ V)
    (j : V ⟶ X)
    [IsOpenImmersion i.hom.left] [IsClosedImmersion i.hom.left] [IsOpenImmersion j.hom.left]
    [IsClosedImmersion j.hom.left] [IsOpenImmersion (i ≫ j).hom.left]
    [IsClosedImmersion (i ≫ j).hom.left] (x : W.H U) :
    extendByZero hA hB hC (i ≫ j) x = extendByZero hA hB hC j (extendByZero hA hB hC i x) := by
  refine (sub_eq_zero.1
    (eq_zero_of_pull_eq_zero_of_pull_complι_eq_zero hA hB hC (i ≫ j) ?_ ?_)).symm
  · rw [map_sub, pull_extendByZero_self, ← pull_pull, pull_extendByZero_self,
      pull_extendByZero_self, sub_self]
  · rw [map_sub, (pull_extendByZero_and hA hB hC (i ≫ j) x).2, sub_zero]
    refine eq_zero_of_pull_eq_zero_of_range hA hB hC (complι (i ≫ j)) j (fun g hg ↦ ?_)
      fun g hg ↦ ?_
    · rw [pull_pull]
      obtain ⟨g', hg'⟩ := exists_comp_eq_of_range_subset (g ≫ complι (i ≫ j)) j hg
      rw [← hg', ← pull_pull, pull_extendByZero_self]
      refine pull_extendByZero_of_disjoint _ _ (Set.disjoint_left.2 ?_) _
      rintro _ ⟨p, rfl⟩ ⟨q, hq⟩
      exact complι_hom_left_apply_notMem_range (i ≫ j) (g.hom.left p)
        ⟨q, by
          rw [comp_hom_left_apply, hq]
          exact congrArg (fun φ ↦ φ.hom.left p) hg'⟩
    · rw [pull_pull]
      exact pull_extendByZero_of_disjoint _ _ hg _

omit [CharZero F] in
include hA hB hC in
/-- **Stacks 0FHP on the whole cohomology ring**: for a coproduct `X = V ⨿ C` of nonempty
schemes equidimensional of dimension `n`, `∫_X y = ∫_V i^*y + ∫_C j^*y` for every `y ∈ H^*(X)`. -/
theorem traceProj_eq_add_of_isColimit {V C X : (SmoothProjectiveScheme k).FullSubcategory}
    {i : V ⟶ X} {i' : C ⟶ X} (hc : IsColimit (BinaryCofan.mk i i')) {n : ℕ}
    (hX : IsNonemptyEquidimensional X n) (hV : IsNonemptyEquidimensional V n)
    (hC' : IsNonemptyEquidimensional C n) (y : W.H X) :
    W.traceProj X n hX y = W.traceProj V n hV (W.pull i y) + W.traceProj C n hC' (W.pull i' y) := by
  induction y using DirectSum.Decomposition.inductionOn (W.grade X) with
  | zero => simp
  | add y y' hy hy' =>
    rw [map_add, hy, hy', map_add, map_add, map_add, map_add]
    abel
  | @homogeneous m y =>
    obtain ⟨y, hym⟩ := y
    change W.traceProj X n hX y =
      W.traceProj V n hV (W.pull i y) + W.traceProj C n hC' (W.pull i' y)
    by_cases hm : m = 2 * (n : ℤ)
    · subst hm
      have h := trace_eq_add hA hB hC hc hV hC' hX ((W.twCoord X _ n).symm ⟨y, hym⟩)
      rwa [trace_eq_traceProj, trace_eq_traceProj, trace_eq_traceProj, twCoord_pullTw,
        twCoord_pullTw, coe_pullDeg, coe_pullDeg, LinearEquiv.apply_symm_apply] at h
    · rw [W.traceProj_of_mem_ne X n hX hym hm,
        W.traceProj_of_mem_ne V n hV (W.pull_grade i m y hym) hm,
        W.traceProj_of_mem_ne C n hC' (W.pull_grade i' m y hym) hm, add_zero]

omit [CharZero F] in
include hA hB hC in
/-- The trace is invariant under pullback along an isomorphism, on the whole cohomology ring. -/
theorem traceProj_pull_of_isIso {V X : (SmoothProjectiveScheme k).FullSubcategory} (j : V ⟶ X)
    [IsIso j.hom.left] {n : ℕ} (hX : IsNonemptyEquidimensional X n)
    (hV : IsNonemptyEquidimensional V n) (y : W.H X) :
    W.traceProj V n hV (W.pull j y) = W.traceProj X n hX y := by
  induction y using DirectSum.Decomposition.inductionOn (W.grade X) with
  | zero => simp
  | add y y' hy hy' => rw [map_add, map_add, hy, hy', map_add]
  | @homogeneous m y =>
    obtain ⟨y, hym⟩ := y
    change W.traceProj V n hV (W.pull j y) = W.traceProj X n hX y
    by_cases hm : m = 2 * (n : ℤ)
    · subst hm
      have h := W.trace_pullTw_of_isIso hA hB hC j hV hX ((W.twCoord X _ n).symm ⟨y, hym⟩)
      rwa [trace_eq_traceProj, trace_eq_traceProj, twCoord_pullTw, coe_pullDeg,
        LinearEquiv.apply_symm_apply] at h
    · rw [W.traceProj_of_mem_ne X n hX hym hm,
        W.traceProj_of_mem_ne V n hV (W.pull_grade j m y hym) hm]

/-- **The trace of an extension by zero** (Stacks 0FHP): `∫_X j_!u ∪ b = ∫_V u ∪ j^*b` for `X`
and `V` nonempty and equidimensional of the same dimension. -/
theorem traceProj_extendByZero_mul {V X : (SmoothProjectiveScheme k).FullSubcategory} (j : V ⟶ X)
    [IsOpenImmersion j.hom.left] [IsClosedImmersion j.hom.left] {n : ℕ}
    (hX : IsNonemptyEquidimensional X n) (hV : IsNonemptyEquidimensional V n) (x : W.H V)
    (b : W.H X) :
    W.traceProj X n hX (extendByZero hA hB hC j x * b) = W.traceProj V n hV (x * W.pull j b) := by
  have hz := pull_extendByZero_and hA hB hC j x
  rcases isEmpty_or_nonempty (clopenObj X (complOpen j) (isClopen_complOpen j)).obj.left with
    hE | hE
  · have : IsIso j.hom.left := (isIso_iff_isOpenImmersion_and_surjective _).2
      ⟨inferInstance, ⟨fun y ↦ Classical.byContradiction fun hy ↦ hE.false ⟨y, hy⟩⟩⟩
    rw [← traceProj_pull_of_isIso (hA := hA) (hB := hB) (hC := hC) j hX hV, map_mul (W.pull j),
      hz.1]
  · have hCn : IsNonemptyEquidimensional (clopenObj X (complOpen j) (isClopen_complOpen j)) n :=
      ⟨hE, RelativeDimension.comp_isOpenImmersion (complι j).hom.left _ hX.relativeDimension⟩
    rw [traceProj_eq_add_of_isColimit (hA := hA) (hB := hB) (hC := hC) (isColimitCompl j) hX hV
      hCn, map_mul (W.pull j), map_mul (W.pull (complι j)), hz.1, hz.2, zero_mul, map_zero,
      add_zero]

/-- Exterior products of extensions by zero are extensions by zero:
`pr₁^*j_!u ∪ pr₂^*j'_!u' = (j × j')_!(pr₁^*u ∪ pr₂^*u')`. -/
theorem pull_fst_extendByZero_mul_pull_snd_extendByZero
    {V X V' X' : (SmoothProjectiveScheme k).FullSubcategory}
    (j : V ⟶ X) (j' : V' ⟶ X') [IsOpenImmersion j.hom.left] [IsClosedImmersion j.hom.left]
    [IsOpenImmersion j'.hom.left] [IsClosedImmersion j'.hom.left] (x : W.H V) (x' : W.H V') :
    W.pull (fst X X') (extendByZero hA hB hC j x) *
        W.pull (snd X X') (extendByZero hA hB hC j' x') =
      extendByZero hA hB hC (prodLift (fst V V' ≫ j) (snd V V' ≫ j'))
        (W.pull (fst V V') x * W.pull (snd V V') x') := by
  set P := prodLift (fst V V' ≫ j) (snd V V' ≫ j')
  refine sub_eq_zero.1 (eq_zero_of_pull_eq_zero_of_pull_complι_eq_zero hA hB hC P ?_ ?_)
  · rw [map_sub, pull_extendByZero_self, map_mul, pull_pull, pull_pull, prodLift_fst,
      prodLift_snd, ← pull_pull, ← pull_pull, pull_extendByZero_self, pull_extendByZero_self,
      sub_self]
  · rw [map_sub, (pull_extendByZero_and hA hB hC P _).2, sub_zero]
    refine eq_zero_of_pull_eq_zero_of_range hA hB hC (complι P ≫ fst X X') j
      (fun g hg ↦ ?_) fun g hg ↦ ?_
    · simp only [map_mul, pull_pull]
      rw [pull_extendByZero_of_disjoint (g ≫ complι P ≫ snd X X') j' ?_ x', mul_zero]
      refine Set.disjoint_left.2 ?_
      rintro _ ⟨p, rfl⟩ ⟨v', hv'⟩
      rw [comp_hom_left_apply, comp_hom_left_apply] at hv'
      refine complι_hom_left_apply_notMem_range P (g.hom.left p) ?_
      rw [range_prodLift_comp]
      exact ⟨hg ⟨p, rfl⟩, v', hv'⟩
    · simp only [map_mul, pull_pull]
      rw [pull_extendByZero_of_disjoint (g ≫ complι P ≫ fst X X') j hg x, zero_mul]

end WeilData

end Stacks.WeilCohomology

end
