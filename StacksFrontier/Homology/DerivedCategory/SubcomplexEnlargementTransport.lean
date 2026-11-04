module

public import StacksFrontier.Homology.DerivedCategory.SubcomplexEnlargement

@[expose] public noncomputable section

/-!
# Stacks 0GYI read at a larger pair of subcomplexes

For a ring homomorphism `A →+* B`, Stacks 0GYI enlarges a compatible pair of subcomplexes
`M₁ ⊆ M`, `N₁ ⊆ N` to a pair `M₂ ⊆ M`, `N₂ ⊆ N` of controlled size on which the two defects of
the comparison map for derived base change disappear: on every cohomology module the kernel of
the comparison at `M₁` dies in `M₂`, and the image of `N₁` in `N₂` is covered by the comparison
at `M₂`. This file restates that conclusion at an arbitrary pair of subcomplexes whose sections
contain those of `M₂` and `N₂` degreewise, and on elements rather than through `kernel.ι` and
`imageSubobject`.

## Main results

* `Stacks.SubcomplexEnlargement.exists_enlargements_stagewise_elementwise`: the enlargement of
  Stacks 0GYI, with its kernel and image conclusions asserted at every larger compatible pair of
  subcomplexes and in elementwise form.

## References

* [Stacks Project, Tag 0GYI](https://stacks.math.columbia.edu/tag/0GYI)
-/

open CategoryTheory CategoryTheory.Limits Cardinal

namespace Stacks.SubcomplexEnlargement

universe u v w

attribute [local instance] HasDerivedCategory.standard

/-- **The enlargement of Stacks 0GYI, with its conclusions read at any larger pair of
subcomplexes and on elements.**

For a ring homomorphism `f : A →+* B` there is a cardinal `κ` with the following property. Let
`b : E.obj M ⟶ N` be a morphism from the base change of a complex of `A`-modules whose image in
the derived category is a comparison isomorphism, and let `m₁ : M₁ ⟶ M`, `n₁ : N₁ ⟶ N` be a
compatible pair of subcomplexes. Then there is an enlargement `m₂ : M₂ ⟶ M`, `n₂ : N₂ ⟶ N` whose
terms have at most `max κ #(M₁ ⊕ N₁)` elements altogether such that, for *every* pair of
subcomplexes `m' : M' ⟶ M`, `n' : N' ⟶ N` whose sections contain those of `M₂` and `N₂` in each
degree and which receives `M₁` and `N₁` compatibly, the comparison defects at `M₁` and `N₁` are
resolved in `M'` and `N'`: a cohomology class of `T.obj M₁` killed by the comparison at `M₁` is
killed by `M₁ ⟶ M'`, and every cohomology class of `N₁` becomes, in `N'`, the image of a class of
`T.obj M'` under the comparison at `M'`.

The conclusions are stated at an arbitrary larger pair because that is what the enlargement of
Stacks 0GYZ has at hand: the next stage of its iteration is a subcomplex of a complex of
presheaf sections, known only to contain the sections of `M₂` and `N₂` rather than to be them.
They are stated on elements rather than through `kernel.ι` and `imageSubobject` because an
elementwise statement is what transports along an isomorphism of the modules involved, which is
what identifying a stage of an increasing chain with its image requires. -/
public theorem exists_enlargements_stagewise_elementwise
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] (f : A →+* B) :
    ∃ κ : Cardinal.{max u v},
      letI : (ModuleCat.extendScalars.{u, v, max v (max u w)} f).IsLeftAdjoint :=
        ModuleCat.instIsLeftAdjointExtendScalars.{u, v, max u w} f
      let E : CochainComplex (ModuleCat.{max u v w} A) ℤ ⥤
          CochainComplex (ModuleCat.{max u v w} B) ℤ :=
        (ModuleCat.extendScalars.{u, v, max v (max u w)} f).mapHomologicalComplex
          (ComplexShape.up ℤ)
      ∀ (T : DerivedCategory (ModuleCat.{max u v w} A) ⥤
          DerivedCategory (ModuleCat.{max u v w} B))
        (α : DerivedCategory.Q (C := ModuleCat.{max u v w} A) ⋙ T ⟶
          E ⋙ DerivedCategory.Q (C := ModuleCat.{max u v w} B))
        [T.IsLeftDerivedFunctor α
          (HomologicalComplex.quasiIso (ModuleCat.{max u v w} A) (ComplexShape.up ℤ))]
        (M : CochainComplex (ModuleCat.{max u v w} A) ℤ)
        (N : CochainComplex (ModuleCat.{max u v w} B) ℤ)
        (b : E.obj M ⟶ N),
      IsIso (α.app M ≫ DerivedCategory.Q.map b) →
      ∀ (M₁ : CochainComplex (ModuleCat.{max u v w} A) ℤ)
        (N₁ : CochainComplex (ModuleCat.{max u v w} B) ℤ)
        (m₁ : M₁ ⟶ M) (n₁ : N₁ ⟶ N) [Mono m₁] [Mono n₁]
        (b₁ : E.obj M₁ ⟶ N₁),
      E.map m₁ ≫ b = b₁ ≫ n₁ →
      ∃ (M₂ : CochainComplex (ModuleCat.{max u v w} A) ℤ)
        (N₂ : CochainComplex (ModuleCat.{max u v w} B) ℤ)
        (m₂ : M₂ ⟶ M) (n₂ : N₂ ⟶ N),
        Cardinal.mk ((Σ i : ℤ, M₂.X i) ⊕ (Σ i : ℤ, N₂.X i)) ≤
            max (Cardinal.lift.{w} κ)
              (Cardinal.mk ((Σ i : ℤ, M₁.X i) ⊕ (Σ i : ℤ, N₁.X i))) ∧
          ∀ (M' : CochainComplex (ModuleCat.{max u v w} A) ℤ)
            (N' : CochainComplex (ModuleCat.{max u v w} B) ℤ)
            (m' : M' ⟶ M) (n' : N' ⟶ N) (_ : Mono m') (_ : Mono n')
            (p : M₁ ⟶ M') (q : N₁ ⟶ N') (b' : E.obj M' ⟶ N'),
            p ≫ m' = m₁ → q ≫ n' = n₁ → E.map m' ≫ b = b' ≫ n' →
            (∀ i, Set.range (m₂.f i) ⊆ Set.range (m'.f i)) →
            (∀ i, Set.range (n₂.f i) ⊆ Set.range (n'.f i)) →
            (∀ (i : ℤ)
              (x : (DerivedCategory.homologyFunctor (ModuleCat.{max u v w} B) i).obj
                (T.obj (DerivedCategory.Q.obj M₁))),
              ((DerivedCategory.homologyFunctor (ModuleCat.{max u v w} B) i).map
                  (α.app M₁ ≫ DerivedCategory.Q.map b₁)) x = 0 →
                ((DerivedCategory.homologyFunctor (ModuleCat.{max u v w} B) i).map
                  (T.map (DerivedCategory.Q.map p))) x = 0) ∧
            (∀ (i : ℤ)
              (y : (DerivedCategory.homologyFunctor (ModuleCat.{max u v w} B) i).obj
                (DerivedCategory.Q.obj N₁)),
              ∃ x : (DerivedCategory.homologyFunctor (ModuleCat.{max u v w} B) i).obj
                (T.obj (DerivedCategory.Q.obj M')),
                ((DerivedCategory.homologyFunctor (ModuleCat.{max u v w} B) i).map
                    (α.app M' ≫ DerivedCategory.Q.map b')) x =
                  ((DerivedCategory.homologyFunctor (ModuleCat.{max u v w} B) i).map
                    (DerivedCategory.Q.map q)) y) := by
  obtain ⟨κ, hκ⟩ := exists_enlargements_killing_kernel_and_covering_image.{u, v, w} f
  refine ⟨κ, ?_⟩
  intro E T α hT M N b hb M₁ N₁ m₁ n₁ hm₁ hn₁ b₁ hcomm
  obtain ⟨M₂, N₂, m₂, n₂, _, _, m₁₂, n₁₂, _, _, b₂, hmfac, hnfac, hbfac, hker, himg, hsize⟩ :=
    hκ T α M N b hb M₁ N₁ m₁ n₁ b₁ hcomm
  refine ⟨M₂, N₂, m₂, n₂, hsize, ?_⟩
  intro M' N' m' n' _ _ p q b' hp hq hb' hMr hNr
  obtain ⟨χ, hχ⟩ := exists_lift_of_range_subset m₂ m' hMr
  obtain ⟨ψ, hψ⟩ := exists_lift_of_range_subset n₂ n' hNr
  have hpχ : m₁₂ ≫ χ = p := by
    rw [← cancel_mono m', Category.assoc, hχ, hmfac, hp]
  have hqψ : n₁₂ ≫ ψ = q := by
    rw [← cancel_mono n', Category.assoc, hψ, hnfac, hq]
  have hsq : E.map χ ≫ b' = b₂ ≫ ψ := by
    rw [← cancel_mono n', Category.assoc, Category.assoc, hψ, ← hb', ← Category.assoc,
      ← Functor.map_comp, hχ, (hbfac : E.map m₂ ≫ b = b₂ ≫ n₂)]
  refine ⟨fun i x hx => ?_, fun i y => ?_⟩
  · rw [← hpχ]
    simp only [Functor.map_comp, ModuleCat.comp_apply]
    rw [forall_of_kernel_comp_eq_zero _ _ (hker i) x hx, map_zero]
  · obtain ⟨x', hx'⟩ := forall_exists_of_imageSubobject_le _ _ (himg i) y
    refine ⟨(DerivedCategory.homologyFunctor (ModuleCat.{max u v w} B) i).map
      (T.map (DerivedCategory.Q.map χ)) x', ?_⟩
    have hcs := ConcreteCategory.congr_hom
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v w} B) i).congr_map
        (comparison_square α χ ψ b₂ b' hsq)) x'
    simp only [Functor.comp_map, Functor.map_comp, ModuleCat.comp_apply] at hcs hx' ⊢
    rw [hcs, hx', ← ModuleCat.comp_apply, ← Functor.map_comp, ← Functor.map_comp, hqψ]

end Stacks.SubcomplexEnlargement

end
