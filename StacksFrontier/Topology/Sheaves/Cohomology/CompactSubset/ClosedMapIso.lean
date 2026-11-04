module

public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.CohomologyOfClosedMap
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Cohomology on a quasi-compact separated subset is the colimit over its neighbourhoods

Let `X` be a topological space, let `Z ⊆ X` be a quasi-compact subset any two distinct points of
which have disjoint open neighbourhoods in `X`, and let `F` be a sheaf of abelian groups on `X`.
The canonical comparison map

`Stacks.Topology.cohomologyOfClosedMap : colim_{U ⊇ Z open} H^p(U, F) ⟶ H^p(Z, F|_Z)`,

is an isomorphism in every degree.

## Main results

* `Stacks.Topology.surjective_cohomologyOfClosedMap_succ` and
  `Stacks.Topology.injective_cohomologyOfClosedMap_succ`: if the comparison map is bijective in
  degree `p` for every abelian sheaf, then it is surjective, respectively injective, in degree
  `p + 1` for the first term of a short exact sequence with injective middle term.
* `Stacks.Topology.bijective_cohomologyOfClosedMap`: the comparison map is bijective in every
  degree.
* `Stacks.Topology.isIso_cohomologyOfClosedMap`: the comparison map is an isomorphism in every
  degree.

## References

* [Stacks Project, Tag 09V3](https://stacks.math.columbia.edu/tag/09V3)
* [SGA 4, Expose V bis, 4.1.3]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat Abelian
open Stacks.Cohomology.FreeYoneda

namespace Stacks.Topology

universe u

noncomputable section

variable {X : TopCat.{u}} (Z : Set X)

/-- Shrinking an open neighbourhood of `Z` induces a map of free abelian sheaves. -/
abbrev freeNhdsMap {U V : (OpenNhdsSet Z)ᵒᵖ} (a : U ⟶ V) :
    (freeYoneda (Opens.grothendieckTopology X)).obj V.unop.obj ⟶
      (freeYoneda (Opens.grothendieckTopology X)).obj U.unop.obj :=
  (freeYoneda (Opens.grothendieckTopology X)).map ((openNhdsSetInclusion Z).map a.unop)

section Diagram

variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
  (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})

/-- The restriction maps of the neighbourhood-cohomology diagram are precomposition with the
induced map of free abelian sheaves. -/
theorem openNeighborhoodCohomology_map_apply (p : ℕ) {U V : (OpenNhdsSet Z)ᵒᵖ} (a : U ⟶ V)
    (x : Ext.{u} ((freeYoneda (Opens.grothendieckTopology X)).obj U.unop.obj) F p) :
    (openNeighborhoodCohomology Z F p).map a x =
      Ext.comp (Ext.mk₀ (freeNhdsMap Z a)) x (zero_add p) :=
  rfl

/-- Every element of the colimit over the open neighbourhoods of `Z` is the class of an
`Ext`-class on one of them. -/
theorem exists_colimit_ι_ext (p : ℕ)
    (t : ToType (colimit (openNeighborhoodCohomology Z F p))) :
    ∃ (U : (OpenNhdsSet Z)ᵒᵖ)
      (x : Ext.{u} ((freeYoneda (Opens.grothendieckTopology X)).obj U.unop.obj) F p),
      colimit.ι (openNeighborhoodCohomology Z F p) U x = t :=
  exists_colimit_ι_openNeighborhoodCohomology Z F p t

/-- Two classes on open neighbourhoods of `Z` defining the same element of the colimit agree
after restriction to a smaller neighbourhood. -/
theorem exists_map_eq_of_colimit_ι_eq (p : ℕ) {U V : (OpenNhdsSet Z)ᵒᵖ}
    (x : ToType ((openNeighborhoodCohomology Z F p).obj U))
    (y : ToType ((openNeighborhoodCohomology Z F p).obj V))
    (h : colimit.ι (openNeighborhoodCohomology Z F p) U x =
      colimit.ι (openNeighborhoodCohomology Z F p) V y) :
    ∃ (W : (OpenNhdsSet Z)ᵒᵖ) (f : U ⟶ W) (g : V ⟶ W),
      (openNeighborhoodCohomology Z F p).map f x =
        (openNeighborhoodCohomology Z F p).map g y :=
  Concrete.colimit_exists_of_rep_eq.{u} _ x y h

/-- Two `Ext`-classes on open neighbourhoods of `Z` defining the same element of the colimit
agree after precomposition with the maps induced by the inclusions of a smaller neighbourhood. -/
theorem exists_comp_eq_of_colimit_ι_eq (p : ℕ) {U V : (OpenNhdsSet Z)ᵒᵖ}
    (x : Ext.{u} ((freeYoneda (Opens.grothendieckTopology X)).obj U.unop.obj) F p)
    (y : Ext.{u} ((freeYoneda (Opens.grothendieckTopology X)).obj V.unop.obj) F p)
    (h : colimit.ι (openNeighborhoodCohomology Z F p) U x =
      colimit.ι (openNeighborhoodCohomology Z F p) V y) :
    ∃ (W : (OpenNhdsSet Z)ᵒᵖ) (f : U ⟶ W) (g : V ⟶ W),
      Ext.comp (Ext.mk₀ (freeNhdsMap Z f)) x (zero_add p) =
        Ext.comp (Ext.mk₀ (freeNhdsMap Z g)) y (zero_add p) :=
  exists_map_eq_of_colimit_ι_eq Z F p x y h

/-- A class vanishing on a smaller open neighbourhood of `Z` is zero in the colimit. -/
theorem colimit_ι_eq_zero_of_map_eq_zero (p : ℕ) {U W : (OpenNhdsSet Z)ᵒᵖ} (f : U ⟶ W)
    (x : ToType ((openNeighborhoodCohomology Z F p).obj U))
    (h : (openNeighborhoodCohomology Z F p).map f x = 0) :
    colimit.ι (openNeighborhoodCohomology Z F p) U x = 0 :=
  (((ConcreteCategory.congr_hom
      (colimit.w (openNeighborhoodCohomology Z F p) f) x).symm).trans
    (ConcreteCategory.comp_apply _ _ x)).trans
    ((congrArg (colimit.ι (openNeighborhoodCohomology Z F p) W) h).trans
      (map_zero (ConcreteCategory.hom (colimit.ι (openNeighborhoodCohomology Z F p) W))))

/-- An `Ext`-class on an open neighbourhood of `Z` whose precomposition with the map induced by
the inclusion of a smaller neighbourhood vanishes is zero in the colimit. -/
theorem colimit_ι_eq_zero_of_comp_eq_zero (p : ℕ) {U W : (OpenNhdsSet Z)ᵒᵖ} (f : U ⟶ W)
    (x : Ext.{u} ((freeYoneda (Opens.grothendieckTopology X)).obj U.unop.obj) F p)
    (h : Ext.comp (Ext.mk₀ (freeNhdsMap Z f)) x (zero_add p) = 0) :
    colimit.ι (openNeighborhoodCohomology Z F p) U x = 0 :=
  colimit_ι_eq_zero_of_map_eq_zero Z F p f x h

end Diagram

/-- Associativity of `Ext`-composition when the first factor is a degree-zero class. -/
private theorem mk₀_comp_comp_assoc {C : Type*} [Category C] [Abelian C] {A B D E : C}
    [HasExt.{u} C] (f : A ⟶ B) {a c n : ℕ} (β : Ext B D a) (γ : Ext D E c) (h : a + c = n) :
    (Ext.mk₀ f).comp (β.comp γ h) (zero_add n) = ((Ext.mk₀ f).comp β (zero_add a)).comp γ h :=
  (Ext.comp_assoc _ _ _ (zero_add a) h (by lia)).symm

section DimensionShift

variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
  [HasExt.{u} (Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{u})]
  (hZ : IsCompact Z)
  (hSep : ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y →
    ∃ A B : Set X, IsOpen A ∧ IsOpen B ∧ x ∈ A ∧ y ∈ B ∧ Disjoint A B)
  (p : ℕ)
  (ih : ∀ G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u},
    Function.Bijective (cohomologyOfClosedMap Z G p))
  (S : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
  (hS : S.ShortExact) (hinj : Injective S.X₂)

include hZ hSep ih hS hinj in
/-- If the comparison map in degree `p` is bijective for every abelian sheaf on `X`, then it is
surjective in degree `p + 1` for the first term of a short exact sequence whose middle term is
injective. -/
theorem surjective_cohomologyOfClosedMap_succ :
    Function.Surjective (cohomologyOfClosedMap Z S.X₁ (p + 1)) := by
  have := hinj
  have hLS : (S.map (restrictionFunctor X Z)).ShortExact :=
    hS.map_of_exact (restrictionFunctor X Z)
  intro y
  have hy0 : Ext.comp y (Ext.mk₀ (S.map (restrictionFunctor X Z)).f) (add_zero (p + 1)) = 0 :=
    ext_eq_zero_of_injective_restriction Z S.X₂ hZ hSep (p + 1) p.succ_pos _
  obtain ⟨x₃, hx₃⟩ := Ext.covariant_sequence_exact₁
    ((freeYoneda (Opens.grothendieckTopology (TopCat.of Z))).obj ⊤) hLS y hy0 rfl
  obtain ⟨c, hc⟩ := (ih S.X₃).2 x₃
  obtain ⟨U, xU, rfl⟩ := exists_colimit_ι_ext Z S.X₃ p c
  refine ⟨colimit.ι (openNeighborhoodCohomology Z S.X₁ (p + 1)) U
    (Ext.comp xU hS.extClass rfl), ?_⟩
  refine (cohomologyOfClosedMap_ι_comp Z hS.extClass p (p + 1) rfl U xU).trans ?_
  rw [hc, Ext.mapExactFunctor_extClass]
  exact hx₃

include ih hS hinj in
/-- If the comparison map in degree `p` is bijective for every abelian sheaf on `X`, then it is
injective in degree `p + 1` for the first term of a short exact sequence whose middle term is
injective. -/
theorem injective_cohomologyOfClosedMap_succ :
    Function.Injective (cohomologyOfClosedMap Z S.X₁ (p + 1)) := by
  have := hinj
  have hLS : (S.map (restrictionFunctor X Z)).ShortExact :=
    hS.map_of_exact (restrictionFunctor X Z)
  suffices hker : ∀ c : ToType (colimit (openNeighborhoodCohomology Z S.X₁ (p + 1))),
      cohomologyOfClosedMap Z S.X₁ (p + 1) c = 0 → c = 0 from
    (injective_iff_map_eq_zero
      (ConcreteCategory.hom (cohomologyOfClosedMap Z S.X₁ (p + 1)))).mpr hker
  intro c hc0
  obtain ⟨U, x, rfl⟩ := exists_colimit_ι_ext Z S.X₁ (p + 1) c
  have h1 : Ext.comp x (Ext.mk₀ S.f) (add_zero (p + 1)) = 0 := Ext.eq_zero_of_injective _
  obtain ⟨b, hb⟩ := Ext.covariant_sequence_exact₁
    ((freeYoneda (Opens.grothendieckTopology X)).obj U.unop.obj) hS x h1 rfl
  have h2 : Ext.comp (cohomologyOfClosedMap Z S.X₃ p
        (colimit.ι (openNeighborhoodCohomology Z S.X₃ p) U b))
      (Ext.mapExactFunctor (restrictionFunctor X Z) hS.extClass) rfl = 0 :=
    (cohomologyOfClosedMap_ι_comp Z hS.extClass p (p + 1) rfl U b).symm.trans
      ((congrArg (fun t ↦ cohomologyOfClosedMap Z S.X₁ (p + 1)
        (colimit.ι (openNeighborhoodCohomology Z S.X₁ (p + 1)) U t)) hb).trans hc0)
  have h3 : Ext.comp (cohomologyOfClosedMap Z S.X₃ p
        (colimit.ι (openNeighborhoodCohomology Z S.X₃ p) U b)) hLS.extClass rfl = 0 := by
    rwa [← Ext.mapExactFunctor_extClass (restrictionFunctor X Z) hS]
  obtain ⟨x₂, hx₂⟩ := Ext.covariant_sequence_exact₃
    ((freeYoneda (Opens.grothendieckTopology (TopCat.of Z))).obj ⊤) hLS _ rfl h3
  obtain ⟨d, hd⟩ := (ih S.X₂).2 x₂
  obtain ⟨V, yV, rfl⟩ := exists_colimit_ι_ext Z S.X₂ p d
  have h4 : colimit.ι (openNeighborhoodCohomology Z S.X₃ p) U b =
      colimit.ι (openNeighborhoodCohomology Z S.X₃ p) V
        (Ext.comp yV (Ext.mk₀ S.g) (add_zero p)) := by
    refine (ih S.X₃).1 ?_
    refine Eq.trans ?_
      (cohomologyOfClosedMap_ι_comp Z (Ext.mk₀ S.g) p p (add_zero p) V yV).symm
    rw [hd, Ext.mapExactFunctor_mk₀]
    exact hx₂.symm
  obtain ⟨W, g, f, hfg⟩ := exists_comp_eq_of_colimit_ι_eq Z S.X₃ p b _ h4
  refine colimit_ι_eq_zero_of_comp_eq_zero Z S.X₁ (p + 1) g x ?_
  have hy' : Ext.comp (Ext.comp yV (Ext.mk₀ S.g) (add_zero p)) hS.extClass rfl = 0 := by
    rw [Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass, Ext.comp_zero]
  rw [← hb, mk₀_comp_comp_assoc, hfg, ← mk₀_comp_comp_assoc, hy', Ext.comp_zero]

end DimensionShift

section Induction

variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
  [HasExt.{u} (Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{u})]
  (hZ : IsCompact Z)
  (hSep : ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y →
    ∃ A B : Set X, IsOpen A ∧ IsOpen B ∧ x ∈ A ∧ y ∈ B ∧ Disjoint A B)

include hZ hSep in
/-- For a quasi-compact subset `Z` of `X` any two distinct points of which have disjoint open
neighbourhoods in `X`, the comparison map from the colimit of the cohomology of an abelian sheaf
`F` over the open neighbourhoods of `Z` to the cohomology of `F|_Z` is bijective in every
degree. -/
theorem bijective_cohomologyOfClosedMap (p : ℕ) :
    ∀ F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u},
      Function.Bijective (cohomologyOfClosedMap Z F p) := by
  induction p with
  | zero =>
    intro F
    have := isIso_cohomologyOfClosedMap_zero Z F hZ hSep
    exact ConcreteCategory.bijective_of_isIso _
  | succ p ih =>
    intro F
    obtain ⟨S, hS, hinjF, rfl⟩ :
        ∃ (S : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
          (_ : S.ShortExact) (_ : Injective S.X₂), S.X₁ = F :=
      ⟨ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F))
          (cokernel.condition (Injective.ι F)),
        { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel (Injective.ι F)) },
        Injective.injective_under F, rfl⟩
    exact ⟨injective_cohomologyOfClosedMap_succ Z p ih S hS hinjF,
      surjective_cohomologyOfClosedMap_succ Z hZ hSep p ih S hS hinjF⟩

include hZ hSep in
/-- For a quasi-compact subset `Z` of a topological space `X` any two
distinct points of which have disjoint open neighbourhoods in `X`, the canonical map from the
colimit of the cohomology of an abelian sheaf `F` over the open neighbourhoods of `Z` to the
cohomology of the restriction of `F` to `Z` is an isomorphism in every degree. -/
@[stacks 09V3, sga "4 Vbis 4.1.3"]
theorem isIso_cohomologyOfClosedMap
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (p : ℕ) :
    IsIso (cohomologyOfClosedMap Z F p) := by
  suffices IsIso ((CategoryTheory.forget AddCommGrpCat.{u}).map
      (cohomologyOfClosedMap Z F p)) from
    isIso_of_reflects_iso (cohomologyOfClosedMap Z F p) (CategoryTheory.forget AddCommGrpCat.{u})
  rw [isIso_iff_bijective]
  exact bijective_cohomologyOfClosedMap Z hZ hSep p F

end Induction

end

end Stacks.Topology

end
