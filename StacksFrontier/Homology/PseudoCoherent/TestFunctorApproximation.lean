module

public import StacksFrontier.Homology.PseudoCoherent.Basic
public import StacksFrontier.Homology.PseudoCoherent.Homology
public import StacksFrontier.Homology.PseudoCoherent.Triangle
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.Triangulated.Triangulated

/-!
# Approximating an object by cells seen through pseudo-coherent test functors

Let `D` be a triangulated category, `R` a ring, `G k` finitely many objects of `D` and `F i`
finitely many triangulated functors `D ⥤ D(R)` such that every `F i (G k)` is concentrated in
degrees `≤ 0`, and every class in `Hʲ(F i X)` comes from a morphism `G k⟦-j⟧ ⟶ X`. If
`F i K` is pseudo-coherent for every `i`, then for every `m` there is a distinguished triangle
`Y ⟶ K ⟶ Z ⟶ Y⟦1⟧` with `Y` built from the `G k` by finitely many shifts, finite direct sums and
extensions, and `Hʲ(F i Z) = 0` for all `i` and all `j ≥ m`.

This is the descending induction of the proof of Stacks 0CSF, run in `D` itself rather than in
the derived category of a ring: at each step the top cohomology of the cone is a finite
`R`-module (Stacks 064S), generators of it are realised by maps from shifts of the `G k`, and the
octahedral axiom attaches the corresponding cells.

## Main results

* `StacksDraft.PseudoCoherence.exists_distTriang_isZero_homology_of_isPseudoCoherent`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

attribute [local instance] HasDerivedCategory.standard

namespace StacksDraft.PseudoCoherence

universe u v w t

variable {D : Type w} [Category.{t} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
  [HasFiniteBiproducts D]
  {R : Type u} [Ring R]

/-- A pseudo-coherent object of `D(R)` has vanishing cohomology in all large degrees. -/
theorem exists_isZero_homology_of_isPseudoCoherent {K : DerivedCategory (ModuleCat.{v} R)}
    (hK : IsPseudoCoherent K) :
    ∃ b : ℤ, ∀ j : ℤ, b ≤ j →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) j).obj K) := by
  obtain ⟨E, hE, ⟨e⟩⟩ := hK
  obtain ⟨b, hb⟩ := hE.upperBound
  have hQ : (DerivedCategory.Q.obj E).IsLE b :=
    (DerivedCategory.isLE_Q_obj_iff E b).2 inferInstance
  refine ⟨b + 1, fun j hj => ?_⟩
  exact (((DerivedCategory.isLE_iff _ b).1 hQ) j (by omega)).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) j).mapIso e).symm

/-- A finite direct sum of zero objects is zero. -/
theorem isZero_biproduct {C : Type*} [Category C] [Preadditive C] {J : Type*} [Finite J]
    {f : J → C} [HasBiproduct f] (h : ∀ j, IsZero (f j)) : IsZero (⨁ f) := by
  rw [IsZero.iff_id_eq_zero]
  exact biproduct.hom_ext' _ _ fun j => (h j).eq_of_src _ _

variable {ι : Type} [Finite ι] {κ : Type*} (G : κ → D)
  (F : ι → D ⥤ DerivedCategory (ModuleCat.{v} R))
  [∀ i, (F i).CommShift ℤ] [∀ i, (F i).IsTriangulated]
  (P : ObjectProperty D) [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]

/-- **One step of the descending induction.** If `Y ⟶ K ⟶ Z ⟶ Y⟦1⟧` is distinguished with
`P Y` and `Hʲ(F i Z) = 0` for `j > m`, then cells attached along generators of the finite
modules `Hᵐ(F i Z)` give a distinguished triangle `Y' ⟶ K ⟶ Z' ⟶ Y'⟦1⟧` with `P Y'` and
`Hʲ(F i Z') = 0` for `j ≥ m`. -/
theorem exists_distTriang_isZero_homology_step
    (hle : ∀ i k, ((F i).obj (G k)).IsLE 0)
    (hGP : ∀ k, P (G k))
    (hPF : ∀ Y, P Y → ∀ i, IsPseudoCoherent ((F i).obj Y))
    (hsurj : ∀ i (X : D) (j : ℤ)
      (y : (DerivedCategory.homologyFunctor (ModuleCat.{v} R) j).obj ((F i).obj X)),
      ∃ (k : κ) (x : (G k)⟦-j⟧ ⟶ X)
        (z : (DerivedCategory.homologyFunctor (ModuleCat.{v} R) j).obj ((F i).obj ((G k)⟦-j⟧))),
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) j).map ((F i).map x)).hom z = y)
    (K : D) (hK : ∀ i, IsPseudoCoherent ((F i).obj K)) (m : ℤ)
    {Y Z : D} (α : Y ⟶ K) (β : K ⟶ Z) (γ : Z ⟶ Y⟦(1 : ℤ)⟧)
    (hT : Triangle.mk α β γ ∈ distTriang D) (hY : P Y)
    (hZ : ∀ i j, m + 1 ≤ j →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) j).obj ((F i).obj Z))) :
    ∃ (Y' Z' : D) (α' : Y' ⟶ K) (β' : K ⟶ Z') (γ' : Z' ⟶ Y'⟦(1 : ℤ)⟧),
      Triangle.mk α' β' γ' ∈ distTriang D ∧ P Y' ∧
      ∀ i j, m ≤ j →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) j).obj ((F i).obj Z')) := by
  classical
  have := Fintype.ofFinite ι
  -- `F i Z` is pseudo-coherent, and its degree `m` cohomology is a finite `R`-module.
  have hFZ : ∀ i, IsPseudoCoherent ((F i).obj Z) := fun i =>
    (isPseudoCoherent_of_distinguished _ ((F i).map_distinguished _ hT)).1
      (hPF Y hY i) (hK i)
  have hfin : ∀ i,
      Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) m).obj ((F i).obj Z)) :=
    fun i => PseudoCoherence.finite_homology_of_isPseudoCoherentFrom _ m
      ((pseudoCoherent_iff_all _).1 (hFZ i) m) fun j hj => hZ i j (by omega)
  -- Generators, and the cells realising them.
  choose r s hs using fun i => (hfin i).exists_fin
  choose k x z hxz using fun (p : Σ i, Fin (r i)) => hsurj p.1 Z m (s p.1 p.2)
  let X : (Σ i, Fin (r i)) → D := fun p => (G (k p))⟦-m⟧
  let Q : D := ⨁ X
  let φ : Q ⟶ Z := biproduct.desc x
  have hQ : P Q := by
    refine P.prop_of_iso (biproduct.isoProduct X).symm (P.prop_limit _ fun p => ?_)
    exact P.le_shift (-m) _ (hGP _)
  -- `F i Q` vanishes in degrees `> m`.
  have hFQ : ∀ i j, m < j →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) j).obj ((F i).obj Q)) := by
    intro i j hj
    refine IsZero.of_iso ?_
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) j).mapIso ((F i).mapBiproduct X) ≪≫
      (DerivedCategory.homologyFunctor (ModuleCat.{v} R) j).mapBiproduct _)
    refine isZero_biproduct fun p => ?_
    have h₀ : ((F i).obj (G (k p))).IsLE 0 := hle i (k p)
    have h₁ : (((F i).obj (G (k p)))⟦-m⟧).IsLE m :=
      DerivedCategory.TStructure.t.isLE_shift _ 0 (-m) m (by omega)
    exact ((DerivedCategory.isLE_iff _ m).1 h₁ j hj).of_iso
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) j).mapIso
        (((F i).commShiftIso (-m)).app _))
  -- `Hᵐ(F i φ)` is surjective.
  have hepi : ∀ i,
      Epi ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) m).map ((F i).map φ)) := by
    intro i
    rw [ModuleCat.epi_iff_surjective, ← LinearMap.range_eq_top, eq_top_iff, ← hs i,
      Submodule.span_le]
    rintro _ ⟨t, rfl⟩
    refine ⟨((DerivedCategory.homologyFunctor (ModuleCat.{v} R) m).map
      ((F i).map (biproduct.ι X ⟨i, t⟩))).hom (z ⟨i, t⟩), ?_⟩
    rw [← hxz ⟨i, t⟩]
    show ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) m).map
      ((F i).map (biproduct.ι X ⟨i, t⟩)) ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{v} R) m).map ((F i).map φ)).hom (z ⟨i, t⟩) = _
    rw [← Functor.map_comp, ← Functor.map_comp, biproduct.ι_desc]
  -- The cone `Z'` of `φ`, and the octahedron.
  obtain ⟨Z', π, δ, hT₂⟩ := distinguished_cocone_triangle φ
  obtain ⟨Y', α', δ', hT₃⟩ := distinguished_cocone_triangle₁ (β ≫ π)
  let o := Triangulated.someOctahedron' rfl hT hT₂ hT₃
  have hY' : P Y' := P.ext_of_isTriangulatedClosed₂ _ o.mem hY hQ
  refine ⟨Y', Z', α', β ≫ π, δ', hT₃, hY', fun i j hj => ?_⟩
  -- Vanishing of `Hʲ(F i Z')` for `j ≥ m`, from the triangle `Q ⟶ Z ⟶ Z' ⟶ Q⟦1⟧`.
  have hT₂' := (F i).map_distinguished _ hT₂
  have hex := DerivedCategory.HomologySequence.exact₃ _ hT₂' j (j + 1) rfl
  refine hex.isZero_X₂ ?_ ((hFQ i (j + 1) (by omega)).eq_of_tgt _ _)
  rcases hj.eq_or_lt with rfl | hlt
  · exact (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff _ hT₂' m).1 (hepi i)
  · exact (hZ i j (by omega)).eq_of_src _ _

/-- A morphism `G ⟶ E X` is `η ≫ E x` for the unit `η` of `E⁻¹ ⊣ E` and some `x : E⁻¹ G ⟶ X`. -/
private theorem exists_eq_unit_comp_map {C : Type*} [Category C] (E : C ≌ C) {G X : C}
    (x' : G ⟶ E.functor.obj X) :
    ∃ x : E.inverse.obj G ⟶ X, x' = E.symm.toAdjunction.unit.app G ≫ E.symm.inverse.map x :=
  ⟨(E.symm.toAdjunction.homEquiv G X).symm x',
    ((E.symm.toAdjunction.homEquiv G X).apply_symm_apply x').symm.trans
      (E.symm.toAdjunction.homEquiv_unit G X _)⟩

omit [HasZeroObject D] [Preadditive D] [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]
  [IsTriangulated D] [HasFiniteBiproducts D] [Finite ι] [∀ (i : ι), (F i).IsTriangulated] in
/-- **Every degree from degree zero.** If every class in `H⁰(F i X)` comes from a morphism
`G k ⟶ X`, then every class in `Hʲ(F i X)` comes from a morphism `G k⟦-j⟧ ⟶ X`. -/
theorem exists_hom_shift_of_exists_hom
    (h0 : ∀ i (X : D) (y : (DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).obj
        ((F i).obj X)),
      ∃ (k : κ) (x : G k ⟶ X)
        (z : (DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).obj ((F i).obj (G k))),
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).map ((F i).map x)).hom z = y)
    (i : ι) (X : D) (j : ℤ)
    (y : (DerivedCategory.homologyFunctor (ModuleCat.{v} R) j).obj ((F i).obj X)) :
    ∃ (k : κ) (x : (G k)⟦-j⟧ ⟶ X)
      (z : (DerivedCategory.homologyFunctor (ModuleCat.{v} R) j).obj ((F i).obj ((G k)⟦-j⟧))),
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) j).map ((F i).map x)).hom z = y := by
  let H₀ := DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0
  -- `Hʲ(F i -) ≅ H⁰(F i (-⟦j⟧))`, naturally.
  let θ : F i ⋙ DerivedCategory.homologyFunctor (ModuleCat.{v} R) j ≅
      (shiftFunctor D j ⋙ F i) ⋙ H₀ :=
    Functor.isoWhiskerLeft (F i) (H₀.shiftIso j 0 j (add_zero j)).symm ≪≫
      Functor.isoWhiskerRight ((F i).commShiftIso j).symm H₀
  obtain ⟨k, x', z', hx'⟩ := h0 i (X⟦j⟧) ((θ.hom.app X).hom y)
  obtain ⟨x : (G k)⟦-j⟧ ⟶ X, hx⟩ := exists_eq_unit_comp_map (shiftEquiv D j) x'
  let η := (shiftEquiv D j).symm.toAdjunction.unit.app (G k)
  let w := (θ.inv.app ((G k)⟦-j⟧)).hom ((H₀.map ((F i).map η)).hom z')
  refine ⟨k, x, w, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso (θ.hom.app X)).1
  have hnat := ConcreteCategory.congr_hom (θ.hom.naturality x) w
  have hw : (θ.hom.app ((G k)⟦-j⟧)).hom w = (H₀.map ((F i).map η)).hom z' :=
    ConcreteCategory.congr_hom (θ.inv_hom_id_app ((G k)⟦-j⟧)) _
  show (θ.hom.app X).hom (((DerivedCategory.homologyFunctor (ModuleCat.{v} R) j).map
    ((F i).map x)).hom w) = _
  refine ((ConcreteCategory.comp_apply ((F i ⋙ DerivedCategory.homologyFunctor
    (ModuleCat.{v} R) j).map x) (θ.hom.app X) w).symm.trans hnat).trans ?_
  refine (ConcreteCategory.comp_apply _ _ w).trans ?_
  rw [hw, ← hx']
  show (H₀.map ((F i).map ((shiftEquiv D j).symm.inverse.map x))).hom
    ((H₀.map ((F i).map η)).hom z') = _
  rw [hx]
  exact ((ConcreteCategory.congr_hom (congrArg H₀.map ((F i).map_comp η
    ((shiftEquiv D j).symm.inverse.map x))) z').trans
      ((ConcreteCategory.congr_hom (H₀.map_comp _ _) z').trans
        (ConcreteCategory.comp_apply _ _ z'))).symm

omit [HasZeroObject D] [HasShift D ℤ] [Preadditive D] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [Pretriangulated D] [IsTriangulated D] [HasFiniteBiproducts D] in
/-- **Transport along an autoequivalence.** If every class in `H⁰(F X)` comes from a morphism
`G ⟶ X`, then every class in `H⁰(F (E X))` comes from a morphism `E⁻¹ G ⟶ X`, read through `E`. -/
theorem exists_hom_of_equivalence (E : D ≌ D) (F₀ : D ⥤ DerivedCategory (ModuleCat.{v} R))
    (G₀ : D)
    (h0 : ∀ (X : D) (y : (DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).obj (F₀.obj X)),
      ∃ (x : G₀ ⟶ X)
        (z : (DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).obj (F₀.obj G₀)),
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).map (F₀.map x)).hom z = y)
    (X : D) (y : (DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).obj
      ((E.functor ⋙ F₀).obj X)) :
    ∃ (x : E.inverse.obj G₀ ⟶ X)
      (z : (DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).obj
        ((E.functor ⋙ F₀).obj (E.inverse.obj G₀))),
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).map
        ((E.functor ⋙ F₀).map x)).hom z = y := by
  let H₀ := DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0
  obtain ⟨x', z', hx'⟩ := h0 (E.functor.obj X) y
  obtain ⟨x, hx⟩ := exists_eq_unit_comp_map E x'
  let η := E.symm.toAdjunction.unit.app G₀
  refine ⟨x, (H₀.map (F₀.map η)).hom z', ?_⟩
  rw [← hx', hx, Functor.map_comp, Functor.map_comp]
  rfl

/-- **Approximation by cells, detected by pseudo-coherent test functors.** If `F i K` is
pseudo-coherent for every `i`, then for every `m` there is a distinguished triangle
`Y ⟶ K ⟶ Z ⟶ Y⟦1⟧` with `P Y` and `Hʲ(F i Z) = 0` for all `i` and all `j ≥ m`. -/
theorem exists_distTriang_isZero_homology_of_isPseudoCoherent
    (hle : ∀ i k, ((F i).obj (G k)).IsLE 0)
    (hGP : ∀ k, P (G k))
    (hPF : ∀ Y, P Y → ∀ i, IsPseudoCoherent ((F i).obj Y))
    (hsurj : ∀ i (X : D) (j : ℤ)
      (y : (DerivedCategory.homologyFunctor (ModuleCat.{v} R) j).obj ((F i).obj X)),
      ∃ (k : κ) (x : (G k)⟦-j⟧ ⟶ X)
        (z : (DerivedCategory.homologyFunctor (ModuleCat.{v} R) j).obj ((F i).obj ((G k)⟦-j⟧))),
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) j).map ((F i).map x)).hom z = y)
    (K : D) (hK : ∀ i, IsPseudoCoherent ((F i).obj K)) (m : ℤ) :
    ∃ (Y Z : D) (α : Y ⟶ K) (β : K ⟶ Z) (γ : Z ⟶ Y⟦(1 : ℤ)⟧),
      Triangle.mk α β γ ∈ distTriang D ∧ P Y ∧
      ∀ i j, m ≤ j →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) j).obj ((F i).obj Z)) := by
  choose b hb using fun i => exists_isZero_homology_of_isPseudoCoherent (hK i)
  obtain ⟨c, hc⟩ := (Set.finite_range b).bddAbove
  have hc' : ∀ i, b i ≤ c := fun i => hc ⟨i, rfl⟩
  -- Induction on the distance `c - m`.
  suffices H : ∀ N : ℕ, ∃ (Y Z : D) (α : Y ⟶ K) (β : K ⟶ Z) (γ : Z ⟶ Y⟦(1 : ℤ)⟧),
      Triangle.mk α β γ ∈ distTriang D ∧ P Y ∧
      ∀ i j, c - N ≤ j →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) j).obj ((F i).obj Z)) by
    obtain ⟨Y, Z, α, β, γ, hT, hY, hZ⟩ := H (c - m).toNat
    exact ⟨Y, Z, α, β, γ, hT, hY, fun i j hj => hZ i j (by omega)⟩
  intro N
  induction N with
  | zero =>
    exact ⟨0, K, 0, 𝟙 K, 0, contractible_distinguished₁ K, P.prop_zero,
      fun i j hj => hb i j (by have := hc' i; omega)⟩
  | succ N ih =>
    obtain ⟨Y, Z, α, β, γ, hT, hY, hZ⟩ := ih
    exact exists_distTriang_isZero_homology_step G F P hle hGP hPF hsurj K hK (c - (N + 1))
      α β γ hT hY fun i j hj => hZ i j (by omega)

end StacksDraft.PseudoCoherence

end
