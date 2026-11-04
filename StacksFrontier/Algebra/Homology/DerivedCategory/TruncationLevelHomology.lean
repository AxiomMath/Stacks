module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncGELTSingle

/-! # Homology and the truncation levels of a derived category

Let `A` be an abelian category and let `X` be an object of its unbounded derived category. This
file records how the canonical truncations of `X` for the standard t-structure interact with the
cohomology objects `H^j(X)`, and compares two truncation levels from below by a distinguished
triangle.

Three things are proved. First, `H^j` turns the truncation map `X ⟶ τ_{≥ a}X` into an isomorphism
when `a ≤ j`, and the map `τ_{< b}X ⟶ X` into an isomorphism when `j < b`: in both cases the
third vertex of the defining triangle has no cohomology in the two relevant degrees. Second, for
`a ≤ b` there is a distinguished triangle

`τ_{< b}(τ_{≥ a}X) ⟶ τ_{≥ a}X ⟶ τ_{≥ b}X ⟶ (τ_{< b}(τ_{≥ a}X))⟦1⟧`

whose second map is the canonical comparison
`CategoryTheory.Triangulated.TStructure.natTransTruncGEOfLE`; it is the triangle of Mathlib's
`CategoryTheory.Triangulated.TStructure.triangleLTGE` at the object `τ_{≥ a}X`, with its third
vertex transported along the isomorphism `τ_{≥ b}X ≅ τ_{≥ b}(τ_{≥ a}X)`. Third, in the one-step
case `b = a + 1` the first vertex is the cohomology object `H^a(X)` placed in degree `a`.

Together these say that passing from `τ_{≥ a + 1}X` to `τ_{≥ a}X` adds exactly `H^a(X)` in degree
`a`, in the form of a distinguished triangle. That is what makes a tower of truncations from below
eventually constant after any functor which kills the single object `H^a(X)` outside degree `a`,
which is the use in Stacks 0BKZ.

## Main results

* `DerivedCategory.isIso_homologyMap_truncGEπ_app`,
  `Stacks.TruncationLevel.isIso_homologyMap_truncLTι_app`,
  `Stacks.TruncationLevel.isIso_homologyMap_truncLEι_app`: the truncation maps are isomorphisms
  on cohomology in the degrees the truncation retains.
* `Stacks.TruncationLevel.truncGELECompHomologyIso`: `H^p(τ^{≥p}τ^{≤p}K) ≅ H^p(K)`, naturally
  in `K`.
* `Stacks.TruncationLevel.exists_distTriang_truncGE`: the distinguished triangle comparing two
  truncation levels from below.
* `Stacks.TruncationLevel.nonempty_iso_singleFunctor_truncLTGE`: the one-step interval truncation
  is `H^a(X)` placed in degree `a`.

## Implementation notes

The two homology lemmas are both instances of a single observation about a distinguished triangle
of `D(A)`: a map is inverted by `H^j` as soon as the cohomology of the opposite vertex vanishes in
the two degrees adjacent to `j` on the correct side. That is recorded separately as
`Stacks.TruncationLevel.isIso_homologyMap_mor₂` and
`Stacks.TruncationLevel.isIso_homologyMap_mor₁`; `D(A)` is not abelian, but the cohomology objects
live in `A`, which is, so a map inverted on both sides by `Mono` and `Epi` is invertible there.

The comparison triangle is stated as the existence of a connecting map rather than as a named
triangle, because no consumer needs that map and naming it would commit to one of the two
transports available.

## References

* [Stacks Project, Tag 0BKZ](https://stacks.math.columbia.edu/tag/0BKZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

namespace Stacks.TruncationLevel

universe w v u

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- In a distinguished triangle of `D(A)`, the second map is inverted by degree-`j` cohomology as
soon as the first vertex has no cohomology in degrees `j` and `j + 1`. -/
lemma isIso_homologyMap_mor₂ (T : Triangle (DerivedCategory A))
    (hT : T ∈ distTriang (DerivedCategory A)) (j : ℤ)
    (h₀ : IsZero ((DerivedCategory.homologyFunctor A j).obj T.obj₁))
    (h₁ : IsZero ((DerivedCategory.homologyFunctor A (j + 1)).obj T.obj₁)) :
    IsIso ((DerivedCategory.homologyFunctor A j).map T.mor₂) := by
  have hmono : Mono ((DerivedCategory.homologyFunctor A j).map T.mor₂) := by
    rw [DerivedCategory.HomologySequence.mono_homologyMap_mor₂_iff T hT j]
    exact h₀.eq_of_src _ _
  have hepi : Epi ((DerivedCategory.homologyFunctor A j).map T.mor₂) := by
    rw [DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff T hT j (j + 1) rfl]
    exact h₁.eq_of_tgt _ _
  exact isIso_of_mono_of_epi _

/-- In a distinguished triangle of `D(A)`, the first map is inverted by degree-`j` cohomology as
soon as the third vertex has no cohomology in degrees `j` and `j - 1`. -/
lemma isIso_homologyMap_mor₁ (T : Triangle (DerivedCategory A))
    (hT : T ∈ distTriang (DerivedCategory A)) (j : ℤ)
    (h₀ : IsZero ((DerivedCategory.homologyFunctor A j).obj T.obj₃))
    (h₁ : IsZero ((DerivedCategory.homologyFunctor A (j - 1)).obj T.obj₃)) :
    IsIso ((DerivedCategory.homologyFunctor A j).map T.mor₁) := by
  have hmono : Mono ((DerivedCategory.homologyFunctor A j).map T.mor₁) := by
    rw [DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff T hT (j - 1) j (by omega)]
    exact h₁.eq_of_src _ _
  have hepi : Epi ((DerivedCategory.homologyFunctor A j).map T.mor₁) := by
    rw [DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT j]
    exact h₀.eq_of_tgt _ _
  exact isIso_of_mono_of_epi _

/-- Truncation from above (strictly) at `b` does not change the cohomology in degrees `< b`. -/
lemma isIso_homologyMap_truncLTι_app (b j : ℤ) (hjb : j < b) (X : DerivedCategory A) :
    IsIso ((DerivedCategory.homologyFunctor A j).map
      ((DerivedCategory.TStructure.t.truncLTι b).app X)) :=
  isIso_homologyMap_mor₁ ((DerivedCategory.TStructure.t.triangleLTGE b).obj X)
    (DerivedCategory.TStructure.t.triangleLTGE_distinguished b X) j
    (DerivedCategory.isZero_of_isGE _ b j (by omega))
    (DerivedCategory.isZero_of_isGE _ b (j - 1) (by omega))

/-- Truncation from above (inclusively) at `b` does not change the cohomology in degrees
`≤ b`. This is `Stacks.TruncationLevel.isIso_homologyMap_truncLTι_app` read through
`CategoryTheory.Triangulated.TStructure.truncLEIsoTruncLT`, which identifies `τ^{≤b}` with
`τ^{<b+1}` over the identity of the ambient object. -/
lemma isIso_homologyMap_truncLEι_app (b j : ℤ) (hjb : j ≤ b) (X : DerivedCategory A) :
    IsIso ((DerivedCategory.homologyFunctor A j).map
      ((DerivedCategory.TStructure.t.truncLEι b).app X)) := by
  rw [← DerivedCategory.TStructure.t.truncLEIsoTruncLT_hom_ι_app b (b + 1) rfl X,
    Functor.map_comp]
  have := isIso_homologyMap_truncLTι_app (A := A) (b + 1) j (by omega) X
  infer_instance

/-- **The one-degree interval truncation does not change the cohomology in its degree**, and does
so naturally: `H^p(τ^{≥p}τ^{≤p}K) ≅ H^p(K)` as functors of `K`.

Both truncations are invisible to `H^p`: `τ^{≤p}` retains the cohomology in degrees `≤ p`
(`Stacks.TruncationLevel.isIso_homologyMap_truncLEι_app`) and `τ^{≥p}` retains it in degrees `≥ p`
(`DerivedCategory.isIso_homologyMap_truncGEπ_app`), so the composite of the inverse of the
second comparison with the first is an isomorphism, and its naturality is that of the two
comparisons. Together with
`DerivedCategory.isoCompSingleFunctorOfIsLEOfIsGE` this is what presents a system of one-degree
interval truncations as the `singleFunctor` of the cohomology of the original system. -/
def truncGELECompHomologyIso (p : ℤ) :
    DerivedCategory.TStructure.t.truncGELE p p ⋙ DerivedCategory.homologyFunctor A p ≅
      DerivedCategory.homologyFunctor A p := by
  haveI hπ : ∀ X : DerivedCategory A, IsIso ((DerivedCategory.homologyFunctor A p).map
      ((DerivedCategory.TStructure.t.truncGEπ p).app
        ((DerivedCategory.TStructure.t.truncLE p).obj X))) :=
    fun X => DerivedCategory.isIso_homologyMap_truncGEπ_app p p le_rfl _
  haveI hι : ∀ X : DerivedCategory A, IsIso ((DerivedCategory.homologyFunctor A p).map
      ((DerivedCategory.TStructure.t.truncLEι p).app X)) :=
    fun X => isIso_homologyMap_truncLEι_app p p le_rfl X
  refine NatIso.ofComponents (fun X => (asIso ((DerivedCategory.homologyFunctor A p).map
    ((DerivedCategory.TStructure.t.truncGEπ p).app
      ((DerivedCategory.TStructure.t.truncLE p).obj X)))).symm ≪≫
    asIso ((DerivedCategory.homologyFunctor A p).map
      ((DerivedCategory.TStructure.t.truncLEι p).app X))) ?_
  intro X Y f
  have hnatπ := congrArg (DerivedCategory.homologyFunctor A p).map
    ((DerivedCategory.TStructure.t.truncGEπ p).naturality
      ((DerivedCategory.TStructure.t.truncLE p).map f))
  have hnatι := congrArg (DerivedCategory.homologyFunctor A p).map
    ((DerivedCategory.TStructure.t.truncLEι p).naturality f)
  simp only [Functor.id_obj, Functor.id_map, Functor.map_comp] at hnatπ hnatι
  dsimp only [Functor.comp_map, Iso.trans_hom, Iso.symm_hom, asIso_inv, asIso_hom]
  rw [← cancel_epi ((DerivedCategory.homologyFunctor A p).map
    ((DerivedCategory.TStructure.t.truncGEπ p).app
      ((DerivedCategory.TStructure.t.truncLE p).obj X)))]
  simp only [Category.assoc]
  rw [IsIso.hom_inv_id_assoc, ← Category.assoc, ← hnatπ, Category.assoc,
    IsIso.hom_inv_id_assoc, hnatι]

section Comparison

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]

omit [IsTriangulated C] in
/-- A distinguished triangle stays distinguished after its third vertex is transported along an
isomorphism, the second and third maps being composed with it. -/
lemma distTriang_of_iso_obj₃ {T : Triangle C} (hT : T ∈ distTriang C) {Y : C} (e : T.obj₃ ≅ Y) :
    Triangle.mk T.mor₁ (T.mor₂ ≫ e.hom) (e.inv ≫ T.mor₃) ∈ distTriang C :=
  isomorphic_distinguished _ hT _
    (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e.symm (by simp) (by simp) (by simp))

/-- **The comparison triangle of two truncation levels from below.** For `a ≤ b` the canonical map
`τ_{≥ a}X ⟶ τ_{≥ b}X` sits in a distinguished triangle whose first vertex is the interval
truncation `τ_{< b}(τ_{≥ a}X)`.

It is the defining triangle of the truncation at `b` of the object `τ_{≥ a}X`, whose third vertex
`τ_{≥ b}(τ_{≥ a}X)` is identified with `τ_{≥ b}X`. -/
theorem exists_distTriang_truncGE (t : TStructure C) (a b : ℤ) (hab : a ≤ b) (X : C) :
    ∃ δ, Triangle.mk ((t.truncLTι b).app ((t.truncGE a).obj X))
      ((t.natTransTruncGEOfLE a b hab).app X) δ ∈ distTriang C := by
  have hiso : IsIso ((t.truncGE b).map ((t.truncGEπ a).app X)) :=
    t.isIso_truncGE_map_truncGEπ_app b a hab X
  have hGE : t.IsGE ((t.truncGE b).obj X) a := t.isGE_of_ge _ a b hab
  have heq : (t.natTransTruncGEOfLE a b hab).app X =
      (t.truncGEπ b).app ((t.truncGE a).obj X) ≫
        inv ((t.truncGE b).map ((t.truncGEπ a).app X)) := by
    refine t.from_truncGE_obj_ext ?_
    simp only [← Category.assoc, t.π_natTransTruncGEOfLE_app a b hab X]
    have hnat := (t.truncGEπ b).naturality ((t.truncGEπ a).app X)
    simp only [Functor.id_map, Functor.id_obj] at hnat
    rw [hnat, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  refine ⟨(t.truncGE b).map ((t.truncGEπ a).app X) ≫
    (t.truncGEδLT b).app ((t.truncGE a).obj X), ?_⟩
  rw [heq]
  exact distTriang_of_iso_obj₃ (t.triangleLTGE_distinguished b ((t.truncGE a).obj X))
    (asIso ((t.truncGE b).map ((t.truncGEπ a).app X))).symm

end Comparison

variable [IsTriangulated (DerivedCategory A)]

/-- The degree-`a` cohomology of the one-step interval truncation `τ_{< a + 1}(τ_{≥ a}X)` is the
degree-`a` cohomology of `X`. -/
def homologyTruncLTGEIso (a : ℤ) (X : DerivedCategory A) :
    (DerivedCategory.homologyFunctor A a).obj
        ((DerivedCategory.TStructure.t.truncLTGE a (a + 1)).obj X) ≅
      (DerivedCategory.homologyFunctor A a).obj X :=
  have h₁ := isIso_homologyMap_truncLTι_app (a + 1) a (by omega)
    ((DerivedCategory.TStructure.t.truncGE a).obj X)
  have h₂ := DerivedCategory.isIso_homologyMap_truncGEπ_app a a le_rfl X
  @asIso _ _ _ _ _ h₁ ≪≫ (@asIso _ _ _ _ _ h₂).symm

/-- **The one-step interval truncation is a single cohomology object.** The interval truncation
`τ_{< a + 1}(τ_{≥ a}X)` is isomorphic to `H^a(X)` placed in degree `a`. -/
theorem nonempty_iso_singleFunctor_truncLTGE (a : ℤ) (X : DerivedCategory A) :
    Nonempty ((DerivedCategory.TStructure.t.truncLTGE a (a + 1)).obj X ≅
      (DerivedCategory.singleFunctor A a).obj ((DerivedCategory.homologyFunctor A a).obj X)) := by
  have hLE : DerivedCategory.TStructure.t.IsLE
      ((DerivedCategory.TStructure.t.truncLTGE a (a + 1)).obj X) a := by
    have h : DerivedCategory.TStructure.t.IsLE
        ((DerivedCategory.TStructure.t.truncLTGE a (a + 1)).obj X) (a + 1 - 1) := inferInstance
    simpa using h
  obtain ⟨Y, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE
    ((DerivedCategory.TStructure.t.truncLTGE a (a + 1)).obj X) a
  refine ⟨e ≪≫ (DerivedCategory.singleFunctor A a).mapIso ?_⟩
  exact ((DerivedCategory.singleFunctorCompHomologyFunctorIso A a).app Y).symm ≪≫
    (DerivedCategory.homologyFunctor A a).mapIso e.symm ≪≫ homologyTruncLTGEIso a X

end Stacks.TruncationLevel

end
