module

public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-!
# Extending a bounded complex by one object in the top degree

Let `A` be an abelian category with a derived category `D(A)`. Suppose that, in `D(A)`, an
object `K` sits in a distinguished triangle
`G[-b] ⟶ K ⟶ L ⟶ G[-b][1]` with `G : A` placed in degree `b`, and that `L` is represented by
an honest cochain complex `C'` concentrated in degrees `[a, b - 1]`. Then `K` is itself
represented by a cochain complex `C` concentrated in degrees `[a, b]` whose terms are those of
`C'` in degrees `≤ b - 1` and `G` in degree `b`. This is the step which builds a complex out of
an object of `D(A)` one degree at a time, by descending induction on its top degree.

## The argument

The connecting morphism `L ⟶ G[-b][1]`, inverse-rotated, is a morphism
`L[-1] ⟶ G[-b]`, and `L[-1]` is represented by the shifted complex `C'[-1]`, which is strictly
`≤ b`. The first result of the file says that a morphism in `D(A)` from a complex strictly
`≤ n` to an object placed in degree `n` is the image of an honest chain map: by
`DerivedCategory.left_fac_of_isStrictlyLE_of_isStrictlyGE` it is a left fraction
`Q.map g ≫ inv (Q.map s)` whose quasi-isomorphism `s` starts at the single complex and ends at a
complex strictly in degrees `[n, n]`, hence at a single complex; `s` is then the image of an
isomorphism of `A` because the single functor is fully faithful, and can be inverted at the chain
level. The mapping cone `C` of the resulting chain map `ψ : C'[-1] ⟶ G[-b]` has the required
terms, `C^k = C'^k ⊞ (G[-b])^k`, and the triangle of the mapping cone is distinguished in
`D(A)` and has the same first morphism as the inverse rotation of the given triangle, so their
third vertices `Q.obj C` and `K` are isomorphic (`Pretriangulated.exists_iso_of_arrow_iso`).

## Main results

* `DerivedCategory.exists_Q_map_eq_of_isStrictlyLE`: every morphism of `D(A)` from a cochain
  complex strictly `≤ n` to the single complex in degree `n` on an object of `A` is the image
  under `Q` of a chain map.
* `DerivedCategory.exists_complex_of_distTriang_single`: the extension statement above.

## Implementation notes

The lower bound `a ≤ b` is needed in the extension statement: if `a > b` then `C'` is zero, `K`
is `G` placed in degree `b`, and a complex strictly `≥ a` has zero term in degree `b`, so it
cannot have `G` as its degree-`b` term unless `G` is zero.
-/

@[expose] public noncomputable section

universe w v u

open CategoryTheory Category Limits Pretriangulated

namespace DerivedCategory

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- A morphism of the derived category from a cochain complex `M` which is strictly `≤ n` to the
single complex on `G : A` in degree `n` is the image under `Q` of a morphism of cochain
complexes. -/
theorem exists_Q_map_eq_of_isStrictlyLE (M : CochainComplex A ℤ) (n : ℤ) [M.IsStrictlyLE n]
    (G : A) (φ : Q.obj M ⟶ Q.obj ((HomologicalComplex.single A (ComplexShape.up ℤ) n).obj G)) :
    ∃ ψ : M ⟶ (HomologicalComplex.single A (ComplexShape.up ℤ) n).obj G, Q.map ψ = φ := by
  obtain ⟨Y, _, _, g, s, _, rfl⟩ := left_fac_of_isStrictlyLE_of_isStrictlyGE n n φ
  obtain ⟨G', ⟨e⟩⟩ := Y.exists_iso_single n
  obtain ⟨u, hu⟩ := (CochainComplex.singleFunctor A n).map_surjective (s ≫ e.hom)
  have : IsIso ((singleFunctor A n).map u) := by
    change IsIso (Q.map ((CochainComplex.singleFunctor A n).map u))
    rw [hu, Q.map_comp]
    infer_instance
  have : IsIso u := isIso_of_fully_faithful (singleFunctor A n) u
  have hs : s = (CochainComplex.singleFunctor A n).map u ≫ e.inv := by simp [hu]
  refine ⟨g ≫ e.hom ≫ (CochainComplex.singleFunctor A n).map (inv u), ?_⟩
  rw [← cancel_mono (Q.map s), assoc, IsIso.inv_hom_id, comp_id, ← Q.map_comp]
  congr 1
  simp [hs]

/-- **Extending a complex by one object in the top degree.** Let
`G[-b] ⟶ K ⟶ L ⟶ G[-b][1]` be a distinguished triangle of `D(A)`, where `G[-b]` is `G : A`
placed in degree `b`, and let `L` be isomorphic to a cochain complex `C'` strictly concentrated in
degrees `[a, b - 1]`, with `a ≤ b`. Then `K` is isomorphic to a cochain complex `C` strictly
concentrated in degrees `[a, b]`, with `C^k ≅ C'^k` for `k ≤ b - 1` and `C^b ≅ G`.

The complex `C` is the mapping cone of a chain map `C'[-1] ⟶ G[-b]` representing the
inverse rotation of the connecting morphism `L ⟶ G[-b][1]`. -/
theorem exists_complex_of_distTriang_single (b : ℤ) (G : A) {K L : DerivedCategory A}
    (f : (singleFunctor A b).obj G ⟶ K) (g : K ⟶ L)
    (h : L ⟶ ((singleFunctor A b).obj G)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f g h ∈ distTriang _) (a : ℤ) (hab : a ≤ b) (C' : CochainComplex A ℤ)
    [C'.IsStrictlyGE a] [C'.IsStrictlyLE (b - 1)] (e : L ≅ Q.obj C') :
    ∃ C : CochainComplex A ℤ, C.IsStrictlyGE a ∧ C.IsStrictlyLE b ∧
      Nonempty (K ≅ Q.obj C) ∧ (∀ k : ℤ, k ≤ b - 1 → Nonempty (C.X k ≅ C'.X k)) ∧
      Nonempty (C.X b ≅ G) := by
  have : (C'⟦(-1 : ℤ)⟧).IsStrictlyLE b := C'.isStrictlyLE_shift (b - 1) (-1) b (by omega)
  let e₁ : Q.obj (C'⟦(-1 : ℤ)⟧) ≅ L⟦(-1 : ℤ)⟧ :=
    (Q.commShiftIso (-1 : ℤ)).app C' ≪≫ (shiftFunctor _ (-1 : ℤ)).mapIso e.symm
  obtain ⟨ψ, hψ⟩ := exists_Q_map_eq_of_isStrictlyLE (C'⟦(-1 : ℤ)⟧) b G
    (e₁.hom ≫ (Triangle.mk f g h).invRotate.mor₁)
  obtain ⟨E, -, -⟩ := exists_iso_of_arrow_iso _ _
    (mappingCone_triangle_distinguished ψ) (inv_rot_of_distTriang _ hT)
    (Arrow.isoMk e₁ (Iso.refl _) (hψ.symm.trans (comp_id _).symm))
  let single := HomologicalComplex.single A (ComplexShape.up ℤ) b
  have hX : ∀ k : ℤ, (CochainComplex.mappingCone ψ).X k ≅ C'.X k ⊞ (single.obj G).X k :=
    fun k => HomologicalComplex.homotopyCofiber.XIsoBiprod ψ k (k + 1) rfl ≪≫
      biprod.mapIso (C'.XIsoOfEq (show k + 1 + -1 = k by omega)) (Iso.refl _)
  refine ⟨CochainComplex.mappingCone ψ, ?_, ?_, ⟨(Triangle.π₃.mapIso E).symm⟩,
    fun k hk => ⟨hX k ≪≫ (isoBiprodZero (HomologicalComplex.isZero_single_obj_X _ b G k
      (by omega))).symm⟩,
    ⟨hX b ≪≫ (isoZeroBiprod (C'.isZero_of_isStrictlyLE (b - 1) b (by omega))).symm ≪≫
      HomologicalComplex.singleObjXSelf _ b G⟩⟩
  · rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    simpa using ⟨C'.isZero_of_isStrictlyGE a i, HomologicalComplex.isZero_single_obj_X _ b G i
      (by omega)⟩
  · rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    simpa using ⟨C'.isZero_of_isStrictlyLE (b - 1) i, HomologicalComplex.isZero_single_obj_X _ b G i
      (by omega)⟩

end DerivedCategory
