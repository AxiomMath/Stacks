module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

/-!
# The canonical truncation of a complex computes the t-structure truncation

Let `C` be an abelian category with a chosen derived category. For a cochain complex `K` over `C`
and `n : ℤ`, Mathlib provides both the complex-level canonical truncation `K.truncGE n`, with its
projection `K.πTruncGE n : K ⟶ K.truncGE n`, and the truncation functor `τ_{≥ n}` of the canonical
t-structure on `D(C)`. This file identifies the two: the comparison
`τ_{≥ n}(Q K) ⟶ Q(K.truncGE n)` obtained from the universal property of `τ_{≥ n}` is an
isomorphism, and more generally so is the comparison induced by any morphism `K ⟶ L` with `L`
strictly `≥ n` which is a quasi-isomorphism in every degree `≥ n`.

Two further gaps in the complex-level API are filled, both needed to present a tower of
truncations: the functoriality of `K.truncGE n` in the *degree* `n`, and the compatibility of that
comparison with the projections.

The `IsIso` criterion for `TStructure.descTruncGE` is stated for an arbitrary t-structure, since
nothing in it is special to a derived category: a morphism `f : X ⟶ Y` with `Y` `≥ n` which sits
in a distinguished triangle whose third vertex is `≤ n - 1` *is* the truncation map of `X`.

## Main definitions

* `CochainComplex.truncGEMapOfLE` — the comparison `K.truncGE a ⟶ K.truncGE b` for `a ≤ b`, the
  functoriality of the canonical truncation in the degree.

## Main results

* `CategoryTheory.Triangulated.TStructure.isIso_descTruncGE_of_distTriang` — for an arbitrary
  t-structure, a morphism onto an object `≥ n` whose fibre is `≤ n - 1` exhibits its target as the
  `≥ n`-truncation of its source.
* `CochainComplex.πTruncGE_comp_truncGEMapOfLE` — the comparison of truncations is compatible with
  the projections: `π_a ≫ truncGEMapOfLE = π_b`.
* `DerivedCategory.isIso_descTruncGE_Q_map_πTruncGE` — `Q(K.truncGE n)` *is* `τ_{≥ n}(Q K)`,
  through `Q(K.πTruncGE n)`.
* `DerivedCategory.isIso_descTruncGE_Q_map` — the same for an arbitrary quasi-isomorphism in
  degrees `≥ n` onto a strictly `≥ n` complex.

## Implementation notes

*Why the compatibility with the projections is in term mode, and carries no `reassoc`.* Both
`rw [truncGEMapOfLE]` and the `simp` run that `@[reassoc]` performs traverse the definition and
mint equation lemmas — `CochainComplex.truncGEMapOfLE.eq_1` and `.congr_simp` — into Mathlib's
`CochainComplex` namespace, which the axiom census reports in its name list. The associated form
has no consumer, so the attribute is a plain `@[simp]` and the proof is a chain of `congrArg`,
`Eq.trans` and `Category.assoc`, which mints nothing.

*Why `truncGEMapOfLE` is not defined degreewise.* The complex `K.truncGE a` differs from
`K.truncGE b` only in degrees `< b`, so a degreewise description is available but needs the
cokernel descriptions of the two truncations in degree `b` and a separate verification that the
result is a chain map. Instead the map is obtained from the functoriality in the complex applied
to `K.πTruncGE b`, composed with the inverse of `(K.truncGE b).πTruncGE a`, which is invertible
because `K.truncGE b` is strictly `≥ b` hence strictly `≥ a`. The compatibility with the
projections is then naturality of `πTruncGE`, and no degreewise computation occurs anywhere.

*Why three steps are in term mode.* `rw` builds its motive at `implicit` transparency, where
`(Triangle.mk h f δ).obj₂` is not interchangeable with its own second vertex, and where
`(K.shortComplexTruncLE n).X₂` is not interchangeable with `K`. The three squares that mention
those spellings — the identification of `descTruncGE` with the triangle isomorphism, and two of
the three commuting squares exhibiting the short-exact-sequence triangle in the shape with
`Q(K.πTruncGE n)` as its second map — are therefore assembled from `congrArg`, `Eq.trans` and
`Category.assoc` as terms.

*Why the `IsLE` hypothesis of the abstract criterion is explicit.* Passed as an instance it is not
found at the use sites, where the object appears as `(K.shortComplexTruncLE (n - 1)).X₁` rather
than as `K.truncLE (n - 1)`; the same applies to the `IsIso` hypotheses of the two cochain-level
results, which is why their isomorphisms are introduced by name rather than through `asIso` with
a synthesized instance.

## References

* [Stacks Project, Tag 0FNG](https://stacks.math.columbia.edu/tag/0FNG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated DerivedCategory Category

universe w v u

namespace CategoryTheory.Triangulated.TStructure

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] (t : TStructure D)

/-- **A morphism onto an object `≥ n` with fibre `≤ n - 1` is the truncation map.** If
`f : X ⟶ Y` has `Y` in the `≥ n` part of a t-structure and fits in a distinguished triangle
`A ⟶ X ⟶ Y ⟶ A⟦1⟧` with `A` in the `≤ n - 1` part, then the factorization
`τ_{≥ n}X ⟶ Y` of `f` through the canonical truncation map is an isomorphism.

Both `A ⟶ X ⟶ Y` and the defining triangle `τ_{<n}X ⟶ X ⟶ τ_{≥n}X` of the truncation have their
outer vertices in the two orthogonal parts, so the identity of `X` extends to an isomorphism of
the two triangles; its third component is the factorization, by the uniqueness of morphisms out
of `τ_{≥ n}X`. -/
theorem isIso_descTruncGE_of_distTriang {A X Y : D} (n : ℤ) (f : X ⟶ Y) [t.IsGE Y n]
    (h : A ⟶ X) (δ : Y ⟶ A⟦(1 : ℤ)⟧) (hT : Triangle.mk h f δ ∈ distTriang D)
    (hA : t.IsLE A (n - 1)) :
    IsIso (t.descTruncGE f n) := by
  obtain ⟨e, he⟩ := t.triangle_iso_exists (t.triangleLTGE_distinguished n X) hT
    (Iso.refl X) (n - 1) n inferInstance inferInstance hA (inferInstanceAs (t.IsGE Y n))
    (by omega)
  have key : t.descTruncGE f n = e.hom.hom₃ :=
    t.from_truncGE_obj_ext (((t.π_descTruncGE f n).trans
      (((Category.id_comp f).symm).trans
        (congrArg (fun z : X ⟶ X => z ≫ f) he.symm))).trans e.hom.comm₂.symm)
  rw [key]
  exact ⟨e.inv.hom₃, e.hom_inv_id_triangle_hom₃, e.inv_hom_id_triangle_hom₃⟩

end CategoryTheory.Triangulated.TStructure

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- **The canonical truncation of a complex is functorial in the degree.** For `a ≤ b` this is the
comparison `K.truncGE a ⟶ K.truncGE b`, the complex-level counterpart of Mathlib's
`CategoryTheory.Triangulated.TStructure.natTransTruncGEOfLE`.

It is `K.πTruncGE b` truncated in degree `a`, read through the invertible projection of the
already strictly `≥ b` complex `K.truncGE b`. -/
def truncGEMapOfLE (K : CochainComplex C ℤ) {a b : ℤ} (h : a ≤ b) :
    K.truncGE a ⟶ K.truncGE b :=
  haveI : (K.truncGE b).IsStrictlyGE a := (K.truncGE b).isStrictlyGE_of_ge a b h
  truncGEMap (K.πTruncGE b) a ≫ inv ((K.truncGE b).πTruncGE a)

/-- A morphism into a strictly `≥ n` complex factors through the truncation projection. -/
private theorem πTruncGE_comp_truncGEMap_comp_inv {K L : CochainComplex C ℤ} (φ : K ⟶ L) (n : ℤ)
    [L.IsStrictlyGE n] : K.πTruncGE n ≫ truncGEMap φ n ≫ inv (L.πTruncGE n) = φ :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z ↦ z ≫ inv (L.πTruncGE n)) (πTruncGE_naturality φ n)).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun z ↦ φ ≫ z) (IsIso.hom_inv_id (L.πTruncGE n))).trans
          (Category.comp_id _))))

/-- The comparison of truncations is compatible with the canonical projections. -/
@[simp]
theorem πTruncGE_comp_truncGEMapOfLE (K : CochainComplex C ℤ) {a b : ℤ} (h : a ≤ b) :
    K.πTruncGE a ≫ K.truncGEMapOfLE h = K.πTruncGE b :=
  have : (K.truncGE b).IsStrictlyGE a := (K.truncGE b).isStrictlyGE_of_ge a b h
  πTruncGE_comp_truncGEMap_comp_inv (K.πTruncGE b) a

end CochainComplex

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- **`Q(K.truncGE n)` is the `≥ n`-truncation of `Q K`.** The factorization of
`Q(K.πTruncGE n)` through the canonical truncation map `Q K ⟶ τ_{≥ n}(Q K)` is an isomorphism.

The short exact sequence `K.truncLE (n-1) ⟶ K ⟶ (K.shortComplexTruncLE (n-1)).X₃` gives a
distinguished triangle in `D(C)` whose third vertex is `Q(K.truncGE n)` — the comparison
`CochainComplex.shortComplexTruncLEX₃ToTruncGE` being a quasi-isomorphism — and whose second map
is `Q(K.πTruncGE n)`; its first vertex is `≤ n - 1`, so
`CategoryTheory.Triangulated.TStructure.isIso_descTruncGE_of_distTriang` applies. -/
theorem isIso_descTruncGE_Q_map_πTruncGE (K : CochainComplex C ℤ) (n : ℤ) :
    IsIso (TStructure.t.descTruncGE (Q.map (K.πTruncGE n)) n) := by
  have hn : n - 1 + 1 = n := by omega
  have hSES := K.shortComplexTruncLE_shortExact (n - 1)
  have hq : IsIso (Q.map (K.shortComplexTruncLEX₃ToTruncGE (n - 1) n hn)) := by
    rw [isIso_Q_map_iff_quasiIso]; infer_instance
  let ε : Q.obj (K.shortComplexTruncLE (n - 1)).X₃ ≅ Q.obj (K.truncGE n) :=
    @asIso _ _ _ _ _ hq
  have hmem : Triangle.mk (Q.map (K.shortComplexTruncLE (n - 1)).f)
      (Q.map (K.πTruncGE n)) (ε.inv ≫ (triangleOfSES hSES).mor₃) ∈
      distTriang (DerivedCategory C) := by
    refine isomorphic_distinguished _ (triangleOfSES_distinguished hSES) _ (Iso.symm ?_)
    refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) ε ?_ ?_ ?_
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · refine Eq.trans (Q.map_comp _ _).symm ?_
      refine Eq.trans (congrArg Q.map
        (CochainComplex.g_shortComplexTruncLEX₃ToTruncGE K (n - 1) n hn)) ?_
      exact (Category.id_comp _).symm
    · refine Eq.trans (congrArg (fun z => (triangleOfSES hSES).mor₃ ≫ z)
        (CategoryTheory.Functor.map_id (shiftFunctor (DerivedCategory C) (1 : ℤ)) _)) ?_
      exact (Category.comp_id _).trans (Iso.hom_inv_id_assoc ε _).symm
  exact TStructure.isIso_descTruncGE_of_distTriang TStructure.t n _ _ _ hmem
    (inferInstanceAs (TStructure.t.IsLE (Q.obj (K.truncLE (n - 1))) (n - 1)))

/-- **A quasi-isomorphism in degrees `≥ n` onto a strictly `≥ n` complex computes the
truncation.** If `φ : K ⟶ L` is a quasi-isomorphism in every degree `≥ n` and `L` is strictly
`≥ n`, then the factorization of `Q φ` through `Q K ⟶ τ_{≥ n}(Q K)` is an isomorphism.

`φ` factors as `K.πTruncGE n` followed by `truncGEMap φ n` followed by the inverse of the
invertible `L.πTruncGE n`, and the middle map is a quasi-isomorphism exactly under the hypothesis
on `φ`, by `CochainComplex.quasiIso_truncGEMap_iff`. -/
theorem isIso_descTruncGE_Q_map {K L : CochainComplex C ℤ} (φ : K ⟶ L) (n : ℤ)
    [L.IsStrictlyGE n] (hφ : ∀ r : ℤ, n ≤ r → QuasiIsoAt φ r) :
    IsIso (TStructure.t.descTruncGE (Q.map φ) n) := by
  have h1 : IsIso (Q.map (CochainComplex.truncGEMap φ n)) := by
    rwa [isIso_Q_map_iff_quasiIso, CochainComplex.quasiIso_truncGEMap_iff]
  have h0 := isIso_descTruncGE_Q_map_πTruncGE K n
  have key : TStructure.t.descTruncGE (Q.map φ) n =
      TStructure.t.descTruncGE (Q.map (K.πTruncGE n)) n ≫
        Q.map (CochainComplex.truncGEMap φ n) ≫ inv (Q.map (L.πTruncGE n)) := by
    refine TStructure.t.from_truncGE_obj_ext ?_
    rw [TStructure.t.π_descTruncGE, ← assoc, TStructure.t.π_descTruncGE, ← assoc, ← Q.map_comp,
      ← Q.map_inv, ← Q.map_comp, assoc, CochainComplex.πTruncGE_comp_truncGEMap_comp_inv]
  rw [key]
  infer_instance

end DerivedCategory

end
