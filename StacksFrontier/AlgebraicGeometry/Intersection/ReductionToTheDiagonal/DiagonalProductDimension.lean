module

public import StacksFrontier.AlgebraicGeometry.F6Rank89.IdealSheafStalk
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Product
public import StacksFrontier.AlgebraicGeometry.Intersection.ProperIntersections.DiagonalRegularImmersion

/-!
# The local dimension of a product of closed subschemes at a point of the diagonal

Let `X` be a variety over a field `k` and let `ι_V : V ⟶ X` and `ι_W : W ⟶ X` be closed
immersions. The product `V ×ₖ W` is a closed subscheme of `X ×ₖ X`, and a point `ζ` of the
scheme-theoretic intersection `V ×_X W` determines a point of `V ×ₖ W` lying over the image
`Δ(ξ)` of `ξ`, the image of `ζ` in `X`, under the diagonal. This file computes the dimension of
the local ring of `V ×ₖ W` at that point:

`dim 𝒪_{V ×ₖ W, p} + dim 𝒪_{X, ξ} = dim 𝒪_{V, v} + dim 𝒪_{W, w} + dim X`.

Geometrically, with `Z` the closure of `ξ`, this reads
`(dim V + dim W − dim Z) + (dim X − dim Z) = (dim V − dim Z) + (dim W − dim Z) + dim X`. It is
the numerical statement the reduction to the diagonal needs about the pair `Δ`, `V × W` on
`X ×ₖ X`: together with `dim 𝒪_{X ×ₖ X, Δ(ξ)} = dim X + dim 𝒪_{X, ξ}` it transfers the
dimension deficit of the pair `V`, `W` on `X` to the pair `Δ`, `V × W` on `X ×ₖ X`.

The proof is the local dimension formula of Stacks tag 0B2M at the point `p`, which gives
`dim_p (V ×ₖ W) = dim_v V + dim_w W`, combined with the dimension formula of Stacks tag 0A21 at
the four points `p`, `v`, `w` and `ξ`, which expresses each local dimension as the
transcendence degree of the residue field plus the dimension of the local ring. All four
residue fields are the residue field of `X` at `ξ`, because `ι_V`, `ι_W`, the diagonal and the
closed immersion `V ×ₖ W ⟶ X ×ₖ X` all induce isomorphisms on residue fields; so the common
transcendence degree `t` cancels once, leaving
`dim 𝒪_{V ×ₖ W, p} = dim 𝒪_{V, v} + dim 𝒪_{W, w} + t`, and `t + dim 𝒪_{X, ξ} = dim X` is the
same formula at `ξ` together with the irreducibility of `X`.

## Main results

* `Stacks.Intersection.Diagonal.prodMap` — the closed immersion `V ×ₖ W ⟶ X ×ₖ X` induced by a
  pair of closed immersions into `X`, together with the instance recording that it is a closed
  immersion.
* `Stacks.Intersection.Diagonal.interToProd` — the morphism `V ×_X W ⟶ V ×ₖ W` from the
  scheme-theoretic intersection, and `prodMap_comp_interToProd`, which says that composing it
  with `prodMap` is the diagonal of `X` applied to the image of the intersection in `X`. This
  is what produces a point of `V ×ₖ W` over `Δ(ξ)`.
* `Stacks.Intersection.Diagonal.ringKrullDim_stalk_prod_add_ringKrullDim_stalk` — the displayed
  dimension formula.
* `Stacks.Intersection.Diagonal.ringKrullDim_quotient_stalk_ker_prodMap_add` — the same
  formula with the local ring of `V ×ₖ W` at `p` presented as the quotient of
  `𝒪_{X ×ₖ X, Δ(ξ)}` by the kernel of the local ring map of `prodMap`, which is the local ideal
  of `V × W` at `Δ(ξ)`.

## Implementation notes

As in `Stacks.Intersection.Diagonal.ringKrullDim_stalk_pullback_diagonal`, every structure
morphism to `Spec k` is taken in the composite form in which
`Stacks.Intersection.trdeg_residueField_eq_of_isClosedImmersion_of_eq` produces it, so that the
`Algebra k` instances on the four residue fields agree syntactically and the transcendence
degrees can be rewritten into one another. The `LocallyOfFiniteType` instances for those
composites are supplied by rewriting them to the forms the typeclass system recognises.

The cancellation of the transcendence degree takes place in `ℕ∞` after stripping the `WithBot`
coercion, using that the transcendence degree of the residue field of a scheme locally of
finite type over a field at a point is finite
(`Stacks.Intersection.trdeg_residueField_lt_aleph0_of_locallyOfFiniteType`).

## References

* [Stacks Project, Tag 0B2M](https://stacks.math.columbia.edu/tag/0B2M)
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
* [Stacks Project, Tag 0B0U](https://stacks.math.columbia.edu/tag/0B0U)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Intersection.Diagonal

variable {k : Type u} [Field k] {X V W : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (iV : V ⟶ X) (iW : W ⟶ X)

/-- The morphism `V ×ₖ W ⟶ X ×ₖ X` induced by a pair of morphisms `V ⟶ X`, `W ⟶ X` over
`Spec k`. When both are closed immersions it exhibits `V × W` as a closed subscheme of the
product. -/
noncomputable def prodMap : (pullback (iV ≫ f) (iW ≫ f) : Scheme.{u}) ⟶ pullback f f :=
  pullback.map (iV ≫ f) (iW ≫ f) f f iV iW (𝟙 _)
    ((Category.comp_id _).trans rfl) ((Category.comp_id _).trans rfl)

/-- The morphism `V ×_X W ⟶ V ×ₖ W` from the scheme-theoretic intersection of two subschemes of
`X` to their product over the base. -/
noncomputable def interToProd : (pullback iV iW : Scheme.{u}) ⟶ pullback (iV ≫ f) (iW ≫ f) :=
  pullback.map iV iW (iV ≫ f) (iW ≫ f) (𝟙 V) (𝟙 W) f (by simp) (by simp)

/-- Closed immersions are stable under composition. -/
instance isStableUnderComposition_isClosedImmersion :
    MorphismProperty.IsStableUnderComposition (@IsClosedImmersion) where
  comp_mem _ _ _ _ := IsClosedImmersion.comp _ _

/-- If `V ⟶ X` and `W ⟶ X` are closed immersions, then so is `prodMap f iV iW`. -/
instance isClosedImmersion_prodMap [IsClosedImmersion iV] [IsClosedImmersion iW] :
    IsClosedImmersion (prodMap f iV iW) :=
  MorphismProperty.pullbackMap (P := @IsClosedImmersion) inferInstance inferInstance rfl rfl

/-- The first projection of `X ×ₖ X` composed with `prodMap` is the first projection of
`V ×ₖ W` followed by `iV`. -/
@[simp]
theorem prodMap_comp_fst :
    prodMap f iV iW ≫ pullback.fst f f = pullback.fst (iV ≫ f) (iW ≫ f) ≫ iV := by
  simp only [prodMap, pullback.map, pullback.lift_fst]

/-- The second projection of `X ×ₖ X` composed with `prodMap` is the second projection of
`V ×ₖ W` followed by `iW`. -/
@[simp]
theorem prodMap_comp_snd :
    prodMap f iV iW ≫ pullback.snd f f = pullback.snd (iV ≫ f) (iW ≫ f) ≫ iW := by
  simp only [prodMap, pullback.map, pullback.lift_snd]

/-- The first projection of `V ×ₖ W` composed with `interToProd` is the first projection of
`V ×_X W`. -/
@[simp]
theorem interToProd_comp_fst :
    interToProd f iV iW ≫ pullback.fst (iV ≫ f) (iW ≫ f) = pullback.fst iV iW := by
  simp only [interToProd, pullback.map, pullback.lift_fst, Category.comp_id]

/-- The second projection of `V ×ₖ W` composed with `interToProd` is the second projection of
`V ×_X W`. -/
@[simp]
theorem interToProd_comp_snd :
    interToProd f iV iW ≫ pullback.snd (iV ≫ f) (iW ≫ f) = pullback.snd iV iW := by
  simp only [interToProd, pullback.map, pullback.lift_snd, Category.comp_id]

/-- The product of two closed subschemes of `X`, seen inside `X ×ₖ X`, contains the image of the
scheme-theoretic intersection under the diagonal: composing `V ×_X W ⟶ V ×ₖ W ⟶ X ×ₖ X` with
the structure maps gives the diagonal of `X` applied to the image of the intersection. -/
theorem prodMap_comp_interToProd :
    interToProd f iV iW ≫ prodMap f iV iW =
      (pullback.fst iV iW ≫ iV) ≫ pullback.diagonal f := by
  apply pullback.hom_ext
  · simp only [Category.assoc, prodMap_comp_fst, pullback.diagonal_fst, Category.comp_id]
    rw [← Category.assoc, interToProd_comp_fst]
  · simp only [Category.assoc, prodMap_comp_snd, pullback.diagonal_snd, Category.comp_id]
    rw [← Category.assoc, interToProd_comp_snd, pullback.condition]

/-- The point of `V ×ₖ W` determined by a point of the scheme-theoretic intersection `V ×_X W`
lies over the image of that point under the diagonal of `X`. -/
theorem prodMap_interToProd_apply (ζ : ↑(pullback iV iW)) :
    prodMap f iV iW (interToProd f iV iW ζ) =
      pullback.diagonal f (iV (pullback.fst iV iW ζ)) := by
  rw [← AlgebraicGeometry.Scheme.Hom.comp_apply, prodMap_comp_interToProd,
    AlgebraicGeometry.Scheme.Hom.comp_apply, AlgebraicGeometry.Scheme.Hom.comp_apply]

/-- Two equal points of a scheme have residue fields of the same transcendence degree over the
base field, for the algebra structures induced by `g`. -/
theorem trdeg_residueField_congr {Z : Scheme.{u}} (g : Z ⟶ Spec (.of k)) {x y : Z} (h : x = y) :
    letI : Algebra k (Z.residueField x) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop ≫ Z.Γevaluation x).hom.toAlgebra
    letI : Algebra k (Z.residueField y) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop ≫ Z.Γevaluation y).hom.toAlgebra
    Algebra.trdeg k (Z.residueField x) = Algebra.trdeg k (Z.residueField y) := by
  subst h; rfl

/-- **The local dimension of a product of closed subschemes at a point of the diagonal.** Let
`X` be a variety over a field `k`, let `ι_V : V ⟶ X` and `ι_W : W ⟶ X` be closed immersions and
let `ζ` be a point of the scheme-theoretic intersection `V ×_X W`, with images `v` in `V`, `w`
in `W` and `ξ` in `X`. Write `p` for the point of `V ×ₖ W` determined by `ζ`, which lies over
`Δ(ξ)`. Then

`dim 𝒪_{V ×ₖ W, p} + dim 𝒪_{X, ξ} = dim 𝒪_{V, v} + dim 𝒪_{W, w} + dim X`.

With `Z` the closure of `ξ` this is
`(dim V + dim W − dim Z) + (dim X − dim Z) = (dim V − dim Z) + (dim W − dim Z) + dim X`. It is
the half of the numerical hypothesis of the reduction to the diagonal that concerns the local
ideal of `V × W`; the other half, concerning the ideal of the diagonal, is
`Stacks.Intersection.Diagonal.ringKrullDim_stalk_pullback_diagonal`. -/
theorem ringKrullDim_stalk_prod_add_ringKrullDim_stalk [IsVariety k f]
    [IsClosedImmersion iV] [IsClosedImmersion iW] (ζ : ↑(pullback iV iW)) :
    ringKrullDim ((pullback (iV ≫ f) (iW ≫ f)).presheaf.stalk (interToProd f iV iW ζ)) +
        ringKrullDim (X.presheaf.stalk (iV (pullback.fst iV iW ζ))) =
      ringKrullDim (V.presheaf.stalk (pullback.fst iV iW ζ)) +
        ringKrullDim (W.presheaf.stalk (pullback.snd iV iW ζ)) + topologicalKrullDim X := by
  set P := (pullback f f : Scheme.{u}) with hP
  set Q := (pullback (iV ≫ f) (iW ≫ f) : Scheme.{u}) with hQ
  set m : Q ⟶ P := prodMap f iV iW with hm
  set v : V := pullback.fst iV iW ζ with hv
  set w : W := pullback.snd iV iW ζ with hw
  set pt : Q := interToProd f iV iW ζ with hpt
  set ξ : X := iV v with hξ
  set pr : P ⟶ Spec (.of k) := pullback.fst f f ≫ f with hpr
  set gX : X ⟶ Spec (.of k) := pullback.diagonal f ≫ pr with hgX
  have hgXf : gX = f := by
    rw [hgX, hpr, ← Category.assoc, pullback.diagonal_fst, Category.id_comp]
  set q : Q ⟶ Spec (.of k) := m ≫ pr with hq
  set gV : V ⟶ Spec (.of k) := iV ≫ gX with hgV
  set gW : W ⟶ Spec (.of k) := iW ≫ gX with hgW
  let : LocallyOfFiniteType gX := by rw [hgXf]; infer_instance
  let : LocallyOfFiniteType gV := by rw [hgV]; infer_instance
  let : LocallyOfFiniteType gW := by rw [hgW]; infer_instance
  let : LocallyOfFiniteType q := by rw [hq]; infer_instance
  have hptfst : pullback.fst (iV ≫ f) (iW ≫ f) pt = v := by
    rw [hpt, hv, ← AlgebraicGeometry.Scheme.Hom.comp_apply, interToProd_comp_fst]
  have hptsnd : pullback.snd (iV ≫ f) (iW ≫ f) pt = w := by
    rw [hpt, hw, ← AlgebraicGeometry.Scheme.Hom.comp_apply, interToProd_comp_snd]
  have hmpt : m pt = pullback.diagonal f ξ := by
    have := congrArg (fun n : (pullback iV iW : Scheme.{u}) ⟶ P => n ζ)
      (prodMap_comp_interToProd f iV iW)
    simpa [hpt, hm, hξ, hv] using this
  let : Algebra k (X.residueField ξ) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ gX.appTop ≫ X.Γevaluation ξ).hom.toAlgebra
  let : Algebra k (V.residueField v) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ gV.appTop ≫ V.Γevaluation v).hom.toAlgebra
  let : Algebra k (W.residueField w) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ gW.appTop ≫ W.Γevaluation w).hom.toAlgebra
  let : Algebra k (Q.residueField pt) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ q.appTop ≫ Q.Γevaluation pt).hom.toAlgebra
  let : Algebra k (P.residueField (m pt)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ pr.appTop ≫ P.Γevaluation (m pt)).hom.toAlgebra
  let : Algebra k (P.residueField (pullback.diagonal f ξ)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ pr.appTop ≫
      P.Γevaluation (pullback.diagonal f ξ)).hom.toAlgebra
  set t : ℕ∞ := Cardinal.toENat (Algebra.trdeg k (X.residueField ξ)) with ht
  have htne : t ≠ ⊤ :=
    ne_of_lt ((Cardinal.toENat_lt_top).2
      (Stacks.Intersection.trdeg_residueField_lt_aleph0_of_locallyOfFiniteType gX ξ))
  have htV : Algebra.trdeg k (V.residueField v) = Algebra.trdeg k (X.residueField ξ) :=
    (trdeg_residueField_eq_of_isClosedImmersion_of_eq gX iV v rfl).symm
  have htW : Algebra.trdeg k (W.residueField w) = Algebra.trdeg k (X.residueField ξ) := by
    refine (trdeg_residueField_eq_of_isClosedImmersion_of_eq gX iW w ?_).symm
    rw [hξ, hv, hw, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  have htQ : Algebra.trdeg k (Q.residueField pt) = Algebra.trdeg k (X.residueField ξ) := by
    have h1 := trdeg_residueField_eq_of_isClosedImmersion_of_eq pr m pt hmpt
    have h2 := trdeg_residueField_eq_of_isClosedImmersion_of_eq pr (pullback.diagonal f) ξ rfl
    exact h1.symm.trans h2
  have hformQ := topologicalKrullDimAt_eq_trdeg_add_krullDim_stalk k Q q pt
  have hformV := topologicalKrullDimAt_eq_trdeg_add_krullDim_stalk k V gV v
  have hformW := topologicalKrullDimAt_eq_trdeg_add_krullDim_stalk k W gW w
  have hformX := topologicalKrullDimAt_eq_trdeg_add_krullDim_stalk k X gX ξ
  have hB2M := topologicalKrullDimAt_pullback k (iV ≫ f) (iW ≫ f) pt
  rw [hptfst, hptsnd] at hB2M
  have hdimX : topologicalKrullDim X = topologicalKrullDimAt X ξ :=
    topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k X gX ξ
  rw [htQ] at hformQ
  rw [htV] at hformV
  rw [htW] at hformW
  simp only [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight, ← ht] at hformQ hformV hformW hformX
  have hkey : (t : WithBot ℕ∞) + (Order.coheight pt : WithBot ℕ∞) =
      ((t : WithBot ℕ∞) + (Order.coheight v : WithBot ℕ∞)) +
        ((t : WithBot ℕ∞) + (Order.coheight w : WithBot ℕ∞)) := by
    rw [← hformQ, hB2M, hformV, hformW]
  have hkey' : t + Order.coheight pt = (t + Order.coheight v) + (t + Order.coheight w) := by
    apply WithBot.coe_injective
    simpa only [WithBot.coe_add] using hkey
  have hcancel : Order.coheight pt = Order.coheight v + Order.coheight w + t := by
    refine WithTop.add_left_cancel htne (hkey'.trans ?_)
    abel
  simp only [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight]
  rw [hdimX, hformX, hcancel]
  push_cast
  ring

/-- **The local ideal of `V × W` at `Δ(ξ)` and the dimension of its quotient.** The stalk at
`Δ(ξ)` of the ideal sheaf of the closed subscheme `V ×ₖ W` of `X ×ₖ X` is the kernel of the
local ring map that the closed immersion `V ×ₖ W ⟶ X ×ₖ X` induces at the point of `V ×ₖ W`
over `Δ(ξ)`, so the quotient of `𝒪_{X ×ₖ X, Δ(ξ)}` by it is the local ring of `V ×ₖ W` there. -/
theorem ringKrullDim_quotient_stalk_ker_prodMap [IsClosedImmersion iV] [IsClosedImmersion iW]
    (ζ : ↑(pullback iV iW)) :
    ringKrullDim ((pullback f f).presheaf.stalk
          (pullback.diagonal f (iV (pullback.fst iV iW ζ))) ⧸
        AlgebraicGeometry.IdealSheafData.stalk (prodMap f iV iW).ker
          (pullback.diagonal f (iV (pullback.fst iV iW ζ)))) =
      ringKrullDim ((pullback (iV ≫ f) (iW ≫ f)).presheaf.stalk (interToProd f iV iW ζ)) := by
  rw [← prodMap_interToProd_apply, AlgebraicGeometry.IdealSheafData.stalk_ker_of_isClosedImmersion]
  exact ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective
    ((prodMap f iV iW).stalkMap_surjective (interToProd f iV iW ζ)))

/-- **The other half of the numerical hypothesis of the reduction to the diagonal.** Let `X` be
a variety over `k`, let `V` and `W` be closed subschemes of `X` and let `ζ` be a point of the
scheme-theoretic intersection, with images `v`, `w` and `ξ`. Writing `J'` for the local ideal of
`V × W` at `Δ(ξ)` — the stalk there of the ideal sheaf of the closed subscheme `V ×ₖ W` of
`X ×ₖ X` — one has

`dim (𝒪_{X ×ₖ X, Δ(ξ)} ⧸ J') + dim 𝒪_{X, ξ} = dim 𝒪_{V, v} + dim 𝒪_{W, w} + dim X`.

Together with `dim 𝒪_{X ×ₖ X, Δ(ξ)} = dim X + dim 𝒪_{X, ξ}`
(`Stacks.Intersection.Diagonal.ringKrullDim_stalk_pullback_diagonal`) this is what transfers the
dimension deficit of the pair `V`, `W` on `X` to the pair `Δ`, `V × W` on `X ×ₖ X`. -/
theorem ringKrullDim_quotient_stalk_ker_prodMap_add [IsVariety k f]
    [IsClosedImmersion iV] [IsClosedImmersion iW] (ζ : ↑(pullback iV iW)) :
    ringKrullDim ((pullback f f).presheaf.stalk
          (pullback.diagonal f (iV (pullback.fst iV iW ζ))) ⧸
        AlgebraicGeometry.IdealSheafData.stalk (prodMap f iV iW).ker
          (pullback.diagonal f (iV (pullback.fst iV iW ζ)))) +
        ringKrullDim (X.presheaf.stalk (iV (pullback.fst iV iW ζ))) =
      ringKrullDim (V.presheaf.stalk (pullback.fst iV iW ζ)) +
        ringKrullDim (W.presheaf.stalk (pullback.snd iV iW ζ)) + topologicalKrullDim X := by
  rw [ringKrullDim_quotient_stalk_ker_prodMap]
  exact ringKrullDim_stalk_prod_add_ringKrullDim_stalk f iV iW ζ

end Stacks.Intersection.Diagonal

end
