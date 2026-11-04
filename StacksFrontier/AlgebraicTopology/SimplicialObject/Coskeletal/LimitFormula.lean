module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import StacksFrontier.AlgebraicTopology.SimplicialObject.Coskeletal
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Coskeleton functors over a category with finite limits, and the degreewise limit formula

Let `C` be a category and `m : ℕ`. Restriction along the inclusion `Δ_{≤ m} ⊆ Δ` is the skeleton
functor `sk_m : Simp(C) ⥤ Simp_m(C)`, `CategoryTheory.SimplicialObject.truncation m`, and its
right adjoint is the coskeleton functor `cosk_m`. Saying that `cosk_m V` *exists* means that
`U ↦ Mor_{Simp_m(C)}(sk_m U, V)` is representable, so that

`Mor_{Simp(C)}(U, cosk_m V) = Mor_{Simp_m(C)}(sk_m U, V)`;

such a representing object is unique up to a unique isomorphism compatible with the counits, by
the Yoneda lemma. When `C` has finite limits all the pointwise right Kan extensions along
`(Δ_{≤ m} ⊆ Δ)ᵒᵖ` exist ([Stacks, Lemma 0183]), and recording that as an instance makes
`CategoryTheory.SimplicialObject.Truncated.cosk m` and the adjunction
`CategoryTheory.SimplicialObject.coskAdj m` available for every `m`.

Pointwiseness is what computes `cosk_m U` degreewise. For every `n` the canonical cone with apex
`(cosk_m U)_n` over the diagram `U(n) : ((Δ/[n])_{≤ m})ᵒᵖ ⥤ C` of
`CategoryTheory.SimplicialObject.Truncated.sliceDiagram`, whose leg at an object `α : [k] → [n]`
of `(Δ/[n])_{≤ m}` is `cosk_m U(α)` followed by the counit identification `(cosk_m U)_k ⟶ U_k`,
is a limit cone:

`(cosk_m U)_n = lim_{((Δ/[n])_{≤ m})ᵒᵖ} U(n)`.

For `φ : [n] → [n']` the object `α` of `(Δ/[n])_{≤ m}` is carried to `φ ∘ α`, and this is the
identification under which `cosk_m U(φ)` becomes the induced morphism of limits: the leg of
`cosk_m U(φ)` at `α` is the leg of the limit cone in degree `n'` at `φ ∘ α`, and the two cones
being limit cones this property determines `cosk_m U(φ)`.

### Main results

* `CategoryTheory.SimplicialObject.Truncated.exists_rightAdjoint_truncation`: over a category
  with finite limits the skeleton functor `sk_m` has a right adjoint for every `m`.
* `CategoryTheory.SimplicialObject.Truncated.existsUnique_iso_rightAdjoint_truncation`: two right
  adjoints of `sk_m` are isomorphic by a unique isomorphism compatible with the counits.
* `CategoryTheory.SimplicialObject.Truncated.coskConeIsLimit`: the canonical cone over `U(n)` with
  apex `(cosk_m U)_n` is a limit cone, and
  `CategoryTheory.SimplicialObject.Truncated.coskObjObjIsoLimit` is the resulting isomorphism of
  `(cosk_m U)_n` with the limit of `U(n)`.
* `CategoryTheory.SimplicialObject.Truncated.map_eq_coskConeIsLimit_lift`: `cosk_m U(φ)` is the
  morphism of limits induced by postcomposition with `φ`.

### References

* [Stacks, Tag 0181](https://stacks.math.columbia.edu/tag/0181)
* [Stacks, Tag 0AMA](https://stacks.math.columbia.edu/tag/0AMA)
-/

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe v u

namespace CategoryTheory.SimplicialObject.Truncated

variable {C : Type u} [Category.{v} C]

/-- Over a category with finite limits every `m`-truncated simplicial object has the limits that
exhibit it as a pointwise right Kan extension along `(Δ_{≤ m} ⊆ Δ)ᵒᵖ`, by [Stacks, Lemma 0183];
as an instance this makes `cosk_m` and the adjunction `coskAdj m` available. -/
instance hasLimit_structuredArrow_proj_inclusion_op [HasFiniteLimits C] {m : ℕ}
    {U : SimplicialObject.Truncated C m} (Y : SimplexCategoryᵒᵖ) :
    HasLimit (StructuredArrow.proj Y (SimplexCategory.Truncated.inclusion m).op ⋙ U) :=
  hasPointwiseRightKanExtension_of_hasFiniteLimits m U Y

/-- **Stacks 0AMA**.
If `C` has finite limits then for every `m` the skeleton functor `sk_m : Simp(C) ⥤ Simp_m(C)` has
a right adjoint, so that the coskeleton functor `cosk_m` exists: morphisms `U ⟶ cosk_m V` of
simplicial objects correspond naturally to morphisms `sk_m U ⟶ V` of `m`-truncated ones. -/
@[stacks 0AMA "the section's assertion that `cosk_m` exists for every `m` over a category with \
  finite limits, which is Lemma 0183 inside the section; the degreewise limit formula is \
  `coskConeIsLimit` below", sga "4 V 7.1.0" "partial", sga "4 Vbis 3.0.1"]
theorem exists_rightAdjoint_truncation [HasFiniteLimits C] (m : ℕ) :
    ∃ G : SimplicialObject.Truncated C m ⥤ SimplicialObject C,
      Nonempty (SimplicialObject.truncation (C := C) m ⊣ G) :=
  ⟨Truncated.cosk m, ⟨SimplicialObject.coskAdj m⟩⟩

/-- **The bijection `Mor(U, cosk_m V) = Mor(sk_m U, V)`** of [Stacks, Equation 0181], over a
category with finite limits: the coskeleton functor is right adjoint to the skeleton functor, an
adjunction being exactly that bijection, natural in both variables. -/
@[stacks 0181 "the displayed bijection, for `cosk_m` itself",
  sga "4 V 7.1.0" "adjunction i_n* ⊣ i_{n*}",
  sga "4 Vbis 3.0.1"]
noncomputable def coskAdjunction [HasFiniteLimits C] (m : ℕ) :
    SimplicialObject.truncation (C := C) m ⊣ Truncated.cosk m :=
  SimplicialObject.coskAdj m

/-- **Stacks 0AMA**.
A right adjoint of `sk_m` is unique up to unique isomorphism: if `G` and `G'` are both right
adjoint to `sk_m`, there is exactly one isomorphism `G ≅ G'` compatible with the two counits. -/
@[stacks 0AMA "the section's uniqueness assertion, that a representing object `cosk_m V` is \
  unique up to unique isomorphism by the Yoneda lemma; `compatible with the counits` is the \
  form the uniqueness takes for the adjunctions themselves"]
theorem existsUnique_iso_rightAdjoint_truncation {m : ℕ}
    {G G' : SimplicialObject.Truncated C m ⥤ SimplicialObject C}
    (adj : SimplicialObject.truncation (C := C) m ⊣ G)
    (adj' : SimplicialObject.truncation (C := C) m ⊣ G') :
    ∃! e : G ≅ G',
      Functor.whiskerRight e.hom (SimplicialObject.truncation m) ≫ adj'.counit = adj.counit := by
  refine ⟨adj.rightAdjointUniq adj', Adjunction.rightAdjointUniq_hom_counit adj adj',
    fun e he => Iso.ext (NatTrans.ext (funext fun X => ?_))⟩
  apply (adj'.homEquiv (G.obj X) X).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit,
    Adjunction.rightAdjointUniq_hom_app_counit]
  exact NatTrans.congr_app he X

/-- The truncated slice category `(Δ/[n])_{≤ m}` is contravariantly equivalent to the category of
structured arrows `op [n] ⟶ (Δ_{≤ m} ⊆ Δ)ᵒᵖ.obj a`, which is the shape over which a pointwise
right Kan extension along `(Δ_{≤ m} ⊆ Δ)ᵒᵖ` is a limit at `[n]`. -/
noncomputable def truncSliceOpEquivalence (m n : ℕ) :
    (TruncSlice m n)ᵒᵖ ≌
      StructuredArrow (op (SimplexCategory.mk n)) (SimplexCategory.Truncated.inclusion m).op :=
  costructuredArrowOpEquivalence _ _

variable [HasFiniteLimits C]

/-- Over a category with finite limits the diagram `U(n)` has a limit for every `n`, not only for
`n ≤ m`: its shape is equivalent to a shape over which the coskeleton is already a limit. -/
instance hasLimit_sliceDiagram_of_hasFiniteLimits (m : ℕ) (U : SimplicialObject.Truncated C m)
    (n : ℕ) : HasLimit (sliceDiagram m U n) :=
  hasLimit_equivalence_comp (F := StructuredArrow.proj (op (SimplexCategory.mk n))
    (SimplexCategory.Truncated.inclusion m).op ⋙ U) (truncSliceOpEquivalence m n)

/-- The canonical cone over `U(n)` with apex `(cosk_m U)_n`: it is the cone exhibiting `cosk_m U`
as a pointwise right Kan extension of `U` at `[n]`, transported along the equivalence
`truncSliceOpEquivalence`. -/
noncomputable def coskCone (m : ℕ) (U : SimplicialObject.Truncated C m) (n : ℕ) :
    Cone (sliceDiagram m U n) :=
  ((Functor.RightExtension.mk _
    ((SimplexCategory.Truncated.inclusion m).op.ranCounit.app U)).coneAt
      (op (SimplexCategory.mk n))).whisker (truncSliceOpEquivalence m n).functor

/-- The apex of the canonical cone over `U(n)` is the object of `n`-simplices of `cosk_m U`. -/
theorem coskCone_pt (m : ℕ) (U : SimplicialObject.Truncated C m) (n : ℕ) :
    (coskCone m U n).pt = ((Truncated.cosk m).obj U).obj (op (SimplexCategory.mk n)) :=
  rfl

/-- The leg of the canonical cone at an object `α : [k] → [n]` of `(Δ/[n])_{≤ m}` is
`cosk_m U(α) : (cosk_m U)_n ⟶ (cosk_m U)_k` followed by the counit `(cosk_m U)_k ⟶ U_k`. -/
theorem coskCone_π_app (m : ℕ) (U : SimplicialObject.Truncated C m) (n : ℕ)
    (α : TruncSlice m n) :
    (coskCone m U n).π.app (op α) =
      ((Truncated.cosk m).obj U).map α.hom.op ≫
        ((SimplexCategory.Truncated.inclusion m).op.ranCounit.app U).app (op α.left) :=
  rfl

/-- **Stacks 0AMA**.
The degreewise limit formula for the coskeleton: for an `m`-truncated simplicial object `U` of a
category with finite limits the canonical cone over `U(n)` with apex `(cosk_m U)_n` is a limit
cone, so `(cosk_m U)_n` is the limit of `U(n)` over `((Δ/[n])_{≤ m})ᵒᵖ`. -/
@[stacks 0AMA "the degreewise limit formula", sga "4 Vbis 3.0.1" "partial"]
noncomputable def coskConeIsLimit (m : ℕ) (U : SimplicialObject.Truncated C m) (n : ℕ) :
    IsLimit (coskCone m U n) :=
  (Functor.isPointwiseRightKanExtensionRanCounit _ U
    (op (SimplexCategory.mk n))).whiskerEquivalence (truncSliceOpEquivalence m n)

/-- The degreewise limit formula as an isomorphism: `(cosk_m U)_n` is isomorphic to the limit of
the diagram `U(n)` over `((Δ/[n])_{≤ m})ᵒᵖ`. -/
noncomputable def coskObjObjIsoLimit (m : ℕ) (U : SimplicialObject.Truncated C m) (n : ℕ) :
    ((Truncated.cosk m).obj U).obj (op (SimplexCategory.mk n)) ≅ limit (sliceDiagram m U n) :=
  (coskConeIsLimit m U n).conePointUniqueUpToIso (limit.isLimit (sliceDiagram m U n))

/-- A map `φ : [n] → [n']` carries an object `α : [k] → [n]` of `(Δ/[n])_{≤ m}` to
`φ ∘ α : [k] → [n']`, and the leg of `cosk_m U(φ)` at `α` is the leg of the canonical cone in
degree `n'` at `φ ∘ α`. -/
theorem map_comp_coskCone_π_app {m : ℕ} (U : SimplicialObject.Truncated C m) {n n' : ℕ}
    (φ : SimplexCategory.mk n ⟶ SimplexCategory.mk n') (α : TruncSlice m n) :
    ((Truncated.cosk m).obj U).map φ.op ≫ (coskCone m U n).π.app (op α) =
      (coskCone m U n').π.app (op ((CostructuredArrow.map φ).obj α)) := by
  rw [coskCone_π_app, coskCone_π_app, ← Category.assoc, ← Functor.map_comp]
  rfl

/-- **Stacks 0AMA**.
The naturality half of the degreewise limit formula: `cosk_m U(φ)` is the morphism of limits
induced by postcomposition with `φ : [n] → [n']`, the canonical cone in degree `n'` restricted
along that functor being a cone over `U(n)`. -/
@[stacks 0AMA "the second clause of the degreewise limit formula, that for `φ : [n] → [n']` the \
  map `cosk_m U(φ)` comes from the identification of `U(n')` restricted along `φ` with `U(n)`"]
theorem map_eq_coskConeIsLimit_lift {m : ℕ} (U : SimplicialObject.Truncated C m) {n n' : ℕ}
    (φ : SimplexCategory.mk n ⟶ SimplexCategory.mk n') :
    ((Truncated.cosk m).obj U).map φ.op =
      (coskConeIsLimit m U n).lift
        ((coskCone m U n').whisker (CostructuredArrow.map φ).op) :=
  (coskConeIsLimit m U n).uniq
    (show Cone (sliceDiagram m U n) from
      (coskCone m U n').whisker (CostructuredArrow.map φ).op)
    (((Truncated.cosk m).obj U).map φ.op) fun α => map_comp_coskCone_π_app U φ α.unop

end CategoryTheory.SimplicialObject.Truncated

end

end
