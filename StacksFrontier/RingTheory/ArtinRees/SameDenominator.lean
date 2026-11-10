module

public import StacksFrontier.RingTheory.ArtinRees.AssociatedGradedRing

/-!
# The denominator criterion for an identity-induced comparison of associated graded algebras

Let `A` be a commutative ring, `J` an ideal and `R`, `S` two further ideals. The comparison of
`AssociatedGraded.pieceEquiv` between `Gr_J(A ⧸ R)` and `Gr_J(A ⧸ S)` exists — and is induced by
the identity of `A`, `AssociatedGraded.GradedAlgEquiv.IsInducedByIdentity` — as soon as the two
denominators `J^(n+1) + R` and `J^(n+1) + S` cut the same submodule out of `J^n`. That condition
is the one `Stacks.ArtinRees.SameDenominator` names, spelt elementwise: for every `z ∈ J^n`,
`z` lies in `J^(n+1) + R` exactly when it lies in `J^(n+1) + S`.

Equivalently — and this is why the condition rather than the comparison is what propagates — it
says that the two surjections of `J^n` onto the degree `n` pieces of `Gr_J(A ⧸ R)` and of
`Gr_J(A ⧸ S)` have the same kernel. Written that way the condition is a statement about the two
quotient *rings*, and `Stacks.ArtinRees.SameDenominator.mem_sup_iff_mem_map` reads it as such: for
`z ∈ J^n`, the class of `z` in `A ⧸ R` lies in the `n+1`-st power of the ideal `J` generates there
exactly when the class of `z` in `A ⧸ S` does.

`AssociatedGraded.presentation_denominator_eq` is the Artin-Rees source of the condition: two maps
sharing an Artin-Rees constant and congruent modulo one power more than it satisfy it. What this
file adds is the passage from the condition to the bundled comparison, so that a chain of
reasoning about the condition alone can be cashed in at the end.

## Main definitions

* `Stacks.ArtinRees.SameDenominator`: the condition.

## Main results

* `Stacks.ArtinRees.sameDenominator_of_isArtinReesConstant`: the Artin-Rees source of the
  condition.
* `Stacks.ArtinRees.SameDenominator.associatedGradedAlgEquiv` and
  `Stacks.ArtinRees.SameDenominator.isInducedByIdentity`: **the condition produces a comparison of
  the associated graded algebras of the two quotients which is induced by the identity of `A`**,
  bundled as `Stacks.ArtinRees.SameDenominator.exists_gradedAlgEquiv_isInducedByIdentity`.

## References

* [Stacks Project, Tag 07VF](https://stacks.math.columbia.edu/tag/07VF)
-/

@[expose] public section

universe u v

namespace Stacks.ArtinRees

open AssociatedGraded

variable {A : Type u} [CommRing A]

/-- **Membership in the image of an ideal in a quotient ring**: the class of `z` modulo `R` lies
in the image of `K` exactly when `z` lies in `K + R`. -/
theorem mk_mem_map_iff (R K : Ideal A) (z : A) :
    Ideal.Quotient.mk R z ∈ K.map (Ideal.Quotient.mk R) ↔ z ∈ K ⊔ R := by
  rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    show Ideal.comap (Ideal.Quotient.mk R) (⊥ : Ideal (A ⧸ R)) = R from Ideal.mk_ker]

/-- **The denominator criterion**: the ideals `J^(n+1) + R` and `J^(n+1) + S` cut the same
subset out of `J^n`, for every `n`. -/
def SameDenominator (J R S : Ideal A) : Prop :=
  ∀ (n : ℕ) (z : A), z ∈ J ^ n → (z ∈ J ^ (n + 1) ⊔ R ↔ z ∈ J ^ (n + 1) ⊔ S)

namespace SameDenominator

variable {J R S : Ideal A}

/-- The denominator criterion is symmetric in `R` and `S`. -/
theorem symm (h : SameDenominator J R S) : SameDenominator J S R :=
  fun n z hz => (h n z hz).symm

/-- Every ideal `R` satisfies the denominator criterion with itself. -/
theorem refl (J R : Ideal A) : SameDenominator J R R := fun _ _ _ => Iff.rfl

/-- The denominator criterion is transitive: if it holds for `R, S` and for `S, T`, it holds for
`R, T`. -/
theorem trans {T : Ideal A} (h : SameDenominator J R S) (h' : SameDenominator J S T) :
    SameDenominator J R T :=
  fun n z hz => (h n z hz).trans (h' n z hz)

/-- The criterion, read in the two quotient rings: for `z ∈ J^n`, the class of `z` modulo `R` lies
in the `n+1`-st power of the ideal `J` generates in `A ⧸ R` exactly when the class of `z` modulo
`S` lies in the `n+1`-st power of the ideal `J` generates in `A ⧸ S`. -/
theorem mem_sup_iff_mem_map (h : SameDenominator J R S) (n : ℕ) {z : A} (hz : z ∈ J ^ n) :
    Ideal.Quotient.mk R z ∈ (J ^ (n + 1)).map (Ideal.Quotient.mk R) ↔
      Ideal.Quotient.mk S z ∈ (J ^ (n + 1)).map (Ideal.Quotient.mk S) := by
  rw [mk_mem_map_iff, mk_mem_map_iff]
  exact h n z hz

/-- The criterion is the equality, for every `n`, of the preimages in `J^n` of the denominators. -/
private theorem iff_comap_subtype_eq (J R S : Ideal A) :
    SameDenominator J R S ↔ ∀ n : ℕ,
      (power (M := A) J (n + 1) ⊔ R).comap (power (M := A) J n).subtype =
        (power (M := A) J (n + 1) ⊔ S).comap (power (M := A) J n).subtype := by
  simp only [SameDenominator, ← ring_power_eq, Submodule.ext_iff, Submodule.mem_comap,
    Submodule.subtype_apply, Subtype.forall]

/-- The criterion, read as an equality of submodules of `J^n`: the two denominators have equal
preimages in `J^n`. -/
theorem comap_subtype_eq (h : SameDenominator J R S) (n : ℕ) :
    (power (M := A) J (n + 1) ⊔ R).comap (power (M := A) J n).subtype =
      (power (M := A) J (n + 1) ⊔ S).comap (power (M := A) J n).subtype :=
  (iff_comap_subtype_eq J R S).1 h n

/-- **The comparison of the associated graded algebras of the two quotients that the criterion
produces.** Degreewise it is `AssociatedGraded.pieceEquiv`, which is `Gr_J(A)`-linear by
`AssociatedGraded.pieceEquiv_homogeneousSMul`, multiplicative by
`AssociatedGraded.pieceEquiv_homogeneousMul` and unital by
`AssociatedGraded.pieceEquiv_homogeneousOne`. -/
noncomputable def associatedGradedAlgEquiv (h : SameDenominator J R S) :
    AssociatedGraded.GradedAlgEquiv J (A ⧸ R) (A ⧸ S) where
  toPieceEquiv n := pieceEquiv J R S n (h.comap_subtype_eq n)
  map_homogeneousSMul i j a x :=
    pieceEquiv_homogeneousSMul J R S i j (h.comap_subtype_eq j) (h.comap_subtype_eq (i + j)) a x
  map_homogeneousMul i j x y :=
    pieceEquiv_homogeneousMul J R S i j (h.comap_subtype_eq i) (h.comap_subtype_eq j)
      (h.comap_subtype_eq (i + j)) x y
  map_homogeneousOne := pieceEquiv_homogeneousOne J R S (h.comap_subtype_eq 0)

/-- **The comparison the criterion produces is induced by the identity of `A`**: it carries the
class of `z ∈ J^n` modulo `R` to the class of the same `z` modulo `S`, which is
`AssociatedGraded.pieceEquiv_mk`. -/
theorem isInducedByIdentity (h : SameDenominator J R S) :
    h.associatedGradedAlgEquiv.IsInducedByIdentity :=
  fun n z => pieceEquiv_mk J R S n (h.comap_subtype_eq n) z

/-- **The criterion gives an identity-induced comparison of the associated graded algebras of the
two quotients.** -/
theorem exists_gradedAlgEquiv_isInducedByIdentity (h : SameDenominator J R S) :
    ∃ e : AssociatedGraded.GradedAlgEquiv J (A ⧸ R) (A ⧸ S), e.IsInducedByIdentity :=
  ⟨h.associatedGradedAlgEquiv, h.isInducedByIdentity⟩

end SameDenominator

/-- **The class of `z ∈ J^n` in the degree `n` piece of `Gr_J(A ⧸ T)` vanishes exactly when `z`
lies in the `n`-th denominator.** The degree `n` piece is `J^n (A ⧸ T)` modulo `J^(n+1) (A ⧸ T)`,
so the class of the class of `z` vanishes exactly when the class of `z` lies in `J^(n+1)(A ⧸ T)`,
which by `Stacks.ArtinRees.mk_mem_map_iff` is membership of `z` in `J^(n+1) + T`. -/
theorem mk_mkQ_eq_zero_iff (J T : Ideal A) (n : ℕ) {z : A} (hz : z ∈ power (M := A) J n) :
    AssociatedGraded.mk J n
        ⟨Ideal.Quotient.mk T z, mk_mem_power_quotient J T n hz⟩ = 0 ↔
      z ∈ J ^ (n + 1) ⊔ T := by
  rw [AssociatedGraded.mk, Submodule.Quotient.mk_eq_zero]
  change Ideal.Quotient.mk T z ∈ power (M := A ⧸ T) J (n + 1) ↔ _
  rw [← mem_power_map_iff J T (n + 1), ring_power_eq, ← Ideal.map_pow, mk_mem_map_iff]

/-- **The criterion is exactly the existence of an identity-induced comparison.** The comparison
carries the class of `z ∈ J^n` modulo `R` to the class of the same `z` modulo `S` and is
injective, so one class vanishes exactly when the other does — and by
`Stacks.ArtinRees.mk_mkQ_eq_zero_iff` those two vanishings are the two memberships the criterion
compares.

Together with `Stacks.ArtinRees.SameDenominator.exists_gradedAlgEquiv_isInducedByIdentity` this
says that `∃ e, e.IsInducedByIdentity` *is* the kernel equality
`ker(J^n ↠ Gr_n(A ⧸ R)) = ker(J^n ↠ Gr_n(A ⧸ S))`. -/
theorem sameDenominator_of_isInducedByIdentity {J R S : Ideal A}
    (e : AssociatedGraded.GradedAlgEquiv J (A ⧸ R) (A ⧸ S)) (he : e.IsInducedByIdentity) :
    SameDenominator J R S := by
  intro n z hz
  have hzp : z ∈ power (M := A) J n := (ring_power_eq J n).ge hz
  rw [← mk_mkQ_eq_zero_iff J R n hzp, ← mk_mkQ_eq_zero_iff J S n hzp, ← he n ⟨z, hzp⟩,
    LinearEquiv.map_eq_zero_iff]

/-- **The denominator criterion and the identity-induced comparison are equivalent.** -/
theorem sameDenominator_iff_exists_isInducedByIdentity (J R S : Ideal A) :
    SameDenominator J R S ↔
      ∃ e : AssociatedGraded.GradedAlgEquiv J (A ⧸ R) (A ⧸ S), e.IsInducedByIdentity :=
  ⟨SameDenominator.exists_gradedAlgEquiv_isInducedByIdentity,
    fun ⟨e, he⟩ => sameDenominator_of_isInducedByIdentity e he⟩

/-- **The Artin-Rees source of the criterion.** If `c` works in the Artin-Rees lemma for two
`A`-linear maps `g, g' : L → A` and the two agree modulo `J^(c+1)`, then the images of `g` and of
`g'` satisfy the denominator criterion. This is
`AssociatedGraded.presentation_denominator_eq`, read elementwise. -/
theorem sameDenominator_of_isArtinReesConstant (J : Ideal A) {L : Type v} [AddCommGroup L]
    [Module A L] (g g' : L →ₗ[A] A) (c : ℕ) (hg : IsArtinReesConstant J g c)
    (hg' : IsArtinReesConstant J g' c) (hgg' : CongruentModPow J g g' (c + 1)) :
    SameDenominator J (LinearMap.range g) (LinearMap.range g') := by
  refine (SameDenominator.iff_comap_subtype_eq J _ _).2 (fun n => ?_)
  exact presentation_denominator_eq J g g' c n hg hg' hgg'

end Stacks.ArtinRees

end
