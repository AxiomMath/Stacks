module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Commuting
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.GysinCommuting
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.PointClassCommuting

/-!
# Commuting bivariant classes: symmetry and the composite rule

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be a scheme
locally of finite type over `S` and let `c ∈ A^r(Y ⟶ X)` be a bivariant class. This file carries
two general laws about `Stacks.Chow.BivariantCommute`, the relation of Stacks 0FA2, that the
library did not have:

* commuting is symmetric;
* commuting is preserved by composition of bivariant classes: if `C ∈ A^q(Z ⟶ X)` commutes with
  `c` and if `c' ∈ A^p(V ⟶ Z)` commutes with the restriction `res(c) ∈ A^r(Y ×_X Z ⟶ Z)` of `c`
  along `f : Z ⟶ X` in the sense of Stacks 0F9Z, then the composite `c' ∘ C ∈ A^{p+q}(V ⟶ X)` of
  Stacks 0FE0 commutes with `c`.

The second law is the sibling of
`Stacks.Chow.bivariantCommute_of_isBivariantProperPushforward`, which transports commuting along
a proper pushforward in the first argument.

## Main definitions

* `Stacks.Chow.mixedCommuteComparisonHom` — the comparison isomorphism
  `V ×_Z (Y ×_X M) ≅ Y ×_X (V ×_Z M)` for `v : V ⟶ Z` and `τ : M ⟶ Z` over `Z` and `g : Y ⟶ X`
  over `X`, where `Z ⟶ X` is the morphism `f`. This is the identification under which the
  commuting relation of a class over `Z` with a class over `X` is read.
* `Stacks.Chow.bivariantRestrictionCommute` — the restriction of Stacks 0F9Z, re-indexed by the
  structure morphism that `Stacks.Chow.BivariantCommute` reads.
* `Stacks.Chow.bivariantClassAssocSource` — a bivariant class for `v : V ⟶ Z`, re-indexed by the
  structure morphism `(v ≫ f) ≫ sX` of `V` that the composition of Stacks 0FE0 reads.

## Main results

* `Stacks.Chow.BivariantCommute.symm` — commuting is symmetric (no Stacks attribute: see its
  docstring).
* `Stacks.Chow.mixedCommuteComparisonHom_eq` — the mixed comparison isomorphism is the conjugate
  of the three-fold comparison isomorphism of Stacks 0FA2 by the pasting isomorphisms of
  Stacks 0F9Z.
* `Stacks.Chow.bivariantCommute_mixedIteratedCap` — the commuting relation of `c'` with `res(c)`
  over `Z`, read as an identity between iterated cap operations in which only `c` itself occurs.
* `Stacks.Chow.bivariantCommute_of_isBivariantClassComposition` — the composite rule.

## Implementation notes

### The comparison isomorphism: mixed base rather than a four-fold fibre product

The composite rule compares `c' ∩ C ∩ c ∩ α` with `c ∩ c' ∩ C ∩ α`, and the intermediate groups
are indexed by fibre products of four schemes `V`, `Y`, `Z`, `T`. Nothing here, however, needs a
*symmetric* four-fold comparison: the step that moves `c` past `c'` is a commuting statement for
one class over `Z` and one over `X`, so the identification it needs is the mixed-base
`V ×_Z (Y ×_X M) ≅ Y ×_X (V ×_Z M)` of `Stacks.Chow.mixedCommuteComparisonHom`, with `M` the
third factor. It is defined directly by `CategoryTheory.Limits.pullback.lift`, so that its three
projections are `simp` lemmas, and
`Stacks.Chow.mixedCommuteComparisonHom_eq` identifies it with the conjugate of the three-fold
`Stacks.Chow.commuteComparisonHom` of Stacks 0FA2 for `v` and `pullback.snd g f` by the pasting
isomorphisms of Stacks 0F9Z. That identification is the only place the relation between the two
comparisons is used, and `Stacks.Chow.commuteComparisonHom` is left as it stands: extending it to
four factors would make every existing caller carry a factor it does not have.

### Only abstract identifications are transported

Every identification here is a pushforward along an isomorphism of schemes over the base, i.e.
`Stacks.Chow.chowPushforwardOfIso`, and the comparisons are composed and compared as *morphisms*
through `Stacks.Chow.chowPushforwardOfIso_comp_apply` and
`Stacks.Chow.chowPushforwardOfIso_congr_apply`. No equality of schemes is transported and no
`Eq.mpr` on a concrete fibre product is formed; the only `subst`s are the ones already inside
`Stacks.Chow.chowGroupCongr` and `Stacks.Chow.chowGroupDegreeEquiv`, on equalities of structure
morphisms and of degrees.

### The hypotheses carried

The composite rule carries exactly what forming the two data it speaks of carries:
`Stacks.Chow.GysinSystem.IsNaturalUnderBaseChangeIso`, the isomorphism case of Stacks 02TA, which
`Stacks.Chow.bivariantRestriction` needs in order to be a bivariant class (Stacks 0F9Z); and
`Stacks.Chow.ProperPushforwardDescends`, Stacks 02S2 over the base, which
`Stacks.Chow.bivariantCompositeCap` needs (Stacks 0FE0). The composite class itself is carried in
characterized form, as a named argument together with
`Stacks.Chow.IsBivariantClassComposition`, exactly as in
`Stacks.Chow.bivariantCommute_of_isBivariantProperPushforward`.

## References

* [Stacks Project, Tag 0FA2](https://stacks.math.columbia.edu/tag/0FA2)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- Transport along an equality of a degree with itself changes nothing. -/
theorem chowGroupDegreeEquiv_self (C : ChowSituation.{u}) {A : Scheme.{u}} (sA : A ⟶ C.S)
    [LocallyOfFiniteType sA] {k : ℤ} (hk : k = k) (x : chowGroup C sA k) :
    chowGroupDegreeEquiv C sA hk x = x :=
  (chowGroupDegreeEquiv_eq_iff_heq C sA hk x x).2 HEq.rfl

/-! ### The mixed-base comparison isomorphism -/

section MixedComparison

variable {X Y Z V : Scheme.{u}} (g : Y ⟶ X) (f : Z ⟶ X) (v : V ⟶ Z)

/-- The canonical morphism `V ×_Z (Y ×_X M) ⟶ Y ×_X (V ×_Z M)` for a test scheme `τ : M ⟶ Z`:
it sends a point to the same triple of points of `V`, `Y` and `M`, read in the other order. Here
`V` and `M` live over `Z` and `Y` lives over `X`, and `Y ×_X M` is a scheme over `Z` through its
projection to `M`, while `V ×_Z M` is a scheme over `X` through `V ⟶ Z ⟶ X`. -/
def mixedCommuteComparisonHom {M : Scheme.{u}} (τ : M ⟶ Z) :
    pullback v (pullback.snd g (τ ≫ f) ≫ τ) ⟶ pullback g (pullback.fst v τ ≫ (v ≫ f)) :=
  pullback.lift
    (pullback.snd v (pullback.snd g (τ ≫ f) ≫ τ) ≫ pullback.fst g (τ ≫ f))
    (pullback.lift (pullback.fst v (pullback.snd g (τ ≫ f) ≫ τ))
      (pullback.snd v (pullback.snd g (τ ≫ f) ≫ τ) ≫ pullback.snd g (τ ≫ f))
      (by rw [Category.assoc]; exact pullback.condition))
    (by
      simp only [← Category.assoc, pullback.lift_fst]
      simp [pullback.condition])

/-- The projection of the mixed comparison morphism to `Y`. -/
@[reassoc (attr := simp)]
theorem mixedCommuteComparisonHom_fst {M : Scheme.{u}} (τ : M ⟶ Z) :
    mixedCommuteComparisonHom g f v τ ≫ pullback.fst g (pullback.fst v τ ≫ (v ≫ f)) =
      pullback.snd v (pullback.snd g (τ ≫ f) ≫ τ) ≫ pullback.fst g (τ ≫ f) :=
  pullback.lift_fst _ _ _

/-- The projection of the mixed comparison morphism to `V`. -/
@[reassoc (attr := simp)]
theorem mixedCommuteComparisonHom_snd_fst {M : Scheme.{u}} (τ : M ⟶ Z) :
    mixedCommuteComparisonHom g f v τ ≫ pullback.snd g (pullback.fst v τ ≫ (v ≫ f)) ≫
        pullback.fst v τ = pullback.fst v (pullback.snd g (τ ≫ f) ≫ τ) := by
  simp only [mixedCommuteComparisonHom, ← Category.assoc, pullback.lift_snd, pullback.lift_fst]

/-- The projection of the mixed comparison morphism to the test scheme. -/
@[reassoc (attr := simp)]
theorem mixedCommuteComparisonHom_snd_snd {M : Scheme.{u}} (τ : M ⟶ Z) :
    mixedCommuteComparisonHom g f v τ ≫ pullback.snd g (pullback.fst v τ ≫ (v ≫ f)) ≫
        pullback.snd v τ =
      pullback.snd v (pullback.snd g (τ ≫ f) ≫ τ) ≫ pullback.snd g (τ ≫ f) := by
  simp only [mixedCommuteComparisonHom, ← Category.assoc, pullback.lift_snd]

/-- The canonical morphism `Y ×_X (V ×_Z M) ⟶ V ×_Z (Y ×_X M)`, inverse to
`Stacks.Chow.mixedCommuteComparisonHom`. -/
def mixedCommuteComparisonInv {M : Scheme.{u}} (τ : M ⟶ Z) :
    pullback g (pullback.fst v τ ≫ (v ≫ f)) ⟶ pullback v (pullback.snd g (τ ≫ f) ≫ τ) :=
  pullback.lift
    (pullback.snd g (pullback.fst v τ ≫ (v ≫ f)) ≫ pullback.fst v τ)
    (pullback.lift (pullback.fst g (pullback.fst v τ ≫ (v ≫ f)))
      (pullback.snd g (pullback.fst v τ ≫ (v ≫ f)) ≫ pullback.snd v τ)
      (by simp [pullback.condition, pullback.condition_assoc]))
    (by
      simp only [← Category.assoc, pullback.lift_snd]
      simp [pullback.condition])

/-- The projection of the inverse mixed comparison morphism to `V`. -/
@[reassoc (attr := simp)]
theorem mixedCommuteComparisonInv_fst {M : Scheme.{u}} (τ : M ⟶ Z) :
    mixedCommuteComparisonInv g f v τ ≫ pullback.fst v (pullback.snd g (τ ≫ f) ≫ τ) =
      pullback.snd g (pullback.fst v τ ≫ (v ≫ f)) ≫ pullback.fst v τ :=
  pullback.lift_fst _ _ _

/-- The projection of the inverse mixed comparison morphism to `Y`. -/
@[reassoc (attr := simp)]
theorem mixedCommuteComparisonInv_snd_fst {M : Scheme.{u}} (τ : M ⟶ Z) :
    mixedCommuteComparisonInv g f v τ ≫ pullback.snd v (pullback.snd g (τ ≫ f) ≫ τ) ≫
        pullback.fst g (τ ≫ f) = pullback.fst g (pullback.fst v τ ≫ (v ≫ f)) := by
  simp only [mixedCommuteComparisonInv, ← Category.assoc, pullback.lift_snd, pullback.lift_fst]

/-- The projection of the inverse mixed comparison morphism to the test scheme. -/
@[reassoc (attr := simp)]
theorem mixedCommuteComparisonInv_snd_snd {M : Scheme.{u}} (τ : M ⟶ Z) :
    mixedCommuteComparisonInv g f v τ ≫ pullback.snd v (pullback.snd g (τ ≫ f) ≫ τ) ≫
        pullback.snd g (τ ≫ f) =
      pullback.snd g (pullback.fst v τ ≫ (v ≫ f)) ≫ pullback.snd v τ := by
  simp only [mixedCommuteComparisonInv, ← Category.assoc, pullback.lift_snd]

/-- The two mixed comparison morphisms are mutually inverse, in one order. -/
@[simp]
theorem mixedCommuteComparisonHom_comp_inv {M : Scheme.{u}} (τ : M ⟶ Z) :
    mixedCommuteComparisonHom g f v τ ≫ mixedCommuteComparisonInv g f v τ =
      𝟙 (pullback v (pullback.snd g (τ ≫ f) ≫ τ)) := by
  refine pullback.hom_ext ?_ (pullback.hom_ext ?_ ?_) <;> simp

/-- The two mixed comparison morphisms are mutually inverse, in the other order. -/
@[simp]
theorem mixedCommuteComparisonInv_comp_hom {M : Scheme.{u}} (τ : M ⟶ Z) :
    mixedCommuteComparisonInv g f v τ ≫ mixedCommuteComparisonHom g f v τ =
      𝟙 (pullback g (pullback.fst v τ ≫ (v ≫ f))) := by
  refine pullback.hom_ext ?_ (pullback.hom_ext ?_ ?_) <;> simp

/-- The mixed comparison morphism is an isomorphism. -/
instance isIso_mixedCommuteComparisonHom {M : Scheme.{u}} (τ : M ⟶ Z) :
    IsIso (mixedCommuteComparisonHom g f v τ) :=
  ⟨⟨mixedCommuteComparisonInv g f v τ, mixedCommuteComparisonHom_comp_inv g f v τ,
    mixedCommuteComparisonInv_comp_hom g f v τ⟩⟩

/-- The inverse of the mixed comparison morphism is the morphism of the other order. -/
@[simp]
theorem inv_mixedCommuteComparisonHom {M : Scheme.{u}} (τ : M ⟶ Z) :
    inv (mixedCommuteComparisonHom g f v τ) = mixedCommuteComparisonInv g f v τ :=
  IsIso.inv_eq_of_hom_inv_id (mixedCommuteComparisonHom_comp_inv g f v τ)

/-- The structure morphism of `Y ×_X M` over `Z`, read through the pasting isomorphism of
Stacks 0F9Z that presents `Y ×_X M` as a base change of `Y ×_X Z` along `τ`. -/
theorem pullbackLeftPullbackSndIso_inv_comp_structure' {M : Scheme.{u}} (τ : M ⟶ Z) :
    (pullbackLeftPullbackSndIso g f τ).inv ≫
        (pullback.fst (pullback.snd g f) τ ≫ pullback.snd g f) =
      pullback.snd g (τ ≫ f) ≫ τ := by
  rw [pullback.condition (f := pullback.snd g f) (g := τ), ← Category.assoc]
  simp

end MixedComparison

/-- The mixed comparison isomorphism is compatible with the structure morphisms of the two
fibre products over the base. -/
theorem mixedCommuteComparisonHom_comp_structureMorphism (C : ChowSituation.{u})
    {X Y Z V M : Scheme.{u}} (sX : X ⟶ C.S) (g : Y ⟶ X) (f : Z ⟶ X) (v : V ⟶ Z) (τ : M ⟶ Z) :
    mixedCommuteComparisonHom g f v τ ≫
        (pullback.fst g (pullback.fst v τ ≫ (v ≫ f)) ≫ (g ≫ sX)) =
      pullback.fst v (pullback.snd g (τ ≫ f) ≫ τ) ≫ (v ≫ (f ≫ sX)) := by
  rw [← Category.assoc, mixedCommuteComparisonHom_fst]
  simp [pullback.condition_assoc]

/-- The structure morphism of `Y ×_X M` over the base, read through its projection to the test
scheme `M` and the morphism `τ : M ⟶ Z`. -/
theorem pullbackFst_comp_structureMorphism_eq_pullbackSnd (C : ChowSituation.{u})
    {X Y Z M : Scheme.{u}} (sX : X ⟶ C.S) (g : Y ⟶ X) (f : Z ⟶ X) (τ : M ⟶ Z) :
    pullback.fst g (τ ≫ f) ≫ (g ≫ sX) = (pullback.snd g (τ ≫ f) ≫ τ) ≫ (f ≫ sX) := by
  rw [← Category.assoc, pullback.condition]
  simp

/-- The structure morphism of `V ×_Z M` over the base, read through `V ⟶ Z ⟶ X`. -/
theorem pullbackFst_comp_comp_structureMorphism_eq (C : ChowSituation.{u})
    {X Z V M : Scheme.{u}} (sX : X ⟶ C.S) (f : Z ⟶ X) (v : V ⟶ Z) (τ : M ⟶ Z) :
    pullback.fst v τ ≫ (v ≫ (f ≫ sX)) = (pullback.fst v τ ≫ (v ≫ f)) ≫ sX := by
  simp

/-- The pasting isomorphism identifying `(Y ×_X Z) ×_Z (V ×_Z M)`, where the iterated cap
operation of the restriction lands, with `Y ×_X (V ×_Z M)`, where the iterated cap operation of
`c` itself lands. -/
abbrev mixedTargetHom {X Y Z V M : Scheme.{u}} (g : Y ⟶ X) (f : Z ⟶ X) (v : V ⟶ Z) (τ : M ⟶ Z) :
    pullback (pullback.snd g f) (pullback.fst v τ ≫ v) ⟶
      pullback g (pullback.fst v τ ≫ (v ≫ f)) :=
  (pullbackLeftPullbackSndIso g f (pullback.fst v τ ≫ v)).hom ≫
    (pullback.congrHom (rfl : g = g) (Category.assoc (pullback.fst v τ) v f)).hom

/-- The comparison of the two targets is compatible with the structure morphisms over the
base. -/
theorem mixedTargetHom_comp_structureMorphism (C : ChowSituation.{u})
    {X Y Z V M : Scheme.{u}} (sX : X ⟶ C.S) (g : Y ⟶ X) (f : Z ⟶ X) (v : V ⟶ Z) (τ : M ⟶ Z) :
    mixedTargetHom g f v τ ≫ (pullback.fst g (pullback.fst v τ ≫ (v ≫ f)) ≫ (g ≫ sX)) =
      pullback.fst (pullback.snd g f) (pullback.fst v τ ≫ v) ≫
        (pullback.snd g f ≫ (f ≫ sX)) := by
  simp [pullback.condition_assoc]

/-! ### The mixed comparison as a conjugate of the comparison of Stacks 0FA2 -/

section Conjugate

variable {X Y Z V : Scheme.{u}} (g : Y ⟶ X) (f : Z ⟶ X) (v : V ⟶ Z)

/-- **The four-fold comparison.** The mixed comparison isomorphism
`V ×_Z (Y ×_X M) ≅ Y ×_X (V ×_Z M)` is the conjugate, by the pasting isomorphisms of
Stacks 0F9Z, of the three-fold comparison isomorphism
`V ×_Z ((Y ×_X Z) ×_Z M) ≅ (Y ×_X Z) ×_Z (V ×_Z M)` of Stacks 0FA2 for the two morphisms
`v : V ⟶ Z` and `pullback.snd g f : Y ×_X Z ⟶ Z` over `Z`. -/
theorem mixedCommuteComparisonHom_eq {M : Scheme.{u}} (τ : M ⟶ Z) :
    mixedCommuteComparisonHom g f v τ =
      (testBaseChangeIso v (pullback.fst (pullback.snd g f) τ ≫ pullback.snd g f)
            (pullbackLeftPullbackSndIso g f τ).inv (pullback.snd g (τ ≫ f) ≫ τ)
            (pullbackLeftPullbackSndIso_inv_comp_structure' g f τ)).hom ≫
        commuteComparisonHom v (pullback.snd g f) τ ≫ mixedTargetHom g f v τ := by
  refine pullback.hom_ext ?_ (pullback.hom_ext ?_ ?_) <;> simp

end Conjugate

/-- Transporting along the comparison isomorphisms of the two orders in turn changes nothing. -/
private theorem chowPushforwardOfIso_commuteComparisonHom_comp_apply (C : ChowSituation.{u})
    {X Z₁ Z₂ T : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (f₁ : Z₁ ⟶ X)
    [LocallyOfFiniteType f₁] (f₂ : Z₂ ⟶ X) [LocallyOfFiniteType f₂] (t : T ⟶ X)
    [LocallyOfFiniteType t] (k : ℤ)
    (x : chowGroup C (pullback.fst f₁ (pullback.fst f₂ t ≫ f₂) ≫ (f₁ ≫ sX)) k) :
    chowPushforwardOfIso C (pullback.fst f₂ (pullback.fst f₁ t ≫ f₁) ≫ (f₂ ≫ sX))
        (pullback.fst f₁ (pullback.fst f₂ t ≫ f₂) ≫ (f₁ ≫ sX)) (commuteComparisonHom f₂ f₁ t)
        (commuteComparisonHom_comp_structureMorphism C sX f₂ f₁ t) k
      (chowPushforwardOfIso C (pullback.fst f₁ (pullback.fst f₂ t ≫ f₂) ≫ (f₁ ≫ sX))
        (pullback.fst f₂ (pullback.fst f₁ t ≫ f₁) ≫ (f₂ ≫ sX)) (commuteComparisonHom f₁ f₂ t)
        (commuteComparisonHom_comp_structureMorphism C sX f₁ f₂ t) k x) = x := by
  rw [chowPushforwardOfIso_comp_apply,
    chowPushforwardOfIso_congr_apply C _ _ _ (𝟙 _) (commuteComparisonHom_comp_commuteComparisonHom
      f₁ f₂ t) _ (Category.id_comp _), chowPushforwardOfIso_id]

/-! ### Commuting is symmetric -/

section Symm

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Z₁ Z₂ : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (f₁ : Z₁ ⟶ X) [LocallyOfFiniteType f₁] (f₂ : Z₂ ⟶ X)
  [LocallyOfFiniteType f₂] (p₁ p₂ : ℤ)
  (c₁ : BivariantClass C G (f₁ ≫ sX) sX f₁ rfl p₁)
  (c₂ : BivariantClass C G (f₂ ≫ sX) sX f₂ rfl p₂)

/-- Commuting is a symmetric relation. The two identifications that Stacks 0FA2 suppresses are
inverse to one another — the comparison isomorphisms of the two iterated fibre products in the
two orders compose to the identity, and the two transports of degrees are mutually inverse — so
no hypothesis is needed beyond the commuting itself.

This carries no Stacks attribute: Stacks 0FA2 is a remark that *defines* the relation, and
although its wording ("we say `c₁` and `c₂` commute") presupposes that the relation is symmetric,
the tag states no symmetry lemma. -/
theorem BivariantCommute.symm (h : BivariantCommute C G sX f₁ f₂ p₁ p₂ c₁ c₂) :
    BivariantCommute C G sX f₂ f₁ p₂ p₁ c₂ c₁ := by
  intro T t _ k α
  have hA := h t k α
  refine (chowGroupDegreeEquiv C (pullback.fst f₁ (pullback.fst f₂ t ≫ f₂) ≫ (f₁ ≫ sX))
    (by ring : (k - p₁) - p₂ = (k - p₂) - p₁)).injective ?_
  rw [chowGroupDegreeEquiv_chowPushforwardOfIso, ← hA,
    chowPushforwardOfIso_commuteComparisonHom_comp_apply,
    chowGroupDegreeEquiv_chowGroupDegreeEquiv]
  exact (chowGroupDegreeEquiv_self C _ _ _).symm

end Symm

/-! ### Presenting the morphism of a class by an equal morphism -/

section CongrMor

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Z₁ Z₂ : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] {f₁ f₁' : Z₁ ⟶ X} [LocallyOfFiniteType f₁] [LocallyOfFiniteType f₁']

/-- Bivariant classes for two equal morphisms `Z₁ ⟶ X`, each read with the source structure
morphism `Stacks.Chow.BivariantCommute` expects, form the same group. Unlike
`Stacks.Chow.bivariantClassCongr` this moves the source structure morphism along with the
morphism, which is what the two factorizations of one morphism through two different towers
require. -/
def bivariantClassCongrMor (hf : f₁ = f₁') (p : ℤ) :
    BivariantClass C G (f₁ ≫ sX) sX f₁ rfl p ≃+ BivariantClass C G (f₁' ≫ sX) sX f₁' rfl p := by
  subst hf
  exact AddEquiv.refl _

/-- Commuting is unchanged when the morphism of the first class is presented by an equal
morphism. -/
theorem bivariantCommute_congrMor (hf : f₁ = f₁') (f₂ : Z₂ ⟶ X) [LocallyOfFiniteType f₂]
    (p₁ p₂ : ℤ) (c₁ : BivariantClass C G (f₁ ≫ sX) sX f₁ rfl p₁)
    (c₂ : BivariantClass C G (f₂ ≫ sX) sX f₂ rfl p₂)
    (h : BivariantCommute C G sX f₁ f₂ p₁ p₂ c₁ c₂) :
    BivariantCommute C G sX f₁' f₂ p₁ p₂ (bivariantClassCongrMor C G sX hf p₁ c₁) c₂ := by
  subst hf
  exact h

end CongrMor

/-! ### The restriction, indexed the way `BivariantCommute` reads it -/

section RestrictionCommuteForm

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y Z : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (g : Y ⟶ X) [LocallyOfFiniteType g] (f : Z ⟶ X)
  [LocallyOfFiniteType f] (r : ℤ) (hgys : G.IsNaturalUnderBaseChangeIso)
  (c : BivariantClass C G (g ≫ sX) sX g rfl r)

/-- **Stacks 0F9Z.** The restriction `res(c) ∈ A^r(Y ×_X Z ⟶ Z)` of `c` along `f : Z ⟶ X`,
indexed by the structure morphism `pullback.snd g f ≫ (f ≫ sX)` of `Y ×_X Z` over the base
instead of by the equal morphism `pullback.fst g f ≫ (g ≫ sX)` that
`Stacks.Chow.bivariantRestriction` produces. This is the shape
`Stacks.Chow.BivariantCommute` consumes: it reads the source structure morphism of its second
argument as that argument's morphism composed with the structure morphism of the target. The two
morphisms are the same and not the same term, and the transport between them is
`Stacks.Chow.bivariantClassCongrBase`. -/
def bivariantRestrictionCommute :
    BivariantClass C G (pullback.snd g f ≫ (f ≫ sX)) (f ≫ sX) (pullback.snd g f) rfl r :=
  bivariantClassCongrBase C G (pullback.snd g f)
    (pullbackSnd_comp_structureMorphism_eq C (g ≫ sX) sX g rfl f).symm rfl r
    (bivariantRestriction C G (g ≫ sX) sX g rfl f r hgys c)

/-- The re-indexed restriction caps as the restriction does. -/
theorem bivariantRestrictionCommute_cap {M : Scheme.{u}} (m : M ⟶ Z) [LocallyOfFiniteType m]
    (k : ℤ) (x : chowGroup C (m ≫ (f ≫ sX)) k) :
    (bivariantRestrictionCommute C G sX g f r hgys c).cap m k x =
      chowGroupCongr C
        (congrArg (pullback.fst (pullback.snd g f) m ≫ ·)
          (pullbackSnd_comp_structureMorphism_eq C (g ≫ sX) sX g rfl f).symm) (k - r)
        (bivariantRestrictionCap C G (g ≫ sX) sX g rfl f r c m k x) :=
  eq_of_heq
    ((bivariantClassCongrBase_cap C G (pullback.snd g f)
        (pullbackSnd_comp_structureMorphism_eq C (g ≫ sX) sX g rfl f).symm rfl r
        (bivariantRestriction C G (g ≫ sX) sX g rfl f r hgys c) m k x x HEq.rfl).trans
      (chowGroupCongr_heq C _ (k - r) _).symm)

end RestrictionCommuteForm

/-! ### Commuting with a restriction, read on iterated cap operations -/

section MixedCommute

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y Z V : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (g : Y ⟶ X) [LocallyOfFiniteType g] (f : Z ⟶ X)
  [LocallyOfFiniteType f] (v : V ⟶ Z) [LocallyOfFiniteType v] (p r : ℤ)
  (c : BivariantClass C G (g ≫ sX) sX g rfl r)
  (c' : BivariantClass C G (v ≫ (f ≫ sX)) (f ≫ sX) v rfl p)
  (hgys : G.IsNaturalUnderBaseChangeIso)

/-- **The commuting relation with a restriction, read on iterated cap operations.** Let
`c ∈ A^r(Y ⟶ X)` and `c' ∈ A^p(V ⟶ Z)` with `f : Z ⟶ X` and `v : V ⟶ Z`. If `c'` commutes with
the restriction `res(c) ∈ A^r(Y ×_X Z ⟶ Z)` of Stacks 0F9Z, then for every test scheme
`τ : M ⟶ Z` the two iterated cap operations of `c'` and of `c` itself agree, under the mixed
comparison isomorphism `V ×_Z (Y ×_X M) ≅ Y ×_X (V ×_Z M)` and the transport of degrees.

This is the form in which the commuting hypothesis is used: the restriction has disappeared, and
with it the fibre product `Y ×_X Z`. -/
theorem bivariantCommute_mixedIteratedCap
    (h : BivariantCommute C G (f ≫ sX) v (pullback.snd g f) p r c'
      (bivariantRestrictionCommute C G sX g f r hgys c))
    {M : Scheme.{u}} (τ : M ⟶ Z) [LocallyOfFiniteType τ] (k : ℤ)
    (β : chowGroup C (τ ≫ (f ≫ sX)) k) :
    chowPushforwardOfIso C (pullback.fst v (pullback.snd g (τ ≫ f) ≫ τ) ≫ (v ≫ (f ≫ sX)))
        (pullback.fst g (pullback.fst v τ ≫ (v ≫ f)) ≫ (g ≫ sX))
        (mixedCommuteComparisonHom g f v τ)
        (mixedCommuteComparisonHom_comp_structureMorphism C sX g f v τ) ((k - r) - p)
        (c'.cap (pullback.snd g (τ ≫ f) ≫ τ) (k - r)
          (chowGroupCongr C (pullbackFst_comp_structureMorphism_eq_pullbackSnd C sX g f τ) (k - r)
            (c.cap (τ ≫ f) k (chowGroupCongr C (Category.assoc τ f sX).symm k β)))) =
      chowGroupDegreeEquiv C (pullback.fst g (pullback.fst v τ ≫ (v ≫ f)) ≫ (g ≫ sX))
        (by ring : (k - p) - r = (k - r) - p)
        (c.cap (pullback.fst v τ ≫ (v ≫ f)) (k - p)
          (chowGroupCongr C (pullbackFst_comp_comp_structureMorphism_eq C sX f v τ) (k - p)
            (c'.cap τ k β))) := by
  have hres := h τ k β
  rw [bivariantIteratedCap_apply, bivariantIteratedCap_apply,
    bivariantRestrictionCommute_cap, bivariantRestrictionCommute_cap,
    bivariantRestrictionCap_apply, bivariantRestrictionCap_apply,
    chowGroupCongr_chowGroupCongr, chowGroupCongr_chowGroupCongr,
    chowGroupCongr_chowPushforwardOfIso_target,
    chowGroupCongr_chowPushforwardOfIso_target] at hres
  · have key := DFunLike.congr_arg
      (chowPushforwardOfIso C
        (pullback.fst (pullback.snd g f) (pullback.fst v τ ≫ v) ≫
          (pullback.snd g f ≫ (f ≫ sX)))
        (pullback.fst g (pullback.fst v τ ≫ (v ≫ f)) ≫ (g ≫ sX))
        (mixedTargetHom g f v τ) (mixedTargetHom_comp_structureMorphism C sX g f v τ)
        ((k - r) - p)) hres
    rw [← chowGroupDegreeEquiv_chowPushforwardOfIso, chowPushforwardOfIso_comp_apply,
      chowPushforwardOfIso_comp_apply,
      c'.cap_chowPushforwardOfIso (pullback.fst (pullback.snd g f) τ ≫ pullback.snd g f)
        (pullbackLeftPullbackSndIso g f τ).inv (pullback.snd g (τ ≫ f) ≫ τ)
        (pullbackLeftPullbackSndIso_inv_comp_structure' g f τ)
        (pullback.fst g (τ ≫ f) ≫ (g ≫ sX))
        (pullbackFst_comp_structureMorphism_eq_pullbackSnd C sX g f τ) (k - r)
        (by simp [pullback.condition_assoc])
        (c.cap (τ ≫ f) k (chowGroupCongr C (Category.assoc τ f sX).symm k β)) _ rfl,
      chowPushforwardOfIso_comp_apply,
      chowPushforwardOfIso_congr_apply C _ _ _ (mixedCommuteComparisonHom g f v τ)
        (mixedCommuteComparisonHom_eq g f v τ).symm _
        (mixedCommuteComparisonHom_comp_structureMorphism C sX g f v τ) ((k - r) - p),
      chowPushforwardOfIso_congr_apply C _ _
        ((pullbackLeftPullbackSndIso g f (pullback.fst v τ ≫ v)).inv ≫ mixedTargetHom g f v τ)
        (pullback.congrHom (rfl : g = g) (Category.assoc (pullback.fst v τ) v f)).hom
        (by simp) _ (by simp) ((k - p) - r),
      chowPushforwardOfIso_congrHom_cap C G (g ≫ sX) sX g rfl r c
        (Category.assoc (pullback.fst v τ) v f) (by simp) (k - p) (c'.cap τ k β) _
        (pullbackFst_comp_comp_structureMorphism_eq C sX f v τ)] at key
    exact key
  · simp [pullback.condition_assoc]
  · simp [pullback.condition_assoc]

end MixedCommute

/-! ### The composite rule -/

section Composite

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y Z V : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (g : Y ⟶ X) [LocallyOfFiniteType g] (f : Z ⟶ X)
  [LocallyOfFiniteType f] (v : V ⟶ Z) [LocallyOfFiniteType v] (p q r : ℤ)
  (c' : BivariantClass C G (v ≫ (f ≫ sX)) (f ≫ sX) v rfl p)

/-- `c' ∈ A^p(V ⟶ Z)` re-indexed by the structure morphism `(v ≫ f) ≫ sX` of `V` over the base
rather than by the equal morphism `v ≫ (f ≫ sX)`. The composition of Stacks 0FE0 reads the
source structure morphism of the composite `c' ∘ C` as the former, while
`Stacks.Chow.BivariantCommute` reads the source structure morphism of `c'` over `Z` as the
latter; the two are the same morphism and not the same term. -/
def bivariantClassAssocSource :
    BivariantClass C G ((v ≫ f) ≫ sX) (f ≫ sX) v (Category.assoc v f sX).symm p :=
  bivariantClassCongrBase C G v (Category.assoc v f sX).symm rfl p c'

/-- The re-indexed class caps as `c'` does. -/
theorem bivariantClassAssocSource_cap {M : Scheme.{u}} (m : M ⟶ Z) [LocallyOfFiniteType m]
    (k : ℤ) (x : chowGroup C (m ≫ (f ≫ sX)) k) :
    (bivariantClassAssocSource C G sX f v p c').cap m k x =
      chowGroupCongr C
        (congrArg (pullback.fst v m ≫ ·) (Category.assoc v f sX).symm) (k - p)
        (c'.cap m k x) :=
  eq_of_heq
    ((bivariantClassCongrBase_cap C G v (Category.assoc v f sX).symm rfl p c' m k x x
        HEq.rfl).trans (chowGroupCongr_heq C _ (k - p) _).symm)

variable (c : BivariantClass C G (g ≫ sX) sX g rfl r)
  (bigC : BivariantClass C G (f ≫ sX) sX f rfl q)
  (d : BivariantClass C G ((v ≫ f) ≫ sX) sX (v ≫ f) rfl (p + q))
  (hgys : G.IsNaturalUnderBaseChangeIso) (hpp : ProperPushforwardDescends C)

/-- **The composite rule for commuting bivariant classes.** Let `c ∈ A^r(Y ⟶ X)`, let
`C ∈ A^q(Z ⟶ X)` and let `c' ∈ A^p(V ⟶ Z)`, and let `d ∈ A^{p+q}(V ⟶ X)` be the composite
`c' ∘ C` of Stacks 0FE0. If `C` commutes with `c`, and if `c'` commutes with the restriction
`res(c) ∈ A^r(Y ×_X Z ⟶ Z)` of `c` along `f` in the sense of Stacks 0F9Z, then `d` commutes
with `c`.

This is the sibling of `Stacks.Chow.bivariantCommute_of_isBivariantProperPushforward`: there
commuting is transported along a proper pushforward in the first argument, here along a
composition. -/
theorem bivariantCommute_of_isBivariantClassComposition
    (hd : IsBivariantClassComposition C G ((v ≫ f) ≫ sX) (f ≫ sX) sX v f
      (Category.assoc v f sX).symm rfl hpp p q
      (bivariantClassAssocSource C G sX f v p c') bigC d)
    (h1 : BivariantCommute C G sX f g q r bigC c)
    (h2 : BivariantCommute C G (f ≫ sX) v (pullback.snd g f) p r c'
      (bivariantRestrictionCommute C G sX g f r hgys c)) :
    BivariantCommute C G sX (v ≫ f) g (p + q) r d c := by
  rw [isBivariantClassComposition_iff] at hd
  intro T t _ k α
  refine (chowGroupDegreeEquiv C _
    (by ring : (k - r) - (p + q) = ((k - r) - q) - p)).injective ?_
  rw [bivariantIteratedCap_apply, bivariantIteratedCap_apply,
    chowGroupDegreeEquiv_chowPushforwardOfIso, hd, bivariantCompositeCap_apply,
    chowGroupDegreeEquiv_chowGroupDegreeEquiv]
  have hX := DFunLike.congr_arg
    (chowPushforwardOfIso C (pullback.fst g (pullback.fst f t ≫ f) ≫ (g ≫ sX))
      (pullback.fst f (pullback.fst g t ≫ g) ≫ (f ≫ sX)) (commuteComparisonHom g f t)
      (commuteComparisonHom_comp_structureMorphism C sX g f t) ((k - r) - q)) (h1 t k α)
  rw [chowPushforwardOfIso_commuteComparisonHom_comp_apply, bivariantIteratedCap_apply,
    bivariantIteratedCap_apply] at hX
  rw [hX, properChowPushforward_eq_chowPushforwardOfIso, bivariantClassAssocSource_cap,
    c.cap_transport_eq (pullback.fst (v ≫ f) t ≫ (v ≫ f))
      (by ring : k - (p + q) = (k - q) - p)
      (by ring : (k - (p + q)) - r = ((k - r) - q) - p)
      (by ring : ((k - q) - p) - r = ((k - r) - q) - p) _,
    ← chowGroupCongr_chowGroupDegreeEquiv, hd, bivariantCompositeCap_apply,
    properChowPushforward_eq_chowPushforwardOfIso,
    c'.cap_chowPushforwardOfIso (pullback.fst f (pullback.fst g t ≫ g))
      (commuteComparisonHom g f t)
      (pullback.snd g (pullback.fst f t ≫ f) ≫ pullback.fst f t)
      (commuteComparisonHom_fst g f t)
      (pullback.fst g (pullback.fst f t ≫ f) ≫ (g ≫ sX))
      (pullbackFst_comp_structureMorphism_eq_pullbackSnd C sX g f (pullback.fst f t))
      ((k - r) - q) (commuteComparisonHom_comp_structureMorphism C sX g f t) _ _ rfl,
    chowGroupCongr_chowPushforwardOfIso_target, chowPushforwardOfIso_comp_apply,
    chowPushforwardOfIso_comp_apply,
    chowGroupCongr_chowPushforwardOfIso_target,
    c.cap_chowPushforwardOfIso (pullback.fst (v ≫ f) t ≫ (v ≫ f))
      (pullbackRightPullbackFstIso f t v).hom
      (pullback.fst v (pullback.fst f t) ≫ (v ≫ f))
      (by rw [← Category.assoc, pullbackRightPullbackFstIso_hom_fst])
      (pullback.fst v (pullback.fst f t) ≫ ((v ≫ f) ≫ sX))
      (Category.assoc (pullback.fst v (pullback.fst f t)) (v ≫ f) sX).symm
      ((k - q) - p) (by simp) _ _ rfl,
    bivariantClassAssocSource_cap, chowGroupCongr_chowGroupCongr]
  · have hcore := bivariantCommute_mixedIteratedCap C G sX g f v p r c c' hgys h2
      (pullback.fst f t) (k - q) (bigC.cap t k α)
    have hmorph : mixedCommuteComparisonHom g f v (pullback.fst f t) ≫
        (testBaseChangeIso g (pullback.fst (v ≫ f) t ≫ (v ≫ f))
          (pullbackRightPullbackFstIso f t v).hom
          (pullback.fst v (pullback.fst f t) ≫ (v ≫ f))
          (by rw [← Category.assoc, pullbackRightPullbackFstIso_hom_fst])).hom =
        (testBaseChangeIso v (pullback.fst f (pullback.fst g t ≫ g))
            (commuteComparisonHom g f t)
            (pullback.snd g (pullback.fst f t ≫ f) ≫ pullback.fst f t)
            (commuteComparisonHom_fst g f t)).hom ≫
          (pullbackRightPullbackFstIso f (pullback.fst g t ≫ g) v).hom ≫
            commuteComparisonHom (v ≫ f) g t := by
      refine pullback.hom_ext ?_ (pullback.hom_ext ?_ ?_) <;> simp
    have key := DFunLike.congr_arg
      (chowGroupDegreeEquiv C
        (pullback.fst g (pullback.fst (v ≫ f) t ≫ (v ≫ f)) ≫ (g ≫ sX))
        (by ring : ((k - q) - r) - p = ((k - r) - q) - p))
      (DFunLike.congr_arg
        (chowPushforwardOfIso C
          (pullback.fst g (pullback.fst v (pullback.fst f t) ≫ (v ≫ f)) ≫ (g ≫ sX))
          (pullback.fst g (pullback.fst (v ≫ f) t ≫ (v ≫ f)) ≫ (g ≫ sX))
          (testBaseChangeIso g (pullback.fst (v ≫ f) t ≫ (v ≫ f))
            (pullbackRightPullbackFstIso f t v).hom
            (pullback.fst v (pullback.fst f t) ≫ (v ≫ f))
            (by rw [← Category.assoc, pullbackRightPullbackFstIso_hom_fst])).hom
          (by simp) (((k - q) - r) - p)) hcore)
    rw [← chowGroupDegreeEquiv_chowPushforwardOfIso,
      chowGroupDegreeEquiv_chowGroupDegreeEquiv, chowPushforwardOfIso_comp_apply,
      chowPushforwardOfIso_congr_apply C _ _ _
        ((testBaseChangeIso v (pullback.fst f (pullback.fst g t ≫ g))
            (commuteComparisonHom g f t)
            (pullback.snd g (pullback.fst f t ≫ f) ≫ pullback.fst f t)
            (commuteComparisonHom_fst g f t)).hom ≫
          (pullbackRightPullbackFstIso f (pullback.fst g t ≫ g) v).hom ≫
            commuteComparisonHom (v ≫ f) g t)
        hmorph _ (by simp [pullback.condition, pullback.condition_assoc])
        (((k - q) - r) - p),
      chowGroupDegreeEquiv_chowPushforwardOfIso,
      c'.cap_transport_eq (pullback.snd g (pullback.fst f t ≫ f) ≫ pullback.fst f t)
        (by ring : (k - q) - r = (k - r) - q)
        (by ring : ((k - q) - r) - p = ((k - r) - q) - p)
        (by ring : ((k - r) - q) - p = ((k - r) - q) - p) _,
      chowGroupDegreeEquiv_self, ← chowGroupCongr_chowGroupDegreeEquiv] at key
    exact key
  · simp
  · simp

end Composite

end Stacks.Chow

end
