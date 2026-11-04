module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CorrespondenceMonoidal
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.Motives
public import StacksFrontier.CategoryTheory.Graded.TwistedKaroubiMonoidal

/-!
# The symmetric monoidal structure on Chow motives

Let `k` be a field. **Stacks 0FGC**: the category `M_k` of Chow motives is symmetric monoidal for

  `(X, p, m) ⊗ (Y, q, n) = (X × Y, p ⊗ q, m + n)`,

with the tensor product of correspondences `a ⊗ a'` on morphisms, with the obvious associativity
and commutativity constraints, and with unit `𝟏 = (Spec(k), 1, 0)`.

The source's proof is "follows readily from Lemma 0FG7". Here Lemma 0FG7 is the symmetric
monoidal structure on the category of correspondences
(`Stacks.WeilCohomology.CorrespondenceCategory.symmetricCategory`). Its tensor product adds
degrees and its constraints, the graphs of the constraints of products of schemes, have degree
zero (`Stacks.WeilCohomology.CorrespondenceCategory.isGradedMonoidal` and `isGradedBraided`).
The passage to the triples `(X, p, m)` is
`CategoryTheory.GradedCategory.TwistedKaroubi.symmetricCategory`. The coherence axioms are
inherited along the faithful functor forgetting the twist.

## Main definitions

* `Stacks.WeilCohomology.ChowMotiveCat.monoidalCategory`,
  `Stacks.WeilCohomology.ChowMotiveCat.braidedCategory`,
  `Stacks.WeilCohomology.ChowMotiveCat.symmetricCategory`: **Stacks 0FGC**.
* `Stacks.WeilCohomology.ChowMotiveCat.tateTensorIso`: `𝟏(n) ⊗ 𝟏(m) ≅ 𝟏(n + m)`.
* `Stacks.WeilCohomology.ChowMotiveCat.twistIso`: `M ⊗ 𝟏(n) ≅ (X, p, m + n)` for
  `M = (X, p, m)`.
* `Stacks.WeilCohomology.ChowMotiveCat.hTensorTateIso`: `(X, 1, m) ≅ h(X) ⊗ 𝟏(m)`.
* `Stacks.WeilCohomology.ChowMotiveCat.tateHasInverse`, `tateExactPairing`,
  `tateExactPairing'`: `𝟏(n)` is invertible, and `𝟏(m)` and `𝟏(-m)` are dual to each other.

## Main results

* `Stacks.WeilCohomology.ChowMotiveCat.tensorObj_mk'_scheme`, `tensorObj_mk'_p`,
  `tensorObj_mk'_twist`: `(X, p, m) ⊗ (Y, q, n) = (X × Y, p ⊗ q, m + n)`.
* `Stacks.WeilCohomology.ChowMotiveCat.tensorHom_val_eq_homOf`: on morphisms the tensor product is
  the tensor product of correspondences.
* `Stacks.WeilCohomology.ChowMotiveCat.tensorUnit_eq_tate`: the unit is `𝟏 = (Spec(k), 1, 0)`.
* `Stacks.WeilCohomology.ChowMotiveCat.associator_hom_val` and
  `Stacks.WeilCohomology.ChowMotiveCat.braiding_hom_val`: the constraints are the graphs of the
  associativity and commutativity isomorphisms of products of schemes, cut down by the
  projectors.
* `Stacks.WeilCohomology.ChowMotiveCat.isInvertible_tate`: `𝟏(n)` is invertible.

## References

* [Stacks Project, Tag 0FGC](https://stacks.math.columbia.edu/tag/0FGC)
* [Stacks Project, Tag 0FG7](https://stacks.math.columbia.edu/tag/0FG7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.GradedCategory MonoidalCategory Opposite

universe u

namespace Stacks.WeilCohomology

namespace ChowMotiveCat

variable (k : Type u) [Field k]

/-- **Stacks Project, Tag 0FGC.** The category `M_k` of Chow motives is monoidal for
`(X, p, m) ⊗ (Y, q, n) = (X × Y, p ⊗ q, m + n)`, with the tensor product of correspondences on
morphisms, unit `𝟏 = (Spec(k), 1, 0)`, and the associativity constraint of correspondences (the
graph of the associativity isomorphism of products of schemes) cut down by the projectors. -/
@[stacks 0FGC "M_k is monoidal for (X,p,m) ⊗ (Y,q,n) = (X × Y, p ⊗ q, m + n), unit (Spec k, 1, 0)"]
instance monoidalCategory : MonoidalCategory (ChowMotiveCat k) :=
  TwistedKaroubi.monoidalCategory

/-- **Stacks Project, Tag 0FGC.** The category `M_k` of Chow motives is braided by the
commutativity constraint of correspondences, the graph of the factor switch
`X × Y ≅ Y × X`, cut down by the projectors. -/
@[stacks 0FGC "the commutativity constraint of M_k"]
instance braidedCategory : BraidedCategory (ChowMotiveCat k) :=
  TwistedKaroubi.braidedCategory

/-- **Stacks Project, Tag 0FGC.** The category `M_k` of Chow motives is symmetric monoidal with
the obvious associativity and commutativity constraints and with unit `𝟏 = (Spec(k), 1, 0)`. -/
@[stacks 0FGC "M_k is symmetric monoidal"]
instance symmetricCategory : SymmetricCategory (ChowMotiveCat k) :=
  TwistedKaroubi.symmetricCategory

variable {k}

/-- The underlying scheme of `M ⊗ N` is the product of the underlying schemes of `M` and `N`. -/
@[simp]
theorem tensorObj_scheme (M N : ChowMotiveCat k) : (M ⊗ N).scheme = M.scheme ⊗ N.scheme :=
  rfl

/-- The twist of `M ⊗ N` is the sum of the twists of `M` and `N`. -/
@[simp]
theorem tensorObj_twist (M N : ChowMotiveCat k) : (M ⊗ N).twist = M.twist + N.twist :=
  rfl

/-- The projector of `M ⊗ N` is the tensor product of the projectors of `M` and `N`. -/
theorem tensorObj_p (M N : ChowMotiveCat k) : (M ⊗ N).p = M.p ⊗ₘ N.p :=
  rfl

/-- The tensor product of homogeneous morphisms of correspondences is the tensor product of
correspondences: `homOf r a ⊗ homOf r' b = homOf (r + r') (a ⊗ b)`. -/
theorem homOf_tensorHom_homOf {X Y X' Y' : (SmoothProjectiveScheme k).FullSubcategory} {r r' : ℤ}
    (a : SmoothProjectiveCorr X Y r) (b : SmoothProjectiveCorr X' Y' r') :
    homOf r a ⊗ₘ homOf r' b = homOf (r + r') (CorrespondenceCategory.tensorCorr r r' a b) := by
  have h := CorrespondenceCategory.tensorHom_of_of (X₁ := GradedCompositionData.Obj.mk X)
    (Y₁ := GradedCompositionData.Obj.mk Y) (X₂ := GradedCompositionData.Obj.mk X')
    (Y₂ := GradedCompositionData.Obj.mk Y') a b
  rw [CorrespondenceCategory.tensorHom_eq, homOf, homOf, homOf, DirectSum.lof_eq_of,
    DirectSum.lof_eq_of, DirectSum.lof_eq_of, h]

/-- The underlying scheme of `(X, p, m) ⊗ (Y, q, n)` is `X × Y`. -/
@[simp]
theorem tensorObj_mk'_scheme (X Y : (SmoothProjectiveScheme k).FullSubcategory)
    (p : SmoothProjectiveCorr X X 0)
    (q : SmoothProjectiveCorr Y Y 0)
    (hp : (canonicalCorrespondenceCompositionData k).comp p p = p)
    (hq : (canonicalCorrespondenceCompositionData k).comp q q = q) (m n : ℤ) :
    (mk' X p hp m ⊗ mk' Y q hq n).scheme = X ⊗ Y :=
  rfl

/-- **Stacks Project, Tag 0FGC.** The tensor product of motives on objects:
`(X, p, m) ⊗ (Y, q, n) = (X × Y, p ⊗ q, m + n)`; this is the projector, `p ⊗ q`, the tensor product
of correspondences (`tensorObj_mk'_scheme` and `tensorObj_mk'_twist` give `X × Y` and `m + n`). -/
@[stacks 0FGC "(X, p, m) ⊗ (Y, q, n) = (X × Y, p ⊗ q, m + n)", simp]
theorem tensorObj_mk'_p (X Y : (SmoothProjectiveScheme k).FullSubcategory)
    (p : SmoothProjectiveCorr X X 0)
    (q : SmoothProjectiveCorr Y Y 0)
    (hp : (canonicalCorrespondenceCompositionData k).comp p p = p)
    (hq : (canonicalCorrespondenceCompositionData k).comp q q = q) (m n : ℤ) :
    (mk' X p hp m ⊗ mk' Y q hq n).p = homOf (0 + 0) (CorrespondenceCategory.tensorCorr 0 0 p q) :=
  homOf_tensorHom_homOf p q

/-- The twist of `(X, p, m) ⊗ (Y, q, n)` is `m + n`. -/
@[simp]
theorem tensorObj_mk'_twist (X Y : (SmoothProjectiveScheme k).FullSubcategory)
    (p : SmoothProjectiveCorr X X 0)
    (q : SmoothProjectiveCorr Y Y 0)
    (hp : (canonicalCorrespondenceCompositionData k).comp p p = p)
    (hq : (canonicalCorrespondenceCompositionData k).comp q q = q) (m n : ℤ) :
    (mk' X p hp m ⊗ mk' Y q hq n).twist = m + n :=
  rfl

/-- The projector of `M ⊗ N` is the tensor product of the projectors of `M` and `N`. -/
theorem homOf_tensorObj_projector (M N : ChowMotiveCat k) :
    homOf 0 (M ⊗ N).projector =
      homOf (0 + 0) (CorrespondenceCategory.tensorCorr 0 0 M.projector N.projector) := by
  rw [homOf_projector, ← homOf_tensorHom_homOf, homOf_projector, homOf_projector]
  rfl

/-- **Stacks Project, Tag 0FGC.** The tensor product of morphisms of motives is the tensor
product of correspondences: if `f : (X, p, m) ⟶ (Y, q, n)` is the correspondence
`a ∈ Corr^{n-m}(X, Y)` and `f' : (X', p', m') ⟶ (Y', q', n')` is `a' ∈ Corr^{n'-m'}(X', Y')`, then
`f ⊗ f'` is `a ⊗ a' ∈ Corr^{(n-m)+(n'-m')}(X × X', Y × Y')`. -/
@[stacks 0FGC "on morphisms, (a, a') ↦ a ⊗ a' with ⊗ the tensor product of correspondences"]
theorem tensorHom_val_eq_homOf {M N M' N' : ChowMotiveCat k} (f : M ⟶ N) (f' : M' ⟶ N')
    {r r' : ℤ} (a : SmoothProjectiveCorr M.scheme N.scheme r)
    (a' : SmoothProjectiveCorr M'.scheme N'.scheme r') (ha : f.val = homOf r a)
    (ha' : f'.val = homOf r' a') :
    (f ⊗ₘ f').val = homOf (r + r') (CorrespondenceCategory.tensorCorr r r' a a') := by
  rw [← homOf_tensorHom_homOf, ← ha, ← ha']
  rfl

/-- **Stacks Project, Tag 0FGC.** The unit of `M_k` is `𝟏 = 𝟏(0) = (Spec(k), 1, 0)`. -/
@[stacks 0FGC "the unit of M_k is 1 = (Spec k, 1, 0)"]
theorem tensorUnit_eq_tate : 𝟙_ (ChowMotiveCat k) = tate k 0 :=
  rfl

/-- **Stacks Project, Tag 0FGC.** The associativity constraint of `M_k` is the obvious one: the
graph of the associativity isomorphism `(X × Y) × Z ≅ X × (Y × Z)`, cut down by the
projectors. -/
@[stacks 0FGC "the associativity constraint of M_k is the obvious one"]
theorem associator_hom_val (M N P : ChowMotiveCat k) :
    (α_ M N P).hom.val =
      ((M ⊗ N) ⊗ P).p ≫ graphHom (α_ M.scheme N.scheme P.scheme).inv :=
  rfl

/-- **Stacks Project, Tag 0FGC.** The commutativity constraint of `M_k` is the obvious one: the
graph of the factor switch `X × Y ≅ Y × X`, cut down by the projectors. -/
@[stacks 0FGC "the commutativity constraint of M_k is the obvious one"]
theorem braiding_hom_val (M N : ChowMotiveCat k) :
    (β_ M N).hom.val = (M ⊗ N).p ≫ graphHom (β_ M.scheme N.scheme).inv :=
  rfl

/-! ### Tate twists -/

/-- `𝟏(n) ⊗ 𝟏(m) ≅ 𝟏(n + m)`. -/
def tateTensorIso (n m : ℤ) : tate k n ⊗ tate k m ≅ tate k (n + m) :=
  TwistedKaroubi.unitTwistTensorIso n m

/-- `M(n) = M ⊗ 𝟏(n)` is `(X, p, m + n)` for `M = (X, p, m)`. -/
def twistIso (M : ChowMotiveCat k) (n : ℤ) : M ⊗ tate k n ≅ { M with twist := M.twist + n } :=
  TwistedKaroubi.tensorUnitTwistIso M n

/-- `(X, 1, m) ≅ h(X) ⊗ 𝟏(m)`. -/
def hTensorTateIso (X : (SmoothProjectiveScheme k).FullSubcategory) (m : ℤ) :
    ({ (h k).obj (op X) with twist := m } : ChowMotiveCat k) ≅ (h k).obj (op X) ⊗ tate k m :=
  (TwistedKaroubi.twistCongrIso ((h k).obj (op X)) (zero_add m).symm).trans
    (twistIso ((h k).obj (op X)) m).symm

/-- `𝟏(n)` is invertible, with inverse `𝟏(n')` for `n + n' = 0`. -/
def tateHasInverse (n n' : ℤ) (h : n + n' = 0) : HasInverse (tate k n) :=
  TwistedKaroubi.unitTwistHasInverse n n' h

/-- `𝟏(n)` is invertible. -/
theorem isInvertible_tate (n : ℤ) : IsInvertible (tate k n) :=
  TwistedKaroubi.isInvertible_unitTwist n

/-- `𝟏(m)` is a right dual of `𝟏(-m)`. -/
instance tateExactPairing (m : ℤ) : ExactPairing (tate k (-m)) (tate k m) :=
  TwistedKaroubi.unitTwistExactPairing (-m) m (neg_add_cancel m)

/-- `𝟏(-m)` is a right dual of `𝟏(m)`. -/
instance tateExactPairing' (m : ℤ) : ExactPairing (tate k m) (tate k (-m)) :=
  TwistedKaroubi.unitTwistExactPairing m (-m) (add_neg_cancel m)

end ChowMotiveCat

end Stacks.WeilCohomology

end
