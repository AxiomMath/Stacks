module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectCatPullbackLocComp
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectFullAffine

/-!
# The comparison functor of Tag 0EXD over an open of the base

Let `p` be a prime and let

```
E ⟶ X'
↓    ↓
Z ⟶ X
```

be a commutative square of schemes in characteristic `p`, with `q : E ⟶ X'`, `e : E ⟶ Z`,
`b : X' ⟶ X` and `z : Z ⟶ X`.  Over an open `U` of `X` there is the **restricted square**

```
e⁻¹ z⁻¹ U ⟶ b⁻¹ U
    ↓          ↓
  z⁻¹ U   ⟶   U
```

whose arrows are the restrictions of the four arrows of the square, and the comparison functor
`𝒮_U ⟶ 𝒮_{z⁻¹U} ×_{𝒮_{e⁻¹z⁻¹U}} 𝒮_{b⁻¹U}` of [Stacks, Tag 0EXD] attached to it.  This file sets
up that restricted square, the restriction functor from the categorical fibre product over `X` to
the one over `U`, its compatibility with the comparison functor, and the same for a nested pair of
opens `U' ≤ U`.  Nothing here is about a particular square: the Zariski glueing in the essential
surjectivity half of [Stacks, Tag 0EXD] runs over opens of `X`, where restriction to a smaller
open composes on the nose with no generators to match.

## Main definitions

* `AlgebraicGeometry.squareRestrictQ`: the restriction of `q` to `e⁻¹ z⁻¹ U ⟶ b⁻¹ U`.
* `AlgebraicGeometry.frobeniusColimitComparisonRestrict`: the comparison functor of the
  restricted square.
* `AlgebraicGeometry.frobeniusColimitLocRestrict` and
  `AlgebraicGeometry.frobeniusColimitLocRestrictIso`: restriction from `X` to `U` on the
  categorical fibre products, and the comparison functor commutes with it.
* `AlgebraicGeometry.frobeniusColimitLocNested` and
  `AlgebraicGeometry.frobeniusColimitLocNestedIso`: the same for `U' ≤ U`.
* `AlgebraicGeometry.frobeniusColimitLocRestrictComp`: restricting to `U` and then to `U'` is
  restricting to `U'`.

## References

* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Frobenius

universe u

namespace AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime] {X X' Z E : Scheme.{u}}
  (b : X' ⟶ X) (z : Z ⟶ X) (q : E ⟶ X') (e : E ⟶ Z)
  (hX : IsInCharacteristic X p) (hX' : IsInCharacteristic X' p)
  (hZ : IsInCharacteristic Z p) (hE : IsInCharacteristic E p) (hw : q ≫ b = e ≫ z)

/-- **The restriction of `q : E ⟶ X'` over an open `U` of the base**, from the preimage of `U`
through the centre to its preimage in the modification. -/
def squareRestrictQ (U : X.Opens) : (e ⁻¹ᵁ z ⁻¹ᵁ U).toScheme ⟶ (b ⁻¹ᵁ U).toScheme :=
  q.resLE (b ⁻¹ᵁ U) (e ⁻¹ᵁ z ⁻¹ᵁ U)
    (by rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hw])

/-- The restriction of `q` followed by the inclusion of `b⁻¹ U` is the inclusion of `e⁻¹ z⁻¹ U`
followed by `q`. -/
@[reassoc (attr := simp)]
theorem squareRestrictQ_ι (U : X.Opens) :
    squareRestrictQ b z q e hw U ≫ (b ⁻¹ᵁ U).ι = (e ⁻¹ᵁ z ⁻¹ᵁ U).ι ≫ q :=
  Scheme.Hom.resLE_comp_ι _ _

/-- **The restricted square commutes.** -/
theorem squareRestrict_w (U : X.Opens) :
    squareRestrictQ b z q e hw U ≫ b ∣_ U = e ∣_ (z ⁻¹ᵁ U) ≫ z ∣_ U := by
  rw [← cancel_mono U.ι]
  simp only [Category.assoc, morphismRestrict_ι, squareRestrictQ_ι_assoc, hw,
    morphismRestrict_ι_assoc]

/-- **The comparison functor of [Stacks, Tag 0EXD] for the square restricted over `U`.** -/
noncomputable def frobeniusColimitComparisonRestrict (U : X.Opens) :
    frobeniusColimitVectorBundles U.toScheme p (isInCharacteristic_toScheme hX U) ⥤
      CategoricalPullback
        (frobeniusColimitVectorBundlesPullback p (e ∣_ (z ⁻¹ᵁ U))
          (isInCharacteristic_toScheme hE _) (isInCharacteristic_toScheme hZ _))
        (frobeniusColimitVectorBundlesPullback p (squareRestrictQ b z q e hw U)
          (isInCharacteristic_toScheme hE _) (isInCharacteristic_toScheme hX' _)) :=
  frobeniusColimitVectorBundlesComparison p (b ∣_ U) (z ∣_ U) (squareRestrictQ b z q e hw U)
    (e ∣_ (z ⁻¹ᵁ U)) (isInCharacteristic_toScheme hX U) (isInCharacteristic_toScheme hX' _)
    (isInCharacteristic_toScheme hZ _) (isInCharacteristic_toScheme hE _)
    (squareRestrict_w b z q e hw U)

/-- **Restriction of the categorical fibre product over `X` to the one over an open `U`.** -/
noncomputable def frobeniusColimitLocRestrict (U : X.Opens) :
    CategoricalPullback (frobeniusColimitVectorBundlesPullback p e hE hZ)
        (frobeniusColimitVectorBundlesPullback p q hE hX') ⥤
      CategoricalPullback
        (frobeniusColimitVectorBundlesPullback p (e ∣_ (z ⁻¹ᵁ U))
          (isInCharacteristic_toScheme hE _) (isInCharacteristic_toScheme hZ _))
        (frobeniusColimitVectorBundlesPullback p (squareRestrictQ b z q e hw U)
          (isInCharacteristic_toScheme hE _) (isInCharacteristic_toScheme hX' _)) :=
  frobeniusColimitVectorBundlesCatPullbackLoc p q e (squareRestrictQ b z q e hw U)
    (e ∣_ (z ⁻¹ᵁ U)) (b ⁻¹ᵁ U).ι (z ⁻¹ᵁ U).ι (e ⁻¹ᵁ z ⁻¹ᵁ U).ι hX' hZ hE
    (isInCharacteristic_toScheme hX' _) (isInCharacteristic_toScheme hZ _)
    (isInCharacteristic_toScheme hE _) (squareRestrictQ_ι b z q e hw U)
    (morphismRestrict_ι e (z ⁻¹ᵁ U))

/-- **The comparison functor commutes with restriction to an open `U` of the base.** -/
noncomputable def frobeniusColimitLocRestrictIso (U : X.Opens)
    (M : frobeniusColimitVectorBundles X p hX) :
    (frobeniusColimitLocRestrict p b z q e hX' hZ hE hw U).obj
        ((frobeniusColimitVectorBundlesComparison p b z q e hX hX' hZ hE hw).obj M) ≅
      (frobeniusColimitComparisonRestrict p b z q e hX hX' hZ hE hw U).obj
        ((frobeniusColimitVectorBundlesPullback p U.ι (isInCharacteristic_toScheme hX U) hX).obj
          M) :=
  frobeniusColimitVectorBundlesCatPullbackLocIso p b z q e (b ∣_ U) (z ∣_ U)
    (squareRestrictQ b z q e hw U) (e ∣_ (z ⁻¹ᵁ U)) U.ι (b ⁻¹ᵁ U).ι (z ⁻¹ᵁ U).ι
    (e ⁻¹ᵁ z ⁻¹ᵁ U).ι hX hX' hZ hE (isInCharacteristic_toScheme hX U)
    (isInCharacteristic_toScheme hX' _) (isInCharacteristic_toScheme hZ _)
    (isInCharacteristic_toScheme hE _) (squareRestrictQ_ι b z q e hw U)
    (morphismRestrict_ι e (z ⁻¹ᵁ U)) hw (squareRestrict_w b z q e hw U)
    (morphismRestrict_ι b U) (morphismRestrict_ι z U) M

/-! ### A nested pair of opens -/

section Nested

variable {U U' : X.Opens} (h : U' ≤ U)

/-- The restriction of `q` over `U'` followed by the inclusion of preimages is the inclusion
followed by the restriction of `q` over `U`. -/
@[reassoc]
theorem squareRestrictQ_homOfLE :
    squareRestrictQ b z q e hw U' ≫ X'.homOfLE (b.preimage_mono h) =
      E.homOfLE (e.preimage_mono (z.preimage_mono h)) ≫ squareRestrictQ b z q e hw U := by
  rw [← cancel_mono (b ⁻¹ᵁ U).ι]
  simp

/-- **Restriction from the categorical fibre product over `U` to the one over `U' ≤ U`.** -/
noncomputable def frobeniusColimitLocNested :
    CategoricalPullback
        (frobeniusColimitVectorBundlesPullback p (e ∣_ (z ⁻¹ᵁ U))
          (isInCharacteristic_toScheme hE _) (isInCharacteristic_toScheme hZ _))
        (frobeniusColimitVectorBundlesPullback p (squareRestrictQ b z q e hw U)
          (isInCharacteristic_toScheme hE _) (isInCharacteristic_toScheme hX' _)) ⥤
      CategoricalPullback
        (frobeniusColimitVectorBundlesPullback p (e ∣_ (z ⁻¹ᵁ U'))
          (isInCharacteristic_toScheme hE _) (isInCharacteristic_toScheme hZ _))
        (frobeniusColimitVectorBundlesPullback p (squareRestrictQ b z q e hw U')
          (isInCharacteristic_toScheme hE _) (isInCharacteristic_toScheme hX' _)) :=
  frobeniusColimitVectorBundlesCatPullbackLoc p (squareRestrictQ b z q e hw U)
    (e ∣_ (z ⁻¹ᵁ U)) (squareRestrictQ b z q e hw U') (e ∣_ (z ⁻¹ᵁ U'))
    (X'.homOfLE (b.preimage_mono h)) (Z.homOfLE (z.preimage_mono h))
    (E.homOfLE (e.preimage_mono (z.preimage_mono h)))
    (isInCharacteristic_toScheme hX' _) (isInCharacteristic_toScheme hZ _)
    (isInCharacteristic_toScheme hE _) (isInCharacteristic_toScheme hX' _)
    (isInCharacteristic_toScheme hZ _) (isInCharacteristic_toScheme hE _)
    (squareRestrictQ_homOfLE b z q e hw h) (morphismRestrict_homOfLE e _ _ (z.preimage_mono h))

/-- **The comparison functor commutes with restriction from `U` to `U' ≤ U`.** -/
noncomputable def frobeniusColimitLocNestedIso
    (M : frobeniusColimitVectorBundles U.toScheme p (isInCharacteristic_toScheme hX U)) :
    (frobeniusColimitLocNested p b z q e hX' hZ hE hw h).obj
        ((frobeniusColimitComparisonRestrict p b z q e hX hX' hZ hE hw U).obj M) ≅
      (frobeniusColimitComparisonRestrict p b z q e hX hX' hZ hE hw U').obj
        ((frobeniusColimitVectorBundlesPullback p (X.homOfLE h)
          (isInCharacteristic_toScheme hX U') (isInCharacteristic_toScheme hX U)).obj M) :=
  frobeniusColimitVectorBundlesCatPullbackLocIso p (b ∣_ U) (z ∣_ U)
    (squareRestrictQ b z q e hw U) (e ∣_ (z ⁻¹ᵁ U)) (b ∣_ U') (z ∣_ U')
    (squareRestrictQ b z q e hw U') (e ∣_ (z ⁻¹ᵁ U')) (X.homOfLE h)
    (X'.homOfLE (b.preimage_mono h)) (Z.homOfLE (z.preimage_mono h))
    (E.homOfLE (e.preimage_mono (z.preimage_mono h)))
    (isInCharacteristic_toScheme hX U) (isInCharacteristic_toScheme hX' _)
    (isInCharacteristic_toScheme hZ _) (isInCharacteristic_toScheme hE _)
    (isInCharacteristic_toScheme hX U') (isInCharacteristic_toScheme hX' _)
    (isInCharacteristic_toScheme hZ _) (isInCharacteristic_toScheme hE _)
    (squareRestrictQ_homOfLE b z q e hw h) (morphismRestrict_homOfLE e _ _ (z.preimage_mono h))
    (squareRestrict_w b z q e hw U) (squareRestrict_w b z q e hw U')
    (morphismRestrict_homOfLE b _ _ h) (morphismRestrict_homOfLE z _ _ h) M

/-- **Restricting from `X` to `U` and then to `U' ≤ U` is restricting from `X` to `U'`.** -/
noncomputable def frobeniusColimitLocRestrictComp :
    frobeniusColimitLocRestrict p b z q e hX' hZ hE hw U ⋙
        frobeniusColimitLocNested p b z q e hX' hZ hE hw h ≅
      frobeniusColimitLocRestrict p b z q e hX' hZ hE hw U' :=
  frobeniusColimitVectorBundlesCatPullbackLocComp p q e (squareRestrictQ b z q e hw U)
    (e ∣_ (z ⁻¹ᵁ U)) (squareRestrictQ b z q e hw U') (e ∣_ (z ⁻¹ᵁ U'))
    (b ⁻¹ᵁ U).ι (z ⁻¹ᵁ U).ι (e ⁻¹ᵁ z ⁻¹ᵁ U).ι
    (X'.homOfLE (b.preimage_mono h)) (Z.homOfLE (z.preimage_mono h))
    (E.homOfLE (e.preimage_mono (z.preimage_mono h)))
    (b ⁻¹ᵁ U').ι (z ⁻¹ᵁ U').ι (e ⁻¹ᵁ z ⁻¹ᵁ U').ι hX' hZ hE
    (isInCharacteristic_toScheme hX' _) (isInCharacteristic_toScheme hZ _)
    (isInCharacteristic_toScheme hE _) (isInCharacteristic_toScheme hX' _)
    (isInCharacteristic_toScheme hZ _) (isInCharacteristic_toScheme hE _)
    (squareRestrictQ_ι b z q e hw U) (morphismRestrict_ι e (z ⁻¹ᵁ U))
    (squareRestrictQ_homOfLE b z q e hw h) (morphismRestrict_homOfLE e _ _ (z.preimage_mono h))
    (squareRestrictQ_ι b z q e hw U') (morphismRestrict_ι e (z ⁻¹ᵁ U'))
    (Scheme.homOfLE_ι _ _) (Scheme.homOfLE_ι _ _) (Scheme.homOfLE_ι _ _)

variable {U'' : X.Opens} (h' : U'' ≤ U')

/-- **Restricting from `U` to `U'` and then to `U'' ≤ U'` is restricting from `U` to `U''`.** -/
noncomputable def frobeniusColimitLocNestedComp :
    frobeniusColimitLocNested p b z q e hX' hZ hE hw h ⋙
        frobeniusColimitLocNested p b z q e hX' hZ hE hw h' ≅
      frobeniusColimitLocNested p b z q e hX' hZ hE hw (h'.trans h) :=
  frobeniusColimitVectorBundlesCatPullbackLocComp p (squareRestrictQ b z q e hw U)
    (e ∣_ (z ⁻¹ᵁ U)) (squareRestrictQ b z q e hw U') (e ∣_ (z ⁻¹ᵁ U'))
    (squareRestrictQ b z q e hw U'') (e ∣_ (z ⁻¹ᵁ U''))
    (X'.homOfLE (b.preimage_mono h)) (Z.homOfLE (z.preimage_mono h))
    (E.homOfLE (e.preimage_mono (z.preimage_mono h)))
    (X'.homOfLE (b.preimage_mono h')) (Z.homOfLE (z.preimage_mono h'))
    (E.homOfLE (e.preimage_mono (z.preimage_mono h')))
    (X'.homOfLE (b.preimage_mono (h'.trans h))) (Z.homOfLE (z.preimage_mono (h'.trans h)))
    (E.homOfLE (e.preimage_mono (z.preimage_mono (h'.trans h))))
    (isInCharacteristic_toScheme hX' _) (isInCharacteristic_toScheme hZ _)
    (isInCharacteristic_toScheme hE _) (isInCharacteristic_toScheme hX' _)
    (isInCharacteristic_toScheme hZ _) (isInCharacteristic_toScheme hE _)
    (isInCharacteristic_toScheme hX' _) (isInCharacteristic_toScheme hZ _)
    (isInCharacteristic_toScheme hE _)
    (squareRestrictQ_homOfLE b z q e hw h) (morphismRestrict_homOfLE e _ _ (z.preimage_mono h))
    (squareRestrictQ_homOfLE b z q e hw h') (morphismRestrict_homOfLE e _ _ (z.preimage_mono h'))
    (squareRestrictQ_homOfLE b z q e hw (h'.trans h))
    (morphismRestrict_homOfLE e _ _ (z.preimage_mono (h'.trans h)))
    (Scheme.homOfLE_homOfLE _ _ _) (Scheme.homOfLE_homOfLE _ _ _) (Scheme.homOfLE_homOfLE _ _ _)

/-- **The restriction comparisons satisfy the pentagon**: restricting from `X` to `U`, then to
`U'`, then to `U''`, the two ways of identifying the result with the restriction to `U''`
agree. -/
theorem frobeniusColimitLocRestrictComp_pentagon
    (S : CategoricalPullback (frobeniusColimitVectorBundlesPullback p e hE hZ)
      (frobeniusColimitVectorBundlesPullback p q hE hX')) :
    (frobeniusColimitLocNested p b z q e hX' hZ hE hw h').map
        ((frobeniusColimitLocRestrictComp p b z q e hX' hZ hE hw h).hom.app S) ≫
      (frobeniusColimitLocRestrictComp p b z q e hX' hZ hE hw h').hom.app S =
    (frobeniusColimitLocNestedComp p b z q e hX' hZ hE hw h h').hom.app
        ((frobeniusColimitLocRestrict p b z q e hX' hZ hE hw U).obj S) ≫
      (frobeniusColimitLocRestrictComp p b z q e hX' hZ hE hw (h'.trans h)).hom.app S :=
  by apply frobeniusColimitVectorBundlesCatPullbackLocComp_pentagon

/-- **The restriction comparison of `U ⊇ U'` is compatible with the comparison functor.** -/
theorem frobeniusColimitLocRestrictComp_locIso (M : frobeniusColimitVectorBundles X p hX) :
    (frobeniusColimitLocRestrictComp p b z q e hX' hZ hE hw h).hom.app
        ((frobeniusColimitVectorBundlesComparison p b z q e hX hX' hZ hE hw).obj M) ≫
      (frobeniusColimitLocRestrictIso p b z q e hX hX' hZ hE hw U' M).hom =
    (frobeniusColimitLocNested p b z q e hX' hZ hE hw h).map
        (frobeniusColimitLocRestrictIso p b z q e hX hX' hZ hE hw U M).hom ≫
      (frobeniusColimitLocNestedIso p b z q e hX hX' hZ hE hw h
        ((frobeniusColimitVectorBundlesPullback p U.ι (isInCharacteristic_toScheme hX U)
          hX).obj M)).hom ≫
      (frobeniusColimitComparisonRestrict p b z q e hX hX' hZ hE hw U').map
        ((frobeniusColimitVectorBundlesPullbackTriangleIso p (X.homOfLE h) U.ι U'.ι
          (isInCharacteristic_toScheme hX U') (isInCharacteristic_toScheme hX U) hX
          (Scheme.homOfLE_ι X h)).hom.app M) := by
  apply frobeniusColimitVectorBundlesCatPullbackLocComp_locIso

/-- **The nested comparison of the comparison functor is natural.** -/
theorem frobeniusColimitLocNestedIso_naturality
    {M N : frobeniusColimitVectorBundles U.toScheme p (isInCharacteristic_toScheme hX U)}
    (f : M ⟶ N) :
    (frobeniusColimitLocNested p b z q e hX' hZ hE hw h).map
        ((frobeniusColimitComparisonRestrict p b z q e hX hX' hZ hE hw U).map f) ≫
      (frobeniusColimitLocNestedIso p b z q e hX hX' hZ hE hw h N).hom =
    (frobeniusColimitLocNestedIso p b z q e hX hX' hZ hE hw h M).hom ≫
      (frobeniusColimitComparisonRestrict p b z q e hX hX' hZ hE hw U').map
        ((frobeniusColimitVectorBundlesPullback p (X.homOfLE h)
          (isInCharacteristic_toScheme hX U') (isInCharacteristic_toScheme hX U)).map f) := by
  apply frobeniusColimitVectorBundlesCatPullbackLocIso_naturality

/-- **The nested restriction comparison of `U ⊇ U' ⊇ U''` is compatible with the comparison
functor.** -/
theorem frobeniusColimitLocNestedComp_locIso
    (M : frobeniusColimitVectorBundles U.toScheme p (isInCharacteristic_toScheme hX U)) :
    (frobeniusColimitLocNestedComp p b z q e hX' hZ hE hw h h').hom.app
        ((frobeniusColimitComparisonRestrict p b z q e hX hX' hZ hE hw U).obj M) ≫
      (frobeniusColimitLocNestedIso p b z q e hX hX' hZ hE hw (h'.trans h) M).hom =
    (frobeniusColimitLocNested p b z q e hX' hZ hE hw h').map
        (frobeniusColimitLocNestedIso p b z q e hX hX' hZ hE hw h M).hom ≫
      (frobeniusColimitLocNestedIso p b z q e hX hX' hZ hE hw h'
        ((frobeniusColimitVectorBundlesPullback p (X.homOfLE h)
          (isInCharacteristic_toScheme hX U') (isInCharacteristic_toScheme hX U)).obj M)).hom ≫
      (frobeniusColimitComparisonRestrict p b z q e hX hX' hZ hE hw U'').map
        ((frobeniusColimitVectorBundlesPullbackTriangleIso p (X.homOfLE h') (X.homOfLE h)
          (X.homOfLE (h'.trans h)) (isInCharacteristic_toScheme hX U'')
          (isInCharacteristic_toScheme hX U') (isInCharacteristic_toScheme hX U)
          (Scheme.homOfLE_homOfLE X h' h)).hom.app M) := by
  apply frobeniusColimitVectorBundlesCatPullbackLocComp_locIso

/-- **The nested restriction comparisons are natural.** -/
theorem frobeniusColimitLocNestedComp_naturality
    {S S' : CategoricalPullback
        (frobeniusColimitVectorBundlesPullback p (e ∣_ (z ⁻¹ᵁ U))
          (isInCharacteristic_toScheme hE _) (isInCharacteristic_toScheme hZ _))
        (frobeniusColimitVectorBundlesPullback p (squareRestrictQ b z q e hw U)
          (isInCharacteristic_toScheme hE _) (isInCharacteristic_toScheme hX' _))} (f : S ⟶ S') :
    (frobeniusColimitLocNested p b z q e hX' hZ hE hw h').map
        ((frobeniusColimitLocNested p b z q e hX' hZ hE hw h).map f) ≫
      (frobeniusColimitLocNestedComp p b z q e hX' hZ hE hw h h').hom.app S' =
    (frobeniusColimitLocNestedComp p b z q e hX' hZ hE hw h h').hom.app S ≫
      (frobeniusColimitLocNested p b z q e hX' hZ hE hw (h'.trans h)).map f :=
  (frobeniusColimitLocNestedComp p b z q e hX' hZ hE hw h h').hom.naturality f

end Nested

/-- **The comparison of the comparison functor with restriction to `U` is natural.** -/
theorem frobeniusColimitLocRestrictIso_naturality (U : X.Opens)
    {M N : frobeniusColimitVectorBundles X p hX} (f : M ⟶ N) :
    (frobeniusColimitLocRestrict p b z q e hX' hZ hE hw U).map
        ((frobeniusColimitVectorBundlesComparison p b z q e hX hX' hZ hE hw).map f) ≫
      (frobeniusColimitLocRestrictIso p b z q e hX hX' hZ hE hw U N).hom =
    (frobeniusColimitLocRestrictIso p b z q e hX hX' hZ hE hw U M).hom ≫
      (frobeniusColimitComparisonRestrict p b z q e hX hX' hZ hE hw U).map
        ((frobeniusColimitVectorBundlesPullback p U.ι (isInCharacteristic_toScheme hX U)
          hX).map f) := by
  apply frobeniusColimitVectorBundlesCatPullbackLocIso_naturality

end AlgebraicGeometry

end
