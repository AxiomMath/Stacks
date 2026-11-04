module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedImmersionsPushforward.SetSheafEssentialImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProperPushforwardBaseChangeUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PushforwardBaseChangeUnit
public import StacksFrontier.CategoryTheory.Limits.Shapes.Pullback.Categorical.RightAdjoint

/-!
# Sheaves of sets on a square that is an isomorphism off a closed subscheme

Let `f : X' ⟶ X` be a proper morphism of schemes, `i : Z ⟶ X` a closed immersion and
`E = Z ×_X X'`, with projections `j : E ⟶ X'` and `g : E ⟶ Z`:

```
E --j--> X'
|g       |f
v        v
Z --i--> X
```

If `f` is an isomorphism over `X ∖ Z`, then [Stacks, Tag 0GF4] says that the functor
`Sh(X_étale) ⥤ Sh(X'_étale) ×_{Sh(E_étale)} Sh(Z_étale)` sending `F` to
`(f⁻¹ F, i⁻¹ F, c)`, with `c : j⁻¹ f⁻¹ F ≅ g⁻¹ i⁻¹ F` the canonical isomorphism, is an
equivalence of categories. The target is the `2`-fibre product of categories of
[Stacks, Tag 003R], Mathlib's `CategoryTheory.Limits.CategoricalPullback`.

## Main definitions

* `Stacks.EtaleCohomology.smallEtaleInverseImageCommSqIso`: for a commutative square
  `e ≫ g = h ≫ f`, the canonical isomorphism `e⁻¹ g⁻¹ ≅ h⁻¹ f⁻¹` of inverse images of sheaves
  of sets on small étale sites.
* `Stacks.EtaleCohomology.smallEtaleSheafToCategoricalPullback`: the functor of Tag 0GF4.

## Main results

* `Stacks.EtaleCohomology.mateEquiv_smallEtaleInverseImageCommSqIso_inv`: the mate of the
  canonical isomorphism of a commutative square is the base change map
  `Stacks.EtaleCohomology.smallEtaleSetBaseChange`.
* `Stacks.EtaleCohomology.isIso_of_isIso_smallEtaleInverseImage_of_union`: inverse images along
  two morphisms whose images cover the scheme jointly reflect isomorphisms of sheaves of sets.
* `Stacks.EtaleCohomology.isEquivalence_smallEtaleSheafToCategoricalPullback`:
  [Stacks, Tag 0GF4].

## Implementation notes

The source writes down a quasi-inverse, `(F', G, α) ↦ f_* F' ×_{i_* g_* g⁻¹ G} i_* G`, and
checks it on stalks, computing the stalks of `f_* F'` by the proper base change theorem. Here the
same fibre product is the value of a right adjoint of the functor
(`CategoryTheory.Limits.CategoricalPullback.gluingAdjunction`), and the unit and counit are shown
to be invertible after inverse image to `Z` and to `X ∖ Z` (respectively to `E` and to
`f⁻¹(X ∖ Z)`), which jointly reflect isomorphisms. The stalk computations of the source become:

* over `Z`, inverse image of the fibre product to `Z` is `G`: the map `f_* F' ⟶ i_* g_* g⁻¹ G`
  becomes, after `i⁻¹`, the base change map `i⁻¹ f_* F' ⟶ g_* j⁻¹ F'` followed by `g_* α`, which
  is invertible by the proper base change theorem for sheaves of sets, Stacks 0A3U
  (`Stacks.EtaleCohomology.isIso_smallEtaleSetBaseChange_of_isProper`), and `i⁻¹ i_* = 𝟭`
  (Stacks 04CA);
* over `X ∖ Z`, the direct images from `Z` restrict to the singleton sheaf (Stacks 04CA), and
  the counit `f⁻¹ f_* ⟶ 𝟭` restricts to an isomorphism over `f⁻¹(X ∖ Z)` by Stacks 0A3U for the
  open immersion of `X ∖ Z`, `f` being an isomorphism there.

## References

* [Stacks Project, Tag 0GF4](https://stacks.math.columbia.edu/tag/0GF4)
* [Stacks Project, Tag 0A3U](https://stacks.math.columbia.edu/tag/0A3U)
* [Stacks Project, Tag 04CA](https://stacks.math.columbia.edu/tag/04CA)
* [Stacks Project, Tag 003R](https://stacks.math.columbia.edu/tag/003R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Limits.CategoricalPullback
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

namespace Stacks.EtaleCohomology

section CommSq

variable {X Y S T : Scheme.{u}} (e : Y ⟶ T) (h : Y ⟶ X) (g : T ⟶ S) (f : X ⟶ S)
  (w : e ≫ g = h ≫ f)

/-- The canonical isomorphism `e⁻¹ g⁻¹ ≅ h⁻¹ f⁻¹` of inverse images of sheaves of sets on small
étale sites attached to a commutative square `e ≫ g = h ≫ f`: both are the inverse image along
the diagonal of the square. -/
def smallEtaleInverseImageCommSqIso :
    smallEtaleInverseImage.{u, v} g ⋙ smallEtaleInverseImage.{u, v} e ≅
      smallEtaleInverseImage.{u, v} f ⋙ smallEtaleInverseImage.{u, v} h :=
  smallEtaleInverseImageComp.{u, v} e g ≪≫
    eqToIso (congrArg (fun k : Y ⟶ S ↦ smallEtaleInverseImage.{u, v} k) w) ≪≫
    (smallEtaleInverseImageComp.{u, v} h f).symm

/-- Conjugating the identification of the inverse images along two equal morphisms gives the
identification of their direct images. -/
theorem conjugateEquiv_symm_smallEtalePushforward_eqToHom {k k' : Y ⟶ S} (hk : k = k') :
    (conjugateEquiv (smallEtaleInverseImageAdjunction.{u, v} k)
        (smallEtaleInverseImageAdjunction.{u, v} k')).symm
      (eqToHom (congrArg (fun m : Y ⟶ S ↦ (smallEtaleBaseChange m).sheafPushforwardContinuous
        (Type (max (u + 1) v)) (smallEtaleTopology S) (smallEtaleTopology Y)) hk)) =
      eqToHom (congrArg (fun m : Y ⟶ S ↦ smallEtaleInverseImage.{u, v} m) hk.symm) := by
  subst hk
  simp

/-- The inverse of the canonical isomorphism of a commutative square is conjugate to the
identification of the two composite direct images around the square. -/
theorem smallEtaleInverseImageCommSqIso_inv_eq :
    (smallEtaleInverseImageCommSqIso.{u, v} e h g f w).inv =
      (conjugateEquiv ((smallEtaleInverseImageAdjunction.{u, v} g).comp
          (smallEtaleInverseImageAdjunction.{u, v} e))
        ((smallEtaleInverseImageAdjunction.{u, v} f).comp
          (smallEtaleInverseImageAdjunction.{u, v} h))).symm
        ((smallEtalePushforwardCompIso.{u, v} e g).hom ≫
          eqToHom (congrArg (fun m : Y ⟶ S ↦ (smallEtaleBaseChange m).sheafPushforwardContinuous
            (Type (max (u + 1) v)) (smallEtaleTopology S) (smallEtaleTopology Y)) w) ≫
          (smallEtalePushforwardCompIso.{u, v} h f).inv) := by
  rw [← conjugateEquiv_symm_comp _ (smallEtaleInverseImageAdjunction.{u, v} (e ≫ g)),
    ← conjugateEquiv_symm_comp _ (smallEtaleInverseImageAdjunction.{u, v} (h ≫ f)),
    conjugateEquiv_symm_smallEtalePushforward_eqToHom w]
  simp only [smallEtaleInverseImageCommSqIso, smallEtaleInverseImageComp, Iso.trans_inv,
    Iso.symm_inv, eqToIso.inv, Category.assoc]
  rfl

/-- **The mate of the canonical isomorphism of a commutative square is the base change map.**
The mate along the horizontal adjunctions of `smallEtaleInverseImageCommSqIso⁻¹` is the base
change map `g_* ⋙ f⁻¹ ⟶ e⁻¹ ⋙ h_*` of `Stacks.EtaleCohomology.smallEtaleSetBaseChange`, which is
defined as a mate along the vertical adjunctions. -/
theorem mateEquiv_smallEtaleInverseImageCommSqIso_inv :
    (mateEquiv (smallEtaleInverseImageAdjunction.{u, v} g)
        (smallEtaleInverseImageAdjunction.{u, v} h)
        (TwoSquare.mk _ _ _ _ (smallEtaleInverseImageCommSqIso.{u, v} e h g f w).inv)).natTrans =
      smallEtaleSetBaseChange.{u, v} e h g f w := by
  have key : mateEquiv (smallEtaleInverseImageAdjunction.{u, v} e)
      (smallEtaleInverseImageAdjunction.{u, v} f)
      (mateEquiv (smallEtaleInverseImageAdjunction.{u, v} g)
        (smallEtaleInverseImageAdjunction.{u, v} h)
        (TwoSquare.mk _ _ _ _ (smallEtaleInverseImageCommSqIso.{u, v} e h g f w).inv)) =
      TwoSquare.mk _ _ _ _ ((smallEtalePushforwardCompIso.{u, v} e g).hom ≫
        (eqToIso (congrArg (fun k : Y ⟶ S ↦
          (smallEtaleBaseChange k).sheafPushforwardContinuous
            (Type (max (u + 1) v)) (smallEtaleTopology S) (smallEtaleTopology Y)) w)).hom ≫
        (smallEtalePushforwardCompIso.{u, v} h f).inv) :=
    (iterated_mateEquiv_conjugateEquiv _ _ _ _ _).trans
      (by rw [smallEtaleInverseImageCommSqIso_inv_eq, Equiv.apply_symm_apply]; rfl)
  have h' := congrArg (mateEquiv (smallEtaleInverseImageAdjunction.{u, v} e)
    (smallEtaleInverseImageAdjunction.{u, v} f)).symm key
  rw [Equiv.symm_apply_apply] at h'
  rw [smallEtaleSetBaseChange_eq]
  exact h'

/-- **The mate of the canonical isomorphism of a cartesian square along a proper morphism is
invertible**: it is the base change map, invertible by the proper base change theorem for sheaves
of sets, Stacks 0A3U. -/
theorem isIso_mateEquiv_smallEtaleInverseImageCommSqIso_inv_of_isProper [IsProper g]
    (sq : IsPullback e h g f) :
    IsIso (mateEquiv (smallEtaleInverseImageAdjunction.{u, 0} g)
        (smallEtaleInverseImageAdjunction.{u, 0} h)
        (TwoSquare.mk _ _ _ _
          (smallEtaleInverseImageCommSqIso.{u, 0} e h g f sq.w).inv)).natTrans := by
  rw [mateEquiv_smallEtaleInverseImageCommSqIso_inv]
  exact isIso_smallEtaleSetBaseChange_of_isProper g f e h sq

end CommSq

section Reflect

/-- **Inverse images along two morphisms whose images cover the scheme jointly reflect
isomorphisms of sheaves of sets.** The residue geometric points of `Y₁` and `Y₂`, pushed
forward to `X`, cover `X`, and the stalk of an inverse image at such a point is the stalk of the
original sheaf at its image. -/
theorem isIso_of_isIso_smallEtaleInverseImage_of_union {X Y₁ Y₂ : Scheme.{u}} (p₁ : Y₁ ⟶ X)
    (p₂ : Y₂ ⟶ X) (hp : Set.range p₁.base ∪ Set.range p₂.base = Set.univ)
    {F G : Sheaf (smallEtaleTopology X) (Type (max (u + 1) v))} (γ : F ⟶ G)
    (h₁ : IsIso ((smallEtaleInverseImage.{u, v} p₁).map γ))
    (h₂ : IsIso ((smallEtaleInverseImage.{u, v} p₂).map γ)) : IsIso γ := by
  let Ω : Y₁ ⊕ Y₂ → Type u := fun t ↦ match t with
    | .inl y => SeparableClosure (Y₁.residueField y)
    | .inr y => SeparableClosure (Y₂.residueField y)
  let (t : Y₁ ⊕ Y₂) : Field (Ω t) := by cases t <;> dsimp [Ω] <;> infer_instance
  let (t : Y₁ ⊕ Y₂) : IsSepClosed (Ω t) := by cases t <;> dsimp [Ω] <;> infer_instance
  let s : ∀ t, Spec (.of (Ω t)) ⟶ X := fun t ↦ match t with
    | .inl y => residueGeometricPoint Y₁ y ≫ p₁
    | .inr y => residueGeometricPoint Y₂ y ≫ p₂
  refine isIso_of_geometricStalk_family s ?_ γ ?_
  · refine Set.eq_univ_of_forall fun x ↦ ?_
    have hx : x ∈ Set.range p₁.base ∪ Set.range p₂.base := hp ▸ Set.mem_univ x
    simp only [Set.mem_iUnion, Set.mem_range]
    rcases hx with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · exact ⟨.inl y, default, by
        show p₁.base (residueGeometricPoint Y₁ y default) = p₁.base y
        rw [residueGeometricPoint_apply]⟩
    · exact ⟨.inr y, default, by
        show p₂.base (residueGeometricPoint Y₂ y default) = p₂.base y
        rw [residueGeometricPoint_apply]⟩
  · intro t
    cases t with
    | inl y =>
      exact (NatIso.isIso_map_iff
        (smallEtaleInverseImageStalkIso.{v, u} p₁ (residueGeometricPoint Y₁ y)) γ).mp
          (inferInstanceAs (IsIso ((pointSmallEtale (residueGeometricPoint Y₁ y)).sheafFiber.map
            ((smallEtaleInverseImage.{u, v} p₁).map γ))))
    | inr y =>
      exact (NatIso.isIso_map_iff
        (smallEtaleInverseImageStalkIso.{v, u} p₂ (residueGeometricPoint Y₂ y)) γ).mp
          (inferInstanceAs (IsIso ((pointSmallEtale (residueGeometricPoint Y₂ y)).sheafFiber.map
            ((smallEtaleInverseImage.{u, v} p₂).map γ))))

end Reflect

/-- The counit `i⁻¹ i_* ⟶ 𝟭` of a closed immersion `i` is an isomorphism (Stacks 04CA). -/
private theorem isIso_smallEtaleInverseImageAdjunction_counit {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] : IsIso (smallEtaleInverseImageAdjunction.{u, 0} i).counit :=
  inferInstanceAs (IsIso (smallEtalePushforwardCompInverseImageIso.{u, 0} i).hom)

section Gluing

variable {X X' Z E : Scheme.{u}} (f : X' ⟶ X) (i : Z ⟶ X) (j : E ⟶ X') (g : E ⟶ Z)

/-- The square of inverse images of sheaves of sets attached to a commutative square
`j ≫ f = g ≫ i`: the inverse images `f⁻¹` and `i⁻¹` out of `Sh(X_étale)`, with the canonical
isomorphism `j⁻¹ f⁻¹ ≅ g⁻¹ i⁻¹`. -/
abbrev smallEtaleSheafCatCommSqOver (w : j ≫ f = g ≫ i) :
    CatCommSqOver (smallEtaleInverseImage.{u, v} j) (smallEtaleInverseImage.{u, v} g)
      (Sheaf (smallEtaleTopology X) (Type (max (u + 1) v))) :=
  ⟨smallEtaleInverseImage.{u, v} f, smallEtaleInverseImage.{u, v} i,
    smallEtaleInverseImageCommSqIso.{u, v} j g f i w⟩

/-- The functor `Sh(X_étale) ⥤ Sh(X'_étale) ×_{Sh(E_étale)} Sh(Z_étale)` of [Stacks, Tag 0GF4],
sending `F` to `(f⁻¹ F, i⁻¹ F, c)` with `c : j⁻¹ f⁻¹ F ≅ g⁻¹ i⁻¹ F` the canonical isomorphism. -/
abbrev smallEtaleSheafToCategoricalPullback (w : j ≫ f = g ≫ i) :
    Sheaf (smallEtaleTopology X) (Type (max (u + 1) v)) ⥤
      (smallEtaleInverseImage.{u, v} j) ⊡ (smallEtaleInverseImage.{u, v} g) :=
  (CatCommSqOver.toFunctorToCategoricalPullback _ _ _).obj
    (smallEtaleSheafCatCommSqOver.{u, v} f i j g w)

variable [IsProper f] [IsClosedImmersion i] (sq : IsPullback j g f i)

/-- Over `Z`: inverse image to `Z` carries the second projection out of the glued sheaf to an
isomorphism, by the proper base change theorem for `f` along `i`. -/
theorem isIso_smallEtaleInverseImage_map_pullbackSnd_gluingObj
    (x : (smallEtaleInverseImage.{u, 0} j) ⊡ (smallEtaleInverseImage.{u, 0} g)) :
    IsIso ((smallEtaleInverseImage.{u, 0} i).map (pullback.snd
      (gluingFst (smallEtaleSheafCatCommSqOver.{u, 0} f i j g sq.w)
        (smallEtaleInverseImageAdjunction.{u, 0} f) (smallEtaleInverseImageAdjunction.{u, 0} i)
        (smallEtaleInverseImageAdjunction.{u, 0} g) x)
      (gluingSnd _ (smallEtaleInverseImageAdjunction.{u, 0} g) x))) := by
  have := isIso_mateEquiv_smallEtaleInverseImageCommSqIso_inv_of_isProper j g f i sq
  have := isIso_smallEtaleInverseImageAdjunction_counit i
  exact isIso_map_pullbackSnd_gluingObj (smallEtaleSheafCatCommSqOver.{u, 0} f i j g sq.w)
    (smallEtaleInverseImageAdjunction.{u, 0} f) (smallEtaleInverseImageAdjunction.{u, 0} i)
    (smallEtaleInverseImageAdjunction.{u, 0} g) x

variable [IsIso (f ∣_ openComplement i)]

/-- Over `f⁻¹(X ∖ Z)`: the counit `f⁻¹ f_* ⟶ 𝟭` restricts to an isomorphism, by the proper base
change theorem for `f` along the open immersion of `X ∖ Z`, over which `f` is an isomorphism. -/
theorem isIso_smallEtaleInverseImage_map_counit_openComplement
    (d : Sheaf (smallEtaleTopology X') (Type (u + 1))) :
    IsIso ((smallEtaleInverseImage.{u, 0} (f ⁻¹ᵁ openComplement i).ι).map
      ((smallEtaleInverseImageAdjunction.{u, 0} f).counit.app d)) := by
  let fU := f ∣_ openComplement i
  have hsq : IsPullback (f ⁻¹ᵁ openComplement i).ι fU f (openComplement i).ι :=
    (isPullback_morphismRestrict f _).flip
  have := isIso_mateEquiv_smallEtaleInverseImageCommSqIso_inv_of_isProper _ _ _ _ hsq
  have := isIso_smallEtaleInverseImageAdjunction_counit fU
  have : IsIso ((mateEquiv (smallEtaleInverseImageAdjunction.{u, 0} f)
      (smallEtaleInverseImageAdjunction.{u, 0} fU) (TwoSquare.mk _ _ _ _
        (smallEtaleInverseImageCommSqIso.{u, 0} _ _ _ _ hsq.w).inv)).natTrans.app d) :=
    NatIso.isIso_app_of_isIso _ _
  have hc : (smallEtaleInverseImage.{u, 0} fU).map ((mateEquiv
      (smallEtaleInverseImageAdjunction.{u, 0} f) (smallEtaleInverseImageAdjunction.{u, 0} fU)
        (TwoSquare.mk _ _ _ _
          (smallEtaleInverseImageCommSqIso.{u, 0} _ _ _ _ hsq.w).inv)).natTrans.app d) ≫
        (smallEtaleInverseImageAdjunction.{u, 0} fU).counit.app _ =
      (smallEtaleInverseImageCommSqIso.{u, 0} _ _ _ _ hsq.w).inv.app _ ≫
        (smallEtaleInverseImage.{u, 0} (f ⁻¹ᵁ openComplement i).ι).map
          ((smallEtaleInverseImageAdjunction.{u, 0} f).counit.app d) :=
    mateEquiv_counit (smallEtaleInverseImageAdjunction.{u, 0} f)
      (smallEtaleInverseImageAdjunction.{u, 0} fU) (TwoSquare.mk _ _ _ _
        (smallEtaleInverseImageCommSqIso.{u, 0} _ _ _ _ hsq.w).inv) d
  have : IsIso ((smallEtaleInverseImageCommSqIso.{u, 0} _ _ _ _ hsq.w).inv.app _ ≫
      (smallEtaleInverseImage.{u, 0} (f ⁻¹ᵁ openComplement i).ι).map
        ((smallEtaleInverseImageAdjunction.{u, 0} f).counit.app d)) := by
    rw [← hc]
    infer_instance
  exact IsIso.of_isIso_comp_left
    ((smallEtaleInverseImageCommSqIso.{u, 0} _ _ _ _ hsq.w).inv.app _) _

omit [IsProper f] [IsIso (f ∣_ openComplement i)] in
/-- Over `X ∖ Z`: inverse image to `X ∖ Z` carries the first projection out of the glued sheaf
to an isomorphism, the direct images from `Z` restricting to the singleton sheaf there. -/
theorem isIso_smallEtaleInverseImage_map_pullbackFst_gluingObj
    (x : (smallEtaleInverseImage.{u, 0} j) ⊡ (smallEtaleInverseImage.{u, 0} g)) :
    IsIso ((smallEtaleInverseImage.{u, 0} (openComplement i).ι).map (pullback.fst
      (gluingFst (smallEtaleSheafCatCommSqOver.{u, 0} f i j g sq.w)
        (smallEtaleInverseImageAdjunction.{u, 0} f) (smallEtaleInverseImageAdjunction.{u, 0} i)
        (smallEtaleInverseImageAdjunction.{u, 0} g) x)
      (gluingSnd _ (smallEtaleInverseImageAdjunction.{u, 0} g) x))) := by
  have hT : ∀ y : Sheaf (smallEtaleTopology Z) (Type (u + 1)),
      IsTerminal ((smallEtaleInverseImage.{u, 0} (openComplement i).ι).obj
        (((smallEtaleBaseChange i).sheafPushforwardContinuous (Type (u + 1))
          (smallEtaleTopology X) (smallEtaleTopology Z)).obj y)) := fun y ↦
    ((smallEtalePushforward_essImage_iff.{u, 0} i _).1 (Functor.obj_mem_essImage _ y)).some
  have : IsIso ((smallEtaleInverseImage.{u, 0} (openComplement i).ι).map
      (gluingSnd _ (smallEtaleInverseImageAdjunction.{u, 0} g) x)) :=
    isIso_of_isTerminal (hT _) (hT _) _
  have := hasPullback_of_preservesPullback (smallEtaleInverseImage.{u, 0} (openComplement i).ι)
    (gluingFst (smallEtaleSheafCatCommSqOver.{u, 0} f i j g sq.w)
      (smallEtaleInverseImageAdjunction.{u, 0} f) (smallEtaleInverseImageAdjunction.{u, 0} i)
      (smallEtaleInverseImageAdjunction.{u, 0} g) x)
    (gluingSnd _ (smallEtaleInverseImageAdjunction.{u, 0} g) x)
  rw [← PreservesPullback.iso_hom_fst]
  infer_instance

/-- Over `X ∖ Z`: the unit `𝟭 ⟶ f_* f⁻¹` restricts to an isomorphism. After inverse image along
the isomorphism `f⁻¹(X ∖ Z) ⟶ X ∖ Z` it is the restriction to `f⁻¹(X ∖ Z)` of `f⁻¹` of the unit,
a section of the restricted counit, which is invertible. -/
theorem isIso_smallEtaleInverseImage_map_unit_openComplement
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    IsIso ((smallEtaleInverseImage.{u, 0} (openComplement i).ι).map
      ((smallEtaleInverseImageAdjunction.{u, 0} f).unit.app F)) := by
  let fU := f ∣_ openComplement i
  have hsq : IsPullback (f ⁻¹ᵁ openComplement i).ι fU f (openComplement i).ι :=
    (isPullback_morphismRestrict f _).flip
  have hrange : Set.range fU.base ∪ Set.range fU.base = Set.univ :=
    (Set.union_self _).trans (Set.range_eq_univ.2 fU.surjective)
  suffices h : IsIso ((smallEtaleInverseImage.{u, 0} fU).map
      ((smallEtaleInverseImage.{u, 0} (openComplement i).ι).map
        ((smallEtaleInverseImageAdjunction.{u, 0} f).unit.app F))) from
    isIso_of_isIso_smallEtaleInverseImage_of_union.{u, 0} fU fU hrange _ h h
  have := isIso_smallEtaleInverseImage_map_counit_openComplement f i
    ((smallEtaleInverseImage.{u, 0} f).obj F)
  have htri : (smallEtaleInverseImage.{u, 0} (f ⁻¹ᵁ openComplement i).ι).map
        ((smallEtaleInverseImage.{u, 0} f).map
          ((smallEtaleInverseImageAdjunction.{u, 0} f).unit.app F)) ≫
      (smallEtaleInverseImage.{u, 0} (f ⁻¹ᵁ openComplement i).ι).map
        ((smallEtaleInverseImageAdjunction.{u, 0} f).counit.app
          ((smallEtaleInverseImage.{u, 0} f).obj F)) = 𝟙 _ := by
    rw [← Functor.map_comp]
    exact (congrArg (smallEtaleInverseImage.{u, 0} (f ⁻¹ᵁ openComplement i).ι).map
      ((smallEtaleInverseImageAdjunction.{u, 0} f).left_triangle_components F)).trans
        (CategoryTheory.Functor.map_id _ _)
  have : IsIso ((smallEtaleInverseImage.{u, 0} (f ⁻¹ᵁ openComplement i).ι).map
      ((smallEtaleInverseImage.{u, 0} f).map
        ((smallEtaleInverseImageAdjunction.{u, 0} f).unit.app F))) := by
    rw [IsIso.eq_inv_of_inv_hom_id htri]
    infer_instance
  exact (NatIso.isIso_map_iff (smallEtaleInverseImageCommSqIso.{u, 0} _ _ _ _ hsq.w) _).1 this

omit [IsProper f] [IsIso (f ∣_ openComplement i)] in
include sq in
/-- The images of `j : E ⟶ X'` and of the open immersion of `f⁻¹(X ∖ Z)` cover `X'`. -/
theorem range_union_range_preimage_openComplement :
    Set.range j.base ∪ Set.range (f ⁻¹ᵁ openComplement i).ι.base = Set.univ := by
  refine Set.eq_univ_of_forall fun x' ↦ ?_
  by_cases hx : f.base x' ∈ Set.range i.base
  · left
    have hx' : x' ∈ Set.range (pullback.fst f i) := by rwa [Scheme.Pullback.range_fst]
    obtain ⟨e, he⟩ := hx'
    refine ⟨sq.isoPullback.inv.base e, ?_⟩
    have h1 : sq.isoPullback.inv ≫ j = pullback.fst f i :=
      (Iso.inv_comp_eq _).2 sq.isoPullback_hom_fst.symm
    rwa [← Scheme.Hom.comp_apply, h1]
  · right
    exact ⟨⟨x', hx⟩, rfl⟩

omit [IsIso (f ∣_ openComplement i)] in
/-- The images of `i : Z ⟶ X` and of the open immersion of `X ∖ Z` cover `X`. -/
theorem range_union_range_openComplement :
    Set.range i.base ∪ Set.range (openComplement i).ι.base = Set.univ := by
  refine Set.eq_univ_of_forall fun x ↦ ?_
  by_cases hx : x ∈ Set.range i.base
  · exact Or.inl hx
  · exact Or.inr ⟨⟨x, hx⟩, rfl⟩

/-- The first component of the counit of the gluing adjunction, `f⁻¹` of the first projection
out of the glued sheaf followed by the counit of `f⁻¹ ⊣ f_*`, is an isomorphism: it is one over
`E` by the gluing condition, and over `f⁻¹(X ∖ Z)` because `f` is an isomorphism there. -/
theorem isIso_smallEtaleSheafGluing_counit_fst
    (x : (smallEtaleInverseImage.{u, 0} j) ⊡ (smallEtaleInverseImage.{u, 0} g)) :
    IsIso ((smallEtaleInverseImage.{u, 0} f).map (pullback.fst
      (gluingFst (smallEtaleSheafCatCommSqOver.{u, 0} f i j g sq.w)
        (smallEtaleInverseImageAdjunction.{u, 0} f) (smallEtaleInverseImageAdjunction.{u, 0} i)
        (smallEtaleInverseImageAdjunction.{u, 0} g) x)
      (gluingSnd _ (smallEtaleInverseImageAdjunction.{u, 0} g) x)) ≫
        (smallEtaleInverseImageAdjunction.{u, 0} f).counit.app x.fst) := by
  have := isIso_smallEtaleInverseImageAdjunction_counit i
  have hsq : IsPullback (f ⁻¹ᵁ openComplement i).ι (f ∣_ openComplement i) f
      (openComplement i).ι := (isPullback_morphismRestrict f _).flip
  refine isIso_of_isIso_smallEtaleInverseImage_of_union.{u, 0} j (f ⁻¹ᵁ openComplement i).ι
    (range_union_range_preimage_openComplement f i j g sq) _ ?_ ?_
  · have hA := isIso_smallEtaleInverseImage_map_pullbackSnd_gluingObj f i j g sq x
    have hw := gluing_counit_w (smallEtaleSheafCatCommSqOver.{u, 0} f i j g sq.w)
      (smallEtaleInverseImageAdjunction.{u, 0} f) (smallEtaleInverseImageAdjunction.{u, 0} i)
      (smallEtaleInverseImageAdjunction.{u, 0} g) x
    have h2 := IsIso.comp_isIso' hA
      (NatIso.isIso_app_of_isIso (smallEtaleInverseImageAdjunction.{u, 0} i).counit x.snd)
    rw [← Iso.eq_comp_inv] at hw
    rw [hw]
    infer_instance
  · have hB := isIso_smallEtaleInverseImage_map_pullbackFst_gluingObj f i j g sq x
    rw [Functor.map_comp]
    refine IsIso.comp_isIso' ?_ (isIso_smallEtaleInverseImage_map_counit_openComplement f i x.fst)
    refine (NatIso.isIso_map_iff (smallEtaleInverseImageCommSqIso.{u, 0} _ _ _ _ hsq.w) _).2 ?_
    exact Functor.map_isIso (smallEtaleInverseImage.{u, 0} (f ∣_ openComplement i)) _

/-- The unit of the gluing adjunction is an isomorphism: over `Z` it is a section of the
isomorphism given by the second projection, and over `X ∖ Z` its first component is the unit of
`f⁻¹ ⊣ f_*`, which is invertible there. -/
theorem isIso_smallEtaleSheafGluingUnit (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    IsIso (gluingUnit (smallEtaleSheafCatCommSqOver.{u, 0} f i j g sq.w)
      (smallEtaleInverseImageAdjunction.{u, 0} f) (smallEtaleInverseImageAdjunction.{u, 0} i)
      (smallEtaleInverseImageAdjunction.{u, 0} g) F) := by
  have := isIso_smallEtaleInverseImageAdjunction_counit i
  refine isIso_of_isIso_smallEtaleInverseImage_of_union.{u, 0} i (openComplement i).ι
    (range_union_range_openComplement i) _ ?_ ?_
  · have hA := isIso_smallEtaleInverseImage_map_pullbackSnd_gluingObj f i j g sq
      ((smallEtaleSheafToCategoricalPullback.{u, 0} f i j g sq.w).obj F)
    have hφ := IsIso.comp_isIso' hA
      (NatIso.isIso_app_of_isIso (smallEtaleInverseImageAdjunction.{u, 0} i).counit
        ((smallEtaleSheafToCategoricalPullback.{u, 0} f i j g sq.w).obj F).snd)
    have htri : (smallEtaleInverseImage.{u, 0} i).map
        (gluingUnit (smallEtaleSheafCatCommSqOver.{u, 0} f i j g sq.w)
          (smallEtaleInverseImageAdjunction.{u, 0} f) (smallEtaleInverseImageAdjunction.{u, 0} i)
          (smallEtaleInverseImageAdjunction.{u, 0} g) F) ≫
        ((smallEtaleInverseImage.{u, 0} i).map (pullback.snd _ _) ≫
          (smallEtaleInverseImageAdjunction.{u, 0} i).counit.app
            ((smallEtaleSheafToCategoricalPullback.{u, 0} f i j g sq.w).obj F).snd) = 𝟙 _ := by
      rw [← Category.assoc, ← Functor.map_comp, gluingUnit_snd]
      exact (smallEtaleInverseImageAdjunction.{u, 0} i).left_triangle_components F
    exact ⟨⟨_, htri, by
      rw [@IsIso.eq_inv_of_inv_hom_id _ _ _ _ _ hφ _ htri]
      exact @IsIso.hom_inv_id _ _ _ _ _ hφ⟩⟩
  · have hB := isIso_smallEtaleInverseImage_map_pullbackFst_gluingObj f i j g sq
      ((smallEtaleSheafToCategoricalPullback.{u, 0} f i j g sq.w).obj F)
    have hD := isIso_smallEtaleInverseImage_map_unit_openComplement f i F
    have hfac : (smallEtaleInverseImage.{u, 0} (openComplement i).ι).map
        (gluingUnit (smallEtaleSheafCatCommSqOver.{u, 0} f i j g sq.w)
          (smallEtaleInverseImageAdjunction.{u, 0} f) (smallEtaleInverseImageAdjunction.{u, 0} i)
          (smallEtaleInverseImageAdjunction.{u, 0} g) F) ≫
          (smallEtaleInverseImage.{u, 0} (openComplement i).ι).map (pullback.fst _ _) =
            (smallEtaleInverseImage.{u, 0} (openComplement i).ι).map
              ((smallEtaleInverseImageAdjunction.{u, 0} f).unit.app F) := by
      rw [← Functor.map_comp, gluingUnit_fst]
      rfl
    have : IsIso ((smallEtaleInverseImage.{u, 0} (openComplement i).ι).map
        (gluingUnit (smallEtaleSheafCatCommSqOver.{u, 0} f i j g sq.w)
          (smallEtaleInverseImageAdjunction.{u, 0} f) (smallEtaleInverseImageAdjunction.{u, 0} i)
          (smallEtaleInverseImageAdjunction.{u, 0} g) F) ≫
          (smallEtaleInverseImage.{u, 0} (openComplement i).ι).map (pullback.fst _ _)) := by
      rw [hfac]
      exact hD
    exact IsIso.of_isIso_comp_right _
      ((smallEtaleInverseImage.{u, 0} (openComplement i).ι).map (pullback.fst _ _))

omit [IsIso (f ∣_ openComplement i)] in
/-- **Stacks Project, Tag 0GF4.** Let `f : X' ⟶ X` be a proper morphism of schemes, `i : Z ⟶ X`
a closed immersion and `E = Z ×_X X'` with projections `j : E ⟶ X'` and `g : E ⟶ Z`. If `f` is
an isomorphism over the open complement `U` of `Z`, the functor
`Sh(X_étale) ⥤ Sh(X'_étale) ×_{Sh(E_étale)} Sh(Z_étale)`, `F ↦ (f⁻¹ F, i⁻¹ F, c)` with `c` the
canonical isomorphism `j⁻¹ f⁻¹ F ≅ g⁻¹ i⁻¹ F`, is an equivalence of categories. -/
@[stacks 0GF4]
theorem isEquivalence_smallEtaleSheafToCategoricalPullback (U : X.Opens)
    (hU : (U : Set X) = (Set.range i.base)ᶜ) [IsIso (f ∣_ U)] :
    (smallEtaleSheafToCategoricalPullback.{u, 0} f i j g sq.w).IsEquivalence := by
  obtain rfl : U = openComplement i := TopologicalSpace.Opens.ext hU
  have := isIso_smallEtaleInverseImageAdjunction_counit i
  exact isEquivalence_toFunctorToCategoricalPullback_of_isIso _ _ _ _
    (isIso_smallEtaleSheafGluingUnit f i j g sq) (isIso_smallEtaleSheafGluing_counit_fst f i j g sq)
    (fun x ↦ IsIso.comp_isIso' (isIso_smallEtaleInverseImage_map_pullbackSnd_gluingObj f i j g sq x)
      (NatIso.isIso_app_of_isIso _ _))

end Gluing

end Stacks.EtaleCohomology
