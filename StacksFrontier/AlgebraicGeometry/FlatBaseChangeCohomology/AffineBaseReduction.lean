module

public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.Locality

/-!
# The base-change morphism for direct images: reduction to affine bases

Let
```
X' --g'--> X
|f'        |f
S' --g-->  S
```
be a commutative square of schemes and let `ℱ` be a sheaf of modules on `X`.  The canonical
base-change morphism `g^* f_* ℱ ⟶ f'_* (g')^* ℱ` is
`Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans`.  Shrinking the base to an
open `U` of `S` *and* to an open `V` of `S'` contained in `g⁻¹U` turns the square into
```
f' ⁻¹ᵁ V --g' ∣_--> f ⁻¹ᵁ U
|f' ∣_ V            |f ∣_ U
    V    --g ∣_-->     U
```
and this file proves that the base-change morphism of the original square is an isomorphism as
soon as the base-change morphisms of those squares are, for `U` and `V` ranging over the affine
opens of `S` and of `S'`.

## Main results

* `Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.baseChangeNatTrans_pasteBase_app`: the
  base-change morphism of a rectangle obtained by stacking two squares along the base, written
  out as a four-fold composite.
* `Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.restrictBasesSquare`: the square displayed
  above commutes.
* `Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isPullback_restrictBasesSquare`: and it is
  cartesian whenever the original square is.
* `Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_restrictBases`:
  if the base-change morphism of that square is invertible, so is the base-change morphism of
  the rectangle obtained by shrinking only the base `S'` to `V`.
* `Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_isOpenCover_le`:
  the version with an explicit covering of `S'` by opens `V i`, each contained in the preimage
  of an open `U i` of `S`.
* `Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_affineBases`:
  the base-change morphism of the square is invertible at `ℱ` as soon as the base-change
  morphism of the doubly restricted square is invertible for every pair of affine opens `U` of
  `S` and `V` of `S'` with `V ≤ g⁻¹U`.

## References

* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.FlatBaseChangeCohomology

/-! ### The base-change morphism of a pasted rectangle, written out -/

section Paste

variable {X X' X'' S S' S'' : Scheme.{u}}
  {f : X ⟶ S} {f' : X' ⟶ S'} {f'' : X'' ⟶ S''}
  {g : S' ⟶ S} {g' : X' ⟶ X} {h : S'' ⟶ S'} {h' : X'' ⟶ X'}

/-- The base-change morphism of the rectangle obtained by stacking two commutative squares
along the base, as a four-fold composite:  the two outer factors are the canonical
identifications of an inverse image along a composite with the composite of the inverse images,
and the two middle factors are the inverse image along the lower-left morphism of the
right-hand square's base-change morphism, followed by the left-hand square's base-change
morphism at the inverse image of the module. -/
theorem baseChangeNatTrans_pasteBase_app (w₁ : g' ≫ f = f' ≫ g) (w₂ : h' ≫ f' = f'' ≫ h)
    (M : X.Modules) :
    (AffinePushforward.baseChangeNatTrans (pasteBase w₁ w₂)).app M =
      (Scheme.Modules.pullbackComp h g).inv.app ((Scheme.Modules.pushforward f).obj M) ≫
        (Scheme.Modules.pullback h).map ((AffinePushforward.baseChangeNatTrans w₁).app M) ≫
        (AffinePushforward.baseChangeNatTrans w₂).app ((Scheme.Modules.pullback g').obj M) ≫
        (Scheme.Modules.pushforward f'').map
          ((Scheme.Modules.pullbackComp h' g').hom.app M) := by
  have key := congrArg (fun t => NatTrans.app t M)
    (baseChangeSquare_pasteBase w₁ w₂)
  simp only [TwoSquare.whiskerRight_app, TwoSquare.whiskerLeft_app,
    natTrans_baseChangeSquare] at key
  exact key

/-- If the base-change morphism of the right-hand square is invertible at the inverse image of
`M`, and that of the left-hand square is invertible at `M`, then that of the pasted rectangle
is invertible at `M`. -/
theorem isIso_baseChangeNatTrans_pasteBase (w₁ : g' ≫ f = f' ≫ g) (w₂ : h' ≫ f' = f'' ≫ h)
    (M : X.Modules)
    (h₁ : IsIso ((AffinePushforward.baseChangeNatTrans w₁).app M))
    (h₂ : IsIso ((AffinePushforward.baseChangeNatTrans w₂).app
      ((Scheme.Modules.pullback g').obj M))) :
    IsIso ((AffinePushforward.baseChangeNatTrans (pasteBase w₁ w₂)).app M) := by
  rw [baseChangeNatTrans_pasteBase_app w₁ w₂]
  have a1 : IsIso ((Scheme.Modules.pullbackComp h g).inv.app
      ((Scheme.Modules.pushforward f).obj M)) :=
    NatIso.isIso_app_of_isIso (Scheme.Modules.pullbackComp h g).inv _
  have a2 : IsIso ((Scheme.Modules.pullback h).map
      ((AffinePushforward.baseChangeNatTrans w₁).app M)) :=
    Functor.map_isIso _ _
  have a4 : IsIso ((Scheme.Modules.pushforward f'').map
      ((Scheme.Modules.pullbackComp h' g').hom.app M)) :=
    Functor.map_isIso _ _
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ a1
    (@IsIso.comp_isIso _ _ _ _ _ _ _ a2 (@IsIso.comp_isIso _ _ _ _ _ _ _ h₂ a4))

end Paste

/-! ### Restricting both bases -/

section Restrict

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'} {g : S' ⟶ S} {g' : X' ⟶ X}

/-- If two commutative squares have the same vertical morphisms and equal horizontal morphisms,
and the base-change morphism of the first is invertible at `M`, then so is that of the
second. -/
theorem isIso_baseChangeNatTrans_congr {gA : S' ⟶ S} {gA' : X' ⟶ X}
    (hg : gA = g) (hg' : gA' = g') (wA : gA' ≫ f = f' ≫ gA) (w : g' ≫ f = f' ≫ g)
    (M : X.Modules) (hA : IsIso ((AffinePushforward.baseChangeNatTrans wA).app M)) :
    IsIso ((AffinePushforward.baseChangeNatTrans w).app M) := by
  subst hg hg'
  exact hA

/-- For a commutative square and an open `V` of `S'` contained in the preimage of an open `U`
of `S`, the preimage of `V` in `X'` is contained in the preimage of the preimage of `U`. -/
theorem preimage_le_of_comm {U : S.Opens} {V : S'.Opens} (w : g' ≫ f = f' ≫ g)
    (hV : V ≤ g ⁻¹ᵁ U) : f' ⁻¹ᵁ V ≤ g' ⁻¹ᵁ (f ⁻¹ᵁ U) := by
  have h : g' ⁻¹ᵁ (f ⁻¹ᵁ U) = f' ⁻¹ᵁ (g ⁻¹ᵁ U) := by
    rw [show g' ⁻¹ᵁ (f ⁻¹ᵁ U) = (g' ≫ f) ⁻¹ᵁ U from rfl, w]; rfl
  rw [h]
  exact fun x hx => hV hx

/-- Shrinking the base of a commutative square to
an open `U` of `S` and to an open `V` of `S'` contained in `g ⁻¹ᵁ U` gives again a commutative
square, whose horizontal morphisms are the restrictions of `g` and of `g'`. -/
theorem restrictBasesSquare (w : g' ≫ f = f' ≫ g) (U : S.Opens) {V : S'.Opens}
    (hV : V ≤ g ⁻¹ᵁ U) :
    g'.resLE (f ⁻¹ᵁ U) (f' ⁻¹ᵁ V) (preimage_le_of_comm w hV) ≫ (f ∣_ U)
      = (f' ∣_ V) ≫ g.resLE U V hV := by
  rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, Category.assoc,
    Scheme.Hom.resLE_comp_ι, ← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, w,
    ← Category.assoc (f' ∣_ V) V.ι g, morphismRestrict_ι, Category.assoc]

/-- If the square is cartesian, then so is the square obtained by restricting its two bases to an
open `U` of `S` and to an open `V ≤ g ⁻¹ᵁ U` of `S'`. -/
theorem isPullback_restrictBasesSquare (w : IsPullback g' f' f g) (U : S.Opens)
    {V : S'.Opens} (hV : V ≤ g ⁻¹ᵁ U) :
    IsPullback (g'.resLE (f ⁻¹ᵁ U) (f' ⁻¹ᵁ V) (preimage_le_of_comm w.w hV)) (f' ∣_ V)
      (f ∣_ U) (g.resLE U V hV) := by
  have hR : IsPullback ((f' ⁻¹ᵁ V).ι ≫ g') (f' ∣_ V) f (V.ι ≫ g) :=
    (isPullback_morphismRestrict f' V).flip.paste_horiz w
  rw [← Scheme.Hom.resLE_comp_ι g' (preimage_le_of_comm w.w hV),
    ← Scheme.Hom.resLE_comp_ι g hV] at hR
  exact hR.of_right (restrictBasesSquare w.w U hV) (isPullback_morphismRestrict f U).flip

/-- If the base-change morphism of the doubly restricted square is invertible at the inverse
image of `M` along the inclusion of `f ⁻¹ᵁ U`, then the base-change morphism of the rectangle
obtained by shrinking only `S'`, to `V`, is invertible at `M`. -/
theorem isIso_baseChangeNatTrans_restrictBases (w : g' ≫ f = f' ≫ g) (U : S.Opens)
    {V : S'.Opens} (hV : V ≤ g ⁻¹ᵁ U) (M : X.Modules)
    (hUV : IsIso ((AffinePushforward.baseChangeNatTrans (restrictBasesSquare w U hV)).app
      ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj M))) :
    IsIso ((AffinePushforward.baseChangeNatTrans (pasteBase_restrictSquare w V)).app M) :=
  isIso_baseChangeNatTrans_congr (Scheme.Hom.resLE_comp_ι g hV)
    (Scheme.Hom.resLE_comp_ι g' (preimage_le_of_comm w hV))
    (pasteBase (AffineBaseChange.restrictSquare f U) (restrictBasesSquare w U hV)) _ M
    (isIso_baseChangeNatTrans_pasteBase _ _ M
      (AffineBaseChange.isIso_baseChangeNatTrans_restrictSquare f U M) hUV)

/-- Let `V` be an open covering of `S'` and let `U i` be an open
of `S` with `V i ≤ g ⁻¹ᵁ U i`.  If the base-change morphism of the square obtained by
restricting the bases to `U i` and `V i` is invertible for every `i`, then the base-change
morphism of the square itself is invertible. -/
theorem isIso_baseChangeNatTrans_of_isOpenCover_le (w : g' ≫ f = f' ≫ g) (M : X.Modules)
    {I : Type*} (U : I → S.Opens) (V : I → S'.Opens) (hVU : ∀ i, V i ≤ g ⁻¹ᵁ U i)
    (hV : IsOpenCover V)
    (hloc : ∀ i, IsIso ((AffinePushforward.baseChangeNatTrans
      (restrictBasesSquare w (U i) (hVU i))).app
      ((Scheme.Modules.pullback (f ⁻¹ᵁ U i).ι).obj M))) :
    IsIso ((AffinePushforward.baseChangeNatTrans w).app M) :=
  isIso_baseChangeNatTrans_of_isOpenCover w M V hV fun i =>
    isIso_baseChangeNatTrans_restrictBases w (U i) (hVU i) M (hloc i)

/-- Let
```
X' --g'--> X
|f'        |f
S' --g-->  S
```
be a commutative square of schemes and let `M` be a sheaf of modules on `X`.  Suppose that for
every affine open `U` of `S` and every affine open `V` of `S'` contained in `g ⁻¹ᵁ U` the
base-change morphism of the square obtained by restricting the two bases to `U` and `V` is
invertible at the inverse image of `M`.  Then the base-change morphism of the given square is
invertible at `M`. -/
theorem isIso_baseChangeNatTrans_of_affineBases (w : g' ≫ f = f' ≫ g) (M : X.Modules)
    (hloc : ∀ (U : S.Opens) (V : S'.Opens) (hV : V ≤ g ⁻¹ᵁ U), IsAffineOpen U → IsAffineOpen V →
      IsIso ((AffinePushforward.baseChangeNatTrans (restrictBasesSquare w U hV)).app
        ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj M))) :
    IsIso ((AffinePushforward.baseChangeNatTrans w).app M) := by
  refine isIso_baseChangeNatTrans_of_isOpenCover_le w M
    (I := { p : S.Opens × S'.Opens //
      IsAffineOpen p.1 ∧ IsAffineOpen p.2 ∧ p.2 ≤ g ⁻¹ᵁ p.1 })
    (fun p => p.1.1) (fun p => p.1.2) (fun p => p.2.2.2) ?_
    (fun p => hloc _ _ p.2.2.2 p.2.1 p.2.2.1)
  refine le_antisymm le_top fun x _ => ?_
  obtain ⟨U, hU, hxU, -⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (X := S) (x := g.base x)
      (U := ⊤) (by trivial)
  obtain ⟨V, hVaff, hxV, hVle⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (X := S') (x := x)
      (U := g ⁻¹ᵁ U) hxU
  exact Opens.mem_iSup.2 ⟨⟨(U, V), hU, hVaff, hVle⟩, hxV⟩

end Restrict

end Stacks.AlgebraicGeometry.FlatBaseChangeCohomology

end
