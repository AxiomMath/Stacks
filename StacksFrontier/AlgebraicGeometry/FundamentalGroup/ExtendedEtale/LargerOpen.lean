module

public import StacksFrontier.AlgebraicGeometry.Etale.Morphisms.EtaleAt
public import StacksFrontier.AlgebraicGeometry.Etale.Morphisms.Permanence
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# Restricting a cover of a larger open, and the depth condition under restriction

Let `X` be a locally Noetherian scheme and `U ⟶ U' ⟶ X` a chain of open immersions whose total
range has a complement of depth at least two in `X`. This file collects the two kinds of fact
needed to compare a finite étale cover of `U'` with the restriction of an extension over `X`.

The first is that the depth-two hypothesis survives restriction: it holds for `U'` off the range
of `U ⟶ U'`, and it holds on any scheme pulled back along an open immersion. Both reduce to
`RingHom.depth_eq_of_isEtaleLocalHom` (Stacks Tag 039T) applied to the stalk maps of an open
immersion, which are étale local homomorphisms by `AlgebraicGeometry.etale_iff_forall_isEtaleAt`
(Stacks Tag 0259).

The second is purely about slice categories: an isomorphism `(Over.pullback i).obj A ≅ Over.mk π`
identifying the restriction of `A : Over U'` with a given `π : V ⟶ U` is the same data as a
morphism `V ⟶ A.left` making `π` a pullback of `A.hom` along `i`, and that correspondence is
compatible with morphisms of `A`.

## Main definitions

* `Stacks.FundamentalGroup.ExtendedEtaleFold.coverMapOfPullbackIso` — the morphism `V ⟶ A.left`
  determined by an identification of the restriction of `A` with `π`.

## Main results

* `two_le_depth_restrict` — the depth-two condition for `U ⟶ U'` follows from the one for
  `U ⟶ X`.
* `two_le_depth_pullback` — the depth-two condition pulls back along an open immersion.
* `isPullback_coverMapOfPullbackIso` — the identification makes `π` a pullback of `A.hom`.
* `pullback_map_comp_eq_of_coverMap_comp` and `coverMap_comp_eq_of_pullback_map_comp` — a
  morphism of slice objects is compatible with the two identifications precisely when it is
  compatible with the two induced morphisms out of `V`.

## Implementation notes

**No `@[stacks]` attribute is placed here.** These are the ingredients of the `larger_open`
clause of [Stacks, Tag 0EY6], not the clause itself. The clause is
`Stacks.FundamentalGroup.ExtendedEtaleFold.existsUnique_restrictionIso`, in
`StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtale.LargerOpenIso`, and the attribute
is written there; the uniqueness statement it consumes is
`Stacks.FundamentalGroup.ExtendedEtaleFold.extendedEtale_unique` of the `unique_extension`
clause.

## References

* [Stacks Project, Tag 0EY6](https://stacks.math.columbia.edu/tag/0EY6)
* [Stacks Project, Tag 039T](https://stacks.math.columbia.edu/tag/039T)
* [Stacks Project, Tag 0259](https://stacks.math.columbia.edu/tag/0259)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.FundamentalGroup.ExtendedEtaleFold

/-! ### Restriction of the depth-two condition -/

/-- A point off the range of `i` has image under an open immersion `k` off the range of `i ≫ k`. -/
private theorem apply_notMem_opensRange_comp {U U' X : Scheme.{u}} (i : U ⟶ U')
    [IsOpenImmersion i]
    (k : U' ⟶ X) [IsOpenImmersion k] {x : U'} (hx : x ∉ (i.opensRange : Set U')) :
    k x ∉ ((i ≫ k).opensRange : Set X) := fun hxX => by
  obtain ⟨u, hu⟩ := Scheme.Hom.mem_opensRange.mp hxX
  exact hx (Scheme.Hom.mem_opensRange.mpr ⟨u, k.isOpenEmbedding.injective (by simpa using hu)⟩)

/-- The depth of a stalk can be computed after an open immersion, as stalk maps are étale. -/
private theorem two_le_depth_of_isOpenImmersion {Y X : Scheme.{u}} (g : Y ⟶ X)
    [IsOpenImmersion g] [IsLocallyNoetherian X] (y : Y)
    (h : (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk (g y))
      (IsLocalRing.maximalIdeal (X.presheaf.stalk (g y))) (X.presheaf.stalk (g y))) :
    (2 : ℕ∞) ≤ Module.depth (Y.presheaf.stalk y)
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y) := by
  let : IsLocallyNoetherian Y := isLocallyNoetherian_of_isOpenImmersion g
  rwa [(RingHom.depth_eq_of_isEtaleLocalHom (g.stalkMap y).hom
    ((AlgebraicGeometry.etale_iff_forall_isEtaleAt g).mp inferInstance y)).symm]

/-- **The depth-two condition restricts to an intermediate open subscheme.** If the local rings
of `X` have depth at least two outside the range of `U ⟶ U' ⟶ X`, then the local rings of `U'`
have depth at least two outside the range of `U ⟶ U'`: the stalks of `U'` are the stalks of `X`,
because the stalk maps of an open immersion are étale local homomorphisms and étale local
homomorphisms preserve depth. -/
public theorem two_le_depth_restrict {U U' X : Scheme.{u}} (i : U ⟶ U') [IsOpenImmersion i]
    (k : U' ⟶ X) [IsOpenImmersion k] [IsLocallyNoetherian X]
    (hdepth : ∀ x : X, x ∉ ((i ≫ k).opensRange : Set X) →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) :
    ∀ x : U', x ∉ (i.opensRange : Set U') →
      (2 : ℕ∞) ≤ Module.depth (U'.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (U'.presheaf.stalk x)) (U'.presheaf.stalk x) := by
  intro x hx
  exact two_le_depth_of_isOpenImmersion k x (hdepth (k x) (apply_notMem_opensRange_comp i k hx))

/-- **The depth-two condition pulls back along an open immersion.** If the local rings of `Y`
have depth at least two over the complement of the range of `U ⟶ U' ⟶ X`, then the local rings
of `Y ×_X U'` have depth at least two over the complement of the range of `U ⟶ U'`. As in
`two_le_depth_restrict`, the stalks are unchanged because the first projection is an open
immersion. -/
public theorem two_le_depth_pullback {U U' X Y : Scheme.{u}} (i : U ⟶ U') [IsOpenImmersion i]
    (k : U' ⟶ X) [IsOpenImmersion k] [IsLocallyNoetherian X] (f : Y ⟶ X)
    [IsLocallyNoetherian Y]
    (hdepthY : ∀ y : Y, f y ∉ ((i ≫ k).opensRange : Set X) →
      (2 : ℕ∞) ≤ Module.depth (Y.presheaf.stalk y)
        (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y)) :
    ∀ z : (pullback f k : Scheme.{u}), (pullback.snd f k) z ∉ (i.opensRange : Set U') →
      (2 : ℕ∞) ≤ Module.depth ((pullback f k).presheaf.stalk z)
        (IsLocalRing.maximalIdeal ((pullback f k).presheaf.stalk z))
        ((pullback f k).presheaf.stalk z) := by
  intro z hz
  refine two_le_depth_of_isOpenImmersion (pullback.fst f k) z (hdepthY _ ?_)
  have hp : f ((pullback.fst f k) z) = k ((pullback.snd f k) z) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  rw [hp]
  exact apply_notMem_opensRange_comp i k hz

/-! ### The morphism out of the cover determined by an identification of restrictions -/

variable {U U' V : Scheme.{u}} (i : U ⟶ U') (A : Over U') (π : V ⟶ U) [HasPullback A.hom i]

/-- **The morphism from the cover to a slice object identified with it after restriction.** An
isomorphism `e : (Over.pullback i).obj A ≅ Over.mk π` exhibits `π` as the restriction of
`A.hom` along `i`; composing its inverse with the first projection gives the induced morphism
`V ⟶ A.left`. -/
public def coverMapOfPullbackIso (e : (Over.pullback i).obj A ≅ Over.mk π) : V ⟶ A.left :=
  e.inv.left ≫ pullback.fst A.hom i

/-- The inverse of an identification of the restriction of `A` with `π` lies over `π`. -/
private theorem inv_left_comp_snd (e : (Over.pullback i).obj A ≅ Over.mk π) :
    e.inv.left ≫ pullback.snd A.hom i = π := by
  simpa only [Over.pullback_obj_hom, Over.mk_hom] using Over.w e.inv

/-- The restriction of a morphism of slice objects commutes with the first projections. -/
private theorem pullback_map_left_comp_fst (A' : Over U') [HasPullback A'.hom i] (e : A ⟶ A') :
    ((Over.pullback i).map e).left ≫ pullback.fst A'.hom i = pullback.fst A.hom i ≫ e.left :=
  pullback.lift_fst _ _ _

/-- **The induced morphism makes the cover a pullback.** -/
public theorem isPullback_coverMapOfPullbackIso (e : (Over.pullback i).obj A ≅ Over.mk π) :
    IsPullback π (coverMapOfPullbackIso i A π e) i A.hom := by
  have hw := inv_left_comp_snd i A π e
  have hcomm : coverMapOfPullbackIso i A π e ≫ A.hom = π ≫ i := by
    rw [coverMapOfPullbackIso, Category.assoc, pullback.condition, ← Category.assoc, hw]
  exact (IsPullback.of_iso_pullback (CommSq.mk hcomm) ((Over.forget U).mapIso e.symm) rfl hw).flip

/-- **Compatibility of a morphism of slice objects with the two identifications, from
compatibility with the two induced morphisms.** -/
public theorem pullback_map_comp_eq_of_coverMap_comp (A' : Over U') [HasPullback A'.hom i]
    (eRest : (Over.pullback i).obj A ≅ Over.mk π) (eV : (Over.pullback i).obj A' ≅ Over.mk π)
    (e : A ≅ A')
    (h : coverMapOfPullbackIso i A π eRest ≫ e.hom.left =
      coverMapOfPullbackIso i A' π eV) :
    (Over.pullback i).map e.hom ≫ eV.hom = eRest.hom := by
  have hfst : pullback.fst A.hom i ≫ e.hom.left =
      eRest.hom.left ≫ coverMapOfPullbackIso i A' π eV := by
    rw [← h]
    simp [coverMapOfPullbackIso]
  have hVw := inv_left_comp_snd i A' π eV
  have hsecond : ((Over.pullback i).map e.hom).left ≫ pullback.snd A'.hom i =
      (eRest.hom.left ≫ eV.inv.left) ≫ pullback.snd A'.hom i := by
    calc
      ((Over.pullback i).map e.hom).left ≫ pullback.snd A'.hom i = pullback.snd A.hom i := by
            change (pullback.lift (pullback.fst A.hom i ≫ e.hom.left)
              (pullback.snd A.hom i) _) ≫ pullback.snd A'.hom i = pullback.snd A.hom i
            rw [pullback.lift_snd]
      _ = eRest.hom.left ≫ π := (Over.w eRest.hom).symm
      _ = eRest.hom.left ≫ (eV.inv.left ≫ pullback.snd A'.hom i) := by rw [hVw]
      _ = (eRest.hom.left ≫ eV.inv.left) ≫ pullback.snd A'.hom i := by simp [Category.assoc]
  have hmap : ((Over.pullback i).map e.hom).left = eRest.hom.left ≫ eV.inv.left := by
    apply pullback.hom_ext
    · rw [pullback_map_left_comp_fst]
      simpa [coverMapOfPullbackIso, Category.assoc] using hfst
    · change ((Over.pullback i).map e.hom).left ≫ pullback.snd A'.hom i =
        eRest.hom.left ≫ eV.inv.left ≫ pullback.snd A'.hom i
      exact hsecond
  ext
  rw [Over.comp_left, hmap]
  simp

/-- **Compatibility of a morphism of slice objects with the two induced morphisms, from
compatibility with the two identifications.** The converse of
`pullback_map_comp_eq_of_coverMap_comp`. -/
public theorem coverMap_comp_eq_of_pullback_map_comp (A' : Over U') [HasPullback A'.hom i]
    (eRest : (Over.pullback i).obj A ≅ Over.mk π) (eV : (Over.pullback i).obj A' ≅ Over.mk π)
    (e : A ≅ A') (h : (Over.pullback i).map e.hom ≫ eV.hom = eRest.hom) :
    coverMapOfPullbackIso i A π eRest ≫ e.hom.left = coverMapOfPullbackIso i A' π eV := by
  have hm : (Over.pullback i).map e.hom = eRest.hom ≫ eV.inv := by
    simpa using congrArg (fun q => q ≫ eV.inv) h
  have hmLeft : ((Over.pullback i).map e.hom).left = eRest.hom.left ≫ eV.inv.left := by
    simpa only [Over.comp_left] using congrArg Over.Hom.left hm
  dsimp only [coverMapOfPullbackIso]
  rw [Category.assoc, ← pullback_map_left_comp_fst i A A' e.hom, hmLeft]
  simp

end Stacks.FundamentalGroup.ExtendedEtaleFold

end
