module

public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.BinaryProductRestrict

/-!
# Restriction to an open is a fibre square of divided power schemes

Let `g : X ⟶ Y` be a morphism of divided power schemes and let `V` be an open of the underlying
scheme of `Y`.  Restriction to an open, `Crystalline.DividedPowerScheme.restrict`, leaves the
sections of the structure sheaf and the divided powers on them alone, so the restriction of `g` to
the preimage of `V` is again a morphism of divided power schemes and the square

```
X|_{g⁻¹V} ---> Y|_V
    |            |
    v            v
    X ----g----> Y
```

commutes.  **It is a fibre square in the category of divided power schemes.**  The input is the
universal property of `Y.restrict V` — a morphism of divided power schemes into `Y` whose
underlying map has image inside `V` factors through `Y.restrict V`, which is
`Crystalline.DividedPowerScheme.restrictLift` of
`StacksFrontier/AlgebraicGeometry/Crystalline/BigSite/BinaryProductRestrict.lean` — together with
the fact that `Y.restrict V ⟶ Y` is a monomorphism.

Pasting that fibre square on top of the one defining a divided power fibre product gives the
comparison of [Stacks, Tag 07ME] with restriction to an open: `S ×_{S'} (T'|_W)` is the
restriction of `S ×_{S'} T'` to the preimage of `W` under the second projection.

## Main definitions

* `Crystalline.DividedPowerScheme.Hom.restrictPreimage` — the restriction of `g : X ⟶ Y` to the
  preimage of an open of `Y`, as a morphism `X.restrict (g⁻¹V) ⟶ Y.restrict V`.
* `Crystalline.DividedPowerScheme.pullbackRestrictιIso` — **the comparison
  `(S ×_{S'} T')|_{q⁻¹W} ≅ S ×_{S'} (T'|_W)`.**

## Main results

* `Crystalline.DividedPowerScheme.mono_restrictι` — `Y.restrict V ⟶ Y` is a monomorphism.
* `Crystalline.DividedPowerScheme.isPullback_restrictι` — **the square above is a fibre square of
  divided power schemes.**
* `Crystalline.DividedPowerScheme.hasPullback_restrictι` — hence the fibre product of a
  restriction with an arbitrary morphism of divided power schemes exists.
* `Crystalline.DividedPowerScheme.isPullback_restrictι_pullback` — **[Stacks, Tag 07ME] commutes
  with restriction to an open of one factor.**

## References

* [Stacks Project, Tag 07I3](https://stacks.math.columbia.edu/tag/07I3)
* [Stacks Project, Tag 07ME](https://stacks.math.columbia.edu/tag/07ME)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace Crystalline.DividedPowerScheme

variable {Z X Y : DividedPowerScheme.{u}}

/-! ### The morphism from a restriction is a monomorphism -/

/-- **The morphism from a restriction is a monomorphism**: a morphism of divided power schemes is
determined by its underlying morphism of schemes, and the open immersion of `V` is a
monomorphism of schemes.

`Crystalline.GlobalCrystallineSituation.mono_restrictι` of
`StacksFrontier/AlgebraicGeometry/Crystalline/BigSite/SituationRestrict.lean` is this instance for
the divided power base of a crystalline situation; it is `DividedPowerScheme.mono_of_mono_hom` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/Functoriality.lean`, which this file does
not import, applied there.  The two overlap and should be merged once the import graph allows it. -/
instance mono_restrictι (V : Y.scheme.Opens) : Mono (Y.restrictι V) where
  right_cancellation {_} _ _ h :=
    Hom.ext ((cancel_mono V.ι).1 (congrArg Hom.hom h))

/-! ### Restriction to an open is a fibre square -/

variable (g : X ⟶ Y) (V : Y.scheme.Opens)

/-- The composite `X|_{g⁻¹V} ⟶ X ⟶ Y` has image inside `V`, a point of `g⁻¹V` being by
definition one whose image under `g` lies in `V`. -/
theorem range_restrictι_comp_subset :
    Set.range (X.restrictι (g.hom ⁻¹ᵁ V) ≫ g).hom.base ⊆ (V : Set Y.scheme) := by
  rintro _ ⟨x, rfl⟩
  exact x.2

/-- **The restriction of a morphism of divided power schemes to the preimage of an open of the
target**, the factorization of `X|_{g⁻¹V} ⟶ X ⟶ Y` through `Y|_V` given by
`Crystalline.DividedPowerScheme.restrictLift`. -/
def Hom.restrictPreimage : X.restrict (g.hom ⁻¹ᵁ V) ⟶ Y.restrict V :=
  restrictLift (X.restrictι (g.hom ⁻¹ᵁ V) ≫ g) V (range_restrictι_comp_subset g V)

/-- The restriction of `g` to the preimage of `V` is a morphism over `g`. -/
@[reassoc (attr := simp)]
theorem Hom.restrictPreimage_restrictι :
    g.restrictPreimage V ≫ Y.restrictι V = X.restrictι (g.hom ⁻¹ᵁ V) ≫ g :=
  restrictLift_restrictι _ _ _

/-- **A cone over the restriction square lands in the preimage of `V`.**  If `a ≫ (Y|_V ⟶ Y)` is
`b ≫ g` then every point in the image of `b` is carried by `g` into `V`, because it is carried
there by `a` followed by the open immersion of `V`. -/
theorem range_subset_preimage_of_restrictι_comp {a : Z ⟶ Y.restrict V} {b : Z ⟶ X}
    (h : a ≫ Y.restrictι V = b ≫ g) :
    Set.range b.hom.base ⊆ ((g.hom ⁻¹ᵁ V : X.scheme.Opens) : Set X.scheme) := by
  rintro _ ⟨z, rfl⟩
  have hz : g.hom.base (b.hom.base z) = (a.hom.base z).1 :=
    congrArg (fun k : Z ⟶ Y ↦ k.hom.base z) h.symm
  change g.hom.base (b.hom.base z) ∈ V
  rw [hz]
  exact (a.hom.base z).2

/-- **Restriction to an open is a fibre square of divided power schemes**: the restriction of `X`
to the preimage of an open `V` of `Y` is the fibre product of `g : X ⟶ Y` with `Y|_V ⟶ Y`.

A cone has a unique factorization: the comparison morphism is
`Crystalline.DividedPowerScheme.restrictLift` applied to the leg into `X`, whose image lies in
`g⁻¹V` by `range_subset_preimage_of_restrictι_comp`, and it is unique because `X|_{g⁻¹V} ⟶ X` is a
monomorphism. -/
theorem isPullback_restrictι :
    IsPullback (g.restrictPreimage V) (X.restrictι (g.hom ⁻¹ᵁ V)) (Y.restrictι V) g := by
  have key : ∀ s : PullbackCone (Y.restrictι V) g,
      ∃ p : s.pt ⟶ X.restrict (g.hom ⁻¹ᵁ V),
        p ≫ X.restrictι (g.hom ⁻¹ᵁ V) = s.snd := fun s ↦
    ⟨restrictLift s.snd (g.hom ⁻¹ᵁ V)
        (range_subset_preimage_of_restrictι_comp g V s.condition),
      restrictLift_restrictι _ _ _⟩
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (Hom.restrictPreimage_restrictι g V) (fun s ↦ (key s).choose) (fun s ↦ ?_)
    (fun s ↦ (key s).choose_spec) (fun s m _ hm₂ ↦ ?_))
  · refine (cancel_mono (Y.restrictι V)).1 ?_
    rw [Category.assoc, Hom.restrictPreimage_restrictι, ← Category.assoc, (key s).choose_spec,
      s.condition]
  · exact (cancel_mono (X.restrictι (g.hom ⁻¹ᵁ V))).1 (hm₂.trans (key s).choose_spec.symm)

/-- **The fibre product of a restriction with an arbitrary morphism of divided power schemes
exists.** -/
instance hasPullback_restrictι : HasPullback (Y.restrictι V) g :=
  (isPullback_restrictι g V).hasPullback

/-! ### Divided power fibre products and restriction to an open -/

section FibreProduct

variable {S S' T' : DividedPowerScheme.{u}} (f : S ⟶ S') (t : T' ⟶ S')
  [HasPullback f t] (W : T'.scheme.Opens)

/-- **[Stacks, Tag 07ME] commutes with restriction to an open of one factor.**  The restriction of
the divided power fibre product `S ×_{S'} T'` to the preimage of an open `W` of `T'` under the
second projection is the divided power fibre product `S ×_{S'} (T'|_W)`, the structure morphism of
`T'|_W` over `S'` being the open immersion followed by that of `T'`.

This is the fibre square of `isPullback_restrictι` for the second projection pasted on top of the
fibre square defining `S ×_{S'} T'`. -/
theorem isPullback_restrictι_pullback :
    IsPullback ((pullback.snd f t).restrictPreimage W)
      ((pullback f t).restrictι ((pullback.snd f t).hom ⁻¹ᵁ W) ≫ pullback.fst f t)
      (T'.restrictι W ≫ t) f :=
  (isPullback_restrictι (pullback.snd f t) W).paste_vert
    (IsPullback.of_hasPullback f t).flip

/-- **The divided power fibre product `S ×_{S'} (T'|_W)` exists** whenever `S ×_{S'} T'` does: it
is a restriction of the latter. -/
instance hasPullback_restrictι_comp : HasPullback f (T'.restrictι W ≫ t) :=
  (isPullback_restrictι_pullback f t W).flip.hasPullback

/-- **The comparison isomorphism `(S ×_{S'} T')|_{q⁻¹W} ≅ S ×_{S'} (T'|_W)`** of
[Stacks, Tag 07ME] and restriction to an open, for `q` the second projection.  It is the
isomorphism of `isPullback_restrictι_pullback` with the chosen fibre product. -/
def pullbackRestrictιIso :
    (pullback f t).restrict ((pullback.snd f t).hom ⁻¹ᵁ W) ≅
      pullback f (T'.restrictι W ≫ t) :=
  (isPullback_restrictι_pullback f t W).flip.isoPullback

end FibreProduct

end Crystalline.DividedPowerScheme

end

end
