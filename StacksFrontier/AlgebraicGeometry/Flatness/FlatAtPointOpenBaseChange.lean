module

public import StacksFrontier.AlgebraicGeometry.Etale.FlatFiniteTypeModules
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.FreeStalk
public import StacksFrontier.AlgebraicGeometry.Modules.FreeSections
public import StacksFrontier.AlgebraicGeometry.Modules.StalkFreePullback
public import StacksFrontier.AlgebraicGeometry.StalkFreeBridge.StalkFree

/-!
# Flatness at a point after a flat base change, and the free module after base change

Two pointwise facts about flatness over the base of a module pulled back along a base change
`b : T ⟶ S`:

* for a flat `g : Y ⟶ S`, the pullback of a free module `𝒪_Y^{(ι)}` along `Y ×_S T ⟶ Y` is flat
  over `T` at every point;
* for `f : X ⟶ S` and a flat `b`, in particular the inclusion of an open of `S`, the pullback of a
  quasi-coherent `F` on `X` to `X ×_S T` is flat over `T` at a point exactly when `F` is flat over
  `S` at the image of that point in `X`.

## Main results

* `AlgebraicGeometry.isFlatOverAt_pullback_free`: the free module after base change.
* `AlgebraicGeometry.isFlatOverAt_pullback_fst_iff_of_flat`: flatness at a point across a flat
  base change, and `AlgebraicGeometry.isFlatOverAt_pullback_fst_iff_of_opens` its instance for
  the inclusion of an open of the base.

## References

* [Stacks Project, Tag 01U8](https://stacks.math.columbia.edu/tag/01U8)
* [Stacks Project, Tag 02JZ](https://stacks.math.columbia.edu/tag/02JZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **The free module after base change is flat over the new base.** For a flat `g : Y ⟶ S` and any
`b : T ⟶ S`, the pullback of the free module `𝒪_Y^{(ι)}` to `Y ×_S T` is flat over `T` at every
point. -/
theorem isFlatOverAt_pullback_free {Y S T : Scheme.{u}} (g : Y ⟶ S) [Flat g] (b : T ⟶ S)
    (ι : Type u) (x : ↑(pullback g b)) :
    IsFlatOverAt (pullback.snd g b).toLRSHom.toShHom
      ((Scheme.Modules.pullback (pullback.fst g b)).obj (Scheme.Modules.free Y ι)) x :=
  isFlatOverAt_of_free_stalk (pullback.snd g b) _ x
    (Stacks.StalkFreeBridge.free_stalk_pullback (pullback.fst g b) _ x
      (Stacks.StalkFreeBridge.free_stalk_of_isLocallyFree _ _))

/-- **Flatness at a point across a flat base change.** For `f : X ⟶ S`, a flat `b : T ⟶ S` and a
quasi-coherent `F` on `X`, the pullback of `F` to `X ×_S T` is flat over `T` at a point exactly
when `F` is flat over `S` at the image of that point in `X`. -/
theorem isFlatOverAt_pullback_fst_iff_of_flat {X S T : Scheme.{u}} (f : X ⟶ S) (b : T ⟶ S)
    [Flat b] (F : X.Modules) [F.IsQuasicoherent] (x : ↑(pullback f b)) :
    IsFlatOverAt (pullback.snd f b).toLRSHom.toShHom
        ((Scheme.Modules.pullback (pullback.fst f b)).obj F) x ↔
      IsFlatOverAt f.toLRSHom.toShHom F (pullback.fst f b x) :=
  let : SheafOfModules.IsQuasicoherent (R := structureSheafRing X.toRingedSpace) F :=
    inferInstanceAs (SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) F)
  ⟨isFlatOverAt_of_isFlatOverAt_pullback f b F,
    modulePullback_isFlatOverAt (IsPullback.of_hasPullback f b) F x⟩

/-- **Flatness at a point across the restriction to an open of the base.** The pullback of a
quasi-coherent `F` to `X ×_S U`, for an open `U ⊆ S`, is flat over `U` at a point exactly when
`F` is flat over `S` at its image in `X`. -/
theorem isFlatOverAt_pullback_fst_iff_of_opens {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens)
    (F : X.Modules) [F.IsQuasicoherent] (x : ↑(pullback f U.ι)) :
    IsFlatOverAt (pullback.snd f U.ι).toLRSHom.toShHom
        ((Scheme.Modules.pullback (pullback.fst f U.ι)).obj F) x ↔
      IsFlatOverAt f.toLRSHom.toShHom F (pullback.fst f U.ι x) :=
  isFlatOverAt_pullback_fst_iff_of_flat f U.ι F x

end AlgebraicGeometry

end
