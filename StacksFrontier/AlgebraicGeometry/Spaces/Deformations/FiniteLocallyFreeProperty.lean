module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Finrank
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.ThickeningProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeFiniteFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeRepresentableIff

/-!
# Finite local freeness in a cartesian finite-order deformation

Let

```
(X ⊂ X') --(f, f')--> (Y ⊂ Y')
         ↘                ↙
            (B ⊂ B')
```

be a cartesian finite-order deformation of algebraic spaces over a scheme `S`. Part 0CGV of
Stacks 0CG6 says that `f` is finite locally free (of rank `d`) if and only if `f'` is. Finite
local freeness is the notion of Stacks 03ZV: affine, with the direct image of the structure sheaf
a finite locally free module (of rank `d`) on the small étale site of the target,
`AlgebraicGeometry.Space.IsFiniteLocallyFree` and
`AlgebraicGeometry.Space.IsFiniteLocallyFreeOfRank`.

The proof follows the source. By Stacks 03ZU,
`AlgebraicGeometry.Space.isFiniteLocallyFree_presheaf_iff_isFiniteLocallyFree` and
`AlgebraicGeometry.Space.presheaf_iff_isFiniteLocallyFreeOfRank`, both notions may be read on the
represented base changes.

* If `f` is finite locally free it is finite, flat and locally of finite presentation by
  Stacks 0416, so `f'` is too by parts 0CGU, 0CG8 and 0CGK of Stacks 0CG6, and `f'` is finite
  locally free by Stacks 0416 again.
* For the rank, let `T ⟶ Y'` be a scheme over `Y'` and `ψ' : T ×_{Y'} X' ⟶ T` the base change
  of `f'`. The inverse image `T₀ ⊂ T` of `Y` is a thickening of schemes, and the base change of
  `ψ'` along it is a represented base change `ψ₀` of `f`, of rank `d`. The rank function of the
  finite flat `ψ'` at a point of `T₀` is that of `ψ₀`, and every point of `T` is in `T₀`.
* Conversely `f` is a base change of `f'`, and finite local freeness, with or without a rank, is
  stable under base change (Stacks 03ZY).

## Main results

* `AlgebraicGeometry.Space.CartesianFiniteOrderDeformation.isFiniteLocallyFree_iff`:
  **Stacks 0CG6, part 0CGV**, without a rank.
* `AlgebraicGeometry.Space.CartesianFiniteOrderDeformation.isFiniteLocallyFreeOfRank_iff`:
  **Stacks 0CG6, part 0CGV**, of rank `d`.

## References

* [Stacks Project, Tag 0416](https://stacks.math.columbia.edu/tag/0416)
* [Stacks Project, Tag 03ZU](https://stacks.math.columbia.edu/tag/03ZU)
* [Stacks Project, Tag 03ZV](https://stacks.math.columbia.edu/tag/03ZV)
* [Stacks Project, Tag 03ZY](https://stacks.math.columbia.edu/tag/03ZY)
* [Stacks Project, Tag 0CG6](https://stacks.math.columbia.edu/tag/0CG6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

namespace CartesianFiniteOrderDeformation

variable {T : BigFppfSite.{u}} {S : Scheme.{u}} {hS : T.Contains S}
    (D : CartesianFiniteOrderDeformation T S hS)

/-- If `f` is finite locally free in the representable sense, so is `f'`: by Stacks 0416 both
are finite, flat and locally of finite presentation, and these three properties pass from `f`
to `f'`. -/
theorem presheaf_isFiniteLocallyFree_f'
    (hf : (MorphismProperty.inverseImage
      (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme T S hS)).presheaf D.f) :
    (MorphismProperty.inverseImage
      (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme T S hS)).presheaf D.f' := by
  obtain ⟨hfin, hflat, hlfp⟩ := (isFiniteLocallyFree_presheaf_iff T S hS
    D.source_thickening.1.1 D.target_thickening.1.1 D.f).1 hf
  exact (isFiniteLocallyFree_presheaf_iff T S hS D.X'.2 D.Y'.2 D.f').2
    ⟨D.isFinite_iff.1 hfin, D.isFlat_iff.1 hflat, D.isLocallyOfFinitePresentation_iff.1 hlfp⟩

/-- **The rank passes from `f` to `f'`.** If every represented base change of `f` is finite
locally free of rank `r` and `f'` is finite locally free, every represented base change of `f'`
has rank `r`.

A represented base change `ψ' : T' ⟶ T` of `f'` restricts over the thickening `T₀ ⊂ T` cut out
by `Y ⊂ Y'` to a represented base change `ψ₀` of `f`; the rank of the finite flat `ψ'` at a
point of `T₀` is the rank of `ψ₀` there, and every point of `T` lies in `T₀`. -/
theorem presheaf_isFiniteLocallyFreeOfRank_f' (r : ℕ)
    (hf : (MorphismProperty.inverseImage
      (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} r)
      (BigFppfOver.toScheme T S hS)).presheaf D.f)
    (hf' : (MorphismProperty.inverseImage
      (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme T S hS)).presheaf D.f') :
    (MorphismProperty.inverseImage
      (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} r)
      (BigFppfOver.toScheme T S hS)).presheaf D.f' := by
  refine ⟨hf'.rep, fun A A' g fst snd sq => ?_⟩
  let Tscheme := BigFppfOver.toScheme T S hS
  have finite_flat : ∀ {X Y : Scheme.{u}} (q : X ⟶ Y),
      Stacks.Morphisms.IsFiniteLocallyFree q →
        _root_.AlgebraicGeometry.IsFinite q ∧ Flat q :=
    fun q hq => ⟨hq.isFinite q, hq.flat q⟩
  obtain ⟨_, _⟩ := finite_flat _ (hf'.property g fst snd sq)
  -- The thickening of `A` cut out by `Y ⊂ Y'`, and the base change of `f` over it.
  obtain ⟨A₀, j, p, hpb, hthick⟩ :=
    exists_thickening_chart_pullback_subfunctor T S hS D.target_thickening A g
  have hsq₀ := hf.rep.isPullback p
  have hrank₀ : Stacks.Morphisms.IsFiniteLocallyFreeOfRank (Tscheme.map (hf.rep.snd p)) r :=
    hf.property p _ _ hsq₀
  obtain ⟨_, _⟩ := finite_flat _ (hrank₀.isFiniteLocallyFree _ r)
  -- The base change of `f` over `A₀` is the base change of `ψ'` along `A₀ ⊂ A`.
  have hbig : IsPullback (hf.rep.fst p ≫ D.X.ι) (yoneda.map (hf.rep.snd p)) D.f'
      (yoneda.map j ≫ g) := by
    rw [← hpb.w]
    exact hsq₀.paste_horiz D.isPullback_f.flip
  let k := sq.lift (hf.rep.fst p ≫ D.X.ι) (yoneda.map (hf.rep.snd p ≫ j))
    (by rw [hbig.w, Functor.map_comp, Category.assoc])
  have hk : k ≫ fst = hf.rep.fst p ≫ D.X.ι := sq.lift_fst _ _ _
  have hk' : k ≫ yoneda.map snd = yoneda.map (hf.rep.snd p) ≫ yoneda.map j := by
    rw [sq.lift_snd, Functor.map_comp]
  have hleft : IsPullback k (yoneda.map (hf.rep.snd p)) (yoneda.map snd) (yoneda.map j) :=
    IsPullback.of_right (by rwa [hk]) hk' sq
  have hleft' : IsPullback (yoneda.map (yoneda.preimage k)) (yoneda.map (hf.rep.snd p))
      (yoneda.map snd) (yoneda.map j) := by
    rwa [Functor.map_preimage]
  have hsite : IsPullback (yoneda.preimage k) (hf.rep.snd p) snd j :=
    IsPullback.of_map_of_faithful yoneda hleft'
  have hscheme := hsite.map Tscheme
  show Stacks.Morphisms.IsFiniteLocallyFreeOfRank (Tscheme.map snd) r
  rw [Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_forall_finrank_eq _ r] at hrank₀ ⊢
  intro t
  obtain ⟨t₀, rfl⟩ := hthick.2 t
  rw [← Scheme.Hom.finrank_of_isPullback _ _ _ _ hscheme t₀]
  exact hrank₀ t₀

/-- **Stacks 0CG6, part 0CGV.** In a cartesian finite-order deformation of algebraic spaces the
morphism of special fibres is finite locally free if and only if its ambient deformation is. -/
@[stacks 0CG6 "0CGV: finite locally free"]
theorem isFiniteLocallyFree_iff :
    IsFiniteLocallyFree T S hS D.smallHom ↔ IsFiniteLocallyFree T S hS D.ambientHom := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hp := presheaf_of_isFiniteLocallyFree T S hS D.smallHom
      (relativelyRepresentable_of_isAffineHom T S hS D.smallHom h.1) h
    exact isFiniteLocallyFree_of_presheaf T S hS D.ambientHom (D.presheaf_isFiniteLocallyFree_f' hp)
  · have hp' := (isFiniteLocallyFree_presheaf_iff_isFiniteLocallyFree T S hS D.ambientHom).2 h
    exact isFiniteLocallyFree_of_presheaf T S hS D.smallHom
      (isFiniteLocallyFree_presheaf_of_isPullback T S hS D.isPullback_f.flip hp')

/-- **Stacks 0CG6, part 0CGV, with the rank.** In a cartesian finite-order deformation of
algebraic spaces the morphism of special fibres is finite locally free of rank `d` if and only
if its ambient deformation is. -/
@[stacks 0CG6 "0CGV: finite locally free of rank d"]
theorem isFiniteLocallyFreeOfRank_iff (d : ℕ) :
    IsFiniteLocallyFreeOfRank T S hS D.smallHom d ↔
      IsFiniteLocallyFreeOfRank T S hS D.ambientHom d := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hflf' := (isFiniteLocallyFree_presheaf_iff_isFiniteLocallyFree T S hS D.ambientHom).2
      (D.isFiniteLocallyFree_iff.1 h.1)
    exact (presheaf_iff_isFiniteLocallyFreeOfRank T S hS D.ambientHom d).1
      (D.presheaf_isFiniteLocallyFreeOfRank_f' d
        ((presheaf_iff_isFiniteLocallyFreeOfRank T S hS D.smallHom d).2 h) hflf')
  · exact (presheaf_iff_isFiniteLocallyFreeOfRank T S hS D.smallHom d).1
      (isFiniteLocallyFreeOfRank_presheaf_of_isPullback T S hS d D.isPullback_f.flip
        ((presheaf_iff_isFiniteLocallyFreeOfRank T S hS D.ambientHom d).2 h))

end CartesianFiniteOrderDeformation

end AlgebraicGeometry.Space

end
