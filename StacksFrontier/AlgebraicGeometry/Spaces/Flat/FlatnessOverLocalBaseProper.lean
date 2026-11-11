module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.FlatnessOverLocalBase
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented

/-!
# Flatness over a local base: the proper example of Stacks 0CWM

Stacks 0CWM (`AlgebraicGeometry.Space.isFlatOver_of_forall_specializes_closedFibre`) says that
for `f : X ⟶ S` locally of finite type over a local scheme `S` with closed point `s` and `ℱ` a
finite type quasi-coherent `𝒪_X`-module, flatness of `ℱ` over `S` follows from (1) every point of
`Ass_{X/S}(ℱ)` specializing to a point of the closed fibre `X_s` and (2) flatness of `ℱ` over `S`
at every point of `X_s`. Its footnote gives two examples in which (1) holds: `f` of finite type
with `ℱ` pure along `X_s`
(`AlgebraicGeometry.Space.isFlatOver_of_isPureAbove_of_isAffineLocalAt`), and `f` proper. The
second example is proved here.

## Main results

* `AlgebraicGeometry.Space.specializes_of_isClosed_of_isLocalBase`: over a local base every
  point specializes to the closed point.
* `AlgebraicGeometry.Space.exists_specializes_closedFibre_of_isProper`: the second example of
  the footnote of Stacks 0CWM — for `f` proper over a local base, every point of `|X|`
  specializes to a point of the closed fibre, so hypothesis (1) holds.
* `AlgebraicGeometry.Space.isFlatOver_of_isProper_of_forall_closedFibre`: for `f` proper over a
  local base, hypothesis (2) alone gives flatness of `ℱ` over `S`.

## References

* [Stacks Project, Tag 0CWM](https://stacks.math.columbia.edu/tag/0CWM)
* [Stacks Project, Tag 03ZM](https://stacks.math.columbia.edu/tag/03ZM)
* [Stacks Project, Tag 03HI](https://stacks.math.columbia.edu/tag/03HI)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] pointTopology

/-! ### The footnote: properness supplies hypothesis (1) -/

/-- **Over a local base every point specializes to the closed point.** Let the target `Y` be
represented by a scheme of the site isomorphic to the spectrum of a local ring, and let `s` be a
closed point of `|Y|`. Then every point of `|Y|` specializes to `s`.

The points of `Y` are homeomorphic to those of the representing scheme
(`AlgebraicGeometry.Space.pointsHomeomorphOfIso` and
`AlgebraicGeometry.Space.schemePointsHomeomorph`), and in a scheme isomorphic to the spectrum
of a local ring every point specializes to every closed point
(`AlgebraicGeometry.Space.specializes_of_isClosed_isoSpec_isLocalRing`). -/
theorem specializes_of_isClosed_of_isLocalBase {Y : AlgebraicSpaces B S hS}
    (hlocal : ∃ (T : BigFppfOver B S hS) (A : CommRingCat.{u}), IsLocalRing A ∧
      Nonempty (Spec A ≅ (BigFppfOver.toScheme B S hS).obj T) ∧ Nonempty (yoneda.obj T ≅ Y.1))
    {s : points B S hS Y.1} (hs : IsClosed ({s} : Set (points B S hS Y.1)))
    (t : points B S hS Y.1) : t ⤳ s := by
  obtain ⟨T, A, hA, ⟨φ⟩, ⟨e⟩⟩ := hlocal
  let E := (pointsHomeomorphOfIso B S hS e).symm.trans (schemePointsHomeomorph B S hS T)
  have hEs : IsClosed ({E s} : Set ((BigFppfOver.toScheme B S hS).obj T)) := by
    rw [← Set.image_singleton]
    exact E.isClosedMap _ hs
  have h := (specializes_of_isClosed_isoSpec_isLocalRing hA φ (E t) (E s) hEs).map
    E.symm.continuous
  simpa using h

/-- **The second example of the footnote of Stacks 0CWM: for `f` proper, hypothesis (1)
holds.** Let `Y` be a local scheme with closed point `s`, read as in
`AlgebraicGeometry.Space.isFlatOver_of_forall_specializes_closedFibre`, and let `f : X ⟶ Y` be
proper. Then every point of `|X|` — in particular every point of `Ass_{X/S}(ℱ)` for every
`𝒪_X`-module `ℱ` — specializes to a point of the closed fibre `X_s`.

A proper morphism is universally closed, hence closed on points
(`AlgebraicGeometry.Space.isClosedMap_pointsMap_of_pullback_fst_id`), so the image of the
closure of `{x'}` is a closed subset of `|Y|` containing `f(x')`; every point of the local base
specializes to `s` (`AlgebraicGeometry.Space.specializes_of_isClosed_of_isLocalBase`), so `s`
lies in that image. -/
@[stacks 0CWM "second example of the footnote: for f proper over the local base, every point \
of |X|, so every point of Ass_{X/S}(F), specializes to a point of the closed fibre X_s"]
theorem exists_specializes_closedFibre_of_isProper {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (s : points B S hS Y.1)
    (hlocal : ∃ (T : BigFppfOver B S hS) (A : CommRingCat.{u}), IsLocalRing A ∧
      Nonempty (Spec A ≅ (BigFppfOver.toScheme B S hS).obj T) ∧ Nonempty (yoneda.obj T ≅ Y.1))
    (hs : IsClosed ({s} : Set (points B S hS Y.1))) (hprop : IsProper B S hS f.hom)
    (x' : points B S hS X.1) :
    ∃ θ : points B S hS X.1, x' ⤳ θ ∧ pointsMap B S hS X.1 f.hom θ = s := by
  have hcl : IsClosedMap (pointsMap B S hS X.1 f.hom) :=
    isClosedMap_pointsMap_of_pullback_fst_id B S hS f.hom
      (IsProper.universallyClosed B S hS hprop Y.1 Y.2 (𝟙 Y.1))
  have hC : IsClosed (pointsMap B S hS X.1 f.hom '' closure {x'}) := hcl _ isClosed_closure
  have hmem : pointsMap B S hS X.1 f.hom x' ∈ pointsMap B S hS X.1 f.hom '' closure {x'} :=
    ⟨x', subset_closure rfl, rfl⟩
  obtain ⟨θ, hθ, hθs⟩ :=
    (specializes_of_isClosed_of_isLocalBase hlocal hs _).mem_closed hC hmem
  exact ⟨θ, specializes_iff_mem_closure.2 hθ, hθs⟩

/-- **Stacks 0CWM for a proper morphism.** Over a local base with closed point `s`, for
`f : X ⟶ Y` proper and `ℱ` a finite type quasi-coherent `𝒪_X`-module, flatness of `ℱ` over the
base at every point of the closed fibre `X_s` gives flatness of `ℱ` over the base: hypothesis
(1) is supplied by `AlgebraicGeometry.Space.exists_specializes_closedFibre_of_isProper`, and a
proper morphism is of finite type, hence locally of finite type. -/
theorem isFlatOver_of_isProper_of_forall_closedFibre {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (s : points B S hS Y.1)
    (hlocal : ∃ (T : BigFppfOver B S hS) (A : CommRingCat.{u}), IsLocalRing A ∧
      Nonempty (Spec A ≅ (BigFppfOver.toScheme B S hS).obj T) ∧ Nonempty (yoneda.obj T ≅ Y.1))
    (hs : IsClosed ({s} : Set (points B S hS Y.1))) (hprop : IsProper B S hS f.hom)
    (hqc : F.IsQuasicoherentOnSite) (hft : SheafOfModules.IsFiniteTypeOnSite F)
    (hflat : ∀ θ : points B S hS X.1, pointsMap B S hS X.1 f.hom θ = s →
      IsFlatOverAtPoint B S hS X.2 f.hom F θ) :
    IsFlatOver B S hS X.2 f.hom F :=
  isFlatOver_of_forall_specializes_closedFibre f F s hlocal hs
    (IsProper.isFiniteType B S hS hprop).1 hqc hft
    (fun x' _ => exists_specializes_closedFibre_of_isProper f s hlocal hs hprop x') hflat

end AlgebraicGeometry.Space

end
