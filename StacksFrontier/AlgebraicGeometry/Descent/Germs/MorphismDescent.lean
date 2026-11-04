module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.RelativeMorphismFunctor

/-!
# Morphisms of schemes satisfy fpqc descent

Let `X` and `Y` be schemes over a scheme `S`. The functor sending an `S`-scheme `T` to the set of
`T`-morphisms `X_T ⟶ Y_T` is a sheaf for the fpqc topology. In particular, for `f : T ⟶ S`
surjective, flat and quasi-compact, a morphism `ψ₀ : X_T ⟶ Y_T` over `T` which is compatible with
the canonical descent data is the base change of a *unique* morphism `ψ : X ⟶ Y` over `S`; this
case is also proved directly, in components.

## Main results

* `AlgebraicGeometry.isSheaf_relativeHom_fpqc`: for schemes `X` and `Y` over `S`, the relative
  morphism functor `Mor_S(X, Y) : (Sch/S)ᵒᵖ ⥤ Set`, which sends an `S`-scheme `T` to the set of
  `T`-morphisms `X_T ⟶ Y_T`, satisfies the sheaf condition for the fpqc topology on the schemes
  over `S`.
* `AlgebraicGeometry.eq_of_comp_eq_of_surjective_of_flat`: a surjective flat morphism of schemes
  is an epimorphism.
* `AlgebraicGeometry.faithful_overPullback`: base change along a surjective flat morphism is a
  faithful functor on slice categories.
* `AlgebraicGeometry.eq_of_pullbackFst_comp_eq`: two morphisms `X ⟶ Y` with the same base change
  along a surjective flat `f : T ⟶ S` are equal.
* `AlgebraicGeometry.exists_desc_of_surjective_flat_quasiCompact'`: a morphism out of the source
  of a surjective flat quasi-compact morphism `p : X' ⟶ X` whose two restrictions to `X' ×_X X'`
  agree factors through `p`.
* `AlgebraicGeometry.existsUnique_desc_of_surjective_flat_quasiCompact`: for `f : T ⟶ S`
  surjective, flat and quasi-compact and schemes `a : X ⟶ S`, `b : Y ⟶ S`, a morphism
  `ψ₀ : X ×_S T ⟶ Y ×_S T` over `T` whose composite with the projection to `Y` is invariant for
  the two projections of `(X ×_S T) ×_X (X ×_S T)` is the base change of exactly one
  `ψ : X ⟶ Y` over `S`.
* `AlgebraicGeometry.existsUnique_overPullback_map_eq`: the same statement with "over `S`",
  "over `T`" and "base change" read off Mathlib's base-change functor `Over.pullback f`.
* `AlgebraicGeometry.existsUnique_desc_of_surjective_flat_of_isAffine`: the same for a surjective
  flat morphism of affine schemes, quasi-compactness of such a morphism being automatic.
* `AlgebraicGeometry.overPullback_map_eq_iff`: a morphism of slices has base change `ψ₀` exactly
  when the two agree after projecting to `Y`.

## Implementation notes

**The sheaf condition.** The functor `T ↦ Mor_T(X_T, Y_T)` is
`AlgebraicGeometry.relativeHom X Y`, the Yoneda functor of `Y` precomposed with `X ⨯ -` on the
schemes over `S`, whose value at `T` is the set of morphisms `X ×_S T ⟶ Y` over `S`;
`AlgebraicGeometry.relativeHomObjEquivOverBase` identifies that set with the morphisms
`X ×_S T ⟶ Y ×_S T` over `T`. Representable presheaves are fpqc sheaves (Stacks 023Q, the
`Subcanonical` instance of `AlgebraicGeometry.Scheme.fpqcTopology`, carried over to the schemes
over `S` by `CategoryTheory.GrothendieckTopology.subcanonical_over`), and `X ⨯ -` is continuous:
on the schemes over `S` it is `Over.star X ⋙ Over.forget X`, and both factors are continuous for
the induced topologies, by the stability of fpqc coverings under base change.

**"Compatible with the canonical descent data", in components.** For a single covering morphism
`f : T ⟶ S` the canonical descent datum on `X_T = X ×_S T` is the canonical isomorphism
`X_T ×_S T ≅ T ×_S X_T` over `T ×_S T`, and `ψ₀ : X_T ⟶ Y_T` is a morphism of descent data when
the square built from it and the two canonical isomorphisms commutes. Both `X_T ×_S T` and
`T ×_S X_T` are canonically `(T ×_S T) ×_S X`, which is also `X_T ×_X X_T`; under those
identifications the canonical isomorphism is the identity, the two vertical maps of the square
become `ψ₀` applied in the first and in the second `T`-coordinate, and the square says exactly
that `X_T ×_X X_T ⟶ X_T ⟶ Y_T ⟶ Y` does not depend on which projection is taken. That
invariance is the hypothesis `hcan` below.

**Pullback orientation.** `CategoryTheory.Over.pullback f` sends an `S`-scheme `a : X ⟶ S` to
`pullback.snd a f : pullback a f ⟶ T`, so throughout this file `X_T` is `pullback a f` with `X`
in the first and `T` in the second slot, and the projection to `X` is `pullback.fst a f`.

## References

* [Stacks Project, Tag 040L](https://stacks.math.columbia.edu/tag/040L)
* [Stacks Project, Tag 0BL2](https://stacks.math.columbia.edu/tag/0BL2)
* [Stacks Project, Tag 023Q](https://stacks.math.columbia.edu/tag/023Q)
* [Stacks Project, Tag 02VW](https://stacks.math.columbia.edu/tag/02VW)
* [Stacks Project, Tag 02VX](https://stacks.math.columbia.edu/tag/02VX)
* [Stacks Project, Tag 02W0](https://stacks.math.columbia.edu/tag/02W0)
* [Stacks Project, Tag 0AP4](https://stacks.math.columbia.edu/tag/0AP4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {S T : Scheme.{u}}

/-- Let `X` and `Y` be schemes over `S`. The relative morphism functor
`Mor_S(X, Y) : (Sch/S)ᵒᵖ ⥤ Set`, which sends an `S`-scheme `T` to the set of morphisms
`X_T ⟶ Y_T` over `T`, satisfies the sheaf condition for the fpqc topology on the schemes over
`S`. -/
@[stacks 040L "the functor `T ↦ Mor_T(X_T, Y_T)` on the schemes over `S` satisfies the sheaf \
condition for the fpqc topology",
  sga "1 VIII 5.2",
  sga "3 IV 4.5.13" "Hom_S(X, special case",
  sga "3 VIII 1.7.1" "more general"]
theorem isSheaf_relativeHom_fpqc (X Y : Over S) :
    Presheaf.IsSheaf (Scheme.fpqcTopology.{u}.over S) (relativeHom X Y) :=
  have : (prod.functor.obj X).IsContinuous (Scheme.fpqcTopology.{u}.over S)
      (Scheme.fpqcTopology.{u}.over S) :=
    Functor.isContinuous_comp (Over.star X) (Over.forget X) _
      ((Scheme.fpqcTopology.{u}.over S).over X) _
  have : (Scheme.fpqcTopology.{u}.over S).Subcanonical :=
    GrothendieckTopology.subcanonical_over _ _
  (prod.functor.obj X).op_comp_isSheaf_of_isSheaf (Scheme.fpqcTopology.{u}.over S)
    (Scheme.fpqcTopology.{u}.over S) _
    ((isSheaf_iff_isSheaf_of_type _ _).2
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (yoneda.obj Y)))

/-- A surjective flat morphism of schemes is an epimorphism: two morphisms out of its target
which agree after precomposition with it are equal. -/
theorem eq_of_comp_eq_of_surjective_of_flat {X Y Z : Scheme.{u}} (p : X ⟶ Y)
    [Flat p] [Surjective p] {ψ ψ' : Y ⟶ Z} (h : p ≫ ψ = p ≫ ψ') : ψ = ψ' :=
  have : Epi p := Flat.epi_of_flat_of_surjective p
  (cancel_epi p).1 h

/-- For `f : T ⟶ S` surjective and flat, the base-change functor `Over S ⥤ Over T` is
faithful. -/
theorem faithful_overPullback (f : T ⟶ S) [Flat f] [Surjective f] :
    (Over.pullback f).Faithful := by
  have : ∀ (Z : Scheme.{u}) (g : Z ⟶ S), Epi (pullback.fst g f) :=
    fun _ g ↦ Flat.epi_of_flat_of_surjective (pullback.fst g f)
  infer_instance

/-- Two morphisms `X ⟶ Y` out of a scheme `a : X ⟶ S` over `S` are equal as soon as they agree
after composition with the projection `X ×_S T ⟶ X`, for a surjective flat `f : T ⟶ S`. -/
theorem eq_of_pullbackFst_comp_eq (f : T ⟶ S) [Flat f] [Surjective f] {X Y : Scheme.{u}}
    (a : X ⟶ S) {ψ ψ' : X ⟶ Y} (h : pullback.fst a f ≫ ψ = pullback.fst a f ≫ ψ') :
    ψ = ψ' :=
  eq_of_comp_eq_of_surjective_of_flat (pullback.fst a f) h

/-- If `p : X' ⟶ X` is surjective, flat and quasi-compact and `g : X' ⟶ Z` has equal
restrictions along the two projections of `X' ×_X X'`, then `g` factors through `p`. -/
theorem exists_desc_of_surjective_flat_quasiCompact' {X' X Z : Scheme.{u}} (p : X' ⟶ X)
    [Flat p] [Surjective p] [QuasiCompact p] (g : X' ⟶ Z)
    (hg : pullback.fst p p ≫ g = pullback.snd p p ≫ g) :
    ∃ ψ : X ⟶ Z, p ≫ ψ = g :=
  have : IsRegularEpi p := (isRegularEpi_iff_effectiveEpi p).mpr inferInstance
  IsRegularEpi.exists_of_isKernelPair p (IsKernelPair.of_hasPullback p) g hg

/-- A morphism of base changes along `f` commutes with the projections to `T`. -/
private theorem overPullback_hom_comp_snd (f : T ⟶ S) {W W' : Over S}
    (ψ₀ : (Over.pullback f).obj W ⟶ (Over.pullback f).obj W') :
    ψ₀.left ≫ pullback.snd W'.hom f = pullback.snd W.hom f := by
  simpa using Over.w ψ₀

/-- A morphism `ψ` of `S`-schemes has base change `ψ₀` along `f : T ⟶ S` exactly when the two
agree after projection to the target over `S`. -/
theorem overPullback_map_eq_iff (f : T ⟶ S) {W W' : Over S} {ψ : W ⟶ W'}
    {ψ₀ : (Over.pullback f).obj W ⟶ (Over.pullback f).obj W'} :
    (Over.pullback f).map ψ = ψ₀ ↔
      pullback.fst W.hom f ≫ ψ.left = ψ₀.left ≫ pullback.fst W'.hom f := by
  constructor
  · rintro rfl
    simp only [Over.pullback_map_left, pullback.lift_fst]
  · intro h
    refine Over.OverMorphism.ext (pullback.hom_ext ?_ ?_)
    · simp only [Over.pullback_map_left, pullback.lift_fst]
      exact h
    · simp only [Over.pullback_map_left, pullback.lift_snd]
      exact (overPullback_hom_comp_snd f ψ₀).symm

/-- Let `f : T ⟶ S` be a surjective, flat, quasi-compact morphism of schemes and let
`a : X ⟶ S` and `b : Y ⟶ S` be schemes over `S`. Let `ψ₀ : X ×_S T ⟶ Y ×_S T` be a morphism
over `T` which is compatible with the canonical descent data, in the sense that the composite
`(X ×_S T) ×_X (X ×_S T) ⟶ X ×_S T ⟶ Y ×_S T ⟶ Y` is the same for both projections. Then there
is exactly one morphism `ψ : X ⟶ Y` over `S` whose base change along `f` is `ψ₀`, that is, whose
composite with the projection `X ×_S T ⟶ X` is that of `ψ₀` with `Y ×_S T ⟶ Y`. -/
@[sga "1 VIII 5.2"]
theorem existsUnique_desc_of_surjective_flat_quasiCompact (f : T ⟶ S)
    [Flat f] [Surjective f] [QuasiCompact f] {X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
    (ψ₀ : pullback a f ⟶ pullback b f)
    (hover : ψ₀ ≫ pullback.snd b f = pullback.snd a f)
    (hcan : pullback.fst (pullback.fst a f) (pullback.fst a f) ≫ ψ₀ ≫ pullback.fst b f =
      pullback.snd (pullback.fst a f) (pullback.fst a f) ≫ ψ₀ ≫ pullback.fst b f) :
    ∃! ψ : X ⟶ Y, ψ ≫ b = a ∧ pullback.fst a f ≫ ψ = ψ₀ ≫ pullback.fst b f := by
  obtain ⟨ψ, hψ⟩ := exists_desc_of_surjective_flat_quasiCompact' (pullback.fst a f)
    (ψ₀ ≫ pullback.fst b f) hcan
  refine ⟨ψ, ⟨eq_of_pullbackFst_comp_eq f a ?_, hψ⟩, ?_⟩
  · rw [← Category.assoc, hψ, Category.assoc, pullback.condition, ← Category.assoc, hover,
      pullback.condition]
  · rintro ψ' ⟨-, hψ'⟩
    exact eq_of_pullbackFst_comp_eq f a (hψ'.trans hψ.symm)

/-- Let `f : T ⟶ S` be surjective, flat and quasi-compact, and let `ψ₀` be a morphism between
the base changes along `f` of two `S`-schemes `W` and `W'` which is compatible with the
canonical descent data (`hcan`). Then `ψ₀` is the image under `CategoryTheory.Over.pullback f`
of exactly one morphism `W ⟶ W'` of `S`-schemes. -/
theorem existsUnique_overPullback_map_eq (f : T ⟶ S)
    [Flat f] [Surjective f] [QuasiCompact f] {W W' : Over S}
    (ψ₀ : (Over.pullback f).obj W ⟶ (Over.pullback f).obj W')
    (hcan : pullback.fst (pullback.fst W.hom f) (pullback.fst W.hom f) ≫
          ψ₀.left ≫ pullback.fst W'.hom f =
        pullback.snd (pullback.fst W.hom f) (pullback.fst W.hom f) ≫
          ψ₀.left ≫ pullback.fst W'.hom f) :
    ∃! ψ : W ⟶ W', (Over.pullback f).map ψ = ψ₀ := by
  obtain ⟨l, ⟨hl, hlfst⟩, -⟩ := existsUnique_desc_of_surjective_flat_quasiCompact f
    W.hom W'.hom ψ₀.left (overPullback_hom_comp_snd f ψ₀) hcan
  have hψ : (Over.pullback f).map (Over.homMk l hl) = ψ₀ :=
    (overPullback_map_eq_iff f).2 (by simpa using hlfst)
  exact ⟨Over.homMk l hl, hψ, fun ψ h ↦ (faithful_overPullback f).map_injective (h.trans hψ.symm)⟩

/-- Let `f : T ⟶ S` be a surjective flat morphism of affine schemes, let `a : X ⟶ S` and
`b : Y ⟶ S` be schemes over `S`, and let `ψ₀ : X ×_S T ⟶ Y ×_S T` be a morphism over `T` which
is compatible with the canonical descent data, as in
`AlgebraicGeometry.existsUnique_desc_of_surjective_flat_quasiCompact`. Then there is exactly one
morphism `ψ : X ⟶ Y` over `S` whose base change along `f` is `ψ₀`. -/
theorem existsUnique_desc_of_surjective_flat_of_isAffine (f : T ⟶ S)
    [IsAffine T] [IsAffine S] [Flat f] [Surjective f]
    {X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
    (ψ₀ : pullback a f ⟶ pullback b f)
    (hover : ψ₀ ≫ pullback.snd b f = pullback.snd a f)
    (hcan : pullback.fst (pullback.fst a f) (pullback.fst a f) ≫ ψ₀ ≫ pullback.fst b f =
      pullback.snd (pullback.fst a f) (pullback.fst a f) ≫ ψ₀ ≫ pullback.fst b f) :
    ∃! ψ : X ⟶ Y, ψ ≫ b = a ∧ pullback.fst a f ≫ ψ = ψ₀ ≫ pullback.fst b f :=
  existsUnique_desc_of_surjective_flat_quasiCompact f a b ψ₀ hover hcan

end AlgebraicGeometry

end
