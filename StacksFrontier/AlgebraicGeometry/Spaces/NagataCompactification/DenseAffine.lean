module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleEnlargementOfOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PointsOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.NagataCompactification.ZariskiMainTheorem
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase

/-!
# Compactifying affine schemes over a base of finite type over `Spec ℤ`

Let `Y` be an algebraic space over `S` which is quasi-compact, quasi-separated and of finite
type over `Spec ℤ`. An affine scheme `V` with a morphism `v : V ⟶ Y` locally of finite type
is then locally of finite type over `S`, so it immerses into a projective space over `S`, and
`V` has a compactification over `Y`. If moreover `X` is a Noetherian algebraic space locally of
finite type over `Y`, it has a dense open affine subspace (Stacks 06NH, 0BA8, 01ZV), which
therefore has a compactification over `Y`. This is the start of the Noetherian induction in the
proof of Nagata's compactification theorem for algebraic spaces, and the same statement
compactifies the affine étale chart which enlarges the open subspace at each step of it.

## Main results

* `AlgebraicGeometry.Space.isLocallyOfFiniteType_of_isFiniteType_viewOverIntegers`: an
  algebraic space of finite type over `Spec ℤ` is locally of finite type over `S`.
* `AlgebraicGeometry.Space.hasCompactification_yoneda_of_isLocallyOfFiniteType`: an affine
  scheme locally of finite type over `Y` has a compactification over `Y`.
* `AlgebraicGeometry.Space.exists_dense_affine_openImmersion_hasCompactification`: a Noetherian
  algebraic space locally of finite type over `Y` has a dense open affine subspace with a
  compactification over `Y`.

## Implementation notes

The source compactifies the affine scheme over `Spec ℤ` (Stacks 0F41) and then passes to `Y`
through `Y ×_{Spec ℤ} Ȳ`. Algebraic spaces here are presheaves on the big fppf site of the base
scheme `S`, over which `Spec ℤ` is not available, so the projective space `ℙⁿ_S` over `S` takes
the place of the compactification over `Spec ℤ`: `V` immerses into it, and the morphism
`V ⟶ Y ×_S ℙⁿ_S` is a quasi-compact monomorphism locally of finite type into a space proper over
`Y`, to which Zariski's main theorem (Stacks 082K) applies; that theorem rests on Stacks 09YA.

Being of finite type over `Spec ℤ` is read, as in
`AlgebraicGeometry.Space.NoetherianApproximation`, on the view of `Y` over the terminal scheme.

## References

* [Stacks Project, Tag 0F4D](https://stacks.math.columbia.edu/tag/0F4D)
* [Stacks Project, Tag 06NH](https://stacks.math.columbia.edu/tag/06NH)
* [Stacks Project, Tag 082K](https://stacks.math.columbia.edu/tag/082K)
* [Stacks Project, Tag 09YA](https://stacks.math.columbia.edu/tag/09YA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **An algebraic space of finite type over `Spec ℤ` is locally of finite type over `S`.** The
view over `Spec ℤ` of the structure morphism to `S` is followed by a morphism to the terminal
presheaf with locally-of-finite-type composite, so it is locally of finite type, and local
finite type is unchanged by the view. -/
theorem isLocallyOfFiniteType_of_isFiniteType_viewOverIntegers (hZ : B.Contains (⊤_ Scheme.{u}))
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (h : IsFiniteType B (⊤_ Scheme.{u}) hZ (terminal.from (viewOverIntegers B S hS hZ Y)))
    (t : Y ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hS)))) : IsLocallyOfFiniteType B S hS t := by
  let k : B.obj hS ⟶ B.obj hZ := ⟨terminal.from S⟩
  rw [← isLocallyOfFiniteType_relocalize_iff B S hS (⊤_ Scheme.{u}) hZ k t]
  refine isLocallyOfFiniteType_of_comp B _ hZ (isAlgebraicSpace_viewOver B S _ hS hZ k Y hY)
    (isAlgebraicSpace_viewOver B S _ hS hZ k _ (isAlgebraicSpace_yoneda B S hS _))
    (isAlgebraicSpace_terminal B _ hZ) _ (terminal.from _) ?_
  rw [terminal.hom_ext ((OverShriek.relocalizePresheafFunctor k).map t ≫ terminal.from _)
    (terminal.from (viewOverIntegers B S hS hZ Y))]
  exact h.1

/-- **An affine scheme locally of finite type over a base of finite type over `Spec ℤ` is
compactifiable over it.** Let `Y` be a quasi-compact and quasi-separated algebraic space of finite
type over `Spec ℤ`, and let `v : V ⟶ Y` be a morphism locally of finite type from an affine
scheme. Then `v` has a compactification. -/
theorem hasCompactification_yoneda_of_isLocallyOfFiniteType (hZ : B.Contains (⊤_ Scheme.{u}))
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hYqc : IsQuasiCompactSpace B S hS Y) (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y)
    (hYft : IsFiniteType B (⊤_ Scheme.{u}) hZ (terminal.from (viewOverIntegers B S hS hZ Y)))
    (V : BigFppfOver B S hS) (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (v : yoneda.obj V ⟶ Y) (hv : IsLocallyOfFiniteType B S hS v) :
    HasCompactification B S hS v := by
  refine hasCompactification_yoneda_of_isAffine hZ hY hYqc hYqs V hV ?_ v
  let T : BigFppfOver B S hS := Over.mk (𝟙 (B.obj hS))
  have hT : IsTerminal (yoneda.obj T) :=
    (Over.mkIdTerminal (X := B.obj hS)).isTerminalObj yoneda _
  let s : V ⟶ T := Over.homMk V.hom (Category.comp_id _)
  refine (isLocallyOfFiniteType_yoneda_map_iff B S hS s).1 ?_
  rw [← hT.hom_ext (v ≫ hT.from Y) (yoneda.map s)]
  exact isLocallyOfFiniteType_comp' B S hS v (hT.from Y) hY (isAlgebraicSpace_yoneda B S hS T) hv
    (isLocallyOfFiniteType_of_isFiniteType_viewOverIntegers hZ hY hYft (hT.from Y))

attribute [local instance] pointTopology in
/-- **A dense open affine subspace with a compactification.** Let `Y` be a quasi-compact and
quasi-separated algebraic space of finite type over `Spec ℤ` and let `f : X ⟶ Y` be locally of
finite type, with `X` Noetherian. Then `X` has a dense open subspace which is an affine scheme
and has a compactification over `Y`.

The dense open affine is Stacks 06NH, 0BA8 and 01ZV,
`AlgebraicGeometry.Space.exists_dense_affine_openImmersion_self`. -/
theorem exists_dense_affine_openImmersion_hasCompactification (hZ : B.Contains (⊤_ Scheme.{u}))
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hXN : IsNoetherian B S hS hZ X) (hY : IsAlgebraicSpace B S hS Y)
    (hYqc : IsQuasiCompactSpace B S hS Y) (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y)
    (hYft : IsFiniteType B (⊤_ Scheme.{u}) hZ (terminal.from (viewOverIntegers B S hS hZ Y)))
    (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f) :
    ∃ (D : BigFppfOver B S hS) (u : yoneda.obj D ⟶ X),
      IsAffine ((BigFppfOver.toScheme B S hS).obj D) ∧ IsOpenImmersion B S hS u ∧
        DenseRange (pointsMap B S hS (yoneda.obj D) u) ∧ HasCompactification B S hS (u ≫ f) := by
  obtain ⟨D, u, hD, hu, hdense⟩ := exists_dense_affine_openImmersion_self B S hS hZ X hX hXN
  exact ⟨D, u, hD, hu, hdense, hasCompactification_yoneda_of_isLocallyOfFiniteType hZ hY hYqc hYqs
    hYft D hD (u ≫ f) (isLocallyOfFiniteType_comp' B S hS u f hX hY
      (isLocallyOfFiniteType_of_isImmersion B S hS u (isImmersion_of_isOpenImmersion B S hS hu))
      hf)⟩

end AlgebraicGeometry.Space

end
