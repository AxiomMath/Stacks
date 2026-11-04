module

public import StacksFrontier.AlgebraicGeometry.Limits.StageMorphismToFiniteTypeOverZ
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.EtaleSliceAtRationalPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.ResidueFieldFactor

/-!
# Slicing a stage of a smooth limit presentation

Let `Spec(𝒪^∧_{S,s})` be presented as the limit of a cofiltered diagram of affine schemes smooth
over `S`, let `T` be locally of finite type over `Spec ℤ` and let `σ : Spec(𝒪^∧_{S,s}) ⟶ T` be a
morphism. This file carries out, in one step, the last two constructions of the proof of Stacks
Tag 0GDX:

* descend `σ` to a morphism `τ_j : S_j ⟶ T` at a stage of the diagram (Tag 01ZC), and
* cut a slice `V ⊂ S_j` through the image `s_j` of the distinguished point, étale over `S` with
  trivial residue field extension (Tag 057G, in the form of the étale slice through a rational
  point of a smooth morphism).

The outcome is clauses (1) and (3) of Tag 0GDX — the elementary étale neighbourhood `(V, v)` of
`(S, s)` and the morphism `τ : V ⟶ T` with `τ(v) = t` — *together with* the immersion
`i : V ⟶ S_j` which exhibits them, the datum the remaining clauses (2) and (4) are built from: the
scheme `W` of the source is the inverse image in `U_j` of this very `V`.

## Main results

* `AlgebraicGeometry.exists_slice_at_stage`: the slice at a prescribed stage.
* `AlgebraicGeometry.exists_slice_stage_of_smooth_limit`: the stage, the descended morphism, the
  slice and its properties.

## Implementation notes

The point `z` of the limit is taken as data rather than constructed as the closed point of
`Spec(𝒪^∧_{S,s})`, with its image `s` in `S` and the triviality of the residue field extension
`κ(s) → κ(z)` as hypotheses. For the limit presentation of the spectrum of a completed local ring
those two hypotheses hold at the closed point.

That the residue field extension `κ(s) → κ(s_j)` at the stage is trivial — which is what makes the
étale slice available — is read off from the triviality at the limit: the projection to the stage
followed by the structure morphism of the stage *is* the morphism to `S`, so
`AlgebraicGeometry.isIso_residueFieldMap_of_isIso_residueFieldMap_comp` applies.

## References

* [Stacks Project, Tag 0GDX](https://stacks.math.columbia.edu/tag/0GDX)
* [Stacks Project, Tag 057G](https://stacks.math.columbia.edu/tag/057G)
* [Stacks Project, Tag 01ZC](https://stacks.math.columbia.edu/tag/01ZC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **The slice at a prescribed stage.** Let `D` be a cofiltered diagram of affine schemes smooth
over a locally Noetherian `S`, with limit cone `c` whose vertex maps to `S` by `m`, and let `z` be
a point of the vertex lying over `s ∈ S` with trivial residue field extension. Then at *every*
stage `j` there is an immersion `i : V ⟶ D.obj j` through the image of `z` such that `V ⟶ S` is
étale with trivial residue field extension at the distinguished point `v`, and `v` lies over `s`.

The stage is an argument rather than an output because the étale neighbourhood whose inverse image
in `V` produces the scheme `W` of Tag 0GDX only becomes available after passing to a later stage
than the one at which the morphism to `T` is defined. -/
public theorem exists_slice_at_stage
    {S : Scheme.{u}} [IsLocallyNoetherian S] {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (p : D ⟶ (Functor.const I).obj S)
    (c : Cone D) (m : c.pt ⟶ S) (hm : ∀ i, c.π.app i ≫ p.app i = m)
    (hsm : ∀ i, Smooth (p.app i)) (j : I)
    (z : c.pt) (s : S) (hz : m z = s) (hres : IsIso (m.residueFieldMap z)) :
    ∃ (V : Scheme.{u}) (i : V ⟶ D.obj j) (v : V),
      IsImmersion i ∧ i v = c.π.app j z ∧
        Etale (i ≫ p.app j) ∧ IsIso ((i ≫ p.app j).residueFieldMap v) ∧
          (i ≫ p.app j) v = s := by
  have hcomp : IsIso ((c.π.app j ≫ p.app j).residueFieldMap z) := by
    rw [hm j]; exact hres
  have hstage : IsIso ((p.app j).residueFieldMap (c.π.app j z)) :=
    isIso_residueFieldMap_of_isIso_residueFieldMap_comp (c.π.app j) (p.app j) z hcomp
  have hsmj : Smooth (p.app j) := hsm j
  obtain ⟨V, i, v, himm, hiv, het, hresv⟩ :=
    Stacks.AlgebraicGeometry.exists_etale_immersion_of_smooth_of_isIso_residueFieldMap
      (p.app j) (c.π.app j z) hstage
  refine ⟨V, i, v, himm, hiv, het, hresv, ?_⟩
  have h1 : (i ≫ p.app j) v = p.app j (c.π.app j z) := by
    rw [Scheme.Hom.comp_apply, hiv]
  rw [h1, ← Scheme.Hom.comp_apply, hm j]
  exact hz

/-- **The stage, the descended morphism and the slice.** Let `D` be a cofiltered diagram of affine
schemes smooth over a locally Noetherian `S`, with limit cone `c` whose vertex maps to `S` by `m`,
let `T` be locally of finite type over `Spec ℤ`, let `bT : c.pt ⟶ T`, and let `z` be a point of the
vertex lying over `s ∈ S` with trivial residue field extension. Then there are a stage `j`, a
morphism `τ_j : D.obj j ⟶ T` through which `bT` factors, and an immersion `i : V ⟶ D.obj j` through
the image `s_j` of `z` such that `V ⟶ S` is étale with trivial residue field extension at the
distinguished point `v`, that point lies over `s`, and `(i ≫ τ_j)(v) = bT(z)`. -/
public theorem exists_slice_stage_of_smooth_limit
    {S T : Scheme.{u}} [IsLocallyNoetherian S] {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (p : D ⟶ (Functor.const I).obj S)
    (c : Cone D) (hc : IsLimit c) (m : c.pt ⟶ S) (hm : ∀ i, c.π.app i ≫ p.app i = m)
    (haff : ∀ i, IsAffine (D.obj i)) (hsm : ∀ i, Smooth (p.app i))
    (hT : LocallyOfFiniteType (specULiftZIsTerminal.{u}.from T))
    (bT : c.pt ⟶ T) (z : c.pt) (s : S) (hz : m z = s)
    (hres : IsIso (m.residueFieldMap z)) :
    ∃ (j : I) (τj : D.obj j ⟶ T) (V : Scheme.{u}) (i : V ⟶ D.obj j) (v : V),
      IsImmersion i ∧ i v = c.π.app j z ∧
        Etale (i ≫ p.app j) ∧ IsIso ((i ≫ p.app j).residueFieldMap v) ∧
          (i ≫ p.app j) v = s ∧ c.π.app j ≫ τj = bT ∧ (i ≫ τj) v = bT z := by
  obtain ⟨j, τj, hτj, hτjz⟩ :=
    exists_stage_morphism_of_locallyOfFiniteTypeOverZ_apply D p c hc m hm haff hT bT z
  obtain ⟨V, i, v, himm, hiv, het, hresv, hvs⟩ :=
    exists_slice_at_stage D p c m hm hsm j z s hz hres
  refine ⟨j, τj, V, i, v, himm, hiv, het, hresv, hvs, hτj, ?_⟩
  rw [Scheme.Hom.comp_apply, hiv]
  exact hτjz

end AlgebraicGeometry

end
