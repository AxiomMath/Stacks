module

public import StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.ProjectiveSectionsAlongFibre
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.EtaleLocalizationQuasiFinite.FiniteNeighborhood

/-!
# Tag 05KW: the image of `X' ⟶ X ×_S S'` contains the fibre over `s'`

Stacks Tag 05KW says: for `f : X ⟶ S` of finite presentation, `F` a quasi-coherent
`𝒪_X`-module of finite presentation and `s ∈ S` such that `F` is flat over `S` at every point of
the fibre `X_s`, there are an elementary étale neighbourhood `(S', s') ⟶ (S, s)` and a
commutative square
```
  X ← X'
  ↓    ↓
  S ← S'
```
whose upper arrow `g : X' ⟶ X` is étale, such that the image of `X' ⟶ X ×_S S'` contains the
fibre `(X ×_S S')_{s'}`, with `X'` and `S'` affine, and with `Γ(X', g^*F)` a projective
`Γ(S', 𝒪_{S'})`-module.

## Main results

* `AlgebraicGeometry.injOn_pullback_fst_of_isElementary`: over the distinguished point of an
  elementary étale neighbourhood the projection `X ×_S S' ⟶ X` is injective.
* `AlgebraicGeometry.exists_elementaryEtaleNeighborhood_projective_sections_image_contains_fibre`
  is Tag 05KW.

## Implementation notes

The fibre `(X ×_S S')_{s'}` is the set of points of `X ×_S S'` whose second projection is `s'`.
The construction of `AlgebraicGeometry.exists_elementary_pointed_projective_cover` gives that each
point of `X_s` is hit by a point of `X'` lying over `s'`. Since `(S', s')` is elementary, the
projection identifies `(X ×_S S')_{s'}` with `X_s`
(`AlgebraicGeometry.fiberIsoOfIsElementary`), and this gives the containment of the fibre in the
image of `X' ⟶ X ×_S S'`.

## References

* [Stacks Project, Tag 05KW](https://stacks.math.columbia.edu/tag/05KW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Over the distinguished point of an elementary étale neighbourhood `(S', s')` of `(S, s)`, the
projection `X ×_S S' ⟶ X` is injective: the fibre `(X ×_S S')_{s'}` is identified with `X_s`
compatibly with the inclusions into `X ×_S S'` and `X`. -/
theorem injOn_pullback_fst_of_isElementary {X S : Scheme.{u}} (f : X ⟶ S) {s : S}
    (U : EtaleNeighborhood S s) (hU : U.IsElementary) :
    Set.InjOn (pullback.fst f U.toBase) (pullback.snd f U.toBase ⁻¹' {U.point}) := by
  intro w hw w' hw' hww'
  let e := fiberIsoOfIsElementary f s U hU
  let a := ((pullback.snd f U.toBase).fiberHomeo U.point).symm ⟨w, hw⟩
  let a' := ((pullback.snd f U.toBase).fiberHomeo U.point).symm ⟨w', hw'⟩
  have ha : (pullback.snd f U.toBase).fiberι U.point a = w :=
    (pullback.snd f U.toBase).fiberι_fiberHomeo_symm U.point ⟨w, hw⟩
  have ha' : (pullback.snd f U.toBase).fiberι U.point a' = w' :=
    (pullback.snd f U.toBase).fiberι_fiberHomeo_symm U.point ⟨w', hw'⟩
  have hcomp (b : (pullback.snd f U.toBase).fiber U.point) :
      f.fiberι s (e.hom b) =
        pullback.fst f U.toBase ((pullback.snd f U.toBase).fiberι U.point b) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, fiberIsoOfIsElementary_hom_fiberι]
  have hinj : Function.Injective (f.fiberι s) := (f.fiberι s).isEmbedding.injective
  have heq : e.hom a = e.hom a' := hinj (by rw [hcomp, hcomp, ha, ha', hww'])
  have haa' : a = a' := by
    have := congrArg e.inv heq
    rwa [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, e.hom_inv_id] at this
  rw [← ha, ← ha', haa']

/-- **Stacks Project, Tag 05KW.** Let `f : X ⟶ S` be of finite presentation, let `F` be a
quasi-coherent `𝒪_X`-module of finite presentation and let `s ∈ S` be such that `F` is flat over
`S` at every point of the fibre `X_s`. Then there is an elementary étale neighbourhood
`(S', s') ⟶ (S, s)` and a commutative square
```
  X ←g— X'
  ↓      ↓ h
  S ←—— S'
```
such that `g` is étale, the image of the induced morphism `X' ⟶ X ×_S S'` contains the fibre
`(X ×_S S')_{s'}`, the schemes `X'` and `S'` are affine, and `Γ(X', g^*F)` is a projective
`Γ(S', 𝒪_{S'})`-module.

The fibre `(X ×_S S')_{s'}` is the set of points of `X ×_S S'` whose second projection is `s'`.
The statement also records the equivalent pointwise form: every point of `X_s` is `g` of a point
of `X'` lying over `s'`. The `Γ(S', 𝒪_{S'})`-module structure on `Γ(X', g^*F)` is restriction of
scalars along the map on global sections induced by `h`. -/
@[stacks 05KW]
theorem exists_elementaryEtaleNeighborhood_projective_sections_image_contains_fibre
    {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (s : S)
    (hf : FinitePresentation f)
    [F.IsQuasicoherent] [F.IsFinitePresentation]
    (hflat : ∀ x : f.fiber s,
      IsFlatOverAt f.toLRSHom.toShHom F (f.fiberι s x)) :
    ∃ (U : EtaleNeighborhood S s) (X' : Scheme.{u})
      (h : X' ⟶ U.scheme) (g : X' ⟶ X) (hc : g ≫ f = h ≫ U.toBase),
      U.IsElementary ∧ IsAffine U.scheme ∧ IsAffine X' ∧ Etale g ∧
      pullback.snd f U.toBase ⁻¹' {U.point} ⊆ Set.range (pullback.lift g h hc) ∧
      (∀ x ∈ f ⁻¹' {s}, ∃ y : X', g y = x ∧ h y = U.point) ∧
      (let N := Γ((Scheme.Modules.pullback g).obj F, ⊤)
       letI : Module Γ(U.scheme, ⊤) N := Module.compHom N h.appTop.hom
       Module.Projective Γ(U.scheme, ⊤) N) := by
  have hID : ExistsElementaryEtaleNeighborhoodProjectiveSections.{u} := by
    intro X S f _ F _ _ x hflat
    exact exists_elementaryEtaleNeighborhood_projective_sections_of_isFlatOverAt f F x hflat
  obtain ⟨U, hU, hUa, X', hX'a, h, g, hg, hcomm, hcover, hproj⟩ :=
    exists_elementary_pointed_projective_cover hID f F s hf hflat
  have hpt (x : X) (hx : x ∈ f ⁻¹' {s}) : ∃ y : X', g y = x ∧ h y = U.point := by
    obtain ⟨y, hy, hyU⟩ := hcover ((f.fiberHomeo s).symm ⟨x, hx⟩)
    exact ⟨y, by rw [hy, f.fiberι_fiberHomeo_symm], hyU⟩
  refine ⟨U, X', h, g, hcomm.symm, hU, hUa, hX'a, hg, fun w hw => ?_, hpt, hproj⟩
  have hfw : f (pullback.fst f U.toBase w) = s := by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply,
      Set.mem_singleton_iff.mp hw, U.map_point]
  obtain ⟨y, hy, hyU⟩ := hpt _ hfw
  refine ⟨y, injOn_pullback_fst_of_isElementary f U hU ?_ hw ?_⟩
  · change (pullback.lift g h hcomm.symm ≫ pullback.snd f U.toBase) y = U.point
    rw [pullback.lift_snd]
    exact hyU
  · change (pullback.lift g h hcomm.symm ≫ pullback.fst f U.toBase) y = _
    rw [pullback.lift_fst]
    exact hy

end AlgebraicGeometry

end
