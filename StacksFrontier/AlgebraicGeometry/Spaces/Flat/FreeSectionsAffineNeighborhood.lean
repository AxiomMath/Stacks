module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.GlobalSectionsCompleteDevissage
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.ExistenceFreeSectionsAlongFibre

/-!
# The conclusion of Stacks 05L1 over an affine elementary étale neighbourhood

Stacks 05L1 produces an elementary étale neighbourhood `(T', t') ⟶ (T, t)` and an affine scheme
over `Spec 𝒪_{T', t'}` with free global sections. The neighbourhood it produces is a common
refinement of finitely many neighbourhoods and carries no finiteness: it need not be
quasi-compact, and so need not be small enough to be an object of a big site. This file shrinks
it to an affine open neighbourhood of its distinguished point, pulling the rest of the conclusion
back along the inclusion by
`AlgebraicGeometry.exists_free_sections_along_fibre_of_neighborhoodHom`.

It also records the fact about points of fibre products that the covering clause of Stacks 0CVW
needs over such a neighbourhood: over a point at which the second leg induces an isomorphism of
residue fields, a point of a fibre product is determined by its two projections.

## Main results

* `AlgebraicGeometry.Scheme.Pullback.eq_of_fst_eq_of_snd_eq_of_isIso_residueFieldMap`: two
  points of `X ×_S Y` with the same projections agree when `Y ⟶ S` is an isomorphism on residue
  fields at their common second projection.
* `AlgebraicGeometry.HasFreeSectionsAlongFibreOver.exists_affine`: the conclusion of Stacks
  05L1 with the elementary étale neighbourhood affine, presented by an étale morphism from an
  affine scheme which is an isomorphism on residue fields at the distinguished point.

## References

* [Stacks Project, Tag 05L1](https://stacks.math.columbia.edu/tag/05L1)
* [Stacks Project, Tag 0CVW](https://stacks.math.columbia.edu/tag/0CVW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **A point of a fibre product is determined by its projections over a point with trivial
residue field extension.** If `z, z'` are points of `X ×_S Y` with the same images in `X` and in
`Y`, and `g : Y ⟶ S` induces an isomorphism of residue fields at their common image in `Y`, then
`z = z'`: the points of `X ×_S Y` over a pair `(x, y)` are the prime ideals of
`κ(x) ⊗_{κ(s)} κ(y)`, which is the field `κ(x)` when `κ(s) ⟶ κ(y)` is an isomorphism. -/
theorem Scheme.Pullback.eq_of_fst_eq_of_snd_eq_of_isIso_residueFieldMap
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (z z' : (pullback f g : Scheme))
    (hfst : pullback.fst f g z = pullback.fst f g z')
    (hsnd : pullback.snd f g z = pullback.snd f g z')
    (hiso : IsIso (g.residueFieldMap (pullback.snd f g z'))) : z = z' := by
  let T := Scheme.Pullback.Triplet.ofPoint z'
  have : IsIso (g.residueFieldMap T.y) := hiso
  have : IsIso ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y) := inferInstance
  have : IsIso T.tensorInl := by
    show IsIso (pushout.inl
      ((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x)
      ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y))
    infer_instance
  apply Scheme.Pullback.carrierEquiv.injective
  apply Scheme.Pullback.carrierEquiv_eq_iff.mpr
  refine ⟨Scheme.Pullback.Triplet.ext hfst hsnd, ?_⟩
  exact (Spec.map T.tensorInl).isOpenEmbedding.injective (Subsingleton.elim _ _)

/-- **Stacks 05L1 over an affine elementary étale neighbourhood.** The conclusion of Stacks 05L1
for `g : Z ⟶ T`, a quasi-coherent module `G` on `Z` and a point `t` of `T`, with its covering
clause read on `Z` itself, can be realized with the elementary étale neighbourhood affine: there
are an étale morphism `σ : W ⟶ T` from an affine scheme and a point `w` of `W` over `t` at which
`σ` is an isomorphism on residue fields, and an affine scheme `Z'` over `Spec 𝒪_{W, w}` with
`c : Z' ⟶ Z`, such that `Z' ⟶ Z ×_T Spec 𝒪_{W, w}` is étale, the fibre `g^{-1}({t})` is the image
of the fibre of `Z'` over the closed point, and `Γ(Z', c^*G)` is a free `𝒪_{W, w}`-module.

The neighbourhood is an affine open neighbourhood of the distinguished point in the one Stacks
05L1 produces, which is again elementary, and the rest of the conclusion is pulled back to it by
`AlgebraicGeometry.exists_free_sections_along_fibre_of_neighborhoodHom`. -/
theorem HasFreeSectionsAlongFibreOver.exists_affine {Z T : Scheme.{u}} {g : Z ⟶ T}
    {G : Z.Modules} [G.IsQuasicoherent] {t : T}
    (h : HasFreeSectionsAlongFibreOver g G t id (g ⁻¹' {t})) :
    ∃ (W : Scheme.{u}) (σ : W ⟶ T) (wpt : W),
      IsAffine W ∧ Etale σ ∧ σ wpt = t ∧ IsIso (σ.residueFieldMap wpt) ∧
      ∃ (Z' : Scheme.{u}) (q : Z' ⟶ Spec (.of (W.presheaf.stalk wpt))) (c : Z' ⟶ Z)
        (hcomm : c ≫ g = q ≫ W.fromSpecStalk wpt ≫ σ),
        Etale (pullback.lift c q hcomm) ∧
        g ⁻¹' {t} = c '' (q ⁻¹' {IsLocalRing.closedPoint _}) ∧ IsAffine Z' ∧
        letI : Module (W.presheaf.stalk wpt) Γ((Scheme.Modules.pullback c).obj G, ⊤) :=
          Module.compHom _ ((Scheme.ΓSpecIso (.of (W.presheaf.stalk wpt))).inv ≫ q.appTop).hom
        Module.Free (W.presheaf.stalk wpt) Γ((Scheme.Modules.pullback c).obj G, ⊤) := by
  obtain ⟨T', hT', Z', q, c, hcomm, het, hcov, haff, hfree⟩ := h
  obtain ⟨W, hWaff, hpW, -⟩ :=
    exists_isAffineOpen_mem_and_subset (x := T'.point) (U := ⊤) trivial
  let N := T'.restrictOpen W hpW
  let hN : N ⟶ T' := ⟨W.ι, rfl, rfl⟩
  obtain ⟨Z'', q', c', hcomm', het', himg, haff', hfree'⟩ :=
    exists_free_sections_along_fibre_of_neighborhoodHom g G hN q c hcomm het hfree
  refine ⟨N.scheme, N.toBase, N.point, hWaff, inferInstance, N.map_point,
    isIso_residueFieldMap_opens_comp T' hT' W ⟨T'.point, hpW⟩ rfl,
    Z'', q', c', hcomm', het', ?_, haff', hfree'⟩
  rw [himg, hcov, Set.image_id]

end AlgebraicGeometry

end
