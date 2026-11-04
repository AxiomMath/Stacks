module

public import StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhoodFlatness
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.AffineBaseChange
public import StacksFrontier.AlgebraicGeometry.OneDimensionalLocal.Basic
public import StacksFrontier.AlgebraicGeometry.StalkFiniteType.FinitePresentation

/-!
# Finite presentation of the stalk of a module flat over the base

Stacks 05I7: if `f : X ⟶ S` is locally of finite presentation and `F` is a finite type
quasi-coherent `𝒪_X`-module which is flat over `S` at `x`, then the stalk `F_x` is a finitely
presented `𝒪_{X,x}`-module.

The source proves it from Stacks 05I5 in two steps. Stacks 05I5 produces an elementary étale
neighbourhood `U` of `(S, f x)` and an open `V` of `X ×_S Spec 𝒪_{U,u}` containing the unique
point `v` over `x`, on which the pullback of `F` is of finite presentation. The composite
`g : V ⟶ X ×_S Spec 𝒪_{U,u} ⟶ X` is flat — `Spec 𝒪_{U,u} ⟶ U` is flat because it is a
localization, `U ⟶ S` is étale, flatness is stable under base change, and an open immersion is
flat — so the stalk map `𝒪_{X,x} → 𝒪_{V,v}` is a flat local homomorphism of local rings. The
pullback of `F` along `g` is finitely presented, hence has finitely presented stalk at `v`
(`Stacks.StalkFiniteType.finitePresentation_stalk`), and that stalk is the base change of `F_x`
(Stacks 0098), so finite presentation descends (Stacks 03C4 (2) and 00HR).

Both steps are available: the second is
`Stacks.StalkFiniteType.finitePresentation_stalk_of_flat`, and Stacks 05I5 is
`AlgebraicGeometry.existsElementaryEtaleNeighborhoodFinitePresentationFlatOver`, proved in
`StacksFrontier/AlgebraicGeometry/Etale/ElementaryNeighborhoodFlatness.lean`. So
`Stacks.Flatness.finitePresentation_stalk_of_isFlatOverAt` below is Stacks 05I7 outright and
carries the tag.

## Main results

* `Stacks.Flatness.finitePresentation_stalk_of_isFlatOverAt`: **Stacks 05I7.**
  A finite type quasi-coherent module which is flat over the base at a point of a morphism
  locally of finite presentation has a finitely presented stalk there.
* `Stacks.Flatness.flat_fromSpecStalk_comp_toBase`: the morphism
  `Spec 𝒪_{U,u} ⟶ U ⟶ S` attached to an étale neighbourhood is flat, which is what makes the
  base change in Stacks 05I5 a flat morphism onto `X`.

## Implementation notes

The hypothesis of flatness over the base at the point, `AlgebraicGeometry.IsFlatOverAt`, is used
only to feed Stacks 05I5; the descent half needs no flatness of the module at all, only flatness
of the morphism `g`. That is why the statement below passes `hflat` straight through.

The point `v` produced by Stacks 05I5 lies in the open `V`, and the fibre condition is an
equality of sets, `pullback.fst f b ⁻¹' {x} = {V.ι v}`; membership of `V.ι v` in the right-hand
singleton is what gives `g v = x`, and the conclusion is transported along that equality of
points with `congrArg`, since the module structure on a stalk is a function of the point.

## References

* [Stacks Project, Tag 05I7](https://stacks.math.columbia.edu/tag/05I7)
* [Stacks Project, Tag 05I5](https://stacks.math.columbia.edu/tag/05I5)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 03C4](https://stacks.math.columbia.edu/tag/03C4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Flatness

/-- The morphism `Spec 𝒪_{U,u} ⟶ S` attached to an étale neighbourhood `U` of a point of `S` is
flat: it is `Spec` of a localization followed by an étale, hence flat, morphism. -/
theorem flat_fromSpecStalk_comp_toBase {S : Scheme.{u}} {s : S} (U : EtaleNeighborhood S s) :
    Flat (U.scheme.fromSpecStalk U.point ≫ U.toBase) :=
  have : Flat (U.scheme.fromSpecStalk U.point) := flat_fromSpecStalk U.scheme U.point
  inferInstance

/-- **Stacks Project, Tag 05I7, from Stacks Project, Tag 05I5.** Let `f : X ⟶ S` be locally of
finite presentation and let `F` be a finite type quasi-coherent `𝒪_X`-module. If `F` is flat over
`S` at `x`, then the stalk `F_x` is a finitely presented `𝒪_{X,x}`-module.

Stacks 05I5 is `AlgebraicGeometry.existsElementaryEtaleNeighborhoodFinitePresentationFlatOver`.
The neighbourhood it produces maps to `X` by a flat morphism, the pullback of `F` to it is
finitely presented, so its stalk is finitely presented
(`Stacks.StalkFiniteType.finitePresentation_stalk`), and finite presentation descends along the
flat local homomorphism of local rings that the stalk map is
(`Stacks.StalkFiniteType.finitePresentation_stalk_of_flat`). -/
@[stacks 05I7]
theorem finitePresentation_stalk_of_isFlatOverAt
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f] (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] (x : X)
    (hflat : IsFlatOverAt f.toLRSHom.toShHom F x) :
    Module.FinitePresentation (ToType (X.presheaf.stalk x))
      (ToType (TopCat.Presheaf.stalk F.val.presheaf x)) := by
  have h05I5 : ExistsElementaryEtaleNeighborhoodFinitePresentationFlatOver.{u} :=
    @existsElementaryEtaleNeighborhoodFinitePresentationFlatOver.{u}
  obtain ⟨U, -, V, v, hfibre, hfp, -⟩ := h05I5 f F x hflat
  have : Flat (U.scheme.fromSpecStalk U.point ≫ U.toBase) := flat_fromSpecStalk_comp_toBase U
  set b : Spec (U.scheme.presheaf.stalk U.point) ⟶ S :=
    U.scheme.fromSpecStalk U.point ≫ U.toBase with hb
  set g : V.toScheme ⟶ X := V.ι ≫ pullback.fst f b with hg
  have : Flat g := inferInstance
  have hgv : g v = x := by
    have hv : V.ι v ∈ (pullback.fst f b) ⁻¹' {x} := by rw [hfibre]; rfl
    exact hv
  have : ((Scheme.Modules.pullback g).obj F).IsFinitePresentation := hfp
  have hstalk := Stacks.StalkFiniteType.finitePresentation_stalk
    ((Scheme.Modules.pullback g).obj F) v
  have hdesc := Stacks.StalkFiniteType.finitePresentation_stalk_of_flat g F v hstalk
  exact Eq.mp (congrArg (fun p : X => Module.FinitePresentation (ToType (X.presheaf.stalk p))
    (ToType (TopCat.Presheaf.stalk F.val.presheaf p))) hgv) hdesc

end Stacks.Flatness

end
