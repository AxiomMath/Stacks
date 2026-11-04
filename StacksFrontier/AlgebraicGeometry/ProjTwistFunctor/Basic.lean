module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwist
public import StacksFrontier.AlgebraicGeometry.ProjTwistFunctor.TensorExact

/-!
# The twist on `Proj 𝒜` as a functor

`AlgebraicGeometry.ProjectiveSpectrum.Proj.twistSheafOfModules 𝒜 ℱ d` is the twist `ℱ(d)` of an
`𝒪_{Proj 𝒜}`-module by the `d`-th twisting sheaf, defined as the tensor product sheaf
`ℱ ⊗_{𝒪} 𝒪(d)`. As defined it is a *function* of the module, with no action on morphisms; this
file promotes it to a functor

`Stacks.AlgebraicGeometry.ProjTwistFunctor.twistFunctor 𝒜 d : Mod(𝒪_{Proj 𝒜}) ⥤ Mod(𝒪_{Proj 𝒜})`

whose object map is `twistSheafOfModules 𝒜 · d` **on the nose**, and records its exactness.

That functor, together with a `CategoryTheory.Functor.PreservesZeroMorphisms` instance and
preservation of short exact sequences, is the input that
`Stacks.HighTwistDevissage.exists_isZero_hgroup_twist_of_descending_devissage` names as missing;
`StacksFrontier/AlgebraicGeometry/ProjTwistFunctor/Devissage.lean` instantiates the dévissage
engine with it.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjTwistFunctor.projRingSheaf`: the sheaf of rings `𝒪_{Proj 𝒜}`
  over which the twists are modules, in the spelling
  `AlgebraicGeometry.ProjectiveSpectrum.Proj.twistSheafOfModules` uses.
* `Stacks.AlgebraicGeometry.ProjTwistFunctor.twistFunctor`: the `d`-th twist as an endofunctor
  of `𝒪_{Proj 𝒜}`-modules.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistFunctor.twistFunctor_obj`: the functor's object map is
  `AlgebraicGeometry.ProjectiveSpectrum.Proj.twistSheafOfModules`, by `rfl`.
* `Stacks.AlgebraicGeometry.ProjTwistFunctor.additive_twistFunctor` and
  `Stacks.AlgebraicGeometry.ProjTwistFunctor.preservesZeroMorphisms_twistFunctor`: the twist is
  additive, hence preserves zero morphisms. Instances, with no hypothesis on `𝒜` beyond
  `GradedRing`.
* `Stacks.AlgebraicGeometry.ProjTwistFunctor.preservesFiniteColimits_twistFunctor`: the twist is
  right exact, again unconditionally.
* `Stacks.AlgebraicGeometry.ProjTwistFunctor.exact_map_and_epi_of_shortExact`: the twist of a
  short exact sequence is exact with epimorphic second map — everything except the
  monomorphism, unconditionally.
* `ProjTwistFunctor.shortExact_map_twistFunctor_of_preservesMonomorphisms`:
  the twist of a short exact sequence is short exact as soon as the twist preserves one
  monomorphism, i.e. as soon as `𝒪(d)` is flat.
* `Stacks.AlgebraicGeometry.ProjTwistFunctor.shortExact_map_twistFunctor` and
  `Stacks.AlgebraicGeometry.ProjTwistFunctor.isEquivalence_twistFunctor`: the same from
  invertibility of `𝒪(d)`.

## Implementation notes

**The functor is not built by hand.** `twistSheafOfModules 𝒜 ℱ d` is the bifunctor
`Stacks.SheafOfModules.Tensor.sheafTensor` evaluated at `ℱ` and the twisting sheaf, and its flip
evaluated at the twisting sheaf is already that tensor product as a functor in its first
variable. The two agree by `rfl`, so `twistFunctor_obj` needs no transport and the dévissage
engine can be instantiated with hypotheses phrased in `twistSheafOfModules` directly. Building
the functor by hand instead would have produced a second notion of the twist, with a bridge
isomorphism between them and every downstream statement having to choose a side.

**Why invertibility of `𝒪(d)` is a hypothesis and not a theorem.** For a graded ring that is
not generated in degree one, `𝒪_{Proj 𝒜}(d)` is genuinely not invertible, so short exactness of
the twist cannot be unconditional. What the repository has towards discharging the hypothesis is
`Stacks.AlgebraicGeometry.CommonDegreeTwist.isInvertible_restrict_twistingSheaf_mul_degree`,
which gives invertibility of the twist *restricted along an open immersion* `Y.ι` for an open
`Y` carrying a cover by standard opens of a common degree; transporting that to `Y = ⊤` is the
step not taken here.

**Where `preservesFiniteColimits_twistFunctor` gets `Sheaf J CommRingCat`.** Right exactness is
stated in `StacksFrontier/AlgebraicGeometry/ProjTwistFunctor/TensorExact.lean` for a sheaf of
*commutative* rings rather than for a presheaf with the sheaf condition on its `RingCat`
composite, because [Stacks, Tag 05NB] is. On `Proj` that costs nothing:
`AlgebraicGeometry.ProjectiveSpectrum.Proj.structureSheaf 𝒜` is already a
`CategoryTheory.Sheaf` of commutative rings, and `projRingSheaf` is its image under
`CategoryTheory.sheafCompose`.

No tag attribute is attached: Tag 01MN is the twist itself and already carries its attribute at
`AlgebraicGeometry.ProjectiveSpectrum.Proj.twistSheafOfModules`; the functoriality and exactness
recorded here are the statement of no tag.

## References

* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 05NB](https://stacks.math.columbia.edu/tag/05NB)
* [Stacks Project, Tag 05ND](https://stacks.math.columbia.edu/tag/05ND)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u w

namespace Stacks.AlgebraicGeometry.ProjTwistFunctor

variable {S : Type u} [CommRing S] {σ : Type w} [SetLike σ S] [AddSubgroupClass σ S]

/-- The sheaf of rings `𝒪_{Proj 𝒜}`: the structure sheaf of `Proj 𝒜` with its commutativity
forgotten, which is the ring sheaf over which
`AlgebraicGeometry.ProjectiveSpectrum.Proj.twistSheafOfModules` takes its modules. -/
abbrev projRingSheaf (𝒜 : ℕ → σ) [GradedRing 𝒜] :
    Sheaf (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒜)) RingCat.{u} :=
  (sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒜))
    (forget₂ CommRingCat.{u} RingCat.{u})).obj
    (ProjectiveSpectrum.Proj.structureSheaf 𝒜)

/-- **The `d`-th twist on `Proj 𝒜` as a functor.** On objects it is
`AlgebraicGeometry.ProjectiveSpectrum.Proj.twistSheafOfModules 𝒜 · d`, by `rfl`
(`twistFunctor_obj`); on morphisms it is the sheafification of the objectwise tensor product
with the identity of the `d`-th twisting sheaf. -/
noncomputable def twistFunctor (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℤ) :
    SheafOfModules.{u} (projRingSheaf 𝒜) ⥤ SheafOfModules.{u} (projRingSheaf 𝒜) :=
  (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    (ProjectiveSpectrum.Proj.structureSheaf 𝒜)).flip.obj (twistingSheaf 𝒜 d)

/-- The twist functor does on objects exactly what the twist does. -/
theorem twistFunctor_obj (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℤ)
    (F : SheafOfModules.{u} (projRingSheaf 𝒜)) :
    (twistFunctor 𝒜 d).obj F = twistSheafOfModules 𝒜 F d := rfl

/-- The twist is an additive functor. -/
instance additive_twistFunctor (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℤ) :
    (twistFunctor 𝒜 d).Additive :=
  Stacks.ProjTwistFunctor.additive_tensorRightFunctor
    (ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj (projRingSheaf 𝒜).property
    (twistingSheaf 𝒜 d)

/-- The twist preserves zero morphisms. This is what makes
`CategoryTheory.ShortComplex.map` applicable to the twist functor, and hence what makes the
statements below about the twist of a short exact sequence well formed. -/
instance preservesZeroMorphisms_twistFunctor (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℤ) :
    (twistFunctor 𝒜 d).PreservesZeroMorphisms :=
  inferInstance

/-- **The twist is right exact.** No hypothesis on `𝒜` or `d`. -/
theorem preservesFiniteColimits_twistFunctor (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℤ) :
    PreservesFiniteColimits (twistFunctor 𝒜 d) :=
  Stacks.ProjTwistFunctor.preservesFiniteColimits_tensorRightFunctor
    (ProjectiveSpectrum.Proj.structureSheaf 𝒜) (projRingSheaf 𝒜).property
    (twistingSheaf 𝒜 d)

/-- The twist of a short exact sequence is exact and its second map is an epimorphism, with no
hypothesis on `𝒜` or `d`: all that short exactness additionally asks is that the first map stay
a monomorphism. -/
theorem exact_map_and_epi_of_shortExact (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℤ)
    {T : ShortComplex (SheafOfModules.{u} (projRingSheaf 𝒜))} (hT : T.ShortExact) :
    (T.map (twistFunctor 𝒜 d)).Exact ∧ Epi ((twistFunctor 𝒜 d).map T.g) :=
  Stacks.ProjTwistFunctor.exact_map_and_epi_of_shortExact
    (ProjectiveSpectrum.Proj.structureSheaf 𝒜) (projRingSheaf 𝒜).property
    (twistingSheaf 𝒜 d) hT

/-- **The twist by a flat twisting sheaf is exact.** Right exactness is unconditional, so the
only hypothesis is that the twist preserves monomorphisms. -/
theorem shortExact_map_twistFunctor_of_preservesMonomorphisms
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℤ) [h : (twistFunctor 𝒜 d).PreservesMonomorphisms]
    {T : ShortComplex (SheafOfModules.{u} (projRingSheaf 𝒜))} (hT : T.ShortExact) :
    (T.map (twistFunctor 𝒜 d)).ShortExact := by
  let : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨(ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj, Presheaf.isSheaf_of_isSheaf_comp _ _
        (forget₂ CommRingCat RingCat) (projRingSheaf 𝒜).property⟩).flip.obj
          (twistingSheaf 𝒜 d)).PreservesMonomorphisms := h
  exact Stacks.ProjTwistFunctor.shortExact_map_tensorRightFunctor_of_preservesMonomorphisms
    (ProjectiveSpectrum.Proj.structureSheaf 𝒜) (projRingSheaf 𝒜).property
    (twistingSheaf 𝒜 d) hT

/-- **The twist by an invertible twisting sheaf is exact**, from the twist being an
equivalence. -/
theorem shortExact_map_twistFunctor (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℤ)
    [(twistFunctor 𝒜 d).IsEquivalence]
    {T : ShortComplex (SheafOfModules.{u} (projRingSheaf 𝒜))} (hT : T.ShortExact) :
    (T.map (twistFunctor 𝒜 d)).ShortExact :=
  hT.map_of_exact _

/-- An invertible `d`-th twisting sheaf makes the twist an equivalence, which by
`shortExact_map_twistFunctor` makes it exact. -/
theorem isEquivalence_twistFunctor
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℤ)
    [Stacks.SheafOfModules.IsInvertible (ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj
      (projRingSheaf 𝒜).property (twistingSheaf 𝒜 d)] :
    (twistFunctor 𝒜 d).IsEquivalence :=
  Stacks.ProjTwistFunctor.isEquivalence_tensorRightFunctor_of_isInvertible
    (ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj (projRingSheaf 𝒜).property
    (twistingSheaf 𝒜 d)

end Stacks.AlgebraicGeometry.ProjTwistFunctor

end
