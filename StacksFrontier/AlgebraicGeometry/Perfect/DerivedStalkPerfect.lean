module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PushforwardClosedImmersion
public import StacksFrontier.Homology.Perfect.Defs
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.CohomologyFiniteFreeLocus
public import StacksFrontier.Topology.Sheaves.Modules.StalkRestrictOpen

/-!
# The derived stalk of a perfect complex is perfect

Let `X` be a ringed space all of whose structure-sheaf stalks are local rings — a scheme, for
instance — and let `K` be a perfect object of the derived category of `𝒪_X`-modules in the sense
of [Stacks, Tag 08CM]. Then the derived stalk of `K` at a point `x`, the image of `K` under the
functor induced on derived categories by the exact stalk functor, is a perfect object of the
derived category of modules over the stalk ring at `x` in the sense of [Stacks, Tag 0657].

## Main definitions

* `AlgebraicGeometry.RingedSpace.moduleStalkOver`: the stalk functor at `x` followed by
  restriction of scalars along a chosen isomorphism of the stalk ring with a ring `R`.

## Main results

* `AlgebraicGeometry.RingedSpace.isPerfect_moduleStalkOver_of_isPerfect`: the statement for any
  exact functor isomorphic to `moduleStalkOver`. This is the form the consumers want: the stalk
  of an `𝒪_X`-module is a module over the `RingCat`-valued stalk of the structure sheaf of rings,
  while `StacksDraft.Perfect.IsPerfect` is wanted over whichever spelling of the local ring at
  `x` the consumer works with.
* `AlgebraicGeometry.RingedSpace.isPerfect_moduleStalk_of_isPerfect`: the same statement for the
  stalk functor itself.
* `AlgebraicGeometry.RingedSpace.exists_basis_moduleStalk_of_isDirectSummandOfFiniteFree`: the
  stalk of a direct summand of a finite free `𝒪_X`-module is finite free, which is the one
  genuinely local input.
* `AlgebraicGeometry.RingedSpace.isPerfect_of_isStrictlyPerfect_model`: the stalks of a strictly
  perfect complex form a bounded complex of finite free modules, so anything isomorphic to it in
  the derived category is perfect.

## Implementation notes

*The shape of the argument.* Perfectness of `K` gives a representative complex `E` and an open
covering on each member of which `E` receives a quasi-isomorphism from a strictly perfect
complex. Only the member `U` containing `x` is used. The strictly perfect complex `P` on `X|_U`
is bounded with terms direct summands of finite free `𝒪_{X|U}`-modules, so — the stalks of `X|_U`
being local rings, transported from those of `X` along
`AlgebraicGeometry.PresheafedSpace.restrictStalkIso` — each stalk `(P^j)_x` is a *finite free*
module over the stalk ring of `X|_U` at `x` by [Stacks, Tag 0BCI]. Taking stalks is exact, so the
complex of those stalks is quasi-isomorphic to the complex of stalks of `E|_U`, which is the
complex of stalks of `E`; that last identification is
`AlgebraicGeometry.RingedSpace.restrictModulesStalkNatIso`.

*Why the restriction of scalars is carried through the whole proof rather than applied at the
end.* The stalk of `X|_U` at `x` is only *isomorphic* to the stalk of `X` at `x`, the two being
colimits over two different index categories, so the bounded finite free complex the argument
produces lives over the wrong ring. Transporting a perfect object along a restriction of scalars
at the end would need finiteness *and projectivity* to be carried along a ring isomorphism, and
projectivity is not given by a basis. Instead the restriction of scalars is folded into the
functor whose value on `P` is taken — that is what `moduleStalkOver` is for: the terms of the
resulting complex are finite free by `Module.Basis.mapCoeffs`, and nothing has to be transported
at all. The same device absorbs the comparison between the `RingCat`-valued and the
`CommRingCat`-valued stalk of the structure sheaf, which is why the statements are parameterised
by an arbitrary isomorphism `ε` of the stalk ring with a ring `R`.

*Two spellings of restriction to an open.* The covering in
`AlgebraicGeometry.RingedSpace.IsPerfectComplex` is phrased with
`AlgebraicGeometry.RingedSpace.restrictModules`, the pushforward along the identity of the
structure sheaf of the open subspace, while the stalk comparison is phrased with
`StrictlyPerfect.restrictModules`, precomposition on underlying presheaves. The two are the same
functor on the nose, which is
`AlgebraicGeometry.RingedSpace.strictlyPerfectRestrictModules_eq`, so the two occurrences are
interchangeable without a comparison map.

*Why `StacksFrontier.Topology.Sheaves.Modules.StalkRestrictOpenExactness` is not imported.* That
file would supply the exactness instances for the stalk functor of the open subspace at the point
`⟨x, hx⟩`, which is the only shape instance search does not reach on its own here, but it also
registers a `CommRing` instance on the `RingCat`-valued stalk of the structure sheaf. With that
instance in scope the `Semiring` instance on the stalk ring found by instance search is no longer
the one carried by the `ModuleCat` the stalk functor is valued in, and `Module (𝒪_{X,x}) (M_x)`
stops being synthesizable — the failure the implementation notes of
`StacksFrontier/AlgebraicGeometry/Perfect/DerivedStalkPseudoCoherent.lean` record. The three
instances actually needed are therefore produced locally inside the proof from the generic
statements they are instances of.

## References

* [Stacks Project, Tag 0657](https://stacks.math.columbia.edu/tag/0657)
* [Stacks Project, Tag 08CM](https://stacks.math.columbia.edu/tag/08CM)
* [Stacks Project, Tag 0BCI](https://stacks.math.columbia.edu/tag/0BCI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect

universe u d

namespace AlgebraicGeometry.RingedSpace

/-- **A basis survives restriction of scalars along an isomorphism of rings.** If `N` is a module
over `S` with basis `b` and `e : R ≃+* S`, then `b` is a basis of `N` read as an `R`-module
through `e`. -/
def basisRestrictScalars {R S : Type u} [Ring R] [Ring S] (e : R ≃+* S) {ι : Type*}
    {N : ModuleCat.{u} S} (b : Module.Basis ι S N) :
    Module.Basis ι R ((ModuleCat.restrictScalars e.toRingHom).obj N) :=
  have b' : Module.Basis ι S ((ModuleCat.restrictScalars e.toRingHom).obj N) := b
  b'.mapCoeffs e.symm fun c m => congrArg (fun r : S => r • (m : N)) (e.apply_symm_apply c)

variable {X : RingedSpace.{u, u}}

/-- **The stalk of a direct summand of a finite free `𝒪_X`-module is finite free.** On a ringed
space whose structure-sheaf stalks are local rings, the stalk at `x` of an `𝒪_X`-module that is a
direct summand of a finite free one has a finite basis over the `RingCat`-valued stalk of the
structure sheaf of rings at `x`.

This is [Stacks, Tag 0BCI] read on stalks: the module is a retract of a finite locally free one,
a retract of a finite locally free module over a space with local stalks is finite locally free,
and a finite locally free module has free stalks of finite rank. -/
theorem exists_basis_moduleStalk_of_isDirectSummandOfFiniteFree
    [hloc : ∀ z : X.carrier, IsLocalRing (ToType (X.presheaf.stalk z))]
    {M : OXMod.{u, u} X} (hM : IsDirectSummandOfFiniteFree M) (x : X.carrier) :
    ∃ r : ℕ, Nonempty (Module.Basis (ULift.{u} (Fin r)) (ringCatStalk X x)
      ((moduleStalkFunctor X x).obj M)) := by
  have _ : ∀ z : X.carrier, IsLocalRing (ToType (TopCat.Presheaf.stalk X.sheaf.obj z)) := hloc
  obtain ⟨n, ⟨ρ⟩⟩ := exists_retract_free hM
  obtain ⟨r, ⟨eqv⟩⟩ := AlgebraicGeometry.SheafOfModules.exists_free_stalk_of_retract
    (X := X.carrier) (O := X.sheaf) ρ
    (isFiniteLocallyFree_of_iso (finiteFreeIsoFree X n).symm
      (isFiniteLocallyFree_finiteFree X n)) x
  exact ⟨r, ⟨Module.Basis.ofRepr eqv⟩⟩

/-- **The stalk functor at `x`, read over a ring `R` isomorphic to the stalk ring.** The stalk
functor on `𝒪_X`-modules is valued in modules over the `RingCat`-valued stalk of the structure
sheaf of rings; this composes it with restriction of scalars along an isomorphism `ε` of `R` with
that stalk ring, so that it is valued in `R`-modules. -/
abbrev moduleStalkOver (X : RingedSpace.{u, u}) (x : X.carrier) {R : Type u} [Ring R]
    (ε : R ≃+* ringCatStalk X x) : OXMod.{u, u} X ⥤ ModuleCat.{u} R :=
  moduleStalkFunctor X x ⋙ ModuleCat.restrictScalars ε.toRingHom

/-- **The stalks of a strictly perfect complex form a bounded complex of finite free modules,**
and therefore represent a perfect object of the derived category: anything isomorphic in the
derived category of `R`-modules to the complex of stalks at `x`, read over `R`, of a strictly
perfect complex of `𝒪_X`-modules is perfect.

The stalks of `X` are assumed to be local rings, which is what makes the terms finite free rather
than merely direct summands of finite free; `Module.Basis.mapCoeffs` then carries the bases across
the restriction of scalars along `ε`. -/
theorem isPerfect_of_isStrictlyPerfect_model
    [∀ z : X.carrier, IsLocalRing (ToType (X.presheaf.stalk z))]
    (x : X.carrier) {R : Type u} [Ring R] [HasDerivedCategory.{d} (ModuleCat.{u} R)]
    (ε : R ≃+* ringCatStalk X x)
    (P : CochainComplex (OXMod.{u, u} X) ℤ) (hP : IsStrictlyPerfect P)
    (L : DerivedCategory (ModuleCat.{u} R))
    (e : L ≅ DerivedCategory.Q.obj
      (((moduleStalkOver X x ε).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) :
    StacksDraft.Perfect.IsPerfect L := by
  classical
  refine ⟨((moduleStalkOver X x ε).mapHomologicalComplex (ComplexShape.up ℤ)).obj P,
    Classical.choose hP.bounded.bddBelow, Classical.choose hP.bounded.bddAbove, ?_, ?_, ?_, ?_,
    ⟨e⟩⟩
  · rw [CochainComplex.isStrictlyGE_iff]
    intro j hj
    refine Functor.map_isZero (moduleStalkOver X x ε) (not_not.mp fun hz => ?_)
    exact absurd (Classical.choose_spec hP.bounded.bddBelow hz) (by omega)
  · rw [CochainComplex.isStrictlyLE_iff]
    intro j hj
    refine Functor.map_isZero (moduleStalkOver X x ε) (not_not.mp fun hz => ?_)
    exact absurd (Classical.choose_spec hP.bounded.bddAbove hz) (by omega)
  all_goals
    intro j
    obtain ⟨r, ⟨b⟩⟩ :=
      exists_basis_moduleStalk_of_isDirectSummandOfFiniteFree (hP.directSummand j) x
  · exact Module.Finite.of_basis (basisRestrictScalars ε b)
  · exact Module.Projective.of_basis (basisRestrictScalars ε b)

/-- The isomorphism of a ring `R` with the stalk ring of the open subspace `X|_U` at a point `x`
of `U`, obtained from an isomorphism `ε` of `R` with the stalk ring of `X` at `x` and the
comparison `AlgebraicGeometry.RingedSpace.restrictModulesStalkRingIso` of the two stalk rings. -/
def stalkRestrictRingEquiv (X : RingedSpace.{u, u}) (U : Opens X.carrier) {x : X.carrier}
    (hx : x ∈ U) {R : Type u} [Ring R] (ε : R ≃+* ringCatStalk X x) :
    R ≃+* ringCatStalk (X.restrict U.isOpenEmbedding) ⟨x, hx⟩ :=
  ε.trans (restrictModulesStalkRingIso X U hx).ringCatIsoToRingEquiv.symm

/-- **Restricting an `𝒪_X`-module to an open `U` containing `x` and taking its stalk at `x` over
`R` is taking its stalk at `x` on `X` over `R`.** This is
`AlgebraicGeometry.RingedSpace.restrictModulesStalkNatIso` with the two restrictions of scalars
that occur on its right-hand side composed into one. -/
def restrictModuleStalkOverIso (X : RingedSpace.{u, u}) (U : Opens X.carrier)
    {x : X.carrier} (hx : x ∈ U) {R : Type u} [Ring R] (ε : R ≃+* ringCatStalk X x) :
    StrictlyPerfect.restrictModules.{u, u, u} X U ⋙
        moduleStalkOver (X.restrict U.isOpenEmbedding) ⟨x, hx⟩
          (stalkRestrictRingEquiv X U hx ε) ≅
      moduleStalkOver X x ε :=
  Functor.isoWhiskerRight (restrictModulesStalkNatIso X U hx)
      (ModuleCat.restrictScalars (stalkRestrictRingEquiv X U hx ε).toRingHom) ≪≫
    Functor.isoWhiskerLeft (moduleStalkFunctor X x)
      (ModuleCat.restrictScalarsComp' (stalkRestrictRingEquiv X U hx ε).toRingHom
        (restrictModulesStalkRingIso X U hx).hom.hom ε.toRingHom (by
          ext a
          exact ((restrictModulesStalkRingIso X U hx).ringCatIsoToRingEquiv.apply_symm_apply
            (ε a)).symm)).symm

/-- **The derived stalk of a perfect complex is perfect.** Let `X` be a ringed space whose
structure-sheaf stalks are local rings, let `x` be a point of `X`, let `R` be a ring isomorphic
by `ε` to the stalk of the structure sheaf of rings at `x`, and let `V` be an exact functor
isomorphic to `AlgebraicGeometry.RingedSpace.moduleStalkOver X x ε`. If `K` is a perfect object
of the derived category of `𝒪_X`-modules, then `V K` is a perfect object of the derived category
of `R`-modules. -/
theorem isPerfect_moduleStalkOver_of_isPerfect
    [∀ z : X.carrier, IsLocalRing (ToType (X.presheaf.stalk z))]
    [HasDerivedCategory.{d} (OXMod.{u, u} X)] (x : X.carrier)
    {R : Type u} [Ring R] [HasDerivedCategory.{d} (ModuleCat.{u} R)]
    (ε : R ≃+* ringCatStalk X x)
    (V : OXMod.{u, u} X ⥤ ModuleCat.{u} R) [V.Additive] [PreservesFiniteLimits V]
    [PreservesFiniteColimits V] (eV : V ≅ moduleStalkOver X x ε)
    (K : DerivedCategory (OXMod.{u, u} X)) (hK : IsPerfect K) :
    StacksDraft.Perfect.IsPerfect (V.mapDerivedCategory.obj K) := by
  classical
  obtain ⟨E, hE, ⟨eEK⟩⟩ := hK
  obtain ⟨I, U, hU, hmodels⟩ := hE
  obtain ⟨i, hxi⟩ : ∃ i, x ∈ U i := by
    have hx : x ∈ (⊤ : Opens X.carrier) := trivial
    rw [← hU] at hx
    simpa using hx
  obtain ⟨P, hP, f, hf⟩ := hmodels i
  have _ : ∀ w : (X.restrict (U i).isOpenEmbedding).carrier,
      IsLocalRing (ToType ((X.restrict (U i).isOpenEmbedding).presheaf.stalk w)) := fun w =>
    RingEquiv.isLocalRing
      ((X.restrictStalkIso (U i).isOpenEmbedding w).symm.commRingCatIsoToRingEquiv)
  -- the three exactness instances for the stalk functor of the open subspace at `⟨x, hxi⟩`
  have _ : (moduleStalkFunctor (X.restrict (U i).isOpenEmbedding) (⟨x, hxi⟩ :
      (X.restrict (U i).isOpenEmbedding).carrier)).Additive :=
    AlgebraicGeometry.SheafOfModules.stalkFunctor_additive _ _
  have _ : PreservesFiniteLimits (moduleStalkFunctor (X.restrict (U i).isOpenEmbedding)
      (⟨x, hxi⟩ : (X.restrict (U i).isOpenEmbedding).carrier)) :=
    AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesFiniteLimits _ _
  have _ : PreservesFiniteColimits (moduleStalkFunctor (X.restrict (U i).isOpenEmbedding)
      (⟨x, hxi⟩ : (X.restrict (U i).isOpenEmbedding).carrier)) :=
    AlgebraicGeometry.SheafOfModules.instPreservesFiniteColimitsStalkFunctor _ _
  have hiso : IsIso (DerivedCategory.Q.map
      (((moduleStalkOver (X.restrict (U i).isOpenEmbedding) ⟨x, hxi⟩
        (stalkRestrictRingEquiv X (U i) hxi ε)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map f)) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    infer_instance
  refine isPerfect_of_isStrictlyPerfect_model (X := X.restrict (U i).isOpenEmbedding)
    ⟨x, hxi⟩
    (stalkRestrictRingEquiv X (U i) hxi ε) P hP _ ?_
  exact (Functor.mapDerivedCategoryCongr eV).app K ≪≫
    (moduleStalkOver X x ε).mapDerivedCategory.mapIso eEK.symm ≪≫
    (moduleStalkOver X x ε).mapDerivedCategoryFactors.app E ≪≫
    DerivedCategory.Q.mapIso ((Functor.mapHomologicalComplexCompIso
      (restrictModuleStalkOverIso X (U i) hxi ε) (ComplexShape.up ℤ)).app E).symm ≪≫
    (@asIso _ _ _ _ _ hiso).symm

/-- **The derived stalk of a perfect complex is perfect**, for the stalk functor itself: the
image of a perfect object of the derived category of `𝒪_X`-modules under the functor induced on
derived categories by the exact stalk functor at `x` is a perfect object of the derived category
of modules over the `RingCat`-valued stalk of the structure sheaf of rings at `x`. -/
theorem isPerfect_moduleStalk_of_isPerfect
    [∀ z : X.carrier, IsLocalRing (ToType (X.presheaf.stalk z))]
    [HasDerivedCategory.{d} (OXMod.{u, u} X)] (x : X.carrier)
    [HasDerivedCategory.{d} (ModuleCat.{u} (ringCatStalk X x))]
    (K : DerivedCategory (OXMod.{u, u} X)) (hK : IsPerfect K) :
    StacksDraft.Perfect.IsPerfect ((moduleStalkFunctor X x).mapDerivedCategory.obj K) :=
  isPerfect_moduleStalkOver_of_isPerfect x (RingEquiv.refl _) (moduleStalkFunctor X x)
    ((Functor.rightUnitor (moduleStalkFunctor X x)).symm ≪≫
      Functor.isoWhiskerLeft (moduleStalkFunctor X x)
        (ModuleCat.restrictScalarsId' (RingEquiv.refl (ringCatStalk X x)).toRingHom rfl).symm)
    K hK

end AlgebraicGeometry.RingedSpace

end
