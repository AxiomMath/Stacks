module

public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardExactSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportGeometricStalkCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedMinimalSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedShortExact
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedVanishingQuasicoherent

/-!
# Injectivity of a map of modules detected at the weakly associated points

Let `X` be an algebraic space over a scheme `S` of a big fppf site and let `φ : F → G` be a map
of quasi-coherent `𝒪_X`-modules.  Stacks 0CUR asserts that `φ` is injective as soon as every
point `x` of `X` satisfies at least one of the two conditions

1. the induced map `F_x̄ → G_x̄` on the stalk at a geometric point above `x` is injective, or
2. `x` is not a weakly associated point of `F`.

The argument of the source is followed.  The weakly associated points of `Ker(φ)` are empty,
and a quasi-coherent module with no weakly associated point vanishes.  The first half is proved
here: at a point satisfying (1) the geometric stalk of `Ker(φ)` at the given geometric point
vanishes, so the point does not even lie in the support of `Ker(φ)` (Stacks 07TZ, for the
quasi-coherent module `Ker(φ)`), which contains the weakly associated points by Stacks 0CTY; at a
point satisfying (2) it is enough that `Ker(φ)` is a subsheaf of `F`, which is Stacks 0CTZ.
Quasi-coherence of `Ker(φ)` is the kernel clause of Stacks 03M1(3),
`AlgebraicGeometry.Space.isQuasicoherentOnSite_kernel_of_quasicoherent`.  The second half itself
is the substantive direction of Stacks 0CU0,
`AlgebraicGeometry.Space.isZero_of_weaklyAssociatedPoints_eq_empty`.

Condition (1) speaks of the map `F_x̄ → G_x̄`, the functoriality of the stalk in the module.  It
is constructed below, on the underlying additive groups, both for the stalk at a point of an
arbitrary site and for the geometric stalk of a module on an algebraic space.

## Main definitions

* `Stacks.liftedSectionMap` is a morphism of sheaves of modules read on the underlying
  presheaves of abelian groups, with the sections raised to the universe of the stalk.
* `Stacks.moduleStalkLargeAddMap` is the map of stalks at a point of a site induced by a
  morphism of sheaves of modules, on the underlying additive groups.
* `AlgebraicGeometry.Space.geometricModuleStalkMap` is the map `F_x̄ → G_x̄` of geometric stalks
  induced by a morphism of `𝒪_X`-modules, on the underlying additive groups.

## Main results

* `Stacks.moduleStalkLargeAddMap_germ` and
  `AlgebraicGeometry.Space.geometricModuleStalkMap_germ`: the induced map sends the germ of a
  section to the germ of its image.  This characterises it, germs being jointly surjective.
* `AlgebraicGeometry.Space.mono_of_stalk_injective_or_notMem_weaklyAssociatedPoints`:
  **Stacks 0CUR**.

## Implementation notes

The vanishing step uses the direction `WeakAss(K) = ∅ → K = 0` of Stacks 0CU0 for the
quasi-coherent module `K = Ker(φ)`.  The support analogue,
`AlgebraicGeometry.Space.isZero_of_supportOfSheaf_eq_empty`, would not do: a point satisfying
condition (2) is removed from `WeakAss(Ker(φ))` but not from the support of `Ker(φ)`.

Quasi-coherence of `F` and of `G` is assumed, as in the source, and quasi-coherence of `Ker(φ)`,
which the argument needs, is *not* assumed: it is the kernel clause of Stacks 03M1(3) at
this module universe, `AlgebraicGeometry.Space.isQuasicoherentOnSite_kernel_of_quasicoherent` in
`StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardExactSequence`.  Quasi-coherence is
`SheafOfModules.IsQuasicoherentOnSite`, the universe-flexible form of Stacks 03DL(6).  It is used
twice: in Stacks 07TZ, which lets the single geometric point of condition (1) detect the support of
`Ker(φ)`, and in the vanishing step.  Stacks 0CTZ, which gives `WeakAss(Ker(φ)) ⊆ WeakAss(F)`,
holds for an arbitrary `𝒪_X`-module.

The module universe of the main theorem is the universe `u` of the schemes.  That is not a
choice: the kernel of `φ` and the short exact sequence `0 → Ker(φ) → F → F/Ker(φ) → 0` need the
abelian structure of `AlgebraicGeometry.Space.Modules`, which is available only there, as
`StacksFrontier.AlgebraicGeometry.Spaces.ShortExactQuasicoherent` records.  The three
stalk-functoriality declarations are stated at a free module universe.

That abelian structure is supplied to the main theorem as a local instance,
`AlgebraicGeometry.Space.smallEtaleModulesAbelian`, rather than left to instance search.  The
search is unusable in a file importing
`StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentKernelsAndCokernels`, which 03M1(3) brings in:
the two sheafification instances it declares for every universe of module sections containing the
objects of the site have a universe parameter occurring only inside a `max`, so matching them
against a goal at the universe of the schemes leaves an unsolvable universe constraint postponed
rather than failing, and the postponed constraint is reported as an error.  The local instance is
the very term the search returns when those two are absent, so it changes nothing.

Condition (1) asks, as the source does, for *one* geometric point `x̄` above `x` at which
`F_x̄ → G_x̄` is injective.  For the quasi-coherent module `Ker(φ)` the stalk at that single
geometric point decides whether `x` lies in the support, by Stacks 07TZ,
`AlgebraicGeometry.Space.mem_supportOfSheaf_iff_nontrivial_geometricModuleStalk_of_liesOver`.

The induced map of stalks is recorded only on the underlying additive groups.  It is the map of
`𝒪_{X, x̄}`-modules of the source, but injectivity — the only thing asked of it — does not see
the scalars, and the semilinearity bookkeeping of
`AlgebraicGeometry.Space.geometricModuleStalkAddEquiv` is not needed for it.

## References

* [Stacks Project, Lemma 71.2.11 (Tag 0CUR)](https://stacks.math.columbia.edu/tag/0CUR)
* [Stacks Project, Tag 0CU0](https://stacks.math.columbia.edu/tag/0CU0)
* [Stacks Project, Tag 0CTY](https://stacks.math.columbia.edu/tag/0CTY)
* [Stacks Project, Tag 0CTZ](https://stacks.math.columbia.edu/tag/0CTZ)
* [Stacks Project, Tag 04KA](https://stacks.math.columbia.edu/tag/04KA)
* [Stacks Project, Tag 07TZ](https://stacks.math.columbia.edu/tag/07TZ)
* [Stacks Project, Tag 05VQ](https://stacks.math.columbia.edu/tag/05VQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u m v w t

attribute [local instance] FinallySmall.preservesColimitsOfShape_of_isFiltered

namespace Stacks

variable {C : Type t} [Category.{v} C] [LocallySmall.{w} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (p : J.Point.{w}) (O : Sheaf J CommRingCat.{w})

/-! ### The map of stalks at a point of a site -/

/-- A morphism of sheaves of modules over the ring sheaf of `O`, read on the underlying
presheaves of abelian groups with their sections raised to the universe in which the stalk
`Stacks.moduleStalkLarge` is formed. -/
noncomputable def liftedSectionMap {F₁ F₂ : SheafOfModules.{m} (commRingSheafToRingSheaf O)}
    (α : F₁ ⟶ F₂) : liftedSectionPresheaf.{m} O F₁ ⟶ liftedSectionPresheaf.{m} O F₂ :=
  Functor.whiskerRight ((PresheafOfModules.toPresheaf _).map α.val) AddCommGrpCat.uliftFunctor.{w}

/-- The map of stalks at a point `p` of a site induced by a morphism of sheaves of modules, on
the underlying additive groups.

The stalk is a colimit of the lifted sections over a small final model of the neighbourhoods of
`p`; the induced map is the one between the colimits over all neighbourhoods, carried to the
final model along `Stacks.moduleStalkLargeFinalIso` on both sides. -/
noncomputable def moduleStalkLargeAddMap
    {F₁ F₂ : SheafOfModules.{m} (commRingSheafToRingSheaf O)} (α : F₁ ⟶ F₂) :
    moduleStalkLarge.{m} p O F₁ →+ moduleStalkLarge.{m} p O F₂ :=
  (moduleStalkLargeFinalIso.{m} p O F₂).inv.hom.comp
    ((p.presheafFiber.map (liftedSectionMap.{m} O α)).hom.comp
      (moduleStalkLargeFinalIso.{m} p O F₁).hom.hom)

/-- The induced map of stalks is the map of colimits over all neighbourhoods of the point, read
through the comparison with the colimit over the small final model which carries the stalk. -/
theorem moduleStalkLargeAddMap_apply
    {F₁ F₂ : SheafOfModules.{m} (commRingSheafToRingSheaf O)} (α : F₁ ⟶ F₂)
    (z : moduleStalkLarge.{m} p O F₁) :
    moduleStalkLargeAddMap.{m} p O α z =
      (moduleStalkLargeFinalIso.{m} p O F₂).inv
        (p.presheafFiber.map (liftedSectionMap.{m} O α)
          ((moduleStalkLargeFinalIso.{m} p O F₁).hom z)) :=
  rfl

/-- The induced map of stalks sends the germ of a section to the germ of its image.  Germs being
jointly surjective, this determines the map. -/
theorem moduleStalkLargeAddMap_germ
    {F₁ F₂ : SheafOfModules.{m} (commRingSheafToRingSheaf O)} (α : F₁ ⟶ F₂)
    (U : C) (x : p.fiber.obj U) (s : F₁.val.obj (op U)) :
    moduleStalkLargeAddMap.{m} p O α (moduleStalkLargeGerm p O F₁ U x s) =
      moduleStalkLargeGerm p O F₂ U x ((α.val.app (op U)).hom s) := by
  refine Eq.trans (congrArg (fun z => (moduleStalkLargeFinalIso.{m} p O F₂).inv
      (p.presheafFiber.map (liftedSectionMap.{m} O α) z))
    (Iso.inv_hom_id_apply (moduleStalkLargeFinalIso.{m} p O F₁)
      (p.toPresheafFiber U x (liftedSectionPresheaf.{m} O F₁) (ULift.up s)))) ?_
  exact congrArg (fun z => (moduleStalkLargeFinalIso.{m} p O F₂).inv z)
    (p.toPresheafFiber_naturality_apply (liftedSectionMap.{m} O α) U x (ULift.up s))

end Stacks

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS)

/-! ### The map of geometric stalks induced by a map of modules -/

variable (x : GeometricPoint B S hS X.1)

/-- The map `F_x̄ → G_x̄` of geometric stalks induced by a morphism `φ : F ⟶ G` of
`𝒪_X`-modules, on the underlying additive groups: the map of stalks at the point of the small
étale site determined by `x̄`, read through the extension of scalars
`AlgebraicGeometry.Space.geometricModuleStalkAddEquiv` which defines the geometric stalk. -/
noncomputable def geometricModuleStalkMap {F G : Modules.{u, m} B S hS X.1 X.2} (φ : F ⟶ G) :
    geometricModuleStalk B S hS X x F →+ geometricModuleStalk B S hS X x G :=
  (geometricModuleStalkAddEquiv B S hS X x G).toAddMonoidHom.comp
    ((Stacks.moduleStalkLargeAddMap (etaleSitePoint B S hS X.1 x X.2)
        (smallEtaleRingedTopos B S hS X).O φ).comp
      (geometricModuleStalkAddEquiv B S hS X x F).symm.toAddMonoidHom)

/-- The induced map of geometric stalks sends the germ of a section over a small étale
neighbourhood to the germ of its image.  Germs being jointly surjective, this determines the
map. -/
theorem geometricModuleStalkMap_germ {F G : Modules.{u, m} B S hS X.1 X.2} (φ : F ⟶ G)
    (N : SmallEtaleNeighborhood x) (s : F.val.obj (op N.chart)) :
    geometricModuleStalkMap B S hS X x φ (geometricModuleStalkGerm B S hS X x F N s) =
      geometricModuleStalkGerm B S hS X x G N ((φ.val.app (op N.chart)).hom s) := by
  exact congrArg (geometricModuleStalkAddEquiv B S hS X x G)
    ((congrArg _ ((geometricModuleStalkAddEquiv B S hS X x F).symm_apply_apply _)).trans
      (Stacks.moduleStalkLargeAddMap_germ (etaleSitePoint B S hS X.1 x X.2)
        (smallEtaleRingedTopos B S hS X).O φ N.chart ⟨N.point, N.point_comp⟩ s))

/-- A subsheaf of `F` killed by `φ : F ⟶ G` has zero geometric stalk at a geometric point where
the induced map `F_x̄ → G_x̄` is injective: a section of the subsheaf with nonzero germ would have
an image in `F` with zero germ in `G`, hence with zero germ in `F`, hence dying on a smaller
neighbourhood, where the section it came from dies too. -/
private theorem not_nontrivial_geometricModuleStalk_of_comp_eq_zero
    {K F G : Modules.{u, m} B S hS X.1 X.2} (ι : K ⟶ F) [Mono ι] (φ : F ⟶ G)
    (hcomp : ι ≫ φ = 0) (hinj : Function.Injective (geometricModuleStalkMap B S hS X x φ)) :
    ¬ Nontrivial (geometricModuleStalk B S hS X x K) := by
  have : Mono ι.val := (SheafOfModules.forget _).map_mono ι
  have hval : ι.val ≫ φ.val = 0 := congrArg (fun ψ => ψ.val) hcomp
  rw [nontrivial_geometricModuleStalk_iff]
  rintro ⟨N, s, hs⟩
  refine hs ?_
  have hzero : (φ.val.app (op N.chart)).hom ((ι.val.app (op N.chart)).hom s) = 0 := by
    have h := congrArg (fun (ψ : K.val ⟶ G.val) => (ψ.app (op N.chart)).hom s) hval
    simpa using h
  have hgermF : geometricModuleStalkGerm B S hS X x F N
      ((ι.val.app (op N.chart)).hom s) = 0 := by
    refine hinj ?_
    rw [geometricModuleStalkMap_germ, map_zero, hzero, map_zero]
  obtain ⟨M, f, hf⟩ := (geometricModuleStalkGerm_eq_zero_iff B S hS X x F N _).mp hgermF
  refine (geometricModuleStalkGerm_eq_zero_iff B S hS X x K N s).mpr ⟨M, f, ?_⟩
  refine PresheafOfModules.injective_of_mono ι.val (op M.chart) ?_
  exact ((PresheafOfModules.naturality_apply ι.val f.hom.op s).trans hf).trans (map_zero _).symm

/-! ### Stacks 0CUR -/

/-- The abelian structure of the `𝒪_X`-modules with sections in the universe of the schemes,
written out instead of being found by instance search.

It is the term instance search returns, namely `SheafOfModules.instAbelian` fed the two
sheafification instances of `StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian`, so nothing is
changed by using it; see the implementation notes for why the search itself is not used. -/
@[instance_reducible] public noncomputable def smallEtaleModulesAbelian :
    Abelian (Modules.{u, u} B S hS X.1 X.2) :=
  @SheafOfModules.instAbelian _ _ _ _ (smallEtaleRingedSite_hasSheafify B S hS X.1 X.2)
    (smallEtaleRingedSite_wEqualsLocallyBijective B S hS X.1 X.2)

attribute [local instance 10000] smallEtaleModulesAbelian in
/-- **Stacks Project, Tag 0CUR**.

Let `φ : F ⟶ G` be a map of quasi-coherent `𝒪_X`-modules on an algebraic space `X` such that
every point `x` of `X` satisfies at least one of: the induced map `F_x̄ → G_x̄` is injective for
a geometric point `x̄` above `x`, or `x` is not a weakly associated point of `F`.  Then `φ` is
injective.

The proof follows the source: `Ker(φ)` is quasi-coherent by the kernel clause of Stacks 03M1(3),
`WeakAss(Ker(φ)) = ∅`, and `Ker(φ)` vanishes by Stacks 0CU0. -/
@[stacks 0CUR]
theorem mono_of_stalk_injective_or_notMem_weaklyAssociatedPoints
    (F G : Modules.{u, u} B S hS X.1 X.2)
    [F.IsQuasicoherentOnSite] [G.IsQuasicoherentOnSite] (φ : F ⟶ G)
    (hφ : ∀ y : points B S hS X.1,
      (∃ ybar : GeometricPoint B S hS X.1, ybar.LiesOver y ∧
          Function.Injective (geometricModuleStalkMap B S hS X ybar φ)) ∨
        y ∉ weaklyAssociatedPoints B S hS X F) :
    Mono φ := by
  have := isQuasicoherentOnSite_kernel_of_quasicoherent B S hS X.1 X.2 φ
  let σ : ShortComplex (Modules.{u, u} B S hS X.1 X.2) :=
    ShortComplex.mk (kernel.ι φ) (cokernel.π (kernel.ι φ)) (cokernel.condition _)
  have hσ : σ.ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel σ
        (Abelian.monoIsKernelOfCokernel (f := kernel.ι φ) _ (colimit.isColimit _))
      mono_f := inferInstanceAs (Mono (kernel.ι φ))
      epi_g := inferInstanceAs (Epi (cokernel.π (kernel.ι φ))) }
  have hempty : weaklyAssociatedPoints B S hS X (kernel φ) = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun y hy => ?_
    have hyF : y ∈ weaklyAssociatedPoints B S hS X F :=
      weaklyAssociatedPoints_subset_of_shortExact B S hS X σ hσ hy
    rcases hφ y with ⟨ybar, hybar, hinj⟩ | hnot
    · exact not_nontrivial_geometricModuleStalk_of_comp_eq_zero B S hS X ybar (kernel.ι φ) φ
        (kernel.condition φ) hinj
        ((mem_supportOfSheaf_iff_nontrivial_geometricModuleStalk_of_liesOver B S hS X
          (kernel φ) ybar y hybar).mp
          (weaklyAssociatedPoints_subset_supportOfSheaf B S hS X (kernel φ) hy))
    · exact hnot hyF
  exact (Preadditive.mono_iff_isZero_kernel φ).mpr
    (isZero_of_weaklyAssociatedPoints_eq_empty B S hS X (kernel φ) hempty)

end AlgebraicGeometry.Space

end
