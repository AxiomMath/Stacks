module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleDenseSubsite
public import StacksFrontier.AlgebraicGeometry.Spaces.CartesianRelations
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSectionsCokernel
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.ShortExactQuasicoherent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.Quasicoherence

/-!
# Cokernels of modules on an algebraic space, and the local-to-global step of quasi-coherence

Let `F` be an algebraic space over a scheme `S`.  Its `𝒪_F`-modules are the sheaves of modules on
the small étale ringed site of `F`, and `AlgebraicGeometry.Space.Modules` leaves the universe of
the module sections free.  This file does two things.

First it records that the category of `𝒪_F`-modules **whose sections lie in the universe of the
schemes** has cokernels.  Second, it reduces quasi-coherence of a cokernel — and of any third
module, cokernel or not — to a purely local statement about *affine* étale charts: the refinement
of the two presenting coverings, and the passage from arbitrary charts to affine ones, are both
carried out here.

## Main results

* `SheafOfModules.IsQuasicoherentOnSite.of_hasGlobalPresentation_pair_of_coverDense`: given a
  cover-dense functor into the site, a sheaf of modules which has a global presentation over the
  image of every object over which two given quasi-coherent modules both have one is itself
  quasi-coherent.
* `SheafOfModules.IsQuasicoherentOnSite.of_hasGlobalPresentation_pair`: the same with no
  cover-dense functor, that is, with the local statement asked of every object of the site.
* `AlgebraicGeometry.Space.hasCokernel_modules`: morphisms of `𝒪_F`-modules with sections in the
  universe of the schemes have cokernels.
* `AlgebraicGeometry.Space.hasCokernels_modules` and
  `AlgebraicGeometry.Space.hasCokernels_modules_succ`: the categories of `𝒪_F`-modules with
  sections in the universe `u` of the schemes, and in `u + 1`, have cokernels.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_cokernel` and
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_cokernel_of_affineCharts`: the cokernel of a
  morphism of quasi-coherent `𝒪_F`-modules is quasi-coherent, granted the local cokernel step —
  over every étale chart in the first, over affine étale charts only in the second.
* `SheafOfModules.val_app_factorThruImage` and `SheafOfModules.exact_val_app_cokernel_π`: on the
  sections over an object, a morphism and the projection to its cokernel form an exact pair as
  soon as the canonical epimorphism onto the image is surjective there.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_cokernel_of_isCartesian` and
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_cokernel_of_h03DX`: **the second route to the
  cokernel clause**, through the base change criterion rather than through presentations.  See
  the implementation notes for why both routes are recorded and what each owes.

## Implementation notes

**Deviation from Stacks 03M1 stated with a free module universe, and why that form is not
provable.**  That form states its two declarations for `AlgebraicGeometry.Space.Modules.{u, m}`
with the module universe `m` independent of the universe `u` of the schemes.  In that generality
`CategoryTheory.Limits.HasCokernel` does not hold, and the failure is a missing construction
rather than a missing proof: a cokernel of sheaves of modules is the sheafification of the
cokernel of presheaves, and `CategoryTheory.HasWeakSheafify` for `AddCommGrpCat.{m}`-valued
presheaves on the small étale site needs `m` to dominate the universes of the site, which an
unconstrained `m` does not.  It holds at `m := u` — the universes of the site are `u + 1` and
`u`, but the site is essentially small at `u`, which is what
`AlgebraicGeometry.Space.SmallEtale.instHasSheafify` and
`AlgebraicGeometry.Space.smallEtaleRingedSite_hasSheafify` exploit — and it holds at `m := u + 1`
by the generic construction, and at no free `m`.  `UnivLE.{u, m}` and `UnivLE.{u + 1, m}` do not
repair it.  Kernels are unaffected, because limits of sheaves of modules are computed pointwise.
So the two declarations below are stated at `m := u`, a universe specialisation of that form and
not a weakening of its mathematics: it is the universe of the structure sheaf and of the
morphisms of the site, and the one in which the quasi-coherence instances this tree supplies for
the small étale ringed site are phrased.

**The second deviation: the quasi-coherence clause is conditional, hence a theorem and not an
instance.**  The tagged statement is an `instance` with no hypotheses.  Here it carries `hlocal`,
the statement that the restriction of the cokernel to a chart over which both modules have
global presentations has a global presentation itself.  That hypothesis is the geometric content
of the cokernel clause of Stacks 03M1 and it is not formal.  Sections of a sheaf of modules are
*left* exact only: `CategoryTheory.Limits.PreservesFiniteLimits` holds for the evaluation
`SheafOfModules.evaluation` at an object of the site, by
`SheafOfModules.Finite.evaluationPreservesFiniteLimits`, whereas the corresponding
`CategoryTheory.Limits.PreservesFiniteColimits` is not available and cannot be — a cokernel of
sheaves of modules is the sheafification of the cokernel of presheaves, so the sections of a
cokernel are not the cokernel of the sections and `hlocal` cannot be read off sections.  In the
source it is discharged by lifting the generators of a presentation of the source along a
presentation of the target over an affine chart, which is Descent, Proposition 03DX(2).  The
formal half of that step is already in the tree, as
`SheafOfModules.HasGlobalPresentation.of_isColimit_cokernelCofork_of_lift`, and its own `lift`
hypothesis is the same obstruction.

What is proved here unconditionally is the local-to-global half, and in the sharp form: the local
statement is needed only over **affine** charts, which is where the source discharges it and
where `AlgebraicGeometry.Space.isCartesianOnAffineCharts_cokernel` operates.  Two inputs make
that possible, both already in the tree.  Restriction of a global presentation along an arbitrary
morphism of the site is `Stacks.SheafOfModules.hasGlobalPresentation_overMap`, so nothing here
re-derives it.  And the affine étale charts are cover dense in all étale charts, by
`AlgebraicGeometry.Space.AffineEtale.inclusion_isSpecialCocontinuous` (Stacks 04JS), which gives
a covering sieve of every chart consisting of arrows that factor through affine charts.  The rest
is sieve arithmetic: the two presenting coverings intersect to a covering sieve, every arrow of
the intersection carries both presentations, and `CategoryTheory.GrothendieckTopology.transitive`
replaces that sieve by the family of its members with affine source.

**The second route, and why it is recorded alongside the first.**  Quasi-coherence of a module on
the small étale site also follows from the base change criterion
`AlgebraicGeometry.Space.IsCartesianOnAffineCharts`, unconditionally, by
`AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isCartesianOnAffineCharts`.  Composing that
with `AlgebraicGeometry.Space.isCartesianOnAffineCharts_cokernel` gives a second proof of the
cokernel clause whose debts are *different* from `hlocal`.  They are:

* the implication "quasi-coherent ⟹ cartesian on affine charts" of Descent,
  Proposition 03DX(2), carried as

      (h03DX : ∀ G : Modules.{u, u} B S hS F hF,
        G.IsQuasicoherentOnSite → IsCartesianOnAffineCharts G)

  which is the spelling `StacksFrontier.AlgebraicGeometry.Spaces.ShortExactQuasicoherent` carries
  verbatim, so that **one** cited input serves both clauses with no adapter;
* surjectivity on the sections over affine charts of two *specific* epimorphisms, the projection
  `CategoryTheory.Limits.cokernel.π f` and the canonical epimorphism
  `CategoryTheory.Abelian.factorThruImage f` of `f` onto its image, carried as

      (hpi : ∀ U : SmallEtale B S hS F,
        IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U) →
          Function.Surjective ((cokernel.π f).val.app (Opposite.op U)))
      (him : ∀ U : SmallEtale B S hS F,
        IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U) →
          Function.Surjective ((Abelian.factorThruImage f).val.app (Opposite.op U)))

  These two are **not** on the same footing: `him` is an instance of Stacks 03DW whose side
  condition is discharged here, whereas `hpi` is 03DW's shape applied to a module whose
  quasi-coherence this file does not have, and so is bespoke to the cokernel clause.  The next
  note is that distinction in full.

`hlocal`, by contrast, is owed by this clause alone.  Neither route subsumes the other —
`AlgebraicGeometry.Space.isQuasicoherentOnSite_cokernel_of_affineCharts` needs no cohomological
input at all, only the presentation step — and both are kept.

`him` is what `SheafOfModules.exact_val_app_cokernel_π` turns into the exactness of the sections
that `AlgebraicGeometry.Space.isCartesianOnAffineCharts_cokernel` asks for: the kernel of
`cokernel.π f` is the image of `f` and sections take a kernel to a kernel, so all that is missing
is that the sections of `f` already fill that image.

**Why `hpi` and `him` are two hypotheses and not one.**  They are *not* consolidated into a
single hypothesis quantified over all epimorphisms, because that hypothesis is false.  An
epimorphism is surjective on the sections over an affine chart because the first cohomology
there of its *kernel* vanishes, and Stacks 03DW gives that vanishing for a *quasi-coherent*
kernel only; this is the same side condition that makes the `h03DW` of
`AlgebraicGeometry.Space.isQuasicoherent_middle_of_shortExact` legitimate, where the kernel is
the hypothesis `[T.X₁.IsQuasicoherentOnSite]`.  The two instances here differ in exactly that
respect, and the difference is sharp.

The kernel of `Abelian.factorThruImage f` is the kernel of `f`, which
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_kernel` makes cartesian unconditionally from
`hM` and `hN`, and `AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isCartesianOnAffineCharts`
then makes quasi-coherent, also unconditionally.  So the side condition of Stacks 03DW is
**discharged** for `him` by the hypotheses already present, and `him` is Stacks 03DW itself with
nothing further owed.  The kernel of `cokernel.π f`, by contrast, is the image of `f`, whose
quasi-coherence this file does not have and whose only routes to it here are circular: `im f` is
the kernel of `cokernel.π f`, so reading it off that kernel needs the cokernel to be cartesian,
which is the conclusion; and `im f` is a cokernel of `ker f ⟶ M`, so reading it off that needs
the cokernel clause being proved.  `hpi` is therefore the genuinely open hypothesis of this
route, and the one that is bespoke to cokernels.

**No `@[stacks]` attribute is claimed**, and for two different reasons, neither of which applies
to every declaration below.

`AlgebraicGeometry.Space.hasCokernel_modules` is unconditional; what it is not is the tagged
statement, being the universe specialisation `m := u` of it.  The four forms of the
quasi-coherence clause each carry an owed input: `hlocal` for
`AlgebraicGeometry.Space.isQuasicoherentOnSite_cokernel_of_affineCharts` and
`AlgebraicGeometry.Space.isQuasicoherentOnSite_cokernel`, `hpi` and `him` for
`AlgebraicGeometry.Space.isQuasicoherentOnSite_cokernel_of_isCartesian`, and `h03DX` on top of
those two for `AlgebraicGeometry.Space.isQuasicoherentOnSite_cokernel_of_h03DX`; tagging a
reduction with the tag it reduces would report the tag as proved.  There is no `h03DW`
hypothesis anywhere in this file — the surjectivity statements `hpi` and `him` are what Stacks
03DW is used *for* here, and each is about one named morphism rather than quantified.

The remaining declarations state no part of Stacks 03M1 at all, and are unconditional:
`SheafOfModules.IsQuasicoherentOnSite.of_hasGlobalPresentation_pair_of_coverDense` and
`SheafOfModules.IsQuasicoherentOnSite.of_hasGlobalPresentation_pair` are the local-to-global
step for an arbitrary site, `SheafOfModules.val_app_factorThruImage` and
`SheafOfModules.exact_val_app_cokernel_π` are statements about sections, and
`AlgebraicGeometry.Space.coverByImage_affineEtaleInclusion_mem` is a restatement of Stacks 04JS.

## References

* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03G9](https://stacks.math.columbia.edu/tag/03G9)
* [Stacks Project, Tag 04JS](https://stacks.math.columbia.edu/tag/04JS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v r m

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}

/-- **The local-to-global step for quasi-coherence, along a cover-dense functor.**  Let `G` be a
functor into the site whose images cover every object, and let `M` and `N` be quasi-coherent
sheaves of modules.  A sheaf of modules `T` which has a global presentation over `G.obj W`
whenever `M` and `N` both have one there is quasi-coherent.

Nothing about cokernels enters and the module universe is free.  The proof intersects the two
covering sieves witnessing quasi-coherence of `M` and of `N`, which is covering; every arrow of
the intersection factors through a member of each of the two presenting families, so both
presentations restrict to its source by
`Stacks.SheafOfModules.hasGlobalPresentation_overMap`; and the covering family finally produced
is the family of those arrows of the intersection whose source is an image of `G`, which is
covering by transitivity against cover density. -/
theorem IsQuasicoherentOnSite.of_hasGlobalPresentation_pair_of_coverDense
    {D : Type u} [Category.{v} D] (G : D ⥤ C)
    (hG : ∀ U : C, Sieve.coverByImage G U ∈ J U)
    {M N T : SheafOfModules.{m} R}
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite)
    (h : ∀ W : D, (M.over (G.obj W)).HasGlobalPresentation →
      (N.over (G.obj W)).HasGlobalPresentation →
        (T.over (G.obj W)).HasGlobalPresentation) :
    T.IsQuasicoherentOnSite where
  locally_hasGlobalPresentation U := by
    obtain ⟨I₁, V₁, p₁, hc₁, hM'⟩ := hM.locally_hasGlobalPresentation U
    obtain ⟨I₂, V₂, p₂, hc₂, hN'⟩ := hN.locally_hasGlobalPresentation U
    set S : Sieve U := Sieve.ofArrows V₁ p₁ ⊓ Sieve.ofArrows V₂ p₂
    have hS : S ∈ J U := J.intersection_covering hc₁ hc₂
    have hpres : ∀ {Z : C} (g : Z ⟶ U), S.arrows g →
        (M.over Z).HasGlobalPresentation ∧ (N.over Z).HasGlobalPresentation := by
      intro Z g hg
      obtain ⟨j₁, a₁, -⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hg.1
      obtain ⟨j₂, a₂, -⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hg.2
      exact ⟨Stacks.SheafOfModules.hasGlobalPresentation_overMap M a₁ (hM' j₁),
        Stacks.SheafOfModules.hasGlobalPresentation_overMap N a₂ (hN' j₂)⟩
    refine ⟨Σ W : D, {g : G.obj W ⟶ U // S.arrows g}, fun i => G.obj i.1, fun i => i.2.1,
      ?_, fun i => h i.1 (hpres i.2.1 i.2.2).1 (hpres i.2.1 i.2.2).2⟩
    refine J.transitive hS _ fun {Z} {g} hg => J.superset_covering ?_ (hG Z)
    rintro Y k ⟨⟨W, l, n, hfac⟩⟩
    rw [Sieve.pullback_apply, Sieve.mem_ofArrows_iff]
    exact ⟨⟨W, ⟨n ≫ g, S.downward_closed hg n⟩⟩, l, by rw [← Category.assoc, hfac]⟩

/-- **The local-to-global step for quasi-coherence.**  A sheaf of modules which has a global
presentation over every object of the site over which two given quasi-coherent sheaves of modules
both have one is itself quasi-coherent.

This is `SheafOfModules.IsQuasicoherentOnSite.of_hasGlobalPresentation_pair_of_coverDense` for
the identity functor, whose images are all the objects, so that the sieve of arrows factoring
through one of them is the maximal sieve. -/
theorem IsQuasicoherentOnSite.of_hasGlobalPresentation_pair
    {M N T : SheafOfModules.{m} R}
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite)
    (h : ∀ V : C, (M.over V).HasGlobalPresentation → (N.over V).HasGlobalPresentation →
      (T.over V).HasGlobalPresentation) :
    T.IsQuasicoherentOnSite :=
  IsQuasicoherentOnSite.of_hasGlobalPresentation_pair_of_coverDense (𝟭 C)
    (fun U => J.superset_covering (fun _ f _ => Presieve.in_coverByImage (𝟭 C) f) (J.top_mem U))
    hM hN h

/-! ### Sections of a morphism and of the projection to its cokernel -/

/-- **The image factorisation of a morphism of sheaves of modules, read on the sections over an
object.**  The canonical epimorphism onto `CategoryTheory.Abelian.image` followed by the
inclusion of that image — which is the inclusion of `CategoryTheory.Limits.kernel` of
`CategoryTheory.Limits.cokernel.π` — induces on the sections over an object the map induced
by the morphism itself.

This is `CategoryTheory.Abelian.image.fac` read on the sections over `X`: the equality of
morphisms of sheaves of modules is pushed to the sections by `CategoryTheory.ConcreteCategory`,
whose `congr_hom` is the concrete-category analogue of `congrFun`. -/
theorem val_app_factorThruImage {M N : SheafOfModules.{m} R} (f : M ⟶ N)
    [HasCokernel f] [HasKernel (cokernel.π f)] (X : Cᵒᵖ) (x : M.val.obj X) :
    (kernel.ι (cokernel.π f)).val.app X ((Abelian.factorThruImage f).val.app X x)
      = f.val.app X x :=
  ConcreteCategory.congr_hom
    (congrArg (fun φ => (SheafOfModules.Hom.val φ).app X) (Abelian.image.fac f)) x

/-- **Sections take a morphism and the projection to its cokernel to an exact pair, granted
that the sections of the morphism already fill its image.**

The kernel of `CategoryTheory.Limits.cokernel.π f` is the image of `f`, and sections take a
kernel to a kernel by `SheafOfModules.exact_val_app_of_isKernelIso`, so the sections of
`kernel.ι (cokernel.π f)` and of `cokernel.π f` form an exact pair unconditionally.  What the
hypothesis `hs` adds is that the image of the sections of `f` is all of that kernel: `f` factors
as the canonical epimorphism onto its image followed by the inclusion of the image, and `hs`
says the first factor is surjective on the sections over `X`.

For sheaves of modules on a site `hs` is a genuine cohomological input — the discrepancy is a
first cohomology group — and is not implied by the factor being an epimorphism. -/
theorem exact_val_app_cokernel_π {M N : SheafOfModules.{m} R} (f : M ⟶ N)
    [HasCokernel f] [HasKernel (cokernel.π f)] (X : Cᵒᵖ)
    (hs : Function.Surjective ((Abelian.factorThruImage f).val.app X)) :
    Function.Exact (f.val.app X) ((cokernel.π f).val.app X) := by
  have h0 : Function.Exact ((kernel.ι (cokernel.π f)).val.app X)
      ((cokernel.π f).val.app X) :=
    exact_val_app_of_isKernelIso (Iso.refl _) (Category.id_comp _) X
  intro y
  refine ⟨fun hy => ?_, ?_⟩
  · obtain ⟨z, hz⟩ := (h0 y).mp hy
    obtain ⟨x, hx⟩ := hs z
    exact ⟨x, by rw [← val_app_factorThruImage f X x, hx, hz]⟩
  · rintro ⟨x, rfl⟩
    exact (h0 _).mpr ⟨(Abelian.factorThruImage f).val.app X x,
      val_app_factorThruImage f X x⟩

end SheafOfModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **Cokernels of `𝒪_F`-modules exist.**  A morphism of sheaves of modules on the small étale
ringed site of an algebraic space `F`, with sections in the universe of the schemes, has a
cokernel.

This is the universe specialisation `m := u` of the first declaration of the statement of
Stacks 03M1; see the implementation notes for why the form with the module universe free
does not hold.  The content is that the small étale site has sheafification of
`AddCommGrpCat.{u}`-valued presheaves, which is
`AlgebraicGeometry.Space.smallEtaleRingedSite_hasSheafify`. -/
instance hasCokernel_modules {M N : Modules.{u, u} B S hS F hF} (f : M ⟶ N) : HasCokernel f :=
  inferInstance

/-- **The `𝒪_F`-modules with sections in the universe of the schemes have cokernels.**

This is the abelian structure `SheafOfModules.instAbelian` at the module universe `u`, which
needs sheafification of `AddCommGrpCat.{u}`-valued presheaves on the small étale site,
`AlgebraicGeometry.Space.smallEtaleRingedSite_hasSheafify`.  The abelian instance is named with
its universe because instance search tries it at the module universe `max (u + 1) ?w` and stops
at the universe constraint `u =?= max (u + 1) ?w` instead of backtracking.

It is not a global instance: with the module universe free, as in statements quantified over
`AlgebraicGeometry.Space.Modules.{u, m}`, instance search would try it and unify `m` with `u`.
A statement at the universe `u` makes it a local instance. -/
theorem hasCokernels_modules : HasCokernels (Modules.{u, u} B S hS F hF) :=
  let := SheafOfModules.instAbelian.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)
  inferInstance

/-- **The `𝒪_F`-modules with sections in the universe `u + 1` have cokernels**, the universe of
the internal homs `AlgebraicGeometry.Space.smallEtaleInternalHom`.

As for `AlgebraicGeometry.Space.hasCokernels_modules`, this is `SheafOfModules.instAbelian` named
at its module universe, here `u + 1`: left to instance search it stops at the universe constraint
`u + 1 =?= max (u + 1) ?w`, although `?w := u` solves it.  It is not a global instance, for
the same reason. -/
theorem hasCokernels_modules_succ : HasCokernels (Modules.{u, u + 1} B S hS F hF) :=
  let := SheafOfModules.instAbelian.{u + 1}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)
  inferInstance

/-- The affine étale charts of an algebraic space cover every étale chart: the arrows factoring
through an affine chart form a covering sieve.

This is the cover-density half of
`AlgebraicGeometry.Space.AffineEtale.inclusion_isSpecialCocontinuous`, Stacks 04JS, restated for
the underlying category and topology of `AlgebraicGeometry.Space.smallEtaleRingedSite`, which are
projections of a structure instance and so are not unfolded by instance search. -/
theorem coverByImage_affineEtaleInclusion_mem (U : (smallEtaleRingedSite B S hS F hF).C) :
    Sieve.coverByImage (AffineEtale.inclusion B S hS F) U ∈
      (smallEtaleRingedSite B S hS F hF).J U :=
  ((AffineEtale.inclusion_isSpecialCocontinuous B S hS F hF).2.isCoverDense').is_cover U

/-- **The cokernel of a morphism of quasi-coherent `𝒪_F`-modules is quasi-coherent, granted the
local cokernel step over affine charts.**  This is the universe specialisation `m := u` of the
second declaration of the statement of Stacks 03M1, with the local step `hlocal` carried
as a hypothesis — and asked only of the *affine* étale charts.

`hlocal` says that over an affine étale chart over which both `M` and `N` have global
presentations, so does the restriction of the cokernel.  Everything else is discharged by
`SheafOfModules.IsQuasicoherentOnSite.of_hasGlobalPresentation_pair_of_coverDense` against the
cover density of the affine charts.  See the implementation notes for why `hlocal` is not formal
and why no `@[stacks]` attribute is claimed. -/
theorem isQuasicoherentOnSite_cokernel_of_affineCharts {M N : Modules.{u, u} B S hS F hF}
    [M.IsQuasicoherentOnSite] [N.IsQuasicoherentOnSite] (f : M ⟶ N)
    (hlocal : ∀ V : (smallEtaleRingedSite B S hS F hF).C, IsAffineChart B S hS F V →
      (M.over V).HasGlobalPresentation → (N.over V).HasGlobalPresentation →
        ((cokernel f).over V).HasGlobalPresentation) :
    (cokernel f).IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_hasGlobalPresentation_pair_of_coverDense
    (AffineEtale.inclusion B S hS F) (coverByImage_affineEtaleInclusion_mem B S hS F hF)
    ‹M.IsQuasicoherentOnSite› ‹N.IsQuasicoherentOnSite›
    fun W => hlocal _ W.property

/-- **The cokernel of a morphism of quasi-coherent `𝒪_F`-modules is quasi-coherent, granted the
local cokernel step.**  The form of
`AlgebraicGeometry.Space.isQuasicoherentOnSite_cokernel_of_affineCharts` in which the local step
is asked of every étale chart; it is the weaker of the two statements, and is recorded because it
is the shape of the statement of Stacks 03M1. -/
theorem isQuasicoherentOnSite_cokernel {M N : Modules.{u, u} B S hS F hF}
    [M.IsQuasicoherentOnSite] [N.IsQuasicoherentOnSite] (f : M ⟶ N)
    (hlocal : ∀ V : (smallEtaleRingedSite B S hS F hF).C,
      (M.over V).HasGlobalPresentation → (N.over V).HasGlobalPresentation →
        ((cokernel f).over V).HasGlobalPresentation) :
    (cokernel f).IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_hasGlobalPresentation_pair
    ‹M.IsQuasicoherentOnSite› ‹N.IsQuasicoherentOnSite› hlocal

/-! ### The second route: through the base change criterion -/

/-- **The cokernel of a morphism of `𝒪_F`-modules cartesian on affine charts is quasi-coherent,
granted Stacks 03DW.**  This is the route through the base change criterion rather than through
presentations: `AlgebraicGeometry.Space.isCartesianOnAffineCharts_cokernel` makes the cokernel
cartesian on affine charts, and
`AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isCartesianOnAffineCharts` makes it
quasi-coherent unconditionally from there.

The two hypotheses are the sections-level content of Stacks 03DW over an affine chart `U`:
`hpi` is surjectivity there of the projection to the cokernel, and `him` surjectivity there of
the canonical epimorphism of `f` onto its image, which is what
`SheafOfModules.exact_val_app_cokernel_π` converts into the exactness of the sections.  They are
asked separately rather than through one hypothesis quantified over all epimorphisms because
that hypothesis is false, and they are not interchangeable: `him`'s side condition is discharged
by `hM` and `hN`, `hpi`'s is not.  See the implementation notes.

`M` and `N` are asked to be cartesian on affine charts rather than quasi-coherent, which is how
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_cokernel` wants them and is what lets this
form be stated without `h03DX`.  It is not a gain in generality:
`AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isCartesianOnAffineCharts` turns each of `hM`
and `hN` into quasi-coherence of `M` and of `N` unconditionally, so this form assumes at least
as much about them as `AlgebraicGeometry.Space.isQuasicoherentOnSite_cokernel_of_h03DX` does. -/
theorem isQuasicoherentOnSite_cokernel_of_isCartesian {M N : Modules.{u, u} B S hS F hF}
    (f : M ⟶ N) (hM : IsCartesianOnAffineCharts M) (hN : IsCartesianOnAffineCharts N)
    (hpi : ∀ U : SmallEtale B S hS F,
      IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U) →
        Function.Surjective ((cokernel.π f).val.app (Opposite.op U)))
    (him : ∀ U : SmallEtale B S hS F,
      IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U) →
        Function.Surjective ((Abelian.factorThruImage f).val.app (Opposite.op U))) :
    (cokernel f).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_isCartesianOnAffineCharts _
    (isCartesianOnAffineCharts_cokernel f (cokernel.π f) hpi
      (fun U hU => SheafOfModules.exact_val_app_cokernel_π f (Opposite.op U) (him U hU)) hM hN)

/-- **Stacks 03M1 for cokernels, at `m := u`, conditional on one implication of Stacks 03DX(2),
on Stacks 03DW, and on one statement bespoke to this clause.**  The cokernel of a morphism of
quasi-coherent `𝒪_F`-modules on an algebraic space is quasi-coherent.

This is the tagged statement along the base change route.  Its inputs are:

* `h03DX`, the implication "quasi-coherent ⟹ cartesian on affine charts" of Descent,
  Proposition 03DX(2), carried as

      (h03DX : ∀ G : Modules.{u, u} B S hS F hF,
        G.IsQuasicoherentOnSite → IsCartesianOnAffineCharts G)

  which is the spelling of `AlgebraicGeometry.Space.isQuasicoherent_left_of_shortExact` and of
  its two siblings verbatim, so that the same cited input serves all four conclusions with no
  adapter.  Its converse is *not* a hypothesis, being proved by
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isCartesianOnAffineCharts`.
* `hpi` and `him`, as in
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_cokernel_of_isCartesian`.

`hpi` and `him` are *deliberately not* consolidated into a hypothesis quantified over all
epimorphisms.  Such a hypothesis would be false: an epimorphism of modules is surjective on the
sections over an affine chart because the first cohomology there of its *kernel* vanishes, and
Stacks 03DW gives that vanishing only for a quasi-coherent kernel.  Nor are the two on the same
footing.  The kernel of `CategoryTheory.Abelian.factorThruImage f` is the kernel of `f`, which
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_kernel` makes cartesian — from the
cartesianness that `h03DX` extracts from `[M.IsQuasicoherentOnSite]` and
`[N.IsQuasicoherentOnSite]` — and
`AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isCartesianOnAffineCharts` then makes
quasi-coherent, so `him` is Stacks 03DW with its side condition discharged.  The kernel of
`CategoryTheory.Limits.cokernel.π f` is the image of `f`, whose quasi-coherence is not available
here, so `hpi` is the genuinely open input and the one bespoke to this clause.

Contrast `AlgebraicGeometry.Space.isQuasicoherentOnSite_cokernel_of_affineCharts`, which needs
no cohomological input but owes the presentation step `hlocal` instead. -/
theorem isQuasicoherentOnSite_cokernel_of_h03DX {M N : Modules.{u, u} B S hS F hF}
    [M.IsQuasicoherentOnSite] [N.IsQuasicoherentOnSite] (f : M ⟶ N)
    (h03DX : ∀ G : Modules.{u, u} B S hS F hF,
      G.IsQuasicoherentOnSite → IsCartesianOnAffineCharts G)
    (hpi : ∀ U : SmallEtale B S hS F,
      IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U) →
        Function.Surjective ((cokernel.π f).val.app (Opposite.op U)))
    (him : ∀ U : SmallEtale B S hS F,
      IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U) →
        Function.Surjective ((Abelian.factorThruImage f).val.app (Opposite.op U))) :
    (cokernel f).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_cokernel_of_isCartesian B S hS F hF f
    (h03DX M ‹M.IsQuasicoherentOnSite›) (h03DX N ‹N.IsQuasicoherentOnSite›) hpi him

end AlgebraicGeometry.Space

end
