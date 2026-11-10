module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Algebraic.Cardinality
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceBaseChange
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.CohenMacaulay.Source
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.PurityCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModule
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalkBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalkExactness
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.InjectiveQuasicoherentPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.OrbitSpaces.InvarianceOnOrbits
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleFlatTopos
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportGeometricStalkCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedChartSectionVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedTensorPullbackFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedVanishingQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Topologies.FiniteTypeFromGlobalGenerators
public import StacksFrontier.RingTheory.Flat.UniversallyInjective

/-!
# A flat morphism meeting the relative assassin separates

Let `Y` be an algebraic space over a scheme `S`, let `g : X' ⟶ X` be a flat morphism of
algebraic spaces over `Y` with `X` locally of finite type over `Y`, and let `F` be a finite
type quasi-coherent `𝒪_X`-module which is flat over `Y`.  Stacks 0CW6 asserts that if the
relative assassin `Ass_{X/Y}(F)` is contained in the image of `|X'|` then the canonical map

`F ⟶ g_*g^*F`

is injective, and remains injective after any base change.  This file proves **both
assertions**.

The canonical map is the unit of the adjunction `g^* ⊣ g_*` of Stacks 03LU,
`AlgebraicGeometry.Space.modulePullbackAdjunction`.  The relative assassin is
`AlgebraicGeometry.Space.relativeWeaklyAssociatedPoints` of Stacks 0CV0, which is the set the
source writes `Ass_{X/Y}(F)` whenever the fibres of `f` are locally Noetherian, as they are
here because `f` is locally of finite type (Stacks 0CUY).

## Main results

* `AlgebraicGeometry.Space.weaklyAssociatedPoints_subset_relativeWeaklyAssociatedPoints`:
  **Stacks 0CVL at `G = 𝒪_Y`**, that `WeakAss_X(F) ⊆ Ass_{X/Y}(F)` for `F` flat over `Y`.
* `AlgebraicGeometry.Space.isZero_of_comp_unit_eq_zero`: a submodule of `F` killed by the
  canonical map is zero.  This is the whole geometric content of the source's proof, and it is
  proved here from the source's own inputs, for a submodule which is not assumed
  quasi-coherent.
* `AlgebraicGeometry.Space.mono_unit_of_relativeWeaklyAssociatedPoints_subset_range`:
  **Stacks 0CW6, injectivity**, the canonical map `F ⟶ g_*g^*F` is a monomorphism.
* `AlgebraicGeometry.Space.mono_unit_baseChange_of_relativeWeaklyAssociatedPoints_subset_range`:
  **Stacks 0CW6, the base-change assertion**, the same canonical map for the base change of the
  data along an arbitrary `Z ⟶ Y` is a monomorphism.

## Implementation notes

**The argument.**  Let `K ⟶ F` be a submodule killed by the unit `F ⟶ g_*g^*F`.  Because the
unit is the unit of an adjunction, the composite `K ⟶ F ⟶ g_*g^*F` is adjunct to the pullback
`g^*K ⟶ g^*F` of the inclusion, so that composite vanishes exactly when `g^*K ⟶ g^*F` does;
this replaces the source's computation of the stalk of a direct image, which this development
does not have in a usable form (see below).  Flatness of `g` makes `g^*` left exact
(Stacks 04JC, `AlgebraicGeometry.Space.preservesMonomorphisms_modulePullback_of_isFlat`), so
`g^*K ⟶ g^*F` is a monomorphism as well as zero, whence `g^*K = 0`.

Reading that off the geometric stalks with the base-change formula of Stacks 05VQ,
`AlgebraicGeometry.Space.geometricModuleStalkPullbackIso`, gives
`𝒪_{X', x̄'} ⊗_{𝒪_{X, g ∘ x̄'}} K_{g ∘ x̄'} = 0` at every geometric point `x̄'` of `X'`.  The
homomorphism of étale local rings along a flat morphism is flat (Stacks 04NG) and local
(Stacks 08AH), hence faithfully flat, so Stacks 05CK —
`faithfullyFlat_tensor_mk_injective` — makes `K_{g ∘ x̄'} ⟶ 𝒪_{X', x̄'} ⊗ K_{g ∘ x̄'}`
injective and therefore `K_{g ∘ x̄'} = 0`.

A weakly associated point of `K` is weakly associated to `F` (Stacks 0CTZ,
`AlgebraicGeometry.Space.weaklyAssociatedPoints_subset_of_mono`), hence lies in
`Ass_{X/Y}(F)`, hence is the image of a point of `X'`; the geometric stalk of `K` above it
vanishes by the previous paragraph, while a weakly associated point lies in the support
(Stacks 0CTY) where the stalk at *every* geometric point above it is nonzero (Stacks 07TZ,
part (2)).  So `WeakAss(K) = ∅`, and `K = 0` by Stacks 0CU0.

Both of those last two steps are statements about a *quasi-coherent* module, and `K` — a
subsheaf of `F` cut out by a vanishing condition — is not one.  The reduction to a
quasi-coherent module is the source's own localisation, carried out in
`StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedChartSectionVanishing` and applied here
as `AlgebraicGeometry.Space.eq_zero_of_forall_exists_subsingleton_geometricModuleStalk`: a
section of `K` over an étale chart `V` is a global section of the restriction of `K` to the
algebraic space `V` presents, the submodule of `F|_V` it generates is the image of a morphism
out of the structure sheaf and so is quasi-coherent unconditionally, and the two steps above are
taken there.  That is why the statements below carry no hypothesis on the kernel.

**Deviation: the module universe is the universe of the schemes.**  As everywhere in this
development, `AlgebraicGeometry.Space.Modules.{u, u}` is used rather than a free module
universe: the abelian structure, hence kernels, is available only there.  This is a
specialisation of the source statement, not a weakening of it.

**Two inputs that are not carried.**  Both are discharged from results of the library, so
neither appears in the statements.

* `WeakAss_X(F) ⊆ Ass_{X/Y}(F)`, which is Stacks 0CVL taken at `G = 𝒪_Y`, is
  `AlgebraicGeometry.Space.weaklyAssociatedPoints_subset_relativeWeaklyAssociatedPoints` below.
  The development's Stacks 0CVL,
  `AlgebraicGeometry.Space.weaklyAssociatedPoints_tensor_modulePullback_eq_inter_preimage` in
  `StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedTensorPullbackFiniteType`, is
  unconditional — the pointwise Bourbaki formula of Stacks 0CVK it rests on is carried in its
  own generality as
  `AlgebraicGeometry.Space.isWeaklyAssociatedPoint_tensor_modulePullback_iff_of_finiteType` in
  `StacksFrontier.AlgebraicGeometry.Spaces.Flat.BourbakiFiniteTypePointwise` — and the
  specialisation to `G = 𝒪_Y` needs only that `F ⊗_{𝒪_X} f^*𝒪_Y ≅ F`, which is
  `AlgebraicGeometry.Space.modulePullbackUnitIso` of Stacks 03LU together with the right
  unitor.  It consumes the tag's hypotheses `hf` and `hF`, exactly as Stacks 0CVL does.
* `WeakAss(K) = ∅ → K = 0`, the substantive direction of Stacks 0CU0, is
  `AlgebraicGeometry.Space.isZero_of_weaklyAssociatedPoints_eq_empty` in
  `StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedVanishingQuasicoherent`, for a
  quasi-coherent module.  Older notes in this development describing it as missing — "a
  nonempty support contains a weakly associated point" — predate that landing.

A further input, that every point of `|X'|` is the image of a geometric point of `X'`, is
*not* carried: it is proved here as
`AlgebraicGeometry.Space.exists_geometricPoint_liesOver`, Stacks 0486 with Stacks 04JW.  It is
needed because the support of Stacks 04KA is defined by nonvanishing of the stalk at *some*
geometric point above a point, so the argument has to produce a geometric point of `X'` over
the point of `|X'|` that the containment hypothesis supplies.  Its auxiliary declarations —
the algebraic closure of a field-valued point, as an object of the site and as a field-valued
point itself — restate a chain of `private` declarations of the same shape in
`StacksFrontier.AlgebraicGeometry.Spaces.Quotients.OrbitSpaces.InvarianceOnOrbits`, which a
`private` name makes unusable from outside that file.

**Why the kernel is handled one section at a time.**  The kernel of the canonical map is *not* a
quasi-coherent module for a general flat `g`, so neither Stacks 0CU0 nor Stacks 07TZ(2) can be
applied to it, and the kernel clause of Stacks 03M1(3),
`AlgebraicGeometry.Space.isQuasicoherentOnSite_kernel_of_quasicoherent`, does not help: it asks
for *both* ends of the map to be quasi-coherent, and the target `g_*g^*F` is quasi-coherent only
by Stacks 03M9, for `g` quasi-compact and quasi-separated — hypotheses Stacks 0CW6 does not
have, and which this development carries only as the named property
`AlgebraicGeometry.Space.PushforwardPreservesQuasicoherence` or as the chartwise exact sequence
of `AlgebraicGeometry.Space.pushforward_isQuasicoherentOnSite_of_chartwiseKernel`.

The failure is genuine and not an artefact of this development.  Quasi-coherence of
`Ker(F → g_*g^*F)` on an affine étale chart `V = Spec A` amounts, through Stacks 03DX, to
injectivity of the flat base-change map `Γ(X'_V, g^*F) ⊗_A A' → Γ(X'_{V'}, g^*F)` along an
étale `A → A'`, and for `X'_V` neither quasi-compact nor quasi-separated that map need not be
injective: already for `A' = A_f` and `X'_V` an infinite disjoint union, annihilating a section
of each summand by a power of `f` needs no uniform exponent.

What is quasi-coherent is the submodule of `F` generated by *one* section over *one* chart, read
on that chart as an algebraic space (`AlgebraicGeometry.Space.chartSpace`,
`AlgebraicGeometry.Space.chartToSpace`), where the section is global: it is then the image of a
morphism out of the structure sheaf, and the image of a morphism of quasi-coherent modules is
quasi-coherent with no further hypothesis.  Nothing of the direct image is needed for that —
only the étale pullback, and the stalk hypothesis moves to the chart space along Stacks 05VN and
Stacks 0CUU.  That localisation is
`AlgebraicGeometry.Space.eq_zero_of_forall_exists_subsingleton_geometricModuleStalk` of
`StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedChartSectionVanishing`, and it is what
makes the statements below carry nothing beyond the tag's own hypotheses.

**The base-change assertion.**  Stacks 0CW6 also asserts that the injection persists after an
arbitrary base change `Z ⟶ Y`, which the source deduces from the first half because the
containment hypothesis survives base change (Stacks 0CW2,
`AlgebraicGeometry.Space.relativeWeaklyAssociatedPoints_baseChange_subset_range` in
`StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceBaseChange`).  That
deduction is carried out below in
`AlgebraicGeometry.Space.mono_unit_baseChange_of_relativeWeaklyAssociatedPoints_subset_range`:
besides Stacks 0CW2 it uses the stability under base change of local finite type (Stacks 03XH),
of flatness of `g` (Stacks 03MO), of quasi-coherence (Stacks 03GA) and finite type
(Stacks 03DL(5)) of the module, and of flatness of the module over the target (Stacks 05VW).
All six are in the library; the base changes are presented by cartesian squares, `X_Z` as `X ×_Y Z`
and `X'_Z` as `X_Z ×_X X'`, as the source's proof presents them.

## References

* [Stacks Project, Tag 0CW6](https://stacks.math.columbia.edu/tag/0CW6)
* [Stacks Project, Tag 0CU0](https://stacks.math.columbia.edu/tag/0CU0)
* [Stacks Project, Tag 0CTZ](https://stacks.math.columbia.edu/tag/0CTZ)
* [Stacks Project, Tag 0CTY](https://stacks.math.columbia.edu/tag/0CTY)
* [Stacks Project, Tag 0CUU](https://stacks.math.columbia.edu/tag/0CUU)
* [Stacks Project, Tag 0CVL](https://stacks.math.columbia.edu/tag/0CVL)
* [Stacks Project, Tag 0CVK](https://stacks.math.columbia.edu/tag/0CVK)
* [Stacks Project, Tag 0CW2](https://stacks.math.columbia.edu/tag/0CW2)
* [Stacks Project, Tag 05CK](https://stacks.math.columbia.edu/tag/05CK)
* [Stacks Project, Tag 05VN](https://stacks.math.columbia.edu/tag/05VN)
* [Stacks Project, Tag 05VQ](https://stacks.math.columbia.edu/tag/05VQ)
* [Stacks Project, Tag 05VW](https://stacks.math.columbia.edu/tag/05VW)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
* [Stacks Project, Tag 07TZ](https://stacks.math.columbia.edu/tag/07TZ)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 03M9](https://stacks.math.columbia.edu/tag/03M9)
* [Stacks Project, Tag 03MO](https://stacks.math.columbia.edu/tag/03MO)
* [Stacks Project, Tag 03XH](https://stacks.math.columbia.edu/tag/03XH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The abelian structure of the `𝒪_X`-modules with sections in the universe of the schemes,
written out instead of being found by instance search.

It is the term instance search returns, namely `SheafOfModules.instAbelian` fed the two
sheafification instances of `StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian`, so nothing
is changed by using it.  The search itself is unusable in a file importing
`StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentKernelsAndCokernels`, as this one does: the
two sheafification instances it declares for every universe of module sections containing the
objects of the site have a universe parameter occurring only inside a `max`, so matching them
against a goal at the universe of the schemes leaves an unsolvable universe constraint
postponed rather than failing.

This restates, under a name of its own, the `private` declaration of the same shape in
`StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalkExactness`. -/
@[instance_reducible] noncomputable def spaceModulesAbelianWrittenOut
    (X : AlgebraicSpaces B S hS) : Abelian (Modules.{u, u} B S hS X.1 X.2) :=
  @SheafOfModules.instAbelian _ _ _ _ (smallEtaleRingedSite_hasSheafify B S hS X.1 X.2)
    (smallEtaleRingedSite_wEqualsLocallyBijective B S hS X.1 X.2)

attribute [local instance 10000] spaceModulesAbelianWrittenOut

/-! ### Stacks 0CVL at `G = 𝒪_Y`: the weak assassin sits inside the relative assassin -/

section Bourbaki

open MonoidalCategory

attribute [local instance] modulesMonoidalCategory

/-- Tensoring with the inverse image of the structure sheaf of the target changes nothing:
`F ⊗_{𝒪_X} f^*𝒪_Y ≅ F`.

The inverse image of `𝒪_Y` is `𝒪_X` by Stacks 03LU,
`AlgebraicGeometry.Space.modulePullbackUnitIso`, and `𝒪_X` is the unit of the tensor product of
Stacks 01CA on the nose, by `AlgebraicGeometry.Space.modulesTensorUnit_eq`, so the right unitor
finishes. -/
noncomputable def tensorModulePullbackUnitIso {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    F ⊗ (modulePullback B S hS f).obj (𝟙_ (Modules.{u, u} B S hS Y.1 Y.2)) ≅ F :=
  whiskerLeftIso F (eqToIso (by rw [modulesTensorUnit_eq]) ≪≫
    modulePullbackUnitIso B S hS f ≪≫ eqToIso (by rw [modulesTensorUnit_eq])) ≪≫ ρ_ F

/-- **Stacks 0CVL at `G = 𝒪_Y`, in the form the tensor product can be eliminated from.**  For a
morphism `f : X ⟶ Y` of algebraic spaces locally of finite type and a finite type quasi-coherent
`𝒪_X`-module `F` flat over `Y`, there is a module isomorphic to `F` whose weakly associated
points lie in the relative assassin `Ass_{X/Y}(F)`, namely `F ⊗_{𝒪_X} f^*𝒪_Y`.

This is the specialisation of Bourbaki's formula,
`AlgebraicGeometry.Space.weaklyAssociatedPoints_tensor_modulePullback_eq_inter_preimage`, to
`G = 𝒪_Y`, whose right-hand side is contained in its first factor.  The structure sheaf is
quasi-coherent by Stacks 03DL(6), `SheafOfModules.isQuasicoherentOnSite_unit`, so the formula
applies with no hypothesis beyond the ones Stacks 0CVL itself carries. -/
theorem exists_iso_weaklyAssociatedPoints_subset_relativeWeaklyAssociatedPoints
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    [F.IsQuasicoherentOnSite] [F.IsFiniteType] (hF : IsFlatOver B S hS X.2 f.hom F) :
    ∃ G : Modules.{u, u} B S hS X.1 X.2, Nonempty (F ≅ G) ∧
      weaklyAssociatedPoints B S hS X G ⊆ relativeWeaklyAssociatedPoints B S hS f F := by
  have : (𝟙_ (Modules.{u, u} B S hS Y.1 Y.2)).IsQuasicoherentOnSite := by
    rw [modulesTensorUnit_eq]; infer_instance
  refine ⟨F ⊗ (modulePullback B S hS f).obj (𝟙_ (Modules.{u, u} B S hS Y.1 Y.2)),
    ⟨(tensorModulePullbackUnitIso B S hS f F).symm⟩, ?_⟩
  rw [weaklyAssociatedPoints_tensor_modulePullback_eq_inter_preimage B S hS f hf F _ hF]
  exact Set.inter_subset_left

end Bourbaki

/-- **Stacks 0CVL at `G = 𝒪_Y`.**  For a morphism `f : X ⟶ Y` of algebraic spaces locally of
finite type and a finite type quasi-coherent `𝒪_X`-module `F` flat over `Y`, every weakly
associated point of `F` lies in the relative assassin `Ass_{X/Y}(F)`.

Bourbaki's formula at `G = 𝒪_Y` computes the weakly associated points of `F ⊗_{𝒪_X} f^*𝒪_Y`,
which is isomorphic to `F`; the weakly associated points of isomorphic modules agree, by
Stacks 0CTZ in both directions. -/
theorem weaklyAssociatedPoints_subset_relativeWeaklyAssociatedPoints
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    [F.IsQuasicoherentOnSite] [F.IsFiniteType] (hF : IsFlatOver B S hS X.2 f.hom F) :
    weaklyAssociatedPoints B S hS X F ⊆ relativeWeaklyAssociatedPoints B S hS f F := by
  obtain ⟨G, ⟨e⟩, hG⟩ :=
    exists_iso_weaklyAssociatedPoints_subset_relativeWeaklyAssociatedPoints B S hS f hf F hF
  have : Mono e.hom :=
    ⟨fun {_} a b h => by
      simpa [Category.assoc] using congrArg (fun k => k ≫ e.inv) h⟩
  exact (weaklyAssociatedPoints_subset_of_mono B S hS e.hom).trans hG

/-! ### Every point of an algebraic space lies under a geometric point -/

section GeometricLift

variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The field extension from the field of a field-valued point to its algebraic closure. -/
noncomputable abbrev algClosureSpecMapOfFieldValuedPoint (q : FieldValuedPoint B S hS F) :
    Spec (.of (AlgebraicClosure q.carrier)) ⟶ Spec (.of q.carrier) :=
  Spec.map (CommRingCat.ofHom (algebraMap q.carrier (AlgebraicClosure q.carrier)))

/-- The object of the site given by the algebraic closure of the field of a field-valued
point, over the base through the point's own structure morphism. -/
noncomputable abbrev algClosureSiteObjectOfFieldValuedPoint (q : FieldValuedPoint B S hS F) :
    BigFppfOver B S hS :=
  Over.mk (⟨algClosureSpecMapOfFieldValuedPoint B S hS q ≫ q.toBase⟩ :
    B.obj (contains_spec_algClosure q) ⟶ B.obj hS)

/-- The field extension to the algebraic closure, as a morphism of the objects of the site. -/
noncomputable def algClosureHomOfFieldValuedPoint (q : FieldValuedPoint B S hS F) :
    algClosureSiteObjectOfFieldValuedPoint B S hS q ⟶ q.siteObject B S hS F :=
  Over.homMk (⟨algClosureSpecMapOfFieldValuedPoint B S hS q⟩ :
    B.obj (contains_spec_algClosure q) ⟶ B.obj q.contained) rfl

/-- The restriction of a field-valued point to an algebraic closure of its field. -/
noncomputable def algClosurePointOfFieldValuedPoint (q : FieldValuedPoint B S hS F) :
    FieldValuedPoint B S hS F where
  carrier := AlgebraicClosure q.carrier
  contained := contains_spec_algClosure q
  toBase := algClosureSpecMapOfFieldValuedPoint B S hS q ≫ q.toBase
  value := F.map (algClosureHomOfFieldValuedPoint B S hS q).op q.value

/-- **Every point of an algebraic space is the image of a geometric point**: a field-valued
representative of it is dominated by its restriction to an algebraic closure of its field,
which is a geometric point by construction and defines the same point.

This is Stacks 0486 together with Stacks 04JW, in the form the argument below needs: the
support of Stacks 04KA is defined by nonvanishing of the stalk at *some* geometric point above
a point, so a geometric point above a given point has to be produced. -/
theorem exists_geometricPoint_liesOver (x : points B S hS F) :
    ∃ xbar : GeometricPoint B S hS F, xbar.LiesOver x := by
  obtain ⟨q, rfl⟩ := Quot.exists_rep x
  refine ⟨⟨algClosurePointOfFieldValuedPoint B S hS q,
    AlgebraicClosure.isAlgClosed q.carrier⟩, ?_⟩
  exact FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS F
    ⟨algClosurePointOfFieldValuedPoint B S hS q, FieldValuedPoint.dominates_refl B S hS F _,
      ⟨algClosureHomOfFieldValuedPoint B S hS q, rfl⟩⟩

end GeometricLift

/-! ### The geometric stalks of a submodule killed by the canonical map -/

/-- **A submodule of `F` killed by the canonical map `F ⟶ g_*g^*F` has vanishing geometric
stalk above every point of `|X'|`.**

The composite `K ⟶ F ⟶ g_*g^*F` is adjunct to the pullback `g^*K ⟶ g^*F` of the inclusion, so
the latter vanishes; flatness of `g` makes it a monomorphism as well, so `g^*K = 0`.  The
base-change formula of Stacks 05VQ turns this into the vanishing of
`𝒪_{X', x̄'} ⊗_{𝒪_{X, g ∘ x̄'}} K_{g ∘ x̄'}`, and the homomorphism of étale local rings is
faithfully flat — flat by Stacks 04NG and local by Stacks 08AH — so Stacks 05CK makes
`K_{g ∘ x̄'}` a submodule of that tensor product. -/
theorem subsingleton_geometricModuleStalk_of_comp_unit_eq_zero
    {X' X : AlgebraicSpaces B S hS} (g : X' ⟶ X) (hg : IsFlat B S hS g.hom)
    {F K : Modules.{u, u} B S hS X.1 X.2} (ι : K ⟶ F) [Mono ι]
    (hι : ι ≫ (modulePullbackAdjunction B S hS g).unit.app F = 0)
    (xbar : GeometricPoint B S hS X'.1) :
    Subsingleton (geometricModuleStalk B S hS X (geometricPointMap g.hom xbar) K) := by
  have hflat := (isFlat_iff_smallEtaleRingedToposHom_isFlat B S hS g).1 hg
  have hmono : (modulePullback B S hS g).PreservesMonomorphisms :=
    preservesMonomorphisms_modulePullback_of_isFlat B S hS g hflat
  have hright : (modulePushforward B S hS g).IsRightAdjoint :=
    ⟨_, ⟨modulePullbackAdjunction B S hS g⟩⟩
  -- The pullback of the inclusion vanishes, by adjunction.
  have hpull : (modulePullback B S hS g).map ι = 0 := by
    refine ((modulePullbackAdjunction B S hS g).homEquiv K
      ((modulePullback B S hS g).obj F)).injective ?_
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
      (modulePullbackAdjunction B S hS g).unit_naturality ι, Functor.map_zero, comp_zero, hι]
  -- Being a monomorphism as well, it has zero source.
  have hzero : IsZero ((modulePullback B S hS g).obj K) := by
    have hm : Mono ((modulePullback B S hS g).map ι) := (modulePullback B S hS g).map_mono ι
    refine (IsZero.iff_id_eq_zero _).mpr ?_
    exact (Preadditive.mono_iff_cancel_zero _).1 hm _
      (𝟙 ((modulePullback B S hS g).obj K)) (by rw [Category.id_comp]; exact hpull)
  -- Hence all its geometric stalks vanish, and the base-change formula transports this.
  have hstalk := (isZero_iff_subsingleton_geometricModuleStalk B S hS X'
    ((modulePullback B S hS g).obj K)).1 hzero xbar
  have hext : Subsingleton ((ModuleCat.extendScalars
      (etaleLocalRingMap X'.2 g.hom xbar)).obj
        (geometricModuleStalk B S hS X (geometricPointMap g.hom xbar) K)) :=
    (Equiv.ofBijective _ (ConcreteCategory.bijective_of_isIso
      (geometricModuleStalkPullbackIso B S hS g xbar K).hom)).symm.subsingleton
  -- Faithful flatness of the étale local rings, and Stacks 05CK.
  let φ := etaleLocalRingMap X'.2 g.hom xbar
  let _ : Algebra ↥(etaleLocalRing B S hS X.1 (geometricPointMap g.hom xbar))
      ↥(etaleLocalRing B S hS X'.1 xbar) := φ.toAlgebra
  let _ : IsLocalRing ↥(etaleLocalRing B S hS X.1 (geometricPointMap g.hom xbar)) :=
    isLocalRing_etaleLocalRing B S hS X.1 X.2 _
  let _ : IsLocalRing ↥(etaleLocalRing B S hS X'.1 xbar) :=
    isLocalRing_etaleLocalRing B S hS X'.1 X'.2 xbar
  have : Module.Flat ↥(etaleLocalRing B S hS X.1 (geometricPointMap g.hom xbar))
      ↥(etaleLocalRing B S hS X'.1 xbar) :=
    flat_etaleLocalRingMap B S hS X'.2 X.2 g.hom hg xbar
  have : IsLocalHom (algebraMap
      ↥(etaleLocalRing B S hS X.1 (geometricPointMap g.hom xbar))
      ↥(etaleLocalRing B S hS X'.1 xbar)) := by
    rw [RingHom.algebraMap_toAlgebra]
    exact isLocalHom_etaleLocalRingMap B S hS X'.2 X.2 g.hom xbar
  have hff : Module.FaithfullyFlat
      ↥(etaleLocalRing B S hS X.1 (geometricPointMap g.hom xbar))
      ↥(etaleLocalRing B S hS X'.1 xbar) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hinj := faithfullyFlat_tensor_mk_injective φ hff
    ↥(geometricModuleStalk B S hS X (geometricPointMap g.hom xbar) K)
  have hten : Subsingleton (TensorProduct
      ↥(etaleLocalRing B S hS X.1 (geometricPointMap g.hom xbar))
      ↥(etaleLocalRing B S hS X'.1 xbar)
      ↥(geometricModuleStalk B S hS X (geometricPointMap g.hom xbar) K)) := hext
  exact ⟨fun a b => hinj (hten.elim _ _)⟩

/-! ### A submodule killed by the canonical map vanishes -/

/-- **A submodule of `F` killed by the canonical map `F ⟶ g_*g^*F` is zero.**  This is the
geometric content of Stacks 0CW6, and the submodule is **not** assumed quasi-coherent.

Each section of `K` over an étale chart vanishes, by
`AlgebraicGeometry.Space.eq_zero_of_forall_exists_subsingleton_geometricModuleStalk`: its two
hypotheses are that the weakly associated points of `F` are carried by the image of `|X'|` —
Stacks 0CVL at `G = 𝒪_Y`, proved above, followed by `hass` — and that above every point of that
image some geometric stalk of `K` vanishes, which is
`AlgebraicGeometry.Space.subsingleton_geometricModuleStalk_of_comp_unit_eq_zero` at a geometric
point of `X'` over a point of `|X'|` above it. -/
theorem isZero_of_comp_unit_eq_zero
    {X' X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : X' ⟶ X)
    (hf : IsLocallyOfFiniteType B S hS f.hom) (hg : IsFlat B S hS g.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite] [F.IsFiniteType]
    (hF : IsFlatOver B S hS X.2 f.hom F)
    (hass : relativeWeaklyAssociatedPoints B S hS f F ⊆
      Set.range (pointsMap B S hS X'.1 g.hom))
    {K : Modules.{u, u} B S hS X.1 X.2} (ι : K ⟶ F) [Mono ι]
    (hι : ι ≫ (modulePullbackAdjunction B S hS g).unit.app F = 0) :
    IsZero K := by
  have hstalk : ∀ x ∈ Set.range (pointsMap B S hS X'.1 g.hom),
      ∃ xbar : GeometricPoint B S hS X.1, xbar.LiesOver x ∧
        Subsingleton (geometricModuleStalk B S hS X xbar K) := by
    rintro x ⟨x', hx'⟩
    obtain ⟨xbar, hxbar⟩ := exists_geometricPoint_liesOver B S hS x'
    refine ⟨geometricPointMap g.hom xbar, ?_,
      subsingleton_geometricModuleStalk_of_comp_unit_eq_zero B S hS g hg ι hι xbar⟩
    rw [GeometricPoint.LiesOver, geometricPointMap_image, hxbar, hx']
  refine isZero_of_subsingleton_val_obj B S hS X K fun V => ⟨fun a b => ?_⟩
  have key : ∀ c : K.val.obj V, c = 0 := fun c =>
    eq_zero_of_forall_exists_subsingleton_geometricModuleStalk B S hS ι
      (Set.range (pointsMap B S hS X'.1 g.hom))
      ((weaklyAssociatedPoints_subset_relativeWeaklyAssociatedPoints B S hS f hf F hF).trans hass)
      hstalk V.unop c
  exact (key a).trans (key b).symm

/-! ### Stacks 0CW6, the injectivity half -/

/-- **Stacks 0CW6, injectivity.**  Let `Y` be an algebraic space over a scheme `S`, let
`g : X' ⟶ X` be a flat morphism of algebraic spaces over `Y` with `X` locally of finite type
over `Y` through `f : X ⟶ Y`, and let `F` be a finite type quasi-coherent `𝒪_X`-module which is
flat over `Y`.  If the relative assassin `Ass_{X/Y}(F)` is contained in the image of `|X'|`
then the canonical map `F ⟶ g_*g^*F` — the unit of the adjunction of Stacks 03LU — is a
monomorphism.

The kernel of the canonical map is zero by
`AlgebraicGeometry.Space.isZero_of_comp_unit_eq_zero`, which is the source's argument; the
hypotheses are the tag's own. -/
@[stacks 0CW6 "the injectivity assertion"]
theorem mono_unit_of_relativeWeaklyAssociatedPoints_subset_range
    {X' X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : X' ⟶ X)
    (hf : IsLocallyOfFiniteType B S hS f.hom) (hg : IsFlat B S hS g.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite] [F.IsFiniteType]
    (hF : IsFlatOver B S hS X.2 f.hom F)
    (hass : relativeWeaklyAssociatedPoints B S hS f F ⊆
      Set.range (pointsMap B S hS X'.1 g.hom)) :
    Mono ((modulePullbackAdjunction B S hS g).unit.app F) :=
  (Preadditive.mono_iff_isZero_kernel _).mpr
    (isZero_of_comp_unit_eq_zero B S hS f g hf hg F hF hass (kernel.ι _) (kernel.condition _))

/-! ### Stacks 0CW6, the base-change half -/

/-- **Stacks 0CW6, injectivity after an arbitrary base change.**  In the situation of
Stacks 0CW6, for every morphism `h : Z ⟶ Y` the canonical map
`F_Z ⟶ (g_Z)_*g_Z^*F_Z` is a monomorphism as well.

The base changes are presented by cartesian squares, `X_Z` as `X ×_Y Z` and `X'_Z` as
`X_Z ×_X X'`, exactly as the source's proof does, so `g` is not required to be given as a
morphism over `Y`.  This is the source's own deduction: every hypothesis of the first half
survives the base change, and the containment of the relative assassin does so by
Stacks 0CW2.  Concretely

* `f_Z : X_Z ⟶ Z` is locally of finite type by Stacks 03XH;
* `g_Z : X'_Z ⟶ X_Z` is flat by Stacks 03MO;
* `F_Z = p^*F` is quasi-coherent by Stacks 03GA and of finite type by Stacks 03DL(5), both
  with no hypothesis on `p`;
* `F_Z` is flat over `Z` by Stacks 05VW;
* `Ass_{X_Z/Z}(F_Z) ⊆ g_Z(|X'_Z|)` by Stacks 0CW2.

All five are proved, so the hypotheses are the tag's own. -/
@[stacks 0CW6 "the base-change assertion"]
theorem mono_unit_baseChange_of_relativeWeaklyAssociatedPoints_subset_range
    {X' X Y Z XZ X'Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : X' ⟶ X) (h : Z ⟶ Y)
    (p : XZ ⟶ X) (fZ : XZ ⟶ Z) (q : X'Z ⟶ X') (gZ : X'Z ⟶ XZ)
    (hp : IsPullback p fZ f h) (hq : IsPullback q gZ g p)
    (hf : IsLocallyOfFiniteType B S hS f.hom) (hg : IsFlat B S hS g.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite] [F.IsFiniteType]
    (hF : IsFlatOver B S hS X.2 f.hom F)
    (hass : relativeWeaklyAssociatedPoints B S hS f F ⊆
      Set.range (pointsMap B S hS X'.1 g.hom)) :
    Mono ((modulePullbackAdjunction B S hS gZ).unit.app
      ((modulePullback B S hS p).obj F)) := by
  have : ((modulePullback B S hS p).obj F).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS p F inferInstance
  have : ((modulePullback B S hS p).obj F).IsFiniteType :=
    Stacks.SheafOfModules.isFiniteType_of_isFiniteTypeOnSite _
      (isFiniteTypeOnSite_modulePullback B S hS p F
        (Stacks.SheafOfModules.isFiniteTypeOnSite_of_isFiniteType F inferInstance))
  have hfZ : IsLocallyOfFiniteType B S hS fZ.hom :=
    IsLocallyOfFiniteType.of_isPullback B S hS (AlgebraicSpaces.isPullback_hom B S hS hp.flip)
      X.property Y.property hf
  have hgZ : IsFlat B S hS gZ.hom :=
    (isFlat_isStableUnderBaseChange B S hS).of_isPullback hq hg
  exact mono_unit_of_relativeWeaklyAssociatedPoints_subset_range B S hS fZ gZ hfZ hgZ
    ((modulePullback B S hS p).obj F) (isFlatOver_modulePullback B S hS hp F hF)
    (relativeWeaklyAssociatedPoints_baseChange_subset_range B S hS
      (AlgebraicSpaces.isPullback_hom B S hS hp)
      (AlgebraicSpaces.isPullback_hom B S hS hq.flip) F hass)

end AlgebraicGeometry.Space

end
