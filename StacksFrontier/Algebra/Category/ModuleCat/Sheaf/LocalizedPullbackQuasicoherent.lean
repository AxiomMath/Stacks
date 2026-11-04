module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackGlobalPresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalTypesUnderComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.FiniteLocallyFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.LocalGeneration
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.LocallyFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.Quasicoherence
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.PullbackToposSquare
import StacksCore.Tactic.StacksAttribute

/-!
# Pullback along the localized morphism of ringed topoi

Let `(f, f♯) : (C, O) ⟶ (D, O')` be a morphism of ringed sites whose underlying functor
`u : D ⥤ C` is left exact, let `F` be a sheaf of `O'`-modules and let `{W_i}` be a family of
objects of `D` covering the final object.  Setting `U_i = u(W_i)`, the family `{U_i}` covers the
final object of `C`, and the localized morphism of ringed topoi
`f_i : (Sh(C/U_i), O_{U_i}) ⟶ (Sh(D/W_i), O'_{W_i})` of Stacks 04J0 carries `F|_{W_i}` to
`(f^*F)|_{U_i}`.  Pullback along `f_i` preserves colimits and carries the structure sheaf to the
structure sheaf.

Those four facts — the covering, the functor, its colimit preservation and the two
identifications — are the whole of what Section 03DG of the source prescribes, and they mention
no property of modules.  Its condition (3) asks that a property be preserved by pullback along a
morphism of ringed sites given by a left exact continuous functor between sites having all
finite limits, and the functor that verification needs is the pullback along the localized
morphism of ringed topoi.  Once the datum is in hand, a property is carried across by whatever
colimits express it: a global presentation of `F|_{W_i}` becomes one of `(f^*F)|_{U_i}`, so
`f^*F` is quasi-coherent; a finite free cofan on `F|_{W_i}` becomes one on `(f^*F)|_{U_i}`, so
`f^*F` is finite locally free.  This file supplies the datum and both consumers.

`Stacks.SheafOfModules.QuasicoherentData.MapData` is the shape in which the quasi-coherent
consumer is phrased, and it is the step whose absence the implementation notes of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ToposPullbackGlobalPresentation.lean` record.

## Main definitions

* `Stacks.Sheaves.LocalizedPullback.pullbackToposUnitIso`: the structure sheaf is its own
  pullback along a morphism of ringed sites.
* `Stacks.Sheaves.LocalizedPullback.localizedPullbackUnitIso` and
  `.localizedPullbackOverIso`, together with
  `.preservesColimitsOfSize_localizedPullbackTopos` and `.coversTop_mapObj`: **the localized
  pullback datum of Section 03DG, before any property of modules.** For each object `W` of the
  target site, the pullback along the localized morphism of ringed topoi of Stacks 04J0 carries
  the structure sheaf to the structure sheaf and `F|_W` to `(f^*F)|_{u(W)}`, it preserves
  colimits, and the images of a family covering the final object again cover the final object.
* `Stacks.Sheaves.LocalizedPullback.localizedPullbackMapData`: that datum packaged as the
  transport of quasi-coherent data for `F` on the target site to quasi-coherent data for `f^*F`
  on the source site.
## Main results

* `Stacks.Sheaves.LocalizedPullback.coversTop_map`: the image under a continuous functor of a
  family covering the final object covers the final object, provided the functor carries the
  final object to a final object.
* `Stacks.Sheaves.LocalizedPullback.isFiniteFree_map`, `.isFree_map`,
  `.isPresentedByGlobalSections_map` and `.generatingSections_map`: finite freeness, freeness on
  an arbitrary index type, a global presentation and a generating family of global sections of a
  sheaf of modules are each carried by a colimit-preserving functor that carries the structure
  sheaf to the structure sheaf.
* `Stacks.Sheaves.LocalizedPullback.isQuasicoherentOnSite_pullbackTopos_of_quasicoherentData`,
  `.hasGlobalPresentation_over_pullbackTopos` and `.isQuasicoherentOnSite_pullbackTopos`: **the
  quasi-coherent clause of Stacks 03DO for a morphism of ringed sites given by a left exact
  continuous functor.** The pullback of a quasi-coherent sheaf of modules is quasi-coherent.
* `Stacks.Sheaves.LocalizedPullback.isFiniteFree_over_pullbackTopos` and
  `.isFiniteLocallyFreeOnSite_pullbackTopos`: **the finite locally free clause of Stacks 03DO,
  clause 03DL (2), for a morphism of ringed sites given by a left exact continuous functor.**
  The pullback of a finite locally free sheaf of modules is finite locally free.
* `Stacks.Sheaves.LocalizedPullback.isFree_over_pullbackTopos` and
  `.isLocallyFreeOnSite_pullbackTopos`: **the locally free clause of Stacks 03DO, clause
  03DL (1), for such a morphism.** The pullback of a locally free sheaf of modules is locally
  free.
* `Stacks.Sheaves.LocalizedPullback.generatingSectionsPullbackTopos` and
  `.isLocallyGeneratedBySectionsOnSite_pullbackTopos`: **the locally generated clause of
  Stacks 03DO, clause 03DL (3), for such a morphism.** The pullback of a sheaf of modules
  locally generated by sections is locally generated by sections.

## Implementation notes

**Scope of the 03DO attribute.** Stacks 03DO states its seven clauses for an arbitrary morphism
of *ringed topoi*, and its proof reduces them, "according to the discussion in Section 18.18"
(Section 03DG), to a morphism of ringed *sites* presented by a left exact continuous functor
between sites having all finite limits.  What is proved here is exactly that case, which is
Section 03DG's condition (3), and each of the 03DO attributes below says so.  The reduction of
the general statement to it is carried out in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/LocalTypesToposPullback.lean`, where the four
clauses 03DL (1), (2), (3) and (6) are stated for an arbitrary morphism of ringed topoi —
`AlgebraicGeometry.RingedToposHom.isLocallyFreeOnSite_pullbackModules`,
`.isFiniteLocallyFreeOnSite_pullbackModules`,
`.isLocallyGeneratedBySectionsOnSite_pullbackModules` and
`.isQuasicoherentOnSite_pullbackModules` — by factoring the morphism with Stacks 03CR and
carrying the clause around the resulting square.  The two sibling clauses
`Stacks.Sheaves.LocalGeneration.pullbackModules_isLocallyGeneratedByOnSite` and
`Stacks.Sheaves.FinitePresentation.isFinitePresentation_pullbackModules` reach that generality
directly, by arguments that localize neither the sites nor the morphism; no such argument is
available for the clauses proved here, for the reason recorded in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ToposPullbackGlobalPresentation.lean` — neither a
presentation nor a free cofan nor a generating family is recorded by the sections of a sheaf of
sets, and so none of them transports along `f⁻¹`.

**How the general statement is reached.** Of the seven clauses, (4), (5) and (7) are proved for
an arbitrary morphism of ringed topoi elsewhere in the development; the four proved here are the
ringed-sites case, and they are what
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/LocalTypesToposPullback.lean` feeds into the
bottom arrow of the square of Stacks 03CR.  The factorization itself is
`AlgebraicGeometry.RingedToposHom.exists_twoSided_isDenseSubsite_morphismOfSites`, with
`.exists_oneSided_isDenseSubsite_of_isEquivalence` its addendum for an equivalence; the two
vertical arrows are crossed by
`AlgebraicGeometry.RingedToposHom.isLocallyFreeOnSite_pullbackModules_ofDenseSubsite` and its
three companions, through the identification
`AlgebraicGeometry.RingedToposHom.pullbackModulesIsoModuleRestriction` of the pullback along a
dense subsite inclusion with `Stacks.DenseSubsiteModules.moduleRestriction` up to restriction of
scalars, and through the invariance of each clause under restriction of scalars along an
isomorphism of sheaves of rings
(`Stacks.SheafOfModules.isLocallyFreeOnSite_restrictScalars_of_isIso` and its companions) and
under an isomorphism of sheaves of modules
(`Stacks.SheafOfModules.Intrinsic.isLocallyFreeOnSite_of_iso`, `.isFiniteLocallyFreeOnSite_of_iso`,
`.isLocallyGeneratedBySectionsOnSite_of_iso` and
`SheafOfModules.IsQuasicoherentOnSite.of_iso`).  Stacks 03DM for exactly these four clauses —
`Stacks.Sheaves.SpecialCocontinuous.isLocallyFreeOnSite_iff` and its companions — does not ask
the special cocontinuous functor to be full and faithful, which is the generality Stacks 03CR
supplies.  The middle morphism of ringed topoi is re-presented as an
`AlgebraicGeometry.RingedToposSiteHom`, the shape the theorems below consume, by
`AlgebraicGeometry.RingedToposSiteHom.ofMorphismOfSites`, whose structure map is the given one
followed by `Stacks.Sheaves.ToposPullback.restrictionCommRingIso`; the square itself becomes a
square of pullbacks of modules by
`AlgebraicGeometry.RingedToposHom.TwoIso.pullbackModulesIso` and
`.pullbackModulesCompIso`.

**Why no clause needs essential smallness.** Each clause is tested on a *single* family covering
the final object, by the corresponding clause of Stacks 03DN — for instance
`Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_iff_exists_cover_isFiniteFree` — whose two
directions already quantify over the covering family.  The alternative route for quasi-coherence,
through `Stacks.SheafOfModules.QuasicoherentData`, has to recover a
`SheafOfModules.Presentation` from the `SheafOfModules.HasGlobalPresentation` that
`SheafOfModules.IsQuasicoherentOnSite` records, and that recovery asks the slices of the site to
be essentially small; `.isQuasicoherentOnSite_pullbackTopos_of_quasicoherentData` is that route
and keeps the data as a hypothesis, while `.isQuasicoherentOnSite_pullbackTopos` takes the
Stacks 03DN route and so carries no smallness hypothesis at all.

**Cover preservation.** Stacks' notion of a continuous functor (Stacks 00WU) includes carrying
coverings to coverings, whereas Mathlib's `CategoryTheory.Functor.IsContinuous` asks only that
restriction along the functor preserve sheaves.  The two agree in the direction needed here, by
`CategoryTheory.CoverPreserving.of_isContinuous`, so `coversTop_map` assumes only Mathlib's
weaker condition.

**The three pullbacks.** The pullback used here is the site-presented
`AlgebraicGeometry.RingedToposSiteHom.pullbackTopos`, which is the one Stacks 04J0's
localization square is available for
(`AlgebraicGeometry.RingedSite.Hom.localizedPullbackToposSquare`).  Its unit isomorphism is
obtained from the one for the pullback of the modules development,
`Stacks.Sheaves.FinitePresentation.pullbackModulesUnitIso`, along the two comparisons
`AlgebraicGeometry.RingedToposHom.pullbackModulesViaComparisonIso` and
`AlgebraicGeometry.RingedSite.Hom.pullbackToposIso`; taking it this way rather than from
Mathlib's `SheafOfModules.pullbackObjUnitToUnit` avoids that map's finality hypothesis on the
underlying functor, which a morphism of sites need not satisfy.

## References

* [Stacks Project, Tag 03DG](https://stacks.math.columbia.edu/tag/03DG)
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 04J0](https://stacks.math.columbia.edu/tag/04J0)
* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
* [Stacks Project, Tag 03CR](https://stacks.math.columbia.edu/tag/03CR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Stacks.Sheaves.LocalizedPullback

/-! ### A covering of the final object travels along a continuous functor -/

section CoversTop

universe v₁ u₁ v₂ u₂

/-- **The image of a covering of the final object covers the final object.** If `u : D ⥤ C` is a
continuous functor of sites carrying a final object `T` of `D` to a final object of `C`, and the
family `Y : I → D` covers the final object of `D`, then the family `i ↦ u(Y i)` covers the final
object of `C`.

Continuity enters through `CategoryTheory.CoverPreserving.of_isContinuous`: the image under `u`
of the sieve of objects generated by `Y` on `T` is a covering sieve of `u(T)`, and it is
contained in the sieve of objects generated by `i ↦ u(Y i)`, since a map to `u(Z)` with `Z`
admitting a map to `Y i` composes to a map to `u(Y i)`. -/
@[sga "4 III 1.6" "special case"]
theorem coversTop_map {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} (u : D ⥤ C) [u.IsContinuous K J]
    (T : D) (hT : IsTerminal (u.obj T)) {I : Type*} {Y : I → D} (hY : K.CoversTop Y) :
    J.CoversTop fun i ↦ u.obj (Y i) := by
  rw [J.coversTop_iff_of_isTerminal (u.obj T) hT]
  refine J.superset_covering ?_
    ((CoverPreserving.of_isContinuous u K J).cover_preserve (hY T))
  rintro A g ⟨Z, p, h, ⟨i, ⟨b⟩⟩, rfl⟩
  exact ⟨i, ⟨h ≫ u.map b⟩⟩

end CoversTop

/-! ### Freeness travels along a colimit-preserving functor -/

section FiniteFree

universe w u₁ v₁ u₂ v₂

variable {C₁ : Type u₁} [Category.{v₁} C₁] {J₁ : GrothendieckTopology C₁}
  {R₁ : Sheaf J₁ RingCat.{w}}
  {C₂ : Type u₂} [Category.{v₂} C₂] {J₂ : GrothendieckTopology C₂}
  {R₂ : Sheaf J₂ RingCat.{w}}

/-- A coproduct cofan of the structure sheaf on `M` is carried by `G` and `ρ` to one on `N`. -/
private def isColimit_cofan_map_comp_iso {B : Type*}
    (G : SheafOfModules.{w} R₁ ⥤ SheafOfModules.{w} R₂)
    [PreservesColimitsOfShape (Discrete B) G]
    (η : G.obj (SheafOfModules.unit R₁) ≅ SheafOfModules.unit R₂)
    {M : SheafOfModules.{w} R₁} {N : SheafOfModules.{w} R₂} (ρ : G.obj M ≅ N)
    (ι : B → (SheafOfModules.unit R₁ ⟶ M)) (hc : IsColimit (Cofan.mk M ι)) :
    IsColimit (Cofan.mk N fun b ↦ η.inv ≫ G.map (ι b) ≫ ρ.hom) :=
  (Stacks.Sheaves.GlobalTypeComparison.isColimitCofanMap G η ι hc).ofIsoColimit
    (Cocone.ext ρ (by intro j; cases j; simp))

/-- **Finite freeness travels along a colimit-preserving functor carrying the structure sheaf to
the structure sheaf.** Let `G` be a functor of categories of sheaves of modules preserving
colimits and carrying `R₁` to `R₂`.  If a sheaf of `R₁`-modules `M` is finite free and `G.obj M`
is isomorphic to `N`, then `N` is finite free, of the same rank.

The cofan exhibiting `M` as a coproduct of copies of `R₁` is carried to one exhibiting `G.obj M`
as a coproduct of as many copies of `R₂` by
`Stacks.Sheaves.GlobalTypeComparison.isColimitCofanMap`, and `ρ` moves its point to `N`.

Unlike `Stacks.Sheaves.GlobalTypeComparison.isFiniteFree_iff`, which is an equivalence and so
asks `G` to be full and faithful, this is the single implication that a pullback supplies; and
it carries the identification `ρ` of the image with a module named independently of `G`, which
is what the localized pullback produces. -/
theorem isFiniteFree_map (G : SheafOfModules.{w} R₁ ⥤ SheafOfModules.{w} R₂)
    [PreservesColimitsOfSize.{0, 0} G]
    (η : G.obj (SheafOfModules.unit R₁) ≅ SheafOfModules.unit R₂)
    {M : SheafOfModules.{w} R₁} {N : SheafOfModules.{w} R₂}
    (ρ : G.obj M ≅ N) (h : _root_.SheafOfModules.IsFiniteFree R₁ M) :
    _root_.SheafOfModules.IsFiniteFree R₂ N := by
  obtain ⟨n, ι, ⟨hc⟩⟩ := (_root_.SheafOfModules.isFiniteFree_iff_exists_isColimit R₁ M).1 h
  refine (_root_.SheafOfModules.isFiniteFree_iff_exists_isColimit R₂ N).2
    ⟨n, fun b ↦ η.inv ≫ G.map (ι b) ≫ ρ.hom, ⟨?_⟩⟩
  exact isColimit_cofan_map_comp_iso G η ρ ι hc

/-- **Freeness travels along a colimit-preserving functor carrying the structure sheaf to the
structure sheaf.** Let `G` be a functor of categories of sheaves of modules preserving colimits
and carrying `R₁` to `R₂`.  If a sheaf of `R₁`-modules `M` is free and `G.obj M` is isomorphic
to `N`, then `N` is free, on the same index type.

This is `Stacks.Sheaves.LocalizedPullback.isFiniteFree_map` with the index type of the cofan
left arbitrary instead of `Fin n`, which is why colimits of the size of the module sections, and
not merely finite ones, have to be preserved. -/
theorem isFree_map (G : SheafOfModules.{w} R₁ ⥤ SheafOfModules.{w} R₂)
    [PreservesColimitsOfSize.{w, w} G]
    (η : G.obj (SheafOfModules.unit R₁) ≅ SheafOfModules.unit R₂)
    {M : SheafOfModules.{w} R₁} {N : SheafOfModules.{w} R₂}
    (ρ : G.obj M ≅ N) (h : M.IsFree) : N.IsFree := by
  obtain ⟨B, ι, ⟨hc⟩⟩ := h
  refine ⟨B, fun b ↦ η.inv ≫ G.map (ι b) ≫ ρ.hom, ⟨?_⟩⟩
  exact isColimit_cofan_map_comp_iso G η ρ ι hc

/-- **A global presentation travels along a colimit-preserving functor carrying the structure
sheaf to the structure sheaf.** Let `G` be a functor of categories of sheaves of modules
preserving colimits and zero morphisms and carrying `R₁` to `R₂`.  If a sheaf of `R₁`-modules `M`
is a cokernel of a map between coproducts of copies of `R₁` and `G.obj M` is isomorphic to `N`,
then `N` is a cokernel of a map between coproducts of as many copies of `R₂`.

The two coproducts travel by `Stacks.Sheaves.GlobalTypeComparison.isColimitCofanMap`, as for
freeness, and the cokernel by right exactness of `G`.  The statement is about
`SheafOfModules.IsPresentedByGlobalSections`, Stacks 03DE (6) at a single universe of sections,
which is where a pullback of sheaves of modules acts; it is carried to and from
`SheafOfModules.HasGlobalPresentation` by
`SheafOfModules.isPresentedByGlobalSections_iff_hasGlobalPresentation`. -/
theorem isPresentedByGlobalSections_map (G : SheafOfModules.{w} R₁ ⥤ SheafOfModules.{w} R₂)
    [PreservesColimitsOfSize.{w, w} G] [G.PreservesZeroMorphisms]
    (η : G.obj (SheafOfModules.unit R₁) ≅ SheafOfModules.unit R₂)
    {M : SheafOfModules.{w} R₁} {N : SheafOfModules.{w} R₂}
    (ρ : G.obj M ≅ N) (h : M.IsPresentedByGlobalSections) :
    N.IsPresentedByGlobalSections := by
  obtain ⟨I, K, P, Q, ι, κ, ⟨hP⟩, ⟨hQ⟩, a, b, hab, ⟨hc⟩⟩ := h
  have : PreservesColimitsOfSize.{0, 0} G := preservesColimitsOfSize_shrink G
  refine ⟨I, K, G.obj P, G.obj Q, fun i ↦ η.inv ≫ G.map (ι i), fun i ↦ η.inv ≫ G.map (κ i),
    ⟨Stacks.Sheaves.GlobalTypeComparison.isColimitCofanMap G η ι hP⟩,
    ⟨Stacks.Sheaves.GlobalTypeComparison.isColimitCofanMap G η κ hQ⟩,
    G.map a, G.map b ≫ ρ.hom,
    by rw [← Category.assoc, ← G.map_comp, hab, G.map_zero, zero_comp], ⟨?_⟩⟩
  exact (isColimitCoforkMapOfIsColimit' G hab hc).ofIsoColimit (Cofork.ext ρ rfl)

section Generators

variable [HasWeakSheafify J₁ AddCommGrpCat.{w}] [J₁.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify J₂ AddCommGrpCat.{w}] [J₂.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Generating global sections travel along a colimit-preserving functor carrying the structure
sheaf to the structure sheaf.** Let `G` be a functor of categories of sheaves of modules
preserving colimits and carrying `R₁` to `R₂`.  A family of global sections generating a sheaf of
`R₁`-modules `M` is carried to a family of global sections generating `G.obj M`, indexed by the
same type, and `ρ` moves that family to a module `N` named independently of `G`.

The transport itself is Mathlib's `SheafOfModules.GeneratingSections.map`; stating it here with
the functor as an explicit argument, as
`Stacks.Sheaves.LocalizedPullback.isFiniteFree_map` and `.isFree_map` are stated, is what the
localized pullback consumes. -/
def generatingSections_map (G : SheafOfModules.{w} R₁ ⥤ SheafOfModules.{w} R₂)
    [PreservesColimitsOfSize.{w, w} G]
    (η : SheafOfModules.unit R₂ ≅ G.obj (SheafOfModules.unit R₁))
    {M : SheafOfModules.{w} R₁} {N : SheafOfModules.{w} R₂} (ρ : G.obj M ≅ N)
    (σ : M.GeneratingSections) : N.GeneratingSections :=
  SheafOfModules.GeneratingSections.equivOfIso ρ (σ.map G η)

end Generators

end FiniteFree

/-! ### The structure sheaf is its own pullback -/

section Unit

universe u

variable {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y)
  [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The structure sheaf is its own pullback along a morphism of ringed sites.** The pullback of
`O'`, viewed as a module over itself, along the site-presented morphism of ringed topoi of a
morphism of ringed sites is `O`.

This is `Stacks.Sheaves.FinitePresentation.pullbackModulesUnitIso` — where the pullback is the
inverse image of Stacks 03D2 followed by extension of scalars along `f⁻¹O' ⟶ O`, so that both
steps visibly carry the structure sheaf to the structure sheaf — transported along the
comparisons of the three presentations of the pullback of sheaves of modules. -/
def pullbackToposUnitIso :
    SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ≅
      f.toRingedToposSiteHom.pullbackTopos.obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :=
  Stacks.Sheaves.FinitePresentation.pullbackModulesUnitIso
      f.ringedToposHom.toRingedToposModulesHom ≪≫
    ((RingedToposHom.pullbackModulesViaComparisonIso f.ringedToposHom).app
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).symm ≪≫
    f.pullbackToposIso.app (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))

end Unit

/-! ### Section 03DG: the localized pullback datum, before any property -/

section Localized

universe u ww w₁ w₂

variable {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y)
  [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasFiniteLimits Y.C] [PreservesFiniteLimits f.u]
  [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{u}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ W : Y.C, HasWeakSheafify (Y.J.over W) AddCommGrpCat.{u}]
  [∀ W : Y.C, (Y.J.over W).WEqualsLocallyBijective AddCommGrpCat.{u}]
  {M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}

omit [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{u}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ W : Y.C, HasWeakSheafify (Y.J.over W) AddCommGrpCat.{u}]
  [∀ W : Y.C, (Y.J.over W).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The images of a covering of the final object under the functor of a morphism of ringed
sites cover the final object.** If the underlying functor `u : D ⥤ C` of a morphism of ringed
sites is left exact and `{W_i}` covers the final object of `D`, then `{u(W_i)}` covers the final
object of `C`.

Left exactness enters only through the terminal object: `u` carries the final object of `D` to a
final object of `C`, and `Stacks.Sheaves.LocalizedPullback.coversTop_map` then applies. -/
theorem coversTop_mapObj {I : Type*} {W : I → Y.C} (hW : Y.J.CoversTop W) :
    X.J.CoversTop fun i ↦ f.u.obj (W i) :=
  coversTop_map f.u (⊤_ Y.C) (IsTerminal.isTerminalObj f.u _ terminalIsTerminal) hW

omit [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasFiniteLimits Y.C] [PreservesFiniteLimits f.u]
  [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{u}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ W : Y.C, HasWeakSheafify (Y.J.over W) AddCommGrpCat.{u}]
  [∀ W : Y.C, (Y.J.over W).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **Pullback along the localized morphism of ringed topoi preserves colimits**, being a left
adjoint (Stacks 03D7); its right adjoint is the pushforward of the localized morphism. -/
theorem preservesColimitsOfSize_localizedPullbackTopos (W : Y.C) :
    PreservesColimitsOfSize.{w₁, w₂}
      (f.localized W).toRingedToposSiteHom.pullbackTopos :=
  ((f.localized W).toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos
    ).leftAdjoint_preservesColimits

/-- **The localized pullback carries the structure sheaf to the structure sheaf.** For `W` an
object of the target site, the pullback along the localized morphism of ringed topoi
`(Sh(C/u(W)), O_{u(W)}) ⟶ (Sh(D/W), O'_W)` of Stacks 04J0 carries `O'_W` to `O_{u(W)}`.

This is `Stacks.Sheaves.LocalizedPullback.pullbackToposUnitIso` read at the localized morphism
of ringed sites, whose source and target ringed sites are the two localizations. -/
def localizedPullbackUnitIso (W : Y.C) :
    SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (f.u.obj W)) ≅
      (f.localized W).toRingedToposSiteHom.pullbackTopos.obj
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over W)) :=
  pullbackToposUnitIso (f.localized W)

/-- **The localized pullback computes the restriction of the pullback.** For `W` an object of
the target site, the pullback of `M|_W` along the localized morphism of ringed topoi of
Stacks 04J0 is `(f^*M)|_{u(W)}`.

This is the localization square of Stacks 04J0 for the site-presented pullback of sheaves of
modules, `AlgebraicGeometry.RingedSite.Hom.localizedPullbackToposSquare`, read at `M`. -/
def localizedPullbackOverIso (W : Y.C) :
    (f.localized W).toRingedToposSiteHom.pullbackTopos.obj (M.over W) ≅
      (f.toRingedToposSiteHom.pullbackTopos.obj M).over (f.u.obj W) :=
  ((f.localizedPullbackToposSquare W).app M).symm

/-! ### Section 03DG for quasi-coherence -/

/-- **The localized pullback datum of Section 03DG, for the quasi-coherent property.** Let
`(f, f♯) : (C, O) ⟶ (D, O')` be a morphism of ringed sites whose underlying functor `u : D ⥤ C`
is left exact, and let `q` be quasi-coherent data for a sheaf of `O'`-modules `M`: a family
`{W_i}` covering the final object of `D` together with a global presentation of `M|_{W_i}` for
each `i`.  Then the family `{u(W_i)}` covers the final object of `C`, and pullback along the
localized morphism of ringed topoi `(Sh(C/u(W_i)), O_{u(W_i)}) ⟶ (Sh(D/W_i), O'_{W_i})` of
Stacks 04J0 carries `M|_{W_i}` to `(f^*M)|_{u(W_i)}` and the structure sheaf to the structure
sheaf, and preserves colimits.

Section 03DG's method for defining an intrinsic property of modules asks, in its condition (3),
that the property be preserved by pullback along a morphism of ringed sites presented by a left
exact continuous functor; the functor that verification needs is the pullback along the
localized morphism of ringed topoi, and this is that datum for quasi-coherence.  The three
properties of it required are exactly the fields of
`Stacks.SheafOfModules.QuasicoherentData.MapData`, and each is one of the property-agnostic
pieces above: colimit preservation is
`Stacks.Sheaves.LocalizedPullback.preservesColimitsOfSize_localizedPullbackTopos`, the unit
isomorphism is `.localizedPullbackUnitIso`, and the identification of the transported module is
`.localizedPullbackOverIso`. -/
@[stacks 03DG "condition (3) of the method, for the quasi-coherent property: the datum needed to
  carry a global presentation along a pullback is the pullback along the localized morphism of
  ringed topoi of 04J0, and this constructs it"]
def localizedPullbackMapData (q : M.QuasicoherentData.{ww}) :
    Stacks.SheafOfModules.QuasicoherentData.MapData
      f.toRingedToposSiteHom.pullbackTopos q where
  I := q.I
  X i := f.u.obj (q.X i)
  coversTop := coversTop_mapObj f q.coversTop
  index i := i
  functor i := (f.localized (q.X i)).toRingedToposSiteHom.pullbackTopos
  preservesColimits i := preservesColimitsOfSize_localizedPullbackTopos f (q.X i)
  unitIso i := localizedPullbackUnitIso f (q.X i)
  overIso i := localizedPullbackOverIso f (q.X i)

/-- **The quasi-coherent clause of Stacks 03DO for a morphism of ringed sites presented by a
left exact continuous functor.** The pullback of a sheaf of `O'`-modules admitting quasi-coherent
data is quasi-coherent on the site.

The data is transported by `Stacks.Sheaves.LocalizedPullback.localizedPullbackMapData` and the
transported presentations assemble into quasi-coherence on the site by
`Stacks.SheafOfModules.isQuasicoherentOnSite_of_mapData`.

This is the case to which Stacks 03DO's own proof reduces its quasi-coherent clause through
Section 03DG; the general statement, for an arbitrary morphism of ringed topoi, is
`AlgebraicGeometry.RingedToposHom.isQuasicoherentOnSite_pullbackModules`, which transports this
one along the two equivalences of ringed topoi that Stacks 03CR produces. -/
@[stacks 03DG "condition (3) verified for the quasi-coherent property: the pullback of a
  quasi-coherent module along a morphism of ringed sites presented by a left exact continuous
  functor is quasi-coherent",
  stacks 03DO "quasi_coherent, for a morphism of ringed *sites* presented by a left exact
  continuous functor — the case 03DO's own proof reduces its quasi-coherent clause to through
  Section 03DG. The clause for an arbitrary morphism of ringed topoi is
  `AlgebraicGeometry.RingedToposHom.isQuasicoherentOnSite_pullbackModules`, which transports this
  one along the two equivalences of ringed topoi 03CR produces"]
theorem isQuasicoherentOnSite_pullbackTopos_of_quasicoherentData
    (q : M.QuasicoherentData.{ww}) :
    (f.toRingedToposSiteHom.pullbackTopos.obj M).IsQuasicoherentOnSite :=
  Stacks.SheafOfModules.isQuasicoherentOnSite_of_mapData (localizedPullbackMapData f q)

omit [HasFiniteLimits Y.C] [PreservesFiniteLimits f.u] in
/-- **The localized pullback datum of Section 03DG, for the quasi-coherent property, on one
member of the covering family.** A global presentation of `M|_W` is carried by the pullback along
the localized morphism of ringed topoi of Stacks 04J0 to a global presentation of
`(f^*M)|_{u(W)}`.

This is `Stacks.Sheaves.LocalizedPullback.isPresentedByGlobalSections_map` read at the localized
pullback, the two readings of a global presentation being identified by
`SheafOfModules.isPresentedByGlobalSections_iff_hasGlobalPresentation`.  Unlike the route through
`Stacks.SheafOfModules.QuasicoherentData`, nothing here has to recover a
`SheafOfModules.Presentation` from the existence statement, so no essential smallness of the
slices is needed. -/
theorem hasGlobalPresentation_over_pullbackTopos (W : Y.C)
    (h : (M.over W).HasGlobalPresentation) :
    ((f.toRingedToposSiteHom.pullbackTopos.obj M).over (f.u.obj W)).HasGlobalPresentation :=
  have : PreservesColimitsOfSize.{u, u}
      (f.localized W).toRingedToposSiteHom.pullbackTopos :=
    preservesColimitsOfSize_localizedPullbackTopos f W
  have : (f.localized W).toRingedToposSiteHom.pullbackTopos.IsLeftAdjoint :=
    ((f.localized W).toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos).isLeftAdjoint
  (SheafOfModules.isPresentedByGlobalSections_iff_hasGlobalPresentation.{u, u, u} _).1
    (isPresentedByGlobalSections_map (f.localized W).toRingedToposSiteHom.pullbackTopos
      (localizedPullbackUnitIso f W).symm (localizedPullbackOverIso f (M := M) W)
      ((SheafOfModules.isPresentedByGlobalSections_iff_hasGlobalPresentation.{u, u, u} _).2 h))

/-- **The quasi-coherent clause of Stacks 03DO for a morphism of ringed sites, with the
hypothesis in the form the clause states it.** If a sheaf of `O'`-modules is quasi-coherent on
the site, so is its pullback along a morphism of ringed sites presented by a left exact
continuous functor.

Quasi-coherence may be tested on a single family covering the final object, by Stacks 03DN in the
form `Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_hasGlobalPresentation`.  Such
a family `{W_i}` for `M` is carried to the family `{u(W_i)}` by
`Stacks.Sheaves.LocalizedPullback.coversTop_mapObj`, and the global presentation of `M|_{W_i}` to
one of `(f^*M)|_{u(W_i)}` by
`Stacks.Sheaves.LocalizedPullback.hasGlobalPresentation_over_pullbackTopos`.  No smallness
hypothesis on the slices of the target site is needed, for the reason recorded there.

This is the case to which Stacks 03DO's own proof reduces its quasi-coherent clause through
Section 03DG; the general statement, for an arbitrary morphism of ringed topoi, is
`AlgebraicGeometry.RingedToposHom.isQuasicoherentOnSite_pullbackModules`, which transports this
one along the two equivalences of ringed topoi that Stacks 03CR produces. -/
@[stacks 03DG "condition (3) verified for the quasi-coherent property, with the hypothesis in the
  form 03DO states it: the pullback of a quasi-coherent module along a morphism of ringed sites
  presented by a left exact continuous functor is quasi-coherent",
  stacks 03DO "quasi_coherent, for a morphism of ringed *sites* presented by a left exact
  continuous functor — the case 03DO's own proof reduces its quasi-coherent clause to through
  Section 03DG. The clause for an arbitrary morphism of ringed topoi is
  `AlgebraicGeometry.RingedToposHom.isQuasicoherentOnSite_pullbackModules`, which transports this
  one along the two equivalences of ringed topoi 03CR produces"]
theorem isQuasicoherentOnSite_pullbackTopos (hM : M.IsQuasicoherentOnSite) :
    (f.toRingedToposSiteHom.pullbackTopos.obj M).IsQuasicoherentOnSite := by
  obtain ⟨I, W, hW, hpres⟩ :=
    (Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_hasGlobalPresentation M).1 hM
  exact (Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_hasGlobalPresentation
      (f.toRingedToposSiteHom.pullbackTopos.obj M)).2
    ⟨I, fun i ↦ f.u.obj (W i), coversTop_mapObj f hW,
      fun i ↦ hasGlobalPresentation_over_pullbackTopos f (W i) (hpres i)⟩

/-! ### Section 03DG for finite local freeness -/

omit [HasFiniteLimits Y.C] [PreservesFiniteLimits f.u] in
/-- **The localized pullback datum of Section 03DG, for the finite locally free property.** Let
`(f, f♯) : (C, O) ⟶ (D, O')` be a morphism of ringed sites whose underlying functor `u : D ⥤ C`
is left exact, let `M` be a sheaf of `O'`-modules and let `W` be an object of `D` on which `M`
is finite free, that is, on which `M|_W` is a coproduct of finitely many copies of `O'_W`.  Then
`(f^*M)|_{u(W)}` is a coproduct of as many copies of `O_{u(W)}`.

The three pieces of the localized pullback datum are what the transport consumes: pullback along
the localized morphism of ringed topoi of Stacks 04J0 preserves colimits, carries `O'_W` to
`O_{u(W)}`, and carries `M|_W` to `(f^*M)|_{u(W)}`.  None of them mentions a property of
modules; the property enters only through
`Stacks.Sheaves.LocalizedPullback.isFiniteFree_map`, which is the statement that finite freeness
is expressed by a colimit. -/
@[stacks 03DG "condition (3) of the method, for the finite locally free property: the datum
  needed to carry a finite free cofan along a pullback is the pullback along the localized
  morphism of ringed topoi of 04J0, and this is that transport", ega "0 5.4.5" "partial"]
theorem isFiniteFree_over_pullbackTopos (W : Y.C)
    (h : _root_.SheafOfModules.IsFiniteFree ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over W)
      (M.over W)) :
    _root_.SheafOfModules.IsFiniteFree
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (f.u.obj W))
      ((f.toRingedToposSiteHom.pullbackTopos.obj M).over (f.u.obj W)) :=
  have : PreservesColimitsOfSize.{0, 0}
      (f.localized W).toRingedToposSiteHom.pullbackTopos :=
    preservesColimitsOfSize_localizedPullbackTopos f W
  isFiniteFree_map (f.localized W).toRingedToposSiteHom.pullbackTopos
    (localizedPullbackUnitIso f W).symm (localizedPullbackOverIso f (M := M) W) h

/-- **The finite locally free clause of Stacks 03DO for a morphism of ringed sites presented by
a left exact continuous functor.** If a sheaf of `O'`-modules is finite locally free on the
site, so is its pullback along a morphism of ringed sites whose underlying functor is left
exact.  This is the clause of Stacks 03DO for Stacks 03DL (2).

Finite local freeness may be tested on a single family covering the final object, by Stacks 03DN
in the form `Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_iff_exists_cover_isFiniteFree`.
Such a family `{W_i}` for `M` is carried to the family `{u(W_i)}` by
`Stacks.Sheaves.LocalizedPullback.coversTop_mapObj`, and the finite freeness of `M|_{W_i}` is
carried to that of `(f^*M)|_{u(W_i)}` by
`Stacks.Sheaves.LocalizedPullback.isFiniteFree_over_pullbackTopos`.

This is the case to which Stacks 03DO's own proof reduces the clause through Section 03DG; the
general statement, for an arbitrary morphism of ringed topoi, is
`AlgebraicGeometry.RingedToposHom.isFiniteLocallyFreeOnSite_pullbackModules`, which transports
this one along the two equivalences of ringed topoi that Stacks 03CR produces. -/
@[stacks 03DG "condition (3) verified for the finite locally free property: the pullback of a
  finite locally free module along a morphism of ringed sites presented by a left exact
  continuous functor is finite locally free",
  stacks 03DO "the finite locally free property, clause 03DL (2), for a morphism of ringed
  *sites* presented by a left exact continuous functor — the case 03DO's own proof reduces that
  clause to through Section 03DG. The clause for an arbitrary morphism of ringed topoi is
  `AlgebraicGeometry.RingedToposHom.isFiniteLocallyFreeOnSite_pullbackModules`, which transports
  this one along the two equivalences of ringed topoi 03CR produces", ega "II 6.4.8" "more general"]
theorem isFiniteLocallyFreeOnSite_pullbackTopos
    (hM : SheafOfModules.IsFiniteLocallyFreeOnSite M) :
    SheafOfModules.IsFiniteLocallyFreeOnSite
      (f.toRingedToposSiteHom.pullbackTopos.obj M) := by
  obtain ⟨I, W, hW, hfree⟩ :=
    (Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_iff_exists_cover_isFiniteFree Y M).1 hM
  refine (Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_iff_exists_cover_isFiniteFree X
    (f.toRingedToposSiteHom.pullbackTopos.obj M)).2
      ⟨I, fun i ↦ f.u.obj (W i), coversTop_mapObj f hW, fun i ↦ ?_⟩
  exact (_root_.SheafOfModules.isFiniteFree_iff_exists_isColimit _ _).1
    (isFiniteFree_over_pullbackTopos f (W i)
      ((_root_.SheafOfModules.isFiniteFree_iff_exists_isColimit _ _).2 (hfree i)))

/-! ### Section 03DG for local freeness -/

omit [HasFiniteLimits Y.C] [PreservesFiniteLimits f.u] in
/-- **The localized pullback datum of Section 03DG, for the locally free property.** Let
`(f, f♯) : (C, O) ⟶ (D, O')` be a morphism of ringed sites whose underlying functor `u : D ⥤ C`
is left exact, let `M` be a sheaf of `O'`-modules and let `W` be an object of `D` on which `M`
is free, that is, on which `M|_W` is a coproduct of copies of `O'_W`.  Then `(f^*M)|_{u(W)}` is
a coproduct of copies of `O_{u(W)}` indexed by the same type.

As for finite freeness, the three pieces of the localized pullback datum are what the transport
consumes, and the property enters only through
`Stacks.Sheaves.LocalizedPullback.isFree_map`. -/
@[stacks 03DG "condition (3) of the method, for the locally free property: the datum needed to
  carry a free cofan along a pullback is the pullback along the localized morphism of ringed
  topoi of 04J0, and this is that transport"]
theorem isFree_over_pullbackTopos (W : Y.C)
    (h : (M.over W).IsFree) :
    ((f.toRingedToposSiteHom.pullbackTopos.obj M).over (f.u.obj W)).IsFree :=
  have : PreservesColimitsOfSize.{u, u}
      (f.localized W).toRingedToposSiteHom.pullbackTopos :=
    preservesColimitsOfSize_localizedPullbackTopos f W
  isFree_map (f.localized W).toRingedToposSiteHom.pullbackTopos
    (localizedPullbackUnitIso f W).symm (localizedPullbackOverIso f (M := M) W) h

/-- **The locally free clause of Stacks 03DO for a morphism of ringed sites presented by a left
exact continuous functor.** If a sheaf of `O'`-modules is locally free on the site, so is its
pullback along a morphism of ringed sites whose underlying functor is left exact.  This is the
clause of Stacks 03DO for Stacks 03DL (1).

Local freeness may be tested on a single family covering the final object, by Stacks 03DN in the
form `Stacks.SheafOfModules.isLocallyFreeOnSite_iff_exists_cover_isFree`.  Such a family `{W_i}`
for `M` is carried to the family `{u(W_i)}` by
`Stacks.Sheaves.LocalizedPullback.coversTop_mapObj`, and the freeness of `M|_{W_i}` is carried to
that of `(f^*M)|_{u(W_i)}` by `Stacks.Sheaves.LocalizedPullback.isFree_over_pullbackTopos`.

This is the case to which Stacks 03DO's own proof reduces the clause through Section 03DG; the
general statement, for an arbitrary morphism of ringed topoi, is
`AlgebraicGeometry.RingedToposHom.isLocallyFreeOnSite_pullbackModules`, which transports this
one along the two equivalences of ringed topoi that Stacks 03CR produces. -/
@[stacks 03DG "condition (3) verified for the locally free property: the pullback of a locally
  free module along a morphism of ringed sites presented by a left exact continuous functor is
  locally free",
  stacks 03DO "the locally free property, clause 03DL (1), for a morphism of ringed *sites*
  presented by a left exact continuous functor — the case 03DO's own proof reduces that clause
  to through Section 03DG. The clause for an arbitrary morphism of ringed topoi is
  `AlgebraicGeometry.RingedToposHom.isLocallyFreeOnSite_pullbackModules`, which transports this
  one along the two equivalences of ringed topoi 03CR produces"]
theorem isLocallyFreeOnSite_pullbackTopos (hM : SheafOfModules.IsLocallyFreeOnSite M) :
    SheafOfModules.IsLocallyFreeOnSite
      (f.toRingedToposSiteHom.pullbackTopos.obj M) := by
  obtain ⟨I, W, hW, hfree⟩ :=
    (Stacks.SheafOfModules.isLocallyFreeOnSite_iff_exists_cover_isFree Y M).1 hM
  exact (Stacks.SheafOfModules.isLocallyFreeOnSite_iff_exists_cover_isFree X
    (f.toRingedToposSiteHom.pullbackTopos.obj M)).2
      ⟨I, fun i ↦ f.u.obj (W i), coversTop_mapObj f hW,
        fun i ↦ isFree_over_pullbackTopos f (W i) (hfree i)⟩

/-! ### Section 03DG for local generation by sections -/

omit [HasFiniteLimits Y.C] [PreservesFiniteLimits f.u] in
/-- **The localized pullback datum of Section 03DG, for the locally generated property.**
Generating global sections of `M|_W` are carried by the pullback along the localized morphism of
ringed topoi of Stacks 04J0 to generating global sections of `(f^*M)|_{u(W)}`, indexed by the
same type.

The transport is Mathlib's `SheafOfModules.GeneratingSections.map`, whose two hypotheses are
again pieces of the localized pullback datum: colimit preservation and the identification of the
two structure sheaves.  The identification of the transported module with `(f^*M)|_{u(W)}` is
`Stacks.Sheaves.LocalizedPullback.localizedPullbackOverIso`. -/
@[stacks 03DG "condition (3) of the method, for the locally generated property: the datum needed
  to carry a generating family of global sections along a pullback is the pullback along the
  localized morphism of ringed topoi of 04J0, and this is that transport"]
def generatingSectionsPullbackTopos (W : Y.C) (σ : (M.over W).GeneratingSections) :
    ((f.toRingedToposSiteHom.pullbackTopos.obj M).over (f.u.obj W)).GeneratingSections :=
  have : PreservesColimitsOfSize.{u, u}
      (f.localized W).toRingedToposSiteHom.pullbackTopos :=
    preservesColimitsOfSize_localizedPullbackTopos f W
  have : HasSheafify (X.J.over (f.u.obj W)) AddCommGrpCat.{u} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  generatingSections_map (f.localized W).toRingedToposSiteHom.pullbackTopos
    (localizedPullbackUnitIso f W) (localizedPullbackOverIso f (M := M) W) σ

/-- **The locally generated clause of Stacks 03DO for a morphism of ringed sites presented by a
left exact continuous functor.** If a sheaf of `O'`-modules is locally generated by sections, so
is its pullback along a morphism of ringed sites whose underlying functor is left exact.  This is
the clause of Stacks 03DO for Stacks 03DL (3).

Local generation by sections may be tested on a single family covering the final object, by
Stacks 03DN in the form
`Stacks.SheafOfModules.isLocallyGeneratedBySectionsOnSite_iff_exists_cover_generatingSections`.
Such a family `{W_i}` for `M` is carried to the family `{u(W_i)}` by
`Stacks.Sheaves.LocalizedPullback.coversTop_mapObj`, and the generating sections of `M|_{W_i}`
to those of `(f^*M)|_{u(W_i)}` by
`Stacks.Sheaves.LocalizedPullback.generatingSectionsPullbackTopos`.

This is the case to which Stacks 03DO's own proof reduces the clause through Section 03DG; the
general statement, for an arbitrary morphism of ringed topoi, is
`AlgebraicGeometry.RingedToposHom.isLocallyGeneratedBySectionsOnSite_pullbackModules`, which
transports this one along the two equivalences of ringed topoi that Stacks 03CR produces.  The
clause for local generation by a fixed number `r` of sections, Stacks 03DL (4), is proved for an
arbitrary morphism of ringed topoi in
`Stacks.Sheaves.LocalGeneration.pullbackModules_isLocallyGeneratedByOnSite`. -/
@[stacks 03DG "condition (3) verified for the locally generated property: the pullback of a
  module locally generated by sections along a morphism of ringed sites presented by a left exact
  continuous functor is locally generated by sections",
  stacks 03DO "the locally generated property, clause 03DL (3), for a morphism of ringed *sites*
  presented by a left exact continuous functor — the case 03DO's own proof reduces that clause
  to through Section 03DG. The clause for an arbitrary morphism of ringed topoi is
  `AlgebraicGeometry.RingedToposHom.isLocallyGeneratedBySectionsOnSite_pullbackModules`, which
  transports this one along the two equivalences of ringed topoi 03CR produces"]
theorem isLocallyGeneratedBySectionsOnSite_pullbackTopos
    (hM : SheafOfModules.IsLocallyGeneratedBySectionsOnSite M) :
    SheafOfModules.IsLocallyGeneratedBySectionsOnSite
      (f.toRingedToposSiteHom.pullbackTopos.obj M) := by
  obtain ⟨I, W, hW, hgen⟩ :=
    (Stacks.SheafOfModules.isLocallyGeneratedBySectionsOnSite_iff_exists_cover_generatingSections
      Y M).1 hM
  exact
    (Stacks.SheafOfModules.isLocallyGeneratedBySectionsOnSite_iff_exists_cover_generatingSections
      X (f.toRingedToposSiteHom.pullbackTopos.obj M)).2
      ⟨I, fun i ↦ f.u.obj (W i), coversTop_mapObj f hW,
        fun i ↦ ⟨generatingSectionsPullbackTopos f (W i) (hgen i).some⟩⟩

end Localized

end Stacks.Sheaves.LocalizedPullback

end
