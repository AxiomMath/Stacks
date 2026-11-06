module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeKernel
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackUnitGenerators
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleEssSurjReduction
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleImageSections
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRingedObjectRestriction
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleSectionsComparison
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleSmallModelPullbackExact
public import StacksFrontier.AlgebraicGeometry.Descent.UniversallyInjective.Exactness
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentStalkLocalProperties
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.JointlySurjectiveSieves
public import StacksFrontier.AlgebraicGeometry.Topologies.FiniteTypeFromGlobalGenerators
public import StacksCore.Tactic.StacksAttribute

/-!
# Finite type on the small étale site

Let `X` be a scheme and let `ε : (X_étale, 𝒪) ⟶ (X_Zar, 𝒪_X)` be the morphism of ringed sites
of Stacks 08H7.  Its pullback of modules is the associated-module functor
`AlgebraicGeometry.SmallEtale.associatedModule` of Stacks 03DU (4), and Stacks 08HD asserts
that an `𝒪_X`-module `𝓕` is of finite type if and only if `ε^*𝓕` is of finite type on the
small étale site.  This file proves **both** implications, with the finite-type condition in
the categorical form `SheafOfModules.IsFiniteTypeOnSite` of Stacks 03DL (5).

The forward argument is the one of Stacks 03DO, carried out on sections.  Pulling back along a
morphism of sites whose underlying functor `i : C ⥤ D` admits a *left* adjoint — on the small
étale site, the image open of Stacks 03WT — and into which at most one arrow from any object
of `D` lands, sends a family of sections generating `𝓕` over `U` to a family generating
`ε^*𝓕` over `i U`: every section of `ε^*𝓕` lies locally in the span of the images of sections
of `𝓕` under the unit of the adjunction, by `Stacks.Adjunction.epi_of_unit_comp_map_eq_zero`,
and the universal factorization through `i U` pins which sections of `𝓕` those are.

The converse runs the same mechanism backwards and finishes by descent.  Finitely many
generating sections of `ε^*𝓕` over an object `Z` of the small étale site are, on a covering of
`Z`, combinations of unit images of sections of `𝓕` over the image open `U` of `Z`, by the two
displayed results above; finitely many of those sections suffice, and since `Z` covers `ε U`
their unit images generate `ε^*𝓕` over `ε U`.  Descending that to `𝓕` over `U` is the only
non-formal step: the subsheaf of `𝓕` locally spanned by the sections has a pullback whose
inclusion is an epimorphism over `ε U`, and `ε^*` *detects* epimorphisms over an open of `X`,
because over an open it is the associated-module functor of the open subscheme (Stacks 03DV at
an object, `AlgebraicGeometry.SmallEtale.associatedModuleObjRestrictIso`) and that functor is
right exact and reflects zero objects.  The image opens obtained this way cover, étale
morphisms being open and étale coverings jointly surjective, which is the covering the
categorical finite-type condition asks for.

## Main definitions

* `Stacks.SheafOfModules.restrictedSectionFamily` is the family of all restrictions of a finite
  family of sections over a fixed object.
* `Stacks.SheafOfModules.unitSectionFamily` is the family of all restrictions of the images,
  under the unit of a pullback adjunction of sheaves of modules, of sections of the source
  module.

## Main results

* `Stacks.SheafOfModules.generates_of_forall_mem_localSpan`: a finite family of sections over
  an object into which at most one arrow lands from anywhere generates the module as soon as
  every section lies locally in its span.
* `Stacks.SheafOfModules.epi_localSpan_unitSectionFamily`: the local span of the unit sections
  inside a module pullback is the whole module.
* `Stacks.SheafOfModules.generates_unit_app`: the unit images of a generating family generate
  the pullback.
* `Stacks.SheafOfModules.presheafIsFiniteType_of_isFiniteTypeOnSite`: the categorical form of
  Stacks 03DL (5) gives the sectionwise form, with no sheafification hypothesis.
* `Stacks.SheafOfModules.isFiniteTypeOnSite_pullback`: **Stacks 03DO for the clause
  03DL (5)**, for the pullback of modules along a morphism of sites admitting an image-open
  factorization.
* `AlgebraicGeometry.SmallEtale.isFiniteTypeOnSite_associatedModule`: **Stacks 08HD, the
  implication (1) ⇒ (2)**: the pullback `ε^*𝓕` of an `𝒪_X`-module of finite type is of finite
  type on the small étale site of `X`.
* `AlgebraicGeometry.SmallEtale.isFiniteTypeOnSite_of_associatedModule`: **Stacks 08HD, the
  implication (2) ⇒ (1)**: an `𝒪_X`-module whose pullback `ε^*𝓕` is of finite type on the small
  étale site of `X` is of finite type.
* `AlgebraicGeometry.SmallEtale.reflectsEpimorphisms_associatedModule` and
  `AlgebraicGeometry.SmallEtale.epi_over_of_epi_over_associatedModule`: `ε^*` reflects
  epimorphisms, globally and over an open of `X`.
* `AlgebraicGeometry.SmallEtale.generates_of_generates_unit_associatedModule`: the converse of
  Stacks 08HD at one open — if the unit images of a finite family of sections over an open
  generate `ε^*𝓕`, the family generates `𝓕`.
* `AlgebraicGeometry.SmallEtale.ofArrows_toImageOpen_mem_topology`: an object of the small étale
  site covers its image open.
* `AlgebraicGeometry.SmallEtale.exists_imageOpen_generates`: finite generators of `ε^*𝓕` on an
  object come, after shrinking around a point, from sections of `𝓕` over an open of `X`.
* `PresheafOfModules.combSieve`, `PresheafOfModules.generates_iff_combSieve`,
  `PresheafOfModules.generates_of_generates_map`, `PresheafOfModules.generates_of_mem_span` and
  `PresheafOfModules.exists_fin_subfamily_span`: generation by a finite family of sections is
  the covering of one sieve, descends along a covering arrow, passes to a family spanning the
  given one, and needs only finitely many members of a spanning family.
* `Stacks.epi_map_of_natIso`: an epimorphism in the image of a functor stays one along a
  natural isomorphism.
* `AlgebraicGeometry.SmallEtale.mono_unit_app_associatedModuleAdjunction`: the unit of the
  associated-module adjunction is a monomorphism at a quasi-coherent module.
* `AlgebraicGeometry.SmallEtale.isZero_of_isZero_associatedModule`: **Stacks 08H8, the
  zero-detection assertion, for quasi-coherent modules**: a quasi-coherent `𝒪_X`-module with
  `ε^*𝓕 = 0` is zero.
* `CategoryTheory.Adjunction.isZero_of_mono_unit_app` and
  `CategoryTheory.Adjunction.mono_unit_app_of_mono_unit_app`: the categorical content of
  zero detection, that a left adjoint with a monomorphic unit at an object detects the
  vanishing of that object, and that this is a property of the right adjoint alone.

## Implementation notes

The small Zariski site of `X` is presented by `AlgebraicGeometry.Scheme.Opens`, so an
`𝒪_X`-module *is* a module on the small Zariski site — `AlgebraicGeometry.Scheme.ringCatSheaf`
is the structure sheaf of `AlgebraicGeometry.Scheme.zariskiRingedTopos` on the nose — and the
equivalence of Stacks 070U needs no mention here.

For `ε`, the hypotheses of `Stacks.SheafOfModules.isFiniteTypeOnSite_pullback` are these: the
universal factorization of an object of the small étale site through an open of `X` is
`AlgebraicGeometry.SmallEtale.imageOpenAdjunction`, which is the openness of étale morphisms,
and the uniqueness of an arrow into an open is
`AlgebraicGeometry.SmallEtale.subsingleton_hom_opensToSmallEtale`.  They are stated as
hypotheses rather than as a general adjunction so that the generic statement also applies to a
morphism of sites with no left adjoint but with image factorizations.

Stacks 03DO is also available as
`Stacks.Sheaves.FiniteType.pullbackModules_isFiniteTypeOnSite`, for a morphism of ringed
*topoi*; that form is unavailable for `ε`, which has no `CategoryTheory.MorphismOfTopoi` in
this development, so the statement is reproved here directly for the pullback of modules along
a morphism of *sites*.

The converse implication rests on the third assertion of Stacks 08H8, that `ε^*` detects zero
objects, for an **arbitrary** `𝒪_X`-module. That is
`AlgebraicGeometry.SmallEtale.isZero_of_isZero_associatedModule_general`, which reads
`AlgebraicGeometry.SmallEtale.isZero_of_isZero_toZariskiModulePullback` through the comparison
of the two constructions of `ε^*`; no stalk and no strict henselization enter. What is proved
here is only the *quasi-coherent* case,
`AlgebraicGeometry.SmallEtale.isZero_of_isZero_associatedModule`, by a route that needs no
exactness: pulling sections back to the open subscheme identifies `𝓕` with the restriction of
the pullback-sections sheaf of Stacks 03DS, which makes the unit a split monomorphism.

The quasi-coherent case would not suffice for the converse of 08HD: the converse produces
finitely many sections of `𝓕` over an open `U`
whose unit images generate `ε^*𝓕`, and then applies zero detection to the quotient of `𝓕` by
the subsheaf they generate; neither that subsheaf nor the quotient is quasi-coherent.

Zero detection is applied over `U`, not over `X`: the generation hypothesis holds only above
the object of `U`, so the quotient whose vanishing is wanted lives on the slice.  The transfer
is `AlgebraicGeometry.SmallEtale.epi_over_of_epi_over_associatedModule`, which conjugates the
slice at the object of `U` into the small étale site of the open subscheme `U` by Stacks 03DV
at an object (`AlgebraicGeometry.SmallEtale.associatedModuleObjRestrictIso`) and the
reindexing equivalence, and the Zariski slice at `U` into `U`'s own small Zariski site by
`AlgebraicGeometry.Scheme.Modules.overFunctorEquiv` and
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`.  Zero detection is then needed
only for the open subscheme, where it is the same unconditional statement.

## References

* [Stacks Project, Tag 08HD](https://stacks.math.columbia.edu/tag/08HD)
* [Stacks Project, Tag 08H7](https://stacks.math.columbia.edu/tag/08H7)
* [Stacks Project, Tag 08H8](https://stacks.math.columbia.edu/tag/08H8)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 08WK](https://stacks.math.columbia.edu/tag/08WK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v₁ v₂ u₁ u₂

namespace CategoryTheory.Adjunction

/-! ### Zero detection from a monomorphic unit -/

/-- **A left adjoint whose unit is a monomorphism at an object detects the vanishing of that
object.**  If `L ⊣ R` with `R` additive, then the unit at `X` factors through a zero object as
soon as `L.obj X` is one, so a monomorphic unit forces `X` to be zero. -/
theorem isZero_of_mono_unit_app {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    [Preadditive C] [Preadditive D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [R.Additive]
    (X : C) [Mono (adj.unit.app X)] (h : Limits.IsZero (L.obj X)) : Limits.IsZero X := by
  have hR : Limits.IsZero (R.obj (L.obj X)) := by
    rw [Limits.IsZero.iff_id_eq_zero] at h ⊢
    rw [← R.map_id, h, R.map_zero]
  exact Limits.IsZero.of_mono_eq_zero _ (hR.eq_zero_of_tgt (adj.unit.app X))

/-- **Two left adjoints of one functor have monomorphic units at the same objects.**  The unit
of one is the unit of the other composed with the image under the right adjoint of the
comparison isomorphism `CategoryTheory.Adjunction.leftAdjointUniq` of the two left adjoints. -/
theorem mono_unit_app_of_mono_unit_app {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] {L L' : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (adj' : L' ⊣ R) (X : C)
    (h : Mono (adj'.unit.app X)) : Mono (adj.unit.app X) :=
  have := h
  mono_of_mono_fac (unit_leftAdjointUniq_hom_app adj adj' X)

end CategoryTheory.Adjunction

namespace Stacks.SheafOfModules

/-! ### Generation from a family of sections over one object -/

section Restricted

variable {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D}
  {R : Sheaf K RingCat.{u}}

/-- The family of all restrictions of a finite family of sections of a sheaf of modules over a
fixed object of the site. -/
def restrictedSectionFamily (N : _root_.SheafOfModules.{u} R) {U : D} {n : ℕ}
    (s : Fin n → N.val.obj (op U)) (Z : Dᵒᵖ) : Set (N.val.obj Z) :=
  {x | ∃ (f : Z.unop ⟶ U) (j : Fin n), N.val.map f.op (s j) = x}

/-- Each section of a family over `U` belongs to the family of all its restrictions. -/
private theorem mem_restrictedSectionFamily_self (N : _root_.SheafOfModules.{u} R) {U : D}
    {n : ℕ} (s : Fin n → N.val.obj (op U)) (j : Fin n) :
    s j ∈ restrictedSectionFamily N s (op U) :=
  ⟨𝟙 U, j, by rw [op_id, N.val.map_id]; rfl⟩

/-- Over an object admitting an arrow to `U`, and with at most one such arrow, the span of all
restrictions of a family of sections over `U` is the span of the restrictions along that one
arrow. -/
theorem spanSubmodule_restrictedSectionFamily (N : _root_.SheafOfModules.{u} R) {U : D}
    (hsub : ∀ W : D, Subsingleton (W ⟶ U)) {n : ℕ}
    (s : Fin n → N.val.obj (op U)) {W : D} (p : W ⟶ U) :
    (spanSubmodule N (restrictedSectionFamily N s)).obj (op W) =
      Submodule.span (R.obj.obj (op W)) (Set.range fun j => N.val.map p.op (s j)) := by
  refine congrArg (Submodule.span (R.obj.obj (op W))) (Set.ext fun y => ⟨?_, ?_⟩)
  · rintro ⟨Z, g, z, ⟨f, j, rfl⟩, rfl⟩
    refine ⟨j, ?_⟩
    have hfg : f.op ≫ g = p.op := by
      rw [← Quiver.Hom.op_unop g, ← op_comp, (hsub W).allEq (g.unop ≫ f) p]
    rw [← N.val.map_comp_apply, hfg]
  · rintro ⟨j, rfl⟩
    exact ⟨op U, p.op, s j, mem_restrictedSectionFamily_self N s j, rfl⟩

/-- **A family of sections over an object into which at most one arrow lands generates the
module as soon as every section lies locally in its span.**  The witnessing covering sieve is
the sieve along which the section restricts into the span, and the uniqueness of the arrow to
`U` identifies that span with the span of the restricted family. -/
theorem generates_of_forall_mem_localSpan (N : _root_.SheafOfModules.{u} R) {U : D}
    (hsub : ∀ W : D, Subsingleton (W ⟶ U)) {n : ℕ} (s : Fin n → N.val.obj (op U))
    (h : ∀ (V : D) (_ : V ⟶ U) (x : N.val.obj (op V)),
      x ∈ (localSpan N (restrictedSectionFamily N s)).obj (op V)) :
    PresheafOfModules.Generates K N.val s := by
  intro V f x
  refine ⟨spanSieve N (restrictedSectionFamily N s) x, (mem_localSpan_iff x).1 (h V f x), ?_⟩
  intro W g hg
  rw [spanSieve_arrows, spanSubmodule_restrictedSectionFamily N hsub s (g ≫ f)] at hg
  exact (Submodule.mem_span_range_iff_exists_fun _).mp hg

end Restricted

/-! ### The unit sections of a pullback of sheaves of modules -/

section Pullback

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {i : C ⥤ D} [i.IsContinuous J K]
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  (φ : S ⟶ (i.sheafPushforwardContinuous RingCat.{u} J K).obj R)
  {L : _root_.SheafOfModules.{u} S ⥤ _root_.SheafOfModules.{u} R}
  (adj : L ⊣ _root_.SheafOfModules.pushforward φ) (M : _root_.SheafOfModules.{u} S)

/-- The family of all restrictions of the images, under the unit of a pullback adjunction of
sheaves of modules, of the local sections of the source module. -/
def unitSectionFamily (Z : Dᵒᵖ) : Set ((L.obj M).val.obj Z) :=
  {x | ∃ (U : C) (f : Z.unop ⟶ i.obj U) (t : M.val.obj (op U)),
    (L.obj M).val.map f.op ((adj.unit.app M).val.app (op U) t) = x}

/-- The unit image of a section belongs to the family of unit sections. -/
theorem mem_unitSectionFamily (U : Cᵒᵖ) (t : M.val.obj U) :
    (adj.unit.app M).val.app U t ∈ unitSectionFamily φ adj M (op (i.obj U.unop)) :=
  ⟨U.unop, 𝟙 _, t, by rw [op_id, (L.obj M).val.map_id]; rfl⟩

/-- The unit of a pullback adjunction commutes with restriction along the image of an arrow of
the source site. -/
theorem unit_app_map {U V : C} (a : U ⟶ V) (x : M.val.obj (op V)) :
    (L.obj M).val.map (i.map a).op ((adj.unit.app M).val.app (op V) x) =
      (adj.unit.app M).val.app (op U) (M.val.map a.op x) :=
  (PresheafOfModules.naturality_apply (adj.unit.app M).val a.op x).symm

/-- Over an object of the target site with a universal arrow to the image of `U`, the span of
all unit sections is the span of the unit images of the sections of the source module over
`U`: every arrow to the image of an object factors through that universal one. -/
theorem spanSubmodule_unitSectionFamily {W : D} {U : C} (p : W ⟶ i.obj U)
    (hp : ∀ (T : C) (f : W ⟶ i.obj T), ∃ g : U ⟶ T, p ≫ i.map g = f) :
    (spanSubmodule (L.obj M) (unitSectionFamily φ adj M)).obj (op W) =
      Submodule.span (R.obj.obj (op W)) (Set.range fun x : M.val.obj (op U) =>
        (L.obj M).val.map p.op ((adj.unit.app M).val.app (op U) x)) := by
  refine congrArg (Submodule.span (R.obj.obj (op W))) (Set.ext fun y => ⟨?_, ?_⟩)
  · rintro ⟨Z, g, z, ⟨T, f, t, rfl⟩, rfl⟩
    obtain ⟨a, ha⟩ := hp T (g.unop ≫ f)
    refine ⟨M.val.map a.op t, ?_⟩
    show (L.obj M).val.map p.op ((adj.unit.app M).val.app (op U) (M.val.map a.op t)) = _
    have hcomp : (i.map a).op ≫ p.op = f.op ≫ g := by
      rw [← op_comp, ha, op_comp, Quiver.Hom.op_unop]
    rw [← unit_app_map φ adj M a t]
    exact ((L.obj M).val.map_comp_apply (i.map a).op p.op _).symm.trans
      (((L.obj M).val.congr_map_apply hcomp _).trans
        ((L.obj M).val.map_comp_apply f.op g _))
  · rintro ⟨x, rfl⟩
    exact ⟨op (i.obj U), p.op, (adj.unit.app M).val.app (op U) x,
      mem_unitSectionFamily φ adj M (op U) x, rfl⟩

/-- **A pullback of sheaves of modules is generated by its unit sections:** the inclusion of
their local span is an epimorphism.  A morphism out of the pullback killing that span kills
every unit section, so its adjoint transpose vanishes. -/
theorem epi_localSpan_unitSectionFamily :
    Epi (localSpan (L.obj M) (unitSectionFamily φ adj M)).ι := by
  refine Stacks.Adjunction.epi_of_unit_comp_map_eq_zero adj _ (fun Z g hg => ?_)
  ext U t
  exact apply_eq_zero_of_mem_localSpan g hg (mem_localSpan (mem_unitSectionFamily φ adj M U t))

/-- **The unit images of a generating family of sections generate the pullback.**  Every
section of the pullback lies locally in the span of the unit sections, each of which lies, over
the universal arrow to an image open, in the local span of the unit images of the given family;
that local span is a subsheaf, so the two localizations compose. -/
theorem generates_unit_app [HasSheafify K AddCommGrpCat.{u}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (himage : ∀ W : D, ∃ (U : C) (p : W ⟶ i.obj U),
      ∀ (T : C) (f : W ⟶ i.obj T), ∃ g : U ⟶ T, p ≫ i.map g = f)
    (hsub : ∀ (U : C) (W : D), Subsingleton (W ⟶ i.obj U))
    {U : C} {n : ℕ} (s : Fin n → M.val.obj (op U))
    (hs : PresheafOfModules.Generates J M.val s) :
    PresheafOfModules.Generates K (L.obj M).val
      (fun j => (adj.unit.app M).val.app (op U) (s j)) := by
  classical
  set s' : Fin n → (L.obj M).val.obj (op (i.obj U)) :=
    fun j => (adj.unit.app M).val.app (op U) (s j) with hs'def
  set P := localSpan (L.obj M) (restrictedSectionFamily (L.obj M) s') with hPdef
  have hsource : ∀ (T : C) (a : T ⟶ U) (x : M.val.obj (op T)),
      (adj.unit.app M).val.app (op T) x ∈ P.obj (op (i.obj T)) := by
    intro T a x
    obtain ⟨A, hA, ha⟩ := hs T a x
    refine P.isSheaf _ (K.superset_covering ?_
      ((CoverPreserving.of_isContinuous i J K).cover_preserve hA))
    rintro W _ ⟨Z, g, k, hg, rfl⟩
    obtain ⟨c, hc⟩ := ha Z g hg
    have hc' : M.val.map g.op x = ∑ j, c j • M.val.map (g ≫ a).op (s j) := hc.symm
    have hstep : (adj.unit.app M).val.app (op Z) (M.val.map g.op x)
        ∈ P.obj (op (i.obj Z)) := by
      have hsum : (adj.unit.app M).val.app (op Z) (M.val.map g.op x)
          = ∑ j, (adj.unit.app M).val.app (op Z) (c j • M.val.map (g ≫ a).op (s j)) := by
        rw [hc']
        exact map_sum ((adj.unit.app M).val.app (op Z)).hom _ _
      rw [hsum]
      refine Submodule.sum_mem _ (fun j _ => ?_)
      have hsm : (adj.unit.app M).val.app (op Z) (c j • M.val.map (g ≫ a).op (s j))
          = c j • (adj.unit.app M).val.app (op Z) (M.val.map (g ≫ a).op (s j)) :=
        map_smul ((adj.unit.app M).val.app (op Z)).hom _ _
      rw [hsm]
      apply Submodule.smul_mem
      rw [← unit_app_map φ adj M (g ≫ a) (s j)]
      exact mem_localSpan ⟨i.map (g ≫ a), j, rfl⟩
    have heq : (L.obj M).val.map (k ≫ i.map g).op ((adj.unit.app M).val.app (op T) x)
        = (L.obj M).val.map k.op
            ((adj.unit.app M).val.app (op Z) (M.val.map g.op x)) := by
      rw [← unit_app_map φ adj M g x]
      exact ((L.obj M).val.congr_map_apply (op_comp (f := k) (g := i.map g)) _).trans
        ((L.obj M).val.map_comp_apply (i.map g).op k.op _)
    show (L.obj M).val.map (k ≫ i.map g).op ((adj.unit.app M).val.app (op T) x)
      ∈ P.obj (op W)
    rw [heq]
    exact P.map_mem k.op hstep
  refine generates_of_forall_mem_localSpan (L.obj M) (hsub U) s' (fun V f x => ?_)
  have hepi : Epi (localSpan (L.obj M) (unitSectionFamily φ adj M)).ι :=
    epi_localSpan_unitSectionFamily φ adj M
  refine P.isSheaf _ (K.superset_covering ?_
    (spanSieve_mem_of_epi_ι (T := unitSectionFamily φ adj M) x))
  intro W g hg
  obtain ⟨T, p, hp⟩ := himage W
  obtain ⟨a, ha⟩ := hp U (g ≫ f)
  have hle : (spanSubmodule (L.obj M) (unitSectionFamily φ adj M)).obj (op W) ≤ P.obj (op W) := by
    rw [spanSubmodule_unitSectionFamily φ adj M p hp]
    refine Submodule.span_le.mpr ?_
    rintro y ⟨t, rfl⟩
    exact P.map_mem p.op (hsource T a t)
  exact hle hg

/-- **The categorical form of Stacks 03DL (5) gives the sectionwise form.**  The covering
family is the family of objects of the site carrying finitely many generating sections, which
contains a covering of every object because the restriction of a module to a slice is
generated by finitely many global sections there. -/
theorem presheafIsFiniteType_of_isFiniteTypeOnSite (N : _root_.SheafOfModules.{u} S)
    (h : N.IsFiniteTypeOnSite) : PresheafOfModules.IsFiniteType J N.val := by
  refine ⟨{Z : C // ∃ (n : ℕ) (t : Fin n → N.val.obj (op Z)),
      PresheafOfModules.Generates J N.val t}, Subtype.val, ?_, fun j => j.2⟩
  intro U
  obtain ⟨I, V, f, hf, hgg⟩ := h.locally_finitelyGenerated U
  refine J.superset_covering ?_ hf
  intro Y g hg
  rw [Sieve.mem_ofArrows_iff] at hg
  obtain ⟨j, a, rfl⟩ := hg
  rw [Sieve.mem_ofObjects_iff]
  exact ⟨⟨V j, exists_generates_of_hasFiniteGlobalGenerators_over N (V j) (hgg j)⟩, ⟨a⟩⟩

include adj in
/-- **Stacks 03DO for the clause 03DL (5), along a morphism of sites.**  If every object of
the target site admits a universal arrow to the image of an object of the source site, and at
most one arrow lands in each such image, then the pullback of a sheaf of modules of finite type
on the source site is of finite type on the target site.

The covering of each object of the target site is the family of images of the objects carrying
finitely many generating sections, pulled back along the universal arrow. -/
theorem isFiniteTypeOnSite_pullback [HasSheafify K AddCommGrpCat.{u}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (himage : ∀ W : D, ∃ (U : C) (p : W ⟶ i.obj U),
      ∀ (T : C) (f : W ⟶ i.obj T), ∃ g : U ⟶ T, p ≫ i.map g = f)
    (hsub : ∀ (U : C) (W : D), Subsingleton (W ⟶ i.obj U))
    (hM : M.IsFiniteTypeOnSite) : (L.obj M).IsFiniteTypeOnSite := by
  obtain ⟨I, V, hV, hgen⟩ :=
    (presheafIsFiniteType_of_isFiniteTypeOnSite M hM).exists_generators
  refine isFiniteTypeOnSite_of_presheaf_isFiniteType _ ⟨?_⟩
  refine ⟨{W : D // ∃ j : I, i.obj (V j) = W}, Subtype.val, ?_, ?_⟩
  · intro W
    obtain ⟨U, p, hp⟩ := himage W
    refine K.superset_covering ?_ (K.pullback_stable p
      ((CoverPreserving.of_isContinuous i J K).cover_preserve (hV U)))
    rintro Z g ⟨T, f, k, ⟨j, ⟨a⟩⟩, -⟩
    rw [Sieve.mem_ofObjects_iff]
    exact ⟨⟨i.obj (V j), j, rfl⟩, ⟨k ≫ i.map a⟩⟩
  · rintro ⟨-, j, rfl⟩
    obtain ⟨n, t, ht⟩ := hgen j
    exact ⟨n, _, generates_unit_app φ adj M himage hsub t ht⟩

end Pullback

end Stacks.SheafOfModules

namespace AlgebraicGeometry.SmallEtale

open AlgebraicGeometry Stacks.SheafOfModules

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)

/-- Every arrow from an object of the small étale site into an open of `X` factors through the
arrow to the image open. -/
private theorem exists_toImageOpen_comp_eq (W : SmallEtale B X hX) (T : X.Opens)
    (f : W ⟶ (opensToSmallEtale B X hX).obj T) :
    ∃ g : imageOpen B X hX W ⟶ T,
      toImageOpen B X hX W ≫ (opensToSmallEtale B X hX).map g = f :=
  ⟨((imageOpenAdjunction B X hX).homEquiv W T).symm f, Subsingleton.elim _ _⟩

/-- Every object of the small étale site of `X` has a universal arrow to an open of `X`,
namely to its image open: an arrow into an open of `X` exists exactly when the image is
contained in that open, and it then factors through the image open. -/
theorem exists_hom_opensToSmallEtale_universal (W : SmallEtale B X hX) :
    ∃ (U : X.Opens) (p : W ⟶ (opensToSmallEtale B X hX).obj U),
      ∀ (T : X.Opens) (f : W ⟶ (opensToSmallEtale B X hX).obj T),
        ∃ g : U ⟶ T, p ≫ (opensToSmallEtale B X hX).map g = f :=
  ⟨imageOpen B X hX W, toImageOpen B X hX W, exists_toImageOpen_comp_eq B X hX W⟩

/-- **Stacks 08HD, the implication (1) ⇒ (2).**  The pullback `ε^*𝓕` along the morphism of
ringed sites `ε : (X_étale, 𝒪) ⟶ (X_Zar, 𝒪_X)` of an `𝒪_X`-module of finite type is of finite
type on the small étale site of `X`.

This is Stacks 03DO at `ε`: the image open of Stacks 03WT factors every object of the small
étale site through an open of `X`, uniquely, so sections generating `𝓕` over an open have
unit images generating `ε^*𝓕` over it. -/
@[stacks 08HD "the implication (1) ⇒ (2), with finite type in the categorical form of \
03DL (5).  The converse is \
`AlgebraicGeometry.SmallEtale.isFiniteTypeOnSite_of_associatedModule`."]
theorem isFiniteTypeOnSite_associatedModule (F : X.Modules)
    (hF : SheafOfModules.IsFiniteTypeOnSite F) :
    SheafOfModules.IsFiniteTypeOnSite ((associatedModule B X hX).obj F) := by
  have hsh : HasSheafify (topology B X hX) AddCommGrpCat.{u} :=
    hasSheafifyEssentiallySmallSite.{u} _ _
  exact Stacks.SheafOfModules.isFiniteTypeOnSite_pullback (structureMap B X hX)
    (associatedModuleAdjunction B X hX) F
    (exists_hom_opensToSmallEtale_universal B X hX)
    (fun U W => subsingleton_hom_opensToSmallEtale B X hX W U) hF

/-! ### Zero detection on quasi-coherent modules -/

/-- **The unit of the associated-module adjunction is a monomorphism at a quasi-coherent
module.**  Pulling a section of a quasi-coherent `𝓕` over an open `U` of `X` back to the open
subscheme `U` is an isomorphism of `𝓕` onto the restriction to the small Zariski site of the
pullback-sections presheaf of Stacks 03DS, and that presheaf is a sheaf on the small étale
site, so the comparison of Stacks 070S (2) factors through the sheafification which defines
`𝓕^a`.  The unit is therefore the first factor of an isomorphism, hence a split monomorphism.
Local bijectivity of the comparison — 070S (2) itself, which would make the unit an
isomorphism — is not used. -/
theorem mono_unit_app_associatedModuleAdjunction (F : X.Modules) [F.IsQuasicoherent] :
    Mono ((associatedModuleAdjunction B X hX).unit.app F) := by
  have hA : IsIso (sectionsUnit B X hX F) := isIso_sectionsUnit B X hX F
  have hB : IsIso ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (structureSheaf B X hX).obj)).unit.app (sectionsPresheafOfModules B X hX F)) :=
    isIso_sheafificationAdjunction_unit_app B X hX _
      (isSheaf_sectionsPresheafOfModules B X hX F)
  have hB2 : IsIso ((PresheafOfModules.pushforward.{u} (structureMap B X hX).hom).map
      ((PresheafOfModules.sheafificationAdjunction
          (𝟙 (structureSheaf B X hX).obj)).unit.app
        (sectionsPresheafOfModules B X hX F))) := inferInstance
  have hkey := Adjunction.unit_comp_map_unit_comp
      (PresheafOfModules.pullbackPushforwardAdjunction.{u} (structureMap B X hX).hom)
      (PresheafOfModules.sheafificationAdjunction (𝟙 (structureSheaf B X hX).obj))
      ((SheafOfModules.forget X.ringCatSheaf).obj F)
      (sectionsComparison B X hX F)
      (unit_comp_map_sectionsComparison B X hX F)
  have hforget : (SheafOfModules.forget X.ringCatSheaf).map
        ((SheafOfModules.PullbackConstruction.adjunction.{u}
          (structureMap B X hX)).unit.app F) =
      (PresheafOfModules.pullbackPushforwardAdjunction.{u}
          (structureMap B X hX).hom).unit.app
          ((SheafOfModules.forget X.ringCatSheaf).obj F) ≫
        (PresheafOfModules.pushforward.{u} (structureMap B X hX).hom).map
          ((PresheafOfModules.sheafificationAdjunction
              (𝟙 (structureSheaf B X hX).obj)).unit.app
            ((PresheafOfModules.pullback.{u} (structureMap B X hX).hom).obj
              ((SheafOfModules.forget X.ringCatSheaf).obj F))) := rfl
  rw [← hforget] at hkey
  have h1 : Mono ((SheafOfModules.forget X.ringCatSheaf).map
      ((SheafOfModules.PullbackConstruction.adjunction.{u}
        (structureMap B X hX)).unit.app F)) := by
    exact @mono_of_mono_fac _ _ _ _ _ _ _ _
      (@mono_comp _ _ _ _ _ _ (@IsIso.mono_of_iso _ _ _ _ _ hA) _
        (@IsIso.mono_of_iso _ _ _ _ _ hB2)) hkey
  exact Adjunction.mono_unit_app_of_mono_unit_app
    (SheafOfModules.pullbackPushforwardAdjunction.{u} (structureMap B X hX))
    (SheafOfModules.PullbackConstruction.adjunction.{u} (structureMap B X hX)) F
    ((SheafOfModules.forget X.ringCatSheaf).mono_of_mono_map h1)

/-- **Stacks 08H8, the zero-detection assertion, for quasi-coherent modules.**  A quasi-coherent
`𝒪_X`-module `𝓕` whose pullback `ε^*𝓕` along the morphism of ringed sites
`ε : (X_étale, 𝒪) ⟶ (X_Zar, 𝒪_X)` is a zero object is itself a zero object.

The unit of the associated-module adjunction is a monomorphism at `𝓕`, and it factors through
`ε_*ε^*𝓕`, which vanishes with `ε^*𝓕`; so the identity of `𝓕` vanishes.  The source instead
computes the stalk of `ε^*𝓕` at a geometric point as `𝓕_x ⊗_{𝒪_{X, x}} 𝒪_{étale, x̄}` and
appeals to faithful flatness of the strict henselization. For an arbitrary `𝒪_X`-module the
assertion is `AlgebraicGeometry.SmallEtale.isZero_of_isZero_associatedModule_general`. -/
@[stacks 08H8 "the zero-detection assertion `ε^*𝓕 = 0 ⟹ 𝓕 = 0`, for quasi-coherent `𝓕`, by a \
route needing no exactness.  The flatness assertion is \
`isFlatMapULift_inverseImageStructureMap`, the exactness assertion is \
`preservesFiniteLimits_associatedModule`, and zero detection for an arbitrary `𝒪_X`-module is \
`isZero_of_isZero_associatedModule_general`."]
theorem isZero_of_isZero_associatedModule (F : X.Modules) [F.IsQuasicoherent]
    (h : IsZero ((associatedModule B X hX).obj F)) : IsZero F :=
  have : (restrictModule B X hX).Additive := ⟨rfl⟩
  have := mono_unit_app_associatedModuleAdjunction B X hX F
  Adjunction.isZero_of_mono_unit_app (associatedModuleAdjunction B X hX) F h

end AlgebraicGeometry.SmallEtale

namespace PresheafOfModules

/-! ### Generation as the covering of a single sieve -/

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
  {J : GrothendieckTopology C} (M : PresheafOfModules.{u} R)

/-- Restricting along a composite is restricting twice. -/
private theorem restrictₛₗ_op_comp_apply {U V W : C} (g : V ⟶ U) (k : W ⟶ V) (x : M.obj (op U)) :
    M.restrictₛₗ (k ≫ g).op x = M.restrictₛₗ k.op (M.restrictₛₗ g.op x) :=
  M.map_comp_apply g.op k.op x

/-- The sieve of arrows along which a section of a presheaf of modules becomes a linear
combination of the restrictions of a finite family of sections over an object.  Downward
closure is the restriction of such a combination, with the coefficients restricted too. -/
def combSieve {U : C} {n : ℕ} (s : Fin n → M.obj (op U)) {V : C} (f : V ⟶ U)
    (x : M.obj (op V)) : Sieve V where
  arrows W g := ∃ a : Fin n → R.obj (op W),
    ∑ i, a i • M.restrictₛₗ (g ≫ f).op (s i) = M.restrictₛₗ g.op x
  downward_closed := by
    rintro W W' g ⟨a, ha⟩ k
    refine ⟨fun i ↦ R.map k.op (a i), ?_⟩
    have hs : ∀ i, M.restrictₛₗ ((k ≫ g) ≫ f).op (s i)
        = M.restrictₛₗ k.op (M.restrictₛₗ (g ≫ f).op (s i)) := by
      intro i
      have h := M.map_comp_apply (g ≫ f).op k.op (s i)
      rw [← op_comp, ← Category.assoc] at h
      exact h
    have hx : M.restrictₛₗ (k ≫ g).op x = M.restrictₛₗ k.op (M.restrictₛₗ g.op x) := by
      have h := M.map_comp_apply g.op k.op x
      rw [← op_comp] at h
      exact h
    rw [hx, ← ha, map_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [hs i, map_smulₛₗ]

/-- **Generation is the covering of the combination sieve.**  A finite family of sections
generates a presheaf of modules for a topology exactly when, for every section over an object
of the slice, the sieve of arrows along which that section becomes a linear combination of the
family is a covering sieve: any witnessing sieve is contained in it. -/
theorem generates_iff_combSieve {U : C} {n : ℕ} (s : Fin n → M.obj (op U)) :
    Generates J M s ↔ ∀ (V : C) (f : V ⟶ U) (x : M.obj (op V)), combSieve M s f x ∈ J V := by
  refine ⟨fun hs V f x ↦ ?_, fun hs V f x ↦ ⟨combSieve M s f x, hs V f x, fun W g hg ↦ hg⟩⟩
  obtain ⟨S, hS, hc⟩ := hs V f x
  refine J.superset_covering ?_ hS
  intro W g hg
  exact hc W g hg

/-- **Generation descends along a covering arrow.**  If the restrictions of a finite family of
sections along an arrow `c : Z ⟶ U` whose sieve covers `U` generate the presheaf of modules,
then the family itself generates it: every arrow to `U` is covered by arrows factoring through
`c`, and on each of those the combination for the restricted family is a combination for the
original one. -/
theorem generates_of_generates_map {U Z : C} (c : Z ⟶ U)
    (hc : Sieve.ofArrows (fun _ : Unit ↦ Z) (fun _ ↦ c) ∈ J U) {n : ℕ}
    (s : Fin n → M.obj (op U))
    (h : Generates J M (fun i ↦ M.restrictₛₗ c.op (s i))) : Generates J M s := by
  rw [generates_iff_combSieve] at h ⊢
  intro V f x
  refine J.transitive (J.pullback_stable f hc) _ ?_
  intro V' g hg
  have hg' : (Sieve.ofArrows (fun _ : Unit ↦ Z) (fun _ ↦ c)).arrows (g ≫ f) := hg
  rw [Sieve.mem_ofArrows_iff] at hg'
  obtain ⟨-, k, hk⟩ := hg'
  refine J.superset_covering ?_ (h V' k (M.restrictₛₗ g.op x))
  intro W g₂ hg₂
  obtain ⟨a, ha⟩ := hg₂
  refine ⟨a, ?_⟩
  have hfac : (g₂ ≫ k) ≫ c = (g₂ ≫ g) ≫ f := by
    rw [Category.assoc, ← hk, Category.assoc]
  have hs : ∀ i, M.restrictₛₗ (g₂ ≫ k).op (M.restrictₛₗ c.op (s i))
      = M.restrictₛₗ ((g₂ ≫ g) ≫ f).op (s i) := fun i ↦ by
    rw [← restrictₛₗ_op_comp_apply, hfac]
  simp only [hs, ← restrictₛₗ_op_comp_apply] at ha
  exact ha

/-- **A family in whose span a generating family lies is itself generating.**  The witnessing
covering sieve is unchanged: on each of its arrows the given combination of the first family is
rewritten, using the combinations expressing it in the second, as a combination of the second. -/
theorem generates_of_mem_span {U : C} {n m : ℕ} (s : Fin n → M.obj (op U))
    (r : Fin m → M.obj (op U)) (hs : Generates J M s)
    (hmem : ∀ k, s k ∈ Submodule.span (R.obj (op U)) (Set.range r)) : Generates J M r := by
  choose b hb using fun k ↦ (Submodule.mem_span_range_iff_exists_fun _).1 (hmem k)
  intro V f x
  obtain ⟨S, hS, hc⟩ := hs V f x
  refine ⟨S, hS, fun W g hg ↦ ?_⟩
  obtain ⟨a, ha⟩ := hc W g hg
  refine ⟨fun j ↦ ∑ k, a k * R.map (g ≫ f).op (b k j), ?_⟩
  calc ∑ j, (∑ k, a k * R.map (g ≫ f).op (b k j)) • M.restrictₛₗ (g ≫ f).op (r j)
      = ∑ j, ∑ k, (a k * R.map (g ≫ f).op (b k j)) • M.restrictₛₗ (g ≫ f).op (r j) :=
        Finset.sum_congr rfl fun j _ ↦ Finset.sum_smul
    _ = ∑ k, ∑ j, (a k * R.map (g ≫ f).op (b k j)) • M.restrictₛₗ (g ≫ f).op (r j) :=
        Finset.sum_comm
    _ = ∑ k, a k • M.restrictₛₗ (g ≫ f).op (s k) := by
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        rw [← hb k, map_sum, Finset.smul_sum]
        exact Finset.sum_congr rfl fun j _ ↦ by rw [map_smulₛₗ, mul_smul]
    _ = M.restrictₛₗ g.op x := ha

/-- **Finitely many sections lying in the span of an arbitrary family lie in the span of a
finite subfamily**: the union of the finitely many finite supports of the expressing
coefficients indexes one. -/
theorem exists_fin_subfamily_span {U : C} {ι : Type*} {n : ℕ} (v : ι → M.obj (op U))
    (s : Fin n → M.obj (op U))
    (hs : ∀ k, s k ∈ Submodule.span (R.obj (op U)) (Set.range v)) :
    ∃ (m : ℕ) (e : Fin m → ι),
      ∀ k, s k ∈ Submodule.span (R.obj (op U)) (Set.range fun i ↦ v (e i)) := by
  classical
  choose cf hcf using fun k ↦ Finsupp.mem_span_range_iff_exists_finsupp.1 (hs k)
  obtain ⟨T, hT⟩ : ∃ T : Finset ι, ∀ k : Fin n, (cf k).support ⊆ T :=
    ⟨Finset.univ.biUnion fun k : Fin n ↦ (cf k).support,
      fun k _ hz ↦ Finset.mem_biUnion.2 ⟨k, Finset.mem_univ k, hz⟩⟩
  refine ⟨T.card, fun i ↦ (T.equivFin.symm i : ι), fun k ↦ ?_⟩
  rw [← hcf k]
  refine Submodule.sum_mem _ fun z hz ↦ Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  exact ⟨T.equivFin ⟨z, hT k hz⟩, by simp only [Equiv.symm_apply_apply]⟩

end PresheafOfModules

namespace Stacks

/-- **An epimorphism in the image of a functor stays one along a natural isomorphism.** -/
theorem epi_map_of_natIso {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {F G : C ⥤ D} (α : F ≅ G) {A A' : C} (f : A ⟶ A') (h : Epi (F.map f)) :
    Epi (G.map f) := by
  rw [← NatIso.naturality_2 α.symm f]
  infer_instance

end Stacks

namespace AlgebraicGeometry.SmallEtale

open AlgebraicGeometry Stacks.SheafOfModules

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)

/-! ### The converse of Stacks 08HD -/

/-- **`ε^*` reflects epimorphisms.**  It is right exact, being a left adjoint, and it detects
zero objects, by the zero-detection assertion of Stacks 08H8 for an *arbitrary* `𝒪_X`-module,
`AlgebraicGeometry.SmallEtale.isZero_of_isZero_associatedModule_general`. -/
theorem reflectsEpimorphisms_associatedModule :
    (associatedModule B X hX).ReflectsEpimorphisms :=
  Functor.reflectsEpimorphisms_of_preservesFiniteColimits_of_reflectsZeroObjects
    (associatedModule B X hX) (fun F ↦ isZero_of_isZero_associatedModule_general B X hX F)

/-- The structure morphism of the object of the small étale site attached to an open of `X` is
the inclusion of that open. -/
theorem objHom_opensToSmallEtale (V : X.Opens) :
    objHom B X hX ((opensToSmallEtale B X hX).obj V) = V.ι := rfl

/-- **`ε^*` detects epimorphisms over an open of `X`.**  If the pullback of `φ` becomes an
epimorphism after restriction to the slice of the small étale site over an open `V` of `X`,
then `φ` is already an epimorphism after restriction to the slice of the small Zariski site
over `V`.

The restriction of `ε^*` to the slice at the object of `V` is, by
`AlgebraicGeometry.SmallEtale.associatedModuleObjRestrictIso`, the associated-module functor of
the open subscheme `V` composed with the pullback along `V ↪ X`; that functor reflects
epimorphisms, and pullback along an open immersion is restriction to the slice, by
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` and
`AlgebraicGeometry.Scheme.Modules.overFunctorEquiv`.  The structure morphism of the object of
`V` is the inclusion of `V` on the nose, which is
`AlgebraicGeometry.SmallEtale.objHom_opensToSmallEtale`; the step from the associated-module
functor of the open subscheme to the pullback along that inclusion is that identification. -/
theorem epi_over_of_epi_over_associatedModule (V : X.Opens) {Q Q' : X.Modules} (φ : Q ⟶ Q')
    (h : Epi ((SheafOfModules.overFunctor (structureSheaf B X hX)
      ((opensToSmallEtale B X hX).obj V)).map ((associatedModule B X hX).map φ))) :
    Epi ((SheafOfModules.overFunctor X.ringCatSheaf V).map φ) := by
  set U := (opensToSmallEtale B X hX).obj V with hU
  have : ((objRestrictEquivalence B X hX U).functor).IsEquivalence := inferInstance
  have hobj : (objRestrictFunctor B X hX U).IsEquivalence := this
  have h2 : Epi ((associatedModule B X hX ⋙ objRestrict B X hX U).map φ) := by
    have := h
    exact inferInstanceAs (Epi ((objRestrictFunctor B X hX U).map _))
  have h3 : Epi ((Scheme.Modules.pullback (objHom B X hX U) ⋙
      associatedModule B (objScheme B X hX U) (contains_objScheme B X hX U)).map φ) :=
    Stacks.epi_map_of_natIso (associatedModuleObjRestrictIso B X hX U).symm φ h2
  have h4 : Epi ((Scheme.Modules.pullback V.ι).map φ) :=
    (reflectsEpimorphisms_associatedModule B (objScheme B X hX U)
      (contains_objScheme B X hX U)).reflects _ h3
  have h5 : Epi ((Scheme.Modules.restrictFunctor V.ι).map φ) :=
    Stacks.epi_map_of_natIso (Scheme.Modules.restrictFunctorIsoPullback V.ι).symm φ h4
  have h6 : Epi ((SheafOfModules.overFunctor X.ringCatSheaf V ⋙
      (Scheme.Modules.overEquiv V).functor).map φ) :=
    Stacks.epi_map_of_natIso (Scheme.Modules.overFunctorEquiv V).symm φ h5
  exact Functor.epi_of_epi_map (Scheme.Modules.overEquiv V).functor h6

/-- **The converse of Stacks 08HD at one open.**  If the unit images of a finite family of
sections of `𝓕` over an open `V` of `X` generate `ε^*𝓕` on the small étale site, then the family
generates `𝓕` on the small Zariski site.

Let `𝒫 ⊆ 𝓕` be the subsheaf locally spanned by the family.  A section of `ε^*𝓕` over an object
of the small étale site lying over `V` is, by hypothesis, locally a combination of the unit
images of the family; those unit images are the images under `ε^*` of unit sections of `𝒫`, by
naturality of the unit, so `ε^*(𝒫 ⊆ 𝓕)` is locally surjective over the object of `V`, hence an
epimorphism there.  `ε^*` detects epimorphisms over an open of `X`
(`AlgebraicGeometry.SmallEtale.epi_over_of_epi_over_associatedModule`), so the inclusion is an
epimorphism over `V`; a section of `𝓕` over an open contained in `V` therefore lifts locally
into `𝒫`, and `𝒫` is closed under locality. -/
theorem generates_of_generates_unit_associatedModule (F : X.Modules) (V : X.Opens) {n : ℕ}
    (t : Fin n → F.val.obj (op V))
    (h : PresheafOfModules.Generates (topology B X hX) ((associatedModule B X hX).obj F).val
      (fun j ↦ ((associatedModuleAdjunction B X hX).unit.app F).val.app (op V) (t j))) :
    PresheafOfModules.Generates (Opens.grothendieckTopology ↥X) F.val t := by
  have hmemt : ∀ j, t j ∈ (localSpan F (restrictedSectionFamily F t)).obj (op V) := fun j ↦
    mem_localSpan (mem_restrictedSectionFamily_self F t j)
  set P := (localSpan F (restrictedSectionFamily F t)).toSheafOfModules with hP
  set ι := (localSpan F (restrictedSectionFamily F t)).ι with hιdef
  set φ := (associatedModule B X hX).map ι with hφ
  set uP : Fin n → ((associatedModule B X hX).obj P).val.obj
      (op ((opensToSmallEtale B X hX).obj V)) :=
    fun j ↦ ((associatedModuleAdjunction B X hX).unit.app P).val.app (op V) ⟨t j, hmemt j⟩
    with huP
  have key : ∀ j, φ.val.app (op ((opensToSmallEtale B X hX).obj V)) (uP j)
      = ((associatedModuleAdjunction B X hX).unit.app F).val.app (op V) (t j) := fun j ↦
    (congrArg (fun ψ ↦ ψ.val.app (op V) (⟨t j, hmemt j⟩ : P.val.obj (op V)))
      ((associatedModuleAdjunction B X hX).unit.naturality ι)).symm
  have hepi1 : Epi ((SheafOfModules.overFunctor (structureSheaf B X hX)
      ((opensToSmallEtale B X hX).obj V)).map φ) := by
    refine SheafOfModules.epi_of_sections _ (fun Z y ↦ ?_)
    obtain ⟨S, hS, hc⟩ := h Z.left Z.hom y
    refine ⟨(Sieve.overEquiv Z).symm S,
      ((topology B X hX).mem_over_iff _).mpr (by rw [OrderIso.apply_symm_apply]; exact hS),
      fun Z' g hg ↦ ?_⟩
    obtain ⟨a, ha⟩ := hc Z'.left g.left ((Sieve.overEquiv_symm_iff S g).1 hg)
    have ha' : ∑ j, a j • ((associatedModule B X hX).obj F).val.map (g.left ≫ Z.hom).op
        (((associatedModuleAdjunction B X hX).unit.app F).val.app (op V) (t j))
        = ((associatedModule B X hX).obj F).val.map g.left.op y := ha
    have hlin : ∀ (c : Fin n → (structureSheaf B X hX).obj.obj (op Z'.left))
        (v : Fin n → ((associatedModule B X hX).obj P).val.obj (op Z'.left)),
        φ.val.app (op Z'.left) (∑ j, c j • v j)
          = ∑ j, c j • φ.val.app (op Z'.left) (v j) := fun c v ↦
      Eq.trans (map_sum (φ.val.app (op Z'.left)).hom _ _)
        (Finset.sum_congr rfl fun j _ ↦ map_smul (φ.val.app (op Z'.left)).hom _ _)
    have hgoal : φ.val.app (op Z'.left)
          (∑ j, a j • ((associatedModule B X hX).obj P).val.map (g.left ≫ Z.hom).op (uP j))
        = ((associatedModule B X hX).obj F).val.map g.left.op y := by
      refine Eq.trans (hlin a _) (Eq.trans ?_ ha')
      refine Finset.sum_congr rfl fun j _ ↦ congrArg (fun z ↦ a j • z) ?_
      exact Eq.trans (PresheafOfModules.naturality_apply φ.val (g.left ≫ Z.hom).op (uP j))
        (congrArg _ (key j))
    exact ⟨∑ j, a j • ((associatedModule B X hX).obj P).val.map (g.left ≫ Z.hom).op (uP j),
      hgoal⟩
  have hepi2 : Epi ((SheafOfModules.overFunctor X.ringCatSheaf V).map ι) :=
    epi_over_of_epi_over_associatedModule B X hX V ι hepi1
  have : HasSheafify ((Opens.grothendieckTopology ↥X).over V) AddCommGrpCat.{u} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{u, u, u} _
  have : ((Opens.grothendieckTopology ↥X).over V).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u, u, u} _
  have := hepi2
  refine generates_of_forall_mem_localSpan F (fun W ↦ inferInstance) t (fun W f' x ↦ ?_)
  obtain ⟨S, hS, hlift⟩ := Stacks.SheafOfModules.EpiMono.exists_covering_of_epi
    ((SheafOfModules.overFunctor X.ringCatSheaf V).map ι)
    (V := Over.mk f') (s := x)
  refine (localSpan F (restrictedSectionFamily F t)).isSheaf x
    ((Opens.grothendieckTopology ↥X).superset_covering ?_
      (((Opens.grothendieckTopology ↥X).mem_over_iff S).mp hS))
  intro W' i hi
  obtain ⟨τ, hτ⟩ := hlift (Over.homMk i : Over.mk (i ≫ f') ⟶ Over.mk f')
    ((Sieve.overEquiv_iff S i).1 hi)
  have hτ' : Subtype.val τ = F.val.map i.op x := hτ
  exact (mem_sieveOfSection_iff x i).2 (hτ' ▸ τ.2)

/-- **An object of the small étale site covers its image open.**  Its structure morphism is
open, and `AlgebraicGeometry.SmallEtale.toImageOpen` is its factorization through the image
open, hence surjective on points; a jointly surjective family of étale morphisms generates a
covering sieve. -/
theorem ofArrows_toImageOpen_mem_topology (Z : SmallEtale B X hX) :
    Sieve.ofArrows (fun _ : Unit ↦ Z) (fun _ ↦ toImageOpen B X hX Z) ∈
      topology B X hX ((opensToSmallEtale B X hX).obj (imageOpen B X hX Z)) := by
  refine generate_ofArrows_mem_topology_of_jointlySurjective B X hX _ _ (fun x ↦ ⟨(), ?_⟩)
  have hmem : (imageOpen B X hX Z).ι.base x ∈ Set.range ⇑Z.obj.hom.hom := by
    rw [← imageOpen_coe B X hX Z, ← Scheme.Opens.range_ι (imageOpen B X hX Z)]
    exact Set.mem_range_self x
  obtain ⟨w, hw⟩ := hmem
  have hfac := BigEtaleOver.hom_hom_eq B X hX (toImageOpen B X hX Z).hom
  refine ⟨w, (imageOpen B X hX Z).ι.isOpenEmbedding.injective ?_⟩
  have h2 : Z.obj.hom.hom.base w
      = (imageOpen B X hX Z).ι.base ((toImageOpen B X hX Z).hom.left.hom.base w) := by
    rw [hfac]; rfl
  exact h2.symm.trans hw

/-- **Finite generators of `ε^*𝓕` on an object of the small étale site come, after shrinking
around any point, from finitely many sections of `𝓕` over an open of `X`.**

Every section of `ε^*𝓕` lies locally in the span of the unit images of sections of `𝓕`
(`Stacks.SheafOfModules.epi_localSpan_unitSectionFamily`), and over an object the span of those
unit sections is the span of the unit images of the sections of `𝓕` over its image open
(`Stacks.SheafOfModules.spanSubmodule_unitSectionFamily`).  So on a covering of `Z` the given
generators are combinations of finitely many such unit images; those unit images then generate
`ε^*𝓕` over the shrunken object, hence over its image open, since an object covers its image
open, and the converse at one open finishes. -/
theorem exists_imageOpen_generates (F : X.Modules) (Z : SmallEtale B X hX) {n : ℕ}
    (s : Fin n → ((associatedModule B X hX).obj F).val.obj (op Z))
    (hs : PresheafOfModules.Generates (topology B X hX) ((associatedModule B X hX).obj F).val s)
    (w : (toScheme B X hX).obj Z) :
    ∃ (Z' : SmallEtale B X hX) (c : Z' ⟶ Z), w ∈ Set.range ((toScheme B X hX).map c) ∧
      ∃ (m : ℕ) (r : Fin m → F.val.obj (op (imageOpen B X hX Z'))),
        PresheafOfModules.Generates (Opens.grothendieckTopology ↥X) F.val r := by
  classical
  have hepi : Epi (localSpan ((associatedModule B X hX).obj F)
      (unitSectionFamily (structureMap B X hX) (associatedModuleAdjunction B X hX) F)).ι :=
    epi_localSpan_unitSectionFamily (structureMap B X hX) (associatedModuleAdjunction B X hX) F
  have hAmem : (Finset.univ.inf fun j : Fin n ↦ spanSieve ((associatedModule B X hX).obj F)
        (unitSectionFamily (structureMap B X hX) (associatedModuleAdjunction B X hX) F) (s j))
      ∈ topology B X hX Z :=
    Stacks.SheafOfModules.FiniteTypeKernel.finsetInf_mem (topology B X hX) _ _
      fun j _ ↦ spanSieve_mem_of_epi_ι (s j)
  obtain ⟨Z', c, hc, hw'⟩ := SmallEtale.exists_mem_arrows_mem_range B X hX hAmem w
  refine ⟨Z', c, hw', ?_⟩
  have hmemspan : ∀ j, ((associatedModule B X hX).obj F).val.restrictₛₗ c.op (s j)
      ∈ Submodule.span ((structureSheaf B X hX).obj.obj (op Z'))
        (Set.range fun z : F.val.obj (op (imageOpen B X hX Z')) ↦
          ((associatedModule B X hX).obj F).val.restrictₛₗ (toImageOpen B X hX Z').op
            (((associatedModuleAdjunction B X hX).unit.app F).val.app
              (op (imageOpen B X hX Z')) z)) := by
    intro j
    have hspan := spanSubmodule_unitSectionFamily (structureMap B X hX)
      (associatedModuleAdjunction B X hX) F (toImageOpen B X hX Z')
      (exists_toImageOpen_comp_eq B X hX Z')
    exact le_of_eq hspan (Finset.inf_le
      (f := fun j : Fin n ↦ spanSieve ((associatedModule B X hX).obj F)
        (unitSectionFamily (structureMap B X hX) (associatedModuleAdjunction B X hX) F) (s j))
      (Finset.mem_univ j) c hc)
  obtain ⟨m, r, hr⟩ := PresheafOfModules.exists_fin_subfamily_span
    ((associatedModule B X hX).obj F).val
    (fun z : F.val.obj (op (imageOpen B X hX Z')) ↦
      ((associatedModule B X hX).obj F).val.restrictₛₗ (toImageOpen B X hX Z').op
        (((associatedModuleAdjunction B X hX).unit.app F).val.app
          (op (imageOpen B X hX Z')) z))
    (fun j ↦ ((associatedModule B X hX).obj F).val.restrictₛₗ c.op (s j)) hmemspan
  refine ⟨m, r, ?_⟩
  refine generates_of_generates_unit_associatedModule B X hX F (imageOpen B X hX Z') r ?_
  refine PresheafOfModules.generates_of_generates_map ((associatedModule B X hX).obj F).val
    (toImageOpen B X hX Z') (ofArrows_toImageOpen_mem_topology B X hX Z') _ ?_
  exact PresheafOfModules.generates_of_mem_span ((associatedModule B X hX).obj F).val
    (fun j ↦ ((associatedModule B X hX).obj F).val.restrictₛₗ c.op (s j)) _
    (hs.restrict c) hr

/-- **Stacks 08HD, the implication (2) ⇒ (1).**  An `𝒪_X`-module whose pullback `ε^*𝓕` along
the morphism of ringed sites `ε : (X_étale, 𝒪) ⟶ (X_Zar, 𝒪_X)` is of finite type on the small
étale site of `X` is itself of finite type, the finite-type condition being in the categorical
form `SheafOfModules.IsFiniteTypeOnSite` of Stacks 03DL (5).

The covering family of opens is the family of *all* opens of `X` carrying finitely many
generating sections, so no choice of covering is recorded: what has to be shown is that those
opens cover, and that is the content of
`AlgebraicGeometry.SmallEtale.exists_imageOpen_generates`.  Given a point `x` of an open `W`,
the finite-type hypothesis at the object of `W` gives an object of the small étale site whose
image contains `x` and on which `ε^*𝓕` has finitely many generating sections; shrinking it
replaces those by unit images of sections of `𝓕` over its image open, which is contained in
`W` and contains `x`. -/
@[stacks 08HD "the implication (2) ⇒ (1), with finite type in the categorical form of \
03DL (5).  The source deduces it from the stalk description of `ε^*`; here it is deduced from \
the zero-detection assertion of 08H8 for an arbitrary `𝒪_X`-module, \
`AlgebraicGeometry.SmallEtale.isZero_of_isZero_associatedModule_general`."]
theorem isFiniteTypeOnSite_of_associatedModule (F : X.Modules)
    (h : SheafOfModules.IsFiniteTypeOnSite ((associatedModule B X hX).obj F)) :
    SheafOfModules.IsFiniteTypeOnSite F := by
  refine isFiniteTypeOnSite_of_presheaf_isFiniteType F ⟨?_⟩
  refine ⟨{V : X.Opens // ∃ (m : ℕ) (r : Fin m → F.val.obj (op V)),
      PresheafOfModules.Generates (Opens.grothendieckTopology ↥X) F.val r},
    Subtype.val, ?_, fun i ↦ i.2⟩
  intro W
  rw [Opens.mem_grothendieckTopology]
  intro x hx
  obtain ⟨I₀, Y, f, hf, hgg⟩ := h.locally_finitelyGenerated ((opensToSmallEtale B X hX).obj W)
  obtain ⟨Z, g, hgmem, w, hwx⟩ := SmallEtale.exists_mem_arrows_mem_range B X hX hf
    (⟨x, hx⟩ : (toScheme B X hX).obj ((opensToSmallEtale B X hX).obj W))
  rw [Sieve.mem_ofArrows_iff] at hgmem
  obtain ⟨i, a, -⟩ := hgmem
  obtain ⟨n, s, hs⟩ := exists_generates_of_hasFiniteGlobalGenerators_over
    ((associatedModule B X hX).obj F) (Y i) (hgg i)
  obtain ⟨Z', c, ⟨w', hw'⟩, hgood⟩ := exists_imageOpen_generates B X hX F Z
    (fun j ↦ ((associatedModule B X hX).obj F).val.restrictₛₗ a.op (s j)) (hs.restrict a) w
  have hZZ : Z'.obj.hom.hom.base w' = x := by
    have e1 : Z'.obj.hom.hom.base w'
        = Z.obj.hom.hom.base ((toScheme B X hX).map c w') := by
      rw [show Z'.obj.hom = c.hom.left ≫ Z.obj.hom from (Over.w c.hom).symm]; rfl
    rw [e1, hw', BigEtaleOver.hom_hom_eq B X hX g.hom]
    exact congrArg Subtype.val hwx
  refine ⟨imageOpen B X hX Z', homOfLE ?_, ⟨⟨imageOpen B X hX Z', hgood⟩, ⟨𝟙 _⟩⟩, ⟨w', hZZ⟩⟩
  calc imageOpen B X hX Z' ≤ imageOpen B X hX Z := imageOpen_le_imageOpen B X hX c
    _ ≤ imageOpen B X hX ((opensToSmallEtale B X hX).obj W) := imageOpen_le_imageOpen B X hX g
    _ = W := imageOpen_opensObj B X hX W

end AlgebraicGeometry.SmallEtale

end
