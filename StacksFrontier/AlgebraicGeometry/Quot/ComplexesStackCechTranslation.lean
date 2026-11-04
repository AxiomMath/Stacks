module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackCechNerve
public import StacksFrontier.AlgebraicGeometry.Quot.DerivedHomDisjointUnionProductProof
public import StacksFrontier.AlgebraicGeometry.Quot.PicardDescent.BaseChange
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackPerfectDescent
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackDescentBridges
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeDerivedHomDualProved
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductSheaf
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackLimitDescentEq

/-!
# Translating between a Čech covering in `Complexes_{X/Y}` and its Čech nerve

Let `C : CechCover T I` be a Čech covering in `Complexes_{X/Y}` and let `R` be a refinement of it
indexed by a type in `Type u`, with disjoint union `V = ∐ W_k` and fppf covering `q : V ⟶ T`
(`AlgebraicGeometry.Space.ComplexesSituation.CechCover.SmallRefinement`). Stacks 0DLA is applied
to the base change `X ×_Y Č(V/T) ⟶ X_T` of the Čech nerve of `q`. This file supplies the
bookkeeping between the two sides.

* Every algebraic space `P` over a scheme `Z` mapping to `V` splits into the pieces
  `P ×_V W_k`, and the derived category of `P` is the product of those of the pieces
  (`AlgebraicGeometry.Space.SmallEtaleDerivedDisjointUnion`): morphisms are families of morphisms
  (`AlgebraicGeometry.Space.derivedHomDisjointUnionProduct`) and every family of objects comes
  from one object (`AlgebraicGeometry.Space.exists_iso_pull_of_isPullback_cofan`).
* For a test scheme `Z` with `c : Z ⟶ V`, the base changes `X_{Z ×_V W_k}` are the pieces of
  `X_Z` (`AlgebraicGeometry.Space.ComplexesSituation.CechCover.SmallRefinement.isPullback_piece`).

Nothing here is registered.

## References

* [Stacks Project, Tag 0DLA](https://stacks.math.columbia.edu/tag/0DLA)
* [Stacks Project, Tag 0DLH](https://stacks.math.columbia.edu/tag/0DLH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

attribute [local instance] AlgebraicGeometry.BigFppfSite.hasPullbacks_schemes
  AlgebraicGeometry.Space.instModulesHasDerivedCategory

namespace CategoryTheory.Functor

/-- A composite of fibres `Functor.fibreComp τ a b` with an identity left factor. -/
theorem fibreComp_id_left_eq {C₀ C₁ C₂ : Type*} [Category* C₀] [Category* C₁]
    [Category* C₂] {La : C₁ ⥤ C₀} {Lb : C₂ ⥤ C₁} {Lab : C₂ ⥤ C₀} (τ : Lab ≅ Lb ⋙ La)
    {M' : C₁} {M'' : C₂} (b : Lb.obj M'' ⟶ M') {c : Lab.obj M'' ⟶ La.obj M'}
    (h : La.map b = τ.inv.app M'' ≫ c) : fibreComp τ (𝟙 (La.obj M')) b = c := by
  simp only [fibreComp, h, Category.comp_id, Iso.hom_inv_id_app_assoc]

end CategoryTheory.Functor

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Objects on an algebraic space over a disjoint union of schemes -/

section Gluing

attribute [local instance] AlgebraicGeometry.Space.etaleModulePullback_additive
  AlgebraicGeometry.Space.preservesFiniteLimits_etaleModulePullback
  AlgebraicGeometry.Space.preservesFiniteColimits_etaleModulePullback

variable {ι : Type u} {W : ι → BigFppfOver B S hS} {W₀ : BigFppfOver B S hS}
  {w : ∀ k, W k ⟶ W₀}
  (hW : IsColimit (Cofan.mk ((BigFppfOver.toScheme B S hS).obj W₀)
    fun k => (BigFppfOver.toScheme B S hS).map (w k)))
  {V : AlgebraicSpaces B S hS} {p : V ⟶ (schemeSpaceFunctor B S hS).obj W₀}
  {V' : ι → AlgebraicSpaces B S hS} {j : ∀ k, V' k ⟶ V}
  {p' : ∀ k, V' k ⟶ (schemeSpaceFunctor B S hS).obj (W k)}
  (hsq : ∀ k, IsPullback (j k) (p' k) p ((schemeSpaceFunctor B S hS).map (w k)))

include hW hsq in
/-- **Objects in the derived category of an algebraic space over a disjoint union of schemes**:
for `V` over `W₀ = ∐ W_k` with pieces `V_k = V ×_{W₀} W_k` and projections `j_k : V_k ⟶ V`, every
family of objects `M_k` of `D(𝒪_{V_k})` is the family of restrictions `Lj_k^*K` of one object
`K` of `D(𝒪_V)`. Restriction to the pieces identifies `D(𝒪_V)` with `∏_k D(𝒪_{V_k})`. -/
theorem exists_iso_pull_of_isPullback_cofan (M : ∀ k, derivedModules B S hS (V' k)) :
    ∃ K : derivedModules B S hS V,
      Nonempty (∀ k, ((smallEtaleDerivedPullbackData B S hS).pull (j k)).obj K ≅ M k) := by
  have hj := isEtale_hom_of_isPullback_cofan hW hsq
  have := isEquivalence_pi'_etaleModulePullback_of_isPullback_cofan hW hsq hj
  have := fun k => hasDerivedModulePullbacks B S hS (j k)
  let Φ := Functor.pi' fun k => (etaleModulePullback.{u, u} B S hS (j k) (hj k)).mapDerivedCategory
  have : Φ.IsEquivalence := Functor.isEquivalence_pi'_mapDerivedCategory _
  exact ⟨Φ.objPreimage M, ⟨fun k =>
    (smallEtaleDerivedModulePullbackIsoEtale B S hS (j k) (hj k)).app _ ≪≫
      Pi.isoApp (Φ.objObjPreimageIso M) k⟩⟩

include hW hsq in
/-- Two morphisms in the derived category of an algebraic space over a disjoint union of schemes
agree as soon as their restrictions to every piece agree. -/
theorem hom_ext_of_isPullback_cofan {K E : derivedModules B S hS V} {f g : K ⟶ E}
    (h : ∀ k, ((smallEtaleDerivedPullbackData B S hS).pull (j k)).map f =
      ((smallEtaleDerivedPullbackData B S hS).pull (j k)).map g) : f = g :=
  (derivedHomDisjointUnionProduct B S hS W W₀ w hW p V' j p' hsq K E).1 (funext h)

include hW hsq in
/-- A family of morphisms between the restrictions of two objects to the pieces of an algebraic
space over a disjoint union of schemes is the family of restrictions of one morphism. -/
theorem exists_hom_of_isPullback_cofan {K E : derivedModules B S hS V}
    (f : ∀ k, ((smallEtaleDerivedPullbackData B S hS).pull (j k)).obj K ⟶
      ((smallEtaleDerivedPullbackData B S hS).pull (j k)).obj E) :
    ∃ g : K ⟶ E, ∀ k, ((smallEtaleDerivedPullbackData B S hS).pull (j k)).map g = f k := by
  obtain ⟨g, hg⟩ := (derivedHomDisjointUnionProduct B S hS W W₀ w hW p V' j p' hsq K E).2 f
  exact ⟨g, fun k => congrFun hg k⟩

include hW hsq in
/-- A family of isomorphisms between the restrictions of two objects to the pieces of an
algebraic space over a disjoint union of schemes is the family of restrictions of one
isomorphism. -/
theorem exists_iso_of_isPullback_cofan {K E : derivedModules B S hS V}
    (f : ∀ k, ((smallEtaleDerivedPullbackData B S hS).pull (j k)).obj K ≅
      ((smallEtaleDerivedPullbackData B S hS).pull (j k)).obj E) :
    ∃ g : K ≅ E, ∀ k, ((smallEtaleDerivedPullbackData B S hS).pull (j k)).map g.hom =
      (f k).hom := by
  obtain ⟨g, hg⟩ := exists_hom_of_isPullback_cofan hW hsq fun k => (f k).hom
  obtain ⟨g', hg'⟩ := exists_hom_of_isPullback_cofan hW hsq fun k => (f k).inv
  refine ⟨⟨g, g', ?_, ?_⟩, hg⟩
  · exact hom_ext_of_isPullback_cofan hW hsq fun k => by
      rw [Functor.map_comp, hg, hg', Iso.hom_inv_id, CategoryTheory.Functor.map_id]
  · exact hom_ext_of_isPullback_cofan hW hsq fun k => by
      rw [Functor.map_comp, hg, hg', Iso.inv_hom_id, CategoryTheory.Functor.map_id]

include hW hsq in
/-- **Quasi-coherence on an algebraic space over a disjoint union of schemes is checked on the
pieces**: an `𝒪_V`-module whose restrictions to the pieces `V_k = V ×_{W₀} W_k` are
quasi-coherent is quasi-coherent. Every étale chart of `V` is covered by its base changes to the
pieces (`AlgebraicGeometry.Space.ofArrows_counit_mem_topology_of_isPullback_cofan`), and global
presentations over the charts of a piece are global presentations over the composite charts of
`V` (`AlgebraicGeometry.Space.hasGlobalPresentation_over_postcomp_iff`). -/
theorem isQuasicoherentOnSite_of_isPullback_cofan (M : Modules.{u, u} B S hS V.1 V.2)
    (h : ∀ k, ((etaleModulePullback B S hS (j k)
      (isEtale_hom_of_isPullback_cofan hW hsq k)).obj M).IsQuasicoherentOnSite) :
    M.IsQuasicoherentOnSite := by
  have hj := isEtale_hom_of_isPullback_cofan hW hsq
  have hrep := fun k => relativelyRepresentable_hom_of_isPullback_cofan hsq k
  refine (Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_hasGlobalPresentation
    M).2 ⟨{Z : (smallEtaleRingedSite B S hS V.1 V.2).C // (M.over Z).HasGlobalPresentation},
      fun z => z.1, fun W => ?_, fun z => z.2⟩
  refine (smallEtaleRingedSite B S hS V.1 V.2).J.transitive
    (ofArrows_counit_mem_topology_of_isPullback_cofan hW hsq hj hrep W) _ ?_
  intro W' p hp
  obtain ⟨_, a, _, ⟨k⟩, rfl⟩ := hp
  set Vk := (smallBaseChange B S hS (j k) (hrep k)).obj W
  obtain ⟨I₁, V₁, q₁, hcov₁, hpres₁⟩ := (h k).locally_hasGlobalPresentation Vk
  have hpush := (SmallEtale.coverPreserving_smallEtalePostcomp B S hS (j k) (hj k)).cover_preserve
    hcov₁
  have hle : Sieve.functorPushforward (ringedSitePostcomp B S hS (j k) (hj k))
      (Sieve.ofArrows V₁ q₁) ≤
      Sieve.ofObjects (fun z : {Z : (smallEtaleRingedSite B S hS V.1 V.2).C //
        (M.over Z).HasGlobalPresentation} => z.1)
        ((ringedSitePostcomp B S hS (j k) (hj k)).obj Vk) := by
    rintro T r ⟨Z₀, r₀, q, hr₀, rfl⟩
    obtain ⟨i, b, -⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hr₀
    exact ⟨⟨_, (hasGlobalPresentation_over_postcomp_iff B S hS (j k) (hj k) M (V₁ i)).1
      (hpres₁ i)⟩, ⟨q ≫ (ringedSitePostcomp B S hS (j k) (hj k)).map b⟩⟩
  have hobj := (smallEtaleRingedSite B S hS V.1 V.2).J.superset_covering hle hpush
  have hα := (smallEtaleRingedSite B S hS V.1 V.2).J.pullback_stable a hobj
  refine (smallEtaleRingedSite B S hS V.1 V.2).J.superset_covering ?_ hα
  intro T b hb
  exact hb

include hW hsq in
/-- **Quasi-coherent cohomology on an algebraic space over a disjoint union of schemes is
checked on the pieces.** -/
theorem isSmallEtaleQuasicoherent_of_isPullback_cofan (K : derivedModules B S hS V)
    (h : ∀ k (n : ℤ), ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS (V' k).1 (V' k).2)
      n).obj (((smallEtaleDerivedPullbackData B S hS).pull (j k)).obj K)).IsQuasicoherentOnSite)
    (n : ℤ) :
    ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS V.1 V.2) n).obj
      K).IsQuasicoherentOnSite := by
  have hj := isEtale_hom_of_isPullback_cofan hW hsq
  have := fun k => hasDerivedModulePullbacks B S hS (j k)
  refine isQuasicoherentOnSite_of_isPullback_cofan hW hsq _ fun k => ?_
  refine SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((Functor.mapDerivedCategoryHomologyIso (etaleModulePullback B S hS (j k) (hj k)) n).app K) ?_
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((DerivedCategory.homologyFunctor _ n).mapIso
      ((smallEtaleDerivedModulePullbackIsoEtale B S hS (j k) (hj k)).app K)) (h k n)

end Gluing

namespace ComplexesSituation

variable {D : ComplexesSituation B S hS}

/-! ### Morphisms of `Complexes_{X/Y}` through a fixed one -/

section Lift

variable {x y z : ComplexesObject D}

/-- The restriction `L h^* A` of an object of `Complexes_{X/Y}` along a morphism of test
schemes. -/
abbrev restrictComplex (A : ComplexesObject D) {V : SchemesOver D.Y} (h : V ⟶ A.T) :
    ComplexesObject D :=
  ⟨V, ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap h)).obj A.E,
    relativelyPerfectBaseChange D h A.E A.relativelyPerfect,
    D.hasNoNegativeFibreExt_pull h A.E A.noNegativeFibreExt⟩

/-- The canonical morphism `L h^* A ⟶ A` of `Complexes_{X/Y}` over `h`. -/
abbrev restrictComplexHom (A : ComplexesObject D) {V : SchemesOver D.Y} (h : V ⟶ A.T) :
    ComplexesHom (restrictComplex A h) A :=
  ⟨h, 𝟙 (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap h)).obj A.E),
    IsIso.id _⟩

/-- **The lift of a morphism of `Complexes_{X/Y}` through another one** along a factorization
`β ≫ Φ.base` of its base map, given by its comparison of complexes `c`: every morphism of
`Complexes_{X/Y}` is cartesian. -/
def liftAlong (Φ : ComplexesHom y x) (β : z.T ⟶ y.T)
    (c : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (β ≫ Φ.base))).obj x.E ≅
      z.E) : ComplexesHom z y :=
  @fillIn _ _ _ _ _ _ _ Φ β c.hom (Iso.isIso_hom c)

/-- The base map of `liftAlong Φ β c` is `β`. -/
theorem liftAlong_base (Φ : ComplexesHom y x) (β : z.T ⟶ y.T)
    (c : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (β ≫ Φ.base))).obj x.E ≅
      z.E) : (liftAlong Φ β c).base = β :=
  rfl

/-- The composite of `liftAlong Φ β c` with `Φ` is the morphism over `β ≫ Φ.base` with
comparison of complexes `c`. -/
theorem liftAlong_comp (Φ : ComplexesHom y x) (β : z.T ⟶ y.T)
    (c : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (β ≫ Φ.base))).obj x.E ≅
      z.E) : (liftAlong Φ β c).comp Φ = ⟨β ≫ Φ.base, c.hom, Iso.isIso_hom c⟩ :=
  fillIn_comp Φ β c.hom (Iso.isIso_hom c)

/-- A morphism over `β` whose composite with `Φ` is the morphism over `β ≫ Φ.base` with
comparison `c` is `liftAlong Φ β c`. -/
theorem eq_liftAlong (Φ : ComplexesHom y x) (β : z.T ⟶ y.T)
    (c : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (β ≫ Φ.base))).obj x.E ≅
      z.E) {m : ComplexesHom z y} (hb : m.base = β)
    (h : m.comp Φ = ⟨β ≫ Φ.base, c.hom, Iso.isIso_hom c⟩) : m = liftAlong Φ β c :=
  eq_fillIn Φ β c.hom (Iso.isIso_hom c) hb h

/-- Equal morphisms of `Complexes_{X/Y}` have heterogeneously equal comparisons of complexes. -/
private theorem heq_fibre_of_eq {m n : ComplexesHom z y} (e : m = n) : HEq m.fibre n.fibre := by
  subst e
  rfl

/-- **Composition with a morphism of `Complexes_{X/Y}` on the right is injective** on the
morphisms with a given base map. -/
theorem complexesHom_cancel_right (Φ : ComplexesHom y x) {m n : ComplexesHom z y}
    (hb : m.base = n.base) (h : m.comp Φ = n.comp Φ) : m = n := by
  obtain ⟨mb, mf, mi⟩ := m
  obtain ⟨nb, nf, ni⟩ := n
  change mb = nb at hb
  subst hb
  have hiso := Φ.isIso_fibre
  have h1 : Functor.fibreComp (D.compComparison mb Φ.base) mf Φ.fibre =
      Functor.fibreComp (D.compComparison mb Φ.base) nf Φ.fibre := by
    have h0 : (ComplexesHom.comp (⟨mb, mf, mi⟩ : ComplexesHom z y) Φ).fibre =
        (ComplexesHom.comp (⟨mb, nf, ni⟩ : ComplexesHom z y) Φ).fibre :=
      eq_of_heq (heq_fibre_of_eq h)
    dsimp only [ComplexesHom.comp] at h0
    exact h0
  refine ComplexesHom.ext rfl ?_
  refine (eqToHom_self_comp _ _).trans ?_
  exact Functor.fibreComp_left_injective (D.compComparison mb Φ.base) Φ.fibre h1

end Lift

namespace CechCover

variable {T : SchemesOver D.Y} {I : Type (u + 1)} {C : CechCover T I}

namespace SmallRefinement

variable (R : C.SmallRefinement)

/-! ### The disjoint union of a refinement as a test scheme -/

section Union

/-- The disjoint union `V` of a refinement, as a test scheme over `Y` through `q : V ⟶ T`. -/
abbrev unionTest : SchemesOver D.Y :=
  restrictTest T R.q

/-- The morphism `q : V ⟶ T` of a refinement, as a morphism of test schemes over `Y`. -/
abbrev unionHom : R.unionTest ⟶ T :=
  restrictTestHom T R.q

/-- A member `W_k` of a refinement, as a test scheme over `Y`. -/
abbrev memberTest (k : R.ι) : SchemesOver D.Y :=
  restrictTest T (R.j k ≫ R.q)

/-- The injection `W_k ⟶ V` of a member of a refinement, as a morphism of test schemes over
`Y`. -/
abbrev memberIncl (k : R.ι) : R.memberTest k ⟶ R.unionTest :=
  restrictTestMap T (R.j k) rfl

/-- The morphism `W_k ⟶ T_{σ k}` from a member of a refinement to the member of the covering
it refines, as a morphism of test schemes over `Y`. -/
def memberMap (k : R.ι) : R.memberTest k ⟶ (C.X (R.σ k)).T :=
  CostructuredArrow.homMk (R.h k) (by
    change (schemeSpaceFunctor B S hS).map (R.h k) ≫ (C.X (R.σ k)).T.hom =
      (schemeSpaceFunctor B S hS).map (R.j k ≫ R.q) ≫ T.hom
    rw [← CostructuredArrow.w (C.a (R.σ k)), ← Category.assoc, ← Functor.map_comp, R.fac])

/-- The square from a member `W_k` through `T_{σ k}` and through `V` to `T` commutes. -/
theorem memberMap_comp_a (k : R.ι) :
    R.memberMap k ≫ C.a (R.σ k) = R.memberIncl k ≫ R.unionHom :=
  CostructuredArrow.hom_ext _ _ (R.fac k)

/-- The base changes of the members of a refinement are the pieces of the base change of its
disjoint union. -/
theorem isPullback_memberIncl (k : R.ι) :
    IsPullback (D.relativeMap (R.memberIncl k)) (D.projection (R.memberTest k))
      (D.projection R.unionTest) ((schemeSpaceFunctor B S hS).map (R.j k)) :=
  isPullback_baseChangeMap D.f (R.memberIncl k)

/-- There is an object of `D(𝒪_{X_V})` on the disjoint union `V` of a refinement whose restriction
to every member `X_{W_k}` is isomorphic to the pullback of `K_{σ k}` along `W_k ⟶ T_{σ k}`. -/
theorem exists_unionObject :
    ∃ K : derivedModules B S hS (D.space R.unionTest),
      Nonempty (∀ k, ((smallEtaleDerivedPullbackData B S hS).pull
        (D.relativeMap (R.memberIncl k))).obj K ≅
          ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (R.memberMap k))).obj
            (C.X (R.σ k)).E) :=
  exists_iso_pull_of_isPullback_cofan R.isColimit R.isPullback_memberIncl _

/-- **The complex `K_0` on the disjoint union of a refinement**: the object of `D(𝒪_{X_V})` whose
restriction to every member `X_{W_k}` is the pullback of `K_{σ k}` along `W_k ⟶ T_{σ k}`. -/
def unionObject : derivedModules B S hS (D.space R.unionTest) :=
  R.exists_unionObject.choose

/-- The restriction of `K_0` to a member of the refinement. -/
def unionObjectIso (k : R.ι) :
    ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (R.memberIncl k))).obj
        R.unionObject ≅
      ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (R.memberMap k))).obj
        (C.X (R.σ k)).E :=
  R.exists_unionObject.choose_spec.some k

/-- The members of a refinement cover its disjoint union, indexed in `Type (u + 1)`. -/
theorem ofArrows_memberIncl_mem_topology :
    Sieve.ofArrows (fun k : ULift.{u + 1} R.ι => (R.memberTest k.down).left)
      (fun k => (R.memberIncl k.down).left) ∈ BigFppfOver.topology B S hS R.unionTest.left := by
  have hopen := fun k => isOpenImmersion_of_isColimit_cofanMk R.isColimit k
  have h := BigFppfOver.ofArrows_mem_topology_of_flat_lfp B S hS R.W R.j
    (fun x => exists_mem_range_of_isColimit_cofanMk R.isColimit x)
    (fun k => by have := hopen k; infer_instance) (fun k => by have := hopen k; infer_instance)
  refine (BigFppfOver.topology B S hS).superset_covering ?_ h
  intro Z g hg
  obtain ⟨k, a, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hg
  exact (Sieve.mem_ofArrows_iff _ _ _).mpr ⟨ULift.up k, a, rfl⟩

/-- A relatively perfect complex has quasi-coherent cohomology (Stacks 08JL: it is
pseudo-coherent). -/
theorem hasQuasicoherentCohomology_of_isRelativelyPerfect {T' : SchemesOver D.Y}
    {E : derivedModules B S hS (D.space T')} (hE : D.IsRelativelyPerfect T' E) :
    D.HasQuasicoherentCohomology T' E := fun n =>
  isQuasicoherentOnSite_homology_of_isPseudoCoherentFrom_unconditional B S hS _ _ E (n - 1) n
    ((RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom _ E).1 hE.1 (n - 1))
    (by omega)

/-- `K_0` has quasi-coherent cohomology: its restrictions to the members of the refinement are
pullbacks of the relatively perfect `K_{σ k}`. -/
theorem unionObject_hasQuasicoherentCohomology :
    D.HasQuasicoherentCohomology R.unionTest R.unionObject := by
  intro n
  refine isSmallEtaleQuasicoherent_of_isPullback_cofan R.isColimit R.isPullback_memberIncl _
    (fun k m => ?_) n
  have h := hasQuasicoherentCohomology_of_isRelativelyPerfect
    (relativelyPerfectBaseChange D (R.memberMap k) _ (C.X (R.σ k)).relativelyPerfect) m
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((DerivedCategory.homologyFunctor _ m).mapIso (R.unionObjectIso k)).symm h

/-- `K_0` is perfect relative to the disjoint union (Stacks 0DL1 with 0DL2, along the members). -/
theorem unionObject_isRelativelyPerfect : D.IsRelativelyPerfect R.unionTest R.unionObject :=
  D.relativelyPerfectDescends R.unionTest (fun k : ULift.{u + 1} R.ι => R.memberTest k.down)
    (fun k => R.memberIncl k.down) R.ofArrows_memberIncl_mem_topology R.unionObject
    R.unionObject_hasQuasicoherentCohomology fun k =>
      isRelativelyPerfect_of_iso (R.unionObjectIso k.down)
        (relativelyPerfectBaseChange D (R.memberMap k.down) _ (C.X (R.σ k.down)).relativelyPerfect)

/-- `K_0` has no negative self-extensions on the fibres (Stacks 0DLC (1), along the members). -/
theorem unionObject_hasNoNegativeFibreExt : D.HasNoNegativeFibreExt R.unionTest R.unionObject :=
  noNegativeFibreExtDescends_of_existsNegativeExtLocus D (existsNegativeExtLocus_proved B S hS)
    R.unionTest (fun k : ULift.{u + 1} R.ι => R.memberTest k.down) (fun k => R.memberIncl k.down)
    R.ofArrows_memberIncl_mem_topology R.unionObject R.unionObject_isRelativelyPerfect fun k =>
      hasNoNegativeFibreExt_of_iso (R.unionObjectIso k.down)
        (D.hasNoNegativeFibreExt_pull (R.memberMap k.down) _ (C.X (R.σ k.down)).noNegativeFibreExt)

/-- **`K_0` as an object of `Complexes_{X/Y}`** over the disjoint union of a refinement. -/
abbrev unionComplex : ComplexesObject D :=
  ⟨R.unionTest, R.unionObject, R.unionObject_isRelativelyPerfect,
    R.unionObject_hasNoNegativeFibreExt⟩

end Union

/-! ### The pieces of a test scheme over the disjoint union of a refinement -/

section Pieces

variable {Z : SchemesOver D.Y} (c : Z ⟶ R.unionTest)

/-- The piece `Z ×_V W_k` of a test scheme `Z` over the disjoint union `V` of a refinement, as a
test scheme over `Y`. -/
abbrev piece (k : R.ι) : SchemesOver D.Y :=
  restrictTest Z (pullback.fst c.left (R.j k))

/-- The inclusion `Z ×_V W_k ⟶ Z` of a piece, as a morphism of test schemes over `Y`. -/
abbrev pieceHom (k : R.ι) : R.piece c k ⟶ Z :=
  restrictTestHom Z (pullback.fst c.left (R.j k))

/-- The projection `Z ×_V W_k ⟶ W_k` of a piece, as a morphism of test schemes over `Y`. -/
def pieceMember (k : R.ι) : R.piece c k ⟶ R.memberTest k :=
  CostructuredArrow.homMk (pullback.snd c.left (R.j k)) (by
    have e : pullback.snd c.left (R.j k) ≫ R.j k ≫ R.q =
        pullback.fst c.left (R.j k) ≫ c.left ≫ R.q := by
      rw [← pullback.condition_assoc]
    have e' := congrArg (fun g => (schemeSpaceFunctor B S hS).map g ≫ T.hom) e
    change (schemeSpaceFunctor B S hS).map (pullback.snd c.left (R.j k)) ≫
        (schemeSpaceFunctor B S hS).map (R.j k ≫ R.q) ≫ T.hom =
      (schemeSpaceFunctor B S hS).map (pullback.fst c.left (R.j k)) ≫ Z.hom
    rw [← CostructuredArrow.w c]
    change _ = (schemeSpaceFunctor B S hS).map (pullback.fst c.left (R.j k)) ≫
      (schemeSpaceFunctor B S hS).map c.left ≫ (schemeSpaceFunctor B S hS).map R.q ≫ T.hom
    simp only [Functor.map_comp, Category.assoc] at e' ⊢
    exact e')

/-- The square from a piece `Z ×_V W_k` through `Z` and through `W_k` to `V` commutes. -/
theorem pieceHom_comp (k : R.ι) :
    R.pieceHom c k ≫ c = R.pieceMember c k ≫ R.memberIncl k :=
  CostructuredArrow.hom_ext _ _ (by
    simp only [CostructuredArrow.comp_left]
    exact pullback.condition)

/-- **The base changes of the pieces of a test scheme are the pieces of its base change**: the
square `X_{Z ×_V W_k} ⟶ X_Z` over `W_k ⟶ V` is cartesian. -/
theorem isPullback_piece (k : R.ι) :
    IsPullback (D.relativeMap (R.pieceHom c k))
      (D.projection (R.piece c k) ≫ (schemeSpaceFunctor B S hS).map (pullback.snd c.left (R.j k)))
      (D.projection Z ≫ (schemeSpaceFunctor B S hS).map c.left)
      ((schemeSpaceFunctor B S hS).map (R.j k)) :=
  (isPullback_baseChangeMap D.f (R.pieceHom c k)).paste_vert
    (isPullback_schemeSpaceFunctor_map (IsPullback.of_hasPullback c.left (R.j k)))

/-- The pullback of `K_0` to a test scheme over the disjoint union, restricted to a piece
`Z ×_V W_k`, is the pullback of `K_{σ k}`. -/
def pieceIso (k : R.ι) :
    ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (R.pieceHom c k))).obj
        (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap c)).obj R.unionObject) ≅
      ((smallEtaleDerivedPullbackData B S hS).pull
        (D.relativeMap (R.pieceMember c k ≫ R.memberMap k))).obj (C.X (R.σ k)).E :=
  (D.compComparison (R.pieceHom c k) c).symm.app _ ≪≫
    (D.relativeMapComparison (R.pieceHom_comp c k)).app _ ≪≫
    (D.compComparison (R.pieceMember c k) (R.memberIncl k)).app _ ≪≫
    ((smallEtaleDerivedPullbackData B S hS).pull
      (D.relativeMap (R.pieceMember c k))).mapIso (R.unionObjectIso k) ≪≫
    (D.compComparison (R.pieceMember c k) (R.memberMap k)).symm.app _

/-! ### The pullback of `K_0` against a member of the covering -/

variable {c} {i : I} {z : Z ⟶ (C.X i).T} (hz : z ≫ C.a i = c ≫ R.unionHom)

include hz in
/-- The two morphisms from a piece `Z ×_V W_k` to `T`, through `T_{σ k}` and through `T_i`,
agree on underlying schemes. -/
theorem pieceMember_comp_eq (k : R.ι) :
    (R.pieceMember c k ≫ R.memberMap k).left ≫ (C.a (R.σ k)).left =
      (R.pieceHom c k ≫ z).left ≫ (C.a i).left := by
  have e : (R.pieceMember c k ≫ R.memberMap k) ≫ C.a (R.σ k) = (R.pieceHom c k ≫ z) ≫ C.a i := by
    rw [Category.assoc, R.memberMap_comp_a, Category.assoc, hz, ← Category.assoc,
      ← Category.assoc, R.pieceHom_comp]
  simpa only [CostructuredArrow.comp_left] using congrArg CommaMorphism.left e

/-- The morphism from a piece `Z ×_V W_k` to the double overlap `T_{σ k} ×_T T_i`, for a test
scheme `Z` mapping to the member `T_i`. -/
def overlapMap (k : R.ι) : R.piece c k ⟶ (C.X₂ (R.σ k) i).T :=
  CostructuredArrow.homMk ((C.isPullback₂ (R.σ k) i).lift (R.pieceMember c k ≫ R.memberMap k).left
    (R.pieceHom c k ≫ z).left (R.pieceMember_comp_eq hz k)) (by
    rw [← CostructuredArrow.w (C.n (R.σ k) i).base, ← Category.assoc, ← Functor.map_comp,
      IsPullback.lift_fst]
    exact CostructuredArrow.w (R.pieceMember c k ≫ R.memberMap k))

/-- The morphism to the double overlap followed by its projection to `T_{σ k}` is
`Z ×_V W_k ⟶ W_k ⟶ T_{σ k}`. -/
theorem overlapMap_comp_n (k : R.ι) :
    R.overlapMap hz k ≫ (C.n (R.σ k) i).base = R.pieceMember c k ≫ R.memberMap k :=
  CostructuredArrow.hom_ext _ _ (IsPullback.lift_fst _ _ _ _)

/-- The morphism to the double overlap followed by its projection to `T_i` is
`Z ×_V W_k ⟶ Z ⟶ T_i`. -/
theorem overlapMap_comp_m (k : R.ι) :
    R.overlapMap hz k ≫ (C.m (R.σ k) i).base = R.pieceHom c k ≫ z :=
  CostructuredArrow.hom_ext _ _ (IsPullback.lift_snd _ _ _ _)

/-- On a piece `Z ×_V W_k`, the pullback of `K_0` against the pullback of `K_i`: the gluing
isomorphism `φ_{σ k, i}` restricted along the morphism to the double overlap. -/
def pieceToMemberIso (k : R.ι) :
    ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (R.pieceHom c k))).obj
        (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap c)).obj R.unionObject) ≅
      ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (R.pieceHom c k))).obj
        (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap z)).obj (C.X i).E) :=
  R.pieceIso c k ≪≫ (D.relativeMapComparison (R.overlapMap_comp_n hz k).symm).app _ ≪≫
    asIso (D.restrictComparison (homComparison (C.n (R.σ k) i) (C.m (R.σ k) i))
      (R.overlapMap hz k)) ≪≫
    (D.relativeMapComparison (R.overlapMap_comp_m hz k)).app _ ≪≫
    (D.compComparison (R.pieceHom c k) z).app _

/-- There is an isomorphism from the pullback of `K_0` to the pullback of `K_i` on `Z` whose
restriction to every piece `Z ×_V W_k` is `pieceToMemberIso`. -/
theorem exists_toMember :
    ∃ g : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap c)).obj R.unionObject ≅
        ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap z)).obj (C.X i).E,
      ∀ k, ((smallEtaleDerivedPullbackData B S hS).pull
        (D.relativeMap (R.pieceHom c k))).map g.hom = (R.pieceToMemberIso hz k).hom :=
  exists_iso_of_isPullback_cofan R.isColimit (R.isPullback_piece c) _

/-- **The pullback of `K_0` against a member of the covering**: for a test scheme `Z` over the
disjoint union `V` of a refinement, mapping to the member `T_i` over `T`, the pullback of `K_0` is
the pullback of `K_i`, through the gluing isomorphisms `φ_{σ k, i}` on the pieces. -/
def toMember : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap c)).obj
      R.unionObject ≅
    ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap z)).obj (C.X i).E :=
  (R.exists_toMember hz).choose

/-- The restriction of `toMember` to a piece `Z ×_V W_k` is `pieceToMemberIso`. -/
theorem toMember_restrict (k : R.ι) :
    ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (R.pieceHom c k))).map
      (R.toMember hz).hom = (R.pieceToMemberIso hz k).hom :=
  (R.exists_toMember hz).choose_spec k

end Pieces

/-! ### Morphisms of `Complexes_{X/Y}` out of an object over the disjoint union -/

section PiecesHom

variable {A X : ComplexesObject D} (c : A.T ⟶ R.unionTest)

/-- **Two morphisms of `Complexes_{X/Y}` out of an object over the disjoint union of a refinement
agree as soon as their restrictions to the pieces agree.** -/
theorem complexesHom_ext_pieces {g g' : ComplexesHom A X} (hb : g.base = g'.base)
    (h : ∀ k, (restrictComplexHom A (R.pieceHom c k)).comp g =
      (restrictComplexHom A (R.pieceHom c k)).comp g') : g = g' := by
  obtain ⟨b, f, hf⟩ := g
  obtain ⟨b', f', hf'⟩ := g'
  change b = b' at hb
  subst hb
  have hfib : f = f' := hom_ext_of_isPullback_cofan R.isColimit (R.isPullback_piece c) fun k => by
    have h0 : ((restrictComplexHom A (R.pieceHom c k)).comp (⟨b, f, hf⟩ : ComplexesHom A X)).fibre =
        ((restrictComplexHom A (R.pieceHom c k)).comp (⟨b, f', hf'⟩ : ComplexesHom A X)).fibre :=
      eq_of_heq (heq_fibre_of_eq (h k))
    dsimp only [ComplexesHom.comp] at h0
    exact Functor.map_eq_of_fibreComp_eq _ _ h0
  subst hfib
  rfl

/-- **Morphisms of `Complexes_{X/Y}` out of an object over the disjoint union of a refinement
glue from the pieces**: a family of comparisons on the restrictions of `A` to the pieces of
`A.T`, over the restrictions of a fixed base map `b`, is the family of restrictions of one
morphism over `b`. -/
theorem exists_complexesHom_of_pieces (b : A.T ⟶ X.T)
    (e : ∀ k, ((smallEtaleDerivedPullbackData B S hS).pull
      (D.relativeMap (R.pieceHom c k ≫ b))).obj X.E ≅
        ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (R.pieceHom c k))).obj A.E) :
    ∃ g : ComplexesHom A X, g.base = b ∧
      ∀ k, (restrictComplexHom A (R.pieceHom c k)).comp g =
        ⟨R.pieceHom c k ≫ b, (e k).hom, Iso.isIso_hom _⟩ := by
  obtain ⟨F, hF⟩ := exists_iso_of_isPullback_cofan R.isColimit (R.isPullback_piece c)
    (K := ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap b)).obj X.E) (E := A.E)
    fun k => (D.compComparison (R.pieceHom c k) b).symm.app X.E ≪≫ e k
  refine ⟨⟨b, F.hom, Iso.isIso_hom _⟩, rfl, fun k => ?_⟩
  have hk := hF k
  simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom] at hk
  refine complexesHom_eq_of_heq rfl (heq_of_eq ?_)
  dsimp only [ComplexesHom.comp]
  exact Functor.fibreComp_id_left_eq _ _ hk

end PiecesHom


end SmallRefinement

end CechCover

end ComplexesSituation

end AlgebraicGeometry.Space

end
