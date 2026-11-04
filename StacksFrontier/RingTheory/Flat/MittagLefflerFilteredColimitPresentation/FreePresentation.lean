module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Util.CountHeartbeats
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.Presentable.Directed
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.MittagLeffler.Colimit
public import StacksFrontier.Algebra.MittagLeffler.Defs
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.AffineLocalization
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finite
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Restriction
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.WeaklyAssociated
public import StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.FreeSectionsFiniteType05MF
public import StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.HenselianCollapse
public import StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.ProjectiveSectionsAlongFibre
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleLocalization.EtalePullback
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.FlatLocus
public import StacksFrontier.AlgebraicGeometry.Flatness.WeaklyAssociated
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.Henselization
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.CompositeFibre
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.AffineComparison
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.PullbackFlatness
public import StacksFrontier.AlgebraicGeometry.Properties.PrincipalOpens.Sections
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
public import StacksFrontier.RingTheory.Etale.FilteredColimit.Basic
public import StacksFrontier.RingTheory.Etale.IndEtaleUniverse
public import StacksFrontier.RingTheory.Henselian.FiniteType.StrictlyHenselian
public import StacksFrontier.RingTheory.Henselian.QuasiFinite
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.BaseChange
public import StacksFrontier.RingTheory.Henselian.TFAE
public import StacksFrontier.Topology.Sheaves.Modules.FiniteType
public import StacksFrontier.Topology.Sheaves.Modules.Quasicoherent
import StacksFrontier.AlgebraicGeometry.Flatness.RelativelyPure.BaseChange
public import StacksFrontier.RingTheory.Flat.MittagLefflerFilteredColimitPresentation.LocalizationColimit
import all StacksFrontier.RingTheory.Flat.MittagLefflerFilteredColimitPresentation.LocalizationAndAssociatedPoints
import all StacksFrontier.RingTheory.Flat.MittagLefflerFilteredColimitPresentation.LocalizationColimit

/-!
# The filtered-colimit presentation of a flat finite module over a henselian base

Let `A → B` be an essentially finite type local homomorphism of local rings with `A` henselian,
and let `N` be a finite `B`-module which is flat over `A`. The first conclusion of Stacks 05U7
says that `N` is a filtered colimit `N = colim_i F_i` of free `A`-modules whose transition maps
`u_i : F_i → F_{i'}` stay injective after reduction modulo the maximal ideal of `A`.

That conclusion is proved here. The second conclusion of Stacks 05U7 -- that `N` is a
Mittag-Leffler `A`-module -- is deduced from this one in
`StacksFrontier.RingTheory.Flat.MittagLefflerEssFiniteType`.

## Main definitions

There are no new definitions.

## Main results

* `exists_filteredColimit_free_with_injective_reduction`: the filtered-colimit presentation,
  which is the first conclusion of Stacks 05U7.

## Implementation notes

Reduction modulo the maximal ideal is represented by quotienting an `A`-module `F` by
`𝔪_A • ⊤`. The colimit is only required to be isomorphic to the given module, not definitionally
equal to it, and the colimit diagram lives in the joint universe of the ring and the module, so
its vertex is compared with the universe lift of `N`.

The proof follows the source. The essentially-finite-type algebra `B` is replaced by the finite
type `A`-subalgebra `Algebra.EssFiniteType.subalgebra A B` and `N` by a finite submodule `M₀`
over it which spans `N` after localizing, so that `N` is a localization of `M₀`; `M₀` is spread
out into the quasi-coherent module `M₀~` of finite type on a finite type `A`-scheme `X`, whose
stalk at the prime `x` corresponding to the maximal ideal of `B` is `N`. The scheme is then
shrunk to an affine open on which every associated point of the closed fibre specializes to `x`,
which is possible because the closed fibre is locally Noetherian, so that its set of associated
points is finite (Stacks 01XZ and 02OJ). Stacks 05MF,
`AlgebraicGeometry.exists_elementaryEtaleNeighborhood_free_sections_of_finiteType`, supplies an
elementary étale neighbourhood of the closed point together with an affine open of the base
change on which the sections are free; because `A` is henselian that base change is an
isomorphism (`AlgebraicGeometry.isIso_fromSpecStalk_comp_of_henselian`), so those free sections
are already sections over `A`. The system of free modules is the system of localizations of
those sections at the elements of the prime complement of `x`, whose colimit is the stalk at
`x`, and the reductions modulo `𝔪_A` stay injective because an element of a kernel would be a
section of the closed fibre supported away from `x`, which the shrinking step has excluded.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits IsLocalRing AlgebraicGeometry
open scoped AlgebraicGeometry
open scoped TensorProduct

universe u v uM uP uQ uN w
private lemma mem_ideal_smul_top_congr
    {R M : Type*} [CommRing R] [AddCommGroup M]
    (P Q : Module R M) (h : P = Q) (I : Ideal R) (m : M) :
    (letI := P; m ∈ I • (⊤ : Submodule R M)) ↔
      (letI := Q; m ∈ I • (⊤ : Submodule R M)) := by
  subst Q
  rfl

/-- **The geometric half of conclusion (1) of Stacks 05U7.** Let `A` be a henselian local ring,
let `A'` be a copy of it in the universe of a scheme `X`, let `f : X ⟶ Spec A'` be locally of
finite type and let `F` be a quasi-coherent `𝒪_X`-module of finite type which is flat over `A'`
at a point `x` above the closed point. Let `A` act on the global sections of `X` through a ring
map `aX` factoring the structure map, and on the stalk `F_x` through `aX` and the germ. Then
`F_x` is a filtered colimit of free `A`-modules whose transition maps stay injective modulo the
maximal ideal of `A`.

This is the geometry of the source's proof: shrink `X` so that every associated point of the
closed fibre specializes to `x` (Stacks 01XZ and 02OJ make that a finite condition), apply
Stacks 05MF to get free sections on an affine open of a base change along an elementary étale
neighbourhood, collapse that base change because `A` is henselian (Stacks 05U7's own step, here
`AlgebraicGeometry.isIso_fromSpecStalk_comp_of_henselian`), and present the stalk as the
filtered colimit of the localizations of those sections.

It is stated separately from `exists_filteredColimit_free_with_injective_reduction` because
`X`, `F`, `f` and `x` are *variables* here. In the main theorem they are local definitions
built from a `ULift` of a `Shrink` of a subalgebra, and every unification against them unfolds
that tower; keeping the geometry in a context where they are opaque is what holds the
elaboration of both halves inside the default heartbeat budget. -/
private theorem exists_filteredColimit_free_of_isFlatOverAt
    {A : Type u} [CommRing A] [HenselianLocalRing A]
    {A' : Type w} [CommRing A'] (eA : A ≃+* A')
    {X : Scheme.{w}} (f : X ⟶ Spec (CommRingCat.of A'))
    [LocallyOfFiniteType f] [QuasiCompact f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (x : X)
    (aX : A →+* Γ(X, ⊤)) [Module A (F.presheaf.stalk x)] :
    letI : IsLocalRing A' := eA.isLocalRing
    letI := stalkModule F x
    f x = IsLocalRing.closedPoint A' →
      AlgebraicGeometry.IsFlatOverAt f.toLRSHom.toShHom F x →
        (∀ a : A, aX a = f.appTop ((Scheme.ΓSpecIso (CommRingCat.of A')).inv (eA a))) →
          (∀ (a : A) (m : F.presheaf.stalk x),
              a • m = (X.presheaf.germ ⊤ x trivial) (aX a) • m) →
            ∃ (I : Type w) (_ : SmallCategory I) (_ : IsFiltered I)
              (D : I ⥤ ModuleCat.{w} A) (c : Cocone D),
              (∀ i, Module.Free A (D.obj i)) ∧
              (∀ {i j : I} (g : i ⟶ j), Function.Injective
                (Submodule.mapQ
                  (maximalIdeal A • (⊤ : Submodule A (D.obj i)))
                  (maximalIdeal A • (⊤ : Submodule A (D.obj j)))
                  (D.map g).hom
                  (Submodule.smul_top_le_comap_smul_top (maximalIdeal A) (D.map g).hom))) ∧
              Nonempty (IsColimit c) ∧
              Nonempty (c.pt ≅ ModuleCat.of A (F.presheaf.stalk x)) := by
  let : IsLocalRing A' := eA.isLocalRing
  let := stalkModule F x
  intro hfx hflatAt haX hFx
  classical
  let : Algebra A A' := eA.toRingHom.toAlgebra
  let xA : Spec (CommRingCat.of A') := IsLocalRing.closedPoint A'
  -- Shrink the finite type model so that every associated point of the closed
  -- fiber in the chosen affine neighbourhood specializes to `x`.
  let G₀ := (Scheme.Modules.pullback (f.fiberι xA)).obj F
  have : G₀.IsQuasicoherent := AlgebraicGeometry.pullback_isQuasicoherent' (f.fiberι xA) F
  have hfiniteAssoc := associatedPoints_fiber_finite f F xA
  let badFiber : Set (f.fiber xA) :=
    {z | z ∈ Stacks.Divisors.associatedPoints G₀ ∧
      ¬ (f.fiberι xA z) ⤳ x}
  have hbadFiberFinite : badFiber.Finite := hfiniteAssoc.subset (by
    intro z hz
    exact hz.1)
  let badSource : Set X := f.fiberι xA '' badFiber
  have hbadSourceFinite : badSource.Finite := hbadFiberFinite.image _
  have hbadSource : ∀ y ∈ badSource, ¬ y ⤳ x := by
    rintro y ⟨z, hz, rfl⟩
    exact hz.2
  obtain ⟨Otop, hxO, hOavoid⟩ :=
    exists_open_mem_avoiding_finite_specializations x badSource hbadSourceFinite hbadSource
  let O : X.Opens := ⟨Otop, Otop.2⟩
  obtain ⟨X₁, hX₁aff, hxX₁, hX₁sub⟩ :=
    exists_isAffineOpen_mem_and_subset (U := O) (x := x) hxO
  let i₁ : X₁.toScheme ⟶ X := X₁.ι
  let f₁ : X₁.toScheme ⟶ Spec (.of A') := i₁ ≫ f
  let F₁ : X₁.toScheme.Modules := (Scheme.Modules.pullback i₁).obj F
  let x₁ : X₁.toScheme := ⟨x, hxX₁⟩
  have : IsAffine X₁.toScheme := hX₁aff
  have : F₁.IsQuasicoherent := AlgebraicGeometry.pullback_isQuasicoherent' i₁ F
  have : F₁.IsFiniteType :=
    @AlgebraicGeometry.SheafOfModules.pullback_isFiniteType
      X₁.toScheme.toRingedSpace X.toRingedSpace
      i₁.toLRSHom.toShHom F inferInstance
  have : LocallyOfFiniteType f₁ := by
    dsimp [f₁]
    infer_instance
  have hflatAt₁ : AlgebraicGeometry.IsFlatOverAt f₁.toLRSHom.toShHom F₁ x₁ := by
    have hflatI : AlgebraicGeometry.IsFlatAt i₁.toLRSHom.toShHom x₁ := by
      show (i₁.stalkMap x₁).hom.Flat
      exact (Flat.iff_flat_stalkMap i₁).mp inferInstance x₁
    exact (AlgebraicGeometry.isFlatOverAt_iff_modulePullback_isFlatOverAt
      i₁ f F x₁ hflatI).1 hflatAt
  have : IsLocallyNoetherian (f.fiber xA) :=
    AlgebraicGeometry.isLocallyNoetherian_fiber_of_locallyOfFiniteType f xA
  have : IsLocallyNoetherian (f₁.fiber xA) :=
    AlgebraicGeometry.isLocallyNoetherian_fiber_of_locallyOfFiniteType f₁ xA
  have : IsOpenImmersion i₁ := inferInstance
  let G₁s := (Scheme.Modules.pullback (f₁.fiberι xA)).obj F₁
  have hAssoc₁s : Stacks.Divisors.associatedPoints G₁s ⊆
      {z | (fiberMapOfSourceHom i₁ f xA z) ∈
        Stacks.Divisors.associatedPoints G₀} := by
    intro z hz
    let m := fiberMapOfSourceHom i₁ f xA
    let e := fiberModuleIso i₁ f F xA
    have : Etale m := MorphismProperty.of_isPullback
      (fiberMapOfSourceHom_isPullback i₁ f xA).flip inferInstance
    have hz' : z ∈ Stacks.Divisors.associatedPoints
        ((Scheme.Modules.pullback m).obj G₀) :=
      (associatedPoints_eq_of_iso e).symm ▸ hz
    exact (associatedPoints_pullback_iff_of_etale m G₀ z).mp hz'
  have hx₁base : f₁ x₁ = xA := by
    show f (i₁ x₁) = xA
    exact hfx
  have hgenFiber₁ (z : f₁.fiber xA)
      (hz : z ∈ Stacks.Divisors.associatedPoints G₁s) :
      (f₁.fiberι xA z) ⤳ x₁ := by
    let m := fiberMapOfSourceHom i₁ f xA
    have hmAssoc : m z ∈ Stacks.Divisors.associatedPoints G₀ := hAssoc₁s hz
    have hmPoint : f.fiberι xA (m z) = i₁ (f₁.fiberι xA z) := by
      have h := congrArg (fun k : f₁.fiber xA ⟶ X => k z)
        (fiberMapOfSourceHom_fiberι i₁ f xA)
      simpa [Scheme.Hom.comp_apply] using h
    have hInO : f.fiberι xA (m z) ∈ O := by
      rw [hmPoint]
      exact hX₁sub (f₁.fiberι xA z).property
    have hspec₀ : (f.fiberι xA (m z)) ⤳ x := by
      by_contra hspec
      have hbad : m z ∈ badFiber := ⟨hmAssoc, hspec⟩
      have hnotO := hOavoid (f.fiberι xA (m z)) ⟨m z, hbad, rfl⟩
      exact hnotO hInO
    have hspecMap : i₁ (f₁.fiberι xA z) ⤳ i₁ x₁ := by
      rw [← hmPoint]
      exact hspec₀
    exact i₁.isOpenEmbedding.isInducing.specializes_iff.mp hspecMap
  obtain ⟨Ue, hUe, hUaff, x', W, hx'f, hx'n, hWaff, hxW, hfree⟩ :=
    AlgebraicGeometry.exists_elementaryEtaleNeighborhood_free_sections_of_finiteType f₁ F₁ x₁
      hflatAt₁
  let a := Ue.scheme.fromSpecStalk Ue.point ≫ Ue.toBase
  let P := pullback f₁ a
  let Z := Spec Γ(P, W)
  let p : Z ⟶ P := hWaff.fromSpec
  let xZ : Z := hWaff.primeIdealOf ⟨x', hxW⟩
  have hpx : p xZ = x' := hWaff.fromSpec_primeIdealOf ⟨x', hxW⟩
  let q := pullback.snd f₁ a
  let g := pullback.fst f₁ a
  have hqclosed : q x' = closedPoint (Ue.scheme.presheaf.stalk Ue.point) := by
    apply (Ue.scheme.fromSpecStalk Ue.point).isEmbedding.injective
    simpa [a, q] using hx'n
  have hpgx : (p ≫ g) xZ = x₁ := (congrArg g hpx).trans hx'f
  have hpEtale : Etale p := by
    dsimp [p]
    infer_instance
  have : IsAffine Z := inferInstance
  have hqclosed' : (p ≫ q) xZ = closedPoint
      (Ue.scheme.presheaf.stalk Ue.point) := (congrArg q hpx).trans hqclosed
  let M := (Scheme.Modules.pullback g).obj F₁
  let φ : CommRingCat.of (Ue.scheme.presheaf.stalk Ue.point) ⟶ Γ(P, W) :=
    (Scheme.ΓSpecIso (.of (Ue.scheme.presheaf.stalk Ue.point))).inv ≫
      q.appLE ⊤ W (by simp)
  let hW : p ''ᵁ ⊤ = W := by
    rw [Scheme.Hom.image_top_eq_opensRange]
    exact hWaff.opensRange_fromSpec
  let φ' : CommRingCat.of (Ue.scheme.presheaf.stalk Ue.point) ⟶ Γ(P, p ''ᵁ ⊤) :=
    φ ≫ P.presheaf.map (eqToHom hW).op
  let ψ : CommRingCat.of (Ue.scheme.presheaf.stalk Ue.point) ⟶ Γ(Z, ⊤) :=
    (Scheme.ΓSpecIso (.of (Ue.scheme.presheaf.stalk Ue.point))).inv ≫
      (p ≫ q).appTop
  let : Module (Ue.scheme.presheaf.stalk Ue.point) Γ(M, W) := Module.compHom _ φ.hom
  let : Module (Ue.scheme.presheaf.stalk Ue.point)
      Γ(M, p ''ᵁ ⊤) := Module.compHom _ φ'.hom
  let : Module (Ue.scheme.presheaf.stalk Ue.point)
      Γ((Scheme.Modules.pullback (p ≫ g)).obj F₁, ⊤) := Module.compHom _ ψ.hom
  let : Module (Ue.scheme.presheaf.stalk Ue.point) Γ(M.restrict p, ⊤) :=
    Module.compHom _ ψ.hom
  have hfreeW : Module.Free (Ue.scheme.presheaf.stalk Ue.point) Γ(M, W) := by
    dsimp [M, g] at hfree ⊢
    exact hfree
  have hφ' : ∀ r, φ'.hom r = P.presheaf.map (eqToHom hW).op (φ.hom r) := by
    intro r
    rfl
  have hfreeImg : Module.Free (Ue.scheme.presheaf.stalk Ue.point)
      Γ(M, p ''ᵁ ⊤) :=
    free_sections_of_opens_eq (CommRingCat.of (Ue.scheme.presheaf.stalk Ue.point))
      M (p ''ᵁ ⊤) W hW φ φ' hφ' hfreeW
  have hφ : ∀ r, (p.appIso ⊤).hom (φ'.hom r) = ψ.hom r := by
    intro r
    let s₀ := (q.appTop.hom
      (((Scheme.ΓSpecIso (.of (Ue.scheme.presheaf.stalk Ue.point))).inv).hom r))
    have hrestr : φ'.hom r =
        P.presheaf.map (homOfLE (le_top : p ''ᵁ ⊤ ≤ ⊤)).op s₀ := by
      let V := p ''ᵁ ⊤
      let e : V ≤ q ⁻¹ᵁ (⊤ : (Spec (Ue.scheme.presheaf.stalk Ue.point)).Opens) := by simp
      have h1 : q.appLE ⊤ W (by simp) ≫ P.presheaf.map (eqToHom hW).op =
          q.appLE ⊤ V e := by
        convert Scheme.Hom.appLE_map' (f := q) (U := ⊤) (V := V) (V' := W) e hW using 1
      have h2 : q.appTop ≫
          P.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op = q.appLE ⊤ V e := by
        rfl
      have hmap : q.appLE ⊤ W (by simp) ≫ P.presheaf.map (eqToHom hW).op =
          q.appTop ≫ P.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op := by
        rw [h1, ← h2]
      have hmap := congrArg (fun k => k
        (((Scheme.ΓSpecIso (.of (Ue.scheme.presheaf.stalk Ue.point))).inv).hom r)) hmap
      exact hmap
    calc
      (p.appIso ⊤).hom (φ'.hom r) =
          (p.appIso ⊤).hom
            (P.presheaf.map (homOfLE (le_top : p ''ᵁ ⊤ ≤ ⊤)).op s₀) := by rw [hrestr]
      _ = p.appTop.hom s₀ := (open_appTop_eq_restrict p s₀).symm
      _ = ψ.hom r := by rfl
  have hfreeRestr := free_sections_of_open_restriction
    (CommRingCat.of (Ue.scheme.presheaf.stalk Ue.point)) p M φ' ψ hφ hfreeImg
  have : Module.Free (Ue.scheme.presheaf.stalk Ue.point) Γ(M.restrict p, ⊤) :=
    hfreeRestr
  let e := ((Scheme.Modules.pullbackComp p g).app F₁).symm ≪≫
    ((Scheme.Modules.restrictFunctorIsoPullback p).app M).symm
  let E : Γ((Scheme.Modules.pullback (p ≫ g)).obj F₁, ⊤) ≃ₗ[
      Ue.scheme.presheaf.stalk Ue.point] Γ(M.restrict p, ⊤) :=
    { Equiv.ofBijective (fun z => (e.hom.app ⊤) z)
        (ConcreteCategory.bijective_of_isIso (e.hom.app ⊤)) with
      map_add' := fun z₁ z₂ => map_add (ConcreteCategory.hom (e.hom.app ⊤)) z₁ z₂
      map_smul' := fun r z => Scheme.Modules.Hom.app_smul e.hom (ψ.hom r) z }
  have hfreePullback : Module.Free (Ue.scheme.presheaf.stalk Ue.point)
      Γ((Scheme.Modules.pullback (p ≫ g)).obj F₁, ⊤) :=
    Module.Free.of_equiv E.symm
  let R := Ue.scheme.presheaf.stalk Ue.point
  have : HenselianLocalRing A' := HenselianLocalRing.of_ringEquiv eA
  have hbase : Ue.toBase Ue.point = closedPoint A' :=
    Ue.map_point.trans hx₁base
  have : HenselianLocalRing
      ((Spec (.of A')).presheaf.stalk (Ue.toBase Ue.point)) := by
    rw [hbase]
    exact HenselianLocalRing.of_ringEquiv
      (stalkClosedPointIso (.of A')).symm.commRingCatIsoToRingEquiv
  have : IsIso ((Spec (.of A')).fromSpecStalk (Ue.toBase Ue.point)) := by
    rw [hbase, ← Spec_stalkClosedPointIso]
    infer_instance
  have : IsIso (Ue.toBase.residueFieldMap Ue.point) := by
    have hres := hUe
    change IsIso (((Spec (.of A')).residueFieldCongr Ue.map_point).inv ≫
      Ue.toBase.residueFieldMap Ue.point) at hres
    exact (isIso_comp_left_iff _ _).mp hres
  have : IsIso a := isIso_fromSpecStalk_comp_of_henselian Ue.toBase Ue.point
  let α : CommRingCat.of A' ⟶ R :=
    (Scheme.ΓSpecIso (.of A')).inv ≫ a.appTop ≫ (Scheme.ΓSpecIso R).hom
  have : IsIso a.appTop := by
    show IsIso (a.app ⊤)
    infer_instance
  have : IsIso α := by dsimp [α]; infer_instance
  let : Algebra A' R := α.hom.toAlgebra
  let eRA : R ≃ₐ[A'] A' :=
    (AlgEquiv.ofBijective (Algebra.ofId A' R)
      (ConcreteCategory.bijective_of_isIso α)).symm
  let S := Γ((Scheme.Modules.pullback (p ≫ g)).obj F₁, ⊤)
  let : Module A' S := Module.compHom S (algebraMap A' R)
  let : IsScalarTower A' R S := IsScalarTower.of_compHom A' R S
  have : Module.Free R S := hfreePullback
  have hfreeA' : Module.Free A' S := free_of_henselian_scalar_equiv eRA
  have : IsIso g := by dsimp [g]; infer_instance
  let j := p ≫ g
  have : IsOpenImmersion j := by dsimp [j]; infer_instance
  let H := (Scheme.Modules.pullback j).obj F₁
  have : H.IsQuasicoherent := AlgebraicGeometry.pullback_isQuasicoherent' j F₁
  let fZ := j ≫ f₁
  have hbaseZ : fZ xZ = xA := by
    show f₁ (j xZ) = xA
    rw [show j xZ = x₁ from hpgx]
    exact hx₁base
  let Hs := (Scheme.Modules.pullback (fZ.fiberι xA)).obj H
  have : Hs.IsQuasicoherent := AlgebraicGeometry.pullback_isQuasicoherent' (fZ.fiberι xA) H
  have : LocallyOfFiniteType fZ := by dsimp [fZ]; infer_instance
  have : IsLocallyNoetherian (fZ.fiber xA) :=
    AlgebraicGeometry.isLocallyNoetherian_fiber_of_locallyOfFiniteType fZ xA
  have hgenZ : ∀ y ∈ Stacks.Divisors.associatedPoints Hs, (fZ.fiberι xA y) ⤳ xZ :=
    associatedPoints_fiber_specialize_of_openImmersion j f₁ F₁ xA xZ
      (fun y hy => by simpa only [show j xZ = x₁ from hpgx] using hgenFiber₁ y hy)
  have hsmulZ (r : Γ(Z, ⊤))
      (hr : IsUnit (Z.presheaf.germ ⊤ xZ trivial r)) :
      Function.Injective (fun m : Γ(Hs, ⊤) => (fZ.fiberι xA).appTop r • m) :=
    fiber_sections_smul_injective fZ xA Hs xZ hbaseZ hgenZ r hr
  have hZ : IsAffineOpen (⊤ : Z.Opens) := isAffineOpen_top Z
  let PZ := (hZ.primeIdealOf ⟨xZ, by simp⟩).asIdeal
  let := affineStalkModule H ⊤ xZ trivial
  have hlocH : IsLocalizedModule PZ.primeCompl
      (affineGerm H ⊤ xZ (show xZ ∈ (⊤ : Z.Opens) from trivial)) :=
    affineGerm_isLocalized H ⊤ hZ xZ trivial
  have hbaseComp : (p ≫ q) ≫ a = fZ := by
    dsimp [fZ, j, q, g]
    rw [Category.assoc, ← pullback.condition, ← Category.assoc]
  have hscalar : α ≫ ψ = (Scheme.ΓSpecIso (.of A')).inv ≫ fZ.appTop := by
    show (Scheme.ΓSpecIso (.of A')).inv ≫ a.appTop ≫
        (Scheme.ΓSpecIso R).hom ≫ (Scheme.ΓSpecIso R).inv ≫ (p ≫ q).appTop = _
    rw [Iso.hom_inv_id_assoc, ← Scheme.Hom.comp_appTop, hbaseComp]
  let : Algebra A' Γ(Z, ⊤) := (α ≫ ψ).hom.toAlgebra
  let : IsScalarTower A' Γ(Z, ⊤) S := IsScalarTower.of_compHom A' Γ(Z, ⊤) S
  let instModAS : Module A S := Module.compHom S eA.toRingHom
  let hstAA'S : IsScalarTower A A' S := IsScalarTower.of_compHom A A' S
  have : Module.Free A' S := hfreeA'
  let eAA : A' ≃ₐ[A] A :=
    { eA.symm with commutes' := fun a => eA.symm_apply_apply a }
  have hfreeA : Module.Free A S :=
    @free_of_henselian_scalar_equiv A A' _ _ _ _ _ instModAS _ hstAA'S eAA hfreeA'
  let : Algebra A Γ(Z, ⊤) := ((α ≫ ψ).hom.comp eA.toRingHom).toAlgebra
  let : IsScalarTower A Γ(Z, ⊤) S := IsScalarTower.of_compHom A Γ(Z, ⊤) S
  let : Module A (H.presheaf.stalk xZ) :=
    Module.compHom _ (algebraMap A Γ(Z, ⊤))
  let : IsScalarTower A Γ(Z, ⊤) (H.presheaf.stalk xZ) :=
    IsScalarTower.of_compHom A Γ(Z, ⊤) (H.presheaf.stalk xZ)
  let k := j ≫ i₁
  have : IsOpenImmersion k := by dsimp [k]; infer_instance
  have hkx : k xZ = x := by
    show i₁ (j xZ) = x
    rw [show j xZ = x₁ from hpgx]
    rfl
  let eH : H ≅ F.restrict k :=
    (Scheme.Modules.pullbackComp j i₁).app F ≪≫
      ((Scheme.Modules.restrictFunctorIsoPullback k).app F).symm
  suffices h : (∀ r : PZ.primeCompl, Function.Injective
      (Submodule.mapQ (maximalIdeal A' • (⊤ : Submodule A' S))
        (maximalIdeal A' • (⊤ : Submodule A' S))
        (localizedScalarMapOver (A := A') (R := Γ(Z, ⊤)) (M := S) r)
        (Submodule.smul_top_le_comap_smul_top (maximalIdeal A')
          (localizedScalarMapOver (A := A') (R := Γ(Z, ⊤)) (M := S) r)))) ∧
      Nonempty (H.presheaf.stalk xZ ≃ₗ[A] F.presheaf.stalk x) by
    obtain ⟨hred, ⟨eN⟩⟩ := h
    have : IsLocalHom (algebraMap A A') := by
      show IsLocalHom eA.toRingHom
      exact isLocalHom_of_leftInverse eA.symm eA.left_inv
    have : IsLocalizedModule PZ.primeCompl
        (affineGerm H ⊤ xZ (show xZ ∈ (⊤ : Z.Opens) from trivial)) := hlocH
    obtain ⟨I, hI, hIf, D, c, hD, hredD, hc, ⟨ec⟩⟩ :=
      exists_filteredColimit_of_isLocalizedModule (A := A)
        PZ.primeCompl (affineGerm H ⊤ xZ (show xZ ∈ (⊤ : Z.Opens) from trivial)) hfreeA
        (fun r => @injective_mapQ_restrictScalars_of_surjective A A' _ _ _ _ _ _ _ _
          instModAS _ hstAA'S eA.surjective
          (localizedScalarMapOver (A := A') (R := Γ(Z, ⊤)) (M := S) r) (hred r))
    exact ⟨I, hI, hIf, D, c, hD, hredD, hc, ⟨ec ≪≫ eN.toModuleIso⟩⟩
  have hHx : ∀ (a : A) (m : H.presheaf.stalk xZ),
      a • m = (Z.presheaf.germ ⊤ xZ trivial) (algebraMap A Γ(Z, ⊤) a) • m := fun _ _ => rfl
  constructor
  · intro r
    apply mapQ_injective_of_preimage
    intro m hm
    have hr : IsUnit ((Z.presheaf.germ ⊤ xZ trivial) (r : Γ(Z, ⊤))) := by
      let : Algebra Γ(Z, ⊤) (Z.presheaf.stalk xZ) :=
        (Z.presheaf.germ ⊤ xZ trivial).hom.toAlgebra
      let : IsLocalization.AtPrime (Z.presheaf.stalk xZ) PZ :=
        hZ.isLocalization_stalk ⟨xZ, by simp⟩
      exact (IsLocalization.AtPrime.isUnit_to_map_iff _ PZ r).mpr r.property
    have hmod : (inferInstance : Module A' S) =
        Module.compHom S (((Scheme.ΓSpecIso (.of A')).inv ≫ fZ.appTop).hom) := by
      apply Module.ext'
      intro a₀ m₀
      show ψ (α a₀) • m₀ =
        ((Scheme.ΓSpecIso (.of A')).inv ≫ fZ.appTop) a₀ • m₀
      rw [← hscalar]
      rfl
    have hred := reduction_injective_of_fiber_smul_injective fZ H r (hsmulZ r hr)
    show m ∈ maximalIdeal A' • (⊤ : Submodule A' S)
    change (r : Γ(Z, ⊤)) • m ∈ maximalIdeal A' • (⊤ : Submodule A' S) at hm
    have hmem (z : S) := mem_ideal_smul_top_congr _ _ hmod (maximalIdeal A') z
    exact (hmem m).mpr (hred m ((hmem ((r : Γ(Z, ⊤)) • m)).mp hm))
  · let := stalkModule H xZ
    have hscalarK (a₀ : A) : algebraMap A Γ(Z, ⊤) a₀ = k.appTop (aX a₀) := by
      show (α ≫ ψ) (eA a₀) = _
      rw [hscalar, haX a₀]
      have hcomp : k ≫ f = fZ := by dsimp [k, fZ, j, f₁]; simp only [Category.assoc]
      rw [← hcomp, Scheme.Hom.comp_appTop]
      rfl
    exact ⟨LinearEquiv.ofBijective
      { toFun := (restrictStalkIso k F H eH xZ x hkx).hom
        map_add' := (restrictStalkIso k F H eH xZ x hkx).hom.hom.map_add
        map_smul' := fun a₀ m => by
          show (restrictStalkIso k F H eH xZ x hkx).hom (a₀ • m) =
            a₀ • (restrictStalkIso k F H eH xZ x hkx).hom m
          rw [hHx a₀ m, hFx a₀ ((restrictStalkIso k F H eH xZ x hkx).hom m), hscalarK a₀]
          exact stalkIso_restrict_smul k F H eH xZ x hkx (aX a₀) m }
      (ConcreteCategory.bijective_of_isIso (restrictStalkIso k F H eH xZ x hkx).hom)⟩

/-- **Conclusion (1) of Stacks 05U7 from an affine model of the pair.** The model is a ring `A'`
isomorphic to the henselian local ring `A` but living in the universe of the module, a finite
type `A'`-algebra `C'`, a finite `C'`-module `M₀'` whose localization at a prime `Q'` is a copy
`N'` of `N`, flat over `A'`, and the fact that `Q'` lies over the closed point. The conclusion is
the filtered-colimit presentation of `N`.

The geometry runs here, where `C'` and `M₀'` are variables. In the main theorem they are a
`ULift` of a `Shrink` of a subalgebra, and every unification against them unfolds that tower;
separating the two halves is what holds each inside the default elaboration budget. -/
private theorem exists_filteredColimit_free_of_affineModel
    {A : Type u} {N : Type uM} [CommRing A] [HenselianLocalRing A]
    [AddCommGroup N] [Module A N]
    {A' C' M₀' N' : Type (max u uM)}
    [CommRing A'] [IsLocalRing A'] [CommRing C'] [Algebra A' C'] [Algebra.FiniteType A' C']
    [AddCommGroup M₀'] [Module C' M₀'] [Module.Finite C' M₀']
    [AddCommGroup N'] [Module C' N'] [Module A' N'] [IsScalarTower A' C' N']
    [Module.Flat A' N']
    [Module A N']
    (eA : A ≃+* A') (hAN : ∀ (a : A) (n : N'), (eA a) • n = a • n)
    (Q' : Ideal C') [Q'.IsPrime]
    (fQ' : M₀' →ₗ[C'] N') [IsLocalizedModule Q'.primeCompl fQ']
    (eNN : N' ≃ₗ[A] ULift.{u} N)
    (hfx : (Spec.map (CommRingCat.ofHom (algebraMap A' C'))) (PrimeSpectrum.mk Q' inferInstance) =
      (PrimeSpectrum.mk (maximalIdeal A') inferInstance : Spec (.of A'))) :
    ∃ (I : Type (max u uM)) (_ : SmallCategory I) (_ : IsFiltered I)
      (F : I ⥤ ModuleCat.{max u uM} A) (c : Cocone F),
      (∀ i, Module.Free A (F.obj i)) ∧
      (∀ {i j : I} (f : i ⟶ j), Function.Injective
        (Submodule.mapQ
          (maximalIdeal A • (⊤ : Submodule A (F.obj i)))
          (maximalIdeal A • (⊤ : Submodule A (F.obj j)))
          (F.map f).hom
          (Submodule.smul_top_le_comap_smul_top (maximalIdeal A)
            (F.map f).hom))) ∧
      Nonempty (IsColimit c) ∧
      Nonempty (c.pt ≅ ModuleCat.of A (ULift.{u} N)) := by
  classical
  let : Algebra A A' := eA.toRingHom.toAlgebra
  let : Algebra A C' := ((algebraMap A' C').comp eA.toRingHom).toAlgebra
  have : HenselianLocalRing A' := HenselianLocalRing.of_ringEquiv eA
  let X : Scheme.{max u uM} := Spec (CommRingCat.of C')
  let F : X.Modules := AlgebraicGeometry.tilde (R := .of C') (ModuleCat.of C' M₀')
  have : F.IsQuasicoherent := inferInstance
  have : F.IsFiniteType :=
    (AlgebraicGeometry.tilde_isFiniteType_iff (R := CommRingCat.of C')
      (ModuleCat.of C' M₀')).mpr inferInstance
  let f : X ⟶ Spec (.of A') :=
    Spec.map (CommRingCat.ofHom (algebraMap A' C'))
  have : LocallyOfFiniteType f := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr ‹Algebra.FiniteType A' C'›
  let x : X := PrimeSpectrum.mk Q' inferInstance
  let xA : Spec (.of A') := PrimeSpectrum.mk (maximalIdeal A') inferInstance
  have hflatAt : AlgebraicGeometry.IsFlatOverAt f.toLRSHom.toShHom F x :=
    @isFlatOverAt_tilde_of_isLocalizedModule A' C' _ _ _ M₀' N' _ _ _ _
      inferInstance inferInstance x fQ' inferInstance inferInstance
  let aX : A →+* Γ(X, ⊤) :=
    ((Scheme.ΓSpecIso (.of A')).inv ≫ f.appTop).hom.comp eA.toRingHom
  let := stalkModule F x
  let instFx : Module A (F.presheaf.stalk x) :=
    Module.compHom _ ((X.presheaf.germ ⊤ x trivial).hom.comp aX)
  let instC'stalk : Module C' (F.presheaf.stalk x) :=
    tilde.instModuleCarrierCarrierStalkAbPresheaf (R := .of C') (ModuleCat.of C' M₀') x
  have hFgerm : ∀ (r : C') (m : F.presheaf.stalk x),
      ((X.presheaf.germ ⊤ x trivial) ((Scheme.ΓSpecIso (.of C')).inv r)) • m = r • m :=
    fun _ _ => rfl
  have hnat : ∀ a : A, (Scheme.ΓSpecIso (.of C')).inv (algebraMap A C' a) = aX a := by
    intro a
    exact congrArg (fun t : CommRingCat.of A' ⟶ Γ(X, ⊤) => t (eA a))
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap A' C')))
  let hstAC'stalk : IsScalarTower A C' (F.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_smul fun a m => by
      rw [← hFgerm (algebraMap A C' a) m, hnat a]
      rfl
  have hstAC'N' : IsScalarTower A C' N' :=
    IsScalarTower.of_algebraMap_smul fun a n =>
      (IsScalarTower.algebraMap_smul (R := A') (A := C') (eA a) n).trans (hAN a n)
  let ELC' : (F.presheaf.stalk x) ≃ₗ[C'] N' :=
    (tilde_stalk_equiv_localized x).trans (IsLocalizedModule.iso Q'.primeCompl fQ')
  let EL := restrictScalarsOfTowers hstAC'stalk hstAC'N' ELC'
  obtain ⟨I, hI, hIf, D, c, hD, hredD, hc, ⟨ec⟩⟩ :=
    exists_filteredColimit_free_of_isFlatOverAt eA f F x aX hfx hflatAt (fun _ => rfl)
      (fun _ _ => rfl)
  exact ⟨I, hI, hIf, D, c, hD, hredD, hc,
    ⟨ec ≪≫ (EL.trans eNN).toModuleIso⟩⟩

/-- Let `A` be a henselian local ring, `A → B` a local homomorphism of local rings with `B`
essentially of finite type over `A`, and `N` a finite `B`-module which is flat over `A`. Then `N`
is a filtered colimit of free `A`-modules `F i` such that every transition map `F i → F j` induces
an injective map `F i / 𝔪_A F i → F j / 𝔪_A F j`. -/
@[stacks 05U7 "filtered-colimit presentation"]
public theorem exists_filteredColimit_free_with_injective_reduction
    {A : Type u} {B : Type v} {N : Type uM} [CommRing A] [CommRing B]
    [IsLocalRing B] [HenselianLocalRing A]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    (hB : Algebra.EssFiniteType A B)
    [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
    [Module.Finite B N] [Module.Flat A N] :
    ∃ (I : Type (max u uM)) (_ : SmallCategory I) (_ : IsFiltered I)
      (F : I ⥤ ModuleCat.{max u uM} A) (c : Cocone F),
      (∀ i, Module.Free A (F.obj i)) ∧
      (∀ {i j : I} (f : i ⟶ j), Function.Injective
        (Submodule.mapQ
          (maximalIdeal A • (⊤ : Submodule A (F.obj i)))
          (maximalIdeal A • (⊤ : Submodule A (F.obj j)))
          (F.map f).hom
          (Submodule.smul_top_le_comap_smul_top (maximalIdeal A)
            (F.map f).hom))) ∧
      Nonempty (IsColimit c) ∧
      Nonempty (c.pt ≅ ModuleCat.of A (ULift.{u} N)) := by
  classical
  let : Algebra.EssFiniteType A B := hB
  let C := Algebra.EssFiniteType.subalgebra A B
  let instAlgCB : Algebra C B := inferInstance
  have hst : IsScalarTower C B N := inferInstance
  obtain ⟨M₀, hM₀, hspan⟩ := @exists_finite_submodule_spanning_module C B N
    _ _ _ _ _ _ hst _
  have : Module.Finite C M₀ := hM₀
  have hlocM₀ : IsLocalizedModule (Algebra.EssFiniteType.submonoid A B)
      (M₀.subtype : M₀ →ₗ[C] N) :=
    @localized_submodule_of_spanning C B N _ _ (Algebra.EssFiniteType.submonoid A B)
      _ _ _ _ _ hst M₀ hspan
  let Q : Ideal C := (maximalIdeal B).comap (algebraMap C B)
  have : Q.IsPrime := Ideal.IsPrime.comap (algebraMap C B)
  have hT : Algebra.EssFiniteType.submonoid A B ≤ Q.primeCompl := by
    intro t ht
    show algebraMap C B (t : C) ∉ maximalIdeal B
    exact (IsLocalRing.notMem_maximalIdeal).mpr ht
  have hunitQ (r : Q.primeCompl) :
      Function.Bijective (fun m : N => (r : C) • m) := by
    have hnot : algebraMap C B (r : C) ∉ maximalIdeal B := by
      intro hr
      exact r.2 (Ideal.mem_comap.mpr hr)
    have hu : IsUnit (algebraMap C B (r : C)) :=
      IsLocalRing.notMem_maximalIdeal.mp hnot
    exact @bijective_smul_of_isUnit_algebraMap C B N _ _ _ _ _ _ hst (r : C) hu
  have hlocQ : IsLocalizedModule Q.primeCompl (M₀.subtype : M₀ →ₗ[C] N) :=
    localizedModule_of_localUnits Q (M₀.subtype : M₀ →ₗ[C] N) hT hunitQ
  have hstAC : IsScalarTower A C N := inferInstance
  have : IsScalarTower A C N := hstAC
  have : Small.{u} C := inferInstance
  have : Algebra.FiniteType A C := inferInstance
  clear hlocM₀ hT hunitQ hspan hM₀
  clear_value C
  have : Small.{max u uM} C :=
    ⟨⟨ULift.{uM} (Shrink.{u} C), ⟨(equivShrink C).trans Equiv.ulift.symm⟩⟩⟩
  let eC : Shrink.{max u uM} C ≃ₐ[A] C := Shrink.algEquiv A C
  let C' := Shrink.{max u uM} C
  let : CommRing C' := inferInstance
  let : Algebra A C' := inferInstance
  let : Module C' M₀ := Module.compHom _ eC.toRingHom
  have hM₀' : Module.Finite C' M₀ := by
    let f : M₀ →ₛₗ[eC.symm.toRingHom] M₀ :=
      { toFun := id
        map_add' := fun _ _ => rfl
        map_smul' := fun r m => by
          show r • m = eC (eC.symm r) • m
          rw [eC.apply_symm_apply] }
    exact Module.Finite.of_surjective f Function.surjective_id
  let : Module.Finite C' M₀ := hM₀'
  let M₀' := ULift.{max u uM} M₀
  let instC'M₀' : Module C' M₀' := ULift.module'
  let : MulAction C' M₀' := instC'M₀'.toMulAction
  have hM₀'' : Module.Finite C' M₀' :=
    Module.Finite.equiv (ULift.moduleEquiv (R := C') (M := M₀)).symm
  let : Module.Finite C' M₀' := hM₀''
  let A' := ULift.{max u uM} A
  let : CommRing A' := inferInstance
  let eA : A ≃+* A' := ULift.ringEquiv.symm
  let : IsLocalRing A' := eA.isLocalRing
  let : Algebra A A' := eA.toRingHom.toAlgebra
  let : Algebra A' C' := Algebra.compHom C' eA.symm.toRingHom
  have hstAA'C' : IsScalarTower A A' C' := IsScalarTower.of_algebraMap_eq fun a => by
    show algebraMap A C' a = algebraMap A C' (eA.symm (eA a))
    simp
  have hC'finiteType : Algebra.FiniteType A C' :=
    Algebra.FiniteType.of_surjective (eC.symm : C →ₐ[A] C') eC.symm.surjective
  let : Algebra.FiniteType A' C' :=
    @Algebra.FiniteType.of_restrictScalars_finiteType A A' C'
      (inferInstance : CommSemiring A) (inferInstance : CommSemiring A')
      (inferInstance : Semiring C') (inferInstance : Algebra A A')
      (inferInstance : Algebra A C') (inferInstance : Algebra A' C')
      hstAA'C' hC'finiteType
  let Q' : Ideal C' := Q.comap eC.toRingHom
  have : Q'.IsPrime := Ideal.IsPrime.comap eC.toRingHom
  have hmapCB (a : A') :
      algebraMap C B (eC (algebraMap A' C' a)) =
        algebraMap A B (eA.symm a) := by
    calc
      algebraMap C B (eC (algebraMap A' C' a)) =
          algebraMap C B (eC (algebraMap A C' (eA.symm a))) := by
            exact congrArg (fun z => algebraMap C B (eC z)) <| calc
              algebraMap A' C' a =
                  algebraMap A' C' (algebraMap A A' (eA.symm a)) := by
                    have ha : algebraMap A A' (eA.symm a) = a := by
                      show eA (eA.symm a) = a
                      exact eA.apply_symm_apply a
                    exact congrArg (algebraMap A' C') ha.symm
              _ = algebraMap A C' (eA.symm a) :=
                (hstAA'C'.algebraMap_apply A A' C' (eA.symm a)).symm
      _ = algebraMap C B (algebraMap A C (eA.symm a)) := by rw [eC.commutes]
      _ = algebraMap A B (eA.symm a) :=
        IsScalarTower.algebraMap_apply A C B (eA.symm a)
  have hfx : (Spec.map (CommRingCat.ofHom (algebraMap A' C'))) (PrimeSpectrum.mk Q' inferInstance) =
      (PrimeSpectrum.mk (maximalIdeal A') inferInstance : Spec (.of A')) := by
    apply PrimeSpectrum.ext
    ext a
    show algebraMap C B (eC (algebraMap A' C' a)) ∈ maximalIdeal B ↔
      a ∈ maximalIdeal A'
    rw [hmapCB]
    let g : A' →+* B := (algebraMap A B).comp eA.symm.toRingHom
    let : IsLocalHom eA.symm.toRingHom :=
      isLocalHom_of_leftInverse eA eA.right_inv
    have hlocal : IsLocalHom g := by
      show IsLocalHom ((algebraMap A B).comp eA.symm.toRingHom)
      exact RingHom.isLocalHom_comp _ _
    show g a ∈ maximalIdeal B ↔ a ∈ maximalIdeal A'
    rw [← Ideal.mem_comap]
    rw [IsLocalRing.maximalIdeal_comap g]
  let N' := ULift.{max u uM} N
  let : AddCommGroup N' := inferInstance
  let : Module B N' := inferInstance
  let : Algebra C' C := eC.toRingHom.toAlgebra
  let : Algebra C' B := Algebra.compHom B eC.toRingHom
  let : IsScalarTower C' C B := by
    apply IsScalarTower.of_algebraMap_eq
    intro c
    rfl
  let : Module C N' := Module.compHom N' (algebraMap C B)
  let : IsScalarTower C B N' := IsScalarTower.of_compHom C B N'
  let instC'N' : Module C' N' := Module.compHom N' (algebraMap C' C)
  let : IsScalarTower C' C N' := IsScalarTower.of_compHom C' C N'
  let hstC'BN' : IsScalarTower C' B N' := by
    apply IsScalarTower.of_algebraMap_smul
    intro c n
    show algebraMap C' B c • n =
      algebraMap C B (algebraMap C' C c) • n
    rfl
  let : Module A N' := inferInstance
  let instModA'N' : Module A' N' := Module.compHom N' eA.symm.toRingHom
  have hscalarA'C'N' (a : A') (n : N') :
      algebraMap A' C' a • n = a • n := by
    calc
      algebraMap A' C' a • n =
          algebraMap C' B (algebraMap A' C' a) • n :=
        (IsScalarTower.algebraMap_smul (R := C') (A := B)
          (algebraMap A' C' a) n).symm
      _ = algebraMap C B (eC (algebraMap A' C' a)) • n :=
        congrArg (fun r : B => r • n)
          (rfl : algebraMap C' B (algebraMap A' C' a) =
            algebraMap C B (eC (algebraMap A' C' a)))
      _ = algebraMap A B (eA.symm a) • n := congrArg (fun r : B => r • n) (hmapCB a)
      _ = eA.symm a • n :=
        IsScalarTower.algebraMap_smul (R := A) (A := B) (eA.symm a) n
  let hstA'C'N' : IsScalarTower A' C' N' :=
    IsScalarTower.of_algebraMap_smul hscalarA'C'N'
  have hflatN' : Module.Flat A' N' := by
    have hflatN : Module.Flat A N' := Module.Flat.of_linearEquiv
      (ULift.moduleEquiv : N' ≃ₗ[A] N)
    apply flat_of_ringEquiv eA
    intro a n
    rfl
  let : Module C' N := Module.compHom N (algebraMap C' C)
  let : IsScalarTower C' C N := IsScalarTower.of_compHom C' C N
  let eM : M₀' ≃ₗ[C'] M₀ := ULift.moduleEquiv
  let eN : N' ≃ₗ[C'] N := ULift.moduleEquiv
  let fN : M₀ →ₗ[C'] N := {
    toFun := fun m => m
    map_add' := fun _ _ => rfl
    map_smul' := by intro r m; rfl }
  let fQ' : M₀' →ₗ[C'] N' :=
    eN.symm.toLinearMap.comp (fN.comp eM.toLinearMap)
  have hunitQ' (r : Q'.primeCompl) :
      Function.Bijective (fun m : N' => (r : C') • m) := by
    have hrC : eC (r : C') ∉ Q := by
      intro h
      exact r.2 (Ideal.mem_comap.mpr h)
    have hrB : algebraMap C B (eC (r : C')) ∉ maximalIdeal B := by
      intro h
      exact hrC (Ideal.mem_comap.mpr h)
    have huB : IsUnit (algebraMap C B (eC (r : C'))) :=
      IsLocalRing.notMem_maximalIdeal.mp hrB
    have hrC'B : IsUnit (algebraMap C' B (r : C')) := huB
    exact @bijective_smul_of_isUnit_algebraMap C' B N' _ _ _ _ _ _ hstC'BN'
      (r : C') hrC'B
  have : IsScalarTower A' C' N' := hstA'C'N'
  have symm_mem_primeCompl (s : Q.primeCompl) : eC.symm (s : C) ∈ Q'.primeCompl := by
    show eC (eC.symm s) ∉ Q
    rw [eC.apply_symm_apply]
    exact s.2
  have hlocQ' : IsLocalizedModule Q'.primeCompl fQ' := by
    classical
    refine isLocalizedModule_of_bijective_smul _ _ hunitQ' ?_ ?_
    · intro n'
      obtain ⟨⟨m, s⟩, hs⟩ := IsLocalizedModule.surj Q.primeCompl
        (M₀.subtype : M₀ →ₗ[C] N) (eN n')
      let s' : C' := eC.symm s
      have hs' : s' ∈ Q'.primeCompl := symm_mem_primeCompl s
      refine ⟨⟨eM.symm m, ⟨s', hs'⟩⟩, ?_⟩
      apply eN.injective
      show eC s' • eN n' = fN m
      have hcoe : eC s' = (s : C) := eC.apply_symm_apply s
      rw [hcoe]
      show (s : C) • eN n' = (m : N)
      exact hs
    · intro x y hxy
      have hxy' : (M₀.subtype : M₀ →ₗ[C] N) (eM x) =
          (M₀.subtype : M₀ →ₗ[C] N) (eM y) := by
        have h := congrArg eN hxy
        have e1 : ∀ z : M₀', eN (fQ' z) = (M₀.subtype : M₀ →ₗ[C] N) (eM z) :=
          fun z => eN.apply_symm_apply (fN (eM z))
        exact (e1 x).symm.trans (h.trans (e1 y))
      obtain ⟨s, hs⟩ := hlocQ.exists_of_eq hxy'
      let s' : C' := eC.symm s
      have hs' : s' ∈ Q'.primeCompl := symm_mem_primeCompl s
      refine ⟨⟨s', hs'⟩, ?_⟩
      apply eM.injective
      show eC s' • eM x = eC s' • eM y
      rw [show eC s' = s from eC.apply_symm_apply s]
      exact hs
  exact @exists_filteredColimit_free_of_affineModel A N _ _ _ _ A' C' M₀' N'
    _ _ _ _ _ _ _ _ _ instC'N' instModA'N' hstA'C'N' hflatN' _ eA
    (fun a n => congrArg (fun z : A => z • n) (eA.symm_apply_apply a)) Q' _ fQ' hlocQ'
    ((ULift.moduleEquiv : N' ≃ₗ[A] N).trans
      (ULift.moduleEquiv : ULift.{u} N ≃ₗ[A] N).symm) hfx

end
