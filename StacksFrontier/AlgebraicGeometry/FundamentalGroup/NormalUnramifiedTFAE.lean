module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Etale.Pi
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
public import Mathlib.RingTheory.Invariant.Galois
public import Mathlib.RingTheory.Localization.Away.Lemmas
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Unramified.Finite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSourceTopologies.Unramified
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.Unramified
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.RankDecomposition
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.SectionIdealSumCapture
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFreeOfRank
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.EtaleNormalization
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Properties
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.AlgebraicGeometry.Pullback.StalkFromSpecStalk
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.LocallyFreeSite
public import StacksFrontier.RingTheory.Etale.IntegralSplitting
public import StacksFrontier.RingTheory.GeometricallyNormal.TFAE
public import StacksFrontier.RingTheory.Henselian.Henselization.Defs
public import StacksFrontier.RingTheory.Henselian.HenselizationUniversalProperty
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.Existence
public import StacksFrontier.RingTheory.Invariant.Inertia
public import StacksFrontier.RingTheory.Module.LocallyFree.FiniteProjective
public import StacksFrontier.RingTheory.Module.LocallyFree.SheafBridge
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree

/-!
# Unramified finite extensions of the function field of a normal scheme

Let `X` be an integral normal scheme with function field `K`, let `L / K` be a finite extension
and let `Y → X` be the normalization of `X` in `L`. The morphism `Y → X` is unramified exactly
when it is étale, when it is finite étale, when it stays unramified after base change to the
local rings of `X`, to their henselizations or to their strict henselizations, and when every
scheme-theoretic fibre is étale of degree at least `[L : K]`. If `L / K` is Galois with group
`G`, this is moreover equivalent to triviality of the inertia group
`I_y = {g ∈ G | g(y) = y and g ≡ id mod m_y}` at every point `y` of `Y`.

## Main results

* `AlgebraicGeometry.normalization_unramified_tfae`: the equivalence of conditions (1)–(8).
* `AlgebraicGeometry.normalization_unramified_iff_trivialInertia`: condition (9), the Galois
  case.

## Implementation notes

"`X` is unramified in `L`" is by definition the statement that the normalization `Y → X` is
unramified, so condition (1) of the source is literally condition (2); the two are represented
by the same proposition in the list rather than duplicated.

The normalization is formed from the canonical morphism `i : Spec L ⟶ X` through the generic
point, which is an explicit argument together with its factorization through `X.fromSpecStalk`;
the quasi-compactness and quasi-separatedness that the relative normalization needs are instance
arguments.

Henselizations are tested on every ring satisfying `IsLocalRing.IsHenselization`, which makes
conditions (6) and (7) independent of the choice of representative. Inertia in condition (9) is
tested on the integral closure of the coordinate ring of each nonempty affine open; the action of
`Gal(L/K)` on that integral closure is `galRestrict`, preservation of the prime `q` is written
elementwise, and acting trivially on the residue field is written as `σ y - y ∈ q`.

## References

* [Stacks Project, Tag 0BTF](https://stacks.math.columbia.edu/tag/0BTF)
* [Stacks Project, Tag 0BQK](https://stacks.math.columbia.edu/tag/0BQK)
* [Stacks Project, Tag 0BSR](https://stacks.math.columbia.edu/tag/0BSR)
* [Stacks Project, Tag 06DI](https://stacks.math.columbia.edu/tag/06DI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace IsLocalRing
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

private theorem normal_of_flat_preimmersion
    {Y X : Scheme.{u}} (f : Y ⟶ X) [Flat f] [IsPreimmersion f]
    [IsNormal X] : IsNormal Y := by
  constructor
  · intro y
    have := isIso_stalkMap_of_flat_isPreimmersion f y
    exact (asIso (f.stalkMap y)).symm.commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
  · intro y
    have := isIso_stalkMap_of_flat_isPreimmersion f y
    exact (IsNormal.stalk_normal (f y)).of_equiv
      (asIso (f.stalkMap y)).commRingCatIsoToRingEquiv

private theorem integral_of_flat_preimmersion
    {Y X : Scheme.{u}} (f : Y ⟶ X) [Flat f] [IsPreimmersion f]
    [IsIntegral X] [Nonempty Y] : IsIntegral Y := by
  have : ∀ y : Y, _root_.IsReduced (Y.presheaf.stalk y) := fun y ↦ by
    have := isIso_stalkMap_of_flat_isPreimmersion f y
    exact isReduced_of_injective (inv (f.stalkMap y)).hom
      (ConcreteCategory.bijective_of_isIso _).1
  have : IsReduced Y := isReduced_of_isReduced_stalk Y
  obtain ⟨y⟩ := ‹Nonempty Y›
  obtain ⟨η, hηy, hη⟩ := Flat.generalizingMap f (genericPoint_specializes (f y))
  have hgen : IsGenericPoint η (Set.univ : Set Y) :=
    Set.eq_univ_iff_forall.mpr fun z ↦ specializes_iff_mem_closure.mp <|
      f.isEmbedding.isInducing.specializes_iff.mp (hη ▸ genericPoint_specializes (f z))
  have : IrreducibleSpace Y := (irreducibleSpace_def Y).mpr hgen.isIrreducible
  exact isIntegral_of_irreducibleSpace_of_isReduced Y

private theorem unramified_respectsIso : MorphismProperty.RespectsIso (@Unramified.{u}) := by
  let P : MorphismProperty Scheme.{u} := @LocallyOfFiniteType
  let Q : MorphismProperty Scheme.{u} := @FormallyUnramified
  have h : (@Unramified.{u}) = P ⊓ Q :=
    MorphismProperty.ext _ _ (fun _ _ f ↦
      AlgebraicGeometry.unramified_iff_locallyOfFiniteType_and_formallyUnramified f)
  rw [h]
  exact MorphismProperty.RespectsIso.inf P Q

attribute [local instance] unramified_respectsIso

private theorem finite_etale_of_integral_unramified
    {Y X : Scheme.{u}} (f : Y ⟶ X) [IsIntegral Y] [IsIntegral X]
    [IsNormal X] [IsIntegralHom f] [IsDominant f]
    (hf : Unramified f) : IsFinite f ∧ Etale f := by
  have hn : Unramified f.fromNormalization := by
    apply (MorphismProperty.cancel_left_of_respectsIso
      (P := @Unramified.{u}) f.toNormalization f.fromNormalization).mp
    simpa only [Scheme.Hom.toNormalization_fromNormalization] using hf
  have he : Etale f.fromNormalization :=
    (AlgebraicGeometry.unramified_normalization_iff_etale f).mp hn
  have hfin := (AlgebraicGeometry.etale_normalization_iff_finite_etale f).mp he
  have := hfin.1
  have := hfin.2
  rw [← f.toNormalization_fromNormalization]
  exact ⟨inferInstance, inferInstance⟩


private theorem finite_etale_pullback_stalk_of_unramified
    {Y X : Scheme.{u}} (f : Y ⟶ X) [IsIntegral Y] [IsIntegral X]
    [IsNormal X] [IsIntegralHom f] [IsDominant f] (x : X)
    (hf : Unramified (pullback.snd f (X.fromSpecStalk x))) :
    IsFinite (pullback.snd f (X.fromSpecStalk x)) ∧
      Etale (pullback.snd f (X.fromSpecStalk x)) := by
  have : Surjective f := by
    constructor
    rw [← Set.range_eq_univ]
    exact (f.isClosedMap.isClosed_range).closure_eq.symm.trans
      (dense_iff_closure_eq.mp f.denseRange)
  let g := X.fromSpecStalk x
  have : Flat g := flat_fromSpecStalk X x
  let p := pullback.snd f g
  have : Nonempty (pullback f g : Scheme.{u}) :=
    ⟨(p.surjective (closedPoint (X.presheaf.stalk x))).choose⟩
  have : IsIntegral (pullback f g) :=
    integral_of_flat_preimmersion (pullback.fst f g)
  have : IsIntegral (Spec (X.presheaf.stalk x)) :=
    integral_of_flat_preimmersion g
  have : IsNormal (Spec (X.presheaf.stalk x)) :=
    normal_of_flat_preimmersion g
  exact finite_etale_of_integral_unramified p hf

private theorem exists_rank_of_subsingleton
    {X : Scheme.{u}} [Nonempty X] [Subsingleton X] (M : X.Modules)
    [hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M] :
    ∃ d : ℕ,
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M d := by
  classical
  obtain ⟨q, hfree, hfinite⟩ := hM.exists_isFiniteLocallyFreeData
  obtain ⟨x⟩ := ‹Nonempty X›
  have hcover : (⨆ i, q.X i) = ⊤ := (Opens.coversTop_iff X q.X).mp q.coversTop
  have hx : x ∈ ⨆ i, q.X i := by rw [hcover]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  have hiTop : q.X i = ⊤ := by
    apply top_unique
    intro y hy
    simpa only [Subsingleton.elim y x] using hi
  have : (q.generators i).IsFiniteType := hfinite.isFiniteType i
  let : Fintype (q.generators i).I := Fintype.ofFinite _
  let q' : M.LocalGeneratorsData.{u} := {
    I := ULift.{u} Unit
    X := fun _ ↦ q.X i
    coversTop := (Opens.coversTop_iff X _).mpr (by simp [IsOpenCover, hiTop])
    generators := fun _ ↦ q.generators i }
  refine ⟨Fintype.card (q.generators i).I, ?_⟩
  constructor
  refine ⟨q', ?_, ?_⟩
  · constructor
    intro j
    exact hfree.isIso i
  · intro j
    exact ⟨Fintype.equivFin _⟩

private alias local_rank_iso_of_local_generators := local_rank_iso_of_generators

private lemma scheme_rank_of_sheaf_rank
    {X : Scheme.{u}} (M : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r] :
    M.IsFiniteLocallyFreeOfRank r := by
  intro x
  let : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r := inferInstance
  obtain ⟨q, hfree, hrank⟩ :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.exists_isFiniteLocallyFreeOfRankData
      (M := M) (r := r)
  have hcover := q.coversTop (⊤ : X.Opens)
  have hcover' : ∀ y ∈ (⊤ : X.Opens), ∃ V f,
      (Sieve.ofObjects q.X (⊤ : X.Opens)).arrows f ∧ y ∈ V :=
    (Opens.mem_grothendieckTopology (T := X)).mp hcover
  obtain ⟨V, f, hf, hxV⟩ := hcover' x (by simp)
  obtain ⟨i, ⟨g⟩⟩ := Sieve.mem_ofObjects_iff q.X f |>.mp hf
  refine ⟨q.X i, g.le hxV, ?_⟩
  let : IsIso (q.generators i).π := hfree.isIso i
  obtain ⟨e⟩ := hrank i
  simpa using local_rank_iso_of_local_generators M (q.generators i) r inferInstance ⟨e⟩

private lemma module_rank_of_sheaf_rank_on_spec
    (R : CommRingCat.{u}) (M : (Spec R).Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r] :
    Module.IsFiniteLocallyFreeOfRank R
      ((modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤)) r := by
  let : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree M r
  let : SheafOfModules.IsLocallyFree.{u, u, u} M := by
    have hM' := (inferInstance :
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M)
    obtain ⟨q, hq, -⟩ := hM'.exists_isFiniteLocallyFreeData
    exact SheafOfModules.IsLocallyFree.mk (M := M) ⟨q, hq⟩
  let : SheafOfModules.IsQuasicoherent.{u, u, u} M := by
    let hfree := (inferInstance : SheafOfModules.IsLocallyFree.{u, u, u} M)
    let q := hfree.exists_isLocallyFreeData.choose
    let : q.IsLocallyFreeData := hfree.exists_isLocallyFreeData.choose_spec
    exact q.quasiCoherentData.isQuasicoherent
  let : IsIso M.fromTildeΓ := inferInstance
  let N := (modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤)
  let e : tilde N ≅ M := asIso M.fromTildeΓ
  have hM := scheme_rank_of_sheaf_rank M r
  have hN := scheme_rank_transport_iso e.symm r hM
  exact (tilde_isFiniteLocallyFreeOfRank_iff R N r).mp hN

/-- Over a field, a finite locally free module of rank `r` has dimension `r`. -/
private alias module_rank_eq_finrank_field :=
  AlgebraicGeometry.GroupoidScheme.finrank_eq_of_isFiniteLocallyFreeOfRank

private theorem finrank_sections_eq_of_rank
    {k : Type u} [Field k] {Z : Scheme.{u}}
    (g : Z ⟶ Spec (.of k)) (r : ℕ)
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank g r] :
    letI : Algebra k Γ(Z, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom.toAlgebra
    Module.finrank k Γ(Z, ⊤) = r := by
  let : Algebra k Γ(Z, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom.toAlgebra
  let M := Stacks.Morphisms.pushforwardStructureSheaf g
  have hM : Module.IsFiniteLocallyFreeOfRank (CommRingCat.of k)
      ((modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤)) r :=
    module_rank_of_sheaf_rank_on_spec (.of k) M r
  change Module.finrank k Γ(Z, ⊤) = r
  exact module_rank_eq_finrank_field hM


section FiniteLocallyFreeOverField

attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules
attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules.instCategory

/-- Finite local freeness of a sheaf of modules is invariant under isomorphism. -/
private theorem finiteLocallyFree_of_iso
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}}
    [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M N : SheafOfModules.{u} R}
    (e : M ≅ N) [hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree M] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree N := by
  obtain ⟨q, hfree, hfinite⟩ := hM.exists_isFiniteLocallyFreeData
  let q' : SheafOfModules.LocalGeneratorsData.{u} N := {
    I := q.I
    X := q.X
    coversTop := q.coversTop
    generators := fun i => (q.generators i).ofEpi (e.hom.over (q.X i)) }
  have hfree' : q'.IsLocallyFreeData := by
    constructor
    intro i
    dsimp [q']
    rw [SheafOfModules.GeneratingSections.ofEpi_π]
    exact IsIso.comp_isIso' (hfree.isIso i) (Functor.map_isIso _ e.hom)
  have hfinite' : q'.IsFiniteType := by
    constructor
    intro i
    have := hfinite.isFiniteType i
    infer_instance
  exact ⟨q', hfree', hfinite'⟩

/-- A finite projective module is finite locally free. -/
private lemma moduleFiniteLocallyFree_of_finite_projective (R M : Type u) [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M] :
    Module.IsFiniteLocallyFree R M := by
  classical
  obtain ⟨s, hs, hloc⟩ :
      ∃ s : Set R, Ideal.span s = ⊤ ∧
        ∀ f ∈ s, Module.Free (Localization.Away f) (LocalizedModule.Away f M) ∧
          Module.Finite (Localization.Away f) (LocalizedModule.Away f M) :=
    (Module.finite_projective_tfae R M).out 2 7
      (a := Module.Finite R M ∧ Module.Projective R M)
      (b := ∃ s : Set R, Ideal.span s = ⊤ ∧
        ∀ f ∈ s, Module.Free (Localization.Away f) (LocalizedModule.Away f M) ∧
          Module.Finite (Localization.Away f) (LocalizedModule.Away f M)).mp
      ⟨inferInstance, inferInstance⟩
  exact ⟨s, Subtype.val, by simpa using hs, fun f => hloc f f.property⟩

/-- The structure sheaf of a scheme, regarded as a module over itself. -/
private noncomputable def selfModule (Z : Scheme.{u}) : Z.Modules :=
  SheafOfModules.unit Z.ringCatSheaf

/-- The canonical comparison from the structure sheaf of the target to the direct image of
the structure sheaf of the source. -/
private noncomputable def unitToPushforwardUnit {Y Z : Scheme.{u}} (e : Y ⟶ Z) :
    selfModule Z ⟶ Stacks.Morphisms.pushforwardStructureSheaf e :=
  SheafOfModules.unitToPushforwardObjUnit e.toRingCatSheafHom

private lemma isIso_unitToPushforwardUnit {Y Z : Scheme.{u}} (e : Y ⟶ Z) [IsIso e] :
    IsIso (unitToPushforwardUnit e) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro U
  have h : IsIso (e.toRingCatSheafHom.hom.app (Opposite.op U)) := by
    change IsIso ((forget₂ CommRingCat RingCat).map (e.app U))
    infer_instance
  change IsIso ((forget₂ RingCat AddCommGrpCat).map (e.toRingCatSheafHom.hom.app (Opposite.op U)))
  infer_instance

/-- Finite local freeness of `f_* 𝒪` is unchanged by precomposing `f` with an isomorphism. -/
private lemma sheafFiniteLocallyFree_comp_isIso {Y Y' Z : Scheme.{u}} (e : Y ⟶ Y') [IsIso e]
    (g : Y' ⟶ Z)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (Stacks.Morphisms.pushforwardStructureSheaf g)] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (Stacks.Morphisms.pushforwardStructureSheaf (e ≫ g)) := by
  let eu : selfModule Y' ≅ Stacks.Morphisms.pushforwardStructureSheaf e :=
    @asIso _ _ _ _ (unitToPushforwardUnit e) (isIso_unitToPushforwardUnit e)
  let e₂ : Stacks.Morphisms.pushforwardStructureSheaf g ≅
      (Scheme.Modules.pushforward g).obj (Stacks.Morphisms.pushforwardStructureSheaf e) :=
    (Scheme.Modules.pushforward g).mapIso eu
  let e₁ : (Scheme.Modules.pushforward g).obj (Stacks.Morphisms.pushforwardStructureSheaf e) ≅
      Stacks.Morphisms.pushforwardStructureSheaf (e ≫ g) :=
    (Scheme.Modules.pushforwardComp e g).app (SheafOfModules.unit Y.ringCatSheaf)
  exact finiteLocallyFree_of_iso.{u} (e₂ ≪≫ e₁)

/-- The direct image of the structure sheaf along `Spec` of a ring map is the sheaf
associated with the target ring, restricted along that map. -/
private noncomputable def specMap_pushforward_iso
    (R S : CommRingCat.{u}) (φ : R ⟶ S) :
    Stacks.Morphisms.pushforwardStructureSheaf (Spec.map φ) ≅
      tilde ((ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of S S)) :=
  (Scheme.Modules.pushforward (Spec.map φ)).mapIso (tildeSelf (R := S)).symm ≪≫
    (AlgebraicGeometry.pushforwardTildeIso R S φ).app
      (ModuleCat.of S S)

/-- If a ring map makes the target a finite projective module over the source, then the
direct image of the structure sheaf along the induced map of spectra is finite locally free. -/
private lemma sheafFiniteLocallyFree_specMap (R S : CommRingCat.{u}) (φ : R ⟶ S)
    (hfin : letI := φ.hom.toAlgebra; Module.Finite R S)
    (hproj : letI := φ.hom.toAlgebra; Module.Projective R S) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (Stacks.Morphisms.pushforwardStructureSheaf (Spec.map φ)) := by
  algebraize [φ.hom]
  let : Module.Finite R S := hfin
  let : Module.Projective R S := hproj
  have hmod : Module.IsFiniteLocallyFree R
      ((ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of S S)) := by
    change Module.IsFiniteLocallyFree R S
    exact moduleFiniteLocallyFree_of_finite_projective _ _
  have h' := (Stacks.Modules.tilde_isFiniteLocallyFree_iff_module R _).mpr hmod
  exact finiteLocallyFree_of_iso.{u} (specMap_pushforward_iso R S φ).symm (hM := h')

/-- For a finite morphism to the spectrum of a field, the direct image of the structure
sheaf is finite locally free. -/
private theorem sheafFiniteLocallyFree_of_finite_over_field
    {k : Type u} [Field k] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of k)) [IsFinite f] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (Stacks.Morphisms.pushforwardStructureSheaf f) := by
  have : IsAffineHom f := inferInstance
  have : IsAffine Y := isAffine_of_isAffineHom f
  set φ : CommRingCat.of k ⟶ Γ(Y, ⊤) := (Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop with hφ
  have hfe : f = Y.toSpecΓ ≫ Spec.map φ := by
    rw [hφ, Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality,
      Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  have hIF : IsFinite (Y.toSpecΓ ≫ Spec.map φ) := hfe ▸ (inferInstance : IsFinite f)
  have : MorphismProperty.RespectsIso (@IsFinite : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : IsFinite (Spec.map φ) :=
    (MorphismProperty.cancel_left_of_respectsIso
      (@IsFinite : MorphismProperty Scheme.{u}) Y.toSpecΓ (Spec.map φ)).mp hIF
  let : Field ↥(CommRingCat.of k) := inferInstanceAs (Field k)
  let : Algebra ↥(CommRingCat.of k) ↥Γ(Y, ⊤) := φ.hom.toAlgebra
  have hfin : Module.Finite ↥(CommRingCat.of k) ↥Γ(Y, ⊤) :=
    (IsFinite.SpecMap_iff φ).mp inferInstance
  have hproj : Module.Projective ↥(CommRingCat.of k) ↥Γ(Y, ⊤) :=
    Module.Projective.of_free
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (Stacks.Morphisms.pushforwardStructureSheaf (Spec.map φ)) :=
    sheafFiniteLocallyFree_specMap _ _ φ hfin hproj
  rw [hfe]
  exact sheafFiniteLocallyFree_comp_isIso Y.toSpecΓ (Spec.map φ)

end FiniteLocallyFreeOverField

private theorem exists_rank_of_finite_etale_over_field
    {k : Type u} [Field k] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of k))
    [IsFinite f] [Etale f] :
    ∃ d : ℕ, Stacks.Morphisms.IsFiniteLocallyFreeOfRank f d := by
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (Stacks.Morphisms.pushforwardStructureSheaf f) :=
    sheafFiniteLocallyFree_of_finite_over_field f
  obtain ⟨d, hd⟩ := exists_rank_of_subsingleton (Stacks.Morphisms.pushforwardStructureSheaf f)
  exact ⟨d, (Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff f d).mpr ⟨inferInstance, hd⟩⟩

private theorem finrank_fiber_eq_finrank_fractionExtension
    (A K B L : Type u) [CommRing A] [IsDomain A] [CommRing K]
    [CommRing B] [CommRing L] [Algebra A B] [Algebra A K]
    [Algebra A L] [Algebra B L] [Module K L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L]
    [Module.Finite A B] [Module.Flat A B]
    (p : Ideal A) [p.IsPrime] :
    Module.finrank p.ResidueField (p.Fiber B) = Module.finrank K L := by
  rw [p.finrank_fiber_eq_finrank, IsFractionRing.finrank_eq A K B L]

private theorem algHom_eq_of_unramified_of_sub_mem
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [IsDomain B]
    [Algebra R A] [Algebra R B] [Algebra.EssFiniteType R A]
    [Algebra.FormallyUnramified R A] (φ ψ : A →ₐ[R] B)
    (I : Ideal B) (hI : I ≠ ⊤) (h : ∀ a, ψ a - φ a ∈ I) : φ = ψ := by
  let t := Algebra.FormallyUnramified.elem R A
  let F : A ⊗[R] A →ₐ[R] B := Algebra.TensorProduct.lift φ ψ (fun _ _ ↦ .all _ _)
  have hF : (Ideal.Quotient.mkₐ R I).comp F =
      ((Ideal.Quotient.mkₐ R I).comp φ).comp (Algebra.TensorProduct.lmul' R) := by
    apply Algebra.TensorProduct.ext
    · ext a
      simp [F]
    · ext a
      simpa [F] using (Ideal.Quotient.eq.mpr (h a))
  have ht : Ideal.Quotient.mk I (F t) = 1 := by
    have := DFunLike.congr_fun hF t
    change Ideal.Quotient.mk I (F t) =
      Ideal.Quotient.mk I (φ (Algebra.TensorProduct.lmul' R t)) at this
    simpa [t, Algebra.FormallyUnramified.lmul_elem] using this
  have hne : F t ≠ 0 := by
    intro hzero
    have hone : (1 : B ⧸ I) = 0 := by simpa [hzero] using ht.symm
    exact hI (Ideal.eq_top_of_isUnit_mem I (by
      exact Ideal.Quotient.eq_zero_iff_mem.mp hone) isUnit_one)
  ext a
  have ha := congrArg F (Algebra.FormallyUnramified.one_tmul_sub_tmul_one_mul_elem
    (R := R) (S := A) a)
  change F ((1 ⊗ₜ[R] a - a ⊗ₜ[R] 1) * t) = F 0 at ha
  simp only [map_mul, map_sub, map_zero] at ha
  simp only [F, Algebra.TensorProduct.lift_tmul, map_one, one_mul, mul_one] at ha
  exact (sub_eq_zero.mp ((mul_eq_zero.mp ha).resolve_right hne)).symm

private theorem functionFieldMap_closedPoint
    (X : Scheme.{u}) [IsIntegral X]
    (L : Type u) [Field L] [Algebra X.functionField L]
    (i : Spec (.of L) ⟶ X)
    (hi : i = Spec.map (CommRingCat.ofHom (algebraMap X.functionField L)) ≫
      X.fromSpecStalk (genericPoint X)) : i (closedPoint L) = genericPoint X := by
  rw [hi]
  change X.fromSpecStalk (genericPoint X)
    (Spec.map (CommRingCat.ofHom (algebraMap X.functionField L))
      (closedPoint L)) = genericPoint X
  have heq : Spec.map (CommRingCat.ofHom (algebraMap X.functionField L))
      (closedPoint L) = closedPoint (X.presheaf.stalk (genericPoint X)) :=
    Subsingleton.elim _ _
  rw [heq, Scheme.fromSpecStalk_closedPoint]

/-- The closed point of `Spec L` maps into every nonempty open of `X`. -/
private theorem functionFieldMap_closedPoint_mem
    (X : Scheme.{u}) [IsIntegral X]
    (L : Type u) [Field L] [Algebra X.functionField L]
    (i : Spec (.of L) ⟶ X)
    (hi : i = Spec.map (CommRingCat.ofHom (algebraMap X.functionField L)) ≫
      X.fromSpecStalk (genericPoint X))
    (U : X.Opens) [Nonempty U] : i (closedPoint L) ∈ U := by
  rw [functionFieldMap_closedPoint X L i hi]
  exact (genericPoint_spec X).mem_open_set_iff U.isOpen |>.mpr
    (by simpa only [Set.univ_inter] using
      (Set.nonempty_coe_sort.mp (inferInstance : Nonempty U)))

/-- On sections over `U`, `i` is the map `Γ(X, U) ⟶ K` followed by `K ⟶ L`. -/
private theorem app_comp_functionFieldMap
    (X : Scheme.{u}) [IsIntegral X]
    (L : Type u) [Field L] [Algebra X.functionField L]
    (i : Spec (.of L) ⟶ X)
    (hi : i = Spec.map (CommRingCat.ofHom (algebraMap X.functionField L)) ≫
      X.fromSpecStalk (genericPoint X))
    (U : X.Opens) [Nonempty U] (hx : i (closedPoint L) ∈ U) :
    i.app U ≫ ((Spec (.of L)).presheaf.mapIso
        (eqToIso (Scheme.preimage_eq_top_of_closedPoint_mem i hx).symm).op ≪≫
          Scheme.ΓSpecIso (.of L)).hom =
      X.germToFunctionField U ≫ CommRingCat.ofHom (algebraMap X.functionField L) := by
  rw [← Scheme.germ_stalkClosedPointTo i U hx]
  subst hi
  exact Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk _ U hx

private noncomputable def functionFieldMapSectionsEquiv
    (X : Scheme.{u}) [IsIntegral X]
    (L : Type u) [Field L] [Algebra X.functionField L]
    (i : Spec (.of L) ⟶ X)
    (hi : i = Spec.map (CommRingCat.ofHom (algebraMap X.functionField L)) ≫
      X.fromSpecStalk (genericPoint X))
    (U : X.Opens) [Nonempty U] :
    letI : Algebra Γ(X, U) L :=
      ((algebraMap X.functionField L).comp (X.germToFunctionField U).hom).toAlgebra
    letI : Algebra Γ(X, U) Γ(Spec (.of L), i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
    Γ(Spec (.of L), i ⁻¹ᵁ U) ≃ₐ[Γ(X, U)] L := by
  letI : Algebra Γ(X, U) L :=
    ((algebraMap X.functionField L).comp (X.germToFunctionField U).hom).toAlgebra
  letI : Algebra Γ(X, U) Γ(Spec (.of L), i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
  have hx := functionFieldMap_closedPoint_mem X L i hi U
  let e := (Spec (.of L)).presheaf.mapIso
    (eqToIso (Scheme.preimage_eq_top_of_closedPoint_mem i hx).symm).op ≪≫
      Scheme.ΓSpecIso (.of L)
  refine { __ := e.commRingCatIsoToRingEquiv, commutes' := ?_ }
  intro a
  exact ConcreteCategory.congr_hom (app_comp_functionFieldMap X L i hi U hx) a

private noncomputable def normalizationSectionsEquiv
    (X : Scheme.{u}) [IsIntegral X]
    (L : Type u) [Field L] [Algebra X.functionField L]
    (i : Spec (.of L) ⟶ X)
    (hi : i = Spec.map (CommRingCat.ofHom (algebraMap X.functionField L)) ≫
      X.fromSpecStalk (genericPoint X))
    [QuasiCompact i] [QuasiSeparated i]
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI : Algebra Γ(X, U) L :=
      ((algebraMap X.functionField L).comp (X.germToFunctionField U).hom).toAlgebra
    letI : Algebra Γ(X, U) Γ(i.normalization, i.fromNormalization ⁻¹ᵁ U) :=
      (i.fromNormalization.app U).hom.toAlgebra
    Γ(i.normalization, i.fromNormalization ⁻¹ᵁ U) ≃ₐ[Γ(X, U)]
      integralClosure Γ(X, U) L := by
  letI : Algebra Γ(X, U) L :=
    ((algebraMap X.functionField L).comp (X.germToFunctionField U).hom).toAlgebra
  let A := Γ(X, U)
  let S := Γ(Spec (.of L), i ⁻¹ᵁ U)
  let N := Γ(i.normalization, i.fromNormalization ⁻¹ᵁ U)
  letI : Algebra A S := (i.app U).hom.toAlgebra
  letI : Algebra A N := (i.fromNormalization.app U).hom.toAlgebra
  let e : N ≃ₐ[A] integralClosure A S := {
    __ := (i.normalizationObjIso hU).commRingCatIsoToRingEquiv
    commutes' a := by
      change (i.normalizationObjIso hU).hom (i.fromNormalization.app U a) = _
      rw [i.fromNormalization_app hU]
      simp
      rfl
  }
  exact e.trans (functionFieldMapSectionsEquiv X L i hi U).mapIntegralClosure

private theorem inertia_eq_one_of_unramified_integralClosure
    (A K L : Type u) [CommRing A] [IsDomain A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L] [FiniteDimensional K L]
    [Algebra A L] [IsScalarTower A K L]
    [Algebra.EssFiniteType A (integralClosure A L)]
    [Algebra.FormallyUnramified A (integralClosure A L)]
    (q : Ideal (integralClosure A L)) (hq : q ≠ ⊤)
    (σ : L ≃ₐ[K] L)
    (hσ : ∀ y, galRestrict A K L (integralClosure A L) σ y - y ∈ q) :
    σ = 1 := by
  have he : (AlgHom.id A (integralClosure A L)) =
      (galRestrict A K L (integralClosure A L) σ).toAlgHom :=
    algHom_eq_of_unramified_of_sub_mem _ _ q hq hσ
  have : IsFractionRing (integralClosure A L) L :=
    IsIntegralClosure.isFractionRing_of_finite_extension A K L (integralClosure A L)
  have hf : σ.toRingHom = (1 : L ≃ₐ[K] L).toRingHom := by
    apply IsFractionRing.ringHom_ext (A := integralClosure A L)
    intro y
    change σ ((algebraMap (integralClosure A L) L) y) = (algebraMap (integralClosure A L) L) y
    rw [← algebraMap_galRestrict_apply A σ y]
    exact congrArg Subtype.val (DFunLike.congr_fun he y).symm
  ext y
  exact RingHom.congr_fun hf y

private theorem etale_fixedPoints_of_inertia_eq_bot
    (B G : Type u) [CommRing B] [Group G] [Finite G] [MulSemiringAction G B]
    (h : ∀ (q : Ideal B) [q.IsPrime], q.inertia G = ⊥) :
    Algebra.Etale (FixedPoints.subring B G) B := by
  classical
  let RG := FixedPoints.subring B G
  have hlocal (q : Ideal B) [q.IsPrime] :
      ∃ b : B, b ∉ q ∧ Algebra.Etale RG (Localization.Away b) := by
    let I := q.inertia G
    let RI := FixedPoints.subring B I
    let : Algebra RG RI := (Subring.inclusion (by
      intro x hx g
      exact hx g)).toAlgebra
    obtain ⟨g, hg, he⟩ := MulSemiringAction.exists_etale_away_fixedPoints_inertia (G := G) q
    have : Algebra.Etale RG (Localization.Away g) := he
    have hbij : Function.Bijective RI.subtype := by
      refine ⟨Subtype.val_injective, ?_⟩
      intro b
      refine ⟨⟨b, ?_⟩, rfl⟩
      intro σ
      have heq : (σ : G) = 1 := by
        have := σ.property
        change (σ : G) ∈ q.inertia G at this
        rwa [h q] at this
      change (σ : G) • b = b
      rw [heq, one_smul]
    let e : RI ≃ₐ[RG] B := {
      __ := RingEquiv.ofBijective RI.subtype hbij
      commutes' _ := rfl
    }
    have hmap : (Submonoid.powers g).map e.toRingEquiv.toMonoidHom =
        Submonoid.powers (e g) := by simp
    let e' : Localization.Away g ≃ₐ[RG] Localization.Away (e g) := {
      __ := IsLocalization.ringEquivOfRingEquiv _ _ e.toRingEquiv hmap
      commutes' a := by
        rw [IsScalarTower.algebraMap_apply RG RI (Localization.Away g)]
        change (IsLocalization.ringEquivOfRingEquiv _ _ e.toRingEquiv hmap)
          (algebraMap RI (Localization.Away g) (algebraMap RG RI a)) = _
        rw [IsLocalization.ringEquivOfRingEquiv_eq]
        change algebraMap B _ (e (algebraMap RG RI a)) = _
        rw [e.commutes]
        exact (IsScalarTower.algebraMap_apply RG B (Localization.Away (e g)) a).symm
    }
    exact ⟨e g, hg, Algebra.Etale.of_equiv e'⟩
  let s : Set B := {b | Algebra.Etale RG (Localization.Away b)}
  have hs : Ideal.span s = ⊤ := by
    by_contra htop
    obtain ⟨q, hq, hle⟩ := Ideal.exists_le_maximal (Ideal.span s) htop
    let : q.IsMaximal := hq
    obtain ⟨b, hb, he⟩ := hlocal q
    exact hb (hle (Ideal.subset_span he))
  apply (RingHom.etale_algebraMap).mp
  apply RingHom.Etale.ofLocalizationSpanTarget (algebraMap RG B) s hs
  intro b
  simpa only [← IsScalarTower.algebraMap_eq RG B (Localization.Away b.1),
    RingHom.etale_algebraMap] using (show Algebra.Etale RG (Localization.Away b.1) from b.property)

private theorem etale_of_invariant_of_inertia_eq_bot
    (A B G : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
    [Algebra.IsInvariant A B G] (hinj : Function.Injective (algebraMap A B))
    (h : ∀ (q : Ideal B) [q.IsPrime], q.inertia G = ⊥) : Algebra.Etale A B := by
  let RG := FixedPoints.subring B G
  let α : A →+* RG := (algebraMap A B).codRestrict RG (fun a ↦ by
    intro σ
    exact smul_algebraMap σ a)
  let : Algebra A RG := α.toAlgebra
  have hbij : Function.Bijective α := by
    refine ⟨fun x y hxy ↦ hinj (congrArg Subtype.val hxy), ?_⟩
    intro b
    obtain ⟨a, ha⟩ := Algebra.IsInvariant.isInvariant (A := A) b.1 b.2
    exact ⟨a, Subtype.ext ha⟩
  have : Algebra.Etale A RG := (RingHom.Etale.of_bijective hbij).toAlgebra
  have : IsScalarTower A RG B := .of_algebraMap_eq' rfl
  have : Algebra.Etale RG B := etale_fixedPoints_of_inertia_eq_bot B G h
  exact Algebra.Etale.comp A RG B

@[sga "1 V 2.3" "(e), special case"]
private theorem integralClosure_etale_of_trivialInertia
    (A K L : Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Algebra A L] [IsScalarTower A K L]
    (h : ∀ (q : Ideal (integralClosure A L)) (_hq : q.IsPrime)
      (σ : L ≃ₐ[K] L),
      (∀ y, galRestrict A K L (integralClosure A L) σ y - y ∈ q) → σ = 1) :
    Algebra.Etale A (integralClosure A L) := by
  let B := integralClosure A L
  let G := L ≃ₐ[K] L
  have : IsFractionRing B L :=
    IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  let : MulSemiringAction G B := IsIntegralClosure.MulSemiringAction A K L B
  have hsmul (σ : G) (y : B) : σ • y = galRestrict A K L B σ y := rfl
  have : SMulCommClass G A B := ⟨fun σ a y ↦ by
    simp only [hsmul, map_smul]⟩
  have : Algebra.IsInvariant A B G := Algebra.isInvariant_of_isGalois A K L B
  apply etale_of_invariant_of_inertia_eq_bot A B G
  · intro a b hab
    apply IsFractionRing.injective A K
    apply (algebraMap K L).injective
    simpa only [← IsScalarTower.algebraMap_apply A K L,
      ← IsScalarTower.algebraMap_apply A B L] using
      congrArg (algebraMap B L) hab
  · exact fun q hq ↦ le_antisymm (fun σ hσ ↦ h q hq σ (Ideal.mem_inertia.mp hσ)) bot_le

/-- The base change of `f` along `h ≫ g` is unramified iff the base change along `h` of the
base change of `f` along `g` is. -/
private theorem unramified_snd_comp_iff
    {Y X S T : Scheme.{u}} (f : Y ⟶ X) (g : S ⟶ X) (h : T ⟶ S) :
    Unramified (pullback.snd f (h ≫ g)) ↔ Unramified (pullback.snd (pullback.snd f g) h) := by
  rw [← pullbackLeftPullbackSndIso_hom_snd f g h]
  exact (MorphismProperty.cancel_left_of_respectsIso (@Unramified.{u}) _ _).symm

private theorem unramified_pullback_of_pullback_comp
    {Y X S T : Scheme.{u}} (f : Y ⟶ X) (g : S ⟶ X) (h : T ⟶ S)
    [Flat h] [Surjective h] [QuasiCompact h]
    (hh : Unramified (pullback.snd f (h ≫ g))) :
    Unramified (pullback.snd f g) := by
  let P : MorphismProperty Scheme.{u} := @Unramified
  have hn : P (pullback.snd (pullback.snd f g) h) := (unramified_snd_comp_iff f g h).mp hh
  apply MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd
    (P := P) (K := Scheme.fpqcPrecoverage)
    (f := pullback.snd f g) h.singleton_mem_fpqcPrecoverage
  intro Z k _ hk
  cases hk
  exact hn

private theorem exists_isHenselization_of_sepClosure
    (A : Type u) [CommRing A] [IsLocalRing A]
    (ksep : Type u) [Field ksep] [Algebra (ResidueField A) ksep]
    [IsSepClosure (ResidueField A) ksep] :
    ∃ (B : Type u) (_ : CommRing B) (_ : IsLocalRing B) (_ : Algebra A B),
      IsHenselization A ksep B := by
  have hA : (CommAlgCat.etale A).ind (CommAlgCat.of A A) :=
    (CommAlgCat.etale A).le_ind _ inferInstance
  have hres : Function.Surjective (ResidueField.map (algebraMap A A)) := by
    simpa using (Function.surjective_id :
      Function.Surjective (id : ResidueField A → ResidueField A))
  obtain ⟨B, hRing, hLocal, hAlg, hAlg', hTower, hLocalHom, hHens,
    hSep, hInd, hMax, hCompat⟩ := exists_strictHenselization A A hA hres ksep
  let := hRing
  let := hLocal
  let := hAlg
  exact ⟨B, hRing, hLocal, hAlg, IsHenselization.of_ind_etale hHens hInd hCompat⟩

private theorem unramified_pullback_comp
    {Y X S T : Scheme.{u}} (f : Y ⟶ X) (g : S ⟶ X) (h : T ⟶ S)
    (hh : Unramified (pullback.snd f g)) :
    Unramified (pullback.snd f (h ≫ g)) :=
  (unramified_snd_comp_iff f g h).mpr
    (AlgebraicGeometry.unramified_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback (pullback.snd f g) h) hh)

private theorem isDominant_functionFieldMap
    (X : Scheme.{u}) [IsIntegral X]
    (L : Type u) [Field L] [Algebra X.functionField L]
    (i : Spec (.of L) ⟶ X)
    (hi : i = Spec.map (CommRingCat.ofHom (algebraMap X.functionField L)) ≫
      X.fromSpecStalk (genericPoint X)) : IsDominant i := by
  rw [isDominant_iff, denseRange_iff_closure_range]
  apply top_unique
  calc
    (Set.univ : Set X) = closure {genericPoint X} :=
      (genericPoint_spec X).symm
    _ ≤ closure (Set.range i) := closure_mono <| by
      rw [Set.singleton_subset_iff]
      refine ⟨closedPoint L, ?_⟩
      exact functionFieldMap_closedPoint X L i hi

/-- The global sections of a finite scheme over a field form a finite-dimensional algebra. -/
private theorem finite_sections_of_isFinite
    {k : Type u} [Field k] {Z : Scheme.{u}} (g : Z ⟶ Spec (.of k)) [IsFinite g] :
    letI : Algebra k Γ(Z, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom.toAlgebra
    Module.Finite k Γ(Z, ⊤) := by
  let : Algebra k Γ(Z, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom.toAlgebra
  rw [← RingHom.finite_algebraMap]
  exact RingHom.Finite.comp g.finite_appTop
    (.of_surjective _ (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (.of k)).inv).surjective)

private theorem finrank_eq_finrank_sections
    {k : Type u} [Field k] {Z : Scheme.{u}} (g : Z ⟶ Spec (.of k))
    [IsFinite g] [Flat g] (z : ↥(Spec (.of k))) :
    letI : Algebra k Γ(Z, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom.toAlgebra
    g.finrank z = Module.finrank k Γ(Z, ⊤) := by
  let : Algebra k Γ(Z, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom.toAlgebra
  have : IsAffine Z := isAffine_of_isAffineHom g
  have : Module.Finite k Γ(Z, ⊤) := finite_sections_of_isFinite g
  have hg : Z.isoSpec.hom ≫
      Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop) = g := by
    rw [Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality]
    simp
  have halg : ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop) =
      CommRingCat.ofHom (algebraMap k Γ(Z, ⊤)) := by
    simp [RingHom.algebraMap_toAlgebra]
  have : Module.Flat k Γ(Z, ⊤) := Module.Flat.of_free
  have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k Γ(Z, ⊤)))) :=
    (IsFinite.SpecMap_iff _).mpr (by simpa [RingHom.finite_algebraMap])
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap k Γ(Z, ⊤)))) :=
    (Flat.SpecMap_iff).mpr (by simpa [RingHom.flat_algebraMap_iff])
  conv_lhs => rw [← hg, halg, Scheme.Hom.finrank_comp_left_of_isIso]
  refine (Scheme.Hom.finrank_SpecMap_algebraMap k Γ(Z, ⊤) z).trans ?_
  have h4 := congrFun (Module.rankAtStalk_eq_finrank_of_free (R := k) (M := Γ(Z, ⊤))) z
  simpa only [Pi.natCast_def, Pi.natCast_apply, Nat.cast_id] using h4

private theorem finrank_eq_of_surjective_algHom
    {K A L : Type u} [Field K] [CommRing A] [IsDomain A] [Field L]
    [Algebra K A] [Algebra K L] [Module.Finite K A]
    (ψ : A →ₐ[K] L) (hψ : Function.Surjective ψ) :
    Module.finrank K A = Module.finrank K L := by
  have : Algebra.IsIntegral K A := Algebra.IsIntegral.of_finite K A
  have hfield : IsField A := isField_of_isIntegral_of_isField' (Field.toIsField K)
  have hinj : Function.Injective ψ := by
    refine (injective_iff_map_eq_zero ψ).mpr fun a ha ↦ ?_
    by_contra h0
    obtain ⟨b, hb⟩ := hfield.mul_inv_cancel h0
    simpa [ha] using congrArg ψ hb
  exact (LinearEquiv.ofBijective ψ.toLinearMap ⟨hinj, hψ⟩).finrank_eq

/-- The section of the generic fibre of the relative normalization coming from
`Spec L` itself. -/
private noncomputable def genericFiberSection
    (X : Scheme.{u}) [IsIntegral X]
    (L : Type u) [Field L] [Algebra X.functionField L]
    (i : Spec (.of L) ⟶ X)
    (hi : i = Spec.map (CommRingCat.ofHom
      (algebraMap X.functionField L)) ≫ X.fromSpecStalk (genericPoint X))
    [QuasiCompact i] [QuasiSeparated i] :
    Spec (.of L) ⟶
      pullback i.fromNormalization (X.fromSpecStalk (genericPoint ↥X)) :=
  pullback.lift i.toNormalization
    (Spec.map (CommRingCat.ofHom (algebraMap X.functionField L)))
    (by rw [Scheme.Hom.toNormalization_fromNormalization]; exact hi)

private theorem finrank_sections_genericFiber
    (X : Scheme.{u}) [IsIntegral X] [IsNormal X]
    (L : Type u) [Field L] [Algebra X.functionField L]
    [FiniteDimensional X.functionField L]
    (i : Spec (.of L) ⟶ X)
    (hi : i = Spec.map (CommRingCat.ofHom
      (algebraMap X.functionField L)) ≫ X.fromSpecStalk (genericPoint X))
    [QuasiCompact i] [QuasiSeparated i]
    [IsFinite (pullback.snd i.fromNormalization
      (X.fromSpecStalk (genericPoint ↥X)))] :
    letI : Algebra ↑X.functionField
        Γ(pullback i.fromNormalization (X.fromSpecStalk (genericPoint ↥X)), ⊤) :=
      ((Scheme.ΓSpecIso (.of ↑X.functionField)).inv ≫
        (pullback.snd i.fromNormalization
          (X.fromSpecStalk (genericPoint ↥X))).appTop).hom.toAlgebra
    Module.finrank ↑X.functionField
        Γ(pullback i.fromNormalization (X.fromSpecStalk (genericPoint ↥X)), ⊤) =
      Module.finrank ↑X.functionField L := by
  let : Algebra ↑X.functionField
      Γ(pullback i.fromNormalization (X.fromSpecStalk (genericPoint ↥X)), ⊤) :=
    ((Scheme.ΓSpecIso (.of ↑X.functionField)).inv ≫
      (pullback.snd i.fromNormalization
        (X.fromSpecStalk (genericPoint ↥X))).appTop).hom.toAlgebra
  have : Flat (X.fromSpecStalk (genericPoint ↥X)) :=
    flat_fromSpecStalk X (genericPoint ↥X)
  set w := genericFiberSection X L i hi with hw
  have : Nonempty ↥(pullback i.fromNormalization
      (X.fromSpecStalk (genericPoint ↥X))) := ⟨w (closedPoint L)⟩
  have : IsIntegral (pullback i.fromNormalization
      (X.fromSpecStalk (genericPoint ↥X))) :=
    integral_of_flat_preimmersion
      (pullback.fst i.fromNormalization (X.fromSpecStalk (genericPoint ↥X)))
  have : Module.Finite ↑X.functionField
      Γ(pullback i.fromNormalization (X.fromSpecStalk (genericPoint ↥X)), ⊤) :=
    finite_sections_of_isFinite
      (pullback.snd i.fromNormalization (X.fromSpecStalk (genericPoint ↥X)))
  have hcomm : ∀ a : ↑X.functionField,
      (Scheme.ΓSpecIso (.of L)).hom (w.appTop
          (algebraMap ↑X.functionField
            Γ(pullback i.fromNormalization
              (X.fromSpecStalk (genericPoint ↥X)), ⊤) a)) = algebraMap _ L a := by
    intro a
    have h1 : (Scheme.ΓSpecIso (.of ↑X.functionField)).inv ≫
        ((pullback.snd i.fromNormalization
          (X.fromSpecStalk (genericPoint ↥X))).appTop ≫ w.appTop) ≫
          (Scheme.ΓSpecIso (.of L)).hom =
        CommRingCat.ofHom (algebraMap ↑X.functionField L) := by
      rw [← Scheme.Hom.comp_appTop, hw,
        show genericFiberSection X L i hi ≫ pullback.snd i.fromNormalization
          (X.fromSpecStalk (genericPoint ↥X)) =
          Spec.map (CommRingCat.ofHom (algebraMap ↑X.functionField L)) from
          pullback.lift_snd _ _ _,
        ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
      simp
    simpa [RingHom.algebraMap_toAlgebra] using ConcreteCategory.congr_hom h1 a
  let ψ : Γ(pullback i.fromNormalization (X.fromSpecStalk (genericPoint ↥X)), ⊤)
      →ₐ[↑X.functionField] L :=
    { __ := ((Scheme.ΓSpecIso (.of L)).hom.hom.comp (w.appTop).hom)
      commutes' := hcomm }
  refine finrank_eq_of_surjective_algHom ψ ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hηU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (show genericPoint ↥X ∈ (⊤ : X.Opens) from trivial) isOpen_univ
  have : Nonempty U := ⟨⟨genericPoint ↥X, hηU⟩⟩
  let : Algebra Γ(X, U) L :=
    ((algebraMap ↑X.functionField L).comp (X.germToFunctionField U).hom).toAlgebra
  let : IsScalarTower Γ(X, U) ↑X.functionField L := .of_algebraMap_eq' rfl
  have : IsFractionRing Γ(X, U) ↑X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  let : Algebra Γ(X, U) Γ(Spec (.of L), i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
  have hitop : i ⁻¹ᵁ U = ⊤ := Scheme.preimage_eq_top_of_closedPoint_mem i
    (functionFieldMap_closedPoint_mem X L i hi U)
  have hg₀top : (X.fromSpecStalk (genericPoint ↥X)) ⁻¹ᵁ U = ⊤ :=
    Scheme.preimage_eq_top_of_closedPoint_mem _
      (by rw [Scheme.fromSpecStalk_closedPoint]; exact hηU)
  have hQtop : (pullback.fst i.fromNormalization
      (X.fromSpecStalk (genericPoint ↥X))) ⁻¹ᵁ (i.fromNormalization ⁻¹ᵁ U) = ⊤ := by
    rw [← Scheme.Hom.comp_preimage, pullback.condition, Scheme.Hom.comp_preimage, hg₀top]
    simp
  have e₁ : (⊤ : (pullback i.fromNormalization
      (X.fromSpecStalk (genericPoint ↥X))).Opens) ≤
      (pullback.fst i.fromNormalization
        (X.fromSpecStalk (genericPoint ↥X))) ⁻¹ᵁ (i.fromNormalization ⁻¹ᵁ U) := by
    rw [hQtop]
  have : IsDomain Γ(X, U) := inferInstance
  have : IsLocalization (Algebra.algebraMapSubmonoid
      (integralClosure Γ(X, U) L) (nonZeroDivisors Γ(X, U))) L :=
    IsIntegralClosure.isLocalization Γ(X, U) ↑X.functionField L
      (integralClosure Γ(X, U) L)
  let e_U := functionFieldMapSectionsEquiv X L i hi U
  have hint : ∀ c : integralClosure Γ(X, U) L,
      ∃ t, ψ t = algebraMap (integralClosure Γ(X, U) L) L c := by
    intro c
    have hcint : _root_.IsIntegral Γ(X, U) (e_U.symm
        (algebraMap (integralClosure Γ(X, U) L) L c)) :=
      IsIntegral.map e_U.symm.toAlgHom c.2
    let n := (i.normalizationObjIso hU).inv
      (⟨e_U.symm (algebraMap (integralClosure Γ(X, U) L) L c), hcint⟩ :
        integralClosure Γ(X, U) Γ(Spec (.of L), i ⁻¹ᵁ U))
    refine ⟨(pullback.fst i.fromNormalization
      (X.fromSpecStalk (genericPoint ↥X))).appLE (i.fromNormalization ⁻¹ᵁ U) ⊤ e₁ n, ?_⟩
    have hval : i.toNormalization.appLE (i.fromNormalization ⁻¹ᵁ U) (i ⁻¹ᵁ U)
        (by simp [← Scheme.Hom.comp_preimage]) n =
        e_U.symm (algebraMap (integralClosure Γ(X, U) L) L c) := by
      have := ConcreteCategory.congr_hom
        (Scheme.Hom.normalizationObjIso_hom_val i hU).symm n
      simpa [n] using this
    have hlift : w ≫ pullback.fst i.fromNormalization
        (X.fromSpecStalk (genericPoint ↥X)) = i.toNormalization := by
      rw [hw]; exact pullback.lift_fst _ _ _
    have hmorgen : ∀ (u : Spec (.of L) ⟶ i.normalization)
        (_ : u = w ≫ pullback.fst i.fromNormalization
          (X.fromSpecStalk (genericPoint ↥X)))
        (h : (i ⁻¹ᵁ U) ≤ u ⁻¹ᵁ (i.fromNormalization ⁻¹ᵁ U)),
        u.appLE (i.fromNormalization ⁻¹ᵁ U) (i ⁻¹ᵁ U) h =
          (pullback.fst i.fromNormalization
              (X.fromSpecStalk (genericPoint ↥X))).appLE
            (i.fromNormalization ⁻¹ᵁ U) ⊤ e₁ ≫ w.appLE ⊤ (i ⁻¹ᵁ U) le_top := by
      intro u hu h
      subst hu
      exact (Scheme.Hom.appLE_comp_appLE w (pullback.fst i.fromNormalization
        (X.fromSpecStalk (genericPoint ↥X))) (i.fromNormalization ⁻¹ᵁ U) ⊤
        (i ⁻¹ᵁ U) e₁ le_top).symm
    have hpsi : ∀ t, e_U (w.appLE ⊤ (i ⁻¹ᵁ U) le_top t) = ψ t := by
      intro t
      change (Scheme.ΓSpecIso (.of L)).hom
          ((Spec (.of L)).presheaf.map (eqToHom
            (Scheme.preimage_eq_top_of_closedPoint_mem i
              (functionFieldMap_closedPoint_mem X L i hi U)).symm).op
            (w.appLE ⊤ (i ⁻¹ᵁ U) le_top t)) = ψ t
      simp only [Scheme.Hom.appLE, ← CommRingCat.comp_apply,
        Category.assoc, ← Functor.map_comp]
      rfl
    have hchain : w.appLE ⊤ (i ⁻¹ᵁ U) le_top
        ((pullback.fst i.fromNormalization
          (X.fromSpecStalk (genericPoint ↥X))).appLE
            (i.fromNormalization ⁻¹ᵁ U) ⊤ e₁ n) =
        e_U.symm (algebraMap (integralClosure Γ(X, U) L) L c) := by
      rw [← hval]
      exact (ConcreteCategory.congr_hom
        (hmorgen i.toNormalization hlift.symm _) n).symm
    rw [← hpsi, hchain]
    simp
  intro y
  obtain ⟨⟨c, m⟩, hcm⟩ := IsLocalization.surj
    (Algebra.algebraMapSubmonoid (integralClosure Γ(X, U) L) (nonZeroDivisors Γ(X, U))) y
  obtain ⟨tc, htc⟩ := hint c
  obtain ⟨tm, htm⟩ := hint m.1
  have : Algebra.IsIntegral ↑X.functionField
      Γ(pullback i.fromNormalization (X.fromSpecStalk (genericPoint ↥X)), ⊤) :=
    Algebra.IsIntegral.of_finite _ _
  have hfield : IsField
      Γ(pullback i.fromNormalization (X.fromSpecStalk (genericPoint ↥X)), ⊤) :=
    isField_of_isIntegral_of_isField' (Field.toIsField ↑X.functionField)
  have hinjA : Function.Injective (algebraMap Γ(X, U) L) := by
    rw [IsScalarTower.algebraMap_eq Γ(X, U) ↑X.functionField L]
    exact (algebraMap ↑X.functionField L).injective.comp
      (IsFractionRing.injective Γ(X, U) ↑X.functionField)
  have hm0 : ψ tm ≠ 0 := by
    obtain ⟨a, ha, hae⟩ := m.2
    have h8 : (algebraMap (integralClosure Γ(X, U) L) L) m.1 =
        algebraMap Γ(X, U) L a := by
      rw [show m.1 = algebraMap Γ(X, U) (integralClosure Γ(X, U) L) a from hae.symm,
        ← IsScalarTower.algebraMap_apply]
    rw [htm, h8]
    intro h0
    exact mem_nonZeroDivisors_iff_ne_zero.mp ha (hinjA (by simpa using h0))
  have htm0 : tm ≠ 0 := fun h0 ↦ hm0 (by rw [h0, map_zero])
  obtain ⟨b, hb⟩ := hfield.mul_inv_cancel htm0
  refine ⟨tc * b, ?_⟩
  have h5 : ψ tm * ψ b = 1 := by rw [← map_mul, hb, map_one]
  have h6 : ψ tc = y * ψ tm := by rw [htc, htm, ← hcm]
  calc ψ (tc * b) = ψ tc * ψ b := map_mul ψ tc b
    _ = y * (ψ tm * ψ b) := by rw [h6, mul_assoc]
    _ = y := by rw [h5, mul_one]

private theorem finrank_genericFiber
    (X : Scheme.{u}) [IsIntegral X] [IsNormal X]
    (L : Type u) [Field L] [Algebra X.functionField L]
    [FiniteDimensional X.functionField L]
    (i : Spec (.of L) ⟶ X)
    (hi : i = Spec.map (CommRingCat.ofHom
      (algebraMap X.functionField L)) ≫ X.fromSpecStalk (genericPoint X))
    [QuasiCompact i] [QuasiSeparated i]
    (g₀ : Spec (X.presheaf.stalk (genericPoint ↥X)) ⟶ X)
    (hg₀ : g₀ = X.fromSpecStalk (genericPoint ↥X))
    [IsFinite (pullback.snd i.fromNormalization g₀)]
    [Flat (pullback.snd i.fromNormalization g₀)]
    (z : ↥(Spec (X.presheaf.stalk (genericPoint ↥X)))) :
    (pullback.snd i.fromNormalization g₀).finrank z =
      Module.finrank X.functionField L := by
  subst hg₀
  exact (finrank_eq_finrank_sections (pullback.snd i.fromNormalization
    (X.fromSpecStalk (genericPoint ↥X))) z).trans
    (finrank_sections_genericFiber X L i hi)

/-- A jointly surjective family of étale morphisms is an fpqc covering. -/
private theorem ofArrows_mem_fpqcPrecoverage_of_etale
    {X : Scheme.{u}} {ι : Type u} {U : ι → Scheme.{u}} (g : ∀ i, U i ⟶ X)
    (hg : ∀ i, Etale (g i)) (hsurj : ∀ x : X, ∃ i, x ∈ Set.range (g i).base) :
    Presieve.ofArrows U g ∈ Scheme.fpqcPrecoverage X := by
  apply Scheme.fppfPrecoverage_le_fpqcPrecoverage
  change Presieve.ofArrows U g ∈
    Scheme.precoverage (@Flat.{u} ⊓ @LocallyOfFinitePresentation.{u}) X
  rw [Scheme.ofArrows_mem_precoverage_iff]
  refine ⟨hsurj, fun i ↦ ?_⟩
  have := hg i
  exact ⟨inferInstance, inferInstance⟩

/-- Being étale may be checked after an étale base change covering the target. -/
private theorem etale_of_etale_cover
    {Y X : Scheme.{u}} (f : Y ⟶ X) {ι : Type u} {U : ι → Scheme.{u}} (g : ∀ i, U i ⟶ X)
    (hg : ∀ i, Etale (g i)) (hsurj : ∀ x : X, ∃ i, x ∈ Set.range (g i).base)
    (h : ∀ i, Etale (pullback.snd f (g i))) :
    Etale f := by
  refine MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd
    (ofArrows_mem_fpqcPrecoverage_of_etale g hg hsurj) ?_
  rintro V g' _ ⟨i⟩
  exact h i

/-- The base change of the normalization along a smooth morphism is étale as soon as the
normalization of the base change is. -/
private theorem etale_pullback_fromNormalization
    {Z X U : Scheme.{u}} (f : Z ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    (g : U ⟶ X) [Smooth g]
    (h : Etale (pullback.snd f g).fromNormalization) :
    Etale (pullback.snd f.fromNormalization g) := by
  have : MorphismProperty.RespectsIso (@Etale.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  refine (MorphismProperty.cancel_left_of_respectsIso (P := @Etale.{u})
    (f.normalizationPullback g) (pullback.snd f.fromNormalization g)).mp ?_
  rw [Scheme.Hom.normalizationPullback_snd]
  exact h

/-- A morphism from an affine scheme whose image lies in an affine open `W` factors through the
open immersion `Spec Γ(Y, W) ⟶ Y` as `Spec` of a ring map. -/
private theorem eq_SpecMap_fromSpec {Y : Scheme.{u}} {W : Y.Opens} (hW : IsAffineOpen W)
    {A : CommRingCat.{u}} (f : Spec A ⟶ Y) (hf : f ⁻¹ᵁ W = ⊤) :
    f = Spec.map (f.appLE W ⊤ hf.ge ≫ (Scheme.ΓSpecIso A).hom) ≫ hW.fromSpec := by
  have key := hW.SpecMap_appLE_fromSpec f (isAffineOpen_top (Spec A)) hf.ge
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at key
  rw [Spec.map_comp, Category.assoc, key, ← Spec.map_comp_assoc, Iso.inv_hom_id,
    Spec.map_id, Category.id_comp]

/-- On a nonempty affine open `U` the canonical morphism `Spec L ⟶ X` through the generic point
is `Spec` of the algebra map `Γ(X, U) ⟶ L`, followed by the open immersion
`Spec Γ(X, U) ⟶ X`. -/
private theorem functionFieldMap_eq_SpecMap_fromSpec
    (X : Scheme.{u}) [IsIntegral X]
    (L : Type u) [Field L] [Algebra X.functionField L]
    (i : Spec (.of L) ⟶ X)
    (hi : i = Spec.map (CommRingCat.ofHom (algebraMap X.functionField L)) ≫
      X.fromSpecStalk (genericPoint X))
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI : Algebra Γ(X, U) L :=
      ((algebraMap X.functionField L).comp (X.germToFunctionField U).hom).toAlgebra
    i = Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) L)) ≫ hU.fromSpec := by
  let : Algebra Γ(X, U) L :=
    ((algebraMap X.functionField L).comp (X.germToFunctionField U).hom).toAlgebra
  have hx := functionFieldMap_closedPoint_mem X L i hi U
  have htop : i ⁻¹ᵁ U = ⊤ := Scheme.preimage_eq_top_of_closedPoint_mem i hx
  have hcomp := app_comp_functionFieldMap X L i hi U hx
  have hLE : i.appLE U ⊤ htop.ge ≫ (Scheme.ΓSpecIso (.of L)).hom =
      CommRingCat.ofHom (algebraMap Γ(X, U) L) := by
    rw [Scheme.Hom.appLE, Category.assoc]
    refine (?_ : _ = i.app U ≫ ((Spec (.of L)).presheaf.mapIso
        (eqToIso htop.symm).op ≪≫ Scheme.ΓSpecIso (.of L)).hom).trans (hcomp.trans ?_)
    · simp only [Iso.trans_hom, Functor.mapIso_hom]
      congr 2
    · rfl
  rw [eq_SpecMap_fromSpec hU i htop, hLE]

/-- Two morphisms from affine schemes into `Y` that both factor through one monomorphism
`Spec R ⟶ Y` have `Spec` of a tensor product over `R` as their fibre product. -/
private theorem isPullback_SpecMap_tensorProduct {Y : Scheme.{u}} {R A B : Type u}
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (j : Spec (.of R) ⟶ Y) [Mono j]
    {f : Spec (.of A) ⟶ Y} (hf : f = Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ j)
    {g : Spec (.of B) ⟶ Y} (hg : g = Spec.map (CommRingCat.ofHom (algebraMap R B)) ≫ j) :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight.toRingHom : A →+* B ⊗[R] A)))
      (Spec.map (CommRingCat.ofHom (algebraMap B (B ⊗[R] A))))
      f g := by
  have s := (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct R B A)).flip
  have t : IsPullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))
      (𝟙 (Spec (.of B))) j g :=
    IsPullback.of_vert_isIso_mono ⟨by rw [hg, Category.id_comp]⟩
  have := s.paste_vert t
  rwa [Category.comp_id, ← hf] at this

/-- Integrality is transported along a pair of compatible ring isomorphisms of the base and of
the algebra. -/
private theorem isIntegral_of_ringEquiv
    {SA SB A B : Type u} [CommRing SA] [CommRing SB] [CommRing A] [CommRing B]
    [Algebra SA SB] [Algebra A B] (d : SA ≃+* A) (e : SB ≃+* B)
    (hcomm : ∀ s : SA, e (algebraMap SA SB s) = algebraMap A B (d s)) (b : B) :
    _root_.IsIntegral SA (e.symm b) ↔ _root_.IsIntegral A b := by
  have h1 : ((e : SB →+* B).comp (algebraMap SA SB)) =
      (algebraMap A B).comp (d : SA →+* A) := by
    ext s
    simpa only [RingHom.comp_apply, RingEquiv.coe_toRingHom] using hcomm s
  have h2 : ((e.symm : B →+* SB).comp (algebraMap A B)) =
      (algebraMap SA SB).comp (d.symm : A →+* SA) := by
    ext a
    simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom]
    apply e.injective
    simp only [RingEquiv.apply_symm_apply, hcomm]
  constructor
  · intro hb
    have h3 : ((e : SB →+* B).comp (algebraMap SA SB)).IsIntegralElem (e (e.symm b)) :=
      RingHom.IsIntegralElem.map hb _
    rw [h1, RingEquiv.apply_symm_apply] at h3
    exact h3.of_comp
  · intro hb
    have h3 : ((e.symm : B →+* SB).comp (algebraMap A B)).IsIntegralElem (e.symm b) :=
      RingHom.IsIntegralElem.map hb _
    rw [h2] at h3
    exact h3.of_comp

/-- Étaleness of an integral closure is transported along a pair of compatible ring
isomorphisms of the base and of the algebra. -/
private theorem etale_integralClosure_of_ringEquiv
    {SA SB A B : Type u} [CommRing SA] [CommRing SB] [CommRing A] [CommRing B]
    [Algebra SA SB] [Algebra A B] (d : SA ≃+* A) (e : SB ≃+* B)
    (hcomm : ∀ s : SA, e (algebraMap SA SB s) = algebraMap A B (d s))
    (h : Algebra.Etale A (integralClosure A B)) :
    Algebra.Etale SA (integralClosure SA SB) := by
  have hmem := isIntegral_of_ringEquiv d e hcomm
  let ι : integralClosure A B ≃+* integralClosure SA SB :=
    { toFun c := ⟨e.symm c.1, (hmem c.1).mpr c.2⟩
      invFun c := ⟨e c.1, (hmem (e c.1)).mp (by
        rw [RingEquiv.symm_apply_apply]; exact c.2)⟩
      left_inv c := by ext; simp
      right_inv c := by ext; simp
      map_add' a b := by ext; simp
      map_mul' a b := by ext; simp }
  have hcomp : (algebraMap SA (integralClosure SA SB)) =
      ((ι : integralClosure A B →+* integralClosure SA SB).comp
        (algebraMap A (integralClosure A B))).comp (d : SA →+* A) := by
    ext s
    change algebraMap SA SB s = e.symm (algebraMap A B (d s))
    rw [← hcomm s, RingEquiv.symm_apply_apply]
  rw [← RingHom.etale_algebraMap, hcomp]
  exact RingHom.Etale.respectsIso.right _ d
    (RingHom.Etale.respectsIso.left _ ι (RingHom.etale_algebraMap.mpr h))

/-- Over an affine base the relative normalization is étale as soon as the integral closure of
the global sections of the base in the global sections of the source is étale. -/
private theorem etale_fromNormalization_of_isAffine
    {Z U : Scheme.{u}} (f : Z ⟶ U) [QuasiCompact f] [QuasiSeparated f] [IsAffine U]
    (h : letI := f.appTop.hom.toAlgebra
      Algebra.Etale Γ(U, ⊤) (integralClosure Γ(U, ⊤) Γ(Z, ⊤))) :
    Etale f.fromNormalization := by
  let := f.appTop.hom.toAlgebra
  have : IsAffine f.normalization :=
    isAffine_of_isAffineHom f.fromNormalization
  rw [HasRingHomProperty.iff_of_isAffine (P := @Etale.{u})]
  have key : RingHom.Etale (CommRingCat.Hom.hom (f.fromNormalization.app ⊤)) := by
    rw [f.fromNormalization_app (isAffineOpen_top U), CommRingCat.hom_comp]
    exact RingHom.Etale.respectsIso.left _
      (f.normalizationObjIso (isAffineOpen_top U)).symm.commRingCatIsoToRingEquiv
      (RingHom.etale_algebraMap.mpr h)
  exact key

/-- An étale algebra `R'` over the coordinate ring of an affine chart `Spec R ⟶ Y` through which
`i` factors gives an étale neighbourhood of any point in the image of `Spec R'`, over which the
relative normalization in `Spec L` is étale. -/
private theorem exists_etale_of_etale_algebra
    {Y : Scheme.{u}} {R : CommRingCat.{u}} {L : Type u} [CommRing L]
    (j : Spec R ⟶ Y) (hj : IsOpenImmersion j) [Algebra R L]
    (i : Spec (.of L) ⟶ Y) [QuasiCompact i] [QuasiSeparated i]
    (hfac : i = Spec.map (CommRingCat.ofHom (algebraMap R L)) ≫ j)
    (R' : Type u) [CommRing R'] [Algebra R R'] [Algebra.Etale R R']
    (hcl : Algebra.Etale R' (integralClosure R' (R' ⊗[R] L)))
    (y : Y) (z : Spec (.of R'))
    (hyz : (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ j).base z = y) :
    ∃ (U : Scheme.{u}) (g : U ⟶ Y), Etale g ∧ y ∈ Set.range g.base ∧
      Etale (pullback.snd i g).fromNormalization := by
  have := hj
  have hEt : Etale (Spec.map (CommRingCat.ofHom (algebraMap R R'))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr ‹_›)
  set g := Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ j with hg
  refine ⟨Spec (.of R'), g, inferInstance, ⟨z, hyz⟩, ?_⟩
  have hIP := isPullback_SpecMap_tensorProduct j hfac (g := g) hg
  let θ := hIP.isoPullback
  have hiso : IsIso θ.hom.appTop :=
    ⟨θ.inv.appTop, by rw [← Scheme.Hom.comp_appTop, θ.inv_hom_id, Scheme.Hom.id_appTop],
      by rw [← Scheme.Hom.comp_appTop, θ.hom_inv_id, Scheme.Hom.id_appTop]⟩
  let := (pullback.snd i g).appTop.hom.toAlgebra
  refine etale_fromNormalization_of_isAffine (pullback.snd i g) ?_
  refine etale_integralClosure_of_ringEquiv
    (Scheme.ΓSpecIso (.of R')).commRingCatIsoToRingEquiv
    (asIso θ.hom.appTop ≪≫ Scheme.ΓSpecIso (.of (R' ⊗[R] L))).commRingCatIsoToRingEquiv
    ?_ hcl
  have hnat : (pullback.snd i g).appTop ≫ θ.hom.appTop ≫
      (Scheme.ΓSpecIso (.of (R' ⊗[R] L))).hom =
      (Scheme.ΓSpecIso (.of R')).hom ≫ CommRingCat.ofHom (algebraMap R' (R' ⊗[R] L)) := by
    rw [← Category.assoc, ← Scheme.Hom.comp_appTop, hIP.isoPullback_hom_snd,
      Scheme.ΓSpecIso_naturality]
  intro s
  exact ConcreteCategory.congr_hom hnat s

/-- The coordinate ring of a nonempty affine open of a normal scheme is integrally closed. -/
private theorem isIntegrallyClosed_sections (X : Scheme.{u}) [IsIntegral X]
    [IsNormal X] (W : X.Opens) (hW : IsAffineOpen W) [Nonempty W] :
    IsIntegrallyClosed Γ(X, W) := by
  have hdom : IsDomain Γ(X, W) := inferInstance
  refine IsIntegrallyClosed.of_localization_maximal fun p hp hpm => ?_
  have hyp : p.IsPrime := hpm.isPrime
  have hy : hW.fromSpec ⟨p, hyp⟩ ∈ W :=
    hW.range_fromSpec.subset (Set.mem_range_self (⟨p, hyp⟩ : PrimeSpectrum Γ(X, W)))
  let : Algebra Γ(X, W) (X.presheaf.stalk (hW.fromSpec ⟨p, hyp⟩)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hW.fromSpec ⟨p, hyp⟩, hy⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk (hW.fromSpec ⟨p, hyp⟩)) p :=
    hW.isLocalization_stalk' ⟨p, hyp⟩ hy
  have : IsIntegrallyClosed (X.presheaf.stalk (hW.fromSpec ⟨p, hyp⟩)) :=
    IsNormal.stalk_normal _
  exact IsIntegrallyClosed.of_equiv
    (IsLocalization.algEquiv p.primeCompl
      (X.presheaf.stalk (hW.fromSpec ⟨p, hyp⟩)) (Localization.AtPrime p)).toRingEquiv

/-- A ring embedding into a Noetherian ring forces finitely many minimal primes. -/
private lemma finite_minimalPrimes_of_injective
    {A B : Type u} [CommRing A] [CommRing B] [IsNoetherianRing B]
    (f : A →+* B) (hf : Function.Injective f) : (minimalPrimes A).Finite := by
  have hk : Ideal.comap f ⊥ = ⊥ := (RingHom.injective_iff_ker_eq_bot f).mp hf
  have h := Ideal.minimalPrimes_comap_subset f (⊥ : Ideal B)
  rw [hk] at h
  exact ((minimalPrimes.finite_of_isNoetherianRing B).image (Ideal.comap f)).subset h

/-- A flat algebra of finite type over a domain has finitely many minimal primes. -/
private lemma finite_minimalPrimes_of_flat_finiteType
    (A C : Type u) [CommRing A] [CommRing C] [IsDomain A]
    [Algebra A C] [Module.Flat A C] [Algebra.FiniteType A C] :
    (minimalPrimes C).Finite := by
  have : Algebra.FiniteType (FractionRing A) (FractionRing A ⊗[A] C) :=
    Algebra.FiniteType.baseChange (FractionRing A)
  have : IsNoetherianRing (FractionRing A ⊗[A] C) :=
    Algebra.FiniteType.isNoetherianRing (FractionRing A) _
  exact finite_minimalPrimes_of_injective
    (Algebra.TensorProduct.includeRight : C →ₐ[A] FractionRing A ⊗[A] C).toRingHom
    (Algebra.TensorProduct.includeRight_injective
      (IsFractionRing.injective A (FractionRing A)))

/-- **Shrinking an étale algebra over a normal domain to a normal integral factor.** For an
étale algebra `R'` over a normal domain and a prime `p'` of `R'`, there is an idempotent `ε ∉ p'`
of `R'` such that the localization of `R'` away from `ε` is an integrally closed domain. -/
private theorem exists_isIdempotentElem_notMem_normal_away
    (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (R' : Type u) [CommRing R'] [Algebra R R'] [Algebra.Etale R R']
    (p' : Ideal R') [hp' : p'.IsPrime] :
    ∃ ε : R', ε ∉ p' ∧ IsIdempotentElem ε ∧
      IsDomain (Localization.Away ε) ∧ IsIntegrallyClosed (Localization.Away ε) := by
  classical
  have hnormal : IsNormalRing R' := IsNormalRing.of_etale_of_isDomain R R'
  have hred : _root_.IsReduced R' := hnormal.isReduced
  have hfin : (minimalPrimes R').Finite := finite_minimalPrimes_of_flat_finiteType R R'
  obtain ⟨n, A, hcr, hdom, hic, ⟨e⟩⟩ :=
    ((isIntegrallyClosed_tfae_of_finite_minimalPrimes hfin).out 1 3).mp hnormal
  let _inst := hcr
  have hone : (∑ i : Fin n, (Pi.single i 1 : ∀ j, A j)) = 1 := by
    simpa using Finset.univ_sum_single (1 : ∀ j, A j)
  have hsum : ∑ i : Fin n, e.symm (Pi.single i 1) = 1 := by
    rw [← map_sum, hone, map_one]
  have hex : ∃ k : Fin n, e.symm (Pi.single k 1) ∉ p' := by
    by_contra hc
    exact hp'.ne_top ((Ideal.eq_top_iff_one p').mpr
      (hsum ▸ Ideal.sum_mem _ fun i _ => not_not.mp fun h => hc ⟨i, h⟩))
  obtain ⟨k, hk⟩ := hex
  have hidem : IsIdempotentElem (e.symm (Pi.single k 1)) := by
    have : (Pi.single k 1 : ∀ i, A i) * Pi.single k 1 = Pi.single k 1 := by
      funext i
      by_cases h : i = k
      · subst h; simp
      · simp [h]
    rw [IsIdempotentElem, ← map_mul, this]
  let : Algebra R' (A k) := ((Pi.evalRingHom A k).comp (e : R' →+* ∀ i, A i)).toAlgebra
  have hsurj : Function.Surjective (algebraMap R' (A k)) :=
    (Function.surjective_eval k).comp e.surjective
  have hker : RingHom.ker (algebraMap R' (A k)) = Ideal.span {1 - e.symm (Pi.single k 1)} := by
    apply le_antisymm
    · intro x hx
      rw [RingHom.mem_ker] at hx
      refine Ideal.mem_span_singleton'.mpr ⟨x, ?_⟩
      apply e.injective
      rw [map_mul, map_sub, map_one, RingEquiv.apply_symm_apply]
      funext i
      by_cases h : i = k
      · subst h
        simp only [Pi.mul_apply, Pi.sub_apply, Pi.one_apply, Pi.single_eq_same, sub_self,
          mul_zero]
        exact hx.symm
      · simp [h]
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
      change (e (1 - e.symm (Pi.single k 1))) k = 0
      rw [map_sub, map_one, RingEquiv.apply_symm_apply]
      simp
  have : IsLocalization.Away (e.symm (Pi.single k 1)) (A k) :=
    IsLocalization.away_of_isIdempotentElem hidem hker hsurj
  let φ : Localization.Away (e.symm (Pi.single k 1)) ≃ₐ[R'] A k :=
    IsLocalization.algEquiv (Submonoid.powers (e.symm (Pi.single k 1))) _ _
  have hd : IsDomain (A k) := hdom k
  have hi : IsIntegrallyClosed (A k) := hic k
  exact ⟨_, hk, hidem,
    Function.Injective.isDomain (φ : Localization.Away _ →+* A k) φ.injective,
    IsIntegrallyClosed.of_equiv (φ.toRingEquiv.symm)⟩

/-- Nonzero complete orthogonal idempotents in an algebra over a field are linearly
independent. -/
private lemma linearIndependent_completeOrthogonalIdempotents
    {F V : Type u} [Field F] [CommRing V] [Algebra F V] {n : ℕ} {e : Fin n → V}
    (he : CompleteOrthogonalIdempotents e) (he0 : ∀ i, e i ≠ 0) :
    LinearIndependent F e := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have hmul : (∑ i, g i • e i) * e j = g j • e j := by
    rw [Finset.sum_mul, Finset.sum_eq_single j]
    · rw [smul_mul_assoc, (he.idem j)]
    · intro i _ hij
      rw [smul_mul_assoc, he.ortho hij, smul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  rw [hg, zero_mul] at hmul
  by_contra hgj
  refine he0 j ?_
  have := congrArg (fun v => (g j)⁻¹ • v) hmul.symm
  simpa [smul_smul, inv_mul_cancel₀ hgj] using this

/-- Two linear combinations of complete orthogonal idempotents multiply coefficientwise. -/
private lemma sum_smul_mul_sum_smul
    {F V : Type u} [Field F] [CommRing V] [Algebra F V] {n : ℕ} {e : Fin n → V}
    (he : CompleteOrthogonalIdempotents e) (c d : Fin n → F) :
    (∑ i, c i • e i) * (∑ i, d i • e i) = ∑ i, (c i * d i) • e i := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [smul_mul_smul_comm, he.idem i]
  · intro j _ hji
    rw [smul_mul_smul_comm, he.ortho (Ne.symm hji), smul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- A finite-dimensional algebra over a field carrying as many nonzero complete orthogonal
idempotents as its dimension is the product of that many copies of the field. -/
private noncomputable def piEquivOfCompleteOrthogonalIdempotents
    {F V : Type u} [Field F] [CommRing V] [Algebra F V] [Module.Finite F V]
    {n : ℕ} {e : Fin n → V}
    (he : CompleteOrthogonalIdempotents e) (he0 : ∀ i, e i ≠ 0)
    (hdim : Module.finrank F V = n) :
    (Fin n → F) ≃ₐ[F] V := by
  have hli : LinearIndependent F e := linearIndependent_completeOrthogonalIdempotents he he0
  haveI : FiniteDimensional F V := ‹Module.Finite F V›
  have hcard : Fintype.card (Fin n) = Module.finrank F V := by simp [hdim]
  let b := basisOfLinearIndependentOfCardEqFinrank' (K := F) e hli hcard
  have hb : ⇑b = e := coe_basisOfLinearIndependentOfCardEqFinrank' (K := F) e hli hcard
  refine AlgEquiv.ofLinearEquiv b.equivFun.symm ?_ ?_
  · rw [b.equivFun_symm_apply]
    simpa [hb] using he.complete
  · intro c d
    rw [b.equivFun_symm_apply, b.equivFun_symm_apply, b.equivFun_symm_apply, hb]
    exact (sum_smul_mul_sum_smul he c d).symm

/-- The integral closure of a normal domain in a finite product of copies of its fraction field is
the product of the same number of copies of the domain. -/
private noncomputable def integralClosureFinPiEquiv
    (R F : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field F]
    [Algebra R F] [IsFractionRing R F] (n : ℕ) :
    (Fin n → R) ≃ₐ[R] integralClosure R (Fin n → F) := by
  classical
  let ψ : (Fin n → R) →ₐ[R] (Fin n → F) := AlgHom.pi fun i =>
    (Algebra.ofId R F).comp (Pi.evalAlgHom R (fun _ : Fin n => R) i)
  have hinj : Function.Injective ψ := by
    intro a b hab
    funext i
    exact IsFractionRing.injective R F (congrFun hab i)
  have hrange : ψ.range = integralClosure R (Fin n → F) := by
    apply le_antisymm
    · rintro _ ⟨c, rfl⟩
      have : Algebra.IsIntegral R (Fin n → R) := Algebra.IsIntegral.of_finite R _
      exact IsIntegral.map ψ (Algebra.IsIntegral.isIntegral c)
    · intro v hv
      have hc : ∀ i, ∃ r : R, algebraMap R F r = v i := fun i =>
        (IsIntegrallyClosed.isIntegral_iff).mp
          (IsIntegral.map (Pi.evalAlgHom R (fun _ : Fin n => F) i) hv)
      choose r hr using hc
      exact ⟨r, by funext i; exact hr i⟩
  exact (AlgEquiv.ofInjective ψ hinj).trans (Subalgebra.equivOfEq _ _ hrange)

/-- A product of copies of the fraction field of a normal domain is étale over the domain, after
passing to the integral closure. -/
private theorem etale_integralClosure_pi
    (R F : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field F]
    [Algebra R F] [IsFractionRing R F] (n : ℕ) :
    Algebra.Etale R (integralClosure R (Fin n → F)) :=
  Algebra.Etale.of_equiv (integralClosureFinPiEquiv R F n)

/-- Over a normal domain `R'` with fraction field `F`, the integral closure of `R'` in an
`F`-algebra `V` of dimension `n` carrying `n` nonzero complete orthogonal idempotents is étale
over `R'`. -/
private theorem etale_integralClosure_of_idempotents
    {R' F V : Type u} [CommRing R'] [IsDomain R'] [IsIntegrallyClosed R']
    [Field F] [Algebra R' F] [IsFractionRing R' F]
    [CommRing V] [Algebra F V] [Algebra R' V] [IsScalarTower R' F V]
    {n : ℕ} {e : Fin n → V} [Module.Finite F V]
    (he : CompleteOrthogonalIdempotents e) (he0 : ∀ i, e i ≠ 0)
    (hdim : Module.finrank F V = n) :
    Algebra.Etale R' (integralClosure R' V) := by
  have : Algebra.Etale R' (integralClosure R' (Fin n → F)) := etale_integralClosure_pi R' F n
  exact Algebra.Etale.of_equiv
    ((piEquivOfCompleteOrthogonalIdempotents he he0 hdim).restrictScalars R').mapIntegralClosure

/-- A module spanned by finitely many elements over a nontrivial commutative ring is finite, of
rank at most their number. -/
private lemma finite_and_finrank_le_of_span_range
    {F V : Type u} [CommRing F] [Nontrivial F] [AddCommGroup V] [Module F V]
    {m : ℕ} (v : Fin m → V) (hspan : Submodule.span F (Set.range v) = ⊤) :
    Module.Finite F V ∧ Module.finrank F V ≤ m := by
  refine ⟨⟨by rw [← hspan]; exact Submodule.fg_span (Set.finite_range _)⟩, ?_⟩
  simpa using finrank_le_of_span_eq_top (R := F) (v := v) hspan

/-- **The fraction field of an étale algebra over a normal domain is a base change.** The base
change of the fraction field of `R` along an étale `R`-algebra `R'` is the total ring of fractions
of `R'`. -/
private theorem isFractionRing_tensorProduct_fractionField
    (R K R' : Type u) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing R'] [Algebra R R'] [Algebra.Etale R R'] :
    IsFractionRing R' (R' ⊗[R] K) := by
  have : Module.Finite K (K ⊗[R] R') := Algebra.FormallyUnramified.finite_of_free K _
  have : IsArtinianRing (K ⊗[R] R') := IsArtinianRing.of_finite K _
  have hart : IsArtinianRing (R' ⊗[R] K) :=
    (Algebra.TensorProduct.comm R R' K).toRingEquiv.symm.isArtinianRing
  have hM : Algebra.algebraMapSubmonoid R' (nonZeroDivisors R) ≤ nonZeroDivisors R' := by
    rintro _ ⟨d, hd, rfl⟩
    rw [mem_nonZeroDivisors_iff_right]
    intro y hy
    rw [mul_comm, ← Algebra.smul_def] at hy
    exact (smul_eq_zero.mp hy).resolve_left (mem_nonZeroDivisors_iff_ne_zero.mp hd)
  refine IsLocalization.of_le _ _ hM fun r hr ↦ ?_
  have h1 := IsLocalization.map_nonZeroDivisors_le
    (Algebra.algebraMapSubmonoid R' (nonZeroDivisors R))
    (S := R' ⊗[R] K) (Submonoid.mem_map_of_mem _ hr)
  exact IsArtinianRing.isUnit_of_mem_nonZeroDivisors h1

/-- Base change along a flat algebra preserves injectivity. -/
@[sga "3 VIB 11.7" "special case"]
private lemma injective_tensorProduct_map
    {R R' A B : Type u} [CommRing R] [CommRing R'] [CommRing A] [CommRing B]
    [Algebra R R'] [Algebra R A] [Algebra R B] [Module.Flat R R']
    (f : A →ₐ[R] B) (hf : Function.Injective f) :
    Function.Injective (Algebra.TensorProduct.map (AlgHom.id R R') f) := by
  have h : ∀ z : R' ⊗[R] A, Algebra.TensorProduct.map (AlgHom.id R R') f z =
      LinearMap.lTensor R' f.toLinearMap z := by
    intro z
    induction z with
    | tmul a b => simp
    | add x y hx hy => simp [map_add, hx, hy]
  have hl : Function.Injective (LinearMap.lTensor R' f.toLinearMap) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := R') f.toLinearMap hf
  intro x y hxy
  exact hl (by rw [← h, ← h, hxy])

/-- The dimension of a finite algebra over a field is the sum of the dimensions of the factors
cut out by a family of complete orthogonal idempotents. -/
private lemma finrank_eq_sum_of_completeOrthogonalIdempotents
    {k B : Type u} [Field k] [CommRing B] [Algebra k B] [Module.Finite k B]
    {n : ℕ} {e : Fin n → B} (he : CompleteOrthogonalIdempotents e) :
    Module.finrank k B = ∑ i, Module.finrank k (B ⧸ Ideal.span {(1 : B) - e i}) := by
  classical
  have hb : Function.Bijective
      (AlgHom.pi fun i => Ideal.Quotient.mkₐ k (Ideal.span {(1 : B) - e i})) := he.bijective_pi
  rw [(AlgEquiv.ofBijective
    (AlgHom.pi fun i => Ideal.Quotient.mkₐ k (Ideal.span {(1 : B) - e i}))
    hb).toLinearEquiv.finrank_eq]
  exact Module.finrank_pi_fintype k

section Ring0BTF

attribute [local instance] Localization.AtPrime.algebraOfLiesOver

/-- An étale algebra over a field whose residue field at a maximal ideal is purely inseparable
over the base is already the base there. -/
private lemma finrank_quotient_eq_one_of_purelyInseparable
    {k B : Type u} [Field k] [CommRing B] [Algebra k B] [Algebra.Etale k B]
    (m : Ideal B) [m.IsMaximal]
    (hpi : letI := Ideal.Quotient.field m; IsPurelyInseparable k (B ⧸ m)) :
    Module.finrank k (B ⧸ m) = 1 := by
  have hfin : Module.Finite k B := Algebra.FormallyUnramified.finite_of_free k B
  have hred : _root_.IsReduced B := Algebra.FormallyUnramified.isReduced_of_field k B
  have hart : IsArtinianRing B := IsArtinianRing.of_finite k B
  let _ := Ideal.Quotient.field m
  have : Algebra.IsSeparable k (B ⧸ m) := inferInstance
  have := hpi
  have hbij : Function.Bijective (algebraMap k (B ⧸ m)) :=
    IsPurelyInseparable.bijective_algebraMap_of_isSeparable k (B ⧸ m)
  have := (AlgEquiv.ofBijective (Algebra.ofId k (B ⧸ m)) hbij).toLinearEquiv.finrank_eq
  simpa using this.symm

/-- If every residue field of an étale algebra over a field is the base field, its dimension is
bounded by any number into which the maximal spectrum injects. -/
private lemma finrank_le_of_etale_of_injective
    {k B : Type u} [Field k] [CommRing B] [Algebra k B] [Algebra.Etale k B] {n : ℕ}
    (hone : ∀ m : MaximalSpectrum B, Module.finrank k (B ⧸ m.asIdeal) = 1)
    (f : MaximalSpectrum B → Fin n) (hf : Function.Injective f) :
    Module.finrank k B ≤ n := by
  classical
  have hfin : Module.Finite k B := Algebra.FormallyUnramified.finite_of_free k B
  have hred : _root_.IsReduced B := Algebra.FormallyUnramified.isReduced_of_field k B
  have hart : IsArtinianRing B := IsArtinianRing.of_finite k B
  let _ : Fintype (MaximalSpectrum B) := Fintype.ofFinite _
  have hfe : Module.finrank k B =
      ∑ m : MaximalSpectrum B, Module.finrank k (B ⧸ m.asIdeal) := by
    rw [((IsArtinianRing.equivPi B).restrictScalars k).toLinearEquiv.finrank_eq]
    exact Module.finrank_pi_fintype k
  rw [hfe]
  calc ∑ m : MaximalSpectrum B, Module.finrank k (B ⧸ m.asIdeal)
      = ∑ _m : MaximalSpectrum B, 1 := Finset.sum_congr rfl fun m _ => hone m
    _ = Fintype.card (MaximalSpectrum B) := by simp
    _ ≤ n := by simpa using Fintype.card_le_of_injective f hf

/-- An étale algebra over a field with at most one maximal ideal, whose residue field there is
purely inseparable over the base, has dimension at most one. -/
private lemma finrank_le_one_of_etale_of_subsingleton
    {k B : Type u} [Field k] [CommRing B] [Algebra k B] [Algebra.Etale k B]
    (hsub : Subsingleton (MaximalSpectrum B))
    (hpi : ∀ m : MaximalSpectrum B,
      letI := Ideal.Quotient.field m.asIdeal
      IsPurelyInseparable k (B ⧸ m.asIdeal)) :
    Module.finrank k B ≤ 1 :=
  finrank_le_of_etale_of_injective
    (fun m => finrank_quotient_eq_one_of_purelyInseparable m.asIdeal (hpi m))
    (fun _ => 0) fun _ _ _ => Subsingleton.elim _ _

/-- The canonical `κ(p)`-algebra map from the fibre of `p` in `A` to the residue field of a prime
of an `A`-algebra lying over `p`. -/
private def fiberToResidueOver {R T : Type u} (A : Type u) [CommRing R] [CommRing A]
    [CommRing T] [Algebra R A] [Algebra A T] [Algebra R T] [IsScalarTower R A T]
    (p : Ideal R) [p.IsPrime] (w : Ideal T) [w.IsPrime] [w.LiesOver p] :
    p.Fiber A →ₐ[p.ResidueField] w.ResidueField :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _)
    ((IsScalarTower.toAlgHom R T w.ResidueField).comp (IsScalarTower.toAlgHom R A T))
    fun _ _ ↦ .all _ _

/-- A prime of the fibre of `p` is determined by the prime of `A` it contracts to. -/
private lemma fiber_prime_eq_of_comap_eq {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (p : Ideal R) [p.IsPrime] (m₁ m₂ : Ideal (p.Fiber A)) [m₁.IsPrime] [m₂.IsPrime]
    (h : m₁.comap (Algebra.TensorProduct.includeRight : A →ₐ[R] p.Fiber A).toRingHom =
      m₂.comap (Algebra.TensorProduct.includeRight : A →ₐ[R] p.Fiber A).toRingHom) :
    m₁ = m₂ :=
  congrArg PrimeSpectrum.asIdeal
    ((PrimeSpectrum.primesOverOrderIsoFiber R A p).symm.injective
      (a₁ := ⟨m₁, inferInstance⟩) (a₂ := ⟨m₂, inferInstance⟩) (Subtype.ext (by
        rw [PrimeSpectrum.coe_primesOverOrderIsoFiber_symm_apply,
          PrimeSpectrum.coe_primesOverOrderIsoFiber_symm_apply]
        exact h)))

/-- The prime of `A` under a prime of the fibre of `p`, together with its two properties. -/
private lemma exists_primesOver_comap {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (p : Ideal R) [p.IsPrime] (m : Ideal (p.Fiber A)) [m.IsPrime] :
    ∃ (q : Ideal A) (_ : q.IsPrime) (_ : q.LiesOver p),
      q = m.comap (Algebra.TensorProduct.includeRight : A →ₐ[R] p.Fiber A).toRingHom :=
  ⟨((PrimeSpectrum.primesOverOrderIsoFiber R A p).symm ⟨m, inferInstance⟩ : Ideal A),
    ((PrimeSpectrum.primesOverOrderIsoFiber R A p).symm ⟨m, inferInstance⟩).2.1,
    ((PrimeSpectrum.primesOverOrderIsoFiber R A p).symm ⟨m, inferInstance⟩).2.2,
    PrimeSpectrum.coe_primesOverOrderIsoFiber_symm_apply ..⟩

/-- Let `m` be a maximal ideal of the fibre `κ(p) ⊗ A` and `w` a prime of an `A`-algebra
contracting to the same prime of `A` as `m`. If `κ(w)` is purely inseparable over `κ(p)`, so is
the residue field of the fibre at `m`. -/
private lemma isPurelyInseparable_fiber_quotient {R A T : Type u} [CommRing R] [CommRing A]
    [CommRing T] [Algebra R A] [Algebra A T] [Algebra R T] [IsScalarTower R A T]
    (p : Ideal R) [p.IsPrime] (m : Ideal (p.Fiber A)) [m.IsMaximal]
    (w : Ideal T) [w.IsPrime] [w.LiesOver p]
    (hw : w.comap (algebraMap A T) =
      m.comap (Algebra.TensorProduct.includeRight : A →ₐ[R] p.Fiber A).toRingHom)
    (hpi : IsPurelyInseparable p.ResidueField w.ResidueField) :
    letI := Ideal.Quotient.field m
    IsPurelyInseparable p.ResidueField (p.Fiber A ⧸ m) := by
  let _ := Ideal.Quotient.field m
  have hp1 : (RingHom.ker (fiberToResidueOver A p w).toRingHom).IsPrime := RingHom.ker_isPrime _
  have hcomap : (RingHom.ker (fiberToResidueOver A p w).toRingHom).comap
      (Algebra.TensorProduct.includeRight : A →ₐ[R] p.Fiber A).toRingHom =
      w.comap (algebraMap A T) := by
    ext a
    simp [RingHom.mem_ker, fiberToResidueOver]
  have hker : RingHom.ker (fiberToResidueOver A p w).toRingHom = m :=
    fiber_prime_eq_of_comap_eq p _ _ (hcomap.trans hw)
  have hle : ∀ a ∈ m, (fiberToResidueOver A p w) a = 0 := fun a ha => by
    have hmem : a ∈ RingHom.ker (fiberToResidueOver A p w).toRingHom := hker.ge ha
    simpa [RingHom.mem_ker] using hmem
  let χ : (p.Fiber A ⧸ m) →ₐ[p.ResidueField] w.ResidueField :=
    Ideal.Quotient.liftₐ m (fiberToResidueOver A p w) hle
  let _ := χ.toRingHom.toAlgebra
  have : IsScalarTower p.ResidueField (p.Fiber A ⧸ m) w.ResidueField :=
    IsScalarTower.of_algebraMap_eq' χ.comp_algebraMap.symm
  have := hpi
  exact IsPurelyInseparable.tower_bot p.ResidueField (p.Fiber A ⧸ m) w.ResidueField

/-- One of a family of complete orthogonal idempotents avoids any given prime. -/
private lemma exists_notMem_of_completeOrthogonalIdempotents {A : Type u} [CommRing A]
    {n : ℕ} {e : Fin n → A} (he : CompleteOrthogonalIdempotents e)
    (q : Ideal A) [hq : q.IsPrime] : ∃ i, e i ∉ q := by
  by_contra hc
  simp only [not_exists, not_not] at hc
  exact hq.ne_top ((Ideal.eq_top_iff_one q).mpr
    (he.complete ▸ Ideal.sum_mem _ fun i _ => hc i))

/-- A prime of `A` above `p'` avoiding `a` is the contraction of the unique prime above `p'` of the
localization of `A` away from `a`. -/
private lemma eq_under_of_notMem {R' A : Type u} [CommRing R'] [CommRing A] [Algebra R' A]
    (p' : Ideal R') [p'.IsPrime] (a : A) (r : Ideal (Localization.Away a))
    (huniq : ∀ Q : Ideal (Localization.Away a), Q.IsPrime → Q.LiesOver p' → Q = r)
    (q : Ideal A) [q.IsPrime] [q.LiesOver p'] (ha : a ∉ q) :
    q = Ideal.under A r := by
  have hdisj : Disjoint ((Submonoid.powers a : Submonoid A) : Set A) (q : Set A) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime a).mpr ha
  have hpm : (q.map (algebraMap A (Localization.Away a))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers a) _ q ‹_› hdisj
  have h1 : (q.map (algebraMap A (Localization.Away a))).LiesOver q :=
    IsLocalization.liesOver_map_of_isPrime_disjoint (Submonoid.powers a) _ hdisj
  have h2 : (q.map (algebraMap A (Localization.Away a))).LiesOver p' := .trans _ q _
  have h3 := IsLocalization.under_map_of_isPrime_disjoint (M := Submonoid.powers a)
    (S := Localization.Away a) ‹q.IsPrime› hdisj
  rw [← h3, huniq _ hpm h2]

/-- If the fibre of `p'` in `A` is étale over `κ(p')`, and `A` is cut by `n` complete orthogonal
idempotents whose localizations each carry a unique prime above `p'` with purely inseparable
residue extension, then the fibre has dimension at most `n`. -/
private lemma finrank_fiber_le_of_completeOrthogonalIdempotents
    {R' A : Type u} [CommRing R'] [CommRing A] [Algebra R' A] (p' : Ideal R') [p'.IsPrime]
    [Algebra.Etale p'.ResidueField (p'.Fiber A)]
    {n : ℕ} {e : Fin n → A} (he : CompleteOrthogonalIdempotents e)
    (r : (i : Fin n) → Ideal (Localization.Away (e i)))
    (hrp : ∀ i, (r i).IsPrime) (hro : ∀ i, (r i).LiesOver p')
    (huniq : ∀ (i : Fin n) (Q : Ideal (Localization.Away (e i))), Q.IsPrime → Q.LiesOver p' →
      Q = r i)
    (hpi : ∀ i, letI := hrp i; letI := hro i;
      IsPurelyInseparable p'.ResidueField (r i).ResidueField) :
    Module.finrank p'.ResidueField (p'.Fiber A) ≤ n := by
  classical
  have hbar : CompleteOrthogonalIdempotents
      (fun i => (Algebra.TensorProduct.includeRight : A →ₐ[R'] p'.Fiber A) (e i)) := he.map _
  have hex : ∀ m : MaximalSpectrum (p'.Fiber A), ∃ i,
      (Algebra.TensorProduct.includeRight : A →ₐ[R'] p'.Fiber A) (e i) ∉ m.asIdeal :=
    fun m => exists_notMem_of_completeOrthogonalIdempotents hbar m.asIdeal
  choose f hf using hex
  refine finrank_le_of_etale_of_injective (fun m => ?_) f (fun m₁ m₂ h => ?_)
  · obtain ⟨q, hq1, hq2, hqe⟩ := exists_primesOver_comap p' m.asIdeal
    have := hq1
    have := hq2
    have := hrp (f m)
    have := hro (f m)
    have hne : e (f m) ∉ q := by rw [hqe]; simpa [Ideal.mem_comap] using hf m
    have hunder : q = Ideal.under A (r (f m)) :=
      eq_under_of_notMem p' _ (r (f m)) (huniq (f m)) q hne
    exact finrank_quotient_eq_one_of_purelyInseparable m.asIdeal
      (isPurelyInseparable_fiber_quotient p' m.asIdeal (r (f m))
        (hunder.symm.trans hqe) (hpi (f m)))
  · have h1 := hf m₁
    have h2 := hf m₂
    rw [h] at h1
    obtain ⟨q₁, hq11, hq12, hqe1⟩ := exists_primesOver_comap p' m₁.asIdeal
    obtain ⟨q₂, hq21, hq22, hqe2⟩ := exists_primesOver_comap p' m₂.asIdeal
    have := hq11
    have := hq12
    have := hq21
    have := hq22
    have hne1 : e (f m₂) ∉ q₁ := by rw [hqe1]; simpa [Ideal.mem_comap] using h1
    have hne2 : e (f m₂) ∉ q₂ := by rw [hqe2]; simpa [Ideal.mem_comap] using h2
    have hqq : q₁ = q₂ := by
      rw [eq_under_of_notMem p' _ (r _) (huniq _) q₁ hne1,
        eq_under_of_notMem p' _ (r _) (huniq _) q₂ hne2]
    exact MaximalSpectrum.ext (fiber_prime_eq_of_comap_eq p' _ _ (by rw [← hqe1, ← hqe2, hqq]))

/-- **Étale fibres are stable under an étale neighbourhood.** If the fibre of `p` in `S` is étale
over `κ(p)`, then for any prime `p'` of an `R`-algebra `R'` lying over `p` the fibre of `p'` in
`R' ⊗[R] S` is étale over `κ(p')`. -/
private lemma etale_fiber_tensorProduct
    {R S R' : Type u} [CommRing R] [CommRing S] [Algebra R S] [CommRing R'] [Algebra R R']
    (p : Ideal R) [p.IsPrime] (p' : Ideal R') [p'.IsPrime] [p'.LiesOver p]
    [Algebra.Etale p.ResidueField (p.Fiber S)] :
    Algebra.Etale p'.ResidueField (p'.Fiber (R' ⊗[R] S)) := by
  have h1 : Algebra.Etale p'.ResidueField
      (p'.ResidueField ⊗[p.ResidueField] p.Fiber S) := inferInstance
  have h2 : Algebra.Etale p'.ResidueField (p'.ResidueField ⊗[R] S) :=
    Algebra.Etale.of_equiv
      (Algebra.TensorProduct.cancelBaseChange R p.ResidueField p'.ResidueField
        p'.ResidueField S)
  exact Algebra.Etale.of_equiv
    (Algebra.TensorProduct.cancelBaseChange R R' p'.ResidueField p'.ResidueField S).symm

/-- The base change of the fraction field of `R` along `R'` acts on the base change of any
extension of that fraction field. -/
@[instance_reducible]
private def tensorBaseChangeAlgebra (R R' K L : Type u) [CommRing R] [CommRing R'] [Algebra R R']
    [CommRing K] [Algebra R K] [CommRing L] [Algebra K L] [Algebra R L] [IsScalarTower R K L] :
    Algebra (R' ⊗[R] K) (R' ⊗[R] L) :=
  RingHom.toAlgebra
    (Algebra.TensorProduct.map (AlgHom.id R R') (IsScalarTower.toAlgHom R K L)).toRingHom

/-- Scaling a pure tensor by a pure tensor of the base change of the fraction field. -/
private lemma tensorBaseChange_smul_tmul (R R' K L : Type u) [CommRing R] [CommRing R']
    [Algebra R R'] [CommRing K] [Algebra R K] [CommRing L] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] (a : R') (c : K) (y : L) :
    letI := tensorBaseChangeAlgebra R R' K L
    (a ⊗ₜ[R] c) • ((1 : R') ⊗ₜ[R] y) = a ⊗ₜ[R] (c • y) := by
  let _ := tensorBaseChangeAlgebra R R' K L
  change (Algebra.TensorProduct.map (AlgHom.id R R') (IsScalarTower.toAlgHom R K L))
      (a ⊗ₜ[R] c) * ((1 : R') ⊗ₜ[R] y) = a ⊗ₜ[R] (c • y)
  simp [Algebra.smul_def]

/-- **The generic-fibre bound.** The base change of a finite field extension `L / K` along an
`R`-algebra `R'` is finite over the base change of `K`, of rank at most `[L : K]`. -/
private lemma finite_and_finrank_tensorProduct_le
    (R R' K L : Type u) [CommRing R] [CommRing R'] [Algebra R R']
    [Field K] [Algebra R K] [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L] [Nontrivial (R' ⊗[R] K)] :
    letI := tensorBaseChangeAlgebra R R' K L
    Module.Finite (R' ⊗[R] K) (R' ⊗[R] L) ∧
      Module.finrank (R' ⊗[R] K) (R' ⊗[R] L) ≤ Module.finrank K L := by
  classical
  let _ := tensorBaseChangeAlgebra R R' K L
  let b := Module.finBasis K L
  have key : ∀ x : R' ⊗[R] L,
      x ∈ Submodule.span (R' ⊗[R] K) (Set.range fun j => (1 : R') ⊗ₜ[R] b j) := by
    intro x
    induction x with
    | tmul a l =>
        have hl : a ⊗ₜ[R] l = ∑ j, a ⊗ₜ[R] (b.repr l j • b j) := by
          rw [← TensorProduct.tmul_sum, b.sum_repr l]
        rw [hl]
        refine Submodule.sum_mem _ fun j _ => ?_
        rw [← tensorBaseChange_smul_tmul R R' K L a (b.repr l j) (b j)]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    | add x y hx hy => exact Submodule.add_mem _ hx hy
  exact finite_and_finrank_le_of_span_range _ (Submodule.eq_top_iff'.mpr key)

/-- Over a normal domain `R'` étale over a domain `R` with fraction field `K`, if the base change
to `R'` of a finite extension `L / K` carries `n` nonzero complete orthogonal idempotents and
`[L : K] ≤ n`, then the integral closure of `R'` in that base change is étale over `R'`. -/
private theorem etale_integralClosure_tensorProduct
    (R K L R' : Type u) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L] [FiniteDimensional K L]
    [CommRing R'] [IsDomain R'] [IsIntegrallyClosed R'] [Algebra R R'] [Algebra.Etale R R']
    {n : ℕ} (hn : Module.finrank K L ≤ n)
    (e : Fin n → R' ⊗[R] L) (he : CompleteOrthogonalIdempotents e) (he0 : ∀ i, e i ≠ 0) :
    Algebra.Etale R' (integralClosure R' (R' ⊗[R] L)) := by
  have hfr : IsFractionRing R' (R' ⊗[R] K) := isFractionRing_tensorProduct_fractionField R K R'
  let _ : Field (R' ⊗[R] K) := IsFractionRing.toField R'
  let _ := tensorBaseChangeAlgebra R R' K L
  have htower : IsScalarTower R' (R' ⊗[R] K) (R' ⊗[R] L) := by
    refine IsScalarTower.of_algebraMap_eq fun r => ?_
    change r ⊗ₜ[R] (1 : L) = _
    simp [Algebra.TensorProduct.algebraMap_apply, RingHom.algebraMap_toAlgebra]
  obtain ⟨hfin, hle⟩ := finite_and_finrank_tensorProduct_le R R' K L
  have hli : LinearIndependent (R' ⊗[R] K) e :=
    linearIndependent_completeOrthogonalIdempotents he he0
  have hge : n ≤ Module.finrank (R' ⊗[R] K) (R' ⊗[R] L) := by
    simpa using hli.fintype_card_le_finrank
  exact etale_integralClosure_of_idempotents he he0 (le_antisymm (hle.trans hn) hge)


/-- The dimension of the fibre is unchanged by an étale neighbourhood: the fibre of `p'` in
`R' ⊗[R] S` is the base change along `κ(p) → κ(p')` of the fibre of `p` in `S`. -/
private lemma finrank_fiber_tensorProduct
    {R S R' : Type u} [CommRing R] [CommRing S] [Algebra R S] [CommRing R'] [Algebra R R']
    (p : Ideal R) [p.IsPrime] (p' : Ideal R') [p'.IsPrime] [p'.LiesOver p] :
    Module.finrank p'.ResidueField (p'.Fiber (R' ⊗[R] S))
      = Module.finrank p.ResidueField (p.Fiber S) := by
  have e1 := Algebra.TensorProduct.cancelBaseChange R p.ResidueField p'.ResidueField
    p'.ResidueField S
  have e2 := Algebra.TensorProduct.cancelBaseChange R R' p'.ResidueField p'.ResidueField S
  rw [(e2.trans e1.symm).toLinearEquiv.finrank_eq, Module.finrank_baseChange]

/-- An étale fibre has only finitely many points, so only finitely many primes lie above `p`. -/
private lemma finite_primesOver_of_etale_fiber
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime]
    [Algebra.Etale p.ResidueField (p.Fiber S)] :
    {q : Ideal S | q.IsPrime ∧ q.LiesOver p}.Finite := by
  have hfin : Module.Finite p.ResidueField (p.Fiber S) :=
    Algebra.FormallyUnramified.finite_of_free p.ResidueField _
  have hart : IsArtinianRing (p.Fiber S) := IsArtinianRing.of_finite p.ResidueField _
  have hfp : Finite (PrimeSpectrum (p.Fiber S)) := inferInstance
  have : Finite ↥(p.primesOver S) :=
    Finite.of_equiv _ (PrimeSpectrum.primesOverOrderIsoFiber R S p).toEquiv.symm
  have hfs : (p.primesOver S).Finite := Set.toFinite _
  exact hfs

/-- An element outside a prime stays nonzero in a localization away from another element outside
that prime. -/
private lemma algebraMap_ne_zero_of_notMem
    {A A' : Type u} [CommRing A] [CommRing A'] [Algebra A A'] (c : A)
    [IsLocalization.Away c A'] (a : A) (q : Ideal A) [q.IsPrime] (hcq : c ∉ q) (haq : a ∉ q) :
    algebraMap A A' a ≠ 0 := by
  intro h
  obtain ⟨⟨m, hm⟩, hma⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers c) A' a).mp h
  obtain ⟨k, rfl⟩ := hm
  exact q.primeCompl.mul_mem (q.primeCompl.pow_mem hcq k) haq (hma ▸ q.zero_mem)

/-- **The base change of an `Away` localization.** The localization of `R'` away from `c`,
tensored with `S`, is an algebra over `R' ⊗[R] S`. -/
@[instance_reducible]
private def awayTensorAlgebra (R R' S : Type u) [CommRing R] [CommRing R']
    [CommRing S] [Algebra R R'] [Algebra R S] (c : R') :
    Algebra (R' ⊗[R] S) (Localization.Away c ⊗[R] S) :=
  RingHom.toAlgebra
    (Algebra.TensorProduct.map (Algebra.ofId R' (Localization.Away c))
      (AlgHom.id R S)).toRingHom

/-- **Base change commutes with localization away from an element.** `R'[1/c] ⊗[R] S` is the
localization of `R' ⊗[R] S` away from `c ⊗ₜ 1`. -/
@[ega "III 6.7.1" "special case"]
private lemma isLocalizationAway_tmul_one (R R' S : Type u) [CommRing R] [CommRing R']
    [CommRing S] [Algebra R R'] [Algebra R S] (c : R') :
    letI := awayTensorAlgebra R R' S c
    IsLocalization.Away (c ⊗ₜ[R] (1 : S)) (Localization.Away c ⊗[R] S) := by
  let _ := awayTensorAlgebra R R' S c
  have _ : IsScalarTower R' (R' ⊗[R] S) (Localization.Away c ⊗[R] S) :=
    IsScalarTower.of_algebraMap_eq'
      (Algebra.TensorProduct.map (Algebra.ofId R' (Localization.Away c))
        (AlgHom.id R S)).comp_algebraMap.symm
  have hpow : Submonoid.powers (c ⊗ₜ[R] (1 : S)) =
      Algebra.algebraMapSubmonoid (R' ⊗[R] S) (Submonoid.powers c) := by simp
  rw [IsLocalization.Away, hpow]
  refine IsLocalization.tensorProduct_tensorProduct _ _ _ _ ?_
  ext; simp [RingHom.algebraMap_toAlgebra]

/-- **The fibre surjects onto a residue field.** For an integral algebra `S` over `R` and a prime
`q` of `S` above `p`, the canonical `κ(p)`-algebra map from the fibre `κ(p) ⊗[R] S` to `κ(q)` is
surjective. -/
private lemma surjective_fiberToResidueOver
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Algebra.IsIntegral R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p] :
    Function.Surjective (fiberToResidueOver S p q) := by
  classical
  set f := fiberToResidueOver S p q with hf
  have hint : Algebra.IsIntegral p.ResidueField (p.Fiber S) := inferInstance
  have hkp : (RingHom.ker f.toRingHom).IsPrime := RingHom.ker_isPrime _
  have hmax : (RingHom.ker f.toRingHom).IsMaximal :=
    Algebra.IsIntegral.isMaximal_of_isPrime (k := p.ResidueField) _
  set T : Subring q.ResidueField := f.toRingHom.range with hT
  have hfield : IsField T :=
    MulEquiv.isField ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp hmax)
      (RingHom.quotientKerEquivRange f.toRingHom).symm.toMulEquiv
  have hS : ∀ s : S, algebraMap S q.ResidueField s ∈ T := by
    intro s
    refine ⟨Algebra.TensorProduct.includeRight s, ?_⟩
    simp [hf, fiberToResidueOver]
  have hQ : ∀ x : S ⧸ q, algebraMap (S ⧸ q) q.ResidueField x ∈ T := by
    intro x
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.algebraMap_quotient_residueField_mk]
    exact hS s
  intro y
  obtain ⟨x, d, hd, hxd⟩ := IsFractionRing.div_surjective (A := S ⧸ q) y
  have hdne : algebraMap (S ⧸ q) q.ResidueField d ≠ 0 := by
    simp only [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective _ _)]
    exact nonZeroDivisors.ne_zero hd
  have hyT : y ∈ T := by
    rw [← hxd, div_eq_mul_inv]
    exact T.mul_mem (hQ x) (Subring.inv_mem_of_isField hfield (hQ d) hdne)
  exact hyT

/-- If the fibre of `p` in an integral algebra `S` is étale over `κ(p)`, then for every prime `q`
of `S` above `p` the maximal separable subextension of `κ(q) / κ(p)` is finite over `κ(p)`. -/
private lemma finite_separableClosure_residueField
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Algebra.IsIntegral R S]
    (p : Ideal R) [p.IsPrime] [Algebra.Etale p.ResidueField (p.Fiber S)]
    (q : Ideal S) (hq : q.IsPrime) (hqover : q.LiesOver p) :
    letI := hq
    letI := hqover
    letI := Localization.AtPrime.algebraOfLiesOver p q
    Module.Finite p.ResidueField (separableClosure p.ResidueField q.ResidueField) := by
  let _ := hq
  let _ := hqover
  have hfib : Module.Finite p.ResidueField (p.Fiber S) :=
    Algebra.FormallyUnramified.finite_of_free p.ResidueField _
  have _ : Module.Finite p.ResidueField q.ResidueField :=
    Module.Finite.of_surjective (fiberToResidueOver S p q).toLinearMap
      (surjective_fiberToResidueOver p q)
  infer_instance

/-- The element inverted by a localization lies outside the contraction of any of its
primes. -/
private lemma notMem_under_of_isPrime {A : Type u} [CommRing A] (a : A)
    (B : Type u) [CommRing B] [Algebra A B] [IsLocalization.Away a B]
    (r : Ideal B) [hr : r.IsPrime] : a ∉ Ideal.under A r := by
  intro ha
  exact hr.ne_top (Ideal.eq_top_of_isUnit_mem r ha
    (IsLocalization.map_units (M := Submonoid.powers a) B ⟨a, Submonoid.mem_powers a⟩))

/-- Let `R` be a normal domain with fraction field `K` and `L / K` a finite extension. If the fibre
of a prime `p` in the integral closure `S` of `R` in `L` is étale over `κ(p)` of dimension at least
`[L : K]`, then there is an étale `R`-algebra `R'` carrying a prime over `p` whose integral closure
in `R' ⊗[R] L` is étale over `R'`. -/
private theorem exists_etale_algebra_integralClosure_etale_of_etale_fiber
    (R K L : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L] [FiniteDimensional K L]
    (p : Ideal R) [p.IsPrime]
    [Algebra.Etale p.ResidueField (p.Fiber (integralClosure R L))]
    (hd : Module.finrank K L ≤
      Module.finrank p.ResidueField (p.Fiber (integralClosure R L))) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R')
      (q : Ideal R') (_ : q.IsPrime) (_ : q.LiesOver p),
      Algebra.Etale R' (integralClosure R' (R' ⊗[R] L)) := by
  classical
  obtain ⟨R₀, _, _, _, p₀, hp₀, hp₀o, n, e, he, r, hrp, hro, _, huniq, hpi⟩ :=
    Algebra.exists_etale_completeOrthogonalIdempotents_integral_isPurelyInseparable
      (S := ↥(integralClosure R L)) p
      (finite_primesOver_of_etale_fiber p)
      (fun q hq hqo => finite_separableClosure_residueField p q hq hqo)
  have _ := hp₀
  have _ := hp₀o
  have hef : Algebra.Etale p₀.ResidueField
      (p₀.Fiber (R₀ ⊗[R] ↥(integralClosure R L))) := etale_fiber_tensorProduct p p₀
  have hn : Module.finrank K L ≤ n := by
    refine hd.trans ?_
    rw [← finrank_fiber_tensorProduct (S := ↥(integralClosure R L)) p p₀]
    exact finrank_fiber_le_of_completeOrthogonalIdempotents p₀ he r hrp hro huniq hpi
  obtain ⟨ε, hε, _, hdom, hic⟩ := exists_isIdempotentElem_notMem_normal_away R R₀ p₀
  have _ := hdom
  have _ := hic
  have htow : IsScalarTower R R₀ (Localization.Away ε) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have _ : Algebra.Etale R₀ (Localization.Away ε) := Algebra.Etale.of_isLocalizationAway ε
  have _ : Algebra.Etale R (Localization.Away ε) := Algebra.Etale.comp R R₀ _
  have hdisj : Disjoint ((Submonoid.powers ε : Submonoid R₀) : Set R₀) (p₀ : Set R₀) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime ε).mpr hε
  have hq'p : (p₀.map (algebraMap R₀ (Localization.Away ε))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers ε) _ p₀ ‹_› hdisj
  have hq'o₀ : (p₀.map (algebraMap R₀ (Localization.Away ε))).LiesOver p₀ :=
    IsLocalization.liesOver_map_of_isPrime_disjoint _ _ hdisj
  have hq'o : (p₀.map (algebraMap R₀ (Localization.Away ε))).LiesOver p := .trans _ p₀ _
  let _ := awayTensorAlgebra R R₀ ↥(integralClosure R L) ε
  have hloc : IsLocalization.Away (ε ⊗ₜ[R] (1 : ↥(integralClosure R L)))
      (Localization.Away ε ⊗[R] ↥(integralClosure R L)) :=
    isLocalizationAway_tmul_one R R₀ ↥(integralClosure R L) ε
  have hΦinj : Function.Injective
      (Algebra.TensorProduct.map (AlgHom.id R (Localization.Away ε))
        (integralClosure R L).val) :=
    injective_tensorProduct_map (integralClosure R L).val Subtype.val_injective
  refine ⟨Localization.Away ε, inferInstance, inferInstance, inferInstance,
    p₀.map (algebraMap R₀ (Localization.Away ε)), hq'p, hq'o,
    etale_integralClosure_tensorProduct R K L (Localization.Away ε) hn
      (fun i => Algebra.TensorProduct.map (AlgHom.id R (Localization.Away ε))
        (integralClosure R L).val
        (algebraMap (R₀ ⊗[R] ↥(integralClosure R L))
          (Localization.Away ε ⊗[R] ↥(integralClosure R L)) (e i)))
      ((he.map (algebraMap (R₀ ⊗[R] ↥(integralClosure R L))
        (Localization.Away ε ⊗[R] ↥(integralClosure R L)))).map
          (Algebra.TensorProduct.map (AlgHom.id R (Localization.Away ε))
            (integralClosure R L).val).toRingHom) (fun i => ?_)⟩
  have _ := hrp i
  have _ := hro i
  have hQo : (Ideal.under (R₀ ⊗[R] ↥(integralClosure R L)) (r i)).LiesOver p₀ :=
    inferInstance
  have hei : e i ∉ Ideal.under (R₀ ⊗[R] ↥(integralClosure R L)) (r i) :=
    notMem_under_of_isPrime (e i) _ (r i)
  have hmapε : (algebraMap R₀ (R₀ ⊗[R] ↥(integralClosure R L))) ε
      = ε ⊗ₜ[R] (1 : ↥(integralClosure R L)) := by simp
  have hεi : ε ⊗ₜ[R] (1 : ↥(integralClosure R L)) ∉
      Ideal.under (R₀ ⊗[R] ↥(integralClosure R L)) (r i) := by
    intro hmem
    refine hε ?_
    rw [hQo.over]
    change (algebraMap R₀ (R₀ ⊗[R] ↥(integralClosure R L))) ε ∈
      Ideal.under (R₀ ⊗[R] ↥(integralClosure R L)) (r i)
    rw [hmapε]
    exact hmem
  have h0 : algebraMap (R₀ ⊗[R] ↥(integralClosure R L))
      (Localization.Away ε ⊗[R] ↥(integralClosure R L)) (e i) ≠ 0 :=
    algebraMap_ne_zero_of_notMem _ (e i)
      (Ideal.under (R₀ ⊗[R] ↥(integralClosure R L)) (r i)) hεi hei
  intro hzero
  exact h0 (hΦinj (by simpa using hzero))

end Ring0BTF

/-- For a ring map `A ⟶ B` and a prime `p` of `A`, if the fibre of `Spec B ⟶ Spec A` at `p` is
étale, then the fibre `κ(p) ⊗[A] B` is étale over `κ(p)`. -/
private lemma etale_fiber_of_etale_fiberToSpecResidueField
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (p : PrimeSpectrum A)
    (h : Etale ((Spec.map (CommRingCat.ofHom (algebraMap A B))).fiberToSpecResidueField p)) :
    Algebra.Etale p.asIdeal.ResidueField (p.asIdeal.Fiber B) := by
  have hri : MorphismProperty.RespectsIso (@Etale.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have h2 : Etale (Spec.map (CommRingCat.ofHom
      (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber B)))) :=
    (MorphismProperty.arrow_mk_iso_iff (P := @Etale.{u})
      (Spec.fiberToSpecResidueFieldIso A B p)).mp h
  exact RingHom.etale_algebraMap.mp (HasRingHomProperty.Spec_iff.mp h2)

/-- For an affine morphism `f` and an affine open `W` of the target, the square identifying the
restriction of `f` over `W` with `Spec` of `f.app W` is a pullback square. -/
private lemma isPullback_SpecMap_app_fromSpec {Z Y : Scheme.{u}} (f : Z ⟶ Y) [IsAffineHom f]
    {W : Y.Opens} (hW : IsAffineOpen W) :
    letI : Algebra Γ(Y, W) Γ(Z, f ⁻¹ᵁ W) := (f.app W).hom.toAlgebra
    IsPullback (hW.preimage f).fromSpec
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, W) Γ(Z, f ⁻¹ᵁ W))))
      f hW.fromSpec := by
  let : Algebra Γ(Y, W) Γ(Z, f ⁻¹ᵁ W) := (f.app W).hom.toAlgebra
  have halg : CommRingCat.ofHom (algebraMap Γ(Y, W) Γ(Z, f ⁻¹ᵁ W)) = f.app W := by
    simp [RingHom.algebraMap_toAlgebra]
  rw [halg]
  refine (IsOpenImmersion.isPullback (Spec.map (f.app W)) (hW.preimage f).fromSpec
    hW.fromSpec f ?_ ?_).flip
  · rw [Scheme.Hom.app_eq_appLE]
    exact (hW.SpecMap_appLE_fromSpec f (hW.preimage f) le_rfl).symm
  · simp

/-- **Étale fibres read on an affine chart.** If the scheme-theoretic fibre of an affine morphism
`f` at the point of an affine open `W` corresponding to a prime `y` of `Γ(Y, W)` is étale, then the
ring-theoretic fibre of `Γ(Y, W) ⟶ Γ(Z, f ⁻¹ᵁ W)` at `y` is étale over the residue field. -/
private lemma etale_fiber_sections {Z Y : Scheme.{u}} (f : Z ⟶ Y) [IsAffineHom f]
    {W : Y.Opens} (hW : IsAffineOpen W) (y : ↥(Spec (CommRingCat.of Γ(Y, W))))
    [y.asIdeal.IsPrime]
    (h : Etale (f.fiberToSpecResidueField (hW.fromSpec.base y))) :
    letI : Algebra Γ(Y, W) Γ(Z, f ⁻¹ᵁ W) := (f.app W).hom.toAlgebra
    Algebra.Etale y.asIdeal.ResidueField (y.asIdeal.Fiber Γ(Z, f ⁻¹ᵁ W)) := by
  let : Algebra Γ(Y, W) Γ(Z, f ⁻¹ᵁ W) := (f.app W).hom.toAlgebra
  exact etale_fiber_of_etale_fiberToSpecResidueField y
    (MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (isPullback_fiberToSpecResidueField_of_isPullback
        (isPullback_SpecMap_app_fromSpec f hW) y) h)

/-- **Fibre ranks read on an affine chart.** If the scheme-theoretic fibre of an integral morphism
`f` at the point of an affine open `W` corresponding to a prime `y` of `Γ(Y, W)` is étale and
finite locally free of rank `d`, then the ring-theoretic fibre of `Γ(Y, W) ⟶ Γ(Z, f ⁻¹ᵁ W)` at `y`
has dimension `d` over the residue field. -/
private lemma finrank_fiber_sections {Z Y : Scheme.{u}} (f : Z ⟶ Y) [IsIntegralHom f]
    {W : Y.Opens} (hW : IsAffineOpen W) (y : ↥(Spec (CommRingCat.of Γ(Y, W))))
    [y.asIdeal.IsPrime]
    (h : Etale (f.fiberToSpecResidueField (hW.fromSpec.base y))) (d : ℕ)
    (hd : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      (f.fiberToSpecResidueField (hW.fromSpec.base y)) d) :
    letI : Algebra Γ(Y, W) Γ(Z, f ⁻¹ᵁ W) := (f.app W).hom.toAlgebra
    Module.finrank y.asIdeal.ResidueField (y.asIdeal.Fiber Γ(Z, f ⁻¹ᵁ W)) = d := by
  let : Algebra Γ(Y, W) Γ(Z, f ⁻¹ᵁ W) := (f.app W).hom.toAlgebra
  have _ := h
  have _ := hd
  have hflatw : Flat (f.fiberToSpecResidueField (hW.fromSpec.base y)) := inferInstance
  have hintw : IsIntegralHom (f.fiberToSpecResidueField (hW.fromSpec.base y)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback f (Y.fromSpecResidueField (hW.fromSpec.base y)))
      inferInstance
  have hfinw : IsFinite (f.fiberToSpecResidueField (hW.fromSpec.base y)) :=
    (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mpr ⟨hintw, inferInstance⟩
  have _ : Algebra.Etale y.asIdeal.ResidueField (y.asIdeal.Fiber Γ(Z, f ⁻¹ᵁ W)) :=
    etale_fiber_sections f hW y h
  have _ : Module.Finite y.asIdeal.ResidueField (y.asIdeal.Fiber Γ(Z, f ⁻¹ᵁ W)) :=
    Algebra.FormallyUnramified.finite_of_free y.asIdeal.ResidueField _
  have _ : Module.Flat y.asIdeal.ResidueField (y.asIdeal.Fiber Γ(Z, f ⁻¹ᵁ W)) :=
    Module.Flat.of_free
  have _ : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap y.asIdeal.ResidueField
      (y.asIdeal.Fiber Γ(Z, f ⁻¹ᵁ W))))) :=
    (IsFinite.SpecMap_iff _).mpr (by simpa [RingHom.finite_algebraMap])
  have _ : Flat (Spec.map (CommRingCat.ofHom (algebraMap y.asIdeal.ResidueField
      (y.asIdeal.Fiber Γ(Z, f ⁻¹ᵁ W))))) :=
    (Flat.SpecMap_iff).mpr (by simpa [RingHom.flat_algebraMap_iff])
  obtain ⟨pt⟩ : Nonempty ↥(Spec ((Spec (CommRingCat.of Γ(Y, W))).residueField y)) := ⟨default⟩
  let e := Spec.fiberToSpecResidueFieldIso (R := Γ(Y, W)) (S := Γ(Z, f ⁻¹ᵁ W)) y
  have hpb : IsPullback e.hom.left
      ((Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, W) Γ(Z, f ⁻¹ᵁ W)))).fiberToSpecResidueField y)
      (Spec.map (CommRingCat.ofHom (algebraMap y.asIdeal.ResidueField
        (y.asIdeal.Fiber Γ(Z, f ⁻¹ᵁ W))))) e.hom.right :=
    IsPullback.of_horiz_isIso ⟨e.hom.w⟩
  have hL := Scheme.Hom.finrank_of_isPullback _
    ((Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, W) Γ(Z, f ⁻¹ᵁ W)))).fiberToSpecResidueField y)
    (f.fiberToSpecResidueField (hW.fromSpec.base y))
    (Spec.map (hW.fromSpec.residueFieldMap y))
    (isPullback_fiberToSpecResidueField_of_isPullback
      (isPullback_SpecMap_app_fromSpec f hW) y) pt
  have hR := Scheme.Hom.finrank_of_isPullback e.hom.left
    ((Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, W) Γ(Z, f ⁻¹ᵁ W)))).fiberToSpecResidueField y)
    (Spec.map (CommRingCat.ofHom (algebraMap y.asIdeal.ResidueField
      (y.asIdeal.Fiber Γ(Z, f ⁻¹ᵁ W))))) e.hom.right hpb pt
  have h1 := @finrank_eq_finrank_sections ↑(Y.residueField (hW.fromSpec.base y)) inferInstance
    (f.fiber (hW.fromSpec.base y)) (f.fiberToSpecResidueField (hW.fromSpec.base y))
    hfinw hflatw ((Spec.map (hW.fromSpec.residueFieldMap y)).base pt)
  have h2 := @finrank_sections_eq_of_rank ↑(Y.residueField (hW.fromSpec.base y)) inferInstance
    (f.fiber (hW.fromSpec.base y)) (f.fiberToSpecResidueField (hW.fromSpec.base y)) d hd
  have h3 := Scheme.Hom.finrank_SpecMap_algebraMap y.asIdeal.ResidueField
    (y.asIdeal.Fiber Γ(Z, f ⁻¹ᵁ W)) (e.hom.right.base pt)
  have h4 : Module.rankAtStalk (y.asIdeal.Fiber Γ(Z, f ⁻¹ᵁ W)) (e.hom.right.base pt)
      = Module.finrank y.asIdeal.ResidueField (y.asIdeal.Fiber Γ(Z, f ⁻¹ᵁ W)) := by
    simpa only [Pi.natCast_def, Pi.natCast_apply, Nat.cast_id] using
      congrFun (Module.rankAtStalk_eq_finrank_of_free
        (R := y.asIdeal.ResidueField) (M := y.asIdeal.Fiber Γ(Z, f ⁻¹ᵁ W))) (e.hom.right.base pt)
  exact h4.symm.trans (h3.symm.trans (hR.symm.trans (hL.trans (h1.trans h2))))

/-- Let `W` be an affine open of `X` containing `x`, with coordinate ring `R = Γ(X, W)` and
corresponding prime `p ⊂ R`. If every scheme theoretic fibre of the normalization is étale of
degree at least `[L : K]`, then there is an étale `R`-algebra `R'` carrying a prime over `p` whose
integral closure in `R' ⊗[R] L` is étale over `R'`. -/
private theorem exists_etale_algebra_integralClosure_etale
    (X : Scheme.{u}) [IsIntegral X] [IsNormal X]
    (L : Type u) [Field L] [Algebra X.functionField L]
    [FiniteDimensional X.functionField L]
    (i : Spec (.of L) ⟶ X)
    (hi : i = Spec.map (CommRingCat.ofHom
      (algebraMap X.functionField L)) ≫ X.fromSpecStalk (genericPoint X))
    [QuasiCompact i] [QuasiSeparated i]
    (h : ∀ x : X, ∃ d : ℕ, Module.finrank X.functionField L ≤ d ∧
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank
        (i.fromNormalization.fiberToSpecResidueField x) d ∧
      Etale (i.fromNormalization.fiberToSpecResidueField x))
    (x : X) (W : X.Opens) (hW : IsAffineOpen W) [Nonempty W] (hx : x ∈ W) :
    letI : Algebra Γ(X, W) L :=
      ((algebraMap X.functionField L).comp (X.germToFunctionField W).hom).toAlgebra
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra Γ(X, W) R')
      (_ : Algebra.Etale Γ(X, W) R') (q : Ideal R') (_ : q.IsPrime)
      (_ : q.LiesOver (hW.primeIdealOf ⟨x, hx⟩).asIdeal),
      Algebra.Etale R' (integralClosure R' (R' ⊗[Γ(X, W)] L)) := by
  let : Algebra Γ(X, W) L :=
    ((algebraMap X.functionField L).comp (X.germToFunctionField W).hom).toAlgebra
  let : IsScalarTower Γ(X, W) X.functionField L := .of_algebraMap_eq' rfl
  have : IsFractionRing Γ(X, W) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X W hW
  have : IsIntegrallyClosed Γ(X, W) := isIntegrallyClosed_sections X W hW
  let : Algebra Γ(X, W) Γ(i.normalization, i.fromNormalization ⁻¹ᵁ W) :=
    (i.fromNormalization.app W).hom.toAlgebra
  obtain ⟨d, hdLE, hdRank, hdEt⟩ := h x
  have hEtN : Algebra.Etale (hW.primeIdealOf ⟨x, hx⟩).asIdeal.ResidueField
      ((hW.primeIdealOf ⟨x, hx⟩).asIdeal.Fiber
        Γ(i.normalization, i.fromNormalization ⁻¹ᵁ W)) := by
    refine etale_fiber_sections i.fromNormalization hW (hW.primeIdealOf ⟨x, hx⟩) ?_
    rw [hW.fromSpec_primeIdealOf ⟨x, hx⟩]
    exact hdEt
  have hrkN : Module.finrank (hW.primeIdealOf ⟨x, hx⟩).asIdeal.ResidueField
      ((hW.primeIdealOf ⟨x, hx⟩).asIdeal.Fiber
        Γ(i.normalization, i.fromNormalization ⁻¹ᵁ W)) = d := by
    refine finrank_fiber_sections i.fromNormalization hW (hW.primeIdealOf ⟨x, hx⟩) ?_ d ?_
    · rw [hW.fromSpec_primeIdealOf ⟨x, hx⟩]; exact hdEt
    · rw [hW.fromSpec_primeIdealOf ⟨x, hx⟩]; exact hdRank
  have _ := hEtN
  let eF := Algebra.TensorProduct.congr
    (AlgEquiv.refl (R := (hW.primeIdealOf ⟨x, hx⟩).asIdeal.ResidueField)
      (A₁ := (hW.primeIdealOf ⟨x, hx⟩).asIdeal.ResidueField))
    (normalizationSectionsEquiv X L i hi W hW)
  have _ : Algebra.Etale (hW.primeIdealOf ⟨x, hx⟩).asIdeal.ResidueField
      ((hW.primeIdealOf ⟨x, hx⟩).asIdeal.Fiber (integralClosure Γ(X, W) L)) :=
    Algebra.Etale.of_equiv eF
  exact exists_etale_algebra_integralClosure_etale_of_etale_fiber Γ(X, W) X.functionField L
    (hW.primeIdealOf ⟨x, hx⟩).asIdeal
    (hdLE.trans (hrkN.symm.trans eF.toLinearEquiv.finrank_eq).le)

/-- If every scheme theoretic fibre of the normalization is étale of degree at least `[L : K]`,
then every point of `X` has an étale neighbourhood `U` such that the normalization of `U` in
`Spec L ×[X] U` is étale over `U`. -/
private theorem exists_etale_neighborhood_normalization_etale
    (X : Scheme.{u}) [IsIntegral X] [IsNormal X]
    (L : Type u) [Field L] [Algebra X.functionField L]
    [FiniteDimensional X.functionField L]
    (i : Spec (.of L) ⟶ X)
    (hi : i = Spec.map (CommRingCat.ofHom
      (algebraMap X.functionField L)) ≫ X.fromSpecStalk (genericPoint X))
    [QuasiCompact i] [QuasiSeparated i]
    (h : ∀ x : X, ∃ d : ℕ, Module.finrank X.functionField L ≤ d ∧
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank
        (i.fromNormalization.fiberToSpecResidueField x) d ∧
      Etale (i.fromNormalization.fiberToSpecResidueField x))
    (x : X) :
    ∃ (U : Scheme.{u}) (g : U ⟶ X), Etale g ∧ x ∈ Set.range g.base ∧
      Etale (pullback.snd i g).fromNormalization := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hx, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ (⊤ : X.Opens) from trivial) isOpen_univ
  have hoi : IsOpenImmersion hW.fromSpec := hW.isOpenImmersion_fromSpec
  have : Nonempty W := ⟨⟨x, hx⟩⟩
  let : Algebra Γ(X, W) L :=
    ((algebraMap X.functionField L).comp (X.germToFunctionField W).hom).toAlgebra
  obtain ⟨R', _, _, _, q, hq, hqo, hcl⟩ :=
    exists_etale_algebra_integralClosure_etale X L i hi h x W hW hx
  refine exists_etale_of_etale_algebra hW.fromSpec hoi i
    (functionFieldMap_eq_SpecMap_fromSpec X L i hi W hW) R' hcl x ⟨q, hq⟩ ?_
  have hpoint : (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, W) R'))).base
      ⟨q, hq⟩ = hW.primeIdealOf ⟨x, hx⟩ :=
    PrimeSpectrum.ext (q.over_def _).symm
  have hfs := hW.fromSpec_primeIdealOf ⟨x, hx⟩
  rwa [← hpoint] at hfs

/-- **Unramifiedness of the normalization of a normal integral scheme in a finite extension of
its function field.** For `X` integral and normal with function field `K`, a finite extension
`L / K` and `f : Y ⟶ X` the normalization of `X` in `L`, the following are equivalent: `f` is
unramified (which is the definition of `X` being unramified in `L`); `f` is étale; `f` is finite
étale; `f` becomes unramified over `Spec` of every local ring of `X`; the same over every
henselization of a local ring of `X`; the same over every strict henselization; and every
scheme-theoretic fibre of `f` is étale and finite locally free of some rank at least
`[L : K]`. -/
@[stacks 0BTF "conditions (1)–(8)"]
public theorem normalization_unramified_tfae
    (X : Scheme.{u}) [IsIntegral X] [IsNormal X]
    (L : Type u) [Field L] [Algebra X.functionField L]
    [FiniteDimensional X.functionField L]
    (i : Spec (.of L) ⟶ X)
    (hi : i = Spec.map (CommRingCat.ofHom
      (algebraMap X.functionField L)) ≫ X.fromSpecStalk (genericPoint X))
    [QuasiCompact i] [QuasiSeparated i] :
    let f : i.normalization ⟶ X := i.fromNormalization
    List.TFAE [
      Unramified f,
      Etale f,
      IsFinite f ∧ Etale f,
      (∀ x : X, Unramified
        (pullback.snd f (X.fromSpecStalk x))),
      (∀ (x : X) (R : Type u) [CommRing R] [IsLocalRing R]
        [Algebra (X.presheaf.stalk x) R]
        [IsLocalRing.IsHenselization (X.presheaf.stalk x)
          (ResidueField (X.presheaf.stalk x)) R],
        Unramified
          (pullback.snd f
            (Spec.map (CommRingCat.ofHom
              (algebraMap (X.presheaf.stalk x) R)) ≫ X.fromSpecStalk x))),
      (∀ (x : X) (κsep : Type u) [Field κsep]
        [Algebra (ResidueField (X.presheaf.stalk x)) κsep]
        [IsSepClosure (ResidueField (X.presheaf.stalk x)) κsep]
        (R : Type u) [CommRing R] [IsLocalRing R]
        [Algebra (X.presheaf.stalk x) R]
        [IsLocalRing.IsHenselization (X.presheaf.stalk x) κsep R],
        Unramified
          (pullback.snd f
            (Spec.map (CommRingCat.ofHom
              (algebraMap (X.presheaf.stalk x) R)) ≫ X.fromSpecStalk x))),
      (∀ x : X, ∃ d : ℕ, Module.finrank X.functionField L ≤ d ∧
        Stacks.Morphisms.IsFiniteLocallyFreeOfRank (f.fiberToSpecResidueField x) d ∧
        Etale (f.fiberToSpecResidueField x))] := by
  let f := i.fromNormalization
  have : IsIntegral (Spec (.of L)) := inferInstance
  have : IsDominant i := isDominant_functionFieldMap X L i hi
  have : IsDominant (i.toNormalization ≫ f) := by
    simpa only [f, Scheme.Hom.toNormalization_fromNormalization] using
      (inferInstance : IsDominant i)
  have : IsDominant f := IsDominant.of_comp i.toNormalization f
  tfae_have 1 ↔ 2 :=
    AlgebraicGeometry.unramified_normalization_iff_etale i
  tfae_have 2 ↔ 3 :=
    AlgebraicGeometry.etale_normalization_iff_finite_etale i
  tfae_have 3 → 4 := by
    rintro ⟨_, hEtale⟩ x
    let : Etale f := hEtale
    let g := pullback.snd f (X.fromSpecStalk x)
    let : Etale g := inferInstance
    exact unramified_of_etale g
  tfae_have 4 → 5 := by
    intro h x R
    exact unramified_pullback_comp f (X.fromSpecStalk x)
      (Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) R))) (h x)
  tfae_have 5 → 6 := by
    intro h x κsep hField hAlgebra hSepClosure R hComm hLocal hAlgebraR hHensel
    let A := X.presheaf.stalk x
    let κ := ResidueField A
    obtain ⟨Ah, hAhRing, hAhAlg, hAhLocal, hAhLocalHom, hAhHens, hAhInd,
      hAhMax, hAhBij⟩ := IsLocalRing.exists_henselization A
    let : CommRing Ah := hAhRing
    let : Algebra A Ah := hAhAlg
    let : IsLocalRing Ah := hAhLocal
    let : IsLocalHom (algebraMap A Ah) := hAhLocalHom
    have hAhCompat : ∃ e : κ ≃+* ResidueField Ah, ∀ a : A,
        e (algebraMap κ κ (residue A a)) = residue Ah (algebraMap A Ah a) := by
      refine ⟨RingEquiv.ofBijective (ResidueField.map (algebraMap A Ah)) hAhBij, ?_⟩
      intro a
      rfl
    let : IsHenselization A κ Ah :=
      IsLocalRing.IsHenselization.of_ind_etale hAhHens hAhInd hAhCompat
    let : HenselianLocalRing R :=
      IsLocalRing.IsHenselization.henselian (R := A) (L := κsep) (Rh := R)
    let : IsLocalHom (algebraMap A R) :=
      IsLocalRing.IsHenselization.isLocalHom (R := A) (L := κsep) (Rh := R)
    obtain ⟨φ, hφ, -⟩ := HenselianLocalRing.existsUnique_isLocalHom_of_ind_etale
      (R := A) (Rh := Ah) (Sh := R)
      (IsLocalRing.IsHenselization.ind_etale (R := A) (L := κ) (Rh := Ah))
      hAhBij.2
    let : Algebra Ah R := φ.toRingHom.toAlgebra
    let : IsScalarTower A Ah R := IsScalarTower.of_algebraMap_eq fun a =>
      (φ.commutes a).symm
    have hAtAh := h x Ah
    have hAtR := unramified_pullback_comp f
      (Spec.map (CommRingCat.ofHom (algebraMap A Ah)) ≫ X.fromSpecStalk x)
      (Spec.map (CommRingCat.ofHom (algebraMap Ah R))) hAtAh
    have hSpec : Spec.map (CommRingCat.ofHom (algebraMap A R)) =
        Spec.map (CommRingCat.ofHom (algebraMap Ah R)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap A Ah)) := by
      rw [IsScalarTower.algebraMap_eq A Ah R, CommRingCat.ofHom_comp,
        Spec.map_comp]
    rw [hSpec, Category.assoc]
    exact hAtR
  tfae_have 6 → 4 := by
    intro h x
    let A := X.presheaf.stalk x
    let ksep := separableClosure (ResidueField A) (AlgebraicClosure (ResidueField A))
    obtain ⟨R, hRing, hLocal, hAlg, hHens⟩ := exists_isHenselization_of_sepClosure A ksep
    let := hRing
    let := hLocal
    let := hAlg
    let := hHens
    have : Module.FaithfullyFlat A R := IsHenselization.faithfullyFlat (L := ksep)
    let g := Spec.map (CommRingCat.ofHom (algebraMap A R))
    have : Surjective g := ⟨PrimeSpectrum.comap_surjective_of_faithfullyFlat⟩
    have : Flat g := (Flat.SpecMap_iff).mpr (by
      exact (RingHom.flat_algebraMap_iff).mpr inferInstance)
    exact unramified_pullback_of_pullback_comp f (X.fromSpecStalk x) g (h x ksep R)
  tfae_have 4 → 7 := by
    intro h x
    have hlocal := finite_etale_pullback_stalk_of_unramified f x (h x)
    let g := X.fromSpecStalk x
    let r := Spec.map (X.residue x)
    let p := pullback.snd f g
    have : IsFinite p := hlocal.1
    have : Etale p := hlocal.2
    let e := pullbackLeftPullbackSndIso f (X.fromSpecStalk x)
      (Spec.map (X.residue x))
    have hcomp : e.hom ≫ f.fiberToSpecResidueField x = pullback.snd p r :=
      pullbackLeftPullbackSndIso_hom_snd f g r
    have hfac : f.fiberToSpecResidueField x = e.inv ≫ pullback.snd p r :=
      (Iso.eq_inv_comp e).2 hcomp
    have : IsFinite (pullback.snd p r) := inferInstance
    have : Etale (pullback.snd p r) := inferInstance
    have : IsFinite e.inv := inferInstance
    have : Etale e.inv := inferInstance
    have hfiniteFiber : IsFinite (f.fiberToSpecResidueField x) := by
      rw [hfac]
      exact MorphismProperty.IsStableUnderComposition.comp_mem e.inv
        (pullback.snd p r) inferInstance inferInstance
    have hetaleFiber : Etale (f.fiberToSpecResidueField x) := by
      rw [hfac]
      exact Etale.etale_comp (f := e.inv) (pullback.snd p r)
    let := hfiniteFiber
    let := hetaleFiber
    obtain ⟨d, hd⟩ := @exists_rank_of_finite_etale_over_field
      (X.residueField x) _ (f.fiber x) (f.fiberToSpecResidueField x)
      hfiniteFiber hetaleFiber
    refine ⟨d, ?_, hd, inferInstance⟩
    have hdimFiber := @finrank_sections_eq_of_rank (X.residueField x) inferInstance
      (f.fiber x) (f.fiberToSpecResidueField x) d hd
    let : IsLocalRing (X.presheaf.stalk x) := X.isLocalRing x
    let : Flat g := flat_fromSpecStalk X x
    have hflatFiber : Flat (f.fiberToSpecResidueField x) := by
      let := hetaleFiber; infer_instance
    have hdx : p.finrank (r (default : ↥(Spec (X.residueField x)))) = d := by
      have h1 : Scheme.Hom.finrank (pullback.snd p r)
            (default : ↥(Spec (X.residueField x))) =
          p.finrank (r (default : ↥(Spec (X.residueField x)))) :=
        Scheme.Hom.finrank_pullback_snd p r _
      rw [← h1, ← Scheme.Hom.finrank_comp_left_of_isIso e.inv (pullback.snd p r), ← hfac]
      exact (@finrank_eq_finrank_sections ↑(X.residueField x) inferInstance
        (f.fiber x) (f.fiberToSpecResidueField x) hfiniteFiber hflatFiber
        default).trans hdimFiber
    have hgen := finite_etale_pullback_stalk_of_unramified f (genericPoint ↥X)
      (h (genericPoint ↥X))
    have : IsFinite (pullback.snd f (X.fromSpecStalk (genericPoint ↥X))) := hgen.1
    have : Etale (pullback.snd f (X.fromSpecStalk (genericPoint ↥X))) := hgen.2
    let s := Spec.map (X.presheaf.stalkSpecializes (genericPoint_specializes x))
    have hsg : s ≫ g = X.fromSpecStalk (genericPoint ↥X) :=
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk _
    have : IsFinite (pullback.snd f (s ≫ g)) := by rw [hsg]; infer_instance
    have : Flat (pullback.snd f (s ≫ g)) := by rw [hsg]; infer_instance
    have hdη : p.finrank (s (closedPoint (X.presheaf.stalk (genericPoint ↥X)))) =
        Module.finrank X.functionField L := by
      have h1 : Scheme.Hom.finrank (pullback.snd p s)
            (closedPoint (X.presheaf.stalk (genericPoint ↥X))) =
          p.finrank (s (closedPoint (X.presheaf.stalk (genericPoint ↥X)))) :=
        Scheme.Hom.finrank_pullback_snd p s _
      have h2 : pullback.snd p s =
          (pullbackLeftPullbackSndIso f g s).hom ≫ pullback.snd f (s ≫ g) :=
        (pullbackLeftPullbackSndIso_hom_snd f g s).symm
      rw [← h1, h2, Scheme.Hom.finrank_comp_left_of_isIso]
      exact finrank_genericFiber X L i hi (s ≫ g) hsg _
    refine le_of_eq ?_
    rw [← hdx, ← hdη]
    exact (p.isLocallyConstant_finrank).apply_eq_of_preconnectedSpace _ _
  tfae_have 7 → 1 := by
    intro h
    refine (AlgebraicGeometry.unramified_normalization_iff_etale i).mpr ?_
    choose U g hg hmem hnorm using exists_etale_neighborhood_normalization_etale X L i hi h
    refine etale_of_etale_cover i.fromNormalization g hg (fun x ↦ ⟨x, hmem x⟩) fun x ↦ ?_
    have := hg x
    exact etale_pullback_fromNormalization i (g x) (hnorm x)
  tfae_finish

/-- **The Galois case: unramifiedness of the normalization is triviality of every inertia
group.** For `X` integral and normal with function field `K` and `L / K` finite Galois with
group `G = Gal(L/K)`, the normalization of `X` in `L` is unramified exactly when, on every
nonempty affine open `U` of `X` and for every prime `q` of the integral closure of `Γ(X, U)` in
`L`, the only `σ ∈ G` fixing `q` elementwise and inducing the identity modulo `q` is the
identity; that is, exactly when every inertia group
`I_q = {σ ∈ G | σ(q) = q and σ ≡ id mod q}` is trivial. -/
@[stacks 0BTF "condition (9)"]
public theorem normalization_unramified_iff_trivialInertia
    (X : Scheme.{u}) [IsIntegral X] [IsNormal X]
    (L : Type u) [Field L] [Algebra X.functionField L]
    [FiniteDimensional X.functionField L] [IsGalois X.functionField L]
    (i : Spec (.of L) ⟶ X)
    (hi : i = Spec.map (CommRingCat.ofHom
      (algebraMap X.functionField L)) ≫ X.fromSpecStalk (genericPoint X))
    [QuasiCompact i] [QuasiSeparated i] :
    Unramified i.fromNormalization ↔
      ∀ (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U],
        letI : Algebra Γ(X, U) L :=
          ((algebraMap X.functionField L).comp
            (X.germToFunctionField U).hom).toAlgebra
        letI : IsScalarTower Γ(X, U) X.functionField L :=
          .of_algebraMap_eq' rfl
        letI : IsFractionRing Γ(X, U) X.functionField :=
          functionField_isFractionRing_of_isAffineOpen X U hU
        ∀ (q : Ideal (integralClosure Γ(X, U) L)) (_hq : q.IsPrime)
          (σ : L ≃ₐ[X.functionField] L),
          ((∀ y, y ∈ q ↔
              galRestrict Γ(X, U) X.functionField L
                (integralClosure Γ(X, U) L) σ y ∈ q) ∧
            (∀ y, galRestrict Γ(X, U) X.functionField L
              (integralClosure Γ(X, U) L) σ y - y ∈ q)) →
          σ = 1 := by
  have : IsDominant i := isDominant_functionFieldMap X L i hi
  constructor
  · intro h U hU hnonempty
    have : Etale i.fromNormalization :=
      (AlgebraicGeometry.unramified_normalization_iff_etale i).mp h
    let : Algebra Γ(X, U) L :=
      ((algebraMap X.functionField L).comp (X.germToFunctionField U).hom).toAlgebra
    let : IsScalarTower Γ(X, U) X.functionField L := .of_algebraMap_eq' rfl
    have : IsFractionRing Γ(X, U) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X U hU
    let : Algebra Γ(X, U) Γ(i.normalization, i.fromNormalization ⁻¹ᵁ U) :=
      (i.fromNormalization.app U).hom.toAlgebra
    have : Algebra.Etale Γ(X, U) Γ(i.normalization, i.fromNormalization ⁻¹ᵁ U) := by
      change RingHom.Etale (i.fromNormalization.app U).hom
      simpa only [Scheme.Hom.app_eq_appLE] using
        i.fromNormalization.etale_appLE hU (hU.preimage i.fromNormalization) le_rfl
    have : Algebra.Etale Γ(X, U) (integralClosure Γ(X, U) L) :=
      Algebra.Etale.of_equiv (normalizationSectionsEquiv X L i hi U hU)
    intro q hq σ hσ
    exact inertia_eq_one_of_unramified_integralClosure Γ(X, U) X.functionField L
      q hq.ne_top σ hσ.2
  · intro h
    constructor
    intro y
    obtain ⟨_, ⟨U, hU, rfl⟩, hy, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (show i.fromNormalization y ∈ (⊤ : X.Opens) from trivial) isOpen_univ
    have : Nonempty U := ⟨⟨i.fromNormalization y, hy⟩⟩
    let : Algebra Γ(X, U) L :=
      ((algebraMap X.functionField L).comp (X.germToFunctionField U).hom).toAlgebra
    let : IsScalarTower Γ(X, U) X.functionField L := .of_algebraMap_eq' rfl
    have : IsFractionRing Γ(X, U) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X U hU
    have : IsIntegrallyClosed Γ(X, U) :=
      (AlgebraicGeometry.isNormal_iff_forall_affineOpen_normal X).mp inferInstance ⟨U, hU⟩
        inferInstance
    have : Algebra.Etale Γ(X, U) (integralClosure Γ(X, U) L) := by
      apply integralClosure_etale_of_trivialInertia Γ(X, U) X.functionField L
      intro q hq σ hσ
      apply h U hU q hq σ
      refine ⟨?_, hσ⟩
      intro z
      constructor
      · intro hz
        simpa only [sub_add_cancel] using q.add_mem (hσ z) hz
      · intro hz
        simpa only [sub_sub_cancel] using q.sub_mem hz (hσ z)
    let : Algebra Γ(X, U) Γ(i.normalization, i.fromNormalization ⁻¹ᵁ U) :=
      (i.fromNormalization.app U).hom.toAlgebra
    have : Algebra.Etale Γ(X, U) Γ(i.normalization, i.fromNormalization ⁻¹ᵁ U) :=
      Algebra.Etale.of_equiv (normalizationSectionsEquiv X L i hi U hU).symm
    refine ⟨i.fromNormalization ⁻¹ᵁ U, hU.preimage i.fromNormalization, hy,
      U, hU, le_rfl, ?_⟩
    rw [← Scheme.Hom.app_eq_appLE]
    infer_instance

end AlgebraicGeometry

end
