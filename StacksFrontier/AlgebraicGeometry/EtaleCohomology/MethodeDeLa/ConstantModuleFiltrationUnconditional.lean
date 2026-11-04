module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.EtaleLocalRepresentability
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.DenseSubsite
public import StacksFrontier.Topology.Sheaves.Modules.TensorExactness
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.FiniteEtalePushforward.OverSiteDisjointCover
public import StacksCore.Algebra.Homology.SpectralSequence.Tower
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.GaloisCoverDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.MonodromyModule
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.PointedGaloisCovering
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.LocalizedGeneralCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.OverMapConstant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.NeighborhoodsStalksPoints.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.RankFpqcDescent
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.EtaleFundamentalGroup
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleEquivalence
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.RingTheory.Branches.Defs
public import StacksFrontier.RingTheory.FinitePresentation.ModuleDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.MethodeDeLa.ConstantModuleFiltration
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.MethodeDeLa.ConstantModuleFiltration

public import Mathlib.Algebra.Category.ModuleCat.Subobject
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.GroupTheory.Sylow
public import Mathlib.RepresentationTheory.Subrepresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.DescentSheafExactness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.FiniteEtalePushforward
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.GaloisCoverSubgroupQuotient
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.GaloisTrivializationExists
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.MethodeDeLa.PGroupFiltration
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.EtaleFundamental.FundamentalGroupTheorem
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FunctorsHomomorphisms.Comparison
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GeometricFibreDegree
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFreeOfRank
public import StacksFrontier.AlgebraicGeometry.Properties.Unibranch
public import StacksCore.Tactic.StacksAttribute

/-!
# ConstantModuleFiltrationUnconditional

Stronger forms of declarations of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.MethodeDeLa.ConstantModuleFiltration`, stated as
separate declarations beside the ones there: over more general coefficient universes, or with
inputs that are carried there as hypotheses discharged, together with the new results built on
them.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped FintypeCatDiscrete SetRel

universe v u

namespace Stacks.EtaleCohomology

/-- **Restriction along an étale morphism `f : Y ⟶ S` of a sheaf constant on `f ∘ C` is constant
on `C`**, with the same value: the two slices are both the small étale site of the scheme
underlying `C`, and the two restrictions of the sheaf agree there. The slice identifications are
the base's own private `Stacks.ConstantSheaf.smallEtaleOverSheafEquivalence` and its companions
(`StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.FiniteEtalePushforward`),
reached by `import all`, which is why this comparison is private. -/
private def overPullbackEtaleModuleRestrictionIso {Λ : Type v} [CommRing Λ] {Y S : Scheme.{u}}
    (f : Y ⟶ S) [Etale f] (C : Y.Etale)
    {F : Sheaf (smallEtaleTopology S) (ModuleCat.{max (u + 1) v} Λ)}
    {M : ModuleCat.{max (u + 1) v} Λ}
    (e : (constantSheaf ((smallEtaleTopology S).over ((Scheme.Etale.smallEtaleCompose f).obj C))
        (ModuleCat.{max (u + 1) v} Λ)).obj M ≅
      ((smallEtaleTopology S).overPullback _ ((Scheme.Etale.smallEtaleCompose f).obj C)).obj F) :
    (constantSheaf ((smallEtaleTopology Y).over C) (ModuleCat.{max (u + 1) v} Λ)).obj M ≅
      ((smallEtaleTopology Y).overPullback _ C).obj ((etaleModuleRestriction.{u, v} Λ f).obj F) :=
  let D := (Scheme.Etale.smallEtaleCompose f).obj C
  let EqC :=
    _root_.Stacks.ConstantSheaf.smallEtaleOverSheafEquivalence C (ModuleCat.{max (u + 1) v} Λ)
  let EqD :=
    _root_.Stacks.ConstantSheaf.smallEtaleOverSheafEquivalence D (ModuleCat.{max (u + 1) v} Λ)
  let Z : EqD.functor.obj (((smallEtaleTopology S).overPullback _ D).obj F) ≅
      EqC.functor.obj (((smallEtaleTopology Y).overPullback _ C).obj
        ((etaleModuleRestriction.{u, v} Λ f).obj F)) :=
    (fullyFaithfulSheafToPresheaf _ _).preimageIso (Functor.isoWhiskerRight (NatIso.op
      (NatIso.ofComponents
        (F := _root_.Stacks.ConstantSheaf.smallEtaleOverInverse C ⋙ Over.forget C ⋙
          Scheme.Etale.smallEtaleCompose f)
        (G := _root_.Stacks.ConstantSheaf.smallEtaleOverInverse D ⋙ Over.forget D)
        (fun V ↦ MorphismProperty.Over.isoMk (Iso.refl V.left) (by
          change 𝟙 _ ≫ (V.hom ≫ C.hom ≫ f) = (V.hom ≫ C.hom) ≫ f
          rw [Category.id_comp]
          exact (Category.assoc _ _ _).symm))
        (fun {V V'} g ↦ by
          apply MorphismProperty.Over.Hom.ext
          change g.left ≫ 𝟙 _ = 𝟙 _ ≫ g.left
          rw [Category.id_comp, Category.comp_id]))) F.obj)
  EqC.fullyFaithfulFunctor.preimageIso
    ((_root_.Stacks.ConstantSheaf.constantSheaf_smallEtaleOverSheafEquivalence_iso C _).app M ≪≫
      ((_root_.Stacks.ConstantSheaf.constantSheaf_smallEtaleOverSheafEquivalence_iso D _).app
        M).symm ≪≫
      EqD.functor.mapIso e ≪≫ Z)

section DescentFiltration

variable {Λ : Type v} [CommRing Λ] {Y : Scheme.{u}} {H : Type u} [Group H]
  (G : EtaleGaloisCovering Y H) {N : Type (max (u + 1) v)} [AddCommGroup N] [Module Λ N]
  (ρ : Representation Λ H N) {B : Sheaf (smallEtaleTopology Y) (ModuleCat.{max (u + 1) v} Λ)}
  (Ψ : G.descentSheaf Λ N ρ ≅ B)

/-- The subsheaf of `B ≅ D(N)` attached to a subrepresentation `K` of `N`: the image of `D(K)`. -/
def descentSubobject (K : Subrepresentation ρ) : Subobject B :=
  haveI := G.mono_descentSheafMap (ρ₁ := K.toRepresentation) (ρ₂ := ρ) K.toSubmodule.subtype
    (fun _ _ ↦ rfl) K.toSubmodule.injective_subtype
  Subobject.mk (G.descentSheafMap (ρ₁ := K.toRepresentation) (ρ₂ := ρ) K.toSubmodule.subtype
    (fun _ _ ↦ rfl) ≫ Ψ.hom)

/-- Descent of the inclusion of a subrepresentation is a monomorphism. -/
private theorem mono_descentSheafMap_subtype (K : Subrepresentation ρ) :
    Mono (G.descentSheafMap (ρ₁ := K.toRepresentation) (ρ₂ := ρ) K.toSubmodule.subtype
      (fun _ _ ↦ rfl)) :=
  G.mono_descentSheafMap (ρ₁ := K.toRepresentation) (ρ₂ := ρ) K.toSubmodule.subtype
    (fun _ _ ↦ rfl) K.toSubmodule.injective_subtype

/-- **A step of a filtration by subrepresentations with trivial action on the quotient gives a
step of the filtration of the descent sheaf whose quotient is the constant sheaf of a finite
`Λ`-module.** The quotient of `D(K₂)` by `D(K₁)` is `D(K₂/K₁)` by exactness of descent, and `H`
acts trivially on `K₂/K₁`. -/
theorem constantFiniteModuleStep_descentSubobject [IsNoetherianRing Λ] [Module.Finite Λ N]
    [ConnectedSpace G.cover.left] (K₁ K₂ : Subrepresentation ρ)
    (hle : K₁.toSubmodule ≤ K₂.toSubmodule)
    (htriv : ∀ (g : H) (x : N), x ∈ K₂.toSubmodule → ρ g x - x ∈ K₁.toSubmodule) :
    (descentSubobject G ρ Ψ K₁, descentSubobject G ρ Ψ K₂) ∈ ConstantFiniteModuleStep Λ B := by
  let L := K₁.toSubmodule.comap K₂.toSubmodule.subtype
  have hL : ∀ g, L ≤ L.comap (K₂.toRepresentation g) := fun g x hx ↦
    K₁.apply_mem_toSubmodule g hx
  let ρQ := K₂.toRepresentation.quotient L hL
  let φ := Submodule.inclusion hle
  have hφ : ∀ (h : H) (x : K₁.toSubmodule),
      φ (K₁.toRepresentation h x) = K₂.toRepresentation h (φ x) := fun _ _ ↦ rfl
  let ψ := L.mkQ
  have hψ : ∀ (h : H) (x : K₂.toSubmodule), ψ (K₂.toRepresentation h x) = ρQ h (ψ x) :=
    fun _ _ ↦ rfl
  have := mono_descentSheafMap_subtype G ρ K₁
  have := mono_descentSheafMap_subtype G ρ K₂
  obtain ⟨hmk, ⟨iso⟩⟩ := exists_cokernel_ofLE_iso_of_comm
    (u := G.descentSheafMap (ρ₁ := K₁.toRepresentation) (ρ₂ := ρ) K₁.toSubmodule.subtype
      (fun _ _ ↦ rfl) ≫ Ψ.hom)
    (v := G.descentSheafMap (ρ₁ := K₂.toRepresentation) (ρ₂ := ρ) K₂.toSubmodule.subtype
      (fun _ _ ↦ rfl) ≫ Ψ.hom)
    (G.descentSheafMap φ hφ) (by rfl)
  have hQtriv : ∀ g : H, ρQ g = 1 := fun g ↦ by
    refine LinearMap.ext fun y ↦ ?_
    induction y using Submodule.Quotient.induction_on with
    | H x =>
      change Submodule.Quotient.mk (K₂.toRepresentation g x) = Submodule.Quotient.mk x
      rw [Submodule.Quotient.eq]
      exact htriv g x x.2
  have hfin₂ : Module.Finite Λ K₂.toSubmodule :=
    Module.Finite.iff_fg.2 (IsNoetherian.noetherian (R := Λ) (M := N) _)
  obtain ⟨isoQ⟩ := G.nonempty_descentSheaf_iso_constantSheaf (K₂.toSubmodule ⧸ L) ρQ hQtriv
  refine ⟨hmk, ModuleCat.of Λ (K₂.toSubmodule ⧸ L), inferInstanceAs (Module.Finite Λ (_ ⧸ L)),
    ⟨iso ≪≫ G.cokernelDescentSheafMapIso φ hφ ψ hψ (Submodule.inclusion_injective hle)
      L.mkQ_surjective (fun y hy ↦ ?_) (fun x ↦ ?_) ≪≫ isoQ⟩⟩
  · exact ⟨⟨y, (Submodule.Quotient.mk_eq_zero L).1 hy⟩, rfl⟩
  · exact (Submodule.Quotient.mk_eq_zero L).2 x.2

/-- The subsheaf attached to the zero subrepresentation is zero. -/
theorem isZero_descentSubobject (K : Subrepresentation ρ)
    (hK : ∀ x ∈ K.toSubmodule, x = 0) :
    IsZero (Subobject.underlying.obj (descentSubobject G ρ Ψ K)) := by
  have : Subsingleton K.toSubmodule :=
    ⟨fun a b ↦ Subtype.ext ((hK a a.2).trans (hK b b.2).symm)⟩
  have := mono_descentSheafMap_subtype G ρ K
  exact (G.isZero_descentSheaf (ρ₁ := K.toRepresentation)).of_iso (Subobject.underlyingIso _)

/-- The subsheaf attached to the whole representation is the whole sheaf. -/
theorem isIso_descentSubobject_arrow (K : Subrepresentation ρ) (hK : ∀ x, x ∈ K.toSubmodule) :
    IsIso (descentSubobject G ρ Ψ K).arrow := by
  have := G.isIso_descentSheafMap (ρ₁ := K.toRepresentation) (ρ₂ := ρ) K.toSubmodule.subtype
    (fun _ _ ↦ rfl) ⟨K.toSubmodule.injective_subtype, fun x ↦ ⟨⟨x, hK x⟩, rfl⟩⟩
  have := mono_descentSheafMap_subtype G ρ K
  change IsIso (Subobject.mk _).arrow
  rw [← Subobject.underlyingIso_hom_comp_eq_mk]
  infer_instance

include Ψ in
/-- **The filtration of a descent sheaf along a Galois covering whose group is an `ℓ`-group.**
Tag 0GIZ filters `N` over the group ring of `H` with trivial action on every successive quotient,
and each step gives a step of the filtration of `D(N)` with constant quotient. -/
theorem exists_relSeries_constantFiniteModuleStep_descentSheaf [IsNoetherianRing Λ]
    [Module.Finite Λ N] [ConnectedSpace G.cover.left] [Finite H] (ℓ n : ℕ) (hℓ : ℓ.Prime)
    (hH : IsPGroup ℓ H) (hann : ∀ x : N, (ℓ ^ n) • x = 0) :
    ∃ X : RelSeries (ConstantFiniteModuleStep Λ B),
      IsZero (Subobject.underlying.obj X.head) ∧ IsIso X.last.arrow := by
  obtain ⟨Xs, hXhead, hXlast⟩ := Module.exists_relSeries_trivial_action_subquotient Λ H
    ρ.asModule ℓ n hℓ hH hann
  let K : Submodule (MonoidAlgebra Λ H) ρ.asModule → Subrepresentation ρ :=
    Subrepresentation.ofSubmodule'
  refine ⟨⟨Xs.length, fun i ↦ descentSubobject G ρ Ψ (K (Xs i)), fun j ↦ ?_⟩, ?_, ?_⟩
  · obtain ⟨hle, htriv⟩ := Xs.step j
    refine constantFiniteModuleStep_descentSubobject G ρ Ψ (K (Xs (Fin.castSucc j)))
      (K (Xs j.succ)) (fun x hx ↦ hle hx) fun g x hx ↦ ?_
    have e : MonoidAlgebra.single g (1 : Λ) • (⟨x, hx⟩ : Xs j.succ).1 =
        ρ.asModuleEquiv.symm (ρ g x) := by
      rw [Representation.single_smul, one_smul]
      rfl
    exact (congrArg (fun z ↦ z - (⟨x, hx⟩ : Xs j.succ).1 ∈ Xs (Fin.castSucc j)) e).mp
      (htriv g ⟨x, hx⟩)
  · refine isZero_descentSubobject G ρ Ψ _ fun x hx ↦ ?_
    have hx' : ρ.asModuleEquiv.symm x ∈ Xs.head := hx
    rw [hXhead] at hx'
    have hx0 := (Submodule.mem_bot (MonoidAlgebra Λ H)).1 hx'
    exact hx0
  · refine isIso_descentSubobject_arrow G ρ Ψ _ fun x ↦ ?_
    have hx' : ρ.asModuleEquiv.symm x ∈ Xs.last := by
      rw [hXlast]
      exact Submodule.mem_top
    exact hx'

end DescentFiltration

/-- **Stacks Project, Tag 0GJ0.** Let `S` be an irreducible, geometrically unibranch scheme, let
`ℓ` be a prime number, let `n ≥ 1`, let `Λ` be a Noetherian ring and let `F` be a finite type
locally constant sheaf of `Λ`-modules on `S_étale` annihilated by `ℓ ^ n`. Then there is a finite
étale morphism `f : T → S` of degree prime to `ℓ` such that `f⁻¹F` has a finite filtration whose
successive quotients are of the form `M_T` for finite `Λ`-modules `M`.

The filtration is a chain of subobjects of `f⁻¹F` running from the zero subobject to the whole
sheaf, each step having the constant sheaf of a finite `Λ`-module as its quotient. The degree of
`f` is the rank of the finite locally free morphism `f` (Tag 02KA). -/
@[stacks 0GJ0]
theorem exists_primeToEll_finiteEtale_finiteModuleFiltration_general {ℓ n : ℕ} (hℓ : ℓ.Prime)
    (_hn : 1 ≤ n) {Λ : Type v} [CommRing Λ] [IsNoetherianRing Λ]
    {S : Scheme.{u}} [IrreducibleSpace S] (hS : IsGeometricallyUnibranch S)
    (s : GeometricPoint S)
    (F : Sheaf (smallEtaleTopology S) (ModuleCat.{max (u + 1) v} Λ))
    (hF : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ (smallEtaleTopology S) F)
    (hann : ∀ (U : S.Etale) (x : F.obj.obj (Opposite.op U)), (ℓ ^ n) • x = 0) :
    ∃ (T : Scheme.{u}) (f : T ⟶ S) (d : ℕ), IsFinite f ∧ Etale f ∧
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank f d ∧ ¬ ℓ ∣ d ∧
      ∃ X : RelSeries (ConstantFiniteModuleStep Λ
          ((smallEtalePullbackModuleCat Λ f).obj F)),
        IsZero (Subobject.underlying.obj X.head) ∧ IsIso X.last.arrow := by
  classical
  -- `F` is constant, with finite value, on a pointed Galois cover `A`
  obtain ⟨A, M, hM, ⟨e⟩⟩ := AlgebraicGeometry.trivializedByPointedGaloisCovers hS s Λ F hF
  -- an `ℓ`-Sylow subgroup of its automorphism group and the quotient `T = A/H`
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨P⟩ : Nonempty (Sylow ℓ (Aut A.obj)) := inferInstance
  let H : Subgroup (Aut A.obj) := P
  let T := PreGaloisCategory.subgroupQuotient A.obj H
  let G := A.subgroupQuotientCovering hS H
  have : Etale T.hom := T.prop.2
  -- the restriction of `F` to `T` is constant on `A`
  let C := G.cover
  have : ConnectedSpace G.cover.left := A.connectedSpace
  let φA : (Scheme.Etale.smallEtaleCompose T.hom).obj C ≅
      (PointedGaloisCover.toEtale s).obj A :=
    MorphismProperty.Over.isoMk (Iso.refl _) (by
      change 𝟙 _ ≫ A.obj.hom = (PreGaloisCategory.subgroupQuotientι A.obj H).left ≫ T.hom
      rw [Category.id_comp]
      exact (MorphismProperty.Over.w (PreGaloisCategory.subgroupQuotientι A.obj H)).symm)
  let eT := overPullbackEtaleModuleRestrictionIso T.hom C
    (Stacks.ConstantSheaf.Localization.overPullbackIsoOfMap (smallEtaleTopology S)
      (ModuleCat.{max (u + 1) v} Λ) φA.hom F M e)
  -- so it is the descent sheaf of its sections `N` over `A`
  let RF := (etaleModuleRestriction.{u, v} Λ T.hom).obj F
  let N := RF.obj.obj (Opposite.op C)
  let ρ : Representation Λ H N := G.sectionsRepresentation RF
  obtain ⟨χ⟩ := G.nonempty_iso_descentSheaf eT
  let Ψ : G.descentSheaf Λ N ρ ≅ (smallEtalePullbackModuleCat Λ T.hom).obj F :=
    χ.symm ≪≫ ((etaleModuleInverseImageRestrictionIso.{u, v} Λ T.hom).app F).symm
  have : Module.Finite Λ N := Module.Finite.equiv
    ((e.sectionsEquiv hS).trans (F.obj.mapIso φA.op).toLinearEquiv)
  refine ⟨T.left, T.hom, Nat.card ((finiteEtaleFiberFunctor s).obj T), T.prop.1, T.prop.2,
    isFiniteLocallyFreeOfRank_natCard_finiteEtaleFiber s T, ?_,
    exists_relSeries_constantFiniteModuleStep_descentSheaf G ρ Ψ ℓ n hℓ P.isPGroup'
      fun x ↦ hann _ x⟩
  have hdeg : Nat.card ((finiteEtaleFiberFunctor s).obj T) = H.index :=
    PreGaloisCategory.natCard_fiber_subgroupQuotient A.obj H (finiteEtaleFiberFintypeFunctor S s)
  rw [hdeg]
  exact P.not_dvd_index

end Stacks.EtaleCohomology

end
