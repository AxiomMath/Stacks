module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.ConstantSheafModuleDictionaryEtaleSite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.SmallEtaleModuleUliftPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.SmallEtaleModuleUniverseDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.FiniteContinuousModuleRepresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.GroupRingContinuousModule
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategory.FiberGeometricPoint
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TransitiveFiberConnected
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.ContainsFiniteEtale

/-!
# The group-ring side of the dictionary of Stacks 0A3R

Stacks 0A3R translates a finite type locally constant sheaf of `F_ℓ`-vector spaces into a finite
`F_ℓ`-vector space with a continuous action of the étale fundamental group, filters the latter as
a module over the group ring of an `ℓ`-group, and translates back. This file supplies the
group-ring half of that translation: it reads a representation of a finite group `K` as a module
over the group ring, and computes what
`Stacks.GroupCohomology.groupRingFiniteTypeContinuousModule` does to it and to a module with
trivial action.

## Main definitions

* `Stacks.EtaleCohomology.asFiniteTypeGroupRingModule`: a representation of a finite group on a
  finite module over a finite ring, as a finitely generated module over the group ring.

## Main results

* `Stacks.EtaleCohomology.rho_eq_one_groupRingFiniteTypeContinuousModule` and
  `Stacks.EtaleCohomology.natCard_groupRingFiniteTypeContinuousModule`: a module over the group
  ring on which the group acts trivially gives a finite module with trivial continuous action, of
  the same cardinality.
* `Stacks.EtaleCohomology.nonempty_iso_groupRingFiniteTypeContinuousModule_res`: **the module over
  the group ring attached to a representation `τ` of `K` gives, after restriction along a
  homomorphism into `K`, the restriction of a finite continuous module whose representation is
  equivalent to `τ` read through that homomorphism.** This is the step that identifies the
  filtration of the group-ring module with a filtration of the stalk.
* `Stacks.EtaleCohomology.preservesFiniteLimits_finiteTypeLocallyConstantι` and its colimit
  companion: the inclusion of the finite type locally constant sheaves of `Λ`-modules into all
  sheaves is exact, which is Stacks 093U (3) read through
  `CategoryTheory.ObjectProperty.preservesKernels_ι`.
* `Stacks.EtaleCohomology.exists_pullbackFunctor_of_rep`: **the exact functor of Stacks 0A3R.**
  Given a finite type locally constant sheaf of `F_ℓ`-modules on a connected cover whose value
  under Stacks 0DV5 (3) is equivalent, as a representation, to a representation of a finite group
  `K` read through a homomorphism with open fibres, there is an exact functor from the finitely
  generated modules over `F_ℓ[K]` to the sheaves of `F_ℓ`-modules which carries the module of that
  representation to the sheaf and a module with `ℓ` elements and trivial action to the constant
  sheaf `Z/ℓZ`.
* `Stacks.EtaleCohomology.repEquivOfIso` and `Stacks.EtaleCohomology.repEquivComp`: an isomorphism
  of finite continuous modules is an equivalence of the representations they carry, and an
  equivalence of representations restricts along a homomorphism of groups.

## Implementation notes

The underlying module of the value of
`Stacks.GroupCohomology.groupRingFiniteTypeContinuousModule` is `Representation.ofModule` of the
group-ring module, and `Representation.ofModule_asAlgebraHom_apply_apply` evaluates it: the action
of `g` is multiplication by `MonoidAlgebra.single g 1`, read through
`RestrictScalars.addEquiv`. That is what makes the two computations above `rfl` on cardinalities
and short on actions.

The comparison with a continuous module goes through Mathlib's unit isomorphism
`Rep.equivalenceModuleMonoidAlgebra`: the module over the group ring attached to `τ` is
`Rep.toModuleMonoidAlgebra` of `Rep.of τ`, so reading it back as a representation returns `τ` up
to that unit. Composing with `CategoryTheory.Action.mkIso` on the linear equivalence underlying a
`Representation.Equiv` gives the isomorphism of actions, and the three full subcategory
inclusions are crossed by `CategoryTheory.ObjectProperty.isoMk`.

## References

* [Stacks Project, Tag 0A3R](https://stacks.math.columbia.edu/tag/0A3R)
* [Stacks Project, Tag 0DV5](https://stacks.math.columbia.edu/tag/0DV5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.ConstantSheaf
open Stacks.GroupCohomology

universe v u r w

namespace Stacks.EtaleCohomology

open scoped Stacks.DiscreteModuleTopology

section GroupRing

variable (Λ : Type r) [CommRing Λ] [Finite Λ] {K : Type w} [Group K] [Finite K]
  {V : Type w} [AddCommGroup V] [Module Λ V] [Finite V]

/-- **A representation of a finite group on a finite module over a finite ring, as a finitely
generated module over the group ring.** Over a finite ring a finitely generated module is a finite
set, so finite generation over the group ring is the finiteness of the underlying set. -/
def asFiniteTypeGroupRingModule (τ : Representation Λ K V) :
    (ModuleCat.isFG.{w} (MonoidAlgebra Λ K)).FullSubcategory :=
  ⟨ModuleCat.of (MonoidAlgebra Λ K) τ.asModule,
    (moduleCat_isFG_iff_finite (MonoidAlgebra Λ K) _).2
      (Finite.of_equiv V τ.asModuleEquiv.toEquiv.symm)⟩

variable {G : Type w} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The finite module with a continuous action attached to a module over the group ring has that
module as its underlying set. -/
theorem natCard_groupRingFiniteTypeContinuousModule (π : G →* K)
    (hπ : ∀ k : K, IsOpen {g : G | π g = k})
    (M : (ModuleCat.isFG.{w} (MonoidAlgebra Λ K)).FullSubcategory) :
    Nat.card (ToType ((groupRingFiniteTypeContinuousModule Λ π hπ).obj M).obj.obj.obj.V) =
      Nat.card (ToType M.obj) :=
  rfl

/-- **A module over the group ring on which the group acts trivially gives a finite module with
trivial continuous action.** -/
theorem rho_eq_one_groupRingFiniteTypeContinuousModule (π : G →* K)
    (hπ : ∀ k : K, IsOpen {g : G | π g = k})
    (M : (ModuleCat.isFG.{w} (MonoidAlgebra Λ K)).FullSubcategory)
    (htriv : ∀ (g : K) (m : ToType M.obj), MonoidAlgebra.single g (1 : Λ) • m = m) (σ : G) :
    ((groupRingFiniteTypeContinuousModule Λ π hπ).obj M).obj.obj.obj.ρ σ = 1 := by
  have key : ∀ m : RestrictScalars Λ (MonoidAlgebra Λ K) (ToType M.obj),
      (Representation.ofModule (k := Λ) (G := K) (ToType M.obj)) (π σ) m = m := by
    intro m
    have h := Representation.ofModule_asAlgebraHom_apply_apply (k := Λ) (G := K)
      (ToType M.obj) (MonoidAlgebra.single (π σ) 1) m
    rw [Representation.asAlgebraHom_single, one_smul] at h
    rw [h, htriv (π σ) _]
    exact (RestrictScalars.addEquiv Λ (MonoidAlgebra Λ K) (ToType M.obj)).symm_apply_apply m
  exact End.ext (ModuleCat.hom_ext (LinearMap.ext key))

/-- The action attached to the module over the group ring of a representation `τ` is `τ` itself,
read through Mathlib's unit isomorphism for `Rep.equivalenceModuleMonoidAlgebra`. -/
def actionOfAsFiniteTypeGroupRingModuleIso (τ : Representation Λ K V) :
    (moduleMonoidAlgebraActionEquivalence Λ K).functor.obj
        (asFiniteTypeGroupRingModule Λ τ).obj ≅
      actionOfRepresentation Λ K V τ :=
  (Rep.RepToAction Λ K).mapIso
    (Rep.equivalenceModuleMonoidAlgebra.unitIso.app (Rep.of τ)).symm

/-- **The module over the group ring attached to a representation `τ` of `K`, restricted along a
homomorphism `π : G → K`, is the restriction of a finite continuous module whose representation is
equivalent to `τ ∘ π`.** -/
theorem nonempty_iso_groupRingFiniteTypeContinuousModule_res (π : G →* K)
    (hπ : ∀ k : K, IsOpen {g : G | π g = k}) (τ : Representation Λ K V)
    (N : FiniteTypeContinuousModule.{r, w, w} Λ G)
    (e : Representation.Equiv (τ.comp π) (Stacks.ContinuousCohomology.rep Λ G N.obj)) :
    Nonempty ((groupRingFiniteTypeContinuousModule Λ π hπ).obj
      (asFiniteTypeGroupRingModule Λ τ) ≅ N) := by
  refine ⟨ObjectProperty.isoMk _ (ObjectProperty.isoMk _ (ObjectProperty.isoMk _
    ((Action.res (ModuleCat.{w} Λ) π).mapIso (actionOfAsFiniteTypeGroupRingModuleIso Λ τ) ≪≫
      Action.mkIso e.toLinearEquiv.toModuleIso fun g ↦ ?_)))⟩
  exact ModuleCat.hom_ext (e.isIntertwining' g)

end GroupRing

/-! ### The exact functor from the group ring to sheaves on the cover -/

section Sheaves

attribute [local instance] ModuleCat.hasLimitsOfSize

/-- Sheafification of presheaves of `Λ`-modules on a slice of Mathlib's small étale site, at the
module universe `u + 1`. -/
public instance hasWeakSheafifyOverEtale (X : Scheme.{u}) (Λ : Type r) [Ring Λ] (W : X.Etale) :
    HasWeakSheafify (X.smallEtaleTopology.over W) (ModuleCat.{u + 1} Λ) :=
  letI := hasSheafify_over_moduleCat.{u + 1, u, r, u + 1} X.smallEtaleTopology Λ W
  inferInstance

/-- Sheafification of presheaves of `Λ`-modules on Mathlib's small étale site, at the module
universe `u + 1`. -/
public instance hasSheafifyEtale (X : Scheme.{u}) (Λ : Type r) [Ring Λ] :
    HasSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  hasSheafify_moduleCat.{u + 1, u, r, u + 1} _ _

/-- The two spellings of local constancy of finite type on Mathlib's small étale site at the
module universe `u + 1` are the same predicate: `Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant`
is the free-universe form and `Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf` the
one whose weak Serre class instance of Stacks 093U (3) is registered. -/
theorem isFiniteTypeLocallyConstant_eq_moduleSheaf (X : Scheme.{u}) (Λ : Type r) [Ring Λ] :
    (fun A : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ↦
        IsFiniteTypeLocallyConstant Λ X.smallEtaleTopology A) =
      IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, u + 1, r} X.smallEtaleTopology Λ :=
  rfl

/-- **The inclusion of the finite type locally constant sheaves of `Λ`-modules into all sheaves
preserves finite limits.** They are a weak Serre class by Stacks 093U (3), hence in particular
closed under subobjects, and `CategoryTheory.ObjectProperty.preservesKernels_ι` applies. -/
theorem preservesFiniteLimits_finiteTypeLocallyConstantι (X : Scheme.{u}) (Λ : Type r) [Ring Λ]
    [IsNoetherianRing Λ] :
    PreservesFiniteLimits
      (ObjectProperty.ι
        (fun A : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ↦
          IsFiniteTypeLocallyConstant Λ X.smallEtaleTopology A)) := by
  rw [isFiniteTypeLocallyConstant_eq_moduleSheaf X Λ]
  have {A A' : ObjectProperty.FullSubcategory
      (IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, u + 1, r} X.smallEtaleTopology Λ)}
      (f : A ⟶ A') :=
    ObjectProperty.preservesKernels_ι
      (IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, u + 1, r} X.smallEtaleTopology Λ) f
  exact Functor.preservesFiniteLimits_of_preservesKernels _

/-- **The inclusion of the finite type locally constant sheaves of `Λ`-modules into all sheaves
preserves finite colimits.** -/
theorem preservesFiniteColimits_finiteTypeLocallyConstantι (X : Scheme.{u}) (Λ : Type r) [Ring Λ]
    [IsNoetherianRing Λ] :
    PreservesFiniteColimits
      (ObjectProperty.ι
        (fun A : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ↦
          IsFiniteTypeLocallyConstant Λ X.smallEtaleTopology A)) := by
  rw [isFiniteTypeLocallyConstant_eq_moduleSheaf X Λ]
  have {A A' : ObjectProperty.FullSubcategory
      (IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, u + 1, r} X.smallEtaleTopology Λ)}
      (f : A ⟶ A') :=
    ObjectProperty.preservesCokernels_ι
      (IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, u + 1, r} X.smallEtaleTopology Λ) f
  exact Functor.preservesFiniteColimits_of_preservesCokernels _

variable {ℓ : ℕ} [NeZero ℓ] (B : BigEtaleSite.{u}) (XT : B.Scheme) [ConnectedSpace XT.obj]
  (t : GeometricPoint XT.obj)

/-- **The exact functor of Stacks 0A3R from the modules over the group ring to the sheaves on the
cover.** Given a finite type locally constant sheaf `A` of `F_ℓ`-modules on the small étale site
of `XT` whose value under the dictionary of Stacks 0DV5 (3) is, as a representation, equivalent to
a representation `τ` of a finite group `K` read through `π' : π₁(XT, t) → K`, there is an exact
functor from the finitely generated modules over `F_ℓ[K]` to the sheaves of `F_ℓ`-modules on `XT`
which carries the module attached to `τ` to `A`, and a module with `ℓ` elements and trivial action
to the constant sheaf `Z/ℓZ`. -/
theorem exists_pullbackFunctor_of_rep (hℓ : ℓ.Prime)
    (A : ObjectProperty.FullSubcategory
      (fun A : Sheaf XT.obj.smallEtaleTopology (ModuleCat.{u + 1} (ZMod ℓ)) ↦
        IsFiniteTypeLocallyConstant (ZMod ℓ) XT.obj.smallEtaleTopology A))
    (K : Type (u + 1)) [Group K] [Finite K]
    (π' : EtaleFundamentalGroup XT.obj t →* K)
    (hπ' : ∀ k : K, IsOpen {σ : EtaleFundamentalGroup XT.obj t | π' σ = k})
    {V : Type (u + 1)} [AddCommGroup V] [Module (ZMod ℓ) V] [Finite V]
    (τ : Representation (ZMod ℓ) K V)
    (e : Representation.Equiv (τ.comp π')
      (Stacks.ContinuousCohomology.rep (ZMod ℓ) (EtaleFundamentalGroup XT.obj t)
        ((finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B XT t (ZMod ℓ)).functor.obj
          A).obj)) :
    ∃ Φ : (ModuleCat.isFG.{u + 1} (MonoidAlgebra (ZMod ℓ) K)).FullSubcategory ⥤
        Sheaf XT.obj.smallEtaleTopology (ModuleCat.{max (u + 1) v} (ZMod ℓ)),
      PreservesFiniteLimits Φ ∧ PreservesFiniteColimits Φ ∧
        Nonempty (Φ.obj (asFiniteTypeGroupRingModule (ZMod ℓ) τ) ≅
          (sheafCompose XT.obj.smallEtaleTopology
            (ModuleCat.uliftFunctor.{v, u + 1} (ZMod ℓ))).obj A.obj) ∧
        ∀ W : (ModuleCat.isFG.{u + 1} (MonoidAlgebra (ZMod ℓ) K)).FullSubcategory,
          Nat.card (ToType W.obj) = ℓ →
          (∀ (g : K) (w : ToType W.obj), MonoidAlgebra.single g (1 : ZMod ℓ) • w = w) →
          Nonempty (Φ.obj W ≅
            (constantSheaf XT.obj.smallEtaleTopology
                (ModuleCat.{max (u + 1) v} (ZMod ℓ))).obj
              (ModuleCat.of (ZMod ℓ) (ULift.{max (u + 1) v} (ZMod ℓ)))) := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  set D := finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B XT t (ZMod ℓ) with hD
  set Ψ := groupRingFiniteTypeContinuousModule (ZMod ℓ) π' hπ' with hΨ
  set U := sheafCompose XT.obj.smallEtaleTopology (ModuleCat.uliftFunctor.{v, u + 1} (ZMod ℓ))
    with hU
  have key {W A'} (i : Ψ.obj W ≅ D.functor.obj A') :
      (Ψ ⋙ D.inverse ⋙ ObjectProperty.ι _ ⋙ U).obj W ≅ U.obj A'.obj :=
    U.mapIso ((ObjectProperty.ι _).mapIso (D.inverse.mapIso i ≪≫ (D.unitIso.app A').symm))
  refine ⟨Ψ ⋙ D.inverse ⋙ ObjectProperty.ι _ ⋙ U, ?_, ?_, ?_, ?_⟩
  · have h₁ := preservesFiniteLimits_groupRingFiniteTypeContinuousModule (ZMod ℓ) π' hπ'
    have h₂ : PreservesFiniteLimits D.inverse := inferInstance
    have h₃ := preservesFiniteLimits_finiteTypeLocallyConstantι.{u, 0} XT.obj (ZMod ℓ)
    have h₄ := preservesFiniteLimits_sheafCompose_smallEtale_moduleUliftFunctor.{v} XT.obj (ZMod ℓ)
    exact comp_preservesFiniteLimits _ _
  · have h₁ := preservesFiniteColimits_groupRingFiniteTypeContinuousModule (ZMod ℓ) π' hπ'
    have h₂ : PreservesFiniteColimits D.inverse := inferInstance
    have h₃ := preservesFiniteColimits_finiteTypeLocallyConstantι.{u, 0} XT.obj (ZMod ℓ)
    have h₄ :=
      preservesFiniteColimits_sheafCompose_smallEtale_moduleUliftFunctor.{v} XT.obj (ZMod ℓ)
    exact comp_preservesFiniteColimits _ _
  · obtain ⟨i⟩ := nonempty_iso_groupRingFiniteTypeContinuousModule_res (ZMod ℓ) π' hπ' τ
      (D.functor.obj A) e
    exact ⟨key i⟩
  · intro W hcard htriv
    have hMc : Nat.card (ToType (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ)))) = ℓ := by
      change Nat.card (ULift.{u + 1} (ZMod ℓ)) = ℓ
      rw [Nat.card_ulift, Nat.card_zmod]
    have : Finite (ToType (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ)))) :=
      inferInstance
    obtain ⟨i⟩ := nonempty_iso_of_rho_eq_one_of_natCard_eq
      (EtaleFundamentalGroup XT.obj t) (ZMod ℓ) (Ψ.obj W)
      (D.functor.obj (constantSheafFiniteTypeLocallyConstantModuleEtaleSite B XT (ZMod ℓ)
        (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ)))))
      (rho_eq_one_groupRingFiniteTypeContinuousModule (ZMod ℓ) π' hπ' W htriv)
      (rho_eq_one_moduleSheafEquivalenceEtaleSite_constantSheaf B XT (ZMod ℓ) t _)
      (by
        rw [hΨ, natCard_groupRingFiniteTypeContinuousModule, hcard,
          natCard_moduleSheafEquivalenceEtaleSite_constantSheaf, hMc])
    have hlift : Nat.card (ULift.{v} (ULift.{u + 1} (ZMod ℓ))) =
        Nat.card (ULift.{max (u + 1) v} (ZMod ℓ)) := by
      simp
    obtain ⟨eU⟩ := Module.nonempty_linearEquiv_of_natCard_eq (ZMod ℓ)
      (ULift.{v} (ULift.{u + 1} (ZMod ℓ))) (ULift.{max (u + 1) v} (ZMod ℓ)) hlift
    refine ⟨key i ≪≫ ?_⟩
    exact (constantCommuteCompose XT.obj.smallEtaleTopology
        (ModuleCat.uliftFunctor.{v, u + 1} (ZMod ℓ))).app
        (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ))) ≪≫
      (constantSheaf XT.obj.smallEtaleTopology
        (ModuleCat.{max (u + 1) v} (ZMod ℓ))).mapIso eU.toModuleIso

end Sheaves

/-! ### Transport of a representation along an isomorphism and along a homomorphism -/

section RepresentationTransport

variable (Λ : Type r) [CommRing Λ] (G : Type w) [Group G] [TopologicalSpace G]

/-- **An isomorphism of finite modules with a continuous action is an equivalence of the
representations they carry.** -/
def repEquivOfIso {A A' : FiniteTypeContinuousModule.{r, w, w} Λ G} (i : A ≅ A') :
    Representation.Equiv (Stacks.ContinuousCohomology.rep Λ G A.obj)
      (Stacks.ContinuousCohomology.rep Λ G A'.obj) :=
  Representation.Equiv.mk (isoV Λ G i).toLinearEquiv
    fun g ↦ ModuleCat.hom_ext_iff.1 (i.hom.hom.hom.hom.comm g)

/-- An equivalence of representations restricts along a homomorphism of groups. -/
def repEquivComp {H : Type w} [Group H] {W W' : Type w} [AddCommGroup W] [Module Λ W]
    [AddCommGroup W'] [Module Λ W'] {ρ : Representation Λ H W} {σ : Representation Λ H W'}
    (i : Representation.Equiv ρ σ) (φ : G →* H) :
    Representation.Equiv (ρ.comp φ) (σ.comp φ) :=
  Representation.Equiv.mk i.toLinearEquiv fun g ↦ i.isIntertwining' (φ g)

end RepresentationTransport

end Stacks.EtaleCohomology

end
