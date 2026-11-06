module

public import StacksFrontier.Deformation.Artin.Basic
public import StacksFrontier.Deformation.Examples.Geometric.Base
public import StacksFrontier.Deformation.Examples.Linear.ContinuousRepresentationsDenseRestriction
public import StacksFrontier.Deformation.Examples.Linear.ContinuousRepresentationsRimSchlessinger
public import StacksFrontier.Deformation.Representation.InfinitesimalAutomorphisms

/-!
# Infinitesimal automorphisms of a continuous representation

Let `Γ` be a topological group and `ρ₀ : Γ → GL_k(V)` a finite-dimensional continuous
representation. Then the infinitesimal automorphism group of the deformation category of
Stacks 0D3K is `H⁰(Γ, End_k(V))`.

The mechanism is the one of Stacks 0DVT. Let `M` be the module of a continuous deformation of
`(V, ρ₀)` over the dual numbers, so `M` is finite free over `k[ε]` with `M/εM = V`. An element
of the infinitesimal automorphism group is an automorphism `γ : M → M` over `k[ε]`, compatible
with the reduction to `V` and commuting with the action of `Γ`. Writing `γ = id + ε ψ` with
`ψ` an endomorphism of `V`, commutation with `Γ` says exactly that `ψ` is `Γ`-equivariant, and
composition of two such automorphisms adds the corresponding `ψ` because `ε² = 0`. The
`Γ`-equivariant endomorphisms of `V` are the invariants of the conjugation representation
`Representation.linHom ρ₀ ρ₀`, that is `H⁰(Γ, End_k(V))`.

## Implementation notes

The category of Stacks 0D3K is a full subcategory of the category of Stacks 0D3J, so a
morphism of continuous representations is a morphism of representations and continuity plays
no part in the computation: the automorphism group of a continuous deformation in its fibre is
the automorphism group of the underlying deformation. Accordingly the module-level input is
taken unchanged from Stacks 0DVT — the first-order reduction data `IsFirstOrderReduction` and
the endomorphisms `Deformation.epsEndo` — and only the categorical plumbing is redone for the
full subcategory.

In degree zero the continuous cochain complex of Stacks 0DVE agrees with the ordinary one: a
`0`-cochain is a single element of the coefficient module, with no continuity condition, so
`H⁰` is the group of invariants either way. Hence the target below is Mathlib's
`groupCohomology … 0` of the conjugation representation, exactly as in Stacks 0DVT, and it is
at the same time the continuous `H⁰(Γ, End_k(V))` of Stacks 0DVW.

The condition defining the infinitesimal automorphism group of Stacks 06JQ — commuting with
the canonical map back to the special fibre — is automatic here: the object of the deformation
category over the residue field is a terminal object of that category, since the residue field
is terminal in `𝒞_Λ` and a morphism over an isomorphism in a category cofibered in groupoids
is an isomorphism. So the group is the full automorphism group of the chosen pushforward in its
fibre.

## Main results

All in the namespace `Deformation.Examples.FiniteProjectiveRepresentation`.

* `continuousInfinitesimalAutomorphismsEquivH0`: the infinitesimal automorphisms of the
  deformation category of a finite-dimensional continuous representation are `H⁰(Γ, End_k(V))`.
* `continuousAutEquivInvariants`: the underlying computation of the automorphism group of a
  first-order continuous deformation.
* `finiteDimensional_continuousTangentSpace`: the tangent space of that deformation category is
  finite dimensional when `Γ` is topologically finitely generated.

## References

* [Stacks Project, Tag 0DVW](https://stacks.math.columbia.edu/tag/0DVW)
* [Stacks Project, Tag 0DVT](https://stacks.math.columbia.edu/tag/0DVT)
* [Stacks Project, Tag 0D3K](https://stacks.math.columbia.edu/tag/0D3K)
-/

@[expose] public section

open CategoryTheory

namespace Deformation.Examples.FiniteProjectiveRepresentation

universe u w

variable {Λ : Type u} {k Γ : Type w} [CommRing Λ] [Field k] [Algebra Λ k] [Group Γ]
  [TopologicalSpace Γ]

/-- The coefficient algebra of a continuous deformation of `ρ₀`, as a functor from the
deformation category of Stacks 0D3K to `𝒞_Λ`. -/
public noncomputable abbrev continuousDeformationProjection
    (V : Type w) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ₀ : Representation k Γ V) (hρ₀ : IsContinuousRepresentation ρ₀) :
    continuousDeformationCategory (Λ := Λ) V ρ₀ hρ₀ ⥤ ArtinianLocalAlgCat.{u, w, w} Λ k :=
  objectsOverFunctor (continuousProjection.{u, w, w, w} (Λ := Λ) (k := k) (Γ := Γ))
    (continuousSpecialFiber (Λ := Λ) V ρ₀ hρ₀)

/-- The deformation category of a finite-dimensional continuous representation is cofibered in
groupoids over the category of Artinian local coefficient algebras. -/
public theorem continuousDeformationProjection_isCofiberedInGroupoids
    (V : Type w) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ₀ : Representation k Γ V) (hρ₀ : IsContinuousRepresentation ρ₀) :
    IsCofiberedInGroupoids (continuousDeformationProjection (Λ := Λ) V ρ₀ hρ₀) :=
  isCofiberedInGroupoids_overForget
    (satisfiesRS_continuousProjection_carrierUniverse.{u, w, w, w}
      (Λ := Λ) (k := k) (Γ := Γ)).1
    (continuousSpecialFiber (Λ := Λ) V ρ₀ hρ₀) (isTerminal_residueFieldBase (Λ := Λ) (k := k))

/-- An object of the deformation category of a continuous representation lying over a terminal
coefficient algebra is a terminal object of that deformation category. -/
public noncomputable def isTerminal_continuousDeformation
    (V : Type w) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ₀ : Representation k Γ V) (hρ₀ : IsContinuousRepresentation ρ₀)
    (z : continuousDeformationCategory (Λ := Λ) V ρ₀ hρ₀)
    (hz : Limits.IsTerminal z.left.obj.base) : Limits.IsTerminal z := by
  have hbase : IsIso ((continuousProjection.{u, w, w, w}
      (Λ := Λ) (k := k) (Γ := Γ)).map z.hom) :=
    isIso_of_isTerminal hz (isTerminal_residueFieldBase (Λ := Λ) (k := k)) _
  have hiso : IsIso z.hom :=
    isIso_of_isCofiberedInGroupoids_of_map_isIso
      (satisfiesRS_continuousProjection_carrierUniverse.{u, w, w, w}
        (Λ := Λ) (k := k) (Γ := Γ)).1 z.hom
  exact Limits.IsTerminal.ofIso Over.mkIdTerminal
    (Over.isoMk (asIso z.hom) (by simp)).symm

/-- In the deformation category of a continuous representation, the infinitesimal automorphism
group at a chosen pushforward over the dual numbers is the whole automorphism group of that
pushforward in its fibre: the condition of commuting with the map back to the special fibre is
automatic, because the special fibre is terminal. -/
public theorem continuousInfinitesimalAutomorphisms_eq_top
    (V : Type w) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ₀ : Representation k Γ V) (hρ₀ : IsContinuousRepresentation ρ₀)
    {A₀ Aε : ArtinianLocalAlgCat.{u, w, w} Λ k}
    {x₀ : (continuousDeformationProjection (Λ := Λ) V ρ₀ hρ₀).Fiber A₀}
    {xε : (continuousDeformationProjection (Λ := Λ) V ρ₀ hρ₀).Fiber Aε}
    (g : A₀ ⟶ Aε) (e : Aε ⟶ A₀) (hpair : IsCanonicalDualNumberPair g e)
    (i : x₀.1 ⟶ xε.1)
    (hi : (continuousDeformationProjection (Λ := Λ) V ρ₀ hρ₀).IsHomLift g i) :
    infinitesimalAutomorphisms
      (continuousDeformationProjection_isCofiberedInGroupoids (Λ := Λ) V ρ₀ hρ₀)
      g e hpair i hi = ⊤ := by
  have hmax : IsLocalRing.maximalIdeal A₀ = ⊥ := by
    obtain ⟨i₀, -, -, -, -⟩ := hpair
    rw [← IsLocalRing.isField_iff_maximalIdeal_eq]
    exact MulEquiv.isField (Field.toIsField k) i₀.toMulEquiv
  have hA₀ : Limits.IsTerminal A₀ :=
    ArtinianLocalAlgCat.isTerminal_of_maximalIdeal_eq_bot A₀ hmax
  have hx₀base : Limits.IsTerminal x₀.1.left.obj.base := by
    rw [show x₀.1.left.obj.base = A₀ from x₀.2]
    exact hA₀
  have hterm : Limits.IsTerminal x₀.1 :=
    isTerminal_continuousDeformation (Λ := Λ) V ρ₀ hρ₀ x₀.1 hx₀base
  rw [Subgroup.eq_top_iff']
  intro a
  rw [mem_infinitesimalAutomorphisms_iff]
  exact hterm.hom_ext _ _

/-- A continuous deformation of `(V, ρ₀)` over a coefficient algebra isomorphic to the dual
numbers exhibits `V` as a first-order reduction of its module. -/
public theorem exists_isFirstOrderReduction_continuousDeformation
    (V : Type w) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ₀ : Representation k Γ V) (hρ₀ : IsContinuousRepresentation ρ₀)
    {Aε : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (xε : (continuousDeformationProjection (Λ := Λ) V ρ₀ hρ₀).Fiber Aε)
    (hNE : Nonempty (xε.1.left.obj.base ≃ₐ[Λ] DualNumber k)) :
    ∃ eps : xε.1.left.obj.base,
      IsFirstOrderReduction (κ := k) (V := V) eps
        xε.1.hom.hom.base.hom.toRingHom xε.1.hom.hom.map := by
  classical
  obtain ⟨eps, hpi, hmul⟩ := ArtinianLocalAlgCat.exists_eps hNE
    (IsLocalRing.maximalIdeal_eq_bot (R := k)) xε.1.hom.hom.base
  refine ⟨eps, ?_⟩
  have : Module.Free xε.1.left.obj.base xε.1.left.obj.carrier :=
    Module.free_of_flat_of_isLocalRing
  let bM := Module.Free.chooseBasis xε.1.left.obj.base xε.1.left.obj.carrier
  have : Finite (Module.Free.ChooseBasisIndex xε.1.left.obj.base
      xε.1.left.obj.carrier) := Module.Finite.finite_basis bM
  let pi : xε.1.left.obj.base →+* k := xε.1.hom.hom.base.hom.toRingHom
  let psi : xε.1.left.obj.carrier →+ V := xε.1.hom.hom.map
  have hsmul : ∀ (a : xε.1.left.obj.base) (mm : xε.1.left.obj.carrier),
      psi (a • mm) = pi a • psi mm := xε.1.hom.hom.map_smul
  let : Algebra xε.1.left.obj.base k := pi.toAlgebra
  let : Module xε.1.left.obj.base V := Module.compHom V pi
  have : IsScalarTower xε.1.left.obj.base k V :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have hbc : IsBaseChange (k : Type w) (restrictAddHom pi psi hsmul) :=
    xε.1.hom.hom.isBaseChange
  let bV : Module.Basis _ k V := (bM.baseChange (k : Type w)).map hbc.equiv
  have hbV : ∀ j, bV j = xε.1.hom.hom.map (bM j) := by
    intro j
    change hbc.equiv ((bM.baseChange (k : Type w)) j) = _
    rw [Module.Basis.baseChange_apply, IsBaseChange.equiv_tmul, one_smul]
    rfl
  exact isFirstOrderReduction_of_basis bM bV hpi hmul
    (ArtinianLocalAlgCat.hom_surjective _ _
      (IsLocalRing.maximalIdeal_eq_bot (R := k)) xε.1.hom.hom.base)
    xε.1.hom.hom.map_smul hbV

/-- The automorphism group of a first-order continuous deformation of `(V, ρ₀)` in its fibre is
the multiplicative presentation of the `Γ`-equivariant endomorphisms of `V`: an automorphism is
`id + ε φ` for a unique `φ`, and composition adds the `φ`'s. -/
public noncomputable def continuousAutEquivInvariants
    (V : Type w) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ₀ : Representation k Γ V) (hρ₀ : IsContinuousRepresentation ρ₀)
    {Aε : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (xε : (continuousDeformationProjection (Λ := Λ) V ρ₀ hρ₀).Fiber Aε)
    (eps : xε.1.left.obj.base)
    (hfo : IsFirstOrderReduction (κ := k) (V := V) eps
      xε.1.hom.hom.base.hom.toRingHom xε.1.hom.hom.map) :
    Aut xε ≃* Multiplicative ↥((Representation.linHom ρ₀ ρ₀).invariants) := by
  classical
  have hequiv : ∀ φ : ↥((Representation.linHom ρ₀ ρ₀).invariants),
      ∀ (γ : Γ) (mm : xε.1.left.obj.carrier),
        epsEndo hfo φ.1 (xε.1.left.obj.action γ mm) =
          xε.1.left.obj.action γ (epsEndo hfo φ.1 mm) := fun φ ↦
    (epsEndo_equivariant_iff hfo xε.1.left.obj.action ρ₀
      xε.1.hom.hom.equivariant φ.1).mpr
      ((mem_invariants_linHom_iff ρ₀ φ.1).mp φ.2)
  let mkHom : ↥((Representation.linHom ρ₀ ρ₀).invariants) →
      (xε.1.left.obj ⟶ xε.1.left.obj) := fun φ ↦
    { base := 𝟙 xε.1.left.obj.base
      map := (epsEndo hfo φ.1).toAddMonoidHom
      map_smul := fun r mm ↦ (epsEndo hfo φ.1).map_smul r mm
      equivariant := hequiv φ
      isBaseChange := IsBaseChange.ofEquiv
        (LinearEquiv.ofBijective (epsEndo hfo φ.1) (epsEndo_bijective hfo φ.1)) }
  let mkSub : ↥((Representation.linHom ρ₀ ρ₀).invariants) →
      (xε.1.left ⟶ xε.1.left) := fun φ ↦ ObjectProperty.homMk (mkHom φ)
  let mkOver : ↥((Representation.linHom ρ₀ ρ₀).invariants) → (xε.1 ⟶ xε.1) := fun φ ↦
    Over.homMk (mkSub φ) (ObjectProperty.hom_ext _
      (FiniteProjectiveRepresentation.Hom.ext (Category.id_comp _)
        (AddMonoidHom.ext fun mm ↦ map_epsEndo hfo φ.1 mm)))
  have hlift : ∀ φ : ↥((Representation.linHom ρ₀ ρ₀).invariants),
      (continuousDeformationProjection (Λ := Λ) V ρ₀ hρ₀).IsHomLift (𝟙 Aε) (mkOver φ) := by
    intro φ
    refine IsHomLift.of_fac' _ (𝟙 Aε) (mkOver φ) xε.2 xε.2 ?_
    have hid : (continuousDeformationProjection (Λ := Λ) V ρ₀ hρ₀).map (mkOver φ) =
        𝟙 ((continuousDeformationProjection (Λ := Λ) V ρ₀ hρ₀).obj xε.1) := rfl
    rw [hid, Category.id_comp, eqToHom_trans, eqToHom_refl]
  let mkFib : ↥((Representation.linHom ρ₀ ρ₀).invariants) → (xε ⟶ xε) := fun φ ↦
    ⟨mkOver φ, hlift φ⟩
  have hcomp : ∀ (φ φ' : ↥((Representation.linHom ρ₀ ρ₀).invariants)),
      mkFib φ ≫ mkFib φ' = mkFib (φ + φ') := by
    intro φ φ'
    refine Subtype.ext (Over.OverMorphism.ext (ObjectProperty.hom_ext _
      (FiniteProjectiveRepresentation.Hom.ext (Category.id_comp _)
        (AddMonoidHom.ext fun mm ↦ ?_))))
    change epsEndo hfo φ'.1 (epsEndo hfo φ.1 mm) = epsEndo hfo (φ + φ').1 mm
    rw [epsEndo_epsEndo hfo]
    change epsEndo hfo (φ'.1 + φ.1) mm = epsEndo hfo (φ.1 + φ'.1) mm
    rw [add_comm]
  have hzero : mkFib 0 = 𝟙 xε := by
    refine Subtype.ext (Over.OverMorphism.ext (ObjectProperty.hom_ext _
      (FiniteProjectiveRepresentation.Hom.ext rfl (AddMonoidHom.ext fun mm ↦ ?_))))
    exact epsEndo_zero hfo mm
  let F : Multiplicative ↥((Representation.linHom ρ₀ ρ₀).invariants) →* Aut xε :=
    { toFun := fun x ↦ Aut.of
        { hom := mkFib (Multiplicative.toAdd x)
          inv := mkFib (-Multiplicative.toAdd x)
          hom_inv_id := by rw [hcomp, add_neg_cancel, hzero]
          inv_hom_id := by rw [hcomp, neg_add_cancel, hzero] }
      map_one' := Aut.ext (Iso.ext hzero)
      map_mul' := fun x y ↦ Aut.ext (Iso.ext (by
        change mkFib (Multiplicative.toAdd x + Multiplicative.toAdd y) =
          mkFib (Multiplicative.toAdd y) ≫ mkFib (Multiplicative.toAdd x)
        rw [hcomp, add_comm])) }
  have hFhom : ∀ (x : Multiplicative ↥((Representation.linHom ρ₀ ρ₀).invariants))
      (mm : xε.1.left.obj.carrier), (F x).asIso.hom.1.left.hom.map mm =
        epsEndo hfo (Multiplicative.toAdd x).1 mm := fun _ _ ↦ rfl
  have hinj : Function.Injective F := by
    intro x y hxy
    refine Multiplicative.toAdd.injective (Subtype.ext (epsEndo_inj hfo fun mm ↦ ?_))
    rw [← hFhom x mm, ← hFhom y mm, hxy]
  have hsurj : Function.Surjective F := by
    intro a
    have := a.asIso.hom.2
    have hub : a.asIso.hom.1.left.hom.base = 𝟙 xε.1.left.obj.base := by
      have hfac := IsHomLift.fac'
        (continuousDeformationProjection (Λ := Λ) V ρ₀ hρ₀) (𝟙 Aε) a.asIso.hom.1
      have h2 : (continuousDeformationProjection (Λ := Λ) V ρ₀ hρ₀).map a.asIso.hom.1 =
          𝟙 ((continuousDeformationProjection (Λ := Λ) V ρ₀ hρ₀).obj xε.1) := by
        simp only [Category.id_comp, eqToHom_trans, eqToHom_refl] at hfac
        simpa using hfac
      exact h2
    let χ : xε.1.left.obj.carrier →ₗ[xε.1.left.obj.base] xε.1.left.obj.carrier :=
      { toFun := a.asIso.hom.1.left.hom.map
        map_add' := a.asIso.hom.1.left.hom.map.map_add
        map_smul' := fun r mm ↦ by
          change a.asIso.hom.1.left.hom.map (r • mm) = r • a.asIso.hom.1.left.hom.map mm
          rw [a.asIso.hom.1.left.hom.map_smul, hub]
          rfl }
    have hχψ : ∀ mm, xε.1.hom.hom.map (χ mm) = xε.1.hom.hom.map mm := fun mm ↦
      congrArg
        (fun q : FiniteProjectiveRepresentation.Hom xε.1.left.obj
          (continuousSpecialFiber (Λ := Λ) V ρ₀ hρ₀).obj ↦ q.map mm)
        (congrArg (fun q : xε.1.left ⟶ (continuousSpecialFiber (Λ := Λ) V ρ₀ hρ₀) ↦ q.hom)
          (Over.w a.asIso.hom.1))
    obtain ⟨φ, hφ⟩ := exists_epsEndo hfo χ hχψ
    have hφinv : φ ∈ (Representation.linHom ρ₀ ρ₀).invariants := by
      rw [mem_invariants_linHom_iff]
      refine (epsEndo_equivariant_iff hfo xε.1.left.obj.action ρ₀
        xε.1.hom.hom.equivariant φ).mp fun γ mm ↦ ?_
      rw [← hφ, ← hφ]
      exact a.asIso.hom.1.left.hom.equivariant γ mm
    refine ⟨Multiplicative.ofAdd ⟨φ, hφinv⟩, Aut.ext <| Iso.ext (Subtype.ext
      (Over.OverMorphism.ext (ObjectProperty.hom_ext _
        (FiniteProjectiveRepresentation.Hom.ext hub.symm
          (AddMonoidHom.ext fun mm ↦ ?_)))))⟩
    exact (hφ mm).symm
  exact (MulEquiv.ofBijective F ⟨hinj, hsurj⟩).symm

/-- The infinitesimal automorphisms of the deformation category of a finite-dimensional
continuous representation `ρ₀` of a topological group are the degree-zero cohomology of the
conjugation action on its endomorphisms, `H⁰(Γ, End_k(V))`. -/
@[stacks 0DVW "Inf"]
public noncomputable def continuousInfinitesimalAutomorphismsEquivH0
    (V : Type w) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ₀ : Representation k Γ V) (hρ₀ : IsContinuousRepresentation ρ₀)
    {A₀ Aε : ArtinianLocalAlgCat.{u, w, w} Λ k}
    {x₀ : (continuousDeformationProjection (Λ := Λ) V ρ₀ hρ₀).Fiber A₀}
    {xε : (continuousDeformationProjection (Λ := Λ) V ρ₀ hρ₀).Fiber Aε}
    (g : A₀ ⟶ Aε) (e : Aε ⟶ A₀) (hpair : IsCanonicalDualNumberPair g e)
    (i : x₀.1 ⟶ xε.1)
    (hi : (continuousDeformationProjection (Λ := Λ) V ρ₀ hρ₀).IsHomLift g i) :
    ↥(infinitesimalAutomorphisms
        (continuousDeformationProjection_isCofiberedInGroupoids (Λ := Λ) V ρ₀ hρ₀)
        g e hpair i hi) ≃*
      Multiplicative (groupCohomology (Rep.of (Representation.linHom ρ₀ ρ₀)) 0) := by
  have hNE : Nonempty (xε.1.left.obj.base ≃ₐ[Λ] DualNumber k) := by
    obtain ⟨-, iε, -, -, -⟩ := hpair
    exact ⟨(ArtinianLocalAlgCat.algEquivOfEq
      (show xε.1.left.obj.base = Aε from xε.2)).trans iε⟩
  have hfo := exists_isFirstOrderReduction_continuousDeformation V ρ₀ hρ₀ xε hNE
  let L : groupCohomology (Rep.of (Representation.linHom ρ₀ ρ₀)) 0 ≃ₗ[k]
      ↥((Representation.linHom ρ₀ ρ₀).invariants) :=
    Iso.toLinearEquiv (groupCohomology.H0Iso (Rep.of (Representation.linHom ρ₀ ρ₀)))
  exact (((MulEquiv.subgroupCongr
    (continuousInfinitesimalAutomorphisms_eq_top V ρ₀ hρ₀ g e hpair i
      hi)).trans Subgroup.topEquiv).trans
    (continuousAutEquivInvariants V ρ₀ hρ₀ xε (Classical.choose hfo)
      (Classical.choose_spec hfo))).trans
    (AddEquiv.toMultiplicative L.toAddEquiv).symm

/-- **Stacks 0DVW**, the clause that the infinitesimal automorphisms are *always* finite
dimensional: the infinitesimal automorphism group of the deformation category of a
finite-dimensional continuous representation `ρ₀` carries a `k`-vector space structure whose
addition is composition of automorphisms, and that vector space is finite dimensional.

No hypothesis on `Γ` is needed. The group is `H⁰(Γ, End_k(V))` by
`continuousInfinitesimalAutomorphismsEquivH0`, and degree-zero cohomology is the subspace of
`Γ`-invariants of `End_k(V)`, which is finite dimensional because `V` is. -/
@[stacks 0DVW "Inf is always finite dimensional"]
public theorem finiteDimensional_continuousInfinitesimalAutomorphisms
    (V : Type w) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ₀ : Representation k Γ V) (hρ₀ : IsContinuousRepresentation ρ₀)
    {A₀ Aε : ArtinianLocalAlgCat.{u, w, w} Λ k}
    {x₀ : (continuousDeformationProjection (Λ := Λ) V ρ₀ hρ₀).Fiber A₀}
    {xε : (continuousDeformationProjection (Λ := Λ) V ρ₀ hρ₀).Fiber Aε}
    (g : A₀ ⟶ Aε) (e : Aε ⟶ A₀) (hpair : IsCanonicalDualNumberPair g e)
    (i : x₀.1 ⟶ xε.1)
    (hi : (continuousDeformationProjection (Λ := Λ) V ρ₀ hρ₀).IsHomLift g i) :
    let G := ↥(infinitesimalAutomorphisms
      (continuousDeformationProjection_isCofiberedInGroupoids (Λ := Λ) V ρ₀ hρ₀)
      g e hpair i hi)
    ∃ hA : AddCommGroup G,
      letI := hA
      ∃ hM : Module k G,
        letI := hM
        (∀ a b : G, a + b = a * b) ∧ FiniteDimensional k G := by
  classical
  dsimp only
  let G := ↥(infinitesimalAutomorphisms
    (continuousDeformationProjection_isCofiberedInGroupoids (Λ := Λ) V ρ₀ hρ₀)
    g e hpair i hi)
  let W := ↥((Representation.linHom ρ₀ ρ₀).invariants)
  let L : groupCohomology (Rep.of (Representation.linHom ρ₀ ρ₀)) 0 ≃ₗ[k] W :=
    Iso.toLinearEquiv (groupCohomology.H0Iso (Rep.of (Representation.linHom ρ₀ ρ₀)))
  let F : G ≃* Multiplicative (groupCohomology (Rep.of (Representation.linHom ρ₀ ρ₀)) 0) :=
    continuousInfinitesimalAutomorphismsEquivH0 (Λ := Λ) V ρ₀ hρ₀ g e hpair i hi
  let eqv : G ≃ W := F.toEquiv.trans (Multiplicative.toAdd.trans L.toEquiv)
  have heqv : ∀ a b : G, eqv (a * b) = eqv a + eqv b := by
    intro a b
    change L (Multiplicative.toAdd (F (a * b))) =
      L (Multiplicative.toAdd (F a)) + L (Multiplicative.toAdd (F b))
    rw [F.map_mul, ← map_add]
    rfl
  let hA : AddCommGroup G := eqv.addCommGroup
  let : AddCommGroup G := hA
  let eadd : G ≃+ W := { toEquiv := eqv, map_add' := fun _ _ ↦ eqv.apply_symm_apply _ }
  let hM : Module k G := eadd.module k
  let : Module k G := hM
  let E : G ≃ₗ[k] W := eadd.linearEquiv k
  have hfin : FiniteDimensional k W := inferInstance
  refine ⟨hA, hM, fun a b ↦ eqv.injective ((eadd.map_add a b).trans (heqv a b).symm), ?_⟩
  exact FiniteDimensional.of_injective E.toLinearMap E.injective

/-! ### Finite dimensionality of the tangent space -/

section TangentSpace

universe m g

variable {Λ : Type u} {k : Type w} {Γ : Type g} [CommRing Λ] [Field k] [Algebra Λ k]
  [Group Γ] [TopologicalSpace Γ]

/-- **Stacks 0DVW**, the tangent clause: for a topologically finitely generated topological
group `Γ` the tangent space of the deformation category of a finite-dimensional continuous
representation `ρ₀` is finite dimensional over `k`.

Topological finite generation enters through a dense finitely generated subgroup `H ≤ Γ`.
A continuous deformation is locally constant, so an `H`-equivariant map between two of them is
`Γ`-equivariant: the agreement locus is closed and contains `H`. Hence restriction of the
action to `H` is fully faithful, so its differential is an injective `k`-linear map from the
tangent space into the tangent space of the deformation category of `ρ₀|_H`, and the latter is
finite dimensional by Stacks 0DVT. -/
@[stacks 0DVW "the tangent space is finite dimensional"]
public theorem finiteDimensional_continuousTangentSpace
    (V : Type m) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ₀ : Representation k Γ V) (hρ₀ : IsContinuousRepresentation ρ₀)
    (hΓ : ∃ H : Subgroup Γ, Group.FG ↥H ∧ Dense (H : Set Γ)) :
    let 𝓕 := BasedCategory.ofFunctor (Deformation.objectsOverFunctor
      (continuousProjection.{u, w, w, m} (Λ := Λ) (k := k) (Γ := Γ))
      (continuousSpecialFiber (Λ := Λ) V ρ₀ hρ₀))
    let hD := isDeformationCategory_continuousDeformationCategory (Λ := Λ) V ρ₀ hρ₀
    letI : Fact (Deformation.IsPredeformationCategory 𝓕.p) := ⟨hD.predeformation⟩
    letI : Fact (Deformation.SchlessingerConditionS2 (CategoryOfElements.π
        (Deformation.isomorphismClasses 𝓕 hD.predeformation.cofibered))) :=
      ⟨Deformation.Artin.schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory
        𝓕 hD⟩
    FiniteDimensional k (Deformation.artinianTangentSpace Λ k
      (Deformation.isomorphismClasses 𝓕 hD.predeformation.cofibered)) := by
  obtain ⟨H, hfg, hdense⟩ := hΓ
  let : Group.FG ↥H := hfg
  let ee := Deformation.tangentSpaceEquivSelfExt (Λ := Λ) V (ρ₀.comp H.subtype)
  exact Deformation.finiteDimensional_artinianTangentSpace_of_fullyFaithful
    (BasedCategory.ofFunctor (Deformation.objectsOverFunctor
      (continuousProjection.{u, w, w, m} (Λ := Λ) (k := k) (Γ := Γ))
      (continuousSpecialFiber (Λ := Λ) V ρ₀ hρ₀)))
    (BasedCategory.ofFunctor
      (Deformation.deformationCategoryProjection (Λ := Λ) V (ρ₀.comp H.subtype)))
    (isDeformationCategory_continuousDeformationCategory (Λ := Λ) V ρ₀ hρ₀).predeformation
    ee.1
    (Deformation.Artin.schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory _
      (isDeformationCategory_continuousDeformationCategory (Λ := Λ) V ρ₀ hρ₀))
    ee.2.1
    (restrictContinuousBasedFunctor (Λ := Λ) V H ρ₀ hρ₀)
    (full_restrictContinuousBasedFunctor (Λ := Λ) (H := H) V hdense ρ₀ hρ₀)
    (faithful_restrictContinuousBasedFunctor (Λ := Λ) V H ρ₀ hρ₀)
    (Deformation.finiteDimensional_tangentSpace_representation (Λ := Λ) V
      (ρ₀.comp H.subtype))

end TangentSpace

end Deformation.Examples.FiniteProjectiveRepresentation

end
