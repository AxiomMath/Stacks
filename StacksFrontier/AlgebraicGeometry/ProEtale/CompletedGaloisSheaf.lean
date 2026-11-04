module

public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.RepresentationTheory.Subrepresentation
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ProetaleComparison

/-!
# Completed Galois sheaves on the pro-étale site of a field

Let `K` be a field with absolute Galois group `G = Gal(Kˢᵉᵖ/K)`. A discrete `G`-module `N`
determines a locally constant sheaf on the small étale site of `Spec K`, whose sections over a
scheme `U` étale over `K` are the `G`-equivariant maps from the geometric points of `U` to `N`.
Pulling that sheaf back along the comparison `ε` from the pro-étale to the étale site and taking
the inverse limit over a system of discrete quotients of a topological `G`-module `M` produces
the completed sheaf `M^∧` on the pro-étale site of `Spec K`.

## Main definitions

* `AlgebraicGeometry.GaloisSheaf.etaleSheaf`: the locally constant étale sheaf of a discrete
  Galois module, as a functor on representations.
* `AlgebraicGeometry.GaloisSheaf.proetaleSheaf`: its pullback `ε⁻¹` to the pro-étale site.
* `AlgebraicGeometry.GaloisSheaf.completion`: the limit `limⱼ ε⁻¹(M/Nⱼ)` over a system of
  subrepresentations `Nⱼ` of `M`.
* `AlgebraicGeometry.GaloisSheaf.profiniteSheaf`: the completed sheaf of a profinite abelian
  group with continuous Galois action, the quotients being those by open stable subgroups.
* `AlgebraicGeometry.GaloisSheaf.adicSheaf`: the completed sheaf of an `I`-adically complete
  module with continuous Galois action, the quotients being the `M/IⁿM`.

## Main results

* `AlgebraicGeometry.GaloisSheaf.completionIsLimit`: the completed sheaf is the limit of the
  pro-étale pullbacks of the discrete quotients, so the quotient system determines it up to
  unique isomorphism. Both `profiniteSheaf` and `adicSheaf` are `completion` applied to their
  quotient system, so this characterizes each of them.

## Implementation notes

The Galois group acts on the geometric points `Hom_{Spec K}(Spec Kˢᵉᵖ, U)` of a scheme `U`
étale over `K` by precomposition, and `sections` is the submodule of equivariant functions out
of that set. Sheafification is applied to the resulting presheaf, so no sheaf condition is
proved separately; for a discrete module the presheaf is already a sheaf and sheafification is
an isomorphism. The field, coefficient ring and module universes are independent, which forces
a `ULift` on the sections of the presheaf.

The hypotheses of the source are carried unbundled: a representation `ρ` of the absolute Galois
group on a module, a topology on that module, and a joint continuity assumption. This keeps the
coefficient ring free of a topology, which the source does not give it. A profinite abelian
group is a `ℤ`-module, so both cases are instances of the same construction over a ring.

## References

* [Stacks Project, Tag 09B4](https://stacks.math.columbia.edu/tag/09B4)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe s t t' u r r' w

namespace AlgebraicGeometry.GaloisSheaf

/-- Module categories have limits of every shape small enough for their carrier universe
(`ModuleCat.hasLimitsOfShape`). -/
local instance moduleCatHasLimitsOfShape {R : Type r'} [Ring R] {J : Type t} [Category.{t'} J]
    [Small.{s} J] : HasLimitsOfShape J (ModuleCat.{s} R) :=
  ModuleCat.hasLimitsOfShape

variable (K : Type u) [Field K]

/-- The spectrum of the field, the scheme whose pro-étale site is in question. -/
abbrev base : Scheme.{u} := Spec (CommRingCat.of K)

/-- The absolute Galois group `Gal(Kˢᵉᵖ/K)` of the field. -/
@[sga "3 VIIB 3.3.3", sga "7 I 0.3"]
abbrev galoisGroup := Gal(SeparableClosure K / K)

/-- The separable closure of the field, viewed as a geometric point of its spectrum. -/
abbrev point : Over (base K) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K (SeparableClosure K))))

/-- The automorphism of the geometric point induced by an absolute Galois element. -/
def pointAction (g : galoisGroup K) : point K ⟶ point K :=
  Over.homMk (Spec.map (CommRingCat.ofHom g.toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext a
    simp)

variable (Λ : Type r) [Ring Λ]

/-- The `Λ`-submodule of Galois-equivariant `M`-valued functions on the geometric points of a
scheme étale over the field. -/
def sections (M : Rep.{w} Λ (galoisGroup K)) (U : (base K).Etale) :
    Submodule Λ ((point K ⟶ (Scheme.Etale.forget (base K)).obj U) → M) where
  carrier := {f | ∀ g q, f (pointAction K g ≫ q) = M.ρ g (f q)}
  zero_mem' := by simp
  add_mem' := by intro f h hf hh g q; simp [hf g q, hh g q]
  smul_mem' := by intro a f hf g q; simp [hf g q]

/-- The presheaf of Galois-equivariant functions on geometric points, functorially in the
coefficient representation. -/
def presheafFunctor : Rep.{w} Λ (galoisGroup K) ⥤
    ((base K).Etaleᵒᵖ ⥤ ModuleCat.{max (u + 1) r w} Λ) where
  obj M :=
    { obj U := ModuleCat.of Λ (ULift.{max (u + 1) r} (sections K Λ M U.unop))
      map {U V} f := ModuleCat.ofHom
        { toFun a := ⟨⟨fun q ↦ a.down.1 (q ≫ (Scheme.Etale.forget (base K)).map f.unop), by
            intro g q
            simpa only [Category.assoc] using
              a.down.2 g (q ≫ (Scheme.Etale.forget (base K)).map f.unop)⟩⟩
          map_add' _ _ := rfl
          map_smul' _ _ := rfl }
      map_id U := by ext a q; simp
      map_comp f g := by ext a q; simp }
  map f :=
    { app U := ModuleCat.ofHom
        { toFun a := ⟨⟨fun q ↦ f.hom (a.down.1 q), by
            intro g q
            dsimp only
            rw [a.down.2 g q]
            exact Rep.hom_comm_apply f g (a.down.1 q)⟩⟩
          map_add' := by intros; ext; simp
          map_smul' := by intros; ext; simp }
      naturality := by intros; rfl }
  map_id := by intros; rfl
  map_comp := by intros; rfl

/-- The locally constant étale sheaf attached to a discrete Galois module. -/
def etaleSheaf : Rep.{w} Λ (galoisGroup K) ⥤
    Sheaf (base K).smallEtaleTopology (ModuleCat.{max (u + 1) r w} Λ) :=
  presheafFunctor K Λ ⋙ presheafToSheaf _ _

/-- The pullback `ε⁻¹` to the pro-étale site of the locally constant étale sheaf attached to a
discrete Galois module. -/
abbrev proetaleSheaf : Rep.{w} Λ (galoisGroup K) ⥤
    Sheaf (Scheme.ProEt.topology (base K)) (ModuleCat.{max (u + 1) r w} Λ) :=
  etaleSheaf K Λ ⋙ Scheme.etaleInverseImage.{u, w, r} (base K) Λ

variable {K Λ} {V : Type w} [AddCommGroup V] [Module Λ V]
  (ρ : Representation Λ (galoisGroup K) V)

/-- The quotient of a representation by a subrepresentation. -/
abbrev quotientRep (N : Subrepresentation ρ) : Rep.{w} Λ (galoisGroup K) :=
  Rep.of (ρ.quotient N.toSubmodule fun g _ hv ↦ N.apply_mem_toSubmodule g hv)

/-- The system of quotients of a representation by its subrepresentations, ordered by
inclusion: an inclusion `N ≤ N'` induces the surjection `M/N ⟶ M/N'`. -/
def quotientDiagram : Subrepresentation ρ ⥤ Rep.{w} Λ (galoisGroup K) where
  obj := quotientRep ρ
  map {N N'} f := Rep.ofHom
    ⟨N.toSubmodule.mapQ N'.toSubmodule LinearMap.id (leOfHom f), fun g ↦ by ext x; rfl⟩
  map_id N := by ext x; rfl
  map_comp {N N' N''} f g := by ext x; rfl

/-- The diagram of pro-étale pullbacks of the discrete quotients of a representation cut out by
a system of subrepresentations. -/
abbrev quotientSheafDiagram {J : Type t} [Category.{t'} J] (D : J ⥤ Subrepresentation ρ) :
    J ⥤ Sheaf (Scheme.ProEt.topology (base K)) (ModuleCat.{max (u + 1) r w} Λ) :=
  D ⋙ quotientDiagram ρ ⋙ proetaleSheaf K Λ

/-- The cone of projections from the completed sheaf onto the pro-étale pullbacks of the
discrete quotients `M/Nⱼ`. -/
abbrev completionCone {J : Type t} [Category.{t'} J] [Small.{max (u + 1) r w} J]
    (D : J ⥤ Subrepresentation ρ) : Cone (quotientSheafDiagram.{t, t', u, r, w} ρ D) :=
  limit.cone (quotientSheafDiagram.{t, t', u, r, w} ρ D)

/-- The completed sheaf `limⱼ ε⁻¹(M/Nⱼ)` on the pro-étale site of the field, attached to a
representation together with a system of subrepresentations cutting out discrete quotients. -/
abbrev completion {J : Type t} [Category.{t'} J] [Small.{max (u + 1) r w} J]
    (D : J ⥤ Subrepresentation ρ) :
    Sheaf (Scheme.ProEt.topology (base K)) (ModuleCat.{max (u + 1) r w} Λ) :=
  (completionCone.{t, t', u, r, w} ρ D).pt

/-- The completed sheaf is the inverse limit of the pro-étale pullbacks of the discrete
quotients, hence is determined by the quotient system up to unique isomorphism. -/
def completionIsLimit {J : Type t} [Category.{t'} J] [Small.{max (u + 1) r w} J]
    (D : J ⥤ Subrepresentation ρ) : IsLimit (completionCone.{t, t', u, r, w} ρ D) :=
  limit.isLimit _

/-! ### Case (1): profinite abelian coefficients -/

/-- The open Galois-stable submodules of a topological module, ordered by inclusion. Over `ℤ`
these are the open Galois-stable subgroups. -/
abbrev OpenStable [TopologicalSpace V] :=
  {N : Subrepresentation ρ // IsOpen (N.toSubmodule : Set V)}

/-- The system of open Galois-stable submodules of a topological module, whose quotients are the
discrete quotients of the module. -/
def openStableDiagram [TopologicalSpace V] : OpenStable ρ ⥤ Subrepresentation ρ where
  obj N := N.val
  map f := homOfLE (leOfHom f)

/-- The canonical pro-étale sheaf `M^∧` attached to a profinite abelian group `M` with continuous
action of the absolute Galois group of a field: the inverse limit of the pro-étale pullbacks of the
locally constant étale sheaves of the discrete quotients `M/N` by the open Galois-stable subgroups
`N`. -/
@[stacks 09B4 "case (1): the canonical sheaf of a profinite abelian group"]
def profiniteSheaf (K : Type u) [Field K] (M : Type w) [AddCommGroup M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [CompactSpace M] [T2Space M] [TotallyDisconnectedSpace M]
    (ρ : Representation ℤ (galoisGroup K) M)
    (_hρ : Continuous fun p : galoisGroup K × M ↦ ρ p.1 p.2) :
    Sheaf (Scheme.ProEt.topology (base K)) (ModuleCat.{max (u + 1) w} ℤ) :=
  completion.{w, w, u, 0, w} ρ (openStableDiagram ρ)

/-! ### Case (2): adically complete module coefficients -/

section Adic

variable (Λ : Type r) [CommRing Λ]

/-- The subrepresentation `IⁿM` cut out by a power of an ideal of the coefficient ring. -/
def adicSubrep {V : Type w} [AddCommGroup V] [Module Λ V]
    (I : Ideal Λ) (ρ : Representation Λ (galoisGroup K) V) (n : ℕ) : Subrepresentation ρ where
  toSubmodule := I ^ n • ⊤
  apply_mem_toSubmodule g := Submodule.smul_top_le_comap_smul_top (I ^ n) (ρ g)

/-- The inverse system `n ↦ IⁿM` of subrepresentations, whose quotients are the `M/IⁿM`. -/
def adicDiagram {V : Type w} [AddCommGroup V] [Module Λ V]
    (I : Ideal Λ) (ρ : Representation Λ (galoisGroup K) V) : ℕᵒᵖ ⥤ Subrepresentation ρ where
  obj n := adicSubrep Λ I ρ n.unop
  map f := homOfLE (Submodule.smul_mono_left (Ideal.pow_le_pow_right (leOfHom f.unop)))

/-- The canonical pro-étale sheaf `M^∧` attached to an `I`-adically complete module `M` over a
Noetherian ring, with continuous action of the absolute Galois group of a field for the `I`-adic
topology: the inverse limit of the pro-étale pullbacks of the locally constant étale sheaves of
the discrete quotients `M/IⁿM`. -/
@[stacks 09B4 "case (2): the canonical sheaf of an adically complete module"]
def adicSheaf (K : Type u) [Field K] [IsNoetherianRing Λ] (I : Ideal Λ) (M : Type w)
    [AddCommGroup M] [Module Λ M] [IsAdicComplete I M]
    (ρ : Representation Λ (galoisGroup K) M)
    (_hρ : letI : TopologicalSpace M := I.adicModuleTopology M
      Continuous fun p : galoisGroup K × M ↦ ρ p.1 p.2) :
    Sheaf (Scheme.ProEt.topology (base K)) (ModuleCat.{max (u + 1) r w} Λ) :=
  completion.{0, 0, u, r, w} ρ (adicDiagram Λ I ρ)

end Adic

end AlgebraicGeometry.GaloisSheaf

end
