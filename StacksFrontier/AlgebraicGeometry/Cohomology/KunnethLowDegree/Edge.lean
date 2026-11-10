module

public import StacksFrontier.Algebra.Homology.RightDerivedDeltaOne
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.Derived.Basic
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageQcqs.AffineBaseSections
public import StacksFrontier.AlgebraicGeometry.ModuleGlobalSections
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleQuotients.Basic
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.Topology.Sheaves.Functors.Module.FlatPullback
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The low-degree Leray sequence of a flat morphism of schemes

For a flat morphism `p : W ⟶ X` of schemes, the edge morphism of the Leray spectral sequence in
degree one, `H¹(X, p_* G) ⟶ H¹(W, G)`, is injective, natural in `G`, and its image is the kernel
of the second edge morphism `H¹(W, G) ⟶ Γ(X, R¹p_* G)`. This is the low-degree part of
[Stacks, Tag 01F2] for `p`, read on the cohomology `(moduleGlobalSections W).rightDerived 1`.

Flatness makes `p^*` exact, so `p_*` preserves injective modules ([Stacks, Tag 02N5]), which is
what the general edge morphism of a composite of right derived functors
(`Stacks.Cohomology.RightDerivedEdge.edge`) needs; global sections of `p_* G` are literally the
global sections of `G`.

## Main definitions

* `Stacks.KunnethLowDegree.leray₁`: the edge morphism `H¹(X, p_* G) ⟶ H¹(W, G)`, as a
  `Γ(X, ⊤)`-linear map to `H¹(W, G)` with scalars restricted along `p.appTop`.
* `Stacks.KunnethLowDegree.leray₂`: the second edge morphism `H¹(W, G) ⟶ Γ(X, R¹p_* G)`.

## Main results

* `Stacks.KunnethLowDegree.mono_leray₁`: the edge morphism is injective.
* `Stacks.KunnethLowDegree.leray₁_naturality`: it is natural in `G`.
* `Stacks.KunnethLowDegree.exact_leray₁_leray₂`: exactness in the middle.

## References

* [Stacks Project, Tag 01F2](https://stacks.math.columbia.edu/tag/01F2)
* [Stacks Project, Tag 02N5](https://stacks.math.columbia.edu/tag/02N5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace Stacks.KunnethLowDegree

variable {W X : Scheme.{u}} (p : W ⟶ X)

/-- Module pullback along a flat morphism of schemes is exact. -/
theorem preservesFiniteLimits_pullback [Flat p] :
    PreservesFiniteLimits (Scheme.Modules.pullback p) :=
  @preservesFiniteLimits_of_natIso _ _ _ _ _ _ (Stacks.ProjectiveBundleQuotients.pullbackIso p).symm
    (Stacks.AlgebraicGeometry.FlatBaseChangeDerived.preservesFiniteLimits_pullback p)

/-- Module pushforward along a flat morphism of schemes preserves injective modules
([Stacks, Tag 02N5]): its left adjoint is exact. -/
theorem preservesInjectiveObjects_pushforward [Flat p] :
    (Scheme.Modules.pushforward p).PreservesInjectiveObjects :=
  have := preservesFiniteLimits_pullback p
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (Scheme.Modules.pullbackPushforwardAdjunction p)

/-- Global sections of a pushforward are the global sections, with scalars restricted. -/
def pushforwardCompGlobalSectionsIso :
    moduleGlobalSections W ⋙ ModuleCat.restrictScalars p.appTop.hom ≅
      Scheme.Modules.pushforward p ⋙ moduleGlobalSections X :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)

/-- The right derived functors of global sections of a pushforward are those of global sections,
with scalars restricted. -/
def rightDerivedPushforwardCompIso (n : ℕ) :
    (moduleGlobalSections W).rightDerived n ⋙ ModuleCat.restrictScalars p.appTop.hom ≅
      (Scheme.Modules.pushforward p ⋙ moduleGlobalSections X).rightDerived n :=
  haveI : (ModuleCat.restrictScalars p.appTop.hom).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  (Functor.rightDerivedCompIso (moduleGlobalSections W)
      (ModuleCat.restrictScalars p.appTop.hom) n).symm ≪≫
    Functor.rightDerivedIsoOfNatIso (pushforwardCompGlobalSectionsIso p) n

/-- Module pushforward is left exact, being a right adjoint. -/
theorem preservesFiniteLimits_pushforward :
    PreservesFiniteLimits (Scheme.Modules.pushforward p) :=
  have := (Scheme.Modules.pullbackPushforwardAdjunction p).rightAdjoint_preservesLimits.{0, 0}
  PreservesLimitsOfSize.preservesFiniteLimits _

variable [Flat p]

/-- **The degree-one edge morphism of the Leray sequence of a flat morphism** `p : W ⟶ X`,
`H¹(X, p_* G) ⟶ H¹(W, G)`, as a `Γ(X, ⊤)`-linear map. -/
def leray₁ (G : W.Modules) :
    ((moduleGlobalSections X).rightDerived 1).obj ((Scheme.Modules.pushforward p).obj G) ⟶
      (ModuleCat.restrictScalars p.appTop.hom).obj
        (((moduleGlobalSections W).rightDerived 1).obj G) :=
  have := preservesInjectiveObjects_pushforward p
  (Stacks.Cohomology.RightDerivedEdge.edge (Scheme.Modules.pushforward p)
      (moduleGlobalSections X) 1).app G ≫ (rightDerivedPushforwardCompIso p 1).inv.app G

/-- **The degree-one second edge morphism of the Leray sequence**, `H¹(W, G) ⟶ Γ(X, R¹p_* G)`. -/
def leray₂ (G : W.Modules) :
    (ModuleCat.restrictScalars p.appTop.hom).obj
        (((moduleGlobalSections W).rightDerived 1).obj G) ⟶
      (moduleGlobalSections X).obj (((Scheme.Modules.pushforward p).rightDerived 1).obj G) :=
  have := preservesInjectiveObjects_pushforward p
  (rightDerivedPushforwardCompIso p 1).hom.app G ≫
    (Stacks.Cohomology.RightDerivedCoEdge.secondEdge (Scheme.Modules.pushforward p)
      (moduleGlobalSections X) 1).app G

/-- The edge morphism is natural in the module. -/
@[reassoc]
theorem leray₁_naturality {G G' : W.Modules} (φ : G ⟶ G') :
    ((moduleGlobalSections X).rightDerived 1).map ((Scheme.Modules.pushforward p).map φ) ≫
        leray₁ p G' =
      leray₁ p G ≫ (ModuleCat.restrictScalars p.appTop.hom).map
        (((moduleGlobalSections W).rightDerived 1).map φ) := by
  have := preservesInjectiveObjects_pushforward p
  have h1 := (Stacks.Cohomology.RightDerivedEdge.edge (Scheme.Modules.pushforward p)
      (moduleGlobalSections X) 1).naturality φ
  have h2 := (rightDerivedPushforwardCompIso p 1).inv.naturality φ
  dsimp only [Functor.comp_map] at h1 h2
  simp only [leray₁, ← Category.assoc, h1]
  simp only [Category.assoc, h2]

/-- **The edge morphism is injective** ([Stacks, Tag 01F2]). -/
theorem mono_leray₁ (G : W.Modules) : Mono (leray₁ p G) := by
  have := preservesInjectiveObjects_pushforward p
  have := preservesFiniteLimits_pushforward p
  have h := Stacks.Cohomology.RightDerivedCoEdge.mono_edge_app_one
      (Scheme.Modules.pushforward p) (moduleGlobalSections X) G
  have h2 : Mono ((rightDerivedPushforwardCompIso p 1).inv.app G) :=
    inferInstanceAs (Mono ((rightDerivedPushforwardCompIso p 1).app G).symm.hom)
  exact @mono_comp _ _ _ _ _ _ h _ h2

/-- The composite of the edge morphism and the second edge morphism is zero. -/
theorem leray₁_comp_leray₂ (G : W.Modules) : leray₁ p G ≫ leray₂ p G = 0 := by
  have := preservesInjectiveObjects_pushforward p
  have h := Stacks.Cohomology.RightDerivedCoEdge.edge_comp_secondEdge
    (Scheme.Modules.pushforward p) (moduleGlobalSections X) 0 G
  rw [leray₁, leray₂, Category.assoc,
    ← Category.assoc ((rightDerivedPushforwardCompIso p 1).inv.app G),
    Iso.inv_hom_id_app, Category.id_comp]
  exact h

/-- **The low-degree Leray sequence `H¹(X, p_* G) ⟶ H¹(W, G) ⟶ Γ(X, R¹p_* G)` is exact**
([Stacks, Tag 01F2]). -/
@[sga "3 XXIV 8.5" "exactness at H¹(S',G')"]
theorem exact_leray₁_leray₂ (G : W.Modules) :
    (ShortComplex.mk (leray₁ p G) (leray₂ p G) (leray₁_comp_leray₂ p G)).Exact := by
  have := preservesInjectiveObjects_pushforward p
  have := preservesFiniteLimits_pushforward p
  have h := Stacks.Cohomology.RightDerivedDeltaOne.exact_edge_secondEdge
    (Scheme.Modules.pushforward p) (moduleGlobalSections X) G
  refine ShortComplex.exact_of_iso ?_ h
  refine ShortComplex.isoMk (Iso.refl _) ((rightDerivedPushforwardCompIso p 1).app G).symm
    (Iso.refl _) ?_ ?_
  · change _ ≫ (rightDerivedPushforwardCompIso p 1).inv.app G = 𝟙 _ ≫ leray₁ p G
    rw [Category.id_comp]
    rfl
  · change (rightDerivedPushforwardCompIso p 1).inv.app G ≫ leray₂ p G = _ ≫ 𝟙 _
    rw [Category.comp_id, leray₂, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

end Stacks.KunnethLowDegree

end
