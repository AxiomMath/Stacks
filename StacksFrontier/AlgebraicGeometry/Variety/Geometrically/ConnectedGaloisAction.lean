module

public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.Topology.Connected.TotallyDisconnected
public import StacksFrontier.AlgebraicGeometry.Variety.Geometric.BaseChangeTower
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedSeparablyClosed
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.IrreducibleGaloisAction
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.QuasiCompactOpen

/-!
# Galois action on geometric connected components

An automorphism of an algebra over a base ring acts on the corresponding base change of a
scheme. The induced homeomorphism of the underlying space acts on its connected components,
giving the canonical action on geometric connected components. This action is compatible with
restriction of Galois automorphisms along an extension of the ground field, and the canonical
base-extension map is bijective on components when the smaller closure is separably closed.

## Main definitions

* `AlgebraicGeometry.connectedComponentsAction`: the action induced on connected components by
  an action on a topological space.
* `AlgebraicGeometry.galoisActionOnGeometricConnectedComponents`: the action of the opposite of
  the group of algebra automorphisms on the connected components after base change.

## Main results

* `AlgebraicGeometry.galoisActionOnGeometricConnectedComponents_ρ_apply_mk`: the action sends the
  component of a point to the component of its image.
* `AlgebraicGeometry.galoisActionOnGeometricConnectedComponents_baseChange` expresses
  equivariance of the canonical map on connected components.
* `AlgebraicGeometry.baseChangeComparison_connectedComponents_bijective` records that this map is
  a bijection.

## Implementation notes

The scheme action is transported to its underlying topological space by
`CategoryTheory.Functor.mapAction`. Its action on the quotient `ConnectedComponents` is induced
by functoriality of connected components. The construction is stated for an arbitrary extension
of commutative rings, since neither the field nor separable-closure hypotheses are needed to
define it.

The morphism `p` is specified by its two pullback projections, which uniquely characterize the
canonical base-change map. The action on the larger geometric fibre is written over the original
base field; the automorphism fixing the intermediate field is restricted to that base field. The
first result gives commutativity of the diagram, and the second identifies its right vertical
arrow as a bijection.

## References

* [Stacks Project, Tag 038D](https://stacks.math.columbia.edu/tag/038D)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

/-- An action by homeomorphisms induces an action on connected components. -/
@[implicit_reducible]
public noncomputable def connectedComponentsAction {G : Type u} [Group G]
    (X : Action TopCat.{u} G) : Action (Type u) G := by
  let : MulAction G X.V := Action.instMulAction X
  let : MulAction G (ConnectedComponents X.V) :=
    { smul g C := (X.ρ g).hom.continuous.connectedComponentsMap C
      one_smul C := by
        obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe C
        change (X.ρ 1).hom.continuous.connectedComponentsMap _ = _
        simp only [Continuous.connectedComponentsMap_mk]
        congr 1
        exact one_smul G x
      mul_smul g h C := by
        obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe C
        change (X.ρ (g * h)).hom.continuous.connectedComponentsMap _ =
          (X.ρ g).hom.continuous.connectedComponentsMap _
        simp only [Continuous.connectedComponentsMap_mk]
        congr 1
        exact mul_smul g h x }
  exact Action.ofMulAction G (ConnectedComponents X.V)

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/- `galoisActionOnGeometricIrreducibleComponents` has the same type as the definition below, but
is a different action: it is built from `irreducibleComponentsAction`, acting on the subtype
`irreducibleComponents` of closed irreducible subsets, while this one is built from
`connectedComponentsAction`, acting on the quotient `ConnectedComponents`. The two underlying
sets differ already for a scheme with a connected but reducible underlying space. -/
/-- The canonical action of the opposite Galois group on the connected components of a scheme
after base change. A component is sent to its image under the corresponding automorphism of the
base-changed scheme. -/
@[stacks 038D "galois_action_on_geometric_connected_components", implicit_reducible]
public noncomputable def galoisActionOnGeometricConnectedComponents
    (X : Over (Spec (.of R))) :
    Action (Type u) (MulOpposite (S ≃ₐ[R] S)) :=
  connectedComponentsAction
    ((Scheme.forgetToTop.mapAction (MulOpposite (S ≃ₐ[R] S))).obj
      (galoisActionOnBaseChange R S X))

/-- The Galois action sends the connected component of a point to the component of its image
under the corresponding automorphism of the base-changed scheme. -/
@[simp]
public theorem galoisActionOnGeometricConnectedComponents_ρ_apply_mk
    (X : Over (Spec (.of R))) (σ : MulOpposite (S ≃ₐ[R] S))
    (x : (galoisActionOnBaseChange R S X).V) :
    ConcreteCategory.hom
        ((galoisActionOnGeometricConnectedComponents R S X).ρ σ)
        (ConnectedComponents.mk x) =
      ConnectedComponents.mk
        (ConcreteCategory.hom
          (((Scheme.forgetToTop.mapAction (MulOpposite (S ≃ₐ[R] S))).obj
            (galoisActionOnBaseChange R S X)).ρ σ) x) :=
  rfl

section BaseExtension

variable (k kbar kbar' : Type u)
  [Field k] [Field kbar] [Field kbar']
  [Algebra k kbar] [Algebra k kbar'] [Algebra kbar kbar']
  [IsScalarTower k kbar kbar']
  (X : Over (Spec (.of k)))

/-- Taking connected components is functorial. -/
private lemma connectedComponentsMap_comp {A B C : Type u} [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace C] {f : A → B} {g : B → C}
    (hf : Continuous f) (hg : Continuous g) :
    (hg.comp hf).connectedComponentsMap =
      hg.connectedComponentsMap ∘ hf.connectedComponentsMap := by
  ext x
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe x
  simp [Continuous.connectedComponentsMap_mk]

/-- Functoriality of connected components, for a factorization of morphisms of schemes. -/
private lemma connectedComponentsMap_comp_of_scheme_hom_eq
    {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) (h : A ⟶ C)
    (hfg : f ≫ g = h) :
    g.continuous.connectedComponentsMap ∘ f.continuous.connectedComponentsMap =
      h.continuous.connectedComponentsMap := by
  have hh := congrArg (fun m : A ⟶ C => m.continuous.connectedComponentsMap) hfg
  change (g.continuous.comp f.continuous).connectedComponentsMap = _ at hh
  rwa [connectedComponentsMap_comp] at hh

/-- An isomorphism of schemes is bijective on connected components. -/
private lemma connectedComponentsMap_bijective_of_iso {A B : Scheme.{u}}
    (e : A ≅ B) : Function.Bijective e.hom.continuous.connectedComponentsMap := by
  constructor
  · intro a b hab
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe a
    obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe b
    simpa [Continuous.connectedComponentsMap_mk] using
      congrArg e.inv.continuous.connectedComponentsMap hab
  · intro b
    obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe b
    exact ⟨e.inv.continuous.connectedComponentsMap (ConnectedComponents.mk y), by
      simp [Continuous.connectedComponentsMap_mk]⟩

/-- The action of an automorphism on the base change fixes the first projection and twists the
second by `specMapAlgAut`. -/
private lemma galoisActionOnBaseChange_comp_projections (K : Type u) [Field K] [Algebra k K]
    (τ : K ≃ₐ[k] K) :
    (galoisActionOnBaseChange k K X).ρ (MulOpposite.op τ) ≫
        pullback.fst X.hom (spectrumMap k K) = pullback.fst X.hom (spectrumMap k K) ∧
      (galoisActionOnBaseChange k K X).ρ (MulOpposite.op τ) ≫
          pullback.snd X.hom (spectrumMap k K) =
        pullback.snd X.hom (spectrumMap k K) ≫ specMapAlgAut k K τ := by
  constructor <;>
    simp [galoisActionOnBaseChange, spectrumMap, pullback.map, pullback.lift_fst,
      pullback.lift_snd]

/-- Restriction of Galois automorphisms commutes with the canonical map on the connected
components of the two geometric base changes. -/
@[stacks 038D "base_extension_compatibility"]
public theorem galoisActionOnGeometricConnectedComponents_baseChange
    (k' : Type u) [Field k'] [Algebra k k'] [Algebra k' kbar']
    [IsScalarTower k k' kbar'] [Normal k kbar]
    (p : pullback X.hom (spectrumMap k kbar') ⟶ pullback X.hom (spectrumMap k kbar))
    (hp₁ : p ≫ pullback.fst X.hom (spectrumMap k kbar) =
      pullback.fst X.hom (spectrumMap k kbar'))
    (hp₂ : p ≫ pullback.snd X.hom (spectrumMap k kbar) =
      pullback.snd X.hom (spectrumMap k kbar') ≫
        Spec.map (CommRingCat.ofHom (algebraMap kbar kbar')))
    (σ : kbar' ≃ₐ[k'] kbar')
    (C : ConnectedComponents (galoisActionOnBaseChange k kbar' X).V) :
    p.continuous.connectedComponentsMap
        (ConcreteCategory.hom
          ((galoisActionOnGeometricConnectedComponents k kbar' X).ρ
            (MulOpposite.op (σ.restrictScalars k))) C) =
      ConcreteCategory.hom
        ((galoisActionOnGeometricConnectedComponents k kbar X).ρ
          (MulOpposite.op ((σ.restrictScalars k).restrictNormal kbar)))
        (p.continuous.connectedComponentsMap C) := by
  have hspec :
      specMapAlgAut k kbar' (σ.restrictScalars k) ≫
          Spec.map (CommRingCat.ofHom (algebraMap kbar kbar')) =
        Spec.map (CommRingCat.ofHom (algebraMap kbar kbar')) ≫
          specMapAlgAut k kbar ((σ.restrictScalars k).restrictNormal kbar) := by
    unfold specMapAlgAut
    rw [← Spec.map_comp, ← Spec.map_comp]
    refine congrArg Spec.map ?_
    ext x
    exact (AlgEquiv.restrictNormal_commutes (σ.restrictScalars k) kbar x).symm
  obtain ⟨hfstq, hsndq⟩ := galoisActionOnBaseChange_comp_projections k X kbar' (σ.restrictScalars k)
  obtain ⟨hfstr, hsndr⟩ := galoisActionOnBaseChange_comp_projections k X kbar
    ((σ.restrictScalars k).restrictNormal kbar)
  set q := (galoisActionOnBaseChange k kbar' X).ρ
    (MulOpposite.op (σ.restrictScalars k))
  set r := (galoisActionOnBaseChange k kbar X).ρ
    (MulOpposite.op ((σ.restrictScalars k).restrictNormal kbar))
  have hqp : q ≫ p = p ≫ r := by
    apply pullback.hom_ext
    · simp only [Category.assoc, hp₁, hfstq, hfstr]
    · simp only [Category.assoc, hp₂, reassoc_of% hp₂, reassoc_of% hsndq, hsndr, hspec]
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe C
  simp only [Continuous.connectedComponentsMap_mk]
  exact congrArg ConnectedComponents.mk
    (congrArg (fun f => (Scheme.forgetToTop.map f).hom x) hqp)

/-- The canonical base-extension map is bijective on geometric connected components. -/
@[stacks 038D "base_extension_compatibility"]
public theorem baseChangeComparison_connectedComponents_bijective
    [IsSepClosed kbar]
    (p : pullback X.hom (spectrumMap k kbar') ⟶ pullback X.hom (spectrumMap k kbar))
    (hp₁ : p ≫ pullback.fst X.hom (spectrumMap k kbar) =
      pullback.fst X.hom (spectrumMap k kbar'))
    (hp₂ : p ≫ pullback.snd X.hom (spectrumMap k kbar) =
      pullback.snd X.hom (spectrumMap k kbar') ≫
        Spec.map (CommRingCat.ofHom (algebraMap kbar kbar'))) :
    Function.Bijective p.continuous.connectedComponentsMap := by
  let f := X.hom
  let g := spectrumMap k kbar
  let c := Spec.map (CommRingCat.ofHom (algebraMap kbar kbar'))
  let g' := spectrumMap k kbar'
  let r := pullback.snd f g
  let t := pullback.fst r c
  have hcomp : g' = c ≫ g := by
    dsimp [g', c, g, spectrumMap]
    rw [← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (IsScalarTower.algebraMap_eq k kbar kbar')
  let e : pullback r c ≅ pullback f g' := baseChangeTowerIsoTo f g c g' hcomp
  have hpe : e.hom ≫ p = t :=
    baseChangeTowerIsoTo_comp_of_projection f g c g' hcomp p hp₁ hp₂
  have ht : Function.Bijective t.continuous.connectedComponentsMap :=
    baseChange_connectedComponents_bijective kbar kbar' r
  have hmap :
      p.continuous.connectedComponentsMap ∘ e.hom.continuous.connectedComponentsMap =
        t.continuous.connectedComponentsMap :=
    connectedComponentsMap_comp_of_scheme_hom_eq e.hom p t hpe
  exact (Function.Bijective.of_comp_iff _ (connectedComponentsMap_bijective_of_iso e)).mp
    (hmap ▸ ht)

end BaseExtension

end AlgebraicGeometry
