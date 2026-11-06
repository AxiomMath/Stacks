module

public import Mathlib.CategoryTheory.Action.Continuous
public import Mathlib.CategoryTheory.Action.Concrete
public import Mathlib.CategoryTheory.Galois.Examples
public import Mathlib.CategoryTheory.Galois.Decomposition
public import Mathlib.Topology.Category.FinTopCat
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategories.AutomorphismTopology
public import StacksFrontier.Topology.Algebra.ProfiniteGroup
public import StacksCore.Tactic.StacksAttribute

/-!
# Automorphisms of the forgetful functor on finite continuous actions

For a topological group `G`, the automorphism group of the forgetful functor from finite
continuous `G`-sets to sets is canonically the profinite completion of `G`.

## Main definitions

* `CategoryTheory.IsProfiniteCompletion` expresses the universal property of a profinite
  completion of a topological group.
* `CategoryTheory.actionOnForget` is the canonical abstract-group homomorphism.
* `CategoryTheory.canonicalHom` is its continuous lift.

## Main results

* `CategoryTheory.continuous_actionOnForget` says the canonical homomorphism is continuous.
* `CategoryTheory.canonicalHom_apply` gives the action on each finite continuous `G`-set.
* `CategoryTheory.profiniteCompletionEquiv_forgetAut` identifies the profinite completion of `G`
  with the automorphism group of the forgetful functor on finite continuous `G`-sets.

## Implementation notes

Finite continuous `G`-sets are represented by `ContAction FintypeCat G`. Since the profinite
completion is taken relative to the topology on `G`, rather than that of the underlying abstract
group, it is expressed by its universal property for continuous homomorphisms to profinite
groups. The topology on the automorphism group is the componentwise topology
`CategoryTheory.functorAutomorphismTopology`. The component equation characterizes the canonical
homomorphism on every finite continuous action. Continuity and the universal property are
separate claims. Being profinite is `Stacks.Chapter05.Tag_0BR1.IsProfiniteTop`, the conjunction
of compactness, Hausdorffness and total disconnectedness of the underlying space.

## References

* [Stacks Project, Tag 0BMU](https://stacks.math.columbia.edu/tag/0BMU)
* [Stacks Project, Tag 0BMR](https://stacks.math.columbia.edu/tag/0BMR)
-/

@[expose] public section

open CategoryTheory Topology
open scoped FintypeCatDiscrete

universe u v w

namespace CategoryTheory

/-- A continuous homomorphism into a profinite group exhibits its target as the profinite
completion when precomposition gives a bijection from continuous homomorphisms out of the target
to continuous homomorphisms out of the source, for every profinite group. -/
public def IsProfiniteCompletion
    {G : Type u} {P : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group P] [TopologicalSpace P] [IsTopologicalGroup P] (c : G →ₜ* P) : Prop :=
  Stacks.Chapter05.Tag_0BR1.IsProfiniteTop P ∧
    ∀ (Q : Type w) [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q],
      Stacks.Chapter05.Tag_0BR1.IsProfiniteTop Q →
        Function.Bijective (fun f : P →ₜ* Q ↦ f.comp c)

/-- The action of `G` on every finite continuous `G`-set, regarded as a natural
automorphism of the forgetful functor. -/
public def actionOnForget (G : Type u) [Group G] [TopologicalSpace G] :
    G →* Aut (forget (ContAction FintypeCat.{u} G)) where
  toFun g := .of <| NatIso.ofComponents
    (fun X => ((forget FintypeCat).mapAut X.obj.V (Action.ρAut X.obj g)).asIso) (by
    intro X Y f
    ext x
    exact congrArg (fun (k : X.obj.V ⟶ Y.obj.V) => ConcreteCategory.hom k x)
      (f.hom.comm g).symm)
  map_one' := by
    apply Aut.ext
    apply Iso.ext
    apply NatTrans.ext
    funext X
    apply ConcreteCategory.ext_apply
    intro x
    change ConcreteCategory.hom (X.obj.ρ 1).asHom x = x
    simp
  map_mul' g h := by
    apply Aut.ext
    apply Iso.ext
    apply NatTrans.ext
    funext X
    apply ConcreteCategory.ext_apply
    intro x
    change ConcreteCategory.hom (X.obj.ρ (g * h)).asHom x =
      ConcreteCategory.hom (X.obj.ρ g).asHom (ConcreteCategory.hom (X.obj.ρ h).asHom x)
    simp [map_mul]

private theorem contAction_topology_eq (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (X : ContAction FintypeCat.{u} G) :
    FintypeCatDiscrete.instTopologicalSpaceObjFinite X.obj.V =
      ((forget₂ (Action FintypeCat G) TopCat).obj X.obj).str := by
  have hdisc : DiscreteTopology ((forget₂ (Action FintypeCat G) TopCat).obj X.obj) := by
    show DiscreteTopology X.obj.V.obj
    infer_instance
  exact DiscreteTopology.eq_bot.trans hdisc.eq_bot.symm

/-- The action of `G` on a finite continuous `G`-set is jointly continuous. -/
private theorem contAction_continuousSMul (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (X : ContAction FintypeCat.{u} G) :
    ContinuousSMul G ((forget₂ (Action FintypeCat G) TopCat).obj X.obj) := by
  rw [← contAction_topology_eq G X]
  exact X.property

/-- The canonical action homomorphism is continuous for the componentwise topology. -/
@[stacks 0BMU "continuity of the canonical homomorphism"]
public theorem continuous_actionOnForget (G : Type u) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] :
    let _ : TopologicalSpace (Aut (forget (ContAction FintypeCat.{u} G))) :=
      functorAutomorphismTopology _
    Continuous (actionOnForget G) := by
  let : TopologicalSpace (Aut (forget (ContAction FintypeCat.{u} G))) :=
    functorAutomorphismTopology _
  apply continuous_induced_rng.mpr
  show Continuous ((componentEmbedding _) ∘ actionOnForget G)
  apply continuous_pi_iff.mpr
  intro X
  show Continuous (fun g : G =>
    ((forget FintypeCat).mapAut X.obj.V (Action.ρAut X.obj g)).asIso.toEquiv)
  let : MulAction G X.obj.V.obj := by
    show MulAction G ((forget₂ (Action FintypeCat G) TopCat).obj X.obj)
    infer_instance
  let : ContinuousSMul G X.obj.V.obj := contAction_continuousSMul G X
  have hsmul : Continuous (fun p : G × X.obj.V.obj => p.1 • p.2) := continuous_smul
  apply continuous_induced_rng.mpr
  apply (continuous_iff_uncurry_continuous _).2
  exact hsmul.congr fun _ => rfl

/-- The canonical continuous homomorphism to natural automorphisms of the forgetful functor. -/
public def canonicalHom (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] :
    let _ : TopologicalSpace (Aut (forget (ContAction FintypeCat.{u} G))) :=
      functorAutomorphismTopology _
    G →ₜ* Aut (forget (ContAction FintypeCat.{u} G)) := by
  letI : TopologicalSpace (Aut (forget (ContAction FintypeCat.{u} G))) :=
    functorAutomorphismTopology _
  exact { toMonoidHom := actionOnForget G
          continuous_toFun := continuous_actionOnForget G }

/-- On every finite continuous action, the canonical homomorphism acts by the given action. -/
@[stacks 0BMU "component action of the canonical homomorphism"]
public theorem canonicalHom_apply (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (g : G) (X : ContAction FintypeCat.{u} G)
    (x : X.obj.V.obj) :
    let _ : TopologicalSpace (Aut (forget (ContAction FintypeCat.{u} G))) :=
      functorAutomorphismTopology _
    ConcreteCategory.hom (((canonicalHom G) g).asIso.hom.app X) x =
      ConcreteCategory.hom (X.obj.ρ g).asHom x := by
  show ConcreteCategory.hom (((actionOnForget G) g).asIso.hom.app X) x = _
  rfl

private theorem exists_action_matching_finite_family (G : Type u) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (γ : Aut (forget (ContAction FintypeCat.{u} G)))
    {I : Type v} [Finite I] (X : I → ContAction FintypeCat.{u} G)
    (x : ∀ i, (X i).obj.V.obj) :
    ∃ g : G, ∀ i, ConcreteCategory.hom ((X i).obj.ρ g).asHom (x i) =
      ConcreteCategory.hom (γ.asIso.hom.app (X i)) (x i) := by
  have : Fintype I := Fintype.ofFinite I
  let (i : I) : MulAction G ((X i).obj.V.obj) := by
    show MulAction G ((forget₂ (Action FintypeCat G) TopCat).obj (X i).obj)
    infer_instance
  let (i : I) : ContinuousSMul G ((X i).obj.V.obj) := contAction_continuousSMul G (X i)
  let E := ∀ i, (X i).obj.V.obj
  let : TopologicalSpace E := inferInstance
  let : Fintype E := Fintype.ofFinite E
  let : MulAction G E := inferInstance
  let : ContinuousSMul G E := inferInstance
  let ESmall : FintypeCat.{u} := FintypeCat.uSwitch.{max u v, u}.obj (FintypeCat.of E)
  let e : ESmall.obj ≃ E := FintypeCat.uSwitchEquiv.{max u v, u} (FintypeCat.of E)
  let : MulAction G ESmall.obj := e.mulAction G
  let : TopologicalSpace ESmall.obj := ⊥
  let : DiscreteTopology ESmall.obj := ⟨rfl⟩
  let : ContinuousSMul G ESmall.obj := by
    constructor
    have hp : Continuous (fun p : G × ESmall.obj => (p.1, e p.2)) :=
      continuous_fst.prodMk (continuous_of_discreteTopology.comp continuous_snd)
    show Continuous (fun p : G × ESmall.obj => e.symm (p.1 • e p.2))
    exact continuous_of_discreteTopology.comp (ContinuousSMul.continuous_smul.comp hp)
  have he_smul (g : G) (y : ESmall.obj) : e (g • y) = g • e y := e.apply_symm_apply _
  let x' : ESmall.obj := e.symm (fun i => x i)
  let O : Type u := {y : ESmall.obj // y ∈ MulAction.orbit G x'}
  let : Fintype O := Fintype.ofFinite O
  let : TopologicalSpace O := TopologicalSpace.induced (Subtype.val : O → ESmall.obj) inferInstance
  let : MulAction G O := inferInstance
  let : ContinuousSMul G O := by
    constructor
    apply continuous_induced_rng.mpr
    have hs : Continuous (fun p : G × O => p.1 • (p.2 : ESmall.obj)) :=
      ContinuousSMul.continuous_smul.comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
    show Continuous (fun p : G × O => (↑(p.1 • p.2) : ESmall.obj))
    exact hs
  have hOdisc : DiscreteTopology O := Finite.instDiscreteTopology
  have hOtop :
      (FintypeCatDiscrete.instTopologicalSpaceObjFinite (FintypeCat.of O) : TopologicalSpace O) =
        (inferInstance : TopologicalSpace O) :=
    hOdisc.eq_bot.symm
  let Q : Action FintypeCat G := Action.FintypeCat.ofMulAction G (FintypeCat.of O)
  have hQ : Q.IsContinuous := by
    show @ContinuousSMul G ((FintypeCat.of O).obj) _
      _ (FintypeCatDiscrete.instTopologicalSpaceObjFinite (FintypeCat.of O))
    rw [hOtop]
    infer_instance
  let Q' : ContAction FintypeCat.{u} G := ⟨Q, hQ⟩
  obtain ⟨γ⟩ := γ
  let xO : O := ⟨x', MulAction.mem_orbit_self _⟩
  let e₁ : ∀ i, Q' ⟶ X i := fun i => ObjectProperty.homMk {
    hom := FintypeCat.homMk (fun y : O => e y.1 i)
    comm := fun g => by
      ext y
      show e (g • y.1) i = g • e y.1 i
      rw [he_smul]
      rw [Pi.smul_apply] }
  let yO : O := ConcreteCategory.hom (γ.hom.app Q') xO
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp yO.2
  refine ⟨g, fun i => ?_⟩
  have hnat := NatTrans.naturality_apply (γ.hom) (e₁ i) xO
  have hmapx : ((forget (ContAction FintypeCat.{u} G)).map (e₁ i)) xO = x i := by
    show ConcreteCategory.hom ((e₁ i).hom.hom) xO = x i
    show e xO.1 i = x i
    simp [xO, x']
  have hmapy : ((forget (ContAction FintypeCat.{u} G)).map (e₁ i))
      ((γ.hom.app Q') xO) = e yO.1 i := by
    show ConcreteCategory.hom ((e₁ i).hom.hom) ((γ.hom.app Q') xO) = e yO.1 i
    show e (((γ.hom.app Q') xO).1) i = e yO.1 i
    rfl
  rw [hmapx, hmapy] at hnat
  change ConcreteCategory.hom ((γ.hom).app (X i)) (x i) = e yO.1 i at hnat
  have htuple : g • (fun j => x j) = e yO.1 := by
    have h := congrArg e hg
    simpa [x', he_smul] using h
  have hcoord : (g • (fun j => x j)) i = e yO.1 i :=
    congrArg (fun z : E => z i) htuple
  calc
    ConcreteCategory.hom ((X i).obj.ρ g).asHom (x i) = g • x i := rfl
    _ = ConcreteCategory.hom ((γ.hom).app (X i)) (x i) := by
      simpa using hcoord.trans hnat.symm

private theorem denseRange_canonicalHom (G : Type u) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] :
    let _ : TopologicalSpace (Aut (forget (ContAction FintypeCat.{u} G))) :=
      functorAutomorphismTopology _
    DenseRange (canonicalHom G) := by
  let : TopologicalSpace (Aut (forget (ContAction FintypeCat.{u} G))) :=
    functorAutomorphismTopology _
  apply dense_iff_inter_open.mpr
  rintro U ⟨s, hsO, hsv⟩ ⟨γ, hγ⟩
  rw [← hsv, Set.mem_preimage] at hγ
  rcases (isOpen_pi_iff.mp hsO) _ hγ with ⟨J, fJ, hJ1, hJ2⟩
  let I := Σ j : J, j.val.obj.V.obj
  let X : I → ContAction FintypeCat.{u} G := fun i => i.1.val
  let x : ∀ i, (X i).obj.V.obj := fun i => i.2
  obtain ⟨g, hg⟩ := exists_action_matching_finite_family G γ X x
  refine ⟨canonicalHom G g, ?_, g, rfl⟩
  rw [← hsv, Set.mem_preimage]
  apply hJ2
  intro j hj
  have heq :
      (componentEmbedding (forget (ContAction FintypeCat.{u} G))
        ((canonicalHom G) g)) j =
      (componentEmbedding (forget (ContAction FintypeCat.{u} G)) γ) j := by
    apply Equiv.ext
    intro y
    show ConcreteCategory.hom (((canonicalHom G) g).asIso.hom.app j) y =
      ConcreteCategory.hom (γ.asIso.hom.app j) y
    rw [canonicalHom_apply]
    simpa [X, x] using hg (⟨⟨j, hj⟩, y⟩ : I)
  exact Set.mem_of_eq_of_mem heq (hJ1 j hj).right

private noncomputable def quotientAutComponent
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (Q : ProfiniteGrp.{v}) (f : G →ₜ* Q) (U : OpenNormalSubgroup Q) :
    let _ : TopologicalSpace (Aut (forget (ContAction FintypeCat.{u} G))) :=
      functorAutomorphismTopology _
    Aut (forget (ContAction FintypeCat.{u} G)) →ₜ* (Q ⧸ U.toOpenSubgroup.toSubgroup) := by
  letI : TopologicalSpace (Aut (forget (ContAction FintypeCat.{u} G))) :=
    functorAutomorphismTopology _
  let A := Q ⧸ U.toOpenSubgroup.toSubgroup
  letI : Finite A := Subgroup.instFiniteQuotientOfSeparatelyContinuousMulOfCompactSpace
    U.toOpenSubgroup
  letI : Fintype A := Fintype.ofFinite A
  letI : DiscreteTopology A := QuotientGroup.discreteTopology U.toOpenSubgroup.isOpen'
  let Csmall : FintypeCat.{u} :=
    FintypeCat.uSwitch.{v, u}.obj (FintypeCat.of A)
  let e : Csmall.obj ≃ A := FintypeCat.uSwitchEquiv.{v, u} (FintypeCat.of A)
  letI : Group Csmall.obj := e.group
  letI : TopologicalSpace Csmall.obj := ⊥
  letI : DiscreteTopology Csmall.obj := ⟨rfl⟩
  let q : G →* A := (QuotientGroup.mk' U.toOpenSubgroup.toSubgroup).comp f.toMonoidHom
  let ψ : G →* Csmall.obj := e.mulEquiv.symm.toMonoidHom.comp q
  have hψ : Continuous ψ := by
    change Continuous (fun g => e.symm (QuotientGroup.mk' U.toOpenSubgroup.toSubgroup (f g)))
    exact (continuous_of_discreteTopology).comp
      (QuotientGroup.continuous_mk.comp f.continuous_toFun)
  letI : MulAction G Csmall.obj := MulAction.compHom Csmall.obj ψ
  letI : ContinuousSMul G Csmall.obj := by
    constructor
    change Continuous (fun p : G × Csmall.obj => ψ p.1 * p.2)
    exact continuous_mul.comp ((hψ.comp continuous_fst).prodMk continuous_snd)
  let Xact : Action FintypeCat G := Action.FintypeCat.ofMulAction G Csmall
  have hXact : Xact.IsContinuous := by
    change ContinuousSMul G Csmall.obj
    infer_instance
  let X : ContAction FintypeCat.{u} G := ⟨Xact, hXact⟩
  letI : Group X.obj.V.obj := e.group
  let r (z : X.obj.V.obj) : X ⟶ X := ObjectProperty.homMk {
    hom := FintypeCat.homMk (fun y : X.obj.V.obj => y * z)
    comm := fun g => by
      ext y
      let y' : Csmall.obj := y
      let z' : Csmall.obj := z
      change (ψ g * y') * z' = ψ g * (y' * z')
      simp [mul_assoc] }
  have hformula (γ : Aut (forget (ContAction FintypeCat.{u} G))) (z : X.obj.V.obj) :
      ConcreteCategory.hom (γ.asIso.hom.app X) z =
        ConcreteCategory.hom (γ.asIso.hom.app X) (1 : X.obj.V.obj) * z := by
    obtain ⟨γ⟩ := γ
    have h := NatTrans.naturality_apply γ.hom (r z) (1 : X.obj.V.obj)
    change ConcreteCategory.hom (γ.hom.app X) ((1 : X.obj.V.obj) * z) =
      ConcreteCategory.hom (γ.hom.app X) (1 : X.obj.V.obj) * z at h
    rwa [one_mul] at h
  let φ : Aut (forget (ContAction FintypeCat.{u} G)) →* X.obj.V.obj := {
    toFun γ := ConcreteCategory.hom (γ.asIso.hom.app X) 1
    map_one' := rfl
    map_mul' γ δ := by
      change ConcreteCategory.hom ((δ.asIso ≪≫ γ.asIso).hom.app X) 1 =
        ConcreteCategory.hom (γ.asIso.hom.app X) 1 * ConcreteCategory.hom (δ.asIso.hom.app X) 1
      exact hformula γ _ }
  have hφ : Continuous φ := by
    change Continuous (fun γ =>
      ⇑((componentEmbedding (forget (ContAction FintypeCat.{u} G)) γ) X)
        (1 : X.obj.V.obj))
    have hXperm : Continuous (fun γ =>
        (componentEmbedding (forget (ContAction FintypeCat.{u} G)) γ) X) :=
      (continuous_apply X).comp continuous_induced_dom
    have hX : Continuous (fun γ =>
        ⇑((componentEmbedding (forget (ContAction FintypeCat.{u} G)) γ) X)) :=
      continuous_induced_dom.comp hXperm
    exact (continuous_apply (1 : X.obj.V.obj)).comp hX
  have he_cont : Continuous (e : X.obj.V.obj → A) := continuous_of_discreteTopology
  exact {
    toMonoidHom := e.mulEquiv.toMonoidHom.comp φ
    continuous_toFun := he_cont.comp hφ }

private theorem quotientAutComponent_canonicalHom
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (Q : ProfiniteGrp.{v}) (f : G →ₜ* Q) (U : OpenNormalSubgroup Q) (g : G) :
    let _ : TopologicalSpace (Aut (forget (ContAction FintypeCat.{u} G))) :=
      functorAutomorphismTopology _
    quotientAutComponent G Q f U ((canonicalHom G) g) =
      QuotientGroup.mk' U.toOpenSubgroup.toSubgroup (f g) := by
  classical
  dsimp [quotientAutComponent]
  let A := Q ⧸ U.toOpenSubgroup.toSubgroup
  let : Finite A := Subgroup.instFiniteQuotientOfSeparatelyContinuousMulOfCompactSpace
    U.toOpenSubgroup
  let : Fintype A := Fintype.ofFinite A
  let : DiscreteTopology A := QuotientGroup.discreteTopology U.toOpenSubgroup.isOpen'
  let Csmall : FintypeCat.{u} :=
    FintypeCat.uSwitch.{v, u}.obj (FintypeCat.of A)
  let e : Csmall.obj ≃ A := FintypeCat.uSwitchEquiv.{v, u} (FintypeCat.of A)
  let : Group Csmall.obj := e.group
  let : TopologicalSpace Csmall.obj := ⊥
  let : DiscreteTopology Csmall.obj := ⟨rfl⟩
  let q : G →* A := (QuotientGroup.mk' U.toOpenSubgroup.toSubgroup).comp f.toMonoidHom
  let ψ : G →* Csmall.obj := e.mulEquiv.symm.toMonoidHom.comp q
  have hψ : Continuous ψ := by
    show Continuous (fun g => e.symm (QuotientGroup.mk' U.toOpenSubgroup.toSubgroup (f g)))
    exact (continuous_of_discreteTopology).comp
      (QuotientGroup.continuous_mk.comp f.continuous_toFun)
  let : MulAction G Csmall.obj := MulAction.compHom Csmall.obj ψ
  let : ContinuousSMul G Csmall.obj := by
    constructor
    show Continuous (fun p : G × Csmall.obj => ψ p.1 * p.2)
    exact continuous_mul.comp ((hψ.comp continuous_fst).prodMk continuous_snd)
  let Xact : Action FintypeCat G := Action.FintypeCat.ofMulAction G Csmall
  have hXact : Xact.IsContinuous := by
    show ContinuousSMul G Csmall.obj
    infer_instance
  let X : ContAction FintypeCat.{u} G := ⟨Xact, hXact⟩
  let : Group X.obj.V.obj := e.group
  show e (ConcreteCategory.hom (((canonicalHom G) g).asIso.hom.app X) 1) =
    QuotientGroup.mk' U.toOpenSubgroup.toSubgroup (f g)
  rw [canonicalHom_apply]
  show e (ψ g * (1 : Csmall.obj)) = q g
  simp only [mul_one]
  show e (e.symm (q g)) = q g
  exact e.apply_symm_apply _

private theorem quotientAutComponent_compatible
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (P : ProfiniteGrp.{v}) (f : G →ₜ* P) {U V : OpenNormalSubgroup P} (h : U ⟶ V) :
    let _ : TopologicalSpace (Aut (forget (ContAction FintypeCat.{u} G))) :=
      functorAutomorphismTopology _
    (fun γ => QuotientGroup.map U.toOpenSubgroup.toSubgroup
      V.toOpenSubgroup.toSubgroup (MonoidHom.id P) (leOfHom h)
      (quotientAutComponent G P f U γ)) =
      fun γ => quotientAutComponent G P f V γ := by
  let : TopologicalSpace (Aut (forget (ContAction FintypeCat.{u} G))) :=
    functorAutomorphismTopology _
  let qU := quotientAutComponent G P f U
  let qV := quotientAutComponent G P f V
  have hleft' : Continuous (fun γ => QuotientGroup.map U.toOpenSubgroup.toSubgroup
      V.toOpenSubgroup.toSubgroup (MonoidHom.id P) (leOfHom h) (qU γ)) :=
    continuous_of_discreteTopology.comp qU.continuous_toFun
  have heq' : (fun γ => QuotientGroup.map U.toOpenSubgroup.toSubgroup
      V.toOpenSubgroup.toSubgroup (MonoidHom.id P) (leOfHom h) (qU γ)) ∘ canonicalHom G =
      qV ∘ canonicalHom G := by
    funext g
    dsimp only [Function.comp_apply, qU, qV]
    rw [quotientAutComponent_canonicalHom, quotientAutComponent_canonicalHom]
    rfl
  exact (denseRange_canonicalHom G).equalizer hleft' qV.continuous_toFun heq'

private noncomputable def profiniteExtensionLimitHom
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (P : ProfiniteGrp.{v}) (f : G →ₜ* P) :
    let _ : TopologicalSpace (Aut (forget (ContAction FintypeCat.{u} G))) :=
      functorAutomorphismTopology _
    Aut (forget (ContAction FintypeCat.{u} G)) →* ProfiniteGrp.limit (P.diagram) := by
  letI : TopologicalSpace (Aut (forget (ContAction FintypeCat.{u} G))) :=
    functorAutomorphismTopology _
  exact {
    toFun γ := ⟨fun U => quotientAutComponent G P f U γ, fun U V h => by
      change QuotientGroup.map U.toOpenSubgroup.toSubgroup
          V.toOpenSubgroup.toSubgroup (MonoidHom.id P) (leOfHom h)
          (quotientAutComponent G P f U γ) = _
      exact congrFun (quotientAutComponent_compatible G P f h) γ⟩
    map_one' := by
      apply Subtype.val_inj.mp
      funext U
      exact (quotientAutComponent G P f U).map_one
    map_mul' γ δ := by
      apply Subtype.val_inj.mp
      funext U
      change (quotientAutComponent G P f U) (γ * δ) =
        (quotientAutComponent G P f U) γ * (quotientAutComponent G P f U) δ
      exact (quotientAutComponent G P f U).map_mul γ δ }

private theorem continuous_profiniteExtensionLimitHom
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (P : ProfiniteGrp.{v}) (f : G →ₜ* P) :
    let _ : TopologicalSpace (Aut (forget (ContAction FintypeCat.{u} G))) :=
      functorAutomorphismTopology _
    Continuous (profiniteExtensionLimitHom G P f) := by
  let : TopologicalSpace (Aut (forget (ContAction FintypeCat.{u} G))) :=
    functorAutomorphismTopology _
  apply continuous_induced_rng.mpr
  apply continuous_pi_iff.mpr
  intro U
  let qU := quotientAutComponent G P f U
  let : DiscreteTopology (P ⧸ U.toOpenSubgroup.toSubgroup) :=
    QuotientGroup.discreteTopology U.toOpenSubgroup.isOpen'
  let : TopologicalSpace ((P.diagram.obj U).toProfinite.toTop) := ⊥
  let : DiscreteTopology ((P.diagram.obj U).toProfinite.toTop) := ⟨rfl⟩
  have htop : (QuotientGroup.instTopologicalSpace U.toOpenSubgroup.toSubgroup :
      TopologicalSpace (P ⧸ U.toOpenSubgroup.toSubgroup)) =
      (P.diagram.obj U).toProfinite.toTop.str :=
    DiscreteTopology.eq_bot
  show @Continuous (Aut (forget (ContAction FintypeCat.{u} G)))
    (P ⧸ U.toOpenSubgroup.toSubgroup)
    (functorAutomorphismTopology _) (P.diagram.obj U).toProfinite.toTop.str
    (fun γ => qU γ)
  rw [← htop]
  exact qU.continuous_toFun

private noncomputable def profiniteExtension
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (P : ProfiniteGrp.{v}) (f : G →ₜ* P) :
    let _ : TopologicalSpace (Aut (forget (ContAction FintypeCat.{u} G))) :=
      functorAutomorphismTopology _
    Aut (forget (ContAction FintypeCat.{u} G)) →ₜ* P := by
  letI : TopologicalSpace (Aut (forget (ContAction FintypeCat.{u} G))) :=
    functorAutomorphismTopology _
  let e := ProfiniteGrp.continuousMulEquivLimittoFiniteQuotientFunctor P
  exact {
    toMonoidHom := e.symm.toMonoidHom.comp (profiniteExtensionLimitHom G P f)
    continuous_toFun :=
      e.symm.continuous_toFun.comp (continuous_profiniteExtensionLimitHom G P f) }

private theorem profiniteExtension_comp_canonicalHom
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (P : ProfiniteGrp.{v}) (f : G →ₜ* P) :
    let _ : TopologicalSpace (Aut (forget (ContAction FintypeCat.{u} G))) :=
      functorAutomorphismTopology _
    (profiniteExtension G P f).comp (canonicalHom G) = f := by
  let : TopologicalSpace (Aut (forget (ContAction FintypeCat.{u} G))) :=
    functorAutomorphismTopology _
  let e := ProfiniteGrp.continuousMulEquivLimittoFiniteQuotientFunctor P
  apply ContinuousMonoidHom.ext
  intro g
  show (profiniteExtension G P f) ((canonicalHom G) g) = f g
  show e.symm (profiniteExtensionLimitHom G P f ((canonicalHom G) g)) = f g
  have hlim : profiniteExtensionLimitHom G P f ((canonicalHom G) g) = e (f g) := by
    apply Subtype.ext
    funext U
    show quotientAutComponent G P f U ((canonicalHom G) g) = _
    rw [quotientAutComponent_canonicalHom]
    rfl
  simpa using congrArg e.symm hlim

/-- The automorphism group of the forgetful functor on finite continuous `G`-sets, with its
componentwise topology, is canonically the profinite completion of `G`. -/
@[stacks 0BMU "profinite completion universal property"]
public theorem profiniteCompletionEquiv_forgetAut
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    let _ : TopologicalSpace (Aut (forget (ContAction FintypeCat.{u} G))) :=
      functorAutomorphismTopology _
    let _ : IsTopologicalGroup (Aut (forget (ContAction FintypeCat.{u} G))) :=
      functorAutomorphismIsTopologicalGroup _
    IsProfiniteCompletion.{u, u + 1, w} (canonicalHom G) := by
  let : TopologicalSpace (Aut (forget (ContAction FintypeCat.{u} G))) :=
    functorAutomorphismTopology _
  let : IsTopologicalGroup (Aut (forget (ContAction FintypeCat.{u} G))) :=
    functorAutomorphismIsTopologicalGroup _
  show Stacks.Chapter05.Tag_0BR1.IsProfiniteTop
    (Aut (forget (ContAction FintypeCat.{u} G))) ∧ _
  refine ⟨isProfiniteGrp_functorAutomorphismTopology _, fun Q _ _ _ hQ => ?_⟩
  let : CompactSpace Q := hQ.1
  let : T2Space Q := hQ.2.1
  let : TotallyDisconnectedSpace Q := hQ.2.2
  refine ⟨fun f g hfg => ?_, fun f => ⟨profiniteExtension G (ProfiniteGrp.of Q) f,
    profiniteExtension_comp_canonicalHom G (ProfiniteGrp.of Q) f⟩⟩
  have hcomp : (fun x : G => f (canonicalHom G x)) = (fun x : G => g (canonicalHom G x)) :=
    funext fun x => congrArg (fun k : G →ₜ* Q => k x) hfg
  exact ContinuousMonoidHom.ext <| congrFun <|
    (denseRange_canonicalHom G).equalizer f.continuous_toFun g.continuous_toFun hcomp

end CategoryTheory
