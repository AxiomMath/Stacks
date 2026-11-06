module

public import Mathlib.CategoryTheory.Abelian.ShortExact
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.ExtComparison
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.DiscreteTopology

/-!
# Finite dimensionality of the first continuous cohomology group

Let `G` be a topological group, `k` a field and `V` a continuous discrete `k`-`G`-module which is
finite dimensional over `k`. If `G` is topologically finitely generated, that is if some finite
subset of `G` generates a dense subgroup, then `H¹(G, V)` is finite dimensional over `k`.

## Main definitions

* `Stacks.ContinuousCohomology.cocycles₁` — the continuous `1`-cocycles `Z¹(G, V)`, the locally
  constant crossed homomorphisms `G → V`.
* `Stacks.ContinuousCohomology.cocyclesExtension` — the extension of `Z¹(G, V)` with its trivial
  action by `V`, on which a group element acts by `(x, f) ↦ (g · x + f g, f)`.

## Main results

* `Stacks.ContinuousCohomology.finite_cocycles₁` — `Z¹(G, V)` is finite dimensional when `V` is
  finite dimensional and `G` is topologically finitely generated.
* `Stacks.ContinuousCohomology.cocyclesToExt_surjective` — every class in `Ext¹(k, V)` is the
  class of the extension obtained from `cocyclesExtension` by restricting along a cocycle.
* `Stacks.ContinuousCohomology.finite_cohomologyFunctor_one` — the first continuous cohomology of
  a finite dimensional coefficient module of a topologically finitely generated group is finite
  dimensional.

## Implementation notes

Continuity of a cochain `G → V` is local constancy, the module `V` being discrete.

## References

* [Stacks Project, Tag 0DVF](https://stacks.math.columbia.edu/tag/0DVF)
* [Stacks Project, Tag 0DVE](https://stacks.math.columbia.edu/tag/0DVE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe d u v w

namespace Stacks.ContinuousCohomology

attribute [local instance] Stacks.DiscreteModuleTopology.hasForget₂ModuleCatTopCat
  Stacks.DiscreteModuleTopology.actionDiscreteTopology

section Cocycles

variable (k : Type u) [Field k] (G : Type v) [Group G] [TopologicalSpace G]

/-- The continuous `1`-cocycles `Z¹(G, V)` of a continuous discrete `k`-`G`-module `V`: the
locally constant crossed homomorphisms, the maps `f : G → V` with `f (g h) = g · f h + f g`. -/
def cocycles₁ (V : Stacks.Injectives.ContinuousModule.{u, v, w} k G) :
    Submodule k (G → V.obj.obj.V) where
  carrier := {f | (∀ g h : G, f (g * h) = rep k G V g (f h) + f g) ∧ IsLocallyConstant f}
  zero_mem' := ⟨fun g h => by simp, IsLocallyConstant.const 0⟩
  add_mem' {f₁ f₂} hf₁ hf₂ :=
    ⟨fun x y => by
      simp only [Pi.add_apply, hf₁.1 x y, hf₂.1 x y, map_add]
      abel, hf₁.2.comp₂ hf₂.2 (· + ·)⟩
  smul_mem' c f hf :=
    ⟨fun x y => by
      simp only [Pi.smul_apply, hf.1 x y, map_smul, smul_add], hf.2.comp (c • ·)⟩

variable {k G}

/-- Membership in `Z¹(G, V)` is the crossed homomorphism identity together with local
constancy. -/
lemma mem_cocycles₁_iff {V : Stacks.Injectives.ContinuousModule.{u, v, w} k G}
    (f : G → V.obj.obj.V) :
    f ∈ cocycles₁ k G V ↔
      (∀ g h : G, f (g * h) = rep k G V g (f h) + f g) ∧ IsLocallyConstant f := Iff.rfl

/-- A crossed homomorphism vanishes at the identity. -/
lemma apply_one_eq_zero_of_mem_cocycles₁
    {V : Stacks.Injectives.ContinuousModule.{u, v, w} k G} {f : G → V.obj.obj.V}
    (hf : f ∈ cocycles₁ k G V) : f 1 = 0 := by
  have h := hf.1 1 1
  rwa [one_mul, show rep k G V 1 = LinearMap.id from map_one _, LinearMap.id_apply,
    left_eq_add] at h

/-- The group elements on which a crossed homomorphism vanishes form a subgroup. -/
def vanishingSubgroup {V : Stacks.Injectives.ContinuousModule.{u, v, w} k G}
    {f : G → V.obj.obj.V} (hf : f ∈ cocycles₁ k G V) : Subgroup G where
  carrier := {g | f g = 0}
  one_mem' := apply_one_eq_zero_of_mem_cocycles₁ hf
  mul_mem' {g h} hg hh := by
    change f g = 0 at hg
    change f h = 0 at hh
    change f (g * h) = 0
    rw [hf.1 g h, hh, hg, map_zero, zero_add]
  inv_mem' {g} hg := by
    change f g = 0 at hg
    change f g⁻¹ = 0
    have h := hf.1 g g⁻¹
    rw [mul_inv_cancel, apply_one_eq_zero_of_mem_cocycles₁ hf, hg, add_zero] at h
    have hρ : rep k G V g⁻¹ * rep k G V g = LinearMap.id := by
      rw [← map_mul, inv_mul_cancel]
      exact map_one _
    have h₂ : rep k G V g⁻¹ (rep k G V g (f g⁻¹)) = f g⁻¹ := LinearMap.congr_fun hρ (f g⁻¹)
    rw [← h₂, ← h, map_zero]

/-- **A continuous cocycle is determined by its values on a topological generating set**: a
continuous cocycle vanishing on a set `S` generating a dense subgroup is zero. -/
theorem eq_zero_of_mem_cocycles₁_of_eqOn
    {V : Stacks.Injectives.ContinuousModule.{u, v, w} k G} {S : Set G}
    (hS : Dense ((Subgroup.closure S : Subgroup G) : Set G)) {f : G → V.obj.obj.V}
    (hf : f ∈ cocycles₁ k G V) (hzero : ∀ s ∈ S, f s = 0) : f = 0 := by
  have hgen : Subgroup.closure S ≤ vanishingSubgroup hf :=
    (Subgroup.closure_le (vanishingSubgroup hf)).2 fun x hx => hzero x hx
  have hsub : closure ((Subgroup.closure S : Subgroup G) : Set G)
      ⊆ ((vanishingSubgroup hf : Subgroup G) : Set G) :=
    closure_minimal (SetLike.coe_subset_coe.2 hgen) (hf.2.isClosed_fiber 0)
  funext g
  exact hsub (by rw [hS.closure_eq]; exact Set.mem_univ g)

/-- Evaluation of continuous cocycles on a finite subset of the group. -/
def cocycles₁Eval (V : Stacks.Injectives.ContinuousModule.{u, v, w} k G) (S : Finset G) :
    cocycles₁ k G V →ₗ[k] (S → V.obj.obj.V) where
  toFun f s := f.1 s
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **`Z¹(G, V)` is finite dimensional for `V` finite dimensional and `G` topologically finitely
generated.** -/
theorem finite_cocycles₁ (V : Stacks.Injectives.ContinuousModule.{u, v, w} k G)
    [Module.Finite k V.obj.obj.V] {S : Finset G}
    (hS : Dense ((Subgroup.closure (S : Set G) : Subgroup G) : Set G)) :
    Module.Finite k (cocycles₁ k G V) := by
  refine Module.Finite.of_injective (cocycles₁Eval V S) fun f g h => Subtype.ext <|
    sub_eq_zero.mp <| eq_zero_of_mem_cocycles₁_of_eqOn hS (sub_mem f.2 g.2) fun s hs =>
      sub_eq_zero.mpr (congrFun h ⟨s, hs⟩)

end Cocycles

section UniversalExtension

variable {k : Type u} [Field k] {G : Type v} [Group G] [TopologicalSpace G]
  (V : Stacks.Injectives.ContinuousModule.{u, v, max u v w} k G)

/-- The action of `G` on `V × Z¹(G, V)` by `g · (x, f) = (g · x + f g, f)`. -/
def cocyclesExtensionAction : Action (ModuleCat.{max u v w} k) G where
  V := ModuleCat.of k (V.obj.obj.V × cocycles₁.{u, v, max u v w} k G V)
  ρ :=
    { toFun g := End.of <| ModuleCat.ofHom
        { toFun p := (rep k G V g p.1 + p.2.1 g, p.2)
          map_add' p q := by
            refine Prod.ext ?_ rfl
            change rep k G V g (p.1 + q.1) + (p.2 + q.2 : cocycles₁.{u, v, max u v w} k G V).1 g
              = rep k G V g p.1 + p.2.1 g + (rep k G V g q.1 + q.2.1 g)
            rw [map_add]
            simp only [Submodule.coe_add, Pi.add_apply]
            abel
          map_smul' c p := by
            refine Prod.ext ?_ rfl
            change rep k G V g (c • p.1) + (c • p.2 : cocycles₁.{u, v, max u v w} k G V).1 g
              = c • (rep k G V g p.1 + p.2.1 g)
            rw [map_smul]
            simp only [Submodule.coe_smul, Pi.smul_apply, smul_add] }
      map_one' := by
        refine End.ext <| ModuleCat.hom_ext (LinearMap.ext fun p => Prod.ext ?_ rfl)
        change rep k G V 1 p.1 + p.2.1 1 = p.1
        rw [show rep k G V 1 = LinearMap.id from map_one _, LinearMap.id_apply,
          apply_one_eq_zero_of_mem_cocycles₁ p.2.2, add_zero]
      map_mul' g h := by
        refine End.ext <| ModuleCat.hom_ext (LinearMap.ext fun p => Prod.ext ?_ rfl)
        change rep k G V (g * h) p.1 + p.2.1 (g * h)
          = rep k G V g (rep k G V h p.1 + p.2.1 h) + p.2.1 g
        rw [map_mul, Module.End.mul_eq_comp, LinearMap.comp_apply, p.2.2.1 g h, map_add]
        abel }

/-- The extension `0 → V → V × Z¹(G, V) → Z¹(G, V) → 0` of continuous discrete `k`-`G`-modules,
whose middle term carries the action `g · (x, f) = (g · x + f g, f)`. -/
def cocyclesExtension : Stacks.Injectives.ContinuousModule.{u, v, max u v w} k G :=
  ⟨⟨cocyclesExtensionAction.{u, v, w} V, by
      refine (Action.isContinuous_def _).2 ?_
      rw [continuous_prod_of_discrete_right]
      rintro ⟨x, f⟩
      exact IsLocallyConstant.continuous
        (((isLocallyConstant_rep k G V x).comp₂ f.2.2 (· + ·)).comp
          (fun y => (y, f)))⟩, ⟨rfl⟩⟩

/-- The module `Z¹(G, V)` of continuous cocycles with the trivial action of `G`. -/
def cocyclesTrivial : Stacks.Injectives.ContinuousModule.{u, v, max u v w} k G :=
  ⟨⟨Action.trivial G (ModuleCat.of k (cocycles₁.{u, v, max u v w} k G V)), by
      refine (Action.isContinuous_def _).2 ?_
      rw [continuous_prod_of_discrete_right]
      exact fun _ => continuous_const⟩, ⟨rfl⟩⟩

/-- The inclusion of `V` as the fibre of `cocyclesExtension` over the zero cocycle. -/
def cocyclesExtensionι : V ⟶ cocyclesExtension.{u, v, w} V :=
  ObjectProperty.homMk (ObjectProperty.homMk
    { hom := ModuleCat.ofHom
        { toFun x := (x, 0)
          map_add' x y := Prod.ext rfl (by simp)
          map_smul' c x := Prod.ext rfl (by simp) }
      comm := fun g => ModuleCat.hom_ext (LinearMap.ext fun x => Prod.ext (by
        change rep k G V g x = rep k G V g x + (0 : cocycles₁.{u, v, max u v w} k G V).1 g
        simp) rfl) })

/-- The projection of `cocyclesExtension` onto the trivially acting module of cocycles. -/
def cocyclesExtensionπ : cocyclesExtension.{u, v, w} V ⟶ cocyclesTrivial.{u, v, w} V :=
  ObjectProperty.homMk (ObjectProperty.homMk
    { hom := ModuleCat.ofHom
        { toFun p := p.2
          map_add' _ _ := rfl
          map_smul' _ _ := rfl }
      comm := fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl) })

/-- The short complex `V → V × Z¹(G, V) → Z¹(G, V)`. -/
def cocyclesExtensionComplex :
    ShortComplex (Stacks.Injectives.ContinuousModule.{u, v, max u v w} k G) :=
  ShortComplex.mk (cocyclesExtensionι.{u, v, w} V) (cocyclesExtensionπ.{u, v, w} V)
    (by
      apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      apply Action.hom_ext
      exact ModuleCat.hom_ext (LinearMap.ext fun _ => rfl))

/-- **The universal extension is short exact.** -/
theorem cocyclesExtension_shortExact : (cocyclesExtensionComplex.{u, v, w} V).ShortExact := by
  apply CategoryTheory.ShortExact.reflects_shortExact_of_faithful
    (continuousModuleUnderlying.{u, v, max u v w} k G)
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    intro x
    refine ⟨fun hx => ⟨x.1, ?_⟩, ?_⟩
    · exact Prod.ext rfl (show x.2 = 0 from hx).symm
    · rintro ⟨y, rfl⟩
      rfl
  · rw [ModuleCat.mono_iff_injective]
    exact fun x y hxy => congrArg Prod.fst hxy
  · rw [ModuleCat.epi_iff_surjective]
    exact fun f => ⟨(0, f), rfl⟩

end UniversalExtension

section ExtSurjection

variable {k : Type u} [Field k] {G : Type v} [Group G] [TopologicalSpace G]
  [HasExt.{max u v w} (Stacks.Injectives.ContinuousModule.{u, v, max u v w} k G)]
  (V : Stacks.Injectives.ContinuousModule.{u, v, max u v w} k G)

/-- Scalar multiples of a cocycle, as a morphism from the trivial module `k` to the trivially
acting module of cocycles. -/
def cocyclesToHom :
    cocycles₁.{u, v, max u v w} k G V →ₗ[k]
      (trivialModule.{u, v, w} k G ⟶ cocyclesTrivial.{u, v, w} V) where
  toFun f := ObjectProperty.homMk (ObjectProperty.homMk
    { hom := ModuleCat.ofHom
        { toFun (x : ULift.{max u v w} k) := x.down • f
          map_add' x y := add_smul _ _ _
          map_smul' c x := mul_smul _ _ _ }
      comm := fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl) })
  map_add' f g := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    change x.down • (f + g) = x.down • f + x.down • g
    exact smul_add _ _ _
  map_smul' c f := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    change x.down • (c • f) = c • (x.down • f)
    rw [smul_smul, smul_smul, mul_comm]

/-- The class of the universal extension in `Ext¹(Z¹(G, V), V)`. -/
def cocyclesExtensionClass : Ext.{max u v w} (cocyclesTrivial.{u, v, w} V) V 1 :=
  (cocyclesExtension_shortExact.{u, v, w} V).extClass

/-- Restricting the universal extension along a cocycle, as a `k`-linear map from `Z¹(G, V)` to
`Ext¹(k, V)`. -/
def cocyclesToExt :
    cocycles₁.{u, v, max u v w} k G V →ₗ[k] Ext.{max u v w} (trivialModule.{u, v, w} k G) V 1 where
  toFun f := (Ext.mk₀ (cocyclesToHom.{u, v, w} V f)).comp
    (cocyclesExtensionClass.{u, v, w} V) (zero_add 1)
  map_add' f g := by rw [map_add, Ext.mk₀_add, Ext.add_comp]
  map_smul' c f := by
    simp only [RingHom.id_apply, map_smul, Ext.mk₀_smul, Ext.smul_comp]

/-- **Every class in `Ext¹(k, V)` comes from a continuous cocycle**: every class is the restriction
of the universal extension along a cocycle. -/
theorem cocyclesToExt_surjective :
    Function.Surjective (cocyclesToExt.{u, v, w} V) := by
  classical
  intro ξ
  let K := trivialModule.{u, v, w} k G
  let F := continuousModuleUnderlying.{u, v, max u v w} k G
  obtain ⟨E, i, p, hz, hE, hξ⟩ :=
    (Ext.extClass_surjective_and_eq_iff_iso_and_baerSum
      (Stacks.Injectives.ContinuousModule.{u, v, max u v w} k G) K V).1 ξ
  have hMapped : ((ShortComplex.mk i p hz).map F).ShortExact := hE.map_of_exact F
  have hp : Function.Surjective (F.map p).hom :=
    (ModuleCat.epi_iff_surjective (F.map p)).1 hMapped.epi_g
  let j : V.obj.obj.V →ₗ[k] E.obj.obj.V := i.hom.hom.hom.hom
  let q : E.obj.obj.V →ₗ[k] K.obj.obj.V := p.hom.hom.hom.hom
  let e : E.obj.obj.V := Classical.choose (hp (ULift.up (1 : k)))
  have he0 : q e = ULift.up (1 : k) := Classical.choose_spec (hp (ULift.up (1 : k)))
  have hexact : Function.Exact j q := by
    have hx := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
      ((ShortComplex.mk i p hz).map F)).mp hMapped.exact
    convert hx using 1 <;> rfl
  have hj : Function.Injective j := by
    have hi := (ModuleCat.mono_iff_injective (F.map i)).1 hMapped.mono_f
    convert hi using 1 <;> rfl
  have hji (g : G) (x : V.obj.obj.V) : j (rep k G V g x) = rep k G E g (j x) :=
    congrArg (fun z : ModuleCat.Hom _ _ => z.hom x) (i.hom.hom.comm g)
  have hqAction (g : G) (x : E.obj.obj.V) : q (rep k G E g x) = q x :=
    congrArg (fun z : ModuleCat.Hom _ _ => z.hom x) (p.hom.hom.comm g)
  let δ : G → E.obj.obj.V := fun g => rep k G E g e - e
  have hqδ (g : G) : q (δ g) = 0 := by
    show q (rep k G E g e - e) = 0
    rw [map_sub, hqAction g e, sub_self]
  let f : G → V.obj.obj.V := fun g => Classical.choose ((hexact (δ g)).mp (hqδ g))
  have hjf (g : G) : j (f g) = δ g := Classical.choose_spec ((hexact (δ g)).mp (hqδ g))
  have hfcocycle : ∀ g h : G, f (g * h) = rep k G V g (f h) + f g := by
    intro g h
    apply hj
    calc j (f (g * h)) = δ (g * h) := hjf _
      _ = rep k G E g (δ h) + δ g := by
        show rep k G E (g * h) e - e
          = rep k G E g (rep k G E h e - e) + (rep k G E g e - e)
        simp only [map_mul, Module.End.mul_eq_comp, LinearMap.comp_apply, map_sub]
        module
      _ = j (rep k G V g (f h) + f g) := by
        rw [map_add, ← hjf h, ← hjf g, ← hji g (f h)]
  have hδloc : IsLocallyConstant δ :=
    (isLocallyConstant_rep k G E e).comp (fun y => y - e)
  have hfloc : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_isOpen_fiber]
    intro y
    have hfib : f ⁻¹' {y} = δ ⁻¹' {j y} := by
      ext g
      simp only [Set.mem_preimage, Set.mem_singleton_iff, ← hjf g]
      exact ⟨fun hgy => by rw [hgy], fun hgy => hj hgy⟩
    rw [hfib]
    exact hδloc _
  let cf : cocycles₁.{u, v, max u v w} k G V := ⟨f, hfcocycle, hfloc⟩
  let s : K.obj.obj.V →ₗ[k] E.obj.obj.V :=
    { toFun x := x.down • e
      map_add' x y := add_smul _ _ _
      map_smul' c x := mul_smul _ _ _ }
  have hs (x : K.obj.obj.V) : q (s x) = x := by
    show q (x.down • e) = x
    rw [map_smul, he0]
    exact ULift.ext (mul_one x.down)
  have hqPart (x : E.obj.obj.V) : q (x - s (q x)) = 0 := by
    rw [map_sub, hs, sub_self]
  let vpart : E.obj.obj.V → V.obj.obj.V := fun x =>
    Classical.choose ((hexact (x - s (q x))).mp (hqPart x))
  have hvpart (x : E.obj.obj.V) : j (vpart x) = x - s (q x) :=
    Classical.choose_spec ((hexact (x - s (q x))).mp (hqPart x))
  have hvadd (x y : E.obj.obj.V) : vpart (x + y) = vpart x + vpart y := by
    apply hj
    calc j (vpart (x + y)) = x + y - s (q (x + y)) := hvpart _
      _ = (x - s (q x)) + (y - s (q y)) := by rw [map_add q, map_add s]; abel
      _ = j (vpart x + vpart y) := by rw [map_add, ← hvpart x, ← hvpart y]
  have hvsmul (c : k) (x : E.obj.obj.V) : vpart (c • x) = c • vpart x := by
    apply hj
    calc j (vpart (c • x)) = c • x - s (q (c • x)) := hvpart _
      _ = c • (x - s (q x)) := by rw [map_smul q, map_smul s]; module
      _ = j (c • vpart x) := by rw [map_smul, ← hvpart x]
  have hvAction (g : G) (x : E.obj.obj.V) :
      vpart (rep k G E g x) = rep k G V g (vpart x) + (q x).down • f g := by
    apply hj
    calc j (vpart (rep k G E g x)) = rep k G E g x - s (q (rep k G E g x)) := hvpart _
      _ = rep k G E g x - s (q x) := by rw [hqAction]
      _ = rep k G E g (x - s (q x)) + (q x).down • δ g := by
        show rep k G E g x - (q x).down • e
          = rep k G E g (x - (q x).down • e) + (q x).down • (rep k G E g e - e)
        simp only [map_sub, map_smul]
        module
      _ = j (rep k G V g (vpart x) + (q x).down • f g) := by
        rw [map_add, map_smul, ← hvpart x, ← hjf g, ← hji g (vpart x)]
  let u : E ⟶ cocyclesExtension.{u, v, w} V :=
    ObjectProperty.homMk (ObjectProperty.homMk
      { hom := ModuleCat.ofHom
          { toFun x := (vpart x, (q x).down • cf)
            map_add' x y := by
              refine Prod.ext (hvadd x y) ?_
              show (q (x + y)).down • cf = (q x).down • cf + (q y).down • cf
              rw [map_add]
              exact add_smul _ _ _
            map_smul' c x := by
              refine Prod.ext (hvsmul c x) ?_
              show (q (c • x)).down • cf = c • ((q x).down • cf)
              rw [map_smul]
              exact mul_smul _ _ _ }
        comm := fun g => ModuleCat.hom_ext (LinearMap.ext fun x => Prod.ext (by
          show vpart (rep k G E g x) = rep k G V g (vpart x) + (q x).down • f g
          rw [hvAction]) (by
          show (q (rep k G E g x)).down • cf = (q x).down • cf
          rw [hqAction])) })
  have hqj (x : V.obj.obj.V) : q (j x) = 0 := (hexact (j x)).mpr ⟨x, rfl⟩
  have hvj (x : V.obj.obj.V) : vpart (j x) = x := by
    apply hj
    rw [hvpart, hqj, map_zero, sub_zero]
  have hIncl : i ≫ u = cocyclesExtensionι.{u, v, w} V := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    refine ModuleCat.hom_ext (LinearMap.ext fun x => Prod.ext (hvj x) ?_)
    show (q (j x)).down • cf = 0
    rw [show (q (j x)).down = 0 from congrArg ULift.down (hqj x), zero_smul]
  have hProj : u ≫ cocyclesExtensionπ.{u, v, w} V = p ≫ cocyclesToHom.{u, v, w} V cf := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    exact ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)
  let φ : ShortComplex.mk i p hz ⟶ cocyclesExtensionComplex.{u, v, w} V :=
    { τ₁ := 𝟙 V
      τ₂ := u
      τ₃ := cocyclesToHom.{u, v, w} V cf
      comm₁₂ := by simpa [cocyclesExtensionComplex] using hIncl.symm
      comm₂₃ := by simpa [cocyclesExtensionComplex] using hProj }
  have hNat : hE.extClass.comp (Ext.mk₀ (𝟙 V)) (add_zero 1)
      = (Ext.mk₀ (cocyclesToHom.{u, v, w} V cf)).comp
          (cocyclesExtensionClass.{u, v, w} V) (zero_add 1) :=
    ShortComplex.ShortExact.extClass_naturality hE (cocyclesExtension_shortExact.{u, v, w} V) φ
  rw [Ext.comp_mk₀_id] at hNat
  exact ⟨cf, hNat.symm.trans hξ⟩

end ExtSurjection

section Main

variable (k : Type u) [Field k] (G : Type v) [Group G] [TopologicalSpace G]

/-- The underlying module of the trivial module `k` is finite over `k`. -/
instance finite_trivialModule :
    Module.Finite k ((trivialModule.{u, v, w} k G).obj.obj.V) :=
  inferInstanceAs (Module.Finite k (ULift.{max u v w} k))

/-- The underlying module of the trivial module `k` is projective over `k`. -/
instance projective_trivialModule :
    Module.Projective k ((trivialModule.{u, v, w} k G).obj.obj.V) :=
  inferInstanceAs (Module.Projective k (ULift.{max u v w} k))

variable {k G}

/-- **The coefficient module of the comparison at the trivial module is the module itself**:
`kᵛ ⊗_k V ≅ V`. -/
def dualTensorTrivialIso
    (V : Stacks.Injectives.ContinuousModule.{u, v, max u v w} k G) :
    dualTensorContinuousModule.{u, v, max u v w} k G (trivialModule.{u, v, w} k G) V ≅ V := by
  let K := trivialModule.{u, v, w} k G
  let P := continuousDualTensor.{u, v, max u v w} k G K V
  let eEval : (K.obj.obj.V →ₗ[k] V.obj.obj.V) ≃ₗ[k] V.obj.obj.V :=
    { toFun f := f (ULift.up 1)
      invFun y := uliftSpan.{max u v w} k (V.obj.obj.V : Type max u v w) y
      left_inv f := LinearMap.ext fun n =>
        uliftSpan_eq.{max u v w} k (V.obj.obj.V : Type max u v w) f n
      right_inv y := uliftSpan_up_one.{max u v w} k (V.obj.obj.V : Type max u v w) y
      map_add' f g := rfl
      map_smul' c f := rfl }
  let eHom : (Representation.linHom (rep k G K) (rep k G V)).Equiv (rep k G V) :=
    Representation.Equiv.mk eEval (by
      intro g
      refine LinearMap.ext fun f => ?_
      change rep k G V g (f (rep k G K g⁻¹ (ULift.up (1 : k))))
        = rep k G V g (f (ULift.up (1 : k)))
      congr 1)
  let eRep : (rep k G P.1).Equiv (rep k G V) :=
    P.2.trans ((Representation.Equiv.dualTensorHom (rep k G K) (rep k G V)).trans eHom)
  refine ObjectProperty.isoMk _ (ObjectProperty.isoMk _
    { hom :=
        { hom := ModuleCat.ofHom eRep.toLinearEquiv.toLinearMap
          comm := fun g => ModuleCat.hom_ext (eRep.isIntertwining' g) }
      inv :=
        { hom := ModuleCat.ofHom eRep.symm.toLinearEquiv.toLinearMap
          comm := fun g => ModuleCat.hom_ext (eRep.symm.isIntertwining' g) }
      hom_inv_id := Action.hom_ext _ _ (ModuleCat.hom_ext (LinearMap.ext fun x =>
        eRep.toLinearEquiv.left_inv x))
      inv_hom_id := Action.hom_ext _ _ (ModuleCat.hom_ext (LinearMap.ext fun x =>
        eRep.toLinearEquiv.right_inv x)) })

variable [IsTopologicalGroup G]
  [HasDerivedCategory.{d} (Stacks.Injectives.ContinuousModule.{u, v, max u v w} k G)]
  [HasDerivedCategory.{d} (ModuleCat.{max u v w} k)]

/-- Let `G` be a topological group, `k` a field and `V` a `k`-`G`-module, that is a `k`-module with
a continuous action of `G` for the discrete topology on `V`. If `G` is topologically finitely
generated, so that some finite subset generates a dense subgroup, and `V` is finite dimensional
over `k`, then the first continuous cohomology group `H¹(G, V)` is finite dimensional over `k`. -/
@[stacks 0DVF]
theorem finite_cohomologyFunctor_one
    (hG : ∃ S : Finset G, Dense ((Subgroup.closure (S : Set G) : Subgroup G) : Set G))
    (V : Stacks.Injectives.ContinuousModule.{u, v, max u v w} k G)
    [Module.Finite k V.obj.obj.V] :
    Module.Finite k ((cohomologyFunctor.{d, u, v, w} k G 1).obj V) := by
  obtain ⟨S, hS⟩ := hG
  have : HasExt.{max u v w}
      (Stacks.Injectives.ContinuousModule.{u, v, max u v w} k G) :=
    hasExt_continuousModule k G
  have : Module.Finite k (cocycles₁.{u, v, max u v w} k G V) := finite_cocycles₁ V hS
  have : Module.Finite k
      (Ext.{max u v w} (trivialModule.{u, v, w} k G) V 1) :=
    Module.Finite.of_surjective (cocyclesToExt.{u, v, w} V)
      (cocyclesToExt_surjective.{u, v, w} V)
  have : Module.Finite k ((cohomologyFunctor.{d, u, v, w} k G 1).obj
      (dualTensorContinuousModule.{u, v, max u v w} k G (trivialModule.{u, v, w} k G) V)) :=
    Module.Finite.equiv (extIsoCohomologyDualTensor.{d, u, v, w} k G
      (trivialModule.{u, v, w} k G) V 1)
  exact Module.Finite.equiv
    (((cohomologyFunctor.{d, u, v, w} k G 1).mapIso
      (dualTensorTrivialIso.{u, v, w} V)).toLinearEquiv)

end Main

end Stacks.ContinuousCohomology

end
