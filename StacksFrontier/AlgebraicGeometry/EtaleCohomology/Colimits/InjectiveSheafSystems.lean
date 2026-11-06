module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition

/-!
# Embedding a system of abelian sheaves into a system of injective sheaves

Let `(X_i, f_{i'i})` be an inverse system of schemes and `(ℱ_i, φ_{i'i})` a system of abelian
sheaves on it ([Stacks, Tag 0EZL]). [Stacks, Tag 0EXZ] produces a map of systems
`(ℱ_i, φ_{i'i}) ⟶ (𝒢_i, ψ_{i'i})` which is injective at every level and whose levels `𝒢_i` are
injective abelian sheaves. The construction chooses an injective hull `ℱ_i ⟶ 𝒜_i` at every level
and sets `𝒢_i = ∏_{b : k → i} f_{b, *} 𝒜_k`; the component of `ℱ_i ⟶ 𝒢_i` at `b` is adjoint to
`f_b^{-1}ℱ_i ⟶ ℱ_k ⟶ 𝒜_k`, and the transition maps of `𝒢` reindex the product.

The systems of this repository satisfy the cocycle condition only, as in the source, and not the
condition that `φ_{ii}` be the identity. Without it the component of `ℱ_i ⟶ 𝒢_i` at `b = id`
need not be the injection `ℱ_i ⟶ 𝒜_i`. The construction here therefore adds one factor: the
product is over the set `Option (Σ k, k → i)`, the extra index `none` carrying `𝒜_i` itself, on
which the component of `ℱ_i ⟶ 𝒢_i` is the chosen injection. The transition map of `𝒢` sends the
factor `none` at `i'` to the factor `b = (i' → i)` at `i`, so it is again a reindexing of the
product, and the cocycle condition is the associativity of composition in the index together
with the pentagon of the comparison of direct images along composites.

## Main definitions

* `Stacks.EtaleCohomology.InjectiveSheafSystem.system` — the system `(𝒢_i, ψ_{i'i})`.
* `Stacks.EtaleCohomology.InjectiveSheafSystem.ι` — the map `ℱ_i ⟶ 𝒢_i` at every level.

## Main results

* `Stacks.EtaleCohomology.InjectiveSheafSystem.injective` — every `𝒢_i` is injective.
* `Stacks.EtaleCohomology.InjectiveSheafSystem.mono_ι` — every `ℱ_i ⟶ 𝒢_i` is a monomorphism.
* `Stacks.EtaleCohomology.InjectiveSheafSystem.ι_comm` — the maps `ℱ_i ⟶ 𝒢_i` form a map of
  systems.

## References

* [Stacks Project, Tag 0EXZ](https://stacks.math.columbia.edu/tag/0EXZ)
* [Stacks Project, Tag 0EZL](https://stacks.math.columbia.edu/tag/0EZL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.InjectiveSheafSystem

variable {I : Type u} [Preorder I] (D : Iᵒᵖ ⥤ Scheme.{u}) (F : EtaleSheafSystem D Ab.{u + 1})

/-- The index set of the product at the level `i`: the arrows into `i`, and one extra index. -/
abbrev Index (i : Iᵒᵖ) : Type u := Option (Σ k : Iᵒᵖ, k ⟶ i)

/-- The injective hull of the sheaf of the system at the level `k`. -/
abbrev hull (k : Iᵒᵖ) : Sheaf (smallEtaleTopology (D.obj k)) Ab.{u + 1} :=
  Injective.under (F.obj k)

/-- The factor of the product at the level `i` with index `x`. -/
def factor (i : Iᵒᵖ) : Index i → Sheaf (smallEtaleTopology (D.obj i)) Ab.{u + 1}
  | none => hull D F i
  | some ⟨k, c⟩ => (systemPushforward D Ab.{u + 1} c).obj (hull D F k)

/-- The sheaf `𝒢_i`: the product of the factors at the level `i`. -/
abbrev obj (i : Iᵒᵖ) : Sheaf (smallEtaleTopology (D.obj i)) Ab.{u + 1} :=
  ∏ᶜ factor D F i

/-- The reindexing along an arrow `a : i ⟶ j`: the extra index goes to `a`, an arrow `c` into
`i` goes to `c ≫ a`. -/
def reindex {i j : Iᵒᵖ} (a : i ⟶ j) : Index i → Index j
  | none => some ⟨i, a⟩
  | some ⟨k, c⟩ => some ⟨k, c ≫ a⟩

/-- The comparison of the factor at a reindexed index with the direct image of the factor. -/
def factorComp {i j : Iᵒᵖ} (a : i ⟶ j) :
    ∀ x : Index i, factor D F j (reindex a x) ⟶
      (systemPushforward D Ab.{u + 1} a).obj (factor D F i x)
  | none => 𝟙 _
  | some ⟨k, c⟩ => (systemPushforwardComp D Ab.{u + 1} c a).inv.app (hull D F k)

/-- The map `𝒢_j ⟶ f_{a,*}𝒢_i` adjoint to the transition map of `𝒢`. -/
def transitionAdj {i j : Iᵒᵖ} (a : i ⟶ j) :
    obj D F j ⟶ (systemPushforward D Ab.{u + 1} a).obj (obj D F i) :=
  Pi.lift (fun x => Pi.π (factor D F j) (reindex a x) ≫ factorComp D F a x) ≫
    (PreservesProduct.iso (systemPushforward D Ab.{u + 1} a) (factor D F i)).inv

/-- A map into the direct image of a product is determined by its composites with the direct
images of the projections. -/
theorem hom_ext_pushforward_pi {i j : Iᵒᵖ} (a : i ⟶ j)
    {Z : Sheaf (smallEtaleTopology (D.obj j)) Ab.{u + 1}}
    {f g : Z ⟶ (systemPushforward D Ab.{u + 1} a).obj (obj D F i)}
    (h : ∀ x, f ≫ (systemPushforward D Ab.{u + 1} a).map (Pi.π (factor D F i) x) =
      g ≫ (systemPushforward D Ab.{u + 1} a).map (Pi.π (factor D F i) x)) : f = g := by
  rw [← cancel_mono (PreservesProduct.iso (systemPushforward D Ab.{u + 1} a) (factor D F i)).hom]
  refine Pi.hom_ext _ _ fun x => ?_
  simp only [Category.assoc, PreservesProduct.iso_hom, piComparison_comp_π]
  exact h x

/-- The component of `transitionAdj` at the index `x` is the projection onto the factor at
`reindex a x`, followed by `factorComp`. -/
@[reassoc (attr := simp)]
theorem transitionAdj_π {i j : Iᵒᵖ} (a : i ⟶ j) (x : Index i) :
    transitionAdj D F a ≫ (systemPushforward D Ab.{u + 1} a).map (Pi.π (factor D F i) x) =
      Pi.π (factor D F j) (reindex a x) ≫ factorComp D F a x := by
  have h : (PreservesProduct.iso (systemPushforward D Ab.{u + 1} a) (factor D F i)).inv ≫
      (systemPushforward D Ab.{u + 1} a).map (Pi.π (factor D F i) x) =
        Pi.π (fun y => (systemPushforward D Ab.{u + 1} a).obj (factor D F i y)) x := by
    rw [Iso.inv_comp_eq, PreservesProduct.iso_hom, piComparison_comp_π]
  rw [transitionAdj, Category.assoc, h, Pi.lift_comp_π]

/-- The comparison of direct images along a composite transition is the named comparison
`Stacks.EtaleCohomology.smallEtalePushforwardComp'`. -/
theorem systemPushforwardComp_eq' {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k) :
    systemPushforwardComp D Ab.{u + 1} a b =
      smallEtalePushforwardComp' (D.map a) (D.map b) (D.map (a ≫ b)) (D.map_comp a b) Ab.{u + 1} :=
  rfl

private theorem comp_inv_hom_app {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] {P Q : 𝒞 ⥤ 𝒟}
    (e : P ≅ Q) (X : 𝒞) {Y : 𝒟} (f : Y ⟶ Q.obj X) : f ≫ e.inv.app X ≫ e.hom.app X = f := by
  simp

/-- The comparisons `factorComp` at the extra index are compatible with composition of arrows. -/
theorem factorComp_comp_none {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k) :
    factorComp D F b (reindex a none) ≫
        (systemPushforward D Ab.{u + 1} b).map (factorComp D F a none) ≫
        (systemPushforwardComp D Ab.{u + 1} a b).hom.app (factor D F i none) =
      factorComp D F (a ≫ b) none := by
  simp only [factorComp, reindex]
  exact Iso.inv_hom_id_app _ _

/-- The comparisons `factorComp` at the index of an arrow `c : l ⟶ i` are compatible with
composition of arrows. -/
theorem factorComp_comp_some {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k) (l : Iᵒᵖ) (c : l ⟶ i) :
    factorComp D F b (reindex a (some ⟨l, c⟩)) ≫
        (systemPushforward D Ab.{u + 1} b).map (factorComp D F a (some ⟨l, c⟩)) ≫
        (systemPushforwardComp D Ab.{u + 1} a b).hom.app (factor D F i (some ⟨l, c⟩)) =
      factorComp D F (a ≫ b) (some ⟨l, c⟩) := by
  have h := smallEtalePushforwardComp'_inv_app_cocycle (D.map c) (D.map a) (D.map b)
    (D.map (c ≫ a)) (D.map_comp c a) (D.map (a ≫ b)) (D.map_comp a b) (D.map (c ≫ a ≫ b))
    (by rw [← Category.assoc, D.map_comp]) (D.map_comp c (a ≫ b)) Ab.{u + 1} (hull D F l)
  simp only [factorComp, reindex]
  rw [systemPushforwardComp_eq', systemPushforwardComp_eq', systemPushforwardComp_eq',
    systemPushforwardComp_eq']
  have h' := reassoc_of% h
  exact (h' _).trans (comp_inv_hom_app
    (smallEtalePushforwardComp' (D.map a) (D.map b) (D.map (a ≫ b)) (D.map_comp a b) Ab.{u + 1})
    ((smallEtalePushforward (D.map c) Ab.{u + 1}).obj (hull D F l)) _)

/-- The maps `transitionAdj` are compatible with composition of arrows, through the comparison of
direct images along a composite. -/
theorem transitionAdj_comp {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k) :
    transitionAdj D F b ≫ (systemPushforward D Ab.{u + 1} b).map (transitionAdj D F a) ≫
        (systemPushforwardComp D Ab.{u + 1} a b).hom.app (obj D F i) =
      transitionAdj D F (a ≫ b) := by
  refine hom_ext_pushforward_pi D F (a ≫ b) fun x => ?_
  have hn := (systemPushforwardComp D Ab.{u + 1} a b).hom.naturality (Pi.π (factor D F i) x)
  simp only [Functor.comp_map] at hn
  rw [Category.assoc, Category.assoc, ← hn, ← Functor.map_comp_assoc, transitionAdj_π,
    Functor.map_comp_assoc, transitionAdj_π_assoc, transitionAdj_π]
  rcases x with _ | ⟨l, c⟩
  · exact congrArg (Pi.π (factor D F k) _ ≫ ·) (factorComp_comp_none D F a b)
  · exact congrArg (Pi.π (factor D F k) _ ≫ ·) (factorComp_comp_some D F a b l c)

/-- The transition map `ψ_{i'i} : f_{i'i}^{-1}𝒢_i ⟶ 𝒢_{i'}` of the system of injective sheaves. -/
def transition {i j : Iᵒᵖ} (a : i ⟶ j) :
    (systemPullback D Ab.{u + 1} a).obj (obj D F j) ⟶ obj D F i :=
  ((systemAdjunction D Ab.{u + 1} a).homEquiv _ _).symm (transitionAdj D F a)

/-- The transition maps of the system of injective sheaves satisfy the cocycle condition. -/
theorem transition_comp {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k) :
    (systemPullbackComp D Ab.{u + 1} a b).inv.app (obj D F k) ≫
        (systemPullback D Ab.{u + 1} a).map (transition D F b) ≫ transition D F a =
      transition D F (a ≫ b) :=
  (leftAdjointCompIso_inv_homEquiv_symm (systemAdjunction D Ab.{u + 1} b)
    (systemAdjunction D Ab.{u + 1} a) (systemAdjunction D Ab.{u + 1} (a ≫ b))
    (systemPushforwardComp D Ab.{u + 1} a b) _ _).trans
    (congrArg _ (transitionAdj_comp D F a b))

/-- **The system of injective sheaves** `(𝒢_i, ψ_{i'i})` of [Stacks, Tag 0EXZ]. -/
def system : EtaleSheafSystem D Ab.{u + 1} where
  obj := obj D F
  map a := transition D F a
  map_comp a b := transition_comp D F a b

/-- The map `ℱ_i ⟶ 𝒢_i`: the chosen injection on the extra factor, and on the factor of an arrow
`c : k → i` the map adjoint to `f_c^{-1}ℱ_i ⟶ ℱ_k ⟶ 𝒜_k`. -/
def ι (i : Iᵒᵖ) : F.obj i ⟶ obj D F i :=
  Pi.lift fun
    | none => Injective.ι (F.obj i)
    | some ⟨k, c⟩ => ((systemAdjunction D Ab.{u + 1} c).homEquiv _ _)
        (F.map c ≫ Injective.ι (F.obj k))

/-- The component of `ι` on the extra factor is the chosen injection into the injective hull. -/
@[reassoc (attr := simp)]
theorem ι_π_none (i : Iᵒᵖ) : ι D F i ≫ Pi.π (factor D F i) none = Injective.ι (F.obj i) :=
  Pi.lift_comp_π _ _

/-- The component of `ι` on the factor of an arrow `c : k ⟶ i` is the map adjoint to
`F.map c ≫ Injective.ι (F.obj k)`. -/
@[reassoc (attr := simp)]
theorem ι_π_some (i k : Iᵒᵖ) (c : k ⟶ i) :
    ι D F i ≫ Pi.π (factor D F i) (some ⟨k, c⟩) =
      ((systemAdjunction D Ab.{u + 1} c).homEquiv _ _) (F.map c ≫ Injective.ι (F.obj k)) :=
  Pi.lift_comp_π _ _

/-- **The levels of the system are injective sheaves.** -/
instance injective (i : Iᵒᵖ) : Injective (obj D F i) := by
  have : ∀ x, Injective (factor D F i x) := by
    rintro (_ | ⟨k, c⟩)
    · dsimp only [factor]
      infer_instance
    · exact Injective.injective_of_adjoint (systemAdjunction D Ab.{u + 1} c) (hull D F k)
  infer_instance

/-- **The map `ℱ_i ⟶ 𝒢_i` is a monomorphism**, its component on the extra factor being the chosen
injection. -/
instance mono_ι (i : Iᵒᵖ) : Mono (ι D F i) := by
  have : Mono (ι D F i ≫ Pi.π (factor D F i) none) := by
    rw [ι_π_none]
    exact Injective.ι_mono _
  exact mono_of_mono _ (Pi.π (factor D F i) none)

private theorem chain_cancel {𝒞 : Type*} [Category* 𝒞] {o₀ o₁ o₂ o₃ : 𝒞}
    {p₁ : o₀ ⟶ o₁} {p₂ : o₁ ⟶ o₂} {hi : o₂ ⟶ o₃} {y : o₀ ⟶ o₂} {x : o₀ ⟶ o₃} {h : o₃ ⟶ o₂}
    (hπ : p₁ ≫ p₂ = y) (hy : y = x ≫ h) (hhi : h ≫ hi = 𝟙 _) : p₁ ≫ p₂ ≫ hi = x := by
  rw [← Category.assoc, hπ, hy, Category.assoc, hhi, Category.comp_id]

/-- The composite of `ι` with `transitionAdj` is the map adjoint to the transition map of `F`,
followed by the direct image of `ι`. -/
theorem ι_transitionAdj {i j : Iᵒᵖ} (a : i ⟶ j) :
    ι D F j ≫ transitionAdj D F a =
      ((systemAdjunction D Ab.{u + 1} a).homEquiv _ _) (F.map a) ≫
        (systemPushforward D Ab.{u + 1} a).map (ι D F i) := by
  refine hom_ext_pushforward_pi D F a fun x => ?_
  rw [Category.assoc, transitionAdj_π, Category.assoc, ← Functor.map_comp]
  rcases x with _ | ⟨l, c⟩
  · dsimp only [reindex, factorComp]
    rw [ι_π_none]
    exact ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ 𝟙 _) (ι_π_some D F j i a)).trans
      (Category.comp_id _))).trans (Adjunction.homEquiv_naturality_right _ _ _)
  · dsimp only [reindex, factorComp]
    rw [ι_π_some]
    have h := leftAdjointCompIso_inv_homEquiv_symm (systemAdjunction D Ab.{u + 1} a)
      (systemAdjunction D Ab.{u + 1} c) (systemAdjunction D Ab.{u + 1} (c ≫ a))
      (systemPushforwardComp D Ab.{u + 1} c a)
      (((systemAdjunction D Ab.{u + 1} a).homEquiv _ _) (F.map a))
      (((systemAdjunction D Ab.{u + 1} c).homEquiv _ _) (F.map c ≫ Injective.ι (F.obj l)))
    simp only [Equiv.symm_apply_apply] at h
    have hc : (systemPullbackComp D Ab.{u + 1} c a).inv.app (F.obj j) ≫
        (systemPullback D Ab.{u + 1} c).map (F.map a) ≫ F.map c ≫ Injective.ι (F.obj l) =
          F.map (c ≫ a) ≫ Injective.ι (F.obj l) := by
      rw [← F.map_comp c a, Category.assoc, Category.assoc]
    have h' := congrArg ((systemAdjunction D Ab.{u + 1} (c ≫ a)).homEquiv _ _) (hc.symm.trans h)
    rw [Equiv.apply_symm_apply] at h'
    exact chain_cancel (ι_π_some D F j l (c ≫ a)) h' (Iso.hom_inv_id_app _ _)

/-- **The maps `ℱ_i ⟶ 𝒢_i` form a map of systems**: they commute with the transition maps. -/
theorem ι_comm {i j : Iᵒᵖ} (a : i ⟶ j) :
    (systemPullback D Ab.{u + 1} a).map (ι D F j) ≫ transition D F a = F.map a ≫ ι D F i := by
  apply ((systemAdjunction D Ab.{u + 1} a).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, transition, Equiv.apply_symm_apply,
    Adjunction.homEquiv_naturality_right, ι_transitionAdj]

end Stacks.EtaleCohomology.InjectiveSheafSystem

namespace Stacks.EtaleCohomology.EtaleSheafSystem

variable {I : Type u} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}} {F G : EtaleSheafSystem D Ab.{u + 1}}
  (α : ∀ i : Iᵒᵖ, F.obj i ⟶ G.obj i)
  (hα : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
    (systemPullback D Ab.{u + 1} a).map (α j) ≫ G.map a = F.map a ≫ α i)

include hα in
/-- The composite of the transition map of the target with the projection onto the cokernel kills
the inverse image of the map of systems. -/
theorem cokernel_cond {i j : Iᵒᵖ} (a : i ⟶ j) :
    (systemPullback D Ab.{u + 1} a).map (α j) ≫ G.map a ≫ cokernel.π (α i) = 0 := by
  rw [← Category.assoc, hα a, Category.assoc, cokernel.condition, comp_zero]

include hα in
/-- The transition map of the cokernel of a map of systems. -/
def cokernelMap {i j : Iᵒᵖ} (a : i ⟶ j) :
    (systemPullback D Ab.{u + 1} a).obj (cokernel (α j)) ⟶ cokernel (α i) :=
  (PreservesCokernel.iso (systemPullback D Ab.{u + 1} a) (α j)).hom ≫
    cokernel.desc _ (G.map a ≫ cokernel.π (α i)) (cokernel_cond α hα a)

include hα in
/-- The inverse image of the projection onto the cokernel, followed by `cokernelMap`, is the
transition map of the target followed by the projection onto the cokernel. -/
@[reassoc]
theorem map_π_cokernelMap {i j : Iᵒᵖ} (a : i ⟶ j) :
    (systemPullback D Ab.{u + 1} a).map (cokernel.π (α j)) ≫ cokernelMap α hα a =
      G.map a ≫ cokernel.π (α i) := by
  have h : (systemPullback D Ab.{u + 1} a).map (cokernel.π (α j)) ≫
      (PreservesCokernel.iso (systemPullback D Ab.{u + 1} a) (α j)).hom =
        cokernel.π ((systemPullback D Ab.{u + 1} a).map (α j)) := by
    rw [← Iso.eq_comp_inv, PreservesCokernel.iso_inv, π_comp_cokernelComparison]
  rw [cokernelMap, reassoc_of% h, cokernel.π_desc]

include hα in
/-- **The cokernel of a map of systems of sheaves**, levelwise, with the induced transition
maps. The inverse images being exact, they commute with the cokernels, and the cocycle
condition is inherited from the target. -/
def cokernel : EtaleSheafSystem D Ab.{u + 1} where
  obj i := Limits.cokernel (α i)
  map a := cokernelMap α hα a
  map_comp {i j k} a b := by
    rw [← cancel_epi ((systemPullback D Ab.{u + 1} (a ≫ b)).map (cokernel.π (α k)))]
    have hn := (systemPullbackComp D Ab.{u + 1} a b).inv.naturality (cokernel.π (α k))
    simp only [Functor.comp_map] at hn
    rw [map_π_cokernelMap, reassoc_of% hn, ← Functor.map_comp_assoc, map_π_cokernelMap,
      Functor.map_comp_assoc, map_π_cokernelMap, ← G.map_comp a b]
    simp only [Category.assoc]

include hα in
/-- The projection onto the cokernel is a map of systems. -/
theorem cokernel_π_comm {i j : Iᵒᵖ} (a : i ⟶ j) :
    (systemPullback D Ab.{u + 1} a).map (cokernel.π (α j)) ≫ (cokernel α hα).map a =
      G.map a ≫ cokernel.π (α i) :=
  map_π_cokernelMap α hα a

end Stacks.EtaleCohomology.EtaleSheafSystem
