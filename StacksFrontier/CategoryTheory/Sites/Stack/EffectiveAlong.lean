module

public import StacksFrontier.CategoryTheory.Sites.Stackification.StageThreeEffectiveDescent
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.DescentUniqueness

/-!
# Descending a descent datum along a morphism into its base

Let `p : 𝒳 ⥤ 𝒮` be a fibred category, `R` a sieve on `U` and `D` a descent datum relative to `R`.
For a morphism `c : V ⟶ U` and an object `a` of the fibre over `V`, *`D` descends to `a` along `c`*
when there are morphisms `ζ f b : D b ⟶ a` lying over `f`, for all `f : Y ⟶ V` and all arrows `b`
of `R` with `f ≫ c = b`, compatible with the gluing isomorphisms of `D`. Indexing the morphisms by
the arrow `b` of `R` rather than by the composite `f ≫ c` makes their type independent of the
factorization, so that descending along `c` and along a morphism equal to `c` are literally the
same data.

For `c = 𝟙 U` this is effectiveness of `D`, and for a general `c` it is effectiveness of the
pullback of `D` along `c`.

## Main definitions

* `CategoryTheory.Functor.SieveDescentDatum.EffectiveAlong`.

## Main results

* `CategoryTheory.Functor.SieveDescentDatum.EffectiveAlong.pullback`: descending along `c` gives
  descending along `ε ≫ c` to the chosen pullback along `ε`.
* `CategoryTheory.Functor.SieveDescentDatum.EffectiveAlong.ofDescends` and
  `CategoryTheory.Functor.SieveDescentDatum.EffectiveAlong.descends`: the comparison with
  effectiveness of the pulled back datum.
* `CategoryTheory.Functor.SieveDescentDatum.EffectiveAlong.exists_iso`: two objects to which `D`
  descends along `c` are isomorphic, compatibly with the descending morphisms, when the morphism
  presheaves are sheaves; and `CategoryTheory.Functor.SieveDescentDatum.EffectiveAlong.iso_ext`:
  such an isomorphism is unique.
-/

@[expose] public section

namespace CategoryTheory.Functor

open Category Limits Opposite

universe v₁ v₂ u₁ u₂

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳] {p : 𝒳 ⥤ 𝒮}
  [p.IsFibered] {U : 𝒮} {R : Sieve U}

attribute [local implicit_reducible] Fiber Fiber.fiberInclusion

namespace SieveDescentDatum

/-- `D` descends to `a` along `c : V ⟶ U`: morphisms `D b ⟶ a` over `f` for every `f : Y ⟶ V` and
every arrow `b` of `R` with `f ≫ c = b`, compatible with the gluing isomorphisms of `D`. -/
structure EffectiveAlong (D : SieveDescentDatum p R) {V : 𝒮} (c : V ⟶ U) (a : p.Fiber V) where
  /-- The descending morphisms. -/
  ζ : ∀ ⦃Y : 𝒮⦄ (f : Y ⟶ V) (b : Y ⟶ U), f ≫ c = b → (hb : R.arrows b) → ((D.obj b hb).1 ⟶ a.1)
  /-- They lie over the given morphisms. -/
  isHomLift : ∀ ⦃Y : 𝒮⦄ (f : Y ⟶ V) (b : Y ⟶ U) (hfb : f ≫ c = b) (hb : R.arrows b),
    p.IsHomLift f (ζ f b hfb hb)
  /-- They are compatible with the gluing isomorphisms. -/
  compat : ∀ ⦃Y Y' Z : 𝒮⦄ (f : Y ⟶ V) (b : Y ⟶ U) (hfb : f ≫ c = b) (hb : R.arrows b)
    (f' : Y' ⟶ V) (b' : Y' ⟶ U) (hfb' : f' ≫ c = b') (hb' : R.arrows b')
    (ε : Z ⟶ Y) (ε' : Z ⟶ Y') (heq : ε ≫ f = ε' ≫ f'),
    Fiber.fiberInclusion.map (D.iso hb hb' ε ε'
        (by rw [← hfb, ← hfb', ← assoc, ← assoc, heq])).hom ≫
      IsPreFibered.pullbackMap (D.obj b' hb').2 ε' ≫ ζ f' b' hfb' hb' =
    IsPreFibered.pullbackMap (D.obj b hb).2 ε ≫ ζ f b hfb hb

namespace EffectiveAlong

variable {D : SieveDescentDatum p R}

/-- Descending along `c` is descending along any morphism equal to `c`. -/
def ofEq {V : 𝒮} {c c' : V ⟶ U} {a : p.Fiber V} (A : D.EffectiveAlong c a) (h : c = c') :
    D.EffectiveAlong c' a where
  ζ _ f b hfb hb := A.ζ f b (by rw [h]; exact hfb) hb
  isHomLift _ f b hfb hb := A.isHomLift f b _ hb
  compat _ _ _ f b hfb hb f' b' hfb' hb' ε ε' heq := A.compat f b _ hb f' b' _ hb' ε ε' heq

/-- Re-indexing along an equality of morphisms leaves the descending morphisms unchanged. -/
@[simp] lemma ofEq_ζ {V : 𝒮} {c c' : V ⟶ U} {a : p.Fiber V} (A : D.EffectiveAlong c a)
    (h : c = c') {Y : 𝒮} (f : Y ⟶ V) (b : Y ⟶ U) (hfb : f ≫ c' = b) (hb : R.arrows b) :
    (A.ofEq h).ζ f b hfb hb = A.ζ f b (by rw [h]; exact hfb) hb := rfl

/-- The factorization of the descending morphism at `f ≫ ε` through the chosen cartesian lift of
`ε`. -/
noncomputable def pullbackζ {V Z : 𝒮} {c : V ⟶ U} {a : p.Fiber V} (A : D.EffectiveAlong c a)
    (ε : Z ⟶ V) {c' : Z ⟶ U} (hc : ε ≫ c = c') {Y : 𝒮} (f : Y ⟶ Z) (b : Y ⟶ U)
    (hfb : f ≫ c' = b) (hb : R.arrows b) : (D.obj b hb).1 ⟶ (pullbackFiber p a ε).1 :=
  haveI := A.isHomLift (f ≫ ε) b (by rw [assoc, hc]; exact hfb) hb
  IsStronglyCartesian.map p ε (IsPreFibered.pullbackMap a.2 ε) (g := f) (f' := f ≫ ε) rfl
    (A.ζ (f ≫ ε) b (by rw [assoc, hc]; exact hfb) hb)

/-- The defining property of `CategoryTheory.Functor.SieveDescentDatum.EffectiveAlong.pullbackζ`:
followed by the chosen cartesian lift of `ε`, it is the descending morphism at `f ≫ ε`. -/
@[reassoc (attr := simp)]
lemma pullbackζ_fac {V Z : 𝒮} {c : V ⟶ U} {a : p.Fiber V} (A : D.EffectiveAlong c a)
    (ε : Z ⟶ V) {c' : Z ⟶ U} (hc : ε ≫ c = c') {Y : 𝒮} (f : Y ⟶ Z) (b : Y ⟶ U)
    (hfb : f ≫ c' = b) (hb : R.arrows b) :
    A.pullbackζ ε hc f b hfb hb ≫ IsPreFibered.pullbackMap a.2 ε =
      A.ζ (f ≫ ε) b (by rw [assoc, hc]; exact hfb) hb := by
  have hb' : (f ≫ ε) ≫ c = b := by rw [assoc, hc]; exact hfb
  have := A.isHomLift (f ≫ ε) b hb' hb
  exact IsStronglyCartesian.fac p ε (IsPreFibered.pullbackMap a.2 ε) (g := f) (f' := f ≫ ε) rfl
    (A.ζ (f ≫ ε) b hb' hb)

/-- The factorized descending morphism lies over `f`. -/
lemma pullbackζ_isHomLift {V Z : 𝒮} {c : V ⟶ U} {a : p.Fiber V} (A : D.EffectiveAlong c a)
    (ε : Z ⟶ V) {c' : Z ⟶ U} (hc : ε ≫ c = c') {Y : 𝒮} (f : Y ⟶ Z) (b : Y ⟶ U)
    (hfb : f ≫ c' = b) (hb : R.arrows b) : p.IsHomLift f (A.pullbackζ ε hc f b hfb hb) := by
  have := A.isHomLift (f ≫ ε) b (by rw [assoc, hc]; exact hfb) hb
  unfold pullbackζ
  infer_instance

/-- **Pulling back along `ε`.** If `D` descends to `a` along `c`, it descends to the chosen
pullback of `a` along `ε : Z ⟶ V` along `ε ≫ c`; the descending morphisms are the factorizations
of those of `a` through the chosen cartesian lift of `ε`. -/
noncomputable def pullback {V Z : 𝒮} {c : V ⟶ U} {a : p.Fiber V} (A : D.EffectiveAlong c a)
    (ε : Z ⟶ V) {c' : Z ⟶ U} (hc : ε ≫ c = c') :
    D.EffectiveAlong c' (pullbackFiber p a ε) where
  ζ _ f b hfb hb := A.pullbackζ ε hc f b hfb hb
  isHomLift _ f b hfb hb := A.pullbackζ_isHomLift ε hc f b hfb hb
  compat _ _ _ f b hfb hb f' b' hfb' hb' ε₁ ε₂ heq := by
    have := A.pullbackζ_isHomLift ε hc f b hfb hb
    have := A.pullbackζ_isHomLift ε hc f' b' hfb' hb'
    have hL : p.IsHomLift (ε₁ ≫ f)
        (Fiber.fiberInclusion.map (D.iso hb hb' ε₁ ε₂
          (by rw [← hfb, ← hfb', ← assoc, ← assoc, heq])).hom ≫
        IsPreFibered.pullbackMap (D.obj b' hb').2 ε₂ ≫ A.pullbackζ ε hc f' b' hfb' hb') := by
      have : p.IsHomLift (𝟙 _ ≫ ε₂ ≫ f')
          (Fiber.fiberInclusion.map (D.iso hb hb' ε₁ ε₂
            (by rw [← hfb, ← hfb', ← assoc, ← assoc, heq])).hom ≫
          IsPreFibered.pullbackMap (D.obj b' hb').2 ε₂ ≫ A.pullbackζ ε hc f' b' hfb' hb') :=
        inferInstance
      exact (congrArg (fun g => p.IsHomLift g _)
        (show 𝟙 _ ≫ ε₂ ≫ f' = ε₁ ≫ f by rw [id_comp, heq])).mp this
    have hR : p.IsHomLift (ε₁ ≫ f)
        (IsPreFibered.pullbackMap (D.obj b hb).2 ε₁ ≫ A.pullbackζ ε hc f b hfb hb) :=
      inferInstance
    refine IsStronglyCartesian.ext p ε (IsPreFibered.pullbackMap a.2 ε) (ε₁ ≫ f) ?_
    simp only [assoc, pullbackζ_fac]
    exact A.compat (f ≫ ε) b _ hb (f' ≫ ε) b' _ hb' ε₁ ε₂ (by rw [← assoc, heq, assoc])

/-- The descending morphisms of the pulled back descent, followed by the chosen cartesian lift
of `ε`, are the descending morphisms of the original one. -/
@[reassoc (attr := simp)]
lemma pullback_ζ_fac {V Z : 𝒮} {c : V ⟶ U} {a : p.Fiber V} (A : D.EffectiveAlong c a)
    (ε : Z ⟶ V) {c' : Z ⟶ U} (hc : ε ≫ c = c') {Y : 𝒮} (f : Y ⟶ Z) (b : Y ⟶ U)
    (hfb : f ≫ c' = b) (hb : R.arrows b) :
    (A.pullback ε hc).ζ f b hfb hb ≫ IsPreFibered.pullbackMap a.2 ε =
      A.ζ (f ≫ ε) b (by rw [assoc, hc]; exact hfb) hb :=
  A.pullbackζ_fac ε hc f b hfb hb

/-- Effectiveness of the pullback of `D` along `c` gives a descent along `c`. -/
noncomputable def ofDescends {V : 𝒮} {c : V ⟶ U} {a : p.Fiber V}
    {ξ : ∀ ⦃Y : 𝒮⦄ (f : Y ⟶ V) (hf : (R.pullback c).arrows f),
      ((D.pullback c).obj f hf).1 ⟶ a.1}
    (h : (D.pullback c).Descends p a ξ) : D.EffectiveAlong c a where
  ζ _ f b hfb hb := eqToHom (by subst hfb; rfl) ≫ ξ f (by rw [Sieve.pullback_apply, hfb]; exact hb)
  isHomLift _ f b hfb hb := by
    subst hfb
    have := h.1 f hb
    simpa using (inferInstance : p.IsHomLift f (ξ f hb))
  compat _ _ _ f b hfb hb f' b' hfb' hb' ε ε' heq := by
    subst hfb hfb'
    simp only [eqToHom_refl, Category.id_comp]
    exact h.2 hb hb' ε ε' heq

/-- A descent along `c` makes the pullback of `D` along `c` descend, for a category fibred in
groupoids. -/
lemma descends (hp : p.IsFiberedInGroupoids) {V : 𝒮} {c : V ⟶ U} {a : p.Fiber V}
    (A : D.EffectiveAlong c a) :
    (D.pullback c).Descends p a (fun _ f hf => A.ζ f (f ≫ c) rfl hf) := by
  refine ⟨fun _ f hf => ?_, fun _ _ _ f hf g hg ε ε' heq => ?_⟩
  · have : p.IsHomLift f (A.ζ f (f ≫ c) rfl hf) := A.isHomLift f (f ≫ c) rfl hf
    have := hp.isStronglyCartesian_homLift f (A.ζ f (f ≫ c) rfl hf)
    exact inferInstance
  · exact A.compat f _ rfl hf g _ rfl hg ε ε' heq

section Uniqueness

/-- Two morphisms of the fibre into a chosen pullback agree if their composites with the chosen
cartesian lift agree. -/
private lemma fiber_hom_ext_pullbackMap {V W : 𝒮} (f : W ⟶ V) (a : p.Fiber V)
    {z : p.Fiber W} (ψ ψ' : z ⟶ pullbackFiber p a f)
    (h : Fiber.fiberInclusion.map ψ ≫ IsPreFibered.pullbackMap a.2 f =
      Fiber.fiberInclusion.map ψ' ≫ IsPreFibered.pullbackMap a.2 f) : ψ = ψ' :=
  fiber_hom_ext_of_cartesian f _ (IsPreFibered.pullbackMap.IsCartesian _ _) _ _ h

variable (hp : p.IsFiberedInGroupoids) {J : GrothendieckTopology 𝒮}
include hp

/-- **Two objects to which `D` descends along `c` are isomorphic, compatibly with the descending
morphisms,** when the morphism presheaves over the source of `c` are sheaves and the pullback of
the sieve along `c` is covering. -/
theorem exists_iso {V : 𝒮} {c : V ⟶ U} (hmor : ∀ (x y : p.Fiber V), IsMorSheaf p J V x y)
    (hRc : R.pullback c ∈ J V) {a a' : p.Fiber V} (A : D.EffectiveAlong c a)
    (A' : D.EffectiveAlong c a') :
    ∃ e : a ≅ a', ∀ ⦃Y : 𝒮⦄ (f : Y ⟶ V) (b : Y ⟶ U) (hfb : f ≫ c = b) (hb : R.arrows b),
      A.ζ f b hfb hb ≫ Fiber.fiberInclusion.map e.hom = A'.ζ f b hfb hb := by
  have hζ := A.descends hp
  have hξ := A'.descends hp
  have hfactor : ∀ ⦃V' W : 𝒮⦄ {f : V' ⟶ V} (hf : (R.pullback c).arrows f) (γ : W ⟶ V')
      {b : W ⟶ V} (hb : γ ≫ f = b) (hb' : (R.pullback c).arrows b),
      descendsIso hζ b hb' = (pullbackFiberCompIso' a f γ b hb).symm ≪≫
        pullbackFiberIso (descendsIso hζ f hf) γ ≪≫ (D.pullback c).isoAlong hf γ hb hb' := by
    intro V' W f hf γ b hb hb'
    have : p.IsCartesian b (A.ζ b (b ≫ c) rfl hb') := hζ.1 b hb'
    refine Iso.ext (fiber_hom_ext_of_cartesian b (A.ζ b (b ≫ c) rfl hb') (hζ.1 b hb') _ _ ?_)
    simp [Iso.trans_hom, Iso.symm_hom, pullbackFiberIso_hom, Functor.map_comp,
      Category.assoc, isoAlong_comp hζ hf γ hb hb', pullbackFiberHom_fac_assoc,
      descendsIso_hom_fac, pullbackFiberCompIso'_inv_fac]
  have hcompat : ∀ ⦃V' W : 𝒮⦄ (f : V' ⟶ V) (hf : (R.pullback c).arrows f) (γ : W ⟶ V')
      (b : W ⟶ V) (hb : γ ≫ f = b) (hb' : (R.pullback c).arrows b),
      (descendsIso hζ b hb' ≪≫ (descendsIso hξ b hb').symm).hom =
        (pullbackFiberCompIso' a f γ b hb).inv ≫
          pullbackFiberHom (descendsIso hζ f hf ≪≫ (descendsIso hξ f hf).symm).hom γ ≫
          (pullbackFiberCompIso' a' f γ b hb).hom := by
    intro V' W f hf γ b hb hb'
    refine fiber_hom_ext_pullbackMap b a' _ _ ?_
    rw [hfactor hf γ hb hb']
    simp [Iso.trans_hom, Iso.symm_hom, pullbackFiberIso_hom, Functor.map_comp,
      Category.assoc, descendsIso_inv_fac, pullbackFiberCompIso'_hom_fac,
      pullbackFiberHom_fac_assoc, isoAlong_comp hξ hf γ hb hb']
  obtain ⟨e, he⟩ := exists_fiberIso_of_locally p hmor hRc
    (fun {_V} f hf => descendsIso hζ f hf ≪≫ (descendsIso hξ f hf).symm) hcompat
  refine ⟨e, fun Y f b hfb hb => ?_⟩
  subst hfb
  have h3 := pullbackFiberHom_fac e.hom f
  rw [he f hb] at h3
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.map_comp, Category.assoc] at h3
  calc A.ζ f (f ≫ c) rfl hb ≫ Fiber.fiberInclusion.map e.hom
      = Fiber.fiberInclusion.map (descendsIso hζ f hb).inv ≫ IsPreFibered.pullbackMap a.2 f ≫
          Fiber.fiberInclusion.map e.hom := by
            rw [← descendsIso_inv_fac hζ f hb, Category.assoc]
    _ = A'.ζ f (f ≫ c) rfl hb := by
        rw [← h3, ← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, Functor.map_id,
          Category.id_comp, descendsIso_inv_fac hξ f hb]

/-- An isomorphism compatible with the descending morphisms is unique. -/
theorem iso_ext {V : 𝒮} {c : V ⟶ U} (hmor : ∀ (x y : p.Fiber V), IsMorSheaf p J V x y)
    (hRc : R.pullback c ∈ J V) {a a' : p.Fiber V} (A : D.EffectiveAlong c a)
    (A' : D.EffectiveAlong c a') (e e' : a ≅ a')
    (he : ∀ ⦃Y : 𝒮⦄ (f : Y ⟶ V) (b : Y ⟶ U) (hfb : f ≫ c = b) (hb : R.arrows b),
      A.ζ f b hfb hb ≫ Fiber.fiberInclusion.map e.hom = A'.ζ f b hfb hb)
    (he' : ∀ ⦃Y : 𝒮⦄ (f : Y ⟶ V) (b : Y ⟶ U) (hfb : f ≫ c = b) (hb : R.arrows b),
      A.ζ f b hfb hb ≫ Fiber.fiberInclusion.map e'.hom = A'.ζ f b hfb hb) :
    e = e' := by
  have hζ := A.descends hp
  refine Iso.ext (eq_of_pullbackFiberHom_locally_eq p (hmor a a') hRc fun Y f hf => ?_)
  refine fiber_hom_ext_pullbackMap f a' _ _ ?_
  rw [pullbackFiberHom_fac, pullbackFiberHom_fac, ← descendsIso_hom_fac hζ f hf]
  simp only [Category.assoc]
  rw [he f (f ≫ c) rfl hf, he' f (f ≫ c) rfl hf]

end Uniqueness

end EffectiveAlong

end SieveDescentDatum

end CategoryTheory.Functor

end
