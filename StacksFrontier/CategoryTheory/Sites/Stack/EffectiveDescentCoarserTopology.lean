module

public import StacksFrontier.CategoryTheory.Sites.Stack.EffectiveAlong

/-!
# Effective descent for a finer topology, from local effectivity for a coarser one

Let `J ≤ K` be two Grothendieck topologies on `𝒮` and let `p : 𝒳 ⥤ 𝒮` be fibred in groupoids.
Suppose that `p` is a stack for `J` and that its morphism presheaves are sheaves for `K`. A descent
datum `D` relative to a `K`-covering sieve `R` of `U` is then effective as soon as it becomes
effective `J`-locally: as soon as the sieve of arrows `h : V ⟶ U` along which `D` descends to some
object over `V` is `J`-covering.

The proof is the standard one. The objects to which `D` descends along the arrows of that sieve
are unique up to unique isomorphism, because the morphism presheaves are `K`-sheaves; those
isomorphisms therefore form a descent datum for `J`, which is effective because `p` is a
`J`-stack; and the object it descends to is one to which `D` descends, which is checked on the
common refinement of `R` and the sieve, a `K`-covering sieve.

This is the form in which the Stacks project passes from a stack for the fppf topology to a stack
for the fpqc topology (the proof of Stacks 0GRH): "since `𝒳` is an fppf stack it suffices to
show" the effectivity fppf locally. No tag states the reduction on its own.

## Main definitions

* `CategoryTheory.Functor.SieveDescentDatum.effectiveSieve`: the sieve of arrows along which a
  descent datum descends to some object.
* `CategoryTheory.Functor.SieveDescentDatum.coarseGlueDatum`: the descent datum for `J` formed by
  the objects to which it descends.

## Main results

* `CategoryTheory.Functor.SieveDescentDatum.isEffective_of_effectiveSieve_mem`: the statement
  above.
-/

@[expose] public section

namespace CategoryTheory.Functor

open Category Limits Opposite

universe v₁ v₂ u₁ u₂

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳] {p : 𝒳 ⥤ 𝒮}
  [p.IsFibered] {U : 𝒮} {R : Sieve U}

attribute [local implicit_reducible] Fiber Fiber.fiberInclusion

namespace SieveDescentDatum

/-- The sieve of arrows `h : V ⟶ U` along which `D` descends to some object over `V`. -/
def effectiveSieve (D : SieveDescentDatum p R) : Sieve U where
  arrows {V} h := ∃ a : p.Fiber V, Nonempty (D.EffectiveAlong h a)
  downward_closed {_ _} _ hh g :=
    ⟨pullbackFiber p hh.choose g, ⟨hh.choose_spec.some.pullback g rfl⟩⟩

/-- The descending morphisms of a descent of `D` along `c` at two equal arrows `f = f'` into `V`
agree. Rewriting the arrow argument of `ζ` goes through this, since the factorization proof
`f ≫ c = b` depends on that argument. -/
lemma EffectiveAlong.ζ_congr {D : SieveDescentDatum p R} {V : 𝒮} {c : V ⟶ U} {a : p.Fiber V}
    (A : D.EffectiveAlong c a) {Y : 𝒮} {f f' : Y ⟶ V} (h : f = f') {b : Y ⟶ U}
    (hfb : f ≫ c = b) (hfb' : f' ≫ c = b) (hb : R.arrows b) :
    A.ζ f b hfb hb = A.ζ f' b hfb' hb := by
  subst h; rfl

/-- An arrow along which the pullback of `D` is effective is an arrow of the effective sieve. -/
lemma effectiveSieve_of_isEffective_pullback (D : SieveDescentDatum p R) {V : 𝒮} (h : V ⟶ U)
    (hh : (D.pullback h).IsEffective) : D.effectiveSieve h := by
  obtain ⟨a, ξ, hξ⟩ := hh
  exact ⟨a, ⟨EffectiveAlong.ofDescends hξ⟩⟩

variable (D : SieveDescentDatum p R)

/-- The object to which `D` descends along an arrow of its effective sieve. -/
noncomputable def effObj {V : 𝒮} {h : V ⟶ U} (hh : D.effectiveSieve h) : p.Fiber V :=
  hh.choose

/-- The descent of `D` to `effObj`. -/
noncomputable def effAlong {V : 𝒮} {h : V ⟶ U} (hh : D.effectiveSieve h) :
    D.EffectiveAlong h (D.effObj hh) :=
  hh.choose_spec.some

variable (hp : p.IsFiberedInGroupoids) {K : GrothendieckTopology 𝒮}
  (hmor : ∀ (V : 𝒮) (x y : p.Fiber V), IsMorSheaf p K V x y) (hR : R ∈ K U)

include hp hmor hR in
/-- **Existence of the gluing isomorphism.** For two arrows `h₁`, `h₂` of the effective sieve of
`D` and morphisms `ε₁`, `ε₂` into their sources that agree over `U`, the pullbacks along `ε₁` and
`ε₂` of the objects to which `D` descends are isomorphic, compatibly with the descending
morphisms. The morphism presheaves being `K`-sheaves is what produces the isomorphism, by
`CategoryTheory.Functor.SieveDescentDatum.EffectiveAlong.exists_iso`.
`CategoryTheory.Functor.SieveDescentDatum.glueIso` is the chosen isomorphism and
`CategoryTheory.Functor.SieveDescentDatum.glueIso_spec` its compatibility. -/
theorem exists_glueIso {V W Z : 𝒮} {h₁ : V ⟶ U} (hh₁ : D.effectiveSieve h₁) {h₂ : W ⟶ U}
    (hh₂ : D.effectiveSieve h₂) (ε₁ : Z ⟶ V) (ε₂ : Z ⟶ W) (heq : ε₁ ≫ h₁ = ε₂ ≫ h₂) :
    ∃ e : pullbackFiber p (D.effObj hh₁) ε₁ ≅ pullbackFiber p (D.effObj hh₂) ε₂,
      ∀ ⦃Y : 𝒮⦄ (f : Y ⟶ Z) (b : Y ⟶ U) (hfb : f ≫ (ε₁ ≫ h₁) = b) (hb : R.arrows b),
        ((D.effAlong hh₁).pullback ε₁ rfl).ζ f b hfb hb ≫ Fiber.fiberInclusion.map e.hom =
          ((D.effAlong hh₂).pullback ε₂ heq.symm).ζ f b hfb hb :=
  EffectiveAlong.exists_iso hp (hmor Z) (K.pullback_stable (ε₁ ≫ h₁) hR) _ _

/-- The isomorphism between the pullbacks of the objects to which `D` descends along two arrows
of its effective sieve. -/
noncomputable def glueIso {V W Z : 𝒮} {h₁ : V ⟶ U} (hh₁ : D.effectiveSieve h₁) {h₂ : W ⟶ U}
    (hh₂ : D.effectiveSieve h₂) (ε₁ : Z ⟶ V) (ε₂ : Z ⟶ W) (heq : ε₁ ≫ h₁ = ε₂ ≫ h₂) :
    pullbackFiber p (D.effObj hh₁) ε₁ ≅ pullbackFiber p (D.effObj hh₂) ε₂ :=
  (D.exists_glueIso hp hmor hR hh₁ hh₂ ε₁ ε₂ heq).choose

/-- **The defining property of the gluing isomorphism.** A descending morphism of the object at
`h₁`, pulled back along `ε₁`, becomes the descending morphism of the object at `h₂`, pulled back
along `ε₂`, after composition with `glueIso`. -/
lemma glueIso_spec {V W Z : 𝒮} {h₁ : V ⟶ U} (hh₁ : D.effectiveSieve h₁) {h₂ : W ⟶ U}
    (hh₂ : D.effectiveSieve h₂) (ε₁ : Z ⟶ V) (ε₂ : Z ⟶ W) (heq : ε₁ ≫ h₁ = ε₂ ≫ h₂)
    ⦃Y : 𝒮⦄ (f : Y ⟶ Z) (b : Y ⟶ U) (hfb : f ≫ (ε₁ ≫ h₁) = b) (hb : R.arrows b) :
    ((D.effAlong hh₁).pullback ε₁ rfl).ζ f b hfb hb ≫
        Fiber.fiberInclusion.map (D.glueIso hp hmor hR hh₁ hh₂ ε₁ ε₂ heq).hom =
      ((D.effAlong hh₂).pullback ε₂ heq.symm).ζ f b hfb hb :=
  (D.exists_glueIso hp hmor hR hh₁ hh₂ ε₁ ε₂ heq).choose_spec f b hfb hb

include hp hmor hR in
/-- **The cocycle condition for the gluing isomorphisms.** Over a common source of three arrows of
the effective sieve, the gluing isomorphism from the first to the third is the composite of the
ones from the first to the second and from the second to the third. This is the cocycle field of
`CategoryTheory.Functor.SieveDescentDatum.coarseGlueDatum`; it is the uniqueness half of
`CategoryTheory.Functor.SieveDescentDatum.EffectiveAlong.iso_ext` applied to the two composites
of descending morphisms. -/
lemma glueIso_cocycle {V W X Z : 𝒮} {f : V ⟶ U} (hf : D.effectiveSieve f) {g : W ⟶ U}
    (hg : D.effectiveSieve g) {h : X ⟶ U} (hh : D.effectiveSieve h) (ε₁ : Z ⟶ V) (ε₂ : Z ⟶ W)
    (ε₃ : Z ⟶ X) (h₁₂ : ε₁ ≫ f = ε₂ ≫ g) (h₂₃ : ε₂ ≫ g = ε₃ ≫ h) (h₁₃ : ε₁ ≫ f = ε₃ ≫ h) :
    (D.glueIso hp hmor hR hf hg ε₁ ε₂ h₁₂).hom ≫ (D.glueIso hp hmor hR hg hh ε₂ ε₃ h₂₃).hom =
      (D.glueIso hp hmor hR hf hh ε₁ ε₃ h₁₃).hom := by
  have := EffectiveAlong.iso_ext hp (hmor Z) (K.pullback_stable (ε₁ ≫ f) hR)
    ((D.effAlong hf).pullback ε₁ rfl) ((D.effAlong hh).pullback ε₃ h₁₃.symm)
    (D.glueIso hp hmor hR hf hg ε₁ ε₂ h₁₂ ≪≫ D.glueIso hp hmor hR hg hh ε₂ ε₃ h₂₃)
    (D.glueIso hp hmor hR hf hh ε₁ ε₃ h₁₃) ?_ (D.glueIso_spec hp hmor hR hf hh ε₁ ε₃ h₁₃)
  · exact congrArg Iso.hom this
  · intro Y f' b hfb hb
    rw [Iso.trans_hom, Functor.map_comp, ← Category.assoc,
      D.glueIso_spec hp hmor hR hf hg ε₁ ε₂ h₁₂ f' b hfb hb]
    exact D.glueIso_spec hp hmor hR hg hh ε₂ ε₃ h₂₃ f' b (by rw [← h₁₂]; exact hfb) hb

include hp hmor hR in
/-- **The gluing isomorphisms are compatible with further base change.** Read through the
comparisons of the twofold chosen pullbacks, the gluing isomorphism at `(ε, ε')` pulled back along
`γ : Z' ⟶ Z` is the gluing isomorphism at `(γ ≫ ε, γ ≫ ε')`. This is the `iso_pullback` field of
`CategoryTheory.Functor.SieveDescentDatum.coarseGlueDatum`. -/
lemma glueIso_pullback {V W Z Z' : 𝒮} {f : V ⟶ U} (hf : D.effectiveSieve f) {g : W ⟶ U}
    (hg : D.effectiveSieve g) (ε : Z ⟶ V) (ε' : Z ⟶ W) (heq : ε ≫ f = ε' ≫ g) (γ : Z' ⟶ Z) :
    (pullbackFiberCompIso (D.effObj hf) ε γ).inv ≫
        (pullbackFiberIso (D.glueIso hp hmor hR hf hg ε ε' heq) γ).hom ≫
        (pullbackFiberCompIso (D.effObj hg) ε' γ).hom =
      (D.glueIso hp hmor hR hf hg (γ ≫ ε) (γ ≫ ε')
        (by rw [Category.assoc, Category.assoc, heq])).hom := by
  let L : pullbackFiber p (D.effObj hf) (γ ≫ ε) ≅ pullbackFiber p (D.effObj hg) (γ ≫ ε') :=
    (pullbackFiberCompIso (D.effObj hf) ε γ).symm ≪≫
      pullbackFiberIso (D.glueIso hp hmor hR hf hg ε ε' heq) γ ≪≫
      pullbackFiberCompIso (D.effObj hg) ε' γ
  have hL : L = D.glueIso hp hmor hR hf hg (γ ≫ ε) (γ ≫ ε')
      (by rw [Category.assoc, Category.assoc, heq]) := by
    refine EffectiveAlong.iso_ext hp (hmor Z') (K.pullback_stable ((γ ≫ ε) ≫ f) hR)
      ((D.effAlong hf).pullback (γ ≫ ε) rfl) ((D.effAlong hg).pullback (γ ≫ ε') _) L _ ?_
      (D.glueIso_spec hp hmor hR hf hg (γ ≫ ε) (γ ≫ ε') _)
    intro Y f'' b hfb hb
    have h₁ := ((D.effAlong hf).pullback (γ ≫ ε) rfl).isHomLift f'' b hfb hb
    have h₂ := ((D.effAlong hg).pullback (γ ≫ ε')
      (by rw [Category.assoc, Category.assoc, heq])).isHomLift f'' b hfb hb
    refine IsStronglyCartesian.ext p (γ ≫ ε')
      (IsPreFibered.pullbackMap (D.effObj hg).2 (γ ≫ ε')) f'' ?_
    -- the factorization through the threefold pullback
    have hmid : ((D.effAlong hf).pullback (γ ≫ ε) rfl).ζ f'' b hfb hb ≫
        Fiber.fiberInclusion.map (pullbackFiberCompIso' (D.effObj hf) ε γ (γ ≫ ε) rfl).inv ≫
          IsPreFibered.pullbackMap (pullbackFiber p (D.effObj hf) ε).2 γ =
        ((D.effAlong hf).pullback ε rfl).ζ (f'' ≫ γ) b
          (by simpa [Category.assoc] using hfb) hb := by
      have h₃ := ((D.effAlong hf).pullback ε rfl).isHomLift (f'' ≫ γ) b
        (by simpa [Category.assoc] using hfb) hb
      refine IsStronglyCartesian.ext p ε (IsPreFibered.pullbackMap (D.effObj hf).2 ε)
        (f'' ≫ γ) ?_
      simp only [Category.assoc, pullbackFiberCompIso'_inv_fac, EffectiveAlong.pullback_ζ_fac]
    simp only [L, Iso.trans_hom, Iso.symm_hom, Functor.map_comp, Category.assoc,
      pullbackFiberCompIso, pullbackFiberCompIso'_hom_fac, pullbackFiberIso_hom,
      pullbackFiberHom_fac_assoc]
    rw [← Category.assoc (Fiber.fiberInclusion.map (pullbackFiberCompIso' (D.effObj hf) ε γ
      (γ ≫ ε) rfl).inv), ← Category.assoc, hmid,
      ← Category.assoc, D.glueIso_spec hp hmor hR hf hg ε ε' heq (f'' ≫ γ) b _ hb,
      EffectiveAlong.pullback_ζ_fac, EffectiveAlong.pullback_ζ_fac]
    exact (D.effAlong hg).ζ_congr (Category.assoc _ _ _) _ _ hb
  rw [← hL]
  rfl

/-- **The descent datum for the coarser topology formed by the objects to which `D` descends**,
relative to the effective sieve of `D`. -/
noncomputable def coarseGlueDatum : SieveDescentDatum p D.effectiveSieve where
  obj _ _ hh := D.effObj hh
  iso _ _ _ _ hf _ hg ε ε' heq := D.glueIso hp hmor hR hf hg ε ε' heq
  cocycle _ _ _ _ _ hf _ hg _ hh ε₁ ε₂ ε₃ h₁₂ h₂₃ h₁₃ :=
    D.glueIso_cocycle hp hmor hR hf hg hh ε₁ ε₂ ε₃ h₁₂ h₂₃ h₁₃
  iso_pullback _ _ _ _ _ hf _ hg ε ε' heq γ := D.glueIso_pullback hp hmor hR hf hg ε ε' heq γ

include hp hmor hR in
/-- **Effective descent for a finer topology, from local effectivity for a coarser one.** Let
`J ≤ K`, let `p` be fibred in groupoids, a stack for `J` with morphism presheaves sheaves for `K`.
A descent datum relative to a `K`-covering sieve whose effective sieve is `J`-covering is
effective. -/
theorem isEffective_of_effectiveSieve_mem {J : GrothendieckTopology 𝒮} (hJK : J ≤ K)
    (hJ : HasEffectiveDescent p J) (hE : D.effectiveSieve ∈ J U) : D.IsEffective := by
  obtain ⟨x, ξ₀, hξcart₀, hξcompat₀⟩ := hJ _ hE (D.coarseGlueDatum hp hmor hR)
  let ξ : ∀ ⦃V : 𝒮⦄ (f : V ⟶ U) (hf : D.effectiveSieve f), (D.effObj hf).1 ⟶ x.1 := ξ₀
  have hξcart : ∀ ⦃V : 𝒮⦄ (f : V ⟶ U) (hf : D.effectiveSieve f), p.IsHomLift f (ξ f hf) :=
    fun V f hf => (hξcart₀ f hf).toIsHomLift
  have hξcompat : ∀ ⦃V W Z : 𝒮⦄ ⦃f : V ⟶ U⦄ (hf : D.effectiveSieve f) ⦃g : W ⟶ U⦄
      (hg : D.effectiveSieve g) (ε : Z ⟶ V) (ε' : Z ⟶ W) (heq : ε ≫ f = ε' ≫ g),
      Fiber.fiberInclusion.map (D.glueIso hp hmor hR hf hg ε ε' heq).hom ≫
          IsPreFibered.pullbackMap (D.effObj hg).2 ε' ≫ ξ g hg =
        IsPreFibered.pullbackMap (D.effObj hf).2 ε ≫ ξ f hf :=
    fun _ _ _ _ hf _ hg ε ε' heq => hξcompat₀ hf hg ε ε' heq
  refine D.isEffective_of_restrict hmor (T := R ⊓ D.effectiveSieve) inf_le_left
    (K.intersection_covering hR (hJK _ hE)) ?_
  let ζx : ∀ ⦃V : 𝒮⦄ (f : V ⟶ U) (hf : (R ⊓ D.effectiveSieve).arrows f),
      ((D.restrict (inf_le_left : R ⊓ D.effectiveSieve ≤ R)).obj f hf).1 ⟶ x.1 :=
    fun V f hf => (D.effAlong ((Sieve.inter_apply f).mp hf).2).ζ (𝟙 V) f (Category.id_comp f)
      ((Sieve.inter_apply f).mp hf).1 ≫ ξ f ((Sieve.inter_apply f).mp hf).2
  have hlift : ∀ ⦃V : 𝒮⦄ (f : V ⟶ U) (hf : (R ⊓ D.effectiveSieve).arrows f),
      p.IsHomLift f (ζx f hf) := by
    intro V f hf
    have := (D.effAlong ((Sieve.inter_apply f).mp hf).2).isHomLift (𝟙 V) f (Category.id_comp f)
      ((Sieve.inter_apply f).mp hf).1
    have := hξcart f ((Sieve.inter_apply f).mp hf).2
    have : p.IsHomLift (𝟙 V ≫ f) (ζx f hf) := by dsimp only [ζx]; infer_instance
    exact (congrArg (fun g => p.IsHomLift g (ζx f hf)) (Category.id_comp f)).mp this
  refine ⟨x, ζx, fun V f hf => ?_, fun V W Z f hf g hg ε ε' heq => ?_⟩
  · have := hlift f hf
    have := hp.isStronglyCartesian_homLift f (ζx f hf)
    exact inferInstance
  · obtain ⟨hf₁, hf₂⟩ := (Sieve.inter_apply f).mp hf
    obtain ⟨hg₁, hg₂⟩ := (Sieve.inter_apply g).mp hg
    have hc : R.arrows (ε ≫ f) := R.downward_closed hf₁ ε
    have e₁ : (𝟙 Z ≫ ε) ≫ f = ε ≫ f := by rw [Category.id_comp]
    have e₂ : (𝟙 Z ≫ ε') ≫ g = ε ≫ f := by rw [Category.id_comp, heq]
    have hspec := D.glueIso_spec hp hmor hR hf₂ hg₂ ε ε' heq (𝟙 Z) (ε ≫ f)
      (Category.id_comp _) hc
    have hξc := hξcompat hf₂ hg₂ ε ε' heq
    have hstar : (D.effAlong hf₂).ζ (𝟙 Z ≫ ε) (ε ≫ f) e₁ hc ≫ ξ f hf₂ =
        (D.effAlong hg₂).ζ (𝟙 Z ≫ ε') (ε ≫ f) e₂ hc ≫ ξ g hg₂ := by
      calc (D.effAlong hf₂).ζ (𝟙 Z ≫ ε) (ε ≫ f) e₁ hc ≫ ξ f hf₂
          = (((D.effAlong hf₂).pullback ε rfl).ζ (𝟙 Z) (ε ≫ f) (Category.id_comp _) hc ≫
              IsPreFibered.pullbackMap (D.effObj hf₂).2 ε) ≫ ξ f hf₂ := by
            rw [EffectiveAlong.pullback_ζ_fac]
        _ = ((D.effAlong hf₂).pullback ε rfl).ζ (𝟙 Z) (ε ≫ f) (Category.id_comp _) hc ≫
              Fiber.fiberInclusion.map (D.glueIso hp hmor hR hf₂ hg₂ ε ε' heq).hom ≫
              IsPreFibered.pullbackMap (D.effObj hg₂).2 ε' ≫ ξ g hg₂ := by
            rw [Category.assoc]
            exact congrArg (_ ≫ ·) hξc.symm
        _ = ((D.effAlong hg₂).pullback ε' heq.symm).ζ (𝟙 Z) (ε ≫ f) (Category.id_comp _) hc ≫
              IsPreFibered.pullbackMap (D.effObj hg₂).2 ε' ≫ ξ g hg₂ := by
            rw [← Category.assoc, hspec]
        _ = (D.effAlong hg₂).ζ (𝟙 Z ≫ ε') (ε ≫ f) e₂ hc ≫ ξ g hg₂ := by
            rw [← Category.assoc, EffectiveAlong.pullback_ζ_fac]
    have Ef := (D.effAlong hf₂).compat (𝟙 V) f (Category.id_comp f) hf₁ (𝟙 Z ≫ ε) (ε ≫ f)
      e₁ hc ε (𝟙 Z) (by simp)
    have Eg := (D.effAlong hg₂).compat (𝟙 W) g (Category.id_comp g) hg₁ (𝟙 Z ≫ ε') (ε ≫ f)
      e₂ hc ε' (𝟙 Z) (by simp)
    have hcoc := D.cocycle hf₁ hg₁ hc ε ε' (𝟙 Z) heq (by rw [Category.id_comp, heq])
      (by rw [Category.id_comp])
    have hcoc' := congrArg (Fiber.fiberInclusion.map ·) hcoc
    simp only [Functor.map_comp] at hcoc'
    change Fiber.fiberInclusion.map (D.iso hf₁ hg₁ ε ε' heq).hom ≫
        IsPreFibered.pullbackMap (D.obj g hg₁).2 ε' ≫
          ((D.effAlong hg₂).ζ (𝟙 W) g (Category.id_comp g) hg₁ ≫ ξ g hg₂) =
      IsPreFibered.pullbackMap (D.obj f hf₁).2 ε ≫
        ((D.effAlong hf₂).ζ (𝟙 V) f (Category.id_comp f) hf₁ ≫ ξ f hf₂)
    rw [← Category.assoc (IsPreFibered.pullbackMap (D.obj g hg₁).2 ε'), ← Eg,
      ← Category.assoc (IsPreFibered.pullbackMap (D.obj f hf₁).2 ε), ← Ef]
    simp only [Category.assoc]
    rw [hstar, ← Category.assoc (Fiber.fiberInclusion.map (D.iso hf₁ hg₁ ε ε' heq).hom),
      hcoc']

include hp hmor hR in
/-- **Descending the glued datum is descending the datum.** Every arrow of `R` being an arrow of the
effective sieve, an object to which the datum glued from the objects `D` descends to descends
along `c` is one to which `D` itself descends along `c`. -/
theorem nonempty_effectiveAlong_of_coarseGlueDatum (hRE : R ≤ D.effectiveSieve) {V : 𝒮}
    {c : V ⟶ U} {x : p.Fiber V} (A : (D.coarseGlueDatum hp hmor hR).EffectiveAlong c x) :
    Nonempty (D.EffectiveAlong c x) := by
  let ξ : ∀ ⦃Y : 𝒮⦄ (f : Y ⟶ V) (b : Y ⟶ U) (hfb : f ≫ c = b) (hb : D.effectiveSieve b),
      (D.effObj hb).1 ⟶ x.1 := fun Y f b hfb hb => A.ζ f b hfb hb
  have hξcompat : ∀ ⦃Y Y' Z : 𝒮⦄ (f : Y ⟶ V) (b : Y ⟶ U) (hfb : f ≫ c = b)
      (hb : D.effectiveSieve b) (f' : Y' ⟶ V) (b' : Y' ⟶ U) (hfb' : f' ≫ c = b')
      (hb' : D.effectiveSieve b') (ε : Z ⟶ Y) (ε' : Z ⟶ Y') (heq : ε ≫ f = ε' ≫ f'),
      Fiber.fiberInclusion.map (D.glueIso hp hmor hR hb hb' ε ε'
          (by rw [← hfb, ← hfb', ← assoc, ← assoc, heq])).hom ≫
        IsPreFibered.pullbackMap (D.effObj hb').2 ε' ≫ ξ f' b' hfb' hb' =
      IsPreFibered.pullbackMap (D.effObj hb).2 ε ≫ ξ f b hfb hb :=
    fun _ _ _ f b hfb hb f' b' hfb' hb' ε ε' heq => A.compat f b hfb hb f' b' hfb' hb' ε ε' heq
  refine ⟨{
    ζ := fun Y f b hfb hb => (D.effAlong (hRE _ hb)).ζ (𝟙 Y) b (Category.id_comp b) hb ≫
      ξ f b hfb (hRE _ hb)
    isHomLift := fun Y f b hfb hb => by
      have := (D.effAlong (hRE _ hb)).isHomLift (𝟙 Y) b (Category.id_comp b) hb
      have : p.IsHomLift f (ξ f b hfb (hRE _ hb)) := A.isHomLift f b hfb (hRE _ hb)
      have : p.IsHomLift (𝟙 Y ≫ f) ((D.effAlong (hRE _ hb)).ζ (𝟙 Y) b (Category.id_comp b) hb ≫
          ξ f b hfb (hRE _ hb)) := inferInstance
      exact (congrArg (fun g => p.IsHomLift g _) (Category.id_comp f)).mp this
    compat := fun Y Y' Z f b hfb hb f' b' hfb' hb' ε ε' heq => ?_ }⟩
  have heqb : ε ≫ b = ε' ≫ b' := by rw [← hfb, ← hfb', ← assoc, ← assoc, heq]
  have hf₂ := hRE _ hb
  have hg₂ := hRE _ hb'
  have hc : R.arrows (ε ≫ b) := R.downward_closed hb ε
  have e₁ : (𝟙 Z ≫ ε) ≫ b = ε ≫ b := by rw [Category.id_comp]
  have e₂ : (𝟙 Z ≫ ε') ≫ b' = ε ≫ b := by rw [Category.id_comp, heqb]
  have hspec := D.glueIso_spec hp hmor hR hf₂ hg₂ ε ε' heqb (𝟙 Z) (ε ≫ b)
    (Category.id_comp _) hc
  have hξc := hξcompat f b hfb hf₂ f' b' hfb' hg₂ ε ε' heq
  have hstar : (D.effAlong hf₂).ζ (𝟙 Z ≫ ε) (ε ≫ b) e₁ hc ≫ ξ f b hfb hf₂ =
      (D.effAlong hg₂).ζ (𝟙 Z ≫ ε') (ε ≫ b) e₂ hc ≫ ξ f' b' hfb' hg₂ := by
    calc (D.effAlong hf₂).ζ (𝟙 Z ≫ ε) (ε ≫ b) e₁ hc ≫ ξ f b hfb hf₂
        = (((D.effAlong hf₂).pullback ε rfl).ζ (𝟙 Z) (ε ≫ b) (Category.id_comp _) hc ≫
            IsPreFibered.pullbackMap (D.effObj hf₂).2 ε) ≫ ξ f b hfb hf₂ := by
          rw [EffectiveAlong.pullback_ζ_fac]
      _ = ((D.effAlong hf₂).pullback ε rfl).ζ (𝟙 Z) (ε ≫ b) (Category.id_comp _) hc ≫
            Fiber.fiberInclusion.map (D.glueIso hp hmor hR hf₂ hg₂ ε ε' heqb).hom ≫
            IsPreFibered.pullbackMap (D.effObj hg₂).2 ε' ≫ ξ f' b' hfb' hg₂ := by
          rw [Category.assoc]
          exact congrArg (_ ≫ ·) hξc.symm
      _ = ((D.effAlong hg₂).pullback ε' heqb.symm).ζ (𝟙 Z) (ε ≫ b) (Category.id_comp _) hc ≫
            IsPreFibered.pullbackMap (D.effObj hg₂).2 ε' ≫ ξ f' b' hfb' hg₂ := by
          rw [← Category.assoc, hspec]
      _ = (D.effAlong hg₂).ζ (𝟙 Z ≫ ε') (ε ≫ b) e₂ hc ≫ ξ f' b' hfb' hg₂ := by
          rw [← Category.assoc, EffectiveAlong.pullback_ζ_fac]
  have Ef := (D.effAlong hf₂).compat (𝟙 Y) b (Category.id_comp b) hb (𝟙 Z ≫ ε) (ε ≫ b)
    e₁ hc ε (𝟙 Z) (by simp)
  have Eg := (D.effAlong hg₂).compat (𝟙 Y') b' (Category.id_comp b') hb' (𝟙 Z ≫ ε') (ε ≫ b)
    e₂ hc ε' (𝟙 Z) (by simp)
  have hcoc := D.cocycle hb hb' hc ε ε' (𝟙 Z) heqb (by rw [Category.id_comp, heqb])
    (by rw [Category.id_comp])
  have hcoc' := congrArg (Fiber.fiberInclusion.map ·) hcoc
  simp only [Functor.map_comp] at hcoc'
  change Fiber.fiberInclusion.map (D.iso hb hb' ε ε' heqb).hom ≫
      IsPreFibered.pullbackMap (D.obj b' hb').2 ε' ≫
        ((D.effAlong hg₂).ζ (𝟙 Y') b' (Category.id_comp b') hb' ≫ ξ f' b' hfb' hg₂) =
    IsPreFibered.pullbackMap (D.obj b hb).2 ε ≫
      ((D.effAlong hf₂).ζ (𝟙 Y) b (Category.id_comp b) hb ≫ ξ f b hfb hf₂)
  rw [← Category.assoc (IsPreFibered.pullbackMap (D.obj b' hb').2 ε'), ← Eg,
    ← Category.assoc (IsPreFibered.pullbackMap (D.obj b hb).2 ε), ← Ef]
  simp only [Category.assoc]
  rw [hstar, ← Category.assoc (Fiber.fiberInclusion.map (D.iso hb hb' ε ε' heqb).hom), hcoc']

/-- Every arrow of `R` is an arrow of the effective sieve of `D`, when `p` has effective descent for
a topology in which the maximal sieve covers. -/
theorem le_effectiveSieve {J : GrothendieckTopology 𝒮} (hJ : HasEffectiveDescent p J) :
    R ≤ D.effectiveSieve := by
  intro V b hb
  refine D.effectiveSieve_of_isEffective_pullback b (hJ _ ?_ (D.pullback b))
  rw [Sieve.pullback_eq_top_of_mem _ hb]
  exact J.top_mem V

end SieveDescentDatum

end CategoryTheory.Functor

end
