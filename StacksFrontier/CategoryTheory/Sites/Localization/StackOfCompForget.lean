module

public import StacksFrontier.CategoryTheory.Sites.Localization.StacksOverSlice
public import StacksFrontier.CategoryTheory.Sites.Stackification.DescentPairOfMorSheaf
public import StacksFrontier.CategoryTheory.Sites.Stackification.StageTwoMorSheaf
public import StacksFrontier.CategoryTheory.Sites.Stack.DescentTransferHom
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.MorGluing

/-!
# Construction B of Stacks 04WV for an arbitrary site

Let `(𝒞, J)` be a site and `U` an object of `𝒞` whose representable presheaf `h_U` is a sheaf, and
write `j_U = Over.forget U : 𝒞/U ⥤ 𝒞`. Construction B of Stacks 04WV says that a functor
`p : 𝒮 ⥤ 𝒞/U` whose composite `p ⋙ j_U` is a stack over `(𝒞, J)` is a stack over
`(𝒞/U, J.over U)`. `StacksFrontier/CategoryTheory/Sites/Localization/StacksOverSlice.lean` proves
this through the pushforward of Stacks 04WC, at the cost of the hypothesis `[HasPullbacks 𝒞]`,
which Stacks does not make (a site of the Stacks project need not have all fibre products). This
file proves it for an arbitrary site, by checking the three conditions of Stacks 026F directly,
and deduces the bijection on objects between the two 2-categories of Stacks 04WV.

The point is that a `J.over U`-covering sieve of `A : 𝒞/U` is `(Sieve.overEquiv A).symm R'` for a
`J`-covering sieve `R'` of `A.left`, every object of `𝒞` over `A.left` being automatically over
`U`, so that descent data on the two sides correspond.

## Main results

* `CategoryTheory.Functor.exists_hom_of_isMorSheaf`: in a fibred category whose presheaves
  `Mor(x, y)` are sheaves, morphisms glue along covering sieves.
* `CategoryTheory.Over.isMorSheaf_of_isMorSheaf_comp_forget`: condition (2) of Stacks 026F passes
  from `p ⋙ j_U` to `p`.
* `CategoryTheory.Over.sliceDatum` and `CategoryTheory.Over.isEffective_of_isEffective_sliceDatum`:
  a descent datum for `p` read as one for `p ⋙ j_U`, and effectivity transported back; this is the
  only place where the sheaf hypothesis on `h_U` is used.
* `CategoryTheory.Over.isStack_of_isStack_comp_forget`: **Construction B of Stacks 04WV**.
* `CategoryTheory.Over.isStack_iff_isStack_comp_forget`: Constructions A and B together.
* `CategoryTheory.Over.basedStackEquivStackPair`: **Constructions A and B are mutually inverse on
  objects** of the two 2-categories of Stacks 04WV.

## Implementation notes

The chosen pullbacks of `p` and of `p ⋙ j_U` are never compared directly: the gluing isomorphisms
of `CategoryTheory.Over.sliceDatum` are defined through the transfer of morphisms along the gluing
isomorphisms of the given datum (`CategoryTheory.Functor.SieveDescentDatum.transferHom`), whose
three laws give the cocycle condition and the compatibility with base change.
-/

@[expose] public noncomputable section

namespace CategoryTheory

open Limits Opposite

universe v₁ v₂ u₁ u₂

-- `Functor.Fiber` and its inclusion are Mathlib definitions that are not implicit-reducible;
-- the composites below cross from a fibre into the total category through them.
attribute [local implicit_reducible] Functor.Fiber Functor.Fiber.fiberInclusion

namespace Functor

section Glue

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {r : 𝒳 ⥤ 𝒮} [r.IsFibered] {J : GrothendieckTopology 𝒮}

/-- **Morphisms of a fibred category with `Mor`-sheaves glue along covering sieves.** If the
presheaves `Mor(x, y)` of Stacks 02ZB are sheaves, a family of morphisms `F Φ : W ⟶ B` indexed by
the morphisms `Φ : W ⟶ A` lying over a covering sieve of `r A`, each lying over `r Φ ≫ u` and
compatible with precomposition, is the family of composites `Φ ≫ G` of a single morphism
`G : A ⟶ B` over `u`. This is the converse of
`CategoryTheory.Functor.isMorSheaf_of_locallyEqual_of_amalgamation`'s gluing hypothesis. -/
theorem exists_hom_of_isMorSheaf (hmor : ∀ (U : 𝒮) (x y : r.Fiber U), IsMorSheaf r J U x y)
    {A B : 𝒳} (u : r.obj A ⟶ r.obj B) {S : Sieve (r.obj A)} (hS : S ∈ J (r.obj A))
    (F : ∀ {W : 𝒳} (Φ : W ⟶ A), S.arrows (r.map Φ) → (W ⟶ B))
    (hFbase : ∀ {W : 𝒳} (Φ : W ⟶ A) (hΦ : S.arrows (r.map Φ)), r.map (F Φ hΦ) = r.map Φ ≫ u)
    (hFcomp : ∀ {W W' : 𝒳} (Ψ : W' ⟶ W) (Φ : W ⟶ A) (hΦ : S.arrows (r.map Φ))
      (hΨΦ : S.arrows (r.map (Ψ ≫ Φ))), F (Ψ ≫ Φ) hΨΦ = Ψ ≫ F Φ hΦ) :
    ∃ G : A ⟶ B, r.map G = u ∧
      ∀ {W : 𝒳} (Φ : W ⟶ A) (hΦ : S.arrows (r.map Φ)), Φ ≫ G = F Φ hΦ := by
  have hFcongr : ∀ {W : 𝒳} {Φ Φ' : W ⟶ A} (_ : Φ = Φ') (hΦ : S.arrows (r.map Φ))
      (hΦ' : S.arrows (r.map Φ')), F Φ hΦ = F Φ' hΦ' := by
    intro W Φ Φ' e _ _
    subst e
    rfl
  have hmem : ∀ {V : 𝒮} {W : 𝒳} (g : V ⟶ r.obj A) (Φ : W ⟶ A), r.IsHomLift g Φ →
      S.arrows g → S.arrows (r.map Φ) := by
    intro V W g Φ hΦ hg
    rw [IsHomLift.fac' r g Φ]
    simpa using S.downward_closed hg (eqToHom (IsHomLift.domain_eq r g Φ))
  let a : r.Fiber (r.obj A) := ⟨A, rfl⟩
  let b₀ : r.Fiber (r.obj B) := ⟨B, rfl⟩
  let b : r.Fiber (r.obj A) := pullbackFiber r b₀ u
  let πb : b.1 ⟶ B := IsPreFibered.pullbackMap b₀.2 u
  have hπb : r.IsStronglyCartesian u πb := isStronglyCartesian_pullbackMap_of_fiber b₀ u
  -- the value of the family at the chosen pullback morphism along a member `g` of `S`
  have hΦg : ∀ ⦃V : 𝒮⦄ (g : V ⟶ r.obj A), r.IsHomLift g (IsPreFibered.pullbackMap a.2 g) :=
    fun V g => isHomLift_pullbackMap_of_fiber a g
  have hFg : ∀ ⦃V : 𝒮⦄ (g : V ⟶ r.obj A) (hg : S.arrows g),
      r.IsHomLift (g ≫ u)
        (F (IsPreFibered.pullbackMap a.2 g)
          (hmem g (IsPreFibered.pullbackMap a.2 g) (hΦg g) hg)) := by
    intro V g hg
    have := hΦg g
    refine IsHomLift.of_fac' r (g ≫ u) _
      (IsHomLift.domain_eq r g (IsPreFibered.pullbackMap a.2 g)) rfl ?_
    rw [hFbase, IsHomLift.fac' r g (IsPreFibered.pullbackMap a.2 g)]
    simp
  let σ : ∀ ⦃V : 𝒮⦄ (g : V ⟶ r.obj A) (hg : S.arrows g), (pullbackFiber r a g).1 ⟶ b.1 :=
    fun V g hg =>
      have := hFg g hg
      IsStronglyCartesian.map r u πb (g := g) (f' := g ≫ u) rfl
        (F (IsPreFibered.pullbackMap a.2 g) (hmem g (IsPreFibered.pullbackMap a.2 g) (hΦg g) hg))
  have hσlift : ∀ ⦃V : 𝒮⦄ (g : V ⟶ r.obj A) (hg : S.arrows g), r.IsHomLift g (σ g hg) := by
    intro V g hg
    have := hFg g hg
    exact IsStronglyCartesian.map_isHomLift r u πb (g := g) (f' := g ≫ u) rfl _
  have hσfac : ∀ ⦃V : 𝒮⦄ (g : V ⟶ r.obj A) (hg : S.arrows g),
      σ g hg ≫ πb =
        F (IsPreFibered.pullbackMap a.2 g)
          (hmem g (IsPreFibered.pullbackMap a.2 g) (hΦg g) hg) := by
    intro V g hg
    have := hFg g hg
    exact IsStronglyCartesian.fac r u πb (g := g) (f' := g ≫ u) rfl _
  let θ : ∀ ⦃V : 𝒮⦄ (g : V ⟶ r.obj A), S.arrows g →
      (pullbackFiber r a g ⟶ pullbackFiber r b g) :=
    fun V g hg => (pullbackFiberHomEquiv (pullbackFiber r a g) b g).symm ⟨σ g hg, hσlift g hg⟩
  have hθfac : ∀ ⦃V : 𝒮⦄ (g : V ⟶ r.obj A) (hg : S.arrows g),
      Fiber.fiberInclusion.map (θ g hg) ≫ IsPreFibered.pullbackMap b.2 g = σ g hg :=
    fun V g hg => pullbackFiberHomEquiv_symm_fac _ _ _ _
  obtain ⟨m, hm⟩ := exists_fiberHom_of_locally r (hmor _ a b) hS θ (by
    intro V W f hf γ c hc hc'
    subst hc
    rw [pullbackFiberCompIso'_rfl, pullbackFiberCompIso'_rfl]
    apply (pullbackFiberHomEquiv (pullbackFiber r a (γ ≫ f)) b (γ ≫ f)).injective
    refine Subtype.ext ?_
    rw [pullbackFiberHomEquiv_apply_coe, pullbackFiberHomEquiv_apply_coe, hθfac (γ ≫ f) hc']
    have hlift : r.IsHomLift (γ ≫ f)
        (Fiber.fiberInclusion.map ((pullbackFiberCompIso a f γ).inv ≫
          pullbackFiberHom (θ f hf) γ ≫ (pullbackFiberCompIso b f γ).hom) ≫
          IsPreFibered.pullbackMap b.2 (γ ≫ f)) :=
      isHomLift_id_comp_explicit ((pullbackFiberCompIso a f γ).inv ≫
        pullbackFiberHom (θ f hf) γ ≫ (pullbackFiberCompIso b f γ).hom).2
        (isHomLift_pullbackMap_of_fiber b _)
    have := hFg (γ ≫ f) hc'
    refine (IsStronglyCartesian.map_uniq r u πb (g := γ ≫ f) (f' := (γ ≫ f) ≫ u) rfl _ _
      ?_).symm
    simp only [Functor.map_comp, Category.assoc, pullbackFiberCompIso_hom_fac_assoc,
      pullbackFiberHom_fac_assoc]
    rw [reassoc_of% hθfac f hf, hσfac f hf]
    have hmem' : S.arrows (r.map ((Fiber.fiberInclusion.map (pullbackFiberCompIso a f γ).inv ≫
        IsPreFibered.pullbackMap (pullbackFiber r a f).2 γ) ≫ IsPreFibered.pullbackMap a.2 f)) := by
      rw [Category.assoc, pullbackFiberCompIso_inv_fac]
      exact hmem _ (IsPreFibered.pullbackMap a.2 (γ ≫ f)) (hΦg _) hc'
    rw [← Category.assoc, ← hFcomp _ _ _ hmem']
    refine hFcongr ?_ _ _
    rw [Category.assoc, pullbackFiberCompIso_inv_fac])
  have hmlift : r.IsHomLift (𝟙 (r.obj A)) m.1 := m.2
  refine ⟨m.1 ≫ πb, ?_, ?_⟩
  · have h : r.IsHomLift u (m.1 ≫ πb) := isHomLift_id_comp_explicit m.2 hπb.toIsHomLift
    rw [IsHomLift.fac' r u (m.1 ≫ πb)]
    simp
  · intro W Φ hΦ
    have hκ := liftToPullback_fac a (r.map Φ) Φ (IsHomLift.map (p := r) Φ)
    have key : IsPreFibered.pullbackMap a.2 (r.map Φ) ≫ m.1 ≫ πb =
        F (IsPreFibered.pullbackMap a.2 (r.map Φ))
          (hmem _ (IsPreFibered.pullbackMap a.2 (r.map Φ)) (hΦg _) hΦ) := by
      rw [← hσfac _ hΦ, ← hθfac _ hΦ, ← hm _ hΦ, Category.assoc, pullbackFiberHom_fac_assoc]
      rfl
    calc Φ ≫ m.1 ≫ πb
        = (liftToPullback a (r.map Φ) Φ (IsHomLift.map (p := r) Φ) ≫
            IsPreFibered.pullbackMap a.2 (r.map Φ)) ≫ m.1 ≫ πb := by rw [hκ]
      _ = liftToPullback a (r.map Φ) Φ (IsHomLift.map (p := r) Φ) ≫
            F (IsPreFibered.pullbackMap a.2 (r.map Φ))
              (hmem _ (IsPreFibered.pullbackMap a.2 (r.map Φ)) (hΦg _) hΦ) := by
          rw [Category.assoc, key]
      _ = F (liftToPullback a (r.map Φ) Φ (IsHomLift.map (p := r) Φ) ≫
            IsPreFibered.pullbackMap a.2 (r.map Φ)) (by rw [hκ]; exact hΦ) :=
          (hFcomp _ _ _ _).symm
      _ = F Φ hΦ := hFcongr hκ _ _

end Glue

namespace SieveDescentDatum

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {r : 𝒳 ⥤ 𝒮} [r.IsFibered] {T : 𝒮} {R : Sieve T} (D : SieveDescentDatum r R)

/-- `CategoryTheory.Functor.SieveDescentDatum.comp_transferHom` with the composites `γ ≫ u`,
`γ ≫ v` and `t ≫ a` given by name. -/
theorem comp_transferHom_of_comp_eq {V W Z Z' : 𝒮} {f : V ⟶ T} (hf : R f) {g : W ⟶ T}
    (hg : R g) (u : Z ⟶ V) (v : Z ⟶ W) (h : u ≫ f = v ≫ g) (γ : Z' ⟶ Z) {ω ω' : 𝒳}
    (a : ω ⟶ (D.obj f hf).1) (ha : r.IsHomLift u a) (t : ω' ⟶ ω) (ht : r.IsHomLift γ t)
    (u' : Z' ⟶ V) (v' : Z' ⟶ W) (hu : γ ≫ u = u') (hv : γ ≫ v = v') (h' : u' ≫ f = v' ≫ g)
    (b : ω' ⟶ (D.obj f hf).1) (hb : t ≫ a = b) (hbl : r.IsHomLift u' b) :
    t ≫ D.transferHom hf hg u v h a ha = D.transferHom hf hg u' v' h' b hbl := by
  subst hu hv hb
  exact D.comp_transferHom hf hg u v h γ a ha t ht h' hbl

end SieveDescentDatum

end Functor

namespace Over

open _root_.CategoryTheory.Functor

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {U : 𝒞} {𝒮 : Type u₂} [Category.{v₂} 𝒮]

/-! ### Transfer lemmas with a named target object -/

section Transfer

variable (p : 𝒮 ⥤ Over U)

/-- `CategoryTheory.Functor.isHomLift_of_comp_forget` with the target of the base morphism named:
a morphism lying over `g.left` for `p ⋙ j_U` lies over `g` for `p`, as soon as its target lies over
the target of `g`. -/
lemma isHomLift_of_comp_forget_of_obj_eq {a b : 𝒮} {A B : Over U} (g : A ⟶ B) (φ : a ⟶ b)
    (hb : p.obj b = B) (h : (p ⋙ Over.forget U).IsHomLift g.left φ) : p.IsHomLift g φ := by
  subst hb
  exact Functor.isHomLift_of_comp_forget p g φ h

/-- The source of a morphism lying over `g.left` for `p ⋙ j_U`, whose target lies over the target
of `g`, lies over the source of `g`. -/
lemma obj_eq_of_isHomLift_comp_forget {a b : 𝒮} {A B : Over U} (g : A ⟶ B) (φ : a ⟶ b)
    (hb : p.obj b = B) (h : (p ⋙ Over.forget U).IsHomLift g.left φ) : p.obj a = A :=
  have := isHomLift_of_comp_forget_of_obj_eq p g φ hb h
  IsHomLift.domain_eq p g φ

/-- `CategoryTheory.Functor.isStronglyCartesian_of_comp_forget` with the target of the base
morphism named. -/
lemma isStronglyCartesian_of_comp_forget_of_obj_eq {a b : 𝒮} {A B : Over U} (g : A ⟶ B)
    (φ : a ⟶ b) (hb : p.obj b = B)
    (h : (p ⋙ Over.forget U).IsStronglyCartesian g.left φ) : p.IsStronglyCartesian g φ := by
  subst hb
  exact Functor.isStronglyCartesian_of_comp_forget p g φ h

/-- The structure morphism of an object of `𝒞/U` read through an equality of objects. -/
lemma hom_eq_eqToHom_comp {X Y : Over U} (e : X = Y) :
    X.hom = eqToHom (congrArg (fun Z : Over U ↦ Z.left) e) ≫ Y.hom := by
  subst e
  simp

end Transfer

/-! ### Condition (2) of Stacks 026F -/

section MorSheaf

variable (p : 𝒮 ⥤ Over U) [p.IsFibered] [(p ⋙ Over.forget U).IsFibered]
  {J : GrothendieckTopology 𝒞}

/-- **Condition (2) of Stacks 026F descends from `p ⋙ j_U` to `p`.** If the presheaves `Mor(x, y)`
of `p ⋙ j_U : 𝒮 ⥤ 𝒞` are `J`-sheaves, then those of `p : 𝒮 ⥤ 𝒞/U` are `J.over U`-sheaves. No
hypothesis on `U` is needed. -/
theorem isMorSheaf_of_isMorSheaf_comp_forget
    (hq : ∀ (V : 𝒞) (x y : (p ⋙ Over.forget U).Fiber V),
      Functor.IsMorSheaf (p ⋙ Over.forget U) J V x y)
    (A : Over U) (x y : p.Fiber A) : Functor.IsMorSheaf p (J.over U) A x y := by
  refine Functor.isMorSheaf_of_locallyEqual_of_amalgamation ?_ ?_ A x y
  · intro X Y F G h
    obtain ⟨hbase, R, hR, hagree⟩ := h
    obtain ⟨R', rfl⟩ := (Sieve.overEquiv (p.obj X)).symm.surjective R
    have hR' : R' ∈ J (p.obj X).left := by simpa using (J.mem_over_iff _).1 hR
    exact Functor.eq_of_locallyEqual_of_isMorSheaf hq
      ⟨congrArg (fun k : p.obj X ⟶ p.obj Y ↦ k.left) hbase, R', hR', fun w φ hφ ↦ hagree φ hφ⟩
  · intro X Y u S hS F hFbase hFcomp
    obtain ⟨S', rfl⟩ := (Sieve.overEquiv (p.obj X)).symm.surjective S
    have hS' : S' ∈ J (p.obj X).left := by simpa using (J.mem_over_iff _).1 hS
    obtain ⟨G, hG, hGF⟩ := Functor.exists_hom_of_isMorSheaf hq (A := X) (B := Y) u.left hS'
      (fun Φ hΦ ↦ F Φ hΦ)
      (fun Φ hΦ ↦ by
        change (p.map (F Φ hΦ)).left = (p.map Φ).left ≫ u.left
        rw [hFbase Φ hΦ, Over.comp_left])
      (fun Ψ Φ hΦ hΨΦ ↦ hFcomp Ψ Φ hΦ hΨΦ)
    exact ⟨G, Over.OverMorphism.ext hG, fun Φ hΦ ↦ hGF Φ hΦ⟩

end MorSheaf

/-! ### Condition (3) of Stacks 026F

A descent datum `D` for `p` relative to a `J.over U`-covering sieve `(overEquiv A).symm R'` of `A`
is read as a descent datum `sliceDatum p D` for `p ⋙ j_U` relative to the `J`-covering sieve `R'`
of `A.left`: its object over `f : V ⟶ A.left` is the object of `D` over the arrow
`Over.homMk f : Over.mk (f ≫ A.hom) ⟶ A`, and its gluing isomorphisms are defined by the transfer
of morphisms along the gluing isomorphisms of `D`
(`CategoryTheory.Functor.SieveDescentDatum.transferHom`). Chosen pullbacks for `p` and for
`p ⋙ j_U` are never compared directly. -/

section Descent

variable (p : 𝒮 ⥤ Over U) [p.IsFibered] [(p ⋙ Over.forget U).IsFibered]
  {A : Over U} {R' : Sieve A.left}
  (D : Functor.SieveDescentDatum p ((Sieve.overEquiv A).symm R'))

namespace SliceDescent

/-- The arrow `Over.mk (f ≫ A.hom) ⟶ A` of `𝒞/U` over an arrow `f : V ⟶ A.left` of `𝒞`. -/
abbrev canon (A : Over U) {V : 𝒞} (f : V ⟶ A.left) : Over.mk (f ≫ A.hom) ⟶ A :=
  Over.homMk f rfl

/-- The arrow `Over.mk (ε ≫ f ≫ A.hom) ⟶ Over.mk (f ≫ A.hom)` over `ε`. -/
abbrev hat (A : Over U) {V Z : 𝒞} (f : V ⟶ A.left) (ε : Z ⟶ V) :
    Over.mk (ε ≫ f ≫ A.hom) ⟶ Over.mk (f ≫ A.hom) :=
  Over.homMk ε rfl

/-- The arrow `Over.mk (ε ≫ f ≫ A.hom) ⟶ Over.mk (g ≫ A.hom)` over `ε'`, for `ε ≫ f = ε' ≫ g`. -/
abbrev hat' (A : Over U) {V W Z : 𝒞} (f : V ⟶ A.left) (g : W ⟶ A.left) (ε : Z ⟶ V)
    (ε' : Z ⟶ W) (heq : ε ≫ f = ε' ≫ g) : Over.mk (ε ≫ f ≫ A.hom) ⟶ Over.mk (g ≫ A.hom) :=
  Over.homMk ε' (by simp only [Over.mk_hom]; rw [reassoc_of% heq])

lemma hat_comp_canon {V W Z : 𝒞} (f : V ⟶ A.left) (g : W ⟶ A.left) (ε : Z ⟶ V) (ε' : Z ⟶ W)
    (heq : ε ≫ f = ε' ≫ g) : hat A f ε ≫ canon A f = hat' A f g ε ε' heq ≫ canon A g := by
  ext
  simpa using heq

/-- A member `f` of `R'` gives the member `Over.homMk f` of `(overEquiv A).symm R'`. -/
lemma canon_mem {V : 𝒞} {f : V ⟶ A.left} (hf : R' f) :
    ((Sieve.overEquiv A).symm R').arrows (canon A f) :=
  hf

/-- A member `f` of `(overEquiv A).symm R'` gives the member `f.left` of `R'`. -/
lemma left_mem {B : Over U} {f : B ⟶ A} (hf : ((Sieve.overEquiv A).symm R').arrows f) :
    R' f.left :=
  hf

/-- The object of `sliceDatum` over a member `f` of `R'`. -/
abbrev objQ ⦃V : 𝒞⦄ (f : V ⟶ A.left) (hf : R' f) : (p ⋙ Over.forget U).Fiber V :=
  ⟨(D.obj (canon A f) (canon_mem hf)).1,
    congrArg (fun B : Over U ↦ B.left) (D.obj (canon A f) (canon_mem hf)).2⟩

/-- The chosen pullback morphism of `p ⋙ j_U` at an object of `sliceDatum`. -/
abbrev πq ⦃V Z : 𝒞⦄ (f : V ⟶ A.left) (hf : R' f) (ε : Z ⟶ V) :
    (pullbackFiber (p ⋙ Over.forget U) (objQ p D f hf) ε).1 ⟶
      (D.obj (canon A f) (canon_mem hf)).1 :=
  IsPreFibered.pullbackMap (objQ p D f hf).2 ε

lemma isHomLift_πq ⦃V Z : 𝒞⦄ (f : V ⟶ A.left) (hf : R' f) (ε : Z ⟶ V) {h : Z ⟶ U}
    (k : Over.mk h ⟶ Over.mk (f ≫ A.hom)) (hk : k.left = ε) : p.IsHomLift k (πq p D f hf ε) := by
  refine isHomLift_of_comp_forget_of_obj_eq p k _ (D.obj (canon A f) (canon_mem hf)).2 ?_
  rw [hk]
  exact Functor.isHomLift_pullbackMap_of_fiber (objQ p D f hf) ε

lemma obj_pullbackFiber ⦃V Z : 𝒞⦄ (f : V ⟶ A.left) (hf : R' f) (ε : Z ⟶ V) :
    p.obj (pullbackFiber (p ⋙ Over.forget U) (objQ p D f hf) ε).1 = Over.mk (ε ≫ f ≫ A.hom) :=
  have := isHomLift_πq p D f hf ε (hat A f ε) rfl
  IsHomLift.domain_eq p (hat A f ε) (πq p D f hf ε)

/-- The morphism of `𝒮` attached to a pair `(ε, ε')`: the transfer of the chosen pullback
morphism of `p ⋙ j_U` along the gluing isomorphism of `D`. -/
def transfer ⦃V W Z : 𝒞⦄ ⦃f : V ⟶ A.left⦄ (hf : R' f) ⦃g : W ⟶ A.left⦄ (hg : R' g)
    (ε : Z ⟶ V) (ε' : Z ⟶ W) (heq : ε ≫ f = ε' ≫ g) :
    (pullbackFiber (p ⋙ Over.forget U) (objQ p D f hf) ε).1 ⟶
      (D.obj (canon A g) (canon_mem hg)).1 :=
  D.transferHom (canon_mem hf) (canon_mem hg) (hat A f ε) (hat' A f g ε ε' heq)
    (hat_comp_canon f g ε ε' heq) (πq p D f hf ε) (isHomLift_πq p D f hf ε _ rfl)

lemma isHomLift_transfer ⦃V W Z : 𝒞⦄ ⦃f : V ⟶ A.left⦄ (hf : R' f) ⦃g : W ⟶ A.left⦄
    (hg : R' g) (ε : Z ⟶ V) (ε' : Z ⟶ W) (heq : ε ≫ f = ε' ≫ g) :
    (p ⋙ Over.forget U).IsHomLift ε' (transfer p D hf hg ε ε' heq) :=
  Functor.isHomLift_comp_forget p (hat' A f g ε ε' heq) (transfer p D hf hg ε ε' heq)
    (D.isHomLift_transferHom (canon_mem hf) (canon_mem hg) _ _ _ _ _)

/-- The gluing morphism of `sliceDatum`. -/
def descHom ⦃V W Z : 𝒞⦄ ⦃f : V ⟶ A.left⦄ (hf : R' f) ⦃g : W ⟶ A.left⦄ (hg : R' g)
    (ε : Z ⟶ V) (ε' : Z ⟶ W) (heq : ε ≫ f = ε' ≫ g) :
    pullbackFiber (p ⋙ Over.forget U) (objQ p D f hf) ε ⟶
      pullbackFiber (p ⋙ Over.forget U) (objQ p D g hg) ε' :=
  ⟨Functor.liftToPullback (objQ p D g hg) ε' (transfer p D hf hg ε ε' heq)
      (isHomLift_transfer p D hf hg ε ε' heq),
    Functor.isHomLift_liftToPullback _ _ _ _⟩

lemma descHom_fac ⦃V W Z : 𝒞⦄ ⦃f : V ⟶ A.left⦄ (hf : R' f) ⦃g : W ⟶ A.left⦄ (hg : R' g)
    (ε : Z ⟶ V) (ε' : Z ⟶ W) (heq : ε ≫ f = ε' ≫ g) :
    Fiber.fiberInclusion.map (descHom p D hf hg ε ε' heq) ≫ πq p D g hg ε' =
      transfer p D hf hg ε ε' heq :=
  Functor.liftToPullback_fac (objQ p D g hg) ε' (transfer p D hf hg ε ε' heq)
    (isHomLift_transfer p D hf hg ε ε' heq)

/-- A morphism of the fibre of `p ⋙ j_U` into a chosen pullback of an object of `sliceDatum` lies,
for `p`, over the comparison `Over.homMk (𝟙 _)`. -/
lemma isHomLift_fiber ⦃V Z : 𝒞⦄ (f : V ⟶ A.left) (hf : R' f) (ε : Z ⟶ V) {ω : 𝒮} {Y₀ : Over U}
    (k : Y₀ ⟶ Over.mk (ε ≫ f ≫ A.hom))
    (t : ω ⟶ (pullbackFiber (p ⋙ Over.forget U) (objQ p D f hf) ε).1)
    (ht : (p ⋙ Over.forget U).IsHomLift k.left t) : p.IsHomLift k t :=
  isHomLift_of_comp_forget_of_obj_eq p k t (obj_pullbackFiber p D f hf ε) ht

lemma descHom_comp ⦃V W X Z : 𝒞⦄ ⦃f : V ⟶ A.left⦄ (hf : R' f) ⦃g : W ⟶ A.left⦄ (hg : R' g)
    ⦃h : X ⟶ A.left⦄ (hh : R' h) (ε₁ : Z ⟶ V) (ε₂ : Z ⟶ W) (ε₃ : Z ⟶ X)
    (h₁₂ : ε₁ ≫ f = ε₂ ≫ g) (h₂₃ : ε₂ ≫ g = ε₃ ≫ h) (h₁₃ : ε₁ ≫ f = ε₃ ≫ h) :
    descHom p D hf hg ε₁ ε₂ h₁₂ ≫ descHom p D hg hh ε₂ ε₃ h₂₃ = descHom p D hf hh ε₁ ε₃ h₁₃ := by
  refine Functor.fiber_hom_ext_of_cartesian ε₃ (πq p D h hh ε₃)
    (IsPreFibered.pullbackMap.IsCartesian _ _) _ _ ?_
  let γ : Over.mk (ε₁ ≫ f ≫ A.hom) ⟶ Over.mk (ε₂ ≫ g ≫ A.hom) :=
    Over.homMk (𝟙 Z) (by simpa using ((reassoc_of% h₁₂) A.hom).symm)
  simp only [Functor.map_comp, Category.assoc]
  rw [descHom_fac, descHom_fac]
  unfold transfer
  rw [D.comp_transferHom_of_comp_eq (canon_mem hg) (canon_mem hh) _ _ _ γ _ _ _
    (isHomLift_fiber p D g hg ε₂ γ (Fiber.fiberInclusion.map (descHom p D hf hg ε₁ ε₂ h₁₂))
      (descHom p D hf hg ε₁ ε₂ h₁₂).2) (hat' A f g ε₁ ε₂ h₁₂)
    (hat' A f h ε₁ ε₃ h₁₃) (by ext; simp [γ]) (by ext; simp [γ]) (by ext; simpa using h₂₃) _
    (descHom_fac p D hf hg ε₁ ε₂ h₁₂)
    (D.isHomLift_transferHom (canon_mem hf) (canon_mem hg) _ _ _ _ _)]
  exact D.transferHom_transferHom (canon_mem hf) (canon_mem hg) (canon_mem hh)
    _ _ _ _ _ _ _ _

lemma descHom_self ⦃V Z : 𝒞⦄ ⦃f : V ⟶ A.left⦄ (hf : R' f) (ε : Z ⟶ V) (heq : ε ≫ f = ε ≫ f) :
    descHom p D hf hf ε ε heq = 𝟙 _ := by
  refine Functor.fiber_hom_ext_of_cartesian ε (πq p D f hf ε)
    (IsPreFibered.pullbackMap.IsCartesian _ _) _ _ ?_
  rw [descHom_fac]
  exact (D.transferHom_self (canon_mem hf) (hat A f ε) _ _ _).trans
    (Category.id_comp _).symm

/-- The gluing isomorphism of `sliceDatum`. -/
@[simps]
def descIso ⦃V W Z : 𝒞⦄ ⦃f : V ⟶ A.left⦄ (hf : R' f) ⦃g : W ⟶ A.left⦄ (hg : R' g)
    (ε : Z ⟶ V) (ε' : Z ⟶ W) (heq : ε ≫ f = ε' ≫ g) :
    pullbackFiber (p ⋙ Over.forget U) (objQ p D f hf) ε ≅
      pullbackFiber (p ⋙ Over.forget U) (objQ p D g hg) ε' where
  hom := descHom p D hf hg ε ε' heq
  inv := descHom p D hg hf ε' ε heq.symm
  hom_inv_id := by rw [descHom_comp p D hf hg hf _ _ _ heq heq.symm rfl, descHom_self]
  inv_hom_id := by rw [descHom_comp p D hg hf hg _ _ _ heq.symm heq rfl, descHom_self]

end SliceDescent

open SliceDescent in
/-- **A descent datum for `p` relative to a `J.over U`-covering sieve, read as one for `p ⋙ j_U`.**
Its object over a member `f : V ⟶ A.left` of `R'` is the object of `D` over
`Over.homMk f : Over.mk (f ≫ A.hom) ⟶ A`. -/
def sliceDatum : Functor.SieveDescentDatum (p ⋙ Over.forget U) R' where
  obj _ f hf := objQ p D f hf
  iso _ _ _ _ hf _ hg ε ε' heq := descIso p D hf hg ε ε' heq
  cocycle _ _ _ _ _ hf _ hg _ hh ε₁ ε₂ ε₃ h₁₂ h₂₃ h₁₃ :=
    descHom_comp p D hf hg hh ε₁ ε₂ ε₃ h₁₂ h₂₃ h₁₃
  iso_pullback := by
    intro V W Z Z' f hf g hg ε ε' heq γ
    refine Functor.fiber_hom_ext_of_cartesian (γ ≫ ε') (πq p D g hg (γ ≫ ε'))
      (IsPreFibered.pullbackMap.IsCartesian _ _) _ _ ?_
    simp only [descIso_hom, Functor.pullbackFiberIso_hom, Functor.map_comp, Category.assoc]
    rw [Functor.pullbackFiberCompIso_hom_fac, Functor.pullbackFiberHom_fac_assoc, descHom_fac,
      descHom_fac]
    unfold transfer
    have hγ : (p ⋙ Over.forget U).IsHomLift γ
        (Fiber.fiberInclusion.map (Functor.pullbackFiberCompIso (objQ p D f hf) ε γ).inv ≫
          IsPreFibered.pullbackMap (pullbackFiber (p ⋙ Over.forget U) (objQ p D f hf) ε).2 γ) :=
      Functor.isHomLift_id_comp_explicit (Subtype.prop _)
        (Functor.isHomLift_pullbackMap_of_fiber _ γ)
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    exact D.comp_transferHom_of_comp_eq (canon_mem hf) (canon_mem hg) (hat A f ε)
      (hat' A f g ε ε' heq) (hat_comp_canon f g ε ε' heq)
      (Over.homMk γ (by simp) : Over.mk ((γ ≫ ε) ≫ f ≫ A.hom) ⟶ Over.mk (ε ≫ f ≫ A.hom))
      (πq p D f hf ε) (isHomLift_πq p D f hf ε _ rfl) _
      (isHomLift_of_comp_forget_of_obj_eq p _ _ (obj_pullbackFiber p D f hf ε) hγ)
      (hat A f (γ ≫ ε)) (hat' A f g (γ ≫ ε) (γ ≫ ε') (by rw [Category.assoc, Category.assoc, heq]))
      (by ext; simp) (by ext; simp) _ (πq p D f hf (γ ≫ ε))
      ((Category.assoc _ _ _).trans (Functor.pullbackFiberCompIso_inv_fac _ _ _))
      (isHomLift_πq p D f hf (γ ≫ ε) _ rfl)

namespace SliceDescent

/-- The comparison `B ⟶ Over.mk (f.left ≫ A.hom)` of `𝒞/U` over the identity of `B.left`, for an
arrow `f : B ⟶ A`. -/
abbrev ιOver {B : Over U} (f : B ⟶ A) : B ⟶ Over.mk (f.left ≫ A.hom) :=
  Over.homMk (𝟙 B.left) (by simp)

lemma ιOver_comp_canon {B : Over U} (f : B ⟶ A) : ιOver f ≫ canon A f.left = f := by
  ext
  simp

lemma id_comp_eq_ιOver_comp_canon {B : Over U} (f : B ⟶ A) :
    𝟙 B ≫ f = ιOver f ≫ canon A f.left := by
  rw [Category.id_comp, ιOver_comp_canon]

/-- The comparison in `𝒮` between the object of `D` over an arrow `f : B ⟶ A` and the object of `D`
over the canonical arrow `Over.homMk f.left`: the transfer of the identity. -/
def compHom {B : Over U} (f : B ⟶ A) (hf : ((Sieve.overEquiv A).symm R').arrows f) :
    (D.obj f hf).1 ⟶ (D.obj (canon A f.left) (canon_mem (left_mem hf))).1 :=
  D.transferHom hf (canon_mem (left_mem hf)) (𝟙 B) (ιOver f) (id_comp_eq_ιOver_comp_canon f) (𝟙 _)
    (IsHomLift.id (D.obj f hf).2)

omit [(p ⋙ Over.forget U).IsFibered] in
lemma isHomLift_compHom {B : Over U} (f : B ⟶ A) (hf : ((Sieve.overEquiv A).symm R').arrows f) :
    p.IsHomLift (ιOver f) (compHom p D f hf) :=
  D.isHomLift_transferHom _ _ _ _ _ _ _

instance isIso_compHom {B : Over U} (f : B ⟶ A) (hf : ((Sieve.overEquiv A).symm R').arrows f) :
    IsIso (compHom p D f hf) := by
  have : IsIso (IsPreFibered.pullbackMap (D.obj f hf).2 (𝟙 B)) :=
    have := Functor.isStronglyCartesian_pullbackMap_of_fiber (D.obj f hf) (𝟙 B)
    IsStronglyCartesian.isIso_of_base_isIso p (𝟙 B) _
  have : IsIso (Functor.liftToPullback (D.obj f hf) (𝟙 B) (𝟙 _)
      (IsHomLift.id (D.obj f hf).2)) := by
    have h := Functor.liftToPullback_fac (D.obj f hf) (𝟙 B) (𝟙 _) (IsHomLift.id (D.obj f hf).2)
    have : IsIso (Functor.liftToPullback (D.obj f hf) (𝟙 B) (𝟙 _)
        (IsHomLift.id (D.obj f hf).2) ≫ IsPreFibered.pullbackMap (D.obj f hf).2 (𝟙 B)) := by
      rw [h]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (IsPreFibered.pullbackMap (D.obj f hf).2 (𝟙 B))
  have : IsIso (ιOver f) := by
    have : IsIso ((Over.forget U).map (ιOver f)) := by
      change IsIso (𝟙 _)
      infer_instance
    exact isIso_of_reflects_iso (ιOver f) (Over.forget U)
  have : IsIso (IsPreFibered.pullbackMap (D.obj (canon A f.left) (canon_mem (left_mem hf))).2
      (ιOver f)) :=
    have := Functor.isStronglyCartesian_pullbackMap_of_fiber
      (D.obj (canon A f.left) (canon_mem (left_mem hf))) (ιOver f)
    IsStronglyCartesian.isIso_of_base_isIso p (ιOver f) _
  unfold compHom Functor.SieveDescentDatum.transferHom
  infer_instance

end SliceDescent

open SliceDescent in
/-- **Effectivity descends from `sliceDatum p D` to `D`**, when `h_U` is a sheaf. The object of the
fibre of `p ⋙ j_U` over `A.left` that `sliceDatum p D` descends to lies over `A` for `p`, because
its structure morphism to `U` and `A.hom` agree locally on `R'` and `h_U` is separated. -/
theorem isEffective_of_isEffective_sliceDatum {J : GrothendieckTopology 𝒞}
    (hU : Presieve.IsSheaf J (yoneda.obj U)) (hR' : R' ∈ J A.left)
    (hD : (sliceDatum p D).IsEffective) : D.IsEffective := by
  obtain ⟨x', ζ', hζc, hζg⟩ := hD
  obtain ⟨ζ, hζc, hζg⟩ : ∃ ζ : ∀ ⦃V : 𝒞⦄ (f : V ⟶ A.left) (hf : R' f),
      (D.obj (canon A f) (canon_mem hf)).1 ⟶ x'.1,
      (∀ ⦃V : 𝒞⦄ (f : V ⟶ A.left) (hf : R' f), (p ⋙ Over.forget U).IsCartesian f (ζ f hf)) ∧
      ∀ ⦃V W Z : 𝒞⦄ ⦃f : V ⟶ A.left⦄ (hf : R' f) ⦃g : W ⟶ A.left⦄ (hg : R' g) (ε : Z ⟶ V)
        (ε' : Z ⟶ W) (heq : ε ≫ f = ε' ≫ g),
        Fiber.fiberInclusion.map (descHom p D hf hg ε ε' heq) ≫ πq p D g hg ε' ≫ ζ g hg =
          πq p D f hf ε ≫ ζ f hf :=
    ⟨ζ', hζc, hζg⟩
  have hloc : ∀ ⦃V : 𝒞⦄ (f : V ⟶ A.left), R' f →
      f ≫ eqToHom x'.2.symm ≫ (p.obj x'.1).hom = f ≫ A.hom := by
    intro V f hf
    have hl : (p ⋙ Over.forget U).IsHomLift f (ζ f hf) := (hζc f hf).toIsHomLift
    let g : Over.mk ((f ≫ eqToHom x'.2.symm) ≫ (p.obj x'.1).hom) ⟶ p.obj x'.1 :=
      Over.homMk (f ≫ eqToHom x'.2.symm) rfl
    have e1 : p.obj (D.obj (canon A f) (canon_mem hf)).1 =
        Over.mk ((f ≫ eqToHom x'.2.symm) ≫ (p.obj x'.1).hom) :=
      obj_eq_of_isHomLift_comp_forget p g (ζ f hf) rfl
        (inferInstance : (p ⋙ Over.forget U).IsHomLift (f ≫ eqToHom x'.2.symm) (ζ f hf))
    have e2 := hom_eq_eqToHom_comp ((D.obj (canon A f) (canon_mem hf)).2.symm.trans e1)
    simpa using e2.symm
  have hc : eqToHom x'.2.symm ≫ (p.obj x'.1).hom = A.hom :=
    (hU R' hR').isSeparatedFor.ext fun Y f hf ↦ by simpa using hloc f hf
  have hxA : p.obj x'.1 = A :=
    over_ext x'.2 (by rw [← hc, ← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp])
  refine ⟨⟨x'.1, hxA⟩, fun B f hf ↦ compHom p D f hf ≫ ζ f.left (left_mem hf), ?_, ?_⟩
  · intro B f hf
    have := hζc f.left (left_mem hf)
    have := isHomLift_compHom p D f hf
    have h1 : p.IsStronglyCartesian (canon A f.left) (ζ f.left (left_mem hf)) :=
      isStronglyCartesian_of_comp_forget_of_obj_eq p _ _ hxA
        (inferInstance : (p ⋙ Over.forget U).IsStronglyCartesian f.left (ζ f.left (left_mem hf)))
    have h2 : p.IsStronglyCartesian (ιOver f) (compHom p D f hf) :=
      IsStronglyCartesian.of_isIso (p := p) (ιOver f) (compHom p D f hf)
    have h3 : p.IsStronglyCartesian (ιOver f ≫ canon A f.left)
        (compHom p D f hf ≫ ζ f.left (left_mem hf)) := inferInstance
    rw [ιOver_comp_canon] at h3
    infer_instance
  · intro B C Z f hf g hg ε ε' heq
    have hπ : p.IsHomLift ε (IsPreFibered.pullbackMap (D.obj f hf).2 ε) :=
      Functor.isHomLift_pullbackMap_of_fiber _ ε
    have h₃ : ε ≫ f = (ε' ≫ ιOver g) ≫ canon A g.left := by
      rw [Category.assoc, ιOver_comp_canon, heq]
    have h₄ : ε ≫ f = (ε ≫ ιOver f) ≫ canon A f.left := by
      rw [Category.assoc, ιOver_comp_canon]
    have h₅ : (ε ≫ ιOver f) ≫ canon A f.left = (ε' ≫ ιOver g) ≫ canon A g.left := by
      rw [← h₃, ← h₄]
    have hL : Fiber.fiberInclusion.map (D.iso hf hg ε ε' heq).hom ≫
        IsPreFibered.pullbackMap (D.obj g hg).2 ε' ≫ compHom p D g hg =
        D.transferHom hf (canon_mem (left_mem hg)) ε (ε' ≫ ιOver g) h₃
          (IsPreFibered.pullbackMap (D.obj f hf).2 ε) hπ := by
      rw [← Category.assoc, ← D.transferHom_pullbackMap hf hg ε ε' heq]
      unfold compHom
      rw [D.comp_transferHom_of_comp_eq hg (canon_mem (left_mem hg)) (𝟙 C) (ιOver g)
        (id_comp_eq_ιOver_comp_canon g) ε'
        (𝟙 _) (IsHomLift.id (D.obj g hg).2) _ (D.isHomLift_transferHom _ _ _ _ _ _ _) ε'
        (ε' ≫ ιOver g) (Category.comp_id _) rfl (by rw [Category.assoc, ιOver_comp_canon]) _
        (Category.comp_id _) (D.isHomLift_transferHom _ _ _ _ _ _ _)]
      exact D.transferHom_transferHom hf hg (canon_mem (left_mem hg)) ε ε' (ε' ≫ ιOver g) heq _ h₃
        _ hπ
    have hR : IsPreFibered.pullbackMap (D.obj f hf).2 ε ≫ compHom p D f hf =
        D.transferHom hf (canon_mem (left_mem hf)) ε (ε ≫ ιOver f) h₄
          (IsPreFibered.pullbackMap (D.obj f hf).2 ε) hπ :=
      D.comp_transferHom_of_comp_eq hf (canon_mem (left_mem hf)) (𝟙 B) (ιOver f)
        (id_comp_eq_ιOver_comp_canon f) ε
        (𝟙 _) (IsHomLift.id (D.obj f hf).2) _ hπ ε (ε ≫ ιOver f) (Category.comp_id _) rfl h₄ _
        (Category.comp_id _) hπ
    have ha₀ : p.IsHomLift (ε ≫ ιOver f)
        (D.transferHom hf (canon_mem (left_mem hf)) ε (ε ≫ ιOver f) h₄
          (IsPreFibered.pullbackMap (D.obj f hf).2 ε) hπ) :=
      D.isHomLift_transferHom _ _ _ _ _ _ _
    have hT : D.transferHom hf (canon_mem (left_mem hg)) ε (ε' ≫ ιOver g) h₃
        (IsPreFibered.pullbackMap (D.obj f hf).2 ε)
        hπ = D.transferHom (canon_mem (left_mem hf)) (canon_mem (left_mem hg)) (ε ≫ ιOver f)
          (ε' ≫ ιOver g) h₅
          (D.transferHom hf (canon_mem (left_mem hf)) ε (ε ≫ ιOver f) h₄
            (IsPreFibered.pullbackMap (D.obj f hf).2 ε) hπ)
          ha₀ :=
      (D.transferHom_transferHom hf (canon_mem (left_mem hf)) (canon_mem (left_mem hg)) ε
        (ε ≫ ιOver f) (ε' ≫ ιOver g) h₄ h₅ h₃ _ hπ).symm
    have hqa : (p ⋙ Over.forget U).IsHomLift ε.left
        (D.transferHom hf (canon_mem (left_mem hf)) ε (ε ≫ ιOver f) h₄
          (IsPreFibered.pullbackMap (D.obj f hf).2 ε) hπ) := by
      have h := Functor.isHomLift_comp_forget p (ε ≫ ιOver f) _ ha₀
      have e1 : (Over.forget U).map (ε ≫ ιOver f) = ε.left := by simp
      rwa [e1] at h
    have hcfac := Functor.liftToPullback_fac (objQ p D f.left (left_mem hf)) ε.left _ hqa
    let κ : Z ⟶ Over.mk (ε.left ≫ f.left ≫ A.hom) := Over.homMk (𝟙 Z.left) (by simp)
    have hκ : p.IsHomLift κ (Functor.liftToPullback (objQ p D f.left (left_mem hf)) ε.left _ hqa) :=
      isHomLift_fiber p D f.left (left_mem hf) ε.left κ _ (Functor.isHomLift_liftToPullback _ _ _ _)
    have heq' : ε.left ≫ f.left = ε'.left ≫ g.left := by
      simpa using congrArg (fun k : Z ⟶ A ↦ k.left) heq
    have hC : Functor.liftToPullback (objQ p D f.left (left_mem hf)) ε.left _ hqa ≫
        transfer p D (left_mem hf) (left_mem hg) ε.left ε'.left heq' =
        D.transferHom (canon_mem (left_mem hf)) (canon_mem (left_mem hg)) (ε ≫ ιOver f)
          (ε' ≫ ιOver g) h₅
          (D.transferHom hf (canon_mem (left_mem hf)) ε (ε ≫ ιOver f) h₄
            (IsPreFibered.pullbackMap (D.obj f hf).2 ε) hπ)
          ha₀ := D.comp_transferHom_of_comp_eq (canon_mem (left_mem hf)) (canon_mem (left_mem hg))
      (hat A f.left ε.left)
      (hat' A f.left g.left ε.left ε'.left heq') (hat_comp_canon _ _ _ _ heq') κ
      (πq p D f.left (left_mem hf) ε.left) (isHomLift_πq p D f.left (left_mem hf) ε.left _ rfl) _
      hκ (ε ≫ ιOver f)
      (ε' ≫ ιOver g) (by ext; simp [κ]) (by ext; simp [κ]) h₅ _ hcfac ha₀
    have hζ := hζg (left_mem hf) (left_mem hg) ε.left ε'.left heq'
    calc Fiber.fiberInclusion.map (D.iso hf hg ε ε' heq).hom ≫
          IsPreFibered.pullbackMap (D.obj g hg).2 ε' ≫ compHom p D g hg ≫ ζ g.left (left_mem hg)
        = (Fiber.fiberInclusion.map (D.iso hf hg ε ε' heq).hom ≫
          IsPreFibered.pullbackMap (D.obj g hg).2 ε' ≫ compHom p D g hg) ≫
          ζ g.left (left_mem hg) := by
          simp only [Category.assoc]
      _ = Functor.liftToPullback (objQ p D f.left (left_mem hf)) ε.left _ hqa ≫
          (Fiber.fiberInclusion.map (descHom p D (left_mem hf) (left_mem hg) ε.left ε'.left heq') ≫
            πq p D g.left (left_mem hg) ε'.left ≫ ζ g.left (left_mem hg)) := by
          rw [hL, hT, ← hC, ← descHom_fac p D (left_mem hf) (left_mem hg) ε.left ε'.left heq']
          simp only [Category.assoc]
      _ = (Functor.liftToPullback (objQ p D f.left (left_mem hf)) ε.left _ hqa ≫
          πq p D f.left (left_mem hf) ε.left) ≫ ζ f.left (left_mem hf) := by
          rw [hζ, Category.assoc]
      _ = IsPreFibered.pullbackMap (D.obj f hf).2 ε ≫ compHom p D f hf ≫
          ζ f.left (left_mem hf) := by
          rw [hcfac, ← hR, Category.assoc]

end Descent

/-- **Construction B of Stacks 04WV, at the level of stacks, for an arbitrary site.** Let `U` be an
object of `𝒞` whose representable presheaf `h_U` is a sheaf, and let `p : 𝒮 ⥤ 𝒞/U` be a functor
whose composite with the localization functor `j_U` is a stack over `(𝒞, J)`. Then `p` itself is a
stack over the site `(𝒞/U, J.over U)`. This is the source's "in this case it is automatically the
case that `p : 𝒯 → 𝒞/U` is a stack over `𝒞/U`".

No fibre products are assumed in `𝒞`: the proof checks the three conditions of Stacks 026F directly.
A covering sieve of `A` in `𝒞/U` is `(overEquiv A).symm R'` for a covering sieve `R'` of `A.left` in
`𝒞`, every object of `𝒞` mapping to `A.left` being automatically over `U`. Condition (1) is
`CategoryTheory.Functor.isFibered_of_comp_forget`; condition (2) is
`CategoryTheory.Over.isMorSheaf_of_isMorSheaf_comp_forget`, through the description of sheaves of
morphisms by gluing; and for condition (3) a descent datum for `p` is read as the descent datum
`CategoryTheory.Over.sliceDatum` for `p ⋙ j_U`, whose effectivity gives back that of the original
one by `CategoryTheory.Over.isEffective_of_isEffective_sliceDatum`. **The sheaf hypothesis on `h_U`
is used only there**, to see that the descended object lies over `A`. Compare
`CategoryTheory.Over.isStack_of_comp_forget`, the same statement under `[HasPullbacks 𝒞]`. -/
@[stacks 04WV]
theorem isStack_of_isStack_comp_forget (p : 𝒮 ⥤ Over U) {J : GrothendieckTopology 𝒞}
    (hU : Presheaf.IsSheaf J (yoneda.obj U)) (hq : (p ⋙ Over.forget U).IsStack J) :
    p.IsStack (J.over U) := by
  have hqf : (p ⋙ Over.forget U).IsFibered := hq.isFibered
  have hpf : p.IsFibered := Functor.isFibered_of_comp_forget p hq.isFibered
  refine ⟨hpf, isMorSheaf_of_isMorSheaf_comp_forget p hq.isMorSheaf, ?_⟩
  intro A R hR D
  obtain ⟨R', rfl⟩ := (Sieve.overEquiv A).symm.surjective R
  have hR' : R' ∈ J A.left := by simpa using (J.mem_over_iff _).1 hR
  exact isEffective_of_isEffective_sliceDatum p D ((isSheaf_iff_isSheaf_of_type J _).1 hU) hR'
    (hq.hasEffectiveDescent R' hR' (sliceDatum p D))

/-- **Stacks over `𝒞/U` are the stacks over `𝒞` mapping to `𝒞/U`**, Constructions A and B of
Stacks 04WV together: when `h_U` is a sheaf, `p : 𝒮 ⥤ 𝒞/U` is a stack over `(𝒞/U, J.over U)` if
and only if `p ⋙ j_U` is a stack over `(𝒞, J)`. -/
theorem isStack_iff_isStack_comp_forget (p : 𝒮 ⥤ Over U) {J : GrothendieckTopology 𝒞}
    (hU : Presheaf.IsSheaf J (yoneda.obj U)) :
    p.IsStack (J.over U) ↔ (p ⋙ Over.forget U).IsStack J :=
  ⟨Functor.isStack_comp_forget p hU, isStack_of_isStack_comp_forget p hU⟩

/-! ### Constructions A and B as mutually inverse functors of the 2-categories of stacks

The bijection on objects, for an arbitrary site. Together with
`CategoryTheory.Over.stackConstructionHomEquiv` and `CategoryTheory.Over.stackConstructionHom₂Equiv`
it exhibits Constructions A and B as mutually inverse functors of the two 2-categories of
Stacks 04WV. The universes are pinned as in
`StacksFrontier/CategoryTheory/Sites/Localization/StacksAndLocalization.lean`. -/

section TwoCategory

variable (U) (J : GrothendieckTopology 𝒞) (hU : Presheaf.IsSheaf J (yoneda.obj U))

include hU

/-- **Construction B of Stacks 04WV** on objects, for an arbitrary site: a pair `(𝒯, p)` of a stack
`𝒯` over `(𝒞, J)` and a 1-morphism `p : 𝒯 ⟶ 𝒞/U` of stacks over `𝒞` is sent to `p : 𝒯 ⥤ 𝒞/U`,
which is a stack over `(𝒞/U, J.over U)` by `CategoryTheory.Over.isStack_of_isStack_comp_forget`. -/
def stackPairToBasedStack (X : StackPair U J hU) :
    BasedStack.{v₁, v₁, max u₁ v₁, max u₁ v₁} (Over U) (J.over U) :=
  ⟨{ obj := X.1.toBasedCategory.obj, category := X.1.toBasedCategory.category,
      p := (X.2.hom.toFunctor : X.1.toBasedCategory.obj ⥤ Over U) },
    isStack_of_isStack_comp_forget (X.2.hom.toFunctor : X.1.toBasedCategory.obj ⥤ Over U) hU
      (by have h := X.1.isStack; rw [← X.2.hom.w] at h; exact h)⟩

/-- The round trip `A ∘ B`, with the data of a pair spelled out so that the equality
`G ⋙ j_U = q` can be substituted. -/
lemma stackConstructionA_stackPairToBasedStack_aux {X₀ : Type (max u₁ v₁)}
    [instX : Category.{v₁} X₀] (G : X₀ ⥤ Over U) (q : X₀ ⥤ 𝒞) (hw : G ⋙ Over.forget U = q)
    (hq : q.IsStack J) (hmor : Functor.IsFibredOneMorphism q (Over.forget U) G) :
    stackConstructionA U J hU
        (stackPairToBasedStack U J hU ⟨⟨⟨X₀, instX, q⟩, hq⟩, ⟨⟨G, hw⟩, hmor⟩⟩) =
      ⟨⟨⟨X₀, instX, q⟩, hq⟩, ⟨⟨G, hw⟩, hmor⟩⟩ := by
  subst hw
  rfl

/-- **Constructions A and B of Stacks 04WV are mutually inverse on objects**, for an arbitrary site
`(𝒞, J)` and an object `U` whose representable presheaf is a sheaf. A pair `(𝒯, p)` carries no
information beyond `p`, because "`p` is a 1-morphism of categories over `𝒞`" says exactly that the
structure functor of `𝒯` is `p ⋙ j_U`; and the two stack conditions agree, by
`CategoryTheory.Functor.isStack_comp_forget` in one direction and
`CategoryTheory.Over.isStack_of_isStack_comp_forget` in the other.

Together with `CategoryTheory.Over.stackConstructionHomEquiv` and
`CategoryTheory.Over.stackConstructionHom₂Equiv`, which are bijections on 1-morphisms and on
2-morphisms compatible with identities, composition and whiskering, this exhibits Constructions A
and B as mutually inverse functors of the two 2-categories. -/
@[stacks 04WV]
def basedStackEquivStackPair :
    BasedStack.{v₁, v₁, max u₁ v₁, max u₁ v₁} (Over U) (J.over U) ≃ StackPair U J hU where
  toFun := stackConstructionA U J hU
  invFun := stackPairToBasedStack U J hU
  left_inv _ := rfl
  right_inv X :=
    stackConstructionA_stackPairToBasedStack_aux U J hU
      (X.2.hom.toFunctor : X.1.toBasedCategory.obj ⥤ Over U) X.1.toBasedCategory.p X.2.hom.w
      X.1.isStack X.2.isFibredOneMorphism

end TwoCategory

end Over

end CategoryTheory
