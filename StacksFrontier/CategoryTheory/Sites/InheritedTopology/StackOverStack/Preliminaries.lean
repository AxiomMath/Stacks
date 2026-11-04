module

public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Defs
public import StacksFrontier.CategoryTheory.FibredOneMorphism
public import StacksFrontier.CategoryTheory.FiberedCategory.CompFibered
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Comp
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Fibrewise
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.MorGluing
public import StacksFrontier.CategoryTheory.Sites.Stack.FibredOneMorphismPullback

/-!
# A stack over a stack: preliminaries

Auxiliary results for Stacks 09WX (a stack over a stack is a stack over the base), proved in
`StacksFrontier.CategoryTheory.Sites.InheritedTopology.StackOverStack.IsStack`: strongly cartesian
morphisms for a composite `q ⋙ p` of fibred categories, the fact that `q` is a 1-morphism of fibred
categories from `q ⋙ p` to `p`, the transfer of `J`-covering sieves of `𝒞` to covering sieves of
a topology `J𝒳` of `𝒳` inherited from `(𝒞, J)` (Stacks 06NV), a sheaf criterion for a presheaf
of types with a natural family of functions to a sheaf, and the Stacks 042V comparison of
morphism presheaves along a 1-morphism of fibred categories.

## References

* [Stacks 09WX](https://stacks.math.columbia.edu/tag/09WX)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Functor

universe v₁ v₂ v₃ u₁ u₂ u₃ ua ub va vb

section Prelude

set_option backward.isDefEq.respectTransparency false
variable {𝒞 : Type u₁} {𝒳 : Type u₂} {𝒴 : Type u₃} [Category.{v₁} 𝒞] [Category.{v₂} 𝒳]
  [Category.{v₃} 𝒴]

/-- Every morphism into `p.obj a` has a strongly cartesian lift into `a`. -/
private lemma exists_isStronglyCartesian_isHomLift (p : 𝒳 ⥤ 𝒞) [p.IsFibered] {a : 𝒳} {V : 𝒞}
    (f : V ⟶ p.obj a) : ∃ (c : 𝒳) (h : c ⟶ a), p.IsStronglyCartesian f h ∧ p.IsHomLift f h := by
  obtain ⟨c, h, hc⟩ := IsPreFibered.exists_isCartesian' (p := p) (a := a) f
  have : p.IsCartesian f h := hc
  exact ⟨c, h, inferInstance, inferInstance⟩

/-- A `(q ⋙ p)`-strongly cartesian morphism has `p`-strongly cartesian `q`-image, and is itself
`q`-strongly cartesian over that image. -/
lemma comp_cart (p : 𝒳 ⥤ 𝒞) (q : 𝒴 ⥤ 𝒳) [p.IsFibered] [q.IsFibered] {U V : 𝒞} (f : V ⟶ U)
    {y' y : 𝒴} (θ : y' ⟶ y) [(q ⋙ p).IsStronglyCartesian f θ] :
    p.IsStronglyCartesian f (q.map θ) ∧ q.IsStronglyCartesian (q.map θ) θ := by
  subst_hom_lift(q ⋙ p)f θ
  obtain ⟨b, φ, _, _⟩ := exists_isStronglyCartesian_isHomLift p ((q ⋙ p).map θ)
  obtain ⟨y₀, θ₀, _, _⟩ := exists_isStronglyCartesian_isHomLift q φ
  obtain rfl : q.obj y₀ = b := IsHomLift.domain_eq q φ θ₀
  obtain rfl : φ = q.map θ₀ := IsHomLift.eq_of_isHomLift q φ θ₀
  have : (q ⋙ p).IsStronglyCartesian ((q ⋙ p).map θ) θ₀ :=
    IsStronglyCartesian.comp_functor q p ((q ⋙ p).map θ) (q.map θ₀) θ₀
  obtain ⟨α, hαlift, hα⟩ :
    ∃ α : y' ≅ y₀, (q ⋙ p).IsHomLift (𝟙 (p.obj (q.obj y'))) α.hom ∧ α.hom ≫ θ₀ = θ :=
    ⟨IsCartesian.domainUniqueUpToIso (q ⋙ p) ((q ⋙ p).map θ) θ₀ θ,
      IsCartesian.domainUniqueUpToIso_inv_isHomLift (q ⋙ p) ((q ⋙ p).map θ) θ₀ θ,
      IsCartesian.fac (q ⋙ p) ((q ⋙ p).map θ) θ₀ θ⟩
  have hqα : q.map α.hom ≫ q.map θ₀ = q.map θ := by rw [← q.map_comp, hα]
  have : (q ⋙ p).IsHomLift (𝟙 (p.obj (q.obj y'))) α.hom := hαlift
  have : p.IsHomLift (𝟙 (p.obj (q.obj y'))) (q.map α.hom) :=
    IsHomLift.of_fac p (𝟙 (p.obj (q.obj y'))) (q.map α.hom)
      (IsHomLift.domain_eq (q ⋙ p) (𝟙 (p.obj (q.obj y'))) α.hom)
      (IsHomLift.codomain_eq (q ⋙ p) (𝟙 (p.obj (q.obj y'))) α.hom)
      (IsHomLift.fac (q ⋙ p) (𝟙 (p.obj (q.obj y'))) α.hom)
  constructor
  · have h1 :
      p.IsStronglyCartesian (𝟙 (p.obj (q.obj y')) ≫ (q ⋙ p).map θ) (q.map α.hom ≫ q.map θ₀) :=
      inferInstance
    rwa [Category.id_comp, hqα] at h1
  · have h2 : q.IsStronglyCartesian (q.map α.hom ≫ q.map θ₀) (α.hom ≫ θ₀) := inferInstance
    rwa [hqα, hα] at h2

/-- `q` is a 1-morphism of fibred categories from `q ⋙ p` to `p`. -/
lemma isFibredOneMorphism_comp (p : 𝒳 ⥤ 𝒞) (q : 𝒴 ⥤ 𝒳) [p.IsFibered] [q.IsFibered] :
    IsFibredOneMorphism (q ⋙ p) p q
    where
  comp_eq := rfl
  map_isStronglyCartesian := by
    intro _ _ f _ _ φ h
    have := h
    exact (comp_cart p q f φ).1

/-- A `J`-covering sieve of `p.obj a` pulls back to a `J𝒳`-covering sieve of `a`. -/
lemma sieve_transfer (p : 𝒳 ⥤ 𝒞) [p.IsFibered] {J : GrothendieckTopology 𝒞}
    {J𝒳 : GrothendieckTopology 𝒳} (hJ𝒳 : IsInheritedTopology.{max u₂ v₂} p J J𝒳) (a : 𝒳)
    (R : Sieve (p.obj a)) (hR : R ∈ J (p.obj a)) : R.functorPullback p ∈ J𝒳 a := by
  let I : Type (max u₂ v₂) :=
    Σ c : 𝒳, { h : c ⟶ a // p.IsStronglyCartesian (p.map h) h ∧ R.arrows (p.map h) }
  let Y' : I → 𝒳 := fun i => i.1
  let g : ∀ i, Y' i ⟶ a := fun i => i.2.1
  have hgc : ∀ i, p.IsStronglyCartesian (p.map (g i)) (g i) := fun i => i.2.2.1
  have himg : Sieve.ofArrows (fun i => p.obj (Y' i)) (fun i => p.map (g i)) = R := by
    apply le_antisymm
    · rw [Sieve.generate_le_iff]
      rintro W u ⟨i⟩
      exact i.2.2.2
    · intro V f hf
      obtain ⟨c, h, _, _⟩ := exists_isStronglyCartesian_isHomLift p f
      obtain rfl : p.obj c = V := IsHomLift.domain_eq p f h
      obtain rfl : f = p.map h := IsHomLift.eq_of_isHomLift p f h
      exact Sieve.ofArrows_mk _ _ (⟨c, h, inferInstance, hf⟩ : I)
  refine J𝒳.superset_covering ?_ ((hJ𝒳 Y' g hgc).2 (by rwa [himg]))
  rw [Sieve.generate_le_iff]
  rintro W u ⟨i⟩
  exact i.2.2.2

/-- For `a` over `V` and `R` a `J`-covering sieve of `V`, the sieve of morphisms of `𝒳` into `a`
whose image lies in `R` is `J𝒳`-covering. -/
lemma sieve_transfer' (p : 𝒳 ⥤ 𝒞) [p.IsFibered] {J : GrothendieckTopology 𝒞}
    {J𝒳 : GrothendieckTopology 𝒳} (hJ𝒳 : IsInheritedTopology.{max u₂ v₂} p J J𝒳) {a : 𝒳} {V : 𝒞}
    (hav : p.obj a = V) (R : Sieve V) (hR : R ∈ J V) :
    (R.pullback (eqToHom hav)).functorPullback p ∈ J𝒳 a :=
  sieve_transfer p hJ𝒳 a _ (J.pullback_stable (eqToHom hav) hR)

/-- A morphism lying over `f` into the target of a strongly cartesian lift of the same `f` factors
uniquely through that lift by a morphism lying over an identity. -/
lemma factor_over_cart (p : 𝒳 ⥤ 𝒞) {V U : 𝒞} (f : V ⟶ U) {b a c : 𝒳} (β : b ⟶ a)
    [p.IsStronglyCartesian f β] (h : c ⟶ a) [p.IsHomLift f h] :
    ∃! δ : c ⟶ b, p.IsHomLift (𝟙 V) δ ∧ δ ≫ β = h :=
  IsStronglyCartesian.universal_property p f β (𝟙 V) f (by simp) h

/-- The morphism induced between two strongly cartesian lifts whose base morphisms are composable
is itself strongly cartesian. -/
private lemma isStronglyCartesian_induced (p : 𝒳 ⥤ 𝒞) {W V U : 𝒞} (k : W ⟶ V) (f : V ⟶ U)
    {b a c : 𝒳} (β : b ⟶ a) [p.IsStronglyCartesian f β] (γ : c ⟶ a)
    [p.IsStronglyCartesian (k ≫ f) γ] (δ : c ⟶ b) [p.IsHomLift k δ] (hδ : δ ≫ β = γ) :
    p.IsStronglyCartesian k δ := by
  have : p.IsStronglyCartesian (k ≫ f) (δ ≫ β) := hδ ▸ inferInstance
  exact IsStronglyCartesian.of_comp p (f := k) (g := f) (φ := δ) (ψ := β)

section AbstractSheaf

universe w₁ w₂ vv uu

/-- A presheaf of types admitting a natural family of functions `Φ` to a sheaf, possibly valued in
a different type universe, is itself a sheaf as soon as, over every covering sieve, every
compatible family together with an amalgamation of its image under `Φ` has a unique amalgamation
lying over that one. -/
lemma isSheaf_of_natFam {D : Type uu} [Category.{vv} D] (K : GrothendieckTopology D)
    {F : Dᵒᵖ ⥤ Type w₁} {G : Dᵒᵖ ⥤ Type w₂} (Φ : ∀ d : Dᵒᵖ, F.obj d → G.obj d)
    (hΦ : ∀ {d d' : Dᵒᵖ} (h : d ⟶ d') (s : F.obj d), Φ d' (F.map h s) = G.map h (Φ d s))
    (hG : Presieve.IsSheaf K G)
    (H :
      ∀ ⦃d : D⦄ (S : Sieve d),
        S ∈ K d →
          ∀ (t : Presieve.FamilyOfElements F (S : Presieve d)),
            t.Compatible →
              ∀ ψ : G.obj (Opposite.op d),
                Presieve.FamilyOfElements.IsAmalgamation
                    (fun _ f hf => Φ _ (t f hf) : Presieve.FamilyOfElements G (S : Presieve d)) ψ →
                  ∃! s : F.obj (Opposite.op d), Φ (Opposite.op d) s = ψ ∧ t.IsAmalgamation s) :
    Presieve.IsSheaf K F := by
  intro d S hS t ht
  have ht'c :
    Presieve.FamilyOfElements.Compatible
      (fun _ f hf => Φ _ (t f hf) : Presieve.FamilyOfElements G (S : Presieve d)) := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ hcomm
    rw [← hΦ g₁.op (t f₁ h₁), ← hΦ g₂.op (t f₂ h₂), ht g₁ g₂ h₁ h₂ hcomm]
  obtain ⟨ψ, hψ, -⟩ := hG S hS _ ht'c
  obtain ⟨s, ⟨hsΦ, hs⟩, -⟩ := H S hS t ht ψ hψ
  refine ⟨s, hs, fun s' hs' => ?_⟩
  have hpush :
    Presieve.FamilyOfElements.IsAmalgamation
      (fun _ f hf => Φ _ (t f hf) : Presieve.FamilyOfElements G (S : Presieve d))
      (Φ (Opposite.op d) s') := by
    intro Y f hf
    rw [← hΦ f.op s', hs' f hf]
  have h2 : Φ (Opposite.op d) s' = ψ := (hG S hS _ ht'c).unique hpush hψ
  exact (H S hS t ht ψ hψ).unique ⟨h2, hs'⟩ ⟨hsΦ, hs⟩

end AbstractSheaf

section Comparison

variable {𝒜 : Type ua} [Category.{va} 𝒜] {ℬ : Type ub} [Category.{vb} ℬ]
variable {pA : 𝒜 ⥤ 𝒞} {pB : ℬ ⥤ 𝒞} {G : 𝒜 ⥤ ℬ} [pA.IsFibered] [pB.IsFibered]

/-- The Stacks 042V comparison of morphism presheaves along a 1-morphism of fibred categories, as a
natural family of functions between presheaves valued in `Type va` and in `Type vb`. -/
noncomputable def phiFun (hF1 : IsFibredOneMorphism pA pB G) {U : 𝒞} (x y : pA.Fiber U)
    (g : Over U) (m : pullbackFiber pA x g.hom ⟶ pullbackFiber pA y g.hom) :
    pullbackFiber pB ((Fiber.mapOfComp pA pB G hF1.comp_eq U).obj x) g.hom ⟶
      pullbackFiber pB ((Fiber.mapOfComp pA pB G hF1.comp_eq U).obj y) g.hom :=
  (mapPbIso hF1 x g.hom).hom ≫
    (Fiber.mapOfComp pA pB G hF1.comp_eq g.left).map m ≫ (mapPbIso hF1 y g.hom).inv

/-- `phiFun` commutes with the restriction maps of the two morphism presheaves. -/
lemma phiFun_naturality (hF1 : IsFibredOneMorphism pA pB G) {U : 𝒞} (x y : pA.Fiber U)
    {g₁ g₂ : Over U} (h : g₁ ⟶ g₂) (m : pullbackFiber pA x g₂.hom ⟶ pullbackFiber pA y g₂.hom) :
    phiFun hF1 x y g₁ (morRestrict pA x y h m) =
      morRestrict pB ((Fiber.mapOfComp pA pB G hF1.comp_eq U).obj x)
        ((Fiber.mapOfComp pA pB G hF1.comp_eq U).obj y) h (phiFun hF1 x y g₂ m) := by
  refine morRestrict_uniq pB _ _ h _ _ ?_
  simp only [phiFun, Functor.map_comp, Category.assoc, mapPbIso_inv_fac,
    Fiber.fiberInclusion_map_mapOfComp_map]
  rw [← Functor.map_comp, morRestrict_fac, Functor.map_comp, Functor.map_comp, ←
    pullbackFiberMap_mapPbIso_hom_assoc hF1 x h]

end Comparison

end Prelude

end CategoryTheory.Functor
