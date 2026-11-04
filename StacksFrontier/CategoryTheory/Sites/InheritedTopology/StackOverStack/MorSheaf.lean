module

public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Defs
public import StacksFrontier.CategoryTheory.FibredOneMorphism
public import StacksFrontier.CategoryTheory.FiberedCategory.CompFibered
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Comp
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Fibrewise
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.MorGluing
public import StacksFrontier.CategoryTheory.Sites.Stack.FibredOneMorphismPullback
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.StackOverStack.Preliminaries

/-!
# A stack over a stack: morphism presheaves are sheaves

Let `p : 𝒳 ⥤ 𝒞` be a stack over the site `(𝒞, J)`, let `J𝒳` be a topology of `𝒳` inherited from
`(𝒞, J)` (Stacks 06NV) and let `q : 𝒴 ⥤ 𝒳` be a stack over `(𝒳, J𝒳)`. This file proves
condition (2) of Stacks 026F for `q ⋙ p`, the first half of Stacks 09WX: the presheaves of
morphisms between objects of the fibres of `q ⋙ p` are sheaves.

## Implementation notes

The inherited topology enters as the hypothesis
`CategoryTheory.Functor.IsInheritedTopology p J J𝒳` on a given topology of `𝒳`, rather than as the
construction `CategoryTheory.Functor.inheritedTopology` (Stacks 06NV), which is one such topology.

The universe of the index types of `IsInheritedTopology` is fixed to `max u₂ v₂`, the universe in
which the family of all arrows of a sieve on `𝒳` lives.

## References

* [Stacks 09WX](https://stacks.math.columbia.edu/tag/09WX)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Functor

universe v₁ v₂ v₃ u₁ u₂ u₃ ua ub va vb

variable {𝒞 : Type u₁} {𝒳 : Type u₂} {𝒴 : Type u₃} [Category.{v₁} 𝒞] [Category.{v₂} 𝒳]
  [Category.{v₃} 𝒴] {p : 𝒳 ⥤ 𝒞} {q : 𝒴 ⥤ 𝒳} {J : GrothendieckTopology 𝒞}
  {J𝒳 : GrothendieckTopology 𝒳}

section CondTwo

set_option backward.isDefEq.respectTransparency false
variable {𝒞 : Type u₁} {𝒳 : Type u₂} {𝒴 : Type u₃} [Category.{v₁} 𝒞] [Category.{v₂} 𝒳]
  [Category.{v₃} 𝒴]

/-- A morphism of `𝒴` lying over a morphism of `𝒳` which in turn lies over a morphism of `𝒞` lies
over the latter for the composite functor. -/
private lemma c2_isHomLift_comp (p : 𝒳 ⥤ 𝒞) (q : 𝒴 ⥤ 𝒳) {c d : 𝒳} (h : c ⟶ d) {a b : 𝒴} (φ : a ⟶ b)
    [q.IsHomLift h φ] {V W : 𝒞} (f : V ⟶ W) [p.IsHomLift f h] : (q ⋙ p).IsHomLift f φ := by
  subst_hom_lift q h φ
  exact
    IsHomLift.of_fac' (q ⋙ p) f φ (IsHomLift.domain_eq p f (q.map φ))
      (IsHomLift.codomain_eq p f (q.map φ)) (IsHomLift.fac' p f (q.map φ))

universe w1 w2

/-- `IsStronglyCartesian` is stable under postcomposing the base morphism with an `eqToHom`. -/
private lemma c2_sc_of_eq {𝒜 : Type w1} [Category.{w2} 𝒜] (r : 𝒜 ⥤ 𝒞) {R T T' : 𝒞} {a b : 𝒜}
    (f : R ⟶ T) (φ : a ⟶ b) [r.IsStronglyCartesian f φ] (hT : T = T') :
    r.IsStronglyCartesian (f ≫ eqToHom hT) φ := by
  subst hT
  simpa using (inferInstance : r.IsStronglyCartesian f φ)

/-- The member of the slice `𝒞/U` over `g` attached to `f : W ⟶ g.left`. -/
private def c2_mem {U : 𝒞} (g : Over U) {W : 𝒞} (f : W ⟶ g.left) :
    (Over.mk (f ≫ g.hom) : Over U) ⟶ g :=
  Over.homMk f

@[simp]
private lemma c2_mem_left {U : 𝒞} (g : Over U) {W : 𝒞} (f : W ⟶ g.left) : (c2_mem g f).left = f :=
  rfl

/-- The morphism of `𝒞/U` from `Over.mk (fb ≫ g.hom)` to `Over.mk (fh ≫ g.hom)` determined by a
factorization `u ≫ fh = fb`. -/
private def c2_over (p : 𝒳 ⥤ 𝒞) {U : 𝒞} (g : Over U) {c c' : 𝒳} {fh : p.obj c ⟶ g.left}
    {fb : p.obj c' ⟶ g.left} (u : p.obj c' ⟶ p.obj c) (hu : u ≫ fh = fb) :
    (Over.mk (fb ≫ g.hom) : Over U) ⟶ Over.mk (fh ≫ g.hom) :=
  Over.homMk u
    (by simp [← hu])

@[simp]
private lemma c2_over_left (p : 𝒳 ⥤ 𝒞) {U : 𝒞} (g : Over U) {c c' : 𝒳} {fh : p.obj c ⟶ g.left}
    {fb : p.obj c' ⟶ g.left} (u : p.obj c' ⟶ p.obj c) (hu : u ≫ fh = fb) :
    (c2_over p g u hu).left = u :=
  rfl

/-- Restricting a section of `Mor(x, y)` along an isomorphism of `𝒞/U` is injective. -/
private lemma c2_morRestrict_inj (p : 𝒳 ⥤ 𝒞) (q : 𝒴 ⥤ 𝒳) [(q ⋙ p).IsFibered] {U : 𝒞}
    (a b : (q ⋙ p).Fiber U) {g₁ g₂ : Over U} (u : g₁ ⟶ g₂) [IsIso u]
    (m m' : pullbackFiber (q ⋙ p) a g₂.hom ⟶ pullbackFiber (q ⋙ p) b g₂.hom)
    (hmm : morRestrict (q ⋙ p) a b u m = morRestrict (q ⋙ p) a b u m') : m = m' := by
  have h1 :
    morRestrict (q ⋙ p) a b (CategoryTheory.inv u) (morRestrict (q ⋙ p) a b u m) =
      morRestrict (q ⋙ p) a b (CategoryTheory.inv u) (morRestrict (q ⋙ p) a b u m') := by
    rw [hmm]
  rwa [← morRestrict_comp, ← morRestrict_comp, IsIso.inv_hom_id, morRestrict_id,
    morRestrict_id] at h1

/-- The canonical comparison from the domain of a `(q ⋙ p)`-morphism `ξ` over `f` into `f₀^* x`
to the chosen `(q ⋙ p)`-pullback of `x` along `f ≫ f₀`. No cartesianness of `ξ` is needed. -/
private noncomputable def c2_nu (p : 𝒳 ⥤ 𝒞) (q : 𝒴 ⥤ 𝒳) [p.IsFibered] [q.IsFibered]
    [(q ⋙ p).IsFibered] {U : 𝒞} (x : (q ⋙ p).Fiber U) (g : Over U) {c : 𝒳} (f : p.obj c ⟶ g.left)
    {Xh : 𝒴} (ξ : Xh ⟶ (pullbackFiber (q ⋙ p) x g.hom).1) (hξ : (q ⋙ p).IsHomLift f ξ) :
    Xh ⟶ (pullbackFiber (q ⋙ p) x (f ≫ g.hom)).1 :=
  IsStronglyCartesian.map (q ⋙ p) (f ≫ g.hom) (IsPreFibered.pullbackMap x.2 (f ≫ g.hom)) (g :=
    𝟙 (p.obj c)) (Category.id_comp (f ≫ g.hom)).symm (ξ ≫ IsPreFibered.pullbackMap x.2 g.hom)

private lemma c2_nu_lift (p : 𝒳 ⥤ 𝒞) (q : 𝒴 ⥤ 𝒳) [p.IsFibered] [q.IsFibered] [(q ⋙ p).IsFibered]
    {U : 𝒞} (x : (q ⋙ p).Fiber U) (g : Over U) {c : 𝒳} (f : p.obj c ⟶ g.left) {Xh : 𝒴}
    (ξ : Xh ⟶ (pullbackFiber (q ⋙ p) x g.hom).1) (hξ : (q ⋙ p).IsHomLift f ξ) :
    (q ⋙ p).IsHomLift (𝟙 (p.obj c)) (c2_nu p q x g f ξ hξ) := by
  exact
    IsStronglyCartesian.map_isHomLift (q ⋙ p) (f ≫ g.hom)
      (IsPreFibered.pullbackMap x.2 (f ≫ g.hom)) (Category.id_comp (f ≫ g.hom)).symm
      (ξ ≫ IsPreFibered.pullbackMap x.2 g.hom)

@[reassoc]
private lemma c2_nu_fac (p : 𝒳 ⥤ 𝒞) (q : 𝒴 ⥤ 𝒳) [p.IsFibered] [q.IsFibered] [(q ⋙ p).IsFibered]
    {U : 𝒞} (x : (q ⋙ p).Fiber U) (g : Over U) {c : 𝒳} (f : p.obj c ⟶ g.left) {Xh : 𝒴}
    (ξ : Xh ⟶ (pullbackFiber (q ⋙ p) x g.hom).1) (hξ : (q ⋙ p).IsHomLift f ξ) :
    c2_nu p q x g f ξ hξ ≫ IsPreFibered.pullbackMap x.2 (f ≫ g.hom) =
      ξ ≫ IsPreFibered.pullbackMap x.2 g.hom := by
  exact
    IsStronglyCartesian.fac (q ⋙ p) (f ≫ g.hom) (IsPreFibered.pullbackMap x.2 (f ≫ g.hom))
      (Category.id_comp (f ≫ g.hom)).symm (ξ ≫ IsPreFibered.pullbackMap x.2 g.hom)

/-- `c2_nu` followed by the restriction map of the chosen pullbacks of `x` is `ξ` again. -/
@[reassoc]
private lemma c2_nu_comp (p : 𝒳 ⥤ 𝒞) (q : 𝒴 ⥤ 𝒳) [p.IsFibered] [q.IsFibered] [(q ⋙ p).IsFibered]
    {U : 𝒞} (x : (q ⋙ p).Fiber U) (g : Over U) {c : 𝒳} (f : p.obj c ⟶ g.left) {Xh : 𝒴}
    (ξ : Xh ⟶ (pullbackFiber (q ⋙ p) x g.hom).1) (hξ : (q ⋙ p).IsHomLift f ξ) :
    c2_nu p q x g f ξ hξ ≫ pullbackFiberMap (q ⋙ p) x (c2_mem g f) = ξ := by
  have hν := c2_nu_lift p q x g f ξ hξ
  have hpfm := pullbackFiberMap_isHomLift (q ⋙ p) x (c2_mem g f)
  simp only [c2_mem_left] at hpfm
  have hpfmfac := pullbackFiberMap_fac (q ⋙ p) x (c2_mem g f)
  simp only [Over.mk_hom] at hpfmfac
  have hl :
    (q ⋙ p).IsHomLift f (c2_nu p q x g f ξ hξ ≫ pullbackFiberMap (q ⋙ p) x (c2_mem g f)) :=
    inferInstance
  refine IsStronglyCartesian.ext (q ⋙ p) g.hom (IsPreFibered.pullbackMap x.2 g.hom) f ?_
  rw [Category.assoc, hpfmfac, c2_nu_fac]

/-- When `ξ` is itself `(q ⋙ p)`-strongly cartesian over `f`, `c2_nu` is an isomorphism. -/
private lemma c2_nu_isIso (p : 𝒳 ⥤ 𝒞) (q : 𝒴 ⥤ 𝒳) [p.IsFibered] [q.IsFibered] [(q ⋙ p).IsFibered]
    {U : 𝒞} (x : (q ⋙ p).Fiber U) (g : Over U) {c : 𝒳} (f : p.obj c ⟶ g.left) {Xh : 𝒴}
    (ξ : Xh ⟶ (pullbackFiber (q ⋙ p) x g.hom).1) (hξ : (q ⋙ p).IsHomLift f ξ)
    (hξc : (q ⋙ p).IsStronglyCartesian f ξ) : IsIso (c2_nu p q x g f ξ hξ) := by
  have := hξc
  have hν := c2_nu_lift p q x g f ξ hξ
  have hcart :
    (q ⋙ p).IsStronglyCartesian (𝟙 (p.obj c) ≫ (f ≫ g.hom))
      (c2_nu p q x g f ξ hξ ≫ IsPreFibered.pullbackMap x.2 (f ≫ g.hom)) := by
    rw [c2_nu_fac, Category.id_comp]
    infer_instance
  have hνc : (q ⋙ p).IsStronglyCartesian (𝟙 (p.obj c)) (c2_nu p q x g f ξ hξ) :=
    IsStronglyCartesian.of_comp (q ⋙ p) (f := 𝟙 (p.obj c)) (g := f ≫ g.hom) (φ :=
      c2_nu p q x g f ξ hξ) (ψ := IsPreFibered.pullbackMap x.2 (f ≫ g.hom))
  exact IsStronglyCartesian.isIso_of_base_isIso (q ⋙ p) (𝟙 (p.obj c)) _

/-- The local morphism attached to `ξ` and a section `τ` of `Mor(x, y)` over `f ≫ f₀`: the unique
morphism over `f` into `f₀^* y` whose composite with the chosen cartesian lift of `f₀` at `y` is
`ν` followed by `τ` followed by the chosen cartesian lift of `f ≫ f₀` at `y`. -/
private noncomputable def c2_sigma (p : 𝒳 ⥤ 𝒞) (q : 𝒴 ⥤ 𝒳) [p.IsFibered] [q.IsFibered]
    [(q ⋙ p).IsFibered] {U : 𝒞} (x y : (q ⋙ p).Fiber U) (g : Over U) {c : 𝒳} (f : p.obj c ⟶ g.left)
    {Xh : 𝒴} (ξ : Xh ⟶ (pullbackFiber (q ⋙ p) x g.hom).1) (hξ : (q ⋙ p).IsHomLift f ξ)
    (τ : pullbackFiber (q ⋙ p) x (f ≫ g.hom) ⟶ pullbackFiber (q ⋙ p) y (f ≫ g.hom)) :
    Xh ⟶ (pullbackFiber (q ⋙ p) y g.hom).1 :=
  have := c2_nu_lift p q x g f ξ hξ
  IsStronglyCartesian.map (q ⋙ p) g.hom (IsPreFibered.pullbackMap y.2 g.hom) (g := f) rfl
    (c2_nu p q x g f ξ hξ ≫ Fiber.fiberInclusion.map τ ≫ IsPreFibered.pullbackMap y.2 (f ≫ g.hom))

private lemma c2_sigma_lift (p : 𝒳 ⥤ 𝒞) (q : 𝒴 ⥤ 𝒳) [p.IsFibered] [q.IsFibered] [(q ⋙ p).IsFibered]
    {U : 𝒞} (x y : (q ⋙ p).Fiber U) (g : Over U) {c : 𝒳} (f : p.obj c ⟶ g.left) {Xh : 𝒴}
    (ξ : Xh ⟶ (pullbackFiber (q ⋙ p) x g.hom).1) (hξ : (q ⋙ p).IsHomLift f ξ)
    (τ : pullbackFiber (q ⋙ p) x (f ≫ g.hom) ⟶ pullbackFiber (q ⋙ p) y (f ≫ g.hom)) :
    (q ⋙ p).IsHomLift f (c2_sigma p q x y g f ξ hξ τ) := by
  have := c2_nu_lift p q x g f ξ hξ
  exact
    IsStronglyCartesian.map_isHomLift (q ⋙ p) g.hom (IsPreFibered.pullbackMap y.2 g.hom) (g := f)
      rfl _

@[reassoc]
private lemma c2_sigma_fac (p : 𝒳 ⥤ 𝒞) (q : 𝒴 ⥤ 𝒳) [p.IsFibered] [q.IsFibered] [(q ⋙ p).IsFibered]
    {U : 𝒞} (x y : (q ⋙ p).Fiber U) (g : Over U) {c : 𝒳} (f : p.obj c ⟶ g.left) {Xh : 𝒴}
    (ξ : Xh ⟶ (pullbackFiber (q ⋙ p) x g.hom).1) (hξ : (q ⋙ p).IsHomLift f ξ)
    (τ : pullbackFiber (q ⋙ p) x (f ≫ g.hom) ⟶ pullbackFiber (q ⋙ p) y (f ≫ g.hom)) :
    c2_sigma p q x y g f ξ hξ τ ≫ IsPreFibered.pullbackMap y.2 g.hom =
      c2_nu p q x g f ξ hξ ≫
        Fiber.fiberInclusion.map τ ≫ IsPreFibered.pullbackMap y.2 (f ≫ g.hom) := by
  have := c2_nu_lift p q x g f ξ hξ
  exact IsStronglyCartesian.fac (q ⋙ p) g.hom (IsPreFibered.pullbackMap y.2 g.hom) (g := f) rfl _

private lemma c2_sigma_q (p : 𝒳 ⥤ 𝒞) (q : 𝒴 ⥤ 𝒳) [p.IsFibered] [q.IsFibered] [(q ⋙ p).IsFibered]
    (hF1 : IsFibredOneMorphism (q ⋙ p) p q) {U : 𝒞} (x y : (q ⋙ p).Fiber U) (g : Over U) {c : 𝒳}
    (f : p.obj c ⟶ g.left) (h : c ⟶ q.obj (pullbackFiber (q ⋙ p) x g.hom).1) [p.IsHomLift f h]
    {Xh : 𝒴} (ξ : Xh ⟶ (pullbackFiber (q ⋙ p) x g.hom).1) [q.IsHomLift h ξ]
    (τ : pullbackFiber (q ⋙ p) x (f ≫ g.hom) ⟶ pullbackFiber (q ⋙ p) y (f ≫ g.hom))
    (ψ :
      pullbackFiber p ((Fiber.mapOfComp (q ⋙ p) p q hF1.comp_eq U).obj x) g.hom ⟶
        pullbackFiber p ((Fiber.mapOfComp (q ⋙ p) p q hF1.comp_eq U).obj y) g.hom)
    (hcompat :
      morRestrict p ((Fiber.mapOfComp (q ⋙ p) p q hF1.comp_eq U).obj x)
          ((Fiber.mapOfComp (q ⋙ p) p q hF1.comp_eq U).obj y) (c2_mem g f) ψ =
        phiFun hF1 x y (Over.mk (f ≫ g.hom)) τ) :
    q.IsHomLift
      (h ≫ Fiber.fiberInclusion.map ((mapPbIso hF1 x g.hom).inv ≫ ψ ≫ (mapPbIso hF1 y g.hom).hom))
      (c2_sigma p q x y g f ξ (c2_isHomLift_comp p q h ξ f) τ) := by
  have hξ : (q ⋙ p).IsHomLift f ξ := c2_isHomLift_comp p q h ξ f
  have hν : (q ⋙ p).IsHomLift (𝟙 (p.obj c)) (c2_nu p q x g f ξ hξ) := c2_nu_lift p q x g f ξ hξ
  have hσ : (q ⋙ p).IsHomLift f (c2_sigma p q x y g f ξ hξ τ) := c2_sigma_lift p q x y g f ξ hξ τ
  have ha : q.obj Xh = c := IsHomLift.domain_eq q h ξ
  have hqξ : q.map ξ = eqToHom ha ≫ h := by simpa using IsHomLift.fac' q h ξ
  have hkey :
    (q.map (c2_nu p q x g f ξ hξ) ≫ Fiber.fiberInclusion.map (mapPbIso hF1 x (f ≫ g.hom)).inv) ≫
        pullbackFiberMap p ((Fiber.mapOfComp (q ⋙ p) p q hF1.comp_eq U).obj x) (c2_mem g f) =
      eqToHom ha ≫ h ≫ Fiber.fiberInclusion.map (mapPbIso hF1 x g.hom).inv := by
    have hl1 :
      p.IsHomLift f
        ((q.map (c2_nu p q x g f ξ hξ) ≫
            Fiber.fiberInclusion.map (mapPbIso hF1 x (f ≫ g.hom)).inv) ≫
          pullbackFiberMap p ((Fiber.mapOfComp (q ⋙ p) p q hF1.comp_eq U).obj x)
            (c2_mem g f)) := by
      have hn : p.IsHomLift (𝟙 (p.obj c)) (q.map (c2_nu p q x g f ξ hξ)) :=
        hF1.map_isHomLift (𝟙 (p.obj c)) _
      have hm :=
        pullbackFiberMap_isHomLift p ((Fiber.mapOfComp (q ⋙ p) p q hF1.comp_eq U).obj x)
          (c2_mem g f)
      simp only [c2_mem_left] at hm
      infer_instance
    refine
      IsStronglyCartesian.ext p g.hom
        (IsPreFibered.pullbackMap ((Fiber.mapOfComp (q ⋙ p) p q hF1.comp_eq U).obj x).2 g.hom) f ?_
    simp only [Category.assoc, pullbackFiberMap_fac, Over.mk_hom, mapPbIso_inv_fac]
    rw [← Functor.map_comp, c2_nu_fac, Functor.map_comp]
    simp [Category.assoc, hqξ]
  have hstar :=
    morRestrict_fac p ((Fiber.mapOfComp (q ⋙ p) p q hF1.comp_eq U).obj x)
      ((Fiber.mapOfComp (q ⋙ p) p q hF1.comp_eq U).obj y) (c2_mem g f) ψ
  rw [hcompat] at hstar
  simp only [phiFun, Functor.map_comp, Category.assoc, Over.mk_hom,
    Fiber.fiberInclusion_map_mapOfComp_map, mapPbIso_inv_fac] at hstar
  have hcancel :
    q.map (c2_nu p q x g f ξ hξ) =
      (q.map (c2_nu p q x g f ξ hξ) ≫ Fiber.fiberInclusion.map (mapPbIso hF1 x (f ≫ g.hom)).inv) ≫
        Fiber.fiberInclusion.map (mapPbIso hF1 x (f ≫ g.hom)).hom := by
    rw [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, Functor.map_id]
    exact (Category.comp_id _).symm
  refine IsHomLift.of_fac' q _ _ ha rfl ?_
  simp only [eqToHom_refl, Category.comp_id]
  have hey : p.IsStronglyCartesian g.hom (q.map (IsPreFibered.pullbackMap y.2 g.hom)) :=
    hF1.map_isStronglyCartesian g.hom _ inferInstance
  have hl1 : p.IsHomLift f (q.map (c2_sigma p q x y g f ξ hξ τ)) := hF1.map_isHomLift f _
  refine IsStronglyCartesian.ext p g.hom (q.map (IsPreFibered.pullbackMap y.2 g.hom)) f ?_
  rw [← Functor.map_comp, c2_sigma_fac]
  simp only [Functor.map_comp, Category.assoc, mapPbIso_hom_fac]
  rw [hcancel]
  simp only [Category.assoc]
  rw [hstar, reassoc_of% hkey]

/-- The section of `Mor(X_h, Z_h)` of `q` attached to `c2_sigma`, obtained from the universal
property of a `q`-strongly cartesian lift of `h ≫ ψ₁` at `f₀^* y`. -/
private noncomputable def c2_theta (p : 𝒳 ⥤ 𝒞) (q : 𝒴 ⥤ 𝒳) [p.IsFibered] [q.IsFibered]
    [(q ⋙ p).IsFibered] {U : 𝒞} (x y : (q ⋙ p).Fiber U) (g : Over U) {c : 𝒳} (f : p.obj c ⟶ g.left)
    {Xh : 𝒴} (ξ : Xh ⟶ (pullbackFiber (q ⋙ p) x g.hom).1) (hξ : (q ⋙ p).IsHomLift f ξ)
    (τ : pullbackFiber (q ⋙ p) x (f ≫ g.hom) ⟶ pullbackFiber (q ⋙ p) y (f ≫ g.hom))
    {b : c ⟶ q.obj (pullbackFiber (q ⋙ p) y g.hom).1} {Zh : 𝒴}
    (ϖ : Zh ⟶ (pullbackFiber (q ⋙ p) y g.hom).1) [q.IsStronglyCartesian b ϖ]
    (hqσ : q.IsHomLift b (c2_sigma p q x y g f ξ hξ τ)) : Xh ⟶ Zh :=
  IsStronglyCartesian.map q b ϖ (g := 𝟙 c) (Category.id_comp b).symm (c2_sigma p q x y g f ξ hξ τ)

private lemma c2_theta_lift (p : 𝒳 ⥤ 𝒞) (q : 𝒴 ⥤ 𝒳) [p.IsFibered] [q.IsFibered] [(q ⋙ p).IsFibered]
    {U : 𝒞} (x y : (q ⋙ p).Fiber U) (g : Over U) {c : 𝒳} (f : p.obj c ⟶ g.left) {Xh : 𝒴}
    (ξ : Xh ⟶ (pullbackFiber (q ⋙ p) x g.hom).1) (hξ : (q ⋙ p).IsHomLift f ξ)
    (τ : pullbackFiber (q ⋙ p) x (f ≫ g.hom) ⟶ pullbackFiber (q ⋙ p) y (f ≫ g.hom))
    {b : c ⟶ q.obj (pullbackFiber (q ⋙ p) y g.hom).1} {Zh : 𝒴}
    (ϖ : Zh ⟶ (pullbackFiber (q ⋙ p) y g.hom).1) [q.IsStronglyCartesian b ϖ]
    (hqσ : q.IsHomLift b (c2_sigma p q x y g f ξ hξ τ)) :
    q.IsHomLift (𝟙 c) (c2_theta p q x y g f ξ hξ τ ϖ hqσ) :=
  IsStronglyCartesian.map_isHomLift q b ϖ (Category.id_comp b).symm (c2_sigma p q x y g f ξ hξ τ)

@[reassoc]
private lemma c2_theta_fac (p : 𝒳 ⥤ 𝒞) (q : 𝒴 ⥤ 𝒳) [p.IsFibered] [q.IsFibered] [(q ⋙ p).IsFibered]
    {U : 𝒞} (x y : (q ⋙ p).Fiber U) (g : Over U) {c : 𝒳} (f : p.obj c ⟶ g.left) {Xh : 𝒴}
    (ξ : Xh ⟶ (pullbackFiber (q ⋙ p) x g.hom).1) (hξ : (q ⋙ p).IsHomLift f ξ)
    (τ : pullbackFiber (q ⋙ p) x (f ≫ g.hom) ⟶ pullbackFiber (q ⋙ p) y (f ≫ g.hom))
    {b : c ⟶ q.obj (pullbackFiber (q ⋙ p) y g.hom).1} {Zh : 𝒴}
    (ϖ : Zh ⟶ (pullbackFiber (q ⋙ p) y g.hom).1) [q.IsStronglyCartesian b ϖ]
    (hqσ : q.IsHomLift b (c2_sigma p q x y g f ξ hξ τ)) :
    c2_theta p q x y g f ξ hξ τ ϖ hqσ ≫ ϖ = c2_sigma p q x y g f ξ hξ τ :=
  IsStronglyCartesian.fac q b ϖ (Category.id_comp b).symm (c2_sigma p q x y g f ξ hξ τ)

private lemma c2_theta_uniq (p : 𝒳 ⥤ 𝒞) (q : 𝒴 ⥤ 𝒳) [p.IsFibered] [q.IsFibered] [(q ⋙ p).IsFibered]
    {U : 𝒞} (x y : (q ⋙ p).Fiber U) (g : Over U) {c : 𝒳} (f : p.obj c ⟶ g.left) {Xh : 𝒴}
    (ξ : Xh ⟶ (pullbackFiber (q ⋙ p) x g.hom).1) (hξ : (q ⋙ p).IsHomLift f ξ)
    (τ : pullbackFiber (q ⋙ p) x (f ≫ g.hom) ⟶ pullbackFiber (q ⋙ p) y (f ≫ g.hom))
    {b : c ⟶ q.obj (pullbackFiber (q ⋙ p) y g.hom).1} {Zh : 𝒴}
    (ϖ : Zh ⟶ (pullbackFiber (q ⋙ p) y g.hom).1) [q.IsStronglyCartesian b ϖ]
    (hqσ : q.IsHomLift b (c2_sigma p q x y g f ξ hξ τ)) (w : Xh ⟶ Zh) (hw : q.IsHomLift (𝟙 c) w)
    (hwfac : w ≫ ϖ = c2_sigma p q x y g f ξ hξ τ) : w = c2_theta p q x y g f ξ hξ τ ϖ hqσ :=
  IsStronglyCartesian.map_uniq q b ϖ (Category.id_comp b).symm (c2_sigma p q x y g f ξ hξ τ) w
    hwfac

/-- `c2_theta` read as a morphism of the fibre of `q` over `c`. -/
private noncomputable def c2_thetaF (p : 𝒳 ⥤ 𝒞) (q : 𝒴 ⥤ 𝒳) [p.IsFibered] [q.IsFibered]
    [(q ⋙ p).IsFibered] {U : 𝒞} (x y : (q ⋙ p).Fiber U) (g : Over U) {c : 𝒳} (f : p.obj c ⟶ g.left)
    {Xh Zh : q.Fiber c} (ξ : Xh.1 ⟶ (pullbackFiber (q ⋙ p) x g.hom).1) (hξ : (q ⋙ p).IsHomLift f ξ)
    (τ : pullbackFiber (q ⋙ p) x (f ≫ g.hom) ⟶ pullbackFiber (q ⋙ p) y (f ≫ g.hom))
    {b : c ⟶ q.obj (pullbackFiber (q ⋙ p) y g.hom).1}
    (ϖ : Zh.1 ⟶ (pullbackFiber (q ⋙ p) y g.hom).1) [q.IsStronglyCartesian b ϖ]
    (hqσ : q.IsHomLift b (c2_sigma p q x y g f ξ hξ τ)) : Xh ⟶ Zh :=
  ⟨c2_theta p q x y g f ξ hξ τ ϖ hqσ, c2_theta_lift p q x y g f ξ hξ τ ϖ hqσ⟩

@[simp]
private lemma c2_thetaF_val (p : 𝒳 ⥤ 𝒞) (q : 𝒴 ⥤ 𝒳) [p.IsFibered] [q.IsFibered] [(q ⋙ p).IsFibered]
    {U : 𝒞} (x y : (q ⋙ p).Fiber U) (g : Over U) {c : 𝒳} (f : p.obj c ⟶ g.left) {Xh Zh : q.Fiber c}
    (ξ : Xh.1 ⟶ (pullbackFiber (q ⋙ p) x g.hom).1) (hξ : (q ⋙ p).IsHomLift f ξ)
    (τ : pullbackFiber (q ⋙ p) x (f ≫ g.hom) ⟶ pullbackFiber (q ⋙ p) y (f ≫ g.hom))
    {b : c ⟶ q.obj (pullbackFiber (q ⋙ p) y g.hom).1}
    (ϖ : Zh.1 ⟶ (pullbackFiber (q ⋙ p) y g.hom).1) [q.IsStronglyCartesian b ϖ]
    (hqσ : q.IsHomLift b (c2_sigma p q x y g f ξ hξ τ)) :
    Fiber.fiberInclusion.map (c2_thetaF p q x y g f ξ hξ τ ϖ hqσ) =
      c2_theta p q x y g f ξ hξ τ ϖ hqσ :=
  rfl

/-- Base-change compatibility of `c2_sigma`: restricting the section along `u` and restricting the
lift `ξ` along a morphism `δ` over `u` give the same local morphism. -/
private lemma c2_sigma_restrict (p : 𝒳 ⥤ 𝒞) (q : 𝒴 ⥤ 𝒳) [p.IsFibered] [q.IsFibered]
    [(q ⋙ p).IsFibered] {U : 𝒞} (x y : (q ⋙ p).Fiber U) (g : Over U) {c c' : 𝒳}
    (fh : p.obj c ⟶ g.left) (fb : p.obj c' ⟶ g.left) (u : p.obj c' ⟶ p.obj c) (hu : u ≫ fh = fb)
    {Xh Xb : 𝒴} (ξh : Xh ⟶ (pullbackFiber (q ⋙ p) x g.hom).1) (hξh : (q ⋙ p).IsHomLift fh ξh)
    (ξb : Xb ⟶ (pullbackFiber (q ⋙ p) x g.hom).1) (hξb : (q ⋙ p).IsHomLift fb ξb) (δ : Xb ⟶ Xh)
    (hδ : (q ⋙ p).IsHomLift u δ) (hδfac : δ ≫ ξh = ξb)
    (τh : pullbackFiber (q ⋙ p) x (fh ≫ g.hom) ⟶ pullbackFiber (q ⋙ p) y (fh ≫ g.hom))
    (τb : pullbackFiber (q ⋙ p) x (fb ≫ g.hom) ⟶ pullbackFiber (q ⋙ p) y (fb ≫ g.hom))
    (hτ : τb = morRestrict (q ⋙ p) x y (c2_over p g u hu) τh) :
    c2_sigma p q x y g fb ξb hξb τb = δ ≫ c2_sigma p q x y g fh ξh hξh τh := by
  have hνh : (q ⋙ p).IsHomLift (𝟙 (p.obj c)) (c2_nu p q x g fh ξh hξh) :=
    c2_nu_lift p q x g fh ξh hξh
  have hνb : (q ⋙ p).IsHomLift (𝟙 (p.obj c')) (c2_nu p q x g fb ξb hξb) :=
    c2_nu_lift p q x g fb ξb hξb
  have hσh : (q ⋙ p).IsHomLift fh (c2_sigma p q x y g fh ξh hξh τh) :=
    c2_sigma_lift p q x y g fh ξh hξh τh
  have hσb : (q ⋙ p).IsHomLift fb (c2_sigma p q x y g fb ξb hξb τb) :=
    c2_sigma_lift p q x y g fb ξb hξb τb
  have hpfm := pullbackFiberMap_isHomLift (q ⋙ p) x (c2_over p g u hu)
  simp only [c2_over_left] at hpfm
  have hνδ :
    δ ≫ c2_nu p q x g fh ξh hξh =
      c2_nu p q x g fb ξb hξb ≫ pullbackFiberMap (q ⋙ p) x (c2_over p g u hu) := by
    have hl : (q ⋙ p).IsHomLift u (δ ≫ c2_nu p q x g fh ξh hξh) := inferInstance
    have hr :
      (q ⋙ p).IsHomLift u
        (c2_nu p q x g fb ξb hξb ≫ pullbackFiberMap (q ⋙ p) x (c2_over p g u hu)) :=
      inferInstance
    have hpfmfac := pullbackFiberMap_fac (q ⋙ p) x (c2_over p g u hu)
    simp only [Over.mk_hom] at hpfmfac
    refine
      IsStronglyCartesian.ext (q ⋙ p) (fh ≫ g.hom) (IsPreFibered.pullbackMap x.2 (fh ≫ g.hom)) u ?_
    rw [Category.assoc, c2_nu_fac, reassoc_of% hδfac, Category.assoc, hpfmfac, c2_nu_fac]
  have hrhs : (q ⋙ p).IsHomLift fb (δ ≫ c2_sigma p q x y g fh ξh hξh τh) := by
    rw [← hu]; infer_instance
  have hmrfac := morRestrict_fac (q ⋙ p) x y (c2_over p g u hu) τh
  simp only [Over.mk_hom] at hmrfac
  refine IsStronglyCartesian.ext (q ⋙ p) g.hom (IsPreFibered.pullbackMap y.2 g.hom) fb ?_
  rw [c2_sigma_fac, Category.assoc, c2_sigma_fac, reassoc_of% hνδ, hτ, hmrfac]

/-- **Condition (2) of Stacks 026F for `q ⋙ p`.** Let `p : 𝒳 ⥤ 𝒞` be a stack over the site
`(𝒞, J)`, let `J𝒳` be a topology of `𝒳` inherited from `(𝒞, J)` and let `q : 𝒴 ⥤ 𝒳` be a stack
over `(𝒳, J𝒳)`. Then the presheaves of morphisms between objects of the fibres of `q ⋙ p` are
sheaves. -/
lemma comp_isMorSheaf (p : 𝒳 ⥤ 𝒞) (q : 𝒴 ⥤ 𝒳) {J : GrothendieckTopology 𝒞}
    {J𝒳 : GrothendieckTopology 𝒳} (hp : p.IsStack J) (hJ𝒳 : IsInheritedTopology.{max u₂ v₂} p J J𝒳)
    (hq : q.IsStack J𝒳) :
    haveI : p.IsFibered := hp.isFibered
    haveI : q.IsFibered := hq.isFibered
    haveI : (q ⋙ p).IsFibered := IsFibered.comp_functor q p
    ∀ (U : 𝒞) (x y : (q ⋙ p).Fiber U), IsMorSheaf (q ⋙ p) J U x y := by
  have hpf : p.IsFibered := hp.isFibered
  have hqf : q.IsFibered := hq.isFibered
  have hPf : (q ⋙ p).IsFibered := IsFibered.comp_functor q p
  have hF1 : IsFibredOneMorphism (q ⋙ p) p q := isFibredOneMorphism_comp p q
  intro U x y
  unfold IsMorSheaf
  rw [isSheaf_iff_isSheaf_of_type]
  refine
    isSheaf_of_natFam (J.over U) (G :=
      morPresheaf p ((Fiber.mapOfComp (q ⋙ p) p q hF1.comp_eq U).obj x)
        ((Fiber.mapOfComp (q ⋙ p) p q hF1.comp_eq U).obj y))
      (fun d m => phiFun hF1 x y d.unop m) ?_ ?_ ?_
  · intro d d' h s
    exact phiFun_naturality hF1 x y h.unop s
  · exact (isSheaf_iff_isSheaf_of_type _ _).1 (hp.isMorSheaf U _ _)
  · intro g S hS t ht ψ hψ
    set A := pullbackFiber (q ⋙ p) x g.hom with hAd
    set B := pullbackFiber (q ⋙ p) y g.hom with hBd
    have hav : p.obj (q.obj A.1) = g.left := A.2
    have hR : Sieve.overEquiv g S ∈ J g.left := (J.mem_over_iff S).1 hS
    have hT : ((Sieve.overEquiv g S).pullback (eqToHom hav)).functorPullback p ∈ J𝒳 (q.obj A.1) :=
      sieve_transfer' p hJ𝒳 hav _ hR
    set XF : q.Fiber (q.obj A.1) := Fiber.mk (rfl : q.obj A.1 = q.obj A.1) with hXFd
    set BF : q.Fiber (q.obj B.1) := Fiber.mk (rfl : q.obj B.1 = q.obj B.1) with hBFd
    set ψ₁ : q.obj A.1 ⟶ q.obj B.1 :=
      Fiber.fiberInclusion.map ((mapPbIso hF1 x g.hom).inv ≫ ψ ≫ (mapPbIso hF1 y g.hom).hom) with
      hψ₁d
    set ZF : q.Fiber (q.obj A.1) := pullbackFiber q BF ψ₁ with hZFd
    set ζ : ZF.1 ⟶ B.1 := IsPreFibered.pullbackMap BF.2 ψ₁ with hζd
    have hζc : q.IsStronglyCartesian ψ₁ ζ := inferInstance
    have htsc := (Presieve.compatible_iff_sieveCompatible t).1 ht
    have hsq :
      ∀ {c : 𝒳} (h : c ⟶ q.obj A.1)
        (hh : (((Sieve.overEquiv g S).pullback (eqToHom hav)).functorPullback p).arrows h),
        q.IsHomLift (h ≫ ψ₁)
          (c2_sigma p q x y g (p.map h ≫ eqToHom hav) (IsPreFibered.pullbackMap XF.2 h)
            (c2_isHomLift_comp p q h (IsPreFibered.pullbackMap XF.2 h) (p.map h ≫ eqToHom hav))
            (t (c2_mem g (p.map h ≫ eqToHom hav)) ((Sieve.overEquiv_iff S _).1 hh))) := by
      intro c h hh
      exact
        c2_sigma_q p q hF1 x y g (p.map h ≫ eqToHom hav) h (IsPreFibered.pullbackMap XF.2 h) _ ψ
          (hψ (c2_mem g (p.map h ≫ eqToHom hav)) ((Sieve.overEquiv_iff S _).1 hh))
    have hglue :=
      exists_fiberHom_of_locally q (hq.isMorSheaf _ XF ZF) hT
        (fun {c} h hh =>
          c2_thetaF p q x y g (p.map h ≫ eqToHom hav) (IsPreFibered.pullbackMap XF.2 h)
            (c2_isHomLift_comp p q h (IsPreFibered.pullbackMap XF.2 h) (p.map h ≫ eqToHom hav))
            (t (c2_mem g (p.map h ≫ eqToHom hav)) ((Sieve.overEquiv_iff S _).1 hh))
            (IsPreFibered.pullbackMap ZF.2 h ≫ ζ) (hsq h hh))
        (by
          intro cc cc' h hh γ b hb hb'
          have hu : p.map γ ≫ (p.map h ≫ eqToHom hav) = p.map b ≫ eqToHom hav := by
            rw [← Category.assoc, ← p.map_comp, hb]
          have hkh : S (c2_mem g (p.map h ≫ eqToHom hav)) := (Sieve.overEquiv_iff S _).1 hh
          have hkb : S (c2_mem g (p.map b ≫ eqToHom hav)) := (Sieve.overEquiv_iff S _).1 hb'
          have hkeq :
            c2_over p g (p.map γ) hu ≫ c2_mem g (p.map h ≫ eqToHom hav) =
              c2_mem g (p.map b ≫ eqToHom hav) := by
            apply Over.OverMorphism.ext
            simp only [Over.comp_left, c2_over_left, c2_mem_left]
            exact hu
          have hδq :
            q.IsHomLift γ
              (Fiber.fiberInclusion.map (pullbackFiberCompIso' XF h γ b hb).inv ≫
                IsPreFibered.pullbackMap (pullbackFiber q XF h).2 γ) := by
            infer_instance
          have hδ :
            (q ⋙ p).IsHomLift (p.map γ)
              (Fiber.fiberInclusion.map (pullbackFiberCompIso' XF h γ b hb).inv ≫
                IsPreFibered.pullbackMap (pullbackFiber q XF h).2 γ) :=
            c2_isHomLift_comp p q γ _ (p.map γ)
          have hδfac :
            (Fiber.fiberInclusion.map (pullbackFiberCompIso' XF h γ b hb).inv ≫
                  IsPreFibered.pullbackMap (pullbackFiber q XF h).2 γ) ≫
                IsPreFibered.pullbackMap XF.2 h =
              IsPreFibered.pullbackMap XF.2 b := by
            rw [Category.assoc]
            exact pullbackFiberCompIso'_inv_fac XF h γ b hb
          have hτ :
            t (c2_mem g (p.map b ≫ eqToHom hav)) hkb =
              morRestrict (q ⋙ p) x y (c2_over p g (p.map γ) hu)
                (t (c2_mem g (p.map h ≫ eqToHom hav)) hkh) := by
            revert hkb
            rw [← hkeq]
            intro hkb
            exact htsc (c2_mem g (p.map h ≫ eqToHom hav)) (c2_over p g (p.map γ) hu) hkh
          refine
            fiber_hom_ext_of_cartesian (b ≫ ψ₁) (IsPreFibered.pullbackMap ZF.2 b ≫ ζ) inferInstance
              _ _ ?_
          simp only [c2_thetaF_val, Functor.map_comp, Category.assoc,
            pullbackFiberCompIso'_hom_fac_assoc, pullbackFiberHom_fac_assoc, c2_theta_fac]
          rw [← Category.assoc]
          exact
            c2_sigma_restrict p q x y g (p.map h ≫ eqToHom hav) (p.map b ≫ eqToHom hav) (p.map γ)
              hu (IsPreFibered.pullbackMap XF.2 h) _ (IsPreFibered.pullbackMap XF.2 b) _ _ hδ hδfac
              _ _ hτ)
    obtain ⟨w, hw⟩ := hglue
    have hψ'lift : p.IsHomLift (𝟙 g.left) ψ₁ :=
      ((mapPbIso hF1 x g.hom).inv ≫ ψ ≫ (mapPbIso hF1 y g.hom).hom).2
    have hqw : q.IsHomLift (𝟙 (q.obj A.1)) (Fiber.fiberInclusion.map w) := w.2
    have hqwζ : q.IsHomLift ψ₁ (Fiber.fiberInclusion.map w ≫ ζ) := inferInstance
    have hslift : (q ⋙ p).IsHomLift (𝟙 g.left) (Fiber.fiberInclusion.map w ≫ ζ) :=
      c2_isHomLift_comp p q ψ₁ (Fiber.fiberInclusion.map w ≫ ζ) (𝟙 g.left)
    set s : A ⟶ B := ⟨Fiber.fiberInclusion.map w ≫ ζ, hslift⟩ with hsd
    have hsval : Fiber.fiberInclusion.map s = Fiber.fiberInclusion.map w ≫ ζ := rfl
    have hqs : q.map (Fiber.fiberInclusion.map s) = ψ₁ := by
      rw [hsval]
      exact (IsHomLift.eq_of_isHomLift q ψ₁ (Fiber.fiberInclusion.map w ≫ ζ)).symm
    have hdagger :
      ∀ {cc : 𝒳} (h : cc ⟶ q.obj A.1)
        (hh : (((Sieve.overEquiv g S).pullback (eqToHom hav)).functorPullback p).arrows h),
        IsPreFibered.pullbackMap XF.2 h ≫ Fiber.fiberInclusion.map s =
          c2_sigma p q x y g (p.map h ≫ eqToHom hav) (IsPreFibered.pullbackMap XF.2 h)
            (c2_isHomLift_comp p q h (IsPreFibered.pullbackMap XF.2 h) (p.map h ≫ eqToHom hav))
            (t (c2_mem g (p.map h ≫ eqToHom hav)) ((Sieve.overEquiv_iff S _).1 hh)) := by
      intro cc h hh
      have h2 := pullbackFiberHom_fac w h
      rw [hw h hh, c2_thetaF_val] at h2
      rw [hsval, ← Category.assoc, ← h2, Category.assoc]
      exact c2_theta_fac p q x y g _ _ _ _ _ (hsq h hh)
    have hA :
      ∀ (s₀ : A ⟶ B),
        (∀ ⦃Z : Over U⦄ (k : Z ⟶ g) (hk : S k), morRestrict (q ⋙ p) x y k s₀ = t k hk) →
          ∀ {cc : 𝒳} (h : cc ⟶ q.obj A.1)
            (hh : (((Sieve.overEquiv g S).pullback (eqToHom hav)).functorPullback p).arrows h),
            IsPreFibered.pullbackMap XF.2 h ≫ Fiber.fiberInclusion.map s₀ =
              c2_sigma p q x y g (p.map h ≫ eqToHom hav) (IsPreFibered.pullbackMap XF.2 h)
                (c2_isHomLift_comp p q h (IsPreFibered.pullbackMap XF.2 h) (p.map h ≫ eqToHom hav))
                (t (c2_mem g (p.map h ≫ eqToHom hav)) ((Sieve.overEquiv_iff S _).1 hh)) := by
      intro s₀ ha cc h hh
      have hξ : (q ⋙ p).IsHomLift (p.map h ≫ eqToHom hav) (IsPreFibered.pullbackMap XF.2 h) :=
        c2_isHomLift_comp p q h (IsPreFibered.pullbackMap XF.2 h) (p.map h ≫ eqToHom hav)
      have hσ :
        (q ⋙ p).IsHomLift (p.map h ≫ eqToHom hav)
          (c2_sigma p q x y g (p.map h ≫ eqToHom hav) (IsPreFibered.pullbackMap XF.2 h) hξ
            (t (c2_mem g (p.map h ≫ eqToHom hav)) ((Sieve.overEquiv_iff S _).1 hh))) :=
        c2_sigma_lift p q x y g _ _ hξ _
      have hls :
        (q ⋙ p).IsHomLift (p.map h ≫ eqToHom hav)
          (IsPreFibered.pullbackMap XF.2 h ≫ Fiber.fiberInclusion.map s₀) := by
        infer_instance
      have hmr := morRestrict_fac (q ⋙ p) x y (c2_mem g (p.map h ≫ eqToHom hav)) s₀
      simp only [Over.mk_hom] at hmr
      rw [ha (c2_mem g (p.map h ≫ eqToHom hav)) ((Sieve.overEquiv_iff S _).1 hh)] at hmr
      refine
        IsStronglyCartesian.ext (q ⋙ p) g.hom (IsPreFibered.pullbackMap y.2 g.hom)
          (p.map h ≫ eqToHom hav) ?_
      rw [c2_sigma_fac, hmr,
        reassoc_of%
          c2_nu_comp p q x g (p.map h ≫ eqToHom hav) (IsPreFibered.pullbackMap XF.2 h) hξ,
        Category.assoc]
    have huniq :
      ∀ (s₀ : A ⟶ B),
        q.map (Fiber.fiberInclusion.map s₀) = ψ₁ →
          (∀ {cc : 𝒳} (h : cc ⟶ q.obj A.1)
            (hh : (((Sieve.overEquiv g S).pullback (eqToHom hav)).functorPullback p).arrows h),
            IsPreFibered.pullbackMap XF.2 h ≫ Fiber.fiberInclusion.map s₀ =
              c2_sigma p q x y g (p.map h ≫ eqToHom hav) (IsPreFibered.pullbackMap XF.2 h)
                (c2_isHomLift_comp p q h (IsPreFibered.pullbackMap XF.2 h) (p.map h ≫ eqToHom hav))
                (t (c2_mem g (p.map h ≫ eqToHom hav)) ((Sieve.overEquiv_iff S _).1 hh))) →
          s₀ = s := by
      intro s₀ hq₀ hd₀
      have hq₀' : q.IsHomLift ψ₁ (Fiber.fiberInclusion.map s₀) := by
        rw [← hq₀]; infer_instance
      have hw₀l :
        q.IsHomLift (𝟙 (q.obj A.1))
          (IsStronglyCartesian.map q ψ₁ ζ (g := 𝟙 (q.obj A.1)) (Category.id_comp ψ₁).symm
            (Fiber.fiberInclusion.map s₀)) :=
        IsStronglyCartesian.map_isHomLift q ψ₁ ζ (Category.id_comp ψ₁).symm _
      have hw₀f :
        (IsStronglyCartesian.map q ψ₁ ζ (g := 𝟙 (q.obj A.1)) (Category.id_comp ψ₁).symm
              (Fiber.fiberInclusion.map s₀)) ≫
            ζ =
          Fiber.fiberInclusion.map s₀ :=
        IsStronglyCartesian.fac q ψ₁ ζ (Category.id_comp ψ₁).symm _
      set w₀ : XF ⟶ ZF :=
        ⟨IsStronglyCartesian.map q ψ₁ ζ (g := 𝟙 (q.obj A.1)) (Category.id_comp ψ₁).symm
            (Fiber.fiberInclusion.map s₀),
          hw₀l⟩ with
        hw₀d
      have hw₀v :
        Fiber.fiberInclusion.map w₀ =
          IsStronglyCartesian.map q ψ₁ ζ (g := 𝟙 (q.obj A.1)) (Category.id_comp ψ₁).symm
            (Fiber.fiberInclusion.map s₀) :=
        rfl
      have hww : w₀ = w := by
        refine eq_of_pullbackFiberHom_locally_eq q (hq.isMorSheaf _ XF ZF) hT ?_
        intro cc h hh
        rw [hw h hh]
        refine Fiber.hom_ext ?_
        rw [c2_thetaF_val]
        refine c2_theta_uniq p q x y g _ _ _ _ _ (hsq h hh) _ (pullbackFiberHom w₀ h).2 ?_
        rw [← Category.assoc, pullbackFiberHom_fac, Category.assoc, hw₀v, hw₀f]
        exact hd₀ h hh
      refine Fiber.hom_ext ?_
      rw [hsval, ← hw₀f, ← hw₀v, hww]
    have hQs :
      (Fiber.mapOfComp (q ⋙ p) p q hF1.comp_eq g.left).map s =
        (mapPbIso hF1 x g.hom).inv ≫ ψ ≫ (mapPbIso hF1 y g.hom).hom := by
      refine Fiber.hom_ext ?_
      rw [Fiber.fiberInclusion_map_mapOfComp_map, hqs]
    have hphi : phiFun hF1 x y g s = ψ := by
      unfold phiFun
      rw [hQs]
      simp
    have hamalg : ∀ ⦃Z : Over U⦄ (k : Z ⟶ g) (hk : S k), morRestrict (q ⋙ p) x y k s = t k hk := by
      intro Z k hk
      have hkleft : (Sieve.overEquiv g S).arrows k.left := ⟨Z, k, 𝟙 _, hk, by simp⟩
      have hc : p.obj (IsPreFibered.pullbackObj hav k.left) = Z.left :=
        IsPreFibered.pullbackObj_proj hav k.left
      have hf₀ :
        p.map (IsPreFibered.pullbackMap hav k.left) ≫ eqToHom hav = eqToHom hc ≫ k.left := by
        rw [IsHomLift.fac' p k.left (IsPreFibered.pullbackMap hav k.left)]
        simp
      have hh₀ :
        (((Sieve.overEquiv g S).pullback (eqToHom hav)).functorPullback p).arrows
          (IsPreFibered.pullbackMap hav k.left) := by
        rw [Sieve.functorPullback_arrows, Presieve.functorPullback_mem, Sieve.pullback_apply]
        rw [hf₀]
        exact (Sieve.overEquiv g S).downward_closed hkleft _
      have hZh : k.left ≫ g.hom = Z.hom := Over.w k
      have huw :
        eqToHom hc ≫ Z.hom =
          ((p.map (IsPreFibered.pullbackMap hav k.left) ≫ eqToHom hav) ≫ g.hom) := by
        rw [hf₀, Category.assoc, hZh]
      have hu'w :
        eqToHom hc.symm ≫ ((p.map (IsPreFibered.pullbackMap hav k.left) ≫ eqToHom hav) ≫ g.hom) =
          Z.hom := by
        rw [hf₀, Category.assoc, hZh, ← Category.assoc, eqToHom_trans, eqToHom_refl,
          Category.id_comp]
      set u :
        (Over.mk ((p.map (IsPreFibered.pullbackMap hav k.left) ≫ eqToHom hav) ≫ g.hom) : Over U) ⟶
          Z :=
        Over.homMk (eqToHom hc) huw with hud
      have hui : IsIso u := by
        refine ⟨Over.homMk (eqToHom hc.symm) hu'w, ?_, ?_⟩
        · apply Over.OverMorphism.ext
          simp [hud]
        · apply Over.OverMorphism.ext
          simp [hud]
      have huk : u ≫ k = c2_mem g (p.map (IsPreFibered.pullbackMap hav k.left) ≫ eqToHom hav) := by
        apply Over.OverMorphism.ext
        simp only [Over.comp_left, c2_mem_left, hud, Over.homMk_left]
        exact hf₀.symm
      have hξ₀ :
        (q ⋙ p).IsHomLift (p.map (IsPreFibered.pullbackMap hav k.left) ≫ eqToHom hav)
          (IsPreFibered.pullbackMap XF.2 (IsPreFibered.pullbackMap hav k.left)) :=
        c2_isHomLift_comp p q (IsPreFibered.pullbackMap hav k.left) _ _
      have hpc0 :
        p.IsStronglyCartesian (eqToHom hc ≫ k.left) (IsPreFibered.pullbackMap hav k.left) := by
        have hid : p.IsHomLift (eqToHom hc) (𝟙 (IsPreFibered.pullbackObj hav k.left)) :=
          IsHomLift.id_lift_eqToHom_domain hc rfl
        have h0 :
          p.IsStronglyCartesian (eqToHom hc ≫ k.left)
            (𝟙 (IsPreFibered.pullbackObj hav k.left) ≫ IsPreFibered.pullbackMap hav k.left) :=
          inferInstance
        rwa [Category.id_comp] at h0
      have hpmap :
        p.map (IsPreFibered.pullbackMap hav k.left) =
          (eqToHom hc ≫ k.left) ≫ eqToHom hav.symm := by
        rw [IsHomLift.fac' p k.left (IsPreFibered.pullbackMap hav k.left), Category.assoc]
      have hpc1 :
        p.IsStronglyCartesian (p.map (IsPreFibered.pullbackMap hav k.left))
          (IsPreFibered.pullbackMap hav k.left) := by
        rw [hpmap]
        exact c2_sc_of_eq p (eqToHom hc ≫ k.left) _ hav.symm
      have hξ₀c0 :
        (q ⋙ p).IsStronglyCartesian (p.map (IsPreFibered.pullbackMap hav k.left))
          (IsPreFibered.pullbackMap XF.2 (IsPreFibered.pullbackMap hav k.left)) :=
        IsStronglyCartesian.comp_functor q p (p.map (IsPreFibered.pullbackMap hav k.left))
          (IsPreFibered.pullbackMap hav k.left)
          (IsPreFibered.pullbackMap XF.2 (IsPreFibered.pullbackMap hav k.left))
      have hξ₀c :
        (q ⋙ p).IsStronglyCartesian (p.map (IsPreFibered.pullbackMap hav k.left) ≫ eqToHom hav)
          (IsPreFibered.pullbackMap XF.2 (IsPreFibered.pullbackMap hav k.left)) :=
        c2_sc_of_eq (q ⋙ p) (p.map (IsPreFibered.pullbackMap hav k.left)) _ hav
      have hνiso :=
        c2_nu_isIso p q x g (p.map (IsPreFibered.pullbackMap hav k.left) ≫ eqToHom hav)
          (IsPreFibered.pullbackMap XF.2 (IsPreFibered.pullbackMap hav k.left)) hξ₀ hξ₀c
      have hcore :
        morRestrict (q ⋙ p) x y
            (c2_mem g (p.map (IsPreFibered.pullbackMap hav k.left) ≫ eqToHom hav)) s =
          t (c2_mem g (p.map (IsPreFibered.pullbackMap hav k.left) ≫ eqToHom hav))
            ((Sieve.overEquiv_iff S _).1 hh₀) := by
        refine
          fiber_hom_ext_of_cartesian
            ((p.map (IsPreFibered.pullbackMap hav k.left) ≫ eqToHom hav) ≫ g.hom)
            (IsPreFibered.pullbackMap y.2
              ((p.map (IsPreFibered.pullbackMap hav k.left) ≫ eqToHom hav) ≫ g.hom))
            inferInstance _ _ ?_
        have hmr :=
          morRestrict_fac (q ⋙ p) x y
            (c2_mem g (p.map (IsPreFibered.pullbackMap hav k.left) ≫ eqToHom hav)) s
        simp only [Over.mk_hom] at hmr
        rw [hmr, ←
          cancel_epi
            (c2_nu p q x g (p.map (IsPreFibered.pullbackMap hav k.left) ≫ eqToHom hav)
              (IsPreFibered.pullbackMap XF.2 (IsPreFibered.pullbackMap hav k.left)) hξ₀),
          reassoc_of%
            c2_nu_comp p q x g (p.map (IsPreFibered.pullbackMap hav k.left) ≫ eqToHom hav)
              (IsPreFibered.pullbackMap XF.2 (IsPreFibered.pullbackMap hav k.left)) hξ₀,
          ← c2_sigma_fac p q x y g _ _ hξ₀ _, ← Category.assoc,
          hdagger (IsPreFibered.pullbackMap hav k.left) hh₀]
      have hts :
        ∀
          (kk :
            (Over.mk ((p.map (IsPreFibered.pullbackMap hav k.left) ≫ eqToHom hav) ≫ g.hom) :
                Over U) ⟶
              g)
          (hkk : S kk), kk = u ≫ k → t kk hkk = morRestrict (q ⋙ p) x y u (t k hk) := by
        intro kk hkk hkkeq
        subst hkkeq
        exact htsc k u hk
      refine c2_morRestrict_inj p q x y u _ _ ?_
      rw [← morRestrict_comp, huk, hcore, hts _ _ huk.symm]
    exact
      ⟨s, ⟨hphi, hamalg⟩, fun s₀ hs₀ =>
        huniq s₀
          (by
            have h1 :
              (Fiber.mapOfComp (q ⋙ p) p q hF1.comp_eq g.left).map s₀ =
                (mapPbIso hF1 x g.hom).inv ≫ ψ ≫ (mapPbIso hF1 y g.hom).hom := by
              have h2 := hs₀.1
              rw [← h2]
              unfold phiFun
              simp
            have h3 := congrArg Fiber.fiberInclusion.map h1
            rw [Fiber.fiberInclusion_map_mapOfComp_map] at h3
            rw [h3, ← hψ₁d])
          (hA s₀ hs₀.2)⟩

end CondTwo

end CategoryTheory.Functor
