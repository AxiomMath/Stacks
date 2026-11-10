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
# A stack over a stack: the transferred descent datum

Towards condition (3) of Stacks 026F for a composite `q ⋙ p` (Stacks 09WX): a descent datum `D`
for `q ⋙ p` relative to a sieve `R` on `p.obj a`, together with a compatible family of
`p`-cartesian descent morphisms for the datum `D` pushed down to `p`, is transferred to a descent
datum for `q` relative to the sieve `R.functorPullback p` on `a`, and an object of `𝒴` descending
the transferred datum is compared with the objects of `D`.

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

/-! ## Condition (3) of Stacks 09WX: effectivity of descent for `q ⋙ p` -/

section CondThree

set_option backward.isDefEq.respectTransparency false

/-- Transport `IsHomLift` along an equality of base morphisms. -/
lemma c3_homLift_of_eq {A B : Type*} [Category A] [Category B] (r : A ⥤ B) {W V : B}
    {n m : W ⟶ V} {b₁ b₂ : A} {φ : b₁ ⟶ b₂} (h : r.IsHomLift n φ) (hnm : n = m) :
    r.IsHomLift m φ := by
  subst hnm; exact h

/-- Composite of homlifts, with the base morphism of the composite given up to an equality. -/
lemma c3_homLift_comp {A B : Type*} [Category A] [Category B] (r : A ⥤ B) {R S T : B}
    (f : R ⟶ S) (g : S ⟶ T) {k : R ⟶ T} {a b c : A} {φ : a ⟶ b} {ψ : b ⟶ c}
    [r.IsHomLift f φ] [r.IsHomLift g ψ] (hk : f ≫ g = k) : r.IsHomLift k (φ ≫ ψ) :=
  c3_homLift_of_eq r (n := f ≫ g) inferInstance hk

variable (p : 𝒳 ⥤ 𝒞) (q : 𝒴 ⥤ 𝒳) [p.IsFibered] [q.IsFibered] [(q ⋙ p).IsFibered]

/-- The compatibility condition of `SieveDescentDatum.IsEffective` for the descended datum
`SieveDescentDatum.mapF (isFibredOneMorphism_comp p q) D`, with the comparison isomorphisms
`mapPbIso` cancelled: the images under `q` of the gluing isomorphisms of `D` intertwine the
descent morphisms `ζ`. -/
lemma c3_zeta_compat {U : 𝒞} {R : Sieve U} (D : SieveDescentDatum (q ⋙ p) R) {b : 𝒳}
    (ζ : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R f), q.obj (D.obj f hf).1 ⟶ b)
    (hc :
      ∀ ⦃V W Z : 𝒞⦄ ⦃f : V ⟶ U⦄ (hf : R f) ⦃g : W ⟶ U⦄ (hg : R g) (ε : Z ⟶ V) (ε' : Z ⟶ W)
        (heq : ε ≫ f = ε' ≫ g),
        Fiber.fiberInclusion.map
              ((SieveDescentDatum.mapF (isFibredOneMorphism_comp p q) D).iso hf hg ε ε' heq).hom ≫
            IsPreFibered.pullbackMap
              ((SieveDescentDatum.mapF (isFibredOneMorphism_comp p q) D).obj g hg).2 ε' ≫
            ζ g hg =
          IsPreFibered.pullbackMap
              ((SieveDescentDatum.mapF (isFibredOneMorphism_comp p q) D).obj f hf).2 ε ≫
            ζ f hf)
    ⦃V W Z : 𝒞⦄ ⦃f : V ⟶ U⦄ (hf : R f) ⦃g : W ⟶ U⦄ (hg : R g) (ε : Z ⟶ V) (ε' : Z ⟶ W)
    (heq : ε ≫ f = ε' ≫ g) :
    q.map (Fiber.fiberInclusion.map (D.iso hf hg ε ε' heq).hom) ≫
        q.map (IsPreFibered.pullbackMap (D.obj g hg).2 ε') ≫ ζ g hg =
      q.map (IsPreFibered.pullbackMap (D.obj f hf).2 ε) ≫ ζ f hf := by
  have h := hc hf hg ε ε' heq
  simp only [SieveDescentDatum.mapF, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc, Fiber.fiberInclusion_map_mapOfComp_map,
    mapPbIso_inv_fac_assoc] at h
  rw [← mapPbIso_hom_fac_assoc (isFibredOneMorphism_comp p q) (D.obj f hf) ε] at h
  exact (cancel_epi _).mp h

/-- The `q`-image of the chosen `(q ⋙ p)`-cartesian lift of `m` at `x` is `p`-strongly
cartesian. -/
lemma c3_pi_sc {V W : 𝒞} (x : (q ⋙ p).Fiber V) (m : W ⟶ V) :
    p.IsStronglyCartesian m (q.map (IsPreFibered.pullbackMap x.2 m)) := by
  have h1 : (q ⋙ p).IsStronglyCartesian m (IsPreFibered.pullbackMap x.2 m) := inferInstance
  have := h1
  exact (comp_cart p q m (IsPreFibered.pullbackMap x.2 m)).1

/-- The chosen `(q ⋙ p)`-cartesian lift of `m` at `x` is `q`-strongly cartesian over its
`q`-image. -/
lemma c3_pi_sc' {V W : 𝒞} (x : (q ⋙ p).Fiber V) (m : W ⟶ V) :
    q.IsStronglyCartesian (q.map (IsPreFibered.pullbackMap x.2 m))
      (IsPreFibered.pullbackMap x.2 m) := by
  have h1 : (q ⋙ p).IsStronglyCartesian m (IsPreFibered.pullbackMap x.2 m) := inferInstance
  have := h1
  exact (comp_cart p q m (IsPreFibered.pullbackMap x.2 m)).2

/-- The cocycle condition of `D`, followed by the chosen cartesian lift at the last arrow. -/
lemma c3_cocycle_pm {E : Type*} [Category E] {F : E ⥤ 𝒞} [F.IsFibered] {U : 𝒞}
    {R : Sieve U} (D : SieveDescentDatum F R) {V₁ V₂ V₃ Z : 𝒞} {f₁ : V₁ ⟶ U} (h₁ : R f₁)
    {f₂ : V₂ ⟶ U} (h₂ : R f₂) {f₃ : V₃ ⟶ U} (h₃ : R f₃) (ε₁ : Z ⟶ V₁) (ε₂ : Z ⟶ V₂) (ε₃ : Z ⟶ V₃)
    (h₁₂ : ε₁ ≫ f₁ = ε₂ ≫ f₂) (h₂₃ : ε₂ ≫ f₂ = ε₃ ≫ f₃) (h₁₃ : ε₁ ≫ f₁ = ε₃ ≫ f₃) :
    Fiber.fiberInclusion.map (D.iso h₁ h₂ ε₁ ε₂ h₁₂).hom ≫
        Fiber.fiberInclusion.map (D.iso h₂ h₃ ε₂ ε₃ h₂₃).hom ≫
          IsPreFibered.pullbackMap (D.obj f₃ h₃).2 ε₃ =
      Fiber.fiberInclusion.map (D.iso h₁ h₃ ε₁ ε₃ h₁₃).hom ≫
        IsPreFibered.pullbackMap (D.obj f₃ h₃).2 ε₃ := by
  rw [← Category.assoc, ← Functor.map_comp, D.cocycle h₁ h₂ h₃ ε₁ ε₂ ε₃ h₁₂ h₂₃ h₁₃]

/-! ### Reindexing a descent datum along a factorization

`D.obj f hf` and `D.obj (u ≫ f) hfu` are related by a strongly cartesian morphism over `u`, built
from the gluing isomorphism of `D` at `(𝟙, u)`, and that morphism is compatible with all the
gluing isomorphisms of `D`. -/

section Beta

variable {U : 𝒞} {R : Sieve U} (D : SieveDescentDatum (q ⋙ p) R)

omit [p.IsFibered] [q.IsFibered] in
/-- A gluing isomorphism of `D` at one and the same arrow, taken between the chosen pullbacks along
two *equal* morphisms, is the canonical comparison of those chosen pullbacks. -/
lemma c3_iso_self_fac {V Z : 𝒞} {f : V ⟶ U} (hf : R f) (ε ε' : Z ⟶ V) (hee : ε = ε')
    (h : ε ≫ f = ε' ≫ f) :
    Fiber.fiberInclusion.map (D.iso hf hf ε ε' h).hom ≫
        IsPreFibered.pullbackMap (D.obj f hf).2 ε' =
      IsPreFibered.pullbackMap (D.obj f hf).2 ε := by
  subst hee
  rw [D.iso_self hf ε h, Functor.map_id, Category.id_comp]

omit [p.IsFibered] [q.IsFibered] in
/-- Contracting the chosen pullback along an identity, after base change, is the gluing isomorphism
of `D` at one and the same arrow. -/
lemma c3_idIso_comp {V Z : 𝒞} {f : V ⟶ U} (hf : R f) (ε : Z ⟶ V)
    (h : ε ≫ f = (ε ≫ 𝟙 V) ≫ f) :
    pullbackFiberHom (pullbackFiberIdIso (D.obj f hf)).inv ε ≫
        (pullbackFiberCompIso (D.obj f hf) (𝟙 V) ε).hom =
      (D.iso hf hf ε (ε ≫ 𝟙 V) h).hom := by
  refine
    fiber_hom_ext_of_cartesian (ε ≫ 𝟙 V) (IsPreFibered.pullbackMap (D.obj f hf).2 (ε ≫ 𝟙 V))
      (IsPreFibered.pullbackMap.IsCartesian _ _) _ _ ?_
  rw [c3_iso_self_fac p q D hf ε (ε ≫ 𝟙 V) (Category.comp_id ε).symm h]
  simp [Functor.map_comp, Category.assoc, pullbackFiberCompIso_hom_fac,
    pullbackFiberHom_fac_assoc, pullbackFiberIdIso_inv_fac, Category.comp_id]

/-- The reindexing morphism `D.obj f₀ ⟶ D.obj f` attached to a factorization `u ≫ f = f₀`. -/
noncomputable def c3_beta {V W : 𝒞} {f : V ⟶ U} (hf : R f) (u : W ⟶ V) {f₀ : W ⟶ U}
    (hf₀ : R f₀) (huf : u ≫ f = f₀) : (D.obj f₀ hf₀).1 ⟶ (D.obj f hf).1 :=
  Fiber.fiberInclusion.map (pullbackFiberIdIso (D.obj f₀ hf₀)).inv ≫
    Fiber.fiberInclusion.map (D.iso hf₀ hf (𝟙 W) u (by rw [Category.id_comp, huf])).hom ≫
    IsPreFibered.pullbackMap (D.obj f hf).2 u

omit [p.IsFibered] [q.IsFibered] in
lemma c3_beta_sc {V W : 𝒞} {f : V ⟶ U} (hf : R f) (u : W ⟶ V) {f₀ : W ⟶ U} (hf₀ : R f₀)
    (huf : u ≫ f = f₀) : (q ⋙ p).IsStronglyCartesian u (c3_beta p q D hf u hf₀ huf) := by
  have h1 :
    (q ⋙ p).IsStronglyCartesian (𝟙 W)
      (Fiber.fiberInclusion.map (pullbackFiberIdIso (D.obj f₀ hf₀)).inv) :=
    IsStronglyCartesian.of_isIso (q ⋙ p) (𝟙 W) _
  have h2 :
    (q ⋙ p).IsStronglyCartesian (𝟙 W)
      (Fiber.fiberInclusion.map (D.iso hf₀ hf (𝟙 W) u (by rw [Category.id_comp, huf])).hom) :=
    IsStronglyCartesian.of_isIso (q ⋙ p) (𝟙 W) _
  have := h1
  have := h2
  have h0 : (q ⋙ p).IsStronglyCartesian (𝟙 W ≫ 𝟙 W ≫ u) (c3_beta p q D hf u hf₀ huf) := by
    unfold c3_beta
    infer_instance
  rwa [Category.id_comp, Category.id_comp] at h0

omit [p.IsFibered] [q.IsFibered] in
/-- The reindexing morphism is compatible with every gluing isomorphism of `D`: restricting along
`ε` and then reindexing is the gluing isomorphism at `(ε, ε ≫ u)` followed by the chosen lift. -/
@[reassoc]
lemma c3_beta_fac {V W Z : 𝒞} {f : V ⟶ U} (hf : R f) (u : W ⟶ V) {f₀ : W ⟶ U} (hf₀ : R f₀)
    (huf : u ≫ f = f₀) (ε : Z ⟶ W) {e : Z ⟶ V} (he : ε ≫ u = e) (hE : ε ≫ f₀ = e ≫ f) :
    IsPreFibered.pullbackMap (D.obj f₀ hf₀).2 ε ≫ c3_beta p q D hf u hf₀ huf =
      Fiber.fiberInclusion.map (D.iso hf₀ hf ε e hE).hom ≫
        IsPreFibered.pullbackMap (D.obj f hf).2 e := by
  subst he
  have hid : (𝟙 W) ≫ f₀ = u ≫ f := by rw [Category.id_comp, huf]
  have hE1 : ε ≫ f₀ = (ε ≫ 𝟙 W) ≫ f₀ := by rw [Category.comp_id]
  have hE2 : (ε ≫ 𝟙 W) ≫ f₀ = (ε ≫ u) ≫ f := by
    rw [Category.comp_id]; exact hE
  rw [← D.cocycle hf₀ hf₀ hf ε (ε ≫ 𝟙 W) (ε ≫ u) hE1 hE2 hE, ← c3_idIso_comp p q D hf₀ ε hE1, ←
    D.iso_pullback hf₀ hf (𝟙 W) u hid ε]
  unfold c3_beta
  simp [Functor.map_comp, Category.assoc, pullbackFiberIso_hom, pullbackFiberCompIso_hom_fac,
    pullbackFiberHom_fac_assoc, Iso.hom_inv_id_assoc]

end Beta

omit [p.IsFibered] [q.IsFibered] [(q ⋙ p).IsFibered] in
/-- The base morphism of the `q`-image of a `(q ⋙ p)`-homlift, read through the identifications of
the fibres. -/
lemma c3_pmap_homLift {V Z : 𝒞} {b₁ b₂ : 𝒴} (ε : Z ⟶ V) (φ : b₁ ⟶ b₂)
    [(q ⋙ p).IsHomLift ε φ] (hb₁ : (q ⋙ p).obj b₁ = Z) (hb₂ : (q ⋙ p).obj b₂ = V) :
    p.map (q.map φ) ≫ eqToHom hb₂ = eqToHom hb₁ ≫ ε := by
  have h := IsHomLift.fac' (q ⋙ p) ε φ
  have h' : p.map (q.map φ) = eqToHom hb₁ ≫ ε ≫ eqToHom hb₂.symm := h
  rw [h']
  simp

/-! ### The transferred descent datum on `𝒳`

Fix `a : 𝒳`, a sieve `R` on `p.obj a`, a descent datum `D` for `q ⋙ p` relative to `R`, and a
family `ζ` of `p`-cartesian descent morphisms for the datum `D` pushed down to `p`, compatible with
the gluing isomorphisms of `D` in the sense of `c3_zeta_compat`. -/

variable {a : 𝒳} {R : Sieve (p.obj a)} (D : SieveDescentDatum (q ⋙ p) R)
  (ζ : ∀ ⦃V : 𝒞⦄ (f : V ⟶ p.obj a) (hf : R f), q.obj (D.obj f hf).1 ⟶ a)
  (hζc : ∀ ⦃V : 𝒞⦄ (f : V ⟶ p.obj a) (hf : R f), p.IsCartesian f (ζ f hf))

/-- The compatibility of a family `ζ` of descent morphisms with the gluing isomorphisms of `D`,
read through `q`. -/
def c3_Compat : Prop :=
  ∀ ⦃V W Z : 𝒞⦄ ⦃f : V ⟶ p.obj a⦄ (hf : R f) ⦃g : W ⟶ p.obj a⦄ (hg : R g) (ε : Z ⟶ V) (ε' : Z ⟶ W)
    (heq : ε ≫ f = ε' ≫ g),
    q.map (Fiber.fiberInclusion.map (D.iso hf hg ε ε' heq).hom) ≫
        q.map (IsPreFibered.pullbackMap (D.obj g hg).2 ε') ≫ ζ g hg =
      q.map (IsPreFibered.pullbackMap (D.obj f hf).2 ε) ≫ ζ f hf

/-- The canonical factorization of an arrow `h : c ⟶ a` of the transferred sieve through the
`p`-cartesian descent morphism `ζ (p.map h)`. -/
noncomputable def c3_delta {c : 𝒳} (h : c ⟶ a) (hh : R (p.map h)) :
    c ⟶ q.obj (D.obj (p.map h) hh).1 :=
  haveI : p.IsCartesian (p.map h) (ζ (p.map h) hh) := hζc (p.map h) hh
  IsStronglyCartesian.map p (p.map h) (ζ (p.map h) hh) (Category.id_comp (p.map h)).symm h

instance c3_delta_isHomLift {c : 𝒳} (h : c ⟶ a) (hh : R (p.map h)) :
    p.IsHomLift (𝟙 (p.obj c)) (c3_delta p q D ζ hζc h hh) :=
  haveI : p.IsCartesian (p.map h) (ζ (p.map h) hh) := hζc (p.map h) hh
  IsStronglyCartesian.map_isHomLift p (p.map h) (ζ (p.map h) hh) (Category.id_comp (p.map h)).symm
    h

omit [q.IsFibered] in
@[reassoc]
lemma c3_delta_fac {c : 𝒳} (h : c ⟶ a) (hh : R (p.map h)) :
    c3_delta p q D ζ hζc h hh ≫ ζ (p.map h) hh = h :=
  have : p.IsCartesian (p.map h) (ζ (p.map h) hh) := hζc (p.map h) hh
  IsStronglyCartesian.fac p (p.map h) (ζ (p.map h) hh) (Category.id_comp (p.map h)).symm h

/-- The object of the fibre of `q` over `c` attached to an arrow `h : c ⟶ a` of the transferred
sieve: the chosen `q`-pullback of `D.obj (p.map h)` along `c3_delta`. -/
noncomputable def c3_obj {c : 𝒳} (h : c ⟶ a) (hh : R (p.map h)) : q.Fiber c :=
  pullbackFiber q (Fiber.mk (rfl : q.obj (D.obj (p.map h) hh).1 = q.obj (D.obj (p.map h) hh).1))
    (c3_delta p q D ζ hζc h hh)

/-- The chosen `q`-cartesian lift exhibiting `c3_obj h hh` as a pullback of `D.obj (p.map h)`. -/
noncomputable def c3_nu {c : 𝒳} (h : c ⟶ a) (hh : R (p.map h)) :
    (c3_obj p q D ζ hζc h hh).1 ⟶ (D.obj (p.map h) hh).1 :=
  IsPreFibered.pullbackMap (rfl : q.obj (D.obj (p.map h) hh).1 = q.obj (D.obj (p.map h) hh).1)
    (c3_delta p q D ζ hζc h hh)

instance c3_nu_isCartesian {c : 𝒳} (h : c ⟶ a) (hh : R (p.map h)) :
    q.IsCartesian (c3_delta p q D ζ hζc h hh) (c3_nu p q D ζ hζc h hh) :=
  IsPreFibered.pullbackMap.IsCartesian _ _

/-! #### The comparison with the chosen `(q ⋙ p)`-pullbacks

The gluing isomorphisms of `D` are taken between the *chosen* `(q ⋙ p)`-pullbacks of the
`D.obj f hf` along morphisms of `𝒞`, while the objects `c3_obj h hh` are chosen `q`-pullbacks along
morphisms of `𝒳`. `c3_sigma` and `c3_tau` are the canonical comparisons between them. The base
morphism of `𝒞` is passed by name, as in `pullbackFiberCompIso'`, so that it may be a composite
written in either of two ways. -/

omit [q.IsFibered] in
lemma c3_isHomLift_eps_delta {c : 𝒳} (h : c ⟶ a) (hh : R (p.map h)) {d : 𝒳} (ε : d ⟶ c)
    (m : p.obj d ⟶ p.obj c) (hm : p.map ε = m) :
    p.IsHomLift m (ε ≫ c3_delta p q D ζ hζc h hh) := by
  have h0 : p.IsHomLift (p.map ε ≫ 𝟙 (p.obj c)) (ε ≫ c3_delta p q D ζ hζc h hh) := inferInstance
  rwa [Category.comp_id, hm] at h0

/-- The comparison in `𝒳` between `d` and the `q`-image of the chosen `(q ⋙ p)`-pullback of
`D.obj (p.map h)` along `m`. -/
noncomputable def c3_sigma {c : 𝒳} (h : c ⟶ a) (hh : R (p.map h)) {d : 𝒳} (ε : d ⟶ c)
    (m : p.obj d ⟶ p.obj c) (hm : p.map ε = m) :
    d ⟶ q.obj (pullbackFiber (q ⋙ p) (D.obj (p.map h) hh) m).1 :=
  haveI := c3_pi_sc p q (D.obj (p.map h) hh) m
  haveI := c3_isHomLift_eps_delta p q D ζ hζc h hh ε m hm
  IsStronglyCartesian.map p m (q.map (IsPreFibered.pullbackMap (D.obj (p.map h) hh).2 m)) (g :=
    𝟙 (p.obj d)) (Category.id_comp m).symm (ε ≫ c3_delta p q D ζ hζc h hh)

instance c3_sigma_isHomLift {c : 𝒳} (h : c ⟶ a) (hh : R (p.map h)) {d : 𝒳} (ε : d ⟶ c)
    (m : p.obj d ⟶ p.obj c) (hm : p.map ε = m) :
    p.IsHomLift (𝟙 (p.obj d)) (c3_sigma p q D ζ hζc h hh ε m hm) :=
  haveI := c3_pi_sc p q (D.obj (p.map h) hh) m
  haveI := c3_isHomLift_eps_delta p q D ζ hζc h hh ε m hm
  IsStronglyCartesian.map_isHomLift p m (q.map (IsPreFibered.pullbackMap (D.obj (p.map h) hh).2 m))
    (Category.id_comp m).symm (ε ≫ c3_delta p q D ζ hζc h hh)

@[reassoc]
lemma c3_sigma_fac {c : 𝒳} (h : c ⟶ a) (hh : R (p.map h)) {d : 𝒳} (ε : d ⟶ c)
    (m : p.obj d ⟶ p.obj c) (hm : p.map ε = m) :
    c3_sigma p q D ζ hζc h hh ε m hm ≫ q.map (IsPreFibered.pullbackMap (D.obj (p.map h) hh).2 m) =
      ε ≫ c3_delta p q D ζ hζc h hh :=
  have := c3_pi_sc p q (D.obj (p.map h) hh) m
  have := c3_isHomLift_eps_delta p q D ζ hζc h hh ε m hm
  IsStronglyCartesian.fac p m (q.map (IsPreFibered.pullbackMap (D.obj (p.map h) hh).2 m))
    (Category.id_comp m).symm (ε ≫ c3_delta p q D ζ hζc h hh)

lemma c3_sigma_uniq {c : 𝒳} (h : c ⟶ a) (hh : R (p.map h)) {d : 𝒳} (ε : d ⟶ c)
    (m : p.obj d ⟶ p.obj c) (hm : p.map ε = m)
    (w : d ⟶ q.obj (pullbackFiber (q ⋙ p) (D.obj (p.map h) hh) m).1)
    (hw₁ : p.IsHomLift (𝟙 (p.obj d)) w)
    (hw₂ :
      w ≫ q.map (IsPreFibered.pullbackMap (D.obj (p.map h) hh).2 m) =
        ε ≫ c3_delta p q D ζ hζc h hh) :
    w = c3_sigma p q D ζ hζc h hh ε m hm :=
  have := c3_pi_sc p q (D.obj (p.map h) hh) m
  have := c3_isHomLift_eps_delta p q D ζ hζc h hh ε m hm
  have := hw₁
  IsStronglyCartesian.map_uniq p m (q.map (IsPreFibered.pullbackMap (D.obj (p.map h) hh).2 m))
    (Category.id_comp m).symm (ε ≫ c3_delta p q D ζ hζc h hh) w hw₂

/-- The chosen `q`-cartesian lift of `ε ≫ c3_delta h hh` at `D.obj (p.map h)`. -/
noncomputable def c3_rho {c : 𝒳} (h : c ⟶ a) (hh : R (p.map h)) {d : 𝒳} (ε : d ⟶ c) :
    (pullbackFiber q (c3_obj p q D ζ hζc h hh) ε).1 ⟶ (D.obj (p.map h) hh).1 :=
  IsPreFibered.pullbackMap (c3_obj p q D ζ hζc h hh).2 ε ≫ c3_nu p q D ζ hζc h hh

instance c3_rho_isCartesian {c : 𝒳} (h : c ⟶ a) (hh : R (p.map h)) {d : 𝒳} (ε : d ⟶ c) :
    q.IsCartesian (ε ≫ c3_delta p q D ζ hζc h hh) (c3_rho p q D ζ hζc h hh ε) := by
  have h1 : q.IsCartesian ε (IsPreFibered.pullbackMap (c3_obj p q D ζ hζc h hh).2 ε) :=
    IsPreFibered.pullbackMap.IsCartesian _ _
  have h2 := c3_nu_isCartesian p q D ζ hζc h hh
  have := h1
  have := h2
  unfold c3_rho
  infer_instance

/-- The comparison in `𝒴` from the chosen `q`-pullback of `c3_obj h hh` along `ε` to the chosen
`(q ⋙ p)`-pullback of `D.obj (p.map h)` along `m`. -/
noncomputable def c3_tau {c : 𝒳} (h : c ⟶ a) (hh : R (p.map h)) {d : 𝒳} (ε : d ⟶ c)
    (m : p.obj d ⟶ p.obj c) (hm : p.map ε = m) :
    (pullbackFiber q (c3_obj p q D ζ hζc h hh) ε).1 ⟶
      (pullbackFiber (q ⋙ p) (D.obj (p.map h) hh) m).1 :=
  haveI := c3_pi_sc' p q (D.obj (p.map h) hh) m
  IsStronglyCartesian.map q (q.map (IsPreFibered.pullbackMap (D.obj (p.map h) hh).2 m))
    (IsPreFibered.pullbackMap (D.obj (p.map h) hh).2 m) (g := c3_sigma p q D ζ hζc h hh ε m hm)
    (c3_sigma_fac p q D ζ hζc h hh ε m hm).symm (c3_rho p q D ζ hζc h hh ε)

instance c3_tau_isHomLift {c : 𝒳} (h : c ⟶ a) (hh : R (p.map h)) {d : 𝒳} (ε : d ⟶ c)
    (m : p.obj d ⟶ p.obj c) (hm : p.map ε = m) :
    q.IsHomLift (c3_sigma p q D ζ hζc h hh ε m hm) (c3_tau p q D ζ hζc h hh ε m hm) :=
  haveI := c3_pi_sc' p q (D.obj (p.map h) hh) m
  IsStronglyCartesian.map_isHomLift q (q.map (IsPreFibered.pullbackMap (D.obj (p.map h) hh).2 m))
    (IsPreFibered.pullbackMap (D.obj (p.map h) hh).2 m) (c3_sigma_fac p q D ζ hζc h hh ε m hm).symm
    (c3_rho p q D ζ hζc h hh ε)

@[reassoc]
lemma c3_tau_fac {c : 𝒳} (h : c ⟶ a) (hh : R (p.map h)) {d : 𝒳} (ε : d ⟶ c)
    (m : p.obj d ⟶ p.obj c) (hm : p.map ε = m) :
    c3_tau p q D ζ hζc h hh ε m hm ≫ IsPreFibered.pullbackMap (D.obj (p.map h) hh).2 m =
      c3_rho p q D ζ hζc h hh ε :=
  have := c3_pi_sc' p q (D.obj (p.map h) hh) m
  IsStronglyCartesian.fac q (q.map (IsPreFibered.pullbackMap (D.obj (p.map h) hh).2 m))
    (IsPreFibered.pullbackMap (D.obj (p.map h) hh).2 m) (c3_sigma_fac p q D ζ hζc h hh ε m hm).symm
    (c3_rho p q D ζ hζc h hh ε)

lemma c3_tau_uniq {c : 𝒳} (h : c ⟶ a) (hh : R (p.map h)) {d : 𝒳} (ε : d ⟶ c)
    (m : p.obj d ⟶ p.obj c) (hm : p.map ε = m)
    (w :
      (pullbackFiber q (c3_obj p q D ζ hζc h hh) ε).1 ⟶
        (pullbackFiber (q ⋙ p) (D.obj (p.map h) hh) m).1)
    (hw₁ : q.IsHomLift (c3_sigma p q D ζ hζc h hh ε m hm) w)
    (hw₂ : w ≫ IsPreFibered.pullbackMap (D.obj (p.map h) hh).2 m = c3_rho p q D ζ hζc h hh ε) :
    w = c3_tau p q D ζ hζc h hh ε m hm :=
  have := c3_pi_sc' p q (D.obj (p.map h) hh) m
  have := hw₁
  IsStronglyCartesian.map_uniq q (q.map (IsPreFibered.pullbackMap (D.obj (p.map h) hh).2 m))
    (IsPreFibered.pullbackMap (D.obj (p.map h) hh).2 m) (c3_sigma_fac p q D ζ hζc h hh ε m hm).symm
    (c3_rho p q D ζ hζc h hh ε) w hw₂

lemma c3_tau_sc {c : 𝒳} (h : c ⟶ a) (hh : R (p.map h)) {d : 𝒳} (ε : d ⟶ c)
    (m : p.obj d ⟶ p.obj c) (hm : p.map ε = m) :
    q.IsStronglyCartesian (c3_sigma p q D ζ hζc h hh ε m hm) (c3_tau p q D ζ hζc h hh ε m hm) := by
  have := c3_pi_sc' p q (D.obj (p.map h) hh) m
  have hc : q.IsStronglyCartesian (ε ≫ c3_delta p q D ζ hζc h hh) (c3_rho p q D ζ hζc h hh ε) :=
    inferInstance
  have :
    q.IsStronglyCartesian
      (c3_sigma p q D ζ hζc h hh ε m hm ≫
        q.map (IsPreFibered.pullbackMap (D.obj (p.map h) hh).2 m))
      (c3_tau p q D ζ hζc h hh ε m hm ≫ IsPreFibered.pullbackMap (D.obj (p.map h) hh).2 m) := by
    rw [c3_sigma_fac, c3_tau_fac]; exact hc
  exact
    IsStronglyCartesian.of_comp q (f := c3_sigma p q D ζ hζc h hh ε m hm) (g :=
      q.map (IsPreFibered.pullbackMap (D.obj (p.map h) hh).2 m)) (φ :=
      c3_tau p q D ζ hζc h hh ε m hm) (ψ := IsPreFibered.pullbackMap (D.obj (p.map h) hh).2 m)

/-! #### The comparisons `c3_sigma` are intertwined by the gluing isomorphisms of `D` -/

lemma c3_sigma_glue (hζg : c3_Compat p q D ζ) {c₁ c₂ d : 𝒳} (h₁ : c₁ ⟶ a)
    (hh₁ : R (p.map h₁)) (h₂ : c₂ ⟶ a) (hh₂ : R (p.map h₂)) (ε : d ⟶ c₁) (ε' : d ⟶ c₂)
    (heq : ε ≫ h₁ = ε' ≫ h₂) (m : p.obj d ⟶ p.obj c₁) (hm : p.map ε = m) (m' : p.obj d ⟶ p.obj c₂)
    (hm' : p.map ε' = m') (hcomm : m ≫ p.map h₁ = m' ≫ p.map h₂) :
    c3_sigma p q D ζ hζc h₁ hh₁ ε m hm ≫
        q.map (Fiber.fiberInclusion.map (D.iso hh₁ hh₂ m m' hcomm).hom) =
      c3_sigma p q D ζ hζc h₂ hh₂ ε' m' hm' := by
  have hπ₂ := c3_pi_sc p q (D.obj (p.map h₂) hh₂) m'
  have hκ :
    p.IsHomLift (𝟙 (p.obj d)) (q.map (Fiber.fiberInclusion.map (D.iso hh₁ hh₂ m m' hcomm).hom)) :=
    isHomLift_map_of_comp_eq (rfl : q ⋙ p = q ⋙ p) (𝟙 (p.obj d)) _
  have := hκ
  have := hπ₂
  have hL :
    p.IsHomLift (𝟙 (p.obj d))
      (c3_sigma p q D ζ hζc h₁ hh₁ ε m hm ≫
        q.map (Fiber.fiberInclusion.map (D.iso hh₁ hh₂ m m' hcomm).hom)) :=
    c3_homLift_comp p (𝟙 _) (𝟙 _) (Category.comp_id _)
  have := hL
  refine
    IsStronglyCartesian.ext p m' (q.map (IsPreFibered.pullbackMap (D.obj (p.map h₂) hh₂).2 m'))
      (𝟙 (p.obj d)) ?_
  rw [c3_sigma_fac]
  have hζ₂ : p.IsCartesian (p.map h₂) (ζ (p.map h₂) hh₂) := hζc (p.map h₂) hh₂
  have := hζ₂
  have hAl :
    p.IsHomLift m'
      ((c3_sigma p q D ζ hζc h₁ hh₁ ε m hm ≫
          q.map (Fiber.fiberInclusion.map (D.iso hh₁ hh₂ m m' hcomm).hom)) ≫
        q.map (IsPreFibered.pullbackMap (D.obj (p.map h₂) hh₂).2 m')) :=
    c3_homLift_comp p (𝟙 _) m' (Category.id_comp _)
  have hAr : p.IsHomLift m' (ε' ≫ c3_delta p q D ζ hζc h₂ hh₂) :=
    c3_isHomLift_eps_delta p q D ζ hζc h₂ hh₂ ε' m' hm'
  have := hAl
  have := hAr
  refine IsStronglyCartesian.ext p (p.map h₂) (ζ (p.map h₂) hh₂) m' ?_
  simp only [Category.assoc]
  rw [hζg hh₁ hh₂ m m' hcomm, ← Category.assoc, c3_sigma_fac, Category.assoc, c3_delta_fac,
    c3_delta_fac, heq]

/-! #### The gluing isomorphism of the transferred datum -/

section Glue

variable {c₁ c₂ d : 𝒳} (h₁ : c₁ ⟶ a) (hh₁ : R (p.map h₁)) (h₂ : c₂ ⟶ a) (hh₂ : R (p.map h₂))
  (ε : d ⟶ c₁) (ε' : d ⟶ c₂) (m : p.obj d ⟶ p.obj c₁) (hm : p.map ε = m) (m' : p.obj d ⟶ p.obj c₂)
  (hm' : p.map ε' = m') (hcomm : m ≫ p.map h₁ = m' ≫ p.map h₂)

/-- `c3_tau` for `h₁`, followed by the gluing isomorphism of `D`, is `q`-strongly cartesian over
`c3_sigma` for `h₂`. -/
lemma c3_tau_glue_sc (hζg : c3_Compat p q D ζ) (heq : ε ≫ h₁ = ε' ≫ h₂) :
    q.IsStronglyCartesian (c3_sigma p q D ζ hζc h₂ hh₂ ε' m' hm')
      (c3_tau p q D ζ hζc h₁ hh₁ ε m hm ≫
        Fiber.fiberInclusion.map (D.iso hh₁ hh₂ m m' hcomm).hom) := by
  have h1 := c3_tau_sc p q D ζ hζc h₁ hh₁ ε m hm
  have := h1
  have hiso : IsIso (Fiber.fiberInclusion.map (D.iso hh₁ hh₂ m m' hcomm).hom) := inferInstance
  have := hiso
  have h2 :
    q.IsStronglyCartesian (q.map (Fiber.fiberInclusion.map (D.iso hh₁ hh₂ m m' hcomm).hom))
      (Fiber.fiberInclusion.map (D.iso hh₁ hh₂ m m' hcomm).hom) :=
    inferInstance
  have := h2
  have h3 :
    q.IsStronglyCartesian
      (c3_sigma p q D ζ hζc h₁ hh₁ ε m hm ≫
        q.map (Fiber.fiberInclusion.map (D.iso hh₁ hh₂ m m' hcomm).hom))
      (c3_tau p q D ζ hζc h₁ hh₁ ε m hm ≫
        Fiber.fiberInclusion.map (D.iso hh₁ hh₂ m m' hcomm).hom) :=
    inferInstance
  rwa [c3_sigma_glue p q D ζ hζc hζg h₁ hh₁ h₂ hh₂ ε ε' heq m hm m' hm' hcomm] at h3

/-- The gluing isomorphism of the transferred datum: the two chosen `q`-pullbacks both carry a
`q`-cartesian morphism over `c3_sigma` for `h₂` into the chosen `(q ⋙ p)`-pullback of
`D.obj (p.map h₂)`. -/
noncomputable def c3_gl (hζg : c3_Compat p q D ζ) (heq : ε ≫ h₁ = ε' ≫ h₂) :
    pullbackFiber q (c3_obj p q D ζ hζc h₁ hh₁) ε ≅
      pullbackFiber q (c3_obj p q D ζ hζc h₂ hh₂) ε' :=
  haveI := c3_tau_glue_sc p q D ζ hζc h₁ hh₁ h₂ hh₂ ε ε' m hm m' hm' hcomm hζg heq
  haveI := c3_tau_sc p q D ζ hζc h₂ hh₂ ε' m' hm'
  fiberIsoOfCartesian (c3_sigma p q D ζ hζc h₂ hh₂ ε' m' hm')
    (c3_tau p q D ζ hζc h₁ hh₁ ε m hm ≫ Fiber.fiberInclusion.map (D.iso hh₁ hh₂ m m' hcomm).hom)
    (c3_tau p q D ζ hζc h₂ hh₂ ε' m' hm') inferInstance inferInstance

@[reassoc]
lemma c3_gl_fac (hζg : c3_Compat p q D ζ) (heq : ε ≫ h₁ = ε' ≫ h₂) :
    Fiber.fiberInclusion.map (c3_gl p q D ζ hζc h₁ hh₁ h₂ hh₂ ε ε' m hm m' hm' hcomm hζg heq).hom ≫
        c3_tau p q D ζ hζc h₂ hh₂ ε' m' hm' =
      c3_tau p q D ζ hζc h₁ hh₁ ε m hm ≫ Fiber.fiberInclusion.map (D.iso hh₁ hh₂ m m' hcomm).hom :=
  fiberIsoOfCartesian_hom_fac _ _ _ _ _

lemma c3_gl_uniq (hζg : c3_Compat p q D ζ) (heq : ε ≫ h₁ = ε' ≫ h₂)
    (ψ :
      pullbackFiber q (c3_obj p q D ζ hζc h₁ hh₁) ε ⟶
        pullbackFiber q (c3_obj p q D ζ hζc h₂ hh₂) ε')
    (hψ :
      Fiber.fiberInclusion.map ψ ≫ c3_tau p q D ζ hζc h₂ hh₂ ε' m' hm' =
        c3_tau p q D ζ hζc h₁ hh₁ ε m hm ≫
          Fiber.fiberInclusion.map (D.iso hh₁ hh₂ m m' hcomm).hom) :
    ψ = (c3_gl p q D ζ hζc h₁ hh₁ h₂ hh₂ ε ε' m hm m' hm' hcomm hζg heq).hom := by
  have := c3_tau_sc p q D ζ hζc h₂ hh₂ ε' m' hm'
  refine
    fiber_hom_ext_of_cartesian (c3_sigma p q D ζ hζc h₂ hh₂ ε' m' hm')
      (c3_tau p q D ζ hζc h₂ hh₂ ε' m' hm') inferInstance _ _ ?_
  rw [hψ, c3_gl_fac]

end Glue

/-! #### Compatibility of the comparisons with iterated chosen pullbacks -/

/-- `c3_sigma` is compatible with contracting an iterated chosen `(q ⋙ p)`-pullback. -/
lemma c3_sigma_comp {c d d' : 𝒳} (h : c ⟶ a) (hh : R (p.map h)) (ε : d ⟶ c) (γ : d' ⟶ d)
    (m : p.obj d ⟶ p.obj c) (hm : p.map ε = m) (n : p.obj d' ⟶ p.obj d) (hn : p.map γ = n) :
    c3_sigma p q D ζ hζc h hh (γ ≫ ε) (n ≫ m) (by rw [Functor.map_comp, hm, hn]) ≫
        q.map
          (Fiber.fiberInclusion.map (pullbackFiberCompIso (D.obj (p.map h) hh) m n).inv ≫
            IsPreFibered.pullbackMap (pullbackFiber (q ⋙ p) (D.obj (p.map h) hh) m).2 n) =
      γ ≫ c3_sigma p q D ζ hζc h hh ε m hm := by
  have hπ := c3_pi_sc p q (D.obj (p.map h) hh) m
  have := hπ
  have hγ : p.IsHomLift n γ := by
    rw [← hn]; infer_instance
  have := hγ
  have hX0 :
    (q ⋙ p).IsHomLift n
      (Fiber.fiberInclusion.map (pullbackFiberCompIso (D.obj (p.map h) hh) m n).inv ≫
        IsPreFibered.pullbackMap (pullbackFiber (q ⋙ p) (D.obj (p.map h) hh) m).2 n) :=
    c3_homLift_comp (q ⋙ p) (𝟙 _) n (Category.id_comp _)
  have := hX0
  have hX :
    p.IsHomLift n
      (q.map
        (Fiber.fiberInclusion.map (pullbackFiberCompIso (D.obj (p.map h) hh) m n).inv ≫
          IsPreFibered.pullbackMap (pullbackFiber (q ⋙ p) (D.obj (p.map h) hh) m).2 n)) :=
    isHomLift_map_of_comp_eq (rfl : q ⋙ p = q ⋙ p) n _
  have := hX
  have hL :
    p.IsHomLift n
      (c3_sigma p q D ζ hζc h hh (γ ≫ ε) (n ≫ m) (by rw [Functor.map_comp, hm, hn]) ≫
        q.map
          (Fiber.fiberInclusion.map (pullbackFiberCompIso (D.obj (p.map h) hh) m n).inv ≫
            IsPreFibered.pullbackMap (pullbackFiber (q ⋙ p) (D.obj (p.map h) hh) m).2 n)) :=
    c3_homLift_comp p (𝟙 _) n (Category.id_comp _)
  have hR : p.IsHomLift n (γ ≫ c3_sigma p q D ζ hζc h hh ε m hm) :=
    c3_homLift_comp p n (𝟙 _) (Category.comp_id _)
  have := hL
  have := hR
  refine
    IsStronglyCartesian.ext p m (q.map (IsPreFibered.pullbackMap (D.obj (p.map h) hh).2 m)) n ?_
  simp only [Category.assoc, ← Functor.map_comp]
  rw [pullbackFiberCompIso_inv_fac, c3_sigma_fac, c3_sigma_fac, Category.assoc]

@[reassoc]
lemma c3_rho_eq {c d : 𝒳} (h : c ⟶ a) (hh : R (p.map h)) (ε : d ⟶ c) :
    c3_rho p q D ζ hζc h hh ε =
      IsPreFibered.pullbackMap (c3_obj p q D ζ hζc h hh).2 ε ≫ c3_nu p q D ζ hζc h hh :=
  rfl

/-- `c3_tau` is compatible with contracting the iterated chosen pullbacks on both sides. -/
@[reassoc]
lemma c3_tau_comp {c d d' : 𝒳} (h : c ⟶ a) (hh : R (p.map h)) (ε : d ⟶ c) (γ : d' ⟶ d)
    (m : p.obj d ⟶ p.obj c) (hm : p.map ε = m) (n : p.obj d' ⟶ p.obj d) (hn : p.map γ = n) :
    c3_tau p q D ζ hζc h hh (γ ≫ ε) (n ≫ m) (by rw [Functor.map_comp, hm, hn]) ≫
        (Fiber.fiberInclusion.map (pullbackFiberCompIso (D.obj (p.map h) hh) m n).inv ≫
          IsPreFibered.pullbackMap (pullbackFiber (q ⋙ p) (D.obj (p.map h) hh) m).2 n) =
      Fiber.fiberInclusion.map (pullbackFiberCompIso (c3_obj p q D ζ hζc h hh) ε γ).inv ≫
        (IsPreFibered.pullbackMap (pullbackFiber q (c3_obj p q D ζ hζc h hh) ε).2 γ ≫
          c3_tau p q D ζ hζc h hh ε m hm) := by
  have hπ' := c3_pi_sc' p q (D.obj (p.map h) hh) m
  have := hπ'
  have hS := c3_sigma_comp p q D ζ hζc h hh ε γ m hm n hn
  have hLb :
    q.IsHomLift (γ ≫ c3_sigma p q D ζ hζc h hh ε m hm)
      (c3_tau p q D ζ hζc h hh (γ ≫ ε) (n ≫ m) (by rw [Functor.map_comp, hm, hn]) ≫
        (Fiber.fiberInclusion.map (pullbackFiberCompIso (D.obj (p.map h) hh) m n).inv ≫
          IsPreFibered.pullbackMap (pullbackFiber (q ⋙ p) (D.obj (p.map h) hh) m).2 n)) := by
    have h0 :
      q.IsHomLift
        (c3_sigma p q D ζ hζc h hh (γ ≫ ε) (n ≫ m) (by rw [Functor.map_comp, hm, hn]) ≫
          (q.map (Fiber.fiberInclusion.map (pullbackFiberCompIso (D.obj (p.map h) hh) m n).inv) ≫
            q.map (IsPreFibered.pullbackMap (pullbackFiber (q ⋙ p) (D.obj (p.map h) hh) m).2 n)))
        (c3_tau p q D ζ hζc h hh (γ ≫ ε) (n ≫ m) (by rw [Functor.map_comp, hm, hn]) ≫
          (Fiber.fiberInclusion.map (pullbackFiberCompIso (D.obj (p.map h) hh) m n).inv ≫
            IsPreFibered.pullbackMap (pullbackFiber (q ⋙ p) (D.obj (p.map h) hh) m).2 n)) :=
      inferInstance
    rw [← q.map_comp, hS] at h0
    exact h0
  have hRb :
    q.IsHomLift (γ ≫ c3_sigma p q D ζ hζc h hh ε m hm)
      (Fiber.fiberInclusion.map (pullbackFiberCompIso (c3_obj p q D ζ hζc h hh) ε γ).inv ≫
        (IsPreFibered.pullbackMap (pullbackFiber q (c3_obj p q D ζ hζc h hh) ε).2 γ ≫
          c3_tau p q D ζ hζc h hh ε m hm)) :=
    c3_homLift_comp q (𝟙 _) _ (Category.id_comp _)
  have := hLb
  have := hRb
  refine
    IsStronglyCartesian.ext q (q.map (IsPreFibered.pullbackMap (D.obj (p.map h) hh).2 m))
      (IsPreFibered.pullbackMap (D.obj (p.map h) hh).2 m) (γ ≫ c3_sigma p q D ζ hζc h hh ε m hm) ?_
  simp [Category.assoc, pullbackFiberCompIso_inv_fac, pullbackFiberCompIso_inv_fac_assoc,
    c3_tau_fac, c3_rho_eq]

/-- `c3_gl` does not depend on the names chosen for the base morphisms. -/
lemma c3_gl_base_indep {c₁ c₂ d : 𝒳} (h₁ : c₁ ⟶ a) (hh₁ : R (p.map h₁)) (h₂ : c₂ ⟶ a)
    (hh₂ : R (p.map h₂)) (ε : d ⟶ c₁) (ε' : d ⟶ c₂) (m m₂ : p.obj d ⟶ p.obj c₁) (hm : p.map ε = m)
    (hm₂ : p.map ε = m₂) (m' m₂' : p.obj d ⟶ p.obj c₂) (hm' : p.map ε' = m')
    (hm₂' : p.map ε' = m₂') (hcomm : m ≫ p.map h₁ = m' ≫ p.map h₂)
    (hcomm₂ : m₂ ≫ p.map h₁ = m₂' ≫ p.map h₂) (hζg : c3_Compat p q D ζ) (heq : ε ≫ h₁ = ε' ≫ h₂) :
    c3_gl p q D ζ hζc h₁ hh₁ h₂ hh₂ ε ε' m hm m' hm' hcomm hζg heq =
      c3_gl p q D ζ hζc h₁ hh₁ h₂ hh₂ ε ε' m₂ hm₂ m₂' hm₂' hcomm₂ hζg heq := by
  subst hm
  subst hm₂
  subst hm'
  subst hm₂'
  rfl

/-- The descent datum for `q` relative to the transferred sieve `R.functorPullback p` on `a`. -/
noncomputable def c3_datum (hζg : c3_Compat p q D ζ) :
    SieveDescentDatum q (R.functorPullback p) where
  obj {c} h hh := c3_obj p q D ζ hζc h hh
  iso {c₁ c₂ d} {h₁} hh₁ {h₂} hh₂ ε ε' heq :=
    c3_gl p q D ζ hζc h₁ hh₁ h₂ hh₂ ε ε' (p.map ε) rfl (p.map ε') rfl
      (by rw [← p.map_comp, ← p.map_comp, heq]) hζg heq
  cocycle {c₁ c₂ c₃ d} {h₁} hh₁ {h₂} hh₂ {h₃} hh₃ ε₁ ε₂ ε₃ h₁₂ h₂₃ h₁₃ := by
    have hc₁₂ : p.map ε₁ ≫ p.map h₁ = p.map ε₂ ≫ p.map h₂ := by
      rw [← p.map_comp, ← p.map_comp, h₁₂]
    have hc₂₃ : p.map ε₂ ≫ p.map h₂ = p.map ε₃ ≫ p.map h₃ := by
      rw [← p.map_comp, ← p.map_comp, h₂₃]
    have hc₁₃ : p.map ε₁ ≫ p.map h₁ = p.map ε₃ ≫ p.map h₃ := by
      rw [← p.map_comp, ← p.map_comp, h₁₃]
    refine
      c3_gl_uniq p q D ζ hζc h₁ hh₁ h₃ hh₃ ε₁ ε₃ (p.map ε₁) rfl (p.map ε₃) rfl hc₁₃ hζg h₁₃ _ ?_
    rw [Functor.map_comp, Category.assoc,
      c3_gl_fac p q D ζ hζc h₂ hh₂ h₃ hh₃ ε₂ ε₃ (p.map ε₂) rfl (p.map ε₃) rfl hc₂₃ hζg h₂₃,
      c3_gl_fac_assoc p q D ζ hζc h₁ hh₁ h₂ hh₂ ε₁ ε₂ (p.map ε₁) rfl (p.map ε₂) rfl hc₁₂ hζg h₁₂, ←
      Functor.map_comp, D.cocycle hh₁ hh₂ hh₃ (p.map ε₁) (p.map ε₂) (p.map ε₃) hc₁₂ hc₂₃ hc₁₃]
  iso_pullback {c₁ c₂ d d'} {h₁} hh₁ {h₂} hh₂ ε ε' heq γ := by
    have hcomm : p.map ε ≫ p.map h₁ = p.map ε' ≫ p.map h₂ := by
      rw [← p.map_comp, ← p.map_comp, heq]
    have heq' : (γ ≫ ε) ≫ h₁ = (γ ≫ ε') ≫ h₂ := by rw [Category.assoc, Category.assoc, heq]
    have hcomm' : (p.map γ ≫ p.map ε) ≫ p.map h₁ = (p.map γ ≫ p.map ε') ≫ p.map h₂ := by
      rw [Category.assoc, Category.assoc, hcomm]
    rw [c3_gl_base_indep p q D ζ hζc h₁ hh₁ h₂ hh₂ (γ ≫ ε) (γ ≫ ε') (p.map (γ ≫ ε))
        (p.map γ ≫ p.map ε) rfl (p.map_comp γ ε) (p.map (γ ≫ ε')) (p.map γ ≫ p.map ε') rfl
        (p.map_comp γ ε') (by rw [← p.map_comp, ← p.map_comp, heq']) hcomm' hζg heq']
    refine
      c3_gl_uniq p q D ζ hζc h₁ hh₁ h₂ hh₂ (γ ≫ ε) (γ ≫ ε') (p.map γ ≫ p.map ε) (p.map_comp γ ε)
        (p.map γ ≫ p.map ε') (p.map_comp γ ε') hcomm' hζg heq' _ ?_
    have hcA₂ :
      IsIso
        (Fiber.fiberInclusion.map
          (pullbackFiberCompIso (D.obj (p.map h₂) hh₂) (p.map ε') (p.map γ)).inv) :=
      inferInstance
    have := hcA₂
    have hs1 :
      q.IsStronglyCartesian
        (q.map
          (Fiber.fiberInclusion.map
            (pullbackFiberCompIso (D.obj (p.map h₂) hh₂) (p.map ε') (p.map γ)).inv))
        (Fiber.fiberInclusion.map
          (pullbackFiberCompIso (D.obj (p.map h₂) hh₂) (p.map ε') (p.map γ)).inv) :=
      inferInstance
    have hs2 := c3_pi_sc' p q (pullbackFiber (q ⋙ p) (D.obj (p.map h₂) hh₂) (p.map ε')) (p.map γ)
    have := hs1
    have := hs2
    have hX₂ :
      q.IsStronglyCartesian
        (q.map
          (Fiber.fiberInclusion.map
              (pullbackFiberCompIso (D.obj (p.map h₂) hh₂) (p.map ε') (p.map γ)).inv ≫
            IsPreFibered.pullbackMap (pullbackFiber (q ⋙ p) (D.obj (p.map h₂) hh₂) (p.map ε')).2
              (p.map γ)))
        (Fiber.fiberInclusion.map
            (pullbackFiberCompIso (D.obj (p.map h₂) hh₂) (p.map ε') (p.map γ)).inv ≫
          IsPreFibered.pullbackMap (pullbackFiber (q ⋙ p) (D.obj (p.map h₂) hh₂) (p.map ε')).2
            (p.map γ)) := by
      have h0 :
        q.IsStronglyCartesian
          (q.map
              (Fiber.fiberInclusion.map
                (pullbackFiberCompIso (D.obj (p.map h₂) hh₂) (p.map ε') (p.map γ)).inv) ≫
            q.map
              (IsPreFibered.pullbackMap (pullbackFiber (q ⋙ p) (D.obj (p.map h₂) hh₂) (p.map ε')).2
                (p.map γ)))
          (Fiber.fiberInclusion.map
              (pullbackFiberCompIso (D.obj (p.map h₂) hh₂) (p.map ε') (p.map γ)).inv ≫
            IsPreFibered.pullbackMap (pullbackFiber (q ⋙ p) (D.obj (p.map h₂) hh₂) (p.map ε')).2
              (p.map γ)) :=
        inferInstance
      rwa [← q.map_comp] at h0
    have := hX₂
    have hgl0 :
      q.IsHomLift
        (𝟙 d' ≫ c3_sigma p q D ζ hζc h₂ hh₂ (γ ≫ ε') (p.map γ ≫ p.map ε') (p.map_comp γ ε'))
        (Fiber.fiberInclusion.map
            ((pullbackFiberCompIso (c3_obj p q D ζ hζc h₁ hh₁) ε γ).inv ≫
              (pullbackFiberIso
                  (c3_gl p q D ζ hζc h₁ hh₁ h₂ hh₂ ε ε' (p.map ε) rfl (p.map ε') rfl hcomm hζg heq)
                  γ).hom ≫
              (pullbackFiberCompIso (c3_obj p q D ζ hζc h₂ hh₂) ε' γ).hom) ≫
          c3_tau p q D ζ hζc h₂ hh₂ (γ ≫ ε') (p.map γ ≫ p.map ε') (p.map_comp γ ε')) :=
      inferInstance
    rw [Category.id_comp] at hgl0
    have := hgl0
    have hR0 :
      q.IsHomLift
        (c3_sigma p q D ζ hζc h₁ hh₁ (γ ≫ ε) (p.map γ ≫ p.map ε) (p.map_comp γ ε) ≫
          q.map
            (Fiber.fiberInclusion.map
              (D.iso hh₁ hh₂ (p.map γ ≫ p.map ε) (p.map γ ≫ p.map ε') hcomm').hom))
        (c3_tau p q D ζ hζc h₁ hh₁ (γ ≫ ε) (p.map γ ≫ p.map ε) (p.map_comp γ ε) ≫
          Fiber.fiberInclusion.map
            (D.iso hh₁ hh₂ (p.map γ ≫ p.map ε) (p.map γ ≫ p.map ε') hcomm').hom) :=
      inferInstance
    rw [c3_sigma_glue p q D ζ hζc hζg h₁ hh₁ h₂ hh₂ (γ ≫ ε) (γ ≫ ε') heq' (p.map γ ≫ p.map ε)
        (p.map_comp γ ε) (p.map γ ≫ p.map ε') (p.map_comp γ ε') hcomm'] at hR0
    have := hR0
    refine
      IsStronglyCartesian.ext q
        (q.map
          (Fiber.fiberInclusion.map
              (pullbackFiberCompIso (D.obj (p.map h₂) hh₂) (p.map ε') (p.map γ)).inv ≫
            IsPreFibered.pullbackMap (pullbackFiber (q ⋙ p) (D.obj (p.map h₂) hh₂) (p.map ε')).2
              (p.map γ)))
        (Fiber.fiberInclusion.map
            (pullbackFiberCompIso (D.obj (p.map h₂) hh₂) (p.map ε') (p.map γ)).inv ≫
          IsPreFibered.pullbackMap (pullbackFiber (q ⋙ p) (D.obj (p.map h₂) hh₂) (p.map ε')).2
            (p.map γ))
        (c3_sigma p q D ζ hζc h₂ hh₂ (γ ≫ ε') (p.map γ ≫ p.map ε') (p.map_comp γ ε')) ?_
    rw [← D.iso_pullback hh₁ hh₂ (p.map ε) (p.map ε') hcomm (p.map γ)]
    simp only [Functor.map_comp, Category.assoc, pullbackFiberIso_hom]
    rw [Iso.hom_inv_id_map_assoc, pullbackFiberHom_fac,
      c3_tau_comp_assoc p q D ζ hζc h₁ hh₁ ε γ (p.map ε) rfl (p.map γ) rfl,
      c3_tau_comp p q D ζ hζc h₂ hh₂ ε' γ (p.map ε') rfl (p.map γ) rfl, Iso.hom_inv_id_map_assoc,
      pullbackFiberHom_fac_assoc,
      c3_gl_fac p q D ζ hζc h₁ hh₁ h₂ hh₂ ε ε' (p.map ε) rfl (p.map ε') rfl hcomm hζg heq]

/-! ### The descended object as a descent of `D` -/

section Final

omit [p.IsFibered] [q.IsFibered] in
/-- The reindexing morphism intertwines the descent morphisms. -/
lemma c3_beta_zeta (hζg : c3_Compat p q D ζ) {V W : 𝒞} {f : V ⟶ p.obj a} (hf : R f)
    (u : W ⟶ V) {f₀ : W ⟶ p.obj a} (hf₀ : R f₀) (huf : u ≫ f = f₀) :
    q.map (c3_beta p q D hf u hf₀ huf) ≫ ζ f hf = ζ f₀ hf₀ := by
  have hid : (𝟙 W) ≫ f₀ = u ≫ f := by rw [Category.id_comp, huf]
  unfold c3_beta
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hζg hf₀ hf (𝟙 W) u hid, ←
    Category.assoc, ← q.map_comp, pullbackFiberIdIso_inv_fac]
  exact (congrArg (fun t => t ≫ ζ f₀ hf₀) (q.map_id (D.obj f₀ hf₀).1)).trans (Category.id_comp _)

include hζc in
omit [q.IsFibered] in
/-- The image under `p` of the descent morphism `ζ f hf` is `f` precomposed with the canonical
identification of `p (q (D.obj f hf))` with the source of `f`. -/
lemma c3_pmap_zeta {V : 𝒞} (f : V ⟶ p.obj a) (hf : R f) :
    eqToHom (D.obj f hf).2 ≫ f = p.map (ζ f hf) := by
  have := hζc f hf
  rw [IsHomLift.fac' p f (ζ f hf)]
  simp

include hζc in
omit [q.IsFibered] in
/-- The image under `p` of `ζ f hf` is again an arrow of `R`, i.e. `ζ f hf` is an arrow of the
transferred sieve. -/
lemma c3_hhf {V : 𝒞} (f : V ⟶ p.obj a) (hf : R f) : R (p.map (ζ f hf)) :=
  c3_pmap_zeta p q D ζ hζc f hf ▸ R.downward_closed hf (eqToHom (D.obj f hf).2)

/-- The reindexing morphism comparing the object attached to the arrow `ζ f hf` of the transferred
sieve with `D.obj f hf` itself. -/
noncomputable def c3_betaf {V : 𝒞} (f : V ⟶ p.obj a) (hf : R f) :
    (D.obj (p.map (ζ f hf)) (c3_hhf p q D ζ hζc f hf)).1 ⟶ (D.obj f hf).1 :=
  c3_beta p q D hf (eqToHom (D.obj f hf).2) (c3_hhf p q D ζ hζc f hf)
    (c3_pmap_zeta p q D ζ hζc f hf)

instance c3_betaf_isIso {V : 𝒞} (f : V ⟶ p.obj a) (hf : R f) :
    IsIso (c3_betaf p q D ζ hζc f hf) := by
  have h :=
    c3_beta_sc p q D hf (eqToHom (D.obj f hf).2) (c3_hhf p q D ζ hζc f hf)
      (c3_pmap_zeta p q D ζ hζc f hf)
  have := h
  unfold c3_betaf
  exact IsStronglyCartesian.isIso_of_base_isIso (q ⋙ p) (eqToHom (D.obj f hf).2) _

omit [q.IsFibered] in
lemma c3_homLift_map_betaf {V : 𝒞} (f : V ⟶ p.obj a) (hf : R f) :
    p.IsHomLift (eqToHom (D.obj f hf).2) (q.map (c3_betaf p q D ζ hζc f hf)) := by
  have h :=
    c3_beta_sc p q D hf (eqToHom (D.obj f hf).2) (c3_hhf p q D ζ hζc f hf)
      (c3_pmap_zeta p q D ζ hζc f hf)
  have := h
  unfold c3_betaf
  exact isHomLift_map_of_comp_eq (rfl : q ⋙ p = q ⋙ p) (eqToHom (D.obj f hf).2) _

omit [q.IsFibered] in
/-- The factorization of `ζ f hf` through the descent morphism at `p.map (ζ f hf)` is inverse to
the `q`-image of the reindexing morphism. -/
lemma c3_delta_betaf (hζg : c3_Compat p q D ζ) {V : 𝒞} (f : V ⟶ p.obj a) (hf : R f) :
    c3_delta p q D ζ hζc (ζ f hf) (c3_hhf p q D ζ hζc f hf) ≫ q.map (c3_betaf p q D ζ hζc f hf) =
      𝟙 (q.obj (D.obj f hf).1) := by
  have hζf : p.IsCartesian f (ζ f hf) := hζc f hf
  have := hζf
  have h1 : p.IsHomLift (eqToHom (D.obj f hf).2) (𝟙 (q.obj (D.obj f hf).1)) :=
    IsHomLift.of_fac' p (eqToHom (D.obj f hf).2) (𝟙 (q.obj (D.obj f hf).1)) rfl (D.obj f hf).2
      (by simp)
  have h2 := c3_homLift_map_betaf p q D ζ hζc f hf
  have := h2
  have h3 :
    p.IsHomLift (eqToHom (D.obj f hf).2)
      (c3_delta p q D ζ hζc (ζ f hf) (c3_hhf p q D ζ hζc f hf) ≫
        q.map (c3_betaf p q D ζ hζc f hf)) :=
    c3_homLift_comp p (𝟙 (p.obj (q.obj (D.obj f hf).1))) _ (Category.id_comp _)
  have := h1
  have := h3
  refine IsStronglyCartesian.ext p f (ζ f hf) (eqToHom (D.obj f hf).2) ?_
  rw [Category.assoc, Category.id_comp]
  unfold c3_betaf
  rw [c3_beta_zeta p q D ζ hζg hf (eqToHom (D.obj f hf).2) (c3_hhf p q D ζ hζc f hf)
      (c3_pmap_zeta p q D ζ hζc f hf),
    c3_delta_fac]

/-- The comparison morphism between the object the transferred datum attaches to the arrow `ζ f hf`
and `D.obj f hf` itself. -/
noncomputable def c3_ehom {V : 𝒞} (f : V ⟶ p.obj a) (hf : R f) :
    (c3_obj p q D ζ hζc (ζ f hf) (c3_hhf p q D ζ hζc f hf)).1 ⟶ (D.obj f hf).1 :=
  c3_nu p q D ζ hζc (ζ f hf) (c3_hhf p q D ζ hζc f hf) ≫ c3_betaf p q D ζ hζc f hf

omit [q.IsFibered] in
lemma c3_delta_isIso (hζg : c3_Compat p q D ζ) {V : 𝒞} (f : V ⟶ p.obj a) (hf : R f) :
    IsIso (c3_delta p q D ζ hζc (ζ f hf) (c3_hhf p q D ζ hζc f hf)) := by
  have hb : IsIso (q.map (c3_betaf p q D ζ hζc f hf)) := inferInstance
  have h := c3_delta_betaf p q D ζ hζc hζg f hf
  have he :
    c3_delta p q D ζ hζc (ζ f hf) (c3_hhf p q D ζ hζc f hf) =
      CategoryTheory.inv (q.map (c3_betaf p q D ζ hζc f hf)) := by
    rw [← Category.comp_id (c3_delta p q D ζ hζc (ζ f hf) (c3_hhf p q D ζ hζc f hf)), ←
      IsIso.hom_inv_id (q.map (c3_betaf p q D ζ hζc f hf)), ← Category.assoc, h, Category.id_comp]
  rw [he]
  infer_instance

lemma c3_ehom_homLift (hζg : c3_Compat p q D ζ) {V : 𝒞} (f : V ⟶ p.obj a) (hf : R f) :
    q.IsHomLift (𝟙 (q.obj (D.obj f hf).1)) (c3_ehom p q D ζ hζc f hf) := by
  have hnu := c3_nu_isCartesian p q D ζ hζc (ζ f hf) (c3_hhf p q D ζ hζc f hf)
  have := hnu
  have h0 :
    q.IsHomLift
      (c3_delta p q D ζ hζc (ζ f hf) (c3_hhf p q D ζ hζc f hf) ≫ q.map (c3_betaf p q D ζ hζc f hf))
      (c3_nu p q D ζ hζc (ζ f hf) (c3_hhf p q D ζ hζc f hf) ≫ c3_betaf p q D ζ hζc f hf) :=
    inferInstance
  rw [c3_delta_betaf p q D ζ hζc hζg f hf] at h0
  exact h0

lemma c3_ehom_isIso (hζg : c3_Compat p q D ζ) {V : 𝒞} (f : V ⟶ p.obj a) (hf : R f) :
    IsIso (c3_ehom p q D ζ hζc f hf) := by
  have hnu := c3_nu_isCartesian p q D ζ hζc (ζ f hf) (c3_hhf p q D ζ hζc f hf)
  have := hnu
  have hsc :
    q.IsStronglyCartesian (c3_delta p q D ζ hζc (ζ f hf) (c3_hhf p q D ζ hζc f hf))
      (c3_nu p q D ζ hζc (ζ f hf) (c3_hhf p q D ζ hζc f hf)) :=
    inferInstance
  have := hsc
  have := c3_delta_isIso p q D ζ hζc hζg f hf
  have hnuiso : IsIso (c3_nu p q D ζ hζc (ζ f hf) (c3_hhf p q D ζ hζc f hf)) :=
    IsStronglyCartesian.isIso_of_base_isIso q
      (c3_delta p q D ζ hζc (ζ f hf) (c3_hhf p q D ζ hζc f hf)) _
  have := hnuiso
  unfold c3_ehom
  infer_instance

/-- The descent morphism of `D` at `f`, obtained from the descent morphism of the transferred datum
at the arrow `ζ f hf` and the comparison `c3_ehom`. -/
noncomputable def c3_zfin (hζg : c3_Compat p q D ζ) {y : 𝒴}
    (ξ : ∀ ⦃c : 𝒳⦄ (h : c ⟶ a) (hh : R (p.map h)), (c3_obj p q D ζ hζc h hh).1 ⟶ y) {V : 𝒞}
    (f : V ⟶ p.obj a) (hf : R f) : (D.obj f hf).1 ⟶ y :=
  haveI := c3_ehom_isIso p q D ζ hζc hζg f hf
  CategoryTheory.inv (c3_ehom p q D ζ hζc f hf) ≫ ξ (ζ f hf) (c3_hhf p q D ζ hζc f hf)

include hζc in
omit [q.IsFibered] in
/-- The compatibility of base morphisms that `D.iso` needs at the arrow `ζ f hf`. -/
lemma c3_hEf {V Z : 𝒞} (f : V ⟶ p.obj a) (hf : R f) (ε : Z ⟶ V) :
    p.map (q.map (IsPreFibered.pullbackMap (D.obj f hf).2 ε)) ≫ p.map (ζ f hf) =
      (eqToHom (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2 ≫ ε) ≫ f := by
  rw [← c3_pmap_zeta p q D ζ hζc f hf, ← Category.assoc,
    c3_pmap_homLift p q ε (IsPreFibered.pullbackMap (D.obj f hf).2 ε)
      (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2 (D.obj f hf).2,
    Category.assoc]

/-- The inverse comparison, composed with the chosen `(q ⋙ p)`-cartesian lift, is the chosen
`q`-cartesian lift followed by `c3_ehom`. -/
lemma c3_that_fac {V Z : 𝒞} (f : V ⟶ p.obj a) (hf : R f) (ε : Z ⟶ V) :
    (c3_tau p q D ζ hζc (ζ f hf) (c3_hhf p q D ζ hζc f hf)
            (q.map (IsPreFibered.pullbackMap (D.obj f hf).2 ε))
            (p.map (q.map (IsPreFibered.pullbackMap (D.obj f hf).2 ε))) rfl ≫
          Fiber.fiberInclusion.map
            (D.iso (c3_hhf p q D ζ hζc f hf) hf
                (p.map (q.map (IsPreFibered.pullbackMap (D.obj f hf).2 ε)))
                (eqToHom (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2 ≫ ε)
                (c3_hEf p q D ζ hζc f hf ε)).hom ≫
          Fiber.fiberInclusion.map
            (pullbackFiberCompIso (D.obj f hf) ε
                (eqToHom (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2)).inv ≫
          IsPreFibered.pullbackMap (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2
            (eqToHom (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2)) ≫
        IsPreFibered.pullbackMap (D.obj f hf).2 ε =
      IsPreFibered.pullbackMap (c3_obj p q D ζ hζc (ζ f hf) (c3_hhf p q D ζ hζc f hf)).2
          (q.map (IsPreFibered.pullbackMap (D.obj f hf).2 ε)) ≫
        c3_ehom p q D ζ hζc f hf := by
  simp only [Category.assoc, pullbackFiberCompIso_inv_fac]
  rw [←
    c3_beta_fac p q D hf (eqToHom (D.obj f hf).2) (c3_hhf p q D ζ hζc f hf)
      (c3_pmap_zeta p q D ζ hζc f hf) (p.map (q.map (IsPreFibered.pullbackMap (D.obj f hf).2 ε)))
      (c3_pmap_homLift p q ε (IsPreFibered.pullbackMap (D.obj f hf).2 ε)
        (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2 (D.obj f hf).2)
      (c3_hEf p q D ζ hζc f hf ε),
    ← Category.assoc, c3_tau_fac, c3_rho_eq, Category.assoc]
  rfl

/-- The base morphism, in `𝒳`, of the inverse comparison is the identity. -/
lemma c3_that_base (hζg : c3_Compat p q D ζ) {V Z : 𝒞} (f : V ⟶ p.obj a) (hf : R f)
    (ε : Z ⟶ V) :
    c3_sigma p q D ζ hζc (ζ f hf) (c3_hhf p q D ζ hζc f hf)
          (q.map (IsPreFibered.pullbackMap (D.obj f hf).2 ε))
          (p.map (q.map (IsPreFibered.pullbackMap (D.obj f hf).2 ε))) rfl ≫
        q.map
          (Fiber.fiberInclusion.map
            (D.iso (c3_hhf p q D ζ hζc f hf) hf
                (p.map (q.map (IsPreFibered.pullbackMap (D.obj f hf).2 ε)))
                (eqToHom (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2 ≫ ε)
                (c3_hEf p q D ζ hζc f hf ε)).hom) ≫
        q.map
          (Fiber.fiberInclusion.map
            (pullbackFiberCompIso (D.obj f hf) ε
                (eqToHom (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2)).inv) ≫
        q.map
          (IsPreFibered.pullbackMap (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2
            (eqToHom (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2)) =
      𝟙 (q.obj (pullbackFiber (q ⋙ p) (D.obj f hf) ε).1) := by
  have hPs : p.IsStronglyCartesian ε (q.map (IsPreFibered.pullbackMap (D.obj f hf).2 ε)) :=
    c3_pi_sc p q (D.obj f hf) ε
  have := hPs
  have hR :
    p.IsHomLift (eqToHom (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2)
      (𝟙 (q.obj (pullbackFiber (q ⋙ p) (D.obj f hf) ε).1)) :=
    IsHomLift.of_fac' p (eqToHom (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2)
      (𝟙 (q.obj (pullbackFiber (q ⋙ p) (D.obj f hf) ε).1)) rfl
      (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2 (by simp)
  have h1 :
    p.IsHomLift (𝟙 (p.obj (q.obj (pullbackFiber (q ⋙ p) (D.obj f hf) ε).1)))
      (q.map
        (Fiber.fiberInclusion.map
          (D.iso (c3_hhf p q D ζ hζc f hf) hf
              (p.map (q.map (IsPreFibered.pullbackMap (D.obj f hf).2 ε)))
              (eqToHom (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2 ≫ ε)
              (c3_hEf p q D ζ hζc f hf ε)).hom)) :=
    isHomLift_map_of_comp_eq (rfl : q ⋙ p = q ⋙ p) _ _
  have h2 :
    p.IsHomLift (𝟙 (p.obj (q.obj (pullbackFiber (q ⋙ p) (D.obj f hf) ε).1)))
      (q.map
        (Fiber.fiberInclusion.map
          (pullbackFiberCompIso (D.obj f hf) ε
              (eqToHom (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2)).inv)) :=
    isHomLift_map_of_comp_eq (rfl : q ⋙ p = q ⋙ p) _ _
  have h3 :
    p.IsHomLift (eqToHom (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2)
      (q.map
        (IsPreFibered.pullbackMap (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2
          (eqToHom (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2))) := by
    have :=
      c3_pi_sc p q (pullbackFiber (q ⋙ p) (D.obj f hf) ε)
        (eqToHom (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2)
    infer_instance
  have := h1
  have := h2
  have := h3
  have s1 :
    p.IsHomLift (eqToHom (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2)
      (q.map
          (Fiber.fiberInclusion.map
            (pullbackFiberCompIso (D.obj f hf) ε
                (eqToHom (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2)).inv) ≫
        q.map
          (IsPreFibered.pullbackMap (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2
            (eqToHom (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2))) :=
    c3_homLift_comp p (𝟙 (p.obj _)) _ (Category.id_comp _)
  have := s1
  have s2' :
    p.IsHomLift (eqToHom (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2)
      (q.map
          (Fiber.fiberInclusion.map
            (D.iso (c3_hhf p q D ζ hζc f hf) hf
                (p.map (q.map (IsPreFibered.pullbackMap (D.obj f hf).2 ε)))
                (eqToHom (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2 ≫ ε)
                (c3_hEf p q D ζ hζc f hf ε)).hom) ≫
        q.map
          (Fiber.fiberInclusion.map
            (pullbackFiberCompIso (D.obj f hf) ε
                (eqToHom (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2)).inv) ≫
        q.map
          (IsPreFibered.pullbackMap (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2
            (eqToHom (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2))) :=
    c3_homLift_comp p (𝟙 (p.obj _)) _ (Category.id_comp _)
  have := s2'
  have s0 :
    p.IsHomLift (𝟙 (p.obj (q.obj (pullbackFiber (q ⋙ p) (D.obj f hf) ε).1)))
      (c3_sigma p q D ζ hζc (ζ f hf) (c3_hhf p q D ζ hζc f hf)
        (q.map (IsPreFibered.pullbackMap (D.obj f hf).2 ε))
        (p.map (q.map (IsPreFibered.pullbackMap (D.obj f hf).2 ε))) rfl) :=
    c3_sigma_isHomLift p q D ζ hζc (ζ f hf) (c3_hhf p q D ζ hζc f hf)
      (q.map (IsPreFibered.pullbackMap (D.obj f hf).2 ε))
      (p.map (q.map (IsPreFibered.pullbackMap (D.obj f hf).2 ε))) rfl
  have := s0
  have hL :
    p.IsHomLift (eqToHom (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2)
      (c3_sigma p q D ζ hζc (ζ f hf) (c3_hhf p q D ζ hζc f hf)
          (q.map (IsPreFibered.pullbackMap (D.obj f hf).2 ε))
          (p.map (q.map (IsPreFibered.pullbackMap (D.obj f hf).2 ε))) rfl ≫
        q.map
          (Fiber.fiberInclusion.map
            (D.iso (c3_hhf p q D ζ hζc f hf) hf
                (p.map (q.map (IsPreFibered.pullbackMap (D.obj f hf).2 ε)))
                (eqToHom (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2 ≫ ε)
                (c3_hEf p q D ζ hζc f hf ε)).hom) ≫
        q.map
          (Fiber.fiberInclusion.map
            (pullbackFiberCompIso (D.obj f hf) ε
                (eqToHom (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2)).inv) ≫
        q.map
          (IsPreFibered.pullbackMap (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2
            (eqToHom (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2))) :=
    c3_homLift_comp p (𝟙 (p.obj _)) _ (Category.id_comp _)
  have := hL
  have := hR
  refine
    IsStronglyCartesian.ext p ε (q.map (IsPreFibered.pullbackMap (D.obj f hf).2 ε))
      (eqToHom (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2) ?_
  simp only [Category.assoc, ← q.map_comp]
  rw [pullbackFiberCompIso_inv_fac, ←
    c3_beta_fac p q D hf (eqToHom (D.obj f hf).2) (c3_hhf p q D ζ hζc f hf)
      (c3_pmap_zeta p q D ζ hζc f hf) (p.map (q.map (IsPreFibered.pullbackMap (D.obj f hf).2 ε)))
      (c3_pmap_homLift p q ε (IsPreFibered.pullbackMap (D.obj f hf).2 ε)
        (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2 (D.obj f hf).2)
      (c3_hEf p q D ζ hζc f hf ε),
    q.map_comp, ← Category.assoc, c3_sigma_fac, Category.assoc]
  rw [show
      q.map
          (c3_beta p q D hf (eqToHom (D.obj f hf).2) (c3_hhf p q D ζ hζc f hf)
            (c3_pmap_zeta p q D ζ hζc f hf)) =
        q.map (c3_betaf p q D ζ hζc f hf)
      from rfl,
    c3_delta_betaf p q D ζ hζc hζg f hf, Category.comp_id]
  exact (Category.id_comp _).symm

omit [p.IsFibered] [q.IsFibered] in
/-- The two descent morphisms of the transferred datum agree over `𝒳`. -/
lemma c3_hE (hζg : c3_Compat p q D ζ) {V W Z : 𝒞} (f : V ⟶ p.obj a) (hf : R f)
    (g : W ⟶ p.obj a) (hg : R g) (ε : Z ⟶ V) (ε' : Z ⟶ W) (heq : ε ≫ f = ε' ≫ g) :
    (q.map (IsPreFibered.pullbackMap (D.obj f hf).2 ε)) ≫ ζ f hf =
      (q.map
          ((Fiber.fiberInclusion.map (D.iso hf hg ε ε' heq).hom) ≫
            IsPreFibered.pullbackMap (D.obj g hg).2 ε')) ≫
        ζ g hg := by
  rw [Functor.map_comp, Category.assoc]
  exact (hζg hf hg ε ε' heq).symm

omit [p.IsFibered] [q.IsFibered] in
/-- The corresponding compatibility of base morphisms of `𝒞`. -/
lemma c3_hcomm (hζg : c3_Compat p q D ζ) {V W Z : 𝒞} (f : V ⟶ p.obj a) (hf : R f)
    (g : W ⟶ p.obj a) (hg : R g) (ε : Z ⟶ V) (ε' : Z ⟶ W) (heq : ε ≫ f = ε' ≫ g) :
    (p.map (q.map (IsPreFibered.pullbackMap (D.obj f hf).2 ε))) ≫ p.map (ζ f hf) =
      (p.map
          (q.map
            ((Fiber.fiberInclusion.map (D.iso hf hg ε ε' heq).hom) ≫
              IsPreFibered.pullbackMap (D.obj g hg).2 ε'))) ≫
        p.map (ζ g hg) := by
  rw [← p.map_comp, ← p.map_comp, c3_hE p q D ζ hζg f hf g hg ε ε' heq]

/-- The gluing isomorphism of the transferred datum, followed by the chosen `q`-cartesian lift and
the comparison `c3_ehom`, is the inverse comparison followed by the gluing isomorphism of `D`. -/
lemma c3_chain (hζg : c3_Compat p q D ζ) {V W Z : 𝒞} (f : V ⟶ p.obj a) (hf : R f)
    (g : W ⟶ p.obj a) (hg : R g) (ε : Z ⟶ V) (ε' : Z ⟶ W) (heq : ε ≫ f = ε' ≫ g) :
    Fiber.fiberInclusion.map
          (c3_gl p q D ζ hζc (ζ f hf) (c3_hhf p q D ζ hζc f hf) (ζ g hg) (c3_hhf p q D ζ hζc g hg)
              (q.map (IsPreFibered.pullbackMap (D.obj f hf).2 ε))
              (q.map
                ((Fiber.fiberInclusion.map (D.iso hf hg ε ε' heq).hom) ≫
                  IsPreFibered.pullbackMap (D.obj g hg).2 ε'))
              (p.map (q.map (IsPreFibered.pullbackMap (D.obj f hf).2 ε))) rfl
              (p.map
                (q.map
                  ((Fiber.fiberInclusion.map (D.iso hf hg ε ε' heq).hom) ≫
                    IsPreFibered.pullbackMap (D.obj g hg).2 ε')))
              rfl (c3_hcomm p q D ζ hζg f hf g hg ε ε' heq) hζg
              (c3_hE p q D ζ hζg f hf g hg ε ε' heq)).hom ≫
        IsPreFibered.pullbackMap (c3_obj p q D ζ hζc (ζ g hg) (c3_hhf p q D ζ hζc g hg)).2
          (q.map
            ((Fiber.fiberInclusion.map (D.iso hf hg ε ε' heq).hom) ≫
              IsPreFibered.pullbackMap (D.obj g hg).2 ε')) ≫
        c3_ehom p q D ζ hζc g hg =
      ((c3_tau p q D ζ hζc (ζ f hf) (c3_hhf p q D ζ hζc f hf)
            (q.map (IsPreFibered.pullbackMap (D.obj f hf).2 ε))
            (p.map (q.map (IsPreFibered.pullbackMap (D.obj f hf).2 ε))) rfl) ≫
          (Fiber.fiberInclusion.map
            (D.iso (c3_hhf p q D ζ hζc f hf) hf
                (p.map (q.map (IsPreFibered.pullbackMap (D.obj f hf).2 ε)))
                ((eqToHom (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2) ≫ ε)
                (c3_hEf p q D ζ hζc f hf ε)).hom) ≫
          (Fiber.fiberInclusion.map
            (pullbackFiberCompIso (D.obj f hf) ε
                (eqToHom (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2)).inv) ≫
          (IsPreFibered.pullbackMap (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2
            (eqToHom (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2))) ≫
        ((Fiber.fiberInclusion.map (D.iso hf hg ε ε' heq).hom) ≫
          IsPreFibered.pullbackMap (D.obj g hg).2 ε') := by
  have hPgl :
    (q ⋙ p).IsHomLift ε'
      ((Fiber.fiberInclusion.map (D.iso hf hg ε ε' heq).hom) ≫
        IsPreFibered.pullbackMap (D.obj g hg).2 ε') :=
    c3_homLift_comp (q ⋙ p) (𝟙 _) ε' (Category.id_comp _)
  have := hPgl
  have hep :
    (p.map
          (q.map
            ((Fiber.fiberInclusion.map (D.iso hf hg ε ε' heq).hom) ≫
              IsPreFibered.pullbackMap (D.obj g hg).2 ε'))) ≫
        eqToHom (D.obj g hg).2 =
      ((eqToHom (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2) ≫ ε') :=
    c3_pmap_homLift p q ε'
      ((Fiber.fiberInclusion.map (D.iso hf hg ε ε' heq).hom) ≫
        IsPreFibered.pullbackMap (D.obj g hg).2 ε')
      (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2 (D.obj g hg).2
  have hEg :
    (p.map
          (q.map
            ((Fiber.fiberInclusion.map (D.iso hf hg ε ε' heq).hom) ≫
              IsPreFibered.pullbackMap (D.obj g hg).2 ε'))) ≫
        p.map (ζ g hg) =
      ((eqToHom (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2) ≫ ε') ≫ g := by
    rw [← c3_pmap_zeta p q D ζ hζc g hg, ← Category.assoc, hep]
  have hEfg :
    (p.map (q.map (IsPreFibered.pullbackMap (D.obj f hf).2 ε))) ≫ p.map (ζ f hf) =
      ((eqToHom (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2) ≫ ε') ≫ g :=
    (c3_hcomm p q D ζ hζg f hf g hg ε ε' heq).trans hEg
  have hEE' :
    ((eqToHom (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2) ≫ ε) ≫ f =
      ((eqToHom (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2) ≫ ε') ≫ g := by
    rw [Category.assoc, Category.assoc, heq]
  have hip :
    Fiber.fiberInclusion.map
          (D.iso hf hg ((eqToHom (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2) ≫ ε)
              ((eqToHom (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2) ≫ ε') hEE').hom ≫
        IsPreFibered.pullbackMap (D.obj g hg).2
          ((eqToHom (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2) ≫ ε') =
      (Fiber.fiberInclusion.map
          (pullbackFiberCompIso (D.obj f hf) ε
              (eqToHom (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2)).inv) ≫
        (IsPreFibered.pullbackMap (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2
          (eqToHom (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2)) ≫
        ((Fiber.fiberInclusion.map (D.iso hf hg ε ε' heq).hom) ≫
          IsPreFibered.pullbackMap (D.obj g hg).2 ε') := by
    rw [← D.iso_pullback hf hg ε ε' heq (eqToHom (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2)]
    simp [Functor.map_comp, Category.assoc, pullbackFiberIso_hom,
      pullbackFiberCompIso_hom_fac, pullbackFiberHom_fac_assoc]
  rw [show
      c3_ehom p q D ζ hζc g hg =
        c3_nu p q D ζ hζc (ζ g hg) (c3_hhf p q D ζ hζc g hg) ≫ c3_betaf p q D ζ hζc g hg
      from rfl]
  simp only [Category.assoc]
  rw [← c3_rho_eq_assoc, ← c3_tau_fac_assoc, c3_gl_fac_assoc]
  · unfold c3_tau
    rw [show
        c3_betaf p q D ζ hζc g hg =
          c3_beta p q D hg (eqToHom (D.obj g hg).2) (c3_hhf p q D ζ hζc g hg)
            (c3_pmap_zeta p q D ζ hζc g hg)
        from rfl,
      c3_beta_fac p q D hg (eqToHom (D.obj g hg).2) (c3_hhf p q D ζ hζc g hg)
        (c3_pmap_zeta p q D ζ hζc g hg)
        (p.map
          (q.map
            ((Fiber.fiberInclusion.map (D.iso hf hg ε ε' heq).hom) ≫
              IsPreFibered.pullbackMap (D.obj g hg).2 ε')))
        hep hEg,
      c3_cocycle_pm D (c3_hhf p q D ζ hζc f hf) (c3_hhf p q D ζ hζc g hg) hg _ _ _
        (c3_hcomm p q D ζ hζg f hf g hg ε ε' heq) hEg hEfg,
      ← c3_cocycle_pm D (c3_hhf p q D ζ hζc f hf) hf hg _ _ _
        (c3_hEf p q D ζ hζc f hf ε) hEE' hEfg, hip]
  · simp [Functor.map_comp]

/-- The comparison `ω` is inverse to the composite of `c3_tau` with the gluing isomorphisms. -/
lemma c3_om_that (hζg : c3_Compat p q D ζ) {V Z : 𝒞} (f : V ⟶ p.obj a) (hf : R f)
    (ε : Z ⟶ V)
    (ω :
      (pullbackFiber (q ⋙ p) (D.obj f hf) ε).1 ⟶
        (pullbackFiber q (c3_obj p q D ζ hζc (ζ f hf) (c3_hhf p q D ζ hζc f hf))
            (q.map (IsPreFibered.pullbackMap (D.obj f hf).2 ε))).1)
    (hω1 : q.IsHomLift (𝟙 (q.obj (pullbackFiber (q ⋙ p) (D.obj f hf) ε).1)) ω)
    (hω2 :
      ω ≫
          IsPreFibered.pullbackMap (c3_obj p q D ζ hζc (ζ f hf) (c3_hhf p q D ζ hζc f hf)).2
            (q.map (IsPreFibered.pullbackMap (D.obj f hf).2 ε)) ≫
          c3_ehom p q D ζ hζc f hf =
        (IsPreFibered.pullbackMap (D.obj f hf).2 ε)) :
    ω ≫
        ((c3_tau p q D ζ hζc (ζ f hf) (c3_hhf p q D ζ hζc f hf)
            (q.map (IsPreFibered.pullbackMap (D.obj f hf).2 ε))
            (p.map (q.map (IsPreFibered.pullbackMap (D.obj f hf).2 ε))) rfl) ≫
          (Fiber.fiberInclusion.map
            (D.iso (c3_hhf p q D ζ hζc f hf) hf
                (p.map (q.map (IsPreFibered.pullbackMap (D.obj f hf).2 ε)))
                ((eqToHom (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2) ≫ ε)
                (c3_hEf p q D ζ hζc f hf ε)).hom) ≫
          (Fiber.fiberInclusion.map
            (pullbackFiberCompIso (D.obj f hf) ε
                (eqToHom (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2)).inv) ≫
          (IsPreFibered.pullbackMap (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2
            (eqToHom (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2))) =
      𝟙 (pullbackFiber (q ⋙ p) (D.obj f hf) ε).1 := by
  have := hω1
  have t1 :
    q.IsHomLift
      (q.map
          (Fiber.fiberInclusion.map
            (pullbackFiberCompIso (D.obj f hf) ε
                (eqToHom (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2)).inv) ≫
        q.map
          (IsPreFibered.pullbackMap (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2
            (eqToHom (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2)))
      ((Fiber.fiberInclusion.map
          (pullbackFiberCompIso (D.obj f hf) ε
              (eqToHom (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2)).inv) ≫
        (IsPreFibered.pullbackMap (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2
          (eqToHom (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2))) :=
    inferInstance
  have := t1
  have t2 :
    q.IsHomLift
      (q.map
          (Fiber.fiberInclusion.map
            (D.iso (c3_hhf p q D ζ hζc f hf) hf
                (p.map (q.map (IsPreFibered.pullbackMap (D.obj f hf).2 ε)))
                ((eqToHom (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2) ≫ ε)
                (c3_hEf p q D ζ hζc f hf ε)).hom) ≫
        q.map
          (Fiber.fiberInclusion.map
            (pullbackFiberCompIso (D.obj f hf) ε
                (eqToHom (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2)).inv) ≫
        q.map
          (IsPreFibered.pullbackMap (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2
            (eqToHom (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2)))
      ((Fiber.fiberInclusion.map
          (D.iso (c3_hhf p q D ζ hζc f hf) hf
              (p.map (q.map (IsPreFibered.pullbackMap (D.obj f hf).2 ε)))
              ((eqToHom (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2) ≫ ε)
              (c3_hEf p q D ζ hζc f hf ε)).hom) ≫
        (Fiber.fiberInclusion.map
          (pullbackFiberCompIso (D.obj f hf) ε
              (eqToHom (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2)).inv) ≫
        (IsPreFibered.pullbackMap (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2
          (eqToHom (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2))) :=
    inferInstance
  have := t2
  have hthl :
    q.IsHomLift (𝟙 (q.obj (pullbackFiber (q ⋙ p) (D.obj f hf) ε).1))
      ((c3_tau p q D ζ hζc (ζ f hf) (c3_hhf p q D ζ hζc f hf)
          (q.map (IsPreFibered.pullbackMap (D.obj f hf).2 ε))
          (p.map (q.map (IsPreFibered.pullbackMap (D.obj f hf).2 ε))) rfl) ≫
        (Fiber.fiberInclusion.map
          (D.iso (c3_hhf p q D ζ hζc f hf) hf
              (p.map (q.map (IsPreFibered.pullbackMap (D.obj f hf).2 ε)))
              ((eqToHom (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2) ≫ ε)
              (c3_hEf p q D ζ hζc f hf ε)).hom) ≫
        (Fiber.fiberInclusion.map
          (pullbackFiberCompIso (D.obj f hf) ε
              (eqToHom (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2)).inv) ≫
        (IsPreFibered.pullbackMap (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2
          (eqToHom (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2))) :=
    c3_homLift_of_eq q (n :=
      ((c3_sigma p q D ζ hζc (ζ f hf) (c3_hhf p q D ζ hζc f hf)
          (q.map (IsPreFibered.pullbackMap (D.obj f hf).2 ε))
          (p.map (q.map (IsPreFibered.pullbackMap (D.obj f hf).2 ε))) rfl) ≫
        q.map
          (Fiber.fiberInclusion.map
            (D.iso (c3_hhf p q D ζ hζc f hf) hf
                (p.map (q.map (IsPreFibered.pullbackMap (D.obj f hf).2 ε)))
                ((eqToHom (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2) ≫ ε)
                (c3_hEf p q D ζ hζc f hf ε)).hom) ≫
        q.map
          (Fiber.fiberInclusion.map
            (pullbackFiberCompIso (D.obj f hf) ε
                (eqToHom (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2)).inv) ≫
        q.map
          (IsPreFibered.pullbackMap (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2
            (eqToHom (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2))))
      inferInstance (c3_that_base p q D ζ hζc hζg f hf ε)
  have := hthl
  have hid :
    q.IsHomLift (𝟙 (q.obj (pullbackFiber (q ⋙ p) (D.obj f hf) ε).1))
      (𝟙 (pullbackFiber (q ⋙ p) (D.obj f hf) ε).1) :=
    IsHomLift.id rfl
  have := hid
  have hcomp :
    q.IsHomLift (𝟙 (q.obj (pullbackFiber (q ⋙ p) (D.obj f hf) ε).1))
      (ω ≫
        ((c3_tau p q D ζ hζc (ζ f hf) (c3_hhf p q D ζ hζc f hf)
            (q.map (IsPreFibered.pullbackMap (D.obj f hf).2 ε))
            (p.map (q.map (IsPreFibered.pullbackMap (D.obj f hf).2 ε))) rfl) ≫
          (Fiber.fiberInclusion.map
            (D.iso (c3_hhf p q D ζ hζc f hf) hf
                (p.map (q.map (IsPreFibered.pullbackMap (D.obj f hf).2 ε)))
                ((eqToHom (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2) ≫ ε)
                (c3_hEf p q D ζ hζc f hf ε)).hom) ≫
          (Fiber.fiberInclusion.map
            (pullbackFiberCompIso (D.obj f hf) ε
                (eqToHom (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2)).inv) ≫
          (IsPreFibered.pullbackMap (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2
            (eqToHom (pullbackFiber (q ⋙ p) (D.obj f hf) ε).2)))) :=
    c3_homLift_comp q (𝟙 _) (𝟙 _) (Category.id_comp _)
  have := hcomp
  have hPfsc := c3_pi_sc' p q (D.obj f hf) ε
  have := hPfsc
  refine
    IsStronglyCartesian.ext q (q.map (IsPreFibered.pullbackMap (D.obj f hf).2 ε))
      (IsPreFibered.pullbackMap (D.obj f hf).2 ε)
      (𝟙 (q.obj (pullbackFiber (q ⋙ p) (D.obj f hf) ε).1)) ?_
  rw [Category.assoc, c3_that_fac p q D ζ hζc f hf ε, hω2, Category.id_comp]

end Final

end CondThree

end CategoryTheory.Functor
