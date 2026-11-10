module

public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.Defs
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.MorGluing
public import StacksFrontier.CategoryTheory.Sites.Stack.TwoFibreProductMorSheafIndependentBase

/-!
# Effective descent in the 2-fibre product, over a base with its own hom universe

Fix a site `(𝒞, J)` and fibred categories `p𝒳 : 𝒳 ⥤ 𝒞`, `p𝒴 : 𝒴 ⥤ 𝒞`, `p𝒮 : 𝒮 ⥤ 𝒞` with
1-morphisms `F : 𝒳 ⥤ 𝒮`, `G : 𝒴 ⥤ 𝒮` of fibred categories over `𝒞`. This file proves condition
(3) of Stacks 026F for the 2-fibre product `𝒳 ×_𝒮 𝒴` — every descent datum relative to a covering
sieve is effective — and packages it with the other two conditions into Stacks 026G, with the hom
universe of the base `𝒞` independent of the common hom universe of `𝒳`, `𝒴` and `𝒮`.

## Main definitions

* `CategoryTheory.TwoFibreProductOver.sieveDescentDatumFst` and
  `CategoryTheory.TwoFibreProductOver.sieveDescentDatumSnd`, the projected descent
  data.

## Main results

* `CategoryTheory.TwoFibreProductOver.exists_vertical_iso_of_component_descent`,
  the glued comparison isomorphism of the descended object;
* `CategoryTheory.TwoFibreProductOver.hasEffectiveDescent_structureFunctor`,
  condition (3) of Stacks 026F for the 2-fibre product, and
  `CategoryTheory.TwoFibreProductOver.isStack_structureFunctor`, Stacks 026G.

## References

* [Stacks Project, Tag 026F](https://stacks.math.columbia.edu/tag/026F)
* [Stacks Project, Tag 026G](https://stacks.math.columbia.edu/tag/026G)
-/

@[expose] public section

namespace CategoryTheory

open Opposite

open _root_.CategoryTheory.Functor

attribute [local implicit_reducible] Functor.Fiber.fiberInclusion

universe vb v u₁ u₂ u₃ u₄

variable {𝒞 : Type u₁} [Category.{vb} 𝒞] {𝒳 : Type u₂} [Category.{v} 𝒳]
  {𝒴 : Type u₃} [Category.{v} 𝒴] {𝒮 : Type u₄} [Category.{v} 𝒮]

namespace TwoFibreProductOver

section Components

variable {p𝒳 : 𝒳 ⥤ 𝒞} {p𝒴 : 𝒴 ⥤ 𝒞} {p𝒮 : 𝒮 ⥤ 𝒞} {F : 𝒳 ⥤ 𝒮} {G : 𝒴 ⥤ 𝒮}

/-! ### The components of a morphism of a fibre are functorial -/

/-- The `𝒳`-component of an identity morphism of a fibre of the 2-fibre product is an identity. -/
@[simp]
lemma fibFstHom_id {V : 𝒞} (P : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber V) :
    fibFstHom (𝟙 P) = 𝟙 (fibFst P) := rfl

/-- The `𝒴`-component of an identity morphism of a fibre of the 2-fibre product is an identity. -/
@[simp]
lemma fibSndHom_id {V : 𝒞} (P : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber V) :
    fibSndHom (𝟙 P) = 𝟙 (fibSnd P) := rfl

/-- Taking the `𝒳`-component of a morphism of a fibre of the 2-fibre product commutes with
composition. -/
@[reassoc]
lemma fibFstHom_comp {V : 𝒞} {P Q R : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber V}
    (Φ : P ⟶ Q) (Ψ : Q ⟶ R) : fibFstHom (Φ ≫ Ψ) = fibFstHom Φ ≫ fibFstHom Ψ := rfl

/-- Taking the `𝒴`-component of a morphism of a fibre of the 2-fibre product commutes with
composition. -/
@[reassoc]
lemma fibSndHom_comp {V : 𝒞} {P Q R : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber V}
    (Φ : P ⟶ Q) (Ψ : Q ⟶ R) : fibSndHom (Φ ≫ Ψ) = fibSndHom Φ ≫ fibSndHom Ψ := rfl

/-- The `𝒳`-component of an isomorphism of the fibre of the 2-fibre product. -/
@[simps]
def fibFstIso {V : 𝒞} {P Q : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber V} (e : P ≅ Q) :
    fibFst P ≅ fibFst Q where
  hom := fibFstHom e.hom
  inv := fibFstHom e.inv
  hom_inv_id := by rw [← fibFstHom_comp, e.hom_inv_id, fibFstHom_id]
  inv_hom_id := by rw [← fibFstHom_comp, e.inv_hom_id, fibFstHom_id]

/-- The `𝒴`-component of an isomorphism of the fibre of the 2-fibre product. -/
@[simps]
def fibSndIso {V : 𝒞} {P Q : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber V} (e : P ≅ Q) :
    fibSnd P ≅ fibSnd Q where
  hom := fibSndHom e.hom
  inv := fibSndHom e.inv
  hom_inv_id := by rw [← fibSndHom_comp, e.hom_inv_id, fibSndHom_id]
  inv_hom_id := by rw [← fibSndHom_comp, e.inv_hom_id, fibSndHom_id]

/-! ### The componentwise comparison and iterated chosen pullbacks -/

/-- A family of cartesian morphisms `ζ` of `p𝒳` is sent by a fibred 1-morphism `F` to cartesian
morphisms, which are isomorphic over `U` to the chosen pullbacks of the fibre functor image. -/
private theorem exists_fiberIso_of_isCartesian_map [p𝒳.IsFibered] [p𝒮.IsFibered]
    (hF : Functor.IsFibredOneMorphism p𝒳 p𝒮 F) {U : 𝒞} {R : Sieve U}
    {P : ∀ ⦃V : 𝒞⦄ (_ : V ⟶ U), R _ → p𝒳.Fiber V} {x : p𝒳.Fiber U}
    {ζ : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R f), (P f hf).1 ⟶ x.1}
    (hζ : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R f), p𝒳.IsCartesian f (ζ f hf)) :
    ∃ e : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R f),
      (fiberFunctorOfCompEq hF.comp_eq V).obj (P f hf) ≅
        pullbackFiber p𝒮 ((fiberFunctorOfCompEq hF.comp_eq U).obj x) f,
      ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R f),
        Fiber.fiberInclusion.map (e f hf).hom ≫
            IsPreFibered.pullbackMap ((fiberFunctorOfCompEq hF.comp_eq U).obj x).2 f =
          F.map (ζ f hf) := by
  have hFζ : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R f), p𝒮.IsCartesian f (F.map (ζ f hf)) := by
    intro V f hf
    have := hζ f hf
    have := hF.map_isStronglyCartesian f (ζ f hf)
      (IsFibered.isStronglyCartesian_of_isCartesian p𝒳 f (ζ f hf))
    infer_instance
  exact ⟨fun {_V} f hf => fiberIsoOfCartesian f (F.map (ζ f hf))
        (IsPreFibered.pullbackMap ((fiberFunctorOfCompEq hF.comp_eq U).obj x).2 f)
        (hFζ f hf) inferInstance,
      fun {_V} _f _hf => fiberIsoOfCartesian_hom_fac _ _ _ _ _⟩

section Pullback

variable [p𝒳.IsFibered] [p𝒴.IsFibered] [p𝒮.IsFibered]
  [(structureFunctor p𝒳 p𝒴 p𝒮 F G).IsFibered]
  (hF : Functor.IsFibredOneMorphism p𝒳 p𝒮 F) (hG : Functor.IsFibredOneMorphism p𝒴 p𝒮 G)

include hF hG

omit [p𝒮.IsFibered] in
/-- Contracting an iterated chosen pullback commutes with the comparison between the
`𝒳`-component of a chosen pullback in the 2-fibre product and the chosen pullback of the
`𝒳`-component. -/
@[reassoc]
lemma fibFstHom_pullbackFiberCompIso_hom {U V Z : 𝒞}
    (P : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber U) (f : V ⟶ U) (γ : Z ⟶ V) :
    fibFstHom (pullbackFiberCompIso P f γ).hom ≫
        (pullbackFiberFstIso hF hG P (γ ≫ f)).hom =
      (pullbackFiberFstIso hF hG (pullbackFiber (structureFunctor p𝒳 p𝒴 p𝒮 F G) P f) γ).hom ≫
        pullbackFiberHom (pullbackFiberFstIso hF hG P f).hom γ ≫
        (pullbackFiberCompIso (fibFst P) f γ).hom := by
  have hprod := congrArg (fun Φ => Φ.a) (pullbackFiberCompIso_hom_fac P f γ)
  simp only [comp_a] at hprod
  refine fiber_hom_ext_of_cartesian (γ ≫ f) (IsPreFibered.pullbackMap (fibFst P).2 (γ ≫ f))
    (IsPreFibered.pullbackMap.IsCartesian _ _) _ _ ?_
  simp only [Functor.map_comp, Category.assoc, fiberInclusion_map_fibFstHom,
    pullbackFiberFstIso_hom_fac, pullbackFiberCompIso_hom_fac, pullbackFiberHom_fac_assoc,
    pullbackFiberFstIso_hom_fac_assoc]
  exact hprod

omit [p𝒮.IsFibered] in
/-- The `𝒴`-component analogue of `fibFstHom_pullbackFiberCompIso_hom`. -/
@[reassoc]
lemma fibSndHom_pullbackFiberCompIso_hom {U V Z : 𝒞}
    (P : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber U) (f : V ⟶ U) (γ : Z ⟶ V) :
    fibSndHom (pullbackFiberCompIso P f γ).hom ≫
        (pullbackFiberSndIso hF hG P (γ ≫ f)).hom =
      (pullbackFiberSndIso hF hG (pullbackFiber (structureFunctor p𝒳 p𝒴 p𝒮 F G) P f) γ).hom ≫
        pullbackFiberHom (pullbackFiberSndIso hF hG P f).hom γ ≫
        (pullbackFiberCompIso (fibSnd P) f γ).hom := by
  have hprod := congrArg (fun Φ => Φ.b) (pullbackFiberCompIso_hom_fac P f γ)
  simp only [comp_b] at hprod
  refine fiber_hom_ext_of_cartesian (γ ≫ f) (IsPreFibered.pullbackMap (fibSnd P).2 (γ ≫ f))
    (IsPreFibered.pullbackMap.IsCartesian _ _) _ _ ?_
  simp only [Functor.map_comp, Category.assoc, fiberInclusion_map_fibSndHom,
    pullbackFiberSndIso_hom_fac, pullbackFiberCompIso_hom_fac, pullbackFiberHom_fac_assoc,
    pullbackFiberSndIso_hom_fac_assoc]
  exact hprod

omit [p𝒮.IsFibered] in
/-- `fibFstHom_pullbackFiberCompIso_hom` read on inverses. -/
@[reassoc]
lemma fibFstHom_pullbackFiberCompIso_inv {U V Z : 𝒞}
    (P : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber U) (f : V ⟶ U) (γ : Z ⟶ V) :
    (pullbackFiberFstIso hF hG P (γ ≫ f)).inv ≫ fibFstHom (pullbackFiberCompIso P f γ).inv ≫
        (pullbackFiberFstIso hF hG (pullbackFiber (structureFunctor p𝒳 p𝒴 p𝒮 F G) P f) γ).hom =
      (pullbackFiberCompIso (fibFst P) f γ).inv ≫
        pullbackFiberHom (pullbackFiberFstIso hF hG P f).inv γ := by
  have h : fibFstIso (pullbackFiberCompIso P f γ) ≪≫ pullbackFiberFstIso hF hG P (γ ≫ f) =
      pullbackFiberFstIso hF hG (pullbackFiber (structureFunctor p𝒳 p𝒴 p𝒮 F G) P f) γ ≪≫
        pullbackFiberIso (pullbackFiberFstIso hF hG P f) γ ≪≫
        pullbackFiberCompIso (fibFst P) f γ :=
    Iso.ext (by
      simpa only [Iso.trans_hom, fibFstIso_hom, pullbackFiberIso_hom, Category.assoc] using
        fibFstHom_pullbackFiberCompIso_hom hF hG P f γ)
  have h2 := congrArg Iso.inv h
  simp only [Iso.trans_inv, fibFstIso_inv, pullbackFiberIso_inv, Category.assoc] at h2
  rw [← Category.assoc, h2]
  simp

omit [p𝒮.IsFibered] in
/-- The `𝒴`-component analogue of `fibFstHom_pullbackFiberCompIso_inv`. -/
@[reassoc]
lemma fibSndHom_pullbackFiberCompIso_inv {U V Z : 𝒞}
    (P : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber U) (f : V ⟶ U) (γ : Z ⟶ V) :
    (pullbackFiberSndIso hF hG P (γ ≫ f)).inv ≫ fibSndHom (pullbackFiberCompIso P f γ).inv ≫
        (pullbackFiberSndIso hF hG (pullbackFiber (structureFunctor p𝒳 p𝒴 p𝒮 F G) P f) γ).hom =
      (pullbackFiberCompIso (fibSnd P) f γ).inv ≫
        pullbackFiberHom (pullbackFiberSndIso hF hG P f).inv γ := by
  have h : fibSndIso (pullbackFiberCompIso P f γ) ≪≫ pullbackFiberSndIso hF hG P (γ ≫ f) =
      pullbackFiberSndIso hF hG (pullbackFiber (structureFunctor p𝒳 p𝒴 p𝒮 F G) P f) γ ≪≫
        pullbackFiberIso (pullbackFiberSndIso hF hG P f) γ ≪≫
        pullbackFiberCompIso (fibSnd P) f γ :=
    Iso.ext (by
      simpa only [Iso.trans_hom, fibSndIso_hom, pullbackFiberIso_hom, Category.assoc] using
        fibSndHom_pullbackFiberCompIso_hom hF hG P f γ)
  have h2 := congrArg Iso.inv h
  simp only [Iso.trans_inv, fibSndIso_inv, pullbackFiberIso_inv, Category.assoc] at h2
  rw [← Category.assoc, h2]
  simp

omit [p𝒮.IsFibered] in
/-- The comparison between the `𝒳`-component of a chosen pullback in the 2-fibre product and the
chosen pullback of the `𝒳`-component is natural in the object of the fibre. -/
@[reassoc]
lemma pullbackFiberFstIso_hom_naturality {V Z : 𝒞}
    {Q Q' : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber V} (Ψ : Q ⟶ Q') (γ : Z ⟶ V) :
    fibFstHom (pullbackFiberHom Ψ γ) ≫ (pullbackFiberFstIso hF hG Q' γ).hom =
      (pullbackFiberFstIso hF hG Q γ).hom ≫ pullbackFiberHom (fibFstHom Ψ) γ := by
  have hprod := congrArg (fun Φ => Φ.a) (pullbackFiberHom_fac Ψ γ)
  simp only [comp_a] at hprod
  refine fiber_hom_ext_of_cartesian γ (IsPreFibered.pullbackMap (fibFst Q').2 γ)
    (IsPreFibered.pullbackMap.IsCartesian _ _) _ _ ?_
  simp only [Functor.map_comp, Category.assoc, fiberInclusion_map_fibFstHom,
    pullbackFiberFstIso_hom_fac, pullbackFiberHom_fac, pullbackFiberFstIso_hom_fac_assoc]
  exact hprod

omit [p𝒮.IsFibered] in
/-- The `𝒴`-component analogue of `pullbackFiberFstIso_hom_naturality`. -/
@[reassoc]
lemma pullbackFiberSndIso_hom_naturality {V Z : 𝒞}
    {Q Q' : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber V} (Ψ : Q ⟶ Q') (γ : Z ⟶ V) :
    fibSndHom (pullbackFiberHom Ψ γ) ≫ (pullbackFiberSndIso hF hG Q' γ).hom =
      (pullbackFiberSndIso hF hG Q γ).hom ≫ pullbackFiberHom (fibSndHom Ψ) γ := by
  have hprod := congrArg (fun Φ => Φ.b) (pullbackFiberHom_fac Ψ γ)
  simp only [comp_b] at hprod
  refine fiber_hom_ext_of_cartesian γ (IsPreFibered.pullbackMap (fibSnd Q').2 γ)
    (IsPreFibered.pullbackMap.IsCartesian _ _) _ _ ?_
  simp only [Functor.map_comp, Category.assoc, fiberInclusion_map_fibSndHom,
    pullbackFiberSndIso_hom_fac, pullbackFiberHom_fac, pullbackFiberSndIso_hom_fac_assoc]
  exact hprod

/-! ### Projecting a descent datum to the two factors -/

/-- The `𝒳`-component of a gluing isomorphism of a descent datum in the 2-fibre product,
transported to the chosen pullbacks taken in `𝒳`. -/
noncomputable def descentIsoFst {U : 𝒞} {R : Sieve U}
    (D : SieveDescentDatum (structureFunctor p𝒳 p𝒴 p𝒮 F G) R)
    ⦃V W Z : 𝒞⦄ ⦃f : V ⟶ U⦄ (hf : R f) ⦃g : W ⟶ U⦄ (hg : R g)
    (ε : Z ⟶ V) (ε' : Z ⟶ W) (heq : ε ≫ f = ε' ≫ g) :
    pullbackFiber p𝒳 (fibFst (D.obj f hf)) ε ≅ pullbackFiber p𝒳 (fibFst (D.obj g hg)) ε' :=
  (pullbackFiberFstIso hF hG (D.obj f hf) ε).symm ≪≫
    fibFstIso (D.iso hf hg ε ε' heq) ≪≫ pullbackFiberFstIso hF hG (D.obj g hg) ε'

/-- The `𝒴`-component of a gluing isomorphism of a descent datum in the 2-fibre product,
transported to the chosen pullbacks taken in `𝒴`. -/
noncomputable def descentIsoSnd {U : 𝒞} {R : Sieve U}
    (D : SieveDescentDatum (structureFunctor p𝒳 p𝒴 p𝒮 F G) R)
    ⦃V W Z : 𝒞⦄ ⦃f : V ⟶ U⦄ (hf : R f) ⦃g : W ⟶ U⦄ (hg : R g)
    (ε : Z ⟶ V) (ε' : Z ⟶ W) (heq : ε ≫ f = ε' ≫ g) :
    pullbackFiber p𝒴 (fibSnd (D.obj f hf)) ε ≅ pullbackFiber p𝒴 (fibSnd (D.obj g hg)) ε' :=
  (pullbackFiberSndIso hF hG (D.obj f hf) ε).symm ≪≫
    fibSndIso (D.iso hf hg ε ε' heq) ≪≫ pullbackFiberSndIso hF hG (D.obj g hg) ε'

omit [p𝒮.IsFibered] in
/-- The `𝒳`-components `descentIsoFst` of the gluing isomorphisms of a descent datum in the
2-fibre product satisfy the cocycle condition. -/
lemma descentIsoFst_cocycle {U : 𝒞} {R : Sieve U}
    (D : SieveDescentDatum (structureFunctor p𝒳 p𝒴 p𝒮 F G) R)
    ⦃V W X Z : 𝒞⦄ ⦃f : V ⟶ U⦄ (hf : R f) ⦃g : W ⟶ U⦄ (hg : R g) ⦃h : X ⟶ U⦄ (hh : R h)
    (ε₁ : Z ⟶ V) (ε₂ : Z ⟶ W) (ε₃ : Z ⟶ X)
    (h₁₂ : ε₁ ≫ f = ε₂ ≫ g) (h₂₃ : ε₂ ≫ g = ε₃ ≫ h) (h₁₃ : ε₁ ≫ f = ε₃ ≫ h) :
    (descentIsoFst hF hG D hf hg ε₁ ε₂ h₁₂).hom ≫
        (descentIsoFst hF hG D hg hh ε₂ ε₃ h₂₃).hom =
      (descentIsoFst hF hG D hf hh ε₁ ε₃ h₁₃).hom := by
  simp only [descentIsoFst, Iso.trans_hom, Iso.symm_hom, Category.assoc, fibFstIso_hom,
    Iso.hom_inv_id_assoc]
  rw [← fibFstHom_comp_assoc, D.cocycle hf hg hh ε₁ ε₂ ε₃ h₁₂ h₂₃ h₁₃]

omit [p𝒮.IsFibered] in
/-- The `𝒴`-components `descentIsoSnd` of the gluing isomorphisms of a descent datum in the
2-fibre product satisfy the cocycle condition. -/
lemma descentIsoSnd_cocycle {U : 𝒞} {R : Sieve U}
    (D : SieveDescentDatum (structureFunctor p𝒳 p𝒴 p𝒮 F G) R)
    ⦃V W X Z : 𝒞⦄ ⦃f : V ⟶ U⦄ (hf : R f) ⦃g : W ⟶ U⦄ (hg : R g) ⦃h : X ⟶ U⦄ (hh : R h)
    (ε₁ : Z ⟶ V) (ε₂ : Z ⟶ W) (ε₃ : Z ⟶ X)
    (h₁₂ : ε₁ ≫ f = ε₂ ≫ g) (h₂₃ : ε₂ ≫ g = ε₃ ≫ h) (h₁₃ : ε₁ ≫ f = ε₃ ≫ h) :
    (descentIsoSnd hF hG D hf hg ε₁ ε₂ h₁₂).hom ≫
        (descentIsoSnd hF hG D hg hh ε₂ ε₃ h₂₃).hom =
      (descentIsoSnd hF hG D hf hh ε₁ ε₃ h₁₃).hom := by
  simp only [descentIsoSnd, Iso.trans_hom, Iso.symm_hom, Category.assoc, fibSndIso_hom,
    Iso.hom_inv_id_assoc]
  rw [← fibSndHom_comp_assoc, D.cocycle hf hg hh ε₁ ε₂ ε₃ h₁₂ h₂₃ h₁₃]

omit [p𝒮.IsFibered] in
/-- The `𝒳`-components `descentIsoFst` of the gluing isomorphisms of a descent datum in the
2-fibre product are compatible with base change along `γ`, once the iterated chosen pullbacks are
contracted. -/
lemma descentIsoFst_pullback {U : 𝒞} {R : Sieve U}
    (D : SieveDescentDatum (structureFunctor p𝒳 p𝒴 p𝒮 F G) R)
    ⦃V W Z Z' : 𝒞⦄ ⦃f : V ⟶ U⦄ (hf : R f) ⦃g : W ⟶ U⦄ (hg : R g)
    (ε : Z ⟶ V) (ε' : Z ⟶ W) (heq : ε ≫ f = ε' ≫ g) (γ : Z' ⟶ Z) :
    (pullbackFiberCompIso (fibFst (D.obj f hf)) ε γ).inv ≫
          (pullbackFiberIso (descentIsoFst hF hG D hf hg ε ε' heq) γ).hom ≫
          (pullbackFiberCompIso (fibFst (D.obj g hg)) ε' γ).hom =
      (descentIsoFst hF hG D hf hg (γ ≫ ε) (γ ≫ ε')
        (by rw [Category.assoc, Category.assoc, heq])).hom := by
  simp only [descentIsoFst, Iso.trans_hom, Iso.symm_hom, fibFstIso_hom, pullbackFiberIso_hom]
  rw [← D.iso_pullback hf hg ε ε' heq γ]
  simp only [fibFstHom_comp, pullbackFiberHom_comp, pullbackFiberIso_hom, Category.assoc]
  rw [fibFstHom_pullbackFiberCompIso_hom, pullbackFiberFstIso_hom_naturality_assoc,
    fibFstHom_pullbackFiberCompIso_inv_assoc]

omit [p𝒮.IsFibered] in
/-- The `𝒴`-components `descentIsoSnd` of the gluing isomorphisms of a descent datum in the
2-fibre product are compatible with base change along `γ`, once the iterated chosen pullbacks are
contracted. -/
lemma descentIsoSnd_pullback {U : 𝒞} {R : Sieve U}
    (D : SieveDescentDatum (structureFunctor p𝒳 p𝒴 p𝒮 F G) R)
    ⦃V W Z Z' : 𝒞⦄ ⦃f : V ⟶ U⦄ (hf : R f) ⦃g : W ⟶ U⦄ (hg : R g)
    (ε : Z ⟶ V) (ε' : Z ⟶ W) (heq : ε ≫ f = ε' ≫ g) (γ : Z' ⟶ Z) :
    (pullbackFiberCompIso (fibSnd (D.obj f hf)) ε γ).inv ≫
          (pullbackFiberIso (descentIsoSnd hF hG D hf hg ε ε' heq) γ).hom ≫
          (pullbackFiberCompIso (fibSnd (D.obj g hg)) ε' γ).hom =
      (descentIsoSnd hF hG D hf hg (γ ≫ ε) (γ ≫ ε')
        (by rw [Category.assoc, Category.assoc, heq])).hom := by
  simp only [descentIsoSnd, Iso.trans_hom, Iso.symm_hom, fibSndIso_hom, pullbackFiberIso_hom]
  rw [← D.iso_pullback hf hg ε ε' heq γ]
  simp only [fibSndHom_comp, pullbackFiberHom_comp, pullbackFiberIso_hom, Category.assoc]
  rw [fibSndHom_pullbackFiberCompIso_hom, pullbackFiberSndIso_hom_naturality_assoc,
    fibSndHom_pullbackFiberCompIso_inv_assoc]

/-- The `𝒳`-component of a descent datum in the 2-fibre product: a descent datum in `𝒳` relative
to the same sieve. -/
noncomputable def sieveDescentDatumFst {U : 𝒞} {R : Sieve U}
    (D : SieveDescentDatum (structureFunctor p𝒳 p𝒴 p𝒮 F G) R) : SieveDescentDatum p𝒳 R where
  obj {_V} f hf := fibFst (D.obj f hf)
  iso {_V _W _Z} {_f} hf {_g} hg ε ε' heq := descentIsoFst hF hG D hf hg ε ε' heq
  cocycle {_V _W _X _Z} {_f} hf {_g} hg {_h} hh ε₁ ε₂ ε₃ h₁₂ h₂₃ h₁₃ :=
    descentIsoFst_cocycle hF hG D hf hg hh ε₁ ε₂ ε₃ h₁₂ h₂₃ h₁₃
  iso_pullback {_V _W _Z _Z'} {_f} hf {_g} hg ε ε' heq γ :=
    descentIsoFst_pullback hF hG D hf hg ε ε' heq γ

/-- The `𝒴`-component of a descent datum in the 2-fibre product. -/
noncomputable def sieveDescentDatumSnd {U : 𝒞} {R : Sieve U}
    (D : SieveDescentDatum (structureFunctor p𝒳 p𝒴 p𝒮 F G) R) : SieveDescentDatum p𝒴 R where
  obj {_V} f hf := fibSnd (D.obj f hf)
  iso {_V _W _Z} {_f} hf {_g} hg ε ε' heq := descentIsoSnd hF hG D hf hg ε ε' heq
  cocycle {_V _W _X _Z} {_f} hf {_g} hg {_h} hh ε₁ ε₂ ε₃ h₁₂ h₂₃ h₁₃ :=
    descentIsoSnd_cocycle hF hG D hf hg hh ε₁ ε₂ ε₃ h₁₂ h₂₃ h₁₃
  iso_pullback {_V _W _Z _Z'} {_f} hf {_g} hg ε ε' heq γ :=
    descentIsoSnd_pullback hF hG D hf hg ε ε' heq γ

omit [p𝒮.IsFibered] in
/-- The object of `sieveDescentDatumFst` over an arrow of the sieve is the `𝒳`-component of the
object of the original descent datum. -/
@[simp]
lemma sieveDescentDatumFst_obj {U : 𝒞} {R : Sieve U}
    (D : SieveDescentDatum (structureFunctor p𝒳 p𝒴 p𝒮 F G) R) ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R f) :
    (sieveDescentDatumFst hF hG D).obj f hf = fibFst (D.obj f hf) := rfl

omit [p𝒮.IsFibered] in
/-- The object of `sieveDescentDatumSnd` over an arrow of the sieve is the `𝒴`-component of the
object of the original descent datum. -/
@[simp]
lemma sieveDescentDatumSnd_obj {U : 𝒞} {R : Sieve U}
    (D : SieveDescentDatum (structureFunctor p𝒳 p𝒴 p𝒮 F G) R) ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R f) :
    (sieveDescentDatumSnd hF hG D).obj f hf = fibSnd (D.obj f hf) := rfl

/-! ### Effective descent -/

omit [p𝒮.IsFibered] in
/-- A family of morphisms compatible with the projected gluing isomorphism `descentIsoFst` and the
chosen pullbacks taken in `𝒳` is compatible with the `𝒳`-components of the gluing isomorphism of
`D` and of the chosen cartesian lifts taken in the 2-fibre product. -/
lemma descentIsoFst_fac_a {U : 𝒞} {R : Sieve U}
    (D : SieveDescentDatum (structureFunctor p𝒳 p𝒴 p𝒮 F G) R) {z : 𝒳}
    ⦃V W Z : 𝒞⦄ ⦃f : V ⟶ U⦄ (hf : R f) ⦃g : W ⟶ U⦄ (hg : R g)
    (ε : Z ⟶ V) (ε' : Z ⟶ W) (heq : ε ≫ f = ε' ≫ g)
    (ζf : (fibFst (D.obj f hf)).1 ⟶ z) (ζg : (fibFst (D.obj g hg)).1 ⟶ z)
    (h : Fiber.fiberInclusion.map (descentIsoFst hF hG D hf hg ε ε' heq).hom ≫
        IsPreFibered.pullbackMap (fibFst (D.obj g hg)).2 ε' ≫ ζg =
      IsPreFibered.pullbackMap (fibFst (D.obj f hf)).2 ε ≫ ζf) :
    (Fiber.fiberInclusion.map (D.iso hf hg ε ε' heq).hom).a ≫
        (IsPreFibered.pullbackMap (D.obj g hg).2 ε').a ≫ ζg =
      (IsPreFibered.pullbackMap (D.obj f hf).2 ε).a ≫ ζf := by
  rw [← pullbackFiberFstIso_hom_fac_assoc hF hG (D.obj f hf) ε ζf, ← h]
  simp [descentIsoFst, Iso.trans_hom, Iso.symm_hom, fibFstIso_hom, Functor.map_comp,
    Category.assoc, fiberInclusion_map_fibFstHom,
    pullbackFiberFstIso_hom_fac_assoc]

omit [p𝒮.IsFibered] in
/-- The `𝒴`-component analogue of `descentIsoFst_fac_a`. -/
lemma descentIsoSnd_fac_b {U : 𝒞} {R : Sieve U}
    (D : SieveDescentDatum (structureFunctor p𝒳 p𝒴 p𝒮 F G) R) {z : 𝒴}
    ⦃V W Z : 𝒞⦄ ⦃f : V ⟶ U⦄ (hf : R f) ⦃g : W ⟶ U⦄ (hg : R g)
    (ε : Z ⟶ V) (ε' : Z ⟶ W) (heq : ε ≫ f = ε' ≫ g)
    (ζf : (fibSnd (D.obj f hf)).1 ⟶ z) (ζg : (fibSnd (D.obj g hg)).1 ⟶ z)
    (h : Fiber.fiberInclusion.map (descentIsoSnd hF hG D hf hg ε ε' heq).hom ≫
        IsPreFibered.pullbackMap (fibSnd (D.obj g hg)).2 ε' ≫ ζg =
      IsPreFibered.pullbackMap (fibSnd (D.obj f hf)).2 ε ≫ ζf) :
    (Fiber.fiberInclusion.map (D.iso hf hg ε ε' heq).hom).b ≫
        (IsPreFibered.pullbackMap (D.obj g hg).2 ε').b ≫ ζg =
      (IsPreFibered.pullbackMap (D.obj f hf).2 ε).b ≫ ζf := by
  rw [← pullbackFiberSndIso_hom_fac_assoc hF hG (D.obj f hf) ε ζf, ← h]
  simp [descentIsoSnd, Iso.trans_hom, Iso.symm_hom, fibSndIso_hom, Functor.map_comp,
    Category.assoc, fiberInclusion_map_fibSndHom,
    pullbackFiberSndIso_hom_fac_assoc]

omit [p𝒮.IsFibered] in
/-- For an arrow `f` of `R` and a further morphism `γ` whose composite `b = γ ≫ f` is again in `R`,
the two descended objects `x_b`, `y_b` map to `x_f`, `y_f` by a single morphism of the 2-fibre
product lying over `γ`, compatibly with the cartesian morphisms `ζx`, `ζy` that exhibit the descent
of the two components. -/
lemma exists_hom_of_descentGlue {U : 𝒞} {R : Sieve U}
    (D : SieveDescentDatum (structureFunctor p𝒳 p𝒴 p𝒮 F G) R)
    {x : p𝒳.Fiber U} {y : p𝒴.Fiber U}
    {ζx : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R f), (fibFst (D.obj f hf)).1 ⟶ x.1}
    {ζy : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R f), (fibSnd (D.obj f hf)).1 ⟶ y.1}
    (hgx : ∀ ⦃V W Z : 𝒞⦄ ⦃f : V ⟶ U⦄ (hf : R f) ⦃g : W ⟶ U⦄ (hg : R g)
      (ε : Z ⟶ V) (ε' : Z ⟶ W) (heq : ε ≫ f = ε' ≫ g),
      Fiber.fiberInclusion.map (descentIsoFst hF hG D hf hg ε ε' heq).hom ≫
          IsPreFibered.pullbackMap (fibFst (D.obj g hg)).2 ε' ≫ ζx g hg =
        IsPreFibered.pullbackMap (fibFst (D.obj f hf)).2 ε ≫ ζx f hf)
    (hgy : ∀ ⦃V W Z : 𝒞⦄ ⦃f : V ⟶ U⦄ (hf : R f) ⦃g : W ⟶ U⦄ (hg : R g)
      (ε : Z ⟶ V) (ε' : Z ⟶ W) (heq : ε ≫ f = ε' ≫ g),
      Fiber.fiberInclusion.map (descentIsoSnd hF hG D hf hg ε ε' heq).hom ≫
          IsPreFibered.pullbackMap (fibSnd (D.obj g hg)).2 ε' ≫ ζy g hg =
        IsPreFibered.pullbackMap (fibSnd (D.obj f hf)).2 ε ≫ ζy f hf)
    ⦃V W : 𝒞⦄ (f : V ⟶ U) (hf : R f) (γ : W ⟶ V) (b : W ⟶ U) (hb : γ ≫ f = b) (hb' : R b) :
    ∃ Λ : (D.obj b hb').1 ⟶ (D.obj f hf).1, p𝒳.IsHomLift γ Λ.a ∧
      Λ.a ≫ ζx f hf = ζx b hb' ∧ Λ.b ≫ ζy f hf = ζy b hb' := by
  have heq : γ ≫ f = 𝟙 W ≫ b := by rw [Category.id_comp, hb]
  have hpm : (structureFunctor p𝒳 p𝒴 p𝒮 F G).IsCartesian γ
      (IsPreFibered.pullbackMap (D.obj f hf).2 γ) := IsPreFibered.pullbackMap.IsCartesian _ _
  have hpm' := hpm.toIsHomLift
  refine ⟨Fiber.fiberInclusion.map (pullbackFiberIdIso (D.obj b hb')).inv ≫
      Fiber.fiberInclusion.map (D.iso hf hb' γ (𝟙 W) heq).inv ≫
      IsPreFibered.pullbackMap (D.obj f hf).2 γ, ?_, ?_, ?_⟩
  · refine isHomLift_a _ γ ?_
    have h0 : (structureFunctor p𝒳 p𝒴 p𝒮 F G).IsHomLift (𝟙 W ≫ 𝟙 W ≫ γ)
        (Fiber.fiberInclusion.map (pullbackFiberIdIso (D.obj b hb')).inv ≫
          Fiber.fiberInclusion.map (D.iso hf hb' γ (𝟙 W) heq).inv ≫
          IsPreFibered.pullbackMap (D.obj f hf).2 γ) := inferInstance
    simpa using h0
  all_goals
    have key : Fiber.fiberInclusion.map (pullbackFiberIdIso (D.obj b hb')).inv ≫
        Fiber.fiberInclusion.map (D.iso hf hb' γ (𝟙 W) heq).inv ≫
        Fiber.fiberInclusion.map (D.iso hf hb' γ (𝟙 W) heq).hom ≫
        IsPreFibered.pullbackMap (D.obj b hb').2 (𝟙 W) = 𝟙 (D.obj b hb').1 := by
      simp [pullbackFiberIdIso_inv_fac]
  · have hax := descentIsoFst_fac_a hF hG D hf hb' γ (𝟙 W) heq (ζx f hf) (ζx b hb')
      (hgx hf hb' γ (𝟙 W) heq)
    have h := congrArg (fun Φ => Φ.a ≫ ζx b hb') key
    simp only [comp_a, id_a, Category.assoc] at h
    simp only [comp_a, Category.assoc]
    rw [← hax]
    exact h.trans (Category.id_comp _)
  · have hby := descentIsoSnd_fac_b hF hG D hf hb' γ (𝟙 W) heq (ζy f hf) (ζy b hb')
      (hgy hf hb' γ (𝟙 W) heq)
    have h := congrArg (fun Φ => Φ.b ≫ ζy b hb') key
    simp only [comp_b, id_b, Category.assoc] at h
    simp only [comp_b, Category.assoc]
    rw [← hby]
    exact h.trans (Category.id_comp _)

/-- Given the two component descents of a descent datum in the 2-fibre product relative to a
covering sieve, the isomorphisms `φ_f` carried by its objects glue to a vertical isomorphism
`φ : F x ≅ G y` over `U`, compatible with the cartesian morphisms `ζx`, `ζy` that exhibit those
descents. -/
lemma exists_vertical_iso_of_component_descent (J : GrothendieckTopology 𝒞)
    (m𝒮 : ∀ (T : 𝒞) (a b : p𝒮.Fiber T), IsMorSheaf p𝒮 J T a b)
    {U : 𝒞} {R : Sieve U} (hR : R ∈ J U)
    (D : SieveDescentDatum (structureFunctor p𝒳 p𝒴 p𝒮 F G) R)
    (x : p𝒳.Fiber U) (y : p𝒴.Fiber U)
    (ζx : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R f), (fibFst (D.obj f hf)).1 ⟶ x.1)
    (ζy : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R f), (fibSnd (D.obj f hf)).1 ⟶ y.1)
    (hζx : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R f), p𝒳.IsCartesian f (ζx f hf))
    (hζy : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R f), p𝒴.IsCartesian f (ζy f hf))
    (hgx : ∀ ⦃V W Z : 𝒞⦄ ⦃f : V ⟶ U⦄ (hf : R f) ⦃g : W ⟶ U⦄ (hg : R g)
      (ε : Z ⟶ V) (ε' : Z ⟶ W) (heq : ε ≫ f = ε' ≫ g),
      Fiber.fiberInclusion.map (descentIsoFst hF hG D hf hg ε ε' heq).hom ≫
          IsPreFibered.pullbackMap (fibFst (D.obj g hg)).2 ε' ≫ ζx g hg =
        IsPreFibered.pullbackMap (fibFst (D.obj f hf)).2 ε ≫ ζx f hf)
    (hgy : ∀ ⦃V W Z : 𝒞⦄ ⦃f : V ⟶ U⦄ (hf : R f) ⦃g : W ⟶ U⦄ (hg : R g)
      (ε : Z ⟶ V) (ε' : Z ⟶ W) (heq : ε ≫ f = ε' ≫ g),
      Fiber.fiberInclusion.map (descentIsoSnd hF hG D hf hg ε ε' heq).hom ≫
          IsPreFibered.pullbackMap (fibSnd (D.obj g hg)).2 ε' ≫ ζy g hg =
        IsPreFibered.pullbackMap (fibSnd (D.obj f hf)).2 ε ≫ ζy f hf) :
    ∃ φ : F.obj x.1 ≅ G.obj y.1, p𝒮.IsHomLift (𝟙 U) φ.hom ∧
      ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R f),
        F.map (ζx f hf) ≫ φ.hom = (D.obj f hf).1.iso.hom ≫ G.map (ζy f hf) := by
  obtain ⟨eF, heF⟩ := exists_fiberIso_of_isCartesian_map hF hζx
  obtain ⟨eG, heG⟩ := exists_fiberIso_of_isCartesian_map hG hζy
  obtain ⟨θ, hθfac⟩ : ∃ θ : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (_ : R f),
      pullbackFiber p𝒮 ((fiberFunctorOfCompEq hF.comp_eq U).obj x) f ≅
        pullbackFiber p𝒮 ((fiberFunctorOfCompEq hG.comp_eq U).obj y) f,
      ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R f),
        Fiber.fiberInclusion.map (eF f hf).hom ≫ Fiber.fiberInclusion.map (θ f hf).hom ≫
            IsPreFibered.pullbackMap ((fiberFunctorOfCompEq hG.comp_eq U).obj y).2 f =
          (D.obj f hf).1.iso.hom ≫ G.map (ζy f hf) := by
    refine ⟨fun {_V} f hf => (eF f hf).symm ≪≫ fibIso hF hG (D.obj f hf) ≪≫ eG f hf,
      fun {_V} f hf => ?_⟩
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.map_comp, Category.assoc,
      fiberInclusion_map_fibIso_hom, Iso.hom_inv_id_map_assoc]
    rw [heG f hf]
  have hcrux : ∀ ⦃V W : 𝒞⦄ (f : V ⟶ U) (hf : R f) (γ : W ⟶ V) (b : W ⟶ U) (_hb : γ ≫ f = b)
      (hb' : R b)
      (κ : (pullbackFiber p𝒮 ((fiberFunctorOfCompEq hF.comp_eq U).obj x) b).1 ⟶
        (pullbackFiber p𝒮 ((fiberFunctorOfCompEq hF.comp_eq U).obj x) f).1),
      p𝒮.IsHomLift γ κ →
      κ ≫ IsPreFibered.pullbackMap ((fiberFunctorOfCompEq hF.comp_eq U).obj x).2 f =
        IsPreFibered.pullbackMap ((fiberFunctorOfCompEq hF.comp_eq U).obj x).2 b →
      Fiber.fiberInclusion.map (θ b hb').hom ≫
          IsPreFibered.pullbackMap ((fiberFunctorOfCompEq hG.comp_eq U).obj y).2 b =
        κ ≫ Fiber.fiberInclusion.map (θ f hf).hom ≫
          IsPreFibered.pullbackMap ((fiberFunctorOfCompEq hG.comp_eq U).obj y).2 f := by
    intro V W f hf γ b hb hb' κ hκlift hκfac
    obtain ⟨Λ, hΛlift, hΛa, hΛb⟩ := exists_hom_of_descentGlue hF hG D hgx hgy f hf γ b hb hb'
    have hdb : IsIso (Fiber.fiberInclusion.map (eF b hb').hom) := inferInstance
    have hclaim : Fiber.fiberInclusion.map (eF b hb').hom ≫ κ =
        F.map Λ.a ≫ Fiber.fiberInclusion.map (eF f hf).hom := by
      have h1 : p𝒮.IsHomLift γ (Fiber.fiberInclusion.map (eF b hb').hom ≫ κ) := by
        have := hκlift
        have h0 : p𝒮.IsHomLift (𝟙 W ≫ γ)
            (Fiber.fiberInclusion.map (eF b hb').hom ≫ κ) := inferInstance
        simpa using h0
      have h2 : p𝒮.IsHomLift γ (F.map Λ.a ≫ Fiber.fiberInclusion.map (eF f hf).hom) := by
        have := hΛlift
        have := hF.map_isHomLift γ Λ.a
        have h0 : p𝒮.IsHomLift (γ ≫ 𝟙 V)
            (F.map Λ.a ≫ Fiber.fiberInclusion.map (eF f hf).hom) := inferInstance
        simpa using h0
      have := h1
      have := h2
      refine IsStronglyCartesian.ext p𝒮 f
        (IsPreFibered.pullbackMap ((fiberFunctorOfCompEq hF.comp_eq U).obj x).2 f) γ ?_
      rw [Category.assoc, Category.assoc, hκfac, heF b hb', heF f hf, ← Functor.map_comp, hΛa]
    rw [← cancel_epi (Fiber.fiberInclusion.map (eF b hb').hom), hθfac b hb', ← Category.assoc,
      hclaim, Category.assoc, hθfac f hf, ← Category.assoc, Λ.w, Category.assoc,
      ← Functor.map_comp, hΛb]
  have hθcompat : ∀ ⦃V W : 𝒞⦄ (f : V ⟶ U) (hf : R f) (γ : W ⟶ V) (b : W ⟶ U) (hb : γ ≫ f = b)
      (hb' : R b), (θ b hb').hom =
        (pullbackFiberCompIso' ((fiberFunctorOfCompEq hF.comp_eq U).obj x) f γ b hb).inv ≫
          pullbackFiberHom (θ f hf).hom γ ≫
          (pullbackFiberCompIso' ((fiberFunctorOfCompEq hG.comp_eq U).obj y) f γ b hb).hom := by
    intro V W f hf γ b hb hb'
    refine fiber_hom_ext_of_cartesian b
      (IsPreFibered.pullbackMap ((fiberFunctorOfCompEq hG.comp_eq U).obj y).2 b)
      (IsPreFibered.pullbackMap.IsCartesian _ _) _ _ ?_
    refine (hcrux f hf γ b hb hb'
      (Fiber.fiberInclusion.map
          (pullbackFiberCompIso' ((fiberFunctorOfCompEq hF.comp_eq U).obj x) f γ b hb).inv ≫
        IsPreFibered.pullbackMap
          (pullbackFiber p𝒮 ((fiberFunctorOfCompEq hF.comp_eq U).obj x) f).2 γ) ?_ ?_).trans ?_
    · have h0 : p𝒮.IsHomLift (𝟙 W ≫ γ)
          (Fiber.fiberInclusion.map
              (pullbackFiberCompIso' ((fiberFunctorOfCompEq hF.comp_eq U).obj x) f γ b hb).inv ≫
            IsPreFibered.pullbackMap
              (pullbackFiber p𝒮 ((fiberFunctorOfCompEq hF.comp_eq U).obj x) f).2 γ) :=
        inferInstance
      simpa using h0
    · rw [Category.assoc]
      exact pullbackFiberCompIso'_inv_fac _ f γ b hb
    · simp [Functor.map_comp, Category.assoc, pullbackFiberCompIso'_hom_fac,
        pullbackFiberHom_fac_assoc]
  obtain ⟨e, he⟩ :=
    exists_fiberIso_of_locally p𝒮 (m𝒮 U) hR (fun {_V} f hf => θ f hf) hθcompat
  refine ⟨Fiber.fiberInclusion.mapIso e, e.hom.2, ?_⟩
  intro V f hf
  have h1 := pullbackFiberHom_fac e.hom f
  rw [he f hf] at h1
  have h2 := Fiber.fiberInclusion.map (eF f hf).hom ≫= h1
  rw [hθfac f hf, ← Category.assoc, heF f hf] at h2
  simpa using h2.symm

section Effective

attribute [local implicit_reducible] sieveDescentDatumFst sieveDescentDatumSnd
  structureFunctor

/-- Condition (3) of Stacks 026F for the 2-fibre product: if `p𝒳` and `p𝒴` have effective descent
and the morphism presheaves of `p𝒮` are sheaves, every descent datum in `𝒳 ×_𝒮 𝒴` relative to a
covering sieve is effective. -/
theorem hasEffectiveDescent_structureFunctor (J : GrothendieckTopology 𝒞)
    (h𝒳 : HasEffectiveDescent p𝒳 J) (h𝒴 : HasEffectiveDescent p𝒴 J)
    (m𝒮 : ∀ (T : 𝒞) (a b : p𝒮.Fiber T), IsMorSheaf p𝒮 J T a b) :
    HasEffectiveDescent (structureFunctor p𝒳 p𝒴 p𝒮 F G) J := by
  intro U R hR D
  obtain ⟨x, ζx, hζx, hgx⟩ := h𝒳 R hR (sieveDescentDatumFst hF hG D)
  obtain ⟨y, ζy, hζy, hgy⟩ := h𝒴 R hR (sieveDescentDatumSnd hF hG D)
  obtain ⟨φ, hφlift, hφ⟩ := exists_vertical_iso_of_component_descent hF hG J m𝒮 hR D x y ζx ζy
    hζx hζy hgx hgy
  have hbase : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R f),
      eqToHom (D.obj f hf).1.hy.symm ≫ p𝒴.map (ζy f hf) ≫ eqToHom y.2 =
        eqToHom (D.obj f hf).1.hx.symm ≫ p𝒳.map (ζx f hf) ≫ eqToHom x.2 := by
    intro V f hf
    have := (hζx f hf).toIsHomLift
    have := (hζy f hf).toIsHomLift
    rw [IsHomLift.fac' p𝒳 f (ζx f hf), IsHomLift.fac' p𝒴 f (ζy f hf)]
    simp
  obtain ⟨ζ, hζa, hζb, hζlift⟩ : ∃ ζ : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R f),
      (D.obj f hf).1 ⟶ (⟨U, x.1, y.1, x.2, y.2, φ, hφlift⟩ : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G),
      (∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R f), (ζ f hf).a = ζx f hf) ∧
      (∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R f), (ζ f hf).b = ζy f hf) ∧
      (∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R f),
        (structureFunctor p𝒳 p𝒴 p𝒮 F G).IsHomLift f (ζ f hf)) := by
    refine ⟨fun {_V} f hf => Hom.mk' (ζx f hf) (ζy f hf) (hbase f hf) (hφ f hf),
      fun {_V} _f _hf => rfl, fun {_V} _f _hf => rfl, fun {_V} f hf => ?_⟩
    refine IsHomLift.of_fac' (structureFunctor p𝒳 p𝒴 p𝒮 F G) f _ (D.obj f hf).2 rfl ?_
    have := (hζx f hf).toIsHomLift
    rw [structureFunctor_map, Hom.mk'_hbase, IsHomLift.fac' p𝒳 f (ζx f hf)]
    simp
  refine ⟨⟨⟨U, x.1, y.1, x.2, y.2, φ, hφlift⟩, rfl⟩, ζ, ?_, ?_⟩
  · intro V f hf
    have hcx : p𝒳.IsStronglyCartesian f (ζ f hf).a := by
      have := hζx f hf
      rw [hζa f hf]
      exact IsFibered.isStronglyCartesian_of_isCartesian p𝒳 f (ζx f hf)
    have hcy : p𝒴.IsStronglyCartesian f (ζ f hf).b := by
      have := hζy f hf
      rw [hζb f hf]
      exact IsFibered.isStronglyCartesian_of_isCartesian p𝒴 f (ζy f hf)
    have := isStronglyCartesian_of_components hF hG f (ζ f hf) (hζlift f hf) hcx hcy
    infer_instance
  · intro V W Z f hf g hg ε ε' heq
    refine Hom.ext' ?_ ?_
    · simp only [comp_a, hζa]
      exact descentIsoFst_fac_a hF hG D hf hg ε ε' heq (ζx f hf) (ζx g hg) (hgx hf hg ε ε' heq)
    · simp only [comp_b, hζb]
      exact descentIsoSnd_fac_b hF hG D hf hg ε ε' heq (ζy f hf) (ζy g hg) (hgy hf hg ε ε' heq)
end Effective

end Pullback

end Components

/-- The 2-fibre product of stacks over a site `(𝒞, J)` is a stack, with the hom universe of the
site independent of the hom universe of the three categories of the cospan: if `p𝒳`, `p𝒴`, `p𝒮`
are stacks over `(𝒞, J)` and `F`, `G` are 1-morphisms of fibred categories over `𝒞`, then the
structure functor of the explicit 2-fibre product `𝒳 ×_𝒮 𝒴` is again a stack. -/
@[stacks 026G]
theorem isStack_structureFunctor
    (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (p𝒮 : 𝒮 ⥤ 𝒞) (F : 𝒳 ⥤ 𝒮) (G : 𝒴 ⥤ 𝒮)
    (J : GrothendieckTopology 𝒞) (h𝒳 : Functor.IsStack p𝒳 J) (h𝒴 : Functor.IsStack p𝒴 J)
    (h𝒮 : Functor.IsStack p𝒮 J) (hF : Functor.IsFibredOneMorphism p𝒳 p𝒮 F)
    (hG : Functor.IsFibredOneMorphism p𝒴 p𝒮 G) :
    Functor.IsStack (TwoFibreProductOver.structureFunctor p𝒳 p𝒴 p𝒮 F G) J := by
  have := h𝒳.isFibered
  have := h𝒴.isFibered
  have := h𝒮.isFibered
  have hfib := TwoFibreProductOver.isFibered_structureFunctor p𝒳 p𝒴 p𝒮 F G hF hG
  exact
    { isFibered := hfib
      isMorSheaf := isMorSheaf_structureFunctor hF hG J h𝒳.isMorSheaf h𝒴.isMorSheaf
        h𝒮.isMorSheaf
      hasEffectiveDescent := hasEffectiveDescent_structureFunctor hF hG J
        h𝒳.hasEffectiveDescent h𝒴.hasEffectiveDescent h𝒮.isMorSheaf }

end TwoFibreProductOver

end CategoryTheory
