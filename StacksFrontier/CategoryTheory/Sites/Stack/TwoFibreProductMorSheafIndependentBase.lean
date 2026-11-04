module

public import StacksFrontier.CategoryTheory.FiberedCategory.TwoFibreProduct
public import StacksFrontier.CategoryTheory.Sites.Stack.TwoFibreProductMorPresheafMap
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverIso

/-!
# The morphism sheaves of the 2-fibre product, over a base with its own hom universe

Fix a site `(𝒞, J)` and fibred categories `p𝒳 : 𝒳 ⥤ 𝒞`, `p𝒴 : 𝒴 ⥤ 𝒞`, `p𝒮 : 𝒮 ⥤ 𝒞` with
1-morphisms `F : 𝒳 ⥤ 𝒮`, `G : 𝒴 ⥤ 𝒮` of fibred categories over `𝒞`. This file proves condition
(2) of Stacks 026F for the 2-fibre product `𝒳 ×_𝒮 𝒴` — the presheaves
`Mor((U, x, y, φ), (U, x', y', φ'))` of Stacks 02ZB are sheaves — with the hom universe of the
base `𝒞` independent of the common hom universe of `𝒳`, `𝒴` and `𝒮`.

The comparison isomorphisms `φ` and `φ'` identify the sections of the morphism presheaf of the
2-fibre product with those of the fibre product `Mor(x, x') ×_{Mor(z, z')} Mor(y, y')`, which is a
sheaf (`CategoryTheory.Presheaf.isSheaf_eqPullback`). When the two hom universes agree, this
identification is an isomorphism of presheaves.

## Main definitions

* `CategoryTheory.TwoFibreProductOver.morSectionEquiv`: the identification of the sections of the
  morphism presheaf with those of the fibre product.
* `CategoryTheory.TwoFibreProductOver.morPresheafEqPullbackIso`: the same identification as an
  isomorphism of presheaves, when the hom universe of `𝒞` is that of `𝒳`, `𝒴` and `𝒮`.

## Main results

* `CategoryTheory.TwoFibreProductOver.morSectionEquiv_naturality`: the identification is natural.
* `CategoryTheory.TwoFibreProductOver.isMorSheaf_structureFunctor`: condition (2) of Stacks 026F
  for the 2-fibre product.

## References

* [Stacks Project, Tag 026F](https://stacks.math.columbia.edu/tag/026F)
* [Stacks Project, Tag 02ZB](https://stacks.math.columbia.edu/tag/02ZB)
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

variable {p𝒳 : 𝒳 ⥤ 𝒞} {p𝒴 : 𝒴 ⥤ 𝒞} {p𝒮 : 𝒮 ⥤ 𝒞} {F : 𝒳 ⥤ 𝒮} {G : 𝒴 ⥤ 𝒮}

/-! ### The fibres of the 2-fibre product -/

/-- The `𝒳`-component of an object of the fibre of the 2-fibre product over `U`, as an object of
the fibre of `p𝒳` over `U`. -/
@[implicit_reducible]
def fibFst {U : 𝒞} (P : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber U) : p𝒳.Fiber U :=
  ⟨P.1.x, P.1.hx.trans P.2⟩

/-- The `𝒴`-component of an object of the fibre of the 2-fibre product over `U`, as an object of
the fibre of `p𝒴` over `U`. -/
@[implicit_reducible]
def fibSnd {U : 𝒞} (P : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber U) : p𝒴.Fiber U :=
  ⟨P.1.y, P.1.hy.trans P.2⟩

/-- The comparison isomorphism of an object of the fibre of the 2-fibre product over `U` lies over
`𝟙 U`. -/
lemma isHomLift_fiber_iso_hom {U : 𝒞} (P : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber U) :
    p𝒮.IsHomLift (𝟙 U) P.1.iso.hom := by
  obtain ⟨P, rfl⟩ := P
  exact P.vertical

/-- The comparison isomorphism of an object of the fibre of the 2-fibre product over `U`, read as
an isomorphism `F x ≅ G y` of the fibre of `p𝒮` over `U`. -/
def fibIso (hF : Functor.IsFibredOneMorphism p𝒳 p𝒮 F) (hG : Functor.IsFibredOneMorphism p𝒴 p𝒮 G)
    {U : 𝒞} (P : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber U) :
    (fiberFunctorOfCompEq hF.comp_eq U).obj (fibFst P) ≅
      (fiberFunctorOfCompEq hG.comp_eq U).obj (fibSnd P) :=
  Fiber.isoMk P.1.iso (isHomLift_fiber_iso_hom P)

/-- The underlying morphism of `𝒮` of the forward direction of `fibIso` is the comparison
isomorphism carried by `P`. -/
@[simp]
lemma fiberInclusion_map_fibIso_hom (hF : Functor.IsFibredOneMorphism p𝒳 p𝒮 F)
    (hG : Functor.IsFibredOneMorphism p𝒴 p𝒮 G) {U : 𝒞}
    (P : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber U) :
    Fiber.fiberInclusion.map (fibIso hF hG P).hom = P.1.iso.hom := rfl

/-- The underlying morphism of `𝒮` of the inverse direction of `fibIso` is the inverse of the
comparison isomorphism carried by `P`. -/
@[simp]
lemma fiberInclusion_map_fibIso_inv (hF : Functor.IsFibredOneMorphism p𝒳 p𝒮 F)
    (hG : Functor.IsFibredOneMorphism p𝒴 p𝒮 G) {U : 𝒞}
    (P : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber U) :
    Fiber.fiberInclusion.map (fibIso hF hG P).inv = P.1.iso.inv := rfl

section fiberHomMk

attribute [local implicit_reducible] structureFunctor

/-- A pair of morphisms of the fibres of `p𝒳` and `p𝒴` over `V` making the comparison square
commute, read as a morphism of the fibre of the 2-fibre product over `V`. Its base morphism is
forced to be the comparison `eqToHom`. -/
def fiberHomMk {V : 𝒞} {P Q : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber V}
    (α : fibFst P ⟶ fibFst Q) (β : fibSnd P ⟶ fibSnd Q)
    (w : F.map (Fiber.fiberInclusion.map α) ≫ Q.1.iso.hom =
      P.1.iso.hom ≫ G.map (Fiber.fiberInclusion.map β)) : P ⟶ Q :=
  ⟨{ hbase := eqToHom P.2 ≫ eqToHom Q.2.symm
     a := Fiber.fiberInclusion.map α
     b := Fiber.fiberInclusion.map β
     ha := by
       have := α.2
       refine IsHomLift.of_fac' p𝒳 _ (Fiber.fiberInclusion.map α) P.1.hx Q.1.hx ?_
       rw [IsHomLift.fac' p𝒳 (𝟙 V) (Fiber.fiberInclusion.map α)]
       simp
     hb := by
       have := β.2
       refine IsHomLift.of_fac' p𝒴 _ (Fiber.fiberInclusion.map β) P.1.hy Q.1.hy ?_
       rw [IsHomLift.fac' p𝒴 (𝟙 V) (Fiber.fiberInclusion.map β)]
       simp
     w := w },
    IsHomLift.of_fac' (structureFunctor p𝒳 p𝒴 p𝒮 F G) (𝟙 V) _ P.2 Q.2 (by simp)⟩

end fiberHomMk

/-- The `𝒳`-component of `fiberHomMk α β w` is `α`. -/
@[simp]
lemma fiberHomMk_a {V : 𝒞} {P Q : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber V}
    (α : fibFst P ⟶ fibFst Q) (β : fibSnd P ⟶ fibSnd Q) (w) :
    (Fiber.fiberInclusion.map (fiberHomMk α β w)).a = Fiber.fiberInclusion.map α := rfl

/-- The `𝒴`-component of `fiberHomMk α β w` is `β`. -/
@[simp]
lemma fiberHomMk_b {V : 𝒞} {P Q : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber V}
    (α : fibFst P ⟶ fibFst Q) (β : fibSnd P ⟶ fibSnd Q) (w) :
    (Fiber.fiberInclusion.map (fiberHomMk α β w)).b = Fiber.fiberInclusion.map β := rfl

/-- The `𝒳`-component of a morphism of the fibre of the 2-fibre product over `V`, as a morphism of
the fibre of `p𝒳` over `V`. -/
def fibFstHom {V : 𝒞} {P Q : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber V} (Φ : P ⟶ Q) :
    fibFst P ⟶ fibFst Q :=
  ⟨(Fiber.fiberInclusion.map Φ).a, isHomLift_a (Fiber.fiberInclusion.map Φ) (𝟙 V) Φ.2⟩

/-- The `𝒴`-component of a morphism of the fibre of the 2-fibre product over `V`, as a morphism of
the fibre of `p𝒴` over `V`. -/
def fibSndHom {V : 𝒞} {P Q : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber V} (Φ : P ⟶ Q) :
    fibSnd P ⟶ fibSnd Q :=
  ⟨(Fiber.fiberInclusion.map Φ).b, isHomLift_b (Fiber.fiberInclusion.map Φ) (𝟙 V) Φ.2⟩

/-- The underlying morphism of `𝒳` of `fibFstHom Φ` is the `𝒳`-component of `Φ`. -/
@[simp]
lemma fiberInclusion_map_fibFstHom {V : 𝒞} {P Q : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber V}
    (Φ : P ⟶ Q) :
    Fiber.fiberInclusion.map (fibFstHom Φ) = (Fiber.fiberInclusion.map Φ).a := rfl

/-- The underlying morphism of `𝒴` of `fibSndHom Φ` is the `𝒴`-component of `Φ`. -/
@[simp]
lemma fiberInclusion_map_fibSndHom {V : 𝒞} {P Q : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber V}
    (Φ : P ⟶ Q) :
    Fiber.fiberInclusion.map (fibSndHom Φ) = (Fiber.fiberInclusion.map Φ).b := rfl

/-- A morphism of the fibre of the 2-fibre product over `V` *is* a pair of morphisms of the fibres
of `p𝒳` and `p𝒴` over `V` making the comparison square commute. -/
def fiberHomEquiv {V : 𝒞} (P Q : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber V) :
    (P ⟶ Q) ≃ {αβ : (fibFst P ⟶ fibFst Q) × (fibSnd P ⟶ fibSnd Q) //
      F.map (Fiber.fiberInclusion.map αβ.1) ≫ Q.1.iso.hom =
        P.1.iso.hom ≫ G.map (Fiber.fiberInclusion.map αβ.2)} where
  toFun Φ := ⟨(fibFstHom Φ, fibSndHom Φ), Φ.1.w⟩
  invFun αβ := fiberHomMk αβ.val.fst αβ.val.snd αβ.property
  left_inv _ := Fiber.hom_ext (Hom.ext' rfl rfl)
  right_inv _ := Subtype.ext (Prod.ext (Fiber.hom_ext rfl) (Fiber.hom_ext rfl))


/-- Two morphisms, each a morphism over `𝟙` followed by one over `g` (in either order), are equal
if they agree after composing with a strongly cartesian morphism over `f`. -/
private theorem ext_comp_of_isStronglyCartesian
    (p : 𝒳 ⥤ 𝒞) {R R' S : 𝒞} (f : R ⟶ S) (g : R' ⟶ R) {a a₁ a₂ b c : 𝒳} (φ : b ⟶ c)
    [p.IsStronglyCartesian f φ] {i₁ : a ⟶ a₁} {u : a₁ ⟶ b} {v : a ⟶ a₂} {i₂ : a₂ ⟶ b}
    [p.IsHomLift (𝟙 R') i₁] [p.IsHomLift g u] [p.IsHomLift g v] [p.IsHomLift (𝟙 R) i₂]
    (h : (i₁ ≫ u) ≫ φ = (v ≫ i₂) ≫ φ) : i₁ ≫ u = v ≫ i₂ := by
  have h₁ : p.IsHomLift g (i₁ ≫ u) := by simpa using (inferInstance : p.IsHomLift (𝟙 R' ≫ g) _)
  have h₂ : p.IsHomLift g (v ≫ i₂) := by simpa using (inferInstance : p.IsHomLift (g ≫ 𝟙 R) _)
  exact IsStronglyCartesian.ext p f φ g h

section Fibered

variable [p𝒳.IsFibered] [p𝒴.IsFibered] [p𝒮.IsFibered]
  [(structureFunctor p𝒳 p𝒴 p𝒮 F G).IsFibered]
  (hF : Functor.IsFibredOneMorphism p𝒳 p𝒮 F) (hG : Functor.IsFibredOneMorphism p𝒴 p𝒮 G)

include hF hG

omit [p𝒮.IsFibered] in
/-- The `𝒳`-component of the chosen cartesian lift of `f` at `P` in the 2-fibre product is strongly
cartesian. -/
lemma isStronglyCartesian_pullbackMap_a {U V : 𝒞}
    (P : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber U) (f : V ⟶ U) :
    p𝒳.IsStronglyCartesian f (IsPreFibered.pullbackMap P.2 f).a :=
  (map_isStronglyCartesian_of_isStronglyCartesian hF hG f
    (IsPreFibered.pullbackMap P.2 f) inferInstance).1

omit [p𝒮.IsFibered] in
/-- The `𝒴`-component of the chosen cartesian lift of `f` at `P` in the 2-fibre product is strongly
cartesian. -/
lemma isStronglyCartesian_pullbackMap_b {U V : 𝒞}
    (P : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber U) (f : V ⟶ U) :
    p𝒴.IsStronglyCartesian f (IsPreFibered.pullbackMap P.2 f).b :=
  (map_isStronglyCartesian_of_isStronglyCartesian hF hG f
    (IsPreFibered.pullbackMap P.2 f) inferInstance).2

/-- The comparison isomorphism, in the fibre of `p𝒳` over `V`, between the `𝒳`-component of the
chosen pullback of `P` in the 2-fibre product and the chosen pullback of the `𝒳`-component of `P`.
-/
noncomputable def pullbackFiberFstIso {U V : 𝒞}
    (P : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber U) (f : V ⟶ U) :
    fibFst (pullbackFiber (structureFunctor p𝒳 p𝒴 p𝒮 F G) P f) ≅ pullbackFiber p𝒳 (fibFst P) f :=
  have := isStronglyCartesian_pullbackMap_a hF hG P f
  fiberIsoOfCartesian f (IsPreFibered.pullbackMap P.2 f).a
    (IsPreFibered.pullbackMap (fibFst P).2 f) inferInstance inferInstance

/-- The comparison isomorphism, in the fibre of `p𝒴` over `V`, between the `𝒴`-component of the
chosen pullback of `P` in the 2-fibre product and the chosen pullback of the `𝒴`-component of
`P`. -/
noncomputable def pullbackFiberSndIso {U V : 𝒞}
    (P : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber U) (f : V ⟶ U) :
    fibSnd (pullbackFiber (structureFunctor p𝒳 p𝒴 p𝒮 F G) P f) ≅ pullbackFiber p𝒴 (fibSnd P) f :=
  have := isStronglyCartesian_pullbackMap_b hF hG P f
  fiberIsoOfCartesian f (IsPreFibered.pullbackMap P.2 f).b
    (IsPreFibered.pullbackMap (fibSnd P).2 f) inferInstance inferInstance

omit [p𝒮.IsFibered] in
/-- The forward direction of `pullbackFiberFstIso` composed with the chosen cartesian lift of `f`
at `x` is the `𝒳`-component of the chosen cartesian lift of `f` at `P`. -/
@[reassoc (attr := simp)]
lemma pullbackFiberFstIso_hom_fac {U V : 𝒞}
    (P : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber U) (f : V ⟶ U) :
    Fiber.fiberInclusion.map (pullbackFiberFstIso hF hG P f).hom ≫
        IsPreFibered.pullbackMap (fibFst P).2 f = (IsPreFibered.pullbackMap P.2 f).a :=
  fiberIsoOfCartesian_hom_fac _ _ _ _ _

omit [p𝒮.IsFibered] in
/-- The inverse direction of `pullbackFiberFstIso` composed with the `𝒳`-component of the chosen
cartesian lift of `f` at `P` is the chosen cartesian lift of `f` at `x`. -/
@[reassoc (attr := simp)]
lemma pullbackFiberFstIso_inv_fac {U V : 𝒞}
    (P : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber U) (f : V ⟶ U) :
    Fiber.fiberInclusion.map (pullbackFiberFstIso hF hG P f).inv ≫
        (IsPreFibered.pullbackMap P.2 f).a = IsPreFibered.pullbackMap (fibFst P).2 f :=
  fiberIsoOfCartesian_inv_fac _ _ _ _ _

omit [p𝒮.IsFibered] in
/-- The forward direction of `pullbackFiberSndIso` composed with the chosen cartesian lift of `f`
at `y` is the `𝒴`-component of the chosen cartesian lift of `f` at `P`. -/
@[reassoc (attr := simp)]
lemma pullbackFiberSndIso_hom_fac {U V : 𝒞}
    (P : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber U) (f : V ⟶ U) :
    Fiber.fiberInclusion.map (pullbackFiberSndIso hF hG P f).hom ≫
        IsPreFibered.pullbackMap (fibSnd P).2 f = (IsPreFibered.pullbackMap P.2 f).b :=
  fiberIsoOfCartesian_hom_fac _ _ _ _ _

omit [p𝒮.IsFibered] in
/-- The inverse direction of `pullbackFiberSndIso` composed with the `𝒴`-component of the chosen
cartesian lift of `f` at `P` is the chosen cartesian lift of `f` at `y`. -/
@[reassoc (attr := simp)]
lemma pullbackFiberSndIso_inv_fac {U V : 𝒞}
    (P : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber U) (f : V ⟶ U) :
    Fiber.fiberInclusion.map (pullbackFiberSndIso hF hG P f).inv ≫
        (IsPreFibered.pullbackMap P.2 f).b = IsPreFibered.pullbackMap (fibSnd P).2 f :=
  fiberIsoOfCartesian_inv_fac _ _ _ _ _


/-- The comparison isomorphism carried by the chosen pullback of `P` in the 2-fibre product, read
through the componentwise comparisons: an isomorphism `F(f^* x) ≅ G(f^* y)` of the fibre
over `V`. -/
noncomputable def xiFibIso {U V : 𝒞} (P : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber U) (f : V ⟶ U) :
    (fiberFunctorOfCompEq hF.comp_eq V).obj (pullbackFiber p𝒳 (fibFst P) f) ≅
      (fiberFunctorOfCompEq hG.comp_eq V).obj (pullbackFiber p𝒴 (fibSnd P) f) :=
  (fiberFunctorOfCompEq hF.comp_eq V).mapIso (pullbackFiberFstIso hF hG P f).symm ≪≫
    fibIso hF hG (pullbackFiber (structureFunctor p𝒳 p𝒴 p𝒮 F G) P f) ≪≫
    (fiberFunctorOfCompEq hG.comp_eq V).mapIso (pullbackFiberSndIso hF hG P f)

/-- The base change of the comparison isomorphism of `P` along `f`, transported by the comparisons
between the chosen pullbacks of `F x`, `G y` and the images of the chosen pullbacks of `x`, `y`. -/
noncomputable def thetaFibIso {U V : 𝒞} (P : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber U) (f : V ⟶ U) :
    (fiberFunctorOfCompEq hF.comp_eq V).obj (pullbackFiber p𝒳 (fibFst P) f) ≅
      (fiberFunctorOfCompEq hG.comp_eq V).obj (pullbackFiber p𝒴 (fibSnd P) f) :=
  (hF.mapPullbackFiberIso (fibFst P) f).symm ≪≫ pullbackFiberIso (fibIso hF hG P) f ≪≫
    hG.mapPullbackFiberIso (fibSnd P) f

/-- The comparison isomorphism of a chosen pullback is the base change of the comparison
isomorphism. -/
lemma xiFibIso_eq_thetaFibIso {U V : 𝒞} (P : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber U)
    (f : V ⟶ U) : xiFibIso hF hG P f = thetaFibIso hF hG P f := by
  have hL : Fiber.fiberInclusion.map (xiFibIso hF hG P f).hom ≫
      G.map (IsPreFibered.pullbackMap (fibSnd P).2 f) =
    F.map (IsPreFibered.pullbackMap (fibFst P).2 f) ≫ P.1.iso.hom := by
    simp only [xiFibIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp,
      Category.assoc, fiberInclusion_map_fiberFunctorOfCompEq_map, fiberInclusion_map_fibIso_hom]
    have hw : (pullbackFiber (structureFunctor p𝒳 p𝒴 p𝒮 F G) P f).1.iso.hom ≫
        G.map (IsPreFibered.pullbackMap P.2 f).b =
      F.map (IsPreFibered.pullbackMap P.2 f).a ≫ P.1.iso.hom :=
      ((IsPreFibered.pullbackMap P.2 f).w).symm
    rw [← Functor.map_comp G, pullbackFiberSndIso_hom_fac, hw, ← Functor.map_comp_assoc,
      pullbackFiberFstIso_inv_fac]
  have hR : Fiber.fiberInclusion.map (thetaFibIso hF hG P f).hom ≫
      G.map (IsPreFibered.pullbackMap (fibSnd P).2 f) =
    F.map (IsPreFibered.pullbackMap (fibFst P).2 f) ≫ P.1.iso.hom := by
    simp only [thetaFibIso, Iso.trans_hom, Iso.symm_hom, pullbackFiberIso_hom, Functor.map_comp,
      Category.assoc]
    rw [Functor.IsFibredOneMorphism.mapPullbackFiberIso_hom_fac, pullbackFiberHom_fac,
      fiberInclusion_map_fibIso_hom,
      Functor.IsFibredOneMorphism.mapPullbackFiberIso_inv_fac_assoc]
  exact Iso.ext (fiber_hom_ext_of_cartesian f
    (G.map (IsPreFibered.pullbackMap (fibSnd P).2 f))
    (hG.isCartesian_map_pullbackMap (fibSnd P) f) _ _ (hL.trans hR.symm))

/-- The base change of `φ`, followed by the comparison for `G` and the inverse comparison for the
`𝒴`-component, is the comparison for `F`, followed by the inverse comparison for the
`𝒳`-component and the comparison isomorphism of the chosen pullback. -/
@[reassoc]
lemma pullbackFiberHom_fibIso_fac {U V : 𝒞}
    (P : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber U) (f : V ⟶ U) :
    Fiber.fiberInclusion.map (pullbackFiberHom (fibIso hF hG P).hom f) ≫
        Fiber.fiberInclusion.map (hG.mapPullbackFiberIso (fibSnd P) f).hom ≫
        G.map (Fiber.fiberInclusion.map (pullbackFiberSndIso hF hG P f).inv) =
      Fiber.fiberInclusion.map (hF.mapPullbackFiberIso (fibFst P) f).hom ≫
        F.map (Fiber.fiberInclusion.map (pullbackFiberFstIso hF hG P f).inv) ≫
        (pullbackFiber (structureFunctor p𝒳 p𝒴 p𝒮 F G) P f).1.iso.hom := by
  have h : pullbackFiberHom (fibIso hF hG P).hom f ≫
        (hG.mapPullbackFiberIso (fibSnd P) f).hom ≫
        (fiberFunctorOfCompEq hG.comp_eq V).map (pullbackFiberSndIso hF hG P f).inv =
      (hF.mapPullbackFiberIso (fibFst P) f).hom ≫
        (fiberFunctorOfCompEq hF.comp_eq V).map (pullbackFiberFstIso hF hG P f).inv ≫
        (fibIso hF hG (pullbackFiber (structureFunctor p𝒳 p𝒴 p𝒮 F G) P f)).hom := by
    have h3 := congrArg Iso.hom (xiFibIso_eq_thetaFibIso hF hG P f)
    simp only [xiFibIso, thetaFibIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      pullbackFiberIso_hom] at h3
    rw [Iso.eq_inv_comp] at h3
    rw [← Category.assoc, ← h3]
    simp [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id, Functor.map_id,
      Category.comp_id]
  have h4 := congrArg Fiber.fiberInclusion.map h
  simpa only [Functor.map_comp, fiberInclusion_map_fiberFunctorOfCompEq_map,
    fiberInclusion_map_fibIso_hom] using h4


/-- The second leg of the cospan: `Mor(y, y') ⟶ Mor(F x, F x')`, the map induced by `G` followed by
the identification of `Mor(G y, G y')` with `Mor(F x, F x')` given by the comparison isomorphisms
`φ` of `P` and `φ'` of `P'`. -/
noncomputable def morSnd {U : 𝒞} (P P' : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber U) :
    morPresheaf p𝒴 (fibSnd P) (fibSnd P') ⟶
      morPresheaf p𝒮 ((fiberFunctorOfCompEq hF.comp_eq U).obj (fibFst P))
        ((fiberFunctorOfCompEq hF.comp_eq U).obj (fibFst P')) :=
  hG.morPresheafMap (fibSnd P) (fibSnd P') ≫
    (morPresheafFiberIso p𝒮 (fibIso hF hG P).symm (fibIso hF hG P').symm).hom

omit [p𝒳.IsFibered] [(structureFunctor p𝒳 p𝒴 p𝒮 F G).IsFibered] in
/-- A section of `Mor(y, y')` over `g` is carried by `morSnd` to its image under `G`, conjugated
by the comparisons
`CategoryTheory.Functor.IsFibredOneMorphism.mapPullbackFiberIso` and then by the base changes of
the comparison isomorphisms of `P` and `P'`. -/
@[simp]
lemma morSnd_app {U : 𝒞} (P P' : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber U) (g : (Over U)ᵒᵖ)
    (n : (morPresheaf p𝒴 (fibSnd P) (fibSnd P')).obj g) :
    (morSnd hF hG P P').app g n =
      pullbackFiberHom (fibIso hF hG P).hom g.unop.hom ≫
        ((hG.mapPullbackFiberIso (fibSnd P) g.unop.hom).hom ≫
          (fiberFunctorOfCompEq hG.comp_eq g.unop.left).map n ≫
          (hG.mapPullbackFiberIso (fibSnd P') g.unop.hom).inv) ≫
        pullbackFiberHom (fibIso hF hG P').inv g.unop.hom := rfl

/-- For a pair of morphisms of the fibres of `p𝒳` and `p𝒴` over `V` between the components of the
chosen pullbacks of `P` and `P'` in the 2-fibre product, the commuting square of the 2-fibre
product holds exactly when the transported pair is a section of the fibre product of the two legs
of the cospan. -/
lemma morCondition_iff {U : 𝒞} (P P' : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber U) (g : Over U)
    (α : fibFst (pullbackFiber (structureFunctor p𝒳 p𝒴 p𝒮 F G) P g.hom) ⟶
      fibFst (pullbackFiber (structureFunctor p𝒳 p𝒴 p𝒮 F G) P' g.hom))
    (β : fibSnd (pullbackFiber (structureFunctor p𝒳 p𝒴 p𝒮 F G) P g.hom) ⟶
      fibSnd (pullbackFiber (structureFunctor p𝒳 p𝒴 p𝒮 F G) P' g.hom)) :
    (F.map (Fiber.fiberInclusion.map α) ≫
          (pullbackFiber (structureFunctor p𝒳 p𝒴 p𝒮 F G) P' g.hom).1.iso.hom =
        (pullbackFiber (structureFunctor p𝒳 p𝒴 p𝒮 F G) P g.hom).1.iso.hom ≫
          G.map (Fiber.fiberInclusion.map β)) ↔
      (hF.morPresheafMap (fibFst P) (fibFst P')).app (op g)
          ((pullbackFiberFstIso hF hG P g.hom).homCongr
            (pullbackFiberFstIso hF hG P' g.hom) α) =
        (morSnd hF hG P P').app (op g)
          ((pullbackFiberSndIso hF hG P g.hom).homCongr
            (pullbackFiberSndIso hF hG P' g.hom) β) := by
  have hw' : G.map (IsPreFibered.pullbackMap P'.2 g.hom).b ≫ P'.1.iso.inv =
      (pullbackFiber (structureFunctor p𝒳 p𝒴 p𝒮 F G) P' g.hom).1.iso.inv ≫
        F.map (IsPreFibered.pullbackMap P'.2 g.hom).a := by
    have h : (pullbackFiber (structureFunctor p𝒳 p𝒴 p𝒮 F G) P' g.hom).1.iso.hom ≫
        G.map (IsPreFibered.pullbackMap P'.2 g.hom).b =
      F.map (IsPreFibered.pullbackMap P'.2 g.hom).a ≫ P'.1.iso.hom :=
      ((IsPreFibered.pullbackMap P'.2 g.hom).w).symm
    rw [Iso.comp_inv_eq, Category.assoc, ← h, Iso.inv_hom_id_assoc]
  have hS : Fiber.fiberInclusion.map ((hF.morPresheafMap (fibFst P) (fibFst P')).app (op g)
        ((pullbackFiberFstIso hF hG P g.hom).homCongr
          (pullbackFiberFstIso hF hG P' g.hom) α)) ≫
      IsPreFibered.pullbackMap ((fiberFunctorOfCompEq hF.comp_eq U).obj (fibFst P')).2 g.hom =
    (Fiber.fiberInclusion.map (hF.mapPullbackFiberIso (fibFst P) g.hom).hom ≫
        F.map (Fiber.fiberInclusion.map (pullbackFiberFstIso hF hG P g.hom).inv)) ≫
      (F.map (Fiber.fiberInclusion.map α) ≫
        F.map (IsPreFibered.pullbackMap P'.2 g.hom).a) := by
    simp only [Functor.IsFibredOneMorphism.morPresheafMap_app, Iso.homCongr_apply,
      Functor.map_comp, Category.assoc, fiberInclusion_map_fiberFunctorOfCompEq_map,
      Functor.IsFibredOneMorphism.mapPullbackFiberIso_inv_fac]
    rw [← Functor.map_comp F, pullbackFiberFstIso_hom_fac]
  have hT : Fiber.fiberInclusion.map ((morSnd hF hG P P').app (op g)
        ((pullbackFiberSndIso hF hG P g.hom).homCongr
          (pullbackFiberSndIso hF hG P' g.hom) β)) ≫
      IsPreFibered.pullbackMap ((fiberFunctorOfCompEq hF.comp_eq U).obj (fibFst P')).2 g.hom =
    (Fiber.fiberInclusion.map (hF.mapPullbackFiberIso (fibFst P) g.hom).hom ≫
        F.map (Fiber.fiberInclusion.map (pullbackFiberFstIso hF hG P g.hom).inv)) ≫
      (((pullbackFiber (structureFunctor p𝒳 p𝒴 p𝒮 F G) P g.hom).1.iso.hom ≫
            G.map (Fiber.fiberInclusion.map β)) ≫
          (pullbackFiber (structureFunctor p𝒳 p𝒴 p𝒮 F G) P' g.hom).1.iso.inv) ≫
        F.map (IsPreFibered.pullbackMap P'.2 g.hom).a := by
    simp only [morSnd_app, Iso.homCongr_apply, Functor.map_comp, Category.assoc,
      fiberInclusion_map_fiberFunctorOfCompEq_map]
    have hGfac : G.map (Fiber.fiberInclusion.map (pullbackFiberSndIso hF hG P' g.hom).hom) ≫
        G.map (IsPreFibered.pullbackMap (fibSnd P').2 g.hom) ≫ P'.1.iso.inv =
      (pullbackFiber (structureFunctor p𝒳 p𝒴 p𝒮 F G) P' g.hom).1.iso.inv ≫
        F.map (IsPreFibered.pullbackMap P'.2 g.hom).a := by
      rw [← Functor.map_comp_assoc, pullbackFiberSndIso_hom_fac, hw']
    rw [pullbackFiberHom_fac, fiberInclusion_map_fibIso_inv,
      Functor.IsFibredOneMorphism.mapPullbackFiberIso_inv_fac_assoc, hGfac,
      pullbackFiberHom_fibIso_fac_assoc]
  constructor
  · intro hw
    refine fiber_hom_ext_of_cartesian g.hom
      (IsPreFibered.pullbackMap ((fiberFunctorOfCompEq hF.comp_eq U).obj (fibFst P')).2 g.hom)
      inferInstance _ _ ?_
    rw [hS, hT, ← hw]
    simp
  · intro hST
    have h1 : Fiber.fiberInclusion.map ((hF.morPresheafMap (fibFst P) (fibFst P')).app (op g)
          ((pullbackFiberFstIso hF hG P g.hom).homCongr
            (pullbackFiberFstIso hF hG P' g.hom) α)) ≫
        IsPreFibered.pullbackMap ((fiberFunctorOfCompEq hF.comp_eq U).obj (fibFst P')).2 g.hom =
      Fiber.fiberInclusion.map ((morSnd hF hG P P').app (op g)
          ((pullbackFiberSndIso hF hG P g.hom).homCongr
            (pullbackFiberSndIso hF hG P' g.hom) β)) ≫
        IsPreFibered.pullbackMap
          ((fiberFunctorOfCompEq hF.comp_eq U).obj (fibFst P')).2 g.hom := by
      rw [hST]
    rw [hS, hT] at h1
    have h2 := (cancel_epi (Fiber.fiberInclusion.map
      (hF.mapPullbackFiberIso (fibFst P) g.hom).hom ≫
        F.map (Fiber.fiberInclusion.map (pullbackFiberFstIso hF hG P g.hom).inv))).1 h1
    have hFα : p𝒮.IsHomLift (𝟙 g.left) (F.map (Fiber.fiberInclusion.map α)) :=
      hF.map_isHomLift (𝟙 g.left) (Fiber.fiberInclusion.map α)
    have hQ := isHomLift_fiber_iso_hom (pullbackFiber (structureFunctor p𝒳 p𝒴 p𝒮 F G) P g.hom)
    have hQ' := isHomLift_fiber_iso_hom (pullbackFiber (structureFunctor p𝒳 p𝒴 p𝒮 F G) P' g.hom)
    have hQ'inv : p𝒮.IsHomLift (𝟙 g.left)
        (pullbackFiber (structureFunctor p𝒳 p𝒴 p𝒮 F G) P' g.hom).1.iso.inv := inferInstance
    have hGβ : p𝒮.IsHomLift (𝟙 g.left) (G.map (Fiber.fiberInclusion.map β)) :=
      hG.map_isHomLift (𝟙 g.left) (Fiber.fiberInclusion.map β)
    have hX : p𝒮.IsHomLift (𝟙 g.left)
        (((pullbackFiber (structureFunctor p𝒳 p𝒴 p𝒮 F G) P g.hom).1.iso.hom ≫
            G.map (Fiber.fiberInclusion.map β)) ≫
          (pullbackFiber (structureFunctor p𝒳 p𝒴 p𝒮 F G) P' g.hom).1.iso.inv) :=
      Functor.isHomLift_id_comp p𝒮 _ _ (Functor.isHomLift_id_comp p𝒮 _ _ hQ hGβ) hQ'inv
    have hM : p𝒮.IsStronglyCartesian g.hom
        (F.map (IsPreFibered.pullbackMap P'.2 g.hom).a) :=
      hF.map_isStronglyCartesian g.hom _ (isStronglyCartesian_pullbackMap_a hF hG P' g.hom)
    have h3 := IsStronglyCartesian.ext p𝒮 g.hom
      (F.map (IsPreFibered.pullbackMap P'.2 g.hom).a) (𝟙 g.left) h2
    rw [h3]
    simp


omit [p𝒳.IsFibered] [p𝒴.IsFibered] [p𝒮.IsFibered] hF hG in
/-- Restriction of the chosen pullbacks in the 2-fibre product, read on the `𝒳`-component. -/
lemma pullbackFiberMap_fac_a {U : 𝒞} (P : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber U)
    {g₁ g₂ : Over U} (h : g₁ ⟶ g₂) :
    (pullbackFiberMap (structureFunctor p𝒳 p𝒴 p𝒮 F G) P h).a ≫
        (IsPreFibered.pullbackMap P.2 g₂.hom).a = (IsPreFibered.pullbackMap P.2 g₁.hom).a := by
  simpa only [comp_a] using
    congrArg (fun Φ => Φ.a) (pullbackFiberMap_fac (structureFunctor p𝒳 p𝒴 p𝒮 F G) P h)

omit [p𝒳.IsFibered] [p𝒴.IsFibered] [p𝒮.IsFibered] hF hG in
/-- Restriction of the chosen pullbacks in the 2-fibre product, read on the `𝒴`-component. -/
lemma pullbackFiberMap_fac_b {U : 𝒞} (P : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber U)
    {g₁ g₂ : Over U} (h : g₁ ⟶ g₂) :
    (pullbackFiberMap (structureFunctor p𝒳 p𝒴 p𝒮 F G) P h).b ≫
        (IsPreFibered.pullbackMap P.2 g₂.hom).b = (IsPreFibered.pullbackMap P.2 g₁.hom).b := by
  simpa only [comp_b] using
    congrArg (fun Φ => Φ.b) (pullbackFiberMap_fac (structureFunctor p𝒳 p𝒴 p𝒮 F G) P h)

omit [p𝒳.IsFibered] [p𝒴.IsFibered] [p𝒮.IsFibered] hF hG in
/-- The defining property of a restricted section of the morphism presheaf of the 2-fibre product,
read on the `𝒳`-component. -/
lemma morRestrict_fac_a {U : 𝒞} (P P' : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber U)
    {g₁ g₂ : Over U} (h : g₁ ⟶ g₂)
    (m : (morPresheaf (structureFunctor p𝒳 p𝒴 p𝒮 F G) P P').obj (op g₂)) :
    (Fiber.fiberInclusion.map (morRestrict (structureFunctor p𝒳 p𝒴 p𝒮 F G) P P' h m)).a ≫
        (IsPreFibered.pullbackMap P'.2 g₁.hom).a =
      (pullbackFiberMap (structureFunctor p𝒳 p𝒴 p𝒮 F G) P h).a ≫
        (Fiber.fiberInclusion.map m).a ≫ (IsPreFibered.pullbackMap P'.2 g₂.hom).a := by
  have h1 : (Fiber.fiberInclusion.map
        (morRestrict (structureFunctor p𝒳 p𝒴 p𝒮 F G) P P' h m) ≫
      IsPreFibered.pullbackMap P'.2 g₁.hom).a =
    (pullbackFiberMap (structureFunctor p𝒳 p𝒴 p𝒮 F G) P h ≫
      Fiber.fiberInclusion.map m ≫ IsPreFibered.pullbackMap P'.2 g₂.hom).a :=
    congrArg (fun Φ => Φ.a) (morRestrict_fac (structureFunctor p𝒳 p𝒴 p𝒮 F G) P P' h m)
  rwa [comp_a, comp_a, comp_a] at h1

omit [p𝒳.IsFibered] [p𝒴.IsFibered] [p𝒮.IsFibered] hF hG in
/-- The defining property of a restricted section of the morphism presheaf of the 2-fibre product,
read on the `𝒴`-component. -/
lemma morRestrict_fac_b {U : 𝒞} (P P' : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber U)
    {g₁ g₂ : Over U} (h : g₁ ⟶ g₂)
    (m : (morPresheaf (structureFunctor p𝒳 p𝒴 p𝒮 F G) P P').obj (op g₂)) :
    (Fiber.fiberInclusion.map (morRestrict (structureFunctor p𝒳 p𝒴 p𝒮 F G) P P' h m)).b ≫
        (IsPreFibered.pullbackMap P'.2 g₁.hom).b =
      (pullbackFiberMap (structureFunctor p𝒳 p𝒴 p𝒮 F G) P h).b ≫
        (Fiber.fiberInclusion.map m).b ≫ (IsPreFibered.pullbackMap P'.2 g₂.hom).b := by
  have h1 : (Fiber.fiberInclusion.map
        (morRestrict (structureFunctor p𝒳 p𝒴 p𝒮 F G) P P' h m) ≫
      IsPreFibered.pullbackMap P'.2 g₁.hom).b =
    (pullbackFiberMap (structureFunctor p𝒳 p𝒴 p𝒮 F G) P h ≫
      Fiber.fiberInclusion.map m ≫ IsPreFibered.pullbackMap P'.2 g₂.hom).b :=
    congrArg (fun Φ => Φ.b) (morRestrict_fac (structureFunctor p𝒳 p𝒴 p𝒮 F G) P P' h m)
  rwa [comp_b, comp_b, comp_b] at h1

omit [p𝒮.IsFibered] in
/-- The comparison between the `𝒳`-component of the chosen pullback in the 2-fibre product and the
chosen pullback in `𝒳` is natural in the object of `𝒞/U`. -/
@[reassoc]
lemma pullbackFiberFstIso_inv_naturality {U : 𝒞}
    (P : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber U) {g₁ g₂ : Over U} (h : g₁ ⟶ g₂) :
    Fiber.fiberInclusion.map (pullbackFiberFstIso hF hG P g₁.hom).inv ≫
        (pullbackFiberMap (structureFunctor p𝒳 p𝒴 p𝒮 F G) P h).a =
      pullbackFiberMap p𝒳 (fibFst P) h ≫
        Fiber.fiberInclusion.map (pullbackFiberFstIso hF hG P g₂.hom).inv := by
  have hcart := isStronglyCartesian_pullbackMap_a hF hG P g₂.hom
  have hi₁ := (pullbackFiberFstIso hF hG P g₁.hom).inv.2
  have hi₂ := (pullbackFiberFstIso hF hG P g₂.hom).inv.2
  have hpm : p𝒳.IsHomLift h.left (pullbackFiberMap (structureFunctor p𝒳 p𝒴 p𝒮 F G) P h).a :=
    isHomLift_a _ h.left (pullbackFiberMap_isHomLift (structureFunctor p𝒳 p𝒴 p𝒮 F G) P h)
  refine ext_comp_of_isStronglyCartesian p𝒳 g₂.hom h.left (IsPreFibered.pullbackMap P.2 g₂.hom).a ?_
  rw [Category.assoc, pullbackFiberMap_fac_a, pullbackFiberFstIso_inv_fac, Category.assoc,
    pullbackFiberFstIso_inv_fac, pullbackFiberMap_fac]

omit [p𝒮.IsFibered] in
/-- The comparison between the `𝒴`-component of the chosen pullback in the 2-fibre product and the
chosen pullback in `𝒴` is natural in the object of `𝒞/U`. -/
@[reassoc]
lemma pullbackFiberSndIso_inv_naturality {U : 𝒞}
    (P : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber U) {g₁ g₂ : Over U} (h : g₁ ⟶ g₂) :
    Fiber.fiberInclusion.map (pullbackFiberSndIso hF hG P g₁.hom).inv ≫
        (pullbackFiberMap (structureFunctor p𝒳 p𝒴 p𝒮 F G) P h).b =
      pullbackFiberMap p𝒴 (fibSnd P) h ≫
        Fiber.fiberInclusion.map (pullbackFiberSndIso hF hG P g₂.hom).inv := by
  have hcart := isStronglyCartesian_pullbackMap_b hF hG P g₂.hom
  have hi₁ := (pullbackFiberSndIso hF hG P g₁.hom).inv.2
  have hi₂ := (pullbackFiberSndIso hF hG P g₂.hom).inv.2
  have hpm : p𝒴.IsHomLift h.left (pullbackFiberMap (structureFunctor p𝒳 p𝒴 p𝒮 F G) P h).b :=
    isHomLift_b _ h.left (pullbackFiberMap_isHomLift (structureFunctor p𝒳 p𝒴 p𝒮 F G) P h)
  refine ext_comp_of_isStronglyCartesian p𝒴 g₂.hom h.left (IsPreFibered.pullbackMap P.2 g₂.hom).b ?_
  rw [Category.assoc, pullbackFiberMap_fac_b, pullbackFiberSndIso_inv_fac, Category.assoc,
    pullbackFiberSndIso_inv_fac, pullbackFiberMap_fac]


omit [p𝒮.IsFibered] in
/-- Naturality of the section bijection on the `𝒳`-component. -/
lemma morSectionEquiv_naturality_fst {U : 𝒞}
    (P P' : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber U) {g₁ g₂ : Over U} (h : g₁ ⟶ g₂)
    (m : (morPresheaf (structureFunctor p𝒳 p𝒴 p𝒮 F G) P P').obj (op g₂)) :
    (pullbackFiberFstIso hF hG P g₁.hom).homCongr (pullbackFiberFstIso hF hG P' g₁.hom)
        (fibFstHom (morRestrict (structureFunctor p𝒳 p𝒴 p𝒮 F G) P P' h m)) =
      morRestrict p𝒳 (fibFst P) (fibFst P') h
        ((pullbackFiberFstIso hF hG P g₂.hom).homCongr
          (pullbackFiberFstIso hF hG P' g₂.hom) (fibFstHom m)) := by
  refine morRestrict_uniq p𝒳 (fibFst P) (fibFst P') h _ _ ?_
  simp only [Iso.homCongr_apply, Functor.map_comp, Category.assoc,
    fiberInclusion_map_fibFstHom, pullbackFiberFstIso_hom_fac]
  rw [morRestrict_fac_a, pullbackFiberFstIso_inv_naturality_assoc]

omit [p𝒮.IsFibered] in
/-- Naturality of the section bijection on the `𝒴`-component. -/
lemma morSectionEquiv_naturality_snd {U : 𝒞}
    (P P' : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber U) {g₁ g₂ : Over U} (h : g₁ ⟶ g₂)
    (m : (morPresheaf (structureFunctor p𝒳 p𝒴 p𝒮 F G) P P').obj (op g₂)) :
    (pullbackFiberSndIso hF hG P g₁.hom).homCongr (pullbackFiberSndIso hF hG P' g₁.hom)
        (fibSndHom (morRestrict (structureFunctor p𝒳 p𝒴 p𝒮 F G) P P' h m)) =
      morRestrict p𝒴 (fibSnd P) (fibSnd P') h
        ((pullbackFiberSndIso hF hG P g₂.hom).homCongr
          (pullbackFiberSndIso hF hG P' g₂.hom) (fibSndHom m)) := by
  refine morRestrict_uniq p𝒴 (fibSnd P) (fibSnd P') h _ _ ?_
  simp only [Iso.homCongr_apply, Functor.map_comp, Category.assoc,
    fiberInclusion_map_fibSndHom, pullbackFiberSndIso_hom_fac]
  rw [morRestrict_fac_b, pullbackFiberSndIso_inv_naturality_assoc]

/-- The sections of the morphism presheaf of the 2-fibre product over `g` are exactly the sections
of the fibre product of the two legs of the cospan. -/
noncomputable def morSectionEquiv {U : 𝒞}
    (P P' : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber U) (g : Over U) :
    (morPresheaf (structureFunctor p𝒳 p𝒴 p𝒮 F G) P P').obj (op g) ≃
      (Presheaf.eqPullback (hF.morPresheafMap (fibFst P) (fibFst P'))
        (morSnd hF hG P P')).obj (op g) :=
  (fiberHomEquiv _ _).trans (Equiv.subtypeEquiv
    (Equiv.prodCongr ((pullbackFiberFstIso hF hG P g.hom).homCongr
        (pullbackFiberFstIso hF hG P' g.hom))
      ((pullbackFiberSndIso hF hG P g.hom).homCongr
        (pullbackFiberSndIso hF hG P' g.hom)))
    fun αβ => morCondition_iff hF hG P P' g αβ.1 αβ.2)

/-- The section bijection `morSectionEquiv` is natural in `𝒞/U`: the presheaf
`Mor((U, x, y, φ), (U, x', y', φ'))` of the 2-fibre product is the fibre product
`Mor(x, x') ×_{Mor(z, z')} Mor(y, y')`. -/
lemma morSectionEquiv_naturality {U : 𝒞}
    (P P' : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber U) {g₁ g₂ : Over U} (h : g₁ ⟶ g₂)
    (m : (morPresheaf (structureFunctor p𝒳 p𝒴 p𝒮 F G) P P').obj (op g₂)) :
    morSectionEquiv hF hG P P' g₁
        ((morPresheaf (structureFunctor p𝒳 p𝒴 p𝒮 F G) P P').map h.op m) =
      (Presheaf.eqPullback (hF.morPresheafMap (fibFst P) (fibFst P'))
          (morSnd hF hG P P')).map h.op (morSectionEquiv hF hG P P' g₂ m) :=
  Subtype.ext (Prod.ext (morSectionEquiv_naturality_fst hF hG P P' h m)
    (morSectionEquiv_naturality_snd hF hG P P' h m))

/-- The inverse of the section bijection is natural in `𝒞/U`. -/
lemma morSectionEquiv_symm_naturality {U : 𝒞}
    (P P' : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber U) {g₁ g₂ : Over U} (h : g₁ ⟶ g₂)
    (s : (Presheaf.eqPullback (hF.morPresheafMap (fibFst P) (fibFst P'))
      (morSnd hF hG P P')).obj (op g₂)) :
    (morSectionEquiv hF hG P P' g₁).symm
        ((Presheaf.eqPullback (hF.morPresheafMap (fibFst P) (fibFst P'))
          (morSnd hF hG P P')).map h.op s) =
      (morPresheaf (structureFunctor p𝒳 p𝒴 p𝒮 F G) P P').map h.op
        ((morSectionEquiv hF hG P P' g₂).symm s) :=
  (morSectionEquiv hF hG P P' g₁).injective <| by
    rw [Equiv.apply_symm_apply, morSectionEquiv_naturality, Equiv.apply_symm_apply]

/-- Condition (2) of Stacks 026F for the 2-fibre product: if the morphism presheaves of `p𝒳`, `p𝒴`
and `p𝒮` are sheaves, then so are the morphism presheaves of the 2-fibre product. -/
theorem isMorSheaf_structureFunctor (J : GrothendieckTopology 𝒞)
    (h𝒳 : ∀ (V : 𝒞) (a b : p𝒳.Fiber V), Functor.IsMorSheaf p𝒳 J V a b)
    (h𝒴 : ∀ (V : 𝒞) (a b : p𝒴.Fiber V), Functor.IsMorSheaf p𝒴 J V a b)
    (h𝒮 : ∀ (V : 𝒞) (a b : p𝒮.Fiber V), Functor.IsMorSheaf p𝒮 J V a b)
    (U : 𝒞) (P P' : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber U) :
    Functor.IsMorSheaf (structureFunctor p𝒳 p𝒴 p𝒮 F G) J U P P' :=
  (isSheaf_iff_isSheaf_of_type _ _).2
    (Presieve.isSheaf_of_nat_equiv (fun g => (morSectionEquiv hF hG P P' g).symm)
      (fun _ _ h s => morSectionEquiv_symm_naturality hF hG P P' h s)
      ((isSheaf_iff_isSheaf_of_type _ _).1
        (Presheaf.isSheaf_eqPullback _ _ _ (h𝒳 U (fibFst P) (fibFst P'))
          (h𝒴 U (fibSnd P) (fibSnd P')) (h𝒮 U _ _))))


end Fibered


section EqualHomUniverse

/-! ### The morphism presheaf at a base whose hom universe is that of the cospan -/

variable {𝒞 : Type u₁} [Category.{v} 𝒞] {𝒳 : Type u₂} [Category.{v} 𝒳]
  {𝒴 : Type u₃} [Category.{v} 𝒴] {𝒮 : Type u₄} [Category.{v} 𝒮]
  {p𝒳 : 𝒳 ⥤ 𝒞} {p𝒴 : 𝒴 ⥤ 𝒞} {p𝒮 : 𝒮 ⥤ 𝒞} {F : 𝒳 ⥤ 𝒮} {G : 𝒴 ⥤ 𝒮}

variable [p𝒳.IsFibered] [p𝒴.IsFibered] [p𝒮.IsFibered]
  [(structureFunctor p𝒳 p𝒴 p𝒮 F G).IsFibered]
  (hF : Functor.IsFibredOneMorphism p𝒳 p𝒮 F) (hG : Functor.IsFibredOneMorphism p𝒴 p𝒮 G)

include hF hG

/-- The presheaf `Mor((U, x, y, φ), (U, x', y', φ'))` of the 2-fibre product is the fibre product
`Mor(x, x') ×_{Mor(z, z')} Mor(y, y')`. -/
noncomputable def morPresheafEqPullbackIso {U : 𝒞}
    (P P' : (structureFunctor p𝒳 p𝒴 p𝒮 F G).Fiber U) :
    morPresheaf (structureFunctor p𝒳 p𝒴 p𝒮 F G) P P' ≅
      Presheaf.eqPullback (hF.morPresheafMap (fibFst P) (fibFst P')) (morSnd hF hG P P') :=
  NatIso.ofComponents (fun g => Equiv.toIso (morSectionEquiv hF hG P P' g.unop)) <| by
    rintro ⟨g₂⟩ ⟨g₁⟩ ⟨h⟩
    ext m
    exact morSectionEquiv_naturality hF hG P P' h m

end EqualHomUniverse

end TwoFibreProductOver

end CategoryTheory
