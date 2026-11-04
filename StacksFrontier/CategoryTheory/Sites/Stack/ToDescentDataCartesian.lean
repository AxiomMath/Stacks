module

public import StacksFrontier.CategoryTheory.Sites.Stack.DescentDataEquivalence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The canonical functor to descent data, read through cartesian morphisms

Let `p : 𝒳 ⥤ 𝒮` be a fibred category and `f i : X i ⟶ U` a family of morphisms of the base.
The functor `x ↦ (f i^* x, can)` from the fibre over `U` to the descent data of the pullback
pseudofunctor of `p` relative to the family is written in terms of the chosen pullbacks of `p`.
This file translates the statements needed to prove that this functor is an equivalence into
statements about morphisms of `𝒳` lying over the morphisms of the family:

* a descent datum `D` is isomorphic to the canonical descent datum of an object `x` as soon as
  there are cartesian morphisms `κ i : D.obj i ⟶ x` over `f i` which intertwine the gluing
  morphisms of `D` with the identity of `x`, and in a base with fibre products this may be
  checked on the chosen fibre products `X i ×_U X j` alone;
* a morphism of canonical descent data is the image of a morphism `m : x ⟶ y` of the fibre as
  soon as `m` lies, after composition with the chosen cartesian lifts, under its components;
* the gluing morphisms of a descent datum, and the components of a morphism of canonical descent
  data, are compatible with base change in the form of morphisms of `𝒳`.

Every statement is made with the objects of the fibres spelled as objects of the fibres, the
chosen cartesian lift being `CategoryTheory.Functor.pullbackLift`, whose domain is spelled as the
object of `𝒳` underlying the chosen pullback.  The values of the pullback pseudofunctor are the
fibres only up to unfolding; the passages between the two spellings are made once, in
`CategoryTheory.Functor.DescentData.objF`, `CategoryTheory.Functor.DescentData.homF` and their
companions.

## Main results

* `CategoryTheory.Functor.nonempty_iso_toDescentData_of_cartesian_pullback`: the criterion for a
  descent datum to be effective.
* `CategoryTheory.Functor.toDescentData_map_eq_of_cartesian`: the criterion for a morphism of
  canonical descent data to come from the fibre.
* `CategoryTheory.Functor.DescentData.homF_pull`: the gluing morphisms of a descent datum under
  base change.
* `CategoryTheory.Functor.toDescentData_hom_comm_cartesian`: the compatibility of the components
  of a morphism of canonical descent data, in `𝒳`.
-/

@[expose] public noncomputable section

namespace CategoryTheory.Functor

open Opposite IsFibered Pseudofunctor Limits

universe w v₁ v₂ u₁ u₂

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {p : 𝒳 ⥤ 𝒮} [p.IsFibered]

/-! ### The chosen cartesian lift, spelled on objects of the fibres -/

/-- The chosen cartesian lift `f^* x ⟶ x` along `f : V ⟶ U` of an object of the fibre over `U`,
with its domain and codomain spelled as the objects of `𝒳` underlying the chosen pullback and
the object. -/
def pullbackLift {U V : 𝒮} (x : p.Fiber U) (f : V ⟶ U) :
    Fiber.fiberInclusion.obj (pullbackFiber p x f) ⟶ Fiber.fiberInclusion.obj x :=
  IsPreFibered.pullbackMap x.2 f

/-- The chosen cartesian lift is cartesian over the morphism it is chosen along. -/
instance isCartesian_pullbackLift {U V : 𝒮} (x : p.Fiber U) (f : V ⟶ U) :
    p.IsCartesian f (pullbackLift x f) :=
  IsPreFibered.pullbackMap.IsCartesian _ _

/-- The chosen cartesian lift is strongly cartesian, `p` being fibred and not merely
prefibred. -/
instance isStronglyCartesian_pullbackLift {U V : 𝒮} (x : p.Fiber U) (f : V ⟶ U) :
    p.IsStronglyCartesian f (pullbackLift x f) :=
  inferInstance

omit [p.IsFibered] in
/-- Two morphisms of a fibre into the domain of a cartesian morphism agree as soon as they agree
after it. -/
theorem fiber_hom_ext_of_isCartesian {Z W : 𝒮} (b : Z ⟶ W) {a : 𝒳} {z z' : p.Fiber Z}
    (φ' : Fiber.fiberInclusion.obj z' ⟶ a) [hφ' : p.IsCartesian b φ'] (ψ ψ' : z ⟶ z')
    (h : Fiber.fiberInclusion.map ψ ≫ φ' = Fiber.fiberInclusion.map ψ' ≫ φ') : ψ = ψ' :=
  fiber_hom_ext_of_cartesian b φ' hφ' ψ ψ' h

/-- The chosen cartesian lift along a composite, through the contraction of the iterated chosen
pullback. -/
@[reassoc]
theorem pullbackFiberCompIso_hom_pullbackLift {T V Z : 𝒮} (y : p.Fiber T) (f : V ⟶ T)
    (ε : Z ⟶ V) :
    Fiber.fiberInclusion.map (pullbackFiberCompIso y f ε).hom ≫ pullbackLift y (ε ≫ f) =
      pullbackLift (pullbackFiber p y f) ε ≫ pullbackLift y f :=
  pullbackFiberCompIso_hom_fac y f ε

/-- The inverse form of `CategoryTheory.Functor.pullbackFiberCompIso_hom_pullbackLift`. -/
@[reassoc]
theorem pullbackFiberCompIso_inv_pullbackLift {T V Z : 𝒮} (y : p.Fiber T) (f : V ⟶ T)
    (ε : Z ⟶ V) :
    Fiber.fiberInclusion.map (pullbackFiberCompIso y f ε).inv ≫
        pullbackLift (pullbackFiber p y f) ε ≫ pullbackLift y f =
      pullbackLift y (ε ≫ f) :=
  pullbackFiberCompIso_inv_fac y f ε

/-- Base change of a morphism of a fibre, followed by the chosen cartesian lift. -/
@[reassoc]
theorem pullbackFiberHom_pullbackLift {Z W : 𝒮} {y y' : p.Fiber W} (α : y ⟶ y') (b : Z ⟶ W) :
    Fiber.fiberInclusion.map (pullbackFiberHom α b) ≫ pullbackLift y' b =
      pullbackLift y b ≫ Fiber.fiberInclusion.map α :=
  pullbackFiberHom_fac α b

/-- The canonical comparison of two chosen pullbacks along two composites with the same
composite, followed by the chosen cartesian lifts. -/
@[reassoc]
theorem pullbackFiberComparison_pullbackLift {T : 𝒮} (y : p.Fiber T) {V W Z : 𝒮} {f : V ⟶ T}
    {g : W ⟶ T} (ε : Z ⟶ V) (ε' : Z ⟶ W) (heq : ε ≫ f = ε' ≫ g) :
    Fiber.fiberInclusion.map (pullbackFiberComparison y ε ε' heq).hom ≫
        pullbackLift (pullbackFiber p y g) ε' ≫ pullbackLift y g =
      pullbackLift (pullbackFiber p y f) ε ≫ pullbackLift y f :=
  pullbackFiberComparison_hom_fac y ε ε' heq

/-- The morphism from the chosen pullback along a composite to the chosen pullback along the
second factor: it lies over the first factor, and the chosen cartesian lift along the composite
factors through it. -/
def pullbackLiftComp {V Y Y' : 𝒮} (a : p.Fiber V) (ε : Y ⟶ V) (g : Y' ⟶ Y) :
    Fiber.fiberInclusion.obj (pullbackFiber p a (g ≫ ε)) ⟶
      Fiber.fiberInclusion.obj (pullbackFiber p a ε) :=
  Fiber.fiberInclusion.map (pullbackFiberCompIso a ε g).inv ≫
    pullbackLift (pullbackFiber p a ε) g

/-- `CategoryTheory.Functor.pullbackLiftComp` lies over the first factor of the composite. -/
instance isHomLift_pullbackLiftComp {V Y Y' : 𝒮} (a : p.Fiber V) (ε : Y ⟶ V) (g : Y' ⟶ Y) :
    p.IsHomLift g (pullbackLiftComp a ε g) := by
  unfold pullbackLiftComp
  infer_instance

/-- The chosen cartesian lift along a composite factors through `pullbackLiftComp`. -/
theorem pullbackLift_comp {V Y Y' : 𝒮} (a : p.Fiber V) (ε : Y ⟶ V) (g : Y' ⟶ Y) :
    pullbackLift a (g ≫ ε) = pullbackLiftComp a ε g ≫ pullbackLift a ε := by
  rw [pullbackLiftComp, Category.assoc, pullbackFiberCompIso_inv_pullbackLift]

/-- The base change of a morphism between two chosen pullbacks along a further morphism of the
base, conjugated by the contractions of the iterated chosen pullbacks, followed by the chosen
cartesian lift: it is the morphism followed by the chosen cartesian lift, after
`CategoryTheory.Functor.pullbackLiftComp`. -/
theorem pullbackFiberCompIso_conj_pullbackLift {V W Y Y' : 𝒮} (a : p.Fiber V) (b : p.Fiber W)
    (ε : Y ⟶ V) (ε' : Y ⟶ W) (γ : Y' ⟶ Y) (φ : pullbackFiber p a ε ⟶ pullbackFiber p b ε') :
    Fiber.fiberInclusion.map ((pullbackFiberCompIso a ε γ).inv ≫ pullbackFiberHom φ γ ≫
        (pullbackFiberCompIso b ε' γ).hom) ≫ pullbackLift b (γ ≫ ε') =
      pullbackLiftComp a ε γ ≫ Fiber.fiberInclusion.map φ ≫ pullbackLift b ε' := by
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
    pullbackFiberCompIso_hom_pullbackLift, pullbackFiberHom_pullbackLift_assoc,
    pullbackLiftComp, Category.assoc]

/-! ### Descent data, spelled on objects of the fibres -/

variable {U : 𝒮} {ι : Type w} {X : ι → 𝒮} {f : ∀ i, X i ⟶ U}

end CategoryTheory.Functor

namespace CategoryTheory.Pseudofunctor.DescentData

open Functor Functor.IsFibered Opposite Limits

universe w v₁ v₂ u₁ u₂

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {p : 𝒳 ⥤ 𝒮} [p.IsFibered] {U : 𝒮} {ι : Type w} {X : ι → 𝒮} {f : ∀ i, X i ⟶ U}

/-- The object of a descent datum over a member of the family, as an object of the fibre. -/
def objF (D : (pullbackPseudofunctor p).DescentData f) (i : ι) : p.Fiber (X i) := D.obj i

/-- The gluing morphism of a descent datum at a pair of morphisms into two members, as a morphism
of the fibre between the two chosen pullbacks. -/
def homF (D : (pullbackPseudofunctor p).DescentData f) {Y : 𝒮} (q : Y ⟶ U) {i₁ i₂ : ι}
    (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    pullbackFiber p (D.objF i₁) f₁ ⟶ pullbackFiber p (D.objF i₂) f₂ :=
  D.hom q f₁ f₂ hf₁ hf₂

/-- The gluing morphisms of a descent datum compose: at three morphisms into three members of
the family over the same morphism to the base, the gluing morphism from the first to the second
followed by the one from the second to the third is the one from the first to the third. -/
theorem homF_comp (D : (pullbackPseudofunctor p).DescentData f) {Y : 𝒮} (q : Y ⟶ U)
    {i₁ i₂ i₃ : ι} (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (f₃ : Y ⟶ X i₃) (hf₁ : f₁ ≫ f i₁ = q)
    (hf₂ : f₂ ≫ f i₂ = q) (hf₃ : f₃ ≫ f i₃ = q) :
    D.homF q f₁ f₂ hf₁ hf₂ ≫ D.homF q f₂ f₃ hf₂ hf₃ = D.homF q f₁ f₃ hf₁ hf₃ :=
  D.hom_comp q f₁ f₂ f₃ hf₁ hf₂ hf₃

/-- The gluing morphism of a descent datum at a morphism paired with itself is the identity. -/
theorem homF_self (D : (pullbackPseudofunctor p).DescentData f) {Y : 𝒮} (q : Y ⟶ U) {i : ι}
    (g : Y ⟶ X i) (hg : g ≫ f i = q) : D.homF q g g hg hg = 𝟙 _ :=
  D.hom_self q g hg

/-- The gluing morphisms do not depend on the name of the morphism to the base. -/
theorem homF_congr_base (D : (pullbackPseudofunctor p).DescentData f) {Y : 𝒮} (q q' : Y ⟶ U)
    {i₁ i₂ : ι} (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (h₁ : f₁ ≫ f i₁ = q) (h₂ : f₂ ≫ f i₂ = q)
    (h₁' : f₁ ≫ f i₁ = q') (h₂' : f₂ ≫ f i₂ = q') :
    D.homF q f₁ f₂ h₁ h₂ = D.homF q' f₁ f₂ h₁' h₂' := by
  obtain rfl : q = q' := h₁.symm.trans h₁'
  rfl

/-- **The gluing morphisms of a descent datum under base change**, read in `𝒳`: at the
composites with `g : Y' ⟶ Y`, the gluing morphism followed by the chosen cartesian lift is
`CategoryTheory.Functor.pullbackLiftComp` followed by the gluing morphism at `Y` and the chosen
cartesian lift. -/
theorem homF_pull (D : (pullbackPseudofunctor p).DescentData f) {Y Y' : 𝒮}
    (g : Y' ⟶ Y) (q : Y ⟶ U) {i₁ i₂ : ι} (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    Fiber.fiberInclusion.map (D.homF (g ≫ q) (g ≫ f₁) (g ≫ f₂) (by rw [Category.assoc, hf₁])
        (by rw [Category.assoc, hf₂])) ≫ pullbackLift (D.objF i₂) (g ≫ f₂) =
      pullbackLiftComp (D.objF i₁) f₁ g ≫ Fiber.fiberInclusion.map (D.homF q f₁ f₂ hf₁ hf₂) ≫
        pullbackLift (D.objF i₂) f₂ := by
  rw [show D.homF (g ≫ q) (g ≫ f₁) (g ≫ f₂) (by rw [Category.assoc, hf₁])
      (by rw [Category.assoc, hf₂]) = (pullbackFiberCompIso (D.objF i₁) f₁ g).inv ≫
        pullbackFiberHom (D.homF q f₁ f₂ hf₁ hf₂) g ≫ (pullbackFiberCompIso (D.objF i₂) f₂ g).hom
    from (D.pullHom_hom g q (g ≫ q) rfl f₁ f₂ hf₁ hf₂ (g ≫ f₁) (g ≫ f₂) rfl rfl).symm.trans
      (pullHom_eq p (D.obj i₁) (D.obj i₂) f₁ f₂ g (D.hom q f₁ f₂ hf₁ hf₂))]
  exact pullbackFiberCompIso_conj_pullbackLift _ _ f₁ f₂ g _

end CategoryTheory.Pseudofunctor.DescentData

namespace CategoryTheory.Functor

open Opposite IsFibered Pseudofunctor Limits

universe w v₁ v₂ u₁ u₂

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {p : 𝒳 ⥤ 𝒮} [p.IsFibered] {U : 𝒮} {ι : Type w} {X : ι → 𝒮} {f : ∀ i, X i ⟶ U}

/-! ### Canonical descent data, spelled on objects of the fibres -/

variable (f) in
/-- The gluing morphism of the canonical descent datum of an object of the fibre, as a morphism
of the fibre between two iterated chosen pullbacks. -/
@[sga "3 IV 2.1"]
def toDescentDataHomF (x : p.Fiber U) {Y : 𝒮} (q : Y ⟶ U) {i₁ i₂ : ι} (f₁ : Y ⟶ X i₁)
    (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    pullbackFiber p (pullbackFiber p x (f i₁)) f₁ ⟶ pullbackFiber p (pullbackFiber p x (f i₂)) f₂ :=
  (((pullbackPseudofunctor p).toDescentData f).obj x).hom q f₁ f₂ hf₁ hf₂

/-- The gluing morphism of a canonical descent datum is the canonical comparison of the two
iterated chosen pullbacks. -/
theorem toDescentDataHomF_eq (x : p.Fiber U) {Y : 𝒮} (q : Y ⟶ U) {i₁ i₂ : ι} (f₁ : Y ⟶ X i₁)
    (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    toDescentDataHomF f x q f₁ f₂ hf₁ hf₂ =
      (pullbackFiberComparison x f₁ f₂ (hf₁.trans hf₂.symm)).hom :=
  toDescentData_obj_hom p f x q f₁ f₂ hf₁ hf₂ _

/-- The gluing morphisms of a canonical descent datum, followed by the chosen cartesian lifts
down to the object, are the chosen cartesian lifts. -/
@[reassoc]
theorem toDescentDataHomF_pullbackLift (x : p.Fiber U) {Y : 𝒮} (q : Y ⟶ U) {i₁ i₂ : ι}
    (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    Fiber.fiberInclusion.map (toDescentDataHomF f x q f₁ f₂ hf₁ hf₂) ≫
        pullbackLift (pullbackFiber p x (f i₂)) f₂ ≫ pullbackLift x (f i₂) =
      pullbackLift (pullbackFiber p x (f i₁)) f₁ ≫ pullbackLift x (f i₁) := by
  rw [toDescentDataHomF_eq]
  exact pullbackFiberComparison_pullbackLift x f₁ f₂ _

/-- The component at a member of a morphism of canonical descent data, as a morphism of the
fibre between two chosen pullbacks. -/
def descentDataHomF {x y : p.Fiber U}
    (Ψ : ((pullbackPseudofunctor p).toDescentData f).obj x ⟶
      ((pullbackPseudofunctor p).toDescentData f).obj y) (i : ι) :
    pullbackFiber p x (f i) ⟶ pullbackFiber p y (f i) :=
  Ψ.hom i

/-- The components of a morphism of canonical descent data commute with the gluing morphisms. -/
theorem descentDataHomF_comm {x y : p.Fiber U}
    (Ψ : ((pullbackPseudofunctor p).toDescentData f).obj x ⟶
      ((pullbackPseudofunctor p).toDescentData f).obj y) {Y : 𝒮} (q : Y ⟶ U) {i₁ i₂ : ι}
    (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    pullbackFiberHom (descentDataHomF Ψ i₁) f₁ ≫ toDescentDataHomF f y q f₁ f₂ hf₁ hf₂ =
      toDescentDataHomF f x q f₁ f₂ hf₁ hf₂ ≫ pullbackFiberHom (descentDataHomF Ψ i₂) f₂ := by
  rw [← pullbackPseudofunctor_map_map p f₁ (descentDataHomF Ψ i₁),
    ← pullbackPseudofunctor_map_map p f₂ (descentDataHomF Ψ i₂)]
  exact Ψ.comm q f₁ f₂ hf₁ hf₂

/-- **The compatibility of the components of a morphism of canonical descent data**, read in `𝒳`
at a pair of morphisms into two members: the composites of the components with the chosen
cartesian lifts down to `y`, precomposed with the two morphisms from the chosen pullback at the
pair, agree. -/
theorem toDescentData_hom_comm_cartesian {x y : p.Fiber U}
    (Ψ : ((pullbackPseudofunctor p).toDescentData f).obj x ⟶
      ((pullbackPseudofunctor p).toDescentData f).obj y) {Y : 𝒮} (q : Y ⟶ U) {i₁ i₂ : ι}
    (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    pullbackLift (pullbackFiber p x (f i₁)) f₁ ≫
        Fiber.fiberInclusion.map (descentDataHomF Ψ i₁) ≫ pullbackLift y (f i₁) =
      Fiber.fiberInclusion.map (toDescentDataHomF f x q f₁ f₂ hf₁ hf₂) ≫
        pullbackLift (pullbackFiber p x (f i₂)) f₂ ≫
          Fiber.fiberInclusion.map (descentDataHomF Ψ i₂) ≫ pullbackLift y (f i₂) := by
  have h := congrArg (fun φ => Fiber.fiberInclusion.map φ ≫
      pullbackLift (pullbackFiber p y (f i₂)) f₂ ≫ pullbackLift y (f i₂))
    (descentDataHomF_comm Ψ q f₁ f₂ hf₁ hf₂)
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
    toDescentDataHomF_pullbackLift, pullbackFiberHom_pullbackLift_assoc,
    pullbackFiberHom_pullbackLift_assoc] at h
  exact h

/-! ### The criterion for effectivity -/

/-- **A descent datum is the canonical descent datum of an object `x` as soon as it maps to `x`
by cartesian morphisms intertwining its gluing morphisms.**  The cartesian morphisms
`κ i : D.obj i ⟶ x` over `f i` identify the objects of the datum with the chosen pullbacks of
`x`, and the hypothesis `hcomm` — the gluing morphism at `(f₁, f₂)` followed by `κ` is the
chosen lift along `f₁` followed by `κ` — makes these identifications an isomorphism of descent
data. -/
theorem nonempty_iso_toDescentData_of_cartesian (D : (pullbackPseudofunctor p).DescentData f)
    (x : p.Fiber U) (κ : ∀ i, Fiber.fiberInclusion.obj (D.objF i) ⟶ Fiber.fiberInclusion.obj x)
    (hκ : ∀ i, p.IsCartesian (f i) (κ i))
    (hcomm : ∀ ⦃Y : 𝒮⦄ (q : Y ⟶ U) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
      (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q),
      Fiber.fiberInclusion.map (D.homF q f₁ f₂ hf₁ hf₂) ≫ pullbackLift (D.objF i₂) f₂ ≫ κ i₂ =
        pullbackLift (D.objF i₁) f₁ ≫ κ i₁) :
    Nonempty (((pullbackPseudofunctor p).toDescentData f).obj x ≅ D) := by
  let e : ∀ i, pullbackFiber p x (f i) ≅ D.objF i := fun i =>
    fiberIsoOfCartesian (f i) (pullbackLift x (f i)) (κ i) (isCartesian_pullbackLift x (f i))
      (hκ i)
  have he : ∀ i, Fiber.fiberInclusion.map (e i).hom ≫ κ i = pullbackLift x (f i) := fun i => by
    have := hκ i
    exact fiberIsoOfCartesian_hom_fac _ _ _ _ _
  have hcommF : ∀ ⦃Y : 𝒮⦄ (q : Y ⟶ U) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
      (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q),
      pullbackFiberHom (e i₁).hom f₁ ≫ D.homF q f₁ f₂ hf₁ hf₂ =
        toDescentDataHomF f x q f₁ f₂ hf₁ hf₂ ≫ pullbackFiberHom (e i₂).hom f₂ := by
    intro Y q i₁ i₂ f₁ f₂ hf₁ hf₂
    have := hκ i₂
    have hc : p.IsCartesian q (pullbackLift (D.objF i₂) f₂ ≫ κ i₂) := by
      subst hf₂
      infer_instance
    refine fiber_hom_ext_of_isCartesian q (pullbackLift (D.objF i₂) f₂ ≫ κ i₂) _ _ ?_
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
      hcomm q f₁ f₂ hf₁ hf₂, pullbackFiberHom_pullbackLift_assoc, he,
      pullbackFiberHom_pullbackLift_assoc, he, toDescentDataHomF_pullbackLift]
  refine ⟨Pseudofunctor.DescentData.isoMk e ?_⟩
  intro Y q i₁ i₂ f₁ f₂ hf₁ hf₂
  have h := hcommF q f₁ f₂ hf₁ hf₂
  rw [← pullbackPseudofunctor_map_map, ← pullbackPseudofunctor_map_map] at h
  exact h

/-- The hypothesis of `CategoryTheory.Functor.nonempty_iso_toDescentData_of_cartesian` at a
composite with `g : Y' ⟶ Y` follows from the hypothesis at `Y`. -/
theorem descentData_comm_pull (D : (pullbackPseudofunctor p).DescentData f) (x : p.Fiber U)
    (κ : ∀ i, Fiber.fiberInclusion.obj (D.objF i) ⟶ Fiber.fiberInclusion.obj x) {Y Y' : 𝒮}
    (g : Y' ⟶ Y) (q : Y ⟶ U) {i₁ i₂ : ι} (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q)
    (h : Fiber.fiberInclusion.map (D.homF q f₁ f₂ hf₁ hf₂) ≫ pullbackLift (D.objF i₂) f₂ ≫
        κ i₂ = pullbackLift (D.objF i₁) f₁ ≫ κ i₁)
    (q' : Y' ⟶ U) (gf₁ : Y' ⟶ X i₁) (gf₂ : Y' ⟶ X i₂) (hg₁ : g ≫ f₁ = gf₁)
    (hg₂ : g ≫ f₂ = gf₂) (hq₁ : gf₁ ≫ f i₁ = q') (hq₂ : gf₂ ≫ f i₂ = q') :
    Fiber.fiberInclusion.map (D.homF q' gf₁ gf₂ hq₁ hq₂) ≫ pullbackLift (D.objF i₂) gf₂ ≫
        κ i₂ = pullbackLift (D.objF i₁) gf₁ ≫ κ i₁ := by
  subst hg₁ hg₂ hq₁
  rw [D.homF_congr_base _ (g ≫ q) _ _ _ _ (by rw [Category.assoc, hf₁])
    (by rw [Category.assoc, hf₂]), ← Category.assoc, D.homF_pull g q f₁ f₂ hf₁ hf₂,
    pullbackLift_comp, Category.assoc, Category.assoc, Category.assoc, h]

/-- **The criterion for effectivity, on the chosen fibre products.**  In a base with fibre
products the intertwining hypothesis of
`CategoryTheory.Functor.nonempty_iso_toDescentData_of_cartesian` need only be checked at the two
projections of the chosen fibre products `X i ×_U X j`, every pair of morphisms into two members
agreeing over `U` factoring through one of them. -/
theorem nonempty_iso_toDescentData_of_cartesian_pullback [HasPullbacks 𝒮]
    (D : (pullbackPseudofunctor p).DescentData f) (x : p.Fiber U)
    (κ : ∀ i, Fiber.fiberInclusion.obj (D.objF i) ⟶ Fiber.fiberInclusion.obj x)
    (hκ : ∀ i, p.IsCartesian (f i) (κ i))
    (hcomm : ∀ i j : ι,
      Fiber.fiberInclusion.map (D.homF (pullback.fst (f i) (f j) ≫ f i)
          (pullback.fst (f i) (f j)) (pullback.snd (f i) (f j)) rfl pullback.condition.symm) ≫
          pullbackLift (D.objF j) (pullback.snd (f i) (f j)) ≫ κ j =
        pullbackLift (D.objF i) (pullback.fst (f i) (f j)) ≫ κ i) :
    Nonempty (((pullbackPseudofunctor p).toDescentData f).obj x ≅ D) := by
  refine nonempty_iso_toDescentData_of_cartesian D x κ hκ ?_
  intro Y q i₁ i₂ f₁ f₂ hf₁ hf₂
  exact descentData_comm_pull D x κ (pullback.lift f₁ f₂ (hf₁.trans hf₂.symm))
    (pullback.fst (f i₁) (f i₂) ≫ f i₁) (pullback.fst (f i₁) (f i₂))
    (pullback.snd (f i₁) (f i₂)) rfl pullback.condition.symm (hcomm i₁ i₂) q f₁ f₂
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) hf₁ hf₂

/-! ### The criterion for a morphism of canonical descent data to come from the fibre -/

/-- The components of the image of a morphism of the fibre, followed by the chosen cartesian lift,
are the chosen cartesian lift followed by the morphism. -/
private theorem toDescentData_map_hom_pullbackLift {x y : p.Fiber U} (m : x ⟶ y) (i : ι) :
    Fiber.fiberInclusion.map ((((pullbackPseudofunctor p).toDescentData f).map m).hom i) ≫
        pullbackLift y (f i) = pullbackLift x (f i) ≫ Fiber.fiberInclusion.map m := by
  have h := pullbackFiberHom_pullbackLift m (f i)
  rw [← pullbackPseudofunctor_map_map] at h
  exact h

/-- **A morphism of canonical descent data is the image of a morphism `m` of the fibre as soon as
`m` lies, after the chosen cartesian lifts, under the components of the morphism.** -/
theorem toDescentData_map_eq_of_cartesian {x y : p.Fiber U}
    (Ψ : ((pullbackPseudofunctor p).toDescentData f).obj x ⟶
      ((pullbackPseudofunctor p).toDescentData f).obj y) (m : x ⟶ y)
    (hm : ∀ i, pullbackLift x (f i) ≫ Fiber.fiberInclusion.map m =
      Fiber.fiberInclusion.map (descentDataHomF Ψ i) ≫ pullbackLift y (f i)) :
    ((pullbackPseudofunctor p).toDescentData f).map m = Ψ := by
  ext i
  refine fiber_hom_ext_of_isCartesian (f i) (pullbackLift y (f i)) _ _ ?_
  exact (toDescentData_map_hom_pullbackLift m i).trans (hm i)

/-- A morphism of the fibre whose image under the canonical functor to descent data is the image
of a second one agrees with it after every chosen cartesian lift. -/
theorem pullbackLift_comp_eq_of_toDescentData_map_eq {x y : p.Fiber U} {φ ψ : x ⟶ y}
    (h : ((pullbackPseudofunctor p).toDescentData f).map φ =
      ((pullbackPseudofunctor p).toDescentData f).map ψ) (i : ι) :
    pullbackLift x (f i) ≫ Fiber.fiberInclusion.map φ =
      pullbackLift x (f i) ≫ Fiber.fiberInclusion.map ψ := by
  rw [← toDescentData_map_hom_pullbackLift φ i, ← toDescentData_map_hom_pullbackLift ψ i]
  exact congrArg (fun Ψ => Fiber.fiberInclusion.map (Ψ.hom i) ≫ pullbackLift y (f i)) h

end CategoryTheory.Functor

end
