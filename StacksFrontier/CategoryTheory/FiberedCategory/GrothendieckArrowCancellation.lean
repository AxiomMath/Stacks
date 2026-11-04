module

public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.FiberedCategory.Grothendieck
public import StacksFrontier.CategoryTheory.FibredOneMorphism
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.PullbackFiberHom
public import StacksFrontier.CategoryTheory.FiberedCategory.HomLift
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Morphisms of a Grothendieck construction out of a fibre, and their arrows

Let `F` be a pseudofunctor from the locally discrete bicategory on `𝒞ᵒᵖ` to `Cat`, so that the
Grothendieck construction `∫ᶜ F` is a fibred category over `𝒞` whose fibre over `T` is `F(T)`.
A vertical morphism of `∫ᶜ F` out of the fibre over `T` is the image under
`CategoryTheory.Pseudofunctor.CoGrothendieck.ι` of a morphism of `F(T)`, and the chosen cartesian
lift of `f : R ⟶ T` at an object `a` of `F(T)` is
`CategoryTheory.Pseudofunctor.CoGrothendieck.cartesianLift`.

This file sets up the dictionary between morphisms of `∫ᶜ F` out of an object of a fibre and
*arrows* of a fibre, and transports it along a 1-morphism of fibred categories out of `∫ᶜ F`.
A morphism of `∫ᶜ F` from an object of the fibre over `V` to an object of the fibre over `T` which
lies over `g : V ⟶ T` is, by the very definition of `∫ᶜ F`, a morphism of `F(V)` from the first
object to the restriction along `g` of the second
(`CategoryTheory.Pseudofunctor.CoGrothendieck.homOf`); the composition law and the chosen cartesian
lifts are read in that normal form, and the comparison isomorphisms supplied by strong
cartesianness carry the dictionary over to the receiving category.

## Main definitions

* `CategoryTheory.Pseudofunctor.CoGrothendieck.homOf`: the morphism of `∫ᶜ F` over a prescribed
  morphism of the base with a prescribed fibre component, with
  `CategoryTheory.Pseudofunctor.CoGrothendieck.homOf_comp`,
  `CategoryTheory.Pseudofunctor.CoGrothendieck.homOf_inj`,
  `CategoryTheory.Pseudofunctor.CoGrothendieck.cartesianLift_eq_homOf`,
  `CategoryTheory.Pseudofunctor.CoGrothendieck.ι_map_eq_homOf` and
  `CategoryTheory.Pseudofunctor.CoGrothendieck.exists_homOf_of_base`.

## Main results

* `CategoryTheory.Pseudofunctor.CoGrothendieck.cartesianLift_comp_ι_map_eq_iff`: the chosen
  cartesian lift of `f` followed by two vertical arrows of `F(T)` gives the same morphism exactly
  when the two arrows have the same image under `F(f)`.
* `CategoryTheory.Pseudofunctor.CoGrothendieck.cartesianLift_comp_ι_map`: for a pseudofunctor
  coming from an ordinary functor, the chosen cartesian lift is natural in the vertical arrows.
* `CategoryTheory.Pseudofunctor.CoGrothendieck.exists_homOf_eq_of_isHomLift`,
  `CategoryTheory.Pseudofunctor.CoGrothendieck.homOf_eq_of_map_eq` and
  `CategoryTheory.Pseudofunctor.CoGrothendieck.exists_restrict_homOf`: for a 1-morphism of fibred
  categories out of `∫ᶜ F` which is full on fibres, every morphism over `g` out of the image of an
  object of a fibre is the image of a morphism in normal form; the normal form is determined by
  the morphism it induces; and restricting along a strongly cartesian morphism prefixes a chosen
  cartesian lift.
* `CategoryTheory.Functor.map_comp_eq_iff_of_isStronglyCartesian`: for a faithful 1-morphism of
  fibred categories, precomposing with a strongly cartesian morphism over `f` identifies the
  images of two morphisms exactly when precomposing with a chosen cartesian lift over `f`
  identifies the two morphisms themselves.
* `CategoryTheory.Functor.exists_isStronglyCartesian_factor_of_comp_eq`: a strongly cartesian
  morphism over `χ ≫ u(d)` factors through the image of a strongly cartesian morphism over `d`,
  and the image of a second one cancels.
* `CategoryTheory.Functor.pullbackFiberHom_eq_of_comp_eq`: two morphisms of a fibre have the same
  base change along `c` as soon as one strongly cartesian morphism over `c` equalizes them.
* `CategoryTheory.Pseudofunctor.CoGrothendieck.exists_eqToHom_comp`,
  `CategoryTheory.Pseudofunctor.CoGrothendieck.exists_eqToHom_id`,
  `CategoryTheory.Pseudofunctor.CoGrothendieck.exists_eqToHom_map` and
  `CategoryTheory.Pseudofunctor.CoGrothendieck.eq_of_exists_eqToHom`: the bookkeeping of
  transports, with which the coherence constraints of a pseudofunctor coming from an ordinary
  functor are handled.
* `CategoryTheory.Functor.isStronglyCartesian_of_isHomLift`,
  `CategoryTheory.Functor.isStronglyCartesian_comp_isoOverId`,
  `CategoryTheory.Functor.isHomLift_comp_functor` and
  `CategoryTheory.Functor.exists_isStronglyCartesian_restrict`: the bookkeeping of strong
  cartesianness used throughout.

## Implementation notes

The composition law of the Grothendieck construction does not rewrite under `simp only`: the
morphism whose fibre component is to be read off is built from
`CategoryTheory.Pseudofunctor.CoGrothendieck.categoryStruct`, whereas the composite is formed in
the category instance, and the two are not matched at `implicit` transparency. The fibre component
is therefore named by a local `have` proved by `rfl` and used in term mode. For the same reason
the two isomorphisms to be cancelled are passed to `cancel_mono` explicitly: given as
placeholders they are read off the goal in a form against which the `IsIso` hypotheses are not
matched.

## References

* [Stacks Project, Tag 003T](https://stacks.math.columbia.edu/tag/003T)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe v₁ u₁ v₂ u₂ v v₃ u₃ u₄

namespace CategoryTheory.Pseudofunctor.CoGrothendieck

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮]
  {F : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat.{v₂, u₂}}

/-- **The chosen cartesian lift of `f` cancels in front of a vertical arrow.** Two arrows of the
fibre `F(S)` give the same morphism after the chosen cartesian lift of `f : R ⟶ S` exactly when
they have the same image under the restriction functor `F(f)`. -/
theorem cartesianLift_comp_ι_map_eq_iff {R S : 𝒮} {a a' : F.obj ⟨op S⟩} (f : R ⟶ S)
    (δ₁ δ₂ : a ⟶ a') :
    cartesianLift a f ≫ (ι F S).map δ₁ = cartesianLift a f ≫ (ι F S).map δ₂ ↔
      (F.map f.op.toLoc).toFunctor.map δ₁ = (F.map f.op.toLoc).toFunctor.map δ₂ := by
  have fib : ∀ δ : a ⟶ a', (cartesianLift a f ≫ (ι F S).map δ).fiber =
      𝟙 ((F.map f.op.toLoc).toFunctor.obj a) ≫
        (F.map f.op.toLoc).toFunctor.map (δ ≫ (F.mapId ⟨op S⟩).inv.toNatTrans.app a') ≫
          (F.mapComp (𝟙 S).op.toLoc f.op.toLoc).inv.toNatTrans.app a' := fun _ => rfl
  have hc : IsIso ((F.mapComp (𝟙 S).op.toLoc f.op.toLoc).inv.toNatTrans.app a') :=
    NatIso.isIso_app_of_isIso (F.mapComp (𝟙 S).op.toLoc f.op.toLoc).inv.toNatTrans a'
  have hi : IsIso ((F.mapId ⟨op S⟩).inv.toNatTrans.app a') :=
    NatIso.isIso_app_of_isIso (F.mapId ⟨op S⟩).inv.toNatTrans a'
  constructor
  · intro h
    have h1 : 𝟙 ((F.map f.op.toLoc).toFunctor.obj a) ≫
          (F.map f.op.toLoc).toFunctor.map (δ₁ ≫ (F.mapId ⟨op S⟩).inv.toNatTrans.app a') ≫
            (F.mapComp (𝟙 S).op.toLoc f.op.toLoc).inv.toNatTrans.app a' =
        𝟙 ((F.map f.op.toLoc).toFunctor.obj a) ≫
          (F.map f.op.toLoc).toFunctor.map (δ₂ ≫ (F.mapId ⟨op S⟩).inv.toNatTrans.app a') ≫
            (F.mapComp (𝟙 S).op.toLoc f.op.toLoc).inv.toNatTrans.app a' :=
      (Hom.congr h).trans (Category.comp_id _)
    simp only [Category.id_comp, Functor.map_comp] at h1
    have h2 := (cancel_mono
      ((F.mapComp (𝟙 S).op.toLoc f.op.toLoc).inv.toNatTrans.app a')).1 h1
    exact (cancel_mono ((F.map f.op.toLoc).toFunctor.map
      ((F.mapId ⟨op S⟩).inv.toNatTrans.app a'))).1 h2
  · intro h
    refine Hom.ext _ _ rfl (Eq.trans ?_ (Category.comp_id _).symm)
    refine (fib δ₁).trans (Eq.trans ?_ (fib δ₂).symm)
    refine congrArg (fun t => 𝟙 ((F.map f.op.toLoc).toFunctor.obj a) ≫ t ≫
      (F.mapComp (𝟙 S).op.toLoc f.op.toLoc).inv.toNatTrans.app a') ?_
    exact (Functor.map_comp _ δ₁ _).trans
      ((congrArg (fun t => t ≫ (F.map f.op.toLoc).toFunctor.map
        ((F.mapId ⟨op S⟩).inv.toNatTrans.app a')) h).trans
        (Functor.map_comp _ δ₂ _).symm)

section NormalForm

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮]
  {F : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat.{v₂, u₂}}

/-- **The morphism of `∫ᶜ F` over `g` with prescribed fibre component.** Every morphism of
`∫ᶜ F` out of an object of the fibre over `V` which lies over `g : V ⟶ T` is of this form. -/
def homOf {V T : 𝒮} (g : V ⟶ T) {c : F.obj ⟨op V⟩} {b : F.obj ⟨op T⟩}
    (γ : c ⟶ (F.map g.op.toLoc).toFunctor.obj b) :
    (⟨V, c⟩ : CoGrothendieck F) ⟶ ⟨T, b⟩ := ⟨g, γ⟩

/-- The chosen cartesian lift of `g` is the morphism over `g` with identity fibre component. -/
theorem cartesianLift_eq_homOf {V T : 𝒮} (g : V ⟶ T) (b : F.obj ⟨op T⟩) :
    cartesianLift b g = homOf g (𝟙 ((F.map g.op.toLoc).toFunctor.obj b)) := rfl

/-- A vertical morphism is the morphism over an identity whose fibre component is the given arrow
followed by the unit constraint. -/
theorem ι_map_eq_homOf {V : 𝒮} {c c' : F.obj ⟨op V⟩} (ε : c ⟶ c') :
    (ι F V).map ε = homOf (𝟙 V) (ε ≫ (F.mapId ⟨op V⟩).inv.toNatTrans.app c') := rfl

/-- The composition law of `∫ᶜ F` in the normal form. -/
theorem homOf_comp {V T U : 𝒮} (g₁ : V ⟶ T) (g₂ : T ⟶ U) {c : F.obj ⟨op V⟩}
    {b : F.obj ⟨op T⟩} {b' : F.obj ⟨op U⟩}
    (γ₁ : c ⟶ (F.map g₁.op.toLoc).toFunctor.obj b)
    (γ₂ : b ⟶ (F.map g₂.op.toLoc).toFunctor.obj b') :
    homOf g₁ γ₁ ≫ homOf g₂ γ₂ =
      homOf (g₁ ≫ g₂) (γ₁ ≫ (F.map g₁.op.toLoc).toFunctor.map γ₂ ≫
        (F.mapComp g₂.op.toLoc g₁.op.toLoc).inv.toNatTrans.app b') := rfl

/-- The normal form is injective in the fibre component. -/
theorem homOf_inj {V T : 𝒮} (g : V ⟶ T) {c : F.obj ⟨op V⟩} {b : F.obj ⟨op T⟩}
    (γ₁ γ₂ : c ⟶ (F.map g.op.toLoc).toFunctor.obj b) (h : homOf g γ₁ = homOf g γ₂) :
    γ₁ = γ₂ := (Hom.congr h).trans (Category.comp_id _)

/-- **Every morphism of `∫ᶜ F` out of an object of a fibre with prescribed base is in normal
form.** -/
theorem exists_homOf_of_base {V T : 𝒮} {c : F.obj ⟨op V⟩} {b : F.obj ⟨op T⟩}
    (w : (⟨V, c⟩ : CoGrothendieck F) ⟶ ⟨T, b⟩) {g : V ⟶ T} (hg : w.base = g) :
    ∃ γ : c ⟶ (F.map g.op.toLoc).toFunctor.obj b, w = homOf g γ := by
  subst hg
  exact ⟨w.fiber, rfl⟩

/-- The fibre comparison of a 1-morphism out of a Grothendieck construction: the inclusion of the
fibre over `T` followed by the 1-morphism is strictly over the constant functor at `T`. -/
theorem ι_comp_comp_eq {𝒯 : Type u₄} [Category.{v₃} 𝒯] {r : 𝒯 ⥤ 𝒮}
    {N : CoGrothendieck F ⥤ 𝒯} (hN : (forget F).IsFibredOneMorphism r N) (T : 𝒮) :
    (ι F T ⋙ N) ⋙ r = (Functor.const (F.obj ⟨op T⟩)).obj T := by
  rw [Functor.assoc, hN.comp_eq]
  exact comp_const F T


end NormalForm

section Transports

variable {D : Type u₃} [Category.{v} D]

/-- A composite of two transports is a transport. -/
theorem exists_eqToHom_comp {x y z : D} {f : x ⟶ y} {g : y ⟶ z}
    (hf : ∃ p : x = y, f = eqToHom p) (hg : ∃ q : y = z, g = eqToHom q) :
    ∃ r : x = z, f ≫ g = eqToHom r := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p.trans q, by rw [hp, hq, eqToHom_trans]⟩

/-- An identity is a transport. -/
theorem exists_eqToHom_id (x : D) : ∃ p : x = x, 𝟙 x = eqToHom p := ⟨rfl, by simp⟩

/-- The image of a transport under a functor is a transport. -/
theorem exists_eqToHom_map {C : Type u₄} [Category.{v₃} C] (Ψ : C ⥤ D) {x y : C}
    {f : x ⟶ y} (hf : ∃ p : x = y, f = eqToHom p) :
    ∃ p : Ψ.obj x = Ψ.obj y, Ψ.map f = eqToHom p := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨congrArg Ψ.obj p, by rw [hp, eqToHom_map]⟩

/-- Two transports between the same pair of objects agree. -/
theorem eq_of_exists_eqToHom {x y : D} {f g : x ⟶ y}
    (hf : ∃ p : x = y, f = eqToHom p) (hg : ∃ q : x = y, g = eqToHom q) : f = g := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  rw [hp, hq]

end Transports

section Naturality

attribute [local implicit_reducible] Functor.toPseudofunctor'
  pseudofunctorOfIsLocallyDiscrete Quiver.Hom.toLoc

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] (K : 𝒞ᵒᵖ ⥤ Cat.{v₂, u₂})

/-- **The chosen cartesian lift of `f` is natural in the vertical arrows.** Restricting an arrow
of the fibre over `S` along `f : R ⟶ S` and then taking the chosen cartesian lift agrees with
taking the chosen cartesian lift and then the arrow.

For a pseudofunctor coming from an ordinary functor into the strict bicategory `Cat`, the unit and
composition constraints are transports, so the two composites have the same base and their fibre
components differ from the restricted arrow by transports between the same pair of objects. -/
theorem cartesianLift_comp_ι_map {R S : 𝒞} {b b' : K.toPseudofunctor'.obj ⟨op S⟩} (f : R ⟶ S)
    (g : b ⟶ b') :
    cartesianLift (F := K.toPseudofunctor') b f ≫ (ι K.toPseudofunctor' S).map g =
      (ι K.toPseudofunctor' R).map ((K.toPseudofunctor'.map f.op.toLoc).toFunctor.map g) ≫
        cartesianLift b' f := by
  have hbL : (cartesianLift (F := K.toPseudofunctor') b f ≫
      (ι K.toPseudofunctor' S).map g).base = f ≫ 𝟙 S := rfl
  have hbR : ((ι K.toPseudofunctor' R).map
        ((K.toPseudofunctor'.map f.op.toLoc).toFunctor.map g) ≫
      cartesianLift (F := K.toPseudofunctor') b' f).base = 𝟙 R ≫ f := rfl
  have hL : (cartesianLift (F := K.toPseudofunctor') b f ≫
      (ι K.toPseudofunctor' S).map g).fiber =
      𝟙 ((K.toPseudofunctor'.map f.op.toLoc).toFunctor.obj b) ≫
        (K.toPseudofunctor'.map f.op.toLoc).toFunctor.map
          (g ≫ (K.toPseudofunctor'.mapId ⟨op S⟩).inv.toNatTrans.app b') ≫
          (K.toPseudofunctor'.mapComp (𝟙 S).op.toLoc f.op.toLoc).inv.toNatTrans.app b' := rfl
  have hR : ((ι K.toPseudofunctor' R).map
        ((K.toPseudofunctor'.map f.op.toLoc).toFunctor.map g) ≫
      cartesianLift (F := K.toPseudofunctor') b' f).fiber =
      ((K.toPseudofunctor'.map f.op.toLoc).toFunctor.map g ≫
          (K.toPseudofunctor'.mapId ⟨op R⟩).inv.toNatTrans.app
            ((K.toPseudofunctor'.map f.op.toLoc).toFunctor.obj b')) ≫
        (K.toPseudofunctor'.map (𝟙 R).op.toLoc).toFunctor.map
          (𝟙 ((K.toPseudofunctor'.map f.op.toLoc).toFunctor.obj b')) ≫
          (K.toPseudofunctor'.mapComp f.op.toLoc (𝟙 R).op.toLoc).inv.toNatTrans.app b' := rfl
  have hu₁ : ∃ p, (K.toPseudofunctor'.mapId ⟨op S⟩).inv.toNatTrans.app b' = eqToHom p :=
    ⟨_, by rw [Functor.toPseudofunctor'_mapId, eqToIso.inv, Cat.eqToHom_app]⟩
  have hu₂ : ∃ p, (K.toPseudofunctor'.mapComp (𝟙 S).op.toLoc f.op.toLoc).inv.toNatTrans.app b' =
      eqToHom p := ⟨_, by rw [Functor.toPseudofunctor'_mapComp, eqToIso.inv, Cat.eqToHom_app]⟩
  have hv₁ : ∃ p, (K.toPseudofunctor'.mapId ⟨op R⟩).inv.toNatTrans.app
      ((K.toPseudofunctor'.map f.op.toLoc).toFunctor.obj b') = eqToHom p :=
    ⟨_, by rw [Functor.toPseudofunctor'_mapId, eqToIso.inv, Cat.eqToHom_app]⟩
  have hv₂ : ∃ p, (K.toPseudofunctor'.mapComp f.op.toLoc (𝟙 R).op.toLoc).inv.toNatTrans.app b' =
      eqToHom p := ⟨_, by rw [Functor.toPseudofunctor'_mapComp, eqToIso.inv, Cat.eqToHom_app]⟩
  refine Hom.ext _ _ (by rw [hbL, hbR, Category.comp_id, Category.id_comp]) ?_
  rw [hL, hR]
  simp only [Functor.map_comp, Category.id_comp, Category.assoc]
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine congrArg (fun t => (K.toPseudofunctor'.map f.op.toLoc).toFunctor.map g ≫ t) ?_
  refine eq_of_exists_eqToHom (exists_eqToHom_comp (exists_eqToHom_map _ hu₁) hu₂) ?_
  exact exists_eqToHom_comp
    (exists_eqToHom_comp hv₁ (exists_eqToHom_comp
      (exists_eqToHom_map _ (exists_eqToHom_id _)) hv₂)) ⟨_, rfl⟩

end Naturality

end CategoryTheory.Pseudofunctor.CoGrothendieck

namespace CategoryTheory.Functor

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒜 : Type u₃} [Category.{v} 𝒜] {ℬ : Type u₄}
  [Category.{v₃} ℬ]

-- `CategoryTheory.Functor.isHomLift_comp_functor` moved to
-- `StacksFrontier.CategoryTheory.FiberedCategory.HomLift` (import closure 1), the module that
-- collects the `IsHomLift` lemmas this development needs and Mathlib does not have. Three
-- `private` re-declarations of it elsewhere were retired onto it; keeping it here would
-- have made each of those files import this one.

/-- Two strongly cartesian morphisms over the same morphism with the same codomain differ by an
isomorphism over an identity. -/
private theorem exists_isIso_comp_eq_of_isStronglyCartesian {𝒳 : Type u₃} [Category.{v} 𝒳]
    {p : 𝒳 ⥤ 𝒞} {R S : 𝒞} {f : R ⟶ S} {a a' b : 𝒳} {φ : a ⟶ b} {ψ : a' ⟶ b}
    (hφ : p.IsStronglyCartesian f φ) (hψ : p.IsStronglyCartesian f ψ) :
    ∃ ι : a' ⟶ a, IsIso ι ∧ p.IsHomLift (𝟙 R) ι ∧ ι ≫ φ = ψ := by
  have hrefl : f = (Iso.refl R).hom ≫ f := by simp
  exact ⟨(IsStronglyCartesian.domainIsoOfBaseIso p hrefl φ ψ).hom, inferInstance,
    IsStronglyCartesian.domainUniqueUpToIso_inv_isHomLift p hrefl φ ψ,
    IsStronglyCartesian.fac p f φ hrefl ψ⟩

/-- **A strongly cartesian morphism may be replaced by a chosen cartesian lift over the same
morphism of the base.** Let `N` be a faithful 1-morphism of fibred categories, let `lam` be
strongly cartesian over `f` with codomain `y`, and let `μ` be strongly cartesian over `f` with
codomain `N(y)`. Then two morphisms out of `y` are identified by `N` after precomposition with
`μ` exactly when they are identified after precomposition with `lam`.

The two strongly cartesian morphisms differ by an isomorphism over an identity, which is an
epimorphism, and `N` is faithful. -/
theorem map_comp_eq_iff_of_isStronglyCartesian {q : 𝒜 ⥤ 𝒞} {r : ℬ ⥤ 𝒞} {N : 𝒜 ⥤ ℬ}
    (hN : q.IsFibredOneMorphism r N) (hfaith : N.Faithful) {R T : 𝒞} {f : R ⟶ T} {x y : 𝒜}
    (lam : x ⟶ y) (hlam : q.IsStronglyCartesian f lam) {z : ℬ} (μ : z ⟶ N.obj y)
    (hμ : r.IsStronglyCartesian f μ) {y' : 𝒜} (g₁ g₂ : y ⟶ y') :
    μ ≫ N.map g₁ = μ ≫ N.map g₂ ↔ lam ≫ g₁ = lam ≫ g₂ := by
  have hNlam : r.IsStronglyCartesian f (N.map lam) :=
    hN.map_isStronglyCartesian f lam hlam
  obtain ⟨ι, hiso, -, hfac⟩ := exists_isIso_comp_eq_of_isStronglyCartesian hNlam hμ
  constructor
  · intro h
    refine hfaith.map_injective ?_
    rw [N.map_comp, N.map_comp]
    refine (cancel_epi ι).1 ?_
    rwa [← Category.assoc, ← Category.assoc, hfac]
  · intro h
    rw [← hfac, Category.assoc, Category.assoc, ← N.map_comp, ← N.map_comp, h]

/-- **A morphism strongly cartesian over one morphism of the base is strongly cartesian over
every morphism of the base it lifts.** -/
lemma isStronglyCartesian_of_isHomLift {𝒳 : Type u₃} [Category.{v} 𝒳] {p : 𝒳 ⥤ 𝒞}
    {R S R' S' : 𝒞} {x y : 𝒳} {f : R ⟶ S} {φ : x ⟶ y} (hf : p.IsStronglyCartesian f φ)
    (g : R' ⟶ S') (hg : p.IsHomLift g φ) : p.IsStronglyCartesian g φ := by
  subst_hom_lift p g φ
  cases (IsStronglyCartesian.toIsHomLift : p.IsHomLift f φ)
  assumption

/-- **Composing a strongly cartesian morphism with an isomorphism lying over an identity leaves
the morphism of the base it is strongly cartesian over unchanged.** -/
@[sga "1 VI 6.13" "special case"]
lemma isStronglyCartesian_comp_isoOverId {𝒳 : Type u₃} [Category.{v} 𝒳] {p : 𝒳 ⥤ 𝒞} {R S : 𝒞}
    {x y w : 𝒳} {f : R ⟶ S} {φ : x ⟶ y} (hφ : p.IsStronglyCartesian f φ) (ψ : y ⟶ w)
    (hψ : p.IsHomLift (𝟙 S) ψ) (hiso : IsIso ψ) : p.IsStronglyCartesian f (φ ≫ ψ) := by
  have h4 : p.IsStronglyCartesian (𝟙 S) ψ := IsStronglyCartesian.of_isIso p (𝟙 S) ψ
  have h5 := IsStronglyCartesian.comp p (f := f) (g := 𝟙 S) (φ := φ) (ψ := ψ)
  rwa [Category.comp_id] at h5

/-- **A strongly cartesian morphism restricts to a strongly cartesian morphism over a composite.**
The chosen cartesian lift of `f` at the domain, followed by the given morphism, is strongly
cartesian over `f ≫ g`. -/
theorem exists_isStronglyCartesian_restrict {𝒳 : Type u₃} [Category.{v} 𝒳] (p : 𝒳 ⥤ 𝒞)
    [p.IsFibered] {R S T : 𝒞} (f : R ⟶ S) (g : S ⟶ T) {y b : 𝒳} (φ : y ⟶ b)
    (hφ : p.IsStronglyCartesian g φ) :
    ∃ (x : 𝒳) (ψ : x ⟶ y), p.IsStronglyCartesian f ψ ∧
      p.IsStronglyCartesian (f ≫ g) (ψ ≫ φ) := by
  have hy : p.obj y = S := IsHomLift.domain_eq p g φ
  have hψ : p.IsStronglyCartesian f (IsPreFibered.pullbackMap hy f) := by
    have := IsPreFibered.pullbackMap.IsCartesian hy f
    infer_instance
  exact ⟨_, IsPreFibered.pullbackMap hy f, hψ,
    IsStronglyCartesian.comp p (f := f) (g := g) (φ := IsPreFibered.pullbackMap hy f) (ψ := φ)⟩

/-- **A strongly cartesian morphism over `χ ≫ u(d)` factors through the image of a strongly
cartesian morphism over `d`, and the image of a second one cancels.** Let `F` be a functor over
`u` carrying strongly cartesian morphisms to strongly cartesian morphisms, let `ex` and `gy` be
strongly cartesian over `d`, and let `t₁`, `t₂` be vertical morphisms with
`ex ≫ nⱼ = tⱼ ≫ gy`. If `M` is strongly cartesian over `χ ≫ u(d)` and identifies the images of
`n₁` and `n₂`, then the induced morphism over `χ` identifies the images of `t₁` and `t₂`.

The images of `ex` and `gy` are strongly cartesian over `u(d)`; the first produces the
factorization of `M` and the second cancels, both being tested against morphisms lying over
`χ`. -/
theorem exists_isStronglyCartesian_factor_of_comp_eq {𝒟 : Type u₂} [Category.{v₂} 𝒟]
    {𝒮 : Type u₃} [Category.{v} 𝒮] {𝒯 : Type u₄} [Category.{v₃} 𝒯]
    {p : 𝒮 ⥤ 𝒞} {q : 𝒯 ⥤ 𝒟} {u : 𝒞 ⥤ 𝒟} {F : 𝒮 ⥤ 𝒯} (hF : F ⋙ q = p ⋙ u)
    (hFsc : ∀ {x y : 𝒮} (α : x ⟶ y), q.IsStronglyCartesian ((p ⋙ u).map α) (F.map α))
    {W U : 𝒞} {d : W ⟶ U} {sx sy xA yB : 𝒮} {ex : sx ⟶ xA} {gy : sy ⟶ yB}
    (hex : p.IsStronglyCartesian d ex) (hgy : p.IsStronglyCartesian d gy)
    {V₁ : 𝒟} {χ : V₁ ⟶ u.obj W} {z : 𝒯} (M : z ⟶ F.obj xA)
    (hM : q.IsStronglyCartesian (χ ≫ u.map d) M)
    {t₁ t₂ : sx ⟶ sy} (ht₁ : p.IsHomLift (𝟙 W) t₁) (ht₂ : p.IsHomLift (𝟙 W) t₂)
    {n₁ n₂ : xA ⟶ yB} (hs₁ : ex ≫ n₁ = t₁ ≫ gy) (hs₂ : ex ≫ n₂ = t₂ ≫ gy)
    (hyp : M ≫ F.map n₁ = M ≫ F.map n₂) :
    ∃ κ : z ⟶ F.obj sx, q.IsStronglyCartesian χ κ ∧ κ ≫ F.map t₁ = κ ≫ F.map t₂ := by
  have hexl : (p ⋙ u).IsHomLift (u.map d) ex := isHomLift_comp_functor u d ex hex.toIsHomLift
  have hgyl : (p ⋙ u).IsHomLift (u.map d) gy := isHomLift_comp_functor u d gy hgy.toIsHomLift
  have hFex : q.IsStronglyCartesian (u.map d) (F.map ex) :=
    isStronglyCartesian_of_isHomLift (hFsc ex) (u.map d)
      (isHomLift_map_of_comp_eq hF (u.map d) ex)
  have hFgy : q.IsStronglyCartesian (u.map d) (F.map gy) :=
    isStronglyCartesian_of_isHomLift (hFsc gy) (u.map d)
      (isHomLift_map_of_comp_eq hF (u.map d) gy)
  have hMl := hM.toIsHomLift
  have hone : χ ≫ u.map d = χ ≫ u.map d := rfl
  set κ := IsStronglyCartesian.map q (u.map d) (F.map ex) hone M with hκdef
  have hκfac : κ ≫ F.map ex = M := by
    rw [hκdef]
    exact IsStronglyCartesian.fac q (u.map d) (F.map ex) hone M
  have hκlift : q.IsHomLift χ κ := by
    rw [hκdef]
    exact IsStronglyCartesian.map_isHomLift q (u.map d) (F.map ex) hone M
  have hκcomp : q.IsStronglyCartesian (χ ≫ u.map d) (κ ≫ F.map ex) := by
    rw [hκfac]
    exact hM
  refine ⟨κ, IsStronglyCartesian.of_comp q (f := χ) (g := u.map d) (φ := κ) (ψ := F.map ex), ?_⟩
  -- the images of the two vertical morphisms lie over an identity
  have hvert : ∀ t : sx ⟶ sy, p.IsHomLift (𝟙 W) t → q.IsHomLift (𝟙 (u.obj W)) (F.map t) := by
    intro t ht
    have h1 : (p ⋙ u).IsHomLift (u.map (𝟙 W)) t := isHomLift_comp_functor u (𝟙 W) t ht
    have h2 := isHomLift_map_of_comp_eq hF (u.map (𝟙 W)) t
    rwa [Functor.map_id] at h2
  have hκt : ∀ t : sx ⟶ sy, p.IsHomLift (𝟙 W) t → q.IsHomLift χ (κ ≫ F.map t) := by
    intro t ht
    have := hvert t ht
    infer_instance
  have hd1 := hκt t₁ ht₁
  have hd2 := hκt t₂ ht₂
  refine IsStronglyCartesian.ext q (u.map d) (F.map gy) χ ?_
  have hchain : ∀ (t : sx ⟶ sy) (n : xA ⟶ yB), ex ≫ n = t ≫ gy →
      (κ ≫ F.map t) ≫ F.map gy = M ≫ F.map n := by
    intro t n hs
    rw [Category.assoc, ← F.map_comp, ← hs, F.map_comp, ← Category.assoc, hκfac]
  exact (hchain t₁ n₁ hs₁).trans (hyp.trans (hchain t₂ n₂ hs₂).symm)

/-- **Two morphisms of a fibre have the same base change along `c` as soon as one strongly
cartesian morphism over `c` into their common source equalizes them.** The chosen cartesian lift
of `c` factors through any strongly cartesian morphism over `c` with the same codomain, so it
equalizes them too, and the base change is pinned down by its composite with the chosen lift. -/
theorem pullbackFiberHom_eq_of_comp_eq {𝒳 : Type u₃} [Category.{v} 𝒳] {p : 𝒳 ⥤ 𝒞}
    [p.IsFibered] {U : 𝒞} {A Bo : p.Fiber U} (n₁ n₂ : A ⟶ Bo) {W : 𝒞} (c : W ⟶ U) {w : 𝒳}
    (Λ : w ⟶ A.1) (hΛ : p.IsStronglyCartesian c Λ)
    (hc : Λ ≫ Fiber.fiberInclusion.map n₁ = Λ ≫ Fiber.fiberInclusion.map n₂) :
    pullbackFiberHom n₁ c = pullbackFiberHom n₂ c := by
  have hpm : p.IsStronglyCartesian c (IsPreFibered.pullbackMap A.2 c) := by
    have := IsPreFibered.pullbackMap.IsCartesian A.2 c
    infer_instance
  obtain ⟨ι, -, -, hfac⟩ := exists_isIso_comp_eq_of_isStronglyCartesian hΛ hpm
  refine (pullbackFiberHom_uniq n₁ c (pullbackFiberHom n₂ c) ?_).symm
  refine (pullbackFiberHom_fac n₂ c).trans ?_
  refine Eq.trans (congrArg (fun t => t ≫ Fiber.fiberInclusion.map n₂) hfac.symm) ?_
  refine Eq.trans (Category.assoc ι Λ (Fiber.fiberInclusion.map n₂)) ?_
  refine Eq.trans (congrArg (fun t => ι ≫ t) hc.symm) ?_
  exact (Category.assoc ι Λ (Fiber.fiberInclusion.map n₁)).symm.trans
    (congrArg (fun t => t ≫ Fiber.fiberInclusion.map n₁) hfac)

end CategoryTheory.Functor

namespace CategoryTheory.Pseudofunctor.CoGrothendieck

section Attachment

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮]
  {F : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat.{v₂, u₂}}
  {𝒯 : Type u₄} [Category.{v₃} 𝒯] {r : 𝒯 ⥤ 𝒮} {N : CoGrothendieck F ⥤ 𝒯}

/-- **Every morphism over `g` out of the image of an object of a fibre is, after a comparison
isomorphism over an identity, the image of a morphism in normal form.** The morphism factors
through the image of the chosen cartesian lift of `g`, and the vertical factor is the image of a
vertical morphism because the 1-morphism is full on the fibre. -/
theorem exists_homOf_eq_of_isHomLift (hN : (forget F).IsFibredOneMorphism r N)
    (hfib : ∀ T : 𝒮, Nonempty (Functor.Fiber.inducedFunctor (ι_comp_comp_eq hN T)).Full)
    {V T : 𝒮} (g : V ⟶ T) {c : F.obj ⟨op V⟩} {b : F.obj ⟨op T⟩} {z : 𝒯}
    (ι₀ : z ⟶ N.obj ⟨V, c⟩) (hiso : IsIso ι₀) (hιlift : r.IsHomLift (𝟙 V) ι₀)
    (θ : z ⟶ N.obj ⟨T, b⟩) (hθ : r.IsHomLift g θ) :
    ∃ γ : c ⟶ (F.map g.op.toLoc).toFunctor.obj b, θ = ι₀ ≫ N.map (homOf g γ) := by
  have hcart : r.IsStronglyCartesian g (N.map (cartesianLift b g)) :=
    hN.map_isStronglyCartesian g _ (isStronglyCartesian_homCartesianLift b g)
  have hone : g = 𝟙 V ≫ g := by simp
  set v := Functor.IsStronglyCartesian.map r g (N.map (cartesianLift b g)) hone θ with hvdef
  have hvfac : v ≫ N.map (cartesianLift b g) = θ := by
    rw [hvdef]
    exact Functor.IsStronglyCartesian.fac r g _ hone θ
  have hvlift : r.IsHomLift (𝟙 V) v := by
    rw [hvdef]
    exact Functor.IsStronglyCartesian.map_isHomLift r g _ hone θ
  obtain ⟨hfull⟩ := hfib V
  obtain ⟨ε, hε⟩ := hfull.map_surjective (Functor.Fiber.homMk r V (inv ι₀ ≫ v))
  have hmap : N.map ((ι F V).map ε) = inv ι₀ ≫ v :=
    (congrArg Functor.Fiber.fiberInclusion.map hε).trans
      (Functor.Fiber.fiberInclusion_homMk r V (inv ι₀ ≫ v))
  have hvI : v = ι₀ ≫ N.map ((ι F V).map ε) :=
    ((congrArg (fun t => ι₀ ≫ t) hmap).trans ((Category.assoc ι₀ (inv ι₀) v).symm.trans
      ((congrArg (fun t => t ≫ v) (IsIso.hom_inv_id ι₀)).trans (Category.id_comp v)))).symm
  obtain ⟨γ, hγ⟩ := exists_homOf_of_base ((ι F V).map ε ≫ cartesianLift b g)
    (show ((ι F V).map ε ≫ cartesianLift b g).base = g from Category.id_comp g)
  refine ⟨γ, ?_⟩
  refine Eq.trans ?_ (congrArg (fun t => ι₀ ≫ N.map t) hγ)
  refine Eq.trans hvfac.symm ?_
  refine Eq.trans (congrArg (fun t => t ≫ N.map (cartesianLift b g)) hvI) ?_
  exact (Category.assoc _ _ _).trans
    (congrArg (fun t => ι₀ ≫ t) (N.map_comp _ _).symm)

/-- **A morphism in normal form is determined by the morphism of the target it induces.** -/
theorem homOf_eq_of_map_eq (hfaith : N.Faithful) {V T : 𝒮} (g : V ⟶ T) {c : F.obj ⟨op V⟩}
    {b : F.obj ⟨op T⟩} {z : 𝒯} (ι₀ : z ⟶ N.obj ⟨V, c⟩) (hiso : IsIso ι₀)
    (γ₁ γ₂ : c ⟶ (F.map g.op.toLoc).toFunctor.obj b)
    (h : ι₀ ≫ N.map (homOf g γ₁) = ι₀ ≫ N.map (homOf g γ₂)) : γ₁ = γ₂ :=
  homOf_inj g γ₁ γ₂ (hfaith.map_injective ((cancel_epi ι₀).1 h))

/-- **Restricting a morphism in normal form along a strongly cartesian morphism** keeps the normal
form, with the chosen cartesian lift of the restricting morphism prefixed. -/
theorem exists_restrict_homOf (hN : (forget F).IsFibredOneMorphism r N)
    {V' V T : 𝒮} (β : V' ⟶ V) (g : V ⟶ T) {c : F.obj ⟨op V⟩} {b : F.obj ⟨op T⟩} {z z' : 𝒯}
    (ι₀ : z ⟶ N.obj ⟨V, c⟩) (hiso : IsIso ι₀) (hιlift : r.IsHomLift (𝟙 V) ι₀)
    (ν : z' ⟶ z) (hν : r.IsStronglyCartesian β ν) :
    ∃ ι₁ : z' ⟶ N.obj ⟨V', (F.map β.op.toLoc).toFunctor.obj c⟩,
      IsIso ι₁ ∧ r.IsHomLift (𝟙 V') ι₁ ∧
      ∀ γ : c ⟶ (F.map g.op.toLoc).toFunctor.obj b,
        ν ≫ ι₀ ≫ N.map (homOf g γ) = ι₁ ≫ N.map (cartesianLift c β ≫ homOf g γ) := by
  have hνι : r.IsStronglyCartesian β (ν ≫ ι₀) :=
    Functor.isStronglyCartesian_comp_isoOverId hν ι₀ hιlift hiso
  have hcL : r.IsStronglyCartesian β (N.map (cartesianLift c β)) :=
    hN.map_isStronglyCartesian β _ (isStronglyCartesian_homCartesianLift c β)
  obtain ⟨ι₁, hι₁iso, hι₁lift, hι₁fac⟩ :=
    Functor.exists_isIso_comp_eq_of_isStronglyCartesian hcL hνι
  refine ⟨ι₁, hι₁iso, hι₁lift, fun γ => ?_⟩
  rw [N.map_comp, reassoc_of% hι₁fac]

end Attachment

end CategoryTheory.Pseudofunctor.CoGrothendieck

end
