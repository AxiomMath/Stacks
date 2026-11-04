module

public import Mathlib.RingTheory.FractionalIdeal.Basic

public import Mathlib.Basic.NNReal.Defs

public import Mathlib.CategoryTheory.Adjunction.Limits


import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Tactic.NormNum.Parity
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.Data.NNRat.Floor
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Sheaves.Init
public import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.CategoryTheory.ExtremalEpi
import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Slice
public import StacksFrontier.CategoryTheory.FiberedInSetoids.Defs
public import StacksFrontier.CategoryTheory.FibredOneMorphism
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Representability of a category fibred in groupoids

Stacks 02Y3: a category fibred in groupoids `p : 𝒮 ⥤ 𝒞` is *representable*, i.e. equivalent
over `𝒞` to a slice category `𝒞/X`, if and only if it is fibred in setoids (every fibre
`𝒮_U` is a thin groupoid, `CategoryTheory.Functor.IsFiberedInSetoids`) and its presheaf of
isomorphism classes `𝒮̄ : U ↦ Ob(𝒮_U)/≅` is representable (`IsoClassRepresentable`); and the
representing object is then unique up to isomorphism in `𝒞`. These are `representable_iff` and
`representing_object_unique`.

The forward direction transports both conditions along an equivalence over `𝒞`, since a slice
satisfies them. The converse builds the equivalence by hand: `toOver` sends `x : 𝒮` to the
object of `𝒞/X` named by the isomorphism class of `x`, `fromOver` picks a chosen
representative in the fibre, and the unit and counit are assembled from the strongly cartesian
lifts of identities that fibredness in setoids supplies.

`StacksRepresentableCFG.sliceHomOfIsoClass` is the descent of
`StacksRepresentableCFG.sliceHomOfFiber` to `IsoClass p U`, which is what lets an equation of
isomorphism classes be turned into an equation of morphisms of `𝒞` without unfolding the
representing equivalences; see its docstring.
-/

-- `Functor.isHomLift_map_of_comp_eq` is used inside the bodies of declarations in the
-- `@[expose] public section` below, so the `FibredOneMorphism` import must be `public` even
-- though the lemma appears in no statement: a plain `import` makes it available only privately.

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory

namespace StacksRepresentableCFG

universe v u v' u' w v''

variable {𝒮 : Type u} [Category.{v} 𝒮] {𝒞 : Type u'} [Category.{v'} 𝒞]

/-!
## Definitions
-/

/-- The set of isomorphism classes of objects of the fibre category `S_U`. Two objects
of the fibre `p.Fiber U` are identified when they are isomorphic *within the fibre*
(i.e. via a morphism lying over `id_U`). This is the value `\overline{S}(U)`.

The fibre `p.Fiber U` is a `Type u` (the universe of objects of `S`), hence so is this
quotient. When this set is compared, via `IsoClassRepresentableBy` below, to the hom-set
`(U ⟶ X) : Type v'` of `C`, the comparison imposes the natural small-presheaf universe
constraint `u = v'`. -/
@[implicit_reducible, sga "7 VI 1.1(d)" "Object set of [X]"]
def IsoClass (p : 𝒮 ⥤ 𝒞) (U : 𝒞) : Type u :=
  _root_.Quotient (isIsomorphicSetoid (p.Fiber U))

/-- The isomorphism class of an object of the fibre `p.Fiber U`. -/
@[implicit_reducible]
def IsoClass.mk (p : 𝒮 ⥤ 𝒞) {U : 𝒞} (x : p.Fiber U) : IsoClass p U :=
  Quotient.mk _ x

/-- `y` (an object of the fibre over `V`) is a *pullback* of `x` (an object of the fibre
over `U`) along `f : V ⟶ U` if there is a morphism `φ : y.1 ⟶ x.1` in `S` lying over `f`
(`p.IsHomLift f φ`) that is *strongly cartesian* (`p.IsStronglyCartesian f φ`). In a
category fibred in groupoids such a `φ` always exists and pins `y` down up to
isomorphism within the fibre over `V`; hence pullback is well defined on isomorphism
classes. -/
def IsPullbackOver (p : 𝒮 ⥤ 𝒞) {U V : 𝒞} (f : V ⟶ U)
    (x : p.Fiber U) (y : p.Fiber V) : Prop :=
  ∃ φ : y.1 ⟶ x.1, p.IsHomLift f φ ∧ p.IsStronglyCartesian f φ

/-- The presheaf of isomorphism classes `\overline{S}` of `p` is *representable by `X`*.
This packages a natural isomorphism of presheaves
`\overline{S} ≅ h_X = Mor_C(-, X)` pointwise:

* a family of bijections `equiv U : IsoClass p U ≃ (U ⟶ X)`, i.e. `\overline{S}(U) ≅ h_X(U)`
  for each `U`;
* naturality with respect to restriction: for `f : V ⟶ U` and a (strongly cartesian)
  pullback `y` of `x` along `f`, the restriction of the class of `x` (namely the class of
  `y`) corresponds under the bijections to precomposition with `f`, i.e.
  `equiv V [y] = f ≫ equiv U [x]`.

This is exactly the data of an isomorphism `\overline{S} ≅ h_X` of presheaves on `C`, and
since `h_X` is the representable presheaf attached to `X`, it expresses that `\overline{S}`
is representable. Stating it as a natural family of `Equiv`s with codomain
`(U ⟶ X)` keeps the universes honest (`IsoClass p U : Type u` is compared to
`(U ⟶ X) : Type v'`) and avoids choosing a model of the intermediate presheaf functor. -/
structure IsoClassRepresentableBy (p : 𝒮 ⥤ 𝒞) (X : 𝒞) where
  /-- Pointwise bijection `\overline{S}(U) ≅ h_X(U) = (U ⟶ X)`. -/
  equiv : ∀ U : 𝒞, IsoClass p U ≃ (U ⟶ X)
  /-- Naturality: restriction along `f` (pullback) corresponds to precomposition by `f`. -/
  naturality : ∀ {U V : 𝒞} (f : V ⟶ U) (x : p.Fiber U) (y : p.Fiber V),
    IsPullbackOver p f x y →
      equiv V (IsoClass.mk p y) = f ≫ equiv U (IsoClass.mk p x)

/-- The presheaf of isomorphism classes `\overline{S}` of `p` is *representable* if it is
representable by some object `X` of `C`. -/
def IsoClassRepresentable (p : 𝒮 ⥤ 𝒞) : Prop :=
  ∃ X : 𝒞, Nonempty (IsoClassRepresentableBy p X)


/-- A *1-morphism over `C`*: a functor `S ⥤ T` between categories over `C` commuting
strictly with the structure functors. -/
@[sga "4 VI 6.0"]
structure MorphismOver {𝒮 : Type u} [Category.{v} 𝒮] {𝒯 : Type w} [Category.{v''} 𝒯]
    (p : 𝒮 ⥤ 𝒞) (q : 𝒯 ⥤ 𝒞) where
  /-- The underlying functor. -/
  functor : 𝒮 ⥤ 𝒯
  /-- The functor commutes strictly with the structure functors. -/
  w : functor ⋙ q = p

/-- An *equivalence in the 2-category of categories over `C`*: forward and backward
1-morphisms over `C` (`hom`, `inv`), together with unit and counit 2-isomorphisms that
are *2-cells over `C`* (the `unit_over` and `counit_over` coherence conditions).

The two coherence equations say that whiskering the unit/counit 2-cell with the relevant
structure functor is the *identity* 2-cell. Concretely, `whiskerRight unitIso.hom p` is a
natural transformation
  `𝟭 S ⋙ p ⟶ (hom.functor ⋙ inv.functor) ⋙ p`,
and the strict commuting equations `inv.w`, `hom.w` together with associativity and
left-unitality give a (definitional) equality of its source and target functors; the
condition `unit_over` asserts that the whiskered unit equals the corresponding `eqToHom`,
i.e. it is the identity 2-cell over `C`. (Likewise for the counit.) This is exactly the
statement that the unit and counit are 2-isomorphisms in the 2-category of categories over
`C`. -/
structure EquivalenceOver {𝒮 : Type u} [Category.{v} 𝒮] {𝒯 : Type w} [Category.{v''} 𝒯]
    (p : 𝒮 ⥤ 𝒞) (q : 𝒯 ⥤ 𝒞) where
  /-- The forward 1-morphism over `C`. -/
  hom : MorphismOver (𝒞 := 𝒞) p q
  /-- The backward 1-morphism over `C`. -/
  inv : MorphismOver (𝒞 := 𝒞) q p
  /-- The unit 2-isomorphism. -/
  unitIso : 𝟭 𝒮 ≅ hom.functor ⋙ inv.functor
  /-- The counit 2-isomorphism. -/
  counitIso : inv.functor ⋙ hom.functor ≅ 𝟭 𝒯
  /-- The unit is a 2-cell *over `C`*: whiskering with `p` gives the identity 2-cell,
  i.e. it equals the canonical `eqToHom` between the (equal) whiskered functors. -/
  unit_over : Functor.whiskerRight unitIso.hom p =
    eqToHom (by rw [Functor.id_comp, Functor.assoc, inv.w, hom.w])
  /-- The counit is a 2-cell *over `C`*: whiskering with `q` gives the identity 2-cell,
  i.e. it equals the canonical `eqToHom` between the (equal) whiskered functors. -/
  counit_over : Functor.whiskerRight counitIso.hom q =
    eqToHom (by rw [Functor.assoc, hom.w, inv.w, Functor.id_comp])

/-- The underlying equivalence of categories of an equivalence over `𝒞`, forgetting that the
1-morphisms and 2-cells are over `𝒞`. -/
def EquivalenceOver.toEquivalence {𝒯 : Type w} [Category.{v''} 𝒯]
    {p : 𝒮 ⥤ 𝒞} {q : 𝒯 ⥤ 𝒞} (e : EquivalenceOver (𝒞 := 𝒞) p q) : 𝒮 ≌ 𝒯 :=
  CategoryTheory.Equivalence.mk e.hom.functor e.inv.functor e.unitIso e.counitIso

/-- A composite of 1-morphisms over `𝒞` preserves the object of `𝒞` lying under each object. -/
private lemma obj_comp_eq {𝒯 ℛ : Type*} [Category 𝒯] [Category ℛ] {p : 𝒮 ⥤ 𝒞} {q : 𝒯 ⥤ 𝒞}
    {r : ℛ ⥤ 𝒞} (F : MorphismOver (𝒞 := 𝒞) p q) (G : MorphismOver (𝒞 := 𝒞) q r) (a : 𝒮) :
    r.obj (G.functor.obj (F.functor.obj a)) = p.obj a :=
  (Functor.congr_obj G.w _).trans (Functor.congr_obj F.w a)

/-- Each component of the unit of an equivalence over `𝒞` lies over an identity of `𝒞`. -/
lemma EquivalenceOver.isHomLift_unitIso_hom_app {𝒯 : Type w} [Category.{v''} 𝒯]
    {p : 𝒮 ⥤ 𝒞} {q : 𝒯 ⥤ 𝒞} (e : EquivalenceOver (𝒞 := 𝒞) p q) (a : 𝒮) :
    p.IsHomLift (𝟙 (p.obj a)) (e.unitIso.hom.app a) := by
  have happ := congrArg (fun (n : _) => n.app a) e.unit_over
  simp only [Functor.whiskerRight_app, eqToHom_app] at happ
  apply IsHomLift.of_fac' p (𝟙 (p.obj a)) (e.unitIso.hom.app a) rfl (obj_comp_eq e.hom e.inv a)
  rw [happ]
  simp

/-- Each component of the inverse unit of an equivalence over `𝒞` lies over an identity
of `𝒞`. -/
lemma EquivalenceOver.isHomLift_unitIso_inv_app {𝒯 : Type w} [Category.{v''} 𝒯]
    {p : 𝒮 ⥤ 𝒞} {q : 𝒯 ⥤ 𝒞} (e : EquivalenceOver (𝒞 := 𝒞) p q) (a : 𝒮) :
    p.IsHomLift (𝟙 (p.obj a)) (e.unitIso.inv.app a) := by
  have := e.isHomLift_unitIso_hom_app a
  rw [show e.unitIso.inv.app a = CategoryTheory.inv (e.unitIso.hom.app a) by simp]
  exact IsHomLift.lift_id_inv_isIso p (p.obj a) (e.unitIso.hom.app a)

/-- Each component of the counit of an equivalence over `𝒞` lies over an identity of `𝒞`. -/
lemma EquivalenceOver.isHomLift_counitIso_hom_app {𝒯 : Type w} [Category.{v''} 𝒯]
    {p : 𝒮 ⥤ 𝒞} {q : 𝒯 ⥤ 𝒞} (e : EquivalenceOver (𝒞 := 𝒞) p q) (t : 𝒯) :
    q.IsHomLift (𝟙 (q.obj t)) (e.counitIso.hom.app t) := by
  have happ := congrArg (fun (n : _) => n.app t) e.counit_over
  simp only [Functor.whiskerRight_app, eqToHom_app] at happ
  apply IsHomLift.of_fac' q (𝟙 (q.obj t)) (e.counitIso.hom.app t) (obj_comp_eq e.inv e.hom t) rfl
  rw [happ]
  simp

/-- `p : S ⥤ C` is *representable by `X`* if there is an equivalence over `C` between `S`
and the slice `C/X = Over X` (with its structure functor `Over.forget X`). -/
def RepresentableBy (p : 𝒮 ⥤ 𝒞) (X : 𝒞) : Type _ :=
  EquivalenceOver (𝒞 := 𝒞) p (Over.forget X)

/-- `p : S ⥤ C` is *representable* if it is representable by some object `X` of `C`. -/
def IsRepresentable (p : 𝒮 ⥤ 𝒞) : Prop :=
  ∃ X : 𝒞, Nonempty (RepresentableBy p X)


/-!
## Helper lemmas for the characterization

The biconditional `representable_iff` is proved by assembling four helper lemmas.

* `over_isFiberedInSetoids` and `isFiberedInSetoids_of_equivalenceOver` handle the
  fibred-in-setoids half of the forward direction.
* `isoClassRepresentableBy_of_equivalenceOver` handles the representable-presheaf half of
  the forward direction.
* `representableBy_of_setoid_and_isoClassRepr` is the converse (the crux, Stacks 04SD +
  category-of-elements ≅ `Over X`).
-/

/-- The slice `Over X` with structure functor `Over.forget X` is fibred in setoids:
it is fibred in groupoids (indeed in sets), and each fibre `(Over.forget X).Fiber U` is
thin. A morphism over `𝟙 U` between two objects `a, b : U ⟶ X` of the fibre is determined
by its underlying `𝒞`-morphism, which is forced to be `𝟙 U`, so there is at most one such
morphism. -/
lemma over_isFiberedInSetoids (X : 𝒞) :
    (Over.forget X).IsFiberedInSetoids := by
  have hfib : (Over.forget X).IsFiberedInGroupoids := by
    constructor
    · intro V W f x1 hx
      exact ⟨Over.mk (f ≫ eqToHom hx.symm ≫ x1.hom),
        Over.homMk (f ≫ eqToHom hx.symm) (by simp),
        IsHomLift.of_fac' (Over.forget X) f _ rfl hx (by simp)⟩
    · intro x1 y z φ ψ h hcomp
      simp only [Over.forget_map] at hcomp
      have hw : h ≫ y.hom = z.hom := by
        rw [← Over.w φ, ← Category.assoc, hcomp, Over.w ψ]
      exact ⟨Over.homMk h hw, ⟨rfl, Over.OverMorphism.ext (by simpa using hcomp)⟩,
        fun _ ⟨h₁, _⟩ ↦ Over.OverMorphism.ext (by simpa using h₁)⟩
  refine ⟨hfib, fun U _ _ => ⟨fun φ ψ => ?_⟩⟩
  apply Functor.Fiber.hom_ext
  apply Over.OverMorphism.ext
  have e₁ := IsHomLift.fac' (Over.forget X) (𝟙 U) (Functor.Fiber.fiberInclusion.map φ)
  have e₂ := IsHomLift.fac' (Over.forget X) (𝟙 U) (Functor.Fiber.fiberInclusion.map ψ)
  simp only [Over.forget_map] at e₁ e₂
  rw [e₁, e₂]

/-- Existence of lifts (the first axiom of a category fibred in groupoids) transports backwards
along an equivalence over `𝒞`: a lift of `f` into `e.hom.functor.obj x` supplied by `q` is
carried back by `e.inv.functor` and corrected by the unit. -/
lemma exists_lift_of_equivalenceOver {𝒯 : Type w} [Category.{v''} 𝒯]
    {p : 𝒮 ⥤ 𝒞} {q : 𝒯 ⥤ 𝒞} (e : EquivalenceOver (𝒞 := 𝒞) p q)
    (hq : q.IsFiberedInGroupoids) {V W : 𝒞} (f : V ⟶ W) (x : 𝒮) (hx : p.obj x = W) :
    ∃ (y : 𝒮) (φ : y ⟶ x), p.IsHomLift f φ := by
  obtain ⟨t, ψ, hqψ⟩ :=
    hq.exists_lift f (e.hom.functor.obj x) ((Functor.congr_obj e.hom.w x).trans hx)
  have hyV : p.obj (e.inv.functor.obj t) = V :=
    (Functor.congr_obj e.inv.w t).trans (IsHomLift.domain_eq q f ψ)
  have hpGψ : p.IsHomLift f (e.inv.functor.map ψ) := Functor.isHomLift_map_of_comp_eq e.inv.w f ψ
  have hu := e.isHomLift_unitIso_inv_app x
  refine ⟨e.inv.functor.obj t, e.inv.functor.map ψ ≫ e.unitIso.inv.app x,
    IsHomLift.of_fac' p f (e.inv.functor.map ψ ≫ e.unitIso.inv.app x) hyV hx ?_⟩
  rw [Functor.map_comp, IsHomLift.fac' p f (e.inv.functor.map ψ),
      IsHomLift.fac' p (𝟙 (p.obj x)) (e.unitIso.inv.app x)]
  simp

/-- Existence and uniqueness of fill-ins (the second axiom of a category fibred in groupoids)
transports backwards along an equivalence over `𝒞`: the fill-in is obtained downstairs for `q`
and pulled back through the fully faithful `e.hom.functor`. -/
lemma unique_lift_of_equivalenceOver {𝒯 : Type w} [Category.{v''} 𝒯]
    {p : 𝒮 ⥤ 𝒞} {q : 𝒯 ⥤ 𝒞} (e : EquivalenceOver (𝒞 := 𝒞) p q)
    (hq : q.IsFiberedInGroupoids) {x y z : 𝒮} (φ : y ⟶ x) (ψ : z ⟶ x)
    (h : p.obj z ⟶ p.obj y) (hh : h ≫ p.map φ = p.map ψ) :
    ∃! χ : z ⟶ y, p.map χ = h ∧ χ ≫ φ = ψ := by
  have ff : e.hom.functor.FullyFaithful := e.toEquivalence.fullyFaithfulFunctor
  have ez : q.obj (e.hom.functor.obj z) = p.obj z := Functor.congr_obj e.hom.w z
  have ey : q.obj (e.hom.functor.obj y) = p.obj y := Functor.congr_obj e.hom.w y
  have ex : q.obj (e.hom.functor.obj x) = p.obj x := Functor.congr_obj e.hom.w x
  set h' : q.obj (e.hom.functor.obj z) ⟶ q.obj (e.hom.functor.obj y) :=
    eqToHom ez ≫ h ≫ eqToHom ey.symm with hh'def
  have cφ : q.map (e.hom.functor.map φ) = eqToHom ey ≫ p.map φ ≫ eqToHom ex.symm :=
    Functor.congr_hom e.hom.w φ
  have cψ : q.map (e.hom.functor.map ψ) = eqToHom ez ≫ p.map ψ ≫ eqToHom ex.symm :=
    Functor.congr_hom e.hom.w ψ
  have transp : ∀ χ : z ⟶ y, q.map (e.hom.functor.map χ) = h' ↔ p.map χ = h := fun χ => by
    have hc : q.map (e.hom.functor.map χ) = eqToHom ez ≫ p.map χ ≫ eqToHom ey.symm :=
      Functor.congr_hom e.hom.w χ
    rw [hc, hh'def]
    exact ⟨fun hk => (cancel_mono (eqToHom ey.symm)).mp ((cancel_epi (eqToHom ez)).mp hk),
      fun hk => by rw [hk]⟩
  have transc : ∀ χ : z ⟶ y,
      e.hom.functor.map χ ≫ e.hom.functor.map φ = e.hom.functor.map ψ ↔ χ ≫ φ = ψ := fun χ => by
    rw [← Functor.map_comp]
    exact ⟨ff.map_injective, fun hk => by rw [hk]⟩
  have hh' : h' ≫ q.map (e.hom.functor.map φ) = q.map (e.hom.functor.map ψ) := by
    rw [hh'def, cφ, cψ]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [← Category.assoc h (p.map φ), hh]
  obtain ⟨g₀, ⟨hg₀a, hg₀b⟩, hg₀uniq⟩ :=
    hq.unique_lift (e.hom.functor.map φ) (e.hom.functor.map ψ) h' hh'
  have hpre : e.hom.functor.map (ff.preimage g₀) = g₀ := ff.map_preimage g₀
  refine ⟨ff.preimage g₀, ⟨(transp _).mp (by rw [hpre, hg₀a]),
    (transc _).mp (by rwa [hpre])⟩, fun χ ⟨hχ1, hχ2⟩ =>
    ff.map_injective ((hg₀uniq _ ⟨(transp χ).mpr hχ1, (transc χ).mpr hχ2⟩).trans hpre.symm)⟩

/-- Being fibred in groupoids transports backwards along an equivalence over `𝒞`. -/
lemma isFiberedInGroupoids_of_equivalenceOver {𝒯 : Type w} [Category.{v''} 𝒯]
    {p : 𝒮 ⥤ 𝒞} {q : 𝒯 ⥤ 𝒞} (e : EquivalenceOver (𝒞 := 𝒞) p q)
    (hq : q.IsFiberedInGroupoids) : p.IsFiberedInGroupoids where
  exists_lift f x hx := exists_lift_of_equivalenceOver e hq f x hx
  unique_lift φ ψ h hh := unique_lift_of_equivalenceOver e hq φ ψ h hh

/-- In a fibred-in-setoids category, two morphisms lying over the same `𝟙 U` are equal
(fibre thinness). -/
private lemma eq_of_isHomLift_id {p : 𝒮 ⥤ 𝒞} (hset : p.IsFiberedInSetoids) (U : 𝒞) {a b : 𝒮}
    (φ ψ : a ⟶ b) [p.IsHomLift (𝟙 U) φ] [p.IsHomLift (𝟙 U) ψ] : φ = ψ :=
  have := hset.fiber_isThin U
  congrArg Functor.Fiber.fiberInclusion.map
    (Subsingleton.elim (Functor.Fiber.homMk p U φ) (Functor.Fiber.homMk p U ψ))

/-- `CategoryTheory.Functor.IsFiberedInSetoids` transports backwards along an equivalence
over `𝒞`: if `e : EquivalenceOver p q` and `q` is fibred in setoids, then so is `p`. The
equivalence `e` restricts to fibre equivalences `p.Fiber U ≌ q.Fiber U` (the 1-morphisms are
over `𝒞` and the unit/counit 2-cells live over `𝟙`), and thinness is invariant under
equivalence of categories. -/
lemma isFiberedInSetoids_of_equivalenceOver {𝒯 : Type w} [Category.{v''} 𝒯]
    {p : 𝒮 ⥤ 𝒞} {q : 𝒯 ⥤ 𝒞}
    (e : EquivalenceOver (𝒞 := 𝒞) p q) (hq : q.IsFiberedInSetoids) :
    p.IsFiberedInSetoids := by
  have hfib := isFiberedInGroupoids_of_equivalenceOver e hq.isFiberedInGroupoids
  refine ⟨hfib, fun U _ _ => ⟨fun φ ψ => ?_⟩⟩
  apply Functor.Fiber.hom_ext
  apply e.toEquivalence.fullyFaithfulFunctor.map_injective
  have hqφ : q.IsHomLift (𝟙 U) (e.hom.functor.map (Functor.Fiber.fiberInclusion.map φ)) :=
    Functor.isHomLift_map_of_comp_eq e.hom.w (𝟙 U) (Functor.Fiber.fiberInclusion.map φ)
  have hqψ : q.IsHomLift (𝟙 U) (e.hom.functor.map (Functor.Fiber.fiberInclusion.map ψ)) :=
    Functor.isHomLift_map_of_comp_eq e.hom.w (𝟙 U) (Functor.Fiber.fiberInclusion.map ψ)
  exact eq_of_isHomLift_id hq U (e.hom.functor.map _) (e.hom.functor.map _)

/-- The fibre inclusion sends an object of the fibre to its underlying object. -/
private lemma fiberInclusion_obj_eq {p : 𝒮 ⥤ 𝒞} {U : 𝒞} (a : p.Fiber U) :
    Functor.Fiber.fiberInclusion.obj a = a.1 := rfl

/-- If `m : a.1 ⟶ b.1` is an isomorphism lying over `𝟙 U`, then `a` and `b` define the
same isomorphism class in `IsoClass p U`. -/
lemma isoClass_eq_of_homlift_iso {p : 𝒮 ⥤ 𝒞} {U : 𝒞} (a b : p.Fiber U)
    (m : a.1 ⟶ b.1) [p.IsHomLift (𝟙 U) m] [IsIso m] :
    IsoClass.mk p a = IsoClass.mk p b := by
  apply Quotient.sound
  have : p.IsHomLift (𝟙 U) (inv m) := IsHomLift.lift_id_inv_isIso p U m
  -- build a fibre isomorphism `a ≅ b`
  refine ⟨⟨Functor.Fiber.homMk p U m, Functor.Fiber.homMk p U (inv m), ?_, ?_⟩⟩
  · apply Functor.Fiber.hom_ext
    simp [fiberInclusion_obj_eq]
  · apply Functor.Fiber.hom_ext
    simp [fiberInclusion_obj_eq]

/-- The morphism `U ⟶ X` attached to an object of the fibre `p.Fiber U` by an equivalence over
`𝒞` between `p` and the slice `Over.forget X`: the structure morphism of its image, read as a
morphism out of `U`. -/
def sliceHomOfFiber {X : 𝒞} {p : 𝒮 ⥤ 𝒞}
    (e : EquivalenceOver (𝒞 := 𝒞) p (Over.forget X)) {U : 𝒞} (a : p.Fiber U) : U ⟶ X :=
  eqToHom ((Functor.congr_obj e.hom.w a.1).trans a.2).symm ≫ (e.hom.functor.obj a.1).hom

/-- The object of the fibre `p.Fiber U` attached to `g : U ⟶ X` by an equivalence over `𝒞`
between `p` and the slice `Over.forget X`: the image of `Over.mk g` under the backward
1-morphism. -/
def fiberOfSliceHom {X : 𝒞} {p : 𝒮 ⥤ 𝒞}
    (e : EquivalenceOver (𝒞 := 𝒞) p (Over.forget X)) {U : 𝒞} (g : U ⟶ X) : p.Fiber U :=
  ⟨e.inv.functor.obj (Over.mk g), Functor.congr_obj e.inv.w (Over.mk g)⟩

/-- Naturality of `sliceHomOfFiber`: if `φ : y.1 ⟶ x.1` lies over `f : V ⟶ U`, then the morphism
named by `y` is `f` followed by the morphism named by `x`. -/
private lemma sliceHomOfFiber_comp_aux {X : 𝒞} {p : 𝒮 ⥤ 𝒞}
    (e : EquivalenceOver (𝒞 := 𝒞) p (Over.forget X)) {U V : 𝒞} (f : V ⟶ U)
    (x : p.Fiber U) (y : p.Fiber V) (φ : y.1 ⟶ x.1) [p.IsHomLift f φ] :
    sliceHomOfFiber e y = f ≫ sliceHomOfFiber e x := by
  have hx : (Over.forget X).obj (e.hom.functor.obj x.1) = U :=
    (Functor.congr_obj e.hom.w x.1).trans x.2
  have hy : (Over.forget X).obj (e.hom.functor.obj y.1) = V :=
    (Functor.congr_obj e.hom.w y.1).trans y.2
  have hl : (Over.forget X).IsHomLift f (e.hom.functor.map φ) :=
    Functor.isHomLift_map_of_comp_eq e.hom.w f φ
  have hwφ := Over.w (e.hom.functor.map φ)
  have hfac := IsHomLift.fac' (Over.forget X) f (e.hom.functor.map φ)
  simp only [Over.forget_map] at hfac
  simp only [sliceHomOfFiber]
  rw [← hwφ, hfac]
  simp

/-- `sliceHomOfFiber` depends only on the isomorphism class of its argument in the fibre, so it
descends to `IsoClass p U`. -/
lemma sliceHomOfFiber_eq_of_iso {X : 𝒞} {p : 𝒮 ⥤ 𝒞}
    (e : EquivalenceOver (𝒞 := 𝒞) p (Over.forget X)) {U : 𝒞} {a a' : p.Fiber U} (ι : a ≅ a') :
    sliceHomOfFiber e a = sliceHomOfFiber e a' := by
  simpa using sliceHomOfFiber_comp_aux e (𝟙 U) a' a (Functor.Fiber.fiberInclusion.map ι.hom)

/-- **`sliceHomOfFiber` as a function on isomorphism classes.** The descent of
`StacksRepresentableCFG.sliceHomOfFiber` promised by
`StacksRepresentableCFG.sliceHomOfFiber_eq_of_iso`: a morphism `U ⟶ X` attached to an
isomorphism class in the fibre `p.Fiber U`, well defined because `sliceHomOfFiber` is constant
on isomorphism classes.

This is the form in which the descent is *usable*. The `_eq_of_iso` form above requires an
isomorphism of fibre objects in hand, so a consumer holding an equation of isomorphism
*classes* — which is what `CategoryTheory.Functor.morphismSpaceEquiv_map` and the other
Stacks 04SW statements produce — has to extract one with
`CategoryTheory.Functor.exists_iso_of_isoClassMk_eq` and is then left comparing the two fibre
objects the extraction produced. Those are large terms whose equality holds only after the
representing equivalences inside them are unfolded, and unfolding them is expensive enough to
exhaust the kernel's budget. Applying this function to the equation with `congrArg` instead
keeps both sides spelled with the equivalences folded, so the comparison stays cheap and each
reduction can be named as its own small lemma.

`CategoryTheory.Functor.isoClassMk` is the same `Quotient.mk` as `IsoClass.mk`, but the module
defining it is not imported here, so the bridge between the two spellings is stated by the
consumer that needs it. -/
def sliceHomOfIsoClass {X : 𝒞} {p : 𝒮 ⥤ 𝒞}
    (e : EquivalenceOver (𝒞 := 𝒞) p (Over.forget X)) {U : 𝒞} (c : IsoClass p U) : U ⟶ X :=
  Quotient.liftOn c (sliceHomOfFiber e) (by
    rintro a a' ⟨ι⟩
    exact sliceHomOfFiber_eq_of_iso e ι)

/-- `StacksRepresentableCFG.sliceHomOfIsoClass` on the class of `x` is
`StacksRepresentableCFG.sliceHomOfFiber` at `x`. -/
@[simp]
lemma sliceHomOfIsoClass_mk {X : 𝒞} {p : 𝒮 ⥤ 𝒞}
    (e : EquivalenceOver (𝒞 := 𝒞) p (Over.forget X)) {U : 𝒞} (x : p.Fiber U) :
    sliceHomOfIsoClass e (IsoClass.mk p x) = sliceHomOfFiber e x :=
  rfl

/-- `sliceHomOfFiber` and `fiberOfSliceHom` are mutually inverse on isomorphism classes: the
class of `fiberOfSliceHom e (sliceHomOfFiber e a)` is the class of `a`. -/
lemma isoClass_fiberOfSliceHom_sliceHomOfFiber {X : 𝒞} {p : 𝒮 ⥤ 𝒞}
    (e : EquivalenceOver (𝒞 := 𝒞) p (Over.forget X)) {U : 𝒞} (a : p.Fiber U) :
    IsoClass.mk p (fiberOfSliceHom e (sliceHomOfFiber e a)) = IsoClass.mk p a := by
  have ha : (Over.forget X).obj (e.hom.functor.obj a.1) = U :=
    (Functor.congr_obj e.hom.w a.1).trans a.2
  set t : Over X := e.hom.functor.obj a.1 with ht
  set g₀ : U ⟶ X := sliceHomOfFiber e a with hg₀set
  have hg₀ : g₀ = eqToHom ha.symm ≫ t.hom := rfl
  -- `Over.mk g₀ ≅ t` in `Over X`, over `𝟙 U`
  set j : Over.mk g₀ ⟶ t := Over.homMk (eqToHom ha.symm) (by simp [Over.mk_hom, hg₀]) with hj
  have hjiso : IsIso j := by
    refine ⟨Over.homMk (eqToHom ha) (by simp [hg₀]), ?_, ?_⟩ <;>
      exact Over.OverMorphism.ext (by simp [hj])
  have hjl : (Over.forget X).IsHomLift (𝟙 U) j := by
    apply IsHomLift.of_fac' (Over.forget X) (𝟙 U) j rfl ha
    simp [hj]
  -- transport along `e.inv.functor`, then correct by the unit at `a.1`
  have hivl : p.IsHomLift (𝟙 U) (e.inv.functor.map j) :=
    Functor.isHomLift_map_of_comp_eq e.inv.w (𝟙 U) j
  have : IsIso (e.inv.functor.map j) := Functor.map_isIso e.inv.functor j
  have hul : p.IsHomLift (𝟙 U) (e.unitIso.hom.app a.1) := by
    have := e.isHomLift_unitIso_hom_app a.1
    rwa [a.2] at this
  have hinvl : p.IsHomLift (𝟙 U) (CategoryTheory.inv (e.unitIso.hom.app a.1)) :=
    IsHomLift.lift_id_inv_isIso p U (e.unitIso.hom.app a.1)
  set m : e.inv.functor.obj (Over.mk g₀) ⟶ a.1 :=
    e.inv.functor.map j ≫ CategoryTheory.inv (e.unitIso.hom.app a.1) with hmdef
  have hml : p.IsHomLift (𝟙 U) m := IsHomLift.comp_of_lift_id p U _ _
  have : IsIso m := by
    rw [hmdef]
    infer_instance
  exact isoClass_eq_of_homlift_iso (fiberOfSliceHom e g₀) a m

/-- `sliceHomOfFiber` recovers `g` from the fibre object `fiberOfSliceHom e g` it names, via
the counit of the equivalence. -/
lemma sliceHomOfFiber_fiberOfSliceHom {X : 𝒞} {p : 𝒮 ⥤ 𝒞}
    (e : EquivalenceOver (𝒞 := 𝒞) p (Over.forget X)) {U : 𝒞} (g : U ⟶ X) :
    sliceHomOfFiber e (fiberOfSliceHom e g) = g := by
  have hsl : (Over.forget X).obj (e.hom.functor.obj (e.inv.functor.obj (Over.mk g))) = U :=
    obj_comp_eq e.inv e.hom (Over.mk g)
  have hl := e.isHomLift_counitIso_hom_app (Over.mk g)
  have hw : (e.counitIso.hom.app (Over.mk g)).left ≫ g =
      (e.hom.functor.obj (e.inv.functor.obj (Over.mk g))).hom :=
    Over.w (e.counitIso.hom.app (Over.mk g))
  have hfac := IsHomLift.fac' (Over.forget X) (𝟙 ((Over.forget X).obj (Over.mk g)))
    (e.counitIso.hom.app (Over.mk g))
  simp only [Over.forget_map] at hfac
  have hcml : (e.counitIso.hom.app (Over.mk g)).left = eqToHom hsl := by rw [hfac]; simp
  simp only [sliceHomOfFiber, fiberOfSliceHom]
  rw [← hw, hcml]
  simp

/-- Naturality of `sliceHomOfFiber`: if `φ : y.1 ⟶ x.1` lies over `f : V ⟶ U`, then the morphism
named by `y` is `f` followed by the morphism named by `x`. -/
lemma sliceHomOfFiber_comp {X : 𝒞} {p : 𝒮 ⥤ 𝒞}
    (e : EquivalenceOver (𝒞 := 𝒞) p (Over.forget X)) {U V : 𝒞} (f : V ⟶ U)
    (x : p.Fiber U) (y : p.Fiber V) (φ : y.1 ⟶ x.1) [p.IsHomLift f φ] :
    sliceHomOfFiber e y = f ≫ sliceHomOfFiber e x :=
  sliceHomOfFiber_comp_aux e f x y φ

/-- The pointwise bijection `IsoClass p U ≃ (U ⟶ X)` induced by an equivalence over `𝒞` between
`p` and the slice `Over.forget X`, i.e. `\overline{S}(U) ≅ h_X(U)`. -/
def isoClassEquivOfEquivalenceOver {X : 𝒞} {p : 𝒮 ⥤ 𝒞}
    (e : EquivalenceOver (𝒞 := 𝒞) p (Over.forget X)) (U : 𝒞) : IsoClass p U ≃ (U ⟶ X) where
  toFun c := sliceHomOfIsoClass e c
  invFun g := IsoClass.mk p (fiberOfSliceHom e g)
  left_inv c := Quotient.inductionOn c (isoClass_fiberOfSliceHom_sliceHomOfFiber e)
  right_inv := sliceHomOfFiber_fiberOfSliceHom e

/-- If `p` is equivalent over `𝒞` to the slice `Over.forget X`, then the presheaf of
isomorphism classes of `p` is representable by `X`. The fibre `(Over X)_U` is thin, so
`IsoClass (Over.forget X) U ≃ (U ⟶ X)` naturally in pullback (= precomposition); the
equivalence `e` gives `IsoClass p U ≃ IsoClass (Over.forget X) U` compatibly with pullback.
Composing yields the required natural family of bijections. -/
def isoClassRepresentableBy_of_equivalenceOver {X : 𝒞}
    {p : 𝒮 ⥤ 𝒞} (e : EquivalenceOver (𝒞 := 𝒞) p (Over.forget X)) :
    IsoClassRepresentableBy p X where
  equiv := isoClassEquivOfEquivalenceOver e
  naturality f x y hpb := by
    obtain ⟨φ, hφ, -⟩ := hpb
    have := hφ
    exact sliceHomOfFiber_comp e f x y φ

/-- **Converse.** If `p` is fibred in setoids and its presheaf of isomorphism classes is
representable by `X`, then `p` is representable by `X` (there is an equivalence over `𝒞`
between `𝒮` and `Over X`). This is the analytic kernel: Stacks 04SD identifies a
fibred-in-setoids `p` (up to equivalence over `𝒞`) with the category fibred in sets whose
fibre over `U` is `IsoClass p U`; `hrep.equiv` identifies that presheaf with `h_X`; and the
category of elements of `h_X` is equivalent over `𝒞` to `Over X`.

The forward functor `𝒮 ⥤ Over X` sends `a` to `Over.mk (hrep.equiv (p.obj a) [⟨a, rfl⟩])`
and `g` to `Over.homMk (p.map g)`; the triangle commutes by `hrep.naturality`. -/
def toOver {X : 𝒞} {p : 𝒮 ⥤ 𝒞}
    (hset : p.IsFiberedInSetoids) (hrep : IsoClassRepresentableBy p X) :
    𝒮 ⥤ Over X where
  obj a := Over.mk (hrep.equiv (p.obj a) (IsoClass.mk p ⟨a, rfl⟩))
  map {a b} g := Over.homMk (p.map g) (by
    have hpb : IsPullbackOver p (p.map g) ⟨b, rfl⟩ ⟨a, rfl⟩ :=
      ⟨g, IsHomLift.map (p := p) g,
        hset.isFiberedInGroupoids.isStronglyCartesian_homLift (p.map g) g⟩
    have hn := hrep.naturality (p.map g) ⟨b, rfl⟩ ⟨a, rfl⟩ hpb
    simp only [Over.mk_left, Over.mk_hom]
    rw [hn])
  map_id a := by
    apply Over.OverMorphism.ext
    simp
  map_comp {a b c} f g := by
    apply Over.OverMorphism.ext
    simp

/-- `toOver` is a 1-morphism over `𝒞`: it commutes strictly with the structure functors. -/
lemma toOver_comp_forget {X : 𝒞} {p : 𝒮 ⥤ 𝒞}
    (hset : p.IsFiberedInSetoids) (hrep : IsoClassRepresentableBy p X) :
    toOver hset hrep ⋙ Over.forget X = p :=
  rfl

/-- In a fibred-in-setoids category, an endomorphism lying over `𝟙 (p.obj a)` is the
identity (fibre thinness). -/
lemma endo_id {p : 𝒮 ⥤ 𝒞} (hset : p.IsFiberedInSetoids) {a : 𝒮}
    (ρ : a ⟶ a) [p.IsHomLift (𝟙 (p.obj a)) ρ] : ρ = 𝟙 a := by
  exact eq_of_isHomLift_id hset (p.obj a) ρ (𝟙 a)

/-- A fibred-in-setoids `p` is faithful: two morphisms with equal image are equal. -/
@[sga "4 I 6.5" "(ii)⇒(i)", sga "4 I 6.5.2" "(ii), special case"]
lemma pfaithful {p : 𝒮 ⥤ 𝒞} (hset : p.IsFiberedInSetoids)
    {a b : 𝒮} (χ χ' : a ⟶ b) (h : p.map χ = p.map χ') : χ = χ' := by
  obtain ⟨ρ, ⟨hρ1, hρ2⟩, huniq⟩ :=
    hset.isFiberedInGroupoids.unique_lift χ χ' (𝟙 (p.obj a)) (by rw [Category.id_comp, h])
  have : p.IsHomLift (𝟙 (p.obj a)) ρ :=
    IsHomLift.of_fac' p (𝟙 (p.obj a)) ρ rfl rfl (by rw [hρ1]; simp)
  obtain rfl : ρ = 𝟙 a := endo_id hset ρ
  simpa using hρ2

/-- Faithfulness phrased for two hom-lifts over the same base morphism. -/
@[sga "4 I 6.5.2" "(ii), special case"]
lemma pfaithful_lift {p : 𝒮 ⥤ 𝒞} (hset : p.IsFiberedInSetoids)
    {R S : 𝒞} {a b : 𝒮} (f : R ⟶ S) (χ χ' : a ⟶ b)
    [p.IsHomLift f χ] [p.IsHomLift f χ'] : χ = χ' := by
  apply pfaithful hset
  rw [IsHomLift.fac' p f χ, IsHomLift.fac' p f χ']

/-- Lift along a base-relation: given fibre objects `xs : p.Fiber V`, `xt : p.Fiber U`
and `f : V ⟶ U` with `equiv V [xs] = f ≫ equiv U [xt]`, there is a morphism
`χ : xs.1 ⟶ xt.1` lying over `f`. -/
lemma exists_map {p : 𝒮 ⥤ 𝒞} {X : 𝒞} (hset : p.IsFiberedInGroupoids)
    (hrep : IsoClassRepresentableBy p X) {U V : 𝒞} (f : V ⟶ U)
    (xt : p.Fiber U) (xs : p.Fiber V)
    (heq : hrep.equiv V (IsoClass.mk p xs) = f ≫ hrep.equiv U (IsoClass.mk p xt)) :
    ∃ χ : xs.1 ⟶ xt.1, p.IsHomLift f χ := by
  obtain ⟨y, φ, hlift⟩ := hset.exists_lift f xt.1 xt.2
  have hy : p.obj y = V := IsHomLift.domain_eq p f φ
  have hcl : IsoClass.mk p xs = IsoClass.mk p (⟨y, hy⟩ : p.Fiber V) :=
    (hrep.equiv V).injective (by
      rw [heq, hrep.naturality f xt ⟨y, hy⟩ ⟨φ, hlift, hset.isStronglyCartesian_homLift f φ⟩])
  obtain ⟨ι⟩ := (Quotient.exact hcl : Nonempty (xs ≅ (⟨y, hy⟩ : p.Fiber V)))
  let g : xs.1 ⟶ y := (Functor.Fiber.fiberInclusion (S := V)).map ι.hom
  exact ⟨g ≫ φ, IsHomLift.comp_lift_id_left' p V g f φ⟩

/-- The chosen representative of the iso-class associated to `t : Over X`. -/
noncomputable def repr (p : 𝒮 ⥤ 𝒞) {X : 𝒞} (hrep : IsoClassRepresentableBy p X)
    (t : Over X) : p.Fiber t.left := ((hrep.equiv t.left).symm t.hom).out

/-- The class of the chosen representative is sent by `equiv` to `t.hom`. -/
lemma repr_equiv (p : 𝒮 ⥤ 𝒞) {X : 𝒞} (hrep : IsoClassRepresentableBy p X) (t : Over X) :
    hrep.equiv t.left (IsoClass.mk p (repr p hrep t)) = t.hom := by
  unfold repr IsoClass.mk
  rw [Quotient.out_eq]
  exact Equiv.apply_symm_apply _ _

/-- Existence of the lift realizing a morphism `m : t ⟶ s` in `Over X` between the chosen
representatives, lying over the base `m.left`. -/
lemma bwdMap_exists {X : 𝒞} {p : 𝒮 ⥤ 𝒞}
    (hset : p.IsFiberedInSetoids) (hrep : IsoClassRepresentableBy p X)
    {t s : Over X} (m : t ⟶ s) :
    ∃ χ : (repr p hrep t).1 ⟶ (repr p hrep s).1, p.IsHomLift m.left χ :=
  exists_map hset.isFiberedInGroupoids hrep m.left (repr p hrep s) (repr p hrep t)
    (by rw [repr_equiv, repr_equiv]; exact (Over.w m).symm)

/-- The chosen lift of a morphism `m : t ⟶ s` in `Over X`. -/
noncomputable def bwdMap {X : 𝒞} {p : 𝒮 ⥤ 𝒞}
    (hset : p.IsFiberedInSetoids) (hrep : IsoClassRepresentableBy p X)
    {t s : Over X} (m : t ⟶ s) : (repr p hrep t).1 ⟶ (repr p hrep s).1 :=
  (bwdMap_exists hset hrep m).choose

/-- `bwdMap m` lies over `m.left`. -/
lemma bwdMap_homlift {X : 𝒞} {p : 𝒮 ⥤ 𝒞}
    (hset : p.IsFiberedInSetoids) (hrep : IsoClassRepresentableBy p X)
    {t s : Over X} (m : t ⟶ s) : p.IsHomLift m.left (bwdMap hset hrep m) :=
  (bwdMap_exists hset hrep m).choose_spec

/-- The backward functor `Over X ⥤ 𝒮`, sending `t` to the chosen representative `repr t` of
the isomorphism class `(hrep.equiv t.left).symm t.hom`. A morphism is sent to the unique lift
supplied by `bwdMap`, which exists by `exists_map` and is unique by faithfulness on fibres. -/
noncomputable def fromOver {X : 𝒞} {p : 𝒮 ⥤ 𝒞}
    (hset : p.IsFiberedInSetoids) (hrep : IsoClassRepresentableBy p X) :
    Over X ⥤ 𝒮 where
  obj t := (repr p hrep t).1
  map {t s} m := bwdMap hset hrep m
  map_id t := by
    have h1 := bwdMap_homlift hset hrep (𝟙 t)
    rw [Over.id_left] at h1
    have h2 : p.IsHomLift (𝟙 t.left) (𝟙 (repr p hrep t).1) := IsHomLift.id (repr p hrep t).2
    exact pfaithful_lift hset (𝟙 t.left) _ _
  map_comp {t s r} m m' := by
    have h1 := bwdMap_homlift hset hrep (m ≫ m')
    rw [Over.comp_left] at h1
    have ha := bwdMap_homlift hset hrep m
    have hb := bwdMap_homlift hset hrep m'
    exact pfaithful_lift hset (m.left ≫ m'.left) _ _

/-- `fromOver` is a 1-morphism over `𝒞`: it commutes strictly with the structure functors. -/
lemma fromOver_comp_proj {X : 𝒞} {p : 𝒮 ⥤ 𝒞}
    (hset : p.IsFiberedInSetoids) (hrep : IsoClassRepresentableBy p X) :
    fromOver hset hrep ⋙ p = Over.forget X := by
  apply CategoryTheory.Functor.ext
  case h_map =>
    intro t s m
    have hl := bwdMap_homlift hset hrep m
    simp only [Functor.comp_map, fromOver]
    rw [IsHomLift.fac' p m.left (bwdMap hset hrep m)]
    rfl
  case h_obj =>
    intro t
    exact (repr p hrep t).2

/-- The class of `repr p hrep (toOver.obj a)` agrees with the class of `⟨a, rfl⟩`. -/
lemma isoClass_repr_toOver {X : 𝒞} {p : 𝒮 ⥤ 𝒞}
    (hset : p.IsFiberedInSetoids) (hrep : IsoClassRepresentableBy p X) (a : 𝒮) :
    IsoClass.mk p (⟨a, rfl⟩ : p.Fiber (p.obj a)) =
      IsoClass.mk p (repr p hrep ((toOver hset hrep).obj a)) :=
  (hrep.equiv (p.obj a)).injective (repr_equiv p hrep ((toOver hset hrep).obj a)).symm

/-- Existence of a lift `a ⟶ (toOver ⋙ fromOver).obj a` over `𝟙 (p.obj a)`. -/
lemma unitHom_exists {X : 𝒞} {p : 𝒮 ⥤ 𝒞}
    (hset : p.IsFiberedInSetoids) (hrep : IsoClassRepresentableBy p X) (a : 𝒮) :
    ∃ χ : a ⟶ (toOver hset hrep ⋙ fromOver hset hrep).obj a, p.IsHomLift (𝟙 (p.obj a)) χ :=
  exists_map hset.isFiberedInGroupoids hrep (𝟙 (p.obj a))
    (repr p hrep ((toOver hset hrep).obj a)) ⟨a, rfl⟩ (by
      rw [Category.id_comp]
      exact congrArg (hrep.equiv (p.obj a)) (isoClass_repr_toOver hset hrep a))

/-- The chosen lift `a ⟶ (toOver ⋙ fromOver).obj a` over `𝟙 (p.obj a)`. -/
noncomputable def unitHom {X : 𝒞} {p : 𝒮 ⥤ 𝒞}
    (hset : p.IsFiberedInSetoids) (hrep : IsoClassRepresentableBy p X) (a : 𝒮) :
    a ⟶ (toOver hset hrep ⋙ fromOver hset hrep).obj a :=
  (unitHom_exists hset hrep a).choose

/-- `unitHom a` lies over `𝟙 (p.obj a)`. -/
instance unitHom_homlift {X : 𝒞} {p : 𝒮 ⥤ 𝒞}
    (hset : p.IsFiberedInSetoids) (hrep : IsoClassRepresentableBy p X) (a : 𝒮) :
    p.IsHomLift (𝟙 (p.obj a)) (unitHom hset hrep a) :=
  (unitHom_exists hset hrep a).choose_spec

/-- `unitHom a` is an isomorphism (a strongly-cartesian lift of `𝟙`). -/
instance unitHom_isIso {X : 𝒞} {p : 𝒮 ⥤ 𝒞}
    (hset : p.IsFiberedInSetoids) (hrep : IsoClassRepresentableBy p X) (a : 𝒮) :
    IsIso (unitHom hset hrep a) := by
  have : p.IsStronglyCartesian (𝟙 (p.obj a)) (unitHom hset hrep a) :=
    hset.isFiberedInGroupoids.isStronglyCartesian_homLift (𝟙 (p.obj a)) (unitHom hset hrep a)
  exact Functor.IsStronglyCartesian.isIso_of_base_isIso p (𝟙 (p.obj a))
    (unitHom hset hrep a)

/-- The unit 2-isomorphism `𝟭 𝒮 ≅ toOver ⋙ fromOver`. Each component is the chosen lift
`unitHom` of an identity, which is an isomorphism because a strongly cartesian lift of an
isomorphism is one. -/
noncomputable def unitIso {X : 𝒞} {p : 𝒮 ⥤ 𝒞}
    (hset : p.IsFiberedInSetoids) (hrep : IsoClassRepresentableBy p X) :
    𝟭 𝒮 ≅ toOver hset hrep ⋙ fromOver hset hrep := by
  refine NatIso.ofComponents
    (fun a => @asIso _ _ _ _ (unitHom hset hrep a) (unitHom_isIso hset hrep a)) ?_
  intro a b g
  -- Both composites lie over `p.map g`; conclude by faithfulness.
  have hbwd : p.IsHomLift (p.map g) ((toOver hset hrep ⋙ fromOver hset hrep).map g) := by
    have h2 := bwdMap_homlift hset hrep ((toOver hset hrep).map g)
    have he : ((toOver hset hrep).map g).left = p.map g := rfl
    rwa [he] at h2
  -- LHS: g ≫ η.app b  lies over  p.map g ≫ 𝟙 (p.obj b) = p.map g
  have hLHS : p.IsHomLift (p.map g ≫ 𝟙 (p.obj b))
      ((𝟭 𝒮).map g ≫ (@asIso _ _ _ _ (unitHom hset hrep b) (unitHom_isIso hset hrep
          b)).hom) :=
    IsHomLift.comp (p := p) (f := p.map g) (g := 𝟙 (p.obj b)) g (unitHom hset hrep b)
  rw [Category.comp_id] at hLHS
  -- RHS: η.app a ≫ F.map g  lies over  𝟙 (p.obj a) ≫ p.map g = p.map g
  have hRHS : p.IsHomLift (𝟙 (p.obj a) ≫ p.map g)
      ((@asIso _ _ _ _ (unitHom hset hrep a) (unitHom_isIso hset hrep a)).hom ≫
        (toOver hset hrep ⋙ fromOver hset hrep).map g) :=
    IsHomLift.comp (p := p) (f := 𝟙 (p.obj a)) (g := p.map g)
      (unitHom hset hrep a) _
  rw [Category.id_comp] at hRHS
  exact pfaithful_lift hset (p.map g) _ _

/-- Transport lemma: for a fibre object `r : p.Fiber W`, the class of `⟨r.1, rfl⟩` over
`p.obj r.1` corresponds to `eqToHom r.2` followed by the class of `r` over `W`. -/
lemma counit_transport {X : 𝒞} {p : 𝒮 ⥤ 𝒞}
    (hset : p.IsFiberedInSetoids) (hrep : IsoClassRepresentableBy p X)
    {W : 𝒞} (r : p.Fiber W) :
    hrep.equiv (p.obj r.1) (IsoClass.mk p ⟨r.1, rfl⟩) =
      eqToHom r.2 ≫ hrep.equiv W (IsoClass.mk p r) := by
  have hlift : p.IsHomLift (eqToHom r.2) (𝟙 r.1) := by
    apply IsHomLift.of_fac' p (eqToHom r.2) (𝟙 r.1) rfl r.2
    simp
  have hsc : p.IsStronglyCartesian (eqToHom r.2) (𝟙 r.1) :=
    hset.isFiberedInGroupoids.isStronglyCartesian_homLift (eqToHom r.2) (𝟙 r.1)
  have hpb : IsPullbackOver p (eqToHom r.2) r ⟨r.1, rfl⟩ := ⟨𝟙 r.1, hlift, hsc⟩
  exact hrep.naturality (eqToHom r.2) r ⟨r.1, rfl⟩ hpb

/-- The counit 2-isomorphism `fromOver ⋙ toOver ≅ 𝟭 (Over X)`, dual to `unitIso`: its
component at `t` is induced by the defining equation of the chosen representative `repr t`. -/
noncomputable def counitIso {X : 𝒞} {p : 𝒮 ⥤ 𝒞}
    (hset : p.IsFiberedInSetoids) (hrep : IsoClassRepresentableBy p X) :
    fromOver hset hrep ⋙ toOver hset hrep ≅ 𝟭 (Over X) := by
  refine NatIso.ofComponents
    (fun t => Over.isoMk (eqToIso (repr p hrep t).2) ?_) ?_
  · -- the `.w` triangle
    simp only [eqToIso.hom, Functor.id_obj]
    change eqToHom (repr p hrep t).2 ≫ t.hom =
        hrep.equiv (p.obj (repr p hrep t).1) (IsoClass.mk p ⟨(repr p hrep t).1, rfl⟩)
    rw [counit_transport hset hrep (repr p hrep t), repr_equiv]
  · -- naturality
    intro t s m
    apply Over.OverMorphism.ext
    have hl := bwdMap_homlift hset hrep m
    simp only [Functor.comp_map, Over.comp_left, Functor.id_map, Over.isoMk_hom_left,
      eqToIso.hom, fromOver, toOver, Over.homMk_left]
    rw [IsHomLift.fac' p m.left (bwdMap hset hrep m)]
    simp

/-- The converse construction packaged as an equivalence over `𝒞`: `toOver` and `fromOver`
with the unit and counit above, whose whiskerings are identity 2-cells because every
component lies over an identity of `𝒞`. -/
@[sga "4 I 6.5" "(ii)⇒(iv), special case"]
noncomputable def representableBy_of_setoid_and_isoClassRepr {X : 𝒞}
    {p : 𝒮 ⥤ 𝒞} (hset : p.IsFiberedInSetoids) (hrep : IsoClassRepresentableBy p X) :
    RepresentableBy p X :=
  { hom := ⟨toOver hset hrep, toOver_comp_forget hset hrep⟩
    inv := ⟨fromOver hset hrep, fromOver_comp_proj hset hrep⟩
    unitIso := unitIso hset hrep
    counitIso := counitIso hset hrep
    -- Coherence: whiskered unit is the identity 2-cell over `𝒞` (components lie over `𝟙`).
    unit_over := by
      ext a
      simp only [Functor.whiskerRight_app, unitIso, NatIso.ofComponents_hom_app,
        asIso_hom, eqToHom_app]
      rw [IsHomLift.fac' p (𝟙 (p.obj a)) (unitHom hset hrep a)]
      simp
    -- Coherence: whiskered counit is the identity 2-cell over `𝒞`.
    counit_over := by
      ext t
      simp [Functor.whiskerRight_app, counitIso, NatIso.ofComponents_hom_app, Over.forget_map,
        Over.isoMk_hom_left, eqToIso.hom, eqToHom_app] }

/-!
## Main results
-/

/-- **Stacks 02Y3** (part 1). A category fibred in groupoids `p : S ⥤ C` is representable
if and only if `S` is fibred in setoids and its presheaf of isomorphism classes
`\overline{S}` is representable. -/
@[stacks 02Y3 "(1)", sga "4 I 6.5" "(ii)⇔(iv), special case"]
theorem representable_iff (p : 𝒮 ⥤ 𝒞) :
    IsRepresentable p ↔ (p.IsFiberedInSetoids ∧ IsoClassRepresentable p) :=
  ⟨fun ⟨X, ⟨j⟩⟩ ↦ ⟨isFiberedInSetoids_of_equivalenceOver j (over_isFiberedInSetoids X),
      X, ⟨isoClassRepresentableBy_of_equivalenceOver j⟩⟩,
    fun ⟨hset, X, ⟨hrep⟩⟩ ↦ ⟨X, ⟨representableBy_of_setoid_and_isoClassRepr hset hrep⟩⟩⟩

/-- **Stacks 02Y3** (part 2). If `p : S ⥤ C` is representable by both `X` (via `j`) and `X'`
(via `j'`), then the representing objects are **canonically isomorphic** in `C`: this is
the isomorphism `X' ≅ X` induced by the composite equivalence over `C`, obtained by
transporting the terminal object `(X', 𝟙 X')` of `Over X'` to the terminal object
`(X, 𝟙 X)` of `Over X`. -/
@[stacks 02Y3 "(2)"]
noncomputable def representing_object_unique (p : 𝒮 ⥤ 𝒞)
    {X X' : 𝒞} (j : RepresentableBy p X) (j' : RepresentableBy p X') :
    X' ≅ X := by
  let e : Over X' ≌ Over X :=
    (EquivalenceOver.toEquivalence j').symm.trans (EquivalenceOver.toEquivalence j)
  have hefun : e.functor = j'.inv.functor ⋙ j.hom.functor := by
    rw [Equivalence.trans_functor, Equivalence.symm_functor]
    rfl
  have hw : e.functor ⋙ Over.forget X = Over.forget X' := by
    rw [hefun, Functor.assoc, j.hom.w, j'.inv.w]
  have hsrc : (Over.forget X).obj (e.functor.obj (Over.mk (𝟙 X'))) = X' := by
    simpa using Functor.congr_obj hw (Over.mk (𝟙 X'))
  exact eqToIso hsrc.symm ≪≫ (Over.forget X).mapIso
    ((Over.mkIdTerminal.isTerminalObj e.functor _).uniqueUpToIso Over.mkIdTerminal)

end StacksRepresentableCFG
