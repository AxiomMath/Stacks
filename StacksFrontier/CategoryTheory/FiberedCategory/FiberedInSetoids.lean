module

public import StacksFrontier.CategoryTheory.FiberedCategory.TwoFibreProduct
public import StacksFrontier.CategoryTheory.FiberedInSetoids.Defs
public import StacksFrontier.CategoryTheory.Sites.Stack.TwoFibreProductMorPresheafMap
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Categories fibred in setoids and their presheaves of isomorphism classes

A category fibred in setoids over `𝒞` is a fibred category `p : 𝒮 ⥤ 𝒞` all of whose fibre
categories are setoids, that is thin groupoids. Thinness of the fibres propagates to the whole
of `𝒮`: between two fixed objects there is at most one morphism lying over a fixed morphism of
the base. This is why the cocycle condition on a descent datum is automatic for such a `p`,
there being no choice of gluing morphism to be made.

To a fibred category `p` one attaches the presheaf `\overline{𝒮} : U ↦ Ob(𝒮_U)/≅` of isomorphism
classes of objects of the fibres; a choice of pullbacks gives the restriction maps, and the choice
does not matter because two cartesian lifts of one morphism have isomorphic domains. Stacks 04SC
says that for categories fibred in setoids this construction is an equivalence onto the category of
presheaves: it is fully faithful up to unique 2-isomorphism, surjective on morphisms, and the
identity on categories fibred in sets. Stacks 04SD says it takes a 2-fibre product to a fibre
product.

Throughout, "isomorphic" means isomorphic **in the fibre category**, that is by an isomorphism of
`𝒮` lying over an identity of `𝒞` — the vertical reading. This is the source's own meaning: its
`Ob(𝒮_U)/\!\cong` is the set of isomorphism classes of the fibre category `𝒮_U`, and the
2-morphisms of the 2-category of categories over `𝒞` (Stacks 003Y) are the morphisms of functors
whose components lie over identities.

## Main definitions

* `CategoryTheory.Functor.isoClassMk`, `CategoryTheory.Functor.isoClassPresheaf`: the presheaf
  `\overline{𝒮}` of isomorphism classes of objects of the fibres, and the class of an object.
* `CategoryTheory.Functor.isoClassMap`: the map of presheaves induced by a 1-morphism of fibred
  categories, with `CategoryTheory.Functor.isoClassMapOfCompEq` its form for categories fibred in
  setoids, where preservation of cartesian morphisms is automatic.
* `CategoryTheory.Functor.twoIsoSetoid`: 2-isomorphism of 1-morphisms over `𝒞`.
* `CategoryTheory.Functor.isoClassLiftFunctor`: the 1-morphism attached to a map of presheaves.

## Main results

* `CategoryTheory.Functor.existsUnique_twoIso_of_isoClassMap_eq`: **Stacks 04SC (1)**.
* `CategoryTheory.Functor.exists_oneMorphism_isoClassMap_eq`: **Stacks 04SC (2)**.
* `CategoryTheory.Functor.fiberPresheafIsoIsoClassPresheaf`: **Stacks 04SC (3)**.
* `CategoryTheory.Functor.isoClassMapEquiv`: **Stacks 04SC**, the bijection
  `Mor_{Cat/𝒞}(𝒮₁, 𝒮₂)/2\text{-isomorphism} = Mor_{PSh(𝒞)}(F₁, F₂)`.
* `CategoryTheory.Functor.twoFibreProductIsoClassEquiv` and
  `CategoryTheory.Functor.twoFibreProductIsoClassMap_naturality`: **Stacks 04SD**.

## Implementation notes

The chosen pullbacks and their coherences are `CategoryTheory.Functor.pullbackFiber`,
`pullbackFiberIso`, `pullbackFiberIdIso` and `pullbackFiberCompIso` from
`StacksFrontier.CategoryTheory.Sites.Descent.IsStack`, which is where this development already keeps
them; the fibre functor of a 1-morphism and its comparison isomorphism with the chosen pullbacks
are `fiberFunctorOfCompEq` and `IsFibredOneMorphism.mapPullbackFiberIso` from
`StacksFrontier.CategoryTheory.Sites.Stack.TwoFibreProductMorPresheafMap`. Those two are stated for
categories whose hom universe agrees with that of `𝒞`, which is why everything from the section on
1-morphisms onwards carries that restriction; the presheaf itself is universe-polymorphic, and so
is `CategoryTheory.Functor.existsUnique_twoIso_of_forall_exists_vertical_hom`, whose proof uses
neither of those two.

The 2-fibre product is `CategoryTheory.TwoFibreProductOver` (Stacks 0040), whose comparison
isomorphism is required to be vertical — this is the 2-fibre product *over `𝒞`*, and not Mathlib's
`CategoryTheory.Limits.CategoricalPullback`. The `IsFibered` hypothesis on it that
`twoFibreProductIsoClassMap_naturality` needs is supplied by
`CategoryTheory.TwoFibreProductOver.isFibered_structureFunctor` (Stacks 02XQ). Stacks 04SD is
stated with the two outer categories only assumed fibred, with the projections 1-morphisms of
fibred categories; only the middle one has to be fibred in setoids, which is where the source's
warning that the lemma fails otherwise bites.
-/

@[expose] public section

open Opposite

namespace CategoryTheory.Functor

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]

section Fibered

variable {𝒮 : Type u₂} [Category.{v₂} 𝒮]

/-- In a fibred category whose fibre over `R` is thin, two morphisms `a ⟶ b` lying over the same
morphism `f : R ⟶ T` of the base are equal: each factors through a cartesian lift of `f` by a
morphism of the fibre over `R`, and the two factorisations agree by thinness. -/
@[sga "4 I 6.5.2" "(ii)"]
lemma hom_unique_of_fiber_isThin (p : 𝒮 ⥤ 𝒞) [p.IsFibered] {R T : 𝒞} (f : R ⟶ T)
    (ht : Quiver.IsThin (p.Fiber R)) {a b : 𝒮} (φ₁ φ₂ : a ⟶ b)
    (h₁ : p.IsHomLift f φ₁) (h₂ : p.IsHomLift f φ₂) : φ₁ = φ₂ := by
  obtain ⟨a', ψ, hψ⟩ := IsPreFibered.exists_isCartesian p (IsHomLift.codomain_eq p f φ₁) f
  obtain ⟨χ₁, ⟨hχ₁, hχ₁'⟩, -⟩ := IsCartesian.universal_property (p := p) (φ := ψ) f φ₁
  obtain ⟨χ₂, ⟨hχ₂, hχ₂'⟩, -⟩ := IsCartesian.universal_property (p := p) (φ := ψ) f φ₂
  have hχ : χ₁ = χ₂ := by
    simpa using congrArg Fiber.fiberInclusion.map
      ((ht _ _).allEq (Fiber.homMk p R χ₁) (Fiber.homMk p R χ₂))
  rw [← hχ₁', ← hχ₂', hχ]

/-- A morphism lying over an identity followed by a morphism lying over `f` lies over `f`. The
`IsHomLift` hypotheses are explicit arguments rather than instances, so that this applies to a
composite whose middle object is spelled differently in the two factors — which is the normal
situation when the first factor comes from a fibre category and the second from a chosen
pullback. -/
lemma isHomLift_comp_of_isHomLift_id (p : 𝒮 ⥤ 𝒞) {R S : 𝒞} {a b c : 𝒮} (ε : a ⟶ b) (π : b ⟶ c)
    (f : R ⟶ S) (hε : p.IsHomLift (𝟙 R) ε) (hπ : p.IsHomLift f π) : p.IsHomLift f (ε ≫ π) :=
  IsHomLift.comp_lift_id_left' p R ε f π

/-- A morphism lying over an identity contributes only a transport: conjugating it by `eqToHom`s
into a fixed pair of base objects gives the canonical `eqToHom`. The `IsHomLift` hypothesis is an
explicit argument rather than an instance. -/
lemma eqToHom_comp_map_comp_eqToHom (p : 𝒮 ⥤ 𝒞) {U V W : 𝒞} {a b : 𝒮} (φ : a ⟶ b)
    (h : p.IsHomLift (𝟙 U) φ) (hV : p.obj a = V) (hW : p.obj b = W) (hVW : V = W) :
    eqToHom hV.symm ≫ p.map φ ≫ eqToHom hW = eqToHom hVW := by
  rw [IsHomLift.fac' p (𝟙 U) φ]
  subst hV hW
  simp

/-! ## The presheaf of isomorphism classes of objects of the fibres -/

section IsoClassPresheaf

/-- Being related by `CategoryTheory.isIsomorphicSetoid` is being isomorphic. Unfolding the
setoid is spelled out once here because the anonymous constructor cannot see through `Setoid.r`
while the setoid is still a metavariable. -/
lemma isIsomorphicSetoid_r_iff {D : Type u₃} [Category.{v₃} D] (x y : D) :
    (isIsomorphicSetoid D).r x y ↔ Nonempty (x ≅ y) :=
  Iff.rfl

variable (p : 𝒮 ⥤ 𝒞)

/-- The isomorphism class of an object of the fibre over `U`, an element of `Ob(𝒮_U)/≅`. -/
def isoClassMk {U : 𝒞} (x : p.Fiber U) : _root_.Quotient (isIsomorphicSetoid (p.Fiber U)) :=
  _root_.Quotient.mk _ x

/-- The presheaf `\overline{𝒮}` on `𝒞` sending `U` to the set `Ob(𝒮_U)/≅` of isomorphism classes
of objects of the fibre category over `U`, and a morphism `f : V ⟶ U` to the map induced by a
choice of pullbacks. The choice does not matter: two cartesian lifts of `f` at the same object
have isomorphic domains, so the induced map on isomorphism classes is canonical. -/
@[implicit_reducible]
noncomputable def isoClassPresheaf [p.IsFibered] : 𝒞ᵒᵖ ⥤ Type u₂ where
  obj U := _root_.Quotient (isIsomorphicSetoid (p.Fiber U.unop))
  map {_ _} f := ↾fun c => _root_.Quotient.liftOn c
    (fun x => isoClassMk p (pullbackFiber p x f.unop))
    (fun _ _ h => _root_.Quotient.sound
      (((isIsomorphicSetoid_r_iff _ _).2
        ⟨pullbackFiberIso ((isIsomorphicSetoid_r_iff _ _).1 h).some f.unop⟩)))
  map_id U := by
    ext x
    induction x using _root_.Quotient.ind with
    | _ x =>
      exact _root_.Quotient.sound ((isIsomorphicSetoid_r_iff _ _).2 ⟨pullbackFiberIdIso x⟩)
  map_comp {_ _ _} f g := by
    ext x
    induction x using _root_.Quotient.ind with
    | _ x =>
      exact _root_.Quotient.sound ((isIsomorphicSetoid_r_iff _ _).2
        ⟨(pullbackFiberCompIso x f.unop g.unop).symm⟩)

variable {p}

/-- Every element of `Ob(𝒮_U)/≅` is the class of an object of the fibre over `U`. -/
lemma isoClassMk_surjective {U : 𝒞} (c : _root_.Quotient (isIsomorphicSetoid (p.Fiber U))) :
    ∃ x : p.Fiber U, isoClassMk p x = c :=
  _root_.Quot.exists_rep c

/-- Restricting the class of `x` along `f : V ⟶ U` is the class of the chosen pullback `f^* x`. -/
@[simp]
lemma isoClassPresheaf_map_isoClassMk [p.IsFibered] {U V : 𝒞} (f : V ⟶ U) (x : p.Fiber U) :
    p.isoClassPresheaf.map f.op (isoClassMk p x) = isoClassMk p (pullbackFiber p x f) :=
  rfl

/-- Two objects of the fibre over `U` have the same class exactly when they are isomorphic in
that fibre. -/
lemma isoClassMk_eq_iff {U : 𝒞} (x y : p.Fiber U) :
    isoClassMk p x = isoClassMk p y ↔ Nonempty (x ≅ y) :=
  ⟨fun h => (isIsomorphicSetoid_r_iff _ _).1 (_root_.Quotient.exact h),
    fun h => _root_.Quotient.sound ((isIsomorphicSetoid_r_iff _ _).2 h)⟩

/-- Objects of a fibre isomorphic in that fibre have the same isomorphism class. -/
lemma isoClassMk_eq_of_iso {U : 𝒞} {x y : p.Fiber U} (e : x ≅ y) :
    isoClassMk p x = isoClassMk p y :=
  (isoClassMk_eq_iff x y).2 ⟨e⟩

/-- Objects of a fibre with the same isomorphism class are isomorphic in that fibre. -/
lemma exists_iso_of_isoClassMk_eq {U : 𝒞} {x y : p.Fiber U}
    (h : isoClassMk p x = isoClassMk p y) : Nonempty (x ≅ y) :=
  (isoClassMk_eq_iff x y).1 h

/-- The class of the domain of *any* cartesian lift of `f : V ⟶ U` at `x` is the restriction
along `f` of the class of `x`. This is what makes `isoClassPresheaf` independent of the choice
of pullbacks, and is the form in which the presheaf is used. -/
lemma isoClassMk_eq_pullbackFiber_of_isCartesian [p.IsPreFibered] {U V : 𝒞} (f : V ⟶ U)
    (x : p.Fiber U) (y : p.Fiber V) (φ : y.1 ⟶ x.1) (_ : p.IsHomLift f φ)
    (hc : p.IsCartesian f φ) :
    isoClassMk p y = isoClassMk p (pullbackFiber p x f) :=
  isoClassMk_eq_of_iso
    (fiberIsoOfCartesian f φ (IsPreFibered.pullbackMap x.2 f) hc
      (IsPreFibered.pullbackMap.IsCartesian x.2 f))

end IsoClassPresheaf

/-- A category fibred in setoids is a fibred category. -/
instance IsFiberedInSetoids.isFibered {𝒮 : Type u₂} [Category.{v₂} 𝒮] (p : 𝒮 ⥤ 𝒞)
    [hp : p.IsFiberedInSetoids] : p.IsFibered :=
  hp.isFiberedInGroupoids.isFibered

end Fibered

/-! ## The map of presheaves induced by a 1-morphism

The declarations from here on tie the hom universes of the categories over `𝒞` to that of `𝒞`
itself, since `CategoryTheory.Functor.fiberFunctorOfCompEq` and
`CategoryTheory.Functor.IsFibredOneMorphism.mapPullbackFiberIso`, which they reuse, are stated
that way.
-/

section IsoClassMap

variable {𝒮 𝒯 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₁} 𝒯]

/-- A functor strictly over `𝒞` transports `IsHomLift`, with the two categories over `𝒞` at
independent universes: nothing in this statement passes through a fibre category, so there is
nothing to tie the two hom universes to that of `𝒞`. A 1-morphism from a category whose
morphisms are small down from its own universe enlargement is exactly such a case. -/
lemma isHomLift_map_of_comp_eq_general {𝒮' : Type u₂} [Category.{v₂} 𝒮'] {𝒯' : Type u₃}
    [Category.{v₃} 𝒯'] {p : 𝒮' ⥤ 𝒞} {q : 𝒯' ⥤ 𝒞} {G : 𝒮' ⥤ 𝒯'} (hG : G ⋙ q = p)
    {R T : 𝒞} (f : R ⟶ T) {a b : 𝒮'} (φ : a ⟶ b) (h : p.IsHomLift f φ) :
    q.IsHomLift f (G.map φ) :=
  isHomLift_map_of_comp_eq hG f φ

/-- A functor strictly over `𝒞` transports `IsHomLift`, with the hypothesis as an explicit
argument rather than an instance. -/
lemma isHomLift_map_of_comp_eq' {p : 𝒮 ⥤ 𝒞} {q : 𝒯 ⥤ 𝒞} {G : 𝒮 ⥤ 𝒯} (hG : G ⋙ q = p)
    {R T : 𝒞} (f : R ⟶ T) {a b : 𝒮} (φ : a ⟶ b) (h : p.IsHomLift f φ) :
    q.IsHomLift f (G.map φ) :=
  isHomLift_map_of_comp_eq hG f φ

variable {p : 𝒮 ⥤ 𝒞} {q : 𝒯 ⥤ 𝒞} [p.IsFibered] [q.IsFibered]

/-- The map `\overline{𝒮} ⟶ \overline{𝒯}` of presheaves of isomorphism classes induced by a
1-morphism `G` of fibred categories over `𝒞`: on classes it is `[x] ↦ [G x]`. Naturality is the
statement that `G` carries a cartesian lift of `f` to a cartesian lift of `f`, which is the
defining property of a 1-morphism of fibred categories. -/
noncomputable def isoClassMap {G : 𝒮 ⥤ 𝒯} (hG : IsFibredOneMorphism p q G) :
    p.isoClassPresheaf ⟶ q.isoClassPresheaf where
  app U := ↾fun c : _root_.Quotient (isIsomorphicSetoid (p.Fiber U.unop)) =>
    _root_.Quotient.liftOn c
      (fun x => isoClassMk q ((fiberFunctorOfCompEq hG.comp_eq U.unop).obj x))
      (fun _ _ h => isoClassMk_eq_of_iso ((fiberFunctorOfCompEq hG.comp_eq U.unop).mapIso
        ((isIsomorphicSetoid_r_iff _ _).1 h).some))
  naturality {_ _} f := by
    ext c
    induction c using _root_.Quotient.ind with
    | _ x => exact (isoClassMk_eq_of_iso (hG.mapPullbackFiberIso x f.unop)).symm

/-- `CategoryTheory.Functor.isoClassMap hG` sends the class of `x` to the class of the image of
`x` under the fibre functor of `G` over `U`. -/
@[simp]
lemma isoClassMap_app_isoClassMk {G : 𝒮 ⥤ 𝒯} (hG : IsFibredOneMorphism p q G) {U : 𝒞}
    (x : p.Fiber U) : (isoClassMap hG).app (op U) (isoClassMk p x) =
      isoClassMk q ((fiberFunctorOfCompEq hG.comp_eq U).obj x) :=
  rfl

/-- Two maps of presheaves of isomorphism classes are equal if they agree on every class `[x]`. -/
private lemma isoClassPresheaf_hom_ext {G H : p.isoClassPresheaf ⟶ q.isoClassPresheaf}
    (h : ∀ {U : 𝒞} (x : p.Fiber U),
      G.app (op U) (isoClassMk p x) = H.app (op U) (isoClassMk p x)) : G = H := by
  ext ⟨U⟩ c
  induction c using _root_.Quotient.ind with
  | _ x => exact h x

omit [p.IsFibered] [q.IsFibered] in
/-- Between categories fibred in groupoids, *every* functor over `𝒞` is a 1-morphism of fibred
categories: by Stacks 003V every morphism of a category fibred in groupoids is strongly
cartesian, so there is nothing to preserve. -/
@[sga "4 XVIII 1.4.6" "more general"]
lemma isFibredOneMorphism_of_isFiberedInGroupoids (hq : q.IsFiberedInGroupoids) {G : 𝒮 ⥤ 𝒯}
    (hG : G ⋙ q = p) : IsFibredOneMorphism p q G where
  comp_eq := hG
  map_isStronglyCartesian := by
    intro _ _ f _ _ φ hφ
    have : q.IsHomLift f (G.map φ) := isHomLift_map_of_comp_eq hG f φ
    exact hq.isStronglyCartesian_homLift f (G.map φ)

/-- The map of presheaves of isomorphism classes induced by a functor over `𝒞` between categories
fibred in setoids. This is the functor `F` of Stacks 04SC on 1-morphisms. -/
noncomputable abbrev isoClassMapOfCompEq [p.IsFiberedInSetoids] [hq : q.IsFiberedInSetoids]
    {G : 𝒮 ⥤ 𝒯} (hG : G ⋙ q = p) : p.isoClassPresheaf ⟶ q.isoClassPresheaf :=
  isoClassMap (isFibredOneMorphism_of_isFiberedInGroupoids hq.isFiberedInGroupoids hG)

end IsoClassMap

/-! ## Stacks 04SC (1): rigidity of 1-morphisms of categories fibred in setoids -/

section TwoIsoOfVerticalHom

variable {𝒮 : Type u₂} [Category.{v₂} 𝒮] {𝒯 : Type u₃} [Category.{v₃} 𝒯]
  {p : 𝒮 ⥤ 𝒞} {q : 𝒯 ⥤ 𝒞} [hq : q.IsFiberedInSetoids]

/-- Between two fixed objects of a category fibred in setoids there is at most one morphism lying
over a fixed morphism of the base. -/
lemma hom_unique_of_isFiberedInSetoids {R T : 𝒞} (f : R ⟶ T) {a b : 𝒯} (θ₁ θ₂ : a ⟶ b)
    (h₁ : q.IsHomLift f θ₁) (h₂ : q.IsHomLift f θ₂) : θ₁ = θ₂ :=
  hom_unique_of_fiber_isThin q f (hq.fiber_isThin R) θ₁ θ₂ h₁ h₂

/-- The engine of Stacks 04SC (1): if two 1-morphisms `G, H : 𝒮 ⥤ 𝒯` over `𝒞` into a category
fibred in setoids agree on objects up to a vertical morphism, then there is a unique
2-isomorphism `G ≅ H` over `𝒞`. Both halves come from thinness of the fibres of `q`: it makes the
chosen vertical morphisms `G x ⟶ H x` unique, hence natural, and it makes any competing
2-morphism equal to them componentwise. That they are isomorphisms is automatic, since a morphism
of a category fibred in groupoids lying over an isomorphism is an isomorphism.

Only `q` needs to be fibred in setoids, and nothing in the argument relates the universes of the
source and the target to those of the base, so `𝒮` and `𝒯` are allowed to be arbitrary — which is
what lets a possibly large category fibred in setoids be compared with the small category of
elements of a presheaf. -/
theorem existsUnique_twoIso_of_forall_exists_vertical_hom {G H : 𝒮 ⥤ 𝒯} (hG : G ⋙ q = p)
    (hH : H ⋙ q = p) (h : ∀ x : 𝒮, ∃ θ : G.obj x ⟶ H.obj x, q.IsHomLift (𝟙 (p.obj x)) θ) :
    ∃! e : G ≅ H, ∀ x : 𝒮, q.IsHomLift (𝟙 (p.obj x)) (e.hom.app x) := by
  classical
  have hθ : ∀ x : 𝒮, q.IsHomLift (𝟙 (p.obj x)) (h x).choose := fun x => (h x).choose_spec
  have huniq : ∀ {x : 𝒮} (θ' : G.obj x ⟶ H.obj x), q.IsHomLift (𝟙 (p.obj x)) θ' →
      θ' = (h x).choose :=
    fun {x} θ' h' => hom_unique_of_isFiberedInSetoids (𝟙 (p.obj x)) _ _ h' (hθ x)
  have hnat : ∀ {x y : 𝒮} (ψ : x ⟶ y),
      G.map ψ ≫ (h y).choose = (h x).choose ≫ H.map ψ := by
    intro x y ψ
    have h1 : q.IsHomLift (p.map ψ) (G.map ψ ≫ (h y).choose) := by
      have := isHomLift_map_of_comp_eq hG (p.map ψ) ψ
      have := hθ y
      exact IsHomLift.comp_lift_id_right' q (p.map ψ) (G.map ψ) (p.obj y) (h y).choose
    have h2 : q.IsHomLift (p.map ψ) ((h x).choose ≫ H.map ψ) := by
      have := isHomLift_map_of_comp_eq hH (p.map ψ) ψ
      have := hθ x
      exact IsHomLift.comp_lift_id_left' q (p.obj x) (h x).choose (p.map ψ) (H.map ψ)
    exact hom_unique_of_isFiberedInSetoids (p.map ψ) _ _ h1 h2
  let t : G ⟶ H := { app := fun x => (h x).choose, naturality := fun _ _ ψ => hnat ψ }
  have hiso : ∀ x : 𝒮, IsIso (t.app x) := fun x =>
    have := hθ x
    have := hq.isFiberedInGroupoids.isStronglyCartesian_homLift (𝟙 (p.obj x)) (h x).choose
    IsStronglyCartesian.isIso_of_base_isIso q (𝟙 (p.obj x)) (h x).choose
  have : IsIso t := NatIso.isIso_of_isIso_app t
  exact ⟨asIso t, hθ, fun e he => Iso.ext (NatTrans.ext (funext fun x => huniq _ (he x)))⟩

end TwoIsoOfVerticalHom

section TwoIso

variable {𝒮 𝒯 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₁} 𝒯] {p : 𝒮 ⥤ 𝒞} {q : 𝒯 ⥤ 𝒞}
  [hp : p.IsFiberedInSetoids] [hq : q.IsFiberedInSetoids]

/-- **Stacks 04SC (1).** For two 1-morphisms `f, g : 𝒮₁ ⟶ 𝒮₂` of categories fibred in setoids
over `𝒞` with `F(f) = F(g)`, that is inducing the same map on the presheaves of isomorphism
classes of objects, there is a unique 2-isomorphism `f ⟶ g`. -/
@[stacks 04SC "(1): a unique 2-isomorphism between two 1-morphisms with the same image under F."]
theorem existsUnique_twoIso_of_isoClassMap_eq {G H : 𝒮 ⥤ 𝒯} (hG : G ⋙ q = p) (hH : H ⋙ q = p)
    (h : isoClassMapOfCompEq hG = isoClassMapOfCompEq hH) :
    ∃! e : G ≅ H, ∀ x : 𝒮, q.IsHomLift (𝟙 (p.obj x)) (e.hom.app x) := by
  refine existsUnique_twoIso_of_forall_exists_vertical_hom hG hH fun x => ?_
  have hx := congrArg (fun t : p.isoClassPresheaf ⟶ q.isoClassPresheaf =>
    t.app (op (p.obj x)) (isoClassMk p (⟨x, rfl⟩ : p.Fiber (p.obj x)))) h
  obtain ⟨e⟩ := exists_iso_of_isoClassMk_eq hx
  exact ⟨Fiber.fiberInclusion.map e.hom, e.hom.2⟩

end TwoIso

/-! ## Stacks 04SC (2): every map of presheaves is induced by a 1-morphism -/

section Lift

variable {𝒮 𝒯 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₁} 𝒯] {p : 𝒮 ⥤ 𝒞} {q : 𝒯 ⥤ 𝒞}
  [hp : p.IsFiberedInSetoids] [hq : q.IsFiberedInSetoids]
  (φ : p.isoClassPresheaf ⟶ q.isoClassPresheaf)

/-- A chosen object of the fibre of `q` over `p(x)` in the isomorphism class `φ([x])`. This is the
choice of representatives that turns a map of presheaves of isomorphism classes into a
1-morphism. -/
noncomputable def isoClassLiftFiber (x : 𝒮) : q.Fiber (p.obj x) :=
  _root_.Quotient.out (φ.app (op (p.obj x)) (isoClassMk p ⟨x, rfl⟩))

/-- The chosen representative of `φ([x])` does lie in the class `φ([x])`. -/
@[simp]
lemma isoClassMk_isoClassLiftFiber (x : 𝒮) :
    isoClassMk q (isoClassLiftFiber φ x) = φ.app (op (p.obj x)) (isoClassMk p ⟨x, rfl⟩) :=
  _root_.Quotient.out_eq _

/-- The chosen representatives are related by a morphism over `p(ψ)` for every `ψ : x ⟶ y` of `𝒮`.
This is the heart of Stacks 04SC (2): as `𝒮` is fibred in groupoids, `ψ` is cartesian, so `[x]` is
the restriction of `[y]` along `p(ψ)`; applying `φ` and using its naturality, `φ([x])` is the
restriction of `φ([y])`, that is the class of a pullback of the chosen representative of
`φ([y])`. -/
lemma exists_isHomLift_isoClassLiftFiber {x y : 𝒮} (ψ : x ⟶ y) :
    ∃ χ : (isoClassLiftFiber φ x).1 ⟶ (isoClassLiftFiber φ y).1,
      q.IsHomLift (p.map ψ) χ := by
  have hcart : p.IsCartesian (p.map ψ) ψ :=
    have := hp.isFiberedInGroupoids.isStronglyCartesian ψ
    inferInstance
  have hbase : isoClassMk p (⟨x, rfl⟩ : p.Fiber (p.obj x))
      = p.isoClassPresheaf.map (p.map ψ).op (isoClassMk p (⟨y, rfl⟩ : p.Fiber (p.obj y))) :=
    isoClassMk_eq_pullbackFiber_of_isCartesian (p.map ψ) ⟨y, rfl⟩ ⟨x, rfl⟩ ψ
      inferInstance hcart
  have key : isoClassMk q (isoClassLiftFiber φ x)
      = isoClassMk q (pullbackFiber q (isoClassLiftFiber φ y) (p.map ψ)) := by
    rw [isoClassMk_isoClassLiftFiber, hbase,
      NatTrans.naturality_apply φ (p.map ψ).op (isoClassMk p (⟨y, rfl⟩ : p.Fiber (p.obj y))),
      ← isoClassMk_isoClassLiftFiber φ y, isoClassPresheaf_map_isoClassMk]
  obtain ⟨e⟩ := exists_iso_of_isoClassMk_eq key
  exact ⟨_, isHomLift_comp_of_isHomLift_id q (Fiber.fiberInclusion.map e.hom)
    (IsPreFibered.pullbackMap (isoClassLiftFiber φ y).2 (p.map ψ)) (p.map ψ) e.hom.2
    (IsPreFibered.pullbackMap.IsCartesian (isoClassLiftFiber φ y).2 (p.map ψ)).toIsHomLift⟩

/-- The morphism of `𝒯` between the chosen representatives lying over `p(ψ)`. It is the *unique*
such morphism, since the fibres of `q` are thin; that is why it is functorial. -/
noncomputable def isoClassLiftMap {x y : 𝒮} (ψ : x ⟶ y) :
    (isoClassLiftFiber φ x).1 ⟶ (isoClassLiftFiber φ y).1 :=
  (exists_isHomLift_isoClassLiftFiber φ ψ).choose

/-- `CategoryTheory.Functor.isoClassLiftMap φ ψ` lies over `p(ψ)`. -/
instance isHomLift_isoClassLiftMap {x y : 𝒮} (ψ : x ⟶ y) :
    q.IsHomLift (p.map ψ) (isoClassLiftMap φ ψ) :=
  (exists_isHomLift_isoClassLiftFiber φ ψ).choose_spec

/-- The 1-morphism `𝒮 ⥤ 𝒯` over `𝒞` induced by a map of presheaves of isomorphism classes
(Stacks 04SC (2)). On objects it picks a representative of the image class; on morphisms it takes
the unique morphism of `𝒯` between the chosen representatives lying over the given morphism of
`𝒞`. Functoriality is that uniqueness. -/
noncomputable def isoClassLiftFunctor : 𝒮 ⥤ 𝒯 where
  obj x := (isoClassLiftFiber φ x).1
  map ψ := isoClassLiftMap φ ψ
  map_id x := by
    have h2 : q.IsHomLift (p.map (𝟙 x)) (𝟙 (isoClassLiftFiber φ x).1) := by
      rw [p.map_id]
      exact IsHomLift.id (isoClassLiftFiber φ x).2
    exact hom_unique_of_isFiberedInSetoids (p.map (𝟙 x)) (isoClassLiftMap φ (𝟙 x)) _
      (isHomLift_isoClassLiftMap φ (𝟙 x)) h2
  map_comp ψ χ := by
    have h2 : q.IsHomLift (p.map (ψ ≫ χ)) (isoClassLiftMap φ ψ ≫ isoClassLiftMap φ χ) := by
      rw [p.map_comp]
      infer_instance
    exact hom_unique_of_isFiberedInSetoids (p.map (ψ ≫ χ)) (isoClassLiftMap φ (ψ ≫ χ)) _
      (isHomLift_isoClassLiftMap φ (ψ ≫ χ)) h2

/-- `CategoryTheory.Functor.isoClassLiftFunctor φ` acts on morphisms by
`CategoryTheory.Functor.isoClassLiftMap φ`. -/
@[simp]
lemma isoClassLiftFunctor_map {x y : 𝒮} (ψ : x ⟶ y) :
    (isoClassLiftFunctor φ).map ψ = isoClassLiftMap φ ψ :=
  rfl

/-- The functor of `CategoryTheory.Functor.isoClassLiftFunctor` is a 1-morphism over `𝒞`. -/
lemma isoClassLiftFunctor_comp_eq : isoClassLiftFunctor φ ⋙ q = p :=
  Functor.ext (fun x => (isoClassLiftFiber φ x).2) fun _ _ ψ =>
    IsHomLift.fac' q (p.map ψ) (isoClassLiftMap φ ψ)

/-- At an object of an arbitrary fibre, the class of the image under
`CategoryTheory.Functor.isoClassLiftFunctor` is the value of `φ`. -/
lemma isoClassMk_fiberFunctorOfCompEq_isoClassLiftFunctor {U : 𝒞} (x : p.Fiber U) :
    isoClassMk q ((fiberFunctorOfCompEq (isoClassLiftFunctor_comp_eq φ) U).obj x)
      = φ.app (op U) (isoClassMk p x) := by
  obtain ⟨a, rfl⟩ := x
  exact isoClassMk_isoClassLiftFiber φ a

/-- `CategoryTheory.Functor.isoClassLiftFunctor` induces the given map of presheaves of
isomorphism classes. -/
lemma isoClassMapOfCompEq_isoClassLiftFunctor :
    isoClassMapOfCompEq (isoClassLiftFunctor_comp_eq φ) = φ := by
  exact isoClassPresheaf_hom_ext fun x => isoClassMk_fiberFunctorOfCompEq_isoClassLiftFunctor φ x

/-- **Stacks 04SC (2).** Every morphism `h : F(𝒮₁) ⟶ F(𝒮₂)` of presheaves of isomorphism classes
is `F(f)` for a 1-morphism `f : 𝒮₁ ⟶ 𝒮₂` of categories fibred in setoids over `𝒞`. -/
@[stacks 04SC "(2): every map of the associated presheaves comes from a 1-morphism."]
theorem exists_oneMorphism_isoClassMap_eq :
    ∃ (G : 𝒮 ⥤ 𝒯) (hG : G ⋙ q = p), isoClassMapOfCompEq hG = φ :=
  ⟨isoClassLiftFunctor φ, isoClassLiftFunctor_comp_eq φ,
    isoClassMapOfCompEq_isoClassLiftFunctor φ⟩

end Lift

/-! ## Stacks 04SC: 1-morphisms modulo 2-isomorphism are maps of the associated presheaves -/

section Equiv

variable {𝒮 𝒯 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₁} 𝒯]

/-- Two 1-morphisms `𝒮 ⥤ 𝒯` over `𝒞` are *2-isomorphic* when there is a natural isomorphism
between them whose components all lie over identities, that is a 2-isomorphism in the 2-category
of categories over `𝒞`. -/
def twoIsoSetoid (p : 𝒮 ⥤ 𝒞) (q : 𝒯 ⥤ 𝒞) : Setoid {G : 𝒮 ⥤ 𝒯 // G ⋙ q = p} where
  r G H := ∃ e : G.1 ≅ H.1, ∀ x : 𝒮, q.IsHomLift (𝟙 (p.obj x)) (e.hom.app x)
  iseqv :=
  { refl G := ⟨Iso.refl _, fun x => IsHomLift.id (Functor.congr_obj G.2 x)⟩
    symm := fun ⟨e, he⟩ => ⟨e.symm, fun x =>
      @IsHomLift.lift_id_inv _ _ _ _ q _ _ _ (e.app x) (he x)⟩
    trans := fun ⟨e, he⟩ ⟨e', he'⟩ => ⟨e.trans e', fun x =>
      isHomLift_id_comp q (e.hom.app x) (e'.hom.app x) (he x) (he' x)⟩ }

variable (p : 𝒮 ⥤ 𝒞) (q : 𝒯 ⥤ 𝒞) [hp : p.IsFiberedInSetoids] [hq : q.IsFiberedInSetoids]

omit hp hq in
/-- At an object of an arbitrary fibre, 2-isomorphic 1-morphisms have the same image class. -/
lemma isoClassMk_fiberFunctorOfCompEq_eq_of_twoIso {G H : 𝒮 ⥤ 𝒯} (hG : G ⋙ q = p)
    (hH : H ⋙ q = p) (e : G ≅ H) (he : ∀ x : 𝒮, q.IsHomLift (𝟙 (p.obj x)) (e.hom.app x))
    {U : 𝒞} (x : p.Fiber U) :
    isoClassMk q ((fiberFunctorOfCompEq hG U).obj x)
      = isoClassMk q ((fiberFunctorOfCompEq hH U).obj x) := by
  obtain ⟨a, rfl⟩ := x
  exact isoClassMk_eq_of_iso (Fiber.isoMk (e.app a) (he a))

/-- 2-isomorphic 1-morphisms induce the same map on the presheaves of isomorphism classes. -/
lemma isoClassMapOfCompEq_eq_of_twoIso {G H : {G : 𝒮 ⥤ 𝒯 // G ⋙ q = p}}
    (h : (twoIsoSetoid p q).r G H) : isoClassMapOfCompEq G.2 = isoClassMapOfCompEq H.2 := by
  obtain ⟨e, he⟩ := h
  exact isoClassPresheaf_hom_ext fun x =>
    isoClassMk_fiberFunctorOfCompEq_eq_of_twoIso p q G.2 H.2 e he x

/-- **Stacks 04SC**, final form: for categories `𝒮₁`, `𝒮₂` fibred in setoids over `𝒞`,
`Mor_{Cat/𝒞}(𝒮₁, 𝒮₂)` modulo 2-isomorphism is `Mor_{PSh(𝒞)}(F₁, F₂)`, where `F_i(U)` is the set of
isomorphism classes of objects of the fibre of `𝒮_i` over `U`. The forward map sends a 1-morphism
to the induced map of presheaves; it is surjective by Stacks 04SC (2) and injective by
Stacks 04SC (1). -/
@[stacks 04SC "The bijection `Mor(𝒮₁, 𝒮₂)/2-isomorphism = Mor_{PSh}(F₁, F₂)`."]
noncomputable def isoClassMapEquiv :
    _root_.Quotient (twoIsoSetoid p q) ≃ (p.isoClassPresheaf ⟶ q.isoClassPresheaf) where
  toFun := _root_.Quotient.lift (fun G => isoClassMapOfCompEq G.2) fun _ _ h =>
    isoClassMapOfCompEq_eq_of_twoIso p q h
  invFun φ := _root_.Quotient.mk _ ⟨isoClassLiftFunctor φ, isoClassLiftFunctor_comp_eq φ⟩
  left_inv := by
    intro G
    induction G using _root_.Quotient.ind with
    | _ G =>
      exact _root_.Quotient.sound (existsUnique_twoIso_of_isoClassMap_eq
        (isoClassLiftFunctor_comp_eq (isoClassMapOfCompEq G.2)) G.2
        (isoClassMapOfCompEq_isoClassLiftFunctor (isoClassMapOfCompEq G.2))).exists
  right_inv φ := isoClassMapOfCompEq_isoClassLiftFunctor φ

end Equiv

/-! ## Stacks 04SC (3): a category fibred in sets is its own image under `F` -/

section FiberedInSets

variable {𝒮 : Type u₂} [Category.{v₂} 𝒮] (p : 𝒮 ⥤ 𝒞) [p.IsFibered]

/-- For a category fibred in sets the canonical surjection `Ob(𝒮_U) → Ob(𝒮_U)/≅` is a bijection:
the fibre is discrete, so isomorphic objects of it are equal. A category fibred in sets is a
category fibred in groupoids all of whose fibre categories are discrete (Stacks 0043), and the
hypothesis here is supplied by `CategoryTheory.Functor.IsFiberedInSets.fiber_isDiscrete`. -/
noncomputable def isoClassMkEquiv (U : 𝒞) (hd : IsDiscrete (p.Fiber U)) :
    p.Fiber U ≃ p.isoClassPresheaf.obj (op U) where
  toFun := isoClassMk p
  invFun := _root_.Quotient.out
  left_inv x :=
    obj_ext_of_isDiscrete
      (exists_iso_of_isoClassMk_eq (_root_.Quotient.out_eq (isoClassMk p x))).some.hom
  right_inv := _root_.Quotient.out_eq

/-- The presheaf `U ↦ Ob(𝒮_U)` of objects of the fibres of a category fibred in sets, which is the
presheaf that Stacks 02Y2 attaches to a category fibred in sets. It is strictly functorial because
a chosen pullback is *the* pullback when the fibres are discrete: the canonical isomorphisms
`(𝟙 U)^* x ≅ x` and `g^* f^* x ≅ (f ∘ g)^* x` become equalities. -/
noncomputable def fiberPresheaf (hd : ∀ U : 𝒞, IsDiscrete (p.Fiber U)) : 𝒞ᵒᵖ ⥤ Type u₂ where
  obj U := p.Fiber U.unop
  map {_ _} f := ↾fun x => pullbackFiber p x f.unop
  map_id U := by
    ext x
    have := hd U.unop
    exact obj_ext_of_isDiscrete (pullbackFiberIdIso x).hom
  map_comp {_ _ W} f g := by
    ext x
    have := hd W.unop
    exact (obj_ext_of_isDiscrete (pullbackFiberCompIso x f.unop g.unop).hom).symm

/-- **Stacks 04SC (3).** A category fibred in sets `𝒮` is equal to `F(𝒮)`: the presheaf of
isomorphism classes of the fibres of `𝒮` is the presheaf `U ↦ Ob(𝒮_U)` of objects of the fibres,
which is the presheaf that Stacks 02Y2 attaches to `𝒮`. The isomorphism is the quotient map at
each `U`, a bijection because the fibres are discrete, and it is natural because on both sides the
restriction along `f : V ⟶ U` is `x ↦ f^* x`. -/
@[stacks 04SC "(3): for a category fibred in sets the presheaf of isomorphism classes of the fibres
is the presheaf of objects of the fibres, i.e. `𝒮 = F(𝒮)`."]
noncomputable def fiberPresheafIsoIsoClassPresheaf (hd : ∀ U : 𝒞, IsDiscrete (p.Fiber U)) :
    p.fiberPresheaf hd ≅ p.isoClassPresheaf :=
  NatIso.ofComponents (fun U => Equiv.toIso (isoClassMkEquiv p U.unop (hd U.unop)))
    fun {_ _} _ => rfl

end FiberedInSets

/-! ## Stacks 04SD: the construction is compatible with 2-fibre products -/

section TwoFibreProduct

variable {𝒳 𝒴 𝒵 : Type u₂} [Category.{v₁} 𝒳] [Category.{v₁} 𝒴] [Category.{v₁} 𝒵]
  (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (p𝒵 : 𝒵 ⥤ 𝒞) (F : 𝒳 ⥤ 𝒵) (G : 𝒴 ⥤ 𝒵)

/-- The first projection of the 2-fibre product `𝒳 ×_𝒵 𝒴` is strictly over `𝒞`, with the five
arguments named so that the universe of the 2-fibre product is determined. -/
lemma twoFibreProduct_fst_comp_eq :
    TwoFibreProductOver.fst p𝒳 p𝒴 p𝒵 F G ⋙ p𝒳
      = TwoFibreProductOver.structureFunctor p𝒳 p𝒴 p𝒵 F G :=
  TwoFibreProductOver.fst_comp_eq

/-- The second projection of the 2-fibre product `𝒳 ×_𝒵 𝒴` is strictly over `𝒞`. -/
lemma twoFibreProduct_snd_comp_eq :
    TwoFibreProductOver.snd p𝒳 p𝒴 p𝒵 F G ⋙ p𝒴
      = TwoFibreProductOver.structureFunctor p𝒳 p𝒴 p𝒵 F G :=
  TwoFibreProductOver.snd_comp_eq

/-- The functor from the fibre of the 2-fibre product `𝒳 ×_𝒵 𝒴` over `U` to the fibre of `𝒳`
over `U`, induced by the first projection. -/
def twoFibreProductFiberFst (U : 𝒞) :
    (TwoFibreProductOver.structureFunctor p𝒳 p𝒴 p𝒵 F G).Fiber U ⥤ p𝒳.Fiber U :=
  fiberFunctorOfCompEq (twoFibreProduct_fst_comp_eq p𝒳 p𝒴 p𝒵 F G) U

/-- The functor from the fibre of the 2-fibre product `𝒳 ×_𝒵 𝒴` over `U` to the fibre of `𝒴`
over `U`, induced by the second projection. -/
def twoFibreProductFiberSnd (U : 𝒞) :
    (TwoFibreProductOver.structureFunctor p𝒳 p𝒴 p𝒵 F G).Fiber U ⥤ p𝒴.Fiber U :=
  fiberFunctorOfCompEq (twoFibreProduct_snd_comp_eq p𝒳 p𝒴 p𝒵 F G) U

variable {p𝒳 p𝒴 p𝒵 F G}

/-- The comparison isomorphism of an object of the fibre of the 2-fibre product over `U` is
vertical over `U`. -/
lemma isHomLift_iso_twoFibreProductFiber {U : 𝒞}
    (P : (TwoFibreProductOver.structureFunctor p𝒳 p𝒴 p𝒵 F G).Fiber U) :
    p𝒵.IsHomLift (𝟙 U) P.1.iso.hom := by
  obtain ⟨P, rfl⟩ := P
  exact P.vertical

section

variable [hp𝒵 : p𝒵.IsFiberedInSetoids]
  (hF : IsFibredOneMorphism p𝒳 p𝒵 F) (hG : IsFibredOneMorphism p𝒴 p𝒵 G)

omit hp𝒵 in
/-- The base compatibility condition of `CategoryTheory.TwoFibreProductOver.Hom.mk'` for a pair of
morphisms of the component fibres over `U`: both induce the same morphism of `𝒞`, since both lie
over `𝟙 U`. -/
lemma twoFibreProduct_hbase_compat {U : 𝒞}
    {A B : (TwoFibreProductOver.structureFunctor p𝒳 p𝒴 p𝒵 F G).Fiber U}
    (γ : (twoFibreProductFiberFst p𝒳 p𝒴 p𝒵 F G U).obj A ⟶
      (twoFibreProductFiberFst p𝒳 p𝒴 p𝒵 F G U).obj B)
    (δ : (twoFibreProductFiberSnd p𝒳 p𝒴 p𝒵 F G U).obj A ⟶
      (twoFibreProductFiberSnd p𝒳 p𝒴 p𝒵 F G U).obj B) :
    eqToHom A.1.hy.symm ≫ p𝒴.map (Fiber.fiberInclusion.map δ) ≫ eqToHom B.1.hy
      = eqToHom A.1.hx.symm ≫ p𝒳.map (Fiber.fiberInclusion.map γ) ≫ eqToHom B.1.hx :=
  (eqToHom_comp_map_comp_eqToHom p𝒴 (Fiber.fiberInclusion.map δ) δ.2 A.1.hy B.1.hy
      (A.2.trans B.2.symm)).trans
    (eqToHom_comp_map_comp_eqToHom p𝒳 (Fiber.fiberInclusion.map γ) γ.2 A.1.hx B.1.hx
      (A.2.trans B.2.symm)).symm

include hF hG in
/-- The comparison square of `CategoryTheory.TwoFibreProductOver.Hom.mk'` commutes automatically
for a pair of morphisms of the component fibres over `U`: both of its sides are morphisms of `𝒵`
lying over `𝟙 U` between the same objects, and there is at most one such because `𝒵` is fibred in
setoids. The source notes that Stacks 04SD is false without this hypothesis. -/
lemma twoFibreProduct_square {U : 𝒞}
    {A B : (TwoFibreProductOver.structureFunctor p𝒳 p𝒴 p𝒵 F G).Fiber U}
    (γ : (twoFibreProductFiberFst p𝒳 p𝒴 p𝒵 F G U).obj A ⟶
      (twoFibreProductFiberFst p𝒳 p𝒴 p𝒵 F G U).obj B)
    (δ : (twoFibreProductFiberSnd p𝒳 p𝒴 p𝒵 F G U).obj A ⟶
      (twoFibreProductFiberSnd p𝒳 p𝒴 p𝒵 F G U).obj B) :
    F.map (Fiber.fiberInclusion.map γ) ≫ B.1.iso.hom
      = A.1.iso.hom ≫ G.map (Fiber.fiberInclusion.map δ) := by
  refine hom_unique_of_fiber_isThin p𝒵 (𝟙 U) (hp𝒵.fiber_isThin U) _ _ ?_ ?_
  · exact isHomLift_id_comp p𝒵 _ _
      (isHomLift_map_of_comp_eq' hF.comp_eq (𝟙 U) (Fiber.fiberInclusion.map γ) γ.2)
      (isHomLift_iso_twoFibreProductFiber B)
  · exact isHomLift_id_comp p𝒵 _ _ (isHomLift_iso_twoFibreProductFiber A)
      (isHomLift_map_of_comp_eq' hG.comp_eq (𝟙 U) (Fiber.fiberInclusion.map δ) δ.2)

include hF hG in
/-- The morphism of the fibre of the 2-fibre product over `U` determined by a pair of morphisms of
the component fibres. Because `𝒵` is fibred in setoids there is no further condition to impose:
the comparison square commutes automatically. -/
def twoFibreProductFiberHomMk {U : 𝒞}
    {A B : (TwoFibreProductOver.structureFunctor p𝒳 p𝒴 p𝒵 F G).Fiber U}
    (γ : (twoFibreProductFiberFst p𝒳 p𝒴 p𝒵 F G U).obj A ⟶
      (twoFibreProductFiberFst p𝒳 p𝒴 p𝒵 F G U).obj B)
    (δ : (twoFibreProductFiberSnd p𝒳 p𝒴 p𝒵 F G U).obj A ⟶
      (twoFibreProductFiberSnd p𝒳 p𝒴 p𝒵 F G U).obj B) : A ⟶ B :=
  ⟨TwoFibreProductOver.Hom.mk' (Fiber.fiberInclusion.map γ) (Fiber.fiberInclusion.map δ)
      (twoFibreProduct_hbase_compat γ δ) (twoFibreProduct_square hF hG γ δ), by
    refine IsHomLift.of_fac' (TwoFibreProductOver.structureFunctor p𝒳 p𝒴 p𝒵 F G) (𝟙 U) _
      A.2 B.2 ?_
    change eqToHom A.1.hx.symm ≫ p𝒳.map (Fiber.fiberInclusion.map γ) ≫ eqToHom B.1.hx
      = eqToHom A.2 ≫ 𝟙 U ≫ eqToHom B.2.symm
    refine Eq.trans (eqToHom_comp_map_comp_eqToHom p𝒳 (Fiber.fiberInclusion.map γ) γ.2
      A.1.hx B.1.hx (A.2.trans B.2.symm)) ?_
    simp only [Category.id_comp, eqToHom_trans]
    rfl⟩

include hF hG in
/-- The `𝒳`-component of `CategoryTheory.Functor.twoFibreProductFiberHomMk hF hG γ δ` is `γ`. -/
@[simp]
lemma fiberInclusion_map_twoFibreProductFiberHomMk_a {U : 𝒞}
    {A B : (TwoFibreProductOver.structureFunctor p𝒳 p𝒴 p𝒵 F G).Fiber U}
    (γ : (twoFibreProductFiberFst p𝒳 p𝒴 p𝒵 F G U).obj A ⟶
      (twoFibreProductFiberFst p𝒳 p𝒴 p𝒵 F G U).obj B)
    (δ : (twoFibreProductFiberSnd p𝒳 p𝒴 p𝒵 F G U).obj A ⟶
      (twoFibreProductFiberSnd p𝒳 p𝒴 p𝒵 F G U).obj B) :
    (Fiber.fiberInclusion.map (twoFibreProductFiberHomMk hF hG γ δ)).a
      = Fiber.fiberInclusion.map γ :=
  rfl

include hF hG in
/-- The `𝒴`-component of `CategoryTheory.Functor.twoFibreProductFiberHomMk hF hG γ δ` is `δ`. -/
@[simp]
lemma fiberInclusion_map_twoFibreProductFiberHomMk_b {U : 𝒞}
    {A B : (TwoFibreProductOver.structureFunctor p𝒳 p𝒴 p𝒵 F G).Fiber U}
    (γ : (twoFibreProductFiberFst p𝒳 p𝒴 p𝒵 F G U).obj A ⟶
      (twoFibreProductFiberFst p𝒳 p𝒴 p𝒵 F G U).obj B)
    (δ : (twoFibreProductFiberSnd p𝒳 p𝒴 p𝒵 F G U).obj A ⟶
      (twoFibreProductFiberSnd p𝒳 p𝒴 p𝒵 F G U).obj B) :
    (Fiber.fiberInclusion.map (twoFibreProductFiberHomMk hF hG γ δ)).b
      = Fiber.fiberInclusion.map δ :=
  rfl

include hF hG in
/-- The construction of `CategoryTheory.Functor.twoFibreProductFiberHomMk` is compatible with
composition, hence carries a pair of isomorphisms to an isomorphism. -/
lemma twoFibreProductFiberHomMk_comp {U : 𝒞}
    {A B C : (TwoFibreProductOver.structureFunctor p𝒳 p𝒴 p𝒵 F G).Fiber U}
    (γ : (twoFibreProductFiberFst p𝒳 p𝒴 p𝒵 F G U).obj A ⟶
      (twoFibreProductFiberFst p𝒳 p𝒴 p𝒵 F G U).obj B)
    (δ : (twoFibreProductFiberSnd p𝒳 p𝒴 p𝒵 F G U).obj A ⟶
      (twoFibreProductFiberSnd p𝒳 p𝒴 p𝒵 F G U).obj B)
    (γ' : (twoFibreProductFiberFst p𝒳 p𝒴 p𝒵 F G U).obj B ⟶
      (twoFibreProductFiberFst p𝒳 p𝒴 p𝒵 F G U).obj C)
    (δ' : (twoFibreProductFiberSnd p𝒳 p𝒴 p𝒵 F G U).obj B ⟶
      (twoFibreProductFiberSnd p𝒳 p𝒴 p𝒵 F G U).obj C) :
    twoFibreProductFiberHomMk hF hG γ δ ≫ twoFibreProductFiberHomMk hF hG γ' δ'
      = twoFibreProductFiberHomMk hF hG (γ ≫ γ') (δ ≫ δ') :=
  Fiber.hom_ext (TwoFibreProductOver.Hom.ext' rfl rfl)

include hF hG in
/-- `CategoryTheory.Functor.twoFibreProductFiberHomMk` of the identities is the identity. -/
lemma twoFibreProductFiberHomMk_id {U : 𝒞}
    (A : (TwoFibreProductOver.structureFunctor p𝒳 p𝒴 p𝒵 F G).Fiber U) :
    twoFibreProductFiberHomMk hF hG (𝟙 ((twoFibreProductFiberFst p𝒳 p𝒴 p𝒵 F G U).obj A))
      (𝟙 ((twoFibreProductFiberSnd p𝒳 p𝒴 p𝒵 F G U).obj A)) = 𝟙 A :=
  Fiber.hom_ext (TwoFibreProductOver.Hom.ext' rfl rfl)

include hF hG in
/-- Two objects of the fibre of the 2-fibre product over `U` whose components are isomorphic in
the fibres of `𝒳` and of `𝒴` are themselves isomorphic. This is the injectivity half of
Stacks 04SD. -/
lemma exists_iso_of_twoFibreProduct_components {U : 𝒞}
    {A B : (TwoFibreProductOver.structureFunctor p𝒳 p𝒴 p𝒵 F G).Fiber U}
    (α : (twoFibreProductFiberFst p𝒳 p𝒴 p𝒵 F G U).obj A ≅
      (twoFibreProductFiberFst p𝒳 p𝒴 p𝒵 F G U).obj B)
    (β : (twoFibreProductFiberSnd p𝒳 p𝒴 p𝒵 F G U).obj A ≅
      (twoFibreProductFiberSnd p𝒳 p𝒴 p𝒵 F G U).obj B) : Nonempty (A ≅ B) :=
  ⟨{ hom := twoFibreProductFiberHomMk hF hG α.hom β.hom
     inv := twoFibreProductFiberHomMk hF hG α.inv β.inv
     hom_inv_id := by
       rw [twoFibreProductFiberHomMk_comp, α.hom_inv_id, β.hom_inv_id,
         twoFibreProductFiberHomMk_id]
     inv_hom_id := by
       rw [twoFibreProductFiberHomMk_comp, α.inv_hom_id, β.inv_hom_id,
         twoFibreProductFiberHomMk_id] }⟩

end

section

variable [p𝒳.IsFibered] [p𝒴.IsFibered] [hp𝒵 : p𝒵.IsFiberedInSetoids]
  (hF : IsFibredOneMorphism p𝒳 p𝒵 F) (hG : IsFibredOneMorphism p𝒴 p𝒵 G)

/-- The two components of an object of the fibre of the 2-fibre product over `U` have the same
image in `Ob(𝒵_U)/≅`: the comparison isomorphism of the object is an isomorphism of the fibre
over `U` between their images. -/
lemma isoClassMk_twoFibreProduct_compat {U : 𝒞}
    (P : (TwoFibreProductOver.structureFunctor p𝒳 p𝒴 p𝒵 F G).Fiber U) :
    (isoClassMap hF).app (op U) (isoClassMk p𝒳 ((twoFibreProductFiberFst p𝒳 p𝒴 p𝒵 F G U).obj P))
      = (isoClassMap hG).app (op U)
        (isoClassMk p𝒴 ((twoFibreProductFiberSnd p𝒳 p𝒴 p𝒵 F G U).obj P)) :=
  isoClassMk_eq_of_iso (Fiber.isoMk P.1.iso (isHomLift_iso_twoFibreProductFiber P))

/-- The map of Stacks 04SD at `U`: the isomorphism class of an object of the fibre of the
2-fibre product `𝒳 ×_𝒵 𝒴` over `U` goes to the pair of the isomorphism classes of its two
components, which have the same image in `Ob(𝒵_U)/≅`. -/
def twoFibreProductIsoClassMap (U : 𝒞) :
    _root_.Quotient
        (isIsomorphicSetoid
          ((TwoFibreProductOver.structureFunctor p𝒳 p𝒴 p𝒵 F G).Fiber U)) →
      {ab : _root_.Quotient (isIsomorphicSetoid (p𝒳.Fiber U)) ×
            _root_.Quotient (isIsomorphicSetoid (p𝒴.Fiber U)) //
          (isoClassMap hF).app (op U) ab.1 = (isoClassMap hG).app (op U) ab.2} :=
  fun c => _root_.Quotient.liftOn c
    (fun P => ⟨(isoClassMk p𝒳 ((twoFibreProductFiberFst p𝒳 p𝒴 p𝒵 F G U).obj P),
        isoClassMk p𝒴 ((twoFibreProductFiberSnd p𝒳 p𝒴 p𝒵 F G U).obj P)),
      isoClassMk_twoFibreProduct_compat hF hG P⟩)
    (fun _ _ h => by
      refine Subtype.ext (Prod.ext ?_ ?_)
      · exact isoClassMk_eq_of_iso ((twoFibreProductFiberFst p𝒳 p𝒴 p𝒵 F G U).mapIso
          ((isIsomorphicSetoid_r_iff _ _).1 h).some)
      · exact isoClassMk_eq_of_iso ((twoFibreProductFiberSnd p𝒳 p𝒴 p𝒵 F G U).mapIso
          ((isIsomorphicSetoid_r_iff _ _).1 h).some))

/-- **Stacks 04SD**, injectivity. -/
lemma twoFibreProductIsoClassMap_injective (U : 𝒞) :
    Function.Injective (twoFibreProductIsoClassMap hF hG U) := by
  intro c c' h
  induction c using _root_.Quotient.ind with
  | _ P =>
    induction c' using _root_.Quotient.ind with
    | _ Q =>
      obtain ⟨α⟩ := exists_iso_of_isoClassMk_eq (congrArg (fun z => z.val.fst) h)
      obtain ⟨β⟩ := exists_iso_of_isoClassMk_eq (congrArg (fun z => z.val.snd) h)
      obtain ⟨e⟩ := exists_iso_of_twoFibreProduct_components hF hG α β
      exact isoClassMk_eq_of_iso e

/-- **Stacks 04SD**, surjectivity: a pair of isomorphism classes with the same image in
`Ob(𝒵_U)/≅` is the pair of components of an object of the 2-fibre product, built from a chosen
vertical isomorphism between chosen representatives. -/
lemma twoFibreProductIsoClassMap_surjective (U : 𝒞) :
    Function.Surjective (twoFibreProductIsoClassMap hF hG U) := by
  rintro ⟨⟨c₁, c₂⟩, hc⟩
  obtain ⟨x, rfl⟩ := isoClassMk_surjective c₁
  obtain ⟨y, rfl⟩ := isoClassMk_surjective c₂
  obtain ⟨e⟩ := exists_iso_of_isoClassMk_eq hc
  refine ⟨isoClassMk _ ⟨TwoFibreProductOver.mk U x.1 y.1 x.2 y.2
    (Fiber.fiberInclusion.mapIso e) e.hom.2, rfl⟩, ?_⟩
  exact Subtype.ext (Prod.ext (congrArg (isoClassMk p𝒳) (Subtype.ext rfl))
    (congrArg (isoClassMk p𝒴) (Subtype.ext rfl)))

/-- **Stacks 04SD.** The presheaf attached by Stacks 04SC to a 2-fibre product `𝒳 ×_𝒵 𝒴` over `𝒞`
is the fibre product of the presheaves attached to `𝒳`, `𝒴` and `𝒵`: at every object `U` of `𝒞`,
`Ob((𝒳 ×_𝒵 𝒴)_U)/≅ = Ob(𝒳_U)/≅ ×_{Ob(𝒵_U)/≅} Ob(𝒴_U)/≅`, by the bijection sending the class of
an object to the pair of the classes of its components. This is the display to which the source's
proof reduces the lemma. -/
@[stacks 04SD]
noncomputable def twoFibreProductIsoClassEquiv (U : 𝒞) :
    _root_.Quotient
        (isIsomorphicSetoid
          ((TwoFibreProductOver.structureFunctor p𝒳 p𝒴 p𝒵 F G).Fiber U)) ≃
      {ab : _root_.Quotient (isIsomorphicSetoid (p𝒳.Fiber U)) ×
            _root_.Quotient (isIsomorphicSetoid (p𝒴.Fiber U)) //
          (isoClassMap hF).app (op U) ab.1 = (isoClassMap hG).app (op U) ab.2} :=
  Equiv.ofBijective _
    ⟨twoFibreProductIsoClassMap_injective hF hG U,
      twoFibreProductIsoClassMap_surjective hF hG U⟩

/-- **Stacks 04SD**, naturality: the bijection of
`CategoryTheory.Functor.twoFibreProductIsoClassEquiv` commutes with restriction along a morphism
of `𝒞`, so it is an isomorphism of presheaves and not merely a family of bijections. -/
@[stacks 04SD "Naturality: the bijection is an isomorphism of presheaves."]
lemma twoFibreProductIsoClassMap_naturality
    [(TwoFibreProductOver.structureFunctor p𝒳 p𝒴 p𝒵 F G).IsFibered] {V U : 𝒞} (f : V ⟶ U)
    (c : (TwoFibreProductOver.structureFunctor p𝒳 p𝒴 p𝒵 F G).isoClassPresheaf.obj (op U)) :
    (twoFibreProductIsoClassMap hF hG V
        ((TwoFibreProductOver.structureFunctor p𝒳 p𝒴 p𝒵 F G).isoClassPresheaf.map f.op c)).val =
      (p𝒳.isoClassPresheaf.map f.op (twoFibreProductIsoClassMap hF hG U c).val.fst,
        p𝒴.isoClassPresheaf.map f.op (twoFibreProductIsoClassMap hF hG U c).val.snd) := by
  induction c using _root_.Quotient.ind with
  | _ P =>
    refine Prod.ext ?_ ?_
    · exact (isoClassMk_eq_of_iso
        ((TwoFibreProductOver.fst_isFibredOneMorphism p𝒳 p𝒴 p𝒵 F G hF
          hG).mapPullbackFiberIso P f)).symm
    · exact (isoClassMk_eq_of_iso
        ((TwoFibreProductOver.snd_isFibredOneMorphism p𝒳 p𝒴 p𝒵 F G hF
          hG).mapPullbackFiberIso P f)).symm

end

end TwoFibreProduct

end CategoryTheory.Functor
