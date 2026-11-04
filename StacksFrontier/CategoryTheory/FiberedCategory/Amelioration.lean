module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import StacksFrontier.CategoryTheory.FiberedCategory.HomLift
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.FibredOneMorphism

/-!
# The amelioration of a 1-morphism of fibred categories (Stacks 08NF)

Let `C` be a category and let `F : X ⥤ Y` be a 1-morphism of fibred categories over `C`,
with structure functors `p : X ⥤ C` and `q : Y ⥤ C`. Then there exist a fibred category
`(X', p'')` over `C` and three 1-morphisms of fibred categories over `C`

  `u : X ⥤ X'`,  `v : X' ⥤ Y`,  `w : X' ⥤ X`,

with `F = u ⋙ v`, such that `u` is fully faithful, `w` is left adjoint to `u`, and `v`
exhibits `X'` as a fibred category over `Y`. The witness is the *amelioration* of `F`: an
object is a quadruple `(U, x, y, f)` with `U = p x = q y` and `f : y ⟶ F x` a morphism of `Y`
lying over `id_U`, and a morphism is a pair `(a, b)` of morphisms of `X` and `Y` lying over a
common morphism of `C` and making the evident square commute.

## Modelling conventions

A *category over `C`* is a functor `p : X ⥤ C`, its structure functor. A *fibred category
over `C`* is such a functor satisfying `p.IsFibered`, equivalently the existence, for every
object `x` over `U = p x` and every `f : V ⟶ U`, of a strongly cartesian lift of `f` with
target `x` (Stacks 02XM, `Functor.IsFibered.of_exists_isStronglyCartesian`). A *strongly
cartesian morphism* is `p.IsStronglyCartesian f φ`, whose `universal_property` is the unique
factorization of the Stacks definition. *Fully faithful* is `Functor.FullyFaithful` and
*left adjoint* is `CategoryTheory.Adjunction` (`w ⊣ u`). A *1-morphism of fibred categories
over `C`* is `Functor.IsFibredOneMorphism`: a functor strictly over `C` which preserves
strongly cartesian morphisms.

## Universe note

An object of `X'` carries a morphism of `Y`, hence lives in the hom universe `v₃` of `Y`; so
the object type of `X'` lives in a universe involving the hom universes as well as the object
universes. To avoid imposing any unintended smallness restriction the existential is stated
at the sufficiently large universe `max u₁ u₂ u₃ v₁ v₂ v₃`, which accommodates the intended
construction for all hom universes. The construction itself is carried out in the universe
`max u₂ u₃ v₃` and transported at the end along a universe-lifting equivalence.
-/
@[expose] public section

open CategoryTheory

namespace CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃


/-! ## Transfer along an equivalence

Both the fibredness of a structure functor and the property of being a 1-morphism of fibred
categories are transported along an equivalence of categories; this is what makes the universe
lift at the end of the file possible. -/

section Transfer

variable {𝒮 : Type*} [Category 𝒮] {𝒯 : Type*} [Category 𝒯] {𝒵 : Type*} [Category 𝒵]

/-- An equivalence of categories transports strongly cartesian morphisms along the structure
functor. Let `e : 𝒮 ≌ 𝒯`, let `r : 𝒯 ⥤ 𝒵` be a structure functor whose restriction along
`e.functor` is `r₀ : 𝒮 ⥤ 𝒵`, and let `ψ` be strongly cartesian over `f` for `r₀`. Then
`e.functor.map ψ` is strongly cartesian over `f` for `r`: a test morphism into
`e.functor.obj b` is carried back to `𝒮` by the counit isomorphism and the fully faithfulness
of `e.functor`, factored uniquely there, and the factorization carried forward again. Applied
to `e` this transports forwards, applied to `e.symm` backwards. -/
lemma Equivalence.isStronglyCartesian_map_functor (e : 𝒮 ≌ 𝒯) (r : 𝒯 ⥤ 𝒵) {r₀ : 𝒮 ⥤ 𝒵}
    (hr : e.functor ⋙ r = r₀) {R S : 𝒵} (f : R ⟶ S) {a b : 𝒮} (ψ : a ⟶ b)
    (h : r₀.IsStronglyCartesian f ψ) : r.IsStronglyCartesian f (e.functor.map ψ) := by
  subst hr
  have : r.IsHomLift f (e.functor.map ψ) :=
    (Functor.isHomLift_comp_iff e.functor r f ψ).1 inferInstance
  refine ⟨?_⟩
  intro c g φ' hφ'
  have hφ'' : r.IsHomLift (g ≫ f) φ' := hφ'
  have i : e.functor.obj (e.inverse.obj c) ≅ c := e.counitIso.app c
  obtain ⟨φ₁, hφ₁⟩ := e.functor.map_surjective (i.hom ≫ φ')
  have hcomp : r.IsHomLift ((r.map i.hom ≫ g) ≫ f) (i.hom ≫ φ') := by
    have h₁ : r.IsHomLift (r.map i.hom ≫ g ≫ f) (i.hom ≫ φ') := inferInstance
    rwa [← Category.assoc] at h₁
  have : (e.functor ⋙ r).IsHomLift ((r.map i.hom ≫ g) ≫ f) φ₁ := by
    rwa [Functor.isHomLift_comp_iff, hφ₁]
  obtain ⟨χ₀, ⟨hχ₀lift, hχ₀fac⟩, hχ₀uniq⟩ :=
    Functor.IsStronglyCartesian.universal_property (e.functor ⋙ r) f ψ (r.map i.hom ≫ g)
      ((r.map i.hom ≫ g) ≫ f) rfl φ₁
  have : r.IsHomLift (r.map i.hom ≫ g) (e.functor.map χ₀) :=
    (Functor.isHomLift_comp_iff e.functor r _ χ₀).1 hχ₀lift
  have hcancel : r.map i.inv ≫ (r.map i.hom ≫ g) = g := by
    rw [← Category.assoc, ← r.map_comp, i.inv_hom_id, r.map_id, Category.id_comp]
  refine ⟨i.inv ≫ e.functor.map χ₀, ⟨?_, ?_⟩, ?_⟩
  · have h₂ : r.IsHomLift (r.map i.inv ≫ (r.map i.hom ≫ g)) (i.inv ≫ e.functor.map χ₀) :=
      inferInstance
    rwa [hcancel] at h₂
  · rw [Category.assoc, ← e.functor.map_comp, hχ₀fac, hφ₁, ← Category.assoc, i.inv_hom_id,
      Category.id_comp]
  · intro y ⟨hylift, hyfac⟩
    have := hylift
    obtain ⟨y₁, hy₁⟩ := e.functor.map_surjective (i.hom ≫ y)
    have hy₂ : y₁ = χ₀ := by
      refine hχ₀uniq y₁ ⟨?_, ?_⟩
      · rw [Functor.isHomLift_comp_iff, hy₁]
        exact inferInstance
      · apply e.functor.map_injective
        rw [Functor.map_comp, hy₁, hφ₁, Category.assoc, hyfac]
    calc y = i.inv ≫ i.hom ≫ y := by rw [← Category.assoc, i.inv_hom_id, Category.id_comp]
      _ = i.inv ≫ e.functor.map χ₀ := by rw [← hy₁, hy₂]

/-- Fibredness of a structure functor is transported along an equivalence of total categories: if
`r₀ : 𝒮 ⥤ 𝒵` is fibred and `e : 𝒮 ≌ 𝒯` restricts the structure functor `e.inverse ⋙ r₀` on `𝒯`
back to `r₀`, then `e.inverse ⋙ r₀` is fibred, a strongly cartesian lift being the image under
`e.functor` of one in `𝒮`. -/
@[sga "1 VI 6.2" "special case"]
lemma Functor.IsFibered.comp_equivalence_inverse (e : 𝒮 ≌ 𝒯) (r₀ : 𝒮 ⥤ 𝒵) [r₀.IsFibered]
    (hr : e.functor ⋙ (e.inverse ⋙ r₀) = r₀) (hobj : ∀ a, e.functor.obj (e.inverse.obj a) = a) :
    (e.inverse ⋙ r₀).IsFibered := by
  apply Functor.IsFibered.of_exists_isStronglyCartesian
  intro a R f
  obtain ⟨b₀, φ₀, hφ₀⟩ := Functor.IsPreFibered.exists_isCartesian' (p := r₀)
    (a := e.inverse.obj a) (f := (f : R ⟶ r₀.obj (e.inverse.obj a)))
  have h₁ : (e.inverse ⋙ r₀).IsStronglyCartesian f (e.functor.map φ₀) :=
    e.isStronglyCartesian_map_functor (e.inverse ⋙ r₀) hr
      (f : R ⟶ r₀.obj (e.inverse.obj a)) φ₀ inferInstance
  have h₂ : (e.inverse ⋙ r₀).IsHomLift (𝟙 (r₀.obj (e.inverse.obj a))) (eqToHom (hobj a)) :=
    IsHomLift.eqToHom_codomain_lift_id (hobj a) rfl
  refine ⟨e.functor.obj b₀, e.functor.map φ₀ ≫ eqToHom (hobj a), ?_⟩
  simpa using Functor.IsStronglyCartesian.comp (e.inverse ⋙ r₀)
    (f := (f : R ⟶ r₀.obj (e.inverse.obj a))) (g := 𝟙 (r₀.obj (e.inverse.obj a)))
    (φ := e.functor.map φ₀) (ψ := eqToHom (hobj a))

/-- A functor strictly over the base computes the same morphism of the base as the structure
functor: for `hr : G ⋙ r = r₀` the morphism `r.map (G.map ψ)` is `r₀.map ψ` up to the
identifications of the objects involved. -/
lemma Functor.map_map_eq_of_comp_eq {G : 𝒮 ⥤ 𝒯} (r : 𝒯 ⥤ 𝒵) {r₀ : 𝒮 ⥤ 𝒵} (hr : G ⋙ r = r₀)
    {a b : 𝒮} (ψ : a ⟶ b) : r.map (G.map ψ) =
      eqToHom (Functor.congr_obj hr a) ≫ r₀.map ψ ≫ eqToHom (Functor.congr_obj hr b).symm := by
  simpa only [Functor.comp_map, Functor.comp_obj] using Functor.congr_hom hr ψ

/-- Being strongly cartesian is unaffected by adjusting the base morphism along an equality of
its codomain. -/
lemma Functor.IsStronglyCartesian.lift_comp_eqToHom_iff (r : 𝒮 ⥤ 𝒵) {R S S' : 𝒵} {a b : 𝒮}
    (f : R ⟶ S) (ψ : a ⟶ b) (h : S = S') :
    r.IsStronglyCartesian (f ≫ eqToHom h) ψ ↔ r.IsStronglyCartesian f ψ := by
  subst h
  simp

/-- Strong cartesianness of the image under a functor over the base depends only on the base
morphism and the target: if the image under `G` of one strongly cartesian `ψ₀ : a₀ ⟶ b` over `f`
is strongly cartesian, then so is the image of every strongly cartesian `ψ : a ⟶ b` over `f`.
Indeed any two such differ by an isomorphism over the identity, which `G` preserves. -/
lemma Functor.isStronglyCartesian_map_of_isStronglyCartesian_map (G : 𝒮 ⥤ 𝒯) (r : 𝒯 ⥤ 𝒵)
    {r₀ : 𝒮 ⥤ 𝒵} (hr : G ⋙ r = r₀) {R S : 𝒵} (f : R ⟶ S) {a a₀ b : 𝒮} (ψ : a ⟶ b) (ψ₀ : a₀ ⟶ b)
    (h : r₀.IsStronglyCartesian f ψ) (h₀ : r₀.IsStronglyCartesian f ψ₀)
    (hmap : r.IsStronglyCartesian f (G.map ψ₀)) : r.IsStronglyCartesian f (G.map ψ) := by
  have hbase : f = (Iso.refl R).hom ≫ f := by simp
  let e : a ≅ a₀ := Functor.IsStronglyCartesian.domainIsoOfBaseIso r₀ hbase ψ₀ ψ
  have hfac : e.hom ≫ ψ₀ = ψ := by
    rw [Functor.IsStronglyCartesian.domainIsoOfBaseIso_hom r₀ hbase ψ₀ ψ]
    exact Functor.IsStronglyCartesian.fac r₀ f ψ₀ hbase ψ
  have hlift : r₀.IsHomLift (𝟙 R) e.hom := by
    have h' : r₀.IsHomLift (Iso.refl R).hom e.hom := inferInstance
    simpa using h'
  have : r.IsHomLift (𝟙 R) (G.map e.hom) := Functor.isHomLift_map_of_comp_eq hr (𝟙 R) e.hom
  have h₁ : r.IsStronglyCartesian (𝟙 R ≫ f) (G.map e.hom ≫ G.map ψ₀) := inferInstance
  rwa [Category.id_comp, ← G.map_comp, hfac] at h₁

end Transfer


/-! ## The explicit construction

Following Stacks 08NF, the witness category has as objects the quadruples `(U, x, y, f)` and
as morphisms the compatible pairs `(a, b)`. It is built as `Amelioration p q F hFq` in the
universe `max u₂ u₃ v₃` and lifted to the required large universe at the very end. -/


section Construction

variable {C : Type u₁} [Category.{v₁} C]
variable {X : Type u₂} [Category.{v₂} X]
variable {Y : Type u₃} [Category.{v₃} Y]
variable {p : X ⥤ C} {q : Y ⥤ C} {F : X ⥤ Y}

/-- An object of `X'`: an object `x` of `X`, an object `y` of `Y` over the same base
`U = p x = q y`, and a morphism `f : y ⟶ F x` lying over `id_U`. The over-`C` data is
packaged via the equality `hy : q y = p x` and the condition `hf` saying `q f` is the
identity (expressed with the relevant `eqToHom`s). -/
structure Amelioration (p : X ⥤ C) (q : Y ⥤ C) (F : X ⥤ Y) (hFq : F ⋙ q = p) where
  /-- The object `x` of `X`. -/
  x : X
  /-- The object `y` of `Y`. -/
  y : Y
  /-- `y` and `x` lie over the same object of `C`. -/
  hy : q.obj y = p.obj x
  /-- The morphism `f : y ⟶ F x` of `Y`. -/
  f : y ⟶ F.obj x
  /-- `f` lies over the identity of `p x`. -/
  hf : q.map f = eqToHom hy ≫ eqToHom (by rw [← hFq]; rfl : p.obj x = q.obj (F.obj x))

variable {hFq : F ⋙ q = p}

namespace Amelioration

/-- A morphism `(a, b) : (U,x,y,f) ⟶ (U',x',y',f')` of `X'`: morphisms `a : x ⟶ x'`,
`b : y ⟶ y'` with `p a = q b` over `C` (the `hpq` condition, expressed with `eqToHom`s)
and the compatibility square `b ≫ f' = f ≫ F a` (the `sq` condition). -/
@[ext]
structure Hom (o o' : Amelioration p q F hFq) where
  /-- The `X`-component `a : x ⟶ x'`. -/
  a : o.x ⟶ o'.x
  /-- The `Y`-component `b : y ⟶ y'`. -/
  b : o.y ⟶ o'.y
  /-- `a` and `b` induce the same morphism of `C`. -/
  hpq : q.map b = eqToHom o.hy ≫ p.map a ≫ eqToHom o'.hy.symm
  /-- The compatibility square `b ≫ f' = f ≫ F a`. -/
  sq : b ≫ o'.f = o.f ≫ F.map a

/-- The category structure on `Amelioration`, with componentwise identities and
composition; the `hpq` and `sq` conditions are stable under both. -/
instance : Category (Amelioration p q F hFq) where
  Hom := Hom
  id o := { a := 𝟙 _, b := 𝟙 _, hpq := by simp, sq := by simp }
  comp {o o' o''} g g' :=
    { a := g.a ≫ g'.a
      b := g.b ≫ g'.b
      hpq := by
        rw [Functor.map_comp, Functor.map_comp, g.hpq, g'.hpq]
        simp
      sq := by rw [Category.assoc, g'.sq, ← Category.assoc, g.sq, Category.assoc, ← F.map_comp] }
  id_comp _ := by ext <;> simp
  comp_id _ := by ext <;> simp
  assoc _ _ _ := by ext <;> simp

/-- A morphism of `Amelioration` is determined by its two components. -/
@[ext] lemma hom_ext {o o' : Amelioration p q F hFq} (g g' : o ⟶ o') (ha : g.a = g'.a)
    (hb : g.b = g'.b) : g = g' := Hom.ext ha hb
/-- The `X`-component of an identity morphism is an identity. -/
@[simp] lemma id_a (o : Amelioration p q F hFq) : (𝟙 o : Hom o o).a = 𝟙 o.x := rfl
/-- The `Y`-component of an identity morphism is an identity. -/
@[simp] lemma id_b (o : Amelioration p q F hFq) : (𝟙 o : Hom o o).b = 𝟙 o.y := rfl
/-- Composition is computed on `X`-components by composing them. -/
@[simp] lemma comp_a {o o' o'' : Amelioration p q F hFq} (g : o ⟶ o') (g' : o' ⟶ o'') :
    (g ≫ g').a = g.a ≫ g'.a := rfl
/-- Composition is computed on `Y`-components by composing them. -/
@[simp] lemma comp_b {o o' o'' : Amelioration p q F hFq} (g : o ⟶ o') (g' : o' ⟶ o'') :
    (g ≫ g').b = g.b ≫ g'.b := rfl

/-- The structure functor `p'' : X' ⥤ C`, `(U,x,y,f) ↦ U` and `(a,b) ↦ p a`. -/
@[simps, implicit_reducible]
def structureFunctor (p : X ⥤ C) (q : Y ⥤ C) (F : X ⥤ Y) (hFq : F ⋙ q = p) :
    Amelioration p q F hFq ⥤ C where
  obj o := p.obj o.x
  map {o o'} g := p.map g.a
  map_id _ := by simp
  map_comp _ _ := by simp

/-- The functor `v : X' ⥤ Y`, `(U,x,y,f) ↦ y` and `(a,b) ↦ b`. -/
@[simps, implicit_reducible]
def proj (p : X ⥤ C) (q : Y ⥤ C) (F : X ⥤ Y) (hFq : F ⋙ q = p) :
    Amelioration p q F hFq ⥤ Y where
  obj o := o.y
  map {_ _} g := g.b
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The functor `w : X' ⥤ X`, `(U,x,y,f) ↦ x` and `(a,b) ↦ a`. -/
@[simps, implicit_reducible]
def retract (p : X ⥤ C) (q : Y ⥤ C) (F : X ⥤ Y) (hFq : F ⋙ q = p) :
    Amelioration p q F hFq ⥤ X where
  obj o := o.x
  map {_ _} g := g.a
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The functor `u : X ⥤ X'`, `x ↦ (p x, x, F x, id)` and `a ↦ (a, F a)`. -/
@[simps, implicit_reducible]
def incl (p : X ⥤ C) (q : Y ⥤ C) (F : X ⥤ Y) (hFq : F ⋙ q = p) :
    X ⥤ Amelioration p q F hFq where
  obj x := ⟨x, F.obj x, by rw [← hFq]; rfl, 𝟙 _, by simp⟩
  map {x x'} a := ⟨a, F.map a, Functor.map_map_eq_of_comp_eq q hFq a, by simp⟩
  map_id _ := by apply hom_ext <;> simp
  map_comp _ _ := by apply hom_ext <;> simp

/-! ### Factorization equalities -/


/-- `p'' = v ⋙ q`: both send `(U,x,y,f)` to the common base `U`; on objects this is `o.hy`,
on morphisms it is the `hpq` condition. -/
lemma structureFunctor_eq : structureFunctor p q F hFq = proj p q F hFq ⋙ q := by
  apply CategoryTheory.Functor.ext
  · intro o o' g
    simp only [structureFunctor_map, Functor.comp_map, proj_map]
    rw [g.hpq]
    simp
  · exact fun o => o.hy.symm

/-- `p'' = w ⋙ p`: both send `(U,x,y,f)` to the base `U` of its `X`-component and a morphism to
the image under `p` of its `X`-component. -/
lemma structureFunctor_eq_retract_comp :
    structureFunctor p q F hFq = retract p q F hFq ⋙ p := rfl

/-- `F = u ⋙ v`: `u` then `v` sends `x ↦ F x` and `a ↦ F a`, definitionally `F`. -/
lemma incl_comp_proj : F = incl p q F hFq ⋙ proj p q F hFq := by
  apply CategoryTheory.Functor.ext
  · simp
  · exact fun _ => rfl

/-! ### Reading off the components -/


/-- The morphism `f : y ⟶ F x` carried by an object of the amelioration lies over the
identification `q y = p x` of the two descriptions of its base. -/
lemma isHomLift_f (o : Amelioration p q F hFq) : q.IsHomLift (eqToHom o.hy) o.f := by
  apply IsHomLift.of_commsq q (eqToHom o.hy) o.f (a := o.y) (b := F.obj o.x)
    (R := q.obj o.y) (S := p.obj o.x) rfl (Functor.congr_obj hFq o.x)
  rw [o.hf]
  simp

/-- A morphism of the amelioration lies over a morphism of the base if and only if its
`X`-component does. -/
lemma isHomLift_iff_a {o o' : Amelioration p q F hFq} {R S : C} (g : R ⟶ S) (φ : o ⟶ o') :
    (structureFunctor p q F hFq).IsHomLift g φ ↔ p.IsHomLift g φ.a := by
  rw [structureFunctor_eq_retract_comp]
  exact Functor.isHomLift_comp_iff (retract p q F hFq) p g φ

/-- A morphism of the amelioration lies over a morphism of the base if and only if its
`Y`-component does. -/
lemma isHomLift_iff_b {o o' : Amelioration p q F hFq} {R S : C} (g : R ⟶ S) (φ : o ⟶ o') :
    (structureFunctor p q F hFq).IsHomLift g φ ↔ q.IsHomLift g φ.b := by
  rw [structureFunctor_eq]
  exact Functor.isHomLift_comp_iff (proj p q F hFq) q g φ

/-- The `hpq` condition of a morphism of the amelioration, read as a formula for the image under
`p` of its `X`-component. -/
lemma map_a_eq {o o' : Amelioration p q F hFq} (φ : o ⟶ o') :
    p.map φ.a = eqToHom o.hy.symm ≫ q.map φ.b ≫ eqToHom o'.hy := by
  rw [φ.hpq]
  simp

/-- A pair of morphisms of `X` and of `Y` lying over a common morphism of the base and making
the compatibility square commute is a morphism of the amelioration; the `hpq` condition is
automatic from the two `IsHomLift` hypotheses. -/
def homOfIsHomLift {o o' : Amelioration p q F hFq} {R S : C} (g : R ⟶ S) (a : o.x ⟶ o'.x)
    (b : o.y ⟶ o'.y) (ha : p.IsHomLift g a) (hb : q.IsHomLift g b)
    (sq : b ≫ o'.f = o.f ≫ F.map a) : o ⟶ o' where
  a := a
  b := b
  hpq := by
    rw [IsHomLift.fac' q g b, IsHomLift.fac' p g a]
    simp
  sq := sq

/-! ### The load-bearing properties of the construction -/


/-- Composing with the structural morphism `f : y ⟶ F x` of an object of the amelioration
changes the morphism of the base a morphism of `Y` lies over by the identification `q y = p x`
of the two descriptions of that base. -/
lemma isHomLift_comp_f {o : Amelioration p q F hFq} {y' : Y} (c : y' ⟶ o.y) {R : C}
    (g : R ⟶ p.obj o.x) (hc : q.IsHomLift (g ≫ eqToHom o.hy.symm) c) :
    q.IsHomLift g (c ≫ o.f) := by
  apply IsHomLift.of_commsq q g (c ≫ o.f) (a := y') (b := F.obj o.x)
    (IsHomLift.domain_eq q (g ≫ eqToHom o.hy.symm) c) (Functor.congr_obj hFq o.x)
  rw [Functor.map_comp, IsHomLift.fac' q (g ≫ eqToHom o.hy.symm) c, o.hf]
  simp

/-- The `Y`-morphism component of a lift in the amelioration. Given an object `o`, a
`p`-strongly-cartesian `α : x' ⟶ o.x` over a morphism `g` of the base and a morphism
`c : y' ⟶ o.y` of `Y` with `c ≫ o.f` over `g`, the universal property of the
`q`-strongly-cartesian morphism `F.map α` produces a morphism `y' ⟶ F x'` over the identity
factoring `c ≫ o.f` through `F.map α`. -/
lemma exists_isHomLift_id_comp_eq (hF : Functor.IsFibredOneMorphism p q F)
    (o : Amelioration p q F hFq) {R : C} {g : R ⟶ p.obj o.x} {x' : X} (α : x' ⟶ o.x)
    (hα : p.IsStronglyCartesian g α) {y' : Y} (c : y' ⟶ o.y) (hc : q.IsHomLift g (c ≫ o.f)) :
    ∃ f' : y' ⟶ F.obj x', q.IsHomLift (𝟙 R) f' ∧ f' ≫ F.map α = c ≫ o.f := by
  have := hF.map_isStronglyCartesian g α hα
  exact ⟨Functor.IsStronglyCartesian.map q g (F.map α) (g := 𝟙 R) (f' := g) (by simp) (c ≫ o.f),
    Functor.IsStronglyCartesian.map_isHomLift q g (F.map α) (by simp) (c ≫ o.f),
    Functor.IsStronglyCartesian.fac q g (F.map α) (by simp) (c ≫ o.f)⟩

/-- The compatibility square of a componentwise factorization is automatic. Let `φ : o ⟶ o'` have
`p`-strongly-cartesian `X`-component over `g`, and let a morphism `φ' : a' ⟶ o'` factor
componentwise through `φ` as `χa` and `χb`, both lying over a morphism `gbase` of the base. Then
the pair `(χa, χb)` satisfies the square condition of a morphism `a' ⟶ o`, because both sides
become the square of `φ'` after composing with the `q`-strongly-cartesian `F.map φ.a`. -/
lemma sq_of_isStronglyCartesian (hF : Functor.IsFibredOneMorphism p q F)
    {o o' a' : Amelioration p q F hFq} {R : C} {g : R ⟶ p.obj o'.x} (φ : o ⟶ o')
    (ha : p.IsStronglyCartesian g φ.a) {R' : C} {gbase : R' ⟶ R} {χa : a'.x ⟶ o.x}
    (hχa : p.IsHomLift gbase χa) {χb : a'.y ⟶ o.y} (hχb : q.IsHomLift gbase χb) (φ' : a' ⟶ o')
    (hχa_fac : χa ≫ φ.a = φ'.a) (hχb_fac : χb ≫ φ.b = φ'.b) :
    χb ≫ o.f = a'.f ≫ F.map χa := by
  have hqFox : q.obj (F.obj o.x) = R :=
    (Functor.congr_obj hFq o.x).trans (IsHomLift.domain_eq p g φ.a)
  have hay : q.obj a'.y = R' := IsHomLift.domain_eq q gbase χb
  have h₁ : q.IsHomLift gbase (χb ≫ o.f) := by
    apply IsHomLift.of_commsq q gbase (χb ≫ o.f) (a := a'.y) (b := F.obj o.x) hay hqFox
    rw [Functor.map_comp, IsHomLift.fac' q gbase χb, o.hf]
    simp
  have h₂ : q.IsHomLift gbase (a'.f ≫ F.map χa) := by
    apply IsHomLift.of_commsq q gbase (a'.f ≫ F.map χa) (a := a'.y) (b := F.obj o.x) hay hqFox
    rw [Functor.map_comp, a'.hf, Functor.map_map_eq_of_comp_eq q hFq χa,
      IsHomLift.fac' p gbase χa]
    simp
  have := hF.map_isStronglyCartesian g φ.a ha
  apply Functor.IsStronglyCartesian.ext q g (F.map φ.a) (g := gbase)
  rw [Category.assoc, ← φ.sq, ← Category.assoc, hχb_fac, Category.assoc, ← F.map_comp, hχa_fac]
  exact φ'.sq

/-- A morphism into the domain of a morphism of the amelioration with strongly cartesian
components is determined by the morphism of the base it lies over together with its composite
with that morphism: each of its two components is, by the universal property of the
corresponding component. -/
lemma hom_ext_of_isStronglyCartesian_components {o o' a' : Amelioration p q F hFq} {R : C}
    (g : R ⟶ p.obj o'.x) (φ : o ⟶ o') (ha : p.IsStronglyCartesian g φ.a)
    (hb : q.IsStronglyCartesian (g ≫ eqToHom o'.hy.symm) φ.b) {R' : C} (gbase : R' ⟶ R)
    (χ χ' : a' ⟶ o) (hχ : (structureFunctor p q F hFq).IsHomLift gbase χ)
    (hχ' : (structureFunctor p q F hFq).IsHomLift gbase χ') (h : χ ≫ φ = χ' ≫ φ) : χ = χ' := by
  have h₁ : p.IsHomLift gbase χ.a := (isHomLift_iff_a gbase χ).1 hχ
  have h₂ : p.IsHomLift gbase χ'.a := (isHomLift_iff_a gbase χ').1 hχ'
  have h₃ : q.IsHomLift gbase χ.b := (isHomLift_iff_b gbase χ).1 hχ
  have h₄ : q.IsHomLift gbase χ'.b := (isHomLift_iff_b gbase χ').1 hχ'
  apply hom_ext
  · exact Functor.IsStronglyCartesian.ext p g φ.a gbase (by rw [← comp_a, ← comp_a, h])
  · exact Functor.IsStronglyCartesian.ext q (g ≫ eqToHom o'.hy.symm) φ.b gbase
      (by rw [← comp_b, ← comp_b, h])

/-- A morphism of the amelioration whose two components are strongly cartesian is strongly
cartesian for the structure functor: the two components of a factorization are supplied by the
universal properties of the two components of `φ`, the compatibility square of the factorization
is then automatic, and it is unique because each of its components is. -/
lemma isStronglyCartesian_of_isStronglyCartesian_components
    (hF : Functor.IsFibredOneMorphism p q F) {o o' : Amelioration p q F hFq} {R : C}
    (g : R ⟶ p.obj o'.x) (φ : o ⟶ o') (ha : p.IsStronglyCartesian g φ.a)
    (hb : q.IsStronglyCartesian (g ≫ eqToHom o'.hy.symm) φ.b) :
    (structureFunctor p q F hFq).IsStronglyCartesian g φ := by
  have hφ_lift : (structureFunctor p q F hFq).IsHomLift g φ :=
    (isHomLift_iff_a g φ).2 inferInstance
  refine ⟨?_⟩
  intro a' gbase φ' hlift'
  have hφ'a : p.IsHomLift (gbase ≫ g) φ'.a := (isHomLift_iff_a (gbase ≫ g) φ').1 hlift'
  have hφ'b : q.IsHomLift (gbase ≫ g) φ'.b := (isHomLift_iff_b (gbase ≫ g) φ').1 hlift'
  have hφ'b' : q.IsHomLift ((gbase ≫ g) ≫ eqToHom o'.hy.symm) φ'.b := inferInstance
  obtain ⟨χa, ⟨hχa_lift, hχa_fac⟩, -⟩ :=
    Functor.IsStronglyCartesian.universal_property p g φ.a gbase (gbase ≫ g) rfl φ'.a
  obtain ⟨χb, ⟨hχb_lift, hχb_fac⟩, -⟩ := Functor.IsStronglyCartesian.universal_property q
    (g ≫ eqToHom o'.hy.symm) φ.b gbase _ (Category.assoc gbase g (eqToHom o'.hy.symm)) φ'.b
  let χ : a' ⟶ o := homOfIsHomLift gbase χa χb hχa_lift hχb_lift
    (sq_of_isStronglyCartesian hF φ ha hχa_lift hχb_lift φ' hχa_fac hχb_fac)
  have hχ_lift : (structureFunctor p q F hFq).IsHomLift gbase χ :=
    (isHomLift_iff_a gbase χ).2 hχa_lift
  have hχ_fac : χ ≫ φ = φ' := hom_ext _ _ hχa_fac hχb_fac
  exact ⟨χ, ⟨hχ_lift, hχ_fac⟩, fun χ' ⟨hχ'_lift, hχ'_fac⟩ =>
    hom_ext_of_isStronglyCartesian_components g φ ha hb gbase χ' χ hχ'_lift hχ_lift
      (hχ'_fac.trans hχ_fac.symm)⟩

/-- The canonical strongly cartesian lift in the amelioration. Given an object
`o = (U, x, y, f)` and a morphism `g : V ⟶ U` of `C`, choose a `p`-strongly-cartesian lift
`α : x* ⟶ x` of `g` and a `q`-strongly-cartesian lift `β : y* ⟶ y` of `g`. The universal
property of the `q`-strongly-cartesian morphism `F.map α` produces `f* : y* ⟶ F x*` making
`(α, β) : (V, x*, y*, f*) ⟶ o` a morphism of the amelioration, and that morphism is strongly
cartesian over `g` for the structure functor. Its two components are recorded as well, since
the 1-morphism properties of `v` and `w` are read off them. -/
lemma exists_isStronglyCartesian_canonical [p.IsFibered] [q.IsFibered]
    (hF : Functor.IsFibredOneMorphism p q F) (o : Amelioration p q F hFq) {R : C}
    (g : R ⟶ p.obj o.x) :
    ∃ (o' : Amelioration p q F hFq) (φ : o' ⟶ o),
      (structureFunctor p q F hFq).IsStronglyCartesian g φ ∧ p.IsStronglyCartesian g φ.a ∧
        q.IsStronglyCartesian (g ≫ eqToHom o.hy.symm) φ.b := by
  obtain ⟨xstar, α, hα⟩ := Functor.IsPreFibered.exists_isCartesian' (p := p)
    (a := o.x) (f := (g : R ⟶ p.obj o.x))
  have hαsc : p.IsStronglyCartesian (g : R ⟶ p.obj o.x) α := inferInstance
  obtain ⟨ystar, β, hβ⟩ := Functor.IsPreFibered.exists_isCartesian' (p := q)
    (a := o.y) (f := (g ≫ eqToHom o.hy.symm : R ⟶ q.obj o.y))
  have hβsc : q.IsStronglyCartesian (g ≫ eqToHom o.hy.symm : R ⟶ q.obj o.y) β := inferInstance
  have hβlift : q.IsHomLift g β :=
    (IsHomLift.lift_comp_eqToHom_iff q g β o.hy.symm).1 hβsc.toIsHomLift
  obtain ⟨fstar, hfstar_lift, hfstar_fac⟩ :=
    exists_isHomLift_id_comp_eq hF o α hαsc β (isHomLift_comp_f β g hβsc.toIsHomLift)
  let ostar : Amelioration p q F hFq :=
    { x := xstar
      y := ystar
      hy := (IsHomLift.domain_eq q (g ≫ eqToHom o.hy.symm) β).trans
        (IsHomLift.domain_eq p (g : R ⟶ p.obj o.x) α).symm
      f := fstar
      hf := by
        rw [IsHomLift.fac' q (𝟙 R) fstar]
        simp }
  let φ : ostar ⟶ o := homOfIsHomLift g α β inferInstance hβlift hfstar_fac.symm
  exact ⟨ostar, φ, isStronglyCartesian_of_isStronglyCartesian_components hF g φ hαsc hβsc,
    hαsc, hβsc⟩

/-- The amelioration is fibred over `C`: `exists_isStronglyCartesian_canonical` provides a
strongly cartesian lift of every morphism of `C` with any prescribed target. -/
lemma structureFunctor_isFibered [p.IsFibered] [q.IsFibered]
    (hF : Functor.IsFibredOneMorphism p q F) : (structureFunctor p q F hFq).IsFibered := by
  apply Functor.IsFibered.of_exists_isStronglyCartesian
  intro o R g
  obtain ⟨ostar, φ, hφ, -, -⟩ :=
    exists_isStronglyCartesian_canonical hF o (g : R ⟶ p.obj o.x)
  exact ⟨ostar, φ, hφ⟩

/-- `u : X ⥤ X'` is a 1-morphism of fibred categories over `C`. It is strictly over `C`
because the structure functor of `X'` reads off the `X`-component, and it sends a
`p`-strongly-cartesian `φ` to the pair `(φ, F.map φ)`, whose universal property reduces to
that of `φ`: a factorization in `X'` is determined by its `X`-component, which factors
uniquely through `φ`, and its `Y`-component is then forced by the commuting square. No
fibredness assumption on either structure functor is needed. -/
lemma incl_isFibredOneMorphism :
    Functor.IsFibredOneMorphism p (structureFunctor p q F hFq) (incl p q F hFq) := by
  refine ⟨rfl, ?_⟩
  intro R S g a b φ hφ
  obtain rfl : S = p.obj b := (IsHomLift.codomain_eq p g φ).symm
  have hu_lift : (structureFunctor p q F hFq).IsHomLift g ((incl p q F hFq).map φ) :=
    (isHomLift_iff_a g ((incl p q F hFq).map φ)).2 hφ.toIsHomLift
  refine ⟨?_⟩
  intro o₁ h ψ hlift
  have hψa_lift : p.IsHomLift (h ≫ g) ψ.a := (isHomLift_iff_a (h ≫ g) ψ).1 hlift
  obtain ⟨χa, ⟨hχa_lift, hχa_fac⟩, hχa_uniq⟩ :=
    Functor.IsStronglyCartesian.universal_property p g φ h (h ≫ g) rfl ψ.a
  have hFχa_lift : q.IsHomLift h (F.map χa) := Functor.isHomLift_map_of_comp_eq hFq h χa
  have hf_lift := isHomLift_f o₁
  have hχb_lift : q.IsHomLift h (o₁.f ≫ F.map χa) :=
    (IsHomLift.lift_eqToHom_comp_iff q h (o₁.f ≫ F.map χa) o₁.hy).1
      (IsHomLift.comp q (eqToHom o₁.hy) h o₁.f (F.map χa))
  let χ : o₁ ⟶ (incl p q F hFq).obj a :=
    homOfIsHomLift h χa (o₁.f ≫ F.map χa) hχa_lift hχb_lift (Category.comp_id _)
  have hχ_lift : (structureFunctor p q F hFq).IsHomLift h χ := (isHomLift_iff_a h χ).2 hχa_lift
  refine ⟨χ, ⟨hχ_lift, ?_⟩, ?_⟩
  · refine hom_ext _ _ hχa_fac ?_
    simp only [comp_b, incl_map_b, χ, homOfIsHomLift]
    rw [(Category.comp_id ψ.b).symm.trans ψ.sq, Category.assoc, ← F.map_comp, hχa_fac]
  · rintro χ' ⟨hχ'_lift, hχ'_fac⟩
    have hχ'a_lift : p.IsHomLift h χ'.a := (isHomLift_iff_a h χ').1 hχ'_lift
    have hχ'a : χ'.a = χa := hχa_uniq _ ⟨hχ'a_lift, by simpa using congrArg (·.a) hχ'_fac⟩
    refine hom_ext _ _ hχ'a ?_
    simp only [χ, homOfIsHomLift]
    rw [(Category.comp_id χ'.b).symm.trans χ'.sq, hχ'a]

/-- `v : X' ⥤ Y` is a 1-morphism of fibred categories from the structure functor of `X'` to
`q`. Strictness over `C` is `structureFunctor_eq`. If `φ` is strongly cartesian over `f` for
the structure functor of `X'` then it differs from the canonical lift of `f` by an isomorphism
over the identity, whose `Y`-component is again such an isomorphism; hence `φ.b` is
`q`-strongly cartesian because the canonical lift's `Y`-component is. -/
lemma proj_isFibredOneMorphism [p.IsFibered] [q.IsFibered]
    (hF : Functor.IsFibredOneMorphism p q F) :
    Functor.IsFibredOneMorphism (structureFunctor p q F hFq) q (proj p q F hFq) := by
  refine ⟨structureFunctor_eq.symm, ?_⟩
  intro R S f o o' φ hφ
  obtain rfl : S = p.obj o'.x := (IsHomLift.codomain_eq (structureFunctor p q F hFq) f φ).symm
  obtain ⟨ostar, φ₀, hφ₀sc, -, hβsc⟩ :=
    exists_isStronglyCartesian_canonical hF o' (f : R ⟶ p.obj o'.x)
  exact Functor.isStronglyCartesian_map_of_isStronglyCartesian_map (proj p q F hFq) q
    structureFunctor_eq.symm f φ φ₀ hφ hφ₀sc
    ((Functor.IsStronglyCartesian.lift_comp_eqToHom_iff q f φ₀.b o'.hy.symm).1 hβsc)

/-- `w : X' ⥤ X` is a 1-morphism of fibred categories from the structure functor of `X'` to
`p`. Strictness over `C` is `structureFunctor_eq_retract_comp`. If `φ` is strongly cartesian
over `f` for the structure functor of `X'` then it differs from the canonical lift of `f` by an
isomorphism over the identity, whose `X`-component is again such an isomorphism; hence `φ.a` is
`p`-strongly cartesian because the canonical lift's `X`-component is. -/
lemma retract_isFibredOneMorphism [p.IsFibered] [q.IsFibered]
    (hF : Functor.IsFibredOneMorphism p q F) :
    Functor.IsFibredOneMorphism (structureFunctor p q F hFq) p (retract p q F hFq) := by
  refine ⟨structureFunctor_eq_retract_comp.symm, ?_⟩
  intro R S f o o' φ hφ
  obtain rfl : S = p.obj o'.x := (IsHomLift.codomain_eq (structureFunctor p q F hFq) f φ).symm
  obtain ⟨ostar, φ₀, hφ₀sc, hαsc, -⟩ :=
    exists_isStronglyCartesian_canonical hF o' (f : R ⟶ p.obj o'.x)
  exact Functor.isStronglyCartesian_map_of_isStronglyCartesian_map (retract p q F hFq) p
    structureFunctor_eq_retract_comp.symm f φ φ₀ hφ hφ₀sc hαsc

/-- `u : X ⥤ X'` is fully faithful: a morphism `u x ⟶ u x'` is a pair `(a, b)` whose square
reads `b ≫ 𝟙 = 𝟙 ≫ F.map a`, so `b = F.map a` and the data is exactly `a : x ⟶ x'`. -/
def inclFullyFaithful : (incl p q F hFq).FullyFaithful where
  preimage g := g.a
  map_preimage g := by
    apply hom_ext
    · simp
    · simp only [incl_map_b]
      exact (Category.id_comp (F.map g.a)).symm.trans
        (g.sq.symm.trans (Category.comp_id g.b))
  preimage_map a := by simp

/-- `w` is left adjoint to `u`. The bijection `(x ⟶ x') ≃ ((U, x, y, f) ⟶ u x')` sends
`a` to the pair `(a, f ≫ F.map a)`, with inverse `(a, b) ↦ a`; it is a bijection because the
square of a morphism `(U, x, y, f) ⟶ u x'` reads `b ≫ 𝟙 = f ≫ F.map a`, forcing the second
component. Both naturality squares hold on the first component. -/
def retractAdjIncl : retract p q F hFq ⊣ incl p q F hFq :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun o x' =>
        { toFun := fun a =>
            { a := a
              b := o.f ≫ F.map a
              hpq := by
                rw [Functor.map_comp, o.hf, Functor.map_map_eq_of_comp_eq q hFq a]
                simp
              sq := Category.comp_id _ }
          invFun := fun g => g.a
          left_inv := by intro a; simp
          right_inv := by
            intro g
            apply hom_ext
            · simp
            · exact g.sq.symm.trans (Category.comp_id g.b) }
      homEquiv_naturality_left_symm := by intro o o' x' g a; simp
      homEquiv_naturality_right := by
        intro o x' x'' a g
        apply hom_ext
        · simp
        · simp [Functor.map_comp] }

/-- A morphism of the amelioration whose `X`-component is strongly cartesian is strongly
cartesian for `v : X' ⥤ Y`, over its own `Y`-component. A test morphism `φ'` factors through it
in the `Y`-direction in exactly one way, namely by the morphism `cbase` it lies over; its
`X`-component is then supplied by the universal property of `φ.a` and is likewise unique, and
the compatibility square of the pair is automatic. -/
lemma isStronglyCartesian_proj_of_isStronglyCartesian_a
    (hF : Functor.IsFibredOneMorphism p q F) {o o' : Amelioration p q F hFq} (φ : o' ⟶ o)
    (ha : p.IsStronglyCartesian (q.map φ.b ≫ eqToHom o.hy) φ.a) :
    (proj p q F hFq).IsStronglyCartesian φ.b φ := by
  set gbar : q.obj o'.y ⟶ p.obj o.x := q.map φ.b ≫ eqToHom o.hy with hgbar
  have hφ_lift : (proj p q F hFq).IsHomLift φ.b φ := IsHomLift.map (proj p q F hFq) φ
  refine ⟨?_⟩
  intro a' cbase φ' hlift'
  have hφ'b : φ'.b = cbase ≫ φ.b :=
    (IsHomLift.eq_of_isHomLift (proj p q F hFq) (cbase ≫ φ.b) φ').symm
  set gbaseC : p.obj a'.x ⟶ q.obj o'.y := eqToHom a'.hy.symm ≫ q.map cbase with hgbaseC
  have hφ'a_lift : p.IsHomLift (gbaseC ≫ gbar) φ'.a := by
    apply IsHomLift.of_commsq p (gbaseC ≫ gbar) φ'.a (a := a'.x) (b := o.x)
      (R := p.obj a'.x) (S := p.obj o.x) rfl rfl
    rw [map_a_eq φ', hφ'b]
    simp [hgbaseC, hgbar, Functor.map_comp]
  obtain ⟨χa, ⟨hχa_lift, hχa_fac⟩, hχa_uniq⟩ :=
    Functor.IsStronglyCartesian.universal_property p gbar φ.a gbaseC (gbaseC ≫ gbar) rfl φ'.a
  have hcbase_lift : q.IsHomLift gbaseC cbase := by
    apply IsHomLift.of_commsq q gbaseC cbase (a := a'.y) (b := o'.y)
      (R := p.obj a'.x) (S := q.obj o'.y) a'.hy rfl
    simp [hgbaseC]
  let χ : a' ⟶ o' := homOfIsHomLift gbaseC χa cbase hχa_lift hcbase_lift
    (sq_of_isStronglyCartesian hF φ ha hχa_lift hcbase_lift φ' hχa_fac hφ'b.symm)
  have hχ_lift : (proj p q F hFq).IsHomLift cbase χ := IsHomLift.map (proj p q F hFq) χ
  refine ⟨χ, ⟨hχ_lift, hom_ext _ _ hχa_fac hφ'b.symm⟩, ?_⟩
  rintro χ' ⟨hχ'_lift, hχ'_fac⟩
  have hχ'b : χ'.b = cbase := (IsHomLift.eq_of_isHomLift (proj p q F hFq) cbase χ').symm
  have hχ'a_lift : p.IsHomLift gbaseC χ'.a := by
    apply IsHomLift.of_commsq p gbaseC χ'.a (a := a'.x) (b := o'.x)
      (R := p.obj a'.x) (S := q.obj o'.y) rfl o'.hy.symm
    rw [map_a_eq χ', hχ'b]
    simp [hgbaseC]
  exact hom_ext _ _ (hχa_uniq _ ⟨hχ'a_lift, by simpa using congrArg (·.a) hχ'_fac⟩) hχ'b

/-- `v` exhibits `X'` as a fibred category over `Y`. Given `o = (U, x, y, f)` and a morphism
`c : y' ⟶ y` of `Y`, let `α : x* ⟶ x` be a `p`-strongly-cartesian lift of the base morphism
`q c` followed by the identification `q y = p x`. Transporting `c ≫ f` along the universal
property of the `q`-strongly-cartesian `F.map α` gives `f* : y' ⟶ F x*`, and
`(α, c) : (q y', x*, y', f*) ⟶ o` is a `v`-strongly-cartesian lift of `c`. -/
lemma proj_isFibered [p.IsFibered] [q.IsFibered] (hF : Functor.IsFibredOneMorphism p q F) :
    (proj p q F hFq).IsFibered := by
  apply Functor.IsFibered.of_exists_isStronglyCartesian
  intro o y' c
  obtain ⟨xstar, α, hα⟩ := Functor.IsPreFibered.exists_isCartesian' (p := p) (a := o.x)
    (f := (q.map c ≫ eqToHom o.hy : q.obj y' ⟶ p.obj o.x))
  have hαsc : p.IsStronglyCartesian (q.map c ≫ eqToHom o.hy : q.obj y' ⟶ p.obj o.x) α :=
    inferInstance
  have hclift : q.IsHomLift (q.map c ≫ eqToHom o.hy) c :=
    (IsHomLift.lift_comp_eqToHom_iff q (q.map c) c o.hy).2 (IsHomLift.map q c)
  obtain ⟨fstar, hfstar_lift, hfstar_fac⟩ :=
    exists_isHomLift_id_comp_eq hF o α hαsc c (isHomLift_comp_f c _ (by simp))
  let ostar : Amelioration p q F hFq :=
    { x := xstar
      y := y'
      hy := (IsHomLift.domain_eq p (q.map c ≫ eqToHom o.hy) α).symm
      f := fstar
      hf := by
        rw [IsHomLift.fac' q (𝟙 (q.obj y')) fstar]
        simp }
  let φ : ostar ⟶ o :=
    homOfIsHomLift (q.map c ≫ eqToHom o.hy) α c hαsc.toIsHomLift hclift hfstar_fac.symm
  exact ⟨ostar, φ, isStronglyCartesian_proj_of_isStronglyCartesian_a hF φ hαsc⟩

end Amelioration

end Construction

/-! ## Universe lift

The construction lives in the universe `max u₂ u₃ v₃`, whereas the statement asks for a
witness in `max u₁ u₂ u₃ v₁ v₂ v₃`. The whole conclusion is transported along the
universe-lifting equivalence `S ≌ ULiftHom (ULift S)`. -/


/-- Universe transport. Given the conclusion of Stacks 08NF realized on a category `S` in the
universe `max u₂ u₃ v₃`, the same conclusion holds with a witness category in the universe
`max u₁ u₂ u₃ v₁ v₂ v₃`. Along the universe-lifting equivalence
`e : S ≌ ULiftHom (ULift S)` the witness is `ULiftHom (ULift S)` with structure functor
`e.inverse ⋙ pS`, and the three 1-morphisms of fibred categories are `uS ⋙ e.functor`,
`e.inverse ⋙ vS` and `e.inverse ⋙ wS`; an equivalence transports both `IsHomLift` and
`IsStronglyCartesian`, the factorization equalities follow from the triangle identities, a
composite of a fully faithful functor with an equivalence is fully faithful, and an
adjunction composes with the adjunction of an equivalence. -/
theorem exists_amelioration_uliftHom
    {C : Type u₁} [Category.{v₁} C]
    {X : Type u₂} [Category.{v₂} X]
    {Y : Type u₃} [Category.{v₃} Y]
    (p : X ⥤ C) (q : Y ⥤ C) (F : X ⥤ Y)
    (S : Type (max u₂ u₃ v₃)) [instS : Category.{max v₂ v₃} S]
    (pS : S ⥤ C) (hpS : pS.IsFibered)
    (uS : X ⥤ S) (vS : S ⥤ Y) (wS : S ⥤ X)
    (h1 : Functor.IsFibredOneMorphism p pS uS) (h2 : Functor.IsFibredOneMorphism pS q vS)
    (h3 : Functor.IsFibredOneMorphism pS p wS)
    (h4 : F = uS ⋙ vS) (h5 : pS = vS ⋙ q)
    (h6 : Nonempty uS.FullyFaithful) (h7 : Nonempty (wS ⊣ uS)) (h8 : vS.IsFibered) :
    ∃ (X' : Type (max u₁ u₂ u₃ v₁ v₂ v₃)) (_ : Category.{max v₁ v₂ v₃} X')
      (p'' : X' ⥤ C) (_ : p''.IsFibered)
      (u : X ⥤ X') (v : X' ⥤ Y) (w : X' ⥤ X),
        Functor.IsFibredOneMorphism p p'' u ∧ Functor.IsFibredOneMorphism p'' q v ∧
          Functor.IsFibredOneMorphism p'' p w ∧
        F = u ⋙ v ∧ p'' = v ⋙ q ∧
        Nonempty u.FullyFaithful ∧ Nonempty (w ⊣ u) ∧ v.IsFibered := by
  let : Category.{max v₂ v₃} (ULift.{max u₁ v₁ v₂} S) := uliftCategory _
  let inst2 : Category.{max v₁ v₂ v₃} (ULiftHom.{max v₁ v₂ v₃} (ULift.{max u₁ v₁ v₂} S)) :=
    ULiftHom.category
  let e : S ≌ ULiftHom.{max v₁ v₂ v₃} (ULift.{max u₁ v₁ v₂} S) := ULiftHomULiftCategory.equiv S
  have hpSe : e.functor ⋙ (e.inverse ⋙ pS) = pS := rfl
  have scr : ∀ {R S' : C} (f : R ⟶ S')
      {a b : ULiftHom.{max v₁ v₂ v₃} (ULift.{max u₁ v₁ v₂} S)} (φ : a ⟶ b),
      (e.inverse ⋙ pS).IsStronglyCartesian f φ → pS.IsStronglyCartesian f (e.inverse.map φ) :=
    e.symm.isStronglyCartesian_map_functor pS rfl
  refine ⟨ULiftHom.{max v₁ v₂ v₃} (ULift.{max u₁ v₁ v₂} S), inst2, e.inverse ⋙ pS,
    Functor.IsFibered.comp_equivalence_inverse e pS hpSe fun _ => rfl, uS ⋙ e.functor,
    e.inverse ⋙ vS, e.inverse ⋙ wS, ?_, ?_, ?_, h4, ?_, ?_, ?_,
    Functor.IsFibered.comp_equivalence_inverse e vS rfl fun _ => rfl⟩
  · refine ⟨h1.comp_eq, ?_⟩
    intro R S' f a b φ hφ
    exact e.isStronglyCartesian_map_functor (e.inverse ⋙ pS) hpSe f (uS.map φ)
      (h1.map_isStronglyCartesian f φ hφ)
  · refine ⟨?_, ?_⟩
    · rw [Functor.assoc, h2.comp_eq]
    · intro R S' f a b φ hφ
      exact h2.map_isStronglyCartesian f (e.inverse.map φ) (scr f φ hφ)
  · refine ⟨?_, ?_⟩
    · rw [Functor.assoc, h3.comp_eq]
    · intro R S' f a b φ hφ
      exact h3.map_isStronglyCartesian f (e.inverse.map φ) (scr f φ hφ)
  · rw [Functor.assoc, ← h5]
  · exact h6.map (·.comp e.fullyFaithfulFunctor)
  · exact h7.map (Adjunction.comp e.symm.toAdjunction)

/-- **Stacks 4.33.14 / 08NF.** Let `F : X ⥤ Y` be a 1-morphism of fibred categories over
`C`, with structure functors `p : X ⥤ C` and `q : Y ⥤ C`. Then there exist a fibred
category `(X', p'')` over `C` and three 1-morphisms of fibred categories over `C`

  `u : X ⥤ X'`, `v : X' ⥤ Y`, `w : X' ⥤ X`,

with `F = u ⋙ v` such that
1. `u` is fully faithful;
2. `w` is left adjoint to `u`; and
3. `v` exhibits `X'` as a fibred category over `Y` (`v.IsFibered`), the structure functor of
   `X'` over `C` factoring as `p'' = v ⋙ q`.

The witness category `X'` is stated in the universe `max u₁ u₂ u₃ v₁ v₂ v₃` so as to
accommodate the explicit construction, in which an object carries a morphism of `Y` (living
in the hom universe `v₃`). It is the amelioration `Amelioration p q F hFq` of `F`, moved
into that universe by `exists_amelioration_uliftHom`. -/
@[stacks 08NF]
theorem Functor.IsFibered.exists_amelioration
    {C : Type u₁} [Category.{v₁} C]
    {X : Type u₂} [Category.{v₂} X]
    {Y : Type u₃} [Category.{v₃} Y]
    (p : X ⥤ C) (q : Y ⥤ C) [p.IsFibered] [q.IsFibered]
    (F : X ⥤ Y) (hF : Functor.IsFibredOneMorphism p q F) :
    ∃ (X' : Type (max u₁ u₂ u₃ v₁ v₂ v₃)) (_ : Category.{max v₁ v₂ v₃} X')
      (p'' : X' ⥤ C) (_ : p''.IsFibered)
      (u : X ⥤ X') (v : X' ⥤ Y) (w : X' ⥤ X),
        -- the three functors are 1-morphisms of fibred categories over C
        Functor.IsFibredOneMorphism p p'' u ∧
        Functor.IsFibredOneMorphism p'' q v ∧
        Functor.IsFibredOneMorphism p'' p w ∧
        -- F factors as u ⋙ v
        F = u ⋙ v ∧
        -- the structure functor of X' over C factors through Y as p'' = v ⋙ q
        p'' = v ⋙ q ∧
        -- (1) u is fully faithful
        Nonempty u.FullyFaithful ∧
        -- (2) w is left adjoint to u
        Nonempty (w ⊣ u) ∧
        -- (3) v exhibits X' as a fibred category over Y
        v.IsFibered := by
  have hFq : F ⋙ q = p := hF.comp_eq
  exact exists_amelioration_uliftHom p q F (Amelioration p q F hFq)
    (Amelioration.structureFunctor p q F hFq) (Amelioration.structureFunctor_isFibered hF)
    (Amelioration.incl p q F hFq) (Amelioration.proj p q F hFq) (Amelioration.retract p q F hFq)
    Amelioration.incl_isFibredOneMorphism (Amelioration.proj_isFibredOneMorphism hF)
    (Amelioration.retract_isFibredOneMorphism hF) Amelioration.incl_comp_proj
    Amelioration.structureFunctor_eq ⟨Amelioration.inclFullyFaithful⟩
    ⟨Amelioration.retractAdjIncl⟩ (Amelioration.proj_isFibered hF)

end CategoryTheory
