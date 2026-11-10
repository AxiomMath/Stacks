module

public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import Mathlib.CategoryTheory.FiberedCategory.Fiber

public import StacksCore.CategoryTheory.Inertia
public import StacksFrontier.CategoryTheory.FibredOneMorphism

/-!
# Extensionality and fibredness for the relative inertia

Facts about the canonical relative inertia `CategoryTheory.RelativeInertia` (Stacks 034I)
that the promoted file does not carry, collected here once so that the Section 4.34 results
(Stacks 034H, 04Z6) and the inertia of a stack (Stacks 036Y) do not each keep a copy.

## Main results

* `CategoryTheory.RelativeInertia.obj_ext`: an object of `I_{S/S'}` is determined by its
  underlying object together with its automorphism (the condition `F α = id` being a
  proposition), and `CategoryTheory.RelativeInertiaHom.eqToHom_hom`: the underlying morphism
  of an `eqToHom` of the inertia is the corresponding `eqToHom` of `S`.
* `CategoryTheory.RelativeInertia.isHomLift_π_comp_iff`: a morphism of the inertia lies over
  a morphism of the base exactly when its underlying morphism of `S` does.
* `CategoryTheory.RelativeInertia.isFibered`, Stacks 034H (2): the relative inertia of a
  1-morphism of fibred categories over `C` is again fibred over `C`.
-/

@[expose] public section

namespace CategoryTheory

universe v₂ v₃ u₂ u₃

variable {S : Type u₂} [Category.{v₂} S] {S' : Type u₃} [Category.{v₃} S']

/-- Objects of the relative inertia are equal as soon as their underlying objects and
their automorphisms are, the automorphisms being compared across the object equality. -/
lemma RelativeInertia.obj_ext {F : S ⥤ S'} {A B : RelativeInertia F}
    (ho : A.obj = B.obj)
    (ha : A.auto.asIso.hom = eqToHom ho ≫ B.auto.asIso.hom ≫ eqToHom ho.symm) : A = B := by
  obtain ⟨ao, aa, ai⟩ := A; obtain ⟨bo, ba, bi⟩ := B
  simp only at ho; subst ho
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at ha
  congr 1
  exact Aut.ext (Iso.ext ha)

/-- The underlying morphism of an `eqToHom` of the relative inertia is the `eqToHom` of
the underlying objects. -/
@[simp] lemma RelativeInertiaHom.eqToHom_hom (F : S ⥤ S') {A B : RelativeInertia F} (h : A = B) :
    (eqToHom h : A ⟶ B).hom = eqToHom (congrArg RelativeInertia.obj h) := by
  subst h; rfl

/-- A morphism of the relative inertia lies over a morphism of the base for the structure
functor `π ⋙ p` exactly when its underlying morphism of `S` does for `p`. -/
lemma RelativeInertia.isHomLift_π_comp_iff {C : Type*} [Category C] {F : S ⥤ S'} {p : S ⥤ C}
    {A B : RelativeInertia F} {R T : C} (g : R ⟶ T) (ψ : A ⟶ B) :
    (RelativeInertia.π F ⋙ p).IsHomLift g ψ ↔ p.IsHomLift g ψ.hom := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · cases h
    exact IsHomLift.map p ψ.hom
  · cases h
    exact IsHomLift.map (RelativeInertia.π F ⋙ p) ψ

/-! ## The relative inertia is a fibred category (Stacks 034H (2)) -/

/-- An endomorphism whose image under `p` is the identity lies over that identity. -/
private theorem isHomLift_id_of_map_eq_id {C : Type*} [Category C] (p : S ⥤ C) {x : S}
    {α : x ⟶ x} (h : p.map α = 𝟙 (p.obj x)) : p.IsHomLift (𝟙 (p.obj x)) α :=
  IsHomLift.of_fac' p _ α rfl rfl (by simpa using h)

/-- If `u` and `v` lie over an identity and become mutually inverse after composing with a
strongly cartesian `φ`, then `u ≫ v = 𝟙`. -/
private theorem comp_eq_id_of_fac_comp_eq_id {C : Type*} [Category C] (p : S ⥤ C) {R : C}
    {x y : S} {f : R ⟶ p.obj y} (φ : x ⟶ y) [p.IsStronglyCartesian f φ] {a b : y ⟶ y}
    {u v : x ⟶ x} [p.IsHomLift (𝟙 R) u] [p.IsHomLift (𝟙 R) v] (hab : a ≫ b = 𝟙 y)
    (hu : u ≫ φ = φ ≫ a) (hv : v ≫ φ = φ ≫ b) : u ≫ v = 𝟙 x := by
  have : p.IsHomLift (𝟙 R) (𝟙 x) := IsHomLift.id (IsHomLift.domain_eq p (𝟙 R) u)
  refine Functor.IsStronglyCartesian.ext p f φ (𝟙 R) ?_
  rw [Category.assoc, hv, ← Category.assoc, hu, Category.assoc, hab, Category.comp_id,
    Category.id_comp]

/-- **Stacks 034H (2)**. Let `p : S ⥤ C` be a fibred category, let `p' : S' ⥤ C` be a category
over `C` and let `F : S ⥤ S'` be a 1-morphism of fibred categories over `C` from `p` to `p'`.
Then the relative inertia `I_{S/S'}`, with its structure functor `π ⋙ p`, is again a fibred
category over `C`.

The lift is built by hand rather than transported from the 2-fibre-product description of the
inertia. Given `A = (x, α)` over `T` and `f : R ⟶ T`, choose a strongly cartesian lift
`φ : y ⟶ x` of `f` for `p`. As `F α = 𝟙`, the automorphism `α` lies over `𝟙 T`, so `φ ≫ α`
lies over `f` and the universal property of `φ` produces a unique `β : y ⟶ y` over `𝟙 R` with
`β ≫ φ = φ ≫ α`. Applying the same construction to `α⁻¹` gives a two-sided inverse of `β`, by
uniqueness, and `F β = 𝟙` because `F φ` is strongly cartesian for `p'` and both `F β` and the
identity lie over `𝟙 R` and become `F φ` after composing with `F φ`. Hence `(y, β)` is an
object of the inertia and `φ` is a morphism `(y, β) ⟶ (x, α)`; it is strongly cartesian for
`π ⋙ p` because a lift of a morphism of the inertia through it is the same thing as a lift of
the underlying morphism of `S` through `p`. -/
theorem RelativeInertia.isFibered {C : Type*} [Category C] (F : S ⥤ S') (p : S ⥤ C) (p' : S' ⥤ C)
    (hp : p.IsFibered) (hF : p.IsFibredOneMorphism p' F) :
    (RelativeInertia.π F ⋙ p).IsFibered := by
  obtain ⟨rfl, hcart⟩ := hF
  apply Functor.IsFibered.of_exists_isStronglyCartesian
  dsimp only [Functor.comp_obj, RelativeInertia.π_obj]
  intro A R f
  -- Step 1: a strongly cartesian lift `φ : x' ⟶ A.obj` of `f` in `S`.
  obtain ⟨x', φ, hφc⟩ :=
    Functor.IsPreFibered.exists_isCartesian' (p := F ⋙ p') (a := A.obj) (R := R) f
  have : (F ⋙ p').IsCartesian f φ := hφc
  have : (F ⋙ p').IsStronglyCartesian f φ := inferInstance
  -- `A.auto.asIso.hom` and `A.auto.asIso.inv` lie over the identity, since
  -- `F A.auto.asIso.hom = 𝟙`.
  have hauto_lift : (F ⋙ p').IsHomLift (𝟙 (p'.obj (F.obj A.obj))) A.auto.asIso.hom :=
    isHomLift_id_of_map_eq_id _ (by simp [A.cond])
  have hautoinv_lift : (F ⋙ p').IsHomLift (𝟙 (p'.obj (F.obj A.obj))) A.auto.asIso.inv :=
    isHomLift_id_of_map_eq_id _ (by simp [A.cond_inv])
  -- Step 2: the induced endomorphisms `βhom`, `βinv` of `x'`, both over `𝟙 R`.
  have hf : f = 𝟙 R ≫ f := (Category.id_comp f).symm
  set βhom : x' ⟶ x' := Functor.IsStronglyCartesian.map (F ⋙ p') f φ hf (φ ≫ A.auto.asIso.hom)
    with βhom_def
  set βinv : x' ⟶ x' := Functor.IsStronglyCartesian.map (F ⋙ p') f φ hf (φ ≫ A.auto.asIso.inv)
    with βinv_def
  have hβhom_lift : (F ⋙ p').IsHomLift (𝟙 R) βhom :=
    Functor.IsStronglyCartesian.map_isHomLift (F ⋙ p') f φ hf _
  have hβinv_lift : (F ⋙ p').IsHomLift (𝟙 R) βinv :=
    Functor.IsStronglyCartesian.map_isHomLift (F ⋙ p') f φ hf _
  have hβhom_fac : βhom ≫ φ = φ ≫ A.auto.asIso.hom :=
    Functor.IsStronglyCartesian.fac (F ⋙ p') f φ hf _
  have hβinv_fac : βinv ≫ φ = φ ≫ A.auto.asIso.inv :=
    Functor.IsStronglyCartesian.fac (F ⋙ p') f φ hf _
  have hx'R : (F ⋙ p').obj x' = R := IsHomLift.domain_eq (F ⋙ p') f φ
  -- Step 3: `βhom` and `βinv` are mutually inverse, by uniqueness in the universal property.
  have hhom_inv : βhom ≫ βinv = 𝟙 x' :=
    comp_eq_id_of_fac_comp_eq_id (F ⋙ p') (f := f) φ A.auto.asIso.hom_inv_id hβhom_fac hβinv_fac
  have hinv_hom : βinv ≫ βhom = 𝟙 x' :=
    comp_eq_id_of_fac_comp_eq_id (F ⋙ p') (f := f) φ A.auto.asIso.inv_hom_id hβinv_fac hβhom_fac
  let β : x' ≅ x' := { hom := βhom, inv := βinv, hom_inv_id := hhom_inv, inv_hom_id := hinv_hom }
  -- Step 4: `F βhom = 𝟙`, because `F φ` is strongly cartesian for `p'`.
  have hFφc : p'.IsStronglyCartesian f (F.map φ) := hcart f φ inferInstance
  have hFβhom : F.map βhom = 𝟙 (F.obj x') := by
    have hReq : p'.obj (F.obj x') = R := hx'R
    have hid_lift : p'.IsHomLift (𝟙 R) (𝟙 (F.obj x')) := IsHomLift.id hReq
    have hFβ_lift : p'.IsHomLift (𝟙 R) (F.map βhom) := by
      refine IsHomLift.of_fac' p' (𝟙 R) (F.map βhom) hReq hReq ?_
      have hq : (F ⋙ p').map βhom = eqToHom hx'R ≫ 𝟙 R ≫ eqToHom hx'R.symm :=
        IsHomLift.fac' (F ⋙ p') (𝟙 R) βhom
      simpa using hq
    apply Functor.IsStronglyCartesian.ext p' f (F.map φ) (𝟙 R)
    rw [Category.id_comp, ← F.map_comp, hβhom_fac, F.map_comp, A.cond, Category.comp_id]
  -- Step 5: the object `B = (x', β)` of the inertia and the candidate lift `φbar : B ⟶ A`.
  let B : RelativeInertia F := { obj := x', auto := .of β, cond := hFβhom }
  let φbar : B ⟶ A := { hom := φ, comm := hβhom_fac.symm }
  refine ⟨B, φbar, ?_⟩
  -- Step 6: `φbar` is strongly cartesian for `π ⋙ (F ⋙ p')`.
  have hφ_lift : (F ⋙ p').IsHomLift f φ := inferInstance
  have hφbar_lift : (RelativeInertia.π F ⋙ F ⋙ p').IsHomLift f φbar :=
    (RelativeInertia.isHomLift_π_comp_iff f φbar).mpr hφ_lift
  apply Functor.IsStronglyCartesian.mk
  dsimp only [Functor.comp_obj, RelativeInertia.π_obj]
  intro Z g ψbar hψbar
  have := hψbar
  have hψ_lift : (F ⋙ p').IsHomLift (g ≫ f) ψbar.hom :=
    (RelativeInertia.isHomLift_π_comp_iff (g ≫ f) ψbar).mp hψbar
  set χ : Z.obj ⟶ x' :=
    Functor.IsStronglyCartesian.map (F ⋙ p') f φ (rfl : g ≫ f = g ≫ f) ψbar.hom with χ_def
  have hχ_lift : (F ⋙ p').IsHomLift g χ :=
    Functor.IsStronglyCartesian.map_isHomLift (F ⋙ p') f φ rfl ψbar.hom
  have hχ_fac : χ ≫ φ = ψbar.hom := Functor.IsStronglyCartesian.fac (F ⋙ p') f φ rfl ψbar.hom
  -- `χ` is a morphism `Z ⟶ B` of the inertia: it commutes with the automorphisms.
  have hχ_comm : χ ≫ β.hom = Z.auto.asIso.hom ≫ χ := by
    have hZauto : (F ⋙ p').IsHomLift (𝟙 (p'.obj (F.obj Z.obj))) Z.auto.asIso.hom :=
      isHomLift_id_of_map_eq_id _ (by simp [Z.cond])
    have : (F ⋙ p').IsHomLift g (Z.auto.asIso.hom ≫ χ) := inferInstance
    have : (F ⋙ p').IsHomLift g (χ ≫ β.hom) := inferInstance
    apply Functor.IsStronglyCartesian.ext (F ⋙ p') f φ g
    show (χ ≫ β.hom) ≫ φ = (Z.auto.asIso.hom ≫ χ) ≫ φ
    rw [Category.assoc, show β.hom = βhom from rfl, hβhom_fac, ← Category.assoc, hχ_fac,
      Category.assoc, hχ_fac]
    exact ψbar.comm
  let χbar : Z ⟶ B := { hom := χ, comm := hχ_comm }
  refine ⟨χbar, ⟨(RelativeInertia.isHomLift_π_comp_iff g χbar).mpr hχ_lift, ?_⟩, ?_⟩
  · exact RelativeInertiaHom.ext hχ_fac
  · rintro ybar ⟨hy_lift, hy_fac⟩
    refine RelativeInertiaHom.ext ?_
    have : (F ⋙ p').IsHomLift g ybar.hom :=
      (RelativeInertia.isHomLift_π_comp_iff g ybar).mp hy_lift
    refine Functor.IsStronglyCartesian.map_uniq (F ⋙ p') f φ (rfl : g ≫ f = g ≫ f)
      ψbar.hom ybar.hom ?_
    have h : (ybar ≫ φbar).hom = ψbar.hom := by rw [hy_fac]
    simpa using h

/-! ### The neutral section -/

/-- The neutral section `e : S ⥤ I_{S/S'}`, `x ↦ (x, 𝟙 x)`, of the relative inertia
(Stacks 4.34.2.2). -/
def RelativeInertia.neutralSection (F : S ⥤ S') : S ⥤ RelativeInertia F where
  obj x := ⟨x, .of (Iso.refl x), by simp⟩
  map φ := ⟨φ, by simp⟩

/-! The three projections of the neutral section. They are deliberately **not** `simp` lemmas:
rewriting `((neutralSection F).obj x).obj` or `((neutralSection F).auto x)` is a dependent
rewrite, so `simp` gets stuck on the resulting `𝟙`s, whereas unfolding `neutralSection` itself
(`simp [RelativeInertia.neutralSection]`) closes such goals outright. Pass them by name where a
projection is what is wanted. -/

/-- The underlying object of `e x` is `x`. -/
lemma RelativeInertia.neutralSection_obj_obj (F : S ⥤ S') (x : S) :
    ((RelativeInertia.neutralSection F).obj x).obj = x := rfl

/-- The automorphism of `e x` is the identity of `x`. -/
lemma RelativeInertia.neutralSection_obj_auto (F : S ⥤ S') (x : S) :
    ((RelativeInertia.neutralSection F).obj x).auto = .of (Iso.refl x) := rfl

/-- The underlying morphism of `e ψ` is `ψ`. -/
lemma RelativeInertia.neutralSection_map_hom (F : S ⥤ S') {x y : S} (ψ : x ⟶ y) :
    ((RelativeInertia.neutralSection F).map ψ).hom = ψ := rfl

/-- The neutral section is a section of the structure map `π`. Taking `S' = C` and `F = p` gives
the same statement for the absolute inertia. -/
@[simp] lemma RelativeInertia.neutralSection_comp_π (F : S ⥤ S') :
    RelativeInertia.neutralSection F ⋙ RelativeInertia.π F = 𝟭 S := rfl

/-- The neutral section is a 1-morphism over the base: composing it with the structure functor of
`I_{S/S'}` recovers `p`. Taking `S' = C` and `F = p` gives the absolute case. -/
@[simp] lemma RelativeInertia.neutralSection_comp_relativeInertiaStruct {C : Type*} [Category C]
    (F : S ⥤ S') (p : S ⥤ C) :
    RelativeInertia.neutralSection F ⋙ relativeInertiaStruct F p = p := rfl

/-! ### When the forgetful functor `π` is an equivalence

`π` is always faithful and essentially surjective, so the whole content of Stacks 04ZM and of
Stacks 042J is that `π` is *full* exactly when the fibres of `p` are thin.

None of the four results below mentions a site or a stack: they are statements about a functor
and its fibres. They are kept here, rather than in the Chapter 8 stacks module, so that
Stacks 042J — a Chapter 4 result — does not need a stacks module to prove itself. -/

/-- `π : I_{S/S'} ⥤ S` is faithful: a morphism of the inertia is determined by its underlying
morphism of `S`. -/
instance RelativeInertia.π_faithful (F : S ⥤ S') : (RelativeInertia.π F).Faithful where
  map_injective h := RelativeInertiaHom.ext h

/-- `π : I_{S/S'} ⥤ S` is essentially surjective: `x` is the image of `(x, 𝟙)`. -/
instance RelativeInertia.π_essSurj (F : S ⥤ S') : (RelativeInertia.π F).EssSurj where
  mem_essImage x := ⟨⟨x, .of (Iso.refl x), by simp⟩, ⟨Iso.refl x⟩⟩

/-- If the fibres of `p` are thin, then every automorphism of an object of `S` lying over an
identity is the identity; equivalently, the objects of the absolute inertia `I_S` are the
objects of `S` with their identity automorphism. -/
lemma RelativeInertia.auto_eq_id_of_fiber_isThin {C : Type*} [Category C] (p : S ⥤ C)
    (ht : ∀ U, Quiver.IsThin (p.Fiber U)) (A : AbsoluteInertia p) : A.auto.asIso.hom = 𝟙 A.obj := by
  have : p.IsHomLift (𝟙 (p.obj A.obj)) A.auto.asIso.hom := isHomLift_id_of_map_eq_id p A.cond
  simpa using congrArg Functor.Fiber.fiberInclusion.map
    ((ht (p.obj A.obj) _ _).allEq (Functor.Fiber.homMk p _ A.auto.asIso.hom) (𝟙 _))

/-- If the fibres of `p` are thin, then `π : I_S ⥤ S` is full: every morphism of `S`
automatically commutes with the automorphisms, since these are identities. -/
lemma RelativeInertia.π_full_of_fiber_isThin {C : Type*} [Category C] (p : S ⥤ C)
    (ht : ∀ U, Quiver.IsThin (p.Fiber U)) : (RelativeInertia.π p).Full where
  map_surjective {A B} φ := ⟨⟨φ, by
    rw [RelativeInertia.auto_eq_id_of_fiber_isThin p ht A,
      RelativeInertia.auto_eq_id_of_fiber_isThin p ht B]
    exact (Category.comp_id φ).trans (Category.id_comp φ).symm⟩, rfl⟩

/-- Conversely, if `π : I_S ⥤ S` is full and the fibres of `p` are groupoids, then the fibres
of `p` are thin: two parallel morphisms of a fibre differ by an automorphism lying over an
identity, and fullness of `π` forces that automorphism to be the identity. -/
lemma RelativeInertia.fiber_isThin_of_π_full {C : Type*} [Category C] (p : S ⥤ C)
    (hg : ∀ U, IsGroupoid (p.Fiber U)) (hfull : (RelativeInertia.π p).Full) (U : C) :
    Quiver.IsThin (p.Fiber U) := fun a _ ↦ ⟨by
  intro f g
  have hgrpd := hg U
  have hgiso : IsIso g := IsGroupoid.all_isIso g
  set α : a ⟶ a := f ≫ inv g with hα
  have hcond : p.map (Functor.Fiber.fiberInclusion.map α) =
      𝟙 (p.obj (Functor.Fiber.fiberInclusion.obj a)) := by
    simpa using IsHomLift.fac' p (𝟙 U) (Functor.Fiber.fiberInclusion.map α)
  obtain ⟨ψ, hψ⟩ := hfull.map_surjective
    (X := ⟨Functor.Fiber.fiberInclusion.obj a, .of (Functor.Fiber.fiberInclusion.mapIso (asIso α)),
      hcond⟩)
    (Y := ⟨Functor.Fiber.fiberInclusion.obj a, .of (Iso.refl _), by simp⟩)
    (𝟙 (Functor.Fiber.fiberInclusion.obj a))
  have hψ' : ψ.hom = 𝟙 (Functor.Fiber.fiberInclusion.obj a) := hψ
  have hval : Functor.Fiber.fiberInclusion.map α = Functor.Fiber.fiberInclusion.map (𝟙 a) := by
    simpa [hψ'] using ψ.comm.symm
  exact (comp_inv_eq_id g).mp (by rw [← hα]; exact Functor.Fiber.hom_ext hval)⟩

end CategoryTheory
