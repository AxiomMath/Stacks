module

public import StacksFrontier.AlgebraicGeometry.Stacks.PresheafFibredCategory
public import StacksFrontier.CategoryTheory.FiberedCategory.DiscreteTwoFibreProduct

/-!
# Gluing 1-morphisms into a sheaf along a family that lifts objects locally

Let `𝒳` be a category fibred in groupoids over the big fppf site of `S` and let `E` be a sheaf of
sets on that site. A family of 1-morphisms `g i : 𝒴 i ⟶ 𝒳` *lifts objects locally* when every
object `x` of `𝒳` over `T` is, after restriction along the arrows of a covering sieve of `T`, the
image of an object of some `𝒴 i`. For such a family, a family of 1-morphisms `φ i : 𝒴 i ⟶ E`
which agree on objects with isomorphic images in `𝒳` glues to a unique 1-morphism `𝒳 ⟶ E` (this
is the construction of the moduli map in the proof of the Keel–Mori theorem, Stacks 0DUT).

## Main definitions

* `AlgebraicGeometry.Stack.homOfSections`: the 1-morphism into the category attached to a
  presheaf named by a family of sections compatible with pullbacks.

## Main results

* `AlgebraicGeometry.Stack.exists_hom_of_liftsLocally`
* `AlgebraicGeometry.Stack.hom_ext_of_liftsLocally`
-/

@[expose] public section

open CategoryTheory Opposite PresheafOfCategories

namespace AlgebraicGeometry.Stack

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
  {E : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### 1-morphisms from sections -/

/-- **The 1-morphism into the category attached to a presheaf named by a family of sections**
compatible with pullbacks: an object `x` over `T` goes to `(T, σ x)`. -/
def homOfSections (σ : ∀ x : 𝒳.val.obj, E.obj (op (𝒳.val.p.obj x)))
    (hσ : ∀ {x' x : 𝒳.val.obj} (m : x' ⟶ x), σ x' = E.map (𝒳.val.p.map m).op (σ x)) :
    𝒳 ⟶ fibredCategory B S hS E := by
  let f : 𝒳.val.obj ⥤ (fibredCategory B S hS E).val.obj :=
    { obj x := ⟨𝒳.val.p.obj x, Discrete.mk (σ x)⟩
      map {x' x} m := {
        base := 𝒳.val.p.map m
        fiber := Discrete.eqToHom (hσ m) }
      map_id x := by
        refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ (𝒳.val.p.map_id x) ?_
        apply Discrete.hom_eq
      map_comp m₁ m₂ := by
        refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ (𝒳.val.p.map_comp m₁ m₂) ?_
        apply Discrete.hom_eq }
  exact (CatFiberedInGroupoids.homEquivBasedFunctor _ _).symm ⟨f, rfl⟩

/-- `homOfSections σ hσ` sends an object `x` over `T` to `(T, σ x)`. -/
theorem homOfSections_obj (σ : ∀ x : 𝒳.val.obj, E.obj (op (𝒳.val.p.obj x)))
    (hσ : ∀ {x' x : 𝒳.val.obj} (m : x' ⟶ x), σ x' = E.map (𝒳.val.p.map m).op (σ x))
    (x : 𝒳.val.obj) :
    (homOfSections σ hσ).hom.obj x = ⟨𝒳.val.p.obj x, Discrete.mk (σ x)⟩ := rfl

/-- The element named by an object depends only on the object. -/
theorem elementOf_congr {X X' : (fibredCategory B S hS E).val.obj} (h : X = X')
    {V : BigFppfOver B S hS} (hX : X.base = V) (hX' : X'.base = V) :
    elementOf E hX = elementOf E hX' := by
  subst h
  rfl

/-! ### Gluing -/

variable {ι : Type*} {𝒴 : ι → CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
  (g : ∀ i, 𝒴 i ⟶ 𝒳)

/-- A family of 1-morphisms into `𝒳` **lifts objects locally** when every object of `𝒳` over `T`
is, along every arrow of some covering sieve of `T`, the target of a morphism from the image of an
object of some member of the family lying over that arrow. -/
def LiftsLocally : Prop :=
  ∀ x : 𝒳.val.obj, ∃ R ∈ BigFppfOver.topology B S hS (𝒳.val.p.obj x),
    ∀ ⦃V : BigFppfOver B S hS⦄ ⦃k : V ⟶ 𝒳.val.p.obj x⦄, R.arrows k →
      ∃ (i : ι) (y : (𝒴 i).val.obj) (m : (g i).hom.obj y ⟶ x), 𝒳.val.p.IsHomLift k m

variable {g} (φ : ∀ i, 𝒴 i ⟶ fibredCategory B S hS E)

/-- The family `φ` is **compatible** along `g` when two objects whose images in `𝒳` are joined by
a morphism over an identity have the same image. -/
def CompatibleAlong : Prop :=
  ∀ (i j : ι) (y : (𝒴 i).val.obj) (y' : (𝒴 j).val.obj) (V : BigFppfOver B S hS)
    (θ : (g i).hom.obj y ⟶ (g j).hom.obj y'), 𝒳.val.p.IsHomLift (𝟙 V) θ →
      (φ i).hom.obj y = (φ j).hom.obj y'

section

variable {φ} (hφ : CompatibleAlong (g := g) φ)

include hφ in
/-- Two lifts of the same object of `𝒳` over the same arrow name the same element. -/
theorem elementOf_eq_of_lifts {x : 𝒳.val.obj} {V : BigFppfOver B S hS}
    {k : V ⟶ 𝒳.val.p.obj x} {i j : ι} {y : (𝒴 i).val.obj} {y' : (𝒴 j).val.obj}
    (m : (g i).hom.obj y ⟶ x) (m' : (g j).hom.obj y' ⟶ x) (hm : 𝒳.val.p.IsHomLift k m)
    (hm' : 𝒳.val.p.IsHomLift k m') (hy : ((φ i).hom.obj y).base = V)
    (hy' : ((φ j).hom.obj y').base = V) :
    elementOf E hy = elementOf E hy' := by
  have := 𝒳.isFiberedInGroupoids.isStronglyCartesian_homLift k m'
  exact elementOf_congr (hφ i j y y' V _
    (Functor.IsStronglyCartesian.map_isHomLift 𝒳.val.p k m' (Category.id_comp k).symm m)) hy hy'

end

section Glue

variable (hE : Presieve.IsSheaf (BigFppfOver.topology B S hS) E)

include hE in
/-- Two elements of a sheaf which agree on a covering sieve are equal. -/
theorem eq_of_forall_map_eq {T : BigFppfOver B S hS} {R : Sieve T}
    (hR : R ∈ BigFppfOver.topology B S hS T) {a b : E.obj (op T)}
    (h : ∀ ⦃V : BigFppfOver B S hS⦄ ⦃k : V ⟶ T⦄, R.arrows k → E.map k.op a = E.map k.op b) :
    a = b :=
  (hE R hR).isSeparatedFor (fun _ k _ => E.map k.op b) a b (fun _ _ hk => h hk)
    (fun _ _ _ => rfl)

/-- The base of the image of an object under a 1-morphism into the category attached to a
presheaf is the base of the object. -/
theorem base_obj_eq {𝒜 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (F : 𝒜 ⟶ fibredCategory B S hS E) (a : 𝒜.val.obj) :
    (F.hom.obj a).base = 𝒜.val.p.obj a :=
  Functor.congr_obj F.hom.w a

/-- A morphism lying over `l` identifies the element named by the image of its source with the
restriction along `l` of the element named by the image of its target. -/
private theorem elementOf_eq_map_of_isHomLift
    {𝒜 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (F : 𝒜 ⟶ fibredCategory B S hS E) {a' a : 𝒜.val.obj} {Z V : BigFppfOver B S hS}
    (l : Z ⟶ V) (n : a' ⟶ a) (hn : 𝒜.val.p.IsHomLift l n) (hX : (F.hom.obj a').base = Z)
    (hY : (F.hom.obj a).base = V) : elementOf E hX = E.map l.op (elementOf E hY) :=
  elementOf_eq_map _ _ l (F.hom.map n) (Functor.isHomLift_map_of_comp_eq F.hom.w l n)

variable (hg : LiftsLocally g) {φ} (hφ : CompatibleAlong (g := g) φ)

/-- The base of the image under `φ i` of a lift over `k : V ⟶ T` is `V`. -/
theorem base_φ_obj_eq {x : 𝒳.val.obj} {V : BigFppfOver B S hS} {k : V ⟶ 𝒳.val.p.obj x} {i : ι}
    {y : (𝒴 i).val.obj} (m : (g i).hom.obj y ⟶ x) (hm : 𝒳.val.p.IsHomLift k m) :
    ((φ i).hom.obj y).base = V :=
  (base_obj_eq (φ i) y).trans ((Functor.congr_obj (g i).hom.w y).symm.trans
    (IsHomLift.domain_eq 𝒳.val.p k m))

/-- The local value of the glued section along an arrow of the chosen covering sieve. -/
noncomputable def localValue (x : 𝒳.val.obj) :
    Presieve.FamilyOfElements E (hg x).choose.arrows := fun _ _ hk =>
  elementOf E (base_φ_obj_eq (φ := φ) ((hg x).choose_spec.2 hk).choose_spec.choose_spec.choose
    ((hg x).choose_spec.2 hk).choose_spec.choose_spec.choose_spec)

include hφ in
/-- The local value along an arrow of the chosen sieve is the element named by any lift over that
arrow. -/
theorem localValue_eq {x : 𝒳.val.obj} {V : BigFppfOver B S hS} {k : V ⟶ 𝒳.val.p.obj x}
    (hk : (hg x).choose.arrows k) {i : ι} {y : (𝒴 i).val.obj} (m : (g i).hom.obj y ⟶ x)
    (hm : 𝒳.val.p.IsHomLift k m) :
    localValue hg (φ := φ) x k hk = elementOf E (base_φ_obj_eq (φ := φ) m hm) :=
  elementOf_eq_of_lifts hφ _ m ((hg x).choose_spec.2 hk).choose_spec.choose_spec.choose_spec hm _ _

/-- A lift of an object along an arrow of the base. -/
theorem exists_lift_obj {𝒜 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (a : 𝒜.val.obj) {Z : BigFppfOver B S hS} (l : Z ⟶ 𝒜.val.p.obj a) :
    ∃ (a' : 𝒜.val.obj) (n : a' ⟶ a), 𝒜.val.p.IsHomLift l n :=
  𝒜.isFiberedInGroupoids.exists_lift l a rfl

/-- **Restricting a lift along an arrow.** If `m : g i y ⟶ x` lies over `k`, then for every
`l : Z ⟶ V` there is a lift `y'` of `y` over `l`, and `g i (y' ⟶ y) ≫ m` lies over `l ≫ k`. -/
theorem exists_restrict_lift {x : 𝒳.val.obj} {V Z : BigFppfOver B S hS}
    {k : V ⟶ 𝒳.val.p.obj x} {i : ι} {y : (𝒴 i).val.obj} (m : (g i).hom.obj y ⟶ x)
    (hm : 𝒳.val.p.IsHomLift k m) (l : Z ⟶ V) :
    ∃ (y' : (𝒴 i).val.obj) (n : y' ⟶ y), (𝒴 i).val.p.IsHomLift l n ∧
      𝒳.val.p.IsHomLift (l ≫ k) ((g i).hom.map n ≫ m) := by
  have hV : V = (𝒴 i).val.p.obj y :=
    (IsHomLift.domain_eq 𝒳.val.p k m).symm.trans (Functor.congr_obj (g i).hom.w y)
  obtain ⟨y', n, hn⟩ := exists_lift_obj y (l ≫ eqToHom hV)
  have hn' : (𝒴 i).val.p.IsHomLift l n := (IsHomLift.lift_comp_eqToHom_iff _ l n hV).mp hn
  have hgn : 𝒳.val.p.IsHomLift l ((g i).hom.map n) :=
    Functor.isHomLift_map_of_comp_eq (g i).hom.w l n
  exact ⟨y', n, hn', inferInstance⟩

include hφ in
/-- The local values along the chosen covering sieve form a compatible family. -/
theorem localValue_compatible (x : 𝒳.val.obj) : (localValue hg (φ := φ) x).Compatible := by
  rw [Presieve.compatible_iff_sieveCompatible]
  intro V Z k l hk
  obtain ⟨i, y, m, hm⟩ := (hg x).choose_spec.2 hk
  obtain ⟨y', n, hn, hcomp⟩ := exists_restrict_lift m hm l
  rw [localValue_eq hg hφ (Sieve.downward_closed _ hk l) _ hcomp, localValue_eq hg hφ hk m hm]
  exact elementOf_eq_map_of_isHomLift (φ i) l n hn _ _

/-- **The glued section** at an object of `𝒳`. -/
noncomputable def glueSection (x : 𝒳.val.obj) : E.obj (op (𝒳.val.p.obj x)) :=
  (hE _ (hg x).choose_spec.1).amalgamate _ (localValue_compatible hg hφ x)

/-- The glued section restricts, along an arrow of the chosen sieve, to the element named by any
lift over that arrow. -/
theorem map_glueSection {x : 𝒳.val.obj} {V : BigFppfOver B S hS} {k : V ⟶ 𝒳.val.p.obj x}
    (hk : (hg x).choose.arrows k) {i : ι} {y : (𝒴 i).val.obj} (m : (g i).hom.obj y ⟶ x)
    (hm : 𝒳.val.p.IsHomLift k m) :
    E.map k.op (glueSection hE hg hφ x) = elementOf E (base_φ_obj_eq (φ := φ) m hm) :=
  ((hE _ (hg x).choose_spec.1).valid_glue _ k hk).trans (localValue_eq hg hφ hk m hm)

/-- The glued sections are compatible with pullbacks along the morphisms of `𝒳`. -/
theorem glueSection_naturality {x' x : 𝒳.val.obj} (m₀ : x' ⟶ x) :
    glueSection hE hg hφ x' = E.map (𝒳.val.p.map m₀).op (glueSection hE hg hφ x) := by
  refine eq_of_forall_map_eq hE (R := (hg x').choose ⊓ (hg x).choose.pullback (𝒳.val.p.map m₀))
    ((BigFppfOver.topology B S hS).intersection_covering (hg x').choose_spec.1
      ((BigFppfOver.topology B S hS).pullback_stable _ (hg x).choose_spec.1)) ?_
  rintro V k ⟨hk₁, hk₂⟩
  obtain ⟨i, y, m, hm⟩ := (hg x').choose_spec.2 hk₁
  have hm₀ : 𝒳.val.p.IsHomLift (𝒳.val.p.map m₀) m₀ := IsHomLift.map _ _
  have hcomp : 𝒳.val.p.IsHomLift (k ≫ 𝒳.val.p.map m₀) (m ≫ m₀) := inferInstance
  rw [map_glueSection hE hg hφ hk₁ m hm, ← Functor.map_comp_apply, ← op_comp,
    map_glueSection hE hg hφ hk₂ (m ≫ m₀) hcomp]

/-- **The glued 1-morphism.** -/
noncomputable def glueHom : 𝒳 ⟶ fibredCategory B S hS E :=
  homOfSections (glueSection hE hg hφ) (glueSection_naturality hE hg hφ)

/-- **The glued 1-morphism restricts to `φ i` along `g i`.** -/
theorem comp_glueHom (i : ι) : g i ≫ glueHom hE hg hφ = φ i := by
  refine hom_ext_of_obj B S hS fun y => ?_
  change (glueHom hE hg hφ).hom.obj ((g i).hom.obj y) = (φ i).hom.obj y
  have hb : ((φ i).hom.obj y).base = 𝒳.val.p.obj ((g i).hom.obj y) :=
    (base_obj_eq (φ i) y).trans (Functor.congr_obj (g i).hom.w y).symm
  refine PresheafOfCategories.obj_eq_of_elementOf_eq (P := E) rfl hb ?_
  change glueSection hE hg hφ ((g i).hom.obj y) = _
  refine eq_of_forall_map_eq hE (hg ((g i).hom.obj y)).choose_spec.1 fun V k hk => ?_
  obtain ⟨j, y'', m, hm⟩ := (hg ((g i).hom.obj y)).choose_spec.2 hk
  rw [map_glueSection hE hg hφ hk m hm]
  -- the lift `y` of itself, restricted along `k`
  have hid : 𝒳.val.p.IsHomLift (𝟙 (𝒳.val.p.obj ((g i).hom.obj y))) (𝟙 ((g i).hom.obj y)) :=
    inferInstance
  obtain ⟨y', n, hn, hcomp⟩ := exists_restrict_lift (𝟙 ((g i).hom.obj y)) hid k
  simp only [Category.comp_id] at hcomp
  rw [elementOf_eq_of_lifts hφ m ((g i).hom.map n) hm hcomp _ (base_φ_obj_eq (φ := φ) _ hcomp)]
  exact elementOf_eq_map_of_isHomLift (φ i) k n hn _ _

include hE hg in
/-- **Two 1-morphisms into a sheaf agreeing on a family which lifts objects locally are equal.** -/
theorem hom_ext_of_liftsLocally {F₁ F₂ : 𝒳 ⟶ fibredCategory B S hS E}
    (h : ∀ i, g i ≫ F₁ = g i ≫ F₂) : F₁ = F₂ := by
  refine hom_ext_of_obj B S hS fun x => ?_
  refine PresheafOfCategories.obj_eq_of_elementOf_eq (P := E) (base_obj_eq F₁ x) (base_obj_eq F₂ x)
    (eq_of_forall_map_eq hE (hg x).choose_spec.1 fun V k hk => ?_)
  obtain ⟨i, y, m, hm⟩ := (hg x).choose_spec.2 hk
  have hy (F : 𝒳 ⟶ fibredCategory B S hS E) : (F.hom.obj ((g i).hom.obj y)).base = V :=
    (base_obj_eq F _).trans (IsHomLift.domain_eq 𝒳.val.p k m)
  rw [← elementOf_eq_map_of_isHomLift F₁ k m hm (hy F₁) (base_obj_eq F₁ x),
    ← elementOf_eq_map_of_isHomLift F₂ k m hm (hy F₂) (base_obj_eq F₂ x)]
  exact elementOf_congr (congrArg (fun G => G.hom.obj y) (h i)) _ _

end Glue

end AlgebraicGeometry.Stack

end
