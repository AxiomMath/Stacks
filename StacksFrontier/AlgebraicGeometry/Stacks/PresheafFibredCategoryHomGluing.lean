module

public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStack
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuotientStackTransitionReindex
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.FiberIso
public import StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PullbackStackEquivalence
public import StacksFrontier.CategoryTheory.Sites.Stackification.UniversalPropertyGroupoid

/-!
# Gluing 1-morphisms out of the category attached to a presheaf

Let `Z` be a presheaf of sets on the big fppf site of `S` whose attached category fibred in
groupoids is a stack (for instance an algebraic space), let `U i ⊆ Z` be a family of
subpresheaves covering `Z` locally, and let `𝒳` be a stack in groupoids. Given 1-morphisms
`x i : U i ⟶ 𝒳` and 2-isomorphisms `φ i j : x i ≅ x j` over the intersections `U i ∩ U j`,
compatible on triple intersections, there is a 1-morphism `x : Z ⟶ 𝒳` whose restriction to
every `U i` is 2-isomorphic to `x i`.

## Main definitions

* `AlgebraicGeometry.Stack.fibredCategoryHomOfEq`: the morphism `(T', g^* z) ⟶ (T, z)` of the
  category attached to a presheaf.
* `AlgebraicGeometry.Stack.fibredCategorySubfunctorObj` and
  `AlgebraicGeometry.Stack.fibredCategorySubfunctorHom`: an object or morphism of the category
  attached to `Z` lying in a subpresheaf `U`, read in the category attached to `U`.

## Main results

* `AlgebraicGeometry.Stack.exists_hom_associatedMap_comp_iso_of_cocycle`: the gluing.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Stack

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Objects

variable {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The morphism of the category attached to a presheaf `Z` lying over `g : a.base ⟶ b.base`,
when the section at `a` is the restriction along `g` of the section at `b`. -/
def fibredCategoryHomOfEq {a b : (fibredCategory B S hS Z).val.obj} (g : a.base ⟶ b.base)
    (h : a.fiber.as = Z.map g.op b.fiber.as) : a ⟶ b :=
  ⟨g, Discrete.eqToHom h⟩

/-- The morphism `fibredCategoryHomOfEq g h` lies over `g`. -/
@[simp]
lemma fibredCategoryHomOfEq_base {a b : (fibredCategory B S hS Z).val.obj} (g : a.base ⟶ b.base)
    (h : a.fiber.as = Z.map g.op b.fiber.as) : (fibredCategoryHomOfEq g h).base = g :=
  rfl

/-- The section at the source of a morphism of the category attached to a presheaf is the
restriction of the section at its target. -/
lemma fibredCategory_fiber_eq {a b : (fibredCategory B S hS Z).val.obj} (m : a ⟶ b) :
    a.fiber.as = Z.map m.base.op b.fiber.as :=
  Discrete.eq_of_hom m.fiber

/-- Every morphism of the category attached to a presheaf is `fibredCategoryHomOfEq` of its
base. -/
lemma fibredCategory_eq_homOfEq {a b : (fibredCategory B S hS Z).val.obj} (m : a ⟶ b) :
    m = fibredCategoryHomOfEq m.base (fibredCategory_fiber_eq m) :=
  fibredCategory_hom_ext _ _ rfl

/-- The object `(T, z)` of the category attached to a subpresheaf `U ⊆ Z`, for an object `(T, z)`
of the category attached to `Z` with `z ∈ U(T)`. -/
abbrev fibredCategorySubfunctorObj (U : Subfunctor Z) (a : (fibredCategory B S hS Z).val.obj)
    (h : a.fiber.as ∈ U.obj (op a.base)) : (fibredCategory B S hS U.toFunctor).val.obj :=
  ⟨a.base, Discrete.mk ⟨a.fiber.as, h⟩⟩

/-- A morphism of the category attached to `Z` between objects lying in a subpresheaf `U`, read
in the category attached to `U`. -/
def fibredCategorySubfunctorHom (U : Subfunctor Z) {a b : (fibredCategory B S hS Z).val.obj}
    (m : a ⟶ b) (ha : a.fiber.as ∈ U.obj (op a.base)) (hb : b.fiber.as ∈ U.obj (op b.base)) :
    fibredCategorySubfunctorObj U a ha ⟶ fibredCategorySubfunctorObj U b hb :=
  fibredCategoryHomOfEq m.base (Subtype.ext (fibredCategory_fiber_eq m))

/-- The morphism `fibredCategorySubfunctorHom U m ha hb` lies over the base of `m`. -/
@[simp]
lemma fibredCategorySubfunctorHom_base (U : Subfunctor Z) {a b : (fibredCategory B S hS Z).val.obj}
    (m : a ⟶ b) (ha : a.fiber.as ∈ U.obj (op a.base)) (hb : b.fiber.as ∈ U.obj (op b.base)) :
    (fibredCategorySubfunctorHom U m ha hb).base = m.base :=
  rfl

/-- `fibredCategorySubfunctorHom` sends an identity to an identity. -/
lemma fibredCategorySubfunctorHom_id (U : Subfunctor Z) (a : (fibredCategory B S hS Z).val.obj)
    (ha : a.fiber.as ∈ U.obj (op a.base)) :
    fibredCategorySubfunctorHom U (𝟙 a) ha ha = 𝟙 _ :=
  fibredCategory_hom_ext _ _ rfl

/-- `fibredCategorySubfunctorHom` sends a composite to the composite. -/
lemma fibredCategorySubfunctorHom_comp (U : Subfunctor Z)
    {a b c : (fibredCategory B S hS Z).val.obj} (m : a ⟶ b) (m' : b ⟶ c)
    (ha : a.fiber.as ∈ U.obj (op a.base)) (hb : b.fiber.as ∈ U.obj (op b.base))
    (hc : c.fiber.as ∈ U.obj (op c.base)) :
    fibredCategorySubfunctorHom U (m ≫ m') ha hc =
      fibredCategorySubfunctorHom U m ha hb ≫ fibredCategorySubfunctorHom U m' hb hc :=
  fibredCategory_hom_ext _ _ rfl

/-- A section of `Z` at the source of a morphism lies in a subpresheaf whenever the section at its
target does. -/
lemma fibredCategory_mem_of_hom (U : Subfunctor Z) {a b : (fibredCategory B S hS Z).val.obj}
    (m : a ⟶ b) (hb : b.fiber.as ∈ U.obj (op b.base)) : a.fiber.as ∈ U.obj (op a.base) := by
  rw [fibredCategory_fiber_eq m]
  exact U.map m.base.op hb

end Objects

/-- If `b ≫ c = f ≫ e` and `a ≫ f = d`, then `(a ≫ b) ≫ c = d ≫ e`. -/
private lemma glue_comp_comp_eq {C : Type*} [Category C] {W X Y Y' Z : C} {a : W ⟶ X}
    {b : X ⟶ Y} {c : Y ⟶ Z} {f : X ⟶ Y'} {e : Y' ⟶ Z} {d : W ⟶ Y'} (h₁ : b ≫ c = f ≫ e)
    (h₂ : a ≫ f = d) : (a ≫ b) ≫ c = d ≫ e := by
  rw [Category.assoc, h₁, ← Category.assoc, h₂]

/-- A morphism of the category attached to a presheaf lies over its base. -/
private lemma isHomLift_base {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {a b : (fibredCategory B S hS Z).val.obj} (m : a ⟶ b) :
    (fibredCategory B S hS Z).val.p.IsHomLift m.base m :=
  IsHomLift.map _ _

section Glue

variable {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {ι : Type*} (U : ι → Subfunctor Z)

/-- The object of the category attached to `Z` underlying an object of the category attached to
the union of the `U i`. -/
abbrev unionObj (a : (fibredCategory B S hS (⨆ i, U i).toFunctor).val.obj) :
    (fibredCategory B S hS Z).val.obj :=
  ⟨a.base, Discrete.mk a.fiber.as.1⟩

/-- The morphism of the category attached to `Z` underlying a morphism of the category attached to
the union of the `U i`. -/
def unionHom {a b : (fibredCategory B S hS (⨆ i, U i).toFunctor).val.obj} (m : a ⟶ b) :
    unionObj U a ⟶ unionObj U b :=
  fibredCategoryHomOfEq m.base (congrArg Subtype.val (fibredCategory_fiber_eq m))

/-- `unionHom` sends an identity to an identity. -/
lemma unionHom_id (a : (fibredCategory B S hS (⨆ i, U i).toFunctor).val.obj) :
    unionHom U (𝟙 a) = 𝟙 _ :=
  fibredCategory_hom_ext _ _ rfl

/-- `unionHom` sends a composite to the composite. -/
lemma unionHom_comp {a b c : (fibredCategory B S hS (⨆ i, U i).toFunctor).val.obj} (m : a ⟶ b)
    (m' : b ⟶ c) : unionHom U (m ≫ m') = unionHom U m ≫ unionHom U m' :=
  fibredCategory_hom_ext _ _ rfl

/-- The section at an object of the category attached to the union of the `U i` lies in some
`U i`. -/
lemma exists_mem_of_mem_iSup (a : (fibredCategory B S hS (⨆ i, U i).toFunctor).val.obj) :
    ∃ i, a.fiber.as.1 ∈ (U i).obj (op a.base) := by
  simpa [Subfunctor.iSup_obj] using a.fiber.as.2

/-- A chosen index `i` with the section at `a` lying in `U i`. -/
noncomputable def glueIndex (a : (fibredCategory B S hS (⨆ i, U i).toFunctor).val.obj) : ι :=
  (exists_mem_of_mem_iSup U a).choose

/-- The section at `a` lies in `U (glueIndex U a)`. -/
lemma glueIndex_spec (a : (fibredCategory B S hS (⨆ i, U i).toFunctor).val.obj) :
    (unionObj U a).fiber.as ∈ (U (glueIndex U a)).obj (op (unionObj U a).base) :=
  (exists_mem_of_mem_iSup U a).choose_spec

variable {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
  (x : ∀ i, fibredCategory B S hS (U i).toFunctor ⟶ 𝒳)
  (φ : ∀ i j (a : (fibredCategory B S hS Z).val.obj) (hi : a.fiber.as ∈ (U i).obj (op a.base))
    (hj : a.fiber.as ∈ (U j).obj (op a.base)),
    (x i).hom.obj (fibredCategorySubfunctorObj (U i) a hi) ⟶
      (x j).hom.obj (fibredCategorySubfunctorObj (U j) a hj))

include φ in
/-- A self-transition satisfying the cocycle condition and lying over an identity is the
identity. -/
lemma glue_self_eq_id
    (hlift : ∀ i j a hi hj, 𝒳.val.p.IsHomLift (𝟙 a.base) (φ i j a hi hj))
    (hcoc : ∀ i j k a hi hj hk, φ i j a hi hj ≫ φ j k a hj hk = φ i k a hi hk)
    (i : ι) (a : (fibredCategory B S hS Z).val.obj) (hi : a.fiber.as ∈ (U i).obj (op a.base)) :
    φ i i a hi hi = 𝟙 _ := by
  have := hlift i i a hi hi
  have := 𝒳.isFiberedInGroupoids.isStronglyCartesian_homLift (𝟙 a.base) (φ i i a hi hi)
  have : IsIso (φ i i a hi hi) :=
    Functor.IsStronglyCartesian.isIso_of_base_isIso 𝒳.val.p (𝟙 a.base) (φ i i a hi hi)
  rw [← cancel_mono (φ i i a hi hi), Category.id_comp, hcoc]

/-- **The 1-morphism out of the union.** On an object of the category attached to `⋃ U i` it is
`x i` for the chosen index `i`, and on a morphism it is the transition `φ` to the index chosen at
the target followed by the image under `x` of that index. -/
noncomputable def glueFunctor
    (hlift : ∀ i j a hi hj, 𝒳.val.p.IsHomLift (𝟙 a.base) (φ i j a hi hj))
    (hnat : ∀ i j {a b : (fibredCategory B S hS Z).val.obj} (m : a ⟶ b) hai haj hbi hbj,
      (x i).hom.map (fibredCategorySubfunctorHom (U i) m hai hbi) ≫ φ i j b hbi hbj =
        φ i j a hai haj ≫ (x j).hom.map (fibredCategorySubfunctorHom (U j) m haj hbj))
    (hcoc : ∀ i j k a hi hj hk, φ i j a hi hj ≫ φ j k a hj hk = φ i k a hi hk) :
    (fibredCategory B S hS (⨆ i, U i).toFunctor).val.obj ⥤ 𝒳.val.obj where
  obj a := (x (glueIndex U a)).hom.obj
    (fibredCategorySubfunctorObj (U (glueIndex U a)) (unionObj U a) (glueIndex_spec U a))
  map {a b} m := φ (glueIndex U a) (glueIndex U b) (unionObj U a) (glueIndex_spec U a)
      (fibredCategory_mem_of_hom (U (glueIndex U b)) (unionHom U m) (glueIndex_spec U b)) ≫
    (x (glueIndex U b)).hom.map (fibredCategorySubfunctorHom (U (glueIndex U b)) (unionHom U m)
      (fibredCategory_mem_of_hom (U (glueIndex U b)) (unionHom U m) (glueIndex_spec U b))
      (glueIndex_spec U b))
  map_id a := by
    rw [glue_self_eq_id U x φ hlift hcoc, Category.id_comp]
    simp only [unionHom_id, fibredCategorySubfunctorHom_id]
    exact (x _).hom.map_id _
  map_comp {a b c} m m' := by
    simp only [Category.assoc]
    rw [reassoc_of% (hnat (glueIndex U b) (glueIndex U c) (unionHom U m) _ _ _ _),
      reassoc_of% (hcoc (glueIndex U a) (glueIndex U b) (glueIndex U c) (unionObj U a) _ _ _),
      ← Functor.map_comp, ← fibredCategorySubfunctorHom_comp, ← unionHom_comp]

/-- The structure functor of the category attached to a presheaf sends a morphism to the morphism
of the site it lies over. -/
lemma fibredCategory_p_map {Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {a b : (fibredCategory B S hS Z').val.obj} (m : a ⟶ b) :
    (fibredCategory B S hS Z').val.p.map m = m.base :=
  rfl

/-- **The 1-morphism out of the union lies over the site.** -/
lemma glueFunctor_comp_p
    (hlift : ∀ i j a hi hj, 𝒳.val.p.IsHomLift (𝟙 a.base) (φ i j a hi hj))
    (hnat : ∀ i j {a b : (fibredCategory B S hS Z).val.obj} (m : a ⟶ b) hai haj hbi hbj,
      (x i).hom.map (fibredCategorySubfunctorHom (U i) m hai hbi) ≫ φ i j b hbi hbj =
        φ i j a hai haj ≫ (x j).hom.map (fibredCategorySubfunctorHom (U j) m haj hbj))
    (hcoc : ∀ i j k a hi hj hk, φ i j a hi hj ≫ φ j k a hj hk = φ i k a hi hk) :
    glueFunctor U x φ hlift hnat hcoc ⋙ 𝒳.val.p =
      (fibredCategory B S hS (⨆ i, U i).toFunctor).val.p := by
  refine CategoryTheory.Functor.ext (fun a => Functor.congr_obj (x (glueIndex U a)).hom.w _) ?_
  intro a b m
  have h1 := hlift (glueIndex U a) (glueIndex U b) (unionObj U a) (glueIndex_spec U a)
    (fibredCategory_mem_of_hom (U (glueIndex U b)) (unionHom U m) (glueIndex_spec U b))
  have h1' : 𝒳.val.p.IsHomLift (𝟙 a.base) (φ (glueIndex U a) (glueIndex U b) (unionObj U a)
      (glueIndex_spec U a)
      (fibredCategory_mem_of_hom (U (glueIndex U b)) (unionHom U m) (glueIndex_spec U b))) := h1
  set rm := fibredCategorySubfunctorHom (U (glueIndex U b)) (unionHom U m)
    (fibredCategory_mem_of_hom (U (glueIndex U b)) (unionHom U m) (glueIndex_spec U b))
    (glueIndex_spec U b)
  have h2 : (fibredCategory B S hS (U (glueIndex U b)).toFunctor).val.p.IsHomLift m.base rm :=
    isHomLift_base rm
  have h2' : 𝒳.val.p.IsHomLift m.base ((x (glueIndex U b)).hom.map rm) :=
    BasedFunctor.preserves_isHomLift (x (glueIndex U b)).hom m.base rm
  have h3 : 𝒳.val.p.IsHomLift m.base ((glueFunctor U x φ hlift hnat hcoc).map m) := by
    change 𝒳.val.p.IsHomLift m.base (_ ≫ (x (glueIndex U b)).hom.map rm)
    exact @IsHomLift.comp_lift_id_left' _ _ _ _ 𝒳.val.p _ _ _ a.base _ h1' _ _ m.base _ h2'
  rw [Functor.comp_map, IsHomLift.fac' 𝒳.val.p m.base ((glueFunctor U x φ hlift hnat hcoc).map m),
    fibredCategory_p_map]
  simp
  rfl

/-- The inclusion of the union of the `U i` into `Z`, on attached categories. -/
abbrev unionInclusion :
    (fibredCategory B S hS (⨆ i, U i).toFunctor).val.obj ⥤ (fibredCategory B S hS Z).val.obj :=
  (associatedMap B S hS (⨆ i, U i).ι).1.hom.toFunctor

/-- The inclusion of the union of the `U i` into `Z` preserves the base of a morphism. -/
lemma unionInclusion_map_base {a b : (fibredCategory B S hS (⨆ i, U i).toFunctor).val.obj}
    (m : a ⟶ b) : ((unionInclusion U).map m).base = m.base :=
  rfl

/-- The inclusion of the union of the `U i` into `Z` is faithful on attached categories. -/
instance : (unionInclusion U).Faithful :=
  ⟨by
    intro _ _ m m' h
    have h' := congrArg Pseudofunctor.CoGrothendieck.Hom.base h
    exact fibredCategory_hom_ext _ _ h'⟩

/-- The inclusion of the union of the `U i` into `Z` is full on attached categories. -/
instance : (unionInclusion U).Full where
  map_surjective {_ _} n :=
    ⟨fibredCategoryHomOfEq n.base (Subtype.ext (fibredCategory_fiber_eq n)),
      fibredCategory_hom_ext _ _ rfl⟩

/-- The inclusion of the union is locally essentially surjective on fibres when the `U i` cover
`Z` locally. -/
lemma essImage_unionInclusion
    (hZ : (fibredCategory B S hS Z).val.p.IsStack (BigFppfOver.topology B S hS))
    (hcov : ∀ (T : BigFppfOver B S hS) (z : Z.obj (op T)), ∃ R ∈ BigFppfOver.topology B S hS T,
      ∀ ⦃V : BigFppfOver B S hS⦄ ⦃f : V ⟶ T⦄, R.arrows f → ∃ i, Z.map f.op z ∈ (U i).obj (op V)) :
    haveI : (fibredCategory B S hS Z).val.p.IsFibered := hZ.isFibered
    ∀ (T : BigFppfOver B S hS) (x' : (fibredCategory B S hS Z).val.p.Fiber T),
      ∃ R ∈ BigFppfOver.topology B S hS T, ∀ ⦃V : BigFppfOver B S hS⦄ ⦃f : V ⟶ T⦄, R.arrows f →
        (Functor.fiberFunctorOfCompEq (associatedMap B S hS (⨆ i, U i).ι).1.hom.w V).essImage
          (Functor.pullbackFiber _ x' f) := by
  have : (fibredCategory B S hS Z).val.p.IsFibered := hZ.isFibered
  rintro _ ⟨a, rfl⟩
  obtain ⟨R, hR, hRcov⟩ := hcov a.base a.fiber.as
  refine ⟨R, hR, fun V f hf => ?_⟩
  obtain ⟨i, hi⟩ := hRcov hf
  have hmem : Z.map f.op a.fiber.as ∈ (⨆ i, U i).obj (op V) := by
    rw [Subfunctor.iSup_obj]
    exact Set.mem_iUnion.2 ⟨i, hi⟩
  let y : (fibredCategory B S hS (⨆ i, U i).toFunctor).val.p.Fiber V :=
    ⟨⟨V, Discrete.mk ⟨Z.map f.op a.fiber.as, hmem⟩⟩, rfl⟩
  let c : (unionInclusion U).obj y.1 ⟶ a := fibredCategoryHomOfEq f rfl
  have hc : (fibredCategory B S hS Z).val.p.IsHomLift f c := isHomLift_base c
  have := (fibredCategory B S hS Z).isFiberedInGroupoids.isStronglyCartesian_homLift f c
  let e := Functor.IsCartesian.domainUniqueUpToIso (fibredCategory B S hS Z).val.p f
    (Functor.IsPreFibered.pullbackMap (p := (fibredCategory B S hS Z).val.p)
      (show (fibredCategory B S hS Z).val.p.obj a = (fibredCategory B S hS Z).val.p.obj a from rfl)
      f) c
  exact ⟨y, ⟨Functor.Fiber.isoMk e inferInstance⟩⟩

/-- The inclusion of the union of the `U i` into `Z` induces locally injective and locally
surjective maps on the presheaves of morphisms. -/
lemma morPresheafMap_unionInclusion
    (hZ : (fibredCategory B S hS Z).val.p.IsStack (BigFppfOver.topology B S hS)) :
    haveI : (fibredCategory B S hS (⨆ i, U i).toFunctor).val.p.IsFibered :=
      (fibredCategory B S hS (⨆ i, U i).toFunctor).isFiberedInGroupoids.isFibered
    haveI : (fibredCategory B S hS Z).val.p.IsFibered := hZ.isFibered
    ∀ (T : BigFppfOver B S hS) (a b : (fibredCategory B S hS (⨆ i, U i).toFunctor).val.p.Fiber T),
      Presheaf.IsLocallyInjective ((BigFppfOver.topology B S hS).over T)
          (((fibredCategory B S hS Z).isFiberedInGroupoids.isFibredOneMorphism
            (associatedMap B S hS (⨆ i, U i).ι).1.hom.w).morPresheafMap a b) ∧
        Presheaf.IsLocallySurjective ((BigFppfOver.topology B S hS).over T)
          (((fibredCategory B S hS Z).isFiberedInGroupoids.isFibredOneMorphism
            (associatedMap B S hS (⨆ i, U i).ι).1.hom.w).morPresheafMap a b) := by
  have : (fibredCategory B S hS (⨆ i, U i).toFunctor).val.p.IsFibered :=
    (fibredCategory B S hS (⨆ i, U i).toFunctor).isFiberedInGroupoids.isFibered
  have : (fibredCategory B S hS Z).val.p.IsFibered := hZ.isFibered
  intro T a b
  have : (unionInclusion U).Full := inferInstance
  have := Comma.isIso_morPresheafMap_of_fullyFaithful
    ((fibredCategory B S hS Z).isFiberedInGroupoids.isFibredOneMorphism
      (associatedMap B S hS (⨆ i, U i).ι).1.hom.w) a b
  exact ⟨inferInstance, inferInstance⟩

variable (hlift : ∀ i j a hi hj, 𝒳.val.p.IsHomLift (𝟙 a.base) (φ i j a hi hj))
  (hnat : ∀ i j {a b : (fibredCategory B S hS Z).val.obj} (m : a ⟶ b) hai haj hbi hbj,
    (x i).hom.map (fibredCategorySubfunctorHom (U i) m hai hbi) ≫ φ i j b hbi hbj =
      φ i j a hai haj ≫ (x j).hom.map (fibredCategorySubfunctorHom (U j) m haj hbj))
  (hcoc : ∀ i j k a hi hj hk, φ i j a hi hj ≫ φ j k a hj hk = φ i k a hi hk)

/-- The 1-morphism out of the union, as a 1-morphism of categories fibred in groupoids. -/
noncomputable def glueUnionHom : fibredCategory B S hS (⨆ i, U i).toFunctor ⟶ 𝒳 :=
  (CatFiberedInGroupoids.homEquivBasedFunctor _ _).symm
    ⟨glueFunctor U x φ hlift hnat hcoc, glueFunctor_comp_p U x φ hlift hnat hcoc⟩

/-- The object of the category attached to the union underlying an object of the category
attached to one `U i`. -/
abbrev glueMemberObj (i : ι) (c : (fibredCategory B S hS (U i).toFunctor).val.obj) :
    (fibredCategory B S hS (⨆ i, U i).toFunctor).val.obj :=
  ⟨c.base, Discrete.mk ⟨c.fiber.as.1, (le_iSup U i) _ c.fiber.as.2⟩⟩

/-- The transition from the chosen index to `i`, at an object of the category attached to
`U i`, as an isomorphism. -/
noncomputable def glueRestrictComponent
    (hlift : ∀ i j a hi hj, 𝒳.val.p.IsHomLift (𝟙 a.base) (φ i j a hi hj))
    (hcoc : ∀ i j k a hi hj hk, φ i j a hi hj ≫ φ j k a hj hk = φ i k a hi hk) (i : ι)
    (c : (fibredCategory B S hS (U i).toFunctor).val.obj) :
    (x (glueIndex U (glueMemberObj U i c))).hom.obj
        (fibredCategorySubfunctorObj (U (glueIndex U (glueMemberObj U i c)))
          (unionObj U (glueMemberObj U i c)) (glueIndex_spec U (glueMemberObj U i c))) ≅
      (x i).hom.obj c where
  hom := φ (glueIndex U (glueMemberObj U i c)) i (unionObj U (glueMemberObj U i c))
    (glueIndex_spec U (glueMemberObj U i c)) c.fiber.as.2
  inv := φ i (glueIndex U (glueMemberObj U i c)) (unionObj U (glueMemberObj U i c)) c.fiber.as.2
    (glueIndex_spec U (glueMemberObj U i c))
  hom_inv_id := (hcoc _ _ _ _ _ _ _).trans (glue_self_eq_id U x φ hlift hcoc _ _ _)
  inv_hom_id := (hcoc _ _ _ _ _ _ _).trans (glue_self_eq_id U x φ hlift hcoc _ _ _)

/-- The morphism of the category attached to the union underlying a morphism of the category
attached to one `U i`. -/
def glueMemberHom (i : ι) {c d : (fibredCategory B S hS (U i).toFunctor).val.obj} (m : c ⟶ d) :
    glueMemberObj U i c ⟶ glueMemberObj U i d :=
  fibredCategoryHomOfEq m.base (by
    have h := fibredCategory_fiber_eq m
    have h' : c.fiber.as.1 = Z.map m.base.op d.fiber.as.1 := congrArg Subtype.val h
    exact Subtype.ext h')

/-- The components `glueRestrictComponent` are natural with respect to morphisms of the category
attached to `U i`. -/
lemma glueFunctor_map_glueMemberHom_comp (i : ι)
    {c d : (fibredCategory B S hS (U i).toFunctor).val.obj} (m : c ⟶ d) :
    (glueFunctor U x φ hlift hnat hcoc).map (glueMemberHom U i m) ≫
        (glueRestrictComponent U x φ hlift hcoc i d).hom =
      (glueRestrictComponent U x φ hlift hcoc i c).hom ≫ (x i).hom.map m := by
  have hm := fibredCategory_mem_of_hom (U (glueIndex U (glueMemberObj U i d)))
    (unionHom U (glueMemberHom U i m)) (glueIndex_spec U (glueMemberObj U i d))
  refine glue_comp_comp_eq (f := φ (glueIndex U (glueMemberObj U i d)) i
      (unionObj U (glueMemberObj U i c)) hm c.fiber.as.2) ?_ ?_
  · have e2 : fibredCategorySubfunctorHom (U i) (unionHom U (glueMemberHom U i m)) c.fiber.as.2
        d.fiber.as.2 = m := fibredCategory_hom_ext _ _ rfl
    exact (hnat (glueIndex U (glueMemberObj U i d)) i (unionHom U (glueMemberHom U i m)) hm
      c.fiber.as.2 (glueIndex_spec U (glueMemberObj U i d)) d.fiber.as.2).trans
        (congrArg (fun t => _ ≫ (x i).hom.map t) e2)
  · exact hcoc (glueIndex U (glueMemberObj U i c)) (glueIndex U (glueMemberObj U i d)) i
      (unionObj U (glueMemberObj U i c)) (glueIndex_spec U (glueMemberObj U i c)) hm c.fiber.as.2

/-- **The restriction of the 1-morphism out of the union to one `U i` is `x i`.** -/
noncomputable def glueRestrictIso (i : ι) :
    (associatedMap B S hS (Subfunctor.homOfLe (le_iSup U i))).1 ≫
      glueUnionHom U x φ hlift hnat hcoc ≅ x i :=
  Bicategory.InducedBicategory.isoMk (BasedNatIso.mkNatIso
    (NatIso.ofComponents (fun c => glueRestrictComponent U x φ hlift hcoc i c)
      (fun m => glueFunctor_map_glueMemberHom_comp U x φ hlift hnat hcoc i m))
    (fun c => hlift (glueIndex U (glueMemberObj U i c)) i (unionObj U (glueMemberObj U i c))
      (glueIndex_spec U (glueMemberObj U i c)) c.fiber.as.2))

include φ hlift hnat hcoc in
/-- **Gluing 1-morphisms into a stack along a covering family of subpresheaves.** Let `Z` be a
presheaf on the big fppf site of `S` whose attached category is a stack, let `U i ⊆ Z` be
subpresheaves covering `Z` locally (every section of `Z` lies in some `U i` along a covering sieve)
and let `𝒳` be a stack in groupoids. Given 1-morphisms `x i : U i ⟶ 𝒳` and transitions
`φ i j : x i ⟶ x j` over `U i ∩ U j`, vertical, natural and satisfying the cocycle condition, there
is a 1-morphism `y : Z ⟶ 𝒳` whose restriction to every `U i` is 2-isomorphic to `x i`. -/
theorem exists_hom_associatedMap_comp_iso_of_cocycle
    (hZ : (fibredCategory B S hS Z).val.p.IsStack (BigFppfOver.topology B S hS))
    (h𝒳 : 𝒳.val.p.IsStack (BigFppfOver.topology B S hS))
    (hcov : ∀ (T : BigFppfOver B S hS) (z : Z.obj (op T)), ∃ R ∈ BigFppfOver.topology B S hS T,
      ∀ ⦃V : BigFppfOver B S hS⦄ ⦃f : V ⟶ T⦄, R.arrows f → ∃ i, Z.map f.op z ∈ (U i).obj (op V)) :
    ∃ y : fibredCategory B S hS Z ⟶ 𝒳,
      ∀ i, Nonempty ((associatedMap B S hS (U i).ι).1 ≫ y ≅ x i) := by
  have hext := Functor.Stackification.extendGroupoid_comp_eq
    (fibredCategory B S hS (⨆ i, U i).toFunctor).isFiberedInGroupoids
    (fibredCategory B S hS Z).isFiberedInGroupoids hZ 𝒳.isFiberedInGroupoids h𝒳
    (associatedMap B S hS (⨆ i, U i).ι).1.hom.w (glueFunctor_comp_p U x φ hlift hnat hcoc)
    (morPresheafMap_unionInclusion U hZ) (essImage_unionInclusion U hZ hcov)
  let y : fibredCategory B S hS Z ⟶ 𝒳 :=
    (CatFiberedInGroupoids.homEquivBasedFunctor _ _).symm ⟨_, hext⟩
  let eP : (associatedMap B S hS (⨆ i, U i).ι).1 ≫ y ≅ glueUnionHom U x φ hlift hnat hcoc :=
    Bicategory.InducedBicategory.isoMk (BasedNatIso.mkNatIso
      (Functor.Stackification.unitGroupoid
        (fibredCategory B S hS (⨆ i, U i).toFunctor).isFiberedInGroupoids
        (fibredCategory B S hS Z).isFiberedInGroupoids hZ 𝒳.isFiberedInGroupoids h𝒳
        (associatedMap B S hS (⨆ i, U i).ι).1.hom.w (glueFunctor_comp_p U x φ hlift hnat hcoc)
        (morPresheafMap_unionInclusion U hZ) (essImage_unionInclusion U hZ hcov))
      (Functor.Stackification.isHomLift_unitGroupoid_app
        (fibredCategory B S hS (⨆ i, U i).toFunctor).isFiberedInGroupoids
        (fibredCategory B S hS Z).isFiberedInGroupoids hZ 𝒳.isFiberedInGroupoids h𝒳
        (associatedMap B S hS (⨆ i, U i).ι).1.hom.w (glueFunctor_comp_p U x φ hlift hnat hcoc)
        (morPresheafMap_unionInclusion U hZ) (essImage_unionInclusion U hZ hcov)))
  refine ⟨y, fun i => ⟨?_⟩⟩
  have hc : (associatedMap B S hS (U i).ι).1 =
      (associatedMap B S hS (Subfunctor.homOfLe (le_iSup U i))).1 ≫
        (associatedMap B S hS (⨆ i, U i).ι).1 := by
    rw [← associatedMap_comp, Subfunctor.homOfLe_ι]
  exact eqToIso (congrArg (· ≫ y) hc) ≪≫ Bicategory.associator _ _ _ ≪≫
    Bicategory.whiskerLeftIso _ eP ≪≫ glueRestrictIso U x φ hlift hnat hcoc i

end Glue

end AlgebraicGeometry.Stack

end
