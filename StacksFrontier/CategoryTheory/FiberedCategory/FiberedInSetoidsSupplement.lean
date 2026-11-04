module

public import StacksFrontier.CategoryTheory.FiberedCategory.FiberedInSetoids
public import StacksFrontier.CategoryTheory.FiberedCategory.TwoFibreProduct
public import StacksFrontier.CategoryTheory.FiberedInSetoids.Defs
public import StacksFrontier.CategoryTheory.Sites.Stack.TwoFibreProductMorPresheafMap

/-!
# Supplement to `FiberedInSetoids`

The results of this module extend those of
`StacksFrontier.CategoryTheory.FiberedCategory.FiberedInSetoids`.
They use imports, universe variables or `open` declarations that the base module does not
have, and are kept in a module of their own so that its header is unchanged.

## Main results

* `isoClassFun`
* `isoClassFun_isoClassMk`
* `isoClassFun_naturality`
* `isoClassMapULift`
* `isoClassMapULift_app`
* `isoClassMapUniv`
* `isoClassMap_app`
* `isoClassMap_app_isoClassMk_univ`
* `isoClassMapOfCompEqUniv`
* `existsUnique_twoIso_of_isoClassMap_eq_univ`
* `isoClassLiftFiberUniv`
* `isoClassMk_isoClassLiftFiber_univ`
* `exists_isHomLift_isoClassLiftFiber_univ`
* `isoClassLiftMapUniv`
* `isHomLift_isoClassLiftMap_univ`
* `isoClassLiftFunctorUniv`
* `isoClassLiftFunctor_map_univ`
* `isoClassLiftFunctor_comp_eq_univ`
* `isoClassMk_fiberFunctorOfCompEq_isoClassLiftFunctor_univ`
* `isoClassMapOfCompEq_isoClassLiftFunctor_univ`
* `exists_oneMorphism_isoClassMap_eq_univ`
* `twoFibreProductFiberFstUniv`
* `twoFibreProductFiberSndUniv`
* `twoFibreProduct_hbase_compat_univ`
* `twoFibreProduct_square_univ`
* `twoFibreProductFiberHomMkUniv`
* `fiberInclusion_map_twoFibreProductFiberHomMk_a_univ`
* `fiberInclusion_map_twoFibreProductFiberHomMk_b_univ`
* `twoFibreProductFiberHomMk_comp_univ`
* `twoFibreProductFiberHomMk_id_univ`
* `exists_iso_of_twoFibreProduct_components_univ`
* and 6 further declarations.
-/

@[expose] public section

open Opposite

/-! ### The generalizations made by this development

The declarations below restate, under weaker hypotheses or at more general universes, declarations
of this file whose statements are kept as they are above. Each carries the name of the declaration
it generalizes with the suffix `_univ` (or `Univ` for a definition). -/

universe v₁ v₂ v₃ u₁ u₂ u₃ u₄

@[expose] public section

open Opposite

namespace CategoryTheory.Functor

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]

/-! ## The map of presheaves induced by a 1-morphism

The declarations from here on tie the hom universes of the categories over `𝒞` to that of `𝒞`
itself, since `CategoryTheory.Functor.fiberFunctorOfCompEq` and
`CategoryTheory.Functor.IsFibredOneMorphism.mapPullbackFiberIso`, which they reuse, are stated
that way.

The *object* universes, on the other hand, are independent. A 1-morphism induces a map
`Ob(𝒮_U)/≅ → Ob(𝒯_U)/≅` at each `U` whatever they are — that is
`CategoryTheory.Functor.isoClassFun` — but `CategoryTheory.Functor.isoClassPresheaf` is valued in
the object universe of the total category, so the two presheaves it compares live in one
functor category only when those universes agree. When they do not,
`CategoryTheory.Functor.isoClassMapULift` compares them after composing each with
`CategoryTheory.uliftFunctor` into the common universe.
-/

section IsoClassFun

variable {𝒮 : Type u₂} [Category.{v₂} 𝒮] {𝒯 : Type u₃} [Category.{v₂} 𝒯]

variable {p : 𝒮 ⥤ 𝒞} {q : 𝒯 ⥤ 𝒞}

variable [p.IsFibered] [q.IsFibered]

/-- The map `Ob(𝒮_U)/≅ → Ob(𝒯_U)/≅` induced at `U` by a 1-morphism `G` of fibred categories over
`𝒞`: on classes it is `[x] ↦ [G x]`. This is the underlying function of
`CategoryTheory.Functor.isoClassMapUniv`, available for total categories whose object universes are
independent, where that map of presheaves does not typecheck. -/
noncomputable def isoClassFun {G : 𝒮 ⥤ 𝒯} (hG : IsFibredOneMorphism p q G) (U : 𝒞) :
    _root_.Quotient (isIsomorphicSetoid (p.Fiber U)) →
      _root_.Quotient (isIsomorphicSetoid (q.Fiber U)) :=
  fun c => _root_.Quotient.liftOn c
    (fun x => isoClassMk q ((fiberFunctorOfCompEq hG.comp_eq U).obj x))
    (fun _ _ h => isoClassMk_eq_of_iso ((fiberFunctorOfCompEq hG.comp_eq U).mapIso
      ((isIsomorphicSetoid_r_iff _ _).1 h).some))

omit [p.IsFibered] [q.IsFibered] in
/-- `CategoryTheory.Functor.isoClassFun hG U` sends the class of `x` to the class of the image of
`x` under the fibre functor of `G` over `U`. -/
@[simp]
lemma isoClassFun_isoClassMk {G : 𝒮 ⥤ 𝒯} (hG : IsFibredOneMorphism p q G) {U : 𝒞}
    (x : p.Fiber U) : isoClassFun hG U (isoClassMk p x) =
      isoClassMk q ((fiberFunctorOfCompEq hG.comp_eq U).obj x) :=
  rfl

/-- `CategoryTheory.Functor.isoClassFun` commutes with restriction. This is the naturality of
`CategoryTheory.Functor.isoClassMapUniv`, written out on elements so that it holds for total
categories whose object universes are independent: it is the statement that `G` carries a
cartesian lift of `f` to a cartesian lift of `f`, the defining property of a 1-morphism of
fibred categories. -/
lemma isoClassFun_naturality {G : 𝒮 ⥤ 𝒯} (hG : IsFibredOneMorphism p q G) {U V : 𝒞} (f : V ⟶ U)
    (c : _root_.Quotient (isIsomorphicSetoid (p.Fiber U))) :
    isoClassFun hG V (p.isoClassPresheaf.map f.op c) =
      q.isoClassPresheaf.map f.op (isoClassFun hG U c) := by
  induction c using _root_.Quotient.ind with
  | _ x => exact (isoClassMk_eq_of_iso (hG.mapPullbackFiberIso x f)).symm

/-- The map of presheaves of isomorphism classes induced by a 1-morphism of fibred categories
over `𝒞` whose total categories have *independent* object universes, both presheaves having been
composed with `CategoryTheory.uliftFunctor` into the common universe `max u₂ u₃`.

`CategoryTheory.Functor.isoClassMapUniv` is this map when the two object universes agree; the
lift is what makes the source and the target objects of one functor category when they do not. -/
noncomputable def isoClassMapULift {G : 𝒮 ⥤ 𝒯} (hG : IsFibredOneMorphism p q G) :
    p.isoClassPresheaf ⋙ uliftFunctor.{u₃, u₂} ⟶
      q.isoClassPresheaf ⋙ uliftFunctor.{u₂, u₃} where
  app U := ↾fun c => ULift.up (isoClassFun hG U.unop c.down)
  naturality {_ _} f := by
    ext c
    exact congrArg ULift.up (isoClassFun_naturality hG f.unop c.down)

/-- `CategoryTheory.Functor.isoClassMapULift` is `CategoryTheory.Functor.isoClassFun` under the
universe lifts. -/
@[simp]
lemma isoClassMapULift_app {G : 𝒮 ⥤ 𝒯} (hG : IsFibredOneMorphism p q G) (U : 𝒞)
    (c : ULift.{u₃} (_root_.Quotient (isIsomorphicSetoid (p.Fiber U)))) :
    (isoClassMapULift hG).app (op U) c = ULift.up (isoClassFun hG U c.down) :=
  rfl

end IsoClassFun

section IsoClassMap

variable {𝒮 𝒯 : Type u₂} [Category.{v₂} 𝒮] [Category.{v₂} 𝒯]

variable {p : 𝒮 ⥤ 𝒞} {q : 𝒯 ⥤ 𝒞} [p.IsFibered] [q.IsFibered]

/-- The map `\overline{𝒮} ⟶ \overline{𝒯}` of presheaves of isomorphism classes induced by a
1-morphism `G` of fibred categories over `𝒞`: on classes it is `[x] ↦ [G x]`. Naturality is the
statement that `G` carries a cartesian lift of `f` to a cartesian lift of `f`, which is the
defining property of a 1-morphism of fibred categories. -/
noncomputable def isoClassMapUniv {G : 𝒮 ⥤ 𝒯} (hG : IsFibredOneMorphism p q G) :
    p.isoClassPresheaf ⟶ q.isoClassPresheaf where
  app U := ↾fun c => isoClassFun hG U.unop c
  naturality {_ _} f := by
    ext c
    exact isoClassFun_naturality hG f.unop c

/-- `CategoryTheory.Functor.isoClassMapUniv` is `CategoryTheory.Functor.isoClassFun`, the same
function read as a morphism of presheaves. -/
lemma isoClassMap_app {G : 𝒮 ⥤ 𝒯} (hG : IsFibredOneMorphism p q G) (U : 𝒞)
    (c : _root_.Quotient (isIsomorphicSetoid (p.Fiber U))) :
    (isoClassMapUniv hG).app (op U) c = isoClassFun hG U c :=
  rfl

/-- `CategoryTheory.Functor.isoClassMapUniv hG` sends the class of `x` to the class of the image of
`x` under the fibre functor of `G` over `U`. -/
@[simp]
lemma isoClassMap_app_isoClassMk_univ {G : 𝒮 ⥤ 𝒯} (hG : IsFibredOneMorphism p q G) {U : 𝒞}
    (x : p.Fiber U) : (isoClassMapUniv hG).app (op U) (isoClassMk p x) =
      isoClassMk q ((fiberFunctorOfCompEq hG.comp_eq U).obj x) :=
  rfl

/-- The map of presheaves of isomorphism classes induced by a functor over `𝒞` between categories
fibred in setoids. This is the functor `F` of Stacks 04SC on 1-morphisms. -/
noncomputable abbrev isoClassMapOfCompEqUniv [p.IsFiberedInSetoids] [hq : q.IsFiberedInSetoids]
    {G : 𝒮 ⥤ 𝒯} (hG : G ⋙ q = p) : p.isoClassPresheaf ⟶ q.isoClassPresheaf :=
  isoClassMapUniv ⟨hG, by
    intro _ _ f _ _ φ hφ
    have := hφ
    have := isHomLift_map_of_comp_eq hG f φ
    exact hq.isFiberedInGroupoids.isStronglyCartesian_homLift f (G.map φ)⟩

end IsoClassMap

/-! ## Stacks 04SC (1): rigidity of 1-morphisms of categories fibred in setoids -/

section TwoIso

variable {𝒮 𝒯 : Type u₂} [Category.{v₂} 𝒮] [Category.{v₂} 𝒯] {p : 𝒮 ⥤ 𝒞} {q : 𝒯 ⥤ 𝒞}
  [hp : p.IsFiberedInSetoids] [hq : q.IsFiberedInSetoids]

/-- **Stacks 04SC (1).** For two 1-morphisms `f, g : 𝒮₁ ⟶ 𝒮₂` of categories fibred in setoids
over `𝒞` with `F(f) = F(g)`, that is inducing the same map on the presheaves of isomorphism
classes of objects, there is a unique 2-isomorphism `f ⟶ g`. -/
theorem existsUnique_twoIso_of_isoClassMap_eq_univ {G H : 𝒮 ⥤ 𝒯} (hG : G ⋙ q = p) (hH : H ⋙ q = p)
    (h : isoClassMapOfCompEqUniv hG = isoClassMapOfCompEqUniv hH) :
    ∃! e : G ≅ H, ∀ x : 𝒮, q.IsHomLift (𝟙 (p.obj x)) (e.hom.app x) := by
  refine existsUnique_twoIso_of_forall_exists_vertical_hom hG hH fun x => ?_
  have hx := congrArg (fun t : p.isoClassPresheaf ⟶ q.isoClassPresheaf =>
    t.app (op (p.obj x)) (isoClassMk p (⟨x, rfl⟩ : p.Fiber (p.obj x)))) h
  obtain ⟨e⟩ := exists_iso_of_isoClassMk_eq hx
  exact ⟨Fiber.fiberInclusion.map e.hom, e.hom.2⟩

end TwoIso

/-! ## Stacks 04SC (2): every map of presheaves is induced by a 1-morphism -/

section Lift

variable {𝒮 𝒯 : Type u₂} [Category.{v₂} 𝒮] [Category.{v₂} 𝒯] {p : 𝒮 ⥤ 𝒞} {q : 𝒯 ⥤ 𝒞}
  [hp : p.IsFiberedInSetoids] [hq : q.IsFiberedInSetoids]
  (φ : p.isoClassPresheaf ⟶ q.isoClassPresheaf)

/-- A chosen object of the fibre of `q` over `p(x)` in the isomorphism class `φ([x])`. This is the
choice of representatives that turns a map of presheaves of isomorphism classes into a
1-morphism. -/
noncomputable def isoClassLiftFiberUniv (x : 𝒮) : q.Fiber (p.obj x) :=
  _root_.Quotient.out (φ.app (op (p.obj x)) (isoClassMk p ⟨x, rfl⟩))

/-- The chosen representative of `φ([x])` does lie in the class `φ([x])`. -/
@[simp]
lemma isoClassMk_isoClassLiftFiber_univ (x : 𝒮) :
    isoClassMk q (isoClassLiftFiberUniv φ x) = φ.app (op (p.obj x)) (isoClassMk p ⟨x, rfl⟩) :=
  _root_.Quotient.out_eq _

/-- The chosen representatives are related by a morphism over `p(ψ)` for every `ψ : x ⟶ y` of `𝒮`.
This is the heart of Stacks 04SC (2): as `𝒮` is fibred in groupoids, `ψ` is cartesian, so `[x]` is
the restriction of `[y]` along `p(ψ)`; applying `φ` and using its naturality, `φ([x])` is the
restriction of `φ([y])`, that is the class of a pullback of the chosen representative of
`φ([y])`. -/
lemma exists_isHomLift_isoClassLiftFiber_univ {x y : 𝒮} (ψ : x ⟶ y) :
    ∃ χ : (isoClassLiftFiberUniv φ x).1 ⟶ (isoClassLiftFiberUniv φ y).1,
      q.IsHomLift (p.map ψ) χ := by
  have hcart : p.IsCartesian (p.map ψ) ψ :=
    have := hp.isFiberedInGroupoids.isStronglyCartesian ψ
    inferInstance
  have hbase : isoClassMk p (⟨x, rfl⟩ : p.Fiber (p.obj x))
      = p.isoClassPresheaf.map (p.map ψ).op (isoClassMk p (⟨y, rfl⟩ : p.Fiber (p.obj y))) :=
    isoClassMk_eq_pullbackFiber_of_isCartesian (p.map ψ) ⟨y, rfl⟩ ⟨x, rfl⟩ ψ
      inferInstance hcart
  have key : isoClassMk q (isoClassLiftFiberUniv φ x)
      = isoClassMk q (pullbackFiber q (isoClassLiftFiberUniv φ y) (p.map ψ)) := by
    rw [isoClassMk_isoClassLiftFiber_univ, hbase,
      NatTrans.naturality_apply φ (p.map ψ).op (isoClassMk p (⟨y, rfl⟩ : p.Fiber (p.obj y))),
      ← isoClassMk_isoClassLiftFiber_univ φ y, isoClassPresheaf_map_isoClassMk]
  obtain ⟨e⟩ := exists_iso_of_isoClassMk_eq key
  refine ⟨Fiber.fiberInclusion.map e.hom ≫
    IsPreFibered.pullbackMap (isoClassLiftFiberUniv φ y).2 (p.map ψ), ?_⟩
  exact isHomLift_comp_of_isHomLift_id q (Fiber.fiberInclusion.map e.hom)
    (IsPreFibered.pullbackMap (isoClassLiftFiberUniv φ y).2 (p.map ψ)) (p.map ψ) e.hom.2
    (IsPreFibered.pullbackMap.IsCartesian (isoClassLiftFiberUniv φ y).2 (p.map ψ)).toIsHomLift

/-- The morphism of `𝒯` between the chosen representatives lying over `p(ψ)`. It is the *unique*
such morphism, since the fibres of `q` are thin; that is why it is functorial. -/
noncomputable def isoClassLiftMapUniv {x y : 𝒮} (ψ : x ⟶ y) :
    (isoClassLiftFiberUniv φ x).1 ⟶ (isoClassLiftFiberUniv φ y).1 :=
  (exists_isHomLift_isoClassLiftFiber_univ φ ψ).choose

/-- `CategoryTheory.Functor.isoClassLiftMapUniv φ ψ` lies over `p(ψ)`. -/
instance isHomLift_isoClassLiftMap_univ {x y : 𝒮} (ψ : x ⟶ y) :
    q.IsHomLift (p.map ψ) (isoClassLiftMapUniv φ ψ) :=
  (exists_isHomLift_isoClassLiftFiber_univ φ ψ).choose_spec

/-- The 1-morphism `𝒮 ⥤ 𝒯` over `𝒞` induced by a map of presheaves of isomorphism classes
(Stacks 04SC (2)). On objects it picks a representative of the image class; on morphisms it takes
the unique morphism of `𝒯` between the chosen representatives lying over the given morphism of
`𝒞`. Functoriality is that uniqueness. -/
noncomputable def isoClassLiftFunctorUniv : 𝒮 ⥤ 𝒯 where
  obj x := (isoClassLiftFiberUniv φ x).1
  map ψ := isoClassLiftMapUniv φ ψ
  map_id x := by
    have h2 : q.IsHomLift (p.map (𝟙 x)) (𝟙 (isoClassLiftFiberUniv φ x).1) := by
      rw [p.map_id]
      exact IsHomLift.id (isoClassLiftFiberUniv φ x).2
    exact hom_unique_of_isFiberedInSetoids (p.map (𝟙 x)) (isoClassLiftMapUniv φ (𝟙 x)) _
      (isHomLift_isoClassLiftMap_univ φ (𝟙 x)) h2
  map_comp ψ χ := by
    have h2 : q.IsHomLift (p.map (ψ ≫ χ)) (isoClassLiftMapUniv φ ψ ≫ isoClassLiftMapUniv φ χ) := by
      rw [p.map_comp]
      infer_instance
    exact hom_unique_of_isFiberedInSetoids (p.map (ψ ≫ χ)) (isoClassLiftMapUniv φ (ψ ≫ χ)) _
      (isHomLift_isoClassLiftMap_univ φ (ψ ≫ χ)) h2

/-- `CategoryTheory.Functor.isoClassLiftFunctorUniv φ` acts on morphisms by
`CategoryTheory.Functor.isoClassLiftMapUniv φ`. -/
@[simp]
lemma isoClassLiftFunctor_map_univ {x y : 𝒮} (ψ : x ⟶ y) :
    (isoClassLiftFunctorUniv φ).map ψ = isoClassLiftMapUniv φ ψ :=
  rfl

/-- The functor of `CategoryTheory.Functor.isoClassLiftFunctorUniv` is a 1-morphism over `𝒞`. -/
lemma isoClassLiftFunctor_comp_eq_univ : isoClassLiftFunctorUniv φ ⋙ q = p := by
  refine Functor.ext (fun x => (isoClassLiftFiberUniv φ x).2) fun _ _ ψ => ?_
  exact IsHomLift.fac' q (p.map ψ) (isoClassLiftMapUniv φ ψ)

/-- At an object of an arbitrary fibre, the class of the image under
`CategoryTheory.Functor.isoClassLiftFunctorUniv` is the value of `φ`. -/
lemma isoClassMk_fiberFunctorOfCompEq_isoClassLiftFunctor_univ {U : 𝒞} (x : p.Fiber U) :
    isoClassMk q ((fiberFunctorOfCompEq (isoClassLiftFunctor_comp_eq_univ φ) U).obj x)
      = φ.app (op U) (isoClassMk p x) := by
  obtain ⟨a, rfl⟩ := x
  exact isoClassMk_isoClassLiftFiber_univ φ a

/-- `CategoryTheory.Functor.isoClassLiftFunctorUniv` induces the given map of presheaves of
isomorphism classes. -/
lemma isoClassMapOfCompEq_isoClassLiftFunctor_univ :
    isoClassMapOfCompEqUniv (isoClassLiftFunctor_comp_eq_univ φ) = φ := by
  ext U c
  obtain ⟨U⟩ := U
  induction c using _root_.Quotient.ind with
  | _ x => exact isoClassMk_fiberFunctorOfCompEq_isoClassLiftFunctor_univ φ x

/-- **Stacks 04SC (2).** Every morphism `h : F(𝒮₁) ⟶ F(𝒮₂)` of presheaves of isomorphism classes
is `F(f)` for a 1-morphism `f : 𝒮₁ ⟶ 𝒮₂` of categories fibred in setoids over `𝒞`. -/
theorem exists_oneMorphism_isoClassMap_eq_univ :
    ∃ (G : 𝒮 ⥤ 𝒯) (hG : G ⋙ q = p), isoClassMapOfCompEqUniv hG = φ :=
  ⟨isoClassLiftFunctorUniv φ, isoClassLiftFunctor_comp_eq_univ φ,
    isoClassMapOfCompEq_isoClassLiftFunctor_univ φ⟩

end Lift

/-! ## Stacks 04SC (3): a category fibred in sets is its own image under `F` -/

/-! ## Stacks 04SD: the construction is compatible with 2-fibre products -/

section TwoFibreProduct

variable {𝒳 : Type u₂} {𝒴 : Type u₃} {𝒵 : Type u₄}
  [Category.{v₂} 𝒳] [Category.{v₂} 𝒴] [Category.{v₂} 𝒵]
  (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (p𝒵 : 𝒵 ⥤ 𝒞) (F : 𝒳 ⥤ 𝒵) (G : 𝒴 ⥤ 𝒵)

/-- The functor from the fibre of the 2-fibre product `𝒳 ×_𝒵 𝒴` over `U` to the fibre of `𝒳`
over `U`, induced by the first projection. -/
def twoFibreProductFiberFstUniv (U : 𝒞) :
    (TwoFibreProductOver.structureFunctor p𝒳 p𝒴 p𝒵 F G).Fiber U ⥤ p𝒳.Fiber U :=
  fiberFunctorOfCompEq TwoFibreProductOver.fst_comp_eq U

/-- The functor from the fibre of the 2-fibre product `𝒳 ×_𝒵 𝒴` over `U` to the fibre of `𝒴`
over `U`, induced by the second projection. -/
def twoFibreProductFiberSndUniv (U : 𝒞) :
    (TwoFibreProductOver.structureFunctor p𝒳 p𝒴 p𝒵 F G).Fiber U ⥤ p𝒴.Fiber U :=
  fiberFunctorOfCompEq TwoFibreProductOver.snd_comp_eq U

variable {p𝒳 p𝒴 p𝒵 F G}

/-- The comparison isomorphism of an object of a fibre of the 2-fibre product is vertical. -/
private lemma isHomLift_iso_hom_of_fiber {U : 𝒞}
    (A : (TwoFibreProductOver.structureFunctor p𝒳 p𝒴 p𝒵 F G).Fiber U) :
    p𝒵.IsHomLift (𝟙 U) A.1.iso.hom := by
  obtain ⟨P, hP⟩ := A
  subst hP
  exact P.vertical

section

variable [hp𝒵 : p𝒵.IsFiberedInSetoids]
  (hF : IsFibredOneMorphism p𝒳 p𝒵 F) (hG : IsFibredOneMorphism p𝒴 p𝒵 G)

omit hp𝒵 in
/-- The base compatibility condition of `CategoryTheory.TwoFibreProductOver.Hom.mk'` for a pair of
morphisms of the component fibres over `U`: both induce the same morphism of `𝒞`, since both lie
over `𝟙 U`. -/
lemma twoFibreProduct_hbase_compat_univ {U : 𝒞}
    {A B : (TwoFibreProductOver.structureFunctor p𝒳 p𝒴 p𝒵 F G).Fiber U}
    (γ : (twoFibreProductFiberFstUniv p𝒳 p𝒴 p𝒵 F G U).obj A ⟶
      (twoFibreProductFiberFstUniv p𝒳 p𝒴 p𝒵 F G U).obj B)
    (δ : (twoFibreProductFiberSndUniv p𝒳 p𝒴 p𝒵 F G U).obj A ⟶
      (twoFibreProductFiberSndUniv p𝒳 p𝒴 p𝒵 F G U).obj B) :
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
lemma twoFibreProduct_square_univ {U : 𝒞}
    {A B : (TwoFibreProductOver.structureFunctor p𝒳 p𝒴 p𝒵 F G).Fiber U}
    (γ : (twoFibreProductFiberFstUniv p𝒳 p𝒴 p𝒵 F G U).obj A ⟶
      (twoFibreProductFiberFstUniv p𝒳 p𝒴 p𝒵 F G U).obj B)
    (δ : (twoFibreProductFiberSndUniv p𝒳 p𝒴 p𝒵 F G U).obj A ⟶
      (twoFibreProductFiberSndUniv p𝒳 p𝒴 p𝒵 F G U).obj B) :
    F.map (Fiber.fiberInclusion.map γ) ≫ B.1.iso.hom
      = A.1.iso.hom ≫ G.map (Fiber.fiberInclusion.map δ) := by
  refine hom_unique_of_fiber_isThin p𝒵 (𝟙 U) (hp𝒵.fiber_isThin U) _ _ ?_ ?_
  · exact isHomLift_id_comp p𝒵 _ _
      (isHomLift_map_of_comp_eq_general hF.comp_eq (𝟙 U) (Fiber.fiberInclusion.map γ) γ.2)
      (isHomLift_iso_hom_of_fiber B)
  · exact isHomLift_id_comp p𝒵 _ _ (isHomLift_iso_hom_of_fiber A)
      (isHomLift_map_of_comp_eq_general hG.comp_eq (𝟙 U) (Fiber.fiberInclusion.map δ) δ.2)

include hF hG in
/-- The morphism of the fibre of the 2-fibre product over `U` determined by a pair of morphisms of
the component fibres. Because `𝒵` is fibred in setoids there is no further condition to impose:
the comparison square commutes automatically. -/
def twoFibreProductFiberHomMkUniv {U : 𝒞}
    {A B : (TwoFibreProductOver.structureFunctor p𝒳 p𝒴 p𝒵 F G).Fiber U}
    (γ : (twoFibreProductFiberFstUniv p𝒳 p𝒴 p𝒵 F G U).obj A ⟶
      (twoFibreProductFiberFstUniv p𝒳 p𝒴 p𝒵 F G U).obj B)
    (δ : (twoFibreProductFiberSndUniv p𝒳 p𝒴 p𝒵 F G U).obj A ⟶
      (twoFibreProductFiberSndUniv p𝒳 p𝒴 p𝒵 F G U).obj B) : A ⟶ B :=
  ⟨TwoFibreProductOver.Hom.mk' (Fiber.fiberInclusion.map γ) (Fiber.fiberInclusion.map δ)
      (twoFibreProduct_hbase_compat_univ γ δ) (twoFibreProduct_square_univ hF hG γ δ), by
    refine IsHomLift.of_fac' (TwoFibreProductOver.structureFunctor p𝒳 p𝒴 p𝒵 F G) (𝟙 U) _
      A.2 B.2 ?_
    change eqToHom A.1.hx.symm ≫ p𝒳.map (Fiber.fiberInclusion.map γ) ≫ eqToHom B.1.hx
      = eqToHom A.2 ≫ 𝟙 U ≫ eqToHom B.2.symm
    refine Eq.trans (eqToHom_comp_map_comp_eqToHom p𝒳 (Fiber.fiberInclusion.map γ) γ.2
      A.1.hx B.1.hx (A.2.trans B.2.symm)) ?_
    simp only [Category.id_comp, eqToHom_trans]
    rfl⟩

include hF hG in
/-- The `𝒳`-component of `CategoryTheory.Functor.twoFibreProductFiberHomMkUniv hF hG γ δ` is
`γ`. -/
@[simp]
lemma fiberInclusion_map_twoFibreProductFiberHomMk_a_univ {U : 𝒞}
    {A B : (TwoFibreProductOver.structureFunctor p𝒳 p𝒴 p𝒵 F G).Fiber U}
    (γ : (twoFibreProductFiberFstUniv p𝒳 p𝒴 p𝒵 F G U).obj A ⟶
      (twoFibreProductFiberFstUniv p𝒳 p𝒴 p𝒵 F G U).obj B)
    (δ : (twoFibreProductFiberSndUniv p𝒳 p𝒴 p𝒵 F G U).obj A ⟶
      (twoFibreProductFiberSndUniv p𝒳 p𝒴 p𝒵 F G U).obj B) :
    (Fiber.fiberInclusion.map (twoFibreProductFiberHomMkUniv hF hG γ δ)).a
      = Fiber.fiberInclusion.map γ :=
  rfl

include hF hG in
/-- The `𝒴`-component of `CategoryTheory.Functor.twoFibreProductFiberHomMkUniv hF hG γ δ` is
`δ`. -/
@[simp]
lemma fiberInclusion_map_twoFibreProductFiberHomMk_b_univ {U : 𝒞}
    {A B : (TwoFibreProductOver.structureFunctor p𝒳 p𝒴 p𝒵 F G).Fiber U}
    (γ : (twoFibreProductFiberFstUniv p𝒳 p𝒴 p𝒵 F G U).obj A ⟶
      (twoFibreProductFiberFstUniv p𝒳 p𝒴 p𝒵 F G U).obj B)
    (δ : (twoFibreProductFiberSndUniv p𝒳 p𝒴 p𝒵 F G U).obj A ⟶
      (twoFibreProductFiberSndUniv p𝒳 p𝒴 p𝒵 F G U).obj B) :
    (Fiber.fiberInclusion.map (twoFibreProductFiberHomMkUniv hF hG γ δ)).b
      = Fiber.fiberInclusion.map δ :=
  rfl

include hF hG in
/-- The construction of `CategoryTheory.Functor.twoFibreProductFiberHomMkUniv` is compatible with
composition, hence carries a pair of isomorphisms to an isomorphism. -/
lemma twoFibreProductFiberHomMk_comp_univ {U : 𝒞}
    {A B C : (TwoFibreProductOver.structureFunctor p𝒳 p𝒴 p𝒵 F G).Fiber U}
    (γ : (twoFibreProductFiberFstUniv p𝒳 p𝒴 p𝒵 F G U).obj A ⟶
      (twoFibreProductFiberFstUniv p𝒳 p𝒴 p𝒵 F G U).obj B)
    (δ : (twoFibreProductFiberSndUniv p𝒳 p𝒴 p𝒵 F G U).obj A ⟶
      (twoFibreProductFiberSndUniv p𝒳 p𝒴 p𝒵 F G U).obj B)
    (γ' : (twoFibreProductFiberFstUniv p𝒳 p𝒴 p𝒵 F G U).obj B ⟶
      (twoFibreProductFiberFstUniv p𝒳 p𝒴 p𝒵 F G U).obj C)
    (δ' : (twoFibreProductFiberSndUniv p𝒳 p𝒴 p𝒵 F G U).obj B ⟶
      (twoFibreProductFiberSndUniv p𝒳 p𝒴 p𝒵 F G U).obj C) :
    twoFibreProductFiberHomMkUniv hF hG γ δ ≫ twoFibreProductFiberHomMkUniv hF hG γ' δ'
      = twoFibreProductFiberHomMkUniv hF hG (γ ≫ γ') (δ ≫ δ') :=
  Fiber.hom_ext (TwoFibreProductOver.Hom.ext' rfl rfl)

include hF hG in
/-- `CategoryTheory.Functor.twoFibreProductFiberHomMkUniv` of the identities is the identity. -/
lemma twoFibreProductFiberHomMk_id_univ {U : 𝒞}
    (A : (TwoFibreProductOver.structureFunctor p𝒳 p𝒴 p𝒵 F G).Fiber U) :
    twoFibreProductFiberHomMkUniv hF hG (𝟙 ((twoFibreProductFiberFstUniv p𝒳 p𝒴 p𝒵 F G U).obj A))
      (𝟙 ((twoFibreProductFiberSndUniv p𝒳 p𝒴 p𝒵 F G U).obj A)) = 𝟙 A :=
  Fiber.hom_ext (TwoFibreProductOver.Hom.ext' rfl rfl)

include hF hG in
/-- Two objects of the fibre of the 2-fibre product over `U` whose components are isomorphic in
the fibres of `𝒳` and of `𝒴` are themselves isomorphic. This is the injectivity half of
Stacks 04SD. -/
lemma exists_iso_of_twoFibreProduct_components_univ {U : 𝒞}
    {A B : (TwoFibreProductOver.structureFunctor p𝒳 p𝒴 p𝒵 F G).Fiber U}
    (α : (twoFibreProductFiberFstUniv p𝒳 p𝒴 p𝒵 F G U).obj A ≅
      (twoFibreProductFiberFstUniv p𝒳 p𝒴 p𝒵 F G U).obj B)
    (β : (twoFibreProductFiberSndUniv p𝒳 p𝒴 p𝒵 F G U).obj A ≅
      (twoFibreProductFiberSndUniv p𝒳 p𝒴 p𝒵 F G U).obj B) : Nonempty (A ≅ B) :=
  ⟨{ hom := twoFibreProductFiberHomMkUniv hF hG α.hom β.hom
     inv := twoFibreProductFiberHomMkUniv hF hG α.inv β.inv
     hom_inv_id := by
       rw [twoFibreProductFiberHomMk_comp_univ, α.hom_inv_id, β.hom_inv_id,
         twoFibreProductFiberHomMk_id_univ]
     inv_hom_id := by
       rw [twoFibreProductFiberHomMk_comp_univ, α.inv_hom_id, β.inv_hom_id,
         twoFibreProductFiberHomMk_id_univ] }⟩

end

section

variable [p𝒳.IsFibered] [p𝒴.IsFibered] [hp𝒵 : p𝒵.IsFiberedInSetoids]
  (hF : IsFibredOneMorphism p𝒳 p𝒵 F) (hG : IsFibredOneMorphism p𝒴 p𝒵 G)

/-- The two components of an object of the fibre of the 2-fibre product over `U` have the same
image in `Ob(𝒵_U)/≅`: the comparison isomorphism of the object is an isomorphism of the fibre
over `U` between their images. -/
lemma isoClassMk_twoFibreProduct_compat_univ {U : 𝒞}
    (P : (TwoFibreProductOver.structureFunctor p𝒳 p𝒴 p𝒵 F G).Fiber U) :
    isoClassFun hF U (isoClassMk p𝒳 ((twoFibreProductFiberFstUniv p𝒳 p𝒴 p𝒵 F G U).obj P))
      = isoClassFun hG U
        (isoClassMk p𝒴 ((twoFibreProductFiberSndUniv p𝒳 p𝒴 p𝒵 F G U).obj P)) :=
  isoClassMk_eq_of_iso (Fiber.isoMk P.1.iso (isHomLift_iso_hom_of_fiber P))

/-- The map of Stacks 04SD at `U`: the isomorphism class of an object of the fibre of the
2-fibre product `𝒳 ×_𝒵 𝒴` over `U` goes to the pair of the isomorphism classes of its two
components, which have the same image in `Ob(𝒵_U)/≅`. -/
def twoFibreProductIsoClassMapUniv (U : 𝒞) :
    _root_.Quotient
        (isIsomorphicSetoid
          ((TwoFibreProductOver.structureFunctor p𝒳 p𝒴 p𝒵 F G).Fiber U)) →
      {ab : _root_.Quotient (isIsomorphicSetoid (p𝒳.Fiber U)) ×
            _root_.Quotient (isIsomorphicSetoid (p𝒴.Fiber U)) //
          isoClassFun hF U ab.1 = isoClassFun hG U ab.2} :=
  fun c => _root_.Quotient.liftOn c
    (fun P => ⟨(isoClassMk p𝒳 ((twoFibreProductFiberFstUniv p𝒳 p𝒴 p𝒵 F G U).obj P),
        isoClassMk p𝒴 ((twoFibreProductFiberSndUniv p𝒳 p𝒴 p𝒵 F G U).obj P)),
      isoClassMk_twoFibreProduct_compat_univ hF hG P⟩)
    (fun _ _ h => by
      refine Subtype.ext (Prod.ext ?_ ?_)
      · exact isoClassMk_eq_of_iso ((twoFibreProductFiberFstUniv p𝒳 p𝒴 p𝒵 F G U).mapIso
          ((isIsomorphicSetoid_r_iff _ _).1 h).some)
      · exact isoClassMk_eq_of_iso ((twoFibreProductFiberSndUniv p𝒳 p𝒴 p𝒵 F G U).mapIso
          ((isIsomorphicSetoid_r_iff _ _).1 h).some))

/-- **Stacks 04SD**, injectivity. -/
lemma twoFibreProductIsoClassMap_injective_univ (U : 𝒞) :
    Function.Injective (twoFibreProductIsoClassMapUniv hF hG U) := by
  intro c c' h
  induction c using _root_.Quotient.ind with
  | _ P =>
    induction c' using _root_.Quotient.ind with
    | _ Q =>
      obtain ⟨α⟩ := exists_iso_of_isoClassMk_eq (congrArg (fun z => z.val.fst) h)
      obtain ⟨β⟩ := exists_iso_of_isoClassMk_eq (congrArg (fun z => z.val.snd) h)
      obtain ⟨e⟩ := exists_iso_of_twoFibreProduct_components_univ hF hG α β
      exact isoClassMk_eq_of_iso e

/-- **Stacks 04SD**, surjectivity: a pair of isomorphism classes with the same image in
`Ob(𝒵_U)/≅` is the pair of components of an object of the 2-fibre product, built from a chosen
vertical isomorphism between chosen representatives. -/
lemma twoFibreProductIsoClassMap_surjective_univ (U : 𝒞) :
    Function.Surjective (twoFibreProductIsoClassMapUniv hF hG U) := by
  rintro ⟨⟨c₁, c₂⟩, hc⟩
  obtain ⟨x, rfl⟩ := isoClassMk_surjective c₁
  obtain ⟨y, rfl⟩ := isoClassMk_surjective c₂
  obtain ⟨e⟩ := exists_iso_of_isoClassMk_eq hc
  refine ⟨isoClassMk _ ⟨TwoFibreProductOver.mk U x.1 y.1 x.2 y.2
    (Fiber.fiberInclusion.mapIso e) e.hom.2, rfl⟩, ?_⟩
  refine Subtype.ext (Prod.ext ?_ ?_)
  · exact congrArg (isoClassMk p𝒳) (Subtype.ext rfl)
  · exact congrArg (isoClassMk p𝒴) (Subtype.ext rfl)

/-- **Stacks 04SD.** The presheaf attached by Stacks 04SC to a 2-fibre product `𝒳 ×_𝒵 𝒴` over `𝒞`
is the fibre product of the presheaves attached to `𝒳`, `𝒴` and `𝒵`: at every object `U` of `𝒞`,
`Ob((𝒳 ×_𝒵 𝒴)_U)/≅ = Ob(𝒳_U)/≅ ×_{Ob(𝒵_U)/≅} Ob(𝒴_U)/≅`, by the bijection sending the class of
an object to the pair of the classes of its components. This is the display to which the source's
proof reduces the lemma. -/
noncomputable def twoFibreProductIsoClassEquivUniv (U : 𝒞) :
    _root_.Quotient
        (isIsomorphicSetoid
          ((TwoFibreProductOver.structureFunctor p𝒳 p𝒴 p𝒵 F G).Fiber U)) ≃
      {ab : _root_.Quotient (isIsomorphicSetoid (p𝒳.Fiber U)) ×
            _root_.Quotient (isIsomorphicSetoid (p𝒴.Fiber U)) //
          isoClassFun hF U ab.1 = isoClassFun hG U ab.2} :=
  Equiv.ofBijective _
    ⟨twoFibreProductIsoClassMap_injective_univ hF hG U,
      twoFibreProductIsoClassMap_surjective_univ hF hG U⟩

/-- **Stacks 04SD**, naturality: the bijection of
`CategoryTheory.Functor.twoFibreProductIsoClassEquivUniv` commutes with restriction along a
morphism of `𝒞`, so it is an isomorphism of presheaves and not merely a family of bijections. -/
lemma twoFibreProductIsoClassMap_naturality_univ
    [(TwoFibreProductOver.structureFunctor p𝒳 p𝒴 p𝒵 F G).IsFibered] {V U : 𝒞} (f : V ⟶ U)
    (c : (TwoFibreProductOver.structureFunctor p𝒳 p𝒴 p𝒵 F G).isoClassPresheaf.obj (op U)) :
    (twoFibreProductIsoClassMapUniv hF hG V
        ((TwoFibreProductOver.structureFunctor p𝒳 p𝒴 p𝒵 F G).isoClassPresheaf.map f.op c)).val =
      (p𝒳.isoClassPresheaf.map f.op (twoFibreProductIsoClassMapUniv hF hG U c).val.fst,
        p𝒴.isoClassPresheaf.map f.op (twoFibreProductIsoClassMapUniv hF hG U c).val.snd) := by
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
