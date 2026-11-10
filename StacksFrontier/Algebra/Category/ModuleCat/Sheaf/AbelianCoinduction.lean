module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Module.Shrink
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import Mathlib.CategoryTheory.Sites.SheafHom

/-!
# The right adjoint of forgetting a sheaf of modules to an abelian sheaf

Let `R` be a sheaf of rings on a site `(C, J)` and `G` an abelian sheaf on it. The sheaf of
`R`-modules *coinduced* by `G` has sections over `V` the morphisms of abelian presheaves
`R|_V ⟶ G|_V` on the slice `C/V`, an `R(V)`-module through multiplication on the source. It
corepresents additive maps into `G`: a morphism of abelian sheaves `N ⟶ G` out of the underlying
abelian sheaf of a sheaf of `R`-modules `N` is the same thing as a morphism of sheaves of
`R`-modules from `N` to the coinduced module, the section `n` over `V` being sent to
`r ↦ φ(r · n)` on `C/V`.

## Main definitions

* `Stacks.SheafOfModules.AbelianCoinduction.Hom`: the sections over `V`, the additive morphisms
  `R|_V ⟶ G|_V`, with their `R(V)`-module structure.
* `Stacks.SheafOfModules.AbelianCoinduction.obj`: the coinduced sheaf of modules.
* `Stacks.SheafOfModules.AbelianCoinduction.homEquiv`: morphisms of abelian sheaves out of the
  underlying abelian sheaf of `N` are morphisms of sheaves of modules into the coinduced module.

## Main results

* `Stacks.SheafOfModules.AbelianCoinduction.isSheaf_presheaf`: the coinduced presheaf is a sheaf.
* `Stacks.SheafOfModules.AbelianCoinduction.sec_homEquiv`: the value of the bijection on
  sections, `n ↦ (r ↦ φ(r • n|_W))`.

## Implementation notes

The morphisms `R|_V ⟶ G|_V` form a type in the universe of the objects of the site, which can be
larger than the universe of the module sections; the sections of the coinduced module are those
morphisms shrunk (`Shrink`) to the module universe, which needs them to be small there. That is
carried as the hypothesis that the presheaf categories of the slices are locally small at the
module universe, which holds on every essentially small site. The sheaf condition is Mathlib's
`CategoryTheory.Presheaf.IsSheaf.hom`.

The `R(V)`-module structure is precomposition with right multiplication by the restrictions of a
section `f ∈ R(V)`, so that `f • (g • β) = (f * g) • β` holds with no commutativity assumption.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe w u₁ v₁

/-- A functor category out of an essentially small category into a locally small one is locally
small. -/
theorem CategoryTheory.locallySmall_functor_of_essentiallySmall.{w', ua, va} (I : Type*)
    [Category I] [EssentiallySmall.{w'} I] (A : Type ua) [Category.{va} A] [LocallySmall.{w'} A] :
    LocallySmall.{w'} (I ⥤ A) :=
  (locallySmall_congr ((equivSmallModel.{w'} I).congrLeft (E := A))).2 inferInstance

namespace Stacks.SheafOfModules.AbelianCoinduction

variable {C : Type u₁} [Category.{v₁} C]

section Presheaf

variable (R : Cᵒᵖ ⥤ RingCat.{w}) (G : Cᵒᵖ ⥤ AddCommGrpCat.{w})

/-- The underlying presheaf of abelian groups of a presheaf of rings, with the additive group of
`R(X)` as its value at `X`. -/
@[simps]
def ab : Cᵒᵖ ⥤ AddCommGrpCat.{w} where
  obj X := AddCommGrpCat.of (R.obj X)
  map f := AddCommGrpCat.ofHom (R.map f).hom.toAddMonoidHom

/-- The sections over `V` of the coinduced module: morphisms of abelian presheaves
`R|_V ⟶ G|_V` on the slice `C/V`. -/
def Hom (V : C) : Type _ :=
  (Over.forget V).op ⋙ ab R ⟶ (Over.forget V).op ⋙ G

/-- The sections over `V` of the coinduced module form an abelian group under pointwise addition
of morphisms. -/
instance (V : C) : AddCommGroup (Hom R G V) :=
  inferInstanceAs (AddCommGroup ((Over.forget V).op ⋙ ab R ⟶ (Over.forget V).op ⋙ G))

variable {R G}

/-- A morphism `R|_V ⟶ G|_V`, read as a section of the coinduced module. -/
def Hom.mk {V : C} (β : (Over.forget V).op ⋙ ab R ⟶ (Over.forget V).op ⋙ G) : Hom R G V := β

/-- A section of the coinduced module, read as a morphism `R|_V ⟶ G|_V`. -/
def Hom.nat {V : C} (β : Hom R G V) : (Over.forget V).op ⋙ ab R ⟶ (Over.forget V).op ⋙ G := β

/-- The value of a section of the coinduced module at an object `W` of the slice and an element
of `R(W)`. -/
def Hom.eval {V : C} (β : Hom R G V) (W : Over V) (r : R.obj (op W.left)) : G.obj (op W.left) :=
  β.nat.app (op W) r

/-- Two sections of the coinduced module are equal if they have the same values at every object
of the slice and every element. -/
@[ext]
lemma Hom.ext {V : C} {β β' : Hom R G V}
    (h : ∀ (W : Over V) (r : R.obj (op W.left)), β.eval W r = β'.eval W r) :
    β = β' :=
  NatTrans.ext (funext fun W => AddCommGrpCat.hom_ext (AddMonoidHom.ext fun r => h W.unop r))

/-- The value of the section `Hom.mk β` is the value of the morphism `β`. -/
@[simp]
lemma Hom.mk_eval {V : C} (β : (Over.forget V).op ⋙ ab R ⟶ (Over.forget V).op ⋙ G)
    (W : Over V) (r : R.obj (op W.left)) : (Hom.mk β).eval W r = β.app (op W) r := rfl

/-- The value of a section of the coinduced module is additive in the element of `R(W)`. -/
lemma Hom.eval_add {V : C} (β : Hom R G V) (W : Over V) (r s : R.obj (op W.left)) :
    β.eval W (r + s) = β.eval W r + β.eval W s :=
  map_add (β.nat.app (op W)).hom r s

/-- A section of the coinduced module takes the value `0` at `0 ∈ R(W)`. -/
lemma Hom.eval_zero {V : C} (β : Hom R G V) (W : Over V) :
    β.eval W 0 = 0 :=
  map_zero (β.nat.app (op W)).hom

/-- The value of a sum of sections of the coinduced module is the sum of their values. -/
@[simp]
lemma Hom.add_eval {V : C} (β β' : Hom R G V) (W : Over V) (r : R.obj (op W.left)) :
    (β + β').eval W r = β.eval W r + β'.eval W r := rfl

/-- The zero section of the coinduced module takes the value `0` everywhere. -/
@[simp]
lemma Hom.zero_eval {V : C} (W : Over V) (r : R.obj (op W.left)) :
    (0 : Hom R G V).eval W r = 0 := rfl

/-- The value of a morphism `R|_V ⟶ G|_V` at an object `h : W ⟶ V` of the slice depends on `h`
only through its value. -/
lemma Hom.eval_mk_congr {V W : C} (β : Hom R G V) {h h' : W ⟶ V} (e : h = h')
    (r : R.obj (op W)) :
    β.eval (Over.mk h) r = β.eval (Over.mk h') r := by
  subst e
  rfl

/-- Naturality of a morphism `R|_V ⟶ G|_V` along a morphism of the slice, on elements. -/
lemma Hom.eval_naturality {V : C} (β : Hom R G V) {W W' : Over V} (g : W ⟶ W')
    (r : R.obj (op W'.left)) :
    β.eval W (R.map g.left.op r) = G.map g.left.op (β.eval W' r) :=
  NatTrans.naturality_apply β.nat g.op r

variable (R) in
/-- Right multiplication by the restrictions of a section `f ∈ R(V)`, as an endomorphism of the
abelian presheaf `R|_V`. -/
def mulRight {V : C} (f : R.obj (op V)) :
    (Over.forget V).op ⋙ ab R ⟶ (Over.forget V).op ⋙ ab R where
  app W := AddCommGrpCat.ofHom (AddMonoidHom.mulRight (R.map W.unop.hom.op f))
  naturality W W' g := by
    ext (r : R.obj (op W.unop.left))
    change R.map g.unop.left.op r * R.map W'.unop.hom.op f =
      R.map g.unop.left.op (r * R.map W.unop.hom.op f)
    rw [map_mul, ← RingCat.comp_apply, ← R.map_comp, ← op_comp, Over.w g.unop]

variable (R G) in
/-- The action of `R(V)` on the sections over `V` of the coinduced module: precomposition with
right multiplication. -/
def smulHom (V : C) : R.obj (op V) →+* AddMonoid.End (Hom R G V) where
  toFun f :=
    { toFun := fun β => Hom.mk (mulRight R f ≫ β.nat)
      map_zero' := Limits.comp_zero
      map_add' := fun β β' => Preadditive.comp_add _ _ _ _ _ _ }
  map_one' := by
    ext β W r
    change β.eval W (r * R.map W.hom.op 1) = β.eval W r
    rw [map_one, mul_one]
  map_mul' f g := by
    ext β W r
    change β.eval W (r * R.map W.hom.op (f * g)) =
      β.eval W ((r * R.map W.hom.op f) * R.map W.hom.op g)
    rw [map_mul, mul_assoc]
  map_zero' := by
    ext β W r
    change β.eval W (r * R.map W.hom.op 0) = 0
    rw [map_zero, mul_zero, Hom.eval_zero]
  map_add' f g := by
    ext β W r
    change β.eval W (r * R.map W.hom.op (f + g)) =
      β.eval W (r * R.map W.hom.op f) + β.eval W (r * R.map W.hom.op g)
    rw [map_add, mul_add, Hom.eval_add]

/-- The `R(V)`-module structure on the sections over `V` of the coinduced module, given by
`smulHom`. -/
instance (V : C) : Module (R.obj (op V)) (Hom R G V) :=
  Module.compHom _ (smulHom R G V)

/-- The value of `f • β` at `r ∈ R(W)` is the value of `β` at `r` times the restriction of `f`
to `W`. -/
@[simp]
lemma Hom.smul_eval {V : C} (f : R.obj (op V)) (β : Hom R G V) (W : Over V)
    (r : R.obj (op W.left)) :
    (f • β).eval W r = β.eval W (r * R.map W.hom.op f) :=
  rfl

variable (R G) in
/-- Restriction of the sections of the coinduced module along a morphism `f : V' ⟶ V`:
whiskering with the relocalization functor `Over.map f`. -/
def restrict {V V' : C} (f : V' ⟶ V) : Hom R G V →+ Hom R G V' where
  toFun β := Hom.mk (Functor.whiskerLeft (Over.map f).op β.nat)
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The value of the restriction of `β` along `f` at an object `W ⟶ V'` is the value of `β` at
the composite `W ⟶ V' ⟶ V`. -/
@[simp]
lemma restrict_eval {V V' : C} (f : V' ⟶ V) (β : Hom R G V) (W : Over V')
    (r : R.obj (op W.left)) :
    (restrict R G f β).eval W r = β.eval (Over.mk (W.hom ≫ f)) r := rfl

/-- Restriction along `f` is semilinear along the restriction map `R(V) → R(V')`. -/
lemma restrict_smul {V V' : C} (f : V' ⟶ V) (a : R.obj (op V)) (β : Hom R G V) :
    restrict R G f (a • β) = R.map f.op a • restrict R G f β := by
  ext W r
  change β.eval (Over.mk (W.hom ≫ f)) (r * R.map (W.hom ≫ f).op a) =
    β.eval (Over.mk (W.hom ≫ f)) (r * R.map W.hom.op (R.map f.op a))
  rw [op_comp, R.map_comp, RingCat.comp_apply]

/-- Restriction along the identity is the identity. -/
lemma restrict_id {V : C} (β : Hom R G V) : restrict R G (𝟙 V) β = β := by
  ext W r
  exact β.eval_mk_congr (Category.comp_id W.hom) r

/-- Restriction along a composite `g ≫ f` is restriction along `f` followed by restriction along
`g`. -/
lemma restrict_comp {V V' V'' : C} (f : V' ⟶ V) (g : V'' ⟶ V') (β : Hom R G V) :
    restrict R G (g ≫ f) β = restrict R G g (restrict R G f β) := by
  ext W r
  exact β.eval_mk_congr (Category.assoc W.hom g f).symm r

variable [∀ V : C, LocallySmall.{w} ((Over V)ᵒᵖ ⥤ AddCommGrpCat.{w})]

/-- The sections over `V` of the coinduced module are `w`-small. -/
instance (V : C) : Small.{w} (Hom R G V) :=
  inferInstanceAs (Small.{w} ((Over.forget V).op ⋙ ab R ⟶ (Over.forget V).op ⋙ G))

variable (R G) in
/-- The shrinking equivalence between the sections of the coinduced module and the morphisms
`R|_V ⟶ G|_V`. -/
abbrev e (V : C) : Shrink.{w} (Hom R G V) ≃ₗ[R.obj (op V)] Hom R G V :=
  Shrink.linearEquiv _ _

variable (R G) in
/-- The underlying abelian presheaf of the coinduced module. -/
def presheaf : Cᵒᵖ ⥤ AddCommGrpCat.{w} where
  obj V := AddCommGrpCat.of (Shrink.{w} (Hom R G V.unop))
  map {V V'} f := AddCommGrpCat.ofHom
    ((e R G V'.unop).symm.toAddMonoidHom.comp
      ((restrict R G f.unop).comp (e R G V.unop).toAddMonoidHom))
  map_id V := by
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => ?_)
    apply (e R G V.unop).injective
    change e R G V.unop ((e R G V.unop).symm _) = e R G V.unop x
    rw [LinearEquiv.apply_symm_apply]
    exact restrict_id _
  map_comp {V V' V''} f g := by
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => ?_)
    apply (e R G V''.unop).injective
    change e R G V''.unop ((e R G V''.unop).symm _) =
      e R G V''.unop ((e R G V''.unop).symm (restrict R G g.unop
        (e R G V'.unop ((e R G V'.unop).symm _))))
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply]
    exact restrict_comp _ _ _

/-- The `R(V)`-module structure on the sections over `V` of the coinduced presheaf. -/
instance (V : Cᵒᵖ) : Module (R.obj V) ((presheaf R G).obj V) :=
  inferInstanceAs (Module (R.obj (op V.unop)) (Shrink.{w} (Hom R G V.unop)))

/-- The `R(V)`-module structure on the morphisms `R|_V ⟶ G|_V`, indexed by an object of `Cᵒᵖ`. -/
instance (V : Cᵒᵖ) : Module (R.obj V) (Hom R G V.unop) :=
  inferInstanceAs (Module (R.obj (op V.unop)) (Hom R G V.unop))

variable (R G) in
/-- The sections over `V` of the coinduced module are the morphisms `R|_V ⟶ G|_V`. -/
def sectionsEquiv (V : Cᵒᵖ) : (presheaf R G).obj V ≃ₗ[R.obj V] Hom R G V.unop :=
  e R G V.unop

/-- Under `sectionsEquiv`, the restriction maps of the coinduced presheaf are `restrict`. -/
lemma sectionsEquiv_map {V V' : Cᵒᵖ} (f : V ⟶ V') (x : (presheaf R G).obj V) :
    sectionsEquiv R G V' ((presheaf R G).map f x) = restrict R G f.unop (sectionsEquiv R G V x) :=
  LinearEquiv.apply_symm_apply _ _

variable (R G) in
/-- The presheaf of `R`-modules coinduced by `G`. -/
def presheafOfModules : PresheafOfModules.{w} R :=
  PresheafOfModules.ofPresheaf (presheaf R G) (fun {V V'} f a x => by
    apply (sectionsEquiv R G V').injective
    rw [sectionsEquiv_map, map_smul, LinearEquiv.map_smul, sectionsEquiv_map]
    exact restrict_smul _ _ _)

/-- If `G` is a sheaf, then the underlying abelian presheaf of the coinduced module is a
sheaf. -/
lemma isSheaf_presheaf {J : GrothendieckTopology C} (hG : Presheaf.IsSheaf J G) :
    Presheaf.IsSheaf J (presheaf R G) := by
  refine Presheaf.isSheaf_of_isSheaf_comp J _ (CategoryTheory.forget AddCommGrpCat.{w}) ?_
  rw [isSheaf_iff_isSheaf_of_type]
  exact Presieve.isSheaf_of_nat_equiv (P₁ := presheafHom (ab R) G)
    (fun V => (sectionsEquiv R G (op V)).toEquiv.symm)
    (fun {V V'} f (x : Hom R G V') => by
      change (sectionsEquiv R G (op V)).symm (restrict R G f x) =
        (presheaf R G).map f.op ((sectionsEquiv R G (op V')).symm x)
      apply (sectionsEquiv R G (op V)).injective
      rw [sectionsEquiv_map, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
      rfl) ((isSheaf_iff_isSheaf_of_type J _).1 (hG.hom (ab R)))

end Presheaf

section Sheaf

variable {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})
  [∀ V : C, LocallySmall.{w} ((Over V)ᵒᵖ ⥤ AddCommGrpCat.{w})]

/-- **The sheaf of `R`-modules coinduced by an abelian sheaf `G`**: its sections over `V` are the
morphisms of abelian presheaves `R|_V ⟶ G|_V`. -/
def obj (G : Sheaf J AddCommGrpCat.{w}) : SheafOfModules.{w} R where
  val := presheafOfModules R.obj G.obj
  isSheaf := isSheaf_presheaf G.property

variable {R}

/-- Restriction of sections of a presheaf of modules, landing in the module of sections itself
rather than in its restriction of scalars. -/
abbrev res (M : PresheafOfModules.{w} R.obj) {X Y : Cᵒᵖ} (f : X ⟶ Y) (m : M.obj X) : M.obj Y :=
  M.map f m

omit [∀ V : C, LocallySmall.{w} ((Over V)ᵒᵖ ⥤ AddCommGrpCat.{w})] in
/-- Restriction of sections of a presheaf of modules is semilinear along the restriction map of
`R`. -/
lemma res_smul (M : PresheafOfModules.{w} R.obj) {X Y : Cᵒᵖ} (f : X ⟶ Y) (r : R.obj.obj X)
    (m : M.obj X) : res M f (r • m) = R.obj.map f r • res M f m :=
  M.map_smul f r m

omit [∀ V : C, LocallySmall.{w} ((Over V)ᵒᵖ ⥤ AddCommGrpCat.{w})] in
/-- Restriction of sections of a presheaf of modules is additive. -/
lemma res_add (M : PresheafOfModules.{w} R.obj) {X Y : Cᵒᵖ} (f : X ⟶ Y) (m m' : M.obj X) :
    res M f (m + m') = res M f m + res M f m' :=
  map_add (M.map f).hom m m'

omit [∀ V : C, LocallySmall.{w} ((Over V)ᵒᵖ ⥤ AddCommGrpCat.{w})] in
/-- Restriction of sections of a presheaf of modules sends `0` to `0`. -/
lemma res_zero (M : PresheafOfModules.{w} R.obj) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    res M f 0 = 0 :=
  map_zero (M.map f).hom

omit [∀ V : C, LocallySmall.{w} ((Over V)ᵒᵖ ⥤ AddCommGrpCat.{w})] in
/-- Restricting along `f` and then along `g` is restricting along `f ≫ g`. -/
lemma res_res (M : PresheafOfModules.{w} R.obj) {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (m : M.obj X) : res M g (res M f m) = res M (f ≫ g) m :=
  (PresheafOfModules.map_comp_apply M f g m).symm

/-- The morphism `R|_V ⟶ N|_V` of abelian presheaves named by a section `n` of a sheaf of modules
`N` over `V`: `r ↦ r • n|_W` on an object `W ⟶ V` of the slice. -/
def sectionMap (N : SheafOfModules.{w} R) {V : C} (n : N.val.obj (op V)) :
    (Over.forget V).op ⋙ ab R.obj ⟶ (Over.forget V).op ⋙ N.val.presheaf where
  app W := AddCommGrpCat.ofHom (X := R.obj.obj (op W.unop.left))
    (Y := N.val.obj (op W.unop.left))
    (AddMonoidHom.mk' (fun r => r • res N.val W.unop.hom.op n) (fun a b => add_smul a b _))
  naturality W W' g := by
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun (r : R.obj.obj (op W.unop.left)) => ?_)
    change R.obj.map g.unop.left.op r • res N.val W'.unop.hom.op n =
      res N.val g.unop.left.op (r • res N.val W.unop.hom.op n)
    rw [res_smul, res_res, ← op_comp, Over.w g.unop]

omit [∀ V : C, LocallySmall.{w} ((Over V)ᵒᵖ ⥤ AddCommGrpCat.{w})] in
/-- The morphism `sectionMap N n` sends `r ∈ R(W)` to `r • n|_W`. -/
lemma sectionMap_app (N : SheafOfModules.{w} R) {V : C} (n : N.val.obj (op V)) (W : Over V)
    (r : R.obj.obj (op W.left)) :
    (sectionMap N n).app (op W) r = r • res N.val W.hom.op n := rfl

variable {G : Sheaf J AddCommGrpCat.{w}}

/-- A morphism of abelian sheaves out of the underlying abelian sheaf of `N`, applied to a section
of `N`. -/
abbrev ap {N : SheafOfModules.{w} R} (φ : (SheafOfModules.toSheaf R).obj N ⟶ G) (X : Cᵒᵖ)
    (m : N.val.obj X) : G.obj.obj X :=
  φ.hom.app X m

omit [∀ V : C, LocallySmall.{w} ((Over V)ᵒᵖ ⥤ AddCommGrpCat.{w})] in
/-- A morphism of abelian sheaves is additive on sections. -/
lemma ap_add {N : SheafOfModules.{w} R} (φ : (SheafOfModules.toSheaf R).obj N ⟶ G) (X : Cᵒᵖ)
    (m m' : N.val.obj X) : ap φ X (m + m') = ap φ X m + ap φ X m' :=
  map_add (φ.hom.app X).hom m m'

omit [∀ V : C, LocallySmall.{w} ((Over V)ᵒᵖ ⥤ AddCommGrpCat.{w})] in
/-- A morphism of abelian sheaves sends the zero section to `0`. -/
lemma ap_zero {N : SheafOfModules.{w} R} (φ : (SheafOfModules.toSheaf R).obj N ⟶ G) (X : Cᵒᵖ) :
    ap φ X 0 = 0 :=
  map_zero (φ.hom.app X).hom

/-- The section of the coinduced module named by a morphism of abelian sheaves `φ` out of the
underlying abelian sheaf of `N` and a section `n` of `N` over `V`: `r ↦ φ(r • n|_W)`. -/
def toHom {N : SheafOfModules.{w} R} (φ : (SheafOfModules.toSheaf R).obj N ⟶ G) {V : C}
    (n : N.val.obj (op V)) : Hom R.obj G.obj V :=
  Hom.mk (sectionMap N n ≫ Functor.whiskerLeft (Over.forget V).op φ.hom)

omit [∀ V : C, LocallySmall.{w} ((Over V)ᵒᵖ ⥤ AddCommGrpCat.{w})] in
/-- The value of `toHom φ n` at `r ∈ R(W)` is `φ(r • n|_W)`. -/
lemma toHom_eval {N : SheafOfModules.{w} R} (φ : (SheafOfModules.toSheaf R).obj N ⟶ G) {V : C}
    (n : N.val.obj (op V)) (W : Over V) (r : R.obj.obj (op W.left)) :
    (toHom φ n).eval W r = ap φ (op W.left) (r • res N.val W.hom.op n) := rfl

omit [∀ V : C, LocallySmall.{w} ((Over V)ᵒᵖ ⥤ AddCommGrpCat.{w})] in
/-- `toHom φ` is additive in the section of `N`. -/
lemma toHom_add {N : SheafOfModules.{w} R} (φ : (SheafOfModules.toSheaf R).obj N ⟶ G) {V : C}
    (n n' : N.val.obj (op V)) : toHom φ (n + n') = toHom φ n + toHom φ n' := by
  ext W r
  rw [toHom_eval, Hom.add_eval, toHom_eval, toHom_eval, res_add, smul_add, ap_add]

omit [∀ V : C, LocallySmall.{w} ((Over V)ᵒᵖ ⥤ AddCommGrpCat.{w})] in
/-- `toHom φ` is `R(V)`-linear in the section of `N`. -/
lemma toHom_smul {N : SheafOfModules.{w} R} (φ : (SheafOfModules.toSheaf R).obj N ⟶ G) {V : C}
    (a : R.obj.obj (op V)) (n : N.val.obj (op V)) : toHom φ (a • n) = a • toHom φ n := by
  ext W r
  rw [toHom_eval, Hom.smul_eval, toHom_eval, res_smul, smul_smul]

omit [∀ V : C, LocallySmall.{w} ((Over V)ᵒᵖ ⥤ AddCommGrpCat.{w})] in
/-- `toHom φ` commutes with restriction along `f : V' ⟶ V`. -/
lemma toHom_map {N : SheafOfModules.{w} R} (φ : (SheafOfModules.toSheaf R).obj N ⟶ G)
    {V V' : C} (f : V' ⟶ V) (n : N.val.obj (op V)) :
    toHom φ (res N.val f.op n) = restrict R.obj G.obj f (toHom φ n) := by
  ext W r
  rw [toHom_eval, restrict_eval, toHom_eval, res_res, ← op_comp]
  rfl

/-- A morphism of abelian sheaves out of the underlying abelian sheaf of `N`, read as a morphism
of sheaves of modules into the coinduced module. -/
def homEquivToFun {N : SheafOfModules.{w} R} (φ : (SheafOfModules.toSheaf R).obj N ⟶ G) :
    N ⟶ obj R G :=
  ⟨PresheafOfModules.homMk
    { app := fun V => AddCommGrpCat.ofHom (X := N.val.obj V)
        (Y := Shrink.{w} (Hom R.obj G.obj V.unop))
        { toFun := fun n => (sectionsEquiv R.obj G.obj V).symm (toHom φ n)
          map_zero' := by
            rw [show toHom φ (0 : N.val.obj V) = 0 by
              ext W r
              rw [toHom_eval, Hom.zero_eval, res_zero, smul_zero, ap_zero], map_zero]
            rfl
          map_add' := fun n n' => by rw [toHom_add, map_add]; rfl }
      naturality := fun {V V'} f => by
        refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun n => ?_)
        change (sectionsEquiv R.obj G.obj V').symm (toHom φ (res N.val f n)) =
          (presheaf R.obj G.obj).map f ((sectionsEquiv R.obj G.obj V).symm (toHom φ n))
        apply (sectionsEquiv R.obj G.obj V').injective
        rw [sectionsEquiv_map, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
        exact toHom_map φ f.unop n }
    (fun V a n => by
      change (sectionsEquiv R.obj G.obj V).symm (toHom φ (a • n)) =
        a • (sectionsEquiv R.obj G.obj V).symm (toHom φ n)
      rw [toHom_smul, map_smul])⟩

/-- The section of the coinduced module that a morphism of sheaves of modules `ψ` into it assigns
to a section `n` of its source, read as a morphism `R|_V ⟶ G|_V`. -/
abbrev sec {N : SheafOfModules.{w} R} (ψ : N ⟶ obj R G) (V : Cᵒᵖ) (n : N.val.obj V) :
    Hom R.obj G.obj V.unop :=
  sectionsEquiv R.obj G.obj V (ψ.val.app V n)

/-- `sec ψ V` is additive. -/
lemma sec_add {N : SheafOfModules.{w} R} (ψ : N ⟶ obj R G) (V : Cᵒᵖ) (n n' : N.val.obj V) :
    sec ψ V (n + n') = sec ψ V n + sec ψ V n' := by
  rw [sec, map_add]
  exact map_add (sectionsEquiv R.obj G.obj V) _ _

/-- `sec ψ V` is `R(V)`-linear. -/
lemma sec_smul {N : SheafOfModules.{w} R} (ψ : N ⟶ obj R G) (V : Cᵒᵖ) (a : R.obj.obj V)
    (n : N.val.obj V) : sec ψ V (a • n) = a • sec ψ V n := by
  rw [sec, map_smul]
  exact map_smul (sectionsEquiv R.obj G.obj V) _ _

/-- `sec ψ` commutes with restriction: the morphism assigned to `n|_{V'}` is the restriction of
the one assigned to `n`. -/
lemma sec_res {N : SheafOfModules.{w} R} (ψ : N ⟶ obj R G) {V V' : Cᵒᵖ} (f : V ⟶ V')
    (n : N.val.obj V) : sec ψ V' (res N.val f n) = restrict R.obj G.obj f.unop (sec ψ V n) := by
  rw [sec, res, PresheafOfModules.naturality_apply]
  exact sectionsEquiv_map f _

/-- Two morphisms of sheaves of modules into the coinduced module agree as soon as they assign the
same morphisms `R|_V ⟶ G|_V` to all sections. -/
lemma hom_ext_sec {N : SheafOfModules.{w} R} {ψ ψ' : N ⟶ obj R G}
    (h : ∀ (V : Cᵒᵖ) (n : N.val.obj V), sec ψ V n = sec ψ' V n) : ψ = ψ' :=
  SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V =>
    ModuleCat.hom_ext (LinearMap.ext fun n => (sectionsEquiv R.obj G.obj V).injective (h V n)))

/-- A morphism of sheaves of modules into the coinduced module, read as a morphism of abelian
sheaves out of the underlying abelian sheaf of its source: a section `n` over `V` is sent to the
value at `1` over `V` itself of the morphism `R|_V ⟶ G|_V` it is assigned. -/
def homEquivInvFun {N : SheafOfModules.{w} R} (ψ : N ⟶ obj R G) :
    (SheafOfModules.toSheaf R).obj N ⟶ G where
  hom :=
    { app := fun V => AddCommGrpCat.ofHom (X := N.val.obj V) (Y := G.obj.obj V)
        { toFun := fun n => (sec ψ V n).eval (Over.mk (𝟙 V.unop)) 1
          map_zero' := by
            rw [show sec ψ V 0 = 0 by rw [sec, map_zero]; exact map_zero _]
            rfl
          map_add' := fun n n' => by rw [sec_add]; rfl }
      naturality := fun {V V'} f => by
        refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun (n : N.val.obj V) => ?_)
        change (sec ψ V' (res N.val f n)).eval (Over.mk (𝟙 V'.unop)) 1 =
          G.obj.map f ((sec ψ V n).eval (Over.mk (𝟙 V.unop)) 1)
        rw [sec_res, restrict_eval]
        refine ((sec ψ V n).eval_mk_congr (Category.id_comp f.unop) 1).trans ?_
        have h := (sec ψ V n).eval_naturality
          (Over.homMk f.unop (by simp) : Over.mk f.unop ⟶ Over.mk (𝟙 V.unop)) 1
        rwa [map_one] at h }

/-- The morphism `homEquivInvFun ψ` sends a section `n` over `V` to the value at `1` over `V` of
`sec ψ V n`. -/
lemma homEquivInvFun_app {N : SheafOfModules.{w} R} (ψ : N ⟶ obj R G) (V : Cᵒᵖ)
    (n : N.val.obj V) :
    ap (homEquivInvFun ψ) V n = (sec ψ V n).eval (Over.mk (𝟙 V.unop)) 1 := rfl

/-- The morphism `homEquivToFun φ` assigns to a section `n` the morphism `toHom φ n`. -/
lemma sec_homEquivToFun {N : SheafOfModules.{w} R} (φ : (SheafOfModules.toSheaf R).obj N ⟶ G)
    (V : Cᵒᵖ) (n : N.val.obj V) : sec (homEquivToFun φ) V n = toHom φ n :=
  LinearEquiv.apply_symm_apply _ _

/-- **Morphisms of abelian sheaves out of the underlying abelian sheaf of a sheaf of modules `N`
are morphisms of sheaves of modules from `N` to the coinduced module.** -/
def homEquiv (N : SheafOfModules.{w} R) (G : Sheaf J AddCommGrpCat.{w}) :
    ((SheafOfModules.toSheaf R).obj N ⟶ G) ≃ (N ⟶ obj R G) where
  toFun := homEquivToFun
  invFun := homEquivInvFun
  left_inv φ := by
    refine Sheaf.hom_ext (NatTrans.ext (funext fun V =>
      AddCommGrpCat.hom_ext (AddMonoidHom.ext fun (n : N.val.obj V) => ?_)))
    change ap (homEquivInvFun (homEquivToFun φ)) V n = ap φ V n
    rw [homEquivInvFun_app, sec_homEquivToFun, toHom_eval, one_smul]
    exact congrArg (ap φ V) (ConcreteCategory.congr_hom (N.val.presheaf.map_id V) n)
  right_inv ψ := by
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V =>
      ModuleCat.hom_ext (LinearMap.ext fun n => (sectionsEquiv R.obj G.obj V).injective ?_))
    change sec (homEquivToFun (homEquivInvFun ψ)) V n = sec ψ V n
    rw [sec_homEquivToFun]
    ext W r
    rw [toHom_eval, homEquivInvFun_app, sec_smul, Hom.smul_eval, sec_res, restrict_eval,
      one_mul]
    refine ((sec ψ V n).eval_mk_congr (Category.id_comp W.hom) _).trans ?_
    exact congrArg ((sec ψ V n).eval W) (ConcreteCategory.congr_hom (R.obj.map_id _) r)

/-- The morphism `homEquiv N G φ` assigns to a section `n` over `V` the morphism `r ↦ φ(r • n|_W)`
on `C/V`. -/
lemma sec_homEquiv {N : SheafOfModules.{w} R} (φ : (SheafOfModules.toSheaf R).obj N ⟶ G)
    (V : Cᵒᵖ) (n : N.val.obj V) : sec (homEquiv N G φ) V n = toHom φ n :=
  sec_homEquivToFun φ V n

end Sheaf

end Stacks.SheafOfModules.AbelianCoinduction
