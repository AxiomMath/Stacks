module

public import Mathlib.CategoryTheory.Elements
public import StacksFrontier.CategoryTheory.FiberedInSets.TwoCategory
public import StacksFrontier.CategoryTheory.Sites.Stack.FiberedInSets

/-!
# Categories fibred in sets are presheaves

Let `C` be a category. The only 2-morphisms between categories fibred in sets over `C` are
identities, so the 2-category of categories fibred in sets over `C` is a category. Moreover there is
an equivalence of categories between presheaves of sets on `C` and categories fibred in sets over
`C`: a presheaf `F` goes to the category `𝒮_F` of pairs `(U, x)` with `x ∈ F(U)`, whose morphisms
`(V, y) ⟶ (U, x)` are the morphisms `f : V ⟶ U` of `C` with `f^* x = y` (Stacks 04TM), and a
category fibred in sets `p : 𝒮 ⥤ C` goes to its presheaf of objects `U ↦ Ob(𝒮_U)`.

## Main definitions

* `CategoryTheory.CatFiberedInSets.elements`: the category `𝒮_F` attached to a presheaf of sets
  `F`, as an object of the 2-category of categories fibred in sets.
* `CategoryTheory.CatFiberedInSets.ofPresheaf`: the functor `F ↦ 𝒮_F`.
* `CategoryTheory.CatFiberedInSets.objPresheafFunctor`: the functor sending `p : 𝒮 ⥤ C` to its
  presheaf of objects `U ↦ Ob(𝒮_U)`.
* `CategoryTheory.CatFiberedInSets.presheafEquivalence`: the equivalence of categories between
  presheaves of sets on `C` and categories fibred in sets over `C`, whose functor is `ofPresheaf`
  and whose inverse is `objPresheafFunctor`.

## Main results

* `CategoryTheory.CatFiberedInSets.exists_eq_eqToHom`: every 2-morphism between 1-morphisms of the
  2-category of categories fibred in sets is an identity.

## Implementation notes

The category `𝒮_F` is Mathlib's category of elements `(F.Elements)ᵒᵖ` with structure functor
`(Functor.Elements.π F).leftOp`: a morphism `(V, y) ⟶ (U, x)` of it is a morphism `f : V ⟶ U`
of `C` with `F(f)(x) = y`, as in the source. The category of categories fibred in sets over `C` is
the underlying 1-category of the strict 2-category `CategoryTheory.CatFiberedInSets C`: its
morphisms are the functors `G` with `p' ∘ G = p`.

For the two functors to be mutually inverse up to isomorphism the presheaves take values in
`Type (max u w)` when `C : Type u`, and the categories fibred in sets have objects in the same
universe and morphisms in the universe of the morphisms of `C`, the universes of `𝒮_F`.

## References

* [Stacks Project, Tag 02Y2](https://stacks.math.columbia.edu/tag/02Y2)
* [Stacks Project, Tag 04TM](https://stacks.math.columbia.edu/tag/04TM)
-/

@[expose] public noncomputable section

open Opposite

namespace CategoryTheory

universe w v₁ v₂ u₁ u₂ v u

attribute [local instance] Functor.isFibered_of_isFiberedInSets

namespace Functor

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒮 : Type u₂} [Category.{v₂} 𝒮]

/-- In a category fibred in sets the chosen pullback of an object `x` of the fibre over `U` along
`f : V ⟶ U` is the source of any morphism into `x` lying over `f`. -/
lemma IsFiberedInSets.pullbackFiber_eq_of_isHomLift (p : 𝒮 ⥤ 𝒞) [p.IsFiberedInSets] {V U : 𝒞}
    (x : p.Fiber U) (f : V ⟶ U) (y : p.Fiber V) (φ : y.1 ⟶ x.1) [p.IsHomLift f φ] :
    pullbackFiber p x f = y := by
  obtain ⟨h, -⟩ := IsFiberedInSets.eq_of_isHomLift p f (IsPreFibered.pullbackMap x.2 f) φ
  exact Subtype.ext h

variable (p : 𝒮 ⥤ 𝒞) [p.IsFiberedInSets]

/-- In a category fibred in sets, the morphism `y ⟶ x` lying over `f : V ⟶ U` attached to an
equality `f^* x = y` of objects of the fibre over `V`. -/
noncomputable def homOfPullbackFiberEq {U V : 𝒞} {x : p.Fiber U} {f : V ⟶ U} {y : p.Fiber V}
    (h : pullbackFiber p x f = y) : y.1 ⟶ x.1 :=
  eqToHom ((congrArg Subtype.val h).symm : y.1 = IsPreFibered.pullbackObj x.2 f) ≫
    IsPreFibered.pullbackMap x.2 f

/-- The morphism `CategoryTheory.Functor.homOfPullbackFiberEq` lies over `f`. -/
instance isHomLift_homOfPullbackFiberEq {U V : 𝒞} {x : p.Fiber U} {f : V ⟶ U}
    {y : p.Fiber V} (h : pullbackFiber p x f = y) : p.IsHomLift f (homOfPullbackFiberEq p h) := by
  unfold homOfPullbackFiberEq
  infer_instance

/-- The action on morphisms of `CategoryTheory.Functor.fromElementsObjPresheaf`: a morphism
`(V, y) ⟶ (U, x)` of the category of elements of the presheaf of objects, i.e. a morphism
`f : V ⟶ U` with `f^* x = y`, goes to the morphism `y ⟶ x` lying over `f`. -/
noncomputable def fromElementsObjPresheafMap {a b : (p.objPresheaf.Elements)ᵒᵖ} (φ : a ⟶ b) :
    a.unop.2.1 ⟶ b.unop.2.1 :=
  homOfPullbackFiberEq p (U := b.unop.1.unop) (V := a.unop.1.unop)
    ((objPresheaf_map' p φ.unop.hom b.unop.2).symm.trans φ.unop.map_val)

/-- `CategoryTheory.Functor.fromElementsObjPresheafMap φ` lies over the morphism of `𝒞` underlying
`φ`. -/
instance isHomLift_fromElementsObjPresheafMap {a b : (p.objPresheaf.Elements)ᵒᵖ} (φ : a ⟶ b) :
    p.IsHomLift φ.unop.hom.unop (fromElementsObjPresheafMap p φ) :=
  isHomLift_homOfPullbackFiberEq p _

/-- The comparison functor from the category of elements of the presheaf of objects of a category
fibred in sets `p : 𝒮 ⥤ 𝒞` back to `𝒮`: it sends `(U, x)`, with `x` an object of the fibre over
`U`, to `x`. -/
noncomputable def fromElementsObjPresheaf : (p.objPresheaf.Elements)ᵒᵖ ⥤ 𝒮 where
  obj a := a.unop.2.1
  map φ := fromElementsObjPresheafMap p φ
  map_id a := by
    have : p.IsHomLift (𝟙 a : a ⟶ a).unop.hom.unop (𝟙 a.unop.2.1) :=
      (IsHomLift.id a.unop.2.2 : p.IsHomLift (𝟙 a.unop.1.unop) (𝟙 a.unop.2.1))
    exact IsFiberedInSets.hom_ext_of_isHomLift p (𝟙 a : a ⟶ a).unop.hom.unop
      (fromElementsObjPresheafMap p (𝟙 a)) (𝟙 a.unop.2.1)
  map_comp {a b c} φ ψ := by
    have : p.IsHomLift (φ ≫ ψ).unop.hom.unop
        (fromElementsObjPresheafMap p φ ≫ fromElementsObjPresheafMap p ψ) :=
      (inferInstance : p.IsHomLift (φ.unop.hom.unop ≫ ψ.unop.hom.unop)
        (fromElementsObjPresheafMap p φ ≫ fromElementsObjPresheafMap p ψ))
    exact IsFiberedInSets.hom_ext_of_isHomLift p (φ ≫ ψ).unop.hom.unop
      (fromElementsObjPresheafMap p (φ ≫ ψ))
      (fromElementsObjPresheafMap p φ ≫ fromElementsObjPresheafMap p ψ)

/-- `CategoryTheory.Functor.fromElementsObjPresheaf` is a functor over `𝒞`. -/
lemma fromElementsObjPresheaf_comp :
    fromElementsObjPresheaf p ⋙ p = (Functor.Elements.π p.objPresheaf).leftOp :=
  Functor.ext (fun a ↦ a.unop.2.2)
    (fun _ _ φ ↦ IsHomLift.fac' p φ.unop.hom.unop (fromElementsObjPresheafMap p φ))

/-- The comparison functor from a category fibred in sets `p : 𝒮 ⥤ 𝒞` to the category of elements
of its presheaf of objects: it sends `x` to `(p(x), x)` and `φ : x ⟶ y` to `p(φ)`. -/
def toElementsObjPresheaf : 𝒮 ⥤ (p.objPresheaf.Elements)ᵒᵖ where
  obj x := op (p.objPresheaf.elementsMk (op (p.obj x)) (⟨x, rfl⟩ : p.Fiber (p.obj x)))
  map {x y} φ := (Functor.Elements.homMk
    (x := p.objPresheaf.elementsMk (op (p.obj y)) (⟨y, rfl⟩ : p.Fiber (p.obj y)))
    (y := p.objPresheaf.elementsMk (op (p.obj x)) (⟨x, rfl⟩ : p.Fiber (p.obj x))) (p.map φ).op
    ((objPresheaf_map' p (p.map φ).op ⟨y, rfl⟩).trans
      (IsFiberedInSets.pullbackFiber_eq_of_isHomLift p ⟨y, rfl⟩ (p.map φ) ⟨x, rfl⟩ φ))).op
  map_id x := by
    apply Quiver.Hom.unop_inj
    apply Functor.Elements.hom_ext
    exact congrArg Quiver.Hom.op (p.map_id x)
  map_comp φ ψ := by
    apply Quiver.Hom.unop_inj
    apply Functor.Elements.hom_ext
    exact congrArg Quiver.Hom.op (p.map_comp φ ψ)

/-- `CategoryTheory.Functor.toElementsObjPresheaf` is a functor over `𝒞`. -/
lemma toElementsObjPresheaf_comp :
    toElementsObjPresheaf p ⋙ (Functor.Elements.π p.objPresheaf).leftOp = p :=
  rfl

end Functor

namespace CategoryOfElements

variable {C : Type u} [Category.{v} C]

/-- **Stacks 04TM.** The structure functor `(U, x) ↦ U` of the category `𝒮_F` of a presheaf of sets
`F`, i.e. of `(F.Elements)ᵒᵖ`, is fibred in sets: a morphism `f : V ⟶ U` of `C` has, at `(U, x)`,
the unique lift `(V, f^* x) ⟶ (U, x)`. -/
instance isFiberedInSets_π_leftOp (F : Cᵒᵖ ⥤ Type w) :
    (Functor.Elements.π F).leftOp.IsFiberedInSets where
  existsUnique_lift {U V} f x hx := by
    subst hx
    let y : F.Elementsᵒᵖ := op (F.elementsMk (op V) (F.map f.op x.unop.2))
    let φ : y ⟶ x := (Functor.Elements.homMk (x := x.unop) (y := y.unop) f.op rfl).op
    have : (Functor.Elements.π F).leftOp.IsHomLift f φ :=
      CategoryTheory.IsHomLift.map (Functor.Elements.π F).leftOp φ
    refine ⟨⟨y, φ⟩,
      ⟨rfl, CategoryTheory.IsHomLift.fac' (Functor.Elements.π F).leftOp f φ⟩, ?_⟩
    rintro ⟨⟨@⟨⟨V'⟩, t⟩⟩, ψ⟩ ⟨hy, hψ⟩
    have := CategoryTheory.IsHomLift.of_fac' (Functor.Elements.π F).leftOp f ψ hy rfl hψ
    change V' = V at hy
    subst V'
    have hgf := CategoryTheory.IsHomLift.eq_of_isHomLift (Functor.Elements.π F).leftOp
      (a := op (F.elementsMk _ t)) (b := x) f ψ
    obtain ⟨⟨g, hg⟩⟩ := ψ
    change F.map g x.unop.2 = t at hg
    have hg' : g = f.op := congrArg Quiver.Hom.op hgf.symm
    subst hg'
    clear hgf hψ this
    exact Eq.rec (motive := fun (t' : F.obj (op V)) (h' : F.map f.op x.unop.2 = t') ↦
        (⟨op (F.elementsMk (op V) t'),
          (Functor.Elements.homMk (x := x.unop) (y := F.elementsMk (op V) t') f.op h').op⟩ :
          Σ z : F.Elementsᵒᵖ, z ⟶ x) = ⟨y, φ⟩) rfl hg

/-- The fibre over `U.unop` of the category `𝒮_F` of a presheaf of sets `F` is `F(U)`. -/
def leftOpFiberEquiv (F : Cᵒᵖ ⥤ Type w) (U : Cᵒᵖ) :
    F.obj U ≃ (Functor.Elements.π F).leftOp.Fiber U.unop where
  toFun x := ⟨op (F.elementsMk U x), rfl⟩
  invFun a := cast (congrArg (fun V : C ↦ F.obj (op V)) a.2) a.1.unop.2
  left_inv _ := rfl
  right_inv a := by
    obtain ⟨⟨@⟨⟨V⟩, y⟩⟩, h⟩ := a
    change V = U.unop at h
    subst h
    rfl

end CategoryOfElements

namespace CatFiberedInSets

open CatFiberedInGroupoids (homFunctor homFunctor_comp_p)

section General

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]

/-- Two functors over `𝒞` with the same underlying functor are equal. -/
private lemma basedFunctor_ext {𝒳 𝒴 : BasedCategory.{v₂, u₂} 𝒞} {F G : BasedFunctor 𝒳 𝒴}
    (h : F.toFunctor = G.toFunctor) : F = G := by
  cases F
  cases G
  cases h
  rfl

/-- Two 1-morphisms into a category fibred in sets which agree on objects are equal. -/
lemma hom_ext_of_obj {𝒳 𝒴 : CatFiberedInSets.{v₁, v₂, u₁, u₂} 𝒞} {G H : 𝒳 ⟶ 𝒴}
    (h : ∀ x, (homFunctor G).obj x = (homFunctor H).obj x) : G = H :=
  Bicategory.InducedBicategory.hom_ext (basedFunctor_ext
    (Functor.IsFiberedInSets.eq_of_obj_eq 𝒳.val.p 𝒴.val.p _ _ (homFunctor_comp_p G)
      (homFunctor_comp_p H) h))

/-- **Stacks 02Y2**, first assertion. The only 2-morphisms between categories fibred in sets are
identities: a 2-morphism `t : G ⟶ H` of the 2-category of categories fibred in sets over `𝒞`
forces `G = H`, and `t` is then the identity 2-morphism of `G` (written `eqToHom`). In other words,
the 2-category of categories fibred in sets is a category. -/
@[stacks 02Y2 "2-morphisms between categories fibred in sets are identities"]
theorem exists_eq_eqToHom {𝒳 𝒴 : CatFiberedInSets.{v₁, v₂, u₁, u₂} 𝒞} {G H : 𝒳 ⟶ 𝒴}
    (t : G ⟶ H) : ∃ h : G = H, t = eqToHom h := by
  have key : ∀ {G H : 𝒳 ⟶ 𝒴} (t : G ⟶ H) (x : 𝒳.val.obj),
      ∃ h : (homFunctor G).obj x = (homFunctor H).obj x,
        t.hom.toNatTrans.app x = eqToHom h ≫ 𝟙 ((homFunctor H).obj x) := by
    intro G H t x
    have : 𝒴.val.p.IsHomLift (𝟙 (𝒳.val.p.obj x)) (𝟙 ((homFunctor H).obj x)) :=
      IsHomLift.id (BasedFunctor.w_obj H.hom x)
    exact Functor.IsFiberedInSets.eq_of_isHomLift 𝒴.val.p (𝟙 (𝒳.val.p.obj x))
      (t.hom.toNatTrans.app x) (𝟙 ((homFunctor H).obj x))
  have hGH : G = H := hom_ext_of_obj fun x ↦ (key t x).1
  refine ⟨hGH, ?_⟩
  subst hGH
  apply Bicategory.InducedBicategory.hom₂_ext
  apply BasedNatTrans.ext
  apply NatTrans.ext
  funext x
  obtain ⟨_, hc⟩ := key t x
  refine hc.trans ?_
  simp only [eqToHom_refl, Category.comp_id]
  rfl

/-- The action on 1-morphisms of `CategoryTheory.CatFiberedInSets.objPresheafFunctor`: a functor
`G : 𝒮 ⥤ 𝒮'` over `𝒞` restricts to maps `Ob(𝒮_U) → Ob(𝒮'_U)`, compatible with pullbacks. -/
def objPresheafMap {𝒳 𝒴 : CatFiberedInSets.{v₁, v₂, u₁, u₂} 𝒞} (G : 𝒳 ⟶ 𝒴) :
    𝒳.val.p.objPresheaf ⟶ 𝒴.val.p.objPresheaf where
  app U := ↾fun (x : 𝒳.val.p.Fiber U.unop) ↦
    (⟨(homFunctor G).obj x.1, (BasedFunctor.w_obj G.hom x.1).trans x.2⟩ : 𝒴.val.p.Fiber U.unop)
  naturality U V f := ConcreteCategory.ext_apply fun (x : 𝒳.val.p.Fiber U.unop) ↦ by
    let φ : (homFunctor G).obj (Functor.pullbackFiber 𝒳.val.p x f.unop).1 ⟶
        (homFunctor G).obj x.1 :=
      (homFunctor G).map (Functor.IsPreFibered.pullbackMap x.2 f.unop)
    have : 𝒴.val.p.IsHomLift f.unop φ :=
      BasedFunctor.preserves_isHomLift G.hom f.unop (Functor.IsPreFibered.pullbackMap x.2 f.unop)
    exact (Functor.IsFiberedInSets.pullbackFiber_eq_of_isHomLift 𝒴.val.p
      ⟨(homFunctor G).obj x.1, (BasedFunctor.w_obj G.hom x.1).trans x.2⟩ f.unop
      ⟨(homFunctor G).obj (Functor.pullbackFiber 𝒳.val.p x f.unop).1,
        (BasedFunctor.w_obj G.hom _).trans (Functor.pullbackFiber 𝒳.val.p x f.unop).2⟩ φ).symm

/-- The functor from the category of categories fibred in sets over `𝒞` to presheaves of sets on
`𝒞` sending `p : 𝒮 ⥤ 𝒞` to its presheaf of objects `U ↦ Ob(𝒮_U)`, whose restriction maps are the
pullbacks `f^*`. -/
noncomputable def objPresheafFunctor :
    CatFiberedInSets.{v₁, v₂, u₁, u₂} 𝒞 ⥤ (𝒞ᵒᵖ ⥤ Type u₂) where
  obj 𝒳 := 𝒳.val.p.objPresheaf
  map G := objPresheafMap G
  map_id _ := NatTrans.ext' (funext fun _ ↦ ConcreteCategory.ext_apply fun _ ↦ rfl)
  map_comp _ _ := NatTrans.ext' (funext fun _ ↦ ConcreteCategory.ext_apply fun _ ↦ rfl)

/-- The value of `CategoryTheory.CatFiberedInSets.objPresheafFunctor` at `p : 𝒮 ⥤ 𝒞` is the
presheaf of objects `U ↦ Ob(𝒮_U)` of `p`. -/
lemma objPresheafFunctor_obj (𝒳 : CatFiberedInSets.{v₁, v₂, u₁, u₂} 𝒞) :
    objPresheafFunctor.obj 𝒳 = 𝒳.val.p.objPresheaf :=
  rfl

end General

section Presheaf

variable {C : Type u} [Category.{v} C]

/-- **Stacks 04TM.** The category `𝒮_F` fibred in sets over `C` attached to a presheaf of sets
`F`: its objects are the pairs `(U, x)` with `x ∈ F(U)`, a morphism `(V, y) ⟶ (U, x)` is a
morphism `f : V ⟶ U` of `C` with `f^* x = y`, and the structure functor is `(U, x) ↦ U`. -/
abbrev elements (F : Cᵒᵖ ⥤ Type (max u w)) : CatFiberedInSets.{v, v, u, max u w} C :=
  mk (BasedCategory.ofFunctor (Functor.Elements.π F).leftOp)
    (CategoryOfElements.isFiberedInSets_π_leftOp F)

/-- The 1-morphism `𝒮_F ⟶ 𝒮_G` over `C` induced by a map of presheaves `α : F ⟶ G`:
`(U, x) ↦ (U, α(x))`. -/
def elementsMap {F G : Cᵒᵖ ⥤ Type (max u w)} (α : F ⟶ G) : elements F ⟶ elements G :=
  Bicategory.InducedBicategory.mkHom
    ({ toFunctor := (NatTrans.mapElements α).op
       w := rfl } : BasedFunctor (BasedCategory.ofFunctor (Functor.Elements.π F).leftOp)
        (BasedCategory.ofFunctor (Functor.Elements.π G).leftOp))

/-- The functor `F ↦ 𝒮_F` from presheaves of sets on `C` to the category of categories fibred in
sets over `C` (Stacks 04TM). -/
def ofPresheaf : (Cᵒᵖ ⥤ Type (max u w)) ⥤ CatFiberedInSets.{v, v, u, max u w} C where
  obj F := elements F
  map α := elementsMap α
  map_id _ := hom_ext_of_obj fun _ ↦ rfl
  map_comp _ _ := hom_ext_of_obj fun _ ↦ rfl

/-- The value of `CategoryTheory.CatFiberedInSets.ofPresheaf` at a presheaf `F` is `𝒮_F`. -/
lemma ofPresheaf_obj (F : Cᵒᵖ ⥤ Type (max u w)) : ofPresheaf.obj F = elements F :=
  rfl

/-- A presheaf of sets `F` is the presheaf of objects of `𝒮_F`: the fibre of `𝒮_F` over `U` is
`F(U)`, and the pullback along `f` in `𝒮_F` is `F(f)`. -/
noncomputable def unitIsoApp (F : Cᵒᵖ ⥤ Type (max u w)) :
    F ≅ (Functor.Elements.π F).leftOp.objPresheaf :=
  NatIso.ofComponents (fun U ↦ (CategoryOfElements.leftOpFiberEquiv F U).toIso)
    (fun {U V} f ↦ ConcreteCategory.ext_apply fun (x : F.obj U) ↦ by
      let φ : (CategoryOfElements.leftOpFiberEquiv F V (F.map f x)).1 ⟶
          (CategoryOfElements.leftOpFiberEquiv F U x).1 :=
        (Functor.Elements.homMk (x := F.elementsMk U x) (y := F.elementsMk V (F.map f x)) f rfl).op
      have : (Functor.Elements.π F).leftOp.IsHomLift f.unop φ :=
        CategoryTheory.IsHomLift.map (Functor.Elements.π F).leftOp φ
      exact (Functor.IsFiberedInSets.pullbackFiber_eq_of_isHomLift (Functor.Elements.π F).leftOp
        (CategoryOfElements.leftOpFiberEquiv F U x) f.unop
        (CategoryOfElements.leftOpFiberEquiv F V (F.map f x)) φ).symm)

/-- A category fibred in sets `p : 𝒮 ⥤ C` is isomorphic, in the category of categories fibred in
sets over `C`, to the category `𝒮_P` of its presheaf of objects `P : U ↦ Ob(𝒮_U)`. -/
noncomputable def counitIsoApp (𝒳 : CatFiberedInSets.{v, v, u, max u w} C) :
    elements 𝒳.val.p.objPresheaf ≅ 𝒳 where
  hom := Bicategory.InducedBicategory.mkHom
    ({ toFunctor := Functor.fromElementsObjPresheaf 𝒳.val.p
       w := Functor.fromElementsObjPresheaf_comp 𝒳.val.p } :
      BasedFunctor (BasedCategory.ofFunctor (Functor.Elements.π 𝒳.val.p.objPresheaf).leftOp)
        𝒳.val)
  inv := Bicategory.InducedBicategory.mkHom
    ({ toFunctor := Functor.toElementsObjPresheaf 𝒳.val.p
       w := Functor.toElementsObjPresheaf_comp 𝒳.val.p } :
      BasedFunctor 𝒳.val
        (BasedCategory.ofFunctor (Functor.Elements.π 𝒳.val.p.objPresheaf).leftOp))
  hom_inv_id := hom_ext_of_obj fun a ↦ by
    obtain ⟨@⟨⟨U⟩, ⟨x, hx⟩⟩⟩ := a
    change 𝒳.val.p.obj x = U at hx
    subst hx
    rfl
  inv_hom_id := hom_ext_of_obj fun _ ↦ rfl

/-- **Stacks 02Y2**, the equivalence. Let `C` be a category. There is an equivalence of categories
between the category of presheaves of sets on `C` and the category of categories fibred in sets
over `C`. The functor from left to right is the construction `F ↦ 𝒮_F` of Stacks 04TM
(`CategoryTheory.CatFiberedInSets.ofPresheaf`), and the functor from right to left sends
`p : 𝒮 ⥤ C` to its presheaf of objects `U ↦ Ob(𝒮_U)`
(`CategoryTheory.CatFiberedInSets.objPresheafFunctor`); see
`CategoryTheory.CatFiberedInSets.presheafEquivalence_functor` and
`CategoryTheory.CatFiberedInSets.presheafEquivalence_inverse`. -/
@[stacks 02Y2 "presheaves of sets ≌ categories fibred in sets: F ↦ S_F, p ↦ (U ↦ Ob(S_U))"]
noncomputable def presheafEquivalence :
    (Cᵒᵖ ⥤ Type (max u w)) ≌ CatFiberedInSets.{v, v, u, max u w} C :=
  CategoryTheory.Equivalence.mk ofPresheaf objPresheafFunctor
    (NatIso.ofComponents (fun F ↦ unitIsoApp F)
      (fun _ ↦ NatTrans.ext' (funext fun _ ↦ ConcreteCategory.ext_apply fun _ ↦ rfl)))
    (NatIso.ofComponents (fun 𝒳 ↦ counitIsoApp 𝒳) (fun _ ↦ hom_ext_of_obj fun _ ↦ rfl))

/-- The functor of `CategoryTheory.CatFiberedInSets.presheafEquivalence` is `F ↦ 𝒮_F`. -/
lemma presheafEquivalence_functor :
    (presheafEquivalence : (Cᵒᵖ ⥤ Type (max u w)) ≌ CatFiberedInSets.{v, v, u, max u w} C).functor =
      ofPresheaf :=
  rfl

/-- The inverse of `CategoryTheory.CatFiberedInSets.presheafEquivalence` sends `p : 𝒮 ⥤ C` to its
presheaf of objects `U ↦ Ob(𝒮_U)`. -/
lemma presheafEquivalence_inverse :
    (presheafEquivalence : (Cᵒᵖ ⥤ Type (max u w)) ≌ CatFiberedInSets.{v, v, u, max u w} C).inverse =
      objPresheafFunctor :=
  rfl

end Presheaf

end CatFiberedInSets

end CategoryTheory
