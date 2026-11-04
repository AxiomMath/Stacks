module

public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack
public import StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.Pushforward

/-!
# Fibres of the pushforward of a fibred category

Let `u : 𝒞 ⥤ 𝒟` be a functor and `p : 𝒮 ⥤ 𝒟` a category over `𝒟`. The fibre of the pushforward
`u^p𝒮 ⥤ 𝒞` over `U : 𝒞` is the fibre of `p` over `u U`: an object of `u^p𝒮` over `U` *is* an
object of `𝒮` over `u U`, and a morphism over `𝟙 U` *is* a morphism over `𝟙 (u U)`. This file
records that identification and the transport of (strong) cartesianness across it, which is what
lets a property of `p` over `u U` be read as the same property of `u^p𝒮` over `U`.

## Main results

* `CategoryTheory.StrictPullback.fiberFib` and `CategoryTheory.StrictPullback.fiberMk`, the two
  directions of the identification of `(u^p𝒮)_U` with `𝒮_{u U}`;
* `CategoryTheory.StrictPullback.isStronglyCartesian_of_fib'`, a morphism of `u^p𝒮` is strongly
  cartesian as soon as its `𝒮`-component is;
* `CategoryTheory.StrictPullback.isStronglyCartesian_fib` and
  `CategoryTheory.StrictPullback.isStronglyCartesian_fib_of_isCartesian`, the converse over a
  fibred `p`, so that the two notions agree; this is the step the proof of Stacks 04WC turns on;
* `CategoryTheory.StrictPullback.fiberFibPullbackIso`, the comparison of the two chosen pullbacks
  that the identification produces: the `𝒮`-component of the chosen `u^p𝒮`-pullback of `x` along
  `g`, and the chosen `p`-pullback of the `𝒮`-component of `x` along `u g`. Taking chosen pullbacks
  commutes with the identification only up to that isomorphism, and every use of the identification
  below and in the files that build on it goes through it.
-/

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒟 : Type u₂} [Category.{v₂} 𝒟]
  {𝒮 : Type u₃} [Category.{v₃} 𝒮] {u : 𝒞 ⥤ 𝒟} {p : 𝒮 ⥤ 𝒟}

namespace StrictPullback

/-- The object of `𝒮` over `u U` underlying an object of `u^p𝒮` over `U`. -/
@[implicit_reducible]
def fiberFib {U : 𝒞} (x : (structureFunctor u p).Fiber U) : p.Fiber (u.obj U) :=
  ⟨x.1.fib, by rw [x.1.over]; exact congrArg u.obj x.2⟩

/-- An object of `𝒮` over `u U` read as an object of `u^p𝒮` over `U`. -/
def fiberMk {U : 𝒞} (y : p.Fiber (u.obj U)) : (structureFunctor u p).Fiber U :=
  ⟨⟨U, y.1, y.2⟩, rfl⟩

/-- Reading an object of `𝒮` over `u U` as an object of `u^p𝒮` over `U` and back gives it
again. -/
@[simp] lemma fiberFib_fiberMk {U : 𝒞} (y : p.Fiber (u.obj U)) :
    fiberFib (u := u) (fiberMk y) = y := rfl

/-- Reading an object of `u^p𝒮` over `U` in `𝒮` and back gives it again; together with
`StrictPullback.fiberFib_fiberMk` this makes `(u^p𝒮)_U` and `𝒮_{u U}` the same collection of
objects. -/
@[simp] lemma fiberMk_fiberFib {U : 𝒞} (x : (structureFunctor u p).Fiber U) :
    fiberMk (fiberFib x) = x := by
  obtain ⟨⟨V, y, hy⟩, rfl⟩ := x
  rfl

/-- The object of `𝒮` underlying `StrictPullback.fiberFib x` is the `𝒮`-component of `x`. -/
@[simp] lemma fiberFib_val {U : 𝒞} (x : (structureFunctor u p).Fiber U) :
    (fiberFib x).1 = x.1.fib := rfl

/-- Every morphism of `u^p𝒮` has `𝒮`-component lying over the image of its `𝒞`-component. -/
instance isHomLift_fib {X Y : StrictPullback u p} (f : X ⟶ Y) :
    p.IsHomLift (u.map f.base) f.fib :=
  IsHomLift.of_fac' p _ _ X.over Y.over f.over

/-- A morphism of `u^p𝒮` from a morphism of `𝒞` and a morphism of `𝒮` lying over its image. -/
def homMk {X Y : StrictPullback u p} (a : X.base ⟶ Y.base) (β : X.fib ⟶ Y.fib)
    [p.IsHomLift (u.map a) β] : X ⟶ Y :=
  ⟨a, β, IsHomLift.fac' p (u.map a) β⟩

/-- The `𝒞`-component of `StrictPullback.homMk a β` is `a`. -/
@[simp] lemma homMk_base {X Y : StrictPullback u p} (a : X.base ⟶ Y.base) (β : X.fib ⟶ Y.fib)
    [p.IsHomLift (u.map a) β] : (homMk a β).base = a := rfl

/-- The `𝒮`-component of `StrictPullback.homMk a β` is `β`. -/
@[simp] lemma homMk_fib {X Y : StrictPullback u p} (a : X.base ⟶ Y.base) (β : X.fib ⟶ Y.fib)
    [p.IsHomLift (u.map a) β] : (homMk a β).fib = β := rfl

/-- A morphism of `u^p𝒮` is strongly cartesian over `𝒞` as soon as its `𝒮`-component is strongly
cartesian over the image of its `𝒞`-component. -/
lemma isStronglyCartesian_of_fib' {X Y : StrictPullback u p} (f : X ⟶ Y)
    (hβ : p.IsStronglyCartesian (u.map f.base) f.fib) :
    (structureFunctor u p).IsStronglyCartesian f.base f :=
  isStronglyCartesian_of_fib f
    (Functor.IsStronglyCartesian.eqToHom_comp_eqToHom X.over Y.over.symm _ _ hβ)

/-- A morphism of `u^p𝒮` lying over `a` has source and target bases those of `a`. -/
private lemma base_eq_of_isHomLift {V U : 𝒞} {X Y : StrictPullback u p} (a : V ⟶ U) (f : X ⟶ Y)
    [(structureFunctor u p).IsHomLift a f] : X.base = V ∧ Y.base = U :=
  ⟨IsHomLift.domain_eq (structureFunctor u p) a f, IsHomLift.codomain_eq (structureFunctor u p) a f⟩

/-- The `𝒮`-component of a morphism of `u^p𝒮` lying over `a` lies over `u a`. -/
lemma isHomLift_fib_of_isHomLift {V U : 𝒞} {X Y : StrictPullback u p} (a : V ⟶ U) (f : X ⟶ Y)
    (hf : (structureFunctor u p).IsHomLift a f) : p.IsHomLift (u.map a) f.fib := by
  have := hf
  obtain ⟨rfl, rfl⟩ := base_eq_of_isHomLift a f
  rw [← base_eq a f]
  infer_instance

/-- The `𝒮`-component of a morphism of `u^p𝒮` lying over `𝟙 U` lies over `𝟙 (u U)`. -/
lemma isHomLift_id_fib {U : 𝒞} {X Y : StrictPullback u p} (f : X ⟶ Y)
    (hf : (structureFunctor u p).IsHomLift (𝟙 U) f) : p.IsHomLift (𝟙 (u.obj U)) f.fib := by
  have := isHomLift_fib_of_isHomLift (𝟙 U) f hf
  rwa [u.map_id] at this

/-- Over a fibred `p`, the `𝒮`-component of a cartesian morphism of `u^p𝒮` is strongly cartesian
over the image of its `𝒞`-component. Together with `isStronglyCartesian_of_fib'` this says that a
morphism `(a, β)` of `u^p𝒮` is strongly cartesian if and only if `β` is strongly cartesian in `𝒮`,
which is the identification of pullback functors the proof of Stacks 04WC turns on. -/
lemma isStronglyCartesian_fib [p.IsFibered] {X Y : StrictPullback u p} (f : X ⟶ Y)
    (hf : (structureFunctor u p).IsCartesian f.base f) :
    p.IsStronglyCartesian (u.map f.base) f.fib := by
  have := hf
  obtain ⟨y, β, hβ⟩ := Functor.IsPreFibered.exists_isCartesian' (p := p) (a := Y.fib)
    (u.map f.base ≫ eqToHom Y.over.symm)
  have hβ' : p.IsCartesian (u.map f.base ≫ eqToHom Y.over.symm) β := hβ
  have hy : p.obj y = u.obj X.base :=
    IsHomLift.domain_eq p (u.map f.base ≫ eqToHom Y.over.symm) β
  have hβs : p.IsStronglyCartesian (u.map f.base) β :=
    Functor.IsStronglyCartesian.of_comp_eqToHom Y.over.symm _ _ inferInstance
  let X' : StrictPullback u p := ⟨X.base, y, hy⟩
  have hβl : p.IsHomLift (u.map f.base) β := hβs.toIsHomLift
  let g : X' ⟶ Y := homMk (X := X') f.base β
  have hg : (structureFunctor u p).IsStronglyCartesian f.base g :=
    isStronglyCartesian_of_fib' g hβs
  have hgc : (structureFunctor u p).IsCartesian f.base g := have := hg; inferInstance
  have := hgc
  let e := Functor.IsCartesian.domainUniqueUpToIso (structureFunctor u p) f.base g f
  have hfac : e.hom ≫ g = f := Functor.IsCartesian.fac _ f.base g f
  have hefib : p.IsHomLift (𝟙 (u.obj X.base)) e.hom.fib :=
    isHomLift_id_fib e.hom
      (Functor.IsCartesian.domainUniqueUpToIso_inv_isHomLift (structureFunctor u p) f.base g f)
  have : IsIso e.hom.fib :=
    ⟨e.inv.fib, by rw [← comp_fib, e.hom_inv_id, id_fib], by rw [← comp_fib, e.inv_hom_id, id_fib]⟩
  have := hefib
  have hcomp : p.IsStronglyCartesian (𝟙 (u.obj X.base) ≫ u.map f.base) (e.hom.fib ≫ β) :=
    have := hβs
    inferInstance
  rw [Category.id_comp] at hcomp
  have hffib : f.fib = e.hom.fib ≫ β := by rw [← hfac]; rfl
  rwa [hffib]

/-- Over a fibred `p`, the `𝒮`-component of a morphism of `u^p𝒮` cartesian over `a` is strongly
cartesian over `u a`. This is `StrictPullback.isStronglyCartesian_fib` with the base morphism
named, rather than read off the morphism. -/
lemma isStronglyCartesian_fib_of_isCartesian [p.IsFibered] {V U : 𝒞}
    {X Y : StrictPullback u p} (a : V ⟶ U) (f : X ⟶ Y)
    (hf : (structureFunctor u p).IsCartesian a f) : p.IsStronglyCartesian (u.map a) f.fib := by
  have := hf
  obtain ⟨rfl, rfl⟩ := base_eq_of_isHomLift a f
  rw [← base_eq a f]
  exact isStronglyCartesian_fib f (by rw [base_eq a f]; exact hf)

/-- A morphism of `u^p𝒮` from a morphism of `𝒞` and a morphism of `𝒮` lying over its image, with
the lifting property as an argument rather than an instance. -/
def homMk' {X Y : StrictPullback u p} (a : X.base ⟶ Y.base) (β : X.fib ⟶ Y.fib)
    (hβ : p.IsHomLift (u.map a) β) : X ⟶ Y :=
  have := hβ
  homMk a β

/-- The `𝒞`-component of `StrictPullback.homMk' a β hβ` is `a`. -/
@[simp] lemma homMk'_base {X Y : StrictPullback u p} (a : X.base ⟶ Y.base) (β : X.fib ⟶ Y.fib)
    (hβ : p.IsHomLift (u.map a) β) : (homMk' a β hβ).base = a := rfl

/-- The `𝒮`-component of `StrictPullback.homMk' a β hβ` is `β`. -/
@[simp] lemma homMk'_fib {X Y : StrictPullback u p} (a : X.base ⟶ Y.base) (β : X.fib ⟶ Y.fib)
    (hβ : p.IsHomLift (u.map a) β) : (homMk' a β hβ).fib = β := rfl

/-! ### The two chosen pullbacks

The chosen pullback of `x` along `g : V ⟶ U` taken in `u^p𝒮` and the chosen pullback of the
`𝒮`-component of `x` along `u g` taken in `𝒮` are two independent choices. They are canonically
isomorphic in the fibre of `p` over `u V`, since the `𝒮`-component of the first is again a
cartesian lift of `u g`. -/

section PullbackFib

-- The domain and codomain of the chosen cartesian lifts compared below are stated through
-- `Functor.pullbackFiber` and `StrictPullback.fiberFib`, so the instance arguments of
-- `IsHomLift` and `IsCartesian` are only found after unfolding those.
set_option backward.isDefEq.respectTransparency false

variable [p.IsFibered]

/-- The `𝒮`-component of the chosen `u^p𝒮`-pullback of `x` along `g` is strongly cartesian over
`u g`. -/
lemma isStronglyCartesian_pullbackMap_fib {U : 𝒞} (x : (structureFunctor u p).Fiber U) {V : 𝒞}
    (g : V ⟶ U) :
    p.IsStronglyCartesian (u.map g) (Functor.IsPreFibered.pullbackMap x.2 g).fib :=
  isStronglyCartesian_fib_of_isCartesian g _ (Functor.IsPreFibered.pullbackMap.IsCartesian x.2 g)

/-- The `𝒮`-component of the chosen `u^p𝒮`-pullback of `x` along `g` is cartesian over `u g`. -/
lemma isCartesian_pullbackMap_fib {U : 𝒞} (x : (structureFunctor u p).Fiber U) {V : 𝒞}
    (g : V ⟶ U) : p.IsCartesian (u.map g) (Functor.IsPreFibered.pullbackMap x.2 g).fib := by
  have := isStronglyCartesian_pullbackMap_fib x g
  infer_instance

/-- The chosen `p`-pullback along `u g` of the `𝒮`-component of `x`, compared with the
`𝒮`-component
of the chosen `u^p𝒮`-pullback of `x` along `g`: both carry a cartesian morphism over `u g` to the
`𝒮`-component of `x`. This is the failure of `StrictPullback.fiberFib` to commute with chosen
pullbacks, and the whole of it. -/
noncomputable def fiberFibPullbackIso {U V : 𝒞} (x : (structureFunctor u p).Fiber U) (g : V ⟶ U) :
    Functor.pullbackFiber p (fiberFib x) (u.map g) ≅
      fiberFib (Functor.pullbackFiber (structureFunctor u p) x g) :=
  have := isCartesian_pullbackMap_fib x g
  Functor.fiberIsoOfCartesian (u.map g)
    (Functor.IsPreFibered.pullbackMap (fiberFib x).2 (u.map g))
    ((Functor.IsPreFibered.pullbackMap x.2 g).fib)
    (Functor.IsPreFibered.pullbackMap.IsCartesian _ _) inferInstance

/-- `StrictPullback.fiberFibPullbackIso` factors the chosen `p`-pullback of the `𝒮`-component of
`x` along `u g` through the `𝒮`-component of the chosen `u^p𝒮`-pullback of `x` along `g`. -/
@[reassoc (attr := simp)]
lemma fiberFibPullbackIso_hom_fac {U V : 𝒞} (x : (structureFunctor u p).Fiber U) (g : V ⟶ U) :
    Functor.Fiber.fiberInclusion.map (fiberFibPullbackIso x g).hom ≫
        (Functor.IsPreFibered.pullbackMap x.2 g).fib =
      Functor.IsPreFibered.pullbackMap (fiberFib x).2 (u.map g) :=
  Functor.fiberIsoOfCartesian_hom_fac _ _ _ _ _

/-- The inverse factorization: `StrictPullback.fiberFibPullbackIso` factors the `𝒮`-component of
the
chosen `u^p𝒮`-pullback of `x` along `g` through the chosen `p`-pullback of the `𝒮`-component of `x`
along `u g`. -/
@[reassoc (attr := simp)]
lemma fiberFibPullbackIso_inv_fac {U V : 𝒞} (x : (structureFunctor u p).Fiber U) (g : V ⟶ U) :
    Functor.Fiber.fiberInclusion.map (fiberFibPullbackIso x g).inv ≫
        Functor.IsPreFibered.pullbackMap (fiberFib x).2 (u.map g) =
      (Functor.IsPreFibered.pullbackMap x.2 g).fib :=
  Functor.fiberIsoOfCartesian_inv_fac _ _ _ _ _

end PullbackFib

end StrictPullback

end CategoryTheory
