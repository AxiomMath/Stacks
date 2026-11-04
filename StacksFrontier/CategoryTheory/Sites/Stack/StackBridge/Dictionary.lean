module

public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.MorGluing
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Stack

/-!
# The dictionary between arbitrary cartesian lifts and the chosen pullbacks

`CategoryTheory.Functor.IsStack` (Stacks 026F) is phrased with the *chosen* pullbacks of a fibred
category, while `CategoryTheory.Functor.IsStackInGroupoids` (Stacks 02ZI) is phrased with arbitrary
cartesian lifts (`CategoryTheory.Functor.Restriction`). This file is the translation between the
two: a restriction of `x` along `f` is canonically isomorphic, in the fibre, to the chosen pullback
of `x` along `f`, because both carry a cartesian morphism to `x` over `f`.

Base change of a morphism between chosen pullbacks is taken along a *named* composite, as in
`CategoryTheory.Functor.pullbackFiberCompIso'`, so that the result can be compared with data given
at that name rather than at the composite; its transitivity and unit laws are proved here.

## Main definitions

* `CategoryTheory.Functor.Restriction.fiberIso` and
  `CategoryTheory.Functor.Restriction.fiberMor`, the dictionary between an arbitrary cartesian lift
  and the chosen pullback, and between a `CategoryTheory.Functor.FibreHom` of two restrictions and
  a morphism of the chosen pullbacks;
* `CategoryTheory.Functor.baseChangeFiberMor` and
  `CategoryTheory.Functor.baseChangeFiberIso`, base change along a named composite, with
  `CategoryTheory.Functor.baseChangeFiberMor_baseChangeFiberMor` and
  `CategoryTheory.Functor.baseChangeFiberMor_id` its transitivity and unit laws.

## Main results

* `CategoryTheory.Functor.fiberMor_eq_baseChangeFiberMor`, the translation of
  `CategoryTheory.Functor.IsRestrictionOf` into an identity between base changes;
* `CategoryTheory.Functor.pullbackFiberHom_eq_fiberMor_iff`, the criterion for a morphism of the
  fibre over `U` to restrict to a given fibre morphism between two restrictions.
-/

@[expose] public section

namespace CategoryTheory

open Limits

universe w v₁ v₂ u₁ u₂

namespace Functor

attribute [local implicit_reducible] Fiber Fiber.fiberInclusion

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]

variable {p : 𝒳 ⥤ 𝒞}

/-- A restriction lies over the base morphism it is a restriction along, with the endpoint
equalities read off rather than carried as `eqToHom`s. -/
lemma Restriction.isHomLift_hom {U V : 𝒞} {f : V ⟶ U} {x : 𝒳} {hx : p.obj x = U}
    (xr : Restriction p f x hx) : p.IsHomLift f xr.hom := by
  refine IsHomLift.of_fac' p f xr.hom xr.hpt hx ?_
  simpa using IsHomLift.fac' p (eqToHom xr.hpt ≫ f ≫ eqToHom hx.symm) xr.hom

/-- The cartesian morphism of a restriction is strongly cartesian over the base morphism itself. -/
lemma Restriction.isStronglyCartesian_hom {U V : 𝒞} {f : V ⟶ U} {x : 𝒳} {hx : p.obj x = U}
    (xr : Restriction p f x hx) : p.IsStronglyCartesian f xr.hom := by
  obtain ⟨pt, hpt, hom, hlift, hcart⟩ := xr
  subst hpt hx
  simpa using hcart

/-- A `CategoryTheory.Functor.FibreHom` read as a morphism of the fibre category. -/
def fibreHomMk {V : 𝒞} {a b : 𝒳} {ha : p.obj a = V} {hb : p.obj b = V} {φ : a ⟶ b}
    (hφ : FibreHom p a b ha hb φ) : (Fiber.mk ha : p.Fiber V) ⟶ Fiber.mk hb :=
  ⟨φ, by
    have : p.IsHomLift (eqToHom ha ≫ eqToHom hb.symm) φ := hφ
    refine IsHomLift.of_fac' p (𝟙 V) φ ha hb ?_
    simpa using IsHomLift.fac' p (eqToHom ha ≫ eqToHom hb.symm) φ⟩

/-- The underlying morphism of `𝒳` of `CategoryTheory.Functor.fibreHomMk hφ` is `φ` itself. -/
@[simp]
lemma fiberInclusion_map_fibreHomMk {V : 𝒞} {a b : 𝒳} {ha : p.obj a = V} {hb : p.obj b = V}
    {φ : a ⟶ b} (hφ : FibreHom p a b ha hb φ) :
    Fiber.fiberInclusion.map (fibreHomMk hφ) = φ := rfl

/-- A morphism of the fibre category read as a `CategoryTheory.Functor.FibreHom`. -/
lemma fibreHom_of_fiberHom {V : 𝒞} {a b : p.Fiber V} (φ : a ⟶ b) :
    FibreHom p a.1 b.1 a.2 b.2 (Fiber.fiberInclusion.map φ) := by
  have := φ.2
  refine IsHomLift.of_fac' p (eqToHom a.2 ≫ eqToHom b.2.symm) (Fiber.fiberInclusion.map φ)
    rfl rfl ?_
  simpa using IsHomLift.fac' p (𝟙 V) (Fiber.fiberInclusion.map φ)

/-- Transporting `CategoryTheory.Functor.IsHomLift` along an equality of base morphisms. -/
lemma isHomLift_of_eq {W V : 𝒞} {n m : W ⟶ V} {a b : 𝒳} {φ : a ⟶ b}
    (h : p.IsHomLift n φ) (hnm : n = m) : p.IsHomLift m φ :=
  hnm ▸ h

/-- The base morphism a given morphism lies over is unique. -/
lemma eq_of_isHomLift_of_isHomLift {R S : 𝒞} {a b : 𝒳} {n n' : R ⟶ S} {φ : a ⟶ b}
    (h : p.IsHomLift n φ) (h' : p.IsHomLift n' φ) : n = n' := by
  have := h
  have := h'
  rw [IsHomLift.fac p n φ, IsHomLift.fac p n' φ]

/-- The cartesian morphism of a restriction is cartesian over the base morphism itself. -/
lemma Restriction.isCartesian_hom {U V : 𝒞} {f : V ⟶ U} {x : 𝒳} {hx : p.obj x = U}
    (xr : Restriction p f x hx) : p.IsCartesian f xr.hom := by
  have := xr.isStronglyCartesian_hom
  infer_instance

variable [p.IsFibered]

/-- **The dictionary.** A restriction of `x` along `f` is canonically isomorphic, in the fibre over
the source of `f`, to the chosen pullback of `x` along `f`: both carry a cartesian morphism to `x`
over `f`. -/
noncomputable def Restriction.fiberIso {U V : 𝒞} {f : V ⟶ U} {x : 𝒳} {hx : p.obj x = U}
    (xr : Restriction p f x hx) :
    pullbackFiber p (Fiber.mk hx) f ≅ (Fiber.mk xr.hpt : p.Fiber V) :=
  fiberIsoOfCartesian f (IsPreFibered.pullbackMap (Fiber.mk hx : p.Fiber U).2 f) xr.hom
    (IsPreFibered.pullbackMap.IsCartesian _ _) xr.isCartesian_hom

/-- The forward direction of `CategoryTheory.Functor.Restriction.fiberIso` composed with the
cartesian morphism of the restriction is the chosen cartesian lift of `f` at `x`. -/
@[reassoc (attr := simp)]
lemma Restriction.fiberIso_hom_fac {U V : 𝒞} {f : V ⟶ U} {x : 𝒳} {hx : p.obj x = U}
    (xr : Restriction p f x hx) :
    Fiber.fiberInclusion.map xr.fiberIso.hom ≫ xr.hom =
      IsPreFibered.pullbackMap (Fiber.mk hx : p.Fiber U).2 f :=
  fiberIsoOfCartesian_hom_fac _ _ _ _ _

/-- The inverse direction of `CategoryTheory.Functor.Restriction.fiberIso` composed with the chosen
cartesian lift of `f` at `x` is the cartesian morphism of the restriction. -/
@[reassoc (attr := simp)]
lemma Restriction.fiberIso_inv_fac {U V : 𝒞} {f : V ⟶ U} {x : 𝒳} {hx : p.obj x = U}
    (xr : Restriction p f x hx) :
    Fiber.fiberInclusion.map xr.fiberIso.inv ≫
        IsPreFibered.pullbackMap (Fiber.mk hx : p.Fiber U).2 f = xr.hom :=
  fiberIsoOfCartesian_inv_fac _ _ _ _ _

/-- A fibre morphism between two restrictions, read as a morphism between the chosen pullbacks. -/
noncomputable def Restriction.fiberMor {Ux Uy V : 𝒞} {fx : V ⟶ Ux} {fy : V ⟶ Uy} {x y : 𝒳}
    {hx : p.obj x = Ux} {hy : p.obj y = Uy}
    (xr : Restriction p fx x hx) (yr : Restriction p fy y hy)
    {φ : xr.pt ⟶ yr.pt} (hφ : FibreHom p xr.pt yr.pt xr.hpt yr.hpt φ) :
    pullbackFiber p (Fiber.mk hx) fx ⟶ pullbackFiber p (Fiber.mk hy) fy :=
  xr.fiberIso.hom ≫ fibreHomMk hφ ≫ yr.fiberIso.inv

set_option backward.isDefEq.respectTransparency false in
/-- `CategoryTheory.Functor.Restriction.fiberMor` is pinned down by its composite with the chosen
cartesian lift of `fy` at `y`, which is `φ` conjugated by the cartesian morphisms of the two
restrictions. -/
@[reassoc (attr := simp)]
lemma Restriction.fiberMor_fac {Ux Uy V : 𝒞} {fx : V ⟶ Ux} {fy : V ⟶ Uy} {x y : 𝒳}
    {hx : p.obj x = Ux} {hy : p.obj y = Uy}
    (xr : Restriction p fx x hx) (yr : Restriction p fy y hy)
    {φ : xr.pt ⟶ yr.pt} (hφ : FibreHom p xr.pt yr.pt xr.hpt yr.hpt φ) :
    Fiber.fiberInclusion.map (xr.fiberMor yr hφ) ≫
        IsPreFibered.pullbackMap (Fiber.mk hy : p.Fiber Uy).2 fy =
      Fiber.fiberInclusion.map xr.fiberIso.hom ≫ φ ≫ yr.hom := by
  simp [Restriction.fiberMor]

/-- Base change of a morphism between chosen pullbacks along a *named* composite: the base morphism
`m` that `g ≫ f` equals is an argument, as in
`CategoryTheory.Functor.pullbackFiberCompIso'`, so that the result can be compared with data given
at `m` rather than at the composite. -/
noncomputable def baseChangeFiberMor {Ux Uy V W : 𝒞} {x : p.Fiber Ux} {y : p.Fiber Uy}
    {fx : V ⟶ Ux} {fy : V ⟶ Uy} (ψ : pullbackFiber p x fx ⟶ pullbackFiber p y fy) (g : W ⟶ V)
    (mx : W ⟶ Ux) (hmx : g ≫ fx = mx) (my : W ⟶ Uy) (hmy : g ≫ fy = my) :
    pullbackFiber p x mx ⟶ pullbackFiber p y my :=
  (pullbackFiberCompIso' x fx g mx hmx).inv ≫ pullbackFiberHom ψ g ≫
    (pullbackFiberCompIso' y fy g my hmy).hom

/-- `CategoryTheory.Functor.baseChangeFiberMor` is pinned down by its composite with the chosen
cartesian lift of `my` at `y`, which contracts the iterated chosen pullback of `x` and then applies
`ψ`. -/
@[reassoc (attr := simp)]
lemma baseChangeFiberMor_fac {Ux Uy V W : 𝒞} {x : p.Fiber Ux} {y : p.Fiber Uy}
    {fx : V ⟶ Ux} {fy : V ⟶ Uy} (ψ : pullbackFiber p x fx ⟶ pullbackFiber p y fy) (g : W ⟶ V)
    (mx : W ⟶ Ux) (hmx : g ≫ fx = mx) (my : W ⟶ Uy) (hmy : g ≫ fy = my) :
    Fiber.fiberInclusion.map (baseChangeFiberMor ψ g mx hmx my hmy) ≫
        IsPreFibered.pullbackMap y.2 my =
      Fiber.fiberInclusion.map (pullbackFiberCompIso' x fx g mx hmx).inv ≫
        IsPreFibered.pullbackMap (pullbackFiber p x fx).2 g ≫
          Fiber.fiberInclusion.map ψ ≫ IsPreFibered.pullbackMap y.2 fy := by
  simp [baseChangeFiberMor]

omit [p.IsFibered] in
/-- The canonical comparison of two restrictions of one object is the unique morphism over the
base morphism factoring the one cartesian lift through the other. -/
lemma Restriction.eq_compTo {U V W : 𝒞} (g : W ⟶ V) (f : V ⟶ U) {m : W ⟶ U} (hm : m = g ≫ f)
    {x : 𝒳} {hx : p.obj x = U} (xr : Restriction p f x hx) (xrW : Restriction p m x hx)
    (ψ : xrW.pt ⟶ xr.pt) (hψ : p.IsHomLift g ψ) (hfac : ψ ≫ xr.hom = xrW.hom) :
    ψ = Restriction.compTo p g f hm xr xrW := by
  have hcart := xr.isCart
  have hlift : p.IsHomLift ((eqToHom xrW.hpt ≫ g ≫ eqToHom xr.hpt.symm) ≫
      (eqToHom xr.hpt ≫ f ≫ eqToHom hx.symm)) xrW.hom := by
    have e : (eqToHom xrW.hpt ≫ g ≫ eqToHom xr.hpt.symm) ≫
        (eqToHom xr.hpt ≫ f ≫ eqToHom hx.symm) = eqToHom xrW.hpt ≫ m ≫ eqToHom hx.symm := by
      subst hm
      simp
    rw [e]
    exact xrW.isHomLift
  have hψ' : p.IsHomLift (eqToHom xrW.hpt ≫ g ≫ eqToHom xr.hpt.symm) ψ := by
    have := hψ
    refine IsHomLift.of_fac' p _ ψ rfl rfl ?_
    simpa using IsHomLift.fac' p g ψ
  exact IsStronglyCartesian.map_uniq p _ xr.hom rfl xrW.hom ψ hfac

/-- Two morphisms of a fibre agree once their composites with a chosen cartesian lift agree. -/
private lemma hom_ext_of_pullbackMap {U V : 𝒞} {y : p.Fiber U} {z : p.Fiber V}
    (f : V ⟶ U) {a b : z ⟶ pullbackFiber p y f}
    (h : Fiber.fiberInclusion.map a ≫ IsPreFibered.pullbackMap y.2 f =
      Fiber.fiberInclusion.map b ≫ IsPreFibered.pullbackMap y.2 f) : a = b :=
  fiber_hom_ext_of_cartesian f _ (IsPreFibered.pullbackMap.IsCartesian _ _) _ _ h

/-- The comparison of two restrictions of one object, read through the fibre dictionary, lies over
`g` and factors the cartesian lift of the first restriction through that of the second. -/
private lemma exists_isHomLift_fiberIso_comp {U V W : 𝒞} (g : W ⟶ V) (f : V ⟶ U) {m : W ⟶ U}
    (hm : m = g ≫ f) {x : 𝒳} {hx : p.obj x = U} (xr : Restriction p f x hx)
    (xrW : Restriction p m x hx) :
    ∃ σ : xrW.pt ⟶ xr.pt, p.IsHomLift g σ ∧ σ ≫ xr.hom = xrW.hom ∧
      σ = Fiber.fiberInclusion.map xrW.fiberIso.inv ≫
        Fiber.fiberInclusion.map (pullbackFiberCompIso' (Fiber.mk hx : p.Fiber U) f g m hm.symm).inv
          ≫ IsPreFibered.pullbackMap (pullbackFiber p (Fiber.mk hx : p.Fiber U) f).2 g ≫
        Fiber.fiberInclusion.map xr.fiberIso.hom := by
  set_option backward.isDefEq.respectTransparency false in
  refine ⟨_, ?_, ?_, rfl⟩
  · have := IsPreFibered.pullbackMap.IsCartesian
      (pullbackFiber p (Fiber.mk hx : p.Fiber U) f).2 g
    exact isHomLift_of_eq (n := 𝟙 W ≫ 𝟙 W ≫ g ≫ 𝟙 V) inferInstance (by simp)
  · simp only [Category.assoc, Restriction.fiberIso_hom_fac]
    rw [pullbackFiberCompIso'_inv_fac, Restriction.fiberIso_inv_fac]

/-- Contracting a threefold chosen pullback of one object in two steps agrees with contracting it
in one: the two comparisons `m'^* x ⟶ f^* x` over `n = g' ≫ g` agree. -/
@[reassoc]
lemma pullbackFiberCompIso'_inv_comp_pullbackMap {U V W W' : 𝒞} (x : p.Fiber U) (f : V ⟶ U)
    (g : W ⟶ V) (m : W ⟶ U) (hm : g ≫ f = m) (g' : W' ⟶ W) (m' : W' ⟶ U) (hm' : g' ≫ m = m')
    (n : W' ⟶ V) (hn : g' ≫ g = n) (hnm : n ≫ f = m') :
    Fiber.fiberInclusion.map (pullbackFiberCompIso' x m g' m' hm').inv ≫
        IsPreFibered.pullbackMap (pullbackFiber p x m).2 g' ≫
        Fiber.fiberInclusion.map (pullbackFiberCompIso' x f g m hm).inv ≫
        IsPreFibered.pullbackMap (pullbackFiber p x f).2 g =
      Fiber.fiberInclusion.map (pullbackFiberCompIso' x f n m' hnm).inv ≫
        IsPreFibered.pullbackMap (pullbackFiber p x f).2 n := by
  have hc1 := IsPreFibered.pullbackMap.IsCartesian (pullbackFiber p x m).2 g'
  have hc2 := IsPreFibered.pullbackMap.IsCartesian (pullbackFiber p x f).2 g
  have hc3 := IsPreFibered.pullbackMap.IsCartesian (pullbackFiber p x f).2 n
  have h1 : p.IsHomLift n
      (Fiber.fiberInclusion.map (pullbackFiberCompIso' x m g' m' hm').inv ≫
        IsPreFibered.pullbackMap (pullbackFiber p x m).2 g' ≫
        Fiber.fiberInclusion.map (pullbackFiberCompIso' x f g m hm).inv ≫
        IsPreFibered.pullbackMap (pullbackFiber p x f).2 g) :=
    isHomLift_of_eq (n := 𝟙 _ ≫ g' ≫ 𝟙 _ ≫ g) inferInstance (by simp [hn])
  have h2 : p.IsHomLift n
      (Fiber.fiberInclusion.map (pullbackFiberCompIso' x f n m' hnm).inv ≫
        IsPreFibered.pullbackMap (pullbackFiber p x f).2 n) :=
    isHomLift_of_eq (n := 𝟙 _ ≫ n) inferInstance (by simp)
  exact IsStronglyCartesian.ext p f (IsPreFibered.pullbackMap x.2 f) n
    (by simp [pullbackFiberCompIso'_inv_fac])

/-- Base change of a base change is base change along the composite. -/
lemma baseChangeFiberMor_baseChangeFiberMor {Ux Uy V W W' : 𝒞} {x : p.Fiber Ux} {y : p.Fiber Uy}
    {fx : V ⟶ Ux} {fy : V ⟶ Uy} (ψ : pullbackFiber p x fx ⟶ pullbackFiber p y fy) (g : W ⟶ V)
    (mx : W ⟶ Ux) (hmx : g ≫ fx = mx) (my : W ⟶ Uy) (hmy : g ≫ fy = my)
    (g' : W' ⟶ W) (mx' : W' ⟶ Ux) (hmx' : g' ≫ mx = mx') (my' : W' ⟶ Uy)
    (hmy' : g' ≫ my = my') :
    baseChangeFiberMor (baseChangeFiberMor ψ g mx hmx my hmy) g' mx' hmx' my' hmy' =
      baseChangeFiberMor ψ (g' ≫ g) mx' (by rw [Category.assoc, hmx, hmx']) my'
        (by rw [Category.assoc, hmy, hmy']) := by
  refine hom_ext_of_pullbackMap my' ?_
  simp only [baseChangeFiberMor_fac]
  rw [pullbackFiberCompIso'_inv_comp_pullbackMap_assoc x fx g mx hmx g' mx' hmx' (g' ≫ g) rfl
    (by rw [Category.assoc, hmx, hmx'])]

set_option backward.isDefEq.respectTransparency false in
/-- **The translation of `CategoryTheory.Functor.IsRestrictionOf`.** If `β` is the canonical
restriction of the fibre morphism `α` along `g`, then, read between the chosen pullbacks, `β` is
the base change of `α` along `g`. -/
lemma fiberMor_eq_baseChangeFiberMor {Ux Uy V W : 𝒞} {x y : 𝒳} {hx : p.obj x = Ux}
    {hy : p.obj y = Uy} {fx : V ⟶ Ux} {fy : V ⟶ Uy} {g : W ⟶ V} {mx : W ⟶ Ux} {my : W ⟶ Uy}
    (hmx : mx = g ≫ fx) (hmy : my = g ≫ fy)
    (xr : Restriction p fx x hx) (yr : Restriction p fy y hy)
    (xrW : Restriction p mx x hx) (yrW : Restriction p my y hy)
    {α : xr.pt ⟶ yr.pt} (hα : FibreHom p xr.pt yr.pt xr.hpt yr.hpt α)
    {β : xrW.pt ⟶ yrW.pt} (hβ : FibreHom p xrW.pt yrW.pt xrW.hpt yrW.hpt β)
    (h : IsRestrictionOf p g hmx hmy xr yr xrW yrW α β) :
    xrW.fiberMor yrW hβ =
      baseChangeFiberMor (xr.fiberMor yr hα) g mx hmx.symm my hmy.symm := by
  -- the comparison of the chosen pullback along `m` with the chosen pullback of the chosen
  -- pullback along `f`, read as a morphism into `xr.pt`
  obtain ⟨σ, hσlift, hσfac, hσ⟩ := exists_isHomLift_fiberIso_comp g fx hmx xr xrW
  -- the two sides agree after composing with the cartesian lift of `my` at `y`
  refine hom_ext_of_pullbackMap my ?_
  rw [Restriction.fiberMor_fac, baseChangeFiberMor_fac, Restriction.fiberMor_fac]
  -- `β ≫ yrW.hom` is `compTo ≫ α ≫ yr.hom`, by the hypothesis and the defining factorization
  have hkey : β ≫ yrW.hom = σ ≫ α ≫ yr.hom := by
    rw [← Restriction.compTo_hom p g fy hmy yr yrW, ← Category.assoc, h,
      Restriction.eq_compTo g fx hmx xr xrW σ hσlift hσfac, Category.assoc]
  rw [hkey, hσ]
  simp only [Category.assoc]
  rw [← Category.assoc (Fiber.fiberInclusion.map xrW.fiberIso.hom),
    ← Functor.map_comp, Iso.hom_inv_id, Functor.map_id, Category.id_comp]

/-- Two base changes along the same morphism agree, whichever proof witnesses the factorization. -/
lemma baseChangeFiberMor_congr {Ux Uy V W : 𝒞} {x : p.Fiber Ux} {y : p.Fiber Uy}
    {fx : V ⟶ Ux} {fy : V ⟶ Uy} (ψ : pullbackFiber p x fx ⟶ pullbackFiber p y fy)
    {g g' : W ⟶ V} (hgg : g = g') {mx : W ⟶ Ux} (hmx : g ≫ fx = mx) (hmx' : g' ≫ fx = mx)
    {my : W ⟶ Uy} (hmy : g ≫ fy = my) (hmy' : g' ≫ fy = my) :
    baseChangeFiberMor ψ g mx hmx my hmy = baseChangeFiberMor ψ g' mx hmx' my hmy' := by
  subst hgg
  rfl

/-- The chosen pullback along an identity of the chosen pullback along `f` is contracted by the
same isomorphism, whether one reads it as a contraction of an iterated pullback or as the pullback
along an identity. -/
lemma pullbackFiberCompIso'_id {U V : 𝒞} (x : p.Fiber U) (f : V ⟶ U) :
    pullbackFiberCompIso' x f (𝟙 V) f (Category.id_comp f) =
      pullbackFiberIdIso (pullbackFiber p x f) := by
  refine Iso.ext (hom_ext_of_pullbackMap f ?_)
  rw [pullbackFiberCompIso'_hom_fac, pullbackFiberIdIso_hom_fac]

/-- Base change of a morphism of a fibre along an identity is the morphism itself. -/
lemma pullbackFiberHom_id_base {V : 𝒞} {a b : p.Fiber V} (ψ : a ⟶ b) :
    pullbackFiberHom ψ (𝟙 V) ≫ (pullbackFiberIdIso b).hom =
      (pullbackFiberIdIso a).hom ≫ ψ := by
  refine Fiber.hom_ext ?_
  simp [pullbackFiberIdIso_hom_fac, pullbackFiberHom_fac]

/-- Base change along an identity is the identity operation. -/
lemma baseChangeFiberMor_id {Ux Uy V : 𝒞} {x : p.Fiber Ux} {y : p.Fiber Uy}
    {fx : V ⟶ Ux} {fy : V ⟶ Uy} (ψ : pullbackFiber p x fx ⟶ pullbackFiber p y fy) :
    baseChangeFiberMor ψ (𝟙 V) fx (Category.id_comp fx) fy (Category.id_comp fy) = ψ := by
  rw [baseChangeFiberMor, pullbackFiberCompIso'_id, pullbackFiberCompIso'_id,
    pullbackFiberHom_id_base, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- Base change of the base change of a morphism of a fibre: the base change of `α` along a named
composite is the base change along the second factor of the base change along the first. -/
lemma pullbackFiberHom_eq_baseChangeFiberMor {U V W : 𝒞} {x y : p.Fiber U} (α : x ⟶ y)
    (f : V ⟶ U) (g : W ⟶ V) (m : W ⟶ U) (hm : g ≫ f = m) :
    pullbackFiberHom α m = baseChangeFiberMor (pullbackFiberHom α f) g m hm m hm := by
  refine hom_ext_of_pullbackMap m ?_
  rw [pullbackFiberHom_fac, baseChangeFiberMor_fac, pullbackFiberHom_fac,
    pullbackFiberCompIso'_inv_fac_assoc]

/-- A `CategoryTheory.Functor.FibreHom` which is an isomorphism, read as an isomorphism of the
fibre category. -/
noncomputable def fibreIsoMk {V : 𝒞} {a b : 𝒳} {ha : p.obj a = V} {hb : p.obj b = V} {φ : a ⟶ b}
    (hφ : FibreHom p a b ha hb φ) (hiso : IsIso φ) : (Fiber.mk ha : p.Fiber V) ≅ Fiber.mk hb :=
  Fiber.isoMk (@asIso _ _ _ _ φ hiso) (fibreHomMk hφ).2

omit [p.IsFibered] in
/-- Reading a `CategoryTheory.Functor.FibreHom` as a morphism of the fibre is compatible with
composition. -/
lemma fibreHomMk_comp {V : 𝒞} {a b c : 𝒳} {ha : p.obj a = V} {hb : p.obj b = V} {hc : p.obj c = V}
    {α : a ⟶ b} {β : b ⟶ c} (hα : FibreHom p a b ha hb α) (hβ : FibreHom p b c hb hc β)
    (hαβ : FibreHom p a c ha hc (α ≫ β)) :
    fibreHomMk hαβ = fibreHomMk hα ≫ fibreHomMk hβ := Fiber.hom_ext rfl

omit [p.IsFibered] in
/-- The forward direction of `CategoryTheory.Functor.fibreIsoMk hφ hiso` is
`CategoryTheory.Functor.fibreHomMk hφ`. -/
@[simp]
lemma fibreIsoMk_hom {V : 𝒞} {a b : 𝒳} {ha : p.obj a = V} {hb : p.obj b = V} {φ : a ⟶ b}
    (hφ : FibreHom p a b ha hb φ) (hiso : IsIso φ) :
    (fibreIsoMk hφ hiso).hom = fibreHomMk hφ := rfl

/-- An isomorphism between two restrictions, read as an isomorphism between the chosen
pullbacks. -/
noncomputable def Restriction.fiberIsoOf {Ux Uy V : 𝒞} {fx : V ⟶ Ux} {fy : V ⟶ Uy} {x y : 𝒳}
    {hx : p.obj x = Ux} {hy : p.obj y = Uy}
    (xr : Restriction p fx x hx) (yr : Restriction p fy y hy)
    {φ : xr.pt ⟶ yr.pt} (hφ : FibreHom p xr.pt yr.pt xr.hpt yr.hpt φ) (hiso : IsIso φ) :
    pullbackFiber p (Fiber.mk hx) fx ≅ pullbackFiber p (Fiber.mk hy) fy :=
  xr.fiberIso ≪≫ fibreIsoMk hφ hiso ≪≫ yr.fiberIso.symm

/-- The forward direction of `CategoryTheory.Functor.Restriction.fiberIsoOf` is
`CategoryTheory.Functor.Restriction.fiberMor`. -/
@[simp]
lemma Restriction.fiberIsoOf_hom {Ux Uy V : 𝒞} {fx : V ⟶ Ux} {fy : V ⟶ Uy} {x y : 𝒳}
    {hx : p.obj x = Ux} {hy : p.obj y = Uy}
    (xr : Restriction p fx x hx) (yr : Restriction p fy y hy)
    {φ : xr.pt ⟶ yr.pt} (hφ : FibreHom p xr.pt yr.pt xr.hpt yr.hpt φ) (hiso : IsIso φ) :
    (xr.fiberIsoOf yr hφ hiso).hom = xr.fiberMor yr hφ := rfl

/-- Base change of an isomorphism between chosen pullbacks along a named composite. -/
noncomputable def baseChangeFiberIso {Ux Uy V W : 𝒞} {x : p.Fiber Ux} {y : p.Fiber Uy}
    {fx : V ⟶ Ux} {fy : V ⟶ Uy} (e : pullbackFiber p x fx ≅ pullbackFiber p y fy) (g : W ⟶ V)
    (mx : W ⟶ Ux) (hmx : g ≫ fx = mx) (my : W ⟶ Uy) (hmy : g ≫ fy = my) :
    pullbackFiber p x mx ≅ pullbackFiber p y my :=
  (pullbackFiberCompIso' x fx g mx hmx).symm ≪≫ pullbackFiberIso e g ≪≫
    pullbackFiberCompIso' y fy g my hmy

/-- The forward direction of `CategoryTheory.Functor.baseChangeFiberIso` is the base change of the
forward direction of `e`. -/
@[simp]
lemma baseChangeFiberIso_hom {Ux Uy V W : 𝒞} {x : p.Fiber Ux} {y : p.Fiber Uy}
    {fx : V ⟶ Ux} {fy : V ⟶ Uy} (e : pullbackFiber p x fx ≅ pullbackFiber p y fy) (g : W ⟶ V)
    (mx : W ⟶ Ux) (hmx : g ≫ fx = mx) (my : W ⟶ Uy) (hmy : g ≫ fy = my) :
    (baseChangeFiberIso e g mx hmx my hmy).hom = baseChangeFiberMor e.hom g mx hmx my hmy := rfl

set_option backward.isDefEq.respectTransparency false in
/-- A morphism of the fibre over `U` restricts to a given fibre morphism between two restrictions
exactly when its base change to the chosen pullbacks is the reading of that fibre morphism. -/
lemma pullbackFiberHom_eq_fiberMor_iff {U V : 𝒞} {f : V ⟶ U} {x y : 𝒳} {hx : p.obj x = U}
    {hy : p.obj y = U} (xr : Restriction p f x hx) (yr : Restriction p f y hy)
    {φ : xr.pt ⟶ yr.pt} (hφ : FibreHom p xr.pt yr.pt xr.hpt yr.hpt φ)
    (m : (Fiber.mk hx : p.Fiber U) ⟶ Fiber.mk hy) :
    pullbackFiberHom m f = xr.fiberMor yr hφ ↔
      xr.hom ≫ Fiber.fiberInclusion.map m = φ ≫ yr.hom := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have h2 := congrArg (fun t => Fiber.fiberInclusion.map t ≫
      IsPreFibered.pullbackMap (Fiber.mk hy : p.Fiber U).2 f) h
    simp only [pullbackFiberHom_fac, Restriction.fiberMor_fac] at h2
    rw [← Restriction.fiberIso_hom_fac xr, Category.assoc] at h2
    exact (cancel_epi (Fiber.fiberInclusion.map xr.fiberIso.hom)).1 h2
  · refine hom_ext_of_pullbackMap f ?_
    rw [pullbackFiberHom_fac, Restriction.fiberMor_fac, ← Restriction.fiberIso_hom_fac xr,
      Category.assoc, h]

set_option backward.isDefEq.respectTransparency false in
/-- The canonical comparison of two restrictions of one object lies over the base morphism it is
taken along. -/
lemma Restriction.isHomLift_compTo {U V W : 𝒞} (g : W ⟶ V) (f : V ⟶ U) {m : W ⟶ U}
    (hm : m = g ≫ f) {x : 𝒳} {hx : p.obj x = U} (xr : Restriction p f x hx)
    (xrW : Restriction p m x hx) : p.IsHomLift g (Restriction.compTo p g f hm xr xrW) := by
  obtain ⟨σ, hσlift, hσfac, -⟩ := exists_isHomLift_fiberIso_comp g f hm xr xrW
  rw [← Restriction.eq_compTo g f hm xr xrW σ hσlift hσfac]
  exact hσlift

/-- Base change is compatible with composition. -/
lemma baseChangeFiberMor_comp {Ux Uy Uz V W : 𝒞} {x : p.Fiber Ux} {y : p.Fiber Uy}
    {z : p.Fiber Uz} {fx : V ⟶ Ux} {fy : V ⟶ Uy} {fz : V ⟶ Uz}
    (χ₁ : pullbackFiber p x fx ⟶ pullbackFiber p y fy)
    (χ₂ : pullbackFiber p y fy ⟶ pullbackFiber p z fz) (g : W ⟶ V)
    (mx : W ⟶ Ux) (hmx : g ≫ fx = mx) (my : W ⟶ Uy) (hmy : g ≫ fy = my)
    (mz : W ⟶ Uz) (hmz : g ≫ fz = mz) :
    baseChangeFiberMor (χ₁ ≫ χ₂) g mx hmx mz hmz =
      baseChangeFiberMor χ₁ g mx hmx my hmy ≫ baseChangeFiberMor χ₂ g my hmy mz hmz := by
  simp [baseChangeFiberMor, pullbackFiberHom_comp]

/-- The inverse direction of `CategoryTheory.Functor.baseChangeFiberIso` is the base change of the
inverse direction of `e`, with the two named factorizations exchanged. -/
@[simp]
lemma baseChangeFiberIso_inv {Ux Uy V W : 𝒞} {x : p.Fiber Ux} {y : p.Fiber Uy}
    {fx : V ⟶ Ux} {fy : V ⟶ Uy} (e : pullbackFiber p x fx ≅ pullbackFiber p y fy) (g : W ⟶ V)
    (mx : W ⟶ Ux) (hmx : g ≫ fx = mx) (my : W ⟶ Uy) (hmy : g ≫ fy = my) :
    (baseChangeFiberIso e g mx hmx my hmy).inv = baseChangeFiberMor e.inv g my hmy mx hmx := by
  simp [baseChangeFiberIso, baseChangeFiberMor, pullbackFiberIso_inv]

omit [p.IsFibered] in
/-- Two base changes along the same morphism agree, whichever proofs witness the
factorizations. -/
lemma baseChangeFiberIso_congr {Ux Uy V W : 𝒞} {x : p.Fiber Ux} {y : p.Fiber Uy}
    {fx : V ⟶ Ux} {fy : V ⟶ Uy} [p.IsFibered]
    (e : pullbackFiber p x fx ≅ pullbackFiber p y fy) {g g' : W ⟶ V} (hgg : g = g')
    {mx : W ⟶ Ux} (hmx : g ≫ fx = mx) (hmx' : g' ≫ fx = mx)
    {my : W ⟶ Uy} (hmy : g ≫ fy = my) (hmy' : g' ≫ fy = my) :
    baseChangeFiberIso e g mx hmx my hmy = baseChangeFiberIso e g' mx hmx' my hmy' := by
  subst hgg
  rfl

/-- Base changing a contraction of an iterated chosen pullback is again such a contraction. -/
lemma baseChangeFiberMor_pullbackFiberCompIso' {T V' Z Z' : 𝒞} (z : p.Fiber T) (fa : V' ⟶ T)
    (ε : Z ⟶ V') (n : Z ⟶ T) (hn : ε ≫ fa = n) (γ : Z' ⟶ Z) (m : Z' ⟶ V') (hm : γ ≫ ε = m)
    (c : Z' ⟶ T) (hc : m ≫ fa = c) (hγn : γ ≫ n = c) :
    baseChangeFiberMor (pullbackFiberCompIso' z fa ε n hn).hom γ m hm c hγn =
      (pullbackFiberCompIso' z fa m c hc).hom := by
  rw [baseChangeFiberMor, pullbackFiberCompIso'_pentagon z fa ε γ n hn m hm c hc,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- The isomorphism form of `CategoryTheory.Functor.baseChangeFiberMor_pullbackFiberCompIso'`. -/
lemma baseChangeFiberIso_pullbackFiberCompIso' {T V' Z Z' : 𝒞} (z : p.Fiber T) (fa : V' ⟶ T)
    (ε : Z ⟶ V') (n : Z ⟶ T) (hn : ε ≫ fa = n) (γ : Z' ⟶ Z) (m : Z' ⟶ V') (hm : γ ≫ ε = m)
    (c : Z' ⟶ T) (hc : m ≫ fa = c) (hγn : γ ≫ n = c) :
    baseChangeFiberIso (pullbackFiberCompIso' z fa ε n hn) γ m hm c hγn =
      pullbackFiberCompIso' z fa m c hc :=
  Iso.ext (baseChangeFiberMor_pullbackFiberCompIso' z fa ε n hn γ m hm c hc hγn)

/-- Reading fibre morphisms between restrictions is compatible with composition. -/
lemma Restriction.fiberMor_comp {Ux Uy Uz V : 𝒞} {fx : V ⟶ Ux} {fy : V ⟶ Uy} {fz : V ⟶ Uz}
    {x y z : 𝒳} {hx : p.obj x = Ux} {hy : p.obj y = Uy} {hz : p.obj z = Uz}
    (xr : Restriction p fx x hx) (yr : Restriction p fy y hy) (zr : Restriction p fz z hz)
    {α : xr.pt ⟶ yr.pt} (hα : FibreHom p xr.pt yr.pt xr.hpt yr.hpt α)
    {β : yr.pt ⟶ zr.pt} (hβ : FibreHom p yr.pt zr.pt yr.hpt zr.hpt β)
    (hαβ : FibreHom p xr.pt zr.pt xr.hpt zr.hpt (α ≫ β)) :
    xr.fiberMor zr hαβ = xr.fiberMor yr hα ≫ yr.fiberMor zr hβ := by
  rw [Restriction.fiberMor, Restriction.fiberMor, Restriction.fiberMor, fibreHomMk_comp hα hβ hαβ]
  simp

omit [p.IsFibered] in
/-- Two readings of the same fibre morphism agree, whichever proof witnesses that it is one. -/
lemma Restriction.fiberMor_congr {Ux Uy V : 𝒞} {fx : V ⟶ Ux} {fy : V ⟶ Uy} {x y : 𝒳}
    {hx : p.obj x = Ux} {hy : p.obj y = Uy} [p.IsFibered]
    (xr : Restriction p fx x hx) (yr : Restriction p fy y hy)
    {φ φ' : xr.pt ⟶ yr.pt} (hφφ : φ = φ')
    (hφ : FibreHom p xr.pt yr.pt xr.hpt yr.hpt φ)
    (hφ' : FibreHom p xr.pt yr.pt xr.hpt yr.hpt φ') :
    xr.fiberMor yr hφ = xr.fiberMor yr hφ' := by
  subst hφφ
  rfl

omit [p.IsFibered] in
/-- Transport of `CategoryTheory.Functor.IsHomLift` to the `eqToHom`-decorated base morphism that
`CategoryTheory.Functor.Restriction` expects. -/
lemma isHomLift_eqToHom {R S : 𝒞} {a b : 𝒳} {n : R ⟶ S} {φ : a ⟶ b} (ha : p.obj a = R)
    (hb : p.obj b = S) (h : p.IsHomLift n φ) :
    p.IsHomLift (eqToHom ha ≫ n ≫ eqToHom hb.symm) φ := by
  subst ha hb
  simpa using h

omit [p.IsFibered] in
/-- Transport of `CategoryTheory.Functor.IsStronglyCartesian` to the `eqToHom`-decorated base
morphism that `CategoryTheory.Functor.Restriction` expects. -/
lemma isStronglyCartesian_eqToHom {R S : 𝒞} {a b : 𝒳} {n : R ⟶ S} {φ : a ⟶ b} (ha : p.obj a = R)
    (hb : p.obj b = S) (h : p.IsStronglyCartesian n φ) :
    p.IsStronglyCartesian (eqToHom ha ≫ n ≫ eqToHom hb.symm) φ := by
  subst ha hb
  simpa using h

omit [p.IsFibered] in
/-- A strongly cartesian morphism, read as a restriction of its target. -/
noncomputable def Restriction.ofCartesian {U V' : 𝒞} {fi : V' ⟶ U} {a x : 𝒳} (ha : p.obj a = V')
    (hx : p.obj x = U) (φ : a ⟶ x) (hφ : p.IsStronglyCartesian fi φ) :
    Restriction p fi x hx where
  pt := a
  hpt := ha
  hom := φ
  isHomLift := isHomLift_eqToHom ha hx (have := hφ; inferInstance)
  isCart := isStronglyCartesian_eqToHom ha hx hφ

/-- The base-change condition of `CategoryTheory.Functor.SieveDescentDatum` is base change of the
gluing isomorphism. -/
lemma baseChangeFiberMor_eq_iso_pullback {Ux Uy V W : 𝒞} {x : p.Fiber Ux} {y : p.Fiber Uy}
    {fx : V ⟶ Ux} {fy : V ⟶ Uy} (e : pullbackFiber p x fx ≅ pullbackFiber p y fy) (γ : W ⟶ V) :
    (pullbackFiberCompIso x fx γ).inv ≫ (pullbackFiberIso e γ).hom ≫
        (pullbackFiberCompIso y fy γ).hom =
      baseChangeFiberMor e.hom γ (γ ≫ fx) rfl (γ ≫ fy) rfl := rfl

/-- Base change of a morphism between chosen pullbacks, read through the contractions of the
iterated chosen pullbacks. -/
lemma pullbackFiberHom_eq_baseChange {Ux Uy V W : 𝒞} {x : p.Fiber Ux} {y : p.Fiber Uy}
    {fx : V ⟶ Ux} {fy : V ⟶ Uy} (ψ : pullbackFiber p x fx ⟶ pullbackFiber p y fy) (g : W ⟶ V)
    (mx : W ⟶ Ux) (hmx : g ≫ fx = mx) (my : W ⟶ Uy) (hmy : g ≫ fy = my) :
    pullbackFiberHom ψ g = (pullbackFiberCompIso' x fx g mx hmx).hom ≫
      baseChangeFiberMor ψ g mx hmx my hmy ≫ (pullbackFiberCompIso' y fy g my hmy).inv := by
  simp [baseChangeFiberMor]


end Functor

end CategoryTheory
