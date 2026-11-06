module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardFunctorAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Quot.SchemesOverCoveringFamily
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.TorsorTotalSpaceAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.LocallySurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.SeparatedQuasiFiniteDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.Unconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget

/-!
# Descending an algebraic space over `Y` along a flat surjection (for Stacks 0D2C)

Let `R` be an fppf sheaf on the test schemes over an algebraic space `Y`, and let `g : Y' ⟶ Y` be
a surjective, flat morphism locally of finite presentation.  The first paragraph of the proof of
Stacks 0D2C observes that if `Y' ×_Y R` is an algebraic space then so is `R`, by the bootstrap
theorem Stacks 04S6.  This file proves that statement,
`AlgebraicGeometry.Space.isAlgebraicSpaceOver_of_map`, for `R` read as a functor on the test
schemes (`AlgebraicGeometry.Space.IsAlgebraicSpaceOver`).  It carries no `@[stacks]` attribute: it
is a step of the proof of Stacks 0D2C, which is not proved here.

## The argument

* `AlgebraicGeometry.Space.overTotalPresheaf`: the total presheaf `U ↦ {(h, r) | h : U ⟶ Y,
  r ∈ R(U, h)}` of `R` on the big fppf site, which is the sheaf `R` of the source; it is an fppf
  sheaf when `R` is (`AlgebraicGeometry.Space.isSheaf_overTotalPresheaf`).
* `AlgebraicGeometry.Space.pointsModelEquiv`: conversely to
  `AlgebraicGeometry.Space.isAlgebraicSpaceOver_of_model`, an algebraic space `H` over `Y`
  identifies its sections with the total presheaf of its functor of points over `Y`.
* `AlgebraicGeometry.Space.exists_generate_singleton_mem_lift`: a point `U ⟶ Y` lifts to `Y'`
  after a single fppf covering `V ⟶ U` (the argument of Stacks 04S1).
* `AlgebraicGeometry.Space.small_overTotal_of_isAlgebraicSpaceOver_map`: the values of the total
  presheaf are `u`-small, being injected by restriction into sections of the algebraic space
  over `Y'`; so the total presheaf has a model `F` with values in `Type u`.
* The algebraic space `H'` over `Y'` maps to `F`, and `H' ⟶ F`, `H' ⟶ Y'` is a cartesian square
  over `F ⟶ Y`, `Y' ⟶ Y`; so `H' ⟶ F` is representable by algebraic spaces, surjective, flat and
  locally of finite presentation (Stacks 046F), and Stacks 04S6, condition (3)
  (`AlgebraicGeometry.Space.isBootstrapAlgebraicSpaceAlongFlatSurjection`) makes `F` an algebraic
  space.

## References

* [Stacks Project, Tag 0D2C](https://stacks.math.columbia.edu/tag/0D2C)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 04S1](https://stacks.math.columbia.edu/tag/04S1)
* [Stacks Project, Tag 046F](https://stacks.math.columbia.edu/tag/046F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe w u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Total

variable {Y : AlgebraicSpaces B S hS} (R : (SchemesOver Y)ᵒᵖ ⥤ Type (u + 1))

/-- Restricting along a morphism of test schemes whose underlying morphism is an identity does
not change a section, up to the identification of the two test schemes. -/
theorem heq_map_of_left_eq_id {U : BigFppfOver B S hS}
    {h₁ h₂ : (schemeSpaceFunctor B S hS).obj U ⟶ Y} (e : h₁ = h₂)
    (k : CostructuredArrow.mk h₁ ⟶ CostructuredArrow.mk h₂) (hk : k.left = 𝟙 U)
    (r : R.obj (op (CostructuredArrow.mk h₂))) :
    R.map k.op r ≍ r := by
  subst e
  obtain rfl : k = 𝟙 _ := CostructuredArrow.hom_ext _ _ hk
  simp

/-- Restricting a section along two morphisms of test schemes with the same underlying morphism
gives the same section, up to the identification of the two sources. -/
theorem heq_map_of_left_eq {U : BigFppfOver B S hS} {T : SchemesOver Y}
    {h₁ h₂ : (schemeSpaceFunctor B S hS).obj U ⟶ Y} (e : h₁ = h₂)
    (k₁ : CostructuredArrow.mk h₁ ⟶ T) (k₂ : CostructuredArrow.mk h₂ ⟶ T)
    (hk : k₁.left = k₂.left) (r : R.obj (op T)) :
    R.map k₁.op r ≍ R.map k₂.op r := by
  subst e
  obtain rfl : k₁ = k₂ := CostructuredArrow.hom_ext _ _ hk
  rfl

/-- Restricting a section along a morphism of test schemes, and along a composite with the same
underlying morphism, gives the same section up to the identification of the two sources. -/
theorem heq_map_map_of_left_eq {U : BigFppfOver B S hS} {T T' : SchemesOver Y}
    {h₁ h₂ : (schemeSpaceFunctor B S hS).obj U ⟶ Y} (e : h₁ = h₂)
    (k₁ : CostructuredArrow.mk h₁ ⟶ T) (k₂ : CostructuredArrow.mk h₂ ⟶ T') (k₃ : T' ⟶ T)
    (hk : k₁.left = k₂.left ≫ k₃.left) (r : R.obj (op T)) :
    R.map k₁.op r ≍ R.map k₂.op (R.map k₃.op r) := by
  subst e
  rw [← Functor.map_comp_apply, ← op_comp]
  obtain rfl : k₁ = k₂ ≫ k₃ := CostructuredArrow.hom_ext _ _ hk
  rfl

/-- Restriction of the total presheaf along an identity is the identity. -/
theorem overTotalMap_id (U : BigFppfOver B S hS) (a : OverTotal R U) :
    overTotalMap R (𝟙 U) a = a := by
  obtain ⟨h, r⟩ := a
  have e : (schemeSpaceFunctor B S hS).map (𝟙 U) ≫ h = h := by simp
  exact Sigma.ext e (heq_map_of_left_eq_id R e _ rfl r)

/-- Restriction of the total presheaf along a composite is the composite of the restrictions. -/
theorem overTotalMap_comp {U V W : BigFppfOver B S hS} (f : V ⟶ U) (g : W ⟶ V)
    (a : OverTotal R U) :
    overTotalMap R (g ≫ f) a = overTotalMap R g (overTotalMap R f a) := by
  obtain ⟨h, r⟩ := a
  have e : (schemeSpaceFunctor B S hS).map (g ≫ f) ≫ h =
      (schemeSpaceFunctor B S hS).map g ≫ (schemeSpaceFunctor B S hS).map f ≫ h := by simp
  exact Sigma.ext e (heq_map_map_of_left_eq R e _ _ _ rfl r)

/-- **The total presheaf of `R`** on the big fppf site: at a scheme `U`, the pairs `(h, r)` of a
morphism `h : U ⟶ Y` and a section `r` of `R` over the test scheme `(U, h)`. -/
def overTotalPresheaf : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1) where
  obj U := OverTotal R U.unop
  map g := ↾(overTotalMap R g.unop)
  map_id U := by
    apply ConcreteCategory.hom_ext
    intro a
    exact overTotalMap_id R U.unop a
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro a
    exact overTotalMap_comp R f.unop g.unop a

/-- The total presheaf acts by `AlgebraicGeometry.Space.overTotalMap`. -/
theorem overTotalPresheaf_map_apply {U V : BigFppfOver B S hS} (g : V ⟶ U) (a : OverTotal R U) :
    (overTotalPresheaf R).map g.op a = overTotalMap R g a :=
  rfl

/-- The section of `Y` that a morphism to `Y` restricted along `g` is, is the restriction of the
section that the morphism is. -/
theorem testPoint_mk_comp {U V : BigFppfOver B S hS} (g : V ⟶ U)
    (h : (schemeSpaceFunctor B S hS).obj U ⟶ Y) :
    testPoint (CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map g ≫ h)) =
      Y.1.map g.op (testPoint (CostructuredArrow.mk h)) :=
  (testPoint_naturality (CostructuredArrow.homMk
    (f := CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map g ≫ h))
    (f' := CostructuredArrow.mk h) g rfl)).symm

/-- An element of the total presheaf, read at its own test scheme, is its second component. -/
theorem overTotalToValue_self {U : BigFppfOver B S hS} (a : OverTotal R U) :
    overTotalToValue R (CostructuredArrow.mk a.1) a rfl = a.2 :=
  (congrArg (fun k ↦ R.map (Quiver.Hom.op k) a.2)
    (CostructuredArrow.hom_ext _ (𝟙 (CostructuredArrow.mk a.1)) rfl)).trans
    (Functor.map_id_apply R _ a.2)

/-- **The total presheaf of a sheaf on the test schemes over an algebraic space is a sheaf.** -/
theorem isSheaf_overTotalPresheaf (hR : Presheaf.IsSheaf (SchemesOver.topology Y) R) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) (overTotalPresheaf R) := by
  rw [isSheaf_iff_isSheaf_of_type]
  have hY := (isSheaf_iff_isSheaf_of_type _ _).1 Y.2.isSheaf
  have hR' := (isSheaf_iff_isSheaf_of_type _ _).1 hR
  intro U Sv hSv x hx
  -- The first components glue in `Y`.
  let y : Presieve.FamilyOfElements Y.1 Sv.arrows := fun _ f hf ↦
    testPoint (CostructuredArrow.mk (x f hf).1)
  have hy : y.Compatible := by
    intro V₁ V₂ W g₁ g₂ f₁ f₂ h₁ h₂ hg
    have := congrArg Sigma.fst (hx g₁ g₂ h₁ h₂ hg)
    change (schemeSpaceFunctor B S hS).map g₁ ≫ (x f₁ h₁).1 =
      (schemeSpaceFunctor B S hS).map g₂ ≫ (x f₂ h₂).1 at this
    show Y.1.map g₁.op (testPoint (CostructuredArrow.mk (x f₁ h₁).1)) =
      Y.1.map g₂.op (testPoint (CostructuredArrow.mk (x f₂ h₂).1))
    rw [← testPoint_mk_comp, ← testPoint_mk_comp, this]
  obtain ⟨yU, hyU, hyuniq⟩ := hY Sv hSv y hy
  let h : (schemeSpaceFunctor B S hS).obj U ⟶ Y := ObjectProperty.homMk (yonedaEquiv.symm yU)
  have htest : testPoint (CostructuredArrow.mk h) = yU := yonedaEquiv.apply_symm_apply yU
  have hfst : ∀ (V : BigFppfOver B S hS) (f : V ⟶ U) (hf : Sv f),
      (x f hf).1 = (schemeSpaceFunctor B S hS).map f ≫ h := fun V f hf ↦
    eq_hom_of_testPoint_mk_eq (T := CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map f ≫ h))
      _ (by rw [testPoint_mk_comp, htest]; exact (hyU f hf).symm)
  -- The second components glue in `R`, over the test scheme `(U, h)`.
  let T : SchemesOver Y := CostructuredArrow.mk h
  let S' : Sieve T := Sieve.functorPullback (X := T) (SchemesOver.proj Y) Sv
  have hS' : S' ∈ SchemesOver.topology Y T := by
    refine Functor.mem_restrictedTopology_of_functorPushforward_mem
      (GrothendieckTopology.superset_covering _ ?_ hSv)
    intro V f hf
    exact ⟨_, SchemesOver.liftHom T f, 𝟙 V, hf, (Category.id_comp _).symm⟩
  have hk : ∀ (T' : SchemesOver Y) (k : T' ⟶ T) (hk : S'.arrows k),
      (x k.left hk).1 = T'.hom := fun T' k hk ↦
    (hfst _ k.left hk).trans (CostructuredArrow.w k)
  have hbase : ∀ {T₀ T₁ : SchemesOver Y} (k : T₀ ⟶ T₁) (a : OverTotal R T₁.left),
      a.1 = T₁.hom → (overTotalMap R k.left a).1 = T₀.hom := fun k a ha ↦ by
    show (schemeSpaceFunctor B S hS).map k.left ≫ a.1 = _
    rw [ha]
    exact CostructuredArrow.w k
  let z : Presieve.FamilyOfElements R S'.arrows := fun T' k hk' ↦
    overTotalToValue R T' (x k.left hk') (hk T' k hk')
  have hz : z.Compatible := by
    intro T₁ T₂ T₀ g₁ g₂ k₁ k₂ h₁ h₂ hg
    show R.map g₁.op (overTotalToValue R T₁ (x k₁.left h₁) _) =
      R.map g₂.op (overTotalToValue R T₂ (x k₂.left h₂) _)
    have ha₁ := hbase g₁ _ (hk T₁ k₁ h₁)
    have ha₂ := hbase g₂ _ (hk T₂ k₂ h₂)
    exact (overTotalToValue_overTotalMap R g₁ (x k₁.left h₁) (hk T₁ k₁ h₁) ha₁).symm.trans
      ((overTotalToValue_congr R T₀ (hx g₁.left g₂.left h₁ h₂
        (congrArg CommaMorphism.left hg)) ha₁).trans
        (overTotalToValue_overTotalMap R g₂ (x k₂.left h₂) (hk T₂ k₂ h₂) ha₂))
  obtain ⟨r, hr, hruniq⟩ := hR' S' hS' z hz
  refine ⟨⟨h, r⟩, fun V f hf ↦ ?_, fun a ha ↦ ?_⟩
  · let T' : SchemesOver Y := CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map f ≫ h)
    let k : T' ⟶ T := SchemesOver.liftHom T f
    refine overTotalToValue_injective R T' (a := overTotalMap R f ⟨h, r⟩) rfl (hfst V f hf) ?_
    exact (overTotalToValue_overTotalMap R k ⟨h, r⟩ rfl rfl).trans
      ((congrArg (R.map k.op) (overTotalToValue_self R ⟨h, r⟩)).trans (hr k hf))
  · have h1 : a.1 = h := by
      refine eq_hom_of_testPoint_mk_eq (T := T) a.1 ((hyuniq _ fun V f hf ↦ ?_).trans htest.symm)
      show Y.1.map f.op (testPoint (CostructuredArrow.mk a.1)) =
        testPoint (CostructuredArrow.mk (x f hf).1)
      rw [← testPoint_mk_comp, ← ha f hf]
      rfl
    have h2 : overTotalToValue R T a h1 = r := by
      refine hruniq _ fun T' k hk' ↦ ?_
      have ha' := hbase k a h1
      exact (overTotalToValue_overTotalMap R k a h1 ha').symm.trans
        (overTotalToValue_congr R T' (ha k.left hk') ha')
    exact overTotalToValue_injective R T h1 rfl (h2.trans (overTotalToValue_self R ⟨h, r⟩).symm)

section Points

variable {H : AlgebraicSpaces B S hS} (p : H ⟶ Y)

/-- The morphism from a scheme to `Y` given by the image of a section of `H` under `p`. -/
def pointBase {U : BigFppfOver B S hS} (x : H.1.obj (op U)) :
    (schemeSpaceFunctor B S hS).obj U ⟶ Y :=
  ObjectProperty.homMk (yonedaEquiv.symm (p.hom.app (op U) x))

/-- The section of `Y` that `pointBase p x` is, is `p(x)`. -/
theorem testPoint_mk_pointBase {U : BigFppfOver B S hS} (x : H.1.obj (op U)) :
    testPoint (CostructuredArrow.mk (pointBase p x)) = p.hom.app (op U) x :=
  yonedaEquiv.apply_symm_apply _

/-- A section of `H` is a point of `H` over `Y` at the test scheme it determines. -/
def toPointsOver {U : BigFppfOver B S hS} (x : H.1.obj (op U)) :
    spacePointsOverObj p (CostructuredArrow.mk (pointBase p x)) :=
  ⟨x, (testPoint_mk_pointBase p x).symm⟩

/-- `pointBase` is natural in the scheme. -/
theorem pointBase_map {U V : BigFppfOver B S hS} (f : V ⟶ U) (x : H.1.obj (op U)) :
    pointBase p (H.1.map f.op x) = (schemeSpaceFunctor B S hS).map f ≫ pointBase p x :=
  eq_hom_of_testPoint_mk_eq (T := CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map f ≫
    pointBase p x)) _ (by
      rw [testPoint_mk_pointBase, testPoint_mk_comp, testPoint_mk_pointBase,
        NatTrans.naturality_apply])


/-- The inverse of a natural isomorphism of functors to types undoes it. -/
theorem iso_inv_app_hom_app_apply {C : Type*} [Category* C] {F G : C ⥤ Type w} (c : F ≅ G)
    (X : C) (z : F.obj X) : c.inv.app X (c.hom.app X z) = z := by
  simp

/-- A natural isomorphism of functors to types undoes its inverse. -/
theorem iso_hom_app_inv_app_apply {C : Type*} [Category* C] {F G : C ⥤ Type w} (c : F ≅ G)
    (X : C) (z : G.obj X) : c.hom.app X (c.inv.app X z) = z := by
  simp

variable {R} (c : spacePointsOver p ⋙ uliftFunctor.{u + 1, u} ≅ R)

/-- Two points of `H` over `Y` with the same underlying section, at test schemes with equal
structure morphisms, have the same image under `c`. -/
theorem heq_hom_app_of_eq {U : BigFppfOver B S hS}
    {h₁ h₂ : (schemeSpaceFunctor B S hS).obj U ⟶ Y}
    (e : h₁ = h₂) (y₁ : spacePointsOverObj p (CostructuredArrow.mk h₁))
    (y₂ : spacePointsOverObj p (CostructuredArrow.mk h₂)) (hy : y₁.1 = y₂.1) :
    c.hom.app (op (CostructuredArrow.mk h₁)) ⟨y₁⟩ ≍
      c.hom.app (op (CostructuredArrow.mk h₂)) ⟨y₂⟩ := by
  subst e
  obtain rfl : y₁ = y₂ := Subtype.ext hy
  rfl

/-- **An algebraic space over `Y` is a model of the total presheaf of its functor of points.**
For `R` isomorphic to the points of `p : H ⟶ Y` over `Y`, a section `x` of `H` over `U` gives the
pair `(p(x), x)` of a morphism `U ⟶ Y` and a section of `R` over it. -/
def pointsModelEquiv (U : BigFppfOver B S hS) : ULift.{u + 1} (H.1.obj (op U)) ≃ OverTotal R U where
  toFun x := ⟨pointBase p x.down,
    c.hom.app (op (CostructuredArrow.mk (pointBase p x.down))) ⟨toPointsOver p x.down⟩⟩
  invFun a := ⟨(c.inv.app (op (CostructuredArrow.mk a.1)) a.2).down.1⟩
  left_inv x := by
    obtain ⟨x⟩ := x
    exact congrArg (fun z : ULift.{u + 1}
        (spacePointsOverObj p (CostructuredArrow.mk (pointBase p x))) ↦ ULift.up z.down.1)
      (iso_inv_app_hom_app_apply c _ _)
  right_inv a := by
    obtain ⟨h, r⟩ := a
    have hz := (c.inv.app (op (CostructuredArrow.mk h)) r).down.2
    have e : pointBase p (c.inv.app (op (CostructuredArrow.mk h)) r).down.1 = h :=
      eq_hom_of_testPoint_mk_eq (T := CostructuredArrow.mk h) _
        ((testPoint_mk_pointBase p _).trans hz)
    refine Sigma.ext e ((heq_hom_app_of_eq p c e _ _ rfl).trans (heq_of_eq ?_))
    exact iso_hom_app_inv_app_apply c _ r

/-- Read at a test scheme `T`, the pair attached to a point `y` of `H` over `T` is `c(y)`. -/
theorem overTotalToValue_pointsModelEquiv (T : SchemesOver Y) (y : spacePointsOverObj p T)
    (hy : (pointsModelEquiv p c T.left ⟨y.1⟩).1 = T.hom) :
    overTotalToValue R T (pointsModelEquiv p c T.left ⟨y.1⟩) hy = c.hom.app (op T) ⟨y⟩ := by
  refine (NatTrans.naturality_apply c.hom _ _).symm.trans (congrArg _ ?_)
  exact ULift.ext (Subtype.ext (by
    show H.1.map (𝟙 (op T.left)) y.1 = y.1
    exact H.1.map_id_apply _ y.1))

/-- The model of the total presheaf is natural. -/
theorem pointsModelEquiv_naturality {U V : BigFppfOver B S hS} (f : V ⟶ U)
    (x : H.1.obj (op U)) :
    pointsModelEquiv p c V ⟨H.1.map f.op x⟩ = overTotalMap R f (pointsModelEquiv p c U ⟨x⟩) := by
  let T : SchemesOver Y :=
    CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map f ≫ pointBase p x)
  have hy : p.hom.app (op T.left) (H.1.map f.op x) = testPoint T := by
    rw [← testPoint_mk_pointBase, pointBase_map]
  let y : spacePointsOverObj p T := ⟨H.1.map f.op x, hy⟩
  have h1 : (pointsModelEquiv p c T.left ⟨y.1⟩).1 = T.hom := pointBase_map p f x
  have key := overTotalToValue_pointsModelEquiv p c T y h1
  let g : T ⟶ CostructuredArrow.mk (pointBase p x) := CostructuredArrow.homMk f rfl
  have key2 := overTotalToValue_overTotalMap R g (pointsModelEquiv p c U ⟨x⟩) rfl rfl
  have key3 := overTotalToValue_pointsModelEquiv p c _ (toPointsOver p x) rfl
  have key4 := NatTrans.naturality_apply c.hom g.op (⟨toPointsOver p x⟩ :
    ULift.{u + 1} (spacePointsOverObj p (CostructuredArrow.mk (pointBase p x))))
  have key5 : (spacePointsOver p ⋙ uliftFunctor.{u + 1, u}).map g.op ⟨toPointsOver p x⟩ = ⟨y⟩ :=
    ULift.ext (Subtype.ext rfl)
  apply overTotalToValue_injective R T h1 rfl
  exact key.trans ((congrArg (c.hom.app (op T)) key5.symm).trans
    (key4.trans ((congrArg (R.map g.op) key3.symm).trans key2.symm)))

end Points

end Total

/-! ### A surjective flat morphism locally of finite presentation has sections fppf locally -/

section Lift

variable {Y Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ Y)

/-- **A morphism of algebraic spaces which is surjective, flat and locally of finite
presentation has sections after a single fppf covering.**  For a scheme-valued point
`ξ : U ⟶ Y` there are a single morphism `j : V ⟶ U` of the site generating a covering sieve and a
point `ξ' : V ⟶ Y'` with `ξ ∘ j = g ∘ ξ'`: `V` is an étale atlas of `U ×_Y Y'`.  This is the
argument of Stacks 04S1 with the covering kept to one member. -/
theorem exists_generate_singleton_mem_lift (hflat : IsFlat B S hS g.hom)
    (hlfp : IsLocallyOfFinitePresentation B S hS g.hom) (hsurj : IsSurjective B S hS g.hom)
    (U : BigFppfOver B S hS) (ξ : yoneda.obj U ⟶ Y.1) :
    ∃ (V : BigFppfOver B S hS) (j : V ⟶ U) (ξ' : yoneda.obj V ⟶ Y'.1),
      Sieve.generate (Presieve.singleton j) ∈ BigFppfOver.topology B S hS U ∧
        yoneda.map j ≫ ξ = ξ' ≫ g.hom := by
  classical
  let J := BigFppfOver.topology B S hS
  let Tscheme := BigFppfOver.toScheme B S hS
  let a := g.hom
  have ha : IsRepresentableByAlgebraicSpaces B S hS a :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicSpace B S hS Y'.2 Y.2 a
  have hflatP : HasProperty B S hS (flatProperty B S hS) a ha :=
    hasProperty_of_space_hom' (flatProperty B S hS) Y'.2 Y.2 a hflat
  have hlfpP : HasProperty B S hS (locallyOfFinitePresentationProperty B S hS) a ha :=
    hasProperty_of_space_hom' (locallyOfFinitePresentationProperty B S hS) Y'.2 Y.2 a hlfp
  have hsurjP : HasProperty B S hS (surjectiveMorphismProperty B S hS) a ha :=
    hasProperty_of_space_hom' (surjectiveMorphismProperty B S hS) Y'.2 Y.2 a hsurj
  let p := pullback.fst ξ a
  have hP : IsAlgebraicSpace B S hS (pullback ξ a) := ha U ξ
  obtain ⟨V, φ, hφs, hφe⟩ := hP.exists_atlas
  have hidEtale : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) Tscheme).presheaf
      (𝟙 (yoneda.obj U)) :=
    presheaf_id_of_iso B S hS _ (fun _ _ f hf => by
      have := hf; change Etale (Tscheme.map f); infer_instance) U
  let j : V ⟶ U := yoneda.preimage (φ ≫ p)
  have hjmap : yoneda.map j = φ ≫ p := yoneda.map_preimage _
  have hchart : yoneda.map j ≫ 𝟙 (yoneda.obj U) = φ ≫ p := by rw [Category.comp_id, hjmap]
  have hjflat : Flat (Tscheme.map j) :=
    hflatP U ξ V U φ (𝟙 (yoneda.obj U)) j hφe hidEtale hchart
  have hjlfp : LocallyOfFinitePresentation (Tscheme.map j) :=
    hlfpP U ξ V U φ (𝟙 (yoneda.obj U)) j hφe hidEtale hchart
  have hjSurjPsh : (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) Tscheme).presheaf (yoneda.map j) := by
    refine (surjective_yonedaMap_iff_surjective_pointsMap B S hS j).mpr ?_
    rw [hjmap, pointsMap_comp]
    exact (hsurjP U ξ).comp
      ((surjective_iff_surjective_pointsMap B S hS _ hP V φ).mp hφs)
  have hjSurj : Surjective (Tscheme.map j) := by
    apply hjSurjPsh.2 (𝟙 _) (𝟙 _) j
    simpa using (IsPullback.of_id_fst (f := yoneda.map j))
  refine ⟨V, j, φ ≫ pullback.snd ξ a, ?_, ?_⟩
  · let E : PreZeroHypercover.{u + 1} (B.inclusion.obj U.left) :=
      PreZeroHypercover.singleton (B.inclusion.map ((BigFppfOver.forget B S hS).map j))
    have hE : E.presieve₀ ∈ Scheme.fppfPrecoverage (B.inclusion.obj U.left) := by
      have _ : Flat (B.inclusion.map ((BigFppfOver.forget B S hS).map j)) := hjflat
      have _ : Surjective (B.inclusion.map ((BigFppfOver.forget B S hS).map j)) := hjSurj
      have _ : LocallyOfFinitePresentation
        (B.inclusion.map ((BigFppfOver.forget B S hS).map j)) := hjlfp
      simpa [E, PreZeroHypercover.presieve₀_singleton] using
        (B.inclusion.map ((BigFppfOver.forget B S hS).map j)).singleton_mem_fppfPrecoverage
    obtain ⟨E', hE', ⟨ρ⟩⟩ := exists_isCovering_refining_fppfCovering B U.left E hE
    let R := Sieve.generate (Presieve.singleton j)
    have hRcov : (Sieve.overEquiv U).symm E'.sieve₀ ∈ J U := by
      rw [GrothendieckTopology.mem_over_iff]
      simpa [PreZeroHypercover.sieve₀, Sieve.ofArrows] using
        (Precoverage.generate_mem_toGrothendieck
          (show E'.presieve₀ ∈ B.precoverage U.left from ⟨E', rfl, hE'⟩))
    have hle : (Sieve.overEquiv U).symm E'.sieve₀ ≤ R := by
      rw [← ((Sieve.overEquiv U).symm).apply_symm_apply R,
        ((Sieve.overEquiv U).symm).map_rel_iff]
      simp only [OrderIso.symm_symm]
      rw [PreZeroHypercover.sieve₀, Sieve.ofArrows, Sieve.generate_le_iff,
        Presieve.ofArrows_le_iff]
      intro i
      rw [Sieve.overEquiv_iff]
      let α : Over.mk (E'.f i ≫ U.hom) ⟶ U := Over.homMk (E'.f i) (by simp)
      let b : (Over.mk (E'.f i ≫ U.hom)).left ⟶ (BigFppfOver.forget B S hS).obj V :=
        B.inclusion.preimage (ρ.h₀ i)
      have hbmap : B.inclusion.map b = ρ.h₀ i := B.inclusion.map_preimage _
      have href0 : ρ.h₀ i ≫ B.inclusion.map ((BigFppfOver.forget B S hS).map j) =
          B.inclusion.map (E'.f i) := by
        simpa [E, PreZeroHypercover.singleton] using ρ.w₀ i
      have hbp : b ≫ (BigFppfOver.forget B S hS).map j = E'.f i := by
        apply B.inclusion.map_injective
        rwa [B.inclusion.map_comp, hbmap]
      let β : Over.mk (E'.f i ≫ U.hom) ⟶ V := Over.homMk b (by
        calc
          b ≫ V.hom = b ≫ (j.left ≫ U.hom) := by rw [← Over.w j]
          _ = (b ≫ j.left) ≫ U.hom := by simp [Category.assoc]
          _ = E'.f i ≫ U.hom := by
            show (b ≫ (BigFppfOver.forget B S hS).map j) ≫ U.hom = _
            rw [hbp])
      show R α
      rw [← show β ≫ j = α from Over.OverMorphism.ext hbp]
      exact ⟨_, β, j, Presieve.singleton.mk, rfl⟩
    exact J.superset_covering hle hRcov
  · rw [hjmap, Category.assoc, pullback.condition, Category.assoc]

end Lift

/-! ### Smallness of the total presheaf -/

section Small

variable {Y : AlgebraicSpaces B S hS} (R : (SchemesOver Y)ᵒᵖ ⥤ Type (u + 1))

/-- **Restriction of a sheaf along a single fppf covering is injective.** If the underlying
morphism `k.left` of a morphism `k : T' ⟶ T` of test schemes generates a covering sieve of the
big fppf site, then the restriction of a sheaf on the test schemes along `k` is injective. -/
theorem injective_map_of_generate_singleton_mem
    (hR : Presheaf.IsSheaf (SchemesOver.topology Y) R) {T T' : SchemesOver Y} (k : T' ⟶ T)
    (hk : Sieve.generate (Presieve.singleton k.left) ∈ BigFppfOver.topology B S hS T.left) :
    Function.Injective (R.map k.op) := by
  have hR' := (isSheaf_iff_isSheaf_of_type _ _).1 hR
  have hcov : Sieve.generate (Presieve.singleton k) ∈ SchemesOver.topology Y T := by
    refine Functor.mem_restrictedTopology_of_functorPushforward_mem
      (GrothendieckTopology.superset_covering _ ?_ hk)
    rintro V f ⟨W, a, b, ⟨⟩, rfl⟩
    exact ⟨T', k, a, ⟨_, 𝟙 _, k, Presieve.singleton.mk, Category.id_comp _⟩, rfl⟩
  intro x y hxy
  refine ((hR' _ hcov).isSeparatedFor).ext fun V f hf ↦ ?_
  obtain ⟨W, a, b, ⟨⟩, rfl⟩ := hf
  rw [op_comp, Functor.map_comp_apply, Functor.map_comp_apply, hxy]

end Small

/-! ### Descending an algebraic space over `Y` along `Y' ⟶ Y` -/

section Descent

variable {Y Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ Y) {R : (SchemesOver Y)ᵒᵖ ⥤ Type (u + 1)}
  {H' : AlgebraicSpaces B S hS} (p' : H' ⟶ Y')
  (c : spacePointsOver p' ⋙ uliftFunctor.{u + 1, u} ≅ (CostructuredArrow.map g).op ⋙ R)

include c in
/-- If `R` read over `Y'` is an algebraic space over `Y'` and `Y' ⟶ Y` is surjective, flat and
locally of finite presentation, then the values of the sheaf `R` are `u`-small. -/
theorem small_obj_of_isAlgebraicSpaceOver_map (hflat : IsFlat B S hS g.hom)
    (hlfp : IsLocallyOfFinitePresentation B S hS g.hom) (hsurj : IsSurjective B S hS g.hom)
    (hR : Presheaf.IsSheaf (SchemesOver.topology Y) R) (T : SchemesOver Y) :
    Small.{u} (R.obj (op T)) := by
  obtain ⟨V, j, ξ', hcov, heq⟩ :=
    exists_generate_singleton_mem_lift g hflat hlfp hsurj T.left T.hom.hom
  let h' : (schemeSpaceFunctor B S hS).obj V ⟶ Y' := ObjectProperty.homMk ξ'
  let k : (CostructuredArrow.map g).obj (CostructuredArrow.mk h') ⟶ T :=
    CostructuredArrow.homMk j (InducedCategory.hom_ext heq)
  have hinj := injective_map_of_generate_singleton_mem R hR k hcov
  have : Small.{u} (R.obj (op ((CostructuredArrow.map g).obj (CostructuredArrow.mk h')))) :=
    small_of_injective (f := fun r ↦ (c.inv.app (op (CostructuredArrow.mk h')) r).down)
      fun a b hab ↦ by
        rw [← iso_hom_app_inv_app_apply c _ a, ← iso_hom_app_inv_app_apply c _ b]
        exact congrArg (c.hom.app _) (ULift.ext hab)
  exact small_of_injective hinj

include c in
/-- The values of the total presheaf of `R` are `u`-small. -/
theorem small_overTotal_of_isAlgebraicSpaceOver_map (hflat : IsFlat B S hS g.hom)
    (hlfp : IsLocallyOfFinitePresentation B S hS g.hom) (hsurj : IsSurjective B S hS g.hom)
    (hR : Presheaf.IsSheaf (SchemesOver.topology Y) R) (U : BigFppfOver B S hS) :
    Small.{u} (OverTotal R U) := by
  have hinj : Function.Injective (fun (h : (schemeSpaceFunctor B S hS).obj U ⟶ Y) ↦
      yonedaEquiv h.hom) := fun _ _ e ↦ InducedCategory.hom_ext (yonedaEquiv.injective e)
  have : Small.{u} ((schemeSpaceFunctor B S hS).obj U ⟶ Y) := small_of_injective hinj
  have := fun h : (schemeSpaceFunctor B S hS).obj U ⟶ Y ↦
    small_obj_of_isAlgebraicSpaceOver_map g p' c hflat hlfp hsurj hR (CostructuredArrow.mk h)
  infer_instance

/-- A pair `(h', r)` over `Y'` read as a pair `(g ∘ h', r)` over `Y`. -/
def overTotalBaseMap {U : BigFppfOver B S hS}
    (a : OverTotal ((CostructuredArrow.map g).op ⋙ R) U) : OverTotal R U :=
  ⟨a.1 ≫ g, a.2⟩

/-- Reading pairs over `Y'` as pairs over `Y` commutes with restriction. -/
theorem overTotalBaseMap_naturality {U V : BigFppfOver B S hS} (f : V ⟶ U)
    (a : OverTotal ((CostructuredArrow.map g).op ⋙ R) U) :
    overTotalBaseMap g (overTotalMap _ f a) = overTotalMap R f (overTotalBaseMap g a) := by
  obtain ⟨h', r⟩ := a
  exact Sigma.ext (Category.assoc _ _ _) (heq_map_of_left_eq R (Category.assoc _ _ _) _ _ rfl r)

include c in
/-- **Descent of an algebraic space over `Y` along `Y' ⟶ Y`** (the reduction step of the proof of
Stacks 0D2C, through Stacks 04S6).  Let `g : Y' ⟶ Y` be surjective, flat and locally of finite
presentation, and let `R` be an fppf sheaf on the test schemes over `Y`.  If `R`, read on the test
schemes over `Y'`, is an algebraic space over `Y'`, then `R` is an algebraic space over `Y`. -/
theorem isAlgebraicSpaceOver_of_map (hflat : IsFlat B S hS g.hom)
    (hlfp : IsLocallyOfFinitePresentation B S hS g.hom) (hsurj : IsSurjective B S hS g.hom)
    (hR : Presheaf.IsSheaf (SchemesOver.topology Y) R) : IsAlgebraicSpaceOver R := by
  have : FunctorToTypes.Small.{u} (overTotalPresheaf R) := fun U ↦
    small_overTotal_of_isAlgebraicSpaceOver_map g p' c hflat hlfp hsurj hR U.unop
  let F := FunctorToTypes.shrink.{u} (overTotalPresheaf R)
  let e : ∀ U, F.obj (op U) ≃ OverTotal R U := fun U ↦ (equivShrink _).symm
  have he : ∀ {U V : BigFppfOver B S hS} (f : V ⟶ U) (x : F.obj (op U)),
      e V (F.map f.op x) = overTotalMap R f (e U x) := fun f x ↦
    (Equiv.symm_apply_apply _ _).trans (overTotalPresheaf_map_apply R f _)
  -- `F` is an fppf sheaf, its universe lift being the total presheaf of `R`.
  have hFsheaf : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F := by
    have hP := isSheaf_overTotalPresheaf R hR
    let eP : F ⋙ uliftFunctor.{u + 1, u} ≅ overTotalPresheaf R :=
      NatIso.ofComponents (fun U ↦ (Equiv.ulift.trans (e U.unop)).toIso) fun {U V} f ↦ by
        ext ⟨x⟩
        exact he f.unop x
    rw [isSheaf_iff_isSheaf_of_type] at hP ⊢
    exact (Presieve.isSheaf_comp_uliftFunctor_iff _).1 (Presieve.isSheaf_iso _ eP.symm hP)
  -- The chart `H' ⟶ F` and the morphism `F ⟶ Y`.
  let q : F ⟶ Y.1 := modelToBase F e he
  let χ : H'.1 ⟶ F :=
    { app := fun U ↦ ↾fun x ↦ (e U.unop).symm
        (overTotalBaseMap g (pointsModelEquiv p' c U.unop ⟨x⟩))
      naturality := fun {U V} f ↦ by
        ext x
        apply (e V.unop).injective
        refine (Equiv.apply_symm_apply _ _).trans ?_
        refine (congrArg (overTotalBaseMap g) (pointsModelEquiv_naturality p' c f.unop x)).trans ?_
        refine (overTotalBaseMap_naturality g f.unop _).trans ?_
        exact (congrArg (overTotalMap R f.unop) (Equiv.apply_symm_apply _ _)).symm.trans
          (he f.unop _).symm }
  have hχ : ∀ (U : BigFppfOver B S hS) (x : H'.1.obj (op U)),
      e U (χ.app (op U) x) = overTotalBaseMap g (pointsModelEquiv p' c U ⟨x⟩) :=
    fun U x ↦ Equiv.apply_symm_apply _ _
  have htg : ∀ {U : BigFppfOver B S hS} (h' : (schemeSpaceFunctor B S hS).obj U ⟶ Y'),
      testPoint (CostructuredArrow.mk (h' ≫ g)) =
        g.hom.app (op U) (testPoint (CostructuredArrow.mk h')) :=
    fun h' ↦ yonedaEquiv_comp h'.hom g.hom
  -- The square `H' ⟶ F`, `H' ⟶ Y'` over `F ⟶ Y`, `Y' ⟶ Y` is cartesian.
  have hsq : IsPullback χ p'.hom q g.hom := by
    refine IsPullback.of_forall_isPullback_app fun U ↦ ?_
    obtain ⟨U⟩ := U
    rw [Types.isPullback_iff]
    refine ⟨?_, ?_, ?_⟩
    · ext x
      show testPoint (CostructuredArrow.mk (e U (χ.app (op U) x)).1) = g.hom.app (op U)
        (p'.hom.app (op U) x)
      rw [hχ, ← testPoint_mk_pointBase p' x]
      exact htg _
    · rintro x y ⟨h₁, h₂⟩
      have hb : pointBase p' x = pointBase p' y := by
        show ObjectProperty.homMk _ = ObjectProperty.homMk _
        rw [show p'.hom.app (op U) x = p'.hom.app (op U) y from h₂]
      have h₃ := congrArg (e U) h₁
      rw [hχ, hχ] at h₃
      have h₄ : pointsModelEquiv p' c U ⟨x⟩ = pointsModelEquiv p' c U ⟨y⟩ :=
        Sigma.ext hb (Sigma.ext_iff.1 h₃).2
      exact congrArg ULift.down ((pointsModelEquiv p' c U).injective h₄)
    · intro z y' hzy
      let a := e U z
      let h' : (schemeSpaceFunctor B S hS).obj U ⟶ Y' := ObjectProperty.homMk (yonedaEquiv.symm y')
      have htest' : testPoint (CostructuredArrow.mk h') = y' := yonedaEquiv.apply_symm_apply y'
      have hh : a.1 = h' ≫ g :=
        eq_hom_of_testPoint_mk_eq (T := CostructuredArrow.mk (h' ≫ g)) _ (by rwa [htg, htest'])
      let k : CostructuredArrow.mk (h' ≫ g) ⟶ CostructuredArrow.mk a.1 :=
        CostructuredArrow.homMk (𝟙 U) (by simp [hh])
      let b : OverTotal ((CostructuredArrow.map g).op ⋙ R) U := ⟨h', R.map k.op a.2⟩
      have hb : pointsModelEquiv p' c U ⟨((pointsModelEquiv p' c U).symm b).down⟩ = b :=
        Equiv.apply_symm_apply _ _
      refine ⟨((pointsModelEquiv p' c U).symm b).down, ?_, ?_⟩
      · apply (e U).injective
        refine (hχ U _).trans ?_
        rw [hb]
        exact Sigma.ext hh.symm (heq_map_of_left_eq_id R hh.symm k rfl a.2)
      · rw [← testPoint_mk_pointBase, show pointBase p' _ = h' from congrArg Sigma.fst hb, htest']
  -- Stacks 04S6: the chart is a base change of `g`, so `F` is an algebraic space.
  have hrep : IsRepresentableByAlgebraicSpaces B S hS χ :=
    isRepresentableByAlgebraicSpaces_of_isPullback B S hS p'.hom χ g.hom q hsq.flip
      (isRepresentableByAlgebraicSpaces_of_isAlgebraicSpace B S hS Y'.2 Y.2 g.hom)
  have hP : ∀ (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange],
      P (ObjectProperty.homMk g.hom : (⟨Y'.1, Y'.2⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y.1, Y.2⟩) →
        HasProperty B S hS P χ hrep := fun P _ hg ↦
    hasProperty_of_isPullback B S hS P p'.hom χ g.hom q hsq.flip _
      (hasProperty_of_space_hom' P Y'.2 Y.2 g.hom hg)
  have hFalg : IsAlgebraicSpace B S hS F :=
    isBootstrapAlgebraicSpaceAlongFlatSurjection B S hS χ hFsheaf H'.2 hrep
      (hP _ hsurj) (hP _ hflat) (hP _ hlfp)
  exact isAlgebraicSpaceOver_of_model e he hFalg

end Descent

end AlgebraicGeometry.Space

end
