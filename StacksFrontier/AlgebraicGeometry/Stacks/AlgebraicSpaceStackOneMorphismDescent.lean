module

public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackHomDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStack
public import StacksFrontier.CategoryTheory.Sites.Stackification.UniversalPropertyGroupoid

/-!
# 1-morphisms out of an algebraic space into a stack descend along étale coverings

Let `T` be an algebraic space over `S`, let `{e k : T k ⟶ T}` be an étale covering of algebraic
spaces, and let `𝒴` be an algebraic stack over `S`. Given 1-morphisms `F k : T k ⟶ 𝒴` together
with identifications of `F k` and `F l` at every point of `T` lifting to both `T k` and `T l`,
natural in the point and satisfying the cocycle condition, there is a 1-morphism `G : T ⟶ 𝒴`
restricting to every `F k` compatibly with the identifications.

The proof extends a 1-morphism along a stackification (**Stacks 0436**). The points of `T` which
lift globally to some member of the covering form a sub-presheaf `P` of `T`, the category of
elements of `P` maps to that of `T`, and this map is a stackification: it is fully faithful on
fibres, the fibres being discrete, and every point of `T` lifts to `P` locally, the covering
being étale. On the category of elements of `P` the 1-morphism is written down by choosing a
lift of each point, and its extension to `T` is `G`.

## Main results

* `AlgebraicGeometry.Stack.exists_hom_of_isEtaleCovering`: the gluing of 1-morphisms.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory

universe u v w

namespace AlgebraicGeometry.Stack

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The fibres of the category of elements of a presheaf are discrete.** -/
instance fibredCategory_fiber_hom_subsingleton (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    {V : BigFppfOver B S hS} (a b : (fibredCategory B S hS F).val.p.Fiber V) :
    Subsingleton (a ⟶ b) where
  allEq m₁ m₂ := by
    apply Functor.Fiber.hom_ext
    have := m₁.2
    have := m₂.2
    have h₁ := IsHomLift.fac' (fibredCategory B S hS F).val.p (𝟙 V) m₁.1
    have h₂ := IsHomLift.fac' (fibredCategory B S hS F).val.p (𝟙 V) m₂.1
    exact Pseudofunctor.CoGrothendieck.Hom.ext _ _ (h₁.trans h₂.symm) Discrete.hom_eq

section ImageSubfunctor

variable {T : AlgebraicSpaces B S hS} {K : Type v} {T' : K → AlgebraicSpaces B S hS}
  (e : ∀ k, T' k ⟶ T)

/-- **The points of `T` lifting globally to a member of a family.** -/
def imageSubfunctor : Subfunctor T.obj where
  obj V := {t | ∃ k a, (e k).hom.app V a = t}
  map {V W} f := by
    rintro t ⟨k, a, rfl⟩
    exact ⟨k, (T' k).obj.map f a, NatTrans.naturality_apply (e k).hom f a⟩

/-- The inclusion of the category of elements of the image into that of `T`. -/
abbrev imageInclusion :
    (fibredCategory B S hS (imageSubfunctor e).toFunctor).val.obj ⥤
      (fibredCategory B S hS T.obj).val.obj :=
  (associatedMap B S hS (imageSubfunctor e).ι).1.hom.toFunctor

/-- The inclusion of the image commutes with the projections to the base. -/
theorem imageInclusion_comp_eq :
    imageInclusion e ⋙ (fibredCategory B S hS T.obj).val.p =
      (fibredCategory B S hS (imageSubfunctor e).toFunctor).val.p :=
  (associatedMap B S hS (imageSubfunctor e).ι).1.hom.w

/-- A morphism of the category of elements of the image is determined by its base. -/
theorem image_hom_ext {o₁ o₂ : (fibredCategory B S hS (imageSubfunctor e).toFunctor).val.obj}
    {f g : o₁ ⟶ o₂} (h : f.base = g.base) : f = g :=
  Pseudofunctor.CoGrothendieck.Hom.ext _ _ h Discrete.hom_eq

/-- The inclusion of the category of elements of the image is faithful. -/
instance imageInclusion_faithful : (imageInclusion e).Faithful where
  map_injective {_ _} _ _ h := image_hom_ext e (congrArg (fun k => k.base) h)

/-- The inclusion of the category of elements of the image is full. -/
instance imageInclusion_full : (imageInclusion e).Full where
  map_surjective n :=
    ⟨⟨n.base, Discrete.eqToHom (Subtype.ext (Discrete.eq_of_hom n.fiber))⟩,
      Pseudofunctor.CoGrothendieck.Hom.ext _ _ rfl Discrete.hom_eq⟩

/-- **The inclusion of the image induces bijections of morphism presheaves**, which is
clause (1) of Stacks 02ZN for it: the fibres of both categories of elements are discrete, and
the inclusion is full. -/
theorem imageInclusion_hmor :
    haveI : (fibredCategory B S hS (imageSubfunctor e).toFunctor).val.p.IsFibered :=
      (fibredCategory B S hS (imageSubfunctor e).toFunctor).2.isFibered
    haveI : (fibredCategory B S hS T.obj).val.p.IsFibered :=
      (isStack_fibredCategory B S hS T.obj T.property).isFibered
    ∀ (U : BigFppfOver B S hS)
      (x y : (fibredCategory B S hS (imageSubfunctor e).toFunctor).val.p.Fiber U),
      Presheaf.IsLocallyInjective ((BigFppfOver.topology B S hS).over U)
          (((fibredCategory B S hS T.obj).2.isFibredOneMorphism
            (imageInclusion_comp_eq e)).morPresheafMap x y) ∧
        Presheaf.IsLocallySurjective ((BigFppfOver.topology B S hS).over U)
          (((fibredCategory B S hS T.obj).2.isFibredOneMorphism
            (imageInclusion_comp_eq e)).morPresheafMap x y) := by
  have : (fibredCategory B S hS (imageSubfunctor e).toFunctor).val.p.IsFibered :=
    (fibredCategory B S hS (imageSubfunctor e).toFunctor).2.isFibered
  have : (fibredCategory B S hS T.obj).val.p.IsFibered :=
    (isStack_fibredCategory B S hS T.obj T.property).isFibered
  intro U x y
  refine ⟨Presheaf.isLocallyInjective_of_injective _ _ fun g m₁ m₂ _ =>
      (fibredCategory_fiber_hom_subsingleton _ (Functor.pullbackFiber _ x g.unop.hom)
        (Functor.pullbackFiber _ y g.unop.hom)).elim m₁ m₂,
    Presheaf.isLocallySurjective_of_surjective _ _ fun g n => ?_⟩
  let hF := (fibredCategory B S hS T.obj).2.isFibredOneMorphism (imageInclusion_comp_eq e)
  let n' := (hF.mapPullbackFiberIso x g.unop.hom).inv ≫ n ≫
    (hF.mapPullbackFiberIso y g.unop.hom).hom
  obtain ⟨m₀, hm₀⟩ := (imageInclusion e).map_surjective n'.1
  have hl : (fibredCategory B S hS T.obj).val.p.IsHomLift (𝟙 g.unop.left)
      ((imageInclusion e).map m₀) := hm₀ ▸ n'.2
  have hl' := BasedFunctor.isHomLift_map (associatedMap B S hS (imageSubfunctor e).ι).1.hom
    (𝟙 g.unop.left) m₀
  exact ⟨⟨m₀, hl'⟩, (fibredCategory_fiber_hom_subsingleton _ _ _).elim _ _⟩

/-- **Every point of `T` lies locally in the image**, which is clause (2) of Stacks 02ZN for the
inclusion of the image: along a covering family of the base, which exists because the covering
of `T` is étale, the chosen pullbacks of an object of the category of elements of `T` are in the
essential image of the fibre functor. -/
theorem imageInclusion_hobj
    (he : Space.IsEtaleCovering B S hS (fun k => (T' k).obj) (fun k => (e k).hom)) :
    haveI : (fibredCategory B S hS T.obj).val.p.IsFibered :=
      (isStack_fibredCategory B S hS T.obj T.property).isFibered
    ∀ (U : BigFppfOver B S hS) (x' : (fibredCategory B S hS T.obj).val.p.Fiber U),
      ∃ R ∈ (BigFppfOver.topology B S hS) U, ∀ ⦃V : BigFppfOver B S hS⦄ ⦃f : V ⟶ U⦄,
        R.arrows f → (Functor.fiberFunctorOfCompEq (imageInclusion_comp_eq e) V).essImage
          (Functor.pullbackFiber _ x' f) := by
  have : (fibredCategory B S hS T.obj).val.p.IsFibered :=
    (isStack_fibredCategory B S hS T.obj T.property).isFibered
  rintro U ⟨⟨U₀, ⟨t⟩⟩, hU⟩
  change U₀ = U at hU
  subst hU
  obtain ⟨V, hV, y, hcov, hy⟩ := exists_cover_lift e he U₀ t
  refine ⟨Sieve.ofArrows V hV, hcov, ?_⟩
  rintro W f ⟨Y, h, _, ⟨k⟩, rfl⟩
  set c := Functor.pullbackFiber (fibredCategory B S hS T.obj).val.p
    (⟨⟨U₀, ⟨t⟩⟩, rfl⟩ : (fibredCategory B S hS T.obj).val.p.Fiber U₀) (h ≫ hV k)
  have hpt : (e k).hom.app _ ((T' k).obj.map h.op (y k)) = T.obj.map (h ≫ hV k).op t :=
    (NatTrans.naturality_apply (e k).hom h.op (y k)).trans
      ((congrArg (T.obj.map h.op) (hy k)).trans
        (Functor.map_comp_apply T.obj (hV k).op h.op t).symm)
  let a : (fibredCategory B S hS (imageSubfunctor e).toFunctor).val.p.Fiber W :=
    ⟨⟨W, ⟨⟨T.obj.map (h ≫ hV k).op t, ⟨k, (T' k).obj.map h.op (y k), hpt⟩⟩⟩⟩, rfl⟩
  let π := Functor.IsPreFibered.pullbackMap
    (rfl : (fibredCategory B S hS T.obj).val.p.obj ⟨U₀, ⟨t⟩⟩ = U₀) (h ≫ hV k)
  have hπc : (fibredCategory B S hS T.obj).val.p.IsCartesian (h ≫ hV k) π :=
    Functor.IsPreFibered.pullbackMap.IsCartesian _ _
  have hπl : (fibredCategory B S hS T.obj).val.p.IsHomLift (h ≫ hV k) π := hπc.toIsHomLift
  have hπ : π.base = eqToHom c.2 ≫ (h ≫ hV k) :=
    (IsHomLift.fac' (fibredCategory B S hS T.obj).val.p (h ≫ hV k) π).trans (by simp; rfl)
  have hs : c.1.fiber.as = T.obj.map (eqToHom c.2).op (T.obj.map (h ≫ hV k).op t) := by
    rw [← Functor.map_comp_apply, ← op_comp, ← hπ]
    exact point_eq_of_hom.{u, 0} (T := T) π
  let ψ : c ⟶ (Functor.fiberFunctorOfCompEq (imageInclusion_comp_eq e) W).obj a :=
    ⟨⟨eqToHom c.2, Discrete.eqToHom hs⟩, IsHomLift.of_fac' _ _ _ c.2 rfl (by simp; rfl)⟩
  have hg := (fibredCategory B S hS T.obj).2.fiber_isGroupoid W
  exact ⟨a, ⟨(asIso ψ).symm⟩⟩

end ImageSubfunctor

/-- **Pointwise gluing data for 1-morphisms out of the members of a family.** For every pair of
points of two members with the same image, a morphism between the values of the two
1-morphisms, natural in the points and satisfying the cocycle condition. -/
structure PointwiseGluing {𝒴 : AlgebraicStacks.{u, w} B S hS} {T : AlgebraicSpaces B S hS}
    {K : Type v} {T' : K → AlgebraicSpaces B S hS} (e : ∀ k, T' k ⟶ T)
    (F : ∀ k, (algebraicSpaceStackFunctor.{u, w} B S hS).obj (T' k) ⟶ 𝒴) where
  /-- The identification at a pair of points with the same image. -/
  φ : ∀ (k l : K) (V : BigFppfOver B S hS) (a : (T' k).obj.obj (Opposite.op V))
    (b : (T' l).obj.obj (Opposite.op V)), (e k).hom.app _ a = (e l).hom.app _ b →
      ((F k).hom.hom.obj (elt.{u, w} (T' k) V a) ⟶ (F l).hom.hom.obj (elt.{u, w} (T' l) V b))
  /-- The identification is a morphism of the fibre. -/
  isHomLift : ∀ k l V a b h, 𝒴.val.val.p.IsHomLift (𝟙 V) (φ k l V a b h)
  /-- The identification is natural in the points. -/
  naturality : ∀ (k l : K) {V W : BigFppfOver B S hS} {a : (T' k).obj.obj (Opposite.op V)}
    {a' : (T' k).obj.obj (Opposite.op W)} {b : (T' l).obj.obj (Opposite.op V)}
    {b' : (T' l).obj.obj (Opposite.op W)} (κa : elt.{u, w} (T' k) W a' ⟶ elt.{u, w} (T' k) V a)
    (κb : elt.{u, w} (T' l) W b' ⟶ elt.{u, w} (T' l) V b), κa.base = κb.base →
    ∀ h h', (F k).hom.hom.map κa ≫ φ k l V a b h = φ k l W a' b' h' ≫ (F l).hom.hom.map κb
  /-- The cocycle condition. -/
  cocycle : ∀ (k l m : K) (V : BigFppfOver B S hS) (a : (T' k).obj.obj (Opposite.op V))
    (b : (T' l).obj.obj (Opposite.op V)) (c : (T' m).obj.obj (Opposite.op V)) h₁ h₂,
    φ k l V a b h₁ ≫ φ l m V b c h₂ = φ k m V a c (h₁.trans h₂)

/-- Bookkeeping for the composition law of the glued 1-morphism, in a plain category. -/
theorem gluedMap_comp_aux {D : Type*} [Category D] {A B B₂ C C₂ C₃ C' : D} (x : A ⟶ B)
    (y : B ⟶ B₂) (z : B₂ ⟶ C₂) (w : C₂ ⟶ C₃) (x' : B ⟶ C) (y' : C ⟶ C₂) (c : A ⟶ C) (d : A ⟶ C')
    (τ : C ⟶ C') (v : C' ⟶ C₃) (i : A ⟶ A) (n₁ : y ≫ z = x' ≫ y') (hc : x ≫ x' = c)
    (n₂ : i ≫ d = c ≫ τ) (hi : i = 𝟙 A) (f₁ : τ ≫ v = y' ≫ w) :
    d ≫ v = (x ≫ y) ≫ (z ≫ w) := by
  subst hi
  rw [Category.id_comp] at n₂
  rw [n₂, Category.assoc, f₁, ← hc, Category.assoc, Category.assoc, ← reassoc_of% n₁]

namespace PointwiseGluing

variable {𝒴 : AlgebraicStacks.{u, w} B S hS} {T : AlgebraicSpaces B S hS}
  {K : Type v} {T' : K → AlgebraicSpaces B S hS} {e : ∀ k, T' k ⟶ T}
  {F : ∀ k, (algebraicSpaceStackFunctor.{u, w} B S hS).obj (T' k) ⟶ 𝒴}
  (D : PointwiseGluing e F)

/-- The identification of a point with itself is the identity. -/
theorem φ_self (k : K) (V : BigFppfOver B S hS) (a : (T' k).obj.obj (Opposite.op V)) :
    D.φ k k V a a rfl = 𝟙 _ := by
  have hp : 𝒴.val.val.p.IsFiberedInGroupoids := 𝒴.val.property
  have := D.isHomLift k k V a a rfl
  have : IsIso (D.φ k k V a a rfl) := hp.isIso_of_isHomLift_isIso (𝟙 V) _
  rw [← cancel_mono (D.φ k k V a a rfl), Category.id_comp, D.cocycle]

/-- The member of the family through which a point of the image sub-presheaf is chosen to
lift. -/
def liftIdx (o : (fibredCategory B S hS (imageSubfunctor e).toFunctor).val.obj) : K :=
  o.fiber.as.2.choose

/-- The chosen lift of a point of the image sub-presheaf. -/
def liftPt (o : (fibredCategory B S hS (imageSubfunctor e).toFunctor).val.obj) :
    (T' (liftIdx o)).obj.obj (Opposite.op o.base) :=
  o.fiber.as.2.choose_spec.choose

/-- The chosen lift of a point of the image sub-presheaf maps to that point. -/
theorem liftPt_spec (o : (fibredCategory B S hS (imageSubfunctor e).toFunctor).val.obj) :
    (e (liftIdx o)).hom.app _ (liftPt o) = o.fiber.as.1 :=
  o.fiber.as.2.choose_spec.choose_spec

/-- The point of the source of a morphism of the category of elements of the image is the
restriction of the point of its target. -/
theorem imagePoint_eq_of_hom
    {o₁ o₂ : (fibredCategory B S hS (imageSubfunctor e).toFunctor).val.obj} (g : o₁ ⟶ o₂) :
    o₁.fiber.as.1 = T.obj.map g.base.op o₂.fiber.as.1 :=
  congrArg Subtype.val (Discrete.eq_of_hom g.fiber)

/-- For a morphism `g : o₁ ⟶ o₂` of the category of elements of the image, the chosen lift of
`o₁` and the restriction along `g` of the chosen lift of `o₂` have the same image in `T`. -/
theorem liftPt_map_eq
    {o₁ o₂ : (fibredCategory B S hS (imageSubfunctor e).toFunctor).val.obj} (g : o₁ ⟶ o₂) :
    (e (liftIdx o₁)).hom.app _ (liftPt o₁) =
      (e (liftIdx o₂)).hom.app _ ((T' (liftIdx o₂)).obj.map g.base.op (liftPt o₂)) := by
  rw [liftPt_spec, imagePoint_eq_of_hom g, ← liftPt_spec o₂, NatTrans.naturality_apply]

/-- **The glued 1-morphism on the image, on objects**: the value of the 1-morphism of the chosen
member at the chosen lift. -/
def gluedObj (F : ∀ k, (algebraicSpaceStackFunctor.{u, w} B S hS).obj (T' k) ⟶ 𝒴)
    (o : (fibredCategory B S hS (imageSubfunctor e).toFunctor).val.obj) : 𝒴.val.val.obj :=
  (F (liftIdx o)).hom.hom.obj (elt.{u, w} (T' (liftIdx o)) o.base (liftPt o))

/-- **The glued 1-morphism on the image, on morphisms**: the identification between the chosen
lift of the source and the restriction of the chosen lift of the target, followed by the image of
the restriction morphism. -/
def gluedMap {o₁ o₂ : (fibredCategory B S hS (imageSubfunctor e).toFunctor).val.obj}
    (g : o₁ ⟶ o₂) : gluedObj F o₁ ⟶ gluedObj F o₂ :=
  D.φ _ _ o₁.base (liftPt o₁) ((T' (liftIdx o₂)).obj.map g.base.op (liftPt o₂))
      (liftPt_map_eq g) ≫
    (F (liftIdx o₂)).hom.hom.map (eltHom.{u, w} (T := T' (liftIdx o₂)) g.base rfl)

/-- The glued 1-morphism on the image preserves identities. -/
theorem gluedMap_id (o : (fibredCategory B S hS (imageSubfunctor e).toFunctor).val.obj) :
    D.gluedMap (𝟙 o) = 𝟙 _ := by
  have h := D.naturality (liftIdx o) (liftIdx o) (𝟙 (elt.{u, w} (T' (liftIdx o)) o.base (liftPt o)))
    (eltHom.{u, w} (T := T' (liftIdx o)) (𝟙 o.base) rfl) rfl rfl (liftPt_map_eq (𝟙 o))
  rw [D.φ_self] at h
  exact h.symm.trans ((congrArg (· ≫ 𝟙 _) ((F (liftIdx o)).hom.hom.map_id _)).trans
    (Category.id_comp _))

/-- The glued 1-morphism on the image preserves composition. -/
theorem gluedMap_comp {o₁ o₂ o₃ : (fibredCategory B S hS (imageSubfunctor e).toFunctor).val.obj}
    (g₁ : o₁ ⟶ o₂) (g₂ : o₂ ⟶ o₃) : D.gluedMap (g₁ ≫ g₂) = D.gluedMap g₁ ≫ D.gluedMap g₂ := by
  have h' : (e (liftIdx o₂)).hom.app _ ((T' (liftIdx o₂)).obj.map g₁.base.op (liftPt o₂)) =
      (e (liftIdx o₃)).hom.app _ ((T' (liftIdx o₃)).obj.map g₁.base.op
        ((T' (liftIdx o₃)).obj.map g₂.base.op (liftPt o₃))) := by
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, liftPt_map_eq g₂]
  have hpt : (T' (liftIdx o₃)).obj.map g₁.base.op
        ((T' (liftIdx o₃)).obj.map g₂.base.op (liftPt o₃)) =
      (T' (liftIdx o₃)).obj.map (𝟙 o₁.base).op
        ((T' (liftIdx o₃)).obj.map (g₁ ≫ g₂).base.op (liftPt o₃)) := by
    rw [op_id, Functor.map_id_apply]
    exact (Functor.map_comp_apply _ _ _ _).symm
  have n₁ := D.naturality (liftIdx o₂) (liftIdx o₃)
    (eltHom.{u, w} (T := T' (liftIdx o₂)) g₁.base rfl)
    (eltHom.{u, w} (T := T' (liftIdx o₃)) g₁.base rfl) rfl (liftPt_map_eq g₂) h'
  have hc := D.cocycle (liftIdx o₁) (liftIdx o₂) (liftIdx o₃) o₁.base (liftPt o₁) _ _
    (liftPt_map_eq g₁) h'
  have n₂ := D.naturality (liftIdx o₁) (liftIdx o₃)
    (𝟙 (elt.{u, w} (T' (liftIdx o₁)) o₁.base (liftPt o₁)))
    (eltHom.{u, w} (T := T' (liftIdx o₃)) (𝟙 o₁.base) hpt) rfl (liftPt_map_eq (g₁ ≫ g₂))
    ((liftPt_map_eq g₁).trans h')
  have f₁ : (F (liftIdx o₃)).hom.hom.map (eltHom.{u, w} (T := T' (liftIdx o₃)) (𝟙 o₁.base) hpt) ≫
      (F (liftIdx o₃)).hom.hom.map (eltHom.{u, w} (T := T' (liftIdx o₃)) (g₁ ≫ g₂).base rfl) =
      (F (liftIdx o₃)).hom.hom.map (eltHom.{u, w} (T := T' (liftIdx o₃)) g₁.base rfl) ≫
        (F (liftIdx o₃)).hom.hom.map (eltHom.{u, w} (T := T' (liftIdx o₃)) g₂.base rfl) :=
    ((F (liftIdx o₃)).hom.hom.map_comp _ _).symm.trans
    ((congrArg (F (liftIdx o₃)).hom.hom.map (elt_hom_ext (Category.id_comp _))).trans
      ((F (liftIdx o₃)).hom.hom.map_comp
        (eltHom.{u, w} (T := T' (liftIdx o₃)) g₁.base rfl)
        (eltHom.{u, w} (T := T' (liftIdx o₃)) g₂.base rfl)))
  exact gluedMap_comp_aux _ _ _ _ _ _ _ _ _ _ _ n₁ hc n₂ ((F (liftIdx o₁)).hom.hom.map_id _) f₁

/-- The glued morphism lies over the base morphism. -/
theorem isHomLift_gluedMap
    {o₁ o₂ : (fibredCategory B S hS (imageSubfunctor e).toFunctor).val.obj} (g : o₁ ⟶ o₂) :
    𝒴.val.val.p.IsHomLift g.base (D.gluedMap g) := by
  have h₁ := D.isHomLift _ _ o₁.base (liftPt o₁)
    ((T' (liftIdx o₂)).obj.map g.base.op (liftPt o₂)) (liftPt_map_eq g)
  have : ((algebraicSpaceStackFunctor.{u, w} B S hS).obj (T' (liftIdx o₂))).val.val.p.IsHomLift
      g.base (eltHom.{u, w} (T := T' (liftIdx o₂)) (t := liftPt o₂) g.base rfl) :=
    isHomLift_eltHom _ _
  have h₂ := BasedFunctor.preserves_isHomLift (F (liftIdx o₂)).hom.hom g.base
    (eltHom.{u, w} (T := T' (liftIdx o₂)) (t := liftPt o₂) g.base rfl)
  exact @IsHomLift.comp_lift_id_left _ _ _ _ _ _ _ _ _ _ g.base _ h₂ _ h₁

/-- **The glued 1-morphism on the image.** -/
def gluedFunctor :
    (fibredCategory B S hS (imageSubfunctor e).toFunctor).val.obj ⥤ 𝒴.val.val.obj where
  obj := gluedObj F
  map := D.gluedMap
  map_id := D.gluedMap_id
  map_comp := D.gluedMap_comp

/-- The glued 1-morphism on the image commutes with the projections to the base. -/
theorem gluedFunctor_comp_eq :
    D.gluedFunctor ⋙ 𝒴.val.val.p = (fibredCategory B S hS (imageSubfunctor e).toFunctor).val.p :=
  CategoryTheory.Functor.ext
    (fun (o : (fibredCategory B S hS (imageSubfunctor e).toFunctor).val.obj) =>
      BasedFunctor.w_obj (F (liftIdx o)).hom.hom _) (fun o₁ o₂ g => by
    have := D.isHomLift_gluedMap g
    exact IsHomLift.fac' _ g.base (D.gluedMap g))

end PointwiseGluing

section Main

variable {T : AlgebraicSpaces B S hS} {K : Type v} {T' : K → AlgebraicSpaces B S hS}
  {e : ∀ k, T' k ⟶ T}

/-- The point `e k (a)` of the image, as an object of its category of elements. -/
abbrev imageObj (e : ∀ k, T' k ⟶ T) (k : K) (V : BigFppfOver B S hS)
    (a : (T' k).obj.obj (Opposite.op V)) :
    (fibredCategory B S hS (imageSubfunctor e).toFunctor).val.obj :=
  ⟨V, ⟨⟨(e k).hom.app _ a, ⟨k, a, rfl⟩⟩⟩⟩

/-- Bookkeeping for the naturality of the comparison of the glued 1-morphism with a member. -/
theorem psi_nat_aux {D' : Type*} [Category D'] {X₁ X₂ Y₁ Y₂ Z₁ Z₂ W : D'} (h : X₁ ⟶ X₂)
    (u₁ : X₁ ⟶ Y₁) (u₂ : X₂ ⟶ Y₂) (gl : Y₁ ⟶ Y₂) (p₁ : Y₁ ⟶ W) (q₁ : W ⟶ Y₂) (φ₂ : Y₂ ⟶ Z₂)
    (φ₁ : Y₁ ⟶ Z₁) (m : Z₁ ⟶ Z₂) (s : W ⟶ Z₁)
    (hu : h ≫ u₂ = u₁ ≫ gl) (hgl : gl = p₁ ≫ q₁) (n : q₁ ≫ φ₂ = s ≫ m) (c : p₁ ≫ s = φ₁) :
    h ≫ (u₂ ≫ φ₂) = (u₁ ≫ φ₁) ≫ m := by
  rw [← Category.assoc, hu, hgl, ← c]
  simp only [Category.assoc, n]

/-- Bookkeeping for the compatibility of the comparisons of the glued 1-morphism. -/
theorem psi_compat_aux {D' : Type*} [Category D'] {Xa Xb Ya Yb Za Zb W : D'} (h : Xa ⟶ Xb)
    (ua : Xa ⟶ Ya) (ub : Xb ⟶ Yb) (gl : Ya ⟶ Yb) (p₁ : Ya ⟶ W) (q₁ : W ⟶ Yb) (φa : Ya ⟶ Za)
    (φab : Za ⟶ Zb) (φb : Yb ⟶ Zb) (s : W ⟶ Zb) (m : Zb ⟶ Zb) (φ' : Ya ⟶ Zb)
    (hu : h ≫ ub = ua ≫ gl) (hgl : gl = p₁ ≫ q₁) (n : q₁ ≫ φb = s ≫ m) (hm : m = 𝟙 Zb)
    (c₁ : φa ≫ φab = φ') (c₂ : p₁ ≫ s = φ') :
    (ua ≫ φa) ≫ φab = h ≫ (ub ≫ φb) := by
  subst hm hgl
  rw [Category.comp_id] at n
  rw [Category.assoc, c₁, ← Category.assoc, hu, Category.assoc, Category.assoc, n, c₂]

/-- **Descent of 1-morphisms along an étale covering.** Given an étale covering
`{e k : T' k ⟶ T}` of algebraic spaces and pointwise gluing data `D` for 1-morphisms
`F k : T' k ⟶ 𝒴` into an algebraic stack, there are a 1-morphism `G : T ⟶ 𝒴` and 2-morphisms
`ψ k : e k ≫ G ⟶ F k` compatible with the identifications `D.φ`. -/
theorem exists_hom_of_isEtaleCovering
    (he : Space.IsEtaleCovering B S hS (fun k => (T' k).obj) (fun k => (e k).hom))
    {𝒴 : AlgebraicStacks.{u, w} B S hS}
    {F : ∀ k, (algebraicSpaceStackFunctor.{u, w} B S hS).obj (T' k) ⟶ 𝒴}
    (D : PointwiseGluing e F) :
    ∃ (G : (algebraicSpaceStackFunctor.{u, w} B S hS).obj T ⟶ 𝒴)
      (ψ : ∀ k, (algebraicSpaceStackFunctor.{u, w} B S hS).map (e k) ≫ G ⟶ F k),
      ∀ (k l : K) (V : BigFppfOver B S hS) (a : (T' k).obj.obj (Opposite.op V))
        (b : (T' l).obj.obj (Opposite.op V)) (h : (e k).hom.app _ a = (e l).hom.app _ b),
        (ψ k).hom.hom.app (elt.{u, w} (T' k) V a) ≫ D.φ k l V a b h =
          G.hom.hom.map (eltHom.{u, w} (T := T) (𝟙 V) (eq_map_id h)) ≫
            (ψ l).hom.hom.app (elt.{u, w} (T' l) V b) := by
  obtain ⟨h𝒴, ⟨hst, -⟩, -⟩ := 𝒴.property
  let H := Functor.Stackification.extendGroupoid (fibredCategory B S hS _).2
    (fibredCategory B S hS T.obj).2 (isStack_fibredCategory B S hS T.obj T.property) 𝒴.val.2 hst
    (imageInclusion_comp_eq e) D.gluedFunctor_comp_eq (imageInclusion_hmor e)
    (imageInclusion_hobj e he)
  have hH : H ⋙ 𝒴.val.val.p = (fibredCategory B S hS T.obj).val.p :=
    Functor.Stackification.extendGroupoid_comp_eq _ _ _ _ _ _ _ _ _
  let un := Functor.Stackification.unitGroupoid (fibredCategory B S hS _).2
    (fibredCategory B S hS T.obj).2 (isStack_fibredCategory B S hS T.obj T.property) 𝒴.val.2 hst
    (imageInclusion_comp_eq e) D.gluedFunctor_comp_eq (imageInclusion_hmor e)
    (imageInclusion_hobj e he)
  let G : (algebraicSpaceStackFunctor.{u, w} B S hS).obj T ⟶ 𝒴 :=
    InducedBicategory.mkHom (InducedBicategory.mkHom ⟨H, hH⟩)
  have hpk : ∀ (k : K) (V : BigFppfOver B S hS) (a : (T' k).obj.obj (Opposite.op V)),
      (e (PointwiseGluing.liftIdx (imageObj e k V a))).hom.app _
        (PointwiseGluing.liftPt (imageObj e k V a)) = (e k).hom.app _ a :=
    fun k V a => PointwiseGluing.liftPt_spec _
  let ψapp : ∀ (k : K) (o : ((algebraicSpaceStackFunctor.{u, w} B S hS).obj (T' k)).val.val.obj),
      ((algebraicSpaceStackFunctor.{u, w} B S hS).map (e k) ≫ G).hom.hom.obj o ⟶
        (F k).hom.hom.obj o := fun k o =>
    un.hom.app (imageObj e k o.base o.fiber.as) ≫
      D.φ _ k o.base _ o.fiber.as (hpk k o.base o.fiber.as)
  have hψnat : ∀ (k : K)
      {o₁ o₂ : ((algebraicSpaceStackFunctor.{u, w} B S hS).obj (T' k)).val.val.obj}
      (κ : o₁ ⟶ o₂), ((algebraicSpaceStackFunctor.{u, w} B S hS).map (e k) ≫ G).hom.hom.map κ ≫
        ψapp k o₂ = ψapp k o₁ ≫ (F k).hom.hom.map κ := by
    intro k o₁ o₂ κ
    have hpe : (imageObj e k o₁.base o₁.fiber.as).fiber.as =
        (imageSubfunctor e).toFunctor.map κ.base.op
          (imageObj e k o₂.base o₂.fiber.as).fiber.as := by
      apply Subtype.ext
      show (e k).hom.app _ o₁.fiber.as = T.obj.map κ.base.op ((e k).hom.app _ o₂.fiber.as)
      rw [point_eq_of_hom.{u, w} (T := T' k) κ, NatTrans.naturality_apply]
    let κP : imageObj e k o₁.base o₁.fiber.as ⟶ imageObj e k o₂.base o₂.fiber.as :=
      ⟨κ.base, Discrete.eqToHom hpe⟩
    have hext : (imageInclusion e).map κP =
        ((algebraicSpaceStackFunctor.{u, w} B S hS).map (e k)).hom.hom.map κ :=
      elt_hom_ext.{u, w} rfl
    have hu := (congrArg (fun t => H.map t ≫ un.hom.app (imageObj e k o₂.base o₂.fiber.as))
      hext).symm.trans (un.hom.naturality κP)
    have h₁ := (PointwiseGluing.liftPt_map_eq κP).symm.trans (hpk k o₁.base o₁.fiber.as)
    have n := D.naturality _ k
      (eltHom.{u, w} (T := T' (PointwiseGluing.liftIdx (imageObj e k o₂.base o₂.fiber.as)))
        (t := PointwiseGluing.liftPt (imageObj e k o₂.base o₂.fiber.as)) κ.base rfl) κ rfl
      (hpk k o₂.base o₂.fiber.as) h₁
    have c := D.cocycle _ _ k o₁.base _ _ o₁.fiber.as
      (PointwiseGluing.liftPt_map_eq κP) h₁
    exact psi_nat_aux _ _ _ _ _ _ _ _ _ _ hu rfl n c
  let ψ : ∀ k, (algebraicSpaceStackFunctor.{u, w} B S hS).map (e k) ≫ G ⟶ F k := fun k =>
    ⟨⟨{ app := ψapp k
        naturality := fun _ _ κ => hψnat k κ
        isHomLift' := fun o => by
          have h₁ := Functor.Stackification.isHomLift_unitGroupoid_app
            (fibredCategory B S hS _).2 (fibredCategory B S hS T.obj).2
            (isStack_fibredCategory B S hS T.obj T.property) 𝒴.val.2 hst
            (imageInclusion_comp_eq e) D.gluedFunctor_comp_eq (imageInclusion_hmor e)
            (imageInclusion_hobj e he) (imageObj e k o.base o.fiber.as)
          have h₂ := D.isHomLift _ k o.base _ o.fiber.as (hpk k o.base o.fiber.as)
          exact @IsHomLift.comp_of_lift_id _ _ _ _ _ o.base _ _ _ _ _ h₁ h₂ }⟩⟩
  refine ⟨G, ψ, fun k l V a b h => ?_⟩
  have hpe : (imageObj e k V a).fiber.as =
      (imageSubfunctor e).toFunctor.map (𝟙 V).op (imageObj e l V b).fiber.as :=
    Subtype.ext (eq_map_id h)
  let κP : imageObj e k V a ⟶ imageObj e l V b := ⟨𝟙 V, Discrete.eqToHom hpe⟩
  have hext : (imageInclusion e).map κP = eltHom.{u, w} (T := T) (𝟙 V) (eq_map_id h) :=
    elt_hom_ext.{u, w} rfl
  have hu := (congrArg (fun t => H.map t ≫ un.hom.app (imageObj e l V b)) hext).symm.trans
    (un.hom.naturality κP)
  have h₁ := (PointwiseGluing.liftPt_map_eq (𝟙 (imageObj e l V b))).symm.trans (hpk l V b)
  have n := D.naturality _ l
    (eltHom.{u, w} (T := T' (PointwiseGluing.liftIdx (imageObj e l V b)))
      (t := PointwiseGluing.liftPt (imageObj e l V b)) (𝟙 V) rfl)
    (𝟙 (elt.{u, w} (T' l) V b)) rfl (hpk l V b) h₁
  have c₁ := D.cocycle _ k l V _ a b (hpk k V a) h
  have c₂ := D.cocycle _ _ l V _ _ b (PointwiseGluing.liftPt_map_eq κP) h₁
  exact psi_compat_aux _ _ _ _ _ _ _ _ _ _ _ _ hu rfl n ((F l).hom.hom.map_id _) c₁ c₂

end Main

end AlgebraicGeometry.Stack

end
