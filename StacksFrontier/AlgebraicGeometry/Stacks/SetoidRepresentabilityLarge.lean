module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Representable
public import StacksFrontier.AlgebraicGeometry.Stacks.Algebraic.MorphismRepresentableBySpaces.Criterion
public import StacksFrontier.AlgebraicGeometry.Stacks.PresheafRepresentability
public import StacksFrontier.AlgebraicGeometry.Stacks.SetoidRepresentability
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeFibre

/-!
# Representability through presheaves of isomorphism classes, with no smallness condition

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of categories fibred in setoids over the big fppf site of a
scheme `S`, and let `a : F ⟶ G` be the map it induces on the presheaves of isomorphism classes.
Stacks 04SY says that `a` is representable by algebraic spaces if and only if `f` is. Here the
total objects of `𝒳` and `𝒴` lie in an arbitrary universe `w`, so `F` and `G` take values in
`Type w`; representability of `a` is then
`AlgebraicGeometry.Space.IsRepresentableByAlgebraicSpacesULift`, the condition of Stacks 02YQ
tested against the universe-lifted scheme-valued points of `G`. No smallness of `F` or `G` is
assumed.

## Main definitions

* `CategoryTheory.OverShriek.fibreOfElement`: the fibre of a map of presheaves on `C/X` over an
  element of its target at `A → X`, as a presheaf on `C/A`, for presheaves with values in any
  universe.

## Main results

* `AlgebraicGeometry.Stack.isAlgebraicSpaceULift_pullback_iff`: the base change of a map of
  presheaves of `Type w` along a scheme-valued point is an algebraic space exactly when the fibre
  over the corresponding element is naturally in bijection with an algebraic space over the
  scheme.
* `AlgebraicGeometry.Stack.isoClassMap_isRepresentableByAlgebraicSpacesULift_iff`:
  **Stacks 04SY**.

## Implementation notes

The proof is pointwise in the scheme-valued points. At a point `ξ` of `G` over `U`, named by an
element `g`, the base change of `a` is an algebraic space exactly when the fibre of `a` over `g`,
a presheaf on the big fppf site of `U`, is one (after shrinking it to `Type u`, which it can be:
an algebraic space is pointwise small). On the side of `f`, Stacks 02ZY reduces representability
of `f` at an object `y` of `𝒴` over `U` to the presheaf of isomorphism classes of pairs
`(x, φ : h^* y ⟶ f x)` being an algebraic space over `U`; since the fibres of `𝒴` are setoids,
such a class is the same as the class of `x` in `F` lying over the restriction of the class of
`y`, which is the fibre of `a` over the class of `y`.

## References

* [Stacks Project, Tag 04SY](https://stacks.math.columbia.edu/tag/04SY)
* [Stacks Project, Tag 02ZY](https://stacks.math.columbia.edu/tag/02ZY)
-/

@[expose] public section

open CategoryTheory Opposite CategoryTheory.Limits

namespace CategoryTheory.OverShriek

universe v u w

variable {C : Type u} [Category.{v} C] {X A : C} (a : A ⟶ X) {F G : (Over X)ᵒᵖ ⥤ Type w}
  (α : F ⟶ G) (g : G.obj (op (Over.mk a)))

/-- **The fibre of `α : F ⟶ G` over an element `g` of `G` at `A → X`**, as a presheaf on the
slice `C/A`: a section over `W` is a section `s` of `F` over `(Over.map a).obj W` whose image
under `α` is the restriction of `g` along the tautological morphism of `W`. This is
`CategoryTheory.OverShriek.fibreOfSection` for presheaves with values in any universe, the
section being given by its element. -/
def fibreOfElement : (Over A)ᵒᵖ ⥤ Type w where
  obj W := {s : F.obj (op ((Over.map a).obj (unop W))) //
    α.app (op ((Over.map a).obj (unop W))) s = G.map (overMapTautHom a (unop W)).op g}
  map {W W'} h := ↾fun s => ⟨F.map ((Over.map a).map h.unop).op s.1, by
    rw [NatTrans.naturality_apply, s.2, ← Functor.map_comp_apply, ← op_comp,
      overMap_map_comp_overMapTautHom]⟩
  map_id W := by
    ext s
    have key : F.map ((Over.map a).map (𝟙 (unop W))).op s.1 = s.1 := by
      rw [(Over.map a).map_id, op_id]
      exact F.map_id_apply _ s.1
    exact key
  map_comp {W W' W''} h h' := by
    ext s
    have key : F.map ((Over.map a).map (h'.unop ≫ h.unop)).op s.1 =
        F.map ((Over.map a).map h'.unop).op (F.map ((Over.map a).map h.unop).op s.1) := by
      rw [(Over.map a).map_comp, op_comp]
      exact F.map_comp_apply _ _ s.1
    exact key

/-- Restriction in `CategoryTheory.OverShriek.fibreOfElement a α g` along `h` is restriction in
`F` along `(Over.map a).map h.unop`, on underlying sections. -/
@[simp] theorem fibreOfElement_map_val {W W' : (Over A)ᵒᵖ} (h : W ⟶ W')
    (s : (fibreOfElement a α g).obj W) :
    ((fibreOfElement a α g).map h s).1 = F.map ((Over.map a).map h.unop).op s.1 :=
  rfl

end CategoryTheory.OverShriek

namespace AlgebraicGeometry.Stack

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A natural family of bijections between two presheaves is an isomorphism of presheaves. -/
private noncomputable def isoOfNaturalEquiv {J : Type*} [Category* J] {P Q : J ⥤ Type w}
    (e : ∀ V, P.obj V ≃ Q.obj V)
    (he : ∀ ⦃V V'⦄ (h : V ⟶ V') (x : P.obj V), e V' (P.map h x) = Q.map h (e V x)) : P ≅ Q :=
  NatIso.ofComponents (fun V => (e V).toIso) fun h => by
    ext x
    exact he h x

/-- Restricting along `CategoryTheory.OverShriek.overMapMkIso` back and then forward is the
identity, for a presheaf with values in any universe. -/
private theorem map_overMapMkIso_hom_inv' {C : Type*} [Category* C] {X A : C} (a₀ : A ⟶ X)
    (H : (Over X)ᵒᵖ ⥤ Type w) {W : Over X} {ψ : W.left ⟶ A} (hψ : ψ ≫ a₀ = W.hom)
    (z : H.obj (op W)) :
    H.map (OverShriek.overMapMkIso a₀ hψ).hom.op (H.map (OverShriek.overMapMkIso a₀ hψ).inv.op z) =
      z := by
  rw [← Functor.map_comp_apply, ← op_comp, Iso.hom_inv_id, op_id,
    Functor.map_id_apply]

/-! ### The base change along a point and the fibre over its element -/

section Fibre

variable {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type w} (a : F ⟶ G) (U : BigFppfOver B S hS)
  (g : G.obj (op (Over.mk U.hom)))
  (ξ : uliftYoneda.{w}.obj (Over.mk U.hom) ⟶ G ⋙ uliftFunctor.{u})

/-- The point of the universe lift of `G` named by an element `g` of `G` over `U`. -/
def pointOfElement : uliftYoneda.{w}.obj (Over.mk U.hom) ⟶ G ⋙ uliftFunctor.{u} where
  app T := ↾fun t => ULift.up (G.map t.down.op g)
  naturality T T' h := by
    ext t
    obtain ⟨t⟩ := t
    change ULift.up (G.map (h.unop ≫ t).op g) = ULift.up (G.map h (G.map t.op g))
    rw [op_comp, Functor.map_comp_apply]
    rfl

/-- The base change of the universe lift of `a` along a scheme-valued point, as one square of
types at each object of the site. -/
private theorem isPullback_app (T : (BigFppfOver B S hS)ᵒᵖ) :
    IsPullback ((pullback.fst ξ (Functor.whiskerRight a uliftFunctor.{u})).app T)
      ((pullback.snd ξ (Functor.whiskerRight a uliftFunctor.{u})).app T) (ξ.app T)
      ((Functor.whiskerRight a uliftFunctor.{u}).app T) :=
  (IsPullback.of_hasPullback ξ (Functor.whiskerRight a uliftFunctor.{u})).map
    ((evaluation _ _).obj T)

variable (hξ : ∀ {T : BigFppfOver B S hS} (t : T ⟶ Over.mk U.hom),
  ξ.app (op T) (ULift.up t) = ULift.up (G.map t.op g))

include hξ in
/-- The two components of a section of the base change along `ξ` are compatible: `a` sends the
second to the restriction of `g` along the first. -/
private theorem app_snd_down_eq {T : (BigFppfOver B S hS)ᵒᵖ}
    (p : (pullback ξ (Functor.whiskerRight a uliftFunctor.{u})).obj T) :
    a.app T ((pullback.snd ξ (Functor.whiskerRight a uliftFunctor.{u})).app T p).down =
      G.map ((pullback.fst ξ (Functor.whiskerRight a uliftFunctor.{u})).app T p).down.op g := by
  have hc := (isPullback_app B S hS a U ξ T).w
  have hc' := congrArg ULift.down (ConcreteCategory.congr_hom hc p)
  have hξ' := congrArg ULift.down
    (hξ ((pullback.fst ξ (Functor.whiskerRight a uliftFunctor.{u})).app T p).down)
  exact hc'.symm.trans hξ'

/-- A section of the base change along `ξ` is determined by its two components. -/
private theorem pullback_ext {T : (BigFppfOver B S hS)ᵒᵖ}
    {p p' : (pullback ξ (Functor.whiskerRight a uliftFunctor.{u})).obj T}
    (h₁ : ((pullback.fst ξ (Functor.whiskerRight a uliftFunctor.{u})).app T p).down =
      ((pullback.fst ξ (Functor.whiskerRight a uliftFunctor.{u})).app T p').down)
    (h₂ : ((pullback.snd ξ (Functor.whiskerRight a uliftFunctor.{u})).app T p).down =
      ((pullback.snd ξ (Functor.whiskerRight a uliftFunctor.{u})).app T p').down) :
    p = p' := by
  have hp := isPullback_app B S hS a U ξ T
  rw [Limits.Types.isPullback_iff] at hp
  exact hp.2.1 p p' ⟨ULift.ext h₁, ULift.ext h₂⟩

include hξ in
/-- A compatible pair of components is a section of the base change along `ξ`. -/
private theorem exists_pullback_obj {T : (BigFppfOver B S hS)ᵒᵖ} (t : T.unop ⟶ Over.mk U.hom)
    (c : F.obj T) (hc : a.app T c = G.map t.op g) :
    ∃ p : (pullback ξ (Functor.whiskerRight a uliftFunctor.{u})).obj T,
      ((pullback.fst ξ (Functor.whiskerRight a uliftFunctor.{u})).app T p).down = t ∧
      ((pullback.snd ξ (Functor.whiskerRight a uliftFunctor.{u})).app T p).down = c := by
  obtain ⟨p, h₁, h₂⟩ := Types.exists_of_isPullback (isPullback_app B S hS a U ξ T)
    (ULift.up t) (ULift.up c) ((hξ t).trans (congrArg ULift.up hc.symm))
  exact ⟨p, congrArg ULift.down h₁, congrArg ULift.down h₂⟩

include hξ in
/-- **The base change along `ξ` is pointwise `u`-small as soon as the fibre over `g` is.** A
section over `T` is a morphism `t : T ⟶ U` together with a section of the fibre over the object
`t` of the site of `U`, transported along the canonical isomorphism of `T` with the image of
that object. -/
theorem small_pullback_of_small_fibreOfElement
    (hsmall : ∀ V, Small.{u} ((OverShriek.fibreOfElement U.hom a g).obj V)) :
    FunctorToTypes.Small.{u} (pullback ξ (Functor.whiskerRight a uliftFunctor.{u})) := by
  intro T
  let fst := (pullback.fst ξ (Functor.whiskerRight a uliftFunctor.{u})).app T
  let snd := (pullback.snd ξ (Functor.whiskerRight a uliftFunctor.{u})).app T
  let code : (pullback ξ (Functor.whiskerRight a uliftFunctor.{u})).obj T →
      Σ t : (T.unop ⟶ Over.mk U.hom),
        (OverShriek.fibreOfElement U.hom a g).obj (op (Over.mk t.left)) := fun p =>
    ⟨(fst p).down, ⟨F.map (OverShriek.overMapMkIso U.hom (Over.w (fst p).down)).inv.op
        (snd p).down, by
      rw [NatTrans.naturality_apply, app_snd_down_eq B S hS a U g ξ hξ p,
        ← Functor.map_comp_apply, ← op_comp]
      congr 2⟩⟩
  have hinj : Function.Injective code := by
    intro p p' h
    have h₁ : (fst p).down = (fst p').down := congrArg Sigma.fst h
    refine pullback_ext B S hS a U ξ h₁ ?_
    have key : ∀ q : Σ t : (T.unop ⟶ Over.mk U.hom),
        (OverShriek.fibreOfElement U.hom a g).obj (op (Over.mk t.left)),
        q = code p → F.map (OverShriek.overMapMkIso U.hom (Over.w q.1)).hom.op q.2.1 =
          (snd p).down := by
      rintro q rfl
      exact map_overMapMkIso_hom_inv' U.hom F (Over.w (fst p).down) _
    exact (key (code p') h.symm).symm.trans
      (map_overMapMkIso_hom_inv' U.hom F (Over.w (fst p').down) _)
  have : ∀ t : (T.unop ⟶ Over.mk U.hom),
      Small.{u} ((OverShriek.fibreOfElement U.hom a g).obj (op (Over.mk t.left))) :=
    fun _ => hsmall _
  exact small_of_injective hinj

variable [FunctorToTypes.Small.{u} (pullback ξ (Functor.whiskerRight a uliftFunctor.{u}))]

/-- The first projection of the base change along `ξ`, on its shrinking to `Type u`. -/
noncomputable def shrinkPullbackFst :
    FunctorToTypes.shrink.{u} (pullback ξ (Functor.whiskerRight a uliftFunctor.{u})) ⟶
      yoneda.obj (Over.mk U.hom) where
  app T := ↾fun q => ((pullback.fst ξ (Functor.whiskerRight a uliftFunctor.{u})).app T
    ((equivShrink _).symm q)).down
  naturality T T' h := by
    ext q
    change ((pullback.fst ξ (Functor.whiskerRight a uliftFunctor.{u})).app T'
        ((equivShrink _).symm ((equivShrink _)
          ((pullback ξ (Functor.whiskerRight a uliftFunctor.{u})).map h
            ((equivShrink _).symm q))))).down =
      h.unop ≫ ((pullback.fst ξ (Functor.whiskerRight a uliftFunctor.{u})).app T
        ((equivShrink _).symm q)).down
    rw [Equiv.symm_apply_apply, NatTrans.naturality_apply]
    rfl

include hξ in
/-- The second component of a section of the fibre of `shrinkPullbackFst` over the identity, as
a section of the fibre of `a` over `g`. -/
noncomputable def fibreOfSectionToFibreOfElement (V : (Over U.left)ᵒᵖ) :
    (OverShriek.fibreOfSection U.hom (shrinkPullbackFst B S hS a U ξ) (𝟙 _)).obj V →
      (OverShriek.fibreOfElement U.hom a g).obj V := fun q =>
  ⟨((pullback.snd ξ (Functor.whiskerRight a uliftFunctor.{u})).app _
      ((equivShrink _).symm q.1)).down, by
    have hq : ((pullback.fst ξ (Functor.whiskerRight a uliftFunctor.{u})).app _
        ((equivShrink _).symm q.1)).down = OverShriek.overMapTautHom U.hom V.unop := q.2
    rw [app_snd_down_eq B S hS a U g ξ hξ, hq]⟩

include hξ in
/-- `fibreOfSectionToFibreOfElement` is bijective. -/
theorem bijective_fibreOfSectionToFibreOfElement (V : (Over U.left)ᵒᵖ) :
    Function.Bijective (fibreOfSectionToFibreOfElement B S hS a U g ξ hξ V) := by
  constructor
  · intro q q' h
    have h₂ := congrArg Subtype.val h
    have hq : ((pullback.fst ξ (Functor.whiskerRight a uliftFunctor.{u})).app _
        ((equivShrink _).symm q.1)).down = OverShriek.overMapTautHom U.hom V.unop := q.2
    have hq' : ((pullback.fst ξ (Functor.whiskerRight a uliftFunctor.{u})).app _
        ((equivShrink _).symm q'.1)).down = OverShriek.overMapTautHom U.hom V.unop := q'.2
    exact Subtype.ext ((equivShrink _).symm.injective
      (pullback_ext B S hS a U ξ (hq.trans hq'.symm) h₂))
  · intro c
    obtain ⟨p, h₁, h₂⟩ := exists_pullback_obj B S hS a U g ξ hξ
      (OverShriek.overMapTautHom U.hom V.unop) c.1 c.2
    refine ⟨⟨equivShrink _ p, ?_⟩, Subtype.ext ?_⟩
    · change ((pullback.fst ξ (Functor.whiskerRight a uliftFunctor.{u})).app _
          ((equivShrink _).symm (equivShrink _ p))).down = _
      rw [Equiv.symm_apply_apply, h₁]
      rfl
    · change ((pullback.snd ξ (Functor.whiskerRight a uliftFunctor.{u})).app _
          ((equivShrink _).symm (equivShrink _ p))).down = c.1
      rw [Equiv.symm_apply_apply, h₂]

include hξ in
/-- `fibreOfSectionToFibreOfElement` is natural. -/
theorem fibreOfSectionToFibreOfElement_naturality ⦃V V' : (Over U.left)ᵒᵖ⦄ (h : V ⟶ V')
    (q : (OverShriek.fibreOfSection U.hom (shrinkPullbackFst B S hS a U ξ) (𝟙 _)).obj V) :
    fibreOfSectionToFibreOfElement B S hS a U g ξ hξ V'
        ((OverShriek.fibreOfSection U.hom (shrinkPullbackFst B S hS a U ξ) (𝟙 _)).map h q) =
      (OverShriek.fibreOfElement U.hom a g).map h
        (fibreOfSectionToFibreOfElement B S hS a U g ξ hξ V q) := by
  apply Subtype.ext
  change ((pullback.snd ξ (Functor.whiskerRight a uliftFunctor.{u})).app _
      ((equivShrink _).symm ((equivShrink _)
        ((pullback ξ (Functor.whiskerRight a uliftFunctor.{u})).map
          ((Over.map U.hom).map h.unop).op ((equivShrink _).symm q.1))))).down =
    F.map ((Over.map U.hom).map h.unop).op
      ((pullback.snd ξ (Functor.whiskerRight a uliftFunctor.{u})).app _
        ((equivShrink _).symm q.1)).down
  rw [Equiv.symm_apply_apply, NatTrans.naturality_apply]
  rfl

include hξ in
/-- The fibre of `shrinkPullbackFst` over the identity is the fibre of `a` over `g`. -/
noncomputable def fibreOfSectionEquivFibreOfElement (V : (Over U.left)ᵒᵖ) :
    (OverShriek.fibreOfSection U.hom (shrinkPullbackFst B S hS a U ξ) (𝟙 _)).obj V ≃
      (OverShriek.fibreOfElement U.hom a g).obj V :=
  Equiv.ofBijective _ (bijective_fibreOfSectionToFibreOfElement B S hS a U g ξ hξ V)

omit [FunctorToTypes.Small.{u} (pullback ξ (Functor.whiskerRight a uliftFunctor.{u}))] in
include hξ in
/-- **The base change along a scheme-valued point and the fibre over its element.** For a map
`a : F ⟶ G` of presheaves of `Type w` on the big fppf site of `S` and a point `ξ` of the universe
lift of `G` over `U` named by an element `g`, the base change of the universe lift of `a` along
`ξ` is an algebraic space over `S` exactly when the fibre of `a` over `g` is naturally in
bijection with an algebraic space over `U`. -/
theorem isAlgebraicSpaceULift_pullback_iff :
    Space.IsAlgebraicSpaceULift.{w} B S hS
        (pullback ξ (Functor.whiskerRight a uliftFunctor.{u})) ↔
      ∃ W : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u,
        IsAlgebraicSpace B U.left.1 U.left.2 W ∧
          ∃ e : ∀ V, (OverShriek.fibreOfElement U.hom a g).obj V ≃ W.obj V,
            ∀ ⦃V V'⦄ (h : V ⟶ V') (x : (OverShriek.fibreOfElement U.hom a g).obj V),
              e V' ((OverShriek.fibreOfElement U.hom a g).map h x) = W.map h (e V x) := by
  let Pb := pullback ξ (Functor.whiskerRight a uliftFunctor.{u})
  constructor
  · intro hPb
    have := Space.small_of_isAlgebraicSpaceULift B S hS hPb
    have hQ : IsAlgebraicSpace B S hS (FunctorToTypes.shrink.{u} Pb) :=
      (Space.isAlgebraicSpaceULift_comp_uliftFunctor_iff B S hS _).mp
        (Space.isAlgebraicSpaceULift_of_iso B S hS (Space.shrinkCompUliftFunctorIso Pb).symm hPb)
    let α := shrinkPullbackFst B S hS a U ξ
    have hsq : IsPullback α (𝟙 _) (𝟙 _) α := IsPullback.of_vert_isIso ⟨by simp⟩
    have hpb : IsAlgebraicSpace B S hS (pullback (𝟙 (yoneda.obj (Over.mk U.hom))) α) :=
      Space.isAlgebraicSpace_of_iso B S hS hsq.isoPullback hQ
    refine ⟨_, Space.isAlgebraicSpace_fibreOfSection B S hS U α (𝟙 _) hpb,
      fun V => (fibreOfSectionEquivFibreOfElement B S hS a U g ξ hξ V).symm, ?_⟩
    intro V V' h x
    apply (fibreOfSectionEquivFibreOfElement B S hS a U g ξ hξ V').injective
    rw [Equiv.apply_symm_apply]
    refine (congrArg _ (Equiv.apply_symm_apply
      (fibreOfSectionEquivFibreOfElement B S hS a U g ξ hξ V) x)).symm.trans ?_
    exact (fibreOfSectionToFibreOfElement_naturality B S hS a U g ξ hξ h _).symm
  · rintro ⟨W, hW, e, he⟩
    have := small_pullback_of_small_fibreOfElement B S hS a U g ξ hξ
      fun V => small_map (e V)
    let α := shrinkPullbackFst B S hS a U ξ
    let e' : ∀ V, (OverShriek.fibreOfSection U.hom α (𝟙 _)).obj V ≃ W.obj V := fun V =>
      (fibreOfSectionEquivFibreOfElement B S hS a U g ξ hξ V).trans (e V)
    have he' : ∀ ⦃V V'⦄ (h : V ⟶ V') (x : (OverShriek.fibreOfSection U.hom α (𝟙 _)).obj V),
        e' V' ((OverShriek.fibreOfSection U.hom α (𝟙 _)).map h x) = W.map h (e' V x) := by
      intro V V' h x
      change e V' (fibreOfSectionToFibreOfElement B S hS a U g ξ hξ V' _) = _
      rw [fibreOfSectionToFibreOfElement_naturality B S hS a U g ξ hξ h x, he]
      rfl
    have hfib : IsAlgebraicSpace B U.left.1 U.left.2
        (OverShriek.fibreOfSection U.hom α (𝟙 _)) :=
      Space.isAlgebraicSpace_of_iso B U.left.1 U.left.2 (isoOfNaturalEquiv e' he').symm hW
    have hpb : IsAlgebraicSpace B S hS (pullback (𝟙 (yoneda.obj (Over.mk U.hom))) α) :=
      Space.isAlgebraicSpace_of_iso B S hS
        (OverShriek.isPullback_relocalizeFibreOfSectionMap U.hom α (𝟙 _)).flip.isoPullback
        (Space.isAlgebraicSpace_relocalizePresheaf B S hS U _ hfib)
    have hsq : IsPullback α (𝟙 _) (𝟙 _) α := IsPullback.of_vert_isIso ⟨by simp⟩
    have hQ : IsAlgebraicSpace B S hS (FunctorToTypes.shrink.{u} Pb) :=
      Space.isAlgebraicSpace_of_iso B S hS hsq.isoPullback.symm hpb
    exact Space.isAlgebraicSpaceULift_of_iso B S hS (Space.shrinkCompUliftFunctorIso Pb)
      ((Space.isAlgebraicSpaceULift_comp_uliftFunctor_iff B S hS _).mpr hQ)

end Fibre

/-! ### Classes of pairs and classes of objects -/

section Pairs

variable {𝒳 𝒴 : CatFiberedInSetoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
  (a : 𝒳.val.p.isoClassPresheaf ⟶ 𝒴.val.p.isoClassPresheaf)
  (ha : ∀ (U : BigFppfOver B S hS) (x : 𝒳.val.p.Fiber U),
    a.app (op U) (Functor.isoClassMk 𝒳.val.p x) =
      Functor.isoClassMk 𝒴.val.p
        ((Functor.Fiber.mapOfComp 𝒳.val.p 𝒴.val.p
          (CatFiberedInGroupoids.homFunctor f)
          (CatFiberedInGroupoids.homFunctor_comp_p f) U).obj x))
  (U : BigFppfOver B S hS) (y : 𝒴.val.p.Fiber U)

/-- The presheaf on the big fppf site of `U` of isomorphism classes of pairs
`(x, φ : h^* y ⟶ f x)` of Stacks 02ZY, for the canonical choice of pullbacks of `𝒴`. -/
noncomputable abbrev pairPresheaf :
    (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type (max (u + 1) v w) :=
  U.iteratedSliceBackward.op ⋙
    PairIsoClass.presheaf (CatFiberedInGroupoids.homFunctor (CatFiberedInSetoids.inclusion.map f))
      (Functor.chosenPullbacks 𝒴.val.p) y (CatFiberedInSetoids.inclusion.obj 𝒳).2
      (CatFiberedInSetoids.inclusion.obj 𝒴).2
      (CatFiberedInGroupoids.homFunctor_comp_p (CatFiberedInSetoids.inclusion.map f))

include ha in
/-- The class of an object `x` of `𝒳` over `V` lies over the restriction of the class of `y`
as soon as there is a vertical morphism from the pullback of `y` to `f x`. -/
theorem app_isoClassMk_eq_of_hom (V : (Over U.left)ᵒᵖ)
    (x : 𝒳.val.p.Fiber ((Over.map U.hom).obj V.unop))
    (φ : (Functor.pullbackFiber 𝒴.val.p y (OverShriek.overMapTautHom U.hom V.unop)).1 ⟶
      (CatFiberedInGroupoids.homFunctor f).obj x.1)
    (hφ : 𝒴.val.p.IsHomLift (𝟙 ((Over.map U.hom).obj V.unop)) φ) :
    a.app (op ((Over.map U.hom).obj V.unop)) (Functor.isoClassMk 𝒳.val.p x) =
      𝒴.val.p.isoClassPresheaf.map (OverShriek.overMapTautHom U.hom V.unop).op
        (Functor.isoClassMk 𝒴.val.p y) := by
  rw [ha, Functor.isoClassPresheaf_map_isoClassMk]
  let ψ : Functor.pullbackFiber 𝒴.val.p y (OverShriek.overMapTautHom U.hom V.unop) ⟶
      (Functor.Fiber.mapOfComp 𝒳.val.p 𝒴.val.p (CatFiberedInGroupoids.homFunctor f)
        (CatFiberedInGroupoids.homFunctor_comp_p f) _).obj x := ⟨φ, hφ⟩
  have : IsIso ψ := (Functor.IsFiberedInSetoids.fiber_isGroupoid 𝒴.val.p _).all_isIso ψ
  exact (Functor.isoClassMk_eq_of_iso (asIso ψ)).symm

/-- The class of a pair `(x, φ)` goes to the class of `x`, which lies in the fibre of `a` over
the class of `y`. -/
noncomputable def pairToFibre (V : (Over U.left)ᵒᵖ) :
    (pairPresheaf B S hS f U y).obj V →
      (OverShriek.fibreOfElement U.hom a (Functor.isoClassMk 𝒴.val.p y)).obj V :=
  Quotient.lift
    (fun A => ⟨Functor.isoClassMk 𝒳.val.p (PairIsoClass.objEquiv
      (CatFiberedInGroupoids.homFunctor (CatFiberedInSetoids.inclusion.map f))
      (Functor.chosenPullbacks 𝒴.val.p) y (CatFiberedInSetoids.inclusion.obj 𝒴).2
      (U.iteratedSliceBackward.obj V.unop) A).1,
      app_isoClassMk_eq_of_hom B S hS f a ha U y V _ _ (PairIsoClass.objEquiv
        (CatFiberedInGroupoids.homFunctor (CatFiberedInSetoids.inclusion.map f))
        (Functor.chosenPullbacks 𝒴.val.p) y (CatFiberedInSetoids.inclusion.obj 𝒴).2
        (U.iteratedSliceBackward.obj V.unop) A).2.2⟩)
    (by
      intro A A' hAA'
      obtain ⟨ι⟩ := (Functor.isIsomorphicSetoid_r_iff _ _).1 hAA'
      have u := TwoFibreProductOver.FstFiber.homEquiv A A' ι.hom
      have u' := TwoFibreProductOver.FstFiber.homEquiv A' A ι.inv
      apply Subtype.ext
      apply Functor.isoClassMk_eq_of_iso
      exact
        { hom := ⟨u.1, u.2.1⟩
          inv := ⟨u'.1, u'.2.1⟩
          hom_inv_id := @Subsingleton.elim _
            ((Functor.IsFiberedInSetoids.fiber_isThin (p := 𝒳.val.p) _) _ _) _ _
          inv_hom_id := @Subsingleton.elim _
            ((Functor.IsFiberedInSetoids.fiber_isThin (p := 𝒳.val.p) _) _ _) _ _ })

/-- `pairToFibre` sends the class of a pair `(x, φ)` to the class of `x`. -/
theorem pairToFibre_mk_val (V : (Over U.left)ᵒᵖ)
    (x : 𝒳.val.p.Fiber (U.iteratedSliceBackward.obj V.unop).left)
    (φ : ((Functor.chosenPullbacks 𝒴.val.p).obj (U.iteratedSliceBackward.obj V.unop).hom y).1 ⟶
      (CatFiberedInGroupoids.homFunctor (CatFiberedInSetoids.inclusion.map f)).obj x.1)
    (hφ : 𝒴.val.p.IsHomLift (𝟙 (U.iteratedSliceBackward.obj V.unop).left) φ) :
    (pairToFibre B S hS f a ha U y V (PairIsoClass.mk
      (CatFiberedInGroupoids.homFunctor (CatFiberedInSetoids.inclusion.map f))
      (Functor.chosenPullbacks 𝒴.val.p) y
      (CatFiberedInSetoids.inclusion.obj 𝒳).2 (CatFiberedInSetoids.inclusion.obj 𝒴).2
      (CatFiberedInGroupoids.homFunctor_comp_p (CatFiberedInSetoids.inclusion.map f))
      (f := U.iteratedSliceBackward.obj V.unop) x φ hφ)).1 = Functor.isoClassMk 𝒳.val.p x := by
  have key := Equiv.apply_symm_apply
    (PairIsoClass.objEquiv
      (CatFiberedInGroupoids.homFunctor (CatFiberedInSetoids.inclusion.map f))
      (Functor.chosenPullbacks 𝒴.val.p) y (CatFiberedInSetoids.inclusion.obj 𝒴).2
      (U.iteratedSliceBackward.obj V.unop)) ⟨x, φ, hφ⟩
  change (pairToFibre B S hS f a ha U y V (Quotient.mk _ _)).1 = _
  exact congrArg (fun z => Functor.isoClassMk 𝒳.val.p z.1) key


include ha in
/-- `pairToFibre` is bijective: since the fibres of `𝒴` are setoids, a pair `(x, φ)` is
determined up to isomorphism by the class of `x`, and a class of `x` over the restriction of the
class of `y` admits some `φ`. -/
theorem bijective_pairToFibre (V : (Over U.left)ᵒᵖ) :
    Function.Bijective (pairToFibre B S hS f a ha U y V) := by
  constructor
  · intro t t' h
    obtain ⟨x, φ, hφ, rfl⟩ := PairIsoClass.mk_surjective
        (CatFiberedInGroupoids.homFunctor (CatFiberedInSetoids.inclusion.map f))
      (Functor.chosenPullbacks 𝒴.val.p) y (CatFiberedInSetoids.inclusion.obj 𝒳).2
      (CatFiberedInSetoids.inclusion.obj 𝒴).2
      (CatFiberedInGroupoids.homFunctor_comp_p (CatFiberedInSetoids.inclusion.map f))
      (f := U.iteratedSliceBackward.obj V.unop) t
    obtain ⟨x', φ', hφ', rfl⟩ := PairIsoClass.mk_surjective
        (CatFiberedInGroupoids.homFunctor (CatFiberedInSetoids.inclusion.map f))
      (Functor.chosenPullbacks 𝒴.val.p) y (CatFiberedInSetoids.inclusion.obj 𝒳).2
      (CatFiberedInSetoids.inclusion.obj 𝒴).2
      (CatFiberedInGroupoids.homFunctor_comp_p (CatFiberedInSetoids.inclusion.map f))
      (f := U.iteratedSliceBackward.obj V.unop) t'
    have hx : Functor.isoClassMk 𝒳.val.p x = Functor.isoClassMk 𝒳.val.p x' :=
      (pairToFibre_mk_val B S hS f a ha U y V x φ hφ).symm.trans
        ((congrArg Subtype.val h).trans (pairToFibre_mk_val B S hS f a ha U y V x' φ' hφ'))
    obtain ⟨ψ⟩ := Functor.exists_iso_of_isoClassMk_eq hx
    refine (PairIsoClass.mk_eq_mk_iff
        (CatFiberedInGroupoids.homFunctor (CatFiberedInSetoids.inclusion.map f))
      (Functor.chosenPullbacks 𝒴.val.p) y (CatFiberedInSetoids.inclusion.obj 𝒳).2
      (CatFiberedInSetoids.inclusion.obj 𝒴).2
      (CatFiberedInGroupoids.homFunctor_comp_p (CatFiberedInSetoids.inclusion.map f))
      (f := U.iteratedSliceBackward.obj V.unop) x x' φ hφ φ' hφ').mpr ⟨ψ, ?_⟩
    have := hφ
    have : 𝒳.val.p.IsHomLift (𝟙 (U.iteratedSliceBackward.obj V.unop).left)
        (Functor.Fiber.fiberInclusion.map ψ.hom) := ψ.hom.2
    have hψ : 𝒴.val.p.IsHomLift (𝟙 (U.iteratedSliceBackward.obj V.unop).left)
        ((CatFiberedInGroupoids.homFunctor (CatFiberedInSetoids.inclusion.map f)).map
          (Functor.Fiber.fiberInclusion.map ψ.hom)) :=
      Functor.isHomLift_map_of_comp_eq_general
        (CatFiberedInGroupoids.homFunctor_comp_p (CatFiberedInSetoids.inclusion.map f)) _ _
        this
    exact Functor.hom_unique_of_fiber_isThin 𝒴.val.p
      (𝟙 (U.iteratedSliceBackward.obj V.unop).left)
      (Functor.IsFiberedInSetoids.fiber_isThin _) _ _
      (by
        have hφ₂ : 𝒴.val.p.IsHomLift (𝟙 (U.iteratedSliceBackward.obj V.unop).left) φ := hφ
        exact @IsHomLift.comp_lift_id_right _ _ _ _ 𝒴.val.p _ _ _ _ _ _ φ hφ₂ _ hψ) hφ'
  · intro c
    obtain ⟨x, hx⟩ := Functor.isoClassMk_surjective c.1
    have hc : Functor.isoClassMk 𝒴.val.p
        ((Functor.Fiber.mapOfComp 𝒳.val.p 𝒴.val.p (CatFiberedInGroupoids.homFunctor f)
          (CatFiberedInGroupoids.homFunctor_comp_p f) _).obj x) =
        Functor.isoClassMk 𝒴.val.p
          (Functor.pullbackFiber 𝒴.val.p y (OverShriek.overMapTautHom U.hom V.unop)) :=
      (ha _ x).symm.trans ((congrArg (a.app _) hx).trans c.2)
    obtain ⟨ι⟩ := Functor.exists_iso_of_isoClassMk_eq hc.symm
    exact ⟨PairIsoClass.mk (CatFiberedInGroupoids.homFunctor (CatFiberedInSetoids.inclusion.map f))
      (Functor.chosenPullbacks 𝒴.val.p) y (CatFiberedInSetoids.inclusion.obj 𝒳).2
      (CatFiberedInSetoids.inclusion.obj 𝒴).2
      (CatFiberedInGroupoids.homFunctor_comp_p (CatFiberedInSetoids.inclusion.map f))
      (f := U.iteratedSliceBackward.obj V.unop) x ι.hom.1 ι.hom.2,
      Subtype.ext ((pairToFibre_mk_val B S hS f a ha U y V x ι.hom.1 ι.hom.2).trans hx)⟩

/-- `pairToFibre` is natural. -/
theorem pairToFibre_naturality ⦃V V' : (Over U.left)ᵒᵖ⦄ (h : V ⟶ V')
    (t : (pairPresheaf B S hS f U y).obj V) :
    pairToFibre B S hS f a ha U y V' ((pairPresheaf B S hS f U y).map h t) =
      (OverShriek.fibreOfElement U.hom a (Functor.isoClassMk 𝒴.val.p y)).map h
        (pairToFibre B S hS f a ha U y V t) := by
  obtain ⟨x, φ, hφ, rfl⟩ := PairIsoClass.mk_surjective
      (CatFiberedInGroupoids.homFunctor (CatFiberedInSetoids.inclusion.map f))
      (Functor.chosenPullbacks 𝒴.val.p) y (CatFiberedInSetoids.inclusion.obj 𝒳).2
      (CatFiberedInSetoids.inclusion.obj 𝒴).2
      (CatFiberedInGroupoids.homFunctor_comp_p (CatFiberedInSetoids.inclusion.map f))
    (f := U.iteratedSliceBackward.obj V.unop) t
  obtain ⟨x', φ', hφ', χ, hχ, hsq⟩ := PairIsoClass.exists_pair_of_hom
      (CatFiberedInGroupoids.homFunctor (CatFiberedInSetoids.inclusion.map f))
      (Functor.chosenPullbacks 𝒴.val.p) y (CatFiberedInSetoids.inclusion.obj 𝒳).2
      (CatFiberedInSetoids.inclusion.obj 𝒴).2
      (CatFiberedInGroupoids.homFunctor_comp_p (CatFiberedInSetoids.inclusion.map f))
    (U.iteratedSliceBackward.map h.unop) x φ hφ
  have hmap := PairIsoClass.presheaf_map_mk
      (CatFiberedInGroupoids.homFunctor (CatFiberedInSetoids.inclusion.map f))
      (Functor.chosenPullbacks 𝒴.val.p) y (CatFiberedInSetoids.inclusion.obj 𝒳).2
      (CatFiberedInSetoids.inclusion.obj 𝒴).2
      (CatFiberedInGroupoids.homFunctor_comp_p (CatFiberedInSetoids.inclusion.map f))
    (U.iteratedSliceBackward.map h.unop) x φ hφ x' φ' hφ' χ hχ hsq
  have := hχ
  have : (CatFiberedInSetoids.inclusion.obj 𝒳).val.p.IsFibered :=
    (CatFiberedInSetoids.inclusion.obj 𝒳).2.isFibered
  have hcart : (CatFiberedInSetoids.inclusion.obj 𝒳).val.p.IsStronglyCartesian
      (U.iteratedSliceBackward.map h.unop).left χ :=
    (CatFiberedInSetoids.inclusion.obj 𝒳).2.isStronglyCartesian_homLift _ χ
  apply Subtype.ext
  refine (congrArg (fun z => (pairToFibre B S hS f a ha U y V' z).1) hmap).trans ?_
  refine (pairToFibre_mk_val B S hS f a ha U y V' x' φ' hφ').trans ?_
  refine (Functor.isoClassMk_eq_pullbackFiber_of_isCartesian _ x x' χ hχ
    inferInstance).trans ?_
  exact congrArg (𝒳.val.p.isoClassPresheaf.map ((Over.map U.hom).map h.unop).op)
    (pairToFibre_mk_val B S hS f a ha U y V x φ hφ).symm

/-- The classes of pairs of Stacks 02ZY are the fibre of `a` over the class of `y`. -/
noncomputable def pairEquivFibre (V : (Over U.left)ᵒᵖ) :
    (pairPresheaf B S hS f U y).obj V ≃
      (OverShriek.fibreOfElement U.hom a (Functor.isoClassMk 𝒴.val.p y)).obj V :=
  Equiv.ofBijective _ (bijective_pairToFibre B S hS f a ha U y V)

end Pairs

/-- **Stacks 04SY.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of categories fibred in setoids over the
big fppf site of `S`, whose total objects lie in an arbitrary universe `w`, and let
`a : F ⟶ G` be the map of presheaves of isomorphism classes corresponding to `f`, i.e. sending
the class of `x` to the class of `f x`. Then `a` is representable by algebraic spaces (Stacks
02YQ, tested on the universe-lifted scheme-valued points of `G`, since `F` and `G` take values
in `Type w`) if and only if `f` is representable by algebraic spaces. -/
@[stacks 04SY "total objects in any universe; `a` tested on universe-lifted points"]
public theorem isoClassMap_isRepresentableByAlgebraicSpacesULift_iff
    {𝒳 𝒴 : CatFiberedInSetoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    (a : 𝒳.val.p.isoClassPresheaf ⟶ 𝒴.val.p.isoClassPresheaf)
    (ha : ∀ (U : BigFppfOver B S hS) (x : 𝒳.val.p.Fiber U),
      a.app (op U) (Functor.isoClassMk 𝒳.val.p x) =
        Functor.isoClassMk 𝒴.val.p
          ((Functor.Fiber.mapOfComp 𝒳.val.p 𝒴.val.p
            (CatFiberedInGroupoids.homFunctor f)
            (CatFiberedInGroupoids.homFunctor_comp_p f) U).obj x)) :
    Space.IsRepresentableByAlgebraicSpacesULift.{w} B S hS
        (Functor.whiskerRight a uliftFunctor.{u}) ↔
      IsRepresentableByAlgebraicSpaces B S hS (CatFiberedInSetoids.inclusion.map f).hom := by
  change _ ↔ _root_.AlgebraicGeometry.IsRepresentableByAlgebraicSpaces B S hS
    (CatFiberedInSetoids.inclusion.map f).hom
  rw [_root_.AlgebraicGeometry.isRepresentableByAlgebraicSpaces_iff_associatedMap B S hS
    (CatFiberedInSetoids.inclusion.map f) (Functor.chosenPullbacks 𝒴.val.p)]
  constructor
  · intro h
    refine ⟨fun U => ⟨fun {x₁ x₂} φ φ' _ =>
      @Subsingleton.elim _ (𝒳.2.fiber_isThin U x₁ x₂) φ φ'⟩,
      fun U y => ?_⟩
    obtain ⟨W, hW, e, he⟩ := (isAlgebraicSpaceULift_pullback_iff B S hS a U
      (Functor.isoClassMk 𝒴.val.p y) (pointOfElement B S hS U _) (fun _ => rfl)).mp (h U _)
    refine ⟨W, hW, fun V => (pairEquivFibre B S hS f a ha U y V).trans (e V), ?_⟩
    intro V V' h' x
    exact (congrArg (e V') (pairToFibre_naturality B S hS f a ha U y h' x)).trans (he h' _)
  · rintro ⟨-, h⟩ U ξ
    let g := (ξ.app (op U) (ULift.up (𝟙 U))).down
    obtain ⟨y, hy⟩ := Functor.isoClassMk_surjective g
    have hξ : ∀ {T : BigFppfOver B S hS} (t : T ⟶ Over.mk U.hom),
        ξ.app (op T) (ULift.up t) = ULift.up (𝒴.val.p.isoClassPresheaf.map t.op
          (Functor.isoClassMk 𝒴.val.p y)) := by
      intro T t
      have ht : (uliftYoneda.{w}.obj U).map t.op (ULift.up (𝟙 U)) = ULift.up t :=
        ULift.ext (Category.comp_id t)
      have hn : ξ.app (op T) ((uliftYoneda.{w}.obj U).map t.op (ULift.up (𝟙 U))) =
          (𝒴.val.p.isoClassPresheaf ⋙ uliftFunctor.{u}).map t.op
            (ξ.app (op U) (ULift.up (𝟙 U))) :=
        NatTrans.naturality_apply ξ t.op _
      rw [ht] at hn
      exact hn.trans (by rw [hy]; rfl)
    refine (isAlgebraicSpaceULift_pullback_iff B S hS a U (Functor.isoClassMk 𝒴.val.p y) ξ
      hξ).mpr ?_
    obtain ⟨W, hW, e, he⟩ := h U y
    refine ⟨W, hW, fun V => (pairEquivFibre B S hS f a ha U y V).symm.trans (e V), ?_⟩
    intro V V' h' x
    have hx : x = pairToFibre B S hS f a ha U y V ((pairEquivFibre B S hS f a ha U y V).symm x) :=
      ((pairEquivFibre B S hS f a ha U y V).apply_symm_apply x).symm
    change e V' ((pairEquivFibre B S hS f a ha U y V').symm _) = _
    conv_lhs => rw [hx, ← pairToFibre_naturality]
    change e V' ((pairEquivFibre B S hS f a ha U y V').symm
      (pairEquivFibre B S hS f a ha U y V' _)) = _
    rw [Equiv.symm_apply_apply]
    exact he h' _

end AlgebraicGeometry.Stack

end
