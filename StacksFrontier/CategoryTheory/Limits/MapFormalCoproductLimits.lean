module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Basic

/-!
# Products and fibre products of semi-representable objects, and their images

Let `C` be a category. A product of a family of formal coproducts of objects of `C` is computed
summandwise over the choices of one summand in each factor: the index set of `∏_{a ∈ ι} X^{(a)}`
is `∏_{a ∈ ι} I(X^{(a)})`, and the summand at a choice `s` is a product in `C` of the chosen
summands. A fibre product is computed summandwise over the compatible pairs of summands. This
file constructs both, from the summandwise data, and deduces that a functor `F : C ⥤ D` which
preserves such products, respectively such fibre products, induces a functor on formal coproducts
which does too.

## Main definitions

* `formalProductFan`: the product fan of a family of formal coproducts, from summandwise
  product fans.
* `formalPullbackPt`, `formalPullbackFst`, `formalPullbackSnd`: the fibre product of a cospan of
  formal coproducts, from summandwise fibre products.

## Main results

* `isLimitFormalProductFan` and `isPullback_formalPullback`: they are limits.
* `preservesLimitsOfShape_discrete_mapFormalCoproduct`: `mapFormalCoproduct F` preserves
  `ι`-indexed products as soon as `C` has them and `F` preserves them.
* `preservesLimitsOfShape_walkingCospan_mapFormalCoproduct`: `mapFormalCoproduct F` preserves
  fibre products as soon as `C` has them and `F` preserves them.

## Implementation notes

The index universe is the same for the formal coproducts and for the indexing type of the family:
the index set of the product is a function type out of that indexing type, so a larger indexing
universe would not give a formal coproduct at all.

Both constructions take the summandwise limits as *data* -- the summand objects, their
projections, and the statement that the resulting summandwise cone is a limit -- rather than as a
family of cones or through a `HasLimit` instance. This is what makes the image of the construction
under `mapFormalCoproduct F` be the construction again, with no comparison isomorphism: the image
of the point is the point built from the images of the summands, and the image of a projection is
the projection, both by definitional unfolding alone.

The second leg of the summandwise cospan of a fibre product carries the `eqToHom` identifying the
two summands of the target that the two legs land in, and the image of that leg under `F` is the
corresponding leg of the image cospan only after `Functor.map_comp` and `eqToHom_map`. The
identification is made once, in `map_formalCoproduct_cospan_fst`, and used only as a rewrite
inside the proposition `IsPullback`.
-/

@[expose] public section

universe w v₁ u₁ v u

open CategoryTheory CategoryTheory.Limits

namespace Stacks.CategoryTheory.Hypercovering

attribute [local implicit_reducible] mapFormalCoproduct

variable {C : Type u} [Category.{v} C] {D : Type u₁} [Category.{v₁} D]

section Products

variable {ι : Type w} (X : ι → FormalCoproduct.{w} C)
  (P : (∀ a, (X a).I) → C) (pr : ∀ (a : ι) (s : ∀ a, (X a).I), P s ⟶ (X a).obj (s a))

/-- **The point of a product of semi-representable objects.** A morphism into it is a choice, for
each of its own summands, of one summand of every factor together with a morphism into the
product of those; so the index set is the type of choice functions and the summand at a choice
`s` is the given product `P s` of the chosen summands. -/
abbrev formalProductPt : FormalCoproduct.{w} C := ⟨(∀ a, (X a).I), P⟩

/-- The projection of `formalProductPt` to the factor at `a`: on indices the evaluation at `a`,
on summands the given summandwise projection. -/
abbrev formalProductProj (a : ι) : formalProductPt X P ⟶ X a :=
  ⟨fun s => s a, fun s => pr a s⟩

/-- **The product fan of a family of semi-representable objects**, assembled from summandwise
product fans. -/
abbrev formalProductFan : Fan X := Fan.mk (formalProductPt X P) (formalProductProj X P pr)

variable (hpr : ∀ s, IsLimit (Fan.mk (P s) fun a => pr a s))

include hpr

/-- The universal property of `formalProductFan`: a morphism into it is exactly a family of
morphisms into the factors. -/
noncomputable def formalProductFanHomEquiv (T : FormalCoproduct.{w} C) :
    (T ⟶ formalProductPt X P) ≃ (∀ a, T ⟶ X a) where
  toFun m a := m ≫ formalProductProj X P pr a
  invFun s := ⟨fun i a => (s a).f i, fun i => Fan.IsLimit.lift (hpr _) fun a => (s a).φ i⟩
  left_inv m := FormalCoproduct.hom_ext rfl fun i => by
    simp only [eqToHom_refl, Category.comp_id]
    exact Fan.IsLimit.hom_ext (hpr (m.f i)) _ _ fun a => Fan.IsLimit.fac (hpr (m.f i)) _ a
  right_inv s := funext fun a => FormalCoproduct.hom_ext rfl fun i => by
    simp only [eqToHom_refl, Category.comp_id]
    exact Fan.IsLimit.fac (hpr _) _ a

/-- **`formalProductFan` is a product.** -/
noncomputable def isLimitFormalProductFan : IsLimit (formalProductFan X P pr) :=
  Fan.IsLimit.mk _
    (fun t => (formalProductFanHomEquiv X P pr hpr t.pt).symm fun a => t.proj a)
    (fun t a =>
      congrFun ((formalProductFanHomEquiv X P pr hpr t.pt).right_inv fun a => t.proj a) a)
    (fun t _m hm => (formalProductFanHomEquiv X P pr hpr t.pt).eq_symm_apply.2 (funext hm))

/-- **A functor preserving the summandwise products preserves the product of
semi-representable objects.** The product fan of the images is the image of the product fan: the
index set is unchanged and the summands are the images of the summands. -/
theorem preservesLimit_discrete_mapFormalCoproduct (F : C ⥤ D)
    (hprF : ∀ s, IsLimit (Fan.mk (F.obj (P s)) fun a => F.map (pr a s))) :
    PreservesLimit (Discrete.functor X) (mapFormalCoproduct.{w} F) :=
  preservesLimit_of_preserves_limit_cone (isLimitFormalProductFan X P pr hpr)
    ((isLimitMapConeFanMkEquiv (mapFormalCoproduct.{w} F) X
      (formalProductProj X P pr)).symm
      (isLimitFormalProductFan (fun a => (mapFormalCoproduct.{w} F).obj (X a))
        (fun s => F.obj (P s)) (fun a s => F.map (pr a s)) hprF))

end Products

section Pullbacks

variable {X Y Z : FormalCoproduct.{w} C} (f : X ⟶ Z) (g : Y ⟶ Z)

/-- The first leg of the summandwise cospan of a cospan of semi-representable objects: the
component of `f` at the chosen summand, carried into the summand of the target that the component
of `g` lands in. -/
abbrev formalCospanFst (i : Function.Pullback f.f g.f) : X.obj i.1.1 ⟶ Z.obj (g.f i.1.2) :=
  f.φ i.1.1 ≫ eqToHom (congrArg Z.obj i.2)

variable (P : Function.Pullback f.f g.f → C)
  (pfst : ∀ i, P i ⟶ X.obj i.1.1) (psnd : ∀ i, P i ⟶ Y.obj i.1.2)

/-- **The point of a fibre product of semi-representable objects.** A morphism into it is a
choice, for each of its own summands, of a compatible pair of summands of the two sources
together with a morphism into the fibre product of those; so the index set is the type of
compatible pairs and the summand at such a pair is the given fibre product `P i`. -/
abbrev formalPullbackPt : FormalCoproduct.{w} C := ⟨Function.Pullback f.f g.f, P⟩

/-- The first projection of `formalPullbackPt`. -/
abbrev formalPullbackFst : formalPullbackPt f g P ⟶ X := ⟨fun i => i.1.1, pfst⟩

/-- The second projection of `formalPullbackPt`. -/
abbrev formalPullbackSnd : formalPullbackPt f g P ⟶ Y := ⟨fun i => i.1.2, psnd⟩

variable (hsq : ∀ i, IsPullback (pfst i) (psnd i) (formalCospanFst f g i) (g.φ i.1.2))

include hsq

/-- Two morphisms into one summand of `formalPullbackPt` agree as soon as their composites with
the two summandwise projections do.

The two morphisms land in the summands at two *equal* compatible pairs, not at the same one, so
the comparison carries the `eqToHom` identifying them; stating the step here, with the pair
universally quantified, is what lets that equality be eliminated by `subst` instead of
transported. -/
private theorem formalPullback_component_ext {A : C}
    {k l : Function.Pullback f.f g.f} (h : k = l) (a : A ⟶ P k) (b : A ⟶ P l)
    (h₁ : a ≫ pfst k ≫ eqToHom (congrArg (fun j : Function.Pullback f.f g.f => X.obj j.1.1) h) =
      b ≫ pfst l)
    (h₂ : a ≫ psnd k ≫ eqToHom (congrArg (fun j : Function.Pullback f.f g.f => Y.obj j.1.2) h) =
      b ≫ psnd l)
    (hP : P k = P l) :
    a ≫ eqToHom hP = b := by
  subst h
  simp only [eqToHom_refl, Category.comp_id] at h₁ h₂ ⊢
  exact (hsq _).hom_ext h₁ h₂

/-- **A square of semi-representable objects assembled from summandwise fibre products is a
fibre product.** -/
theorem isPullback_formalPullback :
    IsPullback (formalPullbackFst f g P pfst) (formalPullbackSnd f g P psnd) f g := by
  refine IsPullback.of_isLimit' ⟨FormalCoproduct.hom_ext (funext fun i => i.2) fun i => ?_⟩ ?_
  · exact (Category.assoc _ _ _).trans (hsq i).w
  · refine PullbackCone.IsLimit.mk _
      (fun s => ⟨fun i => ⟨(s.fst.f i, s.snd.f i),
          congrFun (congrArg FormalCoproduct.Hom.f s.condition) i⟩,
        fun i => (hsq _).lift (s.fst.φ i) (s.snd.φ i) ?_⟩)
      (fun s => FormalCoproduct.hom_ext rfl fun i => ?_)
      (fun s => FormalCoproduct.hom_ext rfl fun i => ?_)
      (fun s m h₁ h₂ => (FormalCoproduct.hom_ext_iff' _ _).2 fun i => ?_)
    · exact (Category.assoc _ _ _).symm.trans
        ((FormalCoproduct.hom_ext_iff' _ _).1 s.condition i).2
    · simp
    · simp
    · obtain ⟨hA, hA'⟩ := (FormalCoproduct.hom_ext_iff' _ _).1 h₁ i
      obtain ⟨hB, hB'⟩ := (FormalCoproduct.hom_ext_iff' _ _).1 h₂ i
      exact ⟨Subtype.ext (Prod.ext hA hB), formalPullback_component_ext f g P pfst psnd hsq
        (Subtype.ext (Prod.ext hA hB)) (m.φ i) _ (by simpa using hA') (by simpa using hB') _⟩

omit hsq

/-- The first leg of the summandwise cospan of the image cospan is the image of the first leg of
the summandwise cospan: the `eqToHom` identifying the two summands of the target is carried
across by `eqToHom_map`. -/
theorem map_formalCoproduct_cospan_fst (F : C ⥤ D) (i : Function.Pullback f.f g.f) :
    F.map (formalCospanFst f g i) =
      formalCospanFst ((mapFormalCoproduct.{w} F).map f) ((mapFormalCoproduct.{w} F).map g) i := by
  rw [formalCospanFst, formalCospanFst, F.map_comp, eqToHom_map]
  rfl

include hsq in
/-- **A functor preserving the summandwise fibre products preserves the fibre product of
semi-representable objects.** -/
theorem preservesLimit_cospan_mapFormalCoproduct (F : C ⥤ D)
    [∀ i, PreservesLimit (cospan (formalCospanFst f g i) (g.φ i.1.2)) F] :
    PreservesLimit (cospan f g) (mapFormalCoproduct.{w} F) := by
  have hsqF : ∀ i : Function.Pullback ((mapFormalCoproduct.{w} F).map f).f
      ((mapFormalCoproduct.{w} F).map g).f,
      IsPullback (F.map (pfst i)) (F.map (psnd i))
        (formalCospanFst ((mapFormalCoproduct.{w} F).map f)
          ((mapFormalCoproduct.{w} F).map g) i)
        (((mapFormalCoproduct.{w} F).map g).φ i.1.2) := fun i =>
    map_formalCoproduct_cospan_fst f g F i ▸ (hsq i).map F
  exact preservesLimit_of_preserves_limit_cone
    (isPullback_formalPullback f g P pfst psnd hsq).isLimit
    (((isPullback_formalPullback f g P pfst psnd hsq).cone.isLimitMapConeEquiv
      (mapFormalCoproduct.{w} F)).symm
        ((isPullback_formalPullback ((mapFormalCoproduct.{w} F).map f)
          ((mapFormalCoproduct.{w} F).map g) (fun i => F.obj (P i))
          (fun i => F.map (pfst i)) (fun i => F.map (psnd i)) hsqF).isLimit))

end Pullbacks

/-- **`mapFormalCoproduct F` preserves `ι`-indexed products** as soon as `C` has them and `F`
preserves them. -/
theorem preservesLimitsOfShape_discrete_mapFormalCoproduct {ι : Type w} (F : C ⥤ D)
    [HasProductsOfShape ι C] [PreservesLimitsOfShape (Discrete ι) F] :
    PreservesLimitsOfShape (Discrete ι) (mapFormalCoproduct.{w} F) := by
  have : ∀ X : ι → FormalCoproduct.{w} C,
      PreservesLimit (Discrete.functor X) (mapFormalCoproduct.{w} F) := fun X =>
    preservesLimit_discrete_mapFormalCoproduct X (fun s => ∏ᶜ fun a => (X a).obj (s a))
      (fun a _ => Pi.π _ a) (fun _ => productIsProduct _) F
      (fun _ => isLimitOfHasProductOfPreservesLimit F _)
  exact preservesLimitsOfShape_of_discrete _

/-- **`mapFormalCoproduct F` preserves fibre products** as soon as `C` has them and `F` preserves
them. -/
theorem preservesLimitsOfShape_walkingCospan_mapFormalCoproduct (F : C ⥤ D) [HasPullbacks C]
    [PreservesLimitsOfShape WalkingCospan F] :
    PreservesLimitsOfShape WalkingCospan (mapFormalCoproduct.{w} F) := by
  have : ∀ {X Y Z : FormalCoproduct.{w} C} (f : X ⟶ Z) (g : Y ⟶ Z),
      PreservesLimit (cospan f g) (mapFormalCoproduct.{w} F) := fun f g =>
    preservesLimit_cospan_mapFormalCoproduct f g
      (fun i => pullback (formalCospanFst f g i) (g.φ i.1.2))
      (fun _ => pullback.fst _ _) (fun _ => pullback.snd _ _)
      (fun _ => IsPullback.of_hasPullback _ _) F
  exact ⟨fun {K} => preservesLimit_of_iso_diagram _ (diagramIsoCospan K).symm⟩

end Stacks.CategoryTheory.Hypercovering

end
