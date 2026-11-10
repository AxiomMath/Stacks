module

public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.SmallEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.MorphismComposition

/-!
# The comparison maps of small étale restrictions compose (Stacks 075D (1))

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids, let `F` be an étale sheaf on
`𝒳`, and let `φ : x ⟶ y` and `ψ : y ⟶ z` be arrows of `𝒳`, lying over morphisms of schemes
`a : U ⟶ V` and `b : V ⟶ W`. Stacks 06W3 gives comparison maps
`c_φ : a_{small}^{-1}(F|_{V_ét}) ⟶ F|_{U_ét}` and likewise for `ψ` and for `ψ ∘ φ`.

**Stacks 075D (1)** says that the composite
`a_{small}^{-1}(b_{small}^{-1}(F|_{W_ét})) → a_{small}^{-1}(F|_{V_ét}) → F|_{U_ét}` is
`c_{ψ ∘ φ}`, under the canonical identification
`(b ∘ a)_{small}^{-1}(F|_{W_ét}) = a_{small}^{-1}(b_{small}^{-1}(F|_{W_ét}))`.

## Main definitions

* `AlgebraicGeometry.Stack.restrictionInverseImageCompIso`: the canonical identification of a
  composite of small étale inverse images with the inverse image along the composite.

## Main results

* `AlgebraicGeometry.Stack.restrictionInverseImageComparison_comp`: **Stacks 075D (1)**.
* `AlgebraicGeometry.Stack.restrictionPushforwardComparison_app_comp`: the same statement for
  the direct-image comparisons of Stacks 06W2, from which it is obtained by taking mates. This
  form is the sharper one: it holds for a presheaf with values in an arbitrary category, and it
  pins each side down as restriction of the presheaf along an explicit arrow of `𝒳`.
* `AlgebraicGeometry.Stack.smallEtaleBaseMorphism_comp`: the morphism of schemes below an arrow
  of `𝒳` is functorial.

## Implementation notes

The direct-image form is the one with content, and it is proved by the component formula
`AlgebraicGeometry.Stack.restrictionPushforwardComparison_app`: each of the three comparisons
is restriction of the presheaf along the arrow of `𝒳` between the cartesian lifts of a
base-change square, so the statement becomes an equality of two arrows of `𝒳`. Producing those
arrows is one construction carried out three times, which is
`AlgebraicGeometry.Stack.exists_restrictionComparisonLift`; the resulting equality of arrows
holds because both sides lift the same morphism of schemes and factor the same arrow, and in a
category fibred in groupoids that forces them to agree.

Identifying the two morphisms of schemes is where the composition comparison of base changes
enters, through `AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso_hom_app_fst`. The
`factored` form of that comparison is needed because the morphism of schemes below `ψ ∘ φ` is
only provably, not syntactically, the composite of those below `φ` and `ψ`; that is
`AlgebraicGeometry.Stack.smallEtaleBaseMorphism_comp`.

Passing from the direct-image form to the inverse-image form is formal: the comparisons are
mates, and the identification of inverse images is the mate of the identification of direct
images, so the two statements correspond under the hom-set bijections of the three adjunctions.

`CategoryTheory.Functor.IsFiberedInGroupoids.exists_hom_of_commSq` and
`.hom_eq_of_map_eq_of_comp_eq` are the two general facts about categories fibred in groupoids
that this needs.

## References

* [Stacks Project, Tag 075D](https://stacks.math.columbia.edu/tag/075D)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w t s

namespace CategoryTheory.Functor.IsFiberedInGroupoids

universe u₁ v₁ u₂ v₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {p : C ⥤ D}

/-- In a category fibred in groupoids, a square in the base whose right-hand and top edges are
already lifted can be completed: given `φ : x ⟶ y`, objects `a` over `x` and `b` over `y`, and a
morphism `β : p a ⟶ p b` making the square commute, there is an arrow `a ⟶ b` lying over `β`
and filling the square. -/
theorem exists_hom_of_commSq (hp : p.IsFiberedInGroupoids) {x y : C} (φ : x ⟶ y) {a b : C}
    (ha : a ⟶ x) (hb : b ⟶ y) (β : p.obj a ⟶ p.obj b)
    (hβ : β ≫ p.map hb = p.map ha ≫ p.map φ) :
    ∃ α : a ⟶ b, p.map α = β ∧ α ≫ hb = ha ≫ φ := by
  obtain ⟨a₀, τ, hτ⟩ := hp.exists_lift β b rfl
  have hd := IsHomLift.domain_eq p β τ
  have hτmap : eqToHom hd.symm ≫ p.map τ = β := by
    rw [IsHomLift.fac' p β τ]
    simp
  have hdiag : eqToHom hd.symm ≫ p.map (τ ≫ hb) = p.map (ha ≫ φ) := by
    rw [Functor.map_comp, Functor.map_comp, ← Category.assoc, hτmap, hβ]
  obtain ⟨χ, hχ, _⟩ := hp.unique_lift (τ ≫ hb) (ha ≫ φ) (eqToHom hd.symm) hdiag
  refine ⟨χ ≫ τ, ?_, ?_⟩
  · rw [Functor.map_comp, hχ.1, hτmap]
  · simpa [Category.assoc] using hχ.2

/-- In a category fibred in groupoids, two parallel arrows lying over the same morphism of the
base and factoring the same arrow are equal: the fill-in of the second axiom is unique. -/
theorem hom_eq_of_map_eq_of_comp_eq (hp : p.IsFiberedInGroupoids) {a b c : C} {f₁ f₂ : a ⟶ b}
    (k : b ⟶ c) (hmap : p.map f₁ = p.map f₂) (hfac : f₁ ≫ k = f₂ ≫ k) : f₁ = f₂ := by
  obtain ⟨u, _, huniq⟩ := hp.unique_lift k (f₁ ≫ k) (p.map f₁) (by simp)
  exact (huniq f₁ ⟨rfl, rfl⟩).trans (huniq f₂ ⟨hmap.symm, hfac.symm⟩).symm

end CategoryTheory.Functor.IsFiberedInGroupoids

namespace CategoryTheory

universe u₁ v₁ u₂ v₂ u₃ v₃

/-- The hom-set bijection of a composite adjunction, applied to a composite of transposes, is
the composite of the two maps it transposes. -/
private theorem comp_homEquiv_symm_comp {C₀ : Type u₁} [Category.{v₁} C₀] {C₁ : Type u₂}
    [Category.{v₂} C₁] {C₂ : Type u₃} [Category.{v₃} C₂] {L₀₁ : C₀ ⥤ C₁} {R₁₀ : C₁ ⥤ C₀}
    {L₁₂ : C₁ ⥤ C₂} {R₂₁ : C₂ ⥤ C₁} (adj₀₁ : L₀₁ ⊣ R₁₀) (adj₁₂ : L₁₂ ⊣ R₂₁)
    {X : C₀} {Y₁ : C₁} {Y₂ : C₂} (f : X ⟶ R₁₀.obj Y₁) (g : Y₁ ⟶ R₂₁.obj Y₂) :
    (adj₀₁.comp adj₁₂).homEquiv X Y₂
        (L₁₂.map ((adj₀₁.homEquiv X Y₁).symm f) ≫ (adj₁₂.homEquiv Y₁ Y₂).symm g) =
      f ≫ R₁₀.map g := by
  rw [Adjunction.comp_homEquiv]
  simp only [Equiv.trans_apply]
  rw [adj₁₂.homEquiv_naturality_left, Equiv.apply_symm_apply,
    adj₀₁.homEquiv_naturality_right]
  simp

/-- Transposing along a conjugate pair of isomorphisms of adjoints: precomposing a transpose
with the component of an isomorphism of left adjoints corresponds to postcomposing with the
component of the conjugate isomorphism of right adjoints. -/
private theorem homEquiv_comp_conjugate {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] {L₁ L₀ : C ⥤ D} {R₁ R₀ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₀ : L₀ ⊣ R₀)
    (eL : L₁ ≅ L₀) (eR : R₁ ≅ R₀) (he : conjugateEquiv adj₀ adj₁ eL.hom = eR.inv)
    (X : C) {Y : D} (d : X ⟶ R₀.obj Y) :
    adj₁.homEquiv X Y (eL.hom.app X ≫ (adj₀.homEquiv X Y).symm d) = d ≫ eR.inv.app Y := by
  rw [Adjunction.homEquiv_apply, Functor.map_comp, ← Category.assoc]
  rw [← CategoryTheory.unit_conjugateEquiv adj₀ adj₁ eL.hom X, he]
  rw [Category.assoc, ← eR.inv.naturality ((adj₀.homEquiv X Y).symm d)]
  rw [← Category.assoc, ← adj₀.homEquiv_apply, Equiv.apply_symm_apply]

/-- A functor preserves an equality of composites of two arrows. -/
private theorem map_comp_eq_map_comp {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] (F : C ⥤ D) {W X Y Z : C} {a : W ⟶ X} {b : X ⟶ Y} {c : W ⟶ Z} {d : Z ⟶ Y}
    (h : a ≫ b = c ≫ d) : F.map a ≫ F.map b = F.map c ≫ F.map d := by
  rw [← F.map_comp, ← F.map_comp, h]

end CategoryTheory

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

/-- The morphism of the big étale category of schemes below an arrow of a category fibred in
groupoids is functorial in the arrow. -/
theorem smallEtaleBaseMorphism_comp {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) {x y z : 𝒳} (φ : x ⟶ y) (ψ : y ⟶ z) :
    smallEtaleBaseMorphism B E h S hS p (φ ≫ ψ) =
      smallEtaleBaseMorphism B E h S hS p φ ≫ smallEtaleBaseMorphism B E h S hS p ψ := by
  apply ObjectProperty.hom_ext
  simp [smallEtaleBaseMorphism]

/-- The canonical identification, for arrows `φ : x ⟶ y` and `ψ : y ⟶ z` of a category fibred
in groupoids, of the composite of the small étale inverse images along the underlying morphisms
of schemes with the inverse image along the underlying morphism of `ψ ∘ φ`.

This is the identification appearing in **Stacks 075D (1)**. It is the mate of the direct-image
comparison induced by `AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso`. -/
@[stacks 075D "part (1), the identification of successive inverse images"]
noncomputable def restrictionInverseImageCompIso {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) {x y z : 𝒳} (φ : x ⟶ y) (ψ : y ⟶ z) :
    (smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p ψ)).sheafPullback
        (Type (max (u + 1) t))
        (SmallEtale.topology E (p.obj z).left.1 (contains_base B E h S hS p z))
        (SmallEtale.topology E (p.obj y).left.1 (contains_base B E h S hS p y)) ⋙
      (smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).sheafPullback
        (Type (max (u + 1) t))
        (SmallEtale.topology E (p.obj y).left.1 (contains_base B E h S hS p y))
        (SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x)) ≅
    (smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p (φ ≫ ψ))).sheafPullback
      (Type (max (u + 1) t))
      (SmallEtale.topology E (p.obj z).left.1 (contains_base B E h S hS p z))
      (SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x)) :=
  Adjunction.leftAdjointCompIso
    ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p ψ)).sheafAdjunctionContinuous
      (Type (max (u + 1) t))
      (SmallEtale.topology E (p.obj z).left.1 (contains_base B E h S hS p z))
      (SmallEtale.topology E (p.obj y).left.1 (contains_base B E h S hS p y)))
    ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).sheafAdjunctionContinuous
      (Type (max (u + 1) t))
      (SmallEtale.topology E (p.obj y).left.1 (contains_base B E h S hS p y))
      (SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x)))
    ((smallEtaleBaseChange E
        (smallEtaleBaseMorphism B E h S hS p (φ ≫ ψ))).sheafAdjunctionContinuous
      (Type (max (u + 1) t))
      (SmallEtale.topology E (p.obj z).left.1 (contains_base B E h S hS p z))
      (SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x)))
    (Functor.sheafPushforwardContinuousComp'
      (smallEtaleBaseChange_factoredCompIso E _ _ _
        (smallEtaleBaseMorphism B E h S hS p φ) (smallEtaleBaseMorphism B E h S hS p ψ)
        (smallEtaleBaseMorphism B E h S hS p (φ ≫ ψ))
        (smallEtaleBaseMorphism_comp B E h S hS p φ ψ).symm)
      (Type (max (u + 1) t))
      (SmallEtale.topology E (p.obj z).left.1 (contains_base B E h S hS p z))
      (SmallEtale.topology E (p.obj y).left.1 (contains_base B E h S hS p y))
      (SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x)))

/-- The arrow of `𝒳` that computes the direct-image comparison of Stacks 06W2 at a small étale
object `W` over the scheme `V` below `y`: it joins the cartesian lifts of `W` and of its base
change along the morphism of schemes below `φ`, and lies over the projection of the base-change
square.

The existence of such an arrow is what makes
`AlgebraicGeometry.Stack.restrictionPushforwardComparison_app` applicable; the two conditions
are exactly that lemma's hypotheses. -/
theorem exists_restrictionComparisonLift {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids) {x y : 𝒳} (φ : x ⟶ y)
    (W : SmallEtale E (p.obj y).left.1 (contains_base B E h S hS p y)) :
    letI : (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).IsEquivalence :=
      isEquivalence_overPost B S hS p hp x
    letI : (Over.post (X := y) (p ⋙ Over.forget (B.obj hS))).IsEquivalence :=
      isEquivalence_overPost B S hS p hp y
    let f := smallEtaleBaseMorphism B E h S hS p φ
    let V' := (smallEtaleInclusion B E h (p.obj y).left.1 (contains_base B E h S hS p y)).obj W
    let U' := (smallEtaleInclusion B E h (p.obj x).left.1
      (contains_base B E h S hS p x)).obj ((smallEtaleBaseChange E f).obj W)
    let y' := (Over.post (X := y) (p ⋙ Over.forget (B.obj hS))).inv.obj V'
    let x' := (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).inv.obj U'
    let εy := (Over.post (X := y) (p ⋙ Over.forget (B.obj hS))).asEquivalence.counit.app V'
    let εx := (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).asEquivalence.counit.app U'
    ∃ φ' : x'.left ⟶ y'.left, φ' ≫ y'.hom = x'.hom ≫ φ ∧
      B.inclusion.map (p.map φ').left ≫ B.inclusion.map εy.left =
        B.inclusion.map εx.left ≫ E.inclusion.map (pullback.fst W.obj.hom f) := by
  classical
  intro f V' U' y' x' εy εx
  let q := p ⋙ Over.forget (B.obj hS)
  let Fx := Over.post (X := x) q
  let Fy := Over.post (X := y) q
  let : Fx.IsEquivalence := isEquivalence_overPost B S hS p hp x
  let : Fy.IsEquivalence := isEquivalence_overPost B S hS p hp y
  let I := ObjectProperty.ιOfLE (P := schemeSizeBelow E.cutoff)
    (P' := schemeSizeBelow B.cutoff) (by intro Z hZ; simpa [h] using hZ)
  let ey := Fy.asEquivalence.counitIso.app V'
  let ex := Fx.asEquivalence.counitIso.app U'
  let fst' : U'.left ⟶ V'.left := I.map (pullback.fst W.obj.hom f)
  have heyInvHom : ey.inv.left ≫ ey.hom.left = 𝟙 V'.left :=
    congrArg Over.Hom.left ey.inv_hom_id
  have heyW : ey.hom.left ≫ V'.hom = q.map y'.hom := ey.hom.w
  have hexW : ex.hom.left ≫ U'.hom = q.map x'.hom := ex.hom.w
  have heyInvW : ey.inv.left ≫ q.map y'.hom = V'.hom :=
    (congrArg (fun k => ey.inv.left ≫ k) heyW.symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun k => k ≫ V'.hom) heyInvHom).trans (Category.id_comp _)))
  have hfstW : fst' ≫ V'.hom = U'.hom ≫ I.map f := map_comp_eq_map_comp I pullback.condition
  have hβ : (ex.hom.left ≫ fst' ≫ ey.inv.left) ≫ q.map y'.hom =
      q.map x'.hom ≫ q.map φ :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun k => ex.hom.left ≫ k) (Category.assoc _ _ _)).trans
        ((congrArg (fun k => ex.hom.left ≫ fst' ≫ k) heyInvW).trans
          ((congrArg (fun k => ex.hom.left ≫ k) hfstW).trans
            ((Category.assoc _ _ _).symm.trans
              (congrArg (fun k => k ≫ I.map f) hexW)))))
  let βOver : p.obj x'.left ⟶ p.obj y'.left :=
    Over.homMk (ex.hom.left ≫ fst' ≫ ey.inv.left)
      ((congrArg (fun k => (ex.hom.left ≫ fst' ≫ ey.inv.left) ≫ k)
          (p.map y'.hom).w.symm).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun k => k ≫ (p.obj y).hom) hβ).trans
            ((Category.assoc _ _ _).trans
              ((congrArg (fun k => q.map x'.hom ≫ k) (p.map φ).w).trans
                (p.map x'.hom).w)))))
  have hβOver : βOver ≫ p.map y'.hom = p.map x'.hom ≫ p.map φ :=
    Over.OverMorphism.ext hβ
  obtain ⟨α, hαmap, hαfac⟩ :=
    Functor.IsFiberedInGroupoids.exists_hom_of_commSq hp φ x'.hom y'.hom βOver hβOver
  have hqα : q.map α = ex.hom.left ≫ fst' ≫ ey.inv.left :=
    congrArg Over.Hom.left hαmap
  refine ⟨α, hαfac, ?_⟩
  have hkey : (p.map α).left ≫ εy.left = εx.left ≫ fst' :=
    (congrArg (fun k => k ≫ ey.hom.left) hqα).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k => ex.hom.left ≫ k) (Category.assoc _ _ _)).trans
          ((congrArg (fun k => ex.hom.left ≫ fst' ≫ k) heyInvHom).trans
            (congrArg (fun k => ex.hom.left ≫ k) (Category.comp_id _)))))
  exact map_comp_eq_map_comp B.inclusion hkey

/-- **Stacks 075D (1)** for the direct-image comparisons of Stacks 06W2: the comparison for a
composite arrow, followed by restriction along the composition comparison of base changes, is
the composite of the two comparisons.

This is the form with content; the inverse-image statement of the source is its mate. It holds
for a presheaf with values in an arbitrary category. -/
@[stacks 075D "part (1), the direct-image form"]
theorem restrictionPushforwardComparison_app_comp {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids) {x y z : 𝒳}
    (φ : x ⟶ y) (ψ : y ⟶ z) {A : Type t} [Category.{s} A] (F : 𝒳ᵒᵖ ⥤ A)
    (W : SmallEtale E (p.obj z).left.1 (contains_base B E h S hS p z)) :
    (restrictionPushforwardComparison B E h S hS p hp ψ F).app (Opposite.op W) ≫
        (restrictionPushforwardComparison B E h S hS p hp φ F).app (Opposite.op
          ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p ψ)).obj W)) =
      (restrictionPushforwardComparison B E h S hS p hp (φ ≫ ψ) F).app (Opposite.op W) ≫
        (restrictToSmallEtale B E h S hS p hp x F).map
          ((smallEtaleBaseChange_factoredCompIso E _ _ _
            (smallEtaleBaseMorphism B E h S hS p φ) (smallEtaleBaseMorphism B E h S hS p ψ)
            (smallEtaleBaseMorphism B E h S hS p (φ ≫ ψ))
            (smallEtaleBaseMorphism_comp B E h S hS p φ ψ).symm).hom.app W).op := by
  classical
  let q := p ⋙ Over.forget (B.obj hS)
  let Fx := Over.post (X := x) q
  let Fy := Over.post (X := y) q
  let Fz := Over.post (X := z) q
  let : Fx.IsEquivalence := isEquivalence_overPost B S hS p hp x
  let : Fy.IsEquivalence := isEquivalence_overPost B S hS p hp y
  let : Fz.IsEquivalence := isEquivalence_overPost B S hS p hp z
  let jx := smallEtaleInclusion B E h (p.obj x).left.1 (contains_base B E h S hS p x)
  let jy := smallEtaleInclusion B E h (p.obj y).left.1 (contains_base B E h S hS p y)
  let jz := smallEtaleInclusion B E h (p.obj z).left.1 (contains_base B E h S hS p z)
  let f := smallEtaleBaseMorphism B E h S hS p φ
  let g := smallEtaleBaseMorphism B E h S hS p ψ
  let fg := smallEtaleBaseMorphism B E h S hS p (φ ≫ ψ)
  have hfg : f ≫ g = fg := (smallEtaleBaseMorphism_comp B E h S hS p φ ψ).symm
  let e := smallEtaleBaseChange_factoredCompIso E _ _ _ f g fg hfg
  let Wy := (smallEtaleBaseChange E g).obj W
  let Wx := (smallEtaleBaseChange E f).obj Wy
  let Wc := (smallEtaleBaseChange E fg).obj W
  -- the three lifts
  obtain ⟨αψ, hαψfac, hαψbase⟩ :=
    exists_restrictionComparisonLift B E h S hS p hp ψ W
  obtain ⟨αφ, hαφfac, hαφbase⟩ :=
    exists_restrictionComparisonLift B E h S hS p hp φ Wy
  obtain ⟨αc, hαcfac, hαcbase⟩ :=
    exists_restrictionComparisonLift B E h S hS p hp (φ ≫ ψ) W
  rw [restrictionPushforwardComparison_app B E h S hS p hp ψ F W αψ hαψfac hαψbase,
    restrictionPushforwardComparison_app B E h S hS p hp φ F Wy αφ hαφfac hαφbase,
    restrictionPushforwardComparison_app B E h S hS p hp (φ ≫ ψ) F W αc hαcfac hαcbase]
  -- the arrow of `𝒳` induced by the composition comparison of base changes
  let k : jx.obj Wx ⟶ jx.obj Wc := jx.map (e.hom.app W)
  let βOver : Fx.inv.obj (jx.obj Wx) ⟶ Fx.inv.obj (jx.obj Wc) := Fx.inv.map k
  let β := βOver.left
  have hβfac : β ≫ (Fx.inv.obj (jx.obj Wc)).hom = (Fx.inv.obj (jx.obj Wx)).hom := βOver.w
  have hmapβ : (restrictToSmallEtale B E h S hS p hp x F).map (e.hom.app W).op =
      F.map β.op := rfl
  rw [hmapβ, ← F.map_comp, ← F.map_comp, ← op_comp, ← op_comp]
  -- the two arrows agree
  let εx := Fx.asEquivalence.counitIso.app (jx.obj Wx)
  let εy := Fy.asEquivalence.counitIso.app (jy.obj Wy)
  let εc := Fx.asEquivalence.counitIso.app (jx.obj Wc)
  let εz := Fz.asEquivalence.counitIso.app (jz.obj W)
  have hαcbase' : B.inclusion.map ((p.map αc).left) ≫ B.inclusion.map εz.hom.left =
      B.inclusion.map εc.hom.left ≫ E.inclusion.map (pullback.fst W.obj.hom fg) := hαcbase
  have hαφbase' : B.inclusion.map ((p.map αφ).left) ≫ B.inclusion.map εy.hom.left =
      B.inclusion.map εx.hom.left ≫ E.inclusion.map (pullback.fst Wy.obj.hom f) := hαφbase
  have hαψbase' : B.inclusion.map ((p.map αψ).left) ≫ B.inclusion.map εz.hom.left =
      B.inclusion.map εy.hom.left ≫ E.inclusion.map (pullback.fst W.obj.hom g) := hαψbase
  have hαcfac' : αc ≫ (Fz.inv.obj (jz.obj W)).hom =
      (Fx.inv.obj (jx.obj Wc)).hom ≫ (φ ≫ ψ) := hαcfac
  have hαφfac' : αφ ≫ (Fy.inv.obj (jy.obj Wy)).hom =
      (Fx.inv.obj (jx.obj Wx)).hom ≫ φ := hαφfac
  have hαψfac' : αψ ≫ (Fz.inv.obj (jz.obj W)).hom =
      (Fy.inv.obj (jy.obj Wy)).hom ≫ ψ := hαψfac
  have hβnat : (Fx.asEquivalence.functor.map βOver).left ≫ εc.hom.left =
      εx.hom.left ≫ k.left :=
    congrArg Over.Hom.left (Fx.asEquivalence.counitIso.hom.naturality k)
  have hβbase : B.inclusion.map ((p.map β).left) ≫ B.inclusion.map εc.hom.left =
      B.inclusion.map εx.hom.left ≫ B.inclusion.map k.left :=
    map_comp_eq_map_comp B.inclusion hβnat
  have hkproj : B.inclusion.map k.left ≫ E.inclusion.map (pullback.fst W.obj.hom fg) =
      E.inclusion.map (pullback.fst Wy.obj.hom f) ≫
        E.inclusion.map (pullback.fst W.obj.hom g) :=
    map_comp_eq_map_comp E.inclusion
      (smallEtaleBaseChange_factoredCompIso_hom_app_fst E _ _ _ f g fg hfg W)
  have hεzIso : IsIso εz.hom.left := by
    change IsIso ((Over.forget (q.obj z)).map εz.hom)
    infer_instance
  have hmapScheme :
      B.inclusion.map ((p.map β).left) ≫ B.inclusion.map ((p.map αc).left) =
        B.inclusion.map ((p.map αφ).left) ≫ B.inclusion.map ((p.map αψ).left) := by
    refine (cancel_mono (B.inclusion.map εz.hom.left)).mp ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun m => B.inclusion.map ((p.map β).left) ≫ m) hαcbase').trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun m => m ≫ E.inclusion.map (pullback.fst W.obj.hom fg))
      hβbase).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun m => B.inclusion.map εx.hom.left ≫ m) hkproj).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun m => m ≫ E.inclusion.map (pullback.fst W.obj.hom g))
      hαφbase'.symm).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun m => B.inclusion.map ((p.map αφ).left) ≫ m)
      hαψbase'.symm).trans ?_
    exact (Category.assoc _ _ _).symm
  have hmap : p.map (β ≫ αc) = p.map (αφ ≫ αψ) := by
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    simp only [Functor.map_comp, Over.comp_left]
    exact hmapScheme
  have hfac : (β ≫ αc) ≫ (Fz.inv.obj (jz.obj W)).hom =
      (αφ ≫ αψ) ≫ (Fz.inv.obj (jz.obj W)).hom :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun m => β ≫ m) hαcfac').trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun m => m ≫ (φ ≫ ψ)) hβfac).trans
            ((Category.assoc _ _ _).symm.trans
              ((congrArg (fun m => m ≫ ψ) hαφfac'.symm).trans
                ((Category.assoc _ _ _).trans
                  ((congrArg (fun m => αφ ≫ m) hαψfac'.symm).trans
                    (Category.assoc _ _ _).symm)))))))
  have harrow : β ≫ αc = αφ ≫ αψ :=
    Functor.IsFiberedInGroupoids.hom_eq_of_map_eq_of_comp_eq hp
      (Fz.inv.obj (jz.obj W)).hom hmap hfac
  rw [harrow]

/-- **Stacks 075D (1).** For an étale sheaf on a category fibred in groupoids, the comparison
map of Stacks 06W3 for a composite arrow is the composite of the two comparison maps, under the
canonical identification of successive small étale inverse images. -/
@[stacks 075D "part (1)"]
theorem restrictionInverseImageComparison_comp {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids) {x y z : 𝒳}
    (φ : x ⟶ y) (ψ : y ⟶ z)
    (F : Sheaf (associatedTopology B S hS p (etaleTopology B)) (Type (max (u + 1) t))) :
    ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).sheafPullback
          (Type (max (u + 1) t))
          (SmallEtale.topology E (p.obj y).left.1 (contains_base B E h S hS p y))
          (SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x))).map
        (restrictionInverseImageComparison B E h S hS p hp ψ F) ≫
      restrictionInverseImageComparison B E h S hS p hp φ F =
    (restrictionInverseImageCompIso B E h S hS p φ ψ).hom.app
        (restrictToSmallEtaleSheaf B E h S hS p hp z F) ≫
      restrictionInverseImageComparison B E h S hS p hp (φ ≫ ψ) F := by
  classical
  let Jx := SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x)
  let Jy := SmallEtale.topology E (p.obj y).left.1 (contains_base B E h S hS p y)
  let Jz := SmallEtale.topology E (p.obj z).left.1 (contains_base B E h S hS p z)
  let Gφ := smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)
  let Gψ := smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p ψ)
  let Gc := smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p (φ ≫ ψ))
  let adjφ := Gφ.sheafAdjunctionContinuous (Type (max (u + 1) t)) Jy Jx
  let adjψ := Gψ.sheafAdjunctionContinuous (Type (max (u + 1) t)) Jz Jy
  let adjc := Gc.sheafAdjunctionContinuous (Type (max (u + 1) t)) Jz Jx
  let e := smallEtaleBaseChange_factoredCompIso E _ _ _
    (smallEtaleBaseMorphism B E h S hS p φ) (smallEtaleBaseMorphism B E h S hS p ψ)
    (smallEtaleBaseMorphism B E h S hS p (φ ≫ ψ))
    (smallEtaleBaseMorphism_comp B E h S hS p φ ψ).symm
  let ePush := Functor.sheafPushforwardContinuousComp' e (Type (max (u + 1) t)) Jz Jy Jx
  let ePull := Adjunction.leftAdjointCompIso adjψ adjφ adjc ePush
  let Sx := restrictToSmallEtaleSheaf B E h S hS p hp x F
  let Sy := restrictToSmallEtaleSheaf B E h S hS p hp y F
  let Sz := restrictToSmallEtaleSheaf B E h S hS p hp z F
  let cφ : Sy ⟶ (Gφ.sheafPushforwardContinuous (Type (max (u + 1) t)) Jy Jx).obj Sx :=
    Sheaf.homEquiv.symm (restrictionPushforwardComparison B E h S hS p hp φ F.obj)
  let cψ : Sz ⟶ (Gψ.sheafPushforwardContinuous (Type (max (u + 1) t)) Jz Jy).obj Sy :=
    Sheaf.homEquiv.symm (restrictionPushforwardComparison B E h S hS p hp ψ F.obj)
  let cc : Sz ⟶ (Gc.sheafPushforwardContinuous (Type (max (u + 1) t)) Jz Jx).obj Sx :=
    Sheaf.homEquiv.symm (restrictionPushforwardComparison B E h S hS p hp (φ ≫ ψ) F.obj)
  have he : conjugateEquiv adjc (adjψ.comp adjφ) ePull.hom = ePush.inv := by
    simp [ePull, Adjunction.leftAdjointCompIso]
  have hpush : cψ ≫ (Gψ.sheafPushforwardContinuous (Type (max (u + 1) t)) Jz Jy).map cφ =
      cc ≫ ePush.inv.app Sx := by
    apply Sheaf.homEquiv.injective
    refine NatTrans.ext (funext fun W => ?_)
    have hLHS : (Sheaf.homEquiv (cψ ≫ (Gψ.sheafPushforwardContinuous
          (Type (max (u + 1) t)) Jz Jy).map cφ)).app W =
        (restrictionPushforwardComparison B E h S hS p hp ψ F.obj).app W ≫
          (restrictionPushforwardComparison B E h S hS p hp φ F.obj).app (Opposite.op
            ((smallEtaleBaseChange E
              (smallEtaleBaseMorphism B E h S hS p ψ)).obj W.unop)) := rfl
    have hRHS : (Sheaf.homEquiv (cc ≫ ePush.inv.app Sx)).app W =
        (restrictionPushforwardComparison B E h S hS p hp (φ ≫ ψ) F.obj).app W ≫
          (restrictToSmallEtale B E h S hS p hp x F.obj).map (e.hom.app W.unop).op := by
      have h₁ : (Sheaf.homEquiv (cc ≫ ePush.inv.app Sx)).app W =
          (restrictionPushforwardComparison B E h S hS p hp (φ ≫ ψ) F.obj).app W ≫
            ((restrictToSmallEtale B E h S hS p hp x F.obj).map (e.hom.app W.unop).op ≫
              𝟙 _) := rfl
      rw [h₁, Category.comp_id]
    rw [hLHS, hRHS]
    exact restrictionPushforwardComparison_app_comp B E h S hS p hp φ ψ F.obj W.unop
  apply (adjψ.comp adjφ).homEquiv Sz Sx |>.injective
  change (adjψ.comp adjφ).homEquiv Sz Sx
      ((Gφ.sheafPullback (Type (max (u + 1) t)) Jy Jx).map ((adjψ.homEquiv Sz Sy).symm cψ) ≫
        (adjφ.homEquiv Sy Sx).symm cφ) =
    (adjψ.comp adjφ).homEquiv Sz Sx (ePull.hom.app Sz ≫ (adjc.homEquiv Sz Sx).symm cc)
  rw [comp_homEquiv_symm_comp adjψ adjφ cψ cφ,
    homEquiv_comp_conjugate (adjψ.comp adjφ) adjc ePull ePush he Sz cc]
  exact hpush

end AlgebraicGeometry.Stack

end
