module

public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentStackDiagonalEqualizer
public import StacksFrontier.CategoryTheory.Sites.Stack.IsomPresheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackBaseChange
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackPushout
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeIsomMutualInverse
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackLimitPreserving
public import StacksFrontier.AlgebraicGeometry.Spaces.RestrictSmallerBase
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteria

/-!
# The isomorphism presheaf of `Coh_{X/Y}` over the equalizer (Stacks 08W6, step 4)

Let `x`, `y` be objects of `𝒳 = Coh_{X/Y}` over a scheme `U`, with base maps `g, h : U ⟶ Y`.  The
source's proof of Stacks 08W6 observes that a section of `Isom_𝒳(x, y)` over `a : V ⟶ U` forces
`a` to factor through the equalizer `E` of `g` and `h`, and that over `E` the presheaf
`Isom_𝒳(x, y)` is the relative Isom functor `Isom(F, G)` of Stacks 08K7 of the standing datum of
Stacks 08JT over `E`.  This file carries that identification out.  Given an algebraic space `H`
over `E` whose functor of points over `E` is `Isom(F, G)` — the conclusion of Proposition 08K9 —
the presheaf `Isom_𝒳(x, y)` on the schemes over `U` is isomorphic to the points of `H` over `U`,
which form an algebraic space over `U`.  So Stacks 08W6 needs only the conclusion of 08K9.

## Main definitions

* `CategoryTheory.Functor.CartesianFamily` and `CategoryTheory.Functor.homOverPresheaf`: a
  family of cartesian lifts at an object, and the presheaf of morphisms over the base from those
  lifts; `CategoryTheory.Functor.morPresheafIsoHomOver` identifies it with `Mor(x, y)`.
* `AlgebraicGeometry.Space.CoherentSituation.psi`: the morphism of `Coh_{X/Y}` that a section of
  the relative Isom functor over a common test scheme defines.
* `AlgebraicGeometry.Space.CoherentSituation.pointPresheafIso`: the presheaf of morphisms over the
  base is the presheaf of points of `H`.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.comp_psi`: the morphisms `psi` are natural.
* `AlgebraicGeometry.Space.CoherentSituation.coherentCFG_isAlgebraicSpaceIsomPresheaf` and
  `AlgebraicGeometry.Space.CoherentSituation.coherentCFG_hasRepresentableDiagonal`: **Stacks 08W6,
  granted the conclusion of Proposition 08K9** for the standing data over the equalizers.  No
  declaration here carries `@[stacks 08W6]`: the hypothesis is the conclusion of 08K9.

## References

* [Stacks Project, Tag 08W6](https://stacks.math.columbia.edu/tag/08W6)
* [Stacks Project, Tag 08K9](https://stacks.math.columbia.edu/tag/08K9)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 02ZB](https://stacks.math.columbia.edu/tag/02ZB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

/-! ### Sections of `Mor(x, y)` as morphisms over the base -/

namespace CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

attribute [local implicit_reducible] Fiber Fiber.fiberInclusion

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  (p : 𝒳 ⥤ 𝒮) {U : 𝒮}

/-- **A family of cartesian lifts at `x`**: for every `a : V ⟶ U` of `𝒮/U`, an object `Q a`
over `V` and a strongly cartesian morphism `Q a ⟶ x` over `a`. -/
structure CartesianFamily (x : 𝒳) where
  /-- The source of the lift over `a`. -/
  obj : Over U → 𝒳
  /-- The lift over `a`. -/
  lift : ∀ a : Over U, obj a ⟶ x
  /-- It lies over `a`. -/
  isHomLift : ∀ a : Over U, p.IsHomLift a.hom (lift a)
  /-- It is strongly cartesian. -/
  isStronglyCartesian : ∀ a : Over U, p.IsStronglyCartesian a.hom (lift a)

/-- A composite of lifts lies over the composite of the bases, up to an equality. -/
private lemma isHomLift_comp_of_eq {R S T : 𝒮} {a b c : 𝒳} {f : R ⟶ S} {g : S ⟶ T} {h : R ⟶ T}
    {φ : a ⟶ b} {ψ : b ⟶ c} [p.IsHomLift f φ] [p.IsHomLift g ψ] (e : f ≫ g = h) :
    p.IsHomLift h (φ ≫ ψ) :=
  e ▸ inferInstance

namespace CartesianFamily

variable {p} {x : 𝒳} (Q : CartesianFamily p (U := U) x)

attribute [instance] CartesianFamily.isHomLift CartesianFamily.isStronglyCartesian

/-- The transition `Q a₁ ⟶ Q a₂` over `h.left`, for `h : a₁ ⟶ a₂` in `𝒮/U`. -/
def trans {a₁ a₂ : Over U} (h : a₁ ⟶ a₂) : Q.obj a₁ ⟶ Q.obj a₂ :=
  IsStronglyCartesian.map p a₂.hom (Q.lift a₂) (Over.w h).symm (Q.lift a₁)

/-- The transition `Q.trans h` lies over `h.left`. -/
instance {a₁ a₂ : Over U} (h : a₁ ⟶ a₂) : p.IsHomLift h.left (Q.trans h) := by
  unfold trans
  infer_instance

/-- The transition `Q.trans h` composed with the lift at `a₂` is the lift at `a₁`. -/
@[reassoc (attr := simp)]
lemma trans_lift {a₁ a₂ : Over U} (h : a₁ ⟶ a₂) : Q.trans h ≫ Q.lift a₂ = Q.lift a₁ :=
  IsStronglyCartesian.fac p a₂.hom _ _ _

/-- The transition along an identity is the identity. -/
lemma trans_id (a : Over U) : Q.trans (𝟙 a) = 𝟙 _ := by
  have h : p.IsHomLift (𝟙 a.left) (𝟙 (Q.obj a)) :=
    IsHomLift.id (IsHomLift.domain_eq p a.hom (Q.lift a))
  have : p.IsHomLift (CommaMorphism.left (𝟙 a)) (𝟙 (Q.obj a)) := h
  unfold trans
  exact (IsStronglyCartesian.map_uniq p a.hom (Q.lift a) _ _ _ (Category.id_comp _)).symm

/-- The transition along a composite is the composite of the transitions. -/
lemma trans_comp {a₁ a₂ a₃ : Over U} (h₁ : a₁ ⟶ a₂) (h₂ : a₂ ⟶ a₃) :
    Q.trans (h₁ ≫ h₂) = Q.trans h₁ ≫ Q.trans h₂ := by
  have : p.IsHomLift (h₁ ≫ h₂).left (Q.trans h₁ ≫ Q.trans h₂) := by
    rw [Over.comp_left]
    infer_instance
  exact (IsStronglyCartesian.map_uniq p a₃.hom (Q.lift a₃) _ _ _ (by simp)).symm

/-- The presheaf on `𝒮/U` of the morphisms over the base from the lifts of `Q` into `y`. -/
@[implicit_reducible]
def homOver (y : 𝒳) : (Over U)ᵒᵖ ⥤ Type v₂ where
  obj a := {m : Q.obj a.unop ⟶ y // p.IsHomLift a.unop.hom m}
  map {a₂ a₁} h := ↾fun m => ⟨Q.trans h.unop ≫ m.1, by
    have := m.2
    have h0 : p.IsHomLift (h.unop.left ≫ a₂.unop.hom) (Q.trans h.unop ≫ m.1) := inferInstance
    rwa [Over.w h.unop] at h0⟩
  map_id a := by
    ext m
    exact (congrArg (· ≫ m.1) (Q.trans_id a.unop)).trans (Category.id_comp m.1)
  map_comp {a₃ a₂ a₁} h₂ h₁ := by
    ext m
    exact (congrArg (· ≫ m.1) (Q.trans_comp h₁.unop h₂.unop)).trans (Category.assoc _ _ _)

/-- The comparison `Q a ⟶ Q' a` over the identity of two families of cartesian lifts. -/
def compare (Q' : CartesianFamily p (U := U) x) (a : Over U) : Q.obj a ⟶ Q'.obj a :=
  IsStronglyCartesian.map p a.hom (Q'.lift a) (Category.id_comp a.hom).symm (Q.lift a)

/-- The comparison `Q.compare Q' a` lies over the identity of `a.left`. -/
instance (Q' : CartesianFamily p (U := U) x) (a : Over U) :
    p.IsHomLift (𝟙 a.left) (Q.compare Q' a) := by
  unfold compare
  infer_instance

/-- The comparison `Q.compare Q' a` composed with the lift of `Q'` at `a` is the lift of `Q`. -/
@[reassoc (attr := simp)]
lemma compare_lift (Q' : CartesianFamily p (U := U) x) (a : Over U) :
    Q.compare Q' a ≫ Q'.lift a = Q.lift a :=
  IsStronglyCartesian.fac p a.hom _ _ _

/-- The comparisons of `Q` with `Q'` and of `Q'` with `Q` are mutually inverse. -/
lemma compare_compare (Q' : CartesianFamily p (U := U) x) (a : Over U) :
    Q.compare Q' a ≫ Q'.compare Q a = 𝟙 _ := by
  have h1 : p.IsHomLift (𝟙 a.left) (Q.compare Q' a ≫ Q'.compare Q a) :=
    isHomLift_comp_of_eq p (Category.id_comp _)
  have h2 : p.IsHomLift (𝟙 a.left) (𝟙 (Q.obj a)) :=
    IsHomLift.id (IsHomLift.domain_eq p a.hom (Q.lift a))
  exact IsStronglyCartesian.ext p a.hom (Q.lift a) (𝟙 a.left) (by simp)

/-- The comparisons commute with the transitions. -/
lemma compare_trans (Q' : CartesianFamily p (U := U) x) {a₁ a₂ : Over U} (h : a₁ ⟶ a₂) :
    Q.compare Q' a₁ ≫ Q'.trans h = Q.trans h ≫ Q.compare Q' a₂ := by
  have h1 : p.IsHomLift h.left (Q.compare Q' a₁ ≫ Q'.trans h) :=
    isHomLift_comp_of_eq p (Category.id_comp _)
  have h2 : p.IsHomLift h.left (Q.trans h ≫ Q.compare Q' a₂) :=
    isHomLift_comp_of_eq p (Category.comp_id _)
  exact IsStronglyCartesian.ext p a₂.hom (Q'.lift a₂) h.left (by simp)

/-- **The presheaf of morphisms over the base does not depend on the family of cartesian
lifts.** -/
def homOverIso (Q' : CartesianFamily p (U := U) x) (y : 𝒳) : Q.homOver y ≅ Q'.homOver y :=
  NatIso.ofComponents (fun a => {
      hom := ↾fun m => ⟨Q'.compare Q a.unop ≫ m.1, by
        have := m.2
        have h0 : p.IsHomLift (𝟙 a.unop.left ≫ a.unop.hom) (Q'.compare Q a.unop ≫ m.1) :=
          inferInstance
        rwa [Category.id_comp] at h0⟩
      inv := ↾fun m => ⟨Q.compare Q' a.unop ≫ m.1, by
        have := m.2
        have h0 : p.IsHomLift (𝟙 a.unop.left ≫ a.unop.hom) (Q.compare Q' a.unop ≫ m.1) :=
          inferInstance
        rwa [Category.id_comp] at h0⟩
      hom_inv_id := by
        ext m
        exact Subtype.ext ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ m.1)
          (Q.compare_compare Q' a.unop)).trans (Category.id_comp m.1)))
      inv_hom_id := by
        ext m
        exact Subtype.ext ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ m.1)
          (Q'.compare_compare Q a.unop)).trans (Category.id_comp m.1))) })
    (fun {a₂ a₁} h => by
      ext m
      apply Subtype.ext
      change Q'.compare Q a₁.unop ≫ Q.trans h.unop ≫ m.1 =
        Q'.trans h.unop ≫ Q'.compare Q a₂.unop ≫ m.1
      rw [← Category.assoc, ← Category.assoc, Q'.compare_trans Q h.unop])

end CartesianFamily

variable [p.IsFibered]

/-- The chosen pullbacks of an object of the fibre, as a family of cartesian lifts. -/
abbrev chosenCartesianFamily (x : p.Fiber U) : CartesianFamily p (U := U) x.1 where
  obj a := (pullbackFiber p x a.hom).1
  lift a := IsPreFibered.pullbackMap x.2 a.hom
  isHomLift _ := inferInstance
  isStronglyCartesian _ := inferInstance

/-- The presheaf on `𝒮/U` of the morphisms from the chosen pullbacks of `x` to `y` lying over the
structure morphism. -/
abbrev homOverPresheaf (x y : p.Fiber U) : (Over U)ᵒᵖ ⥤ Type v₂ :=
  (chosenCartesianFamily p x).homOver y.1

/-- **The sections of `Mor(x, y)` are the morphisms over the base into `y`.**  A morphism
`f^* x ⟶ f^* y` of the fibre corresponds to its composite with the chosen cartesian lift of `f`
at `y`. -/
def morPresheafToHomOver (x y : p.Fiber U) : morPresheaf p x y ⟶ homOverPresheaf p x y where
  app g := ↾fun m => ⟨Fiber.fiberInclusion.map m ≫ IsPreFibered.pullbackMap y.2 g.unop.hom, by
    have h0 : p.IsHomLift (𝟙 g.unop.left ≫ g.unop.hom)
        (Fiber.fiberInclusion.map m ≫ IsPreFibered.pullbackMap y.2 g.unop.hom) := inferInstance
    rwa [Category.id_comp] at h0⟩
  naturality {g₂ g₁} h := by
    ext m
    refine Subtype.ext ?_
    change Fiber.fiberInclusion.map (morRestrict p x y h.unop m) ≫
        IsPreFibered.pullbackMap y.2 g₁.unop.hom =
      pullbackFiberMap p x h.unop ≫ Fiber.fiberInclusion.map m ≫
        IsPreFibered.pullbackMap y.2 g₂.unop.hom
    exact morRestrict_fac p x y h.unop m

/-- The morphism `morPresheafToHomOver p x y` is an isomorphism. -/
instance isIso_morPresheafToHomOver (x y : p.Fiber U) :
    IsIso (morPresheafToHomOver p x y) := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun g => ?_
  rw [isIso_iff_bijective]
  refine ⟨fun m n hmn => ?_, fun n => ?_⟩
  · have h := congrArg Subtype.val hmn
    change Fiber.fiberInclusion.map m ≫ IsPreFibered.pullbackMap y.2 g.unop.hom =
      Fiber.fiberInclusion.map n ≫ IsPreFibered.pullbackMap y.2 g.unop.hom at h
    exact Fiber.hom_ext (IsCartesian.map_uniq p g.unop.hom (IsPreFibered.pullbackMap y.2 g.unop.hom)
      _ _ h |>.trans (IsCartesian.map_uniq p g.unop.hom (IsPreFibered.pullbackMap y.2 g.unop.hom)
      _ _ rfl).symm)
  · obtain ⟨n, hn⟩ := n
    refine ⟨⟨IsCartesian.map p g.unop.hom (IsPreFibered.pullbackMap y.2 g.unop.hom) n,
      IsCartesian.map_isHomLift p g.unop.hom (IsPreFibered.pullbackMap y.2 g.unop.hom) n⟩,
      Subtype.ext ?_⟩
    exact IsCartesian.fac p g.unop.hom (IsPreFibered.pullbackMap y.2 g.unop.hom) n

/-- `Mor(x, y)` is isomorphic to the presheaf of morphisms over the base into `y`. -/
def morPresheafIsoHomOver (x y : p.Fiber U) : morPresheaf p x y ≅ homOverPresheaf p x y :=
  asIso (morPresheafToHomOver p x y)

end CategoryTheory.Functor


/-- Cancelling a pair of mutually inverse identifications in a composite. -/
theorem CategoryTheory.eqToHom_comp_eqToHom_aux {C : Type*} [Category* C] {X Y Z Z' W W' : C}
    (e₁ : X = Y) (f : Y ⟶ Z) (e₂ : Z = Z') (e₃ : Z' = Z) (g : Z ⟶ W) (k : W ⟶ W') :
    (eqToHom e₁ ≫ f ≫ eqToHom e₂) ≫ (eqToHom e₃ ≫ g) ≫ k = eqToHom e₁ ≫ (f ≫ g) ≫ k := by
  subst e₂
  simp

/-- Reassociating a factorization behind an identification. -/
theorem CategoryTheory.eqToHom_comp_comp_aux {C : Type*} [Category* C] {X X' Y Z W : C}
    (e : X = X') (κ : X' ⟶ Y) (ι : Y ⟶ Z) (a : X' ⟶ Z) (F : Z ⟶ W) (h : κ ≫ ι = a) :
    (eqToHom e ≫ κ) ≫ ι ≫ F = eqToHom e ≫ a ≫ F := by
  subst h
  simp

/-- Cancelling an isomorphism after the inverses of two isomorphisms. -/
theorem CategoryTheory.inv_comp_cancel {C : Type*} [Category* C] {X Y Z : C} (f g : X ⟶ Y)
    (k : X ⟶ Z) (hf : IsIso f) (hg : IsIso g) (hk : IsIso k) (h : inv f ≫ k = inv g ≫ k) :
    f = g := by
  have h' : inv f = inv g := by simpa using congrArg (· ≫ inv k) h
  exact IsIso.inv_eq_inv.1 h'

/-! ### The concrete cartesian lifts of `Coh_{X/Y}` -/

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace CoherentSituation

variable (D : CoherentSituation B S hS)

/-- The category structure of `Coh_{X/Y}`, as a local instance. -/
abbrev cohCategory : Category.{u + 1} (CoherentObject D) := D.categoryData.category

attribute [local instance] cohCategory

/-- The projection of `Coh_{X/Y}` to the site is fibred, as a local instance. -/
abbrev cohIsFibered : (coherentSiteProjection D.categoryData).IsFibered :=
  D.isFiberedInGroupoids_siteProjection.isFibered

attribute [local instance] cohIsFibered

variable {D} {U : BigFppfOver B S hS}

/-- The comparison of Stacks 03LU for `τ ≫ c₂`, followed by the identification along
`τ ≫ c₂ = c₁`, is the comparison for the presentation `X_τ ≫ X_{c₂} = X_{c₁}`. -/
theorem compComparison_inv_relativeMapComparison {T₀ T₁ T₂ : SchemesOver D.Y} (τ : T₀ ⟶ T₁)
    (c₂ : T₁ ⟶ T₂) {c₁ : T₀ ⟶ T₂} (hw : τ ≫ c₂ = c₁)
    (h : D.relativeMap τ ≫ D.relativeMap c₂ = D.relativeMap c₁)
    (K : Modules.{u, u} B S hS (D.space T₂).1 (D.space T₂).2) :
    (D.compComparison τ c₂).inv.app K ≫ (D.relativeMapComparison hw).hom.app K =
      (modulePullbackTriangle B S hS h).inv.app K := by
  subst hw
  have e : D.compComparison τ c₂ = modulePullbackTriangle B S hS h := by
    unfold compComparison
    congr 1
  rw [relativeMapComparison_hom_app, eqToHom_refl, Category.comp_id, e]

/-- The computation behind `AlgebraicGeometry.Space.CoherentSituation.sigma_comp`, with the
composite written out. -/
theorem sigma_comp_aux {x y z₁ z₂ : CoherentObject D} (ρ : CoherentHom z₁ z₂)
    (κ₂ : CoherentHom z₂ x) (m₂ : CoherentHom z₂ y)
    (hτ : D.relativeMap ρ.base ≫ D.relativeMap κ₂.base = D.relativeMap (ρ.base ≫ κ₂.base))
    [IsIso (Functor.fibreComp (D.compComparison ρ.base m₂.base) ρ.fibre m₂.fibre)] :
    Functor.fibreComp (D.compComparison ρ.base κ₂.base) ρ.fibre κ₂.fibre ≫
        inv (Functor.fibreComp (D.compComparison ρ.base m₂.base) ρ.fibre m₂.fibre) =
      secRestrict (D.relativeMap ρ.base) hτ (relativeMap_comp D ρ.base m₂.base).symm
        (κ₂.fibre ≫ inv m₂.fibre) := by
  have e₁ : D.compComparison ρ.base κ₂.base = modulePullbackTriangle B S hS hτ := by
    unfold compComparison
    congr 1
  have e₂ : D.compComparison ρ.base m₂.base =
      modulePullbackTriangle B S hS (relativeMap_comp D ρ.base m₂.base).symm := by
    unfold compComparison
    congr 1
  simp only [e₁, e₂, Functor.fibreComp, secRestrict, CategoryTheory.Functor.secMap,
    IsIso.inv_comp, Category.assoc, IsIso.hom_inv_id_assoc, Functor.map_comp, Functor.map_inv]
  rw [IsIso.inv_eq_of_hom_inv_id (Iso.hom_inv_id_app
    (modulePullbackTriangle B S hS (relativeMap_comp D ρ.base m₂.base).symm) y.F)]

/-- **The section of a morphism, read through a cartesian lift, restricts along composition.**
For a morphism `m : z ⟶ y` of `Coh_{X/Y}` and a morphism `κ : z ⟶ x`, write `σ_κ(m)` for the
homomorphism `X_κ^* F_x ⟶ F_z ⟶ X_m^* F_y`.  Then `σ_{ρ ≫ κ₂}(ρ ≫ m₂)` is the restriction of
`σ_{κ₂}(m₂)` along `X_ρ`. -/
theorem sigma_comp {x y z₁ z₂ : CoherentObject D} (ρ : CoherentHom z₁ z₂) (κ₂ : CoherentHom z₂ x)
    (m₂ : CoherentHom z₂ y)
    (hτ : D.relativeMap ρ.base ≫ D.relativeMap κ₂.base = D.relativeMap (ρ.base ≫ κ₂.base)) :
    (ρ.comp κ₂).fibre ≫ inv (ρ.comp m₂).fibre =
      secRestrict (D.relativeMap ρ.base) hτ (relativeMap_comp D ρ.base m₂.base).symm
        (κ₂.fibre ≫ inv m₂.fibre) := by
  have : IsIso (Functor.fibreComp (D.compComparison ρ.base m₂.base) ρ.fibre m₂.fibre) :=
    (ρ.comp m₂).isIso_fibre
  exact sigma_comp_aux ρ κ₂ m₂ hτ

/-- Two morphisms of `Coh_{X/Y}` are equal once their base maps are and their module comparisons
agree through the identification of the inverse images along the two equal base maps. -/
theorem _root_.AlgebraicGeometry.Space.CoherentHom.eq_of_fibre_eq {A₁ A₂ : CoherentObject D}
    (m n : CoherentHom A₁ A₂) (hb : m.base = n.base)
    (hf : m.fibre = (D.relativeMapComparison hb).hom.app A₂.F ≫ n.fibre) : m = n := by
  obtain ⟨mb, mf, mi⟩ := m
  obtain ⟨nb, nf, ni⟩ := n
  change mb = nb at hb
  subst hb
  change mf = _ ≫ nf at hf
  rw [relativeMapComparison_hom_app, eqToHom_refl, Category.id_comp] at hf
  subst hf
  rfl

/-! ### Base changes to a scheme over a common test scheme -/

section Common

variable {A : CoherentObject D} (hA : A.T.left = U) {T : SchemesOver D.Y} (ι : T.left ⟶ U)
  (tA : T ⟶ A.T) (htA : tA.left = ι ≫ eqToHom hA.symm)
  {z : CoherentObject D} {V : BigFppfOver B S hS} (hz : z.T.left = V) (κc : CoherentHom z A)
  {a : V ⟶ U} (hκ : κc.base.left = eqToHom hz ≫ a ≫ eqToHom hA.symm)

include htA hκ in
/-- The composite of `eqToHom hz ≫ κ'` with the structure morphism of `T` is that of `z.T`. -/
theorem zToCommon_w (κ' : V ⟶ T.left) (hκ' : κ' ≫ ι = a) :
    (schemeSpaceFunctor B S hS).map (eqToHom hz ≫ κ') ≫ T.hom = z.T.hom := by
  rw [← CostructuredArrow.w κc.base, ← CostructuredArrow.w tA, htA, hκ, ← hκ',
    ← Functor.map_comp_assoc]
  simp only [Category.assoc]

/-- The morphism of test schemes from `z.T` to `T` given by a factorization `κ'` of `a` through
`ι`. -/
def zToCommon (κ' : V ⟶ T.left) (hκ' : κ' ≫ ι = a) : z.T ⟶ T :=
  CostructuredArrow.homMk (eqToHom hz ≫ κ') (zToCommon_w hA ι tA htA hz κc hκ κ' hκ')

/-- The underlying morphism of `zToCommon` is `eqToHom hz ≫ κ'`. -/
@[simp]
theorem zToCommon_left (κ' : V ⟶ T.left) (hκ' : κ' ≫ ι = a) :
    (zToCommon hA ι tA htA hz κc hκ κ' hκ').left = eqToHom hz ≫ κ' :=
  rfl

/-- The base change of `D` along `zToCommon` is a pullback of `D.projection T` along `κ'`. -/
theorem isPullback_zToCommon (κ' : V ⟶ T.left) (hκ' : κ' ≫ ι = a) :
    IsPullback (D.relativeMap (zToCommon hA ι tA htA hz κc hκ κ' hκ'))
      (D.projection z.T ≫ (schemeSpaceFunctor B S hS).map (eqToHom hz)) (D.projection T)
      ((schemeSpaceFunctor B S hS).map κ') :=
  (isPullback_baseChangeMap D.f (zToCommon hA ι tA htA hz κc hκ κ' hκ')).of_iso (Iso.refl _)
    (Iso.refl _) ((schemeSpaceFunctor B S hS).mapIso (eqToIso hz)) (Iso.refl _) (by simp)
    (by simp) (by simp)
    (by simp only [zToCommon_left, Functor.map_comp, Iso.refl_hom, Category.comp_id,
      Functor.mapIso_hom, eqToIso.hom])

/-- **The comparison of the two base changes**: `X_{z.T}` and `X_T ×_T V`. -/
def zSpaceIso (κ' : V ⟶ T.left) (hκ' : κ' ≫ ι = a) :
    D.space z.T ≅
      baseChangeSpace (D.projection T)
        (CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map κ')) :=
  (isPullback_zToCommon hA ι tA htA hz κc hκ κ' hκ').isoIsPullback _ _
    (AlgebraicSpaces.isPullback_fiberProduct B S hS (D.projection T) _)

/-- The comparison `zSpaceIso` followed by the projection to `X_T` is the relative map of
`zToCommon`. -/
theorem zSpaceIso_hom_projection (κ' : V ⟶ T.left) (hκ' : κ' ≫ ι = a) :
    (zSpaceIso hA ι tA htA hz κc hκ κ' hκ').hom ≫
        baseChangeProjection (D.projection T)
          (CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map κ')) =
      D.relativeMap (zToCommon hA ι tA htA hz κc hκ κ' hκ') :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- The comparison `zSpaceIso` followed by the projection to `V` is the projection of `X_{z.T}`. -/
theorem zSpaceIso_hom_inclusion (κ' : V ⟶ T.left) (hκ' : κ' ≫ ι = a) :
    (zSpaceIso hA ι tA htA hz κc hκ κ' hκ').hom ≫
        baseChangeInclusion (D.projection T)
          (CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map κ')) =
      D.projection z.T ≫ (schemeSpaceFunctor B S hS).map (eqToHom hz) :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

/-- The comparison followed by the projection to `X_T` and `X_t`, for a morphism of test schemes
`t : T ⟶ C`, is the morphism of base changes of any `t'` whose underlying morphism is the
factorization followed by `t`. -/
theorem zSpaceIso_hom_comp (κ' : V ⟶ T.left) (hκ' : κ' ≫ ι = a) {C : SchemesOver D.Y}
    (t : T ⟶ C) (t' : z.T ⟶ C) (ht : t'.left = (eqToHom hz ≫ κ') ≫ t.left) :
    (zSpaceIso hA ι tA htA hz κc hκ κ' hκ').hom ≫
        (baseChangeProjection (D.projection T)
          (CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map κ')) ≫ D.relativeMap t) =
      D.relativeMap t' := by
  rw [← Category.assoc, zSpaceIso_hom_projection, ← relativeMap_comp]
  congr 1
  exact CostructuredArrow.hom_ext _ _ ht.symm

variable (T) in
/-- **The standing datum of Stacks 08JT over a test scheme.**  Its source is the base change
`X_T`, its base is `T`, and its modules are two quasi-coherent modules on `X_T`. -/
abbrev commonHomSituation (F G : Modules.{u, u} B S hS (D.space T).1 (D.space T).2)
    (hF : F.IsQuasicoherentOnSite) (hG : G.IsQuasicoherentOnSite) : HomSituation B S hS where
  X := D.space T
  base := (schemeSpaceFunctor B S hS).obj T.left
  f := D.projection T
  F := F
  G := G
  quasicoherent_F := hF
  quasicoherent_G := hG

variable {A' : CoherentObject D} {hA' : A'.T.left = U} (tA' : T ⟶ A'.T)
  (htA' : tA'.left = ι ≫ eqToHom hA'.symm)

/-- **The standing datum of Stacks 08JT over `T` for the pullbacks of the modules of `A` and
`A'`.** -/
abbrev pairHomSituation : HomSituation B S hS :=
  commonHomSituation T ((modulePullback B S hS (D.relativeMap tA)).obj A.F)
    ((modulePullback B S hS (D.relativeMap tA')).obj A'.F)
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ A.F A.quasicoherent)
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ A'.F A'.quasicoherent)

/-- The test scheme over `T` of a morphism `κ' : V ⟶ T`. -/
abbrev commonTest {V : BigFppfOver B S hS} (κ' : V ⟶ T.left) :
    (pairHomSituation tA tA').SchemesOver :=
  CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map κ')

include hκ htA in
/-- The base morphism of `κc` factors as `(eqToHom hz ≫ κ') ≫ tA.left`. -/
theorem zToCommon_eq_left (κ' : V ⟶ T.left) (hκ' : κ' ≫ ι = a) :
    κc.base.left = (eqToHom hz ≫ κ') ≫ tA.left := by
  rw [hκ, htA, ← hκ']
  simp only [Category.assoc]

/-- **The homomorphism of modules on `X_{z.T}` that a section of the relative Isom functor
defines**: the section, read on `X_T ×_T V` through the comparisons of Stacks 03LU, restricted to
`X_{z.T}` along the comparison of the two base changes.  The base map `b` of the target is any
morphism whose base change is the comparison followed by `X_T ×_T V ⟶ X_T ⟶ X_{A'.T}`. -/
def psiSec (κ' : V ⟶ T.left) (hκ' : κ' ≫ ι = a)
    (u : ((pairHomSituation tA tA').isomFunctor).obj (Opposite.op (commonTest tA tA' κ')))
    (b : z.T ⟶ A'.T)
    (hb : (zSpaceIso hA ι tA htA hz κc hκ κ' hκ').hom ≫
      (baseChangeProjection (D.projection T)
        (CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map κ')) ≫ D.relativeMap tA') =
      D.relativeMap b) :
    (modulePullback B S hS (D.relativeMap κc.base)).obj A.F ⟶
      (modulePullback B S hS (D.relativeMap b)).obj A'.F :=
  secRestrict (zSpaceIso hA ι tA htA hz κc hκ κ' hκ').hom
    (zSpaceIso_hom_comp hA ι tA htA hz κc hκ κ' hκ' tA κc.base
      (zToCommon_eq_left hA ι tA htA hz κc hκ κ' hκ'))
    hb
    (secPush _ (D.relativeMap tA) _ (D.relativeMap tA')
      ((pairHomSituation tA tA').toModuleHom u.1))

/-- The homomorphism `psiSec` of a section of the relative Isom functor is an isomorphism. -/
instance isIso_psiSec (κ' : V ⟶ T.left) (hκ' : κ' ≫ ι = a)
    (u : ((pairHomSituation tA tA').isomFunctor).obj (Opposite.op (commonTest tA tA' κ')))
    (b : z.T ⟶ A'.T)
    (hb : (zSpaceIso hA ι tA htA hz κc hκ κ' hκ').hom ≫
      (baseChangeProjection (D.projection T)
        (CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map κ')) ≫ D.relativeMap tA') =
      D.relativeMap b) :
    IsIso (psiSec hA ι tA htA hz κc hκ tA' κ' hκ' u b hb) := by
  have : IsIso ((pairHomSituation tA tA').toModuleHom u.1) := u.2
  unfold psiSec
  infer_instance

/-- **The morphism of `Coh_{X/Y}` that a section of the relative Isom functor defines.**  For a
cartesian lift `κc : z ⟶ A` over `a : V ⟶ U`, a factorization `κ'` of `a` through `ι : T ⟶ U`
and an isomorphism `u : F_V ≅ G_V` of the standing datum of Stacks 08JT over `T`, the morphism
`z ⟶ A'` with base map `b`, any morphism equal to `z.T ⟶ T ⟶ A'.T`. -/
def psi (κ' : V ⟶ T.left) (hκ' : κ' ≫ ι = a)
    (u : ((pairHomSituation tA tA').isomFunctor).obj (Opposite.op (commonTest tA tA' κ')))
    (b : z.T ⟶ A'.T)
    (hb : (zSpaceIso hA ι tA htA hz κc hκ κ' hκ').hom ≫
      (baseChangeProjection (D.projection T)
        (CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map κ')) ≫ D.relativeMap tA') =
      D.relativeMap b) :
    CoherentHom z A' where
  base := b
  fibre := inv (psiSec hA ι tA htA hz κc hκ tA' κ' hκ' u b hb) ≫ κc.fibre
  isIso_fibre := inferInstance

/-- **The section of `psi` read through the cartesian lift is the homomorphism it was built
from.** -/
theorem fibre_inv_psi (κ' : V ⟶ T.left) (hκ' : κ' ≫ ι = a)
    (u : ((pairHomSituation tA tA').isomFunctor).obj (Opposite.op (commonTest tA tA' κ')))
    (b : z.T ⟶ A'.T)
    (hb : (zSpaceIso hA ι tA htA hz κc hκ κ' hκ').hom ≫
      (baseChangeProjection (D.projection T)
        (CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map κ')) ≫ D.relativeMap tA') =
      D.relativeMap b) :
    κc.fibre ≫ inv (psi hA ι tA htA hz κc hκ tA' κ' hκ' u b hb).fibre =
      psiSec hA ι tA htA hz κc hκ tA' κ' hκ' u b hb := by
  change κc.fibre ≫ inv (inv (psiSec hA ι tA htA hz κc hκ tA' κ' hκ' u b hb) ≫ κc.fibre) = _
  simp

/-- Two morphisms of `Coh_{X/Y}` out of `z` with equal base maps are equal once their sections,
read through a morphism `κ : z ⟶ A`, agree through the identification of the inverse images. -/
theorem eq_of_sigma {A₂ : CoherentObject D} (κ : CoherentHom z A) (m n : CoherentHom z A₂)
    (hb : m.base = n.base)
    (h : (κ.fibre ≫ inv m.fibre) ≫ (D.relativeMapComparison hb).hom.app A₂.F =
      κ.fibre ≫ inv n.fibre) : m = n := by
  refine CoherentHom.eq_of_fibre_eq _ _ hb ?_
  have h' : inv m.fibre ≫ (D.relativeMapComparison hb).hom.app A₂.F = inv n.fibre := by
    simpa only [Category.assoc, IsIso.inv_hom_id_assoc] using congrArg (inv κ.fibre ≫ ·) h
  calc m.fibre = m.fibre ≫ inv n.fibre ≫ n.fibre := by simp
    _ = m.fibre ≫ (inv m.fibre ≫ (D.relativeMapComparison hb).hom.app A₂.F) ≫ n.fibre := by
      rw [h']
    _ = _ := by simp

/-- The map `u ↦ psiSec … u b hb` is injective. -/
theorem psiSec_injective (κ' : V ⟶ T.left) (hκ' : κ' ≫ ι = a) (b : z.T ⟶ A'.T)
    (hb : (zSpaceIso hA ι tA htA hz κc hκ κ' hκ').hom ≫
      (baseChangeProjection (D.projection T)
        (CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map κ')) ≫ D.relativeMap tA') =
      D.relativeMap b) :
    Function.Injective (fun u => psiSec hA ι tA htA hz κc hκ tA' κ' hκ' u b hb) := by
  intro u₁ u₂ h
  have hFF := ((modulePushforwardCoherence B S hS).modulePullbackEquivalence
    (zSpaceIso hA ι tA htA hz κc hκ κ' hκ')).fullyFaithfulFunctor
  have h₁ := (CategoryTheory.Functor.secMap_bijective _ _ hFF).1 h
  have h₂ := (secPush_bijective _ _ _ _).1 h₁
  exact Subtype.ext h₂

/-- Every isomorphism of the modules is `psiSec … u b hb` for some section `u` of the relative
Isom functor. -/
theorem exists_psiSec_eq (κ' : V ⟶ T.left) (hκ' : κ' ≫ ι = a) (b : z.T ⟶ A'.T)
    (hb : (zSpaceIso hA ι tA htA hz κc hκ κ' hκ').hom ≫
      (baseChangeProjection (D.projection T)
        (CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map κ')) ≫ D.relativeMap tA') =
      D.relativeMap b)
    (t : (modulePullback B S hS (D.relativeMap κc.base)).obj A.F ⟶
      (modulePullback B S hS (D.relativeMap b)).obj A'.F) [IsIso t] :
    ∃ u, psiSec hA ι tA htA hz κc hκ tA' κ' hκ' u b hb = t := by
  have hFF := ((modulePushforwardCoherence B S hS).modulePullbackEquivalence
    (zSpaceIso hA ι tA htA hz κc hκ κ' hκ')).fullyFaithfulFunctor
  obtain ⟨w, hw⟩ := (CategoryTheory.Functor.secMap_bijective (modulePullbackTriangle B S hS
    (zSpaceIso_hom_comp hA ι tA htA hz κc hκ κ' hκ' tA κc.base
      (zToCommon_eq_left hA ι tA htA hz κc hκ κ' hκ'))) (modulePullbackTriangle B S hS hb) hFF).2 t
  obtain ⟨v, hv⟩ := (secPush_bijective _ (D.relativeMap tA) _ (D.relativeMap tA')).2 w
  have : IsIso (CategoryTheory.Functor.secMap (modulePullbackTriangle B S hS
    (zSpaceIso_hom_comp hA ι tA htA hz κc hκ κ' hκ' tA κc.base
      (zToCommon_eq_left hA ι tA htA hz κc hκ κ' hκ'))) (modulePullbackTriangle B S hS hb) w) := by
    rw [hw]
    infer_instance
  have : IsIso w := CategoryTheory.Functor.isIso_of_isIso_secMap (modulePullbackTriangle B S hS
    (zSpaceIso_hom_comp hA ι tA htA hz κc hκ κ' hκ' tA κc.base
      (zToCommon_eq_left hA ι tA htA hz κc hκ κ' hκ'))) (modulePullbackTriangle B S hS hb) hFF w
  have : IsIso (secPush _ (D.relativeMap tA) _ (D.relativeMap tA') v) := by
    rw [hv]
    infer_instance
  have : IsIso v := isIso_of_isIso_secPush _ _ _ _ v
  refine ⟨⟨v, this⟩, ?_⟩
  change CategoryTheory.Functor.secMap _ _
    (secPush _ (D.relativeMap tA) _ (D.relativeMap tA') v) = t
  rw [hv, hw]

/-- A morphism of `Coh_{X/Y}` out of `z` is the morphism `psi` of the section of the relative Isom
functor whose homomorphism is its section through the cartesian lift. -/
theorem psi_eq_of_psiSec_eq (κ' : V ⟶ T.left) (hκ' : κ' ≫ ι = a) (mb : z.T ⟶ A'.T)
    (mf : (modulePullback B S hS (D.relativeMap mb)).obj A'.F ⟶ z.F) (mi : IsIso mf)
    (hb : (zSpaceIso hA ι tA htA hz κc hκ κ' hκ').hom ≫
      (baseChangeProjection (D.projection T)
        (CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map κ')) ≫ D.relativeMap tA') =
      D.relativeMap mb)
    (u : ((pairHomSituation tA tA').isomFunctor).obj (Opposite.op (commonTest tA tA' κ')))
    (hu : psiSec hA ι tA htA hz κc hκ tA' κ' hκ' u mb hb = κc.fibre ≫ inv mf) :
    psi hA ι tA htA hz κc hκ tA' κ' hκ' u mb hb = ⟨mb, mf, mi⟩ := by
  have : inv (psiSec hA ι tA htA hz κc hκ tA' κ' hκ' u mb hb) ≫ κc.fibre = mf := by
    rw [IsIso.inv_comp_eq, hu, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  unfold psi
  congr

/-- `psi` depends on its data only through their values. -/
theorem psi_congr {κc₁ κc₂ : CoherentHom z A} (e₁ : κc₁ = κc₂)
    (hκ₁ : κc₁.base.left = eqToHom hz ≫ a ≫ eqToHom hA.symm)
    (hκ₂ : κc₂.base.left = eqToHom hz ≫ a ≫ eqToHom hA.symm)
    {κ'₁ κ'₂ : V ⟶ T.left} (e₂ : κ'₁ = κ'₂) (hκ'₁ : κ'₁ ≫ ι = a) (hκ'₂ : κ'₂ ≫ ι = a)
    (u₁ : ((pairHomSituation tA tA').isomFunctor).obj (Opposite.op (commonTest tA tA' κ'₁)))
    (u₂ : ((pairHomSituation tA tA').isomFunctor).obj (Opposite.op (commonTest tA tA' κ'₂)))
    (e₄ : HEq u₁ u₂) {b₁ b₂ : z.T ⟶ A'.T} (e₃ : b₁ = b₂)
    (hb₁ : (zSpaceIso hA ι tA htA hz κc₁ hκ₁ κ'₁ hκ'₁).hom ≫
      (baseChangeProjection (D.projection T)
        (CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map κ'₁)) ≫ D.relativeMap tA') =
      D.relativeMap b₁)
    (hb₂ : (zSpaceIso hA ι tA htA hz κc₂ hκ₂ κ'₂ hκ'₂).hom ≫
      (baseChangeProjection (D.projection T)
        (CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map κ'₂)) ≫ D.relativeMap tA') =
      D.relativeMap b₂) :
    psi hA ι tA htA hz κc₁ hκ₁ tA' κ'₁ hκ'₁ u₁ b₁ hb₁ =
      psi hA ι tA htA hz κc₂ hκ₂ tA' κ'₂ hκ'₂ u₂ b₂ hb₂ := by
  subst e₁ e₂ e₃
  cases e₄
  rfl

/-- Two morphisms of `Coh_{X/Y}` out of `z` with the same base map are equal once their sections,
read through a morphism `κ : z ⟶ A`, agree. -/
theorem eq_of_sigma_same {A₂ : CoherentObject D} (κ : CoherentHom z A) (b : z.T ⟶ A₂.T)
    (fm fn : (modulePullback B S hS (D.relativeMap b)).obj A₂.F ⟶ z.F) (im : IsIso fm)
    (in' : IsIso fn) (h : κ.fibre ≫ inv fm = κ.fibre ≫ inv fn) :
    (⟨b, fm, im⟩ : CoherentHom z A₂) = ⟨b, fn, in'⟩ := by
  refine eq_of_sigma κ ⟨b, fm, im⟩ ⟨b, fn, in'⟩ rfl ?_
  simpa [relativeMapComparison_hom_app] using h

end Common

/-! ### Naturality -/

section Naturality

variable {A : CoherentObject D} (hA : A.T.left = U) {T : SchemesOver D.Y} (ι : T.left ⟶ U)
  (tA : T ⟶ A.T) (htA : tA.left = ι ≫ eqToHom hA.symm) {A' : CoherentObject D}
  (tA' : T ⟶ A'.T)

/-- The morphism of test schemes over `T` induced by `hl : V₁ ⟶ V₂`. -/
abbrev commonTestMap {V₁ V₂ : BigFppfOver B S hS} (hl : V₁ ⟶ V₂) (κ' : V₂ ⟶ T.left) :
    commonTest tA tA' (hl ≫ κ') ⟶ commonTest tA tA' κ' :=
  CostructuredArrow.homMk hl ((schemeSpaceFunctor B S hS).map_comp hl κ').symm

/-- **The comparisons of base changes are natural.** -/
theorem zSpaceIso_naturality {z₁ z₂ : CoherentObject D} {V₁ V₂ : BigFppfOver B S hS}
    (hz₁ : z₁.T.left = V₁) (hz₂ : z₂.T.left = V₂) (κc₁ : CoherentHom z₁ A)
    (κc₂ : CoherentHom z₂ A) {a₁ : V₁ ⟶ U} {a₂ : V₂ ⟶ U}
    (hκ₁ : κc₁.base.left = eqToHom hz₁ ≫ a₁ ≫ eqToHom hA.symm)
    (hκ₂ : κc₂.base.left = eqToHom hz₂ ≫ a₂ ≫ eqToHom hA.symm) (ρb : z₁.T ⟶ z₂.T)
    (hl : V₁ ⟶ V₂) (hρ : ρb.left = eqToHom hz₁ ≫ hl ≫ eqToHom hz₂.symm)
    (κ'₂ : V₂ ⟶ T.left) (hκ'₂ : κ'₂ ≫ ι = a₂) (hκ'₁ : (hl ≫ κ'₂) ≫ ι = a₁) :
    (zSpaceIso hA ι tA htA hz₁ κc₁ hκ₁ (hl ≫ κ'₂) hκ'₁).hom ≫
        baseChangeMap (D.projection T) (commonTestMap tA tA' hl κ'₂) =
      D.relativeMap ρb ≫ (zSpaceIso hA ι tA htA hz₂ κc₂ hκ₂ κ'₂ hκ'₂).hom := by
  refine baseChange_hom_ext (D.projection T) ?_ ?_
  · rw [Category.assoc, baseChangeMap_comp_projection, zSpaceIso_hom_projection, Category.assoc,
      zSpaceIso_hom_projection, ← relativeMap_comp]
    congr 1
    refine CostructuredArrow.hom_ext _ _ ?_
    rw [CostructuredArrow.comp_left, zToCommon_left, zToCommon_left, hρ]
    simp
  · rw [Category.assoc, baseChangeMap_comp_inclusion, ← Category.assoc, zSpaceIso_hom_inclusion,
      Category.assoc (D.relativeMap ρb), zSpaceIso_hom_inclusion hA ι tA htA hz₂ κc₂ hκ₂ κ'₂ hκ'₂,
      ← Category.assoc, baseChangeMap_comp_inclusion, Category.assoc, Category.assoc,
      ← Functor.map_comp, ← Functor.map_comp, hρ]
    simp

/-- **The morphisms of `Coh_{X/Y}` defined by sections of the relative Isom functor are natural.**
Restricting the morphism of `u` along a morphism `ρ : z₁ ⟶ z₂` of cartesian lifts over `hl` is the
morphism of the restriction of `u` along `hl`. -/
theorem comp_psi {z₁ z₂ : CoherentObject D} {V₁ V₂ : BigFppfOver B S hS} (hz₁ : z₁.T.left = V₁)
    (hz₂ : z₂.T.left = V₂) (κc₂ : CoherentHom z₂ A) {a₁ : V₁ ⟶ U} {a₂ : V₂ ⟶ U}
    (hκ₂ : κc₂.base.left = eqToHom hz₂ ≫ a₂ ≫ eqToHom hA.symm) (ρ : CoherentHom z₁ z₂)
    (hl : V₁ ⟶ V₂) (hρ : ρ.base.left = eqToHom hz₁ ≫ hl ≫ eqToHom hz₂.symm) (hla : hl ≫ a₂ = a₁)
    (hκ₁ : (ρ.comp κc₂).base.left = eqToHom hz₁ ≫ a₁ ≫ eqToHom hA.symm)
    (κ'₂ : V₂ ⟶ T.left) (hκ'₂ : κ'₂ ≫ ι = a₂)
    (u : ((pairHomSituation tA tA').isomFunctor).obj (Opposite.op (commonTest tA tA' κ'₂)))
    (b₂ : z₂.T ⟶ A'.T)
    (hb₂ : (zSpaceIso hA ι tA htA hz₂ κc₂ hκ₂ κ'₂ hκ'₂).hom ≫
      (baseChangeProjection (D.projection T)
        (CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map κ'₂)) ≫ D.relativeMap tA') =
      D.relativeMap b₂)
    (hκ'₁ : (hl ≫ κ'₂) ≫ ι = a₁)
    (hb₁ : (zSpaceIso hA ι tA htA hz₁ (ρ.comp κc₂) hκ₁ (hl ≫ κ'₂) hκ'₁).hom ≫
      (baseChangeProjection (D.projection T)
        (CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map (hl ≫ κ'₂))) ≫ D.relativeMap tA') =
      D.relativeMap (ρ.base ≫ b₂)) :
    ρ.comp (psi hA ι tA htA hz₂ κc₂ hκ₂ tA' κ'₂ hκ'₂ u b₂ hb₂) =
      psi hA ι tA htA hz₁ (ρ.comp κc₂) hκ₁ tA' (hl ≫ κ'₂) hκ'₁
        (((pairHomSituation tA tA').isomFunctor.map (commonTestMap tA tA' hl κ'₂).op) u)
        (ρ.base ≫ b₂) hb₁ := by
  have hτ : D.relativeMap ρ.base ≫ D.relativeMap κc₂.base = D.relativeMap (ρ.base ≫ κc₂.base) :=
    (relativeMap_comp D _ _).symm
  have key : (ρ.comp κc₂).fibre ≫
        inv (ρ.comp (psi hA ι tA htA hz₂ κc₂ hκ₂ tA' κ'₂ hκ'₂ u b₂ hb₂)).fibre =
      (ρ.comp κc₂).fibre ≫ inv (psi hA ι tA htA hz₁ (ρ.comp κc₂) hκ₁ tA' (hl ≫ κ'₂) hκ'₁
        (((pairHomSituation tA tA').isomFunctor.map (commonTestMap tA tA' hl κ'₂).op) u)
        (ρ.base ≫ b₂) hb₁).fibre := by
    rw [sigma_comp ρ κc₂ _ hτ, fibre_inv_psi, fibre_inv_psi]
    unfold psiSec
    have E1₂ := zSpaceIso_hom_comp hA ι tA htA hz₂ κc₂ hκ₂ κ'₂ hκ'₂ tA κc₂.base
      (zToCommon_eq_left hA ι tA htA hz₂ κc₂ hκ₂ κ'₂ hκ'₂)
    have hnat := zSpaceIso_naturality hA ι tA htA tA' hz₁ hz₂ (ρ.comp κc₂) κc₂ hκ₁ hκ₂ ρ.base hl hρ
      κ'₂ hκ'₂ hκ'₁
    have hbcp := baseChangeMap_comp_projection (D.projection T) (commonTestMap tA tA' hl κ'₂)
    have hm : (pairHomSituation tA tA').toModuleHom
        (((pairHomSituation tA tA').isomFunctor.map (commonTestMap tA tA' hl κ'₂).op) u).1 =
        secRestrict (baseChangeMap (D.projection T) (commonTestMap tA tA' hl κ'₂)) hbcp hbcp
          ((pairHomSituation tA tA').toModuleHom u.1) := by
      rw [HomSituation.toModuleHom_isomFunctor_map, CategoryTheory.Functor.conjHom_eq_secMap]
      rfl
    rw [hm, secPush_secRestrict _ _ _ hbcp hbcp (by rw [← Category.assoc, hbcp])
      (by rw [← Category.assoc, hbcp])]
    refine (secRestrict_secRestrict _ _ _ _ _ _
      ((Category.assoc _ _ _).trans ((congrArg _ E1₂).trans hτ))
      ((Category.assoc _ _ _).trans ((congrArg _ hb₂).trans (relativeMap_comp D _ _).symm)) _).trans
      ?_
    refine Eq.trans ?_ (secRestrict_secRestrict _ _ _ _ _ _ ?_ ?_ _).symm
    · exact secRestrict_congr hnat.symm _ _ _ _ _
    · rw [Category.assoc, ← Category.assoc (baseChangeMap (D.projection T)
        (commonTestMap tA tA' hl κ'₂)), hbcp]
      exact zSpaceIso_hom_comp hA ι tA htA hz₁ (ρ.comp κc₂) hκ₁ (hl ≫ κ'₂) hκ'₁ tA _
        (zToCommon_eq_left hA ι tA htA hz₁ (ρ.comp κc₂) hκ₁ (hl ≫ κ'₂) hκ'₁)
    · rw [Category.assoc, ← Category.assoc (baseChangeMap (D.projection T)
        (commonTestMap tA tA' hl κ'₂)), hbcp]
      exact hb₁
  exact eq_of_sigma_same (ρ.comp κc₂) (ρ.base ≫ b₂) _ _ _ _ key

end Naturality




/-! ### The isomorphism presheaf from an algebraic space representing the relative Isom functor -/

section Assembly

variable (x y : (coherentSiteProjection D.categoryData).Fiber U) {T : SchemesOver D.Y}
  (ι : T.left ⟶ U) (tA : T ⟶ x.1.T)
  (htA : tA.left = ι ≫ eqToHom (show x.1.T.left = U from x.2).symm)
  (tA' : T ⟶ y.1.T)
  {H : AlgebraicSpaces B S hS} (p : H ⟶ (schemeSpaceFunctor B S hS).obj T.left)
  (θ : spacePointsOver p ⋙ uliftFunctor.{u + 1, u} ≅ (pairHomSituation tA tA').isomFunctor)

/-- The presheaf on `𝒮/U` of the points of `H` over `T` lying over the given morphism to `U`. -/
abbrev pointPresheaf : (Over U)ᵒᵖ ⥤ Type u :=
  OverShriek.fiber (𝟙 (yoneda.obj U)) (p.hom ≫ yoneda.map ι)

/-- The point of `H` over the test scheme of `κ'`, from a section of the point presheaf. -/
def pointOf {a : Over U} (s : (pointPresheaf ι p).obj (Opposite.op a)) :
    (spacePointsOver p).obj
      (Opposite.op (commonTest tA tA' (p.hom.app (Opposite.op a.left) s.1))) :=
  ⟨s.1, (yonedaEquiv_yoneda_map _).symm⟩

/-- **The morphism of `Coh_{X/Y}` that a point of `H` defines.** -/
def psiPoint (a : Over U) (s : (pointPresheaf ι p).obj (Opposite.op a)) :
    CoherentHom ((coherentSiteProjection D.categoryData).pullbackFiber x a.hom).1 y.1 :=
  psi (show x.1.T.left = U from x.2) ι tA htA
    ((coherentSiteProjection D.categoryData).pullbackFiber x a.hom).2
    (Functor.IsPreFibered.pullbackMap x.2 a.hom)
    (IsHomLift.fac' (coherentSiteProjection D.categoryData) a.hom
      (Functor.IsPreFibered.pullbackMap x.2 a.hom))
    tA' (p.hom.app (Opposite.op a.left) s.1) s.2
    (θ.hom.app _ (ULift.up (pointOf x y ι tA tA' p s)))
    (zToCommon (show x.1.T.left = U from x.2) ι tA htA
      ((coherentSiteProjection D.categoryData).pullbackFiber x a.hom).2
      (Functor.IsPreFibered.pullbackMap x.2 a.hom)
      (IsHomLift.fac' (coherentSiteProjection D.categoryData) a.hom
        (Functor.IsPreFibered.pullbackMap x.2 a.hom)) _ s.2 ≫ tA')
    (zSpaceIso_hom_comp _ ι tA htA _ _ _ _ s.2 tA' _ rfl)

variable (htA' : tA'.left = ι ≫ eqToHom (show y.1.T.left = U from y.2).symm)

include htA' in
/-- The morphism `psiPoint` lies over `a.hom`. -/
theorem isHomLift_psiPoint (a : Over U) (s : (pointPresheaf ι p).obj (Opposite.op a)) :
    (coherentSiteProjection D.categoryData).IsHomLift a.hom
      ((Equiv.cast (D.categoryData.hom_type _ _)).symm (psiPoint x y ι tA htA tA' p θ a s) :
        ((coherentSiteProjection D.categoryData).pullbackFiber x a.hom).1 ⟶ y.1) := by
  have h : (coherentSiteProjection D.categoryData).map
      ((Equiv.cast (D.categoryData.hom_type _ _)).symm (psiPoint x y ι tA htA tA' p θ a s) :
        ((coherentSiteProjection D.categoryData).pullbackFiber x a.hom).1 ⟶ y.1) =
      eqToHom ((coherentSiteProjection D.categoryData).pullbackFiber x a.hom).2 ≫ a.hom ≫
        eqToHom (show y.1.T.left = U from y.2).symm := by
    have hs : p.hom.app (Opposite.op a.left) s.1 ≫ ι = a.hom := s.2
    change (eqToHom _ ≫ p.hom.app (Opposite.op a.left) s.1) ≫ tA'.left = _
    rw [htA']
    exact (Category.assoc _ _ _).trans (congrArg (eqToHom _ ≫ ·)
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ eqToHom _) hs)))
  have h' := (show (coherentSiteProjection D.categoryData).IsHomLift
    ((coherentSiteProjection D.categoryData).map
      ((Equiv.cast (D.categoryData.hom_type _ _)).symm (psiPoint x y ι tA htA tA' p θ a s) :
        ((coherentSiteProjection D.categoryData).pullbackFiber x a.hom).1 ⟶ y.1))
      ((Equiv.cast (D.categoryData.hom_type _ _)).symm (psiPoint x y ι tA htA tA' p θ a s) :
        ((coherentSiteProjection D.categoryData).pullbackFiber x a.hom).1 ⟶ y.1)
    from inferInstance)
  rw [h] at h'
  exact (IsHomLift.lift_comp_eqToHom_iff _ _ _ _).1
    ((IsHomLift.lift_eqToHom_comp_iff _ _ _ _).1 h')

omit htA' in
/-- The values of `θ` at the same point `w` over equal morphisms `κ₁ = κ₂` are heterogeneously
equal. -/
theorem theta_heq {V : BigFppfOver B S hS} {κ₁ κ₂ : V ⟶ T.left} (e : κ₁ = κ₂)
    (w : H.1.obj (Opposite.op V))
    (pf₁ : p.hom.app (Opposite.op V) w = testPoint (commonTest tA tA' κ₁))
    (pf₂ : p.hom.app (Opposite.op V) w = testPoint (commonTest tA tA' κ₂)) :
    HEq (θ.hom.app (Opposite.op (commonTest tA tA' κ₁)) (ULift.up ⟨w, pf₁⟩))
      (θ.hom.app (Opposite.op (commonTest tA tA' κ₂)) (ULift.up ⟨w, pf₂⟩)) := by
  subst e
  rfl

omit htA' in
/-- **The morphisms of `Coh_{X/Y}` defined by the points of `H` are natural.** -/
theorem psiPoint_comp {a₁ a₂ : Over U} (h : a₁ ⟶ a₂)
    (s : (pointPresheaf ι p).obj (Opposite.op a₂)) :
    ((Equiv.cast (D.categoryData.hom_type _ _))
        ((coherentSiteProjection D.categoryData).pullbackFiberMap x h)).comp
        (psiPoint x y ι tA htA tA' p θ a₂ s) =
      psiPoint x y ι tA htA tA' p θ a₁ ((pointPresheaf ι p).map h.op s) := by
  have hρ := IsHomLift.fac' (coherentSiteProjection D.categoryData) h.left
    ((coherentSiteProjection D.categoryData).pullbackFiberMap x h)
  have hfac := (coherentSiteProjection D.categoryData).pullbackFiberMap_fac x h
  have hs : p.hom.app (Opposite.op a₂.left) s.1 ≫ ι = a₂.hom := s.2
  have hρb : ((Equiv.cast (D.categoryData.hom_type _ _))
      ((coherentSiteProjection D.categoryData).pullbackFiberMap x h)).base.left =
      eqToHom ((coherentSiteProjection D.categoryData).pullbackFiber x a₁.hom).2 ≫ h.left ≫
        eqToHom ((coherentSiteProjection D.categoryData).pullbackFiber x a₂.hom).2.symm := hρ
  unfold psiPoint
  refine (comp_psi (show x.1.T.left = U from x.2) ι tA htA tA' _ _ _ _
    ((Equiv.cast (D.categoryData.hom_type _ _))
      ((coherentSiteProjection D.categoryData).pullbackFiberMap x h)) h.left hρb (Over.w h)
    ?_ _ _ _ _ _ ?_ ?_).trans ?_
  · exact (congrArg (fun m => ((Equiv.cast (D.categoryData.hom_type _ _)) m).base.left)
      hfac).trans (IsHomLift.fac' (coherentSiteProjection D.categoryData) a₁.hom
        (Functor.IsPreFibered.pullbackMap x.2 a₁.hom))
  · exact (Category.assoc _ _ _).trans ((congrArg _ hs).trans (Over.w h))
  · refine zSpaceIso_hom_comp _ ι tA htA _ _ _ _ _ tA' _ ?_
    rw [CostructuredArrow.comp_left, hρb]
    change _ ≫ (eqToHom _ ≫ p.hom.app (Opposite.op a₂.left) s.1) ≫ tA'.left = _
    exact eqToHom_comp_eqToHom_aux _ _ _ _ _ _
  · have e₂ : h.left ≫ p.hom.app (Opposite.op a₂.left) s.1 =
        p.hom.app (Opposite.op a₁.left) ((pointPresheaf ι p).map h.op s).1 :=
      (NatTrans.naturality_apply p.hom h.left.op s.1).symm
    have hnat := congrArg (fun f => f (ULift.up (pointOf x y ι tA tA' p s)))
      (θ.hom.naturality (commonTestMap tA tA' h.left (p.hom.app (Opposite.op a₂.left) s.1)).op)
    refine psi_congr _ ι tA htA _ tA' hfac _ _ e₂ _ _ _ _ ?_ ?_ _ _
    · refine HEq.trans (heq_of_eq hnat.symm) ?_
      exact theta_heq x y tA tA' p θ e₂ _ _ _
    · refine CostructuredArrow.hom_ext _ _ ?_
      rw [CostructuredArrow.comp_left, hρb, CostructuredArrow.comp_left]
      change _ ≫ (eqToHom _ ≫ p.hom.app (Opposite.op a₂.left) s.1) ≫ tA'.left =
        (eqToHom _ ≫ p.hom.app (Opposite.op a₁.left) ((pointPresheaf ι p).map h.op s).1) ≫ tA'.left
      rw [← e₂]
      exact (eqToHom_comp_eqToHom_aux _ _ _ _ _ _).trans (Category.assoc _ _ _).symm

omit htA' in
/-- **The morphisms of `Coh_{X/Y}` defined by the points of `H` determine the points.** -/
theorem psiPoint_injective [Mono ι] (a : Over U) :
    Function.Injective (psiPoint x y ι tA htA tA' p θ a) := by
  intro s₁ s₂ h
  have hs₁ : p.hom.app (Opposite.op a.left) s₁.1 ≫ ι = a.hom := s₁.2
  have hs₂ : p.hom.app (Opposite.op a.left) s₂.1 ≫ ι = a.hom := s₂.2
  have e : p.hom.app (Opposite.op a.left) s₂.1 = p.hom.app (Opposite.op a.left) s₁.1 :=
    (cancel_mono ι).1 (hs₂.trans hs₁.symm)
  have pf : p.hom.app (Opposite.op a.left) s₂.1 =
      testPoint (commonTest tA tA' (p.hom.app (Opposite.op a.left) s₁.1)) :=
    e.trans (yonedaEquiv_yoneda_map _).symm
  have h₂ : psiPoint x y ι tA htA tA' p θ a s₂ =
      psi (show x.1.T.left = U from x.2) ι tA htA
        ((coherentSiteProjection D.categoryData).pullbackFiber x a.hom).2
        (Functor.IsPreFibered.pullbackMap x.2 a.hom)
        (IsHomLift.fac' (coherentSiteProjection D.categoryData) a.hom
          (Functor.IsPreFibered.pullbackMap x.2 a.hom))
        tA' (p.hom.app (Opposite.op a.left) s₁.1) hs₁
        (θ.hom.app _ (ULift.up ⟨s₂.1, pf⟩))
        (zToCommon (show x.1.T.left = U from x.2) ι tA htA
          ((coherentSiteProjection D.categoryData).pullbackFiber x a.hom).2
          (Functor.IsPreFibered.pullbackMap x.2 a.hom)
          (IsHomLift.fac' (coherentSiteProjection D.categoryData) a.hom
            (Functor.IsPreFibered.pullbackMap x.2 a.hom)) _ hs₁ ≫ tA')
        (zSpaceIso_hom_comp _ ι tA htA _ _ _ _ hs₁ tA' _ rfl) := by
    unfold psiPoint
    refine psi_congr _ ι tA htA _ tA' rfl _ _ e _ _ _ _ (theta_heq x y tA tA' p θ e _ _ _) ?_ _ _
    refine CostructuredArrow.hom_ext _ _ ?_
    rw [CostructuredArrow.comp_left, CostructuredArrow.comp_left]
    change (eqToHom _ ≫ p.hom.app (Opposite.op a.left) s₂.1) ≫ tA'.left =
      (eqToHom _ ≫ p.hom.app (Opposite.op a.left) s₁.1) ≫ tA'.left
    rw [e]
  rw [h₂] at h
  unfold psiPoint psi at h
  injection h with _ hf
  have hf' := inv_comp_cancel _ _ _ (isIso_psiSec _ _ _ _ _ _ _ _ _ _ _ _ _)
    (isIso_psiSec _ _ _ _ _ _ _ _ _ _ _ _ _) (CoherentHom.isIso_fibre _) hf
  have hu := psiSec_injective _ ι tA htA _ _ _ tA' _ hs₁ _ _ hf'
  have := (θ.app (Opposite.op
    (commonTest tA tA' (p.hom.app (Opposite.op a.left) s₁.1)))).toEquiv.injective hu
  exact Subtype.ext (congrArg (fun w => w.down.1) this)

include htA' in
/-- **Every morphism over the base comes from a point of `H`**, granted that the base maps of the
two objects agree exactly on what factors through `ι`. -/
theorem psiPoint_surjective
    (hfac : ∀ (g : Over U), (schemeSpaceFunctor B S hS).map g.hom ≫ coherentFiberPoint D x =
      (schemeSpaceFunctor B S hS).map g.hom ≫ coherentFiberPoint D y →
        ∃ κ' : g.left ⟶ T.left, κ' ≫ ι = g.hom)
    (a : Over U) (m : ((coherentSiteProjection D.categoryData).pullbackFiber x a.hom).1 ⟶ y.1)
    (hm : (coherentSiteProjection D.categoryData).IsHomLift a.hom m) :
    ∃ s, psiPoint x y ι tA htA tA' p θ a s = (Equiv.cast (D.categoryData.hom_type _ _)) m := by
  have hx := coherentFiberPoint_naturality D
    ((coherentSiteProjection D.categoryData).pullbackFiber x a.hom) x a.hom
    (Functor.IsPreFibered.pullbackMap x.2 a.hom) inferInstance
  have hy := coherentFiberPoint_naturality D
    ((coherentSiteProjection D.categoryData).pullbackFiber x a.hom) y a.hom m hm
  obtain ⟨κ', hκ'⟩ := hfac a (hx.trans hy.symm)
  set mc : CoherentHom _ _ := (Equiv.cast (D.categoryData.hom_type _ _)) m with hmc
  have hmb : mc.base.left =
      eqToHom ((coherentSiteProjection D.categoryData).pullbackFiber x a.hom).2 ≫
      a.hom ≫ eqToHom (show y.1.T.left = U from y.2).symm :=
    IsHomLift.fac' (coherentSiteProjection D.categoryData) a.hom m
  have hb := zSpaceIso_hom_comp (show x.1.T.left = U from x.2) ι tA htA
    ((coherentSiteProjection D.categoryData).pullbackFiber x a.hom).2
    (Functor.IsPreFibered.pullbackMap x.2 a.hom)
    (IsHomLift.fac' (coherentSiteProjection D.categoryData) a.hom
      (Functor.IsPreFibered.pullbackMap x.2 a.hom)) κ' hκ' tA' mc.base (by
        rw [hmb, htA', ← hκ']
        simp only [Category.assoc]
        rfl)
  have : IsIso ((Functor.IsPreFibered.pullbackMap x.2 a.hom : CoherentHom _ _).fibre ≫
      inv mc.fibre) := by
    have := (Functor.IsPreFibered.pullbackMap x.2 a.hom : CoherentHom _ _).isIso_fibre
    infer_instance
  obtain ⟨u, hu⟩ := exists_psiSec_eq _ ι tA htA _ _ _ tA' κ' hκ' mc.base hb
    ((Functor.IsPreFibered.pullbackMap x.2 a.hom : CoherentHom _ _).fibre ≫ inv mc.fibre)
  set w := (θ.inv.app (Opposite.op (commonTest tA tA' κ')) u).down with hwdef
  have hw : p.hom.app (Opposite.op a.left) w.1 = κ' := w.2.trans (yonedaEquiv_yoneda_map κ')
  refine ⟨⟨w.1, (show p.hom.app (Opposite.op a.left) w.1 ≫ ι = a.hom by rwa [hw])⟩, ?_⟩
  unfold psiPoint
  refine (psi_congr _ ι tA htA _ tA' rfl _ _ hw _ hκ' _ u ?_ ?_ _ hb).trans ?_
  · refine (theta_heq x y tA tA' p θ hw _ _ w.2).trans (heq_of_eq ?_)
    exact ((θ.app (Opposite.op (commonTest tA tA' κ'))).toEquiv).apply_symm_apply u
  · refine CostructuredArrow.hom_ext _ _ ?_
    rw [CostructuredArrow.comp_left, hmb]
    change (eqToHom _ ≫ p.hom.app (Opposite.op a.left) w.1) ≫ tA'.left = _
    rw [hw, htA']
    exact eqToHom_comp_comp_aux _ _ _ _ _ hκ'
  · exact psi_eq_of_psiSec_eq _ ι tA htA _ _ _ tA' κ' hκ' mc.base mc.fibre mc.isIso_fibre hb u hu

include htA' in
/-- **The presheaf of morphisms over the base is the presheaf of points of `H`.** -/
def pointPresheafIso [Mono ι]
    (hfac : ∀ (g : Over U), (schemeSpaceFunctor B S hS).map g.hom ≫ coherentFiberPoint D x =
      (schemeSpaceFunctor B S hS).map g.hom ≫ coherentFiberPoint D y →
        ∃ κ' : g.left ⟶ T.left, κ' ≫ ι = g.hom) :
    pointPresheaf ι p ⋙ uliftFunctor.{u + 1, u} ≅
      Functor.homOverPresheaf (coherentSiteProjection D.categoryData) x y ⋙
        uliftFunctor.{u, u + 1} :=
  NatIso.ofComponents (fun a => Equiv.toIso (Equiv.ofBijective
      (fun s => ULift.up ⟨(Equiv.cast (D.categoryData.hom_type _ _)).symm
        (psiPoint x y ι tA htA tA' p θ a.unop s.down),
        isHomLift_psiPoint x y ι tA htA tA' p θ htA' a.unop s.down⟩)
      ⟨fun s₁ s₂ h => by
        have h' := congrArg (fun t => (Equiv.cast (D.categoryData.hom_type _ _)) t.down.1) h
        simp only [Equiv.apply_symm_apply] at h'
        exact ULift.ext (psiPoint_injective x y ι tA htA tA' p θ a.unop h'),
      fun m => by
        obtain ⟨s, hs⟩ :=
          psiPoint_surjective x y ι tA htA tA' p θ htA' hfac a.unop m.down.1 m.down.2
        refine ⟨ULift.up s, ?_⟩
        apply ULift.ext
        apply Subtype.ext
        change (Equiv.cast _).symm (psiPoint x y ι tA htA tA' p θ a.unop s) = m.down.1
        rw [hs, Equiv.symm_apply_apply]⟩))
    (fun {a₂ a₁} h => by
      ext s
      apply ULift.ext
      apply Subtype.ext
      change (Equiv.cast _).symm (psiPoint x y ι tA htA tA' p θ a₁.unop
          ((pointPresheaf ι p).map h s.down)) =
        (coherentSiteProjection D.categoryData).pullbackFiberMap x h.unop ≫
          (Equiv.cast _).symm (psiPoint x y ι tA htA tA' p θ a₂.unop s.down)
      have hc := psiPoint_comp x y ι tA htA tA' p θ h.unop s.down
      rw [Quiver.Hom.op_unop] at hc
      rw [← hc]
      rfl)

omit htA' in
/-- **The presheaf of points of `H` lying over `U`, read on the schemes over `U`, is an algebraic
space over `U`.** -/
theorem isAlgebraicSpace_pointPresheaf :
    IsAlgebraicSpace B U.left.1 U.left.2
      ((Over.iteratedSliceBackward U).op ⋙ pointPresheaf ι p) := by
  let q : H.1 ⟶ yoneda.obj U := p.hom ≫ yoneda.map ι
  let R := OverShriek.relocalizeRestrict U.hom
  let T' : BigFppfOver B U.left.1 U.left.2 := Over.mk (𝟙 _)
  let F := (Over.iteratedSliceBackward U).op ⋙ OverShriek.fiber (𝟙 _) q
  let a' : yoneda.obj T' ⟶ R.obj (yoneda.obj U) := {
    app := fun W => ↾fun _ => Over.homMk W.unop.hom
    naturality := by
      intro W W' g
      ext z
      exact Over.OverMorphism.ext (Over.w g.unop).symm }
  let b : F ⟶ yoneda.obj T' := {
    app := fun W => ↾fun _ => Over.homMk W.unop.hom
    naturality := by
      intro W W' g
      ext z
      exact Over.OverMorphism.ext (Over.w g.unop).symm }
  let i : F ⟶ R.obj H.1 := {
    app := fun _ => ↾fun z => z.1
    naturality := by intros; rfl }
  have hi : b ≫ a' = i ≫ R.map q := by
    ext W z
    exact z.2.symm
  have hp : IsPullback b i a' (R.map q) := by
    apply IsPullback.of_isLimit (c := PullbackCone.mk b i hi)
    refine PullbackCone.IsLimit.mk hi (fun s => {
      app := fun W => ↾fun z => ⟨s.snd.app W z, ?_⟩
      naturality := ?_ }) ?_ ?_ ?_
    · exact (congrArg (fun k => k.app W z) s.condition).symm
    · intro W W' g
      ext z
      apply Subtype.ext
      exact s.snd.naturality_apply g z
    · intro s
      ext W z
      exact (Over.mkIdTerminal : IsTerminal T').hom_ext _ _
    · exact fun _ => rfl
    · intro s m hm₁ hm₂
      ext W z
      exact Subtype.ext (congrArg (fun k => k.app W z) hm₂)
  have hRP := isAlgebraicSpace_relocalizeRestrict B U.left.1 S U.left.2 hS U.hom H.1 H.2
  have hRV := isAlgebraicSpace_relocalizeRestrict B U.left.1 S U.left.2 hS U.hom (yoneda.obj U)
    (isAlgebraicSpace_yoneda B S hS U)
  have hT := isAlgebraicSpace_yoneda B U.left.1 U.left.2 T'
  exact AlgebraicGeometry.Space.isAlgebraicSpace_of_iso B U.left.1 U.left.2 (hp.isoPullback).symm
    (isAlgebraicSpace_pullback B U.left.1 U.left.2 a' (R.map q) hT hRP hRV)

end Assembly

/-! ### Stacks 08W6, granted the conclusion of Proposition 08K9 -/

variable (D) (hst : ModulePullbackStabilityOfFinitePresentation B S hS)

/-- **The isomorphism presheaves of `Coh_{X/Y}` are algebraic spaces once the relative Isom
functors over the equalizers are.**  This is the source's proof of Stacks 08W6 after Lemma 045G:
`Isom_𝒳(x, y)` maps to the equalizer `E` of the two base maps, and over `E` it is the relative
Isom functor `Isom(F, G)` of the standing datum of Stacks 08JT over `E`; the hypothesis is the
conclusion of Proposition 08K9 for that standing datum. -/
theorem coherentCFG_isAlgebraicSpaceIsomPresheaf
    (h08K9 : ∀ (U : BigFppfOver B S hS) (x y : (coherentSiteProjection D.categoryData).Fiber U),
      ∃ (H : AlgebraicSpaces B S hS)
        (p : H ⟶ (schemeSpaceFunctor B S hS).obj (coherentEqualizer D x.1 y.1 x.2 y.2)),
        Nonempty (spacePointsOver p ⋙ uliftFunctor.{u + 1, u} ≅
          (pairHomSituation (coherentEqualizerToFst D x.1 y.1 x.2 y.2)
            (coherentEqualizerToSnd D x.1 y.1 x.2 y.2)).isomFunctor)) :
    Stack.IsAlgebraicSpaceIsomPresheaf B S hS D.coherentCFG := by
  intro U x y
  obtain ⟨H, p, ⟨θ⟩⟩ := h08K9 U x y
  let ι := coherentEqualizerMap D x.1 y.1 x.2 y.2
  have : Mono (show (coherentEqualizerTestScheme D x.1 y.1 x.2 y.2).left ⟶ U from ι) :=
    mono_coherentEqualizerMap D x.1 y.1 x.2 y.2
  let tA := coherentEqualizerToFst D x.1 y.1 x.2 y.2
  let tA' := coherentEqualizerToSnd D x.1 y.1 x.2 y.2
  have hfac : ∀ (g : Over U), (schemeSpaceFunctor B S hS).map g.hom ≫ coherentFiberPoint D x =
      (schemeSpaceFunctor B S hS).map g.hom ≫ coherentFiberPoint D y →
        ∃ κ' : g.left ⟶ (coherentEqualizerTestScheme D x.1 y.1 x.2 y.2).left, κ' ≫ ι = g.hom :=
    fun g hg => exists_factor_pointEqualizer D.Y (coherentObjectPoint x.1 x.2).hom
      (coherentObjectPoint y.1 y.2).hom g.hom (congrArg InducedCategory.Hom.hom hg)
  exact ⟨(Over.iteratedSliceBackward U).op ⋙
      pointPresheaf (T := coherentEqualizerTestScheme D x.1 y.1 x.2 y.2) ι p,
    isAlgebraicSpace_pointPresheaf (T := coherentEqualizerTestScheme D x.1 y.1 x.2 y.2) ι p,
    ⟨Functor.isoWhiskerLeft (Over.iteratedSliceBackward U).op
      (pointPresheafIso (T := coherentEqualizerTestScheme D x.1 y.1 x.2 y.2) x y ι tA rfl tA' p θ
        rfl hfac ≪≫
        Functor.isoWhiskerRight
          ((Functor.morPresheafIsoHomOver (coherentSiteProjection D.categoryData) x y).symm ≪≫
            (@Stack.isomPresheafIsoMorPresheaf _ _ _ _ (coherentSiteProjection D.categoryData)
              (cohIsFibered D) D.isFiberedInGroupoids_siteProjection _ x y).symm)
          uliftFunctor.{u, u + 1})⟩⟩

/-- The standing datum of Stacks 08JT over the equalizer used here is
`AlgebraicGeometry.Space.coherentEqualizerHomSituation`. -/
theorem pairHomSituation_eq_coherentEqualizerHomSituation
    (x y : (coherentSiteProjection D.categoryData).Fiber U) :
    pairHomSituation (coherentEqualizerToFst D x.1 y.1 x.2 y.2)
        (coherentEqualizerToSnd D x.1 y.1 x.2 y.2) =
      coherentEqualizerHomSituation D x.1 y.1 x.2 y.2 hst :=
  rfl

/-- **Stacks 08W6, granted the conclusion of Proposition 08K9.**  The diagonal of `Coh_{X/Y}` is
representable by algebraic spaces once the relative Isom functor of the standing datum of
Stacks 08JT over the equalizer of the two base maps of any two objects over a scheme is an
algebraic space over the equalizer. -/
theorem coherentCFG_hasRepresentableDiagonal
    (h08K9 : ∀ (U : BigFppfOver B S hS) (x y : (coherentSiteProjection D.categoryData).Fiber U),
      ∃ (H : AlgebraicSpaces B S hS)
        (p : H ⟶ (schemeSpaceFunctor B S hS).obj (coherentEqualizer D x.1 y.1 x.2 y.2)),
        Nonempty (spacePointsOver p ⋙ uliftFunctor.{u + 1, u} ≅
          (coherentEqualizerHomSituation D x.1 y.1 x.2 y.2 hst).isomFunctor)) :
    Stack.HasRepresentableDiagonal B S hS D.coherentCFG :=
  (Stack.hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS D.coherentCFG).2
    (coherentCFG_isAlgebraicSpaceIsomPresheaf D fun U x y => by
      obtain ⟨H, p, hθ⟩ := h08K9 U x y
      exact ⟨H, p, hθ⟩)

end CoherentSituation

end AlgebraicGeometry.Space
