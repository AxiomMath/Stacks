module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackAxiomHelpers.CoherentTangentBridge
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackDeformationBridge.Pullback

/-!
# Classes of lifts of an object of `Coh_{X/Y}` as classes of lifts of its module

Let `x = (T, 𝒢)` be an object of `Coh_{X/Y}` (Stacks 08KB), with `Y` final, and let
`b : T ⟶ U` be a morphism of the site out of its test scheme. A lift of `x` along `b` in the sense
of the deformation theory of categories fibred in groupoids — an object of the fibre of
`Under.post p` over `b`, that is, an arrow `x ⟶ y` of `Coh_{X/Y}` lying over `b` — is the same as
a lift of the module `𝒢` across `b` in the sense of
`AlgebraicGeometry.Space.CoherentSituation.ThickeningLift`. This file proves that the two notions
have the same isomorphism classes, compatibly with pullback along morphisms `V ⟶ U` under `T`.
This is the translation the source uses, in the proofs of Stacks 08W8 and 08WA, to compute the
tangent spaces and the obstruction theory of `Coh_{X/Y}` from the deformation theory of modules
(Stacks 08VW).

## Main definitions

* `AlgebraicGeometry.Space.CoherentSituation.liftClassOf`: the class of the lift of `ξ` given by a
  morphism of `Coh_{X/Y}` out of `ξ`, read through an identification of test schemes.
* `AlgebraicGeometry.Space.CoherentSituation.fiberLiftClassEquiv`: the bijection between classes
  of lifts of `x` along `b` and classes of lifts of `𝒢` across `b`.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.ThickeningLift.isIsomorphic_of_comp_eq`: two lifts
  related by a morphism of `Coh_{X/Y}` over the identity are isomorphic.
* `AlgebraicGeometry.Space.CoherentSituation.fiberLiftClass_naturality`: the bijection is
  compatible with pullback.

## Implementation notes

The module comparisons of morphisms of `Coh_{X/Y}` are compared only through statements whose
two sides are spelled alike: base maps are kept as variables, the functors of a comparison are
given explicitly, and an equality of base maps is crossed by an `eqToIso` of the inverse image
functors. Comparing two spellings of the same object beneath `NatTrans.app` by unfolding does not
terminate in reasonable time.

These are private helpers of Stacks 08W8 and 08WA; no declaration here carries a tag.

## References

* [Stacks Project, Tag 08KB](https://stacks.math.columbia.edu/tag/08KB)
* [Stacks Project, Tag 08VW](https://stacks.math.columbia.edu/tag/08VW)
* [Stacks Project, Tag 08W8](https://stacks.math.columbia.edu/tag/08W8)
* [Stacks Project, Tag 08WA](https://stacks.math.columbia.edu/tag/08WA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.Functor

variable {C₀ C₁ C₂ : Type*} [Category* C₀] [Category* C₁] [Category* C₂]

/-- The comparison `τ` followed by `La` of the inverse of `γ` is the identity, when the composite
`τ ≪≫ isoWhiskerRight γ La ≪≫ leftUnitor La` is trivial. -/
private theorem comparison_comp_map_app_eq_id {La : C₁ ⥤ C₀} {Lb : C₁ ⥤ C₁}
    (τ : La ≅ Lb ⋙ La) (γ : Lb ≅ 𝟭 C₁)
    (hfac : τ ≪≫ isoWhiskerRight γ La ≪≫ leftUnitor La = eqToIso (rfl : La = La)) (F : C₁) :
    τ.hom.app F ≫ La.map (γ.hom.app F) = 𝟙 _ := by
  simpa using NatTrans.congr_app (congrArg Iso.hom hfac) F

/-- A composite of fibre morphisms over an identification `γ : Lb ≅ 𝟭` whose comparison is
identified with an equality `Lab = La` is, up to that equality, a fibre morphism along an
isomorphism of its sources. -/
theorem exists_iso_of_heq_fibreComp {La Lab : C₁ ⥤ C₀} {Lb : C₁ ⥤ C₁} (τ : Lab ≅ Lb ⋙ La)
    (γ : Lb ≅ 𝟭 C₁) (hL : Lab = La)
    (hfac : τ ≪≫ isoWhiskerRight γ La ≪≫ leftUnitor La = eqToIso hL)
    {F₁ F₂ : C₁} {N : C₀} (fib : Lb.obj F₂ ⟶ F₁) [IsIso fib] (f₁ : La.obj F₁ ⟶ N)
    (f₂ : La.obj F₂ ⟶ N) (hk : HEq (fibreComp τ f₁ fib) f₂) :
    ∃ e : F₁ ≅ F₂, La.map e.hom ≫ f₂ = f₁ := by
  subst Lab
  have h1 := comparison_comp_map_app_eq_id τ γ hfac F₂
  have h2 : La.map (γ.hom.app F₂) = τ.inv.app F₂ := by
    rw [← cancel_epi (τ.hom.app F₂), h1, Iso.hom_inv_id_app]
  refine ⟨(asIso fib).symm ≪≫ γ.app F₂, ?_⟩
  rw [← eq_of_heq hk]
  change La.map (CategoryTheory.inv fib ≫ γ.hom.app F₂) ≫ τ.hom.app F₂ ≫ La.map fib ≫ f₁ = f₁
  rw [Functor.map_comp, Category.assoc, h2, Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc,
    IsIso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]

/-- Conversely, a fibre morphism along an isomorphism of sources is a composite of fibre
morphisms over `γ`. -/
theorem heq_fibreComp_of_iso {La Lab : C₁ ⥤ C₀} {Lb : C₁ ⥤ C₁} (τ : Lab ≅ Lb ⋙ La)
    (γ : Lb ≅ 𝟭 C₁) (hL : Lab = La)
    (hfac : τ ≪≫ isoWhiskerRight γ La ≪≫ leftUnitor La = eqToIso hL)
    {F₁ F₂ : C₁} {N : C₀} (e : F₁ ≅ F₂) (f₁ : La.obj F₁ ⟶ N)
    (f₂ : La.obj F₂ ⟶ N) (he : La.map e.hom ≫ f₂ = f₁) :
    HEq (fibreComp τ f₁ (γ.hom.app F₂ ≫ e.inv)) f₂ := by
  subst Lab
  have h1 := comparison_comp_map_app_eq_id τ γ hfac F₂
  refine heq_of_eq ?_
  rw [fibreComp, Functor.map_comp, Category.assoc, reassoc_of% h1, ← he,
    ← Functor.map_comp_assoc, e.inv_hom_id]
  simp

/-- A fibre morphism read through a comparison and then composed with the identity is, up to the
identification of the composite functors, the original fibre morphism. -/
theorem heq_fibreComp_comparison_id {La : C₁ ⥤ C₀} {Lb : C₂ ⥤ C₁} {Lab Lh : C₂ ⥤ C₀}
    (τ : Lab ≅ Lb ⋙ La) (hL : Lab = Lh) {M : C₂} {N : C₀} (f : Lh.obj M ⟶ N) :
    HEq (fibreComp τ ((τ.symm ≪≫ eqToIso hL).hom.app M ≫ f) (𝟙 (Lb.obj M))) f := by
  subst Lab
  refine heq_of_eq ?_
  simp [fibreComp]

/-- A fibre morphism `f` which is the composite of `f'` with an isomorphism `fib` through a
comparison `τ` gives back `f'` when composed with the inverse of `fib`. -/
theorem map_inv_comp_eq_of_heq_fibreComp {La : C₁ ⥤ C₀} {Lb : C₂ ⥤ C₁} {Lab Lh : C₂ ⥤ C₀}
    (τ : Lab ≅ Lb ⋙ La) (hL : Lab = Lh) (σ : Lb ⋙ La ≅ Lh) (hσ : σ = τ.symm ≪≫ eqToIso hL)
    {F₂ : C₂} {F₁ : C₁} {N : C₀} (fib : Lb.obj F₂ ⟶ F₁)
    [IsIso fib] (f' : La.obj F₁ ⟶ N) (f : Lh.obj F₂ ⟶ N) (hk : HEq (fibreComp τ f' fib) f) :
    La.map (CategoryTheory.inv fib) ≫ σ.hom.app F₂ ≫ f = f' := by
  subst Lab
  subst hσ
  rw [← eq_of_heq hk]
  simp [fibreComp]

end CategoryTheory.Functor

namespace AlgebraicGeometry.Space.CoherentSituation

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : CoherentSituation B S hS}

namespace ThickeningLift

variable {ξ : CoherentObject D} {T' : SchemesOver D.Y} {h : ξ.T ⟶ T'}

/-- **Two lifts related by a morphism of `Coh_{X/Y}` over the identity are isomorphic.** -/
theorem isIsomorphic_of_comp_eq (L₁ L₂ : D.ThickeningLift ξ h)
    (ψ : CoherentHom L₁.toObject L₂.toObject) (hb : ψ.base = 𝟙 T')
    (hc : L₁.toHom.comp ψ = L₂.toHom) : L₁.IsIsomorphic L₂ := by
  obtain ⟨b, fib, hfib⟩ := ψ
  change b = 𝟙 T' at hb
  subst hb
  have hk := heq_fibre_of_eq hc
  simp only [CoherentHom.comp_fibre] at hk
  exact Functor.exists_iso_of_heq_fibreComp (D.compComparison h (𝟙 T'))
    (D.idComparison (modulePushforwardCoherence B S hS) T')
    (congrArg (fun k => modulePullback B S hS (D.relativeMap k)) (Category.comp_id h))
    (comp_idComparison_fac (modulePushforwardCoherence B S hS) D h) fib L₁.fibre L₂.fibre hk

/-- The morphism of `Coh_{X/Y}` over the identity attached to an isomorphism of two lifts. -/
def isoHom {L₁ L₂ : D.ThickeningLift ξ h} (e : L₁.F ≅ L₂.F) :
    CoherentHom L₁.toObject L₂.toObject where
  base := 𝟙 T'
  fibre := (D.idComparison (modulePushforwardCoherence B S hS) T').hom.app L₂.F ≫ e.inv
  isIso_fibre := Iso.isIso_hom
    ((D.idComparison (modulePushforwardCoherence B S hS) T').app L₂.F ≪≫ e.symm)

/-- **An isomorphism of lifts carries the arrow of the first lift to the arrow of the second.** -/
theorem comp_isoHom {L₁ L₂ : D.ThickeningLift ξ h} (e : L₁.F ≅ L₂.F)
    (he : (modulePullback B S hS (D.relativeMap h)).map e.hom ≫ L₂.fibre = L₁.fibre) :
    L₁.toHom.comp (isoHom e) = L₂.toHom := by
  refine coherentHom_eq_of_heq (Category.comp_id h) ?_
  simp only [CoherentHom.comp_fibre]
  exact Functor.heq_fibreComp_of_iso (D.compComparison h (𝟙 T'))
      (D.idComparison (modulePushforwardCoherence B S hS) T')
      (congrArg (fun k => modulePullback B S hS (D.relativeMap k)) (Category.comp_id h))
      (comp_idComparison_fac (modulePushforwardCoherence B S hS) D h) e L₁.fibre L₂.fibre he

variable {T'₂ : SchemesOver D.Y} {h₂ : ξ.T ⟶ T'₂}

/-- **The pulled back lift, with its module written as the inverse image `(X_g)^*𝒢'`.**  It is
`AlgebraicGeometry.Space.CoherentSituation.ThickeningLift.pullback` by definition
(`AlgebraicGeometry.Space.CoherentSituation.ThickeningLift.pullback_eq_pullbackLift`); the
spelling of the module keeps the source of the comparison and the module syntactically
aligned. -/
abbrev pullbackLift (g : T'₂ ⟶ T') (hg : h₂ ≫ g = h) (L : D.ThickeningLift ξ h) :
    D.ThickeningLift ξ h₂ :=
  L.pullback g hg

/-- The pulled back lift is `pullbackLift` by definition. -/
theorem pullback_eq_pullbackLift (g : T'₂ ⟶ T') (hg : h₂ ≫ g = h) (L : D.ThickeningLift ξ h) :
    L.pullback g hg = pullbackLift g hg L :=
  rfl

/-- **A morphism of `Coh_{X/Y}` under `ξ` between the objects of two lifts exhibits the first as
the pullback of the second.**  If `Φ : (T'₂, 𝒢'₂) ⟶ (T', 𝒢')` carries the arrow of a lift `L'`
across `h₂` to the arrow of a lift `L` across `h`, then `L'` is isomorphic to the pullback of `L`
along `Φ.base`, by the inverse of the module comparison of `Φ`. -/
theorem isIsomorphic_pullbackLift_of_comp_eq (L : D.ThickeningLift ξ h)
    (L' : D.ThickeningLift ξ h₂) (g : T'₂ ⟶ T')
    (fib : (modulePullback B S hS (D.relativeMap g)).obj L.F ⟶ L'.F) (hfib : IsIso fib)
    (hc : L'.toHom.comp (⟨g, fib, hfib⟩ : CoherentHom L'.toObject L.toObject) = L.toHom)
    (hg : h₂ ≫ g = h) :
    L'.IsIsomorphic (pullbackLift g hg L) := by
  have hk := heq_fibre_of_eq hc
  simp only [CoherentHom.comp_fibre] at hk
  refine ⟨(asIso fib).symm, ?_⟩
  rw [Iso.symm_hom, asIso_inv]
  exact Functor.map_inv_comp_eq_of_heq_fibreComp (D.compComparison h₂ g)
    (congrArg (fun k => modulePullback B S hS (D.relativeMap k)) hg) (pullbackComparison g hg)
    (pullbackComparison_eq g hg) fib L'.fibre L.fibre hk

end ThickeningLift


/-- A morphism `f ≫ eqToHom e = g` of a transport identifies `g` with `f` heterogeneously. -/
theorem _root_.CategoryTheory.heq_of_comp_eqToHom_eq {C : Type*} [Category* C] {X Y Y' : C}
    (e : Y = Y') {f : X ⟶ Y} {g : X ⟶ Y'} (h : f ≫ eqToHom e = g) : HEq g f := by
  subst e
  simp only [eqToHom_refl, Category.comp_id] at h
  subst h
  rfl

/-- In a category fibred in groupoids, two objects of a fibre related by a morphism of the fibre
are isomorphic in the fibre. -/
theorem _root_.CategoryTheory.Functor.Fiber.isIsomorphic_of_hom {𝒳 𝒮 : Type*} {_ : Category* 𝒳}
    {_ : Category* 𝒮} {p : 𝒳 ⥤ 𝒮} (hp : p.IsFiberedInGroupoids) {S₀ : 𝒮} {a b : p.Fiber S₀}
    (φ : a ⟶ b) : IsIsomorphic a b := by
  have : p.IsHomLift (𝟙 S₀) φ.1 := φ.2
  have := hp.isStronglyCartesian_homLift (𝟙 S₀) φ.1
  have : IsIso φ.1 := Functor.IsStronglyCartesian.isIso_of_base_isIso p (𝟙 S₀) φ.1
  have : p.IsHomLift (Iso.refl S₀).hom (asIso φ.1).hom := φ.2
  have hinv : p.IsHomLift (𝟙 S₀) (asIso φ.1).inv := IsHomLift.inv_lift_inv p (Iso.refl S₀) _
  exact ⟨⟨φ, ⟨(asIso φ.1).inv, hinv⟩, Subtype.ext (asIso φ.1).hom_inv_id,
    Subtype.ext (asIso φ.1).inv_hom_id⟩⟩

/-- A morphism of objects under `x` whose right component lies over a transport lies, under
`Under.post p`, over the identity of the common image. -/
theorem _root_.CategoryTheory.Under.post_isHomLift_id_of_map_right {X C : Type*}
    {_ : Category* X} {_ : Category* C} (p : X ⥤ C) {x : X} {U : Under (p.obj x)}
    {a b : Under x} (ha : (Under.post p).obj a = U) (hb : (Under.post p).obj b = U) (f : a ⟶ b)
    (h : p.map f.right =
      eqToHom (congrArg Under.right ha) ≫ eqToHom (congrArg Under.right hb).symm) :
    (Under.post p).IsHomLift (𝟙 U) f := by
  refine IsHomLift.of_fac' _ _ _ ha hb ?_
  apply Under.UnderMorphism.ext
  rwa [Under.comp_right, Under.comp_right, Under.eqToHom_right, Under.eqToHom_right,
    Under.id_right, Category.id_comp]

/-! ### The class of a lift of `ξ` given by a morphism of `Coh_{X/Y}` -/

section LiftClassOf

variable {ξ : CoherentObject D} {T' : SchemesOver D.Y} {h : ξ.T ⟶ T'}

/-- **The class of the lift of `ξ` given by a morphism `m : ξ ⟶ A` of `Coh_{X/Y}`**, read across
`h` through an identification `A.T = T'` under which the base of `m` is `h`. -/
def liftClassOf (A : CoherentObject D) (m : CoherentHom ξ A) (hT : A.T = T')
    (hm : HEq m.base h) : D.ThickeningLiftClass ξ h := by
  subst hT
  cases eq_of_heq hm
  exact Quotient.mk _ (ThickeningLift.ofCoherentHom A m)

/-- Over the identification of test schemes by `rfl`, the class is the class of the lift
`AlgebraicGeometry.Space.CoherentSituation.ThickeningLift.ofCoherentHom`. -/
theorem liftClassOf_rfl (A : CoherentObject D) (m : CoherentHom ξ A) (hm : HEq m.base m.base) :
    liftClassOf A m rfl hm = Quotient.mk _ (ThickeningLift.ofCoherentHom A m) :=
  rfl

/-- **A morphism of `Coh_{X/Y}` over the identity into the object of a lift identifies the class
of `m` with the class of that lift.** -/
theorem liftClassOf_eq_mk_of_comp_eq (A : CoherentObject D) (m : CoherentHom ξ A)
    (hT : A.T = T') (hm : HEq m.base h) (L : D.ThickeningLift ξ h)
    (ψ : CoherentHom A L.toObject) (hψ : ψ.base = eqToHom hT) (hc : m.comp ψ = L.toHom) :
    liftClassOf A m hT hm = Quotient.mk _ L := by
  subst hT
  cases eq_of_heq hm
  rw [liftClassOf_rfl]
  exact Quotient.sound (ThickeningLift.isIsomorphic_of_comp_eq (ThickeningLift.ofCoherentHom A m)
    L ψ (hψ.trans (eqToHom_refl _ _)) hc)

/-- **Conversely**, if the class of `m` is the class of a lift, there are morphisms of
`Coh_{X/Y}` over the identity in both directions between the target of `m` and the object of the
lift, compatible with the arrows out of `ξ`. -/
theorem exists_comp_eq_of_liftClassOf_eq_mk (A : CoherentObject D) (m : CoherentHom ξ A)
    (hT : A.T = T') (hm : HEq m.base h) (L : D.ThickeningLift ξ h)
    (hL : liftClassOf A m hT hm = Quotient.mk _ L) :
    (∃ ψ : CoherentHom A L.toObject, ψ.base = eqToHom hT ∧ m.comp ψ = L.toHom) ∧
      ∃ χ : CoherentHom L.toObject A, χ.base = eqToHom hT.symm ∧ L.toHom.comp χ = m := by
  subst hT
  cases eq_of_heq hm
  rw [liftClassOf_rfl] at hL
  have H : (ThickeningLift.ofCoherentHom A m).IsIsomorphic L := Quotient.exact hL
  have H' : L.IsIsomorphic (ThickeningLift.ofCoherentHom A m) :=
    (ThickeningLift.setoid D ξ m.base).symm H
  exact ⟨⟨ThickeningLift.isoHom H.choose, (eqToHom_refl _ _).symm,
      ThickeningLift.comp_isoHom H.choose H.choose_spec⟩,
    ⟨ThickeningLift.isoHom H'.choose, (eqToHom_refl _ _).symm,
      ThickeningLift.comp_isoHom H'.choose H'.choose_spec⟩⟩

end LiftClassOf

/-! ### Lift classes of an object of `Coh_{X/Y}` along a morphism of the site -/

section FiberClasses

variable (hY : IsTerminal D.Y) {x : CoherentObject D} {U : BigFppfOver B S hS}
  {b : (coherentCFG D).val.p.obj x ⟶ U}

include hY in
/-- The test scheme of a lift of `x` along `b` is the test scheme of `U`. -/
theorem fiber_T_eq (y : (Under.post (coherentCFG D).val.p).Fiber (Under.mk b)) :
    y.1.right.T = D.terminalTestScheme hY U :=
  D.schemesOver_ext_of_isTerminal hY (congrArg (fun t => t.right) y.2)

/-- The arrow `x ⟶ y` of a lift of `x` along `b`, as a morphism of `Coh_{X/Y}`. -/
def fiberArrow (y : (Under.post (coherentCFG D).val.p).Fiber (Under.mk b)) :
    CoherentHom x y.1.right :=
  y.1.hom

/-- The arrow of a lift of `x` along `b` lies over `b`. -/
theorem terminalTestMap_comp_eqToHom
    (y : (Under.post (coherentCFG D).val.p).Fiber (Under.mk b)) :
    D.terminalTestMap hY x b ≫ eqToHom (fiber_T_eq hY y).symm = (fiberArrow y).base := by
  have hw := Under.w (eqToHom y.2)
  rw [Under.eqToHom_right] at hw
  have hw' : (coherentCFG D).val.p.map y.1.hom ≫ eqToHom (congrArg (fun t => t.right) y.2) =
      b := hw
  apply CostructuredArrow.hom_ext
  rw [CostructuredArrow.comp_left, CostructuredArrow.eqToHom_left]
  change b ≫ _ = (coherentCFG D).val.p.map y.1.hom
  exact (comp_eqToHom_iff _ _ _).2 hw'.symm

/-- The base of the arrow of a lift of `x` along `b` is the morphism of test schemes of `b`, read
through the identification of test schemes. -/
theorem fiber_base_heq (y : (Under.post (coherentCFG D).val.p).Fiber (Under.mk b)) :
    HEq (fiberArrow y).base (D.terminalTestMap hY x b) :=
  heq_of_comp_eqToHom_eq _ (terminalTestMap_comp_eqToHom hY y)

/-- A morphism of lifts of `x` along `b` lies over the identification of their test schemes. -/
theorem fiberHom_base {y y' : (Under.post (coherentCFG D).val.p).Fiber (Under.mk b)}
    (φ : y ⟶ y') :
    (φ.1.right : CoherentHom y.1.right y'.1.right).base =
      eqToHom ((fiber_T_eq hY y).trans (fiber_T_eq hY y').symm) := by
  have h1 : (coherentCFG D).val.p.IsHomLift (Under.Hom.right (𝟙 (Under.mk b))) φ.1.right :=
    Deformation.Artin.underPost_isHomLift_right _ (𝟙 (Under.mk b)) φ.1 φ.2
  have hfac := IsHomLift.fac' (coherentCFG D).val.p (Under.Hom.right (𝟙 (Under.mk b))) φ.1.right
  apply CostructuredArrow.hom_ext
  rw [CostructuredArrow.eqToHom_left]
  change (coherentCFG D).val.p.map φ.1.right = _
  rw [hfac]
  simp only [Under.id_right, Category.id_comp, eqToHom_trans]
  rfl

/-- Composing two equalities of composites of morphisms of `Coh_{X/Y}`. -/
private theorem comp_comp_eq_of_comp_eq {A₁ A₂ A₃ A₄ : CoherentObject D} {a : CoherentHom A₁ A₂}
    {b : CoherentHom A₂ A₃} {c : CoherentHom A₁ A₃} {d : CoherentHom A₃ A₄}
    {e : CoherentHom A₁ A₄} (hw : a.comp b = c) (hc : c.comp d = e) : a.comp (b.comp d) = e :=
  (CoherentHom.assoc (modulePushforwardCoherence B S hS) _ _ _).symm.trans
    ((congrArg (fun t => CoherentHom.comp t d) hw).trans hc)

/-- A lift `y` of `x` along `b` has its class represented by a lift `L` of the module of `x`, with
morphisms of `Coh_{X/Y}` over the identity in both directions between `y` and `L`. -/
private theorem exists_lift_of_fiber (y : (Under.post (coherentCFG D).val.p).Fiber (Under.mk b)) :
    ∃ L : D.ThickeningLift x (D.terminalTestMap hY x b),
      Quotient.mk _ L = liftClassOf y.1.right (fiberArrow y) (fiber_T_eq hY y)
        (fiber_base_heq hY y) ∧
      (∃ ψ : CoherentHom y.1.right L.toObject, ψ.base = eqToHom (fiber_T_eq hY y) ∧
        (fiberArrow y).comp ψ = L.toHom) ∧
      ∃ χ : CoherentHom L.toObject y.1.right, χ.base = eqToHom (fiber_T_eq hY y).symm ∧
        L.toHom.comp χ = fiberArrow y := by
  obtain ⟨L, hL⟩ := Quotient.exists_rep (liftClassOf y.1.right (fiberArrow y)
    (fiber_T_eq hY y) (fiber_base_heq hY y))
  exact ⟨L, hL, exists_comp_eq_of_liftClassOf_eq_mk _ _ _ _ L hL.symm⟩

/-- **The class of the lift of the module of `x` attached to a class of lifts of `x` along
`b`.** -/
def fiberLiftClass :
    Quotient (isIsomorphicSetoid ((Under.post (coherentCFG D).val.p).Fiber (Under.mk b))) →
      D.ThickeningLiftClass x (D.terminalTestMap hY x b) :=
  Quotient.lift (fun y => liftClassOf y.1.right (fiberArrow y) (fiber_T_eq hY y)
    (fiber_base_heq hY y)) (by
      rintro y y' ⟨e⟩
      obtain ⟨L, hL⟩ := Quotient.exists_rep (liftClassOf y'.1.right (fiberArrow y')
        (fiber_T_eq hY y') (fiber_base_heq hY y'))
      obtain ⟨⟨ψ', hψ', hc'⟩, -⟩ :=
        exists_comp_eq_of_liftClassOf_eq_mk _ _ _ _ L hL.symm
      have hw : (fiberArrow y).comp (e.hom.1.right : CoherentHom y.1.right y'.1.right) =
          fiberArrow y' := Under.w e.hom.1
      refine (liftClassOf_eq_mk_of_comp_eq _ _ _ _ L
        ((e.hom.1.right : CoherentHom y.1.right y'.1.right).comp ψ') ?_ ?_).trans hL
      · change (e.hom.1.right : CoherentHom y.1.right y'.1.right).base ≫ ψ'.base = _
        rw [fiberHom_base hY e.hom, hψ', eqToHom_trans]
      · exact (CoherentHom.assoc (modulePushforwardCoherence B S hS) _ _ _).symm.trans
          ((congrArg (fun t => CoherentHom.comp t ψ') hw).trans hc'))

/-- `fiberLiftClass` sends the class of a lift `y` of `x` along `b` to the class of the lift of
the module of `x` determined by `y`. -/
theorem fiberLiftClass_mk (y : (Under.post (coherentCFG D).val.p).Fiber (Under.mk b)) :
    D.fiberLiftClass hY (Quotient.mk _ y) =
      liftClassOf y.1.right (fiberArrow y) (fiber_T_eq hY y) (fiber_base_heq hY y) :=
  rfl

/-- **Two lifts of `x` along `b` related by a morphism of `Coh_{X/Y}` under `x` over the
identification of their test schemes are isomorphic**: the morphism is a morphism of the fibre,
and the fibres of a category fibred in groupoids are groupoids. -/
theorem isIsomorphic_of_coherentHom
    {y y' : (Under.post (coherentCFG D).val.p).Fiber (Under.mk b)}
    (Θ : CoherentHom y.1.right y'.1.right)
    (hΘ : Θ.base = eqToHom ((fiber_T_eq hY y).trans (fiber_T_eq hY y').symm))
    (hc : (fiberArrow y).comp Θ = fiberArrow y') : IsIsomorphic y y' := by
  refine Functor.Fiber.isIsomorphic_of_hom
    (Deformation.Artin.underPost_isFiberedInGroupoids _ (coherentCFG D).property x)
    (a := y) (b := y') ⟨Under.homMk (T := (coherentCFG D).val.obj)
      (Θ : y.1.right ⟶ y'.1.right) hc, Under.post_isHomLift_id_of_map_right _ y.2 y'.2 _ ?_⟩
  exact (congrArg CommaMorphism.left hΘ).trans
    ((CostructuredArrow.eqToHom_left _).trans (eqToHom_trans _ _).symm)

/-- **The class map on lifts of `x` along `b` is injective.** -/
theorem fiberLiftClass_injective : Function.Injective (D.fiberLiftClass hY (b := b)) := by
  intro c c' hcc
  induction c using Quotient.ind with | _ y => ?_
  induction c' using Quotient.ind with | _ y' => ?_
  rw [fiberLiftClass_mk, fiberLiftClass_mk] at hcc
  obtain ⟨L, hL, ⟨ψ, hψ, hc⟩, -⟩ := exists_lift_of_fiber hY y
  obtain ⟨-, ⟨χ, hχ, hc'⟩⟩ := exists_comp_eq_of_liftClassOf_eq_mk _ _ _ _ L (hcc.symm.trans hL.symm)
  refine Quotient.sound (isIsomorphic_of_coherentHom hY (ψ.comp χ) ?_ ?_)
  · change ψ.base ≫ χ.base = _
    rw [hψ, hχ, eqToHom_trans]
  · exact comp_comp_eq_of_comp_eq hc hc'

/-- **The class map on lifts of `x` along `b` is surjective**: a lift of the module is the lift
of `x` given by its arrow. -/
theorem fiberLiftClass_surjective : Function.Surjective (D.fiberLiftClass hY (b := b)) := by
  intro c
  induction c using Quotient.ind with | _ L => ?_
  let m : (show (coherentCFG D).val.obj from x) ⟶
      (show (coherentCFG D).val.obj from L.toObject) := L.toHom
  refine ⟨Quotient.mk _ ⟨Under.mk m, rfl⟩, ?_⟩
  exact liftClassOf_eq_mk_of_comp_eq L.toObject L.toHom (fiber_T_eq hY ⟨Under.mk m, rfl⟩)
    (fiber_base_heq hY ⟨Under.mk m, rfl⟩) L
    (CoherentHom.id (modulePushforwardCoherence B S hS) L.toObject) (eqToHom_refl _ _).symm
    (CoherentHom.comp_id _ _)

/-- **Classes of lifts of `x` along `b : T ⟶ U` are classes of lifts of its module to `X_U`.** -/
def fiberLiftClassEquiv :
    Quotient (isIsomorphicSetoid ((Under.post (coherentCFG D).val.p).Fiber (Under.mk b))) ≃
      D.ThickeningLiftClass x (D.terminalTestMap hY x b) :=
  Equiv.ofBijective _ ⟨fiberLiftClass_injective hY, fiberLiftClass_surjective hY⟩

/-- The bijection is the class map. -/
theorem fiberLiftClassEquiv_apply (c) :
    D.fiberLiftClassEquiv hY (b := b) c = D.fiberLiftClass hY c :=
  rfl

variable (D) in
/-- The morphism of test schemes induced by a morphism `V ⟶ U` of the site, over a final `Y`. -/
def terminalTestSchemeMap {V : BigFppfOver B S hS} (g : V ⟶ U) :
    D.terminalTestScheme hY V ⟶ D.terminalTestScheme hY U :=
  CostructuredArrow.homMk g (hY.hom_ext _ _)

/-- The morphism of test schemes of `b'` followed by that of `g` is the one of `b = b' ≫ g`. -/
theorem terminalTestMap_comp_terminalTestSchemeMap {V : BigFppfOver B S hS}
    {b' : (coherentCFG D).val.p.obj x ⟶ V} (g : V ⟶ U) (hg : b' ≫ g = b) :
    D.terminalTestMap hY x b' ≫ D.terminalTestSchemeMap hY g = D.terminalTestMap hY x b :=
  CostructuredArrow.hom_ext _ _ hg

/-- The base of a composite of three morphisms of `Coh_{X/Y}`, the outer two over
identifications of test schemes and the middle one over `G` read through such identifications. -/
theorem comp_comp_base_eq {A₁ A₂ A₃ A₄ : CoherentObject D} {T₁ T₄ : SchemesOver D.Y}
    (G : T₁ ⟶ T₄) (χ : CoherentHom A₁ A₂) (Φ : CoherentHom A₂ A₃) (ψ : CoherentHom A₃ A₄)
    (e₁ : A₁.T = A₂.T) (e₂ : A₂.T = T₁) (e₃ : T₄ = A₃.T) (e₄ : A₃.T = A₄.T) (e₅ : A₁.T = T₁)
    (e₆ : T₄ = A₄.T) (hχ : χ.base = eqToHom e₁) (hΦ : Φ.base = eqToHom e₂ ≫ G ≫ eqToHom e₃)
    (hψ : ψ.base = eqToHom e₄) :
    ((χ.comp Φ).comp ψ).base = eqToHom e₅ ≫ G ≫ eqToHom e₆ := by
  change (χ.base ≫ Φ.base) ≫ ψ.base = _
  rw [hχ, hΦ, hψ]
  simp

/-- A morphism of test schemes over a final `Y` is determined by its morphism of the site. -/
theorem eq_eqToHom_comp_terminalTestSchemeMap {A A' : CoherentObject D} {V : BigFppfOver B S hS}
    (hV : A.T = D.terminalTestScheme hY V) (hU : D.terminalTestScheme hY U = A'.T)
    (Φ : CoherentHom A A') (g : V ⟶ U)
    (h : Φ.base.left = eqToHom (congrArg CostructuredArrow.left hV) ≫ g ≫
      eqToHom (congrArg CostructuredArrow.left hU)) :
    Φ.base = eqToHom hV ≫ D.terminalTestSchemeMap hY g ≫ eqToHom hU := by
  apply CostructuredArrow.hom_ext
  rw [h, CostructuredArrow.comp_left, CostructuredArrow.comp_left, CostructuredArrow.eqToHom_left,
    CostructuredArrow.eqToHom_left]
  rfl

/-- **Naturality of the class map**: if a lift `y_V` of `x` along `b'` maps to a lift `y_U` along
`b = b' ≫ g` by a morphism of `Coh_{X/Y}` under `x` lying over `g`, then the class of `y_V` is the
pullback along `g` of the class of `y_U`. -/
theorem fiberLiftClass_naturality {V : BigFppfOver B S hS}
    {b' : (coherentCFG D).val.p.obj x ⟶ V} (g : V ⟶ U) (hg : b' ≫ g = b)
    (yU : (Under.post (coherentCFG D).val.p).Fiber (Under.mk b))
    (yV : (Under.post (coherentCFG D).val.p).Fiber (Under.mk b'))
    (φ : yV.1.right ⟶ yU.1.right) (hφ : (coherentCFG D).val.p.IsHomLift g φ)
    (hw : yV.1.hom ≫ φ = yU.1.hom) :
    D.fiberLiftClass hY (Quotient.mk _ yV) =
      ThickeningLiftClass.pullback (D.terminalTestSchemeMap hY g)
        (terminalTestMap_comp_terminalTestSchemeMap hY g hg)
        (D.fiberLiftClass hY (Quotient.mk _ yU)) := by
  rw [fiberLiftClass_mk, fiberLiftClass_mk]
  obtain ⟨LU, hLU, ⟨ψU, hψU, hcU⟩, -⟩ := exists_lift_of_fiber hY yU
  obtain ⟨LV, hLV, -, χV, hχV, hcV⟩ := exists_lift_of_fiber hY yV
  rw [← hLU, ← hLV, ThickeningLiftClass.pullback_mk, ThickeningLift.pullback_eq_pullbackLift]
  have hw' : (fiberArrow yV).comp (φ : CoherentHom yV.1.right yU.1.right) = fiberArrow yU := hw
  have hfac := IsHomLift.fac' (coherentCFG D).val.p g φ
  have hb := eq_eqToHom_comp_terminalTestSchemeMap hY (fiber_T_eq hY yV) (fiber_T_eq hY yU).symm
    (φ : CoherentHom yV.1.right yU.1.right) g hfac
  have hΦ : ((χV.comp (φ : CoherentHom yV.1.right yU.1.right)).comp ψU).base =
      D.terminalTestSchemeMap hY g :=
    (comp_comp_base_eq _ χV _ ψU _ _ _ _ rfl rfl hχV hb hψU).trans (by simp)
  have hc : LV.toHom.comp ((χV.comp (φ : CoherentHom yV.1.right yU.1.right)).comp ψU) =
      LU.toHom :=
    comp_comp_eq_of_comp_eq (comp_comp_eq_of_comp_eq hcV hw') hcU
  revert hΦ hc
  generalize (χV.comp (φ : CoherentHom yV.1.right yU.1.right)).comp ψU = Θ
  obtain ⟨g', fib, hfib⟩ := Θ
  intro hΦ hc
  change g' = _ at hΦ
  subst hΦ
  exact Quotient.sound (ThickeningLift.isIsomorphic_pullbackLift_of_comp_eq LU LV _ fib hfib hc _)

end FiberClasses

end AlgebraicGeometry.Space.CoherentSituation
