module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Algebraic.RepresentableBySpace.Characterization
public import StacksFrontier.AlgebraicGeometry.Stacks.PresheafRepresentability
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityInvariance
public import StacksFrontier.CategoryTheory.FiberedCategory.FiberedInSetoids
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Fibrewise
public import StacksFrontier.CategoryTheory.FiberedInSetoids.TwoCategory

/-!
# Representability of a morphism of categories fibred in setoids

A 1-morphism of categories fibred in setoids over the big fppf site of a scheme `S` is
representable by algebraic spaces exactly when the map it induces on the presheaves of
isomorphism classes is.

## Main results

* `AlgebraicGeometry.Stack.isoClassMap_isRepresentableByAlgebraicSpaces_iff`: a 1-morphism `f`
  of categories fibred in setoids is representable by algebraic spaces exactly when the induced
  map of presheaves of isomorphism classes is.

## References

* [Stacks Project, Tag 04SY](https://stacks.math.columbia.edu/tag/04SY)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v w z a uS vS uA vA uB vB

private theorem isoClassMk_transport
    {C : Type (u + 1)} [Category.{u} C] {D : Type w} [Category.{v} D]
    (p : D ⥤ C) [p.IsFibered] {x : D} {U V : C} (h : U = V)
    (hu : p.obj x = U) (hv : p.obj x = V) :
    Eq.rec (Discrete.mk (Functor.isoClassMk p (⟨x, hu⟩ : p.Fiber U)))
      (congrArg (fun Z => Discrete (p.isoClassPresheaf.obj (Opposite.op Z))) h) =
    Discrete.mk (Functor.isoClassMk p (⟨x, hv⟩ : p.Fiber V)) := by
  cases h
  rfl

private theorem cast_type_eq_of_proof_irrel
    {A B : Sort u} (h₁ h₂ : A = B) (a : A) : cast h₁ a = cast h₂ a :=
  rfl

/-- For based functors `F G : 𝒜 ⥤ᵇ ℬ` and `h : F.obj x = G.obj x`, the morphism `eqToHom h`
lies over the identity of `𝒜.p.obj x`. -/
theorem based_eqToHom_isHomLift
    {𝒮 : Type uS} [Category.{vS} 𝒮]
    {𝒜 : BasedCategory.{vA, uA} 𝒮} {ℬ : BasedCategory.{vB, uB} 𝒮}
    (F G : 𝒜 ⥤ᵇ ℬ) (x : 𝒜.obj) (h : F.obj x = G.obj x) :
    ℬ.p.IsHomLift (𝟙 (𝒜.p.obj x)) (eqToHom h) := by
  apply IsHomLift.of_fac' (p := ℬ.p) (𝟙 (𝒜.p.obj x)) (eqToHom h)
    (F.w_obj x) (G.w_obj x)
  simp only [eqToHom_map, eqToHom_trans, Category.id_comp]

/-- Let `q` be fibred in setoids and let `G H : D ⥤ E` be functors over `C`. If for every `x`
there is a morphism `G.obj x ⟶ H.obj x` lying over the identity, then there is a unique
isomorphism `G ≅ H` whose components lie over identities. -/
theorem existsUnique_verticalIso_of_forall_exists_verticalHom
    {C : Type (u + 1)} [Category.{u} C]
    {D : Type w} [Category.{v} D] {E : Type z} [Category.{a} E]
    {p : D ⥤ C} {q : E ⥤ C} [hq : q.IsFiberedInSetoids]
    {G H : D ⥤ E} (hG : G ⋙ q = p) (hH : H ⋙ q = p)
    (h : ∀ x : D, ∃ θ : G.obj x ⟶ H.obj x,
      q.IsHomLift (𝟙 (p.obj x)) θ) :
    ∃! e : G ≅ H, ∀ x : D, q.IsHomLift (𝟙 (p.obj x)) (e.hom.app x) := by
  classical
  have hθ : ∀ x : D, q.IsHomLift (𝟙 (p.obj x)) (h x).choose := fun x =>
    (h x).choose_spec
  have huniq : ∀ {x : D} (θ' : G.obj x ⟶ H.obj x),
      q.IsHomLift (𝟙 (p.obj x)) θ' → θ' = (h x).choose := fun {x} θ' h' =>
    CategoryTheory.Functor.hom_unique_of_fiber_isThin q (𝟙 (p.obj x))
      (hq.fiber_isThin (p.obj x))
      θ' (h x).choose h' (hθ x)
  have hnat : ∀ {x y : D} (ψ : x ⟶ y),
      G.map ψ ≫ (h y).choose = (h x).choose ≫ H.map ψ := by
    intro x y ψ
    have h1 : q.IsHomLift (p.map ψ) (G.map ψ ≫ (h y).choose) := by
      have := CategoryTheory.Functor.isHomLift_map_of_comp_eq hG (p.map ψ) ψ
      have := hθ y
      exact IsHomLift.comp_lift_id_right' q (p.map ψ) (G.map ψ) (p.obj y) (h y).choose
    have h2 : q.IsHomLift (p.map ψ) ((h x).choose ≫ H.map ψ) := by
      have := CategoryTheory.Functor.isHomLift_map_of_comp_eq hH (p.map ψ) ψ
      have := hθ x
      exact IsHomLift.comp_lift_id_left' q (p.obj x) (h x).choose (p.map ψ) (H.map ψ)
    exact CategoryTheory.Functor.hom_unique_of_fiber_isThin q (p.map ψ)
      (hq.fiber_isThin (p.obj x)) _ _ h1 h2
  let t : G ⟶ H := { app := fun x => (h x).choose, naturality := fun _ _ ψ => hnat ψ }
  have hiso : ∀ x : D, IsIso (t.app x) := fun x => by
    have := hθ x
    have := hq.isFiberedInGroupoids.isStronglyCartesian_homLift
      (𝟙 (p.obj x)) (t.app x)
    exact Functor.IsStronglyCartesian.isIso_of_base_isIso q (𝟙 (p.obj x)) (t.app x)
  have : IsIso t := NatIso.isIso_of_isIso_app t
  exact ⟨asIso t, hθ, fun e he =>
    Iso.ext (NatTrans.ext (funext fun x => huniq _ (he x)))⟩

section IsoClassComparison

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The equivalence over the site of a category fibred in setoids with the category of elements
of its presheaf of isomorphism classes. -/
noncomputable def isoClassEquivalenceOver
    (𝒳 : CatFiberedInSetoids.{u, v, u + 1, u} (BigFppfOver B S hS)) :
    StacksRepresentableCFG.EquivalenceOver 𝒳.val.p
      (presheafOfCategories (𝒳.val.p.isoClassPresheaf ⋙ typeToCat)).p :=
  equivalenceOver_elements_of_setoids 𝒳.val.p 𝒳.val.p.isoClassPresheaf
    (fun _ => Equiv.refl _) (by intro U V g x; rfl)

/-- `AlgebraicGeometry.Stack.isoClassEquivalenceOver` as a based functor into the category
fibred in groupoids attached to the isomorphism-class presheaf. -/
noncomputable def isoClassBasedFunctor
    (𝒳 : CatFiberedInSetoids.{u, v, u + 1, u} (BigFppfOver B S hS)) :
    𝒳.val ⥤ᵇ (fibredCategory B S hS 𝒳.val.p.isoClassPresheaf).val :=
  ⟨(isoClassEquivalenceOver B S hS 𝒳).hom.functor,
    (isoClassEquivalenceOver B S hS 𝒳).hom.w⟩

variable {𝒳 𝒴 : CatFiberedInSetoids.{u, v, u + 1, u} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    (a : 𝒳.val.p.isoClassPresheaf ⟶ 𝒴.val.p.isoClassPresheaf)

/-- The based functors `isoClassBasedFunctor 𝒳` followed by the 1-morphism attached to `a`, and
`f` followed by `isoClassBasedFunctor 𝒴`, agree on objects. -/
theorem isoClassComparison_obj_eq
    (ha : ∀ (U : BigFppfOver B S hS) (x : 𝒳.val.p.Fiber U),
      a.app (Opposite.op U) (Functor.isoClassMk 𝒳.val.p x) =
        Functor.isoClassMk 𝒴.val.p
          ((Functor.Fiber.mapOfComp 𝒳.val.p 𝒴.val.p
            (CatFiberedInGroupoids.homFunctor f)
            (CatFiberedInGroupoids.homFunctor_comp_p f) U).obj x))
    (x : 𝒳.val.obj) :
    (BasedFunctor.comp (isoClassBasedFunctor B S hS 𝒳)
        (associatedMap B S hS a).1.hom).obj x =
      (BasedFunctor.comp (CatFiberedInSetoids.inclusion.map f).hom
        (isoClassBasedFunctor B S hS 𝒴)).obj x := by
  let pX := 𝒳.val.p
  let pY := 𝒴.val.p
  let F := pX.isoClassPresheaf
  let G := pY.isoClassPresheaf
  let f' := CatFiberedInSetoids.inclusion.map f
  let f'' := (AlgebraicGeometry.Stack.associatedMap B S hS a).1
  let XF := fibredCategory B S hS F
  let YG := fibredCategory B S hS G
  let ax := isoClassBasedFunctor B S hS 𝒳
  let lhs := BasedFunctor.comp ax f''.hom
  let rhs := BasedFunctor.comp f'.hom (isoClassBasedFunctor B S hS 𝒴)
  apply (PresheafOfCategories.objEquiv (G ⋙ typeToCat)).injective
  apply Sigma.ext
  · show YG.val.p.obj (lhs.obj x) = YG.val.p.obj (rhs.obj x)
    calc
      YG.val.p.obj (lhs.obj x) = 𝒳.val.p.obj x := BasedFunctor.w_obj lhs x
      _ = (CatFiberedInSetoids.inclusion.obj 𝒳).val.p.obj x := rfl
      _ = YG.val.p.obj (rhs.obj x) := (BasedFunctor.w_obj rhs x).symm
  · let z := ax.obj x
    have hzbase : z.base = pX.obj x := BasedFunctor.w_obj ax x
    have hzclass : Discrete.as
        (show Discrete (F.obj (Opposite.op z.base)) from z.fiber) =
        Functor.isoClassMk pX ⟨x, hzbase.symm⟩ := by
      rfl
    let xF : pX.Fiber z.base := ⟨x, hzbase.symm⟩
    let yF := (Functor.Fiber.mapOfComp pX pY
      (CatFiberedInGroupoids.homFunctor f)
      (CatFiberedInGroupoids.homFunctor_comp_p f) z.base).obj xF
    have hassoc : HEq (lhs.obj x).fiber
        (Discrete.mk (a.app (Opposite.op z.base)
          (Discrete.as (show Discrete (F.obj (Opposite.op z.base)) from z.fiber)))) :=
      (AlgebraicGeometry.Stack.associatedMap B S hS a).property z
    have hvalue := ha z.base xF
    have hmid : HEq
        (Discrete.mk (a.app (Opposite.op z.base)
          (Discrete.as (show Discrete (F.obj (Opposite.op z.base)) from z.fiber))))
        (Discrete.mk (Functor.isoClassMk pY yF)) := by
      rw [hzclass]
      simpa [F, G, Functor.isoClassPresheaf] using
        heq_of_eq (congrArg Discrete.mk hvalue)
    let yF' : pY.Fiber z.base :=
      ⟨f'.hom.toFunctor.obj x, (BasedFunctor.w_obj f'.hom x).trans hzbase.symm⟩
    have hyF : yF = yF' := Subtype.ext rfl
    have hrbase : (rhs.obj x).base = z.base := by
      calc
        (rhs.obj x).base = (CatFiberedInSetoids.inclusion.obj 𝒳).val.p.obj x := by
          show YG.val.p.obj (rhs.obj x) = _
          exact BasedFunctor.w_obj rhs x
        _ = pX.obj x := rfl
        _ = z.base := hzbase.symm
    have htype : Discrete (G.obj (Opposite.op (rhs.obj x).base)) =
        Discrete (G.obj (Opposite.op z.base)) :=
      congrArg (fun U => Discrete (G.obj (Opposite.op U))) hrbase
    have hxU : pY.obj (f'.hom.obj x) = (rhs.obj x).base := rfl
    have hxV : pY.obj (f'.hom.obj x) = z.base := yF'.property
    have hrhsfiber : (rhs.obj x).fiber =
        Discrete.mk (Functor.isoClassMk pY
          (⟨f'.hom.obj x, hxU⟩ : pY.Fiber ((rhs.obj x).base))) := rfl
    have hlast : HEq (Discrete.mk (Functor.isoClassMk pY yF)) (rhs.obj x).fiber := by
      rw [hyF]
      have hcast : Eq.rec (rhs.obj x).fiber htype = Discrete.mk (Functor.isoClassMk pY yF') := by
        have htype' := congrArg
          (fun U => Discrete (G.obj (Opposite.op U))) (hxU.symm.trans hxV)
        rw [hrhsfiber]
        show cast htype (Discrete.mk (Functor.isoClassMk pY
            (⟨f'.hom.obj x, hxU⟩ : pY.Fiber ((rhs.obj x).base)))) = _
        calc
          _ = cast htype' (Discrete.mk (Functor.isoClassMk pY
              (⟨f'.hom.obj x, hxU⟩ : pY.Fiber ((rhs.obj x).base)))) :=
            cast_type_eq_of_proof_irrel htype htype' _
          _ = Discrete.mk (Functor.isoClassMk pY yF') :=
            isoClassMk_transport pY (hxU.symm.trans hxV) hxU hxV
      exact (heq_of_eqRec_eq htype hcast).symm
    exact hassoc.trans (hmid.trans hlast)

/-- The 2-isomorphism between `isoClassBasedFunctor 𝒳` followed by the 1-morphism attached to the
induced map `a` of isomorphism-class presheaves, and `f` followed by `isoClassBasedFunctor 𝒴`. -/
noncomputable def isoClassComparisonIso
    (ha : ∀ (U : BigFppfOver B S hS) (x : 𝒳.val.p.Fiber U),
      a.app (Opposite.op U) (Functor.isoClassMk 𝒳.val.p x) =
        Functor.isoClassMk 𝒴.val.p
          ((Functor.Fiber.mapOfComp 𝒳.val.p 𝒴.val.p
            (CatFiberedInGroupoids.homFunctor f)
            (CatFiberedInGroupoids.homFunctor_comp_p f) U).obj x)) :
    BasedFunctor.comp (isoClassBasedFunctor B S hS 𝒳)
        (associatedMap B S hS a).1.hom ≅
      BasedFunctor.comp (CatFiberedInSetoids.inclusion.map f).hom
        (isoClassBasedFunctor B S hS 𝒴) := by
  let lhs := BasedFunctor.comp (isoClassBasedFunctor B S hS 𝒳) (associatedMap B S hS a).1.hom
  let rhs := BasedFunctor.comp (CatFiberedInSetoids.inclusion.map f).hom
    (isoClassBasedFunctor B S hS 𝒴)
  let q := (fibredCategory B S hS 𝒴.val.p.isoClassPresheaf).val.p
  letI : q.IsFiberedInSetoids :=
    elementsProjection_isFiberedInSetoids 𝒴.val.p.isoClassPresheaf
  have hvertical : ∀ x : 𝒳.val.obj,
      q.IsHomLift (𝟙 (𝒳.val.p.obj x))
        (eqToHom (isoClassComparison_obj_eq B S hS f a ha x)) :=
    fun x => based_eqToHom_isHomLift (𝒜 := 𝒳.val)
      (ℬ := (fibredCategory B S hS 𝒴.val.p.isoClassPresheaf).val) lhs rhs x
      (isoClassComparison_obj_eq B S hS f a ha x)
  have niResult :=
    existsUnique_verticalIso_of_forall_exists_verticalHom
      (p := 𝒳.val.p) (q := q) (G := lhs.toFunctor) (H := rhs.toFunctor)
    lhs.w rhs.w
      (fun x => ⟨eqToHom (isoClassComparison_obj_eq B S hS f a ha x), hvertical x⟩)
  exact BasedNatIso.mkNatIso niResult.choose niResult.choose_spec.1

end IsoClassComparison


/-- For categories fibred in setoids, representability by algebraic spaces of
the induced map of isomorphism-class presheaves is equivalent to
representability of the original morphism. -/
@[stacks 04SY]
public theorem isoClassMap_isRepresentableByAlgebraicSpaces_iff
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : CatFiberedInSetoids.{u, v, u + 1, u}
      (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    (a : 𝒳.val.p.isoClassPresheaf ⟶ 𝒴.val.p.isoClassPresheaf)
    (ha : ∀ (U : BigFppfOver B S hS) (x : 𝒳.val.p.Fiber U),
      a.app (Opposite.op U) (Functor.isoClassMk 𝒳.val.p x) =
        Functor.isoClassMk 𝒴.val.p
          ((Functor.Fiber.mapOfComp 𝒳.val.p 𝒴.val.p
            (CatFiberedInGroupoids.homFunctor f)
            (CatFiberedInGroupoids.homFunctor_comp_p f) U).obj x)) :
    AlgebraicGeometry.Space.IsRepresentableByAlgebraicSpaces B S hS
        a ↔
      AlgebraicGeometry.Stack.IsRepresentableByAlgebraicSpaces B S hS
        (CatFiberedInSetoids.inclusion.map f).hom := by
  have hbridge := @AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_iff_of_equivalences
    B S hS (CatFiberedInSetoids.inclusion.obj 𝒳)
    (fibredCategory B S hS 𝒳.val.p.isoClassPresheaf)
    (CatFiberedInSetoids.inclusion.obj 𝒴)
    (fibredCategory B S hS 𝒴.val.p.isoClassPresheaf)
    (CatFiberedInSetoids.inclusion.map f).hom (associatedMap B S hS a).1.hom
    (isoClassBasedFunctor B S hS 𝒳) (isoClassBasedFunctor B S hS 𝒴)
    (isoClassComparisonIso B S hS f a ha)
    (show Functor.IsEquivalence (isoClassBasedFunctor B S hS 𝒳).toFunctor from
      (isoClassEquivalenceOver B S hS 𝒳).toEquivalence.isEquivalence_functor)
    (show Functor.IsEquivalence (isoClassBasedFunctor B S hS 𝒴).toFunctor from
      (isoClassEquivalenceOver B S hS 𝒴).toEquivalence.isEquivalence_functor)
  exact (isRepresentableByAlgebraicSpaces_iff_associatedMap B S hS a).trans hbridge

end AlgebraicGeometry.Stack

end
