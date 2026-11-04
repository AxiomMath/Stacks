module

public import StacksFrontier.AlgebraicGeometry.Stacks.FullSubcategoryBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.IsoClassPresheafUniverseModel
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityPostcomp
public import StacksFrontier.AlgebraicGeometry.Stacks.SecondDiagonal

/-!
# The fibres of the diagonal of a category fibred in groupoids

Let `𝒳` be a category fibred in groupoids over the big fppf site of a scheme `S`, let `V` be an
object of that site and let `y : (Sch/V)_{fppf} ⟶ 𝒳 × 𝒳` be a point of `𝒳 × 𝒳` over `V`,
given (2-Yoneda) as a functor over the site. The proof of Stacks 07Y5 studies the 2-fibre product

`𝒴 = 𝒳 ×_{Δ, 𝒳 × 𝒳, y} (Sch/V)_{fppf}`

as a category over `(Sch/V)_{fppf}` through its projection to the second factor. This file shows
that `𝒴` is fibred in setoids over `(Sch/V)_{fppf}` (the observation of the proof that refers to
Stacks 04SI) and that its presheaf of isomorphism classes, the functor `Y` of the proof, takes
`u`-small values, so that it has a model valued in `Type u`.

## Main definitions

* `AlgebraicGeometry.Stack.diagonalPointFibre`: the projection `𝒴 ⟶ (Sch/V)_{fppf}`.
* `AlgebraicGeometry.Stack.diagonalPointFunctor`: the functor `Y` of isomorphism classes of
  `𝒴`, valued in `Type u`.
* `AlgebraicGeometry.Stack.diagonalPointFibreEquivalenceOver`: the equivalence over
  `(Sch/V)_{fppf}` of `𝒴` with the category fibred in sets attached to `Y`.

## Main results

* `AlgebraicGeometry.Stack.diagonalPointFibre_isFiberedInSetoids`: `𝒴` is fibred in setoids.
* `AlgebraicGeometry.Stack.small_isoClassPresheaf_diagonalPointFibre`: its presheaf of
  isomorphism classes is `u`-small. An object of `𝒴` over `T` is an object `x` of `𝒳` over `T`
  with an isomorphism `(x, x) ≅ y|_T`; its class is determined by the isomorphism
  `y₁|_T ≅ y₂|_T` that the two components produce, a morphism of `𝒳`.

## References

* [Stacks Project, Tag 07Y5](https://stacks.math.columbia.edu/tag/07Y5)
* [Stacks Project, Tag 04SI](https://stacks.math.columbia.edu/tag/04SI)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.TwoFibreProductOver

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

section Components

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {𝒴 : Type u₃} [Category.{v₃} 𝒴] {𝒮 : Type u₄} [Category.{v₄} 𝒮]
  {p𝒳 : 𝒳 ⥤ 𝒞} {p𝒴 : 𝒴 ⥤ 𝒞} {p𝒮 : 𝒮 ⥤ 𝒞} {F : 𝒳 ⥤ 𝒮} {G : 𝒴 ⥤ 𝒮}

/-- A morphism of a 2-fibre product lying over `f` in `𝒞` has its first component over `f`. -/
lemma isHomLift_a_of_isHomLift {P Q : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G} {R S : 𝒞}
    (f : R ⟶ S) (φ : P ⟶ Q) [h : (structureFunctor p𝒳 p𝒴 p𝒮 F G).IsHomLift f φ] :
    p𝒳.IsHomLift f φ.a := by
  cases h
  exact Hom.ha φ

/-- A morphism of a 2-fibre product lying over `f` in `𝒞` has its second component over `f`. -/
lemma isHomLift_b_of_isHomLift {P Q : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G} {R S : 𝒞}
    (f : R ⟶ S) (φ : P ⟶ Q) [h : (structureFunctor p𝒳 p𝒴 p𝒮 F G).IsHomLift f φ] :
    p𝒴.IsHomLift f φ.b := by
  cases h
  exact Hom.hb φ

/-- For an isomorphism `α` of 2-fibre products, `α.hom.a ≫ α.inv.a` is the identity. -/
@[reassoc (attr := simp)]
lemma hom_inv_id_a {P Q : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G} (α : P ≅ Q) :
    α.hom.a ≫ α.inv.a = 𝟙 P.x := by
  rw [← comp_a, α.hom_inv_id, id_a]

/-- For an isomorphism `α` of 2-fibre products, `α.inv.a ≫ α.hom.a` is the identity. -/
@[reassoc (attr := simp)]
lemma inv_hom_id_a {P Q : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G} (α : P ≅ Q) :
    α.inv.a ≫ α.hom.a = 𝟙 Q.x := by
  rw [← comp_a, α.inv_hom_id, id_a]

/-- For an isomorphism `α` of 2-fibre products, `α.hom.b ≫ α.inv.b` is the identity. -/
@[reassoc (attr := simp)]
lemma hom_inv_id_b {P Q : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G} (α : P ≅ Q) :
    α.hom.b ≫ α.inv.b = 𝟙 P.y := by
  rw [← comp_b, α.hom_inv_id, id_b]

/-- For an isomorphism `α` of 2-fibre products, `α.inv.b ≫ α.hom.b` is the identity. -/
@[reassoc (attr := simp)]
lemma inv_hom_id_b {P Q : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G} (α : P ≅ Q) :
    α.inv.b ≫ α.hom.b = 𝟙 Q.y := by
  rw [← comp_b, α.inv_hom_id, id_b]

end Components

section DiagonalPoint

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒯 : Type u₂} [Category.{v₂} 𝒯]
  {𝒮 : Type u₃} [Category.{v₃} 𝒮]
  (pT : 𝒯 ⥤ 𝒞) (p : 𝒮 ⥤ 𝒞) (y : 𝒯 ⥤ TwoFibreProductOver p p (𝟭 𝒞) p p)

/-- The 2-fibre product `𝒯 ×_{y, 𝒮 × 𝒮, Δ} 𝒮` of a point `y` of `𝒮 × 𝒮` and the diagonal. -/
abbrev DiagonalPoint : Type _ :=
  TwoFibreProductOver pT p (structureFunctor p p (𝟭 𝒞) p p) y (diagonal (Functor.comp_id p))

variable {pT p y}

-- The components of `Δ x` are `x` itself; composing with them needs that at instance
-- transparency, as in `CategoryTheory.FiberedInGroupoids.Diagonal`.
attribute [local instance_reducible] diagonal

/-- The isomorphism `y₁ ⟶ y₂` of the two components of `y` at the base of an object of the
2-fibre product `𝒯 ×_{y, 𝒮 × 𝒮, Δ} 𝒮`, obtained by composing its two comparison isomorphisms. -/
def DiagonalPoint.twist (P : DiagonalPoint pT p y) : (y.obj P.x).x ⟶ (y.obj P.x).y :=
  P.iso.hom.a ≫ P.iso.inv.b

/-- Two objects of `𝒯 ×_{y, 𝒮 × 𝒮, Δ} 𝒮` over the same object of `𝒯` with the same twist are
joined by a morphism whose `𝒯`-component is the identity. -/
lemma DiagonalPoint.exists_hom_of_twist_eq (x : 𝒯) (sP sQ : 𝒮) (hxP : pT.obj x = p.obj sP)
    (hxQ : pT.obj x = p.obj sQ)
    (iP : y.obj x ≅ (diagonal (Functor.comp_id p)).obj sP)
    (iQ : y.obj x ≅ (diagonal (Functor.comp_id p)).obj sQ)
    (vP : (structureFunctor p p (𝟭 𝒞) p p).IsHomLift (𝟙 (pT.obj x)) iP.hom)
    (vQ : (structureFunctor p p (𝟭 𝒞) p p).IsHomLift (𝟙 (pT.obj x)) iQ.hom)
    (h : iP.hom.a ≫ iP.inv.b = iQ.hom.a ≫ iQ.inv.b) :
    ∃ φ : (⟨pT.obj x, x, sP, rfl, hxP.symm, iP, vP⟩ : DiagonalPoint pT p y) ⟶
      ⟨pT.obj x, x, sQ, rfl, hxQ.symm, iQ, vQ⟩, φ.a = 𝟙 x ∧ φ.hbase = 𝟙 (pT.obj x) := by
  have h₁ : p.IsHomLift (𝟙 (pT.obj x)) iP.inv.a := by
    have : (structureFunctor p p (𝟭 𝒞) p p).IsHomLift (𝟙 (pT.obj x)) iP.inv := inferInstance
    exact isHomLift_a_of_isHomLift _ iP.inv
  have h₂ : p.IsHomLift (𝟙 (pT.obj x)) iQ.hom.a := isHomLift_a_of_isHomLift _ iQ.hom
  have e : iP.inv.b ≫ iQ.hom.b = iP.inv.a ≫ iQ.hom.a := by
    simpa using congrArg (fun k => iP.inv.a ≫ k ≫ iQ.hom.b) h
  have hb : iQ.hom.b = iP.hom.b ≫ iP.inv.a ≫ iQ.hom.a := by
    rw [← e, hom_inv_id_b_assoc]
  let φ : (⟨pT.obj x, x, sP, rfl, hxP.symm, iP, vP⟩ : DiagonalPoint pT p y) ⟶
      ⟨pT.obj x, x, sQ, rfl, hxQ.symm, iQ, vQ⟩ :=
    { hbase := 𝟙 (pT.obj x)
      a := 𝟙 x
      b := iP.inv.a ≫ iQ.hom.a
      ha := inferInstance
      hb := inferInstance
      w := by
        refine Hom.ext' ?_ ?_
        · show (y.map (𝟙 x) ≫ iQ.hom).a = (iP.hom ≫ (diagonal _).map (iP.inv.a ≫ iQ.hom.a)).a
          rw [comp_a, comp_a, Functor.map_id, id_a, diagonal_map_a]
          show 𝟙 _ ≫ iQ.hom.a = iP.hom.a ≫ iP.inv.a ≫ iQ.hom.a
          simp
        · show (y.map (𝟙 x) ≫ iQ.hom).b = (iP.hom ≫ (diagonal _).map (iP.inv.a ≫ iQ.hom.a)).b
          rw [comp_b, comp_b, Functor.map_id, id_b, diagonal_map_b]
          show 𝟙 _ ≫ iQ.hom.b = iP.hom.b ≫ iP.inv.a ≫ iQ.hom.a
          rw [Category.id_comp]
          exact hb }
  exact ⟨φ, rfl, rfl⟩

/-- Every fibre of `𝒯 ×_{y, 𝒮 × 𝒮, Δ} 𝒮 ⟶ 𝒯` is thin. -/
lemma DiagonalPoint.fiber_isThin (x : 𝒯) :
    Quiver.IsThin ((fst pT p (structureFunctor p p (𝟭 𝒞) p p) y
      (diagonal (Functor.comp_id p))).Fiber x) :=
  have := faithful_diagonal (Functor.comp_id p)
  fiber_isThin_fst_of_faithful x

/-- The twist of an object of the fibre over `x`, transported to `x`. -/
def DiagonalPoint.fiberTwist {x : 𝒯}
    (P : (fst pT p (structureFunctor p p (𝟭 𝒞) p p) y
      (diagonal (Functor.comp_id p))).Fiber x) : (y.obj x).x ⟶ (y.obj x).y :=
  eqToHom (congrArg (fun t => (y.obj t).x) (show P.1.x = x from P.2).symm) ≫
    DiagonalPoint.twist P.1 ≫ eqToHom (congrArg (fun t => (y.obj t).y) (show P.1.x = x from P.2))

/-- Two objects of a fibre of `𝒯 ×_{y, 𝒮 × 𝒮, Δ} 𝒮 ⟶ 𝒯` with the same twist are isomorphic. -/
lemma DiagonalPoint.nonempty_iso_of_fiberTwist_eq {x : 𝒯}
    (P Q : (fst pT p (structureFunctor p p (𝟭 𝒞) p p) y
      (diagonal (Functor.comp_id p))).Fiber x)
    (h : DiagonalPoint.fiberTwist P = DiagonalPoint.fiberTwist Q) : Nonempty (P ≅ Q) := by
  have hthin := DiagonalPoint.fiber_isThin (pT := pT) (p := p) (y := y) x
  suffices H : ∀ (P Q : (fst pT p (structureFunctor p p (𝟭 𝒞) p p) y
      (diagonal (Functor.comp_id p))).Fiber x),
      DiagonalPoint.fiberTwist P = DiagonalPoint.fiberTwist Q → Nonempty (P ⟶ Q) by
    obtain ⟨f⟩ := H P Q h
    obtain ⟨g⟩ := H Q P h.symm
    exact ⟨⟨f, g, (hthin _ _).allEq _ _, (hthin _ _).allEq _ _⟩⟩
  rintro ⟨⟨bP, xP, sP, hxP, hsP, iP, vP⟩, hP⟩ ⟨⟨bQ, xQ, sQ, hxQ, hsQ, iQ, vQ⟩, hQ⟩ hPQ
  change xP = x at hP
  change xQ = x at hQ
  subst hP
  subst xQ
  subst hxP hxQ
  simp only [DiagonalPoint.fiberTwist, DiagonalPoint.twist, eqToHom_refl, Category.id_comp,
    Category.comp_id] at hPQ
  have hPQ' : iP.hom.a ≫ iP.inv.b = iQ.hom.a ≫ iQ.inv.b := hPQ
  obtain ⟨φ, hφ, -⟩ := DiagonalPoint.exists_hom_of_twist_eq xP sP sQ hsP.symm hsQ.symm iP iQ vP vQ
    hPQ'
  have : (fst pT p (structureFunctor p p (𝟭 𝒞) p p) y
      (diagonal (Functor.comp_id p))).IsHomLift (𝟙 xP) φ :=
    have h₁ : (fst pT p (structureFunctor p p (𝟭 𝒞) p p) y
        (diagonal (Functor.comp_id p))).map φ = 𝟙 xP := hφ
    by rw [← h₁]; exact IsHomLift.map _ φ
  exact ⟨Functor.Fiber.homMk _ _ φ⟩

/-- The presheaf of isomorphism classes of `𝒯 ×_{y, 𝒮 × 𝒮, Δ} 𝒮 ⟶ 𝒯` is small for the universe
of the morphisms of `𝒮`: a class is determined by its twist. -/
lemma DiagonalPoint.small_isoClassPresheaf
    [hfib : (fst pT p (structureFunctor p p (𝟭 𝒞) p p) y
      (diagonal (Functor.comp_id p))).IsFibered] :
    FunctorToTypes.Small.{v₃}
      (fst pT p (structureFunctor p p (𝟭 𝒞) p p) y (diagonal (Functor.comp_id p))).isoClassPresheaf
      := by
  intro x
  refine small_of_injective
    (f := fun c : _root_.Quotient (isIsomorphicSetoid ((fst pT p (structureFunctor p p (𝟭 𝒞) p p) y
      (diagonal (Functor.comp_id p))).Fiber x.unop)) => DiagonalPoint.fiberTwist c.out) ?_
  intro c c' hc
  rw [← _root_.Quotient.out_eq c, ← _root_.Quotient.out_eq c']
  exact Functor.isoClassMk_eq_of_iso (DiagonalPoint.nonempty_iso_of_fiberTwist_eq _ _ hc).some

end DiagonalPoint

end CategoryTheory.TwoFibreProductOver

namespace AlgebraicGeometry.Stack

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
  (V : BigFppfOver B S hS)
  (y : BigFppfOver B V.left.1 V.left.2 ⥤ (CatFiberedInGroupoids.product 𝒳 𝒳).val.obj)

/-- The 2-fibre product `𝒴 = 𝒳 ×_{Δ, 𝒳 × 𝒳, y} (Sch/V)_{fppf}` of the proof of Stacks 07Y5, as
a category over `(Sch/V)_{fppf}` through its projection to the second factor. -/
abbrev diagonalPointFibre :
    TwoFibreProductOver (Over.map V.hom) 𝒳.val.p (CatFiberedInGroupoids.product 𝒳 𝒳).val.p y
        (diagonalBasedFunctor B S hS 𝒳).toFunctor ⥤ BigFppfOver B V.left.1 V.left.2 :=
  TwoFibreProductOver.fst (Over.map V.hom) 𝒳.val.p (CatFiberedInGroupoids.product 𝒳 𝒳).val.p y
    (diagonalBasedFunctor B S hS 𝒳).toFunctor

variable {B S hS 𝒳 V y}
variable (hy : y ⋙ (CatFiberedInGroupoids.product 𝒳 𝒳).val.p = Over.map V.hom)

include hy in
/-- **`𝒴` is fibred in setoids** over `(Sch/V)_{fppf}` (the observation of the proof of
Stacks 07Y5 citing Stacks 04SI). -/
theorem diagonalPointFibre_isFiberedInSetoids :
    (diagonalPointFibre B S hS 𝒳 V y).IsFiberedInSetoids :=
  ⟨fst_isFiberedInGroupoids_overMap V.hom 𝒳.val.p (CatFiberedInGroupoids.product 𝒳 𝒳).val.p y
      (diagonalBasedFunctor B S hS 𝒳).toFunctor 𝒳.isFiberedInGroupoids
      (CatFiberedInGroupoids.product 𝒳 𝒳).isFiberedInGroupoids hy
      (diagonalBasedFunctor B S hS 𝒳).w,
    fun T => TwoFibreProductOver.DiagonalPoint.fiber_isThin T⟩

include hy in
/-- The presheaf of isomorphism classes of `𝒴` is `u`-small. -/
theorem small_isoClassPresheaf_diagonalPointFibre :
    letI := (diagonalPointFibre_isFiberedInSetoids hy).isFiberedInGroupoids.isFibered
    FunctorToTypes.Small.{u} (diagonalPointFibre B S hS 𝒳 V y).isoClassPresheaf :=
  TwoFibreProductOver.DiagonalPoint.small_isoClassPresheaf
    (hfib := (diagonalPointFibre_isFiberedInSetoids hy).isFiberedInGroupoids.isFibered)

/-- **The functor `Y` of the proof of Stacks 07Y5**: the presheaf of isomorphism classes of
`𝒴 = 𝒳 ×_{Δ, 𝒳 × 𝒳, y} (Sch/V)_{fppf}` on `(Sch/V)_{fppf}`, in its `Type u` model. -/
noncomputable def diagonalPointFunctor : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u :=
  letI := (diagonalPointFibre_isFiberedInSetoids hy).isFiberedInGroupoids.isFibered
  letI := small_isoClassPresheaf_diagonalPointFibre hy
  Functor.isoClassPresheafModel.{u} (diagonalPointFibre B S hS 𝒳 V y)

/-- The equivalence over `(Sch/V)_{fppf}` of `𝒴` with the category fibred in sets attached to its
functor `Y` of isomorphism classes. -/
noncomputable def diagonalPointFibreEquivalenceOver :
    StacksRepresentableCFG.EquivalenceOver (diagonalPointFibre B S hS 𝒳 V y)
      (presheafOfCategories (diagonalPointFunctor hy ⋙ typeToCat)).p :=
  letI := diagonalPointFibre_isFiberedInSetoids hy
  letI := (diagonalPointFibre_isFiberedInSetoids hy).isFiberedInGroupoids.isFibered
  letI := small_isoClassPresheaf_diagonalPointFibre hy
  isoClassEquivalenceOverModel B V.left.1 V.left.2 (diagonalPointFibre B S hS 𝒳 V y)

end AlgebraicGeometry.Stack

end
