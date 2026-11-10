module

public import StacksFrontier.CategoryTheory.Grothendieck.FibrewiseHom
public import StacksFrontier.Deformation.GroupoidQuotient.EvaluationEquivalence
public import StacksFrontier.Deformation.SchlessingerConditions.SmoothMorphisms

/-!
# Realising a 1-morphism of quotients by a morphism of groupoids in functors

A morphism `(U, R, s, t, c) → (U', R', s', t', c')` of groupoids in functors on `𝒞_Λ` induces a
functor `[U/R] → [U'/R']` of the quotient categories over `𝒞_Λ`, namely
`Deformation.GroupoidInFunctors.quotientMap`. Conversely, if `(U, R, s, t, c)` is
prorepresentable and `(U', R', s', t', c')` is smooth, then **every** `1`-morphism of the
quotients over `𝒞_Λ` is isomorphic to one induced this way. That converse is the assertion with
which the proof of Stacks 06KQ opens, that a morphism `[U/R] → [U'/R']` "is the same thing as" a
morphism of the groupoids in functors of Definition 06K3.

## Main definitions

* `Deformation.GroupoidInFunctors.quotientPtHom`: the morphism of the quotient category over a
  morphism of the base with identity fibre component.
* `Deformation.GroupoidInFunctors.Realization`: the data the argument runs on — a
  prorepresentation of the object functor of the source, smoothness of the target, and the given
  functor of quotients over the base.
* `Deformation.GroupoidInFunctors.Realization.tower`: the rectified tower.
* `Deformation.GroupoidInFunctors.Realization.objMap`,
  `Deformation.GroupoidInFunctors.Realization.evalFunctor`: the point of the evaluated groupoid
  of the target attached to a point of the object functor of the source, and the resulting
  functor of evaluated groupoids.
* `Deformation.GroupoidInFunctors.Realization.hom`: the realising morphism of groupoids in
  functors.
* `Deformation.GroupoidInFunctors.Realization.quotientMapIso`: the isomorphism of functors it
  realises.

## Main results

* `Deformation.factorThroughAdicTruncation_unique`: a point of an Artinian local algebra over a
  complete local algebra factors through a given adic truncation in at most one way.
* `Deformation.GroupoidInFunctors.Realization.key`: the point of the evaluated groupoid of the
  target that a factorization produces depends neither on the factorization nor on its level.
* `Deformation.GroupoidInFunctors.Realization.towerFactHom_comp_compare`: the comparison
  isomorphism is compatible with every factorization.
* `Deformation.GroupoidInFunctors.Realization.evalFunctor_naturality`: the resulting
  transformation of evaluated groupoids is strictly natural.
* `Deformation.GroupoidInFunctors.exists_hom_of_morphismOver`: the realisation theorem.

## Implementation notes

### Why the two hypotheses are needed

A functor `[U/R] → [U'/R']` over `𝒞_Λ` carries the fibre over an object of the base into the
fibre over that object, but it respects transport along a morphism of the base only up to an
invertible fibre component over that morphism — it is a pseudonatural, not a strict, morphism of
the two evaluation functors. Only a strict one comes from a morphism of groupoids in functors,
by Stacks 06K4 (`Deformation.GroupoidInFunctors.evaluationEquivalence`), so the fibre components
have to be rectified away, and that is where both hypotheses enter.

Prorepresentability of the source gives a complete local algebra `R` with
`U ≅ restrictedCoyoneda R`. Every point of `U` over `A` is then the image of the canonical point
of the adic truncation `R / m_R ^ (n + 1)` for `n` large, and the morphism of the base realising
it is **unique**, because the truncation projection out of `R` is surjective. So the value of the
rectified transformation at a point is forced once its value on the tower of canonical points is
chosen, which is what makes it strictly natural.

Smoothness of the target supplies the choice on the tower. The given functor identifies the
images of two consecutive canonical points only up to an isomorphism over the transition
`R / m_R ^ (n + 2) → R / m_R ^ (n + 1)`; smoothness of the source morphism of `(U', R', s', t',
c')` lifts an arrow of an evaluated groupoid along that surjection with a prescribed source, and
iterating the lift replaces the tower of images by one the functor respects on the nose.

### The shape of the argument in Lean

The fibre components are extracted through the lemmas of
`StacksFrontier.CategoryTheory.Grothendieck.FibrewiseHom`: a morphism of a Grothendieck
construction whose base component is known is retyped by
`CategoryTheory.Grothendieck.baseHom`, and a morphism over an identity of the base is a morphism
of a single fibre by `CategoryTheory.Grothendieck.fibreHom`. Every fibre of the quotient of a
groupoid in functors is a groupoid, so a morphism of a fibre is automatically invertible and no
separate invertibility hypothesis is ever needed.

The compatibility of the comparison isomorphism with a factorization is proved by induction on
the level, starting at the level of the base object, where it holds by construction, and raising
one level at a time by the strict compatibility of the rectified tower. Levels are compared by
raising both to a common one rather than by transporting along an equality of natural numbers:
`Deformation.GroupoidInFunctors.Realization.exists_raise` is stated with `Nat.le_induction` for
exactly that reason.

## References

* [Stacks Project, Tag 06KQ](https://stacks.math.columbia.edu/tag/06KQ)
* [Stacks Project, Tag 06K3](https://stacks.math.columbia.edu/tag/06K3)
* [Stacks Project, Tag 06K4](https://stacks.math.columbia.edu/tag/06K4)
* [Stacks Project, Tag 06KB](https://stacks.math.columbia.edu/tag/06KB)
-/

@[expose] public section

namespace Deformation

/-! ### Uniqueness of a factorization through an adic truncation -/

section
open CategoryTheory
universe u v w

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The underlying algebra map of the image of the canonical point of the `n`-th adic truncation
under a morphism out of it is that morphism precomposed with the quotient map. -/
private theorem hom_map_canonicalQuotientPoint
    {R : CompleteLocalAlgCat.{u, v, w} Λ k} {A : ArtinianLocalAlgCat.{u, v, w} Λ k} {n : ℕ}
    (g : AdicTruncation.obj R n ⟶ A) :
    ((restrictedCoyoneda R).map g (canonicalQuotientPoint R n)).hom =
      g.hom.comp (Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal R n)) := by
  rw [restrictedCoyoneda_map_hom, canonicalQuotientPoint_hom]

/-- A point of an Artinian local algebra over a complete local algebra `R` factors through the
`n`-th adic truncation of `R` in at most one way: the truncation projection `R → R / m_R ^ (n+1)`
is surjective, so it is an epimorphism on morphisms out of the truncation. -/
theorem factorThroughAdicTruncation_unique
    {R : CompleteLocalAlgCat.{u, v, w} Λ k} {A : ArtinianLocalAlgCat.{u, v, w} Λ k} {n : ℕ}
    {a b : AdicTruncation.obj R n ⟶ A}
    (h : (restrictedCoyoneda R).map a (canonicalQuotientPoint R n) =
      (restrictedCoyoneda R).map b (canonicalQuotientPoint R n)) : a = b := by
  have h' : a.hom.comp (Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal R n)) =
      b.hom.comp (Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal R n)) := by
    have hh := congrArg (fun z : (restrictedCoyoneda R).obj A => z.hom) h
    rwa [hom_map_canonicalQuotientPoint, hom_map_canonicalQuotientPoint] at hh
  refine ArtinianLocalAlgCat.hom_ext (AlgHom.ext fun x => ?_)
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact congrArg (fun g : R →ₐ[Λ] A => g r) h'

/-- A point of an Artinian local algebra `A` over a complete local algebra `R` is the image of
the canonical point of the `n`-th adic truncation of `R` as soon as `m_A ^ (n + 1) = 0`. This is
`Deformation.exists_factorThroughAdicTruncation` read through
`Deformation.canonicalQuotientPoint`. -/
theorem exists_map_canonicalQuotientPoint_eq
    {R : CompleteLocalAlgCat.{u, v, w} Λ k} {A : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (α : (restrictedCoyoneda R).obj A) {n : ℕ}
    (hn : IsLocalRing.maximalIdeal A ^ (n + 1) = ⊥) :
    ∃ a : AdicTruncation.obj R n ⟶ A,
      (restrictedCoyoneda R).map a (canonicalQuotientPoint R n) = α := by
  obtain ⟨a, ha⟩ := exists_factorThroughAdicTruncation α hn
  refine ⟨a, CompleteLocalAlgCat.Hom.ext ?_⟩
  rw [hom_map_canonicalQuotientPoint]
  exact ha

/-- The transition morphism between consecutive adic truncations is surjective: it carries the
canonical point of the higher truncation to the canonical point of the lower one, and both of
those are the surjective quotient projections out of `R`. -/
theorem surjective_adicTruncation_transition_hom
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (n : ℕ) :
    Function.Surjective (AdicTruncation.transition R n).hom := by
  have h := congrArg (fun z : (restrictedCoyoneda R).obj (AdicTruncation.obj R n) => z.hom)
    (canonicalQuotientPoint_transition R n)
  rw [hom_map_canonicalQuotientPoint, canonicalQuotientPoint_hom] at h
  have hmk : Function.Surjective
      (Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal R n) : R → AdicTruncation.obj R n) :=
    Ideal.Quotient.mk_surjective
  refine Function.Surjective.of_comp (g := (Ideal.Quotient.mkₐ Λ
    (AdicTruncation.ideal R (n + 1)) : R → AdicTruncation.obj R (n + 1))) ?_
  exact fun y => by
    obtain ⟨r, hr⟩ := hmk y
    exact ⟨r, (congrArg (fun g : R →ₐ[Λ] AdicTruncation.obj R n => g r) h).trans hr⟩

end

/-! ### The data of the realisation argument -/

section
open CategoryTheory
universe u v w

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

namespace GroupoidInFunctors

/-- The morphism of the quotient category over a morphism of the base, out of a point of the
object functor: its base component is the given morphism of the base, and its fibre component is
an identity. -/
noncomputable def quotientPtHom
    (G : GroupoidInFunctors.{_, max v w, max v w} (ArtinianLocalAlgCat.{u, max v w, w} Λ k))
    {A B : ArtinianLocalAlgCat.{u, max v w, w} Λ k} (f : A ⟶ B) (x : G.Evaluation A) :
    (⟨A, x⟩ : Grothendieck (evaluationFunctor G)) ⟶ ⟨B, G.objects.map f x⟩ :=
  ⟨f, 𝟙 _⟩

/-- The base component of `Deformation.GroupoidInFunctors.quotientPtHom f x` is `f`. -/
@[simp]
theorem quotientPtHom_base
    (G : GroupoidInFunctors.{_, max v w, max v w} (ArtinianLocalAlgCat.{u, max v w, w} Λ k))
    {A B : ArtinianLocalAlgCat.{u, max v w, w} Λ k} (f : A ⟶ B) (x : G.Evaluation A) :
    (G.quotientPtHom f x).base = f := rfl

/-- Transporting a morphism of an evaluated groupoid along a morphism of the base commutes with
the morphisms of the quotient category over that morphism. -/
theorem ofFibreHom_comp_quotientPtHom
    (G : GroupoidInFunctors.{_, max v w, max v w} (ArtinianLocalAlgCat.{u, max v w, w} Λ k))
    {A B : ArtinianLocalAlgCat.{u, max v w, w} Λ k} (f : A ⟶ B)
    {x y : G.Evaluation A} (g : x ⟶ y) :
    Grothendieck.ofFibreHom (F := evaluationFunctor G) (c := A) g ≫ G.quotientPtHom f y =
      G.quotientPtHom f x ≫ Grothendieck.ofFibreHom (F := evaluationFunctor G) (c := B)
        ((evaluationMap G f).map g) := by
  unfold quotientPtHom
  rw [Grothendieck.ofFibreHom_comp_mk, Grothendieck.mk_comp_ofFibreHom]
  exact congrArg (fun m => (⟨f, m⟩ :
    (⟨A, x⟩ : Grothendieck (evaluationFunctor G)) ⟶ ⟨B, G.objects.map f y⟩))
    ((Category.comp_id _).trans (Category.id_comp _).symm)

/-- Every morphism of the quotient category factors as a morphism over the base followed by a
morphism of a single fibre. -/
theorem quotientPtHom_comp_ofFibreHom
    (G : GroupoidInFunctors.{_, max v w, max v w} (ArtinianLocalAlgCat.{u, max v w, w} Λ k))
    {A B : ArtinianLocalAlgCat.{u, max v w, w} Λ k} (f : A ⟶ B) (x : G.Evaluation A)
    (y : G.Evaluation B) (u : (evaluationMap G f).obj x ⟶ y) :
    G.quotientPtHom f x ≫
        Grothendieck.ofFibreHom (F := evaluationFunctor G) (c := B) u =
      (⟨f, u⟩ : (⟨A, x⟩ : Grothendieck (evaluationFunctor G)) ⟶ ⟨B, y⟩) := by
  unfold quotientPtHom
  rw [Grothendieck.mk_comp_ofFibreHom]
  exact congrArg (fun m => (⟨f, m⟩ :
    (⟨A, x⟩ : Grothendieck (evaluationFunctor G)) ⟶ ⟨B, y⟩)) (Category.id_comp u)

/-- The input of the realisation argument: a prorepresentation of the object functor of `G`,
smoothness of `H`, and a functor between the quotient categories lying over `𝒞_Λ`. -/
structure Realization (G H : GroupoidInFunctors.{_, max v w, max v w}
    (ArtinianLocalAlgCat.{u, max v w, w} Λ k)) where
  /-- The complete local algebra prorepresenting the object functor of `G`. -/
  ring : CompleteLocalAlgCat.{u, max v w, w} Λ k
  /-- The prorepresentation of the object functor of `G`. -/
  prorep : G.objects ≅ restrictedCoyoneda ring
  /-- The target groupoid in functors is smooth. -/
  smooth : IsSmooth H
  /-- The given functor of quotient categories. -/
  functor : Grothendieck (evaluationFunctor G) ⥤ Grothendieck (evaluationFunctor H)
  /-- The given functor lies over the base category. -/
  comp_forget : functor ⋙ Grothendieck.forget (evaluationFunctor H) =
    Grothendieck.forget (evaluationFunctor G)

namespace Realization

variable {G H : GroupoidInFunctors.{_, max v w, max v w}
    (ArtinianLocalAlgCat.{u, max v w, w} Λ k)} (D : Realization.{u, v, w} G H)

/-- The `n`-th adic truncation of the prorepresenting algebra. -/
noncomputable abbrev trunc (n : ℕ) : ArtinianLocalAlgCat.{u, max v w, w} Λ k :=
  AdicTruncation.obj D.ring n

/-- The transition morphism from the `(n+1)`-st adic truncation to the `n`-th one. -/
noncomputable abbrev step (n : ℕ) : D.trunc (n + 1) ⟶ D.trunc n :=
  AdicTruncation.transition D.ring n

/-- The point of the object functor over the `n`-th adic truncation that the prorepresentation
carries the canonical quotient point to. -/
noncomputable def pt (n : ℕ) : G.Evaluation (D.trunc n) :=
  D.prorep.inv.app (D.trunc n) (canonicalQuotientPoint D.ring n)

/-- The tower of canonical points is compatible with the transition morphisms. -/
theorem map_step_pt (n : ℕ) : G.objects.map (D.step n) (D.pt (n + 1)) = D.pt n := by
  have hn := NatTrans.naturality_apply D.prorep.inv (D.step n) (canonicalQuotientPoint D.ring
    (n + 1))
  rw [canonicalQuotientPoint_transition] at hn
  exact hn.symm

/-- Composing a factorization of a point with a further morphism factors the image point. -/
private theorem map_comp_pt {A B : ArtinianLocalAlgCat.{u, max v w, w} Λ k} {n : ℕ}
    {a : D.trunc n ⟶ A} {x : G.Evaluation A} (ha : G.objects.map a (D.pt n) = x) (f : A ⟶ B) :
    G.objects.map (a ≫ f) (D.pt n) = G.objects.map f x := by
  rw [G.objects.map_comp_apply, ha]

/-- A morphism out of an adic truncation is determined by the point of the object functor it
carries the canonical point to. -/
theorem factor_unique {A : ArtinianLocalAlgCat.{u, max v w, w} Λ k} {n : ℕ}
    {a b : D.trunc n ⟶ A} (h : G.objects.map a (D.pt n) = G.objects.map b (D.pt n)) : a = b := by
  refine factorThroughAdicTruncation_unique (R := D.ring) ?_
  have ha := NatTrans.naturality_apply D.prorep.hom a (D.pt n)
  have hb := NatTrans.naturality_apply D.prorep.hom b (D.pt n)
  have hpt : D.prorep.hom.app (D.trunc n) (D.pt n) = canonicalQuotientPoint D.ring n :=
    congrArg (fun m => m (canonicalQuotientPoint D.ring n))
      (D.prorep.inv_hom_id_app (D.trunc n))
  rw [hpt] at ha hb
  rw [← ha, ← hb, h]

/-- Every point of the object functor over an Artinian local algebra killed by the `(n+1)`-st
power of its maximal ideal is the image of the canonical point of the `n`-th adic truncation. -/
theorem exists_factor {A : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (x : G.Evaluation A) {n : ℕ} (hn : IsLocalRing.maximalIdeal A ^ (n + 1) = ⊥) :
    ∃ a : D.trunc n ⟶ A, G.objects.map a (D.pt n) = x := by
  obtain ⟨a, ha⟩ := exists_map_canonicalQuotientPoint_eq (D.prorep.hom.app A x) hn
  refine ⟨a, ?_⟩
  have hnat := NatTrans.naturality_apply D.prorep.inv a (canonicalQuotientPoint D.ring n)
  rw [ha] at hnat
  refine Eq.trans ?_ (congrArg (fun m => m x) (D.prorep.hom_inv_id_app A))
  exact hnat.symm

/-- A level at which every point of the object functor over `A` admits a factorization: an
exponent killing the maximal ideal of `A`. -/
noncomputable def level (A : ArtinianLocalAlgCat.{u, max v w, w} Λ k) : ℕ :=
  Classical.choose (exists_pow_maximalIdeal_eq_bot A)

/-- The `(level A + 1)`-st power of the maximal ideal of `A` vanishes. -/
theorem level_spec (A : ArtinianLocalAlgCat.{u, max v w, w} Λ k) :
    IsLocalRing.maximalIdeal A ^ (level.{u, v, w} A + 1) = ⊥ :=
  Classical.choose_spec (exists_pow_maximalIdeal_eq_bot A)

/-- The chosen factorization of a point of the object functor through the adic truncation at
its level. -/
noncomputable def fact {A : ArtinianLocalAlgCat.{u, max v w, w} Λ k} (x : G.Evaluation A) :
    D.trunc (level.{u, v, w} A) ⟶ A :=
  Classical.choose (D.exists_factor x (level_spec.{u, v, w} A))

/-- The chosen factorization carries the canonical point to the given point. -/
theorem map_fact_pt {A : ArtinianLocalAlgCat.{u, max v w, w} Λ k} (x : G.Evaluation A) :
    G.objects.map (D.fact x) (D.pt (level.{u, v, w} A)) = x :=
  Classical.choose_spec (D.exists_factor x (level_spec.{u, v, w} A))

/-- A morphism out of an adic truncation, pushed `d` levels up the tower. -/
noncomputable def stepIter {A : ArtinianLocalAlgCat.{u, max v w, w} Λ k} (n : ℕ)
    (a : D.trunc n ⟶ A) : (d : ℕ) → (D.trunc (n + d) ⟶ A)
  | 0 => a
  | d + 1 => D.step (n + d) ≫ stepIter n a d

/-- Pushing a morphism out of an adic truncation up the tower does not change the point of the
object functor it carries the canonical point to. -/
theorem map_stepIter_pt {A : ArtinianLocalAlgCat.{u, max v w, w} Λ k} (n : ℕ)
    (a : D.trunc n ⟶ A) (d : ℕ) :
    G.objects.map (D.stepIter n a d) (D.pt (n + d)) = G.objects.map a (D.pt n) := by
  induction d with
  | zero => rfl
  | succ d ih =>
      exact (D.map_comp_pt (D.map_step_pt (n + d)) (D.stepIter n a d)).trans ih


/-! ### The isofibration property supplied by smoothness -/

/-- Smoothness of the source morphism of `H` lifts an arrow of an evaluated groupoid along a
surjection of the base: an arrow over `A` whose source is the image of a point over `B` is the
image of an arrow over `B` out of that point, up to the identification of its target. -/
theorem exists_lift_hom_of_isSmooth
    {H : GroupoidInFunctors.{_, max v w, max v w} (ArtinianLocalAlgCat.{u, max v w, w} Λ k)}
    (hH : IsSmooth H) {B A : ArtinianLocalAlgCat.{u, max v w, w} Λ k} (f : B ⟶ A)
    (hf : Function.Surjective f.hom) (xB : H.Evaluation B) (zA : H.Evaluation A)
    (σ : (evaluationMap H f).obj xB ⟶ zA) :
    ∃ (zB : H.Evaluation B) (hz : (evaluationMap H f).obj zB = zA) (μ : xB ⟶ zB),
      (evaluationMap H f).map μ ≫ eqToHom hz = σ := by
  have hα := (H.evaluationArrowEquiv A ((evaluationMap H f).obj xB) zA σ).2
  obtain ⟨β, hβmap, hβsrc⟩ :=
    (isSmooth_elementsBasedFunctor_iff H.source).1 hH.1 f hf
      (H.evaluationArrowEquiv A ((evaluationMap H f).obj xB) zA σ).1 xB hα.1
  have hz : (evaluationMap H f).obj (H.target.app B β) = zA := by
    change H.objects.map f (H.target.app B β) = zA
    rw [← NatTrans.naturality_apply H.target f β, hβmap]
    exact hα.2
  refine ⟨H.target.app B β, hz, H.arrowOfElem B xB (H.target.app B β) β hβsrc rfl, ?_⟩
  have harr : (H.evaluationArrowEquiv A _ _
      ((evaluationMap H f).map (H.arrowOfElem B xB (H.target.app B β) β hβsrc rfl))).1 =
      (H.evaluationArrowEquiv A ((evaluationMap H f).obj xB) zA σ).1 := by
    rw [evaluationMap_map_arrow, evaluationArrowEquiv_arrowOfElem, hβmap]
  have hmap := hom_eq_transport H A (x := (evaluationMap H f).obj xB)
    (x' := (evaluationMap H f).obj xB)
    (y := (evaluationMap H f).obj (H.target.app B β)) (y' := zA) rfl hz
    ((evaluationMap H f).map (H.arrowOfElem B xB (H.target.app B β) β hβsrc rfl)) σ harr
  rw [hmap]
  simp

/-! ### The rectified tower -/

/-- The base object of the value of the given functor at an object of the quotient is the base
object itself. -/
theorem baseObj (X : Grothendieck (evaluationFunctor G)) : (D.functor.obj X).base = X.base :=
  Functor.congr_obj D.comp_forget X

/-- What the given functor does to the base component of a morphism of the quotient. -/
theorem baseMap {X Y : Grothendieck (evaluationFunctor G)} (φ : X ⟶ Y) :
    (D.functor.map φ).base =
      eqToHom (D.baseObj X) ≫ φ.base ≫ eqToHom (D.baseObj Y).symm :=
  Grothendieck.baseMap_eq D.functor D.comp_forget φ

/-- The morphism of quotient objects over a transition of the tower of truncations. -/
noncomputable def towerHom (n : ℕ) :
    (⟨D.trunc (n + 1), D.pt (n + 1)⟩ : Grothendieck (evaluationFunctor G)) ⟶
      ⟨D.trunc n, D.pt n⟩ :=
  ⟨D.step n, eqToHom (D.map_step_pt n)⟩

/-- The base component of `Deformation.GroupoidInFunctors.Realization.towerHom n` is the
transition morphism. -/
@[simp]
theorem towerHom_base (n : ℕ) : (D.towerHom n).base = D.step n := rfl

/-- The morphism of quotient objects attached to a factorization of a point of the object
functor through an adic truncation. -/
noncomputable def factHom {A : ArtinianLocalAlgCat.{u, max v w, w} Λ k} {n : ℕ}
    {x : G.Evaluation A} (a : D.trunc n ⟶ A) (ha : G.objects.map a (D.pt n) = x) :
    (⟨D.trunc n, D.pt n⟩ : Grothendieck (evaluationFunctor G)) ⟶ ⟨A, x⟩ :=
  ⟨a, eqToHom ha⟩

/-- The fibre component of the value of the given functor at a point of the object functor,
transported into the fibre over the base object. -/
noncomputable def fib {A : ArtinianLocalAlgCat.{u, max v w, w} Λ k} (x : G.Evaluation A) :
    H.Evaluation A :=
  Grothendieck.fibreObj D.functor D.comp_forget (⟨A, x⟩ : Grothendieck (evaluationFunctor G))

/-- The canonical isomorphism between the value of the given functor at a point of the object
functor and its transported fibre component, included in the fibre over the base object. -/
noncomputable def fibIso {A : ArtinianLocalAlgCat.{u, max v w, w} Λ k} (x : G.Evaluation A) :
    (⟨A, D.fib x⟩ : Grothendieck (evaluationFunctor H)) ≅ D.functor.obj ⟨A, x⟩ :=
  Grothendieck.fibreObjIso D.functor D.comp_forget ⟨A, x⟩

/-- The base component of the forward morphism of
`Deformation.GroupoidInFunctors.Realization.fibIso x`. -/
@[simp]
theorem fibIso_hom_base {A : ArtinianLocalAlgCat.{u, max v w, w} Λ k} (x : G.Evaluation A) :
    (D.fibIso x).hom.base = eqToHom (D.baseObj ⟨A, x⟩).symm := rfl

/-- The base component of the inverse morphism of
`Deformation.GroupoidInFunctors.Realization.fibIso x`. -/
@[simp]
theorem fibIso_inv_base {A : ArtinianLocalAlgCat.{u, max v w, w} Λ k} (x : G.Evaluation A) :
    (D.fibIso x).inv.base = eqToHom (D.baseObj ⟨A, x⟩) := rfl

/-- The fibre component of the value of the given functor at the canonical point over the
`n`-th truncation. -/
noncomputable abbrev raw (n : ℕ) : H.Evaluation (D.trunc n) := D.fib (D.pt n)

/-- The canonical isomorphism at the canonical point over the `n`-th truncation. -/
noncomputable abbrev rawIso (n : ℕ) :
    (⟨D.trunc n, D.raw n⟩ : Grothendieck (evaluationFunctor H)) ≅
      D.functor.obj ⟨D.trunc n, D.pt n⟩ :=
  D.fibIso (D.pt n)

end Realization

section
variable {G H : GroupoidInFunctors.{_, max v w, max v w}
  (ArtinianLocalAlgCat.{u, max v w, w} Λ k)}

/-- One stage of the rectified tower: a point of the evaluated groupoid of `H` over the `n`-th
truncation, together with an identification of it with the fibre component of the value of the
given functor at the canonical point. -/
structure Realization.Tower (D : Realization.{u, v, w} G H) (n : ℕ) where
  /-- The rectified point. -/
  pt : H.Evaluation (D.trunc n)
  /-- Its identification with the fibre component of the value of the given functor. -/
  iso : pt ≅ D.raw n

/-- The isomorphism of quotient objects that a stage of the rectified tower provides. -/
noncomputable def Realization.Tower.groth {D : Realization.{u, v, w} G H} {n : ℕ}
    (t : D.Tower n) :
    (⟨D.trunc n, t.pt⟩ : Grothendieck (evaluationFunctor H)) ≅
      D.functor.obj ⟨D.trunc n, D.pt n⟩ :=
  Grothendieck.ofFibreIso t.iso ≪≫ D.rawIso n

/-- A step of the rectification: the next stage of the tower, strictly compatible with the
present one and commuting with the value of the given functor on the transition. -/
structure Realization.TowerStep (D : Realization.{u, v, w} G H) (n : ℕ) (t : D.Tower n) where
  /-- The next stage. -/
  next : D.Tower (n + 1)
  /-- Strict compatibility with the transition of the tower of truncations. -/
  compat : (evaluationMap H (D.step n)).obj next.pt = t.pt
  /-- Commutation with the value of the given functor on the transition. -/
  comm : (⟨D.step n, eqToHom compat⟩ :
        (⟨D.trunc (n + 1), next.pt⟩ : Grothendieck (evaluationFunctor H)) ⟶
          ⟨D.trunc n, t.pt⟩) ≫ t.groth.hom =
      next.groth.hom ≫ D.functor.map (D.towerHom n)

end

namespace Realization

variable {G H : GroupoidInFunctors.{_, max v w, max v w}
    (ArtinianLocalAlgCat.{u, max v w, w} Λ k)} (D : Realization.{u, v, w} G H)

/-- The comparison morphism over a transition of the tower of truncations, before
rectification: the given functor identifies the two canonical points only up to the
isomorphisms recorded by the two stages. -/
noncomputable def towerCompare {n : ℕ} (t : D.Tower n) :
    (⟨D.trunc (n + 1), D.raw (n + 1)⟩ : Grothendieck (evaluationFunctor H)) ⟶
      ⟨D.trunc n, t.pt⟩ :=
  (D.rawIso (n + 1)).hom ≫ D.functor.map (D.towerHom n) ≫ t.groth.inv

/-- The comparison morphism over a transition lies over that transition. -/
theorem towerCompare_base {n : ℕ} (t : D.Tower n) : (D.towerCompare t).base = D.step n := by
  rw [towerCompare]
  simp only [Grothendieck.comp_base, D.fibIso_hom_base, D.baseMap, Tower.groth, Iso.trans_inv,
    Grothendieck.ofFibreIso_inv, Grothendieck.ofFibreHom_base, D.fibIso_inv_base]
  simp

/-- The comparison morphism over a transition, followed by the isomorphism of the present stage,
is the value of the given functor on the transition read through the canonical isomorphism. -/
theorem towerCompare_comp_groth {n : ℕ} (t : D.Tower n) :
    D.towerCompare t ≫ t.groth.hom =
      (D.rawIso (n + 1)).hom ≫ D.functor.map (D.towerHom n) := by
  simp only [towerCompare, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The rectification step assembled from a lift of the comparison morphism: a point of the
evaluated groupoid of `H` over the next truncation whose image is the present stage, together
with an arrow from the fibre component of the value of the given functor realising the
comparison morphism, is a strictly compatible next stage of the tower. -/
noncomputable def towerStepOfLift (n : ℕ) (t : D.Tower n)
    (zB : H.Evaluation (D.trunc (n + 1)))
    (hz : (evaluationMap H (D.step n)).obj zB = t.pt) (μ : D.raw (n + 1) ⟶ zB)
    (hμ : (evaluationMap H (D.step n)).map μ ≫ eqToHom hz =
      Grothendieck.baseHom (D.towerCompare t) (D.towerCompare_base t)) :
    D.TowerStep n t where
  next := ⟨zB, (asIso μ).symm⟩
  compat := hz
  comm := by
    have hfib : (evaluationMap H (D.step n)).map (inv μ) ≫
        Grothendieck.baseHom (D.towerCompare t) (D.towerCompare_base t) = eqToHom hz := by
      rw [← hμ, ← Category.assoc, ← CategoryTheory.Functor.map_comp, IsIso.inv_hom_id,
        CategoryTheory.Functor.map_id, Category.id_comp]
    have hkey : (⟨D.step n, eqToHom hz⟩ :
          (⟨D.trunc (n + 1), zB⟩ : Grothendieck (evaluationFunctor H)) ⟶
            ⟨D.trunc n, t.pt⟩) =
        Grothendieck.ofFibreHom (inv μ) ≫ D.towerCompare t := by
      rw [← Grothendieck.mk_baseHom (D.towerCompare t) (D.towerCompare_base t),
        Grothendieck.ofFibreHom_comp_mk]
      exact congrArg (fun m => (⟨D.step n, m⟩ :
        (⟨D.trunc (n + 1), zB⟩ : Grothendieck (evaluationFunctor H)) ⟶
          ⟨D.trunc n, t.pt⟩)) hfib.symm
    rw [hkey, Category.assoc, D.towerCompare_comp_groth t]
    simp [Tower.groth]

/-- The rectification step: smoothness of `H` turns the comparison morphism over a transition
into a strictly compatible next stage of the tower. Smoothness only asserts that the lift of the
comparison morphism exists, so the step is chosen from it. -/
noncomputable def towerStep (n : ℕ) (t : D.Tower n) : D.TowerStep n t :=
  D.towerStepOfLift n t _ _ _
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
      (exists_lift_hom_of_isSmooth D.smooth (D.step n)
        (surjective_adicTruncation_transition_hom D.ring n) (D.raw (n + 1)) t.pt
        (Grothendieck.baseHom (D.towerCompare t) (D.towerCompare_base t))))))

/-- The rectified tower: a strictly compatible system of points of the evaluated groupoids of
`H`, each identified with the fibre component of the value of the given functor. -/
noncomputable def tower : (n : ℕ) → D.Tower n
  | 0 => ⟨D.raw 0, Iso.refl _⟩
  | n + 1 => (D.towerStep n (tower n)).next

/-- The rectified tower is strictly compatible with the transitions. -/
theorem tower_compat (n : ℕ) :
    (evaluationMap H (D.step n)).obj (D.tower (n + 1)).pt = (D.tower n).pt :=
  (D.towerStep n (D.tower n)).compat

/-- The comparison isomorphisms of the rectified tower commute strictly with the transitions. -/
theorem tower_comm (n : ℕ) :
    (⟨D.step n, eqToHom (D.tower_compat n)⟩ :
        (⟨D.trunc (n + 1), (D.tower (n + 1)).pt⟩ : Grothendieck (evaluationFunctor H)) ⟶
          ⟨D.trunc n, (D.tower n).pt⟩) ≫ (D.tower n).groth.hom =
      (D.tower (n + 1)).groth.hom ≫ D.functor.map (D.towerHom n) :=
  (D.towerStep n (D.tower n)).comm

/-! ### The point attached to a point of the object functor -/

/-- The point of the evaluated groupoid of `H` over `A` attached to a point of the object
functor of `G` over `A`: the image of the rectified tower under the chosen factorization. -/
noncomputable def objMap {A : ArtinianLocalAlgCat.{u, max v w, w} Λ k} (x : G.Evaluation A) :
    H.Evaluation A :=
  (evaluationMap H (D.fact x)).obj ((D.tower (level.{u, v, w} A)).pt)

/-- A factorization of a point of the object functor can be raised to any higher level of the
tower without changing the point of the evaluated groupoid of `H` that it produces. -/
theorem exists_raise {A : ArtinianLocalAlgCat.{u, max v w, w} Λ k} {x : G.Evaluation A}
    {n : ℕ} (a : D.trunc n ⟶ A) (ha : G.objects.map a (D.pt n) = x) (N : ℕ) (hN : n ≤ N) :
    ∃ a' : D.trunc N ⟶ A, G.objects.map a' (D.pt N) = x ∧
      (evaluationMap H a').obj ((D.tower N).pt) =
        (evaluationMap H a).obj ((D.tower n).pt) := by
  induction N, hN using Nat.le_induction with
  | base => exact ⟨a, ha, rfl⟩
  | succ N hN ih =>
      obtain ⟨a', ha', hz'⟩ := ih
      refine ⟨D.step N ≫ a', ?_, ?_⟩
      · exact (D.map_comp_pt (D.map_step_pt N) a').trans ha'
      · have hc : (evaluationMap H (D.step N ≫ a')).obj ((D.tower (N + 1)).pt) =
            (evaluationMap H a').obj
              ((evaluationMap H (D.step N)).obj ((D.tower (N + 1)).pt)) :=
          H.objects.map_comp_apply (D.step N) a' ((D.tower (N + 1)).pt)
        rw [hc, D.tower_compat N, hz']

/-- The point of the evaluated groupoid of `H` produced by a factorization depends neither on
the factorization nor on its level: it is always
`Deformation.GroupoidInFunctors.Realization.objMap`. -/
theorem key {A : ArtinianLocalAlgCat.{u, max v w, w} Λ k} {x : G.Evaluation A} {n : ℕ}
    (a : D.trunc n ⟶ A) (ha : G.objects.map a (D.pt n) = x) :
    (evaluationMap H a).obj ((D.tower n).pt) = D.objMap x := by
  obtain ⟨a₁, ha₁, hz₁⟩ := D.exists_raise a ha (max n (level.{u, v, w} A)) (le_max_left _ _)
  obtain ⟨a₂, ha₂, hz₂⟩ := D.exists_raise (D.fact x) (D.map_fact_pt x)
    (max n (level.{u, v, w} A)) (le_max_right _ _)
  calc (evaluationMap H a).obj ((D.tower n).pt)
      = (evaluationMap H a₁).obj ((D.tower (max n (level.{u, v, w} A))).pt) := hz₁.symm
    _ = (evaluationMap H a₂).obj ((D.tower (max n (level.{u, v, w} A))).pt) := by
        rw [D.factor_unique (a := a₁) (b := a₂) (by rw [ha₁, ha₂])]
    _ = D.objMap x := hz₂

/-- The point attached to a point of the object functor is strictly natural in the base
object. -/
theorem objMap_naturality {A B : ArtinianLocalAlgCat.{u, max v w, w} Λ k} (f : A ⟶ B)
    (x : G.Evaluation A) :
    (evaluationMap H f).obj (D.objMap x) = D.objMap (G.objects.map f x) := by
  refine Eq.trans ?_ (D.key (D.fact x ≫ f) (D.map_comp_pt (D.map_fact_pt x) f))
  exact (H.objects.map_comp_apply (D.fact x) f ((D.tower (level.{u, v, w} A)).pt)).symm

/-! ### The comparison isomorphism -/

/-- The morphism of quotient objects that a factorization gives, between the rectified tower
and the point attached to the factored point. -/
noncomputable def towerFactHom {A : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    {x : G.Evaluation A} {n : ℕ} (a : D.trunc n ⟶ A)
    (ha : G.objects.map a (D.pt n) = x) :
    (⟨D.trunc n, (D.tower n).pt⟩ : Grothendieck (evaluationFunctor H)) ⟶ ⟨A, D.objMap x⟩ :=
  ⟨a, eqToHom (D.key a ha)⟩

/-- The value of the given functor on the morphism of quotient objects that a factorization
gives, conjugated by the comparison isomorphisms at its two ends. -/
noncomputable def factCompare {A : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    {x : G.Evaluation A} {n : ℕ} (a : D.trunc n ⟶ A)
    (ha : G.objects.map a (D.pt n) = x) :
    (⟨D.trunc n, (D.tower n).pt⟩ : Grothendieck (evaluationFunctor H)) ⟶ ⟨A, D.fib x⟩ :=
  (D.tower n).groth.hom ≫ D.functor.map (D.factHom a ha) ≫ (D.fibIso x).inv

/-- The morphism `Deformation.GroupoidInFunctors.Realization.factCompare a ha` lies over `a`. -/
theorem factCompare_base {A : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    {x : G.Evaluation A} {n : ℕ} (a : D.trunc n ⟶ A)
    (ha : G.objects.map a (D.pt n) = x) : (D.factCompare a ha).base = a := by
  rw [factCompare]
  simp only [Grothendieck.comp_base, D.fibIso_hom_base, D.baseMap, Tower.groth, Iso.trans_hom,
    Grothendieck.ofFibreIso_hom, Grothendieck.ofFibreHom_base, D.fibIso_inv_base, factHom]
  simp

/-- The comparison morphism identifying the point attached to a point of the object functor
with the fibre component of the value of the given functor there. -/
noncomputable def compare {A : ArtinianLocalAlgCat.{u, max v w, w} Λ k} (x : G.Evaluation A) :
    D.objMap x ⟶ D.fib x :=
  Grothendieck.baseHom (D.factCompare (D.fact x) (D.map_fact_pt x))
    (D.factCompare_base (D.fact x) (D.map_fact_pt x))

/-- The comparison isomorphism between the quotient object built from the rectified tower and
the value of the given functor. Every fibre of the quotient of `H` is a groupoid, so the
comparison morphism is invertible. -/
noncomputable def compareIso {A : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (x : G.Evaluation A) :
    (⟨A, D.objMap x⟩ : Grothendieck (evaluationFunctor H)) ≅ D.functor.obj ⟨A, x⟩ :=
  Grothendieck.ofFibreIso (asIso (D.compare x)) ≪≫ D.fibIso x

/-- The base component of the forward morphism of
`Deformation.GroupoidInFunctors.Realization.compareIso x`. -/
@[simp]
theorem compareIso_hom_base {A : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (x : G.Evaluation A) :
    (D.compareIso x).hom.base = eqToHom (D.baseObj ⟨A, x⟩).symm := by
  simp [compareIso]

/-- The base component of the inverse morphism of
`Deformation.GroupoidInFunctors.Realization.compareIso x`. -/
@[simp]
theorem compareIso_inv_base {A : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (x : G.Evaluation A) :
    (D.compareIso x).inv.base = eqToHom (D.baseObj ⟨A, x⟩) := by
  simp [compareIso]

/-! ### The comparison isomorphism is compatible with every factorization -/

/-- The morphism of quotient objects over a transition of the rectified tower. -/
noncomputable def towerStepHom (n : ℕ) :
    (⟨D.trunc (n + 1), (D.tower (n + 1)).pt⟩ : Grothendieck (evaluationFunctor H)) ⟶
      ⟨D.trunc n, (D.tower n).pt⟩ :=
  ⟨D.step n, eqToHom (D.tower_compat n)⟩

/-- Restatement of `Deformation.GroupoidInFunctors.Realization.tower_comm` in terms of
`Deformation.GroupoidInFunctors.Realization.towerStepHom`. -/
theorem towerStepHom_comp_groth (n : ℕ) :
    D.towerStepHom n ≫ (D.tower n).groth.hom =
      (D.tower (n + 1)).groth.hom ≫ D.functor.map (D.towerHom n) :=
  D.tower_comm n

/-- The morphism of quotient objects given by a factorization raised one level is the transition
of the rectified tower followed by the morphism given by the original factorization. -/
theorem towerFactHom_step {A : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    {x : G.Evaluation A} {N : ℕ} (a : D.trunc N ⟶ A)
    (ha : G.objects.map a (D.pt N) = x)
    (ha' : G.objects.map (D.step N ≫ a) (D.pt (N + 1)) = x) :
    D.towerFactHom (D.step N ≫ a) ha' = D.towerStepHom N ≫ D.towerFactHom a ha := by
  unfold towerFactHom towerStepHom
  exact (Grothendieck.mk_eqToHom_comp_mk_eqToHom
    (X := (⟨D.trunc (N + 1), (D.tower (N + 1)).pt⟩ : Grothendieck (evaluationFunctor H)))
    (Y := (⟨D.trunc N, (D.tower N).pt⟩ : Grothendieck (evaluationFunctor H)))
    (Z := (⟨A, D.objMap x⟩ : Grothendieck (evaluationFunctor H)))
    (b := D.step N) (b' := a)
    (D.tower_compat N) (D.key a ha) (D.key (D.step N ≫ a) ha')).symm

/-- The morphism of quotient objects of `G` given by a factorization raised one level is the
transition of the tower of canonical points followed by the morphism given by the original
factorization. -/
theorem factHom_step {A : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    {x : G.Evaluation A} {N : ℕ} (a : D.trunc N ⟶ A)
    (ha : G.objects.map a (D.pt N) = x)
    (ha' : G.objects.map (D.step N ≫ a) (D.pt (N + 1)) = x) :
    D.factHom (D.step N ≫ a) ha' = D.towerHom N ≫ D.factHom a ha := by
  unfold factHom towerHom
  exact (Grothendieck.mk_eqToHom_comp_mk_eqToHom
    (X := (⟨D.trunc (N + 1), D.pt (N + 1)⟩ : Grothendieck (evaluationFunctor G)))
    (Y := (⟨D.trunc N, D.pt N⟩ : Grothendieck (evaluationFunctor G)))
    (Z := (⟨A, x⟩ : Grothendieck (evaluationFunctor G)))
    (b := D.step N) (b' := a) (D.map_step_pt N) ha ha').symm

/-- The conjugated value of the given functor on a factorization raised one level is the
transition of the rectified tower followed by the one on the original factorization. -/
theorem factCompare_step {A : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    {x : G.Evaluation A} {N : ℕ} (a : D.trunc N ⟶ A)
    (ha : G.objects.map a (D.pt N) = x)
    (ha' : G.objects.map (D.step N ≫ a) (D.pt (N + 1)) = x) :
    D.factCompare (D.step N ≫ a) ha' = D.towerStepHom N ≫ D.factCompare a ha := by
  rw [factCompare, factCompare, D.factHom_step a ha ha', CategoryTheory.Functor.map_comp,
    ← Category.assoc, ← Category.assoc, ← D.towerStepHom_comp_groth N]
  simp only [Category.assoc]

/-- **The comparison isomorphism is compatible with every factorization.** For every
factorization of a point of the object functor, at every level of the tower at or above the
level of its base object, the morphism of quotient objects that the factorization gives,
followed by the comparison isomorphism, is the value of the given functor on the factorization
read through the comparison isomorphism of the tower. -/
theorem towerFactHom_comp_compare {A : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    {x : G.Evaluation A} :
    ∀ N, level.{u, v, w} A ≤ N → ∀ (a : D.trunc N ⟶ A)
      (ha : G.objects.map a (D.pt N) = x),
      D.towerFactHom a ha ≫ Grothendieck.ofFibreHom (D.compare x) = D.factCompare a ha := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base =>
      intro a ha
      have hfa : a = D.fact x := D.factor_unique (by rw [ha, D.map_fact_pt])
      subst hfa
      rw [towerFactHom, Grothendieck.mk_comp_ofFibreHom,
        ← Grothendieck.mk_baseHom (D.factCompare (D.fact x) ha)
          (D.factCompare_base (D.fact x) ha)]
      exact congrArg (fun m => (⟨D.fact x, m⟩ :
        (⟨D.trunc (level.{u, v, w} A), (D.tower (level.{u, v, w} A)).pt⟩ :
          Grothendieck (evaluationFunctor H)) ⟶ ⟨A, D.fib x⟩))
        (eqToHom_comp_of_refl _ _)
  | succ N hN ih =>
      intro a ha
      obtain ⟨a', ha', -⟩ := D.exists_raise (D.fact x) (D.map_fact_pt x) N hN
      have hstep : G.objects.map (D.step N ≫ a') (D.pt (N + 1)) = x :=
        (D.map_comp_pt (D.map_step_pt N) a').trans ha'
      have hae : a = D.step N ≫ a' := D.factor_unique (by rw [ha, hstep])
      subst hae
      rw [D.towerFactHom_step a' ha' ha, Category.assoc, ih a' ha',
        D.factCompare_step a' ha' ha]

/-! ### Compatibility of the comparison isomorphism with transport along the base -/

/-- The morphism of quotient objects of `H` over a morphism of the base, between the points
attached to a point of the object functor and to its image. -/
noncomputable def objMapHom {A B : ArtinianLocalAlgCat.{u, max v w, w} Λ k} (f : A ⟶ B)
    (x : G.Evaluation A) :
    (⟨A, D.objMap x⟩ : Grothendieck (evaluationFunctor H)) ⟶
      ⟨B, D.objMap (G.objects.map f x)⟩ :=
  ⟨f, eqToHom (D.objMap_naturality f x)⟩

/-- The morphism of quotient objects given by a factorization `a`, followed by transport along
`f`, is the morphism given by the factorization `a ≫ f`. -/
theorem towerFactHom_comp_objMapHom {A B : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    {x : G.Evaluation A} {N : ℕ} (a : D.trunc N ⟶ A)
    (ha : G.objects.map a (D.pt N) = x) (f : A ⟶ B)
    (hb : G.objects.map (a ≫ f) (D.pt N) = G.objects.map f x) :
    D.towerFactHom a ha ≫ D.objMapHom f x = D.towerFactHom (a ≫ f) hb := by
  unfold towerFactHom objMapHom
  exact Grothendieck.mk_eqToHom_comp_mk_eqToHom
    (X := (⟨D.trunc N, (D.tower N).pt⟩ : Grothendieck (evaluationFunctor H)))
    (Y := (⟨A, D.objMap x⟩ : Grothendieck (evaluationFunctor H)))
    (Z := (⟨B, D.objMap (G.objects.map f x)⟩ : Grothendieck (evaluationFunctor H)))
    (b := a) (b' := f) (D.key a ha) (D.objMap_naturality f x) (D.key (a ≫ f) hb)

/-- The morphism of quotient objects of `G` given by a factorization `a`, followed by the
morphism over `f` with identity fibre component, is the morphism given by `a ≫ f`. -/
theorem factHom_comp_quotientPtHom {A B : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    {x : G.Evaluation A} {N : ℕ} (a : D.trunc N ⟶ A)
    (ha : G.objects.map a (D.pt N) = x) (f : A ⟶ B)
    (hb : G.objects.map (a ≫ f) (D.pt N) = G.objects.map f x) :
    D.factHom a ha ≫ G.quotientPtHom f x = D.factHom (a ≫ f) hb := by
  unfold factHom quotientPtHom
  exact Grothendieck.mk_eqToHom_comp_mk_eqToHom
    (X := (⟨D.trunc N, D.pt N⟩ : Grothendieck (evaluationFunctor G)))
    (Y := (⟨A, x⟩ : Grothendieck (evaluationFunctor G)))
    (Z := (⟨B, G.objects.map f x⟩ : Grothendieck (evaluationFunctor G)))
    (b := a) (b' := f) ha rfl hb

/-- At every level at or above that of the base object, the morphism of quotient objects given
by a factorization, followed by the comparison isomorphism, is the value of the given functor on
the factorization read through the isomorphism of the rectified tower. -/
theorem towerFactHom_comp_compareIso {A : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    {x : G.Evaluation A} {N : ℕ} (hN : level.{u, v, w} A ≤ N) (a : D.trunc N ⟶ A)
    (ha : G.objects.map a (D.pt N) = x) :
    D.towerFactHom a ha ≫ (D.compareIso x).hom =
      (D.tower N).groth.hom ≫ D.functor.map (D.factHom a ha) := by
  rw [compareIso, Iso.trans_hom, Grothendieck.ofFibreIso_hom, asIso_hom, ← Category.assoc,
    D.towerFactHom_comp_compare N hN a ha]
  simp only [factCompare, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- **The comparison isomorphism is compatible with transport along the base.** Transport along
`f` between the attached points, followed by the comparison isomorphism at the image point, is
the comparison isomorphism followed by the value of the given functor on the morphism over `f`
with identity fibre component. -/
theorem objMapHom_comp_compareIso {A B : ArtinianLocalAlgCat.{u, max v w, w} Λ k} (f : A ⟶ B)
    (x : G.Evaluation A) :
    D.objMapHom f x ≫ (D.compareIso (G.objects.map f x)).hom =
      (D.compareIso x).hom ≫ D.functor.map (G.quotientPtHom f x) := by
  obtain ⟨a, ha, -⟩ := D.exists_raise (D.fact x) (D.map_fact_pt x)
    (max (level.{u, v, w} A) (level.{u, v, w} B)) (le_max_left _ _)
  have hb := D.map_comp_pt ha f
  refine Grothendieck.hom_ext_of_fiber_isIso (D.towerFactHom a ha) ?_ ?_
  · simp only [Grothendieck.comp_base, objMapHom, D.compareIso_hom_base, D.baseMap,
      quotientPtHom_base]
    simp
  · have e1 : D.towerFactHom a ha ≫ D.objMapHom f x ≫
        (D.compareIso (G.objects.map f x)).hom =
        (D.tower (max (level.{u, v, w} A) (level.{u, v, w} B))).groth.hom ≫
          D.functor.map (D.factHom (a ≫ f) hb) := by
      rw [← Category.assoc (D.towerFactHom a ha) (D.objMapHom f x),
        D.towerFactHom_comp_objMapHom a ha f hb]
      exact D.towerFactHom_comp_compareIso
        (le_max_right (level.{u, v, w} A) (level.{u, v, w} B)) (a ≫ f) hb
    have e2 : D.towerFactHom a ha ≫ (D.compareIso x).hom ≫ D.functor.map (G.quotientPtHom f x) =
        (D.tower (max (level.{u, v, w} A) (level.{u, v, w} B))).groth.hom ≫
          D.functor.map (D.factHom (a ≫ f) hb) := by
      rw [← Category.assoc (D.towerFactHom a ha) (D.compareIso x).hom,
        D.towerFactHom_comp_compareIso
          (le_max_left (level.{u, v, w} A) (level.{u, v, w} B)) a ha, Category.assoc,
        ← CategoryTheory.Functor.map_comp, D.factHom_comp_quotientPtHom a ha f hb]
    exact e1.trans e2.symm

/-- The inverse comparison isomorphism is compatible with transport along the base. -/
theorem compareIso_inv_comp_objMapHom {A B : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (f : A ⟶ B) (x : G.Evaluation A) :
    (D.compareIso x).inv ≫ D.objMapHom f x =
      D.functor.map (G.quotientPtHom f x) ≫ (D.compareIso (G.objects.map f x)).inv := by
  have h2 : (D.compareIso x).inv ≫ D.objMapHom f x ≫
      (D.compareIso (G.objects.map f x)).hom = D.functor.map (G.quotientPtHom f x) := by
    rw [D.objMapHom_comp_compareIso f x, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rw [← h2, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-! ### The rectified transformation of evaluated groupoids -/

/-- The functor of evaluated groupoids over an object of the base that the given functor
induces, rectified by the comparison isomorphism. -/
noncomputable def evalFunctor (A : ArtinianLocalAlgCat.{u, max v w, w} Λ k) :
    G.Evaluation A ⥤ H.Evaluation A where
  obj x := D.objMap x
  map {x y} c := Grothendieck.fibreHom
    ((D.compareIso x).hom ≫ D.functor.map (Grothendieck.ofFibreHom c) ≫
      (D.compareIso y).inv) (by
    simp only [Grothendieck.comp_base, D.compareIso_hom_base, D.compareIso_inv_base, D.baseMap,
      Grothendieck.ofFibreHom_base]
    simp)
  map_id x := by
    refine Eq.trans (Grothendieck.fibreHom_congr (ψ :=
      𝟙 (⟨A, D.objMap x⟩ : Grothendieck (evaluationFunctor H))) ?_ _ (by simp)) ?_
    · rw [Grothendieck.ofFibreHom_id, CategoryTheory.Functor.map_id, Category.id_comp,
        Iso.hom_inv_id]
    · exact Grothendieck.fibreHom_id _
  map_comp {x y z} c c' := by
    refine Eq.trans (Grothendieck.fibreHom_congr (ψ :=
      ((D.compareIso x).hom ≫ D.functor.map (Grothendieck.ofFibreHom c) ≫
          (D.compareIso y).inv) ≫
        ((D.compareIso y).hom ≫ D.functor.map (Grothendieck.ofFibreHom c') ≫
          (D.compareIso z).inv)) ?_ _ ?_) ?_
    · rw [← Grothendieck.ofFibreHom_comp, CategoryTheory.Functor.map_comp]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
    · simp only [Grothendieck.comp_base, D.compareIso_hom_base, D.compareIso_inv_base, D.baseMap,
        Grothendieck.ofFibreHom_base]
      simp
    · exact Grothendieck.fibreHom_comp _ _ _ _ _

/-- The rectified functor of evaluated groupoids sends a point to its attached point. -/
@[simp]
theorem evalFunctor_obj (A : ArtinianLocalAlgCat.{u, max v w, w} Λ k) (x : G.Evaluation A) :
    (D.evalFunctor A).obj x = D.objMap x := rfl

/-- The rectified functor of evaluated groupoids sends an arrow to the fibre component of the
value of the given functor on it, conjugated by the comparison isomorphisms. -/
theorem evalFunctor_map (A : ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    {x y : G.Evaluation A} (c : x ⟶ y)
    (h : ((D.compareIso x).hom ≫ D.functor.map (Grothendieck.ofFibreHom c) ≫
      (D.compareIso y).inv).base = 𝟙 A) :
    (D.evalFunctor A).map c = Grothendieck.fibreHom
      ((D.compareIso x).hom ≫ D.functor.map (Grothendieck.ofFibreHom c) ≫
        (D.compareIso y).inv) h := rfl

/-- Included in the quotient category, the image of an arrow under the rectified functor of
evaluated groupoids is the value of the given functor on it, conjugated by the comparison
isomorphisms. -/
theorem ofFibreHom_evalFunctor_map {A : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    {x y : G.Evaluation A} (c : x ⟶ y) :
    Grothendieck.ofFibreHom (F := evaluationFunctor H) (c := A)
        (x := D.objMap x) (y := D.objMap y) ((D.evalFunctor A).map c) =
      (D.compareIso x).hom ≫ D.functor.map (Grothendieck.ofFibreHom c) ≫
        (D.compareIso y).inv := by
  rw [D.evalFunctor_map A c (by
    simp only [Grothendieck.comp_base, D.compareIso_hom_base, D.compareIso_inv_base, D.baseMap,
      Grothendieck.ofFibreHom_base]
    simp), Grothendieck.ofFibreHom_fibreHom]

/-- Transport along a morphism of the base commutes with the functors of evaluated groupoids:
the statement of the naturality, read in the quotient category. -/
theorem objMapHom_naturality {A B : ArtinianLocalAlgCat.{u, max v w, w} Λ k} (f : A ⟶ B)
    {x y : G.Evaluation A} (c : x ⟶ y) :
    D.objMapHom f x ≫ Grothendieck.ofFibreHom (F := evaluationFunctor H) (c := B)
          (x := D.objMap (G.objects.map f x)) (y := D.objMap (G.objects.map f y))
          ((D.evalFunctor B).map ((evaluationMap G f).map c)) =
      Grothendieck.ofFibreHom (F := evaluationFunctor H) (c := A)
          (x := D.objMap x) (y := D.objMap y) ((D.evalFunctor A).map c) ≫
        D.objMapHom f y := by
  rw [D.ofFibreHom_evalFunctor_map c,
    D.ofFibreHom_evalFunctor_map (A := B) (x := G.objects.map f x)
      (y := G.objects.map f y) ((evaluationMap G f).map c),
    ← Category.assoc (D.objMapHom f x) (D.compareIso (G.objects.map f x)).hom,
    D.objMapHom_comp_compareIso f x, Category.assoc, Category.assoc, Category.assoc,
    D.compareIso_inv_comp_objMapHom f y,
    ← Category.assoc (D.functor.map (G.quotientPtHom f x)),
    ← Category.assoc (D.functor.map
      (Grothendieck.ofFibreHom (F := evaluationFunctor G) (c := A) c)),
    ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    ofFibreHom_comp_quotientPtHom G f c]

/-- The rectified transformation of evaluated groupoids is strictly natural in the base
object. -/
theorem evalFunctor_naturality {A B : ArtinianLocalAlgCat.{u, max v w, w} Λ k} (f : A ⟶ B) :
    evaluationMap G f ⋙ D.evalFunctor B = D.evalFunctor A ⋙ evaluationMap H f := by
  refine CategoryTheory.Functor.ext (fun x => (D.objMap_naturality f x).symm) ?_
  intro x y c
  refine Grothendieck.eq_of_transport_square (F := evaluationFunctor H) f
    ((D.evalFunctor A).map c) (x' := D.objMap (G.objects.map f x))
    (y' := D.objMap (G.objects.map f y)) (D.objMap_naturality f x) (D.objMap_naturality f y)
    ((D.evalFunctor B).map ((evaluationMap G f).map c)) ?_
  exact D.objMapHom_naturality f c

/-! ### The realising morphism of groupoids in functors -/

/-- The rectified transformation of the functors of evaluated groupoids. -/
noncomputable def evalNatTrans :
    AlgebraicGeometry.Stack.evaluationGroupoidFunctor G ⟶
      AlgebraicGeometry.Stack.evaluationGroupoidFunctor H where
  app A := D.evalFunctor A
  naturality _ _ f := D.evalFunctor_naturality f

/-- The morphism of groupoids in functors that realises the given functor of quotients. -/
noncomputable def hom : G ⟶ H := homOfNatTrans D.evalNatTrans

/-- The realising morphism evaluates over `A` to the rectified functor of evaluated groupoids. -/
theorem hom_evaluation (A : ArtinianLocalAlgCat.{u, max v w, w} Λ k) :
    Hom.evaluation D.hom A = D.evalFunctor A :=
  congrFun (congrArg NatTrans.app (evaluationNatTrans_homOfNatTrans D.evalNatTrans)) A

/-- The realising morphism evaluated over `A` acts on arrows as the rectified functor of
evaluated groupoids. -/
theorem hom_evaluation_map {A : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    {x y : G.Evaluation A} (u : x ⟶ y) :
    (Hom.evaluation D.hom A).map u = (D.evalFunctor A).map u :=
  (CategoryTheory.Functor.congr_hom (D.hom_evaluation A) u).trans
    ((eqToHom_comp_of_refl _ _).trans (comp_eqToHom_of_refl _ _))

/-- The functor of quotients induced by the realising morphism acts on a morphism of a single
fibre as the rectified functor of evaluated groupoids. -/
theorem quotientMap_hom_map_ofFibreHom {A : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    {x y : G.Evaluation A} (u : x ⟶ y) :
    (quotientMap D.hom).map (Grothendieck.ofFibreHom (F := evaluationFunctor G) (c := A) u) =
      Grothendieck.ofFibreHom (F := evaluationFunctor H) (c := A)
        (x := D.objMap x) (y := D.objMap y) ((D.evalFunctor A).map u) := by
  refine Eq.trans (quotientMap_map_ι D.hom A u) ?_
  rw [D.hom_evaluation_map u]
  rfl

/-- The functor of quotients induced by the realising morphism sends the morphism over `f` with
identity fibre component to the transport morphism
`Deformation.GroupoidInFunctors.Realization.objMapHom f x`. -/
theorem quotientMap_hom_map_quotientPtHom {A B : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (f : A ⟶ B) (x : G.Evaluation A) :
    (quotientMap D.hom).map (G.quotientPtHom f x) = D.objMapHom f x := by
  refine Grothendieck.ext _ _ rfl ?_
  simp only [quotientMap, Grothendieck.map, quotientPtHom, objMapHom,
    CategoryTheory.Functor.map_id, Cat.eqToHom_app]
  exact Grothendieck.eqToHom₂_comp_id_eq (E := H.Evaluation B) _ _ _

/-- The comparison isomorphism is natural: it is an isomorphism between the functor of
quotients induced by the realising morphism of groupoids in functors and the given one. -/
theorem compareIso_naturality {A B : ArtinianLocalAlgCat.{u, max v w, w} Λ k} (f : A ⟶ B)
    (x : G.Evaluation A) (y : G.Evaluation B) (u : (evaluationMap G f).obj x ⟶ y) :
    (quotientMap D.hom).map
          (⟨f, u⟩ : (⟨A, x⟩ : Grothendieck (evaluationFunctor G)) ⟶ ⟨B, y⟩) ≫
        (D.compareIso y).hom =
      (D.compareIso x).hom ≫
        D.functor.map (⟨f, u⟩ : (⟨A, x⟩ : Grothendieck (evaluationFunctor G)) ⟶ ⟨B, y⟩) := by
  have h1 : (quotientMap D.hom).map
        (⟨f, u⟩ : (⟨A, x⟩ : Grothendieck (evaluationFunctor G)) ⟶ ⟨B, y⟩) ≫
          (D.compareIso y).hom =
      D.objMapHom f x ≫ Grothendieck.ofFibreHom (F := evaluationFunctor H) (c := B)
          (x := D.objMap (G.objects.map f x)) (y := D.objMap y)
          ((D.evalFunctor B).map u) ≫ (D.compareIso y).hom := by
    rw [← quotientPtHom_comp_ofFibreHom G f x y u, CategoryTheory.Functor.map_comp,
      D.quotientMap_hom_map_quotientPtHom f x, D.quotientMap_hom_map_ofFibreHom u]
    exact Category.assoc _ _ _
  have h2 : Grothendieck.ofFibreHom (F := evaluationFunctor H) (c := B)
        (x := D.objMap (G.objects.map f x)) (y := D.objMap y) ((D.evalFunctor B).map u) ≫
        (D.compareIso y).hom =
      (D.compareIso (G.objects.map f x)).hom ≫ D.functor.map
        (Grothendieck.ofFibreHom (F := evaluationFunctor G) (c := B) u) := by
    rw [D.ofFibreHom_evalFunctor_map (A := B) (x := G.objects.map f x) (y := y) u,
      Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have h3 : D.objMapHom f x ≫ (D.compareIso (G.objects.map f x)).hom ≫ D.functor.map
        (Grothendieck.ofFibreHom (F := evaluationFunctor G) (c := B) u) =
      (D.compareIso x).hom ≫ D.functor.map (G.quotientPtHom f x) ≫ D.functor.map
        (Grothendieck.ofFibreHom (F := evaluationFunctor G) (c := B) u) := by
    rw [← Category.assoc (D.objMapHom f x), D.objMapHom_comp_compareIso f x, Category.assoc]
  rw [h1, h2, h3, ← CategoryTheory.Functor.map_comp,
    quotientPtHom_comp_ofFibreHom G f x y u]

/-- **The given functor of quotients is isomorphic to the one induced by a morphism of
groupoids in functors.** -/
noncomputable def quotientMapIso : quotientMap D.hom ≅ D.functor :=
  NatIso.ofComponents (fun X => D.compareIso X.fiber) fun {X Y} φ => by
    obtain ⟨A, x⟩ := X
    obtain ⟨B, y⟩ := Y
    obtain ⟨f, u⟩ := φ
    exact D.compareIso_naturality f x y u

end Realization

/-! ### The realisation theorem -/

/-- **The realisation of a `1`-morphism of quotients by a morphism of groupoids in functors.**
Let `(U, R, s, t, c)` be a prorepresentable groupoid in functors on `𝒞_Λ` and let
`(U', R', s', t', c')` be a smooth one. Every `1`-morphism `[U/R] → [U'/R']` over `𝒞_Λ` is
isomorphic, as a functor, to the one induced by a morphism
`(U, R, s, t, c) → (U', R', s', t', c')` of groupoids in functors. -/
theorem exists_hom_of_morphismOver
    (G H : GroupoidInFunctors.{_, max v w, max v w}
      (ArtinianLocalAlgCat.{u, max v w, w} Λ k))
    (hGpro : IsProrepresentable G) (hHsmooth : IsSmooth H)
    (Φ : StacksRepresentableCFG.MorphismOver
      (Grothendieck.forget (evaluationFunctor G))
      (Grothendieck.forget (evaluationFunctor H))) :
    ∃ F : G ⟶ H, Nonempty (quotientMap F ≅ Φ.functor) := by
  obtain ⟨R, ⟨e⟩⟩ := ((isProrepresentable_iff_objects_arrows G).1 hGpro).1
  exact ⟨(Realization.mk R e hHsmooth Φ.functor Φ.w).hom,
    ⟨(Realization.mk R e hHsmooth Φ.functor Φ.w).quotientMapIso⟩⟩

end GroupoidInFunctors

end

end Deformation
