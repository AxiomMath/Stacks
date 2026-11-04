module

public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.QuotRankBound

/-!
# The universal quotient of the Grassmannian and the point of `Quot^P`

`AlgebraicGeometry.Grassmannian.scheme k N` represents the functor of finite locally free
rank-`N - k` quotients of `𝒪^{⊕ N}`. A representative `q_G` of the class of the identity is a
universal quotient: the class of any morphism `g : T ⟶ G` is the pullback `g^* q_G`, up to
isomorphism of presentations. For `K ∈ Quot^P(T)` the presentation
`𝒪_T^{⊕ N} ≅ π_*(𝒪^{⊕ r}(m)) ⟶ π_*(𝒬(m))` is therefore isomorphic to the pullback of `q_G`
along the classifying morphism `T ⟶ G(N - p, N)`. This is the identification
`(T ⟶ G)^* (universal quotient) ≅ π_*(𝒬(m))` of the proof of Stacks 0DPA.

## Main definitions

* `AlgebraicGeometry.Grassmannian.universalPresentation`: a representative of the universal
  quotient on `G(k, N)`.

## Main results

* `AlgebraicGeometry.Grassmannian.QuotientPresentation.isomorphic_of_mk_eq`: presentations with
  the same class are isomorphic.
* `AlgebraicGeometry.Grassmannian.isomorphic_pullbackPresentation_universalPresentation`: a
  presentation in the class of `g : T ⟶ G` is isomorphic to `g^* q_G`.
* `AlgebraicGeometry.ProjectiveQuot.grassmannianPresentation_isomorphic_pullback`: the
  presentation of `K ∈ Quot^P(T)` is isomorphic to the pullback of `q_G` along
  `AlgebraicGeometry.ProjectiveQuot.toGrassmannian`.

## References

* [Stacks Project, Tag 0DPA](https://stacks.math.columbia.edu/tag/0DPA)
* [Stacks Project, Tag 089S](https://stacks.math.columbia.edu/tag/089S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Grassmannian

/-- Bookkeeping in an arbitrary category: `(f ≫ e.hom) ≫ e.inv = f`, stated so that it can be
applied to morphisms of `X.Modules` whose source is spelled as a free sheaf of modules. -/
theorem comp_hom_comp_inv {C : Type*} [Category* C] {A B D : C} (f : A ⟶ B) (e : B ≅ D) :
    (f ≫ e.hom) ≫ e.inv = f := by
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Bookkeeping in an arbitrary category: composing two triangles. -/
theorem comp_hom_comp_hom_of_eq {C : Type*} [Category* C] {A B D E : C} (f : A ⟶ B) (e : B ≅ D)
    (e' : D ≅ E) (g : A ⟶ D) (h : A ⟶ E) (he : f ≫ e.hom = g) (he' : g ≫ e'.hom = h) :
    f ≫ e.hom ≫ e'.hom = h := by
  rw [← Category.assoc, he, he']

/-- Bookkeeping in an arbitrary category: a triangle followed by the inverse of a square. -/
theorem comp_hom_comp_inv_of_eq {C : Type*} [Category* C] {A A₀ B B' D : C} (a : A ⟶ B)
    (e₁ : B ≅ B') (b : A ⟶ B') (h₁ : a ≫ e₁.hom = b) (c : A₀ ⟶ D) (e : D ≅ B') (i : A₀ ≅ A)
    (he : c ≫ e.hom = i.hom ≫ b) : a ≫ e₁.hom ≫ e.inv = i.inv ≫ c := by
  rw [← Category.assoc, h₁, Iso.comp_inv_eq, Category.assoc, he, Iso.inv_hom_id_assoc]

/-- **Presentations with the same class are isomorphic**: `QuotientPresentation.Isomorphic` is
already an equivalence relation, so the equivalence relation it generates adds nothing. -/
theorem QuotientPresentation.isomorphic_of_mk_eq {X : Scheme.{u}} {k N : ℕ}
    {q q' : QuotientPresentation X k N} (h : (⟦q⟧ : Points X k N) = ⟦q'⟧) :
    q.Isomorphic q' := by
  have hr := Quotient.exact h
  change Relation.EqvGen QuotientPresentation.Isomorphic q q' at hr
  clear h
  induction hr with
  | rel _ _ h => exact h
  | refl q => exact ⟨Iso.refl _, Category.comp_id _⟩
  | symm q q' _ ih =>
    obtain ⟨e, he⟩ := ih
    refine ⟨e.symm, ?_⟩
    rw [← he]
    exact comp_hom_comp_inv q.map e
  | trans q q' q'' _ _ ih ih' =>
    obtain ⟨e, he⟩ := ih
    obtain ⟨e', he'⟩ := ih'
    exact ⟨e ≪≫ e', comp_hom_comp_hom_of_eq q.map e e' q'.map q''.map he he'⟩

/-- **A universal quotient on `G(k, N)`**: a representative of the class of the identity of
`AlgebraicGeometry.Grassmannian.scheme k N` under its representability. -/
def universalPresentation (k N : ℕ) : QuotientPresentation (scheme.{u} k N) k N :=
  Quotient.out ((functorData.{u} k N).objEquiv _
    ((schemeRepresentableBy.{u} k N).homEquiv (𝟙 _)))

/-- **The class of `g : T ⟶ G(k, N)` is the pullback of the universal quotient**: any
presentation `q` on `T` whose class is the image of `g` under the representability is isomorphic
to `g^* q_G`. -/
theorem isomorphic_pullbackPresentation_universalPresentation {k N : ℕ} {T : Scheme.{u}}
    (g : T ⟶ scheme.{u} k N) (q : QuotientPresentation T k N)
    (hq : (functorData.{u} k N).objEquiv T ((schemeRepresentableBy.{u} k N).homEquiv g) = ⟦q⟧) :
    q.Isomorphic (pullbackPresentation g (universalPresentation k N)) := by
  obtain ⟨q', hq', ⟨e, he⟩⟩ := (functorData.{u} k N).map_isPullback g (universalPresentation k N)
  have hid : ((functorData.{u} k N).objEquiv _).symm ⟦universalPresentation k N⟧ =
      (schemeRepresentableBy.{u} k N).homEquiv (𝟙 _) :=
    (Equiv.symm_apply_eq _).2 (Quotient.out_eq _)
  have hg : (schemeRepresentableBy.{u} k N).homEquiv g =
      (functorData.{u} k N).toFunctor.map g.op
        ((schemeRepresentableBy.{u} k N).homEquiv (𝟙 _)) :=
    (congrArg (schemeRepresentableBy.{u} k N).homEquiv (Category.comp_id g).symm).trans
      ((schemeRepresentableBy.{u} k N).homEquiv_comp g (𝟙 _))
  rw [hid, ← hg, hq] at hq'
  obtain ⟨e₁, h₁⟩ := QuotientPresentation.isomorphic_of_mk_eq hq'
  exact ⟨e₁ ≪≫ e.symm, comp_hom_comp_inv_of_eq q.map e₁ q'.map h₁
    ((Scheme.Modules.pullback g).map (universalPresentation k N).map) e (pullbackFreeIso g N) he⟩

end AlgebraicGeometry.Grassmannian

namespace AlgebraicGeometry.ProjectiveQuot

variable {n r : ℕ} (hr : 1 ≤ r) {P : Polynomial ℚ}

/-- **`(T ⟶ G)^* q_G ≅ π_*(𝒬(m))`.** The presentation
`𝒪_T^{⊕ N} ≅ π_*(𝒪^{⊕ r}(m)) ⟶ π_*(𝒬(m))` of `K ∈ Quot^P(T)` is isomorphic to the pullback of
the universal quotient along the classifying morphism `toGrassmannian K : T ⟶ G(N - p, N)`. -/
theorem grassmannianPresentation_isomorphic_pullback
    (hp : quotRank.{u} n r hr P ≤ freeRank.{u} n r (regularityIndex.{u} n r hr P))
    {T : Scheme.{u}} {K : Subobject (freeModule n r T)} (hK : K ∈ hilbertFamilies n r P T) :
    (grassmannianPresentation hr hp hK).Isomorphic
      (Grassmannian.pullbackPresentation (toGrassmannian hr hp hK)
        (Grassmannian.universalPresentation _ _)) :=
  Grassmannian.isomorphic_pullbackPresentation_universalPresentation _ _ (by
    rw [toGrassmannian, Equiv.apply_symm_apply, grassmannianPoint, Equiv.apply_symm_apply])

end AlgebraicGeometry.ProjectiveQuot

end
