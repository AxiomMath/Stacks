module

public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Transport of conjugates and of composition comparisons

The conjugate of a transformation of left adjoints is characterised by an identity involving
the counits, and it changes by the comparison isomorphisms when the right adjoints are replaced
by isomorphic ones. A composition comparison `p' ⋙ q' ≅ pq'` conjugated by isomorphisms of the
three functors involved is again a composition comparison, and the associativity cocycle law is
preserved by this conjugation.

## Main definitions

* `CategoryTheory.Functor.compConj`: the comparison `p ⋙ q ≅ pq` obtained from a comparison
  `p' ⋙ q' ≅ pq'` and isomorphisms `p ≅ p'`, `q ≅ q'`, `pq ≅ pq'`.

## Main results

* `CategoryTheory.conjugateEquiv_eq_of_counit`: a transformation of right adjoints satisfying
  the counit identity is the conjugate of the given transformation of left adjoints.
* `CategoryTheory.conjugateEquiv_transport`: the conjugate computed with isomorphic right
  adjoints is the original conjugate composed with the two comparison isomorphisms.
* `CategoryTheory.Functor.compConj_compIsoCongrAux`: conjugation is compatible with transport
  along equalities of the functors.
* `CategoryTheory.Functor.compConj_cocycle_app`: the associativity cocycle law is preserved by
  conjugation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor

namespace CategoryTheory

/-! ### Conjugation of transformations of left adjoints -/

section Conjugate

variable {C D : Type*} [Category* C] [Category* D]

/-- If `β : R₁ ⟶ R₂` satisfies
`L₂.map (β.app d) ≫ adj₂.counit.app d = α.app (R₁.obj d) ≫ adj₁.counit.app d` for every `d`,
then `β` is the conjugate of `α`. -/
theorem conjugateEquiv_eq_of_counit {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁)
    (adj₂ : L₂ ⊣ R₂) (α : L₂ ⟶ L₁) (β : R₁ ⟶ R₂)
    (h : ∀ d, L₂.map (β.app d) ≫ adj₂.counit.app d = α.app (R₁.obj d) ≫ adj₁.counit.app d) :
    conjugateEquiv adj₁ adj₂ α = β := by
  refine NatTrans.ext (funext fun d => ?_)
  refine (adj₂.homEquiv (R₁.obj d) d).symm.injective ?_
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, h d,
    conjugateEquiv_counit adj₁ adj₂ α d]

/-- Let `adj₁'` and `adj₂'` be adjunctions with the same left adjoints as `adj₁` and `adj₂`, and
let `u : R₁ ≅ R₁'` and `v : R₂ ≅ R₂'` be isomorphisms of the right adjoints compatible with the
counits. Then the conjugate of `α` with respect to `adj₁'` and `adj₂'` is
`u.inv ≫ conjugateEquiv adj₁ adj₂ α ≫ v.hom`. -/
theorem conjugateEquiv_transport {L₁ L₂ : C ⥤ D} {R₁ R₂ R₁' R₂' : D ⥤ C} (adj₁ : L₁ ⊣ R₁)
    (adj₂ : L₂ ⊣ R₂) (adj₁' : L₁ ⊣ R₁') (adj₂' : L₂ ⊣ R₂') (u : R₁ ≅ R₁') (v : R₂ ≅ R₂')
    (hu : ∀ d, adj₁'.counit.app d = L₁.map (u.inv.app d) ≫ adj₁.counit.app d)
    (hv : ∀ d, adj₂'.counit.app d = L₂.map (v.inv.app d) ≫ adj₂.counit.app d)
    (α : L₂ ⟶ L₁) :
    conjugateEquiv adj₁' adj₂' α = u.inv ≫ conjugateEquiv adj₁ adj₂ α ≫ v.hom := by
  refine conjugateEquiv_eq_of_counit adj₁' adj₂' α _ fun d => ?_
  simp only [NatTrans.comp_app, Functor.map_comp, Category.assoc, hu d, hv d]
  rw [← Category.assoc (L₂.map (v.hom.app d)) (L₂.map (v.inv.app d)) (adj₂.counit.app d),
    ← Functor.map_comp, v.hom_inv_id_app, Functor.map_id, Category.id_comp,
    conjugateEquiv_counit adj₁ adj₂ α d, ← Category.assoc, α.naturality (u.inv.app d),
    Category.assoc]

end Conjugate

/-! ### Conjugation of a composition comparison -/

namespace Functor

section CompConj

variable {A₀ A₁ A₂ : Type*} [Category* A₀] [Category* A₁] [Category* A₂]

/-- A comparison `p' ⋙ q' ≅ pq'` read through isomorphisms `p ≅ p'`, `q ≅ q'` and `pq ≅ pq'`. -/
def compConj {p p' : A₀ ⥤ A₁} {q q' : A₁ ⥤ A₂} {pq pq' : A₀ ⥤ A₂} (up : p ≅ p') (uq : q ≅ q')
    (upq : pq ≅ pq') (P : p' ⋙ q' ≅ pq') : p ⋙ q ≅ pq :=
  isoWhiskerRight up q ≪≫ isoWhiskerLeft p' uq ≪≫ P ≪≫ upq.symm

/-- The component at `N` of `compConj up uq upq P` is
`q.map (up.hom.app N) ≫ uq.hom.app (p'.obj N) ≫ P.hom.app N ≫ upq.inv.app N`. -/
theorem compConj_hom_app {p p' : A₀ ⥤ A₁} {q q' : A₁ ⥤ A₂} {pq pq' : A₀ ⥤ A₂} (up : p ≅ p')
    (uq : q ≅ q') (upq : pq ≅ pq') (P : p' ⋙ q' ≅ pq') (N : A₀) :
    (compConj up uq upq P).hom.app N =
      q.map (up.hom.app N) ≫ uq.hom.app (p'.obj N) ≫ P.hom.app N ≫ upq.inv.app N := by
  simp [compConj]

/-- Conjugating a comparison transported along equalities `p₁ = p₂`, `q₁ = q₂`, `pq₁ = pq₂` by
the isomorphisms composed with those equalities gives the conjugate of the untransported
comparison. -/
theorem compConj_compIsoCongrAux {p p₁ p₂ : A₀ ⥤ A₁} {q q₁ q₂ : A₁ ⥤ A₂}
    {pq pq₁ pq₂ : A₀ ⥤ A₂} (up : p ≅ p₁) (uq : q ≅ q₁) (upq : pq ≅ pq₁) (ep : p₁ = p₂)
    (eq' : q₁ = q₂) (epq : pq₁ = pq₂) (P : p₁ ⋙ q₁ ≅ pq₁) :
    compConj (up ≪≫ eqToIso ep) (uq ≪≫ eqToIso eq') (upq ≪≫ eqToIso epq)
        (eqToIso (by rw [ep, eq']) ≪≫ P ≪≫ eqToIso epq) = compConj up uq upq P := by
  subst ep eq' epq
  refine Iso.ext (NatTrans.ext (funext fun N => ?_))
  simp [compConj_hom_app]

/-- If the composition comparisons `P`, `Q`, `PQ`, `QR` satisfy the associativity cocycle law,
so do their conjugates by isomorphisms of the six functors involved. -/
theorem compConj_cocycle_app {A₃ : Type*} [Category* A₃]
    {p p' : A₀ ⥤ A₁} {q q' : A₁ ⥤ A₂} {r r' : A₂ ⥤ A₃} {pq pq' : A₀ ⥤ A₂}
    {qr qr' : A₁ ⥤ A₃} {pqr pqr' : A₀ ⥤ A₃}
    (up : p ≅ p') (uq : q ≅ q') (ur : r ≅ r') (upq : pq ≅ pq') (uqr : qr ≅ qr')
    (upqr : pqr ≅ pqr') (P : p' ⋙ q' ≅ pq') (Q : q' ⋙ r' ≅ qr') (PQ : pq' ⋙ r' ≅ pqr')
    (QR : p' ⋙ qr' ≅ pqr')
    (h : ∀ N, r'.map (P.hom.app N) ≫ PQ.hom.app N = Q.hom.app (p'.obj N) ≫ QR.hom.app N)
    (N : A₀) :
    r.map ((compConj up uq upq P).hom.app N) ≫ (compConj upq ur upqr PQ).hom.app N =
      (compConj uq ur uqr Q).hom.app (p.obj N) ≫ (compConj up uqr upqr QR).hom.app N := by
  have hP := ur.hom.naturality (P.hom.app N)
  have hq1 := ur.hom.naturality (uq.hom.app (p'.obj N))
  have hq2 := ur.hom.naturality (q.map (up.hom.app N))
  have hq3 := ur.hom.naturality (uq.hom.app (p.obj N))
  have hqr := uqr.hom.naturality (up.hom.app N)
  have hQ := Q.hom.naturality (up.hom.app N)
  have huq := uq.hom.naturality (up.hom.app N)
  simp only [compConj_hom_app, Functor.map_comp, Category.assoc, Functor.comp_map] at *
  rw [← Functor.map_comp_assoc r (upq.inv.app N) (upq.hom.app N), upq.inv_hom_id_app,
    Functor.map_id, Category.id_comp, reassoc_of% hP, reassoc_of% (h N), reassoc_of% hq1,
    reassoc_of% hq2, ← Functor.map_comp_assoc r' (q.map (up.hom.app N))
      (uq.hom.app (p'.obj N)), huq, Functor.map_comp_assoc, reassoc_of% hQ,
    reassoc_of% hq3, reassoc_of% hqr, uqr.inv_hom_id_app_assoc]

end CompConj

end Functor

end CategoryTheory
