module

public import Mathlib.Algebra.Homology.Embedding.HomEquiv
public import Mathlib.Algebra.Homology.Embedding.StupidTrunc

/-!
# The inclusion and the projection of a stupid truncation

Let `e : c.Embedding c'` be an embedding of complex shapes and `K` a homological complex of
shape `c'`. The stupid truncation `K.stupidTrunc e` agrees with `K` in the degrees in the image
of `e` and vanishes elsewhere.

## Main definitions

* `HomologicalComplex.ιStupidTrunc`: when `e` is `IsTruncGE`, the inclusion
  `K.stupidTrunc e ⟶ K`.
* `HomologicalComplex.πStupidTrunc`: when `e` is `IsTruncLE`, the projection
  `K ⟶ K.stupidTrunc e`.

Both are isomorphisms in the degrees in the image of `e`.
-/

@[expose] public section

open CategoryTheory Category Limits

namespace HomologicalComplex

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]
  {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  (K : HomologicalComplex C c') (e : c.Embedding c')

/-- The differential of a stupid truncation, read through `stupidTruncXIso`. -/
lemma stupidTrunc_d_eq [e.IsRelIff] {i j : ι} {i' j' : ι'} (hi : e.f i = i')
    (hj : e.f j = j') :
    (K.stupidTrunc e).d i' j' = (K.stupidTruncXIso e hi).hom ≫ K.d i' j' ≫
      (K.stupidTruncXIso e hj).inv := by
  subst hi hj
  simp only [stupidTrunc, (K.restriction e).extend_d_eq e rfl rfl, restriction_d, stupidTruncXIso,
    Iso.trans_hom, eqToIso.hom, Iso.trans_inv, eqToIso.inv, assoc]
  erw [eqToHom_refl, eqToHom_refl, id_comp, id_comp]
  rfl

open Classical in
/-- The inclusion `K.stupidTrunc e ⟶ K` of a stupid truncation along an embedding `e` which is
`IsTruncGE`: it is `stupidTruncXIso` in the degrees in the image of `e` and zero elsewhere. -/
noncomputable def ιStupidTrunc [e.IsTruncGE] : K.stupidTrunc e ⟶ K where
  f i' := if hi' : ∃ i, e.f i = i' then (K.stupidTruncXIso e hi'.choose_spec).hom else 0
  comm' i' j' hij' := by
    by_cases hi' : ∃ i, e.f i = i'
    · obtain ⟨j, hj⟩ := e.mem_next (by rw [← hi'.choose_spec] at hij'; exact hij')
      have hj' : ∃ k, e.f k = j' := ⟨j, hj⟩
      simp [hi', hj', stupidTrunc_d_eq K e hi'.choose_spec hj'.choose_spec]
    · exact (K.isZero_stupidTrunc_X e i' (by simpa using hi')).eq_of_src _ _

/-- In a degree `i' = e.f i`, the inclusion of the stupid truncation is `stupidTruncXIso`. -/
lemma ιStupidTrunc_f [e.IsTruncGE] {i : ι} {i' : ι'} (hi' : e.f i = i') :
    (K.ιStupidTrunc e).f i' = (K.stupidTruncXIso e hi').hom := by
  have h : ∃ k, e.f k = i' := ⟨i, hi'⟩
  obtain rfl : h.choose = i := e.injective_f (by rw [h.choose_spec, hi'])
  simp [ιStupidTrunc, h]

/-- The inclusion of the stupid truncation is an isomorphism in the degrees in the image
of `e`. -/
lemma isIso_ιStupidTrunc_f [e.IsTruncGE] {i : ι} {i' : ι'} (hi' : e.f i = i') :
    IsIso ((K.ιStupidTrunc e).f i') := by
  rw [K.ιStupidTrunc_f e hi']
  infer_instance

/-- The inclusion of the stupid truncation is natural in the complex. -/
@[reassoc (attr := simp)]
lemma stupidTruncMap_ιStupidTrunc [e.IsTruncGE] {K L : HomologicalComplex C c'} (φ : K ⟶ L) :
    stupidTruncMap φ e ≫ L.ιStupidTrunc e = K.ιStupidTrunc e ≫ φ := by
  ext i' : 1
  by_cases hi' : ∃ i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi'
    simp [K.ιStupidTrunc_f e hi, L.ιStupidTrunc_f e hi]
  · exact (K.isZero_stupidTrunc_X e i' (by simpa using hi')).eq_of_src _ _

/-- The projection `K ⟶ K.stupidTrunc e` onto a stupid truncation along an embedding `e` which
is `IsTruncLE`, obtained by extending the identity of `K.restriction e`. -/
noncomputable def πStupidTrunc [e.IsTruncLE] : K ⟶ K.stupidTrunc e :=
  e.liftExtend (𝟙 (K.restriction e)) (fun j hj i' hij' ↦ by
    obtain ⟨i, hi⟩ := e.mem_prev hij'
    exact absurd (hi ▸ hij') (hj.2 i))

/-- The projection onto the stupid truncation is an isomorphism in the degrees in the image
of `e`. -/
lemma isIso_πStupidTrunc_f [e.IsTruncLE] {i : ι} {i' : ι'} (hi' : e.f i = i') :
    IsIso ((K.πStupidTrunc e).f i') :=
  (e.isIso_liftExtend_f_iff _ _ hi').2 (by rw [id_f]; infer_instance)

end HomologicalComplex
