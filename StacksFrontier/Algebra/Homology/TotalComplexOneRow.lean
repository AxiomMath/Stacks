module

public import StacksFrontier.Algebra.Homology.MapTotalComplex

/-!
# An additive functor commutes with a totalization with only one nonzero row

`StacksFrontier.Algebra.Homology.MapTotalComplex` makes an additive functor `G` commute with the
total complex of a bicomplex `K` as soon as `G` preserves the coproducts indexed by the
summands of each total degree.  That hypothesis is a genuine restriction: for a general affine
morphism of schemes the direct image of sheaves of modules does *not* preserve infinite direct
sums, so it is unavailable exactly where the projection formula for an affine morphism needs it.

This file supplies the weaker input that suffices there.  A coproduct all but one of whose
summands is zero is carried by *any* functor preserving zero morphisms to a coproduct: the
inclusion of the possibly-nonzero summand is already an isomorphism, so nothing is being
preserved beyond isomorphisms and zero objects.  Hence an additive functor commutes with the
totalization of a bicomplex with a single nonzero row, with no preservation hypothesis at all.

## Main results

* `CategoryTheory.Limits.isIso_cofan_inj_of_isZero`: in a colimit cofan all but one of whose
  summands is zero, the inclusion of that summand is an isomorphism.
* `CategoryTheory.Limits.Cofan.isColimitOfIsIsoInjOfIsZero`: the converse — a cofan all but
  one of whose summands is zero and whose inclusion of that summand is invertible is a colimit.
* `CategoryTheory.Limits.isColimitMapCofanOfIsZero`: **a functor preserving zero morphisms
  preserves a coproduct all but one of whose summands is zero.**  No additivity and no
  preservation of colimits is required.
* `HomologicalComplex₂.TotalMap.isIso_totalMapf_of_isZero`: the comparison
  `Tot(G(K))^n ⟶ G(Tot(K)^n)` is invertible when at most one summand of total degree `n` is
  nonzero.
* `HomologicalComplex₂.TotalMap.isIso_totalMap_of_isZero_row`: **an additive functor commutes
  with the total complex of a bicomplex of cochain complexes with only one nonzero row**,
  `Tot(G(K)) ≅ G(Tot(K))`, with no boundedness hypothesis in the other direction and no
  coproduct-preservation hypothesis on the functor.

## Implementation notes

The three cofan lemmas are stated for a bare `HasZeroMorphisms` category rather than a
preadditive one, and the functor hypothesis is `PreservesZeroMorphisms` rather than `Additive`,
because that is all the argument uses: the descent out of the coproduct is built from the
`IsZero.to_` of the vanishing summands and the identity of the surviving one.

`isIso_totalMapf_of_isZero` takes the surviving bidegree `i₀` together with a proof that it has
total degree `n`.  It is *not* assumed that the summand at `i₀` is itself nonzero, so the lemma
also covers a total degree in which every summand vanishes, provided some bidegree of that total
degree is named; for the shapes `(ℤ, ℤ) → ℤ` of a bicomplex of cochain complexes such a bidegree
always exists, which is why `isIso_totalMap_of_isZero_row` needs only the index of the nonzero
row.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace CategoryTheory.Limits

universe v v' u u'

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]

section ZeroMorphisms

variable [HasZeroMorphisms C]

omit [HasZeroMorphisms C] in
/-- **In a colimit cofan all but one of whose summands is zero, the inclusion of that summand is
an isomorphism.**  The inverse is the descent which is the identity on the surviving summand and
zero on the others. -/
lemma isIso_cofan_inj_of_isZero {J : Type*} {X : J → C} {c : Cofan X} (hc : IsColimit c)
    (j₀ : J) (hz : ∀ j, j ≠ j₀ → IsZero (X j)) : IsIso (c.inj j₀) := by
  classical
  refine ⟨Cofan.IsColimit.desc hc
    (fun j => if h : j = j₀ then eqToHom (congrArg X h) else (hz j h).to_ (X j₀)), ?_, ?_⟩
  · rw [Cofan.IsColimit.fac, dite_eq_left rfl]
    exact eqToHom_refl _ _
  · refine Cofan.IsColimit.hom_ext hc _ _ fun j => ?_
    rw [Category.comp_id]
    by_cases h : j = j₀
    · subst h
      rw [← Category.assoc, Cofan.IsColimit.fac, dite_eq_left rfl, eqToHom_refl, Category.id_comp]
    · exact (hz j h).eq_of_src _ _

/-- **A cofan all but one of whose summands is zero and whose inclusion of that summand is
invertible is a colimit.**  This is the converse of `isIso_cofan_inj_of_isZero`. -/
def Cofan.isColimitOfIsIsoInjOfIsZero {J : Type*} {X : J → C} (c : Cofan X) (j₀ : J)
    (hz : ∀ j, j ≠ j₀ → IsZero (X j)) (h : IsIso (c.inj j₀)) : IsColimit c := by
  letI := h
  refine Cofan.IsColimit.mk _ (fun t => inv (c.inj j₀) ≫ t.inj j₀) (fun t j => ?_)
    (fun t m hm => ?_)
  · by_cases hj : j = j₀
    · subst hj
      rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
    · exact (hz j hj).eq_of_src _ _
  · rw [← hm j₀, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

/-- **A functor preserving zero morphisms preserves a coproduct all but one of whose summands is
zero.**  There is no additivity hypothesis and no hypothesis of preservation of colimits: the
inclusion of the surviving summand is an isomorphism by `isIso_cofan_inj_of_isZero`, the functor
carries it to an isomorphism and the other summands to zero objects, and
`Cofan.isColimitOfIsIsoInjOfIsZero` puts the cofan back together.

This is the input that replaces preservation of infinite direct sums in the projection formula
for an affine morphism, where that preservation is false. -/
def isColimitMapCofanOfIsZero [HasZeroMorphisms D] {J : Type*} {X : J → C} {c : Cofan X}
    (hc : IsColimit c) (j₀ : J) (hz : ∀ j, j ≠ j₀ → IsZero (X j))
    (G : C ⥤ D) [G.PreservesZeroMorphisms] :
    IsColimit (Cofan.mk (G.obj c.pt) fun j => G.map (c.inj j)) := by
  letI := isIso_cofan_inj_of_isZero hc j₀ hz
  exact Cofan.isColimitOfIsIsoInjOfIsZero _ j₀ (fun j hj => G.map_isZero (hz j hj))
    (inferInstanceAs (IsIso (G.map (c.inj j₀))))

end ZeroMorphisms

end CategoryTheory.Limits

namespace HomologicalComplex₂.TotalMap

universe v v' u u' i₁ i₂ i₁₂

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [Preadditive C] [Preadditive D]
  {I₁ : Type i₁} {I₂ : Type i₂} {I₁₂ : Type i₁₂}
  {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂} {c₁₂ : ComplexShape I₁₂}
  [TotalComplexShape c₁ c₂ c₁₂] [DecidableEq I₁₂]
  (G : C ⥤ D) [G.Additive]

section Degreewise

variable (K : HomologicalComplex₂ C c₁ c₂)
  [K.HasTotal c₁₂] [(mapBicomplex G K).HasTotal c₁₂]

/-- **The comparison `Tot(G(K))^n ⟶ G(Tot(K)^n)` is invertible when at most one summand of
total degree `n` is nonzero.**  The surviving bidegree `i₀` is named explicitly, together with a
proof that its total degree is `n`; the summand there is not assumed nonzero, so the statement
also covers a total degree all of whose summands vanish. -/
lemma isIso_totalMapf_of_isZero (n : I₁₂) (i₀ : I₁ × I₂)
    (h₀ : ComplexShape.π c₁ c₂ c₁₂ i₀ = n)
    (hz : ∀ i : I₁ × I₂, ComplexShape.π c₁ c₂ c₁₂ i = n → i ≠ i₀ → IsZero ((K.X i.1).X i.2)) :
    IsIso (totalMapf (c₁₂ := c₁₂) G K n) :=
  isIso_totalMapf_of_isColimit G K n
    (isColimitMapCofanOfIsZero
      (K.toGradedObject.isColimitCofanMapObj (ComplexShape.π c₁ c₂ c₁₂) n) ⟨i₀, h₀⟩
      (fun i hi => hz i.1 i.2 fun h => hi (Subtype.ext h)) G)

end Degreewise

/-- **An additive functor commutes with the total complex of a bicomplex of cochain complexes
with only one nonzero row**: if `K.X p` is the zero complex for every `p ≠ p₀` then the
comparison `Tot(G(K)) ⟶ G(Tot(K))` is an isomorphism.

There is no boundedness hypothesis in the surviving row and — unlike
`HomologicalComplex₂.TotalMap.totalIso` — no hypothesis that `G` preserve coproducts. -/
lemma isIso_totalMap_of_isZero_row
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)] [(mapBicomplex G K).HasTotal (ComplexShape.up ℤ)]
    (p₀ : ℤ) (hz : ∀ p, p ≠ p₀ → ∀ q, IsZero ((K.X p).X q)) :
    IsIso (totalMap (c₁₂ := ComplexShape.up ℤ) G K) := by
  have h : ∀ n, IsIso (totalMapf (c₁₂ := ComplexShape.up ℤ) G K n) := fun n => by
    refine isIso_totalMapf_of_isZero G K n (p₀, n - p₀) (by change p₀ + (n - p₀) = n; omega) ?_
    rintro ⟨p, q⟩ hpq hne
    have hpq' : p + q = n := hpq
    refine hz p (fun hp => hne ?_) q
    subst hp
    have : q = n - p := by omega
    rw [this]
  rw [← totalIsoOfIsIso_hom_eq_totalMap (c₁₂ := ComplexShape.up ℤ) G K h]
  exact (totalIsoOfIsIso (c₁₂ := ComplexShape.up ℤ) G K h).isIso_hom

end HomologicalComplex₂.TotalMap

end
