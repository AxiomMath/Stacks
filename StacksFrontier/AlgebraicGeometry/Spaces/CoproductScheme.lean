module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductInclusion

/-!
# Inclusions into a coproduct of fppf sheaves are open and closed immersions

Let `F` be the coproduct of a family `Fᵢ` of sheaves on the big fppf site over a scheme `S`,
indexed by an arbitrary type. Each coproduct inclusion `Fᵢ i ⟶ F` is representable by open
immersions and by closed immersions. The summand `Fᵢ i` is complemented by the sheafification of
the join of the images of the other summands, which exhibits `F` as a binary coproduct.

## Main results

* `AlgebraicGeometry.Space.isOpenImmersion_coproductInj`: an inclusion into a coproduct of fppf
  sheaves is representable by open immersions.
* `AlgebraicGeometry.Space.isClosedImmersion_coproductInj`: an inclusion into a coproduct of fppf
  sheaves is representable by closed immersions.

## References

* [Stacks Project, Tag 02WO](https://stacks.math.columbia.edu/tag/02WO)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry

private noncomputable def otherSummandsSubfunctor
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (I : Type v)
    (Fᵢ : I → Sheaf (BigFppfOver.topology B S hS) (Type u))
    (F : Sheaf (BigFppfOver.topology B S hS) (Type u))
    (ι : ∀ i, Fᵢ i ⟶ F) (i : I) :
    Subfunctor F.obj :=
  ⨆ j : {j : I // j ≠ i}, Subfunctor.range (ι j.1).hom

private noncomputable abbrev otherSummandsSheaf
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (I : Type v)
    (Fᵢ : I → Sheaf (BigFppfOver.topology B S hS) (Type u))
    (F : Sheaf (BigFppfOver.topology B S hS) (Type u))
    (ι : ∀ i, Fᵢ i ⟶ F) (i : I) :
    Sheaf (BigFppfOver.topology B S hS) (Type u) := by
  let J := BigFppfOver.topology B S hS
  let K := otherSummandsSubfunctor B S hS I Fᵢ F ι i
  let Ksh := Subfunctor.sheafify J K
  exact ⟨Ksh.toFunctor, (isSheaf_iff_isSheaf_of_type J _).mpr
    (K.sheafify_isSheaf ((isSheaf_iff_isSheaf_of_type J _).mp F.property))⟩

private noncomputable def otherSummandsInclusion
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (I : Type v)
    (Fᵢ : I → Sheaf (BigFppfOver.topology B S hS) (Type u))
    (F : Sheaf (BigFppfOver.topology B S hS) (Type u))
    (ι : ∀ i, Fᵢ i ⟶ F) (i : I) :
    otherSummandsSheaf B S hS I Fᵢ F ι i ⟶ F := by
  let J := BigFppfOver.topology B S hS
  let K := otherSummandsSubfunctor B S hS I Fᵢ F ι i
  exact ⟨(Subfunctor.sheafify J K).ι⟩

private noncomputable def otherSummandMap
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (I : Type v)
    (Fᵢ : I → Sheaf (BigFppfOver.topology B S hS) (Type u))
    (F : Sheaf (BigFppfOver.topology B S hS) (Type u))
    (ι : ∀ i, Fᵢ i ⟶ F) (i j : I) (hji : j ≠ i) :
    Fᵢ j ⟶ otherSummandsSheaf B S hS I Fᵢ F ι i := by
  let J := BigFppfOver.topology B S hS
  let K := otherSummandsSubfunctor B S hS I Fᵢ F ι i
  have r : Subfunctor.range (ι j).hom ≤ K :=
    le_iSup (fun k : {k : I // k ≠ i} ↦ Subfunctor.range (ι k.1).hom) ⟨j, hji⟩
  exact ⟨Subfunctor.toRange (ι j).hom ≫ Subfunctor.homOfLe r ≫
    Subfunctor.homOfLe (K.le_sheafify J)⟩

private theorem otherSummandsMap_comp_inclusion
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (I : Type v)
    (Fᵢ : I → Sheaf (BigFppfOver.topology B S hS) (Type u))
    (F : Sheaf (BigFppfOver.topology B S hS) (Type u))
    (ι : ∀ i, Fᵢ i ⟶ F) (i j : I) (hji : j ≠ i) :
    otherSummandMap B S hS I Fᵢ F ι i j hji ≫
        otherSummandsInclusion B S hS I Fᵢ F ι i = ι j := by
  apply Sheaf.hom_ext
  ext X y
  rfl

private noncomputable def otherSummands_binary_isColimit
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (I : Type v)
    (Fᵢ : I → Sheaf (BigFppfOver.topology B S hS) (Type u))
    (F : Sheaf (BigFppfOver.topology B S hS) (Type u))
    (ι : ∀ i, Fᵢ i ⟶ F)
    (hcoprod : IsColimit (Cofan.mk F ι)) (i : I) :
    IsColimit (BinaryCofan.mk (ι i)
    (otherSummandsInclusion B S hS I Fᵢ F ι i)) := by
  classical
  let G := otherSummandsSheaf B S hS I Fᵢ F ι i
  let g := otherSummandsInclusion B S hS I Fᵢ F ι i
  let s : BinaryCofan (Fᵢ i) G := BinaryCofan.mk (ι i) g
  let family := fun {T : Sheaf (BigFppfOver.topology B S hS) (Type u)}
      (f : Fᵢ i ⟶ T) (h : G ⟶ T) (j : I) =>
    if hj : j = i then hj ▸ f else otherSummandMap B S hS I Fᵢ F ι i j hj ≫ h
  let d := fun {T : Sheaf (BigFppfOver.topology B S hS) (Type u)} (f : Fᵢ i ⟶ T) (h : G ⟶ T) =>
    hcoprod.desc (Cofan.mk T (family f h))
  have fac_self : ∀ {T} (f : Fᵢ i ⟶ T) (h : G ⟶ T), ι i ≫ d f h = f := fun f h ↦ by
    simpa [d, family] using hcoprod.fac (Cofan.mk _ (family f h)) ⟨i⟩
  have fac_ne : ∀ {T} (f : Fᵢ i ⟶ T) (h : G ⟶ T) (j) (hj : j ≠ i),
      ι j ≫ d f h = otherSummandMap B S hS I Fᵢ F ι i j hj ≫ h :=
    fun f h j hj ↦ by simpa [d, family, hj] using hcoprod.fac (Cofan.mk _ (family f h)) ⟨j⟩
  refine BinaryCofan.IsColimit.mk s d fac_self ?_ ?_
  · intro T f h
    let K := otherSummandsSubfunctor B S hS I Fᵢ F ι i
    let J := BigFppfOver.topology B S hS
    apply Sheaf.hom_ext
    change (Subfunctor.sheafify J K).ι ≫ (d f h).hom = h.hom
    apply Subfunctor.to_sheafify_lift_unique (G := K)
      ((isSheaf_iff_isSheaf_of_type J _).mp T.property)
    ext X x
    change (d f h).hom.app X x.1 = h.hom.app X ((Subfunctor.homOfLe (K.le_sheafify J)).app X x)
    obtain ⟨j, hj, y, hy⟩ := by
      have hx : x.1 ∈ K.obj X := x.2
      simpa [K, otherSummandsSubfunctor, Subfunctor.iSup_obj] using hx
    have hv := congrArg (fun k : Fᵢ j ⟶ T => k.hom.app X y) (fac_ne f h j hj)
    exact (congrArg _ hy.symm).trans (hv.trans (congrArg _ (Subtype.ext hy)))
  · intro T f h m hm₁ hm₂
    apply hcoprod.hom_ext
    rintro ⟨j⟩
    change ι j ≫ m = ι j ≫ d f h
    by_cases hj : j = i
    · subst j
      exact hm₁.trans (fac_self f h).symm
    · rw [fac_ne f h j hj, ← hm₂, ← otherSummandsMap_comp_inclusion B S hS I Fᵢ F ι i j hj]
      exact Category.assoc _ _ _

/-- An inclusion into a coproduct of fppf sheaves indexed by an arbitrary type is representable
by open immersions. -/
theorem Space.isOpenImmersion_coproductInj
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (I : Type v)
    (Fᵢ : I → Sheaf (BigFppfOver.topology B S hS) (Type u))
    (F : Sheaf (BigFppfOver.topology B S hS) (Type u))
    (ι : ∀ i, Fᵢ i ⟶ F)
    (hcoprod : IsColimit (Cofan.mk F ι)) (i : I) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (ι i).hom :=
  coproductInl_isOpenImmersion B S hS (Fᵢ i)
    (otherSummandsSheaf B S hS I Fᵢ F ι i) F (ι i)
    (otherSummandsInclusion B S hS I Fᵢ F ι i)
    (otherSummands_binary_isColimit B S hS I Fᵢ F ι hcoprod i)

/-- An inclusion into a coproduct of fppf sheaves indexed by an arbitrary type is representable
by closed immersions. -/
theorem Space.isClosedImmersion_coproductInj
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (I : Type v)
    (Fᵢ : I → Sheaf (BigFppfOver.topology B S hS) (Type u))
    (F : Sheaf (BigFppfOver.topology B S hS) (Type u))
    (ι : ∀ i, Fᵢ i ⟶ F)
    (hcoprod : IsColimit (Cofan.mk F ι)) (i : I) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (ι i).hom :=
  coproductInl_isClosedImmersion B S hS (Fᵢ i)
    (otherSummandsSheaf B S hS I Fᵢ F ι i) F (ι i)
    (otherSummandsInclusion B S hS I Fᵢ F ι i)
    (otherSummands_binary_isColimit B S hS I Fᵢ F ι hcoprod i)

end AlgebraicGeometry

end
