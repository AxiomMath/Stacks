module

public import StacksFrontier.Algebra.Homology.HomotopyCategory.Adjunction
public import StacksFrontier.Algebra.Homology.HomotopyCategory.ExactFunctorHomology
public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeSquare

public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeSquareMates
/-!
# The base change map of the adjunctions induced on homotopy categories

Let `pf ⊣ qf` and `pf' ⊣ qf'` be adjunctions of additive functors between preadditive
categories, and `eg : pg ⋙ pf' ≅ pc`, `ef : pf ⋙ pg' ≅ pc` isomorphisms identifying the two
composites around a square.  The base change map `pg (qf K) ⟶ qf' (pg' K)` of
`Stacks.CategoryTheory.BaseChange.map` can be formed degreewise on complexes, or on the
homotopy categories from the adjunctions `CategoryTheory.Adjunction.mapHomotopyCategory`.  This
file records that the second is the image of the first, so that it is invertible as soon as the
base change map of the underlying functors is.

## Main results

* `Stacks.CategoryTheory.BaseChange.map_mapHomotopyCategory_quotient_obj`: the base change map
  on homotopy categories is the image of the degreewise one.
* `Stacks.CategoryTheory.BaseChange.isIso_map_mapHomotopyCategory`: it is invertible when the
  base change map of the underlying functors is invertible at every object.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace Stacks.CategoryTheory.BaseChange

variable {ι : Type*} (c : ComplexShape ι)
  {VY VX VY' VX' : Type*} [Category* VY] [Category* VX] [Category* VY'] [Category* VX']
  [Preadditive VY] [Preadditive VX] [Preadditive VY'] [Preadditive VX']
  {pf : VY ⥤ VX} {qf : VX ⥤ VY} {pf' : VY' ⥤ VX'} {qf' : VX' ⥤ VY'}
  {pg : VY ⥤ VY'} {pg' : VX ⥤ VX'} {pc : VY ⥤ VX'}
  [pf.Additive] [qf.Additive] [pf'.Additive] [qf'.Additive] [pg.Additive] [pg'.Additive]
  [pc.Additive]
  (a : pf ⊣ qf) (a' : pf' ⊣ qf') (eg : pg ⋙ pf' ≅ pc) (ef : pf ⋙ pg' ≅ pc)

/-- **The base change map on homotopy categories is the image of the degreewise one.** -/
theorem map_mapHomotopyCategory_quotient_obj (K : HomologicalComplex VX c) :
    map (a.mapHomotopyCategory c) (a'.mapHomotopyCategory c)
        (Functor.mapHomotopyCategoryCompIso eg c) (Functor.mapHomotopyCategoryCompIso ef c)
        ((HomotopyCategory.quotient VX c).obj K) =
      (HomotopyCategory.quotient VY' c).map
        ((NatTrans.mapHomologicalComplex (twoSquare a a' eg ef) c).app K) := by
  rw [map_eq, Adjunction.homEquiv_unit]
  refine Eq.trans (b := (HomotopyCategory.quotient VY' c).map
    ((NatTrans.mapHomologicalComplex a'.unit c).app ((pg.mapHomologicalComplex c).obj
        ((qf.mapHomologicalComplex c).obj K)) ≫
      (qf'.mapHomologicalComplex c).map
        ((NatTrans.mapHomologicalComplex eg.hom c).app ((qf.mapHomologicalComplex c).obj K) ≫
          (NatTrans.mapHomologicalComplex ef.inv c).app ((qf.mapHomologicalComplex c).obj K) ≫
          (pg'.mapHomologicalComplex c).map ((NatTrans.mapHomologicalComplex a.counit c).app K))))
    rfl ?_
  congr 1
  ext n
  simp [twoSquare, pullbackComparison, mateEquiv_apply]

section Integers

variable {VY VX VY' VX' : Type*} [Category* VY] [Category* VX] [Category* VY'] [Category* VX']
  [Preadditive VY] [Preadditive VX] [Preadditive VY'] [Preadditive VX']
  {pf : VY ⥤ VX} {qf : VX ⥤ VY} {pf' : VY' ⥤ VX'} {qf' : VX' ⥤ VY'}
  {pg : VY ⥤ VY'} {pg' : VX ⥤ VX'}
  [pf.Additive] [qf.Additive] [pf'.Additive] [qf'.Additive] [pg.Additive] [pg'.Additive]

/-- The comparison for a composite followed by the image of an isomorphism is the comparison for
the composite isomorphism. -/
theorem mapHomotopyCategoryCompIso_trans {pc pc' : VY ⥤ VX'} [pc.Additive] [pc'.Additive]
    (e : pg ⋙ pf' ≅ pc) (e' : pc ≅ pc') :
    Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ) ≪≫
        Stacks.Homology.mapHomotopyCategoryIso e' (ComplexShape.up ℤ) =
      Functor.mapHomotopyCategoryCompIso (e ≪≫ e') (ComplexShape.up ℤ) := by
  ext ⟨K⟩
  refine ((HomotopyCategory.quotient VX' (ComplexShape.up ℤ)).map_comp _ _).symm.trans
    (congrArg (HomotopyCategory.quotient VX' (ComplexShape.up ℤ)).map ?_)
  ext n
  simp

/-- **Invertibility of the base change map on homotopy categories of `ℤ`-indexed complexes, at
one complex**, for identifications of the composites around the square that are composition
isomorphisms followed by transports in a family `P t` along `t₁ = t₂`: it is invertible at a
complex `K` as soon as the base change map of the underlying functors is invertible at every term
of `K`. -/
theorem isIso_map_mapHomotopyCategory_quotient_obj {T : Sort*} (P : T → (VY ⥤ VX'))
    [∀ t, (P t).Additive] {t₁ t₂ : T} (h : t₁ = t₂)
    {pcg pcf : VY ⥤ VX'} [pcg.Additive] [pcf.Additive] (a : pf ⊣ qf) (a' : pf' ⊣ qf')
    (eg₀ : pg ⋙ pf' ≅ pcg) (eg₁ : pcg ≅ P t₂) (ef₀ : pf ⋙ pg' ≅ pcf) (ef₁ : pcf ≅ P t₁)
    (K : CochainComplex VX ℤ)
    (hiso : ∀ n, IsIso (map a a' (eg₀ ≪≫ eg₁) ((ef₀ ≪≫ ef₁) ≪≫ eqToIso (congrArg P h)) (K.X n))) :
    IsIso (map (a.mapHomotopyCategory (ComplexShape.up ℤ))
      (a'.mapHomotopyCategory (ComplexShape.up ℤ))
      (Functor.mapHomotopyCategoryCompIso eg₀ (ComplexShape.up ℤ) ≪≫
        Stacks.Homology.mapHomotopyCategoryIso eg₁ (ComplexShape.up ℤ))
      ((Functor.mapHomotopyCategoryCompIso ef₀ (ComplexShape.up ℤ) ≪≫
        Stacks.Homology.mapHomotopyCategoryIso ef₁ (ComplexShape.up ℤ)) ≪≫
          eqToIso (congrArg (fun t => (P t).mapHomotopyCategory (ComplexShape.up ℤ)) h))
      ((HomotopyCategory.quotient VX (ComplexShape.up ℤ)).obj K)) := by
  subst h
  simp only [eqToIso_refl, Iso.trans_refl] at hiso ⊢
  rw [mapHomotopyCategoryCompIso_trans, mapHomotopyCategoryCompIso_trans,
    map_mapHomotopyCategory_quotient_obj]
  have : ∀ n, IsIso (((NatTrans.mapHomologicalComplex
      (twoSquare a a' (eg₀ ≪≫ eg₁) (ef₀ ≪≫ ef₁)) (ComplexShape.up ℤ)).app K).f n) :=
    fun n => hiso n
  have : IsIso ((NatTrans.mapHomologicalComplex (twoSquare a a' (eg₀ ≪≫ eg₁) (ef₀ ≪≫ ef₁))
      (ComplexShape.up ℤ)).app K) :=
    HomologicalComplex.Hom.isIso_of_components _
  exact Functor.map_isIso _ _

/-- **Invertibility of the base change map on homotopy categories of `ℤ`-indexed complexes**,
for identifications of the composites around the square that are composition isomorphisms
followed by transports in a family `P t` along `t₁ = t₂`: it is invertible at every object as
soon as the base change map of the underlying functors is invertible at every object. -/
theorem isIso_map_mapHomotopyCategory {T : Sort*} (P : T → (VY ⥤ VX')) [∀ t, (P t).Additive]
    {t₁ t₂ : T} (h : t₁ = t₂)
    {pcg pcf : VY ⥤ VX'} [pcg.Additive] [pcf.Additive] (a : pf ⊣ qf) (a' : pf' ⊣ qf')
    (eg₀ : pg ⋙ pf' ≅ pcg) (eg₁ : pcg ≅ P t₂) (ef₀ : pf ⋙ pg' ≅ pcf) (ef₁ : pcf ≅ P t₁)
    (hiso : ∀ M, IsIso (map a a' (eg₀ ≪≫ eg₁) ((ef₀ ≪≫ ef₁) ≪≫ eqToIso (congrArg P h)) M))
    (K : HomotopyCategory VX (ComplexShape.up ℤ)) :
    IsIso (map (a.mapHomotopyCategory (ComplexShape.up ℤ))
      (a'.mapHomotopyCategory (ComplexShape.up ℤ))
      (Functor.mapHomotopyCategoryCompIso eg₀ (ComplexShape.up ℤ) ≪≫
        Stacks.Homology.mapHomotopyCategoryIso eg₁ (ComplexShape.up ℤ))
      ((Functor.mapHomotopyCategoryCompIso ef₀ (ComplexShape.up ℤ) ≪≫
        Stacks.Homology.mapHomotopyCategoryIso ef₁ (ComplexShape.up ℤ)) ≪≫
          eqToIso (congrArg (fun t => (P t).mapHomotopyCategory (ComplexShape.up ℤ)) h)) K) := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  exact isIso_map_mapHomotopyCategory_quotient_obj P h a a' eg₀ eg₁ ef₀ ef₁ K
    (fun n => hiso (K.X n))

omit [pf.Additive] [pf'.Additive] in
/-- The base change map of additive functors is invertible at a zero object. -/
theorem isIso_map_of_isZero [Limits.HasZeroObject VY'] {pc : VY ⥤ VX'} (a : pf ⊣ qf)
    (a' : pf' ⊣ qf') (eg : pg ⋙ pf' ≅ pc) (ef : pf ⋙ pg' ≅ pc) {M : VX} (hM : Limits.IsZero M) :
    IsIso (map a a' eg ef M) :=
  Limits.isIso_of_source_target_iso_zero _
    (Functor.map_isZero pg (Functor.map_isZero qf hM)).isoZero
    (Functor.map_isZero qf' (Functor.map_isZero pg' hM)).isoZero

end Integers

end Stacks.CategoryTheory.BaseChange
