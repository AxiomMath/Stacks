module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedBaseChangePlus

/-!
# A base change map through a resolution of the inverse image

Consider a square of additive functors between abelian categories
```
A --G'--> A'
|F        |F'
v         v
B --G---> B'
```
with `G` and `G'` exact, a natural transformation `α : F ⋙ G ⟶ G' ⋙ F'`, functors
`RF : D(A) ⥤ D(B)` and `RF' : D(A') ⥤ D(B')` with transformations `ε : F ⋙ Q ⟶ Q ⋙ RF` and
`ε' : F' ⋙ Q ⟶ Q ⋙ RF'` from the homotopy categories (such as the units of right derived
functors), and a "base change map" `β : RF ⋙ G ⟶ G' ⋙ RF'` characterized at a complex `K` by
the usual equation: precomposed with `G(ε_K)` it is the localized degreewise `α_K` followed by
`ε'`. If `β`, `ε` and `ε'` are invertible at `K` and at the target `K'` of a quasi-isomorphism
`q : G'(K) ⟶ K'`, then the morphism of complexes `α_K ≫ F'(q) : G(F(K)) ⟶ F'(K')` is a
quasi-isomorphism.

This is the abstract form of the argument comparing the derived base change map with the
degreewise one through acyclic resolutions; the abelian proper base change theorem is fed into
it for étale sheaves. Everything is stated for abstract categories and functors, so that the
statement, once instantiated, is read off the given equations without converting between
spellings of the instances of concrete categories.

## Main results

* `Stacks.Cohomology.DerivedBaseChangeResolution.isIso_Q_map_comp_of_isIso_derivedBaseChange`.

## References

* [Stacks Project, Tag 0DDE](https://stacks.math.columbia.edu/tag/0DDE)
* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.DerivedBaseChangeResolution

variable {A A' B B' : Type*} [Category* A] [Category* A'] [Category* B] [Category* B']
  [Abelian A] [Abelian A'] [Abelian B] [Abelian B']
  [HasDerivedCategory A] [HasDerivedCategory A'] [HasDerivedCategory B] [HasDerivedCategory B']
  (F : A ⥤ B) (G : B ⥤ B') (G' : A ⥤ A') (F' : A' ⥤ B')
  [F.Additive] [F'.Additive] [G.Additive] [G'.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G']

/-- **The degreewise base change comparison through a resolution of the inverse image.** If the
base change map `β : RF ⋙ G ⟶ G' ⋙ RF'` is invertible at `K`, characterized there by `hfac`
through the transformation `H` of homotopy categories which is the class of the degreewise
`α_K` (`hH`), and `ε`, `ε'` are invertible at `K` and `K'`, then `α_K ≫ F'(q)` is an isomorphism
of the derived category for every quasi-isomorphism `q : G'(K) ⟶ K'`: by `hfac`, the localized
`α_K` followed by `ε'` at `G'(K)` is invertible, and naturality of `ε'` along `q` carries it to
the localized `α_K ≫ F'(q)` followed by `ε'` at `K'`. -/
theorem isIso_Q_map_comp_of_isIso_derivedBaseChange (α : F ⋙ G ⟶ G' ⋙ F')
    (RF : DerivedCategory A ⥤ DerivedCategory B) (RF' : DerivedCategory A' ⥤ DerivedCategory B')
    (ε : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    (ε' : F'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF')
    (β : RF ⋙ G.mapDerivedCategory ⟶ G'.mapDerivedCategory ⋙ RF')
    (H : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ G.mapHomotopyCategory (ComplexShape.up ℤ) ⟶
      G'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ F'.mapHomotopyCategory (ComplexShape.up ℤ))
    (K : CochainComplex A ℤ) (K' : CochainComplex A' ℤ)
    (q : (G'.mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶ K') [QuasiIso q]
    (hH : H.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) =
      (HomotopyCategory.quotient B' (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app K))
    (hfac : G.mapDerivedCategoryFactorsh.inv.app
        ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) ≫
      G.mapDerivedCategory.map (ε.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) ≫
      β.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) =
      DerivedCategory.Qh.map (H.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) ≫
        ε'.app ((G'.mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) ≫
        RF'.map (G'.mapDerivedCategoryFactorsh.inv.app
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)))
    (h₁ : IsIso (ε.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)))
    (h₂ : IsIso (ε'.app ((HomotopyCategory.quotient A' (ComplexShape.up ℤ)).obj K')))
    (hbc : IsIso (β.app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)))) :
    IsIso (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app K ≫
      (F'.mapHomologicalComplex (ComplexShape.up ℤ)).map q)) := by
  let K₀ := (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K
  let qb := (HomotopyCategory.quotient A' (ComplexShape.up ℤ)).map q
  have hA : IsIso (DerivedCategory.Qh.map (H.app K₀) ≫
      ε'.app ((G'.mapHomotopyCategory (ComplexShape.up ℤ)).obj K₀)) := by
    have hL : IsIso (G.mapDerivedCategoryFactorsh.inv.app
        ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K₀) ≫
      G.mapDerivedCategory.map (ε.app K₀) ≫ β.app (DerivedCategory.Qh.obj K₀)) := inferInstance
    rw [hfac, ← Category.assoc] at hL
    exact IsIso.of_isIso_comp_right _ (RF'.map (G'.mapDerivedCategoryFactorsh.inv.app K₀))
  have hq : IsIso (DerivedCategory.Qh.map qb) := by
    rw [DerivedCategory.isIso_Qh_map_iff, HomotopyCategory.quotient_map_mem_quasiIso_iff]
    show QuasiIso q
    infer_instance
  have hB : IsIso ((DerivedCategory.Qh.map (H.app K₀) ≫
      DerivedCategory.Qh.map ((F'.mapHomotopyCategory (ComplexShape.up ℤ)).map qb)) ≫
      ε'.app ((HomotopyCategory.quotient A' (ComplexShape.up ℤ)).obj K')) := by
    have e : (DerivedCategory.Qh.map (H.app K₀) ≫
        DerivedCategory.Qh.map ((F'.mapHomotopyCategory (ComplexShape.up ℤ)).map qb)) ≫
        ε'.app ((HomotopyCategory.quotient A' (ComplexShape.up ℤ)).obj K') =
      (DerivedCategory.Qh.map (H.app K₀) ≫
        ε'.app ((G'.mapHomotopyCategory (ComplexShape.up ℤ)).obj K₀)) ≫
        RF'.map (DerivedCategory.Qh.map qb) := by
      have hnat := ε'.naturality qb
      simp only [Functor.comp_map] at hnat
      rw [Category.assoc, Category.assoc]
      exact whisker_eq _ hnat
    rw [e]
    have hr : IsIso (RF'.map (DerivedCategory.Qh.map qb)) := by
      have := hq
      infer_instance
    exact IsIso.comp_isIso' hA hr
  have hC : IsIso (DerivedCategory.Qh.map (H.app K₀) ≫
      DerivedCategory.Qh.map ((F'.mapHomotopyCategory (ComplexShape.up ℤ)).map qb)) :=
    IsIso.of_isIso_comp_right _ (ε'.app ((HomotopyCategory.quotient A' (ComplexShape.up ℤ)).obj K'))
  rw [← Functor.map_comp, hH] at hC
  exact Stacks.Cohomology.DerivedBaseChangePlus.isIso_Q_map_comp_of_isIso_Qh_map F' _ q hC

section Forget

/- The instances of the categories `AX, AX', AY, AY'` are implicit, so that a consumer reads
them off the hypothesis `hy` (whose statement fixes their spelling) instead of synthesizing them
anew. -/
variable {MX MX' MY MY' AX AX' AY AY' : Type*} [Category* MX] [Category* MX'] [Category* MY]
  [Category* MY'] {_ : Category AX} {_ : Category AX'} {_ : Category AY} {_ : Category AY'}
  [Abelian MX] [Abelian MX'] [Abelian MY] [Abelian MY'] {_ : Abelian AX} {_ : Abelian AX'}
  {_ : Abelian AY} {_ : Abelian AY'} [HasDerivedCategory MY'] {_ : HasDerivedCategory AY'}
  {Fm : MX ⥤ MY} {Gm : MY ⥤ MY'} {G'm : MX ⥤ MX'} {F'm : MX' ⥤ MY'}
  {Fa : AX ⥤ AY} {Ga : AY ⥤ AY'} {G'a : AX ⥤ AX'} {F'a : AX' ⥤ AY'}
  [Fm.Additive] [Gm.Additive] [G'm.Additive] [F'm.Additive]
  [Fa.Additive] [Ga.Additive] [G'a.Additive] [F'a.Additive]
  {UX : MX ⥤ AX} {UX' : MX' ⥤ AX'} {UY : MY ⥤ AY} {UY' : MY' ⥤ AY'}
  [UX.Additive] [UX'.Additive] [UY.Additive] [UY'.Additive]
  [PreservesFiniteLimits UY'] [PreservesFiniteColimits UY'] [UY'.ReflectsIsomorphisms]
  [PreservesFiniteLimits G'm] [PreservesFiniteColimits G'm]

omit [UY.Additive] [PreservesFiniteLimits G'm] [PreservesFiniteColimits G'm] in
/-- **Detecting the degreewise base change comparison through forgetful functors.** Consider two
squares of functors `Fm, Gm, G'm, F'm` (say on sheaves of modules) and `Fa, Ga, G'a, F'a` (on
abelian sheaves) with comparisons `αm : Fm ⋙ Gm ⟶ G'm ⋙ F'm` and `αa : Fa ⋙ Ga ⟶ G'a ⋙ F'a`,
related by "forgetful" functors `U` which commute with the four functors up to `σ, τ, σ', τ'`,
compatibly with `αm` and `αa` (`hP`). Let `I` be a bounded below complex and
`i : G'm(I) ⟶ L` a morphism. If the image of `U(I)` under `αa` followed by `F'a` of
`τ' ≫ U(i)` is a quasi-isomorphism, so is `αm_I ≫ F'm(i)`, the forgetful functor on the target
being exact and conservative. -/
theorem isIso_Q_map_natTrans_comp_of_forget
    (αm : Fm ⋙ Gm ⟶ G'm ⋙ F'm) (αa : Fa ⋙ Ga ⟶ G'a ⋙ F'a)
    (σ : UX ⋙ Fa ≅ Fm ⋙ UY) (τ : UY ⋙ Ga ≅ Gm ⋙ UY') (τ' : UX ⋙ G'a ≅ G'm ⋙ UX')
    (σ' : UX' ⋙ F'a ≅ F'm ⋙ UY')
    (hP : ∀ M : MX, Ga.map (σ.hom.app M) ≫ τ.hom.app (Fm.obj M) ≫ UY'.map (αm.app M) =
      αa.app (UX.obj M) ≫ F'a.map (τ'.hom.app M) ≫ σ'.hom.app (G'm.obj M))
    (I : CochainComplex.Plus MX) (L : CochainComplex.Plus MX')
    (i : G'm.mapCochainComplexPlus.obj I ⟶ L)
    (hy : IsIso (DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex αa (ComplexShape.up ℤ)).app
          ((UX.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.obj) ≫
        (F'a.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((NatIso.mapHomologicalComplex τ' (ComplexShape.up ℤ)).hom.app I.obj ≫
            (UX'.mapHomologicalComplex (ComplexShape.up ℤ)).map i.hom)))) :
    IsIso (DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex αm (ComplexShape.up ℤ)).app I.obj ≫
        (F'm.mapHomologicalComplex (ComplexShape.up ℤ)).map i.hom)) := by
  refine Stacks.Cohomology.DerivedBaseChangePlus.isIso_Q_map_of_isIso_Q_map_of_comp_eq UY' _ _
    (HomologicalComplex.Hom.isoOfComponents
      (fun n => Ga.mapIso (σ.app (I.obj.X n)) ≪≫ τ.app (Fm.obj (I.obj.X n))) ?_)
    (HomologicalComplex.Hom.isoOfComponents (fun n => σ'.app (L.obj.X n)) ?_) ?_ hy
  · intro a b _
    have h₁ := τ.hom.naturality (Fm.map (I.obj.d a b))
    have h₂ := σ.hom.naturality (I.obj.d a b)
    dsimp at h₁ h₂ ⊢
    rw [Category.assoc, ← h₁, ← Functor.map_comp_assoc, ← h₂, Functor.map_comp_assoc]
  · intro a b _
    exact (σ'.hom.naturality (L.obj.d a b)).symm
  · ext n
    have h₃ := σ'.hom.naturality (i.hom.f n)
    show (αa.app (UX.obj (I.obj.X n)) ≫
        F'a.map (τ'.hom.app (I.obj.X n) ≫ UX'.map (i.hom.f n))) ≫ σ'.hom.app (L.obj.X n) =
      (Ga.map (σ.hom.app (I.obj.X n)) ≫ τ.hom.app (Fm.obj (I.obj.X n))) ≫
        UY'.map (αm.app (I.obj.X n) ≫ F'm.map (i.hom.f n))
    dsimp at h₃
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% (hP (I.obj.X n))]
    exact whisker_eq _ (whisker_eq _ h₃)

omit [UY.Additive] in
/-- **The base change map at a complex of injectives, detected through forgetful functors.**
Under the hypotheses of `isIso_Q_map_natTrans_comp_of_forget`, with `I` and `L` complexes of
injectives and `i` a quasi-isomorphism, the base change map
`Stacks.Cohomology.DerivedBaseChangePlus.derivedBaseChangePlus` of `αm` is invertible at `I`. -/
theorem isIso_derivedBaseChangePlus_app_of_forget [HasDerivedCategory MX]
    [HasDerivedCategory MX'] [HasDerivedCategory MY] [EnoughInjectives MX] [EnoughInjectives MX']
    [PreservesFiniteLimits Gm] [PreservesFiniteColimits Gm]
    (αm : Fm ⋙ Gm ⟶ G'm ⋙ F'm) (αa : Fa ⋙ Ga ⟶ G'a ⋙ F'a) (τ' : UX ⋙ G'a ≅ G'm ⋙ UX')
    (I : CochainComplex.Plus MX) [∀ n, Injective (I.obj.X n)]
    (L : CochainComplex.Plus MX') [∀ n, Injective (L.obj.X n)]
    (i : G'm.mapCochainComplexPlus.obj I ⟶ L) (hi : QuasiIso i.hom)
    (hy : IsIso (DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex αa (ComplexShape.up ℤ)).app
          ((UX.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.obj) ≫
        (F'a.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((NatIso.mapHomologicalComplex τ' (ComplexShape.up ℤ)).hom.app I.obj ≫
            (UX'.mapHomologicalComplex (ComplexShape.up ℤ)).map i.hom))))
    (σ : UX ⋙ Fa ≅ Fm ⋙ UY) (τ : UY ⋙ Ga ≅ Gm ⋙ UY') (σ' : UX' ⋙ F'a ≅ F'm ⋙ UY')
    (hP : ∀ M : MX, Ga.map (σ.hom.app M) ≫ τ.hom.app (Fm.obj M) ≫ UY'.map (αm.app M) =
      αa.app (UX.obj M) ≫ F'a.map (τ'.hom.app M) ≫ σ'.hom.app (G'm.obj M)) :
    IsIso ((Stacks.Cohomology.DerivedBaseChangePlus.derivedBaseChangePlus Fm F'm Gm G'm αm).app
      (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient _).obj I))) :=
  Stacks.Cohomology.DerivedBaseChangePlus.isIso_derivedBaseChangePlus_app_of_quasiIso _ _ _ _ αm
    I L i hi (isIso_Q_map_natTrans_comp_of_forget αm αa σ τ τ' σ' hP I L i hy)

end Forget

end Stacks.Cohomology.DerivedBaseChangeResolution

end
