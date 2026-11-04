module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackToposRightUnitorUnconditional
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorBraiding
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalSheafTensorBraidingUnitor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorCoproductRight
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafCoherence

/-! # The left-unitor coherence of Stacks 03EL, unconditionally

Let `f : (Sh(C), 𝒪_C) ⟶ (Sh(D), 𝒪_D)` be a morphism of ringed topoi in the four-field sense of
Stacks 03D6. The comparison of **Stacks 03EL**, `f^*(F ⊗_{𝒪_D} G) ≅ f^*F ⊗_{𝒪_C} f^*G`, is
compatible with the **left** unitor: comparing, cancelling the pulled-back structure sheaf in the
*first* tensor factor against `𝒪_C` and then applying the left unitor `𝒪_C ⊗_{𝒪_C} - ≅ -` is the
pullback of the left unitor downstairs. The coherence is stated for ringed topoi whose sections
live in `max u v`, and its inverted form for ringed topoi in a single universe.

The **right**-unitor coherence is
`Stacks.Sheaves.RingedToposModules.pullbackTensorIso_hom_app_comp_rightUnitor_unitComparison`.

## Main results

* `Stacks.SheafOfModules.tensorSheafBraiding_hom_eq_sheafTensorBraiding`: the two spellings of
  the braiding of the tensor product sheaf — the sectionwise
  `Stacks.SheafOfModules.tensorSheafBraiding` and the bifunctor-level
  `Stacks.SheafOfModules.Tensor.sheafTensorBraiding` — are the same morphism.
* `Stacks.SheafOfModules.pullbackTensorIso_hom_app_comp_sheafTensorBraiding`: the braiding
  compatibility of Stacks 03EL, restated at the second spelling.
* `Stacks.Sheaves.RingedToposModules.pullbackTensorIso_hom_app_comp_leftUnitor_unitComparison`:
  **the four-field left-unitor coherence of Stacks 03EL**, at the unit comparison
  `Stacks.Sheaves.RingedToposModules.pullbackModulesUnitComparison`, with no hypothesis.
* `Stacks.Sheaves.RingedToposModules.map_tensorSheafUnitLeftIso_inv_comp_pullbackTensorIso`:
  the same coherence with every isomorphism inverted and the unit comparison replaced by the
  comparison `Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso` of Stacks 03LU.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 06YM](https://stacks.math.columbia.edu/tag/06YM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf AlgebraicGeometry
open Stacks.Sheaves.RingedToposModules

universe w w' v u v' u'

namespace Stacks.SheafOfModules

/-! ## The two spellings of the braiding -/

section BraidingSpelling

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{w}) [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **The sectionwise braiding of the tensor product sheaf is the bifunctor-level one.**
`Stacks.SheafOfModules.tensorSheafBraiding` is the sheafification of the sectionwise braiding of
presheaves of modules, and `Stacks.SheafOfModules.Tensor.sheafTensorBraiding` is that same
sheafified braiding read as an isomorphism of bifunctors, so the two are the same morphism. -/
theorem tensorSheafBraiding_hom_eq_sheafTensorBraiding
    (M N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) :
    (tensorSheafBraiding R.obj (Stacks.SheafOfModules.Tensor.ringSheaf R).property M N).hom =
      ((Stacks.SheafOfModules.Tensor.sheafTensorBraiding R).hom.app M).app N :=
  rfl

omit [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **The unit `𝒪 ⊗_𝒪 ℒ ≅ ℒ` of the strict monoidal structure is the left unitor of the tensor
product sheaf.** `Stacks.SheafOfModules.Strict.unitTensorIso` is
`Stacks.SheafOfModules.tensorSheafUnitLeftIso`. -/
theorem Strict.unitTensorIso_eq
    (R : Sheaf J CommRingCat.{max u v}) [HasWeakSheafify J AddCommGrpCat.{max u v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}] (L : Strict.Mod R) :
    Strict.unitTensorIso R L =
      tensorSheafUnitLeftIso R.obj (Stacks.SheafOfModules.Tensor.ringSheaf R).property L :=
  leftUnitor_eq_tensorSheafLeftUnitor R.obj (Strict.isSheaf_ringSheaf R) L

end BraidingSpelling

section BraidingTransport

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (g : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)
  (F G : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))

/-- **The comparison of Stacks 03EL commutes with the braiding**, in the bifunctor spelling
`Stacks.SheafOfModules.Tensor.sheafTensorBraiding` of the braiding. -/
theorem pullbackTensorIso_hom_app_comp_sheafTensorBraiding :
    (pullbackTensorIso g).hom.app (F, G) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensorBraiding X.O).hom.app
          ((g.pullbackModules).obj F)).app ((g.pullbackModules).obj G) =
      (g.pullbackModules).map
          (((Stacks.SheafOfModules.Tensor.sheafTensorBraiding Y.O).hom.app F).app G) ≫
        (pullbackTensorIso g).hom.app (G, F) := by
  refine Eq.trans (congrArg (fun z ↦ (pullbackTensorIso g).hom.app (F, G) ≫ z)
    (tensorSheafBraiding_hom_eq_sheafTensorBraiding X.O ((g.pullbackModules).obj F)
      ((g.pullbackModules).obj G)).symm) ?_
  refine Eq.trans (pullbackTensorIso_hom_app_comp_braiding g F G) ?_
  exact congrArg (fun z ↦ (g.pullbackModules).map z ≫ (pullbackTensorIso g).hom.app (G, F))
    (tensorSheafBraiding_hom_eq_sheafTensorBraiding Y.O F G)

end BraidingTransport

end Stacks.SheafOfModules

namespace Stacks.Sheaves.RingedToposModules

/-! ## Bookkeeping over an abstract category -/

section Bookkeeping

universe vv uu

variable {D : Type uu} [Category.{vv} D]

/-- **The left-unitor coherence from the right-unitor one.** Given the braided law `β ≫ ρ = λ`
upstairs (`hlamX`) and downstairs (`hlamY`, folded into the pullback), the compatibility of the
comparison with the braiding (`hbr`), the naturality of the braiding at the unit comparison
(`hnat`) and the right-unitor coherence (`hright`), the left-unitor coherence `c ≫ n ≫ lX = ml`
holds. -/
private lemma leftUnitorFromRight {P P' Q Q' U U' T : D}
    (c : P ⟶ Q) (c' : P' ⟶ Q') (bQ : Q ⟶ Q') (bU : U ⟶ U') (n : Q ⟶ U) (n' : Q' ⟶ U')
    (lX : U ⟶ T) (rX : U' ⟶ T) (mb : P ⟶ P') (mr : P' ⟶ T) (ml : P ⟶ T)
    (hlamX : bU ≫ rX = lX) (hbr : c ≫ bQ = mb ≫ c') (hnat : n ≫ bU = bQ ≫ n')
    (hright : c' ≫ n' ≫ rX = mr) (hlamY : mb ≫ mr = ml) :
    c ≫ n ≫ lX = ml := by
  rw [← hlamX, ← hlamY, ← hright, ← Category.assoc n bU rX, hnat]
  simp only [Category.assoc]
  rw [← Category.assoc c bQ (n' ≫ rX), hbr]
  simp only [Category.assoc]

/-- A coherence identity of the shape `c ≫ n ≫ lX = m`, with every isomorphism inverted. -/
private lemma invertLeftUnitor {P Q U T : D} (c : P ⟶ Q) (n : Q ⟶ U) (n' : U ⟶ Q)
    (lX : U ⟶ T) (lX' : T ⟶ U) (m : P ⟶ T) (m' : T ⟶ P)
    (h : c ≫ n ≫ lX = m) (hm : m' ≫ m = 𝟙 T) (hl : lX ≫ lX' = 𝟙 U) (hn : n ≫ n' = 𝟙 Q) :
    m' ≫ c = lX' ≫ n' := by
  rw [← Category.id_comp (lX' ≫ n'), ← hm, ← h]
  simp [reassoc_of% hl, hn]

end Bookkeeping

/-! ## The coherence -/

section LeftUnitor

variable {X : RingedTopos.{v, u, max u v}} {Y : RingedTopos.{v', u', max u' v'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{max u' v'} RingCat.{max u' v'})]
  [X.J.HasSheafCompose (forget RingCat.{max u v})]
  [Y.J.HasSheafCompose (forget RingCat.{max u' v'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{max u v})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{max u' v'})]
  [HasWeakSheafify X.J AddCommGrpCat.{max u v}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify Y.J AddCommGrpCat.{max u' v'}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{max u' v'}]
  (g : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)
  (A : SheafOfModules.{max u' v'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))

/-- **The left-unitor coherence of Stacks 03EL for an arbitrary morphism of ringed topoi, at the
canonical unit comparison.** The comparison `f^*(𝒪_D ⊗_{𝒪_D} A) ⟶ f^*𝒪_D ⊗_{𝒪_C} f^*A`, followed
by `ν ⊗ 𝟙` for the unit comparison
`Stacks.Sheaves.RingedToposModules.pullbackModulesUnitComparison` and by the left unitor
`𝒪_C ⊗_{𝒪_C} f^*A ≅ f^*A`, is the pullback of the left unitor downstairs. -/
theorem pullbackTensorIso_hom_app_comp_leftUnitor_unitComparison :
    (Stacks.SheafOfModules.pullbackTensorIso g).hom.app
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O), A) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map
            (pullbackModulesUnitComparison g)).app ((g.pullbackModules).obj A) ≫
          (Stacks.SheafOfModules.tensorSheafUnitLeftIso X.O.obj
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property ((g.pullbackModules).obj A)).hom =
      (g.pullbackModules).map
        (Stacks.SheafOfModules.tensorSheafUnitLeftIso Y.O.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property A).hom := by
  have hlamX : ((Stacks.SheafOfModules.Tensor.sheafTensorBraiding X.O).hom.app
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).app
          ((g.pullbackModules).obj A) ≫
        (Stacks.SheafOfModules.tensorSheafUnitRightIso X.O.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property ((g.pullbackModules).obj A)).hom =
      (Stacks.SheafOfModules.tensorSheafUnitLeftIso X.O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property ((g.pullbackModules).obj A)).hom :=
    _root_.SheafOfModules.sheafTensorBraiding_comp_tensorSheafUnitRightIso X.O
      ((g.pullbackModules).obj A)
  have hlamY : ((Stacks.SheafOfModules.Tensor.sheafTensorBraiding Y.O).hom.app
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).app A ≫
        (Stacks.SheafOfModules.tensorSheafUnitRightIso Y.O.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property A).hom =
      (Stacks.SheafOfModules.tensorSheafUnitLeftIso Y.O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property A).hom :=
    _root_.SheafOfModules.sheafTensorBraiding_comp_tensorSheafUnitRightIso Y.O A
  have hnat : ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map
            (pullbackModulesUnitComparison g)).app ((g.pullbackModules).obj A) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensorBraiding X.O).hom.app
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).app
          ((g.pullbackModules).obj A) =
      ((Stacks.SheafOfModules.Tensor.sheafTensorBraiding X.O).hom.app
            ((g.pullbackModules).obj
              (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))).app
          ((g.pullbackModules).obj A) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
          ((g.pullbackModules).obj A)).map (pullbackModulesUnitComparison g) :=
    NatTrans.congr_app
      ((Stacks.SheafOfModules.Tensor.sheafTensorBraiding X.O).hom.naturality
        (pullbackModulesUnitComparison g)) ((g.pullbackModules).obj A)
  refine leftUnitorFromRight
    ((Stacks.SheafOfModules.pullbackTensorIso g).hom.app
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O), A))
    ((Stacks.SheafOfModules.pullbackTensorIso g).hom.app
      (A, SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (((Stacks.SheafOfModules.Tensor.sheafTensorBraiding X.O).hom.app
        ((g.pullbackModules).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))).app
      ((g.pullbackModules).obj A))
    (((Stacks.SheafOfModules.Tensor.sheafTensorBraiding X.O).hom.app
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).app
      ((g.pullbackModules).obj A))
    (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map
      (pullbackModulesUnitComparison g)).app ((g.pullbackModules).obj A))
    (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
      ((g.pullbackModules).obj A)).map (pullbackModulesUnitComparison g))
    (Stacks.SheafOfModules.tensorSheafUnitLeftIso X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property ((g.pullbackModules).obj A)).hom
    (Stacks.SheafOfModules.tensorSheafUnitRightIso X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property ((g.pullbackModules).obj A)).hom
    ((g.pullbackModules).map
      (((Stacks.SheafOfModules.Tensor.sheafTensorBraiding Y.O).hom.app
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).app A))
    ((g.pullbackModules).map
      (Stacks.SheafOfModules.tensorSheafUnitRightIso Y.O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property A).hom)
    ((g.pullbackModules).map
      (Stacks.SheafOfModules.tensorSheafUnitLeftIso Y.O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property A).hom)
    hlamX
    (Stacks.SheafOfModules.pullbackTensorIso_hom_app_comp_sheafTensorBraiding g
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) A)
    hnat
    (pullbackTensorIso_hom_app_comp_rightUnitor_unitComparison g A)
    ?_
  exact ((g.pullbackModules).map_comp _ _).symm.trans (congrArg (g.pullbackModules).map hlamY)

end LeftUnitor

/-! ## The coherence with every isomorphism inverted -/

section LeftUnitorInv

universe uu

variable {X Y : RingedTopos.{uu, uu, uu}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{uu} RingCat.{uu})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{uu} RingCat.{uu})]
  [X.J.HasSheafCompose (forget RingCat.{uu})] [Y.J.HasSheafCompose (forget RingCat.{uu})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{uu})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{uu})]
  [HasWeakSheafify X.J AddCommGrpCat.{uu}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{uu}]
  [HasWeakSheafify Y.J AddCommGrpCat.{uu}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{uu}]
  (g : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)
  (A : SheafOfModules.{uu} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))

/-- **The left-unitor coherence of Stacks 03EL with every isomorphism inverted**, and the unit
comparison replaced by the comparison `𝒪_C ≅ f^*𝒪_D` of Stacks 03LU: the pullback of the inverse
left unitor followed by the comparison of Stacks 03EL is the inverse left unitor upstairs
followed by `Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso` in the first tensor
factor. -/
theorem map_tensorSheafUnitLeftIso_inv_comp_pullbackTensorIso :
    (g.pullbackModules).map
          (Stacks.SheafOfModules.tensorSheafUnitLeftIso Y.O.obj
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property A).inv ≫
        (Stacks.SheafOfModules.pullbackTensorIso g).hom.app
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O), A) =
      (Stacks.SheafOfModules.tensorSheafUnitLeftIso X.O.obj
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property ((g.pullbackModules).obj A)).inv ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map
          (pullbackModulesObjUnitIso g).hom).app ((g.pullbackModules).obj A) := by
  have hn : ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map
            (pullbackModulesUnitComparison g)).app ((g.pullbackModules).obj A) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map
          (pullbackModulesObjUnitIso g).hom).app ((g.pullbackModules).obj A) = 𝟙 _ := by
    refine Eq.trans (congrArg (fun z ↦ ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map z).app
        ((g.pullbackModules).obj A) ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map
        (pullbackModulesObjUnitIso g).hom).app ((g.pullbackModules).obj A))
      (pullbackModulesUnitComparison_eq_inv g)) ?_
    exact NatTrans.congr_app
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).mapIso
        (pullbackModulesObjUnitIso g)).inv_hom_id ((g.pullbackModules).obj A)
  exact invertLeftUnitor
    ((Stacks.SheafOfModules.pullbackTensorIso g).hom.app
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O), A))
    (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map
      (pullbackModulesUnitComparison g)).app ((g.pullbackModules).obj A))
    (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map
      (pullbackModulesObjUnitIso g).hom).app ((g.pullbackModules).obj A))
    (Stacks.SheafOfModules.tensorSheafUnitLeftIso X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property ((g.pullbackModules).obj A)).hom
    (Stacks.SheafOfModules.tensorSheafUnitLeftIso X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property ((g.pullbackModules).obj A)).inv
    ((g.pullbackModules).map
      (Stacks.SheafOfModules.tensorSheafUnitLeftIso Y.O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property A).hom)
    ((g.pullbackModules).map
      (Stacks.SheafOfModules.tensorSheafUnitLeftIso Y.O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property A).inv)
    (pullbackTensorIso_hom_app_comp_leftUnitor_unitComparison g A)
    ((g.pullbackModules).mapIso (Stacks.SheafOfModules.tensorSheafUnitLeftIso Y.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property A)).inv_hom_id
    (Iso.hom_inv_id _) hn

end LeftUnitorInv

end Stacks.Sheaves.RingedToposModules

end
