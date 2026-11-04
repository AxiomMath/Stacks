module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorStalkRingedSpace
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPreservesColimits
public import StacksFrontier.CategoryTheory.Functor.Bifunctor

/-!
# Presentations of tensor products of sheaves of modules

The relations of a tensor product presentation come from the relations in either factor.
The construction uses the native curried sheaf tensor directly. Right exactness in each
variable follows from preservation of finite colimits; the two presentations are combined
by a generic exactness lemma in an abelian category.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open Stacks.SheafOfModules.Tensor (sheafTensor)

universe u v w u₁

namespace Stacks.SheafOfModules.TensorPresentations

attribute [local implicit_reducible] TensorSheafification.structureSheaf

private lemma exact_biprod_desc_comp {C : Type*} [Category* C] [Abelian C]
    {A B D Z E T : C} (a : A ⟶ B) (p : B ⟶ E) (e : D ⟶ Z) (b : Z ⟶ E)
    (d : D ⟶ B) (q : E ⟶ T)
    (hap : a ≫ p = 0) (hbq : b ≫ q = 0)
    (hde : d ≫ p = e ≫ b)
    (ha : (ShortComplex.mk a p hap).Exact)
    (hb : (ShortComplex.mk b q hbq).Exact) [Epi p] [Epi e] [Epi q] :
    (ShortComplex.mk (biprod.desc a d) (p ≫ q) (by
      apply biprod.hom_ext'
      · simp only [← Category.assoc, biprod.inl_desc, hap, zero_comp, comp_zero]
      · simp only [← Category.assoc, biprod.inr_desc, hde, comp_zero]
        rw [Category.assoc, hbq, comp_zero])).Exact := by
  apply ShortComplex.exact_of_g_is_cokernel
  refine Cofork.IsColimit.mk' _ fun s => ?_
  have ha_zero : a ≫ s.π = 0 := by
    simpa only [← Category.assoc, biprod.inl_desc, zero_comp, comp_zero] using
      congrArg (fun z => biprod.inl ≫ z) s.condition
  let k : E ⟶ s.pt := ha.desc s.π ha_zero
  have hbk : b ≫ k = 0 := by
    apply zero_of_epi_comp e
    calc
      e ≫ b ≫ k = d ≫ p ≫ k := by
        simpa only [Category.assoc] using congrArg (fun z => z ≫ k) hde.symm
      _ = d ≫ s.π := by rw [ha.g_desc]
      _ = biprod.inr ≫ biprod.desc a d ≫ s.π := by
        simp only [← Category.assoc, biprod.inr_desc]
      _ = 0 := by
        simpa only [← Category.assoc, zero_comp, comp_zero] using
          congrArg (fun z => biprod.inr ≫ z) s.condition
  let l : T ⟶ s.pt := hb.desc k hbk
  refine ⟨l, ?_, ?_⟩
  · dsimp [l]
    simp only [Category.assoc, hb.g_desc]
    exact ha.g_desc s.π ha_zero
  · intro m hm
    apply (cancel_epi q).1
    apply (cancel_epi p).1
    calc
      p ≫ q ≫ m = (p ≫ q) ≫ m := (Category.assoc _ _ _).symm
      _ = s.π := hm
      _ = p ≫ k := (ha.g_desc s.π ha_zero).symm
      _ = p ≫ q ≫ l := by rw [hb.g_desc]

private lemma additive_of_preservesFiniteColimits
    {source target : Type*} [Category source] [Category target] [Abelian source] [Abelian target]
    (mapping : source ⥤ target) [PreservesFiniteColimits mapping] : mapping.Additive := by
  let : mapping.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_map_zero_object
      (mapping.mapIso HasZeroObject.zeroIsoInitial ≪≫ PreservesInitial.iso mapping ≪≫
        HasZeroObject.zeroIsoInitial.symm)
  let : PreservesBinaryBiproducts mapping :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts mapping
  exact Functor.additive_of_preservesBinaryBiproducts mapping

/-- A functor preserving finite colimits sends an exact short complex with epi `g` to an exact
short complex. -/
private lemma map_exact_of_preservesFiniteColimits
    {source target : Type*} [Category source] [Category target] [Abelian source] [Abelian target]
    (mapping : source ⥤ target) [PreservesFiniteColimits mapping] (S : ShortComplex source)
    (hS : S.Exact) [Epi S.g] : (S.map mapping).Exact := by
  have := additive_of_preservesFiniteColimits mapping
  have key := ((Functor.preservesFiniteColimits_tfae mapping).out 4 2).mp
    (show PreservesFiniteColimits mapping from inferInstance)
  exact (key S ⟨hS, inferInstance⟩).1

section Site

variable {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})
  (h𝒪 : Presheaf.IsSheaf J (TensorSheafification.structureRingPresheaf 𝒪))
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]
  [HasSheafify J AddCommGrpCat.{w}]

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules

/-- The monoidal structure on presheaves of modules over the underlying presheaf of the structure
sheaf, given by the objectwise tensor product over `𝒪`. -/
noncomputable local instance monoidalPresheafModulesOnSite :
    MonoidalCategory (PresheafOfModules.{w} (TensorSheafification.structureSheaf 𝒪 h𝒪).obj) :=
  PresheafOfModules.monoidalCategory (R := 𝒪)

/-- The symmetric monoidal structure on presheaves of modules over the underlying presheaf of the
structure sheaf, given by the objectwise tensor product over `𝒪` and its braiding. -/
noncomputable local instance symmetricPresheafModulesOnSite :
    SymmetricCategory (PresheafOfModules.{w} (TensorSheafification.structureSheaf 𝒪 h𝒪).obj) :=
  PresheafOfModules.symmetricCategory (R := 𝒪)

private noncomputable def tensorSheafSwapOnSite
    (F G : SheafOfModules.{w} (TensorSheafification.structureSheaf 𝒪 h𝒪)) :
    ((sheafTensor.{u₁, v, w, w, w}
        ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp J 𝒪
          (forget₂ CommRingCat RingCat) h𝒪⟩).obj F).obj G ≅
      ((sheafTensor.{u₁, v, w, w, w}
          ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp J 𝒪
            (forget₂ CommRingCat RingCat) h𝒪⟩).obj G).obj F :=
  (PresheafOfModules.sheafification
    (R := TensorSheafification.structureSheaf 𝒪 h𝒪)
    (𝟙 (TensorSheafification.structureSheaf 𝒪 h𝒪).obj)).mapIso (β_ F.val G.val)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] [HasSheafify J AddCommGrpCat] in
private lemma preservesFiniteColimits_tensorLeft
    (F : SheafOfModules.{w} (TensorSheafification.structureSheaf 𝒪 h𝒪)) :
    PreservesFiniteColimits ((sheafTensor.{u₁, v, w, w, w}
        ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp J 𝒪
          (forget₂ CommRingCat RingCat) h𝒪⟩).obj F) := by
  have : PreservesColimitsOfSize.{w, w}
      ((sheafTensor.{u₁, v, w, w, w}
        ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp J 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj F) :=
    TensorColimits.tensorLeft_preservesColimits.{u₁, v, w, w, w} J
      ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp J 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩ F
  exact PreservesColimitsOfSize.preservesFiniteColimits _

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] [HasSheafify J AddCommGrpCat] in
private lemma preservesFiniteColimits_tensorRight
    (F : SheafOfModules.{w} (TensorSheafification.structureSheaf 𝒪 h𝒪)) :
    PreservesFiniteColimits ((sheafTensor.{u₁, v, w, w, w}
        ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp J 𝒪
          (forget₂ CommRingCat RingCat) h𝒪⟩).flip.obj F) := by
  let := preservesFiniteColimits_tensorLeft 𝒪 h𝒪 F
  let comparison : (sheafTensor.{u₁, v, w, w, w}
      ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp J 𝒪
        (forget₂ CommRingCat RingCat) h𝒪⟩).flip.obj F ≅
      (sheafTensor.{u₁, v, w, w, w}
          ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp J 𝒪
            (forget₂ CommRingCat RingCat) h𝒪⟩).obj F :=
    NatIso.ofComponents (fun left ↦ tensorSheafSwapOnSite 𝒪 h𝒪 left F) (by
      intro leftSource leftTarget leftHom
      exact ((CommSq.mk (BraidedCategory.braiding_naturality
        (C := PresheafOfModules.{w} (𝒪 ⋙ forget₂ CommRingCat RingCat))
        leftHom.val (𝟙 F.val))).map (TensorSheafification.sheafify 𝒪 h𝒪)).w)
  exact preservesFiniteColimits_of_natIso comparison.symm

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The presentation of a tensor product obtained from two presentations, on an arbitrary
site. The two relation maps are the maps in the separate variables of the native bifunctor. -/
lemma exact_tensorSheaf_presentations_on_site
    {F₂ F₁ F G₂ G₁ G : SheafOfModules.{w} (TensorSheafification.structureSheaf 𝒪 h𝒪)}
    (f₂ : F₂ ⟶ F₁) (f₁ : F₁ ⟶ F) (g₂ : G₂ ⟶ G₁) (g₁ : G₁ ⟶ G)
    (hf : (ComposableArrows.mk₂ f₂ f₁).Exact)
    (hg : (ComposableArrows.mk₂ g₂ g₁).Exact) [leftEpi : Epi f₁] [rightEpi : Epi g₁] :
    (ComposableArrows.mk₂
      (biprod.desc (((sheafTensor.{u₁, v, w, w, w}
          ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp J 𝒪
            (forget₂ CommRingCat RingCat) h𝒪⟩).map f₂).app G₁)
        (((sheafTensor.{u₁, v, w, w, w}
            ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp J 𝒪
              (forget₂ CommRingCat RingCat) h𝒪⟩).obj F₁).map g₂))
      (((sheafTensor.{u₁, v, w, w, w}
          ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp J 𝒪
            (forget₂ CommRingCat RingCat) h𝒪⟩).map f₁).app G₁ ≫
        ((sheafTensor.{u₁, v, w, w, w}
            ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp J 𝒪
              (forget₂ CommRingCat RingCat) h𝒪⟩).obj F).map g₁)).Exact := by
  let T : SheafOfModules.{w} (TensorSheafification.structureSheaf 𝒪 h𝒪) ⥤
      SheafOfModules.{w} (TensorSheafification.structureSheaf 𝒪 h𝒪) ⥤
        SheafOfModules.{w} (TensorSheafification.structureSheaf 𝒪 h𝒪) :=
    sheafTensor.{u₁, v, w, w, w}
      ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp J 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩
  let : PreservesFiniteColimits (T.flip.obj G₁) := preservesFiniteColimits_tensorRight 𝒪 h𝒪 G₁
  let : PreservesFiniteColimits (T.flip.obj G₂) := preservesFiniteColimits_tensorRight 𝒪 h𝒪 G₂
  let : PreservesFiniteColimits (T.obj F) := preservesFiniteColimits_tensorLeft 𝒪 h𝒪 F
  let : (T.flip.obj G₁).Additive := additive_of_preservesFiniteColimits _
  let : (T.obj F).Additive := additive_of_preservesFiniteColimits _
  let leftComplex := ShortComplex.mk f₂ f₁ (hf.zero 0)
  let rightComplex := ShortComplex.mk g₂ g₁ (hg.zero 0)
  have leftExact := map_exact_of_preservesFiniteColimits (T.flip.obj G₁) leftComplex
    (hf.exact 0)
  have rightExact := map_exact_of_preservesFiniteColimits (T.obj F) rightComplex (hg.exact 0)
  have : Epi ((T.map f₁).app G₁) := Functor.map_epi (T.flip.obj G₁) f₁
  have : Epi ((T.map f₁).app G₂) := Functor.map_epi (T.flip.obj G₂) f₁
  have : Epi ((T.obj F).map g₁) := Functor.map_epi (T.obj F) g₁
  exact (exact_biprod_desc_comp ((T.map f₂).app G₁) ((T.map f₁).app G₁) ((T.map f₁).app G₂)
    ((T.obj F).map g₂) ((T.obj F₁).map g₂) ((T.obj F).map g₁)
    (leftComplex.map (T.flip.obj G₁)).zero (rightComplex.map (T.obj F)).zero
    ((T.map f₁).naturality g₂) leftExact rightExact).exact_toComposableArrows

/-- The tensor product of two epimorphisms of sheaves of modules on an arbitrary site is
an epimorphism. -/
lemma tensorSheafMapOnSite_epi
    {F₁ F G₁ G : SheafOfModules.{w} (TensorSheafification.structureSheaf 𝒪 h𝒪)}
    (f : F₁ ⟶ F) (g : G₁ ⟶ G) [leftEpi : Epi f] [rightEpi : Epi g] :
    Epi (((sheafTensor.{u₁, v, w, w, w}
        ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp J 𝒪
          (forget₂ CommRingCat RingCat) h𝒪⟩).map f).app G₁ ≫
      ((sheafTensor.{u₁, v, w, w, w}
          ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp J 𝒪
            (forget₂ CommRingCat RingCat) h𝒪⟩).obj F).map g) := by
  let := preservesFiniteColimits_tensorRight 𝒪 h𝒪 G₁
  let := preservesFiniteColimits_tensorLeft 𝒪 h𝒪 F
  exact epi_comp' (@Functor.map_epi _ _ _ _ ((sheafTensor.{u₁, v, w, w, w}
    ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp J 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).flip.obj G₁) _ _ _
    f leftEpi) (@Functor.map_epi _ _ _ _ ((sheafTensor.{u₁, v, w, w, w}
    ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp J 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj F) _ _ _
    g rightEpi)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] [HasSheafify J AddCommGrpCat] in
private lemma tensorSheafSwapOnSite_naturality
    {F F' G G' : SheafOfModules.{w} (TensorSheafification.structureSheaf 𝒪 h𝒪)}
    (f : F ⟶ F') (g : G ⟶ G') :
    (tensorSheafSwapOnSite 𝒪 h𝒪 F G).hom ≫
        (((sheafTensor.{u₁, v, w, w, w}
            ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp J 𝒪
              (forget₂ CommRingCat RingCat) h𝒪⟩).map g).app F ≫
          ((sheafTensor.{u₁, v, w, w, w}
              ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp J 𝒪
                (forget₂ CommRingCat RingCat) h𝒪⟩).obj G').map f) =
      (((sheafTensor.{u₁, v, w, w, w}
          ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp J 𝒪
            (forget₂ CommRingCat RingCat) h𝒪⟩).map f).app G ≫
        ((sheafTensor.{u₁, v, w, w, w}
            ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp J 𝒪
              (forget₂ CommRingCat RingCat) h𝒪⟩).obj F').map g) ≫
          (tensorSheafSwapOnSite 𝒪 h𝒪 F' G').hom := by
  let coefficientSheaf : Sheaf J CommRingCat.{w} :=
    ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp J 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩
  have imageNaturality := ((CommSq.mk (BraidedCategory.braiding_naturality
    (C := PresheafOfModules.{w} (𝒪 ⋙ forget₂ CommRingCat RingCat)) f.val g.val)).map
      (TensorSheafification.sheafify 𝒪 h𝒪)).w
  exact (CategoryTheory.whisker_eq (tensorSheafSwapOnSite 𝒪 h𝒪 F G).hom
    (Tensor.sheafTensor_uncurry_map.{u₁, v, w, w, w} coefficientSheaf g f)).trans
    (imageNaturality.symm.trans
      (CategoryTheory.eq_whisker
        (Tensor.sheafTensor_uncurry_map.{u₁, v, w, w, w} coefficientSheaf f g)
        (tensorSheafSwapOnSite 𝒪 h𝒪 F' G').hom).symm)

end Site

section RingedSpace

variable (X : AlgebraicGeometry.RingedSpace.{u, u})

/-- The braiding of the tensor product of two sheaves of modules on a ringed space is the
sheafification of the braiding on their underlying presheaves. -/
noncomputable def tensorSheafSwap
    (F G : SheafOfModules.{u} (Tensor.ringSheaf X.sheaf)) :
    ((sheafTensor X.sheaf).obj F).obj G ≅ ((sheafTensor X.sheaf).obj G).obj F :=
  letI : MonoidalCategory (PresheafOfModules.{u} (Tensor.ringSheaf X.sheaf).obj) :=
    PresheafOfModules.monoidalCategory (R := X.presheaf)
  letI : SymmetricCategory (PresheafOfModules.{u} (Tensor.ringSheaf X.sheaf).obj) :=
    PresheafOfModules.symmetricCategory (R := X.presheaf)
  (PresheafOfModules.sheafification (R := Tensor.ringSheaf X.sheaf)
    (𝟙 (Tensor.ringSheaf X.sheaf).obj)).mapIso (β_ F.val G.val)

/-- The sheafified braiding is natural in both factors. -/
lemma tensorSheafSwap_naturality
    {F F' G G' : SheafOfModules.{u} (Tensor.ringSheaf X.sheaf)} (f : F ⟶ F') (g : G ⟶ G') :
    (tensorSheafSwap X F G).hom ≫
        (((sheafTensor X.sheaf).map g).app F ≫ ((sheafTensor X.sheaf).obj G').map f) =
      (((sheafTensor X.sheaf).map f).app G ≫ ((sheafTensor X.sheaf).obj F').map g) ≫
        (tensorSheafSwap X F' G').hom :=
  tensorSheafSwapOnSite_naturality X.presheaf (Tensor.ringSheaf X.sheaf).property f g

/-- The relations from either factor present the tensor product on a ringed space. -/
lemma exact_tensorSheaf_presentations
    {F₂ F₁ F G₂ G₁ G : SheafOfModules.{u} (Tensor.ringSheaf X.sheaf)}
    (f₂ : F₂ ⟶ F₁) (f₁ : F₁ ⟶ F) (g₂ : G₂ ⟶ G₁) (g₁ : G₁ ⟶ G)
    (hf : (ComposableArrows.mk₂ f₂ f₁).Exact)
    (hg : (ComposableArrows.mk₂ g₂ g₁).Exact) [Epi f₁] [Epi g₁] :
    (ComposableArrows.mk₂
      (biprod.desc (((sheafTensor X.sheaf).map f₂).app G₁)
        (((sheafTensor X.sheaf).obj F₁).map g₂))
      (((sheafTensor X.sheaf).map f₁).app G₁ ≫ ((sheafTensor X.sheaf).obj F).map g₁)).Exact :=
  exact_tensorSheaf_presentations_on_site X.presheaf (Tensor.ringSheaf X.sheaf).property
    f₂ f₁ g₂ g₁ hf hg (leftEpi := ‹Epi f₁›) (rightEpi := ‹Epi g₁›)

/-- Tensoring two epimorphisms of sheaves of modules on a ringed space gives an epimorphism. -/
lemma tensorSheafMap_epi_of_epi_of_epi
    {F₁ F G₁ G : SheafOfModules.{u} (Tensor.ringSheaf X.sheaf)}
    (f : F₁ ⟶ F) (g : G₁ ⟶ G) [Epi f] [Epi g] :
    Epi (((sheafTensor X.sheaf).map f).app G₁ ≫ ((sheafTensor X.sheaf).obj F).map g) :=
  tensorSheafMapOnSite_epi X.presheaf (Tensor.ringSheaf X.sheaf).property f g
    (leftEpi := ‹Epi f›) (rightEpi := ‹Epi g›)

end RingedSpace

end Stacks.SheafOfModules.TensorPresentations

end
