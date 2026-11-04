module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CurryingIsomorphism
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CurryingNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.IntoAKInjectiveComplexGlobalValue

/-!
# Uncurrying a morphism of complexes into an internal Hom complex

Let `(C, O)` be a ringed site and `A`, `B`, `M` complexes of `O`-modules. A morphism of complexes
`f : A ⟶ SheafHom(B, M)` is a degree-zero cocycle among the global sections of
`SheafHom(A, SheafHom(B, M))`; the currying isomorphism of Stacks 0A90 carries it to a
degree-zero cocycle among the global sections of `SheafHom(Tot(A ⊗_O B), M)`, that is to a
morphism of complexes `Tot(A ⊗_O B) ⟶ M`, the *uncurrying* of `f`. On a local pure tensor it is
`k ⊗ l ↦ f(k)(l)`.

## Main definitions

* `AlgebraicGeometry.RingedSite.homOfGlobalCocycle`: the morphism of complexes given by a
  degree-zero global cocycle of an internal Hom complex.
* `AlgebraicGeometry.RingedSite.uncurryMap`: the uncurrying of `f : A ⟶ SheafHom(B, M)`.

## Main results

* `AlgebraicGeometry.RingedSite.homologyMap_globalHomologyClass_uncurryMap`: the currying
  isomorphism on global cohomology carries the class of `f` to the class of its uncurrying.
* `AlgebraicGeometry.RingedSite.uncurryMap_f_tensorComplexSection`: the value of the uncurrying
  on a local pure tensor.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CochainComplex.HomComplex

universe u

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

section General

variable {L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The cochain attached to a degree-zero global cocycle of `SheafHom(L, M)` is a cocycle. -/
lemma globalSectionsIso_mem_cocycle (s : (globalSectionsComplex X (sheafHomComplex X L M).obj).X 0)
    (hs : (globalSectionsComplex X (sheafHomComplex X L M).obj).d 0 1 s = 0) :
    (((sheafHomComplex X L M).globalSectionsIso.hom.f 0 s).down : Cochain L M 0) ∈
      cocycle L M 0 := by
  refine (Cocycle.mem_iff 0 1 (zero_add 1) _).2 ?_
  have hcomm := ConcreteCategory.congr_hom
    ((sheafHomComplex X L M).globalSectionsIso.hom.comm 0 1) s
  simp only [ConcreteCategory.comp_apply, hs, map_zero] at hcomm
  exact congrArg ULift.down hcomm

/-- The morphism of complexes `L ⟶ M` given by a degree-zero global cocycle of
`SheafHom(L, M)`. -/
def homOfGlobalCocycle (s : (globalSectionsComplex X (sheafHomComplex X L M).obj).X 0)
    (hs : (globalSectionsComplex X (sheafHomComplex X L M).obj).d 0 1 s = 0) : L ⟶ M :=
  Cocycle.homOf ⟨((sheafHomComplex X L M).globalSectionsIso.hom.f 0 s).down,
    globalSectionsIso_mem_cocycle X s hs⟩

/-- The cochain of the morphism given by a global cocycle is the cochain attached to it. -/
private lemma cochain_ofHom_homOfGlobalCocycle {Y : RingedSite.{u, u, u}}
    {L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ}
    (s : (globalSectionsComplex Y (sheafHomComplex Y L M).obj).X 0)
    (hs : (globalSectionsComplex Y (sheafHomComplex Y L M).obj).d 0 1 s = 0) :
    Cochain.ofHom (homOfGlobalCocycle Y s hs) =
      ((sheafHomComplex Y L M).globalSectionsIso.hom.f 0 s).down :=
  Cocycle.cochain_ofHom_homOf_eq_coe
    (⟨((sheafHomComplex Y L M).globalSectionsIso.hom.f 0 s).down,
      globalSectionsIso_mem_cocycle Y s hs⟩ : Cocycle L M 0)

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The global section of a morphism of complexes given by a global cocycle is that cocycle. -/
lemma globalHomSection_homOfGlobalCocycle
    (s : (globalSectionsComplex X (sheafHomComplex X L M).obj).X 0)
    (hs : (globalSectionsComplex X (sheafHomComplex X L M).obj).d 0 1 s = 0) :
    globalHomSection X L M (homOfGlobalCocycle X s hs) = s := by
  have h := cochain_ofHom_homOfGlobalCocycle s hs
  refine (congrArg (fun w : Cochain L M 0 =>
    (sheafHomComplex X L M).globalSectionsIso.inv.f 0 (ULift.up w)) h).trans ?_
  exact ConcreteCategory.congr_hom
    (congrArg (fun ψ => HomologicalComplex.Hom.f ψ 0)
      (sheafHomComplex X L M).globalSectionsIso.hom_inv_id) s

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The components of the morphism given by a global cocycle are read off its sections. -/
lemma homOfGlobalCocycle_f_apply
    (s : (globalSectionsComplex X (sheafHomComplex X L M).obj).X 0)
    (hs : (globalSectionsComplex X (sheafHomComplex X L M).obj).d 0 1 s = 0)
    (c : ℤ) (W : X.C) (x : (L.X c).val.obj (op W)) :
    ((homOfGlobalCocycle X s hs).f c).val.app (op W) x =
      applyHomSection X (sheafHomComplex X L M) W 0 c c (add_zero c) (s.val (op W)) x := by
  have h1 : (homOfGlobalCocycle X s hs).f c =
      ((sheafHomComplex X L M).globalSectionsIso.hom.f 0 s).down.v c c (add_zero c) := by
    rw [← Cochain.ofHom_v (homOfGlobalCocycle X s hs) c]
    exact congrArg (fun w : Cochain L M 0 => w.v c c (add_zero c))
      (cochain_ofHom_homOfGlobalCocycle s hs)
  rw [h1]
  exact sheafHomComplex_globalSectionsIso_v_app X L M 0 c c (add_zero c) s W x

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The section of the global section of a morphism of complexes, evaluated on a local section,
is the value of the morphism. -/
lemma applyHomSection_globalHomSection (f : L ⟶ M) (c : ℤ) (W : X.C)
    (x : (L.X c).val.obj (op W)) :
    applyHomSection X (sheafHomComplex X L M) W 0 c c (add_zero c)
        ((globalHomSection X L M f).val (op W)) x = (f.f c).val.app (op W) x := by
  have h := sheafHomComplex_globalSectionsIso_v_app X L M 0 c c (add_zero c)
    (globalHomSection X L M f) W x
  rw [globalHomSection_v] at h
  exact h.symm

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- If a morphism of internal Hom complexes carries the global section of `f` to that of `g` on
global sections, it carries the cohomology class of `f` to that of `g`. -/
lemma homologyMap_globalHomologyClass
    {L' M' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (φ : (sheafHomComplex X L M).obj ⟶ (sheafHomComplex X L' M').obj) (f : L ⟶ M) (g : L' ⟶ M')
    (h : (globalSectionsComplexMap X φ).f 0 (globalHomSection X L M f) =
      globalHomSection X L' M' g) :
    HomologicalComplex.homologyMap (globalSectionsComplexMap X φ) 0
        (globalHomologyClass X L M f) = globalHomologyClass X L' M' g := by
  dsimp only [globalHomologyClass]
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.homologyπ_naturality,
    ConcreteCategory.comp_apply]
  congr 1
  apply (AddCommGrpCat.mono_iff_injective
    ((globalSectionsComplex X (sheafHomComplex X L' M').obj).iCycles 0)).1 inferInstance
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i, ConcreteCategory.comp_apply,
    iCycles_globalHomCocycle, iCycles_globalHomCocycle, h]

/-- Evaluating the value of a morphism into an internal Hom complex along an arrow is
evaluating its value on the restricted section. -/
lemma applyHomSectionOver_map_apply {Y : RingedSite.{u, u, u}}
    {K L N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ}
    (φ : N ⟶ (sheafHomComplex Y K L).obj) (V W : Y.C) (i : W ⟶ V) (t r d : ℤ) (hrd : r + t = d)
    (k : (N.X t).val.obj (op V)) (l : (K.X r).val.obj (op W)) :
    applyHomSectionOver Y (sheafHomComplex Y K L) V W i t r d hrd ((φ.f t).val.app (op V) k) l =
      applyHomSection Y (sheafHomComplex Y K L) W t r d hrd
        ((φ.f t).val.app (op W) ((N.X t).val.map i.op k)) l := by
  rw [applyHomSectionOver_restrict, ← PresheafOfModules.naturality_apply]

/-- A morphism of internal Hom complexes carries the global section of a morphism of complexes to
a degree-zero cocycle. -/
private lemma d_globalSectionsComplexMap_globalHomSection {Y : RingedSite.{u, u, u}}
    {K L K' L' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ}
    (φ : (sheafHomComplex Y K L).obj ⟶ (sheafHomComplex Y K' L').obj) (f : K ⟶ L) :
    (globalSectionsComplex Y (sheafHomComplex Y K' L').obj).d 0 1
      ((globalSectionsComplexMap Y φ).f 0 (globalHomSection Y K L f)) = 0 := by
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.Hom.comm, ConcreteCategory.comp_apply]
  have h := d_globalHomSection Y K L f
  rw [show (ComplexShape.up ℤ).next 0 = 1 by simp] at h
  rw [h, map_zero]

end General

variable [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

variable
  {A B M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

/-- The image under the currying isomorphism of the global section of `f`. -/
abbrev uncurryGlobalSection (f : A ⟶ (sheafHomComplex X B M).obj) :
    (globalSectionsComplex X (sheafHomComplex X
      (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj B) M).obj).X 0 :=
  (globalSectionsComplexMap X (sheafHomTensorCurryIso X A B M).hom).f 0
    (globalHomSection X A (sheafHomComplex X B M).obj f)

/-- The global section `uncurryGlobalSection X f` is a degree-zero cocycle. -/
lemma d_uncurryGlobalSection (f : A ⟶ (sheafHomComplex X B M).obj) :
    (globalSectionsComplex X (sheafHomComplex X
      (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj B) M).obj).d 0 1
        (uncurryGlobalSection X f) = 0 := by
  exact d_globalSectionsComplexMap_globalHomSection _ f

/-- **The uncurrying** `Tot(A ⊗_O B) ⟶ M` of a morphism of complexes `f : A ⟶ SheafHom(B, M)`:
the morphism of complexes whose global section is the image of that of `f` under the currying
isomorphism of Stacks 0A90. -/
def uncurryMap (f : A ⟶ (sheafHomComplex X B M).obj) :
    ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj B ⟶ M :=
  homOfGlobalCocycle X (uncurryGlobalSection X f) (d_uncurryGlobalSection X f)

/-- The currying isomorphism on degree-zero global cohomology carries the class of `f` to the
class of its uncurrying. -/
theorem homologyMap_globalHomologyClass_uncurryMap (f : A ⟶ (sheafHomComplex X B M).obj) :
    HomologicalComplex.homologyMap
        (globalSectionsComplexMap X (sheafHomTensorCurryIso X A B M).hom) 0
          (globalHomologyClass X A (sheafHomComplex X B M).obj f) =
      globalHomologyClass X _ M (uncurryMap X f) :=
  homologyMap_globalHomologyClass X _ f _
    (globalHomSection_homOfGlobalCocycle X _ (d_uncurryGlobalSection X f)).symm

/-- **The uncurrying on a local pure tensor**: `k ⊗ l ↦ f(k)(l)`. -/
theorem uncurryMap_f_tensorComplexSection (f : A ⟶ (sheafHomComplex X B M).obj)
    (t r c : ℤ) (htr : t + r = c) (W : X.C) (k : (A.X t).val.obj (op W))
    (l : (B.X r).val.obj (op W)) :
    ((uncurryMap X f).f c).val.app (op W) (tensorComplexSection X t r c htr k l) =
      curryRule X W A B M 0 ((globalHomSection X A (sheafHomComplex X B M).obj f).val (op W))
        t r c (by omega) (𝟙 W) k l := by
  rw [uncurryMap, homOfGlobalCocycle_f_apply]
  exact applyHomSectionOver_curryFun X W
    ((globalHomSection X A (sheafHomComplex X B M).obj f).val (op W)) c c (add_zero c) t r htr
    (𝟙 W) k l

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O))
        (ComplexShape.up ℤ)),
      HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
        (ComplexShape.up ℤ)] in
/-- A morphism of complexes is determined by its global section. -/
lemma globalHomSection_injective : Function.Injective (globalHomSection X A M) := by
  intro f f' h
  have h1 := congrArg (fun s => ((sheafHomComplex X A M).globalSectionsIso.hom.f 0 s).down) h
  simp only [globalSectionsIso_globalHomSection] at h1
  exact (Cocycle.equivHom A M).injective (Cocycle.ext h1)

/-- The image under the inverse of the currying isomorphism of the global section of `g`. -/
abbrev curryGlobalSection (g : ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj B ⟶ M) :
    (globalSectionsComplex X (sheafHomComplex X A (sheafHomComplex X B M).obj).obj).X 0 :=
  (globalSectionsComplexMap X (sheafHomTensorCurryIso X A B M).inv).f 0
    (globalHomSection X _ M g)

/-- The global section `curryGlobalSection X g` is a degree-zero cocycle. -/
lemma d_curryGlobalSection
    (g : ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj B ⟶ M) :
    (globalSectionsComplex X (sheafHomComplex X A (sheafHomComplex X B M).obj).obj).d 0 1
        (curryGlobalSection X g) = 0 := by
  exact d_globalSectionsComplexMap_globalHomSection _ g

/-- **The currying** `A ⟶ SheafHom(B, M)` of a morphism of complexes `g : Tot(A ⊗_O B) ⟶ M`,
inverse to `uncurryMap`. -/
def curryMap (g : ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj B ⟶ M) :
    A ⟶ (sheafHomComplex X B M).obj :=
  homOfGlobalCocycle X (curryGlobalSection X g) (d_curryGlobalSection X g)

/-- Uncurrying the currying of `g` gives back `g`. -/
theorem uncurryMap_curryMap
    (g : ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj B ⟶ M) :
    uncurryMap X (curryMap X g) = g := by
  apply globalHomSection_injective X
  rw [uncurryMap, globalHomSection_homOfGlobalCocycle]
  dsimp only [uncurryGlobalSection, curryMap]
  rw [globalHomSection_homOfGlobalCocycle]
  dsimp only [curryGlobalSection]
  rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f, ← Functor.map_comp,
    ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id, HomologicalComplex.id_f, ConcreteCategory.id_apply]

/-- **The currying on local sections**: `(curryMap g)(k)(l) = g(k ⊗ l)`. -/
theorem curryMap_apply (g : ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj B ⟶ M)
    (t r d : ℤ) (hrd : r + t = d) (W : X.C) (k : (A.X t).val.obj (op W))
    (l : (B.X r).val.obj (op W)) :
    applyHomSection X (sheafHomComplex X B M) W t r d hrd
        (((curryMap X g).f t).val.app (op W) k) l =
      (g.f d).val.app (op W) (tensorComplexSection X t r d (by omega) k l) := by
  obtain rfl : d = t + r := by omega
  rw [curryMap, homOfGlobalCocycle_f_apply]
  have h1 : (curryGlobalSection X g).val (op W) =
      uncurryFun X W ((globalHomSection X _ M g).val (op W)) := rfl
  rw [h1]
  refine (applyHomSectionOver_applyHomSectionOver_uncurryFun X W
    ((globalHomSection X _ M g).val (op W)) t t (add_zero t) r (t + r) (by omega) (𝟙 W) (𝟙 W)
    k l).trans ?_
  rw [Category.id_comp, restrictSection_id]
  exact applyHomSection_globalHomSection X g (t + r) W (tensorComplexSection X t r (t + r) rfl k l)

/-- **Currying is natural in the first variable**: the currying of `Tot(a ⊗ B) ≫ g` is `a`
followed by the currying of `g`. -/
theorem curryMap_comp_left
    {A' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (a : A' ⟶ A)
    (g : ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj B ⟶ M) :
    curryMap X (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map a).app B ≫ g) =
      a ≫ curryMap X g := by
  ext t V : 3
  refine ModuleCat.hom_ext (LinearMap.ext fun k => ?_)
  refine homSection_ext X (sheafHomComplex X B M) V.unop t fun r d hrd W i l => ?_
  refine Eq.trans (applyHomSectionOver_map_apply (Y := X) _ V.unop W i t r d hrd k l) ?_
  refine Eq.trans ?_ (applyHomSectionOver_map_apply (Y := X) _ V.unop W i t r d hrd k l).symm
  refine (curryMap_apply X _ t r d hrd W _ l).trans ?_
  simp only [HomologicalComplex.comp_f, SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ConcreteCategory.comp_apply]
  refine Eq.trans ?_ (curryMap_apply X g t r d hrd W _ l).symm
  have h := tensorComplexMap_tensorComplexSection X a (𝟙 B) t r d (by omega) (W := W)
    (((A'.X t).val.map i.op).hom k) l
  simp only [CategoryTheory.Functor.map_id, Category.comp_id, HomologicalComplex.id_f,
    SheafOfModules.id_val, PresheafOfModules.id_app, ConcreteCategory.id_apply] at h
  rw [h]
  rfl

end AlgebraicGeometry.RingedSite

end
