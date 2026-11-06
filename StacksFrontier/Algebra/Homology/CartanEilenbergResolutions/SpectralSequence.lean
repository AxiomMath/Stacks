module

import Mathlib.CategoryTheory.Abelian.Injective.Extend
import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import StacksFrontier.Algebra.Homology.MapTotalComplex
public import StacksFrontier.Algebra.Homology.TotalComplexFiniteSupport
public import StacksFrontier.Algebra.Homology.TotalComplexQuasiIso
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.Algebra.Homology.CartanEilenbergResolutions.Construction
import all StacksFrontier.Algebra.Homology.CartanEilenbergResolutions.Basic
import all StacksFrontier.Algebra.Homology.CartanEilenbergResolutions.Construction

/-!
# Cartan-Eilenberg resolutions: existence and the two spectral sequences

Let `F : 𝒜 ⥤ ℬ` be an additive functor of abelian categories with `𝒜` having enough
injectives, so that `RF : D⁺(𝒜) ⥤ D⁺(ℬ)` is everywhere defined and `R^i F = H^i ∘ RF`
([Stacks, Tag 015A]), let `I` be a Cartan-Eilenberg resolution of a bounded below complex `K`,
and write `L = F(I)`. This file identifies the pages of the two spectral sequences of `L`
([Stacks, Tag 0130]):
```
'E₁^{p,q} = R^qF(K^p)    and    ''E₂^{p,q} = R^pF(H^q(K^•)),
```
the differential `'d₁^{p,q}` being the map `R^qF(K^p) → R^qF(K^{p+1})` that the functor `R^qF`
produces from `d_K^p`, and shows that `Tot(L) = F(Tot(I))` computes `RF(K^•)`, because `Tot(I)`
is an injective resolution of `K^•` ([Stacks, Tag 0133]). It also states the existence of
Cartan-Eilenberg resolutions, built in
`StacksFrontier.Algebra.Homology.CartanEilenbergResolutions.Construction`.

## Main results

* `CochainComplex.exists_cartanEilenbergResolution`: a cochain complex which is strictly `≥ n`
  over an abelian category with enough injectives has a Cartan-Eilenberg resolution whose
  double complex is again strictly `≥ n` in the first direction.
* `CochainComplex.CartanEilenbergResolution.exists_homologyIso_rightDerivedPlus`: the
  `'E₁`-page of `F(I)` is the complex `R^qF(K^•)`, the `''E₂`-page of `F(I)` is
  `R^pF(H^q(K^•))`, and the cohomology of the total complex of `F(I)` is `H^n(RF(K^•))`.

## Implementation notes

See the module documentation of `StacksFrontier.Algebra.Homology.CartanEilenbergResolutions` for
the conventions on double complexes and on the pages, and for why `F` is only assumed additive.

## References

* [Stacks, Tag 015I]
* [Stacks, Tag 015J]
* [Stacks, Tag 0133]
-/

@[expose] public section

open CategoryTheory Limits HomologicalComplex StacksDraft.TotalComplexQuasiIso

namespace StacksDraft.CartanEilenbergResolutions

universe w w' v v' u u' v'' u''

section

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [Limits.HasZeroMorphisms C] [Limits.HasZeroMorphisms D]
  [CategoryWithHomology C] [CategoryWithHomology D]

/-- A functor which preserves homology commutes with the homology of a homological complex:
`H_i(G(K)) ≅ G(H_i(K))`. -/
private noncomputable def mapHomologicalComplexHomologyIso (G : C ⥤ D)
    [G.PreservesZeroMorphisms] {ι : Type*} (c : ComplexShape ι)
    (K : HomologicalComplex C c) (i : ι) [G.PreservesLeftHomologyOf (K.sc i)] :
    ((G.mapHomologicalComplex c).obj K).homology i ≅ G.obj (K.homology i) :=
  ShortComplex.mapHomologyIso (S := K.sc i) G

end

section

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D] [Abelian C] [Abelian D]

/-- If `G` preserves in each degree the limit of a diagram of homological complexes, then
`G.mapHomologicalComplex` preserves that limit: limits of complexes are computed degreewise. -/
private lemma preservesLimit_mapHomologicalComplex {ι : Type} (c : ComplexShape ι) {J : Type}
    [SmallCategory J] [HasLimitsOfShape J C]
    (E : J ⥤ HomologicalComplex C c) (G : C ⥤ D) [G.Additive]
    (h : ∀ i, PreservesLimit (E ⋙ HomologicalComplex.eval C c i) G) :
    PreservesLimit E (G.mapHomologicalComplex c) := by
  constructor
  intro s hs
  refine ⟨HomologicalComplex.isLimitOfEval _ _ (fun i => ?_)⟩
  have := h i
  have : PreservesLimit E (HomologicalComplex.eval C c i ⋙ G) := comp_preservesLimit _ _
  exact isLimitOfPreserves (HomologicalComplex.eval C c i ⋙ G) hs

/-- If `G` preserves in each degree the colimit of a diagram of homological complexes, then
`G.mapHomologicalComplex` preserves that colimit. -/
private lemma preservesColimit_mapHomologicalComplex {ι : Type} (c : ComplexShape ι) {J : Type}
    [SmallCategory J] [HasColimitsOfShape J C]
    (E : J ⥤ HomologicalComplex C c) (G : C ⥤ D) [G.Additive]
    (h : ∀ i, PreservesColimit (E ⋙ HomologicalComplex.eval C c i) G) :
    PreservesColimit E (G.mapHomologicalComplex c) := by
  constructor
  intro s hs
  refine ⟨HomologicalComplex.isColimitOfEval _ _ (fun i => ?_)⟩
  have := h i
  have : PreservesColimit E (HomologicalComplex.eval C c i ⋙ G) := comp_preservesColimit _ _
  exact isColimitOfPreserves (HomologicalComplex.eval C c i ⋙ G) hs

/-- `G.mapHomologicalComplex` preserves the kernel of a morphism of complexes as soon as `G`
preserves the kernel of each of its components. -/
private lemma preservesLimit_parallelPair_mapHomologicalComplex {ι : Type} (c : ComplexShape ι)
    {X Y : HomologicalComplex C c} (f : X ⟶ Y) (G : C ⥤ D) [G.Additive]
    (h : ∀ i, PreservesLimit (parallelPair (f.f i) 0) G) :
    PreservesLimit (parallelPair f 0) (G.mapHomologicalComplex c) := by
  refine preservesLimit_mapHomologicalComplex c _ G (fun i => ?_)
  have := h i
  exact preservesLimit_of_iso_diagram (K₁ := parallelPair (f.f i) 0) G
    (diagramIsoParallelPair (parallelPair f 0 ⋙ HomologicalComplex.eval C c i)).symm

/-- `G.mapHomologicalComplex` preserves the cokernel of a morphism of complexes as soon as `G`
preserves the cokernel of each of its components. -/
private lemma preservesColimit_parallelPair_mapHomologicalComplex {ι : Type} (c : ComplexShape ι)
    {X Y : HomologicalComplex C c} (f : X ⟶ Y) (G : C ⥤ D) [G.Additive]
    (h : ∀ i, PreservesColimit (parallelPair (f.f i) 0) G) :
    PreservesColimit (parallelPair f 0) (G.mapHomologicalComplex c) := by
  refine preservesColimit_mapHomologicalComplex c _ G (fun i => ?_)
  have := h i
  exact preservesColimit_of_iso_diagram (K₁ := parallelPair (f.f i) 0) G
    (diagramIsoParallelPair (parallelPair f 0 ⋙ HomologicalComplex.eval C c i)).symm

/-- **A split kernel is preserved by every additive functor.** If the short complex `S` is
split and `g = S.g ≫ m` for a split monomorphism `m`, then `S.f` is a kernel of `g` which any
additive functor `G` preserves. This is the formal content of "a differential which is a split
surjection onto a direct summand stays one after applying `G`". -/
private lemma preservesLimit_parallelPair_of_splitting {S : ShortComplex C} (sp : S.Splitting)
    {Y : C} (m : S.X₃ ⟶ Y) [IsSplitMono m] {g : S.X₂ ⟶ Y} (hg : g = S.g ≫ m) (G : C ⥤ D)
    [G.Additive] : PreservesLimit (parallelPair g 0) G := by
  have hGm : IsSplitMono (G.map m) :=
    ⟨⟨⟨G.map (retraction m), by rw [← G.map_comp, IsSplitMono.id, G.map_id]⟩⟩⟩
  refine preservesLimit_of_preserves_limit_cone (isKernelCompMono sp.fIsKernel m hg)
    ((KernelFork.isLimitMapConeEquiv _ G).symm ?_)
  exact isKernelCompMono (sp.map G).fIsKernel (G.map m) (by rw [hg, G.map_comp, ShortComplex.map_g])

/-- **A split cokernel is preserved by every additive functor**, the dual of
`preservesLimit_parallelPair_of_splitting`. -/
private lemma preservesColimit_parallelPair_of_splitting {S : ShortComplex C} (sp : S.Splitting)
    {W : C} (e : W ⟶ S.X₁) [IsSplitEpi e] {f : W ⟶ S.X₂} (hf : f = e ≫ S.f) (G : C ⥤ D)
    [G.Additive] : PreservesColimit (parallelPair f 0) G := by
  have hGe : IsSplitEpi (G.map e) :=
    ⟨⟨⟨G.map (section_ e), by rw [← G.map_comp, IsSplitEpi.id, G.map_id]⟩⟩⟩
  refine preservesColimit_of_preserves_colimit_cocone (isCokernelEpiComp sp.gIsCokernel e hf)
    ((CokernelCofork.isColimitMapCoconeEquiv _ G).symm ?_)
  exact isCokernelEpiComp (sp.map G).gIsCokernel (G.map e)
    (by rw [hf, G.map_comp, ShortComplex.map_f])

/-- The short complex `X ⟶ Y ⟶ cokernel k` attached to a morphism `k : X ⟶ Y`. -/
private noncomputable abbrev cokernelShortComplex {X Y : C} (k : X ⟶ Y) : ShortComplex C :=
  ShortComplex.mk k (cokernel.π k) (cokernel.condition k)

omit [Abelian D] in
/-- A monomorphism, together with its cokernel, is a short exact sequence. -/
private lemma shortExact_cokernelShortComplex {X Y : C} (k : X ⟶ Y) [Mono k] :
    (cokernelShortComplex k).ShortExact where
  mono_f := inferInstance
  epi_g := inferInstance
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel k)

omit [Abelian D] in
/-- **A monomorphism with injective source splits off**: the short complex
`X ⟶ Y ⟶ cokernel k` is split as soon as `X` is injective. -/
private noncomputable def splittingCokernelShortComplex {X Y : C} (k : X ⟶ Y) [Mono k]
    [Injective X] : (cokernelShortComplex k).Splitting :=
  (shortExact_cokernelShortComplex k).splittingOfInjective

omit [Abelian D] in
/-- A quotient of an injective object by an injective subobject is injective. -/
private lemma injective_cokernel {X Y : C} (k : X ⟶ Y) [Mono k] [Injective X] [Injective Y] :
    Injective (cokernel k) :=
  Retract.injective
    { i := (splittingCokernelShortComplex k).s
      r := cokernel.π k
      retract := (splittingCokernelShortComplex k).s_g }

omit [Abelian C] [Abelian D] in
/-- A monomorphism with injective source is split. -/
private lemma isSplitMono_of_injective {X Y : C} (m : X ⟶ Y) [Mono m] [Injective X] :
    IsSplitMono m :=
  ⟨⟨⟨Injective.factorThru (𝟙 X) m, Injective.comp_factorThru _ _⟩⟩⟩

/-- If `k` is a kernel of `f`, then the induced map `cokernel k ⟶ Z` is a monomorphism. -/
private lemma mono_cokernelDesc_of_isKernel {X Y Z : C} {k : X ⟶ Y} {f : Y ⟶ Z}
    (w : k ≫ f = 0) (hk : IsLimit (KernelFork.ofι k w)) : Mono (cokernel.desc k f w) :=
  (ShortComplex.exact_of_f_is_kernel (ShortComplex.mk k f w) hk).mono_cokernelDesc

/-- **A kernel between injective objects is preserved by every additive functor.** If
`k : X ⟶ Y` is a kernel of `f : Y ⟶ Z` and both `X` and `Y` are injective, then `f` is the
composition of the split epimorphism `Y ⟶ cokernel k` with a split monomorphism, so any
additive functor preserves the kernel of `f`. -/
private lemma preservesLimit_parallelPair_of_isKernel {X Y Z : C} {k : X ⟶ Y} {f : Y ⟶ Z}
    (w : k ≫ f = 0) (hk : IsLimit (KernelFork.ofι k w)) [Injective X] [Injective Y]
    (G : C ⥤ D) [G.Additive] : PreservesLimit (parallelPair f 0) G := by
  have : Mono k := mono_of_isLimit_fork hk
  have := mono_cokernelDesc_of_isKernel w hk
  have := injective_cokernel k
  have := isSplitMono_of_injective (cokernel.desc k f w)
  exact preservesLimit_parallelPair_of_splitting (splittingCokernelShortComplex k)
    (cokernel.desc k f w) (by simp) G

/-- **A cokernel out of an injective object with injective kernel is preserved by every additive
functor**: with `k : X ⟶ Y` a kernel of `f : Y ⟶ Z` and `X`, `Y` injective, the morphism `f`
is the composition of the split epimorphism `Y ⟶ cokernel k` with a monomorphism which splits
off `cokernel k`. -/
private lemma preservesColimit_parallelPair_of_isKernel {X Y Z : C} {k : X ⟶ Y} {f : Y ⟶ Z}
    (w : k ≫ f = 0) (hk : IsLimit (KernelFork.ofι k w)) [Injective X] [Injective Y]
    (G : C ⥤ D) [G.Additive] : PreservesColimit (parallelPair f 0) G := by
  have : Mono k := mono_of_isLimit_fork hk
  have := mono_cokernelDesc_of_isKernel w hk
  have := injective_cokernel k
  have := (splittingCokernelShortComplex k).isSplitEpi_g
  exact preservesColimit_parallelPair_of_splitting
    (splittingCokernelShortComplex (cokernel.desc k f w)) (cokernel.π k) (by simp) G

/-- **An additive functor preserves the left homology of a short complex whose terms `X₁`, `X₂`,
cycles and the kernel of `f` are all injective.** This is the source's splitting step: both the
kernel of `g` and the cokernel of `X₁ ⟶ Ker(g)` are then split, and a split (co)kernel survives
any additive functor. -/
private lemma preservesLeftHomologyOf_of_injective {S : ShortComplex C} {X : C} {k : X ⟶ S.X₁}
    (w : k ≫ S.f = 0) (hk : IsLimit (KernelFork.ofι k w))
    [Injective X] [Injective S.X₁] [Injective S.X₂] [Injective S.cycles]
    (G : C ⥤ D) [G.Additive] : G.PreservesLeftHomologyOf S := by
  have w' : k ≫ S.toCycles = 0 := by
    rw [← cancel_mono S.iCycles, Category.assoc, S.toCycles_i, w, zero_comp]
  have hk' : IsLimit (KernelFork.ofι k w') := isKernelOfComp S.iCycles S.f hk w' S.toCycles_i
  have : S.leftHomologyData.IsPreservedBy G :=
    { g := preservesLimit_parallelPair_of_isKernel S.iCycles_g S.cyclesIsKernel G
      f' := preservesColimit_parallelPair_of_isKernel w' hk' G }
  exact Functor.PreservesLeftHomologyOf.mk' G S.leftHomologyData

end

section

variable (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- The functor `C ⥤ CochainComplex.Plus C` sending an object to the complex concentrated in
degree `n`. -/
private noncomputable def singleFunctorPlus (n : ℤ) : C ⥤ CochainComplex.Plus C :=
  ObjectProperty.lift _ (HomologicalComplex.single C (ComplexShape.up ℤ) n)
    (fun _ => ⟨n, inferInstance⟩)

/-- Passing from bounded below cochain complexes to `D⁺(C)` through the bounded below
homotopy category agrees with `DerivedCategory.Plus.Q`. -/
private noncomputable def quotientCompQhIso :
    HomotopyCategory.Plus.quotient C ⋙ DerivedCategory.Plus.Qh ≅ DerivedCategory.Plus.Q :=
  (Functor.FullyFaithful.whiskeringRight
      (Functor.FullyFaithful.ofFullyFaithful (DerivedCategory.Plus.ι (C := C)))
      (CochainComplex.Plus C)).preimageIso
      (Functor.isoWhiskerLeft (CochainComplex.Plus.ι C) (DerivedCategory.quotientCompQhIso C))

/-- The homology in degree `n` of the image in `D⁺(C)` of a bounded below cochain complex is
the homology of the complex, naturally. -/
private noncomputable def homologyPlusQIso (n : ℤ) :
    DerivedCategory.Plus.Q ⋙ DerivedCategory.Plus.homologyFunctor C n ≅
      CochainComplex.Plus.ι C ⋙ HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n :=
  Functor.isoWhiskerLeft (CochainComplex.Plus.ι C) (DerivedCategory.homologyFunctorFactors C n)

variable {C}

/-- The functor `CochainComplex.Plus C ⥤ D⁺(C)` inverts quasi-isomorphisms. -/
private lemma isIso_Q_map {X J : CochainComplex.Plus C} (f : X ⟶ J) [QuasiIso f.hom] :
    IsIso (DerivedCategory.Plus.Q.map f) := by
  have : IsIso (DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Q.map f)) := by
    have : IsIso (DerivedCategory.Q.map f.hom) := by
      rw [DerivedCategory.isIso_Q_map_iff_quasiIso]; infer_instance
    exact this
  exact isIso_of_fully_faithful DerivedCategory.Plus.ι _

end

section

variable {A : Type u} {B : Type u'} [Category.{v} A] [Category.{v'} B] [Abelian A] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B] (F : A ⥤ B) [F.Additive]
  [EnoughInjectives A]

/-- `J ↦ H^q(RF(J))`, the target of `derivedHomologyUnit`. -/
private noncomputable abbrev derivedHomology (q : ℤ) : CochainComplex.Plus A ⥤ B :=
  DerivedCategory.Plus.Q ⋙ F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor B q

/-- `J ↦ H^q(F(J))`, the source of `derivedHomologyUnit`. -/
private noncomputable abbrev mapHomology (q : ℤ) : CochainComplex.Plus A ⥤ B :=
  F.mapCochainComplexPlus ⋙ CochainComplex.Plus.ι B ⋙
    HomologicalComplex.homologyFunctor B (ComplexShape.up ℤ) q

/-- The canonical map `H^q(F(J)) ⟶ H^q(RF(J))`, natural in the bounded below complex `J`.
It is an isomorphism when the terms of `J` are injective. -/
private noncomputable def derivedHomologyUnit (q : ℤ) :
    mapHomology F q ⟶ derivedHomology F q :=
  Functor.whiskerLeft F.mapCochainComplexPlus (homologyPlusQIso B q).inv ≫
    Functor.whiskerLeft F.mapCochainComplexPlus
      (Functor.whiskerRight (quotientCompQhIso B).inv
        (DerivedCategory.Plus.homologyFunctor B q)) ≫
    Functor.whiskerRight (Functor.whiskerLeft (HomotopyCategory.Plus.quotient A)
      F.rightDerivedFunctorPlusUnith) (DerivedCategory.Plus.homologyFunctor B q) ≫
    Functor.whiskerRight (quotientCompQhIso A).hom
      (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor B q)

/-- The unit of the right derived functor is an isomorphism at a bounded below complex of
injective objects. -/
private lemma isIso_rightDerivedFunctorPlusUnit_app (J : CochainComplex.Plus A)
    (hJ : ∀ n, Injective (J.obj.X n)) :
    IsIso (F.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient A).obj J)) := by
  obtain ⟨J, n, hn⟩ := J
  have : ∀ n, Injective (J.X n) := hJ
  let L : CochainComplex (InjectiveObject A) ℤ :=
    HomologicalComplex.liftObjectProperty _ J inferInstance
  have hL : L.IsStrictlyGE n := by
    rwa [← CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff _ (InjectiveObject.ι A)]
  exact inferInstanceAs (IsIso (F.rightDerivedFunctorPlusUnith.app
    ((HomotopyCategory.Plus.quotient A).obj
      ((InjectiveObject.ι A).mapCochainComplexPlus.obj ⟨L, n, hL⟩))))

/-- The components of `derivedHomologyUnit`. -/
private lemma derivedHomologyUnit_app (q : ℤ) (J : CochainComplex.Plus A) :
    (derivedHomologyUnit F q).app J =
      (homologyPlusQIso B q).inv.app (F.mapCochainComplexPlus.obj J) ≫
      (DerivedCategory.Plus.homologyFunctor B q).map
        ((quotientCompQhIso B).inv.app (F.mapCochainComplexPlus.obj J)) ≫
      (DerivedCategory.Plus.homologyFunctor B q).map
        (F.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient A).obj J)) ≫
      (DerivedCategory.Plus.homologyFunctor B q).map
        (F.rightDerivedFunctorPlus.map ((quotientCompQhIso A).hom.app J)) := rfl

/-- `H^q(F(J)) ≅ H^q(RF(J))` when the terms of `J` are injective. -/
private lemma isIso_derivedHomologyUnit_app (q : ℤ) (J : CochainComplex.Plus A)
    (hJ : ∀ n, Injective (J.obj.X n)) : IsIso ((derivedHomologyUnit F q).app J) := by
  have := isIso_rightDerivedFunctorPlusUnit_app F J hJ
  rw [derivedHomologyUnit_app]
  have h : IsIso ((DerivedCategory.Plus.homologyFunctor B q).map
      (F.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient A).obj J))) := by
    infer_instance
  exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' inferInstance
    (IsIso.comp_isIso' h inferInstance))

/-- `H^q(RF(X[0])) = R^qF(X)`. -/
private noncomputable def rightDerivedPlusIso (q : ℤ) :
    singleFunctorPlus A 0 ⋙ derivedHomology F q ≅ F.rightDerivedPlus q :=
  Iso.refl _

/-- `RF` followed by `H^n` inverts a quasi-isomorphism of bounded below complexes. -/
private lemma isIso_derivedHomology_map (n : ℤ) {X J : CochainComplex.Plus A} (u : X ⟶ J)
    [QuasiIso u.hom] : IsIso ((derivedHomology F n).map u) :=
  have := isIso_Q_map u
  inferInstanceAs (IsIso ((F.rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.homologyFunctor B n).map (DerivedCategory.Plus.Q.map u)))

/-- **The computation behind all three parts.** If `u : X ⟶ J` is a quasi-isomorphism of
bounded below cochain complexes of `𝒜` whose target has injective terms, then
`H^n(F(J)) ≅ H^n(RF(X))`: the unit `F(J) ⟶ RF(J)` is invertible because `J` is a complex of
injective objects, and `RF(X) ≅ RF(J)` because `RF` inverts quasi-isomorphisms. -/
private noncomputable def mapHomologyIso (n : ℤ) {X J : CochainComplex.Plus A} (u : X ⟶ J)
    (hu : QuasiIso u.hom) (hJ : ∀ m, Injective (J.obj.X m)) :
    (mapHomology F n).obj J ≅ (derivedHomology F n).obj X :=
  have := isIso_derivedHomologyUnit_app F n J hJ
  have := hu
  have := isIso_derivedHomology_map F n u
  asIso ((derivedHomologyUnit F n).app J) ≪≫ (asIso ((derivedHomology F n).map u)).symm

variable {K : CochainComplex A ℤ} (I : K.CartanEilenbergResolution)

/-- `L = F(I)`, the double complex obtained by applying `F` to each term of `I`. -/
private abbrev mapBicomplex : HomologicalComplex₂ B (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  ((F.mapHomologicalComplex (ComplexShape.up ℤ)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj I.bicomplex

/-- The column `I^{p,•}` of a Cartan-Eilenberg resolution, as a bounded below complex. -/
private def column (p : ℤ) : CochainComplex.Plus A :=
  ⟨I.bicomplex.X p, ⟨0, I.isStrictlyGE p⟩⟩

/-- The differential `I^{p,•} ⟶ I^{p',•}` in the first direction. -/
private def columnD (p p' : ℤ) : column I p ⟶ column I p' :=
  ObjectProperty.homMk (I.bicomplex.d p p')

/-- The augmentation `K^p[0] ⟶ I^{p,•}`, an injective resolution of `K^p`. -/
private noncomputable def augmentation (p : ℤ) : (singleFunctorPlus A 0).obj (K.X p) ⟶ column I p :=
  ObjectProperty.homMk (I.ε.f p)

private lemma isIso_derivedHomologyUnit_app_column (q p : ℤ) :
    IsIso ((derivedHomologyUnit F q).app (column I p)) :=
  isIso_derivedHomologyUnit_app F q _ (I.injective p)

private lemma isIso_derivedHomology_map_augmentation (q p : ℤ) :
    IsIso ((derivedHomology F q).map (augmentation I p)) := by
  have : QuasiIso (augmentation I p).hom := I.quasiIso p
  exact isIso_derivedHomology_map F q _

attribute [local instance] isIso_derivedHomologyUnit_app_column
  isIso_derivedHomology_map_augmentation

/-- The `'E₁`-page: `H^q(F(I)^{p,•}) ≅ R^qF(K^p)`. -/
private noncomputable def E₁Iso (q p : ℤ) :
    (mapHomology F q).obj (column I p) ≅ (F.rightDerivedPlus q).obj (K.X p) :=
  mapHomologyIso F q (augmentation I p) (I.quasiIso p) (I.injective p) ≪≫
    (rightDerivedPlusIso F q).app (K.X p)

private lemma E₁Iso_hom (q p : ℤ) : (E₁Iso F I q p).hom =
    ((derivedHomologyUnit F q).app (column I p) ≫
      inv ((derivedHomology F q).map (augmentation I p))) ≫
      (rightDerivedPlusIso F q).hom.app (K.X p) := rfl

omit [HasDerivedCategory.{w} A] [EnoughInjectives A] in
private lemma augmentation_comm (p p' : ℤ) :
    augmentation I p ≫ columnD I p p' =
      (singleFunctorPlus A 0).map (K.d p p') ≫ augmentation I p' :=
  (ObjectProperty.ι (CochainComplex.plus A)).map_injective (I.ε.comm p p')

/-- **Obligation (1)**: the `'E₁`-page of `F(I)` is the complex `p ↦ R^qF(K^p)`. -/
private lemma exists_homologyIso_column (q : ℤ) :
    ∃ e : ∀ p, ((((F.mapHomologicalComplex (ComplexShape.up ℤ)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I.bicomplex).X p).homology q ≅
          (F.rightDerivedPlus q).obj (K.X p),
      ∀ p p', homologyMap ((((F.mapHomologicalComplex (ComplexShape.up ℤ)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I.bicomplex).d p p') q ≫ (e p').hom =
          (e p).hom ≫ (F.rightDerivedPlus q).map (K.d p p') := by
  refine ⟨fun p => E₁Iso F I q p, fun p p' => ?_⟩
  have hu := (derivedHomologyUnit F q).naturality (columnD I p p')
  have hθ : (derivedHomology F q).map ((singleFunctorPlus A 0).map (K.d p p')) ≫
        (rightDerivedPlusIso F q).hom.app (K.X p') =
      (rightDerivedPlusIso F q).hom.app (K.X p) ≫ (F.rightDerivedPlus q).map (K.d p p') :=
    (rightDerivedPlusIso F q).hom.naturality (K.d p p')
  have hd : (derivedHomology F q).map (columnD I p p') =
      inv ((derivedHomology F q).map (augmentation I p)) ≫
        (derivedHomology F q).map ((singleFunctorPlus A 0).map (K.d p p')) ≫
        (derivedHomology F q).map (augmentation I p') := by
    rw [← Functor.map_comp, ← augmentation_comm, Functor.map_comp, IsIso.inv_hom_id_assoc]
  show (mapHomology F q).map (columnD I p p') ≫ (E₁Iso F I q p').hom = _
  rw [E₁Iso_hom, E₁Iso_hom]
  simp only [Category.assoc]
  rw [← Category.assoc, hu, hd]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  rw [hθ]
  exact (Category.assoc _ _ _).symm.trans ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ (F.rightDerivedPlus q).map (K.d p p')) (Category.assoc _ _ _)))

omit [HasDerivedCategory.{w} A] [EnoughInjectives A] in
/-- **(2a)** `H^q_I(I)` is bounded below: its terms in second degree `< 0` vanish, because
those of the columns of `I` do (condition (2) of [Stacks, Tag 015H]). -/
private lemma plus_homology (q : ℤ) : CochainComplex.plus A (I.bicomplex.homology q) := by
  refine ⟨0, (CochainComplex.isStrictlyGE_iff _ _).2 fun i hi => ?_⟩
  refine IsZero.of_iso ?_ (mapHomologicalComplexHomologyIso
    (HomologicalComplex.eval A (ComplexShape.up ℤ) i) (ComplexShape.up ℤ) I.bicomplex q).symm
  refine IsZero.of_epi (homologyπ _ q) (IsZero.of_mono (iCycles _ q) ?_)
  exact CochainComplex.isZero_of_isStrictlyGE (I.bicomplex.X q) 0 i hi

omit [HasDerivedCategory.{w} A] [EnoughInjectives A] in
/-- **(2b)** Condition (6) of [Stacks, Tag 015H], read as an injective resolution of the
*object* `H^q(K^•)`: the augmentation is `homologyMap I.ε q`, whose source is `H^q(K^•)`
placed in second degree `0` because `single 0` is exact. -/
private lemma exists_quasiIso_single_homology (q : ℤ) :
    ∃ u : (HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj (K.homology q) ⟶
      I.bicomplex.homology q, QuasiIso u := by
  have := I.quasiIso_homologyMap q
  exact ⟨(mapHomologicalComplexHomologyIso (HomologicalComplex.single A (ComplexShape.up ℤ) 0)
    (ComplexShape.up ℤ) K q).inv ≫ homologyMap I.ε q, inferInstance⟩

omit [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B] [EnoughInjectives A] in
/-- **(2c), one row.** `F` preserves the left homology of the short complex
`I^{p-1,i} ⟶ I^{p,i} ⟶ I^{p+1,i}` of the row `I^{•,i}`: its two first terms are injective by
condition (3) of [Stacks, Tag 015H], its cycles and the kernel of its first differential are
the terms of `Ker(d₁^{p,•})` and of `Ker(d₁^{p-1,•})`, injective by condition (4). -/
private lemma preservesLeftHomologyOf_row (p i : ℤ) :
    F.PreservesLeftHomologyOf
      ((I.bicomplex.sc p).map (HomologicalComplex.eval A (ComplexShape.up ℤ) i)) := by
  have h₁ : Injective (((I.bicomplex.sc p).map
      (HomologicalComplex.eval A (ComplexShape.up ℤ) i)).X₁) := I.injective _ i
  have h₂ : Injective (((I.bicomplex.sc p).map
      (HomologicalComplex.eval A (ComplexShape.up ℤ) i)).X₂) := I.injective p i
  have h₃ : Injective (((I.bicomplex.sc p).map
      (HomologicalComplex.eval A (ComplexShape.up ℤ) i)).cycles) :=
    Injective.of_iso (ShortComplex.mapCyclesIso (I.bicomplex.sc p) _).symm
      (I.injective_cycles p i)
  have h₄ : Injective ((HomologicalComplex.eval A (ComplexShape.up ℤ) i).obj
      (I.bicomplex.cycles ((ComplexShape.up ℤ).prev p))) := I.injective_cycles _ i
  exact preservesLeftHomologyOf_of_injective _
    (isLimitForkMapOfIsLimit' (HomologicalComplex.eval A (ComplexShape.up ℤ) i)
      (I.bicomplex.iCycles_d ((ComplexShape.up ℤ).prev p) p)
      (I.bicomplex.cyclesIsKernel ((ComplexShape.up ℤ).prev p) p (by simp))) F

omit [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B] [EnoughInjectives A] in
/-- **(2c), all rows at once.** `F.mapHomologicalComplex` preserves the left homology of
`I.bicomplex.sc p`, because kernels and cokernels of morphisms of complexes are computed
degreewise and `F` preserves the ones of each row. -/
private lemma preservesLeftHomologyOf_sc (p : ℤ) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).PreservesLeftHomologyOf (I.bicomplex.sc p) := by
  have h : ((I.bicomplex.sc p).leftHomologyData).IsPreservedBy
      (F.mapHomologicalComplex (ComplexShape.up ℤ)) := by
    constructor
    · refine preservesLimit_parallelPair_mapHomologicalComplex _ _ F (fun i => ?_)
      have := preservesLeftHomologyOf_row F I p i
      exact ShortComplex.LeftHomologyData.IsPreservedBy.hg
        (((I.bicomplex.sc p).map
          (HomologicalComplex.eval A (ComplexShape.up ℤ) i)).leftHomologyData) F
    · refine preservesColimit_parallelPair_mapHomologicalComplex _ _ F (fun i => ?_)
      have := preservesLeftHomologyOf_row F I p i
      have h' := ShortComplex.LeftHomologyData.IsPreservedBy.hf'
        ((I.bicomplex.sc p).leftHomologyData.map
          (HomologicalComplex.eval A (ComplexShape.up ℤ) i)) F
      rwa [ShortComplex.LeftHomologyData.map_f'] at h'
  exact Functor.PreservesLeftHomologyOf.mk' _ (I.bicomplex.sc p).leftHomologyData

omit [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B] [EnoughInjectives A] in
/-- **(2c)** `F` commutes with the homology of `I` in the first direction: each differential
of the row `I^{•,q}` is a split surjection onto a direct summand, its kernel, image and
cohomology being injective (conditions (3)-(6) of [Stacks, Tag 015H]), and a split exact
sequence stays split exact under any additive functor. -/
private lemma nonempty_mapHomologyIso_bicomplex (q : ℤ) :
    Nonempty ((mapBicomplex F I).homology q ≅
      (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (I.bicomplex.homology q)) :=
  have := preservesLeftHomologyOf_sc F I q
  ⟨mapHomologicalComplexHomologyIso (F.mapHomologicalComplex (ComplexShape.up ℤ))
    (ComplexShape.up ℤ) I.bicomplex q⟩

/-- **Obligation (2)**: the `''E₂`-page of `F(I)` is `R^pF(H^q(K^•))`.

The `''E₁`-page is `H^q_I(F(I))`, which agrees with `F(H^q_I(I))` because each differential
of the row `I^{•,q}` is a split surjection onto a direct summand (its kernel, image and
cohomology are injective), and `H^q_I(I)` is an injective resolution of `H^q(K^•)` by
condition (6) of [Stacks, Tag 015H], so `H^p` of `F` of it is `R^pF(H^q(K^•))` by
`derivedHomologyUnit`. -/
private lemma nonempty_homologyIso_homology (p q : ℤ) :
    Nonempty (((((F.mapHomologicalComplex (ComplexShape.up ℤ)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I.bicomplex).homology q).homology p ≅
          (F.rightDerivedPlus p).obj (K.homology q)) := by
  obtain ⟨u, hu⟩ := exists_quasiIso_single_homology I q
  obtain ⟨e⟩ := nonempty_mapHomologyIso_bicomplex F I q
  exact ⟨(HomologicalComplex.homologyFunctor B (ComplexShape.up ℤ) p).mapIso e ≪≫
    mapHomologyIso F p (X := (singleFunctorPlus A 0).obj (K.homology q))
      (J := ⟨I.bicomplex.homology q, plus_homology I q⟩) (ObjectProperty.homMk u) hu
      (I.injective_homology q) ≪≫ (rightDerivedPlusIso F p).app (K.homology q)⟩

omit [HasDerivedCategory.{w} A] [EnoughInjectives A] in
/-- The double complex of a Cartan-Eilenberg resolution is bounded in the sense required by the
machinery of the total complex: it vanishes in negative second degrees (condition (2) of
[Stacks, Tag 015H]) and in first degrees below some `i₀` (condition (1)). -/
public lemma exists_bounds_bicomplex :
    ∃ i₀ : ℤ, (∀ p q : ℤ, q < 0 → IsZero ((I.bicomplex.X p).X q)) ∧
      ∀ p : ℤ, p < i₀ → IsZero (I.bicomplex.X p) := by
  obtain ⟨i₀, hi₀⟩ := I.boundedBelow
  have := hi₀
  exact ⟨i₀, fun p q h => CochainComplex.isZero_of_isStrictlyGE (I.bicomplex.X p) 0 q h,
    fun p h => CochainComplex.isZero_of_isStrictlyGE I.bicomplex i₀ p h⟩

omit [HasDerivedCategory.{w} A] [EnoughInjectives A] in
/-- Condition (1) of [Stacks, Tag 0133] holds for `I`: on each antidiagonal only finitely many
terms of `I` are nonzero, because `I^{p,\bullet} = 0` for `p \ll 0` (condition (1) of
[Stacks, Tag 015H]) and `I^{p,q} = 0` for `q < 0` (condition (2)). -/
public lemma finite_not_isZero_bicomplex (n : ℤ) :
    {pq : ℤ × ℤ | ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) pq = n ∧ ¬ IsZero ((I.bicomplex.X pq.1).X pq.2)}.Finite := by
  obtain ⟨i₀, hq, hp⟩ := exists_bounds_bicomplex I
  exact finite_not_isZero_of_bounded I.bicomplex i₀ hq hp n

omit [HasDerivedCategory.{w} A] [EnoughInjectives A] in
/-- `Tot(I)` exists: only finitely many terms of `I` are nonzero on each antidiagonal, so the
coproducts defining it are finite (`HomologicalComplex₂.hasTotal_of_finite`). -/
public lemma hasTotal_bicomplex : I.bicomplex.HasTotal (ComplexShape.up ℤ) :=
  HomologicalComplex₂.hasTotal_of_finite _ _ (finite_not_isZero_bicomplex I)

omit [HasDerivedCategory.{w} A] [EnoughInjectives A] in
/-- The terms of `Tot(I)` are injective: `Tot(I)^n` is a coproduct of the injective objects
`I^{p,q}` with `p + q = n`, of which only finitely many are nonzero, hence a finite biproduct of
injective objects. -/
public lemma injective_total_X [I.bicomplex.HasTotal (ComplexShape.up ℤ)] (n : ℤ) :
    Injective ((I.bicomplex.total (ComplexShape.up ℤ)).X n) := by
  obtain ⟨i₀, hq, hp⟩ := exists_bounds_bicomplex I
  exact injective_total_X_of_bounded I.bicomplex i₀ hq hp (fun p q => I.injective p q) n

omit [HasDerivedCategory.{w} A] [EnoughInjectives A] in
/-- `Tot(I)` is bounded below: if `n` is below the bound of condition (1) of
[Stacks, Tag 015H], every summand `I^{p,q}` with `p + q = n` has either `p` below that bound or
`q < 0`, so all the summands of `Tot(I)^n` vanish. -/
public lemma plus_total [I.bicomplex.HasTotal (ComplexShape.up ℤ)] :
    CochainComplex.plus A (I.bicomplex.total (ComplexShape.up ℤ)) := by
  obtain ⟨i₀, hq, hp⟩ := exists_bounds_bicomplex I
  exact ⟨i₀, (CochainComplex.isStrictlyGE_iff _ _).2 fun n hn =>
    isZero_total_X I.bicomplex i₀ hq hp n hn⟩

omit [HasDerivedCategory.{w} A] [EnoughInjectives A] in
/-- The augmentation lands in the kernel of the differential of the column: `ε^p` composed with
`d₂^{p, 0} : I^{p, 0} ⟶ I^{p, 1}` vanishes, because `ε` is a morphism of double complexes out of
`K` placed in second degree `0`, where the differentials in the second direction are zero. This
is the half of condition (3) of [Stacks, Tag 015H] which says that `K^p ⟶ I^{p, 0}` factors
through `Ker(d₂^{p, 0})`. -/
public lemma epsilon_comp_d₂ (n : ℤ) : (I.ε.f n).f 0 ≫ (I.bicomplex.X n).d 0 1 = 0 := by
  rw [(I.ε.f n).comm 0 1]
  simp

omit [HasDerivedCategory.{w} A] [EnoughInjectives A] in
/-- The augmentation commutes with the differentials in the first direction: `ε^p` followed by
`d₁^{p, •}` in second degree `0` is `d_K^p` followed by `ε^{p + 1}`. -/
public lemma epsilon_comp_d₁ (n : ℤ) :
    (I.ε.f n).f 0 ≫ (I.bicomplex.d n (n + 1)).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (K.X n)).hom ≫
        K.d n (n + 1) ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (K.X (n + 1))).inv ≫ (I.ε.f (n + 1)).f 0 := by
  have := congrArg (fun φ => HomologicalComplex.Hom.f φ 0) (I.ε.comm n (n + 1))
  simp only [HomologicalComplex.comp_f] at this
  rw [this]
  simp [HomologicalComplex.single_map_f_self]

omit [HasDerivedCategory.{w} A] [EnoughInjectives A] in
/-- The component in degree `n` of the augmentation `K^\bullet ⟶ Tot(I)`, namely
`K^n ⟶ I^{n, 0} ⟶ Tot(I)^n`. -/
public noncomputable def totalAugmentationf [I.bicomplex.HasTotal (ComplexShape.up ℤ)] (n : ℤ) :
    K.X n ⟶ (I.bicomplex.total (ComplexShape.up ℤ)).X n :=
  (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (K.X n)).inv ≫ (I.ε.f n).f 0 ≫
    I.bicomplex.ιTotal (ComplexShape.up ℤ) n 0 n (by simp)

omit [HasDerivedCategory.{w} A] [EnoughInjectives A] in
/-- **The augmentation `K^\bullet ⟶ Tot(I)`**, the source's map: in degree `n` it is
`K^n ⟶ I^{n, 0}` followed by the inclusion of the summand `I^{n, 0}` of `Tot(I)^n`. It is a
morphism of complexes because the differential of `Tot(I)` is `d₁ + (-1)^p d₂` on the summand
`I^{p, q}` ([Stacks, Tag 012Z]), the `d₂`-term dies against `epsilon_comp_d₂`, and the
`d₁`-term is `epsilon_comp_d₁`. -/
public noncomputable def totalAugmentation [I.bicomplex.HasTotal (ComplexShape.up ℤ)] :
    K ⟶ I.bicomplex.total (ComplexShape.up ℤ) where
  f n := totalAugmentationf I n
  comm' n n' h := by
    obtain rfl : n + 1 = n' := h
    dsimp [totalAugmentationf]
    have h2 : (I.ε.f n).f 0 ≫ (I.bicomplex.X n).d 0 (0 + 1) = 0 := by
      simp [epsilon_comp_d₂ I n]
    simp only [Category.assoc, HomologicalComplex₂.ιTotal_d_up_ℤ, Preadditive.comp_add,
      Units.smul_def, Preadditive.comp_zsmul, reassoc_of% h2,
      reassoc_of% (epsilon_comp_d₁ I n)]
    simp

omit [HasDerivedCategory.{w} A] [EnoughInjectives A] in
/-- The components of the augmentation `K^\bullet ⟶ Tot(I)`. -/
@[simp]
public lemma totalAugmentation_f [I.bicomplex.HasTotal (ComplexShape.up ℤ)] (n : ℤ) :
    (totalAugmentation I).f n = totalAugmentationf I n :=
  rfl

omit [HasDerivedCategory.{w} A] [EnoughInjectives A] in
/-- The augmentation `K^\bullet ⟶ Tot(I)` is `Tot` of the augmentation `ε : K[0] ⟶ I` of the
Cartan-Eilenberg resolution, read through the identification `K^\bullet = Tot(K[0])`. -/
public lemma totalAugmentation_eq [I.bicomplex.HasTotal (ComplexShape.up ℤ)]
    [(singleRowZero K).HasTotal (ComplexShape.up ℤ)] :
    totalAugmentation I = totalSingleRowZeroUnit K ≫
      HomologicalComplex₂.total.map I.ε (ComplexShape.up ℤ) := by
  ext n
  dsimp [totalAugmentation, totalAugmentationf, totalSingleRowZeroUnit]
  rw [Category.assoc, HomologicalComplex₂.ιTotal_map]

omit [HasDerivedCategory.{w} A] [EnoughInjectives A] in
/-- **[Stacks, Tag 0133] for `I`**: the augmentation `K^\bullet ⟶ Tot(I)` is a
quasi-isomorphism. It is `Tot` of the augmentation `ε : K[0] ⟶ I`, whose columns
`ε^p : K^p[0] ⟶ I^{p, \bullet}` are quasi-isomorphisms (condition (3) of [Stacks, Tag 015H]),
and `K^\bullet = Tot(K[0])`; so this is the acyclic assembly lemma `quasiIso_total_map`. -/
public lemma quasiIso_totalAugmentation (hK : CochainComplex.plus A K)
    [I.bicomplex.HasTotal (ComplexShape.up ℤ)] :
    QuasiIso (totalAugmentation I) := by
  obtain ⟨a, ha⟩ := hK
  obtain ⟨i₀, hi₀⟩ := I.boundedBelow
  have := ha
  have := hi₀
  have hq : ∀ p q : ℤ, q < 0 → IsZero (((singleRowZero K).X p).X q) :=
    fun p q h => isZero_singleRowZero_X_X K p q h
  have hp : ∀ p : ℤ, p < min a i₀ → IsZero ((singleRowZero K).X p) :=
    fun p h => isZero_singleRowZero_X K a p (lt_of_lt_of_le h (min_le_left _ _))
  have hq' : ∀ p q : ℤ, q < 0 → IsZero ((I.bicomplex.X p).X q) :=
    fun p q h => CochainComplex.isZero_of_isStrictlyGE (I.bicomplex.X p) 0 q h
  have hp' : ∀ p : ℤ, p < min a i₀ → IsZero (I.bicomplex.X p) :=
    fun p h => CochainComplex.isZero_of_isStrictlyGE I.bicomplex i₀ p
      (lt_of_lt_of_le h (min_le_right _ _))
  have : (singleRowZero K).HasTotal (ComplexShape.up ℤ) := hasTotal_of_bounded _ _ hq hp
  have : QuasiIso (HomologicalComplex₂.total.map I.ε (ComplexShape.up ℤ)) :=
    quasiIso_total_map I.ε (min a i₀) hq hp hq' hp' (fun p => I.quasiIso p)
  have := isIso_totalSingleRowZeroUnit K
  rw [totalAugmentation_eq]
  infer_instance

omit [HasDerivedCategory.{w} A] [EnoughInjectives A] in
/-- **[Stacks, Tag 0133] for `I`**, in the existential form used below: `Tot(I)` is
quasi-isomorphic to `K^\bullet`. -/
private lemma exists_quasiIso_total (hK : CochainComplex.plus A K)
    [I.bicomplex.HasTotal (ComplexShape.up ℤ)] :
    ∃ u : K ⟶ I.bicomplex.total (ComplexShape.up ℤ), QuasiIso u :=
  ⟨totalAugmentation I, quasiIso_totalAugmentation I hK⟩

omit [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B] [EnoughInjectives A] in
/-- **`Tot(F(I)) = F(Tot(I))`**: the coproducts defining the total complex have only finitely
many nonzero summands, and an additive functor preserves such a coproduct
(`StacksDraft.TotalComplexQuasiIso.isColimitMapCofan`), so the canonical map
`Tot(F(I)) ⟶ F(Tot(I))` assembled from the
`F(ι_{p,q})` is an isomorphism in each degree. -/
private lemma nonempty_totalIso [I.bicomplex.HasTotal (ComplexShape.up ℤ)]
    [HomologicalComplex₂.HasTotal (mapBicomplex F I) (ComplexShape.up ℤ)] :
    Nonempty (HomologicalComplex₂.total (mapBicomplex F I) (ComplexShape.up ℤ) ≅
      (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (I.bicomplex.total (ComplexShape.up ℤ))) :=
  ⟨HomologicalComplex₂.TotalMap.totalIsoOfFinite F I.bicomplex
    (fun n => finite_not_isZero_bicomplex I n)⟩

omit [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B] [EnoughInjectives A] in
/-- **(3a)** `Tot(I)` is an injective resolution of `K^\bullet` ([Stacks, Tag 0133]) and `F`
commutes with the total complex: there are a bounded below complex `J` of injective objects, a
quasi-isomorphism `K^\bullet ⟶ J` and an isomorphism `Tot(F(I)) ≅ F(J)`. Both halves are the
source's: `J = Tot(I)` is a complex of injectives quasi-isomorphic to `K^\bullet`, and
`Tot(F(I)) = F(Tot(I))` because only finitely many terms of `I` are nonzero on each
antidiagonal, so that the coproducts defining `Tot` are finite biproducts, which every additive
functor preserves. -/
private lemma exists_injectiveResolution_total (hK : CochainComplex.plus A K)
    [HomologicalComplex₂.HasTotal (mapBicomplex F I) (ComplexShape.up ℤ)] :
    ∃ (J : CochainComplex.Plus A) (u : (⟨K, hK⟩ : CochainComplex.Plus A) ⟶ J),
      QuasiIso u.hom ∧ (∀ m, Injective (J.obj.X m)) ∧
      Nonempty (HomologicalComplex₂.total (mapBicomplex F I) (ComplexShape.up ℤ) ≅
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj J.obj) := by
  have := hasTotal_bicomplex I
  obtain ⟨u, hu⟩ := exists_quasiIso_total I hK
  exact ⟨⟨I.bicomplex.total (ComplexShape.up ℤ), plus_total I⟩, ObjectProperty.homMk u, hu,
    fun m => injective_total_X I m, nonempty_totalIso F I⟩

/-- **Obligation (3)**: the cohomology of `Tot(F(I))` is the cohomology of `RF(K^•)`.

`Tot(F(I)) = F(Tot(I))` because only finitely many terms of `I` are nonzero on each
antidiagonal, and `Tot(I)` is an injective resolution of `K^•` ([Stacks, Tag 0133]), so
`H^n` of `F` of it is `H^n(RF(K^•))` by `derivedHomologyUnit`. -/
private lemma nonempty_homologyIso_total (hK : CochainComplex.plus A K)
    [HomologicalComplex₂.HasTotal
      (((F.mapHomologicalComplex (ComplexShape.up ℤ)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I.bicomplex) (ComplexShape.up ℤ)] (n : ℤ) :
    Nonempty ((HomologicalComplex₂.total
        (((F.mapHomologicalComplex (ComplexShape.up ℤ)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I.bicomplex) (ComplexShape.up ℤ)).homology n ≅
          (DerivedCategory.Plus.homologyFunctor B n).obj
            (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj ⟨K, hK⟩))) := by
  obtain ⟨J, u, hu, hJ, ⟨e⟩⟩ := exists_injectiveResolution_total F I hK
  exact ⟨(HomologicalComplex.homologyFunctor B (ComplexShape.up ℤ) n).mapIso e ≪≫
    mapHomologyIso F n u hu hJ⟩

end

/-- **Existence of Cartan-Eilenberg resolutions.** A cochain complex `K` over an abelian
category with enough injectives which is strictly `≥ n` admits a Cartan-Eilenberg
resolution whose double complex is strictly `≥ n` in the first direction. -/
@[stacks 015I, ega "0 11.4.2" "bounded below case", sga "2 VIII 1.4" "existence of resolution"]
public theorem _root_.CochainComplex.exists_cartanEilenbergResolution {C : Type u}
    [Category.{v} C] [Abelian C] [EnoughInjectives C] (K : CochainComplex C ℤ) (n : ℤ)
    [CochainComplex.IsStrictlyGE K n] :
    ∃ I : CochainComplex.CartanEilenbergResolution K,
      CochainComplex.IsStrictlyGE I.bicomplex n :=
  exists_cartanEilenbergResolution_of_horseshoe (horseshoeProperty C)
    exists_injectiveResolution_isZero K n

/-- **The spectral sequences of a Cartan-Eilenberg resolution.** Let `F : 𝒜 ⥤ ℬ` be an
additive functor of abelian categories, with `𝒜` having enough injectives, let `K` be a
bounded below cochain complex of `𝒜` and let `I` be a Cartan-Eilenberg resolution of `K`.
For the double complex `L = F(I)`: the `'E₁`-page `H^q(L^{p,•})` is the complex `R^qF(K^p)`
in `p`, with differential induced by that of `K`; the `''E₂`-page
`H^p_{II}(H^q_I(L^{•,•}))` is `R^pF(H^q(K^•))`; and `H^n(Tot(L))` is `H^n(RF(K^•))`, the
abutment of both spectral sequences. -/
@[stacks 015J,
  ega "0 11.4.3" "bounded below case",
  ega "0 12.4.1" "bounded below complexes",
  ega "0 12.1.7" "partial"]
public theorem _root_.CochainComplex.CartanEilenbergResolution.exists_homologyIso_rightDerivedPlus
    {A : Type u} {B : Type u'} [Category.{v} A] [Category.{v'} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B] (F : A ⥤ B) [F.Additive]
    [EnoughInjectives A] {K : CochainComplex A ℤ} (hK : CochainComplex.plus A K)
    (I : K.CartanEilenbergResolution)
    [HomologicalComplex₂.HasTotal
      (((F.mapHomologicalComplex (ComplexShape.up ℤ)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I.bicomplex) (ComplexShape.up ℤ)] :
    (∀ q, ∃ e : ∀ p, ((((F.mapHomologicalComplex (ComplexShape.up ℤ)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I.bicomplex).X p).homology q ≅
          (F.rightDerivedPlus q).obj (K.X p),
      ∀ p p', homologyMap ((((F.mapHomologicalComplex (ComplexShape.up ℤ)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I.bicomplex).d p p') q ≫ (e p').hom =
          (e p).hom ≫ (F.rightDerivedPlus q).map (K.d p p')) ∧
    (∀ p q, Nonempty (((((F.mapHomologicalComplex (ComplexShape.up ℤ)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I.bicomplex).homology q).homology p ≅
          (F.rightDerivedPlus p).obj (K.homology q))) ∧
    (∀ n, Nonempty ((HomologicalComplex₂.total
        (((F.mapHomologicalComplex (ComplexShape.up ℤ)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I.bicomplex) (ComplexShape.up ℤ)).homology n ≅
          (DerivedCategory.Plus.homologyFunctor B n).obj
            (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj ⟨K, hK⟩)))) :=
  ⟨fun q => exists_homologyIso_column F I q,
    fun p q => nonempty_homologyIso_homology F I p q,
    fun n => nonempty_homologyIso_total F I hK n⟩

end StacksDraft.CartanEilenbergResolutions

end
