module

public import StacksFrontier.AlgebraicGeometry.Ample.DescentStep
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.InvertibleClasses.Basic
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.Basic
public import StacksFrontier.AlgebraicGeometry.PullbackTensor.StalkFormula
public import StacksFrontier.AlgebraicGeometry.TensorFinitePresentation.Basic

/-!
# Descent of invertible modules through a limit of schemes

Let `S = lim Sᵢ` be the limit of a cofiltered system of schemes. Assuming that finitely presented
modules descend through the limit and that isomorphisms between their pullbacks descend to some
stage, every invertible `𝒪_S`-module is the pullback of an invertible `𝒪_{Sᵢ}`-module for some
`i`: descend `L` and a tensor inverse `N` of it to a common stage, then descend the
trivialization `L ⊗ N ≅ 𝒪_S` and recognise the descended module as invertible.

## Main definitions

* `Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso`: for a morphism of schemes `f`,
  `f^*(F ⊗ G) ≅ f^*F ⊗ f^*G`.
* `Stacks.SheafOfModules.Invertible.tensorLeftFunctorSwap`: the sheafified tensor product is
  symmetric.

## Main results

* `Stacks.SheafOfModules.Invertible.isInvertible_of_tensor_iso_unit_right`: a tensor inverse of a
  module sheaf is itself invertible.
* `Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_free_of_finite` and
  `Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_unit`: a free module sheaf on a
  finite index type, and in particular the structure sheaf, is of finite presentation.
* `Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_tensorSheaf`: the tensor product of
  two finitely presented module sheaves on a scheme is of finite presentation.
* `Stacks.AlgebraicGeometry.ModuleLimits.exists_isInvertible_pullback_iso_of_isLimit_of_descent`:
  an invertible module on the limit is the pullback of an invertible module at some stage, given
  the descent properties of finitely presented modules.
* `exists_isInvertible_pullback_iso_of_isLimit_of_descent_of_isAffine_stage`:
  the same, for affine transition morphisms and an affine stage, assuming only that isomorphisms
  between pullbacks descend.
* `Stacks.AlgebraicGeometry.ModuleLimits.fullyFaithful_of_exists_map_of_exists_isIso`: isomorphisms
  between pullbacks of finitely presented modules descend, provided morphisms descend up to
  isomorphism and isomorphisms are detected at a later stage.

## References

* [Stacks Project, Tag 0B8W](https://stacks.math.columbia.edu/tag/0B8W)
* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory TopologicalSpace
open AlgebraicGeometry.SheafOfModules (IsInvertible)

universe v u w

namespace Stacks.SheafOfModules.Invertible

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules

/-- The sheafified tensor product is symmetric: it is the sheafification of the presheaf tensor
product, which is symmetric. -/
noncomputable def tensorLeftFunctorSwap
    (L N : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj N).obj L ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj L).obj N :=
  (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).mapIso (β_ N.val L.val)

/-- If `L ⊗ N` is isomorphic to the structure sheaf, then `N` is invertible. -/
theorem isInvertible_of_tensor_iso_unit_right
    {L N : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO)}
    (e : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj L).obj N ≅
      _root_.SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    AlgebraicGeometry.SheafOfModules.IsInvertible O hO N :=
  isInvertible_of_tensor_iso_unit O hO (tensorLeftFunctorSwap O hO L N ≪≫ e)

end Stacks.SheafOfModules.Invertible

namespace Stacks.AlgebraicGeometry.ModuleLimits

/-- For a morphism of schemes `f : X ⟶ Y`, the pullback of a tensor product:
`f^*(F ⊗_{𝒪_Y} G) ≅ f^*F ⊗_{𝒪_X} f^*G`. -/
noncomputable def pullbackTensorIso {X Y : Scheme.{u}} (f : X ⟶ Y) (F G : Y.Modules) :
    (Scheme.Modules.pullback f).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Y.sheaf.obj,
          Presheaf.isSheaf_of_isSheaf_comp _ (Y.sheaf.obj) (forget₂ CommRingCat RingCat)
            (Y.ringCatSheaf.property)⟩).obj (F)).obj (G))) ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.sheaf.obj,
        Presheaf.isSheaf_of_isSheaf_comp _ (X.sheaf.obj) (forget₂ CommRingCat RingCat)
          (X.ringCatSheaf.property)⟩).obj
        (((Scheme.Modules.pullback f).obj F))).obj (((Scheme.Modules.pullback f).obj G))) :=
  Stacks.RingedSpace.pullbackTensorIsoApp f.toLRSHom.toShHom F G

/-- A free module sheaf on a finite index type is of finite presentation. -/
theorem isFinitePresentation_free_of_finite (X : Scheme.{u}) (ι : Type u) [Finite ι] :
    (_root_.SheafOfModules.free (R := X.ringCatSheaf) ι).IsFinitePresentation := by
  let q := (_root_.SheafOfModules.free.generatingSections
    (R := X.ringCatSheaf) ι).localGeneratorsData.quasiCoherentData
  refine { exists_quasicoherentData := ⟨q, { isFinite_presentation := fun i => ⟨?_, ⟨?_⟩⟩ }⟩ }
  · change ((_root_.SheafOfModules.free.generatingSections
      (R := X.ringCatSheaf) ι).localGeneratorsData.generators i).IsFiniteType
    exact ⟨inferInstanceAs (Finite ι)⟩
  · exact inferInstanceAs (Finite (ULift Empty))

/-- The structure sheaf of a scheme, as a module over itself, is of finite presentation. -/
theorem isFinitePresentation_unit (X : Scheme.{u}) :
    (_root_.SheafOfModules.unit X.ringCatSheaf).IsFinitePresentation :=
  (_root_.SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso
    (coproductUniqueIso fun _ : PUnit => _root_.SheafOfModules.unit X.ringCatSheaf)
    (isFinitePresentation_free_of_finite X PUnit)

/-- The tensor product of two finitely presented module sheaves on a scheme is of finite
presentation. -/
theorem isFinitePresentation_tensorSheaf (X : Scheme.{u}) (F G : X.Modules)
    (hF : F.IsFinitePresentation) (hG : G.IsFinitePresentation) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.sheaf.obj,
      Presheaf.isSheaf_of_isSheaf_comp _ (X.sheaf.obj) (forget₂ CommRingCat RingCat)
        (X.ringCatSheaf.property)⟩).obj (F)).obj (G))).IsFinitePresentation := by
  change ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
    ((X.toRingedSpace)).IsSheaf⟩).obj (F)).obj (G))).IsFinitePresentation
  exact @AlgebraicGeometry.SheafOfModules.tensorSheaf_isFinitePresentation
    X.toRingedSpace F G hF hG

/-- Pulling back along `f` and then `g` agrees with pulling back along any `h` equal to `f ≫ g`. -/
private noncomputable def pullbackPullbackIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {h : X ⟶ Z} (w : f ≫ g = h) (K : Z.Modules) :
    (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj K) ≅
      (Scheme.Modules.pullback h).obj K :=
  (Scheme.Modules.pullbackComp f g).app K ≪≫ (Scheme.Modules.pullbackCongr w).app K

variable {I : Type w} [Category.{v} I] (D : I ⥤ Scheme.{u}) (c : Cone D)

/-- Let `S = lim Dᵢ`. Suppose every morphism between pullbacks to `S` of finitely presented
modules at a stage comes, up to isomorphism, from a later stage, and a morphism whose pullback to
`S` is an isomorphism becomes one at a later stage. Then isomorphisms between pullbacks descend. -/
theorem fullyFaithful_of_exists_map_of_exists_isIso
    (hMap : ∀ (i : I) (A B : (D.obj i).Modules), A.IsFinitePresentation →
      B.IsFinitePresentation →
      ∀ φ : (Scheme.Modules.pullback (c.π.app i)).obj A ⟶
        (Scheme.Modules.pullback (c.π.app i)).obj B,
      ∃ (j : I) (e : j ⟶ i)
        (φj : (Scheme.Modules.pullback (D.map e)).obj A ⟶
          (Scheme.Modules.pullback (D.map e)).obj B)
        (α : (Scheme.Modules.pullback (c.π.app j)).obj
              ((Scheme.Modules.pullback (D.map e)).obj A) ≅
            (Scheme.Modules.pullback (c.π.app i)).obj A)
        (β : (Scheme.Modules.pullback (c.π.app j)).obj
              ((Scheme.Modules.pullback (D.map e)).obj B) ≅
            (Scheme.Modules.pullback (c.π.app i)).obj B),
        (Scheme.Modules.pullback (c.π.app j)).map φj ≫ β.hom = α.hom ≫ φ)
    (hIso : ∀ (j : I) (A B : (D.obj j).Modules), A.IsFinitePresentation →
      B.IsFinitePresentation → ∀ ψ : A ⟶ B,
      IsIso ((Scheme.Modules.pullback (c.π.app j)).map ψ) →
      ∃ (k : I) (g : k ⟶ j), IsIso ((Scheme.Modules.pullback (D.map g)).map ψ))
    (i : I) (A B : (D.obj i).Modules) (hA : A.IsFinitePresentation)
    (hB : B.IsFinitePresentation)
    (h : Nonempty ((Scheme.Modules.pullback (c.π.app i)).obj A ≅
      (Scheme.Modules.pullback (c.π.app i)).obj B)) :
    ∃ (j : I) (e : j ⟶ i), Nonempty ((Scheme.Modules.pullback (D.map e)).obj A ≅
      (Scheme.Modules.pullback (D.map e)).obj B) := by
  obtain ⟨φ⟩ := h
  obtain ⟨j, e, φj, α, β, heq⟩ := hMap i A B hA hB φ.hom
  have hAe : ((Scheme.Modules.pullback (D.map e)).obj A).IsFinitePresentation :=
    @isFinitePresentation_pullback _ _ (D.map e) A hA
  have hBe : ((Scheme.Modules.pullback (D.map e)).obj B).IsFinitePresentation :=
    @isFinitePresentation_pullback _ _ (D.map e) B hB
  have hφj : (Scheme.Modules.pullback (c.π.app j)).map φj = α.hom ≫ φ.hom ≫ β.inv := by
    rw [← Category.assoc, ← heq]
    simp
  have : IsIso ((Scheme.Modules.pullback (c.π.app j)).map φj) := by
    rw [hφj]; infer_instance
  obtain ⟨k, g, hg⟩ := hIso j _ _ hAe hBe φj this
  refine ⟨k, g ≫ e, ⟨?_⟩⟩
  exact (pullbackPullbackIso (D.map g) (D.map e) (D.map_comp g e).symm A).symm ≪≫
    @asIso _ _ _ _ _ hg ≪≫ pullbackPullbackIso (D.map g) (D.map e) (D.map_comp g e).symm B

/-- Let `S = lim Dᵢ` be a cofiltered limit of schemes. If finitely presented modules on `S` and
isomorphisms between their pullbacks descend to some stage, then every invertible module on `S` is
the pullback of an invertible module at some stage. -/
theorem exists_isInvertible_pullback_iso_of_isLimit_of_descent [IsCofiltered I]
    (hDescend : ∀ F : c.pt.Modules, F.IsFinitePresentation →
      ∃ (i : I) (Fᵢ : (D.obj i).Modules), Fᵢ.IsFinitePresentation ∧
        Nonempty (F ≅ (Scheme.Modules.pullback (c.π.app i)).obj Fᵢ))
    (hFullyFaithful : ∀ (i : I) (A B : (D.obj i).Modules), A.IsFinitePresentation →
      B.IsFinitePresentation →
      Nonempty ((Scheme.Modules.pullback (c.π.app i)).obj A ≅
        (Scheme.Modules.pullback (c.π.app i)).obj B) →
      ∃ (j : I) (e : j ⟶ i), Nonempty ((Scheme.Modules.pullback (D.map e)).obj A ≅
        (Scheme.Modules.pullback (D.map e)).obj B))
    (L : c.pt.Modules)
    (hL : IsInvertible c.pt.sheaf.obj c.pt.ringCatSheaf.property L) :
    ∃ (i : I) (Lᵢ : (D.obj i).Modules),
      IsInvertible (D.obj i).sheaf.obj (D.obj i).ringCatSheaf.property Lᵢ ∧
        Nonempty (L ≅ (Scheme.Modules.pullback (c.π.app i)).obj Lᵢ) := by
  obtain ⟨N, ⟨e⟩⟩ := (Stacks.SheafOfModules.Invertible.isInvertible_iff_exists_tensor_iso_unit
    c.pt.sheaf.obj c.pt.ringCatSheaf.property L).mp hL
  have hLfp : L.IsFinitePresentation :=
    @AlgebraicGeometry.SheafOfModules.isFinitePresentation_of_isInvertible c.pt L hL
  have hNinv : IsInvertible c.pt.sheaf.obj c.pt.ringCatSheaf.property N :=
    Stacks.SheafOfModules.Invertible.isInvertible_of_tensor_iso_unit_right _ _ e
  have hNfp : N.IsFinitePresentation :=
    @AlgebraicGeometry.SheafOfModules.isFinitePresentation_of_isInvertible c.pt N hNinv
  obtain ⟨i, Lᵢ, hLᵢ, ⟨eL⟩⟩ := hDescend L hLfp
  obtain ⟨i', Nᵢ, hNᵢ, ⟨eN⟩⟩ := hDescend N hNfp
  obtain ⟨k, a, b, -⟩ := IsCofilteredOrEmpty.cone_objs i i'
  set Lₖ := (Scheme.Modules.pullback (D.map a)).obj Lᵢ
  set Nₖ := (Scheme.Modules.pullback (D.map b)).obj Nᵢ
  have hLₖfp : Lₖ.IsFinitePresentation :=
    @isFinitePresentation_pullback _ _ (D.map a) Lᵢ hLᵢ
  have hNₖfp : Nₖ.IsFinitePresentation :=
    @isFinitePresentation_pullback _ _ (D.map b) Nᵢ hNᵢ
  have eLₖ : L ≅ (Scheme.Modules.pullback (c.π.app k)).obj Lₖ :=
    eL ≪≫ (pullbackPullbackIso (c.π.app k) (D.map a) (c.w a) Lᵢ).symm
  have eNₖ : N ≅ (Scheme.Modules.pullback (c.π.app k)).obj Nₖ :=
    eN ≪≫ (pullbackPullbackIso (c.π.app k) (D.map b) (c.w b) Nᵢ).symm
  set T := (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(D.obj k).sheaf.obj,
    Presheaf.isSheaf_of_isSheaf_comp _ ((D.obj k).sheaf.obj) (forget₂ CommRingCat RingCat)
      ((D.obj k).ringCatSheaf.property)⟩).obj (Lₖ)).obj (Nₖ))
  set U := _root_.SheafOfModules.unit (D.obj k).ringCatSheaf
  have evIso : Nonempty ((Scheme.Modules.pullback (c.π.app k)).obj T ≅
      (Scheme.Modules.pullback (c.π.app k)).obj U) :=
    ⟨pullbackTensorIso (c.π.app k) Lₖ Nₖ ≪≫
      (Stacks.SheafOfModules.Invertible.tensorLeftFunctorCongr
          c.pt.sheaf.obj c.pt.ringCatSheaf.property eLₖ.symm).app
        ((Scheme.Modules.pullback (c.π.app k)).obj Nₖ) ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨c.pt.sheaf.obj, Presheaf.isSheaf_of_isSheaf_comp _ c.pt.sheaf.obj
          (forget₂ CommRingCat RingCat) c.pt.ringCatSheaf.property⟩).obj L).mapIso eNₖ.symm ≪≫
      e ≪≫ (Scheme.Modules.pullbackUnitIso (c.π.app k)).symm⟩
  obtain ⟨m, q, ⟨ψ⟩⟩ := hFullyFaithful k T U
    (isFinitePresentation_tensorSheaf (D.obj k) Lₖ Nₖ hLₖfp hNₖfp)
    (isFinitePresentation_unit (D.obj k)) evIso
  refine ⟨m, (Scheme.Modules.pullback (D.map q)).obj Lₖ,
    Stacks.SheafOfModules.Invertible.isInvertible_of_tensor_iso_unit _ _
      ((pullbackTensorIso (D.map q) Lₖ Nₖ).symm ≪≫ ψ ≪≫
        Scheme.Modules.pullbackUnitIso (D.map q)), ⟨?_⟩⟩
  exact eLₖ ≪≫ (pullbackPullbackIso (c.π.app m) (D.map q) (c.w q) Lₖ).symm

/-- For a cofiltered system of schemes with affine transition morphisms and an affine stage, if
isomorphisms between pullbacks of finitely presented modules descend, then every invertible module
on the limit is the pullback of an invertible module at some stage. -/
theorem exists_isInvertible_pullback_iso_of_isLimit_of_descent_of_isAffine_stage
    (hc : IsLimit c) [IsCofiltered I]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] (i₀ : I) [IsAffine (D.obj i₀)]
    (hFullyFaithful : ∀ (i : I) (A B : (D.obj i).Modules), A.IsFinitePresentation →
      B.IsFinitePresentation →
      Nonempty ((Scheme.Modules.pullback (c.π.app i)).obj A ≅
        (Scheme.Modules.pullback (c.π.app i)).obj B) →
      ∃ (j : I) (e : j ⟶ i), Nonempty ((Scheme.Modules.pullback (D.map e)).obj A ≅
        (Scheme.Modules.pullback (D.map e)).obj B))
    (L : c.pt.Modules)
    (hL : IsInvertible c.pt.sheaf.obj c.pt.ringCatSheaf.property L) :
    ∃ (i : I) (Lᵢ : (D.obj i).Modules),
      IsInvertible (D.obj i).sheaf.obj (D.obj i).ringCatSheaf.property Lᵢ ∧
        Nonempty (L ≅ (Scheme.Modules.pullback (c.π.app i)).obj Lᵢ) :=
  exists_isInvertible_pullback_iso_of_isLimit_of_descent D c
    (fun F hF => @exists_isFinitePresentation_pullback_iso_of_isLimit_of_isAffine_stage
      _ _ D c hc _ _ i₀ _ F hF)
    hFullyFaithful L hL

end Stacks.AlgebraicGeometry.ModuleLimits

end
