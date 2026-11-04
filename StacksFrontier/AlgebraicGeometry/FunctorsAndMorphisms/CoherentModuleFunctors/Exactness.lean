module

public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.Algebra.Homology.ShortComplex.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.CoherentModuleFunctors.CoherentApproximation
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.CoherentModuleFunctors.Extension
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.Basic
public import StacksFrontier.AlgebraicGeometry.QcohLimits.ClosedUnderKernels

/-!
# Exactness of the extension from the coherent to the quasi-coherent modules

Let `X` and `Y` be Noetherian schemes, `F : Coh(𝒪_X) ⥤ Coh(𝒪_Y)` a functor and `E` a
filtered-colimit-preserving extension of `F` to `QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)`. If `F` is left exact,
right exact or exact, then so is `E`. Indeed a short exact sequence of quasi-coherent modules is
a filtered colimit of short exact sequences of coherent modules, the extension carries that
presentation to the colimit of the short complexes obtained by applying `F`, and a filtered
colimit of short complexes which are exact with a monomorphism, resp. an epimorphism, again has
that property.

## Main results

* `AlgebraicGeometry.CoherentModuleFunctors.FilteredColimitExtension.preservesFiniteLimits`: the
  extension of a left exact functor is left exact.
* `AlgebraicGeometry.CoherentModuleFunctors.FilteredColimitExtension.preservesFiniteColimits`:
  the extension of a right exact functor is right exact.
* `AlgebraicGeometry.CoherentModuleFunctors.FilteredColimitExtension.exactFunctor`: the extension
  of an exact functor is exact.

## Implementation notes

Exactness is read as the preservation of finite limits, resp. finite colimits, and each half is
reduced to the preservation of the kernel, resp. the cokernel, of a single morphism of
quasi-coherent modules. The two halves are proved separately and each uses only the
corresponding half of exactness of `F`; they are then combined into the statement for exact
functors. The approximation of a short exact sequence of quasi-coherent modules by short exact
sequences of coherent modules is taken in the category of modules, so the diagrams and cocones
involved are lifted to the two full subcategories, and the filtered colimit arguments are
isolated in lemmas about an abstract abelian category.

## References

* [Stacks Project, Tag 0FZL](https://stacks.math.columbia.edu/tag/0FZL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.SheafOfModules (CoherentModules)
open scoped ZeroObject

universe u w

namespace AlgebraicGeometry.CoherentModuleFunctors

/-! ### Short complexes and a functor -/

section Abstract

variable {C : Type w} {D : Type*} {E : Type*} [Category.{u} C] [Category.{u} D] [Category.{u} E]
  [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroMorphisms E]

/-- A natural isomorphism of functors preserving zero morphisms induces a natural isomorphism of
the induced functors on short complexes. -/
private def mapShortComplexNatIso {G₁ G₂ : C ⥤ D} [G₁.PreservesZeroMorphisms]
    [G₂.PreservesZeroMorphisms] (e : G₁ ≅ G₂) :
    Functor.mapShortComplex G₁ ≅ Functor.mapShortComplex G₂ :=
  NatIso.ofComponents (fun S => S.mapNatIso e) (fun _ => by
    apply ShortComplex.hom_ext <;> simp)

/-- A functor which preserves colimits of a given shape also preserves them on short
complexes. -/
private noncomputable def isColimitMapShortComplexMapCocone {J : Type*} [Category J]
    [HasColimitsOfShape J C] [HasColimitsOfShape J D] (G : C ⥤ D) [G.PreservesZeroMorphisms]
    [PreservesColimitsOfShape J G] {T : J ⥤ ShortComplex C} {c : Cocone T} (hc : IsColimit c) :
    IsColimit ((Functor.mapShortComplex G).mapCocone c) :=
  ShortComplex.isColimitOfIsColimitπ _
    (isColimitOfPreserves G (isColimitOfPreserves ShortComplex.π₁ hc))
    (isColimitOfPreserves G (isColimitOfPreserves ShortComplex.π₂ hc))
    (isColimitOfPreserves G (isColimitOfPreserves ShortComplex.π₃ hc))

/-- A functor preserving zero morphisms sends a zero object to a zero object. -/
private lemma isZero_obj (G : C ⥤ D) [G.PreservesZeroMorphisms] {A : C} (hA : IsZero A) :
    IsZero (G.obj A) := by
  rw [IsZero.iff_id_eq_zero, ← G.map_id, hA.eq_of_src (𝟙 A) 0, G.map_zero]

end Abstract

/-! ### Short complexes in a full subcategory -/

section FullSubcategory

variable {C : Type w} [Category.{u} C] [Preadditive C] (P : ObjectProperty C)

/-- The functor on short complexes induced by the inclusion of a full subcategory is fully
faithful. -/
private noncomputable def mapShortComplexιFullyFaithful :
    (Functor.mapShortComplex P.ι).FullyFaithful where
  preimage {_ _} φ :=
    ShortComplex.homMk (P.ι.preimage φ.τ₁) (P.ι.preimage φ.τ₂) (P.ι.preimage φ.τ₃)
      (P.ι.map_injective (by
        rw [P.ι.map_comp, P.ι.map_comp, Functor.map_preimage, Functor.map_preimage]
        exact φ.comm₁₂))
      (P.ι.map_injective (by
        rw [P.ι.map_comp, P.ι.map_comp, Functor.map_preimage, Functor.map_preimage]
        exact φ.comm₂₃))
  map_preimage φ :=
    ShortComplex.hom_ext _ _ (P.ι.map_preimage φ.τ₁) (P.ι.map_preimage φ.τ₂)
      (P.ι.map_preimage φ.τ₃)
  preimage_map φ :=
    ShortComplex.hom_ext _ _ (P.ι.preimage_map φ.τ₁) (P.ι.preimage_map φ.τ₂)
      (P.ι.preimage_map φ.τ₃)

private instance full_mapShortComplexι : (Functor.mapShortComplex P.ι).Full :=
  (mapShortComplexιFullyFaithful P).full

private instance faithful_mapShortComplexι : (Functor.mapShortComplex P.ι).Faithful :=
  (mapShortComplexιFullyFaithful P).faithful

/-- A short complex all of whose terms lie in a full subcategory, read as a short complex in that
subcategory. -/
private def liftShortComplex (S : ShortComplex C) (h₁ : P S.X₁) (h₂ : P S.X₂) (h₃ : P S.X₃) :
    ShortComplex P.FullSubcategory :=
  ShortComplex.mk (ObjectProperty.homMk (X := ⟨S.X₁, h₁⟩) (Y := ⟨S.X₂, h₂⟩) S.f)
    (ObjectProperty.homMk (X := ⟨S.X₂, h₂⟩) (Y := ⟨S.X₃, h₃⟩) S.g)
    (ObjectProperty.hom_ext _ S.zero)

private lemma liftShortComplex_map_ι (S : ShortComplex C) (h₁ : P S.X₁) (h₂ : P S.X₂)
    (h₃ : P S.X₃) : (liftShortComplex P S h₁ h₂ h₃).map P.ι = S :=
  rfl

/-- A diagram of short complexes all of whose terms lie in a full subcategory, read as a diagram
of short complexes in that subcategory. -/
private def liftShortComplexFunctor {J : Type*} [Category J] (T : J ⥤ ShortComplex C)
    (hT : ∀ j, P (T.obj j).X₁ ∧ P (T.obj j).X₂ ∧ P (T.obj j).X₃) :
    J ⥤ ShortComplex P.FullSubcategory where
  obj j := liftShortComplex P (T.obj j) (hT j).1 (hT j).2.1 (hT j).2.2
  map {_ _} f :=
    { τ₁ := ObjectProperty.homMk (T.map f).τ₁
      τ₂ := ObjectProperty.homMk (T.map f).τ₂
      τ₃ := ObjectProperty.homMk (T.map f).τ₃
      comm₁₂ := ObjectProperty.hom_ext _ (T.map f).comm₁₂
      comm₂₃ := ObjectProperty.hom_ext _ (T.map f).comm₂₃ }
  map_id _ := by
    apply ShortComplex.hom_ext <;> apply ObjectProperty.hom_ext <;> (rw [T.map_id]; rfl)
  map_comp _ _ := by
    apply ShortComplex.hom_ext <;> apply ObjectProperty.hom_ext <;> (rw [T.map_comp]; rfl)

private lemma liftShortComplexFunctor_comp_ι {J : Type*} [Category J] (T : J ⥤ ShortComplex C)
    (hT : ∀ j, P (T.obj j).X₁ ∧ P (T.obj j).X₂ ∧ P (T.obj j).X₃) :
    liftShortComplexFunctor P T hT ⋙ Functor.mapShortComplex P.ι = T :=
  rfl

/-- A cocone of short complexes whose terms all lie in a full subcategory, read as a cocone in
that subcategory. -/
private def liftCocone {J : Type*} [Category J] {T : J ⥤ ShortComplex C}
    (hT : ∀ j, P (T.obj j).X₁ ∧ P (T.obj j).X₂ ∧ P (T.obj j).X₃) (c : Cocone T)
    (k₁ : P c.pt.X₁) (k₂ : P c.pt.X₂) (k₃ : P c.pt.X₃) :
    Cocone (liftShortComplexFunctor P T hT) where
  pt := liftShortComplex P c.pt k₁ k₂ k₃
  ι :=
    { app := fun j =>
        { τ₁ := ObjectProperty.homMk (c.ι.app j).τ₁
          τ₂ := ObjectProperty.homMk (c.ι.app j).τ₂
          τ₃ := ObjectProperty.homMk (c.ι.app j).τ₃
          comm₁₂ := ObjectProperty.hom_ext _ (c.ι.app j).comm₁₂
          comm₂₃ := ObjectProperty.hom_ext _ (c.ι.app j).comm₂₃ }
      naturality := fun _ _ f => by
        apply (Functor.mapShortComplex P.ι).map_injective
        rw [Functor.map_comp, Functor.map_comp]
        exact c.ι.naturality f }

private lemma mapCocone_liftCocone {J : Type*} [Category J] {T : J ⥤ ShortComplex C}
    (hT : ∀ j, P (T.obj j).X₁ ∧ P (T.obj j).X₂ ∧ P (T.obj j).X₃) (c : Cocone T)
    (k₁ : P c.pt.X₁) (k₂ : P c.pt.X₂) (k₃ : P c.pt.X₃) :
    (Functor.mapShortComplex P.ι).mapCocone (liftCocone P hT c k₁ k₂ k₃) = c :=
  rfl

end FullSubcategory

/-! ### Filtered colimits of short complexes -/

section FilteredColimits

variable {C : Type w} [Category.{u} C] [Abelian C] {J : Type u} [SmallCategory J]
  [HasColimitsOfShape J C] [HasExactColimitsOfShape J C]

/-- Taking the colimit of the short complex of functors attached to a diagram of short complexes
gives the colimit of the diagram. -/
private noncomputable def colimitCoconePtIso (T : J ⥤ ShortComplex C) :
    (ShortComplex.colimitCocone T).pt ≅
      ((ShortComplex.functorEquivalence J C).inverse.obj T).map (colim (J := J) (C := C)) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      simp [ShortComplex.colimitCocone, ShortComplex.functorEquivalence,
        ShortComplex.FunctorEquivalence.inverse])
    (by
      simp [ShortComplex.colimitCocone, ShortComplex.functorEquivalence,
        ShortComplex.FunctorEquivalence.inverse])

/-- The point of a colimit cocone of a diagram of short complexes, compared with the colimit of
the attached short complex of functors. -/
private noncomputable def coconePtIso {T : J ⥤ ShortComplex C} {c : Cocone T} (hc : IsColimit c) :
    c.pt ≅ ((ShortComplex.functorEquivalence J C).inverse.obj T).map (colim (J := J) (C := C)) :=
  IsColimit.coconePointUniqueUpToIso hc (ShortComplex.isColimitColimitCocone T) ≪≫
    colimitCoconePtIso T

/-- A filtered colimit of short complexes which are exact with a monomorphism on the left is
exact with a monomorphism on the left. -/
private theorem exact_mono_of_isColimit (T : J ⥤ ShortComplex C) {c : Cocone T}
    (hc : IsColimit c) (hT : ∀ j, (T.obj j).Exact ∧ Mono (T.obj j).f) :
    c.pt.Exact ∧ Mono c.pt.f := by
  have hK : IsLimit (KernelFork.ofι ((ShortComplex.functorEquivalence J C).inverse.obj T).f
      ((ShortComplex.functorEquivalence J C).inverse.obj T).zero) := by
    apply Limits.evaluationJointlyReflectsLimits
    intro j
    have : Mono (T.obj j).f := (hT j).2
    exact (KernelFork.isLimitMapConeEquiv _ _).2 (hT j).1.fIsKernel
  have hK' := (KernelFork.isLimitMapConeEquiv
    (KernelFork.ofι ((ShortComplex.functorEquivalence J C).inverse.obj T).f
      ((ShortComplex.functorEquivalence J C).inverse.obj T).zero)
    (colim (J := J) (C := C))).1 (isLimitOfPreserves (colim (J := J) (C := C)) hK)
  have e := coconePtIso hc
  refine ⟨ShortComplex.exact_of_iso e.symm (ShortComplex.exact_of_f_is_kernel _ hK'), ?_⟩
  have : Mono (((ShortComplex.functorEquivalence J C).inverse.obj T).map
      (colim (J := J) (C := C))).f := mono_of_isLimit_fork hK'
  have hcomp : Mono (c.pt.f ≫ e.hom.τ₂) := by
    rw [← e.hom.comm₁₂]
    infer_instance
  exact mono_of_mono c.pt.f e.hom.τ₂

/-- A filtered colimit of short complexes which are exact with an epimorphism on the right is
exact with an epimorphism on the right. -/
private theorem exact_epi_of_isColimit (T : J ⥤ ShortComplex C) {c : Cocone T}
    (hc : IsColimit c) (hT : ∀ j, (T.obj j).Exact ∧ Epi (T.obj j).g) :
    c.pt.Exact ∧ Epi c.pt.g := by
  have hC : IsColimit (CokernelCofork.ofπ ((ShortComplex.functorEquivalence J C).inverse.obj T).g
      ((ShortComplex.functorEquivalence J C).inverse.obj T).zero) := by
    apply Limits.evaluationJointlyReflectsColimits
    intro j
    have : Epi (T.obj j).g := (hT j).2
    exact (CokernelCofork.isColimitMapCoconeEquiv _ _).2 (hT j).1.gIsCokernel
  have hC' := (CokernelCofork.isColimitMapCoconeEquiv
    (CokernelCofork.ofπ ((ShortComplex.functorEquivalence J C).inverse.obj T).g
      ((ShortComplex.functorEquivalence J C).inverse.obj T).zero)
    (colim (J := J) (C := C))).1 (isColimitOfPreserves (colim (J := J) (C := C)) hC)
  have e := coconePtIso hc
  refine ⟨ShortComplex.exact_of_iso e.symm (ShortComplex.exact_of_g_is_cokernel _ hC'), ?_⟩
  have : Epi (((ShortComplex.functorEquivalence J C).inverse.obj T).map
      (colim (J := J) (C := C))).g := epi_of_isColimit_cofork hC'
  have hcomp : Epi (c.pt.g ≫ e.hom.τ₃) := by
    rw [← e.hom.comm₂₃]
    infer_instance
  exact (epi_comp_iff_of_isIso c.pt.g e.hom.τ₃).1 hcomp

end FilteredColimits

/-! ### Exactness of the two inclusions -/

/-- The inclusion of the quasi-coherent modules into all modules preserves finite limits, being
closed under kernels. -/
private instance preservesFiniteLimits_isQuasicoherentι (X : Scheme.{u}) :
    PreservesFiniteLimits (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι := by
  have : ∀ {A B : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory} (f : A ⟶ B),
      PreservesLimit (parallelPair f 0)
        (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι :=
    fun f => (SheafOfModules.isQuasicoherent X.ringCatSheaf).preservesKernels_ι f
  exact Functor.preservesFiniteLimits_of_preservesKernels _

/-- The inclusion `Coh(𝒪_X) ⥤ QCoh(𝒪_X)` preserves zero morphisms. -/
private instance preservesZeroMorphisms_coherentToQuasicoherent (X : Scheme.{u}) :
    (coherentToQuasicoherent X).PreservesZeroMorphisms where
  map_zero _ _ := rfl

/-- The inclusion `Coh(𝒪_X) ⥤ QCoh(𝒪_X)` composed with the inclusion of the quasi-coherent
modules into all modules is the inclusion of the coherent modules. -/
private lemma coherentToQuasicoherent_comp_ι (X : Scheme.{u}) :
    coherentToQuasicoherent X ⋙ (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι =
      ObjectProperty.ι (fun M : SheafOfModules.{u} X.ringCatSheaf => M.IsCoherent) :=
  rfl

/-- The inclusion `Coh(𝒪_X) ⥤ QCoh(𝒪_X)` preserves finite limits. -/
private instance preservesFiniteLimits_coherentToQuasicoherent (X : Scheme.{u}) :
    PreservesFiniteLimits (coherentToQuasicoherent X) := by
  have : PreservesFiniteLimits
      (coherentToQuasicoherent X ⋙ (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι) := by
    rw [coherentToQuasicoherent_comp_ι]
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves (coherentToQuasicoherent X)
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι

/-- The inclusion `Coh(𝒪_X) ⥤ QCoh(𝒪_X)` preserves finite colimits. -/
private instance preservesFiniteColimits_coherentToQuasicoherent (X : Scheme.{u}) :
    PreservesFiniteColimits (coherentToQuasicoherent X) := by
  have : PreservesFiniteColimits
      (coherentToQuasicoherent X ⋙ (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι) := by
    rw [coherentToQuasicoherent_comp_ι]
    infer_instance
  exact preservesFiniteColimits_of_reflects_of_preserves (coherentToQuasicoherent X)
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι

/-! ### Short exact sequences and the extension -/

section Extension

/-- The quasi-coherent `𝒪_X`-modules. -/
private abbrev Qcoh (X : Scheme.{u}) :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory

variable {X Y : Scheme.{u}}
  {F : CoherentModules X.ringCatSheaf ⥤ CoherentModules Y.ringCatSheaf}

/-- An extension sends the zero module to a zero module as soon as the original functor does, and
therefore preserves zero morphisms. -/
private lemma preservesZeroMorphisms_of_isZero (E : FilteredColimitExtension X Y F)
    (hFZ : IsZero (F.obj (0 : CoherentModules X.ringCatSheaf))) :
    E.functor.PreservesZeroMorphisms := by
  have hqX : IsZero ((coherentToQuasicoherent X).obj (0 : CoherentModules X.ringCatSheaf)) :=
    isZero_obj _ (isZero_zero _)
  have hqY : IsZero ((coherentToQuasicoherent Y).obj
      (F.obj (0 : CoherentModules X.ringCatSheaf))) :=
    isZero_obj _ hFZ
  have hE : IsZero (E.functor.obj (0 : Qcoh X)) :=
    (hqY.of_iso (E.iso.app 0)).of_iso
      (E.functor.mapIso (IsZero.iso (isZero_zero (Qcoh X)) hqX))
  refine ⟨fun A B => ?_⟩
  calc E.functor.map (0 : A ⟶ B)
      = E.functor.map ((0 : A ⟶ (0 : Qcoh X)) ≫ (0 : (0 : Qcoh X) ⟶ B)) := by simp
    _ = E.functor.map (0 : A ⟶ (0 : Qcoh X)) ≫ E.functor.map (0 : (0 : Qcoh X) ⟶ B) :=
        E.functor.map_comp _ _
    _ = 0 := by rw [hE.eq_of_tgt (E.functor.map (0 : A ⟶ (0 : Qcoh X))) 0, zero_comp]

/-- The extension of a left exact functor preserves zero morphisms. -/
private lemma preservesZeroMorphisms_of_preservesFiniteLimits
    (E : FilteredColimitExtension X Y F) [PreservesFiniteLimits F] :
    E.functor.PreservesZeroMorphisms :=
  preservesZeroMorphisms_of_isZero E (isZero_obj F (isZero_zero _))

/-- The extension of a right exact functor preserves zero morphisms. -/
private lemma preservesZeroMorphisms_of_preservesFiniteColimits
    (E : FilteredColimitExtension X Y F) [PreservesFiniteColimits F] :
    E.functor.PreservesZeroMorphisms :=
  preservesZeroMorphisms_of_isZero E (isZero_obj F (isZero_zero _))

/-- A short exact sequence of quasi-coherent modules, after applying the extension, is the
filtered colimit of the short complexes obtained by applying the original functor to a coherent
approximation; the approximating short complexes are exact, with a kernel on the left and a
cokernel on the right. -/
private lemma exists_isColimit_map_extension [IsNoetherian X] [F.PreservesZeroMorphisms]
    (E : FilteredColimitExtension X Y F) [E.functor.PreservesZeroMorphisms]
    (S : ShortComplex (Qcoh X)) (hS : S.ShortExact) :
    ∃ (J : Type u) (_ : SmallCategory J) (_ : IsFiltered J)
      (T : J ⥤ ShortComplex (CoherentModules X.ringCatSheaf))
      (d : Cocone (T ⋙ Functor.mapShortComplex (F ⋙ coherentToQuasicoherent Y))),
      Nonempty (IsColimit d) ∧ Nonempty (d.pt ≅ S.map E.functor) ∧
        ∀ j, Nonempty (IsLimit (KernelFork.ofι (T.obj j).f (T.obj j).zero)) ∧
          Nonempty (IsColimit (CokernelCofork.ofπ (T.obj j).g (T.obj j).zero)) := by
  have := quasicoherentInclusion_isLeftAdjoint X
  have hS₀ : (S.map (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι).ShortExact :=
    hS.map_of_exact _
  have h₁ : (S.map (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι).X₁.IsQuasicoherent :=
    S.X₁.property
  have h₂ : (S.map (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι).X₂.IsQuasicoherent :=
    S.X₂.property
  have h₃ : (S.map (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι).X₃.IsQuasicoherent :=
    S.X₃.property
  obtain ⟨J, hJ, hJf, T₀, c, hpt, ⟨hc⟩, happrox⟩ :=
    exists_filtered_coherent_shortExact_approximation (X := X) _ hS₀
  have hTcoh : ∀ j, (T₀.obj j).X₁.IsCoherent ∧ (T₀.obj j).X₂.IsCoherent ∧
      (T₀.obj j).X₃.IsCoherent :=
    fun j => ⟨(happrox j).2.1, (happrox j).2.2.1, (happrox j).2.2.2⟩
  have hTqc : ∀ j, (T₀.obj j).X₁.IsQuasicoherent ∧ (T₀.obj j).X₂.IsQuasicoherent ∧
      (T₀.obj j).X₃.IsQuasicoherent := fun j =>
    ⟨have := (hTcoh j).1; isQuasicoherent_of_isCoherent _,
     have := (hTcoh j).2.1; isQuasicoherent_of_isCoherent _,
     have := (hTcoh j).2.2; isQuasicoherent_of_isCoherent _⟩
  have k₁ : c.pt.X₁.IsQuasicoherent := hpt ▸ h₁
  have k₂ : c.pt.X₂.IsQuasicoherent := hpt ▸ h₂
  have k₃ : c.pt.X₃.IsQuasicoherent := hpt ▸ h₃
  -- the approximating diagram, read in the coherent and in the quasi-coherent modules
  let T : J ⥤ ShortComplex (CoherentModules X.ringCatSheaf) :=
    liftShortComplexFunctor (fun M : SheafOfModules.{u} X.ringCatSheaf => M.IsCoherent) T₀ hTcoh
  let cC : Cocone (T ⋙ Functor.mapShortComplex (coherentToQuasicoherent X)) :=
    liftCocone (SheafOfModules.isQuasicoherent X.ringCatSheaf) hTqc c k₁ k₂ k₃
  have hcC : IsColimit cC :=
    isColimitOfReflects
      (Functor.mapShortComplex (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι) hc
  -- apply the extension
  have : PreservesColimitsOfShape J E.functor :=
    E.preservesFilteredColimits.preserves_filtered_colimits J
  let β : (T ⋙ Functor.mapShortComplex (coherentToQuasicoherent X)) ⋙
      Functor.mapShortComplex E.functor ≅
      T ⋙ Functor.mapShortComplex (F ⋙ coherentToQuasicoherent Y) :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft T (mapShortComplexNatIso E.iso)
  let cE := (Functor.mapShortComplex E.functor).mapCocone cC
  refine ⟨J, hJ, hJf, T, (Cocone.precompose β.inv).obj cE,
    ⟨(IsColimit.equivOfNatIsoOfIso β cE _ (Iso.refl _))
      (isColimitMapShortComplexMapCocone E.functor hcC)⟩, ⟨?_⟩, fun j => ⟨⟨?_⟩, ⟨?_⟩⟩⟩
  · -- the point of the transported cocone is the extension applied to `S`
    exact (Functor.mapShortComplex E.functor).mapIso
      ((Functor.mapShortComplex (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι).preimageIso
        (eqToIso (show (cC.pt.map (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι) =
          S.map (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι from hpt)))
  · exact isLimitOfReflects
      (ObjectProperty.ι fun M : SheafOfModules.{u} X.ringCatSheaf => M.IsCoherent)
      ((KernelFork.isLimitMapConeEquiv (KernelFork.ofι (T.obj j).f (T.obj j).zero) _).symm
        (happrox j).1.fIsKernel)
  · exact isColimitOfReflects
      (ObjectProperty.ι fun M : SheafOfModules.{u} X.ringCatSheaf => M.IsCoherent)
      ((CokernelCofork.isColimitMapCoconeEquiv (CokernelCofork.ofπ (T.obj j).g (T.obj j).zero)
        _).symm (happrox j).1.gIsCokernel)

/-- The extension of a left exact functor sends a short exact sequence to an exact short complex
with a monomorphism on the left. -/
private theorem extension_exact_mono [IsNoetherian X] [IsNoetherian Y]
    (E : FilteredColimitExtension X Y F) [PreservesFiniteLimits F]
    [E.functor.PreservesZeroMorphisms]
    (S : ShortComplex (Qcoh X)) (hS : S.ShortExact) :
    (S.map E.functor).Exact ∧ Mono (S.map E.functor).f := by
  obtain ⟨J, _, _, T, d, ⟨hd⟩, ⟨e⟩, hT⟩ := exists_isColimit_map_extension E S hS
  have hTerms : ∀ j, ((T ⋙ Functor.mapShortComplex
      (F ⋙ coherentToQuasicoherent Y)).obj j).Exact ∧
      Mono ((T ⋙ Functor.mapShortComplex (F ⋙ coherentToQuasicoherent Y)).obj j).f := by
    intro j
    have hK := (KernelFork.isLimitMapConeEquiv (KernelFork.ofι (T.obj j).f (T.obj j).zero)
      (F ⋙ coherentToQuasicoherent Y)).1
      (isLimitOfPreserves (F ⋙ coherentToQuasicoherent Y) (hT j).1.some)
    exact ⟨ShortComplex.exact_of_f_is_kernel _ hK, mono_of_isLimit_fork hK⟩
  obtain ⟨hExact, hMono⟩ := exact_mono_of_isColimit _ hd hTerms
  refine ⟨ShortComplex.exact_of_iso e hExact, ?_⟩
  have : Mono (e.hom.τ₁ ≫ (S.map E.functor).f) := by
    rw [e.hom.comm₁₂]
    have : IsIso e.hom.τ₂ := ((ShortComplex.isIso_iff e.hom).mp inferInstance).2.1
    infer_instance
  exact (mono_comp_iff_of_isIso e.hom.τ₁ _).1 this

/-- The extension of a right exact functor sends a short exact sequence to an exact short complex
with an epimorphism on the right. -/
private theorem extension_exact_epi [IsNoetherian X] [IsNoetherian Y]
    (E : FilteredColimitExtension X Y F) [PreservesFiniteColimits F]
    [E.functor.PreservesZeroMorphisms]
    (S : ShortComplex (Qcoh X)) (hS : S.ShortExact) :
    (S.map E.functor).Exact ∧ Epi (S.map E.functor).g := by
  obtain ⟨J, _, _, T, d, ⟨hd⟩, ⟨e⟩, hT⟩ := exists_isColimit_map_extension E S hS
  have hTerms : ∀ j, ((T ⋙ Functor.mapShortComplex
      (F ⋙ coherentToQuasicoherent Y)).obj j).Exact ∧
      Epi ((T ⋙ Functor.mapShortComplex (F ⋙ coherentToQuasicoherent Y)).obj j).g := by
    intro j
    have hC := (CokernelCofork.isColimitMapCoconeEquiv
      (CokernelCofork.ofπ (T.obj j).g (T.obj j).zero)
      (F ⋙ coherentToQuasicoherent Y)).1
      (isColimitOfPreserves (F ⋙ coherentToQuasicoherent Y) (hT j).2.some)
    exact ⟨ShortComplex.exact_of_g_is_cokernel _ hC, epi_of_isColimit_cofork hC⟩
  obtain ⟨hExact, hEpi⟩ := exact_epi_of_isColimit _ hd hTerms
  refine ⟨ShortComplex.exact_of_iso e hExact, ?_⟩
  have : Epi (e.hom.τ₂ ≫ (S.map E.functor).g) := by
    rw [e.hom.comm₂₃]
    have : IsIso e.hom.τ₃ := ((ShortComplex.isIso_iff e.hom).mp inferInstance).2.2
    infer_instance
  exact epi_of_epi e.hom.τ₂ _

/-- The extension of a left exact functor preserves monomorphisms. -/
private lemma extension_preservesMonomorphisms [IsNoetherian X] [IsNoetherian Y]
    (E : FilteredColimitExtension X Y F) [PreservesFiniteLimits F]
    [E.functor.PreservesZeroMorphisms] :
    E.functor.PreservesMonomorphisms := by
  refine ⟨fun {A B} f hf => ?_⟩
  have := hf
  exact (extension_exact_mono E (ShortComplex.mk f (cokernel.π f) (cokernel.condition f))
    ⟨ShortComplex.exact_cokernel f⟩).2

/-- The extension of a right exact functor preserves epimorphisms. -/
private lemma extension_preservesEpimorphisms [IsNoetherian X] [IsNoetherian Y]
    (E : FilteredColimitExtension X Y F) [PreservesFiniteColimits F]
    [E.functor.PreservesZeroMorphisms] :
    E.functor.PreservesEpimorphisms := by
  refine ⟨fun {A B} f hf => ?_⟩
  have := hf
  exact (extension_exact_epi E (ShortComplex.mk (kernel.ι f) f (kernel.condition f))
    ⟨ShortComplex.exact_kernel f⟩).2

/-- The extension of a left exact functor preserves kernels. -/
private lemma extension_preservesKernels [IsNoetherian X] [IsNoetherian Y]
    (E : FilteredColimitExtension X Y F) [PreservesFiniteLimits F]
    [E.functor.PreservesZeroMorphisms] {A B : Qcoh X} (f : A ⟶ B) :
    PreservesLimit (parallelPair f 0) E.functor := by
  have := extension_preservesMonomorphisms E
  have hS := extension_exact_mono E
    (ShortComplex.mk (kernel.ι f) (cokernel.π (kernel.ι f)) (cokernel.condition _))
    ⟨ShortComplex.exact_cokernel (kernel.ι f)⟩
  have hK : IsLimit (KernelFork.ofι (E.functor.map (kernel.ι f))
      (show E.functor.map (kernel.ι f) ≫ E.functor.map (cokernel.π (kernel.ι f)) = 0 by
        rw [← E.functor.map_comp, cokernel.condition, E.functor.map_zero])) := by
    have := hS.2
    exact hS.1.fIsKernel
  have hfac : E.functor.map f =
      E.functor.map (cokernel.π (kernel.ι f)) ≫
        E.functor.map (Abelian.factorThruCoimage f) := by
    rw [← E.functor.map_comp]
    exact congrArg E.functor.map (Abelian.coimage.fac f).symm
  have : Mono (E.functor.map (Abelian.factorThruCoimage f)) :=
    E.functor.map_mono (Abelian.factorThruCoimage f)
  have hKf : IsLimit (KernelFork.ofι (E.functor.map (kernel.ι f))
      (show E.functor.map (kernel.ι f) ≫ E.functor.map f = 0 by
        rw [← E.functor.map_comp, kernel.condition, E.functor.map_zero])) :=
    isKernelCompMono hK (E.functor.map (Abelian.factorThruCoimage f)) hfac
  exact preservesLimit_of_preserves_limit_cone (kernelIsKernel f)
    ((KernelFork.isLimitMapConeEquiv (KernelFork.ofι (kernel.ι f) (kernel.condition f))
      E.functor).symm hKf)

/-- The extension of a right exact functor preserves cokernels. -/
private lemma extension_preservesCokernels [IsNoetherian X] [IsNoetherian Y]
    (E : FilteredColimitExtension X Y F) [PreservesFiniteColimits F]
    [E.functor.PreservesZeroMorphisms] {A B : Qcoh X} (f : A ⟶ B) :
    PreservesColimit (parallelPair f 0) E.functor := by
  have := extension_preservesEpimorphisms E
  have hz : Abelian.image.ι f ≫ cokernel.π f = 0 := by
    apply (cancel_epi (Abelian.factorThruImage f)).1
    rw [← Category.assoc, Abelian.image.fac, cokernel.condition, comp_zero]
  have hexact : (ShortComplex.mk (Abelian.image.ι f) (cokernel.π f) hz).Exact :=
    (ShortComplex.exact_iff_exact_image_ι
      (ShortComplex.mk f (cokernel.π f) (cokernel.condition f))).1
      (ShortComplex.exact_cokernel f)
  have hS := extension_exact_epi E _ ⟨hexact⟩
  have hCoker : IsColimit (CokernelCofork.ofπ (E.functor.map (cokernel.π f))
      (show E.functor.map (Abelian.image.ι f) ≫ E.functor.map (cokernel.π f) = 0 by
        rw [← E.functor.map_comp, hz, E.functor.map_zero])) := by
    have := hS.2
    exact hS.1.gIsCokernel
  have hfac : E.functor.map f =
      E.functor.map (Abelian.factorThruImage f) ≫ E.functor.map (Abelian.image.ι f) := by
    rw [← E.functor.map_comp]
    exact congrArg E.functor.map (Abelian.image.fac f).symm
  have : Epi (E.functor.map (Abelian.factorThruImage f)) :=
    E.functor.map_epi (Abelian.factorThruImage f)
  refine preservesColimit_of_preserves_colimit_cocone (cokernelIsCokernel f) ?_
  refine (CokernelCofork.isColimitMapCoconeEquiv
    (CokernelCofork.ofπ (cokernel.π f) (cokernel.condition f)) E.functor).symm ?_
  exact isCokernelEpiComp hCoker (E.functor.map (Abelian.factorThruImage f)) hfac

end Extension

/-! ### Exactness of the extension -/

/-- **Stacks Project, Tag 0FZL.** The extension of a left exact functor on the coherent modules
of a Noetherian scheme is left exact. -/
@[stacks 0FZL "left_exactness"]
theorem FilteredColimitExtension.preservesFiniteLimits {X Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y]
    {F : CoherentModules X.ringCatSheaf ⥤ CoherentModules Y.ringCatSheaf}
    (E : FilteredColimitExtension X Y F) [PreservesFiniteLimits F] :
    PreservesFiniteLimits E.functor := by
  have := preservesZeroMorphisms_of_preservesFiniteLimits E
  have : ∀ {A B : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory} (f : A ⟶ B),
      PreservesLimit (parallelPair f 0) E.functor := fun f => extension_preservesKernels E f
  exact Functor.preservesFiniteLimits_of_preservesKernels E.functor

/-- **Stacks Project, Tag 0FZL.** The extension of a right exact functor on the coherent modules
of a Noetherian scheme is right exact. -/
@[stacks 0FZL "right_exactness"]
theorem FilteredColimitExtension.preservesFiniteColimits {X Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y]
    {F : CoherentModules X.ringCatSheaf ⥤ CoherentModules Y.ringCatSheaf}
    (E : FilteredColimitExtension X Y F) [PreservesFiniteColimits F] :
    PreservesFiniteColimits E.functor := by
  have := preservesZeroMorphisms_of_preservesFiniteColimits E
  have : ∀ {A B : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory} (f : A ⟶ B),
      PreservesColimit (parallelPair f 0) E.functor := fun f => extension_preservesCokernels E f
  exact Functor.preservesFiniteColimits_of_preservesCokernels E.functor

/-- **Stacks Project, Tag 0FZL.** The extension of an exact functor on the coherent modules of a
Noetherian scheme is exact. -/
@[stacks 0FZL "exactness"]
theorem FilteredColimitExtension.exactFunctor {X Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y]
    {F : CoherentModules X.ringCatSheaf ⥤ CoherentModules Y.ringCatSheaf}
    (E : FilteredColimitExtension X Y F)
    (hF : exactFunctor (CoherentModules X.ringCatSheaf) (CoherentModules Y.ringCatSheaf) F) :
    exactFunctor (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory E.functor := by
  rw [exactFunctor_iff] at hF ⊢
  obtain ⟨_, _⟩ := hF
  exact ⟨E.preservesFiniteLimits, E.preservesFiniteColimits⟩

end AlgebraicGeometry.CoherentModuleFunctors
