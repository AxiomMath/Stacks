module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.RestrictScalarsDerivedAdjunction
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.RestrictScalarsSubcategory
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtendScalarsRestrictTensor
public import StacksFrontier.AlgebraicGeometry.QcohOverAlgebra.RestrictScalars
import StacksCore.Tactic.StacksAttribute

/-!
# The equivalence of [Stacks, Tag 099I], reduced to one Hom-set statement
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.SheafOfModules.DerivedRestrictScalars

open _root_.AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

/-- **A map is invertible as soon as precomposition with it is bijective on every Hom-set.**
Surjectivity at the target produces a right inverse, and injectivity at the source makes it a
left inverse. -/
theorem isIso_of_bijective_postcomp {D : Type*} [Category D] {A B : D} (g : A ⟶ B)
    (h : ∀ X : D, Function.Bijective (fun f : X ⟶ A => f ≫ g)) : IsIso g := by
  obtain ⟨s, hs⟩ := (h B).2 (𝟙 B)
  refine ⟨s, ?_, hs⟩
  refine (h A).1 ?_
  dsimp only
  rw [Category.assoc, show s ≫ g = 𝟙 B from hs, Category.comp_id, Category.id_comp]

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {O O' : Sheaf J CommRingCat.{u}}

/-- **[Stacks, Tag 099I] reduced to one Hom-set statement.** Let `α : 𝒪 ⟶ 𝒪'` be a homomorphism
of sheaves of commutative rings on a site and `ℐ ⊂ 𝒪` a sheaf of ideals. Suppose derived
restriction of scalars `D(𝒪') ⥤ D(𝒪)` has a left adjoint `L` — it does whenever `α` is flat,
`L` being derived extension of scalars — and suppose that for every `ℐ`-derived-complete object
`Y` of `D(𝒪)` and every `X`, precomposition with the unit `X ⟶ (L X)_𝒪` is a bijection

`Hom_{D(𝒪)}((L X)_𝒪, Y) ≃ Hom_{D(𝒪)}(X, Y)`.

Then restriction of scalars is an equivalence `D_comp(𝒪', ℐ𝒪') ⥤ D_comp(𝒪, ℐ)`.

The hypothesis is what the flat-neighbourhood Čech comparison [Stacks, Tag 099H] is for: the
unit is `x ↦ x ⊗ 1`, so its cone is killed by `- ⊗^𝐋 Č(f)`, and a complex killed by `Č(f)` has
no maps into a derived-complete object. -/
theorem isEquivalence_derivedCompleteRestrictScalars_of_bijective_precomp_unit
    (α : O ⟶ O')
    (I : _root_.SheafOfModules.Submodule
      (_root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite J O).O))))
    {L : DerivedCategory
        (_root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite J O).O))) ⥤
      DerivedCategory
        (_root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite J O').O)))}
    (adj₁ : L ⊣ (_root_.SheafOfModules.restrictScalars.{u}
      (ringSheafHom (O := O) (O' := O') α)).mapDerivedCategory)
    (hbij : ∀ Y : DerivedCategory
        (_root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite J O).O))),
      RingedSite.IsDerivedComplete.{u, u, u, u} (ringedSite J O) I Y →
      ∀ X : DerivedCategory
        (_root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite J O).O))),
      Function.Bijective (fun g : (_root_.SheafOfModules.restrictScalars.{u}
          (ringSheafHom (O := O) (O' := O') α)).mapDerivedCategory.obj (L.obj X) ⟶ Y =>
        adj₁.unit.app X ≫ g)) :
    (derivedCompleteRestrictScalars α I).IsEquivalence := by
  obtain ⟨G, ⟨adj₂⟩⟩ :=
    exists_restrictScalars_derivedAdjunction (ringSheafHom (O := O) (O' := O') α)
  let : (_root_.SheafOfModules.restrictScalars.{u}
      (ringSheafHom (O := O) (O' := O') α)).mapDerivedCategory.ReflectsIsomorphisms :=
    CompleteRestrictScalarsEquivalence.reflectsIsomorphisms_mapDerivedCategory _
  have hε : ∀ Y : ObjectProperty.FullSubcategory
      (RingedSite.IsDerivedComplete.{u, u, u, u} (ringedSite J O) I),
      IsIso (adj₂.counit.app Y.obj) := by
    intro Y
    refine isIso_of_bijective_postcomp _ fun X => ?_
    exact (CompleteRestrictScalarsEquivalence.bijective_postcomp_counit_iff_precomp_unit
      adj₁ adj₂ X Y.obj).mpr (hbij Y.obj Y.property X)
  have hG : ∀ Y : ObjectProperty.FullSubcategory
        (RingedSite.IsDerivedComplete.{u, u, u, u} (ringedSite J O) I),
      RingedSite.IsDerivedComplete.{u, u, u, u} (ringedSite J O')
        (RingedSite.extendIdeal (ringSheafHom (O := O) (O' := O') α) I) (G.obj Y.obj) := by
    intro Y
    refine (isDerivedComplete_restrictScalars_iff α I (G.obj Y.obj)).mp ?_
    have := hε Y
    exact (RingedSite.isDerivedComplete_iff_of_iso (ringedSite J O) I
      (asIso (adj₂.counit.app Y.obj))).mpr Y.property
  exact CompleteRestrictScalarsEquivalence.isEquivalence_lift_of_counit adj₂ _ _ _ hG hε

section Flat

open Stacks.Sheaves.FlatNeighbourhood (RestrictedRingModule)

variable (α : O ⟶ O')
  [PreservesFiniteLimits ((Stacks.SheafOfModules.Tensor.sheafTensor O).flip.obj
      (RestrictedRingModule.{u, u, u} α))]

/-- **Extension of scalars along a flat homomorphism is left exact.** Restriction of scalars
does not change the underlying sheaf of abelian groups, so left exactness of
`extendScalars α ⋙ restrictScalars α` is left exactness of `extendScalars α`; and that
composite is `- ⊗_𝒪 𝒪'` by `extendRestrictScalarsTensorIso`, which flatness of `α` assumes to
be left exact. -/
instance preservesFiniteLimits_extendScalarsSheaf :
    PreservesFiniteLimits (ExtendScalarsTensor.extendScalarsSheaf α) := by
  let h₀ : PreservesFiniteLimits
      ((Stacks.SheafOfModules.Tensor.sheafTensor O).flip.obj (RestrictedRingModule.{u, u, u} α) ⋙
        _root_.SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf O)) :=
    inferInstance
  let h₁ : PreservesFiniteLimits
      ((ExtendScalarsTensor.extendScalarsSheaf α ⋙
          _root_.SheafOfModules.restrictScalars (ExtendScalarsTensor.ringSheafMap α)) ⋙
        _root_.SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf O)) :=
    preservesFiniteLimits_of_natIso
      (Functor.isoWhiskerRight (ExtendScalarsTensor.extendRestrictScalarsTensorIso α)
        (_root_.SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf O))).symm
  let h₂ : PreservesFiniteLimits
      (ExtendScalarsTensor.extendScalarsSheaf α ⋙
        _root_.SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf O')) := h₁
  exact preservesFiniteLimits_of_reflects_of_preserves _
    (_root_.SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf O'))

/-- **Under flatness, derived restriction of scalars has a left adjoint**, namely derived
extension of scalars. Both functors are exact — restriction of scalars always, extension of
scalars because `α` is flat — so the change-of-rings adjunction of [Stacks, Tag 03CZ] descends
to the derived categories. -/
def derivedExtendRestrictScalarsAdjunction :
    (ExtendScalarsTensor.extendScalarsSheaf α).mapDerivedCategory ⊣
      (_root_.SheafOfModules.restrictScalars.{u}
        (ringSheafHom (O := O) (O' := O') α)).mapDerivedCategory :=
  (ExtendScalarsTensor.adjunction α).mapDerivedCategory

/-- **[Stacks, Tag 099I] for a flat `α`, reduced to one Hom-set statement.** Restriction of
scalars `D_comp(𝒪', ℐ𝒪') ⥤ D_comp(𝒪, ℐ)` is an equivalence as soon as, for every
`ℐ`-derived-complete `Y` and every `X` of `D(𝒪)`, precomposition with the unit
`X ⟶ (X ⊗^𝐋_𝒪 𝒪')_𝒪` of derived extension of scalars is a bijection on maps into `Y`.

The left adjoint is derived extension of scalars, which exists because `α` is flat; the unit is
the derived image of `x ↦ x ⊗ 1` by `adjunction_unit_comp_extendRestrictScalarsTensorIso`, which
is the map [Stacks, Tag 099H] is stated for. -/
theorem isEquivalence_derivedCompleteRestrictScalars_of_flat
    (I : _root_.SheafOfModules.Submodule
      (_root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite J O).O))))
    (hbij : ∀ Y : DerivedCategory
        (_root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite J O).O))),
      RingedSite.IsDerivedComplete.{u, u, u, u} (ringedSite J O) I Y →
      ∀ X : DerivedCategory
        (_root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite J O).O))),
      Function.Bijective (fun g : (_root_.SheafOfModules.restrictScalars.{u}
          (ringSheafHom (O := O) (O' := O') α)).mapDerivedCategory.obj
            ((ExtendScalarsTensor.extendScalarsSheaf α).mapDerivedCategory.obj X) ⟶ Y =>
        (derivedExtendRestrictScalarsAdjunction α).unit.app X ≫ g)) :
    (derivedCompleteRestrictScalars α I).IsEquivalence :=
  isEquivalence_derivedCompleteRestrictScalars_of_bijective_precomp_unit α I
    (derivedExtendRestrictScalarsAdjunction α) hbij

/-- **[Stacks, Tag 099I] for a flat `α`, reduced to a statement about cochain complexes.**
It is enough to know, for every cochain complex `K` of `𝒪`-modules and every
`ℐ`-derived-complete `Y`, that precomposition with the image in `D(𝒪)` of the degreewise
extension-of-scalars map `K ⟶ (K ⊗_𝒪 𝒪')` is bijective on maps into `Y`. That degreewise map is
`x ↦ x ⊗ 1` in each degree, by
`Stacks.SheafOfModules.ExtendScalarsTensor.adjunction_unit_comp_extendRestrictScalarsTensorIso`,
so this is precisely the hypothesis [Stacks, Tag 099H] is about.

Every object of `D(𝒪)` is the image of a cochain complex, and the unit is natural, so the
hypothesis at a complex transports to the hypothesis at an arbitrary object: precomposing with
an isomorphism does not change bijectivity. -/
theorem isEquivalence_derivedCompleteRestrictScalars_of_complexes
    (I : _root_.SheafOfModules.Submodule
      (_root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite J O).O))))
    (hK : ∀ (K : CochainComplex
        (_root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite J O).O))) ℤ)
      (Y : DerivedCategory
        (_root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite J O).O)))),
      RingedSite.IsDerivedComplete.{u, u, u, u} (ringedSite J O) I Y →
      Function.Bijective (fun g : DerivedCategory.Q.obj
          (((_root_.SheafOfModules.restrictScalars.{u}
              (ExtendScalarsTensor.ringSheafMap α)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
            (((ExtendScalarsTensor.extendScalarsSheaf α).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K)) ⟶ Y =>
        DerivedCategory.Q.map (((ExtendScalarsTensor.adjunction α).mapHomologicalComplex
          (ComplexShape.up ℤ)).unit.app K) ≫ g)) :
    (derivedCompleteRestrictScalars α I).IsEquivalence := by
  refine isEquivalence_derivedCompleteRestrictScalars_of_flat α I ?_
  intro Y hY X
  obtain ⟨K, ⟨e⟩⟩ : ∃ K, Nonempty (DerivedCategory.Q.obj K ≅ X) :=
    ⟨_, ⟨DerivedCategory.Q.objObjPreimageIso X⟩⟩
  set adj := derivedExtendRestrictScalarsAdjunction α with hadj
  have hnat : adj.unit.app (DerivedCategory.Q.obj K) ≫
        ((ExtendScalarsTensor.extendScalarsSheaf α).mapDerivedCategory ⋙
          (_root_.SheafOfModules.restrictScalars.{u}
            (ringSheafHom (O := O) (O' := O') α)).mapDerivedCategory).map e.hom =
      e.hom ≫ adj.unit.app X :=
    (adj.unit.naturality e.hom).symm
  have hbase : Function.Bijective (fun g : (_root_.SheafOfModules.restrictScalars.{u}
      (ringSheafHom (O := O) (O' := O') α)).mapDerivedCategory.obj
        ((ExtendScalarsTensor.extendScalarsSheaf α).mapDerivedCategory.obj
          (DerivedCategory.Q.obj K)) ⟶ Y =>
      adj.unit.app (DerivedCategory.Q.obj K) ≫ g) :=
    CompleteRestrictScalarsEquivalence.bijective_precomp_derivedUnit
      (ExtendScalarsTensor.adjunction α) K Y (hK K Y hY)
  have hiso : Function.Bijective (fun g : (_root_.SheafOfModules.restrictScalars.{u}
      (ringSheafHom (O := O) (O' := O') α)).mapDerivedCategory.obj
        ((ExtendScalarsTensor.extendScalarsSheaf α).mapDerivedCategory.obj X) ⟶ Y =>
      ((ExtendScalarsTensor.extendScalarsSheaf α).mapDerivedCategory ⋙
        (_root_.SheafOfModules.restrictScalars.{u}
          (ringSheafHom (O := O) (O' := O') α)).mapDerivedCategory).map e.hom ≫ g) := by
    have : IsIso (((ExtendScalarsTensor.extendScalarsSheaf α).mapDerivedCategory ⋙
        (_root_.SheafOfModules.restrictScalars.{u}
          (ringSheafHom (O := O) (O' := O') α)).mapDerivedCategory).map e.hom) :=
      Functor.map_isIso _ e.hom
    exact (asIso (((ExtendScalarsTensor.extendScalarsSheaf α).mapDerivedCategory ⋙
      (_root_.SheafOfModules.restrictScalars.{u}
        (ringSheafHom (O := O) (O' := O') α)).mapDerivedCategory).map
          e.hom)).homFromEquiv.symm.bijective
  have hcomp : Function.Bijective (fun g : (_root_.SheafOfModules.restrictScalars.{u}
      (ringSheafHom (O := O) (O' := O') α)).mapDerivedCategory.obj
        ((ExtendScalarsTensor.extendScalarsSheaf α).mapDerivedCategory.obj X) ⟶ Y =>
      e.hom ≫ adj.unit.app X ≫ g) := by
    have h := hbase.comp hiso
    simp only [Function.comp_def] at h
    have h2 : ∀ g : (_root_.SheafOfModules.restrictScalars.{u}
        (ringSheafHom (O := O) (O' := O') α)).mapDerivedCategory.obj
          ((ExtendScalarsTensor.extendScalarsSheaf α).mapDerivedCategory.obj X) ⟶ Y,
        adj.unit.app (DerivedCategory.Q.obj K) ≫
            ((ExtendScalarsTensor.extendScalarsSheaf α).mapDerivedCategory ⋙
              (_root_.SheafOfModules.restrictScalars.{u}
                (ringSheafHom (O := O) (O' := O') α)).mapDerivedCategory).map e.hom ≫ g =
          e.hom ≫ adj.unit.app X ≫ g := fun g => by
      rw [← Category.assoc, hnat, Category.assoc]
    simpa only [h2] using h
  have hpre : Function.Bijective (fun g : X ⟶ Y => e.hom ≫ g) :=
    e.homFromEquiv.symm.bijective
  refine (Function.Bijective.of_comp_iff' hpre
    (fun g : (_root_.SheafOfModules.restrictScalars.{u}
      (ringSheafHom (O := O) (O' := O') α)).mapDerivedCategory.obj
        ((ExtendScalarsTensor.extendScalarsSheaf α).mapDerivedCategory.obj X) ⟶ Y =>
      adj.unit.app X ≫ g)).mp ?_
  simpa only [Function.comp_def] using hcomp

end Flat

end Stacks.SheafOfModules.DerivedRestrictScalars

end
