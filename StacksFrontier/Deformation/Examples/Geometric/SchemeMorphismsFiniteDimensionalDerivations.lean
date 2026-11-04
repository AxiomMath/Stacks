module

public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismSequenceTerms
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.ExtFinitenessUnconditional
public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.ChowStalk
public import StacksFrontier.AlgebraicGeometry.DeRham.CoherentDirectImage
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.CotangentSheafComparison
public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType

/-!
# Finite dimensionality of `Der_k(𝒪_Y, f_*𝒪_X)` for a morphism of proper schemes

Let `f : X → Y` be a morphism of schemes over a field `k`. The third term of the exact sequence
of [Stacks Project, Tag 0E3V] is the `k`-vector space `Der_k(𝒪_Y, f_*𝒪_X)`. This file proves that
it is finite dimensional when `f` is proper and `Y` is proper over `k`; in particular when `X`
and `Y` are both proper over `k`, which is the situation of [Stacks Project, Tag 0E3W].

The argument: `Der_k(𝒪_Y, f_*𝒪_X) = Hom_{𝒪_Y}(Ω_{Y/k}, f_*𝒪_X)` by the corepresentability of
derivations ([Stacks Project, Tag 04BL]); `Ω_{Y/k}` is coherent ([Stacks Project, Tag 01V2] and
[Stacks Project, Tag 01XZ]) and so is `f_*𝒪_X` ([Stacks Project, Tag 02O5]); and the group of
`𝒪_Y`-module maps between two coherent modules embeds `k`-linearly into
`Ext⁰_{𝒪_Y}(Ω_{Y/k}, f_*𝒪_X)`, which is finite dimensional by [Stacks Project, Tag 0D0D].

At `f = 𝟙 X` the space is `Der_k(𝒪_X, 𝒪_X)`, the infinitesimal automorphisms of the deformation
category of `X` ([Stacks Project, Tag 0DY9]).

## Main results

* `Deformation.Examples.derivedCategoryBBounded_singleFunctor_isCoherent`: a coherent module
  placed in degree zero lies in `D^b_Coh`.
* `Deformation.Examples.finiteDimensional_hom_of_isCoherent_of_isProper`: on a scheme proper
  over a field, the `k`-vector space of maps between two coherent modules is finite dimensional.
* `Deformation.Examples.finiteDimensional_schemeMorphismDerivations`: `Der_k(𝒪_Y, f_*𝒪_X)` is
  finite dimensional for `f` proper and `Y` proper over `k`.

## References

* [Stacks Project, Tag 0E3V](https://stacks.math.columbia.edu/tag/0E3V)
* [Stacks Project, Tag 0E3W](https://stacks.math.columbia.edu/tag/0E3W)
* [Stacks Project, Tag 0D0D](https://stacks.math.columbia.edu/tag/0D0D)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Deformation.Examples

/-- **A coherent module placed in cohomological degree zero lies in `D^b_Coh(𝒪_Z)`**, for any
model of the derived category: its cohomology is the module itself in degree zero and zero in
every other degree. -/
theorem derivedCategoryBBounded_singleFunctor_isCoherent (Z : Scheme.{u})
    [HasDerivedCategory Z.Modules] (F : Z.Modules) (hF : F.IsCoherent) :
    DerivedCategoryB.derivedCategoryBBounded (fun M : Z.Modules => M.IsCoherent)
      ((DerivedCategory.singleFunctor Z.Modules 0).obj F) := by
  have e : ∀ i : ℤ, (DerivedCategory.homologyFunctor Z.Modules i).obj
      ((DerivedCategory.singleFunctor Z.Modules 0).obj F) ≅
      ((CochainComplex.singleFunctor Z.Modules 0).obj F).homology i :=
    fun i => (DerivedCategory.homologyFunctorFactors Z.Modules i).app _
  have hzero : ∀ i : ℤ, i ≠ 0 → IsZero
      ((DerivedCategory.homologyFunctor Z.Modules i).obj
        ((DerivedCategory.singleFunctor Z.Modules 0).obj F)) :=
    fun i hi => (HomologicalComplex.isZero_single_obj_homology _ _ _ _ hi).of_iso (e i)
  refine ⟨⟨⟨0, fun n hn => hzero n (by omega)⟩, ⟨0, fun n hn => hzero n (by omega)⟩⟩,
    fun n => ?_⟩
  by_cases hn : n = 0
  · subst hn
    exact Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso
      (e 0 ≪≫ HomologicalComplex.singleObjHomologySelfIso _ _ _)
  · exact ProperCoherentFiniteType.isCoherent_of_isZero (hzero n hn)

/-- **On a scheme proper over a field `k`, the maps between two coherent modules form a finite
dimensional `k`-vector space**, for the `k`-structure `AlgebraicGeometry.modulesLinear` induced
by the structure morphism. Placing the modules in degree zero embeds `Hom(F, G)` `k`-linearly
into `Ext⁰(F, G)`, which is finite dimensional by [Stacks Project, Tag 0D0D]. -/
theorem finiteDimensional_hom_of_isCoherent_of_isProper {k : Type u} [Field k]
    (Z : Over (Spec (CommRingCat.of k))) [IsProper Z.hom] (F G : Z.left.Modules)
    (hF : F.IsCoherent) (hG : G.IsCoherent) :
    letI : Module k (F ⟶ G) := (modulesLinear k Z).homModule F G
    FiniteDimensional k (F ⟶ G) := by
  let : Linear k Z.left.Modules := modulesLinear k Z
  let : HasDerivedCategory Z.left.Modules := HasDerivedCategory.standard _
  have hFb := derivedCategoryBBounded_singleFunctor_isCoherent Z.left F hF
  have hGb := derivedCategoryBBounded_singleFunctor_isCoherent Z.left G hG
  have hfin := Stacks.AlgebraicGeometry.ProperSupportCoherent.moduleFinite_ext_of_proper Z
    ((DerivedCategory.singleFunctor Z.left.Modules 0).obj F)
    ((DerivedCategory.singleFunctor Z.left.Modules 0).obj G) ⟨hFb.1.2, hFb.2⟩
    ⟨hGb.1.1, hGb.2⟩ 0
  let φ : (F ⟶ G) →ₗ[k] DerivedCategory.Ext ((DerivedCategory.singleFunctor Z.left.Modules 0).obj F)
      ((DerivedCategory.singleFunctor Z.left.Modules 0).obj G) 0 :=
    { toFun := fun g => ShiftedHom.mk₀ (0 : ℤ) rfl ((DerivedCategory.singleFunctor _ 0).map g)
      map_add' := fun a b => by
        rw [Functor.map_add, ShiftedHom.mk₀_add]
      map_smul' := fun c a => by
        rw [Functor.map_smul, ShiftedHom.mk₀_smul, RingHom.id_apply] }
  exact Module.Finite.of_injective φ fun a b hab =>
    (DerivedCategory.singleFunctor Z.left.Modules 0).map_injective
      ((ShiftedHom.homEquiv (0 : ℤ) rfl).injective hab)

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (pY : Y ⟶ baseSpec (residueFieldBase Λ k))

/-- **`Der_k(𝒪_Y, f_*𝒪_X)` is finite dimensional when `f` is proper and `Y` is proper over `k`.**
It is `Hom_{𝒪_Y}(Ω_{Y/k}, f_*𝒪_X)` (`schemeMorphismDerivationsLinearEquiv`, read through the
comparison `Scheme.Hom.cotangentSheafIso` of the two sheaves of relative differentials), `Ω_{Y/k}`
is coherent because `Y` is of finite type over the field `k`, `f_*𝒪_X` is coherent by
[Stacks Project, Tag 02O5], and maps between coherent modules on the proper `k`-scheme `Y` form
a finite dimensional space by [Stacks Project, Tag 0D0D]. -/
theorem finiteDimensional_schemeMorphismDerivations [IsProper f] [IsProper pY] :
    letI := schemeMorphismDerivationsModule f pY
      (SheafOfModules.unit (structureSheafRing X.toRingedSpace))
    FiniteDimensional k (schemeMorphismDerivations f pY) := by
  let := schemeMorphismDerivationsModule f pY
    (SheafOfModules.unit (structureSheafRing X.toRingedSpace))
  let Z : Over (Spec (CommRingCat.of k)) := Over.mk pY
  have : IsProper Z.hom := ‹IsProper pY›
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian pY
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (f ≫ pY)
  have : (SheafOfModules.unit X.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit
  have hG : ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)).IsCoherent :=
    ProperCoherenceWitness.isCoherent_pushforward f _
  have hF : (Scheme.Hom.relativeDifferentials pY).IsCoherent :=
    Scheme.Hom.isCoherent_relativeDifferentials pY
  let : Module k (Scheme.Hom.relativeDifferentials pY ⟶
      (Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) :=
    (modulesLinear k Z).homModule _ _
  have := finiteDimensional_hom_of_isCoherent_of_isProper Z _ _ hF hG
  let : Module k (Stacks.Sheaves.RingedSpaceDifferentials.moduleOfDifferentials
      pY.toLRSHom.toShHom ⟶ schemeMorphismPushforwardStructureSheaf f) :=
    (modulesLinear k (Over.mk pY)).homModule _ _
  let : Linear k Y.Modules := modulesLinear k Z
  let e₁ : (Scheme.Hom.relativeDifferentials pY ⟶
      (Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) ≃ₗ[k]
      (Stacks.Smooth.cotangentSheaf pY ⟶
        (Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) :=
    Linear.homCongr k (Scheme.Hom.cotangentSheafIso pY) (Iso.refl _)
  exact Module.Finite.equiv (e₁.trans (schemeMorphismDerivationsLinearEquiv f pY
    (SheafOfModules.unit (structureSheafRing X.toRingedSpace))).symm)

end Deformation.Examples

end
