module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExt.PartBExt

/-!
# Relative `Ext` isomorphisms from a natural identification on `D^+_{QCoh}`

Let `g : U ⟶ S` be a morphism of schemes and `𝒢` a bounded complex on `U` flat over `S`, with
`Φ = Lg^*(-) ⊗^L 𝒢`. A natural identification `Hom(L, N) ≃+ Hom(E, Φ N)` for
`N ∈ D^+_{QCoh}(𝒪_S)` gives, for every quasi-coherent `ℱ` and every `i`,

`Ext^i_{𝒪_S}(L, ℱ) ≃+ Ext^i_{𝒪_U}(E, 𝒢 ⊗_{𝒪_U} g^*ℱ)`,

functorial in `ℱ` and compatible with the boundary maps of short exact sequences: the transport of
the identification to shifted morphisms, read through `Φ(ℱ[0]) ≅ 𝒢 ⊗ g^*ℱ`. This is the
construction of `Stacks.Cohomology.RelativeExt.partBExtIso` for an arbitrary identification; it
is how the base-change isomorphisms of [Stacks, Tag 0DJS] are read as isomorphisms of `Ext`-groups.

## Main definitions

* `Stacks.Cohomology.RelativeExtCanonical.extIsoOfIdentification`

## Main results

* `Stacks.Cohomology.RelativeExtCanonical.extIsoOfIdentification_naturality`
* `Stacks.Cohomology.RelativeExtCanonical.extIsoOfIdentification_boundary`
* `Stacks.Cohomology.RelativeExtCanonical.plusQCohDerived_biprod`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry

universe u

namespace Stacks.Cohomology.RelativeExtCanonical

open Stacks.Cohomology.RelativeExt

attribute [local instance] HasDerivedCategory.standard hasSheafifyOpensSpace
  wEqualsLocallyBijectiveOpensSpace

/-- `D^+_{QCoh}(𝒪_S)` is closed under binary biproducts. -/
theorem plusQCohDerived_biprod (S : Scheme.{u}) (N N' : DStd S) (hN : plusQCohDerived S N)
    (hN' : plusQCohDerived S N') : plusQCohDerived S (N ⊞ N') := by
  obtain ⟨hq, m, hm⟩ := hN
  obtain ⟨hq', m', hm'⟩ := hN'
  refine ⟨qcohDerived_biprod S N N' hq hq', min m m', ?_⟩
  rw [DerivedCategory.isGE_iff]
  intro i hi
  have := preservesBinaryBiproducts_of_preservesBiproducts
    (DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) i)
  refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor _ i).mapBiprod N N')
  exact (biprod_isZero_iff _ _).2
    ⟨DerivedCategory.isZero_of_isGE N m i (by omega),
      DerivedCategory.isZero_of_isGE N' m' i (by omega)⟩

variable {U S : Scheme.{u}} {g : U ⟶ S} {G : CochainComplex (TModules U.toRingedSpace) ℤ}
  {E : DStd U} {L : DStd S} (hG : IsBoundedFlatOver g.toLRSHom.toShHom G)
  (θ : ShiftedHom.NaturalHomIdentification (𝟭 (DStd S)) (pullbackTensorDerivedFunctor hG) L E
    (plusQCohDerived S))

/-- **`Ext^i_{𝒪_S}(L, ℱ) ≃+ Ext^i_{𝒪_U}(E, 𝒢 ⊗ g^*ℱ)`** for quasi-coherent `ℱ`, from a natural
identification on `D^+_{QCoh}(𝒪_S)`. -/
def extIsoOfIdentification (i : ℤ) (F : SheafOfModules.{u} (structureSheafRing S.toRingedSpace))
    (hF : F.IsQuasicoherent) : baseExtGroup L F i ≃+ relativeExtGroup g G E F i :=
  (@ShiftedHom.transport _ _ _ _ _ _ _ _ _ _ _ _ _ (Functor.CommShift.id _)
    (pullbackTensorDerivedFunctor_commShift hG) _ _ _ θ (plusQCohDerived_shift S) _
    (plusQCohDerived_single S F hF) i).trans
    (relativeExtTargetShiftIso hG F i)

/-- **The isomorphisms are functorial in `ℱ`.** -/
theorem extIsoOfIdentification_naturality (i : ℤ)
    {F F' : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)} (hF : F.IsQuasicoherent)
    (hF' : F'.IsQuasicoherent) (v : F ⟶ F') (z : baseExtGroup L F i) :
    extIsoOfIdentification hG θ i F' hF' (baseExtMap L i v z) =
      relativeExtMap g G E i v (extIsoOfIdentification hG θ i F hF z) := by
  have h1 := @ShiftedHom.transport_naturality _ _ _ _ _ _ _ _ _ _ _ _ _ (Functor.CommShift.id _)
    (pullbackTensorDerivedFunctor_commShift hG) _ _ _ θ (plusQCohDerived_shift S) _ _
    (plusQCohDerived_single S F hF) (plusQCohDerived_single S F' hF')
    ((DerivedCategory.singleFunctor _ 0).map v) i z
  have h2 := (relativeExtTargetIso hG).hom.naturality v
  have e : ((pullbackTensorDerivedFunctor hG).map
        ((DerivedCategory.singleFunctor _ 0).map v))⟦i⟧' ≫
        ((relativeExtTargetIso hG).hom.app F')⟦i⟧' =
      ((relativeExtTargetIso hG).hom.app F)⟦i⟧' ≫
        (DerivedCategory.Q.map ((relativeExtTargetFunctor g.toLRSHom.toShHom G).map v))⟦i⟧' :=
    ((shiftFunctor (DStd U) i).map_comp _ _).symm.trans
      ((congrArg (shiftFunctor (DStd U) i).map h2).trans ((shiftFunctor (DStd U) i).map_comp _ _))
  exact (congrArg (· ≫ ((relativeExtTargetIso hG).hom.app F')⟦i⟧') h1).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) e).trans (Category.assoc _ _ _).symm))

/-- **Transport commutes with connecting morphisms read through isomorphisms.** For a natural
identification `θ : Hom(a₁, N) ≃+ Hom(a₂, F N)` on a shift-stable class, a morphism
`δ : N₃ ⟶ N₁[1]`, and isomorphisms `F Nⱼ ≅ Zⱼ` carrying `F δ` to `δ'`, transporting `x ∘ δ` and
reading it in `Z₁` is reading the transport of `x` in `Z₃` and composing with `δ'`. -/
theorem transport_comp_conj {C : Type*} {D : Type*} [Category C] [Category D] [HasShift C ℤ]
    [HasShift D ℤ] [Preadditive C] [Preadditive D] {F : C ⥤ D} [hF : F.CommShift ℤ] {a₁ : C}
    {a₂ : D} {P : ObjectProperty C} (θ : ShiftedHom.NaturalHomIdentification (𝟭 C) F a₁ a₂ P)
    (hP : ∀ (N : C) (n : ℤ), P N → P (N⟦n⟧)) {N₃ N₁ : C} (h₃ : P N₃) (h₁ : P N₁)
    (δ : ShiftedHom N₃ N₁ (1 : ℤ)) {Z₃ Z₁ : D} (δ' : ShiftedHom Z₃ Z₁ (1 : ℤ))
    (e₃ : F.obj N₃ ≅ Z₃) (e₁ : F.obj N₁ ≅ Z₁) (hδ : δ.map F ≫ e₁.hom⟦(1 : ℤ)⟧' = e₃.hom ≫ δ')
    (n m : ℤ) (h : 1 + n = m) (x : ShiftedHom a₁ N₃ n) :
    ShiftedHom.transport θ hP N₁ h₁ m (x.comp δ h) ≫ e₁.hom⟦m⟧' =
      ShiftedHom.comp (ShiftedHom.transport θ hP N₃ h₃ n x ≫ e₃.hom⟦n⟧') δ' h := by
  have h1 := ShiftedHom.transport_comp_map θ hP h₃ h₁ δ n m h x
  rw [ShiftedHom.id_map] at h1
  rw [h1]
  exact ShiftedHom.comp_conj' _ _ δ' e₃ e₁ (ShiftedHom.conj_iso_symm _ _ _ _ hδ) h

/-- **The isomorphisms are compatible with the boundary maps** of a short exact sequence
`0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0` of quasi-coherent `𝒪_S`-modules. -/
theorem extIsoOfIdentification_boundary
    {A : ShortComplex (SheafOfModules.{u} (structureSheafRing S.toRingedSpace))}
    (hA : A.ShortExact) (h₁ : A.X₁.IsQuasicoherent) (h₃ : A.X₃.IsQuasicoherent) (n m : ℤ)
    (h : 1 + n = m) (z : baseExtGroup L A.X₃ n) :
    extIsoOfIdentification hG θ m A.X₁ h₁ (baseExtBoundaryMap L hA n m h z) =
      relativeExtBoundaryMap E hG hA n m h (extIsoOfIdentification hG θ n A.X₃ h₃ z) :=
  transport_comp_conj (hF := pullbackTensorDerivedFunctor_commShift hG) θ
    (plusQCohDerived_shift S) (plusQCohDerived_single S A.X₃ h₃)
    (plusQCohDerived_single S A.X₁ h₁) hA.singleδ (relativeExtBoundary hG hA)
    ((relativeExtTargetIso hG).app A.X₃) ((relativeExtTargetIso hG).app A.X₁)
    (map_singleδ_relativeExtTargetIso_shiftedHom hG hA) n m h z

/-- The truncations of an object of `D_{QCoh}(𝒪_S)` lie in `D^+_{QCoh}(𝒪_S)`. -/
theorem plusQCohDerived_truncGE {S : Scheme.{u}} (A : DStd S) (hA : qcohDerived S A) (n : ℤ) :
    plusQCohDerived S ((DerivedCategory.TStructure.t.truncGE n).obj A) :=
  ⟨qcohDerived_truncGE A hA n, n, inferInstance⟩

/-- An isomorphism `φ : L' ≅ L` carrying a natural identification `θ'` of `L'` to one `θ` of `L`
carries the induced `Ext`-isomorphisms of `L'` to those of `L`. -/
theorem extIsoOfIdentification_comp_of_iso {U S : Scheme.{u}} {g : U ⟶ S}
    {G : CochainComplex (TModules U.toRingedSpace) ℤ} {E : DStd U} {L L' : DStd S}
    (hG : IsBoundedFlatOver g.toLRSHom.toShHom G)
    (θ : ShiftedHom.NaturalHomEquiv (𝟭 (DStd S)) (pullbackTensorDerivedFunctor hG) L E
      (plusQCohDerived S))
    (θ' : ShiftedHom.NaturalHomEquiv (𝟭 (DStd S)) (pullbackTensorDerivedFunctor hG) L' E
      (plusQCohDerived S))
    (φ : L' ≅ L) (hφ : ∀ N (hN : plusQCohDerived S N) (x : L ⟶ N),
      θ'.equiv N hN (φ.hom ≫ x) = θ.equiv N hN x)
    (i : ℤ) (F : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) (hF : F.IsQuasicoherent)
    (z : baseExtGroup L F i) :
    extIsoOfIdentification hG (θ'.toIdentification (plusQCohDerived_biprod S)) i F hF
        (φ.hom ≫ z) =
      extIsoOfIdentification hG (θ.toIdentification (plusQCohDerived_biprod S)) i F hF z := by
  let : (pullbackTensorDerivedFunctor hG).CommShift ℤ := pullbackTensorDerivedFunctor_commShift hG
  have e := hφ _ (plusQCohDerived_shift S _ i (plusQCohDerived_single S F hF))
    (z ≫ ((𝟭 (DStd S)).commShiftIso i).inv.app ((DerivedCategory.singleFunctor _ 0).obj F))
  exact congrArg (fun w ↦ (w ≫ ((pullbackTensorDerivedFunctor hG).commShiftIso i).hom.app
      ((DerivedCategory.singleFunctor _ 0).obj F)) ≫ ((relativeExtTargetIso hG).hom.app F)⟦i⟧')
    ((congrArg (θ'.equiv _ _) (Category.assoc _ _ _)).trans e)

end Stacks.Cohomology.RelativeExtCanonical

end
