module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExt.PartBHocolim
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExt.PartAAssembly
public import StacksFrontier.CategoryTheory.Triangulated.SequentialPostnikovSystems

/-!
# The `Ext` isomorphisms of [Stacks, Tag 08IF] (B)

Let `L = hocolim Lₙ` be the homotopy colimit of the system of
`Stacks.Cohomology.RelativeExt.partBSystem` and `η : E ⟶ Φ(L)` the glued unit, which identifies
`Hom(L, N)` with `Hom(E, Φ N)` for `N ∈ D^+_QCoh(𝒪_S)`. Transported to shifted morphisms and
read through `Φ(ℱ[0]) ≅ 𝒢 ⊗ g^*ℱ`, this gives isomorphisms

`Ext^i_{𝒪_S}(L, ℱ) ≅ Ext^i_{𝒪_U}(E, 𝒢 ⊗ g^*ℱ)`

for quasi-coherent `ℱ`, functorial in `ℱ` and compatible with the boundary maps. Over an open
immersion `j : U ⟶ X` for which restriction of the relative `Ext` groups is bijective, they give
the isomorphisms of [Stacks, Tag 08IF] (B) on `X`.

## Main definitions

* `Stacks.Cohomology.RelativeExt.baseExtGroup`: `Ext^i_{𝒪_S}(L, ℱ)`, with its functoriality
  `baseExtMap` and boundary maps `baseExtBoundaryMap`.
* `Stacks.Cohomology.RelativeExt.plusQCohDerived`: `D^+_QCoh(𝒪_S)`.

## Main results

* `Stacks.Cohomology.RelativeExt.exists_relativeExtIso_of_open`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry

universe u

namespace Stacks.Cohomology.RelativeExt

attribute [local instance] HasDerivedCategory.standard hasSheafifyOpensSpace
  wEqualsLocallyBijectiveOpensSpace

section Maps

variable {S : Scheme.{u}} (L : DStd S)

/-- **`Ext^i_{𝒪_S}(L, ℱ)`**, for an object `L` of `D(𝒪_S)` and an `𝒪_S`-module `ℱ`. -/
abbrev baseExtGroup (F : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) (i : ℤ) :=
  DerivedCategory.Ext L ((DerivedCategory.singleFunctor _ 0).obj F) i

/-- **Functoriality of `Ext^i_{𝒪_S}(L, ℱ)` in `ℱ`.** -/
def baseExtMap (i : ℤ) {F F' : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)}
    (v : F ⟶ F') : baseExtGroup L F i →+ baseExtGroup L F' i where
  toFun z := z ≫ ((DerivedCategory.singleFunctor _ 0).map v)⟦i⟧'
  map_zero' := zero_comp
  map_add' _ _ := Preadditive.add_comp _ _ _ _ _ _

/-- **The boundary map `Ext^n_{𝒪_S}(L, ℱ₃) ⟶ Ext^m_{𝒪_S}(L, ℱ₁)`**, `1 + n = m`, of a short exact
sequence `0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0`: composition with its connecting morphism `ℱ₃ ⟶ ℱ₁[1]`. -/
def baseExtBoundaryMap
    {A : ShortComplex (SheafOfModules.{u} (structureSheafRing S.toRingedSpace))}
    (hA : A.ShortExact) (n m : ℤ) (h : 1 + n = m) :
    baseExtGroup L A.X₃ n → baseExtGroup L A.X₁ m :=
  fun z => z.comp hA.singleδ h

/-- **`D^+_QCoh(𝒪_S)`**: objects with quasi-coherent cohomology, bounded below. -/
def plusQCohDerived (S : Scheme.{u}) : ObjectProperty (DStd S) :=
  fun N => qcohDerived S N ∧ ∃ m : ℤ, N.IsGE m

/-- `D^+_QCoh(𝒪_S)` is stable under shifts: if `N` lies in it, so does `N[n]`. -/
theorem plusQCohDerived_shift (S : Scheme.{u}) (N : DStd S) (n : ℤ)
    (hN : plusQCohDerived S N) : plusQCohDerived S (N⟦n⟧) := by
  obtain ⟨hq, m, hm⟩ := hN
  have := hm
  exact ⟨qcohDerived_shift S N n hq, m - n,
    DerivedCategory.TStructure.t.isGE_shift N m n (m - n) (by omega)⟩

/-- For a quasi-coherent `𝒪_S`-module `ℱ`, the complex `ℱ[0]` lies in `D^+_QCoh(𝒪_S)`. -/
theorem plusQCohDerived_single (S : Scheme.{u})
    (F : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) (hF : F.IsQuasicoherent) :
    plusQCohDerived S ((DerivedCategory.singleFunctor _ 0).obj F) :=
  ⟨qcohDerived_single S F hF, 0, inferInstance⟩

end Maps

section Stage

variable {U S : Scheme.{u}} {g : U ⟶ S} {G : CochainComplex (TModules U.toRingedSpace) ℤ}
  {E : DStd U} (D : PartBApproxSystem g G E) (hG : IsBoundedFlatOver g.toLRSHom.toShHom G)
  {L : DStd S} {d : ∀ n, (partBSystem D).obj n ⟶ L} (b : ℤ) (hb : G.IsStrictlyGE b)
  [∀ i : ℤ, HasColimit (partBSystem D ⋙ DerivedCategory.homologyFunctor (SheafOfModules.{u}
      (structureSheafRing S.toRingedSpace)) i)]
  (hcolim : PartBHomologyColimit D L d) (η : E ⟶ (partBΦ hG).obj L)
  (hη : ∀ n, D.c n ≫ η = partBUnit D hG n ≫ (partBΦ hG).map (d n))

include hb hcolim hη in
/-- **`Hom(L, N) ≃+ Hom(E, Φ N)`**, `ψ ↦ η ≫ Φ(ψ)`, naturally in `N ∈ D^+_QCoh(𝒪_S)`. -/
def partBTheta :
    ShiftedHom.NaturalHomIdentification (𝟭 (DStd S)) (partBΦ hG) L E (plusQCohDerived S) where
  equiv N hN := AddEquiv.ofBijective
    (AddMonoidHom.mk' (fun ψ : L ⟶ N => η ≫ (partBΦ hG).map ψ) fun ψ ψ' => by
      change η ≫ (partBΦ hG).map (ψ + ψ') = η ≫ (partBΦ hG).map ψ + η ≫ (partBΦ hG).map ψ'
      rw [Functor.map_add, Preadditive.comp_add])
    (bijective_partBHocolimUnit_comp D hG b hb hcolim η hη N hN.1 hN.2.choose
      hN.2.choose_spec)
  naturality {N N'} _ _ k ψ := by
    change η ≫ (partBΦ hG).map (ψ ≫ k) = (η ≫ (partBΦ hG).map ψ) ≫ (partBΦ hG).map k
    rw [CategoryTheory.Functor.map_comp, Category.assoc]

/-- Composition with `Φ(ℱ[0])[i] ≅ (𝒢 ⊗ g^*ℱ)[i]`. -/
def relativeExtTargetShiftIso (F : SheafOfModules.{u} (structureSheafRing S.toRingedSpace))
    (i : ℤ) :
    ShiftedHom E ((partBΦ hG).obj ((DerivedCategory.singleFunctor _ 0).obj F)) i ≃+
      relativeExtGroup g G E F i :=
  let e := (shiftFunctor (DStd U) i).mapIso ((relativeExtTargetIso hG).app F)
  { toFun := fun z => z ≫ e.hom
    invFun := fun z => z ≫ e.inv
    left_inv := fun z => (Category.assoc _ _ _).trans ((congrArg (z ≫ ·) e.hom_inv_id).trans
      (Category.comp_id z))
    right_inv := fun z => (Category.assoc _ _ _).trans ((congrArg (z ≫ ·) e.inv_hom_id).trans
      (Category.comp_id z))
    map_add' := fun z z' => Preadditive.add_comp _ _ _ z z' e.hom }

include hb hcolim hη in
/-- **`Ext^i_{𝒪_S}(L, ℱ) ≃+ Ext^i_{𝒪_U}(E, 𝒢 ⊗ g^*ℱ)`** for quasi-coherent `ℱ`: the transport
of `partBTheta` to shifted morphisms, read through `Φ(ℱ[0]) ≅ 𝒢 ⊗ g^*ℱ`. -/
def partBExtIso (i : ℤ) (F : SheafOfModules.{u} (structureSheafRing S.toRingedSpace))
    (hF : F.IsQuasicoherent) : baseExtGroup L F i ≃+ relativeExtGroup g G E F i :=
  (@ShiftedHom.transport _ _ _ _ _ _ _ _ _ _ _ _ _ (Functor.CommShift.id _)
    (pullbackTensorDerivedFunctor_commShift hG) _ _ _
    (partBTheta (D := D) (hG := hG) (b := b) (hb := hb) (hcolim := hcolim)
      (η := η) (hη := hη)) (plusQCohDerived_shift S) _
    (plusQCohDerived_single S F hF) i).trans
    (relativeExtTargetShiftIso hG F i)

include hb hcolim hη in
/-- **The isomorphisms are functorial in `ℱ`.** -/
theorem partBExtIso_naturality (i : ℤ)
    {F F' : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)} (hF : F.IsQuasicoherent)
    (hF' : F'.IsQuasicoherent) (v : F ⟶ F') (z : baseExtGroup L F i) :
    partBExtIso D hG b hb hcolim η hη i F' hF' (baseExtMap L i v z) =
      relativeExtMap g G E i v (partBExtIso D hG b hb hcolim η hη i F hF z) := by
  have h1 := @ShiftedHom.transport_naturality _ _ _ _ _ _ _ _ _ _ _ _ _ (Functor.CommShift.id _)
    (pullbackTensorDerivedFunctor_commShift hG) _ _ _
    (partBTheta D hG b hb hcolim η hη) (plusQCohDerived_shift S) _ _
    (plusQCohDerived_single S F hF)
    (plusQCohDerived_single S F' hF') ((DerivedCategory.singleFunctor _ 0).map v) i z
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

/-- Inverting the isomorphisms in a square of connecting morphisms. -/
theorem _root_.CategoryTheory.ShiftedHom.conj_iso_symm {C : Type*} [Category C] [HasShift C ℤ]
    {Y₃ Y₁ Z₃ Z₁ : C} (δ : ShiftedHom Y₃ Y₁ (1 : ℤ)) (δ' : ShiftedHom Z₃ Z₁ (1 : ℤ))
    (e₃ : Y₃ ≅ Z₃) (e₁ : Y₁ ≅ Z₁) (h : δ ≫ e₁.hom⟦(1 : ℤ)⟧' = e₃.hom ≫ δ') :
    δ' ≫ e₁.inv⟦(1 : ℤ)⟧' = e₃.inv ≫ δ := by
  rw [← cancel_epi e₃.hom, Iso.hom_inv_id_assoc, ← reassoc_of% h,
    ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
    Category.comp_id]

include hb hcolim hη in
/-- **The isomorphisms are compatible with the boundary maps** of a short exact sequence
`0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0` of quasi-coherent `𝒪_S`-modules. -/
theorem partBExtIso_boundary
    {A : ShortComplex (SheafOfModules.{u} (structureSheafRing S.toRingedSpace))}
    (hA : A.ShortExact) (h₁ : A.X₁.IsQuasicoherent) (h₃ : A.X₃.IsQuasicoherent) (n m : ℤ)
    (h : 1 + n = m) (z : baseExtGroup L A.X₃ n) :
    partBExtIso D hG b hb hcolim η hη m A.X₁ h₁ (baseExtBoundaryMap L hA n m h z) =
      relativeExtBoundaryMap E hG hA n m h (partBExtIso D hG b hb hcolim η hη n A.X₃ h₃ z) := by
  have h1 := @ShiftedHom.transport_comp_map _ _ _ _ _ _ _ _ _ _ _ _ _ (Functor.CommShift.id _)
    (pullbackTensorDerivedFunctor_commShift hG) _ _ _
    (partBTheta D hG b hb hcolim η hη) (plusQCohDerived_shift S) _ _
    (plusQCohDerived_single S A.X₃ h₃)
    (plusQCohDerived_single S A.X₁ h₁) hA.singleδ n m h z
  rw [ShiftedHom.id_map] at h1
  have hδ2 := map_singleδ_relativeExtTargetIso_shiftedHom hG hA
  exact (congrArg (· ≫ ((relativeExtTargetIso hG).hom.app A.X₁)⟦m⟧') h1).trans
    (ShiftedHom.comp_conj' _ _ (relativeExtBoundary hG hA)
      ((relativeExtTargetIso hG).app A.X₃) ((relativeExtTargetIso hG).app A.X₁)
      (ShiftedHom.conj_iso_symm _ _ _ _ hδ2) h)

include hG hb hcolim in
/-- **The coprojections `dₙ` are isomorphisms on cohomology in any range of degrees bounded below
for `n` large**: the input of [Stacks, Tag 0DJN] (2) ⟹ (1) that makes `L` pseudo-coherent. -/
theorem exists_isIso_homology_partBCoprojection (m : ℤ) :
    ∃ n : ℕ, ∀ i : ℤ, m ≤ i → IsIso ((DerivedCategory.homologyFunctor _ i).map (d n)) := by
  refine ⟨(-m - b).toNat, fun i hi => ?_⟩
  have := Int.self_le_toNat (-m - b)
  exact (isIso_truncGE_map_iff_isIso_homology (d _) m).1
    (isIso_truncGE_partBCoprojection D hG b hb hcolim _ m (by omega)) i hi

end Stage

/-- **`L ∈ D(𝒪_S)` is pseudo-coherent**, in the sense of [Stacks, Tag 08FT]. -/
abbrev IsPseudoCoherentObject {S : Scheme.{u}} (L : DStd S) : Prop :=
  RingedSpace.IsPseudoCoherent (X := S.toRingedSpace) L

/-- **The system of `PartBApproxSystem` has a homotopy colimit**, with coprojections. -/
theorem exists_isHomotopyColimitWith_partBSystem {U S : Scheme.{u}} {g : U ⟶ S}
    {G : CochainComplex (TModules U.toRingedSpace) ℤ} {E : DStd U} (D : PartBApproxSystem g G E)
    [HasCoproduct (partBSystem D).obj] :
    ∃ (L : DStd S) (d : ∀ n, (partBSystem D).obj n ⟶ L),
      IsHomotopyColimitWith (partBSystem D) L d := by
  obtain ⟨L, hL⟩ := CategoryTheory.Triangulated.exists_isHomotopyColimit (partBSystem D)
  obtain ⟨d, hd⟩ := hL.exists_isHomotopyColimitWith
  exact ⟨L, d, hd⟩

section Open

variable {X U S : Scheme.{u}} (f : X ⟶ S) (j : U ⟶ X) [IsOpenImmersion j]
  {G : CochainComplex (TModules X.toRingedSpace) ℤ} (hG : IsBoundedFlatOver f.toLRSHom.toShHom G)
  (E : DStd X)
  (D : PartBApproxSystem (j ≫ f) (restrictComplex j G) ((restrictDerived j).obj E))
  (b : ℤ) (hb : G.IsStrictlyGE b) {L : DStd S} {d : ∀ n, (partBSystem D).obj n ⟶ L}
  [∀ i : ℤ, HasColimit (partBSystem D ⋙ DerivedCategory.homologyFunctor (SheafOfModules.{u}
    (structureSheafRing S.toRingedSpace)) i)]
  (hcolim : PartBHomologyColimit D L d)
  (hres : ∀ (F : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) (i : ℤ),
    Function.Bijective (restrictRelativeExt f j G E F i))
  (η : (restrictDerived j).obj E ⟶
    (partBΦ (isBoundedFlatOver_restrictComplex (f := f) (j := j) hG)).obj L)
  (hη : ∀ n, D.c n ≫ η = partBUnit D (isBoundedFlatOver_restrictComplex (f := f) (j := j) hG) n ≫
    (partBΦ (isBoundedFlatOver_restrictComplex (f := f) (j := j) hG)).map (d n))

/-- **The isomorphisms of [Stacks, Tag 08IF] (B), from a system on an open.** Let `j : U ⟶ X` be
an open immersion such that restriction to `U` is bijective on the relative `Ext` groups, `𝒢`
living in degrees `≥ b`, `D` the data of `PartBApproxSystem` for `E|_U` and `𝒢|_U` over `S`,
`L = hocolim Lₙ` the homotopy colimit of its system, whose cohomology is the colimit of that of
the `Lₙ`, and `η : E|_U ⟶ Φ(L)` the glued unit. Then
`Ext^i_{𝒪_S}(L, ℱ) ≃+ Ext^i_{𝒪_U}(E|_U, 𝒢|_U ⊗ (f|_U)^*ℱ) ≃+ Ext^i_{𝒪_X}(E, 𝒢 ⊗ f^*ℱ)`, the first
isomorphism `partBExtIso`, the second the inverse of restriction. -/
def relativeExtIsoOfOpen (i : ℤ) (F : SheafOfModules.{u} (structureSheafRing S.toRingedSpace))
    (hF : F.IsQuasicoherent) : baseExtGroup L F i ≃+ relativeExtGroup f G E F i :=
  (partBExtIso D (isBoundedFlatOver_restrictComplex (f := f) (j := j) hG) b
    (isStrictlyGE_restrictComplex (j := j) b hb) hcolim η hη i F hF).trans
    (AddEquiv.ofBijective (restrictRelativeExt f j G E F i) (hres F i)).symm

/-- Restricting `relativeExtIsoOfOpen` to `U` gives `partBExtIso`. -/
theorem restrictRelativeExt_relativeExtIsoOfOpen (i : ℤ)
    (F : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) (hF : F.IsQuasicoherent)
    (z : baseExtGroup L F i) :
    restrictRelativeExt f j G E F i
        (relativeExtIsoOfOpen f j hG E D b hb hcolim hres η hη i F hF z) =
      partBExtIso D (isBoundedFlatOver_restrictComplex (f := f) (j := j) hG) b
        (isStrictlyGE_restrictComplex (j := j) b hb) hcolim η hη i F hF z :=
  (AddEquiv.ofBijective (restrictRelativeExt f j G E F i) (hres F i)).apply_symm_apply _

/-- `relativeExtIsoOfOpen` is natural in the quasi-coherent module `ℱ`: it intertwines
`baseExtMap` and `relativeExtMap`. -/
theorem relativeExtIsoOfOpen_naturality (i : ℤ)
    {F F' : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)} (hF : F.IsQuasicoherent)
    (hF' : F'.IsQuasicoherent) (v : F ⟶ F') (z : baseExtGroup L F i) :
    relativeExtIsoOfOpen f j hG E D b hb hcolim hres η hη i F' hF' (baseExtMap L i v z) =
      relativeExtMap f G E i v
        (relativeExtIsoOfOpen f j hG E D b hb hcolim hres η hη i F hF z) := by
  apply (hres F' i).1
  rw [restrictRelativeExt_relativeExtIsoOfOpen]
  change _ = restrictRelativeExt f j G E F' i (_ ≫ _)
  rw [restrictRelativeExt_naturality, restrictRelativeExt_relativeExtIsoOfOpen]
  exact partBExtIso_naturality D _ b _ hcolim η hη i hF hF' v z

include hG in
/-- `relativeExtIsoOfOpen` is compatible with the boundary maps of a short exact sequence
`0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0` with `ℱ₁` and `ℱ₃` quasi-coherent: it intertwines
`baseExtBoundaryMap` and `relativeExtBoundaryMap`. -/
theorem relativeExtIsoOfOpen_boundary
    {A : ShortComplex (SheafOfModules.{u} (structureSheafRing S.toRingedSpace))}
    (hA : A.ShortExact) (h₁ : A.X₁.IsQuasicoherent) (h₃ : A.X₃.IsQuasicoherent) (n m : ℤ)
    (h : 1 + n = m) (z : baseExtGroup L A.X₃ n) :
    relativeExtIsoOfOpen f j hG E D b hb hcolim hres η hη m A.X₁ h₁
        (baseExtBoundaryMap L hA n m h z) =
      relativeExtBoundaryMap E hG hA n m h
        (relativeExtIsoOfOpen f j hG E D b hb hcolim hres η hη n A.X₃ h₃ z) := by
  apply (hres A.X₁ m).1
  rw [restrictRelativeExt_relativeExtIsoOfOpen]
  change _ = restrictRelativeExt f j G E A.X₁ m (ShiftedHom.comp _ _ h)
  rw [restrictRelativeExt_boundary f j hG E hA n m h, restrictRelativeExt_relativeExtIsoOfOpen]
  exact partBExtIso_boundary D _ b _ hcolim η hη hA h₁ h₃ n m h z

end Open

end Stacks.Cohomology.RelativeExt

end
