module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PullbackUnitTransportComp
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafPullbackUnitSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackUnitTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.ReprFpqcFullness
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.RepresentedC3TensorCompatProof

/-!
# Stacks 03LU read on the chart: the pieces of the unit compatibility

Let `g : V ⟶ U` be a morphism of the big fppf site over `S`.  The compatibility
`AlgebraicGeometry.Space.RepresentedC3UnitCompat` of the identification
`(𝒪_U)_{yoneda U} ≅ 𝒪_{yoneda U}` of Stacks 03DX (2) with inverse images is checked on the scheme
underlying `V`, where every factor is read through the base identification of Stacks 03DX (2).
This file proves the readings of the factors: Stacks 03LU for the Zariski morphism of ringed
topoi of a morphism of schemes is Stacks 03LU for the morphism of ringed spaces; Stacks 03LU round
the square of a morphism of schemes between étale and Zariski sites, read through
`AlgebraicGeometry.SmallEtale.restrictModulePullbackObjIso`; Stacks 03LU round the square of `g`,
read through the units of the comparisons of Stacks 04M0; and the reading of the identification
itself.

## Main results

* `AlgebraicGeometry.Scheme.Hom.pullbackUnitIsoTransport_zariskiPullbackModulesIso_hom`: Stacks
  03LU for the Zariski morphism of ringed topoi is the ringed-space comparison.
* `AlgebraicGeometry.SmallEtale.restrictModulePullbackObjIso_pullbackUnitIsoTransport`: the
  étale--Zariski square, read through `restrictModulePullbackObjIso`.
* `AlgebraicGeometry.Space.representedSquare_pullbackUnitIsoTransport_unit`: the square of `g`,
  read through the units of the comparisons of Stacks 04M0.
* `AlgebraicGeometry.Space.representedZariski_map_representedQuasicoherentSchemeUnitIso`: the
  reading of the identification `(𝒪_U)_{yoneda U} ≅ 𝒪_{yoneda U}` on the scheme underlying `U`.
* `pullbackUnitIsoTransport_pullbackModulesReindexIso_eq_representedReindexPullbackIso`, in
  `AlgebraicGeometry.Space`: the two readings of Stacks 03LU at the reindexing agree.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (r : X ⟶ Y)

/-- **Stacks 03LU for the Zariski morphism of ringed topoi of a morphism of schemes is Stacks 03LU
for the morphism of ringed spaces.** -/
theorem pullbackUnitIsoTransport_zariskiPullbackModulesIso_hom :
    (Stacks.SheafOfModules.pullbackUnitIsoTransport r.zariskiRingedToposModulesHom
      r.zariskiPullbackModulesIso).hom =
    (Stacks.PullbackAlgebra.pullbackUnitIso r.toLRSHom.toShHom).hom := by
  refine ((Stacks.RingedSpace.pullbackAdjunction r.toLRSHom.toShHom).homEquiv _ _).injective ?_
  refine (SheafOfModules.unitHomEquiv _).injective (Subtype.ext (funext fun W => ?_))
  have h1 := r.zariskiPullbackAdjunction_transpose_val_app _ _
    (Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso
      r.zariskiRingedToposModulesHom).inv W
    (1 : (Stacks.SheafOfModules.Tensor.ringSheaf Y.zariskiRingedSite.toRingedTopos.O).obj.obj W)
  have h2 := Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso_inv_adjunct_val_app_one
    r.zariskiRingedToposModulesHom W
  rw [Adjunction.homEquiv_unit] at h2
  have h3 := Stacks.PullbackAlgebra.pullbackUnitIso_hom_pullbackUnit r.toLRSHom.toShHom W 1
  have h4 := congrArg (fun φ => (SheafOfModules.unitHomEquiv _ φ).val W)
    ((Stacks.RingedSpace.pullbackAdjunction r.toLRSHom.toShHom).homEquiv_unit _ _
      (Stacks.PullbackAlgebra.pullbackUnitIso r.toLRSHom.toShHom).hom)
  refine h1.symm.trans (h2.trans ?_)
  have hsharp : Stacks.RingedSpace.sharp r.toLRSHom.toShHom W
        (1 : (Stacks.RingedSpace.structureRingSheaf Y.toSheafedSpace).obj.obj W) =
      (1 : (Stacks.RingedSpace.structureRingSheaf X.toSheafedSpace).obj.obj
        ((RingedSpaceModuleAdjunction.opensMap r.toLRSHom.toShHom).op.obj W)) := map_one _
  exact (h4.trans (h3.trans hsharp)).symm

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Space

section Abstract

variable {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']

/-- A square `L' b ≫ p' = θ_O ≫ Q p ≫ q` read through the units of two adjunctions, against a
morphism `c` whose transpose is `θ` followed by `Q` of the counit. -/
private theorem unit_comp_map_of_comp_counit {L : D ⥤ C} {R : C ⥤ D} (adj : L ⊣ R)
    {L' : D' ⥤ C'} {R' : C' ⥤ D'} (adj' : L' ⊣ R') (P : D ⥤ D') (Q : C ⥤ C')
    (θ : P ⋙ L' ⟶ L ⋙ Q) {O : D} {A : C} {O' : D'} {A' : C'} (p : L.obj O ⟶ A)
    (p' : L'.obj O' ⟶ A') (q : Q.obj A ⟶ A') (b₀ b : P.obj O ⟶ O')
    (c : P.obj (R.obj A) ⟶ R'.obj (Q.obj A))
    (hc : L'.map c ≫ adj'.counit.app (Q.obj A) = θ.app (R.obj A) ≫ Q.map (adj.counit.app A))
    (h : L'.map b₀ ≫ p' = θ.app O ≫ Q.map p ≫ q) (hb : b₀ = b) :
    P.map (adj.unit.app O ≫ R.map p) ≫ c ≫ R'.map q = b ≫ adj'.unit.app O' ≫ R'.map p' := by
  subst hb
  refine (adj'.homEquiv _ _).symm.injective ?_
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  have c1 : L'.map (R'.map q) ≫ adj'.counit.app A' = adj'.counit.app _ ≫ q :=
    adj'.counit.naturality q
  have c2 : L'.map (R'.map p') ≫ adj'.counit.app A' = adj'.counit.app _ ≫ p' :=
    adj'.counit.naturality p'
  have tri : L'.map (adj'.unit.app O') ≫ adj'.counit.app (L'.obj O') = 𝟙 _ :=
    adj'.left_triangle_components O'
  have nθ := θ.naturality (adj.unit.app O ≫ R.map p)
  have n1 : L.map (R.map p) ≫ adj.counit.app A = adj.counit.app _ ≫ p := adj.counit.naturality p
  have tri2 : L.map (adj.unit.app O) ≫ L.map (R.map p) ≫ adj.counit.app A = p := by
    rw [n1, ← Category.assoc]
    exact (congrArg (· ≫ p) (adj.left_triangle_components O)).trans (Category.id_comp p)
  have tri3 := congrArg Q.map tri2
  simp only [Functor.map_comp] at tri3
  simp only [Functor.map_comp, Category.assoc, Functor.comp_map] at nθ ⊢
  rw [c1, c2, ← Category.assoc (L'.map (adj'.unit.app O')), tri, Category.id_comp, h,
    reassoc_of% hc, reassoc_of% nθ, reassoc_of% tri3]

/-- A square `θ_A ≫ H p ≫ m = e'(q) ≫ p'` against the inverse mate `θ` of `β`, read through the
units of the two equivalences. -/
theorem unit_comp_inverse_map_of_mateEquiv_symm (e : C ≌ D) (e' : C' ≌ D')
    (G : C ⥤ C') (H : D ⥤ D') (β : e.inverse ⋙ G ⟶ H ⋙ e'.inverse)
    {A : C} {I : D} {A' : C'} {I' : D'} (p₀ p : e.functor.obj A ⟶ I)
    (p₀' p' : e'.functor.obj A' ⟶ I') (q : G.obj A ⟶ A') (m₀ m : H.obj I ⟶ I')
    (h : e'.functor.map q ≫ p₀' =
      ((mateEquiv e.toAdjunction e'.toAdjunction).symm β).app A ≫ H.map p₀ ≫ m₀)
    (hp : p₀ = p) (hp' : p₀' = p') (hm : m₀ = m) :
    G.map (e.unit.app A ≫ e.inverse.map p) ≫ β.app I ≫ e'.inverse.map m =
      q ≫ e'.unit.app A' ≫ e'.inverse.map p' := by
  subst hp hp' hm
  exact unit_comp_map_of_comp_counit e.toAdjunction e'.toAdjunction G H
    ((mateEquiv e.toAdjunction e'.toAdjunction).symm β) p₀ p₀' m₀ q q (β.app I)
    (mateEquiv_counit_symm e.toAdjunction e'.toAdjunction β I) h rfl

/-- A square `L' b ≫ p' = θ_O ≫ Q p ≫ q` read through the units of two adjunctions, against a
morphism `c` whose transpose is `θ` followed by `Q` of the counit. -/
theorem unit_comp_map_of_isSquareTranspose {L : D ⥤ C} {R : C ⥤ D} (adj : L ⊣ R)
    {L' : D' ⥤ C'} {R' : C' ⥤ D'} (adj' : L' ⊣ R') (P : D ⥤ D') (Q : C ⥤ C')
    (θ : P ⋙ L' ≅ L ⋙ Q) {O : D} {A : C} {O' : D'} {A' : C'} (p : L.obj O ⟶ A)
    (p' : L'.obj O' ⟶ A') (q : Q.obj A ⟶ A') (b₀ b : P.obj O ⟶ O')
    (c : P.obj (R.obj A) ⟶ R'.obj (Q.obj A))
    (hc : L'.map c ≫ adj'.counit.app (Q.obj A) = θ.hom.app (R.obj A) ≫ Q.map (adj.counit.app A))
    (h : L'.map b₀ ≫ p' = θ.hom.app O ≫ Q.map p ≫ q) (hb : b₀ = b) :
    P.map (adj.unit.app O ≫ R.map p) ≫ c ≫ R'.map q = b ≫ adj'.unit.app O' ≫ R'.map p' :=
  unit_comp_map_of_comp_counit adj adj' P Q θ.hom p p' q b₀ b c hc h hb

/-- The reading of the unit of an equivalence on an isomorphism `u = E(p₁) ≫ p₂`. -/
theorem unitIso_map_comp_inverse_map {Z : Type*} [Category Z] (e : C ≌ D) (F : C ⥤ Z)
    {M : Z} {X A : C} {I : D} (a : M ⟶ F.obj X) (p₁ : X ≅ A) (p₂ : e.functor.obj A ≅ I)
    (u : e.functor.obj X ≅ I) (hu : u = e.functor.mapIso p₁ ≪≫ p₂) :
    (a ≫ F.map (e.unitIso.hom.app X)) ≫ F.map (e.inverse.map u.hom) =
      a ≫ F.map (p₁.hom ≫ e.unit.app A ≫ e.inverse.map p₂.hom) := by
  subst hu
  have n := e.unit.naturality p₁.hom
  simp only [Functor.id_map, Functor.comp_map] at n
  rw [Category.assoc, ← F.map_comp]
  refine congrArg (fun t => a ≫ F.map t) ?_
  rw [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, ← Category.assoc,
    show e.unitIso.hom.app X = e.unit.app X from rfl, ← n, Category.assoc]

variable {Z Z' : Type*} [Category Z] [Category Z']

/-- A square `P (aU ≫ FU p₁) ≫ cA ≫ FV q = b ≫ aV ≫ FV p₁'`, an equation
`Q k ≫ β ≫ m = q ≫ k'` and the naturality of `c` in `k` give the square for `p₁ ≫ k` and
`p₁' ≫ k'`. -/
theorem comp_map_comp_of_halves (P : Z ⥤ Z') (FU : C ⥤ Z) (FV : C' ⥤ Z') (Q : C ⥤ C')
    {OU : Z} {LU A K : C} {OV : Z'} {LV A' K' N : C'} (aU : OU ⟶ FU.obj LU)
    (aV : OV ⟶ FV.obj LV) (p₁ : LU ⟶ A) (p₁' : LV ⟶ A') (k : A ⟶ K) (k' : A' ⟶ K')
    (q : Q.obj A ⟶ A') (b : P.obj OU ⟶ OV) (cA : P.obj (FU.obj A) ⟶ FV.obj (Q.obj A))
    (cK : P.obj (FU.obj K) ⟶ FV.obj (Q.obj K)) (β : Q.obj K ⟶ N) (m : N ⟶ K')
    (h2a : Q.map k ≫ β ≫ m = q ≫ k')
    (h2b : P.map (aU ≫ FU.map p₁) ≫ cA ≫ FV.map q = b ≫ aV ≫ FV.map p₁')
    (hnat : P.map (FU.map k) ≫ cK = cA ≫ FV.map (Q.map k)) :
    P.map (aU ≫ FU.map (p₁ ≫ k)) ≫ (cK ≫ FV.map β) ≫ FV.map m =
      b ≫ aV ≫ FV.map (p₁' ≫ k') := by
  have h2a' := congrArg FV.map h2a
  simp only [Functor.map_comp] at h2a' h2b ⊢
  simp only [Category.assoc] at h2b ⊢
  rw [reassoc_of% hnat, h2a', ← reassoc_of% h2b]

/-- The equation `F (Hm uU ≫ mU) = F (c ≫ apb ≫ uV)`, from the readings `h1`–`h5` of its factors
through `P` and `F`. -/
theorem map_comp_eq_of_readings {Y Y' : Type*} [Category Y] [Category Y'] (F : Y' ⥤ Z')
    (FU : Y ⥤ Z) (P : Z ⥤ Z') (Hm : Y ⥤ Y') {AU IU : Y} {AV' AV IV : Y'} {OU : Z} {OV : Z'}
    (uU : AU ⟶ IU) (mU : Hm.obj IU ⟶ IV) (c : Hm.obj AU ⟶ AV') (apb : AV' ⟶ AV) (uV : AV ⟶ IV)
    (ZUh : FU.obj AU ⟶ OU) (ZUi : OU ⟶ FU.obj AU) (wU : OU ⟶ FU.obj IU)
    (rA : P.obj (FU.obj AU) ≅ F.obj (Hm.obj AU)) (rI : P.obj (FU.obj IU) ⟶ F.obj (Hm.obj IU))
    (ZVPi : P.obj OU ⟶ F.obj AV') (pb : P.obj OU ⟶ OV) (ZVi : OV ⟶ F.obj AV)
    (wV : OV ⟶ F.obj IV)
    (hZ : ZUh ≫ ZUi = 𝟙 _)
    (h1 : rA.hom ≫ F.map c = P.map ZUh ≫ ZVPi)
    (h2 : P.map (FU.map uU) ≫ rI = rA.hom ≫ F.map (Hm.map uU))
    (h3 : pb ≫ ZVi = ZVPi ≫ F.map apb)
    (h4V : ZVi ≫ F.map uV = wV) (h4U : ZUi ≫ FU.map uU = wU)
    (h5 : P.map wU ≫ rI ≫ F.map mU = pb ≫ wV) :
    F.map (Hm.map uU ≫ mU) = F.map (c ≫ apb ≫ uV) := by
  rw [← cancel_epi rA.hom, F.map_comp, F.map_comp, F.map_comp, reassoc_of% h1, ← reassoc_of% h2,
    ← reassoc_of% h3, h4V, ← h5, ← h4U, ← P.map_comp_assoc, ← Category.assoc ZUh, hZ,
    Category.id_comp]

end Abstract

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u})

/-- **The structure sheaf of the small étale site of a scheme is quasi-coherent**: it is the
associated module of the structure sheaf of the scheme, through Stacks 03LU at `ε`. -/
theorem isQuasicoherentOnSite_unit (S : Scheme.{u}) (hS : B.Contains S) :
    (SheafOfModules.unit (structureSheaf B S hS)).IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso
    (Stacks.SheafOfModules.pullbackUnitIsoTransport (toZariskiRingedToposModulesHom B S hS)
      (pullbackModulesToZariskiIso B S hS))
    (isQuasicoherentOnSite_associatedModule_of_isQuasicoherent B S hS
      (SheafOfModules.unit S.ringCatSheaf) inferInstance)

variable {X Y : B.Scheme} (a : X ⟶ Y)

/-- **Stacks 03LU round the square of `a` between étale and Zariski sites, read through
`AlgebraicGeometry.SmallEtale.restrictModulePullbackObjIso`.**  The structure sheaf of the
Zariski site of `Y`, sent by the unit of `𝓕 ↦ 𝓕^a` and Stacks 03LU at `ε_Y` to the restriction
of the étale structure sheaf, pulled back along `r` and carried by the comparison and by
Stacks 03LU for small étale base change, is Stacks 03LU for `r` followed by the same reading
on `X`. -/
theorem restrictModulePullbackObjIso_pullbackUnitIsoTransport :
    type_of% (AlgebraicGeometry.Space.unit_comp_map_of_isSquareTranspose
      (associatedModuleAdjunction B Y.obj Y.property)
      (associatedModuleAdjunction B X.obj X.property)
      (Scheme.Modules.pullback (schemeHom B a))
      (SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a))
      (associatedModuleBaseChangeIso B a)
      (Stacks.SheafOfModules.pullbackUnitIsoTransport
        (toZariskiRingedToposModulesHom B Y.obj Y.property)
        (pullbackModulesToZariskiIso B Y.obj Y.property)).hom
      (Stacks.SheafOfModules.pullbackUnitIsoTransport
        (toZariskiRingedToposModulesHom B X.obj X.property)
        (pullbackModulesToZariskiIso B X.obj X.property)).hom
      (Stacks.SheafOfModules.pullbackUnitIsoTransport (baseChangeRingedToposModulesHom B a)
        (pullbackModulesBaseChangeIso B a)).hom
      (Stacks.SheafOfModules.pullbackUnitIsoTransport (schemeHom B a).zariskiRingedToposModulesHom
        (schemeHom B a).zariskiPullbackModulesIso).hom
      (Stacks.PullbackAlgebra.pullbackUnitIso (schemeHom B a).toLRSHom.toShHom).hom
      (restrictModulePullbackObjIso B a (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B Y.obj Y.property).toRingedTopos.O))
        (isQuasicoherentOnSite_unit B Y.obj Y.property)).hom
      (isSquareTranspose_restrictModulePullbackObjIso B a
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B Y.obj Y.property).toRingedTopos.O))
        (isQuasicoherentOnSite_unit B Y.obj Y.property))
      (zariskiSquare_pullbackUnitIsoTransport B a)
      ((schemeHom B a).pullbackUnitIsoTransport_zariskiPullbackModulesIso_hom)) :=
  AlgebraicGeometry.Space.unit_comp_map_of_isSquareTranspose
      (associatedModuleAdjunction B Y.obj Y.property)
      (associatedModuleAdjunction B X.obj X.property)
      (Scheme.Modules.pullback (schemeHom B a))
      (SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a))
      (associatedModuleBaseChangeIso B a)
      (Stacks.SheafOfModules.pullbackUnitIsoTransport
        (toZariskiRingedToposModulesHom B Y.obj Y.property)
        (pullbackModulesToZariskiIso B Y.obj Y.property)).hom
      (Stacks.SheafOfModules.pullbackUnitIsoTransport
        (toZariskiRingedToposModulesHom B X.obj X.property)
        (pullbackModulesToZariskiIso B X.obj X.property)).hom
      (Stacks.SheafOfModules.pullbackUnitIsoTransport (baseChangeRingedToposModulesHom B a)
        (pullbackModulesBaseChangeIso B a)).hom
      (Stacks.SheafOfModules.pullbackUnitIsoTransport (schemeHom B a).zariskiRingedToposModulesHom
        (schemeHom B a).zariskiPullbackModulesIso).hom
      (Stacks.PullbackAlgebra.pullbackUnitIso (schemeHom B a).toLRSHom.toShHom).hom
      (restrictModulePullbackObjIso B a (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B Y.obj Y.property).toRingedTopos.O))
        (isQuasicoherentOnSite_unit B Y.obj Y.property)).hom
      (isSquareTranspose_restrictModulePullbackObjIso B a
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B Y.obj Y.property).toRingedTopos.O))
        (isQuasicoherentOnSite_unit B Y.obj Y.property))
      (zariskiSquare_pullbackUnitIsoTransport B a)
      ((schemeHom B a).pullbackUnitIsoTransport_zariskiPullbackModulesIso_hom)

/-- `AlgebraicGeometry.SmallEtale.restrictModulePullbackObjIso_naturality` out of the structure
sheaf, spelled as the target of Stacks 03LU at `ε`. -/
theorem restrictModulePullbackObjIso_naturality_unit
    {N' : SheafOfModules.{u} (structureSheaf B Y.obj Y.property)} (hN' : N'.IsQuasicoherentOnSite)
    (k : SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B Y.obj Y.property).toRingedTopos.O) ⟶ N') :
    type_of% (restrictModulePullbackObjIso_naturality B a
      (N := SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B Y.obj Y.property).toRingedTopos.O))
      (isQuasicoherentOnSite_unit B Y.obj Y.property) hN' k) :=
  restrictModulePullbackObjIso_naturality B a
      (N := SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B Y.obj Y.property).toRingedTopos.O))
      (isQuasicoherentOnSite_unit B Y.obj Y.property) hN' k

end AlgebraicGeometry.SmallEtale

namespace Stacks.SheafOfModules

open Stacks.Sheaves.RingedToposModules

universe w w' v u₁ v' u'

variable {X : AlgebraicGeometry.RingedTopos.{v, u₁, w}}
    {Y : AlgebraicGeometry.RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (f : RingedToposHom X Y)

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- `Stacks.SheafOfModules.pullbackUnitIsoTransport` along the identity identification is
the inverse of `Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso`. -/
theorem pullbackUnitIsoTransport_refl_hom :
    (pullbackUnitIsoTransport f (Iso.refl _)).hom = (pullbackModulesObjUnitIso f).inv :=
  Category.id_comp _

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- `AlgebraicGeometry.Space.representedQuasicoherentSchemeUnitIso` written out, as an equality of
isomorphisms. -/
theorem representedQuasicoherentSchemeUnitIso_eq (U : BigFppfOver B S hS) :
    representedQuasicoherentSchemeUnitIso B S hS U =
      (representedSmallEtaleModuleEquivalence B S hS U).functor.mapIso
        (Stacks.SheafOfModules.pullbackUnitIsoTransport
        (_root_.AlgebraicGeometry.SmallEtale.toZariskiRingedToposModulesHom
          (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
        (_root_.AlgebraicGeometry.SmallEtale.pullbackModulesToZariskiIso (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property)) ≪≫
      Stacks.SheafOfModules.pullbackUnitIsoTransport
        (Stacks.SheafOfModules.reindexRingedToposModulesHom
          (SmallEtale.topology B S hS (yoneda.obj U))
          (representedSmallEtaleEquivalence B S hS U)
          (representedSchemeCommRingStructureSheaf B S hS U))
        (Stacks.SheafOfModules.pullbackModulesReindexIso (SmallEtale.topology B S hS (yoneda.obj U))
          (representedSmallEtaleEquivalence B S hS U)
          (representedSchemeCommRingStructureSheaf B S hS U)) := rfl

/-- `Stacks.SheafOfModules.pullbackUnitIsoTransport` at the reindexing of `U` through the two
identifications of its pullback of modules, at the same morphism of ringed topoi. -/
theorem pullbackUnitIsoTransport_pullbackModulesReindexIso_eq (U : BigFppfOver B S hS) :
    Stacks.SheafOfModules.pullbackUnitIsoTransport
        (Stacks.SheafOfModules.reindexRingedToposModulesHom
          (SmallEtale.topology B S hS (yoneda.obj U))
        (representedSmallEtaleEquivalence B S hS U)
        (representedSchemeCommRingStructureSheaf B S hS U))
        (Stacks.SheafOfModules.pullbackModulesReindexIso (SmallEtale.topology B S hS (yoneda.obj U))
        (representedSmallEtaleEquivalence B S hS U)
        (representedSchemeCommRingStructureSheaf B S hS U)) =
      Stacks.SheafOfModules.pullbackUnitIsoTransport
        (Stacks.SheafOfModules.reindexRingedToposModulesHom
          (SmallEtale.topology B S hS (yoneda.obj U))
        (representedSmallEtaleEquivalence B S hS U)
        (representedSchemeCommRingStructureSheaf B S hS U))
        (representedReindexPullbackIso B S hS U) :=
  congrArg (Stacks.SheafOfModules.pullbackUnitIsoTransport
    (Stacks.SheafOfModules.reindexRingedToposModulesHom
          (SmallEtale.topology B S hS (yoneda.obj U))
        (representedSmallEtaleEquivalence B S hS U)
        (representedSchemeCommRingStructureSheaf B S hS U)))
    (pullbackModulesReindexIso_eq_representedReindexPullbackIso B S hS U)

/-- **The two readings of Stacks 03LU at the reindexing of `U` agree**: through
`Stacks.SheafOfModules.pullbackModulesReindexIso` and through
`AlgebraicGeometry.Space.representedReindexPullbackIso`. -/
theorem pullbackUnitIsoTransport_pullbackModulesReindexIso_eq_representedReindexPullbackIso
    (U : BigFppfOver B S hS) :
    Stacks.SheafOfModules.pullbackUnitIsoTransport
        (Stacks.SheafOfModules.reindexRingedToposModulesHom
          (SmallEtale.topology B S hS (yoneda.obj U))
        (representedSmallEtaleEquivalence B S hS U)
        (representedSchemeCommRingStructureSheaf B S hS U))
        (Stacks.SheafOfModules.pullbackModulesReindexIso (SmallEtale.topology B S hS (yoneda.obj U))
        (representedSmallEtaleEquivalence B S hS U)
        (representedSchemeCommRingStructureSheaf B S hS U)) =
      Stacks.SheafOfModules.pullbackUnitIsoTransport (representedReindexHom B S hS U)
        (representedReindexPullbackIso B S hS U) :=
  pullbackUnitIsoTransport_pullbackModulesReindexIso_eq B S hS U

/-- **The reading of `AlgebraicGeometry.Space.representedQuasicoherentSchemeUnitIso` on the scheme
underlying `U`**: through the base identification of Stacks 03DX (2), it is the unit of
`𝓕 ↦ 𝓕^a` at the structure sheaf followed by the restriction of Stacks 03LU at `ε`, of the unit of
the comparison of Stacks 04M0 and of Stacks 03LU at the reindexing. -/
theorem representedZariski_map_representedQuasicoherentSchemeUnitIso (U : BigFppfOver B S hS) :
    type_of% (unitIso_map_comp_inverse_map (representedSmallEtaleModuleEquivalence B S hS U)
      (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
      ((_root_.AlgebraicGeometry.SmallEtale.associatedModuleAdjunction (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property).unit.app
        (quasicoherentUnitObj B S hS U).obj) _ _ _
      (representedQuasicoherentSchemeUnitIso_eq B S hS U)) :=
  unitIso_map_comp_inverse_map (representedSmallEtaleModuleEquivalence B S hS U)
      (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
      ((_root_.AlgebraicGeometry.SmallEtale.associatedModuleAdjunction (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property).unit.app
        (quasicoherentUnitObj B S hS U).obj) _ _ _
      (representedQuasicoherentSchemeUnitIso_eq B S hS U)

variable {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
  (hg : yoneda.relativelyRepresentable (yoneda.map g))

/-- **Stacks 03LU round the square of `g`, read through the units of the comparisons of
Stacks 04M0.** -/
theorem representedSquare_pullbackUnitIsoTransport_unit :
    type_of% (unit_comp_inverse_map_of_mateEquiv_symm
      (representedReindexEquivalence B S hS T) (representedReindexEquivalence B S hS T')
      (smallEtaleRingedSiteHom (associatedBigEtaleSite B)
        g.left).toRingedToposSiteHom.pullbackToposGeneral
      (smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS g)).pullbackModules
      (representedSiteModulePullbackIso B S hS g hg).inv _ _ _ _ _ _ _
      (representedSquare_pullbackUnitIsoTransport_mateEquiv B S hS g hg) rfl rfl rfl) :=
  unit_comp_inverse_map_of_mateEquiv_symm
      (representedReindexEquivalence B S hS T) (representedReindexEquivalence B S hS T')
      (smallEtaleRingedSiteHom (associatedBigEtaleSite B)
        g.left).toRingedToposSiteHom.pullbackToposGeneral
      (smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS g)).pullbackModules
      (representedSiteModulePullbackIso B S hS g hg).inv _ _ _ _ _ _ _
      (representedSquare_pullbackUnitIsoTransport_mateEquiv B S hS g hg) rfl rfl rfl


/-- **The structure sheaf of a representable algebraic space is quasi-coherent**: it is the module
attached to the structure sheaf of the scheme. -/
theorem isQuasicoherentOnSite_unit_representedStructureRingSheaf (U : BigFppfOver B S hS) :
    (SheafOfModules.unit (representedStructureRingSheaf B S hS U)).IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso (representedQuasicoherentSchemeUnitIso B S hS U)
    ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj
      (quasicoherentUnitObj B S hS U)).property

/-- The structure sheaf of `yoneda.obj U` read on the small étale site of the scheme is
quasi-coherent, spelled as the target of the reindexing of `U`. -/
theorem isQuasicoherentOnSite_representedReindexEquivalence_inverse_unit (U : BigFppfOver B S hS) :
    ((representedReindexEquivalence B S hS U).inverse.obj
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos B S hS
          ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O))).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_representedSmallEtaleInverse B S hS U _
    (isQuasicoherentOnSite_unit_representedStructureRingSheaf B S hS U)

end AlgebraicGeometry.Space

end
