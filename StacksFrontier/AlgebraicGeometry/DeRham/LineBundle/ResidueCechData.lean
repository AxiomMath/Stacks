module

public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.ResidueBoundaryChern
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.WeightZeroWedge
public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.ResidueLogPolesMorphism

/-!
# Čech data of the residue sequence of a line bundle

Let `f : X ⟶ S` be a morphism of schemes, `L` an invertible `𝒪_X`-module and
`0 → Ω^•_{X/S}[1] → Ω^•_{L^⋆/S,0}[1] → Ω^•_{X/S} → 0` the shifted residue sequence of
[Stacks, Tag 0FUF], read in sheaves of abelian groups. Its boundary map is computed in
`Stacks.LineBundle.Situation.abelianBoundary_eq_chernClass` from Čech data: a global section `t`
of the image of the degree-zero cycles, local lifts `eᵢ` of `t` to the cycles of the middle term,
and a Čech `1`-cocycle `z` of `𝒪_X^*` representing the class of `L` whose `d log` is carried to
the coboundary of the lifts. This file constructs that data, following the proof of
[Stacks, Tag 0FUG]: on a base chart with generator `s` the lift is `d log s`, whose residue is
`1`, and two such lifts differ on an overlap by the pullback of `d log` of the transition function
of the generators.

## Main definitions

* `Stacks.LineBundle.Situation.residueCycles`: the short exact sequence of degree-zero cycles of
  the abelian residue sequence.
* `Stacks.LineBundle.Situation.BaseChart.dlogForm`: `d log s` over a base chart, as a section of
  `Ω^1_{L^⋆/S,0}`.

## Main results

* `Stacks.LineBundle.Situation.BaseChart.residueHom_dlogForm`: the residue of `d log s` is `1`.
* `Stacks.LineBundle.Situation.BaseChart.dlogForm_sub_eq`: `d log s₁ - d log s₀ = π^* d log z`
  for generators `s₁ = z s₀`.
* `Stacks.LineBundle.Situation.exists_residueCechData`: the Čech data.

## References

* [Stacks Project, Tag 0FUG](https://stacks.math.columbia.edu/tag/0FUG)
* [Stacks Project, Tag 0FUF](https://stacks.math.columbia.edu/tag/0FUF)
* [Stacks Project, Tag 09NU](https://stacks.math.columbia.edu/tag/09NU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose

namespace Stacks.Cohomology.Leray

variable {X : TopCat.{u}}

/-- **A monomorphism of sheaves of abelian groups is injective on sections.** -/
theorem AbelianSheaf.app_injective_of_mono {F G : AbelianSheaf X} (φ : F ⟶ G) [Mono φ]
    (U : (Opens X)ᵒᵖ) : Function.Injective (φ.hom.app U) := by
  have : Mono φ.hom := (sheafToPresheaf _ _).map_mono φ
  have : Mono (φ.hom.app U) := (NatTrans.mono_iff_mono_app φ.hom).mp inferInstance U
  exact (AddCommGrpCat.mono_iff_injective _).mp inferInstance

/-- **A section killed by the differential lifts to the cycles**, for a complex of sheaves of
abelian groups. -/
theorem AbelianSheaf.exists_iCycles_app (K : CochainComplex (AbelianSheaf X) ℤ) (n m : ℤ)
    (hnm : n + 1 = m) (U : (Opens X)ᵒᵖ) (x : (K.X n).obj.obj U)
    (hx : (K.d n m).hom.app U x = 0) :
    ∃ y : (K.cycles n).obj.obj U, (K.iCycles n).hom.app U y = x := by
  let G : AbelianSheaf X ⥤ AddCommGrpCat.{u} := sheafToPresheaf _ _ ⋙ (evaluation _ _).obj U
  have hl := KernelFork.mapIsLimit _
    (K.cyclesIsKernel n m ((CochainComplex.next ℤ n).trans hnm)) G
  let φ : AddCommGrpCat.of (ULift.{u} ℤ) ⟶ G.obj (K.X n) :=
    AddCommGrpCat.ofHom ((zmultiplesHom _ x).comp AddEquiv.ulift.toAddMonoidHom)
  have hφ : φ ≫ G.map (K.d n m) = 0 := by
    ext k
    change (K.d n m).hom.app U (k.down • x) = 0
    rw [map_zsmul, hx, smul_zero]
  obtain ⟨l, hl'⟩ := KernelFork.IsLimit.lift' hl φ hφ
  exact ⟨l (ULift.up 1), (ConcreteCategory.congr_hom hl' (ULift.up 1)).trans (one_smul ℤ x)⟩

/-- A morphism of sheaves of abelian groups commutes with restriction, on sections. -/
theorem AbelianSheaf.app_map_apply {F G : AbelianSheaf X} (φ : F ⟶ G) {U V : (Opens X)ᵒᵖ}
    (f : U ⟶ V) (a : F.obj.obj U) :
    φ.hom.app V (F.obj.map f a) = G.obj.map f (φ.hom.app U a) :=
  ConcreteCategory.congr_hom (φ.hom.naturality f) a

/-- **Sections of a sheaf of abelian groups agreeing near every point are equal.** -/
theorem AbelianSheaf.eq_of_locally_eq {F : AbelianSheaf X} {U : Opens X}
    (s t : F.obj.obj (op U))
    (h : ∀ x ∈ U, ∃ (V : Opens X) (hV : V ≤ U), x ∈ V ∧
      F.obj.map (homOfLE hV).op s = F.obj.map (homOfLE hV).op t) : s = t := by
  choose V hV hxV hst using h
  exact TopCat.Sheaf.eq_of_locally_eq' (F := (F : TopCat.Sheaf AddCommGrpCat.{u} X))
    (fun x : U => V x.1 x.2) U (fun x => homOfLE (hV x.1 x.2))
    (fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxV x hx⟩) s t (fun x => hst x.1 x.2)

/-- **A section of the target of a monomorphism of sheaves of abelian groups which lies locally
in its image lies in its image.** -/
theorem AbelianSheaf.exists_app_eq_of_mono {F G : AbelianSheaf X} (φ : F ⟶ G) [Mono φ]
    {U : Opens X} (y : G.obj.obj (op U))
    (h : ∀ x ∈ U, ∃ (V : Opens X) (hV : V ≤ U), x ∈ V ∧
      ∃ a : F.obj.obj (op V), φ.hom.app (op V) a = G.obj.map (homOfLE hV).op y) :
    ∃ t : F.obj.obj (op U), φ.hom.app (op U) t = y := by
  choose V hV hxV a ha using h
  have hcomp : TopCat.Presheaf.IsCompatible F.obj (fun x : U => V x.1 x.2)
      (fun x => a x.1 x.2) := by
    intro x x'
    refine AbelianSheaf.app_injective_of_mono φ _ ?_
    rw [AbelianSheaf.app_map_apply, AbelianSheaf.app_map_apply, ha, ha,
      ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← G.obj.map_comp,
      ← G.obj.map_comp]
    rfl
  obtain ⟨t, ht, -⟩ := TopCat.Sheaf.existsUnique_gluing'
    (F := (F : TopCat.Sheaf AddCommGrpCat.{u} X))
    (fun x : U => V x.1 x.2) U (fun x => homOfLE (hV x.1 x.2))
    (fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxV x hx⟩) (fun x => a x.1 x.2) hcomp
  refine ⟨t, AbelianSheaf.eq_of_locally_eq _ _ fun x hx => ⟨V x hx, hV x hx, hxV x hx, ?_⟩⟩
  rw [← AbelianSheaf.app_map_apply]
  exact (congrArg (φ.hom.app _) (ht ⟨x, hx⟩)).trans (ha x hx)

end Stacks.Cohomology.Leray

namespace AlgebraicGeometry.SheafOfModules

attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B)

/-- **`d log` into the complex underlying the de Rham complex of sheaves of `A`-modules**, in
degree one: logarithmic differentiation into `Ω¹`, followed by the identification of `Ω¹` with the
degree-one term of the extension by zero. -/
theorem logarithmicDifferentialAbelian_comp_iso_f_one
    (h : ComplexShape.embeddingUpNat.f 1 = 1) :
    logarithmicDifferentialAbelian B D ≫ (deRhamAbelianComplexPlusIso B D).hom.hom.f 1 =
      logarithmicDifferentialSheafHom B ≫
        (_root_.SheafOfModules.toSheaf (underlyingRingSheaf A)).map
          ((deRhamComplex B D).extendXIso ComplexShape.embeddingUpNat h).inv := by
  change (logarithmicDifferentialSheafHom B ≫ (deRhamAbelianIntXIsoOne B D).inv) ≫
    (HomologicalComplex.mapHomologicalComplexExtendIso
      (_root_.SheafOfModules.toSheaf (underlyingRingSheaf A)) (deRhamComplex B D)
      ComplexShape.embeddingUpNat).hom.f 1 = _
  rw [HomologicalComplex.mapHomologicalComplexExtendIso_hom_f _ _ _ h]
  exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Iso.inv_hom_id_assoc _ _))

end AlgebraicGeometry.SheafOfModules

namespace Stacks.LineBundle

attribute [local instance] Stacks.Cohomology.Generators.picardGroupAddCommGroup

variable (D : Situation.{u})

/-- The short exact sequence of degree-zero cycles of the abelian residue sequence. -/
abbrev Situation.residueCycles :=
  HomologicalComplex.shortExactCycles
    (Stacks.Cohomology.RightDerivedBoundary.toSC D.residueAbelianSequence) 0

/-- The degree-`i'` term of `Ω^•_{L^⋆/S,0}` extended by zero, in a degree `i' = p`. -/
abbrev Situation.weightZeroExtXIso (p : ℕ) (i' : ℤ) (h : ComplexShape.embeddingUpNat.f p = i') :
    (D.weightZeroBaseComplex.extend ComplexShape.embeddingUpNat).X i' ≅
      D.weightZeroBaseComplex.X p :=
  D.weightZeroBaseComplex.extendXIso ComplexShape.embeddingUpNat h

/-- The degree-`i'` term of `Ω^•_{X/S}` extended by zero, in a degree `i' = p`. -/
abbrev Situation.deRhamExtXIso (p : ℕ) (i' : ℤ) (h : ComplexShape.embeddingUpNat.f p = i') :
    ((Scheme.Hom.deRhamComplex D.f).extend ComplexShape.embeddingUpNat).X i' ≅
      (Scheme.Hom.deRhamComplex D.f).X p :=
  (Scheme.Hom.deRhamComplex D.f).extendXIso ComplexShape.embeddingUpNat h

/-- The embedding `ComplexShape.embeddingUpNat` of `ℕ` into `ℤ` sends `1` to `0 + 1`. -/
theorem embeddingUpNat_f_one : ComplexShape.embeddingUpNat.f 1 = 0 + 1 := by simp

/-- The embedding `ComplexShape.embeddingUpNat` of `ℕ` into `ℤ` sends `0` to `0`. -/
theorem embeddingUpNat_f_zero : ComplexShape.embeddingUpNat.f 0 = 0 := by simp

/-- A morphism between transports along equalities of objects, with the transports on the
right composed into one. -/
theorem exists_eqToHom_tail {C : Type*} [Category* C] {A B E F G H I K : C} (a a' : A = B)
    (r : B ⟶ E) (b : E = F) (c : F = G) (d : G = H) (e : H = I) (k : I = K) :
    ∃ h : E = K, eqToHom a ≫ r ≫ eqToHom b ≫ (eqToHom c ≫ eqToHom d) ≫ eqToHom e ≫ eqToHom k =
      eqToHom a' ≫ r ≫ eqToHom h := by
  subst b c d e k
  exact ⟨rfl, by simp⟩

/-- **The degree-zero component of the residue of the shifted residue sequence**: the residue
`Ω^1_{L^⋆/S,0} ⟶ Ω^0_{X/S}`, between the extensions by zero, followed by a transport along an
equality of objects. -/
theorem Situation.residuePlusSequence_g_f_zero :
    ∃ h, D.residuePlusSequence.g.hom.f 0 =
      (D.weightZeroExtXIso 1 (0 + 1) embeddingUpNat_f_one).hom ≫
        (Scheme.Hom.toBaseModules D.f).map (D.residueHom 0) ≫ eqToHom h := by
  change ∃ h, ((HomologicalComplex.extendMap D.residueBaseMap ComplexShape.embeddingUpNat ≫
      (Scheme.Hom.deRhamComplex D.f).desuspendExtendIso.hom)⟦(1 : ℤ)⟧' ≫
      (shiftFunctorCompIsoId _ (-1 : ℤ) 1 (by omega)).hom.app _).f 0 = _
  rw [HomologicalComplex.comp_f, CochainComplex.shiftFunctor_map_f', HomologicalComplex.comp_f,
    HomologicalComplex.extendMap_f D.residueBaseMap ComplexShape.embeddingUpNat
      (i := 1) (i' := 0 + 1) embeddingUpNat_f_one]
  have h1 : (Scheme.Hom.deRhamComplex D.f).desuspendExtendIso.hom.f (0 + 1) =
      ((Scheme.Hom.deRhamComplex D.f).desuspend.extendXIso ComplexShape.embeddingUpNat
        (i := 1) (i' := ((1 : ℕ) : ℤ)) rfl).hom ≫
        ((Scheme.Hom.deRhamComplex D.f).extendXIso ComplexShape.embeddingUpNat
          (i := 0) (i' := ((1 : ℕ) : ℤ) + -1) (by simp)).inv := by
    change (HomologicalComplex.extendUpNatXIso _ _ (fun p (hp : p < 0) =>
      HomologicalComplex.isZero_extend_X_of_neg (p := p + -1) _ (by omega))
      (CochainComplex.desuspendXIso (Scheme.Hom.deRhamComplex D.f)) ((1 : ℕ) : ℤ)).hom = _
    rw [HomologicalComplex.extendUpNatXIso_natCast]
    rfl
  rw [h1]
  simp only [Category.assoc]
  simp only [HomologicalComplex.extendXIso, HomologicalComplex.extend.XIso, eqToIso.hom,
    eqToIso.inv, shiftFunctorCompIsoId, Iso.trans_hom, Iso.symm_hom,
    CochainComplex.shiftFunctorAdd'_inv_app_f', CochainComplex.shiftFunctorZero_hom_app_f,
    HomologicalComplex.XIsoOfEq, NatTrans.comp_app, HomologicalComplex.comp_f]
  exact exists_eqToHom_tail _ _ _ _ _ _ _ _

/-- The embedding `ComplexShape.embeddingUpNat` of `ℕ` into `ℤ` sends `2` to `1 + 1`. -/
theorem embeddingUpNat_f_two : ComplexShape.embeddingUpNat.f 2 = 1 + 1 := by simp

/-- **The degree-zero component of the inclusion of the shifted residue sequence**: the pullback
of one-forms along `π`, between the extensions by zero. -/
theorem Situation.residuePlusSequence_f_f_zero :
    D.residuePlusSequence.f.hom.f 0 =
      (D.deRhamExtXIso 1 (0 + 1) embeddingUpNat_f_one).hom ≫
        (Scheme.Hom.toBaseModules D.f).map (D.pullbackHom 1) ≫
          (D.weightZeroExtXIso 1 (0 + 1) embeddingUpNat_f_one).inv := by
  change ((HomologicalComplex.extendMap D.inclusionBaseMap ComplexShape.embeddingUpNat)⟦(1 : ℤ)⟧').f
    0 = _
  rw [CochainComplex.shiftFunctor_map_f', HomologicalComplex.extendMap_f D.inclusionBaseMap
    ComplexShape.embeddingUpNat (i := 1) (i' := 0 + 1) embeddingUpNat_f_one]
  rfl

/-- **The degree-zero differential of the middle term of the shifted residue sequence**: the
negative of the differential `Ω^1_{L^⋆/S,0} ⟶ Ω^2_{L^⋆/S,0}`, between the extensions by zero. -/
theorem Situation.residuePlusSequence_X₂_d_zero :
    D.residuePlusSequence.X₂.obj.d 0 1 =
      (1 : ℤ).negOnePow • ((D.weightZeroExtXIso 1 (0 + 1) embeddingUpNat_f_one).hom ≫
        D.weightZeroBaseD 1 ≫ (D.weightZeroExtXIso 2 (1 + 1) embeddingUpNat_f_two).inv) := by
  change ((D.weightZeroBaseComplex.extend ComplexShape.embeddingUpNat)⟦(1 : ℤ)⟧).d 0 1 = _
  rw [CochainComplex.shiftFunctor_obj_d', HomologicalComplex.extend_d_eq _ _
    embeddingUpNat_f_one embeddingUpNat_f_two, D.weightZeroBaseComplex_d 1]
  rfl

/-- **`d log` into the abelian de Rham complex**, read through the identification of the
extended degree-one term with `Ω¹`. -/
theorem Situation.logarithmicDifferentialBase_eq :
    D.logarithmicDifferentialBase =
      AlgebraicGeometry.SheafOfModules.logarithmicDifferentialSheafHom
          (Scheme.Hom.deRhamAlgebras D.f) ≫
        (SheafOfModules.toSheaf (structureSheafRing D.baseSpace)).map
          (D.deRhamExtXIso 1 1 embeddingUpNat_f_one).inv :=
  AlgebraicGeometry.SheafOfModules.logarithmicDifferentialAbelian_comp_iso_f_one _ _ _

/-! ### The logarithmic one-form of a base chart -/

namespace Situation.BaseChart

variable {D} (c : D.BaseChart)

attribute [local instance] Situation.AffineChart.algebraRA algebraRB algebraAB isScalarTower

/-- `d log s` in the decomposed form `π^*0 + π^*1 ∧ d log s` of the residue sequence. -/
theorem decomposition_dlogCoord :
    D.pullbackG (0 + 1) c.U.1 0 + D.gradedWedge 0 c.U.1
      (D.pullbackG 0 c.U.1 (((-1 : ℤ) ^ 0) •
        (Scheme.Hom.deRhamAlgebras D.f).exterior.one.eval (op c.U.1))) c.dlogCoord =
      c.dlogCoord := by
  rw [pow_zero, one_smul, D.pullbackG_one, D.gradedWedge_gradedOne_left]
  exact (congrArg (· + c.dlogCoord) (D.pullbackForms_zero 1 c.U.1)).trans (zero_add _)

/-- **`d log s` is a weight-zero one-form** over a base chart. -/
theorem dlogCoord_mem : c.dlogCoord ∈ (D.gradedLaurentForms 1 0).obj (op c.U.1) := by
  have h := c.model.decomposition_mem 0 0
    ((Scheme.Hom.deRhamAlgebras D.f).exterior.one.eval (op c.U.1))
    (c.isDlog_laurentDlog c.unit) c.unit_mem
  have e : c.model.pull 1 0 + c.model.wedge 0 (c.model.pull 0
      ((Scheme.Hom.deRhamAlgebras D.f).exterior.one.eval (op c.U.1))) c.dlogCoord =
      c.dlogCoord := by
    refine Eq.trans ?_ c.decomposition_dlogCoord
    rw [pow_zero, one_smul]
    rfl
  rwa [e] at h

/-- **The logarithmic one-form `d log s` of a base chart**, as a section of `Ω^1_{L^⋆/S,0}`. -/
def dlogForm : Γ(D.weightZero 1, c.U.1) := D.weightZeroMk 1 c.dlogCoord c.dlogCoord_mem

/-- **The residue of `d log s` is `1`.** -/
theorem residueHom_dlogForm :
    (D.residueHom 0).app c.U.1 c.dlogForm =
      (Scheme.Hom.deRhamAlgebras D.f).exterior.one.eval (op c.U.1) := by
  have h := D.residueHom_decomposition 0 c 0
    ((Scheme.Hom.deRhamAlgebras D.f).exterior.one.eval (op c.U.1))
    (c.decomposition_dlogCoord ▸ c.dlogCoord_mem)
  refine Eq.trans ?_ h
  congr 1
  exact D.weightZeroVal_injective 1 c.decomposition_dlogCoord.symm

/-- **`d log s` is closed.** -/
theorem weightZeroD_dlogForm : D.weightZeroD 1 c.U.1 c.dlogForm = 0 :=
  D.weightZeroVal_injective 2 c.gradedDiff_dlogCoord

/-- The restriction of a unit of the functions on an open of `X`. -/
abbrev unitsRestrict {D : Situation.{u}} {U W : D.X.Opens} (h : W ≤ U) (z : (Γ(D.X, U))ˣ) :
    (Γ(D.X, W))ˣ :=
  Units.map (D.X.presheaf.map (homOfLE h).op).hom.toMonoidHom z

/-- **The generators of two base charts differ on an open inside a smaller base chart by the
restriction of their transition function**: if `g₁ = z g₀` on `W`, then on a base chart
`c ≤ W` with `g₀ = u₀ g` the generator `g₁` is `(z|_c u₀) g`. -/
theorem lineGen_res_of_eq (c₀ c₁ c : D.BaseChart) {W : D.X.Opens} (h₀ : W ≤ c₀.U.1)
    (h₁ : W ≤ c₁.U.1) (hc : c.U.1 ≤ W) (z : (Γ(D.X, W))ˣ)
    (hz : D.L.val.map (homOfLE h₁).op c₁.lineGen =
      (show D.X.ringCatSheaf.obj.obj (op W) from (z : Γ(D.X, W))) •
        D.L.val.map (homOfLE h₀).op c₀.lineGen)
    (u₀ : (Γ(D.X, c.U.1))ˣ)
    (hu₀ : D.L.val.map (homOfLE (hc.trans h₀)).op c₀.lineGen =
      (show D.X.ringCatSheaf.obj.obj (op c.U.1) from (u₀ : Γ(D.X, c.U.1))) • c.lineGen) :
    D.L.val.map (homOfLE (hc.trans h₁)).op c₁.lineGen =
      (show D.X.ringCatSheaf.obj.obj (op c.U.1) from
        ((unitsRestrict hc z * u₀ : (Γ(D.X, c.U.1))ˣ) : Γ(D.X, c.U.1))) • c.lineGen := by
  refine (PresheafOfModules.map_comp_apply (M := D.L.val) (homOfLE h₁).op (homOfLE hc).op
    c₁.lineGen).trans ?_
  refine (congrArg (D.L.val.map (homOfLE hc).op) hz).trans
    ((PresheafOfModules.map_smul _ _ _ _).trans ?_)
  refine (congrArg (_ • ·) ((PresheafOfModules.map_comp_apply (M := D.L.val) (homOfLE h₀).op
    (homOfLE hc).op c₀.lineGen).symm.trans hu₀)).trans ?_
  exact (mul_smul _ _ _).symm

/-- **The difference of the logarithmic one-forms of two base charts is the pullback of `d log`
of their transition function**: if the generators satisfy `g₁ = z g₀` on an open `W`, then
`d log s₁ - d log s₀ = π^* d log z` on `W`. -/
theorem dlogForm_sub_eq (c₀ c₁ : D.BaseChart) {W : D.X.Opens} (h₀ : W ≤ c₀.U.1)
    (h₁ : W ≤ c₁.U.1) (z : (Γ(D.X, W))ˣ)
    (hz : D.L.val.map (homOfLE h₁).op c₁.lineGen =
      (show D.X.ringCatSheaf.obj.obj (op W) from (z : Γ(D.X, W))) •
        D.L.val.map (homOfLE h₀).op c₀.lineGen) :
    (D.weightZero 1).presheaf.map (homOfLE h₁).op c₁.dlogForm -
        (D.weightZero 1).presheaf.map (homOfLE h₀).op c₀.dlogForm =
      (D.pullbackHom 1).app W
        (AlgebraicGeometry.SheafOfModules.logarithmicDifferential (Scheme.Hom.deRhamAlgebras D.f)
          (op W) z) := by
  refine Stacks.Coherent.modulesSections_eq_of_locally_eq _ W _ _ fun x hx => ?_
  obtain ⟨c, hxc, hcW⟩ := D.exists_baseChart hx
  refine ⟨c.U.1, hcW, hxc, ?_⟩
  obtain ⟨u₀, hu₀⟩ := c₀.exists_units_lineGen_res c (hcW.trans h₀)
  have hval : ∀ (c' : D.BaseChart) (h : W ≤ c'.U.1) (u : (Γ(D.X, c.U.1))ˣ)
      (hu : D.L.val.map (homOfLE (hcW.trans h)).op c'.lineGen =
        (show D.X.ringCatSheaf.obj.obj (op c.U.1) from (u : Γ(D.X, c.U.1))) • c.lineGen),
      D.weightZeroVal 1 ((D.weightZero 1).presheaf.map (homOfLE hcW).op
        ((D.weightZero 1).presheaf.map (homOfLE h).op c'.dlogForm)) =
        D.laurentDlog c.U.1 (D.laurentPullbackUnit c.U.1 u) + D.laurentDlog c.U.1 c.unit := by
    intro c' h u hu
    have e : (D.weightZero 1).presheaf.map (homOfLE hcW).op
        ((D.weightZero 1).presheaf.map (homOfLE h).op c'.dlogForm) =
        (D.weightZero 1).presheaf.map (homOfLE (hcW.trans h)).op c'.dlogForm :=
      (ConcreteCategory.comp_apply _ _ _).symm.trans
        (ConcreteCategory.congr_hom ((D.weightZero 1).presheaf.map_comp (homOfLE h).op
          (homOfLE hcW).op).symm c'.dlogForm)
    rw [e, D.weightZeroVal_map]
    refine (D.laurentDlog_map (hcW.trans h) c'.unit).trans ?_
    rw [c'.unit_res_eq c (hcW.trans h) u hu, D.laurentDlog_mul]
  have hn : (D.weightZero 1).presheaf.map (homOfLE hcW).op ((D.pullbackHom 1).app W
      (AlgebraicGeometry.SheafOfModules.logarithmicDifferential (Scheme.Hom.deRhamAlgebras D.f)
        (op W) z)) =
      (D.pullbackHom 1).app c.U.1 (AlgebraicGeometry.SheafOfModules.logarithmicDifferential
        (Scheme.Hom.deRhamAlgebras D.f) (op c.U.1) (unitsRestrict hcW z)) :=
    (PresheafOfModules.naturality_apply (D.pullbackHom 1).val (homOfLE hcW).op _).symm.trans
      (congrArg ((D.pullbackHom 1).app c.U.1)
        (AlgebraicGeometry.SheafOfModules.logarithmicDifferential_map _ (homOfLE hcW).op z))
  have hmul : D.laurentPullbackUnit c.U.1 (unitsRestrict hcW z * u₀) =
      D.laurentPullbackUnit c.U.1 (unitsRestrict hcW z) * D.laurentPullbackUnit c.U.1 u₀ :=
    map_mul _ _ _
  apply D.weightZeroVal_injective 1
  rw [map_sub, hn]
  change D.weightZeroVal 1 ((D.weightZero 1).presheaf.map (homOfLE hcW).op
      ((D.weightZero 1).presheaf.map (homOfLE h₁).op c₁.dlogForm)) -
    D.weightZeroVal 1 ((D.weightZero 1).presheaf.map (homOfLE hcW).op
      ((D.weightZero 1).presheaf.map (homOfLE h₀).op c₀.dlogForm)) = _
  rw [hval c₁ h₁ _ (lineGen_res_of_eq c₀ c₁ c h₀ h₁ hcW z hz u₀ hu₀), hval c₀ h₀ u₀ hu₀, hmul,
    D.laurentDlog_mul]
  refine Eq.trans ?_ ((D.pullbackHom_app 1 c _).trans
    (D.laurentDlog_laurentPullbackUnit c.U.1 (unitsRestrict hcW z)).symm).symm
  abel

end Situation.BaseChart

/-! ### Sections of the degree-zero terms of the abelian residue sequence -/

/-- The image under forgetting the module structure of a transport along an equality of sheaves
of modules acts trivially on local sections. -/
theorem toSheaf_map_eqToHom_app_heq {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] {P Q : SheafOfModules.{u} R} (h : P = Q)
    (U : Cᵒᵖ) (x : ((SheafOfModules.toSheaf R).obj P).obj.obj U) :
    HEq (((SheafOfModules.toSheaf R).map (eqToHom h)).hom.app U x) x := by
  subst h
  rfl

/-- Equal morphisms of sheaves of abelian groups agree on sections. -/
private theorem sheaf_hom_app_congr {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {F G : Sheaf J AddCommGrpCat.{u}} {φ ψ : F ⟶ G} (h : φ = ψ) (U : Cᵒᵖ) (x : F.obj.obj U) :
    φ.hom.app U x = ψ.hom.app U x := by
  subst h
  rfl

/-- Two factorizations of the same morphism of sheaves of modules agree on sections of the
underlying abelian sheaves. -/
private theorem toSheaf_map_app_eq_of_comp_eq {C : Type*} [Category* C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}} [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] {P Q Q' T : SheafOfModules.{u} R}
    {a : P ⟶ Q} {b : Q ⟶ T} {c : P ⟶ Q'} {d : Q' ⟶ T} (h : a ≫ b = c ≫ d)
    (U : Cᵒᵖ) (x : ((SheafOfModules.toSheaf R).obj P).obj.obj U) :
    ((SheafOfModules.toSheaf R).map b).hom.app U (((SheafOfModules.toSheaf R).map a).hom.app U x) =
      ((SheafOfModules.toSheaf R).map d).hom.app U
        (((SheafOfModules.toSheaf R).map c).hom.app U x) := by
  exact (sheaf_hom_app_congr ((SheafOfModules.toSheaf R).map_comp a b) U x).symm.trans
    ((sheaf_hom_app_congr (congrArg (SheafOfModules.toSheaf R).map h) U x).trans
      (sheaf_hom_app_congr ((SheafOfModules.toSheaf R).map_comp c d) U x))

/-- An isomorphism cancels against a multiple of a composite starting with it, with every
object and morphism a variable. -/
theorem iso_inv_comp_units_smul {C : Type*} [Category* C] [Preadditive C] {A B E F : C}
    (e : A ≅ B) (d : B ⟶ E) (g : E ⟶ F) (n : ℤˣ) :
    e.inv ≫ (n • (e.hom ≫ d ≫ g)) = d ≫ ((n : ℤ) • g) := by
  simp [Units.smul_def]

/-- **A section of `Ω^1_{L^⋆/S,0}`, read in the degree-zero term of the middle of the abelian
residue sequence.** -/
abbrev Situation.weightZeroOneSection {U : D.X.Opens} (x : Γ(D.weightZero 1, U)) :
    ((Stacks.Cohomology.RightDerivedBoundary.toSC D.residueAbelianSequence).X₂.X 0).obj.obj
      (op U) :=
  ((SheafOfModules.toSheaf (structureSheafRing D.baseSpace)).map
    (D.weightZeroExtXIso 1 (0 + 1) embeddingUpNat_f_one).inv).hom.app (op U) x

/-- **A closed weight-zero one-form is a degree-zero cocycle of the middle term.** -/
theorem Situation.weightZeroOneSection_d {U : D.X.Opens} (x : Γ(D.weightZero 1, U))
    (hx : D.weightZeroD 1 U x = 0) :
    ((Stacks.Cohomology.RightDerivedBoundary.toSC D.residueAbelianSequence).X₂.d 0 1).hom.app
      (op U) (D.weightZeroOneSection x) = 0 := by
  have hm : (D.weightZeroExtXIso 1 (0 + 1) embeddingUpNat_f_one).inv ≫
      D.residuePlusSequence.X₂.obj.d 0 1 =
      D.weightZeroBaseD 1 ≫ (((1 : ℤ).negOnePow : ℤ) •
        (D.weightZeroExtXIso 2 (1 + 1) embeddingUpNat_f_two).inv) := by
    refine (congrArg (_ ≫ ·) D.residuePlusSequence_X₂_d_zero).trans ?_
    exact iso_inv_comp_units_smul (C := SheafOfModules.{u} (Scheme.Hom.baseRingSheaf D.f)) _ _ _ _
  refine (toSheaf_map_app_eq_of_comp_eq hm _ x).trans ?_
  change ((SheafOfModules.toSheaf (structureSheafRing D.baseSpace)).map
    (((1 : ℤ).negOnePow : ℤ) • (D.weightZeroExtXIso 2 (1 + 1) embeddingUpNat_f_two).inv)).hom.app
      (op U) (D.weightZeroD 1 U x) = 0
  rw [hx]
  exact map_zero _

/-- **The residue on degree-zero sections of the abelian residue sequence.** -/
theorem Situation.residueAbelianSequence_g_f_zero_heq {U : D.X.Opens} (x : Γ(D.weightZero 1, U)) :
    HEq (((Stacks.Cohomology.RightDerivedBoundary.toSC D.residueAbelianSequence).g.f 0).hom.app
      (op U) (D.weightZeroOneSection x)) ((D.residueHom 0).app U x) := by
  obtain ⟨h, hg⟩ := D.residuePlusSequence_g_f_zero
  have hm : (D.weightZeroExtXIso 1 (0 + 1) embeddingUpNat_f_one).inv ≫
      D.residuePlusSequence.g.hom.f 0 =
      (Scheme.Hom.toBaseModules D.f).map (D.residueHom 0) ≫ eqToHom h :=
    (congrArg (_ ≫ ·) hg).trans (Iso.inv_hom_id_assoc _ _)
  exact (heq_of_eq (toSheaf_map_app_eq_of_comp_eq hm _ x)).trans
    (toSheaf_map_eqToHom_app_heq h _ _)

/-- **The inclusion on degree-zero sections of the abelian residue sequence** is the pullback of
one-forms along `π`. -/
theorem Situation.residueAbelianSequence_f_f_zero_apply {U : D.X.Opens}
    (α : Γ(Scheme.Hom.relativeDifferentialForms D.f ((1 : ℕ) : ℤ), U)) :
    ((Stacks.Cohomology.RightDerivedBoundary.toSC D.residueAbelianSequence).f.f 0).hom.app (op U)
      (((SheafOfModules.toSheaf (structureSheafRing D.baseSpace)).map
        (D.deRhamExtXIso 1 (0 + 1) embeddingUpNat_f_one).inv).hom.app (op U) α) =
      D.weightZeroOneSection ((D.pullbackHom 1).app U α) := by
  have hm : (D.deRhamExtXIso 1 (0 + 1) embeddingUpNat_f_one).inv ≫
      D.residuePlusSequence.f.hom.f 0 =
      (Scheme.Hom.toBaseModules D.f).map (D.pullbackHom 1) ≫
        (D.weightZeroExtXIso 1 (0 + 1) embeddingUpNat_f_one).inv :=
    (congrArg (_ ≫ ·) D.residuePlusSequence_f_f_zero).trans (Iso.inv_hom_id_assoc _ _)
  exact toSheaf_map_app_eq_of_comp_eq hm _ α

/-- **`d log` on sections**, into the degree-one term of the abelian de Rham complex. -/
theorem Situation.logarithmicDifferentialBase_app {U : D.X.Opens}
    (u : (D.X.presheaf.obj (op U))ˣ) :
    D.logarithmicDifferentialBase.hom.app (op U) (Additive.ofMul u) =
      ((SheafOfModules.toSheaf (structureSheafRing D.baseSpace)).map
        (D.deRhamExtXIso 1 1 embeddingUpNat_f_one).inv).hom.app (op U)
        (AlgebraicGeometry.SheafOfModules.logarithmicDifferential (Scheme.Hom.deRhamAlgebras D.f)
          (op U) u) :=
  sheaf_hom_app_congr D.logarithmicDifferentialBase_eq _ _

/-! ### The Čech data -/

/-- **The Čech data of the residue sequence of a line bundle.** On the covering of `X` by the
base charts `U_c`, with generator `s_c` of `L` over `U_c`:

* `t` is the global section of the image of the degree-zero cycles of the abelian residue
  sequence whose image in `Ω^0_{X/S}` is the unit `1` of the de Rham algebra;
* `e_c` is the closed weight-zero one-form `d log s_c`, a lift of `t` to the cycles of the middle
  term (its residue is `1`);
* `z` is the transition cocycle `s_{c₁} = z_{c₀c₁} s_{c₀}` of the generators, whose Čech class is
  the class of `L` under `H¹(X, 𝒪_X^*) ≅ Pic(X)` (Tag 09NU);
* `ω = d log z` is the cocycle of closed one-forms whose pullback along `π` is the Čech
  coboundary `d log s_{c₁} - d log s_{c₀}` of the lifts.

These are the inputs of `Stacks.LineBundle.Situation.abelianBoundary_eq_chernClass`. -/
theorem Situation.exists_residueCechData (D : Situation.{u}) :
    ∃ (t : D.residueCycles.X₃.obj.obj (op ⊤)) (I : Type u) (Ui : I → Opens D.baseSpace.carrier)
      (hUi : (⊤ : Opens D.baseSpace.carrier) = ⨆ i, Ui i)
      (e : CechCochains.Cochain Ui D.residueCycles.X₂.obj 0)
      (z : CechCochains.cocycles1 Ui D.unitsSheafBase.obj)
      (ω : CechCochains.cocycles1 Ui D.residueCycles.X₁.obj),
      (∀ i : Fin 1 → I, D.residueCycles.g.hom.app (op (CechCochains.inter Ui i)) (e i) =
        D.residueCycles.X₃.obj.map (homOfLE le_top).op t) ∧
      (∀ i : Fin 2 → I, ω.val i =
        D.logarithmicDifferentialClosed.hom.app (op (CechCochains.inter Ui i)) (z.val i)) ∧
      (∀ i : Fin 2 → I, D.residueCycles.f.hom.app (op (CechCochains.inter Ui i)) (ω.val i) =
        CechCochains.cechD Ui D.residueCycles.X₂.obj 0 e i) ∧
      Stacks.Cohomology.CechOne.cechH1ToRightDerivedSections D.baseSpace.carrier ⊤ Ui hUi
          D.unitsSheafBase (CechCochains.cls Ui _ z) =
        (Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup D.X.toRingedSpace).symm
          (Stacks.SheafOfModules.Picard.classOf D.X.toRingedSpace.sheaf.obj
            (_root_.structureSheaf D.X.toRingedSpace.sheaf).property D.L
            (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ D.L D.invertible)) ∧
      (D.residueAbelianSequence.X₃.obj.iCycles 0).hom.app (op ⊤)
          ((HomologicalComplex.cyclesImageι
            (Stacks.Cohomology.RightDerivedBoundary.toSC D.residueAbelianSequence) 0).hom.app
              (op ⊤) t) =
        (AlgebraicGeometry.SheafOfModules.deRhamDifferentialGradedAlgebra
          (Scheme.Hom.deRhamAlgebras D.f)
          (AlgebraicGeometry.SheafOfModules.deRhamDifferential
            (Scheme.Hom.deRhamAlgebras D.f))).one.eval (op ⊤) := by
  classical
  let K := Stacks.Cohomology.RightDerivedBoundary.toSC D.residueAbelianSequence
  let Ui : D.BaseChart → Opens D.baseSpace.carrier := fun c => c.U.1
  have hUi : (⊤ : Opens D.baseSpace.carrier) = ⨆ c, Ui c := by
    refine (eq_top_iff.2 fun x _ => Opens.mem_iSup.2 ?_).symm
    obtain ⟨c, hc, -⟩ := D.exists_baseChart (W := ⊤) (x := x) trivial
    exact ⟨c, hc⟩
  -- the lifts of `d log s` to the cycles of the middle term
  have hy : ∀ c : D.BaseChart, ∃ y : (K.X₂.cycles 0).obj.obj (op c.U.1),
      (K.X₂.iCycles 0).hom.app (op c.U.1) y = D.weightZeroOneSection c.dlogForm := fun c =>
    Stacks.Cohomology.Leray.AbelianSheaf.exists_iCycles_app K.X₂ 0 1 rfl _ _
      (D.weightZeroOneSection_d c.dlogForm c.weightZeroD_dlogForm)
  choose y hy using hy
  -- the inclusion of the image of the cycles into the degree-zero term of `Ω^•`
  let m : D.residueCycles.X₃ ⟶ K.X₃.X 0 := HomologicalComplex.cyclesImageι K 0 ≫ K.X₃.iCycles 0
  have hgm : D.residueCycles.g ≫ m = K.X₂.iCycles 0 ≫ K.g.f 0 := by
    rw [← Category.assoc, HomologicalComplex.shortExactCycles_g_cyclesImageι,
      HomologicalComplex.cyclesMap_i]
  let one := (AlgebraicGeometry.SheafOfModules.deRhamDifferentialGradedAlgebra
    (Scheme.Hom.deRhamAlgebras D.f)
    (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f))).one
  have hone : ∀ c : D.BaseChart,
      m.hom.app (op c.U.1) (D.residueCycles.g.hom.app (op c.U.1) (y c)) = one.eval (op c.U.1) := by
    intro c
    refine (sheaf_hom_app_congr hgm _ _).trans ?_
    change (K.g.f 0).hom.app (op c.U.1) ((K.X₂.iCycles 0).hom.app (op c.U.1) (y c)) = _
    rw [hy c]
    refine eq_of_heq ((D.residueAbelianSequence_g_f_zero_heq c.dlogForm).trans ?_)
    rw [c.residueHom_dlogForm]
    exact (AlgebraicGeometry.SheafOfModules.deRhamDifferentialGradedAlgebra_one _ _ _).symm
  have hone_map : ∀ {V W : Opens D.baseSpace.carrier} (h : W ≤ V),
      (K.X₃.X 0).obj.map (homOfLE h).op (one.eval (op V)) = one.eval (op W) := fun h =>
    one.property (homOfLE h).op
  -- the global section `t` of the image of the cycles
  obtain ⟨t, ht⟩ := Stacks.Cohomology.Leray.AbelianSheaf.exists_app_eq_of_mono m
    (one.eval (op ⊤)) fun x _ => by
      obtain ⟨c, hc, -⟩ := D.exists_baseChart (W := ⊤) (x := x) trivial
      exact ⟨c.U.1, le_top, hc, _, (hone c).trans (hone_map le_top).symm⟩
  -- the lifts on the covering
  let e : CechCochains.Cochain Ui D.residueCycles.X₂.obj 0 := fun i =>
    (K.X₂.cycles 0).obj.map (homOfLE (CechCochains.inter_le Ui i 0)).op (y (i 0))
  have he : ∀ i : Fin 1 → D.BaseChart, D.residueCycles.g.hom.app (op (CechCochains.inter Ui i))
      (e i) = D.residueCycles.X₃.obj.map (homOfLE le_top).op t := by
    intro i
    refine Stacks.Cohomology.Leray.AbelianSheaf.app_injective_of_mono m _ ?_
    refine ((congrArg (m.hom.app _).hom (Stacks.Cohomology.Leray.AbelianSheaf.app_map_apply
      D.residueCycles.g _ (y (i 0)))).trans ((Stacks.Cohomology.Leray.AbelianSheaf.app_map_apply
        m _ _).trans ((congrArg _ (hone (i 0))).trans (hone_map _)))).trans ?_
    exact ((Stacks.Cohomology.Leray.AbelianSheaf.app_map_apply m _ t).trans
      ((congrArg _ ht).trans (hone_map _))).symm
  -- the transition cocycle of the generators of the base charts
  have hL : Stacks.SheafOfModules.IsInvertible D.X.toRingedSpace.sheaf.obj
      (_root_.structureSheaf D.X.toRingedSpace.sheaf).property D.L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ D.L D.invertible
  let F := Stacks.Cohomology.Generators.generatorTorsorOfInvertible D.X.toRingedSpace D.L hL
  let s : ∀ c : D.BaseChart, F.toTorsor.F.obj (Ui c) := fun c =>
    (F.sectionsEquiv (Ui c)).symm ⟨c.lineGen, fun V h => c.bijective_smul_lineGen V h⟩
  let z := Stacks.Cohomology.SheafTorsor.torsorTransitionCocycle F.toTorsor Ui s
  have hz : Stacks.Cohomology.CechOne.cechH1ToRightDerivedSections D.baseSpace.carrier ⊤ Ui hUi
      D.unitsSheafBase (CechCochains.cls Ui _ z) =
      (Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup D.X.toRingedSpace).symm
        (Stacks.SheafOfModules.Picard.classOf D.X.toRingedSpace.sheaf.obj
          (_root_.structureSheaf D.X.toRingedSpace.sheaf).property D.L hL) :=
    ((Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup_symm_classOf D.X.toRingedSpace
      D.L hL).trans (Stacks.Cohomology.SheafTorsor.torsorClassEquivSheafCohomologyOne_of_cocycle
        _ _ F.toTorsor Ui hUi s z
        (Stacks.Cohomology.SheafTorsor.torsorTransitionCocycle_spec _ _ _))).symm
  have hzrel : ∀ i : Fin 2 → D.BaseChart,
      D.L.val.map (homOfLE (CechCochains.inter_le Ui i 1)).op (i 1).lineGen =
        (show D.X.ringCatSheaf.obj.obj (op (CechCochains.inter Ui i)) from
          ((Additive.toMul (z.val i) : (Γ(D.X, CechCochains.inter Ui i))ˣ) :
            Γ(D.X, CechCochains.inter Ui i))) •
          (show D.L.val.obj (op (CechCochains.inter Ui i)) from
            D.L.val.map (homOfLE (CechCochains.inter_le Ui i 0)).op (i 0).lineGen) := by
    intro i
    have h1 := F.sectionsEquiv_restrict (CechCochains.inter_le Ui i 1) (s (i 1))
    have h0 := F.sectionsEquiv_restrict (CechCochains.inter_le Ui i 0) (s (i 0))
    have hs := F.sectionsEquiv_smul (CechCochains.inter Ui i) (Additive.toMul (z.val i))
      (F.F.res (CechCochains.inter_le Ui i 0) (s (i 0)))
    have hspec := Stacks.Cohomology.SheafTorsor.torsorTransitionCocycle_spec F.toTorsor Ui s i
    simp only [s, Equiv.apply_symm_apply] at h1 h0
    refine h1.symm.trans ((congrArg (fun a => (F.sectionsEquiv _ a).val) hspec.symm).trans
      (hs.trans ?_))
    exact congrArg (fun a : D.L.val.obj (op (CechCochains.inter Ui i)) =>
      (show D.X.ringCatSheaf.obj.obj (op (CechCochains.inter Ui i)) from
        ((Additive.toMul (z.val i) : (Γ(D.X, CechCochains.inter Ui i))ˣ) :
          Γ(D.X, CechCochains.inter Ui i))) • a) h0
  -- the cocycle of closed one-forms
  let ω : CechCochains.cocycles1 Ui D.residueCycles.X₁.obj :=
    ⟨Stacks.Cohomology.CechOne.push Ui D.logarithmicDifferentialClosed.hom 1 z.val,
      Stacks.Cohomology.CechOne.cechD_push Ui _ 1 z.val z.2⟩
  -- the faces of the coboundary of the lifts
  let ι := (SheafOfModules.toSheaf.{u} (structureSheafRing D.baseSpace)).map
    (D.weightZeroExtXIso 1 (0 + 1) embeddingUpNat_f_one).inv
  have hface : ∀ (i : Fin 2 → D.BaseChart) (j : Fin 2),
      CechCochains.restr (K.X₂.X 0).obj (CechCochains.inter_le_omit Ui i j)
        ((K.X₂.iCycles 0).hom.app (op _) (e (i ∘ j.succAbove))) =
      D.weightZeroOneSection ((D.weightZero 1).presheaf.map
        (homOfLE (CechCochains.inter_le Ui i (j.succAbove 0))).op
          (i (j.succAbove 0)).dlogForm) := by
    intro i j
    refine (congrArg (CechCochains.restr (K.X₂.X 0).obj (CechCochains.inter_le_omit Ui i j))
      ((Stacks.Cohomology.Leray.AbelianSheaf.app_map_apply (K.X₂.iCycles 0) _ _).trans
        (congrArg _ (hy _)))).trans ?_
    refine (congrArg (CechCochains.restr (K.X₂.X 0).obj (CechCochains.inter_le_omit Ui i j))
      (Stacks.Cohomology.Leray.AbelianSheaf.app_map_apply ι _ _).symm).trans ?_
    refine (Stacks.Cohomology.Leray.AbelianSheaf.app_map_apply ι _ _).symm.trans ?_
    refine congrArg (ι.hom.app _) ?_
    exact (ConcreteCategory.comp_apply _ _ _).symm.trans
      (ConcreteCategory.congr_hom ((D.weightZero 1).presheaf.map_comp _ _).symm _)
  have hω : ∀ i : Fin 2 → D.BaseChart, D.residueCycles.f.hom.app (op (CechCochains.inter Ui i))
      (ω.val i) = CechCochains.cechD Ui D.residueCycles.X₂.obj 0 e i := by
    intro i
    refine Stacks.Cohomology.Leray.AbelianSheaf.app_injective_of_mono (K.X₂.iCycles 0) _ ?_
    have hfi : D.residueCycles.f ≫ K.X₂.iCycles 0 = K.X₁.iCycles 0 ≫ K.f.f 0 :=
      HomologicalComplex.cyclesMap_i _ _
    have hL1 := sheaf_hom_app_congr hfi (op (CechCochains.inter Ui i)) (ω.val i)
    have hL2 := sheaf_hom_app_congr D.logarithmicDifferentialClosed_iCycles
      (op (CechCochains.inter Ui i)) (z.val i)
    have hL3 := D.logarithmicDifferentialBase_app (U := CechCochains.inter Ui i)
      (Additive.toMul (z.val i))
    have hL4 := D.residueAbelianSequence_f_f_zero_apply (U := CechCochains.inter Ui i)
      (AlgebraicGeometry.SheafOfModules.logarithmicDifferential (Scheme.Hom.deRhamAlgebras D.f)
        (op (CechCochains.inter Ui i)) (Additive.toMul (z.val i)))
    have hR1 := congrFun (Stacks.Cohomology.CechOne.push_cechD Ui (K.X₂.iCycles 0).hom 0 e) i
    have hsub := Situation.BaseChart.dlogForm_sub_eq (i 0) (i 1) (CechCochains.inter_le Ui i 0)
      (CechCochains.inter_le Ui i 1) (Additive.toMul (z.val i)) (hzrel i)
    refine (hL1.trans ((congrArg _ (hL2.trans hL3)).trans hL4)).trans (Eq.trans ?_ hR1.symm)
    rw [CechCochains.cechD_apply, Fin.sum_univ_two]
    refine Eq.trans ?_ (congrArg₂ (fun a b => (-1 : ℤ) ^ ((0 : Fin 2) : ℕ) • a +
      (-1 : ℤ) ^ ((1 : Fin 2) : ℕ) • b) (hface i 0) (hface i 1)).symm
    refine (congrArg (fun a => D.weightZeroOneSection (U := CechCochains.inter Ui i) a)
      hsub.symm).trans ?_
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_one_smul,
      ← sub_eq_add_neg]
    exact map_sub _ _ _
  exact ⟨t, D.BaseChart, Ui, hUi, e, z, ω, he, fun _ => rfl, hω, hz, ht⟩

end Stacks.LineBundle

end
