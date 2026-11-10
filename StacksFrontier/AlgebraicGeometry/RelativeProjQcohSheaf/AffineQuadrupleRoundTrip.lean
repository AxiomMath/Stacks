module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AffineTripleQuadruple

/-!
# A quadruple is recovered from the triple it induces

Let `S` be an **affine** scheme, `𝒜` a quasi-coherent graded `𝒪_S`-algebra (Situation 01NN),
`A = Γ(S, 𝒜)` its graded ring of global sections, `d ≥ 1` and `T` a test scheme. A quadruple
`(d, f : T → S, L, ψ)` of Section 01NS induces a triple `(d, L, ψ^♭)` of Section 01N4 over `T`
(`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.veroneseSections`), and a triple over an affine
base is turned back into a quadruple by
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.AffineTripleSections.quadruple`. This file proves
that the quadruple built from a quadruple's own induced triple is the quadruple one started from:
its base morphism is `f`, and its twisting is equal to `ψ`, since over an affine base with
quasi-coherent homogeneous pieces a twisting is determined by the degreewise maps it induces on
global sections. It also shows that the classifying morphism `T ⟶ U_d` of a quadruple depends
only on the strict equivalence class of the quadruple.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting.congrBase` and
  `...RelativeProjQcohSheaf.Quadruple.congrBase`: the transport of a twisting, resp. a quadruple,
  along an equality of its base morphisms.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.comparisonFamily`: the degreewise comparison of
  the iterated tensor powers of two invertible modules attached to an isomorphism of their
  Laurent algebras.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.classifyingHom`: the classifying
  morphism `T ⟶ U_d` of a quadruple over an affine base.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.classifyingHomOfClass`: the map
  `F_d(T) → Mor(T, U_d)` it induces on strict equivalence classes.

## Main results

* `...RelativeProjQcohSheaf.AffineTripleSections.structureHom_veroneseSections`:
  the morphism recovered from a quadruple's own induced triple is the quadruple's own morphism.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.twisting_eq_of_globalSectionHom_eq`: a twisting
  over an affine base with quasi-coherent pieces is determined by its effect on global sections.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.twisting_veroneseSections` and
  `...RelativeProjQcohSheaf.quadruple_veroneseSections`: the twisting, resp. the quadruple,
  reassembled from a quadruple's own induced triple is the original one.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.comparisonFamily_toFun`: a strict equivalence
  of quadruples compares the two triples it induces in every degree.
* `Stacks.SheafOfModules.Invertible.natTensorPowCompare_one_comp_tensorPowerOneIso` and
  `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.powCompare_one_comp_onePowIso`: in degree one
  the comparison `L ^⊗ 1 ≅ L^{⊗ 1}` of [Stacks, Tag 01CU] followed by `L^{⊗ 1} ≅ L` is the left
  unitor, in each of the two localized monoidal structures on `𝒪_T`-modules.
* `Stacks.SheafOfModules.Invertible.natTensorPowCompare_succ`: in degree `n + 1` that comparison
  is the comparison in degree `n` whiskered by one more copy of `L`, followed by the successor
  comparison of the powers of [Stacks, Tag 01CU].
* `...RelativeProjQcohSheaf.Quadruple.classifyingHom_eq_of_strictlyEquivalent`:
  the classifying morphism depends only on the strict equivalence class of a quadruple.

## Implementation notes

Several statements below are about sections of a presheaf of modules written in the spelling
`(𝒜_n).val.obj (op U)` rather than `Γ(𝒜_n, U)`. Instance search does not find the module
structure at that spelling with `Γ(S, U)` as the ring of scalars, so the scalar is bound at
`(structureRingSheaf S.toRingedSpace).obj.obj (op U)` and the image scalar on the target is
supplied as a hypothesis `s = f^♯(r)` rather than written inline; the two types are equal by
`rfl`, so a caller passes `rfl`.

The transport along `f⁻¹⊤ = ⊤` carried by
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting.globalSectionHom` is the identity
(`...AffineTripleSections.restrict_preimage_top`), which is what
`Twisting.globalSectionHom_eq_sectionHom` records; every statement below uses it instead of
rewriting with `globalSectionHom_apply`, which is not applicable at this spelling of `L`.

## References

* [Stacks Project, Tag 01NU](https://stacks.math.columbia.edu/tag/01NU)
* [Stacks Project, Section 01N4](https://stacks.math.columbia.edu/tag/01N4)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01I1](https://stacks.math.columbia.edu/tag/01I1)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open Stacks.RingedSpace
open Stacks.AlgebraicGeometry.CoherentMulSections (powCompare powCompare_hom_app_inv_app)
open Stacks.AlgebraicGeometry.MorphismToProjUniversal (psiSection unitorPow)
open Stacks.AlgebraicGeometry.ProjTripleStructureMorphism (unitGlobal divUnit zeroVeronese
  degreeZeroHom divUnit_eq_of_smul resTop_eq_self)
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.NonvanishingOpen (nonvanishingOpen)

universe u

universe v w

namespace Stacks.SheafOfModules.Invertible

open MonoidalCategory
open Stacks.TensorPowers (natTensorPow)

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafOfModules.monoidalCategory Stacks.SheafOfModules.braidedCategory

/-- **In degree one the comparison of the iterated tensor products of an invertible sheaf of
modules with the integral tensor powers of [Stacks, Tag 01CU] is the left unitor**: the
composite `L ^⊗ 1 ≅ L^{⊗ 1} ≅ L` of `natTensorPowCompare` with
`Stacks.SheafOfModules.TensorPower.tensorPowerOneIso` is `λ_ L`.

The left unitor here is the one of `Stacks.SheafOfModules.monoidalCategory`, whose unit is
`SheafOfModules.unit`. -/
theorem natTensorPowCompare_one_comp_tensorPowerOneIso
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (O : Cᵒᵖ ⥤ CommRingCat.{w})
    (hO : Presheaf.IsSheaf J
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
    (L : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [AlgebraicGeometry.SheafOfModules.IsInvertible O hO L] :
    (natTensorPowCompare O hO L 1).hom ≫
        (Stacks.SheafOfModules.TensorPower.tensorPowerOneIso O hO L).hom = (λ_ L).hom := by
  have h1 : (natTensorPowCompare O hO L 1).hom
      = (Stacks.SheafOfModules.tensorObjIso O hO
          (_root_.SheafOfModules.unit
            (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) L).hom := by
    change 𝟙 _ ≫ (𝟙 (natTensorPow L 0) ⊗ₘ 𝟙 L) ≫
        ((Stacks.SheafOfModules.tensorObjIso O hO
          (_root_.SheafOfModules.unit
            (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) L).hom ≫ 𝟙 _) = _
    let comparison := (Stacks.SheafOfModules.tensorObjIso O hO
      (_root_.SheafOfModules.unit
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) L).hom
    exact (Category.id_comp _).trans
      ((congrArg (fun morphism => morphism ≫ (comparison ≫ 𝟙 _))
        (MonoidalCategory.id_tensorHom_id (natTensorPow L 0) L)).trans
          ((Category.id_comp _).trans (Category.comp_id comparison)))
  have h2 : (Stacks.SheafOfModules.TensorPower.tensorPowerOneIso O hO L).hom
      = (Stacks.SheafOfModules.tensorSheafLeftUnitor O hO L).hom := rfl
  rw [h1, h2]
  exact (Stacks.SheafOfModules.leftUnitor_hom_eq O hO L).symm

/-- **The successor law for the comparison of the iterated tensor products of an invertible sheaf
of modules with the integral tensor powers of [Stacks, Tag 01CU].** The comparison in degree
`n + 1` is the comparison in degree `n` whiskered by one more copy of `L`, followed by the
successor comparison of Tag 01CU's powers. -/
theorem natTensorPowCompare_succ
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (O : Cᵒᵖ ⥤ CommRingCat.{w})
    (hO : Presheaf.IsSheaf J
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
    (L : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [AlgebraicGeometry.SheafOfModules.IsInvertible O hO L] (n : ℕ) :
    (natTensorPowCompare O hO L (n + 1)).hom
      = ((natTensorPowCompare O hO L n).hom ▷ L) ≫
          ((tensorPowerSystem O hO L).succIso n).hom := by
  change 𝟙 _ ≫ ((natTensorPowCompare O hO L n).hom ⊗ₘ 𝟙 L) ≫
      ((tensorPowerSystem O hO L).succIso n).hom = _
  rw [Category.id_comp, MonoidalCategory.tensorHom_id]

end Stacks.SheafOfModules.Invertible


namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

attribute [local instance] Stacks.Algebraization.sectionsModuleΓ
  Stacks.Algebraization.sectionsModuleΓSheaf Stacks.Algebraization.sectionsSMulCommClassΓ
  Stacks.Algebraization.sectionsModuleΓPresheaf
  Stacks.Algebraization.sectionsModuleΓSheafPresheaf
  Stacks.Algebraization.sectionsModuleΓSheafVal

variable {T S : Scheme.{u}} {f : T ⟶ S}
  {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} {d : ℤ}
  {L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]

namespace Twisting

/-! ### The transposed map on global sections -/

/-- A twisting is determined by its homogeneous components. -/
theorem ext_app {ψ ψ' : Twisting f A d L} (h : ∀ i, ψ.app i = ψ'.app i) : ψ = ψ' := by
  obtain ⟨a, hm, ho⟩ := ψ
  obtain ⟨a', hm', ho'⟩ := ψ'
  obtain rfl : a = a' := funext h
  rfl

/-- **The transposed map on sections is semilinear along `f^♯`.** A function `r` on an open
`U ⊆ S` multiplies a section of `𝒜_{kd}` over `U`, and the value of the transposed map is
multiplied by `f^♯(r)`. -/
theorem sectionHom_smul (ψ : Twisting f A d L) (k : ℤ)
    (U : (Opens S.toRingedSpace.carrier)ᵒᵖ)
    (r : (structureRingSheaf S.toRingedSpace).obj.obj U)
    (a : (A.piece (k * d)).val.obj U) :
    ψ.sectionHom k U (r • a) = sharp (ringedSpaceHom f) U r • ψ.sectionHom k U a := by
  change (ψ.app k).val.app _
      (pullbackUnit (ringedSpaceHom f) (A.piece (k * d)) U (r • a)) = _
  rw [pullbackUnit_smul]
  exact map_smul _ _ _

/-- **Over `U = S` the transport of `Twisting.globalSectionHom` is the identity**, so the
degree-`k` map on global sections is the transposed map on sections over `S`. The two opens
`f⁻¹⊤` and `⊤` are equal by `rfl`. -/
theorem globalSectionHom_eq_sectionHom (ψ : Twisting f A d L) (k : ℤ)
    (a : (A.piece (k * d)).val.obj (op (⊤ : Opens S.toRingedSpace.carrier))) :
    ψ.globalSectionHom k a = ψ.sectionHom k (op (⊤ : Opens S.toRingedSpace.carrier)) a :=
  AffineTripleSections.restrict_preimage_top f k _

/-- **The degree-`k` map on global sections is semilinear along `f^♯`.** The image scalar is
supplied as the hypothesis
`hs : s = f^♯(r)` rather than written inline; the two spellings of its type are equal by `rfl`,
so a caller passes `rfl`. -/
theorem globalSectionHom_smul (ψ : Twisting f A d L) (k : ℤ)
    (r : (structureRingSheaf S.toRingedSpace).obj.obj (op (⊤ : Opens S.toRingedSpace.carrier)))
    (s : (structureRingSheaf T.toRingedSpace).obj.obj (op (⊤ : Opens T.toRingedSpace.carrier)))
    (hs : s = sharp (ringedSpaceHom f) (op ⊤) r)
    (a : (A.piece (k * d)).val.obj (op (⊤ : Opens S.toRingedSpace.carrier))) :
    ψ.globalSectionHom k (r • a) = s • ψ.globalSectionHom k a := by
  subst hs
  exact (globalSectionHom_eq_sectionHom ψ k (r • a)).trans
    ((sectionHom_smul ψ k (op ⊤) r a).trans
      (congrArg (fun z => sharp (ringedSpaceHom f) (op ⊤) r • z)
        (globalSectionHom_eq_sectionHom ψ k a).symm))

/-! ### Transport along an equality of base morphisms -/

/-- A twisting over `g : T ⟶ S`, read as a twisting over a morphism `g'` equal to `g`. -/
def congrBase {g g' : T ⟶ S} (h : g = g') (ψ : Twisting g A d L) : Twisting g' A d L := h ▸ ψ

/-- The transported twisting has the same degreewise maps on global sections, whose source and
target do not mention the base morphism. -/
theorem globalSectionHom_congrBase {g g' : T ⟶ S} (h : g = g') (ψ : Twisting g A d L) (i : ℤ)
    (x : (A.piece (i * d)).val.obj (op (⊤ : Opens S.toRingedSpace.carrier))) :
    (congrBase h ψ).globalSectionHom i x = ψ.globalSectionHom i x := by
  subst h
  rfl

/-- The transported twisting is the twisting, heterogeneously. -/
theorem heq_congrBase {g g' : T ⟶ S} (h : g = g') (ψ : Twisting g A d L) :
    HEq (congrBase h ψ) ψ := by
  subst h
  rfl

end Twisting

namespace Quadruple

/-- A quadruple over `g : T ⟶ S`, read as a quadruple over a morphism `g'` equal to `g`. -/
def congrBase {g g' : T ⟶ S} (h : g = g') (P : Quadruple g A d) : Quadruple g' A d := h ▸ P

/-- Two quadruples over equal base morphisms agree as soon as their invertible modules and their
twistings do. -/
theorem congrBase_eq {g g' : T ⟶ S} (h : g = g') (Q : Quadruple g A d) (P : Quadruple g' A d)
    (hL : Q.L = P.L) (hψ : HEq Q.twisting P.twisting) : congrBase h Q = P := by
  subst h
  change Q = P
  obtain ⟨L₁, i₁, t₁, e₁⟩ := Q
  obtain ⟨L₂, i₂, t₂, e₂⟩ := P
  cases hL
  cases hψ
  rfl

end Quadruple

/-! ### A twisting over an affine base is determined by its global sections -/

/-- **Over an affine base with quasi-coherent homogeneous pieces a twisting is determined by the
degreewise maps `Twisting.globalSectionHom` it induces on global sections.** -/
theorem twisting_eq_of_globalSectionHom_eq [IsAffine S]
    (hqc : ∀ i : ℤ, (AffineTwisting.pieceMod A i).IsQuasicoherent)
    {ψ ψ' : Twisting f A d L}
    (h : ∀ (i : ℤ) (x : (A.piece (i * d)).val.obj (op (⊤ : Opens S.toRingedSpace.carrier))),
      ψ.globalSectionHom i x = ψ'.globalSectionHom i x) :
    ψ = ψ' :=
  Twisting.ext_app fun i => by
    let := hqc (i * d)
    refine AffineHomRecovery.hom_ext f (AffineTwisting.pieceMod A (i * d))
      ((laurent L).piece i) fun x => ?_
    exact ((Twisting.globalSectionHom_eq_sectionHom ψ i x).symm.trans (h i x)).trans
      (Twisting.globalSectionHom_eq_sectionHom ψ' i x)

/-! ### The degree-zero part of the induced triple -/

section Veronese

variable {B : SheafGradedAlgebra S} {k : ℕ} {M : T.Modules}
  [Stacks.Ample.IsInvertibleModule T M]

/-- **The Veronese family of a twisting is semilinear along `f^♯`.** -/
theorem veroneseRaw_smul (ψ : Twisting f (situationAlgebra B) (k : ℤ) M) (n : ℕ)
    (r : Γ(S, ⊤)) (y : B.sectionPieces ⊤ (n * k)) :
    veroneseRaw ψ n (r • y) = f.appTop r • veroneseRaw ψ n y :=
  (congrArg ((powCompare M n).inv.app ⊤)
      (Twisting.globalSectionHom_smul ψ (n : ℤ) r (f.appTop r) rfl y)).trans
    (Scheme.Modules.Hom.app_smul (powCompare M n).inv _ _)

/-- **The degree-zero component of the induced triple, on a degree-zero scalar.** The value of
the induced `ψ^♭` in degree `0` on the degree-zero element `r · 1` of `A = Γ(S, 𝒜)` is
`f^♯(r)` times the unit section of `L^{⊗ 0}`. -/
theorem veroneseSections_toFun_zero_gradeZeroHom (ψ : Twisting f (situationAlgebra B) (k : ℤ) M)
    (hone : ∀ a : B.grading (⊤ : S.Opens) (0 * k),
      (a : B.sectionRing ⊤) = 1 → (veroneseSections ψ).toFun 0 a = unitGlobal M)
    (r : Γ(S, ⊤)) :
    (veroneseSections ψ).toFun 0
        (zeroVeronese (B.grading (⊤ : S.Opens)) k (B.gradeZeroHom ⊤ r))
      = f.appTop r • unitGlobal M := by
  set aOne : B.grading (⊤ : S.Opens) (0 * k) :=
    zeroVeronese (B.grading (⊤ : S.Opens)) k 1 with haOne
  set aR : B.grading (⊤ : S.Opens) (0 * k) :=
    zeroVeronese (B.grading (⊤ : S.Opens)) k (B.gradeZeroHom ⊤ r) with haR
  have hof : ∀ (a : B.grading (⊤ : S.Opens) (0 * k)) (c : B.sectionRing ⊤),
      (a : B.sectionRing ⊤) = c → DirectSum.of (B.sectionPieces ⊤) (0 * k)
        ((a : B.sectionRing ⊤) (0 * k)) = c :=
    fun a _ h => (B.of_component ⊤ a).trans h
  have hyOne := hof aOne 1 rfl
  have hwR := hof aR (B.strHom ⊤ r) rfl
  have hsmul : DirectSum.of (B.sectionPieces ⊤) (0 * k)
      (r • (aOne : B.sectionRing ⊤) (0 * k))
      = DirectSum.of (B.sectionPieces ⊤) (0 * k) ((aR : B.sectionRing ⊤) (0 * k)) := by
    rw [← B.strHom_mul_of ⊤ r, hyOne, hwR, mul_one]
  have heq : (aR : B.sectionRing ⊤) (0 * k) = r • (aOne : B.sectionRing ⊤) (0 * k) := by
    have h := congrArg (fun u : B.sectionRing ⊤ => u (0 * k)) hsmul
    simpa using h.symm
  have hfinal : veroneseRaw ψ 0 ((aR : B.sectionRing ⊤) (0 * k))
      = f.appTop r • veroneseRaw ψ 0 ((aOne : B.sectionRing ⊤) (0 * k)) :=
    (congrArg (veroneseRaw ψ 0) heq).trans
      (veroneseRaw_smul ψ 0 r ((aOne : B.sectionRing ⊤) (0 * k)))
  exact hfinal.trans (congrArg (fun z => f.appTop r • z) (hone aOne rfl))

/-- **The degree-zero ring map of the triple induced by a twisting over `f` is `f^♯`.** -/
theorem degreeZeroHom_veroneseSections (ψ : Twisting f (situationAlgebra B) (k : ℤ) M)
    (hone : ∀ a : B.grading (⊤ : S.Opens) (0 * k),
      (a : B.sectionRing ⊤) = 1 → (veroneseSections ψ).toFun 0 a = unitGlobal M)
    (r : Γ(S, ⊤)) :
    degreeZeroHom (B.grading (⊤ : S.Opens)) (veroneseSections ψ) hone (B.gradeZeroHom ⊤ r)
      = f.appTop r :=
  divUnit_eq_of_smul ((veroneseSections_toFun_zero_gradeZeroHom ψ hone r).trans
    (congrArg (fun z => f.appTop r • z) (resTop_eq_self (unitGlobal M)).symm))

/-- **The morphism recovered from a quadruple's own induced triple is the quadruple's own
morphism.** Let `S` be affine, `𝒜` a graded `𝒪_S`-algebra with
quasi-coherent homogeneous pieces (Situation 01NN), `d ≥ 1`, and let `ψ` be the twisting of a
quadruple `(d, f : T → S, L, ψ)` of Section 01NS. The triple of Section 01N4 that `ψ` induces on
the graded ring `A = Γ(S, 𝒜)` determines, through the affine adjunction of [Stacks, Tag 01I1], a
morphism `T ⟶ S`; that morphism is `f`. -/
theorem AffineTripleSections.structureHom_veroneseSections [IsAffine S]
    (ψ : Twisting f (situationAlgebra B) (k : ℤ) M)
    (hgen : (⨆ g : B.grading (⊤ : S.Opens) k,
      nonvanishingOpen T M (psiSection (B.grading (⊤ : S.Opens)) (veroneseSections ψ) g)) = ⊤) :
    AffineTripleSections.structureHom B (veroneseSections ψ) hgen = f := by
  refine (Stacks.RelativeSpec.affineHomEquiv S T).injective ?_
  change (AffineTripleSections.structureHom B (veroneseSections ψ) hgen).appTop = f.appTop
  rw [AffineTripleSections.structureHom_appTop]
  refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
  change degreeZeroHom (B.grading (⊤ : S.Opens)) (veroneseSections ψ)
      (AffineTripleSections.toFun_zero_eq_unitGlobal B (veroneseSections ψ) hgen)
      (B.gradeZeroHom ⊤ r) = f.appTop r
  exact degreeZeroHom_veroneseSections ψ
    (AffineTripleSections.toFun_zero_eq_unitGlobal B (veroneseSections ψ) hgen) r

/-! ### The second round trip -/

/-- **The twisting reassembled from the triple a twisting induces has the original degreewise
maps on global sections.** -/
theorem globalSectionHom_twisting_veroneseSections [IsAffine S] (hk : 0 < k)
    (ψ : Twisting f (situationAlgebra B) (k : ℤ) M)
    (hgen : (⨆ g : B.grading (⊤ : S.Opens) k,
      nonvanishingOpen T M (psiSection (B.grading (⊤ : S.Opens)) (veroneseSections ψ) g)) = ⊤)
    (i : ℤ) (x : Γ(AffineTwisting.pieceMod (situationAlgebra B) (i * (k : ℤ)), ⊤)) :
    (AffineTripleSections.twisting B (veroneseSections ψ) hgen hk).globalSectionHom i x
      = ψ.globalSectionHom i x := by
  refine (AffineTripleSections.globalSectionHom_twisting B (veroneseSections ψ) hgen hk i x).trans
    ?_
  match i with
  | .ofNat n =>
      change (powCompare M n).hom.app ⊤
          (veroneseRaw ψ n (((B.ofGrading ⊤ (n * k) x : B.grading ⊤ (n * k)) :
            B.sectionRing ⊤) (n * k))) = _
      rw [show ((B.ofGrading ⊤ (n * k) x : B.grading ⊤ (n * k)) : B.sectionRing ⊤) (n * k)
          = x from DirectSum.of_eq_same (β := B.sectionPieces ⊤) (n * k) x]
      exact powCompare_hom_app_inv_app M n _
  | .negSucc j =>
      have hx : x = 0 :=
        AffineTripleSections.sections_eq_zero_of_neg B hk (Int.negSucc_lt_zero j) x
      rw [hx, map_zero]
      exact (map_zero (ψ.globalSectionHom (Int.negSucc j))).symm

/-- **Over an affine base, the twisting reassembled from the triple a twisting induces is that
twisting.** The two twistings lie over morphisms `T ⟶ S` that are equal by
`...AffineTripleSections.structureHom_veroneseSections`, along which the first is transported. -/
theorem twisting_veroneseSections [IsAffine S] (hk : 0 < k)
    (ψ : Twisting f (situationAlgebra B) (k : ℤ) M)
    (hgen : (⨆ g : B.grading (⊤ : S.Opens) k,
      nonvanishingOpen T M (psiSection (B.grading (⊤ : S.Opens)) (veroneseSections ψ) g)) = ⊤) :
    Twisting.congrBase (AffineTripleSections.structureHom_veroneseSections ψ hgen)
        (AffineTripleSections.twisting B (veroneseSections ψ) hgen hk) = ψ :=
  twisting_eq_of_globalSectionHom_eq (fun i => B.isQuasicoherent i) fun i x =>
    (Twisting.globalSectionHom_congrBase _ _ i x).trans
      (globalSectionHom_twisting_veroneseSections hk ψ hgen i x)

end Veronese

section Quadruple

variable {B : SheafGradedAlgebra S} {k : ℕ}

/-- **The quadruple reassembled from a quadruple's own induced triple is that quadruple.** Let `S`
be affine, `𝒜` a graded `𝒪_S`-algebra with quasi-coherent homogeneous pieces (Situation 01NN) and
`d ≥ 1`. A quadruple `P = (d, f : T → S, L, ψ)` of Section 01NS induces a triple
`(d, L, ψ^♭)` of Section 01N4 over `T`, and the quadruple
`...AffineTripleSections.quadruple` builds back out of that triple is `P` itself — on the nose,
not merely up to strict equivalence. -/
theorem quadruple_veroneseSections [IsAffine S] (hk : 0 < k)
    (P : Quadruple f (situationAlgebra B) (k : ℤ))
    (hgen : (⨆ g : B.grading (⊤ : S.Opens) k,
      nonvanishingOpen T P.L
        (psiSection (B.grading (⊤ : S.Opens)) (veroneseSections P.twisting) g)) = ⊤) :
    Quadruple.congrBase
        (AffineTripleSections.structureHom_veroneseSections P.twisting hgen)
        (AffineTripleSections.quadruple B (veroneseSections P.twisting) hgen hk) = P :=
  Quadruple.congrBase_eq _ _ _ rfl
    ((Twisting.heq_congrBase _ _).symm.trans
      (heq_of_eq (twisting_veroneseSections hk P.twisting hgen)))

/-! ### The degreewise comparison a strict equivalence induces on the triples -/

/-- **A homomorphism of the Laurent algebras carrying one twisting to another carries the
degreewise maps on global sections of the first to those of the second.** This is the
strict-equivalence condition `ψ ≫ γ = ψ'` read on the pullback-unit image of a global section of
`𝒜_{nd}`. -/
theorem Twisting.app_globalSectionHom {M N : T.Modules}
    [Stacks.Ample.IsInvertibleModule T M] [Stacks.Ample.IsInvertibleModule T N]
    (ψ : Twisting f (situationAlgebra B) (k : ℤ) M)
    (ψ' : Twisting f (situationAlgebra B) (k : ℤ) N)
    (γ : laurent M ⟶ laurent N) (hψ : ∀ n : ℤ, ψ.app n ≫ γ.app n = ψ'.app n) (n : ℤ)
    (y : ((situationAlgebra B).piece (n * (k : ℤ))).val.obj
      (op (⊤ : Opens S.toRingedSpace.carrier))) :
    (γ.app n).val.app (op (⊤ : Opens T.toRingedSpace.carrier)) (ψ.globalSectionHom n y)
      = ψ'.globalSectionHom n y := by
  refine (congrArg ((γ.app n).val.app (op (⊤ : Opens T.toRingedSpace.carrier)))
      (Twisting.globalSectionHom_eq_sectionHom ψ n y)).trans ?_
  refine Eq.trans ?_ (Twisting.globalSectionHom_eq_sectionHom ψ' n y).symm
  exact (SheafOfModules.comp_val_app_apply (ψ.app n) (γ.app n) _ _).symm.trans
    (congrArg (fun θ : (pullbackFunctor (ringedSpaceHom f)).obj
        ((situationAlgebra B).piece (n * (k : ℤ))) ⟶ (laurent N).piece n =>
      θ.val.app _ (pullbackUnit (ringedSpaceHom f)
        ((situationAlgebra B).piece (n * (k : ℤ))) (op ⊤) y)) (hψ n))

/-- **The degreewise comparison of the induced triples attached to an isomorphism of the Laurent
algebras**: the degree-`n` component of `γ`, read on the iterated tensor powers through the
comparison `L ^⊗ n ≅ L^{⊗ n}` of [Stacks, Tag 01CU] on both sides. -/
def comparisonFamily {M N : T.Modules}
    [Stacks.Ample.IsInvertibleModule T M] [Stacks.Ample.IsInvertibleModule T N]
    (γ : laurent M ≅ laurent N) (n : ℕ) :
    Stacks.TensorPowers.natTensorPow M n ≅ Stacks.TensorPowers.natTensorPow N n :=
  powCompare M n ≪≫
    { hom := γ.hom.app (n : ℤ)
      inv := γ.inv.app (n : ℤ)
      hom_inv_id := congrArg (fun φ : laurent M ⟶ laurent M => φ.app (n : ℤ)) γ.hom_inv_id
      inv_hom_id := congrArg (fun φ : laurent N ⟶ laurent N => φ.app (n : ℤ)) γ.inv_hom_id } ≪≫
    (powCompare N n).symm

/-- `comparisonFamily γ n` on a global section. -/
theorem comparisonFamily_hom_app {M N : T.Modules}
    [Stacks.Ample.IsInvertibleModule T M] [Stacks.Ample.IsInvertibleModule T N]
    (γ : laurent M ≅ laurent N) (n : ℕ) (z : Γ(Stacks.TensorPowers.natTensorPow M n, ⊤)) :
    (comparisonFamily γ n).hom.app ⊤ z
      = (powCompare N n).inv.app ⊤ ((γ.hom.app (n : ℤ)).val.app
          (op (⊤ : Opens T.toRingedSpace.carrier)) ((powCompare M n).hom.app ⊤ z)) := rfl

/-- **A strict equivalence of quadruples induces, in every degree, a comparison of the two triples
of Section 01N4 they induce.** Let `γ` be an isomorphism of the
Laurent algebras carrying the twisting of one quadruple to that of the other, as a strict
equivalence of Section 01NS supplies. Then the degree-`n` component of `γ`, read on the iterated
tensor powers, carries the degree-`n` component of the first induced triple to that of the
second — for **every** `n`, and not only for the `n` in which `γ` is pinned to an isomorphism of
the invertible modules. -/
theorem comparisonFamily_toFun {M N : T.Modules}
    [Stacks.Ample.IsInvertibleModule T M] [Stacks.Ample.IsInvertibleModule T N]
    (ψ : Twisting f (situationAlgebra B) (k : ℤ) M)
    (ψ' : Twisting f (situationAlgebra B) (k : ℤ) N)
    (γ : laurent M ≅ laurent N) (hψ : ∀ n : ℤ, ψ.app n ≫ γ.hom.app n = ψ'.app n) (n : ℕ)
    (x : B.grading (⊤ : S.Opens) (n * k)) :
    (comparisonFamily γ n).hom.app ⊤ ((veroneseSections ψ).toFun n x)
      = (veroneseSections ψ').toFun n x :=
  (congrArg ((powCompare N n).inv.app ⊤)
      (congrArg ((γ.hom.app (n : ℤ)).val.app (op ⊤))
        (powCompare_hom_app_inv_app M n
          (ψ.globalSectionHom (n : ℤ) ((x : B.sectionRing ⊤) (n * k)))))).trans
    (congrArg ((powCompare N n).inv.app ⊤)
      (Twisting.app_globalSectionHom ψ ψ' γ.hom hψ (n : ℤ)
        ((x : B.sectionRing ⊤) (n * k))))

/-! ### Well-definedness of the classifying morphism on strict equivalence classes -/

section Rearrangement

/-- A rearrangement with every object and morphism free: if `c ≫ o` is `lB`, if `lB` factors as
`w₂ ≫ lA`, and if `w₂` is a retraction of `w₁`, then `(w₁ ≫ c) ≫ o` is `lA`. The composite it is
applied to below mentions two monoidal structures at once and is not type-correct at the
`implicit` transparency level, so no `rw` can be performed on it directly. -/
private theorem comp_comp_of_retraction {D : Type*} [Category D] {A₀ B₀ P₀ N₀ : D}
    {w₁ : A₀ ⟶ B₀} {c : B₀ ⟶ P₀} {o : P₀ ⟶ N₀} {w₂ : B₀ ⟶ A₀} {lA : A₀ ⟶ N₀} {lB : B₀ ⟶ N₀}
    (h2 : c ≫ o = lB) (h3 : lB = w₂ ≫ lA) (hw : w₁ ≫ w₂ = 𝟙 A₀) :
    (w₁ ≫ c) ≫ o = lA := by
  rw [Category.assoc, h2, h3, ← Category.assoc, hw, Category.id_comp]

variable {Y : Scheme.{u}}

/-- Evaluating a composite of two morphisms of `𝒪_Y`-modules on a section is evaluating the
second on the value of the first. Stated with all three objects free: at the spellings below the
middle object is `L^{⊗ 1}` on one side and `Stacks.SheafOfModules.Invertible.tensorPower` on the
other, and the two are equal only by `rfl`, so
`Stacks.AlgebraicGeometry.Scheme.Modules.Hom.comp_app` cannot be matched against the composite
directly. -/
private theorem hom_app_comp_apply {A₀ B₀ C₀ : Y.Modules} (p : A₀ ⟶ B₀) (q : B₀ ⟶ C₀)
    (U : Y.Opens) (x : Γ(A₀, U)) : (p ≫ q).app U x = q.app U (p.app U x) := by
  rw [Scheme.Modules.Hom.comp_app]
  exact CategoryTheory.comp_apply _ _ x

/-- A morphism which factors as `q ≫ r ≫ e⁻¹`, read on sections and composed with `e`, is
`q` followed by `r`. All four objects are free, for the same reason as in
`hom_app_comp_apply`; the source is additionally written in the
`Stacks.SheafOfModules` spelling `p.val.app (op U)` that a homogeneous component of a morphism
of Laurent algebras carries. -/
theorem val_app_of_eq_comp_inv {A₀ B₀ C₀ D₀ : Y.Modules}
    (p : A₀ ⟶ D₀) (q : A₀ ⟶ B₀) (r : B₀ ⟶ C₀) (e : D₀ ≅ C₀) (U : Y.Opens) (x : Γ(A₀, U))
    (h : p = q ≫ r ≫ e.inv) :
    e.hom.app U (p.val.app (op U) x) = r.app U (q.app U x) := by
  have hx : p.val.app (op U) x = p.app U x := rfl
  subst h
  rw [hx, hom_app_comp_apply, hom_app_comp_apply, ← hom_app_comp_apply e.inv e.hom,
    e.inv_hom_id, Scheme.Modules.Hom.id_app, CategoryTheory.id_apply]

end Rearrangement

/-- **The comparison `L ^⊗ 1 ≅ L^{⊗ 1}` of [Stacks, Tag 01CU] followed by the identification
`L^{⊗ 1} ≅ L` is the left unitor `Stacks.AlgebraicGeometry.MorphismToProjUniversal.unitorPow`.** -/
theorem powCompare_one_comp_onePowIso (M : T.Modules)
    [Stacks.Ample.IsInvertibleModule T M] :
    (powCompare M 1).hom ≫ (onePowIso M).hom = (unitorPow M).hom := by
  let : (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u}
      ⟨T.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (T.presheaf) (forget₂ CommRingCat RingCat)
        ((CoherentMulSections.hStruct T))⟩).flip.obj (M))).IsEquivalence :=
    Stacks.SheafOfModules.isEquivalence_tensorRightFunctor_of_isInvertible
      T.presheaf (CoherentMulSections.hStruct T) M
  have h2 := Stacks.SheafOfModules.Invertible.natTensorPowCompare_one_comp_tensorPowerOneIso
    T.presheaf (CoherentMulSections.hStruct T) M
  have h3 := AlgebraicGeometry.leftUnitor_sheafOfModulesMonoidal_hom
    T.presheaf (CoherentMulSections.hStruct T) M
  have hw := (MonoidalCategory.whiskerRightIso
    (AlgebraicGeometry.SheafOfModules.unitIso T.presheaf
      (CoherentMulSections.hStruct T)) M).hom_inv_id
  exact comp_comp_of_retraction h2 h3 hw

/-- `powCompare_one_comp_onePowIso` read on a global section. -/
theorem onePowIso_hom_app_powCompare_one (M : T.Modules)
    [Stacks.Ample.IsInvertibleModule T M] (y : Γ(Stacks.TensorPowers.natTensorPow M 1, ⊤)) :
    (onePowIso M).hom.app ⊤ ((powCompare M 1).hom.app ⊤ y) = (unitorPow M).hom.app ⊤ y :=
  (hom_app_comp_apply (powCompare M 1).hom (onePowIso M).hom ⊤ y).symm.trans
    (congrArg (fun φ : Stacks.TensorPowers.natTensorPow M 1 ⟶ M => φ.app ⊤ y)
      (powCompare_one_comp_onePowIso M))

/-- **The degree-one compatibility of `comparisonFamily`.** If the degree-one component of `γ` is
the isomorphism `β` of the invertible modules through the two identifications `L^{⊗ 1} ≅ L` —
which is exactly what a strict equivalence of quadruples of Section 01NS pins — then
`comparisonFamily γ` in degree one agrees with `β` through the two left unitors `L ^⊗ 1 ≅ L`. -/
theorem unitorPow_comparisonFamily_one {M N : T.Modules}
    [Stacks.Ample.IsInvertibleModule T M] [Stacks.Ample.IsInvertibleModule T N]
    (β : M ≅ N) (γ : laurent M ≅ laurent N)
    (hβ : ∀ u : Γ(onePowModule M, ⊤),
      (onePowIso N).hom.app ⊤ ((γ.hom.app 1).val.app
          (op (⊤ : Opens T.toRingedSpace.carrier)) u)
        = β.hom.app ⊤ ((onePowIso M).hom.app ⊤ u))
    (y : Γ(Stacks.TensorPowers.natTensorPow M 1, ⊤)) :
    (unitorPow N).hom.app ⊤ ((comparisonFamily γ 1).hom.app ⊤ y)
      = β.hom.app ⊤ ((unitorPow M).hom.app ⊤ y) :=
  calc (unitorPow N).hom.app ⊤ ((comparisonFamily γ 1).hom.app ⊤ y)
      = (unitorPow N).hom.app ⊤ ((powCompare N 1).inv.app ⊤
          ((γ.hom.app 1).val.app (op (⊤ : Opens T.toRingedSpace.carrier))
            ((powCompare M 1).hom.app ⊤ y))) :=
        congrArg (fun z => (unitorPow N).hom.app ⊤ z) (comparisonFamily_hom_app γ 1 y)
    _ = (onePowIso N).hom.app ⊤ ((powCompare N 1).hom.app ⊤ ((powCompare N 1).inv.app ⊤
          ((γ.hom.app 1).val.app (op (⊤ : Opens T.toRingedSpace.carrier))
            ((powCompare M 1).hom.app ⊤ y)))) := (onePowIso_hom_app_powCompare_one N _).symm
    _ = (onePowIso N).hom.app ⊤ ((γ.hom.app 1).val.app
          (op (⊤ : Opens T.toRingedSpace.carrier)) ((powCompare M 1).hom.app ⊤ y)) :=
        congrArg (fun z => (onePowIso N).hom.app ⊤ z) (powCompare_hom_app_inv_app N 1 _)
    _ = β.hom.app ⊤ ((onePowIso M).hom.app ⊤ ((powCompare M 1).hom.app ⊤ y)) := hβ _
    _ = β.hom.app ⊤ ((unitorPow M).hom.app ⊤ y) :=
        congrArg (fun z => β.hom.app ⊤ z) (onePowIso_hom_app_powCompare_one M y)

/-- **The classifying morphism of a quadruple depends only on its strict equivalence class.** Let
`P` and `Q` be strictly equivalent quadruples of Section 01NS over the same morphism `f : T ⟶ S`.
The triples of Section 01N4 they induce (`veroneseSections`) classify, by [Stacks, Tag 01N8],
morphisms `T ⟶ U_d` inside `Proj Γ(S, 𝒜)`; this says those two morphisms are **equal**. -/
theorem Quadruple.classifyingHom_eq_of_strictlyEquivalent (hk : 0 < k)
    (P Q : Quadruple f (situationAlgebra B) (k : ℤ))
    (hPQ : Quadruple.StrictlyEquivalent P Q)
    (hgenP : (⨆ g : B.grading (⊤ : S.Opens) k, nonvanishingOpen T P.L
      (psiSection (B.grading (⊤ : S.Opens)) (veroneseSections P.twisting) g)) = ⊤)
    (hgenQ : (⨆ g : B.grading (⊤ : S.Opens) k, nonvanishingOpen T Q.L
      (psiSection (B.grading (⊤ : S.Opens)) (veroneseSections Q.twisting) g)) = ⊤) :
    Stacks.AlgebraicGeometry.ProjTripleClassifying.classifyingHom
          (B.grading (⊤ : S.Opens)) hk (veroneseSections P.twisting) hgenP
      = Stacks.AlgebraicGeometry.ProjTripleClassifying.classifyingHom
          (B.grading (⊤ : S.Opens)) hk (veroneseSections Q.twisting) hgenQ := by
  obtain ⟨β, γ, h1, hψ⟩ := hPQ
  have h1' : γ.hom.app 1 = P.oneIso.hom ≫ β.hom ≫ Q.oneIso.inv := by
    simpa only [pieceOneIso, Iso.trans_hom, Iso.symm_hom, Category.assoc] using h1
  refine Stacks.AlgebraicGeometry.ProjTripleClassifying.classifyingHom_eq_of_isoFamily
    _ hk hgenP hgenQ β (comparisonFamily γ) (fun y => ?_)
    (comparisonFamily_toFun P.twisting Q.twisting γ hψ)
  exact unitorPow_comparisonFamily_one β γ
    (fun u => by
      have computation := val_app_of_eq_comp_inv (γ.hom.app 1) P.oneIso.hom β.hom
        Q.oneIso ⊤ u h1'
      convert computation using 1 <;> rfl) y

/-- **The classifying morphism `T ⟶ U_d` of a quadruple over an affine base**: the morphism
classified by the triple of Section 01N4 the quadruple induces. -/
def Quadruple.classifyingHom [IsAffine S] (hk : 0 < k)
    (hqc : ∀ n : ℤ, ((situationAlgebra B).piece n).IsQuasicoherent)
    (P : Quadruple f (situationAlgebra B) (k : ℤ)) :
    T ⟶ (AlgebraicGeometry.Proj.degreeOpen (B.grading (⊤ : S.Opens)) k).toScheme :=
  Stacks.AlgebraicGeometry.ProjTripleClassifying.classifyingHom (B.grading (⊤ : S.Opens)) hk
    (veroneseSections P.twisting) (Quadruple.iSup_nonvanishingOpen_psiSection_eq_top hqc P)

/-- **The map `F_d(T) → Mor(T, U_d)`.** For `S` affine and `𝒜` quasi-coherent (Situation 01NN)
the classifying morphism of a quadruple, as a map on the set `F_d(T)` of strict equivalence
classes of Section 01NS. -/
def Quadruple.classifyingHomOfClass [IsAffine S] (hk : 0 < k)
    (hqc : ∀ n : ℤ, ((situationAlgebra B).piece n).IsQuasicoherent) :
    Quotient (Quadruple.setoid f (situationAlgebra B) (k : ℤ)) →
      (T ⟶ (AlgebraicGeometry.Proj.degreeOpen (B.grading (⊤ : S.Opens)) k).toScheme) :=
  Quotient.lift (Quadruple.classifyingHom hk hqc) fun P Q hPQ =>
    Quadruple.classifyingHom_eq_of_strictlyEquivalent hk P Q hPQ _ _

end Quadruple

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
