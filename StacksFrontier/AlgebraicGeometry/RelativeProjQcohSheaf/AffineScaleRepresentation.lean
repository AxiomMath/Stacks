module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTripleVeroneseMorphism
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AffineDegreeRepresentation
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.GluedRepresentsFunctor
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.PowerTransitionDescent

/-!
# The transitions `F_d → F_{a d}` classify the same morphism over an affine base

Let `S` be an **affine** scheme, `𝒜` a graded `𝒪_S`-algebra with quasi-coherent homogeneous
pieces (Situation 01NN), `d ≥ 1`, `a ≥ 1`, and let `X` be a relative homogeneous spectrum of `𝒜`
— in particular `Proj_S(𝒜)` of Lemma 01NQ. The bijections
`...RelativeProjQcohSheaf.Quadruple.fdEquivDegreeOpen'` identify `F_d(T)` with `Mor(T, U_d)` for
the degree-`d` open `U_d` of `X`. This file proves that those bijections are compatible with
the transitions `...RelativeProjQcohSheaf.Fd.scale : F_d → F_{a d}` of Section 01NS, and deduces
that `X` represents the functor `F` of [Stacks, Tag 01NY] and [Stacks, Tag 01NZ] over an affine
base.

## Main results

* `Stacks.AlgebraicGeometry.ProjTripleClassifying.classifyingHom_eq_of_family`: two triples of
  Section 01N4 of the same weight whose degreewise values are matched by any family of
  isomorphisms of the iterated tensor powers classify the same morphism.
* `...RelativeProjQcohSheaf.Twisting.powPairIso_globalSectionHom`: the degreewise maps on global
  sections of the transition `ψ ↦ ψ^{(a)}` are those of `ψ`, read through the power-of-a-power
  comparison.
* `...RelativeProjQcohSheaf.scaleCompare_toFun`: the Veronese family of a scaled twisting is
  the Veronese family of the original, read through the comparison `scaleCompare` of the two
  presentations of a tensor power.
* `...RelativeProjQcohSheaf.Quadruple.fdEquivDegreeOpen'_scale`: the bijections are compatible
  with the transitions.
* `...RelativeProjQcohSheaf.ProjDegreeRepresentation.ofAffineFull`: the representability data
  `...RelativeProjQcohSheaf.ProjDegreeRepresentation` over an affine base.
* `...RelativeProjQcohSheaf.F.representableByRelativeProjOfAffine` and
  `...RelativeProjQcohSheaf.relativeProjRepresentableByFunctorOfAffine`: [Stacks, Tag 01NY] and
  [Stacks, Tag 01NZ] over an affine base.

## Implementation notes

The two sides of `equiv_scale` reach the degree-`n` piece of a tensor power of `L^{⊗ a}` by two
routes: `...RelativeProjQcohSheaf.Twisting.scaleApp` through
`...RelativeProjQcohSheaf.powPowIso`, and
`Stacks.AlgebraicGeometry.ProjVeroneseRestrict.veroneseRestrict` through
`Stacks.AlgebraicGeometry.ProjVeroneseRestrict.powVeroneseIso`.  No coherence square between them
is needed: `classifyingHom_eq_of_family` accepts an arbitrary degreewise family of comparisons,
and the family `scaleCompare` is chosen so that the identification of the two Veronese families
holds by computation.

The module of a quadruple is replaced by a free `M : T.Modules` below the quadruple layer, since
`Quadruple.L` is a `SheafOfModules (structureRingSheaf T.toRingedSpace)` on which `rw` motives
are not type-correct and instance search for the invertibility of `natTensorPow P.L a` fails.

## References

* [Stacks Project, Tag 01NU](https://stacks.math.columbia.edu/tag/01NU)
* [Stacks Project, Tag 01NY](https://stacks.math.columbia.edu/tag/01NY)
* [Stacks Project, Tag 01NZ](https://stacks.math.columbia.edu/tag/01NZ)
* [Stacks Project, Tag 01NB](https://stacks.math.columbia.edu/tag/01NB)
* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
* [Stacks Project, Section 01N4](https://stacks.math.columbia.edu/tag/01N4)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open Stacks.RingedSpace
open Stacks.AlgebraicGeometry.CoherentMulSections (powCompare powCompare_hom_app_inv_app)
open Stacks.AlgebraicGeometry.MorphismToProjUniversal (psiSection unitorPow)
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.TensorPowers (natTensorPow)

universe u w

namespace Stacks.AlgebraicGeometry.ProjTripleClassifying

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {Y : Scheme.{u}} {d : ℕ} {L L' : Y.Modules}
  [Stacks.Ample.IsInvertibleModule Y L] [Stacks.Ample.IsInvertibleModule Y L']

/-- Two triples of [Stacks, Tag 01N8] of one weight whose degreewise values are matched by any
family `c` of isomorphisms of the iterated tensor powers classify the same morphism; no
isomorphism `L ≅ L'` of the invertible modules is asked for. -/
theorem classifyingHom_eq_of_family (hd : 0 < d)
    {ψ : Stacks.AlgebraicGeometry.ProjChartFromRatios.VeroneseSections 𝒜 d L}
    {ψ' : Stacks.AlgebraicGeometry.ProjChartFromRatios.VeroneseSections 𝒜 d L'}
    (hgen : ⨆ f : 𝒜 d, nonvanishingOpen Y L (psiSection 𝒜 ψ f) = ⊤)
    (hgen' : ⨆ f : 𝒜 d, nonvanishingOpen Y L' (psiSection 𝒜 ψ' f) = ⊤)
    (c : ∀ n : ℕ, natTensorPow L n ≅ natTensorPow L' n)
    (hc : ∀ (n : ℕ) (x : 𝒜 (n * d)), (c n).hom.app ⊤ (ψ.toFun n x) = ψ'.toFun n x) :
    classifyingHom 𝒜 hd ψ hgen = classifyingHom 𝒜 hd ψ' hgen' := by
  refine classifyingHom_eq_of_isoFamily 𝒜 hd hgen hgen'
    ((unitorPow L).symm ≪≫ c 1 ≪≫ unitorPow L') c (fun y => ?_) hc
  show (unitorPow L').hom.app ⊤ ((c 1).hom.app ⊤ y)
    = ((unitorPow L).inv ≫ (c 1).hom ≫ (unitorPow L').hom).app ⊤
        ((unitorPow L).hom.app ⊤ y)
  rw [Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply,
    Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply,
    ProjVeroneseRestrict.inv_app_hom_app]

end Stacks.AlgebraicGeometry.ProjTripleClassifying

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

/-! ### The transition of `ψ` on sections -/

section Site

open MonoidalCategory
open Stacks.PullbackTensorCoherence
open Stacks.SheafOfModules.TensorPower RingedSpaceModuleAdjunction

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory
attribute [local instance] isInvertible_piece

namespace Twisting

variable {T S : Scheme.{u}} {f : T ⟶ S}
  {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} {d : ℤ}
  {L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]

/-- The degree-`p` component of `ψ` followed by the power-of-a-power comparison is the
degree-`q` component of the transition of `ψ` to the degree `a d`, for `p = q a`, up to the
transport of the degree `p d = q (a d)`. -/
theorem app_comp_powPairIso (ψ : Twisting f A d L) {a p q : ℤ} (hp : p = q * a) :
    ψ.app p ≫ (powPairIso L a hp).hom =
      (pullbackFunctor (ringedSpaceHom f)).map
          (eqToHom (congrArg A.piece (show p * d = q * (a * d) by rw [hp]; ring))) ≫
        ψ.scaleApp a q := by
  have hr := ψ.app_reindex hp
  simp only [Twisting.scaleApp, powPairIso, Iso.trans_hom, CategoryTheory.eqToHom_map,
    eqToHom_trans_assoc]
  rw [← Category.assoc, hr, Category.assoc]
  simp only [CategoryTheory.eqToHom_map]

/-- `app_comp_powPairIso` on sections over an open `U ⊆ S`: the power-of-a-power comparison
carries the degree-`p` value of the transposed map of `ψ` to the degree-`q` value of the
transposed map of the transition `ψ^{(a)}`, on the same section read in the degree `q (a d)`. -/
theorem powPairIso_sectionHom (ψ : Twisting f A d L) {a p q : ℤ} (hp : p = q * a)
    (U : (Opens S.toRingedSpace.carrier)ᵒᵖ) (x : (A.piece (p * d)).val.obj U) :
    (powPairIso L a hp).hom.val.app ((opensMap (ringedSpaceHom f)).op.obj U)
        (ψ.sectionHom p U x)
      = (ψ.scale a).sectionHom q U
          ((eqToHom (congrArg A.piece
            (show p * d = q * (a * d) by rw [hp]; ring))).val.app U x) := by
  have h0 : (powPairIso L a hp).hom.val.app ((opensMap (ringedSpaceHom f)).op.obj U)
        (ψ.sectionHom p U x)
      = (ψ.app p ≫ (powPairIso L a hp).hom).val.app
          ((opensMap (ringedSpaceHom f)).op.obj U)
          (pullbackUnit (ringedSpaceHom f) (A.piece (p * d)) U x) :=
    (SheafOfModules.comp_val_app_apply (ψ.app p) (powPairIso L a hp).hom _ _).symm
  rw [h0, app_comp_powPairIso ψ hp, SheafOfModules.comp_val_app_apply,
    pullbackUnit_naturality]
  rfl

/-- `powPairIso_sectionHom` over `U = S`, i.e. on the global sections the degreewise maps
`A_{p d} → Γ(T, L^{⊗ p})` of Section 01N4 are built from. -/
theorem powPairIso_globalSectionHom (ψ : Twisting f A d L) {a p q : ℤ} (hp : p = q * a)
    (x : (A.piece (p * d)).val.obj (op (⊤ : Opens S.toRingedSpace.carrier))) :
    (powPairIso L a hp).hom.val.app (op (⊤ : Opens T.toRingedSpace.carrier))
        (ψ.globalSectionHom p x)
      = (ψ.scale a).globalSectionHom q
          ((eqToHom (congrArg A.piece
            (show p * d = q * (a * d) by rw [hp]; ring))).val.app
              (op (⊤ : Opens S.toRingedSpace.carrier)) x) := by
  rw [Twisting.globalSectionHom_eq_sectionHom, Twisting.globalSectionHom_eq_sectionHom]
  exact Twisting.powPairIso_sectionHom ψ hp (op (⊤ : Opens S.toRingedSpace.carrier)) x

end Twisting

end Site

/-! ### The two presentations of the `n`-th power of `L^{⊗ a}`, and the Veronese families -/

section Scale

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {T S : Scheme.{u}} {f : T ⟶ S} {B : SheafGradedAlgebra S} {d : ℕ}

/-- The integral tensor power `L^{⊗ a}` of [Stacks, Tag 01CU] is invertible, in the sense of
`Stacks.Ample.IsInvertibleModule`. -/
theorem isInvertibleModule_powModule (L : T.Modules) [Stacks.Ample.IsInvertibleModule T L]
    (a : ℤ) : Stacks.Ample.IsInvertibleModule T (powModule L a) := by
  have : AlgebraicGeometry.SheafOfModules.IsInvertible T.toRingedSpace.presheaf
      (isSheafStruct T) L := inferInstanceAs (Stacks.Ample.IsInvertibleModule T L)
  exact Stacks.SheafOfModules.Invertible.tensorPower_isInvertible
    T.toRingedSpace.presheaf (isSheafStruct T) L a

attribute [local instance] isInvertibleModule_powModule

variable {L : T.Modules} [Stacks.Ample.IsInvertibleModule T L]

/-- The degree bookkeeping of `scaleCompare`: the exponent `a n` of the iterated powers of `L`,
read as the index `n` of the Laurent algebra of `L^{⊗ a}` times `a`. -/
theorem scaleDeg (a n : ℕ) : ((a * n : ℕ) : ℤ) = (n : ℤ) * (a : ℤ) := by
  push_cast; ring

/-- The comparison `L ^⊗ (a n) ≅ (L^{⊗ a}) ^⊗ n` between the `a n`-th iterated tensor power of
`L` and the `n`-th iterated tensor power of the integral power `L^{⊗ a}`, assembled from
`...CoherentMulSections.powCompare` and `...RelativeProjQcohSheaf.powPairIso`. -/
def scaleCompare (L : T.Modules) [Stacks.Ample.IsInvertibleModule T L] (a n : ℕ) :
    natTensorPow L (a * n) ≅ natTensorPow (powModule L (a : ℤ)) n :=
  powCompare L (a * n) ≪≫ powPairIso L (a : ℤ) (scaleDeg a n) ≪≫
    (powCompare (powModule L (a : ℤ)) n).symm

/-- The Veronese family of the transition of `ψ` to the degree `a d` is the Veronese family of
`ψ`, read through `scaleCompare`: the degree-`n` value of the triple induced by `ψ^{(a)}` on a
section of degree `n (a d)` is the degree-`a n` value of the triple induced by `ψ`. -/
theorem scaleCompare_toFun (ψ : Twisting f (situationAlgebra B) ((d : ℕ) : ℤ) L) (a n : ℕ)
    (x : B.grading (⊤ : S.Opens) (n * (a * d))) (x' : B.grading (⊤ : S.Opens) (a * n * d))
    (hxx : (x' : B.sectionRing ⊤) = (x : B.sectionRing ⊤)) :
    (scaleCompare L a n).hom.app ⊤ ((veroneseSections ψ).toFun (a * n) x')
      = (veroneseSections (d := a * d) (ψ.scale (a : ℤ))).toFun n x := by
  have htr : (eqToHom (congrArg (situationAlgebra B).piece
        (show ((a * n : ℕ) : ℤ) * ((d : ℕ) : ℤ)
          = (n : ℤ) * ((a : ℤ) * ((d : ℕ) : ℤ)) by
            rw [scaleDeg a n]; ring))).val.app
        (op (⊤ : Opens S.toRingedSpace.carrier))
        ((x' : B.sectionRing ⊤) (a * n * d))
      = (x : B.sectionRing ⊤) (n * (a * d)) :=
    eqToHom_piece_app_eq (B := B) (by ring) _ _ _
      ((of_component x').trans (hxx.trans (of_component x).symm))
  refine Eq.trans ?_ (congrArg ((powCompare (powModule L (a : ℤ)) n).inv.app ⊤)
    (congrArg ((ψ.scale (a : ℤ)).globalSectionHom (n : ℤ)) htr))
  refine Eq.trans ?_ (congrArg ((powCompare (powModule L (a : ℤ)) n).inv.app ⊤)
    (Twisting.powPairIso_globalSectionHom ψ (scaleDeg a n)
      ((x' : B.sectionRing ⊤) (a * n * d))))
  exact congrArg ((powCompare (powModule L (a : ℤ)) n).inv.app ⊤)
    (congrArg ((powPairIso L (a : ℤ) (scaleDeg a n)).hom.val.app
      (op (⊤ : Opens T.toRingedSpace.carrier)))
      (powCompare_hom_app_inv_app L (a * n)
        (ψ.globalSectionHom ((a * n : ℕ) : ℤ) ((x' : B.sectionRing ⊤) (a * n * d)))))

/-! ### The transition classifies the same morphism into `Proj Γ(S, 𝒜)` -/

open Stacks.AlgebraicGeometry.MorphismsIntoProj (toProj)
open Stacks.AlgebraicGeometry.ProjTripleClassifying (classifyingHom Triple
  classifyingHom_eq_of_family)

/-- The transition of a twisting from the degree `d` to the degree `a d` classifies the same
morphism `T ⟶ Proj Γ(S, 𝒜)`. -/
theorem toProj_classifyingHom_twistingScale [IsAffine S] (hd : 0 < d) {a : ℕ} (ha : 0 < a)
    (ψ : Twisting f (situationAlgebra B) ((d : ℕ) : ℤ) L)
    (hgenP : (⨆ g : B.grading (⊤ : S.Opens) d, nonvanishingOpen T L
      (psiSection (B.grading (⊤ : S.Opens)) (veroneseSections ψ) g)) = ⊤)
    (hgenS : (⨆ g : B.grading (⊤ : S.Opens) (a * d),
      nonvanishingOpen T (powModule L (a : ℤ))
        (psiSection (B.grading (⊤ : S.Opens))
          (veroneseSections (d := a * d) (ψ.scale (a : ℤ))) g)) = ⊤) :
    toProj (B.grading (⊤ : S.Opens))
        (classifyingHom (B.grading (⊤ : S.Opens)) (Nat.mul_pos ha hd)
          (veroneseSections (d := a * d) (ψ.scale (a : ℤ))) hgenS)
      = toProj (B.grading (⊤ : S.Opens))
        (classifyingHom (B.grading (⊤ : S.Opens)) hd (veroneseSections ψ) hgenP) := by
  have key : classifyingHom (B.grading (⊤ : S.Opens)) (Nat.mul_pos ha hd)
        (ProjVeroneseRestrict.veroneseRestrict (B.grading (⊤ : S.Opens))
          (veroneseSections ψ) a)
        (ProjVeroneseRestrict.iSup_nonvanishingOpen_veroneseRestrict
          (B.grading (⊤ : S.Opens)) (veroneseSections ψ) a hgenP)
      = classifyingHom (B.grading (⊤ : S.Opens)) (Nat.mul_pos ha hd)
        (veroneseSections (d := a * d) (ψ.scale (a : ℤ))) hgenS := by
    refine classifyingHom_eq_of_family (B.grading (⊤ : S.Opens)) (Nat.mul_pos ha hd) _ _
      (fun n => ProjVeroneseRestrict.powVeroneseIso L a n ≪≫ scaleCompare L a n)
      (fun n x => ?_)
    have hx' : ((x : B.sectionRing ⊤)) ∈ B.grading (⊤ : S.Opens) (a * n * d) :=
      ProjVeroneseRestrict.mem_graded_of_eq (B.grading (⊤ : S.Opens)) (by ring) x.2
    exact (congrArg ((scaleCompare L a n).hom.app ⊤)
        (ProjTripleVeroneseMorphism.powVeroneseIso_hom_app_veroneseRestrict
          (B.grading (⊤ : S.Opens)) (veroneseSections ψ) a n x ⟨_, hx'⟩ rfl)).trans
      (scaleCompare_toFun ψ a n x ⟨_, hx'⟩ rfl)
  exact (congrArg (toProj (B.grading (⊤ : S.Opens))) key).symm.trans
    (ProjTripleVeroneseMorphism.classifyingMorphism_veroneseRestrict
      (B.grading (⊤ : S.Opens))
      (⟨d, hd, L, inferInstance, veroneseSections ψ, hgenP⟩ :
        Triple (B.grading (⊤ : S.Opens)) T)
      a ha)

/-- The transition of a quadruple of Section 01NS classifies the same morphism into
`Proj Γ(S, 𝒜)`, over an affine base. -/
theorem Quadruple.toProj_classifyingHom_scale [IsAffine S] (hd : 0 < d) {a : ℕ} (ha : 0 < a)
    (hqc : ∀ n : ℤ, ((situationAlgebra B).piece n).IsQuasicoherent)
    (Q : Quadruple f (situationAlgebra B) ((d : ℕ) : ℤ)) :
    toProj (B.grading (⊤ : S.Opens))
        (Quadruple.classifyingHom (k := a * d) (Nat.mul_pos ha hd) hqc
          (Q.scale (show (0 : ℤ) < (a : ℤ) by exact_mod_cast ha)))
      = toProj (B.grading (⊤ : S.Opens)) (Quadruple.classifyingHom hd hqc Q) :=
  toProj_classifyingHom_twistingScale hd ha Q.twisting
    (Quadruple.iSup_nonvanishingOpen_psiSection_eq_top hqc Q)
    (Quadruple.iSup_nonvanishingOpen_psiSection_eq_top (d := a * d) hqc
      (Q.scale (show (0 : ℤ) < (a : ℤ) by exact_mod_cast ha)))

/-- `Quadruple.toProj_classifyingHom_scale` on strict equivalence classes. -/
theorem Quadruple.toProj_classifyingHomOfClass_scale [IsAffine S] (hd : 0 < d) {a : ℕ}
    (ha : 0 < a) (hqc : ∀ n : ℤ, ((situationAlgebra B).piece n).IsQuasicoherent)
    (W : Scheme.{u}) (ξ : Fd (situationAlgebra B) ((d : ℕ) : ℤ) W) :
    toProj (B.grading (⊤ : S.Opens))
        (Quadruple.classifyingHomOfClass (k := a * d) (Nat.mul_pos ha hd) hqc
          (Fd.scale (show (0 : ℤ) < (a : ℤ) by exact_mod_cast ha) ξ).2)
      = toProj (B.grading (⊤ : S.Opens))
        (Quadruple.classifyingHomOfClass hd hqc ξ.2) := by
  obtain ⟨g, cls⟩ := ξ
  induction cls using Quotient.ind with
  | _ Q => exact Quadruple.toProj_classifyingHom_scale hd ha hqc Q

/-! ### The `equiv_scale` field of `ProjDegreeRepresentation` over an affine base -/

open Stacks.AlgebraicGeometry.RelativeProj

/-- The bijection of [Stacks, Tag 01NU] at the relative `U_d` is compatible with the
transitions `F_d → F_{a d}`, over an affine base and with natural-number degrees: the morphism of
the transition of a class is the morphism of the class followed by `U_d ⊆ U_{a d}`. -/
theorem Quadruple.fdEquivDegreeOpen_scale [IsAffine S] (P : RelativeProjData B) {a : ℕ}
    (hd : 0 < d) (ha : 0 < a)
    (hqc : ∀ n : ℤ, ((situationAlgebra B).piece n).IsQuasicoherent) (W : Scheme.{u})
    (ξ : Fd (situationAlgebra B) ((d : ℕ) : ℤ) W)
    (hle : P.degreeOpen d ≤ P.degreeOpen (a * d)) :
    Quadruple.fdEquivDegreeOpen P (d := a * d) (Nat.mul_pos ha hd) hqc W
        (Fd.scale (show (0 : ℤ) < (a : ℤ) by exact_mod_cast ha) ξ)
      = Quadruple.fdEquivDegreeOpen P hd hqc W ξ ≫ P.scheme.homOfLE hle := by
  have : Mono (P.degreeOpen (a * d)).ι := AlgebraicGeometry.IsOpenImmersion.mono _
  refine (cancel_mono (P.degreeOpen (a * d)).ι).mp ?_
  rw [Quadruple.fdEquivDegreeOpen_apply, Quadruple.fdEquivDegreeOpen_apply]
  simp only [Category.assoc]
  rw [Scheme.homOfLE_ι, P.degreeOpenAffineIso_hom_fac, P.degreeOpenAffineIso_hom_fac,
    ← Category.assoc, ← Category.assoc]
  exact congrArg (fun z => z ≫ P.chart ⊤ (isAffineOpen_top S))
    (Quadruple.toProj_classifyingHomOfClass_scale hd ha hqc W ξ)

/-- `Quadruple.fdEquivDegreeOpen_scale` with the two degrees integers. -/
theorem Quadruple.fdEquivDegreeOpen'_scale [IsAffine S] (P : RelativeProjData B) {p q : ℤ}
    (hp : 0 < p) (hq : 0 < q)
    (hqcoh : ∀ n : ℤ, ((situationAlgebra B).piece n).IsQuasicoherent) (W : Scheme.{u})
    (ξ : Fd (situationAlgebra B) p W) :
    Quadruple.fdEquivDegreeOpen' P (mul_pos hq hp) hqcoh W (Fd.scale hq ξ)
      = Quadruple.fdEquivDegreeOpen' P hp hqcoh W ξ ≫ P.scheme.homOfLE
          (P.degreeOpen_toNat_le_of_dvd hp (mul_pos hq hp) ⟨q, mul_comm q p⟩) := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hp.le
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hq.le
  exact Quadruple.fdEquivDegreeOpen_scale P (by exact_mod_cast hp) (by exact_mod_cast hq)
    hqcoh W ξ _

/-- For `S` affine and `𝒜` with quasi-coherent homogeneous pieces, for every `d ≥ 1` the open
`U_d` of a relative homogeneous spectrum of `𝒜` represents `F_d`, naturally in the test scheme
and compatibly with the transitions. -/
def ProjDegreeRepresentation.ofAffineFull [IsAffine S] (P : RelativeProjData B)
    (hqcoh : ∀ n : ℤ, ((situationAlgebra B).piece n).IsQuasicoherent) :
    ProjDegreeRepresentation B P :=
  ProjDegreeRepresentation.ofAffineOfScale P hqcoh
    fun _ _ hd ha W _ ξ => Quadruple.fdEquivDegreeOpen'_scale P hd ha hqcoh W ξ

/-! ### Tags 01NY and 01NZ over an affine base -/

/-- Stacks Tag 01NY over an affine base: for `S` affine and `𝒜` a graded `𝒪_S`-algebra with
quasi-coherent homogeneous pieces, a relative homogeneous spectrum `X` of `𝒜` represents the
functor `F` of the display 01NX. -/
def F.representableByRelativeProjOfAffine {S : Scheme.{u}} [IsAffine S] {B : SheafGradedAlgebra S}
    (P : RelativeProjData B)
    (hqcoh : ∀ n : ℤ, ((situationAlgebra B).piece n).IsQuasicoherent) :
    (F.limFunctor (situationAlgebra B)).RepresentableBy P.scheme :=
  F.representableByRelativeProj (ProjDegreeRepresentation.ofAffineFull P hqcoh)

/-- Stacks Tag 01NZ over an affine base: for `S` affine and `𝒜` with quasi-coherent homogeneous
pieces, the relative homogeneous spectrum `Proj_S(𝒜)` represents the functor `F` of the display
01NX. -/
def relativeProjRepresentableByFunctorOfAffine {S : Scheme.{u}} [IsAffine S]
    (B : SheafGradedAlgebra S)
    (hqcoh : ∀ n : ℤ, ((situationAlgebra B).piece n).IsQuasicoherent) :
    (F.limFunctor (situationAlgebra B)).RepresentableBy (relativeProj B).scheme :=
  relativeProjRepresentableByFunctor B (relativeProj B)
    (F.representableByRelativeProjOfAffine (relativeProj B) hqcoh)

end Scale

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
