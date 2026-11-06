module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FirstOrderThickeningConormalConverse
public import StacksFrontier.AlgebraicGeometry.Thickenings.SquareZeroExtension
public import StacksFrontier.Deformation.Examples.Geometric.SchemesPredeformation
public import StacksFrontier.Deformation.Examples.Geometric.SchemeDeformationConormalFree
public import StacksFrontier.Deformation.Examples.Geometric.SchemeDeformationSolution
public import StacksFrontier.Deformation.RingedSpaceThickening.SolutionAutomorphisms

/-!
# Realizing a solution of the deformation problem of Stacks 08U7 as a deformation of a scheme

Let `X` be a scheme over a field `k` and `A` an object of `𝒞_Λ`. A solution `Q` of the deformation
problem of [Stacks Project, Tag 08U7] for the closed point `Spec k ⊂ Spec A`, the structure
morphism of `X`, the module `f^* 𝒥` and the identity as prescribed map is a first order
thickening `X ⊂ X'` of *ringed spaces* over `Spec A`. This file shows that `X'` is a scheme and
that it is a deformation of `X` over `A` in the sense of [Stacks Project, Tag 0DY7]: this is the
converse half of the identification, used in the proof of [Stacks Project, Tag 0D14], of flat
deformations with solutions.

The scheme structure is [Stacks Project, Tag 05YV]: `𝒪_{X'}`, read on `|X|` through the
homeomorphism underlying the thickening, is a square-zero extension of `𝒪_X` with quasi-coherent
kernel `f^* 𝒥`, and such an extension is realized by a scheme.

## Main definitions

* `Deformation.Examples.solutionSquareZeroExtension`: the square-zero extension of `𝒪_X` over
  `Spec A` underlying a solution.

## References

* [Stacks Project, Tag 05YV](https://stacks.math.columbia.edu/tag/05YV)
* [Stacks Project, Tag 08U7](https://stacks.math.columbia.edu/tag/08U7)
* [Stacks Project, Tag 0D14](https://stacks.math.columbia.edu/tag/0D14)
* [Stacks Project, Tag 0DY7](https://stacks.math.columbia.edu/tag/0DY7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction AlgebraicGeometry.RingedSpaceThickening

universe u

namespace Deformation.Examples

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
  {X : Over (Spec (CommRingCat.of k))} {A : ArtinianLocalAlgCat.{u, u, u} Λ k}
  {ht : IsFirstOrderThickening (residueSpecMap A).toLRSHom.toShHom}
  (Q : DeformationSolution (residueSpecMap A).toLRSHom.toShHom ht X.hom.toLRSHom.toShHom
    (SchemeDeformationCategory.pulledIdeal A X) (𝟙 _))

/-- The structure sheaf of the deformed space of a solution, read on `|X|` through the
homeomorphism underlying the thickening. -/
noncomputable def solutionSheaf : TopCat.Sheaf CommRingCat.{u} X.left :=
  (TopCat.Sheaf.pushforward CommRingCat.{u} Q.baseIso.inv).obj Q.X'.sheaf

/-- Any two morphisms between opens of a space (in the opposite category) are equal. -/
private theorem opens_op_hom_ext {T : TopCat.{u}} {U V : (Opens T)ᵒᵖ} (p q : U ⟶ V) : p = q :=
  Quiver.Hom.unop_inj (Subsingleton.elim _ _)

/-- The reduction of a solution read on the opens of `X`, as a composite of morphisms. -/
theorem
    _root_.AlgebraicGeometry.RingedSpaceThickening.DeformationSolution.thickenedReduction_eq_comp
    {X S S' : RingedSpace.{u, u}} {t : S ⟶ S'} {ht : IsFirstOrderThickening t} {f : X ⟶ S}
    {G : SheafOfModules.{u} (structureSheafRing X)}
    {c : (modulePullback f).obj
      ((modulePullback t).obj (AlgebraicGeometry.SheafOfModules.idealSheaf t)) ⟶ G}
    (Q : DeformationSolution t ht f G c) (U : (Opens X.carrier)ᵒᵖ) :
    Q.thickenedReduction.app U =
      Q.i.hom.c.app ((Opens.map Q.baseIso.inv).op.obj U) ≫ X.presheaf.map (Q.roundTripHom U) := by
  ext x
  exact Q.thickenedReduction_app U x

/-- The reduction `𝒪_{X'} ⟶ 𝒪_X` of a solution, read on `|X|`. -/
noncomputable def solutionReduction : solutionSheaf Q ⟶ X.left.sheaf where
  hom := Q.thickenedReduction

/-- The inclusion of `X` into the sheafed space `(|X|, 𝒪_{X'})`. -/
noncomputable def solutionInclusion :
    X.left.toSheafedSpace ⟶ Stacks.Thickenings.thickenedSpace X.left (solutionSheaf Q) :=
  InducedCategory.homMk { base := 𝟙 (X.left : TopCat), c := Q.thickenedReduction }

/-- The deformed space of a solution is the sheafed space `(|X|, 𝒪_{X'})`. -/
noncomputable def solutionSheafedIso :
    Q.X' ≅ Stacks.Thickenings.thickenedSpace X.left (solutionSheaf Q) :=
  SheafedSpace.isoMk (PresheafedSpace.isoOfComponents Q.baseIso.symm (Iso.refl _))

/-- The thickening of a solution, read on `(|X|, 𝒪_{X'})`, is the inclusion. -/
theorem i_comp_solutionSheafedIso :
    Q.i ≫ (solutionSheafedIso Q).hom = solutionInclusion Q := by
  apply SheafedSpace.ext _ _ Q.baseIso.hom_inv_id
  refine NatTrans.ext (funext fun U => ?_)
  rw [NatTrans.comp_app]
  show (𝟙 _ ≫ Q.i.hom.c.app _) ≫ X.left.presheaf.map _ = Q.thickenedReduction.app U
  rw [Category.id_comp, Q.thickenedReduction_eq_comp U]
  congr 2
  exact opens_op_hom_ext _ _

/-- The morphism of a solution to `Spec A`, read on `(|X|, 𝒪_{X'})`. -/
noncomputable def solutionToBase :
    Stacks.Thickenings.thickenedSpace X.left (solutionSheaf Q) ⟶
      (baseSpec A).toSheafedSpace :=
  (solutionSheafedIso Q).inv ≫ Q.f'

/-- The inclusion followed by the morphism to `Spec A` is the structure morphism of `X` followed by
the closed point. -/
theorem solutionInclusion_comp_toBase :
    solutionInclusion Q ≫ solutionToBase Q = (X.hom ≫ residueSpecMap A).toLRSHom.toShHom := by
  rw [solutionToBase, ← i_comp_solutionSheafedIso, Category.assoc, Iso.hom_inv_id_assoc]
  exact Q.comm

/-- The restriction identifying an open of `X` with the matching open of `X'` pulled back. -/
noncomputable abbrev ascendHom (U : (Opens X.left.carrier)ᵒᵖ) :
    U ⟶ (Opens.map Q.baseIso.hom).op.obj ((Opens.map Q.baseIso.inv).op.obj U) :=
  eqToHom (congrArg op (Q.opens_roundTrip U.unop).symm)

/-- The inclusion of the ideal `f^* 𝒥` of a solution into `𝒪_{X'}`, read on `|X|`. -/
noncomputable def solutionKernelInclusion (U : (Opens X.left.carrier)ᵒᵖ) :
    (SchemeDeformationCategory.pulledIdeal A X).val.obj U →+ (solutionSheaf Q).presheaf.obj U :=
  ((Q.idealInclusion.val.app ((Opens.map Q.baseIso.inv).op.obj U)).hom.toAddMonoidHom).comp
    ((SchemeDeformationCategory.pulledIdeal A X).val.map (ascendHom Q U)).hom.toAddMonoidHom

/-- Two chains of restriction maps between the same opens agree, the opens forming a poset. -/
theorem pulledIdeal_map_map {P R R' T : (Opens X.left.carrier)ᵒᵖ} (p : P ⟶ R) (q : R ⟶ T)
    (p' : P ⟶ R') (q' : R' ⟶ T) (w : (SchemeDeformationCategory.pulledIdeal A X).val.obj P) :
    (SchemeDeformationCategory.pulledIdeal A X).val.map q
        ((SchemeDeformationCategory.pulledIdeal A X).val.map p w) =
      (SchemeDeformationCategory.pulledIdeal A X).val.map q'
        ((SchemeDeformationCategory.pulledIdeal A X).val.map p' w) := by
  rw [← PresheafOfModules.map_comp_apply, ← PresheafOfModules.map_comp_apply]
  exact (SchemeDeformationCategory.pulledIdeal A X).val.congr_map_apply
    (opens_op_hom_ext _ _) w

/-- The inclusion of the ideal commutes with restriction. -/
theorem solutionKernelInclusion_naturality {U V : (Opens X.left.carrier)ᵒᵖ} (g : U ⟶ V)
    (x : (SchemeDeformationCategory.pulledIdeal A X).val.obj U) :
    solutionKernelInclusion Q V ((SchemeDeformationCategory.pulledIdeal A X).val.map g x) =
      (solutionSheaf Q).presheaf.map g (solutionKernelInclusion Q U x) := by
  show Q.incl _ = (Q.X'.presheaf.map ((Opens.map Q.baseIso.inv).op.map g)).hom (Q.incl _)
  rw [← DeformationSolution.incl_naturality]
  exact congrArg Q.incl (pulledIdeal_map_map _ _ _ _ x)

/-- The ideal is killed by the reduction. -/
theorem solutionKernelInclusion_mem_kernel (U : (Opens X.left.carrier)ᵒᵖ)
    (x : (SchemeDeformationCategory.pulledIdeal A X).val.obj U) :
    (solutionReduction Q).hom.app U (solutionKernelInclusion Q U x) = 0 := by
  show (Q.thickenedReduction.app U).hom (Q.incl _) = 0
  rw [Q.thickenedReduction_app]
  show (X.left.presheaf.map (Q.roundTripHom U)).hom (Q.reduction (Q.incl _)) = 0
  rw [Q.reduction_incl]
  exact map_zero _

/-- The ideal has square zero. -/
theorem solutionKernelInclusion_square_zero (U : (Opens X.left.carrier)ᵒᵖ)
    (x y : (SchemeDeformationCategory.pulledIdeal A X).val.obj U) :
    solutionKernelInclusion Q U x * solutionKernelInclusion Q U y = 0 :=
  DeformationSolution.incl_mul_incl _ _

/-- Restricting a section of a presheaf of modules on a space to a smaller open and back to the
original one returns it: the opens form a poset. -/
theorem _root_.PresheafOfModules.map_map_eq_self_of_opens {T : TopCat.{u}}
    {R : (Opens T)ᵒᵖ ⥤ RingCat.{u}} (M : PresheafOfModules.{u} R) {U V : (Opens T)ᵒᵖ}
    (p : U ⟶ V) (q : V ⟶ U) (x : M.obj U) : M.map q (M.map p x) = x := by
  rw [← M.map_comp_apply, M.congr_map_apply
    (opens_op_hom_ext _ (𝟙 U))]
  simp only [PresheafOfModules.map_id]
  rfl

/-- Restricting along the round trip of opens and back does nothing. -/
theorem pulledIdeal_map_roundTrip (U : (Opens X.left.carrier)ᵒᵖ)
    (g : (SchemeDeformationCategory.pulledIdeal A X).val.obj
      ((Opens.map Q.baseIso.hom).op.obj ((Opens.map Q.baseIso.inv).op.obj U))) :
    (SchemeDeformationCategory.pulledIdeal A X).val.map (ascendHom Q U)
      ((SchemeDeformationCategory.pulledIdeal A X).val.map (Q.roundTripHom U) g) = g :=
  PresheafOfModules.map_map_eq_self_of_opens _ _ _ g

/-- Restricting back along the round trip of opens and forth does nothing. -/
theorem pulledIdeal_map_roundTrip' (U : (Opens X.left.carrier)ᵒᵖ)
    (y : (SchemeDeformationCategory.pulledIdeal A X).val.obj U) :
    (SchemeDeformationCategory.pulledIdeal A X).val.map (Q.roundTripHom U)
      ((SchemeDeformationCategory.pulledIdeal A X).val.map (ascendHom Q U) y) = y :=
  PresheafOfModules.map_map_eq_self_of_opens _ _ _ y

/-- The ideal is exactly the kernel of the reduction. -/
theorem solutionKernelInclusion_exact (U : (Opens X.left.carrier)ᵒᵖ)
    (a : (solutionSheaf Q).presheaf.obj U) (ha : (solutionReduction Q).hom.app U a = 0) :
    ∃! x, solutionKernelInclusion Q U x = a := by
  have h0 := Q.comorphism_eq_zero_of_thickenedReduction_eq_zero a ha
  obtain ⟨g, hg⟩ := Q.exists_incl a h0
  refine ⟨(SchemeDeformationCategory.pulledIdeal A X).val.map (Q.roundTripHom U) g, ?_, ?_⟩
  · exact (congrArg Q.incl (pulledIdeal_map_roundTrip Q U g)).trans hg
  · intro y hy
    have hy' : Q.incl ((SchemeDeformationCategory.pulledIdeal A X).val.map (ascendHom Q U) y) =
        Q.incl g := hy.trans hg.symm
    exact ((congrArg _ (Q.incl_injective hy').symm).trans (pulledIdeal_map_roundTrip' Q U y)).symm

/-- Restricting a section of a presheaf of rings on a space to a smaller open and back returns it.
-/
theorem presheaf_map_map_eq_self_of_opens {T : TopCat.{u}} (F : (Opens T)ᵒᵖ ⥤ CommRingCat.{u})
    {U V : (Opens T)ᵒᵖ} (p : U ⟶ V) (q : V ⟶ U) (x : F.obj U) :
    (F.map q).hom ((F.map p).hom x) = x := by
  rw [← ConcreteCategory.comp_apply, ← CategoryTheory.Functor.map_comp,
    opens_op_hom_ext (p ≫ q) (𝟙 U),
    CategoryTheory.Functor.map_id]
  rfl

/-- The module structure of the ideal is multiplication by local lifts. -/
theorem solutionKernelInclusion_smul (U : (Opens X.left.carrier)ᵒᵖ)
    (a : (solutionSheaf Q).presheaf.obj U)
    (x : (SchemeDeformationCategory.pulledIdeal A X).val.obj U) :
    solutionKernelInclusion Q U
      ((((SchemeDeformationCategory.pulledIdeal A X).val.obj U).smul
        ((solutionReduction Q).hom.app U a)).asHom.hom x) =
      a * solutionKernelInclusion Q U x := by
  have hc : X.left.ringCatSheaf.obj.map (ascendHom Q U)
      ((solutionReduction Q).hom.app U a) =
      Q.i.hom.c.app ((Opens.map Q.baseIso.inv).op.obj U) a := by
    show (X.left.presheaf.map (ascendHom Q U)).hom ((Q.thickenedReduction.app U).hom a) = _
    exact (congrArg _ (Q.thickenedReduction_app U a)).trans
      (presheaf_map_map_eq_self_of_opens _ _ _ _)
  show Q.incl _ = (show Q.X'.presheaf.obj ((Opens.map Q.baseIso.inv).op.obj U) from a) *
    Q.incl _
  refine Eq.trans (congrArg Q.incl ?_) (Q.mul_incl _ _).symm
  exact ((SchemeDeformationCategory.pulledIdeal A X).val.map_smul (ascendHom Q U)
      ((solutionReduction Q).hom.app U a) x).trans (congrArg (· • _) hc)

/-- **The pulled-back ideal of the closed point is free**, of rank `dim_k 𝔪_A`, when the maximal
ideal of `A` has square zero: the conormal sheaf of the closed point is free
(`Deformation.Examples.residueConormalIsoFree`) and pullback preserves free sheaves. -/
noncomputable def pulledIdealIsoFree (A : ArtinianLocalAlgCat.{u, u, u} Λ k)
    (X : Over (Spec (CommRingCat.of k)))
    (hA : IsLocalRing.maximalIdeal (A : Type u) ^ 2 = ⊥) :
    SchemeDeformationCategory.pulledIdeal A X ≅
      SheafOfModules.free (R := structureSheafRing X.left.toRingedSpace)
        (ULift.{u} (Fin (residueKerRank A hA))) :=
  haveI := residueSpecMap_isClosedImmersion A
  (modulePullback X.hom.toLRSHom.toShHom).mapIso
      (Stacks.Immersion.conormalSheafSelfIso (residueSpecMap A) ≪≫ residueConormalIsoFree A hA) ≪≫
    modulePullbackFreeIso X.hom.toLRSHom.toShHom _

/-- The pulled-back ideal of the closed point is quasi-coherent. -/
theorem isQuasicoherent_pulledIdeal (A : ArtinianLocalAlgCat.{u, u, u} Λ k)
    (X : Over (Spec (CommRingCat.of k)))
    (hA : IsLocalRing.maximalIdeal (A : Type u) ^ 2 = ⊥) :
    (SchemeDeformationCategory.pulledIdeal A X).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent _).prop_of_iso (pulledIdealIsoFree A X hA).symm
    (inferInstance : (SheafOfModules.free (R := structureSheafRing X.left.toRingedSpace)
        (ULift.{u} (Fin (residueKerRank A hA)))).IsQuasicoherent)

/-- **The square-zero extension of `𝒪_X` over `Spec A` underlying a solution**, read on `|X|`
through the homeomorphism of the thickening. -/
noncomputable def solutionSquareZeroExtension
    (hG : (SchemeDeformationCategory.pulledIdeal A X).IsQuasicoherent) :
    Stacks.Thickenings.SquareZeroExtension (X.hom ≫ residueSpecMap A) where
  A := solutionSheaf Q
  π := solutionReduction Q
  locallySurjective_π := Q.isLocallySurjective_thickenedReduction
  inclusion := solutionInclusion Q
  inclusion_base := rfl
  inclusion_sheaf := HEq.rfl
  toBase := solutionToBase Q
  over_base := solutionInclusion_comp_toBase Q
  I := SchemeDeformationCategory.pulledIdeal A X
  quasicoherent := hG
  ι := solutionKernelInclusion Q
  naturality := solutionKernelInclusion_naturality Q
  mem_kernel := solutionKernelInclusion_mem_kernel Q
  exact_kernel := solutionKernelInclusion_exact Q
  smul_lift := solutionKernelInclusion_smul Q
  square_zero := solutionKernelInclusion_square_zero Q

/-! ### The deformation realizing a solution -/

variable (hA : IsLocalRing.maximalIdeal (A : Type u) ^ 2 = ⊥)

/-- A scheme realizing the square-zero extension underlying a solution ([Stacks Project, Tag
05YV]). -/
noncomputable def solutionRealization :
    Stacks.Thickenings.Realization
      (solutionSquareZeroExtension Q (isQuasicoherent_pulledIdeal A X hA)) :=
  (Stacks.Thickenings.squareZeroExtension_realization _).some

/-- The realizing scheme is the deformed space of the solution, as ringed spaces. -/
noncomputable def solutionRealizationIso :
    (solutionRealization Q hA).ambient.toSheafedSpace ≅ (Q.X' : SheafedSpace CommRingCat.{u}) :=
  (solutionRealization Q hA).sheafedIso ≪≫ (solutionSheafedIso Q).symm

/-- The immersion of the realizing scheme followed by `solutionRealizationIso` is the closed
immersion `Q.i` of the solution. -/
theorem immersion_comp_solutionRealizationIso :
    (solutionRealization Q hA).immersion.toLRSHom.toShHom ≫ (solutionRealizationIso Q hA).hom =
      Q.i := by
  calc (solutionRealization Q hA).immersion.toLRSHom.toShHom ≫
        ((solutionRealization Q hA).sheafedIso.hom ≫ (solutionSheafedIso Q).inv)
      = ((solutionRealization Q hA).immersion.toLRSHom.toShHom ≫
          (solutionRealization Q hA).sheafedIso.hom) ≫ (solutionSheafedIso Q).inv :=
        (Category.assoc _ _ _).symm
    _ = (Q.i ≫ (solutionSheafedIso Q).hom) ≫ (solutionSheafedIso Q).inv := by
        rw [(solutionRealization Q hA).inclusion_eq, i_comp_solutionSheafedIso Q]
        rfl
    _ = Q.i := by rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- `solutionRealizationIso` followed by the structure morphism `Q.f'` of the solution is the
structure morphism of the realizing scheme to the base. -/
theorem solutionRealizationIso_comp_f' :
    (solutionRealizationIso Q hA).hom ≫ Q.f' =
      (solutionRealization Q hA).toBase.toLRSHom.toShHom := by
  have h : (solutionRealization Q hA).sheafedIso.inv ≫
      (solutionRealization Q hA).toBase.toLRSHom.toShHom = solutionToBase Q :=
    (solutionRealization Q hA).toBase_eq
  calc ((solutionRealization Q hA).sheafedIso.hom ≫ (solutionSheafedIso Q).inv) ≫ Q.f'
      = (solutionRealization Q hA).sheafedIso.hom ≫ solutionToBase Q := Category.assoc _ _ _
    _ = (solutionRealization Q hA).toBase.toLRSHom.toShHom := by
        rw [← h, Iso.hom_inv_id_assoc]

/-- **Every solution of the deformation problem of Stacks 08U7 for `Spec k ⊂ Spec A`, `f^* 𝒥` and
the identity is isomorphic to the solution of a deformation of `X` over `A`.** The realizing scheme
of [Stacks Project, Tag 05YV] is a first order thickening of `X` over `Spec A` isomorphic to the
deformed space; its first-order ideal map is invertible because that of the solution is (the
prescribed map being invertible), so by condition (2) ⟹ (1) of [Stacks Project, Tag 063Y] it is
flat over `Spec A` with special fibre `X`. -/
theorem exists_isomorphic_fiberSolution :
    ∃ x : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).Fiber A,
      Isomorphic (fiberSolution hA x) Q := by
  let R := solutionRealization Q hA
  have hiS : Stacks.Thickenings.IsFirstOrderThickening R.immersion := R.immersion_isFirstOrder
  have : IsClosedImmersion R.immersion := hiS.1
  have := residueSpecMap_isClosedImmersion A
  have hi : IsFirstOrderThickening R.immersion.toLRSHom.toShHom :=
    Stacks.Thickenings.isFirstOrderThickening_toShHom _ hiS.2
  have comm : R.immersion ≫ R.toBase = X.hom ≫ residueSpecMap A := R.over_base
  have commRS := Stacks.Immersion.toShHom_square comm
  let e := solutionRealizationIso Q hA
  have th₀ := immersion_comp_solutionRealizationIso Q hA
  have bh₀ := solutionRealizationIso_comp_f' Q hA
  have th : Q.i ≫ e.inv = R.immersion.toLRSHom.toShHom := by
    rw [← th₀, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have bh : e.inv ≫ R.toBase.toLRSHom.toShHom = Q.f' := by
    rw [← bh₀, Iso.inv_hom_id_assoc]
  have hQ := Q.isIso_firstOrderIdealMap
  have hY : IsIso ((thickeningSquare ht R.immersion.toLRSHom.toShHom
      R.toBase.toLRSHom.toShHom hi commRS).firstOrderIdealMap hi ht).1 :=
    isIso_firstOrderIdealMap_of_iso (ht := ht) Q.i Q.f' Q.i_firstOrder Q.comm
      R.immersion.toLRSHom.toShHom R.toBase.toLRSHom.toShHom hi commRS e.inv th bh
  have hc := MorphismOfThickenings.isIso_conormalSheafMap_of_isIso
    (thickeningSquare ht R.immersion.toLRSHom.toShHom R.toBase.toLRSHom.toShHom hi commRS) hi ht
  have hiso : IsIso (Stacks.Immersion.immersionConormalSheafMap R.immersion (residueSpecMap A)
      X.hom R.toBase commRS) := by
    rw [Stacks.Immersion.immersionConormalSheafMap]
    exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' hc inferInstance)
  have : Flat X.hom := flat_of_isField_stalk X.hom fun _ => isField_stalk_Spec_field k _
  obtain ⟨hflat, hpb⟩ := Stacks.Thickenings.flat_and_isPullback_of_isIso_immersionConormalSheafMap
    R.immersion (residueSpecMap A) X.hom R.toBase comm hiS.2 (residueSpecMap_ker_sq_eq_bot A hA)
    hiso
  let P : SchemeDeformationCategory (Λ := Λ) (k := k) X :=
    { base := A, scheme := R.ambient, toBase := R.toBase, flat := hflat,
      specialMap := R.immersion, specialCartesian := hpb }
  refine ⟨⟨P, rfl⟩, isomorphic_of_comm e.hom th₀ ?_⟩
  refine bh₀.trans ?_
  show R.toBase.toLRSHom.toShHom = (R.toBase ≫ eqToHom rfl).toLRSHom.toShHom
  rw [eqToHom_refl, Category.comp_id]

/-- **The isomorphism classes of the fibre of the deformation category of `X` over `A` are the
isomorphism classes of solutions of the deformation problem of Stacks 08U7** for `Spec k ⊂ Spec A`,
`f^* 𝒥` and the identity, for any setoid on solutions whose relation is
`AlgebraicGeometry.RingedSpaceThickening.Isomorphic`. This is the identification of flat
deformations with solutions made in the proof of [Stacks Project, Tag 0D14]: a deformation goes to
its solution (`Deformation.Examples.fiberSolution`), isomorphic deformations to isomorphic
solutions and conversely, and every solution is realized
(`Deformation.Examples.exists_isomorphic_fiberSolution`). -/
noncomputable def fiberClassesEquivSolutionClasses
    (r : Setoid (DeformationSolution (residueSpecMap A).toLRSHom.toShHom
      (residueSpecMap_isFirstOrderThickening A hA) X.hom.toLRSHom.toShHom
      (SchemeDeformationCategory.pulledIdeal A X) (𝟙 _)))
    (hr : ∀ Q₁ Q₂, r Q₁ Q₂ ↔ Isomorphic Q₁ Q₂) :
    Quotient (isIsomorphicSetoid ((schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).Fiber
      A)) ≃ Quotient r :=
  Equiv.ofBijective
    (Quotient.lift (fun x => Quotient.mk r (fiberSolution hA x)) fun _ _ ⟨e⟩ =>
      Quotient.sound ((hr _ _).2 (isomorphic_fiberSolution_of_hom hA e.inv)))
    ⟨fun a b => Quotient.inductionOn₂ a b fun x y h =>
      Quotient.sound ((isIsomorphicSetoid _).symm
        (isIsomorphic_of_isomorphic_fiberSolution hA ((hr _ _).1 (Quotient.exact h)))),
     fun q => Quotient.inductionOn q fun Q => by
      obtain ⟨x, hx⟩ := exists_isomorphic_fiberSolution Q hA
      exact ⟨Quotient.mk _ x, Quotient.sound ((hr _ _).2 hx)⟩⟩

end Deformation.Examples

end
