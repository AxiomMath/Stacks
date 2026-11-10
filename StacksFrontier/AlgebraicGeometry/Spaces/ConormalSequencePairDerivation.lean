module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequencePairKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.LiftDifferenceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSharpCompSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQuasicoherentRightAdjoint
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceComplex
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleFunctorial
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardDerivation

/-!
# The conormal sequence of a pair of closed subspaces, in cokernel form

Let `Z ⊆ X` be a thickening of algebraic spaces over a scheme `S`, with inclusion `i` and
defining ideal `𝓘`, and let `g : X ⟶ X'` restrict to an isomorphism `f` of `Z` onto a closed
subspace `W ⊆ X'` with defining ideal `𝓙`.  For a base `q : X' ⟶ Y` this file proves that every
morphism `k : 𝒞_{Z/X} ⟶ M` of `𝒪_Z`-modules killed by the conormal map
`f^*𝒞_{W/X'} ⟶ 𝒞_{Z/X}` of Stacks 04CP factors through the first arrow
`𝒞_{Z/X} ⟶ i^*Ω_{X/Y}` of Stacks 05ZA.  This is exactness at `𝒞_{Z/X}` of the sequence of
Stacks 067L for the two closed immersions `Z ⟶ X` and `Z ⟶ X'`, in the form in which a cokernel
is tested.

The proof is the one of Algebra, Lemma 065V, carried out on the small étale site of `X`.  For a
ring map `A ⟶ B` inducing an isomorphism `A/J ≅ B/I`, an `A`-linear map `κ : I ⟶ M` killing the
image of `J` extends to the `A`-derivation `b ↦ κ(b - a)` of `B`, where `a ∈ A` is any element
with the same image as `b` in `B/I`.  On the site the choice of `a` is only possible locally, so
the derivation is built on the sheaf of rings of pairs
`AlgebraicGeometry.Space.subspaceFibreRing`, the fibre product `𝒪_X ×_{i_*𝒪_Z} g^{-1}𝒪_{X'}`,
as the datum `(b, a) ↦ κ(b - g^♯(a))` (`AlgebraicGeometry.Space.subspaceFibreQuotientDerivation`),
and descended along the locally surjective first projection by
`Stacks.Sites.QuotientDerivation.descend`.  The two geometric inputs — that the first projection
is locally surjective and that the datum kills the sections with vanishing first component —
are the two facts of `StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequencePairKernel.lean`.

The file also proves the vanishing of the composite of the two arrows when `Ω_{X'/Y}` vanishes:
a `Y`-derivation of `𝒪_X` composed with `g^♯` is a `Y`-derivation of `𝒪_{X'}`, hence zero.

## Main definitions

* `AlgebraicGeometry.Space.subspaceFibreRing`: the sheaf of rings of pairs.
* `AlgebraicGeometry.Space.subspaceFibreQuotientDerivation`: the datum `(b, a) ↦ κ(b - g^♯(a))`.

## Main results

* `AlgebraicGeometry.Space.exists_conormalSequenceIdealPullbackMap_comp_eq`: the factorization,
  stated for the transpose `κ` of `k`.
* `AlgebraicGeometry.Space.conormalMap_comp_eq_zero_iff`: `k` is killed by the conormal map
  exactly when its transpose is killed by the map of defining ideal sheaves.
* `AlgebraicGeometry.Space.idealSheafMap_comp_conormalSequenceIdealDifferential_eq_zero`: the
  composite vanishes when `Ω_{X'/Y}` does.

## References

* [Stacks Project, Tag 065V](https://stacks.math.columbia.edu/tag/065V)
* [Stacks Project, Tag 067L](https://stacks.math.columbia.edu/tag/067L)
* [Stacks Project, Tag 05ZA](https://stacks.math.columbia.edu/tag/05ZA)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 0619](https://stacks.math.columbia.edu/tag/0619)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Sites

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pullbacks of sheaves of rings on the small étale site, as a shortcut instance for
`HasLimit (cospan f g)`. -/
instance (priority := high) hasPullback_sheafRingCat_conormalSequencePairDerivation
    {X : AlgebraicSpaces B S hS} {P Q R : Sheaf (SmallEtale.topology B S hS X.1) RingCat.{u}}
    (f : P ⟶ R) (g : Q ⟶ R) : HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

section Construction

variable {X X' : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1) (g : X ⟶ X')

/-- The sheaf of rings of pairs `(b, a)` of a section `b` of `𝒪_X` and a section `a` of
`g^{-1}𝒪_{X'}` with the same image in `i_*𝒪_Z`. -/
noncomputable abbrev subspaceFibreRing : Sheaf (SmallEtale.topology B S hS X.1) RingCat.{u} :=
  pullback (structureSharp B S hS (subspaceInclusion B S hS X Z))
    (structureSharpRingInverseImage B S hS g ≫ structureSharp B S hS (subspaceInclusion B S hS X Z))

/-- The first projection of `AlgebraicGeometry.Space.subspaceFibreRing`. -/
noncomputable abbrev subspaceFibreRingFst :
    subspaceFibreRing B S hS Z g ⟶ structureRingSheaf B S hS X :=
  pullback.fst _ _

/-- The second projection of `AlgebraicGeometry.Space.subspaceFibreRing`. -/
noncomputable abbrev subspaceFibreRingSnd :
    subspaceFibreRing B S hS Z g ⟶ structureRingSheafInverseImage B S hS g :=
  pullback.snd _ _

/-- The two components of a section of `AlgebraicGeometry.Space.subspaceFibreRing` have the same
image in `i_*𝒪_Z`. -/
theorem subspaceFibreRing_condition_app (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (x : (subspaceFibreRing B S hS Z g).obj.obj U) :
    ((structureSharp B S hS (subspaceInclusion B S hS X Z)).hom.app U).hom
        (((subspaceFibreRingFst B S hS Z g).hom.app U).hom x) =
      ((structureSharp B S hS (subspaceInclusion B S hS X Z)).hom.app U).hom
        (((structureSharpRingInverseImage B S hS g).hom.app U).hom
          (((subspaceFibreRingSnd B S hS Z g).hom.app U).hom x)) :=
  ConcreteCategory.congr_hom (congrArg (fun m ↦ m.hom.app U) (pullback.condition (f :=
    structureSharp B S hS (subspaceInclusion B S hS X Z))
        (g := structureSharpRingInverseImage B S hS g ≫
      structureSharp B S hS (subspaceInclusion B S hS X Z)))) x

/-- A pair of sections with the same image in `i_*𝒪_Z` is a section of
`AlgebraicGeometry.Space.subspaceFibreRing`. -/
theorem exists_subspaceFibreRing (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (b : (structureRingSheaf B S hS X).obj.obj U)
    (a : (structureRingSheafInverseImage B S hS g).obj.obj U)
    (h : ((structureSharp B S hS (subspaceInclusion B S hS X Z)).hom.app U).hom b =
      ((structureSharp B S hS (subspaceInclusion B S hS X Z)).hom.app U).hom
        (((structureSharpRingInverseImage B S hS g).hom.app U).hom a)) :
    ∃ x : (subspaceFibreRing B S hS Z g).obj.obj U,
        ((subspaceFibreRingFst B S hS Z g).hom.app U).hom x = b ∧
      ((subspaceFibreRingSnd B S hS Z g).hom.app U).hom x = a := by
  let F := sheafToPresheaf (SmallEtale.topology B S hS X.1) RingCat.{u} ⋙ (evaluation _ _).obj U ⋙
    forget RingCat.{u}
  have hP := (IsPullback.of_hasPullback (structureSharp B S hS (subspaceInclusion B S hS X Z))
    (structureSharpRingInverseImage B S hS g ≫
      structureSharp B S hS (subspaceInclusion B S hS X Z))).map F
  have hw : (↾fun _ : PUnit.{u + 1} ↦ b) ≫ F.map
      (structureSharp B S hS (subspaceInclusion B S hS X Z)) =
      (↾fun _ : PUnit.{u + 1} ↦ a) ≫ F.map (structureSharpRingInverseImage B S hS g ≫
        structureSharp B S hS (subspaceInclusion B S hS X Z)) := by
    ext _
    exact h
  exact ⟨hP.lift _ _ hw PUnit.unit, ConcreteCategory.congr_hom (hP.lift_fst _ _ hw) PUnit.unit,
    ConcreteCategory.congr_hom (hP.lift_snd _ _ hw) PUnit.unit⟩

/-- The section `b - g^♯(a)` of the defining ideal sheaf of `Z` attached to a section `(b, a)` of
`AlgebraicGeometry.Space.subspaceFibreRing`. -/
noncomputable def subspaceFibreRingIdeal (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (x : (subspaceFibreRing B S hS Z g).obj.obj U) :
    (definingIdealSheaf B S hS X Z).toSheafOfModules.val.obj U :=
  ⟨((subspaceFibreRingFst B S hS Z g).hom.app U).hom x -
      ((structureSharpRingInverseImage B S hS g).hom.app U).hom
        (((subspaceFibreRingSnd B S hS Z g).hom.app U).hom x),
    (mem_definingIdealAt_iff B S hS X Z U _).2 (by
      rw [map_sub, subspaceFibreRing_condition_app, sub_self])⟩

/-- The value of `AlgebraicGeometry.Space.subspaceFibreRingIdeal`. -/
@[simp]
theorem subspaceFibreRingIdeal_coe (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (x : (subspaceFibreRing B S hS Z g).obj.obj U) :
    (subspaceFibreRingIdeal B S hS Z g U x).1 =
        ((subspaceFibreRingFst B S hS Z g).hom.app U).hom x -
      ((structureSharpRingInverseImage B S hS g).hom.app U).hom
        (((subspaceFibreRingSnd B S hS Z g).hom.app U).hom x) :=
  rfl

/-- `AlgebraicGeometry.Space.subspaceFibreRingIdeal` is additive. -/
theorem subspaceFibreRingIdeal_add (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (x y : (subspaceFibreRing B S hS Z g).obj.obj U) :
    subspaceFibreRingIdeal B S hS Z g U (x + y) =
        subspaceFibreRingIdeal B S hS Z g U x + subspaceFibreRingIdeal B S hS Z g U y :=
  Subtype.ext (by
    change _ = (subspaceFibreRingIdeal B S hS Z g U x).1 + (subspaceFibreRingIdeal B S hS Z g U y).1
    simp only [subspaceFibreRingIdeal_coe, map_add]
    abel)

/-- `AlgebraicGeometry.Space.subspaceFibreRingIdeal` commutes with restriction. -/
theorem subspaceFibreRingIdeal_map {U V : (SmallEtale B S hS X.1)ᵒᵖ} (h : U ⟶ V)
    (x : (subspaceFibreRing B S hS Z g).obj.obj U) :
    subspaceFibreRingIdeal B S hS Z g V (((subspaceFibreRing B S hS Z g).obj.map h).hom x) =
      (definingIdealSheaf B S hS X Z).toSheafOfModules.val.map h
          (subspaceFibreRingIdeal B S hS Z g U x) := by
  refine Subtype.ext ?_
  change _ = ((structureRingSheaf B S hS X).obj.map h).hom (subspaceFibreRingIdeal B S hS Z g U x).1
  have h1 := NatTrans.naturality_apply (subspaceFibreRingFst B S hS Z g).hom h x
  have h2 := NatTrans.naturality_apply (subspaceFibreRingSnd B S hS Z g).hom h x
  have h3 := NatTrans.naturality_apply (structureSharpRingInverseImage B S hS g).hom h
    (((subspaceFibreRingSnd B S hS Z g).hom.app U).hom x)
  simp only [subspaceFibreRingIdeal_coe, map_sub]
  rw [h1, h2, h3]

/-- The Leibniz rule for `AlgebraicGeometry.Space.subspaceFibreRingIdeal`:
`bb' - g^♯(aa') = b(b' - g^♯a') + g^♯(a')(b - g^♯a)`. -/
theorem subspaceFibreRingIdeal_mul (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (x y : (subspaceFibreRing B S hS Z g).obj.obj U) :
    subspaceFibreRingIdeal B S hS Z g U (x * y) =
      ((subspaceFibreRingFst B S hS Z g).hom.app U).hom x • subspaceFibreRingIdeal B S hS Z g U y +
        ((structureSharpRingInverseImage B S hS g).hom.app U).hom
          (((subspaceFibreRingSnd B S hS Z g).hom.app U).hom y) • subspaceFibreRingIdeal B S hS Z g
              U x := by
  refine Subtype.ext ?_
  change ((subspaceFibreRingFst B S hS Z g).hom.app U).hom (x * y) -
      ((structureSharpRingInverseImage B S hS g).hom.app U).hom
        (((subspaceFibreRingSnd B S hS Z g).hom.app U).hom (x * y)) =
    ((subspaceFibreRingFst B S hS Z g).hom.app U).hom x *
        (((subspaceFibreRingFst B S hS Z g).hom.app U).hom y -
      ((structureSharpRingInverseImage B S hS g).hom.app U).hom
        (((subspaceFibreRingSnd B S hS Z g).hom.app U).hom y)) +
    ((structureSharpRingInverseImage B S hS g).hom.app U).hom
        (((subspaceFibreRingSnd B S hS Z g).hom.app U).hom y) *
      (((subspaceFibreRingFst B S hS Z g).hom.app U).hom x -
      ((structureSharpRingInverseImage B S hS g).hom.app U).hom
        (((subspaceFibreRingSnd B S hS Z g).hom.app U).hom x))
  simp only [map_mul]
  have hcomm : ∀ p q : (structureRingSheaf B S hS X).obj.obj U, p * q = q * p :=
    fun p q ↦ ringSheaf_mul_comm_smallEtaleRingedSite B S hS X U p q
  have hc := hcomm (((structureSharpRingInverseImage B S hS g).hom.app U).hom
      (((subspaceFibreRingSnd B S hS Z g).hom.app U).hom y))
          (((subspaceFibreRingFst B S hS Z g).hom.app U).hom x)
  have hc' := hcomm
    (((structureSharpRingInverseImage B S hS g).hom.app U).hom
      (((subspaceFibreRingSnd B S hS Z g).hom.app U).hom y))
    (((structureSharpRingInverseImage B S hS g).hom.app U).hom
      (((subspaceFibreRingSnd B S hS Z g).hom.app U).hom x))
  rw [mul_sub, mul_sub, hc, hc']
  abel

variable (W : ClosedSubspaces B S hS X'.1)
  (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨W.1.toFunctor, W.2.1⟩ : AlgebraicSpaces B S hS))
  (M : Modules.{u, u} B S hS Z.1.toFunctor Z.2.1)
  (κ : (definingIdealSheaf B S hS X Z).toSheafOfModules ⟶
    (modulePushforward B S hS (subspaceInclusion B S hS X Z)).obj M)

/-- The direct image `i_*M`, read as a sheaf of modules over
`AlgebraicGeometry.Space.structureRingSheaf`. -/
noncomputable abbrev subspaceDirectImageModule : SheafOfModules.{u} (structureRingSheaf B S hS X) :=
  (modulePushforward B S hS (subspaceInclusion B S hS X Z)).obj M

/-- The additive map `(b, a) ↦ κ(b - g^♯(a))` on the sections of the ring of pairs. -/
noncomputable def subspaceFibreDerivationFun (U : (SmallEtale B S hS X.1)ᵒᵖ) :
    (subspaceFibreRing B S hS Z g).obj.obj U →+ (subspaceDirectImageModule B S hS Z M).val.obj U :=
  AddMonoidHom.mk' (fun x ↦ (κ.val.app U).hom (subspaceFibreRingIdeal B S hS Z g U x))
    (fun x y ↦ by rw [subspaceFibreRingIdeal_add, map_add])

/-- The value of `AlgebraicGeometry.Space.subspaceFibreDerivationFun`. -/
theorem subspaceFibreDerivationFun_apply (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (x : (subspaceFibreRing B S hS Z g).obj.obj U) :
    subspaceFibreDerivationFun B S hS Z g M κ U x = (κ.val.app U).hom
        (subspaceFibreRingIdeal B S hS Z g U x) :=
  rfl

/-- The Leibniz rule for `AlgebraicGeometry.Space.subspaceFibreDerivationFun`, for the action of
`𝒪_X` through the first projection: the defining ideal of `Z` kills `i_*M`. -/
theorem subspaceFibreDerivationFun_mul (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (x y : (subspaceFibreRing B S hS Z g).obj.obj U) :
    subspaceFibreDerivationFun B S hS Z g M κ U (x * y) =
      ((subspaceFibreRingFst B S hS Z g).hom.app U).hom x • subspaceFibreDerivationFun B S hS Z g M
          κ U y +
        ((subspaceFibreRingFst B S hS Z g).hom.app U).hom y • subspaceFibreDerivationFun B S hS Z g
            M κ U x := by
  rw [subspaceFibreDerivationFun_apply, subspaceFibreDerivationFun_apply,
    subspaceFibreDerivationFun_apply, subspaceFibreRingIdeal_mul, map_add, map_smul, map_smul]
  congr 1
  have h0 := definingIdealAt_smul_modulePushforward_eq_zero B S hS Z M U _
    (subspaceFibreRingIdeal B S hS Z g U y).2
    ((κ.val.app U).hom (subspaceFibreRingIdeal B S hS Z g U x))
  exact (sub_eq_zero.mp ((sub_smul _ _ _).symm.trans h0)).symm

/-- `AlgebraicGeometry.Space.subspaceFibreDerivationFun` commutes with restriction. -/
theorem subspaceFibreDerivationFun_map {U V : (SmallEtale B S hS X.1)ᵒᵖ} (h : U ⟶ V)
    (x : (subspaceFibreRing B S hS Z g).obj.obj U) :
    subspaceFibreDerivationFun B S hS Z g M κ V (((subspaceFibreRing B S hS Z g).obj.map h).hom x) =
      (subspaceDirectImageModule B S hS Z M).val.map h
          (subspaceFibreDerivationFun B S hS Z g M κ U x) := by
  rw [subspaceFibreDerivationFun_apply, subspaceFibreDerivationFun_apply,
      subspaceFibreRingIdeal_map]
  exact PresheafOfModules.naturality_apply κ.val h (subspaceFibreRingIdeal B S hS Z g U x)

/-- `AlgebraicGeometry.Space.subspaceFibreDerivationFun` kills the sections whose first component
vanishes: such a section is `(0, a)` with `g^♯(a)` in the defining ideal of `Z`, and `κ` kills
`g^♯(a)` because it kills the image of `g^*𝓙`. -/
theorem subspaceFibreDerivationFun_eq_zero (hZ : IsThickening B S hS X Z.1) [IsIso f]
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' W)
    (hκ : idealSheafMap B S hS Z W g f hsq ≫ κ = 0) (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (x : (subspaceFibreRing B S hS Z g).obj.obj U)
        (hx : ((subspaceFibreRingFst B S hS Z g).hom.app U).hom x = 0) :
    subspaceFibreDerivationFun B S hS Z g M κ U x = 0 := by
  rw [subspaceFibreDerivationFun_apply]
  have hmem : ((structureSharpRingInverseImage B S hS g).hom.app U).hom
      (((subspaceFibreRingSnd B S hS Z g).hom.app U).hom x) ∈ definingIdealAt B S hS X Z U := by
    have h := (subspaceFibreRingIdeal B S hS Z g U x).2
    rw [subspaceFibreRingIdeal_coe, hx, zero_sub] at h
    simpa using (definingIdealAt B S hS X Z U).neg_mem h
  have he : subspaceFibreRingIdeal B S hS Z g U x = -⟨_, hmem⟩ := by
    refine Subtype.ext ?_
    rw [subspaceFibreRingIdeal_coe, hx, zero_sub]
    rfl
  rw [he]
  refine (map_neg (κ.val.app U).hom _).trans ?_
  rw [app_structureSharpRingInverseImage_eq_zero_of_idealSheafMap_comp_eq_zero B S hS Z W g f hZ
      hsq κ hκ U _ hmem, neg_zero]

/-- **The derivation datum on the ring of pairs**: `(b, a) ↦ κ(b - g^♯(a))`. -/
noncomputable def subspaceFibreQuotientDerivation (hZ : IsThickening B S hS X Z.1) [IsIso f]
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' W)
    (hκ : idealSheafMap B S hS Z W g f hsq ≫ κ = 0) :
    QuotientDerivation (subspaceFibreRingFst B S hS Z g)
        (subspaceDirectImageModule B S hS Z M) where
  d {U} := subspaceFibreDerivationFun B S hS Z g M κ U
  d_mul := subspaceFibreDerivationFun_mul B S hS Z g M κ _
  d_map h x := subspaceFibreDerivationFun_map B S hS Z g M κ h x
  d_eq_zero_of_app_eq_zero x hx :=
    subspaceFibreDerivationFun_eq_zero B S hS Z g W f M κ hZ hsq hκ _ x hx

/-- The first projection of `AlgebraicGeometry.Space.subspaceFibreRing` is locally surjective. -/
theorem isLocallySurjective_subspaceFibreRingFst (hZ : IsThickening B S hS X Z.1) [IsIso f]
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' W) :
    Sheaf.IsLocallySurjective (subspaceFibreRingFst B S hS Z g) where
  imageSieve_mem {U} b := by
    obtain ⟨T, hT, hTb⟩ := exists_sub_mem_definingIdealAt B S hS Z W g f hZ hsq (op U) b
    refine (SmallEtale.topology B S hS X.1).superset_covering (fun V h hh ↦ ?_) hT
    obtain ⟨c, hc⟩ := hTb V h hh
    have hc' := (mem_definingIdealAt_iff B S hS X Z (op V) _).1 hc
    rw [map_sub, sub_eq_zero] at hc'
    obtain ⟨x, hx, -⟩ := exists_subspaceFibreRing B S hS Z g (op V) _ c hc'
    exact ⟨x, hx⟩

/-- The descended derivation sends `b` to `κ(e)` whenever `b - g^♯(c) = e`. -/
private theorem subspaceFibreQuotientDerivation_descend_eq
    (hZ : IsThickening B S hS X Z.1) [IsIso f]
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' W)
    (hκ : idealSheafMap B S hS Z W g f hsq ≫ κ = 0) (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (b : (structureRingSheaf B S hS X).obj.obj U)
    (c : (structureRingSheafInverseImage B S hS g).obj.obj U)
    (e : (definingIdealSheaf B S hS X Z).toSheafOfModules.val.obj U)
    (h : b - ((structureSharpRingInverseImage B S hS g).hom.app U).hom c = e.1) :
    haveI := isLocallySurjective_subspaceFibreRingFst B S hS Z g W f hZ hsq
    (subspaceFibreQuotientDerivation B S hS Z g W f M κ hZ hsq hκ).descend b =
      (κ.val.app U).hom e := by
  have := isLocallySurjective_subspaceFibreRingFst B S hS Z g W f hZ hsq
  have hcond := (mem_definingIdealAt_iff B S hS X Z U e.1).1 e.2
  rw [← h, map_sub, sub_eq_zero] at hcond
  obtain ⟨x, hx, hx'⟩ := exists_subspaceFibreRing B S hS Z g U b c hcond
  rw [← hx, QuotientDerivation.descend_app]
  exact congrArg (κ.val.app U).hom (Subtype.ext (by rw [subspaceFibreRingIdeal_coe, hx, hx', h]))

/-- The descended derivation kills `g^♯(c)`. -/
theorem subspaceFibreQuotientDerivation_descend_structureSharpRingInverseImage
    (hZ : IsThickening B S hS X Z.1) [IsIso f]
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' W)
    (hκ : idealSheafMap B S hS Z W g f hsq ≫ κ = 0) (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (c : (structureRingSheafInverseImage B S hS g).obj.obj U) :
    haveI := isLocallySurjective_subspaceFibreRingFst B S hS Z g W f hZ hsq
    (subspaceFibreQuotientDerivation B S hS Z g W f M κ hZ hsq hκ).descend
      (((structureSharpRingInverseImage B S hS g).hom.app U).hom c) = 0 :=
  (subspaceFibreQuotientDerivation_descend_eq B S hS Z g W f M κ hZ hsq hκ U _ c 0
    (sub_self _)).trans (map_zero _)

/-- The descended derivation restricts to `κ` on the defining ideal of `Z`. -/
theorem subspaceFibreQuotientDerivation_descend_definingIdeal
    (hZ : IsThickening B S hS X Z.1) [IsIso f]
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' W)
    (hκ : idealSheafMap B S hS Z W g f hsq ≫ κ = 0) (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (e : (definingIdealSheaf B S hS X Z).toSheafOfModules.val.obj U) :
    haveI := isLocallySurjective_subspaceFibreRingFst B S hS Z g W f hZ hsq
    (subspaceFibreQuotientDerivation B S hS Z g W f M κ hZ hsq hκ).descend e.1 =
        (κ.val.app U).hom e :=
  subspaceFibreQuotientDerivation_descend_eq B S hS Z g W f M κ hZ hsq hκ U _ 0 e
    ((congrArg _ (map_zero _)).trans (sub_zero (e.1 : (structureRingSheaf B S hS X).obj.obj U)))

end Construction

section Factorization

variable {X X' Y : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1) (g : X ⟶ X')
  (W : ClosedSubspaces B S hS X'.1)
  (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨W.1.toFunctor, W.2.1⟩ : AlgebraicSpaces B S hS))
  (q : X' ⟶ Y) (M : Modules.{u, u} B S hS Z.1.toFunctor Z.2.1)
  (κ : (definingIdealSheaf B S hS X Z).toSheafOfModules ⟶
    (modulePushforward B S hS (subspaceInclusion B S hS X Z)).obj M)

/-- The descended derivation kills the sections read from the base along `g ≫ q`, which factor
through `g^♯`. -/
theorem subspaceFibreQuotientDerivation_descend_base (hZ : IsThickening B S hS X Z.1) [IsIso f]
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' W)
    (hκ : idealSheafMap B S hS Z W g f hsq ≫ κ = 0) (V : (SmallEtale B S hS X.1)ᵒᵖ)
    (s : (inverseImageStructureSheaf B S hS (g ≫ q)).obj.obj V) :
    haveI := isLocallySurjective_subspaceFibreRingFst B S hS Z g W f hZ hsq
    (subspaceFibreQuotientDerivation B S hS Z g W f M κ hZ hsq hκ).descend
      ((structureSharpInverseImage B S hS (g ≫ q)).hom.app V s) = 0 := by
  have harg : (structureSharpInverseImage B S hS (g ≫ q)).hom.app V s =
      (structureSharpRingInverseImage B S hS g).hom.app V
        (((Stacks.Sheaves.ToposPushforward.inverseImageRingFunctor
            (smallToposMorphismTypeU B S hS g)).map
          (structureSharpRingInverseImage B S hS q)).hom.app V
          (((smallEtaleRingedToposHom_compInverseImageRingIso B S hS g q).inv.app
            (smallEtaleRingedTopos B S hS Y).O).hom.app V s)) := by
    rw [app_structureSharpInverseImage_comp B S hS g q V s,
      app_inverseImage_structureSharpRingInverseImage B S hS g q V
        (((smallEtaleRingedToposHom_compInverseImageRingIso B S hS g q).inv.app
          (smallEtaleRingedTopos B S hS Y).O).hom.app V s),
      structureSharpRingInverseImage_eq_forget₂ B S hS g]
    rfl
  have := isLocallySurjective_subspaceFibreRingFst B S hS Z g W f hZ hsq
  refine Eq.trans (congrArg (fun z : (structureRingSheaf B S hS X).obj.obj V ↦
    (subspaceFibreQuotientDerivation B S hS Z g W f M κ hZ hsq hκ).descend z) harg) ?_
  exact subspaceFibreQuotientDerivation_descend_structureSharpRingInverseImage B S hS Z g W f M κ
    hZ hsq hκ V _

/-- The transpose `κ` of the factorization, as a property of the morphism `θ` out of the
pulled back differentials. -/
theorem conormalSequenceIdealDifferential_comp_map_descendedDifferentialsHom
    (hZ : IsThickening B S hS X Z.1) [IsIso f]
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' W)
    (hκ : idealSheafMap B S hS Z W g f hsq ≫ κ = 0) :
    haveI := isLocallySurjective_subspaceFibreRingFst B S hS Z g W f hZ hsq
    conormalSequenceIdealDifferential B S hS Z (g ≫ q) ≫
      (modulePushforward B S hS (subspaceInclusion B S hS X Z)).map
        (descendedDifferentialsHom B S hS (g ≫ q) (subspaceInclusion B S hS X Z) M
          (subspaceFibreQuotientDerivation B S hS Z g W f M κ hZ hsq hκ)
          (subspaceFibreQuotientDerivation_descend_base B S hS Z g W f q M κ hZ hsq hκ)) = κ := by
  have := isLocallySurjective_subspaceFibreRingFst B S hS Z g W f hZ hsq
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U ↦
    ModuleCat.hom_ext (LinearMap.ext fun e ↦ ?_))
  refine Eq.trans ?_ ((descendedDifferentialsHom_spec B S hS (g ≫ q)
      (subspaceInclusion B S hS X Z) M
          (subspaceFibreQuotientDerivation B S hS Z g W f M κ hZ hsq hκ)
      (subspaceFibreQuotientDerivation_descend_base B S hS Z g W f q M κ hZ hsq hκ) e.1).trans
    (subspaceFibreQuotientDerivation_descend_definingIdeal B S hS Z g W f M κ hZ hsq hκ U e))
  refine (congrArg (fun x ↦ (((modulePushforward B S hS (subspaceInclusion B S hS X Z)).map
      (descendedDifferentialsHom B S hS (g ≫ q) (subspaceInclusion B S hS X Z) M
        (subspaceFibreQuotientDerivation B S hS Z g W f M κ hZ hsq hκ)
        (subspaceFibreQuotientDerivation_descend_base B S hS Z g W f q M κ hZ hsq hκ))).val.app
            U).hom x)
    (conormalSequenceIdealDifferential_val_app_apply B S hS Z (g ≫ q) U e)).trans ?_
  rw [Adjunction.homEquiv_unit]
  rfl

/-- **The factorization through the first arrow of Stacks 05ZA.**  Let `Z ⊆ X` be a thickening,
let `g : X ⟶ X'` restrict to an isomorphism `f` of `Z` onto a closed subspace `W ⊆ X'`, and let
`q : X' ⟶ Y`.  Every morphism `k : i^*𝓘_Z ⟶ M` of `𝒪_Z`-modules whose transpose kills the image
of `g^*𝓘_W` factors through the first arrow `𝒞_{Z/X} ⟶ i^*Ω_{X/Y}` of Stacks 05ZA. -/
theorem exists_conormalSequenceIdealPullbackMap_comp_eq (hZ : IsThickening B S hS X Z.1) [IsIso f]
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' W)
    (hκ : idealSheafMap B S hS Z W g f hsq ≫ κ = 0) :
    ∃ h, conormalSequenceIdealPullbackMap B S hS Z (g ≫ q) ≫ h =
      ((modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z)).homEquiv _ _).symm κ := by
  have := isLocallySurjective_subspaceFibreRingFst B S hS Z g W f hZ hsq
  let θ := descendedDifferentialsHom B S hS (g ≫ q) (subspaceInclusion B S hS X Z) M
    (subspaceFibreQuotientDerivation B S hS Z g W f M κ hZ hsq hκ)
    (subspaceFibreQuotientDerivation_descend_base B S hS Z g W f q M κ hZ hsq hκ)
  have e1 : conormalSequenceIdealPullbackMap B S hS Z (g ≫ q) ≫ θ =
      ((modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z)).homEquiv _ _).symm
        (conormalSequenceIdealDifferential B S hS Z (g ≫ q) ≫
          (modulePushforward B S hS (subspaceInclusion B S hS X Z)).map θ) := by
    rw [conormalSequenceIdealPullbackMap_eq_homEquiv_symm]
    exact (Adjunction.homEquiv_naturality_right_symm
      (modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z))
      (conormalSequenceIdealDifferential B S hS Z (g ≫ q)) θ).symm
  exact ⟨θ, e1.trans (congrArg ((modulePullbackAdjunction B S hS
        (subspaceInclusion B S hS X Z)).homEquiv _ _).symm
      (conormalSequenceIdealDifferential_comp_map_descendedDifferentialsHom B S hS Z g W f q M κ hZ
        hsq hκ))⟩

end Factorization

section ConormalMap

variable {X X' : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1) (g : X ⟶ X')
  (W : ClosedSubspaces B S hS X'.1)
  (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨W.1.toFunctor, W.2.1⟩ : AlgebraicSpaces B S hS))
  (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' W)

private theorem comp_map_comp_eq_zero_iff {C D : Type*} [Category C] [Category D] [Preadditive C]
    [Preadditive D] {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive] (adj : L ⊣ R) {P Q : C}
    {T V : D} (c : T ⟶ L.obj P) [IsIso c] (a : P ⟶ Q) (k : L.obj Q ⟶ V) :
    (c ≫ L.map a) ≫ k = 0 ↔ a ≫ adj.homEquiv _ _ k = 0 := by
  rw [Category.assoc, Preadditive.IsIso.comp_left_eq_zero, ← Adjunction.homEquiv_naturality_left]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [h, Adjunction.homEquiv_unit, Functor.map_zero, Limits.comp_zero]
  · have := congrArg (adj.homEquiv _ _).symm h
    rwa [Equiv.symm_apply_apply, Adjunction.homEquiv_counit, Functor.map_zero,
      Limits.zero_comp] at this

attribute [local irreducible] modulePullback in
/-- **A morphism out of `𝒞_{Z/X}` is killed by the conormal map of Stacks 04CP exactly when its
transpose is killed by the map of defining ideal sheaves.** -/
theorem conormalMap_comp_eq_zero_iff {N : Modules.{u, u} B S hS Z.1.toFunctor Z.2.1}
    (k : (modulePullback B S hS (subspaceInclusion B S hS X Z)).obj
      (definingIdealSheaf B S hS X Z).toSheafOfModules ⟶ N) :
    conormalMap B S hS Z W g f hsq ≫ k = 0 ↔
      idealSheafMap B S hS Z W g f hsq ≫
        (modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z)).homEquiv _ _ k = 0 := by
  have := isIso_conormalPullbackComparison B S hS Z W g f hsq
  have := additive_modulePushforward B S hS (subspaceInclusion B S hS X Z)
  have := additive_modulePullback B S hS (subspaceInclusion B S hS X Z)
  unfold conormalMap
  exact comp_map_comp_eq_zero_iff
    (modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z))
    (conormalPullbackComparison B S hS Z W g f hsq) (idealSheafMap B S hS Z W g f hsq) k

end ConormalMap

section Composite

variable {X X' Y : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1) (g : X ⟶ X')
  (W : ClosedSubspaces B S hS X'.1)
  (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨W.1.toFunctor, W.2.1⟩ : AlgebraicSpaces B S hS))
  (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' W)

private theorem comp_eq_zero_of_homEquiv_comp_map_eq_zero {C D : Type*} [Category C]
    [Category D] [Preadditive C] [Preadditive D] {L : C ⥤ D} {R : D ⥤ C} [R.Additive]
    (adj : L ⊣ R) {P : C} {Q₁ Q₂ : D} (a : L.obj P ⟶ Q₁) (b : Q₁ ⟶ Q₂)
    (h : adj.homEquiv _ _ a ≫ R.map b = 0) : a ≫ b = 0 := by
  refine (adj.homEquiv _ _).injective ?_
  rw [Adjunction.homEquiv_naturality_right, h, Adjunction.homEquiv_unit, Functor.map_zero,
    Limits.comp_zero]

/-- A derivation relative to a morphism whose sheaf of differentials vanishes is zero. -/
theorem derivation_d_eq_zero_of_isZero_sheafOfDifferentials {T : AlgebraicSpaces B S hS}
    (q : X' ⟶ T)
    (hΩ : Limits.IsZero (sheafOfDifferentials B S hS q)) (G : Modules.{u, u} B S hS X'.1 X'.2)
    (E : PresheafOfModulesOfCommRing.Derivation' G.val (structureSharpInverseImage B S hS q).hom)
    (U : (SmallEtale B S hS X'.1)ᵒᵖ) (t : (structureRingSheaf B S hS X').obj.obj U) :
    E.d t = 0 := by
  have h := (differentialsHomEquiv B S hS q G).apply_symm_apply E
  rw [hΩ.eq_of_src ((differentialsHomEquiv B S hS q G).symm E) 0] at h
  rw [← h, differentialsHomEquiv_apply]
  rfl

/-- The underlying morphism of sheaves of sets of the adjoint form of the first arrow of
Stacks 05ZA is the inclusion of the ideal followed by the unit derivation. -/
theorem moduleSheafFunctor_map_conormalSequenceIdealDifferential (b : X ⟶ Y) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
        (conormalSequenceIdealDifferential B S hS Z b) =
      Stacks.Sheaves.ToposPullback.submoduleInclSheafSets (definingIdealSheaf B S hS X Z) ≫
        derivationHom B S hS b _ (conormalSequenceUnitDerivation B S hS Z b) :=
  Sheaf.hom_ext_sections fun U e ↦
    conormalSequenceIdealDifferential_val_app_apply B S hS Z b U e

/-- **The composite of the conormal map of Stacks 04CP and the first arrow of Stacks 05ZA
vanishes when the sheaf of differentials of the target over the base does.** -/
theorem idealSheafMap_comp_conormalSequenceIdealDifferential_eq_zero (q : X' ⟶ Y)
    (hΩ : Limits.IsZero (sheafOfDifferentials B S hS q)) :
    idealSheafMap B S hS Z W g f hsq ≫ conormalSequenceIdealDifferential B S hS Z (g ≫ q) = 0 := by
  have := additive_modulePushforward B S hS g
  refine comp_eq_zero_of_homEquiv_comp_map_eq_zero (modulePullbackAdjunction B S hS g)
    (idealSheafMap B S hS Z W g f hsq) (conormalSequenceIdealDifferential B S hS Z (g ≫ q)) ?_
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V ↦
    ModuleCat.hom_ext (LinearMap.ext fun s ↦ ?_))
  have key := congrArg (fun m ↦ m.hom.app V s)
    (moduleSheafFunctor_map_homEquiv_idealSheafMap_comp B S hS Z W g f hsq)
  let E := pushforwardDerivation B S hS (g ≫ q) _ (conormalSequenceUnitDerivation B S hS Z (g ≫ q))
    g q (𝟙 Y) (Category.comp_id _).symm
  have hE := derivation_d_eq_zero_of_isZero_sheafOfDifferentials B S hS q hΩ _ E V s.1
  refine Eq.trans ?_ (hE.trans rfl)
  change ((smallToposMorphismTypeU B S hS g).pushforward.map
      ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
        (conormalSequenceIdealDifferential B S hS Z (g ≫ q)))).hom.app V
      (((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X')).map
        ((modulePullbackAdjunction B S hS g).homEquiv _ _
          (idealSheafMap B S hS Z W g f hsq))).hom.app V s) = _
  rw [moduleSheafFunctor_map_conormalSequenceIdealDifferential B S hS Z (g ≫ q),
    Functor.map_comp]
  change ((smallToposMorphismTypeU B S hS g).pushforward.map
      (derivationHom B S hS (g ≫ q) _ (conormalSequenceUnitDerivation B S hS Z (g ≫ q)))).hom.app V
      (((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X')).map
        ((modulePullbackAdjunction B S hS g).homEquiv _ _ (idealSheafMap B S hS Z W g f hsq)) ≫
        (smallToposMorphismTypeU B S hS g).pushforward.map
          (Stacks.Sheaves.ToposPullback.submoduleInclSheafSets
            (definingIdealSheaf B S hS X Z))).hom.app V s) = _
  rw [key]
  rfl

end Composite

end AlgebraicGeometry.Space

end
