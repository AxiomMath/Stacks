module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorStalkRingedSpace
public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalCartier
public import StacksFrontier.AlgebraicGeometry.Blowup.IsomorphismOffCenter.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.Proper
public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierComplement
public import StacksFrontier.AlgebraicGeometry.Divisors.HartogsExtension.Basic
public import StacksFrontier.AlgebraicGeometry.F6Rank136.ExceptionalCurveContraction
public import StacksFrontier.AlgebraicGeometry.F6Rank147.ContractionUniversalProperty
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.DenseOpenImmersion
public import StacksFrontier.RingTheory.RegularLocalRing.Basic

/-!
# The universal property of contracting an exceptional curve of the first kind

Let `E ⊆ X` be an exceptional curve of the first kind on a Noetherian scheme, presented by its
ideal sheaf `D`, and let `b : X ⟶ X'` be a contraction of `E`. Every morphism `φ : X ⟶ Y` which
sends `E` to a single point factors through `b`, and the factorisation is unique.

The contraction is proper and is an isomorphism away from the point `x` it contracts `E` to, so
on underlying spaces it is the quotient identifying `E` to a point. The structure-sheaf
comparison `𝒪_{X'} ⟶ b_* 𝒪_X` is an isomorphism as well: away from `x` this is immediate, and
at `x` it follows because the local ring there is regular of dimension two, hence of depth two,
so sections of the structure sheaf extend across `x` and the Hartogs comparison for the
structure sheaf is invertible. These two facts identify `X'` with the quotient of `X` carrying
`b_* 𝒪_X`, which gives the factorisation and its uniqueness.

The contraction is therefore unique up to unique isomorphism: a contraction carries the curve to
a single point, so each of two contractions of one curve factors through the other, and the two
factorisations compose to the identity because the identity is itself the unique factorisation of
a contraction through itself. The isomorphism this produces is recorded as data rather than only
existentially, since a consumer that moves sheaves or divisors between the two targets needs the
map and not merely its existence.

## Main results

* `AlgebraicGeometry.existsUnique_comp_eq_of_isContractionOfExceptionalCurve` — the universal
  property: a morphism constant on the exceptional curve factors uniquely through the
  contraction.
* `AlgebraicGeometry.IsContractionOfExceptionalCurve.isIso_c` — the structure-sheaf comparison
  of a contraction is an isomorphism.
* `AlgebraicGeometry.IsContractionOfExceptionalCurve.isProper` and
  `AlgebraicGeometry.isIso_morphismRestrict_compl_of_blowUp_iso` — a contraction is proper and
  is an isomorphism over the complement of its centre.
* `AlgebraicGeometry.isIso_c_ι_of_depth_ge_two` — the comparison map of an open immersion of
  schemes is an isomorphism when the structure sheaf has depth at least two along the
  complement.
* `AlgebraicGeometry.existsUnique_iso_of_isContractionOfExceptionalCurve` — a contraction is
  unique up to unique isomorphism.
* `AlgebraicGeometry.IsContractionOfExceptionalCurve.exists_const_on_subscheme` — a contraction
  carries the curve it contracts to a single point, which is the hypothesis under which another
  morphism factors through it.

## Main definitions

* `AlgebraicGeometry.contractionIso` — the isomorphism between the targets of two contractions
  of one ideal sheaf, with the characterising equations
  `AlgebraicGeometry.contractionIso_hom_comp`, `AlgebraicGeometry.contractionIso_inv_comp` and
  `AlgebraicGeometry.eq_contractionIso`.

## References

* [Stacks Project, Tag 0C5J](https://stacks.math.columbia.edu/tag/0C5J)
* [Stacks Project, Tag 0C5K](https://stacks.math.columbia.edu/tag/0C5K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### The stalk of the structure sheaf as a module over itself -/

/-- The stalk of the structure sheaf viewed as a sheaf of modules over itself, identified with
the stalk of the sheaf of rings. -/
private noncomputable def unitStalkAddEquiv {X : TopCat.{u}}
    (R : X.Presheaf CommRingCat.{u}) (x : X) :
    TopCat.Presheaf.stalk (C := Ab.{u})
      (PresheafOfModules.unit (R ⋙ forget₂ _ RingCat)).presheaf x ≃+ R.stalk x :=
  (preservesColimitIso
    (forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u})
    ((TopologicalSpace.OpenNhds.inclusion x).op ⋙ R)).symm.addCommGroupIsoToAddEquiv

/-- `AlgebraicGeometry.unitStalkAddEquiv` carries the germ of a section to its germ as a ring
element. -/
private lemma unitStalkAddEquiv_germ {X : TopCat.{u}}
    (R : X.Presheaf CommRingCat.{u}) (x : X) (U : TopologicalSpace.Opens X)
    (hx : x ∈ U) (r : R.obj (.op U)) :
    unitStalkAddEquiv R x
      (TopCat.Presheaf.germ (PresheafOfModules.unit (R ⋙ forget₂ _ RingCat)).presheaf U x hx r) =
      R.germ U x hx r :=
  congrArg (fun f : AddCommGrpCat.of (R.obj (.op U)) ⟶ AddCommGrpCat.of (R.stalk x) ↦ f r)
    (ι_preservesColimitIso_inv
      (forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u})
      ((TopologicalSpace.OpenNhds.inclusion x).op ⋙ R) (.op ⟨U, hx⟩))

/-- `AlgebraicGeometry.unitStalkAddEquiv` is linear over the stalk of the sheaf of rings, the
scalar action on sections of the unit module being multiplication. -/
private noncomputable def unitStalkLinearEquiv {X : TopCat.{u}}
    (R : X.Presheaf CommRingCat.{u}) (x : X) :
    TopCat.Presheaf.stalk (C := Ab.{u})
      (PresheafOfModules.unit (R ⋙ forget₂ _ RingCat)).presheaf x ≃ₗ[R.stalk x]
      R.stalk x := by
  refine { unitStalkAddEquiv R x with map_smul' := ?_ }
  intro r m
  change unitStalkAddEquiv R x (r • m) = r • unitStalkAddEquiv R x m
  obtain ⟨U, hxU, a, rfl⟩ := R.exists_germ_eq r
  obtain ⟨V, hxV, b, rfl⟩ :=
    TopCat.Presheaf.exists_germ_eq (PresheafOfModules.unit (R ⋙ forget₂ _ RingCat)).presheaf m
  have hxUV : x ∈ U ⊓ V := ⟨hxU, hxV⟩
  -- The identity is proved with the section and the scalar as bound variables, where the germ
  -- lemmas apply to explicit arguments, and then instantiated on a common neighbourhood.
  have key : ∀ (W : TopologicalSpace.Opens X) (hxW : x ∈ W) (p s : R.obj (.op W)),
      unitStalkAddEquiv R x
          (R.germ W x hxW p • TopCat.Presheaf.germ
            (PresheafOfModules.unit (R ⋙ forget₂ _ RingCat)).presheaf W x hxW s) =
        R.germ W x hxW p *
          unitStalkAddEquiv R x
            (TopCat.Presheaf.germ
              (PresheafOfModules.unit (R ⋙ forget₂ _ RingCat)).presheaf W x hxW s) := by
    intro W hxW p s
    refine Eq.trans (congrArg (unitStalkAddEquiv R x)
      (PresheafOfModules.germ_smul (R := R)
        (PresheafOfModules.unit (R ⋙ forget₂ _ RingCat)) x W hxW p s).symm) ?_
    refine Eq.trans (unitStalkAddEquiv_germ R x W hxW (p * s)) ?_
    refine Eq.trans ((R.germ W x hxW).hom.map_mul p s) ?_
    exact congrArg (fun z => R.germ W x hxW p * z) (unitStalkAddEquiv_germ R x W hxW s).symm
  rw [← R.germ_res_apply (homOfLE (show U ⊓ V ≤ U from inf_le_left)) x hxUV a,
    ← TopCat.Presheaf.germ_res_apply (PresheafOfModules.unit (R ⋙ forget₂ _ RingCat)).presheaf
      (homOfLE (show U ⊓ V ≤ V from inf_le_right)) x hxUV b, smul_eq_mul]
  exact key (U ⊓ V) hxUV _ _


/-! ### Hartogs extension for the structure sheaf -/

/-- **The comparison map of an open immersion is an isomorphism in depth at least two.** On a
locally Noetherian scheme, if the structure sheaf has depth at least two at every point outside
an open `U`, then `𝒪_X ⟶ (U.ι)_* 𝒪_U` is an isomorphism: sections of the structure sheaf over
any open extend uniquely across the complement of `U`. -/
public theorem isIso_c_ι_of_depth_ge_two
    (X : Scheme.{u}) [IsLocallyNoetherian X] (U : X.Opens)
    (hdepth : ∀ x : X, x ∉ (U : Set X) →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) :
    IsIso U.ι.c := by
  let F : X.Modules := SheafOfModules.unit X.ringCatSheaf
  have hF : F.IsCoherent := Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit
  have hη := AlgebraicGeometry.isIso_unit_restrict_pushforward_of_depth_ge_two X F U
    (fun x hx => (hdepth x hx).trans_eq
      (Module.depth_eq_depth_of_linearEquiv _ (unitStalkLinearEquiv X.presheaf x)).symm)
  have _ : (Opens.map U.ι.base).Final :=
    Functor.final_of_adjunction U.ι.isOpenEmbedding.isOpenMap.adjunction
  have _ : (SheafOfModules.pushforward U.ι.toRingCatSheafHom).IsRightAdjoint := by
    change (Scheme.Modules.pushforward U.ι).IsRightAdjoint
    infer_instance
  have hleft : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app F) := hη
  have hright : IsIso (SheafOfModules.pullbackObjUnitToUnit.{u} U.ι.toRingCatSheafHom) :=
    SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal _
  have hunit : IsIso (SheafOfModules.unitToPushforwardObjUnit.{u} U.ι.toRingCatSheafHom) := by
    rw [← SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
      (φ := U.ι.toRingCatSheafHom), Adjunction.homEquiv_unit]
    change IsIso ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app F ≫
      (Scheme.Modules.pushforward U.ι).map
        (SheafOfModules.pullbackObjUnitToUnit U.ι.toRingCatSheafHom))
    have h2 : IsIso ((Scheme.Modules.pushforward U.ι).map
        (SheafOfModules.pullbackObjUnitToUnit U.ι.toRingCatSheafHom)) :=
      (Functor.mapIso (Scheme.Modules.pushforward U.ι)
        (@asIso _ _ _ _
          (SheafOfModules.pullbackObjUnitToUnit U.ι.toRingCatSheafHom) hright)).isIso_hom
    exact IsIso.comp_isIso' hleft h2
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ ?_
  intro V
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact ConcreteCategory.bijective_of_isIso
    ((SheafOfModules.evaluation X.ringCatSheaf V).map
      (SheafOfModules.unitToPushforwardObjUnit.{u} U.ι.toRingCatSheafHom))

/-! ### A contraction is proper and an isomorphism off its centre -/

/-- A contraction is proper: it is the blowup of a Noetherian scheme in a closed point, up to an
isomorphism of the source. -/
public theorem IsContractionOfExceptionalCurve.isProper {X X' : Scheme.{u}}
    {D : X.IdealSheafData} {b : X ⟶ X'} (hb : IsContractionOfExceptionalCurve D b) :
    IsProper b := by
  obtain ⟨x, hx, hreg, hdim, hD, e, he⟩ := hb.exists_blowUp_iso
  have _ : IsNoetherian X' := hb.isNoetherian
  rw [← he]
  infer_instance

/-- A morphism exhibited as the blowup of an ideal sheaf supported at a single closed point is
an isomorphism over the complement of that point. -/
public theorem isIso_morphismRestrict_compl_of_blowUp_iso
    {X X' : Scheme.{u}} {b : X ⟶ X'} (I : X'.IdealSheafData) (x : X')
    (hx : IsClosed ({x} : Set X')) (hI : (I.support : Set X') = {x})
    (e : X ≅ blowUp I) (he : e.hom ≫ blowUpToBase I = b) :
    IsIso (b ∣_ (⟨({x} : Set X')ᶜ, hx.isOpen_compl⟩ : X'.Opens)) := by
  have hsupp : (⟨(I.support : Set X')ᶜ, I.support.isClosed.isOpen_compl⟩ : X'.Opens) =
      (⟨({x} : Set X')ᶜ, hx.isOpen_compl⟩ : X'.Opens) :=
    Opens.ext (congrArg (fun s : Set X' => sᶜ) hI)
  have hBiso : IsIso (blowUpToBase I ∣_ (⟨({x} : Set X')ᶜ, hx.isOpen_compl⟩ : X'.Opens)) := by
    rw [← hsupp]
    exact isIso_blowUp_restrict_compl_support I
  subst he
  have key : IsIso (e.hom ∣_
      (blowUpToBase I ⁻¹ᵁ (⟨({x} : Set X')ᶜ, hx.isOpen_compl⟩ : X'.Opens))) := inferInstance
  have hcomp := IsIso.comp_isIso' key hBiso
  rw [← morphismRestrict_comp] at hcomp
  exact hcomp

/-! ### The structure-sheaf comparison of a contraction -/

/-- **The blowup of a point of depth at least two does not change the structure sheaf.** For an
ideal sheaf on a Noetherian scheme whose support is a single closed point at which the structure
sheaf has depth at least two, the comparison map of the blowup morphism is an isomorphism: away
from the point the blowup is an isomorphism, sections extend across the point by Hartogs, and
the complement of the exceptional divisor is scheme-theoretically dense, which makes the
comparison map of its inclusion a monomorphism. -/
private theorem isIso_c_blowUpToBase_of_support_singleton
    {X' : Scheme.{u}} [IsNoetherian X'] (I : X'.IdealSheafData) (x : X')
    (hx : IsClosed ({x} : Set X')) (hI : (I.support : Set X') = {x})
    (hdepth : (2 : ℕ∞) ≤ Module.depth (X'.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X'.presheaf.stalk x)) (X'.presheaf.stalk x)) :
    IsIso (blowUpToBase I).c := by
  let U : X'.Opens := ⟨({x} : Set X')ᶜ, hx.isOpen_compl⟩
  have hBiso : IsIso (blowUpToBase I ∣_ U) :=
    isIso_morphismRestrict_compl_of_blowUp_iso I x hx hI (Iso.refl _) (Category.id_comp _)
  have hOU : IsIso U.ι.c := by
    refine isIso_c_ι_of_depth_ge_two X' U fun z hz => ?_
    have hzx : z = x := by
      simpa [U] using hz
    rw [hzx]
    exact hdepth
  have hdense : Scheme.Opens.IsSchemeTheoreticallyDense (blowUpToBase I ⁻¹ᵁ U) := by
    have h := Stacks.Divisors.isSchemeTheoreticallyDense_compl_of_isEffectiveCartierDivisor
      (exceptionalIdeal I) inferInstance
    have hopen : (exceptionalIdeal I).support.compl = blowUpToBase I ⁻¹ᵁ U := by
      refine Opens.ext ?_
      ext z
      change z ∉ (((I.comap (blowUpToBase I)).support) : Set (blowUp I)) ↔ _
      rw [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage, hI]
      change blowUpToBase I z ∉ ({x} : Set X') ↔ blowUpToBase I z ∈ (U : Set X')
      simp [U]
    rwa [hopen] at h
  have hmono : Mono (blowUpToBase I ⁻¹ᵁ U).ι.c := by
    refine (isSchemeTheoreticallyDense_opensRange_iff_mono _).mp ?_
    rwa [Scheme.Opens.opensRange_ι]
  exact isIso_c_of_isIso_morphismRestrict (blowUpToBase I) U

/-- **The structure-sheaf comparison of a contraction is an isomorphism.** The centre of the
contraction is a regular local point of dimension two, hence of depth two, so sections of the
structure sheaf extend across it. -/
public theorem IsContractionOfExceptionalCurve.isIso_c {X X' : Scheme.{u}}
    {D : X.IdealSheafData} {b : X ⟶ X'} (hb : IsContractionOfExceptionalCurve D b) :
    IsIso b.c := by
  have _ : IsNoetherian X' := hb.isNoetherian
  obtain ⟨x, hx, hreg, hdim, hD, e, he⟩ := hb.exists_blowUp_iso
  have _ : IsRegularLocalRing (X'.presheaf.stalk x) := hreg
  have hdepth : (2 : ℕ∞) ≤ Module.depth (X'.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X'.presheaf.stalk x)) (X'.presheaf.stalk x) := by
    have hCM :=
      (IsRegularLocalRing.isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay
        (X'.presheaf.stalk x)).2
    change ((Module.depth (X'.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X'.presheaf.stalk x))
      (X'.presheaf.stalk x) : ℕ∞) : WithBot ℕ∞) =
        ringKrullDim (X'.presheaf.stalk x) at hCM
    refine WithBot.coe_le_coe.mp ?_
    rw [hCM, hdim]
    norm_num
  have hB : IsIso (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal
      (⟨{x}, hx⟩ : Closeds X'))).c :=
    isIso_c_blowUpToBase_of_support_singleton _ x hx
      (Scheme.IdealSheafData.coe_support_vanishingIdeal _) hdepth
  have hec : IsIso e.hom.c := inferInstance
  have h2 : IsIso ((TopCat.Presheaf.pushforward CommRingCat
      (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal
        (⟨{x}, hx⟩ : Closeds X'))).base).map e.hom.c) := inferInstance
  subst he
  change IsIso ((blowUpToBase (Scheme.IdealSheafData.vanishingIdeal
    (⟨{x}, hx⟩ : Closeds X'))).c ≫
      (TopCat.Presheaf.pushforward CommRingCat
        (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal
          (⟨{x}, hx⟩ : Closeds X'))).base).map e.hom.c)
  exact IsIso.comp_isIso' hB h2

/-! ### The universal property -/

/-- **The universal property of a contraction, granted the structure-sheaf comparison.** A
morphism out of `X` which is constant on the exceptional curve factors uniquely through a
contraction of that curve whose comparison map of structure sheaves is an isomorphism. -/
public theorem existsUnique_comp_eq_of_isContractionOfExceptionalCurve_of_isIso_c
    {X X' Y : Scheme.{u}} (D : X.IdealSheafData) (b : X ⟶ X')
    (hb : IsContractionOfExceptionalCurve D b) (hO : IsIso b.c) (φ : X ⟶ Y)
    (hφ : ∃ y : Y, ∀ z : D.subscheme, φ (D.subschemeι z) = y) :
    ∃! ψ : X' ⟶ Y, b ≫ ψ = φ := by
  obtain ⟨x, hx, hreg, hdim, hD, e, he⟩ := hb.exists_blowUp_iso
  have _ : IsNoetherian X' := hb.isNoetherian
  have hclosed : IsClosedMap b.base := by
    have := hb.isProper
    exact b.isClosedMap
  have hdim0 : ringKrullDim (X'.presheaf.stalk x) ≠ 0 := by
    rw [hdim]; decide
  have hoff : IsIso (b ∣_ (⟨({x} : Set X')ᶜ, hx.isOpen_compl⟩ : X'.Opens)) :=
    isIso_morphismRestrict_compl_of_blowUp_iso _ x hx
      (Scheme.IdealSheafData.coe_support_vanishingIdeal _) e he
  exact existsUnique_comp_eq_of_isIso_morphismRestrict_compl b φ hclosed x hx hdim0 hoff hO
    (exists_const_on_fibre_of_const_on_subscheme D b φ x hx hD hφ)

/-- **Stacks Project, Tag 0C5J.** Let `E ⊆ X` be an exceptional curve of the first kind on a
Noetherian scheme, given by its ideal sheaf `D`, and let `b : X ⟶ X'` be a contraction of `E`.
Then every morphism `φ : X ⟶ Y` carrying `E` to a single point factors as `φ = b ≫ ψ` for a
unique `ψ : X' ⟶ Y`. -/
@[stacks 0C5J "unique factorization through the contraction"]
public theorem existsUnique_comp_eq_of_isContractionOfExceptionalCurve
    {X X' Y : Scheme.{u}} (D : X.IdealSheafData) (b : X ⟶ X')
    (hb : IsContractionOfExceptionalCurve D b) (φ : X ⟶ Y)
    (hφ : ∃ y : Y, ∀ z : D.subscheme, φ (D.subschemeι z) = y) :
    ∃! ψ : X' ⟶ Y, b ≫ ψ = φ :=
  existsUnique_comp_eq_of_isContractionOfExceptionalCurve_of_isIso_c D b hb hb.isIso_c φ hφ

/-! ### Uniqueness of the contraction -/

/-- Every point of the support of the contracted ideal sheaf is sent to the centre. -/
public theorem IsContractionOfExceptionalCurve.eq_centre_of_mem_support {X X' : Scheme.{u}}
    {D : X.IdealSheafData} {b : X ⟶ X'} {x : X'} {hx : IsClosed ({x} : Set X')}
    (hD : D = (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X')).comap b)
    {p : X} (hp : p ∈ (D.support : Set X)) : b p = x := by
  rw [hD] at hp
  simpa only [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage,
    Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_mk, Set.mem_preimage,
    Set.mem_singleton_iff] using hp

/-- A contraction carries the curve it contracts to a single point, namely to its centre. This is
the hypothesis under which another morphism factors through it. -/
public theorem IsContractionOfExceptionalCurve.exists_const_on_subscheme {X X' : Scheme.{u}}
    {D : X.IdealSheafData} {b : X ⟶ X'} (hb : IsContractionOfExceptionalCurve D b) :
    ∃ y : X', ∀ z : D.subscheme, b (D.subschemeι z) = y := by
  obtain ⟨x, hx, -, -, hD, -, -⟩ := hb.exists_blowUp_iso
  refine ⟨x, fun z => IsContractionOfExceptionalCurve.eq_centre_of_mem_support hD ?_⟩
  rw [← D.range_subschemeι]
  exact ⟨z, rfl⟩

/-- **Stacks Project, Tag 0C5K.** A contraction of an exceptional curve of the first kind is
unique up to unique isomorphism: if `b₁ : X ⟶ X₁` and `b₂ : X ⟶ X₂` both contract the ideal
sheaf `D`, there is exactly one isomorphism `X₁ ≅ X₂` compatible with them. -/
@[stacks 0C5K "a contraction is unique up to unique isomorphism"]
public theorem existsUnique_iso_of_isContractionOfExceptionalCurve {X X₁ X₂ : Scheme.{u}}
    {D : X.IdealSheafData} {b₁ : X ⟶ X₁} {b₂ : X ⟶ X₂}
    (h₁ : IsContractionOfExceptionalCurve D b₁) (h₂ : IsContractionOfExceptionalCurve D b₂) :
    ∃! e : X₁ ≅ X₂, b₁ ≫ e.hom = b₂ := by
  obtain ⟨ψ, hψ, hψu⟩ := existsUnique_comp_eq_of_isContractionOfExceptionalCurve D b₁ h₁ b₂
    h₂.exists_const_on_subscheme
  obtain ⟨χ, hχ, -⟩ := existsUnique_comp_eq_of_isContractionOfExceptionalCurve D b₂ h₂ b₁
    h₁.exists_const_on_subscheme
  obtain ⟨w₁, -, hu₁⟩ := existsUnique_comp_eq_of_isContractionOfExceptionalCurve D b₁ h₁ b₁
    h₁.exists_const_on_subscheme
  obtain ⟨w₂, -, hu₂⟩ := existsUnique_comp_eq_of_isContractionOfExceptionalCurve D b₂ h₂ b₂
    h₂.exists_const_on_subscheme
  have hid₁ : ψ ≫ χ = 𝟙 X₁ :=
    (hu₁ _ (show b₁ ≫ ψ ≫ χ = b₁ by rw [← Category.assoc, hψ, hχ])).trans
      (hu₁ _ (Category.comp_id b₁)).symm
  have hid₂ : χ ≫ ψ = 𝟙 X₂ :=
    (hu₂ _ (show b₂ ≫ χ ≫ ψ = b₂ by rw [← Category.assoc, hχ, hψ])).trans
      (hu₂ _ (Category.comp_id b₂)).symm
  exact ⟨⟨ψ, χ, hid₁, hid₂⟩, hψ, fun e' he' => Iso.ext (hψu e'.hom he')⟩

/-- The isomorphism identifying the targets of two contractions of the same ideal sheaf. -/
public noncomputable def contractionIso {X X₁ X₂ : Scheme.{u}} {D : X.IdealSheafData}
    {b₁ : X ⟶ X₁} {b₂ : X ⟶ X₂} (h₁ : IsContractionOfExceptionalCurve D b₁)
    (h₂ : IsContractionOfExceptionalCurve D b₂) : X₁ ≅ X₂ :=
  (existsUnique_iso_of_isContractionOfExceptionalCurve h₁ h₂).choose

/-- `AlgebraicGeometry.contractionIso` is compatible with the two contractions. -/
@[simp]
public theorem contractionIso_hom_comp {X X₁ X₂ : Scheme.{u}} {D : X.IdealSheafData}
    {b₁ : X ⟶ X₁} {b₂ : X ⟶ X₂} (h₁ : IsContractionOfExceptionalCurve D b₁)
    (h₂ : IsContractionOfExceptionalCurve D b₂) :
    b₁ ≫ (contractionIso h₁ h₂).hom = b₂ :=
  (existsUnique_iso_of_isContractionOfExceptionalCurve h₁ h₂).choose_spec.1

/-- `AlgebraicGeometry.contractionIso` is the only isomorphism compatible with the two
contractions. -/
public theorem eq_contractionIso {X X₁ X₂ : Scheme.{u}} {D : X.IdealSheafData}
    {b₁ : X ⟶ X₁} {b₂ : X ⟶ X₂} (h₁ : IsContractionOfExceptionalCurve D b₁)
    (h₂ : IsContractionOfExceptionalCurve D b₂) (e : X₁ ≅ X₂) (he : b₁ ≫ e.hom = b₂) :
    e = contractionIso h₁ h₂ :=
  (existsUnique_iso_of_isContractionOfExceptionalCurve h₁ h₂).choose_spec.2 e he

/-- The inverse of `AlgebraicGeometry.contractionIso` carries the second contraction to the
first. -/
@[simp]
public theorem contractionIso_inv_comp {X X₁ X₂ : Scheme.{u}} {D : X.IdealSheafData}
    {b₁ : X ⟶ X₁} {b₂ : X ⟶ X₂} (h₁ : IsContractionOfExceptionalCurve D b₁)
    (h₂ : IsContractionOfExceptionalCurve D b₂) :
    b₂ ≫ (contractionIso h₁ h₂).inv = b₁ :=
  calc b₂ ≫ (contractionIso h₁ h₂).inv
      = (b₁ ≫ (contractionIso h₁ h₂).hom) ≫ (contractionIso h₁ h₂).inv := by
        rw [contractionIso_hom_comp]
    _ = b₁ := by rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end AlgebraicGeometry

end
