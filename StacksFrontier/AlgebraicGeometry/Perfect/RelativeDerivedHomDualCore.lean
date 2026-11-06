module

public import StacksFrontier.CategoryTheory.Triangulated.DerivedLimitOfAHomotopyColimit
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedHomOfAHomotopyColimit
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectBidual
public import
  StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackDevissage
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackPerfectAndPseudoCoherent
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangeMap
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Triangulated
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedApplicationUnitLaw
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.UnitComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.RingedSiteComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDual
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDualTensorHom
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDualLeftDual
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectObjectCanonical
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Derived internal Homs out of a homotopy colimit, pushed forward

Let `f : X ⟶ S` be a morphism of schemes, `(Kₙ)` a system of objects of `D(𝒪_X)` with
`K = hocolim Kₙ` and `E ∈ D(𝒪_X)`. With `Mₙ = Rf_* R𝓗om(Kₙ, E)` perfect and
`L = hocolim Mₙ^∨`,

`Rf_* R𝓗om(K, E) = R lim Mₙ = R lim R𝓗om(Mₙ^∨, 𝒪_S) = R𝓗om(L, 𝒪_S)`,

and the same holds after base change along `g : S' ⟶ S` when the `Kₙ` are perfect and the base
change map is invertible on the terms of the system.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeDerivedHomDual.pushforwardSheafHomSystem`: the inverse system
  `n ↦ Rf_* R𝓗om(Kₙ, E)`.
* `Stacks.AlgebraicGeometry.RelativeDerivedHomDual.dualSystem`: the system `n ↦ Mₙ^∨` of duals.
* `Stacks.AlgebraicGeometry.RelativeDerivedHomDual.bidualSystemIso`: biduality `Mₙ ≅ (Mₙ^∨)^∨`
  as an isomorphism of inverse systems.

## Main results

* `CategoryTheory.Pretriangulated.IsDerivedLimit.nonempty_iso`: two derived limits of one
  inverse system are isomorphic.
* `CategoryTheory.Pretriangulated.IsDerivedLimit.map`: a triangulated functor preserving the
  product carries a derived limit to a derived limit.
* `Stacks.AlgebraicGeometry.RelativeDerivedHomDual.nonempty_iso_pushforward_sheafHom`:
  `Rf_* R𝓗om(K, E) ≅ R𝓗om(L, 𝒪_S)`.
* `Stacks.AlgebraicGeometry.RelativeDerivedHomDual.nonempty_iso_pushforward_sheafHom_pullback`:
  `Rf'_* R𝓗om(L(g')^*K, L(g')^*E) ≅ R𝓗om(Lg^*L, 𝒪_{S'})`.

## References

* [Stacks Project, Tag 0DJU](https://stacks.math.columbia.edu/tag/0DJU)
* [Stacks Project, Tag 0DJI](https://stacks.math.columbia.edu/tag/0DJI)
* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 08I3](https://stacks.math.columbia.edu/tag/08I3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry

universe u

namespace CategoryTheory.Pretriangulated

variable {D : Type*} [Category D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- Two derived limits of one inverse system are isomorphic. -/
theorem IsDerivedLimit.nonempty_iso {F : ℕᵒᵖ ⥤ D} [HasProduct fun n : ℕ => F.obj ⟨n⟩]
    {K K' : D} (h : IsDerivedLimit F K) (h' : IsDerivedLimit F K') : Nonempty (K ≅ K') := by
  obtain ⟨p, δ, hT⟩ := h
  obtain ⟨p', δ', hT'⟩ := h'
  obtain ⟨e, -⟩ := exists_iso_of_arrow_iso _ _ (rot_of_distTriang _ hT)
    (rot_of_distTriang _ hT') (Iso.refl _)
  exact ⟨(shiftFunctor D (1 : ℤ)).preimageIso (Triangle.π₃.mapIso e)⟩

variable {D' : Type*} [Category D'] [Preadditive D'] [HasZeroObject D'] [HasShift D' ℤ]
  [∀ n : ℤ, (shiftFunctor D' n).Additive] [Pretriangulated D']

/-- A triangulated functor preserving the product carries a derived limit to a derived limit. -/
theorem IsDerivedLimit.map {F : ℕᵒᵖ ⥤ D} [HasProduct fun n : ℕ => F.obj ⟨n⟩] {K : D}
    (h : IsDerivedLimit F K) (G : D ⥤ D') [G.CommShift ℤ] [G.IsTriangulated]
    [HasProduct fun n : ℕ => (F ⋙ G).obj ⟨n⟩]
    [PreservesLimit (Discrete.functor fun n : ℕ => F.obj ⟨n⟩) G] :
    IsDerivedLimit (F ⋙ G) (G.obj K) := by
  have : HasProduct fun n : ℕ => G.obj (F.obj ⟨n⟩) := ‹HasProduct fun n : ℕ => (F ⋙ G).obj ⟨n⟩›
  obtain ⟨p, δ, hT⟩ := h
  let e := PreservesProduct.iso G fun n : ℕ => F.obj ⟨n⟩
  let b := Pi.lift fun n : ℕ => Pi.π (fun n : ℕ => F.obj ⟨n⟩) n -
    Pi.π (fun n : ℕ => F.obj ⟨n⟩) (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op
  let b' := Pi.lift fun n : ℕ => Pi.π (fun n : ℕ => G.obj (F.obj ⟨n⟩)) n -
    Pi.π (fun n : ℕ => G.obj (F.obj ⟨n⟩)) (n + 1) ≫ G.map (F.map (homOfLE (Nat.le_succ n)).op)
  have he (n : ℕ) : e.hom ≫ Pi.π (fun n : ℕ => G.obj (F.obj ⟨n⟩)) n =
      G.map (Pi.π (fun n : ℕ => F.obj ⟨n⟩) n) := by
    simp [e, PreservesProduct.iso_hom]
  have hb : G.map b ≫ e.hom = e.hom ≫ b' := by
    refine Pi.hom_ext _ _ fun n => ?_
    have he' := fun m => reassoc_of% (he m)
    simp only [Category.assoc, b', Pi.lift_comp_π, Preadditive.comp_sub, he, he', ← G.map_comp, b,
      G.map_sub]
  have hb' : b' ≫ e.inv = e.inv ≫ G.map b := by
    rw [Iso.comp_inv_eq, Category.assoc, hb, Iso.inv_hom_id_assoc]
  have hfin : Triangle.mk (G.map p ≫ e.hom) b'
      (e.inv ≫ G.map δ ≫ (G.commShiftIso (1 : ℤ)).hom.app K) ∈ distTriang D' := by
    refine isomorphic_distinguished _ (G.map_distinguished _ hT) _
      (Triangle.isoMk _ _ (Iso.refl _) e.symm e.symm ?_ ?_ ?_)
    · exact (by simp : (G.map p ≫ e.hom) ≫ e.inv = 𝟙 _ ≫ G.map p)
    · exact hb'
    · exact (by simp : (e.inv ≫ G.map δ ≫ (G.commShiftIso (1 : ℤ)).hom.app K) ≫
        (shiftFunctor D' (1 : ℤ)).map (𝟙 _) = e.inv ≫ G.map δ ≫ (G.commShiftIso (1 : ℤ)).hom.app K)
  exact ⟨_, _, hfin⟩

end CategoryTheory.Pretriangulated

namespace DerivedCategory

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

/-- The first map of a distinguished triangle is an isomorphism on cohomology in the degrees
`≥ t + 2` when its third vertex lies in `D^{≤ t}`. -/
theorem isIso_homologyMap_mor₁_of_isLE (T : Pretriangulated.Triangle (DerivedCategory C))
    (hT : T ∈ distTriang _) (t : ℤ) (h : T.obj₃.IsLE t) (i : ℤ) (hi : t + 2 ≤ i) :
    IsIso ((homologyFunctor C i).map T.mor₁) := by
  have hepi : Epi ((homologyFunctor C i).map T.mor₁) :=
    (HomologySequence.epi_homologyMap_mor₁_iff T hT i).2
      ((isZero_of_isLE T.obj₃ t i (by omega)).eq_of_tgt _ _)
  have hmono : Mono ((homologyFunctor C i).map T.mor₁) :=
    (HomologySequence.mono_homologyMap_mor₁_iff T hT (i - 1) i (by omega)).2
      ((isZero_of_isLE T.obj₃ t (i - 1) (by omega)).eq_of_src _ _)
  exact isIso_of_mono_of_epi _

/-- The truncation map `K ⟶ τ_{≥ a} K` is an isomorphism on cohomology in the degree `a`. -/
theorem isIso_homologyFunctor_map_truncGEπ_app_self (K : DerivedCategory C) (a : ℤ) :
    IsIso ((homologyFunctor C a).map ((TStructure.t.truncGEπ a).app K)) := by
  let T := (TStructure.t.triangleLEGE (a - 1) a (by omega)).obj K
  have hT := TStructure.t.triangleLEGE_distinguished (a - 1) a (by omega) K
  have hEpi : Epi ((homologyFunctor C a).map T.mor₂) :=
    (HomologySequence.epi_homologyMap_mor₂_iff T hT a (a + 1) (by omega)).2
      ((isZero_of_isLE ((TStructure.t.truncLE (a - 1)).obj K) (a - 1) (a + 1)
        (by omega)).eq_of_tgt _ _)
  have hMono : Mono ((homologyFunctor C a).map T.mor₂) :=
    (HomologySequence.mono_homologyMap_mor₂_iff T hT a).2
      ((isZero_of_isLE ((TStructure.t.truncLE (a - 1)).obj K) (a - 1) a (by omega)).eq_of_src _ _)
  exact isIso_of_mono_of_epi ((homologyFunctor C a).map T.mor₂)

/-- If `D ∈ D^{≤ m}`, the `m`-th cohomology of `D` satisfies a property `P` closed under
isomorphism, and every morphism from `D` to `Y[-m]` with `P Y` is zero, then `D ∈ D^{≤ m - 1}`. -/
theorem isLE_pred_of_subsingleton_hom_single (P : C → Prop)
    (hP : ∀ {Y Y' : C}, (Y ≅ Y') → P Y → P Y') (D : DerivedCategory C) (m : ℤ) (hm : D.IsLE m)
    (hD : P ((homologyFunctor C m).obj D))
    (hvan : ∀ Y : C, P Y → Subsingleton (D ⟶ (singleFunctor C m).obj Y)) : D.IsLE (m - 1) := by
  rw [isLE_iff]
  intro i hi
  rcases lt_or_eq_of_le (show m ≤ i by omega) with h | rfl
  · exact isZero_of_isLE D m i h
  · let π := (TStructure.t.truncGEπ m).app D
    obtain ⟨Y, ⟨e⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE
      ((TStructure.t.truncGE m).obj D) m
    have := isIso_homologyFunctor_map_truncGEπ_app_self D m
    have hY : P Y := hP ((asIso ((homologyFunctor C m).map π)) ≪≫
      (homologyFunctor C m).mapIso e ≪≫ (singleFunctorCompHomologyFunctorIso C m).app Y) hD
    have h0 : π ≫ e.hom = 0 := (hvan Y hY).elim _ _
    have h2 : (homologyFunctor C m).map π = 0 := by
      rw [← cancel_mono ((homologyFunctor C m).map e.hom), ← CategoryTheory.Functor.map_comp, h0,
        CategoryTheory.Functor.map_zero, zero_comp]
    have h3 : IsIso (0 : (homologyFunctor C m).obj ((𝟭 (DerivedCategory C)).obj D) ⟶ _) :=
      h2 ▸ (inferInstance : IsIso ((homologyFunctor C m).map π))
    exact ((isIsoZero_iff_source_target_isZero _ _).1 h3).1

/-- A bounded above object of `D(𝒜)` whose cohomology objects satisfy a property `P` closed under
isomorphism, with no nonzero map to any `Y[-j]` with `j > t` and `P Y`, lies in `D^{≤ t}`. -/
theorem isLE_of_subsingleton_hom_single (P : C → Prop)
    (hP : ∀ {Y Y' : C}, (Y ≅ Y') → P Y → P Y') (D : DerivedCategory C) (b t : ℤ) (hb : D.IsLE b)
    (hD : ∀ j, P ((homologyFunctor C j).obj D))
    (hvan : ∀ j, t < j → ∀ Y : C, P Y → Subsingleton (D ⟶ (singleFunctor C j).obj Y)) :
    D.IsLE t := by
  have key : ∀ k : ℕ, D.IsLE (max t (b - k)) := by
    intro k
    induction k with
    | zero =>
      rcases le_total t b with h | h
      · simpa [max_eq_right h] using hb
      · rw [max_eq_left (by omega)]
        exact TStructure.t.isLE_of_le D b t h
    | succ k ih =>
      rcases le_or_gt (b - k) t with h | h
      · rw [max_eq_left (by omega : b - ((k + 1 : ℕ) : ℤ) ≤ t)]
        rwa [max_eq_left h] at ih
      · rw [max_eq_right (by omega : t ≤ b - ((k + 1 : ℕ) : ℤ))]
        rw [max_eq_right h.le] at ih
        have := isLE_pred_of_subsingleton_hom_single P hP D (b - k) ih (hD _)
          (hvan (b - k) h)
        rwa [show b - (k : ℤ) - 1 = b - ((k + 1 : ℕ) : ℤ) by push_cast; ring] at this
  have := key (b - t).toNat
  rwa [max_eq_left (by omega)] at this

end DerivedCategory

namespace Stacks.AlgebraicGeometry.RelativeDerivedHomDual

open Stacks.SheafOfModules

attribute [local implicit_reducible] TopCat.Sheaf structureSheafRing CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

/-! ### The standard model -/

section StandardModel

attribute [local instance] HasDerivedCategory.standard

/-- `D(𝒪_X)` at the standard model. -/
abbrev DStd (X : Scheme.{u}) : Type (u + 1) :=
  DerivedCategory (StructureSheafModules X.sheaf)

/-- The shift functors of `D(𝒪_X)` are additive, at the standard model. -/
instance instAdditiveShiftFunctorDStd (X : Scheme.{u}) :
    ∀ n : ℤ, (shiftFunctor (DStd X) n).Additive :=
  fun _ => inferInstance

/-- `D(𝒪_X)` has direct sums at the standard model ([Stacks, Tag 07D9]). -/
instance instHasCoproductsDStd (X : Scheme.{u}) : HasCoproducts.{u} (DStd X) := inferInstance

/-- `D(𝒪_X)` has products at the standard model ([Stacks, Tag 07D9]). -/
instance instHasProductsDStd (X : Scheme.{u}) : HasProducts.{u} (DStd X) := inferInstance

/-- The derived direct image `Rf_* : D(𝒪_X) ⥤ D(𝒪_S)` at the standard model. -/
abbrev pushStd {X S : Scheme.{u}} (f : X ⟶ S) : DStd X ⥤ DStd S :=
  Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f.toLRSHom.toShHom

/-- `Rf_*` commutes with the shift: it is the right adjoint of `Lf^*`. -/
instance instCommShiftPushStd {X S : Scheme.{u}} (f : X ⟶ S) : (pushStd f).CommShift ℤ :=
  Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCommShift f.toLRSHom.toShHom

/-- `Rf_*` is a triangulated functor. -/
instance instIsTriangulatedPushStd {X S : Scheme.{u}} (f : X ⟶ S) : (pushStd f).IsTriangulated :=
  Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward_isTriangulated
    f.toLRSHom.toShHom

/-- The derived pullback `Lg^* : D(𝒪_S) ⥤ D(𝒪_X)` at the standard model. -/
abbrev pullStd {X S : Scheme.{u}} (g : X ⟶ S) : DStd S ⥤ DStd X :=
  Stacks.Cohomology.DerivedInternalHomPullback.derivedPullbackFunctor g.toLRSHom.toShHom

/-- The derived adjunction `Lf^* ⊣ Rf_*` of [Stacks, Tag 079W] at the standard model. -/
abbrev adjStd {X S : Scheme.{u}} (f : X ⟶ S) : pullStd f ⊣ pushStd f :=
  Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction f.toLRSHom.toShHom

/-- `Rf_*` preserves limits, being a right adjoint. -/
instance instPreservesLimitsPushStd {X S : Scheme.{u}} (f : X ⟶ S) :
    PreservesLimitsOfSize.{0, 0} (pushStd f) :=
  (adjStd f).rightAdjoint_preservesLimits

/-- `Lf^*` preserves colimits, being a left adjoint. -/
instance instPreservesColimitsPullStd {X S : Scheme.{u}} (f : X ⟶ S) :
    PreservesColimitsOfSize.{0, 0} (pullStd f) :=
  (adjStd f).leftAdjoint_preservesColimits

/-- The cohomology sheaves `Hⁱ : D(𝒪_X) ⥤ Mod(𝒪_X)` at the standard model. -/
abbrev HStd (X : Scheme.{u}) (i : ℤ) : DStd X ⥤ StructureSheafModules X.sheaf :=
  DerivedCategory.homologyFunctor _ i

/-- A module placed in degree `j`, at the standard model. -/
abbrev singleStd (X : Scheme.{u}) (j : ℤ) : StructureSheafModules X.sheaf ⥤ DStd X :=
  DerivedCategory.singleFunctor _ j

/-- The standard model of `D(𝒪_X)` at the spelling `OXMod` of the category of modules. -/
abbrev stdOXMod (X : RingedSpace.{u, u}) : HasDerivedCategory (StrictlyPerfect.OXMod.{u, u} X) :=
  HasDerivedCategory.standard _

/-- The structure sheaf `𝒪_X` placed in degree zero, as an object of `D(𝒪_X)`. -/
abbrev unitObj (X : Scheme.{u}) : DStd X :=
  RingedSite.derivedStructureSheaf (ringedSite X.sheaf)

/-- The inverse system `n ↦ R𝓗om(Kₙ, E)` attached to a system `(Kₙ)` of objects of `D(𝒪_X)`
and an object `E`. -/
def homSystem {X : Scheme.{u}} (F : ℕ ⥤ DStd X) (E : DStd X) : ℕᵒᵖ ⥤ DStd X :=
  derivedSheafHomSystem X.sheaf F E

/-- Perfectness at the standard model, in the ringed-site reading of [Stacks, Tag 08G5]. -/
abbrev IsPerfectSite {X : Scheme.{u}} (K : DStd X) : Prop :=
  (ringedSite X.sheaf).IsPerfect K

section Biduality

variable {S : Scheme.{u}}

/-- The left unitor `𝒪_S ⊗^L K ⟶ K` of the derived tensor product is an isomorphism. -/
theorem isIso_derivedLeftUnitorHom (K : DStd S) : IsIso (derivedLeftUnitorHom S.sheaf K) := by
  rw [derivedLeftUnitorHom_eq]
  exact Iso.isIso_hom _

/-- The left unitor `𝒪_S ⊗^L - ≅ 𝟭` of the derived tensor product, as an isomorphism of
functors. -/
def leftUnitNatIso (S : Scheme.{u}) : (derivedTensor S.sheaf).obj (unitObj S) ≅ 𝟭 (DStd S) :=
  NatIso.ofComponents (fun K => @asIso _ _ _ _ _ (isIso_derivedLeftUnitorHom K))
    (fun φ => derivedLeftUnitorHom_naturality S.sheaf φ)

/-- The trivialisation `R𝓗om(𝒪_S, 𝒪_S) ≅ 𝒪_S` in the left factor of the derived tensor
product. -/
def unitTensorTrivIso (S : Scheme.{u}) :
    (derivedTensor S.sheaf).obj (unitObj S) ≅
      (derivedTensor S.sheaf).obj
        (((derivedSheafHom S.sheaf).obj (op (unitObj S))).obj (unitObj S)) :=
  (derivedTensor S.sheaf).mapIso (derivedDualStructureSheafIso S.sheaf).symm

/-- The identity functor of `D(𝒪_S)` is isomorphic to `R𝓗om(𝒪_S, 𝒪_S) ⊗^L -`. -/
def unitHomTensorIso (S : Scheme.{u}) :
    𝟭 (DStd S) ≅ (derivedTensor S.sheaf).obj
      (((derivedSheafHom S.sheaf).obj (op (unitObj S))).obj (unitObj S)) :=
  Iso.trans (leftUnitNatIso S).symm (unitTensorTrivIso S)

/-- The system `n ↦ Mₙ^∨ = R𝓗om(Mₙ, 𝒪_S)` of duals of an inverse system `(Mₙ)` of `D(𝒪_S)`;
its transition maps are the duals of those of `(Mₙ)`. -/
abbrev dualSystem (M : ℕᵒᵖ ⥤ DStd S) : ℕ ⥤ DStd S :=
  M.rightOp ⋙ (derivedSheafHom S.sheaf).flip.obj (unitObj S)

/-- **Biduality for an inverse system of perfect objects**, as an isomorphism of inverse systems:
`Mₙ ≅ (Mₙ^∨)^∨`, naturally in `n`.  The components are the evaluation morphisms of Stacks 0A8U at
`L = M = 𝒪_S`, invertible by Stacks 0G40, after the identification `Mₙ ≅ R𝓗om(𝒪_S, 𝒪_S) ⊗^L Mₙ`;
both steps are natural, the second by the functoriality of the evaluation morphism. -/
@[sga "5 III 6.2" "special case"]
def bidualSystemIso (M : ℕᵒᵖ ⥤ DStd S) (hM : ∀ n, IsPerfectSite (M.obj n)) :
    M ≅ homSystem (dualSystem M) (unitObj S) :=
  (Functor.rightUnitor M).symm ≪≫ Functor.isoWhiskerLeft M (unitHomTensorIso S) ≪≫
    NatIso.ofComponents
      (fun n => @asIso _ _ _ _
        (derivedSheafHomEvaluation S.sheaf (M.obj n) (unitObj S) (unitObj S))
        (derivedSheafHomEvaluation_isIso_of_isPerfect S.sheaf _ _ _ (hM n)))
      (fun {n m} φ => by
        have hev := derivedSheafHomEvaluation_natural S.sheaf (M.map φ) (𝟙 (unitObj S))
          (𝟙 (unitObj S))
        have h₁ : derivedSheafHomMap S.sheaf (𝟙 (unitObj S)) (𝟙 (unitObj S)) = 𝟙 _ :=
          RingedSite.derivedSheafHomMap_id (ringedSite S.sheaf) (derivedInternalHom S.sheaf) _ _
        have h₂ : derivedTensorMap S.sheaf
            (𝟙 (((derivedSheafHom S.sheaf).obj (op (unitObj S))).obj (unitObj S))) (M.map φ) =
            ((derivedTensor S.sheaf).obj
              (((derivedSheafHom S.sheaf).obj (op (unitObj S))).obj (unitObj S))).map (M.map φ) :=
          RingedSite.derivedTensorMap_id_left (ringedSite S.sheaf)
            (canonicalDerivedTensorProduct (ringedSite S.sheaf)) _ _
        have h₃ : derivedSheafHomMap S.sheaf (M.map φ) (𝟙 (unitObj S)) =
            ((derivedSheafHom S.sheaf).map (M.map φ).op).app (unitObj S) :=
          RingedSite.derivedSheafHomMap_id_right (ringedSite S.sheaf)
            (derivedInternalHom S.sheaf) _ _
        have h₄ : derivedSheafHomMap S.sheaf
            (((derivedSheafHom S.sheaf).map (M.map φ).op).app (unitObj S)) (𝟙 (unitObj S)) =
            ((derivedSheafHom S.sheaf).map
              (((derivedSheafHom S.sheaf).map (M.map φ).op).app (unitObj S)).op).app (unitObj S) :=
          RingedSite.derivedSheafHomMap_id_right (ringedSite S.sheaf)
            (derivedInternalHom S.sheaf) _ _
        rwa [h₁, h₂, h₃, h₄] at hev)

end Biduality

section Systems

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The inverse system `n ↦ Rf_* R𝓗om(Kₙ, E)` on `S` attached to a system `(Kₙ)` of objects
of `D(𝒪_X)` and an object `E` of `D(𝒪_X)`. -/
abbrev pushforwardSheafHomSystem (F : ℕ ⥤ DStd X) (E : DStd X) : ℕᵒᵖ ⥤ DStd S :=
  homSystem F E ⋙ pushStd f

/-- `Rf_* R𝓗om(hocolim Kₙ, E)` is a derived limit of the system `n ↦ Rf_* R𝓗om(Kₙ, E)`. -/
theorem isDerivedLimit_pushforwardSheafHomSystem (F : ℕ ⥤ DStd X) (E : DStd X) {K : DStd X}
    (hK : IsHomotopyColimit F K) :
    IsDerivedLimit (pushforwardSheafHomSystem f F E)
      ((pushStd f).obj (((derivedSheafHom X.sheaf).obj (op K)).obj E)) :=
  (isDerivedLimit_derivedSheafHom_of_isHomotopyColimit X.sheaf F E hK).map (pushStd f)

/-- `R𝓗om(hocolim Mₙ^∨, 𝒪_S)` is a derived limit of `(Mₙ)` for an inverse system of perfect
objects. -/
theorem isDerivedLimit_of_isHomotopyColimit_dualSystem (M : ℕᵒᵖ ⥤ DStd S)
    (hM : ∀ n, IsPerfectSite (M.obj n)) {L : DStd S}
    (hL : IsHomotopyColimit (dualSystem M) L) :
    IsDerivedLimit M (((derivedSheafHom S.sheaf).obj (op L)).obj (unitObj S)) :=
  IsDerivedLimit.of_natIso (bidualSystemIso M hM).symm
    (isDerivedLimit_derivedSheafHom_of_isHomotopyColimit S.sheaf (dualSystem M) (unitObj S) hL)

/-- If `K = hocolim Kₙ`, the objects `Mₙ = Rf_* R𝓗om(Kₙ, E)` are perfect and `L = hocolim Mₙ^∨`,
then `Rf_* R𝓗om(K, E) ≅ R𝓗om(L, 𝒪_S)`. -/
theorem nonempty_iso_pushforward_sheafHom (F : ℕ ⥤ DStd X) (E : DStd X) {K : DStd X}
    (hK : IsHomotopyColimit F K)
    (hM : ∀ n, IsPerfectSite ((pushforwardSheafHomSystem f F E).obj n))
    {L : DStd S} (hL : IsHomotopyColimit (dualSystem (pushforwardSheafHomSystem f F E)) L) :
    Nonempty ((pushStd f).obj (((derivedSheafHom X.sheaf).obj (op K)).obj E) ≅
      ((derivedSheafHom S.sheaf).obj (op L)).obj (unitObj S)) :=
  (isDerivedLimit_pushforwardSheafHomSystem f F E hK).nonempty_iso
    (isDerivedLimit_of_isHomotopyColimit_dualSystem _ hM hL)

end Systems

section BaseChange

open Stacks.Cohomology.DerivedInternalHomPullback Stacks.Cohomology.DerivedBaseChange

/-- `Lg^*` commutes with the shift ([Stacks, Tag 06YJ]). -/
instance instCommShiftPullStd {X S : Scheme.{u}} (g : X ⟶ S) : (pullStd g).CommShift ℤ :=
  Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_commShift g.toLRSHom.toShHom

/-- `Lg^*` is a triangulated functor ([Stacks, Tag 06YJ]). -/
instance instIsTriangulatedPullStd {X S : Scheme.{u}} (g : X ⟶ S) : (pullStd g).IsTriangulated :=
  Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_isTriangulated g.toLRSHom.toShHom

/-- `Lg^*𝒪_S ≅ 𝒪_{S'}`. -/
def pullbackUnitIso {X S : Scheme.{u}} (g : X ⟶ S) : (pullStd g).obj (unitObj S) ≅ unitObj X :=
  Stacks.Cohomology.DerivedPullbackUnit.derivedPullbackUnitIso g.toLRSHom.toShHom

variable {X S X' S' : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (sq : g'.toLRSHom.toShHom ≫ f.toLRSHom.toShHom = f'.toLRSHom.toShHom ≫ g.toLRSHom.toShHom)

/-- The perfectness predicate of the ringed site, read as the one of the ringed space. -/
theorem isPerfect_ringedSpace_of_isPerfectSite {X : Scheme.{u}} {K : DStd X}
    (hK : IsPerfectSite K) : AlgebraicGeometry.RingedSpace.IsPerfect (X := X.toRingedSpace) K :=
  (Stacks.Cohomology.PerfectComplexes.isPerfect_iff_ringedSite X.toRingedSpace K).2 hK

/-- The comparison map `Lh^*R𝓗om(K, E) ⟶ R𝓗om(Lh^*K, Lh^*E)` is an isomorphism for a perfect
`K`. -/
theorem isIso_derivedPullbackSheafHomMap_of_isPerfectSite {X Y : Scheme.{u}} (h : X ⟶ Y)
    {K : DStd Y} (hK : IsPerfectSite K) (E : DStd Y) :
    IsIso (derivedPullbackSheafHomMap h.toLRSHom.toShHom K E) :=
  isIso_derivedPullbackSheafHomMap_of_isPerfect h.toLRSHom.toShHom K
    (isPerfect_ringedSpace_of_isPerfectSite hK) E

/-- The comparison map `Lh^*R𝓗om(A, M) ⟶ R𝓗om(Lh^*A, Lh^*M)` is natural in `A`:
`Lh^*R𝓗om(B, M) ⟶ Lh^*R𝓗om(A, M) ⟶ R𝓗om(Lh^*A, Lh^*M)` and
`Lh^*R𝓗om(B, M) ⟶ R𝓗om(Lh^*B, Lh^*M) ⟶ R𝓗om(Lh^*A, Lh^*M)` agree for `φ : A ⟶ B`. -/
theorem derivedPullbackSheafHomMap_naturality {X Y : Scheme.{u}} (h : X ⟶ Y) {A B : DStd Y}
    (φ : A ⟶ B) (M : DStd Y) :
    (pullStd h).map (((derivedSheafHom Y.sheaf).map φ.op).app M) ≫
        derivedPullbackSheafHomMap h.toLRSHom.toShHom A M =
      derivedPullbackSheafHomMap h.toLRSHom.toShHom B M ≫
        ((derivedSheafHom X.sheaf).map ((pullStd h).map φ).op).app ((pullStd h).obj M) :=
  Transpose.homComparison_naturality_source (derivedPullbackFunctor h.toLRSHom.toShHom)
    (derivedSheafHom Y.sheaf) (derivedSheafHom X.sheaf) (internalHomTensorUncurried Y.toRingedSpace)
    (internalHomTensorUncurried X.toRingedSpace)
    (fun A B C => (RingedSite.derivedCurryHomEquiv (ringedSite Y.sheaf) A B C).toEquiv)
    (fun A B C => (RingedSite.derivedCurryHomEquiv (ringedSite X.sheaf) A B C).toEquiv)
    (pullbackTensorIso h.toLRSHom.toShHom)
    (tensorHomEquivNaturalLeft_ringedSpace Y.toRingedSpace)
    (tensorHomEquivDinatural_ringedSpace Y.toRingedSpace)
    (tensorHomEquivNaturalLeft_ringedSpace X.toRingedSpace)
    (tensorHomEquivDinatural_ringedSpace X.toRingedSpace) φ M

/-- For a system `(Kₙ)` of perfect objects, the isomorphism of inverse systems
`Lh^* R𝓗om(Kₙ, E) ≅ R𝓗om(Lh^*Kₙ, Lh^*E)`. -/
def pullbackSheafHomSystemIso {X Y : Scheme.{u}} (h : X ⟶ Y) (F : ℕ ⥤ DStd Y)
    (hF : ∀ n, IsPerfectSite (F.obj n)) (E : DStd Y) :
    homSystem F E ⋙ pullStd h ≅
      homSystem (F ⋙ pullStd h) ((pullStd h).obj E) :=
  NatIso.ofComponents
    (fun n => @asIso _ _ _ _ (derivedPullbackSheafHomMap h.toLRSHom.toShHom (F.obj n.unop) E)
      (isIso_derivedPullbackSheafHomMap_of_isPerfectSite h (hF n.unop) E))
    (fun {_ _} φ => derivedPullbackSheafHomMap_naturality h (F.map φ.unop) E)

/-- For an inverse system `(Gₙ)` of `D(𝒪_X)` on whose terms the base change map
`Lg^*Rf_*Gₙ ⟶ Rf'_*L(g')^*Gₙ` is invertible, the isomorphism of inverse systems
`Lg^*Rf_*Gₙ ≅ Rf'_*L(g')^*Gₙ`. -/
def baseChangeSystemIso (G : ℕᵒᵖ ⥤ DStd X)
    (hG : ∀ n, IsIso ((derivedBaseChangeSquare g'.toLRSHom.toShHom f'.toLRSHom.toShHom
      f.toLRSHom.toShHom g.toLRSHom.toShHom sq).app (G.obj n))) :
    (G ⋙ pushStd f) ⋙ pullStd g ≅ (G ⋙ pullStd g') ⋙ pushStd f' :=
  NatIso.ofComponents
    (fun n => @asIso _ _ _ _ ((derivedBaseChangeSquare g'.toLRSHom.toShHom f'.toLRSHom.toShHom
      f.toLRSHom.toShHom g.toLRSHom.toShHom sq).app (G.obj n)) (hG n))
    (fun φ => (derivedBaseChangeSquare g'.toLRSHom.toShHom f'.toLRSHom.toShHom
      f.toLRSHom.toShHom g.toLRSHom.toShHom sq).naturality (G.map φ))

/-- The terms of the dual system of a system of perfect objects are perfect
([Stacks, Tag 08DQ]). -/
theorem isPerfectSite_dualSystem {S : Scheme.{u}} (M : ℕᵒᵖ ⥤ DStd S)
    (hM : ∀ n, IsPerfectSite (M.obj n)) (n : ℕ) : IsPerfectSite ((dualSystem M).obj n) :=
  isPerfect_derivedDual S.sheaf _ (hM (op n))

/-- The isomorphism of inverse systems `R𝓗om(Lg^*Lₙ, 𝒪_{S'}) ≅ R𝓗om(Lg^*Lₙ, Lg^*𝒪_S)`. -/
def bcStep₁ (L : ℕ ⥤ DStd S) :
    homSystem (L ⋙ pullStd g) (unitObj S') ≅
      homSystem (L ⋙ pullStd g) ((pullStd g).obj (unitObj S)) :=
  Functor.isoWhiskerLeft (L ⋙ pullStd g).op
    ((derivedSheafHom S'.sheaf).flip.mapIso (pullbackUnitIso g).symm)

/-- Biduality `Lg^*((Mₙ^∨)^∨) ≅ Lg^*Mₙ` for an inverse system of perfect objects. -/
def bcStep₃ (M : ℕᵒᵖ ⥤ DStd S) (hM : ∀ n, IsPerfectSite (M.obj n)) :
    homSystem (dualSystem M) (unitObj S) ⋙ pullStd g ≅ M ⋙ pullStd g :=
  Functor.isoWhiskerRight (bidualSystemIso M hM).symm (pullStd g)

/-- The base change isomorphism `Lg^*Rf_* R𝓗om(Kₙ, E) ≅ Rf'_*L(g')^* R𝓗om(Kₙ, E)` of inverse
systems, when the base change map is invertible on the terms. -/
def bcStep₄ (F : ℕ ⥤ DStd X) (E : DStd X)
    (hbc : ∀ n, IsIso ((derivedBaseChangeSquare g'.toLRSHom.toShHom f'.toLRSHom.toShHom
      f.toLRSHom.toShHom g.toLRSHom.toShHom sq).app ((homSystem F E).obj n))) :
    pushforwardSheafHomSystem f F E ⋙ pullStd g ≅
      (homSystem F E ⋙ pullStd g') ⋙ pushStd f' :=
  baseChangeSystemIso f f' g g' sq (homSystem F E) hbc

/-- The isomorphism `Rf'_*L(g')^* R𝓗om(Kₙ, E) ≅ Rf'_* R𝓗om(L(g')^*Kₙ, L(g')^*E)` of inverse
systems, for perfect `Kₙ`. -/
def bcStep₅ (F : ℕ ⥤ DStd X) (hF : ∀ n, IsPerfectSite (F.obj n)) (E : DStd X) :
    (homSystem F E ⋙ pullStd g') ⋙ pushStd f' ≅
      pushforwardSheafHomSystem f' (F ⋙ pullStd g') ((pullStd g').obj E) :=
  Functor.isoWhiskerRight (pullbackSheafHomSystemIso g' F hF E) (pushStd f')

/-- The isomorphism of inverse systems
`R𝓗om(Lg^*Mₙ^∨, 𝒪_{S'}) ≅ Rf'_* R𝓗om(L(g')^*Kₙ, L(g')^*E)`, where `Mₙ = Rf_* R𝓗om(Kₙ, E)`. -/
def baseChangeSystemsIso (F : ℕ ⥤ DStd X) (hF : ∀ n, IsPerfectSite (F.obj n)) (E : DStd X)
    (hM : ∀ n, IsPerfectSite ((pushforwardSheafHomSystem f F E).obj n))
    (hbc : ∀ n, IsIso ((derivedBaseChangeSquare g'.toLRSHom.toShHom f'.toLRSHom.toShHom
      f.toLRSHom.toShHom g.toLRSHom.toShHom sq).app ((homSystem F E).obj n))) :
    homSystem (dualSystem (pushforwardSheafHomSystem f F E) ⋙ pullStd g)
        (unitObj S') ≅
      pushforwardSheafHomSystem f' (F ⋙ pullStd g') ((pullStd g').obj E) :=
  bcStep₁ g (dualSystem (pushforwardSheafHomSystem f F E)) ≪≫
    (pullbackSheafHomSystemIso g (dualSystem (pushforwardSheafHomSystem f F E))
      (isPerfectSite_dualSystem _ hM) (unitObj S)).symm ≪≫
    bcStep₃ g _ hM ≪≫ bcStep₄ f f' g g' sq F E hbc ≪≫ bcStep₅ f' g' F hF E

/-- Let `K = hocolim Kₙ` for perfect `Kₙ`, such that `Mₙ = Rf_* R𝓗om(Kₙ, E)` is perfect and the
base change map is invertible on the `R𝓗om(Kₙ, E)`, and let `L = hocolim Mₙ^∨`. For a commutative
square `g' ≫ f = f' ≫ g`,

`Rf'_* R𝓗om(L(g')^*K, L(g')^*E) ≅ R𝓗om(Lg^*L, 𝒪_{S'})`. -/
theorem nonempty_iso_pushforward_sheafHom_pullback (F : ℕ ⥤ DStd X)
    (hF : ∀ n, IsPerfectSite (F.obj n)) (E : DStd X) {K : DStd X} (hK : IsHomotopyColimit F K)
    (hM : ∀ n, IsPerfectSite ((pushforwardSheafHomSystem f F E).obj n))
    (hbc : ∀ n, IsIso ((derivedBaseChangeSquare g'.toLRSHom.toShHom f'.toLRSHom.toShHom
      f.toLRSHom.toShHom g.toLRSHom.toShHom sq).app ((homSystem F E).obj n)))
    {L : DStd S} (hL : IsHomotopyColimit (dualSystem (pushforwardSheafHomSystem f F E)) L) :
    Nonempty ((pushStd f').obj (((derivedSheafHom X'.sheaf).obj
        (op ((pullStd g').obj K))).obj ((pullStd g').obj E)) ≅
      ((derivedSheafHom S'.sheaf).obj (op ((pullStd g).obj L))).obj (unitObj S')) :=
  (isDerivedLimit_pushforwardSheafHomSystem f' (F ⋙ pullStd g') ((pullStd g').obj E)
    (hK.map (pullStd g'))).nonempty_iso (IsDerivedLimit.of_natIso
      (baseChangeSystemsIso f f' g g' sq F hF E hM hbc)
      (isDerivedLimit_derivedSheafHom_of_isHomotopyColimit S'.sheaf
        (dualSystem (pushforwardSheafHomSystem f F E) ⋙ pullStd g) (unitObj S')
        (hL.map (pullStd g))))

end BaseChange

section RelativelyPerfect

/-- Pseudo-coherence ([Stacks, Tag 08CB] part (3)) at the standard model. -/
abbrev IsPseudoCoherentStd {X : Scheme.{u}} (K : DStd X) : Prop :=
  AlgebraicGeometry.RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) K

/-- Relative perfectness ([Stacks, Tag 0DI0]) at the standard model. -/
abbrev IsRelPerfect {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    (E : DStd X) : Prop :=
  f.IsRelativelyPerfect E

/-- An `S`-perfect object is pseudo-coherent: this is the first clause of [Stacks, Tag 0DI0]. -/
theorem isPseudoCoherentStd_of_isRelPerfect {X S : Scheme.{u}} {f : X ⟶ S} [Flat f]
    [LocallyOfFinitePresentation f] {E : DStd X} (hE : IsRelPerfect f E) : IsPseudoCoherentStd E :=
  hE.1

/-- The perfectness predicate of the ringed space, read as the one of the ringed site. -/
theorem isPerfectSite_of_isPerfect_ringedSpace {X : Scheme.{u}} {K : DStd X}
    (hK : AlgebraicGeometry.RingedSpace.IsPerfect (X := X.toRingedSpace) K) : IsPerfectSite K :=
  (Stacks.Cohomology.PerfectComplexes.isPerfect_iff_ringedSite X.toRingedSpace K).1 hK

variable {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]

/-- Relative perfectness is invariant under isomorphism in `D(𝒪_X)`. -/
theorem isRelativelyPerfect_of_iso {E E' : DStd X} (e : E ≅ E') (h : f.IsRelativelyPerfect E) :
    f.IsRelativelyPerfect E' := by
  obtain ⟨⟨K, hK, ⟨e₀⟩⟩, I, U, hU, h₂⟩ := h
  refine ⟨⟨K, hK, ⟨e₀ ≪≫ e⟩⟩, I, U, hU, fun i => ?_⟩
  obtain ⟨a, b, hab⟩ := h₂ i
  refine ⟨a, b, fun F j hj => (hab F j hj).of_iso ?_⟩
  exact (DerivedCategory.homologyFunctor _ j).mapIso
    (((Stacks.Cohomology.TorAmplitude.derTensor.{u, u + 1} _).tensor.mapIso
      ((AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules _
        (U i)).mapDerivedCategory.mapIso
          ((Scheme.Hom.derivedScalarRestriction f).mapIso e))).app _).symm

end RelativelyPerfect

section TensorDual

open MonoidalCategory

attribute [local instance] derivedMonoidalStructure derivedSymmetricStructure

/-- `R𝓗om(P, E) ≅ P^∨ ⊗^L E` for a perfect `P`, with the tensor product read at the derived
tensor product of [Stacks, Tag 06YU]. -/
def sheafHomIsoDualTensor {X : Scheme.{u}} (P E : DStd X) (hP : IsPerfectSite P) :
    ((derivedSheafHom X.sheaf).obj (op P)).obj E ≅
      ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.sheaf).tensor.obj
        (derivedDual X.sheaf P)).obj E :=
  (@asIso _ _ _ _ (derivedTensorDualToSheafHom X.sheaf P E)
      (isIso_derivedTensorDualToSheafHom_of_isPerfect X.sheaf P E hP)).symm ≪≫
    β_ E (derivedDual X.sheaf P) ≪≫
    ((Stacks.Cohomology.DerivedInternalHomPullback.tensorBridge X.toRingedSpace).app
      (derivedDual X.sheaf P, E)).symm

end TensorDual

section Triangles

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- For a distinguished triangle `A ⟶ B ⟶ C ⟶ A⟦1⟧` of `D(𝒪_X)` and `E ∈ D(𝒪_X)`, the maps
`(Rf_* R𝓗om(A, E))^∨ ⟶ (Rf_* R𝓗om(B, E))^∨ ⟶ (Rf_* R𝓗om(C, E))^∨` induced by the two maps of
the triangle extend to a distinguished triangle of `D(𝒪_S)`. -/
theorem exists_distinguished_dual_pushforward_sheafHom (E : DStd X)
    (T : Pretriangulated.Triangle (DStd X)) (hT : T ∈ distTriang _) :
    ∃ δ, Pretriangulated.Triangle.mk
      (((derivedSheafHom S.sheaf).flip.obj (unitObj S)).map ((pushStd f).map
        (((derivedSheafHom X.sheaf).flip.obj E).map T.mor₁.op)).op)
      (((derivedSheafHom S.sheaf).flip.obj (unitObj S)).map ((pushStd f).map
        (((derivedSheafHom X.sheaf).flip.obj E).map T.mor₂.op)).op) δ ∈ distTriang (DStd S) := by
  obtain ⟨δ₁, h₁⟩ := RingedSite.exists_distinguished_derivedSheafHom (ringedSite X.sheaf) E T hT
  exact RingedSite.exists_distinguished_derivedSheafHom (ringedSite S.sheaf) (unitObj S) _
    ((pushStd f).map_distinguished _ h₁)

end Triangles

section ExtVanishing

open MonoidalCategory

attribute [local instance] derivedMonoidalStructure derivedSymmetricStructure

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Let `Q` be perfect on `X`, `E ∈ D(𝒪_X)`, `N = Rf_* R𝓗om(Q, E)` perfect and `Y ∈ D(𝒪_S)` such
that `N ⊗^L Y ≅ Rf_*(R𝓗om(Q, E) ⊗^L Lf^*Y)`. If every morphism `Q ⟶ E ⊗^L Lf^*Y` is zero, then
so is every morphism `N^∨ ⟶ Y`. -/
theorem subsingleton_hom_dual_pushforward_sheafHom (Q E : DStd X) (hQ : IsPerfectSite Q)
    (hN : IsPerfectSite ((pushStd f).obj (((derivedSheafHom X.sheaf).obj (op Q)).obj E)))
    (Y : DStd S)
    (e : (pushStd f).obj (((derivedSheafHom X.sheaf).obj (op Q)).obj E) ⊗ Y ≅
      (pushStd f).obj ((((derivedSheafHom X.sheaf).obj (op Q)).obj E) ⊗ (pullStd f).obj Y))
    (hvan : Subsingleton (Q ⟶ E ⊗ (pullStd f).obj Y)) :
    Subsingleton (derivedDual S.sheaf
      ((pushStd f).obj (((derivedSheafHom X.sheaf).obj (op Q)).obj E)) ⟶ Y) := by
  let N₀ := ((derivedSheafHom X.sheaf).obj (op Q)).obj E
  let N := (pushStd f).obj N₀
  let := exactPairingDerivedDual S.sheaf N hN
  let := exactPairingDerivedDual X.sheaf Q hQ
  let e₁ : ((derivedDual S.sheaf N : DStd S) ⟶ Y) ≃ (𝟙_ (DStd S) ⟶ N ⊗ Y) :=
    ((MonoidalCategory.rightUnitor (C := DStd S) (derivedDual S.sheaf N)).homCongr
      (Iso.refl Y)).symm.trans
      (tensorLeftHomEquiv (C := DStd S) (𝟙_ _) N (derivedDual S.sheaf N) Y)
  let e₂ : (𝟙_ (DStd S) ⟶ N ⊗ Y) ≃ (𝟙_ (DStd X) ⟶ N₀ ⊗ (pullStd f).obj Y) :=
    ((Iso.refl _).homCongr e).trans (((adjStd f).homEquiv _ _).symm.trans
      ((pullbackUnitIso f).homCongr (Iso.refl _)))
  let iN₀ : N₀ ≅ E ⊗ (derivedDual X.sheaf Q : DStd X) :=
    (@asIso _ _ _ _ (derivedTensorDualToSheafHom X.sheaf Q E)
      (isIso_derivedTensorDualToSheafHom_of_isPerfect X.sheaf Q E hQ)).symm
  let i₃ : N₀ ⊗ (pullStd f).obj Y ≅ (E ⊗ (pullStd f).obj Y) ⊗ (derivedDual X.sheaf Q : DStd X) :=
    whiskerRightIso iN₀ _ ≪≫ α_ _ _ _ ≪≫ whiskerLeftIso E (β_ _ _) ≪≫ (α_ _ _ _).symm
  let e₃ : (𝟙_ (DStd X) ⟶ N₀ ⊗ (pullStd f).obj Y) ≃ (Q ⟶ E ⊗ (pullStd f).obj Y) :=
    ((Iso.refl _).homCongr i₃).trans ((tensorRightHomEquiv (C := DStd X) (𝟙_ _) Q
      (derivedDual X.sheaf Q) (E ⊗ (pullStd f).obj Y)).symm.trans ((λ_ Q).homCongr (Iso.refl _)))
  exact (e₁.trans (e₂.trans e₃)).subsingleton

end ExtVanishing

end StandardModel

end Stacks.AlgebraicGeometry.RelativeDerivedHomDual
