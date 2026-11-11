module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.PowerSeries.Inverse
public import StacksFrontier.AlgebraicGeometry.Descent.SchemeProperty.Regular
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianSchemeBaseChange
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.Torsion
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreStalk
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.LocallyProjective
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension
public import StacksFrontier.AlgebraicGeometry.Properties.NormalConnectedIntegral
public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Topologies.FppfCompletedLocalRing
public import StacksFrontier.Examples.Stacks.NonAlgebraicHomStack.Situation
public import StacksFrontier.RingTheory.RegularLocalRing.FlatLocalHom

/-!
# Geometry of the standing data of the non-algebraic Hom-stack

Section 0AF8 of the source fixes a projective flat morphism `f : X ⟶ S = Spec k⟦t⟧` with
geometrically connected one-dimensional fibres and `X` regular, and a non-zero abelian variety
`A₀` over `k` with constant abelian scheme `A = A₀ ×_k S`. The proofs of Lemma 0AFB and
Proposition 0AFC use, without comment, that `X` is a regular integral Noetherian scheme of
dimension two (the source calls `X` a surface) and that `A` is an abelian scheme over `S`. This
file derives these facts from `Stacks.Examples.NonAlgebraicHomStack.Situation`, together with the
membership of the schemes involved in a big fppf site containing `S`.

## Main results

* `AlgebraicGeometry.topologicalKrullDim_eq_add_of_flat_of_forall_fiber`: for a flat morphism of
  locally Noetherian schemes all of whose fibres have dimension `d`, the dimension of the source
  is that of the target plus `d`.
* `Stacks.Examples.NonAlgebraicHomStack.Situation.isNoetherian`, `.isRegular`, `.isIntegral`,
  `.topologicalKrullDim_eq_two`: `X` is a Noetherian, regular, integral scheme of dimension two.
* `Stacks.Examples.NonAlgebraicHomStack.Situation.isAbelianScheme`: `A = A₀ ×_k S` is an abelian
  scheme over `S`.
* `Stacks.Examples.NonAlgebraicHomStack.Situation.contains_X`, `.contains_thickening`,
  `.contains_abelianScheme`, `.contains_spec_functionField`: these schemes lie in every big fppf
  site containing `S`.

## Implementation notes

* *Integrality.* The source does not argue it. `f` is flat and locally of finite presentation,
  hence open, and its fibres are connected, so `X` is connected as `S` is; a connected regular
  locally Noetherian scheme is normal, hence integral.
* *Dimension.* At every point `x` over `s`, the local dimension formula for the flat local
  homomorphism `𝒪_{S,s} → 𝒪_{X,x}` gives `dim 𝒪_{X,x} = dim 𝒪_{S,s} + dim 𝒪_{X_s,x}`; taking
  suprema, `dim X = dim S + 1 = 2` as `k⟦t⟧` is a discrete valuation ring.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Dimension of the source of a flat morphism with fibres of constant dimension.** Let
`f : X ⟶ Y` be a flat morphism of locally Noetherian schemes all of whose fibres have dimension
`d`. Then `dim X = dim Y + d`: both sides are suprema of Krull dimensions of local rings, and for
each point `x` of `X` the flat local homomorphism `𝒪_{Y,f x} → 𝒪_{X,x}` satisfies
`dim 𝒪_{X,x} = dim 𝒪_{Y,f x} + dim 𝒪_{X_{f x},x}`. -/
theorem topologicalKrullDim_eq_add_of_flat_of_forall_fiber {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y) [Flat f] {d : ℕ}
    (hf : ∀ y : Y, topologicalKrullDim (f.fiber y) = (d : WithBot ℕ∞)) :
    topologicalKrullDim X = topologicalKrullDim Y + (d : WithBot ℕ∞) := by
  have hne : ∀ (R : Type u) [CommRing R] [IsLocalRing R], ringKrullDim R ≠ ⊥ := fun R _ _ ↦
    ne_bot_of_le_ne_bot (by simp) ringKrullDim_nonneg_of_nontrivial
  have hadd : ∀ {ι : Type u} (a : WithBot ℕ∞) (g : ι → WithBot ℕ∞), (∀ i, g i ≠ ⊥) →
      a + ⨆ i, g i = ⨆ i, a + g i := by
    intro ι a g hg
    rcases isEmpty_or_nonempty ι with hι | hι
    · simp
    cases a with
    | bot => simp
    | coe a =>
      let h : ι → ℕ∞ := fun i ↦ WithBot.unbotD (α := ℕ∞) 0 (g i)
      have hgh : ∀ i, g i = (h i : WithBot ℕ∞) := by
        intro i
        cases hi : g i with
        | bot => exact (hg i hi).elim
        | coe b => simp [h, hi]
      have hsup : (⨆ i, g i) = ((⨆ i, h i : ℕ∞) : WithBot ℕ∞) :=
        (iSup_congr hgh).trans (WithBot.coe_iSup (f := h) (OrderTop.bddAbove _)).symm
      rw [hsup, ← WithBot.coe_add, ENat.add_iSup,
        WithBot.coe_iSup (f := fun i ↦ a + h i) (OrderTop.bddAbove _)]
      exact iSup_congr fun i ↦ by rw [WithBot.coe_add, ← hgh i]
  have hstalk : ∀ x : X, ringKrullDim (X.presheaf.stalk x) =
      ringKrullDim (Y.presheaf.stalk (f x)) +
        ringKrullDim ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) := by
    intro x
    let R := Y.presheaf.stalk (f x)
    let S := X.presheaf.stalk x
    let : Algebra R S := (f.stalkMap x).hom.toAlgebra
    have : IsLocalHom (algebraMap R S) := inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
    have h := ringKrullDim_eq_add_ringKrullDim_closedFibre R S (Flat.stalkMap f x)
    have he := ringKrullDim_eq_of_ringEquiv (quotientStalkEquivFiberStalk f x)
    simpa only [R, S] using
      h.trans (congrArg (fun n : WithBot ℕ∞ ↦ ringKrullDim R + n) he)
  have hFdim : ∀ y : Y,
      (⨆ z : f.fiber y, ringKrullDim ((f.fiber y).presheaf.stalk z)) = (d : WithBot ℕ∞) := by
    intro y
    rw [← topologicalKrullDim_eq_iSup_krullDimOfRing_stalk (f.fiber y)]
    exact hf y
  rw [topologicalKrullDim_eq_iSup_krullDimOfRing_stalk X,
    topologicalKrullDim_eq_iSup_krullDimOfRing_stalk Y]
  refine le_antisymm (iSup_le fun x ↦ ?_) ?_
  · rw [hstalk x]
    calc ringKrullDim (Y.presheaf.stalk (f x)) +
          ringKrullDim ((f.fiber (f x)).presheaf.stalk (f.asFiber x))
        ≤ ringKrullDim (Y.presheaf.stalk (f x)) + (d : WithBot ℕ∞) := by
          gcongr
          exact hFdim (f x) ▸ le_iSup (fun w : f.fiber (f x) ↦
            ringKrullDim ((f.fiber (f x)).presheaf.stalk w)) (f.asFiber x)
      _ ≤ (⨆ y : Y, ringKrullDim (Y.presheaf.stalk y)) + (d : WithBot ℕ∞) := by
          gcongr
          exact le_iSup (fun y : Y ↦ ringKrullDim (Y.presheaf.stalk y)) (f x)
  · rw [show (⨆ y : Y, ringKrullDim (Y.presheaf.stalk y)) + (d : WithBot ℕ∞) =
        ⨆ y : Y, ringKrullDim (Y.presheaf.stalk y) + (d : WithBot ℕ∞) by
      rw [add_comm, hadd (d : WithBot ℕ∞) (fun y : Y ↦ ringKrullDim (Y.presheaf.stalk y))
        fun y ↦ hne _]
      exact iSup_congr fun y ↦ add_comm _ _]
    refine iSup_le fun y ↦ ?_
    rw [← hFdim y, hadd _ _ fun z ↦ hne _]
    refine iSup_le fun z ↦ ?_
    have hbase : f (f.fiberι y z) = y := by
      simpa using (f.fiberHomeo y z).property
    have hfiberDim : ringKrullDim ((f.fiber y).presheaf.stalk z) =
        ringKrullDim ((f.fiber (f (f.fiberι y z))).presheaf.stalk
          (f.asFiber (f.fiberι y z))) := by
      have hcast : ∀ {y y' : Y} (h : y = y') (w : f.fiber y),
          ringKrullDim ((f.fiber y).presheaf.stalk w) =
            ringKrullDim ((f.fiber y').presheaf.stalk (h ▸ w)) := by
        intro y y' h w
        cases h
        rfl
      have hdim := hcast hbase (f.asFiber (f.fiberι y z))
      rw [Scheme.Hom.cast_asFiber_fiberι f y z hbase] at hdim
      exact hdim.symm
    rw [show ringKrullDim (Y.presheaf.stalk y) =
      ringKrullDim (Y.presheaf.stalk (f (f.fiberι y z))) by rw [hbase], hfiberDim,
      ← hstalk (f.fiberι y z)]
    exact le_iSup (fun x : X ↦ ringKrullDim (X.presheaf.stalk x)) (f.fiberι y z)

/-- An abelian variety over a field `k` is an abelian scheme over `Spec k`: its only fibre is
its base change along the isomorphism `Spec κ(x) ⟶ Spec k`, an abelian variety by Stacks 0BFB. -/
instance isAbelianScheme_of_isAbelianVariety {k : Type u} [Field k] (A : Over (Spec (.of k)))
    [GrpObj A] [IsAbelianVariety k A] : IsAbelianScheme A where
  toFlat := inferInstance
  toIsProper := inferInstance
  toLocallyOfFinitePresentation :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  fibre_isAbelianVariety x := by
    let g : Spec ((Spec (.of k)).residueField x) ⟶ Spec (.of k) :=
      (Spec (.of k)).fromSpecResidueField x
    let φ : CommRingCat.of k ⟶ (Spec (.of k)).residueField x := Spec.preimage g
    let _ : Algebra k ((Spec (.of k)).residueField x) := φ.hom.toAlgebra
    have hg : Spec.map (CommRingCat.ofHom (algebraMap k ((Spec (.of k)).residueField x))) = g :=
      Spec.map_preimage g
    have hA := isAbelianVariety_pullbackObj (k := k) (K := (Spec (.of k)).residueField x) A
    exact IsAbelianVariety.of_iso (eqToIso (congrArg (fun h ↦ (Over.pullback h).obj A) hg))

end AlgebraicGeometry

open AlgebraicGeometry

namespace Stacks.Examples.NonAlgebraicHomStack

variable {k : Type u} [Field k]

namespace Situation

variable (sit : Situation k)

/-- The family `f : X ⟶ S` is proper. -/
theorem isProper : IsProper sit.f := sit.isProjective.isProper

/-- The family `f : X ⟶ S` is locally of finite presentation, `S` being Noetherian. -/
theorem locallyOfFinitePresentation : LocallyOfFinitePresentation sit.f :=
  have := sit.isProper
  LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance

/-- **`X` is Noetherian**: it is of finite type over the Noetherian scheme `Spec k⟦t⟧`. -/
theorem isNoetherian : IsNoetherian sit.X :=
  have := sit.isProper
  have : IsLocallyNoetherian sit.X := LocallyOfFiniteType.isLocallyNoetherian sit.f
  have : CompactSpace sit.X := QuasiCompact.compactSpace_of_compactSpace sit.f
  {}

/-- **`X` is regular**, as a locally Noetherian scheme all of whose local rings are regular. -/
theorem isRegular : IsRegular sit.X :=
  have := sit.isNoetherian
  (isRegular_iff_regular_stalks sit.X).mpr ⟨inferInstance, sit.regular⟩

/-- **`X` is connected**: `f` is flat and locally of finite presentation, hence open, with
connected fibres, over the connected scheme `S`. -/
theorem connectedSpace : ConnectedSpace sit.X :=
  have := sit.flat
  have := sit.geometricallyConnected
  have := sit.locallyOfFinitePresentation
  GeometricallyConnected.connectedSpace sit.f sit.f.isOpenMap

/-- **`X` is integral**: a connected regular locally Noetherian scheme is normal and connected,
hence integral. -/
theorem isIntegral : IsIntegral sit.X :=
  have := sit.isNoetherian
  have := sit.connectedSpace
  have : IsNormal sit.X := isNormal_of_isRegular sit.X sit.isRegular
  isIntegral_of_isNormal_of_connectedSpace sit.X

/-- **`X` is a surface**: it has dimension `dim S + 1 = 2`, `f` being flat with fibres of
dimension one over the spectrum `S` of the discrete valuation ring `k⟦t⟧`. -/
theorem topologicalKrullDim_eq_two : topologicalKrullDim sit.X = (2 : WithBot ℕ∞) := by
  have := sit.isNoetherian
  have := sit.flat
  have hS : topologicalKrullDim (base k) = 1 := by
    change topologicalKrullDim (PrimeSpectrum (PowerSeries k)) = 1
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact IsDiscreteValuationRing.ringKrullDim_eq_one (PowerSeries k)
  rw [topologicalKrullDim_eq_add_of_flat_of_forall_fiber sit.f (d := 1)
    (fun s ↦ by exact_mod_cast sit.dim_fiber s), hS]
  rfl

/-- **The constant abelian scheme `A = A₀ ×_k S` is an abelian scheme over `S`**, as a base
change of the abelian variety `A₀`. -/
instance isAbelianScheme : IsAbelianScheme sit.abelianScheme :=
  have := sit.isAbelianVariety
  isAbelianScheme_overPullbackObj baseToField sit.A₀

variable {B : BigFppfSite.{u}} (hS : B.Contains (base k))
include hS

/-- `X` lies in every big fppf site containing `S`, being of finite type over `S`. -/
theorem contains_X : B.Contains sit.X :=
  have := sit.isProper
  (Scheme.size_le_of_locallyOfFiniteType_of_quasiCompact sit.f).trans_lt hS

/-- The thickenings `Xₙ = X ×_S Spec (k⟦t⟧ / (tⁿ⁺¹))` lie in every big fppf site containing `S`,
being closed subschemes of `X`. -/
theorem contains_thickening (n : ℕ) : B.Contains (thickening sit.f n) := by
  have : IsClosedImmersion (adicThickeningι (PowerSeries k) (uniformizer k) n) := by
    unfold adicThickeningι
    exact IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  exact (Scheme.size_le_of_locallyOfFiniteType_of_quasiCompact
    (thickeningToTotal sit.f n)).trans_lt (sit.contains_X hS)

/-- The abelian scheme `A = A₀ ×_k S` lies in every big fppf site containing `S`, being of finite
type over `S`. -/
theorem contains_abelianScheme : B.Contains sit.abelianScheme.left :=
  have := sit.isAbelianVariety
  (Scheme.size_le_of_locallyOfFiniteType_of_quasiCompact sit.abelianScheme.hom).trans_lt hS

/-- The spectrum of the function field of `X` lies in every big fppf site containing `S`. -/
theorem contains_spec_functionField :
    have := sit.isIntegral
    B.Contains (Spec sit.X.functionField) :=
  BigFppfSite.contains_spec_stalk_of_contains B (sit.contains_X hS) _

end Situation

end Stacks.Examples.NonAlgebraicHomStack
