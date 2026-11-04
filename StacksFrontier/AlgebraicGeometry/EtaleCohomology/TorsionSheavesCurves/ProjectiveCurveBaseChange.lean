module

public import Mathlib.RingTheory.Algebraic.Cardinality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.TorsionSheafSituation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ArithmeticFrobeniusInverse
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Product
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.LocallyProjective
public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs

/-!
# The base change of a projective curve to an algebraically closed field

Let `X` be a projective curve over a field `k`, with structure morphism `g : X ⟶ Spec k`, and let
`k̄` be an algebraically closed extension of `k`. The base change
`X_{k̄} = X ×_{Spec k} Spec k̄` (`Stacks.Frobenius.fieldBaseChange`) with its projection to
`Spec k̄` is in Situation 0A52 of the Stacks project: separated, of finite type, of dimension at
most one, and moreover proper. This file records these facts, for `X_{k̄}` and for any scheme
identified with it over `Spec k̄`, together with the corresponding instance of
`Stacks.EtaleCohomology.TorsionSheafSituation`; it also shows that `X_{k̄}` lies in every big
étale site containing `X` when `k̄` is algebraic over `k`.

## Main results

* `Stacks.EtaleCohomology.ProjectiveCurveBaseChange.isProper_snd` and its companions:
  the projection `X_{k̄} ⟶ Spec k̄` is separated, locally of finite type, quasi-compact and proper.
* `Stacks.EtaleCohomology.ProjectiveCurveBaseChange.topologicalKrullDim_le_one`:
  `X_{k̄}` has dimension at most one.
* `Stacks.EtaleCohomology.ProjectiveCurveBaseChange.torsionSheafSituationOfIso`: the situation
  of Tag 0A52 attached to a scheme identified with `X_{k̄}` and a torsion sheaf on it.
* `Stacks.EtaleCohomology.ProjectiveCurveBaseChange.contains_fieldBaseChange`: if `k̄` is
  algebraic over `k`, then `X_{k̄}` lies in every big étale site containing `X`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Cardinal

universe v u

namespace Stacks.EtaleCohomology.ProjectiveCurveBaseChange

variable {k : Type u} [Field k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k))
  (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- The projection `X_{k̄} ⟶ Spec k̄` of the base change of a curve is separated. -/
theorem isSeparated_snd (hcurve : IsCurve k g) :
    IsSeparated (pullback.snd (Over.mk g).hom (Stacks.Frobenius.specAlgebraMap k kbar)) := by
  have : IsSeparated g := hcurve.toIsSeparated
  exact inferInstanceAs (IsSeparated (pullback.snd g _))

/-- The projection `X_{k̄} ⟶ Spec k̄` of the base change of a curve is locally of finite type. -/
theorem locallyOfFiniteType_snd (hcurve : IsCurve k g) :
    LocallyOfFiniteType
      (pullback.snd (Over.mk g).hom (Stacks.Frobenius.specAlgebraMap k kbar)) := by
  have : LocallyOfFiniteType g := hcurve.toLocallyOfFiniteType
  exact inferInstanceAs (LocallyOfFiniteType (pullback.snd g _))

/-- The projection `X_{k̄} ⟶ Spec k̄` of the base change of a curve is quasi-compact. -/
theorem quasiCompact_snd (hcurve : IsCurve k g) :
    QuasiCompact (pullback.snd (Over.mk g).hom (Stacks.Frobenius.specAlgebraMap k kbar)) := by
  have : QuasiCompact g := hcurve.toQuasiCompact
  exact inferInstanceAs (QuasiCompact (pullback.snd g _))

/-- The projection `X_{k̄} ⟶ Spec k̄` of the base change of a projective scheme is proper. -/
theorem isProper_snd (hproj : IsProjective g) :
    IsProper (pullback.snd (Over.mk g).hom (Stacks.Frobenius.specAlgebraMap k kbar)) := by
  have : IsProper g := hproj.isProper
  exact inferInstanceAs (IsProper (pullback.snd g _))

/-- The base change `X_{k̄}` of a curve has dimension at most one. -/
theorem topologicalKrullDim_le_one (hcurve : IsCurve k g) :
    topologicalKrullDim (Stacks.Frobenius.fieldBaseChange (Over.mk g) kbar) ≤ 1 := by
  have : LocallyOfFiniteType g := hcurve.toLocallyOfFiniteType
  exact (topologicalKrullDim_pullback_spec_algebraMap k kbar g).trans_le
    hcurve.topologicalKrullDim_eq_one.le

section Iso

variable {g kbar} {Y : Scheme.{u}} (e : Y ≅ Stacks.Frobenius.fieldBaseChange (Over.mk g) kbar)

/-- A scheme identified with `X_{k̄}` is separated over `Spec k̄`. -/
theorem isSeparated_of_iso (hcurve : IsCurve k g) :
    IsSeparated (e.hom ≫ pullback.snd (Over.mk g).hom (Stacks.Frobenius.specAlgebraMap k kbar)) :=
  have := isSeparated_snd g kbar hcurve
  inferInstance

/-- A scheme identified with `X_{k̄}` is locally of finite type over `Spec k̄`. -/
theorem locallyOfFiniteType_of_iso (hcurve : IsCurve k g) :
    LocallyOfFiniteType
      (e.hom ≫ pullback.snd (Over.mk g).hom (Stacks.Frobenius.specAlgebraMap k kbar)) :=
  have := locallyOfFiniteType_snd g kbar hcurve
  inferInstance

/-- A scheme identified with `X_{k̄}` is quasi-compact over `Spec k̄`. -/
theorem quasiCompact_of_iso (hcurve : IsCurve k g) :
    QuasiCompact (e.hom ≫ pullback.snd (Over.mk g).hom (Stacks.Frobenius.specAlgebraMap k kbar)) :=
  have := quasiCompact_snd g kbar hcurve
  inferInstance

/-- A scheme identified with the base change of a projective scheme is proper over `Spec k̄`. -/
theorem isProper_of_iso (hproj : IsProjective g) :
    IsProper (e.hom ≫ pullback.snd (Over.mk g).hom (Stacks.Frobenius.specAlgebraMap k kbar)) :=
  have := isProper_snd g kbar hproj
  inferInstance

include e in
/-- A scheme identified with `X_{k̄}` has dimension at most one. -/
theorem topologicalKrullDim_le_one_of_iso (hcurve : IsCurve k g) :
    topologicalKrullDim Y ≤ 1 :=
  (IsHomeomorph.topologicalKrullDim_eq _ e.hom.homeomorph.isHomeomorph).le.trans
    (topologicalKrullDim_le_one g kbar hcurve)

/-- **The situation of Tag 0A52 on the base change of a curve.** For a curve `X` over `k`, an
algebraically closed extension `k̄` of `k`, a scheme `Y` identified with `X_{k̄}`, and a torsion
abelian sheaf `F` on the small étale site of `Y`: the data of Situation 0A52, with structure
morphism `Y ≅ X_{k̄} ⟶ Spec k̄`. -/
def torsionSheafSituationOfIso [IsAlgClosed kbar] (hcurve : IsCurve k g)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hF : Stacks.Torsion.torsionSheafProperty Y.smallEtaleTopology F) :
    TorsionSheafSituation.{u, v} where
  k := kbar
  X := Y
  structureMorphism := e.hom ≫ pullback.snd (Over.mk g).hom (Stacks.Frobenius.specAlgebraMap k kbar)
  isSeparated := isSeparated_of_iso e hcurve
  locallyOfFiniteType := locallyOfFiniteType_of_iso e hcurve
  quasiCompact := quasiCompact_of_iso e hcurve
  dimension_le_one := topologicalKrullDim_le_one_of_iso e hcurve
  F := F
  isTorsion := hF

end Iso

/-- **The situation of Tag 0A52 on `X_{k̄}` itself**, with structure morphism the projection
`X_{k̄} ⟶ Spec k̄`. -/
def torsionSheafSituation [IsAlgClosed kbar] (hcurve : IsCurve k g)
    (F : Sheaf (Stacks.Frobenius.fieldBaseChange (Over.mk g) kbar).smallEtaleTopology
      AddCommGrpCat.{max (u + 1) v})
    (hF : Stacks.Torsion.torsionSheafProperty
      (Stacks.Frobenius.fieldBaseChange (Over.mk g) kbar).smallEtaleTopology F) :
    TorsionSheafSituation.{u, v} :=
  torsionSheafSituationOfIso (Iso.refl _) hcurve F hF

include g in
/-- The cardinality of a field is bounded by the size of every nonempty scheme over it. -/
theorem mk_le_size_of_nonempty [Nonempty X] : #k ≤ X.size := by
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨W, hW, hxW, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  have : Nonempty W := ⟨⟨x, hxW⟩⟩
  let φ : k →+* Γ(X, W) :=
    (X.presheaf.map (homOfLE le_top).op).hom.comp
      (g.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)
  exact (mk_le_of_injective φ.injective).trans (Scheme.mk_sections_le_size X ⟨W, hW⟩)

/-- **The base change to an algebraic extension stays in the big étale site.** If `k̄` is
algebraic over `k` and `X` lies in a big étale site `B`, then `X_{k̄}` lies in `B` too: `X_{k̄}`
is of finite type over `Spec k̄`, whose size is at most `max(|k|, ℵ₀)`, and `|k|` is bounded by
the size of `X` when `X` is nonempty; when `X` is empty so is `X_{k̄}`. -/
theorem contains_fieldBaseChange [Algebra.IsAlgebraic k kbar] (B : BigEtaleSite.{u})
    (hX : B.Contains X) (hfin : LocallyOfFiniteType g) (hqc : QuasiCompact g) :
    B.Contains (Stacks.Frobenius.fieldBaseChange (Over.mk g) kbar) := by
  rcases isEmpty_or_nonempty X with hE | hN
  · have : IsEmpty (Stacks.Frobenius.fieldBaseChange (Over.mk g) kbar) :=
      ⟨fun y ↦ hE.elim ((pullback.fst (Over.mk g).hom
        (Stacks.Frobenius.specAlgebraMap k kbar)).base y)⟩
    have : Mono (pullback.fst (Over.mk g).hom (Stacks.Frobenius.specAlgebraMap k kbar)) :=
      isInitialOfIsEmpty.mono_from _
    exact Scheme.size_lt_of_mono_of_isStrongPrelimit B.cutoff_isStrongPrelimit
      (pullback.fst (Over.mk g).hom (Stacks.Frobenius.specAlgebraMap k kbar)) hX
  · have hsnd := Scheme.size_le_of_locallyOfFiniteType_of_quasiCompact
      (pullback.snd g (Stacks.Frobenius.specAlgebraMap k kbar))
    have hk : #k < B.cutoff := (mk_le_size_of_nonempty g).trans_lt hX
    have hkbar : #kbar ≤ max #k ℵ₀ := Algebra.IsAlgebraic.cardinalMk_le_max k kbar
    show (pullback g (Stacks.Frobenius.specAlgebraMap k kbar)).size < B.cutoff
    refine hsnd.trans_lt ?_
    rw [Scheme.size_Spec]
    exact max_lt B.aleph0_lt_cutoff
      (hkbar.trans_lt (max_lt hk B.aleph0_lt_cutoff))

end Stacks.EtaleCohomology.ProjectiveCurveBaseChange

end
