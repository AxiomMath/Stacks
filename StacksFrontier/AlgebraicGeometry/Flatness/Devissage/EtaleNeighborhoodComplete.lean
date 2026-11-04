module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.DevissageNoetherian.Support
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.BaseChange
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.Transport
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.EtaleNeighborhoodOneStep

/-!
# Complete dévissage after elementary étale neighbourhoods

Stacks 05HR asserts that a finite-type quasi-coherent module `F` on a scheme `X` locally of
finite type over `S` acquires a complete dévissage at a chosen point `x` after passing to
elementary étale neighbourhoods of `x` and of its image. Its proof is an induction on the
dimension of the support of `F` on the fibre of `X` through `x`, whose base step is Stacks 05H6
— the same statement with *one-step* dévissage in place of complete dévissage.

This module collects the two terminal cases of that induction, in which no further dévissage is
needed: the case where `x` does not lie in the support at all, which is the case the empty
dévissage was introduced for, and the case where the free-module map produced by Stacks 05HF
already has zero cokernel, in which the one-step dévissage *is* a complete dévissage of length
one.

## Main definitions

* `AlgebraicGeometry.DevissageStage.ofOneStepDevissageAt`: a one-step dévissage at a point,
  together with a free-module map invertible over the generic point of the distinguished fibre,
  is a stage of a complete dévissage.
* `AlgebraicGeometry.NonemptyCompleteDevissageAt.ofOneStepDevissageAt`: such a stage whose
  free-module map has zero cokernel is a complete dévissage at the point, of length one.

## Main results

* `AlgebraicGeometry.exists_etaleNeighborhood_completeDevissageAt_of_notMem_supp`: Stacks 05HR
  for a point outside the support of the module, where the complete dévissage obtained is the
  empty one.
* `AlgebraicGeometry.exists_etaleNeighborhood_completeDevissageAt_of_etaleNeighborhood`: the
  conclusion of Stacks 05HR is local for elementary étale neighbourhoods, so that the induction
  may pass to one at any point.

## Implementation notes

For a point outside the support, the elementary étale neighbourhood chosen is an *open*
neighbourhood: the complement of the support, which is open because the support of a finite-type
module is closed, and on which the module therefore pulls back to zero. An open immersion is
étale and induces isomorphisms on residue fields, so this is an elementary étale neighbourhood,
and the base needs no shrinking at all — the identity of `S` serves as its neighbourhood. This
is the only case in which the complete dévissage produced is the empty one, and it is the reason
`AlgebraicGeometry.CompleteDevissageAt` has an empty constructor: Stacks 05HR imposes no
hypothesis on the support, so for `F = 0` nothing but the empty dévissage can satisfy it.

## References

* [Stacks Project, Tag 05HR](https://stacks.math.columbia.edu/tag/05HR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### A one-step dévissage with zero cokernel -/

variable {X S : Scheme.{u}} {f : X ⟶ S} {F : X.Modules} {x : X} [LocallyOfFiniteType f]
  [F.IsQuasicoherent] [F.IsFiniteType]

/-- A one-step dévissage at `x`, together with a map from a finite free module to the direct
image of its module which becomes an isomorphism over the residue field of the generic point of
the distinguished fibre, is a stage of a complete dévissage. The generic point is the one
supplied by `AlgebraicGeometry.OneStepDevissage.fiberGenericPoint`, which exists because the
smooth structure morphism of a one-step dévissage has geometrically irreducible fibres. -/
def DevissageStage.ofOneStepDevissageAt (D : OneStepDevissageAt f F x) (r : ℕ)
    (α : SheafOfModules.free (R := D.toOneStepDevissage.Y.ringCatSheaf) (ULift.{u} (Fin r)) ⟶
      (Scheme.Modules.pushforward D.toOneStepDevissage.π).obj D.toOneStepDevissage.G)
    (hα : IsIso ((Scheme.Modules.pullback (D.toOneStepDevissage.Y.fromSpecResidueField
      (D.toOneStepDevissage.g.fiberι (f x)
        D.toOneStepDevissage.fiberGenericPoint))).map α)) : DevissageStage f F (f x) where
  oneStep := D.toOneStepDevissage
  rank := r
  alpha := α
  genericPoint := D.toOneStepDevissage.fiberGenericPoint
  genericPoint_spec := D.toOneStepDevissage.isGenericPoint_fiberGenericPoint
  genericFiber_isIso := hα

/-- The stage of `AlgebraicGeometry.DevissageStage.ofOneStepDevissageAt` is pointed by the
distinguished points of the one-step dévissage it comes from. -/
def PointedDevissageStage.ofOneStepDevissageAt (D : OneStepDevissageAt f F x) (r : ℕ)
    (α : SheafOfModules.free (R := D.toOneStepDevissage.Y.ringCatSheaf) (ULift.{u} (Fin r)) ⟶
      (Scheme.Modules.pushforward D.toOneStepDevissage.π).obj D.toOneStepDevissage.G)
    (hα : IsIso ((Scheme.Modules.pullback (D.toOneStepDevissage.Y.fromSpecResidueField
      (D.toOneStepDevissage.g.fiberι (f x)
        D.toOneStepDevissage.fiberGenericPoint))).map α)) :
    PointedDevissageStage f F (f x) x (DevissageStage.ofOneStepDevissageAt D r α hα) where
  atPoint := D
  sameOneStep := HEq.rfl
  y := D.y
  sameY := HEq.rfl

namespace NonemptyCompleteDevissageAt

/-- A one-step dévissage at `x` whose free-module map is invertible over the generic point of the
distinguished fibre and has zero cokernel is a complete dévissage at `x`: the chain consists of
that single stage, which is final because its cokernel vanishes. -/
def ofOneStepDevissageAt (D : OneStepDevissageAt f F x) (r : ℕ)
    (α : SheafOfModules.free (R := D.toOneStepDevissage.Y.ringCatSheaf) (ULift.{u} (Fin r)) ⟶
      (Scheme.Modules.pushforward D.toOneStepDevissage.π).obj D.toOneStepDevissage.G)
    (hα : IsIso ((Scheme.Modules.pullback (D.toOneStepDevissage.Y.fromSpecResidueField
      (D.toOneStepDevissage.g.fiberι (f x)
        D.toOneStepDevissage.fiberGenericPoint))).map α))
    (hzero : IsZero (cokernel α)) : NonemptyCompleteDevissageAt f F x where
  toNonemptyCompleteDevissage :=
    ⟨.last (DevissageStage.ofOneStepDevissageAt D r α hα) hzero⟩
  pointed := .last x (DevissageStage.ofOneStepDevissageAt D r α hα) hzero
    (PointedDevissageStage.ofOneStepDevissageAt D r α hα)

end NonemptyCompleteDevissageAt

/-! ### Points outside the support -/

/-- The complement of the support of a finite-type module, as an open subscheme. -/
def suppCompl (F : X.Modules) [F.IsFiniteType] : X.Opens :=
  ⟨(SheafOfModules.supp F)ᶜ,
    (Stacks.AlgebraicGeometry.DevissageNoetherian.isClosed_supp X.sheaf F).isOpen_compl⟩

/-- A finite-type module pulls back to zero on the complement of its support. -/
lemma isZero_pullback_suppCompl (F : X.Modules) [F.IsFiniteType] :
    IsZero ((Scheme.Modules.pullback (suppCompl F).ι).obj F) :=
  Stacks.AlgebraicGeometry.DevissageNoetherian.isZero_of_supp_eq_empty _ <| by
    rw [Stacks.Modules.supp_pullback]
    exact Set.eq_empty_of_forall_notMem fun p hp => p.property hp

/-- **Stacks Project, Tag 05HR, the case of a point outside the support.** A finite-type
quasi-coherent module admits a complete dévissage at a point outside its support after
elementary étale neighbourhoods of the point and of its image — namely the empty one, on the
open complement of the support. -/
theorem exists_etaleNeighborhood_completeDevissageAt_of_notMem_supp (f : X ⟶ S)
    [LocallyOfFiniteType f] (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent] (x : X)
    (hx : x ∉ SheafOfModules.supp F) :
    ∃ (U : EtaleNeighborhood X x) (V : EtaleNeighborhood S (f x)) (h : U.scheme ⟶ V.scheme),
      U.IsElementary ∧ V.IsElementary ∧ (U.toBase ≫ f = h ≫ V.toBase) ∧ (h U.point = V.point) ∧
        ∃ (hft : LocallyOfFiniteType h)
          (hq : ((Scheme.Modules.pullback U.toBase).obj F).IsQuasicoherent)
          (hf : ((Scheme.Modules.pullback U.toBase).obj F).IsFiniteType),
          letI : LocallyOfFiniteType h := hft
          letI : ((Scheme.Modules.pullback U.toBase).obj F).IsQuasicoherent := hq
          letI : ((Scheme.Modules.pullback U.toBase).obj F).IsFiniteType := hf
          Nonempty (CompleteDevissageAt h
            ((Scheme.Modules.pullback U.toBase).obj F) U.point) := by
  have hft : LocallyOfFiniteType ((suppCompl F).ι ≫ f) :=
    MorphismProperty.IsStableUnderComposition.comp_mem _ _ inferInstance inferInstance
  have hqc : ((Scheme.Modules.pullback (suppCompl F).ι).obj F).IsQuasicoherent := inferInstance
  have hfin : ((Scheme.Modules.pullback (suppCompl F).ι).obj F).IsFiniteType :=
    SheafOfModules.pullback_isFiniteType (suppCompl F).ι.toLRSHom.toShHom F
  exact ⟨EtaleNeighborhood.ofEtale (suppCompl F).ι ⟨x, hx⟩, EtaleNeighborhood.self S (f x),
    (suppCompl F).ι ≫ f, EtaleNeighborhood.isElementary_ofEtale_of_isOpenImmersion _ _,
    EtaleNeighborhood.isElementary_self S (f x), (Category.comp_id _).symm, rfl,
    hft, hqc, hfin,
    ⟨@CompleteDevissageAt.empty _ _ _ _ _ hft hqc hfin (isZero_pullback_suppCompl F)⟩⟩

/-! ### Locality of the conclusion in the étale topology -/

/-- **The conclusion of Stacks 05HR is local for elementary étale neighbourhoods.** If the
pullback of `F` to an elementary étale neighbourhood `U` of `x`, over an elementary étale
neighbourhood `V` of `f x`, acquires a complete dévissage after further elementary étale
neighbourhoods, then so does `F` itself: the two pairs of neighbourhoods compose.

This is the step the source of Stacks 05HR performs twice with the words "the local nature of
the problem implies that we may replace `(X, x) → (S, s)` by `(X', x') → (S', s')`". -/
theorem exists_etaleNeighborhood_completeDevissageAt_of_etaleNeighborhood (f : X ⟶ S)
    [LocallyOfFiniteType f] (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent] (x : X)
    (U : EtaleNeighborhood X x) (V : EtaleNeighborhood S (f x)) (k : U.scheme ⟶ V.scheme)
    (hU : U.IsElementary) (hV : V.IsElementary) (hsq : U.toBase ≫ f = k ≫ V.toBase)
    (hpt : k U.point = V.point) (hk : LocallyOfFiniteType k)
    (hq₁ : ((Scheme.Modules.pullback U.toBase).obj F).IsQuasicoherent)
    (hf₁ : ((Scheme.Modules.pullback U.toBase).obj F).IsFiniteType)
    (hrec :
      letI : LocallyOfFiniteType k := hk
      letI : ((Scheme.Modules.pullback U.toBase).obj F).IsQuasicoherent := hq₁
      letI : ((Scheme.Modules.pullback U.toBase).obj F).IsFiniteType := hf₁
      ∃ (U' : EtaleNeighborhood U.scheme U.point)
        (V' : EtaleNeighborhood V.scheme (k U.point)) (k' : U'.scheme ⟶ V'.scheme),
        U'.IsElementary ∧ V'.IsElementary ∧ (U'.toBase ≫ k = k' ≫ V'.toBase) ∧
          (k' U'.point = V'.point) ∧
          ∃ (hft : LocallyOfFiniteType k')
            (hq : ((Scheme.Modules.pullback U'.toBase).obj
              ((Scheme.Modules.pullback U.toBase).obj F)).IsQuasicoherent)
            (hf : ((Scheme.Modules.pullback U'.toBase).obj
              ((Scheme.Modules.pullback U.toBase).obj F)).IsFiniteType),
            letI : LocallyOfFiniteType k' := hft
            letI := hq
            letI := hf
            Nonempty (CompleteDevissageAt k' ((Scheme.Modules.pullback U'.toBase).obj
              ((Scheme.Modules.pullback U.toBase).obj F)) U'.point)) :
    ∃ (W : EtaleNeighborhood X x) (T : EtaleNeighborhood S (f x)) (m : W.scheme ⟶ T.scheme),
      W.IsElementary ∧ T.IsElementary ∧ (W.toBase ≫ f = m ≫ T.toBase) ∧ (m W.point = T.point) ∧
        ∃ (hft : LocallyOfFiniteType m)
          (hq : ((Scheme.Modules.pullback W.toBase).obj F).IsQuasicoherent)
          (hf : ((Scheme.Modules.pullback W.toBase).obj F).IsFiniteType),
          letI : LocallyOfFiniteType m := hft
          letI : ((Scheme.Modules.pullback W.toBase).obj F).IsQuasicoherent := hq
          letI : ((Scheme.Modules.pullback W.toBase).obj F).IsFiniteType := hf
          Nonempty (CompleteDevissageAt m
            ((Scheme.Modules.pullback W.toBase).obj F) W.point) := by
  obtain ⟨U', V', k', hU', hV', hsq', hpt', hk', hq₂, hf₂, hD⟩ := hrec
  let T' : EtaleNeighborhood V.scheme V.point :=
    { scheme := V'.scheme
      point := V'.point
      toBase := V'.toBase
      map_point := V'.map_point.trans hpt }
  have hT' : T'.IsElementary :=
    (EtaleNeighborhood.isElementary_iff T').mpr ((EtaleNeighborhood.isElementary_iff V').mp hV')
  have e : ((Scheme.Modules.pullback U'.toBase).obj ((Scheme.Modules.pullback U.toBase).obj F)) ≅
      (Scheme.Modules.pullback (U'.toBase ≫ U.toBase)).obj F :=
    (Scheme.Modules.pullbackComp U'.toBase U.toBase).app F
  have hq₃ : ((Scheme.Modules.pullback (U'.toBase ≫ U.toBase)).obj F).IsQuasicoherent :=
    SheafOfModules.isQuasicoherent_of_iso e hq₂
  have hf₃ : ((Scheme.Modules.pullback (U'.toBase ≫ U.toBase)).obj F).IsFiniteType :=
    SheafOfModules.isFiniteType_of_iso e hf₂
  refine ⟨U.comp U', V.comp T', k', hU.comp hU', hV.comp hT', ?_, hpt', hk', hq₃, hf₃,
    ⟨@CompleteDevissageAt.ofModuleIso _ _ _ _ _ hk' hq₂ hf₂ hq₃ hf₃ _ hD.some e.symm⟩⟩
  show (U'.toBase ≫ U.toBase) ≫ f = k' ≫ V'.toBase ≫ V.toBase
  calc
    (U'.toBase ≫ U.toBase) ≫ f = U'.toBase ≫ k ≫ V.toBase := by
      rw [Category.assoc, hsq]
    _ = (U'.toBase ≫ k) ≫ V.toBase := by rw [Category.assoc]
    _ = (k' ≫ V'.toBase) ≫ V.toBase := by rw [hsq']
    _ = k' ≫ V'.toBase ≫ V.toBase := by rw [Category.assoc]

end AlgebraicGeometry

end
