module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.OverFiniteFree
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.RingedSite
public import StacksFrontier.AlgebraicGeometry.Topologies.GlobalPresentationComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineColimitPresentations
public import StacksFrontier.CategoryTheory.Sites.Modules.FiniteLocallyFreeOfRank

/-!
# The module `ℰ ⊕ 𝒪_X` of the projective completion of a vector bundle

Let `X` be an algebraic space and `ℰ` a finite locally free `𝒪_X`-module of rank `r` on its small
étale site. The projective completion of the vector bundle of `ℰ` is the projective bundle of
`ℰ ⊕ 𝒪_X` (Stacks 0ERW, proof). This file shows that `ℰ ⊕ 𝒪_X` is again finite locally free, of
rank `r + 1`, and quasi-coherent, in the forms the projective bundle of a module asks for.

The argument is local and categorical. On a member `V` of a covering on which `ℰ|_V` is a
coproduct of `r` copies of `𝒪_V`, the restriction `(ℰ ⊕ 𝒪_X)|_V = ℰ|_V ⊕ 𝒪_V` is a coproduct of
`r + 1` copies, restriction being additive. A coproduct of copies of the structure sheaf has a
global presentation, so a finite locally free module of constant rank is quasi-coherent.

## Main definitions

* `AlgebraicGeometry.Space.addUnit`: the module `ℰ ⊕ 𝒪`, and
  `AlgebraicGeometry.Space.addUnitInr` the inclusion of its summand `𝒪` and
  `AlgebraicGeometry.Space.addUnitSnd` the projection to it.

## Main results

* `Stacks.SheafOfModules.isColimitCofanBiprodUnit`: a coproduct of `n` copies of the structure
  sheaf, plus one more copy, is a coproduct of `n + 1` copies.
* `AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRank.biprod_unit`: if `ℰ` is finite locally
  free of rank `r`, then `ℰ ⊕ 𝒪` is finite locally free of rank `r + 1`.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank`: a finite locally
  free module of constant rank on the small étale site of an algebraic space is quasi-coherent.
* `AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_addUnit`,
  `AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_addUnit`,
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_addUnit`: the three properties of `ℰ ⊕ 𝒪`.

## References

* [Stacks Project, Tag 0ERW](https://stacks.math.columbia.edu/tag/0ERW)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

attribute [local instance] HasBinaryBiproducts.of_hasBinaryProducts

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- The injections of the coproduct `M ⊕ 𝒪` of `n + 1` copies of the structure sheaf: the first
`n` through the injections `ι` of `M` followed by the first inclusion, the last the second
inclusion. -/
def cofanBiprodUnitInj (M : SheafOfModules.{w} R) {n : ℕ}
    (ι : Fin n → (SheafOfModules.unit R ⟶ M)) :
    Fin (n + 1) → (SheafOfModules.unit R ⟶ M ⊞ SheafOfModules.unit R) :=
  Fin.lastCases biprod.inr fun i => ι i ≫ biprod.inl

/-- The injection of index `i.castSucc` is the `i`-th injection of `M` followed by the first
inclusion. -/
@[simp]
theorem cofanBiprodUnitInj_castSucc (M : SheafOfModules.{w} R) {n : ℕ}
    (ι : Fin n → (SheafOfModules.unit R ⟶ M)) (i : Fin n) :
    cofanBiprodUnitInj M ι i.castSucc = ι i ≫ biprod.inl := by
  simp [cofanBiprodUnitInj]

/-- The last injection is the second inclusion. -/
@[simp]
theorem cofanBiprodUnitInj_last (M : SheafOfModules.{w} R) {n : ℕ}
    (ι : Fin n → (SheafOfModules.unit R ⟶ M)) :
    cofanBiprodUnitInj M ι (Fin.last n) = biprod.inr := by
  simp [cofanBiprodUnitInj]

/-- **A coproduct of `n` copies of the structure sheaf, plus one copy, is a coproduct of `n + 1`
copies.** If the injections `ι` exhibit `M` as a coproduct of `n` copies of `𝒪`, then `M ⊕ 𝒪`
is a coproduct of `n + 1` copies, with the injections
`Stacks.SheafOfModules.cofanBiprodUnitInj`. -/
def isColimitCofanBiprodUnit (M : SheafOfModules.{w} R) {n : ℕ}
    (ι : Fin n → (SheafOfModules.unit R ⟶ M)) (hc : IsColimit (Cofan.mk M ι)) :
    IsColimit (Cofan.mk (M ⊞ SheafOfModules.unit R) (cofanBiprodUnitInj M ι)) :=
  Cofan.IsColimit.mk _
    (fun s => biprod.desc (hc.desc (Cofan.mk s.pt fun i => s.inj i.castSucc))
      (s.inj (Fin.last n)))
    (fun s j => by
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simp
      · simp only [cofan_mk_inj, cofanBiprodUnitInj_castSucc, Category.assoc, biprod.inl_desc]
        exact hc.fac (Cofan.mk s.pt fun i => s.inj i.castSucc) ⟨i⟩)
    (fun s m hm => by
      refine biprod.hom_ext' _ _ ?_ ?_
      · rw [biprod.inl_desc]
        refine hc.hom_ext fun ⟨i⟩ => ?_
        rw [hc.fac (Cofan.mk s.pt fun i => s.inj i.castSucc) ⟨i⟩]
        have := hm i.castSucc
        simp only [cofan_mk_inj, cofanBiprodUnitInj_castSucc, Category.assoc] at this
        simpa using this
      · rw [biprod.inr_desc]
        simpa using hm (Fin.last n))

/-- **A finite coproduct of copies of the structure sheaf has a global presentation.** Each copy
has one (`SheafOfModules.hasGlobalPresentation_unit`), and coproducts of globally presented
modules are globally presented (`SheafOfModules.HasGlobalPresentation.of_isColimit_cofan`). -/
theorem hasGlobalPresentation_of_isColimit_cofan_unit
    [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    {M : SheafOfModules.{w} R} {n : ℕ} (ι : Fin n → (SheafOfModules.unit R ⟶ M))
    (hc : IsColimit (Cofan.mk M ι)) : M.HasGlobalPresentation :=
  SheafOfModules.HasGlobalPresentation.of_isColimit_cofan
    (isColimitCofanULift hc : IsColimit (Cofan.mk M fun j : ULift.{w} (Fin n) => ι j.down))
    fun _ => SheafOfModules.hasGlobalPresentation_unit R

end Stacks.SheafOfModules

namespace AlgebraicGeometry.RingedSite

universe u₁ v₁ w₁

/-- **`ℰ ⊕ 𝒪` is finite locally free of rank `r + 1` when `ℰ` is finite locally free of rank
`r`.** On a member `V` of a covering on which `ℰ|_V` is a coproduct of `r` copies of `𝒪_V`, the
restriction of `ℰ ⊕ 𝒪` is `ℰ|_V ⊕ 𝒪_V`, restriction being additive, and that is a coproduct of
`r + 1` copies. -/
theorem IsFiniteLocallyFreeOfRank.biprod_unit {X : RingedSite.{u₁, v₁, w₁}}
    {F : SheafOfModules.{w₁} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} {r : ℕ}
    (h : IsFiniteLocallyFreeOfRank X F r) :
    IsFiniteLocallyFreeOfRank X
      (F ⊞ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (r + 1) := by
  intro U
  obtain ⟨I, V, f, hf, hfree⟩ := h U
  refine ⟨I, V, f, hf, fun i => ?_⟩
  obtain ⟨ι, ⟨hc⟩⟩ := hfree i
  let R := Stacks.SheafOfModules.Tensor.ringSheaf X.O
  let G := SheafOfModules.overFunctor.{w₁} R (V i)
  have : PreservesBinaryBiproducts G := preservesBinaryBiproducts_of_preservesBiproducts G
  let e : (F ⊞ SheafOfModules.unit R).over (V i) ≅
      F.over (V i) ⊞ SheafOfModules.unit (R.over (V i)) :=
    G.mapBiprod F (SheafOfModules.unit R)
  refine ⟨fun j => Stacks.SheafOfModules.cofanBiprodUnitInj (F.over (V i)) ι j ≫ e.inv,
    ⟨IsColimit.ofIsoColimit (Stacks.SheafOfModules.isColimitCofanBiprodUnit _ ι hc)
      (Cofan.ext e.symm fun _ => rfl)⟩⟩

end AlgebraicGeometry.RingedSite

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)

/-- **A finite locally free module of constant rank on an algebraic space is quasi-coherent.**
On a member of a covering on which it is a coproduct of copies of the structure sheaf it has a
global presentation. -/
theorem isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank {E : Modules.{u, u} B S hS F hF}
    {r : ℕ} (h : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS F hF) E r) :
    E.IsQuasicoherentOnSite where
  locally_hasGlobalPresentation U := by
    obtain ⟨I, V, f, hf, hfree⟩ := h U
    exact ⟨I, V, f, hf, fun i => (hfree i).elim fun ι ⟨hc⟩ =>
      Stacks.SheafOfModules.hasGlobalPresentation_of_isColimit_cofan_unit ι hc⟩

/-- The module `ℰ ⊕ 𝒪` on an algebraic space, whose projective bundle is the projective completion
of the vector bundle of `ℰ`. -/
abbrev addUnit (E : Modules.{u, u} B S hS F hF) : Modules.{u, u} B S hS F hF :=
  E ⊞ SheafOfModules.unit _

/-- The inclusion `𝒪 ⟶ ℰ ⊕ 𝒪` of the second summand. -/
def addUnitInr (E : Modules.{u, u} B S hS F hF) : SheafOfModules.unit _ ⟶ addUnit hF E :=
  biprod.inr

/-- The projection `ℰ ⊕ 𝒪 ⟶ 𝒪` to the second summand. -/
def addUnitSnd (E : Modules.{u, u} B S hS F hF) : addUnit hF E ⟶ SheafOfModules.unit _ :=
  biprod.snd

/-- The projection to the summand `𝒪` is a retraction of its inclusion. -/
theorem addUnitInr_addUnitSnd (E : Modules.{u, u} B S hS F hF) :
    addUnitInr hF E ≫ addUnitSnd hF E = 𝟙 _ :=
  biprod.inr_snd

variable {hF} {E : Modules.{u, u} B S hS F hF} {r : ℕ}

/-- `ℰ ⊕ 𝒪` is finite locally free of rank `r + 1` when `ℰ` is finite locally free of rank `r`. -/
theorem isFiniteLocallyFreeOfRank_addUnit
    (h : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS F hF) E r) :
    RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS F hF) (addUnit hF E)
      (r + 1) :=
  h.biprod_unit

/-- `ℰ ⊕ 𝒪` is finite locally free when `ℰ` is finite locally free of constant rank. -/
theorem isFiniteLocallyFreeOnSite_addUnit
    (h : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS F hF) E r) :
    SheafOfModules.IsFiniteLocallyFreeOnSite (addUnit hF E) :=
  (isFiniteLocallyFreeOfRank_addUnit h).isFiniteLocallyFreeOnSite

/-- `ℰ ⊕ 𝒪` is quasi-coherent when `ℰ` is finite locally free of constant rank. -/
theorem isQuasicoherentOnSite_addUnit
    (h : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS F hF) E r) :
    (addUnit hF E).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank hF (isFiniteLocallyFreeOfRank_addUnit h)

end AlgebraicGeometry.Space

end
