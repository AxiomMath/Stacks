module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtale.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.GlobalGeneration.Stalks
import all StacksFrontier.AlgebraicGeometry.Cohomology.GlobalGeneration.Stalks
public import StacksFrontier.Topology.Sheaves.Modules.StalkTensorRing
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Sheaf
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat

/-!
# A finite locally free sheaf of modules is reflexive

A sheaf of modules on a scheme that is locally isomorphic to a finite free sheaf has free
stalks, so its stalks are reflexive modules over the local rings, and a coherent module on a
locally Noetherian scheme with reflexive stalks is reflexive ([Stacks, Tag 0AY3]). This file
proves that, and applies it to the direct image of the structure sheaf along a finite étale
morphism, which is finite locally free by [Stacks, Tag 02KB].

That last statement is the reflexivity hypothesis of
`isCoherent_and_isReflexive_underlyingModule_pushforwardAlgebra_of_isReflexive`, so after this
file the only remaining input to the two module-level assertions of [Stacks, Tag 0EY6] is a
coherent extension of `π_* 𝒪_V` to the whole of `X`, which is [Stacks, Tag 0G41] part (2).

## Main results

* `isReflexive_stalk_of_iso_free` — the stalks of a sheaf of modules isomorphic to a finite
  free one are reflexive.
* `isReflexive_of_isFiniteLocallyFree` — a coherent finite locally free sheaf of modules on a
  locally Noetherian scheme is reflexive.
* `isReflexive_underlyingModule_pushforwardAlgebra` — `π_* 𝒪_V` is reflexive for `π` finite
  étale onto a locally Noetherian base.
* `isCoherent_and_isReflexive_underlyingModule_pushforwardAlgebra_of_extension'` — the two
  module-level assertions of [Stacks, Tag 0EY6] with the coherent extension as the only
  hypothesis.

## Implementation notes

The identification of the stalk of `SheafOfModules.free I` with `I →₀ 𝒪_x` is the private
`AlgebraicGeometry.freeStalkLinearEquiv` of
`StacksFrontier/AlgebraicGeometry/Cohomology/GlobalGeneration/Stalks.lean`, reached by
`import all` rather than re-proved; the implementation notes of
`StacksFrontier/AlgebraicGeometry/Modules/FiniteLocallyFree.lean` record this identification as
missing, and that record is out of date. The identification is linear over the
**`RingCat`-valued** stalk of `𝒪_X ⋙ forget₂ CommRingCat RingCat`, which is the ring
`AlgebraicGeometry.SheafOfModules.stalkFunctor` uses, whereas reflexivity has to be stated over
the **`CommRingCat`-valued** stalk `𝒪_x`; the two actions agree through
`SemilinearStalk.commStalkRingEquiv` by
`AlgebraicGeometry.SheafOfModules.commStalk_smul_eq`, and that is the only nontrivial step of
`isReflexive_stalk_of_equiv_finsupp`. `ringStalk` abbreviates that `RingCat`-valued stalk; it is
an `abbrev` so that the instances stated for the unfolded spelling are still found.

The composite linear equivalence of `isReflexive_stalk_of_iso_free` is built by `have g := …`
with no expected type, and that is deliberate: elaborating the `LinearEquiv.trans` against the
expected type pushes the two spellings `Y.ringCatSheaf.obj` and
`Y.presheaf ⋙ forget₂ CommRingCat RingCat` of the same ring presheaf into the
`RingHomCompTriple` instance problem, which then fails although the two are definitionally
equal.

The coherence predicate is written `_root_.SheafOfModules.IsCoherent` throughout. That is not
cosmetic: this branch carries two distinct coherence constants with identical fields, and inside
the `Stacks.` namespace both the unqualified name and dot notation resolve to the other one, with
no error anywhere. See the implementation notes of
`StacksFrontier/AlgebraicGeometry/PushforwardCoherent.lean`.

## References

* [Stacks Project, Tag 0AY3](https://stacks.math.columbia.edu/tag/0AY3)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 02KB](https://stacks.math.columbia.edu/tag/02KB)
* [Stacks Project, Tag 0EY6](https://stacks.math.columbia.edu/tag/0EY6)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules Stacks.AlgebraicGeometry.ReflexiveEquivalence
open Stacks.AffineAlgebraEquivalence Stacks.RelativeSpec

universe u

namespace Stacks.FundamentalGroup.ExtendedEtale

/-! ### Reflexivity of the stalks of a finite free sheaf -/

/-- A module stalk carrying a finite-rank free basis over the `RingCat`-valued stalk ring is a
reflexive module over the `CommRingCat`-valued one. The two scalar actions agree through
`SemilinearStalk.commStalkRingEquiv` by
`AlgebraicGeometry.SheafOfModules.commStalk_smul_eq`. -/
private abbrev ringStalk {X : TopCat.{u}} (R : TopCat.Presheaf CommRingCat.{u} X) (x : X) :=
  ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
    (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}) x)

private theorem isReflexive_stalk_of_equiv_finsupp {X : TopCat.{u}}
    (R : TopCat.Presheaf CommRingCat.{u} X) (x : X)
    (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
    (I : Type u) [Finite I]
    (g : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf x)
      ≃ₗ[ringStalk R x] (I →₀ ringStalk R x)) :
    Module.IsReflexive (ToType (TopCat.Presheaf.stalk R x))
      (ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf x)) := by
  classical
  have hfin : Module.Finite (ToType (TopCat.Presheaf.stalk R x))
      (I →₀ ToType (TopCat.Presheaf.stalk R x)) := by
    have := Fintype.ofFinite I
    infer_instance
  let r := SemilinearStalk.commStalkRingEquiv R x
  let h : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf x) ≃+
      (I →₀ ToType (TopCat.Presheaf.stalk R x)) :=
    g.toAddEquiv.trans (Finsupp.mapRange.addEquiv r.toAddEquiv)
  have hsmul : ∀ (c : ToType (TopCat.Presheaf.stalk R x))
      (m : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf x)),
      h (c • m) = c • h m := by
    intro c m
    have hc : c • m = (r.symm c) • m := by
      have hcm := AlgebraicGeometry.SheafOfModules.commStalk_smul_eq R x M (r.symm c) m
      rwa [r.apply_symm_apply] at hcm
    rw [hc]
    change Finsupp.mapRange.addEquiv r.toAddEquiv (g.toAddEquiv ((r.symm c) • m)) = c • _
    rw [show g.toAddEquiv ((r.symm c) • m) = (r.symm c) • g m from g.map_smul _ m]
    ext i
    change r ((r.symm c) * (g m) i) = c * r ((g m) i)
    rw [map_mul, r.apply_symm_apply]
  exact Module.equiv (AddEquiv.toLinearEquiv h hsmul).symm

/-- **The stalks of a sheaf of modules isomorphic to a finite free one are reflexive.** The
stalk is `I →₀ 𝒪_y` with `I` finite, hence finite and free, hence reflexive. -/
public theorem isReflexive_stalk_of_iso_free {Y : Scheme.{u}} (y : Y) (G : Y.Modules)
    (I : Type u) [Finite I] (e : G ≅ SheafOfModules.free.{u} I) :
    Module.IsReflexive (Y.presheaf.stalk y) (G.presheaf.stalk y) := by
  refine isReflexive_stalk_of_equiv_finsupp Y.presheaf y G.val I ?_
  have g := ((AlgebraicGeometry.SheafOfModules.stalkFunctor Y.ringCatSheaf y).mapIso
    e).toLinearEquiv.trans (AlgebraicGeometry.freeStalkLinearEquiv Y.ringCatSheaf y I)
  exact g

/-! ### Reflexivity of a finite locally free sheaf -/

/-- **A coherent finite locally free sheaf of modules on a locally Noetherian scheme is
reflexive.** Each stalk is free of finite rank by `isReflexive_stalk_of_iso_free`, transported
from the trivialising open by
`Stacks.AlgebraicGeometry.ReflexiveEquivalence.isReflexive_stalk_of_isReflexive_stalk_restrict`,
and [Stacks, Tag 0AY3] (2) ⇒ (1) concludes. -/
public theorem isReflexive_of_isFiniteLocallyFree {X : Scheme.{u}} [IsLocallyNoetherian X]
    (F : X.Modules) [_root_.SheafOfModules.IsCoherent F]
    (hF : Scheme.Modules.IsFiniteLocallyFree F) : IsReflexive F := by
  have hfp : F.IsFinitePresentation := isFinitePresentation_of_isCoherent F
  have hdfp : (dualSheaf F).IsFinitePresentation := isFinitePresentation_dualSheaf F
  refine isReflexive_of_forall_isReflexive_stalk F fun x => ?_
  obtain ⟨U, hxU, I, hIfin, ⟨e⟩⟩ := hF x
  exact isReflexive_stalk_of_isReflexive_stalk_restrict U.ι F ⟨x, hxU⟩
    (isReflexive_stalk_of_iso_free (Y := U.toScheme) ⟨x, hxU⟩ (F.restrict U.ι) I e)

/-! ### The direct image of the structure sheaf along a finite étale morphism -/

/-- **`π_* 𝒪_V` is finite locally free for `π` finite étale onto a locally Noetherian base.**
This is [Stacks, Tag 02KB] condition (3): a finite flat morphism onto a locally Noetherian base
is finite locally free, and an étale morphism is flat. -/
public theorem isFiniteLocallyFree_underlyingModule_pushforwardAlgebra {U V : Scheme.{u}}
    [IsLocallyNoetherian U] (π : V ⟶ U) [IsFinite π] [Etale π] :
    _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (AlgebraSheaf.underlyingModule (pushforwardAlgebra π)) :=
  have hflat : Flat π := (Etale.iff_flat_and_formallyUnramified.mp inferInstance).1
  have h : Stacks.Morphisms.IsFiniteLocallyFree π :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_of_isLocallyNoetherian π).2
      ⟨inferInstance, hflat⟩
  h.toIsFiniteLocallyFree

/-- **`π_* 𝒪_V` is reflexive for `π` finite étale onto a locally Noetherian base.** This is the
reflexivity input to the two module-level assertions of [Stacks, Tag 0EY6]: it is finite locally
free by [Stacks, Tag 02KB], hence coherent and reflexive. -/
public theorem isReflexive_underlyingModule_pushforwardAlgebra {U V : Scheme.{u}}
    [IsLocallyNoetherian U] (π : V ⟶ U) [IsFinite π] [Etale π] :
    IsReflexive (AlgebraSheaf.underlyingModule (pushforwardAlgebra π)) :=
  have _hcoh : _root_.SheafOfModules.IsCoherent
      (AlgebraSheaf.underlyingModule (pushforwardAlgebra π)) :=
    isCoherent_underlyingModule_pushforwardAlgebra π
  have hflf : _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (AlgebraSheaf.underlyingModule (pushforwardAlgebra π)) :=
    isFiniteLocallyFree_underlyingModule_pushforwardAlgebra π
  isReflexive_of_isFiniteLocallyFree _
    ((Scheme.Modules.isFiniteLocallyFree_iff _).mpr hflf)

/-- **The two module-level assertions of [Stacks, Tag 0EY6], with the coherent extension as the
only hypothesis.** Let `j : U ⟶ X` be an open immersion into a locally Noetherian scheme whose
complement carries depth at least two and let `π : V ⟶ U` be finite étale. If `π_* 𝒪_V` is the
restriction to `j(U)` of some coherent `𝒪_X`-module, then the `𝒪_X`-module underlying the
extension algebra `𝓑 = (π ≫ j)_* 𝒪_V` is coherent and reflexive.

The remaining hypothesis is [Stacks, Tag 0G41] part (2), which no declaration on this branch
carries. -/
public theorem isCoherent_and_isReflexive_underlyingModule_pushforwardAlgebra_of_extension'
    {U X V : Scheme.{u}} [IsLocallyNoetherian X] (j : U ⟶ X) [IsOpenImmersion j]
    (π : V ⟶ U) [IsFinite π] [Etale π] (E : X.Modules)
    [_root_.SheafOfModules.IsCoherent E]
    (e : E.restrict j.opensRange.ι ≅
      (AlgebraSheaf.underlyingModule (pushforwardAlgebra (π ≫ j))).restrict j.opensRange.ι)
    (hdepth : ∀ x : X, x ∉ (j.opensRange : Set X) →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) :
    _root_.SheafOfModules.IsCoherent
        (AlgebraSheaf.underlyingModule (pushforwardAlgebra (π ≫ j))) ∧
      IsReflexive (AlgebraSheaf.underlyingModule (pushforwardAlgebra (π ≫ j))) :=
  have : IsLocallyNoetherian U := isLocallyNoetherian_of_isOpenImmersion j
  isCoherent_and_isReflexive_underlyingModule_pushforwardAlgebra_of_isReflexive j π E e
    (isReflexive_underlyingModule_pushforwardAlgebra π) hdepth

end Stacks.FundamentalGroup.ExtendedEtale

end
