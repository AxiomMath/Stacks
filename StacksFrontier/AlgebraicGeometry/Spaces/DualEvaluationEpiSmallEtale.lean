module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicExactnessLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeDualSmallEtale
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CoherentDualEvaluation
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The trace of a finite locally free module on an algebraic space is an epimorphism

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`, let `M` be an
`𝒪_F`-module on the small étale site of `F` and let `M^∨ = 𝓗om_{𝒪_F}(M, 𝒪_F)` be its dual,
`AlgebraicGeometry.Space.smallEtaleInternalHomSmall` into the monoidal unit.  This file builds the
**trace** of `M`, the morphism

`M^∨ ⊗_{𝒪_F} M ⟶ 𝒪_F`, `k ⊗ m ↦ k(m)`,

and proves that it is an **epimorphism** when `M` is finite locally free and the structure sheaf
admits a monomorphism into `M`.  This is the step of the proof of Stacks 0GUV that the dual twist
needs and that nothing in this development had: see
`StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyFiniteLocallyFreeTrace`, where it
is applied to `M = f_*𝒪_X` for a surjective finite locally free `f` and discharges
`AlgebraicGeometry.Space.DirectImageDualDescent`.

## Main definitions

* `AlgebraicGeometry.Space.dualEvaluationPairing`: the evaluation pairing on sections,
  `(k, m) ↦ k(m)`, as a bilinear map of sheaves of modules.
* `AlgebraicGeometry.Space.dualEvaluationDesc`: **the trace** `M^∨ ⊗ M ⟶ 𝒪_F`, the descent of
  that pairing along the sheafification that defines the tensor product of Stacks 01CA.

## Main results

* `AlgebraicGeometry.Space.exists_internalHomSheafSmallEval_eq_one`: over an object on which `M`
  is a coproduct of `n ≥ 1` copies of the structure sheaf there are a section `k` of `M^∨` and a
  section `m` of `M` with `k(m) = 1` — the basis vector and the matching coordinate functional.
* `AlgebraicGeometry.Space.eq_zero_of_isColimit_cofan_fin_zero`: over an object on which `M` is a
  coproduct of *no* copies of the structure sheaf, every section of `M` vanishes.
* `AlgebraicGeometry.Space.epi_dualEvaluationDesc`: **the trace of a finite locally free module
  into which the structure sheaf embeds is an epimorphism.**

## Implementation notes

**The hypothesis `m₀ : 𝒪_F ⟶ M` with `Mono m₀`, and why it is an input and not a weakening.**
The trace of a finite locally free module is *not* an epimorphism in general: over a piece of a
covering where `M` is free of rank zero its image is the zero submodule of `𝒪_F`.  What the
source of Stacks 0GUV assumes is that `f_*𝒪_X` is "finite locally free **of positive rank**", and
positive rank is exactly what excludes those pieces — except where the structure sheaf itself
vanishes, since over an empty object every module is free of rank zero.  The hypothesis used here
is that form of positive rank: a monomorphism `𝒪_F ⟶ M` forces `𝒪_F` to vanish wherever `M`
does, which is all the proof below consumes, and for `M = f_*𝒪_X` it is supplied by the
surjectivity hypothesis of Stacks 0GUV through
`AlgebraicGeometry.Space.exists_mono_unit_pushforwardStructureModule` (Stacks 03ME for `f`
together with faithful flatness on the affine charts).  So nothing beyond the hypotheses of
Stacks 0GUV is assumed, and the rank-zero case is not excluded by fiat: it is discharged, by
observing that the sections of `𝒪_F` vanish there too.

**Why a new morphism rather than
`AlgebraicGeometry.Space.smallEtaleDualEvaluation`.**  That morphism is the same evaluation,
presented as the counit of the tensor--internal-Hom adjunction of Stacks 03EO; this one is the
same pairing presented as a descent along sheafification.  The proof of epimorphy is a statement
about sections — over a covering, `1` is in the image — and only the second presentation has a
formula on sections: `Stacks.SheafOfModules.bilinearDesc_val_app_tensorSheafUnit` evaluates it on
a pure tensor, whereas the counit of an adjunction built by transporting another adjunction along
two natural isomorphisms has no such formula in this development.  The two morphisms agree, and
epimorphy of this one implies epimorphy of the counit by the universal property of the
adjunction (every `N ⊗ M ⟶ 𝒪_F` factors through the counit), but that factorisation is not
recorded here: the identification of the two monoidal structures it needs — the localized one
that `AlgebraicGeometry.Space.modulesMonoidalCategory` carries and the one
`AlgebraicGeometry.RingedSite.tensorRightIso` is stated for, equal by `rfl` — is beyond the
elaborator's default budget.  Nothing below or downstream uses the counit.

**No coevaluation is used.**  The implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyFiniteLocallyFreeDualTwist` record
the coevaluation `𝒪_F ⟶ M ⊗ M^∨` of Stacks 0FNY as the obstruction to the dual twist.  It is not
needed: the twisted map of the source's last step is written down directly from the trace in
`AlgebraicGeometry.Space.directImageDualDescent`, and a duality would only be used to *recognise*
it as a transpose.  What the last step genuinely needs is the epimorphy of the trace, which is
what is proved here.

## References

* [Stacks Project, Tag 0GUV](https://stacks.math.columbia.edu/tag/0GUV)
* [Stacks Project, Tag 0FNY](https://stacks.math.columbia.edu/tag/0FNY)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 03ME](https://stacks.math.columbia.edu/tag/03ME)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **The evaluation pairing of the dual**, `(k, m) ↦ k(m)`, as a bilinear map of sheaves of
`𝒪_F`-modules `M^∨ × M ⟶ 𝒪_F`: a section of `M^∨ = 𝓗om_{𝒪_F}(M, 𝒪_F)` over an object `V` is a
morphism `M|_V ⟶ 𝒪_F|_V` on the slice site, and it is evaluated at a section of `M` over `V` by
`AlgebraicGeometry.RingedSite.internalHomSheafSmallEval`, whose additivity, bilinearity and
compatibility with restriction are the four fields of a bilinear map. -/
@[sga "5 IIIB 5.0" "special case"]
def dualEvaluationPairing (M : Modules.{u, u} B S hS F hF) :
    Stacks.BilinearMap
      (smallEtaleInternalHomSmall B S hS F hF M (𝟙_ (Modules.{u, u} B S hS F hF))).val
      M.val (𝟙_ (Modules.{u, u} B S hS F hF)).val where
  app V := AddMonoidHom.mk'
    (fun k => AddMonoidHom.mk'
      (fun a => RingedSite.internalHomSheafSmallEval (smallEtaleRingedSite B S hS F hF) M
        (𝟙_ (Modules.{u, u} B S hS F hF)) V k a)
      (fun a a' => RingedSite.internalHomSheafSmallEval_add_right
        (smallEtaleRingedSite B S hS F hF) M _ V k a a'))
    (fun k k' => AddMonoidHom.ext fun a =>
      RingedSite.internalHomSheafSmallEval_add_left
        (smallEtaleRingedSite B S hS F hF) M _ V k k' a)
  map_smul_left V r k a := RingedSite.internalHomSheafSmallEval_smul_left
    (smallEtaleRingedSite B S hS F hF) M _ V r k a
  map_smul_right V r k a := RingedSite.internalHomSheafSmallEval_smul_right
    (smallEtaleRingedSite B S hS F hF) M _ V k r a
  naturality {_V _W} g k a := (RingedSite.internalHomSheafSmallEval_map
    (smallEtaleRingedSite B S hS F hF) M _ g k a).symm

/-- **The trace `M^∨ ⊗_{𝒪_F} M ⟶ 𝒪_F` of an `𝒪_F`-module on an algebraic space**, the descent of
the evaluation pairing `AlgebraicGeometry.Space.dualEvaluationPairing` along the sheafification
that defines the tensor product of Stacks 01CA.  On a pure tensor it is `k ⊗ m ↦ k(m)`, which is
`AlgebraicGeometry.Space.exists_apply_dualEvaluationDesc_eq`. -/
def dualEvaluationDesc (M : Modules.{u, u} B S hS F hF) :
    smallEtaleInternalHomSmall B S hS F hF M (𝟙_ (Modules.{u, u} B S hS F hF)) ⊗ M ⟶
      𝟙_ (Modules.{u, u} B S hS F hF) :=
  Stacks.SheafOfModules.bilinearDesc (structureSheaf B S hS F hF)
    (structureRingPresheaf_isSheaf B S hS F hF) (dualEvaluationPairing B S hS F hF M)

/-- **The trace on a pure tensor.**  For sections `k` of `M^∨` and `a` of `M` over `V` there is a
section of `M^∨ ⊗ M` over `V` — the image of `k ⊗ a` under the comparison with the tensor product
sheaf — which the trace sends to `k(a)`.

Stated existentially because the section itself is the composite of the sheafification unit with
the inverse of `Stacks.SheafOfModules.tensorObjIso`, which is never needed by name. -/
theorem exists_apply_dualEvaluationDesc_eq (M : Modules.{u, u} B S hS F hF)
    (V : (SmallEtale B S hS F)ᵒᵖ)
    (k : (smallEtaleInternalHomSmall B S hS F hF M (𝟙_ (Modules.{u, u} B S hS F hF))).val.obj V)
    (a : M.val.obj V) :
    ∃ t, (dualEvaluationDesc B S hS F hF M).val.app V t =
      RingedSite.internalHomSheafSmallEval (smallEtaleRingedSite B S hS F hF) M
        (𝟙_ (Modules.{u, u} B S hS F hF)) V k a :=
  ⟨_, Stacks.SheafOfModules.bilinearDesc_val_app_tensorSheafUnit _ _ _ _ k a⟩

/-- A morphism `κ : M|_W ⟶ 𝒪_F|_W` of modules on the slice site over `W` is a section of `M^∨`
over `W`, on the nose, and evaluating that section at a section of `M` over `W` applies `κ` at the
final object of the slice. -/
theorem internalHomSheafSmallEval_section_symm (M : Modules.{u, u} B S hS F hF)
    (W : (smallEtaleRingedSite B S hS F hF).C)
    (κ : M.over W ⟶ SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).over W))
    (a : M.val.obj (op W)) :
    RingedSite.internalHomSheafSmallEval (smallEtaleRingedSite B S hS F hF) M
        (𝟙_ (Modules.{u, u} B S hS F hF)) (op W)
        ((RingedSite.internalHomSheafSmallSection (smallEtaleRingedSite B S hS F hF) M
          (𝟙_ (Modules.{u, u} B S hS F hF)) (op W)).symm κ.val) a =
      κ.val.app (op (Over.mk (𝟙 W))) a :=
  congrArg (fun φ => PresheafOfModules.Hom.app φ (op (Over.mk (𝟙 W))) a)
    ((RingedSite.internalHomSheafSmallSection (smallEtaleRingedSite B S hS F hF) M
      (𝟙_ (Modules.{u, u} B S hS F hF)) (op W)).apply_symm_apply κ.val)

/-- **A local trivialisation of positive rank pairs to `1`.**  If over `W` the module `M` is a
coproduct of `n` copies of the structure sheaf and `n` is nonzero, then there are a section `k` of
`M^∨` and a section `a` of `M` over `W` with `k(a) = 1`.

Take `a` to be the image of `1` under one of the `n` inclusions `𝒪_F|_W ⟶ M|_W` and `k` to be the
matching coordinate functional, the morphism out of the coproduct which is the identity on that
summand and zero on the others; the two compose to the identity of `𝒪_F|_W`.  This is where the
rank is used, and it is the only place: a coproduct of no copies has no inclusion to start
from. -/
theorem exists_internalHomSheafSmallEval_eq_one (M : Modules.{u, u} B S hS F hF)
    (W : (smallEtaleRingedSite B S hS F hF).C) {n : ℕ} (j : Fin n)
    (ι : ∀ _ : Fin n, SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).over W) ⟶
        M.over W)
    (hc : IsColimit (Cofan.mk (M.over W) ι)) :
    ∃ (k : (smallEtaleInternalHomSmall B S hS F hF M
        (𝟙_ (Modules.{u, u} B S hS F hF))).val.obj (op W)) (a : M.val.obj (op W)),
      RingedSite.internalHomSheafSmallEval (smallEtaleRingedSite B S hS F hF) M
        (𝟙_ (Modules.{u, u} B S hS F hF)) (op W) k a =
      (1 : (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O).obj.obj (op W)) := by
  classical
  obtain ⟨κ, hfac⟩ : ∃ κ : M.over W ⟶ SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).over W),
      ι j ≫ κ = 𝟙 _ :=
    ⟨Cofan.IsColimit.desc hc (fun t => if t = j then 𝟙 _ else 0), by
      simpa using Cofan.IsColimit.fac hc (fun t => if t = j then 𝟙 _ else 0) j⟩
  refine ⟨(RingedSite.internalHomSheafSmallSection (smallEtaleRingedSite B S hS F hF) M
      (𝟙_ (Modules.{u, u} B S hS F hF)) (op W)).symm κ.val,
    (ι j).val.app (op (Over.mk (𝟙 W)))
      (1 : (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O).obj.obj (op W)),
    (internalHomSheafSmallEval_section_symm B S hS F hF M W κ _).trans ?_⟩
  have h2 := congrArg (fun φ : SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).over W) ⟶
      SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).over W) =>
    φ.val.app (op (Over.mk (𝟙 W)))
      (1 : (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O).obj.obj (op W))) hfac
  exact h2

/-- **A local trivialisation of rank zero makes the sections vanish.**  If over `W` the module `M`
is a coproduct of no copies of the structure sheaf, then `M|_W` is a zero object and in particular
every section of `M` over `W` is zero. -/
theorem eq_zero_of_isColimit_cofan_fin_zero (M : Modules.{u, u} B S hS F hF)
    (W : (smallEtaleRingedSite B S hS F hF).C)
    (ι : ∀ _ : Fin 0, SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).over W) ⟶
        M.over W)
    (hc : IsColimit (Cofan.mk (M.over W) ι)) :
    ∀ x : M.val.obj (op W), x = 0 := fun x =>
  congrArg (fun φ : M.over W ⟶ M.over W => φ.val.app (op (Over.mk (𝟙 W))) x)
    ((IsZero.iff_id_eq_zero _).1
      ((IsZero.iff_id_eq_zero _).2 (hc.hom_ext (fun j => j.as.elim0))))

/-- **The trace of a finite locally free module into which the structure sheaf embeds is an
epimorphism.**

A morphism of `𝒪_F`-modules is an epimorphism as soon as every section of its target is locally in
its image (`AlgebraicGeometry.Space.modules_epi_iff_exists_covering`), so take a section `s` of
`𝒪_F` over an object `U` and the covering of `U` on whose members `M` is finite free, Stacks
03DL(2).  On a member where the rank is positive,
`AlgebraicGeometry.Space.exists_internalHomSheafSmallEval_eq_one` gives sections `k` of `M^∨` and
`a` of `M` with `k(a) = 1`, and the pure tensor `s·k ⊗ a` is sent to `s`.  On a member where the
rank is zero the sections of `M` vanish, so the monomorphism `m₀` forces the sections of `𝒪_F` to
vanish there as well and `s` restricts to `0`, which is the image of `0`.

**The hypothesis `m₀`** is the positive rank of the source of Stacks 0GUV, in the form this
development has it; the implementation notes of this file say why it is an input of that proof and
not a weakening of it. -/
theorem epi_dualEvaluationDesc (M : Modules.{u, u} B S hS F hF)
    (hM : SheafOfModules.IsFiniteLocallyFreeOnSite M)
    (m₀ : 𝟙_ (Modules.{u, u} B S hS F hF) ⟶ M) (hm₀ : Mono m₀) :
    Epi (dualEvaluationDesc B S hS F hF M) := by
  classical
  refine (modules_epi_iff_exists_covering B S hS F hF _).mpr fun U s => ?_
  obtain ⟨I, V, p, hp, hV⟩ := hM U
  refine ⟨Sieve.ofArrows V p, hp, ?_⟩
  rintro W g ⟨Z, h, q, ⟨i⟩, hfac⟩
  obtain ⟨n, ι, ⟨hc⟩⟩ := Stacks.SheafOfModules.exists_isColimitCofan_over_of_le M h
    ((SheafOfModules.isFiniteFree_iff_exists_isColimit _ _).1 (hV i))
  obtain ⟨r, hr⟩ : ∃ r : (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS F hF).O).obj.obj (op W),
      r = (𝟙_ (Modules.{u, u} B S hS F hF)).val.map g.op s :=
    ⟨_, rfl⟩
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hs0 : r = 0 :=
      have := hm₀
      Stacks.SheafOfModules.injective_val_app_of_mono m₀ (op W)
        ((eq_zero_of_isColimit_cofan_fin_zero B S hS F hF M W ι hc _).trans (map_zero _).symm)
    exact ⟨0, (map_zero _).trans (hs0.symm.trans hr)⟩
  · obtain ⟨k, a, hka⟩ :=
      exists_internalHomSheafSmallEval_eq_one B S hS F hF M W ⟨0, hn⟩ ι hc
    obtain ⟨t, ht⟩ := exists_apply_dualEvaluationDesc_eq B S hS F hF M (op W) (r • k) a
    refine ⟨t, ht.trans ?_⟩
    refine ((RingedSite.internalHomSheafSmallEval_smul_left
      (smallEtaleRingedSite B S hS F hF) M _ (op W) r k a).trans
        (congrArg (fun z => r • z) hka)).trans ?_
    exact (mul_one r).trans hr

end AlgebraicGeometry.Space

end
