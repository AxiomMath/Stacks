module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalenceStandard
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentFrom.Affine
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentStandardModel
public import StacksFrontier.Homology.Perfect.NilpotentLifting
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Pseudo-coherence along an affine finite-order thickening

Let `f : R ⟶ S` be a surjection of commutative rings whose kernel is nilpotent, so that
`Spec S ⟶ Spec R` is a finite-order thickening, and let `A` be an object of `D(𝒪_{Spec R})` whose
derived pullback to `Spec S` is pseudo-coherent. The affine case of [Stacks, Tag 0DJX] asserts
that `A` is itself pseudo-coherent.

This file proves that **granted that the cohomology sheaves of `A` are quasi-coherent**, and
isolates that hypothesis: everything else in the affine case is here and complete. The reduction is
the source's. Quasi-coherence of the cohomology sheaves presents `A` as `M̃^•` for an object `M`
of `D(R)` ([Stacks, Tag 06Z0]); the affine comparison square of [Stacks, Tag 08DW] turns the
derived pullback into derived extension of scalars, so the hypothesis becomes pseudo-coherence of
`S ⊗ᴸ_R M` over `S`; the nilpotent-lifting criterion of [Stacks, Tag 0H76] descends it to `M`;
and [Stacks, Tag 08E7] carries it back to `A`.

## Main results

* `Stacks.Thickenings.isPseudoCoherent_mapDerivedCategory_tilde_iff` — [Stacks, Tag 08E7] for an
  *object* of `D(R)` rather than a complex: `M̃^•` is pseudo-coherent on `Spec R` exactly when `M`
  is pseudo-coherent.
* `Stacks.Thickenings.isPseudoCoherent_of_derivedPullback_specMap_of_isQuasicoherent` — **the
  affine case of [Stacks, Tag 0DJX] for an object with quasi-coherent cohomology sheaves.**
* `Stacks.Thickenings.exists_restrictScalars_iso_of_smul_eq_bot` and
  `Stacks.Thickenings.prop_of_isNilpotent_of_smul_eq_bot` — the two algebraic inputs of the
  dévissage that the missing quasi-coherence half runs on; see the implementation notes.

## The hypothesis that is not discharged, and what it costs

`isPseudoCoherent_of_derivedPullback_specMap_of_isQuasicoherent` carries
```
∀ n : ℤ, ((DerivedCategory.homologyFunctor (Spec R).Modules n).obj A).IsQuasicoherent
```
and **nothing else** beyond the library. That is `A ∈ D_QCoh(𝒪_{Spec R})` written out:
`CategoryTheory.DerivedCategoryB.derivedCategoryB` is by definition the conjunction over all
degrees of its argument property on the cohomology, so the hypothesis is literally
`AlgebraicGeometry.StandardModel.derivedQuasicoherent R A`, that is
`DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf) A`, and
a consumer holding either spelling can pass it. The hypothesis cannot be dropped by a
different arrangement of the affine argument: pseudo-coherence implies quasi-coherence of the
cohomology sheaves ([Stacks, Tag 08E5]), so it is a consequence of the conclusion, and every
passage from `D(𝒪_{Spec R})` to `D(R)` — which is what makes the module-level criterion of
[Stacks, Tag 0H76] applicable at all — goes through [Stacks, Tag 06Z0], whose essential image is
exactly the complexes with quasi-coherent cohomology.

The source proves it by dévissage on the kernel ideal `I = ker f`. Writing `i` for `Spec f`, the
short exact sequence `0 → I·N → N → N/I·N → 0` of `R`-modules filters `R` into finitely many
steps annihilated by `I` (`prop_of_isNilpotent_of_smul_eq_bot`), each step is a module restricted
from `S` (`exists_restrictScalars_iso_of_smul_eq_bot`), and tensoring the resulting distinguished
triangles with `A` reduces the claim to: `i_*(Ñ) ⊗ᴸ_{𝒪_{Spec R}} A` has quasi-coherent cohomology
for an `S`-module `N`. The projection formula of [Stacks, Tag 0B55] rewrites that as
`i_*(Ñ ⊗ᴸ_{𝒪_{Spec S}} Li^*A)`, where [Stacks, Tag 08E5] and [Stacks, Tag 08DX] put the argument
in `D_QCoh(𝒪_{Spec S})` and [Stacks, Tag 08D5] brings it back; quasi-coherence is a weak Serre
class, so it passes to the middle term of each triangle.

*Which of those inputs is where.* [Stacks, Tag 08E5] is
`AlgebraicGeometry.isQuasicoherentDerived_of_isPseudoCoherent`, which takes a free
`HasDerivedCategory` binder, and [Stacks, Tag 08D5] is
`AlgebraicGeometry.isQuasicoherent_derivedPushforward`, at the standard model; that
quasi-coherence is a weak Serre class is `AlgebraicGeometry.isQuasicoherent_isWeakSerre`, which
mentions no derived category, and the two-out-of-three step
`CategoryTheory.DerivedCategoryB.derivedCategoryB_mem_obj₂_of_distinguished` takes a free model
binder. Only [Stacks, Tag 08DX], `Stacks.Duality.isQuasicoherent_homology_derivedTensor`, is
pinned to the locally small model. Its file explains that as forced by the essential surjectivity
of derived sheafification being available there and nowhere else; that is no longer so — it is
`AlgebraicGeometry.StandardModel.exists_iso_mapDerivedCategory` at the standard model — so Tag
08DX can be re-proved at the standard model by its own argument, and no transport of the
pseudo-coherence predicate between models arises anywhere in the affine case. None is performed
below.

What is then missing in this repository is the projection formula, and only it. The
*complex-level*
statement for a closed embedding is available —
`Stacks.Cohomology.ClosedEmbeddingProjectionFormulaComplexes.complexProjectionFormulaIso`,
`Tot(i_*A^• ⊗ B^•) ≅ i_* Tot(A^• ⊗ i^*B^•)` for arbitrary complexes — but its identification with
the derived morphism of [Stacks, Tag 0B53] is not, and that identification is what the file
declaring `complexProjectionFormulaIso`, under
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/`,
records as the remaining content of [Stacks, Tag 0B55]. Note that the *canonical* morphism is not
needed for the dévissage: any isomorphism of the two objects does, since only membership in
`D_QCoh` is being transported.

## Implementation notes

Everything is at `CategoryTheory.HasDerivedCategory.standard`, the model of the pseudo-coherence
development, and the local instance carries a high priority because the import closure also
supplies the *global* locally small instances of
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`, which a default-priority local attribute
would not beat.

No transport between the two models is needed, and none is performed: all four inputs are
available at the standard model. [Stacks, Tag 06Z0] is
`AlgebraicGeometry.StandardModel.exists_iso_mapDerivedCategory`, [Stacks, Tag 08DW] part (2) is
`AlgebraicGeometry.StandardModel.affinePullbackComparison`, and [Stacks, Tag 08E7] and
[Stacks, Tag 0H76] are proved in files whose closures do not contain the locally small instances
at all. The categories `Stacks.StrictlyPerfect.OXMod (Spec R).toRingedSpace`,
`AlgebraicGeometry.SheafOfModules (Spec R).ringCatSheaf` and `(Spec R).Modules` are the same type
with the same instances up to `rfl`, but `AlgebraicGeometry.Scheme.Modules` is not reducible, so
the crossings between the three spellings are made by type ascription in term position — the
`have`s with explicit types below — and never by instance search.

The two algebraic lemmas are stated for `ModuleCat` and an arbitrary predicate because that is
the shape the dévissage needs: the predicate it is applied to is "the derived tensor product of
`Ñ` with `A` has quasi-coherent cohomology", which is not a condition on `N` expressible in
module theory, and the induction is on the power of `I` killing the module, not on the module.

## References

* [Stacks Project, Tag 0DJX](https://stacks.math.columbia.edu/tag/0DJX)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
* [Stacks Project, Tag 08E7](https://stacks.math.columbia.edu/tag/08E7)
* [Stacks Project, Tag 0H76](https://stacks.math.columbia.edu/tag/0H76)
* [Stacks Project, Tag 0B55](https://stacks.math.columbia.edu/tag/0B55)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits StrictlyPerfect
open CochainComplex.DerivedExtensionScalars
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.Thickenings

/-! ### Pseudo-coherence of the sheaf attached to an object of `D(R)` -/

/-- **[Stacks, Tag 08E7] for an object of `D(R)`.** The complex of quasi-coherent sheaves on
`Spec R` attached to an object `N` of `D(R)` is pseudo-coherent exactly when `N` is
pseudo-coherent.

`AlgebraicGeometry.RingedSpace.isPseudoCoherent_tilde_iff` is the same statement for a *complex*
of `R`-modules, applied here to a complex representing `N`:
`CategoryTheory.Functor.mapDerivedCategoryFactors` identifies the sheaf attached to that complex
with the one attached to `N`, and both notions of pseudo-coherence depend only on the isomorphism
class of their argument. -/
@[sga "6 I 2.13" "special case"]
public theorem isPseudoCoherent_mapDerivedCategory_tilde_iff (R : CommRingCat.{u})
    (N : DerivedCategory (ModuleCat.{u} R)) :
    AlgebraicGeometry.RingedSpace.IsPseudoCoherent (X := (Spec R).toRingedSpace)
        ((tilde.functor R).mapDerivedCategory.obj N) ↔
      StacksDraft.PseudoCoherence.IsPseudoCoherent N := by
  let E := DerivedCategory.Q.objPreimage N
  let eN : DerivedCategory.Q.obj E ≅ N := DerivedCategory.Q.objObjPreimageIso N
  let eT : (tilde.functor R).mapDerivedCategory.obj N ≅
      DerivedCategory.Q.obj
        (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj E) :=
    (tilde.functor R).mapDerivedCategory.mapIso eN.symm ≪≫
      (tilde.functor R).mapDerivedCategoryFactors.app E
  have hpc : AlgebraicGeometry.RingedSpace.IsPseudoCoherent (X := (Spec R).toRingedSpace)
        (DerivedCategory.Q.obj
          (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj E)) ↔
      StacksDraft.PseudoCoherence.IsPseudoCoherent (DerivedCategory.Q.obj E) :=
    AlgebraicGeometry.RingedSpace.isPseudoCoherent_tilde_iff (A := (R : Type u)) E
  exact ⟨fun h => (hpc.mp (h.of_iso eT)).ofIso eN,
    fun h => (hpc.mpr (h.ofIso eN.symm)).of_iso eT.symm⟩

/-! ### The affine case of Stacks 0DJX, for an object with quasi-coherent cohomology -/

/-- **The affine case of [Stacks, Tag 0DJX], granted quasi-coherence of the cohomology sheaves.**
Let `f : R ⟶ S` be a surjection of commutative rings with nilpotent kernel and let `A` be an
object of `D(𝒪_{Spec R})` whose cohomology sheaves are all quasi-coherent and whose derived
pullback along `Spec f` is pseudo-coherent. Then `A` is pseudo-coherent.

The hypothesis of quasi-coherence is the one thing this statement assumes beyond the existing
library; it is the half of the source's argument that rests on the projection formula of
[Stacks, Tag 0B55], and the module docstring says exactly what of that formula is missing. It is
not a weakening of the conclusion in substance — [Stacks, Tag 08E5] derives it from
pseudo-coherence — but it is a genuine hypothesis, and this theorem therefore carries no `stacks`
attribute.

The argument: quasi-coherence presents `A` as `M̃^•` ([Stacks, Tag 06Z0], at the standard model
`AlgebraicGeometry.StandardModel.exists_iso_mapDerivedCategory`); the affine comparison square
`AlgebraicGeometry.StandardModel.affinePullbackComparison` ([Stacks, Tag 08DW] part (2)) rewrites
`L(Spec f)^*(M̃^•)` as the sheaf attached to `S ⊗ᴸ_R M`; `Stacks.Tag 08E7`, in the form
`isPseudoCoherent_mapDerivedCategory_tilde_iff`, makes the hypothesis pseudo-coherence of
`S ⊗ᴸ_R M` in `D(S)`; the kernel being nilpotent,
`StacksDraft.Perfect.isPseudoCoherent_derivedExtensionScalars_iff` ([Stacks, Tag 0H76]) descends
that to `M`; and Tag 08E7 again, read backwards, returns pseudo-coherence of `M̃^• ≅ A`. -/
public theorem isPseudoCoherent_of_derivedPullback_specMap_of_isQuasicoherent
    {R S : CommRingCat.{u}} (f : R ⟶ S)
    (hf : Function.Surjective f.hom) (hnil : IsNilpotent (RingHom.ker f.hom))
    (A : DerivedCategory (StrictlyPerfect.OXMod.{u, u} (Spec R).toRingedSpace))
    (hqc : ∀ n : ℤ,
      ((DerivedCategory.homologyFunctor (Spec R).Modules n).obj A).IsQuasicoherent)
    (hA : AlgebraicGeometry.RingedSpace.IsPseudoCoherent (X := (Spec S).toRingedSpace)
      ((derivedPullback (Spec.map f).toLRSHom.toShHom).obj A)) :
    AlgebraicGeometry.RingedSpace.IsPseudoCoherent (X := (Spec R).toRingedSpace) A := by
  obtain ⟨M, ⟨e⟩⟩ := AlgebraicGeometry.StandardModel.exists_iso_mapDerivedCategory R A hqc
  have epull : (derivedPullback (Spec.map f).toLRSHom.toShHom).obj A ≅
      (tilde.functor S).mapDerivedCategory.obj
        ((totalDerivedExtensionScalars.{u, u, u} f.hom).functor.obj M) :=
    (AlgebraicGeometry.StandardModel.specDerivedPullback f).mapIso e.symm ≪≫
      (AlgebraicGeometry.StandardModel.affinePullbackComparison R S f).app M
  have hS : StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((totalDerivedExtensionScalars.{u, u, u} f.hom).functor.obj M) :=
    (isPseudoCoherent_mapDerivedCategory_tilde_iff S _).mp (hA.of_iso epull)
  have hM : StacksDraft.PseudoCoherence.IsPseudoCoherent M :=
    (StacksDraft.Perfect.isPseudoCoherent_derivedExtensionScalars_iff f.hom hf hnil M).mp hS
  exact ((isPseudoCoherent_mapDerivedCategory_tilde_iff R M).mpr hM).of_iso e

/-! ### The algebraic inputs of the missing quasi-coherence half -/

/-- **A module annihilated by the kernel of a surjection is restricted from the quotient.** If
`f : R →+* S` is surjective and `ker f` annihilates an `R`-module `N`, then `N` carries an
`S`-module structure inducing its `R`-module structure; that is, `N` is isomorphic to the
restriction of scalars of an `S`-module along `f`.

The `S`-module is `N ⧸ (ker f • ⊤)`, which is `N` itself because that submodule is `⊥`; its
`S`-action comes from the ring isomorphism `R ⧸ ker f ≅ S` of
`RingHom.quotientKerEquivOfSurjective`. -/
public theorem exists_restrictScalars_iso_of_smul_eq_bot
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) (N : ModuleCat.{u} R)
    (hN : RingHom.ker f • (⊤ : Submodule R N) = ⊥) :
    ∃ M : ModuleCat.{u} S, Nonempty ((ModuleCat.restrictScalars f).obj M ≅ N) := by
  let _ : Module S (N ⧸ (RingHom.ker f • (⊤ : Submodule R N))) :=
    Module.compHom _ (RingHom.quotientKerEquivOfSurjective hf).symm.toRingHom
  let M : ModuleCat.{u} S := ModuleCat.of S (N ⧸ (RingHom.ker f • (⊤ : Submodule R N)))
  let e : ((ModuleCat.restrictScalars f).obj M) ≃ₗ[R]
      (N ⧸ (RingHom.ker f • (⊤ : Submodule R N))) :=
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro r x
        refine Quotient.inductionOn x fun y => ?_
        show (RingHom.quotientKerEquivOfSurjective hf).symm (f r) •
          (Submodule.Quotient.mk y : N ⧸ (RingHom.ker f • (⊤ : Submodule R N))) = _
        have hr : (RingHom.quotientKerEquivOfSurjective hf).symm (f r) =
            Ideal.Quotient.mk (RingHom.ker f) r := by
          apply (RingHom.quotientKerEquivOfSurjective hf).injective
          rw [RingEquiv.apply_symm_apply]
          rfl
        rw [hr]
        rfl }
  exact ⟨M, ⟨(e.trans (Submodule.quotEquivOfEqBot _ hN)).toModuleIso⟩⟩

/-- **Dévissage along a nilpotent ideal.** A property of `R`-modules which is stable under
extensions and holds for every module annihilated by a nilpotent ideal `I` holds for every
module.

The induction is on the power of `I` that annihilates the module, and the inductive step is the
short exact sequence `0 → I·N → N → N/I·N → 0`: the quotient is annihilated by `I`, and `I·N` is
annihilated by one power less. Only `I^n = 0` is used, so no finiteness of `I` or of the modules
is needed. -/
public theorem prop_of_isNilpotent_of_smul_eq_bot
    {R : Type u} [CommRing R] (I : Ideal R) (hI : IsNilpotent I)
    (P : ModuleCat.{u} R → Prop)
    (hext : ∀ T : ShortComplex (ModuleCat.{u} R), T.ShortExact → P T.X₁ → P T.X₃ → P T.X₂)
    (hbase : ∀ N : ModuleCat.{u} R, I • (⊤ : Submodule R N) = ⊥ → P N)
    (N : ModuleCat.{u} R) : P N := by
  have step (n : ℕ) : ∀ N : ModuleCat.{u} R, I ^ (n + 1) • (⊤ : Submodule R N) = ⊥ → P N := by
    induction n with
    | zero => simpa using hbase
    | succ n ih =>
      intro N hN
      let J : Submodule R N := I • ⊤
      let T : ShortComplex (ModuleCat.{u} R) :=
        ShortComplex.mk (ModuleCat.ofHom J.subtype) (ModuleCat.ofHom J.mkQ)
          (by ext x; exact (Submodule.Quotient.mk_eq_zero J).2 x.2)
      have hT : T.ShortExact := ShortComplex.ShortExact.mk'
        (by
          rw [ShortComplex.moduleCat_exact_iff]
          intro x hx
          exact (LinearMap.exact_subtype_mkQ J x).mp hx)
        ((ModuleCat.mono_iff_injective _).2 Subtype.coe_injective)
        ((ModuleCat.epi_iff_surjective _).2 (Submodule.mkQ_surjective J))
      refine hext T hT (ih (ModuleCat.of R J) ?_) (hbase (ModuleCat.of R (N ⧸ J)) ?_)
      · refine le_antisymm (Submodule.smul_le.2 fun r hr x _ => ?_) bot_le
        rw [Submodule.mem_bot]
        have hx : r • (x : N) ∈ I ^ (n + 1) • J := Submodule.smul_mem_smul hr x.2
        have hJ : I ^ (n + 1) • J = ⊥ := by
          show I ^ (n + 1) • (I • (⊤ : Submodule R N)) = ⊥
          rw [← Submodule.mul_smul, ← pow_succ, hN]
        exact Submodule.coe_eq_zero.mp ((Submodule.mem_bot R).mp (hJ.le hx))
      · refine le_antisymm (Submodule.smul_le.2 fun r hr y _ => ?_) bot_le
        rw [Submodule.mem_bot]
        obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective J y
        exact (Submodule.Quotient.mk_eq_zero J).2 (Submodule.smul_mem_smul hr Submodule.mem_top)
  obtain ⟨n, hn⟩ := hI
  refine step n N ?_
  rw [pow_succ, hn, zero_mul, zero_smul]
  rfl

end Stacks.Thickenings

end
