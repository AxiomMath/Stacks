module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import StacksFrontier.AlgebraicGeometry.SymmetricSituation.Basic
public import StacksFrontier.AlgebraicGeometry.SymmetricSituation.SliceRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraConstruction.Sectionwise

/-!
# Quasi-coherence of the symmetric powers: the degree-one piece, and the residue

`Stacks.RelativeProj.symmetricSituation` builds a relative `Proj` situation out of the
symmetric algebra of a sheaf of modules `F` on a scheme, taking as its one hypothesis the
quasi-coherence of every nonnegative homogeneous piece of
`SheafOfModules.sheafifiedSymmetricAlgebra`. This file settles two things about that
hypothesis.

**It is not unconditional.** The degree-one piece of the symmetric algebra *is* `F`: the
sectionwise degree-one generator `PresheafOfModules.symPowIntGen` is an isomorphism of
presheaves of modules, because `SymmetricAlgebra.ι` is injective and `Sym¹` is by definition
the range of `SymmetricAlgebra.ι`. So the hypothesis of `symmetricSituation` *implies* that `F`
is quasi-coherent, and no proof of it for an arbitrary `F : X.Modules` can exist. The
hypothesis is exactly clause (5) of Tag 01CK, whose source statement assumes `F` quasi-coherent.

**With `F` quasi-coherent it reduces to a single obligation.** Combining the quasi-coherent
data of `F` with `Stacks.SliceAlgebra.isQuasicoherent_piece_of_presentations`, quasi-coherence
of every piece follows from: *a sheaf of modules with a global presentation has a symmetric
power with a global presentation*, over each slice site of the cover. That is Tag 01CJ at the
sheaf level (the presentation sequence `F₂ ⊗ Symⁿ⁻¹(F₁) → Symⁿ(F₁) → Symⁿ(F) → 0`) together
with Tag 00DN at the sheaf level (a symmetric power of a free sheaf of modules is free). The first
is `SheafOfModules.exact_and_epi_symmetricPresentationShortComplex`; the second is not available,
see the implementation notes.

## Main definitions

* `PresheafOfModules.symmetricAlgebraGenIso`: the degree-one generator of the sectionwise
  symmetric algebra is an isomorphism `F ≅ Sym¹ F`, the symmetric counterpart of
  `PresheafOfModules.tensorAlgebraGenIso`.
* `SheafOfModules.sheafifiedSymmetricPieceOneIso`: the degree-one identification
  `Sym¹(F) ≅ F` for the symmetric algebra of a sheaf of modules, the counterpart of
  `SheafOfModules.sheafifiedTensorPieceOneIso`.

## Main results

* `SymmetricAlgebra.ι_injective`: the canonical map `M → Sym_R(M)` is injective.
* `SheafOfModules.isQuasicoherent_of_isQuasicoherent_sheafifiedSymmetricAlgebra_piece_one` and
  `Stacks.RelativeProj.isQuasicoherent_of_forall_piece_isQuasicoherent`: **quasi-coherence of
  the symmetric pieces forces `F` to be quasi-coherent.** The second is stated at the exact
  spelling of the `hqc` hypothesis of `Stacks.RelativeProj.symmetricSituation`.
* `Stacks.SliceAlgebra.isQuasicoherent_piece_of_symmetricPowerPresentations`: for a
  quasi-coherent `F` on a scheme, quasi-coherence of the degree-`n` symmetric piece follows
  from a presentation of the degree-`n` symmetric power of any sheaf of modules admitting a
  presentation on a slice site.

## Implementation notes

**No `@[stacks]` tag.** Nothing here proves a clause of Tag 01CK. The degree-one
identification is part of the data of the symmetric algebra rather than a numbered clause of a
tag, and the two quasi-coherence results are a *necessary condition* and a *reduction*, not
clause (5).

**What clause (5) still needs.** After
`isQuasicoherent_piece_of_symmetricPowerPresentations` the whole of the sheaf-theoretic clause
(5) of Tag 01CK is the single hypothesis `hpres`: a `SheafOfModules.Presentation` of
`(sheafifiedSymmetricAlgebra _ G).piece n` for a `G` that has one. By the source's proof that
is Tag 01CJ — whose maps and complex are built in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PowerPresentationSequences` — plus freeness of a
symmetric power of a free sheaf of modules, which is available for plain modules
(`SymPow.free_symmetricPower`, `SymPow.symmetricPower_freePresentation`) and not for sheaves.

**Tag 01CJ for symmetric powers is proved, and its route does not run through Tag 01CH.**
Surjectivity of the second map is `SheafOfModules.epi_descComp_app_symmetric`; exactness at the
middle term is `SheafOfModules.exact_symmetricPresentationShortComplex`. No stalk appears in
either: the step that looks like a stalk computation — passing from `Symⁿ` of a presheaf of modules
to `Symⁿ` of the sheaf it sheafifies to — is the universal property
`PresheafOfModules.isSymmetricAlgebra_sheafify_symmetricAlgebra`, which is stated for an
*arbitrary* presheaf of modules and not only for the underlying presheaf of a sheaf, read through
`SheafOfModules.GradedAlgebra.IsSymmetricAlgebra.pieceIso`. With it, exactness reduces to the
*sectionwise* algebraic Tag 00DO, which is `symmetric_power_presentation`, applied to the
sectionwise-exact sequence of presheaves of modules obtained by taking the presheaf cokernel, and
then sheafified — sheafification of presheaves of modules being exact. The sheafification
description (01CG) holds in this library by construction (`Stacks.GradedAlgebra.sheafify_piece`)
and the restriction-to-an-open case of 01CI is `Stacks.SliceAlgebra.symmetricPieceOverIso`.

So what clause (5) still owes is **Tag 00DN at the sheaf level** (`Symⁿ` of a free sheaf of
modules is free) together with freeness of `F₂ ⊗ Symⁿ⁻¹(F₁)` for free `F₁`, `F₂`; with those,
`exact_and_epi_symmetricPresentationShortComplex` supplies `hpres` below.

**Why `SymmetricAlgebra.ι` is injective.** `Sym_R(M)` is the free commutative `R`-algebra on
`M`, so the linear map `M → R ⊕ M` into the trivial square-zero extension extends to an
algebra map; it sends `ι m` to `inr m`, and `TrivSqZeroExt.inr` is injective. The square-zero
extension needs a right `R`-action on `M`, supplied here from the left one by commutativity of
`R`; both that and the `CommRing` structure stay inside the proof.

## References

* [Stacks Project, Tag 01CK](https://stacks.math.columbia.edu/tag/01CK)
* [Stacks Project, Tag 01CJ](https://stacks.math.columbia.edu/tag/01CJ)
* [Stacks Project, Tag 00DN](https://stacks.math.columbia.edu/tag/00DN)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite PresheafOfModules
  TrivSqZeroExt

universe v u w a

/-- **The canonical map `M → Sym_R(M)` is injective.** -/
theorem SymmetricAlgebra.ι_injective (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M]
    [Module R M] : Function.Injective (SymmetricAlgebra.ι R M) := by
  let _ : Module Rᵐᵒᵖ M :=
    Module.compHom M ((RingHom.id R).fromOpposite fun a b => mul_comm a b)
  have _ : IsCentralScalar R M := ⟨fun _ _ => rfl⟩
  let _ : CommRing (TrivSqZeroExt R M) := TrivSqZeroExt.commRing
  let f : M →ₗ[R] TrivSqZeroExt R M :=
    { toFun := fun m => inr m
      map_add' := fun a b => by simp
      map_smul' := fun r a => by simp }
  intro a b hab
  have h : ∀ m : M, (SymmetricAlgebra.lift f) (SymmetricAlgebra.ι R M m) = inr m := fun m => by
    simp [f]
  have h2 := h a
  rw [hab, h b] at h2
  exact inr_injective h2.symm

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat))

/-- The degree-one generator of the sectionwise symmetric algebra is injective on sections. -/
theorem symmetricAlgebraGen_injective (X : Cᵒᵖ) :
    Function.Injective (PresheafOfModules.Hom.app (symPowIntGen F) X) := fun _ _ h =>
  SymmetricAlgebra.ι_injective _ _ (congrArg Subtype.val h)

/-- The degree-one generator of the sectionwise symmetric algebra is surjective on sections:
`Sym¹` is the range of `SymmetricAlgebra.ι`. -/
theorem symmetricAlgebraGen_surjective (X : Cᵒᵖ) :
    Function.Surjective (PresheafOfModules.Hom.app (symPowIntGen F) X) := by
  rintro ⟨x, hx⟩
  replace hx : x ∈ SymPow.symmetricPower 1 ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X) := hx
  rw [SymPow.symmetricPower, pow_one] at hx
  obtain ⟨m, rfl⟩ := hx
  exact ⟨m, Subtype.ext rfl⟩

/-- **The degree-one generator of the sectionwise symmetric algebra is an isomorphism**: the
degree-one piece of `Sym_{O(U)}(F(U))` is `F(U)`, naturally in `U`. The two halves are
`PresheafOfModules.symmetricAlgebraGen_injective` and `symmetricAlgebraGen_surjective`. -/
noncomputable def symmetricAlgebraGenIso : F ≅ symPowInt 1 F := by
  have hiso : ∀ X : Cᵒᵖ, IsIso ((symPowIntGen F).app X) := fun X =>
    (ConcreteCategory.isIso_iff_bijective _).mpr
      ⟨symmetricAlgebraGen_injective F X, symmetricAlgebraGen_surjective F X⟩
  refine isoMk (fun X => asIso ((symPowIntGen F).app X)) ?_
  intro X Y f
  exact (symPowIntGen F).naturality f

/-- `PresheafOfModules.symmetricAlgebraGenIso` is the degree-one generator. -/
@[simp]
theorem symmetricAlgebraGenIso_hom :
    (symmetricAlgebraGenIso F).hom = symPowIntGen F := rfl

end PresheafOfModules

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (F : SheafOfModules.{w} (toRingCat J Osharp))

/-- **The degree-one identification** `Sym¹(F) ≅ F`: the sectionwise degree-one generator is an
isomorphism, and the sheafification of `F.val` is `F`. -/
noncomputable def sheafifiedSymmetricPieceOneIso :
    (sheafifiedSymmetricAlgebra J F).piece 1 ≅ F :=
  (PresheafOfModules.sheafification (𝟙 (toRingCat J Osharp).obj)).mapIso
      (PresheafOfModules.symmetricAlgebraGenIso F.val).symm ≪≫
    sheafifiedValIso J F

variable [∀ Y : C, HasSheafify (J.over Y) AddCommGrpCat.{w}]
  [∀ Y : C, (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Quasi-coherence of the degree-one symmetric piece forces `F` to be quasi-coherent**, that
piece being `F` itself. So quasi-coherence of all the symmetric pieces is not a property of an
arbitrary sheaf of modules: it is clause (5) of Tag 01CK, which assumes `F` quasi-coherent. -/
theorem isQuasicoherent_of_isQuasicoherent_sheafifiedSymmetricAlgebra_piece_one
    (h : ((sheafifiedSymmetricAlgebra J F).piece 1).IsQuasicoherent) : F.IsQuasicoherent :=
  (isQuasicoherent (toRingCat J Osharp)).prop_of_iso (sheafifiedSymmetricPieceOneIso J F) h

end SheafOfModules

namespace Stacks

open _root_.AlgebraicGeometry TopologicalSpace _root_.SheafOfModules

/-- **The hypothesis of `Stacks.RelativeProj.symmetricSituation` implies that `F` is
quasi-coherent.** Taken at `n = 1`, where the symmetric piece is `F` itself. In particular that
hypothesis cannot be discharged for an arbitrary `F : X.Modules`. -/
theorem RelativeProj.isQuasicoherent_of_forall_piece_isQuasicoherent (X : Scheme.{u})
    (F : X.Modules)
    (hqc : ∀ n : ℕ, ((SheafOfModules.sheafifiedSymmetricAlgebra
      (Opens.grothendieckTopology ↥X) F).piece (n : ℤ)).IsQuasicoherent) :
    F.IsQuasicoherent :=
  SheafOfModules.isQuasicoherent_of_isQuasicoherent_sheafifiedSymmetricAlgebra_piece_one _ F
    (by exact_mod_cast hqc 1)

/-- **Clause (5) of Tag 01CK, reduced to one obligation.** For a quasi-coherent sheaf of
modules `F` on a scheme, the degree-`n` piece of its symmetric algebra is quasi-coherent as
soon as the degree-`n` symmetric power of *any* sheaf of modules admitting a global
presentation on a slice site admits a global presentation. The cover and the presentations of
`F` on it come from the quasi-coherent data of `F`, and the passage from the slice sites back
to `X` is `Stacks.SliceAlgebra.isQuasicoherent_piece_of_presentations`. -/
theorem SliceAlgebra.isQuasicoherent_piece_of_symmetricPowerPresentations (X : Scheme.{u})
    (F : X.Modules) [F.IsQuasicoherent] (n : ℤ)
    (hpres : ∀ (Y : Opens ↥X)
      (G : SheafOfModules.{u} (toRingCat ((Opens.grothendieckTopology ↥X).over Y)
        (X.sheaf.over Y))), G.Presentation →
        ((sheafifiedSymmetricAlgebra ((Opens.grothendieckTopology ↥X).over Y) G).piece
          n).Presentation) :
    ((sheafifiedSymmetricAlgebra (Opens.grothendieckTopology ↥X) F).piece n).IsQuasicoherent := by
  obtain ⟨q⟩ := (inferInstance : F.IsQuasicoherent).nonempty_quasicoherentData
  exact SliceAlgebra.isQuasicoherent_piece_of_presentations _ F q.coversTop n
    fun i => hpres (q.X i) _ (q.presentation i)

end Stacks

end
