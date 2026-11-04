module

public import StacksFrontier.AlgebraicGeometry.CoherentKernel.Basic
public import StacksFrontier.AlgebraicGeometry.Constructions.DirectSumQuasiCompactSections
public import StacksFrontier.AlgebraicGeometry.FiniteDirectImageCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.AssociatedGraded
public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.BaseChangeGradedModule
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteTypePullbackScheme
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LeftGradedModuleRealization

/-!
# Finite type of the module of Tag 01SB produced from a graded module of finite type

[Stacks, Tag 0897] runs over the base change `X' = Spec(B) ×_{Spec A} X` and uses on it a
*coherent* module `ℱ'` with `π_* ℱ' = ⨁ₙ ℱₙ`.
`Stacks.AffineGradedAlgebra.exists_isQuasicoherent_pushforward_baseChange_iso_intCoprod`
produces one that is only quasi-coherent, because the isomorphism it returns is one of
`𝒪_X`-modules and finite type of `ℱ'` is measured over `Γ(𝒪_{X'}, π⁻¹U)`, not over `Γ(X, U)`.

This file produces the finite type. The point is that `ℱ'` has to be produced *together with*
the identification of its direct image in the quasi-coherent `𝓑`-modules — the one
`Stacks.RelativeSpec.exists_iso_relativeSpecQcohPushforward_gradedModuleSheafOfRight_of_piece`
returns and which the quasi-coherent statement above forgets along
`Stacks.AffineAlgebraEquivalence.restrictScalars_relativeSpecQcohEquivalence_functor_obj`. Over
an affine open `U` of `X` that identification *is* linear over `Γ(𝓑, U)`, and
`Γ(𝒪_{X'}, π⁻¹U)` is `Γ(𝓑, U)` read through [Stacks, Tag 01LX] (3).

## Main results

* `SheafOfModules.LeftGradedModule.bijective_toUngradedSheafModule_app`: **the sheafification
  unit of the ungraded realization of a left graded module is bijective on the sections over an
  affine open** — the module-side companion of
  `Stacks.RelativeSpec.bijective_totalUnit_of_isAffineOpen`.
* `SheafOfModules.GradedModule.moduleFinite_total`: **local finite generation by homogeneous
  sections says that the direct sum of the sections of the homogeneous pieces over an affine
  open is a finite module over the direct sum of the sections of the homogeneous pieces of the
  algebra.** This is `Stacks.Coherent.IsFiniteTypeOnAffine`, a degreewise `AddSubgroup.closure`
  statement, read as a spanning statement over `Stacks.GradedAlgebra.Total`.
* `Stacks.RelativeSpec.moduleFinite_sections_gradedModuleSheafOfRight`: the same for the
  sections of the ungraded realization over the sections of the algebra sheaf.
* `Stacks.RelativeSpec.moduleFinite_sections_of_iso` and
  `isFiniteType_gradedModuleSheafOfRight_of_iso`: **the module of [Stacks, Tag 01SB] on the
  relative spectrum is of finite type**, given the identification of its direct image in the
  quasi-coherent `𝒜`-modules.
* `Stacks.AffineGradedAlgebra.exists_isFiniteType_pushforward_baseChange_iso_intCoprod`:
  **on `X' = Spec(B) ×_{Spec A} X` there is a quasi-coherent module of finite type whose
  direct image along `π` is `∐ₙ ℱₙ`** — returned together with the identification in the
  quasi-coherent `𝓑`-modules that the `𝒪_X`-module one is read off, which is the only record of
  which scalars that identification respects.

## Implementation notes

**The three transports.** Finite type of `ℱ'` on `X'` is module-finiteness of `Γ(ℱ', π⁻¹U)` over
`Γ(𝒪_{X'}, π⁻¹U)` on an affine open `U` of `X`, and it is reached in three steps, each of which
is a transport of scalars along a ring homomorphism rather than a new sheaf-theoretic fact.

* `Stacks.Coherent.IsFiniteTypeOnAffine ℱ` says the chosen homogeneous sections *span*
  `SheafOfModules.LeftGradedModule.Total` over `Stacks.GradedAlgebra.Total`. The degreewise
  `AddSubgroup.closure` becomes a `Submodule.span` because the action of a homogeneous section
  of the algebra on a homogeneous section of the module *is* the action of the ungraded
  realization, by `SheafOfModules.LeftGradedModule.incl_smul_incl`, and because every section of
  the ungraded realization is a finite sum of homogeneous ones.
* the sections pass from the `Total` to the sheaf. On the algebra side nothing more than the
  ring homomorphism `Stacks.GradedAlgebra.totalUnit` is needed — not its bijectivity, which is
  `Stacks.RelativeSpec.totalSectionsRingEquiv` and would be available. On the module side what
  is needed is *surjectivity* of the sheafification unit over an affine open, which is
  `bijective_toUngradedSheafModule_app` below: the same three-line argument as
  `Stacks.RelativeSpec.bijective_totalUnit_of_isAffineOpen`, with
  `Stacks.GradedAlgebra.directSumHom` replaced by
  `SheafOfModules.LeftGradedModule.ungradedDirectSumHom`, resting on
  `Stacks.DirectSumSections.bijective_sheafifyUnit_directSum_app`, which is
  [Stacks, Tag 01AI].
* The identification of `Γ(ℱ', π⁻¹U)` with `Γ(𝒢, U)` is linear over `Γ(𝓑, U)` because the
  isomorphism carried here lives in the quasi-coherent `𝓑`-modules; and
  `Stacks.AffineAlgebraEquivalence.relativeSpecQcohEquivalence_functor_obj_obj` writes the
  functor of [Stacks, Tag 01SB] as a restriction of scalars of the direct image over
  `π_* 𝒪_{X'}` along `(pushforwardRingIso 𝓑).inv`, whose component over `U` is a ring
  isomorphism `Γ(𝓑, U) ≅ Γ(𝒪_{X'}, π⁻¹U)`. So the `Γ(𝓑, U)`-module `Γ(ℱ', π⁻¹U)` and the
  `Γ(𝒪_{X'}, π⁻¹U)`-module `Γ(ℱ', π⁻¹U)` are the same module read over two spellings of one
  ring, and `Module.Finite.of_surjective` at the identity carries the finiteness across.

**Why `Module.Finite.of_surjective` and not a linear equivalence.** Every step above is
semilinear over a ring homomorphism rather than linear, so `Module.Finite.equiv` does not
apply; `Module.Finite.of_surjective` takes exactly a semilinear surjection, which is what each
step supplies. In particular the middle step needs no injectivity: the generators of
`Γ(𝒢, U)` are the images of the generators of the `Total`.

**Where the finite type is proved.** On the relative spectrum, not on `X'`: the preimages of the
affine opens of `X` under `relativeSpecToBase` are affine
(`Stacks.AffineAlgebraEquivalence.isAffineOpen_preimage_relativeSpecToBase`) and cover it, so
`Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isFiniteTildeOn_of_moduleFinite_sections`
and `Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_of_cover_isFiniteTildeOn` — (4) ⇒ (2) of
[Stacks, Tag 01XZ] — apply there directly. It is then carried to `X'` by
`Stacks.Modules.isFiniteType_pullback` along the identification of
[Stacks, Tag 01LX]; no hypothesis on the base is needed for that, and in particular the
coherence upgrade of [Stacks, Tag 01XZ] is left to the consumer, which is where the Noetherian
hypotheses live.

## References

* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
* [Stacks Project, Tag 01AI](https://stacks.math.columbia.edu/tag/01AI)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AffineAlgebraEquivalence
open Stacks.AlgebraicGeometry.CoherentTFAE
open Stacks.AlgebraicGeometry.FiniteDirectImageCoherent
open Stacks.RelativeSpec (AlgebraSheaf)

universe u

namespace SheafOfModules.LeftGradedModule

variable {X : Scheme.{u}} {A : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf}

/-- **A homogeneous section of a left graded module, seen in the ungraded realization, depends
only on its degree up to the identification of the degrees.** -/
public theorem incl_congr_heq (M : LeftGradedModule.{u, u, u} A) {W : (Opens ↥X)ᵒᵖ} {k k' : ℤ}
    (h : k = k') (x : (M.piece k).val.obj W) (x' : (M.piece k').val.obj W) (hx : HEq x x') :
    M.incl k x = M.incl k' x' := by
  subst h
  rw [eq_of_heq hx]

/-- **The sheafification unit of the ungraded realization of a left graded module is bijective on
the sections over an affine open of a scheme**: over such an open the sections of the ungraded
realization are the direct sum of the sections of the homogeneous pieces.

This is the module-side companion of `Stacks.RelativeSpec.bijective_totalUnit_of_isAffineOpen`,
with the same proof: the comparison into the sheafification is locally bijective, so
`Stacks.PresheafOfModules.bijective_sheafifyUnit_app_iff` reduces the claim to bijectivity of
the sheafification unit of the objectwise direct sum, which is
`Stacks.DirectSumSections.bijective_sheafifyUnit_directSum_app` — [Stacks, Tag 01AI] — at the
quasi-compact open `V`. -/
public theorem bijective_toUngradedSheafModule_app (M : LeftGradedModule.{u, u, u} A)
    {V : X.Opens} (hV : IsAffineOpen V) :
    Function.Bijective (PresheafOfModules.Hom.app M.ungradedDirectSumHom (op V)) :=
  (Stacks.PresheafOfModules.bijective_sheafifyUnit_app_iff (𝟙 X.ringCatSheaf.obj)
      ((SheafOfModules.restrictScalars.{u} A.ungradedStructureMap).obj M.ungradedSheafModule)
      M.ungradedDirectSumHom
      M.isLocallyInjective_ungradedDirectSumHom
      M.isLocallySurjective_ungradedDirectSumHom (op V)).1
    (Stacks.DirectSumSections.bijective_sheafifyUnit_directSum_app (fun n : ℤ => M.piece n) V
      (Stacks.SheafOfModules.isQuasiCompactObject_of_isCompact V hV.isCompact))

end SheafOfModules.LeftGradedModule

namespace SheafOfModules.GradedModule

variable {X : Scheme.{u}} {A : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf}
  (F : SheafOfModules.GradedModule.{u, u, u} A)
  (hc : ∀ (i j : ℤ) (W : (Opens ↥X)ᵒᵖ) (a : (A.piece i).val.obj W) (b : (A.piece j).val.obj W),
    HEq ((A.mul i j).app W a b) ((A.mul j i).app W b a))

include hc in
/-- **The right action of a homogeneous section of the algebra on a homogeneous section of a
graded module is the action of the ungraded realization.** This is
`SheafOfModules.LeftGradedModule.incl_smul_incl` with the two degrees commuted, which is where
the commutativity hypothesis `hc` is spent. -/
public theorem incl_smul_incl_right (n m : ℤ) (W : (Opens ↥X)ᵒᵖ) (z : (F.piece n).val.obj W)
    (a : (A.piece m).val.obj W) :
    A.toPresheafGradedAlgebra.incl m a • (F.toLeftGradedModuleOfComm hc).incl n z =
      (F.toLeftGradedModuleOfComm hc).incl (n + m) (F.smul n m W z a) :=
  ((F.toLeftGradedModuleOfComm hc).incl_smul_incl m n a z).trans
    ((F.toLeftGradedModuleOfComm hc).incl_congr_heq (add_comm m n) _ _
      (F.heq_smulOfEq n m (m + n) (add_comm n m) W z a))

include hc in
/-- **Local finite generation by homogeneous sections is a spanning statement over the ungraded
realization of the algebra.** Over an affine open `U`, the direct sum of the sections of the
homogeneous pieces of `ℱ` is a finite module over the direct sum of the sections of the
homogeneous pieces of `𝒜`.

`Stacks.Coherent.IsFiniteTypeOnAffine` gives a finite set of homogeneous sections whose
degreewise `AddSubgroup.closure` under the graded action is everything. Their images under
`SheafOfModules.LeftGradedModule.incl` span: the span is an additive subgroup containing every
`ℱ_{d+m}`-generator of the closure by `incl_smul_incl_right`, and every section of the ungraded
realization is a finite sum of homogeneous ones by
`SheafOfModules.LeftGradedModule.incl_induction`. -/
public theorem moduleFinite_total (hft : Stacks.Coherent.IsFiniteTypeOnAffine F)
    (U : X.affineOpens) :
    Module.Finite (A.toPresheafGradedAlgebra.Total (op U.1))
      ((F.toLeftGradedModuleOfComm hc).Total (op U.1)) := by
  obtain ⟨gens, hgens⟩ := hft U
  rw [Module.finite_def, Submodule.fg_def]
  refine ⟨(fun s : Σ n : ℤ, (F.piece n).val.obj (op U.1) =>
      (F.toLeftGradedModuleOfComm hc).incl s.1 s.2) '' (gens : Set _),
    Set.Finite.image _ gens.finite_toSet, ?_⟩
  set P := Submodule.span (A.toPresheafGradedAlgebra.Total (op U.1))
    ((fun s : Σ n : ℤ, (F.piece n).val.obj (op U.1) =>
      (F.toLeftGradedModuleOfComm hc).incl s.1 s.2) '' (gens : Set _)) with hP
  have hgen : ∀ s : Σ n : ℤ, (F.piece n).val.obj (op U.1), s ∈ gens →
      (F.toLeftGradedModuleOfComm hc).incl s.1 s.2 ∈ P := fun s hs =>
    Submodule.subset_span ⟨s, hs, rfl⟩
  have key : ∀ (n : ℤ) (x : (F.piece n).val.obj (op U.1)),
      (F.toLeftGradedModuleOfComm hc).incl n x ∈ P := by
    intro n x
    let g : (F.piece n).val.obj (op U.1) →+ (F.toLeftGradedModuleOfComm hc).Total (op U.1) :=
      AddMonoidHom.mk' (fun y => (F.toLeftGradedModuleOfComm hc).incl n y)
        fun y y' => (F.toLeftGradedModuleOfComm hc).incl_add n y y'
    have hsub : { t : (F.piece n).val.obj (op U.1) |
        ∃ s : Σ d : ℤ, (F.piece d).val.obj (op U.1),
          s ∈ gens ∧ ∃ (m : ℤ) (a : (A.piece m).val.obj (op U.1)) (h : s.1 + m = n),
            t = h ▸ F.smul s.1 m (op U.1) s.2 a } ⊆
        ↑(AddSubgroup.comap g P.toAddSubgroup) := by
      rintro t ⟨s, hs, m, a, h, rfl⟩
      subst h
      show (F.toLeftGradedModuleOfComm hc).incl (s.1 + m) (F.smul s.1 m (op U.1) s.2 a) ∈ P
      rw [← F.incl_smul_incl_right hc s.1 m (op U.1) s.2 a]
      exact P.smul_mem _ (hgen s hs)
    exact (AddSubgroup.closure_le _).2 hsub (hgens n ▸ AddSubgroup.mem_top x)
  refine Submodule.eq_top_iff'.2 fun z => ?_
  induction z using (F.toLeftGradedModuleOfComm hc).incl_induction with
  | zero => exact P.zero_mem
  | incl n x => exact key n x
  | add z z' hz hz' => exact P.add_mem hz hz'

end SheafOfModules.GradedModule

namespace Stacks.RelativeSpec

variable {X : Scheme.{u}} {A : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf}
  (F : SheafOfModules.GradedModule.{u, u, u} A)
  (hc : ∀ (i j : ℤ) (W : (Opens ↥X)ᵒᵖ) (a : (A.piece i).val.obj W) (b : (A.piece j).val.obj W),
    HEq ((A.mul i j).app W a b) ((A.mul j i).app W b a))
  (hF : ∀ n : ℤ, (F.piece n).IsQuasicoherent)
  (hA : AlgebraSheaf.IsQuasicoherent (gradedAlgebraSheaf X A hc))

/-- **Module-finiteness transports along a surjective additive map that is semilinear over a ring
homomorphism.** -/
private theorem moduleFinite_of_surjective_of_map_smul {R S M N : Type*} [Semiring R] [Semiring S]
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module S N] [Module.Finite R M]
    (σ : R →+* S) (f : M → N) (hadd : ∀ x y, f (x + y) = f x + f y)
    (hsmul : ∀ (r : R) x, f (r • x) = σ r • f x) (hf : Function.Surjective f) :
    Module.Finite S N :=
  Module.Finite.of_surjective ({ toFun := f, map_add' := hadd, map_smul' := hsmul } : M →ₛₗ[σ] N) hf

include hc in
/-- **The sections of the ungraded realization of a graded module of finite type over an affine
open form a finite module over the sections of the algebra sheaf.**

`SheafOfModules.GradedModule.moduleFinite_total` supplies the finiteness over
`Stacks.GradedAlgebra.Total`, and the sheafification unit is a surjection onto the sections
semilinear over `Stacks.GradedAlgebra.totalUnit`, by
`SheafOfModules.LeftGradedModule.bijective_toUngradedSheafModule_app`. Only surjectivity is
used. -/
public theorem moduleFinite_sections_gradedModuleSheafOfRight
    (hft : Stacks.Coherent.IsFiniteTypeOnAffine F) (U : X.affineOpens) :
    Module.Finite ((AlgebraSheaf.ringSheaf (gradedAlgebraSheaf X A hc)).obj.obj (op U.1))
      ((gradedModuleSheafOfRight X A hc F).val.obj (op U.1)) := by
  have := F.moduleFinite_total hc hft U
  refine moduleFinite_of_surjective_of_map_smul
    (R := A.toPresheafGradedAlgebra.Total (op U.1))
    (M := (F.toLeftGradedModuleOfComm hc).Total (op U.1))
    (A.toPresheafGradedAlgebra.totalUnit (Opens.grothendieckTopology (X : TopCat)) (op U.1))
    (fun z => ((F.toLeftGradedModuleOfComm hc).toUngradedSheafModule.app (op U.1)) z)
    (map_add (((F.toLeftGradedModuleOfComm hc).toUngradedSheafModule.app (op U.1)).hom))
    (((F.toLeftGradedModuleOfComm hc).toUngradedSheafModule.app (op U.1)).hom).map_smul ?_
  exact ((F.toLeftGradedModuleOfComm hc).bijective_toUngradedSheafModule_app U.2).2

include hc hA in
/-- **The sections of the module of [Stacks, Tag 01SB] over the preimage of an affine open form a
finite module.**

The isomorphism `iso` lives in the quasi-coherent `𝒜`-modules, so its component over `U` is
linear over `Γ(𝒜, U)`; and
`Stacks.AffineAlgebraEquivalence.relativeSpecQcohEquivalence_functor_obj_obj` makes the source of
that component the sections of `𝒢` over `π⁻¹U` with the scalars restricted along the component
of `(pushforwardRingIso 𝒜).inv`. So the finiteness of
`moduleFinite_sections_gradedModuleSheafOfRight` transports along a single semilinear
surjection. -/
public theorem moduleFinite_sections_of_iso (hft : Stacks.Coherent.IsFiniteTypeOnAffine F)
    (G : (relativeSpec (gradedAlgebraSheaf X A hc)).Modules) (hG : G.IsQuasicoherent)
    (iso : (relativeSpecQcohEquivalence (gradedAlgebraSheaf X A hc)).functor.obj ⟨G, hG⟩ ≅
      qcohGradedModuleSheafOfRightOfPiece X A hc F hA hF)
    (U : X.affineOpens) :
    Module.Finite Γ(relativeSpec (gradedAlgebraSheaf X A hc),
        relativeSpecToBase (gradedAlgebraSheaf X A hc) ⁻¹ᵁ U.1)
      Γ(G, relativeSpecToBase (gradedAlgebraSheaf X A hc) ⁻¹ᵁ U.1) := by
  have := hA
  have := moduleFinite_sections_gradedModuleSheafOfRight F hc hft U
  let el := ((_root_.SheafOfModules.evaluation
    (AlgebraSheaf.ringSheaf (gradedAlgebraSheaf X A hc))
    (op U.1)).mapIso ((ObjectProperty.ι _).mapIso iso)).toLinearEquiv.symm
  let sigma : ((AlgebraSheaf.ringSheaf (gradedAlgebraSheaf X A hc)).obj.obj (op U.1) : Type u) →+*
      Γ(relativeSpec (gradedAlgebraSheaf X A hc),
        relativeSpecToBase (gradedAlgebraSheaf X A hc) ⁻¹ᵁ U.1) :=
    ((pushforwardRingIso (gradedAlgebraSheaf X A hc)).inv.hom.app (op U.1)).hom
  exact moduleFinite_of_surjective_of_map_smul (M := (gradedModuleSheafOfRight X A hc F).val.obj
    (op U.1)) sigma el el.map_add el.map_smul el.surjective

include hc hA in
/-- **The module of [Stacks, Tag 01SB] produced from a graded module of finite type is of finite
type on the relative spectrum.**

The preimages of the affine opens of `X` under the structure morphism are affine and cover the
relative spectrum, and over each of them the sections are finite by
`moduleFinite_sections_of_iso`; so (4) ⇒ (2) of [Stacks, Tag 01XZ] applies. -/
public theorem isFiniteType_gradedModuleSheafOfRight_of_iso
    (hft : Stacks.Coherent.IsFiniteTypeOnAffine F)
    (G : (relativeSpec (gradedAlgebraSheaf X A hc)).Modules) (hG : G.IsQuasicoherent)
    (iso : (relativeSpecQcohEquivalence (gradedAlgebraSheaf X A hc)).functor.obj ⟨G, hG⟩ ≅
      qcohGradedModuleSheafOfRightOfPiece X A hc F hA hF) :
    G.IsFiniteType := by
  have := hG
  exact isFiniteType_of_cover_isFiniteTildeOn G
    (fun U : X.affineOpens => relativeSpecToBase (gradedAlgebraSheaf X A hc) ⁻¹ᵁ U.1)
    (IsOpenCover.mk (Scheme.Hom.iSup_preimage_eq_top _ (iSup_affineOpens_eq_top X)))
    (fun U => isAffineOpen_preimage_relativeSpecToBase _ U)
    (fun U => isFiniteTildeOn_of_moduleFinite_sections G
      ⟨_, isAffineOpen_preimage_relativeSpecToBase _ U⟩
      (moduleFinite_sections_of_iso F hc hF hA hft G hG iso U))

end Stacks.RelativeSpec

namespace Stacks.AffineGradedAlgebra

attribute [local instance] isQuasicoherent_gradedAlgebraSheaf_gradedTildePullback

/-- **The module `ℱ'` of the proof of [Stacks, Tag 0897] on the base change
`X' = Spec(B) ×_{Spec A} X`, now of finite type.** For a graded `A`-algebra `B`, a morphism
`f : X ⟶ Spec A` and a graded `f^* B̃`-module `ℱ` with quasi-coherent pieces which is of finite
type on affine opens, there is a quasi-coherent `𝒪_{X'}`-module *of finite type* whose direct
image along the projection `π = pullback.snd` is the coproduct `∐ₙ ℱₙ`.

Nothing is assumed of `f` beyond its target, and nothing of `A`: the Noetherian hypotheses of
[Stacks, Tag 0897] are needed only for the coherence upgrade of [Stacks, Tag 01XZ], which a
consumer performs with
`Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isQuasicoherent_isFiniteType`.

This strengthens `exists_isQuasicoherent_pushforward_baseChange_iso_intCoprod`, and the two
share everything but the finite type: the module is the same
`baseChangeModuleOfRelativeSpec` of the module on the relative spectrum and the isomorphism is
the same composite. What the finite type needs in addition is the isomorphism in the
quasi-coherent `𝓑`-modules, which is why this statement obtains that isomorphism itself rather
than consuming the `𝒪_X`-module one.

**The `𝓑`-linear identification is returned, not discarded.** The conclusion quantifies over the
quasi-coherent module `𝒢` on `Spec_X(𝓑)` and over the identification of its direct image in the
quasi-coherent `𝓑`-modules, and `ℱ'` is `baseChangeModuleOfRelativeSpec 𝒜 f 𝒢`. The
`𝒪_X`-module identification `π_* ℱ' ≅ ∐ₙ ℱₙ` is `pushforwardPullbackIsoIntCoprod` applied to
that one — a total function of it — and is kept as the last conjunct so that this statement
visibly implies the shape
`∃ ℱ', ℱ'.IsQuasicoherent ∧ ℱ'.IsFiniteType ∧ Nonempty (π_* ℱ' ≅ ∐ₙ ℱₙ)`. Concluding *only* that
shape would discard the
`Γ(𝓑, U)`-linearity which is built here and is the whole reason the finite type is provable:
an action carried across an `𝒪_X`-module identification chosen from a bare `Nonempty` cannot be
compared with any action defined from the graded structure, because nothing records which
scalars the identification respects. -/
public theorem exists_isFiniteType_pushforward_baseChange_iso_intCoprod
    {X : Scheme.{u}} (A : Type u) [CommRing A] {B : Type u} [CommRing B] [Algebra A B]
    (𝒜 : ℕ → Submodule A B) [SetLike.GradedMonoid 𝒜] [DirectSum.Decomposition 𝒜]
    (f : X ⟶ Spec (CommRingCat.of A))
    (F : SheafOfModules.GradedModule.{u, u, u}
      (Stacks.Conormal.gradedPullback f (gradedTildeOf A 𝒜)))
    (hF : ∀ n : ℤ, (F.piece n).IsQuasicoherent)
    (hft : Stacks.Coherent.IsFiniteTypeOnAffine F) :
    ∃ (G : (SheafOfModules.isQuasicoherent
        (relativeSpec (gradedTildePullbackAlgebraSheaf A 𝒜 f)).ringCatSheaf).FullSubcategory)
      (_ : (relativeSpecQcohEquivalence
          (gradedTildePullbackAlgebraSheaf A 𝒜 f)).functor.obj G ≅
        qcohGradedTildePullbackModule A 𝒜 f F hF),
      (baseChangeModuleOfRelativeSpec A 𝒜 f G.obj).IsQuasicoherent ∧
      (baseChangeModuleOfRelativeSpec A 𝒜 f G.obj).IsFiniteType ∧
      Nonempty ((Scheme.Modules.pushforward
        (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap A B))) f)).obj
          (baseChangeModuleOfRelativeSpec A 𝒜 f G.obj) ≅ ∐ fun n : ℤ => F.piece n) :=
  let key :=
    Stacks.RelativeSpec.exists_iso_relativeSpecQcohPushforward_gradedModuleSheafOfRight_of_piece X
      (Stacks.Conormal.gradedPullback f (gradedTildeOf A 𝒜))
      (gradedTildePullback_mul_comm A 𝒜 f) F
      (isQuasicoherent_gradedAlgebraSheaf_gradedTildePullback A 𝒜 f) hF
  have := key.choose.property
  have : key.choose.obj.IsFiniteType :=
    Stacks.RelativeSpec.isFiniteType_gradedModuleSheafOfRight_of_iso F
      (gradedTildePullback_mul_comm A 𝒜 f) hF
      (isQuasicoherent_gradedAlgebraSheaf_gradedTildePullback A 𝒜 f) hft key.choose.obj
      key.choose.property key.choose_spec.some
  ⟨key.choose, key.choose_spec.some,
    isQuasicoherent_pullback_baseChangeIsoRelativeSpec A 𝒜 f key.choose.obj,
    Stacks.Modules.isFiniteType_pullback _ key.choose.obj inferInstance,
    ⟨pushforwardPullbackIsoIntCoprod A 𝒜 f F hF key.choose key.choose_spec.some⟩⟩

end Stacks.AffineGradedAlgebra

end
