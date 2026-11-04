module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleQuasicoherentDerived
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModuleEssentialImage
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModuleUnitEpi
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactKernelQuasicoherent
public import StacksFrontier.CategoryTheory.Sites.Modules.AdicQuotientModuleTower
public import StacksCore.Tactic.StacksAttribute

/-!
# The conormal sheaf of an immersion of algebraic spaces

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B` and let
`i : Z ⟶ X` be an **immersion**.  Stacks 76.5 constructs the conormal sheaf of `i` in three
steps: for a *closed* immersion it takes the quasi-coherent ideal sheaf `𝓘 ⊆ 𝒪_X` of `Z`, forms
the short exact sequence `0 → 𝓘² → 𝓘 → 𝓘/𝓘² → 0`, and reads `𝓘/𝓘²` — which `𝓘` annihilates — as
a quasi-coherent `𝒪_Z`-module through the equivalence of Stacks 04CJ; for a general immersion it
applies that to the closed immersion of `Z` into the complement `X ∖ ∂Z` of the boundary of its
image, through which `i` factors by Stacks 04CE.

**Stacks 04CN** names the result:

> **Definition 76.5.1.**  Let `S` be a scheme.  Let `i : Z → X` be an immersion of algebraic
> spaces over `S`.  The *conormal sheaf* `𝒞_{Z/X}` *of* `Z` *in* `X` or the *conormal sheaf of*
> `i` is the quasi-coherent `𝒪_Z`-module `𝓘/𝓘²` described above.

This file supplies all three steps.  The `𝒪_Z`-module is `i^*𝓘`, the realization this
repository already uses for a closed subspace (`AlgebraicGeometry.Space.conormalModule`) and one
category down for schemes (`Stacks.Conormal.conormalSheaf`); what is new here is that this is no
longer a *convention* but a theorem — `AlgebraicGeometry.Space.conormalIdealQuotientIso`
identifies `𝓘/𝓘²` with `i_*i^*𝓘` canonically — that it is quasi-coherent unconditionally, and
that both hold for the conormal sheaf `AlgebraicGeometry.Space.conormalModuleOfImmersion` of an
arbitrary immersion, constructed through the closed factorisation, and not only for a closed one.

## Main definitions

* `AlgebraicGeometry.Space.conormalModuleOfHom`: the conormal module `𝒞_{Z/X} = i^*𝓘` of a
  morphism `i : Z ⟶ X` of algebraic spaces, `𝓘 = Ker(𝒪_X ⟶ i_*𝒪_Z)` being the kernel ideal
  sheaf of `i`.  For the inclusion of a closed subspace it is
  `AlgebraicGeometry.Space.conormalModule`, on the nose.
* `AlgebraicGeometry.Space.conormalIdealSquareModule` and
  `AlgebraicGeometry.Space.conormalIdealSquareι`: the ideal square `𝓘²` and its inclusion into
  `𝓘`.
* `AlgebraicGeometry.Space.conormalIdealQuotient`: the `𝒪_X`-module `𝓘/𝓘²`, the cokernel of that
  inclusion, with its projection `AlgebraicGeometry.Space.conormalIdealQuotientπ`.
* `AlgebraicGeometry.Space.conormalIdealQuotientToPushforward` and
  `AlgebraicGeometry.Space.conormalIdealQuotientIso`: the canonical map `𝓘/𝓘² ⟶ i_*𝒞_{Z/X}`
  induced by the unit of `i^* ⊣ i_*`, and the proof that it is an isomorphism.

## Main results

* `AlgebraicGeometry.Space.idealSheafPow_two_le_kernelIdealSheaf`: the ideal square is
  contained in the ideal, so the quotient below makes sense.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_conormalModuleOfHom`,
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_conormalModule` and
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_conormalModuleOfImmersion`: **the
  quasi-coherence clause of Stacks 04CN, unconditionally**, for a closed immersion, for a closed
  subspace, and for an arbitrary immersion.
* `AlgebraicGeometry.Space.conormalIdealSquareι_comp_eq_zero`: an `𝒪_X`-linear map out of `𝓘`
  into a module annihilated by `𝓘` kills `𝓘²`.
* `AlgebraicGeometry.Space.annihilatedByKerIdeal_conormalIdealQuotient`: `𝓘` annihilates
  `𝓘/𝓘²`, which is what puts that quotient in the essential image of `i_*`.
* `AlgebraicGeometry.Space.conormalIdealQuotientIso` and
  `AlgebraicGeometry.Space.conormalIdealQuotientIsoOfImmersion`: **the identification of
  Stacks 04CN**, `𝓘/𝓘² ≅ i_*𝒞_{Z/X}`, for a closed immersion and for an arbitrary immersion.
* `AlgebraicGeometry.Space.conormalModuleOfImmersion_eq_conormalModuleOfHom`: the conormal sheaf
  `AlgebraicGeometry.Space.conormalModuleOfImmersion` of an immersion is the conormal module of
  its closed factorisation of Stacks 04CE.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_and_nonempty_conormalIdealQuotientIso`:
  **Stacks 04CN**: the conormal sheaf of an immersion is the quasi-coherent `𝒪_Z`-module
  `𝓘/𝓘²`.

## Implementation notes

**Why the identification is an isomorphism, and where each input comes from.**  Write
`η : 𝓘 ⟶ i_*i^*𝓘` for the unit of the adjunction of Stacks 03LU and `π : 𝓘 ⟶ 𝓘/𝓘²` for the
projection.

* `η` kills `𝓘²`, because `i_*i^*𝓘` is annihilated by `𝓘`
  (`AlgebraicGeometry.Space.annihilatedByKerIdeal_modulePushforward`) and a section of `𝓘²` is
  locally a sum of products of two sections of `𝓘`; so `η` factors as `π ≫ φ`.
* `η` is an epimorphism, by
  `AlgebraicGeometry.Space.epi_modulePullbackAdjunction_unit_of_essImage_of_annihilated` fed
  with the now-unconditional
  `AlgebraicGeometry.Space.essImage_modulePushforward_of_annihilatedByKerIdeal`; hence so is
  `φ`.
* `𝓘/𝓘²` is itself annihilated by `𝓘`, so the unit `η_{𝓘/𝓘²}` is an isomorphism, and
  naturality of `η` at `π` together with `π` being an epimorphism gives
  `φ ≫ (i_*i^*π ≫ η_{𝓘/𝓘²}⁻¹) = 𝟙`.  A split monomorphism which is an epimorphism in an
  abelian category is an isomorphism.

Only the first and third items touch sections.  Both go through the local description of the
closure of an objectwise submodule
(`Stacks.SheafOfModules.exists_sieve_of_mem_sheafifySubmodule`), the local surjectivity of an
epimorphism of sheaves of modules
(`Stacks.SheafOfModules.EpiMono.exists_covering_of_epi`) and the separatedness of a sheaf of
modules (`Stacks.SheafOfModules.eq_zero_of_locally_eq_zero`).

**Which ideal power `𝓘²` is.**  It is `SheafOfModules.idealSheafPow 𝓘 2`, the second member of
the family of powers of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/IdealSheafPowers.lean` — the same family
`AlgebraicGeometry.Space.kernelIdealSheafZPow` extends to the integers and from which the
conormal algebra of Stacks 09RN is built, so no second notion of ideal power is introduced
here.  The other power in this repository,
`Stacks.Sites.idealPow` of `StacksFrontier/CategoryTheory/Sites/Modules/IdealSubsheaf.lean`, is
stated over a sheaf of *commutative* rings, a different spelling of the structure sheaf from the
`RingCat`-valued one over which the modules are indexed; the two agree, but mixing the spellings
loses the scalar action on the sections to instance search.  For the same reason the quotient is
not `Stacks.Sites.adicGradedPiece 𝓘 1`, which is in addition the cokernel of `𝓘² ⟶ 𝓘¹` rather
than of `𝓘² ⟶ 𝓘`.

**Why the modules below are introduced by abbreviations, and why the abelian structure is a
local instance.**  `Modules.{u, u} B S hS X.1 X.2` is `SheafOfModules.{u}` over the structure
sheaf; writing a submodule's associated sheaf of modules without that ascription leaves the
module universe an unsolved metavariable, and then the `Zero` on the morphism groups is not
found, so `AlgebraicGeometry.Space.kernelIdealModule` and
`AlgebraicGeometry.Space.conormalIdealSquareModule` carry the ascription once.  Even with the
universe pinned, instance search does not reach the abelian structure at module universe `u`:
see `AlgebraicGeometry.Space.abelianModulesSmallEtale` below, which supplies it.

**Why the scalar action on the sections is seated by hand, and why the scalar is a bound
variable.**  The modules here are indexed by `Stacks.SheafOfModules.Tensor.ringSheaf`, a plain
`def`, so the instance arguments that instance search assembles for a goal stated at the
`AlgebraicGeometry.Space.structureRingSheaf` spelling agree with the ones carried by the section
module's own structure only after that `def` is unfolded, which search — working at `instances`
transparency — will not do.  The two proofs below that act on sections therefore name the
canonical `CategoryTheory.ModuleCat.isModule` of the section module in a `let`, exactly as
`AlgebraicGeometry.Space.AnnihilatedByKerIdeal` itself does; the bound value is term-identical
to the canonical instance, so no second module structure exists, and the statements of the two
theorems are untouched — only their proofs name what search cannot find.

Seating the instance is necessary but not sufficient: a `•` whose *scalar* is an application —
`(structureRingSheaf B S hS X).obj.map g.op a`, the restriction of a section along a chart
arrow — is still not resolved, while the same `•` with the scalar a local variable of the same
type is.  So `AlgebraicGeometry.Space.annihilatedByKerIdeal_conormalIdealQuotient` abstracts the
restricted section as a bound variable `b` ranging over the sections of `𝒪_X` over the chart,
carrying only the hypothesis that `b` lies in `𝓘` there, and instantiates it at the very end
through `PresheafOfModules.map_smul`.  Its target section is abstracted the same way, which also
keeps the statement off the restriction-of-scalars spelling
`(ModuleCat.restrictScalars _).obj _` that `PresheafOfModules.map` returns.

**Why quasi-coherence is unconditional now.**  The ideal sheaf of a closed immersion is
quasi-coherent because a closed immersion is quasi-compact
(`AlgebraicGeometry.Space.isQuasiCompact_of_isClosedImmersion'`) and the kernel of the structure
map of a quasi-compact morphism is quasi-coherent
(`AlgebraicGeometry.Space.isQuasicoherentOnSite_kernelIdealSheaf`, Stacks 082Z), and the inverse
image of a quasi-coherent module along an arbitrary morphism of algebraic spaces is
quasi-coherent, which is Stacks 03GA
(`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite`).
Earlier notes in this tree said that quasi-coherence of the conormal module needed Stacks 03DO,
part (6) as a hypothesis; Stacks 03GA has since been proved here and supersedes that.

**The general immersion.**  The factorisation of an immersion as a closed immersion into the
complement of the boundary of its image is
`AlgebraicGeometry.Space.immersionClosedFactorization`, built in
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalAlgebra.lean` from Stacks 04CE as a canonical
morphism rather than a chosen one, so the conormal module of an immersion below involves no
choice.  It is the degree-one piece of
`AlgebraicGeometry.Space.conormalAlgebraOfImmersion`, the conormal algebra of Stacks 09RN.

## References

* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN)
* [Stacks Project, Tag 04CE](https://stacks.math.columbia.edu/tag/04CE)
* [Stacks Project, Tag 04CJ](https://stacks.math.columbia.edu/tag/04CJ)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 082Z](https://stacks.math.columbia.edu/tag/082Z)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 09RN](https://stacks.math.columbia.edu/tag/09RN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v₁ u₁ u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **`𝒪_F`-modules with sections in the universe of the schemes form an abelian category.**
This is Mathlib's `SheafOfModules.instAbelian`, restated so that the module universe is pinned
by the statement: left to itself, instance search reaches a candidate stated at the module
universe `max (u + 1) m` first and gets stuck on the universe constraint rather than
backtracking.  `AlgebraicGeometry.Space.spaceModulesAbelian` of
`StacksFrontier/AlgebraicGeometry/Spaces/CoherentDevissageFiltration.lean` is the same workaround
as an abbreviation; this one is a `local instance` because the cokernel below is formed in term
mode, where there is no `let` to hang it on. -/
local instance abelianModulesSmallEtale (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) : Abelian (Modules.{u, u} B S hS F hF) :=
  SheafOfModules.instAbelian _

section ClosedImmersion

variable {Z X : AlgebraicSpaces B S hS}

/-! ### The conormal module of a morphism, and its quasi-coherence -/

/-- **The conormal module of a morphism of algebraic spaces**: the inverse image along
`i : Z ⟶ X` of the kernel ideal sheaf `𝓘 = Ker(𝒪_X ⟶ i_*𝒪_Z)` of `i`.

For a closed immersion this is the conormal module `𝒞_{Z/X}` of Stacks 04CN; the identification
with the `𝓘/𝓘²` of the source is `AlgebraicGeometry.Space.conormalIdealQuotientIso` below.  No
hypothesis is imposed on `i`, exactly as for the conormal algebra
`AlgebraicGeometry.Space.conormalAlgebra` of which this is the degree-one piece. -/
def conormalModuleOfHom (i : Z ⟶ X) : Modules.{u, u} B S hS Z.1 Z.2 :=
  (modulePullback B S hS i).obj (kernelIdealSheaf B S hS i).toSheafOfModules

/-- The conormal module of a morphism is the degree-one piece of its conormal algebra. -/
theorem conormalModuleOfHom_eq_conormalAlgebra_piece_one (i : Z ⟶ X) :
    conormalModuleOfHom B S hS i = (conormalAlgebra B S hS i).piece 1 :=
  (conormalAlgebra_piece_one B S hS i).symm

/-- For the inclusion of a closed subspace the conormal module of the morphism is the conormal
module `AlgebraicGeometry.Space.conormalModule` of the subspace: the kernel ideal sheaf of the
inclusion is the defining ideal sheaf of the subspace. -/
theorem conormalModuleOfHom_eq_conormalModule (Y : AlgebraicSpaces B S hS)
    (W : ClosedSubspaces B S hS Y.1) :
    conormalModuleOfHom B S hS (subspaceInclusion B S hS Y W) = conormalModule B S hS Y W :=
  rfl

/-- **The quasi-coherence clause of Stacks 04CN for a closed immersion, unconditionally.**  The
kernel ideal sheaf of a quasi-compact morphism is quasi-coherent (Stacks 082Z) and a closed
immersion is quasi-compact, and the inverse image of a quasi-coherent module is quasi-coherent
(Stacks 03GA). -/
theorem isQuasicoherentOnSite_conormalModuleOfHom (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) :
    (conormalModuleOfHom B S hS i).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS i _
    (isQuasicoherentOnSite_kernelIdealSheaf B S hS i
      (isQuasiCompact_of_isClosedImmersion' B S hS hi))

/-- **The quasi-coherence clause of Stacks 04CN for a closed subspace, unconditionally.**  This
discharges the hypothesis `h03DO` of
`AlgebraicGeometry.Space.isQuasicoherentOnSite_conormalModule_of_h03DO`. -/
theorem isQuasicoherentOnSite_conormalModule (Y : AlgebraicSpaces B S hS)
    (W : ClosedSubspaces B S hS Y.1) :
    (conormalModule B S hS Y W).IsQuasicoherentOnSite :=
  conormalModuleOfHom_eq_conormalModule B S hS Y W ▸
    isQuasicoherentOnSite_conormalModuleOfHom B S hS (subspaceInclusion B S hS Y W) W.2.2

/-! ### The ideal square and the quotient `𝓘/𝓘²` -/

/-- The kernel ideal sheaf `𝓘` of a morphism of algebraic spaces, as an `𝒪_X`-module. -/
abbrev kernelIdealModule (i : Z ⟶ X) : Modules.{u, u} B S hS X.1 X.2 :=
  (kernelIdealSheaf B S hS i).toSheafOfModules

/-- The square of the ideal of sections of `𝓘` over an étale chart is the product of that ideal
with itself. -/
theorem idealAt_sq_eq_mul (i : Z ⟶ X) (U : (SmallEtale B S hS X.1)ᵒᵖ) :
    SheafOfModules.idealAt (kernelIdealSheaf B S hS i) U ^ 2 =
      SheafOfModules.idealAt (kernelIdealSheaf B S hS i) U *
        SheafOfModules.idealAt (kernelIdealSheaf B S hS i) U := by
  have h2 : (2 : ℕ) = 1 + 1 := rfl
  rw [h2, Submodule.pow_succ, Submodule.pow_one]

/-- **The ideal square `𝓘²` is contained in `𝓘`.** -/
theorem idealSheafPow_two_le_kernelIdealSheaf (i : Z ⟶ X) :
    SheafOfModules.idealSheafPow (kernelIdealSheaf B S hS i) 2 ≤ kernelIdealSheaf B S hS i := by
  have h : SheafOfModules.idealSheafPow (kernelIdealSheaf B S hS i) 2 ≤
      SheafOfModules.idealSheafPow (kernelIdealSheaf B S hS i) 1 :=
    SheafOfModules.idealSheafPow_antitone (kernelIdealSheaf B S hS i) (by norm_num)
  rwa [SheafOfModules.idealSheafPow_one] at h

/-- **The ideal square `𝓘²`**, as an `𝒪_X`-module: the second power of the kernel ideal sheaf of
`i : Z ⟶ X`, in the family of powers from which the conormal algebra of Stacks 09RN is built. -/
abbrev conormalIdealSquareModule (i : Z ⟶ X) : Modules.{u, u} B S hS X.1 X.2 :=
  (SheafOfModules.idealSheafPow (kernelIdealSheaf B S hS i) 2).toSheafOfModules

/-- **The inclusion `𝓘² ⟶ 𝓘`.** -/
abbrev conormalIdealSquareι (i : Z ⟶ X) :
    conormalIdealSquareModule B S hS i ⟶ kernelIdealModule B S hS i :=
  Stacks.SheafOfModules.Submodule.homOfLE (idealSheafPow_two_le_kernelIdealSheaf B S hS i)



/-- The inclusion `𝓘² ⟶ 𝓘` is the identity on underlying sections. -/
theorem conormalIdealSquareι_val_app (i : Z ⟶ X) (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (z : (conormalIdealSquareModule B S hS i).val.obj U) :
    (conormalIdealSquareι B S hS i).val.app U z =
      ⟨z.1, idealSheafPow_two_le_kernelIdealSheaf B S hS i U z.2⟩ :=
  rfl

/-- **The `𝒪_X`-module `𝓘/𝓘²`** of a morphism `i : Z ⟶ X` of algebraic spaces: the cokernel of
the inclusion of the ideal square into the kernel ideal sheaf of `i`. -/
def conormalIdealQuotient (i : Z ⟶ X) : Modules.{u, u} B S hS X.1 X.2 :=
  cokernel (C := Modules.{u, u} B S hS X.1 X.2) (conormalIdealSquareι B S hS i)

/-- The projection `𝓘 ⟶ 𝓘/𝓘²`. -/
def conormalIdealQuotientπ (i : Z ⟶ X) :
    kernelIdealModule B S hS i ⟶ conormalIdealQuotient B S hS i :=
  cokernel.π _

/-- The projection `𝓘 ⟶ 𝓘/𝓘²` is an epimorphism. -/
instance epi_conormalIdealQuotientπ (i : Z ⟶ X) : Epi (conormalIdealQuotientπ B S hS i) :=
  inferInstanceAs (Epi (cokernel.π _))

/-- The sections of `𝓘²` die in `𝓘/𝓘²`. -/
@[reassoc]
theorem conormalIdealSquareι_comp_conormalIdealQuotientπ (i : Z ⟶ X) :
    conormalIdealSquareι B S hS i ≫ conormalIdealQuotientπ B S hS i = 0 :=
  cokernel.condition _

/-- A section of `𝓘` lying in `𝓘²` dies in `𝓘/𝓘²`. -/
theorem conormalIdealQuotientπ_apply_eq_zero (i : Z ⟶ X) (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (z : (kernelIdealModule B S hS i).val.obj U)
    (hz : (z.1 : ToType ((structureRingSheaf B S hS X).obj.obj U)) ∈
      SheafOfModules.idealAt (SheafOfModules.idealSheafPow (kernelIdealSheaf B S hS i) 2) U) :
    (conormalIdealQuotientπ B S hS i).val.app U z = 0 :=
  Stacks.SheafOfModules.val_app_apply_eq_zero (conormalIdealSquareι B S hS i)
    (conormalIdealQuotientπ B S hS i)
    (conormalIdealSquareι_comp_conormalIdealQuotientπ B S hS i) U
    (⟨z.1, hz⟩ : (conormalIdealSquareModule B S hS i).val.obj U)

/-! ### A map out of `𝓘` into an annihilated module kills `𝓘²` -/

/-- A section of `𝓘` whose value is a sum of products of two sections of `𝓘` is killed by every
`𝒪_X`-linear map into a module annihilated by `𝓘`: the map is `𝒪_X`-linear and the first factor
of each product acts as zero on the target. -/
theorem app_apply_eq_zero_of_mem_idealAt_mul (i : Z ⟶ X)
    {M : Modules.{u, u} B S hS X.1 X.2} (hM : AnnihilatedByKerIdeal B S hS i M)
    (φ : kernelIdealModule B S hS i ⟶ M) (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (w : ToType ((structureRingSheaf B S hS X).obj.obj U))
    (hw : w ∈ SheafOfModules.idealAt (kernelIdealSheaf B S hS i) U *
      SheafOfModules.idealAt (kernelIdealSheaf B S hS i) U)
    (hw' : w ∈ SheafOfModules.idealAt (kernelIdealSheaf B S hS i) U) :
    φ.val.app U (⟨w, hw'⟩ : (kernelIdealModule B S hS i).val.obj U) = 0 := by
  let _ : Module ((structureRingSheaf B S hS X).obj.obj U) (M.val.obj U) :=
    (M.val.obj U).isModule
  have key : ∀ v ∈ SheafOfModules.idealAt (kernelIdealSheaf B S hS i) U *
      SheafOfModules.idealAt (kernelIdealSheaf B S hS i) U,
      v ∈ SheafOfModules.idealAt (kernelIdealSheaf B S hS i) U ∧
        ∀ hv : v ∈ SheafOfModules.idealAt (kernelIdealSheaf B S hS i) U,
          φ.val.app U (⟨v, hv⟩ : (kernelIdealModule B S hS i).val.obj U) = 0 := by
    intro v hv
    refine Submodule.mul_induction_on hv (fun a ha b hb => ⟨Ideal.mul_mem_left _ a hb, ?_⟩)
      (fun x y hx hy => ⟨add_mem hx.1 hy.1, ?_⟩)
    · intro hab
      have hsm : (⟨a * b, hab⟩ : (kernelIdealModule B S hS i).val.obj U) =
          a • (⟨b, hb⟩ : (kernelIdealModule B S hS i).val.obj U) :=
        Subtype.ext rfl
      have hlin : φ.val.app U (a • (⟨b, hb⟩ : (kernelIdealModule B S hS i).val.obj U)) =
          a • φ.val.app U (⟨b, hb⟩ : (kernelIdealModule B S hS i).val.obj U) :=
        (φ.val.app U).hom.map_smul a _
      rw [hsm, hlin]
      exact hM U a ((SheafOfModules.mem_kerIdeal _ U a).2 ha) _
    · intro hxy
      have hadd : (⟨x + y, hxy⟩ : (kernelIdealModule B S hS i).val.obj U) =
          (⟨x, hx.1⟩ : (kernelIdealModule B S hS i).val.obj U) +
            (⟨y, hy.1⟩ : (kernelIdealModule B S hS i).val.obj U) :=
        Subtype.ext rfl
      have hmapadd : φ.val.app U
            ((⟨x, hx.1⟩ : (kernelIdealModule B S hS i).val.obj U) +
              (⟨y, hy.1⟩ : (kernelIdealModule B S hS i).val.obj U)) =
          φ.val.app U (⟨x, hx.1⟩ : (kernelIdealModule B S hS i).val.obj U) +
            φ.val.app U (⟨y, hy.1⟩ : (kernelIdealModule B S hS i).val.obj U) :=
        (φ.val.app U).hom.map_add _ _
      rw [hadd, hmapadd, hx.2 hx.1, hy.2 hy.1, add_zero]
  exact (key w hw).2 hw'

/-- **An `𝒪_X`-linear map out of `𝓘` into a module annihilated by `𝓘` kills `𝓘²`, on sections.**

A section of `𝓘²` restricts, along the arrows of a covering sieve, to an honest sum of products
of two sections of `𝓘`, where
`AlgebraicGeometry.Space.app_apply_eq_zero_of_mem_idealAt_mul` applies; the target is a
sheaf, so a section killed locally is killed. -/
theorem app_apply_conormalIdealSquareι_eq_zero (i : Z ⟶ X)
    {M : Modules.{u, u} B S hS X.1 X.2} (hM : AnnihilatedByKerIdeal B S hS i M)
    (φ : kernelIdealModule B S hS i ⟶ M) (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (z : (conormalIdealSquareModule B S hS i).val.obj U) :
    φ.val.app U ((conormalIdealSquareι B S hS i).val.app U z) = 0 := by
  rw [conormalIdealSquareι_val_app]
  refine Stacks.SheafOfModules.eq_zero_of_locally_eq_zero _ z.2 fun {W} g hg => ?_
  have hnat : M.val.map g.op (φ.val.app U
        (⟨z.1, idealSheafPow_two_le_kernelIdealSheaf B S hS i U z.2⟩ :
          (kernelIdealModule B S hS i).val.obj U)) =
      φ.val.app (op W) ((kernelIdealModule B S hS i).val.map g.op
        (⟨z.1, idealSheafPow_two_le_kernelIdealSheaf B S hS i U z.2⟩ :
          (kernelIdealModule B S hS i).val.obj U)) :=
    (PresheafOfModules.naturality_apply φ.val g.op _).symm
  rw [hnat]
  exact app_apply_eq_zero_of_mem_idealAt_mul B S hS i hM φ (op W)
    (((structureRingSheaf B S hS X).obj.map g.op).hom z.1)
    ((idealAt_sq_eq_mul B S hS i (op W)).le hg)
    (SheafOfModules.map_mem_idealAt g.op
      (idealSheafPow_two_le_kernelIdealSheaf B S hS i U z.2))

/-- **An `𝒪_X`-linear map out of `𝓘` into a module annihilated by `𝓘` kills `𝓘²`.** -/
theorem conormalIdealSquareι_comp_eq_zero (i : Z ⟶ X)
    {M : Modules.{u, u} B S hS X.1 X.2} (hM : AnnihilatedByKerIdeal B S hS i M)
    (φ : kernelIdealModule B S hS i ⟶ M) :
    conormalIdealSquareι B S hS i ≫ φ = 0 := by
  refine (SheafOfModules.forget _).map_injective ?_
  rw [Functor.map_zero]
  refine PresheafOfModules.hom_ext fun U => ?_
  refine ModuleCat.hom_ext (LinearMap.ext fun z => ?_)
  exact app_apply_conormalIdealSquareι_eq_zero B S hS i hM φ U z

/-! ### `𝓘/𝓘²` is annihilated by `𝓘` -/

/-- **The quotient `𝓘/𝓘²` is annihilated by `𝓘`.**

A section of `𝓘/𝓘²` is locally the image of a section `t` of `𝓘`, and for a section `a` of `𝓘`
the product `a · t` lies in `𝓘²`, hence dies in the quotient; the quotient is a sheaf, so a
section killed locally is killed. -/
theorem annihilatedByKerIdeal_conormalIdealQuotient (i : Z ⟶ X) :
    AnnihilatedByKerIdeal B S hS i (conormalIdealQuotient B S hS i) := by
  intro U a ha m
  let _ : Module ((structureRingSheaf B S hS X).obj.obj U)
      ((conormalIdealQuotient B S hS i).val.obj U) :=
    ((conormalIdealQuotient B S hS i).val.obj U).isModule
  obtain ⟨T, hT, hsec⟩ := Stacks.SheafOfModules.EpiMono.exists_covering_of_epi
    (conormalIdealQuotientπ B S hS i) m
  refine Stacks.SheafOfModules.eq_zero_of_locally_eq_zero _ hT fun {W} g hg => ?_
  let _ : Module ((structureRingSheaf B S hS X).obj.obj (op W))
      ((kernelIdealModule B S hS i).val.obj (op W)) :=
    ((kernelIdealModule B S hS i).val.obj (op W)).isModule
  let _ : Module ((structureRingSheaf B S hS X).obj.obj (op W))
      ((conormalIdealQuotient B S hS i).val.obj (op W)) :=
    ((conormalIdealQuotient B S hS i).val.obj (op W)).isModule
  have key : ∀ b : (structureRingSheaf B S hS X).obj.obj (op W),
      b ∈ SheafOfModules.idealAt (kernelIdealSheaf B S hS i) (op W) →
      ∀ (t : (kernelIdealModule B S hS i).val.obj (op W))
        (y : (conormalIdealQuotient B S hS i).val.obj (op W)),
      (conormalIdealQuotientπ B S hS i).val.app (op W) t = y → b • y = 0 := by
    rintro b hc t _ rfl
    exact (((conormalIdealQuotientπ B S hS i).val.app (op W)).hom.map_smul b t).symm.trans
      (conormalIdealQuotientπ_apply_eq_zero B S hS i (op W) (b • t)
        (SheafOfModules.mem_idealSheafPow_of_mem_pow (kernelIdealSheaf B S hS i) 2
          ((idealAt_sq_eq_mul B S hS i (op W)).ge (Submodule.mul_mem_mul hc t.2))))
  obtain ⟨t, ht⟩ := hsec g hg
  exact ((conormalIdealQuotient B S hS i).val.map_smul g.op a m).trans
    (key _ (SheafOfModules.map_mem_idealAt g.op ((SheafOfModules.mem_kerIdeal _ U a).1 ha))
      t _ ht)

/-! ### The identification `𝓘/𝓘² ≅ i_*𝒞_{Z/X}` -/

/-- The unit `𝓘 ⟶ i_*i^*𝓘 = i_*𝒞_{Z/X}` of the adjunction of Stacks 03LU at the kernel ideal
sheaf.  This is the map `𝓘 ⟶ 𝓘/𝓘²` of Stacks 76.5, read through the identification below. -/
abbrev conormalUnit (i : Z ⟶ X) :
    kernelIdealModule B S hS i ⟶
      (modulePushforward B S hS i).obj (conormalModuleOfHom B S hS i) :=
  (modulePullbackAdjunction B S hS i).unit.app (kernelIdealModule B S hS i)

/-- **The unit `𝓘 ⟶ i_*𝒞_{Z/X}` of a closed immersion is an epimorphism.** -/
theorem epi_conormalUnit (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom) :
    Epi (conormalUnit B S hS i) :=
  epi_modulePullbackAdjunction_unit_of_essImage_of_annihilated B S hS i hi
    (fun M hM => essImage_modulePushforward_of_annihilatedByKerIdeal B S hS i hi M hM) _

/-- **The canonical map `𝓘/𝓘² ⟶ i_*𝒞_{Z/X}`**, induced by the unit of `i^* ⊣ i_*`: the unit
kills `𝓘²` because its target is annihilated by `𝓘`. -/
def conormalIdealQuotientToPushforward (i : Z ⟶ X) :
    conormalIdealQuotient B S hS i ⟶
      (modulePushforward B S hS i).obj (conormalModuleOfHom B S hS i) :=
  cokernel.desc _ (conormalUnit B S hS i)
    (conormalIdealSquareι_comp_eq_zero B S hS i
      (annihilatedByKerIdeal_modulePushforward B S hS i (conormalModuleOfHom B S hS i)) _)

/-- The canonical map is the one the unit factors through. -/
@[reassoc]
theorem conormalIdealQuotientπ_comp_toPushforward (i : Z ⟶ X) :
    conormalIdealQuotientπ B S hS i ≫ conormalIdealQuotientToPushforward B S hS i =
      conormalUnit B S hS i :=
  cokernel.π_desc _ _ _

/-- **The unit is an isomorphism at `𝓘/𝓘²`.**  The quotient is annihilated by `𝓘`, hence lies in
the essential image of the direct image along a closed immersion (Stacks 08KS), and the direct
image is fully faithful (Stacks 04CJ, part (2)). -/
theorem isIso_unit_conormalIdealQuotient (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom) :
    IsIso ((modulePullbackAdjunction B S hS i).unit.app (conormalIdealQuotient B S hS i)) := by
  have hff := fullyFaithfulModulePushforward B S hS i hi
  have := hff.full
  have := hff.faithful
  exact (modulePullbackAdjunction B S hS i).isIso_unit_app_iff_mem_essImage.2
    (essImage_modulePushforward_of_annihilatedByKerIdeal B S hS i hi _
      (annihilatedByKerIdeal_conormalIdealQuotient B S hS i))

/-- **The canonical map `𝓘/𝓘² ⟶ i_*𝒞_{Z/X}` is a split monomorphism.**  Naturality of the unit
at the projection `π : 𝓘 ⟶ 𝓘/𝓘²` gives a retraction after `π` is cancelled, which is legitimate
because `π` is an epimorphism. -/
theorem isSplitMono_conormalIdealQuotientToPushforward (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) :
    IsSplitMono (conormalIdealQuotientToPushforward B S hS i) := by
  have hiso := isIso_unit_conormalIdealQuotient B S hS i hi
  refine IsSplitMono.mk' ⟨(modulePushforward B S hS i).map
      ((modulePullback B S hS i).map (conormalIdealQuotientπ B S hS i)) ≫
      inv ((modulePullbackAdjunction B S hS i).unit.app
        (conormalIdealQuotient B S hS i)), ?_⟩
  have hnat : conormalUnit B S hS i ≫ (modulePushforward B S hS i).map
        ((modulePullback B S hS i).map (conormalIdealQuotientπ B S hS i)) =
      conormalIdealQuotientπ B S hS i ≫
        (modulePullbackAdjunction B S hS i).unit.app (conormalIdealQuotient B S hS i) :=
    ((modulePullbackAdjunction B S hS i).unit.naturality
      (conormalIdealQuotientπ B S hS i)).symm
  refine (cancel_epi (conormalIdealQuotientπ B S hS i)).1 ?_
  rw [Category.comp_id, ← Category.assoc, conormalIdealQuotientπ_comp_toPushforward,
    ← Category.assoc, hnat, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-- **Stacks 04CN, the identification with `𝓘/𝓘²`.**  For a closed immersion `i : Z ⟶ X` of
algebraic spaces the canonical map induced by the unit of `i^* ⊣ i_*` is an isomorphism

`𝓘/𝓘² ≅ i_*𝒞_{Z/X}`,

so the `𝒪_Z`-module `𝒞_{Z/X} = i^*𝓘` of `AlgebraicGeometry.Space.conormalModuleOfHom` is the one
Stacks 76.5 describes as `𝓘/𝓘²`.  The characterising property is
`AlgebraicGeometry.Space.conormalIdealQuotientπ_comp_toPushforward`: composed with the
projection `𝓘 ⟶ 𝓘/𝓘²` it is the unit. -/
@[stacks 04CN "the identification of the conormal module with 𝓘/𝓘², for a closed immersion"]
def conormalIdealQuotientIso (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom) :
    conormalIdealQuotient B S hS i ≅
      (modulePushforward B S hS i).obj (conormalModuleOfHom B S hS i) :=
  have hepi : Epi (conormalIdealQuotientToPushforward B S hS i) := by
    have hcomp : Epi (conormalIdealQuotientπ B S hS i ≫
        conormalIdealQuotientToPushforward B S hS i) := by
      rw [conormalIdealQuotientπ_comp_toPushforward]
      exact epi_conormalUnit B S hS i hi
    exact epi_of_epi (conormalIdealQuotientπ B S hS i) _
  have : Mono (conormalIdealQuotientToPushforward B S hS i) :=
    (isSplitMono_conormalIdealQuotientToPushforward B S hS i hi).mono
  have : IsIso (conormalIdealQuotientToPushforward B S hS i) :=
    isIso_of_mono_of_epi (C := Modules.{u, u} B S hS X.1 X.2)
      (conormalIdealQuotientToPushforward B S hS i)
  asIso (conormalIdealQuotientToPushforward B S hS i)

/-- The isomorphism of Stacks 04CN is the canonical map, so its characterisation applies to
it. -/
theorem conormalIdealQuotientIso_hom (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom) :
    (conormalIdealQuotientIso B S hS i hi).hom =
      conormalIdealQuotientToPushforward B S hS i :=
  rfl

end ClosedImmersion

/-! ### The conormal sheaf of a general immersion -/

section Immersion

attribute [local instance] pointTopology

variable {Z₀ X₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The conormal sheaf `AlgebraicGeometry.Space.conormalModuleOfImmersion` of an immersion is the
conormal module of its closed factorisation `Z ⟶ X ∖ ∂Z` of Stacks 04CE: the kernel ideal sheaf
of that closed immersion is the defining ideal sheaf of its image. -/
theorem conormalModuleOfImmersion_eq_conormalModuleOfHom (hX : IsAlgebraicSpace B S hS X₀)
    (hZ : IsAlgebraicSpace B S hS Z₀) (i : Z₀ ⟶ X₀) (hi : IsImmersion B S hS i) :
    conormalModuleOfImmersion B S hS hX hZ i hi =
      conormalModuleOfHom B S hS (immersionClosedFactorization B S hS hX hZ i hi) := by
  rw [conormalModuleOfHom, kernelIdealSheaf_immersionClosedFactorization]
  exact conormalModuleOfImmersion_eq B S hS hX hZ i hi

/-- **The quasi-coherence clause of Stacks 04CN for an arbitrary immersion**, unconditionally:
the closed factorisation of Stacks 04CE is a closed immersion, where
`AlgebraicGeometry.Space.isQuasicoherentOnSite_conormalModuleOfHom` applies.

The definition of the source calls `𝒞_{Z/X}` *the quasi-coherent `𝒪_Z`-module* `𝓘/𝓘²`; this is
that clause of the definition, which `AlgebraicGeometry.Space.conormalModuleOfImmersion` — being
a definition — cannot itself state. -/
@[stacks 04CN "the conormal sheaf is a quasi-coherent module"]
theorem isQuasicoherentOnSite_conormalModuleOfImmersion (hX : IsAlgebraicSpace B S hS X₀)
    (hZ : IsAlgebraicSpace B S hS Z₀) (i : Z₀ ⟶ X₀) (hi : IsImmersion B S hS i) :
    (conormalModuleOfImmersion B S hS hX hZ i hi).IsQuasicoherentOnSite := by
  rw [conormalModuleOfImmersion_eq_conormalModuleOfHom]
  exact isQuasicoherentOnSite_conormalModuleOfHom B S hS
    (immersionClosedFactorization B S hS hX hZ i hi)
    (isClosedImmersion_boundaryComplementLift B S hS hX hZ i hi)

/-- **Stacks 04CN, the identification with `𝓘/𝓘²` for an arbitrary immersion.**  For `𝓘` the
ideal sheaf of `Z` in the complement `X ∖ ∂Z` of the boundary of the image of `i`, the direct
image of the conormal sheaf along the closed factorisation of Stacks 04CE is canonically
`𝓘/𝓘²`. -/
def conormalIdealQuotientIsoOfImmersion (hX : IsAlgebraicSpace B S hS X₀)
    (hZ : IsAlgebraicSpace B S hS Z₀) (i : Z₀ ⟶ X₀) (hi : IsImmersion B S hS i) :
    conormalIdealQuotient B S hS (immersionClosedFactorization B S hS hX hZ i hi) ≅
      (modulePushforward B S hS (immersionClosedFactorization B S hS hX hZ i hi)).obj
        (conormalModuleOfImmersion B S hS hX hZ i hi) :=
  conormalIdealQuotientIso B S hS (immersionClosedFactorization B S hS hX hZ i hi)
      (isClosedImmersion_boundaryComplementLift B S hS hX hZ i hi) ≪≫
    eqToIso (congrArg
      (modulePushforward B S hS (immersionClosedFactorization B S hS hX hZ i hi)).obj
      (conormalModuleOfImmersion_eq_conormalModuleOfHom B S hS hX hZ i hi).symm)

/-- **Stacks Project, Tag 04CN.**  The *conormal sheaf* `𝒞_{Z/X}` of an immersion
`i : Z ⟶ X` of algebraic spaces over `S`, constructed as
`AlgebraicGeometry.Space.conormalModuleOfImmersion` through the closed immersion of `Z` into the
complement `X ∖ ∂Z` of the boundary of its image (Stacks 04CE), is the quasi-coherent
`𝒪_Z`-module `𝓘/𝓘²` of the source: it is quasi-coherent, and for `𝓘` the ideal sheaf of `Z` in
`X ∖ ∂Z` its direct image along that closed immersion is `𝓘/𝓘²`. -/
@[stacks 04CN]
theorem isQuasicoherentOnSite_and_nonempty_conormalIdealQuotientIso
    (hX : IsAlgebraicSpace B S hS X₀) (hZ : IsAlgebraicSpace B S hS Z₀) (i : Z₀ ⟶ X₀)
    (hi : IsImmersion B S hS i) :
    (conormalModuleOfImmersion B S hS hX hZ i hi).IsQuasicoherentOnSite ∧
      Nonempty (conormalIdealQuotient B S hS (immersionClosedFactorization B S hS hX hZ i hi) ≅
        (modulePushforward B S hS (immersionClosedFactorization B S hS hX hZ i hi)).obj
          (conormalModuleOfImmersion B S hS hX hZ i hi)) :=
  ⟨isQuasicoherentOnSite_conormalModuleOfImmersion B S hS hX hZ i hi,
    ⟨conormalIdealQuotientIsoOfImmersion B S hS hX hZ i hi⟩⟩

end Immersion

end AlgebraicGeometry.Space

end
