module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.Localization
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.StrictAdicRestrictionToAnOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerModule
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SubmoduleOver
public import StacksFrontier.CategoryTheory.Sites.Modules.IdealSubsheafLocal

/-!
# The product of a sheaf of ideals with a submodule commutes with restriction to a slice

Let `(𝒞, 𝒪)` be a ringed site, `ℐ ⊂ 𝒪` a sheaf of ideals, `ℳ` a sheaf of `𝒪`-modules, `𝒩 ⊆ ℳ` a
submodule and `V` an object of `𝒞`. This file proves

`(ℐ𝒩)|_V = (ℐ|_V)(𝒩|_V)` and `(ℐⁿ𝒩)|_V = (ℐ|_V)ⁿ(𝒩|_V)`,

as *equalities* of submodules of `ℳ|_V` rather than as isomorphisms.

`AlgebraicGeometry.RingedSite.overIdeal_idealPow` of `StrictAdicRestrictionToAnOpen.lean` is the
same statement for the powers of `ℐ` inside `𝒪`, and the proof here is the same argument with the
objectwise product in place of the objectwise power.

## Main results

* `AlgebraicGeometry.RingedSite.overSubmodule_idealSmul` — `(ℐ𝒩)|_V = (ℐ|_V)(𝒩|_V)`.
* `AlgebraicGeometry.RingedSite.overSubmodule_idealPowSmul` — `(ℐⁿ𝒩)|_V = (ℐ|_V)ⁿ(𝒩|_V)`.
* `AlgebraicGeometry.RingedSite.overSubmodule_top` — `⊤|_V = ⊤`, needed because the product the
  adic quotients are formed with is `ℐⁿ⊤`.
* `AlgebraicGeometry.RingedSite.cokernelOverSubmoduleIso`, with
  `π_comp_cokernelOverSubmoduleIso` and the `OfEq` combinator — **restriction commutes with the
  quotient by a submodule**, compatibly with the quotient projections. Together with the
  equalities above this is the term-level identification of the restriction of an adic quotient
  with the slice's own.

## Implementation notes

`Stacks.Sites.idealSmul` is the local-membership closure
`Stacks.SheafOfModules.sheafifySubmodule` of the objectwise product, so neither inclusion is
objectwise. The easy one is the closure's universal property
(`Stacks.SheafOfModules.sheafifySubmodule_le`): a product of a section of `ℐ|_V` over `W` with a
section of `𝒩|_V` over `W` is, by definition of the restriction, a product of a section of `ℐ`
over `W.left` with a section of `𝒩` over `W.left`, hence a section of `ℐ𝒩` there, hence a section
of `(ℐ𝒩)|_V` over `W`.

The other needs the local description `Stacks.SheafOfModules.mem_sheafifySubmodule_iff`: a
section of `(ℐ𝒩)|_V` over `W` is a section of `ℐ𝒩` over `W.left`, so it lies in the objectwise
product along a covering sieve of `W.left`; that sieve pulls back to a covering sieve of `W` for
the slice topology (`CategoryTheory.GrothendieckTopology.overEquiv_symm_mem_over`), and along it
the section lies in the objectwise product of the restrictions, which is the same objectwise
product read at `W.left`.

The powers follow by `AlgebraicGeometry.RingedSite.overIdeal_idealPow`, since
`Stacks.Sites.idealPowSmul ℐ n 𝒩` is `Stacks.Sites.idealSmul (Stacks.Sites.idealPow ℐ n) 𝒩` by
definition. The composite is `Eq.trans`ed rather than rewritten: `(X.over V).O`'s sheaf of rings
and `(Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V` are definitionally but not reducibly
equal, so a goal mentioning both is not type-correct at the transparency `rw` builds its motive at
— the same obstruction the implementation notes of `StrictAdicRestrictionToAnOpen.lean` record.

## References

* [Stacks Project, Tag 0942](https://stacks.math.columbia.edu/tag/0942)
* [Stacks Project, Tag 03DI](https://stacks.math.columbia.edu/tag/03DI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

variable (X : RingedSite.{u, u, u}) (V : X.C)
  [HasWeakSheafify (X.J.over V) AddCommGrpCat.{u}]
  [(X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [HasWeakSheafify (X.J.over V) AddCommGrpCat.{u}]
  [(X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The largest submodule restricts to the largest submodule.** -/
theorem overSubmodule_top {M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))} :
    (⊤ : M.Submodule).over V = ⊤ :=
  top_unique (SheafOfModules.Submodule.le_iff.2 fun _ s _ =>
    Stacks.SheafOfModules.mem_top_obj (M := M) s)

variable (I : SheafOfModules.Submodule
    (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
  {M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))} (N : M.Submodule)

omit [HasWeakSheafify (X.J.over V) AddCommGrpCat.{u}]
  [(X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The product of a sheaf of ideals with a submodule commutes with restriction to a slice
site**: `(ℐ𝒩)|_V = (ℐ|_V)(𝒩|_V)`. -/
theorem overSubmodule_idealSmul :
    (Stacks.Sites.idealSmul (O := X.O) I N).over V =
      Stacks.Sites.idealSmul (O := (X.over V).O) (overIdeal I V) (N.over V) :=
  le_antisymm
    (SheafOfModules.Submodule.le_iff.2 fun W s hs => by
      obtain ⟨S, hS, hx⟩ :=
        Stacks.SheafOfModules.exists_sieve_of_mem_sheafifySubmodule (N :=
          Stacks.Sites.presheafIdealSmul (O := X.O) I N.toSubmodule) hs
      exact Stacks.SheafOfModules.mem_sheafifySubmodule_of_mem
        (X.J.overEquiv_symm_mem_over (unop W) S hS)
        fun W' f hf => hx f.left ((Sieve.overEquiv_symm_iff S f).1 hf))
    (Stacks.SheafOfModules.sheafifySubmodule_le
      (Stacks.Sites.presheafIdealSmul_le (O := (X.over V).O) (overIdeal I V)
        fun _ _ ha _ hz => Stacks.Sites.smul_mem_idealSmul (O := X.O) I ha hz))

omit [HasWeakSheafify (X.J.over V) AddCommGrpCat.{u}]
  [(X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The product of a power of a sheaf of ideals with a submodule commutes with restriction to a
slice site**: `(ℐⁿ𝒩)|_V = (ℐ|_V)ⁿ(𝒩|_V)`. -/
theorem overSubmodule_idealPowSmul (n : ℕ) :
    (Stacks.Sites.idealPowSmul (O := X.O) I n N).over V =
      Stacks.Sites.idealPowSmul (O := (X.over V).O) (overIdeal I V) n (N.over V) :=
  (overSubmodule_idealSmul X V (Stacks.Sites.idealPow (O := X.O) I n) N).trans
    (congrArg (fun K => Stacks.Sites.idealSmul (O := (X.over V).O) K (N.over V))
      (overIdeal_idealPow X V I n))

/-! ### The quotient by a submodule, restricted -/

/-- **Restriction to a slice commutes with the quotient by a submodule of an arbitrary sheaf of
modules.** `AlgebraicGeometry.RingedSite.cokernelOverIso` of `StrictAdicRestrictionToAnOpen.lean`
is the same statement for a submodule of the structure sheaf; restriction preserves colimits, so
the proof is the same. -/
def cokernelOverSubmoduleIso :
    (restrictModulesToSlice X V).obj (cokernel N.ι) ≅ cokernel ((N.over V).ι) :=
  PreservesCokernel.iso (restrictModulesToSlice X V) N.ι

/-- The identification of the restricted quotient respects the quotient projections. -/
@[reassoc]
theorem π_comp_cokernelOverSubmoduleIso :
    (restrictModulesToSlice X V).map (cokernel.π N.ι) ≫ (cokernelOverSubmoduleIso X V N).hom =
      cokernel.π ((N.over V).ι) :=
  PreservesCokernel.π_iso_hom _ _

variable {N}
variable {N' : ((restrictModulesToSlice X V).obj M).Submodule}

/-- `AlgebraicGeometry.RingedSite.cokernelOverSubmoduleIso` with the restricted submodule named by
an equation, which is how a consumer meets it: the submodule downstairs is presented not as a
literal restriction but as something *equal* to one. -/
def cokernelOverSubmoduleIsoOfEq (h : N.over V = N') :
    (restrictModulesToSlice X V).obj (cokernel N.ι) ≅ cokernel N'.ι :=
  h ▸ cokernelOverSubmoduleIso X V N

/-- At the restricted submodule itself the comparison is
`AlgebraicGeometry.RingedSite.cokernelOverSubmoduleIso`. -/
theorem cokernelOverSubmoduleIsoOfEq_rfl :
    cokernelOverSubmoduleIsoOfEq X V (rfl : N.over V = N.over V) =
      cokernelOverSubmoduleIso X V N :=
  rfl

/-- The comparison for a presented submodule respects the quotient projections. -/
@[reassoc]
theorem π_comp_cokernelOverSubmoduleIsoOfEq (h : N.over V = N') :
    (restrictModulesToSlice X V).map (cokernel.π N.ι) ≫
        (cokernelOverSubmoduleIsoOfEq X V h).hom = cokernel.π N'.ι := by
  subst h
  exact π_comp_cokernelOverSubmoduleIso X V N

end AlgebraicGeometry.RingedSite

end
