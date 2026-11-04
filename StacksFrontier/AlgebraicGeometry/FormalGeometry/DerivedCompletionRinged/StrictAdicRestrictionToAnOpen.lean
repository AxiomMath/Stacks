module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.StrictAdicMilnorFibre
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.Localization
public import StacksFrontier.CategoryTheory.Sites.Modules.IdealSubsheafLocal
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.RestrictionNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.RestrictionSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.UnitCollapseComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CurryingNaturality

/-!
# The strict adic augmentation base-changed along restriction to an open

Let `(𝒞, 𝒪)` be a ringed site, `ℐ ⊂ 𝒪` a sheaf of ideals, `K̃` a complex of sheaves of modules
and `U` an object of `𝒞`. `StrictAdicQuotientTower.lean` builds the strict cone
`AlgebraicGeometry.RingedSite.strictAdicAugmentation` of [Stacks, Tag 0CQH] on the strictified
adic quotient tower `n ↦ Tot(K̃ ⊗_𝒪 (𝒪/ℐⁿ⁺¹)[0])`, and
`AlgebraicGeometry.RingedSite.quasiIso_strictAdicComparison_of_forall` reduces invertibility of
the comparison map it induces to invertibility of the comparison maps of the *base-changed*
cones `(strictAdicAugmentation X I K̃).map Gᵢ`. This file identifies that base change, for `Gᵢ`
the restriction to the slice site over `U`:

**the base change of the strict adic augmentation along restriction to an open is the strict
adic augmentation of the restricted data.**

So a chart-by-chart hypothesis about the strict adic comparison map — the same assertion one
site down — discharges the hypothesis of
`quasiIso_strictAdicComparison_of_forall`; that is
`AlgebraicGeometry.RingedSite.quasiIso_map_strictAdicAugmentation_augmentationMap`. No
exactness of countable products is used anywhere: the cone and the comparison map are formulas,
and only `Limits.HasProductsOfShape ℕ` is needed to write them down.

## Main definitions

* `AlgebraicGeometry.RingedSite.adicQuotientModuleOverIso` — `(𝒪/ℐⁿ)|_U ≅ 𝒪_U/(ℐ|_U)ⁿ`.
* `AlgebraicGeometry.RingedSite.adicQuotientTowerOverIso` and
  `strictAdicQuotientTowerOverIso` — the same over the tower, and after placing it in degree
  zero.
* `AlgebraicGeometry.RingedSite.strictAdicReductionTowerOverIso` — **the restriction of the
  strictified adic quotient tower of `K̃` is the strictified adic quotient tower of `K̃|_U` over
  the restricted ideal.**
* `AlgebraicGeometry.RingedSite.tensorComplexUnitOverIso` — the restriction comparison of
  `Tot(K̃ ⊗_𝒪 𝒪[0])`.

## Main results

* `AlgebraicGeometry.RingedSite.overIdeal_idealPow` — `(ℐⁿ)|_U = (ℐ|_U)ⁿ`.
* `AlgebraicGeometry.RingedSite.restrictComplexMap_tensorComplexUnitIsoFreeSections_inv` —
  **restriction commutes with the right unit law `Tot(K̃ ⊗_𝒪 𝒪[0]) ≅ K̃`.**
* `AlgebraicGeometry.RingedSite.map_strictAdicAugmentation_app` — **the base change of the
  strict adic augmentation along restriction is the strict adic augmentation of the restricted
  data**, at each map of the cone; the two sources agree on the nose.
* `AlgebraicGeometry.RingedSite.quasiIso_augmentationMap_of_iso` — invertibility of the
  comparison map of an augmented tower transports along an isomorphism of the augmented data.
* `AlgebraicGeometry.RingedSite.quasiIso_map_strictAdicAugmentation_augmentationMap` — **the
  hypothesis `hlocal` of `quasiIso_strictAdicComparison_of_forall`, at restriction to an open.**
* `AlgebraicGeometry.RingedSite.quasiIso_strictAdicComparison_of_forall_restrict` — **that
  consumer applied with restriction to a family of objects as the base change**, so that the
  only hypotheses left are the product comparison and the joint detection of
  quasi-isomorphisms.

## Implementation notes

Restriction commutes with the total tensor complex: that is
`AlgebraicGeometry.RingedSite.tensorComplexOverIso`, with its naturality in each variable in
`CategoryTheory/Sites/Cohomology/TensorComplex/RestrictionNaturality.lean`. This file proves the
same for the other factor of the tower and for the unit law of the cone:

* **the adic quotients.** `Stacks.Sites.idealPow` is the *sheafification* of the objectwise
  power, so `(ℐⁿ)|_U = (ℐ|_U)ⁿ` is not an objectwise identity: a section of `ℐⁿ` is only
  locally an `n`-fold product. The inclusion that needs an argument is proved from the local
  description `Stacks.SheafOfModules.mem_sheafifySubmodule_iff` of the sheafification together
  with `CategoryTheory.GrothendieckTopology.overEquiv_symm_mem_over`: a covering sieve of `V`
  pulls back to a covering sieve of `V ⟶ U` for the slice topology. Restriction is then pushed
  through the cokernel defining `𝒪/ℐⁿ` because it preserves colimits.
* **the right unit law** `Stacks.SheafOfModules.tensorComplexUnitIsoFreeSections`. Its
  compatibility with restriction is proved on sections, where both sides are formulas: the
  inverse unit law takes a section `w` to the pure tensor `w ⊗ 1`, the restriction comparison
  takes a pure tensor to the pure tensor of the restricted sections, and the identification of
  the restricted structure sheaf complex takes the unit section to the unit section on the nose.

**Two spellings, twice over.** The restriction lemmas of
`CategoryTheory/Sites/Cohomology/TensorComplex/` are stated at `X.O.over U`, while the
strict-tower API instantiated at the localized ringed site produces `(X.over U).O`; and
`AlgebraicGeometry.RingedSite.Modules` and the sheaves of modules over
`((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U` that the restriction functor is valued in
are a second such pair. Both crossings are
definitional and neither is reducible, so a goal mixing two spellings is not type-correct at
`implicit` transparency and no rewrite fires on it. Every chain below is therefore `Eq.trans`ed
with `congrArg` rather than rewritten, each statement names one spelling, and the few places
where two must meet are isolated into their own `rfl` lemmas
(`AlgebraicGeometry.RingedSite.map_strictAdicAugmentation_app_eq`,
`strictAdicAugmentation_app_over_eq`, `tensorComplexUnitOverIso_hom`).

**Why the cone identification is two declarations.** The heartbeat budget is per declaration,
and the single chain from the restricted cone map to the cone map of the slice exceeds it: each
step is cheap, but there are nine of them over terms as large as the bicomplex of a total
tensor complex.
`AlgebraicGeometry.RingedSite.restrictComplexMap_tensorComplex_map_strictAdicQuotientπ` is the
first half, split off for that reason alone.

## References

* [Stacks Project, Tag 0CQH](https://stacks.math.columbia.edu/tag/0CQH)
* [Stacks Project, Tag 0A0K](https://stacks.math.columbia.edu/tag/0A0K)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

/-! ### Restriction of the powers of a sheaf of ideals -/

variable (X : RingedSite.{u, u, u}) (U : X.C)
  [HasWeakSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [HasWeakSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **Restriction to a slice site commutes with the powers of a sheaf of ideals**:
`(ℐⁿ)|_U = (ℐ|_U)ⁿ`. -/
theorem overIdeal_idealPow
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) (n : ℕ) :
    overIdeal (Stacks.Sites.idealPow (O := X.O) I n) U =
      Stacks.Sites.idealPow (O := (X.over U).O) (overIdeal I U) n :=
  le_antisymm
    (SheafOfModules.Submodule.le_iff.2 fun V s hs => by
      obtain ⟨S, hS, hx⟩ :=
        Stacks.SheafOfModules.exists_sieve_of_mem_sheafifySubmodule (N :=
          Stacks.Sites.presheafIdealPow (O := X.O) I n) hs
      exact Stacks.SheafOfModules.mem_sheafifySubmodule_of_mem
        (X.J.overEquiv_symm_mem_over (unop V) S hS)
        fun W f hf => hx f.left ((Sieve.overEquiv_symm_iff S f).1 hf))
    (Stacks.Sites.idealPow_le (O := (X.over U).O) (overIdeal I U) n fun V =>
      Stacks.Sites.presheafIdealPow_le_idealPow (O := X.O) I n (op (unop V).left))

/-! ### Restriction of the quotient by a submodule -/

/-- Restriction of sheaves of modules to the slice site over `U`. This is the same functor as
`AlgebraicGeometry.RingedSite.restrictModules` of `Spaces/DerivedDuality/LocalCharts.lean`, kept
here so that this file does not import that module, whose global `HasDerivedCategory` instances
would override the `HasDerivedCategory.standard` models used in this directory. -/
abbrev restrictModulesToSlice : Modules X ⥤ Modules (X.over U) :=
  SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U

/-- Restriction of sheaves of modules to the slice site over `U` is additive. -/
instance additive_restrictModulesToSlice : (restrictModulesToSlice X U).Additive where
  map_add := by intros; rfl

/-- Restriction of sheaves of modules to the slice site over `U` preserves colimits. -/
instance preservesColimitsOfSize_restrictModulesToSlice :
    PreservesColimitsOfSize.{u, u} (restrictModulesToSlice X U) :=
  Stacks.SheafOfModules.pushforward_preservesColimits (J := X.J.over U) (K := X.J)
    (Over.forget U) (𝟙 (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U))

variable (N : SheafOfModules.Submodule
  (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))

/-- **Restriction commutes with the quotient by a submodule of the structure sheaf.** -/
def cokernelOverIso :
    (restrictModulesToSlice X U).obj (cokernel N.ι) ≅ cokernel ((overIdeal N U).ι) :=
  PreservesCokernel.iso (restrictModulesToSlice X U) N.ι

/-- The restriction of the projection onto `𝒪/N`, followed by
`AlgebraicGeometry.RingedSite.cokernelOverIso`, is the projection onto `𝒪_U/N|_U`. -/
@[reassoc]
theorem π_comp_cokernelOverIso :
    (restrictModulesToSlice X U).map (cokernel.π N.ι) ≫ (cokernelOverIso X U N).hom =
      cokernel.π ((overIdeal N U).ι) :=
  PreservesCokernel.π_iso_hom _ _

variable {N}
variable {N' : SheafOfModules.Submodule
  (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)))}

/-- `AlgebraicGeometry.RingedSite.cokernelOverIso` with the restricted submodule named by an
equation. -/
def cokernelOverIsoOfEq (h : overIdeal N U = N') :
    (restrictModulesToSlice X U).obj (cokernel N.ι) ≅ cokernel N'.ι :=
  h ▸ cokernelOverIso X U N

/-- The restriction of the projection onto `𝒪/N`, followed by
`AlgebraicGeometry.RingedSite.cokernelOverIsoOfEq`, is the projection onto `𝒪_U/N'`. -/
@[reassoc]
theorem π_comp_cokernelOverIsoOfEq (h : overIdeal N U = N') :
    (restrictModulesToSlice X U).map (cokernel.π N.ι) ≫ (cokernelOverIsoOfEq X U h).hom =
      cokernel.π N'.ι := by
  subst h
  exact π_comp_cokernelOverIso X U N

/-! ### Restriction of the adic quotients -/

variable (I : SheafOfModules.Submodule
  (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))

/-- **Restriction to a slice site commutes with the adic quotients of the structure sheaf**:
`(𝒪/ℐⁿ)|_U = 𝒪_U/(ℐ|_U)ⁿ`. -/
def adicQuotientModuleOverIso (n : ℕ) :
    (restrictModulesToSlice X U).obj (Stacks.Sites.adicQuotientModule (X := X) I n) ≅
      Stacks.Sites.adicQuotientModule (X := X.over U) (overIdeal I U) n :=
  cokernelOverIsoOfEq X U (overIdeal_idealPow X U I n)

/-- The restriction of the projection `𝒪 ⟶ 𝒪/ℐⁿ`, followed by
`AlgebraicGeometry.RingedSite.adicQuotientModuleOverIso`, is the projection
`𝒪_U ⟶ 𝒪_U/(ℐ|_U)ⁿ`. -/
@[reassoc]
theorem adicQuotientModuleπ_comp_adicQuotientModuleOverIso (n : ℕ) :
    (restrictModulesToSlice X U).map (Stacks.Sites.adicQuotientModuleπ (X := X) I n) ≫
        (adicQuotientModuleOverIso X U I n).hom =
      Stacks.Sites.adicQuotientModuleπ (X := X.over U) (overIdeal I U) n :=
  π_comp_cokernelOverIsoOfEq X U (overIdeal_idealPow X U I n)

/-- The restriction of the projection `𝒪 ⟶ 𝒪/ℐⁿ` to the slice site over `U` is an
epimorphism. -/
instance epi_restrictModulesToSlice_map_adicQuotientModuleπ (n : ℕ) :
    Epi ((restrictModulesToSlice X U).map (Stacks.Sites.adicQuotientModuleπ (X := X) I n)) := by
  rw [← epi_comp_iff_of_isIso _ (adicQuotientModuleOverIso X U I n).hom,
    adicQuotientModuleπ_comp_adicQuotientModuleOverIso]
  exact Stacks.Sites.epi_adicQuotientModuleπ (X := X.over U) (overIdeal I U) n

/-- **The identification of the restricted adic quotients is compatible with the transition
maps of the tower.** -/
@[reassoc]
theorem adicQuotientModuleMap_comp_adicQuotientModuleOverIso {m n : ℕ} (hmn : m ≤ n) :
    (restrictModulesToSlice X U).map (Stacks.Sites.adicQuotientModuleMap (X := X) I hmn) ≫
        (adicQuotientModuleOverIso X U I m).hom =
      (adicQuotientModuleOverIso X U I n).hom ≫
        Stacks.Sites.adicQuotientModuleMap (X := X.over U) (overIdeal I U) hmn := by
  refine (cancel_epi ((restrictModulesToSlice X U).map
    (Stacks.Sites.adicQuotientModuleπ (X := X) I n))).1 ?_
  rw [← Category.assoc, ← (restrictModulesToSlice X U).map_comp,
    Stacks.Sites.adicQuotientModuleπ_comp_adicQuotientModuleMap,
    adicQuotientModuleπ_comp_adicQuotientModuleOverIso, ← Category.assoc,
    adicQuotientModuleπ_comp_adicQuotientModuleOverIso]
  exact (Stacks.Sites.adicQuotientModuleπ_comp_adicQuotientModuleMap (X := X.over U)
    (overIdeal I U) hmn).symm

/-! ### The tower of adic quotients -/

/-- Restriction of complexes of `𝒪`-modules to the slice site over `U`, degreewise. -/
abbrev restrictComplexes :
    CochainComplex (Modules X) ℤ ⥤ CochainComplex (Modules (X.over U)) ℤ :=
  (restrictModulesToSlice X U).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The restriction of the structure sheaf complex is the structure sheaf complex of the
slice. -/
abbrev restrictUnitIso :
    restrictComplex X (Stacks.SheafOfModules.unitCochainComplex X) U ≅
      Stacks.SheafOfModules.unitCochainComplex (X.over U) :=
  (HomologicalComplex.singleMapHomologicalComplex (restrictModulesToSlice X U)
    (ComplexShape.up ℤ) 0).app (Stacks.SheafOfModules.unitModule X)

/-- The identification of the restricted adic quotients, assembled over the tower. -/
def adicQuotientTowerOverNatTrans :
    adicQuotientTower X I ⋙ restrictModulesToSlice X U ⟶
      adicQuotientTower (X.over U) (overIdeal I U) :=
  NatTrans.ofOpSequence (fun n => (adicQuotientModuleOverIso X U I (n + 1)).hom) fun n => by
    refine Eq.trans (congrArg (fun w => (restrictModulesToSlice X U).map w ≫
      (adicQuotientModuleOverIso X U I (n + 1)).hom) (adicQuotientTower_map_succ X I n)) ?_
    refine Eq.trans (adicQuotientModuleMap_comp_adicQuotientModuleOverIso X U I
      (Nat.le_succ (n + 1))) ?_
    exact congrArg (fun w => (adicQuotientModuleOverIso X U I (n + 1 + 1)).hom ≫ w)
      (adicQuotientTower_map_succ (X.over U) (overIdeal I U) n).symm

/-- Each component of `AlgebraicGeometry.RingedSite.adicQuotientTowerOverNatTrans` is an
isomorphism. -/
instance isIso_adicQuotientTowerOverNatTrans_app (n : ℕᵒᵖ) :
    IsIso ((adicQuotientTowerOverNatTrans X U I).app n) :=
  inferInstanceAs (IsIso (adicQuotientModuleOverIso X U I (unop n + 1)).hom)

/-- **Restriction to a slice site carries the tower `n ↦ 𝒪/ℐⁿ⁺¹` to the tower
`n ↦ 𝒪_U/(ℐ|_U)ⁿ⁺¹`**, naturally in the index. -/
def adicQuotientTowerOverIso :
    adicQuotientTower X I ⋙ restrictModulesToSlice X U ≅
      adicQuotientTower (X.over U) (overIdeal I U) :=
  haveI : IsIso (adicQuotientTowerOverNatTrans X U I) := NatIso.isIso_of_isIso_app _
  asIso (adicQuotientTowerOverNatTrans X U I)

/-- **Restriction to a slice site carries the strictified tower `n ↦ (𝒪/ℐⁿ⁺¹)[0]` to the
strictified tower of the restricted ideal.** -/
def strictAdicQuotientTowerOverIso :
    strictAdicQuotientTower X I ⋙ restrictComplexes X U ≅
      strictAdicQuotientTower (X.over U) (overIdeal I U) :=
  Functor.isoWhiskerLeft (adicQuotientTower X I)
      (HomologicalComplex.singleMapHomologicalComplex (restrictModulesToSlice X U)
        (ComplexShape.up ℤ) 0) ≪≫
    Functor.isoWhiskerRight (adicQuotientTowerOverIso X U I)
      (CochainComplex.singleFunctor (Modules (X.over U)) 0)

/-- The identification of the `n`-th term of the restricted strictified tower, written out. -/
theorem strictAdicQuotientTowerOverIso_hom_app (n : ℕᵒᵖ) :
    (strictAdicQuotientTowerOverIso X U I).hom.app n =
      (HomologicalComplex.singleMapHomologicalComplex (restrictModulesToSlice X U)
            (ComplexShape.up ℤ) 0).hom.app ((adicQuotientTower X I).obj n) ≫
        (CochainComplex.singleFunctor (Modules (X.over U)) 0).map
          ((adicQuotientTowerOverIso X U I).hom.app n) :=
  rfl

/-- If `r ≫ α = β ≫ G.map γ` and `γ ≫ δ = ε`, then `r ≫ α ≫ G.map δ = β ≫ G.map ε`. -/
private theorem comp_comp_map_eq_of_comp_eq {C D : Type*} [Category C] [Category D]
    (G : C ⥤ D) {P Q : D} {a b c : C} {r : P ⟶ Q} {α : Q ⟶ G.obj b} {β : P ⟶ G.obj a}
    {γ : a ⟶ b} {δ : b ⟶ c} {ε : a ⟶ c} (hnat : r ≫ α = β ≫ G.map γ) (h : γ ≫ δ = ε) :
    r ≫ α ≫ G.map δ = β ≫ G.map ε := by
  rw [← Category.assoc, hnat, Category.assoc, ← G.map_comp, h]

/-- **The restricted projections of the structure sheaf onto the adic quotients are the
projections of the slice**, through the identification of the restricted tower.

The chain is `Eq.trans`ed rather than rewritten: `Modules (X.over U)` and the sheaves of
modules over `((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U` that the restriction functor
is valued in are definitionally but not reducibly equal, so a goal in which a tactic has brought
both spellings together is not type-correct at `implicit` transparency and no rewrite fires on
it. -/
@[reassoc]
theorem strictAdicQuotientπ_comp_strictAdicQuotientTowerOverIso (n : ℕ) :
    restrictComplexMap X U (strictAdicQuotientπ X I n) ≫
        (strictAdicQuotientTowerOverIso X U I).hom.app ⟨n⟩ =
      (restrictUnitIso X U).hom ≫ strictAdicQuotientπ (X.over U) (overIdeal I U) n := by
  have hnat : restrictComplexMap X U (strictAdicQuotientπ X I n) ≫
      (HomologicalComplex.singleMapHomologicalComplex (restrictModulesToSlice X U)
          (ComplexShape.up ℤ) 0).hom.app ((adicQuotientTower X I).obj ⟨n⟩) =
      (restrictUnitIso X U).hom ≫
        (CochainComplex.singleFunctor (Modules (X.over U)) 0).map
          ((restrictModulesToSlice X U).map
            (Stacks.Sites.adicQuotientModuleπ (X := X) I (n + 1))) :=
    (HomologicalComplex.singleMapHomologicalComplex (restrictModulesToSlice X U)
      (ComplexShape.up ℤ) 0).hom.naturality _
  refine Eq.trans (congrArg (fun w => restrictComplexMap X U (strictAdicQuotientπ X I n) ≫ w)
    (strictAdicQuotientTowerOverIso_hom_app X U I ⟨n⟩)) ?_
  exact comp_comp_map_eq_of_comp_eq (CochainComplex.singleFunctor (Modules (X.over U)) 0) hnat
    (adicQuotientModuleπ_comp_adicQuotientModuleOverIso X U I (n + 1))

/-! ### The strictified reduction tower -/

variable (Kt : CochainComplex (Modules X) ℤ)

/-- **Restriction to a slice site commutes with `Tot(K̃ ⊗_𝒪 -)`**, naturally in the right
factor. The components are
`AlgebraicGeometry.RingedSite.tensorComplexOverIso` and the naturality square is
`AlgebraicGeometry.RingedSite.tensorComplexOverIso_hom_naturality_right`. -/
def tensorComplexOverNatIso :
    (Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj Kt ⋙ restrictComplexes X U ≅
      restrictComplexes X U ⋙
        (Stacks.SheafOfModules.Tensor.tensorComplex (X.O.over U)).obj
          (restrictComplex X Kt U) :=
  NatIso.ofComponents (fun B => tensorComplexOverIso X U Kt B) fun {_ _} g =>
    tensorComplexOverIso_hom_naturality_right X U Kt g

/-- **Restriction to a slice site carries the strictified adic quotient tower of `K̃` to the
strictified adic quotient tower of `K̃|_U` over the restricted ideal.** -/
def strictAdicReductionTowerOverIso :
    strictAdicReductionTower X I Kt ⋙ restrictComplexes X U ≅
      strictAdicReductionTower (X.over U) (overIdeal I U) (restrictComplex X Kt U) :=
  Functor.isoWhiskerLeft (strictAdicQuotientTower X I) (tensorComplexOverNatIso X U Kt) ≪≫
    Functor.isoWhiskerRight (strictAdicQuotientTowerOverIso X U I)
      ((Stacks.SheafOfModules.Tensor.tensorComplex (X.O.over U)).obj
        (restrictComplex X Kt U))

/-! ### The right unit law under restriction -/

/-- **The restriction comparison of `Tot(K̃ ⊗_𝒪 𝒪[0])`**: the restriction comparison of the
total tensor complex, followed by the identification of the restricted structure sheaf complex
with the structure sheaf complex of the slice. -/
def tensorComplexUnitOverIso :
    restrictComplex X (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj Kt).obj
        (Stacks.SheafOfModules.unitCochainComplex X)) U ≅
      ((Stacks.SheafOfModules.Tensor.tensorComplex (X.O.over U)).obj
        (restrictComplex X Kt U)).obj (Stacks.SheafOfModules.unitCochainComplex (X.over U)) :=
  tensorComplexOverIso X U Kt (Stacks.SheafOfModules.unitCochainComplex X) ≪≫
    ((Stacks.SheafOfModules.Tensor.tensorComplex (X.O.over U)).obj
      (restrictComplex X Kt U)).mapIso (restrictUnitIso X U)

/-- **Restriction commutes with the right unit law `Tot(K̃ ⊗_𝒪 𝒪[0]) ≅ K̃`.**

Both sides are maps out of `K̃|_U`, so the statement is checked on sections, where each step is
a formula: the inverse unit law takes a section `w` to the pure tensor `w ⊗ 1`
(`AlgebraicGeometry.RingedSite.tensorComplexUnitIsoFreeSections_inv_val_app`), the restriction
comparison takes a pure tensor to the pure tensor of the restricted sections
(`AlgebraicGeometry.RingedSite.tensorComplexOverIso_inv_tensorComplexSection`), and the
identification of the restricted structure sheaf complex takes the unit section to the unit
section, on the nose. -/
theorem tensorComplexUnitIsoFreeSections_inv_comp_restrict :
    (Stacks.SheafOfModules.tensorComplexUnitIsoFreeSections (X.O.over U)
          (restrictComplex X Kt U)).inv ≫ (tensorComplexUnitOverIso X U Kt).inv =
      restrictComplexMap X U
        (Stacks.SheafOfModules.tensorComplexUnitIsoFreeSections X.O Kt).inv := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  refine SheafOfModules.Hom.ext (PresheafOfModules.hom_ext fun V => ?_)
  refine ModuleCat.hom_ext (LinearMap.ext fun w => ?_)
  have hid : ((Stacks.SheafOfModules.Tensor.tensorComplex (X.O.over U)).map
          (𝟙 (restrictComplex X Kt U))).app
            (Stacks.SheafOfModules.unitCochainComplex (X.over U)) ≫
        ((Stacks.SheafOfModules.Tensor.tensorComplex (X.O.over U)).obj
          (restrictComplex X Kt U)).map (restrictUnitIso X U).inv =
      ((Stacks.SheafOfModules.Tensor.tensorComplex (X.O.over U)).obj
        (restrictComplex X Kt U)).map (restrictUnitIso X U).inv :=
    (congrArg (fun φ => NatTrans.app φ
        (Stacks.SheafOfModules.unitCochainComplex (X.over U)) ≫
        ((Stacks.SheafOfModules.Tensor.tensorComplex (X.O.over U)).obj
          (restrictComplex X Kt U)).map (restrictUnitIso X U).inv)
      ((Stacks.SheafOfModules.Tensor.tensorComplex (X.O.over U)).map_id
        (restrictComplex X Kt U))).trans (Category.id_comp _)
  have h1 := tensorComplexUnitIsoFreeSections_inv_val_app (X.over U)
    (restrictComplex X Kt U) n (unop V) w
  have h2 := tensorComplexMap_tensorComplexSection (X.over U)
    (𝟙 (restrictComplex X Kt U)) (restrictUnitIso X U).inv n 0 n (add_zero n)
    (W := unop V) w (structureSheafOne (X.over U) (unop V))
  have h2' : (ConcreteCategory.hom
        (((((Stacks.SheafOfModules.Tensor.tensorComplex (X.O.over U)).obj
          (restrictComplex X Kt U)).map (restrictUnitIso X U).inv).f n).val.app V))
        (tensorComplexSection (X.over U) n 0 n (add_zero n) w
          (structureSheafOne (X.over U) (unop V))) =
      tensorComplexSection (X.over U) n 0 n (add_zero n) w
        (structureSheafOne X (unop V).left) := by
    rw [← hid]; exact h2
  have h3 := tensorComplexOverIso_inv_tensorComplexSection X U Kt
    (Stacks.SheafOfModules.unitCochainComplex X) (unop V) n 0 n (add_zero n) w
    (structureSheafOne X (unop V).left)
  have h4 := tensorComplexUnitIsoFreeSections_inv_val_app X Kt n (unop V).left w
  refine Eq.trans ?_ h4.symm
  refine Eq.trans (congrArg (fun z => (ConcreteCategory.hom
      (((tensorComplexOverIso X U Kt
        (Stacks.SheafOfModules.unitCochainComplex X)).inv.f n).val.app V))
      ((ConcreteCategory.hom
        (((((Stacks.SheafOfModules.Tensor.tensorComplex (X.O.over U)).obj
          (restrictComplex X Kt U)).map (restrictUnitIso X U).inv).f n).val.app V)) z)) h1) ?_
  refine Eq.trans (congrArg (fun z => (ConcreteCategory.hom
      (((tensorComplexOverIso X U Kt
        (Stacks.SheafOfModules.unitCochainComplex X)).inv.f n).val.app V)) z) h2') ?_
  exact h3


/-- The comparison of `AlgebraicGeometry.RingedSite.tensorComplexUnitOverIso`, written out.

Stated so that the consumers below mention the composite and never
`AlgebraicGeometry.RingedSite.tensorComplexUnitOverIso` itself: unfolding that definition inside
a goal whose subterms are the bicomplex of the total tensor complex is what the elaborator
cannot afford. -/
theorem tensorComplexUnitOverIso_hom :
    (tensorComplexUnitOverIso X U Kt).hom =
      (tensorComplexOverIso X U Kt (Stacks.SheafOfModules.unitCochainComplex X)).hom ≫
        ((Stacks.SheafOfModules.Tensor.tensorComplex (X.O.over U)).obj
          (restrictComplex X Kt U)).map (restrictUnitIso X U).hom :=
  rfl

/-- **Restriction commutes with the right unit law**, in the form the strict cone needs: the
restriction of the inverse unit law, read through the restriction comparison of the total
tensor complex and the identification of the restricted structure sheaf complex, is the inverse
unit law of the slice. -/
@[reassoc]
theorem restrictComplexMap_tensorComplexUnitIsoFreeSections_inv :
    restrictComplexMap X U
          (Stacks.SheafOfModules.tensorComplexUnitIsoFreeSections X.O Kt).inv ≫
        (tensorComplexOverIso X U Kt (Stacks.SheafOfModules.unitCochainComplex X)).hom ≫
          ((Stacks.SheafOfModules.Tensor.tensorComplex (X.O.over U)).obj
            (restrictComplex X Kt U)).map (restrictUnitIso X U).hom =
      (Stacks.SheafOfModules.tensorComplexUnitIsoFreeSections (X.O.over U)
        (restrictComplex X Kt U)).inv := by
  rw [← tensorComplexUnitOverIso_hom]
  exact (Iso.eq_comp_inv _).1 (tensorComplexUnitIsoFreeSections_inv_comp_restrict X U Kt).symm

/-- The identification of the `n`-th term of the restricted strictified reduction tower,
written out. -/
theorem strictAdicReductionTowerOverIso_hom_app (n : ℕᵒᵖ) :
    (strictAdicReductionTowerOverIso X U I Kt).hom.app n =
      (tensorComplexOverIso X U Kt ((strictAdicQuotientTower X I).obj n)).hom ≫
        ((Stacks.SheafOfModules.Tensor.tensorComplex (X.O.over U)).obj
            (restrictComplex X Kt U)).map
          ((strictAdicQuotientTowerOverIso X U I).hom.app n) :=
  rfl

/-- **The restriction of `K̃` tensored with the `n`-th projection of the structure sheaf is
`K̃|_U` tensored with the `n`-th projection of the slice**, through the identification of the
restricted tower.

Every step is `Eq.trans`ed rather than rewritten, and the statement is split off from
`AlgebraicGeometry.RingedSite.strictAdicAugmentationApp_comp_strictAdicReductionTowerOverIso`
rather than inlined there, because the heartbeat budget is per declaration and the two halves
together exceed it. -/
@[reassoc]
theorem restrictComplexMap_tensorComplex_map_strictAdicQuotientπ (n : ℕ) :
    restrictComplexMap X U
          (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj Kt).map
            (strictAdicQuotientπ X I n)) ≫
        (strictAdicReductionTowerOverIso X U I Kt).hom.app ⟨n⟩ =
      (tensorComplexOverIso X U Kt (Stacks.SheafOfModules.unitCochainComplex X)).hom ≫
        ((Stacks.SheafOfModules.Tensor.tensorComplex (X.O.over U)).obj
            (restrictComplex X Kt U)).map (restrictUnitIso X U).hom ≫
          ((Stacks.SheafOfModules.Tensor.tensorComplex (X.O.over U)).obj
            (restrictComplex X Kt U)).map
            (strictAdicQuotientπ (X.over U) (overIdeal I U) n) := by
  refine Eq.trans (congrArg (fun w => _ ≫ w)
    (strictAdicReductionTowerOverIso_hom_app X U I Kt ⟨n⟩)) ?_
  refine Eq.trans (comp_comp_map_eq_of_comp_eq
    ((Stacks.SheafOfModules.Tensor.tensorComplex (X.O.over U)).obj (restrictComplex X Kt U))
    (tensorComplexOverIso_hom_naturality_right X U Kt (strictAdicQuotientπ X I n))
    (strictAdicQuotientπ_comp_strictAdicQuotientTowerOverIso X U I n)) ?_
  exact congrArg (fun w => _ ≫ w)
    (((Stacks.SheafOfModules.Tensor.tensorComplex (X.O.over U)).obj
      (restrictComplex X Kt U)).map_comp _ _)

/-! ### The strict cone -/

omit [HasWeakSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The `n`-th map of the base-changed strict cone, written out. -/
theorem map_strictAdicAugmentation_app_eq (n : ℕ) :
    ((strictAdicAugmentation X I Kt).map (restrictModulesToSlice X U)).app n =
      restrictComplexMap X U (strictAdicAugmentationApp X I Kt n) :=
  rfl

/-- The `n`-th map of the strict cone of the slice, written out. -/
theorem strictAdicAugmentation_app_over_eq (n : ℕ) :
    (strictAdicAugmentation (X.over U) (overIdeal I U) (restrictComplex X Kt U)).app n =
      (Stacks.SheafOfModules.tensorComplexUnitIsoFreeSections (X.O.over U)
            (restrictComplex X Kt U)).inv ≫
        ((Stacks.SheafOfModules.Tensor.tensorComplex (X.O.over U)).obj
          (restrictComplex X Kt U)).map (strictAdicQuotientπ (X.over U) (overIdeal I U) n) :=
  rfl

/-- **The restriction of the `n`-th map of the strict cone is the `n`-th map of the strict cone
of the restricted data**, through the identification of the restricted tower.

This is the content of the file assembled: the restriction comparison of `Tot(K̃ ⊗_𝒪 -)` is
natural in the right factor, the restricted projections of the structure sheaf onto the adic
quotients are the projections of the slice, and restriction commutes with the right unit law. -/
@[reassoc]
theorem strictAdicAugmentationApp_comp_strictAdicReductionTowerOverIso (n : ℕ) :
    restrictComplexMap X U (strictAdicAugmentationApp X I Kt n) ≫
        (strictAdicReductionTowerOverIso X U I Kt).hom.app ⟨n⟩ =
      (Stacks.SheafOfModules.tensorComplexUnitIsoFreeSections (X.O.over U)
            (restrictComplex X Kt U)).inv ≫
        ((Stacks.SheafOfModules.Tensor.tensorComplex (X.O.over U)).obj
          (restrictComplex X Kt U)).map
          (strictAdicQuotientπ (X.over U) (overIdeal I U) n) := by
  refine Eq.trans (congrArg (fun w => w ≫ _)
    (((restrictModulesToSlice X U).mapHomologicalComplex (ComplexShape.up ℤ)).map_comp
      (Stacks.SheafOfModules.tensorComplexUnitIsoFreeSections X.O Kt).inv
      (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj Kt).map
        (strictAdicQuotientπ X I n)))) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun w => _ ≫ w)
    (restrictComplexMap_tensorComplex_map_strictAdicQuotientπ X U I Kt n)) ?_
  exact restrictComplexMap_tensorComplexUnitIsoFreeSections_inv_assoc X U Kt
    (((Stacks.SheafOfModules.Tensor.tensorComplex (X.O.over U)).obj
      (restrictComplex X Kt U)).map (strictAdicQuotientπ (X.over U) (overIdeal I U) n))

/-- **The base change of the strict adic augmentation along restriction to an open is the
strict adic augmentation of the restricted data**, at each map of the cone.

The source of the base-changed augmentation is `K̃|_U`, which is the source of the strict
augmentation of the restricted data on the nose, so what the identification needs beyond the
isomorphism `AlgebraicGeometry.RingedSite.strictAdicReductionTowerOverIso` of the towers is
exactly this equality of the two families of cone maps. -/
@[reassoc]
theorem map_strictAdicAugmentation_app (n : ℕ) :
    ((strictAdicAugmentation X I Kt).map (restrictModulesToSlice X U)).app n ≫
        (strictAdicReductionTowerOverIso X U I Kt).hom.app ⟨n⟩ =
      (strictAdicAugmentation (X.over U) (overIdeal I U) (restrictComplex X Kt U)).app n := by
  refine Eq.trans (congrArg
    (fun w => w ≫ (strictAdicReductionTowerOverIso X U I Kt).hom.app ⟨n⟩)
    (map_strictAdicAugmentation_app_eq X U I Kt n)) ?_
  exact Eq.trans (strictAdicAugmentationApp_comp_strictAdicReductionTowerOverIso X U I Kt n)
    (strictAdicAugmentation_app_over_eq X U I Kt n).symm

/-! ### Invertibility of the comparison map transports -/

section Transport

variable {A : Type*} [Category A] [Abelian A] [HasProductsOfShape ℕ A]
  {F G : ℕᵒᵖ ⥤ CochainComplex A ℤ}

/-- **Invertibility of the canonical comparison map of an augmented tower transports along an
isomorphism of the augmented data.** The comparison map is a formula in the augmentation, so an
isomorphism of towers carrying one family of cone maps to the other carries one comparison map
to the other. -/
theorem quasiIso_augmentationMap_of_iso (a : Stacks.MilnorTower.TowerAugmentation F)
    (b : Stacks.MilnorTower.TowerAugmentation G) (k : a.source ≅ b.source) (e : F ≅ G)
    (h : ∀ n, k.hom ≫ b.app n = a.app n ≫ e.hom.app ⟨n⟩)
    (hb : QuasiIso b.augmentationMap) : QuasiIso a.augmentationMap := by
  have := hb
  have : IsIso (Stacks.MilnorTower.mappingCoconeMap e.hom) :=
    ⟨Stacks.MilnorTower.mappingCoconeMap e.inv,
      by rw [← Stacks.MilnorTower.mappingCoconeMap_comp, e.hom_inv_id,
        Stacks.MilnorTower.mappingCoconeMap_id],
      by rw [← Stacks.MilnorTower.mappingCoconeMap_comp, e.inv_hom_id,
        Stacks.MilnorTower.mappingCoconeMap_id]⟩
  have : QuasiIso (a.augmentationMap ≫ Stacks.MilnorTower.mappingCoconeMap e.hom) := by
    rw [← Stacks.MilnorTower.TowerAugmentation.augmentationMap_naturality a b k.hom e.hom h]
    infer_instance
  exact (quasiIso_iff_comp_right a.augmentationMap
    (Stacks.MilnorTower.mappingCoconeMap e.hom)).1 inferInstance

end Transport

/-- **The hypothesis `hlocal` of
`AlgebraicGeometry.RingedSite.quasiIso_strictAdicComparison_of_forall`, at restriction to an
open.** If the comparison map `K̃|_U ⟶ R lim (K̃|_U ⊗_{𝒪_U} 𝒪_U/(ℐ|_U)ⁿ⁺¹)` of the restricted
data is a quasi-isomorphism, then so is the base change along restriction of the comparison map
upstairs.

This is what makes `quasiIso_strictAdicComparison_of_forall` applicable with the restrictions to
the members of a cover as the base-change functors: its hypothesis about the base-changed data is
turned into a hypothesis about the strict adic comparison map of the slice, which is the same
assertion one site down. -/
theorem quasiIso_map_strictAdicAugmentation_augmentationMap
    (h : QuasiIso (strictAdicComparison (X.over U) (overIdeal I U) (restrictComplex X Kt U))) :
    QuasiIso ((strictAdicAugmentation X I Kt).map (restrictModulesToSlice X U)).augmentationMap :=
  quasiIso_augmentationMap_of_iso ((strictAdicAugmentation X I Kt).map (restrictModulesToSlice X U))
    (strictAdicAugmentation (X.over U) (overIdeal I U) (restrictComplex X Kt U))
    (Iso.refl _) (strictAdicReductionTowerOverIso X U I Kt)
    (fun n => (Category.id_comp _).trans
      (map_strictAdicAugmentation_app X U I Kt n).symm) h

/-! ### Locality of invertibility, with restriction as the base change -/

section Cover

variable (X : RingedSite.{u, u, u})
  (I : SheafOfModules.Submodule
    (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
  (Kt : CochainComplex (Modules X) ℤ) {ι : Type*} (V : ι → X.C)
  [∀ i, HasWeakSheafify (X.J.over (V i)) AddCommGrpCat.{u}]
  [∀ i, (X.J.over (V i)).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Invertibility of the comparison map `K̃ ⟶ R lim (K̃ ⊗_𝒪 𝒪/ℐⁿ⁺¹)` is local on the site,
with restriction to a family of objects as the base change.**

This is `AlgebraicGeometry.RingedSite.quasiIso_strictAdicComparison_of_forall` with the
restrictions `-|_{V i}` as the base-change functors, which is what the identification of this
file makes possible: the hypothesis that file states about the *base-changed* data has become
the hypothesis `hlocal` here, which is the invertibility of the strict adic comparison map of
the restricted data — the same assertion one site down.

The two hypotheses that remain are not about the cone. `hpc` says that each restriction
preserves the countable product of the terms of the tower, which holds because restriction to a
slice site is a right adjoint ([Stacks, Tag 08FJ]); `hdetect` says that the restrictions jointly
detect quasi-isomorphisms out of `K̃`, which is locality of invertibility for the family. Neither
is supplied here, and no exactness of countable products is used: only
`CategoryTheory.Limits.HasProductsOfShape ℕ`. -/
theorem quasiIso_strictAdicComparison_of_forall_restrict
    (hpc : ∀ i, IsIso (Stacks.MilnorTower.towerProductComparison (restrictModulesToSlice X (V i))
      (strictAdicReductionTower X I Kt)))
    (hdetect : ∀ f : Kt ⟶ strictAdicMilnorFibre X I Kt,
      (∀ i, QuasiIso (((restrictModulesToSlice X (V i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map f)) → QuasiIso f)
    (hlocal : ∀ i, QuasiIso (strictAdicComparison (X.over (V i)) (overIdeal I (V i))
      (restrictComplex X Kt (V i)))) :
    QuasiIso (strictAdicComparison X I Kt) :=
  quasiIso_strictAdicComparison_of_forall X I Kt (fun i => restrictModulesToSlice X (V i)) hpc
    hdetect
    fun i => quasiIso_map_strictAdicAugmentation_augmentationMap X (V i) I Kt (hlocal i)

end Cover

end AlgebraicGeometry.RingedSite

end
