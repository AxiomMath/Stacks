module

public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedCohomologySequence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedCone
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedCategory

/-!
# The comparison of the cone with the quotient, and the connecting morphism of a short exact
sequence of sheaf differential graded modules

Let `R` be a sheaf of rings on a site and let `(A, d)` be a sheaf of differential graded
`R`-algebras. Let
`0 → K --a--> L --b--> M → 0`
be a short exact sequence of right differential graded `A`-modules. The cone `C(a)` of tag 0FS5
comes with its canonical inclusion `i : L → C(a)` and its canonical projection
`p : C(a) → K[1]`. This file constructs the third map of the picture, the comparison

`q : C(a) ⟶ M`,

shows that it is a quasi-isomorphism — so that it becomes invertible in the derived category
`D(A, d)` of tag 0FT5 — and assembles the connecting morphism

`δ = - p ∘ q⁻¹`

of [Stacks, Tag 0FTB] out of it.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.coneDescHom`: the comparison `q : C(a) ⟶ M`, whose
  underlying morphism of complexes is Mathlib's `CochainComplex.mappingCone.descShortComplex`
  read through the identification of the cone's complex with the mapping cone.
* `SheafOfModules.DifferentialGradedModule.moduleToDerivedCategory`: the localization functor
  `Mod(A, d) ⥤ D(A, d)`, the quotient by homotopy followed by the localization at the
  quasi-isomorphisms.
* `SheafOfModules.DifferentialGradedModule.shortExactδ`: the connecting morphism `- p ∘ q⁻¹` of a
  short exact sequence, as a morphism `Mod(A,d) → D(A,d)` of its third term into the image of the
  degree-one shift of its first term.

## Main results

* `SheafOfModules.DifferentialGradedModule.coneIncl_coneDescHom`: the comparison restricts along
  the cone's inclusion of `L` to the second map `b` of the sequence, which is what identifies it
  with the source's `q`.
* `SheafOfModules.DifferentialGradedModule.quasiIso_coneDescHom`: for a short exact sequence the
  comparison is a quasi-isomorphism of the underlying complexes of sheaves of modules.
* `SheafOfModules.DifferentialGradedModule.isIso_moduleToDerivedCategory_map_coneDescHom`: hence
  it becomes invertible in `D(A, d)`, so `q⁻¹` is available there.
* `SheafOfModules.DifferentialGradedModule.shortExactδ_eq`: the connecting morphism is literally
  `- p ∘ q⁻¹`, the minus sign being the one attached to the cone projection in the source.

## Implementation notes

*The hypothesis `hS`.* Every declaration below that is conditional is conditional on exactly one
thing, `hS : S.ShortExact`, and that is the source's own datum rather than a result borrowed from
elsewhere: Section [Stacks, Tag 0FTA] defines `δ` for a short exact sequence
`0 → K --a--> L --b--> M → 0` of `Mod(A, d)`, and the `δ`-functor structure that tag 0FTB asserts
assigns a `δ` to each such sequence, so short exactness of `S` is quantified inside the statement
of the tag. `S.ShortExact` is Mathlib's notion in the abelian category
`SheafOfModules.DifferentialGradedModule A` (`DifferentialGradedModule.abelian`, which is what the
two sheafification hypotheses below supply), i.e. `S` exact with `S.f` a monomorphism and `S.g` an
epimorphism — the source's `0 → K → L → M → 0`.

*Why the comparison is a quasi-isomorphism.* The underlying complex of the cone is Mathlib's
`CochainComplex.mappingCone` — this is the field `ConePackage.cone_complex` of tag 0FS5 — and the
underlying short complex of complexes of a short exact sequence of differential graded modules is
short exact, which is tag 0FRK
(`SheafOfModules.DifferentialGradedModule.toCochainComplex_shortExact`). So the statement is
Mathlib's `CochainComplex.mappingCone.quasiIso_descShortComplex` transported along that
identification; no new homological algebra is needed.

*Spelling the types so that `rw` can work.* `CochainComplex.mappingCone (S.map
(SheafOfModules.toCochainComplex A)).f` and `CochainComplex.mappingCone S.f.toHomologicalComplex`
are definitionally but not syntactically equal, and the same holds for
`HomologicalComplex.homotopyCofiber.X` against `(CochainComplex.mappingCone _).X`. A goal mixing
the two spellings is not type-correct at the transparency `rw` and `simp` use to build a motive,
and every rewrite then fails with no progress. The definitions `coneSplit`, `coneInlX`, `coneInrX`
and `coneDesc` below therefore re-state the relevant Mathlib data with their *declared* types
spelled in the form the cone package uses, and the bridging lemmas are discharged by `exact`,
which elaborates at full transparency. All later rewriting stays inside one spelling.

*What this file does not do.* [Stacks, Tag 0FTB] asserts that the localization functor
`Mod(A, d) ⥤ D(A, d)` carries a `δ`-functor structure in the sense of
[Stacks, Tag 0150] (`CategoryTheory.Functor.DeltaFunctorStructure`) with connecting morphism
`δ = - p ∘ q⁻¹`. That structure is assembled in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedDeltaFunctorTriangle.lean`
(`SheafOfModules.DifferentialGradedModule.deltaFunctorStructure`), not here, because it needs two
things that are unavailable at this point in the development:

* a pre-triangulated structure on `D(A, d)`, which is [Stacks, Tag 0FT4] — that the
  quasi-isomorphisms are a multiplicative system compatible with the triangulation of
  `K(Mod(A, d))`. Given it, Mathlib's `CategoryTheory.Triangulated.Localization` supplies the
  structure from [Stacks, Tag 0FS7]
  (`SheafOfModules.DifferentialGradedModule.HomotopyCategory.instPretriangulated`), exactly as
  `StacksFrontier/Algebra/DGA/DerivedCategory.lean` does in the non-sheaf case; without it `D(A, d)`
  carries no shift, which is why `shortExactδ` below lands in the image of the differential graded
  shift `SheafOfModules.DifferentialGradedModule.shift` rather than in a translate;
* that the triangle `(K, L, C(a), a, i, -p)` is distinguished in `K(Mod(A, d))`. Tag 0FS7
  describes the distinguished triangles as those of *admissible* short exact sequences, and the
  graded splitting of the concrete cone of tag 0FS5 into such a sequence is
  `SheafOfModules.DifferentialGradedModule.exists_coneSequence`, which needs the differential
  graded category of
  `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedAxiomC.lean`; the triangle is
  then distinguished by
  `SheafOfModules.DifferentialGradedModule.homotopyConeTriangle_distinguished`, which is
  [Stacks, Tag 09QU].

The naturality half of the `δ`-functor structure does have its complex-level input here:
`SheafOfModules.DifferentialGradedModule.coneDesc_naturality` is Mathlib's
`CochainComplex.mappingCone.map_descShortComplex`, i.e. the compatibility of the comparisons `q`
with the morphism of cones induced by a morphism of short complexes.

The base is an arbitrary sheaf of rings on an arbitrary site rather than the structure sheaf of a
ringed site, and the universes of the site, the ring, the algebra pieces and the module pieces are
independent; a ringed site `X` is the case `R := X.ringSheaf`. `HasSheafify J AddCommGrpCat.{m}`
and `J.WEqualsLocallyBijective AddCommGrpCat.{m}` are carried where they are needed, as in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedCohomologySequence.lean`: over an
arbitrary site they are what make `SheafOfModules.{m} R` abelian, hence what makes "short exact"
mean anything.

## References

* [Stacks Project, Tag 0FTB](https://stacks.math.columbia.edu/tag/0FTB)
* [Stacks Project, Tag 0FS5](https://stacks.math.columbia.edu/tag/0FS5)
* [Stacks Project, Tag 0FT5](https://stacks.math.columbia.edu/tag/0FT5)
* [Stacks Project, Tag 0FRK](https://stacks.math.columbia.edu/tag/0FRK)
* [Stacks Project, Tag 0150](https://stacks.math.columbia.edu/tag/0150)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe t a m v u

namespace SheafOfModules.DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-! ### The mapping cone of a morphism of complexes, spelled as the cone package spells it -/

section Spelling

variable {K L : CochainComplex (SheafOfModules.{m} R) ℤ}

/-- The degreewise splitting of the mapping cone, with its declared type spelled through
`CochainComplex.mappingCone` rather than `HomologicalComplex.homotopyCofiber`. -/
def coneSplit (φ : K ⟶ L) (n : ℤ) :
    (CochainComplex.mappingCone φ).X n ≅ K.X (n + 1) ⊞ L.X n :=
  HomologicalComplex.homotopyCofiber.XIsoBiprod φ n (n + 1) (by simp)

/-- The inclusion of the shifted source into the mapping cone in degree `n`. -/
def coneInlX (φ : K ⟶ L) (n : ℤ) : K.X (n + 1) ⟶ (CochainComplex.mappingCone φ).X n :=
  HomologicalComplex.homotopyCofiber.inlX φ (n + 1) n (by simp)

/-- The inclusion of the target into the mapping cone in degree `n`. -/
def coneInrX (φ : K ⟶ L) (n : ℤ) : L.X n ⟶ (CochainComplex.mappingCone φ).X n :=
  HomologicalComplex.homotopyCofiber.inrX φ n

/-- The inverse of the splitting restricts on the first summand to `coneInlX`. -/
theorem biprod_inl_coneSplit_inv (φ : K ⟶ L) (n : ℤ) :
    biprod.inl ≫ (coneSplit φ n).inv = coneInlX φ n :=
  HomologicalComplex.homotopyCofiber.inl_XIsoBiprod_inv φ (n + 1) n (by simp)

/-- The inverse of the splitting restricts on the second summand to `coneInrX`. -/
theorem biprod_inr_coneSplit_inv (φ : K ⟶ L) (n : ℤ) :
    biprod.inr ≫ (coneSplit φ n).inv = coneInrX φ n :=
  HomologicalComplex.homotopyCofiber.inr_XIsoBiprod_inv φ (n + 1) n (by simp)

end Spelling

/-! ### The comparison of the cone with the third term -/

section Comparison

variable [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
  {A : DifferentialGradedAlgebra.{t, a} R}

/-- Mathlib's comparison `C(a) ⟶ M` of the mapping cone of the first map of a short complex
`K --a--> L --b--> M` with its third term, at the level of complexes of sheaves of modules and
with its declared type spelled as the cone package of tag 0FS5 spells it. -/
def coneDesc (S : ShortComplex (DifferentialGradedModule.{t, a, m} A)) :
    CochainComplex.mappingCone S.f.toHomologicalComplex ⟶ S.X₃.complex :=
  CochainComplex.mappingCone.descShortComplex (S.map (toCochainComplex A))

/-- The comparison `coneDesc` vanishes on the shifted source in each degree. -/
theorem coneInlX_coneDesc (S : ShortComplex (DifferentialGradedModule.{t, a, m} A)) (n : ℤ) :
    coneInlX S.f.toHomologicalComplex n ≫ (coneDesc S).f n = 0 :=
  CochainComplex.mappingCone.inl_v_descShortComplex_f
    (S.map (toCochainComplex A)) (n + 1) n (by omega)

/-- On the target, the comparison `coneDesc` is the second map of the short complex in each
degree. -/
theorem coneInrX_coneDesc (S : ShortComplex (DifferentialGradedModule.{t, a, m} A)) (n : ℤ) :
    coneInrX S.f.toHomologicalComplex n ≫ (coneDesc S).f n = S.g.toHomologicalComplex.f n :=
  CochainComplex.mappingCone.inr_f_descShortComplex_f (S.map (toCochainComplex A)) n

/-- Read through the degreewise splitting, the comparison is the second projection followed by
the second map of the short complex. -/
theorem coneSplit_inv_coneDesc (S : ShortComplex (DifferentialGradedModule.{t, a, m} A))
    (n : ℤ) :
    (coneSplit S.f.toHomologicalComplex n).inv ≫ (coneDesc S).f n =
      biprod.snd ≫ S.g.toHomologicalComplex.f n := by
  apply biprod.hom_ext'
  · rw [← Category.assoc, biprod_inl_coneSplit_inv, coneInlX_coneDesc, biprod.inl_snd_assoc,
      zero_comp]
  · rw [← Category.assoc, biprod_inr_coneSplit_inv, coneInrX_coneDesc, biprod.inr_snd_assoc]

/-- Both degreewise facts about the comparison read off a cone package: the formula through the
splitting, and the restriction along the inclusion. -/
private theorem conePackage_coneDesc_f_and_inclusion
    (S : ShortComplex (DifferentialGradedModule.{t, a, m} A)) (P : ConePackage S.f) (n : ℤ) :
    (eqToHom P.cone_complex ≫ coneDesc S).f n =
        (P.componentIso n).hom ≫ biprod.snd ≫ S.g.toHomologicalComplex.f n ∧
      P.inclusion.toHomologicalComplex.f n ≫ (eqToHom P.cone_complex ≫ coneDesc S).f n =
        S.g.toHomologicalComplex.f n := by
  obtain ⟨⟨cplx, mul, hassoc, hone, hleib⟩, incl, proj, hc, iso, hiso, af, as, hi, hp⟩ := P
  dsimp only at hc hiso hi ⊢
  subst hc
  rw [eqToHom_refl, Category.id_comp]
  have hiso' : iso n = coneSplit S.f.toHomologicalComplex n := eq_of_heq (hiso n)
  have hi' : incl.toHomologicalComplex =
      CochainComplex.mappingCone.inr S.f.toHomologicalComplex := eq_of_heq hi
  rw [hi']
  exact ⟨by rw [hiso', ← Iso.inv_comp_eq, coneSplit_inv_coneDesc], coneInrX_coneDesc S n⟩

/-- The degreewise formula for the comparison, read off any cone package: in degree `n` it is the
second projection of the splitting followed by the second map of the short complex. This is the
form in which the comparison is seen to commute with the right action of the algebra, the action
on the cone being specified in the second coordinate by `ConePackage.action_second`. -/
theorem conePackage_coneDesc_f (S : ShortComplex (DifferentialGradedModule.{t, a, m} A))
    (P : ConePackage S.f) (n : ℤ) :
    (eqToHom P.cone_complex ≫ coneDesc S).f n =
      (P.componentIso n).hom ≫ biprod.snd ≫ S.g.toHomologicalComplex.f n :=
  (conePackage_coneDesc_f_and_inclusion S P n).1

/-- The underlying morphism of complexes restricts along the cone's inclusion of the middle term
to the second map of the short complex. -/
theorem conePackage_inclusion_coneDesc
    (S : ShortComplex (DifferentialGradedModule.{t, a, m} A)) (P : ConePackage S.f) (n : ℤ) :
    P.inclusion.toHomologicalComplex.f n ≫ (eqToHom P.cone_complex ≫ coneDesc S).f n =
      S.g.toHomologicalComplex.f n :=
  (conePackage_coneDesc_f_and_inclusion S P n).2

/-- **The comparison `q : C(a) ⟶ M`.** For a short complex `K --a--> L --b--> M` of right
differential graded `A`-modules, this is the morphism of differential graded modules out of the
cone of `a` of tag 0FS5 whose underlying morphism of complexes is Mathlib's comparison of the
mapping cone with the third term: read through the degreewise splitting of the cone it is the
second projection followed by `b`. It commutes with the right action because the cone acts in its
second coordinate as `L` does (`ConePackage.action_second`) and `b` commutes with the action. -/
@[stacks 0FTB "the comparison q of the cone with the quotient"]
def coneDescHom (S : ShortComplex (DifferentialGradedModule.{t, a, m} A)) :
    (conePackage S.f).cone ⟶ S.X₃ where
  toHomologicalComplex := eqToHom (conePackage S.f).cone_complex ≫ coneDesc S
  map_mul n i U x y := by
    have hsplit := (conePackage S.f).action_second n i U x y
    rw [conePackage_coneDesc_f, conePackage_coneDesc_f]
    change (S.g.toHomologicalComplex.f (n + i)).val.app U
        ((((conePackage S.f).componentIso (n + i)).hom ≫ biprod.snd).val.app U
          (((conePackage S.f).cone.mul n i).app U x y)) = _
    rw [hsplit, S.g.map_mul]
    rfl

/-- The comparison restricts along the cone's inclusion of the middle term to the second map of
the short complex: this is the equation `i ≫ q = b` that identifies `q` with the map of the
source. -/
@[stacks 0FTB "the comparison q restricts to b along the cone inclusion"]
theorem coneIncl_coneDescHom (S : ShortComplex (DifferentialGradedModule.{t, a, m} A)) :
    (conePackage S.f).inclusion ≫ coneDescHom S = S.g :=
  Hom.ext fun n => conePackage_inclusion_coneDesc S (conePackage S.f) n

/-- **The comparison is a quasi-isomorphism** when the short complex is short exact. The
underlying complex of the cone is Mathlib's mapping cone, the underlying short complex of
complexes is short exact by tag 0FRK, and Mathlib's
`CochainComplex.mappingCone.quasiIso_descShortComplex` applies. -/
@[stacks 0FTB "q is a quasi-isomorphism"]
theorem quasiIso_coneDescHom {S : ShortComplex (DifferentialGradedModule.{t, a, m} A)}
    (hS : S.ShortExact) : QuasiIso (coneDescHom S).toHomologicalComplex := by
  have h : QuasiIso (coneDesc S) :=
    CochainComplex.mappingCone.quasiIso_descShortComplex (toCochainComplex_shortExact A S hS)
  show QuasiIso (eqToHom (conePackage S.f).cone_complex ≫ coneDesc S)
  infer_instance

/-- The naturality of the comparison in the short complex, at the level of complexes: Mathlib's
`CochainComplex.mappingCone.map_descShortComplex`. This is the complex-level half of the
naturality of the connecting morphism. -/
theorem coneDesc_naturality {S₁ S₂ : ShortComplex (DifferentialGradedModule.{t, a, m} A)}
    (φ : S₁ ⟶ S₂) :
    CochainComplex.mappingCone.map S₁.f.toHomologicalComplex S₂.f.toHomologicalComplex
        φ.τ₁.toHomologicalComplex φ.τ₂.toHomologicalComplex
        (congrArg Hom.toHomologicalComplex φ.comm₁₂).symm ≫ coneDesc S₂ =
      coneDesc S₁ ≫ φ.τ₃.toHomologicalComplex :=
  CochainComplex.mappingCone.map_descShortComplex (S₁.map (toCochainComplex A))
    (S₂.map (toCochainComplex A)) ((toCochainComplex A).mapShortComplex.map φ)

end Comparison

/-! ### The connecting morphism -/

section Connecting

variable [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]

/-- The localization functor `Mod(A, d) ⥤ D(A, d)`: the quotient by homotopy of tag 0FS1 followed
by the localization at the quasi-isomorphisms of tag 0FT5. -/
@[stacks 0FTB "the localization functor Mod(A,d) → D(A,d)"]
abbrev moduleToDerivedCategory (A : DifferentialGradedAlgebra.{t, a} R) :
    DifferentialGradedModule.{t, a, m} A ⥤ derivedCategory.{t, a, m} A :=
  HomotopyCategory.quotient A ⋙ toDerivedCategory A

variable {A : DifferentialGradedAlgebra.{t, a} R}

/-- The comparison `q` of a short exact sequence represents a quasi-isomorphism of the homotopy
category. -/
theorem quasiIsomorphisms_quotient_map_coneDescHom
    {S : ShortComplex (DifferentialGradedModule.{t, a, m} A)} (hS : S.ShortExact) :
    quasiIsomorphisms A ((HomotopyCategory.quotient A).map (coneDescHom S)) :=
  (quasiIsomorphisms_quotient_map_iff _).2 (quasiIso_coneDescHom hS)

/-- **The comparison `q` becomes invertible in `D(A, d)`**, so that `q⁻¹` is available there. -/
@[stacks 0FTB "q is invertible in D(A,d)"]
theorem isIso_moduleToDerivedCategory_map_coneDescHom
    {S : ShortComplex (DifferentialGradedModule.{t, a, m} A)} (hS : S.ShortExact) :
    IsIso ((moduleToDerivedCategory A).map (coneDescHom S)) :=
  Localization.inverts (quasiIsomorphisms A).Q (quasiIsomorphisms A) _
    (quasiIsomorphisms_quotient_map_coneDescHom hS)

/-- **The connecting morphism `δ = - p ∘ q⁻¹` of a short exact sequence of right differential
graded modules**, as a morphism of `D(A, d)` from the image of the third term to the image of the
degree-one shift of the first term. Here `q` is the comparison
`SheafOfModules.DifferentialGradedModule.coneDescHom`, invertible in `D(A, d)`, and `p` is the
canonical cone projection `ConePackage.projection` of tag 0FS5; **the minus sign is the one the
source attaches to the cone projection**, and dropping it gives a different connecting morphism.

Because `D(A, d)` carries no translation functor in this development — that is tag 0FT4, see the
implementation notes — the target is spelled as the image of the differential graded shift
`SheafOfModules.DifferentialGradedModule.shift` of the first term rather than as a translate of
the image. -/
@[stacks 0FTB "the connecting morphism δ = - p ∘ q⁻¹"]
def shortExactδ {S : ShortComplex (DifferentialGradedModule.{t, a, m} A)} (hS : S.ShortExact) :
    (moduleToDerivedCategory A).obj S.X₃ ⟶
      (moduleToDerivedCategory A).obj (shift S.X₁) :=
  have := isIso_moduleToDerivedCategory_map_coneDescHom hS
  inv ((moduleToDerivedCategory A).map (coneDescHom S)) ≫
    (moduleToDerivedCategory A).map (-(conePackage S.f).projection)

/-- **Tag 0FTB, the formula for the connecting morphism**: it is `- p ∘ q⁻¹`, with `q` the
comparison of the cone with the third term — which restricts to the second map of the sequence
along the cone's inclusion — and `p` the canonical cone projection. -/
@[stacks 0FTB "the connecting morphism δ = - p ∘ q⁻¹"]
theorem shortExactδ_eq {S : ShortComplex (DifferentialGradedModule.{t, a, m} A)}
    (hS : S.ShortExact) :
    (conePackage S.f).inclusion ≫ coneDescHom S = S.g ∧
      ∃ _ : IsIso ((moduleToDerivedCategory A).map (coneDescHom S)),
        shortExactδ hS =
          inv ((moduleToDerivedCategory A).map (coneDescHom S)) ≫
            (moduleToDerivedCategory A).map (-(conePackage S.f).projection) :=
  ⟨coneIncl_coneDescHom S, isIso_moduleToDerivedCategory_map_coneDescHom hS, rfl⟩

end Connecting

end SheafOfModules.DifferentialGradedModule

end
