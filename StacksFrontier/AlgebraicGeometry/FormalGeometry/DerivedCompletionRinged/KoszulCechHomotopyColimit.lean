module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulCechColimit
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulLimitFormula
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulPerfect
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedColimits
public import StacksFrontier.CategoryTheory.Sites.Simplicial.IntegerResolutionPostnikov
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomCoproducts
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DualTensorDerivedLimit

/-!
# The Čech complex is the homotopy colimit of the Koszul complexes, and Tag 0A0E

Let `(𝒞, 𝒪)` be a ringed site and let `f_1, …, f_r` be global sections of `𝒪`. The extended
alternating Čech complex `Č(f)` is the colimit of the Koszul complexes
`K(𝒪, f_1^{n+1}, …, f_r^{n+1})` in the category of cochain complexes of sheaves of
`𝒪`-modules, by `AlgebraicGeometry.RingedSite.isColimitKoszulCechComplexCocone`. Since colimits
over `ℕ` are exact in that category, [Stacks, Tag 0949] turns that into a *homotopy* colimit
presentation in `D(𝒪)`, which is the hypothesis `hcolim` of the formula of [Stacks, Tag 0A0E].

With that hypothesis discharged, with the direct-sum comparison `hcomp` of
[Stacks, Tag 0A0A] available from
`AlgebraicGeometry.RingedSite.isIso_derivedSheafHomSigmaComparison`, and with the third input
`hdual` of the formula *bypassed* — the proof of [Stacks, Tag 0A0A] uses clause 3 of
[Stacks, Tag 08JJ] only to identify the two towers, and
`AlgebraicGeometry.RingedSite.tensorDerivedDualSystemIsoOfPerfect` identifies them from
perfectness of the Koszul complexes alone — the formula of [Stacks, Tag 0A0E] is proved here,
unconditionally, for the canonical derived tensor product.

## Main results

* `AlgebraicGeometry.RingedSite.hasExactColimitsOfShape_nat_ringSheaf`: colimits over `ℕ` are
  exact in the category of sheaves of `𝒪`-modules.
* `AlgebraicGeometry.RingedSite.isHomotopyColimit_koszulPowerSystem`: **the Čech complex is the
  homotopy colimit in `D(𝒪)` of the Koszul complexes on the positive powers of `f_1, …, f_r`.**
  This is [Stacks, Tag 0913] followed by [Stacks, Tag 0949], and it is exactly the hypothesis
  `hcolim` of
  `AlgebraicGeometry.RingedSite.isDerivedLimit_tensorDerivedDualSystem_completionFunctor`.
* `AlgebraicGeometry.RingedSite.isDerivedLimit_tensorDerivedDualSystem_koszulPowerSystem`: the
  formula of [Stacks, Tag 0A0E] for the Koszul system at an *arbitrary* derived tensor product
  datum, with `hcolim` and `hcomp` discharged and `hdual` a hypothesis.
* `RingedSite.isDerivedLimit_tensorDerivedDualSystem_koszulPowerSystem_canonical`: **[Stacks,
  Tag 0A0E]**, the formula `K^∧ = R lim (K ⊗^𝐋_𝒪 K_n)` for the canonical derived tensor product,
  with no hypothesis left.

## Implementation notes

Exactness of the colimits over `ℕ` is the Grothendieck-abelianness of the sheaves of
`𝒪`-modules together with the passage from one universe of index categories to a smaller one:
`CategoryTheory.IsGrothendieckAbelian` supplies `CategoryTheory.AB5OfSize` at the universe `u`
of the site, and `ℕ` is a small category at universe `0`, so
`CategoryTheory.AB5OfSize_of_univLE` is what bridges them. The same one-line derivation appears
in `StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/ModuleResolutionPostnikov.lean`
for the total site of a simplicial site situation.

[Stacks, Tag 0949] is stated for the colimit *object* `colimit L`, so the homotopy colimit
statement is transported to the Čech complex along the canonical isomorphism between the two
colimits, by `StacksDraft.BrutalPostnikov.isHomotopyColimit_of_iso`.

The universes are the diagonal `RingedSite.{u, u, u}` with coefficient universe `u`, and the
derived category is the standard model, as everywhere in this directory.

The hypothesis `hdual` of
`AlgebraicGeometry.RingedSite.isDerivedLimit_tensorDerivedDualSystem_koszulPowerSystem` is
clause 3 of [Stacks, Tag 08JJ] in the shape "the canonical map
`K ⊗^𝐋_𝒪 L^∨ ⟶ R𝑆heafHom_𝒪(L, K)` of [Stacks, Tag 08JD] is invertible for a perfect `L`". The
canonical version does not need it. The proof of [Stacks, Tag 0A0A] uses clause 3 of
[Stacks, Tag 08JJ] for exactly one purpose, an isomorphism of the tower `n ↦ K ⊗^𝐋_𝒪 K_n^∨`
with the tower `n ↦ R𝑆heafHom_𝒪(K_n, K)`, and the isomorphism
`M ⊗^𝐋_𝒪 L^∨ ≅ R𝑆heafHom_𝒪(L, M)` for perfect `L`, with both of its naturalities, is
`AlgebraicGeometry.RingedSite.derivedDualTensorSheafHomIso`, constructed along
[Stacks, Tag 0ATN] rather than from the canonical map of [Stacks, Tag 08JD]. The resulting
formula for a tower of perfect objects is
`AlgebraicGeometry.RingedSite.isDerivedLimit_tensorDerivedDual_of_isPerfect` of
`StacksFrontier/CategoryTheory/Sites/Cohomology/Perfect/DualTensorDerivedLimit.lean`. The
isomorphism of [Stacks, Tag 0ATN] is stated for the canonical derived tensor product datum, so
for an arbitrary datum the hypothesis `hdual` stays.

## References

* [Stacks Project, Tag 0913](https://stacks.math.columbia.edu/tag/0913)
* [Stacks Project, Tag 0949](https://stacks.math.columbia.edu/tag/0949)
* [Stacks Project, Tag 0A0A](https://stacks.math.columbia.edu/tag/0A0A)
* [Stacks Project, Tag 0A0E](https://stacks.math.columbia.edu/tag/0A0E)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
* [Stacks Project, Tag 08JD](https://stacks.math.columbia.edu/tag/08JD)
* [Stacks Project, Tag 0ATN](https://stacks.math.columbia.edu/tag/0ATN)
* [Stacks Project, Tag 099B](https://stacks.math.columbia.edu/tag/099B)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard

/-- **Colimits over `ℕ` are exact in the category of sheaves of `𝒪`-modules.** That category is
Grothendieck abelian for the universe of the site, so filtered colimits of that size are exact,
and a category with exact filtered colimits of one size has them for every smaller size. -/
instance hasExactColimitsOfShape_nat_ringSheaf (X : RingedSite.{u, u, u}) :
    HasExactColimitsOfShape ℕ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  (AB5OfSize_of_univLE.{0, 0, u, u}
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).ofShape ℕ

section Colimit

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}] {r : ℕ}
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

/-- **The extended alternating Čech complex of `f_1, …, f_r` is the homotopy colimit in `D(𝒪)`
of the Koszul complexes on the positive powers of `f_1, …, f_r`.**

This is `AlgebraicGeometry.RingedSite.isColimitKoszulCechComplexCocone`, the colimit
presentation of [Stacks, Tag 0913] at the level of complexes, pushed into the derived category
by [Stacks, Tag 0949], which applies because colimits over `ℕ` are exact in the sheaves of
`𝒪`-modules.

It is exactly the hypothesis `hcolim` of
`AlgebraicGeometry.RingedSite.isDerivedLimit_tensorDerivedDualSystem_completionFunctor`, taken
at the Koszul system. -/
theorem isHomotopyColimit_koszulPowerSystem :
    IsHomotopyColimit (koszulPowerSystem X f ⋙ DerivedCategory.Q)
      (DerivedCategory.Q.obj (extendedAlternatingCech X f)) :=
  StacksDraft.BrutalPostnikov.isHomotopyColimit_of_iso
    (DerivedCategory.isHomotopyColimit_Q_obj_colimit (koszulPowerSystem X f))
    (DerivedCategory.Q.mapIso
      ((colimit.isColimit (koszulPowerSystem X f)).coconePointUniqueUpToIso
        (isColimitKoszulCechComplexCocone X f)))

end Colimit

section Formula

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ K₁ K₂ : HomologicalComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O))
      (ComplexShape.up ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  (T : Stacks.SheafOfModules.DerivedTensorProduct X)
  {r : ℕ} [HasWeakSheafify X.J CommRingCat.{u}]
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

/-- The formula of [Stacks, Tag 0A0E] for the Koszul system, with every input of
`AlgebraicGeometry.RingedSite.isDerivedLimit_tensorDerivedDualSystem_completionFunctor`
discharged but one: the derived-colimit presentation of the Čech complex is
`AlgebraicGeometry.RingedSite.isHomotopyColimit_koszulPowerSystem`, and the direct-sum
comparison `AlgebraicGeometry.RingedSite.isIso_derivedSheafHomSigmaComparison` is already built
into that statement.

The remaining hypothesis `hdual` is clause 3 of [Stacks, Tag 08JJ] at the Koszul complexes, in
the shape "the canonical map of [Stacks, Tag 08JD] is invertible".

This statement holds for an *arbitrary* derived tensor product datum. For the canonical derived
tensor product the formula of [Stacks, Tag 0A0E] holds without `hdual`, by
`AlgebraicGeometry.RingedSite.isDerivedLimit_tensorDerivedDualSystem_koszulPowerSystem_canonical`.
-/
theorem isDerivedLimit_tensorDerivedDualSystem_koszulPowerSystem
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hdual : ∀ n : ℕ, IsIso (derivedTensorDualToSheafHom X T
      ((koszulPowerSystem X f ⋙ DerivedCategory.Q).obj n) K)) :
    IsDerivedLimit (tensorDerivedDualSystem X T
        (koszulPowerSystem X f ⋙ DerivedCategory.Q) K)
      ((completionFunctor X f).obj K) :=
  isDerivedLimit_tensorDerivedDualSystem_completionFunctor X T f
    (koszulPowerSystem X f ⋙ DerivedCategory.Q) K
    hdual (isHomotopyColimit_koszulPowerSystem X f)

end Formula

section Canonical

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).obj A).Additive]
  [∀ K₁ K₂ : HomologicalComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O))
      (ComplexShape.up ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  {r : ℕ} [HasWeakSheafify X.J CommRingCat.{u}]
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

/-- **[Stacks, Tag 0A0E].** Let `(𝒞, 𝒪)` be a ringed site, let `f_1, …, f_r` be global sections
of `𝒪` and let `K` be an object of `D(𝒪)`. Then the derived completion
`K^∧ = R𝑆heafHom_𝒪(Č(f), K)` of [Stacks, Tag 099B] along the ideal sheaf generated by
`f_1, …, f_r` is a derived limit of the tower

`n ↦ K ⊗^𝐋_𝒪 K_n^∨`, `K_n = K(𝒪, f_1^{n+1}, …, f_r^{n+1})`,

the derived tensor product being the canonical one of [Stacks, Tag 06YU].

The three inputs of
`AlgebraicGeometry.RingedSite.isDerivedLimit_tensorDerivedDualSystem_completionFunctor` are all
discharged. The derived-colimit presentation of the Čech complex by the Koszul complexes is
`AlgebraicGeometry.RingedSite.isHomotopyColimit_koszulPowerSystem`, which is [Stacks, Tag 0913]
followed by [Stacks, Tag 0949]; the direct-sum comparison is
`AlgebraicGeometry.RingedSite.isIso_derivedSheafHomSigmaComparison`; and clause 3 of
[Stacks, Tag 08JJ] — the hypothesis `hdual` of that statement — is not needed at all. The proof
of [Stacks, Tag 0A0A] uses that clause for one purpose only, an isomorphism of the tower
`n ↦ K ⊗^𝐋_𝒪 K_n^∨` with the tower `n ↦ R𝑆heafHom_𝒪(K_n, K)`, and
`AlgebraicGeometry.RingedSite.tensorDerivedDualSystemIsoOfPerfect` builds that isomorphism from
the perfectness of the `K_n` alone, which is
`AlgebraicGeometry.RingedSite.isPerfect_koszulPowerComplex`. The canonical map of
[Stacks, Tag 08JD] therefore never enters.

The tower is the one of `AlgebraicGeometry.RingedSite.tensorDerivedDualSystem`,
`n ↦ K ⊗^𝐋_𝒪 K_n^∨` with `K_n` the Koszul complex in degrees `0, …, r`; that is the spelling
in which [Stacks, Tag 0A0A] is stated, and it is the source's `K ⊗^𝐋_𝒪 K_n` for the source's
`K_n`, which is the `𝒪`-dual of the complex in degrees `0, …, r` and so sits in degrees
`-r, …, 0`, as the proof of the tag records. -/
@[stacks 0A0E "the formula `K^∧ = R lim (K ⊗^L_O K_n)` for the derived completion along the \
ideal sheaf generated by global sections `f_1, …, f_r`, at the canonical derived tensor \
product, with the Koszul tower spelled as the duals `K_n^∨` of the Koszul complexes in \
degrees `0, …, r`, which is the spelling of Stacks 0A0A and the source's own `K_n`; the tower \
is indexed by `n : ℕ` carrying the exponent `n + 1`, the source's positive powers"]
theorem isDerivedLimit_tensorDerivedDualSystem_koszulPowerSystem_canonical
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    [HasCoproduct ((koszulPowerSystem X f ⋙ DerivedCategory.Q).obj)]
    [HasProduct fun n : ℕ ↦
      (derivedSheafHomSystem X (koszulPowerSystem X f ⋙ DerivedCategory.Q) K).obj (op n)]
    [HasProduct fun n : ℕ ↦
      (tensorDerivedDualSystem X (Stacks.SheafOfModules.canonicalDerivedTensorProduct.{u} X)
        (koszulPowerSystem X f ⋙ DerivedCategory.Q) K).obj (op n)] :
    IsDerivedLimit (tensorDerivedDualSystem X
        (Stacks.SheafOfModules.canonicalDerivedTensorProduct.{u} X)
        (koszulPowerSystem X f ⋙ DerivedCategory.Q) K)
      ((completionFunctor X f).obj K) :=
  isDerivedLimit_tensorDerivedDual_of_isPerfect X
    (koszulPowerSystem X f ⋙ DerivedCategory.Q) K
    (fun n ↦ isPerfect_koszulPowerComplex X f n)
    (isHomotopyColimit_koszulPowerSystem X f)

end Canonical

end AlgebraicGeometry.RingedSite

end
