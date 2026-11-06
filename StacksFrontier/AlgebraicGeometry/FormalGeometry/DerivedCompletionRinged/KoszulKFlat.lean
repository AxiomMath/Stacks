module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulPerfectDual
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatRetract
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.BoundedAboveFlatComplexes
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.FlatnessOfFiniteFreeSummands
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.KFlatIntoKInjectiveIsKInjective
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.StrictlyPerfectIsKFlat
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.Duals
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.UnboundedGlobalSections
import StacksCore.Tactic.StacksAttribute

/-!
# The Koszul complex is K-flat, and the derived internal Hom out of it

Let `(𝒞, 𝒪)` be a ringed site and let `f_1, …, f_r` be global sections of `𝒪`. The Koszul
complex `K^n = K(𝒪, f_1^{n+1}, …, f_r^{n+1})` of [Stacks, Tag 0913] —
`AlgebraicGeometry.RingedSite.koszulPowerComplex` — is concentrated in degrees `0, …, r` and
each of its terms is a finite product of copies of `𝒪`. This file draws the two consequences
of that which the derived form of the projection formula against the Koszul complexes needs:

* `K^n` is **K-flat** ([Stacks, Tag 06YQ]); hence
* the internal Hom complex `SheafHom•_𝒪(K^n, J)` out of it into a K-injective complex `J` is
  again **K-injective** ([Stacks, Tag 0A96]), and the derived internal Hom
  `R𝑆heafHom_𝒪(K^n, L)` is represented by the internal Hom complex `SheafHom•_𝒪(K^n, L)`
  ([Stacks, Tag 08JH]).

The second item is the arbitrary-`r` replacement for the step that
`Stacks.Cohomology.KoszulTowerSections.nonempty_iso_koszulTower_derivedSections` of
`PrincipalKoszulTowerDerivedSections.lean` performs at `r = 1` with
`CochainComplex.isKInjective_mappingCone`: there the Koszul complex is a mapping cone, so its
Hom complex into a K-injective complex is K-injective for that reason, whereas at an arbitrary
`r` it is K-flatness of the Koszul complex that supplies it.

## Main results

* `AlgebraicGeometry.RingedSite.isFlat_of_isFiniteFreeSummand`: a direct summand of a finite
  free `𝒪`-module is a flat `𝒪`-module, in the `IsFiniteFreeSummand` spelling.
* `AlgebraicGeometry.RingedSite.isKFlat_of_isFiniteFreeSummand`: a bounded above complex whose
  terms are direct summands of finite free `𝒪`-modules is K-flat — [Stacks, Tag 06YQ] in that
  spelling.
* `AlgebraicGeometry.RingedSite.isDirectSummandOfFiniteFree_of_isFiniteFreeSummand`: the
  converse of `AlgebraicGeometry.RingedSite.IsDirectSummandOfFiniteFree.isFiniteFreeSummand`.
* `AlgebraicGeometry.RingedSite.isStrictlyLE_koszulPowerComplex`: the Koszul complex vanishes
  above degree `r`.
* `AlgebraicGeometry.RingedSite.isKFlat_koszulPowerComplex`: **the Koszul complex is K-flat.**
* `AlgebraicGeometry.RingedSite.isStrictlyPerfect_koszulPowerComplex`: the Koszul complex is
  strictly perfect in the [Stacks, Tag 08FL] spelling.
* `AlgebraicGeometry.RingedSite.isKFlat_sheafHomComplex_structureSheaf` and
  `AlgebraicGeometry.RingedSite.isKFlat_koszulPowerDualComplex`: **the `𝒪`-dual of a strictly
  perfect complex, and in particular the `𝒪`-dual `Hom_𝒪(K^n, 𝒪)` of the Koszul complex — the
  complex `K_n` of the Koszul formula of [Stacks, Tag 0A0E] — is K-flat.**
* `AlgebraicGeometry.RingedSite.isKInjective_sheafHomComplex_koszulPowerComplex`: **the internal
  Hom complex out of the Koszul complex into a K-injective complex is K-injective.**
* `AlgebraicGeometry.RingedSite.isIso_strictlyPerfectHomComparison_koszulPowerComplex` and
  `AlgebraicGeometry.RingedSite.koszulDerivedSheafHomComplexIso`: **the derived internal Hom out
  of the Koszul complex is represented by the internal Hom complex**, which is [Stacks, Tag 08JH]
  at a Koszul source.
* `AlgebraicGeometry.RingedSite.moduleGlobalSectionsDerivedUnit` and
  `AlgebraicGeometry.RingedSite.isIso_moduleGlobalSectionsDerivedUnit_app`: the complex-level
  comparison `Q(Γ(𝒞, C)) ⟶ RΓ(𝒞, Q C)` for `A`-linear global sections, and its invertibility at
  a K-injective complex.
* `RingedSite.isIso_moduleGlobalSectionsDerivedUnit_app_sheafHomComplex_koszulPowerComplex`:
  **`Γ(𝒞, -)` computes `RΓ(𝒞, -)` on the internal Hom complexes against the Koszul tower**, at an
  arbitrary number `r` of sections.

## Implementation notes

Two spellings of "direct summand of a finite free module" occur in this area.
`Stacks.IsDirectSummandOfFiniteFree` of [Stacks, Tag 08FL] is what `Stacks.IsStrictlyPerfect`
and `Stacks.SheafOfModules.isFlat_X_of_isStrictlyPerfect` are stated against, while
`AlgebraicGeometry.RingedSite.IsFiniteFreeSummand` — a retract of the iterated binary biproduct
`AlgebraicGeometry.RingedSite.unitPower` — is what the internal Hom cluster, and in particular
`AlgebraicGeometry.RingedSite.isFiniteFreeSummand_koszulPowerComplex_X`, is stated against. The
library has the bridge in one direction only
(`AlgebraicGeometry.RingedSite.IsDirectSummandOfFiniteFree.isFiniteFreeSummand`), so the
flatness of a term is re-derived here from the `IsFiniteFreeSummand` side rather than routed
through `Stacks.SheafOfModules.isFlat_X_of_isStrictlyPerfect`: a retract of
`⨁ (fun _ : Fin m => 𝒪)` is a retract of the finite free module
`SheafOfModules.free (ULift (Fin m))`, which is flat by
`Stacks.SheafOfModules.isFlat_free`, and flatness passes to retracts by
`Stacks.SheafOfModules.FlatRetract.isFlat_of_retract`. Nothing here needs
`Stacks.IsStrictlyPerfect`, which is why `AlgebraicGeometry.RingedSite.kFlat_of_isStrictlyPerfect`
of `StacksFrontier/CategoryTheory/Sites/Cohomology/KFlat/StrictlyPerfectIsKFlat.lean` is not used directly.

The boundedness of the Koszul complex is `isZero_koszulPowerComplex_X_of_lt` of
`KoszulDerivedCompletion.lean`, and the two inputs about its terms are
`isFiniteFreeSummand_koszulPowerComplex_X` and `finite_support_koszulPowerComplex` of
`KoszulDerivedDualNaive.lean` and `KoszulDerivedTensorDual.lean`.

## References

* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [Stacks Project, Tag 08FL](https://stacks.math.columbia.edu/tag/08FL)
* [Stacks Project, Tag 08JH](https://stacks.math.columbia.edu/tag/08JH)
* [Stacks Project, Tag 0913](https://stacks.math.columbia.edu/tag/0913)
* [Stacks Project, Tag 0A96](https://stacks.math.columbia.edu/tag/0A96)
* [Stacks Project, Tag 0A0E](https://stacks.math.columbia.edu/tag/0A0E)
* [Stacks Project, Tag 0BLX](https://stacks.math.columbia.edu/tag/0BLX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u d

namespace AlgebraicGeometry.RingedSite

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

/-- Weak sheafification of abelian presheaves on a ringed site, from the global instance
`Stacks.SheafOfModules.coefficientSheafification`. It is made a local instance of high priority
so that the declarations below find it rather than the section variable
`[HasSheafify X.J AddCommGrpCat.{u}]`, and so do not depend on that variable. -/
abbrev hasWeakSheafifyAddCommGrpCatKoszulKFlat (X : RingedSite.{u, u, u}) :
    HasWeakSheafify X.J AddCommGrpCat.{u} :=
  inferInstance

attribute [local instance high] hasWeakSheafifyAddCommGrpCatKoszulKFlat
  hasFiniteBiproducts_sheafOfModules

/-! ## Flatness from the `IsFiniteFreeSummand` spelling -/

section Flat

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The finite free `𝒪`-module on `ULift (Fin m)` agrees with the biproduct of `m` copies of
the structure sheaf**: both are a coproduct of copies of `𝒪` over a type of cardinality `m`.
This identifies the two spellings of "finite free" that the flatness cluster and the internal
Hom cluster use. -/
def freeIsoBiproductUnit (m : ℕ) :
    SheafOfModules.free (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ULift.{u} (Fin m)) ≅
      ⨁ fun _ : Fin m => SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  (CategoryTheory.Limits.IsColimit.coconePointUniqueUpToIso
      (SheafOfModules.isColimitFreeCofan (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ULift.{u} (Fin m)))
      (biproduct.isColimit fun _ : ULift.{u} (Fin m) =>
        SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).trans
    (biproduct.whiskerEquiv
      (f := fun _ : ULift.{u} (Fin m) =>
        SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (g := fun _ : Fin m => SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      Equiv.ulift fun _ => Iso.refl _)

/-- The biproduct of finitely many copies of the structure sheaf is a flat `𝒪`-module, being a
finite free `𝒪`-module. -/
theorem isFlat_biproduct_unit (m : ℕ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O)
      (⨁ fun _ : Fin m => SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  Stacks.SheafOfModules.FlatRetract.isFlat_of_retract X.O (freeIsoBiproductUnit X m).inv
    (freeIsoBiproductUnit X m).hom (freeIsoBiproductUnit X m).inv_hom_id
    (Stacks.SheafOfModules.isFlat_free (Y := X) (ULift.{u} (Fin m)))

omit [HasSheafify X.J AddCommGrpCat.{u}] in
/-- **The `IsFiniteFreeSummand` spelling implies the [Stacks, Tag 08FL] spelling.** A retract of
the iterated binary biproduct `𝒪^{⊕m}` is a retract of the finite free `𝒪`-module on
`ULift (Fin m)`. This is the converse of
`AlgebraicGeometry.RingedSite.IsDirectSummandOfFiniteFree.isFiniteFreeSummand`. -/
theorem isDirectSummandOfFiniteFree_of_isFiniteFreeSummand
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hM : IsFiniteFreeSummand X M) :
    _root_.IsDirectSummandOfFiniteFree (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M := by
  obtain ⟨m, ⟨ρ⟩⟩ := (isFiniteFreeSummand_iff_retract_biproduct X M).1 hM
  refine (isDirectSummandOfFiniteFree_iff_free (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M).2
    ⟨m, ρ.i ≫ (freeIsoBiproductUnit X m).inv, (freeIsoBiproductUnit X m).hom ≫ ρ.r, ?_⟩
  rw [Category.assoc, ← Category.assoc (freeIsoBiproductUnit X m).inv,
    (freeIsoBiproductUnit X m).inv_hom_id, Category.id_comp, ρ.retract]

/-- **A direct summand of a finite free `𝒪`-module is flat**, in the `IsFiniteFreeSummand`
spelling of the condition. The module is a retract of `⨁ (fun _ : Fin m => 𝒪)`, which is flat
by `isFlat_biproduct_unit`, and flatness passes to retracts. -/
theorem isFlat_of_isFiniteFreeSummand
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hM : IsFiniteFreeSummand X M) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O) M := by
  obtain ⟨m, ⟨ρ⟩⟩ := (isFiniteFreeSummand_iff_retract_biproduct X M).1 hM
  exact Stacks.SheafOfModules.FlatRetract.isFlat_of_retract X.O ρ.i ρ.r ρ.retract
    (isFlat_biproduct_unit X m)

variable [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- **[Stacks, Tag 06YQ] in the `IsFiniteFreeSummand` spelling**: a bounded above complex of
`𝒪`-modules each of which is a direct summand of a finite free `𝒪`-module is K-flat. -/
theorem isKFlat_of_isFiniteFreeSummand
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hbound : ∃ n : ℤ, K.IsStrictlyLE n)
    (hterm : ∀ i : ℤ, IsFiniteFreeSummand X (K.X i)) :
    Stacks.SheafOfModules.IsKFlat X.O K :=
  Stacks.SheafOfModules.kFlat_of_boundedAbove_of_flat X.O K hbound
    fun i => isFlat_of_isFiniteFreeSummand X (K.X i) (hterm i)

end Flat

/-! ## The Koszul complex is K-flat -/

section Koszul

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify X.J CommRingCat.{u}] {r : ℕ}
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

omit [HasSheafify X.J AddCommGrpCat.{u}] [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify X.J CommRingCat.{u}] in
/-- **The Koszul complex is concentrated in degrees `≤ r`.** Its term in a degree above `r` is a
product over an empty index type. -/
theorem isStrictlyLE_koszulPowerComplex (n : ℕ) :
    (koszulPowerComplex X f n).IsStrictlyLE (r : ℤ) :=
  (CochainComplex.isStrictlyLE_iff (koszulPowerComplex X f n) (r : ℤ)).2
    fun _ hi => isZero_koszulPowerComplex_X_of_lt X f n hi

variable [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- **The Koszul complex `K(𝒪, f_1^{n+1}, …, f_r^{n+1})` is K-flat.** It is concentrated in
degrees `0, …, r`, hence bounded above, and each of its terms is a finite product of copies of
`𝒪` and therefore a flat `𝒪`-module; [Stacks, Tag 06YQ] concludes. Nothing is assumed of the
sections `f_1, …, f_r`. -/
theorem isKFlat_koszulPowerComplex (n : ℕ) :
    Stacks.SheafOfModules.IsKFlat X.O (koszulPowerComplex X f n) :=
  isKFlat_of_isFiniteFreeSummand X (koszulPowerComplex X f n)
    ⟨(r : ℤ), isStrictlyLE_koszulPowerComplex X f n⟩
    (isFiniteFreeSummand_koszulPowerComplex_X X f n)

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- **The internal Hom complex out of the Koszul complex into a K-injective complex is
K-injective.** The Koszul complex is K-flat, and [Stacks, Tag 0A96] says the internal Hom
complex out of a K-flat complex into a K-injective complex is K-injective.

This is what makes `Γ(𝒞, -)` compute `RΓ(𝒞, -)` on the Hom complexes against the Koszul tower,
at an arbitrary number `r` of sections: at `r = 1` the corresponding input is
`CochainComplex.isKInjective_mappingCone`, the Koszul complex being a mapping cone there. -/
theorem isKInjective_sheafHomComplex_koszulPowerComplex (n : ℕ)
    (J : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [J.IsKInjective] :
    (sheafHomComplex X (koszulPowerComplex X f n) J).obj.IsKInjective :=
  isKInjective_sheafHomComplex_of_isKFlat X (koszulPowerComplex X f n) J
    (isKFlat_koszulPowerComplex X f n)

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- **The `𝒪`-dual of a strictly perfect complex is K-flat.** The dual of a strictly perfect
complex is strictly perfect, and a strictly perfect complex is K-flat by [Stacks, Tag 06YQ]. -/
theorem isKFlat_sheafHomComplex_structureSheaf
    (E : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hE : _root_.IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf X.O) E) :
    Stacks.SheafOfModules.IsKFlat X.O (sheafHomComplex X E (structureSheafComplex X)).obj :=
  kFlat_of_isStrictlyPerfect X (sheafHomComplex X E (structureSheafComplex X)).obj
    (isStrictlyPerfect_sheafHomComplex_structureSheaf X E hE)

omit [HasWeakSheafify X.J CommRingCat.{u}]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive] in
/-- **The `𝒪`-dual of the Koszul complex is strictly perfect.** The Koszul complex is strictly
perfect, and the internal Hom complex of a strictly perfect complex into the structure sheaf in
degree zero is again strictly perfect. -/
theorem isStrictlyPerfect_sheafHomComplex_koszulPowerComplex (n : ℕ) :
    _root_.IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      (sheafHomComplex X (koszulPowerComplex X f n) (structureSheafComplex X)).obj :=
  isStrictlyPerfect_sheafHomComplex_structureSheaf X (koszulPowerComplex X f n)
    (isStrictlyPerfect_koszulPowerComplex X f n)

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- **The `𝒪`-dual `Hom_𝒪(K^n, 𝒪)` of the Koszul complex is K-flat.** This is the complex `K_n`
in the grading of the Koszul formula of [Stacks, Tag 0A0E]: it is strictly perfect, being the
dual of a strictly perfect complex, and a strictly perfect complex is K-flat by
[Stacks, Tag 06YQ]. -/
theorem isKFlat_koszulPowerDualComplex (n : ℕ) :
    Stacks.SheafOfModules.IsKFlat X.O
      (sheafHomComplex X (koszulPowerComplex X f n) (structureSheafComplex X)).obj :=
  isKFlat_sheafHomComplex_structureSheaf X (koszulPowerComplex X f n)
    (isStrictlyPerfect_koszulPowerComplex X f n)

end Koszul

/-! ## The derived internal Hom out of the Koszul complex is the internal Hom complex -/

section Representation

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify X.J CommRingCat.{u}]
  [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  (D : DerivedInternalHom.{u, d} X) {r : ℕ}
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

omit [HasSheafify X.J AddCommGrpCat.{u}] [HasWeakSheafify X.J CommRingCat.{u}] in
/-- **[Stacks, Tag 08JH] at a Koszul source.** The canonical comparison from the class of the
internal Hom complex `SheafHom•_𝒪(K^n, L)` to the derived internal Hom `R𝑆heafHom_𝒪(K^n, L)` is
invertible, for every complex `L` of `𝒪`-modules. The Koszul complex is bounded with every term
a direct summand of a finite free `𝒪`-module, which is exactly the hypothesis of
`strictlyPerfectHomComparison_isIso`. -/
theorem isIso_strictlyPerfectHomComparison_koszulPowerComplex
    [HasWeakSheafify X.J AddCommGrpCat.{u}] (n : ℕ)
    (L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    IsIso (strictlyPerfectHomComparison X D (koszulPowerComplex X f n) L) :=
  strictlyPerfectHomComparison_isIso X D (koszulPowerComplex X f n) L
    (finite_support_koszulPowerComplex X f n)
    (isFiniteFreeSummand_koszulPowerComplex_X X f n)

/-- **The derived internal Hom out of the Koszul complex is represented by the internal Hom
complex**, as an isomorphism `Q(SheafHom•_𝒪(K^n, L)) ≅ R𝑆heafHom_𝒪(K^n, L)` in `D(𝒪)`. -/
def koszulDerivedSheafHomComplexIso
    [HasWeakSheafify X.J AddCommGrpCat.{u}] (n : ℕ)
    (L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    DerivedCategory.Q.obj (sheafHomComplex X (koszulPowerComplex X f n) L).obj ≅
      (D.hom.obj (op (DerivedCategory.Q.obj (koszulPowerComplex X f n)))).obj
        (DerivedCategory.Q.obj L) :=
  @asIso _ _ _ _ (strictlyPerfectHomComparison X D (koszulPowerComplex X f n) L)
    (isIso_strictlyPerfectHomComparison_koszulPowerComplex X D f n L)

end Representation

/-! ## Global sections compute derived global sections on those Hom complexes -/

section GlobalSections

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u}) (A : Type u) [CommRing A]
  (ρ : A →+* RingCat.sectionsSubring ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj)

/-- **The complex-level comparison `Q(Γ(𝒞, C)) ⟶ RΓ(𝒞, Q C)`** for `A`-linear global sections:
the unit of the total right derived functor
`AlgebraicGeometry.RingedSite.derivedGlobalSectionsOverUnbounded`, read on cochain complexes
rather than on the homotopy category. -/
def moduleGlobalSectionsDerivedUnit :
    (moduleGlobalSectionsOver X A ρ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ derivedGlobalSectionsOverUnbounded X A ρ :=
  ((Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      ((moduleGlobalSectionsOver X A ρ).mapHomotopyCategoryFactors (ComplexShape.up ℤ))
      DerivedCategory.Qh ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A))).inv ≫
  Functor.whiskerLeft
    (HomotopyCategory.quotient (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
      (ComplexShape.up ℤ))
    (derivedGlobalSectionsOverUnboundedUnit X A ρ) ≫
  (Functor.associator _ _ _).inv ≫
  Functor.whiskerRight
    (DerivedCategory.quotientCompQhIso
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).hom
    (derivedGlobalSectionsOverUnbounded X A ρ)

/-- **`Γ(𝒞, -)` computes `RΓ(𝒞, -)` on a K-injective complex.** The comparison
`Q(Γ(𝒞, I)) ⟶ RΓ(𝒞, Q I)` is invertible at every K-injective complex of `𝒪`-modules.

`Mod(𝒪)` is Grothendieck abelian and so carries functorial K-injective resolutions, which is
what makes the total right derived functor pointwise and its unit invertible there. This is
`Stacks.Cohomology.KoszulTowerSections.isIso_sectionsDerivedUnit_app` of
`PrincipalKoszulTowerDerivedSections.lean` for `A`-linear global sections on a ringed site in
place of sections over the whole of a ringed space. -/
theorem isIso_moduleGlobalSectionsDerivedUnit_app
    (I : CochainComplex (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ℤ)
    (hI : I.IsKInjective) :
    IsIso ((moduleGlobalSectionsDerivedUnit X A ρ).app I) := by
  have _ := SheafOfModules.isGrothendieckAbelianU ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  have h : IsIso ((derivedGlobalSectionsOverUnboundedUnit X A ρ).app
      ((HomotopyCategory.quotient
          (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
        (ComplexShape.up ℤ)).obj I)) :=
    (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
      (homotopyGlobalSectionsOver X A ρ)
      (fun K ↦ ⟨(Stacks.Injectives.kInjectiveResolutionFunctor
          (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).obj K,
        (Stacks.Injectives.kInjectiveResolutionInclusion
          (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).app K,
        inferInstance, inferInstance⟩)).2
      DerivedCategory.Qh (derivedGlobalSectionsOverUnbounded X A ρ)
      (derivedGlobalSectionsOverUnboundedUnit X A ρ) I hI
  dsimp [moduleGlobalSectionsDerivedUnit]
  infer_instance

variable [HasSheafify X.J AddCommGrpCat.{u}]
  [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify X.J CommRingCat.{u}] {r : ℕ}
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).Additive]
  [∀ B, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).obj B).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- **`A`-linear global sections compute derived global sections on the internal Hom complexes
against the Koszul tower.** For a K-injective complex `J` of `𝒪`-modules the comparison
`Q(Γ(𝒞, SheafHom•_𝒪(K^n, J))) ⟶ RΓ(𝒞, R𝑆heafHom_𝒪(K^n, J))` is invertible.

The Koszul complex is K-flat, so `SheafHom•_𝒪(K^n, J)` is itself K-injective by
[Stacks, Tag 0A96], and `Γ(𝒞, -)` computes `RΓ(𝒞, -)` there. This is the statement that the
proof of the identity of [Stacks, Tag 0BLX] needs at an arbitrary number `r` of sections, and
that `Stacks.Cohomology.KoszulTowerSections.nonempty_iso_koszulTower_derivedSections` obtains
at `r = 1` from `CochainComplex.isKInjective_mappingCone`. -/
theorem isIso_moduleGlobalSectionsDerivedUnit_app_sheafHomComplex_koszulPowerComplex (n : ℕ)
    (J : CochainComplex (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ℤ)
    [J.IsKInjective] :
    IsIso ((moduleGlobalSectionsDerivedUnit X A ρ).app
      (sheafHomComplex X (koszulPowerComplex X f n) J).obj) :=
  isIso_moduleGlobalSectionsDerivedUnit_app X A ρ
    (sheafHomComplex X (koszulPowerComplex X f n) J).obj
    (isKInjective_sheafHomComplex_koszulPowerComplex X f n J)

end GlobalSections

end AlgebraicGeometry.RingedSite

end
