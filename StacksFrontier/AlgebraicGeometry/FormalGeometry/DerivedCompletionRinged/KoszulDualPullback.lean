module

public import
StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulDualCoefficientComplex
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulPullbackDerived
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ProjectionFormulaSingleUnit
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ProjectionFormulaStrictlyPerfect

/-!
# The derived pullback of the Koszul dual

Let `f : (Sh(𝒟), 𝒪') ⟶ (Sh(𝒞), 𝒪)` be a morphism of ringed sites, let `t_1, …, t_r` be global
sections of `𝒪` and let `g_1, …, g_r` be global sections of `𝒪'` with `g_i = f^♯(t_i)`, and let
`K^n = K(𝒪, t_1^{n+1}, …, t_r^{n+1})` be the Koszul complex of [Stacks, Tag 0913]. This file
identifies the derived pullback of the `𝒪`-**dual**

`Lf^*((K^n)^∨) ≅ (Lf^*K^n)^∨ = (K(𝒪', g_1^{n+1}, …, g_r^{n+1}))^∨`,

naturally in `n` for the transitions `(K^{n+1})^∨ ⟶ (K^n)^∨` of the dual tower.

This is the identification the proof of [Stacks, Tag 0A0G] uses alongside the projection
formula [Stacks, Tag 0944]: the tower of the Koszul formula of [Stacks, Tag 0A0E] is
`n ↦ K ⊗^𝐋_𝒪 (K^n)^∨`, so what the projection formula has to be fed is the derived pullback of
the dual, not of the Koszul complex itself. The latter is
`AlgebraicGeometry.RingedSite.derivedPullbackKoszulPowerComplexIso`, and it does **not** give
this: the dual lives in degrees `-r, …, 0` and the Koszul complex in degrees `0, …, r`.

## The shape of the proof

The Koszul complex is self-dual up to the shift by `r` and a sign twist, and that self-duality
is already available with coefficients:
`AlgebraicGeometry.RingedSite.koszulDualComplexIsoCoeff` of `KoszulDualCoefficientComplex.lean`
reads `SheafHom•_𝒪(K^n, ℱ[0]) ≅ (K(𝒪, t^{n+1}) ⊗ ℱ)[r]`. At `ℱ = 𝒪` its source is the dual
`(K^n)^∨` and its target is the `r`-fold shift of `K^n` itself, because
`AlgebraicGeometry.RingedSite.koszulPowerComplexOn_unit` identifies the Koszul complex with
coefficients in `𝒪` with the Koszul complex. So the dual of the Koszul complex carries no
information the Koszul complex does not, and the degreewise pullback of the dual is computed by
transporting `AlgebraicGeometry.RingedSite.pullbackKoszulPowerComplexIso` through that
self-duality and through the commutation of the inverse image with the shift,
`CategoryTheory.Functor.mapCochainComplexShiftIso` — the inverse image is additive, so it
commutes with the shift on cochain complexes with identity components.

Passing to the derived category is then the same step as for the Koszul complex itself: the
dual is strictly perfect —
`AlgebraicGeometry.RingedSite.isStrictlyPerfect_sheafHomComplex_koszulPowerComplex` — hence
K-flat with flat terms, so `Stacks.Sheaves.DerivedPullback.flatPullbackIso`, the computation
assertion of [Stacks, Tag 06YY], says its derived pullback is the class of its degreewise
pullback.

Both transitions of the dual tower are needed, and they are the two different things the dual
turns the Koszul tower into: the dual of the Koszul transition
`AlgebraicGeometry.RingedSite.koszulPowerComplexMap` is, under the self-duality, the **downward**
transition `AlgebraicGeometry.RingedSite.koszulDualComplexOnMap`, which multiplies the factor
indexed by `T` by `∏_{i ∉ T} t_i`. That the inverse image carries one to the other is
`AlgebraicGeometry.RingedSite.pullbackKoszulPowerFunctorIso_dualTrans` below, proved exactly as
`AlgebraicGeometry.RingedSite.pullbackKoszulPowerFunctorIso_trans` is, from
`AlgebraicGeometry.RingedSite.pullbackTopos_map_koszulScalar` at the exponent vector of the
complement.

## Main results

* `AlgebraicGeometry.RingedSite.pullbackKoszulPowerDualComplexIso`:
  **`f^*((K^n)^∨) ≅ (K(𝒪', g^{n+1}))^∨`** as complexes of `𝒪'`-modules, and
  `AlgebraicGeometry.RingedSite.pullbackKoszulPowerDualComplexIso_naturality`: it is compatible
  with the transitions of the two dual towers.
* `AlgebraicGeometry.RingedSite.pullbackKoszulSheafHomSystemIso`: the same as an isomorphism of
  towers of complexes.
* `AlgebraicGeometry.RingedSite.derivedPullbackKoszulPowerDualComplexIso`:
  **`Lf^*((K^n)^∨) ≅ (K(𝒪', g^{n+1}))^∨`** in `D(𝒪')`, with
  `AlgebraicGeometry.RingedSite.derivedPullbackKoszulPowerDualComplexIso_naturality` and
  `AlgebraicGeometry.RingedSite.derivedPullbackKoszulSheafHomSystemIso` for the naturality and
  the tower.
* `AlgebraicGeometry.RingedSite.derivedPullbackKoszulDerivedDualIso`: **the same read through
  the derived dual of [Stacks, Tag 08JD]**, `Lf^*(E^∨) ≅ (Lf^*E)^∨` at `E = K^n`, which is the
  form the projection formula against the Koszul duals consumes, and
  `AlgebraicGeometry.RingedSite.derivedPullbackKoszulDualSystemIso`: **the same as an
  isomorphism of towers of derived duals**, natural in `n`.
* `AlgebraicGeometry.RingedSite.isIso_projectionFormulaMap_koszulDerivedDual`:
  **[Stacks, Tag 0944] at the Koszul dual** — Equation 21.50.0.1 is invertible there, the dual
  being strictly perfect — and
  `AlgebraicGeometry.RingedSite.pushforwardKoszulDualSystemProjectionIso`: **the projection
  formula against the whole dual Koszul tower**,
  `Rf_*K ⊗^𝐋_𝒪 (K^n)^∨ ≅ Rf_*(K ⊗^𝐋_{𝒪'} (K'^n)^∨)`, naturally in `n`. This is the
  display that the source's proof of [Stacks, Tag 0A0G] compares its two sides by.

## Implementation notes

Nothing here carries a `@[stacks]` attribute: the identification is an input to the proofs of
[Stacks, Tag 0A0G] and [Stacks, Tag 0944], not a tag of its own.

`koszulPowerComplexOn X t (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) n`
and `koszulPowerComplex X t n` are equal by `rfl` but not syntactically, and so are
`singleSheafComplex X (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))` and
`structureSheafComplex X`. A goal mixing the two spellings is not type-correct at the
transparency at which `rw` checks its motive, with the symptom that every rewrite fails with "did
not find an occurrence" while the pattern is in plain sight. The naturality square is therefore
assembled in term mode out of four squares by `Stacks.Sheaves.DerivedPullback.trans_naturality`,
and the one step that would need a rewrite under a functor is written as a composite of
`Functor.map_comp` and `congrArg` instead.

## References

* [Stacks Project, Tag 0913](https://stacks.math.columbia.edu/tag/0913)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 08JD](https://stacks.math.columbia.edu/tag/08JD)
* [Stacks Project, Tag 0944](https://stacks.math.columbia.edu/tag/0944)
* [Stacks Project, Tag 0A0E](https://stacks.math.columbia.edu/tag/0A0E)
* [Stacks Project, Tag 0A0G](https://stacks.math.columbia.edu/tag/0A0G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] hasFiniteBiproducts_sheafOfModules
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

/-! ## The degreewise inverse image of the dual -/

section Complex

variable {X Y : RingedSite.{u, u, u}}
  [HasSheafify X.J AddCommGrpCat.{u}] [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [HasWeakSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify Y.J CommRingCat.{u}] [HasWeakSheafify X.J CommRingCat.{u}]
  (f : RingedSite.Hom X Y) {r : ℕ}
  (t : Fin r → Presheaf.globalSections (Y.O.obj ⋙ forget CommRingCat.{u}))
  (g : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))
  (hg : PushGlobalSectionsCompatible f t g)

include hg in
omit [HasSheafify X.J AddCommGrpCat.{u}] [HasSheafify Y.J AddCommGrpCat.{u}]
  [HasWeakSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify Y.J CommRingCat.{u}] [HasWeakSheafify X.J CommRingCat.{u}] in
/-- **The comparison of the two systems of copies of the structure sheaf is compatible with the
downward transitions of the two dual Koszul towers.** On either side the transition at the
subset `T` is multiplication by the monomial indexed by the complement of `T`, so this is
`AlgebraicGeometry.RingedSite.pullbackTopos_map_koszulScalar` at that exponent vector, exactly
as `AlgebraicGeometry.RingedSite.pullbackKoszulPowerFunctorIso_trans` is at the exponent vector
of `T` itself. -/
theorem pullbackKoszulPowerFunctorIso_dualTrans (m : ℕ) :
    Functor.whiskerRight (koszulDualTransOn Y t
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) m)
          f.toRingedToposSiteHom.pullbackTopos ≫
        (pullbackKoszulPowerFunctorIso f t g hg m).hom =
      (pullbackKoszulPowerFunctorIso f t g hg (m + 1)).hom ≫
        koszulDualTransOn X g
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) m := by
  refine NatTrans.ext (funext fun T => ?_)
  exact pullbackTopos_map_koszulScalar f t g hg (fun i => if i ∈ Tᶜ then 1 else 0)

include hg in
omit [HasSheafify X.J AddCommGrpCat.{u}] [HasSheafify Y.J AddCommGrpCat.{u}]
  [HasWeakSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify Y.J CommRingCat.{u}] [HasWeakSheafify X.J CommRingCat.{u}] in
/-- **The inverse image carries the downward transition of one Koszul tower to the downward
transition of the other.** -/
theorem pullbackKoszulPowerComplexIso_dualTrans (m : ℕ) :
    (f.toRingedToposSiteHom.pullbackTopos.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (koszulDualComplexOnMap Y t
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) m) ≫
        (pullbackKoszulPowerComplexIso f t g hg m).hom =
      (pullbackKoszulPowerComplexIso f t g hg (m + 1)).hom ≫
        koszulDualComplexOnMap X g
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) m :=
  AlternatingCech.mapComplexIso_trans_mapIso_map f.toRingedToposSiteHom.pullbackTopos
    (koszulDualTransOn Y t (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) m)
    (pullbackKoszulPowerFunctorIso f t g hg (m + 1))
    (pullbackKoszulPowerFunctorIso f t g hg m)
    (koszulDualTransOn X g (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) m)
    (pullbackKoszulPowerFunctorIso_dualTrans f t g hg m)

include hg in
/-- **The inverse image of the `𝒪`-dual of the Koszul complex on the `(n+1)`-st powers of
`t_1, …, t_r` is the `𝒪'`-dual of the Koszul complex on the `(n+1)`-st powers of
`g_1, …, g_r`.**

Both duals are, by the self-duality
`AlgebraicGeometry.RingedSite.koszulDualComplexIsoCoeff` at the structure sheaf, the `r`-fold
shifts of the two Koszul complexes; the inverse image commutes with the shift, and it carries
one Koszul complex to the other by
`AlgebraicGeometry.RingedSite.pullbackKoszulPowerComplexIso`. -/
def pullbackKoszulPowerDualComplexIso (n : ℕ) :
    (f.toRingedToposSiteHom.pullbackTopos.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (sheafHomComplex Y (koszulPowerComplex Y t n) (structureSheafComplex Y)).obj ≅
      (sheafHomComplex X (koszulPowerComplex X g n) (structureSheafComplex X)).obj :=
  (f.toRingedToposSiteHom.pullbackTopos.mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
      (koszulDualComplexIsoCoeff Y t
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) n) ≪≫
    (f.toRingedToposSiteHom.pullbackTopos.mapCochainComplexShiftIso (r : ℤ)).app
      (koszulPowerComplex Y t n) ≪≫
    (shiftFunctor
        (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
        (r : ℤ)).mapIso
      (pullbackKoszulPowerComplexIso f t g hg n) ≪≫
    (koszulDualComplexIsoCoeff X g
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) n).symm

/-- A functor carries a commuting square given as an equality of composites to a commuting
square. -/
private theorem map_comp_eq_map_comp_of_comp_eq {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {P Q R S : C} {a : P ⟶ Q} {b : Q ⟶ S} {c : P ⟶ R} {d : R ⟶ S}
    (h : a ≫ b = c ≫ d) : F.map a ≫ F.map b = F.map c ≫ F.map d := by
  simp only [← F.map_comp, h]

include hg in
omit [HasSheafify X.J AddCommGrpCat.{u}] [HasSheafify Y.J AddCommGrpCat.{u}]
  [HasWeakSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The identification is compatible with the transitions of the two dual towers**, which are
the duals of the transitions of the two Koszul towers. -/
theorem pullbackKoszulPowerDualComplexIso_naturality (m : ℕ) :
    (f.toRingedToposSiteHom.pullbackTopos.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (homMap Y (koszulPowerComplexMap Y t m) (𝟙 (structureSheafComplex Y))) ≫
        (pullbackKoszulPowerDualComplexIso f t g hg m).hom =
      (pullbackKoszulPowerDualComplexIso f t g hg (m + 1)).hom ≫
        homMap X (koszulPowerComplexMap X g m) (𝟙 (structureSheafComplex X)) := by
  have h1 := map_comp_eq_map_comp_of_comp_eq
    (f.toRingedToposSiteHom.pullbackTopos.mapHomologicalComplex (ComplexShape.up ℤ))
    (koszulDualComplexIsoCoeff_trans Y t
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) m)
  have h2 := (f.toRingedToposSiteHom.pullbackTopos.mapCochainComplexShiftIso
    (r : ℤ)).hom.naturality (koszulDualComplexOnMap Y t
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) m)
  have h3 := map_comp_eq_map_comp_of_comp_eq
    (shiftFunctor
      (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
      (r : ℤ))
    (pullbackKoszulPowerComplexIso_dualTrans f t g hg m)
  have h4 : (shiftFunctor
        (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
        (r : ℤ)).map
          (koszulDualComplexOnMap X g
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) m) ≫
        (koszulDualComplexIsoCoeff X g
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) m).inv =
      (koszulDualComplexIsoCoeff X g
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (m + 1)).inv ≫
        homMap X (koszulPowerComplexMap X g m) (𝟙 (structureSheafComplex X)) := by
    rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq]
    exact (koszulDualComplexIsoCoeff_trans X g
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) m).symm
  exact Stacks.Sheaves.DerivedPullback.trans_naturality h1
    (Stacks.Sheaves.DerivedPullback.trans_naturality h2
      (Stacks.Sheaves.DerivedPullback.trans_naturality h3 h4))

include hg in
/-- **The inverse image carries the tower of `𝒪`-duals of the Koszul complexes to the tower of
`𝒪'`-duals**, compatibly with the transitions. -/
def pullbackKoszulSheafHomSystemMap :
    koszulSheafHomSystemOf Y t (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⋙
        f.toRingedToposSiteHom.pullbackTopos.mapHomologicalComplex (ComplexShape.up ℤ) ⟶
      koszulSheafHomSystemOf X g
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  NatTrans.ofOpSequence
    (fun m => (pullbackKoszulPowerDualComplexIso f t g hg m).hom) fun m => by
    rw [show (koszulSheafHomSystemOf Y t
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⋙
          f.toRingedToposSiteHom.pullbackTopos.mapHomologicalComplex
            (ComplexShape.up ℤ)).map (homOfLE (Nat.le_add_right m 1)).op =
        (f.toRingedToposSiteHom.pullbackTopos.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((koszulSheafHomSystemOf Y t
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
            (homOfLE (Nat.le_add_right m 1)).op) from rfl,
      koszulSheafHomSystemOf_map_succ, koszulSheafHomSystemOf_map_succ]
    exact pullbackKoszulPowerDualComplexIso_naturality f t g hg m

include hg in
omit [HasSheafify X.J AddCommGrpCat.{u}] [HasSheafify Y.J AddCommGrpCat.{u}]
  [HasWeakSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The map of towers `pullbackKoszulSheafHomSystemMap` from the inverse image of the tower of
`𝒪`-duals of the Koszul complexes to the tower of `𝒪'`-duals is an isomorphism. -/
theorem isIso_pullbackKoszulSheafHomSystemMap :
    IsIso (pullbackKoszulSheafHomSystemMap f t g hg) := by
  have hi (m : ℕᵒᵖ) : IsIso ((pullbackKoszulSheafHomSystemMap f t g hg).app m) := by
    change IsIso (pullbackKoszulPowerDualComplexIso f t g hg m.unop).hom
    infer_instance
  exact NatIso.isIso_of_isIso_app _

include hg in
/-- **The inverse image carries one tower of Koszul duals to the other**, as an isomorphism of
towers of complexes. -/
def pullbackKoszulSheafHomSystemIso :
    koszulSheafHomSystemOf Y t (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⋙
        f.toRingedToposSiteHom.pullbackTopos.mapHomologicalComplex (ComplexShape.up ℤ) ≅
      koszulSheafHomSystemOf X g
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  @asIso _ _ _ _ (pullbackKoszulSheafHomSystemMap f t g hg)
    (isIso_pullbackKoszulSheafHomSystemMap f t g hg)

end Complex

/-! ## The derived pullback of the dual -/

section Derived

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] hasLeftDerivedFunctor_pullbackOnHomotopy

open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

variable {X Y : RingedSite.{u, u, u}}
  [HasSheafify X.J AddCommGrpCat.{u}] [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [HasWeakSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} Y.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} Y.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]
  [HasWeakSheafify Y.J CommRingCat.{u}] [HasWeakSheafify X.J CommRingCat.{u}]
  (f : RingedSite.Hom X Y) {r : ℕ}
  (t : Fin r → Presheaf.globalSections (Y.O.obj ⋙ forget CommRingCat.{u}))
  (g : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))
  (hg : PushGlobalSectionsCompatible f t g)

include hg in
/-- **`Lf^*((K^n)^∨) ≅ (K(𝒪', g^{n+1}))^∨`.** The `𝒪`-dual of the Koszul complex is strictly
perfect, hence K-flat with flat terms, so its derived pullback is the class of its degreewise
pullback, and that is the `𝒪'`-dual of the Koszul complex on the pushed-forward sections. -/
def derivedPullbackKoszulPowerDualComplexIso (n : ℕ) :
    (derivedPullback.{u} f.toRingedToposSiteHom).obj
        (DerivedCategory.Q.obj
          (sheafHomComplex Y (koszulPowerComplex Y t n) (structureSheafComplex Y)).obj) ≅
      DerivedCategory.Q.obj
        (sheafHomComplex X (koszulPowerComplex X g n) (structureSheafComplex X)).obj :=
  Stacks.Sheaves.DerivedPullback.flatPullbackIso f.toRingedToposSiteHom f.isMorphismOfSites
      (sheafHomComplex Y (koszulPowerComplex Y t n) (structureSheafComplex Y)).obj
      (isKFlat_koszulPowerDualComplex Y t n)
      (fun i => Stacks.SheafOfModules.isFlat_X_of_isStrictlyPerfect
        (isStrictlyPerfect_sheafHomComplex_koszulPowerComplex Y t n) i) ≪≫
    DerivedCategory.Q.mapIso (pullbackKoszulPowerDualComplexIso f t g hg n)

include hg in
/-- **The identification is compatible with the transitions of the two dual towers.** -/
theorem derivedPullbackKoszulPowerDualComplexIso_naturality (m : ℕ) :
    (derivedPullback.{u} f.toRingedToposSiteHom).map
          (DerivedCategory.Q.map
            (homMap Y (koszulPowerComplexMap Y t m) (𝟙 (structureSheafComplex Y)))) ≫
        (derivedPullbackKoszulPowerDualComplexIso f t g hg m).hom =
      (derivedPullbackKoszulPowerDualComplexIso f t g hg (m + 1)).hom ≫
        DerivedCategory.Q.map
          (homMap X (koszulPowerComplexMap X g m) (𝟙 (structureSheafComplex X))) :=
  Stacks.Sheaves.DerivedPullback.trans_naturality
    (Stacks.Sheaves.DerivedPullback.flatPullbackIso_naturality f.toRingedToposSiteHom
      f.isMorphismOfSites (homMap Y (koszulPowerComplexMap Y t m) (𝟙 (structureSheafComplex Y)))
      (isKFlat_koszulPowerDualComplex Y t (m + 1)) (isKFlat_koszulPowerDualComplex Y t m)
      (fun i => Stacks.SheafOfModules.isFlat_X_of_isStrictlyPerfect
        (isStrictlyPerfect_sheafHomComplex_koszulPowerComplex Y t (m + 1)) i)
      (fun i => Stacks.SheafOfModules.isFlat_X_of_isStrictlyPerfect
        (isStrictlyPerfect_sheafHomComplex_koszulPowerComplex Y t m) i))
    (map_comp_eq_map_comp_of_comp_eq DerivedCategory.Q
      (pullbackKoszulPowerDualComplexIso_naturality f t g hg m))

include hg in
/-- **The derived pullback carries the tower of Koszul duals to the tower of Koszul duals**,
compatibly with the transitions. -/
def derivedPullbackKoszulSheafHomSystemMap :
    koszulSheafHomSystemOf Y t
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⋙ DerivedCategory.Q ⋙
        derivedPullback.{u} f.toRingedToposSiteHom ⟶
      koszulSheafHomSystemOf X g
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⋙ DerivedCategory.Q :=
  NatTrans.ofOpSequence
    (fun m => (derivedPullbackKoszulPowerDualComplexIso f t g hg m).hom) fun m => by
    rw [show (koszulSheafHomSystemOf Y t
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⋙
          DerivedCategory.Q ⋙
          derivedPullback.{u} f.toRingedToposSiteHom).map
            (homOfLE (Nat.le_add_right m 1)).op =
        (derivedPullback.{u} f.toRingedToposSiteHom).map (DerivedCategory.Q.map
          ((koszulSheafHomSystemOf Y t
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
            (homOfLE (Nat.le_add_right m 1)).op)) from rfl,
      show (koszulSheafHomSystemOf X g
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⋙
          DerivedCategory.Q).map (homOfLE (Nat.le_add_right m 1)).op =
        DerivedCategory.Q.map
          ((koszulSheafHomSystemOf X g
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).map
            (homOfLE (Nat.le_add_right m 1)).op) from rfl,
      koszulSheafHomSystemOf_map_succ, koszulSheafHomSystemOf_map_succ]
    exact derivedPullbackKoszulPowerDualComplexIso_naturality f t g hg m

include hg in
/-- The map of towers `derivedPullbackKoszulSheafHomSystemMap` from the derived pullback of the
tower of Koszul duals to the tower of Koszul duals in `D(𝒪')` is an isomorphism. -/
theorem isIso_derivedPullbackKoszulSheafHomSystemMap :
    IsIso (derivedPullbackKoszulSheafHomSystemMap f t g hg) := by
  have hi (m : ℕᵒᵖ) : IsIso ((derivedPullbackKoszulSheafHomSystemMap f t g hg).app m) := by
    change IsIso (derivedPullbackKoszulPowerDualComplexIso f t g hg m.unop).hom
    infer_instance
  exact NatIso.isIso_of_isIso_app _

include hg in
/-- **The derived pullback carries one tower of Koszul duals to the other**, as an isomorphism
of towers in `D(𝒪')`. -/
def derivedPullbackKoszulSheafHomSystemIso :
    koszulSheafHomSystemOf Y t
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⋙ DerivedCategory.Q ⋙
        derivedPullback.{u} f.toRingedToposSiteHom ≅
      koszulSheafHomSystemOf X g
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⋙ DerivedCategory.Q :=
  @asIso _ _ _ _ (derivedPullbackKoszulSheafHomSystemMap f t g hg)
    (isIso_derivedPullbackKoszulSheafHomSystemMap f t g hg)

include hg in
/-- **`Lf^*(E^∨) ≅ (Lf^*E)^∨` at the Koszul complex `E = K^n`**, for the derived dual
`E^∨ = R𝑆heafHom(E, 𝒪)` of [Stacks, Tag 08JD].

The derived dual of the Koszul complex is represented by the internal Hom complex
`SheafHom•_𝒪(K^n, 𝒪[0])` — that is [Stacks, Tag 08JH] at a Koszul source,
`AlgebraicGeometry.RingedSite.koszulDerivedSheafHomComplexIso` — on either site, and the derived
pullback carries one to the other by
`AlgebraicGeometry.RingedSite.derivedPullbackKoszulPowerDualComplexIso`; the target is then read
back through `AlgebraicGeometry.RingedSite.derivedPullbackKoszulPowerComplexIso`, the derived
pullback of the Koszul complex itself. -/
def derivedPullbackKoszulDerivedDualIso (n : ℕ) :
    (derivedPullback.{u} f.toRingedToposSiteHom).obj
        (derivedDual Y (DerivedCategory.Q.obj (koszulPowerComplex Y t n))) ≅
      derivedDual X ((derivedPullback.{u} f.toRingedToposSiteHom).obj
        (DerivedCategory.Q.obj (koszulPowerComplex Y t n))) :=
  (derivedPullback.{u} f.toRingedToposSiteHom).mapIso
      (koszulDerivedSheafHomComplexIso Y (derivedInternalHomOfBifunctor Y) t n
        (structureSheafComplex Y)).symm ≪≫
    derivedPullbackKoszulPowerDualComplexIso f t g hg n ≪≫
    koszulDerivedSheafHomComplexIso X (derivedInternalHomOfBifunctor X) g n
      (structureSheafComplex X) ≪≫
    ((derivedSheafHomBifunctor X).mapIso
      (derivedPullbackKoszulPowerComplexIso f t g hg n).op).app (derivedStructureSheaf X)

end Derived

/-! ## The derived pullback of the dual tower -/

section DualSystem

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] hasLeftDerivedFunctor_pullbackOnHomotopy

open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

variable {X Y : RingedSite.{u, u, u}}
  [HasSheafify X.J AddCommGrpCat.{u}] [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [HasSheafify Y.J AddCommGrpCat.{u}] [HasWeakSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} Y.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} Y.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]
  [HasWeakSheafify Y.J CommRingCat.{u}] [HasWeakSheafify X.J CommRingCat.{u}]
  (f : RingedSite.Hom X Y) {r : ℕ}
  (t : Fin r → Presheaf.globalSections (Y.O.obj ⋙ forget CommRingCat.{u}))
  (g : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))
  (hg : PushGlobalSectionsCompatible f t g)

include hg in
/-- **`Lf^*` carries the tower of Koszul duals to the tower of Koszul duals**, as an isomorphism
of towers `ℕᵒᵖ ⥤ D(𝒪')` of *derived* duals:

`Lf^*(R𝑆heafHom_𝒪(K(𝒪, t^{n+1}), 𝒪)) ≅ R𝑆heafHom_{𝒪'}(K(𝒪', g^{n+1}), 𝒪')`, naturally in `n`.

This is `AlgebraicGeometry.RingedSite.derivedPullbackKoszulDerivedDualIso` made natural in `n`.
The bridge from the internal Hom complexes to the derived internal Homs is already natural in
`n`: it is `AlgebraicGeometry.RingedSite.koszulDerivedSheafHomSystemComparison`, the tower form
of [Stacks, Tag 08JH] at a Koszul source, read at the coefficient sheaf `𝒪` — where
`AlgebraicGeometry.RingedSite.koszulSheafHomSystemOf X g 𝒪` is the tower of `𝒪`-duals and
`Q(𝒪[0])` is `AlgebraicGeometry.RingedSite.derivedStructureSheaf`. Between the two bridges sits
`AlgebraicGeometry.RingedSite.derivedPullbackKoszulSheafHomSystemIso`.

This is the form in which the projection formula [Stacks, Tag 0944] consumes the identification
in the proof of [Stacks, Tag 0A0G]: the tower of that proof is `n ↦ K ⊗^𝐋_𝒪 (K^n)^∨`, so what
has to be natural in `n` is the pulled-back **dual**. -/
def derivedPullbackKoszulDualSystemIso :
    derivedSheafHomSystem Y (koszulPowerSystem Y t ⋙ DerivedCategory.Q)
          (derivedStructureSheaf Y) ⋙
        derivedPullback.{u} f.toRingedToposSiteHom ≅
      derivedSheafHomSystem X (koszulPowerSystem X g ⋙ DerivedCategory.Q)
        (derivedStructureSheaf X) :=
  Functor.isoWhiskerRight
      (asIso (koszulDerivedSheafHomSystemComparison Y t
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))).symm
      (derivedPullback.{u} f.toRingedToposSiteHom) ≪≫
    derivedPullbackKoszulSheafHomSystemIso f t g hg ≪≫
    asIso (koszulDerivedSheafHomSystemComparison X g
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))

end DualSystem

/-! ## The projection formula against the dual Koszul tower -/

section ProjectionFormula

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] hasLeftDerivedFunctor_pullbackOnHomotopy

open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.Cohomology.ProjectionFormulaOnRingedTopoi
open Stacks.Cohomology.ProjectionFormulaPerfectOnRingedTopoi

variable {X Y : RingedSite.{u, u, u}}
  [HasSheafify X.J AddCommGrpCat.{u}] [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [HasSheafify Y.J AddCommGrpCat.{u}] [HasWeakSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} Y.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} Y.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]
  [HasWeakSheafify Y.J CommRingCat.{u}] [HasWeakSheafify X.J CommRingCat.{u}]
  (f : RingedSite.Hom X Y) {r : ℕ}
  (t : Fin r → Presheaf.globalSections (Y.O.obj ⋙ forget CommRingCat.{u}))
  (g : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))
  (hg : PushGlobalSectionsCompatible f t g)

omit [HasWeakSheafify Y.J CommRingCat.{u}] [HasWeakSheafify X.J CommRingCat.{u}] in
/-- **[Stacks, Tag 0944] at the `𝒪`-dual of the Koszul complex.** Equation 21.50.0.1 of
[Stacks, Tag 0B56],

`Rf_*K ⊗^𝐋_𝒪 (K^n)^∨ ⟶ Rf_*(K ⊗^𝐋_{𝒪'} Lf^*((K^n)^∨))`,

is invertible for every `K` in `D(𝒪')`.

The dual `(K^n)^∨ = R𝑆heafHom_𝒪(K^n, 𝒪)` is the class of the internal Hom complex
`SheafHom•_𝒪(K^n, 𝒪[0])` ([Stacks, Tag 08JH] at a Koszul source,
`AlgebraicGeometry.RingedSite.koszulDerivedSheafHomComplexIso`), and that complex is strictly
perfect by `AlgebraicGeometry.RingedSite.isStrictlyPerfect_sheafHomComplex_koszulPowerComplex`;
so this is
`Stacks.Cohomology.ProjectionFormulaOnRingedTopoi.isIso_projectionFormulaMap_isStrictlyPerfect`
at the zeroth shift, transported along that identification by
`Stacks.Cohomology.ProjectionFormulaPerfectOnRingedTopoi.isIso_projectionFormulaMap_congr_target`.
Nothing is assumed beyond `f` being a morphism of ringed sites. -/
theorem isIso_projectionFormulaMap_koszulDerivedDual
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (n : ℕ) :
    IsIso (projectionFormulaMap f.toRingedToposSiteHom f.isMorphismOfSites K
      (derivedDual Y (DerivedCategory.Q.obj (koszulPowerComplex Y t n)))) :=
  (isIso_projectionFormulaMap_congr_target f.toRingedToposSiteHom f.isMorphismOfSites K
    ((shiftFunctorZero
        (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) ℤ).app
        (DerivedCategory.Q.obj
          (sheafHomComplex Y (koszulPowerComplex Y t n) (structureSheafComplex Y)).obj) ≪≫
      koszulDerivedSheafHomComplexIso Y (derivedInternalHomOfBifunctor Y) t n
        (structureSheafComplex Y))).1
    (isIso_projectionFormulaMap_isStrictlyPerfect f.toRingedToposSiteHom f.isMorphismOfSites K
      (sheafHomComplex Y (koszulPowerComplex Y t n) (structureSheafComplex Y)).obj
      (isStrictlyPerfect_sheafHomComplex_koszulPowerComplex Y t n) 0)

omit [HasWeakSheafify Y.J CommRingCat.{u}] [HasWeakSheafify X.J CommRingCat.{u}] in
/-- **The projection formula is invertible at every level of the dual Koszul tower at once.**
The components of the whiskering are the maps of
`AlgebraicGeometry.RingedSite.isIso_projectionFormulaMap_koszulDerivedDual`. -/
theorem isIso_whiskerLeft_projectionFormulaTransformation
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    IsIso (Functor.whiskerLeft
      (derivedSheafHomSystem Y (koszulPowerSystem Y t ⋙ DerivedCategory.Q)
        (derivedStructureSheaf Y))
      (projectionFormulaTransformation f.toRingedToposSiteHom f.isMorphismOfSites K)) := by
  have h (n : ℕᵒᵖ) : IsIso ((Functor.whiskerLeft
      (derivedSheafHomSystem Y (koszulPowerSystem Y t ⋙ DerivedCategory.Q)
        (derivedStructureSheaf Y))
      (projectionFormulaTransformation f.toRingedToposSiteHom f.isMorphismOfSites K)).app n) := by
    change IsIso (projectionFormulaMap f.toRingedToposSiteHom f.isMorphismOfSites K
      (derivedDual Y (DerivedCategory.Q.obj (koszulPowerComplex Y t n.unop))))
    exact isIso_projectionFormulaMap_koszulDerivedDual f t K n.unop
  exact NatIso.isIso_of_isIso_app _

include hg in
/-- **The projection formula against the whole dual Koszul tower**, as an isomorphism of towers
`ℕᵒᵖ ⥤ D(𝒪)`:

`Rf_*K ⊗^𝐋_𝒪 (K(𝒪, t^{n+1}))^∨  ≅  Rf_*(K ⊗^𝐋_{𝒪'} (K(𝒪', g^{n+1}))^∨)`,  naturally in `n`,

for every `K` in `D(𝒪')`. This is the display by which the source's proof of
[Stacks, Tag 0A0G] compares the two sides of that tag, and it is exactly the composite of the
tag's two inputs: the projection formula [Stacks, Tag 0944] at the Koszul duals, invertible by
`AlgebraicGeometry.RingedSite.isIso_projectionFormulaMap_koszulDerivedDual` and natural in `n`
as the whiskering of
`Stacks.Cohomology.ProjectionFormulaPerfectOnRingedTopoi.projectionFormulaTransformation`; and
the identification of the pulled-back dual,
`AlgebraicGeometry.RingedSite.derivedPullbackKoszulDualSystemIso`, pushed through
`K ⊗^𝐋_{𝒪'} -` and `Rf_*`.

The derived tensor product here is `Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor`,
the one [Stacks, Tag 0944] is stated over, which is a different construction, made opaque with
`irreducible_def`, from the `Stacks.SheafOfModules.canonicalDerivedTensorProduct` of
`AlgebraicGeometry.RingedSite.tensorDerivedDualSystem`; their bifunctors are identified by
`AlgebraicGeometry.RingedSite.derivedTensorFunctorIso`, but no declaration of this library
transports this isomorphism of towers across that identification. The `hproj` hypothesis
of `nonempty_iso_derivedPushforward_derivedCompletion_generatedIdealSheaf_of_natIso` is stated
over the latter, and is discharged without the projection formula by
`AlgebraicGeometry.RingedSite.pushforwardKoszulTensorDualSystemIso`. -/
def pushforwardKoszulDualSystemProjectionIso
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    derivedSheafHomSystem Y (koszulPowerSystem Y t ⋙ DerivedCategory.Q)
          (derivedStructureSheaf Y) ⋙
        (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.O).obj
          ((derivedPushforward.{u} f.toRingedToposSiteHom).obj K) ≅
      derivedSheafHomSystem X (koszulPowerSystem X g ⋙ DerivedCategory.Q)
          (derivedStructureSheaf X) ⋙
        (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O).obj K ⋙
          derivedPushforward.{u} f.toRingedToposSiteHom :=
  @asIso _ _ _ _ (Functor.whiskerLeft
      (derivedSheafHomSystem Y (koszulPowerSystem Y t ⋙ DerivedCategory.Q)
        (derivedStructureSheaf Y))
      (projectionFormulaTransformation f.toRingedToposSiteHom f.isMorphismOfSites K))
      (isIso_whiskerLeft_projectionFormulaTransformation f t K) ≪≫
    Functor.isoWhiskerRight (derivedPullbackKoszulDualSystemIso f t g hg)
      ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O).obj K ⋙
        derivedPushforward.{u} f.toRingedToposSiteHom)

end ProjectionFormula

end AlgebraicGeometry.RingedSite

end
