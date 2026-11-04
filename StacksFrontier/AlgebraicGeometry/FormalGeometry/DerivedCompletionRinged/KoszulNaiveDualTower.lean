module

public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulCechHomotopyColimit
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulNaiveDualDegree
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.HomComplexCompositionComparison
public import StacksFrontier.CategoryTheory.Triangulated.DerivedLimitTriangulatedTower
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulDerivedTensorDual

/-!
# The tower of Stacks 0A0E through the naive dual

Let `(𝒞, 𝒪)` be a ringed site and let `f_1, …, f_r` be global sections of `𝒪`. The tower of
[Stacks, Tag 0A0E] is `n ↦ K ⊗^𝐋_𝒪 Kₙ^∨` with `Kₙ^∨ = R𝑆heafHom(K(𝒪, f^{n+1}), 𝒪)` the *derived*
dual of the Koszul complex, which is what
`AlgebraicGeometry.RingedSite.isDerivedLimit_tensorDerivedDualSystem_koszulPowerSystem` is stated
against. This file replaces that derived dual by the *naive* termwise dual, as a map of towers.

The single-stage replacement is `AlgebraicGeometry.RingedSite`'s
`derivedDualIsoSheafHomComplexUnit_koszulPowerComplex`, [Stacks, Tag 08JH] at the Koszul complex,
which is strictly perfect. What this file adds is that the single-stage isomorphisms are
compatible with the transition maps, so that they assemble into an isomorphism of *towers*: the
transition map of the derived-dual tower is `R𝑆heafHom(-, 𝒪)` applied to the transition map of the
Koszul system, the comparison of [Stacks, Tag 08JH] is natural in its source by
`AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison_naturality_source`, and the naive dual
of the Koszul tower is the Koszul terms with the transposed differential by
`AlgebraicGeometry.RingedSite.homMap_comp_koszulNaiveDualComplexIso_hom`.

## Main definitions

* `AlgebraicGeometry.RingedSite.koszulNaiveDualSystem` — the tower of naive duals of the Koszul
  complexes, as a tower of complexes: at `n` it is
  `AlgebraicGeometry.RingedSite.koszulNaiveDualComplex`, with the transition map
  `koszulNaiveDualComplexMap`.
* `AlgebraicGeometry.RingedSite.koszulDerivedDualSystem` — the tower of derived duals of the
  Koszul complexes, the tower of [Stacks, Tag 0A0E] before tensoring with `K`.
* `AlgebraicGeometry.RingedSite.koszulNaiveDualSystemIso` — **the two towers agree.**

## Main results

* `AlgebraicGeometry.RingedSite.koszulNaiveDualSystemIso_hom_app` — the characterising clause of
  that isomorphism: at `n` it is the single-stage comparison of [Stacks, Tag 08JH], followed by
  the degreewise identification of the naive dual.
* `isDerivedLimit_tensorDerivedDualSystem_koszulPowerSystem_completionFunctor` — the formula
  for the tower of derived duals, the input `hdual` of
  `AlgebraicGeometry.RingedSite.isDerivedLimit_tensorDerivedDualSystem_koszulPowerSystem` being
  supplied by `AlgebraicGeometry.RingedSite.isIso_derivedTensorDualToSheafHom_koszulPowerSystem`.
* `AlgebraicGeometry.RingedSite.isDerivedLimit_tensorKoszulNaiveDualSystem_koszulPowerSystem` —
  **[Stacks, Tag 0A0E] with the derived dual replaced by the naive one**: the completion
  `K^∧` of [Stacks, Tag 099B] is a derived limit of the tower
  `n ↦ K ⊗^𝐋_𝒪 SheafHom(K(𝒪, f^{n+1}), 𝒪)`.

## Implementation notes

The derived-dual tower is written as
`(koszulPowerSystem X f ⋙ Q).op ⋙ (derivedSheafHomBifunctor X).flip.obj (derivedStructureSheaf X)`
rather than with `AlgebraicGeometry.RingedSite.derivedDual` spelled out at each stage, because
that is the shape `AlgebraicGeometry.RingedSite.tensorDerivedDualSystem` has: the tower of
[Stacks, Tag 0A0E] is this one composed with `T.tensor.obj K`, on the nose, so the isomorphism
below whiskers onto it with no comparison of models.

The naturality is proved only for the transition maps `n + 1 ⟶ n`, through
`CategoryTheory.NatTrans.ofOpSequence`; the two towers are both built from sequences, so that is
all there is to check. `AlgebraicGeometry.RingedSite.derivedDualIsoSheafHomComplexUnit_hom`
records that the single-stage isomorphism *is* the comparison of [Stacks, Tag 08JH], which is
what lets its naturality lemma be applied to it.

## References

* [Stacks Project, Tag 0A0E](https://stacks.math.columbia.edu/tag/0A0E)
* [Stacks Project, Tag 08JH](https://stacks.math.columbia.edu/tag/08JH)
* [Stacks Project, Tag 099B](https://stacks.math.columbia.edu/tag/099B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {r : ℕ} (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

/-! ### The two towers -/

/-- **The tower of naive termwise duals of the Koszul complexes.** At `n` it is
`AlgebraicGeometry.RingedSite.koszulNaiveDualComplex`, the Koszul terms with the transposed
differential, and its transition map is `koszulNaiveDualComplexMap`. -/
def koszulNaiveDualSystem :
    ℕᵒᵖ ⥤ CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ :=
  Functor.ofOpSequence fun n => koszulNaiveDualComplexMap X f n

/-- The `n`-th term of `koszulNaiveDualSystem` is `koszulNaiveDualComplex X f n`. -/
@[simp]
theorem koszulNaiveDualSystem_obj (n : ℕ) :
    (koszulNaiveDualSystem X f).obj ⟨n⟩ = koszulNaiveDualComplex X f n :=
  rfl

/-- The transition map `n + 1 ⟶ n` of `koszulNaiveDualSystem` is
`koszulNaiveDualComplexMap X f n`. -/
@[simp]
theorem koszulNaiveDualSystem_map_succ (n : ℕ) :
    (koszulNaiveDualSystem X f).map (homOfLE (n.le_add_right 1)).op =
      koszulNaiveDualComplexMap X f n :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

/-- **The tower of derived duals of the Koszul complexes**, the tower of [Stacks, Tag 0A0E]
before tensoring: at `n` it is `Kₙ^∨ = R𝑆heafHom(K(𝒪, f^{n+1}), 𝒪)`. It is written in the shape
`AlgebraicGeometry.RingedSite.tensorDerivedDualSystem` has, so that the tower of the source is
this one composed with `T.tensor.obj K`. -/
abbrev koszulDerivedDualSystem :
    ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  (koszulPowerSystem X f ⋙ DerivedCategory.Q).op ⋙
    (derivedSheafHomBifunctor X).flip.obj (derivedStructureSheaf X)

/-- The transition map of `AlgebraicGeometry.RingedSite.koszulDerivedDualSystem` is
`R𝑆heafHom(-, 𝒪)` applied to the transition map of the Koszul system. -/
theorem koszulDerivedDualSystem_map_succ (n : ℕ) :
    (koszulDerivedDualSystem X f).map (homOfLE (n.le_add_right 1)).op =
      ((derivedSheafHomBifunctor X).map
        (DerivedCategory.Q.map (koszulPowerComplexMap X f n)).op).app
          (derivedStructureSheaf X) :=
  congrArg (fun φ : koszulPowerComplex X f n ⟶ koszulPowerComplex X f (n + 1) =>
      ((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map φ).op).app
        (derivedStructureSheaf X))
    (koszulPowerSystem_map_succ X f n)

/-! ### The two towers agree -/

/-- **The derived dual of the `n`-th Koszul complex is its naive termwise dual, read on the
Koszul terms.** This is the single-stage comparison
`AlgebraicGeometry.RingedSite.derivedDualIsoSheafHomComplexUnit_koszulPowerComplex` of
[Stacks, Tag 08JH], followed by the degreewise identification
`AlgebraicGeometry.RingedSite.koszulNaiveDualComplexIso`. -/
def koszulNaiveDualTowerDegreeIso (n : ℕ) :
    (koszulDerivedDualSystem X f).obj ⟨n⟩ ≅
      (koszulNaiveDualSystem X f ⋙ DerivedCategory.Q).obj ⟨n⟩ :=
  (derivedDualIsoSheafHomComplexUnit_koszulPowerComplex X f n).symm ≪≫
    DerivedCategory.Q.mapIso (koszulNaiveDualComplexIso X f n)

/-- The degreewise identifications are compatible with the transition maps of the two towers.
Its three inputs are: that the single-stage comparison is the one of [Stacks, Tag 08JH]
(`derivedDualIsoSheafHomComplexUnit_hom`), that this comparison is natural in its source
(`strictlyPerfectHomComparison_naturality_source`), and that the degreewise identification of
the naive dual is compatible with the dualized transition map
(`homMap_comp_koszulNaiveDualComplexIso_hom`). -/
theorem koszulNaiveDualTowerDegreeIso_naturality (n : ℕ) :
    (koszulDerivedDualSystem X f).map (homOfLE (n.le_add_right 1)).op ≫
        (koszulNaiveDualTowerDegreeIso X f n).hom =
      (koszulNaiveDualTowerDegreeIso X f (n + 1)).hom ≫
        (koszulNaiveDualSystem X f ⋙ DerivedCategory.Q).map
          (homOfLE (n.le_add_right 1)).op := by
  have hnat : DerivedCategory.Q.map (homMap X (koszulPowerComplexMap X f n)
          (𝟙 (structureSheafComplex X))) ≫
        (derivedDualIsoSheafHomComplexUnit_koszulPowerComplex X f n).hom =
      (derivedDualIsoSheafHomComplexUnit_koszulPowerComplex X f (n + 1)).hom ≫
        ((derivedSheafHomBifunctor X).map
          (DerivedCategory.Q.map (koszulPowerComplexMap X f n)).op).app
            (derivedStructureSheaf X) :=
    strictlyPerfectHomComparison_naturality_source X (derivedInternalHomOfBifunctor X)
      (koszulPowerComplex X f (n + 1)) (koszulPowerComplex X f n) (structureSheafComplex X)
      (koszulPowerComplexMap X f n)
  have hQ : DerivedCategory.Q.map (homMap X (koszulPowerComplexMap X f n)
          (𝟙 (structureSheafComplex X))) ≫
        DerivedCategory.Q.map (koszulNaiveDualComplexIso X f n).hom =
      DerivedCategory.Q.map (koszulNaiveDualComplexIso X f (n + 1)).hom ≫
        DerivedCategory.Q.map (koszulNaiveDualComplexMap X f n) := by
    rw [← Functor.map_comp, ← Functor.map_comp, homMap_comp_koszulNaiveDualComplexIso_hom]
  have hB : ((derivedSheafHomBifunctor X).map
        (DerivedCategory.Q.map (koszulPowerComplexMap X f n)).op).app
          (derivedStructureSheaf X) =
      (derivedDualIsoSheafHomComplexUnit_koszulPowerComplex X f (n + 1)).inv ≫
        (DerivedCategory.Q.map (homMap X (koszulPowerComplexMap X f n)
            (𝟙 (structureSheafComplex X))) ≫
          (derivedDualIsoSheafHomComplexUnit_koszulPowerComplex X f n).hom) :=
    (Iso.eq_inv_comp _).2 hnat.symm
  rw [koszulDerivedDualSystem_map_succ, Functor.comp_map, koszulNaiveDualSystem_map_succ]
  show ((derivedSheafHomBifunctor X).map
        (DerivedCategory.Q.map (koszulPowerComplexMap X f n)).op).app
          (derivedStructureSheaf X) ≫
      (derivedDualIsoSheafHomComplexUnit_koszulPowerComplex X f n).inv ≫
        DerivedCategory.Q.map (koszulNaiveDualComplexIso X f n).hom =
    ((derivedDualIsoSheafHomComplexUnit_koszulPowerComplex X f (n + 1)).inv ≫
        DerivedCategory.Q.map (koszulNaiveDualComplexIso X f (n + 1)).hom) ≫
      DerivedCategory.Q.map (koszulNaiveDualComplexMap X f n)
  rw [hB]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← hQ]

/-- **The tower of derived duals of the Koszul complexes is the tower of their naive termwise
duals.** The degreewise comparisons of [Stacks, Tag 08JH] are compatible with the transition
maps, so they are an isomorphism of towers; this is the form in which [Stacks, Tag 0A0E] can be
fed to a statement about the Koszul terms themselves. -/
def koszulNaiveDualSystemIso :
    koszulDerivedDualSystem X f ≅ koszulNaiveDualSystem X f ⋙ DerivedCategory.Q :=
  NatIso.ofComponents (fun n => koszulNaiveDualTowerDegreeIso X f n.unop)
    (fun {_m _n} g =>
      (NatTrans.ofOpSequence (F := koszulDerivedDualSystem X f)
        (G := koszulNaiveDualSystem X f ⋙ DerivedCategory.Q)
        (fun k => (koszulNaiveDualTowerDegreeIso X f k).hom)
        (koszulNaiveDualTowerDegreeIso_naturality X f)).naturality g)

/-- **The characterising clause of `koszulNaiveDualSystemIso`**: at `n` it is the single-stage
comparison of [Stacks, Tag 08JH] at the `n`-th Koszul complex, followed by the degreewise
identification of its naive dual. -/
@[simp]
theorem koszulNaiveDualSystemIso_hom_app (n : ℕ) :
    (koszulNaiveDualSystemIso X f).hom.app ⟨n⟩ =
      (derivedDualIsoSheafHomComplexUnit_koszulPowerComplex X f n).inv ≫
        DerivedCategory.Q.map (koszulNaiveDualComplexIso X f n).hom :=
  rfl

/-! ### Stacks 0A0E through the naive dual -/

section Formula

variable
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ K₁ K₂ : HomologicalComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O))
      (ComplexShape.up ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  (T : Stacks.SheafOfModules.DerivedTensorProduct X)
  [HasWeakSheafify X.J CommRingCat.{u}]

/-- **The formula of [Stacks, Tag 0A0E] for the tower of derived duals of the Koszul complexes.**
For a ringed site `(𝒞, 𝒪)`, global sections `f_1, …, f_r` of `𝒪` and `K ∈ D(𝒪)`, the completion
`K^∧ = R𝑆heafHom_𝒪(Č(f), K)` of [Stacks, Tag 099B] is a derived limit of the tower
`n ↦ K ⊗^𝐋_𝒪 R𝑆heafHom_𝒪(K(𝒪, f^{n+1}), 𝒪)`.

This is `AlgebraicGeometry.RingedSite.isDerivedLimit_tensorDerivedDualSystem_koszulPowerSystem`
with its input `hdual`, clause 3 of [Stacks, Tag 08JJ] at the Koszul complexes, supplied by
`AlgebraicGeometry.RingedSite.isIso_derivedTensorDualToSheafHom_koszulPowerSystem`. -/
theorem isDerivedLimit_tensorDerivedDualSystem_koszulPowerSystem_completionFunctor
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    IsDerivedLimit (tensorDerivedDualSystem X T (koszulPowerSystem X f ⋙ DerivedCategory.Q) K)
      ((completionFunctor X f).obj K) :=
  isDerivedLimit_tensorDerivedDualSystem_koszulPowerSystem X T f K
    (isIso_derivedTensorDualToSheafHom_koszulPowerSystem X T K f)

/-- **The formula of [Stacks, Tag 0A0E] with the derived dual replaced by the naive termwise
dual.** For a ringed site `(𝒞, 𝒪)`, global sections `f_1, …, f_r` of `𝒪` and `K ∈ D(𝒪)`, the
completion `K^∧` of [Stacks, Tag 099B] along the ideal sheaf generated by `f_1, …, f_r` is a
derived limit of the tower `n ↦ K ⊗^𝐋_𝒪 SheafHom(K(𝒪, f^{n+1}), 𝒪)`, the naive termwise dual
replacing the derived one.

This is `isDerivedLimit_tensorDerivedDualSystem_koszulPowerSystem_completionFunctor` transported
along `AlgebraicGeometry.RingedSite.koszulNaiveDualSystemIso`, whiskered with the derived tensor
product by `K`. -/
theorem isDerivedLimit_tensorKoszulNaiveDualSystem_koszulPowerSystem
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    IsDerivedLimit (koszulNaiveDualSystem X f ⋙ DerivedCategory.Q ⋙ T.tensor.obj K)
      ((completionFunctor X f).obj K) :=
  IsDerivedLimit.of_iso
    (Functor.isoWhiskerRight (koszulNaiveDualSystemIso X f) (T.tensor.obj K))
    (isDerivedLimit_tensorDerivedDualSystem_koszulPowerSystem_completionFunctor X f T K)

end Formula

end AlgebraicGeometry.RingedSite

end
