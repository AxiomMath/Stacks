module

public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulAdicQuotientSite
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulAdicReductionUnit
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulPerfectDualProjections
public import StacksFrontier.CategoryTheory.Shift.SingleFunctorsPostcompComp
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.HomComparisonStructureSheaf

/-!
# The pigeonhole comparison of towers, named, and its cone along the completion unit

`KoszulAdicQuotientSite.lean` produces the comparison `ψ` of the coefficient-free dual Koszul
tower with the tower `n ↦ 𝒪/ℐⁿ⁺¹` in degree zero only existentially, as
`AlgebraicGeometry.RingedSite.exists_hasEventualInverses_derivedSheafHomSystem_adicQuotientTower`,
and `KoszulAdicReductionUnit.lean` reduces part (1) of [Stacks, Tag 0A0K] over that tower to a
**coefficient-free identity** in `ψ`. An existentially bound `ψ` cannot be fed to that reduction,
so this file names it.

## What naming it buys

Written out, the comparison is
`(triv)⁻¹ ≫ R𝑆heafHom(φ, 𝒪[0]) ≫ ψ_n`, and the first two factors of `ψ` collapse: the
identification `AlgebraicGeometry.RingedSite.koszulTensorDualSystemCoefficientIso` of
[Stacks, Tag 0A0E]'s tower with the shifted dual Koszul tower *begins* with the identification
`AlgebraicGeometry.RingedSite.koszulTensorDualSystemIso` the first factor inverts, so the
interchange morphism of [Stacks, Tag 0BYU] cancels against itself and never has to be computed.
What is left of `ψ` is the comparison of [Stacks, Tag 08JH] out of the internal Hom complex, the
self-duality of the Koszul complex, [Stacks, Tag 0G3D] across the shift by `r`, and the
pigeonhole comparison.

Two further collapses make the whole composite the image under `DerivedCategory.Q` of a single
morphism of complexes, followed by the pigeonhole comparison placed in degree zero:

* `AlgebraicGeometry.RingedSite.derivedStructureSheafHomIso_inv_comp_map_eq_Q_map_comp` — the
  dual of a morphism of complexes `φ : E ⟶ 𝒪[0]`, read through the trivialisation of
  `R𝑆heafHom_𝒪(𝒪[0], 𝒪[0])`, is the class of a morphism of complexes followed by the comparison
  of [Stacks, Tag 08JH]. So the comparison of 08JH cancels as well, against the one inside `ψ`.
* `AlgebraicGeometry.RingedSite.koszulShiftedDualToTopSingle_app` — the comparison across the
  shift by `r` is the class of a morphism of complexes. The commutation isomorphism of
  `DerivedCategory.Q` with the shift, which has no formula, cancels against the one inside the
  shift isomorphism of the single functors of the derived category; that cancellation is
  `CategoryTheory.SingleFunctors.postcomp_shiftIso_hom_app_comp`.

## Main results

* `AlgebraicGeometry.RingedSite.derivedSheafHomToAdicQuotientTower` — **the comparison `ψ`,
  named**.
* `AlgebraicGeometry.RingedSite.hasEventualInverses_derivedSheafHomToAdicQuotientTower` — the
  comparison `ψ` has eventual inverses.
* `AlgebraicGeometry.RingedSite.koszulShiftedDualToTopSingle_app` — the comparison across the
  shift is the class of a morphism of complexes.
* `AlgebraicGeometry.RingedSite.derivedStructureSheafHomIso_inv_comp_map_eq_Q_map_comp` — the dual
  of `φ`, read through the trivialisation, is the class of a morphism of complexes followed by the
  comparison of [Stacks, Tag 08JH].
* `AlgebraicGeometry.RingedSite.koszulToTopHomologyOn_comp_koszulTopHomologyToAdicQuotientApp` —
  the canonical map onto the top Koszul cohomology sheaf, followed by the pigeonhole comparison,
  is the projection `𝒪 ⟶ 𝒪/ℐⁿ⁺¹`. This is the last step of the coefficient-free identity, and the
  only one of its steps that is about the two towers rather than about a cancellation.
* `AlgebraicGeometry.RingedSite.koszulTopHomologyToAdicQuotientSigned` — that comparison twisted
  by the sign `(-1)^r`, which is the twist the degree-zero component of the Koszul self-duality
  carries; `AlgebraicGeometry.RingedSite.derivedSheafHomToAdicQuotientTower` is built from the
  twisted form, because only for it does the coefficient-free identity hold on the nose. The
  degree-zero computation that forces the sign is in `KoszulAdicDualDegreeZero.lean`.

## Implementation notes

The pigeonhole comparison
`AlgebraicGeometry.RingedSite.koszulTopHomologyToAdicQuotient` is stated in the degree
`AlgebraicGeometry.RingedSite.koszulTopDeg r = r - 1 + 1` that the index type of the top-degree
term of the Koszul complex carries, while
`AlgebraicGeometry.RingedSite.koszulTopHomologySystem` — the tower the comparison across the
shift lands in — is taken in the degree `r`. The two integers are equal but not syntactically so,
so the comparison and the canonical map onto the top cohomology sheaf are both transported along
an equation of degrees, by
`AlgebraicGeometry.RingedSite.koszulTopHomologyToAdicQuotientAt` and
`AlgebraicGeometry.RingedSite.koszulToTopHomologyAt`. Every statement about the transported pair
is proved by `subst` on that equation, which is legitimate because the degree is a bound variable
there and is what the existing
`AlgebraicGeometry.RingedSite.exists_hasEventualInverses_homologyFunctor_adicQuotientTower` does.

## References

* [Stacks Project, Tag 0A0E](https://stacks.math.columbia.edu/tag/0A0E)
* [Stacks Project, Tag 0A0K](https://stacks.math.columbia.edu/tag/0A0K)
* [Stacks Project, Tag 08JH](https://stacks.math.columbia.edu/tag/08JH)
* [Stacks Project, Tag 0G3D](https://stacks.math.columbia.edu/tag/0G3D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.RingedSite

universe u

open scoped IsMulCommutative

attribute [local instance] HasDerivedCategory.standard hasFiniteBiproducts_sheafOfModules
  hasSheafCompose_forget₂_ringCat

section Shift

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}]
  [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] {r : ℕ}
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))
  (ℱ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- The morphism of complexes whose class is the comparison of the shifted dual Koszul tower with
the tower of top cohomology sheaves in degree zero: the morphism onto the top cohomology sheaf
placed in degree `r`, shifted by `r`, followed by the shift isomorphism of the single functors of
complexes. -/
def koszulShiftedToTopSingleComplexMap (n : ℕ) :
    ((koszulDualSystemOn X f ℱ).obj (op n))⟦(r : ℤ)⟧ ⟶
      (CochainComplex.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
        ((koszulTopHomologySystem X f ℱ).obj (op n)) :=
  (shiftFunctor (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
      (r : ℤ)).map
      ((koszulToTopSingle X f ℱ).app (op n)) ≫
    ((CochainComplex.singleFunctors
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).shiftIso
      (r : ℤ) 0 (r : ℤ) (by ring)).hom.app ((koszulTopHomologySystem X f ℱ).obj (op n))

/-- **The comparison across the shift by `r` is the class of a morphism of complexes.** The
commutation isomorphism of `DerivedCategory.Q` with the shift, which has no formula, cancels
against the one inside the shift isomorphism of the single functors of the derived category. -/
theorem koszulShiftedDualToTopSingle_app (n : ℕ) :
    (koszulShiftedDualToTopSingle X f ℱ).app (op n) =
      DerivedCategory.Q.map (koszulShiftedToTopSingleComplexMap X f ℱ n) :=
  SingleFunctors.postcomp_shiftIso_hom_app_comp
    (CochainComplex.singleFunctors
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) DerivedCategory.Q
    (r : ℤ) 0 (r : ℤ) (by ring) ((koszulTopHomologySystem X f ℱ).obj (op n))
    ((koszulToTopSingle X f ℱ).app (op n))

end Shift

section Dual

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The dual of a morphism of complexes `φ : E ⟶ 𝒪[0]`, read through the trivialisation of
`R𝑆heafHom_𝒪(𝒪[0], QF)`, is the class of a morphism of complexes followed by the comparison of
[Stacks, Tag 08JH].**

Two inputs: the comparison is natural in its contravariant variable
(`AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison_naturality_source`), and out of
`𝒪[0]` it is the trivialisation inverted
(`AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison_comp_derivedStructureSheafHomIso`),
evaluation at the unit section being invertible. So the comparison out of `𝒪[0]` cancels and only
the comparison out of `E` is left, which is the one a tower identification built from 08JH
inverts.

The target complex `F` is arbitrary: both inputs are stated at an arbitrary target, and the
coefficient-ful chain of [Stacks, Tag 0A0K] part (3) needs it at `F = ℱ[0]`, where the
coefficient does *not* drop out of the tower comparison. At `F = 𝒪[0]` it is the
coefficient-free statement part (1) consumes. -/
theorem derivedStructureSheafHomIso_inv_comp_map_eq_Q_map_comp
    (E F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (φ : E ⟶ structureSheafComplex X) :
    (derivedStructureSheafHomIso X (DerivedCategory.Q.obj F)).inv ≫
        ((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map φ).op).app
          (DerivedCategory.Q.obj F) =
      DerivedCategory.Q.map ((structureSheafHomIso X F).inv ≫ homMap X φ (𝟙 F)) ≫
        strictlyPerfectHomComparison X (derivedInternalHomOfBifunctor X) E F := by
  have hA := strictlyPerfectHomComparison_comp_derivedStructureSheafHomIso X F
  have hB := strictlyPerfectHomComparison_naturality_source X (derivedInternalHomOfBifunctor X)
    (structureSheafComplex X) E F φ
  have hσ : strictlyPerfectHomComparison X (derivedInternalHomOfBifunctor X)
        (structureSheafComplex X) F =
      DerivedCategory.Q.map (structureSheafHomEvaluation X F) ≫
        (derivedStructureSheafHomIso X (DerivedCategory.Q.obj F)).inv := by
    rw [← hA, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hcancel : DerivedCategory.Q.map (structureSheafHomIso X F).inv ≫
      DerivedCategory.Q.map (structureSheafHomEvaluation X F) = 𝟙 _ := by
    rw [← DerivedCategory.Q.map_comp]
    exact (congrArg DerivedCategory.Q.map
      (structureSheafHomIso X F).inv_hom_id).trans
      (DerivedCategory.Q.map_id _)
  symm
  rw [DerivedCategory.Q.map_comp, Category.assoc, hB, hσ, ← Category.assoc, ← Category.assoc,
    hcancel, Category.id_comp]

end Dual

section Comparison

variable (X : RingedSite.{u, u, u}) {r : ℕ}
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))
  [HasWeakSheafify X.J CommRingCat.{u}]

/-- The top degree of the Koszul complex, in the two spellings `r - 1 + 1` and `r`. -/
theorem koszulTopDeg_eq : koszulTopDeg r = (r : ℤ) := by ring

/-- **The canonical map onto the top Koszul cohomology sheaf, followed by the pigeonhole
comparison, is the projection `𝒪 ⟶ 𝒪/ℐⁿ⁺¹`.** Both are read off the unique top-degree factor:
the canonical map is the inverse of the projection onto that factor followed by the canonical map
out of the top-degree term, and the pigeonhole comparison is the projection `𝒪 ⟶ 𝒪/ℐⁿ⁺¹` read
through that same factor and descended. -/
theorem koszulToTopHomologyOn_comp_koszulTopHomologyToAdicQuotientApp (n : ℕ) :
    koszulToTopHomologyOn X f
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) n ≫
        koszulTopHomologyToAdicQuotientApp X f n =
      adicQuotientTowerπ X f n := by
  rw [koszulToTopHomologyOn_eq, Category.assoc,
    topToHomology_comp_koszulTopHomologyToAdicQuotientApp,
    koszulTopTermInj_comp_koszulTopTermProj_assoc]

/-- The pigeonhole comparison of the Koszul top cohomology tower with the adic quotient tower, at
an arbitrary spelling `p` of the top degree. -/
def koszulTopHomologyToAdicQuotientAt (p : ℤ) (hp : koszulTopDeg r = p) :
    koszulDualSystemOn X f (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ⋙
        HomologicalComplex.homologyFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (ComplexShape.up ℤ) p ⟶
      adicQuotientTower X (generatedIdealSheaf f) :=
  hp ▸ koszulTopHomologyToAdicQuotient X f

/-- The canonical map onto the top Koszul cohomology sheaf, at an arbitrary spelling `p` of the
top degree and with an arbitrary coefficient sheaf `M`. -/
def koszulToTopHomologyAt (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (p : ℤ) (hp : koszulTopDeg r = p)
    (n : ℕ) :
    M ⟶
      (koszulDualSystemOn X f M ⋙
        HomologicalComplex.homologyFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (ComplexShape.up ℤ) p).obj (op n) :=
  hp ▸ koszulToTopHomologyOn X f M n

/-- `AlgebraicGeometry.RingedSite.koszulToTopHomologyOn_comp_koszulTopHomologyToAdicQuotientApp`
at an arbitrary spelling of the top degree. -/
theorem koszulToTopHomologyAt_comp_koszulTopHomologyToAdicQuotientAt
    (p : ℤ) (hp : koszulTopDeg r = p) (n : ℕ) :
    koszulToTopHomologyAt X f
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) p hp n ≫
        (koszulTopHomologyToAdicQuotientAt X f p hp).app (op n) =
      adicQuotientTowerπ X f n := by
  subst hp
  exact koszulToTopHomologyOn_comp_koszulTopHomologyToAdicQuotientApp X f n

/-- The pigeonhole comparison has eventual inverses at an arbitrary spelling of the top degree. -/
theorem hasEventualInverses_koszulTopHomologyToAdicQuotientAt (p : ℤ)
    (hp : koszulTopDeg r = p) :
    NoetherianAdicCompletion.HasEventualInverses
      (koszulTopHomologyToAdicQuotientAt X f p hp) := by
  subst hp
  exact hasEventualInverses_koszulTopHomologyToAdicQuotient X f

/-- The square of the sign `(-1)^r` is one. -/
theorem neg_one_pow_mul_neg_one_pow : ((-1 : ℤ) ^ r) * ((-1 : ℤ) ^ r) = 1 := by
  rw [← pow_add]
  exact Even.neg_one_pow ⟨r, rfl⟩

/-- **The pigeonhole comparison twisted by the sign of the Koszul self-duality.** The degree-zero
component of the self-duality of the Koszul complex multiplies the unique top-degree factor by the
dual twist `CategoryTheory.AlternatingCech.dualSign Finset.univ`, which is `(-1)^r`; so it is this
twisted form of the pigeonhole comparison, and not the untwisted one, for which the
coefficient-free identity of part (1) of [Stacks, Tag 0A0K] holds on the nose. -/
def koszulTopHomologyToAdicQuotientSigned (p : ℤ) (hp : koszulTopDeg r = p) :
    koszulDualSystemOn X f (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ⋙
        HomologicalComplex.homologyFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (ComplexShape.up ℤ) p ⟶
      adicQuotientTower X (generatedIdealSheaf f) :=
  (-1 : ℤ) ^ r • koszulTopHomologyToAdicQuotientAt X f p hp

/-- The components of the twisted pigeonhole comparison. -/
theorem koszulTopHomologyToAdicQuotientSigned_app (p : ℤ) (hp : koszulTopDeg r = p) (n : ℕ) :
    (koszulTopHomologyToAdicQuotientSigned X f p hp).app (op n) =
      (-1 : ℤ) ^ r • (koszulTopHomologyToAdicQuotientAt X f p hp).app (op n) :=
  NatTrans.app_zsmul _ _ _

/-- **The canonical map onto the top Koszul cohomology sheaf, twisted by the same sign and
followed by the twisted pigeonhole comparison, is the projection `𝒪 ⟶ 𝒪/ℐⁿ⁺¹`.** The two signs
multiply to one. -/
theorem zsmul_koszulToTopHomologyAt_comp_koszulTopHomologyToAdicQuotientSigned
    (p : ℤ) (hp : koszulTopDeg r = p) (n : ℕ) :
    ((-1 : ℤ) ^ r • koszulToTopHomologyAt X f
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) p hp n) ≫
        (koszulTopHomologyToAdicQuotientSigned X f p hp).app (op n) =
      adicQuotientTowerπ X f n := by
  rw [koszulTopHomologyToAdicQuotientSigned_app, Preadditive.zsmul_comp,
    Preadditive.comp_zsmul, smul_smul, neg_one_pow_mul_neg_one_pow, one_smul,
    koszulToTopHomologyAt_comp_koszulTopHomologyToAdicQuotientAt]

/-- The twisted pigeonhole comparison has eventual inverses: the inverses of the untwisted one,
twisted by the same sign. -/
theorem hasEventualInverses_koszulTopHomologyToAdicQuotientSigned (p : ℤ)
    (hp : koszulTopDeg r = p) :
    NoetherianAdicCompletion.HasEventualInverses
      (koszulTopHomologyToAdicQuotientSigned X f p hp) := by
  intro n
  obtain ⟨m, hm, s, h1, h2⟩ := hasEventualInverses_koszulTopHomologyToAdicQuotientAt X f p hp n
  refine ⟨m, hm, (-1 : ℤ) ^ r • s, ?_, ?_⟩ <;>
    rw [koszulTopHomologyToAdicQuotientSigned_app, Preadditive.zsmul_comp,
      Preadditive.comp_zsmul, smul_smul, neg_one_pow_mul_neg_one_pow, one_smul]
  · exact h1
  · exact h2

end Comparison

section Named

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [HasWeakSheafify X.J CommRingCat.{u}] {r : ℕ}
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

/-- **The site-level pigeonhole comparison of the coefficient-free dual Koszul tower with the
tower `n ↦ 𝒪/ℐⁿ⁺¹` in degree zero, named.** This is the transformation
`AlgebraicGeometry.RingedSite.exists_hasEventualInverses_derivedSheafHomSystem_adicQuotientTower`
produces, written out: the identification of [Stacks, Tag 0A0E]'s tower at the coefficient object
`𝒪` with the dual Koszul tower, inverted; the absorption of that coefficient into the Koszul
complex; [Stacks, Tag 0G3D] across the shift by `r`; and the pigeonhole comparison in degree
zero.

The last factor is the pigeonhole comparison **twisted by the sign `(-1)^r`**
(`AlgebraicGeometry.RingedSite.koszulTopHomologyToAdicQuotientSigned`): the degree-zero component
of the Koszul self-duality carries the dual twist at the unique top-degree factor, so only the
twisted comparison makes the coefficient-free identity of part (1) of [Stacks, Tag 0A0K] an
equality on the nose. Twisting by a sign changes nothing about the eventual inverses. -/
def derivedSheafHomToAdicQuotientTower :
    derivedSheafHomSystem X (koszulPowerSystem X f ⋙ DerivedCategory.Q)
        (derivedStructureSheaf X) ⟶
      adicQuotientTower X (generatedIdealSheaf f) ⋙
        DerivedCategory.singleFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0 :=
  (koszulTensorDualSystemIso X f (derivedStructureSheaf X)).inv ≫
    (koszulTensorDualSystemCoefficientIso X f
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).hom ≫
      koszulShiftedDualToTopSingle X f
          (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ≫
        Functor.whiskerRight (koszulTopHomologyToAdicQuotientSigned X f (r : ℤ)
            (koszulTopDeg_eq (r := r)))
          (DerivedCategory.singleFunctor
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0)

/-- A natural map of towers whose components are all invertible has eventual inverses. -/
private theorem hasEventualInverses_of_isIso_app {C : Type*} [Category C] {F G : ℕᵒᵖ ⥤ C}
    (φ : F ⟶ G) (hφ : ∀ n : ℕ, IsIso (φ.app (op n))) :
    NoetherianAdicCompletion.HasEventualInverses φ := fun n ↦ by
  have := hφ n
  refine ⟨n, le_rfl, inv (φ.app (op n)), ?_, ?_⟩
  · rw [IsIso.hom_inv_id, ← F.map_id]
    exact congrArg F.map (Subsingleton.elim _ _)
  · rw [IsIso.inv_hom_id, ← G.map_id]
    exact congrArg G.map (Subsingleton.elim _ _)

/-- **The named comparison has eventual inverses**, which is what
`NoetherianAdicCompletion.IsDerivedLimitWithProjections.comp_of_hasEventualInverses` consumes.
The first two factors are isomorphisms of towers, so they have eventual inverses at the same
level; the pro-vanishing hypothesis is spent in [Stacks, Tag 0G3D]; and the last factor is the
pigeonhole comparison, whiskered into degree zero. -/
theorem hasEventualInverses_derivedSheafHomToAdicQuotientTower
    (hpz : ∀ (n : ℕ) (p : ℤ), p < r → ∃ (m : ℕ) (_ : n ≤ m),
      HomologicalComplex.homologyMap
        ((koszulDualSystemOn X f
            (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).map
          (homOfLE ‹n ≤ m›).op) p = 0) :
    NoetherianAdicCompletion.HasEventualInverses
      (derivedSheafHomToAdicQuotientTower X f) := by
  have h₁ := hasEventualInverses_of_isIso_app
    (koszulTensorDualSystemIso X f (derivedStructureSheaf X)).inv fun n ↦ inferInstance
  have h₂ := hasEventualInverses_of_isIso_app
    (koszulTensorDualSystemCoefficientIso X f
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).hom
    fun n ↦ inferInstance
  exact h₁.comp (h₂.comp ((hasEventualInverses_koszulShiftedDualToTopSingle X f
    (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) hpz).comp
      ((hasEventualInverses_koszulTopHomologyToAdicQuotientSigned X f (r : ℤ)
        (koszulTopDeg_eq (r := r))).whiskerRight _)))

/-- **The comparison of [Stacks, Tag 08JH] cancels against the one inside the named comparison of
towers.** The identification of [Stacks, Tag 0A0E]'s tower at the coefficient object `ℱ` with the
dual Koszul tower is inverted by the first factor of the named comparison, so what survives of
its first two factors is the inverse of the comparison of 08JH followed by the class of the
self-duality of the Koszul complex.

The coefficient `ℱ` is arbitrary. At `ℱ = 𝒪` this is what the named comparison of towers
`AlgebraicGeometry.RingedSite.derivedSheafHomToAdicQuotientTower` consumes, for part (1) of
[Stacks, Tag 0A0K]; part (3) consumes it at a general coefficient, where the coefficient stays
inside the Koszul complex instead of dropping out through `ℱ ⊗^𝐋_𝒪 -`. -/
theorem koszulDerivedSheafHomSystemComparison_app_comp_koszulTensorDualSystemIso_inv_app
    (ℱ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (n : ℕ) :
    (koszulDerivedSheafHomSystemComparison X f
            ℱ).app (op n) ≫
        (koszulTensorDualSystemIso X f (DerivedCategory.Q.obj
            (singleSheafComplex X ℱ))).inv.app (op n) ≫
          (koszulTensorDualSystemCoefficientIso X f
            ℱ).hom.app (op n) =
      DerivedCategory.Q.map
        (koszulDualComplexIsoCoeff X f ℱ n).hom := by
  rw [koszulTensorDualSystemCoefficientIso, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, NatTrans.comp_app, Iso.inv_hom_id_app_assoc,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app]
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun z ↦ z ≫ DerivedCategory.Q.map
    ((koszulDualSystemComplexIso X f ℱ).hom.app (op n)))
    ((asIso (koszulDerivedSheafHomSystemComparison X f
      ℱ)).hom_inv_id_app (op n))).trans ?_
  refine (Category.id_comp _).trans (congrArg DerivedCategory.Q.map ?_)
  show (koszulDualSystemComplexMap X f ℱ).app (op n) = _
  exact NatTrans.ofOpSequence_app _ _ _

end Named


end AlgebraicGeometry.RingedSite

end
