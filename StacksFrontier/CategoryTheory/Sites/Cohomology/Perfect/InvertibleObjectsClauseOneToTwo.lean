module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.InvertibleObjectsChainPairing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.InvertibleObjectsClauseThree
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.InvertibleObjectsClauseThreeToTwo
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.InvertibleObjectsClauseTwoToOne
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.StrictlyPerfectIsKFlat
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedRestrictionMonoidal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation

/-!
# Clause (1) of Stacks 0FPY implies clause (2), for perfect objects

Let `(C, O)` be a ringed site and let `M`, `N` be perfect objects of `D(O)` with
`M ⊗^L N ≅ O`. Then `M` satisfies clause (2) of Stacks 0FPY: there is a locally finite direct
product decomposition `O = ∏ O_n` and invertible `O_n`-modules `ℋ^n` with `M = ⨁ ℋ^n[-n]`.

This is the proof of the source after its first step: "Then `N` is a left dual for `M` in the
monoidal category `D(O)` and we conclude that `M` is perfect by Lemma 0FPV. By symmetry we see that
`N` is perfect." Perfectness of `M` and `N` is taken as a hypothesis here; it is proved, for an
invertible object, by
`AlgebraicGeometry.RingedSite.InvertibleDerived.isPerfect_of_isInvertibleObject`, and the two are
put together in `AlgebraicGeometry.RingedSite.InvertibleDerived.isInvertibleObject_tfae`.

Over a covering of every object `M` and `N` are represented by strictly perfect complexes `P`,
`P'`, and `Tot(P ⊗ P') ≅ O[0]` in the derived category of the localized site. Along a further
covering this is a homotopy equivalence (Stacks 08FR), so the global sections of `P` and `P'` over
the members of that covering are mutually inverse objects of `D(R)` (Stacks 0FPX), and Stacks 0FNT
splits their cohomology by idempotents; these local splittings glue.

## Main results

* `hasInvertibleModuleDecomposition_of_tensorIsoUnit`: the statement above.

## References

* [Stacks Project, Tag 0FPY](https://stacks.math.columbia.edu/tag/0FPY)
* [Stacks Project, Tag 0FPV](https://stacks.math.columbia.edu/tag/0FPV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open Opposite Stacks.SheafOfModules.DerivedMonoidal

universe u d

namespace AlgebraicGeometry.RingedSite.InvertibleDerived

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

variable {X : RingedSite.{u, u, u}} [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ W : X.C, HasSheafify (X.J.over W) AddCommGrpCat.{u}]
  [∀ W : X.C, (X.J.over W).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Over `V`, the complexes `E` and `E'` have strictly perfect models. -/
def GoodModels (E E' : CochainComplex (Mod X.O) ℤ) (V : X.C) : Prop :=
  ∃ (P P' : CochainComplex
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ),
    IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V) P ∧
    IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V) P' ∧
    (∃ q : P ⟶ X.restrictComplex E V, QuasiIso q) ∧ ∃ q' : P' ⟶ X.restrictComplex E' V, QuasiIso q'

/-- Restriction of sheaves of modules along `a : W ⟶ V` preserves homology. -/
instance overMap_preservesHomology' {V W : X.C} (a : W ⟶ V) :
    (SheafOfModules.overMap.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a).PreservesHomology := by
  have := Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteLimits
    (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O) a
  have := Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteColimits
    (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O) a
  infer_instance

/-- A strictly perfect model of `E` over `V` restricts to one over any `W ⟶ V`. -/
private theorem exists_strictlyPerfect_model_restr {X : RingedSite.{u, u, u}}
    [∀ W : X.C, HasSheafify (X.J.over W) AddCommGrpCat.{u}]
    [∀ W : X.C, (X.J.over W).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {E : CochainComplex (Mod X.O) ℤ} {V W : X.C} (a : W ⟶ V) {P : CochainComplex
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ}
    (hP : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V) P)
    (q : P ⟶ X.restrictComplex E V) [QuasiIso q] :
    ∃ R : CochainComplex
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W)) ℤ,
    IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W) R ∧
      ∃ q' : R ⟶ X.restrictComplex E W, QuasiIso q' :=
  ⟨(restr X a).obj P, isStrictlyPerfect_overMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a hP,
    (restr X a).map q ≫ (restrictComplexOverIso a E).hom, inferInstance⟩

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- If `E` and `E'` have strictly perfect models over `V`, they have them over any `V₀ ⟶ V`. -/
theorem GoodModels.map {E E' : CochainComplex (Mod X.O) ℤ} {V : X.C} (h : GoodModels E E' V)
    {V₀ : X.C} (a : V₀ ⟶ V) : GoodModels E E' V₀ := by
  obtain ⟨P, P', hP, hP', ⟨q, hq⟩, ⟨q', hq'⟩⟩ := h
  obtain ⟨R, hR, r⟩ := exists_strictlyPerfect_model_restr a hP q
  obtain ⟨R', hR', r'⟩ := exists_strictlyPerfect_model_restr a hP' q'
  exact ⟨R, R', hR, hR', r, r'⟩

/-- The sieve of arrows over whose source two complexes have strictly perfect models. -/
def goodModelsSieve (E E' : CochainComplex (Mod X.O) ℤ) (U : X.C) : Sieve U where
  arrows V _ := GoodModels E E' V
  downward_closed h a := h.map a

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Two perfect complexes have strictly perfect models on a covering of every object. -/
theorem goodModelsSieve_mem {E E' : CochainComplex (Mod X.O) ℤ} (hE : X.IsPerfectComplex E)
    (hE' : X.IsPerfectComplex E') (U : X.C) : goodModelsSieve E E' U ∈ X.J U := by
  obtain ⟨S, hS, hd⟩ := hE U
  obtain ⟨S', hS', hd'⟩ := hE' U
  refine X.J.superset_covering ?_ (X.J.intersection_covering hS hS')
  rintro V h ⟨⟨Vs, a, s, hs, rfl⟩, ⟨Vs', a', s', hs', hh⟩⟩
  obtain ⟨P, hP, q, hq⟩ := hd s hs
  obtain ⟨P', hP'', q', hq'⟩ := hd' s' hs'
  obtain ⟨R, hR, r⟩ := exists_strictlyPerfect_model_restr a hP q
  obtain ⟨R', hR', r'⟩ := exists_strictlyPerfect_model_restr a' hP'' q'
  exact ⟨R, R', hR, hR', r, r'⟩

section Local

variable [HasDerivedCategory.{d} (Mod X.O)]

/-- An isomorphism in `D(O)` between the images of two complexes, restricted to the localized site
over `V`. -/
def restrictDerivedIso (V : X.C) {A B : CochainComplex (Mod X.O) ℤ}
    (e : DerivedCategory.Q.obj A ≅ DerivedCategory.Q.obj B) :
    letI : HasDerivedCategory (Mod (X.over V).O) := HasDerivedCategory.standard _
    DerivedCategory.Q.obj ((ovF X V).mapHomologicalComplex (ComplexShape.up ℤ) |>.obj A) ≅
      DerivedCategory.Q.obj ((ovF X V).mapHomologicalComplex (ComplexShape.up ℤ) |>.obj B) :=
  letI : HasDerivedCategory (Mod (X.over V).O) := HasDerivedCategory.standard _
  haveI : PreservesFiniteLimits (ovF X V) :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits
      (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O) V
  haveI : PreservesFiniteColimits (ovF X V) :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits
      (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O) V
  ((ovF X V).mapDerivedCategoryFactors.app A).symm ≪≫ (ovF X V).mapDerivedCategory.mapIso e ≪≫
    (ovF X V).mapDerivedCategoryFactors.app B

/-- **Over an object with strictly perfect models, the derived pairing gives paired splittings
on a covering.** -/
theorem pairedPresieve_mem_of_goodModels {E E' Mc Nc : CochainComplex (Mod X.O) ℤ}
    (hMc : KFlat X.O Mc) (hNc : KFlat X.O Nc)
    (αE : DerivedCategory.Q.obj E ≅ DerivedCategory.Q.obj Mc)
    (αE' : DerivedCategory.Q.obj E' ≅ DerivedCategory.Q.obj Nc)
    (γg : DerivedCategory.Q.obj (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj Mc).obj Nc) ≅
      DerivedCategory.Q.obj (X.structureSheafComplex))
    {V : X.C} (hV : GoodModels E E' V) : Sieve.generate (pairedPresieve E E' V) ∈ X.J V := by
  obtain ⟨P, P', hP, hP', ⟨q, hq⟩, ⟨q', hq'⟩⟩ := hV
  let : HasDerivedCategory (Mod (X.over V).O) := HasDerivedCategory.standard _
  let PY : CochainComplex (Mod (X.over V).O) ℤ := P
  let PY' : CochainComplex (Mod (X.over V).O) ℤ := P'
  have hPY : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf (X.over V).O) PY := hP
  have hPY' : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf (X.over V).O) PY' := hP'
  let qY : PY ⟶ restrictMod E V := q
  let qY' : PY' ⟶ restrictMod E' V := q'
  have : QuasiIso qY := hq
  have : QuasiIso qY' := hq'
  let φ : DerivedCategory.Q.obj PY ≅ DerivedCategory.Q.obj (restrictMod Mc V) :=
    asIso (DerivedCategory.Q.map qY) ≪≫ restrictDerivedIso V αE
  let φ' : DerivedCategory.Q.obj PY' ≅ DerivedCategory.Q.obj (restrictMod Nc V) :=
    asIso (DerivedCategory.Q.map qY') ≪≫ restrictDerivedIso V αE'
  have hKM : KFlat (X.over V).O (restrictMod Mc V) :=
    Stacks.Cohomology.DerivedRestriction.kFlat_restriction X V Mc hMc
  have hKN : KFlat (X.over V).O (restrictMod Nc V) :=
    Stacks.Cohomology.DerivedRestriction.kFlat_restriction X V Nc hNc
  have hKP : KFlat (X.over V).O PY := kFlat_of_isStrictlyPerfect (X.over V) PY hPY
  have hKP' : KFlat (X.over V).O PY' := kFlat_of_isStrictlyPerfect (X.over V) PY' hPY'
  let := derivedMonoidal (X.over V).O
  let cmp := (symmetricMonoidalDerived (X.over V).O).comparison
  let γV : DerivedCategory.Q.obj (((Stacks.SheafOfModules.Tensor.tensorComplex (X.over V).O).obj
        PY).obj PY') ≅
      DerivedCategory.Q.obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (X.over V).O))) :=
    (cmp PY PY' hKP hKP').symm ≪≫ tensorIso φ φ' ≪≫ cmp _ _ hKM hKN ≪≫
      DerivedCategory.Q.mapIso (tensorComplexOverIso X V Mc Nc).symm ≪≫
      restrictDerivedIso V γg ≪≫
      DerivedCategory.Q.mapIso ((HomologicalComplex.singleMapHomologicalComplex (ovF X V)
        (ComplexShape.up ℤ) 0).app _)
  have hY := pairedPresieve_mem (Z := X.over V) PY PY' hPY hPY' γV (Over.mk (𝟙 V))
  have hY' := (GrothendieckTopology.mem_over_iff (J := X.J) (X := V) _).mp hY
  refine X.J.superset_covering ?_ hY'
  intro W g hg
  rw [Sieve.overEquiv_iff] at hg
  obtain ⟨W'', a, b, ⟨A⟩, hab⟩ := hg
  let ΘE : ∀ k, PY.homology k ≅ (ovF X V).obj (E.homology k) := fun k =>
    asIso (HomologicalComplex.homologyMap qY k) ≪≫ restrictModHomologyIso E V k
  let ΘE' : ∀ k, PY'.homology k ≅ (ovF X V).obj (E'.homology k) := fun k =>
    asIso (HomologicalComplex.homologyMap qY' k) ≪≫ restrictModHomologyIso E' V k
  refine ⟨W''.left, a.left, W''.hom, ⟨A.descend ΘE ΘE'⟩, ?_⟩
  have := Over.w a
  simp

/-- **Clause (1) of Stacks 0FPY implies clause (2), for perfect objects.** Let `M` and `N` be
perfect objects of `D(O)` with `M ⊗^L N ≅ O`. Then `M` admits a locally finite direct product
decomposition `O = ∏ O_n` of the structure sheaf together with invertible `O_n`-modules `ℋ^n`
such that `M = ⨁ ℋ^n[-n]`. -/
theorem hasInvertibleModuleDecomposition_of_tensorIsoUnit (M N : DerivedCategory (Mod X.O))
    (e : letI := derivedMonoidal X.O; M ⊗ N ≅ 𝟙_ _) (hM : X.IsPerfect M) (hN : X.IsPerfect N) :
    HasInvertibleModuleDecomposition X M := by
  let := derivedMonoidal X.O
  obtain ⟨E, hE, ⟨eE⟩⟩ := hM
  obtain ⟨E', hE', ⟨eE'⟩⟩ := hN
  obtain ⟨Mc, κ, hMc, hκ⟩ := exists_kFlat_resolution X.O E
  obtain ⟨Nc, κ', hNc, hκ'⟩ := exists_kFlat_resolution X.O E'
  have hMc' : KFlat X.O Mc := hMc
  have hNc' : KFlat X.O Nc := hNc
  let αE : DerivedCategory.Q.obj E ≅ DerivedCategory.Q.obj Mc :=
    (asIso (DerivedCategory.Q.map κ)).symm
  let αE' : DerivedCategory.Q.obj E' ≅ DerivedCategory.Q.obj Nc :=
    (asIso (DerivedCategory.Q.map κ')).symm
  let γg : DerivedCategory.Q.obj (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj Mc).obj
      Nc) ≅ DerivedCategory.Q.obj (X.structureSheafComplex) :=
    ((symmetricMonoidalDerived X.O).comparison Mc Nc hMc' hNc').symm ≪≫
      tensorIso (αE.symm ≪≫ eE) (αE'.symm ≪≫ eE') ≪≫ e ≪≫
      (symmetricMonoidalDerived X.O).unitIso
  have key : ∀ U : X.C, Sieve.generate (pairedPresieve E E' U) ∈ X.J U := by
    intro U
    refine X.J.transitive (goodModelsSieve_mem hE hE' U) _ fun V h hV => ?_
    refine X.J.superset_covering ?_ (pairedPresieve_mem_of_goodModels hMc' hNc' αE αE' γg hV)
    rintro W g ⟨W', a, b, hb, rfl⟩
    exact ⟨W', a, b ≫ h, hb, by simp⟩
  obtain ⟨D, H, hH, ⟨e'⟩⟩ := hasInvertibleModuleDecomposition_of_paired key
  exact ⟨D, H, hH, ⟨eE.symm ≪≫ e'⟩⟩

end Local

end AlgebraicGeometry.RingedSite.InvertibleDerived

end
