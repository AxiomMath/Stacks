module

public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import StacksCore.Tactic.StacksAttribute
public import
  StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedHomotopyCategoryTriangulated
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedInjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedModuleAbelian
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedShiftCommutator
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedGrothendieck

/-!
# Hom into a graded injective differential graded module

Let `X` be a ringed site and let `A` be a sheaf of differential graded algebras on it. For a
graded injective right differential graded `A`-module `I` and a short exact sequence
`0 → M₁ → M₂ → M₃ → 0` of right differential graded `A`-modules — *not* assumed admissible —
the homogeneous morphisms into `I` form a short exact sequence in every degree, and
precomposition commutes with the differential of the Hom complex. Taking cohomology degree by
degree then produces a long exact sequence whose degree-`n` term is the group of morphisms into
the `n`-fold translate of `I` in the homotopy category, and whose two non-connecting maps are
composition in that category.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.precompCocycle` is precomposition with a closed
  degree-zero morphism, on the degree-`n` homogeneous morphisms into a fixed object.
* `SheafOfModules.DifferentialGradedModule.homCohomology` is the cohomology of the Hom complex
  of a differential graded category: closed morphisms of a given degree modulo differentials.
* `SheafOfModules.DifferentialGradedModule.IsLongExactHomCohomology` says of a family of
  connecting maps that it is given by the lifting recipe and that the resulting sequence is
  exact at each of its three kinds of term.
* `SheafOfModules.DifferentialGradedModule.homCohomologyZeroEquiv` identifies the degree-zero
  cohomology of the Hom complex with the group of morphisms of the homotopy category.
* `SheafOfModules.DifferentialGradedModule.homCohomologyShiftEquiv` identifies the degree-`n`
  cohomology of the Hom complex with the group of morphisms into the `n`-fold translate of the
  target, through the shift functors of axiom (B).
* `SheafOfModules.DifferentialGradedModule.homotopyHomShift` and
  `SheafOfModules.DifferentialGradedModule.precompHomotopyHom` are the terms and the
  composition maps of the long exact sequence of the source, in the homotopy category of the
  differential graded category of right differential graded modules.

## Main results

* `SheafOfModules.DifferentialGradedModule.homComplex_shortExact_of_gradedInjective`: in each
  degree the two precomposition maps into a graded injective module are injective, exact and
  surjective.
* `SheafOfModules.DifferentialGradedModule.d_precompCocycle`: precomposition with a closed
  morphism commutes with the differential of the Hom complex.
* `SheafOfModules.DifferentialGradedModule.exists_isLongExactHomCohomology`: a sequence of Hom
  complexes that is short exact in every degree has a long exact cohomology sequence.
* `SheafOfModules.DifferentialGradedModule.exists_isLongExactHomCohomology_of_gradedInjective`:
  the long exact sequence for a short exact sequence of differential graded modules and a
  graded injective target.
* `SheafOfModules.DifferentialGradedModule.homCohomologyZeroEquiv_precompCocycleCohomology`
  and `SheafOfModules.DifferentialGradedModule.homCohomologyShiftEquiv_precompCocycleCohomology`:
  under those identifications the maps of the long exact sequence are composition in the
  homotopy category.
* `SheafOfModules.DifferentialGradedModule.exists_longExact_homotopyHomShift_of_gradedInjective`:
  the long exact sequence of the groups of morphisms into the translates of `I` in the homotopy
  category, which is the display of the source.

## Implementation notes

Graded injectivity is a condition on the module obtained by forgetting the differential, so the
proof passes to graded modules: a degree-`n` homogeneous morphism `M → I` of the differential
graded category is the same thing as a morphism of graded modules from the degree shift of `M`
by `-n` into `I`, and under that identification precomposition with a morphism of differential
graded modules becomes precomposition with its degree shift. The sequence of graded modules
obtained from the given one by forgetting differentials and shifting is short exact, because
forgetting the differential preserves all limits and colimits and the degree shift is an
equivalence; and `Hom` out of a short exact sequence into an injective object is short exact.
Commutation with the differential is the Leibniz rule together with closedness of the cocycle
being precomposed.

The degree shift of graded modules is the library's `SheafOfModules.GradedModule.shift`; only
its functoriality and the cancellation of two opposite shifts are built here.

Nothing here passes through a distinguished triangle, which is the point of the source: the
given short exact sequence is not assumed admissible, so it defines no distinguished triangle in
the homotopy category.

The cohomology of a Hom complex is built directly as the quotient of the closed morphisms of a
given degree by the differentials of the morphisms of one degree lower, rather than through the
homology of a complex of abelian groups, because in degree zero that quotient is literally the
set of morphisms of the homotopy category. The connecting map is produced by the usual recipe:
lift a closed morphism out of `M₁` to one out of `M₂`, take its differential, which is then the
image of a unique closed morphism out of `M₃`. Only the class of that morphism is well defined,
so the long exact sequence is stated as the existence of a family of connecting maps satisfying
the lifting characterisation, which pins them down uniquely.

Reading the terms of that sequence as groups of homomorphisms in the homotopy category needs two
further identifications. In degree zero the group structure of the quotient of closed morphisms
by differentials is matched with the one of the preadditive structure of the homotopy category by
`DGCategory.homotopyPreadditive_mk_add` and `DGCategory.homotopyPreadditive_zero`, which read
that preadditive structure on representing cocycles. In degree `n` the cohomology is carried onto
the degree-zero cohomology of the Hom complex into the `n`-fold translate by axiom (B)'s
identification `DGCategory.ShiftAxiomB.toShift`, which intertwines the two differentials up to
the unit `(-1) ^ n` and therefore matches cocycles with cocycles and coboundaries with
coboundaries; the translate is the value of the translation functor of the homotopy category by
`DGCategory.ShiftAxiomB.kShift_functor`.

### Scope of `@[stacks 0FSQ]`

Stacks 0FSQ displays two assertions: the short exact sequence of Hom complexes, and the long
exact sequence of groups of homomorphisms in the homotopy category and their translates which
its cohomology produces. The covering set of the tag is therefore the two declarations
`homComplex_shortExact_of_gradedInjective` and
`exists_longExact_homotopyHomShift_of_gradedInjective`, and each carries the bare attribute.

The intermediate statements about the cohomology of the Hom complexes — `homCohomology`,
`IsLongExactHomCohomology` and `exists_isLongExactHomCohomology_of_gradedInjective` — are not
tagged: the cohomology of a Hom complex is a different object from a group of homomorphisms in
the homotopy category, and the source's display names the latter. The two objects are matched
here by `homCohomologyShiftEquiv`, an additive bijection for the group structure of the
preadditive structure already fixed on the homotopy category and for the translation functors
of axiom (B), which is what makes the bare attribute honest.

## References

* [Stacks Project, Tag 0FSP](https://stacks.math.columbia.edu/tag/0FSP)
* [Stacks Project, Tag 0FSQ](https://stacks.math.columbia.edu/tag/0FSQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.HomComplex

universe u v w

namespace SheafOfModules.DifferentialGradedModule

/-! ### The degree shift functor on graded modules -/

section GradedShift

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  (B : GradedAlgebra.{u, v} R)

/-- The degree shift functor on right graded modules. -/
private def gradedShiftFunctor (k : ℤ) :
    GradedModule.{u, v, w} B ⥤ GradedModule.{u, v, w} B where
  obj M := M.shift k
  map φ := GradedModule.shiftHom φ k
  map_id M := GradedModule.shiftHom_id M k
  map_comp φ ψ := GradedModule.shiftHom_comp φ ψ k

/-- The degree shift functor is additive. -/
private instance gradedShiftFunctor_additive (k : ℤ) :
    (gradedShiftFunctor.{u, v, w} B k).Additive where
  map_add := GradedModule.Hom.ext (fun _ => rfl)

/-- Transport along an equality of degrees, read on sections through `eqToHom`. -/
private lemma eqToHom_val_app_eq_castHom (F : ℤ → SheafOfModules.{w} R) {i j : ℤ} (h : i = j)
    (U : Cᵒᵖ) (x : (F i).val.obj U) :
    (eqToHom (congrArg F h)).val.app U x = castHom F h U x := by
  cases h
  rfl

/-- Two opposite transports along equalities of degrees cancel. -/
private lemma degCastHom_comp_degCastHom {F : ℤ → SheafOfModules.{w} R} {i j : ℤ}
    (h : i = j) (h' : j = i) : degCastHom F h ≫ degCastHom F h' = 𝟙 _ := by
  cases h
  rw [show h' = rfl from Subsingleton.elim _ _]
  simp

/-- Two opposite degree shifts of a graded module cancel. -/
private def gradedShiftCancel {B : GradedAlgebra.{u, v} R}
    (M : GradedModule.{u, v, w} B) (k l : ℤ) (h : k + l = 0) :
    (M.shift k).shift l ≅ M where
  hom :=
    { app n := degCastHom M.piece (show (n + l) + k = n by omega)
      map_smul n i U x y := by
        simp only [degCastHom_val_app, GradedModule.shift_smul,
          GradedModule.castHom_shift_piece, Cofree.smul_castHom_left, Cofree.castHom_castHom] }
  inv :=
    { app n := degCastHom M.piece (show n = (n + l) + k by omega)
      map_smul n i U x y := by
        simp only [degCastHom_val_app, GradedModule.shift_smul,
          GradedModule.castHom_shift_piece, Cofree.smul_castHom_left, Cofree.castHom_castHom] }
  hom_inv_id := GradedModule.Hom.ext (fun _ => degCastHom_comp_degCastHom _ _)
  inv_hom_id := GradedModule.Hom.ext (fun _ => degCastHom_comp_degCastHom _ _)

/-- Composing two opposite degree shifts is the identity functor. -/
private def gradedShiftCancelIso (k l : ℤ) (h : k + l = 0) :
    gradedShiftFunctor.{u, v, w} B k ⋙ gradedShiftFunctor B l ≅ 𝟭 _ :=
  NatIso.ofComponents (fun M => gradedShiftCancel M k l h) (by
    intro M N φ
    apply GradedModule.Hom.ext
    intro n
    have hn : n + l + k = n := by omega
    change φ.app (n + l + k) ≫ degCastHom N.piece hn = degCastHom M.piece hn ≫ φ.app n
    rw [degCastHom_eq_eqToHom, degCastHom_eq_eqToHom]
    exact CategoryTheory.eqToHom_naturality (fun p => φ.app p) hn)

/-- The degree shift is an equivalence of the category of right graded modules. -/
private def gradedShiftEquivalence (k : ℤ) :
    GradedModule.{u, v, w} B ≌ GradedModule.{u, v, w} B :=
  CategoryTheory.Equivalence.mk
    (gradedShiftFunctor B k) (gradedShiftFunctor B (-k))
    (gradedShiftCancelIso B k (-k) (by omega)).symm
    (gradedShiftCancelIso B (-k) k (by omega))

private instance gradedShiftFunctor_isEquivalence (k : ℤ) :
    (gradedShiftFunctor.{u, v, w} B k).IsEquivalence :=
  (gradedShiftEquivalence.{u, v, w} B k).isEquivalence_functor

end GradedShift

/-! ### Hom out of a short exact sequence into an injective object -/

/-- Precomposition with the two arrows of a short exact sequence, into an injective object, is
injective, exact and surjective. -/
private lemma hom_shortExact_of_injective {D : Type*} [Category D] [Preadditive D]
    (S : ShortComplex D) (hS : S.ShortExact) {I : D} [Injective I] :
    Function.Injective (fun k : S.X₃ ⟶ I => S.g ≫ k) ∧
      Function.Exact (fun k : S.X₃ ⟶ I => S.g ≫ k) (fun k : S.X₂ ⟶ I => S.f ≫ k) ∧
      Function.Surjective (fun k : S.X₂ ⟶ I => S.f ≫ k) := by
  have : Mono S.f := hS.mono_f
  have : Epi S.g := hS.epi_g
  refine ⟨?_, ?_, ?_⟩
  · exact fun _ _ hab => (cancel_epi S.g).1 hab
  · intro a
    change (S.f ≫ a = 0) ↔ a ∈ Set.range (fun k : S.X₃ ⟶ I => S.g ≫ k)
    constructor
    · intro ha
      have := hS.exact.hasHomology
      let e := S.rightHomologyData
      have := hS.exact.mono_g' e
      refine ⟨Injective.factorThru (e.descQ a ha) e.g', ?_⟩
      dsimp only
      rw [← e.p_g', Category.assoc, Injective.comp_factorThru, e.p_descQ]
    · rintro ⟨b, rfl⟩
      simp
  · exact fun a => ⟨Injective.factorThru a S.f, by simp⟩

/-- Transport of the exactness of a sequence of maps along bijections of the three terms. -/
private lemma exact_of_equiv {P Q T P' Q' T' : Type*} [Zero T] [Zero T']
    (eP : P ≃ P') (eQ : Q ≃ Q') (eT : T ≃ T')
    (p : P → Q) (q : Q → T) (p' : P' → Q') (q' : Q' → T')
    (hp : ∀ x, eQ (p x) = p' (eP x)) (hq : ∀ x, eT (q x) = q' (eQ x))
    (hzero : eT 0 = 0) (hex : Function.Exact p' q') : Function.Exact p q := by
  intro x
  rw [← eT.injective.eq_iff, hzero, hq, hex]
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨y, rfl⟩ := eP.surjective y
    exact ⟨y, eQ.injective ((hp y).trans hy)⟩
  · rintro ⟨y, rfl⟩
    exact ⟨eP y, (hp y).symm⟩

/-! ### Homogeneous morphisms as morphisms of graded modules -/

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}
  (A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- A component of a cochain is unchanged by transporting its source degree. -/
private lemma cochain_v_castHom
    {M N : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    {k : ℤ} (f : Cochain M N k) {p p' q : ℤ} (h : p = p') (hp : p + k = q) (hp' : p' + k = q)
    (U : X.Cᵒᵖ) (x : (M.X p).val.obj U) :
    (f.v p' q hp').val.app U (castHom M.X h U x) = (f.v p q hp).val.app U x := by
  subst p'
  rfl

/-- The morphism of graded modules of a homogeneous morphism of degree `k`. -/
private noncomputable def homogeneousToGraded {M N : DifferentialGradedModule.{u, v, w} A} {k : ℤ}
    (f : HomogeneousMap A M N k) :
    ((forgetToGradedModule A).obj M).shift (-k) ⟶ (forgetToGradedModule A).obj N where
  app p := f.val.v (p + -k) p (by omega)
  map_smul p m U x a := by
    rw [GradedModule.shift_smul]
    change (f.val.v ((p + m) + -k) (p + m) (by omega)).val.app U
      (castHom M.complex.X (show (p + -k) + m = (p + m) + -k by omega) U
        ((M.mul (p + -k) m).app U x a)) = _
    rw [cochain_v_castHom f.val _ (by omega)]
    exact eq_of_heq (f.property (p + -k) p m (by omega) U x a)

/-- The cochain of a morphism of graded modules out of a degree shift. -/
private noncomputable def gradedToCochain {M N : DifferentialGradedModule.{u, v, w} A} {k : ℤ}
    (f : ((forgetToGradedModule A).obj M).shift (-k) ⟶ (forgetToGradedModule A).obj N) :
    Cochain M.complex N.complex k :=
  Cochain.mk (fun p q h => eqToHom (congrArg M.complex.X (show p = q + -k by omega)) ≫ f.app q)

/-- The cochain of a morphism of graded modules commutes with the action. -/
private lemma gradedToCochain_actionLinear {M N : DifferentialGradedModule.{u, v, w} A} {k : ℤ}
    (f : ((forgetToGradedModule A).obj M).shift (-k) ⟶ (forgetToGradedModule A).obj N) :
    IsActionLinear A (gradedToCochain A f) := by
  intro p q m hpq U x a
  have hp : p = q + -k := by omega
  subst p
  have hf := f.map_smul q m U x a
  apply heq_of_eq
  change (f.app (q + m)).val.app U
      ((eqToHom (congrArg M.complex.X (show (q + -k) + m = (q + m) + -k by omega))).val.app U
        ((M.mul (q + -k) m).app U x a)) =
    (N.mul q m).app U ((f.app q).val.app U
      ((eqToHom (congrArg M.complex.X (show q + -k = q + -k by rfl))).val.app U x)) a
  rw [eqToHom_val_app_eq_castHom M.complex.X
      (show (q + -k) + m = (q + m) + -k by omega),
    eqToHom_val_app_eq_castHom M.complex.X (show q + -k = q + -k from rfl)]
  exact hf

/-- Degree-`k` homogeneous morphisms are the morphisms of graded modules out of the degree
shift by `-k`. -/
private noncomputable def homogeneousGradedEquiv
    (M N : DifferentialGradedModule.{u, v, w} A) (k : ℤ) :
    HomogeneousMap A M N k ≃
      (((forgetToGradedModule A).obj M).shift (-k) ⟶ (forgetToGradedModule A).obj N) where
  toFun := homogeneousToGraded A
  invFun f := ⟨gradedToCochain A f, gradedToCochain_actionLinear A f⟩
  left_inv f := by
    apply Subtype.ext
    apply Cochain.ext
    intro p q hpq
    change eqToHom (congrArg M.complex.X (show p = q + -k by omega)) ≫
      f.val.v (q + -k) q (by omega) = f.val.v p q hpq
    have hp : p = q + -k := by omega
    subst p
    simp
  right_inv f := by
    apply GradedModule.Hom.ext
    intro p
    change eqToHom (congrArg M.complex.X (show p + -k = p + -k by rfl)) ≫ f.app p = _
    exact Category.id_comp _

/-- Precomposition on degree-`k` homogeneous morphisms is precomposition with the degree
shift, under the identification with morphisms of graded modules. -/
private lemma homogeneousGradedEquiv_precomp {M N I : DifferentialGradedModule.{u, v, w} A}
    {k : ℤ} (f : M ⟶ N) (a : HomogeneousMap A N I k) (b : HomogeneousMap A M I k)
    (h : b.val = (Cochain.ofHom f.toHomologicalComplex).comp a.val (by omega)) :
    homogeneousGradedEquiv A M I k b =
      GradedModule.shiftHom ((forgetToGradedModule A).map f) (-k) ≫
        homogeneousGradedEquiv A N I k a := by
  apply GradedModule.Hom.ext
  intro p
  change b.val.v (p + -k) p (by omega) = _
  rw [h, Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  rfl

/-! ### Homogeneous morphisms of the differential graded category as graded morphisms -/

/-- The zero cochain commutes with the action. -/
private lemma isActionLinear_zero (M N : DifferentialGradedModule.{u, v, w} A) (k : ℤ) :
    IsActionLinear A (0 : Cochain M.complex N.complex k) := by
  intro p q m hpq U x a
  change HEq (0 : (N.complex.X (q + m)).val.obj U) ((N.mul q m).app U 0 a)
  simp

/-- The homogeneous right-linear map underlying a homogeneous morphism of degree `n`. -/
private noncomputable def dgHomEquiv (M N : DifferentialGradedModule.{u, v, w} A) (n : ℤ) :
    (dgCategoryData.{u, v, w} A).category.Hom (asObject A M) (asObject A N) n ≃
      HomogeneousMap A M N n :=
  Equiv.cast ((dgCategoryData A).homs M N n)

/-- The cochain of the cocycle of a morphism of differential graded modules is the morphism. -/
private lemma dgHomEquiv_cocycleOfHom {M N : DifferentialGradedModule.{u, v, w} A} (f : M ⟶ N) :
    (dgHomEquiv A M N 0 (cocycleOfHom A (dgCategoryData A) f).val).val =
      Cochain.ofHom f.toHomologicalComplex :=
  congrArg Subtype.val ((Equiv.cast ((dgCategoryData A).homs M N 0)).apply_symm_apply _)

/-- Passing to underlying cochains turns composition into composition of cochains. -/
private lemma dgHomEquiv_comp {M N P : DifferentialGradedModule.{u, v, w} A} {m n k : ℤ}
    (h : m + n = k)
    (g : (dgCategoryData.{u, v, w} A).category.Hom (asObject A N) (asObject A P) m)
    (f : (dgCategoryData.{u, v, w} A).category.Hom (asObject A M) (asObject A N) n) :
    (dgHomEquiv A M P k ((dgCategoryData A).category.comp h g f)).val =
      (dgHomEquiv A M N n f).val.comp (dgHomEquiv A N P m g).val (by omega) :=
  eq_of_heq ((dgCategoryData A).composition M N P m n k h g f)

/-- The cochain of a zero homogeneous morphism is zero. -/
private lemma dgHomEquiv_zero (M N : DifferentialGradedModule.{u, v, w} A) (k : ℤ) :
    (dgHomEquiv A M N k 0).val = 0 := by
  let z := (dgHomEquiv A N N 0).symm ⟨0, isActionLinear_zero A N N 0⟩
  have hz : (dgHomEquiv A N N 0 z).val = 0 :=
    congrArg Subtype.val ((dgHomEquiv A N N 0).apply_symm_apply _)
  have h := dgHomEquiv_comp A (show 0 + k = k by omega) z
    (0 : (dgCategoryData.{u, v, w} A).category.Hom (asObject A M) (asObject A N) k)
  simpa only [DGCategory.comp_zero_right, hz, Cochain.comp_zero] using h

/-- Degree-`k` homogeneous morphisms of the differential graded category are the morphisms of
graded modules out of the degree shift by `-k`. -/
private noncomputable def dgGradedEquiv (M N : DifferentialGradedModule.{u, v, w} A) (k : ℤ) :
    (dgCategoryData.{u, v, w} A).category.Hom (asObject A M) (asObject A N) k ≃
      (((forgetToGradedModule A).obj M).shift (-k) ⟶ (forgetToGradedModule A).obj N) :=
  (dgHomEquiv A M N k).trans (homogeneousGradedEquiv A M N k)

/-- The identification sends a zero homogeneous morphism to zero. -/
private lemma dgGradedEquiv_zero (M N : DifferentialGradedModule.{u, v, w} A) (k : ℤ) :
    dgGradedEquiv A M N k 0 = 0 := by
  apply GradedModule.Hom.ext
  intro p
  change (dgHomEquiv A M N k 0).val.v (p + -k) p (by omega) = 0
  rw [dgHomEquiv_zero]
  rfl

/-- The identification turns precomposition with a morphism of differential graded modules into
precomposition with its degree shift. -/
private lemma dgGradedEquiv_precomp {M N I : DifferentialGradedModule.{u, v, w} A} {k : ℤ}
    (f : M ⟶ N)
    (a : (dgCategoryData.{u, v, w} A).category.Hom (asObject A N) (asObject A I) k) :
    dgGradedEquiv A M I k ((dgCategoryData A).category.comp (add_zero k) a
        (cocycleOfHom A (dgCategoryData A) f).val) =
      GradedModule.shiftHom ((forgetToGradedModule A).map f) (-k) ≫ dgGradedEquiv A N I k a := by
  refine homogeneousGradedEquiv_precomp A f _ _ ?_
  refine (dgHomEquiv_comp A (add_zero k) a
    (cocycleOfHom A (dgCategoryData A) f).val).trans ?_
  exact congrArg (fun c => Cochain.comp c (dgHomEquiv A N I k a).val (by omega))
    (dgHomEquiv_cocycleOfHom A f)

/-! ### The shifted sequence of graded modules is short exact -/

/-- Forgetting the differential and shifting the degrees takes a short exact sequence of
differential graded modules to a short exact sequence of graded modules. -/
private theorem gradedShift_shortExact
    (S : ShortComplex (DifferentialGradedModule.{u, v, w} A)) (hS : S.ShortExact) (k : ℤ) :
    ((S.map (forgetToGradedModule A)).map
      (gradedShiftFunctor.{u, v, w} A.toGradedAlgebra k)).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  have := hS.exact.hasHomology
  have : (forgetToGradedModule.{u, v, w} A).PreservesMonomorphisms :=
    CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape _
  have : (forgetToGradedModule.{u, v, w} A).PreservesEpimorphisms :=
    CategoryTheory.preservesEpimorphisms_of_preservesColimitsOfShape _
  have h := hS.map (forgetToGradedModule A)
  have := h.mono_f
  have := h.epi_g
  have := h.exact.hasHomology
  have : (gradedShiftFunctor.{u, v, w} A.toGradedAlgebra k).PreservesMonomorphisms :=
    CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape _
  have : (gradedShiftFunctor.{u, v, w} A.toGradedAlgebra k).PreservesEpimorphisms :=
    CategoryTheory.preservesEpimorphisms_of_preservesColimitsOfShape _
  exact h.map (gradedShiftFunctor.{u, v, w} A.toGradedAlgebra k)

/-! ### The short exact sequence of Hom complexes -/

/-- Precomposition with a closed degree-zero morphism of a differential graded category, on the
degree-`n` homogeneous morphisms into a fixed object. -/
def precompCocycle {S : Type*} [CommRing S] (D : DGCategory S) {x y : D.Obj}
    (c : D.Cocycle x y) (z : D.Obj) (n : ℤ) : D.Hom y z n → D.Hom x z n :=
  fun h => D.comp (add_zero n) h c.val

/-- Precomposition with a closed morphism commutes with the differential of the Hom complex. -/
theorem d_precompCocycle {S : Type*} [CommRing S] (D : DGCategory S) {x y : D.Obj}
    (c : D.Cocycle x y) (z : D.Obj) (n : ℤ) (h : D.Hom y z n) :
    D.d (precompCocycle D c z n h) = precompCocycle D c z (n + 1) (D.d h) := by
  change D.d (D.comp (add_zero n) h c.val) = D.comp (add_zero (n + 1)) (D.d h) c.val
  rw [D.leibniz (add_zero n) h c.val, c.property]
  simp

/-- **Stacks 0FSQ, first display.** For a graded injective differential graded module `I` and
a short exact sequence of differential graded modules — not assumed admissible — the degree-`n`
homogeneous morphisms into `I` form a short exact sequence. -/
@[stacks 0FSQ]
theorem homComplex_shortExact_of_gradedInjective
    {M₁ M₂ M₃ I : DifferentialGradedModule.{u, v, w} A} (f : M₁ ⟶ M₂) (g : M₂ ⟶ M₃)
    (hfg : f ≫ g = 0) (hS : (ShortComplex.mk f g hfg).ShortExact)
    (hI : GradedInjective I) (n : ℤ) :
    Function.Injective (precompCocycle (dgCategoryData.{u, v, w} A).category
        (cocycleOfHom A (dgCategoryData A) g) (asObject A I) n) ∧
      Function.Exact
        (precompCocycle (dgCategoryData.{u, v, w} A).category
          (cocycleOfHom A (dgCategoryData A) g) (asObject A I) n)
        (precompCocycle (dgCategoryData.{u, v, w} A).category
          (cocycleOfHom A (dgCategoryData A) f) (asObject A I) n) ∧
      Function.Surjective (precompCocycle (dgCategoryData.{u, v, w} A).category
        (cocycleOfHom A (dgCategoryData A) f) (asObject A I) n) := by
  have : Injective ((forgetToGradedModule A).obj I) := hI
  have hT := gradedShift_shortExact.{u, v, w} A (ShortComplex.mk f g hfg) hS (-n)
  have hE := hom_shortExact_of_injective _ hT (I := (forgetToGradedModule A).obj I)
  have hjc := dgGradedEquiv_precomp A (I := I) (k := n) g
  have hic := dgGradedEquiv_precomp A (I := I) (k := n) f
  refine ⟨?_, ?_, ?_⟩
  · exact fun a b hab => (dgGradedEquiv A M₃ I n).injective
      (hE.1 ((hjc a).symm.trans ((congrArg (dgGradedEquiv A M₂ I n) hab).trans (hjc b))))
  · exact exact_of_equiv (dgGradedEquiv A M₃ I n) (dgGradedEquiv A M₂ I n)
      (dgGradedEquiv A M₁ I n) _ _ _ _ hjc hic (dgGradedEquiv_zero A M₁ I n) hE.2.1
  · intro a
    obtain ⟨b, hb⟩ := hE.2.2 (dgGradedEquiv A M₁ I n a)
    obtain ⟨b, rfl⟩ := (dgGradedEquiv A M₂ I n).surjective b
    exact ⟨b, (dgGradedEquiv A M₁ I n).injective ((hic b).trans hb)⟩

section HomComplexCohomology

variable {S : Type*} [CommRing S] (D : DGCategory S)

/-- The differential of the Hom complex, as a group homomorphism. -/
def dHom (x y : D.Obj) (n : ℤ) : D.Hom x y n →+ D.Hom x y (n + 1) where
  toFun f := D.d f
  map_zero' := D.d_zero
  map_add' f g := D.d_add f g

/-- The transported differential `D.d'` is additive. -/
lemma d'_add {x y : D.Obj} {m n : ℤ} (e : m + 1 = n) (f g : D.Hom x y m) :
    D.d' e (f + g) = D.d' e f + D.d' e g := by
  subst e
  exact D.d_add f g

/-- The transported differential `D.d'` sends zero to zero. -/
lemma d'_zero_eq {x y : D.Obj} {m n : ℤ} (e : m + 1 = n) :
    D.d' e (0 : D.Hom x y m) = 0 := by
  subst e
  exact D.d_zero

/-- The transported differential `D.d'` commutes with negation. -/
lemma d'_neg {x y : D.Obj} {m n : ℤ} (e : m + 1 = n) (f : D.Hom x y m) :
    D.d' e (-f) = -D.d' e f := by
  subst e
  change D.d (-f) = -D.d f
  rw [← neg_one_smul S f, D.d_smul, neg_one_smul]

/-- The transported differential `D.d'` is `S`-linear. -/
lemma d'_smul {x y : D.Obj} {m n : ℤ} (e : m + 1 = n) (r : S) (f : D.Hom x y m) :
    D.d' e (r • f) = r • D.d' e f := by
  subst e
  exact D.d_smul r f

/-- The differential vanishes on the image of the transported differential `D.d'`. -/
lemma d_d' {x y : D.Obj} {m n : ℤ} (e : m + 1 = n) (f : D.Hom x y m) :
    D.d (D.d' e f) = 0 := by
  subst e
  exact D.d_d f

/-- The cocycles of the Hom complex. -/
def homCocycles (x y : D.Obj) (n : ℤ) : AddSubgroup (D.Hom x y n) := (dHom D x y n).ker

/-- A morphism is a cocycle of the Hom complex if and only if its differential vanishes. -/
lemma mem_homCocycles {x y : D.Obj} {n : ℤ} {f : D.Hom x y n} :
    f ∈ homCocycles D x y n ↔ D.d f = 0 := Iff.rfl

/-- The coboundaries of the Hom complex, inside the cocycles. -/
def homCoboundaries (x y : D.Obj) (n : ℤ) : AddSubgroup ↥(homCocycles D x y n) where
  carrier := {a | ∃ (m : ℤ) (e : m + 1 = n) (h : D.Hom x y m),
    D.d' e h = (a : D.Hom x y n)}
  zero_mem' := ⟨n - 1, by omega, 0, by rw [d'_zero_eq]; rfl⟩
  add_mem' := by
    rintro a b ⟨m, e, h, hh⟩ ⟨m', e', h', hh'⟩
    obtain rfl : m = m' := by omega
    exact ⟨m, e, h + h', by rw [d'_add, hh, hh']; rfl⟩
  neg_mem' := by
    rintro a ⟨m, e, h, hh⟩
    exact ⟨m, e, -h, by rw [d'_neg, hh]; rfl⟩

/-- The cohomology of the Hom complex. -/
abbrev homCohomology (x y : D.Obj) (n : ℤ) : Type _ :=
  ↥(homCocycles D x y n) ⧸ homCoboundaries D x y n

/-! ### Precomposition on the cohomology of the Hom complex -/

/-- Precomposition with a closed degree-zero morphism is additive. -/
lemma precompCocycle_add {x y : D.Obj} (c : D.Cocycle x y) (z : D.Obj) (n : ℤ)
    (h₁ h₂ : D.Hom y z n) :
    precompCocycle D c z n (h₁ + h₂) =
      precompCocycle D c z n h₁ + precompCocycle D c z n h₂ :=
  D.comp_add_left (add_zero n) h₁ h₂ c.val

/-- Precomposition with a closed degree-zero morphism sends zero to zero. -/
lemma precompCocycle_zero {x y : D.Obj} (c : D.Cocycle x y) (z : D.Obj) (n : ℤ) :
    precompCocycle D c z n (0 : D.Hom y z n) = 0 :=
  D.comp_zero_left (add_zero n) c.val

/-- Precomposition with a closed degree-zero morphism commutes with subtraction. -/
lemma precompCocycle_sub {x y : D.Obj} (c : D.Cocycle x y) (z : D.Obj) (n : ℤ)
    (h₁ h₂ : D.Hom y z n) :
    precompCocycle D c z n (h₁ - h₂) =
      precompCocycle D c z n h₁ - precompCocycle D c z n h₂ :=
  D.comp_sub_left (add_zero n) h₁ h₂ c.val

/-- Precomposition with a closed degree-zero morphism commutes with the transported differential
`D.d'`. -/
lemma d'_precompCocycle {x y : D.Obj} {m n : ℤ} (e : m + 1 = n) (c : D.Cocycle x y)
    (z : D.Obj) (h : D.Hom y z m) :
    precompCocycle D c z n (D.d' e h) = D.d' e (precompCocycle D c z m h) := by
  subst e
  exact (d_precompCocycle D c z m h).symm

/-- Precomposition with a closed degree-zero morphism, on the cocycles of the Hom complex. -/
def precompCocycleCocycles {x y : D.Obj} (c : D.Cocycle x y) (z : D.Obj) (n : ℤ) :
    ↥(homCocycles D y z n) →+ ↥(homCocycles D x z n) where
  toFun a := ⟨precompCocycle D c z n (a : D.Hom y z n), by
    rw [mem_homCocycles, d_precompCocycle, show D.d (a : D.Hom y z n) = 0 from a.2,
      precompCocycle_zero]⟩
  map_zero' := Subtype.ext (by
    change precompCocycle D c z n (0 : D.Hom y z n) = 0
    rw [precompCocycle_zero])
  map_add' a b := Subtype.ext (by
    change precompCocycle D c z n ((a : D.Hom y z n) + b) = _
    rw [precompCocycle_add]; rfl)

/-- Precomposition with a closed degree-zero morphism, on the cohomology of the Hom
complex. -/
def precompCocycleCohomology {x y : D.Obj} (c : D.Cocycle x y) (z : D.Obj) (n : ℤ) :
    homCohomology D y z n →+ homCohomology D x z n :=
  QuotientAddGroup.map _ _ (precompCocycleCocycles D c z n) (by
    rintro a ⟨m, e, h, hh⟩
    exact ⟨m, e, precompCocycle D c z m h, by
      rw [← d'_precompCocycle, hh]; rfl⟩)

/-- `precompCocycleCohomology` sends the class of a cocycle to the class of its precomposition. -/
@[simp] lemma precompCocycleCohomology_mk {x y : D.Obj} (c : D.Cocycle x y) (z : D.Obj)
    (n : ℤ) (a : ↥(homCocycles D y z n)) :
    precompCocycleCohomology D c z n (QuotientAddGroup.mk a) =
      QuotientAddGroup.mk (precompCocycleCocycles D c z n a) := rfl

/-- Along the equation `m + 1 = m + 1`, the transported differential `D.d'` is `D.d`. -/
lemma d'_rfl {x y : D.Obj} {m : ℤ} (f : D.Hom x y m) : D.d' rfl f = D.d f := rfl

/-- The differential of the Hom complex commutes with subtraction. -/
lemma d_sub {x y : D.Obj} {n : ℤ} (f g : D.Hom x y n) :
    D.d (f - g) = D.d f - D.d g := by
  rw [sub_eq_add_neg, D.d_add, ← neg_one_smul S g, D.d_smul, neg_one_smul, ← sub_eq_add_neg]

/-- The underlying morphism of `precompCocycleCocycles D c z n a` is the precomposition of the
underlying morphism of `a`. -/
@[simp] lemma precompCocycleCocycles_coe {x y : D.Obj} (c : D.Cocycle x y) (z : D.Obj)
    (n : ℤ) (a : ↥(homCocycles D y z n)) :
    ((precompCocycleCocycles D c z n a : ↥(homCocycles D x z n)) : D.Hom x z n) =
      precompCocycle D c z n (a : D.Hom y z n) := rfl

/-! ### The long exact cohomology sequence -/

/-- A family of connecting maps `δ` makes the cohomology of a sequence of Hom complexes into a
long exact sequence when `δ` is given by the usual lifting recipe — the class of the unique
morphism out of `x₃` whose image is the differential of a lift of a given cocycle — and the
resulting sequence is exact at each of its three kinds of term. -/
def IsLongExactHomCohomology {x₁ x₂ x₃ : D.Obj}
    (cf : D.Cocycle x₁ x₂) (cg : D.Cocycle x₂ x₃) (z : D.Obj)
    (δ : ∀ n : ℤ, homCohomology D x₁ z n →+ homCohomology D x₃ z (n + 1)) : Prop :=
  (∀ (n : ℤ) (a : ↥(homCocycles D x₁ z n)) (b : D.Hom x₂ z n)
      (c : ↥(homCocycles D x₃ z (n + 1))),
      precompCocycle D cf z n b = (a : D.Hom x₁ z n) →
      precompCocycle D cg z (n + 1) (c : D.Hom x₃ z (n + 1)) = D.d b →
      δ n (QuotientAddGroup.mk a) = QuotientAddGroup.mk c) ∧
    (∀ n : ℤ, Function.Exact (precompCocycleCohomology D cg z n)
      (precompCocycleCohomology D cf z n)) ∧
    (∀ n : ℤ, Function.Exact (precompCocycleCohomology D cf z n) (δ n)) ∧
    (∀ n : ℤ, Function.Exact (δ n) (precompCocycleCohomology D cg z (n + 1)))

/-- Every cocycle `a` out of `x₁` has a connecting datum: a lift `b` of `a` along `cf` whose
differential is the image along `cg` of a cocycle `c` out of `x₃`. -/
private theorem exists_connecting_datum {x₁ x₂ x₃ z : D.Obj}
    (cf : D.Cocycle x₁ x₂) (cg : D.Cocycle x₂ x₃)
    (hinj : ∀ n : ℤ, Function.Injective (precompCocycle D cg z n))
    (hexact : ∀ n : ℤ, Function.Exact (precompCocycle D cg z n) (precompCocycle D cf z n))
    (hsurj : ∀ n : ℤ, Function.Surjective (precompCocycle D cf z n))
    (n : ℤ) (a : ↥(homCocycles D x₁ z n)) :
    ∃ (c : ↥(homCocycles D x₃ z (n + 1))) (b : D.Hom x₂ z n),
      precompCocycle D cf z n b = (a : D.Hom x₁ z n) ∧
        precompCocycle D cg z (n + 1) (c : D.Hom x₃ z (n + 1)) = D.d b := by
  obtain ⟨b, hb⟩ := hsurj n (a : D.Hom x₁ z n)
  have hdb : precompCocycle D cf z (n + 1) (D.d b) = 0 := by
    rw [← d_precompCocycle, hb, show D.d (a : D.Hom x₁ z n) = 0 from a.2]
  obtain ⟨c, hc⟩ := (hexact (n + 1) (D.d b)).mp hdb
  refine ⟨⟨c, ?_⟩, b, hb, hc⟩
  rw [mem_homCocycles]
  apply hinj (n + 1 + 1)
  rw [← d_precompCocycle, hc, D.d_d, precompCocycle_zero]

/-- The cohomology class of the cocycle of a connecting datum does not depend on the datum. -/
private theorem connecting_class_eq {x₁ x₂ x₃ z : D.Obj}
    (cf : D.Cocycle x₁ x₂) (cg : D.Cocycle x₂ x₃)
    (hinj : ∀ n : ℤ, Function.Injective (precompCocycle D cg z n))
    (hexact : ∀ n : ℤ, Function.Exact (precompCocycle D cg z n) (precompCocycle D cf z n))
    (n : ℤ) (a : ↥(homCocycles D x₁ z n)) (b b' : D.Hom x₂ z n)
    (c c' : ↥(homCocycles D x₃ z (n + 1)))
    (hb : precompCocycle D cf z n b = (a : D.Hom x₁ z n))
    (hc : precompCocycle D cg z (n + 1) (c : D.Hom x₃ z (n + 1)) = D.d b)
    (hb' : precompCocycle D cf z n b' = (a : D.Hom x₁ z n))
    (hc' : precompCocycle D cg z (n + 1) (c' : D.Hom x₃ z (n + 1)) = D.d b') :
    (QuotientAddGroup.mk c : homCohomology D x₃ z (n + 1)) = QuotientAddGroup.mk c' := by
  rw [QuotientAddGroup.eq_iff_sub_mem]
  have hz : precompCocycle D cf z n (b - b') = 0 := by
    rw [precompCocycle_sub, hb, hb', sub_self]
  obtain ⟨e, he⟩ := (hexact n (b - b')).mp hz
  refine ⟨n, rfl, e, ?_⟩
  change D.d e = ((c - c' : ↥(homCocycles D x₃ z (n + 1))) : D.Hom x₃ z (n + 1))
  rw [AddSubgroup.coe_sub]
  apply hinj (n + 1)
  rw [← d_precompCocycle, he, precompCocycle_sub, hc, hc', d_sub]

/-- The cocycle of a connecting datum of a coboundary is a coboundary. -/
private theorem connecting_class_eq_zero_of_mem_homCoboundaries {x₁ x₂ x₃ z : D.Obj}
    (cf : D.Cocycle x₁ x₂) (cg : D.Cocycle x₂ x₃)
    (hinj : ∀ n : ℤ, Function.Injective (precompCocycle D cg z n))
    (hexact : ∀ n : ℤ, Function.Exact (precompCocycle D cg z n) (precompCocycle D cf z n))
    (hsurj : ∀ n : ℤ, Function.Surjective (precompCocycle D cf z n))
    (n : ℤ) (a : ↥(homCocycles D x₁ z n)) (b : D.Hom x₂ z n)
    (c : ↥(homCocycles D x₃ z (n + 1)))
    (hb : precompCocycle D cf z n b = (a : D.Hom x₁ z n))
    (hc : precompCocycle D cg z (n + 1) (c : D.Hom x₃ z (n + 1)) = D.d b)
    (ha : a ∈ homCoboundaries D x₁ z n) :
    (QuotientAddGroup.mk c : homCohomology D x₃ z (n + 1)) = 0 := by
  obtain ⟨m, e, h, hh⟩ := ha
  obtain ⟨h₂, hh₂⟩ := hsurj m h
  have hb' : precompCocycle D cf z n (D.d' e h₂) = (a : D.Hom x₁ z n) := by
    rw [d'_precompCocycle, hh₂, hh]
  have hc' : precompCocycle D cg z (n + 1)
      ((0 : ↥(homCocycles D x₃ z (n + 1))) : D.Hom x₃ z (n + 1)) = D.d (D.d' e h₂) := by
    rw [d_d', ZeroMemClass.coe_zero, precompCocycle_zero]
  rw [connecting_class_eq D cf cg hinj hexact n a b (D.d' e h₂) c 0 hb hc hb' hc']
  rfl

/-- Exactness at a quotient term can be checked on representatives. -/
private theorem exact_quotient_mk {G G' T : Type*} [AddCommGroup G] [AddCommGroup G'] [Zero T]
    {s : AddSubgroup G} {s' : AddSubgroup G'} (f : G' ⧸ s' → G ⧸ s) (g : G ⧸ s → T)
    (h₁ : ∀ a : G, g (QuotientAddGroup.mk a) = 0 → ∃ y, f y = QuotientAddGroup.mk a)
    (h₂ : ∀ t : G', g (f (QuotientAddGroup.mk t)) = 0) : Function.Exact f g := by
  intro u
  induction u using QuotientAddGroup.induction_on with
  | H a =>
    refine ⟨h₁ a, ?_⟩
    rintro ⟨y, hy⟩
    induction y using QuotientAddGroup.induction_on with
    | H t => rw [← hy]; exact h₂ t

/-- Exactness of the cohomology sequence of a degreewise short exact sequence of Hom complexes
at the middle term. -/
private theorem exact_precompCocycleCohomology {x₁ x₂ x₃ z : D.Obj}
    (cf : D.Cocycle x₁ x₂) (cg : D.Cocycle x₂ x₃)
    (hinj : ∀ n : ℤ, Function.Injective (precompCocycle D cg z n))
    (hexact : ∀ n : ℤ, Function.Exact (precompCocycle D cg z n) (precompCocycle D cf z n))
    (hsurj : ∀ n : ℤ, Function.Surjective (precompCocycle D cf z n)) (n : ℤ) :
    Function.Exact (precompCocycleCohomology D cg z n) (precompCocycleCohomology D cf z n) := by
  refine exact_quotient_mk _ _ (fun v hv => ?_) fun t => ?_
  · rw [precompCocycleCohomology_mk, QuotientAddGroup.eq_zero_iff] at hv
    obtain ⟨m, e, h, hh⟩ := hv
    obtain ⟨h₂, hh₂⟩ := hsurj m h
    have hz : precompCocycle D cf z n ((v : D.Hom x₂ z n) - D.d' e h₂) = 0 := by
      rw [precompCocycle_sub, d'_precompCocycle, hh₂, hh, precompCocycleCocycles_coe, sub_self]
    obtain ⟨w, hw⟩ := (hexact n _).mp hz
    have hwc : D.d w = 0 := by
      apply hinj (n + 1)
      rw [← d_precompCocycle, hw, d_sub, d_d', show D.d (v : D.Hom x₂ z n) = 0 from v.2,
        precompCocycle_zero, sub_zero]
    refine ⟨QuotientAddGroup.mk ⟨w, hwc⟩, ?_⟩
    rw [precompCocycleCohomology_mk, QuotientAddGroup.eq_iff_sub_mem]
    refine ⟨m, e, -h₂, ?_⟩
    rw [d'_neg, AddSubgroup.coe_sub, precompCocycleCocycles_coe, hw]
    abel
  · rw [precompCocycleCohomology_mk, precompCocycleCohomology_mk, QuotientAddGroup.eq_zero_iff]
    refine ⟨n - 1, by omega, 0, ?_⟩
    rw [d'_zero_eq, precompCocycleCocycles_coe, precompCocycleCocycles_coe,
      (hexact n).apply_apply_eq_zero]

/-- Exactness of the cohomology sequence of a degreewise short exact sequence of Hom complexes
at the source of a connecting map given by the lifting recipe. -/
private theorem exact_precompCocycleCohomology_connecting {x₁ x₂ x₃ z : D.Obj}
    (cf : D.Cocycle x₁ x₂) (cg : D.Cocycle x₂ x₃)
    (hinj : ∀ n : ℤ, Function.Injective (precompCocycle D cg z n))
    (hexact : ∀ n : ℤ, Function.Exact (precompCocycle D cg z n) (precompCocycle D cf z n))
    (hsurj : ∀ n : ℤ, Function.Surjective (precompCocycle D cf z n))
    (δ : ∀ n : ℤ, homCohomology D x₁ z n →+ homCohomology D x₃ z (n + 1))
    (hδ : ∀ (n : ℤ) (a : ↥(homCocycles D x₁ z n)) (b : D.Hom x₂ z n)
      (c : ↥(homCocycles D x₃ z (n + 1))),
      precompCocycle D cf z n b = (a : D.Hom x₁ z n) →
      precompCocycle D cg z (n + 1) (c : D.Hom x₃ z (n + 1)) = D.d b →
      δ n (QuotientAddGroup.mk a) = QuotientAddGroup.mk c) (n : ℤ) :
    Function.Exact (precompCocycleCohomology D cf z n) (δ n) := by
  refine exact_quotient_mk _ _ (fun a ha => ?_) fun t => ?_
  · obtain ⟨c, b, hb, hc⟩ := exists_connecting_datum D cf cg hinj hexact hsurj n a
    rw [hδ n a b c hb hc, QuotientAddGroup.eq_zero_iff] at ha
    obtain ⟨m, e, h, hh⟩ := ha
    obtain rfl : n = m := by omega
    rw [d'_rfl] at hh
    have hdv : D.d (b - precompCocycle D cg z n h) = 0 := by
      rw [d_sub, ← hc, d_precompCocycle, hh, sub_self]
    have hv : precompCocycleCocycles D cf z n ⟨_, hdv⟩ = a := by
      apply Subtype.ext
      rw [precompCocycleCocycles_coe]
      change precompCocycle D cf z n (b - precompCocycle D cg z n h) = _
      rw [precompCocycle_sub, hb, (hexact n).apply_apply_eq_zero, sub_zero]
    exact ⟨QuotientAddGroup.mk ⟨_, hdv⟩, by rw [precompCocycleCohomology_mk, hv]⟩
  · have h0 : precompCocycle D cg z (n + 1)
        ((0 : ↥(homCocycles D x₃ z (n + 1))) : D.Hom x₃ z (n + 1)) =
          D.d (t : D.Hom x₂ z n) := by
      rw [ZeroMemClass.coe_zero, precompCocycle_zero, show D.d (t : D.Hom x₂ z n) = 0 from t.2]
    rw [precompCocycleCohomology_mk,
      hδ n (precompCocycleCocycles D cf z n t) (t : D.Hom x₂ z n) 0
        (precompCocycleCocycles_coe D cf z n t).symm h0]
    rfl

/-- Exactness of the cohomology sequence of a degreewise short exact sequence of Hom complexes
at the target of a connecting map given by the lifting recipe. -/
private theorem exact_connecting_precompCocycleCohomology {x₁ x₂ x₃ z : D.Obj}
    (cf : D.Cocycle x₁ x₂) (cg : D.Cocycle x₂ x₃)
    (hinj : ∀ n : ℤ, Function.Injective (precompCocycle D cg z n))
    (hexact : ∀ n : ℤ, Function.Exact (precompCocycle D cg z n) (precompCocycle D cf z n))
    (hsurj : ∀ n : ℤ, Function.Surjective (precompCocycle D cf z n))
    (δ : ∀ n : ℤ, homCohomology D x₁ z n →+ homCohomology D x₃ z (n + 1))
    (hδ : ∀ (n : ℤ) (a : ↥(homCocycles D x₁ z n)) (b : D.Hom x₂ z n)
      (c : ↥(homCocycles D x₃ z (n + 1))),
      precompCocycle D cf z n b = (a : D.Hom x₁ z n) →
      precompCocycle D cg z (n + 1) (c : D.Hom x₃ z (n + 1)) = D.d b →
      δ n (QuotientAddGroup.mk a) = QuotientAddGroup.mk c) (n : ℤ) :
    Function.Exact (δ n) (precompCocycleCohomology D cg z (n + 1)) := by
  refine exact_quotient_mk _ _ (fun c hc0 => ?_) fun a => ?_
  · rw [precompCocycleCohomology_mk, QuotientAddGroup.eq_zero_iff] at hc0
    obtain ⟨m, e, b, hb⟩ := hc0
    obtain rfl : n = m := by omega
    rw [d'_rfl, precompCocycleCocycles_coe] at hb
    have hda : D.d (precompCocycle D cf z n b) = 0 := by
      rw [d_precompCocycle, hb, (hexact (n + 1)).apply_apply_eq_zero]
    exact ⟨QuotientAddGroup.mk ⟨_, hda⟩, hδ n ⟨_, hda⟩ b c rfl hb.symm⟩
  · obtain ⟨c', b, hb, hc⟩ := exists_connecting_datum D cf cg hinj hexact hsurj n a
    rw [hδ n a b c' hb hc, precompCocycleCohomology_mk, QuotientAddGroup.eq_zero_iff]
    exact ⟨n, rfl, b, by rw [d'_rfl, precompCocycleCocycles_coe, hc]⟩

/-- The long exact cohomology sequence attached to a sequence of Hom complexes which is
short exact in every degree. -/
theorem exists_isLongExactHomCohomology {x₁ x₂ x₃ z : D.Obj}
    (cf : D.Cocycle x₁ x₂) (cg : D.Cocycle x₂ x₃)
    (hinj : ∀ n : ℤ, Function.Injective (precompCocycle D cg z n))
    (hexact : ∀ n : ℤ, Function.Exact (precompCocycle D cg z n) (precompCocycle D cf z n))
    (hsurj : ∀ n : ℤ, Function.Surjective (precompCocycle D cf z n)) :
    ∃ δ, IsLongExactHomCohomology D cf cg z δ := by
  classical
  choose cc bb hbb hcc using exists_connecting_datum D cf cg hinj hexact hsurj
  have hφadd : ∀ (n : ℤ) (a a' : ↥(homCocycles D x₁ z n)),
      (QuotientAddGroup.mk (cc n (a + a')) : homCohomology D x₃ z (n + 1)) =
        QuotientAddGroup.mk (cc n a) + QuotientAddGroup.mk (cc n a') := by
    intro n a a'
    rw [← QuotientAddGroup.mk_add]
    refine connecting_class_eq D cf cg hinj hexact n (a + a') (bb n (a + a'))
      (bb n a + bb n a') (cc n (a + a')) (cc n a + cc n a') (hbb n (a + a')) (hcc n (a + a'))
      ?_ ?_
    · rw [precompCocycle_add, hbb n a, hbb n a', AddSubgroup.coe_add]
    · rw [AddSubgroup.coe_add, precompCocycle_add, hcc n a, hcc n a', D.d_add]
  obtain ⟨δ, hδ⟩ : ∃ δ : ∀ n : ℤ, homCohomology D x₁ z n →+ homCohomology D x₃ z (n + 1),
      ∀ (n : ℤ) (a : ↥(homCocycles D x₁ z n)),
        δ n (QuotientAddGroup.mk a) = QuotientAddGroup.mk (cc n a) :=
    ⟨fun n => QuotientAddGroup.lift _
      (AddMonoidHom.mk'
        (fun a => (QuotientAddGroup.mk (cc n a) : homCohomology D x₃ z (n + 1)))
        (hφadd n))
      (fun a ha => connecting_class_eq_zero_of_mem_homCoboundaries D cf cg hinj hexact hsurj
        n a (bb n a) (cc n a) (hbb n a) (hcc n a) ha), fun _ _ => rfl⟩
  have hchar : ∀ (n : ℤ) (a : ↥(homCocycles D x₁ z n)) (b : D.Hom x₂ z n)
      (c : ↥(homCocycles D x₃ z (n + 1))),
      precompCocycle D cf z n b = (a : D.Hom x₁ z n) →
      precompCocycle D cg z (n + 1) (c : D.Hom x₃ z (n + 1)) = D.d b →
      δ n (QuotientAddGroup.mk a) = QuotientAddGroup.mk c := by
    intro n a b c hb hc
    rw [hδ]
    exact connecting_class_eq D cf cg hinj hexact n a (bb n a) b (cc n a) c (hbb n a) (hcc n a)
      hb hc
  exact ⟨δ, hchar, exact_precompCocycleCohomology D cf cg hinj hexact hsurj,
    exact_precompCocycleCohomology_connecting D cf cg hinj hexact hsurj δ hchar,
    exact_connecting_precompCocycleCohomology D cf cg hinj hexact hsurj δ hchar⟩

/-! ### Degree zero: the morphisms of the homotopy category -/

/-- The group structure on the homotopy classes of closed degree-zero morphisms from `x` to
`y`, namely the one of the preadditive structure of the homotopy category. -/
@[instance_reducible]
noncomputable def homotopyClassAddCommGroup (x y : D.Obj) :
    AddCommGroup (D.HomotopyClass x y) :=
  (DGCategory.homotopyPreadditive D).homGroup x y

attribute [local instance] homotopyClassAddCommGroup

/-- The sum of two morphisms of the homotopy category is represented by the sum of any two
representing cocycles. -/
theorem homotopyClass_mk_add (x y : D.Obj) (f g : D.Cocycle x y) :
    Quotient.mk (D.homotopySetoid x y) f + Quotient.mk (D.homotopySetoid x y) g =
      Quotient.mk (D.homotopySetoid x y) ⟨f.1 + g.1, by rw [D.d_add, f.2, g.2, add_zero]⟩ :=
  DGCategory.homotopyPreadditive_mk_add D x y f g

/-- The zero morphism of the homotopy category is represented by the zero cocycle. -/
theorem homotopyClass_zero (x y : D.Obj) :
    (0 : D.HomotopyClass x y) = Quotient.mk (D.homotopySetoid x y) ⟨0, D.d_zero⟩ :=
  DGCategory.homotopyPreadditive_zero D x y

/-- In degree zero the cocycles of the Hom complex are the closed degree-zero morphisms. -/
def homCocyclesZeroEquiv (x y : D.Obj) : ↥(homCocycles D x y 0) ≃ D.Cocycle x y :=
  Equiv.subtypeEquivRight (fun _ => mem_homCocycles D)

/-- In degree zero the coboundaries of the Hom complex are the differentials of the morphisms
of degree `-1`. -/
lemma mem_homCoboundaries_zero {x y : D.Obj} (a : ↥(homCocycles D x y 0)) :
    a ∈ homCoboundaries D x y 0 ↔
      ∃ h : D.Hom x y (-1),
        D.d' (show (-1 : ℤ) + 1 = 0 by omega) h = (a : D.Hom x y 0) := by
  constructor
  · rintro ⟨m, e, h, hh⟩
    obtain rfl : (-1 : ℤ) = m := by omega
    exact ⟨h, hh⟩
  · rintro ⟨h, hh⟩
    exact ⟨-1, by omega, h, hh⟩

/-- The underlying bijection of `homCohomologyZeroEquiv`: in degree zero the cohomology of the
Hom complex is the set of closed degree-zero morphisms modulo homotopy, which is the set of
morphisms of the homotopy category. -/
def homCohomologyZeroBijection (x y : D.Obj) :
    homCohomology D x y 0 ≃ D.HomotopyClass x y :=
  Quotient.congr (homCocyclesZeroEquiv D x y) (by
    intro a b
    change QuotientAddGroup.leftRel (homCoboundaries D x y 0) a b ↔ D.Homotopic _ _
    rw [QuotientAddGroup.leftRel_apply, mem_homCoboundaries_zero]
    constructor
    · rintro ⟨h, hh⟩
      refine ⟨-h, ?_⟩
      change (a : D.Hom x y 0) - (b : D.Hom x y 0) =
        D.d' (show (-1 : ℤ) + 1 = 0 by omega) (-h)
      rw [d'_neg, hh, AddSubgroup.coe_add, AddSubgroup.coe_neg]
      abel
    · rintro ⟨h, hh⟩
      refine ⟨-h, ?_⟩
      change D.d' (show (-1 : ℤ) + 1 = 0 by omega) (-h) =
        ((-a + b : ↥(homCocycles D x y 0)) : D.Hom x y 0)
      rw [d'_neg, AddSubgroup.coe_add, AddSubgroup.coe_neg,
        show D.d' (show (-1 : ℤ) + 1 = 0 by omega) h
          = (a : D.Hom x y 0) - (b : D.Hom x y 0) from hh.symm]
      abel)

/-- **Stacks 0FSQ, degree zero.** The degree-zero cohomology of the Hom complex is the group of
morphisms from `x` to `y` in the homotopy category: the closed degree-zero morphisms modulo
homotopy, with the addition of the preadditive structure of the homotopy category. -/
noncomputable def homCohomologyZeroEquiv (x y : D.Obj) :
    homCohomology D x y 0 ≃+ D.HomotopyClass x y where
  toEquiv := homCohomologyZeroBijection D x y
  map_add' u v := by
    induction u using QuotientAddGroup.induction_on with
    | H a =>
      induction v using QuotientAddGroup.induction_on with
      | H b => exact (homotopyClass_mk_add D x y _ _).symm

/-- `homCohomologyZeroEquiv` sends the class of a degree-zero cocycle to its homotopy class. -/
@[simp] lemma homCohomologyZeroEquiv_mk (x y : D.Obj) (a : ↥(homCocycles D x y 0)) :
    homCohomologyZeroEquiv D x y (QuotientAddGroup.mk a) =
      Quotient.mk (D.homotopySetoid x y) (homCocyclesZeroEquiv D x y a) := rfl

/-- Under the identification of the degree-zero cohomology of the Hom complexes with the
morphisms of the homotopy category, precomposition with a closed degree-zero morphism is
composition in the homotopy category. -/
lemma homCohomologyZeroEquiv_precompCocycleCohomology {x y : D.Obj} (c : D.Cocycle x y)
    (z : D.Obj) (u : homCohomology D y z 0) :
    homCohomologyZeroEquiv D x z (precompCocycleCohomology D c z 0 u) =
      D.compK (homCohomologyZeroEquiv D y z u) (Quotient.mk (D.homotopySetoid x y) c) := by
  induction u using QuotientAddGroup.induction_on with
  | H a =>
    rw [precompCocycleCohomology_mk, homCohomologyZeroEquiv_mk, homCohomologyZeroEquiv_mk]
    rfl

/-! ### Degree `n`: the morphisms into the `n`-fold translate -/

section Shift

variable (B : DGCategory.ShiftAxiomB D)

/-- Multiplying by the unit `(-1) ^ j` does not change whether an element vanishes. -/
private lemma neg_one_pow_smul_eq_zero_iff {M : Type*} [AddCommGroup M] [Module S M] (j : ℕ)
    (z : M) : (-1 : S) ^ j • z = 0 ↔ z = 0 :=
  ((isUnit_neg_one (α := S)).pow j).smul_eq_zero

/-- Transport of homotopy classes along an equality of the target object. -/
noncomputable def homotopyClassCongrRight {x y y' : D.Obj} (h : y = y') :
    D.HomotopyClass x y ≃+ D.HomotopyClass x y' :=
  @Eq.rec D.Obj y (fun z _ => D.HomotopyClass x y ≃+ D.HomotopyClass x z)
    (AddEquiv.refl _) y' h

/-- Transport of the target object commutes with composition in the homotopy category. -/
private lemma homotopyClassCongrRight_compK {x y z z' : D.Obj} (h : z = z')
    (u : D.HomotopyClass y z) (c : D.Cocycle x y) :
    homotopyClassCongrRight D h (D.compK u (Quotient.mk (D.homotopySetoid x y) c)) =
      D.compK (homotopyClassCongrRight D h u) (Quotient.mk (D.homotopySetoid x y) c) := by
  cases h
  rfl

/-- The identification of axiom (B): degree-`m` morphisms into `y` are degree-`k` morphisms into
the `n`-fold translate of `y`, whenever `k + n = m`. -/
noncomputable def shiftHom (n : ℤ) (x y : D.Obj) {k m : ℤ} (e : k + n = m) :
    D.Hom x y m ≃+ D.Hom x ((B.shiftFunctor n).obj y) k :=
  @Eq.rec ℤ (k + n)
    (fun p _ => D.Hom x y p ≃+ D.Hom x ((B.shiftFunctor n).obj y) k)
    (B.toShift n x y k).toAddEquiv m e

/-- The identification of axiom (B) intertwines the differentials of the two Hom complexes, up
to the sign `(-1) ^ n`. -/
private lemma shiftHom_d (n : ℤ) (x y : D.Obj) {k k' m m' : ℤ}
    (e : k + n = m) (e' : k' + n = m') (hk : k + 1 = k') (hm : m + 1 = m')
    (f : D.Hom x y m) :
    shiftHom D B n x y e' (D.d' hm f) =
      (-1 : S) ^ n.natAbs • D.d' hk (shiftHom D B n x y e f) := by
  cases e'
  cases e
  cases hk
  exact B.toShift_d n x y k f

/-- Axiom (B)'s compatibility of the identification with composition on the right, with the
degrees given by explicit equations. -/
private lemma toShift_comp_right' (n : ℤ) {x y z : D.Obj} {k k' : ℤ} (hk : k + 0 = k')
    (hc : (k + n) + 0 = k' + n) (g : D.Hom y z (k + n)) (fc : D.Hom x y 0) :
    B.toShift n x z k' (D.comp hc g fc) = D.comp hk (B.toShift n y z k g) fc := by
  cases hk
  exact B.toShift_comp_right n g fc

/-- Precomposition with a closed degree-zero morphism commutes with the identification
of axiom (B). -/
private lemma shiftHom_precompCocycle (n : ℤ) {x y z : D.Obj} (c : D.Cocycle x y) {k m : ℤ}
    (e : k + n = m) (h : D.Hom y z m) :
    shiftHom D B n x z e (precompCocycle D c z m h) =
      precompCocycle D c ((B.shiftFunctor n).obj z) k (shiftHom D B n y z e h) := by
  cases e
  exact toShift_comp_right' D B n (add_zero k) (add_zero (k + n)) h c.val

/-- The identification of axiom (B) matches the cocycles of the two Hom complexes. -/
theorem shiftHom_mem_homCocycles (n : ℤ) (x y : D.Obj) {k m : ℤ} (e : k + n = m)
    (f : D.Hom x y m) :
    shiftHom D B n x y e f ∈ homCocycles D x ((B.shiftFunctor n).obj y) k ↔
      f ∈ homCocycles D x y m := by
  have h := shiftHom_d D B n x y e (show (k + 1) + n = m + 1 by omega)
    (rfl : k + 1 = k + 1) (rfl : m + 1 = m + 1) f
  rw [d'_rfl, d'_rfl] at h
  rw [mem_homCocycles, mem_homCocycles]
  refine ⟨fun hz => ?_, fun hz => ?_⟩
  · apply (shiftHom D B n x y (show (k + 1) + n = m + 1 by omega)).injective
    rw [h, hz, smul_zero, map_zero]
  · rw [← neg_one_pow_smul_eq_zero_iff (S := S) n.natAbs, ← h, hz, map_zero]

/-- The identification of axiom (B), on the cocycles of the Hom complex. -/
noncomputable def shiftHomCocycles (n : ℤ) (x y : D.Obj) {k m : ℤ} (e : k + n = m) :
    ↥(homCocycles D x y m) ≃+ ↥(homCocycles D x ((B.shiftFunctor n).obj y) k) where
  toFun a := ⟨shiftHom D B n x y e (a : D.Hom x y m),
    (shiftHom_mem_homCocycles D B n x y e _).2 a.2⟩
  invFun b := ⟨(shiftHom D B n x y e).symm (b : D.Hom x ((B.shiftFunctor n).obj y) k),
    (shiftHom_mem_homCocycles D B n x y e _).1
      (((shiftHom D B n x y e).apply_symm_apply _).symm ▸ b.2)⟩
  left_inv _ := Subtype.ext ((shiftHom D B n x y e).symm_apply_apply _)
  right_inv _ := Subtype.ext ((shiftHom D B n x y e).apply_symm_apply _)
  map_add' _ _ := Subtype.ext (map_add (shiftHom D B n x y e) _ _)

private lemma shiftHomCocycles_coe (n : ℤ) (x y : D.Obj) {k m : ℤ} (e : k + n = m)
    (a : ↥(homCocycles D x y m)) :
    ((shiftHomCocycles D B n x y e a :
        ↥(homCocycles D x ((B.shiftFunctor n).obj y) k)) :
      D.Hom x ((B.shiftFunctor n).obj y) k) = shiftHom D B n x y e (a : D.Hom x y m) := rfl

/-- The identification of axiom (B) matches the coboundaries of the two Hom complexes. -/
theorem shiftHomCocycles_mem_homCoboundaries (n : ℤ) (x y : D.Obj) {k m : ℤ}
    (e : k + n = m) (a : ↥(homCocycles D x y m)) :
    shiftHomCocycles D B n x y e a ∈ homCoboundaries D x ((B.shiftFunctor n).obj y) k ↔
      a ∈ homCoboundaries D x y m := by
  refine ⟨fun hb => ?_, fun hb => ?_⟩
  · obtain ⟨kk, hk, h', hh'⟩ := hb
    refine ⟨kk + n, by omega, (shiftHom D B n x y (rfl : kk + n = kk + n)).symm
      ((-1 : S) ^ n.natAbs • h'), ?_⟩
    apply (shiftHom D B n x y e).injective
    rw [shiftHom_d D B n x y (rfl : kk + n = kk + n) e hk (show kk + n + 1 = m by omega),
      AddEquiv.apply_symm_apply, d'_smul, smul_smul, ← pow_add, ← two_mul, pow_mul,
      neg_one_sq, one_pow, one_smul, hh', shiftHomCocycles_coe]
  · obtain ⟨mm, hm, h, hh⟩ := hb
    refine ⟨k - 1, by omega, (-1 : S) ^ n.natAbs •
      shiftHom D B n x y (show k - 1 + n = mm by omega) h, ?_⟩
    rw [d'_smul, ← shiftHom_d D B n x y (show k - 1 + n = mm by omega) e
        (show k - 1 + 1 = k by omega) hm, hh, shiftHomCocycles_coe]

/-- The identification of axiom (B) carries the coboundaries of the Hom complex onto the
coboundaries of the Hom complex of the translate. -/
theorem map_homCoboundaries_shiftHomCocycles (n : ℤ) (x y : D.Obj) {k m : ℤ} (e : k + n = m) :
    AddSubgroup.map (shiftHomCocycles D B n x y e).toAddMonoidHom (homCoboundaries D x y m) =
      homCoboundaries D x ((B.shiftFunctor n).obj y) k := by
  refine AddSubgroup.ext fun b => ?_
  simp only [AddSubgroup.mem_map, AddEquiv.coe_toAddMonoidHom]
  refine ⟨?_, fun hb => ?_⟩
  · rintro ⟨a, ha, rfl⟩
    exact (shiftHomCocycles_mem_homCoboundaries D B n x y e a).2 ha
  · refine ⟨(shiftHomCocycles D B n x y e).symm b, ?_,
      (shiftHomCocycles D B n x y e).apply_symm_apply b⟩
    refine (shiftHomCocycles_mem_homCoboundaries D B n x y e _).1 ?_
    rwa [AddEquiv.apply_symm_apply]

/-- The identification of axiom (B), on the cohomology of the Hom complex. -/
noncomputable def shiftHomCohomology (n : ℤ) (x y : D.Obj) {k m : ℤ} (e : k + n = m) :
    homCohomology D x y m ≃+ homCohomology D x ((B.shiftFunctor n).obj y) k :=
  QuotientAddGroup.congr _ _ (shiftHomCocycles D B n x y e)
    (map_homCoboundaries_shiftHomCocycles D B n x y e)

private lemma shiftHomCohomology_mk (n : ℤ) (x y : D.Obj) {k m : ℤ} (e : k + n = m)
    (a : ↥(homCocycles D x y m)) :
    shiftHomCohomology D B n x y e (QuotientAddGroup.mk a) =
      QuotientAddGroup.mk (shiftHomCocycles D B n x y e a) := rfl

private lemma shiftHomCohomology_precompCocycleCohomology (n : ℤ) {x y z : D.Obj}
    (c : D.Cocycle x y) {k m : ℤ} (e : k + n = m) (u : homCohomology D y z m) :
    shiftHomCohomology D B n x z e (precompCocycleCohomology D c z m u) =
      precompCocycleCohomology D c ((B.shiftFunctor n).obj z) k
        (shiftHomCohomology D B n y z e u) := by
  induction u using QuotientAddGroup.induction_on with
  | H a =>
    rw [precompCocycleCohomology_mk, shiftHomCohomology_mk, shiftHomCohomology_mk,
      precompCocycleCohomology_mk]
    exact congrArg QuotientAddGroup.mk (Subtype.ext
      (shiftHom_precompCocycle D B n c e (a : D.Hom y z m)))

/-- **Stacks 0FSQ, degree `n`.** The degree-`n` cohomology of the Hom complex from `x` to `y` is
the group of morphisms from `x` into the `n`-fold translate of `y` in the homotopy category. -/
noncomputable def homCohomologyShiftEquiv (x y : D.Obj) (n : ℤ) :
    homCohomology D x y n ≃+ D.HomotopyClass x ((B.shiftFunctor n).obj y) :=
  (shiftHomCohomology D B n x y (zero_add n)).trans
    (homCohomologyZeroEquiv D x ((B.shiftFunctor n).obj y))

/-- Under the degree-`n` identification, precomposition with a closed degree-zero morphism is
composition in the homotopy category. -/
lemma homCohomologyShiftEquiv_precompCocycleCohomology {x y : D.Obj} (c : D.Cocycle x y)
    (z : D.Obj) (n : ℤ) (u : homCohomology D y z n) :
    homCohomologyShiftEquiv D B x z n (precompCocycleCohomology D c z n u) =
      D.compK (homCohomologyShiftEquiv D B y z n u) (Quotient.mk (D.homotopySetoid x y) c) := by
  change homCohomologyZeroEquiv D x ((B.shiftFunctor n).obj z)
      (shiftHomCohomology D B n x z (zero_add n) (precompCocycleCohomology D c z n u)) = _
  rw [shiftHomCohomology_precompCocycleCohomology,
    homCohomologyZeroEquiv_precompCocycleCohomology]
  rfl

/-- On objects, the translation functor of the homotopy category is the shift of axiom (B). -/
lemma shiftFunctor_K_obj (n : ℤ) (x : D.Obj) :
    letI : HasShift D.K ℤ := B.kShift
    (CategoryTheory.shiftFunctor D.K n).obj (x : D.K) = (B.shiftFunctor n).obj x :=
  congrArg (fun F : D.K ⥤ D.K => F.obj (x : D.K)) (B.kShift_functor n)

end Shift

end HomComplexCohomology

/-! ### The long exact sequence of Hom groups into a graded injective module -/

attribute [local instance] homotopyClassAddCommGroup

/-- The cohomology of the short exact sequence of Hom complexes into a graded injective
differential graded module is a long exact sequence. -/
theorem exists_isLongExactHomCohomology_of_gradedInjective
    {M₁ M₂ M₃ I : DifferentialGradedModule.{u, v, w} A} (f : M₁ ⟶ M₂) (g : M₂ ⟶ M₃)
    (hfg : f ≫ g = 0) (hS : (ShortComplex.mk f g hfg).ShortExact)
    (hI : GradedInjective I) :
    ∃ δ, IsLongExactHomCohomology (dgCategoryData.{u, v, w} A).category
      (cocycleOfHom A (dgCategoryData A) f) (cocycleOfHom A (dgCategoryData A) g)
      (asObject A I) δ :=
  exists_isLongExactHomCohomology _ _ _
    (fun n => (homComplex_shortExact_of_gradedInjective A f g hfg hS hI n).1)
    (fun n => (homComplex_shortExact_of_gradedInjective A f g hfg hS hI n).2.1)
    (fun n => (homComplex_shortExact_of_gradedInjective A f g hfg hS hI n).2.2)

/-- Morphisms from `M` into the `n`-fold translate of `I` in the homotopy category of the
differential graded category of right differential graded `A`-modules. -/
abbrev homotopyHomShift (M I : DifferentialGradedModule.{u, v, w} A) (n : ℤ) : Type _ :=
  (toDGHomotopyCategory.{u, v, w} A).obj M ⟶
    (shiftFunctor (dgCategoryData.{u, v, w} A).category.K n).obj
      ((toDGHomotopyCategory.{u, v, w} A).obj I)

/-- Precomposition with a morphism of differential graded modules, on the morphisms into the
`n`-fold translate of `I` in the homotopy category. -/
noncomputable def precompHomotopyHom {M N : DifferentialGradedModule.{u, v, w} A} (f : M ⟶ N)
    (I : DifferentialGradedModule.{u, v, w} A) (n : ℤ) :
    homotopyHomShift A N I n →+ homotopyHomShift A M I n :=
  Preadditive.leftComp _ ((toDGHomotopyCategory A).map f)

/-- On objects, the translation functor of the differential graded homotopy category is the
shift functor of the chosen cone situation. -/
theorem shiftFunctor_dgK_obj (n : ℤ) (x : (dgCategoryData.{u, v, w} A).category.Obj) :
    (shiftFunctor (dgCategoryData.{u, v, w} A).category.K n).obj x =
      ((dgConeSituation A).shift.shiftFunctor n).obj x :=
  shiftFunctor_K_obj (dgCategoryData.{u, v, w} A).category (dgConeSituation A).shift n x

/-- **Stacks 0FSQ, the terms of the long exact sequence.** The degree-`n` cohomology of the Hom
complex from `M` into `I` is the group of morphisms from `M` into the `n`-fold translate of `I`
in the homotopy category. -/
noncomputable def homCohomologyEquivHomotopyHom (M I : DifferentialGradedModule.{u, v, w} A)
    (n : ℤ) :
    homCohomology (dgCategoryData.{u, v, w} A).category (asObject A M) (asObject A I) n ≃+
      homotopyHomShift A M I n :=
  (homCohomologyShiftEquiv (dgCategoryData.{u, v, w} A).category (dgConeSituation A).shift
      (asObject A M) (asObject A I) n).trans
    (homotopyClassCongrRight (dgCategoryData.{u, v, w} A).category
      (shiftFunctor_dgK_obj A n (asObject A I)).symm)

/-- Under that identification, precomposition on the cohomology of the Hom complexes is
composition in the homotopy category. -/
lemma homCohomologyEquivHomotopyHom_precomp {M N I : DifferentialGradedModule.{u, v, w} A}
    (f : M ⟶ N) (n : ℤ)
    (u : homCohomology (dgCategoryData.{u, v, w} A).category (asObject A N) (asObject A I) n) :
    homCohomologyEquivHomotopyHom A M I n
        (precompCocycleCohomology (dgCategoryData.{u, v, w} A).category
          (cocycleOfHom A (dgCategoryData A) f) (asObject A I) n u) =
      precompHomotopyHom A f I n (homCohomologyEquivHomotopyHom A N I n u) := by
  have key := homCohomologyShiftEquiv_precompCocycleCohomology
    (dgCategoryData.{u, v, w} A).category (dgConeSituation A).shift
    (cocycleOfHom A (dgCategoryData A) f) (asObject A I) n u
  exact (congrArg (fun t => homotopyClassCongrRight (dgCategoryData.{u, v, w} A).category
    (shiftFunctor_dgK_obj A n (asObject A I)).symm t) key).trans
    (homotopyClassCongrRight_compK _ _ _ _)

private lemma symm_homCohomologyEquivHomotopyHom_precomp
    {M N I : DifferentialGradedModule.{u, v, w} A} (f : M ⟶ N) (n : ℤ)
    (x : homotopyHomShift A N I n) :
    (homCohomologyEquivHomotopyHom A M I n).symm (precompHomotopyHom A f I n x) =
      precompCocycleCohomology (dgCategoryData.{u, v, w} A).category
        (cocycleOfHom A (dgCategoryData A) f) (asObject A I) n
        ((homCohomologyEquivHomotopyHom A N I n).symm x) := by
  refine (homCohomologyEquivHomotopyHom A M I n).injective ?_
  refine Eq.trans ((homCohomologyEquivHomotopyHom A M I n).apply_symm_apply _) ?_
  refine Eq.trans ?_ (homCohomologyEquivHomotopyHom_precomp A f n
    ((homCohomologyEquivHomotopyHom A N I n).symm x)).symm
  exact congrArg (precompHomotopyHom A f I n)
    ((homCohomologyEquivHomotopyHom A N I n).apply_symm_apply x).symm

/-- Transport of the exactness of a sequence of maps along additive bijections of the three
terms. -/
private lemma exact_of_addEquiv {P Q T P' Q' T' : Type*} [AddGroup T] [AddGroup T']
    (eP : P ≃ P') (eQ : Q ≃ Q') (eT : T ≃+ T')
    (p : P → Q) (q : Q → T) (p' : P' → Q') (q' : Q' → T')
    (hp : ∀ x, eQ (p x) = p' (eP x)) (hq : ∀ x, eT (q x) = q' (eQ x))
    (hex : Function.Exact p' q') : Function.Exact p q :=
  exact_of_equiv eP eQ eT.toEquiv p q p' q' hp hq (map_zero eT) hex

/-- **Stacks 0FSQ.** Let `I` be a graded injective differential graded module and let
`0 → M₁ → M₂ → M₃ → 0` be a short exact sequence of differential graded modules, *not* assumed
admissible. Then the groups of morphisms into the translates of `I` in the homotopy category sit
in a long exact sequence
`Hom(M₃, I[n]) → Hom(M₂, I[n]) → Hom(M₁, I[n]) → Hom(M₃, I[n+1])`,
the first two maps being composition in the homotopy category. The point is that this holds even
though the given sequence is not admissible, so that it defines no distinguished triangle. -/
@[stacks 0FSQ]
theorem exists_longExact_homotopyHomShift_of_gradedInjective
    {M₁ M₂ M₃ I : DifferentialGradedModule.{u, v, w} A} (f : M₁ ⟶ M₂) (g : M₂ ⟶ M₃)
    (hfg : f ≫ g = 0) (hS : (ShortComplex.mk f g hfg).ShortExact)
    (hI : GradedInjective I) :
    ∃ δ : ∀ n : ℤ, homotopyHomShift A M₁ I n →+ homotopyHomShift A M₃ I (n + 1),
      (∀ n : ℤ, Function.Exact (precompHomotopyHom A g I n) (precompHomotopyHom A f I n)) ∧
        (∀ n : ℤ, Function.Exact (precompHomotopyHom A f I n) (δ n)) ∧
        (∀ n : ℤ, Function.Exact (δ n) (precompHomotopyHom A g I (n + 1))) := by
  obtain ⟨δ, -, hex₁, hex₂, hex₃⟩ :=
    exists_isLongExactHomCohomology_of_gradedInjective A f g hfg hS hI
  have hδ : ∀ (n : ℤ) (x : homotopyHomShift A M₁ I n),
      (homCohomologyEquivHomotopyHom A M₃ I (n + 1)).symm
          ((homCohomologyEquivHomotopyHom A M₃ I (n + 1))
            (δ n ((homCohomologyEquivHomotopyHom A M₁ I n).symm x))) =
        δ n ((homCohomologyEquivHomotopyHom A M₁ I n).symm x) :=
    fun n x => (homCohomologyEquivHomotopyHom A M₃ I (n + 1)).symm_apply_apply _
  refine ⟨fun n => (homCohomologyEquivHomotopyHom A M₃ I (n + 1)).toAddMonoidHom.comp
    ((δ n).comp (homCohomologyEquivHomotopyHom A M₁ I n).symm.toAddMonoidHom), ?_, ?_, ?_⟩
  · intro n
    exact exact_of_addEquiv (homCohomologyEquivHomotopyHom A M₃ I n).symm.toEquiv
      (homCohomologyEquivHomotopyHom A M₂ I n).symm.toEquiv
      (homCohomologyEquivHomotopyHom A M₁ I n).symm _ _ _ _
      (symm_homCohomologyEquivHomotopyHom_precomp A g n)
      (symm_homCohomologyEquivHomotopyHom_precomp A f n) (hex₁ n)
  · intro n
    exact exact_of_addEquiv (homCohomologyEquivHomotopyHom A M₂ I n).symm.toEquiv
      (homCohomologyEquivHomotopyHom A M₁ I n).symm.toEquiv
      (homCohomologyEquivHomotopyHom A M₃ I (n + 1)).symm _ _ _ _
      (symm_homCohomologyEquivHomotopyHom_precomp A f n)
      (hδ n) (hex₂ n)
  · intro n
    exact exact_of_addEquiv (homCohomologyEquivHomotopyHom A M₁ I n).symm.toEquiv
      (homCohomologyEquivHomotopyHom A M₃ I (n + 1)).symm.toEquiv
      (homCohomologyEquivHomotopyHom A M₂ I (n + 1)).symm _ _ _ _
      (hδ n)
      (symm_homCohomologyEquivHomotopyHom_precomp A g (n + 1)) (hex₃ n)

end SheafOfModules.DifferentialGradedModule
