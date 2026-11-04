module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeGradedModuleCoefficients
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedRelativeTensor

/-!
# The relative tensor product of a free graded module with a graded module

Let `(C, O)` be a ringed site, let `A` be a sheaf of graded `O`-algebras, let `S` be a sheaf of
graded sets and let `N` be a left graded `A`-module. The source's computation of the relative
tensor product of the free graded `A`-module `A[S]` with `N` is

`A[S] ⊗_A N = O[S] ⊗_O N = N[S]`,

where `N[S]` is the free graded module on `S` with coefficients in `N`: in degree `n` the
sheafification of `U ↦ ⨁_{s ∈ S(U)} s · N^{n - deg s}(U)`. This file proves that identification
degreewise, together with its naturality in `N`.

The two maps are built from the two universal properties at hand. Out of the tensor product one
descends the `A`-balanced bilinear family which sends `(s · a) ⊗ y` to `s · ay`, placed in the
summand of `s`; out of `N[S]` one extends along the sheafification the map which sends the
summand `s · y` to `s ⊗ y`, for `s` the canonical generator of `A[S]` attached to `s`. The two
composites are computed on local sections of the two presentations and come out as the
identities.

## Main definitions

* `SheafOfModules.freeTensorCoeffPres` is the coefficient map on the presentation of `A[S]^p`,
  and `SheafOfModules.freeTensorCoeffBilinPres` the bilinear map it assembles into;
  `SheafOfModules.freeTensorCoeffBilin` is its extension to the sheafification.
* `SheafOfModules.freeTensorBalanced` is the resulting `A`-balanced bilinear family, and
  `SheafOfModules.freeTensorCoeff` its descent `A[S] ⊗_A N ⟶ N[S]` in degree `n`.
* `SheafOfModules.coeffTensorPresAddHom` sends the summand `s · y` of the presentation of
  `N[S]^n` to the local section `s ⊗ y`, `SheafOfModules.coeffTensorPres` is it as a morphism of
  presheaves of modules and `SheafOfModules.coeffTensorFree` its factorization through the
  sheafification.

## Main results

* `SheafOfModules.freeTensorCoeffIso`: degree `n` of the relative tensor product `A[S] ⊗_A N` is
  `N[S]`.
* `SheafOfModules.freeTensorCoeff_naturality`: the identification is natural in the left graded
  `A`-module, carrying `SheafOfModules.RelativeTensor.gradedTensorMap` to
  `SheafOfModules.coeffPieceMap`.
* `SheafOfModules.freeTensorCoeffPres_presAct` is what makes the family balanced: on the
  presentation, acting by a homogeneous section `a` of `A` on the module variable and acting by
  `a` on the coefficient produce the same coefficients.
* `SheafOfModules.tmul_freeUnit_freeOf`: every summand of the presentation of `A[S]^p`, tensored
  with a coefficient, is a canonical generator tensored with the product of the two
  coefficients. This is the computation behind one of the two composites.
* `SheafOfModules.RelativeTensor.tmul_castHom_left` and
  `SheafOfModules.RelativeTensor.tmul_castHom_right` transport a local section `x ⊗ y` along an
  equality of the degrees of its factors, which is what the `n - i` bookkeeping needs.

## Implementation notes

The universe of the pieces of the algebra, of the pieces of the modules and of the values of
the sheaf of graded sets is one and the same `m`. The first two are tied together by the
relative tensor product, whose summand `P^r ⊗_O A^s ⊗_O N^t` mixes them; the third is then
forced, since the pieces of `A[S]` live in `Type (max w m)` for `S` valued in `Type w` while
the relative tensor product needs them in `Type m`.

Two spellings of one and the same type recur and must be kept apart in *statements*, exactly as
in `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FreeGradedModule.lean`: the sections of a
presentation are `SheafOfModules.freeSections` or `SheafOfModules.coeffSections` when written as
a direct sum and `↑((freePres A S n).obj U)` or `↑((coeffPres S X n).obj U)` when written as
sections of a presheaf of modules. They are definitionally equal, so term-mode proofs never
notice, but `rw` does. Accordingly the proofs that cross the boundary are chains of `Eq.trans`
and `congrArg`, and `SheafOfModules.freeUnit_zero`, `SheafOfModules.coeffUnit_zero` and
`SheafOfModules.coeffUnit_add` restate additivity of the two sheafification units in the
direct-sum spelling, which is the one the induction principles produce.

The two local bijectivity instances of `SheafOfModules.freeUnit` are restated here for the
structure sheaf of a ringed site; see the comment at the head of the `Sheafify` section for
why the ones upstream are not found.

## References

* [Stacks Project, Tag 0FSG](https://stacks.math.columbia.edu/tag/0FSG)
* [Stacks Project, Tag 0FSF](https://stacks.math.columbia.edu/tag/0FSF)
* [Stacks Project, Tag 0FR2](https://stacks.math.columbia.edu/tag/0FR2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

universe t m v u

namespace SheafOfModules

open Stacks Stacks.SheafOfGradedSets

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] {Osharp : Sheaf J CommRingCat.{t}}

section Transport

variable {A : GradedAlgebra.{t, m} (toRingCat J Osharp)}

/-- Transporting the algebra argument of the action of a left graded module along an equality
of degrees. -/
theorem LeftGradedModule.smul_castHom_alg (N : LeftGradedModule.{t, m, m} A) {i i' l k : ℤ}
    (h : i = i') (h' : i' + l = k) (h'' : i + l = k) (U : Cᵒᵖ)
    (a : (A.piece i).val.obj U) (y : (N.piece l).val.obj U) :
    castHom N.piece h' U (N.smul i' l U (castHom A.piece h U a) y) =
      castHom N.piece h'' U (N.smul i l U a y) := by
  subst h; rfl

/-- Transport along an equality of degrees commutes with a homomorphism of left graded
modules. -/
theorem LeftGradedModule.app_castHom {N N' : LeftGradedModule.{t, m, m} A} (f : N ⟶ N')
    {k k' : ℤ} (h : k = k') (U : Cᵒᵖ) (x : (N.piece k).val.obj U) :
    (f.app k').val.app U (castHom N.piece h U x) =
      castHom N'.piece h U ((f.app k).val.app U x) := by
  subst h; rfl

end Transport

section Presentation

variable [HasWeakSheafify J (Type m)] (A : GradedAlgebra.{t, m} (toRingCat J Osharp))
  (S : SheafOfGradedSets.{m} J) (N : LeftGradedModule.{t, m, m} A)

/-- The degree bookkeeping of the identification `A[S] ⊗_A N = N[S]`: a generator of degree `j`
contributes `A^{p - j}` to `A[S]^p`, which acting on `N^q` lands in `N^{n - j}`. -/
theorem freeTensorDeg {p q n : ℤ} (h : p + q = n) (j : ℤ) : p - j + q = n - j := by omega

/-- The coefficients of the image of `ζ ⊗ y` in `N[S]^n`, for `ζ` a section of the presentation
of `A[S]^p` and `y` a section of `N^q`: the summand `s · a` of `ζ` contributes `s · ay`. -/
noncomputable def freeTensorCoeffPres (p q n : ℤ) (h : p + q = n) (U : Cᵒᵖ)
    (y : (N.piece q).val.obj U) :
    freeSections A S p U →+ coeffSections S N.piece n U :=
  _root_.DirectSum.toAddMonoid fun r =>
    ((_root_.DirectSum.of (fun r' : S.Index U => ((N.piece (n - r'.1)).val.obj U : Type m))
          r).comp (castHom N.piece (freeTensorDeg h r.1) U)).comp
      ((N.smul (p - r.1) q U).flip y)

/-- On the summand `s · x` of the presentation of `A[S]^p`, the coefficient map tensored with `y`
is `s · xy`. -/
@[simp] theorem freeTensorCoeffPres_freeOf (p q n : ℤ) (h : p + q = n) (U : Cᵒᵖ)
    (y : (N.piece q).val.obj U) (j : ℤ) (s : S.sheaf.obj.obj U) (hs : S.HasDegree U s j)
    (x : (A.piece (p - j)).val.obj U) :
    freeTensorCoeffPres A S N p q n h U y (freeOf A S p U j s hs x) =
      coeffOf S N.piece n U j s hs
        (castHom N.piece (freeTensorDeg h j) U (N.smul (p - j) q U x y)) :=
  _root_.DirectSum.toAddMonoid_of _ _ _

/-- The coefficients of `ζ ⊗ y` are additive in `y`. -/
theorem freeTensorCoeffPres_add_right (p q n : ℤ) (h : p + q = n) (U : Cᵒᵖ)
    (y y' : (N.piece q).val.obj U) (ζ : freeSections A S p U) :
    freeTensorCoeffPres A S N p q n h U (y + y') ζ =
      freeTensorCoeffPres A S N p q n h U y ζ + freeTensorCoeffPres A S N p q n h U y' ζ := by
  induction ζ using freeSections_induction with
  | hzero => rw [map_zero, map_zero, map_zero, add_zero]
  | hof j s hs x =>
    rw [freeTensorCoeffPres_freeOf, freeTensorCoeffPres_freeOf, freeTensorCoeffPres_freeOf,
      map_add (N.smul (p - j) q U x), map_add (castHom N.piece (freeTensorDeg h j) U),
      coeffOf_add]
  | hadd ζ ζ' hζ hζ' =>
    rw [map_add, map_add, map_add, hζ, hζ']
    abel

/-- The coefficients of `ζ ⊗ y` are linear over `O` in `ζ`. -/
theorem freeTensorCoeffPres_smul_left (p q n : ℤ) (h : p + q = n) (U : Cᵒᵖ)
    (r : (toRingCat J Osharp).obj.obj U) (y : (N.piece q).val.obj U)
    (ζ : freeSections A S p U) :
    freeTensorCoeffPres A S N p q n h U y (r • ζ) =
      r • freeTensorCoeffPres A S N p q n h U y ζ := by
  induction ζ using freeSections_induction with
  | hzero => rw [smul_zero, map_zero, smul_zero]
  | hof j s hs x =>
    rw [← freeOf_smul, freeTensorCoeffPres_freeOf, freeTensorCoeffPres_freeOf,
      N.smul_smul_left, castHom_smul, coeffOf_smul]
  | hadd ζ ζ' hζ hζ' => rw [smul_add, map_add, map_add, hζ, hζ', smul_add]

/-- The coefficients of `ζ ⊗ y` are linear over `O` in `y`. -/
theorem freeTensorCoeffPres_smul_right (p q n : ℤ) (h : p + q = n) (U : Cᵒᵖ)
    (r : (toRingCat J Osharp).obj.obj U) (y : (N.piece q).val.obj U)
    (ζ : freeSections A S p U) :
    freeTensorCoeffPres A S N p q n h U (r • y) ζ =
      r • freeTensorCoeffPres A S N p q n h U y ζ := by
  induction ζ using freeSections_induction with
  | hzero => rw [map_zero, map_zero, smul_zero]
  | hof j s hs x =>
    rw [freeTensorCoeffPres_freeOf, freeTensorCoeffPres_freeOf, N.smul_smul_right,
      castHom_smul, coeffOf_smul]
  | hadd ζ ζ' hζ hζ' => rw [map_add, map_add, hζ, hζ', smul_add]

/-- The coefficients of `ζ ⊗ y` commute with restriction of sections. -/
theorem freeTensorCoeffPres_naturality (p q n : ℤ) (h : p + q = n) {U V : Cᵒᵖ} (f : U ⟶ V)
    (y : (N.piece q).val.obj U) (ζ : freeSections A S p U) :
    coeffRestrict S N.piece n f (freeTensorCoeffPres A S N p q n h U y ζ) =
      freeTensorCoeffPres A S N p q n h V (sectionRestrict (N.piece q).val f y)
        (freeRestrict A S p f ζ) := by
  induction ζ using freeSections_induction with
  | hzero => rw [map_zero, map_zero, map_zero, map_zero]
  | hof j s hs x =>
    rw [freeTensorCoeffPres_freeOf, coeffRestrict_coeffOf, freeRestrict_freeOf,
      freeTensorCoeffPres_freeOf]
    refine coeffOf_congr S N.piece n V j _ _ rfl ?_
    rw [sectionRestrict_castHom N.piece (freeTensorDeg h j) f]
    exact congrArg (castHom N.piece (freeTensorDeg h j) V)
      (N.smul_naturality (p - j) q f x y)
  | hadd ζ ζ' hζ hζ' => rw [map_add, map_add, map_add, map_add, hζ, hζ']

/-- The bilinear map which sends `ζ ⊗ y` to the family of its coefficients, for `ζ` a section
of the presentation of `A[S]^p`. -/
noncomputable def freeTensorCoeffBilinPres (p q n : ℤ) (h : p + q = n) :
    Stacks.BilinearMap (freePres A S p) (N.piece q).val (coeffPres S N.piece n) where
  app U := AddMonoidHom.mk'
    (fun ζ => AddMonoidHom.mk' (fun y => freeTensorCoeffPres A S N p q n h U y ζ)
      (fun y y' => freeTensorCoeffPres_add_right A S N p q n h U y y' ζ))
    (fun ζ ζ' => by
      ext y : 1
      exact map_add (freeTensorCoeffPres A S N p q n h U y) ζ ζ')
  map_smul_left U r ζ y := freeTensorCoeffPres_smul_left A S N p q n h U r y ζ
  map_smul_right U r ζ y := freeTensorCoeffPres_smul_right A S N p q n h U r y ζ
  naturality {_ _} f ζ y := freeTensorCoeffPres_naturality A S N p q n h f y ζ

/-- The bilinear map `SheafOfModules.freeTensorCoeffBilinPres` evaluated at `ζ` and `y` is the
family of coefficients of `ζ ⊗ y`. -/
@[simp] theorem freeTensorCoeffBilinPres_app (p q n : ℤ) (h : p + q = n) (U : Cᵒᵖ)
    (ζ : (freePres A S p).obj U) (y : (N.piece q).val.obj U) :
    (freeTensorCoeffBilinPres A S N p q n h).app U ζ y =
      freeTensorCoeffPres A S N p q n h U y ζ := rfl

/-- **The presentation is balanced.** Acting on a section of the presentation of `A[S]^p` by a
homogeneous section `a` of `A` has the same effect on coefficients as letting `a` act on the
coefficient `y`: both give `s · bay` on the summand of `s · b`. -/
theorem freeTensorCoeffPres_presAct (p i q n : ℤ) (h₁ : p + i + q = n) (h₂ : p + (i + q) = n)
    (U : Cᵒᵖ) (ζ : freeSections A S p U) (a : (A.piece i).val.obj U)
    (y : (N.piece q).val.obj U) :
    freeTensorCoeffPres A S N (p + i) q n h₁ U y (presAct A S p i U ζ a) =
      freeTensorCoeffPres A S N p (i + q) n h₂ U (N.smul i q U a y) ζ := by
  induction ζ using freeSections_induction with
  | hzero => rw [map_zero (presAct A S p i U), AddMonoidHom.zero_apply, map_zero, map_zero]
  | hof j s hs b =>
    rw [presAct_freeOf, freeTensorCoeffPres_freeOf, freeTensorCoeffPres_freeOf]
    refine coeffOf_congr S N.piece n U j hs hs rfl ?_
    refine (N.smul_castHom_alg (freeDeg p i j) (freeTensorDeg h₁ j) (by omega) U
      ((A.mul (p - j) i).app U b a) y).trans ?_
    exact Cofree.castHom_eq_castHom (by omega) (freeTensorDeg h₂ j) U
      (N.mul_smul (p - j) i q U b a y)
  | hadd ζ ζ' hζ hζ' =>
    rw [map_add (presAct A S p i U), AddMonoidHom.add_apply, map_add, hζ, hζ', map_add]

end Presentation

section PresentationNaturality

variable [HasWeakSheafify J (Type m)] (A : GradedAlgebra.{t, m} (toRingCat J Osharp))
  (S : SheafOfGradedSets.{m} J) {N N' : LeftGradedModule.{t, m, m} A} (f : N ⟶ N')

/-- The coefficients of `ζ ⊗ y` are natural in the left graded module. -/
theorem coeffPresAddHom_freeTensorCoeffPres (p q n : ℤ) (h : p + q = n) (U : Cᵒᵖ)
    (y : (N.piece q).val.obj U) (ζ : freeSections A S p U) :
    coeffPresAddHom S (fun k => f.app k) n U (freeTensorCoeffPres A S N p q n h U y ζ) =
      freeTensorCoeffPres A S N' p q n h U ((f.app q).val.app U y) ζ := by
  induction ζ using freeSections_induction with
  | hzero => rw [map_zero, map_zero, map_zero]
  | hof j s hs x =>
    rw [freeTensorCoeffPres_freeOf, coeffPresAddHom_coeffOf, freeTensorCoeffPres_freeOf]
    refine coeffOf_congr S N'.piece n U j hs hs rfl ?_
    rw [show homSections (f.app (n - j)) U
          (castHom N.piece (freeTensorDeg h j) U (N.smul (p - j) q U x y)) =
        (f.app (n - j)).val.app U
          (castHom N.piece (freeTensorDeg h j) U (N.smul (p - j) q U x y)) from rfl,
      LeftGradedModule.app_castHom f (freeTensorDeg h j) U, f.map_smul (p - j) q U x y]
  | hadd ζ ζ' hζ hζ' => rw [map_add, map_add, map_add, hζ, hζ']

end PresentationNaturality

section TensorIndexTransport

variable [HasWeakSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
  {A : GradedAlgebra.{t, m} (toRingCat J Osharp)} (P : GradedModule.{t, m, m} A)
  (N : LeftGradedModule.{t, m, m} A)

/-- A local section `x ⊗ y` of the relative tensor product with a zero left factor is zero. -/
theorem RelativeTensor.tmul_zero_left (n : ℤ) (p : TensorIndex n) (X : Cᵒᵖ)
    (y : (N.piece p.1.2).val.obj X) : RelativeTensor.tmul P N n p X 0 y = 0 := by
  have hz := map_zero (((RelativeTensor.tmulBalanced P N n).app p).app X)
  rw [show RelativeTensor.tmul P N n p X 0 y =
    ((RelativeTensor.tmulBalanced P N n).app p).app X 0 y from rfl, hz]
  rfl

/-- A local section `x ⊗ y` of the relative tensor product is additive in its left factor. -/
theorem RelativeTensor.tmul_add_left (n : ℤ) (p : TensorIndex n) (X : Cᵒᵖ)
    (x x' : (P.piece p.1.1).val.obj X) (y : (N.piece p.1.2).val.obj X) :
    RelativeTensor.tmul P N n p X (x + x') y =
      RelativeTensor.tmul P N n p X x y + RelativeTensor.tmul P N n p X x' y :=
  ((RelativeTensor.tmulBalanced P N n).app p).map_add_left X x x' y

/-- Transport of a local section `x ⊗ y` along an equality of the degree of its left factor. -/
theorem RelativeTensor.tmul_castHom_left (n a a' b : ℤ) (h : a + b = n) (h' : a' + b = n)
    (ha : a = a') (X : Cᵒᵖ) (x : (P.piece a).val.obj X) (y : (N.piece b).val.obj X) :
    RelativeTensor.tmul P N n ⟨(a', b), h'⟩ X (castHom P.piece ha X x) y =
      RelativeTensor.tmul P N n ⟨(a, b), h⟩ X x y := by
  subst ha; rfl

/-- Transport of a local section `x ⊗ y` along an equality of the degree of its right factor. -/
theorem RelativeTensor.tmul_castHom_right (n a b b' : ℤ) (h : a + b = n) (h' : a + b' = n)
    (hb : b = b') (X : Cᵒᵖ) (x : (P.piece a).val.obj X) (y : (N.piece b).val.obj X) :
    RelativeTensor.tmul P N n ⟨(a, b'), h'⟩ X x (castHom N.piece hb X y) =
      RelativeTensor.tmul P N n ⟨(a, b), h⟩ X x y := by
  subst hb; rfl

end TensorIndexTransport

section Sheafify

variable [HasWeakSheafify J (Type m)] [HasWeakSheafify J AddCommGrpCat.{m}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
  (A : GradedAlgebra.{t, m} (toRingCat J Osharp)) (S : SheafOfGradedSets.{m} J)
  (N : LeftGradedModule.{t, m, m} A)

/-! The two local bijectivity instances of `SheafOfModules.freeUnit` are restated for the
structure sheaf of a ringed site. The instances of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FreeGradedModule.lean` are stated for an
arbitrary sheaf of rings `R`, and their discrimination tree keys mention `R.obj`; here the
sheaf of rings is `CategoryTheory.Sheaf.toRingCat J Osharp`, a reducible abbreviation whose
underlying presheaf is syntactically a composite, so those keys do not match and instance
resolution does not reach them. -/

/-- The map from the presentation of `A[S]^p` to its sheafification is locally surjective. -/
instance isLocallySurjective_freeUnit_toRingCat (p : ℤ) :
    PresheafOfModules.IsLocallySurjective J (freeUnit A S p) :=
  inferInstanceAs (PresheafOfModules.IsLocallySurjective J
    (PresheafOfModules.toSheafify (𝟙 (toRingCat J Osharp).obj)
      (CategoryTheory.toSheafify J (coeffPres S A.piece p).presheaf)))

/-- The map from the presentation of `A[S]^p` to its sheafification is locally injective. -/
instance isLocallyInjective_freeUnit_toRingCat (p : ℤ) :
    PresheafOfModules.IsLocallyInjective J (freeUnit A S p) :=
  inferInstanceAs (PresheafOfModules.IsLocallyInjective J
    (PresheafOfModules.toSheafify (𝟙 (toRingCat J Osharp).obj)
      (CategoryTheory.toSheafify J (coeffPres S A.piece p).presheaf)))

/-- The bilinear map `A[S]^p × N^q → N[S]^n`, for `p + q = n`: the unique extension to the
sheafification of the coefficient map of the presentation. -/
noncomputable def freeTensorCoeffBilin (p q n : ℤ) (h : p + q = n) :
    Stacks.BilinearMap (freePiece A S p).val (N.piece q).val (coeffPiece S N.piece n).val :=
  Stacks.BilinearMap.extend (coeffPiece S N.piece n).isSheaf (freeUnit A S p)
    (postcompBilin (freeTensorCoeffBilinPres A S N p q n h) (coeffUnit S N.piece n))

/-- On the image of a section `ζ` of the presentation of `A[S]^p`, the bilinear map
`SheafOfModules.freeTensorCoeffBilin` gives the image in `N[S]^n` of the coefficients of
`ζ ⊗ y`. -/
@[simp] theorem freeTensorCoeffBilin_unit (p q n : ℤ) (h : p + q = n) (U : Cᵒᵖ)
    (ζ : (freePres A S p).obj U) (y : (N.piece q).val.obj U) :
    (freeTensorCoeffBilin A S N p q n h).app U ((freeUnit A S p).app U ζ) y =
      (coeffUnit S N.piece n).app U (freeTensorCoeffPres A S N p q n h U y ζ) :=
  Stacks.BilinearMap.extendVal_app (coeffPiece S N.piece n).isSheaf (freeUnit A S p)
    (postcompBilin (freeTensorCoeffBilinPres A S N p q n h) (coeffUnit S N.piece n)) ζ y

/-- The coefficients of `x ⊗ y`, computed on a local lift of `x` to the presentation. -/
theorem freeTensorCoeffBilin_lift (p q n : ℤ) (h : p + q = n) (U : Cᵒᵖ)
    (x : (freePiece A S p).val.obj U) (y : (N.piece q).val.obj U) {Y : Cᵒᵖ} (f : U ⟶ Y)
    (ζ : (freePres A S p).obj Y)
    (hζ : (freeUnit A S p).app Y ζ = (freePiece A S p).val.map f x) :
    sectionRestrict (coeffPiece S N.piece n).val f
        ((freeTensorCoeffBilin A S N p q n h).app U x y) =
      (coeffUnit S N.piece n).app Y
        (freeTensorCoeffPres A S N p q n h Y (sectionRestrict (N.piece q).val f y) ζ) :=
  ((freeTensorCoeffBilin A S N p q n h).naturality f x y).trans
    ((congrArg (fun z => (freeTensorCoeffBilin A S N p q n h).app Y z
        (sectionRestrict (N.piece q).val f y)) hζ).symm.trans
      (freeTensorCoeffBilin_unit A S N p q n h Y ζ (sectionRestrict (N.piece q).val f y)))

/-- **The coefficient maps form an `A`-balanced family**, so that they descend to the relative
tensor product `A[S] ⊗_A N`. -/
noncomputable def freeTensorBalanced (n : ℤ) :
    RelativeTensor.Balanced (freeGradedModule A S) N (coeffPiece S N.piece n).val n where
  app p := freeTensorCoeffBilin A S N p.1.1 p.1.2 n p.2
  balanced i U x a y := by
    refine Stacks.eq_of_forall_lift (coeffPiece S N.piece n).isSheaf.isSeparated
      (freeUnit A S i.1.1) x _ _ ?_
    intro Y f ζ hζ
    have hlift := freeActBilin_lift A S i.1.1 i.1.2.1 U x a f ζ hζ
    have e₁ := freeTensorCoeffBilin_lift A S N (i.1.1 + i.1.2.1) i.1.2.2 n i.2 U
      ((freeActBilin A S i.1.1 i.1.2.1).app U x a) y f
      (presAct A S i.1.1 i.1.2.1 Y ζ (sectionRestrict (A.piece i.1.2.1).val f a)) hlift.symm
    have e₂ := freeTensorCoeffBilin_lift A S N i.1.1 (i.1.2.1 + i.1.2.2) n
      (RelativeTensor.rightIndex i).2 U x (N.smul i.1.2.1 i.1.2.2 U a y) f ζ hζ
    refine e₁.trans (Eq.trans ?_ e₂.symm)
    refine congrArg ((coeffUnit S N.piece n).app Y) ?_
    refine (freeTensorCoeffPres_presAct A S N i.1.1 i.1.2.1 i.1.2.2 n i.2
      (RelativeTensor.rightIndex i).2 Y ζ (sectionRestrict (A.piece i.1.2.1).val f a)
      (sectionRestrict (N.piece i.1.2.2).val f y)).trans ?_
    exact congrArg (fun z => freeTensorCoeffPres A S N i.1.1 (i.1.2.1 + i.1.2.2) n
      (RelativeTensor.rightIndex i).2 Y z ζ) (N.smul_naturality i.1.2.1 i.1.2.2 f a y).symm

/-- **The identification `A[S] ⊗_A N = N[S]`, in degree `n`**, from the relative tensor product
to the free graded module on `S` with coefficients in `N`. -/
noncomputable def freeTensorCoeff (n : ℤ) :
    RelativeTensor.gradedTensor (freeGradedModule A S) N n ⟶ coeffPiece S N.piece n :=
  (freeTensorBalanced A S N n).desc (freeGradedModule A S) N

/-- The identification `SheafOfModules.freeTensorCoeff` sends the local section `x ⊗ y` to the
value of `SheafOfModules.freeTensorCoeffBilin` at `x` and `y`. -/
@[simp] theorem freeTensorCoeff_tmul (n : ℤ) (p : TensorIndex n) (U : Cᵒᵖ)
    (x : (freePiece A S p.1.1).val.obj U) (y : (N.piece p.1.2).val.obj U) :
    (freeTensorCoeff A S N n).val.app U
        (RelativeTensor.tmul (freeGradedModule A S) N n p U x y) =
      (freeTensorCoeffBilin A S N p.1.1 p.1.2 n p.2).app U x y :=
  RelativeTensor.Balanced.desc_tmul (freeGradedModule A S) N (freeTensorBalanced A S N n) p U x y

/-- The index `(j, n - j)` of the summand of the presentation of `A[S] ⊗_A N` in degree `n`
holding a generator of degree `j` together with its coefficient. -/
abbrev freeGenIndex (n j : ℤ) : TensorIndex n := ⟨(j, n - j), by omega⟩

/-- The map from the presentation of `N[S]^n` to `A[S] ⊗_A N` in degree `n`, sending the
summand `s · y` to `s ⊗ y` for `s` the canonical generator of `A[S]` attached to `s`. -/
noncomputable def coeffTensorPresAddHom (n : ℤ) (U : Cᵒᵖ) :
    coeffSections S N.piece n U →+
      (RelativeTensor.gradedTensor (freeGradedModule A S) N n).val.obj U :=
  _root_.DirectSum.toAddMonoid fun r =>
    ((RelativeTensor.tmulBalanced (freeGradedModule A S) N n).app (freeGenIndex n r.1)).app U
      (freeGeneratorSection A S r.1 U r.2.1 r.2.2)

/-- `SheafOfModules.coeffTensorPresAddHom` sends the summand `s · y` to `s ⊗ y`, for `s` the
canonical generator of `A[S]` attached to `s`. -/
@[simp] theorem coeffTensorPresAddHom_coeffOf (n : ℤ) (U : Cᵒᵖ) (j : ℤ)
    (s : S.sheaf.obj.obj U) (hs : S.HasDegree U s j) (y : (N.piece (n - j)).val.obj U) :
    coeffTensorPresAddHom A S N n U (coeffOf S N.piece n U j s hs y) =
      RelativeTensor.tmul (freeGradedModule A S) N n (freeGenIndex n j) U
        (freeGeneratorSection A S j U s hs) y :=
  _root_.DirectSum.toAddMonoid_of _ _ _

/-- `SheafOfModules.coeffTensorPresAddHom` is linear over `O`. -/
theorem coeffTensorPresAddHom_smul (n : ℤ) (U : Cᵒᵖ) (r : (toRingCat J Osharp).obj.obj U)
    (ξ : coeffSections S N.piece n U) :
    coeffTensorPresAddHom A S N n U (r • ξ) = r • coeffTensorPresAddHom A S N n U ξ := by
  induction ξ using coeffSections_induction with
  | hzero => rw [smul_zero, map_zero, smul_zero]
  | hof j s hs y =>
    rw [← coeffOf_smul, coeffTensorPresAddHom_coeffOf, coeffTensorPresAddHom_coeffOf]
    exact ((RelativeTensor.tmulBalanced (freeGradedModule A S) N n).app
      (freeGenIndex n j)).map_smul_right U r _ y
  | hadd ξ ξ' hξ hξ' => rw [smul_add, map_add, map_add, hξ, hξ', smul_add]

/-- `SheafOfModules.coeffTensorPresAddHom` commutes with restriction of sections. -/
theorem coeffTensorPresAddHom_naturality (n : ℤ) {U V : Cᵒᵖ} (f : U ⟶ V)
    (ξ : coeffSections S N.piece n U) :
    sectionRestrict (RelativeTensor.gradedTensor (freeGradedModule A S) N n).val f
        (coeffTensorPresAddHom A S N n U ξ) =
      coeffTensorPresAddHom A S N n V (coeffRestrict S N.piece n f ξ) := by
  induction ξ using coeffSections_induction with
  | hzero => rw [map_zero, map_zero, map_zero, map_zero]
  | hof j s hs y =>
    rw [coeffTensorPresAddHom_coeffOf, coeffRestrict_coeffOf, coeffTensorPresAddHom_coeffOf]
    refine (((RelativeTensor.tmulBalanced (freeGradedModule A S) N n).app
      (freeGenIndex n j)).naturality f _ y).trans ?_
    exact congrArg (fun z => RelativeTensor.tmul (freeGradedModule A S) N n (freeGenIndex n j)
        V z (sectionRestrict (N.piece (n - j)).val f y))
      ((freeGenerator A S).sectionRestrict_app j f s hs (S.hasDegree_map f hs))
  | hadd ξ ξ' hξ hξ' => rw [map_add, map_add, map_add, map_add, hξ, hξ']

/-- The map from the presentation of `N[S]^n` to degree `n` of `A[S] ⊗_A N`, as a morphism of
presheaves of modules. -/
noncomputable def coeffTensorPres (n : ℤ) :
    coeffPres S N.piece n ⟶ (RelativeTensor.gradedTensor (freeGradedModule A S) N n).val :=
  PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom (coeffTensorPresAddHom A S N n U)
      naturality := fun {_ _} f => by
        ext ξ; exact (coeffTensorPresAddHom_naturality A S N n f ξ).symm }
    fun U r ξ => coeffTensorPresAddHom_smul A S N n U r ξ

/-- The components of `SheafOfModules.coeffTensorPres` are
`SheafOfModules.coeffTensorPresAddHom`. -/
@[simp] theorem coeffTensorPres_app (n : ℤ) (U : Cᵒᵖ) (ξ : coeffSections S N.piece n U) :
    (coeffTensorPres A S N n).app U ξ = coeffTensorPresAddHom A S N n U ξ := rfl

/-- **The inverse identification `N[S] = A[S] ⊗_A N`, in degree `n`.** -/
noncomputable def coeffTensorFree (n : ℤ) :
    coeffPiece S N.piece n ⟶ RelativeTensor.gradedTensor (freeGradedModule A S) N n :=
  (Adjunction.homEquiv (PresheafOfModules.sheafificationAdjunction
    (𝟙 (toRingCat J Osharp).obj)) (coeffPres S N.piece n)
      (RelativeTensor.gradedTensor (freeGradedModule A S) N n)).symm (coeffTensorPres A S N n)

/-- On the image of a section `ξ` of the presentation of `N[S]^n`,
`SheafOfModules.coeffTensorFree` agrees with `SheafOfModules.coeffTensorPresAddHom`. -/
@[simp] theorem coeffTensorFree_coeffUnit (n : ℤ) (U : Cᵒᵖ)
    (ξ : (coeffPres S N.piece n).obj U) :
    (coeffTensorFree A S N n).val.app U ((coeffUnit S N.piece n).app U ξ) =
      coeffTensorPresAddHom A S N n U ξ :=
  (PresheafOfModules.hom_congr_apply
    (PresheafOfModules.sheafificationAdjunction_unit_comp_homEquiv_symm
      (𝟙 (toRingCat J Osharp).obj)
      (N := RelativeTensor.gradedTensor (freeGradedModule A S) N n)
      (coeffTensorPres A S N n)) U ξ).trans rfl

/-- **Every summand of the presentation of `A[S]^p`, tensored with a coefficient, is a canonical
generator tensored with the product of the two coefficients.** -/
theorem tmul_freeUnit_freeOf (p q n j : ℤ) (h : p + q = n) (U : Cᵒᵖ) (s : S.sheaf.obj.obj U)
    (hs : S.HasDegree U s j) (b : (A.piece (p - j)).val.obj U)
    (y : (N.piece q).val.obj U) :
    RelativeTensor.tmul (freeGradedModule A S) N n ⟨(p, q), h⟩ U
        ((freeUnit A S p).app U (freeOf A S p U j s hs b)) y =
      RelativeTensor.tmul (freeGradedModule A S) N n (freeGenIndex n j) U
        (freeGeneratorSection A S j U s hs)
        (castHom N.piece (freeTensorDeg h j) U (N.smul (p - j) q U b y)) := by
  have hh : j + (p - j) = p := by omega
  have h₁ : j + (p - j) + q = n := by omega
  have h₂ : j + ((p - j) + q) = n := by omega
  have hb : RelativeTensor.tmul (freeGradedModule A S) N n ⟨(j + (p - j), q), h₁⟩ U
        ((freeActBilin A S j (p - j)).app U (freeGeneratorSection A S j U s hs) b) y =
      RelativeTensor.tmul (freeGradedModule A S) N n ⟨(j, (p - j) + q), h₂⟩ U
        (freeGeneratorSection A S j U s hs) (N.smul (p - j) q U b y) :=
    (RelativeTensor.tmulBalanced (freeGradedModule A S) N n).balanced
      ⟨(j, p - j, q), h₁⟩ U (freeGeneratorSection A S j U s hs) b y
  refine Eq.trans (congrArg (fun z => RelativeTensor.tmul (freeGradedModule A S) N n
    ⟨(p, q), h⟩ U z y) (freeUnit_freeOf A S p j U s hs b hh).symm) ?_
  refine Eq.trans (RelativeTensor.tmul_castHom_left (freeGradedModule A S) N n
    (j + (p - j)) p q h₁ h hh U _ y) ?_
  exact hb.trans (RelativeTensor.tmul_castHom_right (freeGradedModule A S) N n j
    ((p - j) + q) (n - j) h₂ (freeGenIndex n j).2 (freeTensorDeg h j) U _ _).symm

/-- The map to the sheafification kills the zero section of the presentation of `A[S]^n`. -/
theorem freeUnit_zero (p : ℤ) (U : Cᵒᵖ) :
    (freeUnit A S p).app U (0 : freeSections A S p U) = 0 :=
  map_zero ((freeUnit A S p).app U).hom

/-- The map to the sheafification kills the zero section of the presentation of `N[S]^n`. -/
theorem coeffUnit_zero (n : ℤ) (U : Cᵒᵖ) :
    (coeffUnit S N.piece n).app U (0 : coeffSections S N.piece n U) = 0 :=
  map_zero ((coeffUnit S N.piece n).app U).hom

/-- The map to the sheafification of the presentation of `N[S]^n` is additive, with its source
written as a direct sum. -/
theorem coeffUnit_add (n : ℤ) (U : Cᵒᵖ) (ξ ξ' : coeffSections S N.piece n U) :
    (coeffUnit S N.piece n).app U (ξ + ξ') =
      (coeffUnit S N.piece n).app U ξ + (coeffUnit S N.piece n).app U ξ' :=
  map_add ((coeffUnit S N.piece n).app U).hom ξ ξ'

/-- **The coefficients of a canonical generator tensored with a section of `N`**: the generator
of degree `j` contributes the summand of `s`, with the unit of `A` acting on the coefficient. -/
theorem freeTensorCoeffBilin_generator (q n j : ℤ) (h : j + q = n) (U : Cᵒᵖ)
    (s : S.sheaf.obj.obj U) (hs : S.HasDegree U s j) (y : (N.piece q).val.obj U) :
    (freeTensorCoeffBilin A S N j q n h).app U (freeGeneratorSection A S j U s hs) y =
      (coeffUnit S N.piece n).app U (coeffOf S N.piece n U j s hs
        (castHom N.piece (freeTensorDeg h j) U
          (N.smul (j - j) q U (castHom A.piece (sub_self j).symm U (A.one.eval U)) y))) :=
  (freeTensorCoeffBilin_unit A S N j q n h U
      (freeOf A S j U j s hs (castHom A.piece (sub_self j).symm U (A.one.eval U))) y).trans
    (congrArg ((coeffUnit S N.piece n).app U)
      (freeTensorCoeffPres_freeOf A S N j q n h U y j s hs _))

/-- The two presentation-level maps are mutually inverse: the coefficients of `ζ ⊗ y` reassemble
to `ζ ⊗ y`. -/
theorem coeffTensorPresAddHom_freeTensorCoeffPres (p q n : ℤ) (h : p + q = n) (U : Cᵒᵖ)
    (y : (N.piece q).val.obj U) (ζ : freeSections A S p U) :
    coeffTensorPresAddHom A S N n U (freeTensorCoeffPres A S N p q n h U y ζ) =
      RelativeTensor.tmul (freeGradedModule A S) N n ⟨(p, q), h⟩ U
        ((freeUnit A S p).app U ζ) y := by
  refine DFunLike.congr_fun (freeSections_addHom_ext A S
    (φ := (coeffTensorPresAddHom A S N n U).comp (freeTensorCoeffPres A S N p q n h U y))
    (ψ := ((((RelativeTensor.tmulBalanced (freeGradedModule A S) N n).app ⟨(p, q), h⟩).app U).flip
      y).comp ((freeUnit A S p).app U).hom.toAddMonoidHom) fun j s hs b => ?_) ζ
  refine Eq.trans (congrArg (coeffTensorPresAddHom A S N n U)
    (freeTensorCoeffPres_freeOf A S N p q n h U y j s hs b)) ?_
  refine (coeffTensorPresAddHom_coeffOf A S N n U j s hs _).trans ?_
  exact (tmul_freeUnit_freeOf A S N p q n j h U s hs b y).symm

/-- The reassembly of the presentation of `N[S]^n` inside `A[S] ⊗_A N` has the coefficients it
started from. -/
theorem freeTensorCoeff_coeffTensorPresAddHom (n : ℤ) (U : Cᵒᵖ)
    (ξ : coeffSections S N.piece n U) :
    (freeTensorCoeff A S N n).val.app U (coeffTensorPresAddHom A S N n U ξ) =
      (coeffUnit S N.piece n).app U ξ := by
  refine DFunLike.congr_fun (coeffSections_addHom_ext S N.piece
    (φ := ((freeTensorCoeff A S N n).val.app U).hom.toAddMonoidHom.comp
      (coeffTensorPresAddHom A S N n U))
    (ψ := ((coeffUnit S N.piece n).app U).hom.toAddMonoidHom) fun j s hs y => ?_) ξ
  refine Eq.trans (congrArg ((freeTensorCoeff A S N n).val.app U)
    (coeffTensorPresAddHom_coeffOf A S N n U j s hs y)) ?_
  refine (freeTensorCoeff_tmul A S N n (freeGenIndex n j) U
    (freeGeneratorSection A S j U s hs) y).trans ?_
  have hjn : j + (n - j) = n := by omega
  refine (freeTensorCoeffBilin_generator A S N (n - j) n j hjn U s hs y).trans ?_
  refine congrArg ((coeffUnit S N.piece n).app U) ?_
  refine coeffOf_congr S N.piece n U j hs hs rfl ?_
  refine (N.smul_castHom_alg (sub_self j).symm
    (freeTensorDeg hjn j) (by omega) U (A.one.eval U) y).trans ?_
  exact eq_of_heq ((heq_castHom N.piece (by omega) U _).trans (N.one_smul (n - j) U y))

/-- Degree `n` of the relative tensor product `A[S] ⊗_A N` of the free graded `A`-module on a
sheaf of graded sets `S` with a left graded `A`-module `N` is the free graded module on `S` with
coefficients in `N`. -/
noncomputable def freeTensorCoeffIso (n : ℤ) :
    RelativeTensor.gradedTensor (freeGradedModule A S) N n ≅ coeffPiece S N.piece n where
  hom := freeTensorCoeff A S N n
  inv := coeffTensorFree A S N n
  hom_inv_id := by
    refine RelativeTensor.gradedTensor_hom_ext (freeGradedModule A S) N fun p U x y => ?_
    refine Stacks.eq_of_forall_lift
      (RelativeTensor.gradedTensor (freeGradedModule A S) N n).isSheaf.isSeparated
      (freeUnit A S p.1.1) x _ _ ?_
    intro Y f ζ hζ
    refine Eq.trans (congrArg
      ((RelativeTensor.gradedTensor (freeGradedModule A S) N n).val.map f)
      (congrArg ((coeffTensorFree A S N n).val.app U)
        (freeTensorCoeff_tmul A S N n p U x y))) ?_
    refine Eq.trans (PresheafOfModules.naturality_apply
      (coeffTensorFree A S N n).val f _).symm ?_
    refine Eq.trans (congrArg ((coeffTensorFree A S N n).val.app Y)
      (freeTensorCoeffBilin_lift A S N p.1.1 p.1.2 n p.2 U x y f ζ hζ)) ?_
    refine (coeffTensorFree_coeffUnit A S N n Y _).trans ?_
    refine (coeffTensorPresAddHom_freeTensorCoeffPres A S N p.1.1 p.1.2 n p.2 Y
      (sectionRestrict (N.piece p.1.2).val f y) ζ).trans ?_
    refine Eq.trans (congrArg (fun z => RelativeTensor.tmul (freeGradedModule A S) N n p Y z
      (sectionRestrict (N.piece p.1.2).val f y)) hζ) ?_
    exact (((RelativeTensor.tmulBalanced (freeGradedModule A S) N n).app p).naturality f x y).symm
  inv_hom_id := by
    refine coeffPiece_hom_ext S fun U ξ => ?_
    exact (congrArg ((freeTensorCoeff A S N n).val.app U)
      (coeffTensorFree_coeffUnit A S N n U ξ)).trans
        (freeTensorCoeff_coeffTensorPresAddHom A S N n U ξ)

/-- The forward map of `SheafOfModules.freeTensorCoeffIso` is `SheafOfModules.freeTensorCoeff`. -/
@[simp] theorem freeTensorCoeffIso_hom (n : ℤ) :
    (freeTensorCoeffIso A S N n).hom = freeTensorCoeff A S N n := rfl

/-- The inverse map of `SheafOfModules.freeTensorCoeffIso` is `SheafOfModules.coeffTensorFree`. -/
@[simp] theorem freeTensorCoeffIso_inv (n : ℤ) :
    (freeTensorCoeffIso A S N n).inv = coeffTensorFree A S N n := rfl

end Sheafify

section SheafifyNaturality

variable [HasWeakSheafify J (Type m)] [HasWeakSheafify J AddCommGrpCat.{m}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
  (A : GradedAlgebra.{t, m} (toRingCat J Osharp)) (S : SheafOfGradedSets.{m} J)
  {N N' : LeftGradedModule.{t, m, m} A} (f : N ⟶ N')

/-- Sheafification is compatible with the maps of presentations of `N[S]`: the morphism of
pieces induced by a morphism of the coefficients restricts to the morphism of presentations. -/
theorem coeffPieceMap_coeffUnit (n : ℤ) (U : Cᵒᵖ) (ξ : (coeffPres S N.piece n).obj U) :
    (coeffPieceMap S (fun k => f.app k) n).val.app U ((coeffUnit S N.piece n).app U ξ) =
      (coeffUnit S N'.piece n).app U ((coeffPresMap S (fun k => f.app k) n).app U ξ) :=
  PresheafOfModules.unit_naturality_apply (α := 𝟙 (toRingCat J Osharp).obj)
    (φ := coeffPresMap S (fun k => f.app k) n) U ξ

/-- The coefficient map `A[S]^p × N^q → N[S]^n` is natural in the left graded module `N`. -/
theorem coeffPieceMap_freeTensorCoeffBilin (p q n : ℤ) (h : p + q = n) (U : Cᵒᵖ)
    (x : (freePiece A S p).val.obj U) (y : (N.piece q).val.obj U) :
    (coeffPieceMap S (fun k => f.app k) n).val.app U
        ((freeTensorCoeffBilin A S N p q n h).app U x y) =
      (freeTensorCoeffBilin A S N' p q n h).app U x ((f.app q).val.app U y) := by
  refine Stacks.eq_of_forall_lift (coeffPiece S N'.piece n).isSheaf.isSeparated
    (freeUnit A S p) x _ _ ?_
  intro Y g ζ hζ
  refine Eq.trans (PresheafOfModules.naturality_apply
    (coeffPieceMap S (fun k => f.app k) n).val g _).symm ?_
  refine Eq.trans (congrArg ((coeffPieceMap S (fun k => f.app k) n).val.app Y)
    (freeTensorCoeffBilin_lift A S N p q n h U x y g ζ hζ)) ?_
  refine (coeffPieceMap_coeffUnit A S f n Y _).trans ?_
  refine Eq.trans (congrArg ((coeffUnit S N'.piece n).app Y)
    (coeffPresAddHom_freeTensorCoeffPres A S f p q n h Y
      (sectionRestrict (N.piece q).val g y) ζ)) ?_
  refine Eq.trans ?_ (freeTensorCoeffBilin_lift A S N' p q n h U x
    ((f.app q).val.app U y) g ζ hζ).symm
  exact congrArg (fun z => (coeffUnit S N'.piece n).app Y
      (freeTensorCoeffPres A S N' p q n h Y z ζ))
    (PresheafOfModules.naturality_apply (f.app q).val g y)

/-- **The identification `A[S] ⊗_A N = N[S]` is natural in the left graded `A`-module `N`**:
it carries the functoriality of the relative tensor product to the functoriality of the
coefficients. -/
theorem freeTensorCoeff_naturality (n : ℤ) :
    RelativeTensor.gradedTensorMap (freeGradedModule A S) f n ≫
        (freeTensorCoeffIso A S N' n).hom =
      (freeTensorCoeffIso A S N n).hom ≫ coeffPieceMap S (fun k => f.app k) n := by
  refine RelativeTensor.gradedTensor_hom_ext (freeGradedModule A S) N fun p U x y => ?_
  refine Eq.trans (congrArg ((freeTensorCoeff A S N' n).val.app U)
    (RelativeTensor.gradedTensorMap_tmul (freeGradedModule A S) f n p U x y)) ?_
  refine (freeTensorCoeff_tmul A S N' n p U x ((f.app p.1.2).val.app U y)).trans ?_
  refine (coeffPieceMap_freeTensorCoeffBilin A S f p.1.1 p.1.2 n p.2 U x y).symm.trans ?_
  exact congrArg ((coeffPieceMap S (fun k => f.app k) n).val.app U)
    (freeTensorCoeff_tmul A S N n p U x y).symm

end SheafifyNaturality

end SheafOfModules
