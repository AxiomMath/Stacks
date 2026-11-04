module

public import Mathlib.Algebra.Category.ModuleCat.Products
public import StacksFrontier.Algebra.Homology.TotalComplexQuasiIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.Bifunctor
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.StrictlyPerfectHomFiniteFree
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.StrictlyPerfectHomQuasiIso
public import StacksFrontier.CategoryTheory.Limits.SigmaSupport
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplex
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftFiniteColimits
public import StacksFrontier.AlgebraicGeometry.Topologies.GlobalPresentationComparison
import all
  StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.HomComplexOfAStrictlyPerfectComplex
import all StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.InternalHomUnitSource

/-!
# The internal Hom complex out of a strictly perfect source, at unequal universes

Let `(C, O)` be a ringed site whose objects, morphisms and structure sheaf live in independent
universes, let `E` be a complex of `O`-modules with finitely many nonzero terms, each a direct
summand of a finite free `O`-module, and let `f : F ⟶ G` be a quasi-isomorphism of complexes of
`O`-modules.  Then the induced morphism `SheafHom(E, F) ⟶ SheafHom(E, G)` of internal Hom
complexes (Stacks 0A8Z) is a quasi-isomorphism (Stacks 08JH).

`AlgebraicGeometry.RingedSite.homMap_quasiIso_of_isFiniteFreeSummand` states this for a
`AlgebraicGeometry.RingedSite.{u, u, u}`.  The argument — the stupid filtration of `E`, down to
a single term `O` — uses the coincidence of the universes in one place only: for a source
concentrated in one degree with term `O`, the internal Hom complex is identified with the target.
At unequal universes the internal Hom complex lives in the universe `max u v w` of its sections
while the target lives in `w`, and the identification is with the universe lift of the target
(`AlgebraicGeometry.RingedSite.General.homUnitEvaluationG`).  The universe lift is exact, so it
preserves quasi-isomorphisms, and the rest of the argument goes through unchanged.  This covers
the small étale site of an algebraic space, a `AlgebraicGeometry.RingedSite.{u + 1, u, u}`.

## Main results

* `AlgebraicGeometry.RingedSite.General.homMap_quasiIso_of_isFiniteFreeSummand`: Stacks 08JH at
  unequal universes.
* `AlgebraicGeometry.RingedSite.General.IsDirectSummandOfFiniteFree.isFiniteFreeSummand`: the
  termwise condition of Stacks 08FL implies the retract condition used here.
* `AlgebraicGeometry.RingedSite.General.RetractOfLiftWith.sheafHomComplex_X`: each term of
  `SheafHom(E, F)` is a retract of the universe lift of a finite direct sum of terms of `F`, so it
  inherits any property of the terms of `F` closed under isomorphisms, finite coproducts and
  retracts.

## References

* [Stacks Project, Tag 08JH](https://stacks.math.columbia.edu/tag/08JH)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
* [Stacks Project, Tag 08FL](https://stacks.math.columbia.edu/tag/08FL)
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CochainComplex.HomComplex ZeroObject

universe u v w

namespace AlgebraicGeometry.RingedSite.General

open AlgebraicGeometry.RingedSite

section HomComplexOfAStrictlyPerfectComplex

variable (X : RingedSite.{u, v, w})
  [HasSheafify X.J AddCommGrpCat.{max u v w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]

/-- The projection of the `n`-th term of the internal Hom complex onto the internal Hom sheaf
from `E^{-q}` to `F^{n-q}`, read off from the identification of sections with the ordinary Hom
complex on each slice site. The two naturality clauses of `SheafHomComplex` are exactly what
make this a morphism of sheaves of modules: `smul_natural` gives semilinearity over the
sections of the structure sheaf, and `restrict_natural` gives naturality in the site. -/
@[expose] public def homDegreeProjection
    (E F : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
      (n q : ℤ) :
    (sheafHomComplex X E F).obj.X n ⟶ internalHomSheaf X (E.X (-q)) (F.X (n - q)) where
  val :=
    { app := fun U => ModuleCat.homAddEquiv.symm
        { toFun := fun s =>
            ((AddCommGrpCat.Hom.hom (((sheafHomComplex X E F).sectionsIso U.unop).hom.f n)
              s).v (-q) (n - q) (by omega)).val
          map_add' := by
            intro a b
            have hf := map_add (AddCommGrpCat.Hom.hom
              (((sheafHomComplex X E F).sectionsIso U.unop).hom.f n)) a b
            exact congrArg
              (fun c : Cochain (restrictComplex X E U.unop)
                  (restrictComplex X F U.unop) n =>
                (c.v (-q) (n - q) (by omega)).val) hf
          map_smul' := by
            intro r s
            apply PresheafOfModules.hom_ext
            intro V
            ext x
            exact (sheafHomComplex X E F).smul_natural U.unop r n (-q) (n - q)
              (by omega) s V.unop.hom x }
      naturality := by
        intro U V f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro s
        apply PresheafOfModules.hom_ext
        intro W
        ext x
        exact ((sheafHomComplex X E F).restrict_natural f.unop n (-q) (n - q)
          (by omega) s W.unop.hom x).symm }

omit [HasSheafify X.J AddCommGrpCat.{max u v w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}] in
/-- The defining property of `homDegreeProjection`: on a section over `U` it reads off the
`(-q, n - q)` component of the corresponding degree-`n` cochain of the restrictions.

Stated because the declarations of this file are `public` but not `@[expose]`, so a consumer
cannot unfold the projection; `homDegreeProjection` itself carries `@[expose]` only so that
this characterisation can be proved by `rfl`. -/
public lemma homDegreeProjection_val_app_apply
    (E F : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
      (n q : ℤ) (U : X.C)
    (s : ((sheafHomComplex X E F).obj.X n).val.obj (op U)) :
    (homDegreeProjection X E F n q).val.app (op U) s =
      ((AddCommGrpCat.Hom.hom (((sheafHomComplex X E F).sectionsIso U).hom.f n) s).v
        (-q) (n - q) (by omega)).val := rfl

/-- Sections of the internal Hom sheaf over `U` are morphisms of the restrictions to the slice
site over `U`; the two directions are the constructor and the projection of
`SheafOfModules.Hom`. -/
private def internalHomSectionAddEquiv
    (A B : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (U : X.C) :
    (internalHomSheaf X A B).val.obj (op U) ≃+ (A.over U ⟶ B.over U) where
  toFun s := ⟨s⟩
  invFun s := s.val
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- Sections over `U` of the `n`-th term of the internal Hom complex are families of sections
of the internal Hom sheaves of the terms. -/
private def homDegreeSectionEquiv
    (E F : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
      (n : ℤ) (U : X.C) :
    ((sheafHomComplex X E F).obj.X n).val.obj (op U) ≃+
      (∀ q : ℤ, (internalHomSheaf X (E.X (-q)) (F.X (n - q))).val.obj (op U)) :=
  (HomologicalComplex.Hom.isoApp
    ((sheafHomComplex X E F).sectionsIso U) n).addCommGroupIsoToAddEquiv.trans
    ((cochainFamilyEquiv (restrictComplex X E U) (restrictComplex X F U) n).trans
      (AddEquiv.piCongrRight (fun q =>
        (internalHomSectionAddEquiv X (E.X (-q)) (F.X (n - q)) U).symm)))

/-- The `n`-th term of the internal Hom complex is the product, over `q : ℤ`, of the internal
Hom sheaves from `E^{-q}` to `F^{n-q}`, with `homDegreeProjection` as the projections.

The limit is proved after reflecting along `SheafOfModules.forget` and evaluating at each
object of the site, where `homDegreeSectionEquiv` turns the claim into the corresponding
product of modules. -/
public def homDegreeIsLimit
    (E F : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
      (n : ℤ) :
    IsLimit (Fan.mk ((sheafHomComplex X E F).obj.X n)
      (homDegreeProjection X E F n)) := by
  haveI :=
    (SheafOfModules.fullyFaithfulForget.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).full
  haveI :=
    (SheafOfModules.fullyFaithfulForget.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).faithful
  apply isLimitOfReflects (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  apply PresheafOfModules.evaluationJointlyReflectsLimits
  intro U
  let A : ℤ → ModuleCat ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U) := fun q =>
    (internalHomSheaf X (E.X (-q)) (F.X (n - q))).val.obj U
  let e : ((sheafHomComplex X E F).obj.X n).val.obj U
      ≃ₗ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U] (∀ q : ℤ, A q) :=
    { __ := homDegreeSectionEquiv X E F n U.unop
      map_smul' := by
        intro r s
        funext q
        exact (homDegreeProjection X E F n q).val.app U |>.hom.map_smul r s }
  let T := SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
    PresheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj U
  refine (isLimitMapConeFanMkEquiv T _ (homDegreeProjection X E F n)).symm ?_
  refine (ModuleCat.productConeIsLimit A).ofIsoLimit ?_
  refine (Cone.ext e.toModuleIso ?_).symm
  intro q
  ext s
  rfl

omit [HasSheafify X.J AddCommGrpCat.{max u v w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}] in
/-- The internal Hom sheaf out of a zero module is zero. -/
public theorem internalHomSheaf_isZero_of_isZero
    {A B : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (hA : IsZero A) :
    IsZero (internalHomSheaf X A B) := by
  apply (IsZero.iff_id_eq_zero _).2
  ext U s
  have hz :=
    (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U.unop).map_isZero hA
  exact congrArg SheafOfModules.Hom.val
    (hz.eq_of_src (⟨s⟩ : A.over U.unop ⟶ B.over U.unop)
      ⟨(0 : (internalHomSheaf X A B).val.obj U)⟩)

omit [HasSheafify X.J AddCommGrpCat.{max u v w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}] in
/-- The summands of the degreewise direct-sum description vanish outside the negated support of
`E`: there `E^{-q}` is zero, hence so is the internal Hom sheaf out of it. -/
private theorem isZero_internalHomSheaf_notMem_negSupport
    (E F : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hE : {i : ℤ | ¬ IsZero (E.X i)}.Finite) (n q : ℤ)
    (hq : q ∉ (hE.image (fun i : ℤ => -i)).toFinset) :
    IsZero (internalHomSheaf X (E.X (-q)) (F.X (n - q))) := by
  apply internalHomSheaf_isZero_of_isZero
  by_contra h
  exact hq ((Set.Finite.mem_toFinset _).2 ⟨-q, h, neg_neg q⟩)

/-- **Stacks 08JH**, degreewise statement. For `E` bounded, the `n`-th term of the internal Hom
complex `SheafHom(E, F)` of Stacks 0A8Z is the direct sum, over `q : ℤ`, of the internal Hom
sheaves `SheafHom(E^{-q}, F^{n-q})`.

By `homDegreeIsLimit` the term is the *product* of those sheaves, with no hypothesis on `E`.
Boundedness makes `E^{-q}` vanish outside a finite set of `q`, hence each summand vanish there
by `internalHomSheaf_isZero_of_isZero`, and `productCoproductIsoOfFiniteSupport` then
identifies the product with the coproduct.

The source lemma assumes `E` strictly perfect; boundedness is the `bounded` field of that
condition and the only part used, so this is the source statement generalized. See the
implementation notes for why the strict-perfectness predicate cannot be named at these
universes.

The differential needs no separate description: that it is the standard Hom-complex
differential is part of the data of `SheafHomComplex`, whose `sectionsIso` is an isomorphism
of complexes onto `CochainComplex.HomComplex` on every slice site. -/
def strictlyPerfectHomDegreeIso
    (E F : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hE : {i : ℤ | ¬ IsZero (E.X i)}.Finite) (n : ℤ) :
    ((sheafHomComplex X E F).obj.X n) ≅
      ∐ (fun q : ℤ => internalHomSheaf X (E.X (-q)) (F.X (n - q))) :=
  ((homDegreeIsLimit X E F n).conePointUniqueUpToIso
      (limit.isLimit (Discrete.functor
        (fun q : ℤ => internalHomSheaf X (E.X (-q)) (F.X (n - q)))))).trans
    (productCoproductIsoOfFiniteSupport
      (fun q : ℤ => internalHomSheaf X (E.X (-q)) (F.X (n - q)))
      (hE.image (fun i : ℤ => -i)).toFinset
      (isZero_internalHomSheaf_notMem_negSupport X E F hE n))

/-- **A section-level handle on `strictlyPerfectHomDegreeIso`.** When all but the `q₀`-th
summand of the direct sum vanishes, the degreewise identification followed by a descent out of
the coproduct is the `q₀`-th projection `homDegreeProjection` followed by the `q₀`-th component
of the descent.

This is what makes the identification usable from outside this file: the identification itself
is a composite of a limit comparison and `productCoproductIsoOfFiniteSupport`, neither of which
a consumer can unfold, whereas `homDegreeProjection` is characterised on sections by
`homDegreeProjection_val_app_apply` and is natural in the source by
`homDegreeProjection_homMap`.

The two factors are treated separately. `productCoproductIsoOfFiniteSupport` is the sum, over
the finite support, of the projections followed by the coproduct injections, so the composite
with the descent is the sum of the projections followed by the components; every term other
than the one at `q₀` has a zero source by `hvan`, and the term at `q₀` survives — or has a zero
source as well, if `q₀` is outside the support, in which case both sides vanish. The limit
comparison composed with a projection is `homDegreeProjection` by the defining property of
`homDegreeIsLimit`. -/
public lemma strictlyPerfectHomDegreeIso_hom_comp_desc
    (E F : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hE : {i : ℤ | ¬ IsZero (E.X i)}.Finite) (n q₀ : ℤ)
    (hvan : ∀ q : ℤ, q ≠ q₀ → IsZero (internalHomSheaf X (E.X (-q)) (F.X (n - q))))
    {T : SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (g : ∀ q : ℤ, internalHomSheaf X (E.X (-q)) (F.X (n - q)) ⟶ T) :
    (strictlyPerfectHomDegreeIso X E F hE n).hom ≫ Sigma.desc g =
      homDegreeProjection X E F n q₀ ≫ g q₀ := by
  have hsum : (productCoproductIsoOfFiniteSupport
        (fun q : ℤ => internalHomSheaf X (E.X (-q)) (F.X (n - q)))
        (hE.image (fun i : ℤ => -i)).toFinset
        (isZero_internalHomSheaf_notMem_negSupport X E F hE n)).hom ≫ Sigma.desc g =
      ∑ i ∈ (hE.image (fun i : ℤ => -i)).toFinset,
        Pi.π (fun q : ℤ => internalHomSheaf X (E.X (-q)) (F.X (n - q))) i ≫ g i := by
    show (∑ i ∈ (hE.image (fun i : ℤ => -i)).toFinset,
        Pi.π (fun q : ℤ => internalHomSheaf X (E.X (-q)) (F.X (n - q))) i ≫
          Sigma.ι (fun q : ℤ => internalHomSheaf X (E.X (-q)) (F.X (n - q))) i) ≫
      Sigma.desc g = _
    simp only [Preadditive.sum_comp, Category.assoc, Sigma.ι_desc]
  unfold strictlyPerfectHomDegreeIso
  rw [Iso.trans_hom, Category.assoc, hsum, Preadditive.comp_sum]
  have hterm : ∀ i : ℤ,
      ((homDegreeIsLimit X E F n).conePointUniqueUpToIso
          (limit.isLimit (Discrete.functor
            (fun q : ℤ => internalHomSheaf X (E.X (-q)) (F.X (n - q)))))).hom ≫
        Pi.π (fun q : ℤ => internalHomSheaf X (E.X (-q)) (F.X (n - q))) i ≫ g i =
      homDegreeProjection X E F n i ≫ g i := fun i =>
    (Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ g i) ((homDegreeIsLimit X E F n).conePointUniqueUpToIso_hom_comp
        (limit.isLimit (Discrete.functor
          (fun q : ℤ => internalHomSheaf X (E.X (-q)) (F.X (n - q))))) ⟨i⟩))
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  refine Finset.sum_eq_single q₀ (fun i _ hi => ?_) (fun hq₀ => ?_)
  · rw [(hvan i hi).eq_of_tgt (homDegreeProjection X E F n i) 0, zero_comp]
  · rw [(isZero_internalHomSheaf_notMem_negSupport X E F hE n q₀ hq₀).eq_of_tgt
      (homDegreeProjection X E F n q₀) 0, zero_comp]


end HomComplexOfAStrictlyPerfectComplex

end AlgebraicGeometry.RingedSite.General

end

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CochainComplex.HomComplex ZeroObject

universe u v w

namespace AlgebraicGeometry.RingedSite.General

open AlgebraicGeometry.RingedSite

section InternalHomTermwiseSplit

variable (X : RingedSite.{u, v, w})
  [HasSheafify X.J AddCommGrpCat.{max u v w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]


section Pre

omit [HasSheafify X.J AddCommGrpCat.{max u v w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}] in
/-- Precomposition with the identity is the identity on internal Hom sheaves. -/
lemma internalHomPreG_id {A C : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} :
    internalHomPre X (C := C) (𝟙 A) = 𝟙 (internalHomSheaf X A C) := by
  ext U a
  rfl

omit [HasSheafify X.J AddCommGrpCat.{max u v w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}] in
/-- Precomposition on internal Hom sheaves is contravariantly functorial. -/
lemma internalHomPreG_comp
    {A B C D : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (f : A ⟶ B) (g : B ⟶ C) :
    internalHomPre X (C := D) g ≫ internalHomPre X (C := D) f =
      internalHomPre X (C := D) (f ≫ g) := by
  ext U a
  rfl

omit [HasSheafify X.J AddCommGrpCat.{max u v w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}] in
/-- Restriction to a slice of the site is additive on the underlying presheaves of modules. -/
private lemma restrFunG_map_add
    {A B : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (f g : A ⟶ B) (U : X.C) :
    (restrFun X.O.obj U).map (homOf X (f + g)) =
      (restrFun X.O.obj U).map (homOf X f) + (restrFun X.O.obj U).map (homOf X g) := by
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

omit [HasSheafify X.J AddCommGrpCat.{max u v w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}] in
/-- Restriction to a slice of the site sends the zero morphism to zero. -/
private lemma restrFunG_map_zero
    {A B : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (U : X.C) : (restrFun X.O.obj U).map (homOf X (0 : A ⟶ B)) = 0 := by
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

omit [HasSheafify X.J AddCommGrpCat.{max u v w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}] in
/-- Precomposition on internal Hom sheaves is additive in the morphism. -/
lemma internalHomPreG_add {A B C : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (f g : A ⟶ B) :
    internalHomPre X (C := C) (f + g) =
      internalHomPre X (C := C) f + internalHomPre X (C := C) g := by
  ext U a
  show (restrFun X.O.obj (unop U)).map (homOf X (f + g)) ≫
      (a : (restrFun X.O.obj (unop U)).obj (valOf X B) ⟶
        (restrFun X.O.obj (unop U)).obj (valOf X C)) =
    (restrFun X.O.obj (unop U)).map (homOf X f) ≫
      (a : (restrFun X.O.obj (unop U)).obj (valOf X B) ⟶
        (restrFun X.O.obj (unop U)).obj (valOf X C)) +
    (restrFun X.O.obj (unop U)).map (homOf X g) ≫
      (a : (restrFun X.O.obj (unop U)).obj (valOf X B) ⟶
        (restrFun X.O.obj (unop U)).obj (valOf X C))
  rw [restrFunG_map_add]
  exact Preadditive.add_comp _ _ _ _ _ _

omit [HasSheafify X.J AddCommGrpCat.{max u v w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}] in
/-- Precomposition with the zero morphism is zero. -/
lemma internalHomPreG_zero
    {A B C : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} :
    internalHomPre X (C := C) (0 : A ⟶ B) = 0 := by
  ext U a
  show (restrFun X.O.obj (unop U)).map (homOf X (0 : A ⟶ B)) ≫
      (a : (restrFun X.O.obj (unop U)).obj (valOf X B) ⟶
        (restrFun X.O.obj (unop U)).obj (valOf X C)) = 0
  rw [restrFunG_map_zero]
  exact zero_comp

end Pre

omit [HasSheafify X.J AddCommGrpCat.{max u v w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}] in
/-- The degree-`n` component of `homMap k (𝟙 B)` is, in the product description of the terms of
the internal Hom complex, the product of the precompositions with the components of `k`. -/
@[reassoc]
lemma homDegreeProjection_homMap
    {E E' : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
      (k : E' ⟶ E)
    (B : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
      (n q : ℤ) :
    (homMap X k (𝟙 B)).f n ≫ homDegreeProjection X E' B n q =
      homDegreeProjection X E B n q ≫ internalHomPre X (k.f (-q)) := by
  ext U s
  rw [comp_val_app_apply, comp_val_app_apply, homDegreeProjection_val_app_apply,
    homDegreeProjection_val_app_apply]
  refine Eq.trans (congrArg SheafOfModules.Hom.val
    (sectionsIso_homMap_v X k (𝟙 B) U.unop n (-q) (n - q) (by omega) s)) ?_
  rfl

omit [HasSheafify X.J AddCommGrpCat.{max u v w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}] in
/-- Two morphisms into the degree-`n` term of an internal Hom complex agree as soon as their
composites with all the projections of `homDegreeIsLimit` agree. -/
lemma homDegree_hom_ext
    {T : SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    {E B : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
      (n : ℤ)
    (f g : T ⟶ (sheafHomComplex X E B).obj.X n)
    (h : ∀ q, f ≫ homDegreeProjection X E B n q = g ≫ homDegreeProjection X E B n q) :
    f = g :=
  Fan.IsLimit.hom_ext (homDegreeIsLimit X E B n) f g h

/-- The morphism of degree-`n` terms of internal Hom complexes induced by a family of morphisms
`E'^p ⟶ E^p` of the terms of the sources.

No compatibility with the differentials is required: the degree-`n` term of `SheafHom(E, B)` is
the product over `q` of `SheafHom(E^{-q}, B^{n-q})` by `homDegreeIsLimit`, so a family of
morphisms of the terms induces one of the products. -/
def homDegreeFamilyMap
    {E E' : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (φ : ∀ p : ℤ, E'.X p ⟶ E.X p)
    (B : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
      (n : ℤ) :
    (sheafHomComplex X E B).obj.X n ⟶ (sheafHomComplex X E' B).obj.X n :=
  Fan.IsLimit.lift (homDegreeIsLimit X E' B n)
    (fun q => homDegreeProjection X E B n q ≫ internalHomPre X (φ (-q)))

omit [HasSheafify X.J AddCommGrpCat.{max u v w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}] in
/-- The defining property of `homDegreeFamilyMap`. -/
@[reassoc]
lemma homDegreeFamilyMap_homDegreeProjection
    {E E' : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
      (φ : ∀ p : ℤ, E'.X p ⟶ E.X p)
    (B : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
      (n q : ℤ) :
    homDegreeFamilyMap X φ B n ≫ homDegreeProjection X E' B n q =
      homDegreeProjection X E B n q ≫ internalHomPre X (φ (-q)) :=
  Fan.IsLimit.fac (homDegreeIsLimit X E' B n) _ q

omit [HasSheafify X.J AddCommGrpCat.{max u v w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}] in
/-- The zero morphism of sources induces the zero morphism of internal Hom complexes. -/
lemma homMap_zero_left
    {E E' : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (B : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    homMap X (0 : E' ⟶ E) (𝟙 B) = 0 := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  rw [HomologicalComplex.zero_f]
  refine homDegree_hom_ext X n _ _ fun q => ?_
  rw [homDegreeProjection_homMap, HomologicalComplex.zero_f, internalHomPreG_zero, comp_zero,
    zero_comp]

section Split

variable (S : ShortComplex
    (CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ))
  (B : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

omit [HasSheafify X.J AddCommGrpCat.{max u v w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}] in
/-- The two induced maps of internal Hom complexes out of a short complex of sources compose to
zero. -/
lemma internalHomShortComplex_zero :
    (homMap X S.g (𝟙 B) ≫ homMap X S.f (𝟙 B) :
      (sheafHomComplex X S.X₃ B).obj ⟶ (sheafHomComplex X S.X₁ B).obj) = 0 := by
  rw [homMap_comp, S.zero, Category.comp_id, homMap_zero_left]

/-- The short complex `SheafHom(E₃, B) ⟶ SheafHom(E₂, B) ⟶ SheafHom(E₁, B)` of internal Hom
complexes obtained from a short complex `E₁ ⟶ E₂ ⟶ E₃` of sources. -/
def internalHomShortComplex :
    ShortComplex (CochainComplex
      (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :=
  ShortComplex.mk (homMap X S.g (𝟙 B)) (homMap X S.f (𝟙 B)) (internalHomShortComplex_zero X S B)

omit [HasSheafify X.J AddCommGrpCat.{max u v w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}] in
/-- A degreewise section of `S.g` induces a degreewise retraction of the induced map of
internal Hom complexes. -/
lemma homMap_g_comp_homDegreeFamilyMap
    (S : ShortComplex (CochainComplex
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ))
    (B : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
      (s : ∀ p : ℤ, S.X₃.X p ⟶ S.X₂.X p)
    (hs : ∀ p : ℤ, s p ≫ S.g.f p = 𝟙 (S.X₃.X p)) (n : ℤ) :
    (homMap X S.g (𝟙 B)).f n ≫ homDegreeFamilyMap X s B n =
      𝟙 ((sheafHomComplex X S.X₃ B).obj.X n) := by
  refine homDegree_hom_ext X n _ _ fun q => ?_
  rw [Category.assoc, homDegreeFamilyMap_homDegreeProjection, homDegreeProjection_homMap_assoc,
    internalHomPreG_comp, hs, internalHomPreG_id, Category.comp_id, Category.id_comp]

omit [HasSheafify X.J AddCommGrpCat.{max u v w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}] in
/-- A degreewise retraction of `S.f` induces a degreewise section of the induced map of
internal Hom complexes. -/
lemma homDegreeFamilyMap_comp_homMap_f
    (S : ShortComplex (CochainComplex
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ))
    (B : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
      (r : ∀ p : ℤ, S.X₂.X p ⟶ S.X₁.X p)
    (hr : ∀ p : ℤ, S.f.f p ≫ r p = 𝟙 (S.X₁.X p)) (n : ℤ) :
    homDegreeFamilyMap X r B n ≫ (homMap X S.f (𝟙 B)).f n =
      𝟙 ((sheafHomComplex X S.X₁ B).obj.X n) := by
  refine homDegree_hom_ext X n _ _ fun q => ?_
  rw [Category.assoc, homDegreeProjection_homMap, homDegreeFamilyMap_homDegreeProjection_assoc,
    internalHomPreG_comp, hr, internalHomPreG_id, Category.comp_id, Category.id_comp]

omit [HasSheafify X.J AddCommGrpCat.{max u v w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}] in
/-- The compatibility identity of a degreewise splitting is inherited by the induced maps of
internal Hom complexes. -/
lemma homDegreeFamilyMap_splitting_id
    (S : ShortComplex (CochainComplex
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ))
    (B : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
      (r : ∀ p : ℤ, S.X₂.X p ⟶ S.X₁.X p)
    (s : ∀ p : ℤ, S.X₃.X p ⟶ S.X₂.X p)
    (hid : ∀ p : ℤ, S.g.f p ≫ s p + r p ≫ S.f.f p = 𝟙 (S.X₂.X p)) (n : ℤ) :
    homDegreeFamilyMap X s B n ≫ (homMap X S.g (𝟙 B)).f n +
        (homMap X S.f (𝟙 B)).f n ≫ homDegreeFamilyMap X r B n =
      𝟙 ((sheafHomComplex X S.X₂ B).obj.X n) := by
  refine homDegree_hom_ext X n _ _ fun q => ?_
  rw [Preadditive.add_comp, Category.assoc, Category.assoc, homDegreeProjection_homMap,
    homDegreeFamilyMap_homDegreeProjection, homDegreeFamilyMap_homDegreeProjection_assoc,
    homDegreeProjection_homMap_assoc, internalHomPreG_comp, internalHomPreG_comp,
    ← Preadditive.comp_add, ← internalHomPreG_add, hid, internalHomPreG_id, Category.comp_id,
    Category.id_comp]

end Split


end InternalHomTermwiseSplit

/-- **The internal Hom complex reverses a termwise split short exact sequence of sources, and
the result is again termwise split.**

Only the degreewise splitting data of the given short complex is used, through the product
description of the terms of the internal Hom complex.

This generalizes `AlgebraicGeometry.RingedSite.internalHomTermwiseSplitting`, which is the same
splitting for a `RingedSite.{u, u, u}`: here the ringed site is a `RingedSite.{u, v, w}`, its
modules in the universe `w` and its internal Hom complexes in `max u v w`. -/
def internalHomTermwiseSplitting (X : RingedSite.{u, v, w})
    [HasSheafify X.J AddCommGrpCat.{max u v w}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    (S : ShortComplex
      (CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ))
    (B : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (σ : ∀ p : ℤ, (S.map (HomologicalComplex.eval _ _ p)).Splitting) (n : ℤ) :
    ((internalHomShortComplex X S B).map (HomologicalComplex.eval _ _ n)).Splitting where
  r := homDegreeFamilyMap X (fun p => show S.X₃.X p ⟶ S.X₂.X p from (σ p).s) B n
  s := homDegreeFamilyMap X (fun p => show S.X₂.X p ⟶ S.X₁.X p from (σ p).r) B n
  f_r := homMap_g_comp_homDegreeFamilyMap X S B _ (fun p => (σ p).s_g) n
  s_g := homDegreeFamilyMap_comp_homMap_f X S B _ (fun p => (σ p).f_r) n
  id := homDegreeFamilyMap_splitting_id X S B _ _ (fun p => by rw [add_comm]; exact (σ p).id) n

section InternalHomUnitSource

variable (X : RingedSite.{u, v, w})
  [HasSheafify X.J AddCommGrpCat.{max u v w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
/-- A morphism of `O|_U`-modules out of the restriction of the structure sheaf is determined by
the image of the unit section. -/
def unitOverHomEquiv (B : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (U : X.C) :
    ((SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U ⟶ B.over U) ≃
      B.val.obj (op U) where
  toFun φ := (φ.val.app (op (Over.mk (𝟙 U))))
    (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))
  invFun b := (B.over U).unitHomEquiv.symm
    ((B.over U).val.sectionsMk (fun V => B.val.map V.unop.hom.op b) (by
      intro V W g
      change B.val.map g.unop.left.op (B.val.map V.unop.hom.op b) = B.val.map W.unop.hom.op b
      rw [← PresheafOfModules.map_comp_apply]
      have hg : V.unop.hom.op ≫ g.unop.left.op = W.unop.hom.op :=
        congrArg Quiver.Hom.op (Over.w g.unop)
      rw [hg]))
  left_inv φ := by
    apply (B.over U).unitHomEquiv.injective
    rw [Equiv.apply_symm_apply]
    apply PresheafOfModules.sections_ext
    intro V
    have h := PresheafOfModules.naturality_apply φ.val
      (show V.unop ⟶ Over.mk (𝟙 U) from Over.homMk V.unop.hom (by simp)).op
      (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))
    change B.val.map V.unop.hom.op
      (φ.val.app (op (Over.mk (𝟙 U)))
        (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))) =
      φ.val.app V (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V.unop.left))
    change φ.val.app V
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map V.unop.hom.op
        (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))) =
      B.val.map V.unop.hom.op
        (φ.val.app (op (Over.mk (𝟙 U)))
          (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))) at h
    rw [map_one] at h
    exact h.symm
  right_inv b := by
    change ((B.over U).unitHomEquiv ((B.over U).unitHomEquiv.symm _)).val
      (op (Over.mk (𝟙 U))) = b
    rw [Equiv.apply_symm_apply]
    change B.val.map (𝟙 U).op b = b
    rw [op_id, B.val.map_id]
    rfl

variable {E F : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

/-- The universe lift of sheaves of `O`-modules into the universe of the internal Hom complex. -/
abbrev homULift :
    SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤
      SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  Stacks.SheafOfModules.moduleULift.{max u v w, w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)

/-- The universe lift `homULift` is an additive functor. -/
instance homULift_additive : (homULift X).Additive where
  map_add := by intros; rfl

/-- Evaluation of the `(k, k + n)` component of a degree-`n` section of the internal Hom
complex over `U` at the image under `e⁻¹` of the unit section, as a linear map on sections over
`U`. -/
def homUnitEvaluationLinear (k n : ℤ)
    (e : E.X k ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (U : X.Cᵒᵖ) :
    ↑(((sheafHomComplex X E F).obj.X n).val.obj U)
      →ₗ[↑((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U)] ↑((F.X (k + n)).val.obj U) where
  toFun s :=
    ((((AddCommGrpCat.Hom.hom (((sheafHomComplex X E F).sectionsIso U.unop).hom.f n)
      s).v k (k + n) rfl).val.app (op (Over.mk (𝟙 U.unop))))
        (e.inv.val.app U (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U)))
  map_add' a b :=
    congrArg
      (fun c : Cochain (restrictComplex X E U.unop) (restrictComplex X F U.unop) n =>
        (c.v k (k + n) rfl).val.app (op (Over.mk (𝟙 U.unop)))
          (e.inv.val.app U (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U)))
      (map_add (AddCommGrpCat.Hom.hom
        (((sheafHomComplex X E F).sectionsIso U.unop).hom.f n)) a b)
  map_smul' := by
    intro r s
    have h := (sheafHomComplex X E F).smul_natural U.unop r n k (k + n)
      rfl s (𝟙 U.unop)
      (e.inv.val.app U (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U))
    rw [op_id, (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map_id] at h
    exact h

/-- Evaluation of the internal Hom complex at a trivialisation of a single term of the source,
landing in the universe lift of the target.

If `E^k ≅ O`, a degree-`n` section of `SheafHom(E, F)` over `U` has a `(k, k+n)` component, a
morphism `E^k|_U ⟶ F^{k+n}|_U`, and evaluating it at the image of the unit section gives a
section of `F^{k+n}` over `U`. -/
def homUnitEvaluationG (k n : ℤ)
    (e : E.X k ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (sheafHomComplex X E F).obj.X n ⟶ (homULift X).obj (F.X (k + n)) where
  val :=
    { app := fun U => ModuleCat.ofHom
          (X := ((sheafHomComplex X E F).obj.X n).val.obj U)
          (Y := ModuleCat.of ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U)
            (ULift.{max u v w} ((F.X (k + n)).val.obj U)))
          ((ULift.moduleEquiv.{w, w, max u v w}
            (R := ↑((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U))
            (M := ↑((F.X (k + n)).val.obj U))).symm.toLinearMap.comp
              (homUnitEvaluationLinear X k n e U))
      naturality := by
        intro U V f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro s
        let g : Over.mk f.unop ⟶ Over.mk (𝟙 U.unop) := Over.homMk f.unop (by simp)
        have he : (((restrictComplex X E U.unop).X k).val.map g.op)
              (e.inv.val.app U (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U)) =
            e.inv.val.app V (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj V) := by
          have h := PresheafOfModules.naturality_apply e.inv.val f
            (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U)
          change e.inv.val.app V ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map f 1) = _ at h
          rw [map_one] at h
          exact h.symm
        have hφ := PresheafOfModules.naturality_apply
          (((AddCommGrpCat.Hom.hom (((sheafHomComplex X E F).sectionsIso U.unop).hom.f n)
            s).v k (k + n) rfl).val) g.op
          (e.inv.val.app U (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U))
        have hr := (sheafHomComplex X E F).restrict_natural f.unop n k (k + n)
          rfl s (𝟙 V.unop)
          (e.inv.val.app V (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj V))
        rw [Category.id_comp] at hr
        rw [he] at hφ
        exact congrArg ULift.up (hr.symm.trans hφ) }

omit [HasSheafify X.J AddCommGrpCat.{max u v w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}] in
/-- If `E` is concentrated in degree `k` and `E^k ≅ O`, then `homUnitEvaluationG` is an
isomorphism. -/
theorem homUnitEvaluationG_isIso (k n : ℤ)
    (e : E.X k ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hE : ∀ p, p ≠ k → IsZero (E.X p)) :
    IsIso (homUnitEvaluationG X (F := F) k n e) := by
  let t := homUnitEvaluationG X (F := F) k n e
  have ht (U : X.Cᵒᵖ) : IsIso (t.val.app U) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    let e₁ := (HomologicalComplex.Hom.isoApp
      ((sheafHomComplex X E F).sectionsIso U.unop) n).addCommGroupIsoToAddEquiv.toEquiv
    let e₂ := cochainSingleSourceEquiv (restrictComplex X E U.unop)
      (restrictComplex X F U.unop) k n
      (fun p hp => (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        U.unop).map_isZero (hE p hp))
    let e₃ := Iso.homCongr
      ((SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U.unop).mapIso e)
        (Iso.refl ((F.X (k + n)).over U.unop))
    exact (Equiv.ulift.{max u v w}.symm.bijective).comp
      ((e₁.trans e₂).trans (e₃.trans (unitOverHomEquiv X (F.X (k + n)) U.unop))).bijective
  have (U : X.Cᵒᵖ) : IsIso (t.val.app U) := ht U
  let e' := PresheafOfModules.isoMk (fun U => asIso (t.val.app U))
    (by intro U V g; exact t.val.naturality g)
  have h1 : IsIso t.val := show IsIso e'.hom from inferInstance
  have h2 : IsIso ((SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map t) := h1
  let := (SheafOfModules.fullyFaithfulForget.{max u v w}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).reflectsIsomorphisms
  exact isIso_of_reflects_iso t (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

omit [HasSheafify X.J AddCommGrpCat.{max u v w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}] in
/-- `homUnitEvaluationG` is compatible with the differentials when the differential leaving the
degree `k` term of the source vanishes. -/
theorem homUnitEvaluationG_d (k n m : ℤ) (hnm : n + 1 = m)
    (e : E.X k ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hd : E.d k (k + 1) = 0) :
    (sheafHomComplex X E F).obj.d n m ≫ homUnitEvaluationG X (F := F) k m e =
      homUnitEvaluationG X (F := F) k n e ≫ (homULift X).map (F.d (k + n) (k + m)) := by
  ext U s
  have hc : AddCommGrpCat.Hom.hom (((sheafHomComplex X E F).sectionsIso U.unop).hom.f m)
        (((sheafHomComplex X E F).obj.d n m).val.app U s) =
      CochainComplex.HomComplex.δ n m
        (AddCommGrpCat.Hom.hom (((sheafHomComplex X E F).sectionsIso U.unop).hom.f n) s) :=
    (congrArg (fun z => AddCommGrpCat.Hom.hom z s)
      (((sheafHomComplex X E F).sectionsIso U.unop).hom.comm n m)).symm
  have hdU : (restrictComplex X E U.unop).d k (k + 1) = 0 := by
    show (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U.unop).map
      (E.d k (k + 1)) = 0
    rw [hd, Functor.map_zero]
  have key : ∀ z : CochainComplex.HomComplex.Cochain (restrictComplex X E U.unop)
        (restrictComplex X F U.unop) n,
      (CochainComplex.HomComplex.δ n m z).v k (k + m) rfl =
        z.v k (k + n) rfl ≫ (restrictComplex X F U.unop).d (k + n) (k + m) := by
    intro z
    rw [CochainComplex.HomComplex.δ_v n m hnm z k (k + m) rfl (k + n) (k + 1) (by omega) rfl,
      hdU, zero_comp, smul_zero, add_zero]
  apply ULift.ext
  show (((AddCommGrpCat.Hom.hom (((sheafHomComplex X E F).sectionsIso U.unop).hom.f m)
      (((sheafHomComplex X E F).obj.d n m).val.app U s)).v k (k + m) rfl).val.app
        (op (Over.mk (𝟙 U.unop)))) (e.inv.val.app U
          (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U)) =
    (F.d (k + n) (k + m)).val.app U ((((AddCommGrpCat.Hom.hom
      (((sheafHomComplex X E F).sectionsIso U.unop).hom.f n) s).v k (k + n) rfl).val.app
        (op (Over.mk (𝟙 U.unop)))) (e.inv.val.app U
          (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U)))
  refine Eq.trans (congrArg
    (fun z : CochainComplex.HomComplex.Cochain (restrictComplex X E U.unop)
        (restrictComplex X F U.unop) m =>
      (z.v k (k + m) rfl).val.app (op (Over.mk (𝟙 U.unop)))
        (e.inv.val.app U (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U))) hc) ?_
  refine Eq.trans (congrArg
    (fun φ : (restrictComplex X E U.unop).X k ⟶ (restrictComplex X F U.unop).X (k + m) =>
      φ.val.app (op (Over.mk (𝟙 U.unop)))
        (e.inv.val.app U (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U)))
    (key (AddCommGrpCat.Hom.hom
      (((sheafHomComplex X E F).sectionsIso U.unop).hom.f n) s))) ?_
  rfl

omit [HasSheafify X.J AddCommGrpCat.{max u v w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}] in
/-- `homUnitEvaluationG` is natural in the target complex. -/
theorem homUnitEvaluationG_naturality
    {G : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (f : F ⟶ G) (k n : ℤ)
    (e : E.X k ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (homMap X (𝟙 E) f).f n ≫ homUnitEvaluationG X (F := G) k n e =
      homUnitEvaluationG X (F := F) k n e ≫ (homULift X).map (f.f (k + n)) := by
  ext U s
  have h := sectionsIso_homMap_v X (𝟙 E) f U.unop n k (k + n) rfl s
  apply ULift.ext
  show (((AddCommGrpCat.Hom.hom
    (((sheafHomComplex X E G).sectionsIso U.unop).hom.f n)
      (((homMap X (𝟙 E) f).f n).val.app U s)).v k (k + n) rfl).val.app
        (op (Over.mk (𝟙 U.unop))))
          (e.inv.val.app U (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U)) = _
  rw [h]
  rfl

/-- The evaluation isomorphism `SheafHom(E, F)^n ≅ F^{k+n}`, lifted, for a source concentrated
in degree `k` with `E^k ≅ O`. -/
def homUnitEvaluationGIso (k n : ℤ)
    (e : E.X k ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hE : ∀ p, p ≠ k → IsZero (E.X p)) :
    (sheafHomComplex X E F).obj.X n ≅ (homULift X).obj (F.X (k + n)) :=
  @asIso _ _ _ _ (homUnitEvaluationG X (F := F) k n e) (homUnitEvaluationG_isIso X k n e hE)

/-- The three-term truncations of the internal Hom complex out of a source concentrated in
degree `k` with `E^k ≅ O` are isomorphic to those of the universe lift of the target, shifted
by `k`. -/
def homUnitShortComplexGIso (k i n j : ℤ) (hi : i + 1 = n) (hj : n + 1 = j)
    (e : E.X k ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hd : E.d k (k + 1) = 0) (hE : ∀ p, p ≠ k → IsZero (E.X p)) :
    ((sheafHomComplex X E F).obj.sc' i n j) ≅
      (((homULift X).mapHomologicalComplex (ComplexShape.up ℤ)).obj F).sc'
        (k + i) (k + n) (k + j) :=
  ShortComplex.isoMk (homUnitEvaluationGIso X k i e hE) (homUnitEvaluationGIso X k n e hE)
    (homUnitEvaluationGIso X k j e hE)
    (homUnitEvaluationG_d X k i n hi e hd).symm
    (homUnitEvaluationG_d X k n j hj e hd).symm

variable [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **The single-term unit case.** If `E` is concentrated in degree `k` with `E^k ≅ O`, then the
internal Hom complex out of `E` carries a quasi-isomorphism of targets to a
quasi-isomorphism. -/
theorem homMap_quasiIso_of_unitG
    {G : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (f : F ⟶ G) [QuasiIso f] (k : ℤ)
    (e : E.X k ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hd : E.d k (k + 1) = 0) (hE : ∀ p, p ≠ k → IsZero (E.X p)) :
    QuasiIso (homMap X (𝟙 E) f) := by
  have : PreservesFiniteLimits (homULift X) :=
    Stacks.SheafOfModules.preservesFiniteLimits_moduleULift
      (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  have : PreservesFiniteColimits (homULift X) :=
    Stacks.SheafOfModules.preservesFiniteColimits_moduleULift.{max u v w, w}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  have hUf : QuasiIso (((homULift X).mapHomologicalComplex (ComplexShape.up ℤ)).map f) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology f (homULift X)
  constructor
  intro n
  rw [quasiIsoAt_iff' _ (n - 1) n (n + 1) (by simp) (by simp)]
  let eF := homUnitShortComplexGIso X (F := F) k (n - 1) n (n + 1) (by omega) rfl e hd hE
  let eG := homUnitShortComplexGIso X (F := G) k (n - 1) n (n + 1) (by omega) rfl e hd hE
  have hf0 := hUf.quasiIsoAt (k + n)
  have hf : ShortComplex.QuasiIso
      ((HomologicalComplex.shortComplexFunctor' _ _ (k + (n - 1)) (k + n)
        (k + (n + 1))).map (((homULift X).mapHomologicalComplex (ComplexShape.up ℤ)).map f)) :=
    (quasiIsoAt_iff' _ (k + (n - 1)) (k + n) (k + (n + 1))
      (by simp; omega) (by simp; omega)).1 hf0
  refine (ShortComplex.quasiIso_iff_of_arrow_mk_iso _ _ (Arrow.isoMk eF eG ?_)).2 hf
  apply ShortComplex.hom_ext
  · exact (homUnitEvaluationG_naturality X f k (n - 1) e).symm
  · exact (homUnitEvaluationG_naturality X f k n e).symm
  · exact (homUnitEvaluationG_naturality X f k (n + 1) e).symm


end InternalHomUnitSource

section StrictlyPerfectHomQuasiIso

variable (X : RingedSite.{u, v, w})
  [HasSheafify X.J AddCommGrpCat.{max u v w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {F G : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
/-- The internal Hom complexes out of a varying source, with the map induced by a fixed
morphism `f` of targets, as a functor to the arrow category. -/
def homArrowFunctor (f : F ⟶ G) :
    (CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)ᵒᵖ ⥤
      Arrow (CochainComplex
        (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) where
  obj E := Arrow.mk (homMap X (𝟙 E.unop) f)
  map g := Arrow.homMk (homMap X g.unop (𝟙 F)) (homMap X g.unop (𝟙 G)) (by
    dsimp
    rw [homMap_comp, homMap_comp, Category.id_comp, Category.comp_id, Category.id_comp,
      Category.comp_id])
  map_id E := by
    apply Arrow.hom_ext <;> exact homMap_id X _ _
  map_comp g h := by
    apply Arrow.hom_ext <;>
      simp only [Arrow.homMk_left, Arrow.homMk_right, Arrow.comp_left, Arrow.comp_right,
        homMap_comp, Category.comp_id, unop_comp]

omit [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The induced map of internal Hom complexes passes to retracts of the source. -/
theorem homMap_quasiIso_of_retract
    {E E' : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (ρ : Retract E E') (f : F ⟶ G) [QuasiIso (homMap X (𝟙 E') f)] :
    QuasiIso (homMap X (𝟙 E) f) :=
  quasiIso_of_retractArrow (ρ.op.map (homArrowFunctor X f))

omit [HasSheafify X.J AddCommGrpCat.{max u v w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The internal Hom complex out of a zero source is zero. -/
theorem sheafHomComplex_isZero_of_isZero
    {E : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
      (hE : IsZero E)
    (L : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    IsZero (sheafHomComplex X E L).obj := by
  apply complex_isZero_of_terms
  intro n
  apply (IsZero.iff_id_eq_zero _).2
  refine homDegree_hom_ext X n _ _ fun q => ?_
  exact (internalHomSheaf_isZero_of_isZero X
    ((HomologicalComplex.eval _ _ (-q)).map_isZero hE)).eq_of_tgt _ _

omit [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- A zero source gives a quasi-isomorphism for trivial reasons. -/
theorem homMap_quasiIso_of_isZero
    {E : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hE : IsZero E) (f : F ⟶ G) : QuasiIso (homMap X (𝟙 E) f) := by
  have h := StacksDraft.TotalComplexQuasiIso.isIso_of_isZero_of_isZero
    (homMap X (𝟙 E) f) (sheafHomComplex_isZero_of_isZero X hE F)
    (sheafHomComplex_isZero_of_isZero X hE G)
  infer_instance

omit [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **Two out of three for a termwise split short complex of sources.** -/
theorem homMap_quasiIso_of_degreewiseSplit
    (S : ShortComplex
      (CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ))
    (σ : ∀ p : ℤ, (S.map (HomologicalComplex.eval _ _ p)).Splitting) (f : F ⟶ G)
    [QuasiIso (homMap X (𝟙 S.X₁) f)] [QuasiIso (homMap X (𝟙 S.X₃) f)] :
    QuasiIso (homMap X (𝟙 S.X₂) f) := by
  let φ : internalHomShortComplex X S F ⟶ internalHomShortComplex X S G :=
    { τ₁ := homMap X (𝟙 S.X₃) f
      τ₂ := homMap X (𝟙 S.X₂) f
      τ₃ := homMap X (𝟙 S.X₁) f
      comm₁₂ := by
        dsimp [internalHomShortComplex]
        rw [homMap_comp, homMap_comp, Category.id_comp, Category.comp_id, Category.id_comp,
          Category.comp_id]
      comm₂₃ := by
        dsimp [internalHomShortComplex]
        rw [homMap_comp, homMap_comp, Category.id_comp, Category.comp_id, Category.id_comp,
          Category.comp_id] }
  have h1 : QuasiIso φ.τ₁ := ‹QuasiIso (homMap X (𝟙 S.X₃) f)›
  have h3 : QuasiIso φ.τ₃ := ‹QuasiIso (homMap X (𝟙 S.X₁) f)›
  exact StacksDraft.TotalComplexQuasiIso.quasiIso_τ₂ φ
    (HomologicalComplex.shortExact_of_degreewise_shortExact _
      (fun n => (internalHomTermwiseSplitting X S F σ n).shortExact))
    (HomologicalComplex.shortExact_of_degreewise_shortExact _
      (fun n => (internalHomTermwiseSplitting X S G σ n).shortExact))


section FiniteFree

/-- Sheaves of modules on a ringed site have finite biproducts, being abelian. -/
local instance hasFiniteBiproducts_sheafOfModules :
    HasFiniteBiproducts (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- `O^{⊕r}`, the direct sum of `r` copies of the structure sheaf, as an iterated binary
biproduct. -/
def unitPower : ℕ → SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  | 0 => 0
  | r + 1 => unitPower r ⊞ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)

omit [HasSheafify X.J AddCommGrpCat.{max u v w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}] in
/-- `O^{⊕0}` is the zero sheaf of modules. -/
@[simp] lemma unitPower_zero : unitPower X 0 = 0 := rfl

/-- The degreewise split short complex `O^{⊕r} ⟶ O^{⊕(r+1)} ⟶ O`. -/
def unitPowerShortComplex (r : ℕ) :
    ShortComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  ShortComplex.mk (biprod.inl : unitPower X r ⟶
      unitPower X r ⊞ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    biprod.snd (by simp)

/-- A direct summand of a finite free `O`-module: a retract of `O^{⊕r}` for some `r`.

This is the condition `IsDirectSummandOfFiniteFree` of Stacks 08FL, spelled so that it can be
stated at an arbitrary module universe; see the implementation notes. -/
def IsFiniteFreeSummand
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) : Prop :=
  ∃ r : ℕ, Nonempty (Retract M (unitPower X r))

/-- **The single-degree finite free case.** -/
theorem homMap_single_quasiIso_of_unitPower (f : F ⟶ G) [QuasiIso f] (k : ℤ) (r : ℕ) :
    QuasiIso (homMap X
      (𝟙 ((HomologicalComplex.single
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ) k).obj
        (unitPower X r))) f) := by
  let Sg := HomologicalComplex.single
    (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ) k
  have hone : QuasiIso
    (homMap X (𝟙 (Sg.obj (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) f) :=
    homMap_quasiIso_of_unitG X f k (HomologicalComplex.singleObjXSelf _ k _)
      (HomologicalComplex.single_obj_d
        (V := SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (c := ComplexShape.up ℤ) k _ k (k + 1))
      (HomologicalComplex.isZero_single_obj_X _ _ _)
  induction r with
  | zero =>
    rw [unitPower_zero]
    exact homMap_quasiIso_of_isZero X (Sg.map_isZero (isZero_zero _)) f
  | succ r ih =>
    show QuasiIso (homMap X (𝟙 (Sg.obj (unitPower X r ⊞
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) f)
    let T := (unitPowerShortComplex X r).map Sg
    have hT (p : ℤ) : (T.map (HomologicalComplex.eval _ _ p)).Splitting :=
      ((ShortComplex.Splitting.ofHasBinaryBiproduct (unitPower X r)
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).map Sg).map _
    have h1 : QuasiIso (homMap X (𝟙 T.X₁) f) := ih
    have h3 : QuasiIso (homMap X (𝟙 T.X₃) f) := hone
    exact homMap_quasiIso_of_degreewiseSplit X T hT f

/-- **The single-degree case for a direct summand of a finite free module.** -/
theorem homMap_single_quasiIso_of_isFiniteFreeSummand (f : F ⟶ G) [QuasiIso f] (k : ℤ)
    {A : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
      (hA : IsFiniteFreeSummand X A) :
    QuasiIso (homMap X
      (𝟙 ((HomologicalComplex.single
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ) k).obj
        A)) f) := by
  obtain ⟨r, ⟨ρ⟩⟩ := hA
  have := homMap_single_quasiIso_of_unitPower X f k r
  exact homMap_quasiIso_of_retract X
    (ρ.map
      (HomologicalComplex.single (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ) k)) f

omit [HasSheafify X.J AddCommGrpCat.{max u v w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}] in
/-- Being a direct summand of a finite free module transports along an isomorphism. -/
theorem IsFiniteFreeSummand.of_iso
    {M N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (e : M ≅ N)
    (hN : IsFiniteFreeSummand X N) : IsFiniteFreeSummand X M := by
  obtain ⟨r, ⟨ρ⟩⟩ := hN
  exact ⟨r, ⟨e.retract.trans ρ⟩⟩

omit [HasSheafify X.J AddCommGrpCat.{max u v w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}] in
/-- A zero module is a direct summand of a finite free module. -/
theorem IsFiniteFreeSummand.of_isZero
    {M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (hM : IsZero M) :
    IsFiniteFreeSummand X M :=
  ⟨0, ⟨⟨0, 0, by rw [zero_comp]; exact hM.eq_of_src (0 : M ⟶ M) (𝟙 M)⟩⟩⟩

end FiniteFree


section Main

/-- **The bounded case.** If `E` vanishes outside the window `[a, a + r)` and each of its terms
is a direct summand of a finite free `O`-module, then the internal Hom complex out of `E`
carries a quasi-isomorphism of targets to a quasi-isomorphism. -/
theorem homMap_quasiIso_of_bounded (f : F ⟶ G) [QuasiIso f] (r : ℕ) (a : ℤ)
    (E : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hlo : ∀ i, i < a → IsZero (E.X i)) (hhi : ∀ i, a + r ≤ i → IsZero (E.X i))
    (hterm : ∀ i, IsFiniteFreeSummand X (E.X i)) :
    QuasiIso (homMap X (𝟙 E) f) := by
  induction r generalizing a E with
  | zero =>
    refine homMap_quasiIso_of_isZero X (complex_isZero_of_terms E fun i => ?_) f
    by_cases hi : i < a
    · exact hlo i hi
    · exact hhi i (by push_cast; omega)
  | succ r ih =>
    have ha : IsZero (E.X (a - 1)) := hlo (a - 1) (by omega)
    set p := bottomProjection E a ha with hp
    set K := kernel p with hK
    have hz : IsZero (K.X a) := isZero_kernel_bottomProjection_X_self E a ha
    have hKiso (i : ℤ) (hi : i ≠ a) : K.X i ≅ E.X i :=
      have := isIso_kernel_ι_bottomProjection_f E a ha i hi
      asIso ((kernel.ι p).f i)
    have hKterm (i : ℤ) : IsFiniteFreeSummand X (K.X i) := by
      by_cases hi : i = a
      · subst i
        exact IsFiniteFreeSummand.of_isZero X hz
      · exact IsFiniteFreeSummand.of_iso X (hKiso i hi) (hterm i)
    have hKlo (i : ℤ) (hi : i < a + 1) : IsZero (K.X i) := by
      by_cases hia : i = a
      · subst i
        exact hz
      · exact IsZero.of_iso (hlo i (by omega)) (hKiso i hia)
    have hKhi (i : ℤ) (hi : a + 1 + r ≤ i) : IsZero (K.X i) :=
      IsZero.of_iso (hhi i (by push_cast; omega)) (hKiso i (by omega))
    have hKq : QuasiIso (homMap X (𝟙 K) f) := ih (a + 1) K hKlo hKhi hKterm
    have hAq : QuasiIso (homMap X
        (𝟙 ((HomologicalComplex.single
          (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (ComplexShape.up ℤ) a).obj (E.X a))) f) :=
      homMap_single_quasiIso_of_isFiniteFreeSummand X f a (hterm a)
    let T := ShortComplex.mk (kernel.ι p) p (kernel.condition p)
    refine homMap_quasiIso_of_degreewiseSplit X T (fun i => ?_) f
    by_cases hi : i = a
    · subst i
      have hpi : IsIso (p.f a) := isIso_bottomProjection_f_self E a ha
      exact ShortComplex.Splitting.ofIsZeroOfIsIso _ hz hpi
    · have hki := isIso_kernel_ι_bottomProjection_f E a ha i hi
      exact ShortComplex.Splitting.ofIsIsoOfIsZero _ hki
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) a (E.X a) i hi)

/-- **The strictly perfect case.** If `E` has only finitely many nonzero terms and each of them
is a direct summand of a finite free `O`-module, then the internal Hom complex out of `E`
carries a quasi-isomorphism of targets to a quasi-isomorphism. -/
theorem homMap_quasiIso_of_isFiniteFreeSummand (f : F ⟶ G) [QuasiIso f]
    (E : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hbdd : {i : ℤ | ¬ IsZero (E.X i)}.Finite)
    (hterm : ∀ i, IsFiniteFreeSummand X (E.X i)) :
    QuasiIso (homMap X (𝟙 E) f) := by
  obtain ⟨a, ha⟩ := hbdd.bddBelow
  obtain ⟨b, hb⟩ := hbdd.bddAbove
  refine homMap_quasiIso_of_bounded X f (b - a + 1).toNat a E ?_ ?_ hterm
  · intro i hi
    by_contra hz
    have := ha hz
    omega
  · intro i hi
    by_contra hz
    have := hb hz
    omega

end Main

end StrictlyPerfectHomQuasiIso

section CompareG

attribute [local instance] hasFiniteBiproducts_sheafOfModules

/-- `O^{⊕r}` written as an iterated binary biproduct is isomorphic to the direct sum over
`Fin r`.

This generalizes `AlgebraicGeometry.RingedSite.unitPowerIsoBiproduct`, which is the same
isomorphism for a `RingedSite.{u, u, u}`: here the ringed site is a `RingedSite.{u, v, w}`, its
objects, morphisms and structure sheaf in independent universes, and `unitPower` is
`AlgebraicGeometry.RingedSite.General.unitPower`. -/
def unitPowerIsoBiproduct (X : RingedSite.{u, v, w})
    [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] (r : ℕ) :
    unitPower X r ≅
      ⨁ fun _ : Fin r => SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O) := by
  induction r with
  | zero =>
    exact (isZero_zero _).iso
      (isZero_biproduct_fin_zero (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
  | succ r e =>
    exact (biprod.mapIso e (Iso.refl _)).trans
      (biproductFinSuccIso
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) r).symm

variable (X : RingedSite.{u, v, w})
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Being a direct summand of a finite free `O`-module can equivalently be tested against the
direct sum `O^{⊕r}` over `Fin r`. -/
theorem isFiniteFreeSummand_iff_retract_biproduct
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    IsFiniteFreeSummand X M ↔
      ∃ r : ℕ, Nonempty
        (Retract M
          (⨁ fun _ : Fin r => SheafOfModules.unit
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) := by
  constructor
  · rintro ⟨r, ⟨ρ⟩⟩
    exact ⟨r, ⟨ρ.trans (unitPowerIsoBiproduct X r).retract⟩⟩
  · rintro ⟨r, ⟨ρ⟩⟩
    exact ⟨r, ⟨ρ.trans (unitPowerIsoBiproduct X r).symm.retract⟩⟩

/-- A retract of a finite free `O`-module `SheafOfModules.free I` is a direct summand of a
finite free `O`-module in the sense of `IsFiniteFreeSummand`.

This is the bridge to the Stacks 08FL condition: `IsDirectSummandOfFiniteFree R M` is, by
`isDirectSummandOfFiniteFree_iff_free`, the existence of maps
`M ⟶ SheafOfModules.free (ULift (Fin n))` and back composing to the identity, which is exactly a
`Retract M (SheafOfModules.free (ULift (Fin n)))`. -/
theorem isFiniteFreeSummand_of_retract_free
    {M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (I : Type w) [Finite I]
    (ρ : Retract M (SheafOfModules.free (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) I)) :
    IsFiniteFreeSummand X M := by
  obtain ⟨r, ⟨e⟩⟩ := Finite.exists_equiv_fin I
  have hfree : SheafOfModules.free (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) I ≅
      ⨁ fun _ : Fin r => SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
    (CategoryTheory.Limits.IsColimit.coconePointUniqueUpToIso
        (SheafOfModules.isColimitFreeCofan (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) I)
        (biproduct.isColimit fun _ : I => SheafOfModules.unit
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).trans
      (biproduct.whiskerEquiv
        (f := fun _ : I => SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (g := fun _ : Fin r => SheafOfModules.unit
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) e fun _ => Iso.refl _)
  exact (isFiniteFreeSummand_iff_retract_biproduct X M).2 ⟨r, ⟨ρ.trans hfree.retract⟩⟩

/-- **The Stacks 08FL termwise condition implies `IsFiniteFreeSummand`, at an arbitrary
universe.** This is the `RingedSite.{u, u, u}` form of
`AlgebraicGeometry.RingedSite.isFiniteFreeSummand_of_isDirectSummandOfFiniteFree`, which is
stated at `RingedSite.{0, 0, 0}` because the whole of `IsStrictlyPerfect` is written there.
Nothing of the universe restriction is needed for the termwise condition: the substance is
`AlgebraicGeometry.RingedSite.isFiniteFreeSummand_of_retract_free`, which is general, and
`isDirectSummandOfFiniteFree_iff_free` holds whenever the sections of the modules and of the
structure sheaf lie in the same universe, as they do here. -/
theorem IsDirectSummandOfFiniteFree.isFiniteFreeSummand
    [X.J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
    {M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (hM : IsDirectSummandOfFiniteFree (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M) :
    IsFiniteFreeSummand X M := by
  obtain ⟨n, i, r, hir⟩ :=
    (isDirectSummandOfFiniteFree_iff_free (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M).1 hM
  exact isFiniteFreeSummand_of_retract_free X (ULift.{w} (Fin n)) ⟨i, r, hir⟩

end CompareG

section Terms

variable (X : RingedSite.{u, v, w})
  [HasSheafify X.J AddCommGrpCat.{max u v w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

attribute [local instance] hasFiniteBiproducts_sheafOfModules

/-- Sheaves of modules in the universe of the internal Hom complex have finite biproducts. -/
local instance hasFiniteBiproducts_sheafOfModulesMax :
    HasFiniteBiproducts (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- A sheaf of modules in the universe of the internal Hom complex is a retract of the universe
lift of a sheaf of modules with property `Pr`. -/
def RetractOfLiftWith
    (Pr : ObjectProperty (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (M : SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) : Prop :=
  ∃ D, Pr D ∧ Nonempty (Retract M ((homULift X).obj D))

variable {X}
variable (Pr : ObjectProperty (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
  [Pr.IsClosedUnderIsomorphisms] [Pr.IsClosedUnderFiniteCoproducts]

omit [HasSheafify X.J AddCommGrpCat.{max u v w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [Pr.IsClosedUnderIsomorphisms] [Pr.IsClosedUnderFiniteCoproducts] in
/-- A retract of a sheaf of modules satisfying `RetractOfLiftWith X Pr` satisfies it too. -/
lemma RetractOfLiftWith.of_retract {M M' : SheafOfModules.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (ρ : Retract M M') (h : RetractOfLiftWith X Pr M') : RetractOfLiftWith X Pr M := by
  obtain ⟨D, hD, ⟨ρ'⟩⟩ := h
  exact ⟨D, hD, ⟨ρ.trans ρ'⟩⟩

omit [HasSheafify X.J AddCommGrpCat.{max u v w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [Pr.IsClosedUnderIsomorphisms] [Pr.IsClosedUnderFiniteCoproducts] in
/-- `RetractOfLiftWith X Pr` is invariant under isomorphism. -/
lemma RetractOfLiftWith.of_iso {M M' : SheafOfModules.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (e : M ≅ M') (h : RetractOfLiftWith X Pr M') : RetractOfLiftWith X Pr M :=
  h.of_retract Pr ⟨e.hom, e.inv, e.hom_inv_id⟩

omit [HasSheafify X.J AddCommGrpCat.{max u v w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [Pr.IsClosedUnderIsomorphisms] in
/-- A zero sheaf of modules satisfies `RetractOfLiftWith X Pr`. -/
lemma RetractOfLiftWith.of_isZero {M : SheafOfModules.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (hM : IsZero M) :
    RetractOfLiftWith X Pr M :=
  ⟨∐ (PEmpty.elim : PEmpty.{1} → SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)),
    Pr.prop_coproduct (fun j => PEmpty.elim j),
    ⟨⟨0, 0, hM.eq_of_src _ _⟩⟩⟩

omit [HasSheafify X.J AddCommGrpCat.{max u v w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- `RetractOfLiftWith` is closed under finite biproducts. -/
lemma RetractOfLiftWith.biproduct {J : Type} [Fintype J]
    (f : J → SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (h : ∀ j, RetractOfLiftWith X Pr (f j)) : RetractOfLiftWith X Pr (⨁ f) := by
  choose D hD ρ using h
  let ρ' : ∀ j, Retract (f j) ((homULift X).obj (D j)) := fun j => (ρ j).some
  have hPD : Pr (⨁ D) :=
    Pr.prop_of_iso (CategoryTheory.Limits.biproduct.isoCoproduct D).symm (Pr.prop_coproduct hD)
  refine ⟨⨁ D, hPD, ⟨⟨CategoryTheory.Limits.biproduct.map (fun j => (ρ' j).i) ≫
      ((homULift X).mapBiproduct D).inv,
    ((homULift X).mapBiproduct D).hom ≫ CategoryTheory.Limits.biproduct.map (fun j => (ρ' j).r),
    ?_⟩⟩⟩
  refine CategoryTheory.Limits.biproduct.hom_ext' _ _ fun j => ?_
  simp only [Category.assoc, Iso.inv_hom_id_assoc, CategoryTheory.Limits.biproduct.ι_map_assoc,
    Category.comp_id]
  rw [CategoryTheory.Limits.biproduct.ι_map, ← Category.assoc, (ρ' j).retract, Category.id_comp]

/-- `RetractOfLiftWith` is closed under binary biproducts. -/
lemma RetractOfLiftWith.biprod
    {M M' : SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (h : RetractOfLiftWith X Pr M) (h' : RetractOfLiftWith X Pr M') :
    RetractOfLiftWith X Pr (M ⊞ M') := by
  obtain ⟨D, hD, ⟨ρ⟩⟩ := h
  obtain ⟨D', hD', ⟨ρ'⟩⟩ := h'
  have hDD : Pr (D ⊞ D') := by
    have hc : Pr (∐ (fun b : Bool => if b then D else D')) :=
      Pr.prop_coproduct fun b => by cases b <;> simpa using ‹_›
    refine Pr.prop_of_iso ?_ hc
    exact (CategoryTheory.Limits.biproduct.isoCoproduct _).symm ≪≫
      { hom := CategoryTheory.Limits.biproduct.desc fun b => match b with
          | true => CategoryTheory.Limits.biprod.inl
          | false => CategoryTheory.Limits.biprod.inr
        inv := CategoryTheory.Limits.biprod.desc
          (CategoryTheory.Limits.biproduct.ι (fun b : Bool => if b then D else D') true)
          (CategoryTheory.Limits.biproduct.ι (fun b : Bool => if b then D else D') false)
        hom_inv_id := by
          refine CategoryTheory.Limits.biproduct.hom_ext' _ _ fun b => ?_
          cases b <;> simp
        inv_hom_id := by
          refine CategoryTheory.Limits.biprod.hom_ext' _ _ ?_ ?_ <;> simp }
  have : PreservesFiniteLimits (homULift X) :=
    Stacks.SheafOfModules.preservesFiniteLimits_moduleULift
      (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  have : PreservesBinaryBiproducts (homULift X) :=
    preservesBinaryBiproducts_of_preservesBinaryProducts _
  refine ⟨D ⊞ D', hDD, ⟨⟨CategoryTheory.Limits.biprod.map ρ.i ρ'.i ≫
      ((homULift X).mapBiprod D D').inv,
    ((homULift X).mapBiprod D D').hom ≫ CategoryTheory.Limits.biprod.map ρ.r ρ'.r, ?_⟩⟩⟩
  rw [Category.assoc, Iso.inv_hom_id_assoc]
  refine CategoryTheory.Limits.biprod.hom_ext' _ _ ?_ ?_ <;>
    simp [Retract.retract_assoc]

omit [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- `RetractOfLiftWith` is closed under coproducts indexed by `ℤ` with finite support. -/
lemma RetractOfLiftWith.coproduct_of_finite_support
    (I : ℤ → SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (S : Finset ℤ) (hS : ∀ q, q ∉ S → IsZero (I q))
    (h : ∀ q, q ∈ S → RetractOfLiftWith X Pr (I q)) : RetractOfLiftWith X Pr (∐ I) := by
  classical
  let I' : S → SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
    fun q => I q.1
  refine RetractOfLiftWith.of_iso Pr
    ((CategoryTheory.Limits.sigmaSubtypeIsoOfIsZero I (fun q => q ∈ S)
        (fun q hq => hS q hq)).symm ≪≫
      (CategoryTheory.Limits.biproduct.isoCoproduct I').symm) ?_
  exact RetractOfLiftWith.biproduct Pr I' (fun q => h q.1 q.2)

/-- The internal Hom sheaf out of a retract is a retract. -/
def internalHomSheafRetract {M M' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (ρ : Retract M M') (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    Retract (internalHomSheaf X M F) (internalHomSheaf X M' F) where
  i := internalHomPre X (C := F) ρ.r
  r := internalHomPre X (C := F) ρ.i
  retract := by rw [internalHomPreG_comp, ρ.retract, internalHomPreG_id]

/-- The internal Hom sheaf out of a binary biproduct is a retract of the biproduct of the internal
Hom sheaves. -/
def internalHomSheafBiprodRetract
    (A A' F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    Retract (internalHomSheaf X (A ⊞ A') F) (internalHomSheaf X A F ⊞ internalHomSheaf X A' F) where
  i := biprod.lift (internalHomPre X (C := F) biprod.inl) (internalHomPre X (C := F) biprod.inr)
  r := biprod.desc (internalHomPre X (C := F) biprod.fst) (internalHomPre X (C := F) biprod.snd)
  retract := by
    rw [biprod.lift_desc, internalHomPreG_comp, internalHomPreG_comp, ← internalHomPreG_add,
      biprod.total, internalHomPreG_id]

omit [HasSheafify X.J AddCommGrpCat.{max u v w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- Postcomposition with the identity is the identity on internal Hom sheaves. -/
lemma internalHomPostG_id {A B : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} :
    internalHomPost X (A := A) (𝟙 B) = 𝟙 (internalHomSheaf X A B) := by
  ext U a
  rfl

/-- The internal Hom sheaf is invariant under isomorphisms of both variables. -/
def internalHomSheafIsoOfIso
    {A A' B B' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (eA : A ≅ A') (eB : B ≅ B') : internalHomSheaf X A B ≅ internalHomSheaf X A' B' where
  hom := internalHomPre X (C := B) eA.inv ≫ internalHomPost X (A := A') eB.hom
  inv := internalHomPost X (A := A') eB.inv ≫ internalHomPre X (C := B) eA.hom
  hom_inv_id := by
    rw [Category.assoc, ← Category.assoc (internalHomPost X eB.hom), internalHomPost_comp,
      eB.hom_inv_id, internalHomPostG_id, Category.id_comp, internalHomPreG_comp, eA.hom_inv_id,
      internalHomPreG_id]
  inv_hom_id := by
    rw [Category.assoc, ← Category.assoc (internalHomPre X eA.hom), internalHomPreG_comp,
      eA.inv_hom_id, internalHomPreG_id, Category.id_comp, internalHomPost_comp, eB.inv_hom_id,
      internalHomPostG_id]

omit [HasSheafify X.J AddCommGrpCat.{max u v w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [Pr.IsClosedUnderIsomorphisms] [Pr.IsClosedUnderFiniteCoproducts] in
/-- The internal Hom sheaf out of the structure sheaf is a retract of the universe lift of the
target: it is the degree-zero term of the internal Hom complex between the two modules placed in
degree zero. -/
lemma RetractOfLiftWith.internalHomSheaf_unit
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (hF : Pr F) :
    RetractOfLiftWith X Pr
      (internalHomSheaf X
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) F) := by
  classical
  let Sg := HomologicalComplex.single
    (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (ComplexShape.up ℤ) 0
  let E := Sg.obj (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  let F' := Sg.obj F
  have hE : ∀ p, p ≠ 0 → IsZero (E.X p) :=
    fun p hp => HomologicalComplex.isZero_single_obj_X _ _ _ p hp
  -- the degree-zero term of `SheafHom(E, F')` is a retract of the lift of `F`
  have hterm : RetractOfLiftWith X Pr ((sheafHomComplex X E F').obj.X 0) :=
    ⟨F, hF, ⟨(homUnitEvaluationGIso X (E := E) (F := F') 0 0
        (HomologicalComplex.singleObjXSelf _ 0 _) hE ≪≫
      (homULift X).mapIso (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F)).retract⟩⟩
  -- the component at `q = 0` is a retract of that term
  let φ := homDegreeProjection X E F' 0 0
  let c : Fan (fun q : ℤ => internalHomSheaf X (E.X (-q)) (F'.X (0 - q))) :=
    Fan.mk (internalHomSheaf X (E.X (-0)) (F'.X (0 - 0))) fun q =>
      if hq : q = 0 then eqToHom (by subst hq; rfl) else 0
  let ψ : internalHomSheaf X (E.X (-0)) (F'.X (0 - 0)) ⟶ (sheafHomComplex X E F').obj.X 0 :=
    (homDegreeIsLimit X E F' 0).lift c
  have hψ : ψ ≫ φ = 𝟙 _ := by
    have := (homDegreeIsLimit X E F' 0).fac c ⟨0⟩
    refine this.trans ?_
    simp [c]
  refine RetractOfLiftWith.of_retract Pr
    ((internalHomSheafIsoOfIso (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).symm
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).symm).retract.trans
      ⟨ψ, φ, hψ⟩) hterm


/-- The internal Hom sheaf out of `O^{⊕r}` into a module with property `Pr` is a retract of the
universe lift of a module with property `Pr`. -/
lemma RetractOfLiftWith.internalHomSheaf_unitPower (r : ℕ)
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (hF : Pr F) :
    RetractOfLiftWith X Pr (internalHomSheaf X (unitPower X r) F) := by
  induction r with
  | zero =>
    exact RetractOfLiftWith.of_isZero Pr (internalHomSheaf_isZero_of_isZero X (isZero_zero _))
  | succ r ih =>
    refine RetractOfLiftWith.of_retract Pr (internalHomSheafBiprodRetract (unitPower X r)
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) F) ?_
    exact RetractOfLiftWith.biprod Pr ih (RetractOfLiftWith.internalHomSheaf_unit Pr F hF)

/-- The internal Hom sheaf out of a direct summand of a finite free module into a module with
property `Pr` is a retract of the universe lift of a module with property `Pr`. -/
lemma RetractOfLiftWith.internalHomSheaf_of_isFiniteFreeSummand
    {M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
      (hM : IsFiniteFreeSummand X M)
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (hF : Pr F) :
    RetractOfLiftWith X Pr (internalHomSheaf X M F) := by
  obtain ⟨r, ⟨ρ⟩⟩ := hM
  exact RetractOfLiftWith.of_retract Pr (internalHomSheafRetract ρ F)
    (RetractOfLiftWith.internalHomSheaf_unitPower Pr r F hF)

/-- **The terms of the internal Hom complex out of a strictly perfect complex.**  If `E` is
bounded with terms direct summands of finite free modules, the degree-`n` term of
`SheafHom^•(E, F)` is a retract of the universe lift of a module with property `Pr`, as soon as
`Pr` holds of the terms `F^{p + n}` for the degrees `p` in which `E` does not vanish and `Pr` is
closed under isomorphisms and finite coproducts. -/
theorem RetractOfLiftWith.sheafHomComplex_X
    (E F : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hE : {i : ℤ | ¬ IsZero (E.X i)}.Finite) (hEt : ∀ i, IsFiniteFreeSummand X (E.X i)) (n : ℤ)
    (hF : ∀ p, ¬ IsZero (E.X p) → Pr (F.X (p + n))) :
    RetractOfLiftWith X Pr ((sheafHomComplex X E F).obj.X n) := by
  classical
  refine RetractOfLiftWith.of_iso Pr (strictlyPerfectHomDegreeIso X E F hE n) ?_
  refine RetractOfLiftWith.coproduct_of_finite_support Pr _ (hE.image (fun i : ℤ => -i)).toFinset
    (fun q hq => isZero_internalHomSheaf_notMem_negSupport X E F hE n q hq) fun q hq => ?_
  have hq' : ¬ IsZero (E.X (-q)) := by
    simp only [Set.Finite.mem_toFinset, Set.mem_image, Set.mem_setOf_eq] at hq
    obtain ⟨i, hi, rfl⟩ := hq
    simpa using hi
  exact RetractOfLiftWith.internalHomSheaf_of_isFiniteFreeSummand Pr (hEt _) _
    (Pr.prop_of_iso (F.XIsoOfEq (by omega)) (hF (-q) hq'))

end Terms

end AlgebraicGeometry.RingedSite.General

end
