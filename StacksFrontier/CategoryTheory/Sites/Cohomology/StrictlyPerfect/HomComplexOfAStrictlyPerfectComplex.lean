module

public import Mathlib.Algebra.Category.ModuleCat.Products
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplex
import StacksCore.Tactic.StacksAttribute

/-!
# The internal Hom complex of a strictly perfect complex

Let `(C, O)` be a ringed site and let `E` and `F` be complexes of `O`-modules with `E`
bounded — in particular, with `E` strictly perfect. This file identifies each term of the
internal Hom complex `SheafHom(E, F)` of Stacks 0A8Z with the finite direct sum

  `SheafHom(E, F)^n = ⨁_{n = p + q} SheafHom(E^{-q}, F^{n-q})`

of the internal Hom sheaves of its terms.

## Main definitions

* `AlgebraicGeometry.RingedSite.homDegreeProjection`: the projection of the `n`-th term of the
  internal Hom complex onto `SheafHom(E^{-q}, F^{n-q})`.

## Main results

* `AlgebraicGeometry.RingedSite.homDegreeIsLimit`: those projections exhibit the `n`-th term as
  the product, over `q : ℤ`, of the internal Hom sheaves of the terms. This needs no hypothesis
  on `E` at all.
* `AlgebraicGeometry.RingedSite.strictlyPerfectHomDegreeIso`: the degreewise direct-sum
  description, for `E` bounded.
* `AlgebraicGeometry.RingedSite.strictlyPerfectHomDegreeIso_inv_homDegreeProjection` and
  `AlgebraicGeometry.RingedSite.strictlyPerfectHomDegreeIso_inv_homDegreeProjection_of_ne`:
  **the characterisation of that isomorphism.** Its inverse carries the `q`-th coproduct
  inclusion to the `q`-th projection `homDegreeProjection X E F n q` and kills the other
  projections. Since the projections exhibit a limit and the inclusions a colimit, this
  determines the isomorphism, so a consumer can compute with it without unfolding it.

## Implementation notes

The internal Hom complex of Stacks 0A8Z is realized by
`AlgebraicGeometry.RingedSite.sheafHomComplex`, whose underlying complex is produced by
`Classical.choice` from the structure `SheafHomComplex`. Its terms are therefore opaque: the
explicit product `sheafHomComplexObj` is not available, and the only access to
`(sheafHomComplex X E F).obj.X n` is through the characterizing data `sectionsIso`,
`restrict_natural` and `smul_natural`. Accordingly the direct-sum description is obtained in
two steps, neither of which inspects the construction:

* `homDegreeIsLimit` shows that the maps `homDegreeProjection`, read off from `sectionsIso`,
  exhibit `(sheafHomComplex X E F).obj.X n` as the *product* over `q : ℤ` of the sheaves
  `SheafHom(E^{-q}, F^{n-q})`. This is proved by reflecting the limit through
  `SheafOfModules.forget` and evaluating at each object of the site, where the statement
  becomes the corresponding product of modules. The reindexing `q ↦ (-q, n - q)` of
  `CochainComplex.HomComplex.Triplet n` by `ℤ` is `cochainFamilyEquiv`.
* `productCoproductIsoOfFiniteSupport` identifies that product with the coproduct, using that
  all but finitely many summands vanish. This is the only place the hypothesis on `E` enters:
  `E` is bounded, so `E^{-q}` is zero for all but finitely many `q`, and
  `internalHomSheaf_isZero_of_isZero` turns that into vanishing of the summand.

The differential is not re-described here. Its standard Hom-complex form is already part of
the data of `SheafHomComplex`, namely the statement that `sectionsIso` is an isomorphism of
complexes onto `CochainComplex.HomComplex`, so it carries no separate content.

Universes are collapsed to `RingedSite.{u, u, u}` with modules in `SheafOfModules.{u}`. This is
not a narrowing introduced here: the Hom complex of `Ch21.Sec34` lands in
`SheafOfModules.{max u v m}`, so a statement relating it to a coproduct of `SheafOfModules.{m}`
sheaves of modules forces `max u v m = m`, and the statement of Stacks 08JH is itself written at
`RingedSite.{u, u, u}`.

The hypothesis on `E` is boundedness, `{i | ¬ IsZero (E.X i)}.Finite`, rather than strict
perfectness. Two reasons, and the first is forced:

* `IsStrictlyPerfect` of `Ch21.Sec44.Tag08FM` — the definition carrying the Stacks 08FL tag —
  is **universe-monomorphic in the ring and module universes**. Its signature is
  `IsStrictlyPerfect.{u_1, u_2}` over `Sheaf J RingCat.{0}` with complexes in
  `SheafOfModules.{0, u_2, u_1, 0}`, because that file's variable block writes `RingCat` and
  `AddCommGrpCat` with no universe annotation and both universes are then solved to `0`. So the
  predicate cannot even be mentioned at `RingedSite.{u, u, u}`; stating it would require
  `Stacks.SheafOfModules.Tensor.ringSheaf X.O : Sheaf X.J RingCat.{0}` plus two further
  `AddCommGrpCat.{0}` sheafification instances that Stacks 08JH does not assume.
* Boundedness is strictly weaker than strict perfectness — it is literally the `bounded` field
  of `IsStrictlyPerfect` — and it is all the direct-sum decomposition uses. The direct-summand
  condition on the terms plays no role in this lemma. So the statement below is a
  generalization of the tag's statement, not a weakening of it, and it carries no hypothesis
  the tag lacks.

## References

* [Stacks Project, Tag 08JH](https://stacks.math.columbia.edu/tag/08JH)
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CochainComplex.HomComplex

universe u

namespace AlgebraicGeometry.RingedSite

/-- A product indexed by a type on which all but finitely many factors vanish agrees with the
coproduct over the same index. The two canonical maps are built from the finite set carrying
the support, and both composites are checked componentwise. -/
def productCoproductIsoOfFiniteSupport
    {C : Type*} [Category C] [Preadditive C] {ι : Type*}
    (A : ι → C) [HasProduct A] [HasCoproduct A]
    (s : Finset ι) (hs : ∀ i, i ∉ s → IsZero (A i)) : ∏ᶜ A ≅ ∐ A := by
  classical
  let f : ∏ᶜ A ⟶ ∐ A := ∑ i ∈ s, Pi.π A i ≫ Sigma.ι A i
  let g : ∐ A ⟶ ∏ᶜ A := Sigma.desc (fun i => Pi.lift
    (fun j => if h : i = j then eqToHom (congrArg A h) else 0))
  have hg (i j : ι) : Sigma.ι A i ≫ g ≫ Pi.π A j =
      if h : i = j then eqToHom (congrArg A h) else 0 := by simp [g]
  refine ⟨f, g, ?_, ?_⟩
  · apply Pi.hom_ext
    intro j
    by_cases hj : j ∈ s
    · simp only [f, Preadditive.sum_comp, Category.assoc, hg, Category.id_comp]
      rw [Finset.sum_eq_single j]
      · simp
      · intro i hi hij
        simp [hij]
      · simp [hj]
    · exact (hs j hj).eq_of_tgt _ _
  · apply Sigma.hom_ext
    intro i
    by_cases hi : i ∈ s
    · simp only [f, g, Preadditive.comp_sum, Sigma.ι_comp_desc_assoc,
        Pi.lift_comp_π_assoc, Category.comp_id]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j hj hji
        simp [Ne.symm hji]
      · simp [hi]
    · exact (hs i hi).eq_of_src _ _

/-- The defining property of `productCoproductIsoOfFiniteSupport` on the diagonal: its inverse
sends the `i`-th coproduct inclusion to the `i`-th product projection.

Stated, together with `productCoproductIsoOfFiniteSupport_inv_π_of_ne`, because the
declarations of this file are `public` but not `@[expose]`, so a consumer cannot unfold the
isomorphism. The two lemmas together determine `.inv` completely — `Sigma.hom_ext` and
`Pi.hom_ext` reduce any identity involving it to its composites with the inclusions and the
projections — hence determine the isomorphism. No hypothesis beyond those of the isomorphism
itself. -/
@[simp] public lemma productCoproductIsoOfFiniteSupport_inv_π_self
    {C : Type*} [Category C] [Preadditive C] {ι : Type*}
    (A : ι → C) [HasProduct A] [HasCoproduct A]
    (s : Finset ι) (hs : ∀ i, i ∉ s → IsZero (A i)) (i : ι) :
    Sigma.ι A i ≫ (productCoproductIsoOfFiniteSupport A s hs).inv ≫ Pi.π A i = 𝟙 (A i) := by
  simp [productCoproductIsoOfFiniteSupport]

/-- The defining property of `productCoproductIsoOfFiniteSupport` off the diagonal: its inverse
kills the composite of the `i`-th coproduct inclusion with the `j`-th product projection for
`i ≠ j`. The companion of `productCoproductIsoOfFiniteSupport_inv_π_self`; the only hypothesis
beyond those of the isomorphism is `i ≠ j`. -/
public lemma productCoproductIsoOfFiniteSupport_inv_π_of_ne
    {C : Type*} [Category C] [Preadditive C] {ι : Type*}
    (A : ι → C) [HasProduct A] [HasCoproduct A]
    (s : Finset ι) (hs : ∀ i, i ∉ s → IsZero (A i)) {i j : ι} (hij : i ≠ j) :
    Sigma.ι A i ≫ (productCoproductIsoOfFiniteSupport A s hs).inv ≫ Pi.π A j = 0 := by
  simp [productCoproductIsoOfFiniteSupport, hij]

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The projection of the `n`-th term of the internal Hom complex onto the internal Hom sheaf
from `E^{-q}` to `F^{n-q}`, read off from the identification of sections with the ordinary Hom
complex on each slice site. The two naturality clauses of `SheafHomComplex` are exactly what
make this a morphism of sheaves of modules: `smul_natural` gives semilinearity over the
sections of the structure sheaf, and `restrict_natural` gives naturality in the site. -/
@[expose] public def homDegreeProjection
    (E F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
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
        refine ModuleCat.hom_ext (LinearMap.ext fun s => PresheafOfModules.hom_ext fun W => ?_)
        ext x
        exact ((sheafHomComplex X E F).restrict_natural f.unop n (-q) (n - q)
          (by omega) s W.unop.hom x).symm }

omit [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The defining property of `homDegreeProjection`: on a section over `U` it reads off the
`(-q, n - q)` component of the corresponding degree-`n` cochain of the restrictions.

Stated because the declarations of this file are `public` but not `@[expose]`, so a consumer
cannot unfold the projection; `homDegreeProjection` itself carries `@[expose]` only so that
this characterisation can be proved by `rfl`. -/
public lemma homDegreeProjection_val_app_apply
    (E F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n q : ℤ) (U : X.C)
    (s : ((sheafHomComplex X E F).obj.X n).val.obj (op U)) :
    (homDegreeProjection X E F n q).val.app (op U) s =
      ((AddCommGrpCat.Hom.hom (((sheafHomComplex X E F).sectionsIso U).hom.f n) s).v
        (-q) (n - q) (by omega)).val := rfl

/-- A degree-`n` cochain from `E` to `F` is the same thing as a family, indexed by `q : ℤ`, of
morphisms `E^{-q} ⟶ F^{n-q}`. This is the reindexing of
`CochainComplex.HomComplex.Triplet n` by `ℤ` along `q ↦ (-q, n - q)`. -/
private def cochainFamilyEquiv
    {C : Type*} [Category C] [Preadditive C]
    (E F : CochainComplex C ℤ) (n : ℤ) :
    Cochain E F n ≃+ (∀ q : ℤ, E.X (-q) ⟶ F.X (n - q)) := by
  let e : ℤ ≃ Triplet n :=
    { toFun q := ⟨-q, n - q, by omega⟩
      invFun t := -t.p
      left_inv q := neg_neg q
      right_inv t := by
        obtain ⟨p, q, h⟩ := t
        dsimp
        congr 1 <;> omega }
  exact
    { __ := (Equiv.piCongrLeft (fun t : Triplet n => E.X t.p ⟶ F.X t.q) e).symm
      map_add' := fun _ _ => rfl }

/-- Sections of the internal Hom sheaf over `U` are morphisms of the restrictions to the slice
site over `U`; the two directions are the constructor and the projection of
`SheafOfModules.Hom`. -/
private def internalHomSectionAddEquiv
    (A B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (U : X.C) :
    (internalHomSheaf X A B).val.obj (op U) ≃+ (A.over U ⟶ B.over U) where
  toFun s := ⟨s⟩
  invFun s := s.val
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- Sections over `U` of the `n`-th term of the internal Hom complex are families of sections
of the internal Hom sheaves of the terms. -/
private def homDegreeSectionEquiv
    (E F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
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
    (E F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n : ℤ) :
    IsLimit (Fan.mk ((sheafHomComplex X E F).obj.X n)
      (homDegreeProjection X E F n)) := by
  haveI := (SheafOfModules.fullyFaithfulForget.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).full
  haveI := (SheafOfModules.fullyFaithfulForget.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).faithful
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

omit [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The internal Hom sheaf out of a zero module is zero. -/
public theorem internalHomSheaf_isZero_of_isZero
    {A B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (hA : IsZero A) :
    IsZero (internalHomSheaf X A B) := by
  apply (IsZero.iff_id_eq_zero _).2
  ext U s
  have hz := (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
    U.unop).map_isZero hA
  exact congrArg SheafOfModules.Hom.val
    (hz.eq_of_src (⟨s⟩ : A.over U.unop ⟶ B.over U.unop)
      ⟨(0 : (internalHomSheaf X A B).val.obj U)⟩)

omit [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The summands of the degreewise direct-sum description vanish outside the negated support of
`E`: there `E^{-q}` is zero, hence so is the internal Hom sheaf out of it. -/
private theorem isZero_internalHomSheaf_notMem_negSupport
    (E F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hE : {i : ℤ | ¬ IsZero (E.X i)}.Finite) (n q : ℤ)
    (hq : q ∉ (hE.image (fun i : ℤ => -i)).toFinset) :
    IsZero (internalHomSheaf X (E.X (-q)) (F.X (n - q))) :=
  internalHomSheaf_isZero_of_isZero X
    (of_not_not fun h => hq ((Set.Finite.mem_toFinset _).2 ⟨-q, h, neg_neg q⟩))

section StrictlyPerfectHomDegreeIso

/- Since Mathlib v4.35.0 instance search reaches the `ℤ`-indexed coproducts of sheaves of
modules through the section variable `HasSheafify X.J AddCommGrpCat` (via
`instHasWeakSheafifyOfHasSheafify`), which would make that variable a hypothesis of the
declarations below. With the bridge erased here, the same coproducts are found without it, as
before the bump. -/
attribute [-instance] instHasWeakSheafifyOfHasSheafify

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
@[stacks 08JH "finite direct-sum terms and Hom differential"]
def strictlyPerfectHomDegreeIso
    (E F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
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

omit [HasSheafify X.J AddCommGrpCat.{u}] in
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
    (E F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hE : {i : ℤ | ¬ IsZero (E.X i)}.Finite) (n q₀ : ℤ)
    (hvan : ∀ q : ℤ, q ≠ q₀ → IsZero (internalHomSheaf X (E.X (-q)) (F.X (n - q))))
    {T : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (g : ∀ q : ℤ, internalHomSheaf X (E.X (-q)) (F.X (n - q)) ⟶ T) :
    (strictlyPerfectHomDegreeIso X E F hE n).hom ≫ Sigma.desc g =
      homDegreeProjection X E F n q₀ ≫ g q₀ := by
  have hsum : (productCoproductIsoOfFiniteSupport
        (fun q : ℤ => internalHomSheaf X (E.X (-q)) (F.X (n - q)))
        (hE.image (fun i : ℤ => -i)).toFinset
        (isZero_internalHomSheaf_notMem_negSupport X E F hE n)).hom ≫ Sigma.desc g =
      ∑ i ∈ (hE.image (fun i : ℤ => -i)).toFinset,
        Pi.π (fun q : ℤ => internalHomSheaf X (E.X (-q)) (F.X (n - q))) i ≫ g i := by
    change (∑ i ∈ (hE.image (fun i : ℤ => -i)).toFinset,
        Pi.π (fun q : ℤ => internalHomSheaf X (E.X (-q)) (F.X (n - q))) i ≫
          Sigma.ι (fun q : ℤ => internalHomSheaf X (E.X (-q)) (F.X (n - q))) i) ≫
      Sigma.desc g = _
    simp only [Preadditive.sum_comp, Category.assoc, Sigma.ι_comp_desc]
  unfold strictlyPerfectHomDegreeIso
  rw [Iso.trans_hom, Category.assoc, hsum, Preadditive.comp_sum]
  rw [Finset.sum_eq_single q₀ (fun i _ hi => ?_) (fun hq₀ => ?_), ← Category.assoc]
  · exact congrArg (· ≫ g q₀)
      ((homDegreeIsLimit X E F n).conePointUniqueUpToIso_hom_comp _ ⟨q₀⟩)
  · simp [(hvan i hi).eq_zero_of_tgt]
  · simp [(isZero_internalHomSheaf_notMem_negSupport X E F hE n q₀ hq₀).eq_zero_of_tgt]

omit [HasSheafify X.J AddCommGrpCat.{u}] in
/-- The composite of the inverse of `strictlyPerfectHomDegreeIso` with the degree projections,
read off from `homDegreeIsLimit`: the inverse of the direct-sum description carries the `q`-th
coproduct inclusion to the `q`-th projection `homDegreeProjection X E F n q`. -/
private lemma strictlyPerfectHomDegreeIso_inv_homDegreeProjection_aux
    (E F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hE : {i : ℤ | ¬ IsZero (E.X i)}.Finite) (n q q' : ℤ) :
    Sigma.ι (fun q : ℤ => internalHomSheaf X (E.X (-q)) (F.X (n - q))) q ≫
        (strictlyPerfectHomDegreeIso X E F hE n).inv ≫ homDegreeProjection X E F n q' =
      Sigma.ι (fun q : ℤ => internalHomSheaf X (E.X (-q)) (F.X (n - q))) q ≫
        (productCoproductIsoOfFiniteSupport
            (fun q : ℤ => internalHomSheaf X (E.X (-q)) (F.X (n - q)))
            (hE.image (fun i : ℤ => -i)).toFinset
            (isZero_internalHomSheaf_notMem_negSupport X E F hE n)).inv ≫
        Pi.π (fun q : ℤ => internalHomSheaf X (E.X (-q)) (F.X (n - q))) q' := by
  have hcpu := IsLimit.conePointUniqueUpToIso_inv_comp (homDegreeIsLimit X E F n)
    (limit.isLimit (Discrete.functor
      (fun q : ℤ => internalHomSheaf X (E.X (-q)) (F.X (n - q))))) ⟨q'⟩
  simp only [Fan.mk_π_app, limit.cone_π] at hcpu
  simp only [strictlyPerfectHomDegreeIso, Iso.trans_inv, Category.assoc, hcpu]

omit [HasSheafify X.J AddCommGrpCat.{u}] in
/-- **The characterisation of `strictlyPerfectHomDegreeIso`.** The inverse of the degreewise
direct-sum description of Stacks 08JH carries the `q`-th coproduct inclusion to the `q`-th
degree projection: the composite of the inclusion of `SheafHom(E^{-q}, F^{n-q})`, of the
inverse of the isomorphism and of `homDegreeProjection X E F n q` is the identity.

Together with `strictlyPerfectHomDegreeIso_inv_homDegreeProjection_of_ne` this determines the
isomorphism, since `Sigma.hom_ext` and `homDegreeIsLimit` reduce any identity involving its
inverse to those composites. Stated because `strictlyPerfectHomDegreeIso` is `public` but not
`@[expose]`, so a consumer cannot unfold it.

The hypotheses are exactly those of `strictlyPerfectHomDegreeIso`: `E` bounded, i.e.
`hE : {i : ℤ | ¬ IsZero (E.X i)}.Finite`. Nothing further. -/
@[simp] public lemma strictlyPerfectHomDegreeIso_inv_homDegreeProjection
    (E F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hE : {i : ℤ | ¬ IsZero (E.X i)}.Finite) (n q : ℤ) :
    Sigma.ι (fun q : ℤ => internalHomSheaf X (E.X (-q)) (F.X (n - q))) q ≫
        (strictlyPerfectHomDegreeIso X E F hE n).inv ≫ homDegreeProjection X E F n q =
      𝟙 (internalHomSheaf X (E.X (-q)) (F.X (n - q))) := by
  rw [strictlyPerfectHomDegreeIso_inv_homDegreeProjection_aux]
  exact productCoproductIsoOfFiniteSupport_inv_π_self _ _ _ q

omit [HasSheafify X.J AddCommGrpCat.{u}] in
/-- The off-diagonal half of the characterisation of `strictlyPerfectHomDegreeIso`: for
`q ≠ q'` the composite of the `q`-th coproduct inclusion, of the inverse of the isomorphism and
of the `q'`-th degree projection vanishes. The companion of
`strictlyPerfectHomDegreeIso_inv_homDegreeProjection`.

Hypotheses: `E` bounded, as for `strictlyPerfectHomDegreeIso`, and `q ≠ q'`. -/
public lemma strictlyPerfectHomDegreeIso_inv_homDegreeProjection_of_ne
    (E F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hE : {i : ℤ | ¬ IsZero (E.X i)}.Finite) (n : ℤ) {q q' : ℤ} (hqq' : q ≠ q') :
    Sigma.ι (fun q : ℤ => internalHomSheaf X (E.X (-q)) (F.X (n - q))) q ≫
        (strictlyPerfectHomDegreeIso X E F hE n).inv ≫ homDegreeProjection X E F n q' = 0 := by
  rw [strictlyPerfectHomDegreeIso_inv_homDegreeProjection_aux]
  exact productCoproductIsoOfFiniteSupport_inv_π_of_ne _ _ _ hqq'

end StrictlyPerfectHomDegreeIso

end AlgebraicGeometry.RingedSite

end
