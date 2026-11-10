module

public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.Bifunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.StrictlyPerfectHomQuasiIso

/-!
# The internal Hom complex of a strictly perfect source, at unequal universes

Let `(C, O)` be a ringed site whose objects, morphisms and structure rings lie in three
independent universes `u`, `v` and `w`, and let `E`, `F` be complexes of `O`-modules with
sections in a fourth universe `m`. The internal Hom complex `SheafHom(E, F)` of Stacks 0A8Z has
sections in `max u v m`, and this module develops it at those universes:

* its degree-`n` term is the product over `q : ℤ` of the internal Hom sheaves
  `SheafHom(E^{-q}, F^{n-q})`, so a degreewise family of morphisms of the sources, not
  necessarily compatible with the differentials, induces a morphism of degree-`n` terms;
* a short complex `E₁ ⟶ E₂ ⟶ E₃` of sources which is split in every degree is therefore taken
  to a short complex `SheafHom(E₃, B) ⟶ SheafHom(E₂, B) ⟶ SheafHom(E₁, B)` which is again split
  in every degree, hence short exact;
* a morphism out of the restricted structure sheaf is determined by the image of the unit
  section.

The statements record the universes they are about: every one of them already has both of its
sides in `SheafOfModules.{max u v m}`, so none of them needs a collapse. They are needed on the
small étale site of an algebraic space, a `RingedSite.{u + 1, u, u}`, where the internal Hom
complex of two complexes of modules with sections in `u` has sections in `u + 1`.

The collapsed case `RingedSite.{u, u, u}` with modules in `u` is the instance `v := u`,
`w := u`, `m := u`, and is, in the namespace
`StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect`,
`HomComplexOfAStrictlyPerfectComplex`, `InternalHomTermwiseSplit`,
`StrictlyPerfectHomQuasiIso` and `InternalHomUnitSource`. The
coproduct description of the terms, including the 08JH comparison, is only available there: it
equates `max u v m` with `m`.

## Main definitions

* `AlgebraicGeometry.RingedSite.Raised.homDegreeProjection`: the projection of the degree-`n`
  term of `SheafHom(E, F)` onto `SheafHom(E^{-q}, F^{n-q})`.
* `AlgebraicGeometry.RingedSite.Raised.homDegreeFamilyMap`: the morphism of degree-`n` terms
  induced by a degreewise family of morphisms of the sources.
* `AlgebraicGeometry.RingedSite.Raised.internalHomShortComplex`: the short complex of internal
  Hom complexes out of a short complex of sources.
* `AlgebraicGeometry.RingedSite.Raised.internalHomTermwiseSplitting`: its degreewise splitting.
* `AlgebraicGeometry.RingedSite.Raised.unitOverHomEquiv`: a morphism out of the restricted
  structure sheaf is determined by the image of the unit section.

## Main results

* `AlgebraicGeometry.RingedSite.Raised.homDegreeIsLimit`: the degree-`n` term is the product of
  the internal Hom sheaves of the terms.
* `AlgebraicGeometry.RingedSite.Raised.internalHomShortComplex_shortExact`: the internal Hom
  complex out of a termwise split short complex of sources is short exact.

## References

* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
* [Stacks Project, Tag 08JC](https://stacks.math.columbia.edu/tag/08JC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CochainComplex.HomComplex

universe m u v w

namespace AlgebraicGeometry.RingedSite.Raised

variable (X : RingedSite.{u, v, w})

/-! ### The product description of the terms -/

/-- The projection of the degree-`n` term of the internal Hom complex onto the internal Hom
sheaf from `E^{-q}` to `F^{n-q}`, read off from the identification of sections with the ordinary
Hom complex on each slice site. -/
def homDegreeProjection
    (E F : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n q : ℤ) :
    (sheafHomComplex X E F).obj.X n ⟶ internalHomSheaf X (E.X (-q)) (F.X (n - q)) where
  val :=
    { app := fun U => ModuleCat.homAddEquiv.symm
        { toFun := fun s =>
            ((AddCommGrpCat.Hom.hom (((sheafHomComplex X E F).sectionsIso U.unop).hom.f n)
              s).v (-q) (n - q) (by omega)).val
          map_add' := by
            intro a b
            exact congrArg
              (fun c : Cochain (restrictComplex X E U.unop)
                  (restrictComplex X F U.unop) n =>
                (c.v (-q) (n - q) (by omega)).val)
              (map_add (AddCommGrpCat.Hom.hom
                (((sheafHomComplex X E F).sectionsIso U.unop).hom.f n)) a b)
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

/-- The defining property of `homDegreeProjection`: on a section over `U` it reads off the
`(-q, n - q)` component of the corresponding degree-`n` cochain of the restrictions. -/
lemma homDegreeProjection_val_app_apply
    (E F : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n q : ℤ) (U : X.C) (s : ((sheafHomComplex X E F).obj.X n).val.obj (op U)) :
    (homDegreeProjection X E F n q).val.app (op U) s =
      ((AddCommGrpCat.Hom.hom (((sheafHomComplex X E F).sectionsIso U).hom.f n) s).v
        (-q) (n - q) (by omega)).val := rfl

/-- Sections of the internal Hom sheaf over `U` are morphisms of the restrictions. -/
def internalHomSectionAddEquiv
    (A B : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (U : X.C) :
    (internalHomSheaf X A B).val.obj (op U) ≃+ (A.over U ⟶ B.over U) where
  toFun s := ⟨s⟩
  invFun s := s.val
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- Sections over `U` of the degree-`n` term of the internal Hom complex are families of
sections of the internal Hom sheaves of the terms.

The middle step is that a degree-`n` cochain from `E|_U` to `F|_U` is a family, indexed by
`q : ℤ`, of morphisms `E^{-q}|_U ⟶ F^{n-q}|_U`: that is the reindexing of
`CochainComplex.HomComplex.Triplet n` by `ℤ` along `q ↦ (-q, n - q)`. -/
def homDegreeSectionEquiv
    (E F : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n : ℤ) (U : X.C) :
    ((sheafHomComplex X E F).obj.X n).val.obj (op U) ≃+
      (∀ q : ℤ, (internalHomSheaf X (E.X (-q)) (F.X (n - q))).val.obj (op U)) :=
  let e : ℤ ≃ Triplet n :=
    { toFun q := ⟨-q, n - q, by omega⟩
      invFun t := -t.p
      left_inv q := neg_neg q
      right_inv t := by
        obtain ⟨p, q, h⟩ := t
        dsimp
        congr 1 <;> omega }
  let family : Cochain (restrictComplex X E U) (restrictComplex X F U) n ≃+
      (∀ q : ℤ, (restrictComplex X E U).X (-q) ⟶ (restrictComplex X F U).X (n - q)) :=
    { __ := (Equiv.piCongrLeft (fun t : Triplet n =>
        (restrictComplex X E U).X t.p ⟶ (restrictComplex X F U).X t.q) e).symm
      map_add' := fun _ _ => rfl }
  (HomologicalComplex.Hom.isoApp
    ((sheafHomComplex X E F).sectionsIso U) n).addCommGroupIsoToAddEquiv.trans
    (family.trans
      (AddEquiv.piCongrRight (fun q =>
        (internalHomSectionAddEquiv X (E.X (-q)) (F.X (n - q)) U).symm)))

/-- The degree-`n` term of the internal Hom complex is the product, over `q : ℤ`, of the
internal Hom sheaves from `E^{-q}` to `F^{n-q}`, with `homDegreeProjection` as projections. -/
def homDegreeIsLimit
    (E F : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n : ℤ) :
    IsLimit (Fan.mk ((sheafHomComplex X E F).obj.X n) (homDegreeProjection X E F n)) := by
  haveI := (SheafOfModules.fullyFaithfulForget.{max u v m}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).full
  haveI := (SheafOfModules.fullyFaithfulForget.{max u v m}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).faithful
  apply isLimitOfReflects (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  apply PresheafOfModules.evaluationJointlyReflectsLimits
  intro U
  let A : ℤ → ModuleCat ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U) := fun q =>
    (internalHomSheaf X (E.X (-q)) (F.X (n - q))).val.obj U
  let e : ((sheafHomComplex X E F).obj.X n).val.obj U ≃ₗ[
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U] (∀ q : ℤ, A q) :=
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

/-- The internal Hom sheaf out of a zero module is zero. -/
theorem internalHomSheaf_isZero_of_isZero
    {A B : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (hA : IsZero A) :
    IsZero (internalHomSheaf X A B) := by
  apply (IsZero.iff_id_eq_zero _).2
  ext U s
  have hz := (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
    U.unop).map_isZero hA
  exact congrArg SheafOfModules.Hom.val
    (hz.eq_of_src (⟨s⟩ : A.over U.unop ⟶ B.over U.unop)
      ⟨(0 : (internalHomSheaf X A B).val.obj U)⟩)

/-- Two morphisms into the degree-`n` term of an internal Hom complex agree as soon as their
composites with all the projections agree. -/
lemma homDegree_hom_ext
    {T : SheafOfModules.{max u v m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    {E B : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (n : ℤ) (f g : T ⟶ (sheafHomComplex X E B).obj.X n)
    (h : ∀ q, f ≫ homDegreeProjection X E B n q = g ≫ homDegreeProjection X E B n q) :
    f = g :=
  Fan.IsLimit.hom_ext (homDegreeIsLimit X E B n) f g h

/-- The internal Hom complex out of a zero source is zero. -/
theorem sheafHomComplex_isZero_of_isZero
    {E : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hE : IsZero E)
    (L : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    IsZero (sheafHomComplex X E L).obj := by
  apply complex_isZero_of_terms
  intro n
  apply (IsZero.iff_id_eq_zero _).2
  refine homDegree_hom_ext X n _ _ fun q => ?_
  exact (internalHomSheaf_isZero_of_isZero X
    ((HomologicalComplex.eval _ _ (-q)).map_isZero hE)).eq_of_tgt _ _

/-! ### Precomposition on internal Hom sheaves -/

/-- Precomposition with the identity is the identity on internal Hom sheaves. -/
lemma internalHomPre_id
    {A C : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} :
    internalHomPre X (C := C) (𝟙 A) = 𝟙 (internalHomSheaf X A C) := by
  ext U a
  rfl

/-- Precomposition on internal Hom sheaves is contravariantly functorial. -/
lemma internalHomPre_comp
    {A B C D : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (f : A ⟶ B) (g : B ⟶ C) :
    internalHomPre X (C := D) g ≫ internalHomPre X (C := D) f =
      internalHomPre X (C := D) (f ≫ g) := by
  ext U a
  rfl

/-- Precomposition on internal Hom sheaves is additive in the morphism, because restriction to a
slice of the site is additive on the underlying presheaves of modules. -/
lemma internalHomPre_add
    {A B C : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (f g : A ⟶ B) :
    internalHomPre X (C := C) (f + g) =
      internalHomPre X (C := C) f + internalHomPre X (C := C) g := by
  have hadd (U : X.C) :
      (restrFun X.O.obj U).map (homOf X (f + g)) =
        (restrFun X.O.obj U).map (homOf X f) + (restrFun X.O.obj U).map (homOf X g) := by
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  ext U a
  change (restrFun X.O.obj (unop U)).map (homOf X (f + g)) ≫
      (a : (restrFun X.O.obj (unop U)).obj (valOf X B) ⟶
        (restrFun X.O.obj (unop U)).obj (valOf X C)) =
    (restrFun X.O.obj (unop U)).map (homOf X f) ≫
      (a : (restrFun X.O.obj (unop U)).obj (valOf X B) ⟶
        (restrFun X.O.obj (unop U)).obj (valOf X C)) +
    (restrFun X.O.obj (unop U)).map (homOf X g) ≫
      (a : (restrFun X.O.obj (unop U)).obj (valOf X B) ⟶
        (restrFun X.O.obj (unop U)).obj (valOf X C))
  rw [hadd]
  exact Preadditive.add_comp _ _ _ _ _ _

/-- Precomposition with the zero morphism is zero, because restriction to a slice of the site
sends the zero morphism to zero. -/
lemma internalHomPre_zero
    {A B C : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} :
    internalHomPre X (C := C) (0 : A ⟶ B) = 0 := by
  have hzero (U : X.C) : (restrFun X.O.obj U).map (homOf X (0 : A ⟶ B)) = 0 := by
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  ext U a
  change (restrFun X.O.obj (unop U)).map (homOf X (0 : A ⟶ B)) ≫
      (a : (restrFun X.O.obj (unop U)).obj (valOf X B) ⟶
        (restrFun X.O.obj (unop U)).obj (valOf X C)) = 0
  rw [hzero]
  exact zero_comp

/-! ### Degreewise families of morphisms of the sources -/

/-- The degree-`n` component of `homMap k (𝟙 B)` is the product of the precompositions with the
components of `k`. -/
@[reassoc]
lemma homDegreeProjection_homMap
    {E E' : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (k : E' ⟶ E)
    (B : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n q : ℤ) :
    (homMap X k (𝟙 B)).f n ≫ homDegreeProjection X E' B n q =
      homDegreeProjection X E B n q ≫ internalHomPre X (k.f (-q)) := by
  ext U s
  rw [comp_val_app_apply, comp_val_app_apply, homDegreeProjection_val_app_apply,
    homDegreeProjection_val_app_apply]
  refine Eq.trans (congrArg SheafOfModules.Hom.val
    (sectionsIso_homMap_v X k (𝟙 B) U.unop n (-q) (n - q) (by omega) s)) ?_
  rfl

/-- The morphism of degree-`n` terms of internal Hom complexes induced by a family of morphisms
`E'^p ⟶ E^p` of the terms of the sources, with no compatibility with the differentials. -/
def homDegreeFamilyMap
    {E E' : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (φ : ∀ p : ℤ, E'.X p ⟶ E.X p)
    (B : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n : ℤ) :
    (sheafHomComplex X E B).obj.X n ⟶ (sheafHomComplex X E' B).obj.X n :=
  Fan.IsLimit.lift (homDegreeIsLimit X E' B n)
    (fun q => homDegreeProjection X E B n q ≫ internalHomPre X (φ (-q)))

/-- The defining property of `homDegreeFamilyMap`. -/
@[reassoc]
lemma homDegreeFamilyMap_homDegreeProjection
    {E E' : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (φ : ∀ p : ℤ, E'.X p ⟶ E.X p)
    (B : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n q : ℤ) :
    homDegreeFamilyMap X φ B n ≫ homDegreeProjection X E' B n q =
      homDegreeProjection X E B n q ≫ internalHomPre X (φ (-q)) :=
  Fan.IsLimit.fac (homDegreeIsLimit X E' B n) _ q

/-- The zero morphism of sources induces the zero morphism of internal Hom complexes. -/
lemma homMap_zero_left
    {E E' : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (B : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    homMap X (0 : E' ⟶ E) (𝟙 B) = 0 := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  rw [HomologicalComplex.zero_f]
  refine homDegree_hom_ext X n _ _ fun q => ?_
  rw [homDegreeProjection_homMap, HomologicalComplex.zero_f, internalHomPre_zero, comp_zero,
    zero_comp]

/-! ### Termwise split short complexes of sources -/

/-- The two induced maps of internal Hom complexes out of a short complex of sources compose to
zero. -/
lemma internalHomShortComplex_zero
    (S : ShortComplex
      (CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ))
    (B : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    homMap X S.g (𝟙 B) ≫ homMap X S.f (𝟙 B) = 0 := by
  rw [homMap_comp, S.zero, Category.comp_id, homMap_zero_left]

/-- The short complex `SheafHom(E₃, B) ⟶ SheafHom(E₂, B) ⟶ SheafHom(E₁, B)` obtained from a
short complex `E₁ ⟶ E₂ ⟶ E₃` of sources. -/
@[reducible] def internalHomShortComplex
    (S : ShortComplex
      (CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ))
    (B : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ShortComplex (CochainComplex
      (SheafOfModules.{max u v m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :=
  ShortComplex.mk (homMap X S.g (𝟙 B)) (homMap X S.f (𝟙 B)) (internalHomShortComplex_zero X S B)

/-- A degreewise section of `S.g` induces a degreewise retraction of the induced map. -/
lemma homMap_g_comp_homDegreeFamilyMap
    (S : ShortComplex
      (CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ))
    (B : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (s : ∀ p : ℤ, S.X₃.X p ⟶ S.X₂.X p)
    (hs : ∀ p : ℤ, s p ≫ S.g.f p = 𝟙 (S.X₃.X p)) (n : ℤ) :
    (homMap X S.g (𝟙 B)).f n ≫ homDegreeFamilyMap X s B n =
      𝟙 ((sheafHomComplex X S.X₃ B).obj.X n) := by
  refine homDegree_hom_ext X n _ _ fun q => ?_
  rw [Category.assoc, homDegreeFamilyMap_homDegreeProjection, homDegreeProjection_homMap_assoc,
    internalHomPre_comp, hs, internalHomPre_id, Category.comp_id, Category.id_comp]

/-- A degreewise retraction of `S.f` induces a degreewise section of the induced map. -/
lemma homDegreeFamilyMap_comp_homMap_f
    (S : ShortComplex
      (CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ))
    (B : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (r : ∀ p : ℤ, S.X₂.X p ⟶ S.X₁.X p)
    (hr : ∀ p : ℤ, S.f.f p ≫ r p = 𝟙 (S.X₁.X p)) (n : ℤ) :
    homDegreeFamilyMap X r B n ≫ (homMap X S.f (𝟙 B)).f n =
      𝟙 ((sheafHomComplex X S.X₁ B).obj.X n) := by
  refine homDegree_hom_ext X n _ _ fun q => ?_
  rw [Category.assoc, homDegreeProjection_homMap, homDegreeFamilyMap_homDegreeProjection_assoc,
    internalHomPre_comp, hr, internalHomPre_id, Category.comp_id, Category.id_comp]

/-- The compatibility identity of a degreewise splitting is inherited by the induced maps. -/
lemma homDegreeFamilyMap_splitting_id
    (S : ShortComplex
      (CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ))
    (B : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (r : ∀ p : ℤ, S.X₂.X p ⟶ S.X₁.X p)
    (s : ∀ p : ℤ, S.X₃.X p ⟶ S.X₂.X p)
    (hid : ∀ p : ℤ, S.g.f p ≫ s p + r p ≫ S.f.f p = 𝟙 (S.X₂.X p)) (n : ℤ) :
    homDegreeFamilyMap X s B n ≫ (homMap X S.g (𝟙 B)).f n +
        (homMap X S.f (𝟙 B)).f n ≫ homDegreeFamilyMap X r B n =
      𝟙 ((sheafHomComplex X S.X₂ B).obj.X n) := by
  refine homDegree_hom_ext X n _ _ fun q => ?_
  rw [Preadditive.add_comp, Category.assoc, Category.assoc, homDegreeProjection_homMap,
    homDegreeFamilyMap_homDegreeProjection, homDegreeFamilyMap_homDegreeProjection_assoc,
    homDegreeProjection_homMap_assoc, internalHomPre_comp, internalHomPre_comp,
    ← Preadditive.comp_add, ← internalHomPre_add, hid, internalHomPre_id, Category.comp_id,
    Category.id_comp]

/-- **The internal Hom complex reverses a termwise split short complex of sources, and the
result is again termwise split.** -/
def internalHomTermwiseSplitting
    (S : ShortComplex
      (CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ))
    (B : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (σ : ∀ p : ℤ, (S.map (HomologicalComplex.eval _ _ p)).Splitting) (n : ℤ) :
    ((internalHomShortComplex X S B).map (HomologicalComplex.eval _ _ n)).Splitting where
  r := homDegreeFamilyMap X (fun p => show S.X₃.X p ⟶ S.X₂.X p from (σ p).s) B n
  s := homDegreeFamilyMap X (fun p => show S.X₂.X p ⟶ S.X₁.X p from (σ p).r) B n
  f_r := homMap_g_comp_homDegreeFamilyMap X S B _ (fun p => (σ p).s_g) n
  s_g := homDegreeFamilyMap_comp_homMap_f X S B _ (fun p => (σ p).f_r) n
  id := homDegreeFamilyMap_splitting_id X S B _ _ (fun p => by rw [add_comm]; exact (σ p).id) n

/-- **The internal Hom complex out of a termwise split short complex of sources is short
exact.** -/
theorem internalHomShortComplex_shortExact
    (S : ShortComplex
      (CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ))
    (B : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [HasSheafify X.J AddCommGrpCat.{max u v m}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v m}]
    (σ : ∀ p : ℤ, (S.map (HomologicalComplex.eval _ _ p)).Splitting) :
    (internalHomShortComplex X S B).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (fun n => (internalHomTermwiseSplitting X S B σ n).shortExact)

/-! ### Morphisms out of the structure sheaf -/

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
    change φ.val.app V ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map V.unop.hom.op
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

end AlgebraicGeometry.RingedSite.Raised

end
