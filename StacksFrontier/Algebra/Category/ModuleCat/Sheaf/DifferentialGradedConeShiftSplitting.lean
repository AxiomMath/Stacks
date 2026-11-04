module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedConePushout
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedPullbackGradedShift

/-!
# The degreewise splitting of a cone as homogeneous families

Let `R` be a sheaf of rings on a site, let `A` be a sheaf of differential graded `R`-algebras and
let `f : K ⟶ L` be a morphism of right differential graded `A`-modules. Degreewise the cone of
`f` is the direct sum `K^{n+1} ⊕ L^n`, and
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedConeAdmissible.lean` records that
splitting as a `SheafOfModules.DifferentialGradedModule.GradedSplitting` of the pair
(inclusion, projection). The projection there goes to the *chosen* shift `shift K`.

This file writes the same splitting without the chosen shift: its two off-diagonal coordinates
become right-linear families of degrees `1` and `-1` in the sense of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedPullbackGradedShift.lean`, where
a right-linear family of degree `k` from `M` to `N` is a homomorphism of right graded modules
`M ⟶ N.shift k`. This is the form the splitting has to be in to be transported by a pullback
`f^*` or by a relative tensor product `- ⊗ N`: those transport a homogeneous family of a given
degree, but they have no comparison with the chosen shift.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.ConePackage.firstFamily`: the first coordinate of the
  degreewise splitting, a right-linear family of degree one from the cone to the source.
* `SheafOfModules.DifferentialGradedModule.ConePackage.sectionFamily`: the inclusion of the first
  summand, a right-linear family of degree minus one from the source to the cone, whose
  degreewise components are `SheafOfModules.DifferentialGradedModule.ConePackage.sectionX`.

## Main results

* `SheafOfModules.DifferentialGradedModule.ConePackage.sectionFamily_firstFamily`,
  `sectionFamily_retraction`, `inclusion_firstFamily`, `inclusion_retraction` and
  `firstFamily_sectionFamily_add`: **the four coordinate families split the cone**. Together with
  the degree-zero families of the retraction of `ConePackage.gradedSplitting` and of the cone's
  inclusion they are a matrix of homogeneous families whose off-diagonal products vanish, whose
  diagonal products are the identities of the source and of the target, and whose two diagonal
  products in the other order add up to the identity of the cone.
* `SheafOfModules.DifferentialGradedModule.ConePackage.sectionFamily_d`: **the section of the
  cone's projection is a null-homotopy of `f` followed by the cone's inclusion**, written without
  the chosen shift.

## Implementation notes

The two new families are the ones already present in the admissible-splitting file, read in
degrees shifted by one: `firstFamily` is `n ↦ (componentIso n).hom ≫ biprod.fst`, which needs no
transport at all, and `sectionX` is `ConePackage.coneSectionX` with the identification
`ShiftPackage.xIso` of `(K[1])^n` with `K^{n+1}` removed, which costs one transport
`SheafOfModules.degCastHom` along `n = n + -1 + 1`.

That `sectionX` commutes with the right action is `ConePackage.sections_ext` on the two
coordinates, exactly as `ConePackage.gradedSplitting` proves it for `coneSectionX`; the first
coordinate is `ConePackage.action_first`, which is an `HEq` because the degrees `(n + i) + 1` and
`(n + 1) + i` are propositionally but not definitionally equal, and the second vanishes by
`ConePackage.action_second`. It is stated separately, as `sectionX_map_smul`, rather than inlined
in the definition of `sectionFamily`, because the definition is exposed and so its proof term may
not mention a private declaration.

All five splitting relations are proved degreewise, the content of each being one of Mathlib's
`CategoryTheory.Limits.biprod.inl_fst`, `biprod.inl_snd`, `biprod.inr_fst`, `biprod.inr_snd` and
`biprod.total` conjugated by `ConePackage.componentIso`. What surrounds that content is the
bookkeeping of the transports which `SheafOfModules.GradedModule.shiftComp` and
`SheafOfModules.GradedModule.shiftOfHom` insert, and the private lemmas below — each proved by
`subst` on an equality of degrees — are what commutes a transport past the map it meets.

The null-homotopy identity is `ConePackage.coneSectionX_d` with the chosen shift removed. The one
input that cannot be read off the cone package is the sign of the differential of `shift K`: by
`ShiftPackage.shifted_complex` its complex is Mathlib's `CochainComplex.shiftFunctor` applied to
the complex of `K`, whose differential is `(-1)^1` times that of `K`, and transporting that
across the equality of complexes is `HomologicalComplex.Hom.comm` for the corresponding
`CategoryTheory.eqToHom`. That sign is why the two terms of `sectionFamily_d` are added rather
than subtracted.

Both summands of `sectionFamily_d` are morphisms `K^n ⟶ C(f)^n`, but one of them is produced with
its source spelled `((forgetToGradedModule A).obj K).piece n` and the other with it spelled
`K.complex.X n`. The two are definitionally equal and not syntactically equal, which is enough
for every judgement except the search for the `HAdd` instance of their sum, so the first summand
carries a type ascription.

## References

* [Stacks Project, Tag 0FS5](https://stacks.math.columbia.edu/tag/0FS5)
* [Stacks Project, Tag 0FSC](https://stacks.math.columbia.edu/tag/0FSC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe t a m v u

namespace SheafOfModules.DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A : DifferentialGradedAlgebra.{t, a} R} {K L : DifferentialGradedModule.{t, a, m} A}

namespace ConePackage

variable {f : K ⟶ L}

/-! ### Transports along equalities of degrees -/

/-- A transport of degrees commutes with the first coordinate of the degreewise splitting. -/
@[reassoc]
private theorem degCastHom_fst (Pk : ConePackage f) {p q : ℤ} (h : p = q) :
    degCastHom Pk.cone.complex.X h ≫ (Pk.componentIso q).hom ≫ biprod.fst =
      ((Pk.componentIso p).hom ≫ biprod.fst) ≫
        degCastHom K.complex.X (show p + 1 = q + 1 by omega) := by
  subst h
  rw [degCastHom_eq_id, degCastHom_eq_id, Category.id_comp, Category.comp_id]

/-- A transport of degrees commutes with the second coordinate of the degreewise splitting. -/
@[reassoc]
private theorem degCastHom_coneRetractionX (Pk : ConePackage f) {p q : ℤ} (h : p = q) :
    degCastHom Pk.cone.complex.X h ≫ Pk.coneRetractionX q =
      Pk.coneRetractionX p ≫ degCastHom L.complex.X h := by
  subst h
  rw [degCastHom_eq_id, degCastHom_eq_id, Category.id_comp, Category.comp_id]

/-- A transport of degrees commutes with the inclusion of the first summand of the degreewise
splitting. -/
@[reassoc]
private theorem degCastHom_inl (Pk : ConePackage f) {p q : ℤ} (h : p + 1 = q + 1) :
    degCastHom K.complex.X h ≫ biprod.inl ≫ (Pk.componentIso q).inv =
      biprod.inl ≫ (Pk.componentIso p).inv ≫
        degCastHom Pk.cone.complex.X (show p = q by omega) := by
  have hpq : p = q := by omega
  subst hpq
  rw [degCastHom_eq_id, degCastHom_eq_id, Category.id_comp, Category.comp_id]

/-- A transport of degrees commutes with a morphism of right differential graded modules. -/
@[reassoc]
private theorem degCastHom_hom (φ : K ⟶ L) {p q : ℤ} (h : p = q) :
    degCastHom K.complex.X h ≫ φ.toHomologicalComplex.f q =
      φ.toHomologicalComplex.f p ≫ degCastHom L.complex.X h := by
  subst h
  rw [degCastHom_eq_id, degCastHom_eq_id, Category.id_comp, Category.comp_id]

/-- A transport of degrees commutes with the cone's inclusion. -/
@[reassoc]
private theorem degCastHom_inclusion (Pk : ConePackage f) {p q : ℤ} (h : p = q) :
    degCastHom L.complex.X h ≫ Pk.inclusion.toHomologicalComplex.f q =
      Pk.inclusion.toHomologicalComplex.f p ≫ degCastHom Pk.cone.complex.X h :=
  degCastHom_hom Pk.inclusion h

/-- A transport of degrees is absorbed by the differential it precedes. -/
@[reassoc]
private theorem degCastHom_comp_d' (T : CochainComplex (SheafOfModules.{m} R) ℤ) {i i' : ℤ}
    (h : i = i') (j : ℤ) : degCastHom T.X h ≫ T.d i' j = T.d i j :=
  degCastHom_comp_d T h j

/-- A transport of degrees is absorbed by the differential it follows. -/
@[reassoc]
private theorem d_comp_degCastHom' (T : CochainComplex (SheafOfModules.{m} R) ℤ) (i : ℤ)
    {j j' : ℤ} (h : j = j') : T.d i j ≫ degCastHom T.X h = T.d i j' :=
  d_comp_degCastHom T i h

/-- The cone's inclusion is split by the second coordinate of the degreewise splitting. -/
@[reassoc]
private theorem inclusion_coneRetractionX' (Pk : ConePackage f) (n : ℤ) :
    Pk.inclusion.toHomologicalComplex.f n ≫ Pk.coneRetractionX n = 𝟙 _ :=
  Pk.inclusion_coneRetractionX n

/-- Two readings of the differential of `K` followed by the inclusion of the first summand, at
two spellings of the same degree, agree. -/
private theorem inl_comp_eq (Pk : ConePackage f) {p n : ℤ} (h : p = n) :
    K.complex.d n (p + 1) ≫ biprod.inl ≫ (Pk.componentIso p).inv ≫
        degCastHom Pk.cone.complex.X h =
      K.complex.d n (n + 1) ≫ biprod.inl ≫ (Pk.componentIso n).inv := by
  subst h
  rw [degCastHom_eq_id, Category.comp_id]

/-- A transport of degrees commutes with the first coordinate of the degreewise splitting, read
on local sections. -/
private theorem fst_castHom (Pk : ConePackage f) {p q : ℤ} (h : p = q) (U : Cᵒᵖ)
    (w : (Pk.cone.complex.X p).val.obj U) :
    ((Pk.componentIso q).hom ≫ biprod.fst).val.app U (castHom Pk.cone.complex.X h U w) =
      castHom K.complex.X (show p + 1 = q + 1 by omega) U
        (((Pk.componentIso p).hom ≫ biprod.fst).val.app U w) := by
  subst h; rfl

/-- A transport of degrees commutes with the second coordinate of the degreewise splitting, read
on local sections. -/
private theorem snd_castHom (Pk : ConePackage f) {p q : ℤ} (h : p = q) (U : Cᵒᵖ)
    (w : (Pk.cone.complex.X p).val.obj U) :
    ((Pk.componentIso q).hom ≫ biprod.snd).val.app U (castHom Pk.cone.complex.X h U w) =
      castHom L.complex.X h U (((Pk.componentIso p).hom ≫ biprod.snd).val.app U w) := by
  subst h; rfl

/-- Two transports of degrees with the same target agree on sections identified by an
`HEq`. -/
private theorem castHom_congr_heq {X : ℤ → SheafOfModules.{m} R} {i j k : ℤ} (hi : i = k)
    (hj : j = k) (U : Cᵒᵖ) {x : (X i).val.obj U} {y : (X j).val.obj U} (hxy : HEq x y) :
    castHom X hi U x = castHom X hj U y := by
  subst hi; subst hj; exact eq_of_heq hxy

/-- The right action on a transported homogeneous section is the transport of the right
action. -/
private theorem mul_castHom {p q : ℤ} (h : p = q) (i : ℤ) (U : Cᵒᵖ)
    (x : (K.complex.X p).val.obj U) (a : (A.complex.X i).val.obj U) :
    (K.mul q i).app U (castHom K.complex.X h U x) a =
      castHom K.complex.X (show p + i = q + i by omega) U ((K.mul p i).app U x a) := by
  subst h; rfl

/-! ### The first coordinate as a family of degree one -/

/-- **The first coordinate of the degreewise splitting of a cone**, as a right-linear family of
degree one from the cone to the source: in degree `n` it is the projection of
`C(f)^n ≅ K^{n+1} ⊕ L^n` onto its first summand. -/
noncomputable def firstFamily (Pk : ConePackage f) :
    (forgetToGradedModule A).obj Pk.cone ⟶ ((forgetToGradedModule A).obj K).shift 1 where
  app n := (Pk.componentIso n).hom ≫ biprod.fst
  map_smul n i U x a := by
    refine Eq.trans ?_
      (GradedModule.shift_smul ((forgetToGradedModule A).obj K) 1 n i U _ a).symm
    exact eq_of_heq ((Pk.action_first n i U x a).trans
      (heq_castHom K.complex.X (show n + 1 + i = n + i + 1 by omega) U _).symm)

/-- The degree-`n` component of the family of degree one is the first coordinate of the
degreewise splitting. -/
theorem firstFamily_app (Pk : ConePackage f) (n : ℤ) :
    Pk.firstFamily.app n = (Pk.componentIso n).hom ≫ biprod.fst :=
  rfl

/-! ### The inclusion of the first summand as a family of degree minus one -/

/-- The inclusion of the first summand of the degreewise splitting of a cone, in degree `n`: it
goes from `K^n` to `C(f)^{n-1}`, so it carries one transport of degrees. -/
noncomputable def sectionX (Pk : ConePackage f) (n : ℤ) :
    K.complex.X n ⟶ Pk.cone.complex.X (n + -1) :=
  degCastHom K.complex.X (show n = n + -1 + 1 by omega) ≫ biprod.inl ≫
    (Pk.componentIso (n + -1)).inv

/-- The inclusion of the first summand, read in the first coordinate of the degreewise
splitting. -/
@[reassoc]
private theorem sectionX_fst (Pk : ConePackage f) (n : ℤ) :
    Pk.sectionX n ≫ (Pk.componentIso (n + -1)).hom ≫ biprod.fst =
      degCastHom K.complex.X (show n = n + -1 + 1 by omega) := by
  show (degCastHom K.complex.X (show n = n + -1 + 1 by omega) ≫ biprod.inl ≫
    (Pk.componentIso (n + -1)).inv) ≫ (Pk.componentIso (n + -1)).hom ≫ biprod.fst = _
  simp only [Category.assoc, Iso.inv_hom_id_assoc, biprod.inl_fst, Category.comp_id]

/-- The inclusion of the first summand is annihilated by the second coordinate of the degreewise
splitting. -/
@[reassoc]
private theorem sectionX_snd (Pk : ConePackage f) (n : ℤ) :
    Pk.sectionX n ≫ (Pk.componentIso (n + -1)).hom ≫ biprod.snd = 0 := by
  show (degCastHom K.complex.X (show n = n + -1 + 1 by omega) ≫ biprod.inl ≫
    (Pk.componentIso (n + -1)).inv) ≫ (Pk.componentIso (n + -1)).hom ≫ biprod.snd = _
  simp only [Category.assoc, Iso.inv_hom_id_assoc, biprod.inl_snd, comp_zero]

/-- The inclusion of the first summand in the first coordinate, read on local sections. -/
private theorem sectionX_fst_app (Pk : ConePackage f) (n : ℤ) (U : Cᵒᵖ)
    (x : (K.complex.X n).val.obj U) :
    ((Pk.componentIso (n + -1)).hom ≫ biprod.fst).val.app U ((Pk.sectionX n).val.app U x) =
      castHom K.complex.X (show n = n + -1 + 1 by omega) U x :=
  (congrArg (fun φ : K.complex.X n ⟶ K.complex.X (n + -1 + 1) => φ.val.app U x)
    (Pk.sectionX_fst n)).trans (degCastHom_val_app _ _ U x)

/-- The inclusion of the first summand in the second coordinate, read on local sections. -/
private theorem sectionX_snd_app (Pk : ConePackage f) (n : ℤ) (U : Cᵒᵖ)
    (x : (K.complex.X n).val.obj U) :
    ((Pk.componentIso (n + -1)).hom ≫ biprod.snd).val.app U ((Pk.sectionX n).val.app U x) = 0 :=
  (congrArg (fun φ : K.complex.X n ⟶ L.complex.X (n + -1) => φ.val.app U x)
    (Pk.sectionX_snd n)).trans (homSections_zero U x)

/-- **The inclusion of the first summand of the degreewise splitting commutes with the right
action of the algebra**, up to the transport of degrees that the shift of a right graded module
inserts. -/
theorem sectionX_map_smul (Pk : ConePackage f) (n i : ℤ) (U : Cᵒᵖ)
    (x : (K.complex.X n).val.obj U) (a : (A.complex.X i).val.obj U) :
    (Pk.sectionX (n + i)).val.app U ((K.mul n i).app U x a) =
      castHom Pk.cone.complex.X (show n + -1 + i = n + i + -1 by omega) U
        ((Pk.cone.mul (n + -1) i).app U ((Pk.sectionX n).val.app U x) a) := by
  refine Pk.sections_ext (n + i + -1) U ?_ ?_
  · refine Eq.trans (Pk.sectionX_fst_app (n + i) U _) ?_
    refine Eq.trans ?_ (Pk.fst_castHom (show n + -1 + i = n + i + -1 by omega) U _).symm
    refine castHom_congr_heq _ _ U ?_
    refine HEq.symm ((Pk.action_first (n + -1) i U _ a).trans
      ((heq_of_eq ?_).trans (heq_castHom K.complex.X
        (show n + i = n + -1 + 1 + i by omega) U ((K.mul n i).app U x a))))
    exact Eq.trans (congrArg (fun w => (K.mul (n + -1 + 1) i).app U w a)
      (Pk.sectionX_fst_app n U x)) (mul_castHom (show n = n + -1 + 1 by omega) i U x a)
  · refine Eq.trans (Pk.sectionX_snd_app (n + i) U _) ?_
    refine Eq.trans ?_ (Pk.snd_castHom (show n + -1 + i = n + i + -1 by omega) U _).symm
    refine Eq.symm (Eq.trans (congrArg (castHom L.complex.X
      (show n + -1 + i = n + i + -1 by omega) U) ?_) (map_zero _))
    refine Eq.trans (Pk.action_second (n + -1) i U _ a) ?_
    refine Eq.trans (congrArg (fun w => (L.mul (n + -1) i).app U w a)
      (Pk.sectionX_snd_app n U x)) ?_
    exact Eq.trans (congrArg (fun q : (A.complex.X i).val.obj U →+ _ => q a)
      (map_zero ((L.mul (n + -1) i).app U))) (AddMonoidHom.zero_apply a)

/-- **The inclusion of the first summand of the degreewise splitting of a cone**, as a
right-linear family of degree minus one from the source to the cone: in degree `n` it is the
inclusion of `K^n` as the first summand of `C(f)^{n-1} ≅ K^n ⊕ L^{n-1}`. -/
noncomputable def sectionFamily (Pk : ConePackage f) :
    (forgetToGradedModule A).obj K ⟶ ((forgetToGradedModule A).obj Pk.cone).shift (-1) where
  app n := Pk.sectionX n
  map_smul n i U x a := Pk.sectionX_map_smul n i U x a

/-- The degree-`n` component of the family of degree minus one. -/
theorem sectionFamily_app (Pk : ConePackage f) (n : ℤ) :
    Pk.sectionFamily.app n = Pk.sectionX n :=
  rfl

/-- **The first coordinate of the family of degree minus one** is the transport of degrees along
`n = n + -1 + 1`. -/
theorem first_sectionFamily (Pk : ConePackage f) (n : ℤ) (U : Cᵒᵖ)
    (x : (K.complex.X n).val.obj U) :
    ((Pk.componentIso (n + -1)).hom ≫ biprod.fst).val.app U
        ((Pk.sectionFamily.app n).val.app U x) =
      castHom K.complex.X (show n = n + -1 + 1 by omega) U x :=
  Pk.sectionX_fst_app n U x

/-- **The second coordinate of the family of degree minus one vanishes.** -/
theorem second_sectionFamily (Pk : ConePackage f) (n : ℤ) (U : Cᵒᵖ)
    (x : (K.complex.X n).val.obj U) :
    ((Pk.componentIso (n + -1)).hom ≫ biprod.snd).val.app U
        ((Pk.sectionFamily.app n).val.app U x) = 0 :=
  Pk.sectionX_snd_app n U x

/-! ### The splitting relations -/

/-- The cone's inclusion is annihilated by the first coordinate of the degreewise splitting. -/
@[reassoc]
private theorem inclusion_fst (Pk : ConePackage f) (n : ℤ) :
    Pk.inclusion.toHomologicalComplex.f n ≫ (Pk.componentIso n).hom ≫ biprod.fst = 0 := by
  rw [Pk.inclusion_f n]
  simp

/-- The two coordinates of the degreewise splitting of a cone decompose its identity. -/
private theorem componentIso_total (Pk : ConePackage f) (n : ℤ) :
    ((Pk.componentIso n).hom ≫ biprod.fst) ≫ biprod.inl ≫ (Pk.componentIso n).inv +
        Pk.coneRetractionX n ≫ Pk.inclusion.toHomologicalComplex.f n = 𝟙 _ := by
  rw [Pk.inclusion_f n]
  show (Pk.componentIso n).hom ≫ (biprod.fst ≫ biprod.inl) ≫ (Pk.componentIso n).inv +
    (Pk.componentIso n).hom ≫ (biprod.snd ≫ biprod.inr) ≫ (Pk.componentIso n).inv = 𝟙 _
  rw [← Preadditive.comp_add, ← Preadditive.add_comp, biprod.total, Category.id_comp,
    Iso.hom_inv_id]

/-- **The family of degree minus one followed by the family of degree one is the identity of the
source.** -/
theorem sectionFamily_firstFamily (Pk : ConePackage f) :
    GradedModule.shiftComp (show (-1 : ℤ) + 1 = 0 by omega) Pk.sectionFamily Pk.firstFamily =
      GradedModule.shiftOfHom (𝟙 ((forgetToGradedModule A).obj K)) := by
  refine GradedModule.Hom.ext fun n => ?_
  show Pk.sectionX n ≫ ((Pk.componentIso (n + -1)).hom ≫ biprod.fst) ≫
      degCastHom K.complex.X (show n + -1 + 1 = n + 0 by omega) =
    𝟙 _ ≫ degCastHom K.complex.X (show n = n + 0 by omega)
  rw [← Category.assoc, Pk.sectionX_fst n, degCastHom_comp_degCastHom, Category.id_comp]

/-- **The family of degree minus one is annihilated by the retraction of the cone's
inclusion.** -/
theorem sectionFamily_retraction (Pk : ConePackage f) :
    GradedModule.shiftComp (show (-1 : ℤ) + 0 = -1 by omega) Pk.sectionFamily
        (GradedModule.shiftOfHom Pk.gradedSplitting.r) = 0 := by
  refine GradedModule.Hom.ext fun n => ?_
  show Pk.sectionX n ≫ (((Pk.componentIso (n + -1)).hom ≫ biprod.snd) ≫
      degCastHom L.complex.X (show n + -1 = n + -1 + 0 by omega)) ≫
      degCastHom L.complex.X (show n + -1 + 0 = n + -1 by omega) = 0
  rw [← Category.assoc, ← Category.assoc, Pk.sectionX_snd n, zero_comp, zero_comp]

/-- **The cone's inclusion is annihilated by the family of degree one.** -/
theorem inclusion_firstFamily (Pk : ConePackage f) :
    GradedModule.shiftComp (show (0 : ℤ) + 1 = 1 by omega)
        (GradedModule.shiftOfHom ((forgetToGradedModule A).map Pk.inclusion))
        Pk.firstFamily = 0 := by
  refine GradedModule.Hom.ext fun n => ?_
  show (Pk.inclusion.toHomologicalComplex.f n ≫
      degCastHom Pk.cone.complex.X (show n = n + 0 by omega)) ≫
      ((Pk.componentIso (n + 0)).hom ≫ biprod.fst) ≫
      degCastHom K.complex.X (show n + 0 + 1 = n + 1 by omega) = 0
  simp only [Category.assoc, Pk.degCastHom_fst_assoc (show n = n + 0 by omega),
    Pk.inclusion_fst_assoc, zero_comp]

/-- **The cone's inclusion followed by the retraction is the identity of the target.** -/
theorem inclusion_retraction (Pk : ConePackage f) :
    GradedModule.shiftComp (show (0 : ℤ) + 0 = 0 by omega)
        (GradedModule.shiftOfHom ((forgetToGradedModule A).map Pk.inclusion))
        (GradedModule.shiftOfHom Pk.gradedSplitting.r) =
      GradedModule.shiftOfHom (𝟙 ((forgetToGradedModule A).obj L)) := by
  refine GradedModule.Hom.ext fun n => ?_
  show (Pk.inclusion.toHomologicalComplex.f n ≫
      degCastHom Pk.cone.complex.X (show n = n + 0 by omega)) ≫
      (Pk.coneRetractionX (n + 0) ≫
        degCastHom L.complex.X (show n + 0 = n + 0 + 0 by omega)) ≫
      degCastHom L.complex.X (show n + 0 + 0 = n + 0 by omega) =
    𝟙 _ ≫ degCastHom L.complex.X (show n = n + 0 by omega)
  rw [Category.id_comp]
  simp only [Category.assoc,
    Pk.degCastHom_coneRetractionX_assoc (show n = n + 0 by omega),
    Pk.inclusion_coneRetractionX'_assoc n, degCastHom_comp_degCastHom]

/-- **The two diagonal products of the splitting add up to the identity of the cone.** -/
theorem firstFamily_sectionFamily_add (Pk : ConePackage f) :
    GradedModule.shiftComp (show (1 : ℤ) + -1 = 0 by omega) Pk.firstFamily Pk.sectionFamily +
        GradedModule.shiftComp (show (0 : ℤ) + 0 = 0 by omega)
          (GradedModule.shiftOfHom (M := (forgetToGradedModule A).obj Pk.cone)
            (N := (forgetToGradedModule A).obj L) Pk.gradedSplitting.r)
          (GradedModule.shiftOfHom ((forgetToGradedModule A).map Pk.inclusion)) =
      GradedModule.shiftOfHom (𝟙 ((forgetToGradedModule A).obj Pk.cone)) := by
  refine GradedModule.Hom.ext fun n => ?_
  have h₁ : ((Pk.componentIso n).hom ≫ biprod.fst) ≫ Pk.sectionX (n + 1) ≫
        degCastHom Pk.cone.complex.X (show n + 1 + -1 = n + 0 by omega) =
      (((Pk.componentIso n).hom ≫ biprod.fst) ≫ biprod.inl ≫ (Pk.componentIso n).inv) ≫
        degCastHom Pk.cone.complex.X (show n = n + 0 by omega) := by
    rw [sectionX]
    simp only [Category.assoc, Pk.degCastHom_inl_assoc (show n + 1 = n + 1 + -1 + 1 by omega),
      degCastHom_comp_degCastHom]
  have h₂ : (Pk.coneRetractionX n ≫ degCastHom L.complex.X (show n = n + 0 by omega)) ≫
        (Pk.inclusion.toHomologicalComplex.f (n + 0) ≫
          degCastHom Pk.cone.complex.X (show n + 0 = n + 0 + 0 by omega)) ≫
        degCastHom Pk.cone.complex.X (show n + 0 + 0 = n + 0 by omega) =
      (Pk.coneRetractionX n ≫ Pk.inclusion.toHomologicalComplex.f n) ≫
        degCastHom Pk.cone.complex.X (show n = n + 0 by omega) := by
    simp only [Category.assoc, Pk.degCastHom_inclusion_assoc (show n = n + 0 by omega),
      degCastHom_comp_degCastHom]
  show ((Pk.componentIso n).hom ≫ biprod.fst) ≫ Pk.sectionX (n + 1) ≫
        degCastHom Pk.cone.complex.X (show n + 1 + -1 = n + 0 by omega) +
      (Pk.coneRetractionX n ≫ degCastHom L.complex.X (show n = n + 0 by omega)) ≫
        (Pk.inclusion.toHomologicalComplex.f (n + 0) ≫
          degCastHom Pk.cone.complex.X (show n + 0 = n + 0 + 0 by omega)) ≫
        degCastHom Pk.cone.complex.X (show n + 0 + 0 = n + 0 by omega) =
    𝟙 _ ≫ degCastHom Pk.cone.complex.X (show n = n + 0 by omega)
  rw [h₁, h₂, ← Preadditive.add_comp, Pk.componentIso_total n]

/-! ### The null-homotopy identity -/

/-- The inclusion of the first summand of the degreewise splitting, read through the chosen
shift. -/
@[reassoc]
private theorem xIso_inv_coneSectionX (Pk : ConePackage f) (p : ℤ) :
    ((shiftPackage K).xIso p).inv ≫ Pk.coneSectionX p =
      biprod.inl ≫ (Pk.componentIso p).inv := by
  show ((shiftPackage K).xIso p).inv ≫ ((shiftPackage K).xIso p).hom ≫ biprod.inl ≫
    (Pk.componentIso p).inv = _
  rw [Iso.inv_hom_id_assoc]

/-- The family of degree minus one, written through the chosen shift. -/
private theorem sectionX_eq (Pk : ConePackage f) (n : ℤ) :
    Pk.sectionX n = degCastHom K.complex.X (show n = n + -1 + 1 by omega) ≫
      ((shiftPackage K).xIso (n + -1)).inv ≫ Pk.coneSectionX (n + -1) := by
  show degCastHom K.complex.X (show n = n + -1 + 1 by omega) ≫ biprod.inl ≫
    (Pk.componentIso (n + -1)).inv = _
  rw [Pk.xIso_inv_coneSectionX (n + -1)]

/-- **The differential of the chosen shift of `K` is minus the differential of `K`**, read
through the identification `ShiftPackage.xIso` of the homogeneous pieces. -/
private theorem shift_d_eq (p : ℤ) :
    (shift K).complex.d p (p + 1) =
      -(((shiftPackage K).xIso p).hom ≫ K.complex.d (p + 1) (p + 1 + 1) ≫
        ((shiftPackage K).xIso (p + 1)).inv) := by
  have hcomm : (shift K).complex.d p (p + 1) ≫ ((shiftPackage K).xIso (p + 1)).hom =
      -(((shiftPackage K).xIso p).hom ≫ K.complex.d (p + 1) (p + 1 + 1)) := by
    refine Eq.trans ((eqToHom (shiftPackage K).shifted_complex).comm p (p + 1)).symm ?_
    show ((shiftPackage K).xIso p).hom ≫
      ((1 : ℤ).negOnePow • K.complex.d (p + 1) (p + 1 + 1)) = _
    simp
  rw [← Iso.eq_comp_inv] at hcomm
  rw [hcomm, Preadditive.neg_comp, Category.assoc]

/-- **The section of a cone's projection is a null-homotopy of `f` followed by the cone's
inclusion**, written without the chosen shift: the family of degree minus one followed by the
cone's differential, plus the differential of `K` followed by the family, is `f` followed by the
cone's inclusion. -/
theorem sectionFamily_d (Pk : ConePackage f) (n : ℤ) :
    (Pk.sectionFamily.app n ≫ Pk.cone.complex.d (n + -1) (n + -1 + 1) ≫
          degCastHom Pk.cone.complex.X (show n + -1 + 1 = n by omega) :
        K.complex.X n ⟶ Pk.cone.complex.X n) +
        K.complex.d n (n + 1) ≫ Pk.sectionFamily.app (n + 1) ≫
          degCastHom Pk.cone.complex.X (show n + 1 + -1 = n by omega) =
      f.toHomologicalComplex.f n ≫ Pk.inclusion.toHomologicalComplex.f n := by
  have hT : Pk.sectionX n ≫ Pk.cone.complex.d (n + -1) (n + -1 + 1) ≫
        degCastHom Pk.cone.complex.X (show n + -1 + 1 = n by omega) =
      f.toHomologicalComplex.f n ≫ Pk.inclusion.toHomologicalComplex.f n +
        -(K.complex.d n (n + 1) ≫ Pk.sectionX (n + 1) ≫
          degCastHom Pk.cone.complex.X (show n + 1 + -1 = n by omega)) := by
    rw [Pk.sectionX_eq n, Category.assoc, Category.assoc,
      ← Category.assoc (Pk.coneSectionX (n + -1)), Pk.coneSectionX_d (n + -1),
      Preadditive.add_comp, Preadditive.comp_add, Preadditive.comp_add]
    refine congrArg₂ (· + ·) ?_ ?_
    · simp only [Category.assoc, Iso.inv_hom_id_assoc,
        degCastHom_hom_assoc f (show n = n + -1 + 1 by omega),
        Pk.degCastHom_inclusion_assoc (show n = n + -1 + 1 by omega),
        degCastHom_comp_degCastHom, degCastHom_eq_id, Category.comp_id]
    · rw [sectionX]
      simp only [shift_d_eq, Preadditive.neg_comp, Preadditive.comp_neg, Category.assoc,
        Iso.inv_hom_id_assoc, Pk.xIso_inv_coneSectionX_assoc, degCastHom_comp_d'_assoc,
        d_comp_degCastHom'_assoc, Pk.inl_comp_eq]
  show Pk.sectionX n ≫ Pk.cone.complex.d (n + -1) (n + -1 + 1) ≫
        degCastHom Pk.cone.complex.X (show n + -1 + 1 = n by omega) +
      K.complex.d n (n + 1) ≫ Pk.sectionX (n + 1) ≫
        degCastHom Pk.cone.complex.X (show n + 1 + -1 = n by omega) =
    f.toHomologicalComplex.f n ≫ Pk.inclusion.toHomologicalComplex.f n
  rw [hT]
  exact neg_add_cancel_right _ _

end ConePackage

end SheafOfModules.DifferentialGradedModule

end
