module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedComposition
import StacksCore.Tactic.StacksAttribute

/-! # Internal Hom out of the structure sheaf on a ringed site

Let `(C, O)` be a ringed site and write `O[0]` for the structure sheaf viewed as a complex of
`O`-modules concentrated in degree zero. For a complex `I` of `O`-modules, a homogeneous local
section of the internal Hom complex `SheafHom(O[0], I)` is determined by its value at the unit
section `1` of the structure sheaf, and every local section of `I` arises this way. So
evaluation at `1` is an isomorphism of complexes `SheafHom(O[0], I) ≅ I`, and after passing to
the derived category it assembles into a natural isomorphism `RSheafHom(O[0], -) ≅ 𝟭` on
`D(Mod(O))`: the identity functor is the derived internal Hom out of the structure sheaf.

## Main definitions

* `AlgebraicGeometry.RingedSite.structureSheafComplex`: the structure sheaf as a complex of
  modules concentrated in degree zero.
* `AlgebraicGeometry.RingedSite.structureSheafHomEvaluation`: evaluation at the unit section,
  as a morphism of complexes `SheafHom(O[0], I) ⟶ I`.
* `AlgebraicGeometry.RingedSite.structureSheafHomIso`: that morphism as an isomorphism.
* `AlgebraicGeometry.RingedSite.derivedStructureSheafHomModelIso`: the identification
  `RSheafHom(O[0], I) ≅ I` for a K-injective complex `I`.
* `AlgebraicGeometry.RingedSite.derivedStructureSheafHomIso`: the identification
  `RSheafHom(O[0], Z) ≅ Z` for an arbitrary object `Z` of the derived category.
* `AlgebraicGeometry.RingedSite.derivedStructureSheafHomNatIso`: the natural isomorphism
  `RSheafHom(O[0], -) ≅ 𝟭`.

## Main results

* `AlgebraicGeometry.RingedSite.structureSheafHomEvaluation_apply`: evaluation at the unit
  section is what the morphism of complexes does on a homogeneous local section.
* `AlgebraicGeometry.RingedSite.structureSheafHomEvaluation_naturality`: the complex-level
  identification is natural in the target.
* `AlgebraicGeometry.RingedSite.derivedStructureSheafHomIso_model`: on a K-injective complex
  the derived identification is the K-injective model comparison followed by evaluation at the
  unit section. This pins the derived identification, which is otherwise built from a chosen
  K-injective representative.

## Implementation notes

The internal Hom complex is available only through the characterising data recorded by
`AlgebraicGeometry.RingedSite.SheafHomComplex`, so evaluation at the unit section is built from
the evaluation operation `AlgebraicGeometry.RingedSite.applyHomSection` on homogeneous local
sections: additivity and `O`-linearity are the additivity and semilinearity of evaluation in
the Hom section, compatibility with restriction is the restriction compatibility of evaluation
together with the fact that `1` restricts to `1`, and compatibility with the differentials is
the Leibniz rule, whose second term vanishes because `O[0]` has zero differentials.

Bijectivity on sections over `U` is a composite of three bijections: the characterising
description of the sections of the internal Hom complex as cochains on the slice site over `U`;
the fact that a cochain out of a complex concentrated in degree zero is one morphism; and the
fact that a morphism out of the free module of rank one on the slice site over `U` is one
section of the target, namely its value at `1`.

The passage to the derived category is the usual transport along a K-injective representative:
`AlgebraicGeometry.RingedSite.derivedSheafHomComparison` computes the derived internal Hom into
a K-injective complex as the class of the ordinary internal Hom complex, and the naturality of
the resulting identification extends from morphisms of complexes to arbitrary morphisms of the
derived category because every morphism into the class of a K-injective complex is the class of
a morphism of complexes.

## References

* [Stacks Project, Tag 08JD](https://stacks.math.columbia.edu/tag/08JD)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
* [Stacks Project, Tag 0A97](https://stacks.math.columbia.edu/tag/0A97)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CochainComplex.HomComplex

universe u v w d

namespace AlgebraicGeometry.RingedSite

section StructureSheaf

variable (X : RingedSite.{u, v, w})
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The structure sheaf of a ringed site, as a complex of modules concentrated in degree
zero.

The universes of the objects, of the morphisms and of the sections of the structure sheaf are
independent: the module sections are those of the structure sheaf, so the module universe is
the ring universe, and nothing here refers to the size of the site. This is what lets the
complex be formed on the small étale ringed site of an algebraic space, which is a
`AlgebraicGeometry.RingedSite.{u + 1, u, u}`. -/
abbrev structureSheafComplex :
    CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ :=
  (HomologicalComplex.single (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (ComplexShape.up ℤ) 0).obj (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- The unit section `1` of the structure sheaf over `U`, read as a section of degree zero of
the structure sheaf complex. -/
abbrev structureSheafOne (U : X.C) : ((structureSheafComplex X).X 0).val.obj (op U) :=
  (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))

omit [HasSheafify X.J AddCommGrpCat] [X.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- The unit section restricts to the unit section along any arrow of the site. -/
lemma structureSheafOne_restrict {U V : X.C} (g : V ⟶ U) :
    ((structureSheafComplex X).X 0).val.map g.op (structureSheafOne X U) =
      structureSheafOne X V :=
  PresheafOfModules.unit_map_one (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj g.op

variable
  [HasDerivedCategory.{d} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

/-- The structure sheaf in degree zero, as an object of the derived category of modules. -/
abbrev derivedStructureSheaf :
    DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  DerivedCategory.Q.obj (structureSheafComplex X)

/-- The structure sheaf in degree zero is the image of the structure sheaf under the
degree-zero single functor into the derived category. -/
lemma derivedStructureSheaf_eq_singleFunctor_obj :
    derivedStructureSheaf X =
      (DerivedCategory.singleFunctor
          (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) := rfl

end StructureSheaf

variable (X : RingedSite.{u, u, u})

section Complex

variable {I J : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

/-- The value at the unit section of a degree-`n` section over `U` of the internal Hom complex
out of the structure sheaf. -/
def evalAtOneFun
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n : ℤ) (U : X.C)
    (s : ((sheafHomComplex X (structureSheafComplex X) I).obj.X n).val.obj (op U)) :
    (I.X n).val.obj (op U) :=
  applyHomSection X (sheafHomComplex X (structureSheafComplex X) I) U n 0 n (zero_add n) s
    (structureSheafOne X U)

/-- Evaluation at the unit section is additive. -/
lemma evalAtOneFun_add (n : ℤ) (U : X.C)
    (s t : ((sheafHomComplex X (structureSheafComplex X) I).obj.X n).val.obj (op U)) :
    evalAtOneFun X I n U (s + t) = evalAtOneFun X I n U s + evalAtOneFun X I n U t :=
  applyHomSection_add_left X _ U n 0 n (zero_add n) s t _

/-- Evaluation at the unit section is `O(U)`-linear. -/
lemma evalAtOneFun_smul (n : ℤ) (U : X.C)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))
    (s : ((sheafHomComplex X (structureSheafComplex X) I).obj.X n).val.obj (op U)) :
    evalAtOneFun X I n U (r • s) = r • evalAtOneFun X I n U s :=
  applyHomSection_smul_left X _ U r n 0 n (zero_add n) s _

/-- Evaluation at the unit section commutes with restriction along an arrow of the site. -/
lemma evalAtOneFun_restrict (n : ℤ) {U V : X.C} (g : V ⟶ U)
    (s : ((sheafHomComplex X (structureSheafComplex X) I).obj.X n).val.obj (op U)) :
    evalAtOneFun X I n V (restrictSection X g s) =
      restrictSection X g (evalAtOneFun X I n U s) := by
  rw [evalAtOneFun, ← applyHomSectionOver_restrict, ← structureSheafOne_restrict X g,
    applyHomSectionOver_map, evalAtOneFun]

/-- Evaluation at the unit section commutes with the differentials: the Leibniz rule for the
internal Hom complex, whose correction term vanishes because the structure sheaf complex has
zero differentials. -/
lemma evalAtOneFun_differential (n n' : ℤ) (hnn' : n + 1 = n') (U : X.C)
    (s : ((sheafHomComplex X (structureSheafComplex X) I).obj.X n).val.obj (op U)) :
    evalAtOneFun X I n' U
        (((sheafHomComplex X (structureSheafComplex X) I).obj.d n n').val.app (op U) s) =
      (I.d n n').val.app (op U) (evalAtOneFun X I n U s) := by
  subst hnn'
  have hzero : ((structureSheafComplex X).d 0 (0 + 1)).val.app (op U)
      (structureSheafOne X U) = 0 := by
    rw [show (structureSheafComplex X).d 0 (0 + 1) = 0 from rfl]
    rfl
  have hvanish : applyHomSectionOver X (sheafHomComplex X (structureSheafComplex X) I) U U (𝟙 U)
      n (0 + 1) (n + 1) (by omega) s
      (((structureSheafComplex X).d 0 (0 + 1)).val.app (op U) (structureSheafOne X U)) = 0 := by
    rw [hzero]
    exact map_zero _
  simp only [evalAtOneFun, applyHomSection]
  rw [applyHomSectionOver_differential X _ U U (𝟙 U) n 0 n (n + 1) (zero_add n) rfl s _,
    hvanish, smul_zero, add_zero]

/-- Evaluation at the unit section, in degree `n`, as a morphism of sheaves of modules. -/
def evalAtOneHom
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n : ℤ) :
    (sheafHomComplex X (structureSheafComplex X) I).obj.X n ⟶ I.X n :=
  ⟨{ app := fun U ↦ ModuleCat.ofHom
      { toFun := fun s ↦ evalAtOneFun X I n U.unop s
        map_add' := fun s t ↦ evalAtOneFun_add X n U.unop s t
        map_smul' := fun r s ↦ evalAtOneFun_smul X n U.unop r s }
     naturality := by
       rintro ⟨U⟩ ⟨V⟩ ⟨g : V ⟶ U⟩
       exact ModuleCat.hom_ext (LinearMap.ext fun s ↦ evalAtOneFun_restrict X n g s) }⟩

/-- **Evaluation at the unit section.** The morphism of complexes `SheafHom(O[0], I) ⟶ I` that
sends a homogeneous local section of the internal Hom complex out of the structure sheaf to its
value at the unit section `1`. -/
def structureSheafHomEvaluation
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (sheafHomComplex X (structureSheafComplex X) I).obj ⟶ I where
  f n := evalAtOneHom X I n
  comm' n n' h :=
    SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U ↦ ModuleCat.hom_ext
      (LinearMap.ext fun s ↦ (evalAtOneFun_differential X n n' h U.unop s).symm))

/-- The degreewise components of evaluation at the unit section. -/
lemma structureSheafHomEvaluation_f
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n : ℤ) :
    (structureSheafHomEvaluation X I).f n = evalAtOneHom X I n := rfl

/-- Evaluation at the unit section acts on a homogeneous local section of the internal Hom
complex by evaluating it at the unit section `1`. -/
lemma structureSheafHomEvaluation_apply
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n : ℤ) (U : X.C)
    (s : ((sheafHomComplex X (structureSheafComplex X) I).obj.X n).val.obj (op U)) :
    ((structureSheafHomEvaluation X I).f n).val.app (op U) s =
      applyHomSection X (sheafHomComplex X (structureSheafComplex X) I) U n 0 n (zero_add n) s
        (structureSheafOne X U) :=
  rfl

/-- The degreewise terms of the structure sheaf complex vanish away from degree zero, and so do
their restrictions to a slice site. -/
private lemma isZero_restrictComplex_structureSheafComplex_X (U : X.C) (p : ℤ) (hp : p ≠ 0) :
    IsZero ((restrictComplex X (structureSheafComplex X) U).X p) := by
  have : (SheafOfModules.overFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).PreservesZeroMorphisms :=
    ⟨fun {_ _} ↦ SheafOfModules.hom_ext
      (PresheafOfModules.hom_ext fun _ ↦ ModuleCat.hom_ext (LinearMap.ext fun _ ↦ rfl))⟩
  exact (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).map_isZero
    (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ p hp)

/-- A cochain out of a complex concentrated in degree zero is the single morphism out of that
degree, so taking that component is a bijection. -/
private lemma cochain_v_zero_bijective {A : Type*} [Category A] [Preadditive A]
    (K L : CochainComplex A ℤ) (n : ℤ) (hK : ∀ p : ℤ, p ≠ 0 → IsZero (K.X p)) :
    Function.Bijective (fun z : Cochain K L n ↦ z.v 0 n (zero_add n)) := by
  refine ⟨fun z w h ↦ Cochain.ext _ _ fun p q hpq ↦ ?_,
    fun f ↦ ⟨Cochain.single f n, Cochain.single_v f n (zero_add n)⟩⟩
  by_cases hp : p = 0
  · subst hp
    obtain rfl : q = n := by omega
    exact h
  · exact (hK p hp).eq_of_src _ _

/-- A section of a sheaf of modules on the slice site over `U` is determined by, and can be
prescribed by, its value at the terminal object `𝟙 U` of that site. -/
private lemma over_sections_eval_bijective
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (U : X.C) :
    Function.Bijective
      (fun s : (M.over U).sections ↦
        (s.val (op (Over.mk (𝟙 U))) : M.val.obj (op U))) := by
  refine ⟨fun s t h ↦ PresheafOfModules.sections_ext _ _ fun V ↦ ?_,
    fun (y : M.val.obj (op U)) ↦ ?_⟩
  · have ha : V.unop ⟶ Over.mk (𝟙 U) := Over.homMk V.unop.hom (Category.comp_id _)
    rw [← s.property ha.op, ← t.property ha.op]
    exact congrArg (fun x ↦ (M.over U).val.presheaf.map ha.op x) h
  · refine ⟨PresheafOfModules.sectionsMk (fun V ↦ (M.val.map V.unop.hom.op) y) ?_, ?_⟩
    · intro V W f
      change (M.val.map f.unop.left.op) ((M.val.map V.unop.hom.op) y) =
        (M.val.map W.unop.hom.op) y
      rw [← M.val.map_comp_apply]
      exact M.val.congr_map_apply (by simp only [← op_comp, Over.w]) y
    · change (M.val.presheaf.map (𝟙 (op U))) y = y
      rw [CategoryTheory.Functor.map_id]
      rfl

/-- A morphism out of the free module of rank one on the slice site over `U` is determined by,
and can be prescribed by, its value at the unit section `1`. -/
private lemma structureSheafOver_hom_bijective
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (U : X.C) :
    Function.Bijective
      (fun f : ((structureSheafComplex X).X 0).over U ⟶ M.over U ↦
        f.val.app (op (Over.mk (𝟙 U))) (show _ from structureSheafOne X U)) :=
  (over_sections_eval_bijective X M U).comp (M.over U).unitHomEquiv.bijective

/-- Evaluation at the unit section is bijective on sections over every object of the site. -/
lemma evalAtOneFun_bijective
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) (n : ℤ)
    (U : X.C) : Function.Bijective (evalAtOneFun X I n U) :=
  (structureSheafOver_hom_bijective X (I.X n) U).comp
    ((cochain_v_zero_bijective (restrictComplex X (structureSheafComplex X) U)
        (restrictComplex X I U) n
        (isZero_restrictComplex_structureSheafComplex_X X U)).comp
      (ConcreteCategory.bijective_of_isIso
        (((sheafHomComplex X (structureSheafComplex X) I).sectionsIso U).hom.f n)))

/-- Evaluation at the unit section is an isomorphism in each degree. -/
instance isIso_evalAtOneHom
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n : ℤ) :
    IsIso (evalAtOneHom X I n) := by
  have hcomp (U : X.Cᵒᵖ) : IsIso ((evalAtOneHom X I n).val.app U) :=
    inferInstanceAs (IsIso (LinearEquiv.ofBijective
      (ModuleCat.Hom.hom ((evalAtOneHom X I n).val.app U))
      (evalAtOneFun_bijective X I n U.unop)).toModuleIso.hom)
  have hval : IsIso (evalAtOneHom X I n).val := by
    have ha : (PresheafOfModules.isoMk (fun U ↦ asIso ((evalAtOneHom X I n).val.app U))
        (fun {_ _} g ↦ (evalAtOneHom X I n).val.naturality g)).hom =
        (evalAtOneHom X I n).val :=
      PresheafOfModules.hom_ext fun _ ↦ rfl
    rw [← ha]
    infer_instance
  have : IsIso ((SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map
      (evalAtOneHom X I n)) := hval
  have := (SheafOfModules.fullyFaithfulForget.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).reflectsIsomorphisms
  exact isIso_of_reflects_iso (evalAtOneHom X I n)
    (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- Evaluation at the unit section is an isomorphism of complexes. -/
instance isIso_structureSheafHomEvaluation
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    IsIso (structureSheafHomEvaluation X I) := by
  have h (n : ℤ) : IsIso ((structureSheafHomEvaluation X I).f n) := by
    rw [structureSheafHomEvaluation_f]
    infer_instance
  exact HomologicalComplex.Hom.isIso_of_components _

/-- **Internal Hom out of the structure sheaf is the identity.** Evaluation at the unit section
identifies `SheafHom(O[0], I)` with `I`. -/
def structureSheafHomIso
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (sheafHomComplex X (structureSheafComplex X) I).obj ≅ I :=
  asIso (structureSheafHomEvaluation X I)

/-- The identification of `SheafHom(O[0], I)` with `I` is natural in `I`. -/
lemma structureSheafHomEvaluation_naturality (g : I ⟶ J) :
    homMap X (𝟙 (structureSheafComplex X)) g ≫ structureSheafHomEvaluation X J =
      structureSheafHomEvaluation X I ≫ g := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ SheafOfModules.hom_ext
    (PresheafOfModules.hom_ext fun U ↦ ModuleCat.hom_ext (LinearMap.ext fun s ↦ ?_))
  change ((structureSheafHomEvaluation X J).f n).val.app U
      (((homMap X (𝟙 (structureSheafComplex X)) g).f n).val.app U s) =
    (g.f n).val.app U (((structureSheafHomEvaluation X I).f n).val.app U s)
  rw [structureSheafHomEvaluation_apply, structureSheafHomEvaluation_apply,
    applyHomSection_homMap X (𝟙 (structureSheafComplex X)) g U.unop n 0 n (zero_add n) s _]
  rfl

end Complex

section Derived

variable
  [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

/-- The derived internal Hom out of the structure sheaf into a K-injective complex is the class
of that complex: the K-injective model comparison followed by evaluation at the unit
section. -/
def derivedStructureSheafHomModelIso
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective] :
    ((derivedSheafHomBifunctor X).obj (op (derivedStructureSheaf X))).obj
        (DerivedCategory.Q.obj I) ≅ DerivedCategory.Q.obj I :=
  derivedSheafHomComparison X (structureSheafComplex X) I ≪≫
    DerivedCategory.Q.mapIso (structureSheafHomIso X I)

/-- The identification on K-injective models is natural for morphisms of complexes. -/
private lemma derivedStructureSheafHomModelIso_naturality
    {I J : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [I.IsKInjective] [J.IsKInjective]
    (g : I ⟶ J) :
    ((derivedSheafHomBifunctor X).obj (op (derivedStructureSheaf X))).map
          (DerivedCategory.Q.map g) ≫ (derivedStructureSheafHomModelIso X J).hom =
      (derivedStructureSheafHomModelIso X I).hom ≫ DerivedCategory.Q.map g := by
  have h : ((derivedSheafHomBifunctor X).obj (op (derivedStructureSheaf X))).map
        (DerivedCategory.Q.map g) ≫
        (derivedSheafHomComparison X (structureSheafComplex X) J).hom =
      (derivedSheafHomComparison X (structureSheafComplex X) I).hom ≫
        DerivedCategory.Q.map (homMap X (𝟙 (structureSheafComplex X)) g) := by
    simpa only [CategoryTheory.Functor.map_id, op_id, NatTrans.id_app, Category.id_comp]
      using derivedSheafHomComparison_naturality X (𝟙 (structureSheafComplex X)) g
  dsimp only [derivedStructureSheafHomModelIso, Iso.trans_hom, Functor.mapIso_hom,
    structureSheafHomIso, asIso_hom]
  rw [← Category.assoc]
  refine (congrArg
    (fun φ ↦ φ ≫ DerivedCategory.Q.map (structureSheafHomEvaluation X J)) h).trans ?_
  rw [Category.assoc, ← CategoryTheory.Functor.map_comp,
    structureSheafHomEvaluation_naturality, CategoryTheory.Functor.map_comp, Category.assoc]

/-- The identification on K-injective models is natural for arbitrary morphisms of the derived
category, since every morphism into the class of a K-injective complex is the class of a
morphism of complexes. -/
private lemma derivedStructureSheafHomModelIso_naturality_derived
    {I J : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [I.IsKInjective] [J.IsKInjective]
    (φ : DerivedCategory.Q.obj I ⟶ DerivedCategory.Q.obj J) :
    ((derivedSheafHomBifunctor X).obj (op (derivedStructureSheaf X))).map φ ≫
        (derivedStructureSheafHomModelIso X J).hom =
      (derivedStructureSheafHomModelIso X I).hom ≫ φ := by
  obtain ⟨g, rfl⟩ := exists_Q_map_eq_of_isKInjective X φ
  exact derivedStructureSheafHomModelIso_naturality X g

/-- **Derived internal Hom out of the structure sheaf is the identity.** The identification
`RSheafHom(O[0], Z) ≅ Z`, obtained by transporting the K-injective model identification along
the chosen K-injective representative of `Z`. -/
def derivedStructureSheafHomIso
    (Z : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((derivedSheafHomBifunctor X).obj (op (derivedStructureSheaf X))).obj Z ≅ Z :=
  ((derivedSheafHomBifunctor X).obj (op (derivedStructureSheaf X))).mapIso
      (kInjectiveModelIso X Z).symm ≪≫
    derivedStructureSheafHomModelIso X (kInjectiveModel X Z) ≪≫ kInjectiveModelIso X Z

/-- The identification `RSheafHom(O[0], Z) ≅ Z` is natural in `Z`. -/
lemma derivedStructureSheafHomIso_naturality
    {Z W : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (φ : Z ⟶ W) :
    ((derivedSheafHomBifunctor X).obj (op (derivedStructureSheaf X))).map φ ≫
        (derivedStructureSheafHomIso X W).hom =
      (derivedStructureSheafHomIso X Z).hom ≫ φ := by
  have h := derivedStructureSheafHomModelIso_naturality_derived X
    ((kInjectiveModelIso X Z).hom ≫ φ ≫ (kInjectiveModelIso X W).inv)
  have h' := congrArg (fun ψ ↦
    ((derivedSheafHomBifunctor X).obj (op (derivedStructureSheaf X))).map
      (kInjectiveModelIso X Z).inv ≫ ψ ≫ (kInjectiveModelIso X W).hom) h
  simpa [derivedStructureSheafHomIso, Functor.map_comp, Category.assoc] using h'

/-- On the class of a K-injective complex, the derived identification is the K-injective model
comparison followed by evaluation at the unit section. -/
theorem derivedStructureSheafHomIso_model
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective] :
    (derivedStructureSheafHomIso X (DerivedCategory.Q.obj I)).hom =
      (derivedSheafHomComparison X (structureSheafComplex X) I).hom ≫
        DerivedCategory.Q.map (structureSheafHomEvaluation X I) := by
  dsimp only [derivedStructureSheafHomIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  rw [← Category.assoc, derivedStructureSheafHomModelIso_naturality_derived,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

/-- **The identity functor is the derived internal Hom out of the structure sheaf.** -/
def derivedStructureSheafHomNatIso :
    (derivedSheafHomBifunctor X).obj (op (derivedStructureSheaf X)) ≅
      𝟭 (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :=
  NatIso.ofComponents (derivedStructureSheafHomIso X)
    fun φ ↦ derivedStructureSheafHomIso_naturality X φ

end Derived

end AlgebraicGeometry.RingedSite

end
