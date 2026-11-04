module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSectionRealization
public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleTensorPureSpan
public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleTensorTriangulated
public import StacksFrontier.Algebra.DifferentialGraded.Module.BaseChangeUnitAlgebra
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedPullback

/-!
# Pullback of differential graded modules along a functor of chaotic sites

Let `F : C' ⥤ C` be a functor between categories, both viewed as sites with the chaotic
topology. It is continuous and cocontinuous, so it induces a morphism of topoi
`g : Sh(C') → Sh(C)` whose inverse image is restriction along `F`: `(g⁻¹𝓕)(U') = 𝓕(F U')`
(Sites, Lemma 00XO). Let `O` and `O'` be sheaves of commutative rings on `C` and `C'`, let
`σ : g⁻¹O ⟶ O'` be a map of sheaves of rings and let `φ : g^*A → A'` be a map of differential
graded `O'`-algebras, for sheaves of differential graded algebras `A` on `C` and `A'` on `C'`.
Since `g⁻¹` is restriction along `F`, such a `φ` is the same thing as a family of maps
`A^n(F U') ⟶ A'^n(U')`, natural in `U'`, semilinear over `σ`, and compatible with the
differentials, the multiplications and the units: that is
`SheafOfModules.DifferentialGradedAlgebra.InverseImageHom`.

The pullback of a right differential graded `A`-module `M` is `g^*M = g⁻¹M ⊗_{g⁻¹A} A'`. Every
presheaf being a sheaf for the chaotic topology, its sections over `U'` are
`M(F U') ⊗_{A(F U')} A'(U')`, the relative tensor product of differential graded modules over
the differential graded algebra `A(F U')` of sections, with `A'(U')` an
`(A(F U'), A'(U'))`-bimodule through the homomorphism `A(F U') ⟶ A'(U')` induced by `φ`. This
presheaf of section modules, `pullbackSystem`, is realized as a right differential graded
`A'`-module, `pullbackFunctor`.

## Main definitions

* `SheafOfModules.DifferentialGradedAlgebra.InverseImageHom`: a map `g^*A → A'` of sheaves of
  differential graded algebras along a functor of chaotic sites.
* `SheafOfModules.DifferentialGradedAlgebra.InverseImageHom.sectionHom`: the induced
  homomorphism `A(F U') ⟶ A'(U')` of the differential graded algebras of sections.
* `SheafOfModules.DifferentialGradedModule.pullbackSystem`: the presheaf of section modules
  `U' ↦ M(F U') ⊗_{A(F U')} A'(U')`, and `pullbackSystemFunctor` its functoriality in `M`.
* `SheafOfModules.DifferentialGradedModule.pullbackFunctor`: **the pullback
  `g^* : Mod(A, d) ⥤ Mod(A', d)`**, the realization of that presheaf of section modules.

## Main results

* `SheafOfModules.DifferentialGradedAlgebra.InverseImageHom.sectionHom_sectionRestriction`: the
  homomorphisms of sections are natural.
* `SheafOfModules.DifferentialGradedModule.pullbackSectionsIso`: the sections of `g^*M` over `U'`
  are `M(F U') ⊗_{A(F U')} A'(U')`.

## References

* [Stacks Project, Section 24.33 (Tag 0GZ8)](https://stacks.math.columbia.edu/tag/0GZ8)
* [Stacks Project, Lemma 7.21.1 (Tag 00XO)](https://stacks.math.columbia.edu/tag/00XO)
* [Stacks Project, Section 24.17 (Tag 0FRT)](https://stacks.math.columbia.edu/tag/0FRT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf

universe t m v u v' u'

namespace SheafOfModules

attribute [local instance] GradedAlgebra.sectionsGOne GradedAlgebra.sectionsGMul
  GradedAlgebra.sectionsGRing Stacks.uliftIntAlgebra

variable {C : Type u} [Category.{v} C]
  [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  {C' : Type u'} [Category.{v'} C']
  [(⊥ : GrothendieckTopology C').HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  {Osharp : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{t}}
  {Osharp' : Sheaf (⊥ : GrothendieckTopology C') CommRingCat.{t}}

namespace DifferentialGradedAlgebra

/-- **A map `φ : g^*A → A'` of sheaves of differential graded algebras along a functor
`F : C' ⥤ C` of chaotic sites**, over the map `σ : g⁻¹O ⟶ O'` of sheaves of rings. The inverse
image along the morphism of topoi induced by `F` is restriction along `F`, so `φ` is a family of
maps `A^n(F U') ⟶ A'^n(U')`, natural in `U'`, semilinear over `σ` and compatible with the
differentials, the multiplications and the units. -/
structure InverseImageHom (F : C' ⥤ C)
    (σ : F.op ⋙ (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj ⟶
      (Stacks.SheafOfModules.Tensor.ringSheaf Osharp').obj)
    (A : DifferentialGradedAlgebra.{t, m} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp))
    (A' : DifferentialGradedAlgebra.{t, m} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp')) where
  /-- The map in degree `n` over `U'`. -/
  app (n : ℤ) (U' : C'ᵒᵖ) : (A.complex.X n).val.obj (F.op.obj U') →+ (A'.complex.X n).val.obj U'
  /-- The map is semilinear over `σ`. -/
  app_smul (n : ℤ) (U' : C'ᵒᵖ)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj.obj (F.op.obj U'))
    (x : (A.complex.X n).val.obj (F.op.obj U')) : app n U' (r • x) = σ.app U' r • app n U' x
  /-- The map is natural in `U'`. -/
  naturality (n : ℤ) {U' V' : C'ᵒᵖ} (a : V' ⟶ U') (x : (A.complex.X n).val.obj (F.op.obj V')) :
    app n U' ((A.complex.X n).val.map (F.op.map a) x) = (A'.complex.X n).val.map a (app n V' x)
  /-- The map commutes with the differentials. -/
  app_d (n : ℤ) (U' : C'ᵒᵖ) (x : (A.complex.X n).val.obj (F.op.obj U')) :
    app (n + 1) U' ((A.complex.d n (n + 1)).val.app (F.op.obj U') x) =
      (A'.complex.d n (n + 1)).val.app U' (app n U' x)
  /-- The map is multiplicative. -/
  app_mul (n i : ℤ) (U' : C'ᵒᵖ) (x : (A.complex.X n).val.obj (F.op.obj U'))
    (y : (A.complex.X i).val.obj (F.op.obj U')) :
    app (n + i) U' ((A.mul n i).app (F.op.obj U') x y) =
      (A'.mul n i).app U' (app n U' x) (app i U' y)
  /-- The map preserves the unit. -/
  app_one (U' : C'ᵒᵖ) : app 0 U' (A.one.eval (F.op.obj U')) = A'.one.eval U'

namespace InverseImageHom

variable {F : C' ⥤ C}
  {σ : F.op ⋙ (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj ⟶
    (Stacks.SheafOfModules.Tensor.ringSheaf Osharp').obj}
  {A : DifferentialGradedAlgebra.{t, m} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)}
  {A' : DifferentialGradedAlgebra.{t, m} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp')}
  (φ : InverseImageHom F σ A A')

/-- The map on the rings of sections over `U'`, summand by summand. -/
def sectionRing (U' : C'ᵒᵖ) :
    A.toGradedAlgebra.totalSections (F.op.obj U') →+* A'.toGradedAlgebra.totalSections U' :=
  DirectSum.toSemiring
    (fun n ↦ (DirectSum.of (A'.toGradedAlgebra.sectionsPiece U') n).comp (φ.app n U'))
    (by
      change DirectSum.of (A'.toGradedAlgebra.sectionsPiece U') 0
          (φ.app 0 U' (A.one.eval (F.op.obj U'))) = 1
      rw [φ.app_one U']
      exact DirectSum.of_zero_one _)
    (fun {i j} p q ↦ by
      change DirectSum.of (A'.toGradedAlgebra.sectionsPiece U') (i + j)
          (φ.app (i + j) U' ((A.mul i j).app (F.op.obj U') p q)) = _
      rw [φ.app_mul i j U' p q]
      exact (GradedAlgebra.of_mul_of_eq A'.toGradedAlgebra U' i j _ _).symm)

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  [(⊥ : GrothendieckTopology C').HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- The map on rings of sections sends `x` of degree `n` to `φ x` of degree `n`. -/
@[simp] theorem sectionRing_of (U' : C'ᵒᵖ) (n : ℤ)
    (x : A.toGradedAlgebra.sectionsPiece (F.op.obj U') n) :
    φ.sectionRing U' (DirectSum.of (A.toGradedAlgebra.sectionsPiece (F.op.obj U')) n x) =
      DirectSum.of (A'.toGradedAlgebra.sectionsPiece U') n (φ.app n U' x) :=
  DirectSum.toAddMonoid_of
    (fun n ↦ (DirectSum.of (A'.toGradedAlgebra.sectionsPiece U') n).comp (φ.app n U')) n x

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  [(⊥ : GrothendieckTopology C').HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- The map on rings of sections commutes with the differentials. -/
theorem sectionRing_sectionD (U' : C'ᵒᵖ) (x : A.toGradedAlgebra.totalSections (F.op.obj U')) :
    φ.sectionRing U' (A.sectionD (F.op.obj U') x) = A'.sectionD U' (φ.sectionRing U' x) := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | of n p =>
      rw [sectionD_of, sectionRing_of, sectionRing_of, sectionD_of]
      exact congrArg (DirectSum.of (A'.toGradedAlgebra.sectionsPiece U') (n + 1))
        (φ.app_d n U' p)

/-- **The homomorphism of differential graded algebras of sections** `A(F U') ⟶ A'(U')`
induced by `φ`. -/
def sectionHom (U' : C'ᵒᵖ) : (A.sectionAlgebra (F.op.obj U')).Hom (A'.sectionAlgebra U') where
  toAlgebraHom := Stacks.uliftIntAlgHom (φ.sectionRing U')
  map_grading := by
    rintro n x ⟨p, rfl⟩
    exact ⟨_, (φ.sectionRing_of U' n p).symm⟩
  map_d x := φ.sectionRing_sectionD U' x

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  [(⊥ : GrothendieckTopology C').HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- The homomorphism of sections sends `x` in degree `n` to `φ x` in degree `n`. -/
theorem sectionHom_sectionOf (U' : C'ᵒᵖ) (n : ℤ)
    (x : A.toGradedAlgebra.sectionsPiece (F.op.obj U') n) :
    (φ.sectionHom U').toAlgebraHom (A.sectionOf (F.op.obj U') n x) =
      A'.sectionOf U' n (φ.app n U' x) :=
  φ.sectionRing_of U' n x

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  [(⊥ : GrothendieckTopology C').HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- **The homomorphisms of sections are natural**: they commute with the restriction
homomorphisms of `A` along `F` and of `A'`. -/
theorem sectionHom_sectionRestriction {U' V' : C'ᵒᵖ} (a : V' ⟶ U')
    (x : (A.sectionAlgebra (F.op.obj V')).A) :
    (φ.sectionHom U').toAlgebraHom ((A.sectionRestriction (F.op.map a)).toAlgebraHom x) =
      (A'.sectionRestriction a).toAlgebraHom ((φ.sectionHom V').toAlgebraHom x) := by
  have key : (φ.sectionRing U').comp (A.sectionRestrictRing (F.op.map a)) =
      (A'.sectionRestrictRing a).comp (φ.sectionRing V') := by
    refine DirectSum.ringHom_ext fun n p ↦ ?_
    simp only [RingHom.coe_comp, Function.comp_apply, sectionRestrictRing_of, sectionRing_of]
    exact congrArg (DirectSum.of (A'.toGradedAlgebra.sectionsPiece U') n) (φ.naturality n a p)
  exact DFunLike.congr_fun key x

end InverseImageHom

end DifferentialGradedAlgebra

namespace DifferentialGradedModule


variable {F : C' ⥤ C}
  {σ : F.op ⋙ (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj ⟶
    (Stacks.SheafOfModules.Tensor.ringSheaf Osharp').obj}
  {A : DifferentialGradedAlgebra.{t, m} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)}
  {A' : DifferentialGradedAlgebra.{t, m} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp')}
  (φ : DifferentialGradedAlgebra.InverseImageHom F σ A A')

/-! ### Restriction of sections along a functor -/

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- Restriction of total sections along an identity morphism is the identity. -/
theorem sectionRestrictAdd_id (M : DifferentialGradedModule.{t, m, m} A) (U : Cᵒᵖ)
    (x : M.totalSections U) : M.sectionRestrictAdd (𝟙 U) x = x := by
  refine DFunLike.congr_fun (DirectSum.addHom_ext (g := AddMonoidHom.id _) fun n p ↦ ?_) x
  rw [sectionRestrictAdd_of, sectionRestrictApp_apply, PresheafOfModules.map_id]
  rfl

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- Restriction of total sections along a composite is the composite of the restrictions. -/
theorem sectionRestrictAdd_comp (M : DifferentialGradedModule.{t, m, m} A) {U V W : Cᵒᵖ}
    (a : V ⟶ U) (b : W ⟶ V) (x : M.totalSections W) :
    M.sectionRestrictAdd (b ≫ a) x = M.sectionRestrictAdd a (M.sectionRestrictAdd b x) := by
  refine DFunLike.congr_fun (DirectSum.addHom_ext
    (g := (M.sectionRestrictAdd a).comp (M.sectionRestrictAdd b)) fun n p ↦ ?_) x
  rw [AddMonoidHom.comp_apply, sectionRestrictAdd_of, sectionRestrictAdd_of,
    sectionRestrictAdd_of, sectionRestrictApp_apply, sectionRestrictApp_apply,
    sectionRestrictApp_apply, PresheafOfModules.map_comp_apply]

omit [(⊥ : GrothendieckTopology C').HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- Restriction of the ring of total sections along an identity morphism is the identity. -/
theorem _root_.SheafOfModules.DifferentialGradedAlgebra.sectionRestrictRing_id
    (B : DifferentialGradedAlgebra.{t, m} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp'))
    (U : C'ᵒᵖ) (x : B.toGradedAlgebra.totalSections U) : B.sectionRestrictRing (𝟙 U) x = x := by
  refine DFunLike.congr_fun (DirectSum.ringHom_ext (g := RingHom.id _) fun n p ↦ ?_) x
  rw [DifferentialGradedAlgebra.sectionRestrictRing_of,
    DifferentialGradedAlgebra.sectionRestrictApp_apply, PresheafOfModules.map_id]
  rfl

omit [(⊥ : GrothendieckTopology C').HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- Restriction of the ring of total sections along a composite is the composite of the
restrictions. -/
theorem _root_.SheafOfModules.DifferentialGradedAlgebra.sectionRestrictRing_comp
    (B : DifferentialGradedAlgebra.{t, m} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp'))
    {U V W : C'ᵒᵖ} (a : V ⟶ U) (b : W ⟶ V) (x : B.toGradedAlgebra.totalSections W) :
    B.sectionRestrictRing (b ≫ a) x = B.sectionRestrictRing a (B.sectionRestrictRing b x) := by
  refine DFunLike.congr_fun (DirectSum.ringHom_ext
    (g := (B.sectionRestrictRing a).comp (B.sectionRestrictRing b)) fun n p ↦ ?_) x
  rw [RingHom.comp_apply, DifferentialGradedAlgebra.sectionRestrictRing_of,
    DifferentialGradedAlgebra.sectionRestrictRing_of,
    DifferentialGradedAlgebra.sectionRestrictRing_of,
    DifferentialGradedAlgebra.sectionRestrictApp_apply,
    DifferentialGradedAlgebra.sectionRestrictApp_apply,
    DifferentialGradedAlgebra.sectionRestrictApp_apply, PresheafOfModules.map_comp_apply]

/-- A module structure over the lifted integers is the action of the integers. -/
theorem uliftInt_smul_eq {M : Type*} [AddCommGroup M] (iM : Module (ULift.{m} ℤ) M)
    (c : ULift.{m} ℤ) (x : M) :
    @HSMul.hSMul _ _ _ (@instHSMul _ _ iM.toSMul) c x = c.down • x :=
  @Int.cast_smul_eq_zsmul (ULift.{m} ℤ) M _ _ iM c.down x

/-- A biadditive map between modules over the lifted integers is bilinear, for any module
structures on the three groups. -/
def uliftBilinear {M N P : Type m} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    (iM : Module (ULift.{m} ℤ) M) (iN : Module (ULift.{m} ℤ) N) (iP : Module (ULift.{m} ℤ) P)
    (f : M →+ N →+ P) :=
  letI := iM
  letI := iN
  letI := iP
  LinearMap.mk₂ (ULift.{m} ℤ) (fun x y ↦ f x y)
    (fun x x' y ↦ by rw [map_add, AddMonoidHom.add_apply])
    (fun c x y ↦ by
      rw [uliftInt_smul_eq iM, uliftInt_smul_eq iP, map_zsmul]
      rfl)
    (fun x y y' ↦ map_add (f x) y y')
    (fun c x y ↦ by rw [uliftInt_smul_eq iN, uliftInt_smul_eq iP, map_zsmul])

/-- The bilinear map `uliftBilinear iM iN iP f` evaluates as `f`. -/
theorem uliftBilinear_apply {M N P : Type m} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    (iM : Module (ULift.{m} ℤ) M) (iN : Module (ULift.{m} ℤ) N) (iP : Module (ULift.{m} ℤ) P)
    (f : M →+ N →+ P) (x : M) (y : N) : uliftBilinear iM iN iP f x y = f x y := rfl

/-! ### The presheaf of section modules of the pullback -/

/-- The `(A(F U'), A'(U'))`-bimodule `A'(U')`, through the homomorphism of sections induced by
`φ`. -/
abbrev pullbackBimodule (U' : C'ᵒᵖ) :
    DifferentialGraded.Bimodule (A.sectionAlgebra (F.op.obj U')) (A'.sectionAlgebra U') :=
  DifferentialGraded.Bimodule.regular (φ.sectionHom U')

/-- The sections over `U'` of the pullback of `M`: `M(F U') ⊗_{A(F U')} A'(U')`. -/
abbrev pullbackSections (M : DifferentialGradedModule.{t, m, m} A) (U' : C'ᵒᵖ) :
    _root_.DifferentialGradedModule.{m, m, m} (A'.sectionAlgebra U') :=
  (DifferentialGraded.Bimodule.tensorDGFunctor (pullbackBimodule φ U')).functor.obj
    (M.sectionModule (F.op.obj U'))

/-- An element of `A'(U')`, read in the bimodule `A'(U')`. -/
def regElt (U' : C'ᵒᵖ) (y : (A'.sectionAlgebra U').A) : (pullbackBimodule φ U').rightModule.M := y

/-- An element of the bimodule `A'(U')`, read in `A'(U')`. -/
def algElt (U' : C'ᵒᵖ) (y : (pullbackBimodule φ U').rightModule.M) : (A'.sectionAlgebra U').A := y

/-- The pure tensor `x ⊗ b` of `M(F U') ⊗_{A(F U')} A'(U')`. -/
abbrev pullbackPure (M : DifferentialGradedModule.{t, m, m} A) (U' : C'ᵒᵖ) :=
  ((DifferentialGraded.Bimodule.tensorDGFunctor (pullbackBimodule φ U')).pure
    (M.sectionModule (F.op.obj U'))).toLinearMap

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  [(⊥ : GrothendieckTopology C').HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- The left action of `A(F U')` on `A'(U')` is multiplication through the homomorphism of
sections. -/
theorem pullbackBimodule_action (U' : C'ᵒᵖ) (n q : ℤ)
    (a : (A.sectionAlgebra (F.op.obj U')).grading n)
    (y : (pullbackBimodule φ U').rightModule.grading q) :
    ((show (pullbackBimodule φ U').rightModule.grading (q + n) from
      ((pullbackBimodule φ U').leftAction.1.action n a).v q (q + n) (by omega) y) :
        (pullbackBimodule φ U').rightModule.M) =
      (φ.sectionHom U').toAlgebraHom (a : (A.sectionAlgebra (F.op.obj U')).A) *
        (show (A'.sectionAlgebra U').A from y.1) :=
  _root_.DifferentialGradedModule.regularBimoduleStructure_action (φ.sectionHom U') n q a y

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  [(⊥ : GrothendieckTopology C').HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- For `a : V' ⟶ U'`, `φ(b|_{F a}) · y|_a = (φ(b) · y)|_a` in `A'(U')`. -/
theorem pullbackRestr_mul {U' V' : C'ᵒᵖ} (a : V' ⟶ U') (b : (A.sectionAlgebra (F.op.obj V')).A)
    (y : (A'.sectionAlgebra V').A) :
    (φ.sectionHom U').toAlgebraHom ((A.sectionRestriction (F.op.map a)).toAlgebraHom b) *
        (A'.sectionRestriction a).toAlgebraHom y =
      (A'.sectionRestriction a).toAlgebraHom ((φ.sectionHom V').toAlgebraHom b * y) := by
  rw [map_mul, φ.sectionHom_sectionRestriction]

/-- The bilinear map `(x, b) ↦ x|_{F a} ⊗ b|_a`. -/
def pullbackRestrLinear (M : DifferentialGradedModule.{t, m, m} A) {U' V' : C'ᵒᵖ}
    (a : V' ⟶ U') :=
  uliftBilinear (M.sectionModule (F.op.obj V')).module
    (pullbackBimodule φ V').rightModule.module
    (_root_.DifferentialGradedModule.restrictScalars (A'.sectionRestriction a)
      (pullbackSections φ M U')).module
    (AddMonoidHom.mk' (fun x ↦ AddMonoidHom.mk' (fun y ↦
        pullbackPure φ M U' ((M.sectionModuleRestriction (F.op.map a)).toFun x)
          ((A'.sectionRestriction a).toAlgebraHom y))
        (fun y y' ↦ (congrArg (pullbackPure φ M U'
            ((M.sectionModuleRestriction (F.op.map a)).toFun x))
          (map_add (A'.sectionRestriction a).toAlgebraHom y y')).trans (map_add _ _ _)))
      (fun x x' ↦ AddMonoidHom.ext fun y ↦
        (congrArg (fun z ↦ pullbackPure φ M U' z ((A'.sectionRestriction a).toAlgebraHom y))
          (map_add (M.sectionModuleRestriction (F.op.map a)).toFun x x')).trans
          (congrArg (fun g ↦ g ((A'.sectionRestriction a).toAlgebraHom y))
            (map_add (pullbackPure φ M U') _ _))))

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  [(⊥ : GrothendieckTopology C').HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- The bilinear map `pullbackRestrLinear φ M a` sends `(x, y)` to `x|_{F a} ⊗ y|_a`. -/
theorem pullbackRestrLinear_apply (M : DifferentialGradedModule.{t, m, m} A) {U' V' : C'ᵒᵖ}
    (a : V' ⟶ U') (x : (M.sectionModule (F.op.obj V')).M)
    (y : (pullbackBimodule φ V').rightModule.M) :
    pullbackRestrLinear φ M a x y =
      pullbackPure φ M U' ((M.sectionModuleRestriction (F.op.map a)).toFun x)
        ((A'.sectionRestriction a).toAlgebraHom y) :=
  rfl

/-- The balanced bilinear map `(x, b) ↦ x|_{F a} ⊗ b|_a` out of the sections over `V'`, into the
sections over `U'` read over `A'(V')`. -/
def pullbackRestrBalanced (M : DifferentialGradedModule.{t, m, m} A) {U' V' : C'ᵒᵖ}
    (a : V' ⟶ U') :
    DifferentialGraded.Bimodule.BalancedBilinearMap (M.sectionModule (F.op.obj V'))
      (pullbackBimodule φ V')
      (_root_.DifferentialGradedModule.restrictScalars (A'.sectionRestriction a)
        (pullbackSections φ M U')) where
  toLinearMap := pullbackRestrLinear φ M a
  map_grading p q x y :=
    ((DifferentialGraded.Bimodule.tensorDGFunctor (pullbackBimodule φ U')).pure
      (M.sectionModule (F.op.obj U'))).map_grading p q
      ⟨_, (M.sectionModuleRestriction (F.op.map a)).map_grading p x x.2⟩
      ⟨_, (A'.sectionRestriction a).map_grading q (show (A'.sectionAlgebra V').A from y.1) y.2⟩
  map_d p x y := by
    have h := ((DifferentialGraded.Bimodule.tensorDGFunctor (pullbackBimodule φ U')).pure
      (M.sectionModule (F.op.obj U'))).map_d p
      ⟨_, (M.sectionModuleRestriction (F.op.map a)).map_grading p x x.2⟩
      ((A'.sectionRestriction a).toAlgebraHom y)
    have h1 : (M.sectionModuleRestriction (F.op.map a)).toFun
        ((M.sectionModule (F.op.obj V')).d (x : (M.sectionModule (F.op.obj V')).M)) =
        (M.sectionModule (F.op.obj U')).d
          ((M.sectionModuleRestriction (F.op.map a)).toFun x) :=
      congrArg (fun g ↦ g (x : (M.sectionModule (F.op.obj V')).M))
        (M.sectionModuleRestriction (F.op.map a)).map_d
    have h2 : (A'.sectionRestriction a).toAlgebraHom ((A'.sectionAlgebra V').d y) =
        (A'.sectionAlgebra U').d ((A'.sectionRestriction a).toAlgebraHom y) :=
      (A'.sectionRestriction a).map_d y
    refine h.trans ?_
    change _ = pullbackPure φ M U' ((M.sectionModuleRestriction (F.op.map a)).toFun
        ((M.sectionModule (F.op.obj V')).d (x : (M.sectionModule (F.op.obj V')).M)))
        ((A'.sectionRestriction a).toAlgebraHom y) +
      (p.negOnePow : ℤ) • pullbackPure φ M U' ((M.sectionModuleRestriction (F.op.map a)).toFun x)
        ((A'.sectionRestriction a).toAlgebraHom ((A'.sectionAlgebra V').d y))
    rw [h1, h2]
    rfl
  balance p q n x y b :=
    (congrArg (fun z ↦ pullbackPure φ M U' z
      ((A'.sectionRestriction a).toAlgebraHom (show (A'.sectionAlgebra V').A from y.1)))
      ((M.sectionModuleRestriction (F.op.map a)).map_smul x b)).trans
    ((((DifferentialGraded.Bimodule.tensorDGFunctor (pullbackBimodule φ U')).pure
      (M.sectionModule (F.op.obj U'))).balance p q n
      ⟨_, (M.sectionModuleRestriction (F.op.map a)).map_grading p x x.2⟩
      ⟨_, (A'.sectionRestriction a).map_grading q (show (A'.sectionAlgebra V').A from y.1) y.2⟩
      ⟨_, (A.sectionRestriction (F.op.map a)).map_grading n b b.2⟩).trans
    (congrArg (pullbackPure φ M U' ((M.sectionModuleRestriction (F.op.map a)).toFun x))
      ((pullbackBimodule_action φ U' n q _ _).trans
        ((pullbackRestr_mul φ a b (show (A'.sectionAlgebra V').A from y.1)).trans
          (congrArg (A'.sectionRestriction a).toAlgebraHom
            (pullbackBimodule_action φ V' n q b y).symm)))))
  map_right x y b :=
    (congrArg (pullbackPure φ M U' ((M.sectionModuleRestriction (F.op.map a)).toFun x))
      (map_mul (A'.sectionRestriction a).toAlgebraHom
        (show (A'.sectionAlgebra V').A from y) b)).trans
      (((DifferentialGraded.Bimodule.tensorDGFunctor (pullbackBimodule φ U')).pure
        (M.sectionModule (F.op.obj U'))).map_right _ _ _)

/-- **Extensionality for additive maps out of a relative tensor product**: two additive maps out
of `M ⊗_A N` agreeing on the pure tensors are equal. -/
theorem tensorObj_addHom_ext {B B' : _root_.DifferentialGradedAlgebra (ULift.{m} ℤ)}
    (N : DifferentialGraded.Bimodule B B') (X : _root_.DifferentialGradedModule.{m, m, m} B)
    {P : Type*} [AddCommGroup P]
    (f g : ((DifferentialGraded.Bimodule.tensorDGFunctor N).functor.obj X).M →+ P)
    (h : ∀ (x : X.M) (y : N.rightModule.M),
      f (((DifferentialGraded.Bimodule.tensorDGFunctor N).pure X).toLinearMap x y) =
        g (((DifferentialGraded.Bimodule.tensorDGFunctor N).pure X).toLinearMap x y)) :
    f = g := by
  refine AddMonoidHom.ext fun z ↦ ?_
  have hz : z ∈ DifferentialGraded.Bimodule.pureSpan N X := by
    rw [DifferentialGraded.Bimodule.pureSpan_eq_top]
    trivial
  induction hz using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨p, q, x, y, rfl⟩ := hw
    exact h _ _
  | zero => simp only [map_zero]
  | add w w' _ _ ihw ihw' => simp only [map_add, ihw, ihw']
  | smul r w _ ih =>
    have hr := uliftInt_smul_eq
      ((DifferentialGraded.Bimodule.tensorDGFunctor N).functor.obj X).module r w
    exact (congrArg f hr).trans ((map_zsmul f r.down w).trans
      ((congrArg (fun v ↦ r.down • v) ih).trans ((map_zsmul g r.down w).symm.trans
        (congrArg g hr).symm)))

/-- Two additive maps out of `M ⊗_A N` agreeing on the pure tensors agree on every element. -/
private theorem tensorObj_addHom_apply_ext {B B' : _root_.DifferentialGradedAlgebra (ULift.{m} ℤ)}
    (N : DifferentialGraded.Bimodule B B') (X : _root_.DifferentialGradedModule.{m, m, m} B)
    {P : Type*} [AddCommGroup P]
    (f g : ((DifferentialGraded.Bimodule.tensorDGFunctor N).functor.obj X).M →+ P)
    (h : ∀ (x : X.M) (y : N.rightModule.M),
      f (((DifferentialGraded.Bimodule.tensorDGFunctor N).pure X).toLinearMap x y) =
        g (((DifferentialGraded.Bimodule.tensorDGFunctor N).pure X).toLinearMap x y))
    (z : ((DifferentialGraded.Bimodule.tensorDGFunctor N).functor.obj X).M) : f z = g z :=
  DFunLike.congr_fun (tensorObj_addHom_ext N X f g h) z

/-- **The restriction homomorphism of the pullback** along a morphism `a : V' ⟶ U'` of `C'ᵒᵖ`:
`x ⊗ b ↦ x|_{F a} ⊗ b|_a`, from `M(F V') ⊗ A'(V')` to `M(F U') ⊗ A'(U')` read over `A'(V')`. -/
def pullbackRestr (M : DifferentialGradedModule.{t, m, m} A) {U' V' : C'ᵒᵖ} (a : V' ⟶ U') :
    (pullbackSections φ M V').Hom
      (_root_.DifferentialGradedModule.restrictScalars (A'.sectionRestriction a)
        (pullbackSections φ M U')) :=
  ((DifferentialGraded.Bimodule.tensorDGFunctor (pullbackBimodule φ V')).universal _ _
    (pullbackRestrBalanced φ M a)).choose

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  [(⊥ : GrothendieckTopology C').HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- The restriction homomorphism of the pullback sends `x ⊗ y` to `x|_{F a} ⊗ y|_a`. -/
theorem pullbackRestr_pure (M : DifferentialGradedModule.{t, m, m} A) {U' V' : C'ᵒᵖ}
    (a : V' ⟶ U') (x : (M.sectionModule (F.op.obj V')).M)
    (y : (pullbackBimodule φ V').rightModule.M) :
    (pullbackRestr φ M a).toFun (pullbackPure φ M V' x y) =
      pullbackPure φ M U' ((M.sectionModuleRestriction (F.op.map a)).toFun x)
        (regElt φ U' ((A'.sectionRestriction a).toAlgebraHom (algElt φ V' y))) :=
  ((DifferentialGraded.Bimodule.tensorDGFunctor (pullbackBimodule φ V')).universal _ _
    (pullbackRestrBalanced φ M a)).choose_spec.1 x y

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  [(⊥ : GrothendieckTopology C').HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- The restriction homomorphism of the pullback along an identity morphism is the identity. -/
theorem pullbackRestr_id (M : DifferentialGradedModule.{t, m, m} A) (U' : C'ᵒᵖ)
    (z : (pullbackSections φ M U').M) : (pullbackRestr φ M (𝟙 U')).toFun z = z := by
  refine tensorObj_addHom_apply_ext _ _ (pullbackRestr φ M (𝟙 U')).toFun.toAddMonoidHom
    (AddMonoidHom.id _) (fun x y ↦ ?_) z
  refine (pullbackRestr_pure φ M (𝟙 U') x y).trans ?_
  exact congrArg₂ (fun p q ↦ pullbackPure φ M U' p q)
    ((congrArg (fun f ↦ M.sectionRestrictAdd f x) (F.op.map_id U')).trans
      (sectionRestrictAdd_id M _ x))
    (DifferentialGradedAlgebra.sectionRestrictRing_id A' U' y)

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  [(⊥ : GrothendieckTopology C').HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- The restriction homomorphism of the pullback along a composite is the composite of the
restriction homomorphisms. -/
theorem pullbackRestr_comp (M : DifferentialGradedModule.{t, m, m} A) {U' V' W' : C'ᵒᵖ}
    (a : V' ⟶ U') (b : W' ⟶ V') (z : (pullbackSections φ M W').M) :
    (pullbackRestr φ M (b ≫ a)).toFun z =
      (pullbackRestr φ M a).toFun ((pullbackRestr φ M b).toFun z) := by
  refine tensorObj_addHom_apply_ext _ _ (pullbackRestr φ M (b ≫ a)).toFun.toAddMonoidHom
    ((pullbackRestr φ M a).toFun.toAddMonoidHom.comp
      (pullbackRestr φ M b).toFun.toAddMonoidHom) (fun x y ↦ ?_) z
  refine (pullbackRestr_pure φ M (b ≫ a) x y).trans ?_
  refine Eq.trans ?_ (congrArg (pullbackRestr φ M a).toFun (pullbackRestr_pure φ M b x y)).symm
  refine Eq.trans ?_ (pullbackRestr_pure φ M a _ _).symm
  exact congrArg₂ (fun p q ↦ pullbackPure φ M U' p q)
    ((congrArg (fun f ↦ M.sectionRestrictAdd f x) (F.op.map_comp b a)).trans
      (sectionRestrictAdd_comp M _ _ x))
    (DifferentialGradedAlgebra.sectionRestrictRing_comp A' a b y)

/-- **The presheaf of section modules of the pullback** `g^*M`: over `U'` it is
`M(F U') ⊗_{A(F U')} A'(U')`, with restriction `x ⊗ b ↦ x|_{F a} ⊗ b|_a`. -/
def pullbackSystem (M : DifferentialGradedModule.{t, m, m} A) : SectionSystem A' where
  obj U' := pullbackSections φ M U'
  restr a := pullbackRestr φ M a
  restr_id U' z := pullbackRestr_id φ M U' z
  restr_comp a b z := pullbackRestr_comp φ M a b z

/-- The pullback of a homomorphism on the sections over `U'`: `x ⊗ b ↦ f(x) ⊗ b`. -/
abbrev pullbackSectionsMap {M N : DifferentialGradedModule.{t, m, m} A} (f : M ⟶ N) (U' : C'ᵒᵖ) :
    pullbackSections φ M U' ⟶ pullbackSections φ N U' :=
  (DifferentialGraded.Bimodule.tensorCompFunctor (pullbackBimodule φ U')).map
    (sectionMap f (F.op.obj U'))

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  [(⊥ : GrothendieckTopology C').HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- The pullback of a homomorphism `f` on the sections over `U'` sends `x ⊗ y` to `f(x) ⊗ y`. -/
theorem pullbackSectionsMap_pure {M N : DifferentialGradedModule.{t, m, m} A} (f : M ⟶ N)
    (U' : C'ᵒᵖ) (x : (M.sectionModule (F.op.obj U')).M)
    (y : (pullbackBimodule φ U').rightModule.M) :
    (pullbackSectionsMap φ f U').toFun (pullbackPure φ M U' x y) =
      pullbackPure φ N U' ((sectionMap f (F.op.obj U')).toFun x) y :=
  DifferentialGraded.Bimodule.tensorCompFunctor_map_pure' (pullbackBimodule φ U')
    (sectionMap f (F.op.obj U')) x y

/-- **The pullback of a homomorphism**, as a morphism of presheaves of section modules. -/
def pullbackSystemMap {M N : DifferentialGradedModule.{t, m, m} A} (f : M ⟶ N) :
    pullbackSystem φ M ⟶ pullbackSystem φ N where
  app U' := pullbackSectionsMap φ f U'
  naturality {U' V'} a z := by
    have key : (pullbackRestr φ N a).toFun.toAddMonoidHom.comp
        (pullbackSectionsMap φ f V').toFun.toAddMonoidHom =
        (pullbackSectionsMap φ f U').toFun.toAddMonoidHom.comp
          (pullbackRestr φ M a).toFun.toAddMonoidHom := by
      refine tensorObj_addHom_ext _ _ _ _ fun x y ↦ ?_
      change (pullbackRestr φ N a).toFun ((pullbackSectionsMap φ f V').toFun
          (pullbackPure φ M V' x y)) =
        (pullbackSectionsMap φ f U').toFun ((pullbackRestr φ M a).toFun (pullbackPure φ M V' x y))
      rw [pullbackSectionsMap_pure, pullbackRestr_pure, pullbackRestr_pure,
        pullbackSectionsMap_pure]
      exact congrArg (fun p ↦ pullbackPure φ N U' p
        (regElt φ U' ((A'.sectionRestriction a).toAlgebraHom (algElt φ V' y))))
        (sectionRestrictAdd_sectionMapAdd f (F.op.map a) x)
    exact DFunLike.congr_fun key z

include φ in
/-- **The pullback functor on presheaves of section modules.** -/
def pullbackSystemFunctor : DifferentialGradedModule.{t, m, m} A ⥤ SectionSystem A' where
  obj M := pullbackSystem φ M
  map f := pullbackSystemMap φ f
  map_id M := SectionSystem.hom_ext fun U' ↦ by
    change (DifferentialGraded.Bimodule.tensorCompFunctor (pullbackBimodule φ U')).map
      ((sectionModuleFunctor A (F.op.obj U')).map (𝟙 M)) = 𝟙 _
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  map_comp f g := SectionSystem.hom_ext fun U' ↦ by
    change (DifferentialGraded.Bimodule.tensorCompFunctor (pullbackBimodule φ U')).map
      ((sectionModuleFunctor A (F.op.obj U')).map (f ≫ g)) = _
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
    rfl

/-- **The pullback `g^*M = g⁻¹M ⊗_{g⁻¹A} A'`** of a right differential graded `A`-module along the
morphism of chaotic ringed sites given by `F` and `φ`: the realization of the presheaf of section
modules `U' ↦ M(F U') ⊗_{A(F U')} A'(U')`. -/
def pullbackFunctor (φ : DifferentialGradedAlgebra.InverseImageHom F σ A A') :
    DifferentialGradedModule.{t, m, m} A ⥤ DifferentialGradedModule.{t, m, m} A' :=
  pullbackSystemFunctor φ ⋙ SectionSystem.realizeFunctor A'

/-- **The sections of the pullback**: `(g^*M)(U') ≅ M(F U') ⊗_{A(F U')} A'(U')`. -/
def pullbackSectionsIso (M : DifferentialGradedModule.{t, m, m} A) (U' : C'ᵒᵖ) :
    ((pullbackFunctor φ).obj M).sectionModule U' ≅ pullbackSections φ M U' :=
  (pullbackSystem φ M).sectionsIso U'

/-! ### Homotopies -/

section TensorHomotopy

variable {B B' : _root_.DifferentialGradedAlgebra.{m, m} (ULift.{m} ℤ)}
  (N : DifferentialGraded.Bimodule B B')

/-- A homotopy tensored with a bimodule, as a homogeneous map of degree `-1`. -/
def tensorHomotopyMap {L L' : _root_.DifferentialGradedModule.{m, m, m} B} {f g : L ⟶ L'}
    (H : _root_.DifferentialGradedModule.Homotopy f g) :=
  (DifferentialGraded.Bimodule.tensorDGFunctor N).functor.map
    (_root_.DifferentialGradedModule.homotopyToHomogeneousMap B H)

/-- A homotopy `H` tensored with a bimodule sends `x ⊗ y` to `H(x) ⊗ y`. -/
theorem tensorHomotopyMap_pure {L L' : _root_.DifferentialGradedModule.{m, m, m} B}
    {f g : L ⟶ L'} (H : _root_.DifferentialGradedModule.Homotopy f g) (x : L.M)
    (y : N.rightModule.M) :
    (tensorHomotopyMap N H).1
        (((DifferentialGraded.Bimodule.tensorDGFunctor N).pure L).toLinearMap x y) =
      ((DifferentialGraded.Bimodule.tensorDGFunctor N).pure L').toLinearMap
        (H.toLinearMap x) y :=
  (DifferentialGraded.Bimodule.tensorDGFunctor N).map_pure _ x y

/-- A homomorphism tensored with a bimodule, read through the differential graded functor. -/
abbrev tensorMapFun {L L' : _root_.DifferentialGradedModule.{m, m, m} B} (f : L ⟶ L') :=
  ((DifferentialGraded.Bimodule.tensorDGFunctor N).functor.map
    (_root_.DifferentialGradedModule.cocycleOfHom B f).1).1

/-- A homomorphism `f` tensored with a bimodule sends `x ⊗ y` to `f(x) ⊗ y`. -/
theorem tensorMapFun_pure {L L' : _root_.DifferentialGradedModule.{m, m, m} B} (f : L ⟶ L')
    (x : L.M) (y : N.rightModule.M) :
    tensorMapFun N f (((DifferentialGraded.Bimodule.tensorDGFunctor N).pure L).toLinearMap x y) =
      ((DifferentialGraded.Bimodule.tensorDGFunctor N).pure L').toLinearMap (f.toFun x) y :=
  (DifferentialGraded.Bimodule.tensorDGFunctor N).map_pure _ x y

/-- For a homotopy `H` between `f` and `g`, the tensored maps satisfy
`f ⊗ 1 - g ⊗ 1 = d ∘ (H ⊗ 1) + (H ⊗ 1) ∘ d`. -/
theorem tensorHomotopy_eq {L L' : _root_.DifferentialGradedModule.{m, m, m} B} {f g : L ⟶ L'}
    (H : _root_.DifferentialGradedModule.Homotopy f g)
    (z : ((DifferentialGraded.Bimodule.tensorDGFunctor N).functor.obj L).M) :
    tensorMapFun N f z - tensorMapFun N g z =
      ((DifferentialGraded.Bimodule.tensorDGFunctor N).functor.obj L').d
          ((tensorHomotopyMap N H).1 z) +
        (tensorHomotopyMap N H).1
          (((DifferentialGraded.Bimodule.tensorDGFunctor N).functor.obj L).d z) := by
  let P := (DifferentialGraded.Bimodule.tensorDGFunctor N).pure L
  let P' := (DifferentialGraded.Bimodule.tensorDGFunctor N).pure L'
  let T' := (DifferentialGraded.Bimodule.tensorDGFunctor N).functor.obj L'
  let T := (DifferentialGraded.Bimodule.tensorDGFunctor N).functor.obj L
  let lhs : T.M →+ T'.M := (tensorMapFun N f).toAddMonoidHom - (tensorMapFun N g).toAddMonoidHom
  let rhs : T.M →+ T'.M :=
    T'.d.toAddMonoidHom.comp (tensorHomotopyMap N H).1.toAddMonoidHom +
      (tensorHomotopyMap N H).1.toAddMonoidHom.comp T.d.toAddMonoidHom
  have key : lhs = rhs := by
    refine tensorObj_addHom_ext N L lhs rhs fun x y ↦ ?_
    induction x using DirectSum.Decomposition.inductionOn L.grading with
    | zero => simp only [map_zero, LinearMap.zero_apply]
    | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
    | @homogeneous p x =>
      have h1 : T'.d (P'.toLinearMap (H.toLinearMap (x : L.M)) y) =
          P'.toLinearMap (L'.d (H.toLinearMap (x : L.M))) y +
            ((p - 1).negOnePow : ℤ) • P'.toLinearMap (H.toLinearMap (x : L.M))
              (N.rightModule.d y) :=
        P'.map_d (p - 1) ⟨_, H.map_grading p x x.2⟩ y
      have hsub : ∀ a b : L'.M, P'.toLinearMap (a - b) y =
          P'.toLinearMap a y - P'.toLinearMap b y := fun a b ↦ by
        rw [map_sub]
        rfl
      have hadd : ∀ a b : L'.M, P'.toLinearMap (a + b) y =
          P'.toLinearMap a y + P'.toLinearMap b y := fun a b ↦ by
        rw [map_add]
        rfl
      change tensorMapFun N f (P.toLinearMap x y) - tensorMapFun N g (P.toLinearMap x y) =
        T'.d ((tensorHomotopyMap N H).1 (P.toLinearMap x y)) +
          (tensorHomotopyMap N H).1 (T.d (P.toLinearMap x y))
      rw [tensorMapFun_pure, tensorMapFun_pure, ← hsub, H.homotopy_eq (x : L.M), hadd,
        tensorHomotopyMap_pure, P.map_d p x y,
        map_add, map_zsmul, tensorHomotopyMap_pure, tensorHomotopyMap_pure, h1,
        Int.negOnePow_sub, Int.negOnePow_one, mul_neg, _root_.mul_one, Units.val_neg, neg_smul]
      abel
  exact DFunLike.congr_fun key z

/-- **A homotopy tensored with a bimodule**: `x ⊗ y ↦ h(x) ⊗ y` is a homotopy between the
tensored homomorphisms. -/
def tensorHomotopy {L L' : _root_.DifferentialGradedModule.{m, m, m} B} {f g : L ⟶ L'}
    (H : _root_.DifferentialGradedModule.Homotopy f g) :
    _root_.DifferentialGradedModule.Homotopy
      ((DifferentialGraded.Bimodule.tensorCompFunctor N).map f)
      ((DifferentialGraded.Bimodule.tensorCompFunctor N).map g) where
  toLinearMap :=
    { toFun := (tensorHomotopyMap N H).1
      map_add' := map_add _
      map_smul' := fun b z ↦ (tensorHomotopyMap N H).2.2 b.unop z }
  map_grading n z hz := by
    have h := (tensorHomotopyMap N H).2.1 n z hz
    rwa [← sub_eq_add_neg] at h
  homotopy_eq z := tensorHomotopy_eq N H z

end TensorHomotopy

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- The map on sections of a homotopy commutes with restriction of sections. -/
theorem Homotopy.sectionRestrictAdd_sectionsAdd {M N : DifferentialGradedModule.{t, m, m} A}
    {f g : M ⟶ N} (h : Homotopy f g) {U V : Cᵒᵖ} (a : V ⟶ U) (x : M.totalSections V) :
    N.sectionRestrictAdd a (h.sectionsAdd V x) = h.sectionsAdd U (M.sectionRestrictAdd a x) := by
  refine DFunLike.congr_fun (DirectSum.addHom_ext
    (f := (N.sectionRestrictAdd a).comp (h.sectionsAdd V))
    (g := (h.sectionsAdd U).comp (M.sectionRestrictAdd a)) fun n p ↦ ?_) x
  rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, Homotopy.sectionsAdd_of,
    sectionRestrictAdd_of, sectionRestrictAdd_of, Homotopy.sectionsAdd_of]
  exact congrArg (DirectSum.of (N.sectionsPiece U) (n - 1))
    (PresheafOfModules.naturality_apply (h.app n).val a p).symm

/-- The tensored homotopy `tensorHomotopy N H` sends `x ⊗ y` to `H(x) ⊗ y`. -/
theorem tensorHomotopy_pure {B B' : _root_.DifferentialGradedAlgebra.{m, m} (ULift.{m} ℤ)}
    (N : DifferentialGraded.Bimodule B B') {L L' : _root_.DifferentialGradedModule.{m, m, m} B}
    {f g : L ⟶ L'} (H : _root_.DifferentialGradedModule.Homotopy f g) (x : L.M)
    (y : N.rightModule.M) :
    (tensorHomotopy N H).toLinearMap
        (((DifferentialGraded.Bimodule.tensorDGFunctor N).pure L).toLinearMap x y) =
      ((DifferentialGraded.Bimodule.tensorDGFunctor N).pure L').toLinearMap
        (H.toLinearMap x) y :=
  tensorHomotopyMap_pure N H x y

/-- **The pullback of a homotopy**, as a homotopy of presheaves of section modules: over `U'` it
is the homotopy on sections over `F U'` tensored with `A'(U')`. -/
def pullbackSystemHomotopy {M N : DifferentialGradedModule.{t, m, m} A} {f g : M ⟶ N}
    (h : Homotopy f g) :
    SectionSystem.Homotopy (pullbackSystemMap φ f) (pullbackSystemMap φ g) where
  app U' := tensorHomotopy (pullbackBimodule φ U') (h.sections (F.op.obj U'))
  naturality {U' V'} a z := by
    have key : (pullbackRestr φ N a).toFun.toAddMonoidHom.comp
        (tensorHomotopy (pullbackBimodule φ V')
          (h.sections (F.op.obj V'))).toLinearMap.toAddMonoidHom =
        (tensorHomotopy (pullbackBimodule φ U')
          (h.sections (F.op.obj U'))).toLinearMap.toAddMonoidHom.comp
          (pullbackRestr φ M a).toFun.toAddMonoidHom := by
      refine tensorObj_addHom_ext (pullbackBimodule φ V') (M.sectionModule (F.op.obj V')) _ _
        fun x y ↦ ?_
      change (pullbackRestr φ N a).toFun ((tensorHomotopy (pullbackBimodule φ V')
          (h.sections (F.op.obj V'))).toLinearMap (pullbackPure φ M V' x y)) =
        (tensorHomotopy (pullbackBimodule φ U') (h.sections (F.op.obj U'))).toLinearMap
          ((pullbackRestr φ M a).toFun (pullbackPure φ M V' x y))
      rw [tensorHomotopy_pure, pullbackRestr_pure, pullbackRestr_pure, tensorHomotopy_pure]
      exact congrArg (fun p ↦ pullbackPure φ N U' p
        (regElt φ U' ((A'.sectionRestriction a).toAlgebraHom (algElt φ V' y))))
        (h.sectionRestrictAdd_sectionsAdd (F.op.map a) x)
    exact DFunLike.congr_fun key z

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- **The pullback carries homotopic morphisms to homotopic morphisms.** -/
theorem preservesHomotopic_pullbackFunctor : PreservesHomotopic (pullbackFunctor φ) :=
  fun _ _ ⟨h⟩ ↦ SectionSystem.realizeMap_homotopic (pullbackSystemHomotopy φ h)

end DifferentialGradedModule

end SheafOfModules

end
