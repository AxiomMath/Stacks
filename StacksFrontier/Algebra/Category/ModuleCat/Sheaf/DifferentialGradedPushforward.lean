module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedAxiomA
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedPullback
public import StacksCore.Tactic.StacksAttribute

/-!
# Pull and push for sheaves of differential graded modules

Let `f : (C, J, R) ⟶ (C', J', R')` be a morphism of ringed sites, presented as a functor
`u : C' ⥤ C` in the direction opposite to `f` together with the structure map
`σ : R' ⟶ f_*R` of its sheaves of rings. Let `A` be a sheaf of differential graded `R`-algebras
on the source, let `A'` be a sheaf of differential graded `R'`-algebras on the target and let
`φ : A' ⟶ f_*A`, equivalently `φ : f⁻¹A' ⟶ A`, be a homomorphism of sheaves of differential
graded algebras. The direct image `f_* : Mod^dg(A, d) ⥤ Mod^dg(A', d)` is constructed here: the
underlying complex of `f_*M` is the degreewise direct image of the underlying complex of `M`,
and a homogeneous section `b` of `A'` over `V` acts on a section of `f_*M` over `V`, which is a
section of `M` over `u V`, through `φ b`.

The pullback `f^*` is the one of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedPullback.lean`, pinned by its
universal property. Pullback is left adjoint to the direct image, and in every degree the
homogeneous maps `P ⟶ f_*M` are the homogeneous maps `f^*P ⟶ M`, compatibly with the
differentials of the two Hom complexes.

## Main definitions

* `SheafOfModules.structureMapSheaf` reads the structure map of a morphism of ringed sites as a
  morphism of sheaves of rings, and `SheafOfModules.sitePushforward` is the resulting direct
  image of sheaves of modules.
* `SheafOfModules.semilinearSheafHom` builds a morphism into a direct image out of a degreewise
  additive, semilinear, restriction-compatible family of maps on sections.
* `SheafOfModules.DifferentialGradedModule.pushforwardObj` is the direct image `f_*M` of a right
  differential graded `A`-module, `pushforwardMap` is its action on morphisms and
  `pushforwardFunctor` is the functor `f_* : Mod^dg(A, d) ⥤ Mod^dg(A', d)`.
* `SheafOfModules.DifferentialGradedModule.precompCochain` precomposes a homogeneous cochain out
  of `f^*P` with the unit, giving a homogeneous cochain from `P` into the direct image.
* `SheafOfModules.DifferentialGradedModule.GradedPullbackData` is a pullback of every right
  differential graded `A'`-module whose unit is universal in every degree.

## Main results

* `SheafOfModules.DifferentialGradedModule.semilinearHomEquiv`: a `φ`-semilinear map `P ⟶ M` is
  exactly a morphism `P ⟶ f_*M`, which is what makes the description of a semilinear map as a
  map into the direct image a theorem rather than a reading.
* `SheafOfModules.DifferentialGradedModule.pullbackPushforwardHomEquiv` and
  `pullbackPushforwardAdjunction`: the hom-set identification `Hom(P, f_*M) = Hom(f^*P, M)` and
  the adjunction `f^* ⊣ f_*` it assembles into.
* `SheafOfModules.DifferentialGradedModule.precompCochain_delta`: precomposition with the unit
  commutes with the differential of the Hom complexes.
* `SheafOfModules.DifferentialGradedModule.GradedPullbackData.homogeneousMapEquiv` and
  `delta_homogeneousMapEquiv_symm_val`: the identification of the differential graded Hom
  objects in every degree, and its compatibility with their differentials.

## Implementation notes

The direct image is **constructed**, not pinned by a universal property: the direct image of a
sheaf of modules along a morphism of ringed sites is restriction of sections along `u` with
scalars restricted along `σ`, which is `SheafOfModules.pushforward`, and all of the laws of a
right differential graded module are then inherited from those of `M` at `u V` together with the
five laws of `φ`. In particular the sections of `f_*M` over `V` are the sections of `M` over
`u V` on the nose, which is why every statement below is proved on sections.

The pullback cannot be constructed at this point in the development, for the reasons recorded in
`DifferentialGradedPullback.lean`: the inverse image of a sheaf of differential graded modules
and the tensor product of a right differential graded module with a differential graded bimodule
are both built later, so `f^*P = f⁻¹P ⊗_{f⁻¹A'} A` cannot be written down yet. It is therefore
carried as the hypothesis `PullbackData`, exactly as in that file and in
`DifferentialGradedPullbackTensor.lean`. At a continuous functor of two small sites in one
universe which is representably flat and final that hypothesis is a theorem:
`Stacks.DifferentialGradedPullbackConstruction.pullbackData` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedPullbackAdjunction.lean`.

`PullbackData` characterises `f^*P` through morphisms of differential graded modules only, that
is in degree zero, so it gives the adjunction and the identification of the degree-zero Hom
groups but says nothing about homogeneous maps of other degrees. The universal property of the
unit in **every** degree is what the construction `f^*P = f⁻¹P ⊗_{f⁻¹A'} A` supplies, and it is
carried as the extra datum `GradedPullbackData.homEquiv`.

That datum **is** the identification of the two differential graded Hom objects in every degree,
so `homogeneousMapEquiv` is an abbreviation for it and not a theorem. It is not an extra
assumption: `PullbackData.toGradedPullbackData` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedPushPullHomogeneous.lean` builds
it from the degree-zero universal property alone, by testing that property against the cofree
differential graded module on a shift of `M`, so `GradedPullbackData` is here only as the
interface of the consumers that take it as input. What is proved from the datum is that the
identification is compatible with the differentials of the two Hom complexes: this is the
computation `δ(z ∘ θ) = (δz) ∘ θ` of `precompCochain_delta`, which needs exactly that the unit
`θ` commutes with the differentials. Additivity of the same identification is
`precompCochain_add`.

The homogeneous maps are `DifferentialGradedModule.HomogeneousMap`, the action-linear cochains of
`DifferentialGradedAxiomA.lean`; because that notion is indexed by a ringed site, the two sites
of the last section are ringed sites with their structure sheaves, and their universes agree with
one another since the structure map relates the two sheaves of rings. Everything before that
section is stated for an arbitrary sheaf of rings on an arbitrary site, with the universes of the
two sites, their morphisms, the two algebras and the module sections independent, as in the
neighbouring differential graded files; the two sheaves of rings share the universe `t` because
the structure map relates them, and the module sections of a sheaf and of its direct image share
the universe `m` because `SheafOfModules.pushforward` preserves it.

## References

* [Stacks Project, Tag 0FRU](https://stacks.math.columbia.edu/tag/0FRU)
* [Stacks Project, Tag 0FRI](https://stacks.math.columbia.edu/tag/0FRI)
* [Stacks Project, Tag 0FRF](https://stacks.math.columbia.edu/tag/0FRF)
-/

@[expose] public section

open CategoryTheory

universe t a m v u a' m' v' u' v₀ u₀ z

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {C' : Type u'} [Category.{v'} C'] {J' : GrothendieckTopology C'} {R' : Sheaf J' RingCat.{t}}

/-- The structure map of a morphism of ringed sites, read as a morphism of sheaves of rings. -/
def structureMapSheaf (u : C' ⥤ C) [u.IsContinuous J' J] (σ : R'.obj ⟶ u.op ⋙ R.obj) :
    R' ⟶ (u.sheafPushforwardContinuous RingCat.{t} J' J).obj R :=
  ObjectProperty.homMk σ

/-- The underlying morphism of presheaves of `structureMapSheaf u σ` is `σ`. -/
@[simp]
theorem structureMapSheaf_hom (u : C' ⥤ C) [u.IsContinuous J' J]
    (σ : R'.obj ⟶ u.op ⋙ R.obj) : (structureMapSheaf u σ).hom = σ :=
  rfl

/-- The direct image of sheaves of modules along a morphism of ringed sites: its sections over
`V` are the sections of the original sheaf over `u V`, with scalars restricted along `σ`. -/
noncomputable abbrev sitePushforward (u : C' ⥤ C) [u.IsContinuous J' J]
    (σ : R'.obj ⟶ u.op ⋙ R.obj) : SheafOfModules.{m} R ⥤ SheafOfModules.{m} R' :=
  SheafOfModules.pushforward (structureMapSheaf u σ)

/-- The direct image of sheaves of modules along a morphism of ringed sites is additive. -/
instance sitePushforward_additive (u : C' ⥤ C) [u.IsContinuous J' J]
    (σ : R'.obj ⟶ u.op ⋙ R.obj) :
    (SheafOfModules.pushforward.{m} (structureMapSheaf u σ)).Additive where
  map_add := rfl

/-- A degreewise additive family of maps on sections which is semilinear over the structure map
and compatible with restriction is a morphism into the direct image. -/
noncomputable def semilinearSheafHom {u : C' ⥤ C} [u.IsContinuous J' J]
    {σ : R'.obj ⟶ u.op ⋙ R.obj} {N : SheafOfModules.{m} R'} {T : SheafOfModules.{m} R}
    (g : ∀ V : C'ᵒᵖ, N.val.obj V →+ T.val.obj (u.op.obj V))
    (hsmul : ∀ (V : C'ᵒᵖ) (s : R'.obj.obj V) (x : N.val.obj V),
      g V (s • x) = (σ.app V).hom s • g V x)
    (hnat : ∀ (V W : C'ᵒᵖ) (k : V ⟶ W) (x : N.val.obj V),
      g W (N.val.map k x) = T.val.map (u.op.map k) (g V x)) :
    N ⟶ (sitePushforward u σ).obj T where
  val := PresheafOfModules.homMk
    { app := fun V => AddCommGrpCat.ofHom (g V)
      naturality := fun {V W} k => by ext x; exact hnat V W k x }
    fun V r x => hsmul V r x

/-- On sections over `V`, `semilinearSheafHom g hsmul hnat` is `g V`. -/
@[simp]
theorem semilinearSheafHom_app {u : C' ⥤ C} [u.IsContinuous J' J]
    {σ : R'.obj ⟶ u.op ⋙ R.obj} {N : SheafOfModules.{m} R'} {T : SheafOfModules.{m} R}
    (g : ∀ V : C'ᵒᵖ, N.val.obj V →+ T.val.obj (u.op.obj V)) (hsmul) (hnat) (V : C'ᵒᵖ)
    (x : N.val.obj V) :
    (semilinearSheafHom (σ := σ) g hsmul hnat).val.app V x = g V x :=
  rfl

section Sections

variable {D : Type u₀} [Category.{v₀} D] {K : GrothendieckTopology D} {S : Sheaf K RingCat.{t}}

/-- The map on sections induced by a morphism of sheaves of modules is compatible with integer
scalar multiplication of morphisms. -/
theorem homSections_zsmul {S T : SheafOfModules.{m} R} (k : ℤ) (f : S ⟶ T) (U : Cᵒᵖ)
    (x : S.val.obj U) : homSections (k • f) U x = k • homSections f U x := by
  have hv : (k • f).val = k • f.val := by
    show (SheafOfModules.forget R).map (k • f) = _
    rw [Functor.map_zsmul]
    rfl
  have heval : (k • f.val).app U = k • f.val.app U := by
    show (PresheafOfModules.evaluation R.obj U).map (k • f.val) = _
    rw [Functor.map_zsmul]
    rfl
  show ConcreteCategory.hom ((k • f).val.app U) x = _
  rw [hv, heval]
  simp

/-- A sum of morphisms of sheaves of modules acts on sections as the sum of their actions. -/
theorem sheafHom_add_app {M N : SheafOfModules.{m} S} (f g : M ⟶ N) (U : Dᵒᵖ)
    (x : M.val.obj U) : (f + g).val.app U x = f.val.app U x + g.val.app U x :=
  homSections_add f g U x

/-- A composite of morphisms of sheaves of modules acts on sections as the composite. -/
theorem sheafHom_comp_app {M N T : SheafOfModules.{m} S} (f : M ⟶ N) (g : N ⟶ T) (U : Dᵒᵖ)
    (x : M.val.obj U) : (f ≫ g).val.app U x = g.val.app U (f.val.app U x) :=
  homSections_comp f g U x

/-- A sign multiple of a morphism of sheaves of modules acts on sections by the same sign. -/
theorem sheafHom_units_zsmul_app {M N : SheafOfModules.{m} S} (k : ℤˣ) (f : M ⟶ N) (U : Dᵒᵖ)
    (x : M.val.obj U) : (k • f).val.app U x = k • f.val.app U x := by
  rw [Units.smul_def, Units.smul_def]
  exact homSections_zsmul (k : ℤ) f U x

end Sections

namespace DifferentialGradedModule

variable {u : C' ⥤ C} [u.IsContinuous J' J] {σ : R'.obj ⟶ u.op ⋙ R.obj}
    {A : DifferentialGradedAlgebra.{t, a} R} {A' : DifferentialGradedAlgebra.{t, a'} R'}

/-- The direct image of a right differential graded `A`-module: its underlying complex is the
degreewise direct image, and a homogeneous section `b` of `A'` acts through `φ b`. -/
noncomputable def pushforwardObj
    (φ : DifferentialGradedAlgebra.SemilinearHom u σ A' A)
    (M : DifferentialGradedModule.{t, a, m} A) : DifferentialGradedModule.{t, a', m} A' where
  complex :=
    ((sitePushforward u σ).mapHomologicalComplex (ComplexShape.up ℤ)).obj M.complex
  mul n i :=
    { app := fun V =>
        (AddMonoidHom.compHom' (φ.app i V)).comp ((M.mul n i).app (u.op.obj V))
      map_smul_left := fun V r x b => (M.mul n i).map_smul_left (u.op.obj V) _ x (φ.app i V b)
      map_smul_right := fun V r x b => by
        change (M.mul n i).app (u.op.obj V) x (φ.app i V (r • b)) = _
        rw [φ.map_smul]
        exact (M.mul n i).map_smul_right (u.op.obj V) _ x (φ.app i V b)
      naturality := fun {V W} k x b => by
        change (M.complex.X (n + i)).val.map (u.op.map k)
            ((M.mul n i).app (u.op.obj V) x (φ.app i V b)) =
          (M.mul n i).app (u.op.obj W) ((M.complex.X n).val.map (u.op.map k) x)
            (φ.app i W ((A'.complex.X i).val.map k b))
        rw [(M.mul n i).naturality (u.op.map k) x (φ.app i V b), φ.naturality] }
  mul_assoc := fun n i j V x y z => by
    have h := M.mul_assoc n i j (u.op.obj V) x (φ.app i V y) (φ.app j V z)
    rw [← φ.map_mul] at h
    exact h
  mul_one := fun n V x => by
    have h := M.mul_one n (u.op.obj V) x
    rw [← φ.map_one] at h
    exact h
  leibniz := fun n i V x y => by
    have h := M.leibniz n i (u.op.obj V) x (φ.app i V y)
    rw [← φ.comm_d] at h
    exact h

/-- The degree-`n` term of the direct image `f_* M` is the direct image of the degree-`n` term of
`M`. -/
@[simp]
theorem pushforwardObj_complex_X
    (φ : DifferentialGradedAlgebra.SemilinearHom u σ A' A)
    (M : DifferentialGradedModule.{t, a, m} A) (n : ℤ) :
    (pushforwardObj φ M).complex.X n = (sitePushforward u σ).obj (M.complex.X n) :=
  rfl

/-- A section `b` of `A'` acts on a section `x` of `f_* M` over `V` as `φ b` acts on `x`, viewed as
a section of `M` over `u V`. -/
@[simp]
theorem pushforwardObj_mul_app
    (φ : DifferentialGradedAlgebra.SemilinearHom u σ A' A)
    (M : DifferentialGradedModule.{t, a, m} A) (n i : ℤ) (V : C'ᵒᵖ)
    (x : ((pushforwardObj φ M).complex.X n).val.obj V)
    (b : (A'.complex.X i).val.obj V) :
    ((pushforwardObj φ M).mul n i).app V x b =
      (M.mul n i).app (u.op.obj V) x (φ.app i V b) :=
  rfl

/-- The direct image of a morphism of right differential graded `A`-modules is its degreewise
direct image. -/
noncomputable def pushforwardMap
    (φ : DifferentialGradedAlgebra.SemilinearHom u σ A' A)
    {M N : DifferentialGradedModule.{t, a, m} A} (g : M ⟶ N) :
    pushforwardObj φ M ⟶ pushforwardObj φ N where
  toHomologicalComplex :=
    ((sitePushforward u σ).mapHomologicalComplex (ComplexShape.up ℤ)).map
      g.toHomologicalComplex
  map_mul n i V x b := g.map_mul n i (u.op.obj V) x (φ.app i V b)

/-- The direct image functor `f_* : Mod^dg(A, d) ⥤ Mod^dg(A', d)` on sheaves of differential
graded modules. -/
noncomputable def pushforwardFunctor
    (φ : DifferentialGradedAlgebra.SemilinearHom u σ A' A) :
    DifferentialGradedModule.{t, a, m} A ⥤ DifferentialGradedModule.{t, a', m} A' where
  obj M := pushforwardObj φ M
  map g := pushforwardMap φ g
  map_id M := Hom.ext fun n => (sitePushforward u σ).map_id (M.complex.X n)
  map_comp g g' := Hom.ext fun n =>
    (sitePushforward u σ).map_comp (g.toHomologicalComplex.f n)
      (g'.toHomologicalComplex.f n)

/-- The direct image functor sends `M` to `pushforwardObj φ M`. -/
@[simp]
theorem pushforwardFunctor_obj
    (φ : DifferentialGradedAlgebra.SemilinearHom u σ A' A)
    (M : DifferentialGradedModule.{t, a, m} A) :
    (pushforwardFunctor φ).obj M = pushforwardObj φ M :=
  rfl

/-- The degree-`n` component of the direct image of a morphism `g` is the direct image of the
degree-`n` component of `g`. -/
@[simp]
theorem pushforwardFunctor_map_f
    (φ : DifferentialGradedAlgebra.SemilinearHom u σ A' A)
    {M N : DifferentialGradedModule.{t, a, m} A} (g : M ⟶ N) (n : ℤ) :
    ((pushforwardFunctor φ).map g).toHomologicalComplex.f n =
      (sitePushforward u σ).map (g.toHomologicalComplex.f n) :=
  rfl

section Semilinear

variable {φ : DifferentialGradedAlgebra.SemilinearHom u σ A' A}
    {P : DifferentialGradedModule.{t, a', m} A'} {M : DifferentialGradedModule.{t, a, m} A}

/-- The degree-`i` component of the morphism `P ⟶ f_* M` attached to a `φ`-semilinear map. -/
noncomputable def semilinearComponent (θ : SemilinearHom φ P M) (i : ℤ) :
    P.complex.X i ⟶ (sitePushforward u σ).obj (M.complex.X i) :=
  semilinearSheafHom (fun V => θ.app i V) (θ.map_smul i) fun _ _ k x => θ.naturality i k x

/-- On sections over `V`, `semilinearComponent θ i` is the degree-`i` component of `θ` over `V`. -/
@[simp]
theorem semilinearComponent_app (θ : SemilinearHom φ P M) (i : ℤ) (V : C'ᵒᵖ)
    (x : (P.complex.X i).val.obj V) :
    (semilinearComponent θ i).val.app V x = θ.app i V x :=
  rfl

/-- A `φ`-semilinear map `P ⟶ M` is exactly a morphism `P ⟶ f_* M` of right differential
graded `A'`-modules. -/
noncomputable def semilinearHomEquiv (φ : DifferentialGradedAlgebra.SemilinearHom u σ A' A)
    (P : DifferentialGradedModule.{t, a', m} A') (M : DifferentialGradedModule.{t, a, m} A) :
    SemilinearHom φ P M ≃ (P ⟶ pushforwardObj φ M) where
  toFun θ :=
    { toHomologicalComplex :=
        { f := fun i => semilinearComponent θ i
          comm' := fun i j hij => by
            obtain rfl : i + 1 = j := hij
            ext V x
            exact (θ.comm_d i V x).symm }
      map_mul := fun n i V x b => θ.map_mul n i V x b }
  invFun h :=
    { app := fun i V => homSections (h.toHomologicalComplex.f i) V
      map_smul := fun i V s x => (h.toHomologicalComplex.f i).val.app V |>.hom.map_smul s x
      naturality := fun i {V W} k x =>
        PresheafOfModules.naturality_apply (h.toHomologicalComplex.f i).val k x
      comm_d := fun i V x => hom_comm_d_app h i V x
      map_mul := fun n i V x b => h.map_mul n i V x b }
  left_inv θ := SemilinearHom.ext fun _ _ _ => rfl
  right_inv h := Hom.ext fun i => by
    ext V x
    rfl

/-- On sections over `V`, the degree-`i` component of the morphism attached to `θ` is the
degree-`i` component of `θ` over `V`. -/
@[simp]
theorem semilinearHomEquiv_apply_f (θ : SemilinearHom φ P M) (i : ℤ) (V : C'ᵒᵖ)
    (x : (P.complex.X i).val.obj V) :
    ((semilinearHomEquiv φ P M θ).toHomologicalComplex.f i).val.app V x = θ.app i V x :=
  rfl

/-- The degree-`i` component over `V` of the semilinear map attached to a morphism `h` is the
action of `h` on sections over `V` in degree `i`. -/
@[simp]
theorem semilinearHomEquiv_symm_apply_app (h : P ⟶ pushforwardObj φ M) (i : ℤ) (V : C'ᵒᵖ)
    (x : (P.complex.X i).val.obj V) :
    ((semilinearHomEquiv φ P M).symm h).app i V x =
      (h.toHomologicalComplex.f i).val.app V x :=
  rfl

end Semilinear

section Cochains

open CochainComplex.HomComplex

variable {φ : DifferentialGradedAlgebra.SemilinearHom u σ A' A}
    {P : DifferentialGradedModule.{t, a', m} A'}
    {Q M : DifferentialGradedModule.{t, a, m} A}

/-- Precomposition of a homogeneous cochain out of `Q` with a `φ`-semilinear map `P ⟶ Q`: a
homogeneous cochain of the same degree from `P` into the direct image of `M`. -/
noncomputable def precompCochain (θ : SemilinearHom φ P Q) {n : ℤ}
    (z : Cochain Q.complex M.complex n) :
    Cochain P.complex (pushforwardObj φ M).complex n :=
  Cochain.mk fun p q h =>
    semilinearSheafHom (σ := σ)
      (fun V => (homSections (z.v p q h) (u.op.obj V)).comp (θ.app p V))
      (fun V s x => by
        change homSections (z.v p q h) (u.op.obj V) (θ.app p V (s • x)) = _
        rw [θ.map_smul]
        exact homSections_smul _ _ _ _)
      (fun V W k x => by
        change homSections (z.v p q h) (u.op.obj W)
          (θ.app p W ((P.complex.X p).val.map k x)) = _
        rw [θ.naturality]
        exact (homSections_naturality (z.v p q h) (u.op.map k) (θ.app p V x)).symm)

/-- On sections over `V`, the component of `precompCochain θ z` from degree `p` to degree `q` is
the component of `z` over `u V` precomposed with the degree-`p` component of `θ`. -/
@[simp]
theorem precompCochain_v_app (θ : SemilinearHom φ P Q) {n : ℤ}
    (z : Cochain Q.complex M.complex n) (p q : ℤ) (h : p + n = q) (V : C'ᵒᵖ)
    (x : (P.complex.X p).val.obj V) :
    ((precompCochain θ z).v p q h).val.app V x =
      (z.v p q h).val.app (u.op.obj V) (θ.app p V x) :=
  rfl

/-- Precomposition with a `φ`-semilinear map is additive. -/
theorem precompCochain_add (θ : SemilinearHom φ P Q) {n : ℤ}
    (z z' : Cochain Q.complex M.complex n) :
    precompCochain θ (z + z') = precompCochain θ z + precompCochain θ z' := by
  refine Cochain.ext _ _ fun p q hpq => ?_
  ext V x
  simp only [Cochain.add_v, sheafHom_add_app, precompCochain_v_app]
  rfl

/-- Precomposition with a `φ`-semilinear map commutes with the differential of the Hom
complexes: this is the compatibility with differentials behind the adjunction. -/
theorem precompCochain_delta (θ : SemilinearHom φ P Q) {n m : ℤ} (hnm : n + 1 = m)
    (z : Cochain Q.complex M.complex n) :
    precompCochain θ (δ n m z) = δ n m (precompCochain θ z) := by
  refine Cochain.ext _ _ fun p q hpq => ?_
  ext V x
  rw [δ_v n m hnm (precompCochain θ z) p q hpq (q - 1) (p + 1) rfl rfl,
    precompCochain_v_app, δ_v n m hnm z p q hpq (q - 1) (p + 1) rfl rfl]
  simp only [sheafHom_add_app, sheafHom_units_zsmul_app, sheafHom_comp_app,
    precompCochain_v_app]
  rw [θ.comm_d p V x]
  rfl

end Cochains

section Adjunction

variable {φ : DifferentialGradedAlgebra.SemilinearHom u σ A' A}

/-- The hom-set identification `Hom(N, f_* M) = Hom(f^* N, M)` of the pullback–direct image
adjunction, for a pullback datum for `φ`. -/
noncomputable def pullbackPushforwardHomEquiv (P : PullbackData φ)
    (N : DifferentialGradedModule.{t, a', m} A') (M : DifferentialGradedModule.{t, a, m} A) :
    (P.functor.obj N ⟶ M) ≃ (N ⟶ (pushforwardFunctor φ).obj M) :=
  ((P.isPullback N).homEquiv M).trans (semilinearHomEquiv φ N M)

/-- The pullback of sheaves of differential graded modules is left adjoint to the direct
image. -/
noncomputable def pullbackPushforwardAdjunction (P : PullbackData φ) :
    P.functor ⊣ pushforwardFunctor.{t, a, m} φ :=
  Adjunction.mkOfHomEquiv
    { homEquiv := pullbackPushforwardHomEquiv P
      homEquiv_naturality_left_symm := fun {N' N M} f g => by
        change (P.isPullback N').desc ((semilinearHomEquiv φ N' M).symm (f ≫ g)) =
          P.map f ≫ (P.isPullback N).desc ((semilinearHomEquiv φ N M).symm g)
        refine ((P.isPullback N').uniq _ _ ?_).symm
        rw [SemilinearHom.postcomp_comp, P.unit_postcomp_map, SemilinearHom.precomp_postcomp,
          (P.isPullback N).fac]
        exact SemilinearHom.ext fun _ _ _ => rfl
      homEquiv_naturality_right := fun {N M M'} f g => Hom.ext fun i => by
        ext V x
        rfl }

end Adjunction

end DifferentialGradedModule

end SheafOfModules

namespace SheafOfModules.DifferentialGradedModule

open AlgebraicGeometry CochainComplex.HomComplex

variable {X X' : RingedSite.{z, z, z}} {u : X'.C ⥤ X.C} [u.IsContinuous X'.J X.J]
    {σ : (Stacks.SheafOfModules.Tensor.ringSheaf X'.O).obj ⟶
      u.op ⋙ (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj}
    {A : DifferentialGradedAlgebra.{z, a} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    {A' : DifferentialGradedAlgebra.{z, a'} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)}

/-- A pullback of every right differential graded `A'`-module together with the universal
property of its unit in every degree: precomposition with the unit identifies the homogeneous
`A`-linear maps out of `f^*P` with the homogeneous `A'`-linear maps from `P` into `f_*M`.
Nothing here mentions the differentials of the two Hom complexes. -/
structure GradedPullbackData (φ : DifferentialGradedAlgebra.SemilinearHom u σ A' A) where
  /-- The pullback of a right differential graded `A'`-module. -/
  obj (P : DifferentialGradedModule.{z, a', m} A') : DifferentialGradedModule.{z, a, m} A
  /-- The unit, a `φ`-semilinear map from a module to its pullback. -/
  unit (P : DifferentialGradedModule.{z, a', m} A') : SemilinearHom φ P (obj P)
  /-- Precomposition with the unit is bijective in every degree. -/
  homEquiv (P : DifferentialGradedModule.{z, a', m} A')
      (M : DifferentialGradedModule.{z, a, m} A) (n : ℤ) :
    HomogeneousMap A (obj P) M n ≃ HomogeneousMap A' P (pushforwardObj φ M) n
  /-- The bijection is precomposition with the unit. -/
  homEquiv_val (P : DifferentialGradedModule.{z, a', m} A')
      (M : DifferentialGradedModule.{z, a, m} A) (n : ℤ)
      (w : HomogeneousMap A (obj P) M n) :
    (homEquiv P M n w).val = precompCochain (unit P) w.val

namespace GradedPullbackData

variable {φ : DifferentialGradedAlgebra.SemilinearHom u σ A' A}
    (GP : GradedPullbackData φ)
    (P : DifferentialGradedModule.{z, a', m} A')
    (M : DifferentialGradedModule.{z, a, m} A) (n : ℤ)

/-- Pull and push for sheaves of differential graded modules: the homogeneous maps of degree `n`
from `P` to `f_* M` are the homogeneous maps of degree `n` from `f^* P` to `M`. -/
noncomputable def homogeneousMapEquiv :
    HomogeneousMap A' P (pushforwardObj φ M) n ≃ HomogeneousMap A (GP.obj P) M n :=
  (GP.homEquiv P M n).symm

/-- The identification of the Hom complexes is precomposition with the unit of the pullback. -/
theorem homogeneousMapEquiv_symm_val (w : HomogeneousMap A (GP.obj P) M n) :
    ((GP.homogeneousMapEquiv P M n).symm w).val = precompCochain (GP.unit P) w.val :=
  GP.homEquiv_val P M n w

/-- The identification of the Hom complexes is compatible with their differentials. -/
theorem delta_homogeneousMapEquiv_symm_val (w : HomogeneousMap A (GP.obj P) M n) :
    δ n (n + 1) (((GP.homogeneousMapEquiv P M n).symm w).val) =
      precompCochain (GP.unit P) (δ n (n + 1) w.val) := by
  rw [GP.homogeneousMapEquiv_symm_val P M n w,
    ← precompCochain_delta (GP.unit P) rfl w.val]

/-- The identification of the Hom complexes carries the differential of a homogeneous map to the
differential of its image. -/
theorem homogeneousMapEquiv_symm_val_of_delta (w : HomogeneousMap A (GP.obj P) M n)
    (w' : HomogeneousMap A (GP.obj P) M (n + 1)) (hw : w'.val = δ n (n + 1) w.val) :
    ((GP.homogeneousMapEquiv P M (n + 1)).symm w').val =
      δ n (n + 1) (((GP.homogeneousMapEquiv P M n).symm w).val) := by
  rw [GP.delta_homogeneousMapEquiv_symm_val P M n w,
    GP.homogeneousMapEquiv_symm_val P M (n + 1) w', hw]

end GradedPullbackData

end SheafOfModules.DifferentialGradedModule

end
