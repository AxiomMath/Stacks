module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedPushPullHomogeneous
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedToposPullbackAdjunction
public import
  StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedToposPushforwardSheafHomExact

/-!
# Pull and push for sheaves of differential graded modules on ringed topoi: the Hom complexes

Let `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi, let `A` be a sheaf of
differential graded `O_C`-algebras, let `B` be a sheaf of differential graded `O_D`-algebras and
let `φ : B ⟶ f_*A` be a unital homomorphism of sheaves of differential graded `O_D`-algebras (the
datum of Tag 0FRT, in the form `B ⟶ f_*A` of Remark 0FRG). Write `f^*N = f^*N ⊗_{f^*B} A` for the
pullback `toposPullbackDg f φ hφ`, which is `toposBaseChangeFunctor f φ hφ`, and `f_*` for the
direct image `toposPushforwardDg f φ hφ`, which is `toposPushforward (toposDirectImageModules f) φ
hφ`. This file proves Tag 0FRU: the differential graded Hom objects

`Hom_{Mod^dg(B, d)}(N, f_*M) = Hom_{Mod^dg(A, d)}(f^*N, M)`

agree. In every degree `n` the homogeneous right-linear maps `f^*N ⟶ M` of degree `n` correspond
to those `N ⟶ f_*M` of degree `n`, by `w ↦ η_N ∘ f_*(w)`, where `η` is the unit of the
adjunction `f^* ⊣ f_*` (`toposBaseChangeAdjunction`) and `f_*(w)` is the direct image of `w` as a
homogeneous map (`toposPushforwardConcreteDGFunctor`); the correspondence is additive, commutes
with the differentials of the two Hom complexes, is natural in `N` and in `M`, and is the hom-set
bijection of `f^* ⊣ f_*` on morphisms.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.cofreeHomogeneousCounit`: the degree-`n` homogeneous
  map `Cofree(M[n]) ⟶ M` corresponding to the identity of the cofree module.
* `SheafOfModules.DifferentialGradedModule.toposCofreeShiftIso`: the direct image of the cofree
  module on `M[n]` is the cofree module on `(f_*M)[n]`.
* `SheafOfModules.DifferentialGradedModule.toposPullbackPushforwardHomogeneousEquiv`: the
  identification of the degree-`n` pieces of the two Hom complexes.

## Main results

* `SheafOfModules.DifferentialGradedModule.toposCochain_toposPullbackPushforwardHomogeneousEquiv`:
  the identification is `w ↦ η_N ∘ f_*(w)`.
* `SheafOfModules.DifferentialGradedModule.exists_toposPullbackPushforwardHomEquiv`: **Tag
  0FRU** for a morphism of ringed topoi.

## Implementation notes

The degreewise bijection is obtained from the adjunction `f^* ⊣ f_*` on morphisms through the
cofree modules: a homogeneous map of degree `n` into `M` is a morphism into the cofree module on
the shift `M[n]` (`homogeneousMapEquivCofree`), and the direct image of that cofree module is the
cofree module on `(f_*M)[n]`, the comparison being in each degree the additivity comparison
`f_*(P ⊞ Q) ≅ f_*P ⊞ f_*Q`. The comparison morphism itself is the cofree transpose of the direct
image of the homogeneous counit, so its right linearity comes from that of the direct image of
homogeneous maps.

The functors `f^*` and `f_*` and the adjunction between them are restated as
`toposPullbackDg`, `toposPushforwardDg` and `toposPullbackPushforwardAdjunction`, definitionally
`toposBaseChangeFunctor`, `toposPushforward` and `toposBaseChangeAdjunction`: as named constants
they are compared by name rather than by unfolding their large bodies.

The sites are taken in a common universe `u` with `Category.{u}`, the morphisms of a Stacks site
forming sets, as in `toposPushforwardConcreteDGFunctor`.

## References

* [Stacks Project, Tag 0FRU](https://stacks.math.columbia.edu/tag/0FRU)
* [Stacks Project, Tag 0FRT](https://stacks.math.columbia.edu/tag/0FRT)
* [Stacks Project, Tag 0FRG](https://stacks.math.columbia.edu/tag/0FRG)
* [Stacks Project, Tag 0FR8](https://stacks.math.columbia.edu/tag/0FR8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf CochainComplex.HomComplex
open Stacks.Sheaves.RingedToposModules

universe u

namespace SheafOfModules.DifferentialGradedModule

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory
  AlgebraicGeometry.RingedTopos.hasSheafCompose_forget₂_ringCat

/-- Two composites of morphisms of cochain complexes which agree give the same cochain when
followed by a cochain. -/
theorem cochain_ofHom_comp_ofHom_comp {C : Type*} [Category C] [Preadditive C]
    {K L L' P Q : CochainComplex C ℤ} {n : ℤ} {a : K ⟶ L} {b : L ⟶ P} {c : K ⟶ L'} {d : L' ⟶ P}
    (h : a ≫ b = c ≫ d) (z : Cochain P Q n) :
    (Cochain.ofHom a).comp ((Cochain.ofHom b).comp z (zero_add n)) (zero_add n) =
      (Cochain.ofHom c).comp ((Cochain.ofHom d).comp z (zero_add n)) (zero_add n) := by
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.comp_assoc_of_first_is_zero_cochain,
    ← Cochain.ofHom_comp, ← Cochain.ofHom_comp, h]

/-- For an adjunction `L ⊣ R` and an isomorphism `R.obj Y ≅ Z`, the bijection
`(L.obj X ⟶ Y) ≃ (X ⟶ Z)`: transposition followed by the isomorphism. -/
def adjunctionHomEquivComp {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) (X : C) {Y : D} {Z : C} (e : R.obj Y ≅ Z) : (L.obj X ⟶ Y) ≃ (X ⟶ Z) :=
  (adj.homEquiv X Y).trans
    { toFun := fun g => g ≫ e.hom
      invFun := fun g => g ≫ e.inv
      left_inv := fun g => by simp
      right_inv := fun g => by simp }

/-- The bijection `adjunctionHomEquivComp` is the unit, the right adjoint and the isomorphism. -/
theorem adjunctionHomEquivComp_apply {C D : Type*} [Category C] [Category D] {L : C ⥤ D}
    {R : D ⥤ C} (adj : L ⊣ R) (X : C) {Y : D} {Z : C} (e : R.obj Y ≅ Z) (k : L.obj X ⟶ Y) :
    adjunctionHomEquivComp adj X e k = adj.unit.app X ≫ R.map k ≫ e.hom := by
  simp [adjunctionHomEquivComp, Adjunction.homEquiv_unit]

/-! ### Homogeneous maps as morphisms into a cofree module -/

section Counit

variable {X : AlgebraicGeometry.RingedTopos.{u, u, u}}
  {A : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O)}

/-- The underlying cochain of a homogeneous right-linear map over a ringed topos; it is
`w.val`. -/
def toposCochain {Q M : DifferentialGradedModule.{u, u, u} A} {n : ℤ}
    (w : HomogeneousMap (X := X.toRingedSite) A Q M n) : Cochain Q.complex M.complex n :=
  w.val

/-- A homogeneous right-linear map over a ringed topos is determined by its underlying
cochain. -/
theorem toposCochain_injective {Q M : DifferentialGradedModule.{u, u, u} A} {n : ℤ}
    {w w' : HomogeneousMap (X := X.toRingedSite) A Q M n} (h : toposCochain w = toposCochain w') :
    w = w' :=
  Subtype.ext h

/-- The underlying graded module of a right differential graded module over a ringed topos,
shifted by `n`. -/
abbrev toposShiftForget (M : DifferentialGradedModule.{u, u, u} A) (n : ℤ) :
    GradedModule.{u, u, u} A.toGradedAlgebra :=
  ((forgetToGradedModule A).obj M).shift n

/-- The morphism into the cofree module on `M[n]` attached to a degree-`n` homogeneous
right-linear map into `M`; this is `homogeneousMapEquivCofree` at the site of the ringed topos. -/
def toposCofreeOfHomogeneous {Q M : DifferentialGradedModule.{u, u, u} A} {n : ℤ}
    (w : HomogeneousMap (X := X.toRingedSite) A Q M n) :
    Q ⟶ Cofree.cofree (toposShiftForget M n) :=
  homogeneousMapEquivCofree (Y := X.toRingedSite) A Q M n w

/-- The degree-`n` homogeneous right-linear map into `M` attached to a morphism into the cofree
module on `M[n]`, inverse to `toposCofreeOfHomogeneous`. -/
def toposHomogeneousOfCofree {Q M : DifferentialGradedModule.{u, u, u} A} {n : ℤ}
    (g : Q ⟶ Cofree.cofree (toposShiftForget M n)) :
    HomogeneousMap (X := X.toRingedSite) A Q M n :=
  (homogeneousMapEquivCofree (Y := X.toRingedSite) A Q M n).symm g

/-- `toposHomogeneousOfCofree` is a left inverse of `toposCofreeOfHomogeneous`. -/
theorem toposHomogeneousOfCofree_toposCofreeOfHomogeneous
    {Q M : DifferentialGradedModule.{u, u, u} A} {n : ℤ}
    (w : HomogeneousMap (X := X.toRingedSite) A Q M n) :
    toposHomogeneousOfCofree (toposCofreeOfHomogeneous w) = w :=
  (homogeneousMapEquivCofree (Y := X.toRingedSite) A Q M n).symm_apply_apply w

/-- `toposHomogeneousOfCofree` is a right inverse of `toposCofreeOfHomogeneous`. -/
theorem toposCofreeOfHomogeneous_toposHomogeneousOfCofree
    {Q M : DifferentialGradedModule.{u, u, u} A} {n : ℤ}
    (g : Q ⟶ Cofree.cofree (toposShiftForget M n)) :
    toposCofreeOfHomogeneous (toposHomogeneousOfCofree g) = g :=
  (homogeneousMapEquivCofree (Y := X.toRingedSite) A Q M n).apply_symm_apply g

/-- The component from degree `p` to degree `p + n` of the homogeneous map attached to
`g : Q ⟶ Cofree(M[n])` is `g` followed by the first coordinate. -/
theorem toposCochain_toposHomogeneousOfCofree_v {Q M : DifferentialGradedModule.{u, u, u} A}
    {n : ℤ} (g : Q ⟶ Cofree.cofree (toposShiftForget M n)) (p : ℤ) :
    (toposCochain (toposHomogeneousOfCofree g)).v p (p + n) rfl =
      g.toHomologicalComplex.f p ≫ cofreeFstHom (toposShiftForget M n) p := by
  change (g.toHomologicalComplex.f p ≫ cofreeFstHom (toposShiftForget M n) p) ≫
      degCastHom M.complex.X (rfl : p + n = p + n) = _
  rw [degCastHom_rfl]
  exact Category.comp_id _

/-- **The homogeneous counit of the cofree module on a shift**: the degree-`n` homogeneous
right-linear map `Cofree(M[n]) ⟶ M` corresponding to the identity of `Cofree(M[n])`. -/
def cofreeHomogeneousCounit (M : DifferentialGradedModule.{u, u, u} A) (n : ℤ) :
    HomogeneousMap (X := X.toRingedSite) A (Cofree.cofree (toposShiftForget M n)) M n :=
  toposHomogeneousOfCofree (X := X) (A := A) (𝟙 _)

/-- The component of the homogeneous counit from degree `p` to degree `p + n` is the first
coordinate. -/
theorem cofreeHomogeneousCounit_v (M : DifferentialGradedModule.{u, u, u} A) (n p : ℤ) :
    (toposCochain (cofreeHomogeneousCounit M n)).v p (p + n) rfl =
      cofreeFstHom (toposShiftForget M n) p := by
  refine (toposCochain_toposHomogeneousOfCofree_v (𝟙 _) p).trans ?_
  rw [id_f]
  exact Category.id_comp _

/-- **Every homogeneous map into `M` factors through the homogeneous counit**: the homogeneous map
attached to a morphism `g : Q ⟶ Cofree(M[n])` is `g` followed by the homogeneous counit. -/
theorem toposCochain_toposHomogeneousOfCofree {Q M : DifferentialGradedModule.{u, u, u} A}
    {n : ℤ} (g : Q ⟶ Cofree.cofree (toposShiftForget M n)) :
    toposCochain (toposHomogeneousOfCofree g) =
      (Cochain.ofHom g.toHomologicalComplex).comp (toposCochain (cofreeHomogeneousCounit M n))
        (zero_add n) := by
  refine Cochain.ext _ _ fun p q hpq => ?_
  subst hpq
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, toposCochain_toposHomogeneousOfCofree_v]
  exact congrArg (g.toHomologicalComplex.f p ≫ ·) (cofreeHomogeneousCounit_v M n p).symm

end Counit

/-! ### The direct image of a cofree module on a shift -/

section Topos

variable {X Y : AlgebraicGeometry.RingedTopos.{u, u, u}} (f : RingedToposHom X Y)
  {A : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O)}
  {B : DifferentialGradedAlgebra.{u, u} (toRingCat Y.J Y.O)}
  (φ : B ⟶ toposPushforwardAlgebra (Osharp := X.O) (Psharp := Y.O)
    (toposDirectImageModules (X := X) (Y := Y) f) A) (hφ : φ.IsUnital)

/-- **The pullback `f^*N = f^*N ⊗_{f^*B} A`** of right differential graded modules along `f` and
`φ`; it is `toposBaseChangeFunctor f φ hφ`. -/
def toposPullbackDg : DifferentialGradedModule.{u, u, u} B ⥤ DifferentialGradedModule.{u, u, u} A :=
  toposBaseChangeFunctor f φ hφ

/-- **The direct image `f_*`** of right differential graded modules along `f` and `φ`; it is
`toposPushforward (toposDirectImageModules f) φ hφ`. -/
def toposPushforwardDg :
    DifferentialGradedModule.{u, u, u} A ⥤ DifferentialGradedModule.{u, u, u} B :=
  toposPushforward (Osharp := X.O) (Psharp := Y.O) (toposDirectImageModules (X := X) (Y := Y) f)
    φ hφ

/-- `toposPullbackDg` is `toposBaseChangeFunctor`. -/
theorem toposPullbackDg_eq : toposPullbackDg f φ hφ = toposBaseChangeFunctor f φ hφ :=
  rfl

/-- `toposPushforwardDg` is `toposPushforward (toposDirectImageModules f) φ hφ`. -/
theorem toposPushforwardDg_eq :
    toposPushforwardDg f φ hφ =
      toposPushforward (Osharp := X.O) (Psharp := Y.O)
        (toposDirectImageModules (X := X) (Y := Y) f) φ hφ :=
  rfl

/-- The adjunction `f^* ⊣ f_*` of right differential graded modules,
`toposBaseChangeAdjunction`, with its right adjoint spelled
`toposPushforward (toposDirectImageModules f) φ hφ` over the two ringed topoi. -/
def toposPullbackPushforwardAdjunction : toposPullbackDg f φ hφ ⊣ (toposPushforwardDg f φ hφ) :=
  toposBaseChangeAdjunction f φ hφ

/-- The unit `N ⟶ f_*f^*N` of the adjunction `f^* ⊣ f_*` of right differential graded
modules. -/
def toposBaseChangeUnit (N : DifferentialGradedModule.{u, u, u} B) :
    N ⟶ (toposPushforwardDg f φ hφ).obj ((toposPullbackDg f φ hφ).obj N) :=
  (toposPullbackPushforwardAdjunction f φ hφ).unit.app N

/-- The direct image of a homogeneous map along a morphism of ringed topoi, as a homogeneous
map. -/
def toposPushforwardHomogeneous {P M : DifferentialGradedModule.{u, u, u} A} {n : ℤ}
    (w : HomogeneousMap (X := X.toRingedSite) A P M n) :
    HomogeneousMap (X := Y.toRingedSite) B ((toposPushforwardDg f φ hφ).obj P)
      ((toposPushforwardDg f φ hφ).obj M) n :=
  ⟨(toposPushforwardConcreteDGFunctor f φ hφ).mapCochain w.val w.2,
    (toposPushforwardConcreteDGFunctor f φ hφ).isActionLinear_mapCochain w.val w.2⟩

/-- The direct image of a homogeneous map is the direct image of sheaves of modules applied
degreewise. -/
theorem toposCochain_toposPushforwardHomogeneous {P M : DifferentialGradedModule.{u, u, u} A}
    {n : ℤ} (w : HomogeneousMap (X := X.toRingedSite) A P M n) :
    toposCochain (toposPushforwardHomogeneous f φ hφ w) =
      (toposCochain w).map (toposDirectImageModules (X := X) (Y := Y) f) :=
  rfl

/-- **The comparison** `f_*(Cofree(M[n])) ⟶ Cofree((f_*M)[n])`: the cofree transpose of the
direct image of the homogeneous counit. -/
def toposCofreeShiftHom (M : DifferentialGradedModule.{u, u, u} A) (n : ℤ) :
    (toposPushforwardDg f φ hφ).obj (Cofree.cofree (toposShiftForget M n)) ⟶
      Cofree.cofree (toposShiftForget ((toposPushforwardDg f φ hφ).obj M) n) :=
  toposCofreeOfHomogeneous (toposPushforwardHomogeneous f φ hφ (cofreeHomogeneousCounit M n))

/-- The comparison followed by the first coordinate is the direct image of the first
coordinate. -/
theorem toposCofreeShiftHom_comp_fst (M : DifferentialGradedModule.{u, u, u} A) (n p : ℤ) :
    (toposCofreeShiftHom f φ hφ M n).toHomologicalComplex.f p ≫
        cofreeFstHom (toposShiftForget ((toposPushforwardDg f φ hφ).obj M) n) p =
      (toposDirectImageModules (X := X) (Y := Y) f).map
        (cofreeFstHom (toposShiftForget M n) p) := by
  have h := toposCochain_toposHomogeneousOfCofree_v (toposCofreeShiftHom f φ hφ M n) p
  have h' := congrArg (fun z => (toposCochain z).v p (p + n) rfl)
    (toposHomogeneousOfCofree_toposCofreeOfHomogeneous
      (toposPushforwardHomogeneous f φ hφ (cofreeHomogeneousCounit M n)))
  refine h.symm.trans (h'.trans ?_)
  exact congrArg (toposDirectImageModules (X := X) (Y := Y) f).map (cofreeHomogeneousCounit_v M n p)

/-- **The comparison in degree `p` is the additivity comparison of the direct image**: its two
coordinates are the direct images of the two projections. -/
theorem toposCofreeShiftHom_f (M : DifferentialGradedModule.{u, u, u} A) (n p : ℤ) :
    (toposCofreeShiftHom f φ hφ M n).toHomologicalComplex.f p =
      biprod.lift
        ((toposDirectImageModules (X := X) (Y := Y) f).map
          (cofreeFstHom (toposShiftForget M n) p))
        ((toposDirectImageModules (X := X) (Y := Y) f).map
          (cofreeSndHom (toposShiftForget M n) p)) := by
  have h1 := toposCofreeShiftHom_comp_fst f φ hφ M n p
  have h2 := toposCofreeShiftHom_comp_fst f φ hφ M n (p + 1)
  have hcomm := (toposCofreeShiftHom f φ hφ M n).toHomologicalComplex.comm p (p + 1)
  refine biprod.hom_ext _ _ (h1.trans (biprod.lift_fst _ _).symm) ?_
  exact (congrArg ((toposCofreeShiftHom f φ hφ M n).toHomologicalComplex.f p ≫ ·)
      (cofree_d_comp_fstHom (toposShiftForget ((toposPushforwardDg f φ hφ).obj M) n) p).symm).trans
    ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ cofreeFstHom (toposShiftForget ((toposPushforwardDg f φ hφ).obj M) n) (p + 1))
      hcomm).trans
    ((Category.assoc _ _ _).trans
    ((congrArg (((toposPushforwardDg f φ hφ).obj
        (Cofree.cofree (toposShiftForget M n))).complex.d p (p + 1) ≫ ·) h2).trans
    (((toposDirectImageModules (X := X) (Y := Y) f).map_comp
        ((Cofree.cofree (toposShiftForget M n)).complex.d p (p + 1))
        (cofreeFstHom (toposShiftForget M n) (p + 1))).symm.trans
    ((congrArg (toposDirectImageModules (X := X) (Y := Y) f).map
        (cofree_d_comp_fstHom (toposShiftForget M n) p)).trans
      (biprod.lift_snd _ _).symm))))))

/-- The comparison is an isomorphism. -/
theorem isIso_toposCofreeShiftHom (M : DifferentialGradedModule.{u, u, u} A) (n : ℤ) :
    IsIso (toposCofreeShiftHom f φ hφ M n) :=
  isIso_of_componentwise _ fun p => by
    rw [toposCofreeShiftHom_f]
    exact biprod.isIso_lift_map (toposDirectImageModules (X := X) (Y := Y) f)
      ((toposShiftForget M n).piece p) ((toposShiftForget M n).piece (p + 1))

/-- **The direct image of the cofree module on `M[n]` is the cofree module on `(f_*M)[n]`.** -/
def toposCofreeShiftIso (M : DifferentialGradedModule.{u, u, u} A) (n : ℤ) :
    (toposPushforwardDg f φ hφ).obj (Cofree.cofree (toposShiftForget M n)) ≅
      Cofree.cofree (toposShiftForget ((toposPushforwardDg f φ hφ).obj M) n) :=
  haveI := isIso_toposCofreeShiftHom f φ hφ M n
  asIso (toposCofreeShiftHom f φ hφ M n)

/-! ### The direct image of homogeneous maps -/

/-- The direct image of homogeneous maps is additive. -/
theorem toposCochain_toposPushforwardHomogeneous_add {P M : DifferentialGradedModule.{u, u, u} A}
    {n : ℤ} {w w' w'' : HomogeneousMap (X := X.toRingedSite) A P M n}
    (h : toposCochain w'' = toposCochain w + toposCochain w') :
    toposCochain (toposPushforwardHomogeneous f φ hφ w'') =
      toposCochain (toposPushforwardHomogeneous f φ hφ w) +
        toposCochain (toposPushforwardHomogeneous f φ hφ w') :=
  have hl : IsActionLinear (X := X.toRingedSite) A (toposCochain w + toposCochain w') :=
    (congrArg (IsActionLinear (X := X.toRingedSite) A) h).mp w''.2
  ((toposPushforwardConcreteDGFunctor f φ hφ).mapCochain_congr h w''.2 hl).trans
    ((toposPushforwardConcreteDGFunctor f φ hφ).mapCochain_add _ _ w.2 w'.2 hl)

/-- The direct image of homogeneous maps commutes with the differentials of the Hom complexes. -/
theorem toposCochain_toposPushforwardHomogeneous_delta {P M : DifferentialGradedModule.{u, u, u} A}
    {n : ℤ} {w : HomogeneousMap (X := X.toRingedSite) A P M n}
    {w' : HomogeneousMap (X := X.toRingedSite) A P M (n + 1)}
    (h : toposCochain w' = δ n (n + 1) (toposCochain w)) :
    toposCochain (toposPushforwardHomogeneous f φ hφ w') =
      δ n (n + 1) (toposCochain (toposPushforwardHomogeneous f φ hφ w)) :=
  have hl : IsActionLinear (X := X.toRingedSite) A (δ n (n + 1) (toposCochain w)) :=
    (congrArg (IsActionLinear (X := X.toRingedSite) A) h).mp w'.2
  ((toposPushforwardConcreteDGFunctor f φ hφ).mapCochain_congr h w'.2 hl).trans
    ((toposPushforwardConcreteDGFunctor f φ hφ).mapCochain_delta _ w.2 hl)

/-- The direct image of a homogeneous map precomposed with a morphism. -/
theorem toposCochain_toposPushforwardHomogeneous_ofHom_comp
    {P P' M : DifferentialGradedModule.{u, u, u} A} {n : ℤ} (v : P' ⟶ P)
    {w : HomogeneousMap (X := X.toRingedSite) A P M n}
    {w' : HomogeneousMap (X := X.toRingedSite) A P' M n}
    (h : toposCochain w' = (Cochain.ofHom v.toHomologicalComplex).comp (toposCochain w)
      (zero_add n)) :
    toposCochain (toposPushforwardHomogeneous f φ hφ w') =
      (Cochain.ofHom ((toposPushforwardDg f φ hφ).map v).toHomologicalComplex).comp
        (toposCochain (toposPushforwardHomogeneous f φ hφ w)) (zero_add n) :=
  have hl : IsActionLinear (X := X.toRingedSite) A
      ((Cochain.ofHom v.toHomologicalComplex).comp (toposCochain w) (zero_add n)) :=
    (congrArg (IsActionLinear (X := X.toRingedSite) A) h).mp w'.2
  ((toposPushforwardConcreteDGFunctor f φ hφ).mapCochain_congr h w'.2 hl).trans
    (((toposPushforwardConcreteDGFunctor f φ hφ).mapCochain_comp _ _ (zero_add n)
        (actionLinear_ofHom (X := X.toRingedSite) A v) w.2 hl).trans
      (congrArg (fun z => z.comp ((toposPushforwardConcreteDGFunctor f φ hφ).mapCochain _ w.2)
        (zero_add n)) ((toposPushforwardConcreteDGFunctor f φ hφ).mapCochain_ofHom v)))

/-- The direct image of a homogeneous map followed by a morphism. -/
theorem toposCochain_toposPushforwardHomogeneous_comp_ofHom
    {P M M' : DifferentialGradedModule.{u, u, u} A} {n : ℤ} (v : M ⟶ M')
    {w : HomogeneousMap (X := X.toRingedSite) A P M n}
    {w' : HomogeneousMap (X := X.toRingedSite) A P M' n}
    (h : toposCochain w' = (toposCochain w).comp (Cochain.ofHom v.toHomologicalComplex)
      (add_zero n)) :
    toposCochain (toposPushforwardHomogeneous f φ hφ w') =
      (toposCochain (toposPushforwardHomogeneous f φ hφ w)).comp
        (Cochain.ofHom ((toposPushforwardDg f φ hφ).map v).toHomologicalComplex) (add_zero n) :=
  have hl : IsActionLinear (X := X.toRingedSite) A
      ((toposCochain w).comp (Cochain.ofHom v.toHomologicalComplex) (add_zero n)) :=
    (congrArg (IsActionLinear (X := X.toRingedSite) A) h).mp w'.2
  ((toposPushforwardConcreteDGFunctor f φ hφ).mapCochain_congr h w'.2 hl).trans
    (((toposPushforwardConcreteDGFunctor f φ hφ).mapCochain_comp _ _ (add_zero n) w.2
        (actionLinear_ofHom (X := X.toRingedSite) A v) hl).trans
      (congrArg (fun z => ((toposPushforwardConcreteDGFunctor f φ hφ).mapCochain _ w.2).comp z
        (add_zero n)) ((toposPushforwardConcreteDGFunctor f φ hφ).mapCochain_ofHom v)))

/-- The direct image of the homogeneous map of a morphism is the homogeneous map of its direct
image. -/
theorem toposCochain_toposPushforwardHomogeneous_ofHom {P M : DifferentialGradedModule.{u, u, u} A}
    (g : P ⟶ M) {w : HomogeneousMap (X := X.toRingedSite) A P M 0}
    (h : toposCochain w = Cochain.ofHom g.toHomologicalComplex) :
    toposCochain (toposPushforwardHomogeneous f φ hφ w) =
      Cochain.ofHom ((toposPushforwardDg f φ hφ).map g).toHomologicalComplex :=
  ((toposPushforwardConcreteDGFunctor f φ hφ).mapCochain_congr h w.2
    (actionLinear_ofHom (X := X.toRingedSite) A g)).trans
    ((toposPushforwardConcreteDGFunctor f φ hφ).mapCochain_ofHom g)

/-- The unit `N ⟶ f_*f^*N` is natural. -/
theorem toposBaseChangeUnit_naturality {N N' : DifferentialGradedModule.{u, u, u} B}
    (v : N' ⟶ N) :
    toposBaseChangeUnit f φ hφ N' ≫
        (toposPushforwardDg f φ hφ).map ((toposPullbackDg f φ hφ).map v) =
      v ≫ toposBaseChangeUnit f φ hφ N :=
  ((toposPullbackPushforwardAdjunction f φ hφ).unit.naturality v).symm

/-- The hom-set bijection of `f^* ⊣ f_*` is the unit followed by the direct image. -/
theorem toposBaseChangeAdjunction_homEquiv_apply (N : DifferentialGradedModule.{u, u, u} B)
    {M : DifferentialGradedModule.{u, u, u} A} (g : (toposPullbackDg f φ hφ).obj N ⟶ M) :
    (toposPullbackPushforwardAdjunction f φ hφ).homEquiv N M g =
      toposBaseChangeUnit f φ hφ N ≫ (toposPushforwardDg f φ hφ).map g :=
  Adjunction.homEquiv_unit _ _ _ _

/-! ### The identification of the Hom complexes -/

/-- In degree `p`, the first coordinate of the transpose of `k : f^*N ⟶ Cofree(M[n])` is the
unit followed by the direct image of the first coordinate of `k`. -/
theorem adjunctionHomEquivComp_f_comp_fst {N : DifferentialGradedModule.{u, u, u} B}
    {M : DifferentialGradedModule.{u, u, u} A} {n : ℤ}
    (k : (toposPullbackDg f φ hφ).obj N ⟶ Cofree.cofree (toposShiftForget M n)) (p : ℤ) :
    (adjunctionHomEquivComp (toposPullbackPushforwardAdjunction f φ hφ) N
        (toposCofreeShiftIso f φ hφ M n) k).toHomologicalComplex.f p ≫
        cofreeFstHom (toposShiftForget ((toposPushforwardDg f φ hφ).obj M) n) p =
      (toposBaseChangeUnit f φ hφ N).toHomologicalComplex.f p ≫
        (toposDirectImageModules (X := X) (Y := Y) f).map
          (k.toHomologicalComplex.f p ≫ cofreeFstHom (toposShiftForget M n) p) := by
  rw [adjunctionHomEquivComp_apply, comp_f, comp_f, Category.assoc, Category.assoc]
  change _ ≫ _ ≫ (toposCofreeShiftHom f φ hφ M n).toHomologicalComplex.f p ≫ _ = _
  rw [toposCofreeShiftHom_comp_fst, Functor.map_comp]
  rfl

/-- The transpose of a degree-`n` homogeneous map `f^*N ⟶ M` along the adjunction `f^* ⊣ f_*`,
through the cofree modules on `M[n]` and `(f_*M)[n]`. -/
def toposCofreeTranspose {N : DifferentialGradedModule.{u, u, u} B}
    {M : DifferentialGradedModule.{u, u, u} A} {n : ℤ}
    (w : HomogeneousMap (X := X.toRingedSite) A ((toposPullbackDg f φ hφ).obj N) M n) :
    HomogeneousMap (X := Y.toRingedSite) B N ((toposPushforwardDg f φ hφ).obj M) n :=
  toposHomogeneousOfCofree (X := Y) (A := B)
    (adjunctionHomEquivComp (toposPullbackPushforwardAdjunction f φ hφ) N
      (toposCofreeShiftIso f φ hφ M n) (toposCofreeOfHomogeneous w))

/-- The inverse transpose of a degree-`n` homogeneous map `N ⟶ f_*M`, through the cofree
modules. -/
def toposCofreeTransposeInv {N : DifferentialGradedModule.{u, u, u} B}
    {M : DifferentialGradedModule.{u, u, u} A} {n : ℤ}
    (w : HomogeneousMap (X := Y.toRingedSite) B N ((toposPushforwardDg f φ hφ).obj M) n) :
    HomogeneousMap (X := X.toRingedSite) A ((toposPullbackDg f φ hφ).obj N) M n :=
  toposHomogeneousOfCofree (X := X) (A := A)
    ((adjunctionHomEquivComp (toposPullbackPushforwardAdjunction f φ hφ) N
      (toposCofreeShiftIso f φ hφ M n)).symm (toposCofreeOfHomogeneous w))

/-- The inverse transpose undoes the transpose. -/
theorem toposCofreeTransposeInv_toposCofreeTranspose {N : DifferentialGradedModule.{u, u, u} B}
    {M : DifferentialGradedModule.{u, u, u} A} {n : ℤ}
    (w : HomogeneousMap (X := X.toRingedSite) A ((toposPullbackDg f φ hφ).obj N) M n) :
    toposCofreeTransposeInv f φ hφ (toposCofreeTranspose f φ hφ w) = w :=
  (congrArg (fun k => toposHomogeneousOfCofree (X := X) (A := A)
      ((adjunctionHomEquivComp (toposPullbackPushforwardAdjunction f φ hφ) N
        (toposCofreeShiftIso f φ hφ M n)).symm k))
    (toposCofreeOfHomogeneous_toposHomogeneousOfCofree (X := Y) (A := B) _)).trans
    ((congrArg (toposHomogeneousOfCofree (X := X) (A := A))
      ((adjunctionHomEquivComp (toposPullbackPushforwardAdjunction f φ hφ) N
        (toposCofreeShiftIso f φ hφ M n)).symm_apply_apply (toposCofreeOfHomogeneous w))).trans
    (toposHomogeneousOfCofree_toposCofreeOfHomogeneous (X := X) (A := A) w))

/-- The transpose undoes the inverse transpose. -/
theorem toposCofreeTranspose_toposCofreeTransposeInv {N : DifferentialGradedModule.{u, u, u} B}
    {M : DifferentialGradedModule.{u, u, u} A} {n : ℤ}
    (w : HomogeneousMap (X := Y.toRingedSite) B N ((toposPushforwardDg f φ hφ).obj M) n) :
    toposCofreeTranspose f φ hφ (toposCofreeTransposeInv f φ hφ w) = w :=
  (congrArg (fun k => toposHomogeneousOfCofree (X := Y) (A := B)
      (adjunctionHomEquivComp (toposPullbackPushforwardAdjunction f φ hφ) N
        (toposCofreeShiftIso f φ hφ M n) k))
    (toposCofreeOfHomogeneous_toposHomogeneousOfCofree (X := X) (A := A) _)).trans
    ((congrArg (toposHomogeneousOfCofree (X := Y) (A := B))
      ((adjunctionHomEquivComp (toposPullbackPushforwardAdjunction f φ hφ) N
        (toposCofreeShiftIso f φ hφ M n)).apply_symm_apply (toposCofreeOfHomogeneous w))).trans
    (toposHomogeneousOfCofree_toposCofreeOfHomogeneous (X := Y) (A := B) w))

/-- **The map `w ↦ η_N ∘ f_*(w)`** from the degree-`n` homogeneous maps `f^*N ⟶ M` to the
degree-`n` homogeneous maps `N ⟶ f_*M`, for `η` the unit of `f^* ⊣ f_*` and `f_*(w)` the direct
image of the homogeneous map `w`. -/
def toposPullbackPushforwardHomogeneous {N : DifferentialGradedModule.{u, u, u} B}
    {M : DifferentialGradedModule.{u, u, u} A} {n : ℤ}
    (w : HomogeneousMap (X := X.toRingedSite) A ((toposPullbackDg f φ hφ).obj N) M n) :
    HomogeneousMap (X := Y.toRingedSite) B N ((toposPushforwardDg f φ hφ).obj M) n :=
  ⟨(Cochain.ofHom (toposBaseChangeUnit f φ hφ N).toHomologicalComplex).comp
      (toposPushforwardHomogeneous f φ hφ w).val (zero_add n),
    actionLinear_comp (X := Y.toRingedSite) B _ _ (zero_add n)
      (actionLinear_ofHom (X := Y.toRingedSite) B _) (toposPushforwardHomogeneous f φ hφ w).2⟩

/-- The underlying cochain of `w ↦ η_N ∘ f_*(w)`. -/
theorem toposCochain_toposPullbackPushforwardHomogeneous
    {N : DifferentialGradedModule.{u, u, u} B} {M : DifferentialGradedModule.{u, u, u} A} {n : ℤ}
    (w : HomogeneousMap (X := X.toRingedSite) A ((toposPullbackDg f φ hφ).obj N) M n) :
    toposCochain (toposPullbackPushforwardHomogeneous f φ hφ w) =
      (Cochain.ofHom (toposBaseChangeUnit f φ hφ N).toHomologicalComplex).comp
        (toposCochain (toposPushforwardHomogeneous f φ hφ w)) (zero_add n) :=
  rfl

/-- The bijection obtained through the cofree modules is `w ↦ η_N ∘ f_*(w)`, on underlying
cochains. -/
theorem toposCochain_toposCofreeTranspose (N : DifferentialGradedModule.{u, u, u} B)
    (M : DifferentialGradedModule.{u, u, u} A) (n : ℤ)
    (w : HomogeneousMap (X := X.toRingedSite) A ((toposPullbackDg f φ hφ).obj N) M n) :
    toposCochain (toposCofreeTranspose f φ hφ w) =
      toposCochain (toposPullbackPushforwardHomogeneous f φ hφ w) := by
  refine Cochain.ext _ _ fun p q hpq => ?_
  subst hpq
  have hwv : (toposCochain w).v p (p + n) rfl =
      (toposCofreeOfHomogeneous w).toHomologicalComplex.f p ≫
        cofreeFstHom (toposShiftForget M n) p :=
    (congrArg (fun z => (toposCochain z).v p (p + n) rfl)
      (toposHomogeneousOfCofree_toposCofreeOfHomogeneous (X := X) (A := A) w)).symm.trans
      (toposCochain_toposHomogeneousOfCofree_v (X := X) (A := A) (toposCofreeOfHomogeneous w) p)
  have h1 := toposCochain_toposHomogeneousOfCofree_v (X := Y) (A := B)
    (adjunctionHomEquivComp (toposPullbackPushforwardAdjunction f φ hφ) N
      (toposCofreeShiftIso f φ hφ M n) (toposCofreeOfHomogeneous w)) p
  have h2 := adjunctionHomEquivComp_f_comp_fst f φ hφ (toposCofreeOfHomogeneous w) p
  have h3 := congrArg (fun x => (toposBaseChangeUnit f φ hφ N).toHomologicalComplex.f p ≫
    (toposDirectImageModules (X := X) (Y := Y) f).map x) hwv.symm
  have h4 := (Cochain.zero_cochain_comp_v
      (Cochain.ofHom (toposBaseChangeUnit f φ hφ N).toHomologicalComplex)
      ((toposCochain w).map (toposDirectImageModules (X := X) (Y := Y) f)) p (p + n) rfl).trans
    (congrArg (· ≫ _) (Cochain.ofHom_v _ p))
  exact h1.trans (h2.trans (h3.trans h4.symm))

/-- The transpose through the cofree modules is `w ↦ η_N ∘ f_*(w)`. -/
theorem toposCofreeTranspose_eq {N : DifferentialGradedModule.{u, u, u} B}
    {M : DifferentialGradedModule.{u, u, u} A} {n : ℤ}
    (w : HomogeneousMap (X := X.toRingedSite) A ((toposPullbackDg f φ hφ).obj N) M n) :
    toposCofreeTranspose f φ hφ w = toposPullbackPushforwardHomogeneous f φ hφ w :=
  toposCochain_injective (X := Y) (A := B) (toposCochain_toposCofreeTranspose f φ hφ N M n w)

/-- **Pull and push for the Hom complexes, in degree `n`**: the homogeneous right-linear maps of
degree `n` from `f^*N` to `M` are the homogeneous right-linear maps of degree `n` from `N` to
`f_*M`, by `w ↦ η_N ∘ f_*(w)`. -/
def toposPullbackPushforwardHomogeneousEquiv (N : DifferentialGradedModule.{u, u, u} B)
    (M : DifferentialGradedModule.{u, u, u} A) (n : ℤ) :
    HomogeneousMap (X := X.toRingedSite) A ((toposPullbackDg f φ hφ).obj N) M n ≃
      HomogeneousMap (X := Y.toRingedSite) B N ((toposPushforwardDg f φ hφ).obj M) n where
  toFun := toposPullbackPushforwardHomogeneous f φ hφ
  invFun := toposCofreeTransposeInv f φ hφ
  left_inv w :=
    (congrArg (toposCofreeTransposeInv f φ hφ) (toposCofreeTranspose_eq f φ hφ w).symm).trans
    (toposCofreeTransposeInv_toposCofreeTranspose f φ hφ w)
  right_inv w := (toposCofreeTranspose_eq f φ hφ _).symm.trans
    (toposCofreeTranspose_toposCofreeTransposeInv f φ hφ w)

/-- The underlying cochain of the identification is `η_N ∘ f_*(w)`. -/
theorem toposCochain_toposPullbackPushforwardHomogeneousEquiv
    (N : DifferentialGradedModule.{u, u, u} B) (M : DifferentialGradedModule.{u, u, u} A) (n : ℤ)
    (w : HomogeneousMap (X := X.toRingedSite) A ((toposPullbackDg f φ hφ).obj N) M n) :
    toposCochain (toposPullbackPushforwardHomogeneousEquiv f φ hφ N M n w) =
      (Cochain.ofHom (toposBaseChangeUnit f φ hφ N).toHomologicalComplex).comp
        (toposCochain (toposPushforwardHomogeneous f φ hφ w)) (zero_add n) :=
  rfl

/-- **Stacks Project, Tag 0FRU.** Let `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of
ringed topoi, let `A` be a differential graded `O_C`-algebra, let `B` be a differential graded
`O_D`-algebra and let `φ : B ⟶ f_*A` be a unital homomorphism of differential graded
`O_D`-algebras (the datum of Tag 0FRT in the form of Remark 0FRG). Then for a right differential
graded `B`-module `N` and a right differential graded `A`-module `M`,
`Hom_{Mod^dg(B, d)}(N, f_*M) = Hom_{Mod^dg(A, d)}(f^*N, M)`.

Here `f^*N = f^*N ⊗_{f^*B} A` is `toposPullbackDg f φ hφ` (that is, `toposBaseChangeFunctor f φ
hφ`) and `f_*` is `toposPushforwardDg f φ hφ` (that is,
`toposPushforward (toposDirectImageModules f) φ hφ`). The identification `e` of the two
differential graded Hom objects is given in every degree `n`; it is `w ↦ η_N ∘ f_*(w)` for `η`
the unit of the adjunction `f^* ⊣ f_*` and `f_*(w)` the direct image of the homogeneous map `w`;
it is additive and carries the differential of the one Hom complex to the differential of the
other, so it is an isomorphism of complexes; it is natural in `N` and in `M`; and on morphisms of
differential graded modules it is the hom-set bijection of the adjunction `f^* ⊣ f_*`
(`toposPullbackPushforwardAdjunction`, that is, `toposBaseChangeAdjunction`). -/
@[stacks 0FRU]
theorem exists_toposPullbackPushforwardHomEquiv :
    ∃ e : ∀ (N : DifferentialGradedModule.{u, u, u} B)
        (M : DifferentialGradedModule.{u, u, u} A) (n : ℤ),
        HomogeneousMap (X := X.toRingedSite) A ((toposPullbackDg f φ hφ).obj N) M n ≃
          HomogeneousMap (X := Y.toRingedSite) B N ((toposPushforwardDg f φ hφ).obj M) n,
      (∀ N M n w, toposCochain (e N M n w) =
        (Cochain.ofHom (toposBaseChangeUnit f φ hφ N).toHomologicalComplex).comp
          (toposCochain (toposPushforwardHomogeneous f φ hφ w)) (zero_add n)) ∧
      (∀ N M n w w' w'', toposCochain w'' = toposCochain w + toposCochain w' →
        toposCochain (e N M n w'') = toposCochain (e N M n w) + toposCochain (e N M n w')) ∧
      (∀ N M n w w', toposCochain w' = δ n (n + 1) (toposCochain w) →
        toposCochain (e N M (n + 1) w') = δ n (n + 1) (toposCochain (e N M n w))) ∧
      (∀ (N N' : DifferentialGradedModule.{u, u, u} B) M n (v : N' ⟶ N) w w',
        toposCochain w' =
          (Cochain.ofHom ((toposPullbackDg f φ hφ).map v).toHomologicalComplex).comp
            (toposCochain w) (zero_add n) →
        toposCochain (e N' M n w') =
          (Cochain.ofHom v.toHomologicalComplex).comp (toposCochain (e N M n w)) (zero_add n)) ∧
      (∀ N (M M' : DifferentialGradedModule.{u, u, u} A) n (v : M ⟶ M') w w',
        toposCochain w' = (toposCochain w).comp (Cochain.ofHom v.toHomologicalComplex)
          (add_zero n) →
        toposCochain (e N M' n w') = (toposCochain (e N M n w)).comp
          (Cochain.ofHom ((toposPushforwardDg f φ hφ).map v).toHomologicalComplex) (add_zero n)) ∧
      (∀ (N : DifferentialGradedModule.{u, u, u} B) (M : DifferentialGradedModule.{u, u, u} A)
          (g : (toposPullbackDg f φ hφ).obj N ⟶ M) w,
        toposCochain w = Cochain.ofHom g.toHomologicalComplex →
        toposCochain (e N M 0 w) = Cochain.ofHom
          ((toposPullbackPushforwardAdjunction f φ hφ).homEquiv N M g).toHomologicalComplex) := by
  refine ⟨toposPullbackPushforwardHomogeneousEquiv f φ hφ,
    toposCochain_toposPullbackPushforwardHomogeneousEquiv f φ hφ, ?_, ?_, ?_, ?_, ?_⟩
  · intro N M n w w' w'' hw
    rw [toposCochain_toposPullbackPushforwardHomogeneousEquiv,
      toposCochain_toposPullbackPushforwardHomogeneousEquiv,
      toposCochain_toposPullbackPushforwardHomogeneousEquiv,
      toposCochain_toposPushforwardHomogeneous_add f φ hφ hw, Cochain.comp_add]
  · intro N M n w w' hw
    rw [toposCochain_toposPullbackPushforwardHomogeneousEquiv,
      toposCochain_toposPullbackPushforwardHomogeneousEquiv,
      toposCochain_toposPushforwardHomogeneous_delta f φ hφ hw, δ_ofHom_comp]
  · intro N N' M n v w w' hw
    rw [toposCochain_toposPullbackPushforwardHomogeneousEquiv,
      toposCochain_toposPullbackPushforwardHomogeneousEquiv,
      toposCochain_toposPushforwardHomogeneous_ofHom_comp f φ hφ _ hw]
    exact cochain_ofHom_comp_ofHom_comp
      (congrArg Hom.toHomologicalComplex (toposBaseChangeUnit_naturality f φ hφ v)) _
  · intro N M M' n v w w' hw
    rw [toposCochain_toposPullbackPushforwardHomogeneousEquiv,
      toposCochain_toposPullbackPushforwardHomogeneousEquiv,
      toposCochain_toposPushforwardHomogeneous_comp_ofHom f φ hφ _ hw,
      Cochain.comp_assoc_of_third_is_zero_cochain]
  · intro N M g w hw
    refine (toposCochain_toposPullbackPushforwardHomogeneousEquiv f φ hφ N M 0 w).trans ?_
    refine (congrArg
      (fun z => (Cochain.ofHom (toposBaseChangeUnit f φ hφ N).toHomologicalComplex).comp
        z (zero_add 0)) (toposCochain_toposPushforwardHomogeneous_ofHom f φ hφ g hw)).trans ?_
    rw [toposBaseChangeAdjunction_homEquiv_apply]
    exact (Cochain.ofHom_comp _ _).symm

end Topos

end SheafOfModules.DifferentialGradedModule

end
