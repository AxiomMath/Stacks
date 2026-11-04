module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedCategory
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedInternalHomSheaf

/-!
# The internal hom of a differential graded bimodule, as a differential graded module

Let `R` be a sheaf of commutative rings on a site, let `A` and `A'` be sheaves of differential
graded `R`-algebras, let `N` be a differential graded `(A, A')`-bimodule and let `M` be a right
differential graded `A'`-module. The internal hom `SheafHom^dg_{A'}(N, M)`, the complex
`SheafOfModules.sheafHomComplex`, is a right differential graded `A`-module, a local section `a`
of `A` acting by `(q a)(x) = q (a x)`. This file constructs that module and the functor
`SheafHom^dg_{A'}(N, -)`.

## Main definitions

* `SheafOfModules.LocalHom.actLeft`: the action `(q a)(x) = q (a x)` on local homomorphisms.
* `SheafOfModules.LocalHom.postcomp` and `SheafOfModules.sheafHomCochain`: postcomposition with
  a cochain commuting with the action, on local homomorphisms and as a cochain between internal
  homs.
* `SheafOfModules.sheafHomModule`: the right differential graded `A`-module
  `SheafHom^dg_{A'}(N, M)`.
* `SheafOfModules.sheafHomFunctor`: the functor `SheafHom^dg_{A'}(N, -)`.
* `SheafOfModules.sheafHomFunctorData` and `SheafOfModules.sheafHomHomotopyExtension`: the
  functor `SheafHom^dg_{A'}(N, -)` as a `SheafOfModules.SheafHomFunctorData`, and its extension
  to homotopies.
* `SheafOfModules.DifferentialGradedModule.Homotopy.toCochain` and
  `SheafOfModules.homotopyOfCochain`: homotopies of differential graded modules and linear
  cochains of degree `-1` with prescribed differential.

## Main results

* `SheafOfModules.LocalHom.diffAt_actLeft`: the Leibniz rule `d(q a) = d(q) a + (-1)^n q d(a)`.
* `SheafOfModules.sheafHomCochain_delta`: postcomposition commutes with the differentials of the
  hom complexes.

## Implementation notes

The base sheaf of rings has commutative rings of sections, recorded by the instance argument
`∀ U, IsMulCommutative (R.obj.obj U)`; this holds for the structure sheaf of a ringed site.
Postcomposition is sign-free: `(c ∘ q)(x) = c (q x)`, and with the differential
`d(f) = d ∘ f - (-1)^n f ∘ d` on both hom complexes this commutes with the differentials.

## References

* [Stacks Project, Tag 0FRN](https://stacks.math.columbia.edu/tag/0FRN)
* [Stacks Project, Tag 0FRS](https://stacks.math.columbia.edu/tag/0FRS)
-/

@[expose] public section

open CategoryTheory Opposite

universe t a z s v u

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

namespace LocalHom

section Transport

variable {A : DifferentialGradedAlgebra.{t, a} R}
  {K : DifferentialGradedModule.{t, a, z} A} {L : DifferentialGradedModule.{t, a, s} A} {U : C}

/-- Local homomorphisms of two equal degrees are heterogeneously equal when their values are. -/
theorem heq_of_app {n n' : ℤ} (h : n = n') {f : LocalHom K L n U} {g : LocalHom K L n' U}
    (H : ∀ (i j : ℤ) (hij : i + n = j) (hij' : i + n' = j) (V : Over U)
      (x : (K.complex.X i).val.obj (op V.left)), f.app i j hij V x = g.app i j hij' V x) :
    HEq f g := by
  subst h
  exact heq_of_eq (LocalHom.ext fun i j hij V x => H i j hij hij V x)

/-- Transporting a local homomorphism along an equality of degrees does not change its
values. -/
theorem gradedCast_app {n n' : ℤ} (h : n = n') (f : LocalHom K L n U) (i j : ℤ)
    (hij : i + n' = j) (V : Over U) (x : (K.complex.X i).val.obj (op V.left)) :
    (gradedCast (fun k => LocalHom K L k U) h f).app i j hij V x = f.app i j (by omega) V x := by
  subst h; rfl

end Transport

section LeftAction

variable {A A' : DifferentialGradedAlgebra.{t, a} R} {N : DifferentialGradedBimodule.{t, a, z} A A'}
  {M : DifferentialGradedModule.{t, a, s} A'} {n : ℤ} {U : C}

/-- Restriction of a local section of a sheaf of modules along a morphism of the site, with its
type written as the sections over the source. -/
noncomputable def resSec (F : SheafOfModules.{a} R) {U V : C} (g : V ⟶ U)
    (x : F.val.obj (op U)) : F.val.obj (op V) :=
  F.val.map g.op x

/-- Restriction of local sections is additive. -/
theorem resSec_add (F : SheafOfModules.{a} R) {U V : C} (g : V ⟶ U) (x y : F.val.obj (op U)) :
    resSec F g (x + y) = resSec F g x + resSec F g y :=
  map_add _ _ _

/-- Restriction of local sections is semilinear along the restriction of the ring of sections. -/
theorem resSec_smul (F : SheafOfModules.{a} R) {U V : C} (g : V ⟶ U) (r : R.obj.obj (op U))
    (x : F.val.obj (op U)) : resSec F g (r • x) = R.obj.map g.op r • resSec F g x :=
  PresheafOfModules.map_smul _ _ _ _

/-- Restriction along a composite is the composite of the restrictions. -/
theorem resSec_comp (F : SheafOfModules.{a} R) {U V W : C} (g : V ⟶ U) (g' : W ⟶ V)
    (x : F.val.obj (op U)) : resSec F (g' ≫ g) x = resSec F g' (resSec F g x) := by
  unfold resSec
  rw [op_comp, PresheafOfModules.map_comp_apply]

/-- The action `(q a)(x) = q (a x)` of a homogeneous local section `a` of `A` on a local
homomorphism `q` out of the bimodule `N`. -/
noncomputable def actLeft (q : LocalHom N.toRightModule M n U) {p : ℤ}
    (b : (A.complex.X p).val.obj (op U)) :
    LocalHom N.toRightModule M (n + p) U where
  app i j hij V := AddMonoidHom.mk'
    (fun x => q.app (p + i) j (by omega) V
      ((N.leftMul p i).app (op V.left) (resSec (A.complex.X p) V.hom b) x))
    (fun x y => (congrArg (q.app (p + i) j (by omega) V) (map_add _ x y)).trans (map_add _ _ _))
  map_smul i j hij V r x := by
    change q.app (p + i) j _ V ((N.leftMul p i).app (op V.left) (resSec (A.complex.X p) V.hom b)
      (r • x)) = r • q.app (p + i) j _ V
        ((N.leftMul p i).app (op V.left) (resSec (A.complex.X p) V.hom b) x)
    exact (congrArg (q.app (p + i) j _ V)
      ((N.leftMul p i).map_smul_right (op V.left) r _ x)).trans
        (q.map_smul (p + i) j _ V r _)
  naturality i j hij {V W} k x := by
    change (M.complex.X j).val.map k.left.op (q.app (p + i) j _ V
        ((N.leftMul p i).app (op V.left) (resSec (A.complex.X p) V.hom b) x)) =
      q.app (p + i) j _ W ((N.leftMul p i).app (op W.left) (resSec (A.complex.X p) W.hom b)
        ((N.complex.X i).val.map k.left.op x))
    have hb : (A.complex.X p).val.map k.left.op (resSec (A.complex.X p) V.hom b) =
        resSec (A.complex.X p) W.hom b := by
      change resSec _ k.left (resSec _ V.hom b) = _
      rw [← resSec_comp, Over.w k]
    refine (q.naturality (p + i) j _ k _).trans ?_
    refine congrArg (q.app (p + i) j _ W) (((N.leftMul p i).naturality k.left.op _ x).trans ?_)
    exact congrArg (fun y => (N.leftMul p i).app (op W.left) y
      ((N.complex.X i).val.map k.left.op x)) hb
  isLinear i j hij c V x e := by
    change q.app (p + (i + c)) (j + c) _ V ((N.leftMul p (i + c)).app (op V.left)
        (resSec (A.complex.X p) V.hom b) ((N.rightMul i c).app (op V.left) x e)) =
      (M.mul j c).app (op V.left) (q.app (p + i) j _ V
        ((N.leftMul p i).app (op V.left) (resSec (A.complex.X p) V.hom b) x)) e
    refine Eq.trans ?_ (q.isLinear (p + i) j (by omega) c V _ e)
    exact LocalGradedHom.app_congr_heq _ _ _ V
      (N.left_right_assoc p i c (op V.left) _ x e).symm

/-- The value of `q a` at `x` is `q (a x)`, with `a` restricted to the open of `x`. -/
theorem actLeft_app (q : LocalHom N.toRightModule M n U) {p : ℤ}
    (b : (A.complex.X p).val.obj (op U)) (i j : ℤ) (hij : i + (n + p) = j) (V : Over U)
    (x : (N.complex.X i).val.obj (op V.left)) :
    (q.actLeft b).app i j hij V x =
      q.app (p + i) j (by omega) V
        ((N.leftMul p i).app (op V.left) (resSec (A.complex.X p) V.hom b) x) := rfl

/-- The action is additive in the local homomorphism: `(q + q') a = q a + q' a`. -/
theorem actLeft_add_left (q q' : LocalHom N.toRightModule M n U) {p : ℤ}
    (b : (A.complex.X p).val.obj (op U)) :
    (q + q').actLeft b = q.actLeft b + q'.actLeft b := rfl

/-- The action is additive in the section: `q (a + a') = q a + q a'`. -/
theorem actLeft_add_right (q : LocalHom N.toRightModule M n U) {p : ℤ}
    (b b' : (A.complex.X p).val.obj (op U)) :
    q.actLeft (b + b') = q.actLeft b + q.actLeft b' :=
  LocalHom.ext fun i j hij V x => by
    show q.app (p + i) j _ V ((N.leftMul p i).app (op V.left)
      (resSec (A.complex.X p) V.hom (b + b')) x) = q.app (p + i) j _ V ((N.leftMul p i).app
        (op V.left) (resSec (A.complex.X p) V.hom b) x) + q.app (p + i) j _ V
          ((N.leftMul p i).app (op V.left) (resSec (A.complex.X p) V.hom b') x)
    rw [resSec_add, map_add, AddMonoidHom.add_apply]
    exact map_add _ _ _

/-- The action commutes with restriction: `(q a)|_{U'} = q|_{U'} a|_{U'}`. -/
theorem restrict_actLeft (q : LocalHom N.toRightModule M n U) {p : ℤ}
    (b : (A.complex.X p).val.obj (op U)) {U' : C} (g : U' ⟶ U) :
    (q.actLeft b).restrict g = (q.restrict g).actLeft (resSec (A.complex.X p) g b) :=
  LocalHom.ext fun i j hij V x => by
    show q.app (p + i) j _ (Over.mk (V.hom ≫ g)) ((N.leftMul p i).app (op V.left)
      (resSec (A.complex.X p) (V.hom ≫ g) b) x) = q.app (p + i) j _ (Over.mk (V.hom ≫ g))
        ((N.leftMul p i).app (op V.left) (resSec (A.complex.X p) V.hom
          (resSec (A.complex.X p) g b)) x)
    rw [resSec_comp]

variable [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)]

/-- The action is linear in the local homomorphism: `(r q) a = r (q a)`. -/
theorem actLeft_smul_left (r : R.obj.obj (op U)) (q : LocalHom N.toRightModule M n U) {p : ℤ}
    (b : (A.complex.X p).val.obj (op U)) :
    (r • q).actLeft b = r • q.actLeft b := rfl

/-- The action is linear in the section: `q (r a) = r (q a)`. -/
theorem actLeft_smul_right (r : R.obj.obj (op U)) (q : LocalHom N.toRightModule M n U) {p : ℤ}
    (b : (A.complex.X p).val.obj (op U)) :
    q.actLeft (r • b) = r • q.actLeft b :=
  LocalHom.ext fun i j hij V x => by
    show q.app (p + i) j _ V ((N.leftMul p i).app (op V.left)
      (resSec (A.complex.X p) V.hom (r • b)) x) = R.obj.map V.hom.op r • q.app (p + i) j _ V
        ((N.leftMul p i).app (op V.left) (resSec (A.complex.X p) V.hom b) x)
    rw [resSec_smul, (N.leftMul p i).map_smul_left]
    exact q.map_smul (p + i) j _ V _ _

omit [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)] in
/-- The action is associative: `(q a) a' = q (a a')`. -/
theorem actLeft_actLeft (q : LocalHom N.toRightModule M n U) {p p' : ℤ}
    (b : (A.complex.X p).val.obj (op U)) (b' : (A.complex.X p').val.obj (op U)) :
    HEq ((q.actLeft b).actLeft b') (q.actLeft ((A.mul p p').app (op U) b b')) :=
  heq_of_app (add_assoc n p p') fun i j hij hij' V x => by
    show q.app (p + (p' + i)) j _ V ((N.leftMul p (p' + i)).app (op V.left)
        (resSec (A.complex.X p) V.hom b) ((N.leftMul p' i).app (op V.left)
          (resSec (A.complex.X p') V.hom b') x)) =
      q.app (p + p' + i) j _ V ((N.leftMul (p + p') i).app (op V.left)
        (resSec (A.complex.X (p + p')) V.hom ((A.mul p p').app (op U) b b')) x)
    have hm : resSec (A.complex.X (p + p')) V.hom ((A.mul p p').app (op U) b b') =
        (A.mul p p').app (op V.left) (resSec (A.complex.X p) V.hom b)
          (resSec (A.complex.X p') V.hom b') :=
      (A.mul p p').naturality V.hom.op b b'
    rw [hm]
    exact LocalGradedHom.app_congr_heq _ _ _ V (N.left_assoc p p' i (op V.left) _ _ x)

omit [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)] in
/-- The unit acts trivially. -/
theorem actLeft_one (q : LocalHom N.toRightModule M n U) :
    HEq (q.actLeft (A.one.eval (op U))) q :=
  heq_of_app (add_zero n) fun i j hij hij' V x => by
    show q.app (0 + i) j _ V ((N.leftMul 0 i).app (op V.left)
        (resSec (A.complex.X 0) V.hom (A.one.eval (op U))) x) = q.app i j _ V x
    have h1 : resSec (A.complex.X 0) V.hom (A.one.eval (op U)) = A.one.eval (op V.left) :=
      PresheafOfModules.sections_property A.one V.hom.op
    rw [h1]
    exact LocalGradedHom.app_congr_heq _ _ _ V (N.one_left i (op V.left) x)

omit [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)] in
/-- **The Leibniz rule for the action**: `d(q a) = d(q) a + (-1)^n q d(a)`. -/
theorem diffAt_actLeft (q : LocalHom N.toRightModule M n U) {p : ℤ}
    (b : (A.complex.X p).val.obj (op U)) :
    (q.actLeft b).diffAt =
      gradedCast (fun k => LocalHom N.toRightModule M k U) (add_right_comm n 1 p)
          (q.diffAt.actLeft b) +
        (n.negOnePow : ℤ) • gradedCast (fun k => LocalHom N.toRightModule M k U)
          (add_assoc n p 1).symm (q.actLeft ((A.complex.d p (p + 1)).val.app (op U) b)) :=
  LocalHom.ext fun i j hij V x => by
    rw [add_app, zsmul_app, gradedCast_app, gradedCast_app, diffAt_app]
    show (M.complex.d (i + (n + p)) j).val.app (op V.left)
        (q.app (p + i) (i + (n + p)) (by omega) V
          ((N.leftMul p i).app (op V.left) (resSec (A.complex.X p) V.hom b) x)) -
      ((n + p).negOnePow : ℤ) • q.app (p + (i + 1)) j (by omega) V
        ((N.leftMul p (i + 1)).app (op V.left)
          (resSec (A.complex.X p) V.hom b) ((N.complex.d i (i + 1)).val.app (op V.left) x)) =
      q.diffAt.app (p + i) j (by omega) V ((N.leftMul p i).app (op V.left)
        (resSec (A.complex.X p) V.hom b) x) +
      (n.negOnePow : ℤ) • q.app (p + 1 + i) j (by omega) V ((N.leftMul (p + 1) i).app (op V.left)
        (resSec (A.complex.X (p + 1)) V.hom ((A.complex.d p (p + 1)).val.app (op U) b)) x)
    have hd : resSec (A.complex.X (p + 1)) V.hom ((A.complex.d p (p + 1)).val.app (op U) b) =
        (A.complex.d p (p + 1)).val.app (op V.left) (resSec (A.complex.X p) V.hom b) :=
      (PresheafOfModules.naturality_apply (A.complex.d p (p + 1)).val V.hom.op b).symm
    rw [hd, diffAt_app, N.leibniz_left p i (op V.left), ← castHom_apply, ← castHom_apply,
      map_add, map_zsmul,
      q.toLocalGradedHom.app_castHom_src (show p + 1 + i = p + i + 1 by omega) (by omega) V,
      q.toLocalGradedHom.app_castHom_src (show p + (i + 1) = p + i + 1 by omega) (by omega) V]
    have key : (M.complex.d (i + (n + p)) j).val.app (op V.left)
        (q.app (p + i) (i + (n + p)) (by omega) V ((N.leftMul p i).app (op V.left)
          (resSec (A.complex.X p) V.hom b) x)) =
      (M.complex.d (p + i + n) j).val.app (op V.left)
        (q.app (p + i) (p + i + n) rfl V ((N.leftMul p i).app (op V.left)
          (resSec (A.complex.X p) V.hom b) x)) := by
      have e : ∀ (r r' : ℤ) (hr : p + i + n = r) (hr' : p + i + n = r'),
          (M.complex.d r j).val.app (op V.left) (q.app (p + i) r hr V ((N.leftMul p i).app
            (op V.left) (resSec (A.complex.X p) V.hom b) x)) =
          (M.complex.d r' j).val.app (op V.left) (q.app (p + i) r' hr' V ((N.leftMul p i).app
            (op V.left) (resSec (A.complex.X p) V.hom b) x)) := by
        intro r r' hr hr'; subst hr; subst hr'; rfl
      exact e _ _ _ _
    rw [key, Int.negOnePow_add, Units.val_mul, mul_smul, smul_add, smul_comm
      ((n.negOnePow : ℤˣ) : ℤ) ((p.negOnePow : ℤˣ) : ℤ)]
    abel

end LeftAction

end LocalHom

section Postcomp

open CochainComplex.HomComplex

/-- An integer multiple of a morphism of sheaves of modules acts on sections by that multiple. -/
theorem homSections_zsmul' {S T : SheafOfModules.{s} R} (k : ℤ) (f : S ⟶ T) (U : Cᵒᵖ)
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

/-- A sign multiple of a morphism of sheaves of modules acts on sections by that sign. -/
theorem homSections_units_smul {S T : SheafOfModules.{s} R} (k : ℤˣ) (f : S ⟶ T) (U : Cᵒᵖ)
    (x : S.val.obj U) : homSections (k • f) U x = (k : ℤ) • homSections f U x := by
  rw [Units.smul_def]
  exact homSections_zsmul' (k : ℤ) f U x

variable {A : DifferentialGradedAlgebra.{t, a} R}

/-- A cochain between right differential graded modules is *linear* when it commutes with the
right action of the algebra. -/
def CochainIsLinear {L L' : DifferentialGradedModule.{t, a, s} A} {k : ℤ}
    (c : Cochain L.complex L'.complex k) : Prop :=
  ∀ (p q m : ℤ) (hpq : p + k = q) (U : Cᵒᵖ) (x : (L.complex.X p).val.obj U)
    (b : (A.complex.X m).val.obj U),
    (c.v (p + m) (q + m) (by omega)).val.app U ((L.mul p m).app U x b) =
      (L'.mul q m).app U ((c.v p q hpq).val.app U x) b

/-- The morphism of right differential graded modules attached to a closed linear cochain of
degree zero. -/
noncomputable def homOfLinearCocycle {L L' : DifferentialGradedModule.{t, a, s} A}
    (c : Cochain L.complex L'.complex 0) (hc : CochainIsLinear c) (hδ : δ 0 1 c = 0) :
    L ⟶ L' where
  toHomologicalComplex := Cocycle.homOf (Cocycle.mk c 1 (zero_add 1) hδ)
  map_mul n i U x y := hc n n i (add_zero n) U x y

/-- The components of `homOfLinearCocycle c` are those of the cochain `c`. -/
theorem homOfLinearCocycle_f {L L' : DifferentialGradedModule.{t, a, s} A}
    (c : Cochain L.complex L'.complex 0) (hc : CochainIsLinear c) (hδ : δ 0 1 c = 0) (n : ℤ) :
    (homOfLinearCocycle c hc hδ).toHomologicalComplex.f n = c.v n n (add_zero n) := rfl

/-- The cochain of a morphism of right differential graded modules is linear. -/
theorem cochainIsLinear_ofHom {L L' : DifferentialGradedModule.{t, a, s} A} (g : L ⟶ L') :
    CochainIsLinear (Cochain.ofHom g.toHomologicalComplex) := by
  intro p q m hpq U x b
  obtain rfl : p = q := by omega
  simpa using g.map_mul p m U x b

namespace LocalHom

variable {K : DifferentialGradedModule.{t, a, z} A} {L L' : DifferentialGradedModule.{t, a, s} A}
  {k : ℤ} {U : C}

/-- Postcomposition of a degree-`n` local homomorphism `q : K|_U → L|_U` with a linear cochain
`c : L ⟶ L'` of degree `k`: the degree-`m` local homomorphism `c ∘ q`, where `n + k = m`. -/
def postcomp (c : Cochain L.complex L'.complex k) (hc : CochainIsLinear c) {n m : ℤ}
    (h : n + k = m) (q : LocalHom K L n U) : LocalHom K L' m U where
  app i j hij V := (homSections (c.v (i + n) j (by omega)) (op V.left)).comp (q.app i (i + n) rfl V)
  map_smul i j hij V r x := by
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, q.map_smul, homSections_smul]
  naturality i j hij {V W} g x := by
    simp only [AddMonoidHom.coe_comp, Function.comp_apply]
    rw [homSections_naturality, q.naturality]
    rfl
  isLinear i j hij p V x b := by
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, homSections_apply]
    have e : ∀ (r : ℤ) (hr : i + p + n = r),
        (c.v (i + p + n) (j + p) (by omega)).val.app (op V.left)
          (q.app (i + p) (i + p + n) rfl V ((K.mul i p).app (op V.left) x b)) =
        (c.v r (j + p) (by omega)).val.app (op V.left)
          (q.app (i + p) r hr V ((K.mul i p).app (op V.left) x b)) := by
      intro r hr; subst hr; rfl
    rw [e (i + n + p) (by omega), q.isLinear i (i + n) rfl p V x b]
    exact hc (i + n) j p (by omega) (op V.left) _ b

/-- The value of `c ∘ q` at `x` is `c (q x)`, for any choice of the intermediate degree. -/
theorem postcomp_app (c : Cochain L.complex L'.complex k) (hc : CochainIsLinear c) {n m : ℤ}
    (h : n + k = m) (q : LocalHom K L n U) (i j : ℤ) (hij : i + m = j) (r : ℤ) (hr : i + n = r)
    (V : Over U) (x : (K.complex.X i).val.obj (op V.left)) :
    (q.postcomp c hc h).app i j hij V x =
      (c.v r j (by omega)).val.app (op V.left) (q.app i r hr V x) := by
  subst hr; rfl

/-- Postcomposition is additive: `c ∘ (q + q') = c ∘ q + c ∘ q'`. -/
theorem postcomp_add_left (c : Cochain L.complex L'.complex k) (hc : CochainIsLinear c)
    {n m : ℤ} (h : n + k = m) (q q' : LocalHom K L n U) :
    (q + q').postcomp c hc h = q.postcomp c hc h + q'.postcomp c hc h :=
  LocalHom.ext fun i j hij V x => by
    simp only [postcomp, AddMonoidHom.coe_comp, Function.comp_apply, add_app, map_add]

/-- Postcomposition commutes with restriction: `c ∘ q|_{U'} = (c ∘ q)|_{U'}`. -/
theorem postcomp_restrict (c : Cochain L.complex L'.complex k) (hc : CochainIsLinear c)
    {n m : ℤ} (h : n + k = m) (q : LocalHom K L n U) {U' : C} (g : U' ⟶ U) :
    (q.restrict g).postcomp c hc h = (q.postcomp c hc h).restrict g := rfl

/-- Postcomposition is linear: `c ∘ (r q) = r (c ∘ q)`. -/
theorem postcomp_smul [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)]
    (c : Cochain L.complex L'.complex k) (hc : CochainIsLinear c)
    {n m : ℤ} (h : n + k = m) (r : R.obj.obj (op U)) (q : LocalHom K L n U) :
    (r • q).postcomp c hc h = r • q.postcomp c hc h :=
  LocalHom.ext fun i j hij V x => by
    simp only [postcomp, AddMonoidHom.coe_comp, Function.comp_apply, smul_app, homSections_smul]

end LocalHom

namespace LocalHom

variable {K : DifferentialGradedModule.{t, a, z} A} {L L' : DifferentialGradedModule.{t, a, s} A}
  {U : C}

/-- The value of `g ∘ q` at `x` is `g (q x)`, for a morphism `g` of differential graded modules. -/
private theorem postcomp_ofHom_app (g : L ⟶ L') {n : ℤ} (q : LocalHom K L n U) (i j : ℤ)
    (hij : i + n = j) (V : Over U) (x : (K.complex.X i).val.obj (op V.left)) :
    (q.postcomp (Cochain.ofHom g.toHomologicalComplex) (cochainIsLinear_ofHom g)
      (add_zero n)).app i j hij V x = (g.toHomologicalComplex.f j).val.app (op V.left)
        (q.app i j hij V x) := by
  rw [postcomp_app _ _ _ _ i j hij j hij, Cochain.ofHom_v]

/-- Postcomposition with a morphism of differential graded modules commutes with the
differential of the internal hom. -/
theorem postcomp_ofHom_diffAt (g : L ⟶ L') {n : ℤ} (q : LocalHom K L n U) :
    q.diffAt.postcomp (Cochain.ofHom g.toHomologicalComplex) (cochainIsLinear_ofHom g)
        (add_zero (n + 1)) =
      (q.postcomp (Cochain.ofHom g.toHomologicalComplex) (cochainIsLinear_ofHom g)
        (add_zero n)).diffAt :=
  LocalHom.ext fun i j hij V x => by
    rw [diffAt_app, postcomp_app _ _ _ _ i j hij j (by omega), diffAt_app,
      postcomp_ofHom_app, postcomp_ofHom_app]
    simp only [Cochain.ofHom_v, map_sub, map_zsmul]
    congr 1
    rw [← homSections_apply, ← homSections_apply, ← homSections_apply, ← homSections_apply,
      ← homSections_comp, ← homSections_comp]
    exact homSections_congr (g.toHomologicalComplex.comm (i + n) j).symm _ _

end LocalHom

variable [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)]
  {K : DifferentialGradedModule.{t, a, z} A}

/-- Postcomposition with a linear cochain, as a morphism of sheaves of modules between the
pieces of the internal homs. -/
noncomputable def postcompHom {L L' : DifferentialGradedModule.{t, a, s} A} {k : ℤ}
    (c : Cochain L.complex L'.complex k) (hc : CochainIsLinear c) {n m : ℤ} (h : n + k = m) :
    (sheafHomComplex K L).X n ⟶ (sheafHomComplex K L').X m where
  val :=
    { app := fun U => ModuleCat.ofHom
        { toFun := fun q => LocalHom.postcomp (U := U.unop) c hc h q
          map_add' := fun q q' => LocalHom.postcomp_add_left c hc h q q'
          map_smul' := fun r q => LocalHom.postcomp_smul c hc h r q }
      naturality := fun {U U'} g =>
        ModuleCat.hom_ext (LinearMap.ext fun q => by
          exact LocalHom.postcomp_restrict c hc h q g.unop) }

/-- On local sections, `postcompHom c` is postcomposition `q ↦ c ∘ q`. -/
theorem postcompHom_app {L L' : DifferentialGradedModule.{t, a, s} A} {k : ℤ}
    (c : Cochain L.complex L'.complex k) (hc : CochainIsLinear c) {n m : ℤ} (h : n + k = m)
    (U : C) (q : LocalHom K L n U) :
    (postcompHom (K := K) c hc h).val.app (op U) q = q.postcomp c hc h := rfl

/-- **Postcomposition with a linear cochain `c` of degree `k`**, as a cochain of degree `k`
between the internal homs: `SheafHom^dg(K, L) ⟶ SheafHom^dg(K, L')`, `q ↦ c ∘ q`. -/
noncomputable def sheafHomCochain {L L' : DifferentialGradedModule.{t, a, s} A} {k : ℤ}
    (c : Cochain L.complex L'.complex k) (hc : CochainIsLinear c) :
    Cochain (sheafHomComplex K L) (sheafHomComplex K L') k :=
  Cochain.mk fun _ _ h => postcompHom c hc h

/-- The components of `sheafHomCochain c` are the morphisms `postcompHom c`. -/
theorem sheafHomCochain_v {L L' : DifferentialGradedModule.{t, a, s} A} {k : ℤ}
    (c : Cochain L.complex L'.complex k) (hc : CochainIsLinear c) (n m : ℤ) (h : n + k = m) :
    (sheafHomCochain (K := K) c hc).v n m h = postcompHom c hc h :=
  Cochain.mk_v _ _ _ _

/-- On local sections, the differential of the internal hom complex is
`SheafOfModules.LocalHom.diffTo`. -/
theorem homSections_sheafHomComplex_d {L : DifferentialGradedModule.{t, a, s} A} (n m : ℤ)
    (h : n + 1 = m) (U : C) (q : ((sheafHomComplex K L).X n).val.obj (op U)) :
    homSections ((sheafHomComplex K L).d n m) (op U) q =
      (LocalHom.diffTo (U := U) q m h : LocalHom K L m U) := by
  subst h
  rw [sheafHomComplex_d_self]
  rfl

/-- On local sections, `postcompHom c` is `SheafOfModules.LocalHom.postcomp`. -/
theorem homSections_postcompHom {L L' : DifferentialGradedModule.{t, a, s} A} {k : ℤ}
    (c : Cochain L.complex L'.complex k) (hc : CochainIsLinear c) {n m : ℤ} (h : n + k = m)
    (U : C) (q : ((sheafHomComplex K L).X n).val.obj (op U)) :
    homSections (postcompHom (K := K) c hc h) (op U) q =
      (LocalHom.postcomp (U := U) c hc h q : LocalHom K L' m U) := rfl

/-- **Postcomposition commutes with the differentials**: the internal hom of the differential
`δ c = d ∘ c - (-1)^k c ∘ d` of a linear cochain is the differential of its internal hom. -/
theorem sheafHomCochain_delta {L L' : DifferentialGradedModule.{t, a, s} A} {k : ℤ}
    (c : Cochain L.complex L'.complex k) (hc : CochainIsLinear c)
    (hδ : CochainIsLinear (δ k (k + 1) c)) :
    δ k (k + 1) (sheafHomCochain (K := K) c hc) = sheafHomCochain (δ k (k + 1) c) hδ := by
  refine Cochain.ext _ _ fun p q hpq => ?_
  obtain rfl : q = p + k + 1 := by omega
  rw [δ_v k (k + 1) rfl _ p (p + k + 1) hpq (p + k) (p + 1) (by omega) rfl,
    sheafHomCochain_v, sheafHomCochain_v, sheafHomCochain_v]
  refine hom_ext_sections fun U f => ?_
  induction U using Opposite.rec with | op U => ?_
  rw [homSections_add, homSections_comp, homSections_units_smul, homSections_comp,
    homSections_postcompHom, homSections_sheafHomComplex_d, homSections_sheafHomComplex_d,
    homSections_postcompHom, homSections_postcompHom]
  all_goals try rfl
  refine LocalHom.ext fun i j hij V x => ?_
  rw [LocalHom.add_app, LocalHom.zsmul_app, LocalHom.diffTo_app,
    LocalHom.postcomp_app c hc _ _ i j hij (i + (p + 1)) (by omega), LocalHom.diffTo_app,
    localDiffApp_eq _ _ i j (i + (p + k)) (i + 1) hij rfl (by omega),
    localDiffApp_eq _ _ i (i + (p + 1)) (i + p) (i + 1) rfl rfl (by omega),
    LocalHom.postcomp_app c hc _ _ i (i + (p + k)) rfl (i + p) rfl,
    LocalHom.postcomp_app c hc _ _ (i + 1) j (by omega) (i + 1 + p) (by omega),
    LocalHom.postcomp_app (δ k (k + 1) c) hδ _ _ i j hij (i + p) rfl,
    δ_v k (k + 1) rfl c (i + p) j (by omega) (i + (p + k)) (i + p + 1) (by omega) rfl]
  conv_rhs => rw [← homSections_apply, homSections_add, homSections_comp,
    homSections_units_smul, homSections_comp]
  simp only [homSections_apply, map_add, map_zsmul]
  have e₁ : ∀ (r r' : ℤ) (hr : i + p + 1 = r) (hr' : i + p + 1 = r') (h₁ : r + k = j)
      (h₂ : r' + k = j),
      (c.v r j h₁).val.app (op V.left) ((L.complex.d (i + p) r).val.app (op V.left)
        (f.app i (i + p) rfl V x)) =
      (c.v r' j h₂).val.app (op V.left) ((L.complex.d (i + p) r').val.app (op V.left)
        (f.app i (i + p) rfl V x)) := by
    intro r r' hr hr' _ _; subst hr; subst hr'; rfl
  have e₂ : ∀ (r r' : ℤ) (hr : i + 1 + p = r) (hr' : i + 1 + p = r') (h₁ : r + k = j)
      (h₂ : r' + k = j),
      (c.v r j h₁).val.app (op V.left) (f.app (i + 1) r hr V
        ((K.complex.d i (i + 1)).val.app (op V.left) x)) =
      (c.v r' j h₂).val.app (op V.left) (f.app (i + 1) r' hr' V
        ((K.complex.d i (i + 1)).val.app (op V.left) x)) := by
    intro r r' hr hr' _ _; subst hr; subst hr'; rfl
  rw [e₁ (i + (p + 1)) (i + p + 1) (by omega) rfl (by omega) (by omega),
    e₂ (i + (p + 1)) (i + 1 + p) (by omega) rfl (by omega) (by omega)]
  rw [smul_add, smul_smul, ← Units.val_mul, ← Int.negOnePow_add,
    show k + 1 + (p + 1) = p + k + 1 + 1 by ring, Int.negOnePow_succ (p + k + 1),
    Units.val_neg, neg_smul]
  abel

/-- Equal linear cochains have equal internal homs. -/
theorem sheafHomCochain_congr {L L' : DifferentialGradedModule.{t, a, s} A} {k : ℤ}
    {c c' : Cochain L.complex L'.complex k} (h : c = c') (hc : CochainIsLinear c)
    (hc' : CochainIsLinear c') :
    sheafHomCochain (K := K) c hc = sheafHomCochain c' hc' := by
  subst h; rfl

omit [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)] in
/-- The difference of two linear cochains is linear. -/
theorem cochainIsLinear_sub {L L' : DifferentialGradedModule.{t, a, s} A} {k : ℤ}
    {c c' : Cochain L.complex L'.complex k} (hc : CochainIsLinear c)
    (hc' : CochainIsLinear c') : CochainIsLinear (c - c') := by
  intro p q m hpq U x b
  simp only [Cochain.sub_v]
  rw [← homSections_apply, homSections_sub, homSections_apply,
    homSections_apply, hc, hc', ← homSections_apply (c.v p q hpq - c'.v p q hpq), homSections_sub,
    map_sub, AddMonoidHom.sub_apply]
  rfl

/-- The internal hom of a difference of linear cochains is the difference of their internal
homs. -/
theorem sheafHomCochain_sub {L L' : DifferentialGradedModule.{t, a, s} A} {k : ℤ}
    (c c' : Cochain L.complex L'.complex k) (hc : CochainIsLinear c)
    (hc' : CochainIsLinear c') :
    sheafHomCochain (K := K) (c - c') (cochainIsLinear_sub hc hc') =
      sheafHomCochain c hc - sheafHomCochain c' hc' := by
  refine Cochain.ext _ _ fun p q hpq => ?_
  rw [Cochain.sub_v, sheafHomCochain_v, sheafHomCochain_v, sheafHomCochain_v]
  refine hom_ext_sections fun U f => ?_
  induction U using Opposite.rec with | op U => ?_
  rw [homSections_sub, homSections_postcompHom, homSections_postcompHom,
    homSections_postcompHom]
  refine LocalHom.ext fun i j hij V x => ?_
  rw [LocalHom.sub_app, LocalHom.postcomp_app _ _ _ _ i j hij (i + p) rfl,
    LocalHom.postcomp_app _ _ _ _ i j hij (i + p) rfl,
    LocalHom.postcomp_app _ _ _ _ i j hij (i + p) rfl, Cochain.sub_v, ← homSections_apply,
    homSections_sub]
  rfl

/-! ### Homotopies as cochains of degree `-1` -/

section HomotopyCochain

variable {M M' : DifferentialGradedModule.{t, a, s} A} {f g : M ⟶ M'}

/-- A component of a cochain followed by the identification `G.X j = G.X j'` is the component
with target `j'`. -/
theorem linearCochain_v_comp_eqToHom {B : Type*} [Category B] [Preadditive B]
    {F G : CochainComplex B ℤ} {k i j j' : ℤ}
    (c : Cochain F G k) (h : i + k = j) (h' : i + k = j') (e : j = j') :
    c.v i j h ≫ eqToHom (congrArg G.X e) = c.v i j' h' := by
  cases e
  simp

omit [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)] in
/-- The components of a cochain with equal target degrees take heterogeneously equal values on
a local section. -/
theorem linearCochain_v_app_heq {F G : CochainComplex (SheafOfModules.{s} R) ℤ}
    {k i j j' : ℤ} (c : Cochain F G k) (h : i + k = j) (h' : i + k = j') (e : j = j')
    (U : Cᵒᵖ) (x : (F.X i).val.obj U) :
    HEq ((c.v i j h).val.app U x) ((c.v i j' h').val.app U x) := by
  cases e
  rfl

omit [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)] in
/-- The identification `F i = F j` of an equality of indices leaves a local section
heterogeneously unchanged. -/
theorem sheafEqToHom_app_heq (F : ℤ → SheafOfModules.{s} R) {i j : ℤ} (h : i = j) (U : Cᵒᵖ)
    (x : (F i).val.obj U) : HEq ((eqToHom (congrArg F h)).val.app U x) x := by
  cases h
  rfl

/-- The degree `-1` cochain of a homotopy. -/
noncomputable def DifferentialGradedModule.Homotopy.toCochain
    (H : DifferentialGradedModule.Homotopy f g) : Cochain M.complex M'.complex (-1) :=
  Cochain.mk fun p q hpq => H.app p ≫ eqToHom (congrArg M'.complex.X (by omega : p - 1 = q))

omit [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)] in
/-- The component of `H.toCochain` from degree `p` is `H.app p`, with target `p - 1`. -/
theorem DifferentialGradedModule.Homotopy.toCochain_v
    (H : DifferentialGradedModule.Homotopy f g) (p q : ℤ) (hpq : p + -1 = q) :
    H.toCochain.v p q hpq =
      H.app p ≫ eqToHom (congrArg M'.complex.X (by omega : p - 1 = q)) :=
  Cochain.mk_v _ _ _ _

omit [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)] in
/-- The cochain of a homotopy of differential graded modules is linear. -/
theorem DifferentialGradedModule.Homotopy.toCochain_isLinear
    (H : DifferentialGradedModule.Homotopy f g) : CochainIsLinear H.toCochain := by
  intro p q m hpq U x b
  obtain rfl : q = p - 1 := by omega
  rw [H.toCochain_v, H.toCochain_v]
  refine eq_of_heq ?_
  refine (sheafEqToHom_app_heq M'.complex.X (show p + m - 1 = p - 1 + m by omega) U _).trans ?_
  refine (H.map_mul p m U x b).trans ?_
  have e : ∀ (r : ℤ) (hr : p - 1 = r) (y : (M'.complex.X (p - 1)).val.obj U),
      HEq ((M'.mul (p - 1) m).app U y b)
        ((M'.mul r m).app U ((eqToHom (congrArg M'.complex.X hr)).val.app U y) b) := by
    intro r hr y; subst hr; rfl
  exact e (p - 1) rfl ((H.app p).val.app U x)

omit [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)] in
/-- The cochain of the underlying homotopy of complexes is `H.toCochain`. -/
theorem DifferentialGradedModule.Homotopy.ofHomotopy_toComplexHomotopy
    (H : DifferentialGradedModule.Homotopy f g) :
    Cochain.ofHomotopy H.toComplexHomotopy = H.toCochain := by
  refine Cochain.ext _ _ fun p q hpq => ?_
  obtain rfl : q = p - 1 := by omega
  rw [H.toCochain_v]
  simp [Cochain.ofHomotopy, DifferentialGradedModule.Homotopy.toComplexHomotopy,
    show p - 1 + 1 = p by omega]

omit [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)] in
/-- The differential of the cochain of a homotopy from `f` to `g` is `f - g`. -/
theorem DifferentialGradedModule.Homotopy.delta_toCochain
    (H : DifferentialGradedModule.Homotopy f g) :
    δ (-1) 0 H.toCochain = Cochain.ofHom f.toHomologicalComplex -
      Cochain.ofHom g.toHomologicalComplex := by
  rw [← H.ofHomotopy_toComplexHomotopy, δ_ofHomotopy]

/-- A homotopy of differential graded modules from a linear cochain of degree `-1` whose
differential is the difference of the two morphisms. -/
noncomputable def homotopyOfCochain (c : Cochain M.complex M'.complex (-1)) (hc : CochainIsLinear c)
    (hδ : δ (-1) 0 c = Cochain.ofHom f.toHomologicalComplex -
      Cochain.ofHom g.toHomologicalComplex) :
    DifferentialGradedModule.Homotopy f g where
  app n := c.v n (n - 1) (by omega)
  map_mul n m U x b :=
    (linearCochain_v_app_heq c _ _ (show n - 1 + m = n + m - 1 by omega) U _).symm.trans
      (heq_of_eq (hc n (n - 1) m (by omega) U x b))
  comm n := by
    have hn := Cochain.congr_v hδ n n (add_zero n)
    rw [δ_v (-1) 0 rfl c n n (add_zero n) (n - 1) (n + 1) rfl rfl] at hn
    simp only [Cochain.sub_v, Cochain.ofHom_v, Int.negOnePow_zero, one_smul] at hn
    rw [← hn, Category.assoc, linearCochain_v_comp_eqToHom]
    omega

end HomotopyCochain

end Postcomp


section Module

variable {A A' : DifferentialGradedAlgebra.{t, a} R} (N : DifferentialGradedBimodule.{t, a, z} A A')
  [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)]

/-- The action `(q a)(x) = q (a x)`, as a bilinear map of sheaves of modules. -/
noncomputable def sheafHomMul (M : DifferentialGradedModule.{t, a, s} A') (n p : ℤ) :
    BilinearMap ((sheafHomComplex N.toRightModule M).X n) (A.complex.X p)
      ((sheafHomComplex N.toRightModule M).X (n + p)) where
  app U := AddMonoidHom.mk' (fun q => AddMonoidHom.mk' (fun b => LocalHom.actLeft (U := U.unop) q b)
      (fun b b' => LocalHom.actLeft_add_right q b b'))
    (fun q q' => AddMonoidHom.ext fun b => LocalHom.actLeft_add_left q q' b)
  map_smul_left U r q b := LocalHom.actLeft_smul_left (U := U.unop) r q b
  map_smul_right U r q b := LocalHom.actLeft_smul_right (U := U.unop) r q b
  naturality g q b := LocalHom.restrict_actLeft q b g.unop

/-- On local sections, `sheafHomMul` is the action `SheafOfModules.LocalHom.actLeft`. -/
theorem sheafHomMul_app (M : DifferentialGradedModule.{t, a, s} A') (n p : ℤ) (U : C)
    (q : LocalHom N.toRightModule M n U) (b : (A.complex.X p).val.obj (op U)) :
    (sheafHomMul N M n p).app (op U) q b = q.actLeft b := rfl

/-- **The internal hom `SheafHom^dg_{A'}(N, M)` of a differential graded `(A, A')`-bimodule `N`
and a right differential graded `A'`-module `M`**, as a right differential graded `A`-module: the
complex of sheaves of local homomorphisms `N|_U → M|_U`, with `(q a)(x) = q (a x)`. -/
noncomputable abbrev sheafHomModule (M : DifferentialGradedModule.{t, a, s} A') :
    DifferentialGradedModule.{t, a, max u v z s} A where
  complex := sheafHomComplex N.toRightModule M
  mul := sheafHomMul N M
  mul_assoc n i j U q b b' := LocalHom.actLeft_actLeft (U := U.unop) q b b'
  mul_one n U q := LocalHom.actLeft_one (U := U.unop) q
  leibniz n i U q b := by
    change ((sheafHomComplex N.toRightModule M).d (n + i) (n + i + 1)).val.app U
      (LocalHom.actLeft (U := U.unop) q b) = _
    rw [sheafHomComplex_d_self, sheafHomComplex_d_self]
    exact LocalHom.diffAt_actLeft q b

/-- The underlying complex of `sheafHomModule N M` is the internal hom complex. -/
theorem sheafHomModule_complex (M : DifferentialGradedModule.{t, a, s} A') :
    (sheafHomModule N M).complex = sheafHomComplex N.toRightModule M := rfl

end Module

section Functor

open CochainComplex.HomComplex

variable {A A' : DifferentialGradedAlgebra.{t, a} R} {N : DifferentialGradedBimodule.{t, a, z} A A'}

namespace LocalHom

/-- Postcomposition commutes with the action `(q a)(x) = q (a x)`. -/
theorem postcomp_actLeft {L L' : DifferentialGradedModule.{t, a, s} A'} {k : ℤ}
    (c : Cochain L.complex L'.complex k) (hc : CochainIsLinear c) {n m p : ℤ} (h : n + k = m)
    (h' : n + p + k = m + p) {U : C} (q : LocalHom N.toRightModule L n U)
    (b : (A.complex.X p).val.obj (op U)) :
    (q.actLeft b).postcomp c hc h' = (q.postcomp c hc h).actLeft b :=
  LocalHom.ext fun i j hij V x => by
    rw [postcomp_app c hc h' _ i j hij (p + i + n) (by omega), actLeft_app, actLeft_app,
      postcomp_app c hc h _ (p + i) j (by omega) (p + i + n) rfl]

end LocalHom

variable [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)]

/-- The internal hom of a linear cochain is linear for the action of `A`. -/
theorem cochainIsLinear_sheafHomCochain {L L' : DifferentialGradedModule.{t, a, s} A'} {k : ℤ}
    (c : Cochain L.complex L'.complex k) (hc : CochainIsLinear c) :
    CochainIsLinear (L := sheafHomModule N L) (L' := sheafHomModule N L')
      (sheafHomCochain (K := N.toRightModule) c hc) := by
  intro n m p hnm U q b
  induction U using Opposite.rec with | op U => ?_
  rw [sheafHomCochain_v, sheafHomCochain_v]
  exact LocalHom.postcomp_actLeft c hc hnm (by omega) q b

/-- The internal hom of the zero cochain is zero. -/
theorem sheafHomCochain_zero {L L' : DifferentialGradedModule.{t, a, s} A'} {k : ℤ}
    (hc : CochainIsLinear (0 : Cochain L.complex L'.complex k)) :
    sheafHomCochain (K := N.toRightModule) (0 : Cochain L.complex L'.complex k) hc = 0 := by
  have h := (sheafHomCochain_congr (K := N.toRightModule)
    (sub_self (0 : Cochain L.complex L'.complex k)).symm hc (cochainIsLinear_sub hc hc)).trans
    (sheafHomCochain_sub (K := N.toRightModule) (0 : Cochain L.complex L'.complex k) 0 hc hc)
  rw [sub_self] at h
  exact h

/-- Postcomposition with a morphism of differential graded modules is a cocycle. -/
theorem sheafHomCochain_ofHom_delta {L L' : DifferentialGradedModule.{t, a, s} A'} (g : L ⟶ L') :
    δ 0 1 (sheafHomCochain (K := N.toRightModule) (Cochain.ofHom g.toHomologicalComplex)
      (cochainIsLinear_ofHom g)) = 0 := by
  have hz : CochainIsLinear (0 : Cochain L.complex L'.complex 1) := by
    intro p q m hpq U x b
    simp only [Cochain.zero_v]
    rw [← homSections_apply, homSections_zero, ← homSections_apply, homSections_zero, map_zero,
      AddMonoidHom.zero_apply]
  have h0 : CochainIsLinear (δ 0 1 (Cochain.ofHom g.toHomologicalComplex)) := by
    rw [δ_ofHom]; exact hz
  refine (sheafHomCochain_delta _ _ h0).trans ?_
  exact (sheafHomCochain_congr (δ_ofHom _) h0 hz).trans (sheafHomCochain_zero hz)

/-- The action of `SheafHom^dg_{A'}(N, -)` on a morphism `g`: postcomposition with `g`. -/
noncomputable def sheafHomMap {L L' : DifferentialGradedModule.{t, a, s} A'} (g : L ⟶ L') :
    sheafHomModule N L ⟶ sheafHomModule N L' :=
  homOfLinearCocycle _ (cochainIsLinear_sheafHomCochain _ (cochainIsLinear_ofHom g))
    (sheafHomCochain_ofHom_delta g)

/-- On local sections, `sheafHomMap g` is postcomposition `q ↦ g ∘ q`. -/
theorem sheafHomMap_f_app {L L' : DifferentialGradedModule.{t, a, s} A'} (g : L ⟶ L') (n : ℤ)
    (U : C) (q : LocalHom N.toRightModule L n U) :
    ((sheafHomMap g).toHomologicalComplex.f n).val.app (op U) q =
      q.postcomp (Cochain.ofHom g.toHomologicalComplex) (cochainIsLinear_ofHom g)
        (add_zero n) := rfl

variable (N) in
/-- **The functor `SheafHom^dg_{A'}(N, -) : Mod^dg(A', d) ⥤ Mod^dg(A, d)`** of a differential
graded `(A, A')`-bimodule `N`. -/
noncomputable def sheafHomFunctor :
    DifferentialGradedModule.{t, a, s} A' ⥤ DifferentialGradedModule.{t, a, max u v z s} A where
  obj M := sheafHomModule N M
  map g := sheafHomMap g
  map_id M := DifferentialGradedModule.Hom.ext fun n => hom_ext_sections fun U q => by
    induction U using Opposite.rec with | op U => ?_
    refine LocalHom.ext fun i j hij V x => ?_
    rw [homSections_apply, sheafHomMap_f_app,
      LocalHom.postcomp_app _ _ _ _ i j hij j (by omega), Cochain.ofHom_v]
    rfl
  map_comp g g' := DifferentialGradedModule.Hom.ext fun n => hom_ext_sections fun U q => by
    induction U using Opposite.rec with | op U => ?_
    refine LocalHom.ext fun i j hij V x => ?_
    rw [DifferentialGradedModule.comp_f, homSections_apply, sheafHomMap_f_app,
      LocalHom.postcomp_app _ _ _ _ i j hij j (by omega), Cochain.ofHom_v]
    change _ = ((((sheafHomMap g').toHomologicalComplex.f n).val.app (op U))
      ((sheafHomMap g).toHomologicalComplex.f n |>.val.app (op U) q)).app i j hij V x
    rw [sheafHomMap_f_app, sheafHomMap_f_app,
      LocalHom.postcomp_app _ _ _ _ i j hij j (by omega), Cochain.ofHom_v,
      LocalHom.postcomp_app _ _ _ _ i j hij j (by omega), Cochain.ofHom_v]
    rfl

/-- The internal hom of the cochain of a morphism `g` is the cochain of `sheafHomMap g`. -/
theorem sheafHomCochain_ofHom {L L' : DifferentialGradedModule.{t, a, s} A'} (g : L ⟶ L') :
    sheafHomCochain (K := N.toRightModule) (Cochain.ofHom g.toHomologicalComplex)
      (cochainIsLinear_ofHom g) = Cochain.ofHom (sheafHomMap (N := N) g).toHomologicalComplex := by
  refine Cochain.ext _ _ fun p q hpq => ?_
  obtain rfl : q = p := by omega
  rw [Cochain.ofHom_v]
  rfl

variable (N) in
/-- The internal hom `SheafHom^dg_{A'}(N, M)` constructed here *is* the internal hom, with the
right `A`-action of the source. -/
noncomputable def isSheafHom_sheafHomModule (M : DifferentialGradedModule.{t, a, s} A') :
    IsSheafHom N M (sheafHomModule N M) where
  isInternalHom := isInternalHom_sheafHomComplex N.toRightModule M
  mul_spec _ _ _ _ _ _ _ _ _ _ := rfl

variable (N) in
/-- **The internal hom functor `SheafHom^dg_{A'}(N, -)`, constructed**, with the identification
of its values with the internal homs and of its action on morphisms with postcomposition. -/
noncomputable def sheafHomFunctorData : SheafHomFunctorData.{t, a, max u v z s, s, z} N where
  functor := sheafHomFunctor N
  isSheafHom M := isSheafHom_sheafHomModule N M
  map_spec g n U q i j hij V x := by
    refine (LocalHom.postcomp_app (U := U) _ (cochainIsLinear_ofHom g) (add_zero n)
      (q : LocalHom N.toRightModule _ n U) i j hij j (by omega) V x).trans ?_
    rw [Cochain.ofHom_v]
    rfl

variable (N) in
/-- **The internal hom functor carries homotopies to homotopies**: the image of a homotopy `h`
is `q ↦ h ∘ q`, the differential graded extension of `SheafHom^dg_{A'}(N, -)`. -/
noncomputable def sheafHomHomotopyExtension : (sheafHomFunctorData N).HomotopyExtension where
  mapHomotopy {M M₂ ψ χ} H := by
    have hl := cochainIsLinear_sub (cochainIsLinear_ofHom ψ) (cochainIsLinear_ofHom χ)
    have hδ : CochainIsLinear (δ (-1) (-1 + 1) H.toCochain) := by
      rw [show (-1 : ℤ) + 1 = 0 from rfl, H.delta_toCochain]; exact hl
    refine homotopyOfCochain (sheafHomCochain H.toCochain H.toCochain_isLinear)
      (cochainIsLinear_sheafHomCochain _ _) ?_
    refine (sheafHomCochain_delta _ _ hδ).trans ?_
    refine (sheafHomCochain_congr H.delta_toCochain hδ hl).trans ?_
    rw [sheafHomCochain_sub _ _ (cochainIsLinear_ofHom ψ) (cochainIsLinear_ofHom χ),
      sheafHomCochain_ofHom, sheafHomCochain_ofHom]
    rfl

end Functor

end SheafOfModules
