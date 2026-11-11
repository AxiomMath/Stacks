module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedPushforward
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedForgetRightAdjoint
public import StacksCore.Tactic.StacksAttribute

/-!
# Pull and push for sheaves of graded modules: the adjunction

Let `f : (C, J, R) ⟶ (C', J', R')` be a morphism of ringed sites, presented as a functor
`u : C' ⥤ C` in the direction opposite to `f` together with the structure map `σ : R' ⟶ f_*R`,
let `A` be a sheaf of graded `R`-algebras, let `B` be a sheaf of graded `R'`-algebras and let
`φ : B ⟶ f_*A` be a homomorphism of sheaves of graded algebras. The direct image
`f_* : Mod(A) ⥤ Mod(B)` and its graded enhancement `f_* : Mod^gr(A) ⥤ Mod^gr(B)` are
constructed in `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedPushforward.lean`. This file
proves the adjunction

`Hom_{Mod^gr(B)}(N, f_*M) = Hom_{Mod^gr(A)}(f^*N, M)`

in every homogeneous degree, for `f^*N = f^{-1}N ⊗_{f^{-1}B, φ} A` presented by its universal
property: a `φ`-semilinear homomorphism out of `N` into a right graded `A`-module factors
uniquely through the unit `N ⟶ f^*N`.

## Main definitions

* `SheafOfModules.GradedModule.SemilinearHom.postcomp` and `precomp` compose a `φ`-semilinear
  homomorphism of right graded modules with a homomorphism on either side.
* `SheafOfModules.GradedModule.IsPullback` is the universal property of the unit
  `θ : N ⟶ f^*N`, and `SheafOfModules.GradedModule.PullbackData` is a pullback of every right
  graded `B`-module at once, with its units and their universal property;
  `SheafOfModules.GradedModule.PullbackData.functor` is the resulting
  `f^* : Mod(B) ⥤ Mod(A)`.
* `SheafOfModules.GradedModule.SemilinearHomOfDegree` is a `φ`-semilinear homomorphism of right
  graded modules homogeneous of degree `n`, the morphisms of degree `n` from `N` to `M` of the
  graded category underlying the semilinear setting.

## Main results

* `SheafOfModules.GradedModule.SemilinearHomOfDegree.shiftEquiv` and
  `SheafOfModules.GradedHomOfDegree.shiftHomEquiv`: a homomorphism homogeneous of degree `n`
  into `M`, semilinear or not, is a degree-zero homomorphism into the shift `M⟨n⟩`.
* `SheafOfModules.GradedModule.semilinearHomOfDegreeEquiv`: **`f_*M` corepresents the
  `φ`-semilinear homomorphisms into `M` homogeneous of degree `n`**, that is, those are exactly
  the degree-`n` homogeneous homomorphisms `N ⟶ f_*M` of right graded `B`-modules.
* `SheafOfModules.GradedModule.PullbackData.homOfDegreeEquiv`: **the adjunction in every
  degree**, `Hom^n(f^*N, M) = Hom^n(N, f_*M)`, natural in both arguments.
* `SheafOfModules.GradedModule.PullbackData.homEquivPushforward` and
  `pullbackPushforwardAdjunction`: its degree-zero case, and that case as an adjunction
  `f^* ⊣ f_*` of the two functors.

## Implementation notes

The pullback enters here **through its universal property**: `PullbackData` carries the pullback
of every right graded `B`-module together with the universal property that determines it up to
unique isomorphism, in the shape used for sheaves of differential graded modules in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedPullback.lean`, and
`PullbackData.homOfDegreeEquiv` is the identification of the source read against such a datum.
That such a datum exists for every `φ` is
`SheafOfModules.GradedModule.pullbackData` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedModulePullbackConstruction.lean`, which
obtains the pullback as the left adjoint of the direct image. The explicit pullback
`f⁻¹N ⊗_{f⁻¹B, φ} A` of the source is a datum too,
`SheafOfModules.GradedTensorPullback.tensorPullbackData` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedModulePullbackTensor.lean`; the tag's
attribute sits there, on
`SheafOfModules.GradedTensorPullback.tensorPullbackHomOfDegreeEquiv`, which is
`PullbackData.homOfDegreeEquiv` at that datum. What this file contributes is the other half of
the source's proof: the universal property is at degree zero only, and the degree-`n` statement
is obtained from it by shifting the target, together with `semilinearHomOfDegreeEquiv`, which is
the corepresentability of `f_*M` by `φ`-semilinear maps in degree `n`.

The degree bookkeeping of the shift is the one of
`SheafOfModules.GradedModule.shift`: the degree-`i` piece of `M⟨n⟩` is the degree-`i + n` piece
of `M`, and its action transports along `i + n + p = i + p + n`. A homogeneous homomorphism of
degree `n` indexes its components by a pair `i, j` with `i + n = j` rather than by `i` alone,
so both shift identifications insert exactly one `SheafOfModules.castHom` for that transport;
`SheafOfModules.GradedHomOfDegree.app_castHom` and
`SheafOfModules.GradedModule.SemilinearHomOfDegree.app_castHom` are the lemmas that move the
target index, the counterparts of the existing
`SheafOfModules.GradedHomOfDegree.app_congr_heq` for the source index.

The two sheaves of rings share the universe of their values because the structure map relates
them, and the module sections of a sheaf and of its direct image share theirs because
`SheafOfModules.pushforward` preserves them; the universes of the two sites, their morphisms and
the two algebras are independent.

## References

* [Stacks Project, Tag 0FR8](https://stacks.math.columbia.edu/tag/0FR8)
* [Stacks Project, Tag 0FR7](https://stacks.math.columbia.edu/tag/0FR7)
* [Stacks Project, Tag 0FR1](https://stacks.math.columbia.edu/tag/0FR1)
-/

@[expose] public section

open CategoryTheory

universe t a m v u a' v' u'

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {C' : Type u'} [Category.{v'} C'] {J' : GrothendieckTopology C'} {R' : Sheaf J' RingCat.{t}}

namespace GradedHomOfDegree

variable {A : GradedAlgebra.{t, a} R} {M L : GradedModule.{t, a, m} A}

/-- The value of a homogeneous homomorphism in a propositionally different target degree is the
transport of its value. -/
theorem app_castHom {n : ℤ} (f : GradedHomOfDegree M L n) {i j j' : ℤ} (hij : i + n = j)
    (hij' : i + n = j') (U : Cᵒᵖ) (x : (M.piece i).val.obj U) :
    (f.app i j' hij').val.app U x =
      castHom L.piece (by omega : j = j') U ((f.app i j hij).val.app U x) := by
  obtain rfl : j = j' := by omega
  rfl

/-- **A homogeneous homomorphism of degree `n` into `M` is a degree-zero homomorphism into the
shift `M⟨n⟩`.** -/
noncomputable def shiftHomEquiv (M L : GradedModule.{t, a, m} A) (n : ℤ) :
    GradedHomOfDegree M L n ≃ (M ⟶ L.shift n) where
  toFun f :=
    { app := fun i => f.app i (i + n) rfl
      map_smul := fun i p U x b => by
        rw [f.app_castHom (j := i + n + p) (by omega) (by omega),
          f.map_mul i (i + n) rfl p U x b]
        exact (L.shift_smul n i p U ((f.app i (i + n) rfl).val.app U x) b).symm }
  invFun g :=
    { app := fun i j hij => g.app i ≫ degCastHom L.piece hij
      map_mul := fun i j hij p U x b => by
        change homSections (degCastHom L.piece (by omega : i + p + n = j + p)) U
            ((g.app (i + p)).val.app U (M.smul i p U x b)) =
          L.smul j p U (homSections (degCastHom L.piece hij) U ((g.app i).val.app U x)) b
        rw [homSections_degCastHom, homSections_degCastHom, g.map_smul i p U x b,
          L.shift_smul n i p U ((g.app i).val.app U x) b, Cofree.smul_castHom_left,
          Cofree.castHom_castHom] }
  left_inv f := ext fun i j hij => by
    subst hij
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    ext x
    rfl
  right_inv g := GradedModule.Hom.ext fun i => by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    ext x
    rfl

end GradedHomOfDegree

namespace GradedModule

variable {u : C' ⥤ C} [u.IsContinuous J' J] {σ : R'.obj ⟶ u.op ⋙ R.obj}
  {A : GradedAlgebra.{t, a} R} {B : GradedAlgebra.{t, a'} R'}

section Composition

variable {φ : GradedAlgebra.SemilinearHom u σ B A}

omit [u.IsContinuous J' J]

namespace SemilinearHom

/-- Postcomposition of a `φ`-semilinear homomorphism of right graded modules with a
homomorphism of right graded `A`-modules on the target. -/
noncomputable def postcomp {P : GradedModule.{t, a', m} B} {M M' : GradedModule.{t, a, m} A}
    (θ : SemilinearHom φ P M) (h : M ⟶ M') : SemilinearHom φ P M' where
  app i V := (homSections (h.app i) (u.op.obj V)).comp (θ.app i V)
  map_smul i V s x := by
    change homSections (h.app i) (u.op.obj V) (θ.app i V (s • x)) =
      (σ.app V).hom s • homSections (h.app i) (u.op.obj V) (θ.app i V x)
    rw [θ.map_smul]
    exact homSections_smul _ _ _ _
  naturality i {V W} k x := by
    change homSections (h.app i) (u.op.obj W) (θ.app i W ((P.piece i).val.map k x)) =
      (M'.piece i).val.map (u.op.map k)
        (homSections (h.app i) (u.op.obj V) (θ.app i V x))
    rw [θ.naturality]
    exact (homSections_naturality (h.app i) (u.op.map k) (θ.app i V x)).symm
  map_smul_right n i V x b := by
    change homSections (h.app (n + i)) (u.op.obj V) (θ.app (n + i) V (P.smul n i V x b)) =
      M'.smul n i (u.op.obj V) (homSections (h.app n) (u.op.obj V) (θ.app n V x)) (φ.app i V b)
    rw [θ.map_smul_right]
    exact h.map_smul n i (u.op.obj V) (θ.app n V x) (φ.app i V b)

/-- The postcomposite `θ.postcomp h` sends a section `x` of `P` in degree `i` to `h (θ x)`. -/
@[simp]
theorem postcomp_app {P : GradedModule.{t, a', m} B} {M M' : GradedModule.{t, a, m} A}
    (θ : SemilinearHom φ P M) (h : M ⟶ M') (i : ℤ) (V : C'ᵒᵖ) (x : (P.piece i).val.obj V) :
    (θ.postcomp h).app i V x = homSections (h.app i) (u.op.obj V) (θ.app i V x) :=
  rfl

/-- Precomposition of a `φ`-semilinear homomorphism of right graded modules with a homomorphism
of right graded `B`-modules on the source. -/
noncomputable def precomp {P P' : GradedModule.{t, a', m} B} {M : GradedModule.{t, a, m} A}
    (θ : SemilinearHom φ P' M) (g : P ⟶ P') : SemilinearHom φ P M where
  app i V := (θ.app i V).comp (homSections (g.app i) V)
  map_smul i V s x := by
    have e : homSections (g.app i) V (s • x) = s • homSections (g.app i) V x :=
      homSections_smul _ _ _ _
    change θ.app i V (homSections (g.app i) V (s • x)) =
      (σ.app V).hom s • θ.app i V (homSections (g.app i) V x)
    rw [e, θ.map_smul]
  naturality i {V W} k x := by
    have e : homSections (g.app i) W ((P.piece i).val.map k x) =
        (P'.piece i).val.map k (homSections (g.app i) V x) :=
      (homSections_naturality (g.app i) k x).symm
    change θ.app i W (homSections (g.app i) W ((P.piece i).val.map k x)) =
      (M.piece i).val.map (u.op.map k) (θ.app i V (homSections (g.app i) V x))
    rw [e, θ.naturality]
  map_smul_right n i V x b := by
    change θ.app (n + i) V ((g.app (n + i)).val.app V (P.smul n i V x b)) =
      M.smul n i (u.op.obj V) (θ.app n V ((g.app n).val.app V x)) (φ.app i V b)
    rw [g.map_smul n i V x b, θ.map_smul_right]

/-- The precomposite `θ.precomp g` sends a section `x` of `P` in degree `i` to `θ (g x)`. -/
@[simp]
theorem precomp_app {P P' : GradedModule.{t, a', m} B} {M : GradedModule.{t, a, m} A}
    (θ : SemilinearHom φ P' M) (g : P ⟶ P') (i : ℤ) (V : C'ᵒᵖ) (x : (P.piece i).val.obj V) :
    (θ.precomp g).app i V x = θ.app i V (homSections (g.app i) V x) :=
  rfl

variable {P P' P'' : GradedModule.{t, a', m} B} {M M' M'' : GradedModule.{t, a, m} A}

/-- Postcomposition with the identity is the identity. -/
@[simp]
theorem postcomp_id (θ : SemilinearHom φ P M) : θ.postcomp (𝟙 M) = θ :=
  SemilinearHom.ext fun _ _ _ => rfl

/-- Postcomposition with a composite `h ≫ h'` is postcomposition with `h` followed by `h'`. -/
theorem postcomp_comp (θ : SemilinearHom φ P M) (h : M ⟶ M') (h' : M' ⟶ M'') :
    θ.postcomp (h ≫ h') = (θ.postcomp h).postcomp h' :=
  SemilinearHom.ext fun _ _ _ => rfl

/-- Precomposition with the identity is the identity. -/
@[simp]
theorem precomp_id (θ : SemilinearHom φ P M) : θ.precomp (𝟙 P) = θ :=
  SemilinearHom.ext fun _ _ _ => rfl

/-- Precomposition with a composite `g ≫ g'` is precomposition with `g'` followed by `g`. -/
theorem precomp_comp (θ : SemilinearHom φ P'' M) (g : P ⟶ P') (g' : P' ⟶ P'') :
    θ.precomp (g ≫ g') = (θ.precomp g').precomp g :=
  SemilinearHom.ext fun _ _ _ => rfl

/-- Precomposition and postcomposition commute. -/
theorem precomp_postcomp (θ : SemilinearHom φ P' M) (g : P ⟶ P') (h : M ⟶ M') :
    (θ.precomp g).postcomp h = (θ.postcomp h).precomp g :=
  SemilinearHom.ext fun _ _ _ => rfl
end SemilinearHom

/-- A `φ`-semilinear homomorphism `θ : N ⟶ P` exhibits `P` as the pullback `f^*N` of the right
graded `B`-module `N` when every `φ`-semilinear homomorphism out of `N` factors through `θ` by a
unique homomorphism of right graded `A`-modules. -/
structure IsPullback {N : GradedModule.{t, a', m} B} {P : GradedModule.{t, a, m} A}
    (θ : SemilinearHom φ N P) where
  /-- The homomorphism through which a `φ`-semilinear homomorphism out of `N` factors. -/
  desc {P' : GradedModule.{t, a, m} A} (θ' : SemilinearHom φ N P') : P ⟶ P'
  /-- The factorisation holds. -/
  fac {P' : GradedModule.{t, a, m} A} (θ' : SemilinearHom φ N P') : θ.postcomp (desc θ') = θ'
  /-- The factorising homomorphism is the only one. -/
  uniq {P' : GradedModule.{t, a, m} A} (θ' : SemilinearHom φ N P') (h : P ⟶ P')
    (hh : θ.postcomp h = θ') : h = desc θ'

namespace IsPullback

variable {N : GradedModule.{t, a', m} B} {P : GradedModule.{t, a, m} A}
  {θ : SemilinearHom φ N P}

/-- Two homomorphisms out of a pullback which agree after composition with the unit are
equal. -/
theorem hom_ext (hP : IsPullback θ) {P' : GradedModule.{t, a, m} A} {h h' : P ⟶ P'}
    (e : θ.postcomp h = θ.postcomp h') : h = h' :=
  (hP.uniq _ h rfl).trans (hP.uniq _ h' e.symm).symm

/-- The homomorphism through which `θ.postcomp h` factors is `h`. -/
@[simp]
theorem desc_postcomp (hP : IsPullback θ) {P' : GradedModule.{t, a, m} A} (h : P ⟶ P') :
    hP.desc (θ.postcomp h) = h :=
  (hP.uniq _ h rfl).symm

/-- The universal property of the pullback as a bijection: homomorphisms out of `f^*N` are the
`φ`-semilinear homomorphisms out of `N`. -/
noncomputable def homEquiv (hP : IsPullback θ) (P' : GradedModule.{t, a, m} A) :
    (P ⟶ P') ≃ SemilinearHom φ N P' where
  toFun h := θ.postcomp h
  invFun θ' := hP.desc θ'
  left_inv h := hP.desc_postcomp h
  right_inv θ' := hP.fac θ'

end IsPullback

/-- A pullback of every right graded `B`-module at once, along a morphism of ringed sites `f` and
a homomorphism `φ : B ⟶ f_*A` of sheaves of graded algebras: the module `f^*N`, its unit, and
the universal property of the unit. -/
structure PullbackData (φ : GradedAlgebra.SemilinearHom u σ B A) where
  /-- The pullback of a right graded `B`-module. -/
  obj (N : GradedModule.{t, a', m} B) : GradedModule.{t, a, m} A
  /-- The unit, a `φ`-semilinear homomorphism from a module to its pullback. -/
  unit (N : GradedModule.{t, a', m} B) : SemilinearHom φ N (obj N)
  /-- The unit exhibits the pullback as the pullback. -/
  isPullback (N : GradedModule.{t, a', m} B) : IsPullback (unit N)

namespace PullbackData

/-- The pullback of a homomorphism of right graded `B`-modules: the unique homomorphism of the
pullbacks compatible with the two units. -/
noncomputable def map (PD : PullbackData φ)
    {N N₂ : GradedModule.{t, a', m} B} (g : N ⟶ N₂) : PD.obj N ⟶ PD.obj N₂ :=
  (PD.isPullback N).desc ((PD.unit N₂).precomp g)

/-- The unit of the pullback is natural. -/
@[simp]
theorem unit_postcomp_map (PD : PullbackData φ)
    {N N₂ : GradedModule.{t, a', m} B} (g : N ⟶ N₂) :
    (PD.unit N).postcomp (PD.map g) = (PD.unit N₂).precomp g :=
  (PD.isPullback N).fac _

/-- The pullback functor `f^* : Mod(B) ⥤ Mod(A)` on sheaves of graded modules. -/
noncomputable def functor (PD : PullbackData φ) :
    GradedModule.{t, a', m} B ⥤ GradedModule.{t, a, m} A where
  obj N := PD.obj N
  map {_N _N₂} g := PD.map g
  map_id N := ((PD.isPullback N).uniq _ (𝟙 _) (by
    rw [SemilinearHom.postcomp_id, SemilinearHom.precomp_id])).symm
  map_comp {N _N₂ _N₃} g g' := ((PD.isPullback N).uniq _ _ (by
    rw [SemilinearHom.postcomp_comp, PD.unit_postcomp_map, SemilinearHom.precomp_postcomp,
      PD.unit_postcomp_map, ← SemilinearHom.precomp_comp])).symm

/-- The pullback functor sends a module `N` to its pullback `PD.obj N`. -/
@[simp]
theorem functor_obj (PD : PullbackData φ)
    (N : GradedModule.{t, a', m} B) : PD.functor.obj N = PD.obj N :=
  rfl

/-- The pullback functor sends a homomorphism `g` to its pullback `PD.map g`. -/
@[simp]
theorem functor_map (PD : PullbackData φ)
    {N N₂ : GradedModule.{t, a', m} B} (g : N ⟶ N₂) : PD.functor.map g = PD.map g :=
  rfl

end PullbackData

end Composition

section Homogeneous

variable (φ : GradedAlgebra.SemilinearHom u σ B A)

/-- A `φ`-semilinear homomorphism of right graded modules homogeneous of degree `n`: a family of
additive maps from the sections of `N` in degree `i` over `V` to the sections of `M` in degree
`i + n` over `u V`, compatible with restriction, semilinear over the structure map, and carrying
the action of a homogeneous section `b` of `B` to the action of `φ b`. -/
structure SemilinearHomOfDegree (N : GradedModule.{t, a', m} B) (M : GradedModule.{t, a, m} A)
    (n : ℤ) where
  /-- The map on local sections, from degree `i` over `V` to degree `j = i + n` over `u V`. -/
  app (i j : ℤ) (hij : i + n = j) (V : C'ᵒᵖ) :
    (N.piece i).val.obj V →+ (M.piece j).val.obj (u.op.obj V)
  /-- The maps are semilinear over the structure map of the morphism of ringed sites. -/
  map_smul (i j : ℤ) (hij : i + n = j) (V : C'ᵒᵖ) (s : R'.obj.obj V)
      (x : (N.piece i).val.obj V) :
    app i j hij V (s • x) = (σ.app V).hom s • app i j hij V x
  /-- The maps commute with restriction along a morphism of the site. -/
  naturality (i j : ℤ) (hij : i + n = j) {V W : C'ᵒᵖ} (k : V ⟶ W)
      (x : (N.piece i).val.obj V) :
    app i j hij W ((N.piece i).val.map k x) =
      (M.piece j).val.map (u.op.map k) (app i j hij V x)
  /-- The maps carry the action of a homogeneous section `b` of `B` to the action of `φ b`. -/
  map_smul_right (i j : ℤ) (hij : i + n = j) (p : ℤ) (V : C'ᵒᵖ)
      (x : (N.piece i).val.obj V) (b : (B.piece p).val.obj V) :
    app (i + p) (j + p) (by omega) V (N.smul i p V x b) =
      M.smul j p (u.op.obj V) (app i j hij V x) (φ.app p V b)

namespace SemilinearHomOfDegree

variable {φ} {N : GradedModule.{t, a', m} B} {M : GradedModule.{t, a, m} A}

omit [u.IsContinuous J' J] in
/-- A homogeneous `φ`-semilinear homomorphism is determined by its values on local sections. -/
@[ext]
theorem ext {n : ℤ} {θ θ' : SemilinearHomOfDegree φ N M n}
    (h : ∀ (i j : ℤ) (hij : i + n = j) (V : C'ᵒᵖ) (x : (N.piece i).val.obj V),
      θ.app i j hij V x = θ'.app i j hij V x) : θ = θ' := by
  cases θ with
  | mk app smul nat mul =>
    cases θ' with
    | mk app' smul' nat' mul' =>
      have happ : app = app' := by
        funext i j hij V
        exact AddMonoidHom.ext fun x => h i j hij V x
      subst happ
      rfl

omit [u.IsContinuous J' J] in
/-- The value of a homogeneous `φ`-semilinear homomorphism in a propositionally different target
degree is the transport of its value. -/
theorem app_castHom {n : ℤ} (θ : SemilinearHomOfDegree φ N M n) {i j j' : ℤ} (hij : i + n = j)
    (hij' : i + n = j') (V : C'ᵒᵖ) (x : (N.piece i).val.obj V) :
    θ.app i j' hij' V x =
      castHom M.piece (by omega : j = j') (u.op.obj V) (θ.app i j hij V x) := by
  obtain rfl : j = j' := by omega
  rfl

/-- **A homogeneous `φ`-semilinear homomorphism of degree `n` into `M` is a degree-zero
`φ`-semilinear homomorphism into the shift `M⟨n⟩`.** -/
noncomputable def shiftEquiv (φ : GradedAlgebra.SemilinearHom u σ B A)
    (N : GradedModule.{t, a', m} B) (M : GradedModule.{t, a, m} A) (n : ℤ) :
    SemilinearHomOfDegree φ N M n ≃ SemilinearHom φ N (M.shift n) where
  toFun θ :=
    { app := fun i V => θ.app i (i + n) rfl V
      map_smul := fun i V s x => θ.map_smul i (i + n) rfl V s x
      naturality := fun i {_V _W} k x => θ.naturality i (i + n) rfl k x
      map_smul_right := fun i p V x b => by
        rw [θ.app_castHom (j := i + n + p) (by omega) (by omega),
          θ.map_smul_right i (i + n) rfl p V x b]
        exact (M.shift_smul n i p (u.op.obj V) (θ.app i (i + n) rfl V x) (φ.app p V b)).symm }
  invFun ρ :=
    { app := fun i j hij V => (castHom M.piece hij (u.op.obj V)).comp (ρ.app i V)
      map_smul := fun i j hij V s x =>
        (congrArg (fun z => castHom M.piece hij (u.op.obj V) z) (ρ.map_smul i V s x)).trans
          (castHom_smul M.piece hij (u.op.obj V) ((σ.app V).hom s) (ρ.app i V x))
      naturality := fun i j hij {_V _W} k x =>
        (congrArg (fun z => castHom M.piece hij (u.op.obj _) z) (ρ.naturality i k x)).trans
          (castHom_naturality M.piece hij (u.op.map k) (ρ.app i _ x)).symm
      map_smul_right := fun i j hij p V x b => by
        refine ((congrArg (fun z => castHom M.piece
            (show i + p + n = j + p by omega) (u.op.obj V) z)
          (ρ.map_smul_right i p V x b)).trans ?_).trans
          (Cofree.smul_castHom_left M hij (u.op.obj V) (ρ.app i V x) (φ.app p V b)).symm
        rw [M.shift_smul n i p (u.op.obj V) (ρ.app i V x) (φ.app p V b),
          Cofree.castHom_castHom] }
  left_inv θ := SemilinearHomOfDegree.ext fun i j hij V x => by
    subst hij; rfl
  right_inv ρ := SemilinearHom.ext fun _ _ _ => rfl

end SemilinearHomOfDegree

/-- **`f_*M` corepresents the `φ`-semilinear homomorphisms into `M` homogeneous of degree `n`**:
such a homomorphism out of `N` is exactly a homomorphism `N ⟶ f_*M` of right graded `B`-modules
homogeneous of degree `n`. -/
@[stacks 0FR7 "f_*M corepresents the φ-semilinear homomorphisms into M homogeneous of degree n, \
the morphisms of the graded category Mod^gr"]
noncomputable def semilinearHomOfDegreeEquiv (N : GradedModule.{t, a', m} B)
    (M : GradedModule.{t, a, m} A) (n : ℤ) :
    SemilinearHomOfDegree φ N M n ≃ GradedHomOfDegree N (pushforwardObj φ M) n where
  toFun θ :=
    { app := fun i j hij => semilinearSheafHom (fun V => θ.app i j hij V)
        (θ.map_smul i j hij) fun _ _ k x => θ.naturality i j hij k x
      map_mul := fun i j hij p V x b => θ.map_smul_right i j hij p V x b }
  invFun h :=
    { app := fun i j hij V => homSections (h.app i j hij) V
      map_smul := fun i j hij V s x => (h.app i j hij).val.app V |>.hom.map_smul s x
      naturality := fun i j hij {_V _W} k x =>
        PresheafOfModules.naturality_apply (h.app i j hij).val k x
      map_smul_right := fun i j hij p V x b => h.map_mul i j hij p V x b }
  left_inv θ := SemilinearHomOfDegree.ext fun _ _ _ _ _ => rfl
  right_inv h := GradedHomOfDegree.ext fun i j hij => by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    ext x
    rfl

end Homogeneous

section Adjunction

variable {φ : GradedAlgebra.SemilinearHom u σ B A}

/-- Postcomposition of a `φ`-semilinear homomorphism with a homomorphism of right graded
`A`-modules is, read through the corepresentation of the semilinear homomorphisms by the direct
image, composition with the direct image of that homomorphism. -/
theorem SemilinearHom.semilinearHomEquiv_postcomp {N : GradedModule.{t, a', m} B}
    {M M' : GradedModule.{t, a, m} A} (θ : SemilinearHom φ N M) (h : M ⟶ M') :
    semilinearHomEquiv φ N M' (θ.postcomp h) =
      semilinearHomEquiv φ N M θ ≫ pushforwardMap φ h :=
  GradedModule.Hom.ext fun _ => by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    ext x
    rfl

/-- **The adjunction between the pullback and the direct image of sheaves of graded modules, in
every homogeneous degree**: `Hom^n(f^*N, M) = Hom^n(N, f_*M)`. -/
noncomputable def PullbackData.homOfDegreeEquiv
    (PD : PullbackData φ) (N : GradedModule.{t, a', m} B)
    (M : GradedModule.{t, a, m} A) (n : ℤ) :
    GradedHomOfDegree (PD.obj N) M n ≃ GradedHomOfDegree N (pushforwardObj φ M) n :=
  ((GradedHomOfDegree.shiftHomEquiv (PD.obj N) M n).trans
    ((PD.isPullback N).homEquiv (M.shift n))).trans
      ((SemilinearHomOfDegree.shiftEquiv φ N M n).symm.trans
        (semilinearHomOfDegreeEquiv φ N M n))

/-- The hom identification `Hom(f^*N, M) = Hom(N, f_*M)` in degree zero. -/
noncomputable def PullbackData.homEquivPushforward
    (PD : PullbackData φ) (N : GradedModule.{t, a', m} B)
    (M : GradedModule.{t, a, m} A) : (PD.functor.obj N ⟶ M) ≃ (N ⟶ pushforwardObj φ M) :=
  ((PD.isPullback N).homEquiv M).trans (semilinearHomEquiv φ N M)

/-- **The pullback of sheaves of graded modules is left adjoint to the direct image.** -/
noncomputable def PullbackData.pullbackPushforwardAdjunction
    (PD : PullbackData φ) :
    PD.functor ⊣ pushforwardFunctor.{t, a, m} φ :=
  Adjunction.mkOfHomEquiv
    { homEquiv := PD.homEquivPushforward
      homEquiv_naturality_left_symm := fun {N' N M} f g => by
        change (PD.isPullback N').desc ((semilinearHomEquiv φ N' M).symm (f ≫ g)) =
          PD.map f ≫ (PD.isPullback N).desc ((semilinearHomEquiv φ N M).symm g)
        refine ((PD.isPullback N').uniq _ _ ?_).symm
        rw [SemilinearHom.postcomp_comp, PD.unit_postcomp_map, SemilinearHom.precomp_postcomp,
          (PD.isPullback N).fac]
        exact SemilinearHom.ext fun _ _ _ => rfl
      homEquiv_naturality_right := fun {N M M'} f g => GradedModule.Hom.ext fun i => by
        apply SheafOfModules.hom_ext
        apply PresheafOfModules.hom_ext
        intro V
        apply ModuleCat.hom_ext
        ext x
        rfl }

end Adjunction

end GradedModule

end SheafOfModules
