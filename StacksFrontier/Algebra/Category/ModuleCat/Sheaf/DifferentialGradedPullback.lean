module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedForgetColimits

/-!
# Pullback of sheaves of differential graded modules along a morphism of ringed sites

Let `f : (C, J, R) ⟶ (C', J', R')` be a morphism of ringed sites, presented as a functor
`u : C' ⥤ C` in the direction opposite to `f` together with the structure map
`σ : R' ⟶ f_*R` of its sheaves of rings; the direct image of a sheaf on `C` is then restriction
of its sections along `u`. Let `A` be a sheaf of differential graded `R`-algebras on the source,
let `A'` be a sheaf of differential graded `R'`-algebras on the target and let
`φ : f⁻¹A' ⟶ A`, equivalently `φ : A' ⟶ f_*A`, be a homomorphism of sheaves of differential
graded algebras. For a right differential graded `A'`-module `M` the pullback `f^*M` is a right
differential graded `A`-module, and it is characterised by the universal property that
`φ`-semilinear maps out of `M` are the same thing as morphisms of right differential graded
`A`-modules out of `f^*M`.

A `φ`-semilinear map `M ⟶ N` is the datum, for every degree `i` and every object `V` of `C'`, of
an additive map from the degree-`i` sections of `M` over `V` to the degree-`i` sections of `N`
over `u V`, compatible with restriction, semilinear over `σ`, commuting with the differentials
and carrying the action of a homogeneous section `b` of `A'` to the action of `φ b`. This is
exactly the datum of a morphism `M ⟶ f_*N` of right differential graded `A'`-modules, written
out so that no sheaf-theoretic direct or inverse image has to be formed.

## Main definitions

* `SheafOfModules.compRingMap` is the structure map of a composite of two morphisms of ringed
  sites.
* `SheafOfModules.DifferentialGradedAlgebra.SemilinearHom` is a `σ`-semilinear homomorphism of
  sheaves of differential graded algebras along `u`, that is a map `A' ⟶ f_*A`, and
  `SheafOfModules.DifferentialGradedAlgebra.SemilinearHom.trans` is its composition.
* `SheafOfModules.DifferentialGradedModule.SemilinearHom` is a `φ`-semilinear map of right
  differential graded modules, with `postcomp`, `precomp` and `trans` for composition with a
  morphism of modules on the target, on the source, and with a semilinear map along a second
  morphism of ringed sites.
* `SheafOfModules.DifferentialGradedModule.IsPullback` says that a `φ`-semilinear map
  `θ : M ⟶ N` exhibits `N` as the pullback `f^*M`: every `φ`-semilinear map out of `M` factors
  uniquely through `θ` by a morphism of right differential graded `A`-modules.
* `SheafOfModules.DifferentialGradedModule.PullbackData` packages a pullback of every right
  differential graded `A'`-module at once, and
  `SheafOfModules.DifferentialGradedModule.PullbackData.functor` is the resulting functor
  `f^* : Mod^dg(A', d) ⥤ Mod^dg(A, d)`.
* `SheafOfModules.DifferentialGradedModule.SemilinearHom.IsUniversal` says that a unit
  `θ : M ⟶ P` stays universal when tested against the `φ`-semilinear maps out of `P` for a
  further morphism of ringed sites, which is what makes pullbacks compose.

## Main results

* `SheafOfModules.DifferentialGradedModule.IsPullback.homEquiv`: the universal property as a
  bijection between morphisms out of `f^*M` and `φ`-semilinear maps out of `M`.
* `SheafOfModules.DifferentialGradedModule.IsPullback.isoOfPullback`: two pullbacks of the same
  module are canonically isomorphic, by the unique isomorphism compatible with the two units.
* `SheafOfModules.DifferentialGradedModule.PullbackData.functor` together with
  `SheafOfModules.DifferentialGradedModule.PullbackData.unit_postcomp_map`: the pullback is
  functorial and the unit is natural; and
  `SheafOfModules.DifferentialGradedModule.PullbackData.isoFunctor`: the functor is unique up to
  the natural isomorphism compatible with the units.
* `SheafOfModules.DifferentialGradedModule.IsPullback.trans`: the composite of the unit of a
  pullback along `g` with the unit of a pullback along `f` exhibits a pullback along `g ∘ f`.
* `SheafOfModules.DifferentialGradedModule.PullbackData.transIso`: pullback along a composite is
  naturally isomorphic to the composite of the two pullbacks, and
  `SheafOfModules.DifferentialGradedModule.PullbackData.trans` is the pullback datum for the
  composite built from the two given ones, so that no datum for the composite has to be
  assumed.

## Implementation notes

The construction `f^*M = f⁻¹M ⊗_{f⁻¹A'} A` cannot be written down *at this point in the
development*: it needs the tensor product of a right differential graded module with a
differential graded bimodule over a sheaf of differential graded algebras and the inverse image
of a sheaf of differential graded modules, and neither is available yet. So the pullback is
pinned by its universal property instead, in the same way as the differential graded internal
hom of `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedInternalHom.lean`:
`IsPullback` is a predicate on a semilinear map, `PullbackData` carries one for every module at
once, and the functoriality is *constructed* from that data rather than assumed. The universal
property determines the pullback up to a unique isomorphism compatible with the units and it
determines the action of the functor on morphisms, so nothing below is vacuous.

**The construction is carried out downstream, and `PullbackData` is inhabited there.** At a
continuous functor of two *small* sites in one universe which is representably flat and final,
`Stacks.DifferentialGradedPullbackConstruction.pullbackObj` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedPullbackConstruction.lean` *is*
`f⁻¹M ⊗_{f⁻¹A'} A`, and
`Stacks.DifferentialGradedPullbackConstruction.pullbackData` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedPullbackAdjunction.lean` is a
`PullbackData` for it — so there the whole structure below is a theorem rather than a
hypothesis. It stays a hypothesis here because everything below holds at arbitrary universes
for an unrestricted functor, which is what the consumers of `PullbackData` are stated at.

The compatibility with composition is likewise not assumed. What is assumed is
`SemilinearHom.IsUniversal`, which strengthens the universal property of one unit from
morphisms of modules to `φ`-semilinear maps for a *further* morphism of ringed sites; the
pullback `g⁻¹M ⊗_{g⁻¹A''} A'` has that property because a `φ`-semilinear map out of it is a
morphism of right differential graded `A'`-modules into `f_*N`, but that reformulation needs the
direct image of a sheaf of differential graded modules, which is only constructed downstream in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedPushforward.lean`. The
conclusion that pullback along a composite is the composite of the pullbacks is then proved, not
assumed.

The morphism of ringed sites is not bundled. Its two pieces, the functor `u : C' ⥤ C` and the
structure map `σ : R'.obj ⟶ u.op ⋙ R.obj` of presheaves of rings, are taken as separate
variables, which avoids adding a fourth structure called a morphism of ringed topoi to this
development and keeps the hypotheses minimal: neither continuity of `u` nor the sheaf condition
for `f_*R` is used, because all of the data below is expressed on sections. For a morphism of
ringed sites in the sense of `AlgebraicGeometry.RingedSite.Hom` the functor is its `u` and the
structure map is its `fsharp`, whose direct image is restriction of sections along `u`.

There is no cross-base homomorphism of sheaves of differential graded algebras in this
development: `SheafOfModules.DifferentialGradedAlgebra.Hom` requires one and the same sheaf of
rings on one and the same site. `DifferentialGradedAlgebra.SemilinearHom` is therefore new, and
it *does* require preservation of the unit, which `Hom` deliberately omits: without it the
restricted action of `A'` on a module over `A` need not satisfy the unit axiom, so semilinear
maps of modules could not be composed with semilinear maps of algebras.

Because the structure map relates the two sheaves of rings, they must take values in one and the
same `RingCat.{t}`; every other universe — the two underlying categories, their morphisms, the
homogeneous pieces of the algebras and of the modules — is independent, as in the neighbouring
differential graded files. The three independent ringed sites of the composition statements
follow the naming of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedDerivedPullback.lean`.

A semilinear map is required to commute with the differentials only in consecutive degrees. That
is no loss: the differential of a cochain complex vanishes between any other pair of degrees.
All the degrees appearing in the compatibility with the module actions agree on the nose, so
nothing below needs a heterogeneous equality or a transport along an equality of degrees.

## References

* [Stacks Project, Tag 0FRU](https://stacks.math.columbia.edu/tag/0FRU)
* [Stacks Project, Tag 0FRI](https://stacks.math.columbia.edu/tag/0FRI)
* [Stacks Project, Tag 0FRF](https://stacks.math.columbia.edu/tag/0FRF)
-/

@[expose] public section

open CategoryTheory

universe t a m v u a' m' v' u' a'' m'' v'' u''

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {C' : Type u'} [Category.{v'} C'] {J' : GrothendieckTopology C'} {R' : Sheaf J' RingCat.{t}}
  {C'' : Type u''} [Category.{v''} C''] {J'' : GrothendieckTopology C''}
  {R'' : Sheaf J'' RingCat.{t}}

/-- The structure map of a composite of two morphisms of ringed sites: from `σ : R' ⟶ f_*R` and
`τ : R'' ⟶ g_*R'` it is the map `R'' ⟶ (g ∘ f)_*R` obtained by applying `g_*` to `σ`, the direct
image along a composite being restriction of sections along the composite functor. -/
def compRingMap (u : C' ⥤ C) (σ : R'.obj ⟶ u.op ⋙ R.obj) (v : C'' ⥤ C')
    (τ : R''.obj ⟶ v.op ⋙ R'.obj) : R''.obj ⟶ (v ⋙ u).op ⋙ R.obj :=
  τ ≫ Functor.whiskerLeft v.op σ

/-- On a local section, the structure map of a composite applies `τ` and then `σ`. -/
@[simp]
theorem compRingMap_app_apply (u : C' ⥤ C) (σ : R'.obj ⟶ u.op ⋙ R.obj) (v : C'' ⥤ C')
    (τ : R''.obj ⟶ v.op ⋙ R'.obj) (W : C''ᵒᵖ) (s : R''.obj.obj W) :
    ((compRingMap u σ v τ).app W).hom s = (σ.app (v.op.obj W)).hom ((τ.app W).hom s) :=
  rfl

namespace DifferentialGradedModule

/-- A morphism of right differential graded modules commutes with the differentials, on local
sections and in consecutive degrees. -/
theorem hom_comm_d_app {A : DifferentialGradedAlgebra.{t, a} R}
    {M N : DifferentialGradedModule.{t, a, m} A} (f : M ⟶ N) (i : ℤ) (U : Cᵒᵖ)
    (x : (M.complex.X i).val.obj U) :
    (f.toHomologicalComplex.f (i + 1)).val.app U ((M.complex.d i (i + 1)).val.app U x) =
      (N.complex.d i (i + 1)).val.app U ((f.toHomologicalComplex.f i).val.app U x) := by
  have h := homSections_congr (f.toHomologicalComplex.comm i (i + 1)) U x
  simp only [homSections_apply] at h
  exact h.symm

end DifferentialGradedModule

namespace DifferentialGradedAlgebra

/-- A semilinear homomorphism of sheaves of differential graded algebras along a morphism of
ringed sites: a map `A' ⟶ f_*A`, given on local sections as a degreewise additive map from the
sections of `A'` over `V` to the sections of `A` over `u V` which is compatible with restriction,
semilinear over the structure map `σ`, and a unital homomorphism of differential graded
algebras. -/
structure SemilinearHom (u : C' ⥤ C) (σ : R'.obj ⟶ u.op ⋙ R.obj)
    (A' : DifferentialGradedAlgebra.{t, a'} R') (A : DifferentialGradedAlgebra.{t, a} R) where
  /-- The map on local sections, from the sections of `A'` over `V` to those of `A` over
  `u V`. -/
  app (i : ℤ) (V : C'ᵒᵖ) : (A'.complex.X i).val.obj V →+ (A.complex.X i).val.obj (u.op.obj V)
  /-- The maps are semilinear over the structure map of the morphism of ringed sites. -/
  map_smul (i : ℤ) (V : C'ᵒᵖ) (s : R'.obj.obj V) (x : (A'.complex.X i).val.obj V) :
    app i V (s • x) = (σ.app V).hom s • app i V x
  /-- The maps commute with restriction along a morphism of the site. -/
  naturality (i : ℤ) {V W : C'ᵒᵖ} (k : V ⟶ W) (x : (A'.complex.X i).val.obj V) :
    app i W ((A'.complex.X i).val.map k x) = (A.complex.X i).val.map (u.op.map k) (app i V x)
  /-- The maps commute with the differentials. -/
  comm_d (i : ℤ) (V : C'ᵒᵖ) (x : (A'.complex.X i).val.obj V) :
    app (i + 1) V ((A'.complex.d i (i + 1)).val.app V x) =
      (A.complex.d i (i + 1)).val.app (u.op.obj V) (app i V x)
  /-- The maps respect the graded multiplication. -/
  map_mul (i j : ℤ) (V : C'ᵒᵖ) (x : (A'.complex.X i).val.obj V)
      (y : (A'.complex.X j).val.obj V) :
    app (i + j) V ((A'.mul i j).app V x y) =
      (A.mul i j).app (u.op.obj V) (app i V x) (app j V y)
  /-- The maps carry the unit to the unit. -/
  map_one (V : C'ᵒᵖ) : app 0 V (A'.one.eval V) = A.one.eval (u.op.obj V)

namespace SemilinearHom

variable {u : C' ⥤ C} {σ : R'.obj ⟶ u.op ⋙ R.obj} {v : C'' ⥤ C'}
  {τ : R''.obj ⟶ v.op ⋙ R'.obj} {A : DifferentialGradedAlgebra.{t, a} R}
  {A' : DifferentialGradedAlgebra.{t, a'} R'} {A'' : DifferentialGradedAlgebra.{t, a''} R''}

/-- A semilinear homomorphism of sheaves of differential graded algebras is determined by its
values on local sections. -/
@[ext]
theorem ext {φ ψ : SemilinearHom u σ A' A}
    (h : ∀ (i : ℤ) (V : C'ᵒᵖ) (x : (A'.complex.X i).val.obj V), φ.app i V x = ψ.app i V x) :
    φ = ψ := by
  cases φ with
  | mk app smul nat cd mul one =>
    cases ψ with
    | mk app' smul' nat' cd' mul' one' =>
      have happ : app = app' := by
        funext i V
        exact AddMonoidHom.ext fun x => h i V x
      subst happ
      rfl

/-- The composition of semilinear homomorphisms of sheaves of differential graded algebras along
two composable morphisms of ringed sites, a semilinear homomorphism along the composite. -/
def trans (ψ : SemilinearHom v τ A'' A') (φ : SemilinearHom u σ A' A) :
    SemilinearHom (v ⋙ u) (compRingMap u σ v τ) A'' A where
  app i W := (φ.app i (v.op.obj W)).comp (ψ.app i W)
  map_smul i W s x := by
    change φ.app i (v.op.obj W) (ψ.app i W (s • x)) =
      (σ.app (v.op.obj W)).hom ((τ.app W).hom s) • φ.app i (v.op.obj W) (ψ.app i W x)
    rw [ψ.map_smul, φ.map_smul]
  naturality i {V W} k x := by
    change φ.app i (v.op.obj W) (ψ.app i W ((A''.complex.X i).val.map k x)) =
      (A.complex.X i).val.map (u.op.map (v.op.map k)) (φ.app i (v.op.obj V) (ψ.app i V x))
    rw [ψ.naturality, φ.naturality]
  comm_d i W x := by
    change φ.app (i + 1) (v.op.obj W) (ψ.app (i + 1) W ((A''.complex.d i (i + 1)).val.app W x)) =
      (A.complex.d i (i + 1)).val.app (u.op.obj (v.op.obj W))
        (φ.app i (v.op.obj W) (ψ.app i W x))
    rw [ψ.comm_d, φ.comm_d]
  map_mul i j W x y := by
    change φ.app (i + j) (v.op.obj W) (ψ.app (i + j) W ((A''.mul i j).app W x y)) =
      (A.mul i j).app (u.op.obj (v.op.obj W)) (φ.app i (v.op.obj W) (ψ.app i W x))
        (φ.app j (v.op.obj W) (ψ.app j W y))
    rw [ψ.map_mul, φ.map_mul]
  map_one W := by
    change φ.app 0 (v.op.obj W) (ψ.app 0 W (A''.one.eval W)) =
      A.one.eval (u.op.obj (v.op.obj W))
    rw [ψ.map_one, φ.map_one]

/-- On a local section, the composite of two semilinear homomorphisms of algebras applies `ψ` and
then `φ`. -/
@[simp]
theorem trans_app (ψ : SemilinearHom v τ A'' A') (φ : SemilinearHom u σ A' A) (i : ℤ)
    (W : C''ᵒᵖ) (x : (A''.complex.X i).val.obj W) :
    (ψ.trans φ).app i W x = φ.app i (v.op.obj W) (ψ.app i W x) :=
  rfl

end SemilinearHom

end DifferentialGradedAlgebra

namespace DifferentialGradedModule

/-- A semilinear map of right differential graded modules along a morphism of ringed sites `f`
and a semilinear homomorphism `φ : A' ⟶ f_*A` of sheaves of differential graded algebras: a
degreewise additive map from the sections of `M` over `V` to the sections of `N` over `u V`,
compatible with restriction, semilinear over the structure map, commuting with the
differentials, and carrying the action of a homogeneous section `b` of `A'` to the action of
`φ b`. This is the datum of a morphism `M ⟶ f_*N` of right differential graded `A'`-modules. -/
structure SemilinearHom {u : C' ⥤ C} {σ : R'.obj ⟶ u.op ⋙ R.obj}
    {A' : DifferentialGradedAlgebra.{t, a'} R'} {A : DifferentialGradedAlgebra.{t, a} R}
    (φ : DifferentialGradedAlgebra.SemilinearHom u σ A' A)
    (M : DifferentialGradedModule.{t, a', m'} A')
    (N : DifferentialGradedModule.{t, a, m} A) where
  /-- The map on local sections, from the sections of `M` over `V` to those of `N` over
  `u V`. -/
  app (i : ℤ) (V : C'ᵒᵖ) : (M.complex.X i).val.obj V →+ (N.complex.X i).val.obj (u.op.obj V)
  /-- The maps are semilinear over the structure map of the morphism of ringed sites. -/
  map_smul (i : ℤ) (V : C'ᵒᵖ) (s : R'.obj.obj V) (x : (M.complex.X i).val.obj V) :
    app i V (s • x) = (σ.app V).hom s • app i V x
  /-- The maps commute with restriction along a morphism of the site. -/
  naturality (i : ℤ) {V W : C'ᵒᵖ} (k : V ⟶ W) (x : (M.complex.X i).val.obj V) :
    app i W ((M.complex.X i).val.map k x) = (N.complex.X i).val.map (u.op.map k) (app i V x)
  /-- The maps commute with the differentials. -/
  comm_d (i : ℤ) (V : C'ᵒᵖ) (x : (M.complex.X i).val.obj V) :
    app (i + 1) V ((M.complex.d i (i + 1)).val.app V x) =
      (N.complex.d i (i + 1)).val.app (u.op.obj V) (app i V x)
  /-- The maps carry the action of a homogeneous section `b` of `A'` to the action of `φ b`. -/
  map_mul (n i : ℤ) (V : C'ᵒᵖ) (x : (M.complex.X n).val.obj V)
      (b : (A'.complex.X i).val.obj V) :
    app (n + i) V ((M.mul n i).app V x b) =
      (N.mul n i).app (u.op.obj V) (app n V x) (φ.app i V b)

namespace SemilinearHom

variable {u : C' ⥤ C} {σ : R'.obj ⟶ u.op ⋙ R.obj} {v : C'' ⥤ C'}
  {τ : R''.obj ⟶ v.op ⋙ R'.obj} {A : DifferentialGradedAlgebra.{t, a} R}
  {A' : DifferentialGradedAlgebra.{t, a'} R'} {A'' : DifferentialGradedAlgebra.{t, a''} R''}
  {φ : DifferentialGradedAlgebra.SemilinearHom u σ A' A}
  {ψ : DifferentialGradedAlgebra.SemilinearHom v τ A'' A'}

/-- A semilinear map of right differential graded modules is determined by its values on local
sections. -/
@[ext]
theorem ext {M : DifferentialGradedModule.{t, a', m'} A'}
    {N : DifferentialGradedModule.{t, a, m} A} {θ θ' : SemilinearHom φ M N}
    (h : ∀ (i : ℤ) (V : C'ᵒᵖ) (x : (M.complex.X i).val.obj V), θ.app i V x = θ'.app i V x) :
    θ = θ' := by
  cases θ with
  | mk app smul nat cd mul =>
    cases θ' with
    | mk app' smul' nat' cd' mul' =>
      have happ : app = app' := by
        funext i V
        exact AddMonoidHom.ext fun x => h i V x
      subst happ
      rfl

/-- Postcomposition of a semilinear map with a morphism of right differential graded modules on
the target. -/
def postcomp {M : DifferentialGradedModule.{t, a', m'} A'}
    {N N' : DifferentialGradedModule.{t, a, m} A} (θ : SemilinearHom φ M N) (h : N ⟶ N') :
    SemilinearHom φ M N' where
  app i V := (homSections (h.toHomologicalComplex.f i) (u.op.obj V)).comp (θ.app i V)
  map_smul i V s x := by
    change homSections (h.toHomologicalComplex.f i) (u.op.obj V) (θ.app i V (s • x)) =
      (σ.app V).hom s •
        homSections (h.toHomologicalComplex.f i) (u.op.obj V) (θ.app i V x)
    rw [θ.map_smul]
    exact homSections_smul _ _ _ _
  naturality i {V W} k x := by
    change homSections (h.toHomologicalComplex.f i) (u.op.obj W)
        (θ.app i W ((M.complex.X i).val.map k x)) =
      (N'.complex.X i).val.map (u.op.map k)
        (homSections (h.toHomologicalComplex.f i) (u.op.obj V) (θ.app i V x))
    rw [θ.naturality]
    exact (homSections_naturality (h.toHomologicalComplex.f i) (u.op.map k)
      (θ.app i V x)).symm
  comm_d i V x := by
    change homSections (h.toHomologicalComplex.f (i + 1)) (u.op.obj V)
        (θ.app (i + 1) V ((M.complex.d i (i + 1)).val.app V x)) =
      (N'.complex.d i (i + 1)).val.app (u.op.obj V)
        (homSections (h.toHomologicalComplex.f i) (u.op.obj V) (θ.app i V x))
    rw [θ.comm_d]
    exact hom_comm_d_app h i (u.op.obj V) (θ.app i V x)
  map_mul n i V x b := by
    change homSections (h.toHomologicalComplex.f (n + i)) (u.op.obj V)
        (θ.app (n + i) V ((M.mul n i).app V x b)) =
      (N'.mul n i).app (u.op.obj V)
        (homSections (h.toHomologicalComplex.f n) (u.op.obj V) (θ.app n V x)) (φ.app i V b)
    rw [θ.map_mul]
    exact h.map_mul n i (u.op.obj V) (θ.app n V x) (φ.app i V b)

/-- On a local section, the postcomposite `θ.postcomp h` applies `θ` and then `h`. -/
@[simp]
theorem postcomp_app {M : DifferentialGradedModule.{t, a', m'} A'}
    {N N' : DifferentialGradedModule.{t, a, m} A} (θ : SemilinearHom φ M N) (h : N ⟶ N')
    (i : ℤ) (V : C'ᵒᵖ) (x : (M.complex.X i).val.obj V) :
    (θ.postcomp h).app i V x =
      homSections (h.toHomologicalComplex.f i) (u.op.obj V) (θ.app i V x) :=
  rfl

/-- Precomposition of a semilinear map with a morphism of right differential graded modules on
the source. -/
def precomp {M M' : DifferentialGradedModule.{t, a', m'} A'}
    {N : DifferentialGradedModule.{t, a, m} A} (θ : SemilinearHom φ M' N) (g : M ⟶ M') :
    SemilinearHom φ M N where
  app i V := (θ.app i V).comp (homSections (g.toHomologicalComplex.f i) V)
  map_smul i V s x := by
    have e : (g.toHomologicalComplex.f i).val.app V (s • x) =
        s • (g.toHomologicalComplex.f i).val.app V x := homSections_smul _ _ _ _
    change θ.app i V ((g.toHomologicalComplex.f i).val.app V (s • x)) =
      (σ.app V).hom s • θ.app i V ((g.toHomologicalComplex.f i).val.app V x)
    rw [e, θ.map_smul]
  naturality i {V W} k x := by
    have e : (g.toHomologicalComplex.f i).val.app W ((M.complex.X i).val.map k x) =
        (M'.complex.X i).val.map k ((g.toHomologicalComplex.f i).val.app V x) :=
      (homSections_naturality (g.toHomologicalComplex.f i) k x).symm
    change θ.app i W ((g.toHomologicalComplex.f i).val.app W ((M.complex.X i).val.map k x)) =
      (N.complex.X i).val.map (u.op.map k)
        (θ.app i V ((g.toHomologicalComplex.f i).val.app V x))
    rw [e, θ.naturality]
  comm_d i V x := by
    change θ.app (i + 1) V
        ((g.toHomologicalComplex.f (i + 1)).val.app V ((M.complex.d i (i + 1)).val.app V x)) =
      (N.complex.d i (i + 1)).val.app (u.op.obj V)
        (θ.app i V ((g.toHomologicalComplex.f i).val.app V x))
    rw [hom_comm_d_app g i V x, θ.comm_d]
  map_mul n i V x b := by
    change θ.app (n + i) V
        ((g.toHomologicalComplex.f (n + i)).val.app V ((M.mul n i).app V x b)) =
      (N.mul n i).app (u.op.obj V) (θ.app n V ((g.toHomologicalComplex.f n).val.app V x))
        (φ.app i V b)
    rw [g.map_mul n i V x b, θ.map_mul]

/-- On a local section, the precomposite `θ.precomp g` applies `g` and then `θ`. -/
@[simp]
theorem precomp_app {M M' : DifferentialGradedModule.{t, a', m'} A'}
    {N : DifferentialGradedModule.{t, a, m} A} (θ : SemilinearHom φ M' N) (g : M ⟶ M') (i : ℤ)
    (V : C'ᵒᵖ) (x : (M.complex.X i).val.obj V) :
    (θ.precomp g).app i V x = θ.app i V (homSections (g.toHomologicalComplex.f i) V x) :=
  rfl

/-- The composition of a semilinear map along one morphism of ringed sites with a semilinear map
along a second one, a semilinear map along the composite. -/
def trans {M : DifferentialGradedModule.{t, a'', m''} A''}
    {P : DifferentialGradedModule.{t, a', m'} A'} {N : DifferentialGradedModule.{t, a, m} A}
    (θ : SemilinearHom ψ M P) (ρ : SemilinearHom φ P N) : SemilinearHom (ψ.trans φ) M N where
  app i W := (ρ.app i (v.op.obj W)).comp (θ.app i W)
  map_smul i W s x := by
    change ρ.app i (v.op.obj W) (θ.app i W (s • x)) =
      (σ.app (v.op.obj W)).hom ((τ.app W).hom s) • ρ.app i (v.op.obj W) (θ.app i W x)
    rw [θ.map_smul, ρ.map_smul]
  naturality i {V W} k x := by
    change ρ.app i (v.op.obj W) (θ.app i W ((M.complex.X i).val.map k x)) =
      (N.complex.X i).val.map (u.op.map (v.op.map k)) (ρ.app i (v.op.obj V) (θ.app i V x))
    rw [θ.naturality, ρ.naturality]
  comm_d i W x := by
    change ρ.app (i + 1) (v.op.obj W) (θ.app (i + 1) W ((M.complex.d i (i + 1)).val.app W x)) =
      (N.complex.d i (i + 1)).val.app (u.op.obj (v.op.obj W))
        (ρ.app i (v.op.obj W) (θ.app i W x))
    rw [θ.comm_d, ρ.comm_d]
  map_mul n i W x b := by
    change ρ.app (n + i) (v.op.obj W) (θ.app (n + i) W ((M.mul n i).app W x b)) =
      (N.mul n i).app (u.op.obj (v.op.obj W)) (ρ.app n (v.op.obj W) (θ.app n W x))
        (φ.app i (v.op.obj W) (ψ.app i W b))
    rw [θ.map_mul, ρ.map_mul]

/-- On a local section, the composite `θ.trans ρ` applies `θ` and then `ρ`. -/
@[simp]
theorem trans_app {M : DifferentialGradedModule.{t, a'', m''} A''}
    {P : DifferentialGradedModule.{t, a', m'} A'} {N : DifferentialGradedModule.{t, a, m} A}
    (θ : SemilinearHom ψ M P) (ρ : SemilinearHom φ P N) (i : ℤ) (W : C''ᵒᵖ)
    (x : (M.complex.X i).val.obj W) :
    (θ.trans ρ).app i W x = ρ.app i (v.op.obj W) (θ.app i W x) :=
  rfl

section Composition

variable {M M' M'' : DifferentialGradedModule.{t, a', m'} A'}
  {N N' N'' : DifferentialGradedModule.{t, a, m} A}

/-- Postcomposition with the identity morphism is the identity. -/
@[simp]
theorem postcomp_id (θ : SemilinearHom φ M N) : θ.postcomp (𝟙 N) = θ := by
  ext i V x
  rfl

/-- Postcomposition with a composite of morphisms is postcomposition with each in turn. -/
theorem postcomp_comp (θ : SemilinearHom φ M N) (h : N ⟶ N') (h' : N' ⟶ N'') :
    θ.postcomp (h ≫ h') = (θ.postcomp h).postcomp h' := by
  ext i V x
  rfl

/-- Precomposition with the identity morphism is the identity. -/
@[simp]
theorem precomp_id (θ : SemilinearHom φ M N) : θ.precomp (𝟙 M) = θ := by
  ext i V x
  rfl

/-- Precomposition with a composite of morphisms is precomposition with each in turn. -/
theorem precomp_comp (θ : SemilinearHom φ M'' N) (g : M ⟶ M') (g' : M' ⟶ M'') :
    θ.precomp (g ≫ g') = (θ.precomp g').precomp g := by
  ext i V x
  rfl

/-- Precomposition and postcomposition of a semilinear map commute. -/
theorem precomp_postcomp (θ : SemilinearHom φ M' N) (g : M ⟶ M') (h : N ⟶ N') :
    (θ.precomp g).postcomp h = (θ.postcomp h).precomp g := by
  ext i V x
  rfl

end Composition

section TransComposition

variable {M M' : DifferentialGradedModule.{t, a'', m''} A''}
  {P P' : DifferentialGradedModule.{t, a', m'} A'}
  {N N' : DifferentialGradedModule.{t, a, m} A}

/-- Postcomposing a composite of semilinear maps with a morphism is composing with the
postcomposite of the second map. -/
theorem trans_postcomp (θ : SemilinearHom ψ M P) (ρ : SemilinearHom φ P N) (h : N ⟶ N') :
    (θ.trans ρ).postcomp h = θ.trans (ρ.postcomp h) := by
  ext i W x
  rfl

/-- Composing with the precomposite of the second map by `k` is the same as composing the
postcomposite of the first map by `k` with the second map. -/
theorem trans_precomp (θ : SemilinearHom ψ M P) (ρ : SemilinearHom φ P' N) (k : P ⟶ P') :
    θ.trans (ρ.precomp k) = (θ.postcomp k).trans ρ := by
  ext i W x
  rfl

/-- Composing the precomposite of the first map by `g` is precomposing the composite by `g`. -/
theorem precomp_trans (θ : SemilinearHom ψ M' P) (ρ : SemilinearHom φ P N) (g : M ⟶ M') :
    (θ.precomp g).trans ρ = (θ.trans ρ).precomp g := by
  ext i W x
  rfl

end TransComposition

end SemilinearHom

variable {u : C' ⥤ C} {σ : R'.obj ⟶ u.op ⋙ R.obj} {v : C'' ⥤ C'}
  {τ : R''.obj ⟶ v.op ⋙ R'.obj} {A : DifferentialGradedAlgebra.{t, a} R}
  {A' : DifferentialGradedAlgebra.{t, a'} R'} {A'' : DifferentialGradedAlgebra.{t, a''} R''}
  {φ : DifferentialGradedAlgebra.SemilinearHom u σ A' A}
  {ψ : DifferentialGradedAlgebra.SemilinearHom v τ A'' A'}

/-- A semilinear map `θ : M ⟶ N` exhibits `N` as the pullback `f^*M` of the right differential
graded `A'`-module `M` when every `φ`-semilinear map out of `M` factors through `θ` by a unique
morphism of right differential graded `A`-modules. -/
structure IsPullback {M : DifferentialGradedModule.{t, a', m'} A'}
    {N : DifferentialGradedModule.{t, a, m} A} (θ : SemilinearHom φ M N) where
  /-- The morphism through which a `φ`-semilinear map out of `M` factors. -/
  desc {N' : DifferentialGradedModule.{t, a, m} A} (θ' : SemilinearHom φ M N') : N ⟶ N'
  /-- The factorisation holds. -/
  fac {N' : DifferentialGradedModule.{t, a, m} A} (θ' : SemilinearHom φ M N') :
    θ.postcomp (desc θ') = θ'
  /-- The factorising morphism is the only one. -/
  uniq {N' : DifferentialGradedModule.{t, a, m} A} (θ' : SemilinearHom φ M N') (h : N ⟶ N')
    (hh : θ.postcomp h = θ') : h = desc θ'

namespace IsPullback

variable {M : DifferentialGradedModule.{t, a', m'} A'}
  {N : DifferentialGradedModule.{t, a, m} A} {θ : SemilinearHom φ M N}

/-- Two morphisms out of a pullback which agree after composition with the unit are equal. -/
theorem hom_ext (hN : IsPullback θ) {N' : DifferentialGradedModule.{t, a, m} A} {h h' : N ⟶ N'}
    (e : θ.postcomp h = θ.postcomp h') : h = h' :=
  (hN.uniq _ h rfl).trans (hN.uniq _ h' e.symm).symm

/-- The morphism out of a pullback through which the postcomposite of the unit with `h` factors is
`h` itself. -/
@[simp]
theorem desc_postcomp (hN : IsPullback θ) {N' : DifferentialGradedModule.{t, a, m} A}
    (h : N ⟶ N') : hN.desc (θ.postcomp h) = h :=
  (hN.uniq _ h rfl).symm

/-- The universal property of the pullback as a bijection: morphisms out of `f^*M` are the
`φ`-semilinear maps out of `M`. -/
def homEquiv (hN : IsPullback θ) (N' : DifferentialGradedModule.{t, a, m} A) :
    (N ⟶ N') ≃ SemilinearHom φ M N' where
  toFun h := θ.postcomp h
  invFun θ' := hN.desc θ'
  left_inv h := hN.desc_postcomp h
  right_inv θ' := hN.fac θ'

/-- **The converse of `homEquiv`**: a family of bijections between the morphisms out of `N` and
the `φ`-semilinear maps out of `M`, natural in the target, exhibits its value at the identity as
the unit of a pullback. This is how a *constructed* pullback is recognised, the construction
coming with the bijection rather than with the factorisation property. -/
def ofHomEquiv
    (e : ∀ N' : DifferentialGradedModule.{t, a, m} A, (N ⟶ N') ≃ SemilinearHom φ M N')
    (he : ∀ (N' N'' : DifferentialGradedModule.{t, a, m} A) (g : N ⟶ N') (h : N' ⟶ N''),
      e N'' (g ≫ h) = (e N' g).postcomp h) :
    IsPullback (e N (𝟙 N)) where
  desc {N'} θ' := (e N').symm θ'
  fac {N'} θ' := by
    refine Eq.trans (congrArg (fun ϑ : SemilinearHom φ M N' => ϑ)
      (he N N' (𝟙 N) ((e N').symm θ')).symm) ?_
    rw [Category.id_comp, Equiv.apply_symm_apply]
  uniq {N'} θ' h hh := by
    refine (e N').injective ?_
    rw [Equiv.apply_symm_apply, ← hh, ← he N N' (𝟙 N) h, Category.id_comp]

/-- The canonical isomorphism between two pullbacks of the same right differential graded
module: the unique morphism compatible with the two units. -/
noncomputable def isoOfPullback {N₁ N₂ : DifferentialGradedModule.{t, a, m} A}
    {θ₁ : SemilinearHom φ M N₁} {θ₂ : SemilinearHom φ M N₂} (h₁ : IsPullback θ₁)
    (h₂ : IsPullback θ₂) : N₁ ≅ N₂ where
  hom := h₁.desc θ₂
  inv := h₂.desc θ₁
  hom_inv_id := h₁.hom_ext (calc
    θ₁.postcomp (h₁.desc θ₂ ≫ h₂.desc θ₁)
        = (θ₁.postcomp (h₁.desc θ₂)).postcomp (h₂.desc θ₁) :=
          SemilinearHom.postcomp_comp _ _ _
    _ = θ₂.postcomp (h₂.desc θ₁) := by rw [h₁.fac]
    _ = θ₁ := h₂.fac θ₁
    _ = θ₁.postcomp (𝟙 N₁) := (SemilinearHom.postcomp_id θ₁).symm)
  inv_hom_id := h₂.hom_ext (calc
    θ₂.postcomp (h₂.desc θ₁ ≫ h₁.desc θ₂)
        = (θ₂.postcomp (h₂.desc θ₁)).postcomp (h₁.desc θ₂) :=
          SemilinearHom.postcomp_comp _ _ _
    _ = θ₁.postcomp (h₁.desc θ₂) := by rw [h₂.fac]
    _ = θ₂ := h₁.fac θ₂
    _ = θ₂.postcomp (𝟙 N₂) := (SemilinearHom.postcomp_id θ₂).symm)

/-- The canonical isomorphism between two pullbacks carries the first unit to the second. -/
@[simp]
theorem postcomp_isoOfPullback_hom {N₁ N₂ : DifferentialGradedModule.{t, a, m} A}
    {θ₁ : SemilinearHom φ M N₁} {θ₂ : SemilinearHom φ M N₂} (h₁ : IsPullback θ₁)
    (h₂ : IsPullback θ₂) : θ₁.postcomp (h₁.isoOfPullback h₂).hom = θ₂ :=
  h₁.fac θ₂

end IsPullback

/-- If two morphisms out of a pullback, followed by compatible comparison morphisms, agree on
the unit, then they agree: the square of pullback morphisms commutes. -/
private theorem comp_eq_of_postcomp_eq {u₀ : C'' ⥤ C} {σ₀ : R''.obj ⟶ u₀.op ⋙ R.obj}
    {φ₀ : DifferentialGradedAlgebra.SemilinearHom u₀ σ₀ A'' A}
    {M M₂ : DifferentialGradedModule.{t, a'', m''} A''}
    {N₁ N₂ N₁' N₂' : DifferentialGradedModule.{t, a, m} A} {g : M ⟶ M₂}
    {θ₁ : SemilinearHom φ₀ M N₁} (hθ₁ : IsPullback θ₁) {θ₂ : SemilinearHom φ₀ M₂ N₂}
    {κ₁ : SemilinearHom φ₀ M N₁'} {κ₂ : SemilinearHom φ₀ M₂ N₂'} {a : N₁ ⟶ N₂}
    {b : N₁' ⟶ N₂'} {c₁ : N₁ ⟶ N₁'} {c₂ : N₂ ⟶ N₂'} (ha : θ₁.postcomp a = θ₂.precomp g)
    (hc₁ : θ₁.postcomp c₁ = κ₁) (hc₂ : θ₂.postcomp c₂ = κ₂) (hb : κ₁.postcomp b = κ₂.precomp g) :
    a ≫ c₂ = c₁ ≫ b := by
  refine hθ₁.hom_ext ?_
  rw [SemilinearHom.postcomp_comp, SemilinearHom.postcomp_comp, ha, hc₁, hb,
    SemilinearHom.precomp_postcomp, hc₂]

/-- A pullback of every right differential graded `A'`-module at once, along a morphism of ringed
sites `f` and a semilinear homomorphism `φ : A' ⟶ f_*A`: the module `f^*M`, its unit, and the
universal property of the unit. -/
structure PullbackData (φ : DifferentialGradedAlgebra.SemilinearHom u σ A' A) where
  /-- The pullback of a right differential graded `A'`-module. -/
  obj (M : DifferentialGradedModule.{t, a', m'} A') : DifferentialGradedModule.{t, a, m} A
  /-- The unit, a `φ`-semilinear map from a module to its pullback. -/
  unit (M : DifferentialGradedModule.{t, a', m'} A') : SemilinearHom φ M (obj M)
  /-- The unit exhibits the pullback as the pullback. -/
  isPullback (M : DifferentialGradedModule.{t, a', m'} A') : IsPullback (unit M)

namespace PullbackData

/-- The pullback of a morphism of right differential graded `A'`-modules: the unique morphism of
the pullbacks compatible with the two units. -/
noncomputable def map (P : PullbackData φ)
    {M M₂ : DifferentialGradedModule.{t, a', m'} A'} (g : M ⟶ M₂) : P.obj M ⟶ P.obj M₂ :=
  (P.isPullback M).desc ((P.unit M₂).precomp g)

/-- The unit of the pullback is natural: composing it with the pullback of a morphism is the
same as precomposing the unit of the target with that morphism. -/
@[simp]
theorem unit_postcomp_map (P : PullbackData φ)
    {M M₂ : DifferentialGradedModule.{t, a', m'} A'} (g : M ⟶ M₂) :
    (P.unit M).postcomp (P.map g) = (P.unit M₂).precomp g :=
  (P.isPullback M).fac _

/-- The pullback functor `f^* : Mod^dg(A', d) ⥤ Mod^dg(A, d)`. On a morphism it is the unique
morphism of pullbacks compatible with the units, so the functor is determined by the data. -/
noncomputable def functor (P : PullbackData φ) :
    DifferentialGradedModule.{t, a', m'} A' ⥤ DifferentialGradedModule.{t, a, m} A where
  obj M := P.obj M
  map {M M₂} g := P.map g
  map_id M := ((P.isPullback M).uniq _ (𝟙 _) (by
    rw [SemilinearHom.postcomp_id, SemilinearHom.precomp_id])).symm
  map_comp {M M₂ M₃} g g' := ((P.isPullback M).uniq _ _ (by
    rw [SemilinearHom.postcomp_comp, P.unit_postcomp_map, SemilinearHom.precomp_postcomp,
      P.unit_postcomp_map, ← SemilinearHom.precomp_comp])).symm

/-- The pullback functor sends a module to its pullback. -/
@[simp]
theorem functor_obj (P : PullbackData φ) (M : DifferentialGradedModule.{t, a', m'} A') :
    P.functor.obj M = P.obj M :=
  rfl

/-- The pullback functor sends a morphism to its pullback `P.map g`. -/
@[simp]
theorem functor_map (P : PullbackData φ) {M M₂ : DifferentialGradedModule.{t, a', m'} A'}
    (g : M ⟶ M₂) : P.functor.map g = P.map g :=
  rfl

/-- The canonical isomorphism between the pullbacks of a module given by two pullback data. -/
noncomputable def compare (P Q : PullbackData φ)
    (M : DifferentialGradedModule.{t, a', m'} A') : P.obj M ≅ Q.obj M :=
  (P.isPullback M).isoOfPullback (Q.isPullback M)

/-- The comparison isomorphism between two pullbacks of a module is compatible with the
units. -/
@[simp]
theorem unit_postcomp_compare (P Q : PullbackData φ)
    (M : DifferentialGradedModule.{t, a', m'} A') :
    (P.unit M).postcomp (P.compare Q M).hom = Q.unit M :=
  (P.isPullback M).fac _

/-- The comparison isomorphism between two pullbacks is natural. -/
theorem map_comp_compare (P Q : PullbackData φ)
    {M M₂ : DifferentialGradedModule.{t, a', m'} A'} (g : M ⟶ M₂) :
    P.map g ≫ (P.compare Q M₂).hom = (P.compare Q M).hom ≫ Q.map g :=
  comp_eq_of_postcomp_eq (P.isPullback M) (P.unit_postcomp_map g)
    (P.unit_postcomp_compare Q M) (P.unit_postcomp_compare Q M₂) (Q.unit_postcomp_map g)

/-- Two pullback functors for the same morphism of ringed sites and the same semilinear
homomorphism of algebras are naturally isomorphic, by the unique natural isomorphism compatible
with the units. -/
noncomputable def isoFunctor (P Q : PullbackData φ) : P.functor ≅ Q.functor :=
  NatIso.ofComponents (fun M => P.compare Q M) (fun g => P.map_comp_compare Q g)

end PullbackData

namespace SemilinearHom

/-- The unit `θ : M ⟶ P` of a pullback is *universal for a further morphism of ringed sites*
when composition with it identifies the `φ`-semilinear maps from `P` to `N` with the
`ψ ∘ φ`-semilinear maps from `M` to `N`. The pullback `P = g⁻¹M ⊗_{g⁻¹A''} A'` has this
property, because a `φ`-semilinear map `P ⟶ N` is a morphism of right differential graded
`A'`-modules `P ⟶ f_*N`; it is what makes pullback along a composite the composite of the
pullbacks. -/
structure IsUniversal {M : DifferentialGradedModule.{t, a'', m''} A''}
    {P : DifferentialGradedModule.{t, a', m'} A'} (θ : SemilinearHom ψ M P)
    (φ : DifferentialGradedAlgebra.SemilinearHom u σ A' A)
    (N : DifferentialGradedModule.{t, a, m} A) where
  /-- Composition with `θ` identifies the two sets of semilinear maps. -/
  transEquiv : SemilinearHom φ P N ≃ SemilinearHom (ψ.trans φ) M N
  /-- The identification is composition with `θ`. -/
  transEquiv_apply (ρ : SemilinearHom φ P N) : transEquiv ρ = θ.trans ρ

end SemilinearHom

/-- The composite of the unit of a pullback along `g` with the unit of a pullback along `f`
exhibits a pullback along the composite `g ∘ f`, provided the first unit stays universal when
tested against the `φ`-semilinear maps out of its target. -/
def IsPullback.trans {M : DifferentialGradedModule.{t, a'', m''} A''}
    {P : DifferentialGradedModule.{t, a', m'} A'} {N : DifferentialGradedModule.{t, a, m} A}
    {θ : SemilinearHom ψ M P} {ρ : SemilinearHom φ P N}
    (hθ : ∀ N' : DifferentialGradedModule.{t, a, m} A, θ.IsUniversal φ N')
    (hρ : IsPullback ρ) : IsPullback (θ.trans ρ) where
  desc {N'} ϑ := hρ.desc ((hθ N').transEquiv.symm ϑ)
  fac {N'} ϑ := by
    rw [SemilinearHom.trans_postcomp, hρ.fac, ← (hθ N').transEquiv_apply,
      Equiv.apply_symm_apply]
  uniq {N'} ϑ h hh := by
    refine hρ.uniq _ h ((hθ N').transEquiv.injective ?_)
    rw [(hθ N').transEquiv_apply, Equiv.apply_symm_apply, ← SemilinearHom.trans_postcomp, hh]

namespace PullbackData

/-- The unit of the composite of a pullback along `g` and a pullback along `f`: the composite of
the two units, a semilinear map along the composite morphism of ringed sites. -/
def transUnit (Pφ : PullbackData φ) (Pψ : PullbackData ψ)
    (M : DifferentialGradedModule.{t, a'', m''} A'') :
    SemilinearHom (ψ.trans φ) M (Pφ.obj (Pψ.obj M)) :=
  (Pψ.unit M).trans (Pφ.unit (Pψ.obj M))

/-- The unit of the composite of two pullbacks is natural. -/
theorem transUnit_postcomp_map (Pφ : PullbackData φ) (Pψ : PullbackData ψ)
    {M M₂ : DifferentialGradedModule.{t, a'', m''} A''} (g : M ⟶ M₂) :
    (Pφ.transUnit Pψ M).postcomp (Pφ.map (Pψ.map g))
      = (Pφ.transUnit Pψ M₂).precomp g := calc
  (Pφ.transUnit Pψ M).postcomp (Pφ.map (Pψ.map g))
      = (Pψ.unit M).trans ((Pφ.unit (Pψ.obj M)).postcomp (Pφ.map (Pψ.map g))) :=
        SemilinearHom.trans_postcomp _ _ _
  _ = (Pψ.unit M).trans ((Pφ.unit (Pψ.obj M₂)).precomp (Pψ.map g)) :=
        congrArg (fun ρ : SemilinearHom φ (Pψ.obj M) (Pφ.obj (Pψ.obj M₂)) =>
          SemilinearHom.trans (Pψ.unit M) ρ) (Pφ.unit_postcomp_map (Pψ.map g))
  _ = ((Pψ.unit M).postcomp (Pψ.map g)).trans (Pφ.unit (Pψ.obj M₂)) :=
        SemilinearHom.trans_precomp _ _ _
  _ = ((Pψ.unit M₂).precomp g).trans (Pφ.unit (Pψ.obj M₂)) :=
        congrArg (fun θ : SemilinearHom ψ M (Pψ.obj M₂) =>
          SemilinearHom.trans θ (Pφ.unit (Pψ.obj M₂))) (Pψ.unit_postcomp_map g)
  _ = (Pφ.transUnit Pψ M₂).precomp g := SemilinearHom.precomp_trans _ _ _

/-- The composite of a pullback along `g` and a pullback along `f` is a pullback along the
composite `g ∘ f`. -/
def transIsPullback (Pφ : PullbackData φ) (Pψ : PullbackData ψ)
    (hψ : ∀ (M : DifferentialGradedModule.{t, a'', m''} A'')
      (N : DifferentialGradedModule.{t, a, m} A), (Pψ.unit M).IsUniversal φ N)
    (M : DifferentialGradedModule.{t, a'', m''} A'') : IsPullback (Pφ.transUnit Pψ M) :=
  IsPullback.trans (hψ M) (Pφ.isPullback (Pψ.obj M))

/-- The canonical isomorphism from the composite of the two pullbacks of a module to its
pullback along the composite morphism of ringed sites. -/
noncomputable def transCompare (Pφ : PullbackData φ) (Pψ : PullbackData ψ)
    (Pχ : PullbackData (ψ.trans φ))
    (hψ : ∀ (M : DifferentialGradedModule.{t, a'', m''} A'')
      (N : DifferentialGradedModule.{t, a, m} A), (Pψ.unit M).IsUniversal φ N)
    (M : DifferentialGradedModule.{t, a'', m''} A'') : Pφ.obj (Pψ.obj M) ≅ Pχ.obj M :=
  (Pφ.transIsPullback Pψ hψ M).isoOfPullback (Pχ.isPullback M)

/-- The comparison isomorphism for a composite is compatible with the units. -/
@[simp]
theorem transUnit_postcomp_transCompare (Pφ : PullbackData φ) (Pψ : PullbackData ψ)
    (Pχ : PullbackData (ψ.trans φ))
    (hψ : ∀ (M : DifferentialGradedModule.{t, a'', m''} A'')
      (N : DifferentialGradedModule.{t, a, m} A), (Pψ.unit M).IsUniversal φ N)
    (M : DifferentialGradedModule.{t, a'', m''} A'') :
    (Pφ.transUnit Pψ M).postcomp (Pφ.transCompare Pψ Pχ hψ M).hom = Pχ.unit M :=
  (Pφ.transIsPullback Pψ hψ M).fac _

/-- The comparison isomorphism for a composite is natural. -/
theorem transMap_comp_transCompare (Pφ : PullbackData φ) (Pψ : PullbackData ψ)
    (Pχ : PullbackData (ψ.trans φ))
    (hψ : ∀ (M : DifferentialGradedModule.{t, a'', m''} A'')
      (N : DifferentialGradedModule.{t, a, m} A), (Pψ.unit M).IsUniversal φ N)
    {M M₂ : DifferentialGradedModule.{t, a'', m''} A''} (g : M ⟶ M₂) :
    Pφ.map (Pψ.map g) ≫ (Pφ.transCompare Pψ Pχ hψ M₂).hom
      = (Pφ.transCompare Pψ Pχ hψ M).hom ≫ Pχ.map g :=
  comp_eq_of_postcomp_eq (Pφ.transIsPullback Pψ hψ M) (Pφ.transUnit_postcomp_map Pψ g)
    (Pφ.transUnit_postcomp_transCompare Pψ Pχ hψ M)
    (Pφ.transUnit_postcomp_transCompare Pψ Pχ hψ M₂) (Pχ.unit_postcomp_map g)

/-- Pullback along a composite of two morphisms of ringed sites is naturally isomorphic to the
composite of the two pullbacks. -/
noncomputable def transIso (Pφ : PullbackData φ) (Pψ : PullbackData ψ)
    (Pχ : PullbackData (ψ.trans φ))
    (hψ : ∀ (M : DifferentialGradedModule.{t, a'', m''} A'')
      (N : DifferentialGradedModule.{t, a, m} A), (Pψ.unit M).IsUniversal φ N) :
    Pψ.functor ⋙ Pφ.functor ≅ Pχ.functor :=
  NatIso.ofComponents (fun M => Pφ.transCompare Pψ Pχ hψ M)
    (fun g => Pφ.transMap_comp_transCompare Pψ Pχ hψ g)

/-- **A pullback along a composite, built from the two pullbacks.** The composite of a pullback
along `g` and a pullback along `f` is a pullback along `g ∘ f`, by `transIsPullback`, so it is
itself a `PullbackData` for the composite homomorphism — no datum for the composite has to be
assumed. -/
def trans (Pφ : PullbackData φ) (Pψ : PullbackData ψ)
    (hψ : ∀ (M : DifferentialGradedModule.{t, a'', m''} A'')
      (N : DifferentialGradedModule.{t, a, m} A), (Pψ.unit M).IsUniversal φ N) :
    PullbackData (ψ.trans φ) where
  obj M := Pφ.obj (Pψ.obj M)
  unit M := Pφ.transUnit Pψ M
  isPullback M := Pφ.transIsPullback Pψ hψ M

/-- The pullback along a composite built from the two pullbacks acts on a morphism as the two
pullbacks do in turn: both are the morphism compatible with the composite units, and that one is
unique. -/
@[simp]
theorem trans_map (Pφ : PullbackData φ) (Pψ : PullbackData ψ)
    (hψ : ∀ (M : DifferentialGradedModule.{t, a'', m''} A'')
      (N : DifferentialGradedModule.{t, a, m} A), (Pψ.unit M).IsUniversal φ N)
    {M M₂ : DifferentialGradedModule.{t, a'', m''} A''} (g : M ⟶ M₂) :
    (Pφ.trans Pψ hψ).map g = Pφ.map (Pψ.map g) :=
  ((Pφ.transIsPullback Pψ hψ M).uniq _ _ (Pφ.transUnit_postcomp_map Pψ g)).symm

/-- Transporting a pullback datum along an equality of semilinear homomorphisms does not change
its pullback functor: the functor's type does not mention the homomorphism. -/
theorem functor_congr {θ θ' : DifferentialGradedAlgebra.SemilinearHom u σ A' A} (h : θ = θ')
    (P : PullbackData.{t, a, m, v, u, a', m'} θ) :
    (h ▸ P : PullbackData.{t, a, m, v, u, a', m'} θ').functor = P.functor := by
  subst h
  rfl

end PullbackData

end DifferentialGradedModule

end SheafOfModules

end
