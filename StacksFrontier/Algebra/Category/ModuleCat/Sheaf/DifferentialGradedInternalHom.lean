module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedForgetColimits
public import StacksCore.Tactic.StacksAttribute

/-!
# Local sections of the internal hom for sheaves of differential graded modules

Let `R` be a sheaf of rings on a site `(C, J)`, let `A` be a sheaf of differential graded
`R`-algebras and let `M` and `L` be right differential graded `A`-modules. The differential
graded internal hom is the complex of sheaves of `R`-modules

`SheafHom^dg_A(M, L) = ⨁_n SheafHom^n_A(M, L)`,

a section of whose degree-`n` part over an object `U` of the site is a map `M|_U → L|_U` of
right differential graded `A|_U`-modules homogeneous of degree `n`, with differential
`d(f) = d_L|_U ∘ f - (-1)^n f ∘ d_M|_U`, and with composition of homogeneous maps as its
multiplication.

This file provides the vocabulary of those local sections: the degree-`n` local graded
homomorphisms, their `A`-linear ones, their composition, the value of the differential on them,
and the predicate saying that a given complex of sheaves of `R`-modules *is* the internal hom.
The complex itself is constructed in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedInternalHomSheaf.lean`
(`SheafOfModules.sheafHomComplex`).

## Main definitions

* `SheafOfModules.LocalGradedHom` is a degree-`n` map `M|_U → L|_U` of the underlying graded
  `R|_U`-modules, written out as a family of maps on sections over the objects `V ⟶ U` of the
  slice site; `SheafOfModules.LocalGradedHom.IsLinear` is `A|_U`-linearity, and
  `SheafOfModules.LocalHom` is a degree-`n` map of right differential graded `A|_U`-modules,
  i.e. a local section of `SheafHom^n_A(M, L)`.
* `SheafOfModules.LocalGradedHom.comp` and `SheafOfModules.LocalHom.comp` are the composition
  of local homomorphisms, which is the composition map of the internal hom on local sections,
  and `SheafOfModules.LocalGradedHom.id` is the identity local homomorphism.
* `SheafOfModules.localDiffApp` is the value on local sections of the differential
  `d(f) = d_L ∘ f - (-1)^n f ∘ d_M` of the internal hom.
* `SheafOfModules.IsInternalHom` says that a complex `H` of sheaves of `R`-modules is
  `SheafHom^dg_A(M, L)`: its degree-`n` sections over `U` are the degree-`n` local
  homomorphisms `M|_U → L|_U`, additively, `R`-linearly and compatibly with restriction, and
  its differential is `SheafOfModules.localDiffApp`.
* `SheafOfModules.InternalHomFunctorData` packages an internal hom for all pairs of modules at
  once as a bifunctor, contravariant in the source and covariant in the target, together with
  the description of its action on morphisms.

## Main results

* `SheafOfModules.LocalGradedHom.ext` and `SheafOfModules.LocalHom.ext`: a local homomorphism
  is determined by its values on local sections.
* `SheafOfModules.LocalHom.comp_app` computes a composition through an arbitrary intermediate
  degree.
* `SheafOfModules.IsInternalHom.sections_ext` and
  `SheafOfModules.IsInternalHom.sectionsEquiv_zero`: a section of the internal hom is
  determined by the local homomorphism it names, and the zero section names the zero
  homomorphism.

## Implementation notes

There is no internal hom for sheaves of modules available to build on: the monoidal structure
on presheaves of modules is defined only over a presheaf of *commutative* rings, and sheaves of
modules carry limits, colimits, abelianness and change of rings but nothing monoidal. So the
internal hom cannot be written down by a formula and is instead pinned by a universal property:
a complex of sheaves of `R`-modules *is* the internal hom when its local sections are the local
homomorphisms, additively and `R`-linearly and compatibly with restriction, and its
differential is given by `localDiffApp`. This determines it up to canonical isomorphism, and it
pins the sheaf-of-modules structure as well as the underlying sheaves of sets, since the
identification of local sections is required to be additive and `R`-linear
(`IsInternalHom.sectionsEquiv_add` and `IsInternalHom.sectionsEquiv_smul`). Likewise the action
of the bifunctor on morphisms is pinned to be `φ ↦ g ∘ φ ∘ f` on local sections
(`InternalHomFunctorData.map_spec`).

Restriction of a sheaf of modules to a slice site is not available either, so a degree-`n` map
`M|_U → L|_U` is written out directly as a family of maps on sections over the objects `V ⟶ U`
of the slice site, which is the same datum.

Degrees are carried in the form `(i, j, hij : i + n = j)` used by the cochains of
`CochainComplex.HomComplex`. The point is that the intermediate degrees of every formula can
then be chosen so that both sides are sections of one and the same sheaf: no statement below
needs a heterogeneous equality or a transport along an equality of degrees.

The compatibility of the composition map with the differentials, proved by the same computation
as for the hom-complex of the differential graded category of modules, is
`SheafOfModules.sheafHomComp_leibniz` in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedInternalHomComposition.lean`,
together with the identification of the global sections of the internal hom with the
hom-complex of `Mod^dg(A, d)`.

The universes of the site, of the sheaf of rings, of the algebra and of each of the three
modules `M`, `L` and `H` are independent. The bifunctor has to take the module universes of
`M`, `L` and `H` equal, since it is an endo-bifunctor of one category of differential graded
modules.

## References

* [Stacks Project, Tag 0FRN](https://stacks.math.columbia.edu/tag/0FRN)
* [Stacks Project, Tag 0FRF](https://stacks.math.columbia.edu/tag/0FRF)
* [Stacks Project, Tag 0FRI](https://stacks.math.columbia.edu/tag/0FRI)
-/

@[expose] public section

open CategoryTheory

universe t a w z s v u

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A : DifferentialGradedAlgebra.{t, a} R}

/-- A map `M|_U → L|_U` of the underlying graded `R|_U`-modules, homogeneous of degree `n`,
written out as a family of maps on sections over the objects `V ⟶ U` of the slice site. -/
structure LocalGradedHom (M : DifferentialGradedModule.{t, a, w} A)
    (L : DifferentialGradedModule.{t, a, z} A) (n : ℤ) (U : C) where
  /-- The map on sections over an object `V ⟶ U` of the slice site, from degree `i` to degree
  `j`, where `i + n = j`. -/
  app (i j : ℤ) (hij : i + n = j) (V : Over U) :
    (M.complex.X i).val.obj (Opposite.op V.left) →+
      (L.complex.X j).val.obj (Opposite.op V.left)
  /-- The maps are linear over the sheaf of rings. -/
  map_smul (i j : ℤ) (hij : i + n = j) (V : Over U)
      (r : R.obj.obj (Opposite.op V.left))
      (x : (M.complex.X i).val.obj (Opposite.op V.left)) :
    app i j hij V (r • x) = r • app i j hij V x
  /-- The maps commute with restriction inside the slice site. -/
  naturality (i j : ℤ) (hij : i + n = j) {V W : Over U} (g : W ⟶ V)
      (x : (M.complex.X i).val.obj (Opposite.op V.left)) :
    (L.complex.X j).val.map g.left.op (app i j hij V x) =
      app i j hij W ((M.complex.X i).val.map g.left.op x)

namespace LocalGradedHom

variable {M : DifferentialGradedModule.{t, a, w} A} {L : DifferentialGradedModule.{t, a, z} A}

/-- A degree-`n` map of the underlying graded modules is determined by its values on local
sections. -/
@[ext]
theorem ext {n : ℤ} {U : C} {f g : LocalGradedHom M L n U}
    (h : ∀ (i j : ℤ) (hij : i + n = j) (V : Over U)
      (x : (M.complex.X i).val.obj (Opposite.op V.left)),
      f.app i j hij V x = g.app i j hij V x) : f = g := by
  cases f with
  | mk fApp fSmul fNat =>
    cases g with
    | mk gApp gSmul gNat =>
      have hApp : fApp = gApp := by
        funext i j hij V
        exact AddMonoidHom.ext fun x => h i j hij V x
      subst hApp
      rfl

/-- A degree-`n` map of the underlying graded `R|_U`-modules is `A|_U`-linear when
`f (x a) = f (x) a` for homogeneous local sections `x` of `M` and `a` of `A`. -/
def IsLinear {n : ℤ} {U : C} (f : LocalGradedHom M L n U) : Prop :=
  ∀ (i j : ℤ) (hij : i + n = j) (p : ℤ) (V : Over U)
    (x : (M.complex.X i).val.obj (Opposite.op V.left))
    (b : (A.complex.X p).val.obj (Opposite.op V.left)),
    f.app (i + p) (j + p) (by omega) V ((M.mul i p).app (Opposite.op V.left) x b) =
      (L.mul j p).app (Opposite.op V.left) (f.app i j hij V x) b

end LocalGradedHom

/-- A local section of `SheafHom^n_A(M, L)` over `U`: a map `M|_U → L|_U` of right differential
graded `A|_U`-modules homogeneous of degree `n`. -/
@[stacks 0FRN "a local section of SheafHom^n_A(M, L) over U: an A|_U-linear map M|_U → L|_U
homogeneous of degree n"]
structure LocalHom (M : DifferentialGradedModule.{t, a, w} A)
    (L : DifferentialGradedModule.{t, a, z} A) (n : ℤ) (U : C)
    extends LocalGradedHom M L n U where
  /-- The map is `A|_U`-linear. -/
  isLinear : LocalGradedHom.IsLinear toLocalGradedHom

/-- A degree-`n` map of right differential graded modules is determined by its values on local
sections. -/
@[ext]
theorem LocalHom.ext {M : DifferentialGradedModule.{t, a, w} A}
    {L : DifferentialGradedModule.{t, a, z} A} {n : ℤ} {U : C} {f g : LocalHom M L n U}
    (h : ∀ (i j : ℤ) (hij : i + n = j) (V : Over U)
      (x : (M.complex.X i).val.obj (Opposite.op V.left)),
      f.app i j hij V x = g.app i j hij V x) : f = g := by
  cases f with
  | mk f hf =>
    cases g with
    | mk g hg =>
      have hfg : f = g := LocalGradedHom.ext h
      subst hfg
      rfl

namespace LocalGradedHom

variable {K : DifferentialGradedModule.{t, a, s} A} {M : DifferentialGradedModule.{t, a, w} A}
  {L : DifferentialGradedModule.{t, a, z} A}

/-- The composition of a degree-`n` map `K|_U → M|_U` with a degree-`m` map `M|_U → L|_U`, as a
degree-`nm` map `K|_U → L|_U`. This is the composition map of the internal hom, on local
sections. -/
def comp {n m nm : ℤ} {U : C} (g : LocalGradedHom K M n U) (f : LocalGradedHom M L m U)
    (h : n + m = nm) : LocalGradedHom K L nm U where
  app i j hij V := (f.app (i + n) j (by omega) V).comp (g.app i (i + n) rfl V)
  map_smul i j hij V r x := by
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, g.map_smul, f.map_smul]
  naturality i j hij {V W} k x := by
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, f.naturality, g.naturality]
    rfl

/-- The composition of local homomorphisms of graded modules, computed through an arbitrary
intermediate degree. -/
theorem comp_app {n m nm : ℤ} {U : C} (g : LocalGradedHom K M n U) (f : LocalGradedHom M L m U)
    (h : n + m = nm) (i i' j : ℤ) (hii' : i + n = i') (hj : i' + m = j) (V : Over U) :
    (g.comp f h).app i j (by omega) V = (f.app i' j hj V).comp (g.app i i' hii' V) := by
  subst hii'; rfl

/-- The identity map of `M|_U`, as a degree-zero map of the underlying graded modules. -/
def id (M : DifferentialGradedModule.{t, a, w} A) (U : C) : LocalGradedHom M M 0 U where
  app i j hij V := by
    have hij' : i = j := (add_zero i).symm.trans hij
    cases hij'
    exact AddMonoidHom.id ((M.complex.X i).val.obj (Opposite.op V.left))
  map_smul i j hij V r x := by
    have hij' : i = j := (add_zero i).symm.trans hij
    cases hij'
    rfl
  naturality i j hij V W g x := by
    have hij' : i = j := (add_zero i).symm.trans hij
    cases hij'
    rfl

end LocalGradedHom

/-- The composition of local homomorphisms of right differential graded `A|_U`-modules. -/
@[stacks 0FRN "the composition map of the internal hom on local sections: composition of
homogeneous A|_U-linear maps, of degree n + m"]
def LocalHom.comp {K : DifferentialGradedModule.{t, a, s} A}
    {M : DifferentialGradedModule.{t, a, w} A} {L : DifferentialGradedModule.{t, a, z} A}
    {n m nm : ℤ} {U : C} (g : LocalHom K M n U) (f : LocalHom M L m U) (h : n + m = nm) :
    LocalHom K L nm U where
  toLocalGradedHom := g.toLocalGradedHom.comp f.toLocalGradedHom h
  isLinear i j hij p V x b := by
    rw [LocalGradedHom.comp_app g.toLocalGradedHom f.toLocalGradedHom h (i + p) (i + n + p)
        (j + p) (by omega) (by omega) V,
      LocalGradedHom.comp_app g.toLocalGradedHom f.toLocalGradedHom h i (i + n) j rfl
        (by omega) V]
    simp only [AddMonoidHom.coe_comp, Function.comp_apply]
    rw [g.isLinear i (i + n) rfl p V x b, f.isLinear (i + n) j (by omega) p V _ b]

/-- The composition of local homomorphisms of differential graded modules, computed through an
arbitrary intermediate degree. -/
theorem LocalHom.comp_app {K : DifferentialGradedModule.{t, a, s} A}
    {M : DifferentialGradedModule.{t, a, w} A} {L : DifferentialGradedModule.{t, a, z} A}
    {n m nm i i' j : ℤ} {U : C} (g : LocalHom K M n U) (f : LocalHom M L m U) (h : n + m = nm)
    (hii' : i + n = i') (hj : i' + m = j) (V : Over U)
    (x : (K.complex.X i).val.obj (Opposite.op V.left)) :
    (g.comp f h).app i j (by omega) V x = f.app i' j hj V (g.app i i' hii' V x) := by
  subst hii'; rfl

/-- The identity map of `M|_U`, as a degree-zero local homomorphism of right differential
graded `A|_U`-modules. -/
def LocalHom.id (M : DifferentialGradedModule.{t, a, w} A) (U : C) : LocalHom M M 0 U where
  toLocalGradedHom := LocalGradedHom.id M U
  isLinear i j hij p V x b := by
    have hij' : i = j := (add_zero i).symm.trans hij
    cases hij'
    rfl

/-- The value on local sections of the differential of the internal hom:
`d(f) = d_L ∘ f + (-1)^m f ∘ d_M`, which for `m = n + 1` is the rule
`d(f) = d_L ∘ f - (-1)^n f ∘ d_M`. It vanishes unless `m = n + 1`, because the differentials of
`M` and `L` do. -/
def localDiffApp {M : DifferentialGradedModule.{t, a, w} A}
    {L : DifferentialGradedModule.{t, a, z} A} {n : ℤ} {U : C} (f : LocalGradedHom M L n U)
    (m i j : ℤ) (hij : i + m = j) (V : Over U)
    (x : (M.complex.X i).val.obj (Opposite.op V.left)) :
    (L.complex.X j).val.obj (Opposite.op V.left) :=
  (L.complex.d (i + n) j).val.app (Opposite.op V.left) (f.app i (i + n) rfl V x) +
    (Int.negOnePow m : ℤ) • f.app (i + m - n) j (by omega) V
      ((M.complex.d i (i + m - n)).val.app (Opposite.op V.left) x)

/-- A complex `H` of sheaves of `R`-modules is the internal hom `SheafHom^dg_A(M, L)` when its
degree-`n` sections over `U` are the degree-`n` local homomorphisms `M|_U → L|_U`, additively
and `R`-linearly, compatibly with restriction, and its differential is
`SheafOfModules.localDiffApp`. -/
structure IsInternalHom (M : DifferentialGradedModule.{t, a, w} A)
    (L : DifferentialGradedModule.{t, a, z} A)
    (H : CochainComplex (SheafOfModules.{s} R) ℤ) where
  /-- Sections of `H` in degree `n` over `U` are the degree-`n` local homomorphisms
  `M|_U → L|_U`. -/
  sectionsEquiv (n : ℤ) (U : C) : (H.X n).val.obj (Opposite.op U) ≃ LocalHom M L n U
  /-- The identification is additive. -/
  sectionsEquiv_add (n : ℤ) (U : C) (p q : (H.X n).val.obj (Opposite.op U))
      (i j : ℤ) (hij : i + n = j) (V : Over U)
      (x : (M.complex.X i).val.obj (Opposite.op V.left)) :
    (sectionsEquiv n U (p + q)).app i j hij V x =
      (sectionsEquiv n U p).app i j hij V x + (sectionsEquiv n U q).app i j hij V x
  /-- The identification is linear over the sheaf of rings. -/
  sectionsEquiv_smul (n : ℤ) (U : C) (r : R.obj.obj (Opposite.op U))
      (p : (H.X n).val.obj (Opposite.op U)) (i j : ℤ) (hij : i + n = j) (V : Over U)
      (x : (M.complex.X i).val.obj (Opposite.op V.left)) :
    (sectionsEquiv n U (r • p)).app i j hij V x =
      R.obj.map V.hom.op r • (sectionsEquiv n U p).app i j hij V x
  /-- The identification is compatible with restriction along a morphism of the site. -/
  sectionsEquiv_naturality (n : ℤ) {U U' : C} (g : U' ⟶ U)
      (p : (H.X n).val.obj (Opposite.op U)) (i j : ℤ) (hij : i + n = j) (V : Over U') :
    (sectionsEquiv n U' ((H.X n).val.map g.op p)).app i j hij V =
      (sectionsEquiv n U p).app i j hij (Over.mk (V.hom ≫ g))
  /-- The differential of `H` is the differential `d(f) = d_L ∘ f - (-1)^n f ∘ d_M` of the
  internal hom. -/
  sectionsEquiv_d (n m : ℤ) (U : C) (p : (H.X n).val.obj (Opposite.op U))
      (i j : ℤ) (hij : i + m = j) (V : Over U)
      (x : (M.complex.X i).val.obj (Opposite.op V.left)) :
    (sectionsEquiv m U ((H.d n m).val.app (Opposite.op U) p)).app i j hij V x =
      localDiffApp (sectionsEquiv n U p).toLocalGradedHom m i j hij V x

namespace IsInternalHom

variable {M : DifferentialGradedModule.{t, a, w} A} {L : DifferentialGradedModule.{t, a, z} A}
  {H : CochainComplex (SheafOfModules.{s} R) ℤ}

/-- A section of the internal hom is determined by the local homomorphism it names. -/
theorem sections_ext (hH : IsInternalHom M L H) {n : ℤ} {U : C}
    {p q : (H.X n).val.obj (Opposite.op U)}
    (h : ∀ (i j : ℤ) (hij : i + n = j) (V : Over U)
      (x : (M.complex.X i).val.obj (Opposite.op V.left)),
      (hH.sectionsEquiv n U p).app i j hij V x = (hH.sectionsEquiv n U q).app i j hij V x) :
    p = q :=
  (hH.sectionsEquiv n U).injective (LocalHom.ext h)

/-- The zero section of the internal hom names the zero local homomorphism. -/
theorem sectionsEquiv_zero (hH : IsInternalHom M L H) (n : ℤ) (U : C) (i j : ℤ)
    (hij : i + n = j) (V : Over U)
    (x : (M.complex.X i).val.obj (Opposite.op V.left)) :
    (hH.sectionsEquiv n U (0 : (H.X n).val.obj (Opposite.op U))).app i j hij V x = 0 := by
  have h := hH.sectionsEquiv_add n U 0 0 i j hij V x
  rw [add_zero] at h
  exact left_eq_add.mp h

end IsInternalHom

/-- An internal hom of right differential graded `A`-modules for all pairs of modules at once:
a bifunctor `Mod^dg(A, d)ᵒᵖ × Mod^dg(A, d) ⟶ Comp(R)` whose values are internal homs, together
with the description of its action on morphisms as composition. -/
structure InternalHomFunctorData (A : DifferentialGradedAlgebra.{t, a} R) where
  /-- The internal hom as a bifunctor into complexes of sheaves of `R`-modules. -/
  functor : (DifferentialGradedModule.{t, a, w} A)ᵒᵖ × DifferentialGradedModule.{t, a, w} A ⥤
    CochainComplex (SheafOfModules.{w} R) ℤ
  /-- Its value at `(M, L)` is an internal hom `SheafHom^dg_A(M, L)`. -/
  isInternalHom (M L : DifferentialGradedModule.{t, a, w} A) :
    IsInternalHom M L (functor.obj ⟨Opposite.op M, L⟩)
  /-- On local sections, the bifunctor sends a pair `(f, g)` of homomorphisms to
  `φ ↦ g ∘ φ ∘ f`. -/
  map_spec {M M' L L' : DifferentialGradedModule.{t, a, w} A} (f : M' ⟶ M) (g : L ⟶ L')
      (n : ℤ) (U : C) (p : ((functor.obj ⟨Opposite.op M, L⟩).X n).val.obj (Opposite.op U))
      (i j : ℤ) (hij : i + n = j) (V : Over U)
      (x : (M'.complex.X i).val.obj (Opposite.op V.left)) :
    ((isInternalHom M' L').sectionsEquiv n U
        (((functor.map (X := ⟨Opposite.op M, L⟩) (Y := ⟨Opposite.op M', L'⟩)
            ⟨f.op, g⟩).f n).val.app (Opposite.op U) p)).app i j hij V x =
      (g.toHomologicalComplex.f j).val.app (Opposite.op V.left)
        (((isInternalHom M L).sectionsEquiv n U p).app i j hij V
          ((f.toHomologicalComplex.f i).val.app (Opposite.op V.left) x))

end SheafOfModules

end
