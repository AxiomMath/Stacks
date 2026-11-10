module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedInternalHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedTensor

/-!
# The functor `ℳ ↦ f_*SheafHom^dg_{𝒜'}(𝒩, ℳ)` on homotopy categories of differential graded
modules

Let `f` be a morphism of ringed sites, presented as a functor `u : C' ⥤ C` in the direction
opposite to `f` together with the structure map `σ : R' ⟶ f_*R` of its sheaves of rings. Let `𝒜`
and `𝒜'` be sheaves of differential graded `R`-algebras on the source, let `ℬ` be a sheaf of
differential graded `R'`-algebras on the target, let `φ : ℬ ⟶ f_*𝒜` be a homomorphism of sheaves
of differential graded algebras and let `𝒩` be a differential graded `(𝒜, 𝒜')`-bimodule, so that
both algebras of the bimodule live on the source. Then

`ℳ ↦ f_*SheafHom^dg_{𝒜'}(𝒩, ℳ)`

is a functor `Mod^dg(𝒜', d) ⥤ Mod^dg(ℬ, d)`, and it carries homotopic morphisms to homotopic
morphisms, so it induces a functor `K(Mod(𝒜', d)) ⥤ K(Mod(ℬ, d))` of homotopy categories.

The direct image is pinned here by a universal property dual to the one that pins the pullback
of `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedPullback.lean`: a
`φ`-semilinear map `ℳ ⟶ 𝒩` is the datum of a morphism `ℳ ⟶ f_*𝒩` of right differential graded
`ℬ`-modules, so `f_*𝒩` is the right differential graded `ℬ`-module *corepresenting* the
`φ`-semilinear maps into `𝒩`. This determines it up to a unique isomorphism compatible with the
counits and it determines the action of the direct image on morphisms, which is constructed
below rather than assumed.

## Main definitions

* `SheafOfModules.DifferentialGradedBimodule.toRightModule` is a differential graded
  `(𝒜, 𝒜')`-bimodule read as a right differential graded `𝒜'`-module.
* `SheafOfModules.IsSheafHom` says that a right differential graded `𝒜`-module *is* the internal
  hom `SheafHom^dg_{𝒜'}(𝒩, ℳ)`, and `SheafOfModules.SheafHomFunctorData` packages one for every
  module at once as the functor `SheafHom^dg_{𝒜'}(𝒩, -)`.
* `SheafOfModules.DifferentialGradedModule.IsPushforward` says that a `φ`-semilinear map
  `θ : 𝒫 ⟶ ℳ` exhibits `𝒫` as the direct image `f_*ℳ`, and
  `SheafOfModules.DifferentialGradedModule.PushforwardData` packages one for every module at
  once, with `...PushforwardData.functor` the resulting functor
  `f_* : Mod^dg(𝒜, d) ⥤ Mod^dg(ℬ, d)`.
* `SheafOfModules.DifferentialGradedModule.pushforwardSheafHomFunctor` is the functor
  `ℳ ↦ f_*SheafHom^dg_{𝒜'}(𝒩, ℳ)`, and
  `SheafOfModules.DifferentialGradedModule.HomotopyCategory.pushforwardSheafHom` is the functor
  it induces on the homotopy categories.

## Main results

* `SheafOfModules.DifferentialGradedModule.IsPushforward.homEquiv`: the universal property as a
  bijection between morphisms into `f_*ℳ` and `φ`-semilinear maps into `ℳ`.
* `SheafOfModules.DifferentialGradedModule.IsPushforward.isoOfPushforward`: two direct images of
  the same module are canonically isomorphic, by the unique isomorphism compatible with the two
  counits.
* `SheafOfModules.DifferentialGradedModule.PushforwardData.functor` together with
  `SheafOfModules.DifferentialGradedModule.PushforwardData.map_postcomp_counit`: the direct
  image is functorial and the counit is natural.
* `SheafOfModules.DifferentialGradedModule.preservesHomotopic_pushforwardSheafHomFunctor`:
  `ℳ ↦ f_*SheafHom^dg_{𝒜'}(𝒩, ℳ)` carries homotopic morphisms to homotopic morphisms.
* `SheafOfModules.DifferentialGradedModule.HomotopyCategory.pushforwardSheafHom_obj` and
  `...pushforwardSheafHom_map` compute the induced functor on an object and on a homotopy class,
  and `...quotient_comp_pushforwardSheafHom` and `...eq_pushforwardSheafHom` say that it is the
  unique functor factoring `ℳ ↦ f_*SheafHom^dg_{𝒜'}(𝒩, ℳ)` through the two quotient functors.

## Implementation notes

Both factors are pinned by universal properties here rather than built. The internal hom of a
bimodule is pinned by `IsSheafHom`, which says that the underlying complex is the internal hom
of `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedInternalHom.lean` and that
the right `𝒜`-action is precomposition with the left action of `𝒜` on `𝒩`; the direct image is
pinned by `IsPushforward`. Each universal property determines its object up to a unique
isomorphism and determines the action of the functor on morphisms.

The direct image is in fact constructed:
`SheafOfModules.DifferentialGradedModule.pushforwardData` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedDerivedPushforward.lean`
inhabits `PushforwardData`, and
`SheafOfModules.DifferentialGradedModule.pushforwardHomotopyExtension` of the sibling file
`DifferentialGradedPushforwardHomotopyExtension.lean` (in `StacksFrontier/Algebra/Category/`
`ModuleCat/Sheaf/`) inhabits its `HomotopyExtension`. The internal hom is not, and at the
generality of this file it cannot be: by
`SheafOfModules.DifferentialGradedModule.commutator_smul_eq_of_isInternalHom_self`, an internal
hom of a module with itself forces every commutator of the sheaf of rings to annihilate that
module, so over a sheaf of rings whose commutators act nontrivially `SheafHomFunctorData` is
empty. Tag 0FTS is therefore registered on
`SheafOfModules.DifferentialGradedModule.exists_homotopyPushforwardSheafHom`, which quantifies
over an arbitrary homotopy-preserving first factor and uses the constructed direct image; the
descent below is that theorem's content specialised to a `SheafHomFunctorData`.

`SheafHomFunctorData.HomotopyExtension` and `PushforwardData.HomotopyExtension` each say that
the functor of differential graded categories of Stacks, Tags 0FRS and 0FRG carries a homotopy
to a homotopy: a degree `-1` map out of an object that is itself only pinned in degree zero — a
universal property formulated through morphisms of differential graded modules says nothing
about maps of degree `-1` out of the object it pins.

Exactness of the induced functor is not formulated below, and no statement here mentions
triangulated categories. The homotopy category of sheaf differential graded modules over a
ringed site *is* triangulated —
`SheafOfModules.DifferentialGradedModule.HomotopyCategory.instIsTriangulated` of
[Stacks, Tag 0FS7] — and
`SheafOfModules.DifferentialGradedModule.isTriangulated_onK` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedCrossSiteExact.lean` reduces
exactness of a functor across two ringed sites to the source's own hypothesis
`F(x[1]) = F(x)[1]` on a differential graded functor. What the descent below is built from is
homotopy preservation alone, which does not supply that functor.

The universes of the two sites and their morphisms, of the two algebras on the source and the
algebra on the target, and of the bimodule, of the module `ℳ`, of the internal hom and of the
direct image are all independent, while the two sheaves of rings share the universe `t` because
the structure map of the morphism of ringed sites relates them, and the two algebras on the
source share the universe `a` because `𝒩` is a bimodule between them.

## References

* [Stacks Project, Tag 0FTS](https://stacks.math.columbia.edu/tag/0FTS)
* [Stacks Project, Tag 0FRS](https://stacks.math.columbia.edu/tag/0FRS)
* [Stacks Project, Tag 0FRG](https://stacks.math.columbia.edu/tag/0FRG)
* [Stacks Project, Tag 0FS1](https://stacks.math.columbia.edu/tag/0FS1)
-/

@[expose] public section

open CategoryTheory

universe t a a' m m' s z v u v' u'

namespace SheafOfModules

section SheafHom

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A A' : DifferentialGradedAlgebra.{t, a} R}

/-- A differential graded `(A, A')`-bimodule, read as a right differential graded `A'`-module by
forgetting the left action. -/
abbrev DifferentialGradedBimodule.toRightModule (N : DifferentialGradedBimodule.{t, a, z} A A') :
    DifferentialGradedModule.{t, a, z} A' where
  complex := N.complex
  mul := N.rightMul
  mul_assoc := N.right_assoc
  mul_one := N.one_right
  leibniz := N.leibniz_right

/-- The underlying complex of a bimodule read as a right module is the complex of the bimodule. -/
@[simp]
theorem DifferentialGradedBimodule.toRightModule_complex
    (N : DifferentialGradedBimodule.{t, a, z} A A') :
    N.toRightModule.complex = N.complex :=
  rfl

/-- A right differential graded `A`-module `H` *is* the internal hom
`SheafHom^dg_{A'}(N, M)` of a differential graded `(A, A')`-bimodule `N` and a right
differential graded `A'`-module `M` when its underlying complex of sheaves of `R`-modules is
that internal hom and its right `A`-action is precomposition with the left action of `A` on `N`,
without signs: the section `q a` is the local homomorphism `x ↦ q (a x)`. -/
structure IsSheafHom (N : DifferentialGradedBimodule.{t, a, z} A A')
    (M : DifferentialGradedModule.{t, a, s} A') (H : DifferentialGradedModule.{t, a, m} A) where
  /-- The underlying complex of `H` is the internal hom `SheafHom^dg_{A'}(N, M)`. -/
  isInternalHom : IsInternalHom N.toRightModule M H.complex
  /-- The right `A`-action on `H` is precomposition with the left action of `A` on `N`. -/
  mul_spec (n p : ℤ) (U : C) (q : (H.complex.X n).val.obj (Opposite.op U))
      (b : (A.complex.X p).val.obj (Opposite.op U)) (i j : ℤ) (hij : i + (n + p) = j)
      (V : Over U) (x : (N.complex.X i).val.obj (Opposite.op V.left)) :
    (isInternalHom.sectionsEquiv (n + p) U
        ((H.mul n p).app (Opposite.op U) q b)).app i j hij V x =
      (isInternalHom.sectionsEquiv n U q).app (p + i) j (by omega) V
        ((N.leftMul p i).app (Opposite.op V.left)
          ((A.complex.X p).val.map V.hom.op b) x)

/-- An internal hom `SheafHom^dg_{A'}(N, M)` for every right differential graded `A'`-module `M`
at once, as a functor `SheafHom^dg_{A'}(N, -) : Mod^dg(A', d) ⥤ Mod^dg(A, d)`, together with
the description of its action on morphisms as postcomposition. -/
structure SheafHomFunctorData (N : DifferentialGradedBimodule.{t, a, z} A A') where
  /-- The internal hom functor `SheafHom^dg_{A'}(N, -)`. -/
  functor : DifferentialGradedModule.{t, a, s} A' ⥤ DifferentialGradedModule.{t, a, m} A
  /-- Its value at `M` is an internal hom `SheafHom^dg_{A'}(N, M)`. -/
  isSheafHom (M : DifferentialGradedModule.{t, a, s} A') : IsSheafHom N M (functor.obj M)
  /-- On local sections, the functor sends a morphism `g` to the map determined by
  `q ↦ g ∘ q`. -/
  map_spec {M M₂ : DifferentialGradedModule.{t, a, s} A'} (g : M ⟶ M₂) (n : ℤ) (U : C)
      (q : ((functor.obj M).complex.X n).val.obj (Opposite.op U)) (i j : ℤ) (hij : i + n = j)
      (V : Over U) (x : (N.complex.X i).val.obj (Opposite.op V.left)) :
    ((isSheafHom M₂).isInternalHom.sectionsEquiv n U
        (((functor.map g).toHomologicalComplex.f n).val.app (Opposite.op U) q)).app i j hij V
          x =
      (g.toHomologicalComplex.f j).val.app (Opposite.op V.left)
        (((isSheafHom M).isInternalHom.sectionsEquiv n U q).app i j hij V x)

namespace SheafHomFunctorData

open DifferentialGradedModule

variable {N : DifferentialGradedBimodule.{t, a, z} A A'}

/-- A differential graded extension of the internal hom functor `SheafHom^dg_{A'}(N, -)`: a
homotopy between the images of the two morphisms a homotopy connects. For a homotopy `h` the
image homotopy is `q ↦ h ∘ q` on local sections. -/
structure HomotopyExtension (S : SheafHomFunctorData.{t, a, m, s, z} N) where
  /-- The image of a homotopy. -/
  mapHomotopy {M M₂ : DifferentialGradedModule.{t, a, s} A'} {ψ χ : M ⟶ M₂}
    (h : Homotopy ψ χ) : Homotopy (S.functor.map ψ) (S.functor.map χ)

/-- An internal hom functor with a differential graded extension carries homotopic morphisms to
homotopic morphisms. -/
theorem HomotopyExtension.preservesHomotopic {S : SheafHomFunctorData.{t, a, m, s, z} N}
    (E : S.HomotopyExtension) : PreservesHomotopic S.functor :=
  fun _ _ ⟨h⟩ => ⟨E.mapHomotopy h⟩

end SheafHomFunctorData

end SheafHom

section Pushforward

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {C' : Type u'} [Category.{v'} C'] {J' : GrothendieckTopology C'} {R' : Sheaf J' RingCat.{t}}

namespace DifferentialGradedModule

variable {u : C' ⥤ C} {σ : R'.obj ⟶ u.op ⋙ R.obj} {A : DifferentialGradedAlgebra.{t, a} R}
  {B : DifferentialGradedAlgebra.{t, a'} R'}
  {φ : DifferentialGradedAlgebra.SemilinearHom u σ B A}

/-- A `φ`-semilinear map `θ : P ⟶ M` exhibits `P` as the direct image `f_*M` of the right
differential graded `A`-module `M` when every `φ`-semilinear map into `M` factors through `θ` by
a unique morphism of right differential graded `B`-modules. -/
structure IsPushforward {P : DifferentialGradedModule.{t, a', m'} B}
    {M : DifferentialGradedModule.{t, a, m} A} (θ : SemilinearHom φ P M) where
  /-- The morphism through which a `φ`-semilinear map into `M` factors. -/
  lift {P' : DifferentialGradedModule.{t, a', m'} B} (θ' : SemilinearHom φ P' M) : P' ⟶ P
  /-- The factorisation holds. -/
  fac {P' : DifferentialGradedModule.{t, a', m'} B} (θ' : SemilinearHom φ P' M) :
    θ.precomp (lift θ') = θ'
  /-- The factorising morphism is the only one. -/
  uniq {P' : DifferentialGradedModule.{t, a', m'} B} (θ' : SemilinearHom φ P' M) (h : P' ⟶ P)
    (hh : θ.precomp h = θ') : h = lift θ'

namespace IsPushforward

variable {P : DifferentialGradedModule.{t, a', m'} B} {M : DifferentialGradedModule.{t, a, m} A}
  {θ : SemilinearHom φ P M}

/-- Two morphisms into a direct image which agree after composition with the counit are
equal. -/
theorem hom_ext (hP : IsPushforward θ) {P' : DifferentialGradedModule.{t, a', m'} B}
    {h h' : P' ⟶ P} (e : θ.precomp h = θ.precomp h') : h = h' :=
  (hP.uniq _ h rfl).trans (hP.uniq _ h' e.symm).symm

/-- The morphism into a direct image through which the counit precomposed with `h` factors is
`h` itself. -/
@[simp]
theorem lift_precomp (hP : IsPushforward θ) {P' : DifferentialGradedModule.{t, a', m'} B}
    (h : P' ⟶ P) : hP.lift (θ.precomp h) = h :=
  (hP.uniq _ h rfl).symm

/-- The universal property of the direct image as a bijection: morphisms into `f_*M` are the
`φ`-semilinear maps into `M`. -/
def homEquiv (hP : IsPushforward θ) (P' : DifferentialGradedModule.{t, a', m'} B) :
    (P' ⟶ P) ≃ SemilinearHom φ P' M where
  toFun h := θ.precomp h
  invFun θ' := hP.lift θ'
  left_inv h := hP.lift_precomp h
  right_inv θ' := hP.fac θ'

/-- The canonical isomorphism between two direct images of the same right differential graded
module: the unique morphism compatible with the two counits. -/
noncomputable def isoOfPushforward {P₁ P₂ : DifferentialGradedModule.{t, a', m'} B}
    {θ₁ : SemilinearHom φ P₁ M} {θ₂ : SemilinearHom φ P₂ M} (h₁ : IsPushforward θ₁)
    (h₂ : IsPushforward θ₂) : P₁ ≅ P₂ where
  hom := h₂.lift θ₁
  inv := h₁.lift θ₂
  hom_inv_id := h₁.hom_ext (calc
    θ₁.precomp (h₂.lift θ₁ ≫ h₁.lift θ₂)
        = (θ₁.precomp (h₁.lift θ₂)).precomp (h₂.lift θ₁) :=
          SemilinearHom.precomp_comp _ _ _
    _ = θ₂.precomp (h₂.lift θ₁) := by rw [h₁.fac]
    _ = θ₁ := h₂.fac θ₁
    _ = θ₁.precomp (𝟙 P₁) := (SemilinearHom.precomp_id θ₁).symm)
  inv_hom_id := h₂.hom_ext (calc
    θ₂.precomp (h₁.lift θ₂ ≫ h₂.lift θ₁)
        = (θ₂.precomp (h₂.lift θ₁)).precomp (h₁.lift θ₂) :=
          SemilinearHom.precomp_comp _ _ _
    _ = θ₁.precomp (h₁.lift θ₂) := by rw [h₂.fac]
    _ = θ₂ := h₁.fac θ₂
    _ = θ₂.precomp (𝟙 P₂) := (SemilinearHom.precomp_id θ₂).symm)

/-- The canonical isomorphism between two direct images is compatible with the two counits. -/
@[simp]
theorem precomp_isoOfPushforward_hom {P₁ P₂ : DifferentialGradedModule.{t, a', m'} B}
    {θ₁ : SemilinearHom φ P₁ M} {θ₂ : SemilinearHom φ P₂ M} (h₁ : IsPushforward θ₁)
    (h₂ : IsPushforward θ₂) : θ₂.precomp (h₁.isoOfPushforward h₂).hom = θ₁ :=
  h₂.fac θ₁

end IsPushforward

/-- A direct image of every right differential graded `A`-module at once, along a morphism of
ringed sites `f` and a semilinear homomorphism `φ : B ⟶ f_*A`: the module `f_*M`, its counit,
and the universal property of the counit. -/
structure PushforwardData (φ : DifferentialGradedAlgebra.SemilinearHom u σ B A) where
  /-- The direct image of a right differential graded `A`-module. -/
  obj (M : DifferentialGradedModule.{t, a, m} A) : DifferentialGradedModule.{t, a', m'} B
  /-- The counit, a `φ`-semilinear map from the direct image of a module to the module. -/
  counit (M : DifferentialGradedModule.{t, a, m} A) : SemilinearHom φ (obj M) M
  /-- The counit exhibits the direct image as the direct image. -/
  isPushforward (M : DifferentialGradedModule.{t, a, m} A) : IsPushforward (counit M)

namespace PushforwardData

/-- The direct image of a morphism of right differential graded `A`-modules: the unique morphism
of the direct images compatible with the two counits. -/
noncomputable def map (P : PushforwardData.{t, a, a', m, m'} φ)
    {M M₂ : DifferentialGradedModule.{t, a, m} A} (g : M ⟶ M₂) : P.obj M ⟶ P.obj M₂ :=
  (P.isPushforward M₂).lift ((P.counit M).postcomp g)

/-- The counit of the direct image is natural: precomposing the counit of the target with the
direct image of a morphism is the same as composing the counit with that morphism. -/
@[simp]
theorem map_postcomp_counit (P : PushforwardData.{t, a, a', m, m'} φ)
    {M M₂ : DifferentialGradedModule.{t, a, m} A} (g : M ⟶ M₂) :
    (P.counit M₂).precomp (P.map g) = (P.counit M).postcomp g :=
  (P.isPushforward M₂).fac _

/-- The direct image functor `f_* : Mod^dg(A, d) ⥤ Mod^dg(B, d)`. On a morphism it is the unique
morphism of direct images compatible with the counits, so the functor is determined by the
data. -/
noncomputable def functor (P : PushforwardData.{t, a, a', m, m'} φ) :
    DifferentialGradedModule.{t, a, m} A ⥤ DifferentialGradedModule.{t, a', m'} B where
  obj M := P.obj M
  map {M M₂} g := P.map g
  map_id M := ((P.isPushforward M).uniq _ (𝟙 _) (by
    rw [SemilinearHom.precomp_id, SemilinearHom.postcomp_id])).symm
  map_comp {M M₂ M₃} g g' := ((P.isPushforward M₃).uniq _ _ (by
    rw [SemilinearHom.precomp_comp, P.map_postcomp_counit, ← SemilinearHom.precomp_postcomp,
      P.map_postcomp_counit, ← SemilinearHom.postcomp_comp])).symm

/-- The direct image functor takes a module to its direct image. -/
@[simp]
theorem functor_obj (P : PushforwardData.{t, a, a', m, m'} φ)
    (M : DifferentialGradedModule.{t, a, m} A) : P.functor.obj M = P.obj M :=
  rfl

/-- The direct image functor takes a morphism to its direct image. -/
@[simp]
theorem functor_map (P : PushforwardData.{t, a, a', m, m'} φ)
    {M M₂ : DifferentialGradedModule.{t, a, m} A} (g : M ⟶ M₂) : P.functor.map g = P.map g :=
  rfl

/-- The canonical isomorphism between the direct images of a module given by two direct image
data. -/
noncomputable def compare (P Q : PushforwardData.{t, a, a', m, m'} φ)
    (M : DifferentialGradedModule.{t, a, m} A) : P.obj M ≅ Q.obj M :=
  (P.isPushforward M).isoOfPushforward (Q.isPushforward M)

/-- The comparison isomorphism between two direct images of a module is compatible with the
counits. -/
@[simp]
theorem compare_precomp_counit (P Q : PushforwardData.{t, a, a', m, m'} φ)
    (M : DifferentialGradedModule.{t, a, m} A) :
    (Q.counit M).precomp (P.compare Q M).hom = P.counit M :=
  (Q.isPushforward M).fac _

/-- A differential graded extension of the direct image of right differential graded modules
along a morphism of ringed sites: a direct image of every homotopy, a homotopy between the
direct images of the two morphisms it connects. -/
structure HomotopyExtension (P : PushforwardData.{t, a, a', m, m'} φ) where
  /-- The direct image of a homotopy. -/
  mapHomotopy {M M₂ : DifferentialGradedModule.{t, a, m} A} {ψ χ : M ⟶ M₂}
    (h : Homotopy ψ χ) : Homotopy (P.map ψ) (P.map χ)

/-- A direct image with a differential graded extension carries homotopic morphisms to homotopic
morphisms. -/
theorem HomotopyExtension.preservesHomotopic {P : PushforwardData.{t, a, a', m, m'} φ}
    (E : P.HomotopyExtension) : PreservesHomotopic P.functor :=
  fun _ _ ⟨h⟩ => ⟨E.mapHomotopy h⟩

end PushforwardData

end DifferentialGradedModule

end Pushforward

section PushforwardHom

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {C' : Type u'} [Category.{v'} C'] {J' : GrothendieckTopology C'} {R' : Sheaf J' RingCat.{t}}

namespace DifferentialGradedModule

variable {u : C' ⥤ C} {σ : R'.obj ⟶ u.op ⋙ R.obj}
  {A A' : DifferentialGradedAlgebra.{t, a} R} {B : DifferentialGradedAlgebra.{t, a'} R'}
  {φ : DifferentialGradedAlgebra.SemilinearHom u σ B A}
  {N : DifferentialGradedBimodule.{t, a, z} A A'}

/-- The functor `ℳ ↦ f_*SheafHom^dg_{𝒜'}(𝒩, ℳ)` from right differential graded `𝒜'`-modules on
the source of a morphism of ringed sites to right differential graded `ℬ`-modules on its target:
the internal hom of the differential graded `(𝒜, 𝒜')`-bimodule `𝒩`, followed by the direct image
along the morphism. -/
noncomputable def pushforwardSheafHomFunctor (S : SheafHomFunctorData.{t, a, m, s, z} N)
    (P : PushforwardData.{t, a, a', m, m'} φ) :
    DifferentialGradedModule.{t, a, s} A' ⥤ DifferentialGradedModule.{t, a', m'} B :=
  S.functor ⋙ P.functor

/-- The functor `ℳ ↦ f_*SheafHom^dg_{𝒜'}(𝒩, ℳ)` takes a module to the direct image of the
internal hom. -/
@[simp]
theorem pushforwardSheafHomFunctor_obj (S : SheafHomFunctorData.{t, a, m, s, z} N)
    (P : PushforwardData.{t, a, a', m, m'} φ) (M : DifferentialGradedModule.{t, a, s} A') :
    (pushforwardSheafHomFunctor S P).obj M = P.obj (S.functor.obj M) :=
  rfl

/-- The functor `ℳ ↦ f_*SheafHom^dg_{𝒜'}(𝒩, ℳ)` takes a morphism to the direct image of the
morphism induced on the internal homs. -/
@[simp]
theorem pushforwardSheafHomFunctor_map (S : SheafHomFunctorData.{t, a, m, s, z} N)
    (P : PushforwardData.{t, a, a', m, m'} φ)
    {M M₂ : DifferentialGradedModule.{t, a, s} A'} (g : M ⟶ M₂) :
    (pushforwardSheafHomFunctor S P).map g = P.map (S.functor.map g) :=
  rfl

/-- The functor `ℳ ↦ f_*SheafHom^dg_{𝒜'}(𝒩, ℳ)` carries homotopic morphisms to homotopic
morphisms: the direct image of the homotopy induced on the internal homs. -/
theorem preservesHomotopic_pushforwardSheafHomFunctor
    {S : SheafHomFunctorData.{t, a, m, s, z} N} (ES : S.HomotopyExtension)
    {P : PushforwardData.{t, a, a', m, m'} φ} (EP : P.HomotopyExtension) :
    PreservesHomotopic (pushforwardSheafHomFunctor S P) :=
  PreservesHomotopic.comp ES.preservesHomotopic EP.preservesHomotopic

namespace HomotopyCategory

/-- The functor `K(Mod(𝒜', d)) ⥤ K(Mod(ℬ, d))` induced by `ℳ ↦ f_*SheafHom^dg_{𝒜'}(𝒩, ℳ)` on
the homotopy categories of right differential graded modules, for an internal hom and a direct
image given by their universal properties. Tag 0FTS is this functor stated without the internal
hom datum — which is empty over a sheaf of rings with a nontrivial commutator — and is
registered on `SheafOfModules.DifferentialGradedModule.exists_homotopyPushforwardSheafHom`. -/
noncomputable def pushforwardSheafHom {S : SheafHomFunctorData.{t, a, m, s, z} N}
    (ES : S.HomotopyExtension) {P : PushforwardData.{t, a, a', m, m'} φ}
    (EP : P.HomotopyExtension) :
    HomotopyCategory.{t, a, s} A' ⥤ HomotopyCategory.{t, a', m'} B :=
  descend (pushforwardSheafHomFunctor S P)
    (preservesHomotopic_pushforwardSheafHomFunctor ES EP)

/-- The induced functor factors `ℳ ↦ f_*SheafHom^dg_{𝒜'}(𝒩, ℳ)` through the two quotient
functors. -/
theorem quotient_comp_pushforwardSheafHom {S : SheafHomFunctorData.{t, a, m, s, z} N}
    (ES : S.HomotopyExtension) {P : PushforwardData.{t, a, a', m, m'} φ}
    (EP : P.HomotopyExtension) :
    quotient A' ⋙ pushforwardSheafHom ES EP = pushforwardSheafHomFunctor S P ⋙ quotient B :=
  quotient_comp_descend _ _

/-- On an object represented by a right differential graded `𝒜'`-module `ℳ`, the induced functor
is `f_*SheafHom^dg_{𝒜'}(𝒩, ℳ)`. -/
@[simp]
theorem pushforwardSheafHom_obj {S : SheafHomFunctorData.{t, a, m, s, z} N}
    (ES : S.HomotopyExtension) {P : PushforwardData.{t, a, a', m, m'} φ}
    (EP : P.HomotopyExtension) (M : DifferentialGradedModule.{t, a, s} A') :
    (pushforwardSheafHom ES EP).obj ((quotient A').obj M) =
      (quotient B).obj (P.obj (S.functor.obj M)) :=
  rfl

/-- On a homotopy class represented by a morphism `g` of right differential graded `𝒜'`-modules,
the induced functor is `f_*SheafHom^dg_{𝒜'}(𝒩, g)`. -/
@[simp]
theorem pushforwardSheafHom_map {S : SheafHomFunctorData.{t, a, m, s, z} N}
    (ES : S.HomotopyExtension) {P : PushforwardData.{t, a, a', m, m'} φ}
    (EP : P.HomotopyExtension) {M M₂ : DifferentialGradedModule.{t, a, s} A'} (g : M ⟶ M₂) :
    (pushforwardSheafHom ES EP).map ((quotient A').map g) =
      (quotient B).map (P.map (S.functor.map g)) :=
  rfl

/-- The induced functor is the only functor of homotopy categories factoring
`ℳ ↦ f_*SheafHom^dg_{𝒜'}(𝒩, ℳ)` through the two quotient functors. -/
theorem eq_pushforwardSheafHom {S : SheafHomFunctorData.{t, a, m, s, z} N}
    (ES : S.HomotopyExtension) {P : PushforwardData.{t, a, a', m, m'} φ}
    (EP : P.HomotopyExtension)
    (Φ : HomotopyCategory.{t, a, s} A' ⥤ HomotopyCategory.{t, a', m'} B)
    (hΦ : quotient A' ⋙ Φ = pushforwardSheafHomFunctor S P ⋙ quotient B) :
    Φ = pushforwardSheafHom ES EP :=
  eq_descend _ _ _ hΦ

end HomotopyCategory

end DifferentialGradedModule

end PushforwardHom

end SheafOfModules

end
