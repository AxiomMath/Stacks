module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ExistenceOnARingedSite
public import StacksFrontier.Homology.Injectives.DerivedCategory.DerivedLimit
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Triangulated
import StacksCore.Tactic.StacksAttribute

/-!
# Fourier-Mukai functors

Let `S` be a scheme and let `X` and `Y` be schemes over `S`, with projections
`pr₁ : X ×_S Y ⟶ X` and `pr₂ : X ×_S Y ⟶ Y`. A complex `K ∈ D(𝒪_{X ×_S Y})` determines the
functor

`Φ_K : D(𝒪_X) ⟶ D(𝒪_Y)`,  `M ⟼ R pr_{2,*} (L pr_1^* M ⊗^𝐋_{𝒪_{X ×_S Y}} K)`,

built here as the honest composite of the derived pullback along `pr₁`, the derived tensor
product with `K`, and the derived direct image along `pr₂`. It is an exact functor of
triangulated categories, each of the three factors being one. A functor of this shape is a
*Fourier-Mukai functor* and such a `K` is a *Fourier-Mukai kernel* for it.

## Main definitions

* `AlgebraicGeometry.fourierMukai` — the Fourier-Mukai functor `Φ_K` attached to a kernel
  `K ∈ D(𝒪_{X ×_S Y})`.
* `AlgebraicGeometry.IsFourierMukaiKernel` — `K` is a Fourier-Mukai kernel for a functor `Φ`
  when `Φ` is isomorphic to `Φ_K`.
* `AlgebraicGeometry.IsFourierMukaiFunctor` — a functor `D(𝒪_X) ⟶ D(𝒪_Y)` is a Fourier-Mukai
  functor when it admits a Fourier-Mukai kernel.
* `AlgebraicGeometry.fourierMukaiOn` — the functor induced by `Φ_K` on a pair of full
  subcategories it carries into one another, also called a Fourier-Mukai functor.

## Main results

* `AlgebraicGeometry.commShift_fourierMukai` — `Φ_K` commutes with the shift.
* `AlgebraicGeometry.isTriangulated_fourierMukai` — **`Φ_K` is exact**, i.e. a functor of
  triangulated categories.
* `AlgebraicGeometry.isTriangulated_fourierMukaiOn` — the induced functor on a preserved pair of
  triangulated subcategories is exact as well.
* `AlgebraicGeometry.isFourierMukaiKernel_self` and
  `AlgebraicGeometry.isFourierMukaiFunctor_fourierMukai` — `K` is a Fourier-Mukai kernel for
  `Φ_K`, so `Φ_K` is a Fourier-Mukai functor.

## Implementation notes

*The model of the derived categories.* Everything below is at `HasDerivedCategory.standard`,
activated as a local instance. That is forced by the exactness statement: the exactness of the
derived pullback along a morphism of ringed spaces, Stacks 06YJ, is proved at that model, and a
statement proved for one model says nothing about another. The derived direct image and the
derived tensor product are both available at an arbitrary model, so they are read at the
standard one here as well, and no declaration mixes the two.

*Why the derived functors are those of the underlying morphisms of ringed spaces.* The derived
pullback and derived direct image used here are Stacks 079W for the morphisms of ringed spaces
underlying `pr₁` and `pr₂`, and the derived tensor product is Stacks 06YU at the ringed site of
opens of `X ×_S Y`; the scheme spelling `Z.Modules` of the categories of modules is the
ringed-space spelling `SheafOfModules (structureSheafRing Z.toSheafedSpace)` for a scheme `Z`, so
the three functors compose with no comparison in between and the composite is displayed in the
scheme spelling.

*The commutation with the shift carried by each factor.* `Functor.IsTriangulated` takes a
`Functor.CommShift` structure as an instance argument, so the exactness of the composite is a
statement about a particular choice of commutation for each factor. For the derived pullback it
is the instance of Stacks 06YJ; for the derived direct image it is the one a right derived
functor carries; and for the tensor product it is the field `commShift_left` of the derived
tensor product of Stacks 06YU. The three are seated below and the composite's commutation is
assembled from them, so `isTriangulated_fourierMukai` is read against exactly that structure.

*No finiteness hypothesis.* `S`, `X`, `Y` and `K` are arbitrary.

*The restricted versions of the definition.* The source also calls a Fourier-Mukai functor the
functor induced by `Φ_K` on `D_QCoh`, on `D_perf`, and — over a Noetherian base — on `D^b_Coh`,
whenever `Φ_K` maps the subcategory of `D(𝒪_X)` into the one of `D(𝒪_Y)`. The three are the one
construction `fourierMukaiOn` at three choices of the pair of subcategories, so it is stated
for an arbitrary preserved pair; what is *not* here is the geometry, namely the hypotheses on
`X`, `Y`, `S` and `K` under which each of the three subcategories is in fact preserved.

## References

* [Stacks Project, Tag 0FYQ](https://stacks.math.columbia.edu/tag/0FYQ)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
* [Shigeru Mukai, *Duality between `D(X)` and `D(X̂)` with its application to Picard
  sheaves*][Mukai1981]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedTensor.RingedSite

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

/-! ### The commutation with the shift of the three factors -/

section Factors

variable {X' Y' : RingedSpace.{u, u}} (h : X' ⟶ Y')

/-- The derived direct image along a morphism of ringed spaces commutes with the shift: it is a
right derived functor along the quasi-isomorphisms, and those are stable under the shift. -/
local instance commShift_derivedPushforward : (derivedPushforward h).CommShift ℤ :=
  Functor.IsRightDerivedFunctor.commShift (derivedPushforward h) (derivedPushforwardUnit h)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X')) (ComplexShape.up ℤ)) ℤ

/-- **The derived direct image along a morphism of ringed spaces is exact.** Sheaves of
`𝒪_{X'}`-modules form a Grothendieck abelian category, and a right derived functor of an
additive functor out of such a category is triangulated. -/
local instance isTriangulated_derivedPushforward : (derivedPushforward h).IsTriangulated := by
  have _ := SheafOfModules.isGrothendieckAbelianU (structureSheafRing X')
  exact Stacks.Injectives.rightDerivedFunctor_isTriangulated (modulePushforward h)
    (derivedPushforward h) (derivedPushforwardUnit h)

variable (Z : RingedSpace.{u, u}) (K : DerivedModules Z.sheaf)

/-- Tensoring with a fixed complex `K` commutes with the shift; this is the commutation the
derived tensor product of Stacks 06YU carries in its first variable. -/
local instance commShift_tensorRight :
    ((derivedTensorProductFunctor Z.sheaf).flip.obj K).CommShift ℤ :=
  (canonicalDerivedTensorProduct Z.sheaf).commShift_left K

/-- **Tensoring with a fixed complex is exact**, by the exactness of the derived tensor product
of Stacks 06YU in its first variable. -/
local instance isTriangulated_tensorRight :
    ((derivedTensorProductFunctor Z.sheaf).flip.obj K).IsTriangulated :=
  (canonicalDerivedTensorProduct Z.sheaf).exact_left K

end Factors

/-! ### The Fourier-Mukai functor -/

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- `L pr_1^* : D(𝒪_X) ⟶ D(𝒪_{X ×_S Y})`, the derived pullback along the first projection. -/
abbrev fourierMukaiPullback :
    DerivedCategory X.Modules ⥤ DerivedCategory (Limits.pullback f g).Modules :=
  derivedPullback (Limits.pullback.fst f g).toLRSHom.toShHom

/-- `R pr_{2,*} : D(𝒪_{X ×_S Y}) ⟶ D(𝒪_Y)`, the derived direct image along the second
projection. -/
abbrev fourierMukaiPushforward :
    DerivedCategory (Limits.pullback f g).Modules ⥤ DerivedCategory Y.Modules :=
  derivedPushforward (Limits.pullback.snd f g).toLRSHom.toShHom

/-- `- ⊗^𝐋_{𝒪_{X ×_S Y}} K`, the derived tensor product with a fixed complex `K` on
`X ×_S Y`. -/
abbrev fourierMukaiTensor (K : DerivedCategory (Limits.pullback f g).Modules) :
    DerivedCategory (Limits.pullback f g).Modules ⥤
      DerivedCategory (Limits.pullback f g).Modules :=
  (derivedTensorProductFunctor (Limits.pullback f g).toRingedSpace.sheaf).flip.obj K

/-! ### The three factors, read in the scheme spelling

Each of the next six instances is one factor's commutation with the shift or its exactness,
transported from the ringed-space spelling of the categories of modules to the scheme spelling.
Transporting them here is what confines the two spellings of `D(𝒪_Z)` to a single boundary. -/

/-- `L pr_1^*` commutes with the shift, by Stacks 06YJ. -/
local instance commShift_fourierMukaiPullback : (fourierMukaiPullback f g).CommShift ℤ :=
  Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_commShift
    (f := (Limits.pullback.fst f g).toLRSHom.toShHom)

/-- `L pr_1^*` is exact, by Stacks 06YJ. -/
local instance isTriangulated_fourierMukaiPullback : (fourierMukaiPullback f g).IsTriangulated :=
  Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_isTriangulated
    (f := (Limits.pullback.fst f g).toLRSHom.toShHom)

/-- `R pr_{2,*}` commutes with the shift. -/
local instance commShift_fourierMukaiPushforward : (fourierMukaiPushforward f g).CommShift ℤ :=
  commShift_derivedPushforward (Limits.pullback.snd f g).toLRSHom.toShHom

/-- `R pr_{2,*}` is exact. -/
local instance isTriangulated_fourierMukaiPushforward :
    (fourierMukaiPushforward f g).IsTriangulated :=
  isTriangulated_derivedPushforward (Limits.pullback.snd f g).toLRSHom.toShHom

/-- `- ⊗^𝐋 K` commutes with the shift, by Stacks 06YU. -/
local instance commShift_fourierMukaiTensor
    (K : DerivedCategory (Limits.pullback f g).Modules) :
    (fourierMukaiTensor f g K).CommShift ℤ :=
  commShift_tensorRight (Limits.pullback f g).toRingedSpace K

/-- `- ⊗^𝐋 K` is exact, by Stacks 06YU. -/
local instance isTriangulated_fourierMukaiTensor
    (K : DerivedCategory (Limits.pullback f g).Modules) :
    (fourierMukaiTensor f g K).IsTriangulated :=
  isTriangulated_tensorRight (Limits.pullback f g).toRingedSpace K

/-- **Stacks Project, Tag 0FYQ (the functor).** The Fourier-Mukai functor
`Φ_K : D(𝒪_X) ⟶ D(𝒪_Y)` attached to a complex `K` on `X ×_S Y`, namely
`M ⟼ R pr_{2,*}(L pr_1^* M ⊗^𝐋_{𝒪_{X ×_S Y}} K)`. -/
@[stacks 0FYQ "the Fourier-Mukai functor"]
def fourierMukai (K : DerivedCategory (Limits.pullback f g).Modules) :
    DerivedCategory X.Modules ⥤ DerivedCategory Y.Modules :=
  fourierMukaiPullback f g ⋙ fourierMukaiTensor f g K ⋙ fourierMukaiPushforward f g

/-- The value of the Fourier-Mukai functor on an object: pull back along the first projection,
tensor with the kernel, push forward along the second projection. -/
theorem fourierMukai_obj (K : DerivedCategory (Limits.pullback f g).Modules)
    (M : DerivedCategory X.Modules) :
    (fourierMukai f g K).obj M =
      (fourierMukaiPushforward f g).obj
        ((fourierMukaiTensor f g K).obj ((fourierMukaiPullback f g).obj M)) :=
  rfl

/-- Tensoring with `K` and then pushing forward along the second projection commutes with the
shift. -/
instance commShift_fourierMukaiTensor_comp
    (K : DerivedCategory (Limits.pullback f g).Modules) :
    (fourierMukaiTensor f g K ⋙ fourierMukaiPushforward f g).CommShift ℤ :=
  Functor.CommShift.comp (F := fourierMukaiTensor f g K) (G := fourierMukaiPushforward f g)

/-- Tensoring with `K` and then pushing forward along the second projection is exact. -/
instance isTriangulated_fourierMukaiTensor_comp
    (K : DerivedCategory (Limits.pullback f g).Modules) :
    (fourierMukaiTensor f g K ⋙ fourierMukaiPushforward f g).IsTriangulated :=
  Functor.IsTriangulated.instComp (F := fourierMukaiTensor f g K)
    (G := fourierMukaiPushforward f g)

/-- The Fourier-Mukai functor commutes with the shift, each of its three factors doing so. -/
instance commShift_fourierMukai (K : DerivedCategory (Limits.pullback f g).Modules) :
    (fourierMukai f g K).CommShift ℤ :=
  Functor.CommShift.comp (F := fourierMukaiPullback f g)
    (G := fourierMukaiTensor f g K ⋙ fourierMukaiPushforward f g)

/-- **Stacks Project, Tag 0FYQ (exactness).** The Fourier-Mukai functor is an exact functor of
triangulated categories: the derived pullback along `pr₁` is exact by Stacks 06YJ, tensoring
with `K` is exact by Stacks 06YU, and the derived direct image along `pr₂` is exact because it
is a right derived functor out of a Grothendieck abelian category. -/
@[stacks 0FYQ "exactness of the Fourier-Mukai functor"]
instance isTriangulated_fourierMukai (K : DerivedCategory (Limits.pullback f g).Modules) :
    (fourierMukai f g K).IsTriangulated :=
  Functor.IsTriangulated.instComp (F := fourierMukaiPullback f g)
    (G := fourierMukaiTensor f g K ⋙ fourierMukaiPushforward f g)

/-! ### The induced functor on a preserved pair of full subcategories -/

/-- **Stacks Project, Tag 0FYQ (the induced functor).** Suppose `Φ_K` carries every object of
`D(𝒪_X)` with property `P` to an object of `D(𝒪_Y)` with property `Q`. Then it induces a functor
between the corresponding full subcategories, which is again called a Fourier-Mukai functor;
taking `P` and `Q` to be quasi-coherence of the cohomology sheaves, perfectness, or bounded
coherence over a Noetherian base gives the three restricted versions of the definition. -/
@[stacks 0FYQ "the induced functor on a preserved pair of full subcategories"]
def fourierMukaiOn (K : DerivedCategory (Limits.pullback f g).Modules)
    (P : ObjectProperty (DerivedCategory X.Modules))
    (Q : ObjectProperty (DerivedCategory Y.Modules))
    (h : ∀ M : P.FullSubcategory, Q ((fourierMukai f g K).obj M.obj)) :
    P.FullSubcategory ⥤ Q.FullSubcategory :=
  Q.lift (P.ι ⋙ fourierMukai f g K) h

/-- The induced functor on full subcategories is `Φ_K` on underlying objects. -/
theorem fourierMukaiOn_obj (K : DerivedCategory (Limits.pullback f g).Modules)
    (P : ObjectProperty (DerivedCategory X.Modules))
    (Q : ObjectProperty (DerivedCategory Y.Modules))
    (h : ∀ M : P.FullSubcategory, Q ((fourierMukai f g K).obj M.obj))
    (M : P.FullSubcategory) :
    ((fourierMukaiOn f g K P Q h).obj M).obj = (fourierMukai f g K).obj M.obj :=
  rfl

section Restricted

variable (K : DerivedCategory (Limits.pullback f g).Modules)
  (P : ObjectProperty (DerivedCategory X.Modules))
  (Q : ObjectProperty (DerivedCategory Y.Modules)) [P.IsTriangulated] [Q.IsTriangulated]
  (h : ∀ M : P.FullSubcategory, Q ((fourierMukai f g K).obj M.obj))

/-- The induced functor on a preserved pair of triangulated subcategories commutes with the
shift. -/
instance commShift_fourierMukaiOn : (fourierMukaiOn f g K P Q h).CommShift ℤ :=
  inferInstanceAs ((Q.lift (P.ι ⋙ fourierMukai f g K) h).CommShift ℤ)

/-- **Stacks Project, Tag 0FYQ (exactness of the induced functor).** On a preserved pair of
triangulated subcategories the induced functor is again exact, `Φ_K` being exact. -/
@[stacks 0FYQ "exactness of the induced functor"]
instance isTriangulated_fourierMukaiOn : (fourierMukaiOn f g K P Q h).IsTriangulated :=
  inferInstanceAs ((Q.lift (P.ι ⋙ fourierMukai f g K) h).IsTriangulated)

end Restricted

/-! ### Fourier-Mukai kernels -/

/-- **Stacks Project, Tag 0FYQ (the kernel).** A complex `K` on `X ×_S Y` is a Fourier-Mukai
kernel for a functor `Φ : D(𝒪_X) ⟶ D(𝒪_Y)` when `Φ` is isomorphic to the Fourier-Mukai functor
`Φ_K` attached to `K`. -/
@[stacks 0FYQ "the Fourier-Mukai kernel"]
def IsFourierMukaiKernel (Φ : DerivedCategory X.Modules ⥤ DerivedCategory Y.Modules)
    (K : DerivedCategory (Limits.pullback f g).Modules) : Prop :=
  Nonempty (Φ ≅ fourierMukai f g K)

/-- **Stacks Project, Tag 0FYQ (the property of being a Fourier-Mukai functor).** A functor
`D(𝒪_X) ⟶ D(𝒪_Y)` is a Fourier-Mukai functor when some complex on `X ×_S Y` is a Fourier-Mukai
kernel for it. -/
@[stacks 0FYQ "being a Fourier-Mukai functor"]
def IsFourierMukaiFunctor (Φ : DerivedCategory X.Modules ⥤ DerivedCategory Y.Modules) : Prop :=
  ∃ K : DerivedCategory (Limits.pullback f g).Modules, IsFourierMukaiKernel f g Φ K

/-- A complex on `X ×_S Y` is a Fourier-Mukai kernel for the Fourier-Mukai functor it
determines. -/
theorem isFourierMukaiKernel_self (K : DerivedCategory (Limits.pullback f g).Modules) :
    IsFourierMukaiKernel f g (fourierMukai f g K) K :=
  ⟨Iso.refl _⟩

/-- The Fourier-Mukai functor attached to a complex on `X ×_S Y` is a Fourier-Mukai functor. -/
theorem isFourierMukaiFunctor_fourierMukai
    (K : DerivedCategory (Limits.pullback f g).Modules) :
    IsFourierMukaiFunctor f g (fourierMukai f g K) :=
  ⟨K, isFourierMukaiKernel_self f g K⟩

/-- A functor isomorphic to one with Fourier-Mukai kernel `K` has `K` as a kernel too. -/
theorem IsFourierMukaiKernel.of_iso
    {Φ Ψ : DerivedCategory X.Modules ⥤ DerivedCategory Y.Modules}
    {K : DerivedCategory (Limits.pullback f g).Modules}
    (hK : IsFourierMukaiKernel f g Φ K) (e : Ψ ≅ Φ) : IsFourierMukaiKernel f g Ψ K :=
  hK.elim fun i => ⟨e ≪≫ i⟩

/-- A functor isomorphic to a Fourier-Mukai functor is a Fourier-Mukai functor. -/
theorem IsFourierMukaiFunctor.of_iso
    {Φ Ψ : DerivedCategory X.Modules ⥤ DerivedCategory Y.Modules}
    (hΦ : IsFourierMukaiFunctor f g Φ) (e : Ψ ≅ Φ) : IsFourierMukaiFunctor f g Ψ :=
  hΦ.imp fun _ hK => hK.of_iso f g e

end AlgebraicGeometry

end
