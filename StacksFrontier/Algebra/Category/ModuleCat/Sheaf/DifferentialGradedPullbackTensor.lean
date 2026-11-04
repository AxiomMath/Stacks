module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedTensorGradedShift

/-!
# The functor `ℳ ↦ f^*ℳ ⊗_𝒜 𝒩` on homotopy categories of differential graded modules

Let `f` be a morphism of ringed sites, presented as a functor `u : C' ⥤ C` in the direction
opposite to `f` together with the structure map `σ : R' ⟶ f_*R` of its sheaves of rings. Let `𝒜`
and `𝒜'` be sheaves of differential graded `R`-algebras on the source, let `ℬ` be a sheaf of
differential graded `R'`-algebras on the target, let `φ : f⁻¹ℬ ⟶ 𝒜` be a homomorphism of sheaves
of differential graded algebras and let `𝒩` be a differential graded `(𝒜, 𝒜')`-bimodule, so that
both algebras of the bimodule live on the source. Then

`ℳ ↦ f^*ℳ ⊗_𝒜 𝒩`

is a functor `Mod^dg(ℬ, d) ⥤ Mod^dg(𝒜', d)`, and it carries homotopic morphisms to homotopic
morphisms, so it induces a functor `K(Mod(ℬ, d)) ⥤ K(Mod(𝒜', d))` of homotopy categories.

The mathematical content is that the tensor product of a homotopy with the identity of `𝒩` is
again a homotopy. For a homotopy `h` between `ψ` and `χ`, the balanced bilinear family
`x ⊗ y ↦ h x ⊗ y` of degree `-1` descends, by the universal property of the tensor product in
degree `-1`, to a degree `-1` map `H` of the tensor products, and the commutator of `H` with the
two differentials is

`d(h x ⊗ y) + h(d x) ⊗ y + (-1)^i h x ⊗ d y + (-1)^{i-1} h x ⊗ d y = (ψ x - χ x) ⊗ y`

on a homogeneous local section `x` of degree `i`: the two mixed terms carry opposite signs and
cancel, and what is left is the homotopy equation for `h`. The same cancellation makes the
commutator `d ∘ H + H ∘ d` linear over the algebra, which is what exhibits it as a degree-zero
local homomorphism and so lets the universal property be applied to it.

## Main definitions

* `SheafOfModules.LocalHom.ofHomSub` reads the difference of two morphisms of right
  differential graded modules as a degree-zero local homomorphism.
* `SheafOfModules.LocalHom.diffCommutator` is the commutator `d ∘ H + H ∘ d` of a degree `-1`
  local homomorphism with the differentials, a degree-zero local homomorphism.
* `SheafOfModules.TensorFunctorData.homotopyBilinear`,
  `SheafOfModules.TensorFunctorData.homotopyLocalHom` and
  `SheafOfModules.TensorFunctorData.homotopyHom` are the balanced bilinear family
  `x ⊗ y ↦ h x ⊗ y`, the degree `-1` local homomorphism it descends to, and the resulting
  degreewise map of sheaves of modules.
* `SheafOfModules.TensorFunctorData.mapHomotopy` is the tensor product `h ⊗ 1` of a homotopy
  with the identity of the bimodule, a homotopy between the two tensored morphisms.
* `SheafOfModules.DifferentialGradedModule.PullbackData.HomotopyExtension` is a pullback of
  every homotopy along the morphism of ringed sites.
* `SheafOfModules.DifferentialGradedModule.pullbackTensorFunctor` is the functor
  `ℳ ↦ f^*ℳ ⊗_𝒜 𝒩`, and
  `SheafOfModules.DifferentialGradedModule.HomotopyCategory.pullbackTensor` is the functor it
  induces on the homotopy categories.

## Main results

* `SheafOfModules.TensorFunctorData.ofHomSub_eq_diffCommutator`: the difference of the two
  tensored morphisms is the commutator of the tensored homotopy with the differentials. This is
  the homotopy equation, and it is proved by the sign cancellation above.
* `SheafOfModules.TensorFunctorData.preservesHomotopic`: tensoring with a differential graded
  bimodule carries homotopic morphisms to homotopic morphisms.
* `SheafOfModules.DifferentialGradedModule.preservesHomotopic_pullbackTensorFunctor`: so does
  `ℳ ↦ f^*ℳ ⊗_𝒜 𝒩`.
* `SheafOfModules.DifferentialGradedModule.HomotopyCategory.pullbackTensor_obj` and
  `...pullbackTensor_map` compute the induced functor on an object and on a homotopy class, and
  `...quotient_comp_pullbackTensor` and `...eq_pullbackTensor` say that it is the unique functor
  factoring `ℳ ↦ f^*ℳ ⊗_𝒜 𝒩` through the two quotient functors.
* `SheafOfModules.DifferentialGradedModule.isTensorProduct_pullbackTensorFunctor_obj` and
  `...pullbackTensorFunctor_map_tmul` pin the functor down: its value at `ℳ` is a tensor product
  of `f^*ℳ` with `𝒩`, and on local sections it sends a morphism `ψ` to `x ⊗ y ↦ (f^*ψ) x ⊗ y`.

## Implementation notes

The pullback and the tensor product are the ones of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedPullback.lean` and
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedTensor.lean`: both objects are
pinned by universal properties rather than constructed, so `PullbackData` and
`TensorFunctorData` are hypotheses here, and the descent to the homotopy categories is the one
of `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedDerivedPullback.lean`.

Homotopy preservation is proved for the tensor product and assumed for the pullback. The
asymmetry is forced by the two universal properties. A tensor product is characterised by its
degree-`n` local homomorphisms for *every* `n`, so the degree `-1` map `h ⊗ 1` is obtained from
the universal property and the homotopy equation for it is proved. A pullback is characterised
only through morphisms of differential graded modules, that is in degree zero, so nothing about
degree `-1` maps out of `f^*ℳ` follows from `PullbackData`; the pullback `f⁻¹h ⊗ 1` of a
homotopy is therefore the extra datum `PullbackData.HomotopyExtension`, which the construction
`f^*ℳ = f⁻¹ℳ ⊗_{f⁻¹ℬ} 𝒜` supplies:
`Stacks.DifferentialGradedPullbackConstruction.pullbackHomotopyExtension` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedPullbackHomotopyExtension.lean`.
It is strictly weaker than the conclusion here: it says nothing about the tensor product with
`𝒩`, nor about the homotopy categories.

The map `h ⊗ 1` itself is not built here. A homotopy is a right-linear family of degree `-1`
between the underlying graded modules, which
`SheafOfModules.DifferentialGradedModule.Homotopy.toGradedShift` says, and the transport of a
right-linear family of an arbitrary degree through `- ⊗_𝒜 𝒩` is
`SheafOfModules.TensorFunctorData.gradedShiftMap` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedTensorGradedShift.lean`. The
`homotopy*` chain below is that construction at `k = -1`, so the only thing proved here about
`h ⊗ 1` is the homotopy equation `ofHomSub_eq_diffCommutator`.

Exactness of the induced functor is not formulated below, and no statement here mentions
triangulated categories.

Degrees are carried as in the two input files: a local homomorphism takes its target degree as
an independent argument together with a proof, which is what lets `d ∘ H + H ∘ d` be written
with no transport at all, while the tensor product's multiplication map has target degree
`i + j` on the nose, so the computations on `x ⊗ y` move between spellings of a degree by the
transports `SheafOfModules.castHom` and `SheafOfModules.castHom₂`.

The universes are those of the two input files: the three sites and their morphisms, the two
algebra universes and the three module universes are independent, while the two sheaves of rings
share the universe `t` because the structure map of the morphism of ringed sites relates them,
and the two algebras on the source share the universe `a` because the bimodule `𝒩` is a
bimodule between them.

## References

* [Stacks Project, Tag 0FTE](https://stacks.math.columbia.edu/tag/0FTE)
* [Stacks Project, Tag 0FRU](https://stacks.math.columbia.edu/tag/0FRU)
* [Stacks Project, Tag 0FRS](https://stacks.math.columbia.edu/tag/0FRS)
* [Stacks Project, Tag 0FS1](https://stacks.math.columbia.edu/tag/0FS1)
-/

@[expose] public section

open CategoryTheory

universe t a a' m m' s z v u v' u'

namespace SheafOfModules

section Degrees

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-- The restriction maps of a sheaf of modules are compatible with addition of local
sections. -/
theorem map_add_sections (X : SheafOfModules.{s} R) {U V : Cᵒᵖ} (g : U ⟶ V)
    (x y : X.val.obj U) : X.val.map g (x + y) = X.val.map g x + X.val.map g y :=
  (X.val.map g).hom.toAddMonoidHom.map_add x y

/-- Transport of local sections along an equality of degrees is the action of the corresponding
`eqToHom`. -/
theorem castHom_eq_homSections_eqToHom (X : ℤ → SheafOfModules.{s} R) {i j : ℤ} (h : i = j)
    (U : Cᵒᵖ) (x : (X i).val.obj U) :
    castHom X h U x = homSections (eqToHom (congrArg X h)) U x := by
  subst h; rfl

/-- The differential of a cochain complex of sheaves of modules commutes with transport of
local sections along equalities of degrees. -/
theorem d_castHom_app (X : CochainComplex (SheafOfModules.{s} R) ℤ) {i i' j j' : ℤ}
    (hi : i = i') (hj : j = j') (U : Cᵒᵖ) (x : (X.X i).val.obj U) :
    (X.d i' j').val.app U (castHom X.X hi U x) =
      castHom X.X hj U ((X.d i j).val.app U x) := by
  subst hi; subst hj; rfl

variable {A : DifferentialGradedAlgebra.{t, a} R}

/-- The sign of a degree lowered by one is the opposite of the sign of the degree. -/
theorem negOnePow_sub_one (i : ℤ) :
    ((i - 1).negOnePow : ℤ) = -((i.negOnePow : ℤ)) := by
  have h : (i.negOnePow : ℤˣ) = -(i - 1).negOnePow := by
    simpa using Int.negOnePow_succ (i - 1)
  rw [h]
  simp

/-- The commutator `d ∘ H + H ∘ d` of a degree `-1` local homomorphism with the differentials,
as a degree-zero local homomorphism: it is linear over the algebra because the two signs in the
Leibniz rules for `d ∘ H` and for `H ∘ d` are opposite. -/
def LocalHom.diffCommutator {K : DifferentialGradedModule.{t, a, m} A}
    {L : DifferentialGradedModule.{t, a, s} A} {U : C} (H : LocalHom K L (-1) U) :
    LocalHom K L 0 U where
  app i j hij V :=
    (homSections (L.complex.d (i - 1) j) (Opposite.op V.left)).comp
        (H.app i (i - 1) (by omega) V) +
      (H.app (i + 1) j (by omega) V).comp
        (homSections (K.complex.d i (i + 1)) (Opposite.op V.left))
  map_smul i j hij V r x := by
    simp only [AddMonoidHom.add_apply, AddMonoidHom.coe_comp, Function.comp_apply,
      homSections_smul, H.map_smul, smul_add]
  naturality i j hij {V W} g x := by
    simp only [AddMonoidHom.add_apply, AddMonoidHom.coe_comp, Function.comp_apply]
    rw [map_add_sections]
    simp only [homSections_naturality, H.naturality]
    rfl
  isLinear i j hij p V x b := by
    obtain rfl : i = j := (add_zero i).symm.trans hij
    simp only [AddMonoidHom.add_apply, AddMonoidHom.coe_comp, Function.comp_apply,
      homSections_apply, map_add, AddMonoidHom.add_apply]
    rw [H.toLocalGradedHom.app_castHom_target (show (i - 1) + p = (i + p) - 1 by omega)
        (by omega) (by omega) V ((K.mul i p).app (Opposite.op V.left) x b),
      H.isLinear i (i - 1) (by omega) p V x b,
      d_castHom_app L.complex (show (i - 1) + p = (i + p) - 1 by omega)
        (show (i - 1) + p + 1 = i + p by omega) (Opposite.op V.left),
      L.leibniz_castHom (i - 1) p (Opposite.op V.left) (H.app i (i - 1) (by omega) V x) b,
      K.leibniz_castHom i p (Opposite.op V.left) x b]
    simp only [map_add, map_zsmul, castHom_castHom]
    rw [H.toLocalGradedHom.app_castHom_source (show (i + 1) + p = i + p + 1 by omega)
        (by omega) (by omega) V _,
      H.toLocalGradedHom.app_castHom_source (show i + (p + 1) = i + p + 1 by omega)
        (by omega) (by omega) V _,
      H.isLinear (i + 1) i (by omega) p V ((K.complex.d i (i + 1)).val.app _ x) b,
      H.toLocalGradedHom.app_castHom_target
        (show (i - 1) + (p + 1) = i + p by omega) (by omega) (by omega) V _,
      H.isLinear i (i - 1) (by omega) (p + 1) V x _,
      d_app_castHom L.complex (show i - 1 + 1 = i by omega) (Opposite.op V.left)
        (H.app i (i - 1) (by omega) V x),
      mul_app_castHom L (show i - 1 + 1 = i by omega) p (Opposite.op V.left)]
    simp only [negOnePow_sub_one, neg_smul]
    abel

/-- Subtraction of morphisms of sheaves of modules is sectionwise. -/
theorem homSections_sub {X Y : SheafOfModules.{s} R} (ψ χ : X ⟶ Y) (U : Cᵒᵖ)
    (x : X.val.obj U) : homSections (ψ - χ) U x = homSections ψ U x - homSections χ U x := rfl

/-- Two morphisms of sheaves of modules which agree on local sections are equal. -/
theorem hom_ext_sections {X Y : SheafOfModules.{s} R} {ψ χ : X ⟶ Y}
    (hψχ : ∀ (U : Cᵒᵖ) (x : X.val.obj U), homSections ψ U x = homSections χ U x) : ψ = χ :=
  SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
    ModuleCat.hom_ext (LinearMap.ext (hψχ U)))

/-- The difference of two morphisms of right differential graded modules, read as a degree-zero
local homomorphism over an object of the site. -/
def LocalHom.ofHomSub {K L : DifferentialGradedModule.{t, a, m} A} (ψ χ : K ⟶ L) (U : C) :
    LocalHom K L 0 U where
  app i j hij V := (castHom L.complex.X ((add_zero i).symm.trans hij) (Opposite.op V.left)).comp
    (homSections (ψ.toHomologicalComplex.f i) (Opposite.op V.left) -
      homSections (χ.toHomologicalComplex.f i) (Opposite.op V.left))
  map_smul i j hij V r x := by
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.sub_apply,
      homSections_smul, ← smul_sub, castHom_smul]
  naturality i j hij {V W} g x := by
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.sub_apply]
    rw [castHom_naturality, map_sub_sections, homSections_naturality, homSections_naturality]
    rfl
  isLinear i j hij p V x b := by
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.sub_apply,
      homSections_apply, map_sub, AddMonoidHom.sub_apply]
    rw [ψ.map_mul i p (Opposite.op V.left) x b, χ.map_mul i p (Opposite.op V.left) x b,
      mul_app_castHom, mul_app_castHom]

/-- The difference of two morphisms of right differential graded modules, read as a local
homomorphism, acts on local sections through the difference of their values. -/
@[simp]
theorem LocalHom.ofHomSub_app {K L : DifferentialGradedModule.{t, a, m} A} (ψ χ : K ⟶ L)
    (U : C) (i j : ℤ) (hij : i + 0 = j) (V : Over U)
    (x : (K.complex.X i).val.obj (Opposite.op V.left)) :
    (LocalHom.ofHomSub ψ χ U).app i j hij V x =
      castHom L.complex.X ((add_zero i).symm.trans hij) (Opposite.op V.left)
        (homSections (ψ.toHomologicalComplex.f i) (Opposite.op V.left) x -
          homSections (χ.toHomologicalComplex.f i) (Opposite.op V.left) x) :=
  rfl

/-- The commutator of a degree `-1` local homomorphism with the differentials acts on a local
section `x` by `d (H x) + H (d x)`. -/
@[simp]
theorem LocalHom.diffCommutator_app {K : DifferentialGradedModule.{t, a, m} A}
    {L : DifferentialGradedModule.{t, a, s} A} {U : C} (H : LocalHom K L (-1) U) (i j : ℤ)
    (hij : i + 0 = j) (V : Over U) (x : (K.complex.X i).val.obj (Opposite.op V.left)) :
    H.diffCommutator.app i j hij V x =
      (L.complex.d (i - 1) j).val.app (Opposite.op V.left) (H.app i (i - 1) (by omega) V x) +
        H.app (i + 1) j (by omega) V
          ((K.complex.d i (i + 1)).val.app (Opposite.op V.left) x) :=
  rfl

end Degrees

section Tensor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A A' : DifferentialGradedAlgebra.{t, a} R} {N : DifferentialGradedBimodule.{t, a, z} A A'}

namespace IsTensorProduct

variable {M : DifferentialGradedModule.{t, a, m} A} {T : DifferentialGradedModule.{t, a, s} A'}

/-- The multiplication map of a tensor product is compatible with subtraction in the first
variable. -/
theorem tmul_sub_left (hT : IsTensorProduct M N T) (i j : ℤ) (U : Cᵒᵖ)
    (x x' : (M.complex.X i).val.obj U) (y : (N.complex.X j).val.obj U) :
    hT.tmul i j U (x - x') y = hT.tmul i j U x y - hT.tmul i j U x' y := by
  rw [map_sub]; rfl

end IsTensorProduct

namespace DifferentialGradedModule

variable {M M₂ : DifferentialGradedModule.{t, a, m} A} {f g : M ⟶ M₂}

/-- **A homotopy between two morphisms of right differential graded modules, read as a
right-linear family of degree `-1`** between the underlying graded modules: the component in
degree `n` is the component of the homotopy, and the two spellings `n - 1` and `n + (-1)` of the
degree it lands in are definitionally equal. -/
def Homotopy.toGradedShift (h : Homotopy f g) :
    (forgetToGradedModule A).obj M ⟶ ((forgetToGradedModule A).obj M₂).shift (-1) where
  app n := h.app n
  map_smul n i U x y :=
    eq_of_heq ((h.map_mul n i U x y).trans
      (heq_castHom M₂.complex.X (show n + -1 + i = n + i + -1 by omega) U _).symm)

end DifferentialGradedModule

namespace TensorFunctorData

variable (D : TensorFunctorData.{t, a, m, z, s} A A' N)
  {M M₂ : DifferentialGradedModule.{t, a, m} A} {f g : M ⟶ M₂}

open DifferentialGradedModule

/-- The balanced bilinear family `x ⊗ y ↦ h x ⊗ y` of degree `-1` attached to a homotopy `h`
between two morphisms of right differential graded `𝒜`-modules: the family of
`SheafOfModules.TensorFunctorData.shiftBilinear` at the degree `-1` right-linear family of the
homotopy. -/
def homotopyBilinear (h : Homotopy f g) (U : C) :
    LocalBalancedBilinear M N (D.functor.obj M₂) (-1) U :=
  D.shiftBilinear (-1) h.toGradedShift U

/-- The balanced bilinear family attached to a homotopy sends `(x, y)` to `h x ⊗ y`. -/
@[simp]
theorem homotopyBilinear_app (h : Homotopy f g) (U : C) (i j k : ℤ) (hijk : i + j + (-1) = k)
    (V : Over U) (x : (M.complex.X i).val.obj (Opposite.op V.left))
    (y : (N.complex.X j).val.obj (Opposite.op V.left)) :
    (D.homotopyBilinear h U).app i j k hijk V x y =
      castHom (D.functor.obj M₂).complex.X (show i - 1 + j = k by omega) (Opposite.op V.left)
        ((D.isTensorProduct M₂).tmul (i - 1) j (Opposite.op V.left)
          (homSections (h.app i) (Opposite.op V.left) x) y) :=
  D.shiftBilinear_app (-1) h.toGradedShift U i j k hijk V x y

/-- The degree `-1` local homomorphism `ℳ ⊗_𝒜 𝒩 → ℳ₂ ⊗_𝒜 𝒩` determined by `x ⊗ y ↦ h x ⊗ y`
for a homotopy `h`. -/
noncomputable def homotopyLocalHom (h : Homotopy f g) (U : C) :
    LocalHom (D.functor.obj M) (D.functor.obj M₂) (-1) U :=
  D.shiftLocalHom (-1) h.toGradedShift U

/-- Composing the tensor product of a homotopy with the multiplication map returns the balanced
bilinear family it was built from. -/
theorem universal_homotopyLocalHom (h : Homotopy f g) (U : C) :
    (D.isTensorProduct M).universal (D.functor.obj M₂) (-1) U (D.homotopyLocalHom h U) =
      D.homotopyBilinear h U :=
  D.universal_shiftLocalHom (-1) h.toGradedShift U

/-- The tensor product of a homotopy sends `x ⊗ y` to `h x ⊗ y`. -/
theorem homotopyLocalHom_tmul (h : Homotopy f g) (U : C) (i j k : ℤ)
    (hijk : i + j + (-1) = k) (V : Over U)
    (x : (M.complex.X i).val.obj (Opposite.op V.left))
    (y : (N.complex.X j).val.obj (Opposite.op V.left)) :
    (D.homotopyLocalHom h U).app (i + j) k hijk V
        ((D.isTensorProduct M).tmul i j (Opposite.op V.left) x y) =
      castHom (D.functor.obj M₂).complex.X (show i - 1 + j = k by omega) (Opposite.op V.left)
        ((D.isTensorProduct M₂).tmul (i - 1) j (Opposite.op V.left)
          (homSections (h.app i) (Opposite.op V.left) x) y) :=
  D.shiftLocalHom_tmul (-1) h.toGradedShift U i j k hijk V x y

/-- The tensor product of a homotopy is compatible with restriction along a morphism of the
site. -/
theorem restrict_homotopyLocalHom (h : Homotopy f g) {U U' : C} (q : U' ⟶ U) :
    (D.homotopyLocalHom h U).restrict q = D.homotopyLocalHom h U' :=
  D.restrict_shiftLocalHom (-1) h.toGradedShift q

/-- The map on sections over an object of the site given by the tensor product of a
homotopy. -/
noncomputable def homotopySections (h : Homotopy f g) (k : ℤ) (U : Cᵒᵖ) :
    ((D.functor.obj M).complex.X k).val.obj U →+
      ((D.functor.obj M₂).complex.X (k - 1)).val.obj U :=
  D.shiftSections (-1) h.toGradedShift k U

/-- The tensor product of a homotopy commutes with restriction. -/
theorem homotopySections_naturality (h : Homotopy f g) (k : ℤ) {U V : Cᵒᵖ} (γ : U ⟶ V)
    (x : ((D.functor.obj M).complex.X k).val.obj U) :
    ((D.functor.obj M₂).complex.X (k - 1)).val.map γ (D.homotopySections h k U x) =
      D.homotopySections h k V (((D.functor.obj M).complex.X k).val.map γ x) :=
  D.shiftSections_naturality (-1) h.toGradedShift k γ x

/-- The degreewise map of sheaves of modules given by the tensor product of a homotopy. -/
noncomputable def homotopyHom (h : Homotopy f g) (k : ℤ) :
    (D.functor.obj M).complex.X k ⟶ (D.functor.obj M₂).complex.X (k - 1) :=
  D.shiftHom (-1) h.toGradedShift k

/-- The degreewise map given by the tensor product of a homotopy acts on local sections through
the degree `-1` local homomorphism it descends from. -/
theorem homotopyHom_apply (h : Homotopy f g) (k : ℤ) (U : Cᵒᵖ)
    (x : ((D.functor.obj M).complex.X k).val.obj U) :
    (D.homotopyHom h k).val.app U x = D.homotopySections h k U x := rfl

/-- The tensor product of a homotopy is a map of graded modules: it carries the action of a
homogeneous section of `𝒜'` to the action of that same section, the two degrees involved being
the two spellings `(n + i) - 1` and `(n - 1) + i`. -/
theorem homotopyHom_mul (h : Homotopy f g) (n i : ℤ) (U : Cᵒᵖ)
    (x : ((D.functor.obj M).complex.X n).val.obj U)
    (b : (A'.complex.X i).val.obj U) :
    HEq ((D.homotopyHom h (n + i)).val.app U
        (((D.functor.obj M).mul n i).app U x b))
      (((D.functor.obj M₂).mul (n - 1) i).app U ((D.homotopyHom h n).val.app U x) b) :=
  (heq_of_eq ((D.gradedShiftMap (-1) h.toGradedShift).map_smul n i U x b)).trans
    (heq_castHom (D.functor.obj M₂).complex.X
      (show n + -1 + i = n + i + -1 by omega) U _)

/-- The difference of the images of two homotopic morphisms is the commutator of the tensor
product of the homotopy with the differentials. This is the homotopy equation for the image
homotopy: the two signs produced by the Leibniz rule for the differential of a tensor product
cancel, leaving the homotopy equation for `h` tensored with the identity of `𝒩`. -/
theorem ofHomSub_eq_diffCommutator (h : Homotopy f g) (U : C) :
    LocalHom.ofHomSub (D.functor.map f) (D.functor.map g) U =
      (D.homotopyLocalHom h U).diffCommutator := by
  refine (D.isTensorProduct M).localHom_ext fun i j k hijk V x y => ?_
  have hcomm := homSections_congr (h.comm i) (Opposite.op V.left) x
  rw [homSections_sub] at hcomm
  simp only [homSections_add, homSections_comp] at hcomm
  rw [← castHom_eq_homSections_eqToHom M₂.complex.X (show i + 1 - 1 = i by omega)
    (Opposite.op V.left)] at hcomm
  simp only [homSections_apply] at hcomm
  rw [LocalHom.ofHomSub_app, LocalHom.diffCommutator_app,
    D.homotopyLocalHom_tmul h U i j (i + j - 1) (by omega) V x y]
  simp only [homSections_apply]
  rw [D.map_spec f i j (Opposite.op V.left) x y, D.map_spec g i j (Opposite.op V.left) x y,
    d_castHom_app (D.functor.obj M₂).complex (show i - 1 + j = i + j - 1 by omega)
      (show i - 1 + j + 1 = k by omega) (Opposite.op V.left),
    (D.isTensorProduct M₂).tmul_d_castHom (i - 1) j (Opposite.op V.left) _ y,
    (D.isTensorProduct M).tmul_d_castHom i j (Opposite.op V.left) x y]
  simp only [map_add, map_zsmul, castHom_castHom]
  rw [(D.homotopyLocalHom h U).toLocalGradedHom.app_castHom_source
      (show i + 1 + j = i + j + 1 by omega) (by omega) (by omega) V _,
    (D.homotopyLocalHom h U).toLocalGradedHom.app_castHom_source
      (show i + (j + 1) = i + j + 1 by omega) (by omega) (by omega) V _,
    D.homotopyLocalHom_tmul h U (i + 1) j k (by omega) V _ y,
    D.homotopyLocalHom_tmul h U i (j + 1) k (by omega) V x _]
  simp only [homSections_apply]
  rw [← (D.isTensorProduct M₂).tmul_sub_left, hcomm, (D.isTensorProduct M₂).tmul_add_left,
    map_add, d_app_castHom M₂.complex (show i - 1 + 1 = i by omega) (Opposite.op V.left),
    (D.isTensorProduct M₂).tmul_castHom_left (show i - 1 + 1 = i by omega) j
      (Opposite.op V.left),
    (D.isTensorProduct M₂).tmul_castHom_left (show i + 1 - 1 = i by omega) j
      (Opposite.op V.left)]
  simp only [castHom_castHom, negOnePow_sub_one, neg_smul]
  abel

/-- The tensor product `- ⊗_𝒜 𝒩` of a homotopy between two morphisms of right differential
graded `𝒜`-modules: a homotopy between the two tensored morphisms, given on `x ⊗ y` by
`h x ⊗ y`. -/
noncomputable def mapHomotopy (h : Homotopy f g) :
    Homotopy (D.functor.map f) (D.functor.map g) where
  app k := D.homotopyHom h k
  map_mul n i U x b := D.homotopyHom_mul h n i U x b
  comm n := by
    refine hom_ext_sections fun U x => ?_
    have hL := LocalHom.app_congr (D.ofHomSub_eq_diffCommutator h U.unop) n n (add_zero n)
      (Over.mk (𝟙 U.unop)) x
    rw [LocalHom.ofHomSub_app, LocalHom.diffCommutator_app, castHom_self] at hL
    rw [homSections_sub]
    refine hL.trans ?_
    simp only [homSections_add, homSections_comp]
    rw [← castHom_eq_homSections_eqToHom (D.functor.obj M₂).complex.X
      (show n + 1 - 1 = n by omega) U]
    simp only [homSections_apply, homotopyHom_apply, homotopySections]
    exact congrArg₂ (· + ·) rfl
      ((D.homotopyLocalHom h U.unop).toLocalGradedHom.app_castHom_target
        (show n + 1 - 1 = n by omega) (by omega) (by omega) (Over.mk (𝟙 U.unop))
        ((((D.functor.obj M).complex.d n (n + 1)).val.app U) x))

/-- The tensor product with a differential graded bimodule carries homotopic morphisms to
homotopic morphisms. -/
theorem preservesHomotopic : PreservesHomotopic D.functor :=
  fun _ _ ⟨h⟩ => ⟨D.mapHomotopy h⟩

end TensorFunctorData

end Tensor


section PullbackTensor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {C' : Type u'} [Category.{v'} C'] {J' : GrothendieckTopology C'} {R' : Sheaf J' RingCat.{t}}

namespace DifferentialGradedModule

variable {u : C' ⥤ C} {σ : R'.obj ⟶ u.op ⋙ R.obj}
  {A A' : DifferentialGradedAlgebra.{t, a} R} {B : DifferentialGradedAlgebra.{t, a'} R'}
  {φ : DifferentialGradedAlgebra.SemilinearHom u σ B A}
  {N : DifferentialGradedBimodule.{t, a, z} A A'}

/-- A differential graded extension of a pullback of right differential graded modules along a
morphism of ringed sites: a pullback of every homotopy, a homotopy between the pullbacks of the
two morphisms it connects. For the pullback `f^*ℳ = f⁻¹ℳ ⊗_{f⁻¹ℬ} 𝒜` the pullback of a
homotopy `h` is `f⁻¹h ⊗ 1`. -/
structure PullbackData.HomotopyExtension (P : PullbackData.{t, a, m, v, u, a', m'} φ) where
  /-- The pullback of a homotopy. -/
  mapHomotopy {M M₂ : DifferentialGradedModule.{t, a', m'} B} {ψ χ : M ⟶ M₂}
    (h : Homotopy ψ χ) : Homotopy (P.map ψ) (P.map χ)

/-- A pullback with a differential graded extension carries homotopic morphisms to homotopic
morphisms. -/
theorem PullbackData.HomotopyExtension.preservesHomotopic
    {P : PullbackData.{t, a, m, v, u, a', m'} φ} (E : P.HomotopyExtension) :
    PreservesHomotopic P.functor :=
  fun _ _ ⟨h⟩ => ⟨E.mapHomotopy h⟩

/-- The functor `ℳ ↦ f^*ℳ ⊗_𝒜 𝒩` from right differential graded `ℬ`-modules on the target of
a morphism of ringed sites to right differential graded `𝒜'`-modules on its source: the pullback
along the morphism, followed by the tensor product with the differential graded
`(𝒜, 𝒜')`-bimodule `𝒩`. -/
noncomputable def pullbackTensorFunctor (P : PullbackData.{t, a, m, v, u, a', m'} φ)
    (D : TensorFunctorData.{t, a, m, z, s} A A' N) :
    DifferentialGradedModule.{t, a', m'} B ⥤ DifferentialGradedModule.{t, a, s} A' :=
  P.functor ⋙ D.functor

/-- The functor `ℳ ↦ f^*ℳ ⊗_𝒜 𝒩` takes a module to the tensor product of its pullback with the
bimodule. -/
@[simp]
theorem pullbackTensorFunctor_obj (P : PullbackData.{t, a, m, v, u, a', m'} φ)
    (D : TensorFunctorData.{t, a, m, z, s} A A' N)
    (M : DifferentialGradedModule.{t, a', m'} B) :
    (pullbackTensorFunctor P D).obj M = D.functor.obj (P.obj M) :=
  rfl

/-- The functor `ℳ ↦ f^*ℳ ⊗_𝒜 𝒩` takes a morphism to the tensor product of its pullback with
the identity of the bimodule. -/
@[simp]
theorem pullbackTensorFunctor_map (P : PullbackData.{t, a, m, v, u, a', m'} φ)
    (D : TensorFunctorData.{t, a, m, z, s} A A' N)
    {M M₂ : DifferentialGradedModule.{t, a', m'} B} (ψ : M ⟶ M₂) :
    (pullbackTensorFunctor P D).map ψ = D.functor.map (P.map ψ) :=
  rfl

/-- The value of the functor at `ℳ` is a tensor product of the pullback of `ℳ` with `𝒩`. -/
def isTensorProduct_pullbackTensorFunctor_obj
    (P : PullbackData.{t, a, m, v, u, a', m'} φ)
    (D : TensorFunctorData.{t, a, m, z, s} A A' N)
    (M : DifferentialGradedModule.{t, a', m'} B) :
    IsTensorProduct (P.obj M) N ((pullbackTensorFunctor P D).obj M) :=
  D.isTensorProduct (P.obj M)

/-- On local sections the functor sends a morphism `ψ` to the map determined by
`x ⊗ y ↦ (f^*ψ) x ⊗ y`. -/
theorem pullbackTensorFunctor_map_tmul (P : PullbackData.{t, a, m, v, u, a', m'} φ)
    (D : TensorFunctorData.{t, a, m, z, s} A A' N)
    {M M₂ : DifferentialGradedModule.{t, a', m'} B} (ψ : M ⟶ M₂) (i j : ℤ) (U : Cᵒᵖ)
    (x : ((P.obj M).complex.X i).val.obj U) (y : (N.complex.X j).val.obj U) :
    (((pullbackTensorFunctor P D).map ψ).toHomologicalComplex.f (i + j)).val.app U
        ((D.isTensorProduct (P.obj M)).tmul i j U x y) =
      (D.isTensorProduct (P.obj M₂)).tmul i j U
        (((P.map ψ).toHomologicalComplex.f i).val.app U x) y :=
  D.map_spec (P.map ψ) i j U x y

/-- The functor `ℳ ↦ f^*ℳ ⊗_𝒜 𝒩` carries homotopic morphisms to homotopic morphisms: the
pullback of the homotopy, tensored with the identity of `𝒩`. -/
theorem preservesHomotopic_pullbackTensorFunctor
    {P : PullbackData.{t, a, m, v, u, a', m'} φ} (E : P.HomotopyExtension)
    (D : TensorFunctorData.{t, a, m, z, s} A A' N) :
    PreservesHomotopic (pullbackTensorFunctor P D) :=
  PreservesHomotopic.comp E.preservesHomotopic D.preservesHomotopic

namespace HomotopyCategory

/-- The functor `K(Mod(ℬ, d)) ⥤ K(Mod(𝒜', d))` induced by `ℳ ↦ f^*ℳ ⊗_𝒜 𝒩` on the homotopy
categories of right differential graded modules, for a pullback and a tensor product given by
their universal properties. Tag 0FTE is this functor at the *constructed* pullback and tensor
product, and is registered on
`Stacks.DifferentialGradedPullbackConstruction.exists_homotopyPullbackTensor`. -/
noncomputable def pullbackTensor {P : PullbackData.{t, a, m, v, u, a', m'} φ}
    (E : P.HomotopyExtension) (D : TensorFunctorData.{t, a, m, z, s} A A' N) :
    HomotopyCategory.{t, a', m'} B ⥤ HomotopyCategory.{t, a, s} A' :=
  descend (pullbackTensorFunctor P D) (preservesHomotopic_pullbackTensorFunctor E D)

/-- The induced functor factors `ℳ ↦ f^*ℳ ⊗_𝒜 𝒩` through the two quotient functors. -/
theorem quotient_comp_pullbackTensor {P : PullbackData.{t, a, m, v, u, a', m'} φ}
    (E : P.HomotopyExtension) (D : TensorFunctorData.{t, a, m, z, s} A A' N) :
    quotient B ⋙ pullbackTensor E D = pullbackTensorFunctor P D ⋙ quotient A' :=
  quotient_comp_descend _ _

/-- On an object represented by a right differential graded `ℬ`-module `ℳ`, the induced functor
is `f^*ℳ ⊗_𝒜 𝒩`. -/
@[simp]
theorem pullbackTensor_obj {P : PullbackData.{t, a, m, v, u, a', m'} φ}
    (E : P.HomotopyExtension) (D : TensorFunctorData.{t, a, m, z, s} A A' N)
    (M : DifferentialGradedModule.{t, a', m'} B) :
    (pullbackTensor E D).obj ((quotient B).obj M) =
      (quotient A').obj (D.functor.obj (P.obj M)) :=
  rfl

/-- On a homotopy class represented by a morphism `ψ` of right differential graded
`ℬ`-modules, the induced functor is `f^*ψ ⊗_𝒜 1`. -/
@[simp]
theorem pullbackTensor_map {P : PullbackData.{t, a, m, v, u, a', m'} φ}
    (E : P.HomotopyExtension) (D : TensorFunctorData.{t, a, m, z, s} A A' N)
    {M M₂ : DifferentialGradedModule.{t, a', m'} B} (ψ : M ⟶ M₂) :
    (pullbackTensor E D).map ((quotient B).map ψ) =
      (quotient A').map (D.functor.map (P.map ψ)) :=
  rfl

/-- The induced functor is the only functor of homotopy categories factoring
`ℳ ↦ f^*ℳ ⊗_𝒜 𝒩` through the two quotient functors. -/
theorem eq_pullbackTensor {P : PullbackData.{t, a, m, v, u, a', m'} φ}
    (E : P.HomotopyExtension) (D : TensorFunctorData.{t, a, m, z, s} A A' N)
    (Φ : HomotopyCategory.{t, a', m'} B ⥤ HomotopyCategory.{t, a, s} A')
    (hΦ : quotient B ⋙ Φ = pullbackTensorFunctor P D ⋙ quotient A') :
    Φ = pullbackTensor E D :=
  eq_descend _ _ _ hΦ

end HomotopyCategory

end DifferentialGradedModule

end PullbackTensor

end SheafOfModules

end
