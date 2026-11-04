module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CartesianModulePair

/-!
# Kernels and cokernels of morphisms of cartesian modules, read on pairs

Let `S` be a simplicial-site situation and `O` a sheaf of commutative rings on its total site.
Stacks 07TH presents a cartesian `O`-module as a pair `(F, α)`: a module `F` on the degree-zero
component together with an isomorphism `α : f_{δ¹₁}^* F ≅ f_{δ¹₀}^* F` on the degree-one
component satisfying a cocycle condition on the degree-two component. Stacks 0D7K is the warning
that the category of such pairs can be abelian while the inclusion of cartesian `O`-modules into
all `O`-modules is not exact; the half of it that is a mathematical assertion is that the
category of pairs is abelian as soon as `f_{δ¹₁}` and `f_{δ¹₀}` are flat. This file supplies the
degree-zero construction of kernels and cokernels of morphisms of pairs that that assertion rests
on.

What is built here is the degree-one half of that: the kernel and the cokernel of the
degree-zero morphism of a morphism of pairs, each with the comparison isomorphism in degree one
that restricts, resp. corestricts, the comparison isomorphism of the given pair, and each pinned
uniquely by that property. The cokernel needs no hypothesis at all — the pullback of sheaves of
modules is a left adjoint, hence right exact. The kernel needs the pullbacks `f_{δ¹₁}^*` and
`f_{δ¹₀}^*` to be left exact, which for flat `f_{δ¹₁}` and `f_{δ¹₀}` is Stacks 04JC.

The degree-two cocycle condition for those two comparison isomorphisms is *not* proved here, so
neither the kernel nor the cokernel is assembled into an object of the category of pairs and the
abelian structure itself is not covered; see the implementation notes for what is missing on each
side. The formal step that the cokernel side needs is supplied abstractly as
`CategoryTheory.ComparisonPair.cocycleTransport`, together with the naturality of the three
identifications occurring in the cocycle condition.

## Main definitions

* `CategoryTheory.ComparisonPair.kernelIso` and `CategoryTheory.ComparisonPair.cokernelIso`: for
  two functors `L`, `R` between abelian categories and a commuting square of comparison
  isomorphisms over a morphism `φ`, the induced comparison isomorphism on `kernel φ` (for `L`,
  `R` left exact) and on `cokernel φ` (for `L`, `R` right exact).
* `CategoryTheory.SimplicialSiteSituation.CartesianModulePair.kernelIso`: the degree-one
  comparison isomorphism on the kernel of a morphism of pairs.
* `CategoryTheory.SimplicialSiteSituation.CartesianModulePair.cokernelIso`: the degree-one
  comparison isomorphism on the cokernel of a morphism of pairs.

## Main results

* `CategoryTheory.ComparisonPair.kernelIso_hom_comp`, `.map_comp_cokernelIso_hom` and the two
  uniqueness statements `.eq_kernelIso_hom`, `.eq_cokernelIso_hom`: the comparison isomorphisms
  restrict the given one along the kernel inclusion, resp. corestrict it along the cokernel
  projection, and are the only morphisms that do.
* `CategoryTheory.ComparisonPair.cocycleTransport`: the formal transport of a degree-two cocycle
  condition along a morphism whose image under the middle degree-two functor is an epimorphism.
* `CategoryTheory.SimplicialSiteSituation.pasteModulesOfEq_naturality`,
  `.glueModulesOfEq_naturality` and `.glueModulesOfEq_naturality_inv`: the identifications of the
  pullbacks of a module along two factorizations of one simplex map are natural in the module.
* `CategoryTheory.SimplicialSiteSituation.CartesianModulePair.kernelIso_hom_comp`: **Stacks
  0D7K**, the kernel half in degree one.
* `CategoryTheory.SimplicialSiteSituation.CartesianModulePair.map_comp_cokernelIso_hom`:
  **Stacks 0D7K**, the cokernel half in degree one, with no flatness hypothesis.

## Implementation notes

**What of Stacks 0D7K is and is not covered.** The source's remark has two halves. The positive
half, that the category of cartesian `O`-modules is abelian when only `f_{δ¹₁}` and `f_{δ¹₀}` are
known to be flat, is said to follow from the pair description of Stacks 07TH. Both halves are
proved here in degree one and neither in degree two, but for different reasons.

On the kernel side the degree-two cocycle condition does not follow from the stated hypotheses at
all. It is an equation between two morphisms `f_{τ²₀}^* K ⟶ f_{τ²₂}^* K`, where
`τ²ᵢ : ⦋0⦌ ⟶ ⦋2⦌` is a vertex of `⦋2⦌` and so factors through a degree-two face, which the
hypotheses do *not* make flat. The two morphisms agree after composition with `f_{τ²₂}^*` of the
kernel inclusion, and that morphism is a monomorphism only if the degree-two pullback is left
exact. The source's "follows easily" does not address this, and no proof of it is given here.

On the cokernel side the condition does follow, with no hypothesis: the pullback of modules is
right exact unconditionally, so the dual cancellation is by the epimorphism
`f_{δ²₁}^* f_{δ¹₁}^* π`, which is always available. That argument is carried out here as the
abstract `CategoryTheory.ComparisonPair.cocycleTransport`, whose three naturality hypotheses are
the `glueModulesOfEq` naturality lemmas below. What is not carried out is its instantiation at
the simplicial pullbacks: a face `δ²ⱼ` has domain `⦋1⦌` while a degree-one face has codomain
`⦋0 + 1⦌`, so the degree-one component occurs in two spellings differing by an invisible numeral,
and a direct instantiation of the transport crosses those two spellings in more than one
argument at once and exhausts the elaborator. Assembling the cokernel pair and its universal
property therefore waits on a spelling in which that crossing is made once; the mathematics of it
is complete in `cocycleTransport`.

The negative half of the remark — that for non-flat `f_{δ²₀}` "there is no reason for the
inclusion functor to be exact" — asserts no counterexample, only the absence of an argument, and
is therefore not a formalizable statement; nothing here covers it.

**Left exactness rather than flatness as the hypothesis on the kernel side.** The remark's
hypothesis is flatness of the two degree-one faces. Flatness of a morphism of ringed topoi
implies exactness of its pullback of modules by Stacks 04JC, which this development has as
`Stacks.Sheaves.RingedToposModules.pullbackModules_exact_of_isFlatMap`. That statement is phrased
for the pullback built over `AlgebraicGeometry.RingedToposHom.toRingedToposModulesHom`, whereas
`CategoryTheory.SimplicialSiteSituation.componentModulePullback`, over which the category of
pairs is defined, is built over `AlgebraicGeometry.RingedToposHom.toModulesHom`. The two take the
inverse-image form of the structure map through the adjunction for sheaves of rings and for
sheaves of commutative rings respectively, and their identification is, in the words of the
docstring of `AlgebraicGeometry.RingedToposHom.fSharpInverseImageRing`, "not needed here and is
not recorded"; it is not an identity of definitional unfoldings, nor one that
holds on sections by `rfl`. The kernel statements below therefore take left exactness of the two
degree-one pullbacks as the hypothesis. That is a weaker hypothesis than flatness, so the
statements are more general rather than weaker, and the flatness form follows from them as soon
as that identification is recorded.

**Naturality of the pullback identifications.** The cocycle condition is stated through the three
identifications `glueModulesLeft`, `glueModulesMiddle` and `glueModulesRight` of
`StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/CartesianModulePair.lean`, which
are given one module at a time. Transporting the condition from a pair to its cokernel needs them
to be natural in the module, which that file does not record; the naturality lemmas are supplied
here, for `pasteModulesOfEq` and then for `glueModulesOfEq`, rather than added there, so that no
module already built against that file has to be rebuilt. They are consequences of the naturality
of `transitionPullbackModulesCompIso`, which is a natural isomorphism of functors, together with
the fact that the `eqToHom` of a factorization becomes an identity once the factorized morphism
is substituted away.

The abstract comparison constructions are stated for two arbitrary functors between abelian
categories, and the simplicial statements are instances of them; stating the kernel and cokernel
comparisons directly over the pullbacks of modules puts the four layers of
`Stacks.Sheaves.RingedToposModules.pullbackModules` into every goal, which is the cost this
directory's abstract-helper discipline exists to avoid.

## References

* [Stacks Project, Tag 0D7K](https://stacks.math.columbia.edu/tag/0D7K)
* [Stacks Project, Tag 07TH](https://stacks.math.columbia.edu/tag/07TH)
* [Stacks Project, Tag 0D7J](https://stacks.math.columbia.edu/tag/0D7J)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Simplicial

universe v₁ v₂ u₁ u₂ u

namespace CategoryTheory

noncomputable section

/-! ### Comparison isomorphisms on kernels and cokernels -/

namespace ComparisonPair

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
  [Abelian A] [Abelian B] (L R : A ⥤ B) {X Y : A} (φ : X ⟶ Y)
  (a : L.obj X ≅ R.obj X) (b : L.obj Y ≅ R.obj Y)
  (h : L.map φ ≫ b.hom = a.hom ≫ R.map φ)

section Kernel

variable [PreservesFiniteLimits L] [PreservesFiniteLimits R]

/-- The comparison isomorphism induced on the kernel of `φ` by a commuting square of comparison
isomorphisms over `φ`, for left exact `L` and `R`. -/
def kernelIso : L.obj (kernel φ) ≅ R.obj (kernel φ) :=
  PreservesKernel.iso L φ ≪≫ kernel.mapIso (L.map φ) (R.map φ) a b h ≪≫
    (PreservesKernel.iso R φ).symm

/-- `R.map (kernel.ι φ)` is a monomorphism when `R` is left exact. -/
theorem mono_map_kernel_ι : Mono (R.map (kernel.ι φ)) := by
  have hR : R.map (kernel.ι φ) = (PreservesKernel.iso R φ).hom ≫ kernel.ι (R.map φ) := by
    rw [← PreservesKernel.iso_inv_ι R φ, Iso.hom_inv_id_assoc]
  rw [hR]
  infer_instance

/-- The comparison isomorphism on the kernel of `φ` restricts the given comparison isomorphism
along the kernel inclusion. -/
theorem kernelIso_hom_comp :
    (kernelIso L R φ a b h).hom ≫ R.map (kernel.ι φ) = L.map (kernel.ι φ) ≫ a.hom := by
  simp [kernelIso]

/-- The comparison isomorphism on the kernel of `φ` is the only morphism restricting the given
comparison isomorphism along the kernel inclusion. -/
theorem eq_kernelIso_hom (β : L.obj (kernel φ) ⟶ R.obj (kernel φ))
    (hβ : β ≫ R.map (kernel.ι φ) = L.map (kernel.ι φ) ≫ a.hom) :
    β = (kernelIso L R φ a b h).hom := by
  rw [← cancel_mono (R.map (kernel.ι φ)), hβ, kernelIso_hom_comp]

end Kernel

section Cokernel

variable [PreservesFiniteColimits L] [PreservesFiniteColimits R]

/-- The comparison isomorphism induced on the cokernel of `φ` by a commuting square of comparison
isomorphisms over `φ`, for right exact `L` and `R`. -/
def cokernelIso : L.obj (cokernel φ) ≅ R.obj (cokernel φ) :=
  PreservesCokernel.iso L φ ≪≫ cokernel.mapIso (L.map φ) (R.map φ) a b h ≪≫
    (PreservesCokernel.iso R φ).symm

/-- `L.map (cokernel.π φ)` is an epimorphism when `L` is right exact. -/
theorem epi_map_cokernel_π : Epi (L.map (cokernel.π φ)) :=
  inferInstance

/-- The comparison isomorphism on the cokernel of `φ` corestricts the given comparison
isomorphism along the cokernel projection. -/
theorem map_comp_cokernelIso_hom :
    L.map (cokernel.π φ) ≫ (cokernelIso L R φ a b h).hom = b.hom ≫ R.map (cokernel.π φ) := by
  simp [cokernelIso]

/-- The comparison isomorphism on the cokernel of `φ` is the only morphism corestricting the
given comparison isomorphism along the cokernel projection. -/
theorem eq_cokernelIso_hom (β : L.obj (cokernel φ) ⟶ R.obj (cokernel φ))
    (hβ : L.map (cokernel.π φ) ≫ β = b.hom ≫ R.map (cokernel.π φ)) :
    β = (cokernelIso L R φ a b h).hom := by
  rw [← cancel_epi (L.map (cokernel.π φ)), hβ, map_comp_cokernelIso_hom]

end Cokernel

section CocycleTransport

universe w₁ w₂ t₁ t₂

variable {C₁ : Type t₁} [Category.{w₁} C₁] {C₂ : Type t₂} [Category.{w₂} C₂]

/-- Transport of a degree-two cocycle condition along a morphism whose image under the middle
degree-two functor is an epimorphism. The three functors are the degree-two faces; the objects
and morphisms are read in degree one, so the degree-one faces do not appear. -/
theorem cocycleTransport (D₂ D₁ D₀ : C₁ ⥤ C₂) {X₁ X₀ Y₁ Y₀ : C₁}
    (p₁ : X₁ ⟶ Y₁) (p₀ : X₀ ⟶ Y₀)
    (gLX : D₂.obj X₁ ≅ D₁.obj X₁) (gLY : D₂.obj Y₁ ≅ D₁.obj Y₁)
    (gMX : D₂.obj X₀ ≅ D₀.obj X₁) (gMY : D₂.obj Y₀ ≅ D₀.obj Y₁)
    (gRX : D₀.obj X₀ ≅ D₁.obj X₀) (gRY : D₀.obj Y₀ ≅ D₁.obj Y₀)
    (hL : D₁.map p₁ ≫ gLY.inv = gLX.inv ≫ D₂.map p₁)
    (hM : D₂.map p₀ ≫ gMY.hom = gMX.hom ≫ D₀.map p₁)
    (hR : D₀.map p₀ ≫ gRY.hom = gRX.hom ≫ D₁.map p₀)
    (αX : X₁ ⟶ X₀) (αY : Y₁ ⟶ Y₀) (hα : p₁ ≫ αY = αX ≫ p₀)
    (hepi : Epi (D₁.map p₁))
    (hX : D₁.map αX = gLX.inv ≫ D₂.map αX ≫ gMX.hom ≫ D₀.map αX ≫ gRX.hom) :
    D₁.map αY = gLY.inv ≫ D₂.map αY ≫ gMY.hom ≫ D₀.map αY ≫ gRY.hom := by
  rw [← cancel_epi (D₁.map p₁)]
  rw [← Functor.map_comp, hα, Functor.map_comp]
  rw [reassoc_of% hL, ← Functor.map_comp_assoc, hα, Functor.map_comp_assoc]
  rw [reassoc_of% hM, ← Functor.map_comp_assoc, hα, Functor.map_comp_assoc]
  rw [hR, hX]
  simp only [Category.assoc]

end CocycleTransport

end ComparisonPair

/-! ### Naturality of the pullback identifications -/

namespace SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

/-- The pullback compositor at a factorization is natural in the module. -/
theorem pasteModulesOfEq_naturality {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (θ : l ⟶ n) (hθ : ψ ≫ φ = θ) {F F' : (S.componentRingedTopos O l).Modules} (g : F ⟶ F') :
    (S.componentModulePullback O φ).map ((S.componentModulePullback O ψ).map g) ≫
        (S.pasteModulesOfEq O ψ φ θ hθ F').hom =
      (S.pasteModulesOfEq O ψ φ θ hθ F).hom ≫ (S.componentModulePullback O θ).map g := by
  subst hθ
  simp only [pasteModulesOfEq, Iso.trans_hom, eqToIso.hom, eqToHom_refl, Category.comp_id]
  exact (S.transitionPullbackModulesCompIso O ψ φ).inv.naturality g

/-- The identification of the pullbacks of a module along two factorizations of one simplex map
is natural in the module. -/
theorem glueModulesOfEq_naturality {l m n : SimplexCategory} (ψ ψ' : l ⟶ m) (φ φ' : m ⟶ n)
    (v : l ⟶ n) (hv : ψ ≫ φ = v) (hv' : ψ' ≫ φ' = v)
    {F F' : (S.componentRingedTopos O l).Modules} (g : F ⟶ F') :
    (S.componentModulePullback O φ).map ((S.componentModulePullback O ψ).map g) ≫
        (S.glueModulesOfEq O ψ ψ' φ φ' v hv hv' F').hom =
      (S.glueModulesOfEq O ψ ψ' φ φ' v hv hv' F).hom ≫
        (S.componentModulePullback O φ').map ((S.componentModulePullback O ψ').map g) := by
  rw [glueModulesOfEq_hom, glueModulesOfEq_hom, ← Category.assoc,
    S.pasteModulesOfEq_naturality O ψ φ v hv g, Category.assoc, Category.assoc,
    Iso.cancel_iso_hom_left, Iso.eq_inv_comp, ← Category.assoc,
    ← S.pasteModulesOfEq_naturality O ψ' φ' v hv' g]
  simp

/-- The inverse form of `glueModulesOfEq_naturality`. -/
theorem glueModulesOfEq_naturality_inv {l m n : SimplexCategory} (ψ ψ' : l ⟶ m) (φ φ' : m ⟶ n)
    (v : l ⟶ n) (hv : ψ ≫ φ = v) (hv' : ψ' ≫ φ' = v)
    {F F' : (S.componentRingedTopos O l).Modules} (g : F ⟶ F') :
    (S.componentModulePullback O φ').map ((S.componentModulePullback O ψ').map g) ≫
        (S.glueModulesOfEq O ψ ψ' φ φ' v hv hv' F').inv =
      (S.glueModulesOfEq O ψ ψ' φ φ' v hv hv' F).inv ≫
        (S.componentModulePullback O φ).map ((S.componentModulePullback O ψ).map g) := by
  rw [Iso.eq_inv_comp, ← Category.assoc,
    ← S.glueModulesOfEq_naturality O ψ ψ' φ φ' v hv hv' g]
  simp

/-! ### Right exactness of the pullback of modules along a transition -/

/-- The pullback of sheaves of modules along a simplicial transition is a left adjoint. -/
local instance componentModulePullback_isLeftAdjoint {m n : SimplexCategory} (φ : m ⟶ n) :
    (S.componentModulePullback O φ).IsLeftAdjoint := by
  change ((S.transitionRingedToposHom O φ).toModulesHom.pullbackModules).IsLeftAdjoint
  exact (AlgebraicGeometry.RingedToposHom.pullbackAdjPushforwardModules
    (S.transitionRingedToposHom O φ)).isLeftAdjoint

/-- The pullback of sheaves of modules along a simplicial transition is right exact. -/
local instance componentModulePullback_preservesFiniteColimits {m n : SimplexCategory}
    (φ : m ⟶ n) : PreservesFiniteColimits (S.componentModulePullback O φ) := by
  change PreservesFiniteColimits ((S.transitionRingedToposHom O φ).toModulesHom.pullbackModules)
  exact AlgebraicGeometry.RingedToposHom.pullbackModules_preservesFiniteColimits
    (S.transitionRingedToposHom O φ)

/-! ### Kernels and cokernels of morphisms of pairs -/

namespace CartesianModulePair

section Kernel

variable [PreservesFiniteLimits (S.componentModulePullback O (SimplexCategory.δ (1 : Fin 2)))]
  [PreservesFiniteLimits (S.componentModulePullback O (SimplexCategory.δ (0 : Fin 2)))]
  {A B : CartesianModulePair S O} (f : A ⟶ B)

/-- The degree-one comparison isomorphism on the kernel of a morphism of pairs, for left exact
degree-one pullbacks. -/
def kernelIso :
    (S.componentModulePullback O (SimplexCategory.δ (1 : Fin 2))).obj (kernel f.map) ≅
      (S.componentModulePullback O (SimplexCategory.δ (0 : Fin 2))).obj (kernel f.map) :=
  ComparisonPair.kernelIso _ _ f.map A.iso B.iso f.comm

/-- **Stacks 0D7K**, the kernel half of the positive assertion, in degree one. If the two
degree-one pullbacks are left exact — which, for flat `f_{δ¹₁}` and `f_{δ¹₀}`, is Stacks 04JC —
then the kernel of the degree-zero morphism of a morphism of pairs carries a comparison
isomorphism restricting the comparison isomorphism of the source pair along the kernel
inclusion. -/
@[stacks 0D7K "the kernel half of the positive assertion, in degree one: under left exactness of
f_{δ¹₁}^* and f_{δ¹₀}^* (which flatness of f_{δ¹₁} and f_{δ¹₀} gives by Stacks 04JC), the kernel
of a morphism of the pairs of Stacks 07TH carries a comparison isomorphism restricting that of
the source pair, and it is the only morphism that does. NOT covered here: the degree-two cocycle
condition for that isomorphism, hence not the kernel object in the category of pairs and not the
abelian structure; and not the assertion that the inclusion of cartesian O-modules into all
O-modules fails to be exact, which the source states as the absence of a reason for exactness
and not as a counterexample"]
theorem kernelIso_hom_comp :
    (kernelIso S O f).hom ≫
        (S.componentModulePullback O (SimplexCategory.δ (0 : Fin 2))).map (kernel.ι f.map) =
      (S.componentModulePullback O (SimplexCategory.δ (1 : Fin 2))).map (kernel.ι f.map) ≫
        A.iso.hom :=
  ComparisonPair.kernelIso_hom_comp _ _ f.map A.iso B.iso f.comm

/-- The comparison isomorphism on the kernel is the only morphism restricting the comparison
isomorphism of the source pair along the kernel inclusion. -/
theorem eq_kernelIso_hom
    (β : (S.componentModulePullback O (SimplexCategory.δ (1 : Fin 2))).obj (kernel f.map) ⟶
      (S.componentModulePullback O (SimplexCategory.δ (0 : Fin 2))).obj (kernel f.map))
    (hβ : β ≫ (S.componentModulePullback O (SimplexCategory.δ (0 : Fin 2))).map
          (kernel.ι f.map) =
        (S.componentModulePullback O (SimplexCategory.δ (1 : Fin 2))).map (kernel.ι f.map) ≫
          A.iso.hom) :
    β = (kernelIso S O f).hom :=
  ComparisonPair.eq_kernelIso_hom _ _ f.map A.iso B.iso f.comm β hβ

end Kernel

section Cokernel

variable {A B : CartesianModulePair S O} (f : A ⟶ B)

/-- The degree-one comparison isomorphism on the cokernel of a morphism of pairs. The pullback of
sheaves of modules is right exact with no hypothesis, so none is needed here. -/
def cokernelIso :
    (S.componentModulePullback O (SimplexCategory.δ (1 : Fin 2))).obj (cokernel f.map) ≅
      (S.componentModulePullback O (SimplexCategory.δ (0 : Fin 2))).obj (cokernel f.map) :=
  ComparisonPair.cokernelIso _ _ f.map A.iso B.iso f.comm

/-- **Stacks 0D7K**, the cokernel half of the positive assertion, in degree one. The pullback of
sheaves of modules is right exact unconditionally, so with no flatness hypothesis at all the
cokernel of the degree-zero morphism of a morphism of pairs carries a comparison isomorphism
corestricting the comparison isomorphism of the target pair along the cokernel projection. -/
@[stacks 0D7K "the cokernel half of the positive assertion, in degree one, and with no flatness
hypothesis at all, the pullback of modules being right exact unconditionally: the cokernel of a
morphism of the pairs of Stacks 07TH carries a comparison isomorphism corestricting that of the
target pair, and it is the only morphism that does. NOT covered here: the degree-two cocycle
condition for that isomorphism, hence not the cokernel object in the category of pairs and not
the abelian structure; and not the assertion that the inclusion of cartesian O-modules into all
O-modules fails to be exact, which the source states as the absence of a reason for exactness
and not as a counterexample"]
theorem map_comp_cokernelIso_hom :
    (S.componentModulePullback O (SimplexCategory.δ (1 : Fin 2))).map (cokernel.π f.map) ≫
        (cokernelIso S O f).hom =
      B.iso.hom ≫
        (S.componentModulePullback O (SimplexCategory.δ (0 : Fin 2))).map (cokernel.π f.map) :=
  ComparisonPair.map_comp_cokernelIso_hom _ _ f.map A.iso B.iso f.comm

/-- The comparison isomorphism on the cokernel is the only morphism corestricting the comparison
isomorphism of the target pair along the cokernel projection. -/
theorem eq_cokernelIso_hom
    (β : (S.componentModulePullback O (SimplexCategory.δ (1 : Fin 2))).obj (cokernel f.map) ⟶
      (S.componentModulePullback O (SimplexCategory.δ (0 : Fin 2))).obj (cokernel f.map))
    (hβ : (S.componentModulePullback O (SimplexCategory.δ (1 : Fin 2))).map
          (cokernel.π f.map) ≫ β =
        B.iso.hom ≫ (S.componentModulePullback O (SimplexCategory.δ (0 : Fin 2))).map
          (cokernel.π f.map)) :
    β = (cokernelIso S O f).hom :=
  ComparisonPair.eq_cokernelIso_hom _ _ f.map A.iso B.iso f.comm β hβ

/-- The cokernel projection of the degree-zero morphism stays an epimorphism under every
pullback out of degree zero. -/
theorem epi_map_cokernel_π {k : SimplexCategory} (φ : ⦋0⦌ ⟶ k) :
    Epi ((S.componentModulePullback O φ).map (cokernel.π f.map)) :=
  ComparisonPair.epi_map_cokernel_π (L := S.componentModulePullback O φ) (φ := f.map)

end Cokernel

end CartesianModulePair

end SimplicialSiteSituation

end

end CategoryTheory

end
