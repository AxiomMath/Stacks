module

public import StacksFrontier.Deformation.RingedSpaceThickening.DeformationDiagram
public import StacksCore.CategoryTheory.Abelian.DiagramLemmas.Four
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
import StacksCore.Tactic.StacksAttribute

/-!
# A morphism of solutions of a deformation problem is invertible (Stacks 08UC)

Fix a first order thickening `t : (S, 𝒪_S) ⟶ (S', 𝒪_{S'})` with ideal `𝒥`, a morphism
`f : (X, 𝒪_X) ⟶ (S, 𝒪_S)`, an `𝒪_X`-module `𝒢` and a prescribed map `c : f^* t^* 𝒥 ⟶ 𝒢`. A
solution of the deformation problem (91.7.0.1) of Tag 08U7 is a
`AlgebraicGeometry.RingedSpaceThickening.DeformationSolution t ht f G c`. A *morphism* of
solutions is a morphism of the deformed ringed spaces which is a morphism under `X`, a morphism
over `S'`, and the identity on the prescribed square-zero ideal `𝒢`.

The point of this file is the source's parenthetical "clearly, this element is the obstruction to
the existence of an isomorphism": a morphism of solutions is *automatically* invertible. Two
solutions `Q₁`, `Q₂` sit in short exact sequences of `𝒪_{X'₂}`-modules

    0 ⟶ 𝒢 ⟶ (X'₁ ⟶ X'₂)_* 𝒪_{X'₁} ⟶ 𝒪_X ⟶ 0        and        0 ⟶ 𝒢 ⟶ 𝒪_{X'₂} ⟶ 𝒪_X ⟶ 0

with the *same* outer terms, and a morphism of solutions is by definition compatible with both
of them; so the short five lemma applies and the comparison of the middle terms is an
isomorphism.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.SolutionHom`: a morphism of solutions of the
  deformation problem of Tag 08U7.
* `AlgebraicGeometry.RingedSpaceThickening.SolutionHom.id`: the identity morphism of a
  solution; in particular the notion is not vacuous.
* `AlgebraicGeometry.RingedSpaceThickening.Isomorphic`: two solutions are isomorphic when some
  morphism of solutions between them is invertible as a morphism of ringed spaces.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.SolutionHom.isIso_structureMap`: the short five
  lemma on the two ideal rows — the map of structure sheaves of a morphism of solutions is an
  isomorphism of sheaves of modules.
* `AlgebraicGeometry.RingedSpaceThickening.SolutionHom.isIso_hom`: a morphism of solutions is
  an isomorphism of ringed spaces.
* `AlgebraicGeometry.RingedSpaceThickening.isomorphic_iff_nonempty_solutionHom`:
  **Stacks 08UC**, the half asserting that the obstruction separates isomorphism classes — two
  solutions are isomorphic exactly when there is a morphism of solutions between them.

## Implementation notes

**The torsor half of Tag 08UC is not claimed here**; it is
`exists_addTorsor_solutionClasses` of
`StacksFrontier/Deformation/RingedSpaceThickening/SolutionClassesPrincipalHomogeneous.lean`, built
on `SolutionClasses.lean`. The tag has two halves: that the set of
isomorphism classes of solutions is a principal homogeneous space under
`Ext¹_{𝒪_X}(NL_{X/S}, 𝒢)`, and that the obstruction class of Tag 08U8 separates those classes.
Only the second is proved here, and the tag attribute carries a clause string saying so. The
first needs the difference cocycle of two solutions, which in the source is computed after
replacing the presentation by `𝒪_{X'₁} ×_{𝒪_X} 𝒪_{X'₂}`; that choice depends on the *pair* of
solutions, and the formalism of
`StacksFrontier/Deformation/RingedSpaceThickening/SolutionTorsor.lean` takes the presentation as a
single fixed datum. Nothing in this file depends on that formalism: no obstruction class, no
pushout action and no `Ext` group occurs below.

For the same reason the `Setoid` of `SolutionObstruction` in that file is *not* reused: its
relation is *defined* as the vanishing of the obstruction class, hence presupposes the
obstruction data. The relation here is the geometric one — existence of an invertible morphism
of solutions — and `isomorphic_iff_nonempty_solutionHom` is exactly the bridge that makes the
two quotients agree once an obstruction theory is available.

The two exact rows live on `X'₂`: the row of `Q₁`, which lives on `X'₁`, is pushed forward along
the comparison morphism, which is legitimate because a right adjoint preserves kernels, and
surjectivity of the pushed-forward structure map is read off the commutative square rather than
from exactness of the pushforward. Accordingly the comparison of the two ideals is the induced
map on kernels (`SolutionHom.idealMap`), and the comparison of the two quotients is
`SolutionHom.quotientComparison`, the component of `pushforwardIsoOfComp` which identifies
`(Q₂.i)_*` with `(Q₁.i)_* ⋙ hom_*`. The short five lemma is applied in the `ShortComplex` form,
`CategoryTheory.ShortComplex.mono_of_mono_of_mono_of_mono` and
`CategoryTheory.ShortComplex.epi_of_epi_of_epi_of_epi`, which are the two halves of
**Stacks 05QA** behind the five lemma of **Stacks 05QB**; the `ComposableArrows` form is not
convenient here because only two of the five columns are nonzero.

The passage from an isomorphism of sheaves of modules to an isomorphism of ringed spaces is
sectionwise: `SheafOfModules.unitToPushforwardObjUnit` has the same underlying map on sections
as the comorphism it is built from, so bijectivity transfers, and a morphism of presheafed
spaces whose base map and comorphism are both isomorphisms is an isomorphism. That the base map
is an isomorphism needs no sheaf theory: both thickenings are homeomorphisms on underlying
spaces by definition.

## References

* [Stacks Project, Tag 08UC](https://stacks.math.columbia.edu/tag/08UC)
* [Stacks Project, Tag 08U7](https://stacks.math.columbia.edu/tag/08U7)
* [Stacks Project, Tag 08U8](https://stacks.math.columbia.edu/tag/08U8)
* [Stacks Project, Tag 05QB](https://stacks.math.columbia.edu/tag/05QB)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

/-! ### Pushforward along a factorisation -/

/-- The comparison `j_* ≅ a_* ⋙ b_*` attached to a factorisation `a ≫ b = j` of a morphism of
ringed spaces: the pushforward comparison `modulePushforwardCompSymm` of `a` and `b`, which
points from `(a ≫ b)_*` to `a_* ⋙ b_*`, transported along the equality of morphisms. The type
of `modulePushforward` does not depend on the morphism, only on its source and target, so the
transport is an `eqToIso` of functors. -/
noncomputable def pushforwardIsoOfComp {X Y Z : RingedSpace.{u, u}} (a : X ⟶ Y) (b : Y ⟶ Z)
    (j : X ⟶ Z) (hj : a ≫ b = j) :
    modulePushforward j ≅ modulePushforward a ⋙ modulePushforward b :=
  eqToIso (congrArg (fun k : X ⟶ Z => modulePushforward k) hj).symm ≪≫
    modulePushforwardCompSymm a b

/-- The map of structure sheaves of a factorisation `a ≫ b = j`, as a map of sheaves of
modules, is the composite of the two maps of the factors, read through
`pushforwardIsoOfComp`. Both sides are the same map on sections, so after transporting along
the factorisation the two agree componentwise. -/
lemma unitToPushforwardObjUnit_comp {X Y Z : RingedSpace.{u, u}} (a : X ⟶ Y) (b : Y ⟶ Z)
    (j : X ⟶ Z) (hj : a ≫ b = j) :
    SheafOfModules.unitToPushforwardObjUnit (structureSheafHom b) ≫
        (modulePushforward b).map
          (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom a)) =
      SheafOfModules.unitToPushforwardObjUnit (structureSheafHom j) ≫
        (pushforwardIsoOfComp a b j hj).hom.app (SheafOfModules.unit (structureSheafRing X)) := by
  subst hj
  ext U
  rfl

/-- Reassociation of a composite of four morphisms, in the one shape used below. -/
lemma comp_assoc₃ {C : Type*} [Category* C] {A B D E F : C}
    (a : A ⟶ B) (b : B ⟶ D) (d : D ⟶ E) (g : E ⟶ F) :
    (a ≫ b ≫ d) ≫ g = a ≫ b ≫ d ≫ g :=
  (Category.assoc a (b ≫ d) g).trans (congrArg (fun k => a ≫ k) (Category.assoc b d g))

variable {X S S' : RingedSpace.{u, u}} {t : S ⟶ S'}
  {ht : IsFirstOrderThickening t} {f : X ⟶ S}
  {G : SheafOfModules.{u} (structureSheafRing X)}
  {c : (modulePullback f).obj
    ((modulePullback t).obj (AlgebraicGeometry.SheafOfModules.idealSheaf t)) ⟶ G}

/-! ### The ideal row of a solution -/

/-- The map `𝒪_{X'} ⟶ i_* 𝒪_X` of structure sheaves of a solution of the deformation problem of
Tag 08U7, as a map of sheaves of `𝒪_{X'}`-modules. Its kernel is the ideal of the thickening. -/
noncomputable abbrev DeformationSolution.structureMap (Q : DeformationSolution t ht f G c) :
    SheafOfModules.unit (structureSheafRing Q.X') ⟶ (modulePushforward Q.i).obj
      (SheafOfModules.unit (structureSheafRing X)) :=
  SheafOfModules.unitToPushforwardObjUnit (structureSheafHom Q.i)

/-- The identification of `𝒢` with the ideal of a solution, with the ideal spelled out as the
kernel of `DeformationSolution.structureMap` rather than as
`AlgebraicGeometry.SheafOfModules.idealSheaf`. The two are the same object; naming the kernel is
what lets the five-lemma rows below be stated and rewritten in a single vocabulary. -/
noncomputable def DeformationSolution.idealIso (Q : DeformationSolution t ht f G c) :
    (modulePushforward Q.i).obj G ≅ kernel Q.structureMap :=
  Q.kernelIso.symm

/-- The inclusion `𝒢 ⟶ 𝒪_{X'}` of the prescribed module as the square-zero ideal of a
solution. -/
noncomputable abbrev DeformationSolution.idealInclusion (Q : DeformationSolution t ht f G c) :
    (modulePushforward Q.i).obj G ⟶ SheafOfModules.unit (structureSheafRing Q.X') :=
  Q.idealIso.hom ≫ kernel.ι Q.structureMap

/-- The ideal of a solution is killed by the map to the structure sheaf of `X`. -/
lemma DeformationSolution.idealInclusion_comp_structureMap
    (Q : DeformationSolution t ht f G c) : Q.idealInclusion ≫ Q.structureMap = 0 := by
  rw [Category.assoc, kernel.condition, comp_zero]

/-- Reading the ideal inclusion back through the identification with `𝒢` gives the inclusion of
the kernel. -/
lemma DeformationSolution.idealIso_inv_comp_idealInclusion
    (Q : DeformationSolution t ht f G c) :
    Q.idealIso.inv ≫ Q.idealInclusion = kernel.ι Q.structureMap :=
  Q.idealIso.inv_hom_id_assoc _

/-! ### Morphisms of solutions -/

/-- A morphism of solutions of the deformation problem of Tag 08U7: a morphism of the deformed
ringed spaces which is a morphism under `X`, a morphism over `S'`, and the identity on the
prescribed square-zero ideal `𝒢`.

The last condition is the commutative square saying that the comorphism `hom^♯`, restricted to
the ideal of `Q₂` and read through the two identifications of the ideals with `𝒢`, is the
identity of `𝒢`; the identification of `(Q₂.i)_* 𝒢` with `hom_* (Q₁.i)_* 𝒢` is
`pushforwardIsoOfComp`, available because `hom` is a morphism under `X`. -/
structure SolutionHom (Q₁ Q₂ : DeformationSolution t ht f G c) where
  /-- The morphism of the deformed ringed spaces. -/
  hom : Q₁.X' ⟶ Q₂.X'
  /-- It is a morphism under `X`. -/
  thickening_comm : Q₁.i ≫ hom = Q₂.i
  /-- It is a morphism over `S'`. -/
  base_comm : hom ≫ Q₂.f' = Q₁.f'
  /-- It is the identity on the prescribed ideal `𝒢`. -/
  kernel_comm :
    Q₂.idealInclusion ≫ SheafOfModules.unitToPushforwardObjUnit (structureSheafHom hom) =
      (pushforwardIsoOfComp Q₁.i hom Q₂.i thickening_comm).hom.app G ≫
        (modulePushforward hom).map Q₁.idealInclusion

namespace SolutionHom

variable {Q₁ Q₂ : DeformationSolution t ht f G c} (e : SolutionHom Q₁ Q₂)

/-- The comorphism `𝒪_{X'₂} ⟶ hom_* 𝒪_{X'₁}` of a morphism of solutions, as a map of sheaves of
`𝒪_{X'₂}`-modules. This is the middle column of the five-lemma square. -/
noncomputable abbrev structureMap :
    SheafOfModules.unit (structureSheafRing Q₂.X') ⟶ (modulePushforward e.hom).obj
      (SheafOfModules.unit (structureSheafRing Q₁.X')) :=
  SheafOfModules.unitToPushforwardObjUnit (structureSheafHom e.hom)

/-- The underlying continuous map of a morphism of solutions is a homeomorphism: it is a factor
of the homeomorphism underlying `Q₂.i` whose other factor, the one underlying `Q₁.i`, is a
homeomorphism as well. -/
lemma isIso_base : IsIso e.hom.hom.base := by
  have h1 : IsIso Q₁.i.hom.base := Q₁.i_firstOrder.1.1
  have hb : Q₁.i.hom.base ≫ e.hom.hom.base = Q₂.i.hom.base :=
    congrArg (fun k : X ⟶ Q₂.X' => k.hom.base) e.thickening_comm
  have h3 : IsIso (Q₁.i.hom.base ≫ e.hom.hom.base) := by
    rw [hb]
    exact Q₂.i_firstOrder.1.1
  exact IsIso.of_isIso_comp_left Q₁.i.hom.base e.hom.hom.base

/-- The right-hand column of the five-lemma square: the identification of `(Q₂.i)_* 𝒪_X` with
`hom_* (Q₁.i)_* 𝒪_X` coming from `Q₁.i ≫ hom = Q₂.i`. It is an isomorphism. -/
noncomputable abbrev quotientComparison :
    (modulePushforward Q₂.i).obj (SheafOfModules.unit (structureSheafRing X)) ⟶
      (modulePushforward e.hom).obj
        ((modulePushforward Q₁.i).obj (SheafOfModules.unit (structureSheafRing X))) :=
  (pushforwardIsoOfComp Q₁.i e.hom Q₂.i e.thickening_comm).hom.app
    (SheafOfModules.unit (structureSheafRing X))

/-- The right-hand square of the five-lemma diagram commutes: the two ways of mapping
`𝒪_{X'₂}` to `hom_* (Q₁.i)_* 𝒪_X` agree. -/
lemma structureMap_comm :
    e.structureMap ≫ (modulePushforward e.hom).map Q₁.structureMap =
      Q₂.structureMap ≫ e.quotientComparison :=
  unitToPushforwardObjUnit_comp Q₁.i e.hom Q₂.i e.thickening_comm

/-- The pushed-forward structure map of `Q₁` is surjective. This is read off the commutative
square — the composite with `e.structureMap` is the surjection of `Q₂` followed by an
isomorphism — and so needs no exactness of the pushforward functor. -/
lemma epi_pushedMap : Epi ((modulePushforward e.hom).map Q₁.structureMap) := by
  have h1 : Epi Q₂.structureMap := Q₂.i_firstOrder.1.2.1
  have h3 : Epi (e.structureMap ≫ (modulePushforward e.hom).map Q₁.structureMap) := by
    rw [structureMap_comm]
    infer_instance
  exact epi_of_epi e.structureMap _

/-- The map from `𝒢`, read as the ideal of `Q₂`, to the kernel of the pushed-forward structure
map of `Q₁`, induced by the comorphism of a morphism of solutions. -/
noncomputable def idealComparison :
    (modulePushforward Q₂.i).obj G ⟶
      kernel ((modulePushforward e.hom).map Q₁.structureMap) :=
  kernel.lift _ (Q₂.idealInclusion ≫ e.structureMap)
    (by rw [Category.assoc, e.structureMap_comm, ← Category.assoc,
      DeformationSolution.idealInclusion_comp_structureMap, zero_comp])

/-- The defining property of `SolutionHom.idealComparison`. -/
lemma idealComparison_comp_ι :
    e.idealComparison ≫ kernel.ι ((modulePushforward e.hom).map Q₁.structureMap) =
      Q₂.idealInclusion ≫ e.structureMap :=
  kernel.lift_ι _ _ _

/-- `SolutionHom.idealComparison` is an isomorphism. This is where the condition that a morphism
of solutions is the identity on `𝒢` is used: the comparison becomes the identification of `𝒢`
with the ideal of `Q₁`, pushed forward and composed with the kernel comparison of the
pushforward, which preserves kernels because it is a right adjoint. -/
lemma isIso_idealComparison : IsIso e.idealComparison := by
  have hra : (modulePushforward e.hom).IsRightAdjoint := modulePushforward_isRightAdjoint e.hom
  have hmc : (modulePushforward e.hom).map Q₁.idealInclusion =
      (modulePushforward e.hom).map Q₁.idealIso.hom ≫
        kernelComparison Q₁.structureMap (modulePushforward e.hom) ≫
          kernel.ι ((modulePushforward e.hom).map Q₁.structureMap) := by
    rw [kernelComparison_comp_ι, ← Functor.map_comp]
  have hι : e.idealComparison ≫ kernel.ι ((modulePushforward e.hom).map Q₁.structureMap) =
      ((pushforwardIsoOfComp Q₁.i e.hom Q₂.i e.thickening_comm).hom.app G ≫
        (modulePushforward e.hom).map Q₁.idealIso.hom ≫
          kernelComparison Q₁.structureMap (modulePushforward e.hom)) ≫
        kernel.ι ((modulePushforward e.hom).map Q₁.structureMap) :=
    ((idealComparison_comp_ι e).trans e.kernel_comm).trans
      ((congrArg (fun k => (pushforwardIsoOfComp Q₁.i e.hom Q₂.i e.thickening_comm).hom.app G ≫ k)
        hmc).trans (comp_assoc₃ _ _ _ _).symm)
  have key := (cancel_mono (kernel.ι ((modulePushforward e.hom).map Q₁.structureMap))).1 hι
  exact key ▸ inferInstance

/-- The left-hand column of the five-lemma square: the map on the two ideals. -/
noncomputable def idealMap :
    kernel Q₂.structureMap ⟶ kernel ((modulePushforward e.hom).map Q₁.structureMap) :=
  Q₂.idealIso.inv ≫ e.idealComparison

/-- The map on ideals is an isomorphism. -/
lemma isIso_idealMap : IsIso e.idealMap := by
  have h := e.isIso_idealComparison
  rw [idealMap]
  infer_instance

/-- The left-hand square of the five-lemma diagram commutes. -/
lemma idealMap_comp_ι :
    e.idealMap ≫ kernel.ι ((modulePushforward e.hom).map Q₁.structureMap) =
      kernel.ι Q₂.structureMap ≫ e.structureMap := by
  rw [idealMap, Category.assoc, idealComparison_comp_ι, ← Category.assoc,
    DeformationSolution.idealIso_inv_comp_idealInclusion]

/-- The comparison of the two ideal rows attached to a morphism of solutions: the ideal row of
`Q₂` maps to the pushforward along `hom` of the ideal row of `Q₁`, by `SolutionHom.idealMap` on
the ideals, the comorphism on the structure sheaves, and `SolutionHom.quotientComparison` on the
quotients. -/
noncomputable def fiveLemmaSquare :
    ShortComplex.mk (kernel.ι Q₂.structureMap) Q₂.structureMap (kernel.condition _) ⟶
      ShortComplex.mk (kernel.ι ((modulePushforward e.hom).map Q₁.structureMap))
        ((modulePushforward e.hom).map Q₁.structureMap) (kernel.condition _) where
  τ₁ := e.idealMap
  τ₂ := e.structureMap
  τ₃ := e.quotientComparison
  comm₁₂ := e.idealMap_comp_ι
  comm₂₃ := e.structureMap_comm

/-- The left column of `SolutionHom.fiveLemmaSquare`. -/
lemma fiveLemmaSquare_τ₁ : e.fiveLemmaSquare.τ₁ = e.idealMap := rfl

/-- The middle column of `SolutionHom.fiveLemmaSquare`. -/
lemma fiveLemmaSquare_τ₂ : e.fiveLemmaSquare.τ₂ = e.structureMap := rfl

/-- The right column of `SolutionHom.fiveLemmaSquare`. -/
lemma fiveLemmaSquare_τ₃ : e.fiveLemmaSquare.τ₃ = e.quotientComparison := rfl

/-- **The short five lemma on the two ideal rows.** The comorphism of a morphism of solutions is
an isomorphism of sheaves of modules: the outer columns of `SolutionHom.fiveLemmaSquare` are
isomorphisms and both rows are short exact, so the middle column is both a monomorphism and an
epimorphism, hence an isomorphism. -/
lemma isIso_structureMap : IsIso e.structureMap := by
  have hra : (modulePushforward e.hom).IsRightAdjoint := modulePushforward_isRightAdjoint e.hom
  have hτ₁ : IsIso e.idealMap := e.isIso_idealMap
  have hg : Epi Q₂.structureMap := Q₂.i_firstOrder.1.2.1
  have hm₁ : Mono e.fiveLemmaSquare.τ₁ := inferInstanceAs (Mono e.idealMap)
  have hm₃ : Mono e.fiveLemmaSquare.τ₃ := inferInstanceAs (Mono e.quotientComparison)
  have he₁ : Epi e.fiveLemmaSquare.τ₁ := inferInstanceAs (Epi e.idealMap)
  have he₃ : Epi e.fiveLemmaSquare.τ₃ := inferInstanceAs (Epi e.quotientComparison)
  have hmono : Mono e.fiveLemmaSquare.τ₂ :=
    ShortComplex.mono_of_mono_of_mono_of_mono e.fiveLemmaSquare
      (ShortComplex.exact_kernel Q₂.structureMap) inferInstance hm₁ hm₃
  have hepi : Epi e.fiveLemmaSquare.τ₂ :=
    ShortComplex.epi_of_epi_of_epi_of_epi e.fiveLemmaSquare
      (ShortComplex.exact_kernel ((modulePushforward e.hom).map Q₁.structureMap)) hg he₁ he₃
  rw [fiveLemmaSquare_τ₂] at hmono hepi
  exact isIso_of_mono_of_epi e.structureMap

/-- The comorphism of a morphism of solutions is an isomorphism of sheaves of rings. The
components of `SolutionHom.structureMap` are the components of the comorphism as maps of sets,
so bijectivity transfers from the one to the other. -/
lemma isIso_c : IsIso e.hom.hom.c := by
  have h := e.isIso_structureMap
  have happ : ∀ U, IsIso (e.hom.hom.c.app U) := fun U => by
    have hF : IsIso ((SheafOfModules.forget (structureSheafRing Q₂.X') ⋙
        PresheafOfModules.evaluation (structureSheafRing Q₂.X').obj U).map e.structureMap) :=
      inferInstance
    have hb : Function.Bijective (e.structureMap.val.app U) :=
      (ConcreteCategory.isIso_iff_bijective _).mp hF
    exact (ConcreteCategory.isIso_iff_bijective _).mpr hb
  exact NatIso.isIso_of_isIso_app _

/-- **A morphism of solutions is automatically an isomorphism of ringed spaces.** Its base map
is a homeomorphism because both thickenings are, and its comorphism is an isomorphism by the
short five lemma on the two ideal rows. -/
lemma isIso_hom : IsIso e.hom := by
  have h1 := e.isIso_base
  have h2 := e.isIso_c
  have : IsIso (SheafedSpace.forgetToPresheafedSpace.map e.hom) :=
    PresheafedSpace.isIso_of_components e.hom.hom
  exact isIso_of_reflects_iso e.hom SheafedSpace.forgetToPresheafedSpace

/-- The identity morphism of a solution. All three conditions hold on the nose: the structure
sheaf map of an identity morphism, the pushforward comparison and the pushforward functor all
leave sections untouched. -/
noncomputable def id (Q : DeformationSolution t ht f G c) : SolutionHom Q Q where
  hom := 𝟙 Q.X'
  thickening_comm := Category.comp_id _
  base_comm := Category.id_comp _
  kernel_comm := by ext U; rfl

end SolutionHom

/-- Two solutions of the deformation problem of Tag 08U7 are isomorphic when some morphism of
solutions between them is invertible as a morphism of ringed spaces. -/
def Isomorphic (Q₁ Q₂ : DeformationSolution t ht f G c) : Prop :=
  ∃ e : SolutionHom Q₁ Q₂, IsIso e.hom

/-- **Stacks Project, Tag 08UC**, the half asserting that the obstruction separates isomorphism
classes. Two solutions of the deformation problem of Tag 08U7 are isomorphic exactly when there
is a morphism of solutions between them: by `SolutionHom.isIso_hom` every morphism of solutions
is already invertible. This is the source's "clearly, this element is the obstruction to the
existence of an isomorphism, hence separates the isomorphism classes" — the obstruction class of
Tag 08U8, which obstructs a *morphism* of solutions, thereby obstructs an isomorphism.

The other half of the tag — that the isomorphism classes form a principal homogeneous space
under `Ext¹_{𝒪_X}(NL_{X/S}, 𝒢)` — is not claimed here; the full statement of the tag is
`exists_addTorsor_solutionClasses` in
`StacksFrontier/Deformation/RingedSpaceThickening/SolutionClassesPrincipalHomogeneous.lean`. -/
@[stacks 08UC "the step of the proof that the obstruction to a morphism of solutions is the \
obstruction to an isomorphism; the full statement is exists_addTorsor_solutionClasses"]
theorem isomorphic_iff_nonempty_solutionHom (Q₁ Q₂ : DeformationSolution t ht f G c) :
    Isomorphic Q₁ Q₂ ↔ Nonempty (SolutionHom Q₁ Q₂) :=
  ⟨fun h => h.elim fun e _ => ⟨e⟩, fun h => h.elim fun e => ⟨e, e.isIso_hom⟩⟩

/-- Every solution is isomorphic to itself. -/
lemma isomorphic_refl (Q : DeformationSolution t ht f G c) : Isomorphic Q Q :=
  (isomorphic_iff_nonempty_solutionHom Q Q).2 ⟨SolutionHom.id Q⟩

end AlgebraicGeometry.RingedSpaceThickening

end
