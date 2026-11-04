module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Sites.Abelian
import StacksCore.Tactic.StacksAttribute

/-!
# Sheaves of modules form an abelian category, and forgetting the module structure is exact

Let `R` be a sheaf of rings on a site. The category of sheaves of `R`-modules is abelian, and
the functor to abelian sheaves forgetting the module structure is exact: it preserves kernels
and cokernels, so a short complex of sheaves of modules is exact exactly when its underlying
short complex of abelian sheaves is.

## Main results

* `SheafOfModules.instAbelian` is the abelian structure; it is registered here for Stacks 03DA.
* `Stacks.SheafOfModules.instPreservesFiniteColimitsToSheaf`: the forgetful functor
  `SheafOfModules.toSheaf` preserves finite colimits. Together with Mathlib's finite-limit
  preservation this is exactness of the forgetful functor.
* `Stacks.SheafOfModules.toSheafKernelIso` and `Stacks.SheafOfModules.toSheafCokernelIso`: the
  kernel and the cokernel of a morphism of sheaves of modules are the kernel and the cokernel
  of the underlying morphism of abelian sheaves.
* `Stacks.SheafOfModules.exact_iff_toSheaf_exact`: a short complex of sheaves of modules is
  exact if and only if the underlying short complex of abelian sheaves is.

## Implementation notes

Preservation of finite limits by `SheafOfModules.toSheaf` is already available in Mathlib, so
only the colimit half is proved. The proof transports preservation along the sheafification
functor for presheaves of modules: the composite of `PresheafOfModules.sheafification` with
`SheafOfModules.toSheaf` is isomorphic to a composite of two functors that preserve finite
colimits, and every sheaf of modules is, up to isomorphism, the sheafification of its own
underlying presheaf of modules, the isomorphism being the counit of the sheafification
adjunction.

The correspondence of kernels and cokernels is the comparison isomorphism of a functor that
preserves them, and the correspondence of exactness is Mathlib's
`CategoryTheory.ShortComplex.exact_map_iff_of_faithful` applied to `SheafOfModules.toSheaf R`,
which is faithful. The sheafification hypotheses are the standard size conditions for Mathlib's
abelian categories of abelian sheaves. Everything applies to sheaves of modules over an
arbitrary sheaf of rings, hence in particular over the structure sheaf of a ringed topos.

## References

* [Stacks Project, Tag 03DA](https://stacks.math.columbia.edu/tag/03DA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v v' u u'

namespace Stacks.SheafOfModules

add_to_stacks 03DA "abelian category" SheafOfModules.instAbelian
add_to_sga "3 I 3.1.1" "more general" SheafOfModules.instAbelian
add_to_sga "3 I 4.7.1.1" "more general" SheafOfModules.instAbelian
add_to_sga "4 II 6.7" SheafOfModules.instAbelian
add_to_sga "4 IV 11.1.2" "partial" SheafOfModules.instAbelian
add_to_sga "4 Vbis 2.4.0" "The fibers of Mod(E°" SheafOfModules.instAbelian
add_to_sga "4 XVII 2.2.6" "partial" SheafOfModules.instAbelian
add_to_sga "6 I 1.3" "partial" SheafOfModules.instAbelian

add_to_stacks 03DA "exact forgetful functor"
  SheafOfModules.instPreservesFiniteLimitsSheafAddCommGrpCatToSheaf
add_to_sga "4 V 3.5" "left exactness of M ↦ ℳ"
  SheafOfModules.instPreservesFiniteLimitsSheafAddCommGrpCatToSheaf

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u})

/-- The forgetful functor from sheaves of modules to abelian sheaves preserves finite colimits,
including cokernels. Together with its finite-limit preservation this says the functor is
exact. -/
@[stacks 03DA "exact forgetful functor"]
public noncomputable instance instPreservesFiniteColimitsToSheaf
    [HasSheafify J AddCommGrpCat.{v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{v}] :
    PreservesFiniteColimits (_root_.SheafOfModules.toSheaf.{v} R) := by
  let F := PresheafOfModules.sheafification (𝟙 R.obj)
  have hFG : PreservesFiniteColimits (F ⋙ _root_.SheafOfModules.toSheaf.{v} R) :=
    preservesFiniteColimits_of_natIso
      (PresheafOfModules.sheafificationCompToSheaf (𝟙 R.obj)).symm
  refine ⟨fun K _ _ => ⟨fun {D} => ?_⟩⟩
  let G := _root_.SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)
  have e : (D ⋙ G) ⋙ F ≅ D :=
    (Functor.associator D G F) ≪≫
      Functor.isoWhiskerLeft D
        (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit) ≪≫
      D.rightUnitor
  have : PreservesColimit (D ⋙ G) F := inferInstance
  have : PreservesColimit (D ⋙ G) (F ⋙ _root_.SheafOfModules.toSheaf.{v} R) :=
    (hFG.preservesFiniteColimits K).preservesColimit
  have : PreservesColimit ((D ⋙ G) ⋙ F) (_root_.SheafOfModules.toSheaf.{v} R) :=
    preservesColimit_of_preserves_colimit_cocone
      (isColimitOfPreserves F (colimit.isColimit (D ⋙ G)))
      (isColimitOfPreserves (F ⋙ _root_.SheafOfModules.toSheaf R) (colimit.isColimit (D ⋙ G)))
  exact preservesColimit_of_iso_diagram _ e

section Correspondence

variable [HasSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

/-- Kernels of sheaves of modules correspond to kernels of abelian sheaves: the forgetful
functor carries the kernel of a morphism `f` of sheaves of modules to the kernel of the
underlying morphism of abelian sheaves. -/
@[stacks 03DA "kernels correspond"]
public noncomputable def toSheafKernelIso {M N : _root_.SheafOfModules.{v} R} (f : M ⟶ N) :
    (_root_.SheafOfModules.toSheaf.{v} R).obj (kernel f) ≅
      kernel ((_root_.SheafOfModules.toSheaf.{v} R).map f) :=
  PreservesKernel.iso _ f

/-- Cokernels of sheaves of modules correspond to cokernels of abelian sheaves: the forgetful
functor carries the cokernel of a morphism `f` of sheaves of modules to the cokernel of the
underlying morphism of abelian sheaves. -/
@[stacks 03DA "cokernels correspond"]
public noncomputable def toSheafCokernelIso {M N : _root_.SheafOfModules.{v} R} (f : M ⟶ N) :
    (_root_.SheafOfModules.toSheaf.{v} R).obj (cokernel f) ≅
      cokernel ((_root_.SheafOfModules.toSheaf.{v} R).map f) :=
  PreservesCokernel.iso _ f

/-- Exactness of sheaves of modules corresponds to exactness of abelian sheaves: a short
complex of sheaves of `R`-modules is exact if and only if the underlying short complex of
abelian sheaves is. -/
@[stacks 03DA "exactness corresponds"]
public theorem exact_iff_toSheaf_exact (S : ShortComplex (_root_.SheafOfModules.{v} R)) :
    (S.map (_root_.SheafOfModules.toSheaf.{v} R)).Exact ↔ S.Exact :=
  S.exact_map_iff_of_faithful _

end Correspondence

end Stacks.SheafOfModules

end
