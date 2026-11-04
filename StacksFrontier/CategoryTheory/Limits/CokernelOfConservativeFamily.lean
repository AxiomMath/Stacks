module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A cokernel detected by a conservative family of functors

A cofork `b : P ⟶ N` of `a : Q ⟶ P` is a cokernel of `a` exactly when the canonical comparison
map `cokernel a ⟶ N` is an isomorphism.  Being an isomorphism is a condition that a *family* of
functors can detect even when no single member of the family detects it, and each member of the
family only has to be told that it carries `b` to a cokernel — provided it carries the cokernel
of `a` to a cokernel at all.

That is what this file proves.  It is the step a local-to-global argument takes when a cokernel
of sheaves on a site has to be recognised from its restrictions along a family of functors of
sites which is jointly conservative but in which no single restriction reflects anything: the
restrictions are left adjoints, so they preserve the cokernel of `a` for free, and the family is
conservative because a morphism of sheaves is an isomorphism as soon as it is one on every
section.

## Main results

* `CategoryTheory.Limits.isIso_map_cokernelDesc_of_isColimit` — **one functor which preserves the
  cokernel of `a` and carries `b` to a cokernel carries the comparison map `cokernel a ⟶ N` to an
  isomorphism.**
* `CategoryTheory.Limits.isColimitCokernelCoforkOfConservativeFamily` — **a cofork is a cokernel
  as soon as a jointly conservative family of functors, each preserving the cokernel of `a`,
  carries it to a cokernel.**

## Implementation notes

The hypothesis of joint conservativity is taken as a plain `∀`-statement rather than as a class:
the family is indexed by an arbitrary type and its members land in categories which may differ
from one index to the next, so there is no single functor whose
`CategoryTheory.Functor.ReflectsIsomorphisms` instance could carry the information.

Preservation of the cokernel of `a` is asked for as
`CategoryTheory.Limits.PreservesColimit (parallelPair a 0)`, which is what a functor that
preserves colimits of this shape supplies, and the hypothesis that the image of `b` is a cokernel
is phrased with `CategoryTheory.Limits.CokernelCofork.ofπ` so that it matches the conclusion of
`CategoryTheory.Limits.isColimitCoforkMapOfIsColimit'`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v v' u u'

namespace CategoryTheory.Limits

variable {D : Type u} [Category.{v} D] [HasZeroMorphisms D] {Q P N : D} {a : Q ⟶ P} {b : P ⟶ N}

section Single

variable {E : Type u'} [Category.{v'} E] [HasZeroMorphisms E]

/-- **A functor which preserves the cokernel of `a` and carries `b` to a cokernel of the image of
`a` carries the comparison map `cokernel a ⟶ N` to an isomorphism.**  The image of the cokernel
projection of `a` is then a cokernel projection as well, and two cokernels of one morphism are
identified by the unique map between them; that map is the image of the comparison map, the image
of the cokernel projection being an epimorphism. -/
theorem isIso_map_cokernelDesc_of_isColimit (hab : a ≫ b = 0) [HasCokernel a] (G : D ⥤ E)
    [G.PreservesZeroMorphisms] [PreservesColimit (parallelPair a 0) G]
    (hb : IsColimit (CokernelCofork.ofπ (G.map b)
      (show G.map a ≫ G.map b = 0 by rw [← G.map_comp, hab, G.map_zero]))) :
    IsIso (G.map (cokernel.desc a b hab)) := by
  have hGπ : IsColimit (CokernelCofork.ofπ (G.map (cokernel.π a))
      (show G.map a ≫ G.map (cokernel.π a) = 0 by
        rw [← G.map_comp, cokernel.condition, G.map_zero])) :=
    isColimitCoforkMapOfIsColimit' G (cokernel.condition a) (cokernelIsCokernel a)
  have hfac : G.map (cokernel.π a) ≫ (hGπ.coconePointUniqueUpToIso hb).hom = G.map b :=
    hGπ.comp_coconePointUniqueUpToIso_hom hb WalkingParallelPair.one
  have hepi : Epi (G.map (cokernel.π a)) := Cofork.IsColimit.epi hGπ
  have hdesc : G.map (cokernel.desc a b hab) = (hGπ.coconePointUniqueUpToIso hb).hom := by
    rw [← cancel_epi (G.map (cokernel.π a)), hfac, ← G.map_comp, cokernel.π_desc]
  rw [hdesc]
  infer_instance

end Single

section Family

variable {ι : Type w} {E : ι → Type u'} [∀ i, Category.{v'} (E i)] [∀ i, HasZeroMorphisms (E i)]

/-- **A cofork is a cokernel as soon as a jointly conservative family of functors, each of which
preserves the cokernel of `a`, carries it to a cokernel.**  Each member of the family carries the
comparison map `cokernel a ⟶ N` to an isomorphism by
`CategoryTheory.Limits.isIso_map_cokernelDesc_of_isColimit`, so conservativity makes the
comparison map itself an isomorphism, and the cokernel of `a` transports along it. -/
@[sga "4 I 6.2" "(v), special case"]
noncomputable def isColimitCokernelCoforkOfConservativeFamily (hab : a ≫ b = 0) [HasCokernel a]
    (G : ∀ i, D ⥤ E i) [∀ i, (G i).PreservesZeroMorphisms]
    [∀ i, PreservesColimit (parallelPair a 0) (G i)]
    (hG : ∀ ⦃X Y : D⦄ (f : X ⟶ Y), (∀ i, IsIso ((G i).map f)) → IsIso f)
    (hb : ∀ i, IsColimit (CokernelCofork.ofπ ((G i).map b)
      (show (G i).map a ≫ (G i).map b = 0 by
        rw [← (G i).map_comp, hab, (G i).map_zero]))) :
    IsColimit (CokernelCofork.ofπ b hab) :=
  have : IsIso (cokernel.desc a b hab) :=
    hG _ fun i ↦ isIso_map_cokernelDesc_of_isColimit hab (G i) (hb i)
  IsColimit.ofIsoColimit (cokernelIsCokernel a)
    (Cofork.ext (asIso (cokernel.desc a b hab)) (by simp))

end Family

end CategoryTheory.Limits

end
