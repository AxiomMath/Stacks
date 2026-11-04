module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Whiskering
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A morphism into a coproduct of sheaves is epi as soon as each summand is locally in its image

A coproduct of sheaves is the sheafification of the coproduct of the underlying presheaves, so a
section of it over an object is only *locally* a finite sum of sections of the summands. Showing
that a morphism `d : F ⟶ ∐ G` is surjective therefore looks as though it needs that local
description: one would read an arbitrary section as a finite sum, lift each summand, and add.

It does not. This file proves that `d` is an epimorphism as soon as, for each index `i`, each
object `U` and each section `t` of the summand `G i` over `U`, the *single* section
`(Sigma.ι G i).app U t` is locally in the set-theoretic image of `d`. Neither the passage from a
section of the coproduct to a finite family of sections of the summands, nor the closure of the
local image under addition, is needed.

The reason is that an epimorphism out of a coproduct is tested on the summands. To prove `d` epi
one takes `f, g : ∐ G ⟶ Z` with `d ≫ f = d ≫ g` and must show `f = g`; by the universal property
of the coproduct it suffices that `Sigma.ι G i ≫ f = Sigma.ι G i ≫ g` for each `i`, and that is an
equality of morphisms out of a *summand*, so only the sections of the summands are ever named. Each
such equality is checked section by section, where the target being a sheaf is used exactly once:
two of its sections that agree on a covering sieve are equal
(`CategoryTheory.Sheaf.isSeparated`), and the covering sieve is the one on which the section of the
summand lifts along `d`.

## Main results

* `CategoryTheory.Sheaf.epi_of_forall_imageSieve_ι_mem`: **a morphism into a coproduct of sheaves
  is an epimorphism as soon as every section of every summand is locally in its image.**
* `CategoryTheory.Presheaf.imageSieve_mem_of_isCoverDense`: **a section is locally in the image as
  soon as its restrictions to the objects of a cover-dense subsite are**, so the hypothesis above
  need only be checked on a dense subsite.
* `CategoryTheory.Sheaf.epi_of_forall_imageSieve_ι_mem_of_isCoverDense`: the two combined — the
  epimorphism is tested on the summands *and* on a dense subsite.

## Implementation notes

The hypothesis is stated with `CategoryTheory.Presheaf.imageSieve`, the sieve of arrows along which
a section restricts into the set-theoretic image, so it is literally the condition
`CategoryTheory.Presheaf.IsLocallySurjective` would impose — but imposed only on the sections of the
summands, which is strictly weaker than imposing it on the sections of the coproduct, and is what
the geometry producing such a `d` actually supplies.

Separatedness of the target is where the coefficient category has to be concrete and the topology
has to admit composition with the forgetful functor, which is the hypothesis
`CategoryTheory.GrothendieckTopology.HasSheafCompose`. Nothing else about the coefficients is used:
no abelian structure, no sheafification, no colimits beyond the coproduct that is named in the
statement.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w w' v₂ u₂ v u v₁ u₁

namespace CategoryTheory.Presheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {A : Type u₂}
  [Category.{v₂} A] {FA : A → A → Type*} {CA : A → Type w'}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w'} A FA]

/-- **A section is locally in the image of a morphism of presheaves as soon as its restrictions to
the objects of a cover-dense subsite are.** For `H : C' ⥤ C` cover dense for `J`, a section `s` of
`G` over `U` has `CategoryTheory.Presheaf.imageSieve f s` covering as soon as, for every object
`V` of `C'` and every arrow `g : H.obj V ⟶ U`, the restriction of `s` along `g` is locally in the
image.

The objects of `C'` cover `U` through arrows that factor as `lift ≫ map` with
`map : H.obj V ⟶ U`, so `CategoryTheory.GrothendieckTopology.transitive` reduces the sieve at `U`
to its pullbacks along those arrows, and `CategoryTheory.Presheaf.pullback_imageSieve` identifies
the pullback of an image sieve with the image sieve of the restricted section. -/
@[sga "3 IV 4.2.3" "special case"]
theorem imageSieve_mem_of_isCoverDense {C' : Type u₁} [Category.{v₁} C'] (H : C' ⥤ C)
    [H.IsCoverDense J] {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) {U : C} (s : ToType (G.obj (op U)))
    (h : ∀ (V : C') (g : H.obj V ⟶ U), imageSieve f (G.map g.op s) ∈ J (H.obj V)) :
    imageSieve f s ∈ J U := by
  refine J.transitive (H.is_cover_of_isCoverDense J U) _ fun W k hk => ?_
  obtain ⟨⟨V, lift, map, fac⟩⟩ := hk
  rw [← fac, Sieve.pullback_comp, pullback_imageSieve]
  exact J.pullback_stable lift (h V map)

end CategoryTheory.Presheaf

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {A : Type u₂}
  [Category.{v₂} A] {FA : A → A → Type*} {CA : A → Type w'}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w'} A FA]
  [J.HasSheafCompose (forget A)] {I : Type w} (G : I → Sheaf J A) [HasCoproduct G]
  {F : Sheaf J A}

/-- **A morphism into a coproduct of sheaves is an epimorphism as soon as every section of every
summand is locally in its image.** If for each index `i`, each object `U` and each section `t` of
the summand `G i` over `U` the section `(Sigma.ι G i).app U t` of the coproduct restricts into the
image of `d` along the arrows of a covering sieve, then `d` is epi.

No local description of the sections of the coproduct is involved: `d ≫ f = d ≫ g` is turned into
`f = g` by the universal property of the coproduct, which reduces it to the summands, and there the
hypothesis applies directly. The sheaf condition on the target enters only as its separatedness,
`CategoryTheory.Sheaf.isSeparated`. -/
theorem epi_of_forall_imageSieve_ι_mem (d : F ⟶ ∐ G)
    (h : ∀ (i : I) (U : C) (t : ToType ((G i).obj.obj (op U))),
      Presheaf.imageSieve d.hom ((Sigma.ι G i).hom.app (op U) t) ∈ J U) :
    Epi d := by
  have hcomp : ∀ {X Y W : Sheaf J A} (a : X ⟶ Y) (ψ : Y ⟶ W) (U : Cᵒᵖ) (x : ToType (X.obj.obj U)),
      (a ≫ ψ).hom.app U x = ψ.hom.app U (a.hom.app U x) := fun a ψ U x =>
    ConcreteCategory.comp_apply (a.hom.app U) (ψ.hom.app U) x
  refine ⟨fun {Z} f g hfg => ?_⟩
  refine Sigma.hom_ext _ _ fun i => Sheaf.hom_ext (NatTrans.ext (funext fun U =>
    ConcreteCategory.hom_ext _ _ fun t => ?_))
  rw [hcomp, hcomp]
  refine Z.isSeparated U.unop _ (h i U.unop t) _ _ fun Y k ⟨a, ha⟩ => ?_
  rw [← NatTrans.naturality_apply f.hom k.op, ← NatTrans.naturality_apply g.hom k.op, ← ha,
    ← hcomp d f, ← hcomp d g, hfg]

/-- **A morphism into a coproduct of sheaves is an epimorphism as soon as every section of every
summand over an object of a cover-dense subsite is locally in its image.** This is
`CategoryTheory.Sheaf.epi_of_forall_imageSieve_ι_mem` with its hypothesis checked only at the
objects in the image of a cover-dense functor `H`, which is where the geometry producing such a
`d` can compute the components of `d`.

Two reductions are at work and neither involves the sections of the coproduct: the summands,
because an epimorphism out of a coproduct is tested on them, and the dense subsite, by
`CategoryTheory.Presheaf.imageSieve_mem_of_isCoverDense`. Passing from an arbitrary object to one
of the subsite is the naturality of the summand inclusion, which carries the restriction of
`(Sigma.ι G i).app U t` to the section attached to the restriction of `t`. -/
@[sga "4 II 5.1" "partial"]
theorem epi_of_forall_imageSieve_ι_mem_of_isCoverDense {C' : Type u₁} [Category.{v₁} C']
    (H : C' ⥤ C) [H.IsCoverDense J] (d : F ⟶ ∐ G)
    (h : ∀ (i : I) (V : C') (t : ToType ((G i).obj.obj (op (H.obj V)))),
      Presheaf.imageSieve d.hom ((Sigma.ι G i).hom.app (op (H.obj V)) t) ∈ J (H.obj V)) :
    Epi d :=
  epi_of_forall_imageSieve_ι_mem G d fun i U t =>
    Presheaf.imageSieve_mem_of_isCoverDense H d.hom _ fun V g => by
      rw [← NatTrans.naturality_apply (Sigma.ι G i).hom g.op t]
      exact h i V ((G i).obj.map g.op t)

end CategoryTheory.Sheaf

end
