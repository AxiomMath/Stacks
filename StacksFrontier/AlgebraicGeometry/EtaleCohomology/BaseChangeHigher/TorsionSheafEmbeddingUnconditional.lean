module
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.TorsionSheafEmbedding
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.TorsionSheafEmbedding

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.LadderAssembly
public import StacksFrontier.AlgebraicGeometry.SheafifyCommRing.Basic
public import StacksFrontier.AlgebraicGeometry.SheafifyCommRing.BasicUnconditional
public import StacksFrontier.CategoryTheory.Sites.Modules.Colimits
public import StacksFrontier.CategoryTheory.Sites.Modules.TorsionSheavesAsZModModules

/-!
# TorsionSheafEmbeddingUnconditional

Stronger forms of declarations of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.TorsionSheafEmbedding`, stated as
separate declarations beside the ones there: over more general coefficient universes, or with
inputs that are carried there as hypotheses discharged, together with the new results built on
them.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Cohomology.ZModSheaf

universe u w

namespace Stacks.Cohomology.BaseChange

end Stacks.Cohomology.BaseChange

namespace Stacks.EtaleCohomology

section RingSheaf

variable (T : Scheme.{u}) (n : ℤ)

/-- Sheafification of presheaves of commutative rings on the small étale site of a scheme, with
rings in any universe `w` containing the objects of the site, inverts exactly the locally
bijective maps. Stating the universe as a variable constrained by `UnivLE` rather than as a
`max` lets instance search find it at `u + 1` itself. -/
public instance wEqualsLocallyBijective_commRingCat_smallEtale_general [UnivLE.{u + 1, w}] :
    (smallEtaleTopology T).WEqualsLocallyBijective CommRingCat.{w} :=
  have h := (essentiallySmall_iff.{u + 1} T.Etale).1 inferInstance
  have hS : Small.{w} (Skeleton T.Etale) := @Small.trans_univLE _ h.1 _
  have : UnivLE.{u, w} := @UnivLE.trans UnivLE.succ.{u, u} ‹_›
  have : EssentiallySmall.{w} T.Etale :=
    (essentiallySmall_iff.{w} T.Etale).2 ⟨hS, locallySmall_of_univLE _⟩
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, w, u + 1, w + 1, w} _

end RingSheaf

section Embedding

variable {T : Scheme.{u}} {n : ℤ} (F : Sheaf (smallEtaleTopology T) Ab.{u + 1})
  (hF : ∀ (U : T.Etale) (x : F.obj.obj (op U)), n • x = 0)

end Embedding

section Assertions

variable {X S S' X' T Y : Scheme.{u}} (f : X ⟶ S) (n : ℤ) (q : ℕ)
  (s : S' ⟶ S) (p : X' ⟶ X) (f' : X' ⟶ S') (g : T ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T)

end Assertions

end Stacks.EtaleCohomology

end
