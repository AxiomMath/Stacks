module

public import StacksFrontier.CategoryTheory.Sites.Subtopos.Open
public import StacksFrontier.CategoryTheory.Sites.Subtopos.Closed
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Open and closed immersions of topoi

## Main definitions

* `MorphismOfTopoi.IsOpenImmersion`: a morphism of topoi is an *open immersion* when it is an
  embedding whose essential image is an open subtopos (Stacks 08M0(1)).
* `MorphismOfTopoi.IsClosedImmersion`: a morphism of topoi is a *closed immersion* when it is
  an embedding whose essential image is a closed subtopos (Stacks 08M0(2)).

Tags covered: 08M0.
-/

@[expose] public section

open CategoryTheory

universe w v u v' u'

namespace MorphismOfTopoi

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}

/-- **Stacks Project, Definition 7.43.7(1) (tag 08M0).**

A morphism of topoi `f : Sh(D, K) → Sh(C, J)` is an *open immersion* if it is an embedding and
the essential image of `f_*` is an open subtopos of `Sh(C, J)`. -/
@[stacks 08M0, sga "4 IV 9.2.1" "open embedding def"]
def IsOpenImmersion (f : MorphismOfTopoi (Sheaf K (Type w)) (Sheaf J (Type w))) : Prop :=
  f.IsEmbedding ∧ OpenSubtopos.IsOpenSubtopos J f.pushforward.essImage

/-- **Stacks Project, Definition 7.43.7(2) (tag 08M0).**

A morphism of topoi `f : Sh(D, K) → Sh(C, J)` is a *closed immersion* if it is an embedding and
the essential image of `f_*` is a closed subtopos of `Sh(C, J)`. -/
@[stacks 08M0, sga "4 IV 9.3.5" "closed embedding"]
def IsClosedImmersion (f : MorphismOfTopoi (Sheaf K (Type w)) (Sheaf J (Type w))) : Prop :=
  f.IsEmbedding ∧ IsClosedSubtopos J f.pushforward.essImage

end MorphismOfTopoi
