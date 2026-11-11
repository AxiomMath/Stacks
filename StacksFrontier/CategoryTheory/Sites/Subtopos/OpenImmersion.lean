module

public import StacksFrontier.CategoryTheory.Sites.Subtopos.Immersions
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Adjunction.Unique
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Open immersions of topoi, through the pushforward of the localization

For a sheaf `F` on a site `C`, the localization morphism of topoi
`j_F : Sh(C)/F → Sh(C)` has inverse image `j_F⁻¹ = Over.star F : Sh(C) ⥤ Sh(C)/F`,
`G ↦ (F × G → F)`, and pushforward `j_{F,*}` a right adjoint of it. When `F` is a subobject of
the final object, `j_F` is an embedding (Stacks 08LW), and the subtopos `Sh(C)/F` of `Sh(C)`
in the sense of Stacks 08LV is the essential image of `j_{F,*}`. Stacks 08LX calls such a
subcategory an *open subtopos*, and Stacks 08M0(1) calls a morphism of topoi an *open
immersion* when it is an embedding whose pushforward has an open subtopos as essential image.

## Main definitions

* `OpenSubtopos.IsOpenSubtoposOfSlicePushforward`: a strictly full subcategory of `Sh(C)` is
  the essential image of `j_{F,*}` for a subsheaf `F` of the final sheaf.
* `MorphismOfTopoi.IsOpenImmersionOfSlicePushforward`: `f` is an embedding and the essential
  image of `f_*` is such a subcategory (Stacks 08M0(1)).

## Main results

* `OpenSubtopos.isOpenSubtoposOfSlicePushforward_top`: all of `Sh(C)` is an open subtopos, for
  `F` the final sheaf.

## Implementation notes

`OpenSubtopos.IsOpenSubtopos` describes `Sh(C)/F` inside `Sh(C)` as the essential image of
`Over.forget F = j_{F,!}`, the sheaves admitting a map to `F`. That is a different subcategory:
it contains the final sheaf only when `F` is final, so with it `IsOpenImmersion` holds only for
the equivalences of topoi. The definitions here use `j_{F,*}` instead. The pushforward is not
chosen: it enters as a functor `R` with an adjunction `Over.star F ⊣ R`, and right adjoints are
unique up to isomorphism, so its essential image does not depend on the choice.

Part (2) of Stacks 08M0 is `MorphismOfTopoi.IsClosedImmersion`.

Tags covered: 08M0.
-/

@[expose] public section

open CategoryTheory Limits

universe w v u v' u'

namespace OpenSubtopos

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- **Open subtopos, via the pushforward of the localization (Stacks 08LX).**

A strictly full subcategory `E ⊆ Sh(C, J)`, given by the property `P` of its objects, is the
open subtopos `Sh(C)/F` for a subsheaf `F` of the final sheaf: it is the essential image of the
pushforward `j_{F,*} : Sh(C)/F ⥤ Sh(C)` of the localization morphism `j_F`, that is of a right
adjoint `R` of the inverse image `j_F⁻¹ = Over.star F`. -/
def IsOpenSubtoposOfSlicePushforward [HasTerminal (Sheaf J (Type w))]
    [HasBinaryProducts (Sheaf J (Type w))] (P : ObjectProperty (Sheaf J (Type w))) : Prop :=
  ∃ (F : Sheaf J (Type w)) (_ : Mono (terminal.from F))
    (R : Over F ⥤ Sheaf J (Type w)) (_ : Over.star F ⊣ R), R.essImage = P

/-- For a terminal object `T`, `Over.star T` is left adjoint to `Over.forget T`: being right
adjoint to the equivalence `Over.forget T : Over T ≌ D`, it is isomorphic to its inverse. -/
noncomputable def starAdjForgetOfIsTerminal {D : Type u'} [Category.{v'} D]
    [HasBinaryProducts D] {T : D} (hT : IsTerminal T) : Over.star T ⊣ Over.forget T :=
  (Over.equivalenceOfIsTerminal hT).symm.toAdjunction.ofNatIsoLeft
    ((Over.forgetAdjStar T).rightAdjointUniq (Over.equivalenceOfIsTerminal hT).toAdjunction).symm

/-- All of `Sh(C, J)` is an open subtopos: it is the essential image of `j_{F,*}` for `F` the
final sheaf. -/
theorem isOpenSubtoposOfSlicePushforward_top [HasTerminal (Sheaf J (Type w))]
    [HasBinaryProducts (Sheaf J (Type w))] :
    IsOpenSubtoposOfSlicePushforward J (⊤ : ObjectProperty (Sheaf J (Type w))) := by
  refine ⟨⊤_ _, inferInstance, Over.forget _, starAdjForgetOfIsTerminal terminalIsTerminal, ?_⟩
  have : (Over.forget (⊤_ (Sheaf J (Type w)))).EssSurj :=
    (Over.equivalenceOfIsTerminal terminalIsTerminal).essSurj_functor
  ext G
  simpa using Functor.EssSurj.mem_essImage (Over.forget (⊤_ (Sheaf J (Type w)))) G

end OpenSubtopos

namespace MorphismOfTopoi

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}

/-- **Stacks Project, Definition 7.43.7(1) (tag 08M0).**

A morphism of topoi `f : Sh(D, K) → Sh(C, J)` is an *open immersion* if it is an embedding and
the essential image of `f_*` is an open subtopos of `Sh(C, J)`: the essential image of the
pushforward `j_{F,*}` of the localization `j_F : Sh(C)/F → Sh(C)` at a subsheaf `F` of the
final sheaf. Part (2) of the definition is `MorphismOfTopoi.IsClosedImmersion`. -/
@[stacks 08M0 "(1) open immersion; part (2) is MorphismOfTopoi.IsClosedImmersion"]
def IsOpenImmersionOfSlicePushforward
    (f : MorphismOfTopoi (Sheaf K (Type w)) (Sheaf J (Type w))) : Prop :=
  f.IsEmbedding ∧ OpenSubtopos.IsOpenSubtoposOfSlicePushforward J f.pushforward.essImage

end MorphismOfTopoi
