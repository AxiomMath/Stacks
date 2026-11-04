module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.BaseChange
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
public import StacksFrontier.CategoryTheory.Sites.Localization.Relocalize

/-!
# A representable group algebraic space is a group scheme

A group object of presheaves over the representable presheaf `h_E` of an object `E` of the big
fppf site over `S`, whose underlying object is represented by an object `Y` of the site over
`E`, makes the scheme of `Y` a group scheme over the scheme of `E`. A group algebraic space over
the terminal presheaf is a group object of presheaves, and restriction along a morphism
`T ⟶ S` of the site carries group objects of presheaves to group objects of presheaves.

## Main definitions

* `AlgebraicGeometry.Space.presheafGrp`: a group object over the terminal presheaf, read as a
  group object of presheaves.
* `AlgebraicGeometry.Space.relocalizeRestrictGrp`: the restriction of a group object of
  presheaves along a morphism of the site.
* `AlgebraicGeometry.Space.grpOverOfIso`: the group scheme over the scheme of `E` given by a group
  object of presheaves over `h_E` together with a representing object of its underlying object.

## Implementation notes

All three constructions are `CategoryTheory.Functor.mapGrp` or its fully faithful inverse
`CategoryTheory.Functor.FullyFaithful.grpObj`, for functors preserving finite products: the
forgetful functor from the slice over a terminal object, restriction along `Over.map f`, the
Yoneda embedding of the slice over `E`, and the inclusion of the slice of the site over `E` into
the slice of all schemes over the scheme of `E`, which preserves finite products because the
inclusion of the site into schemes preserves pullbacks. No group law is written down by hand.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] Over.cartesianMonoidalCategory

variable (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)

/-- The forgetful functor from presheaves over the terminal presheaf preserves finite products:
it is an equivalence. -/
instance preservesFiniteProducts_overForget_terminal :
    PreservesFiniteProducts (Over.forget (yoneda.obj (⊤_ (BigFppfOver C S hS)))) := by
  have : (Over.forget (yoneda.obj (⊤_ (BigFppfOver C S hS)))).IsEquivalence :=
    (Over.equivalenceOfIsTerminal
      (terminalIsTerminal.isTerminalObj yoneda (⊤_ (BigFppfOver C S hS)))).isEquivalence_functor
  infer_instance

/-- A group object over the terminal presheaf of the big fppf site over `S`, read as a group
object of presheaves. -/
noncomputable def presheafGrp (G : Grp (Over (yoneda.obj (⊤_ (BigFppfOver C S hS))))) :
    Grp ((BigFppfOver C S hS)ᵒᵖ ⥤ Type u) :=
  letI := Functor.Monoidal.ofChosenFiniteProducts
    (Over.forget (yoneda.obj (⊤_ (BigFppfOver C S hS))))
  (Over.forget _).mapGrp.obj G

/-- The underlying presheaf of `presheafGrp C S hS G` is the source of the underlying object of
`G`. -/
@[simp]
theorem presheafGrp_X (G : Grp (Over (yoneda.obj (⊤_ (BigFppfOver C S hS))))) :
    (presheafGrp C S hS G).X = G.X.left :=
  rfl

/-- The restriction of a group object of presheaves on the site over `S` along a morphism
`f : T ⟶ S` of the site. -/
noncomputable def relocalizeRestrictGrp {T : Scheme.{u}} {hT : C.Contains T}
    (f : C.obj hT ⟶ C.obj hS) (P : Grp ((BigFppfOver C S hS)ᵒᵖ ⥤ Type u)) :
    Grp ((BigFppfOver C T hT)ᵒᵖ ⥤ Type u) :=
  letI := Functor.Monoidal.ofChosenFiniteProducts (OverShriek.relocalizeRestrict f)
  (OverShriek.relocalizeRestrict f).mapGrp.obj P

/-- The underlying presheaf of `relocalizeRestrictGrp C S hS f P` is the restriction along `f` of
the underlying presheaf of `P`. -/
@[simp]
theorem relocalizeRestrictGrp_X {T : Scheme.{u}} {hT : C.Contains T}
    (f : C.obj hT ⟶ C.obj hS) (P : Grp ((BigFppfOver C S hS)ᵒᵖ ⥤ Type u)) :
    (relocalizeRestrictGrp C S hS f P).X = (OverShriek.relocalizeRestrict f).obj P.X :=
  rfl

/-- The inclusion of the slice of the site over an object `E` into the slice of all schemes over
the underlying scheme of `E` preserves finite products: binary products are fibre products over
`E`, which the inclusion of the site preserves. -/
instance preservesFiniteProducts_overPost_toScheme (E : BigFppfOver C S hS) :
    PreservesFiniteProducts (Over.post (X := E) (BigFppfOver.toScheme C S hS)) := by
  have : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme C S hS) := by
    dsimp [BigFppfOver.toScheme]
    infer_instance
  have : PreservesLimitsOfShape (WithTerminal (Discrete WalkingPair))
      (BigFppfOver.toScheme C S hS) :=
    PreservesLimitsOfShape.ofWidePullbacks
  have : PreservesLimitsOfShape (Discrete WalkingPair)
      (Over.post (X := E) (BigFppfOver.toScheme C S hS)) :=
    PreservesLimitsOfShape.overPost
  have : PreservesLimit (Functor.empty.{0} (Over E))
      (Over.post (X := E) (BigFppfOver.toScheme C S hS)) :=
    preservesTerminal_of_iso _
      (((Over.post (BigFppfOver.toScheme C S hS)).mapIso
          (terminalIsoIsTerminal Over.mkIdTerminal)) ≪≫
        (terminalIsoIsTerminal Over.mkIdTerminal).symm)
  have : PreservesLimitsOfShape (Discrete PEmpty.{1})
      (Over.post (X := E) (BigFppfOver.toScheme C S hS)) :=
    preservesLimitsOfShape_pempty_of_preservesTerminal _
  exact PreservesFiniteProducts.of_preserves_binary_and_terminal _

/-- The Yoneda embedding of the slice of the site over `E` into presheaves over `h_E` preserves
finite products. -/
instance preservesFiniteProducts_overPost_yoneda (E : BigFppfOver C S hS) :
    PreservesFiniteProducts (Over.post (X := E) (yoneda (C := BigFppfOver C S hS))) := by
  have : PreservesLimitsOfShape (WithTerminal (Discrete WalkingPair))
      (yoneda (C := BigFppfOver C S hS)) := inferInstance
  have : PreservesLimitsOfShape (Discrete WalkingPair)
      (Over.post (X := E) (yoneda (C := BigFppfOver C S hS))) :=
    PreservesLimitsOfShape.overPost
  have : PreservesLimitsOfShape (WithTerminal (Discrete PEmpty.{1}))
      (yoneda (C := BigFppfOver C S hS)) := inferInstance
  have : PreservesLimitsOfShape (Discrete PEmpty.{1})
      (Over.post (X := E) (yoneda (C := BigFppfOver C S hS))) :=
    PreservesLimitsOfShape.overPost
  exact PreservesFiniteProducts.of_preserves_binary_and_terminal _

/-- **A representable group algebraic space is a group scheme.** Let `E` be an object of the big
fppf site over `S` and let `𝒢` be a group object of presheaves over `h_E`. If its underlying
object is represented by an object `Y` of the site over `E`, then `Y`, read as a scheme over the
underlying scheme of `E`, is a group scheme over it. -/
noncomputable def grpOverOfIso (E : BigFppfOver C S hS) (𝒢 : Grp (Over (yoneda.obj E)))
    (Y : Over E) (e : (Over.post yoneda).obj Y ≅ 𝒢.X) :
    Grp (Over ((BigFppfOver.toScheme C S hS).obj E)) :=
  letI := Functor.Monoidal.ofChosenFiniteProducts
    (Over.post (X := E) (yoneda (C := BigFppfOver C S hS)))
  letI : GrpObj ((Over.post yoneda).obj Y) := .ofIso e.symm
  letI : GrpObj Y := (Functor.FullyFaithful.ofFullyFaithful (Over.post yoneda)).grpObj Y
  letI := Functor.Monoidal.ofChosenFiniteProducts
    (Over.post (X := E) (BigFppfOver.toScheme C S hS))
  (Over.post (BigFppfOver.toScheme C S hS)).mapGrp.obj (Grp.mk Y)

/-- The underlying scheme over the scheme of `E` of `grpOverOfIso C S hS E 𝒢 Y e` is `Y`, read as
a scheme over the scheme of `E`. -/
@[simp]
theorem grpOverOfIso_X (E : BigFppfOver C S hS) (𝒢 : Grp (Over (yoneda.obj E)))
    (Y : Over E) (e : (Over.post yoneda).obj Y ≅ 𝒢.X) :
    (grpOverOfIso C S hS E 𝒢 Y e).X = (Over.post (BigFppfOver.toScheme C S hS)).obj Y :=
  rfl

end AlgebraicGeometry.Space

end
