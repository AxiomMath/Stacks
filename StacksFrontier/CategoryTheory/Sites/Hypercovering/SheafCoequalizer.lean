module

public import StacksFrontier.CategoryTheory.Sites.CoequalizerOfEpi
public import StacksFrontier.CategoryTheory.Sites.Glueing.SheafHomContravariant
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Presheaf

/-!
# The degree-one coequalizer presentation of the final sheaf by a hypercovering

Let `(C, J)` be a site with equalizers and fibre products and let `K` be a hypercovering of the
final presheaf, in the sense of Stacks 09VU. Conditions (1) and (2) of that definition say that
the degree-zero augmentation `F(K_0) ⟶ *` and the degree-one matching map
`F(K_1) ⟶ F(K_0) ×_* F(K_0)` are locally surjective. This file records what the proof of
Stacks 0D8E calls "a coequalizer diagram in sheaves of sets by definition of a hypercovering":

`F(K_1)^# ⇉ F(K_0)^# ⟶ *`

is a coequalizer of sheaves of sets, the two parallel maps being the sheafifications of the two
degree-one face maps. Condition (3) is not used.

Applying `SheafHom(-, G)`, which turns coequalizers into equalizers, presents every sheaf of
sets `G` on `(C, J)` as the equalizer of the two transition maps between the internal homs out of
`F(K_0)^#` and `F(K_1)^#`. That equalizer presentation is the right-hand side of the fork
comparison which the fullness clause of Stacks 0D8E asks for: by Stacks 0D70 (3) the sheaf
`a_* a^{-1} G` is the equalizer of the two degree-one transitions of the component push-pulls,
and by Stacks 0D8B and 0D86 each of those vertices is an internal hom out of `F(K_n)^#`.

## Main results

* `Stacks.CategoryTheory.Hypercovering.isColimitCoforkTerminalOfHypercovering`: **conditions (1)
  and (2) of Stacks 09VU as a coequalizer.** For a hypercovering of the final presheaf the
  diagram `F(K_1)^# ⇉ F(K_0)^# ⟶ *` is a coequalizer of sheaves of sets.
* `Stacks.CategoryTheory.Hypercovering.isLimitForkSheafHomOfHypercovering`: the equalizer
  obtained from it by `SheafHom(-, G)`, with vertex `SheafHom(*, G)`.
* `Stacks.CategoryTheory.Hypercovering.isLimitForkSheafHomOfHypercovering'`: the same equalizer
  with its vertex read as `G` itself, through the identification of the internal hom out of a
  terminal sheaf with the identity functor.

## Implementation notes

`CategoryTheory.Sheaf.isColimitCoforkOfLocallySurjective` is stated with the two parallel maps
spelled as the composites of the matching map with the two projections of the chosen fibre
product, because that is the shape its proof produces. The two face maps of the simplicial
presheaf are *equal* to those composites, by
`Stacks.CategoryTheory.Hypercovering.oneMatchingMap_fst` and `.oneMatchingMap_snd`, but not
definitionally so; `CategoryTheory.Limits.isColimitCofork_congr` transports the colimit along
that equality. The cofork's commutation proof plays no part in the transport, both commutations
being proofs of the same proposition.

The terminality of the augmentation target is proved inline rather than taken from the library.
The only existing statement of it, `Stacks.CategoryTheory.Hypercovering.isTerminal_liftedTerminal`,
lives in a file about representing cohomology classes whose import closure is far larger than
anything used here, and a second named declaration of the same fact would be a shadow of it.

## References

* [Stacks Project, Tag 0D8E](https://stacks.math.columbia.edu/tag/0D8E)
* [Stacks Project, Tag 09VU](https://stacks.math.columbia.edu/tag/09VU)
* [Stacks Project, Tag 0D86](https://stacks.math.columbia.edu/tag/0D86)
* [Stacks Project, Tag 0D70](https://stacks.math.columbia.edu/tag/0D70)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.Limits

/-- **A colimit cofork is a colimit cofork of any equal parallel pair.** The two coforks have the
same projection, and their commutation proofs are proofs of the same proposition. -/
def isColimitCofork_congr {D : Type*} [Category D] {A B Q : D} {f g f' g' : A ⟶ B}
    {h : B ⟶ Q} (hf : f = f') (hg : g = g') {w : f ≫ h = g ≫ h} {w' : f' ≫ h = g' ≫ h}
    (hc : IsColimit (Cofork.ofπ h w)) : IsColimit (Cofork.ofπ h w') := by
  subst hf
  subst hg
  exact hc

end CategoryTheory.Limits

namespace Stacks.CategoryTheory.Hypercovering

variable {C : Type u} [SmallCategory C] [HasEqualizers C] [HasPullbacks C]

/-- The sheafification of the presheaf represented by the semi-representable object in simplicial
degree `n` of a simplicial semi-representable object: the sheaf written `F(K_n)^#` in Stacks
0D8E. -/
abbrev degreeSheafification (J : GrothendieckTopology C)
    (K : SimplicialObject (FormalCoproduct.{u} C)) (n : SimplexCategory) :
    Sheaf J (Type u) :=
  (presheafToSheaf J (Type u)).obj
    ((associatedSimplicialPresheaf.{u} K).obj (op n))

/-- The sheafification of a degree-one face map of the simplicial presheaf of `K`, the map written
`K_1 ⟶ K_0` in the proof of Stacks 0D8E. -/
abbrev faceSheafification (J : GrothendieckTopology C)
    (K : SimplicialObject (FormalCoproduct.{u} C)) (i : Fin 2) :
    degreeSheafification J K (SimplexCategory.mk 1) ⟶
      degreeSheafification J K (SimplexCategory.mk 0) :=
  (presheafToSheaf J (Type u)).map ((associatedSimplicialPresheaf.{u} K).δ i)

omit [HasEqualizers C] [HasPullbacks C] in
/-- The two composites of the two degree-one face maps with the terminal map agree, both being
maps into a terminal object. -/
theorem faceSheafification_comp_terminal_from (J : GrothendieckTopology C)
    (K : SimplicialObject (FormalCoproduct.{u} C)) :
    faceSheafification J K 0 ≫ terminal.from (degreeSheafification J K (SimplexCategory.mk 0)) =
      faceSheafification J K 1 ≫
        terminal.from (degreeSheafification J K (SimplexCategory.mk 0)) :=
  terminal.hom_ext _ _

/-- **Conditions (1) and (2) of Stacks 09VU, as a coequalizer of sheaves of sets.** For a
hypercovering `K` of the final presheaf the diagram

`F(K_1)^# ⇉ F(K_0)^# ⟶ *`

is a coequalizer, the two parallel maps being the sheafifications of the two degree-one face maps
of `K`. This is the assertion the proof of Stacks 0D8E makes "by definition of a hypercovering";
condition (3) is not used.

Condition (1) says that the degree-zero augmentation towards the final presheaf is locally
surjective, and condition (2) that the degree-one matching map into its fibre square is; so
`CategoryTheory.Sheaf.isColimitCoforkOfLocallySurjective` applies, and its two parallel maps are
the two face maps by `oneMatchingMap_fst` and `oneMatchingMap_snd`. -/
def isColimitCoforkTerminalOfHypercovering (P : Pretopology C)
    (H : HypercoveringOfTerminal.{u, u, u} P) :
    IsColimit (Cofork.ofπ
      (terminal.from
        (degreeSheafification P.toGrothendieck H.toSimplicialObject (SimplexCategory.mk 0)))
      (faceSheafification_comp_terminal_from P.toGrothendieck H.toSimplicialObject)) := by
  haveI := H.locallySurjective_zero
  haveI := H.locallySurjective_one
  have hT : IsTerminal
      (liftedPresheaf.{u, u} (⊤_ (Cᵒᵖ ⥤ Type u)) : Cᵒᵖ ⥤ Type u) :=
    terminalIsTerminal.isTerminalObj
      ((Functor.whiskeringRight Cᵒᵖ (Type u) (Type u)).obj uliftFunctor.{u, u}) _
  set m := oneMatchingMap (associatedSimplicialPresheaf.{u} H.toSimplicialObject)
    (liftedPresheaf.{u, u} (⊤_ (Cᵒᵖ ⥤ Type u))) H.augmentation with hm
  have h0 : (presheafToSheaf P.toGrothendieck (Type u)).map
        (m ≫ pullback.fst (H.augmentation.app (op (SimplexCategory.mk 0)))
          (H.augmentation.app (op (SimplexCategory.mk 0)))) =
      faceSheafification P.toGrothendieck H.toSimplicialObject 0 := by
    rw [hm, oneMatchingMap_fst]
  have h1 : (presheafToSheaf P.toGrothendieck (Type u)).map
        (m ≫ pullback.snd (H.augmentation.app (op (SimplexCategory.mk 0)))
          (H.augmentation.app (op (SimplexCategory.mk 0)))) =
      faceSheafification P.toGrothendieck H.toSimplicialObject 1 := by
    rw [hm, oneMatchingMap_snd]
  exact isColimitCofork_congr h0 h1
    (CategoryTheory.Sheaf.isColimitCoforkOfLocallySurjective P.toGrothendieck
      (H.augmentation.app (op (SimplexCategory.mk 0))) hT m)

/-- **The equalizer presentation `SheafHom(-, G)` turns the coequalizer of a hypercovering
into.** For a hypercovering `K` of the final presheaf and a sheaf of sets `G` on `(C, J)` the
internal hom out of the final sheaf is the equalizer of the two transition maps
`SheafHom(F(K_0)^#, G) ⇉ SheafHom(F(K_1)^#, G)`.

This is the last sentence of the first half of the proof of Stacks 0D8E: `SheafHom(-, G)`
transforms coequalizers into equalizers. -/
def isLimitForkSheafHomOfHypercovering (P : Pretopology C)
    (H : HypercoveringOfTerminal.{u, u, u} P) (G : Sheaf P.toGrothendieck (Type u)) :
    IsLimit (Fork.ofι
      ((SheafHomAdj.sheafHomContraMap
        (terminal.from
          (degreeSheafification P.toGrothendieck H.toSimplicialObject
            (SimplexCategory.mk 0)))).app G)
      (show _ = _ by
        rw [← NatTrans.comp_app, ← NatTrans.comp_app,
          ← SheafHomAdj.sheafHomContraMap_comp, ← SheafHomAdj.sheafHomContraMap_comp,
          faceSheafification_comp_terminal_from]) :
      Fork
        ((SheafHomAdj.sheafHomContraMap
          (faceSheafification P.toGrothendieck H.toSimplicialObject 0)).app G)
        ((SheafHomAdj.sheafHomContraMap
          (faceSheafification P.toGrothendieck H.toSimplicialObject 1)).app G)) :=
  SheafHomAdj.isLimitForkSheafHomContraMap _
    (isColimitCoforkTerminalOfHypercovering P H) G

/-- The leg of the equalizer presentation of a sheaf `G` itself: the transition map out of the
internal hom at the final sheaf, read through the identification of `SheafHom(*, -)` with the
identity functor. -/
def sheafHomForkLeg (P : Pretopology C) (H : HypercoveringOfTerminal.{u, u, u} P)
    (G : Sheaf P.toGrothendieck (Type u)) :
    G ⟶ (SheafHomAdj.sheafHomFunctor
      (degreeSheafification P.toGrothendieck H.toSimplicialObject
        (SimplexCategory.mk 0))).obj G :=
  (SheafHomAdj.sheafHomFunctorTerminalIso.app G).inv ≫
    (SheafHomAdj.sheafHomContraMap
      (terminal.from
        (degreeSheafification P.toGrothendieck H.toSimplicialObject
          (SimplexCategory.mk 0)))).app G

/-- **A sheaf of sets is the equalizer of the two degree-one internal-hom transitions of a
hypercovering.** For a hypercovering `K` of the final presheaf every sheaf of sets `G` on
`(C, J)` is the equalizer of

`SheafHom(F(K_0)^#, G) ⇉ SheafHom(F(K_1)^#, G)`,

with the leg `sheafHomForkLeg`. This is `isLimitForkSheafHomOfHypercovering` with its vertex
`SheafHom(*, G)` replaced by `G`, the two being identified by
`CategoryTheory.SheafHomAdj.sheafHomFunctorTerminalIso`. -/
def isLimitForkSheafHomOfHypercovering' (P : Pretopology C)
    (H : HypercoveringOfTerminal.{u, u, u} P) (G : Sheaf P.toGrothendieck (Type u)) :
    IsLimit (Fork.ofι (sheafHomForkLeg P H G)
      (show _ = _ by
        rw [sheafHomForkLeg, Category.assoc, Category.assoc, ← NatTrans.comp_app,
          ← NatTrans.comp_app, ← SheafHomAdj.sheafHomContraMap_comp,
          ← SheafHomAdj.sheafHomContraMap_comp, faceSheafification_comp_terminal_from]) :
      Fork
        ((SheafHomAdj.sheafHomContraMap
          (faceSheafification P.toGrothendieck H.toSimplicialObject 0)).app G)
        ((SheafHomAdj.sheafHomContraMap
          (faceSheafification P.toGrothendieck H.toSimplicialObject 1)).app G)) :=
  IsLimit.ofIsoLimit (isLimitForkSheafHomOfHypercovering P H G)
    (Fork.ext (SheafHomAdj.sheafHomFunctorTerminalIso.app G) (by
      change (SheafHomAdj.sheafHomFunctorTerminalIso.app G).hom ≫
          (SheafHomAdj.sheafHomFunctorTerminalIso.app G).inv ≫
            (SheafHomAdj.sheafHomContraMap
              (terminal.from
                (degreeSheafification P.toGrothendieck H.toSimplicialObject
                  (SimplexCategory.mk 0)))).app G =
        (SheafHomAdj.sheafHomContraMap
          (terminal.from
            (degreeSheafification P.toGrothendieck H.toSimplicialObject
              (SimplexCategory.mk 0)))).app G
      rw [Iso.hom_inv_id_assoc]))

end Stacks.CategoryTheory.Hypercovering

end
