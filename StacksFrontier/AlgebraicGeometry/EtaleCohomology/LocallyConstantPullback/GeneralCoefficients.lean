module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Pullback
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange
import all StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange

/-!
# The inverse image of a constant sheaf is constant, for any coefficient category

Let `F : C ⥤ D` be a continuous functor between sites whose induced pushforward of sheaves has a
left adjoint — the inverse image. If both sites have a final object and `F` carries the one to the
other, then the inverse image carries the constant sheaf on an object of the coefficient category
to the constant sheaf on that same object, hence constant sheaves to constant sheaves.

The proof is by uniqueness of left adjoints and never touches sheafification, so there is no
constraint tying the coefficient category to the sites. Writing `Γ_C` for sections over the final
object of `C`, the constant sheaf functor is left adjoint to `Γ_C`
(`CategoryTheory.constantSheafAdj`), so `C_J ⋙ F⁻¹` is left adjoint to `F_* ⋙ Γ_C`, and the whole
content is the identification `F_* ⋙ Γ_C ≅ Γ_D`. That one is immediate: `F_*` is precomposition
with `F.op`, so sections of `F_* G` over the final object of `C` are sections of `G` over
`F` of that object, and `F` sends it to the final object of `D`.

This generalizes `Stacks.ConstantSheaf.inverseImageConstantSheafIso`, which proves the same
statement for sheaves of sets by a different route — through the corepresentability of sections by
the constant sheaf on a one-element set — and therefore does not apply to sheaves of abelian
groups or of modules. Mathlib records the statement as an open problem: see the `TODO` after
`CategoryTheory.equivCommuteConstant'` in `Mathlib/CategoryTheory/Sites/ConstantSheaf.lean`.

The small étale site of a scheme is the intended application. Base change along a morphism of the
big étale site preserves the final object, so the hypotheses hold there for every coefficient
category, which is what the constructible-sheaf statements of Tags 095E and 09YR need: they range
over an arbitrary concrete category, covering sheaves of sets and of abelian groups at once, and
separately over modules.

## Main results

* `Stacks.ConstantSheaf.pushforwardSectionsIsoOfTerminal` — sections of a pushforward over the
  final object of the source site are sections over the image of that object.
* `Stacks.ConstantSheaf.sheafPullbackConstantSheafIso` — the inverse image of the constant sheaf
  on `E` is the constant sheaf on `E`.
* `Stacks.ConstantSheaf.isConstant_sheafPullback_obj` — the inverse image of a constant sheaf is
  constant.
* `AlgebraicGeometry.smallEtaleSheafPullbackConstantSheafIso` and
  `AlgebraicGeometry.isConstant_smallEtaleSheafPullback` — the same on small étale sites, for the
  inverse image along a morphism of the big étale site.

## Implementation notes

`AlgebraicGeometry.smallEtaleFinalBaseChangeIso` carries `@[no_expose]`. The instance saying that
small étale base change preserves the final object is `private` in
`StacksFrontier/AlgebraicGeometry/Topologies/Etale/SmallEtaleBaseChange.lean`, so it is reached by
an `import all` of that module and may not appear in an exposed definition body; without
`@[no_expose]` the symptom is an ordinary synthesis failure naming `PreservesLimit`. Consumers
still get the isomorphism and every statement about it.

No `@[stacks]` attribute appears in this file. Tag 093R is the assertion for *locally* constant
sheaves; only the constant case is proved here, since the passage to local constancy needs the
localizations of the morphism of topoi. Tag 095A is its specialization to étale sites and is
likewise not proved here.

## References

* [Stacks Project, Tag 093R](https://stacks.math.columbia.edu/tag/093R)
* [Stacks Project, Tag 095A](https://stacks.math.columbia.edu/tag/095A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u v' u' t

namespace Stacks.ConstantSheaf

section General

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (F : C ⥤ D) (A : Type w) [Category.{t} A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [Functor.IsContinuous F J K]

/-- **Sections of a pushforward are sections.** The pushforward along a continuous functor `F` is
precomposition with `F.op`, so the sections of `F_* G` over an object `T` of the source site are
the sections of `G` over `F.obj T`; transported along an isomorphism `F.obj T ≅ T'` this
identifies the two section functors.

No hypothesis is placed on the coefficient category, and none on the pushforward beyond
continuity: this is the step which, for sheaves of sets, was carried out by corepresenting global
sections by the constant sheaf on a one-element set. That is what lets
`Stacks.ConstantSheaf.constantSheafIsoOfPushforward` use it with no adjointness assumption on the
pushforward itself, only an adjoint pair whose right adjoint is isomorphic to it. -/
public def pushforwardSectionsIsoOfTerminal {T : C} {T' : D} (e : F.obj T ≅ T') :
    F.sheafPushforwardContinuous A J K ⋙ (sheafSections J A).obj (op T) ≅
      (sheafSections K A).obj (op T') :=
  NatIso.ofComponents (fun G => (G.obj.mapIso (Iso.op e)).symm)
    (fun φ => (φ.1.naturality (Iso.op e).inv).symm)

variable [(F.sheafPushforwardContinuous A J K).IsRightAdjoint]
  [HasWeakSheafify J A] [HasWeakSheafify K A]

/-- **The inverse image of a constant sheaf is the constant sheaf, in any coefficient category.**
Both `C_J ⋙ F⁻¹` and `C_K` are left adjoint to sections over the final object of `D`, the first by
`Stacks.ConstantSheaf.pushforwardSectionsIsoOfTerminal`, so they agree. -/
public def sheafPullbackConstantSheafIso {T : C} (hT : IsTerminal T) {T' : D}
    (hT' : IsTerminal T') (e : F.obj T ≅ T') :
    constantSheaf J A ⋙ F.sheafPullback A J K ≅ constantSheaf K A :=
  (((constantSheafAdj J A hT).comp (F.sheafAdjunctionContinuous A J K)).ofNatIsoRight
      (pushforwardSectionsIsoOfTerminal F A J K e)).leftAdjointUniq (constantSheafAdj K A hT')

/-- **The inverse image of a constant sheaf is constant, in any coefficient category.** -/
public lemma isConstant_sheafPullback_obj {T : C} (hT : IsTerminal T) {T' : D}
    (hT' : IsTerminal T') (e : F.obj T ≅ T') (G : Sheaf J A) [Sheaf.IsConstant J G] :
    Sheaf.IsConstant K ((F.sheafPullback A J K).obj G) := by
  obtain ⟨E, ⟨eG⟩⟩ := Sheaf.mem_essImage_of_isConstant J G
  exact Sheaf.isConstant_of_iso K
    ((F.sheafPullback A J K).mapIso eG.symm ≪≫
      (sheafPullbackConstantSheafIso F A J K hT hT' e).app E)

end General

end Stacks.ConstantSheaf

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {S T : B.Scheme} (f : T ⟶ S)
  (A : Type w) [Category.{t} A]

/-- Base change along `f : T ⟶ S` carries the final object `S / S` of the small étale site of `S`
to the final object `T / T` of that of `T`: it preserves the final object, and final objects are
unique up to isomorphism. -/
@[no_expose]
public def smallEtaleFinalBaseChangeIso :
    (smallEtaleBaseChange B f).obj (SmallEtale.final B S.obj S.property) ≅
      SmallEtale.final B T.obj T.property :=
  ((SmallEtale.finalIsTerminal B S.obj S.property).isTerminalObj
      (smallEtaleBaseChange B f)).uniqueUpToIso
    (SmallEtale.finalIsTerminal B T.obj T.property)

variable
  [((smallEtaleBaseChange B f).sheafPushforwardContinuous A
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [HasWeakSheafify (SmallEtale.topology B S.obj S.property) A]
  [HasWeakSheafify (SmallEtale.topology B T.obj T.property) A]

/-- **The inverse image along a morphism of schemes of the constant sheaf on `E` is the constant
sheaf on `E`**, on small étale sites and for an arbitrary coefficient category. -/
public def smallEtaleSheafPullbackConstantSheafIso :
    constantSheaf (SmallEtale.topology B S.obj S.property) A ⋙
        (smallEtaleBaseChange B f).sheafPullback A
          (SmallEtale.topology B S.obj S.property)
          (SmallEtale.topology B T.obj T.property) ≅
      constantSheaf (SmallEtale.topology B T.obj T.property) A :=
  Stacks.ConstantSheaf.sheafPullbackConstantSheafIso (smallEtaleBaseChange B f) A
    (SmallEtale.topology B S.obj S.property) (SmallEtale.topology B T.obj T.property)
    (SmallEtale.finalIsTerminal B S.obj S.property)
    (SmallEtale.finalIsTerminal B T.obj T.property)
    (smallEtaleFinalBaseChangeIso B f)

/-- **The inverse image of a constant sheaf is constant**, on small étale sites and for an
arbitrary coefficient category. -/
public lemma isConstant_smallEtaleSheafPullback
    (G : Sheaf (SmallEtale.topology B S.obj S.property) A)
    [Sheaf.IsConstant (SmallEtale.topology B S.obj S.property) G] :
    Sheaf.IsConstant (SmallEtale.topology B T.obj T.property)
      (((smallEtaleBaseChange B f).sheafPullback A
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).obj G) :=
  Stacks.ConstantSheaf.isConstant_sheafPullback_obj (smallEtaleBaseChange B f) A
    (SmallEtale.topology B S.obj S.property) (SmallEtale.topology B T.obj T.property)
    (SmallEtale.finalIsTerminal B S.obj S.property)
    (SmallEtale.finalIsTerminal B T.obj T.property)
    (smallEtaleFinalBaseChangeIso B f) G

end AlgebraicGeometry

end
