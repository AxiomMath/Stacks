module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.GeneralCoefficients
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SliceEquivalence
public import StacksFrontier.CategoryTheory.Sites.Localization.PushforwardAdjunction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The slice equivalence on sheaves: restriction to a localized site is inverse image

Let `B` be a big étale site, `X` an object of it and `V` an object of the small étale site of
`X`, with structure morphism `v : V ⟶ X`. The slice equivalence
`AlgebraicGeometry.smallEtaleEquivalenceOver` identifies the small étale site of the scheme `V`
with the localization of the small étale site of `X` at `V`. This file carries that
identification to sheaves, with the consequence that matters for local constancy:

> a sheaf on the small étale site of `X` becomes the constant sheaf on `E` after restriction to
> the localized site at `V` **if and only if** its inverse image along `v` becomes the constant
> sheaf on `E` on the small étale site of the scheme `V`.

The left-hand condition is the one appearing in the definitions of
`Stacks.ConstantSheaf.IsLocallyConstant`, `Stacks.ConstantSheaf.IsFiniteLocallyConstant` and
`Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant`; the right-hand one is the one to which the
identity and composition laws of inverse image (`AlgebraicGeometry.smallEtaleSheafPullbackIdIso`,
`AlgebraicGeometry.smallEtaleSheafPullbackCompIso`) and the preservation of constant sheaves
(`AlgebraicGeometry.isConstant_smallEtaleSheafPullback`) apply.

Three steps make up the identification, and the first two are general facts about an equivalence
of sites rather than about étale morphisms, so they are stated for an arbitrary one.

* Sheafification transports: a site equivalent to one admitting weak sheafification admits weak
  sheafification. This is needed because the coefficient hypotheses available in the
  constructibility statements are weak sheafification on the *localized* sites only.
* The constant sheaf functor transports: restriction along the functor of an equivalence of
  sites carries the constant sheaf on `E` to the constant sheaf on `E`. Both sides are left
  adjoint to sections over a final object, the comparison of the two sections functors being
  `Stacks.ConstantSheaf.pushforwardSectionsIsoOfTerminal`.
* Restriction to the localized site at `V`, transported along the slice equivalence, is
  restriction along `AlgebraicGeometry.smallEtalePostcompose` — an equality of functors, since
  `AlgebraicGeometry.smallEtaleEquivalenceOver_restriction` is one — and that restriction is the
  inverse image along `v`, because composition with `v` is left adjoint to base change along `v`.

## Main results

* `CategoryTheory.hasWeakSheafify_of_equivalence` — weak sheafification transports along an
  equivalence of sites.
* `CategoryTheory.constantSheafSheafCongrInverseIso` — the constant sheaf functor commutes with
  the inverse of the equivalence of sheaf categories induced by an equivalence of sites.
* `AlgebraicGeometry.smallEtalePostcomposeBaseChangeAdjunction_structureMorphism` — composition
  with `v` is left adjoint to base change along `v`.
* `AlgebraicGeometry.smallEtaleSheafPullbackIsoPostcompose` — inverse image along `v` is
  restriction along composition with `v`.
* `AlgebraicGeometry.hasWeakSheafify_smallEtale_of_over` — weak sheafification on the small étale
  site of `V` from weak sheafification on the localized site at `V`.
* `AlgebraicGeometry.nonempty_constantSheafIso_over_iff` — the equivalence of the two
  trivialization conditions.

## Implementation notes

Base change along the structure morphism of `V` is `smallEtaleBaseChange B V.obj.hom`, whose
source site is the small étale site of `B.obj X hX` rather than of `X`. The two are the *same*
site — `B.obj X hX` is `⟨X, hX⟩` — but not syntactically, so typeclass search does not cross
between them. The crossing is made once, in
`AlgebraicGeometry.smallEtaleBaseChange_structureMorphism_isContinuous`, which restates the
continuity instance in the spelling used here; `CategoryTheory.Functor.IsContinuous` is a `Prop`,
so no second route to one instance is created.

No `@[stacks]` attribute appears in this file. Tag 03S3 is the statement that the small étale
site of `V` is the localization of that of `X`, attributed where the equivalence of sites is
proved; what is added here is the resulting identification of restriction with inverse image,
which the source performs silently.

## References

* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
* [Stacks Project, Tag 093Q](https://stacks.math.columbia.edu/tag/093Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v₁ v₂ u₁ u₂ t w u

namespace CategoryTheory

section Equivalence

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  {D : Type u₂} [Category.{v₂} D] (K : GrothendieckTopology D) (e : C ≌ D)
  [e.inverse.IsDenseSubsite K J] (A : Type w) [Category.{t} A] [HasWeakSheafify K A]

/-- Transporting a presheaf across an equivalence of sites, sheafifying there and transporting
back is left adjoint to taking the underlying presheaf.

This is `CategoryTheory.Equivalence.transportSheafificationAdjunction` with `HasSheafify` on the
target weakened to `HasWeakSheafify`, which is all the construction uses and all that is
available on a localized small étale site. -/
public def transportWeakSheafificationAdjunction :
    (Equivalence.congrLeft (E := A) e.op).functor ⋙ presheafToSheaf K A ⋙
        (e.sheafCongr J K A).inverse ⊣ sheafToPresheaf J A :=
  (((Equivalence.congrLeft (E := A) e.op).toAdjunction.comp
      (sheafificationAdjunction K A)).comp
    (e.sheafCongr J K A).symm.toAdjunction).ofNatIsoRight
      (NatIso.ofComponents (fun F ↦ Functor.isoWhiskerRight e.op.unitIso.symm F.obj)
        (by intro _ _ f; ext Z; exact (f.hom.naturality _).symm))

include K e in
/-- **Weak sheafification transports along an equivalence of sites.** -/
public theorem hasWeakSheafify_of_equivalence : HasWeakSheafify J A :=
  (transportWeakSheafificationAdjunction J K e A).isRightAdjoint

variable [HasWeakSheafify J A]

/-- **The constant sheaf functor commutes with an equivalence of sites.** Restriction along the
functor of the equivalence — the inverse of the induced equivalence of sheaf categories — carries
the constant sheaf on `E` to the constant sheaf on `E`.

Both functors are left adjoint to sections over a final object: the first because the
right adjoint of the composite is sections over the image of the final object, which is
`Stacks.ConstantSheaf.pushforwardSectionsIsoOfTerminal`. -/
public def constantSheafSheafCongrInverseIso {TC : C} (hTC : IsTerminal TC) {TD : D}
    (hTD : IsTerminal TD) (i : e.inverse.obj TD ≅ TC) :
    constantSheaf K A ⋙ (e.sheafCongr J K A).inverse ≅ constantSheaf J A :=
  (((constantSheafAdj K A hTD).comp (e.sheafCongr J K A).symm.toAdjunction).ofNatIsoRight
    (Stacks.ConstantSheaf.pushforwardSectionsIsoOfTerminal e.inverse A K J i)).leftAdjointUniq
      (constantSheafAdj J A hTC)

end Equivalence

end CategoryTheory

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)
  (V : SmallEtale B X hX)

/-- The inverse of the slice equivalence exhibits the localization of the small étale site of `X`
at `V` as a dense subsite of the small étale site of the scheme `V`. This is the form in which
`AlgebraicGeometry.smallEtaleEquivalenceOver_topology` is consumed: it is what makes the induced
equivalence of sheaf categories available to typeclass inference. -/
public instance smallEtaleEquivalenceOver_inverse_isDenseSubsite :
    (smallEtaleEquivalenceOver B X hX V).inverse.IsDenseSubsite
      ((SmallEtale.topology B X hX).over V)
      (SmallEtale.topology B V.obj.left.1 V.obj.left.property) := by
  set e := smallEtaleEquivalenceOver B X hX V with he
  set J := SmallEtale.topology B V.obj.left.1 V.obj.left.property with hJ
  set K := (SmallEtale.topology B X hX).over V with hK
  have h1 : e.functor.IsCocontinuous J K :=
    (e.toAdjunction.isCocontinuous_iff_coverPreserving J K).2
      (smallEtaleEquivalenceOver_inverse_coverPreserving B X hX V)
  have h2 : e.inverse.IsCocontinuous K J :=
    (e.symm.toAdjunction.isCocontinuous_iff_coverPreserving K J).2
      (smallEtaleEquivalenceOver_functor_coverPreserving B X hX V)
  exact Equivalence.isDenseSubsite_inverse_of_isCocontinuous J K e

/-- The slice equivalence carries the final object of the localized site — the identity of `V` —
to the final object `V / V` of the small étale site of the scheme `V`. -/
public def smallEtaleEquivalenceOverFinalIso :
    (smallEtaleEquivalenceOver B X hX V).inverse.obj (Over.mk (𝟙 V)) ≅
      SmallEtale.final B V.obj.left.1 V.obj.left.property :=
  (Over.mkIdTerminal.isTerminalObj (smallEtaleEquivalenceOver B X hX V).inverse).uniqueUpToIso
    (SmallEtale.finalIsTerminal B V.obj.left.1 V.obj.left.property)

/-- **Composition with the structure morphism of `V` is left adjoint to base change along it.**
This is the restriction of `CategoryTheory.Over.mapPullbackAdj` to the étale objects, along the
two full subcategory inclusions; both squares commute on the nose.

Indexed by the object `V` of the small étale site of `X`, as
`AlgebraicGeometry.smallEtaleBaseChange_structureMorphism_isContinuous` below is;
`AlgebraicGeometry.smallEtalePostcomposeBaseChangeAdjunction` is the same adjunction indexed by
an étale morphism of the site instead. -/
public def smallEtalePostcomposeBaseChangeAdjunction_structureMorphism :
    smallEtalePostcompose B X hX V ⊣ smallEtaleBaseChange B V.obj.hom :=
  (Over.mapPullbackAdj V.obj.hom).restrictFullyFaithful
    (BigEtaleOver.IsEtaleOver B V.obj.left.1 V.obj.left.property).fullyFaithfulι
    (BigEtaleOver.IsEtaleOver B X hX).fullyFaithfulι
    (eqToIso (smallEtalePostcompose_comp_inclusion B X hX V).symm)
    (eqToIso (smallEtaleBaseChange_comp_inclusion B V.obj.hom).symm)

/-- Continuity of base change along the structure morphism of `V`, stated with the source site
written as the small étale site of `X` rather than of `B.obj X hX`. The two are the same site and
not the same term, so typeclass inference does not produce this spelling on its own. -/
public instance smallEtaleBaseChange_structureMorphism_isContinuous :
    Functor.IsContinuous (smallEtaleBaseChange B V.obj.hom)
      (SmallEtale.topology B X hX)
      (SmallEtale.topology B V.obj.left.1 V.obj.left.property) :=
  smallEtaleBaseChange_isContinuous B V.obj.hom

variable (A : Type w) [Category.{t} A]

/-- **Weak sheafification on the small étale site of the scheme `V`**, from weak sheafification on
the localization at `V` of the small étale site of `X`. The two sites are equivalent, so this is
`CategoryTheory.hasWeakSheafify_of_equivalence`.

It is a theorem rather than an instance because the localized site of the hypothesis is not
determined by the small étale site of the conclusion. -/
public theorem hasWeakSheafify_smallEtale_of_over
    [HasWeakSheafify ((SmallEtale.topology B X hX).over V) A] :
    HasWeakSheafify (SmallEtale.topology B V.obj.left.1 V.obj.left.property) A :=
  hasWeakSheafify_of_equivalence (SmallEtale.topology B V.obj.left.1 V.obj.left.property)
    ((SmallEtale.topology B X hX).over V) (smallEtaleEquivalenceOver B X hX V) A

/-- Restriction to the localized site at `V`, read through the slice equivalence, is restriction
along composition with the structure morphism of `V`. The underlying functors agree because
`AlgebraicGeometry.smallEtaleEquivalenceOver_restriction` is an equality. -/
public theorem overPullback_comp_sheafCongr_inverse :
    (SmallEtale.topology B X hX).overPullback A V ⋙
        ((smallEtaleEquivalenceOver B X hX V).sheafCongr
          (SmallEtale.topology B V.obj.left.1 V.obj.left.property)
          ((SmallEtale.topology B X hX).over V) A).inverse =
      (smallEtalePostcompose B X hX V).sheafPushforwardContinuous A
        (SmallEtale.topology B V.obj.left.1 V.obj.left.property)
        (SmallEtale.topology B X hX) :=
  rfl

variable [((smallEtaleBaseChange B V.obj.hom).sheafPushforwardContinuous A
    (SmallEtale.topology B X hX)
    (SmallEtale.topology B V.obj.left.1 V.obj.left.property)).IsRightAdjoint]

/-- **Inverse image along the structure morphism of `V` is restriction along composition with
it.** Both are left adjoint to restriction along base change: the first by definition, the second
because composition with `v` is left adjoint to base change along `v`
(`AlgebraicGeometry.smallEtalePostcomposeBaseChangeAdjunction_structureMorphism`) and
precomposition along an adjoint pair of continuous site functors is again an adjoint pair.

In particular the inverse image along an étale morphism needs no sheafification. -/
@[sga "4 VII 1.6" "more general"]
public def smallEtaleSheafPullbackIsoPostcompose :
    (smallEtaleBaseChange B V.obj.hom).sheafPullback A (SmallEtale.topology B X hX)
        (SmallEtale.topology B V.obj.left.1 V.obj.left.property) ≅
      (smallEtalePostcompose B X hX V).sheafPushforwardContinuous A
        (SmallEtale.topology B V.obj.left.1 V.obj.left.property)
        (SmallEtale.topology B X hX) :=
  ((smallEtaleBaseChange B V.obj.hom).sheafAdjunctionContinuous A _ _).leftAdjointUniq
    ((smallEtalePostcomposeBaseChangeAdjunction_structureMorphism
      B X hX V).sheafPushforwardAdjunction A)

/-- **The two trivialization conditions agree.** A sheaf on the small étale site of `X` restricts
to the constant sheaf on `E` over the localized site at `V` exactly when its inverse image along
the structure morphism of `V` is the constant sheaf on `E` on the small étale site of the scheme
`V`.

The three ingredients are the transport of the constant sheaf functor
(`CategoryTheory.constantSheafSheafCongrInverseIso`), the identification of the two restrictions
(`AlgebraicGeometry.overPullback_comp_sheafCongr_inverse` and
`AlgebraicGeometry.smallEtaleSheafPullbackIsoPostcompose`), and full faithfulness of the
equivalence of sheaf categories, which is what allows the isomorphism to be transported back. -/
public theorem nonempty_constantSheafIso_over_iff
    [HasWeakSheafify ((SmallEtale.topology B X hX).over V) A]
    [HasWeakSheafify (SmallEtale.topology B V.obj.left.1 V.obj.left.property) A]
    (F : Sheaf (SmallEtale.topology B X hX) A) (E : A) :
    Nonempty ((constantSheaf ((SmallEtale.topology B X hX).over V) A).obj E ≅
        ((SmallEtale.topology B X hX).overPullback A V).obj F) ↔
      Nonempty ((constantSheaf (SmallEtale.topology B V.obj.left.1 V.obj.left.property) A).obj E ≅
        (((smallEtaleBaseChange B V.obj.hom).sheafPullback A (SmallEtale.topology B X hX)
          (SmallEtale.topology B V.obj.left.1 V.obj.left.property)).obj F)) := by
  set e := smallEtaleEquivalenceOver B X hX V with he
  set J := SmallEtale.topology B V.obj.left.1 V.obj.left.property with hJ
  set K := (SmallEtale.topology B X hX).over V with hK
  set cg := e.sheafCongr J K A with hcg
  -- the constant sheaf on `E` corresponds to the constant sheaf on `E`
  have hconst : cg.inverse.obj ((constantSheaf K A).obj E) ≅ (constantSheaf J A).obj E :=
    (constantSheafSheafCongrInverseIso J K e A (SmallEtale.finalIsTerminal B V.obj.left.1
      V.obj.left.property) Over.mkIdTerminal (smallEtaleEquivalenceOverFinalIso B X hX V)).app E
  -- the restriction to the localized site corresponds to the inverse image
  have hrestr : cg.inverse.obj ((SmallEtale.topology B X hX).overPullback A V |>.obj F) ≅
      ((smallEtaleBaseChange B V.obj.hom).sheafPullback A (SmallEtale.topology B X hX) J).obj F :=
    ((smallEtaleSheafPullbackIsoPostcompose B X hX V A).app F).symm
  exact ⟨fun ⟨c⟩ => ⟨hconst.symm ≪≫ cg.inverse.mapIso c ≪≫ hrestr⟩,
    fun ⟨c⟩ => ⟨cg.inverse.preimageIso (hconst ≪≫ c ≪≫ hrestr.symm)⟩⟩

end AlgebraicGeometry

end
