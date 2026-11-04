module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ShriekGeneratorConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StrongSerre
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StrongSerreSets
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.WeakSerreAbelian
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.AbelianUnderlyingSets
public import StacksFrontier.CategoryTheory.Sites.PullbackSheafCompose

/-!
# Constructible abelian sheaves form a strong Serre subcategory

Let `X` be a Noetherian scheme. The constructible sheaves of abelian groups on the small étale
site of `X` are closed under subobjects, quotients and extensions, that is, they form a strong
Serre subcategory of all abelian sheaves.

The closure statements take as hypotheses that inverse image commutes with passing to underlying
sheaves of sets (`AlgebraicGeometry.SmallEtaleUnderlyingSetCommutes`), that representable sheaves
of sets are constructible (`AlgebraicGeometry.RepresentableIsConstructibleSetSheaf`) and that
every constructible sheaf of sets is covered by finitely many representable ones
(`AlgebraicGeometry.HasFiniteRepresentableCover`).

## Main definitions

* `AlgebraicGeometry.smallEtaleUnderlyingSetSheaf`: the sheaf of sets underlying an abelian sheaf.
* `AlgebraicGeometry.SmallEtaleUnderlyingSetCommutes`: inverse image along small étale base
  change commutes with passing to the underlying sheaf of sets.

## Main results

* `AlgebraicGeometry.smallEtaleUnderlyingSetCommutes`: inverse image along small étale base
  change commutes with passing to the underlying sheaf of sets.
* `AlgebraicGeometry.isConstructibleSetSheaf_underlying` and
  `AlgebraicGeometry.isConstructibleAbelianSheaf_of_underlying`: an abelian sheaf is
  constructible if and only if its underlying sheaf of sets is.
* `AlgebraicGeometry.isConstructibleAbelianSheaf_of_mono`: a subsheaf of a constructible abelian
  sheaf is constructible.
* `AlgebraicGeometry.isConstructibleAbelianSheaf_of_epi`: a quotient of a constructible abelian
  sheaf is constructible.
* `AlgebraicGeometry.isSerreClass_isConstructibleAbelianSheaf`: the constructible abelian sheaves
  form a strong Serre subcategory, `CategoryTheory.ObjectProperty.IsSerreClass`: they contain
  zero and are closed under subobjects, quotients and extensions.

## References

* [Stacks Project, Tag 09BH](https://stacks.math.columbia.edu/tag/09BH)
* [Stacks Project, Tag 02MP](https://stacks.math.columbia.edu/tag/02MP)
* [Stacks Project, Tag 00YT](https://stacks.math.columbia.edu/tag/00YT)
* [Stacks Project, Tag 03RZ](https://stacks.math.columbia.edu/tag/03RZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u})
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) AddCommGrpCat.{u + 1}]

/-- Passing from an abelian sheaf on the small étale site of `S` to the sheaf of sets underlying
it. -/
public abbrev smallEtaleUnderlyingSetSheaf (S : B.Scheme) :
    Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmallEtale.topology B S.obj S.property) (Type (u + 1)) :=
  sheafCompose (SmallEtale.topology B S.obj S.property) (forget AddCommGrpCat.{u + 1})

variable (X : B.Scheme)

/-- `SmallEtaleUnderlyingSetCommutes B X` says that, on the small étale sites of the objects of
`B` over `X`, inverse image along small étale base change to any `T ⟶ X` commutes with passing
from an abelian sheaf to its underlying sheaf of sets. -/
public abbrev SmallEtaleUnderlyingSetCommutes : Prop :=
  ∀ (T : B.Scheme) (g : T ⟶ X)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}),
    Nonempty ((smallEtaleSetPullback B g).obj ((smallEtaleUnderlyingSetSheaf B X).obj F) ≅
      (smallEtaleUnderlyingSetSheaf B T).obj ((smallEtaleAbelianPullback B g).obj F))

omit [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
  HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) AddCommGrpCat.{u + 1}] in
/-- On the small étale sites of the objects of `B` over `X`, inverse image along small étale base
change to any `T ⟶ X` commutes with passing from an abelian sheaf to its underlying sheaf of
sets. -/
@[stacks 00YT "the forgetful functor from abelian groups to sets, on the small étale sites over \
X: inverse image along small étale base change commutes with passing to the underlying sheaf of \
sets"]
public theorem smallEtaleUnderlyingSetCommutes : SmallEtaleUnderlyingSetCommutes B X := by
  intro T g F
  let Φ := smallEtaleBaseChange B g
  have : ∀ P : (SmallEtale B X.obj X.property)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      Φ.op.HasPointwiseLeftKanExtension P := fun _ Y => by
    have := hasColimitsOfShape_of_essentiallySmall.{u + 1}
      (CostructuredArrow Φ.op Y) AddCommGrpCat.{u + 1}
    infer_instance
  have : ∀ P : (SmallEtale B X.obj X.property)ᵒᵖ ⥤ Type (u + 1),
      Φ.op.HasPointwiseLeftKanExtension P := fun _ Y => by
    have := hasColimitsOfShape_of_essentiallySmall.{u + 1}
      (CostructuredArrow Φ.op Y) (Type (u + 1))
    infer_instance
  have : ∀ Y : (SmallEtale B T.obj T.property)ᵒᵖ,
      PreservesColimitsOfShape (CostructuredArrow Φ.op Y)
        (forget AddCommGrpCat.{u + 1}) := fun Y => by
    have : IsFiltered (CostructuredArrow Φ.op Y) :=
      IsFiltered.of_equivalence (structuredArrowOpEquivalence Φ Y.unop)
    have : PreservesFilteredColimitsOfSize.{u, u + 1} (forget AddCommGrpCat.{u + 1}) :=
      preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u + 1}
        (forget AddCommGrpCat.{u + 1})
    exact PreservesFilteredColimitsOfSize.preserves_filtered_colimits
      (CostructuredArrow Φ.op Y)
  exact ⟨Φ.sheafPullbackSheafComposeIso AddCommGrpCat.{u + 1}
    (SmallEtale.topology B X.obj X.property) (SmallEtale.topology B T.obj T.property)
    (forget AddCommGrpCat.{u + 1}) F⟩

/-- Under `SmallEtaleUnderlyingSetCommutes B X`, pulling back the underlying sheaf of sets of `F`
is finite locally constant if and only if pulling back `F` is. -/
private theorem isFiniteLocallyConstant_setPullback_underlying_iff
    (hunderlying : SmallEtaleUnderlyingSetCommutes B X) {T : B.Scheme} (g : T ⟶ X)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) :
    Stacks.ConstantSheaf.IsFiniteLocallyConstant
        (SmallEtale.topology B T.obj T.property)
        ((smallEtaleSetPullback B g).obj ((smallEtaleUnderlyingSetSheaf B X).obj F)) ↔
      Stacks.ConstantSheaf.IsFiniteLocallyConstant
        (SmallEtale.topology B T.obj T.property) ((smallEtaleAbelianPullback B g).obj F) := by
  obtain ⟨e⟩ := hunderlying T g F
  exact ⟨fun h => Stacks.ConstantSheaf.isFiniteLocallyConstant_of_forget _ _
      (Stacks.ConstantSheaf.isFiniteLocallyConstant_congr _ e (hF := h)),
    fun h => Stacks.ConstantSheaf.isFiniteLocallyConstant_congr _ e.symm
      (hF := Stacks.ConstantSheaf.isFiniteLocallyConstant_forget _ _ h)⟩

/-- Given `hunderlying : SmallEtaleUnderlyingSetCommutes B X`, the sheaf of sets underlying a
constructible abelian sheaf is constructible. -/
public theorem isConstructibleSetSheaf_underlying
    (hunderlying : SmallEtaleUnderlyingSetCommutes B X)
    {F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}}
    (hF : IsConstructibleAbelianSheaf B X F) :
    IsConstructibleSetSheaf B X ((smallEtaleUnderlyingSetSheaf B X).obj F) := by
  intro U
  obtain ⟨s, hs⟩ := hF U
  exact ⟨s, fun i =>
    (isFiniteLocallyConstant_setPullback_underlying_iff B X hunderlying _ F).2 (hs i)⟩

/-- Given `hunderlying : SmallEtaleUnderlyingSetCommutes B X`, an abelian sheaf whose underlying
sheaf of sets is constructible is constructible. -/
public theorem isConstructibleAbelianSheaf_of_underlying
    (hunderlying : SmallEtaleUnderlyingSetCommutes B X)
    {F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}}
    (hF : IsConstructibleSetSheaf B X ((smallEtaleUnderlyingSetSheaf B X).obj F)) :
    IsConstructibleAbelianSheaf B X F := by
  intro U
  obtain ⟨s, hs⟩ := hF U
  exact ⟨s, fun i =>
    (isFiniteLocallyConstant_setPullback_underlying_iff B X hunderlying _ F).1 (hs i)⟩

/-- A subsheaf of a constructible sheaf of abelian groups on the small étale site of a Noetherian
scheme is constructible. It assumes `hunderlying : SmallEtaleUnderlyingSetCommutes B X`,
`hrep : RepresentableIsConstructibleSetSheaf B X` and `hcover : HasFiniteRepresentableCover B X`.
-/
@[stacks 09BH "part (2), subsheaf, with Stacks 00YT as hunderlying, Stacks 03S8 as hrep and the \
surjection half of Stacks 09Y9 as hcover"]
public theorem isConstructibleAbelianSheaf_of_mono [IsNoetherian X.obj]
    (hunderlying : SmallEtaleUnderlyingSetCommutes B X)
    (hrep : RepresentableIsConstructibleSetSheaf B X)
    (hcover : HasFiniteRepresentableCover B X)
    {F G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}}
    (i : G ⟶ F) [Mono i] (hF : IsConstructibleAbelianSheaf B X F) :
    IsConstructibleAbelianSheaf B X G :=
  isConstructibleAbelianSheaf_of_underlying B X hunderlying <|
    isConstructibleSetSheaf_of_mono B X hrep hcover ((smallEtaleUnderlyingSetSheaf B X).map i)
      (isConstructibleSetSheaf_underlying B X hunderlying hF)

/-- The class of constructible abelian sheaves on the small étale site of a Noetherian scheme is
closed under subobjects. It assumes `hunderlying : SmallEtaleUnderlyingSetCommutes B X`,
`hrep : RepresentableIsConstructibleSetSheaf B X` and `hcover : HasFiniteRepresentableCover B X`.
-/
public theorem isClosedUnderSubobjects_isConstructibleAbelianSheaf [IsNoetherian X.obj]
    (hunderlying : SmallEtaleUnderlyingSetCommutes B X)
    (hrep : RepresentableIsConstructibleSetSheaf B X)
    (hcover : HasFiniteRepresentableCover B X) :
    (isConstructibleAbelianSheafProperty B X :
      ObjectProperty (Sheaf (SmallEtale.topology B X.obj X.property)
        AddCommGrpCat.{u + 1})).IsClosedUnderSubobjects :=
  ⟨fun i _ hF => isConstructibleAbelianSheaf_of_mono B X hunderlying hrep hcover i hF⟩

/-- The constructible abelian sheaves on the small étale site of a Noetherian scheme form a Serre
subcategory, given the three hypotheses of `isSerreClass_isConstructibleAbelianSheaf`. -/
private theorem isSerreClass_isConstructibleAbelianSheaf_aux [IsNoetherian X.obj]
    (hunderlying : SmallEtaleUnderlyingSetCommutes B X)
    (hrep : RepresentableIsConstructibleSetSheaf B X)
    (hcover : HasFiniteRepresentableCover B X) :
    (isConstructibleAbelianSheafProperty B X :
      ObjectProperty (Sheaf (SmallEtale.topology B X.obj X.property)
        AddCommGrpCat.{u + 1})).IsSerreClass := by
  have : (isConstructibleAbelianSheafProperty B X :
      ObjectProperty (Sheaf (SmallEtale.topology B X.obj X.property)
        AddCommGrpCat.{u + 1})).IsClosedUnderSubobjects :=
    isClosedUnderSubobjects_isConstructibleAbelianSheaf B X hunderlying hrep hcover
  have : (isConstructibleAbelianSheafProperty B X :
      ObjectProperty (Sheaf (SmallEtale.topology B X.obj X.property)
        AddCommGrpCat.{u + 1})).IsWeakSerreClass :=
    constructibleAbelianSheaf_isWeakSerreClass B X
  exact (isConstructibleAbelianSheafProperty B X).isSerreClass_of_isClosedUnderSubobjects

/-- A quotient of a constructible sheaf of abelian groups on the small étale site of a Noetherian
scheme is constructible. It assumes `hunderlying : SmallEtaleUnderlyingSetCommutes B X`,
`hrep : RepresentableIsConstructibleSetSheaf B X` and `hcover : HasFiniteRepresentableCover B X`.
-/
@[stacks 09BH "part (2), quotient sheaf, with Stacks 00YT as hunderlying, Stacks 03S8 as hrep \
and the surjection half of Stacks 09Y9 as hcover"]
public theorem isConstructibleAbelianSheaf_of_epi [IsNoetherian X.obj]
    (hunderlying : SmallEtaleUnderlyingSetCommutes B X)
    (hrep : RepresentableIsConstructibleSetSheaf B X)
    (hcover : HasFiniteRepresentableCover B X)
    {F Q : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}}
    (p : F ⟶ Q) [Epi p] (hF : IsConstructibleAbelianSheaf B X F) :
    IsConstructibleAbelianSheaf B X Q := by
  have := isSerreClass_isConstructibleAbelianSheaf_aux B X hunderlying hrep hcover
  exact (isConstructibleAbelianSheafProperty B X).prop_of_epi p hF

/-- The constructible sheaves of abelian groups on the small étale site of a Noetherian scheme form
a *strong* Serre subcategory of all abelian sheaves on that site: they contain zero and are closed
under subobjects, quotients and extensions. It assumes
`hunderlying : SmallEtaleUnderlyingSetCommutes B X`,
`hrep : RepresentableIsConstructibleSetSheaf B X` and `hcover : HasFiniteRepresentableCover B X`.
-/
@[stacks 09BH "part (2), the strong Serre property, with Stacks 00YT as hunderlying, Stacks 03S8 \
as hrep and the surjection half of Stacks 09Y9 as hcover"]
public theorem isSerreClass_isConstructibleAbelianSheaf [IsNoetherian X.obj]
    (hunderlying : SmallEtaleUnderlyingSetCommutes B X)
    (hrep : RepresentableIsConstructibleSetSheaf B X)
    (hcover : HasFiniteRepresentableCover B X) :
    (isConstructibleAbelianSheafProperty B X :
      ObjectProperty (Sheaf (SmallEtale.topology B X.obj X.property)
        AddCommGrpCat.{u + 1})).IsSerreClass := by
  exact isSerreClass_isConstructibleAbelianSheaf_aux B X hunderlying hrep hcover

end AlgebraicGeometry

end
