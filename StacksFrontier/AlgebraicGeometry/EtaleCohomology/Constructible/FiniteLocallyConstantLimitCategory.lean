module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantIsConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.LimitCategory
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StratumPullback

/-!
# Finite locally constant sheaves on a limit of schemes

Let `X = lim X_i` be the limit of a directed inverse system of quasi-compact and quasi-separated
schemes with affine transition morphisms. Stacks Tag 0GL2 asserts that the category of finite
locally constant sheaves of sets on `X_étale` is the colimit of the categories of finite locally
constant sheaves of sets on the `(X_i)_étale`, and likewise for finite locally constant abelian
sheaves and — over a Noetherian ring `Λ` — for finite type locally constant sheaves of
`Λ`-modules.

The source proves all three clauses by reducing them to Tag 09YU, the same assertion for
*constructible* sheaves: full faithfulness of the comparison is inherited from 09YU outright,
and essential surjectivity is inherited from 09YU together with the geometric statement that a
constructible sheaf at a stage whose inverse image to `X` is finite locally constant is already
finite locally constant at some later stage. This file carries out that reduction.

## Main definitions

* `AlgebraicGeometry.SmallEtaleSheafProperty` — a property of sheaves attached to every object of
  a big étale site; constructibility and finite local constancy are the two instances used here.
* `AlgebraicGeometry.smallEtaleStageTransition` and
  `AlgebraicGeometry.smallEtaleStageProjection` — inverse image between two stages of an inverse
  system of schemes, and from a stage to the vertex of a cone over it.
* `AlgebraicGeometry.smallEtaleStageComparison` — the canonical identification of inverse image
  to the vertex through a later stage with inverse image to the vertex through an earlier one.
* `AlgebraicGeometry.SmallEtaleStagesFaithful`,
  `AlgebraicGeometry.SmallEtaleStagesFull`,
  `AlgebraicGeometry.SmallEtaleStagesEssSurj` and
  `AlgebraicGeometry.SmallEtaleStagesColimit` — the elementwise form of the assertion that the
  category of sheaves with a given property on the vertex is the colimit of the categories of
  such sheaves at the stages.
* `AlgebraicGeometry.SmallEtaleStagesDescend` — the geometric input of Tag 0GL2: a sheaf with the
  first property at a stage whose inverse image to the vertex has the second property acquires
  the second property at a later stage.
* `AlgebraicGeometry.FiniteLocallyConstantSheaves` and
  `AlgebraicGeometry.FiniteTypeLocallyConstantModuleSheaves` — the categories Tag 0GL2 speaks
  about, with `AlgebraicGeometry.smallEtaleFiniteLocallyConstantPullback` and
  `AlgebraicGeometry.smallEtaleFiniteTypeLocallyConstantModulePullback` the inverse-image
  functors between them.

## Main results

* `Stacks.ConstantSheaf.IsFiniteLocallyConstant.of_iso` and
  `Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant.of_iso` — both conditions are invariant
  under isomorphism of sheaves, for an arbitrary concrete coefficient category and for sheaves
  of modules in an arbitrary universe.
* `AlgebraicGeometry.smallEtaleStagesFaithful_of_imp` and
  `AlgebraicGeometry.smallEtaleStagesFull_of_imp` — faithfulness and fullness of the comparison
  pass from a larger class of sheaves to a smaller one. This is the source's "by Lemma 09YU the
  functor in each case is fully faithful".
* `AlgebraicGeometry.smallEtaleStagesEssSurj_of_descend` — essential surjectivity passes from a
  larger class to a smaller one as soon as the smaller class descends to a finite stage. This is
  the source's reduction of each clause to its one remaining geometric assertion.
* `AlgebraicGeometry.smallEtaleStagesColimit_of_descend` — the three put together.
* `AlgebraicGeometry.smallEtaleStagesColimit_isFiniteLocallyConstant` and
  `AlgebraicGeometry.smallEtaleStagesColimit_isFiniteTypeLocallyConstant` — the three clauses of
  Tag 0GL2, each reduced to the corresponding clause of Tag 09YU together with the descent
  statement.

## Implementation notes

The colimit assertion is stated elementwise — faithfulness, fullness and essential surjectivity
of the comparison — rather than as an equivalence out of a colimit in `CategoryTheory.Cat`. The
inverse-image functors compose only up to the canonical isomorphism
`AlgebraicGeometry.smallEtaleSheafPullbackCompIso`, so the stages do not form a strict diagram of
categories without a strictification; the elementwise form needs none, and it is the form the
source's proof is organized in, one paragraph per condition. For a directed index category the
three conditions are exactly the assertion that the category on the vertex is the filtered
colimit of the categories at the stages.

Nothing below assumes that the index preorder is directed or that the cone is a limit cone: the
reductions proved here are implications between the conditions, valid for any cone over any
preordered inverse system, and the hypotheses that make the conditions themselves true are not
touched. Adding the unused assumptions would not strengthen any statement.

The conditions are stated for a property of sheaves rather than for a full subcategory, so that
one statement covers constructibility and finite local constancy at once and the reductions
become statements about an implication between two properties.

### Not proved here

**No `@[stacks 0GL2]` attribute appears in this file.** Tag 0GL2 asserts that the comparison
functor *is* an equivalence; what is proved here is that it is one as soon as

* the corresponding assertion of Tag 09YU holds for constructible sheaves — that tag has no proof
  in this library, only the vocabulary in
  `StacksFrontier/AlgebraicGeometry/EtaleCohomology/Constructible/LimitCategory.lean`; and
* `AlgebraicGeometry.SmallEtaleStagesDescend` holds for the pair (constructible, finite locally
  constant) — the geometric core of Tag 0GL2's own proof, which goes through the descent of a
  finite trivializing étale covering along the system (Tag 0EYL) and is not proved here either.

So no clause of Tag 0GL2 is proved, and no declaration here may be tagged with it, not even with
a qualifier. What is formalized is the reduction the source performs in the first two sentences
of its proof, and the two named inputs are the whole of what remains.

## References

* [Stacks Project, Tag 0GL2](https://stacks.math.columbia.edu/tag/0GL2)
* [Stacks Project, Tag 09YU](https://stacks.math.columbia.edu/tag/09YU)
* [Stacks Project, Tag 0EYL](https://stacks.math.columbia.edu/tag/0EYL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w w' t v u iu r

namespace Stacks.ConstantSheaf

/-- **Finite local constancy is invariant under isomorphism.** A trivializing covering for `F` is
a trivializing covering for any sheaf isomorphic to it, because restriction to a member of the
covering carries the isomorphism along. -/
public theorem IsFiniteLocallyConstant.of_iso {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) {D : Type t} [Category.{w'} D]
    {FD : D → D → Type*} {CD : D → Type w} [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)]
    [ConcreteCategory.{w} D FD] [∀ U : C, HasWeakSheafify (J.over U) D]
    {F G : Sheaf J D} (e : F ≅ G)
    (hF : IsFiniteLocallyConstant (FD := FD) (CD := CD) J F) :
    IsFiniteLocallyConstant (FD := FD) (CD := CD) J G where
  exists_finite_cover U := by
    obtain ⟨I, V, f, hcov, h⟩ := hF.exists_finite_cover U
    refine ⟨I, V, f, hcov, fun i ↦ ?_⟩
    obtain ⟨E, hE, ⟨φ⟩⟩ := h i
    exact ⟨E, hE, ⟨φ ≪≫ (J.overPullback D (V i)).mapIso e⟩⟩

/-- **Local constancy of finite type is invariant under isomorphism.** -/
public theorem IsFiniteTypeLocallyConstant.of_iso (R : Type r) [Ring R] {C : Type u}
    [Category.{v} C] (J : GrothendieckTopology C)
    [∀ V : C, HasWeakSheafify (J.over V) (ModuleCat.{w} R)]
    {F G : Sheaf J (ModuleCat.{w} R)} (e : F ≅ G)
    (hF : IsFiniteTypeLocallyConstant R J F) :
    IsFiniteTypeLocallyConstant R J G := fun U ↦ by
  obtain ⟨I, V, f, hcov, h⟩ := hF U
  refine ⟨I, V, f, hcov, fun i ↦ ?_⟩
  obtain ⟨E, hE, ⟨φ⟩⟩ := h i
  exact ⟨E, hE, ⟨φ ≪≫ (J.overPullback (ModuleCat.{w} R) (V i)).mapIso e⟩⟩

end Stacks.ConstantSheaf

namespace AlgebraicGeometry

section Property

variable (B : BigEtaleSite.{u}) (A : Type t) [Category.{v} A]

/-- A property of `A`-valued sheaves on the small étale site of every object of a big étale site.
Constructibility, `AlgebraicGeometry.IsConstructibleFiniteSheaf`, and finite local constancy are
the two examples used here. -/
public abbrev SmallEtaleSheafProperty : Type (max (u + 1) t v) :=
  ∀ X : B.Scheme, Sheaf (SmallEtale.topology B X.obj X.property) A → Prop

end Property

section Stages

variable (B : BigEtaleSite.{u}) (A : Type t) [Category.{v} A]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous A
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  {I : Type iu} [Preorder I] (Dg : Iᵒᵖ ⥤ B.Scheme)

/-- Inverse image of sheaves from the stage `i` to the stage `j` of an inverse system of schemes
indexed by a preorder, for `i ≤ j`. -/
public abbrev smallEtaleStageTransition {i j : I} (h : i ≤ j) :
    Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property) A ⥤
      Sheaf (SmallEtale.topology B (Dg.obj (op j)).obj (Dg.obj (op j)).property) A :=
  smallEtaleSheafPullback B A (Dg.map (homOfLE h).op)

variable (c : Cone (Dg ⋙ B.inclusion)) (hX : B.Contains c.pt)

/-- Inverse image of sheaves from the stage `i` to the vertex of a cone over the inverse
system. -/
public abbrev smallEtaleStageProjection (i : I) :
    Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property) A ⥤
      Sheaf (SmallEtale.topology B c.pt hX) A :=
  smallEtaleSheafPullback B A
    (ObjectProperty.homMk (c.π.app (op i)) : B.obj c.pt hX ⟶ Dg.obj (op i))

/-- The canonical identification of inverse image to the vertex through the stage `j` with
inverse image to the vertex through the stage `i`, for `i ≤ j`. It is the transported composition
isomorphism `AlgebraicGeometry.smallEtaleSheafPullbackStageComparison` of Tag 021J, so the
conditions below are conditions on canonical maps. -/
public abbrev smallEtaleStageComparison {i j : I} (h : i ≤ j)
    (F : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property) A) :
    (smallEtaleStageProjection B A Dg c hX j).obj
        ((smallEtaleStageTransition B A Dg h).obj F) ≅
      (smallEtaleStageProjection B A Dg c hX i).obj F :=
  smallEtaleSheafPullbackStageComparison B A Dg c hX (homOfLE h).op F

/-- **Faithfulness of the comparison.** Two maps between sheaves with the property `P` at a stage
which agree after inverse image to the vertex already agree at some later stage. -/
public def SmallEtaleStagesFaithful (P : SmallEtaleSheafProperty B A) : Prop :=
  ∀ (i : I)
    (F G : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property) A),
    P (Dg.obj (op i)) F → P (Dg.obj (op i)) G → ∀ a b : F ⟶ G,
      (smallEtaleStageProjection B A Dg c hX i).map a =
        (smallEtaleStageProjection B A Dg c hX i).map b →
      ∃ (j : I) (h : i ≤ j),
        (smallEtaleStageTransition B A Dg h).map a =
          (smallEtaleStageTransition B A Dg h).map b

/-- **Fullness of the comparison.** Every map between the inverse images to the vertex of two
sheaves with the property `P` at a stage is the inverse image of a map at some later stage, read
through the canonical comparison `AlgebraicGeometry.smallEtaleStageComparison`. -/
public def SmallEtaleStagesFull (P : SmallEtaleSheafProperty B A) : Prop :=
  ∀ (i : I)
    (F G : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property) A),
    P (Dg.obj (op i)) F → P (Dg.obj (op i)) G →
    ∀ a : (smallEtaleStageProjection B A Dg c hX i).obj F ⟶
        (smallEtaleStageProjection B A Dg c hX i).obj G,
      ∃ (j : I) (h : i ≤ j) (b : (smallEtaleStageTransition B A Dg h).obj F ⟶
          (smallEtaleStageTransition B A Dg h).obj G),
        (smallEtaleStageComparison B A Dg c hX h F).inv ≫
            (smallEtaleStageProjection B A Dg c hX j).map b ≫
            (smallEtaleStageComparison B A Dg c hX h G).hom = a

/-- **Essential surjectivity of the comparison.** Every sheaf with the property `P` on the vertex
is isomorphic to the inverse image of a sheaf with the property `P` at some stage. -/
public def SmallEtaleStagesEssSurj (P : SmallEtaleSheafProperty B A) : Prop :=
  ∀ F : Sheaf (SmallEtale.topology B c.pt hX) A, P (B.obj c.pt hX) F →
    ∃ (i : I)
      (Fi : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property) A),
      P (Dg.obj (op i)) Fi ∧
        Nonempty ((smallEtaleStageProjection B A Dg c hX i).obj Fi ≅ F)

/-- **The category of `P`-sheaves on the vertex is the colimit of the categories of `P`-sheaves at
the stages**, in elementwise form: the comparison is faithful, full and essentially surjective.
For a directed index preorder these three conditions are exactly that assertion. -/
public structure SmallEtaleStagesColimit (P : SmallEtaleSheafProperty B A) : Prop where
  /-- The comparison is faithful. -/
  faithful : SmallEtaleStagesFaithful B A Dg c hX P
  /-- The comparison is full. -/
  full : SmallEtaleStagesFull B A Dg c hX P
  /-- The comparison is essentially surjective. -/
  essSurj : SmallEtaleStagesEssSurj B A Dg c hX P

/-- **The descent condition.** A sheaf with the property `P` at a stage whose inverse image to the
vertex has the property `Q` has the property `Q` at some later stage. For `P` constructibility and
`Q` finite local constancy this is the geometric core of the proof of Tag 0GL2. -/
public def SmallEtaleStagesDescend (P Q : SmallEtaleSheafProperty B A) : Prop :=
  ∀ (i : I)
    (F : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property) A),
    P (Dg.obj (op i)) F →
    Q (B.obj c.pt hX) ((smallEtaleStageProjection B A Dg c hX i).obj F) →
    ∃ (j : I) (h : i ≤ j),
      Q (Dg.obj (op j)) ((smallEtaleStageTransition B A Dg h).obj F)

variable {B A Dg c hX}

/-- **Faithfulness passes to a smaller class of sheaves.** The condition quantifies over the
sheaves with the given property, so it only gets weaker as the property gets stronger. With `P`
constructibility and `Q` finite local constancy this is the faithfulness half of the source's
"by Lemma 09YU the functor in each case is fully faithful". -/
public theorem smallEtaleStagesFaithful_of_imp {P Q : SmallEtaleSheafProperty B A}
    (hQP : ∀ (X : B.Scheme) (F : Sheaf (SmallEtale.topology B X.obj X.property) A),
      Q X F → P X F)
    (hP : SmallEtaleStagesFaithful B A Dg c hX P) :
    SmallEtaleStagesFaithful B A Dg c hX Q :=
  fun i F G hF hG a b hab => hP i F G (hQP _ F hF) (hQP _ G hG) a b hab

/-- **Fullness passes to a smaller class of sheaves.** With `P` constructibility and `Q` finite
local constancy this is the fullness half of the source's "by Lemma 09YU the functor in each case
is fully faithful". -/
public theorem smallEtaleStagesFull_of_imp {P Q : SmallEtaleSheafProperty B A}
    (hQP : ∀ (X : B.Scheme) (F : Sheaf (SmallEtale.topology B X.obj X.property) A),
      Q X F → P X F)
    (hP : SmallEtaleStagesFull B A Dg c hX P) :
    SmallEtaleStagesFull B A Dg c hX Q :=
  fun i F G hF hG a => hP i F G (hQP _ F hF) (hQP _ G hG) a

/-- **Essential surjectivity passes to a smaller class of sheaves which descends.** Given a
`Q`-sheaf `F` on the vertex, essential surjectivity for the larger class `P` writes it as the
inverse image of a `P`-sheaf `Fi` at a stage; that inverse image has the property `Q`, so the
descent condition makes `Fi` acquire `Q` at a later stage `j`, and the canonical comparison
identifies the inverse image from `j` with `F`.

With `P` constructibility and `Q` finite local constancy this is the source's reduction of each
clause of Tag 0GL2 to its one remaining geometric assertion. -/
public theorem smallEtaleStagesEssSurj_of_descend {P Q : SmallEtaleSheafProperty B A}
    (hQP : ∀ (X : B.Scheme) (F : Sheaf (SmallEtale.topology B X.obj X.property) A),
      Q X F → P X F)
    (hQiso : ∀ (X : B.Scheme) (F G : Sheaf (SmallEtale.topology B X.obj X.property) A),
      (F ≅ G) → Q X F → Q X G)
    (hP : SmallEtaleStagesEssSurj B A Dg c hX P)
    (hd : SmallEtaleStagesDescend B A Dg c hX P Q) :
    SmallEtaleStagesEssSurj B A Dg c hX Q := by
  intro F hF
  obtain ⟨i, Fi, hPFi, ⟨e⟩⟩ := hP F (hQP (B.obj c.pt hX) F hF)
  obtain ⟨j, h, hQj⟩ := hd i Fi hPFi (hQiso (B.obj c.pt hX) F _ e.symm hF)
  exact ⟨j, (smallEtaleStageTransition B A Dg h).obj Fi, hQj,
    ⟨smallEtaleStageComparison B A Dg c hX h Fi ≪≫ e⟩⟩

/-- **The colimit assertion passes to a smaller class of sheaves which descends.** This is the
whole of the source's proof of Tag 0GL2 apart from its two inputs: the colimit assertion for the
larger class, which for constructible sheaves is Tag 09YU, and the descent condition. -/
public theorem smallEtaleStagesColimit_of_descend {P Q : SmallEtaleSheafProperty B A}
    (hQP : ∀ (X : B.Scheme) (F : Sheaf (SmallEtale.topology B X.obj X.property) A),
      Q X F → P X F)
    (hQiso : ∀ (X : B.Scheme) (F G : Sheaf (SmallEtale.topology B X.obj X.property) A),
      (F ≅ G) → Q X F → Q X G)
    (hP : SmallEtaleStagesColimit B A Dg c hX P)
    (hd : SmallEtaleStagesDescend B A Dg c hX P Q) :
    SmallEtaleStagesColimit B A Dg c hX Q where
  faithful := smallEtaleStagesFaithful_of_imp hQP hP.faithful
  full := smallEtaleStagesFull_of_imp hQP hP.full
  essSurj := smallEtaleStagesEssSurj_of_descend hQP hQiso hP.essSurj hd

end Stages

section Concrete

variable (B : BigEtaleSite.{u}) (A : Type t) [Category.{v} A]
  {FA : A → A → Type*} {CA : A → Type w} [∀ E E', FunLike (FA E E') (CA E) (CA E')]
  [ConcreteCategory.{w} A FA]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous A
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (X : B.Scheme) (V : SmallEtale B X.obj X.property),
    HasWeakSheafify ((SmallEtale.topology B X.obj X.property).over V) A]

/-- Finite local constancy of `A`-valued sheaves, as a property attached to every object of the
big étale site. This is the subject of clauses (1) and (2) of Tag 0GL2, for `A` the category of
sets and the category of abelian groups respectively. -/
public abbrev isFiniteLocallyConstantSmallEtaleSheaf : SmallEtaleSheafProperty B A :=
  fun X F => Stacks.ConstantSheaf.IsFiniteLocallyConstant (FD := FA) (CD := CA)
    (SmallEtale.topology B X.obj X.property) F

/-- The category of finite locally constant `A`-valued sheaves on the small étale site of `X`, as
a full subcategory of all `A`-valued sheaves on it. -/
public abbrev FiniteLocallyConstantSheaves (X : B.Scheme) :=
  (show ObjectProperty (Sheaf (SmallEtale.topology B X.obj X.property) A) from
    isFiniteLocallyConstantSmallEtaleSheaf B A (FA := FA) (CA := CA) X).FullSubcategory

/-- The inclusion of finite locally constant sheaves into all sheaves. -/
public abbrev finiteLocallyConstantSheafInclusion (X : B.Scheme) :
    FiniteLocallyConstantSheaves B A (FA := FA) (CA := CA) X ⥤
      Sheaf (SmallEtale.topology B X.obj X.property) A :=
  (show ObjectProperty (Sheaf (SmallEtale.topology B X.obj X.property) A) from
    isFiniteLocallyConstantSmallEtaleSheaf B A (FA := FA) (CA := CA) X).ι

/-- **Inverse image of finite locally constant sheaves.** The functor Tag 0GL2's comparison is
built from, with the inverse image of the underlying sheaf as its value: finite local constancy
survives inverse image along any morphism of the big étale site. -/
public def smallEtaleFiniteLocallyConstantPullback {S T : B.Scheme} (f : T ⟶ S) :
    FiniteLocallyConstantSheaves B A (FA := FA) (CA := CA) S ⥤
      FiniteLocallyConstantSheaves B A (FA := FA) (CA := CA) T :=
  ObjectProperty.lift _
    (finiteLocallyConstantSheafInclusion B A (FA := FA) (CA := CA) S ⋙
      smallEtaleSheafPullback B A f)
    fun F => isFiniteLocallyConstant_smallEtaleSheafPullback' B A f F.obj (hH := F.property)

/-- The inverse image of finite locally constant sheaves is the inverse image of sheaves: the
inclusion into all sheaves intertwines the two. -/
public def smallEtaleFiniteLocallyConstantPullbackCompIso {S T : B.Scheme} (f : T ⟶ S) :
    smallEtaleFiniteLocallyConstantPullback B A (FA := FA) (CA := CA) f ⋙
        finiteLocallyConstantSheafInclusion B A (FA := FA) (CA := CA) T ≅
      finiteLocallyConstantSheafInclusion B A (FA := FA) (CA := CA) S ⋙
        smallEtaleSheafPullback B A f :=
  ObjectProperty.liftCompιIso _ _ _

/-- **A finite locally constant sheaf is constructible**, as an implication between the two
properties of `AlgebraicGeometry.SmallEtaleSheafProperty`. -/
public theorem isConstructibleFiniteSheaf_of_isFiniteLocallyConstantSmallEtaleSheaf
    (X : B.Scheme) (F : Sheaf (SmallEtale.topology B X.obj X.property) A)
    (hF : isFiniteLocallyConstantSmallEtaleSheaf B A (FA := FA) (CA := CA) X F) :
    IsConstructibleFiniteSheaf B X F :=
  isConstructibleFiniteSheaf_of_isFiniteLocallyConstant B X F (hF := hF)

variable {I : Type iu} [Preorder I] (Dg : Iᵒᵖ ⥤ B.Scheme) (c : Cone (Dg ⋙ B.inclusion))
  (hX : B.Contains c.pt)

/-- **Clauses (1) and (2) of Tag 0GL2, reduced to Tag 09YU and the descent condition.** If the
category of constructible `A`-valued sheaves on the vertex is the colimit of the categories of
constructible `A`-valued sheaves at the stages, and a constructible sheaf at a stage whose
inverse image to the vertex is finite locally constant is finite locally constant at some later
stage, then the category of finite locally constant `A`-valued sheaves on the vertex is the
colimit of the categories of finite locally constant `A`-valued sheaves at the stages.

Taking `A` to be the category of sets gives clause (1) and taking it to be the category of
abelian groups gives clause (2), since `AlgebraicGeometry.IsConstructibleSetSheaf` and
`AlgebraicGeometry.IsConstructibleAbelianSheaf` are by definition
`AlgebraicGeometry.IsConstructibleFiniteSheaf`. Neither hypothesis is proved in this
library. -/
public theorem smallEtaleStagesColimit_isFiniteLocallyConstant
    (hP : SmallEtaleStagesColimit B A Dg c hX (fun X => IsConstructibleFiniteSheaf B X))
    (hd : SmallEtaleStagesDescend B A Dg c hX (fun X => IsConstructibleFiniteSheaf B X)
      (isFiniteLocallyConstantSmallEtaleSheaf B A (FA := FA) (CA := CA))) :
    SmallEtaleStagesColimit B A Dg c hX
      (isFiniteLocallyConstantSmallEtaleSheaf B A (FA := FA) (CA := CA)) :=
  smallEtaleStagesColimit_of_descend
    (isConstructibleFiniteSheaf_of_isFiniteLocallyConstantSmallEtaleSheaf B A)
    (fun X _ _ e hF => Stacks.ConstantSheaf.IsFiniteLocallyConstant.of_iso
      (SmallEtale.topology B X.obj X.property) e hF)
    hP hd

end Concrete

section Modules

variable (B : BigEtaleSite.{u}) (R : Type r) [Ring R] [IsNoetherianRing R]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{w} R)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (X : B.Scheme) (V : SmallEtale B X.obj X.property),
    HasWeakSheafify ((SmallEtale.topology B X.obj X.property).over V) (ModuleCat.{w} R)]

/-- Local constancy of finite type for sheaves of `R`-modules, as a property attached to every
object of the big étale site. This is the subject of clause (3) of Tag 0GL2. -/
public abbrev isFiniteTypeLocallyConstantSmallEtaleSheaf :
    SmallEtaleSheafProperty B (ModuleCat.{w} R) :=
  fun X F => Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant R
    (SmallEtale.topology B X.obj X.property) F

/-- The category of finite type locally constant sheaves of `R`-modules on the small étale site of
`X`, as a full subcategory of all sheaves of `R`-modules on it. -/
public abbrev FiniteTypeLocallyConstantModuleSheaves (X : B.Scheme) :=
  (show ObjectProperty (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} R)) from
    isFiniteTypeLocallyConstantSmallEtaleSheaf B R X).FullSubcategory

/-- The inclusion of finite type locally constant module sheaves into all module sheaves. -/
public abbrev finiteTypeLocallyConstantModuleSheafInclusion (X : B.Scheme) :
    FiniteTypeLocallyConstantModuleSheaves B R X ⥤
      Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} R) :=
  (show ObjectProperty (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} R)) from
    isFiniteTypeLocallyConstantSmallEtaleSheaf B R X).ι

/-- **Inverse image of finite type locally constant module sheaves.** The functor clause (3) of
Tag 0GL2's comparison is built from. -/
public def smallEtaleFiniteTypeLocallyConstantModulePullback {S T : B.Scheme} (f : T ⟶ S) :
    FiniteTypeLocallyConstantModuleSheaves B R S ⥤
      FiniteTypeLocallyConstantModuleSheaves B R T :=
  ObjectProperty.lift _
    (finiteTypeLocallyConstantModuleSheafInclusion B R S ⋙
      smallEtaleSheafPullback B (ModuleCat.{w} R) f)
    fun F => isFiniteTypeLocallyConstant_smallEtaleSheafPullback B R f F.obj F.property

/-- The inverse image of finite type locally constant module sheaves is the inverse image of
module sheaves. -/
public def smallEtaleFiniteTypeLocallyConstantModulePullbackCompIso {S T : B.Scheme}
    (f : T ⟶ S) :
    smallEtaleFiniteTypeLocallyConstantModulePullback B R f ⋙
        finiteTypeLocallyConstantModuleSheafInclusion B R T ≅
      finiteTypeLocallyConstantModuleSheafInclusion B R S ⋙
        smallEtaleSheafPullback B (ModuleCat.{w} R) f :=
  ObjectProperty.liftCompιIso _ _ _

variable {I : Type iu} [Preorder I] (Dg : Iᵒᵖ ⥤ B.Scheme) (c : Cone (Dg ⋙ B.inclusion))
  (hX : B.Contains c.pt)

omit [IsNoetherianRing R] in
/-- **Clause (3) of Tag 0GL2, reduced to Tag 09YU and the descent condition.** If the category of
constructible sheaves of `R`-modules on the vertex is the colimit of the categories of
constructible sheaves of `R`-modules at the stages, and a constructible module sheaf at a stage
whose inverse image to the vertex is locally constant of finite type is locally constant of
finite type at some later stage, then the category of finite type locally constant sheaves of
`R`-modules on the vertex is the colimit of the categories of finite type locally constant
sheaves of `R`-modules at the stages.

Neither hypothesis is proved in this library. -/
public theorem smallEtaleStagesColimit_isFiniteTypeLocallyConstant
    (hP : SmallEtaleStagesColimit B (ModuleCat.{w} R) Dg c hX
      (fun X => IsConstructibleModuleSheaf B X R))
    (hd : SmallEtaleStagesDescend B (ModuleCat.{w} R) Dg c hX
      (fun X => IsConstructibleModuleSheaf B X R)
      (isFiniteTypeLocallyConstantSmallEtaleSheaf B R)) :
    SmallEtaleStagesColimit B (ModuleCat.{w} R) Dg c hX
      (isFiniteTypeLocallyConstantSmallEtaleSheaf B R) :=
  smallEtaleStagesColimit_of_descend
    (fun X F hF => isConstructibleModuleSheaf_of_isFiniteTypeLocallyConstant B X R F hF)
    (fun X _ _ e hF => Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant.of_iso R
      (SmallEtale.topology B X.obj X.property) e hF)
    hP hd

end Modules

end AlgebraicGeometry

end
