module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Point.Comap
public import Mathlib.CategoryTheory.Sites.Point.Conservative
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.ElementsColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeContinuous
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleStalkBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BigSitesPushforward.ClosedImmersionCoverings
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedSubschemeSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedImmersionsPushforward.LiftingMorphisms
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Direct image of sheaves of sets along a closed immersion

Let `i : Z ⟶ X` be a closed immersion of schemes. Direct image of sheaves of sets on the small
étale sites, `i_{small, *} : Sh(Z_étale) ⟶ Sh(X_étale)`, is fully faithful, the inverse image
`i_{small}^{-1}` is a left inverse to it, and a sheaf of sets on `X_étale` lies in the essential
image exactly when its restriction to the open complement `X ∖ Z` is the singleton sheaf.

## Main definitions

* `Stacks.EtaleCohomology.openComplement` — the open complement of the image of a closed
  immersion.

## Main results

* `Stacks.EtaleCohomology.smallEtalePushforwardFullyFaithful` — full faithfulness of the direct
  image.
* `Stacks.EtaleCohomology.smallEtalePushforwardCompInverseImageIso` — the counit
  `i^{-1} i_* ⟶ 𝟭` is an isomorphism, so `i^{-1}` is a left inverse of `i_*`.
* `Stacks.EtaleCohomology.smallEtalePushforward_essImage_iff` — the description of the essential
  image, in both directions.
* `Stacks.EtaleCohomology.isCoverDense_smallEtaleBaseChange` and
  `Stacks.EtaleCohomology.isLocallyFull_smallEtaleBaseChange` — base change along a closed
  immersion exhibits the small étale site of `Z` as a dense subsite of itself.

## Implementation notes

Direct image along `i` is restriction along the base-change functor
`Stacks.EtaleCohomology.smallEtaleBaseChange i : X.Etale ⥤ Z.Etale`, so full faithfulness is the
statement that base change is cover dense and locally full. Cover density is the Zariski-local
lifting of étale schemes across a closed immersion: an étale scheme over `Z` is covered by base
changes of étale schemes over `X`. Local fullness is the lifting of morphisms: a morphism between
two base changes is, after replacing the source by a scheme whose base change is isomorphic to
it, base changed from a morphism over `X`; the replacement is an isomorphism, so the image sieve
is already the maximal one. Since `i_*` is a fully faithful right adjoint, the counit of the
adjunction is an isomorphism, which is the left-inverse assertion, and membership in the
essential image is equivalent to the unit being an isomorphism.

The essential image is identified at the level of stalks at geometric points, which jointly
reflect isomorphisms. Away from `Z` the direct image has a singleton stalk because the base
change of an étale neighbourhood disjoint from `Z` is empty, and a sheaf takes an object with
empty underlying scheme to a singleton; that gives one inclusion. Conversely a sheaf whose
restriction to `X ∖ Z` is the singleton sheaf has the unit map an isomorphism on stalks both at
the geometric points of `Z` and at those of `X ∖ Z`, hence everywhere, because the stalk of an
inverse image at a geometric point is the stalk at the image point.

The conservativity of the geometric points is needed at the coefficient universe
`Type (max (u + 1) v)` of the statement, which is larger than the universe at which the small
étale site has enough points. It is supplied by
`Stacks.EtaleCohomology.isIso_of_forall_geometricStalk`, which establishes it there from local
injectivity and local surjectivity rather than from the conservative-family API, whose
concreteness hypotheses pin the coefficients to the universe of the points.

## References

* [Stacks Project, Tag 03PU](https://stacks.math.columbia.edu/tag/03PU)
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
* [Stacks Project, Tag 04CA](https://stacks.math.columbia.edu/tag/04CA)
* [Stacks Project, Tag 04E3](https://stacks.math.columbia.edu/tag/04E3)
* [Stacks Project, Tag 04FV](https://stacks.math.columbia.edu/tag/04FV)
* [Stacks Project, Tag 04FW](https://stacks.math.columbia.edu/tag/04FW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

namespace Stacks.EtaleCohomology

/-- Base change along a closed immersion is a cover-dense functor of small étale sites. -/
public instance isCoverDense_smallEtaleBaseChange {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] :
    (smallEtaleBaseChange i).IsCoverDense (Scheme.smallEtaleTopology Z) := by
  refine ⟨fun V ↦ ?_⟩
  have hV : Etale (V.hom : V.left ⟶ Z) := V.prop
  obtain ⟨I, W, q, g, hq, hg, hcov⟩ :=
    exists_etale_zariskiCover_baseChange_of_isClosedImmersion i (V.hom : V.left ⟶ Z)
  let A : I → X.Etale := fun j ↦ MorphismProperty.Over.mk ⊤ (q j) (hq j)
  let G : ∀ j, (smallEtaleBaseChange i).obj (A j) ⟶ V := fun j ↦
    MorphismProperty.Over.homMk (g j) (hg j) trivial
  have hmem : Sieve.ofArrows _ G ∈ Scheme.smallEtaleTopology Z V := by
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    rw [Scheme.ofArrows_mem_precoverage_iff] at hcov
    ext y
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    exact hcov.1 y
  refine Scheme.smallEtaleTopology Z |>.superset_covering ?_ hmem
  rw [Sieve.ofArrows, Sieve.generate_le_iff]
  rintro Y f ⟨j⟩
  exact Presieve.in_coverByImage _ (G j)

/-- Base change along a closed immersion is a locally full functor of small étale sites. -/
public instance isLocallyFull_smallEtaleBaseChange {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] :
    (smallEtaleBaseChange i).IsLocallyFull (Scheme.smallEtaleTopology Z) := by
  refine ⟨fun {U V} h ↦ ?_⟩
  have hU : Etale (U.hom : U.left ⟶ X) := U.prop
  have hV : Etale (V.hom : V.left ⟶ X) := V.prop
  obtain ⟨W, a, b, hab, hW, e, hehom, hh⟩ :=
    exists_span_baseChange_iso i (U.hom : U.left ⟶ X) (V.hom : V.left ⟶ X) h.left
      (MorphismProperty.Over.w h)
  let A : X.Etale := MorphismProperty.Over.mk ⊤ (a ≫ (U.hom : U.left ⟶ X)) hW
  let iA : A ⟶ U := MorphismProperty.Over.homMk a rfl trivial
  let lA : A ⟶ V := MorphismProperty.Over.homMk b hab.symm trivial
  have hiAleft : ((smallEtaleBaseChange i).map iA).left = e.hom := by
    rw [hehom]
    rfl
  have hsnd : e.inv ≫ pullback.snd (A.hom : A.left ⟶ X) i =
      pullback.snd (U.hom : U.left ⟶ X) i := by
    have h1 : e.hom ≫ pullback.snd (U.hom : U.left ⟶ X) i =
        pullback.snd (A.hom : A.left ⟶ X) i := by
      rw [hehom]
      exact pullback.lift_snd _ _ _
    exact e.inv_comp_eq.mpr h1.symm
  have hh' : h.left = e.inv ≫ ((smallEtaleBaseChange i).map lA).left := hh
  have hkey : (smallEtaleBaseChange i).map lA = (smallEtaleBaseChange i).map iA ≫ h :=
    MorphismProperty.Over.Hom.ext <|
      (((congrArg (· ≫ h.left) hiAleft).trans (congrArg (e.hom ≫ ·) hh')).trans
        (e.hom_inv_id_assoc _)).symm
  have htop : ((smallEtaleBaseChange i).imageSieve h).functorPushforward
      (smallEtaleBaseChange i) = ⊤ := by
    rw [← Sieve.id_mem_iff_eq_top]
    exact ⟨A, iA, MorphismProperty.Over.homMk e.inv hsnd trivial, ⟨lA, hkey⟩,
      MorphismProperty.Over.Hom.ext ((congrArg (e.inv ≫ ·) hiAleft).trans e.inv_hom_id).symm⟩
  rw [htop]
  exact (Scheme.smallEtaleTopology Z).top_mem _

/-- Direct image of sheaves of sets along a closed immersion is fully faithful. -/
@[stacks 04CA "part (1): fully faithful"]
public def smallEtalePushforwardFullyFaithful {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] :
    ((smallEtaleBaseChange i).sheafPushforwardContinuous (Type (max (u + 1) v))
      (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology Z)).FullyFaithful :=
  Functor.FullyFaithful.ofFullyFaithful _

/-- The counit `i^{-1} i_* ⟶ 𝟭` of the adjunction is an isomorphism. -/
@[stacks 04CA "left inverse, sheaves of sets"]
public def smallEtalePushforwardCompInverseImageIso {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] :
    (smallEtaleBaseChange i).sheafPushforwardContinuous (Type (max (u + 1) v))
        (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology Z) ⋙
      smallEtaleInverseImage.{u, v} i ≅
      𝟭 (Sheaf (Scheme.smallEtaleTopology Z) (Type (max (u + 1) v))) :=
  let := (smallEtalePushforwardFullyFaithful.{u, v} i).full
  let := (smallEtalePushforwardFullyFaithful.{u, v} i).faithful
  asIso (smallEtaleInverseImageAdjunction.{u, v} i).counit

/-! ### Stalks and the essential image -/


/-- A sheaf of sets on the small étale site with a terminal stalk at every geometric point is
terminal. -/
private noncomputable def isTerminal_of_stalks {X : Scheme.{u}}
    (F : Sheaf (Scheme.smallEtaleTopology X) (Type (max (u + 1) v)))
    (hF : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
      IsTerminal ((Scheme.pointSmallEtale s).sheafFiber.obj F)) : IsTerminal F := by
  have hAB : AB5OfSize.{u, u} (Type (max (u + 1) v)) :=
    AB5OfSize_of_univLE.{u, u, max (u + 1) v, max (u + 1) v} _
  let f := terminal.from F
  have hiso : IsIso f := isIso_of_forall_geometricStalk f fun _ _ _ s ↦
    isIso_of_isTerminal (hF _ s)
      (IsTerminal.isTerminalObj (Scheme.pointSmallEtale s).sheafFiber _ terminalIsTerminal) _
  exact terminalIsTerminal.ofIso (asIso f).symm

/-- A sheaf of sets on the small étale site takes an object with empty underlying scheme to a
singleton: that object is covered by the empty family. -/
private noncomputable def isTerminal_obj_of_isEmpty {Z : Scheme.{u}}
    (G : Sheaf (Scheme.smallEtaleTopology Z) (Type (max (u + 1) v)))
    (V : Z.Etale) [IsEmpty V.left] : IsTerminal (G.obj.obj (Opposite.op V)) := by
  apply G.isTerminalOfBotCover
  convert (Scheme.ofArrows_mem_smallEtaleTopology_iff
    (f := fun e : Empty ↦ (e.elim : V ⟶ V))).2 (Set.eq_univ_of_forall fun x ↦ isEmptyElim x)
    using 1
  ext Y g
  simp only [Sieve.bot_apply, Sieve.mem_ofArrows_iff]
  exact ⟨False.elim, fun ⟨e, _⟩ ↦ e.elim⟩

/-- If a presheaf is terminal on every object admitting a morphism to one marked by an element
of the fibre of a point, then the stalk of that presheaf at the point is terminal. -/
private noncomputable def isTerminal_presheafFiber_of_neighborhood {C : Type*} [Category* C]
    [LocallySmall.{u} C] {J : GrothendieckTopology C} (Φ : GrothendieckTopology.Point.{u} J)
    (P : Cᵒᵖ ⥤ Type (max (u + 1) v)) (N : Φ.fiber.Elements)
    (hN : ∀ (V : C) (_ : V ⟶ N.1), IsTerminal (P.obj (Opposite.op V))) :
    IsTerminal (Φ.presheafFiber.obj P) := by
  let x := (Types.isTerminalEquivUnique _ (hN N.1 (𝟙 _))).default
  refine (Types.isTerminalEquivUnique _).symm ⟨⟨Φ.toPresheafFiber N.1 N.2 P x⟩, fun a ↦ ?_⟩
  obtain ⟨V, t, y, z, hy, hz⟩ := Φ.toPresheafFiber_jointly_surjective₂ (P := P) a
    (Φ.toPresheafFiber N.1 N.2 P x)
  let T : Φ.fiber.Elements := Φ.fiber.elementsMk V t
  let M := IsCofiltered.min (C := Φ.fiber.Elements) T N
  let l : M ⟶ T := IsCofiltered.minToLeft (C := Φ.fiber.Elements) T N
  let r : M ⟶ N := IsCofiltered.minToRight (C := Φ.fiber.Elements) T N
  have heq : P.map l.1.op y = P.map l.1.op z :=
    ((Types.isTerminalEquivUnique _ (hN M.1 r.1)).uniq _).trans
      ((Types.isTerminalEquivUnique _ (hN M.1 r.1)).uniq _).symm
  rw [← hy, ← hz]
  simpa only [GrothendieckTopology.Point.toPresheafFiber_w_apply, l.2] using
    congrArg (Φ.toPresheafFiber M.1 M.2 P) heq

/-- The open complement of the image of a closed immersion. -/
public def openComplement {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] : X.Opens :=
  ⟨(Set.range i.base)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩

/-- The stalk of a direct image from a closed subscheme is terminal at every geometric point of
the open complement: the complement itself is an étale neighbourhood of such a point all of
whose refinements have empty base change to the closed subscheme. -/
private noncomputable def pushforwardStalk_isTerminal_complement {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (G : Sheaf (Scheme.smallEtaleTopology Z) (Type (max (u + 1) v)))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ (openComplement i).toScheme) :
    IsTerminal ((Scheme.pointSmallEtale (s ≫ (openComplement i).ι)).sheafFiber.obj
      (((smallEtaleBaseChange i).sheafPushforwardContinuous (Type (max (u + 1) v))
        (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology Z)).obj G)) := by
  let N : X.Etale := MorphismProperty.Over.mk ⊤ (openComplement i).ι inferInstance
  apply isTerminal_presheafFiber_of_neighborhood _ _
    (Functor.elementsMk _ N (CategoryTheory.Over.homMk s rfl) : (Scheme.pointSmallEtale _).fiber.Elements)
  intro V g
  have hdis : Disjoint (Set.range (V.hom : V.left ⟶ X).base) (Set.range i.base) := by
    rw [Set.disjoint_left]
    rintro x ⟨w, rfl⟩ hx
    have hm := (g.left w).property
    change ¬ ((openComplement i).ι (g.left w) ∈ Set.range i.base) at hm
    apply hm
    change (g.left ≫ (openComplement i).ι) w ∈ Set.range i.base
    rw [show g.left ≫ (openComplement i).ι = (V.hom : V.left ⟶ X) from
      MorphismProperty.Over.w g]
    exact hx
  have : IsEmpty ((smallEtaleBaseChange i).obj V).left := by
    change IsEmpty ↥(pullback (V.hom : V.left ⟶ X) i)
    exact Scheme.isEmpty_pullback _ _ hdis
  exact isTerminal_obj_of_isEmpty G ((smallEtaleBaseChange i).obj V)

/-- The restriction to the open complement of a direct image from a closed subscheme is the
singleton sheaf. -/
@[sga "4 VIII 6.3" "partial"]
private noncomputable def inverseImage_pushforward_isTerminal_complement {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i]
    (G : Sheaf (Scheme.smallEtaleTopology Z) (Type (max (u + 1) v))) :
    IsTerminal ((smallEtaleInverseImage.{u, v} (openComplement i).ι).obj
      (((smallEtaleBaseChange i).sheafPushforwardContinuous (Type (max (u + 1) v))
        (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology Z)).obj G)) := by
  apply isTerminal_of_stalks
  intro Ω _ _ s
  exact (pushforwardStalk_isTerminal_complement i G s).ofIso
    ((smallEtaleInverseImageStalkIso.{v, u} (openComplement i).ι s).app _).symm

/-- A map of sheaves of sets on `X` that becomes an isomorphism both on the closed subscheme and
on its open complement is an isomorphism: every point of `X` lies in one of the two. -/
private lemma isIso_of_inverseImage_complement {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i]
    {F G : Sheaf (Scheme.smallEtaleTopology X) (Type (max (u + 1) v))} (f : F ⟶ G)
    [IsIso ((smallEtaleInverseImage.{u, v} i).map f)]
    [IsIso ((smallEtaleInverseImage.{u, v} (openComplement i).ι).map f)] :
    IsIso f := by
  let U := openComplement i
  let Ω : Z ⊕ U.toScheme → Type u := fun t ↦ match t with
    | .inl z => SeparableClosure (Z.residueField z)
    | .inr x => SeparableClosure (U.toScheme.residueField x)
  let (t : Z ⊕ U.toScheme) : Field (Ω t) := by cases t <;> dsimp [Ω] <;> infer_instance
  let (t : Z ⊕ U.toScheme) : IsSepClosed (Ω t) := by cases t <;> dsimp [Ω] <;> infer_instance
  let s : ∀ t, Spec (.of (Ω t)) ⟶ X := fun t ↦ match t with
    | .inl z => residueGeometricPoint Z z ≫ i
    | .inr x => residueGeometricPoint U.toScheme x ≫ U.ι
  refine isIso_of_geometricStalk_family s ?_ f ?_
  · ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    by_cases hx : x ∈ Set.range i.base
    · obtain ⟨z, rfl⟩ := hx
      exact ⟨.inl z, default, by
        change i.base (residueGeometricPoint Z z default) = i.base z
        rw [residueGeometricPoint_apply]⟩
    · let y : U.toScheme := ⟨x, hx⟩
      exact ⟨.inr y, default, by
        change U.ι.base (residueGeometricPoint U.toScheme y default) = x
        rw [residueGeometricPoint_apply]
        rfl⟩
  · intro t
    cases t with
    | inl z =>
      have : IsIso ((smallEtaleInverseImage.{u, v} i ⋙
          (Scheme.pointSmallEtale (residueGeometricPoint Z z)).sheafFiber).map f) := by
        change IsIso ((Scheme.pointSmallEtale (residueGeometricPoint Z z)).sheafFiber.map
          ((smallEtaleInverseImage.{u, v} i).map f))
        infer_instance
      exact (NatIso.isIso_map_iff
        (smallEtaleInverseImageStalkIso.{v, u} i (residueGeometricPoint Z z)) f).mp inferInstance
    | inr x =>
      have : IsIso ((smallEtaleInverseImage.{u, v} U.ι ⋙
          (Scheme.pointSmallEtale (residueGeometricPoint U.toScheme x)).sheafFiber).map f) := by
        change IsIso ((Scheme.pointSmallEtale (residueGeometricPoint U.toScheme x)).sheafFiber.map
          ((smallEtaleInverseImage.{u, v} (openComplement i).ι).map f))
        infer_instance
      exact (NatIso.isIso_map_iff
        (smallEtaleInverseImageStalkIso.{v, u} U.ι (residueGeometricPoint U.toScheme x)) f).mp
          inferInstance

/-- A sheaf of sets on `X_étale` lies in the essential image of direct image along a closed
immersion `i : Z ⟶ X` exactly when its restriction to the open complement of `Z` is the
singleton sheaf. -/
@[stacks 04CA "part (1): essential image"]
public theorem smallEtalePushforward_essImage_iff {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (F : Sheaf (Scheme.smallEtaleTopology X) (Type (max (u + 1) v))) :
    ((smallEtaleBaseChange i).sheafPushforwardContinuous (Type (max (u + 1) v))
        (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology Z)).essImage F ↔
      Nonempty (IsTerminal ((smallEtaleInverseImage.{u, v} (openComplement i).ι).obj F)) := by
  have := (smallEtalePushforwardFullyFaithful.{u, v} i).full
  have := (smallEtalePushforwardFullyFaithful.{u, v} i).faithful
  let adj := smallEtaleInverseImageAdjunction.{u, v} i
  refine ⟨fun ⟨G, ⟨e⟩⟩ ↦ ⟨(inverseImage_pushforward_isTerminal_complement i G).ofIso
    ((smallEtaleInverseImage.{u, v} (openComplement i).ι).mapIso e)⟩, fun ⟨hF⟩ ↦ ?_⟩
  have : IsIso ((smallEtaleInverseImage.{u, v} i).map (adj.unit.app F)) := by
    have : IsIso ((smallEtaleInverseImage.{u, v} i).map (adj.unit.app F) ≫
        adj.counit.app ((smallEtaleInverseImage.{u, v} i).obj F)) := by
      have htri : (smallEtaleInverseImage.{u, v} i).map (adj.unit.app F) ≫
          adj.counit.app ((smallEtaleInverseImage.{u, v} i).obj F) = 𝟙 _ :=
        adj.left_triangle_components F
      rw [htri]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (adj.counit.app _)
  have : IsIso ((smallEtaleInverseImage.{u, v} (openComplement i).ι).map (adj.unit.app F)) :=
    isIso_of_isTerminal hF (inverseImage_pushforward_isTerminal_complement i _) _
  have : IsIso (adj.unit.app F) := isIso_of_inverseImage_complement i (adj.unit.app F)
  exact adj.mem_essImage_of_unit_isIso F

end Stacks.EtaleCohomology

end
