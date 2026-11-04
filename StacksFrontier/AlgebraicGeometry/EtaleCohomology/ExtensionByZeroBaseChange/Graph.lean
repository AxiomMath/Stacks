module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Localization
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.CategoryTheory.Comma.Over.Pullback
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The graph of an étale object inside a base change

Let `j : U ⟶ X` be an object of the small étale site of `X` and let `W ⟶ U` be étale. Viewing
`W` as étale over `X` and base changing back to `U` gives `W ×_X U`, and the graph
`(1, W → U) : W ⟶ W ×_X U` is an open immersion, because it is a section of a morphism between
schemes étale over `U`, and a closed immersion as soon as `j` is separated, because it is a
section of a scheme separated over `W`. Its range is therefore open and closed, so `W` and the
open complement of that range cover `W ×_X U` in the small étale site of `U`.

That clopen decomposition is what makes extension by zero along a separated étale morphism
land in the direct image: a section of a sheaf on `W` extends over `W ×_X U` by prescribing it
on the graph and zero on the complement.

## Main definitions

* `AlgebraicGeometry.smallEtaleGraph` — the graph `W ⟶ W ×_X U`.
* `AlgebraicGeometry.smallEtaleGraphComplement` and
  `AlgebraicGeometry.smallEtaleGraphComplementInto` — the complementary open subscheme and its
  inclusion, as an object of the small étale site of `U`.
* `AlgebraicGeometry.disjointFromSmallEtaleGraph` — the étale-test-object criterion for a
  morphism into `W ×_X U` to avoid the graph.
* `AlgebraicGeometry.Scheme.Hom.complementScheme` — the open subscheme complementary to the
  range of a morphism which is both an open and a closed immersion.

## Main results

* `AlgebraicGeometry.etaleGraphIntoPullback_isOpenImmersion` and
  `AlgebraicGeometry.separatedEtaleGraphIntoPullback_isOpenAndClosed` — the graph of a
  morphism over an étale, respectively separated étale, morphism of schemes.
* `AlgebraicGeometry.bigEtaleGraphIntoPullback_isOpenAndClosed` — the same inside a big étale
  site.
* `AlgebraicGeometry.smallEtaleGraph_mono` and
  `AlgebraicGeometry.smallEtaleGraphComplementInto_mono` — both members of the decomposition
  are monomorphisms of the site.
* `AlgebraicGeometry.smallEtaleGraphComplement_disjoint` — the two members are disjoint.
* `AlgebraicGeometry.graphComplementCover_mem_smallEtaleTopology` — the two members cover
  `W ×_X U`.
* `AlgebraicGeometry.emptyCover_mem_smallEtaleTopology` — an étale object over `U` with empty
  underlying scheme is covered by the empty family.

## References

* [Stacks Project, Tag 0F4L](https://stacks.math.columbia.edu/tag/0F4L)
* [Stacks Project, Tag 01KT](https://stacks.math.columbia.edu/tag/01KT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry

/-- The graph `(1, f) : W ⟶ W ×_Z Y` of a morphism `f : W ⟶ Y` over an étale morphism
`g : Y ⟶ Z` is an open immersion: it is a base change of the diagonal of `g`, which is an open
immersion because `g` is unramified. -/
public theorem etaleGraphIntoPullback_isOpenImmersion
    {W Y Z : Scheme.{u}} (f : W ⟶ Y) (g : Y ⟶ Z) [Etale g] :
    IsOpenImmersion
      (CategoryTheory.Limits.pullback.lift (𝟙 W) f (Category.id_comp (f ≫ g))) := by
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsOpenImmersion (pullback.fst f (𝟙 Y)),
    ← MorphismProperty.cancel_right_of_respectsIso @IsOpenImmersion _
      (pullback.congrHom rfl (Category.id_comp g)).inv]
  convert (MorphismProperty.of_isPullback
    (pullback_map_diagonal_isPullback f (𝟙 Y) g)
    (inferInstance : IsOpenImmersion (pullback.diagonal g)))
  ext : 1
  · simp [pullback.congrHom_inv, pullback.map, Category.assoc, pullback.lift_fst]
  · simp [pullback.congrHom_inv, pullback.map, Category.assoc, pullback.lift_snd,
      pullback.condition]

/-- If `g` is moreover separated, the graph of `f` over `g` is both an open and a closed
immersion, being a section of a morphism separated over `W`. -/
@[ega "IV 17.9.3" "more general"]
public theorem separatedEtaleGraphIntoPullback_isOpenAndClosed
    {W Y Z : Scheme.{u}} (f : W ⟶ Y) (g : Y ⟶ Z)
    [Etale g] [IsSeparated g] :
    IsOpenImmersion
        (CategoryTheory.Limits.pullback.lift (𝟙 W) f (Category.id_comp (f ≫ g))) ∧
      IsClosedImmersion
        (CategoryTheory.Limits.pullback.lift (𝟙 W) f (Category.id_comp (f ≫ g))) :=
  ⟨etaleGraphIntoPullback_isOpenImmersion f g, inferInstance⟩

/-- The inclusion of a big étale site into schemes sends the graph of `f` over `g` to the graph
of the image of `f` over the image of `g`, up to the canonical identification of fibre
products. -/
public theorem bigEtale_inclusion_map_graph_comp_iso_hom
    (B : BigEtaleSite.{u}) {W Y Z : B.Scheme} (f : W ⟶ Y) (g : Y ⟶ Z) :
    B.inclusion.map (pullback.lift (𝟙 W) f (Category.id_comp (f ≫ g))) ≫
      (PreservesPullback.iso B.inclusion (f ≫ g) g ≪≫
        pullback.congrHom (Functor.map_comp B.inclusion f g) rfl).hom =
      pullback.lift (𝟙 (B.inclusion.obj W)) (B.inclusion.map f)
        (Category.id_comp (B.inclusion.map f ≫ B.inclusion.map g)) := by
  let e₀ := PreservesPullback.iso B.inclusion (f ≫ g) g
  let e₁ : pullback (B.inclusion.map (f ≫ g)) (B.inclusion.map g) ≅
      pullback (B.inclusion.map f ≫ B.inclusion.map g) (B.inclusion.map g) :=
    pullback.congrHom (Functor.map_comp B.inclusion f g) rfl
  have he₀fst : e₀.hom ≫ pullback.fst (B.inclusion.map (f ≫ g))
      (B.inclusion.map g) = B.inclusion.map (pullback.fst (f ≫ g) g) := by
    simpa only [e₀] using PreservesPullback.iso_hom_fst B.inclusion (f ≫ g) g
  have he₀snd : e₀.hom ≫ pullback.snd (B.inclusion.map (f ≫ g))
      (B.inclusion.map g) = B.inclusion.map (pullback.snd (f ≫ g) g) := by
    simpa only [e₀] using PreservesPullback.iso_hom_snd B.inclusion (f ≫ g) g
  have he₁fst : e₁.hom ≫ pullback.fst
      (B.inclusion.map f ≫ B.inclusion.map g) (B.inclusion.map g) =
      pullback.fst (B.inclusion.map (f ≫ g)) (B.inclusion.map g) := by
    simp [e₁, pullback.congrHom, pullback.map]
  have he₁snd : e₁.hom ≫ pullback.snd
      (B.inclusion.map f ≫ B.inclusion.map g) (B.inclusion.map g) =
      pullback.snd (B.inclusion.map (f ≫ g)) (B.inclusion.map g) := by
    simp [e₁, pullback.congrHom, pullback.map]
  show B.inclusion.map (pullback.lift (𝟙 W) f (Category.id_comp (f ≫ g))) ≫
    (e₀ ≪≫ e₁).hom = _
  apply pullback.hom_ext
  · calc
      (B.inclusion.map (pullback.lift (𝟙 W) f (Category.id_comp (f ≫ g))) ≫
            (e₀ ≪≫ e₁).hom) ≫ pullback.fst (B.inclusion.map f ≫ B.inclusion.map g)
            (B.inclusion.map g) =
          B.inclusion.map (pullback.lift (𝟙 W) f (Category.id_comp (f ≫ g))) ≫
            e₀.hom ≫ pullback.fst (B.inclusion.map (f ≫ g)) (B.inclusion.map g) := by
              simp only [Iso.trans_hom, Category.assoc, he₁fst]
      _ = B.inclusion.map (pullback.lift (𝟙 W) f (Category.id_comp (f ≫ g))) ≫
            B.inclusion.map (pullback.fst (f ≫ g) g) := by rw [he₀fst]
      _ = B.inclusion.map (pullback.lift (𝟙 W) f (Category.id_comp (f ≫ g)) ≫
            pullback.fst (f ≫ g) g) := by rw [Functor.map_comp]
      _ = 𝟙 (B.inclusion.obj W) := by rw [pullback.lift_fst, CategoryTheory.Functor.map_id]
      _ = pullback.lift (𝟙 (B.inclusion.obj W)) (B.inclusion.map f)
            (Category.id_comp (B.inclusion.map f ≫ B.inclusion.map g)) ≫
            pullback.fst (B.inclusion.map f ≫ B.inclusion.map g) (B.inclusion.map g) :=
              (pullback.lift_fst _ _ _).symm
  · calc
      (B.inclusion.map (pullback.lift (𝟙 W) f (Category.id_comp (f ≫ g))) ≫
            (e₀ ≪≫ e₁).hom) ≫ pullback.snd (B.inclusion.map f ≫ B.inclusion.map g)
            (B.inclusion.map g) =
          B.inclusion.map (pullback.lift (𝟙 W) f (Category.id_comp (f ≫ g))) ≫
            e₀.hom ≫ pullback.snd (B.inclusion.map (f ≫ g)) (B.inclusion.map g) := by
              simp only [Iso.trans_hom, Category.assoc, he₁snd]
      _ = B.inclusion.map (pullback.lift (𝟙 W) f (Category.id_comp (f ≫ g))) ≫
            B.inclusion.map (pullback.snd (f ≫ g) g) := by rw [he₀snd]
      _ = B.inclusion.map (pullback.lift (𝟙 W) f (Category.id_comp (f ≫ g)) ≫
            pullback.snd (f ≫ g) g) := by rw [Functor.map_comp]
      _ = B.inclusion.map f := by
            simpa only [Functor.map_comp] using congrArg B.inclusion.map
              (pullback.lift_snd (𝟙 W) f (Category.id_comp (f ≫ g)))
      _ = pullback.lift (𝟙 (B.inclusion.obj W)) (B.inclusion.map f)
            (Category.id_comp (B.inclusion.map f ≫ B.inclusion.map g)) ≫
            pullback.snd (B.inclusion.map f ≫ B.inclusion.map g) (B.inclusion.map g) :=
              (pullback.lift_snd _ _ _).symm

/-- The graph of a morphism of a big étale site over a separated étale morphism is an open and
closed immersion of schemes. Fibre products of a big étale site are computed in schemes, so
this is the statement for schemes transported along the canonical identification. -/
public theorem bigEtaleGraphIntoPullback_isOpenAndClosed
    (B : BigEtaleSite.{u})
    {W Y Z : B.Scheme} (f : W ⟶ Y) (g : Y ⟶ Z)
    [Etale (B.inclusion.map g)] [IsSeparated (B.inclusion.map g)] :
    IsOpenImmersion (B.inclusion.map
      (pullback.lift (𝟙 W) f (Category.id_comp (f ≫ g)))) ∧
    IsClosedImmersion (B.inclusion.map
      (pullback.lift (𝟙 W) f (Category.id_comp (f ≫ g)))) := by
  let e := PreservesPullback.iso B.inclusion (f ≫ g) g ≪≫
    pullback.congrHom (Functor.map_comp B.inclusion f g) rfl
  have he := bigEtale_inclusion_map_graph_comp_iso_hom B f g
  constructor
  · refine (MorphismProperty.cancel_right_of_respectsIso @IsOpenImmersion _ e.hom).mp ?_
    rw [he]
    exact etaleGraphIntoPullback_isOpenImmersion _ _
  · refine (MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _ e.hom).mp ?_
    rw [he]
    exact (separatedEtaleGraphIntoPullback_isOpenAndClosed _ _).2

namespace Scheme.Hom

/-- The range of a morphism which is both an open and a closed immersion is closed. -/
public theorem isClosed_opensRange
    {A Z : Scheme.{u}} (i : A ⟶ Z)
    [IsOpenImmersion i] [IsClosedImmersion i] :
    IsClosed (i.opensRange : Set Z) := by
  rw [coe_opensRange]
  exact i.isClosedEmbedding.isClosed_range

/-- The open complement of the range of a morphism which is both an open and a closed
immersion. -/
public noncomputable def complementOpens
    {A Z : Scheme.{u}} (i : A ⟶ Z)
    [IsOpenImmersion i] [IsClosedImmersion i] : Z.Opens :=
  ⟨(i.opensRange : Set Z)ᶜ, (isClosed_opensRange i).isOpen_compl⟩

/-- The open subscheme complementary to the range of a morphism which is both an open and a
closed immersion. -/
public noncomputable def complementScheme
    {A Z : Scheme.{u}} (i : A ⟶ Z)
    [IsOpenImmersion i] [IsClosedImmersion i] : Scheme.{u} :=
  Z.restrict (TopologicalSpace.Opens.isOpenEmbedding (complementOpens i))

/-- The inclusion of the complementary open subscheme of a morphism which is both an open and
a closed immersion. -/
public noncomputable def complementι
    {A Z : Scheme.{u}} (i : A ⟶ Z)
    [IsOpenImmersion i] [IsClosedImmersion i] : complementScheme i ⟶ Z :=
  Z.ofRestrict (TopologicalSpace.Opens.isOpenEmbedding (complementOpens i))

/-- Every point of the complementary open subscheme lies outside the range. -/
public theorem complementι_mem_compl_opensRange
    {A Z : Scheme.{u}} (i : A ⟶ Z) [IsOpenImmersion i] [IsClosedImmersion i]
    (x : complementScheme i) :
    complementι i x ∈ (i.opensRange : Set Z)ᶜ := by
  show x.1 ∈ (i.opensRange : Set Z)ᶜ
  exact x.2

end Scheme.Hom

/-- The graph of an étale object `W` over `U`, viewed inside the base change to `U` of `W`
regarded as étale over `X`. It is the unit `W ⟶ W ×_X U` of the adjunction between composition
with the structure morphism of `U` and base change along it. -/
public noncomputable def smallEtaleGraph
    (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)
    (U : SmallEtale B X hX)
    (W : SmallEtale B U.obj.left.1 U.obj.left.property) :
    W ⟶ (smallEtaleBaseChange B U.obj.hom).obj
      ((smallEtalePostcompose B X hX U).obj W) := by
  letI := hasPullbacks_bigEtaleSite B
  exact ObjectProperty.homMk ((Over.mapPullbackAdj U.obj.hom).unit.app W.obj)

/-- The graph of an étale object over `U` is an open immersion of schemes. -/
public theorem isOpenImmersion_map_smallEtaleGraph
    (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)
    (U : SmallEtale B X hX) [IsSeparated (B.inclusion.map U.obj.hom)]
    (W : SmallEtale B U.obj.left.1 U.obj.left.property) :
    IsOpenImmersion ((SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map
      (smallEtaleGraph B X hX U W)) := by
  let : Etale (B.inclusion.map U.obj.hom) := U.property
  show IsOpenImmersion (B.inclusion.map
    (pullback.lift (𝟙 (Over.left W.obj)) (Over.hom W.obj)
      (Category.id_comp (Over.hom W.obj ≫ U.obj.hom))))
  exact (bigEtaleGraphIntoPullback_isOpenAndClosed B W.obj.hom U.obj.hom).1

/-- When the structure morphism of `U` is separated, the graph of an étale object over `U` is a
closed immersion of schemes; with the previous lemma, its range is open and closed. -/
public theorem isClosedImmersion_map_smallEtaleGraph
    (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)
    (U : SmallEtale B X hX) [IsSeparated (B.inclusion.map U.obj.hom)]
    (W : SmallEtale B U.obj.left.1 U.obj.left.property) :
    IsClosedImmersion ((SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map
      (smallEtaleGraph B X hX U W)) := by
  let : Etale (B.inclusion.map U.obj.hom) := U.property
  show IsClosedImmersion (B.inclusion.map
    (pullback.lift (𝟙 (Over.left W.obj)) (Over.hom W.obj)
      (Category.id_comp (Over.hom W.obj ≫ U.obj.hom))))
  exact (bigEtaleGraphIntoPullback_isOpenAndClosed B W.obj.hom U.obj.hom).2

/-- The complement of the graph of `W` inside the base change `W ×_X U`, as an object of the
small étale site of `U`. It is an open subscheme of a scheme étale over `U`, hence étale over
`U`, and it is the second member of the covering along which a section is extended by zero. -/
public noncomputable def smallEtaleGraphComplement
    (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)
    (U : SmallEtale B X hX)
    [IsSeparated (B.inclusion.map U.obj.hom)]
    (W : SmallEtale B U.obj.left.1 U.obj.left.property) :
    SmallEtale B U.obj.left.1 U.obj.left.property := by
  letI := hasPullbacks_bigEtaleSite B
  letI := hasPullbacks_smallEtale B U.obj.left.1 U.obj.left.property
  let K := smallEtalePostcompose B X hX U
  let H := smallEtaleBaseChange B U.obj.hom
  let Z : SmallEtale B U.obj.left.1 U.obj.left.property := H.obj (K.obj W)
  let j := smallEtaleGraph B X hX U W
  let i := (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map j
  let : IsOpenImmersion i := isOpenImmersion_map_smallEtaleGraph B X hX U W
  let : IsClosedImmersion i := isClosedImmersion_map_smallEtaleGraph B X hX U W
  let d := Scheme.Hom.complementScheme i
  let dToZ := Scheme.Hom.complementι i
  letI : IsOpenImmersion dToZ := by
    dsimp [dToZ, Scheme.Hom.complementι, d, Scheme.Hom.complementScheme]
    infer_instance
  let d' : B.Scheme := B.obj d
    (Scheme.size_lt_of_isOpenImmersion dToZ Z.obj.left.property)
  let dToZ' : d' ⟶ Z.obj.left := ⟨dToZ⟩
  letI : Etale (B.inclusion.map dToZ') := by
    change Etale dToZ
    infer_instance
  refine ⟨Over.mk (dToZ' ≫ Z.obj.hom), ?_⟩
  change Etale (B.inclusion.map (dToZ' ≫ Z.obj.hom))
  rw [Functor.map_comp]
  infer_instance

/-- Two morphisms into a scheme with disjoint images — one an open immersion, the other landing
in the complement of its range — have no nonempty common refinement. -/
public theorem false_of_comp_eq_of_mem_compl_opensRange
    {S A D Z : Scheme.{u}} (i : A ⟶ Z) (j : D ⟶ Z)
    [IsOpenImmersion i] [IsClosedImmersion i]
    (hj : ∀ x : D, j x ∈ (i.opensRange : Set Z)ᶜ)
    (hS : Nonempty S) (f : S ⟶ A) (g : S ⟶ D)
    (hfg : f ≫ i = g ≫ j) : False := by
  obtain ⟨x⟩ := hS
  have hx : i (f x) ∈ (i.opensRange : Set Z) := by
    rw [Scheme.Hom.coe_opensRange]
    exact ⟨f x, rfl⟩
  have heq : i (f x) = j (g x) := by
    show (i.base.hom) (f.base.hom x) = (j.base.hom) (g.base.hom x)
    exact congrArg (fun k : S ⟶ Z => k x) hfg
  exact (hj (g x)) (heq ▸ hx)

/-- The inclusion of the complement of the graph of `W` into the base change `W ×_X U`. -/
public noncomputable def smallEtaleGraphComplementInto
    (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)
    (U : SmallEtale B X hX) [IsSeparated (B.inclusion.map U.obj.hom)]
    (W : SmallEtale B U.obj.left.1 U.obj.left.property) :
    smallEtaleGraphComplement B X hX U W ⟶
      (smallEtaleBaseChange B U.obj.hom).obj
        ((smallEtalePostcompose B X hX U).obj W) := by
  let K := smallEtalePostcompose B X hX U
  let H := smallEtaleBaseChange B U.obj.hom
  let Z : SmallEtale B U.obj.left.1 U.obj.left.property := H.obj (K.obj W)
  let i := (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map
    (smallEtaleGraph B X hX U W)
  let : IsOpenImmersion i := isOpenImmersion_map_smallEtaleGraph B X hX U W
  let : IsClosedImmersion i := isClosedImmersion_map_smallEtaleGraph B X hX U W
  let d := Scheme.Hom.complementScheme i
  let dToZ := Scheme.Hom.complementι i
  letI : IsOpenImmersion dToZ := by
    dsimp [dToZ, Scheme.Hom.complementι, d, Scheme.Hom.complementScheme]
    infer_instance
  let d' : B.Scheme := B.obj d (Scheme.size_lt_of_isOpenImmersion dToZ Z.obj.left.property)
  let dToZ' : d' ⟶ Z.obj.left := ⟨dToZ⟩
  exact ObjectProperty.homMk (Over.homMk dToZ' rfl)

/-- The graph of `W` and the complement of that graph are disjoint: no nonempty étale object
over `U` maps into both compatibly with their inclusions into `W ×_X U`. -/
public theorem smallEtaleGraphComplement_disjoint
    (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)
    (U : SmallEtale B X hX) [IsSeparated (B.inclusion.map U.obj.hom)]
    (W : SmallEtale B U.obj.left.1 U.obj.left.property)
    (S : SmallEtale B U.obj.left.1 U.obj.left.property)
    (hS : Nonempty S.obj.left.1)
    (a : S ⟶ W) (b : S ⟶ smallEtaleGraphComplement B X hX U W) :
    a ≫ smallEtaleGraph B X hX U W ≠
      b ≫ smallEtaleGraphComplementInto B X hX U W := by
  let T := SmallEtale.toScheme B U.obj.left.1 U.obj.left.property
  let i := T.map (smallEtaleGraph B X hX U W)
  have : IsOpenImmersion i := isOpenImmersion_map_smallEtaleGraph B X hX U W
  have : IsClosedImmersion i := isClosedImmersion_map_smallEtaleGraph B X hX U W
  let j := Scheme.Hom.complementι i
  intro hab
  have hfg : T.map a ≫ i = T.map b ≫ j := by
    calc
      T.map a ≫ i = T.map a ≫ T.map (smallEtaleGraph B X hX U W) := rfl
      _ = T.map (a ≫ smallEtaleGraph B X hX U W) := by rw [Functor.map_comp]
      _ = T.map (b ≫ smallEtaleGraphComplementInto B X hX U W) := congrArg T.map hab
      _ = T.map b ≫ T.map (smallEtaleGraphComplementInto B X hX U W) := by
        rw [Functor.map_comp]
      _ = T.map b ≫ j := rfl
  exact false_of_comp_eq_of_mem_compl_opensRange i j
    (Scheme.Hom.complementι_mem_compl_opensRange i) hS (T.map a) (T.map b) hfg

/-- The graph of `W` is a monomorphism of the small étale site of `U`: the forgetful functor
to schemes is faithful and sends it to an open immersion. -/
public theorem smallEtaleGraph_mono
    (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)
    (U : SmallEtale B X hX)
    [IsSeparated (B.inclusion.map U.obj.hom)]
    (W : SmallEtale B U.obj.left.1 U.obj.left.property) :
    Mono (smallEtaleGraph B X hX U W) := by
  let := hasPullbacks_bigEtaleSite B
  let := hasPullbacks_smallEtale B U.obj.left.1 U.obj.left.property
  let T := SmallEtale.toScheme B U.obj.left.1 U.obj.left.property
  have : IsOpenImmersion (T.map (smallEtaleGraph B X hX U W)) :=
    isOpenImmersion_map_smallEtaleGraph B X hX U W
  exact (Functor.reflectsMonomorphisms_of_faithful T).reflects _ inferInstance

/-- The inclusion of the complement of the graph of `W` is a monomorphism of the small étale
site of `U`. -/
public theorem smallEtaleGraphComplementInto_mono
    (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)
    (U : SmallEtale B X hX)
    [IsSeparated (B.inclusion.map U.obj.hom)]
    (W : SmallEtale B U.obj.left.1 U.obj.left.property) :
    Mono (smallEtaleGraphComplementInto B X hX U W) := by
  let := hasPullbacks_bigEtaleSite B
  let := hasPullbacks_smallEtale B U.obj.left.1 U.obj.left.property
  let T := SmallEtale.toScheme B U.obj.left.1 U.obj.left.property
  let i := T.map (smallEtaleGraph B X hX U W)
  have : IsOpenImmersion i := isOpenImmersion_map_smallEtaleGraph B X hX U W
  have : IsClosedImmersion i := isClosedImmersion_map_smallEtaleGraph B X hX U W
  have : IsOpenImmersion (T.map (smallEtaleGraphComplementInto B X hX U W)) := by
    dsimp [smallEtaleGraphComplementInto]
    show IsOpenImmersion (Scheme.Hom.complementι i)
    dsimp [Scheme.Hom.complementι, Scheme.Hom.complementScheme]
    infer_instance
  exact (Functor.reflectsMonomorphisms_of_faithful T).reflects _ inferInstance

/-- A morphism into the base change `W ×_X U` has image disjoint from the graph of `W` when no
nonempty étale test object over `U` maps compatibly into both. This is the étale-test-object
form of "the image avoids the graph" and it avoids naming the complementary open subscheme. -/
public def disjointFromSmallEtaleGraph
    (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)
    (U : SmallEtale B X hX)
    (W T : SmallEtale B U.obj.left.1 U.obj.left.property)
    (g : T ⟶ (smallEtaleBaseChange B U.obj.hom).obj
      ((smallEtalePostcompose B X hX U).obj W)) : Prop :=
  ∀ (S : SmallEtale B U.obj.left.1 U.obj.left.property),
    Nonempty (S.obj.left.1) → ∀ (a : S ⟶ W) (b : S ⟶ T),
      a ≫ smallEtaleGraph B X hX U W ≠ b ≫ g

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)
    (U : SmallEtale B X hX)
    [IsSeparated (B.inclusion.map U.obj.hom)]

omit [IsSeparated (B.inclusion.map U.obj.hom)] in
/-- A family of étale objects over `U` whose underlying family of schemes is an étale covering
generates a covering sieve of the small étale site of `U`. -/
public theorem smallEtale_sieve_mem_of_cover
    (Z : SmallEtale B U.obj.left.1 U.obj.left.property)
    (E : PreZeroHypercover.{u + 1} Z)
    (hE : IsEtaleCovering ⟨Z.obj.left,
      (E.map (SmallEtale.inclusion B U.obj.left.1 U.obj.left.property)).map
        (Over.forget _)⟩) :
    E.sieve₀ ∈ SmallEtale.topology B U.obj.left.1 U.obj.left.property Z := by
  let E₀ := (E.map (SmallEtale.inclusion B U.obj.left.1 U.obj.left.property)).map
    (Over.forget _)
  obtain ⟨⟨Rtarget, R⟩, hR, he⟩ := B.exists_covering_rep ⟨Z.obj.left, E₀⟩ hE
  obtain ⟨heq, he⟩ := he
  dsimp only at heq
  subst Rtarget
  change PreZeroHypercover.CombinatoriallyEquivalent E₀ R at he
  have hEt (a : R.I₀) : Etale (B.inclusion.map (R.f a)) :=
    ((Scheme.ofArrows_mem_precoverage_iff (@Etale)).mp hR.1).2 a
  let Rₛ : PreZeroHypercover Z := {
    I₀ := R.I₀
    X := fun a => ⟨Over.mk (R.f a ≫ Z.obj.hom), by
      show Etale (B.inclusion.map (R.f a ≫ Z.obj.hom))
      rw [Functor.map_comp]
      have := hEt a
      infer_instance⟩
    f := fun a => ObjectProperty.homMk (Over.homMk (R.f a)) }
  have hc : Rₛ.sieve₀ ∈
      SmallEtale.topology B U.obj.left.1 U.obj.left.property Z := by
    rw [Precoverage.mem_toGrothendieck_iff]
    apply Precoverage.Saturate.of
    exact ⟨Rₛ, rfl, hR⟩
  apply GrothendieckTopology.superset_covering _ _ hc
  rw [Sieve.generate_le_iff]
  rintro Y g ⟨a⟩
  obtain ⟨β, hX, hf⟩ := he.2
  let δ : Rₛ.X a ⟶ E.X (β a) := ObjectProperty.homMk
    (Over.homMk (eqToHom (hX a)) (by
      show eqToHom (hX a) ≫ (E.X (β a)).obj.hom = R.f a ≫ Z.obj.hom
      rw [hf a, Category.assoc]
      congr 1
      exact (E.f (β a)).hom.w.symm))
  have hδ : δ ≫ E.f (β a) = Rₛ.f a := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact (hf a).symm
  rw [← hδ]
  exact E.sieve₀.downward_closed (Sieve.ofArrows_mk _ _ (β a)) δ

omit [IsSeparated (B.inclusion.map U.obj.hom)] in
/-- The empty family covers an étale object over `U` whose underlying scheme is empty. -/
public theorem emptyCover_mem_smallEtaleTopology
    (S : SmallEtale B U.obj.left.1 U.obj.left.property)
    (hS : IsEmpty S.obj.left.1) :
    (PreZeroHypercover.empty.{w} S).sieve₀ ∈
      SmallEtale.topology B U.obj.left.1 U.obj.left.property S := by
  let := hasPullbacks_bigEtaleSite B
  let := hasPullbacks_smallEtale B U.obj.left.1 U.obj.left.property
  have : IsEmpty (B.inclusion.obj S.obj.left) := by simpa using hS
  let E : PreZeroHypercover S := PreZeroHypercover.empty S
  have hE : SmallEtale.IsCovering B U.obj.left.1 U.obj.left.property ⟨S, E⟩ := by
    show CovBounded IsEtaleCovering B.coveringBound
      ⟨_, (E.map (SmallEtale.inclusion B U.obj.left.1 U.obj.left.property)).map
        (BigEtaleOver.forget B U.obj.left.1 U.obj.left.property)⟩
    constructor
    · show (((E.map (SmallEtale.inclusion B U.obj.left.1 U.obj.left.property)).map
        (BigEtaleOver.forget B U.obj.left.1 U.obj.left.property)).map B.inclusion).presieve₀ ∈
        Scheme.precoverage (@Etale) (B.inclusion.obj S.obj.left)
      rw [Scheme.ofArrows_mem_precoverage_iff (@Etale)]
      exact ⟨fun x => isEmptyElim x, fun i => i.elim⟩
    · simp [E]
  have hpre : E.presieve₀ ∈
      SmallEtale.precoverage B U.obj.left.1 U.obj.left.property S :=
    (SmallEtale.mem_precoverage_iff B U.obj.left.1 U.obj.left.property).2
      ⟨E, rfl, hE⟩
  rw [Precoverage.mem_toGrothendieck_iff]
  simpa [E, PreZeroHypercover.sieve₀, PreZeroHypercover.presieve₀, Sieve.ofArrows] using
    Precoverage.Saturate.of _ _ hpre

/-- The graph of `W` and its complement cover the base change `W ×_X U` in the small étale
site of `U`: their underlying schemes cover it because the graph has open and closed range,
and both are étale over `U`. -/
public theorem graphComplementCover_mem_smallEtaleTopology
    (W : SmallEtale B U.obj.left.1 U.obj.left.property) :
    Sieve.ofTwoArrows (smallEtaleGraph B X hX U W)
      (smallEtaleGraphComplementInto B X hX U W) ∈
        SmallEtale.topology B U.obj.left.1 U.obj.left.property
          ((smallEtaleBaseChange B U.obj.hom).obj
            ((smallEtalePostcompose B X hX U).obj W)) := by
  classical
  let := hasPullbacks_bigEtaleSite B
  let := hasPullbacks_smallEtale B U.obj.left.1 U.obj.left.property
  let Z := (smallEtaleBaseChange B U.obj.hom).obj
    ((smallEtalePostcompose B X hX U).obj W)
  let D := smallEtaleGraphComplement B X hX U W
  let E : PreZeroHypercover Z := {
    I₀ := ULift.{u + 1} Bool
    X := fun b => match b.down with
      | false => W
      | true => D
    f := fun b => match b.down with
      | false => smallEtaleGraph B X hX U W
      | true => smallEtaleGraphComplementInto B X hX U W }
  let E₀ := (E.map (SmallEtale.inclusion B U.obj.left.1 U.obj.left.property)).map
    (BigEtaleOver.forget B U.obj.left.1 U.obj.left.property)
  let i := B.inclusion.map (E₀.f (ULift.up false))
  let : IsOpenImmersion i := isOpenImmersion_map_smallEtaleGraph B X hX U W
  let : IsClosedImmersion i := isClosedImmersion_map_smallEtaleGraph B X hX U W
  let C := Scheme.Cover.mkOfCovers (ULift.{u + 1} Bool)
    (E₀.map B.inclusion).X (E₀.map B.inclusion).f
    (by
      intro z
      by_cases hz : z ∈ (i.opensRange : Set _)
      · obtain ⟨y, hy⟩ := Scheme.Hom.mem_opensRange.mp hz
        exact ⟨ULift.up false, y, hy⟩
      · refine ⟨ULift.up true, ⟨z, ?_⟩, ?_⟩
        · show z ∈ (i.opensRange : Set _)ᶜ
          exact hz
        · show Scheme.Hom.complementι i ⟨z, hz⟩ = z
          rfl)
    (by
      rintro ⟨_ | _⟩
      · show Etale i
        infer_instance
      · show Etale (Scheme.Hom.complementι i)
        dsimp [Scheme.Hom.complementι, Scheme.Hom.complementScheme]
        infer_instance)
  have hEtale : IsEtaleCovering ⟨Z.obj.left, E₀⟩ := by
    show (E₀.map B.inclusion).presieve₀ ∈ Scheme.etalePrecoverage
      (B.inclusion.obj Z.obj.left)
    rw [show E₀.map B.inclusion = C.toPreZeroHypercover by ext <;> rfl]
    exact C.mem₀
  have hc := smallEtale_sieve_mem_of_cover B X hX U Z E hEtale
  apply GrothendieckTopology.superset_covering _ _ hc
  rw [Sieve.generate_le_iff]
  rintro Y f ⟨⟨_ | _⟩⟩
  exacts [Sieve.ofArrows_mk _ _ WalkingPair.left, Sieve.ofArrows_mk _ _ WalkingPair.right]

end AlgebraicGeometry

end
