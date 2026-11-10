module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Graph
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Adjunction
public import StacksFrontier.CategoryTheory.Sites.SectionGluingByZero
public import StacksFrontier.CategoryTheory.Sites.PullbackComparisonInjectivity
public import StacksFrontier.CategoryTheory.Sites.Sheafification.PreservesFiniteColimits
public import StacksFrontier.CategoryTheory.Sites.Sheafification.SectionsLocalDescription
public import Mathlib.CategoryTheory.Functor.EpiMono
public import StacksCore.Tactic.StacksAttribute

/-!
# Extension by zero maps to the direct image along a separated étale morphism

Let `j : U ⟶ X` be a separated étale morphism, viewed as an object of the small étale site of `X`.
Extension by zero `j_!` is the sheafification of the presheaf `V ↦ ⨁_{φ : V → U} F(V →^φ U)`, and
the direct image `j_*F` has sections `F(V ×_X U)` over `V`. For each `φ : V ⟶ U` the graph
`Γ_φ : V ⟶ V ×_X U` is an open and closed immersion, so a section of `F` over `V →^φ U` extends
uniquely to `V ×_X U` by prescribing it on the graph and zero off it. Those extensions are
compatible with restriction and natural in `F`, so they assemble into a map `j_!F ⟶ j_*F`.

The map is injective.

## Main definitions

* `AlgebraicGeometry.abelianExtensionByZeroToPushforward` and
  `AlgebraicGeometry.moduleExtensionByZeroToPushforward` — the comparison maps `j_! ⟶ j_*` for
  abelian sheaves and for sheaves of `Λ`-modules.
* `AlgebraicGeometry.smallEtaleGraphExtension` — extension of a section by zero along the graph.
* `AlgebraicGeometry.smallEtaleArrowsDisjoint` — disjointness of two morphisms `V ⟶ U`.

## Main results

* `AlgebraicGeometry.abelianExtensionByZeroToPushforward_mono` and
  `AlgebraicGeometry.moduleExtensionByZeroToPushforward_mono` — every component of the comparison
  map is a monomorphism.
* `AlgebraicGeometry.abelianExtensionByZeroToPushforward_graph` and
  `AlgebraicGeometry.moduleExtensionByZeroToPushforward_graph` — on the summand indexed by `W ⟶ U`
  the comparison restricts along the graph to the original section.
* `AlgebraicGeometry.abelianExtensionByZeroToPushforward_graph_compl` and
  `AlgebraicGeometry.moduleExtensionByZeroToPushforward_graph_compl` — the same section restricts
  to zero away from that graph.
* `AlgebraicGeometry.mono_of_graph_unit` — the injectivity criterion the two `_mono` results are
  instances of.

## Implementation notes

The comparison maps are total: the construction uses separatedness of `U ⟶ X`, and without it the
map is defined to be zero. All four statements characterising the maps assume separatedness. The
graph restriction and the complementary vanishing together pin the maps down on every summand of
the presheaf extension; the vanishing is stated with the étale-test-object criterion
`AlgebraicGeometry.disjointFromSmallEtaleGraph` rather than by naming the complementary open
subscheme.

### The transparency option

The option `backward.isDefEq.respectTransparency` is disabled for this file. The objects
`((smallEtaleBaseChange B U.obj.hom).obj Q).obj.left` and `pullback Q.obj.hom U.obj.hom` are the
same object carrying two different chosen limit cones; they are defeq at default transparency only,
while `rw` and `simp` check type-correctness at `implicit` transparency and instance synthesis runs
at `instances`. Bridging the two spellings would mean unfolding
`CategoryTheory.Limits.getLimitCone`, which Mathlib does not expose.

## References

* [Stacks Project, Tag 0F4L](https://stacks.math.columbia.edu/tag/0F4L)
* [Stacks Project, Tag 0F4K](https://stacks.math.columbia.edu/tag/0F4K)
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w x

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)
    (U : SmallEtale B X hX)
    [IsSeparated (B.inclusion.map U.obj.hom)]

/-- A section of `F` on `W` extended over the base change `W ×_X U` by zero: it restricts to the
given section along the graph of `W` and to zero on the complement of that graph. -/
public noncomputable def smallEtaleGraphExtension
    {Acat : Type v} [Category.{w} Acat] [Preadditive Acat]
    (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
      Acat)
    (W : SmallEtale B U.obj.left.1 U.obj.left.property)
    (hcover : Sieve.ofTwoArrows (smallEtaleGraph B X hX U W)
      (smallEtaleGraphComplementInto B X hX U W) ∈
        SmallEtale.topology B U.obj.left.1 U.obj.left.property
          ((smallEtaleBaseChange B U.obj.hom).obj
            ((smallEtalePostcompose B X hX U).obj W))) :
    F.obj.obj (Opposite.op W) ⟶ F.obj.obj (Opposite.op
      ((smallEtaleBaseChange B U.obj.hom).obj
        ((smallEtalePostcompose B X hX U).obj W))) := by
  let := hasPullbacks_bigEtaleSite B
  let := hasPullbacks_smallEtale B U.obj.left.1 U.obj.left.property
  let J := SmallEtale.topology B U.obj.left.1 U.obj.left.property
  let Z := (smallEtaleBaseChange B U.obj.hom).obj
    ((smallEtalePostcompose B X hX U).obj W)
  let D := smallEtaleGraphComplement B X hX U W
  let i := smallEtaleGraph B X hX U W
  let j := smallEtaleGraphComplementInto B X hX U W
  let : Mono i := smallEtaleGraph_mono B X hX U W
  let : Mono j := smallEtaleGraphComplementInto_mono B X hX U W
  have hcompat := Presheaf.glueSectionByZero_compat F.obj i j
      (𝟙 (F.obj.obj (Opposite.op W))) (by
    intro S f g hfg
    by_cases hne : Nonempty S.obj.left.1
    · exact False.elim (smallEtaleGraphComplement_disjoint B X hX U W S hne f g hfg)
    · have hEmpty : IsEmpty S.obj.left.1 := not_nonempty_iff.mp hne
      simpa only [Category.id_comp] using
        (Presheaf.eq_zero_of_isEmptyCover J F.property
          (emptyCover_mem_smallEtaleTopology.{u, u + 1} B X hX U S hEmpty)
          (F.obj.map (Opposite.op f))))
  exact Presheaf.glueSectionByZero J F.obj F.property i j hcover
    (𝟙 (F.obj.obj (Opposite.op W))) hcompat

/-- The extension by zero of a section restricts along the graph to the section itself. -/
public theorem smallEtaleGraphExtension_graph
    {Acat : Type v} [Category.{w} Acat] [Preadditive Acat]
    (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
      Acat)
    (W : SmallEtale B U.obj.left.1 U.obj.left.property)
    (hcover : Sieve.ofTwoArrows (smallEtaleGraph B X hX U W)
      (smallEtaleGraphComplementInto B X hX U W) ∈
        SmallEtale.topology B U.obj.left.1 U.obj.left.property
          ((smallEtaleBaseChange B U.obj.hom).obj
            ((smallEtalePostcompose B X hX U).obj W))) :
    smallEtaleGraphExtension B X hX U F W hcover ≫
      F.obj.map (smallEtaleGraph B X hX U W).op =
        𝟙 (F.obj.obj (Opposite.op W)) := by
  have := smallEtaleGraph_mono B X hX U W
  have := smallEtaleGraphComplementInto_mono B X hX U W
  exact Presheaf.glueSectionByZero_graph _ _ F.property _ _ hcover _ _

/-- The extension by zero of a section restricts to zero on the complement of the graph. -/
public theorem smallEtaleGraphExtension_compl
    {Acat : Type v} [Category.{w} Acat] [Preadditive Acat]
    (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
      Acat)
    (W : SmallEtale B U.obj.left.1 U.obj.left.property)
    (hcover : Sieve.ofTwoArrows (smallEtaleGraph B X hX U W)
      (smallEtaleGraphComplementInto B X hX U W) ∈
        SmallEtale.topology B U.obj.left.1 U.obj.left.property
          ((smallEtaleBaseChange B U.obj.hom).obj
            ((smallEtalePostcompose B X hX U).obj W))) :
    smallEtaleGraphExtension B X hX U F W hcover ≫
      F.obj.map (smallEtaleGraphComplementInto B X hX U W).op = 0 := by
  have := smallEtaleGraph_mono B X hX U W
  have := smallEtaleGraphComplementInto_mono B X hX U W
  exact Presheaf.glueSectionByZero_compl _ _ F.property _ _ hcover _ _

omit [IsSeparated (B.inclusion.map U.obj.hom)] in
/-- The graph is natural in the étale object over `U`. -/
public theorem smallEtaleGraph_naturality
    {W W' : SmallEtale B U.obj.left.1 U.obj.left.property} (f : W ⟶ W') :
    f ≫ smallEtaleGraph B X hX U W' = smallEtaleGraph B X hX U W ≫
      (smallEtaleBaseChange B U.obj.hom).map
        ((smallEtalePostcompose B X hX U).map f) := by
  apply ObjectProperty.hom_ext
  exact (Over.mapPullbackAdj U.obj.hom).unit.naturality f.hom

omit [IsSeparated (B.inclusion.map U.obj.hom)] in
/-- A morphism into `W ×_X U` whose composite with the base change of `f : W ⟶ W'` factors through
the graph of `W'` already factors through the graph of `W`. -/
public theorem smallEtaleGraph_lift
    {W W' S : SmallEtale B U.obj.left.1 U.obj.left.property}
    (f : W ⟶ W') (a : S ⟶ W')
    (b : S ⟶ (smallEtaleBaseChange B U.obj.hom).obj
      ((smallEtalePostcompose B X hX U).obj W))
    (h : a ≫ smallEtaleGraph B X hX U W' = b ≫
      (smallEtaleBaseChange B U.obj.hom).map
        ((smallEtalePostcompose B X hX U).map f)) :
    ∃ c : S ⟶ W, c ≫ smallEtaleGraph B X hX U W = b := by
  have h₀ := congrArg (fun k => k.hom.left) h
  have hfst := congrArg (fun k => k ≫ pullback.fst
    ((smallEtalePostcompose B X hX U).obj W').obj.hom U.obj.hom) h₀
  have ha : a.hom.left = b.hom.left ≫
      pullback.fst ((smallEtalePostcompose B X hX U).obj W).obj.hom U.obj.hom ≫
      f.hom.left := by
    change (a.hom.left ≫ pullback.lift (𝟙 _) W'.obj.hom _) ≫ pullback.fst _ _ =
      (b.hom.left ≫ pullback.lift (pullback.fst _ _ ≫ f.hom.left)
        (pullback.snd _ _) _) ≫ pullback.fst _ _ at hfst
    simpa only [Category.assoc, pullback.lift_fst, Category.comp_id,
      SmallEtale.inclusion, ObjectProperty.ι, inducedFunctor] using hfst
  let c : S ⟶ W := ObjectProperty.homMk (Over.homMk
    (b.hom.left ≫ pullback.fst ((smallEtalePostcompose B X hX U).obj W).obj.hom U.obj.hom) (by
      calc
        _ = (b.hom.left ≫ pullback.fst _ _) ≫ (f.hom.left ≫ W'.obj.hom) :=
          congrArg ((b.hom.left ≫ pullback.fst _ _) ≫ ·) f.hom.w.symm
        _ = a.hom.left ≫ W'.obj.hom := by
          simpa only [Category.assoc, SmallEtale.inclusion, ObjectProperty.ι, inducedFunctor]
            using congrArg (fun k => k ≫ W'.obj.hom) ha.symm
        _ = S.obj.hom := a.hom.w))
  refine ⟨c, ?_⟩
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change (c.hom.left ≫ pullback.lift (𝟙 _) W.obj.hom _) ≫ pullback.fst _ _ = _
    simp [c, Category.assoc, smallEtalePostcompose]
  · change (c.hom.left ≫
      pullback.lift (𝟙 W.obj.left) W.obj.hom _) ≫
        pullback.snd ((smallEtalePostcompose B X hX U).obj W).obj.hom U.obj.hom = _
    rw [Category.assoc, pullback.lift_snd]
    exact c.hom.w.trans b.hom.w.symm

/-- The extension by zero of a section restricts to zero along every morphism into `W ×_X U` whose
image avoids the graph. -/
public theorem smallEtaleGraphExtension_disjoint
    {Acat : Type v} [Category.{w} Acat] [Preadditive Acat]
    (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) Acat)
    (W T : SmallEtale B U.obj.left.1 U.obj.left.property)
    (g : T ⟶ (smallEtaleBaseChange B U.obj.hom).obj
      ((smallEtalePostcompose B X hX U).obj W))
    (hg : disjointFromSmallEtaleGraph B X hX U W T g) :
    smallEtaleGraphExtension B X hX U F W
      (graphComplementCover_mem_smallEtaleTopology B X hX U W) ≫ F.obj.map g.op = 0 := by
  let J := SmallEtale.topology B U.obj.left.1 U.obj.left.property
  let i := smallEtaleGraph B X hX U W
  let j := smallEtaleGraphComplementInto B X hX U W
  have hc := graphComplementCover_mem_smallEtaleTopology B X hX U W
  apply F.property.hom_ext ⟨(Sieve.ofTwoArrows i j).pullback g, J.pullback_stable g hc⟩
  intro t
  obtain ⟨k, a, ha⟩ := Sieve.ofArrows.exists t.hf
  cases k with
  | left =>
    have hempty : IsEmpty t.Y.obj.left.1 := by
      rw [← not_nonempty_iff]
      intro hn
      exact hg t.Y hn a t.f ha.symm
    have hz : F.obj.map t.f.op = 0 :=
      Presheaf.eq_zero_of_isEmptyCover J F.property
        (emptyCover_mem_smallEtaleTopology.{u, u + 1} B X hX U t.Y hempty) _
    simp [hz]
  | right =>
    change t.f ≫ g = a ≫ j at ha
    simp only [Category.assoc, ← Functor.map_comp, ← op_comp, ha]
    change _ ≫ F.obj.map (a ≫ smallEtaleGraphComplementInto B X hX U W).op = _
    change _ ≫ F.obj.map ((smallEtaleGraphComplementInto B X hX U W).op ≫ a.op) = _
    rw [Functor.map_comp, ← Category.assoc, smallEtaleGraphExtension_compl]
    simp

/-- Extension by zero is compatible with restriction along a morphism `W ⟶ W'` of étale objects
over `U`. -/
public theorem smallEtaleGraphExtension_map
    {Acat : Type v} [Category.{w} Acat] [Preadditive Acat]
    (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) Acat)
    {W W' : SmallEtale B U.obj.left.1 U.obj.left.property} (f : W ⟶ W') :
    F.obj.map f.op ≫ smallEtaleGraphExtension B X hX U F W
      (graphComplementCover_mem_smallEtaleTopology B X hX U W) =
    smallEtaleGraphExtension B X hX U F W'
      (graphComplementCover_mem_smallEtaleTopology B X hX U W') ≫
      F.obj.map ((smallEtaleBaseChange B U.obj.hom).map
        ((smallEtalePostcompose B X hX U).map f)).op := by
  apply Presheaf.glueSectionByZero_unique
    (SmallEtale.topology B U.obj.left.1 U.obj.left.property) F.obj F.property
    (smallEtaleGraph B X hX U W) (smallEtaleGraphComplementInto B X hX U W)
    (graphComplementCover_mem_smallEtaleTopology B X hX U W)
  · simp only [Category.assoc, smallEtaleGraphExtension_graph, Category.comp_id]
    rw [← Functor.map_comp, ← op_comp, ← smallEtaleGraph_naturality,
      op_comp, Functor.map_comp, ← Category.assoc, smallEtaleGraphExtension_graph,
      Category.id_comp]
  · simp only [Category.assoc, smallEtaleGraphExtension_compl, comp_zero]
    rw [← Functor.map_comp, ← op_comp]
    symm
    apply smallEtaleGraphExtension_disjoint
    intro S hn a b hab
    obtain ⟨c, hc⟩ := smallEtaleGraph_lift B X hX U f a
      (b ≫ smallEtaleGraphComplementInto B X hX U W) (by
        simpa only [Category.assoc] using hab)
    exact smallEtaleGraphComplement_disjoint B X hX U W S hn c b hc

/-- Extension by zero is natural in the sheaf. -/
public theorem smallEtaleGraphExtension_naturality
    {Acat : Type v} [Category.{w} Acat] [Preadditive Acat]
    {F G : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) Acat}
    (φ : F ⟶ G)
    (W : SmallEtale B U.obj.left.1 U.obj.left.property) :
    φ.hom.app (Opposite.op W) ≫ smallEtaleGraphExtension B X hX U G W
      (graphComplementCover_mem_smallEtaleTopology B X hX U W) =
    smallEtaleGraphExtension B X hX U F W
      (graphComplementCover_mem_smallEtaleTopology B X hX U W) ≫
        φ.hom.app (Opposite.op
          ((smallEtaleBaseChange B U.obj.hom).obj
            ((smallEtalePostcompose B X hX U).obj W))) := by
  apply Presheaf.glueSectionByZero_unique
    (SmallEtale.topology B U.obj.left.1 U.obj.left.property) G.obj G.property
    (smallEtaleGraph B X hX U W) (smallEtaleGraphComplementInto B X hX U W)
    (graphComplementCover_mem_smallEtaleTopology B X hX U W)
  · simp only [Category.assoc, smallEtaleGraphExtension_graph, Category.comp_id]
    rw [← φ.hom.naturality, ← Category.assoc, smallEtaleGraphExtension_graph,
      Category.id_comp]
  · simp only [Category.assoc, smallEtaleGraphExtension_compl, comp_zero]
    rw [← φ.hom.naturality, ← Category.assoc, smallEtaleGraphExtension_compl,
      zero_comp]

/-- Extension by zero of sections assembles into a natural transformation from the identity to
restriction along `U ⟶ X` composed with the direct image along base change. -/
public noncomputable def smallEtaleGraphExtensionUnit
    (Acat : Type v) [Category.{w} Acat] [Preadditive Acat] :
    let := smallEtaleBaseChange_isContinuous B U.obj.hom
    𝟭 (Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) Acat) ⟶
      (smallEtaleBaseChange B U.obj.hom).sheafPushforwardContinuous
        Acat (SmallEtale.topology B X hX)
        (SmallEtale.topology B U.obj.left.1 U.obj.left.property) ⋙
      (smallEtalePostcompose B X hX U).sheafPushforwardContinuous
        Acat (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
        (SmallEtale.topology B X hX) := by
  let := smallEtaleBaseChange_isContinuous B U.obj.hom
  refine { app := ?_, naturality := ?_ }
  · intro F
    refine
      { hom :=
          { app := fun W =>
              smallEtaleGraphExtension B X hX U F W.unop
                (graphComplementCover_mem_smallEtaleTopology B X hX U W.unop)
            naturality := ?_ } }
    intro W W' f
    exact smallEtaleGraphExtension_map B X hX U F f.unop
  · intro F G φ
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext W
    exact smallEtaleGraphExtension_naturality B X hX U φ W.unop

/-- An étale object `V` over `X` together with a morphism `V ⟶ U` over `X`, regarded as an étale
object over `U`. -/
public def smallEtaleLift
    (V : SmallEtale B X hX) (φ : V ⟶ U) :
    SmallEtale B U.obj.left.1 U.obj.left.property :=
  ⟨Over.mk φ.hom.left, by
    change Etale (B.inclusion.map φ.hom.left)
    apply MorphismProperty.of_postcomp (W' := @Etale) (@Etale) _
      (B.inclusion.map U.obj.hom) U.property
    rw [← Functor.map_comp, φ.hom.w]
    exact V.property⟩

/-- Regarding `V ⟶ U` as an étale object over `U` and then composing with `U ⟶ X` recovers `V`. -/
public def smallEtaleLiftPostIso
    (V : SmallEtale B X hX) (φ : V ⟶ U) :
    (smallEtalePostcompose B X hX U).obj
      (smallEtaleLift B X hX U V φ) ≅ V :=
  ObjectProperty.isoMk _ (Over.isoMk (Iso.refl _) (by
    change 𝟙 V.obj.left ≫ V.obj.hom = φ.hom.left ≫ U.obj.hom
    simpa only [Category.id_comp] using φ.hom.w.symm))

/-- A morphism `V' ⟶ V` over `X` induces a morphism of the corresponding étale objects over `U`. -/
public def smallEtaleLiftMap
    {V V' : SmallEtale B X hX} (f : V' ⟶ V) (φ : V ⟶ U) :
    smallEtaleLift B X hX U V' (f ≫ φ) ⟶ smallEtaleLift B X hX U V φ :=
  ObjectProperty.homMk (Over.homMk f.hom.left (by rfl))

omit [IsSeparated (B.inclusion.map U.obj.hom)] in
/-- The identification `smallEtaleLiftPostIso` is natural in `V`. -/
public theorem smallEtaleLiftPostIso_naturality
    {V V' : SmallEtale B X hX} (f : V' ⟶ V) (φ : V ⟶ U) :
    (smallEtalePostcompose B X hX U).map
        (smallEtaleLiftMap B X hX U f φ) ≫
      (smallEtaleLiftPostIso B X hX U V φ).hom =
    (smallEtaleLiftPostIso B X hX U V' (f ≫ φ)).hom ≫ f := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  simp [smallEtaleLiftMap, smallEtaleLiftPostIso, smallEtalePostcompose]

/-- The graph of `V ⟶ U`, transported along `smallEtaleLiftPostIso` into the base change of `V` to
`U`. -/
public def smallEtaleLiftGraph
    (V : SmallEtale B X hX) (φ : V ⟶ U) :
    smallEtaleLift B X hX U V φ ⟶
      (smallEtaleBaseChange B U.obj.hom).obj V :=
  smallEtaleGraph B X hX U (smallEtaleLift B X hX U V φ) ≫
    (smallEtaleBaseChange B U.obj.hom).map
      (smallEtaleLiftPostIso B X hX U V φ).hom

omit [IsSeparated (B.inclusion.map U.obj.hom)] in
/-- The transported graph is natural in `V`. -/
public theorem smallEtaleLiftGraph_naturality
    {V V' : SmallEtale B X hX} (f : V' ⟶ V) (φ : V ⟶ U) :
    smallEtaleLiftMap B X hX U f φ ≫ smallEtaleLiftGraph B X hX U V φ =
    smallEtaleLiftGraph B X hX U V' (f ≫ φ) ≫
      (smallEtaleBaseChange B U.obj.hom).map f := by
  unfold smallEtaleLiftGraph
  rw [← Category.assoc, smallEtaleGraph_naturality]
  simp only [Category.assoc, ← Functor.map_comp, smallEtaleLiftPostIso_naturality]

/-- Extension by zero of a section along the transported graph of `V ⟶ U`. -/
public def smallEtaleLiftExtension
    {Acat : Type v} [Category.{w} Acat] [Preadditive Acat]
    (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) Acat)
    (V : SmallEtale B X hX) (φ : V ⟶ U) :
    F.obj.obj (Opposite.op (smallEtaleLift B X hX U V φ)) ⟶
      F.obj.obj (Opposite.op
        ((smallEtaleBaseChange B U.obj.hom).obj V)) :=
  smallEtaleGraphExtension B X hX U F (smallEtaleLift B X hX U V φ)
      (graphComplementCover_mem_smallEtaleTopology B X hX U _) ≫
    F.obj.map ((smallEtaleBaseChange B U.obj.hom).map
      (smallEtaleLiftPostIso B X hX U V φ).inv).op

/-- The extension restricts along the transported graph to the section itself. -/
public theorem smallEtaleLiftExtension_graph
    {Acat : Type v} [Category.{w} Acat] [Preadditive Acat]
    (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) Acat)
    (V : SmallEtale B X hX) (φ : V ⟶ U) :
    smallEtaleLiftExtension B X hX U F V φ ≫
      F.obj.map (smallEtaleLiftGraph B X hX U V φ).op = 𝟙 _ := by
  simp only [smallEtaleLiftExtension, smallEtaleLiftGraph, Category.assoc, ← op_comp,
    ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.comp_id,
    smallEtaleGraphExtension_graph]

/-- The extension is compatible with restriction along a morphism `V' ⟶ V` over `X`. -/
public theorem smallEtaleLiftExtension_map
    {Acat : Type v} [Category.{w} Acat] [Preadditive Acat]
    (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) Acat)
    {V V' : SmallEtale B X hX} (f : V' ⟶ V) (φ : V ⟶ U) :
    F.obj.map (smallEtaleLiftMap B X hX U f φ).op ≫
        smallEtaleLiftExtension B X hX U F V' (f ≫ φ) =
    smallEtaleLiftExtension B X hX U F V φ ≫
      F.obj.map ((smallEtaleBaseChange B U.obj.hom).map f).op := by
  unfold smallEtaleLiftExtension
  rw [← Category.assoc, smallEtaleGraphExtension_map]
  simp only [Category.assoc, ← Functor.map_comp, ← op_comp, ← Functor.map_comp]
  congr 4

omit [IsSeparated (B.inclusion.map U.obj.hom)] in
/-- The transported graph of `V ⟶ U` is a section of the first projection of `V ×_X U`. -/
public theorem smallEtaleLiftGraph_fst
    (V : SmallEtale B X hX) (φ : V ⟶ U) :
    (smallEtaleLiftGraph B X hX U V φ).hom.left ≫
      pullback.fst V.obj.hom U.obj.hom = 𝟙 V.obj.left := by
  simp [smallEtaleLiftGraph, smallEtaleGraph, smallEtaleLiftPostIso,
    smallEtaleBaseChange,
    smallEtalePostcompose, Over.mapPullbackAdj,
    Over.pullback, smallEtaleLift, Category.assoc]

omit [IsSeparated (B.inclusion.map U.obj.hom)] in
/-- Two morphisms into the base change of `V`, one through the transported graph of `φ` and the
other through that of `ψ`, agree exactly when their underlying morphisms of schemes do. -/
public theorem smallEtaleLiftGraph_comp_eq_iff
    (V : SmallEtale B X hX) (φ ψ : V ⟶ U)
    (T : SmallEtale B U.obj.left.1 U.obj.left.property)
    (a : T ⟶ smallEtaleLift B X hX U V φ)
    (b : T ⟶ smallEtaleLift B X hX U V ψ) :
    a ≫ smallEtaleLiftGraph B X hX U V φ =
      b ≫ smallEtaleLiftGraph B X hX U V ψ ↔ a.hom.left = b.hom.left := by
  constructor
  · intro h
    have hh := congrArg (fun t => t.hom.left ≫ pullback.fst V.obj.hom U.obj.hom) h
    change (a.hom.left ≫ _) ≫ _ = (b.hom.left ≫ _) ≫ _ at hh
    rw [Category.assoc, smallEtaleLiftGraph_fst, Category.assoc,
      smallEtaleLiftGraph_fst] at hh
    exact (Category.comp_id _).symm.trans (hh.trans (Category.comp_id _))
  · intro h
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · change (a.hom.left ≫ _) ≫ _ = (b.hom.left ≫ _) ≫ _
      change (a.hom.left ≫ (smallEtaleLiftGraph B X hX U V φ).hom.left) ≫
        pullback.fst V.obj.hom U.obj.hom =
        (b.hom.left ≫ (smallEtaleLiftGraph B X hX U V ψ).hom.left) ≫
        pullback.fst V.obj.hom U.obj.hom
      rw [Category.assoc, smallEtaleLiftGraph_fst, Category.assoc, smallEtaleLiftGraph_fst]
      exact (Category.comp_id _).trans (h.trans (Category.comp_id _).symm)
    · exact (a ≫ smallEtaleLiftGraph B X hX U V φ).hom.w.trans
        (b ≫ smallEtaleLiftGraph B X hX U V ψ).hom.w.symm

/-- Two morphisms `V ⟶ U` over `X` are disjoint when no nonempty étale object over `U` maps to `V`
compatibly with both of them; equivalently their equalizer, an open and closed subscheme of `V`, is
empty. -/
public def smallEtaleArrowsDisjoint
    (V : SmallEtale B X hX) (φ ψ : V ⟶ U) : Prop :=
  ∀ (T : SmallEtale B U.obj.left.1 U.obj.left.property),
    Nonempty T.obj.left.1 →
    ∀ (a : T ⟶ smallEtaleLift B X hX U V φ)
      (b : T ⟶ smallEtaleLift B X hX U V ψ), a.hom.left ≠ b.hom.left

omit [IsSeparated (B.inclusion.map U.obj.hom)] in
/-- Disjointness of two morphisms `V ⟶ U` is symmetric. -/
public theorem smallEtaleArrowsDisjoint_symm
    (V : SmallEtale B X hX) (φ ψ : V ⟶ U)
    (h : smallEtaleArrowsDisjoint B X hX U V φ ψ) :
    smallEtaleArrowsDisjoint B X hX U V ψ φ :=
  fun T hn a b hab => h T hn b a hab.symm

/-- The extension along the graph of `φ` restricts to zero along the graph of a morphism `ψ`
disjoint from `φ`. -/
public theorem smallEtaleLiftExtension_disjoint
    {Acat : Type v} [Category.{w} Acat] [Preadditive Acat]
    (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) Acat)
    (V : SmallEtale B X hX) (φ ψ : V ⟶ U)
    (h : smallEtaleArrowsDisjoint B X hX U V φ ψ) :
    smallEtaleLiftExtension B X hX U F V φ ≫
      F.obj.map (smallEtaleLiftGraph B X hX U V ψ).op = 0 := by
  unfold smallEtaleLiftExtension
  rw [Category.assoc, ← Functor.map_comp, ← op_comp]
  apply smallEtaleGraphExtension_disjoint
  intro T hn a b hab
  have hh := congrArg (· ≫
    (smallEtaleBaseChange B U.obj.hom).map
      (smallEtaleLiftPostIso B X hX U V φ).hom) hab
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.comp_id] at hh
  exact h T hn a b ((smallEtaleLiftGraph_comp_eq_iff B X hX U V φ ψ T a b).mp hh)

/-- The component at `V ⟶ U` of a natural transformation out of a sheaf on the small étale site of
`U`, transported to sections over `V`. -/
public def smallEtaleLiftUnit
    {Acat : Type v} [Category.{w} Acat]
    (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) Acat)
    (H : Sheaf (SmallEtale.topology B X hX) Acat)
    (η : F.obj ⟶ (smallEtalePostcompose B X hX U).op ⋙ H.obj)
    (V : SmallEtale B X hX) (φ : V ⟶ U) :
    F.obj.obj (Opposite.op (smallEtaleLift B X hX U V φ)) ⟶ H.obj.obj (Opposite.op V) :=
  η.app _ ≫ H.obj.map (smallEtaleLiftPostIso B X hX U V φ).inv.op

omit [IsSeparated (B.inclusion.map U.obj.hom)] in
/-- That component is compatible with restriction along a morphism `V' ⟶ V` over `X`. -/
public theorem smallEtaleLiftUnit_map
    {Acat : Type v} [Category.{w} Acat]
    (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) Acat)
    (H : Sheaf (SmallEtale.topology B X hX) Acat)
    (η : F.obj ⟶ (smallEtalePostcompose B X hX U).op ⋙ H.obj)
    {V V' : SmallEtale B X hX} (f : V' ⟶ V) (φ : V ⟶ U) :
    F.obj.map (smallEtaleLiftMap B X hX U f φ).op ≫
        smallEtaleLiftUnit B X hX U F H η V' (f ≫ φ) =
    smallEtaleLiftUnit B X hX U F H η V φ ≫ H.obj.map f.op := by
  unfold smallEtaleLiftUnit
  rw [← Category.assoc, η.naturality]
  simp only [Functor.comp_map, Functor.op_map, Category.assoc,
    ← Functor.map_comp, ← op_comp]
  congr 3

/-- Two sections over `V` of a sheaf on the small étale site of `X` agree as soon as they agree
after restriction to every `V' ⟶ V` on which two given morphisms `φ, ψ : V ⟶ U` either become equal
or become disjoint. -/
public theorem hom_ext_of_equal_or_disjoint
    {Acat : Type v} [Category.{w} Acat]
    (H : Sheaf (SmallEtale.topology B X hX) Acat)
    (V : SmallEtale B X hX) (φ ψ : V ⟶ U)
    {E : Acat} (a b : E ⟶ H.obj.obj (Opposite.op V))
    (hab : ∀ (V' : SmallEtale B X hX) (f : V' ⟶ V),
      (f ≫ φ = f ≫ ψ ∨ smallEtaleArrowsDisjoint B X hX U V' (f ≫ φ) (f ≫ ψ)) →
      a ≫ H.obj.map f.op = b ≫ H.obj.map f.op) : a = b := by
  let G := smallEtalePostcompose B X hX U
  let K := smallEtaleBaseChange B U.obj.hom
  let Wφ := smallEtaleLift B X hX U V φ
  let Wψ := smallEtaleLift B X hX U V ψ
  let d := smallEtaleLiftGraph B X hX U V φ ≫
    K.map (smallEtaleLiftPostIso B X hX U V ψ).inv
  let J := SmallEtale.topology B U.obj.left.1 U.obj.left.property
  let R := G.sheafPushforwardContinuous Acat J (SmallEtale.topology B X hX)
  let hc := J.pullback_stable d (graphComplementCover_mem_smallEtaleTopology B X hX U Wψ)
  apply (cancel_mono (H.obj.map (smallEtaleLiftPostIso B X hX U V φ).hom.op)).1
  apply (R.obj H).property.hom_ext ⟨_, hc⟩
  intro t
  let f : G.obj t.Y ⟶ V := G.map t.f ≫ (smallEtaleLiftPostIso B X hX U V φ).hom
  have key : t.f ≫ smallEtaleLiftGraph B X hX U V φ =
      (t.f ≫ d) ≫ K.map (smallEtaleLiftPostIso B X hX U V ψ).hom := by
    simp only [d, Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id]
    exact (Category.comp_id _).symm
  have hsplit : f ≫ φ = f ≫ ψ ∨
      smallEtaleArrowsDisjoint B X hX U (G.obj t.Y) (f ≫ φ) (f ≫ ψ) := by
    obtain ⟨k, c, htc⟩ := Sieve.ofArrows.exists t.hf
    cases k with
    | left =>
      left
      have he : t.f ≫ smallEtaleLiftGraph B X hX U V φ =
          c ≫ smallEtaleLiftGraph B X hX U V ψ :=
        key.trans ((congrArg (· ≫ K.map (smallEtaleLiftPostIso B X hX U V ψ).hom) htc).trans
          (Category.assoc _ _ _))
      have he' := (smallEtaleLiftGraph_comp_eq_iff B X hX U V φ ψ t.Y t.f c).mp he
      apply ObjectProperty.hom_ext
      apply Over.OverMorphism.ext
      change t.f.hom.left ≫ φ.hom.left = t.f.hom.left ≫ ψ.hom.left
      have hc : c.hom.left ≫ ψ.hom.left = t.Y.obj.hom := c.hom.w
      rw [← he'] at hc
      exact t.f.hom.w.trans hc.symm
    | right =>
      right
      intro S hn p q hpq
      let z : S ⟶ t.Y := ObjectProperty.homMk (Over.homMk p.hom.left (by
        have hp := p.hom.w
        change p.hom.left ≫ (t.f.hom.left ≫ φ.hom.left) = S.obj.hom at hp
        have ht : t.f.hom.left ≫ φ.hom.left = t.Y.obj.hom := t.f.hom.w
        rw [ht] at hp
        exact hp))
      let z' : S ⟶ Wψ := ObjectProperty.homMk (Over.homMk
        (q.hom.left ≫ t.f.hom.left) (by
          have hq := q.hom.w
          change q.hom.left ≫ (t.f.hom.left ≫ ψ.hom.left) = S.obj.hom at hq
          exact (Category.assoc _ _ _).trans hq))
      have he : (z ≫ t.f) ≫ smallEtaleLiftGraph B X hX U V φ =
          z' ≫ smallEtaleLiftGraph B X hX U V ψ := by
        apply (smallEtaleLiftGraph_comp_eq_iff B X hX U V φ ψ S _ _).2
        change p.hom.left ≫ t.f.hom.left = q.hom.left ≫ t.f.hom.left
        rw [hpq]
      apply smallEtaleGraphComplement_disjoint B X hX U Wψ S hn z' (z ≫ c)
      apply (cancel_mono (K.map (smallEtaleLiftPostIso B X hX U V ψ).hom)).1
      change z' ≫ smallEtaleGraph B X hX U Wψ ≫ K.map _ = _
      rw [← smallEtaleLiftGraph, ← he]
      rw [Category.assoc, key, htc]
      simp only [Category.assoc]
  have hh := hab (G.obj t.Y) f hsplit
  change (a ≫ H.obj.map (smallEtaleLiftPostIso B X hX U V φ).hom.op) ≫
    H.obj.map (G.map t.f).op =
    (b ≫ H.obj.map (smallEtaleLiftPostIso B X hX U V φ).hom.op) ≫
      H.obj.map (G.map t.f).op
  simpa only [f, op_comp, Functor.map_comp, Category.assoc] using hh

/-- Extending a section along the graph of `φ` and then restricting it along the graph of `ψ`: the
off-diagonal comparison of two morphisms `V ⟶ U`. -/
public def smallEtaleLiftCross
    {Acat : Type v} [Category.{w} Acat] [Preadditive Acat]
    (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) Acat)
    (V : SmallEtale B X hX) (φ ψ : V ⟶ U) :=
  smallEtaleLiftExtension B X hX U F V φ ≫
    F.obj.map (smallEtaleLiftGraph B X hX U V ψ).op

/-- The off-diagonal comparison is compatible with restriction along `V' ⟶ V`. -/
@[reassoc]
public theorem smallEtaleLiftCross_map
    {Acat : Type v} [Category.{w} Acat] [Preadditive Acat]
    (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) Acat)
    {V V' : SmallEtale B X hX} (f : V' ⟶ V) (φ ψ : V ⟶ U) :
    smallEtaleLiftCross B X hX U F V φ ψ ≫
        F.obj.map (smallEtaleLiftMap B X hX U f ψ).op =
      F.obj.map (smallEtaleLiftMap B X hX U f φ).op ≫
        smallEtaleLiftCross B X hX U F V' (f ≫ φ) (f ≫ ψ) := by
  unfold smallEtaleLiftCross
  rw [Category.assoc, ← Functor.map_comp, ← op_comp, smallEtaleLiftGraph_naturality,
    op_comp, Functor.map_comp, ← Category.assoc, ← smallEtaleLiftExtension_map,
    Category.assoc]

/-- Composing the off-diagonal comparison with the component of a natural transformation at `φ` is
the same as routing it back through the comparison at `ψ`. -/
public theorem smallEtaleLiftCross_unit
    {Acat : Type v} [Category.{w} Acat] [Preadditive Acat]
    (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) Acat)
    (H : Sheaf (SmallEtale.topology B X hX) Acat)
    (η : F.obj ⟶ (smallEtalePostcompose B X hX U).op ⋙ H.obj)
    (V : SmallEtale B X hX) (φ ψ : V ⟶ U) :
    smallEtaleLiftCross B X hX U F V ψ φ ≫ smallEtaleLiftUnit B X hX U F H η V φ =
    smallEtaleLiftCross B X hX U F V ψ φ ≫
      smallEtaleLiftCross B X hX U F V φ ψ ≫ smallEtaleLiftUnit B X hX U F H η V ψ := by
  apply hom_ext_of_equal_or_disjoint B X hX U H V φ ψ
  intro V' f hf
  simp only [Category.assoc, ← smallEtaleLiftUnit_map,
    smallEtaleLiftCross_map_assoc]
  cases hf with
  | inl h =>
    rw [h]
    simp only [smallEtaleLiftCross, smallEtaleLiftExtension_graph, Category.id_comp]
  | inr h =>
    have hzero : smallEtaleLiftCross B X hX U F V' (f ≫ ψ) (f ≫ φ) = 0 :=
      smallEtaleLiftExtension_disjoint B X hX U F V' _ _
        (smallEtaleArrowsDisjoint_symm B X hX U V' _ _ h)
    simp only [hzero, zero_comp, comp_zero]

/-- An étale object over `U`, regarded as étale over `X`, maps to `U`. -/
public def smallEtaleStructureMap
    (W : SmallEtale B U.obj.left.1 U.obj.left.property) :
    (smallEtalePostcompose B X hX U).obj W ⟶ U :=
  ObjectProperty.homMk (Over.homMk W.obj.hom (by rfl))

/-- A morphism from `V` to `W` regarded as étale over `X` exhibits `V`, with the induced morphism
to `U`, as an étale object over `U` mapping to `W`. -/
public def smallEtaleArrowLift
    (V : SmallEtale B X hX)
    (W : SmallEtale B U.obj.left.1 U.obj.left.property)
    (f : V ⟶ (smallEtalePostcompose B X hX U).obj W) :
    smallEtaleLift B X hX U V (f ≫ smallEtaleStructureMap B X hX U W) ⟶ W :=
  ObjectProperty.homMk (Over.homMk f.hom.left (by rfl))

omit [IsSeparated (B.inclusion.map U.obj.hom)] in
/-- Every restriction of the component at `W` of a natural transformation factors through the
component at the induced morphism `V ⟶ U`. -/
public theorem smallEtaleLiftUnit_factor
    {Acat : Type v} [Category.{w} Acat]
    (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) Acat)
    (H : Sheaf (SmallEtale.topology B X hX) Acat)
    (η : F.obj ⟶ (smallEtalePostcompose B X hX U).op ⋙ H.obj)
    (V : SmallEtale B X hX)
    (W : SmallEtale B U.obj.left.1 U.obj.left.property)
    (f : V ⟶ (smallEtalePostcompose B X hX U).obj W) :
    η.app (Opposite.op W) ≫ H.obj.map f.op =
      F.obj.map (smallEtaleArrowLift B X hX U V W f).op ≫
        smallEtaleLiftUnit B X hX U F H η V
          (f ≫ smallEtaleStructureMap B X hX U W) := by
  unfold smallEtaleLiftUnit
  rw [← Category.assoc, η.naturality]
  simp only [Category.assoc, Functor.comp_map, Functor.op_map, ← Functor.map_comp, ← op_comp]
  congr 3

omit [IsSeparated (B.inclusion.map U.obj.hom)] in
/-- A section of the presheaf extension by zero over `V`, pushed into the target sheaf, is a finite
sum of sections coming from the summands indexed by the morphisms `V ⟶ U`. This is the
`⨁_{φ : V → U} F(V →^φ U)` description of the presheaf extension, read through a functor to abelian
groups preserving the colimit. -/
public theorem image_lan_is_sum
    {Acat : Type v} [Category.{w} Acat] [HasColimitsOfSize.{u, u + 1} Acat]
    (T : Acat ⥤ AddCommGrpCat.{x}) [PreservesColimitsOfSize.{u, u + 1} T]
    (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) Acat)
    (H : Sheaf (SmallEtale.topology B X hX) Acat)
    (η : F.obj ⟶ (smallEtalePostcompose B X hX U).op ⋙ H.obj)
    (δ : ((smallEtalePostcompose B X hX U).op.lan.obj F.obj) ⟶ H.obj)
    (hδ : (smallEtalePostcompose B X hX U).op.lanUnit.app F.obj ≫
      Functor.whiskerLeft (smallEtalePostcompose B X hX U).op δ = η)
    (V : SmallEtale B X hX)
    (s : T.obj (((smallEtalePostcompose B X hX U).op.lan.obj F.obj).obj
      (Opposite.op V))) :
    ∃ l : List (Σ φ : V ⟶ U, T.obj (F.obj.obj (Opposite.op (smallEtaleLift B X hX U V φ)))),
      (l.map fun a => T.map (smallEtaleLiftUnit B X hX U F H η V a.1) a.2).sum =
        T.map (δ.app (Opposite.op V)) s := by
  classical
  let G := smallEtalePostcompose B X hX U
  let P := G.op.lan.obj F.obj
  let α := G.op.lanUnit.app F.obj
  let c := (Functor.LeftExtension.mk P α).coconeAt (Opposite.op V)
  have hc : IsColimit (T.mapCocone c) := isColimitOfPreserves T
    (G.op.isPointwiseLeftKanExtensionLeftKanExtensionUnit F.obj (Opposite.op V))
  obtain ⟨l, hl⟩ := exists_list_sum_of_isColimit _ _ hc s
  let l' := l.map fun a =>
    let W := a.1.left.unop
    let f := a.1.hom.unop
    (⟨f ≫ smallEtaleStructureMap B X hX U W,
      T.map (F.obj.map (smallEtaleArrowLift B X hX U V W f).op) a.2⟩ :
      Σ φ : V ⟶ U, T.obj (F.obj.obj (Opposite.op (smallEtaleLift B X hX U V φ))))
  refine ⟨l', ?_⟩
  dsimp only [l']
  rw [← hl]
  clear hl s
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, map_add, ih]
    congr 1
    let W := a.1.left.unop
    let f := a.1.hom.unop
    have hη := congrArg (fun t => t.app (Opposite.op W)) hδ
    change α.app (Opposite.op W) ≫ δ.app (Opposite.op (G.obj W)) = η.app (Opposite.op W) at hη
    have heq : (α.app (Opposite.op W) ≫ P.map f.op) ≫ δ.app (Opposite.op V) =
        F.obj.map (smallEtaleArrowLift B X hX U V W f).op ≫
          smallEtaleLiftUnit B X hX U F H η V
            (f ≫ smallEtaleStructureMap B X hX U W) := by
      rw [Category.assoc, δ.naturality, ← Category.assoc]
      change (α.app (Opposite.op W) ≫ δ.app (Opposite.op (G.obj W))) ≫ _ = _
      rw [hη, smallEtaleLiftUnit_factor]
    change T.map (smallEtaleLiftUnit B X hX U F H η V
      (f ≫ smallEtaleStructureMap B X hX U W))
      (T.map (F.obj.map (smallEtaleArrowLift B X hX U V W f).op) a.2) =
      T.map (δ.app (Opposite.op V)) (T.map (α.app (Opposite.op W) ≫ P.map f.op) a.2)
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← ConcreteCategory.comp_apply, ← Functor.map_comp]
    exact congrArg (fun t => T.map t a.2) heq.symm

/-- A natural transformation whose components on the graphs are the extensions by zero sends the
component at `φ` to the extension along the graph of `φ`. -/
public theorem smallEtaleLiftUnit_comparison
    {Acat : Type v} [Category.{w} Acat] [Preadditive Acat]
    (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) Acat)
    (H : Sheaf (SmallEtale.topology B X hX) Acat)
    (η : F.obj ⟶ (smallEtalePostcompose B X hX U).op ⋙ H.obj)
    (τ : H.obj ⟶ (smallEtaleBaseChange B U.obj.hom).op ⋙ F.obj)
    (hτ : ∀ W, η.app (Opposite.op W) ≫ τ.app
      (Opposite.op ((smallEtalePostcompose B X hX U).obj W)) =
      smallEtaleGraphExtension B X hX U F W
        (graphComplementCover_mem_smallEtaleTopology B X hX U W))
    (V : SmallEtale B X hX) (φ : V ⟶ U) :
    smallEtaleLiftUnit B X hX U F H η V φ ≫ τ.app (Opposite.op V) =
      smallEtaleLiftExtension B X hX U F V φ := by
  unfold smallEtaleLiftUnit smallEtaleLiftExtension
  rw [Category.assoc, τ.naturality, ← Category.assoc]
  dsimp only [Functor.op_obj, Functor.comp_map, Functor.op_map]
  rw [hτ]
  rfl

/-- A finite sum of sections coming from the summands indexed by morphisms `V ⟶ U` vanishes as soon
as its image in the direct image vanishes. -/
public theorem sum_unit_eq_zero
    {Acat : Type v} [Category.{w} Acat] [Preadditive Acat]
    (T : Acat ⥤ AddCommGrpCat.{x})
    (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) Acat)
    (H : Sheaf (SmallEtale.topology B X hX) Acat)
    (η : F.obj ⟶ (smallEtalePostcompose B X hX U).op ⋙ H.obj)
    (τ : H.obj ⟶ (smallEtaleBaseChange B U.obj.hom).op ⋙ F.obj)
    (hτ : ∀ W, η.app (Opposite.op W) ≫ τ.app
      (Opposite.op ((smallEtalePostcompose B X hX U).obj W)) =
      smallEtaleGraphExtension B X hX U F W
        (graphComplementCover_mem_smallEtaleTopology B X hX U W))
    (V : SmallEtale B X hX)
    (l : List (Σ φ : V ⟶ U, T.obj (F.obj.obj (Opposite.op (smallEtaleLift B X hX U V φ)))))
    (h : T.map (τ.app (Opposite.op V))
      ((l.map fun a => T.map (smallEtaleLiftUnit B X hX U F H η V a.1) a.2).sum) = 0) :
    (l.map fun a => T.map (smallEtaleLiftUnit B X hX U F H η V a.1) a.2).sum = 0 := by
  apply AddMonoidHom.sum_eq_zero_of_projections
    (fun φ : V ⟶ U => T.obj (F.obj.obj (Opposite.op (smallEtaleLift B X hX U V φ))))
    (fun φ => (T.map (smallEtaleLiftUnit B X hX U F H η V φ)).hom)
    (T.map (τ.app (Opposite.op V))).hom
    (fun φ => (T.map (F.obj.map (smallEtaleLiftGraph B X hX U V φ).op)).hom) _ _ l h
  · intro φ s
    have he : (smallEtaleLiftUnit B X hX U F H η V φ ≫ τ.app (Opposite.op V)) ≫
        F.obj.map (smallEtaleLiftGraph B X hX U V φ).op = 𝟙 _ := by
      rw [smallEtaleLiftUnit_comparison B X hX U F H η τ hτ, smallEtaleLiftExtension_graph]
    simpa only [Functor.map_comp, ConcreteCategory.comp_apply,
      CategoryTheory.Functor.map_id, ConcreteCategory.id_apply] using
      congrArg (fun t => T.map t s) he
  · intro φ ψ s
    refine ⟨T.map (smallEtaleLiftCross B X hX U F V ψ φ ≫
      smallEtaleLiftCross B X hX U F V φ ψ) s, ?_⟩
    have he : ((smallEtaleLiftUnit B X hX U F H η V ψ ≫ τ.app (Opposite.op V)) ≫
        F.obj.map (smallEtaleLiftGraph B X hX U V φ).op) ≫
          smallEtaleLiftUnit B X hX U F H η V φ =
      (smallEtaleLiftCross B X hX U F V ψ φ ≫
        smallEtaleLiftCross B X hX U F V φ ψ) ≫
          smallEtaleLiftUnit B X hX U F H η V ψ := by
      rw [smallEtaleLiftUnit_comparison B X hX U F H η τ hτ]
      exact (smallEtaleLiftCross_unit B X hX U F H η V φ ψ).trans (Category.assoc _ _ _).symm
    simpa only [Functor.map_comp, ConcreteCategory.comp_apply] using
      congrArg (fun t => T.map t s) he

/-- Injectivity criterion for a comparison map into the direct image: if the comparison restricts
on each graph to the identity, and the sheaf is locally generated by the presheaf extension by
zero, then the comparison is a monomorphism. -/
public theorem mono_of_graph_unit
    {Acat : Type v} [Category.{w} Acat] [Preadditive Acat]
    [HasColimitsOfSize.{u, u + 1} Acat]
    (T : Acat ⥤ AddCommGrpCat.{x}) [T.Faithful]
    [PreservesColimitsOfSize.{u, u + 1} T]
    [(SmallEtale.topology B X hX).HasSheafCompose T]
    (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) Acat)
    (H : Sheaf (SmallEtale.topology B X hX) Acat)
    (η : F.obj ⟶ (smallEtalePostcompose B X hX U).op ⋙ H.obj)
    (τ : H.obj ⟶ (smallEtaleBaseChange B U.obj.hom).op ⋙ F.obj)
    (hτ : ∀ W, η.app (Opposite.op W) ≫ τ.app
      (Opposite.op ((smallEtalePostcompose B X hX U).obj W)) =
      smallEtaleGraphExtension B X hX U F W
        (graphComplementCover_mem_smallEtaleTopology B X hX U W))
    (δ : ((smallEtalePostcompose B X hX U).op.lan.obj F.obj) ⟶ H.obj)
    [Presheaf.IsLocallySurjective (SmallEtale.topology B X hX)
      (Functor.whiskerRight δ T)]
    (hδ : (smallEtalePostcompose B X hX U).op.lanUnit.app F.obj ≫
      Functor.whiskerLeft (smallEtalePostcompose B X hX U).op δ = η) :
    Mono τ := by
  let J := SmallEtale.topology B X hX
  let HT := (sheafCompose J T).obj H
  have hz (V : SmallEtale B X hX) (s : T.obj (H.obj.obj (Opposite.op V)))
      (hs : T.map (τ.app (Opposite.op V)) s = 0) : s = 0 := by
    let δT := Functor.whiskerRight δ T
    apply HT.property.isSeparated V (Presheaf.imageSieve δT s)
      (Presheaf.imageSieve_mem (J := J) (f := δT) (s := s)) s 0
    intro V' f hf
    change ∃ t : T.obj ((smallEtalePostcompose B X hX U).op.lan.obj F.obj |>.obj (Opposite.op V')),
      T.map (δ.app (Opposite.op V')) t = T.map (H.obj.map f.op) s at hf
    obtain ⟨t, ht⟩ := hf
    obtain ⟨l, hl⟩ := image_lan_is_sum B X hX U T F H η δ hδ V' t
    have hzero : T.map (τ.app (Opposite.op V'))
        (T.map (δ.app (Opposite.op V')) t) = 0 := by
      rw [ht]
      have he := NatTrans.naturality_apply (Functor.whiskerRight τ T) f.op s
      change T.map (τ.app (Opposite.op V')) (T.map (H.obj.map f.op) s) =
        T.map (F.obj.map ((smallEtaleBaseChange B U.obj.hom).map f).op)
          (T.map (τ.app (Opposite.op V)) s) at he
      rwa [hs, map_zero] at he
    have hlzero := sum_unit_eq_zero B X hX U T F H η τ hτ V' l (by rw [hl]; exact hzero)
    change T.map (H.obj.map f.op) s = T.map (H.obj.map f.op) 0
    rw [map_zero]
    exact ht.symm.trans (hl.symm.trans hlzero)
  have : ∀ V, Mono (τ.app V) := by
    intro V
    have hi : Function.Injective (T.map (τ.app V)) := by
      intro a b hab
      apply sub_eq_zero.mp
      apply hz V.unop (a - b)
      rw [map_sub, hab, sub_self]
    exact T.mono_of_mono_map (ConcreteCategory.mono_of_injective _ hi)
  exact NatTrans.mono_of_mono_app τ

omit [IsSeparated (B.inclusion.map U.obj.hom)] in
/-- The canonical map from extension by zero to the direct image of abelian sheaves along the étale
morphism `U ⟶ X`. On the summand of the presheaf extension indexed by `φ : V ⟶ U` it extends a
section by zero along the open and closed graph of `φ`; that requires `U ⟶ X` to be separated, and
off the separated locus the map is zero. -/
@[stacks 0F4L "abelian natural map"]
public noncomputable def abelianExtensionByZeroToPushforward :
    let := smallEtaleBaseChange_isContinuous B U.obj.hom
    abelianExtensionByZero B X hX U ⟶
      (smallEtaleBaseChange B U.obj.hom).sheafPushforwardContinuous
        AddCommGrpCat.{u + 1}
        (SmallEtale.topology B X hX)
        (SmallEtale.topology B U.obj.left.1 U.obj.left.property) := by
  classical
  let := smallEtaleBaseChange_isContinuous B U.obj.hom
  by_cases h : IsSeparated (B.inclusion.map U.obj.hom)
  · letI := h
    exact Adjunction.transposeNatTrans
      (abelianExtensionByZeroAdjunction B X hX U) _
      (smallEtaleGraphExtensionUnit B X hX U AddCommGrpCat.{u + 1})
  · exact 0

/-- The comparison map, composed with the unit of the extension-by-zero adjunction, is extension of
sections by zero along the graph. -/
public theorem abelianExtensionByZeroToPushforward_unit
    (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
      AddCommGrpCat.{u + 1})
    (W : SmallEtale B U.obj.left.1 U.obj.left.property) :
    ((abelianExtensionByZeroAdjunction B X hX U).unit.app F).hom.app (Opposite.op W) ≫
      ((abelianExtensionByZeroToPushforward B X hX U).app F).hom.app
        (Opposite.op ((smallEtalePostcompose B X hX U).obj W)) =
    smallEtaleGraphExtension B X hX U F W
      (graphComplementCover_mem_smallEtaleTopology B X hX U W) := by
  have h := Adjunction.unit_comp_map_transposeNatTrans
    (abelianExtensionByZeroAdjunction B X hX U) _
    (smallEtaleGraphExtensionUnit B X hX U AddCommGrpCat.{u + 1}) F
  unfold abelianExtensionByZeroToPushforward
  rw [dite_eq_left (inferInstance : IsSeparated (B.inclusion.map U.obj.hom))]
  exact congrArg (fun k => k.hom.app (Opposite.op W)) h

/-- For a separated étale morphism, every component of the canonical map from extension by zero to
the direct image of abelian sheaves is a monomorphism. -/
@[stacks 0F4L "abelian injectivity"]
public theorem abelianExtensionByZeroToPushforward_mono
    (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
      AddCommGrpCat.{u + 1}) :
    Mono ((abelianExtensionByZeroToPushforward B X hX U).app F) := by
  let G := smallEtalePostcompose B X hX U
  let J := SmallEtale.topology B X hX
  let H := (abelianExtensionByZero B X hX U).obj F
  let η := ((abelianExtensionByZeroAdjunction B X hX U).unit.app F).hom
  let τ := ((abelianExtensionByZeroToPushforward B X hX U).app F).hom
  let δ := toSheafify J (G.op.lan.obj F.obj)
  have : Presheaf.IsLocallySurjective J (Functor.whiskerRight δ (𝟭 AddCommGrpCat.{u + 1})) := by
    change Presheaf.IsLocallySurjective J δ
    infer_instance
  have hm : Mono τ := mono_of_graph_unit B X hX U (𝟭 AddCommGrpCat.{u + 1}) F H η τ
    (abelianExtensionByZeroToPushforward_unit B X hX U F) δ
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous_unit_app_hom
      G _ J F).symm)
  exact Sheaf.Hom.mono_of_presheaf_mono J AddCommGrpCat.{u + 1} _

/-- On the summand indexed by `W ⟶ U`, the canonical map restricts along the graph `W ⟶ W ×_X U` to
the original section. -/
@[stacks 0F4L "abelian graph restriction"]
public theorem abelianExtensionByZeroToPushforward_graph
    (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
      AddCommGrpCat.{u + 1})
    (W : SmallEtale B U.obj.left.1 U.obj.left.property)
    (s : F.obj.obj (Opposite.op W)) :
    let V := (smallEtalePostcompose B X hX U).obj W
    (F.obj.map (smallEtaleGraph B X hX U W).op)
      (((abelianExtensionByZeroToPushforward B X hX U).app F).hom.app
        (Opposite.op V)
        (((abelianExtensionByZeroAdjunction
          B X hX U).unit.app F).hom.app (Opposite.op W) s)) = s := by
  change ((((abelianExtensionByZeroAdjunction B X hX U).unit.app F).hom.app (Opposite.op W) ≫
  ((abelianExtensionByZeroToPushforward B X hX U).app F).hom.app
    (Opposite.op ((smallEtalePostcompose B X hX U).obj W))) ≫
      F.obj.map (smallEtaleGraph B X hX U W).op) s = s
  rw [abelianExtensionByZeroToPushforward_unit, smallEtaleGraphExtension_graph]
  rfl

/-- The image of the summand indexed by `W ⟶ U` restricts to zero along every morphism into
`W ×_X U` whose image avoids the graph of `W`. -/
@[stacks 0F4L "abelian complementary vanishing"]
public theorem abelianExtensionByZeroToPushforward_graph_compl
    (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
      AddCommGrpCat.{u + 1})
    (W T : SmallEtale B U.obj.left.1 U.obj.left.property)
    (g : T ⟶ (smallEtaleBaseChange B U.obj.hom).obj
      ((smallEtalePostcompose B X hX U).obj W))
    (hg : disjointFromSmallEtaleGraph B X hX U W T g)
    (s : F.obj.obj (Opposite.op W)) :
    let V := (smallEtalePostcompose B X hX U).obj W
    (F.obj.map g.op)
      (((abelianExtensionByZeroToPushforward B X hX U).app F).hom.app
        (Opposite.op V)
        (((abelianExtensionByZeroAdjunction
          B X hX U).unit.app F).hom.app (Opposite.op W) s)) = 0 := by
  change ((((abelianExtensionByZeroAdjunction B X hX U).unit.app F).hom.app (Opposite.op W) ≫
  ((abelianExtensionByZeroToPushforward B X hX U).app F).hom.app
    (Opposite.op ((smallEtalePostcompose B X hX U).obj W))) ≫
      F.obj.map g.op) s = 0
  rw [abelianExtensionByZeroToPushforward_unit,
    smallEtaleGraphExtension_disjoint B X hX U F W T g hg]
  rfl

omit [IsSeparated (B.inclusion.map U.obj.hom)] in
/-- The canonical map from extension by zero to the direct image of sheaves of `Λ`-modules along
the étale morphism `U ⟶ X`, constructed exactly as in the abelian case. -/
@[stacks 0F4L "module natural map"]
public noncomputable def moduleExtensionByZeroToPushforward
    (Λ : Type v) [Ring Λ] :
    let := smallEtaleBaseChange_isContinuous B U.obj.hom
    moduleExtensionByZero B X hX U Λ ⟶
      (smallEtaleBaseChange B U.obj.hom).sheafPushforwardContinuous
        (ModuleCat.{max (u + 1) v} Λ)
        (SmallEtale.topology B X hX)
        (SmallEtale.topology B U.obj.left.1 U.obj.left.property) := by
  classical
  let := smallEtaleBaseChange_isContinuous B U.obj.hom
  by_cases h : IsSeparated (B.inclusion.map U.obj.hom)
  · letI := h
    exact Adjunction.transposeNatTrans
      (moduleExtensionByZeroAdjunction B X hX U Λ) _
      (smallEtaleGraphExtensionUnit B X hX U (ModuleCat.{max (u + 1) v} Λ))
  · exact 0

/-- The module comparison map, composed with the unit of the extension-by-zero adjunction, is
extension of sections by zero along the graph. -/
public theorem moduleExtensionByZeroToPushforward_unit
    (Λ : Type v) [Ring Λ]
    (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
      (ModuleCat.{max (u + 1) v} Λ))
    (W : SmallEtale B U.obj.left.1 U.obj.left.property) :
    ((moduleExtensionByZeroAdjunction B X hX U Λ).unit.app F).hom.app (Opposite.op W) ≫
      ((moduleExtensionByZeroToPushforward B X hX U Λ).app F).hom.app
        (Opposite.op ((smallEtalePostcompose B X hX U).obj W)) =
    smallEtaleGraphExtension B X hX U F W
      (graphComplementCover_mem_smallEtaleTopology B X hX U W) := by
  have h := Adjunction.unit_comp_map_transposeNatTrans
    (moduleExtensionByZeroAdjunction B X hX U Λ) _
    (smallEtaleGraphExtensionUnit B X hX U (ModuleCat.{max (u + 1) v} Λ)) F
  unfold moduleExtensionByZeroToPushforward
  rw [dite_eq_left (inferInstance : IsSeparated (B.inclusion.map U.obj.hom))]
  exact congrArg (fun k => k.hom.app (Opposite.op W)) h

/-- For a separated étale morphism, every component of the canonical map from extension by zero to
the direct image of sheaves of `Λ`-modules is a monomorphism. -/
@[stacks 0F4L "module injectivity"]
public theorem moduleExtensionByZeroToPushforward_mono
    (Λ : Type v) [Ring Λ]
    (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
      (ModuleCat.{max (u + 1) v} Λ)) :
    Mono ((moduleExtensionByZeroToPushforward B X hX U Λ).app F) := by
  let G := smallEtalePostcompose B X hX U
  let J := SmallEtale.topology B X hX
  let T := forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v}
  let : PreservesFilteredColimits (forget (ModuleCat.{max (u + 1) v} Λ)) :=
    comp_preservesFilteredColimits T (forget AddCommGrpCat)
  let : EssentiallySmall.{max (u + 1) v} (SmallEtale B X hX) := inferInstance
  let : HasSheafify J (ModuleCat.{max (u + 1) v} Λ) :=
    hasSheafifyEssentiallySmallSite.{_, _, _, _, max (u + 1) v} _ _
  let : J.WEqualsLocallyBijective (ModuleCat.{max (u + 1) v} Λ) :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall J
  let H := (moduleExtensionByZero B X hX U Λ).obj F
  let η := ((moduleExtensionByZeroAdjunction B X hX U Λ).unit.app F).hom
  let τ := ((moduleExtensionByZeroToPushforward B X hX U Λ).app F).hom
  let δ := toSheafify J (G.op.lan.obj F.obj)
  have : Presheaf.IsLocallySurjective J (Functor.whiskerRight δ T) := by
    constructor
    intro V s
    exact Presheaf.imageSieve_mem (J := J) (f := δ) (s := s)
  have hm : Mono τ := mono_of_graph_unit B X hX U T F H η τ
    (moduleExtensionByZeroToPushforward_unit B X hX U Λ F) δ
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous_unit_app_hom
      G _ J F).symm)
  exact Sheaf.Hom.mono_of_presheaf_mono J (ModuleCat.{max (u + 1) v} Λ) _

/-- On the summand indexed by `W ⟶ U`, the canonical map for sheaves of modules restricts along the
graph `W ⟶ W ×_X U` to the original section. -/
@[stacks 0F4L "module graph restriction"]
public theorem moduleExtensionByZeroToPushforward_graph
    (Λ : Type v) [Ring Λ]
    (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
      (ModuleCat.{max (u + 1) v} Λ))
    (W : SmallEtale B U.obj.left.1 U.obj.left.property)
    (s : F.obj.obj (Opposite.op W)) :
    let V := (smallEtalePostcompose B X hX U).obj W
    (F.obj.map (smallEtaleGraph B X hX U W).op)
      (((moduleExtensionByZeroToPushforward B X hX U Λ).app F).hom.app
        (Opposite.op V)
      (((moduleExtensionByZeroAdjunction
          B X hX U Λ).unit.app F).hom.app (Opposite.op W) s)) = s := by
  change ((((moduleExtensionByZeroAdjunction B X hX U Λ).unit.app F).hom.app (Opposite.op W) ≫
  ((moduleExtensionByZeroToPushforward B X hX U Λ).app F).hom.app
    (Opposite.op ((smallEtalePostcompose B X hX U).obj W))) ≫
      F.obj.map (smallEtaleGraph B X hX U W).op) s = s
  rw [moduleExtensionByZeroToPushforward_unit, smallEtaleGraphExtension_graph]
  rfl

/-- The image of the summand indexed by `W ⟶ U` restricts to zero along every morphism into
`W ×_X U` whose image avoids the graph of `W`, for sheaves of modules. -/
@[stacks 0F4L "module complementary vanishing"]
public theorem moduleExtensionByZeroToPushforward_graph_compl
    (Λ : Type v) [Ring Λ]
    (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
      (ModuleCat.{max (u + 1) v} Λ))
    (W T : SmallEtale B U.obj.left.1 U.obj.left.property)
    (g : T ⟶ (smallEtaleBaseChange B U.obj.hom).obj
      ((smallEtalePostcompose B X hX U).obj W))
    (hg : disjointFromSmallEtaleGraph B X hX U W T g)
    (s : F.obj.obj (Opposite.op W)) :
    let V := (smallEtalePostcompose B X hX U).obj W
    (F.obj.map g.op)
      (((moduleExtensionByZeroToPushforward B X hX U Λ).app F).hom.app
        (Opposite.op V)
      (((moduleExtensionByZeroAdjunction
          B X hX U Λ).unit.app F).hom.app (Opposite.op W) s)) = 0 := by
  change ((((moduleExtensionByZeroAdjunction B X hX U Λ).unit.app F).hom.app (Opposite.op W) ≫
  ((moduleExtensionByZeroToPushforward B X hX U Λ).app F).hom.app
    (Opposite.op ((smallEtalePostcompose B X hX U).obj W))) ≫
      F.obj.map g.op) s = 0
  rw [moduleExtensionByZeroToPushforward_unit,
    smallEtaleGraphExtension_disjoint B X hX U F W T g hg]
  rfl

end AlgebraicGeometry

end
