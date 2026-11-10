module

public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Construction.PresheafObjects.MatchingComparison

/-!
# Descending hypercoverings along the Yoneda embedding

The Yoneda embedding of semi-representable objects into the slice over the final presheaf, local
surjectivity on maps out of the objects of the site, and the two transfers between hypercoverings
of the final presheaf and hypercoverings for `localPretopology`:
`hypercoveringOfTerminal_lift` (descent) and `isHypercovering_yonedaFormal` (ascent).
-/

@[expose] public section

universe w v u q d e

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.CategoryTheory.Hypercovering

attribute [local implicit_reducible] mapFormalCoproduct

variable {C : Type u} [Category.{v} C] [HasEqualizers C] [HasPullbacks C]

section Descent

/-- **The Yoneda embedding read into the slice over the final presheaf.**  The final presheaf is
terminal, so the slice over it is equivalent to the category of presheaves itself; this is the
Yoneda embedding followed by that equivalence.  Hypercoverings of an *object* are simplicial
formal coproducts in a slice, which is why the comparison with hypercoverings of the final
presheaf is stated here rather than in the presheaf category. -/
noncomputable abbrev overYoneda :
    C ⥤ Over (⊤_ (Cᵒᵖ ⥤ Type (max w u v))) :=
  uliftYoneda.{max w u} ⋙ (Over.equivalenceOfIsTerminal (terminalIsTerminal)).inverse

/-- **The Yoneda embedding on semi-representable objects**: `overYoneda` applied summandwise to a
formal coproduct.  It is fully faithful (`yonedaFormalFullyFaithful`), which is what lets
morphisms, factorisations and local lifts pass between the two settings. -/
noncomputable abbrev yonedaFormal :
    FormalCoproduct.{max w u v} C ⥤
      FormalCoproduct.{max w u v} (Over (⊤_ (Cᵒᵖ ⥤ Type (max w u v)))) :=
  mapFormalCoproduct overYoneda

/-- **The test objects**: the one-summand formal coproducts on the images of the objects of the
site.  A covering family for `localPretopology` is tested on sections over objects of `C`, and by
Yoneda's bijection a section of a summand over `U` is a morphism out of the test object at `U`;
that is the content of `homLocallySurjective_of_covering` and of its converse
`isCoveringOver_of_homLocallySurjective`. -/
noncomputable abbrev testObjects :
    C ⥤ FormalCoproduct.{max w u v} (Over (⊤_ (Cᵒᵖ ⥤ Type (max w u v)))) :=
  FormalCoproduct.incl C ⋙ yonedaFormal

/-- The sieve of arrows along which a map out of a test object lifts through a given map. -/
def homLifts {D : Type d} [Category.{e} D] (T : C ⥤ D)
    {X Y : D} (p : X ⟶ Y) {U : C} (s : T.obj U ⟶ Y) : Sieve U where
  arrows V f := ∃ t : T.obj V ⟶ X, t ≫ p = T.map f ≫ s
  downward_closed := by
    rintro V W f ⟨t, ht⟩ g
    refine ⟨T.map g ≫ t, ?_⟩
    rw [Category.assoc, ht, T.map_comp, Category.assoc]

/-- A map is locally surjective on maps out of test objects when every such map lifts through it
locally on the site. -/
def HomLocallySurjective {D : Type d} [Category.{e} D]
    (J : GrothendieckTopology C) (T : C ⥤ D) {X Y : D} (p : X ⟶ Y) : Prop :=
  ∀ (U : C) (s : T.obj U ⟶ Y), homLifts T p s ∈ J U

omit [HasEqualizers C] [HasPullbacks C] in
/-- Yoneda's bijection sends a map classified by a section, composed with a map of presheaves,
to that map evaluated at the section.

Stated as its own lemma, with the presheaves explicit, so that its use sites can discharge it by
`exact`: the `uliftYonedaEquiv_comp` step is definitional, and a `simp` that reaches the same
place by unfolding `uliftYonedaEquiv` leaves the goal ill-typed at `implicit` transparency. -/
private lemma uliftYonedaEquiv_symm_comp_apply {V : C} {F G : Cᵒᵖ ⥤ Type (max w u v)}
    (y : F.obj (op V)) (g : F ⟶ G) :
    uliftYonedaEquiv.{max w u} (uliftYonedaEquiv.{max w u}.symm y ≫ g) = g.app (op V) y :=
  congrArg (ConcreteCategory.hom (g.app (op V))) (uliftYonedaEquiv.{max w u}.apply_symm_apply y)

omit [HasEqualizers C] [HasPullbacks C] in
/-- The two-step form of `uliftYonedaEquiv_symm_comp_apply`, stated with the composition
bracketed to the left: a component of a morphism of formal coproducts over an object arrives
already composed with an `eqToHom`, and reassociating it inside the `uliftYonedaEquiv` is not a
definitional step. -/
private lemma uliftYonedaEquiv_symm_comp_comp_apply {V : C}
    {F G H : Cᵒᵖ ⥤ Type (max w u v)} (y : F.obj (op V)) (g : F ⟶ G) (h : G ⟶ H) :
    uliftYonedaEquiv.{max w u} ((uliftYonedaEquiv.{max w u}.symm y ≫ g) ≫ h) =
      (g ≫ h).app (op V) y :=
  (congrArg uliftYonedaEquiv.{max w u} (Category.assoc _ g h)).trans
    (uliftYonedaEquiv_symm_comp_apply y (g ≫ h))

omit [HasEqualizers C] [HasPullbacks C] in
/-- Yoneda's bijection sends the image of a morphism of the site, composed with a map of
presheaves, to that map evaluated at the morphism. -/
private lemma uliftYonedaEquiv_map_comp_apply {U V : C} (f : V ⟶ U)
    {G : Cᵒᵖ ⥤ Type (max w u v)} (g : (uliftYoneda.{max w u} (C := C)).obj U ⟶ G) :
    uliftYonedaEquiv.{max w u} (uliftYoneda.map f ≫ g) = g.app (op V) (ULift.up f) :=
  congrArg (ConcreteCategory.hom (g.app (op V))) (uliftYonedaEquiv_uliftYoneda_map.{max w u} f)

omit [HasEqualizers C] in
private theorem homLocallySurjective_of_covering (J : Pretopology C)
    {X Y : FormalCoproduct.{max w u v} (Over (⊤_ (Cᵒᵖ ⥤ Type (max w u v))))}
    (p : X ⟶ Y) (hp : IsCoveringOver (localPretopology J) p) :
    HomLocallySurjective J.toGrothendieck testObjects p := by
  intro U s
  let j := s.f PUnit.unit
  let x := uliftYonedaEquiv ((s.φ PUnit.unit).left)
  apply J.toGrothendieck.superset_covering ?_ (hp j U x)
  intro V f hf
  obtain ⟨P, g, hg, y, hy⟩ := hf
  cases hg with
  | mk i =>
    let t : (FormalCoproduct.incl _).obj (overYoneda.obj V) ⟶ X :=
      FormalCoproduct.Hom.fromIncl i.1
        (Over.homMk (uliftYonedaEquiv.{max w u}.symm y) (terminalIsTerminal.hom_ext _ _))
    refine ⟨t, ?_⟩
    refine FormalCoproduct.hom_ext ?_ ?_
    · funext z
      exact i.2
    · intro z
      cases z
      apply Over.OverMorphism.ext
      apply uliftYonedaEquiv.injective
      -- Stated as a term, applying `(s.φ _).left.app (op V)` to the equation rather than
      -- rewriting underneath its coercion: a `dsimp [uliftYonedaEquiv]` here pushes the goal
      -- through `uliftYoneda` and leaves it ill-typed at `implicit` transparency.
      have hx : (Y.obj j).left.map f.op x =
          (s.φ PUnit.unit).left.app (op V) (ULift.up f) :=
        (uliftYonedaEquiv_naturality (s.φ PUnit.unit).left f.op).trans
          (congrArg (ConcreteCategory.hom ((s.φ PUnit.unit).left.app (op V)))
            (uliftYonedaEquiv_uliftYoneda_map f))
      -- The goal differs from `hy.trans hx` by two steps that are not definitional, and both
      -- are supplied as terms rather than rewritten: the index cast of
      -- `FormalCoproduct.hom_ext` lives in the over category whereas `IsCoveringOver` states
      -- its covering family with the cast already pushed down to the underlying presheaves
      -- (`Over.eqToHom_left`), and Yoneda's bijection has to be moved across each composite
      -- (the two lemmas above). Everything else is composition of equalities.
      have hleft : Over.Hom.left (eqToHom (congrArg Y.obj i.2)) =
          eqToHom (congrArg (fun k ↦ (Y.obj k).left) i.2) := Over.eqToHom_left _
      refine Eq.trans (congrArg (fun m ↦ uliftYonedaEquiv.{max w u}
        ((uliftYonedaEquiv.{max w u}.symm y ≫ (p.φ i.1).left) ≫ m)) hleft) ?_
      exact ((uliftYonedaEquiv_symm_comp_comp_apply y (p.φ i.1).left
        (eqToHom (congrArg (fun k ↦ (Y.obj k).left) i.2))).trans (hy.trans hx)).trans
          (uliftYonedaEquiv_map_comp_apply f (s.φ PUnit.unit).left).symm

omit [HasEqualizers C] in
/-- **A covering morphism for `localPretopology` is locally surjective on maps out of the test
objects.**  This is the direction of the equivalence with `isCoveringOver_of_homLocallySurjective`
that reads a covering family off a covering morphism: a covering family for `localPretopology` is
tested on sections over objects of `C`, and a section of a summand over `U` is a map out of the
test object at `U`. -/
alias homLocallySurjective_of_covering' := homLocallySurjective_of_covering

omit [HasEqualizers C] in
/-- **A morphism of formal coproducts over the final presheaf which is locally surjective on maps
out of the test objects is covering for `localPretopology`.**  This is the converse of
`homLocallySurjective_of_covering`, and the two together say that for a morphism of formal
coproducts of presheaves the two conditions coincide: a covering family for `localPretopology` is
tested on sections over objects of `C`, and a section of a representable over `U` is a map out of
the test object at `U`.

A section `x` of the summand `Y.obj j` over `U` is turned into the map out of the test object at
`U` which Yoneda's bijection assigns to it; a local lift of that map is a summand `i` of `X` over
`j` together with a map of test objects into it, and the section of `(X.obj i).left` that Yoneda's
bijection assigns back to its underlying map of presheaves is the required local lift of `x`. -/
theorem isCoveringOver_of_homLocallySurjective (J : Pretopology C)
    {X Y : FormalCoproduct.{max w u v} (Over (⊤_ (Cᵒᵖ ⥤ Type (max w u v))))}
    (p : X ⟶ Y) (hp : HomLocallySurjective J.toGrothendieck testObjects p) :
    IsCoveringOver (localPretopology J) p := by
  intro j U x
  apply J.toGrothendieck.superset_covering ?_ (hp U
    (show (FormalCoproduct.incl _).obj (overYoneda.obj U) ⟶ Y from
      FormalCoproduct.Hom.fromIncl j
        (Over.homMk (uliftYonedaEquiv.{max w u}.symm x) (terminalIsTerminal.hom_ext _ _))))
  rintro V f ⟨t, ht⟩
  obtain ⟨hij, hcomp⟩ := (FormalCoproduct.hom_ext_iff' _ _).1 ht PUnit.unit
  -- The composition and the one-summand morphism are unfolded by a type ascription rather than
  -- by `simp`: `(t ≫ p).φ` and `(testObjects.map f ≫ _).φ` are definitionally the composites
  -- below, and the two `eqToHom` witnesses agree by proof irrelevance.
  have hcomp' : (t.φ PUnit.unit ≫ p.φ (t.f PUnit.unit)) ≫ eqToHom (congrArg Y.obj hij) =
      overYoneda.map f ≫
        Over.homMk (uliftYonedaEquiv.{max w u}.symm x)
          (terminalIsTerminal.hom_ext _ _) := hcomp
  have hleft : ((t.φ PUnit.unit).left ≫ (p.φ (t.f PUnit.unit)).left) ≫
      eqToHom (congrArg (fun k ↦ (Y.obj k).left) hij) =
      uliftYoneda.{max w u}.map f ≫ uliftYonedaEquiv.{max w u}.symm x := by
    have h0 := congrArg Over.Hom.left hcomp'
    simp only [Over.comp_left, Over.eqToHom_left] at h0
    exact h0
  refine ⟨(X.obj (t.f PUnit.unit)).left,
    (p.φ (t.f PUnit.unit)).left ≫ eqToHom (congrArg (fun k ↦ (Y.obj k).left) hij),
    Presieve.ofArrows.mk (⟨t.f PUnit.unit, hij⟩ : {i : X.I // p.f i = j}),
    uliftYonedaEquiv.{max w u} ((t.φ PUnit.unit).left), ?_⟩
  exact (uliftYonedaEquiv_comp ((t.φ PUnit.unit).left) _).symm.trans
    ((congrArg (fun α ↦ uliftYonedaEquiv.{max w u} α)
        ((Category.assoc _ _ _).symm.trans hleft)).trans
      ((uliftYonedaEquiv_naturality (uliftYonedaEquiv.{max w u}.symm x) f.op).symm.trans
        (congrArg (ConcreteCategory.hom ((Y.obj j).left.map f.op))
          (uliftYonedaEquiv.{max w u}.apply_symm_apply x))))

/-- **A fully faithful functor induces a fully faithful functor on formal coproducts**: a
morphism of formal coproducts is a function on the indexing sets together with a morphism on each
summand, and the summandwise morphisms are taken bijectively. -/
def mapFormalCoproductFullyFaithful {D : Type d} [Category.{e} D]
    (F : C ⥤ D) (hF : F.FullyFaithful) :
    (mapFormalCoproduct F : FormalCoproduct.{w} C ⥤ FormalCoproduct.{w} D).FullyFaithful where
  preimage f := ⟨f.f, fun i ↦ hF.preimage (f.φ i)⟩
  map_preimage f := by
    refine FormalCoproduct.hom_ext rfl fun i ↦ ?_
    simp only [mapFormalCoproduct_map_φ, hF.map_preimage, eqToHom_refl, Category.comp_id]
  preimage_map f := by
    refine FormalCoproduct.hom_ext rfl ?_
    intro i
    simp [mapFormalCoproduct, hF.preimage_map]

/-- **`yonedaFormal` is fully faithful**, Yoneda's embedding being fully faithful and the slice
over a terminal object being equivalent to the ambient category. -/
noncomputable def yonedaFormalFullyFaithful :
    (yonedaFormal : FormalCoproduct.{max w u v} C ⥤ _).FullyFaithful :=
  mapFormalCoproductFullyFaithful _ ((ULiftYoneda.fullyFaithful C).comp
    (Over.equivalenceOfIsTerminal terminalIsTerminal).fullyFaithfulInverse)

noncomputable def liftSimplicialIso (B : Set C)
    (K : SimplicialObject (FormalCoproduct.{max w u v}
      (Over (⊤_ (Cᵒᵖ ⥤ Type (max w u v))))))
    (hK : ∀ (n : SimplexCategoryᵒᵖ) (i : (K.obj n).I),
      ((K.obj n).obj i).left ∈ representableObjectsIn (C := C) B) :
    let Q := K ⋙ mapFormalCoproduct (Over.forget _)
    liftSimplicialObject B Q hK ⋙ yonedaFormal ≅ K := by
  let Q := K ⋙ mapFormalCoproduct (Over.forget _)
  refine NatIso.ofComponents (fun n ↦ FormalCoproduct.isoOfComponents (Equiv.refl _) (fun i ↦
    Over.isoMk (eqToIso (liftFormalObject_eq B (Q.obj n) (hK n) i)).symm
      (terminalIsTerminal.hom_ext _ _))) ?_
  intro n m f
  refine FormalCoproduct.hom_ext rfl ?_
  intro i
  apply Over.OverMorphism.ext
  change uliftYoneda.map ((liftFormalHom B (hK n) (hK m) (Q.map f)).φ i) ≫
    eqToHom (liftFormalObject_eq B (Q.obj m) (hK m) ((K.map f).f i)).symm ≫ 𝟙 _ =
    eqToHom (liftFormalObject_eq B (Q.obj n) (hK n) i).symm ≫ ((K.map f).φ i).left
  rw [liftFormalHom_map]
  simp [Q, mapFormalCoproduct]

noncomputable section

/-- Sections of the presheaf associated to a formal coproduct are maps out of the one-element
formal coproduct. -/
def sectionEquiv (X : FormalCoproduct.{w} C) (U : C) :
    ((associatedPresheafFunctor.{v}).obj X).obj (op U) ≃
      ((FormalCoproduct.incl C).obj U ⟶ X) :=
  Equiv.ulift.trans <|
    (sigmaObjIso (fun i : X.I ↦ uliftYoneda.{w}.obj (X.obj i)) (op U)).toEquiv.trans <|
    (Types.coproductIso (fun i : X.I ↦ ULift.{w} (U ⟶ X.obj i))).toEquiv.trans <|
    (Equiv.sigmaCongrRight (fun _ ↦ Equiv.ulift)).trans (FormalCoproduct.inclHomEquiv U X).symm

omit [HasEqualizers C] [HasPullbacks C] in
/-- Under `sectionEquiv`, the map out of the one-element formal coproduct given by
`f : U ⟶ X.obj i` corresponds to the image of `f` under the `i`-th coprojection of the presheaf
coproduct. -/
lemma sectionEquiv_symm_fromIncl (X : FormalCoproduct.{w} C) (U : C)
    (i : X.I) (f : U ⟶ X.obj i) :
    (sectionEquiv X U).symm (FormalCoproduct.Hom.fromIncl i f) =
      ULift.up ((Sigma.ι (fun i : X.I ↦ uliftYoneda.{w}.obj (X.obj i)) i).app (op U)
        (ULift.up f)) := by
  change ULift.up (((sigmaObjIso (fun i : X.I ↦ uliftYoneda.{w}.obj (X.obj i)) (op U)).inv)
    ((Types.coproductIso (fun i : X.I ↦ ULift.{w} (U ⟶ X.obj i))).inv ⟨i, ULift.up f⟩)) = _
  have h := types_congr_hom (Types.coproductIso_mk_comp_inv
    (fun i : X.I ↦ ULift.{w} (U ⟶ X.obj i)) i) (ULift.up f)
  change (Types.coproductIso (fun i : X.I ↦ ULift.{w} (U ⟶ X.obj i))).inv
    ⟨i, ULift.up f⟩ = _ at h
  rw [h]
  congr 1
  exact types_congr_hom
    (ι_comp_sigmaObjIso_inv (fun i : X.I ↦ uliftYoneda.{w}.obj (X.obj i)) (op U) i)
    (ULift.up f)

omit [HasEqualizers C] [HasPullbacks C] in
/-- `sectionEquiv` is natural in the formal coproduct: postcomposition with `f : X ⟶ Y`
corresponds to the map of associated presheaves induced by `f`. -/
lemma sectionEquiv_symm_postcomp (X Y : FormalCoproduct.{w} C) (U : C)
    (f : X ⟶ Y) (s : (FormalCoproduct.incl C).obj U ⟶ X) :
    (sectionEquiv Y U).symm (s ≫ f) =
      ((associatedPresheafFunctor.{v}).map f).app (op U)
        ((sectionEquiv X U).symm s) := by
  rw [← s.fromIncl_asSigma]
  have h : FormalCoproduct.Hom.fromIncl s.asSigma.1 s.asSigma.2 ≫ f =
      FormalCoproduct.Hom.fromIncl (f.f s.asSigma.1) (s.asSigma.2 ≫ f.φ s.asSigma.1) := rfl
  rw [h, sectionEquiv_symm_fromIncl, sectionEquiv_symm_fromIncl]
  congr 1
  change _ = ((Sigma.ι _ _ ≫ FormalCoproduct.uliftYoneda.map f).app (op U)) _
  simp [FormalCoproduct.uliftYoneda, FormalCoproduct.eval, Function.comp_def]
  rfl

omit [HasEqualizers C] [HasPullbacks C] in
/-- `sectionEquiv` is natural in the object: precomposition with the image of `f : V ⟶ U`
corresponds to restriction of sections of the associated presheaf along `f`. -/
lemma sectionEquiv_symm_precomp (X : FormalCoproduct.{w} C) {U V : C}
    (f : V ⟶ U) (s : (FormalCoproduct.incl C).obj U ⟶ X) :
    (sectionEquiv X V).symm ((FormalCoproduct.incl C).map f ≫ s) =
      ((associatedPresheafFunctor.{v}).obj X).map f.op
        ((sectionEquiv X U).symm s) := by
  rw [← s.fromIncl_asSigma]
  have h : (FormalCoproduct.incl C).map f ≫
      FormalCoproduct.Hom.fromIncl s.asSigma.1 s.asSigma.2 =
      FormalCoproduct.Hom.fromIncl s.asSigma.1 (f ≫ s.asSigma.2) := rfl
  rw [h, sectionEquiv_symm_fromIncl, sectionEquiv_symm_fromIncl]
  congr 1
  exact types_congr_hom
    ((Sigma.ι (fun i : X.I ↦ uliftYoneda.{w}.obj (X.obj i)) s.asSigma.1).naturality f.op)
    (ULift.up s.asSigma.2)

omit [HasEqualizers C] [HasPullbacks C] in
private theorem homLocallySurjective_of_iso {D : Type d} [Category.{e} D]
    (J : GrothendieckTopology C) (T : C ⥤ D)
    {X Y X' Y' : D} (p : X ⟶ Y) (p' : X' ⟶ Y') (a : X ≅ X') (b : Y ≅ Y')
    (w : a.hom ≫ p' = p ≫ b.hom) (hp : HomLocallySurjective J T p') :
    HomLocallySurjective J T p := by
  intro U s
  apply J.superset_covering ?_ (hp U (s ≫ b.hom))
  rintro V f ⟨t, ht⟩
  refine ⟨t ≫ a.inv, ?_⟩
  apply (cancel_mono b.hom).mp
  simpa only [Category.assoc, ← w, Iso.inv_hom_id_assoc] using ht

omit [HasEqualizers C] [HasPullbacks C] in
private theorem homLocallySurjective_unit_of_iso {D : Type d} [Category.{e} D]
    (J : GrothendieckTopology C) (T : C ⥤ D)
    {K L : SimplicialObject D} (a : K ≅ L) (n : ℕ)
    [∀ F : SimplicialObject.Truncated D n,
      (SimplexCategory.Truncated.inclusion n).op.HasPointwiseRightKanExtension F]
    (t : SimplexCategoryᵒᵖ)
    (h : HomLocallySurjective J T (((SimplicialObject.coskAdj n).unit.app L).app t)) :
    HomLocallySurjective J T (((SimplicialObject.coskAdj n).unit.app K).app t) :=
  homLocallySurjective_of_iso J T _ _ (a.app t) (((SimplicialObject.cosk n).mapIso a).app t)
    (NatTrans.congr_app ((SimplicialObject.coskAdj n).unit.naturality a.hom) t) h

omit [HasEqualizers C] [HasPullbacks C] in
private theorem homLocallySurjective_unit_of_fullyFaithful
    {A : Type d} [Category.{e} A] {D : Type q} [Category.{w} D]
    (J : GrothendieckTopology C) (T : C ⥤ A) (G : A ⥤ D) (hG : G.FullyFaithful)
    (L : SimplicialObject A) (n : ℕ)
    [∀ F : SimplicialObject.Truncated A n,
      (SimplexCategory.Truncated.inclusion n).op.HasPointwiseRightKanExtension F]
    [∀ F : SimplicialObject.Truncated D n,
      (SimplexCategory.Truncated.inclusion n).op.HasPointwiseRightKanExtension F]
    (t : SimplexCategoryᵒᵖ)
    (h : HomLocallySurjective J (T ⋙ G)
      (((SimplicialObject.coskAdj n).unit.app (L ⋙ G)).app t)) :
    HomLocallySurjective J T (((SimplicialObject.coskAdj n).unit.app L).app t) := by
  have := hG.faithful
  intro U s
  apply J.superset_covering ?_ (h U (G.map s ≫ matchingComparison G L n t))
  rintro V f ⟨x, hx⟩
  refine ⟨hG.preimage x, ?_⟩
  apply matchingComparison_injective G L n t
  simp only [G.map_comp, Category.assoc, unit_matchingComparison, hG.map_preimage]
  exact hx

omit [HasEqualizers C] [HasPullbacks C] in
private theorem homLocallySurjective_one_of_fullyFaithful
    {A : Type d} [Category.{e} A] {D : Type q} [Category.{w} D]
    (J : GrothendieckTopology C) (T : C ⥤ A) (G : A ⥤ D) (hG : G.FullyFaithful)
    (L : SimplicialObject A)
    [∀ F : SimplicialObject.Truncated D 0,
      (SimplexCategory.Truncated.inclusion 0).op.HasPointwiseRightKanExtension F]
    (h : HomLocallySurjective J (T ⋙ G)
      (((SimplicialObject.coskAdj 0).unit.app (L ⋙ G)).app (op (SimplexCategory.mk 1))))
    (U : C) (a b : T.obj U ⟶ L.obj (op (SimplexCategory.mk 0))) :
    ∃ S : Sieve U, S ∈ J U ∧ ∀ {V : C} (f : V ⟶ U), S f →
      ∃ x : T.obj V ⟶ L.obj (op (SimplexCategory.mk 1)),
        x ≫ L.δ 0 = T.map f ≫ a ∧ x ≫ L.δ 1 = T.map f ≫ b := by
  let s := zeroMatchingLift (L ⋙ G) (G.map a) (G.map b)
  refine ⟨_, h U s, ?_⟩
  rintro V f ⟨x, hx⟩
  refine ⟨hG.preimage x, ?_, ?_⟩
  all_goals
    apply hG.map_injective
    simp only [G.map_comp, hG.map_preimage]
  · have h := congrArg (fun z ↦ z ≫ (matchingCone (L ⋙ G) 0 _).π.app
        (StructuredArrow.mk
          (Y := op (⟨SimplexCategory.mk 0, le_rfl⟩ : SimplexCategory.Truncated 0))
          (SimplexCategory.δ (0 : Fin 2)).op)) hx
    simp only [Category.assoc, unit_matching_π, s, zeroMatchingLift_π, ite_true] at h
    exact h
  · have h := congrArg (fun z ↦ z ≫ (matchingCone (L ⋙ G) 0 _).π.app
        (StructuredArrow.mk
          (Y := op (⟨SimplexCategory.mk 0, le_rfl⟩ : SimplexCategory.Truncated 0))
          (SimplexCategory.δ (1 : Fin 2)).op)) hx
    simp only [Category.assoc, unit_matching_π, s, zeroMatchingLift_π,
      ite_eq_right (by decide : (1 : Fin 2) ≠ 0)] at h
    exact h

omit [HasEqualizers C] [HasPullbacks C] in
/-- **The ascent of local surjectivity on test objects along a fully faithful functor**, for the
canonical map to a matching object.  This is the converse of
`homLocallySurjective_unit_of_fullyFaithful`, and it is what the reverse transfer of a
hypercovering needs: there the local lifts are available in `A` and are wanted in `D`.

Both directions rest on the same bijection: precomposing with `matchingComparison G L n t` is a
bijection from `T ⟶ Mₙ(L)ₜ` onto `G T ⟶ Mₙ(L ⋙ G)ₜ`, injective by
`matchingComparison_injective` and surjective by `exists_matchingComparison_eq`.  Here the given
map into the matching object of the image is pulled back along that bijection, the local lift is
taken in `A`, and its image under `G` is a local lift of the original map because
`unit_matchingComparison` carries the unit across. -/
theorem homLocallySurjective_unit_comp_of_fullyFaithful
    {A : Type d} [Category.{e} A] {D : Type q} [Category.{w} D]
    (J : GrothendieckTopology C) (T : C ⥤ A) (G : A ⥤ D) (hG : G.FullyFaithful)
    (L : SimplicialObject A) (n : ℕ)
    [∀ F : SimplicialObject.Truncated A n,
      (SimplexCategory.Truncated.inclusion n).op.HasPointwiseRightKanExtension F]
    [∀ F : SimplicialObject.Truncated D n,
      (SimplexCategory.Truncated.inclusion n).op.HasPointwiseRightKanExtension F]
    (t : SimplexCategoryᵒᵖ)
    (h : HomLocallySurjective J T (((SimplicialObject.coskAdj n).unit.app L).app t)) :
    HomLocallySurjective J (T ⋙ G)
      (((SimplicialObject.coskAdj n).unit.app (L ⋙ G)).app t) := by
  intro U s
  obtain ⟨a, ha⟩ := exists_matchingComparison_eq G hG L n t s
  apply J.superset_covering ?_ (h U a)
  rintro V f ⟨x, hx⟩
  refine ⟨G.map x, ?_⟩
  change G.map x ≫ _ = G.map (T.map f) ≫ s
  have h1 : G.map x ≫ ((SimplicialObject.coskAdj n).unit.app (L ⋙ G)).app t =
      G.map (x ≫ ((SimplicialObject.coskAdj n).unit.app L).app t) ≫
        matchingComparison G L n t := by
    rw [G.map_comp, Category.assoc, unit_matchingComparison]
  rw [h1, hx, G.map_comp, Category.assoc, ha]

omit [HasEqualizers C] [HasPullbacks C] in
/-- **The ascent of local surjectivity on test objects along a fully faithful functor, in degree
one**: the degree-one clause of a hypercovering in the shape
`homLocallySurjective_one_of_fullyFaithful` produces it -- a pair of maps into degree zero lifts
locally to degree one -- gives local surjectivity of the canonical map to the degree-one matching
object of the image.

The hypothesis is the conclusion of `homLocallySurjective_one_of_fullyFaithful`, so the two
lemmas together say that in degree one the matching condition may be read in either category.
A map into the matching object is here *given* and its two faces are read off it by
`zeroMatchingπ`; that the image of the lift agrees with it is `zeroMatching_hom_ext`, there being
exactly two face maps `⦋0⦌ ⟶ ⦋1⦌`. -/
private theorem homLocallySurjective_one_comp_of_fullyFaithful
    {A : Type d} [Category.{e} A] {D : Type q} [Category.{w} D]
    (J : GrothendieckTopology C) (T : C ⥤ A) (G : A ⥤ D) (hG : G.FullyFaithful)
    (L : SimplicialObject A)
    [∀ F : SimplicialObject.Truncated D 0,
      (SimplexCategory.Truncated.inclusion 0).op.HasPointwiseRightKanExtension F]
    (h : ∀ (U : C) (a b : T.obj U ⟶ L.obj (op (SimplexCategory.mk 0))),
      ∃ S : Sieve U, S ∈ J U ∧ ∀ {V : C} (f : V ⟶ U), S f →
        ∃ x : T.obj V ⟶ L.obj (op (SimplexCategory.mk 1)),
          x ≫ L.δ 0 = T.map f ≫ a ∧ x ≫ L.δ 1 = T.map f ≫ b) :
    HomLocallySurjective J (T ⋙ G)
      (((SimplicialObject.coskAdj 0).unit.app (L ⋙ G)).app (op (SimplexCategory.mk 1))) := by
  intro U s
  obtain ⟨S, hS, hS'⟩ := h U (hG.preimage (s ≫ zeroMatchingπ (L ⋙ G) 0))
    (hG.preimage (s ≫ zeroMatchingπ (L ⋙ G) 1))
  apply J.superset_covering ?_ hS
  intro V f hf
  obtain ⟨x, hx₀, hx₁⟩ := hS' f hf
  refine ⟨G.map x, ?_⟩
  change G.map x ≫ _ = G.map (T.map f) ≫ s
  refine zeroMatching_hom_ext (L ⋙ G) _ _ fun i ↦ ?_
  rw [Category.assoc, Category.assoc, unit_matching_π]
  change G.map x ≫ G.map (L.δ i) = G.map (T.map f) ≫ s ≫ zeroMatchingπ (L ⋙ G) i
  rw [← G.map_comp]
  have hcases : ∀ j : Fin 2, j = 0 ∨ j = 1 := by decide
  rcases hcases i with rfl | rfl
  · rw [hx₀, G.map_comp, hG.map_preimage]
  · rw [hx₁, G.map_comp, hG.map_preimage]

omit [HasEqualizers C] [HasPullbacks C] in
/-- **A morphism of formal coproducts whose associated morphism of presheaves is locally
surjective is locally surjective on maps out of the site.**  This is the converse of
`locallySurjective_of_homLocallySurjective`: the two conditions are the same condition read
through the bijection `sectionEquiv` between the sections of the associated presheaf and the maps
out of a one-element formal coproduct. -/
theorem homLocallySurjective_of_locallySurjective
    (J : GrothendieckTopology C) {X Y : FormalCoproduct.{w} C} (p : X ⟶ Y)
    (hp : Presheaf.IsLocallySurjective J ((associatedPresheafFunctor.{v}).map p)) :
    HomLocallySurjective J (FormalCoproduct.incl C) p := by
  intro U s
  apply J.superset_covering ?_ (hp.imageSieve_mem ((sectionEquiv Y U).symm s))
  rintro V f ⟨x, hx⟩
  refine ⟨sectionEquiv X V x, ?_⟩
  apply (sectionEquiv Y V).symm.injective
  rw [sectionEquiv_symm_postcomp, Equiv.symm_apply_apply, sectionEquiv_symm_precomp, hx]

omit [HasEqualizers C] [HasPullbacks C] in
/-- A morphism of formal coproducts which is locally surjective on maps out of the site induces
a locally surjective morphism of the associated presheaves. -/
theorem locallySurjective_of_homLocallySurjective
    (J : GrothendieckTopology C) {X Y : FormalCoproduct.{w} C} (p : X ⟶ Y)
    (hp : HomLocallySurjective J (FormalCoproduct.incl C) p) :
    Presheaf.IsLocallySurjective J ((associatedPresheafFunctor.{v}).map p) := by
  constructor
  intro U s
  apply J.superset_covering ?_ (hp U (sectionEquiv Y U s))
  rintro V f ⟨x, hx⟩
  refine ⟨(sectionEquiv X V).symm x, ?_⟩
  rw [← sectionEquiv_symm_postcomp, hx, sectionEquiv_symm_precomp, Equiv.symm_apply_apply]

omit [HasEqualizers C] in
/-- A covering morphism of formal coproducts is locally surjective on maps out of the objects of
the site: a map from an object of `C` into the target lifts to the source locally on `C`. -/
theorem homLocallySurjective_incl_of_isCovering (J : Pretopology C)
    {X Y : FormalCoproduct.{w} C} (p : X ⟶ Y) (hp : IsCovering J p) :
    HomLocallySurjective J.toGrothendieck (FormalCoproduct.incl C) p := by
  intro U s
  let j : Y.I := s.f PUnit.unit
  let x : U ⟶ Y.obj j := s.φ PUnit.unit
  let Xj : { i : X.I // p.f i = j } → C := fun i ↦ X.obj i.1
  let aj : (i : { i : X.I // p.f i = j }) → Xj i ⟶ Y.obj j :=
    fun i ↦ p.φ i.1 ≫ eqToHom (congrArg Y.obj i.2)
  have hS : Sieve.ofArrows Xj aj ∈ J.toGrothendieck (Y.obj j) := by
    rw [Pretopology.mem_toGrothendieck]
    exact ⟨Presieve.ofArrows Xj aj, hp j, Sieve.le_generate _⟩
  refine J.toGrothendieck.superset_covering ?_ (J.toGrothendieck.pullback_stable x hS)
  intro V f hf
  rw [Sieve.pullback_apply] at hf
  obtain ⟨i, k, hk⟩ := (Sieve.mem_ofArrows_iff Xj aj _).mp hf
  refine ⟨FormalCoproduct.Hom.fromIncl i.1 k, FormalCoproduct.hom_ext (funext fun _ ↦ i.2) ?_⟩
  rintro ⟨⟩
  change (k ≫ p.φ i.1) ≫ eqToHom (congrArg Y.obj i.2) = f ≫ x
  simpa [aj, Category.assoc] using hk.symm

omit [HasEqualizers C] in
/-- **A covering morphism of semi-representable objects induces a locally surjective morphism of
the associated presheaves.** -/
theorem locallySurjective_map_of_isCovering (J : Pretopology C)
    {X Y : FormalCoproduct.{w} C} (p : X ⟶ Y) (hp : IsCovering J p) :
    Presheaf.IsLocallySurjective J.toGrothendieck ((associatedPresheafFunctor.{v}).map p) :=
  locallySurjective_of_homLocallySurjective J.toGrothendieck p
    (homLocallySurjective_incl_of_isCovering J p hp)

omit [HasEqualizers C] [HasPullbacks C] in
/-- A section of a fibre product of presheaves is determined by its two projections. -/
theorem presheaf_pullback_section_ext
    {X Y Z : Cᵒᵖ ⥤ Type (max w v)} (f : X ⟶ Z) (g : Y ⟶ Z)
    (U : C) {a b : (pullback f g).obj (op U)}
    (h₁ : (pullback.fst f g).app (op U) a = (pullback.fst f g).app (op U) b)
    (h₂ : (pullback.snd f g).app (op U) a = (pullback.snd f g).app (op U) b) : a = b := by
  apply uliftYonedaEquiv.{w}.symm.injective
  apply pullback.hom_ext
  · apply uliftYonedaEquiv.injective
    simpa only [uliftYonedaEquiv_comp, Equiv.apply_symm_apply] using h₁
  · apply uliftYonedaEquiv.injective
    simpa only [uliftYonedaEquiv_comp, Equiv.apply_symm_apply] using h₂

/-- The lift of the final presheaf of `Type v` to `Type (max w u v)` is terminal. -/
private noncomputable def isTerminalLiftedPresheaf :
    IsTerminal (liftedPresheaf.{v, max w u v} (⊤_ (Cᵒᵖ ⥤ Type v))) :=
  IsTerminal.isTerminalObj
    ((Functor.whiskeringRight (Cᵒᵖ) (Type v) (Type (max w u v))).obj uliftFunctor.{max w u v})
    (⊤_ (Cᵒᵖ ⥤ Type v)) terminalIsTerminal

/-- Each section set of the lift of the final presheaf is terminal. -/
private noncomputable def isTerminalLiftedPresheafObj (U : C) :
    IsTerminal ((liftedPresheaf.{v, max w u v} (⊤_ (Cᵒᵖ ⥤ Type v))).obj (op U)) :=
  IsTerminal.isTerminalObj ((evaluation _ _).obj (op U)) _ isTerminalLiftedPresheaf

/-- **The degree-one clause of a hypercovering of the final presheaf, read as a lifting property
for pairs of maps out of an object of the site.**

Condition (2) of [Stacks, Tag 09VU] says that the map of presheaves from degree one to the fibre
product of the two degree-zero augmentation maps is locally surjective.  The target of the
augmentation is the final presheaf, so that fibre product is a product and a section of it over
`U` is a *pair* of sections of degree zero, that is a pair of maps out of the one-summand formal
coproduct at `U`.  This is that reading, and it is the hypothesis of
`homLocallySurjective_one_comp_of_fullyFaithful`.

It is the converse of the step `homLocallySurjective_one_of_fullyFaithful` performs in
`hypercoveringOfTerminal_lift`, where the pair is produced from a map into the matching object
and the fibre-product section is then built from it. -/
private theorem homLocallySurjective_one_pair (J : Pretopology C)
    (H : HypercoveringOfTerminal.{max w u v} J) (U : C)
    (a b : (FormalCoproduct.incl C).obj U ⟶
      H.toSimplicialObject.obj (op (SimplexCategory.mk 0))) :
    ∃ S : Sieve U, S ∈ J.toGrothendieck U ∧ ∀ {V : C} (f : V ⟶ U), S f →
      ∃ x : (FormalCoproduct.incl C).obj V ⟶
          H.toSimplicialObject.obj (op (SimplexCategory.mk 1)),
        x ≫ H.toSimplicialObject.δ 0 = (FormalCoproduct.incl C).map f ≫ a ∧
          x ≫ H.toSimplicialObject.δ 1 = (FormalCoproduct.incl C).map f ≫ b := by
  let σmap : uliftYoneda.{max w u}.obj U ⟶
      pullback (H.augmentation.app (op (SimplexCategory.mk 0)))
        (H.augmentation.app (op (SimplexCategory.mk 0))) :=
    pullback.lift
      (uliftYonedaEquiv.{max w u}.symm
        ((sectionEquiv (H.toSimplicialObject.obj (op (SimplexCategory.mk 0))) U).symm a))
      (uliftYonedaEquiv.{max w u}.symm
        ((sectionEquiv (H.toSimplicialObject.obj (op (SimplexCategory.mk 0))) U).symm b))
      (isTerminalLiftedPresheaf.hom_ext _ _)
  refine ⟨_, H.locallySurjective_one.imageSieve_mem (uliftYonedaEquiv.{max w u} σmap), ?_⟩
  intro V f hf
  obtain ⟨t, ht⟩ := hf
  -- One argument for each projection: the projection of the fibre-product section is the
  -- degree-zero section it was built from, and the projection of the matching map is a face map.
  have main : ∀ (π : pullback (H.augmentation.app (op (SimplexCategory.mk 0)))
          (H.augmentation.app (op (SimplexCategory.mk 0))) ⟶
        (associatedPresheafFunctor.{v}).obj
          (H.toSimplicialObject.obj (op (SimplexCategory.mk 0))))
      (d : H.toSimplicialObject.obj (op (SimplexCategory.mk 1)) ⟶
        H.toSimplicialObject.obj (op (SimplexCategory.mk 0)))
      (c : (FormalCoproduct.incl C).obj U ⟶
        H.toSimplicialObject.obj (op (SimplexCategory.mk 0))),
      oneMatchingMap (associatedSimplicialPresheaf.{v} H.toSimplicialObject)
            (liftedPresheaf.{v, max w u v} (⊤_ (Cᵒᵖ ⥤ Type v))) H.augmentation ≫ π =
          (associatedPresheafFunctor.{v}).map d →
        π.app (op U) (uliftYonedaEquiv.{max w u} σmap) =
          (sectionEquiv (H.toSimplicialObject.obj (op (SimplexCategory.mk 0))) U).symm c →
        sectionEquiv (H.toSimplicialObject.obj (op (SimplexCategory.mk 1))) V t ≫ d =
          (FormalCoproduct.incl C).map f ≫ c := by
    intro π d c hπd hπσ
    apply (sectionEquiv (H.toSimplicialObject.obj (op (SimplexCategory.mk 0))) V).symm.injective
    rw [sectionEquiv_symm_postcomp, Equiv.symm_apply_apply, sectionEquiv_symm_precomp]
    have hcomp := congrArg
      (fun m : (associatedPresheafFunctor.{v}).obj
            (H.toSimplicialObject.obj (op (SimplexCategory.mk 1))) ⟶
          (associatedPresheafFunctor.{v}).obj
            (H.toSimplicialObject.obj (op (SimplexCategory.mk 0))) ↦ m.app (op V) t) hπd
    refine hcomp.symm.trans ?_
    refine (congrArg (fun z ↦ π.app (op V) z) ht).trans ?_
    refine (NatTrans.naturality_apply π f.op (uliftYonedaEquiv.{max w u} σmap)).trans ?_
    exact congrArg (fun z ↦ ((associatedPresheafFunctor.{v}).obj
      (H.toSimplicialObject.obj (op (SimplexCategory.mk 0)))).map f.op z) hπσ
  refine ⟨sectionEquiv (H.toSimplicialObject.obj (op (SimplexCategory.mk 1))) V t,
    main (pullback.fst _ _) (H.toSimplicialObject.δ 0) a
      (oneMatchingMap_fst (associatedSimplicialPresheaf.{v} H.toSimplicialObject)
        (liftedPresheaf.{v, max w u v} (⊤_ (Cᵒᵖ ⥤ Type v))) H.augmentation) ?_,
    main (pullback.snd _ _) (H.toSimplicialObject.δ 1) b
      (oneMatchingMap_snd (associatedSimplicialPresheaf.{v} H.toSimplicialObject)
        (liftedPresheaf.{v, max w u v} (⊤_ (Cᵒᵖ ⥤ Type v))) H.augmentation) ?_⟩
  · exact (uliftYonedaEquiv_comp σmap (pullback.fst _ _)).symm.trans
      ((congrArg (fun m ↦ uliftYonedaEquiv.{max w u} m) (pullback.lift_fst _ _ _)).trans
        (uliftYonedaEquiv.{max w u}.apply_symm_apply _))
  · exact (uliftYonedaEquiv_comp σmap (pullback.snd _ _)).symm.trans
      ((congrArg (fun m ↦ uliftYonedaEquiv.{max w u} m) (pullback.lift_snd _ _ _)).trans
        (uliftYonedaEquiv.{max w u}.apply_symm_apply _))

/-- A hypercovering of the terminal presheaf in the presheaf category, together with an
identification of its lift along Yoneda, gives a hypercovering of the final presheaf on the
original site. -/
theorem hypercoveringOfTerminal_lift
    (J : Pretopology C) (L : SimplicialObject (FormalCoproduct.{max w u v} C))
    (K : SimplicialObject (FormalCoproduct.{max w u v}
      (Over (⊤_ (Cᵒᵖ ⥤ Type (max w u v))))))
    (e : L ⋙ yonedaFormal ≅ K)
    (hK : IsHypercovering (localPretopology J) K) :
    ∃ H : HypercoveringOfTerminal.{max w u v} J, H.toSimplicialObject = L := by
  let G := (yonedaFormal : FormalCoproduct.{max w u v} C ⥤ _)
  let hG : G.FullyFaithful := yonedaFormalFullyFaithful
  let P := liftedPresheaf.{v, max w u v} (⊤_ (Cᵒᵖ ⥤ Type v))
  have hP : IsTerminal P := isTerminalLiftedPresheaf
  let aug : associatedSimplicialPresheaf.{v} L ⟶
      (SimplicialObject.const _).obj P :=
    { app n := hP.from _
      naturality n m f := hP.hom_ext _ _ }
  have hunit (n : ℕ) : HomLocallySurjective J.toGrothendieck testObjects
      (((SimplicialObject.coskAdj n).unit.app (L ⋙ G)).app
        (op (SimplexCategory.mk (n + 1)))) :=
    homLocallySurjective_unit_of_iso J.toGrothendieck testObjects e n _
      (homLocallySurjective_of_covering J _ (hK.2 n))
  refine ⟨{
    toSimplicialObject := L
    augmentation := aug
    locallySurjective_zero := ?_
    locallySurjective_one := ?_
    locallySurjective_succ := ?_ }, rfl⟩
  · constructor
    intro U s
    have h := homLocallySurjective_of_covering J _ hK.1 U (terminal.from (testObjects.obj U))
    apply J.toGrothendieck.superset_covering ?_ h
    rintro V f ⟨x, hx⟩
    let a := hG.preimage (x ≫ e.inv.app (op (SimplexCategory.mk 0)))
    refine ⟨(sectionEquiv (L.obj (op (SimplexCategory.mk 0))) V).symm a, ?_⟩
    have := Types.isTerminalEquivUnique _ (isTerminalLiftedPresheafObj (C := C) V)
    change (_ : P.obj (op V)) = _
    exact Subsingleton.elim _ _
  · constructor
    intro U s
    let f := aug.app (op (SimplexCategory.mk 0))
    let a := sectionEquiv (L.obj (op (SimplexCategory.mk 0))) U
      ((pullback.fst f f).app (op U) s)
    let b := sectionEquiv (L.obj (op (SimplexCategory.mk 0))) U
      ((pullback.snd f f).app (op U) s)
    obtain ⟨S, hS, hS'⟩ := homLocallySurjective_one_of_fullyFaithful J.toGrothendieck
      (FormalCoproduct.incl C) G hG L (hunit 0) U a b
    apply J.toGrothendieck.superset_covering ?_ hS
    intro V g hg
    obtain ⟨x, hx₁, hx₂⟩ := hS' g hg
    let t := (sectionEquiv (L.obj (op (SimplexCategory.mk 1))) V).symm x
    refine ⟨t, ?_⟩
    apply presheaf_pullback_section_ext.{max w u v, v, u} f f V
    · have hx := congrArg (sectionEquiv (L.obj (op (SimplexCategory.mk 0))) V).symm hx₁
      rw [sectionEquiv_symm_postcomp, sectionEquiv_symm_precomp] at hx
      simp only [a, Equiv.symm_apply_apply] at hx
      change ((oneMatchingMap (associatedSimplicialPresheaf.{v} L)
        P aug ≫ pullback.fst f f).app (op V)) t = _
      rw [oneMatchingMap_fst, NatTrans.naturality_apply]
      exact hx
    · have hx := congrArg (sectionEquiv (L.obj (op (SimplexCategory.mk 0))) V).symm hx₂
      rw [sectionEquiv_symm_postcomp, sectionEquiv_symm_precomp] at hx
      simp only [b, Equiv.symm_apply_apply] at hx
      change ((oneMatchingMap (associatedSimplicialPresheaf.{v} L)
        P aug ≫ pullback.snd f f).app (op V)) t = _
      rw [oneMatchingMap_snd, NatTrans.naturality_apply]
      exact hx
  · intro n hn
    have := hasPositiveCoskeleta (C := C) n hn
    exact locallySurjective_of_homLocallySurjective J.toGrothendieck _
      (homLocallySurjective_unit_of_fullyFaithful J.toGrothendieck
        (FormalCoproduct.incl C) G hG L n _ (hunit n))

omit [HasEqualizers C] [HasPullbacks C] in
/-- **Local surjectivity on test objects ascends along a fully faithful functor**, for an
arbitrary morphism.  Fullness turns a morphism out of the image of a test object into one in the
source category, where the local lift is available, and faithfulness is not even needed for the
conclusion -- only to name the preimage. -/
private theorem homLocallySurjective_comp_of_fullyFaithful
    {A : Type d} [Category.{e} A] {D : Type q} [Category.{w} D]
    (J : GrothendieckTopology C) (T : C ⥤ A) (G : A ⥤ D) (hG : G.FullyFaithful)
    {X Y : A} (p : X ⟶ Y) (h : HomLocallySurjective J T p) :
    HomLocallySurjective J (T ⋙ G) (G.map p) := by
  intro U s
  apply J.superset_covering ?_ (h U (hG.preimage s))
  rintro V f ⟨t, ht⟩
  refine ⟨G.map t, ?_⟩
  change G.map t ≫ G.map p = G.map (T.map f) ≫ s
  rw [← G.map_comp, ht, G.map_comp, hG.map_preimage]

omit [HasEqualizers C] in
/-- **A covering morphism of semi-representable objects of the site becomes a covering morphism
for `localPretopology`.**  This is the companion of `isHypercovering_yonedaFormal`: together they
carry a hypercovering of the final presheaf *and* a covering of one of its terms into the slice
over the final presheaf, which is where [Stacks, Tag 01GJ] is available. -/
theorem isCoveringOver_yonedaFormal_map (J : Pretopology C)
    {X Y : FormalCoproduct.{max w u v} C} (p : X ⟶ Y) (hp : IsCovering J p) :
    IsCoveringOver (localPretopology.{v, u, max w u v} J) (yonedaFormal.map p) :=
  isCoveringOver_of_homLocallySurjective J _
    (homLocallySurjective_comp_of_fullyFaithful J.toGrothendieck (FormalCoproduct.incl C)
      yonedaFormal yonedaFormalFullyFaithful p
      (homLocallySurjective_incl_of_isCovering J p hp))

/-- **The reverse transfer of [Stacks, Tag 0DAX]: a hypercovering of the final presheaf becomes a
hypercovering, for `localPretopology`, of the terminal presheaf.**

This is the converse of `hypercoveringOfTerminal_lift`, and it is what lets results about
hypercoverings of an *object* -- [Stacks, Tag 01GJ] above all, whose chain of permanence lemmas
needs a terminal object and all finite limits -- be applied to hypercoverings of the final
presheaf: the slice over the final presheaf is a slice over a terminal object in a category with
all limits.

Each of the three clauses of [Stacks, Tag 09VU] is carried across in two steps.  First the clause
is read as local surjectivity on morphisms out of the test objects -- in degree zero directly, in
degree one through `homLocallySurjective_one_pair` and in higher degrees through
`homLocallySurjective_of_locallySurjective`; `yonedaFormal` being fully faithful, that condition
passes to the image by `homLocallySurjective_one_comp_of_fullyFaithful` and
`homLocallySurjective_unit_comp_of_fullyFaithful`.  Then
`isCoveringOver_of_homLocallySurjective` turns it back into a covering family for
`localPretopology`.

Nothing is assumed of `C` beyond the equalizers and fibre products a hypercovering of a presheaf
already needs; in particular no terminal object of `C`. -/
theorem isHypercovering_yonedaFormal (J : Pretopology C)
    (H : HypercoveringOfTerminal.{max w u v} J) :
    IsHypercovering (localPretopology.{v, u, max w u v} J)
      (H.toSimplicialObject ⋙ yonedaFormal) := by
  constructor
  · refine isCoveringOver_of_homLocallySurjective J _ ?_
    intro U s
    have hU := Types.isTerminalEquivUnique _ (isTerminalLiftedPresheafObj (C := C) U)
    refine J.toGrothendieck.superset_covering ?_
      (H.locallySurjective_zero.imageSieve_mem (U := U) hU.default)
    rintro V f ⟨y, -⟩
    exact ⟨yonedaFormal.map
      (sectionEquiv (H.toSimplicialObject.obj (op (SimplexCategory.mk 0))) V y),
      terminal.hom_ext _ _⟩
  · intro n
    refine isCoveringOver_of_homLocallySurjective J _ ?_
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · exact homLocallySurjective_one_comp_of_fullyFaithful J.toGrothendieck
        (FormalCoproduct.incl C) yonedaFormal yonedaFormalFullyFaithful H.toSimplicialObject
        (homLocallySurjective_one_pair J H)
    · have := hasPositiveCoskeleta.{max w u v} (C := C) n hpos
      exact homLocallySurjective_unit_comp_of_fullyFaithful J.toGrothendieck
        (FormalCoproduct.incl C) yonedaFormal yonedaFormalFullyFaithful H.toSimplicialObject n _
        (homLocallySurjective_of_locallySurjective J.toGrothendieck
          (((SimplicialObject.coskAdj n).unit.app H.toSimplicialObject).app
            (op (SimplexCategory.mk (n + 1))))
          (H.locallySurjective_succ n hpos))

end

end Descent

end Stacks.CategoryTheory.Hypercovering

end
