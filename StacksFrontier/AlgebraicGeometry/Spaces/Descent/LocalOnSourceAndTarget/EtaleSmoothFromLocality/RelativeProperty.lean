module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.LocalOnSourceAndTarget.EtaleSmoothFromLocality.SchemeNeighborhoods

/-!
# Étale-smooth locality from locality hypotheses: the induced property of schemes

The property of morphisms of schemes over `S` of size below the cutoff of the site induced by a
property of morphisms of algebraic spaces over `S`, its stability under precomposition with étale
morphisms, postcomposition with open immersions and base change, its descent along surjective
smooth morphisms and locality on the source, and its largest open locus.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v w

namespace AlgebraicGeometry

/-- A scheme over `S` of size below the cutoff of the site, read as an object of the big fppf site
of `S`. -/
abbrev relativeScheme
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : Scheme.{u}) [X.Over S] [Fact (B.Contains X)] :
    BigFppfOver B S hS :=
  Over.mk (ObjectProperty.homMk (X ↘ S) : B.obj (Fact.out : B.Contains X) ⟶ B.obj hS)

/-- A morphism over `S` of schemes of size below the cutoff of the site, read as a morphism of the
big fppf site of `S`. -/
abbrev relativeMap
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : Scheme.{u}} [X.Over S] [Y.Over S]
    [Fact (B.Contains X)] [Fact (B.Contains Y)] (f : X ⟶ Y) [f.IsOver S] :
    relativeScheme B S hS X ⟶ relativeScheme B S hS Y :=
  Over.homMk (ObjectProperty.homMk f) (ObjectProperty.hom_ext _ (comp_over f S))

/-- The property of morphisms of schemes over `S` of size below the cutoff of the site induced by a
property of morphisms of algebraic spaces over `S`. -/
abbrev relativeProperty
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    {X Y : Scheme.{u}} [Y.Over S]
    [Fact (B.Contains X)] [Fact (B.Contains Y)] (f : X ⟶ Y) : Prop :=
  letI : X.Over S := ⟨f ≫ Y ↘ S⟩
  letI : f.IsOver S := ⟨rfl⟩
  P (schemeMap B S hS (relativeMap B S hS f))

/-- The induced property of a morphism over `S` is the property of the corresponding morphism of
represented algebraic spaces, for the structure morphism the morphism already carries. -/
theorem relativeProperty_iff
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    {X Y : Scheme.{u}} [hX : X.Over S] [Y.Over S]
    [Fact (B.Contains X)] [Fact (B.Contains Y)] (f : X ⟶ Y) [f.IsOver S] :
    relativeProperty B S hS P f ↔ P (schemeMap B S hS (relativeMap B S hS f)) := by
  have h : (OverClass.ofHom (f ≫ Y ↘ S) : X.Over S) = hX := by
    change OverClass.ofHom (f ≫ Y ↘ S) = OverClass.ofHom (X ↘ S)
    exact congrArg OverClass.ofHom (comp_over f S)
  cases h
  rfl

/-- An open subscheme of a scheme of size below the cutoff of the site again has size below it. -/
theorem bounded_open
    (B : BigFppfSite.{u}) {X : Scheme.{u}} [Fact (B.Contains X)]
    (U : X.Opens) : Fact (B.Contains U.toScheme) :=
  ⟨Scheme.size_lt_of_isOpenImmersion U.ι Fact.out⟩

attribute [local instance] bounded_open

/-- A fibre product of two schemes of size below the cutoff of the site again has size below it. -/
theorem bounded_pullback
    (B : BigFppfSite.{u}) {X Y Z : Scheme.{u}}
    [Fact (B.Contains X)] [Fact (B.Contains Y)] (f : X ⟶ Z) (g : Y ⟶ Z) :
    Fact (B.Contains (Limits.pullback f g)) :=
  ⟨Scheme.size_pullback_lt f g Fact.out Fact.out⟩

attribute [local instance] bounded_pullback

/-- Affine space on a finite index type over a scheme of size below the cutoff of the site again
has size below it. -/
theorem bounded_affineSpace
    (B : BigFppfSite.{u}) {X : Scheme.{u}} [Fact (B.Contains X)]
    (n : Type u) [Finite n] : Fact (B.Contains (AffineSpace n X)) :=
  ⟨Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact (AffineSpace n X ↘ X)
    Fact.out⟩

attribute [local instance] bounded_affineSpace

/-- A property of scheme morphisms stable under base change is inherited by the represented
morphism of presheaves induced by a morphism of the site. -/
theorem schemeMap_presheaf_property
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (R : MorphismProperty Scheme.{u}) [R.IsStableUnderBaseChange]
    {X Y : BigFppfOver B S hS} (f : X ⟶ Y)
    (hf : R ((BigFppfOver.toScheme B S hS).map f)) :
    (MorphismProperty.inverseImage R (BigFppfOver.toScheme B S hS)).presheaf
      (yoneda.map f) := by
  let F := BigFppfOver.toScheme B S hS
  have : Limits.PreservesLimitsOfShape Limits.WalkingCospan F :=
    Limits.comp_preservesLimitsOfShape _ _
  have : (MorphismProperty.inverseImage R F).IsStableUnderBaseChange := by
    constructor
    intro X Y Z W f g a b sq hf
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := R) (sq.map F) hf
  exact (MorphismProperty.relative_map_iff (F := yoneda)
    (P := MorphismProperty.inverseImage R F) (f := f)).mpr hf

/-- A family of morphisms of the site whose underlying scheme morphisms are jointly surjective
induces a family which is jointly surjective on points. -/
private theorem schemeMap_jointly_surjective
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type v} {X : BigFppfOver B S hS}
    (U : I → BigFppfOver B S hS) (a : ∀ i, U i ⟶ X)
    (ha : ∀ x : (BigFppfOver.toScheme B S hS).obj X,
      ∃ i z, (BigFppfOver.toScheme B S hS).map (a i) z = x) :
    (⋃ i, Set.range (Space.pointsMap B S hS (yoneda.obj (U i))
      (yoneda.map (a i)))) = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
  obtain ⟨i, z, hz⟩ := ha (Space.pointsToScheme B S hS X x)
  obtain ⟨w, hw⟩ := Space.surjective_pointsToScheme B S hS (U i) z
  refine ⟨i, w, Space.injective_pointsToScheme B S hS X ?_⟩
  rw [Space.pointsToScheme_pointsMap, hw, hz]

/-- The functor from the big fppf site of `S` to algebraic spaces over `S` sending an object to the
algebraic space it represents. -/
noncomputable def schemeEmbedding
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    BigFppfOver B S hS ⥤ AlgebraicSpaces B S hS where
  obj U := Space.representedAlgebraicSpace B S hS U
  map f := schemeMap B S hS f

/-- A square of the site which is cartesian on underlying schemes is cartesian in the category of
algebraic spaces over `S`. -/
private theorem schemeMap_isPullback
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {A X T Y : BigFppfOver B S hS}
    {a : A ⟶ X} {h : A ⟶ T} {f : X ⟶ Y} {b : T ⟶ Y}
    (sq : IsPullback
      ((BigFppfOver.toScheme B S hS).map a)
      ((BigFppfOver.toScheme B S hS).map h)
      ((BigFppfOver.toScheme B S hS).map f)
      ((BigFppfOver.toScheme B S hS).map b)) :
    IsPullback (schemeMap B S hS a) (schemeMap B S hS h)
      (schemeMap B S hS f) (schemeMap B S hS b) := by
  have sq' := IsPullback.of_map_of_faithful
    (BigFppfOver.toScheme B S hS) sq
  exact IsPullback.of_map_of_faithful
    (ObjectProperty.ι (IsAlgebraicSpace B S hS)) (sq'.map yoneda)

/-- A morphism of the site which is smooth on underlying schemes induces a smooth morphism of
represented algebraic spaces. -/
private theorem schemeMap_smooth
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : BigFppfOver B S hS} (f : X ⟶ Y)
    (hf : Smooth ((BigFppfOver.toScheme B S hS).map f)) :
    Space.IsSmooth B S hS (yoneda.map f) := by
  apply (Space.holdsOnEveryEtaleChart_iff_surjectiveChart B S hS _
    Smooth.isEtaleLocalOnSourceAndTarget
    (isAlgebraicSpace_yoneda B S hS X)
    (isAlgebraicSpace_yoneda B S hS Y) (yoneda.map f)).mpr
  refine ⟨X, Y, 𝟙 _, 𝟙 _, f, AlgebraicGeometry.Space.presheaf_etale_id B S hS X,
    AlgebraicGeometry.Space.presheaf_etale_id B S hS Y, ?_, by simp, hf⟩
  exact (yoneda.map_id X) ▸
    schemeMap_presheaf_property B S hS (@Surjective) (𝟙 X) (by
      change Surjective (𝟙 _)
      infer_instance)

/-- The induced property of a composite over `S` is the property of the composite of the
corresponding morphisms of represented algebraic spaces. -/
private theorem relativeProperty_comp_iff
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    {A X Y : Scheme.{u}} [A.Over S] [X.Over S] [Y.Over S]
    [Fact (B.Contains A)] [Fact (B.Contains X)] [Fact (B.Contains Y)]
    (a : A ⟶ X) (f : X ⟶ Y) [a.IsOver S] [f.IsOver S] :
    relativeProperty B S hS P (a ≫ f) ↔
      P (schemeMap B S hS (relativeMap B S hS a) ≫ schemeMap B S hS (relativeMap B S hS f)) := by
  rw [relativeProperty_iff B S hS P (a ≫ f)]
  change P ((schemeEmbedding B S hS).map (relativeMap B S hS a ≫ relativeMap B S hS f)) ↔ _
  rw [Functor.map_comp]
  rfl

section RelativeRules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (P : MorphismProperty (AlgebraicSpaces B S hS))
  [hsource : P.IsLocalAtSource (Space.Topology.precoverage.{u, u + 1} .etale B S hS)]
  [htarget : P.IsLocalAtTarget (Space.Topology.precoverage.{u, u + 1} .smooth B S hS)]
  [hopen : P.RespectsRight (fun ⦃X Y : AlgebraicSpaces B S hS⦄
    (f : X ⟶ Y) => Space.IsOpenImmersion B S hS f.hom)]

omit htarget hopen in
/-- The induced property of morphisms of schemes over `S` is stable under precomposition with an
étale morphism. -/
private theorem relative_precomp_etale
    {A X Y : Scheme.{u}} [Y.Over S]
    [Fact (B.Contains A)] [Fact (B.Contains X)] [Fact (B.Contains Y)]
    (a : A ⟶ X) (f : X ⟶ Y) [Etale a]
    (hf : relativeProperty B S hS P f) : relativeProperty B S hS P (a ≫ f) := by
  let : X.Over S := ⟨f ≫ Y ↘ S⟩
  let : A.Over S := ⟨a ≫ X ↘ S⟩
  have : f.IsOver S := ⟨rfl⟩
  have : a.IsOver S := ⟨rfl⟩
  rw [relativeProperty_iff B S hS P f] at hf
  rw [relativeProperty_comp_iff B S hS P a f]
  have ha := etale_of_presheaf_etale B S hS _
    (schemeMap_presheaf_property B S hS (@Etale) (relativeMap B S hS a)
      (show Etale a from inferInstance))
  exact Space.comp_isEtale (P := P)
    (schemeMap B S hS (relativeMap B S hS a))
    (schemeMap B S hS (relativeMap B S hS f)) ha hf

omit hsource htarget in
/-- The induced property of morphisms of schemes over `S` is stable under postcomposition with an
open immersion over `S`. -/
theorem relative_postcomp_open
    {X Y Z : Scheme.{u}} [Y.Over S] [Z.Over S]
    [Fact (B.Contains X)] [Fact (B.Contains Y)] [Fact (B.Contains Z)]
    (f : X ⟶ Y) (b : Y ⟶ Z) [b.IsOver S] [IsOpenImmersion b]
    (hf : relativeProperty B S hS P f) : relativeProperty B S hS P (f ≫ b) := by
  let : X.Over S := ⟨f ≫ Y ↘ S⟩
  have : f.IsOver S := ⟨rfl⟩
  rw [relativeProperty_iff B S hS P f] at hf
  rw [relativeProperty_comp_iff B S hS P f b]
  exact MorphismProperty.RespectsRight.postcomp
    (Q := fun ⦃X Y : AlgebraicSpaces B S hS⦄ (g : X ⟶ Y) =>
      Space.IsOpenImmersion B S hS g.hom)
    _ (schemeMap_presheaf_property B S hS (@IsOpenImmersion)
      (relativeMap B S hS b) (show IsOpenImmersion b from inferInstance)) _ hf

omit hsource hopen in
/-- The induced property of morphisms of schemes over `S` is stable under base change along a
smooth morphism over `S`. -/
private theorem relative_of_isPullback
    {A X T Y : Scheme.{u}} [T.Over S] [Y.Over S]
    [Fact (B.Contains A)] [Fact (B.Contains X)]
    [Fact (B.Contains T)] [Fact (B.Contains Y)]
    (a : A ⟶ X) (h : A ⟶ T) (f : X ⟶ Y) (b : T ⟶ Y)
    [b.IsOver S]
    (sq : IsPullback a h f b) [Smooth b]
    (hf : relativeProperty B S hS P f) : relativeProperty B S hS P h := by
  let : X.Over S := ⟨f ≫ Y ↘ S⟩
  let : A.Over S := ⟨h ≫ T ↘ S⟩
  have : f.IsOver S := ⟨rfl⟩
  have : h.IsOver S := ⟨rfl⟩
  have : a.IsOver S := ⟨by
    change a ≫ (f ≫ Y ↘ S) = h ≫ T ↘ S
    rw [← Category.assoc, sq.w, Category.assoc, comp_over]⟩
  rw [relativeProperty_iff B S hS P f] at hf
  rw [relativeProperty_iff B S hS P h]
  exact property_of_isPullback_smooth B S hS P _ _ _ _
    (schemeMap_isPullback B S hS (a := relativeMap B S hS a)
      (h := relativeMap B S hS h) (f := relativeMap B S hS f)
      (b := relativeMap B S hS b) sq)
    (schemeMap_smooth B S hS _ (show Smooth b from inferInstance)) hf

omit hsource hopen in
/-- The induced property of morphisms of schemes over `S` descends along a surjective smooth base
change over `S`. -/
theorem relative_of_surjective_isPullback
    {A X T Y : Scheme.{u}} [T.Over S] [Y.Over S]
    [Fact (B.Contains A)] [Fact (B.Contains X)]
    [Fact (B.Contains T)] [Fact (B.Contains Y)]
    (a : A ⟶ X) (h : A ⟶ T) (f : X ⟶ Y) (b : T ⟶ Y)
    [b.IsOver S]
    (sq : IsPullback a h f b) [Smooth b] [Surjective b]
    (hh : relativeProperty B S hS P h) : relativeProperty B S hS P f := by
  let : X.Over S := ⟨f ≫ Y ↘ S⟩
  let : A.Over S := ⟨h ≫ T ↘ S⟩
  have : f.IsOver S := ⟨rfl⟩
  have : h.IsOver S := ⟨rfl⟩
  have : a.IsOver S := ⟨by
    change a ≫ (f ≫ Y ↘ S) = h ≫ T ↘ S
    rw [← Category.assoc, sq.w, Category.assoc, comp_over]⟩
  rw [relativeProperty_iff B S hS P h] at hh
  rw [relativeProperty_iff B S hS P f]
  apply of_isPullback_surjective_smooth B S hS P _ _ _ _
    (schemeMap_isPullback B S hS (a := relativeMap B S hS a)
      (h := relativeMap B S hS h) (f := relativeMap B S hS f)
      (b := relativeMap B S hS b) sq)
    (schemeMap_smooth B S hS _ (show Smooth b from inferInstance)) _ hh
  have hsurj := schemeMap_jointly_surjective B S hS
    (fun _ : Unit => relativeScheme B S hS T)
    (fun _ => relativeMap B S hS b)
    (fun y => ⟨(), b.surjective y⟩)
  simpa only [Set.iUnion_const, Set.range_eq_univ, schemeMap,
    ObjectProperty.homMk_hom] using hsurj

omit htarget hopen in
/-- The induced property of morphisms of schemes over `S` is local on the source for jointly
surjective families of étale morphisms. -/
theorem relative_of_source_cover
    {X Y : Scheme.{u}} [Y.Over S]
    [Fact (B.Contains X)] [Fact (B.Contains Y)]
    (f : X ⟶ Y) {I : Type v} [Small.{u + 1} I]
    (U : I → Scheme.{u}) [∀ i, Fact (B.Contains (U i))]
    (a : ∀ i, U i ⟶ X) (ha : ∀ i, Etale (a i))
    (hsurj : ∀ x : X, ∃ i z, a i z = x)
    (hf : ∀ i, relativeProperty B S hS P (a i ≫ f)) :
    relativeProperty B S hS P f := by
  classical
  let : X.Over S := ⟨f ≫ Y ↘ S⟩
  have : f.IsOver S := ⟨rfl⟩
  let (i : I) : (U i).Over S := ⟨a i ≫ X ↘ S⟩
  let (i : I) : (a i).IsOver S := ⟨rfl⟩
  let e := (equivShrink I).symm
  let U' (i : Shrink.{u + 1} I) := relativeScheme B S hS (U (e i))
  let a' (i : Shrink.{u + 1} I) := relativeMap B S hS (a (e i))
  let R := Presieve.ofArrows (fun i => Space.representedAlgebraicSpace B S hS (U' i))
    (fun i => schemeMap B S hS (a' i))
  have hR : R ∈ Space.Topology.precoverage.{u, u + 1} .etale B S hS
      (Space.representedAlgebraicSpace B S hS (relativeScheme B S hS X)) := by
    refine ⟨Shrink.{u + 1} I, _, _, rfl,
      (isAlgebraicSpace_yoneda B S hS _),
      (fun i => isAlgebraicSpace_yoneda B S hS _),
      (isAlgebraicSpace_yoneda B S hS _),
      (fun i => isAlgebraicSpace_yoneda B S hS _), ?_, ?_⟩
    · intro i
      exact etale_of_presheaf_etale B S hS _
        (schemeMap_presheaf_property B S hS (@Etale) (a' i) (ha (e i)))
    · exact schemeMap_jointly_surjective B S hS U' a' (fun x => by
        obtain ⟨i, z, hz⟩ := hsurj x
        refine ⟨e.symm i, ?_⟩
        change ∃ z : U (e (e.symm i)), a (e (e.symm i)) z = x
        rw [e.apply_symm_apply]
        exact ⟨z, hz⟩)
  rw [relativeProperty_iff B S hS P f]
  apply MorphismProperty.IsLocalAtSource.of_forall_comp (P := P) hR
  rintro Z g ⟨i⟩
  exact (relativeProperty_comp_iff B S hS P (a (e i)) f).mp (hf (e i))

end RelativeRules

/-- A fibre product read as a scheme over the target of its second projection. -/
@[instance_reducible] noncomputable def pullbackCanonicallyOverRight
    {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (Limits.pullback f g).CanonicallyOver Y where
  hom := Limits.pullback.snd f g

attribute [local instance] pullbackCanonicallyOverRight

/-- The second projection of a fibre product is a morphism over the base of its target. -/
theorem pullbackSnd_isOver
    {X Y Z S : Scheme.{u}} [Y.Over S] (f : X ⟶ Z) (g : Y ⟶ Z) :
    (Limits.pullback.snd f g).IsOver S := ⟨rfl⟩

attribute [local instance] pullbackSnd_isOver

/-- The first projection of a fibre product of schemes over `S` along morphisms over `S` is a
morphism over `S`. -/
theorem pullbackFst_isOver
    {X Y Z S : Scheme.{u}} [X.Over S] [Y.Over S] [Z.Over S]
    (f : X ⟶ Z) (g : Y ⟶ Z) [f.IsOver S] [g.IsOver S] :
    (Limits.pullback.fst f g).IsOver S := by
  constructor
  change Limits.pullback.fst f g ≫ X ↘ S = Limits.pullback.snd f g ≫ Y ↘ S
  rw [← comp_over f S, ← comp_over g S, Limits.pullback.condition_assoc]

attribute [local instance] pullbackFst_isOver

/-- The morphism into a fibre product induced by a commutative square is over `S` as soon as its
second component is. -/
theorem pullbackLift_isOver
    {A X Y Z S : Scheme.{u}} [A.Over S] [Y.Over S]
    {f : X ⟶ Z} {g : Y ⟶ Z} (a : A ⟶ X) (b : A ⟶ Y)
    (h : a ≫ f = b ≫ g) [b.IsOver S] :
    (Limits.pullback.lift a b h).IsOver S := by
  constructor
  change Limits.pullback.lift a b h ≫ (Limits.pullback.snd f g ≫ Y ↘ S) = A ↘ S
  rw [Limits.pullback.lift_snd_assoc, comp_over]

attribute [local instance] pullbackLift_isOver

section RelativeOpen

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (P : MorphismProperty (AlgebraicSpaces B S hS))
  [hsource : P.IsLocalAtSource (Space.Topology.precoverage.{u, u + 1} .etale B S hS)]
  [htarget : P.IsLocalAtTarget (Space.Topology.precoverage.{u, u + 1} .smooth B S hS)]
  [hopen : P.RespectsRight (fun ⦃X Y : AlgebraicSpaces B S hS⦄
    (f : X ⟶ Y) => Space.IsOpenImmersion B S hS f.hom)]

omit htarget hopen in
/-- The induced property of morphisms of schemes over `S` is invariant under precomposition with an
isomorphism. -/
theorem relative_cancel_left_iso
    {A X Y : Scheme.{u}} [Y.Over S]
    [Fact (B.Contains A)] [Fact (B.Contains X)] [Fact (B.Contains Y)]
    (a : A ⟶ X) [IsIso a] (f : X ⟶ Y) :
    relativeProperty B S hS P (a ≫ f) ↔ relativeProperty B S hS P f := by
  constructor
  · intro h
    simpa only [IsIso.inv_hom_id_assoc] using
      relative_precomp_etale B S hS P (inv a) (a ≫ f) h
  · exact relative_precomp_etale B S hS P a f

omit hsource hopen in
/-- The induced property of morphisms of schemes over `S` is inherited by the base change along a
smooth morphism over `S`, stated for the chosen fibre product. -/
theorem relative_pullback_snd
    {X Y T : Scheme.{u}} [Y.Over S] [T.Over S]
    [Fact (B.Contains X)] [Fact (B.Contains Y)] [Fact (B.Contains T)]
    (f : X ⟶ Y) (b : T ⟶ Y) [b.IsOver S] [Smooth b]
    (hf : relativeProperty B S hS P f) :
    relativeProperty B S hS P (Limits.pullback.snd f b) := by
  let : X.Over S := ⟨f ≫ Y ↘ S⟩
  have : f.IsOver S := ⟨rfl⟩
  exact relative_of_isPullback B S hS P _ _ f b
    (IsPullback.of_hasPullback f b) hf

/-- The largest open of the source on which the induced property of morphisms of schemes over `S`
holds for the restriction of a morphism. -/
def relativeLargestOpen
    {X Y : Scheme.{u}} [Y.Over S]
    [Fact (B.Contains X)] [Fact (B.Contains Y)] (f : X ⟶ Y) : X.Opens :=
  sSup {U : X.Opens | relativeProperty B S hS P (U.ι ≫ f)}

omit hsource htarget hopen in
/-- A point lies in the largest open locus exactly when some open neighbourhood of it is a locus
for the induced property. -/
theorem mem_relativeLargestOpen
    {X Y : Scheme.{u}} [Y.Over S]
    [Fact (B.Contains X)] [Fact (B.Contains Y)] (f : X ⟶ Y) (x : X) :
    x ∈ relativeLargestOpen B S hS P f ↔
      ∃ U : X.Opens, x ∈ U ∧ relativeProperty B S hS P (U.ι ≫ f) := by
  change x ∈ sSup {U : X.Opens | relativeProperty B S hS P (U.ι ≫ f)} ↔ _
  rw [TopologicalSpace.Opens.mem_sSup]
  constructor
  · rintro ⟨U, hU, hx⟩
    exact ⟨U, hx, hU⟩
  · rintro ⟨U, hx, hU⟩
    exact ⟨U, hU, hx⟩

omit htarget hopen in
/-- The largest open locus is the greatest open whose restriction has the induced property. -/
theorem relativeLargestOpen_isGreatest
    {X Y : Scheme.{u}} [Y.Over S]
    [Fact (B.Contains X)] [Fact (B.Contains Y)] (f : X ⟶ Y) :
    IsGreatest {U : X.Opens | relativeProperty B S hS P (U.ι ≫ f)}
      (relativeLargestOpen B S hS P f) := by
  let I := {U : X.Opens // relativeProperty B S hS P (U.ι ≫ f)}
  let W := relativeLargestOpen B S hS P f
  have hi (i : I) : i.1 ≤ W := le_sSup i.2
  refine ⟨relative_of_source_cover B S hS P (W.ι ≫ f) (fun i : I => i.1.toScheme)
    (fun i => X.homOfLE (hi i)) (fun _ => inferInstance) (fun x => ?_) (fun i => ?_),
    fun U hU => le_sSup hU⟩
  · obtain ⟨U, hx, hP⟩ := (mem_relativeLargestOpen B S hS P f x.1).mp x.2
    exact ⟨⟨U, hP⟩, ⟨x.1, hx⟩, Subtype.ext (Scheme.homOfLE_apply _ _)⟩
  · simpa only [← Category.assoc, Scheme.homOfLE_ι] using i.2

omit htarget hopen in
/-- The largest open locus is everything exactly when the morphism itself has the induced
property. -/
theorem relativeLargestOpen_eq_top_iff
    {X Y : Scheme.{u}} [Y.Over S]
    [Fact (B.Contains X)] [Fact (B.Contains Y)] (f : X ⟶ Y) :
    relativeLargestOpen B S hS P f = ⊤ ↔ relativeProperty B S hS P f := by
  refine ⟨fun h => ?_, fun h => top_unique ((relativeLargestOpen_isGreatest B S hS P f).2
    ((relative_cancel_left_iso B S hS P X.topIso.hom f).mpr h))⟩
  have hP := (relativeLargestOpen_isGreatest B S hS P f).1
  rw [h] at hP
  exact (relative_cancel_left_iso B S hS P X.topIso.hom f).mp hP

omit htarget hopen in
/-- The inverse image of the largest open locus along an étale morphism is the largest open locus
of the composite. -/
theorem preimage_relativeLargestOpen_etale
    {A X Y : Scheme.{u}} [Y.Over S]
    [Fact (B.Contains A)] [Fact (B.Contains X)] [Fact (B.Contains Y)]
    (a : A ⟶ X) [Etale a] (f : X ⟶ Y) :
    a ⁻¹ᵁ relativeLargestOpen B S hS P f =
      relativeLargestOpen B S hS P (a ≫ f) := by
  let W := relativeLargestOpen B S hS P f
  let W' := relativeLargestOpen B S hS P (a ≫ f)
  have hW := relativeLargestOpen_isGreatest B S hS P f
  have hW' := relativeLargestOpen_isGreatest B S hS P (a ≫ f)
  apply le_antisymm
  · apply hW'.2
    have h := relative_precomp_etale B S hS P (a ∣_ W) (W.ι ≫ f) hW.1
    rwa [← Category.assoc, morphismRestrict_ι, Category.assoc] at h
  · intro x hx
    let g : W'.toScheme ⟶ X := W'.ι ≫ a
    let U : X.Opens := ⟨Set.range g, g.isOpenMap.isOpen_range⟩
    have hsub : Set.range g ⊆ Set.range U.ι := by simp [U]
    let q := IsOpenImmersion.lift U.ι g hsub
    have hfac : q ≫ U.ι = g := IsOpenImmersion.lift_fac U.ι g hsub
    have : Etale q := MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsOpenImmersion.isPullback_lift_id g U.ι hsub).flip (show Etale g from inferInstance)
    have hq : Function.Surjective q := by
      intro y
      obtain ⟨z, hz⟩ := y.property
      exact ⟨z, U.ι.isOpenEmbedding.injective ((congrArg (fun k => k z) hfac).trans hz)⟩
    have hU : relativeProperty B S hS P (U.ι ≫ f) := by
      apply relative_of_source_cover B S hS P (U.ι ≫ f)
        (fun _ : Unit => W'.toScheme) (fun _ => q) (fun _ => inferInstance)
        (fun y => ⟨(), hq y⟩)
      intro i
      rw [← Category.assoc, hfac]
      exact hW'.1
    exact hW.2 hU ⟨⟨x, hx⟩, rfl⟩

end RelativeOpen

/-- A member of the standard affine cover of a scheme, read as a scheme over that scheme. -/
@[instance_reducible] noncomputable def affineCoverCanonicallyOver
    (X : Scheme.{u}) (i : X.affineCover.I₀) : (X.affineCover.X i).CanonicallyOver X where
  hom := X.affineCover.f i

attribute [local instance] affineCoverCanonicallyOver

/-- A member of the standard affine cover of a scheme over `S` is a morphism over `S`. -/
theorem affineCoverMap_isOver
    {X S : Scheme.{u}} [X.Over S] (i : X.affineCover.I₀) :
    (X.affineCover.f i).IsOver S := ⟨rfl⟩

attribute [local instance] affineCoverMap_isOver

/-- A member of the standard affine cover of a scheme of size below the cutoff of the site again
has size below it. -/
theorem bounded_affineCover
    (B : BigFppfSite.{u}) {X : Scheme.{u}} [Fact (B.Contains X)]
    (i : X.affineCover.I₀) : Fact (B.Contains (X.affineCover.X i)) :=
  ⟨Scheme.size_lt_of_isOpenImmersion (X.affineCover.f i) Fact.out⟩

attribute [local instance] bounded_affineCover

section RelativeMore

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (P : MorphismProperty (AlgebraicSpaces B S hS))
  [hsource : P.IsLocalAtSource (Space.Topology.precoverage.{u, u + 1} .etale B S hS)]
  [htarget : P.IsLocalAtTarget (Space.Topology.precoverage.{u, u + 1} .smooth B S hS)]
  [hopen : P.RespectsRight (fun ⦃X Y : AlgebraicSpaces B S hS⦄
    (f : X ⟶ Y) => Space.IsOpenImmersion B S hS f.hom)]

omit htarget hopen in
/-- A morphism of schemes over `S` with empty source has the induced property. -/
theorem relative_of_empty_source
    {X Y : Scheme.{u}} [Y.Over S] [IsEmpty X]
    [Fact (B.Contains X)] [Fact (B.Contains Y)] (f : X ⟶ Y) :
    relativeProperty B S hS P f :=
  relative_of_source_cover B S hS P f (fun _ : Empty => X)
    (fun _ => 𝟙 X) (fun _ => inferInstance) (fun x => isEmptyElim x)
    (fun i => isEmptyElim i)

omit hsource hopen in
/-- The induced property of morphisms of schemes over `S` descends along a surjective smooth
morphism over `S`, stated for the chosen fibre product. -/
theorem relative_of_pullback_snd
    {X Y T : Scheme.{u}} [Y.Over S] [T.Over S]
    [Fact (B.Contains X)] [Fact (B.Contains Y)] [Fact (B.Contains T)]
    (f : X ⟶ Y) (b : T ⟶ Y) [b.IsOver S] [Smooth b] [Surjective b]
    (hf : relativeProperty B S hS P (Limits.pullback.snd f b)) :
    relativeProperty B S hS P f := by
  let : X.Over S := ⟨f ≫ Y ↘ S⟩
  have : f.IsOver S := ⟨rfl⟩
  exact relative_of_surjective_isPullback B S hS P _ _ f b
    (IsPullback.of_hasPullback f b) hf

omit htarget in
/-- The induced property of morphisms of schemes over `S` may be checked on the base changes along
the standard affine cover of the target. -/
theorem relative_of_target_affineCover
    {X Y : Scheme.{u}} [Y.Over S]
    [Fact (B.Contains X)] [Fact (B.Contains Y)] (f : X ⟶ Y)
    (hf : ∀ i : Y.affineCover.I₀,
      relativeProperty B S hS P (Limits.pullback.snd f (Y.affineCover.f i))) :
    relativeProperty B S hS P f := by
  apply relative_of_source_cover B S hS P f
    (fun i => Limits.pullback f (Y.affineCover.f i))
    (fun i => Limits.pullback.fst f (Y.affineCover.f i))
    (fun _ => inferInstance) (Scheme.Cover.exists_eq (Y.affineCover.pullback₁ f))
  intro i
  rw [Limits.pullback.condition]
  exact relative_postcomp_open B S hS P _ (Y.affineCover.f i) (hf i)

end RelativeMore

end AlgebraicGeometry

end
