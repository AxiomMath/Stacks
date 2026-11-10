module

public import Mathlib.CategoryTheory.Sites.RegularEpi
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.AlgebraicQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafGivesSpaceRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtalePostcomp
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleSubterminalSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleStructureSheaf

/-!
# A sheaf covered by a scheme chart is representable (the core of Stacks 0GF6)

Let `Y` be an algebraic space over `S` and let `G` be a sheaf of sets on the spaces-étale site of
`Y`. Stacks 0GF6 asserts that, provided a set-theoretic condition holds, `G` is represented by an
algebraic space étale over `Y`. The condition, as the source's proof uses it, is that some scheme
chart `V ⟶ Y` carries an epimorphism `h_V ⟶ G`. This file carries out the proof from there:

* the fibre product `h_V ×_G h_V ⊆ h_{V ×_Y V}` is represented by an open subspace `R` of
  `V ×_Y V`, by Stacks 04K8 applied to the subsheaf of `V ×_Y V` on which the two pullbacks of
  the section of `G` agree;
* `R ⇉ V` is an étale equivalence relation, being the kernel pair of `h_V ⟶ G`;
* the quotient `V / R` of Stacks 02WW is an algebraic space étale over `Y`, with `R` the kernel
  pair of `V ⟶ V / R` by Stacks 02WV;
* `h_V ⟶ G` and `h_V ⟶ h_{V / R}` are effective epimorphisms of sheaves with the same kernel
  pair, hence `G ≅ h_{V / R}`.

## Main results

* `AlgebraicGeometry.Space.exists_iso_yoneda_of_epi`: a sheaf on the
  spaces-étale site of `Y` covered by the representable sheaf of a scheme chart is isomorphic to
  the sheaf represented by an algebraic space étale over `Y`.

## Implementation notes

The relation `R` is first found as an object of the spaces-étale site of `Y` and is shown to be
an internal equivalence relation there, by reflecting the kernel pair of `h_V ⟶ G` along the
fully faithful Yoneda embedding into sheaves; only then is it moved to the representing schemes,
where Stacks 02WW needs it. In this way reflexivity, symmetry and transitivity are never checked
by hand. The Yoneda embedding into sheaves is available because the spaces-étale topology is
subcanonical, `AlgebraicGeometry.Space.SpacesEtale.subcanonical`.

## References

* [Stacks Project, Tag 0GF6](https://stacks.math.columbia.edu/tag/0GF6)
* [Stacks Project, Tag 04K8](https://stacks.math.columbia.edu/tag/04K8)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {Y : AlgebraicSpaces B S hS}

namespace SheafGivesSpace

variable {B S hS} {G : Sheaf (SpacesEtale.topology B S hS Y) (Type (u + 1))}
  {V : SpacesEtale B S hS Y}

variable (V) in
/-- The fibre product `V ×_Y V` of an object of the spaces-étale site of `Y` with itself, the
product in that site. -/
noncomputable abbrev pairObj : SpacesEtale B S hS Y :=
  pullback ((SpacesEtale.final_isTerminal B S hS Y).from V)
    ((SpacesEtale.final_isTerminal B S hS Y).from V)

variable (V) in
/-- Postcomposition with the structure morphism of `V ×_Y V`, from the spaces-étale site of
`V ×_Y V` to that of `Y`. -/
noncomputable abbrev pairPostcomp :
    SpacesEtale B S hS (pairObj V).1.left ⥤ SpacesEtale B S hS Y :=
  spacesEtalePostcomp B S hS (pairObj V).1.hom (pairObj V).property

variable (V) in
/-- An object étale over `V ×_Y V`, read in the spaces-étale site of `Y`, maps to `V ×_Y V`. -/
noncomputable def toPair (U : SpacesEtale B S hS (pairObj V).1.left) :
    (pairPostcomp V).obj U ⟶ pairObj V :=
  ObjectProperty.homMk (Over.homMk U.1.hom rfl)

/-- The maps `toPair` are natural in the object étale over `V ×_Y V`. -/
theorem pairPostcomp_map_toPair {U U' : SpacesEtale B S hS (pairObj V).1.left} (f : U ⟶ U') :
    (pairPostcomp V).map f ≫ toPair V U' = toPair V U :=
  ObjectProperty.hom_ext _ (Over.OverMorphism.ext (Over.w f.hom))

variable (s : G.obj.obj (op V))

/-- The subterminal subfunctor of the spaces-étale site of `V ×_Y V` on which the two pullbacks
of the section `s` of `G` agree. -/
noncomputable def agreeSubfunctor :
    Subfunctor (spacesEtaleTerminalSheaf B S hS (pairObj V).1.left) where
  obj U := {_x | G.obj.map (toPair V U.unop ≫ pullback.fst _ _).op s =
    G.obj.map (toPair V U.unop ≫ pullback.snd _ _).op s}
  map {U U'} f := by
    intro x hx
    change G.obj.map (toPair V U'.unop ≫ pullback.fst _ _).op s =
      G.obj.map (toPair V U'.unop ≫ pullback.snd _ _).op s
    have key : ∀ c : (pairPostcomp V).obj U.unop ⟶ V,
        G.obj.map ((pairPostcomp V).map f.unop ≫ c).op s =
          G.obj.map ((pairPostcomp V).map f.unop).op (G.obj.map c.op s) := fun c => by
      rw [op_comp, Functor.map_comp_apply]
    rw [← pairPostcomp_map_toPair f.unop, Category.assoc, Category.assoc, key, key]
    exact congrArg _ hx

/-- Restriction of a section of `G` along a composite is the iterated restriction. -/
private theorem map_comp_op_apply {P Q T : SpacesEtale B S hS Y} (f : P ⟶ Q) (c : Q ⟶ T)
    (t : G.obj.obj (op T)) :
    G.obj.map (f ≫ c).op t = G.obj.map f.op (G.obj.map c.op t) := by
  rw [op_comp, Functor.map_comp_apply]

/-- The two pullbacks of `s` to an object `W` étale over `V ×_Y V` are the restrictions along
`W ⟶ U` of their pullbacks to `U`. -/
theorem map_toPair_comp {U W : SpacesEtale B S hS (pairObj V).1.left} (g : W ⟶ U)
    (c : pairObj V ⟶ V) :
    G.obj.map ((pairPostcomp V).map g).op (G.obj.map (toPair V U ≫ c).op s) =
      G.obj.map (toPair V W ≫ c).op s := by
  rw [← map_comp_op_apply, ← Category.assoc, pairPostcomp_map_toPair]

/-- The subfunctor on which the two pullbacks of `s` agree is a sheaf: postcomposition with the
structure morphism of `V ×_Y V` is continuous, so `G` restricts to a sheaf on the spaces-étale
site of `V ×_Y V`, and that sheaf is separated. -/
theorem isSheaf_agreeSubfunctor :
    Presheaf.IsSheaf (SpacesEtale.topology B S hS (pairObj V).1.left)
      (agreeSubfunctor s).toFunctor := by
  rw [isSheaf_iff_isSheaf_of_type]
  intro U T hT x _
  have hsh := (pairPostcomp V).op_comp_isSheaf_of_types
    (SpacesEtale.topology B S hS (pairObj V).1.left) (SpacesEtale.topology B S hS Y) G
  have heq : G.obj.map (toPair V U ≫ pullback.fst _ _).op s =
      G.obj.map (toPair V U ≫ pullback.snd _ _).op s := by
    refine (hsh T hT).isSeparatedFor.ext (fun W g hg => ?_)
    change G.obj.map ((pairPostcomp V).map g).op _ = G.obj.map ((pairPostcomp V).map g).op _
    rw [map_toPair_comp, map_toPair_comp]
    exact (x g hg).property
  exact ⟨⟨PUnit.unit, heq⟩, fun _ _ _ => Subtype.ext rfl, fun _ _ => Subtype.ext rfl⟩

/-- **Stacks 04K8 applied to the agreement subfunctor**: the open subspace of `V ×_Y V` whose
étale neighbourhoods are exactly those on which the two pullbacks of `s` agree. -/
noncomputable def agreeOpen :
    {W : Subfunctor (pairObj V).1.left.1 // IsOpenSubspace B S hS W} :=
  (existsUnique_openSubspace_of_subterminalSheaf B S hS _ (agreeSubfunctor s)
    (isSheaf_agreeSubfunctor s)).exists.choose

/-- The agreement subfunctor is the subterminal sheaf of the open subspace `agreeOpen s`. -/
theorem agreeSubfunctor_eq :
    agreeSubfunctor s = openSubspaceSheaf B S hS _ (agreeOpen s) :=
  (existsUnique_openSubspace_of_subterminalSheaf B S hS _ (agreeSubfunctor s)
    (isSheaf_agreeSubfunctor s)).exists.choose_spec

variable {s} in
/-- An object `T` of the spaces-étale site of `Y` with a map `z` to `V ×_Y V`, read as an object
étale over `V ×_Y V`. -/
noncomputable def liftObj {T : SpacesEtale B S hS Y} (z : T ⟶ pairObj V) :
    SpacesEtale B S hS (pairObj V).1.left :=
  ⟨Over.mk z.hom.left, SpacesEtale.isEtale_toSpaces_map B S hS Y z⟩

/-- The object `T` is recovered from `liftObj z` by postcomposing with `V ×_Y V ⟶ Y`. -/
noncomputable def liftIso {T : SpacesEtale B S hS Y} (z : T ⟶ pairObj V) :
    T ≅ (pairPostcomp V).obj (liftObj z) where
  hom := ObjectProperty.homMk (Over.homMk (𝟙 T.1.left) (by
    change 𝟙 T.1.left ≫ z.hom.left ≫ (pairObj V).1.hom = T.1.hom
    rw [Category.id_comp]; exact Over.w z.hom))
  inv := ObjectProperty.homMk (Over.homMk (𝟙 T.1.left) (by
    change 𝟙 T.1.left ≫ T.1.hom = z.hom.left ≫ (pairObj V).1.hom
    rw [Category.id_comp]; exact (Over.w z.hom).symm))
  hom_inv_id := ObjectProperty.hom_ext _ (Over.OverMorphism.ext (Category.id_comp _))
  inv_hom_id := ObjectProperty.hom_ext _ (Over.OverMorphism.ext (Category.id_comp _))

/-- The identification `liftIso z` carries `toPair` to `z`. -/
theorem liftIso_hom_toPair {T : SpacesEtale B S hS Y} (z : T ⟶ pairObj V) :
    (liftIso z).hom ≫ toPair V (liftObj z) = z :=
  ObjectProperty.hom_ext _ (Over.OverMorphism.ext (by
    change 𝟙 _ ≫ z.hom.left = z.hom.left
    exact Category.id_comp _))

/-- The two pullbacks of `s` agree along `z : T ⟶ V ×_Y V` exactly when the underlying morphism
of `z` factors through the open subspace `agreeOpen s`. -/
theorem map_eq_iff_factors {T : SpacesEtale B S hS Y} (z : T ⟶ pairObj V) :
    G.obj.map (z ≫ pullback.fst _ _).op s = G.obj.map (z ≫ pullback.snd _ _).op s ↔
      ∃ g : T.1.left.1 ⟶ (agreeOpen s).1.toFunctor, g ≫ (agreeOpen s).1.ι = z.hom.left.hom := by
  have hmem : PUnit.unit ∈ (agreeSubfunctor s).obj (op (liftObj z)) ↔
      PUnit.unit ∈ (openSubspaceSheaf B S hS _ (agreeOpen s)).obj (op (liftObj z)) := by
    rw [agreeSubfunctor_eq]
  refine Iff.trans ?_ hmem
  change _ ↔ G.obj.map (toPair V (liftObj z) ≫ pullback.fst _ _).op s =
    G.obj.map (toPair V (liftObj z) ≫ pullback.snd _ _).op s
  have hz : ∀ c : pairObj V ⟶ V, G.obj.map (z ≫ c).op s =
      G.obj.map (liftIso z).hom.op (G.obj.map (toPair V (liftObj z) ≫ c).op s) := fun c => by
    rw [← map_comp_op_apply, ← Category.assoc, liftIso_hom_toPair]
  rw [hz, hz]
  exact (G.obj.mapIso (liftIso z).op).toEquiv.injective.eq_iff

/-- The relation object `R ⊆ V ×_Y V` of the proof of Stacks 0GF6: the open subspace on which
the two pullbacks of `s` agree, as an object of the spaces-étale site of `Y`. -/
noncomputable abbrev relObj : SpacesEtale B S hS Y :=
  (pairPostcomp V).obj (openSubspaceObject B S hS _ (agreeOpen s))

/-- The inclusion of the relation object into `V ×_Y V`. -/
noncomputable abbrev relι : relObj s ⟶ pairObj V :=
  toPair V (openSubspaceObject B S hS _ (agreeOpen s))

/-- The two pullbacks of `s` agree along `z : T ⟶ V ×_Y V` exactly when `z` factors through
the relation object. -/
theorem map_eq_iff_exists_lift {T : SpacesEtale B S hS Y} (z : T ⟶ pairObj V) :
    G.obj.map (z ≫ pullback.fst _ _).op s = G.obj.map (z ≫ pullback.snd _ _).op s ↔
      ∃ r : T ⟶ relObj s, r ≫ relι s = z := by
  rw [map_eq_iff_factors]
  constructor
  · rintro ⟨g, hg⟩
    have hw : (ObjectProperty.homMk g : T.1.left ⟶ (relObj s).1.left) ≫ (relObj s).1.hom =
        T.1.hom := by
      refine ObjectProperty.hom_ext _ ?_
      change g ≫ (agreeOpen s).1.ι ≫ (pairObj V).1.hom.hom = T.1.hom.hom
      rw [← Category.assoc, hg]
      exact congrArg (fun k => k.hom) (Over.w z.hom)
    refine ⟨ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk g) hw), ?_⟩
    exact ObjectProperty.hom_ext _ (Over.OverMorphism.ext (ObjectProperty.hom_ext _ hg))
  · rintro ⟨r, rfl⟩
    exact ⟨r.hom.left.hom, rfl⟩

/-- The relation object is a subobject of `V ×_Y V`. -/
instance mono_relι : Mono (relι s) where
  right_cancellation r₁ r₂ h := by
    refine ObjectProperty.hom_ext _ (Over.OverMorphism.ext (ObjectProperty.hom_ext _ ?_))
    exact (cancel_mono (agreeOpen s).1.ι).1 (congrArg (fun k => k.hom.left.hom) h)

/-- **The fibre product `h_V ×_G h_V` is represented by the relation object.** For the map
`h_V ⟶ G` given by the section `s`, the square
`h_R ⇉ h_V ⟶ G` formed by the two composites `R ⟶ V ×_Y V ⇉ V` is cartesian in the category of
sheaves on the spaces-étale site of `Y`. -/
theorem isPullback_relObj :
    IsPullback ((SpacesEtale.topology B S hS Y).yoneda.map (relι s ≫ pullback.fst _ _))
      ((SpacesEtale.topology B S hS Y).yoneda.map (relι s ≫ pullback.snd _ _))
      ((SpacesEtale.topology B S hS Y).yonedaEquiv.symm s)
      ((SpacesEtale.topology B S hS Y).yonedaEquiv.symm s) := by
  have hpre : IsPullback (yoneda.map (relι s ≫ pullback.fst _ _))
      (yoneda.map (relι s ≫ pullback.snd _ _))
      ((SpacesEtale.topology B S hS Y).yonedaEquiv.symm s).hom
      ((SpacesEtale.topology B S hS Y).yonedaEquiv.symm s).hom := by
    refine IsPullback.of_forall_isPullback_app fun T => ?_
    rw [Types.isPullback_iff]
    refine ⟨?_, ?_, ?_⟩
    · ext r
      simpa [Category.assoc] using (map_eq_iff_exists_lift s (r ≫ relι s)).2 ⟨r, rfl⟩
    · rintro r₁ r₂ ⟨h₁, h₂⟩
      change r₁ ≫ relι s ≫ pullback.fst _ _ = r₂ ≫ relι s ≫ pullback.fst _ _ at h₁
      change r₁ ≫ relι s ≫ pullback.snd _ _ = r₂ ≫ relι s ≫ pullback.snd _ _ at h₂
      rw [← Category.assoc, ← Category.assoc] at h₁ h₂
      exact (cancel_mono (relι s)).1 (pullback.hom_ext h₁ h₂)
    · intro x y hxy
      change G.obj.map x.op s = G.obj.map y.op s at hxy
      let z : T.unop ⟶ pairObj V := pullback.lift x y
        ((SpacesEtale.final_isTerminal B S hS Y).hom_ext _ _)
      obtain ⟨r, hr⟩ := (map_eq_iff_exists_lift s z).1 (by
        simpa only [z, pullback.lift_fst, pullback.lift_snd] using hxy)
      refine ⟨r, ?_, ?_⟩
      · change r ≫ relι s ≫ pullback.fst _ _ = x
        rw [← Category.assoc, hr, pullback.lift_fst]
      · change r ≫ relι s ≫ pullback.snd _ _ = y
        rw [← Category.assoc, hr, pullback.lift_snd]
  exact IsPullback.of_map (sheafToPresheaf _ _) (Sheaf.hom_ext hpre.w) hpre

/-- The two projections of the relation object form an internal equivalence relation in the
spaces-étale site of `Y`: their images under the Yoneda embedding into sheaves form the kernel
pair of `h_V ⟶ G`, and the Yoneda embedding is fully faithful. -/
theorem isEquivalenceRelation_relObj :
    IsEquivalenceRelation (relι s ≫ pullback.fst _ _) (relι s ≫ pullback.snd _ _) := by
  let J := SpacesEtale.topology B S hS Y
  have e := IsKernelPair.equivalenceRelation (J.yonedaEquiv.symm s)
    (J.yoneda.map (relι s ≫ pullback.fst _ _)) (J.yoneda.map (relι s ≫ pullback.snd _ _))
    (pullbackIsPullback _ _) (isPullback_relObj s)
  exact isEquivalenceRelation_of_map J.yoneda _ _ e.isEquivalenceRelation

/-- The underlying morphism of the map from an object of the spaces-étale site to its final
object is the structure morphism. -/
theorem toSpaces_map_from_final (W : SpacesEtale B S hS Y) :
    (SpacesEtale.toSpaces B S hS Y).map ((SpacesEtale.final_isTerminal B S hS Y).from W) =
      W.1.hom :=
  (Category.comp_id _).symm.trans (Over.w ((SpacesEtale.final_isTerminal B S hS Y).from W).hom)

variable (V) in
/-- The underlying algebraic space of `V ×_Y V` is the fibre product of presheaves. -/
theorem isPullback_pairObj :
    IsPullback ((SpacesEtale.toSpaces B S hS Y).map (pullback.fst
        ((SpacesEtale.final_isTerminal B S hS Y).from V)
        ((SpacesEtale.final_isTerminal B S hS Y).from V))).hom
      ((SpacesEtale.toSpaces B S hS Y).map (pullback.snd
        ((SpacesEtale.final_isTerminal B S hS Y).from V)
        ((SpacesEtale.final_isTerminal B S hS Y).from V))).hom
      V.1.hom.hom V.1.hom.hom := by
  have h := AlgebraicSpaces.isPullback_hom B S hS
    ((IsPullback.of_hasPullback ((SpacesEtale.final_isTerminal B S hS Y).from V)
      ((SpacesEtale.final_isTerminal B S hS Y).from V)).map (SpacesEtale.toSpaces B S hS Y))
  rwa [toSpaces_map_from_final] at h

/-- The underlying morphisms of presheaves of the two projections of the relation object form
an internal equivalence relation of presheaves on the big fppf site of `S`. -/
theorem isEquivalenceRelation_relObj_hom :
    IsEquivalenceRelation ((SpacesEtale.toSpaces B S hS Y).map (relι s ≫ pullback.fst _ _)).hom
      ((SpacesEtale.toSpaces B S hS Y).map (relι s ≫ pullback.snd _ _)).hom := by
  let Φ := SpacesEtale.toSpaces B S hS Y ⋙ (algebraicSpaceProperty B S hS).ι
  obtain ⟨e⟩ := (isEquivalenceRelation_relObj s).nonempty_equivalenceRelation
  have hι : Φ.map (relι s) = (agreeOpen s).1.ι := rfl
  have : JointlyMono₂ (Φ.map (relι s ≫ pullback.fst _ _)) (Φ.map (relι s ≫ pullback.snd _ _)) :=
    ⟨fun T a b h₁ h₂ => by
      rw [Functor.map_comp, ← Category.assoc, ← Category.assoc] at h₁ h₂
      have h := (isPullback_pairObj V).hom_ext h₁ h₂
      rw [hι] at h
      have := mono_of_isOpenImmersion B S hS _ (agreeOpen s).2.2
      exact (cancel_mono (agreeOpen s).1.ι).1 h⟩
  exact EquivalenceRelation.isEquivalenceRelation
    { __ := e.toReflexiveRelation.map Φ
      __ := e.toSymmetricRelation.map Φ
      __ := e.toTransitiveRelation.map Φ }

section Chart

variable (V₀ : SmallEtale B S hS Y.1)

/-- For a scheme chart `V₀` of `Y`, the fibre product `V₀ ×_Y V₀` is represented by the chosen
representing object of the base change of the chart along itself. -/
noncomputable def pairIso :
    (pairObj ((comparisonFunctor B S hS Y).obj V₀)).1.left.obj ≅
      yoneda.obj (V₀.2.rep.pullback V₀.1.hom) :=
  (isPullback_pairObj _).isoIsPullback _ _ (V₀.2.rep.isPullback V₀.1.hom)

variable {V₀} (s : G.obj.obj (op ((comparisonFunctor B S hS Y).obj V₀)))

/-- The scheme representing the relation object: an open subspace of the representable
`V₀ ×_Y V₀` is representable. -/
noncomputable def relRep : BigFppfOver B S hS :=
  (agreeOpen s).2.2.rep.pullback (pairIso V₀).inv

/-- The relation object is represented by `relRep s`. -/
noncomputable def relIso : (agreeOpen s).1.toFunctor ≅ yoneda.obj (relRep s) :=
  haveI := ((agreeOpen s).2.2.rep.isPullback (pairIso V₀).inv).isIso_fst_of_isIso
  (asIso ((agreeOpen s).2.2.rep.fst (pairIso V₀).inv)).symm

/-- The target map `R ⟶ V₀` of the relation, on representing schemes. -/
noncomputable def relTarget : relRep s ⟶ (SmallEtale.toOver B S hS Y.1).obj V₀ :=
  yoneda.preimage ((relIso s).inv ≫
    ((SpacesEtale.toSpaces B S hS Y).map (relι s ≫ pullback.fst _ _)).hom)

/-- The source map `R ⟶ V₀` of the relation, on representing schemes. -/
noncomputable def relSource : relRep s ⟶ (SmallEtale.toOver B S hS Y.1).obj V₀ :=
  yoneda.preimage ((relIso s).inv ≫
    ((SpacesEtale.toSpaces B S hS Y).map (relι s ≫ pullback.snd _ _)).hom)

/-- The target map, read on represented presheaves. -/
theorem yoneda_map_relTarget : yoneda.map (relTarget s) = (relIso s).inv ≫
    ((SpacesEtale.toSpaces B S hS Y).map (relι s ≫ pullback.fst _ _)).hom :=
  yoneda.map_preimage _

/-- The source map, read on represented presheaves. -/
theorem yoneda_map_relSource : yoneda.map (relSource s) = (relIso s).inv ≫
    ((SpacesEtale.toSpaces B S hS Y).map (relι s ≫ pullback.snd _ _)).hom :=
  yoneda.map_preimage _

/-- The target map is the first projection of the relation object, through `relIso s`. -/
theorem relIso_hom_yoneda_map_relTarget : (relIso s).hom ≫ yoneda.map (relTarget s) =
    (show (agreeOpen s).1.toFunctor ⟶ _ from
      ((SpacesEtale.toSpaces B S hS Y).map (relι s ≫ pullback.fst _ _)).hom) := by
  rw [yoneda_map_relTarget]
  exact Iso.hom_inv_id_assoc _ _

/-- The source map is the second projection of the relation object, through `relIso s`. -/
theorem relIso_hom_yoneda_map_relSource : (relIso s).hom ≫ yoneda.map (relSource s) =
    (show (agreeOpen s).1.toFunctor ⟶ _ from
      ((SpacesEtale.toSpaces B S hS Y).map (relι s ≫ pullback.snd _ _)).hom) := by
  rw [yoneda_map_relSource]
  exact Iso.hom_inv_id_assoc _ _

/-- The relation is an étale equivalence relation on the scheme underlying `V₀`. -/
theorem isEtaleEquivalenceRelation_rel :
    Stacks.Groupoids.IsEtaleEquivalenceRelation
      (relation B S hS (relSource s) (relTarget s)) := by
  have hetale : ∀ c : relObj s ⟶ (comparisonFunctor B S hS Y).obj V₀,
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) (yoneda.preimage ((relIso s).inv ≫
          ((SpacesEtale.toSpaces B S hS Y).map c).hom)) := fun c => by
    refine (presheaf_yoneda_map_etale_iff B S hS _).1 ?_
    rw [yoneda.map_preimage]
    exact (isEtale_iff_presheaf_of_yoneda B S hS _).1
      (isEtale_comp B S hS (isEtale_of_isIso B S hS _)
        (SpacesEtale.isEtale_toSpaces_map B S hS Y c))
  refine isEtaleEquivalenceRelation_of_embedding B S hS (relSource s) (relTarget s) yoneda
    (relIso s) ?_ (hetale _) (hetale _)
  rw [relIso_hom_yoneda_map_relTarget, relIso_hom_yoneda_map_relSource]
  exact isEquivalenceRelation_relObj_hom s

/-- The quotient sheaf `V₀ / R` of Stacks 02WW. -/
noncomputable abbrev quot : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  (Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion)
    (relation B S hS (relSource s) (relTarget s))).obj

/-- **Stacks 02WW.** The quotient `V₀ / R` is an algebraic space. -/
theorem isAlgebraicSpace_quot : IsAlgebraicSpace B S hS (quot s) :=
  have := isEtaleEquivalenceRelation_rel s
  isAlgebraicSpace_quotient_unconditional B S hS (relSource s) (relTarget s)

/-- The chart `V₀ ⟶ V₀ / R` factors the chart `V₀ ⟶ Y`: the latter identifies the two maps
`R ⇉ V₀`, and `V₀ ⟶ V₀ / R` is the coequalizer of its kernel pair by Stacks 0262. -/
theorem exists_quot_desc :
    ∃ δ : quot s ⟶ Y.1, quotientMap B S hS (relSource s) (relTarget s) ≫ δ = V₀.1.hom := by
  have := isEtaleEquivalenceRelation_rel s
  obtain ⟨hRsh, hUsh, ⟨hc⟩⟩ := isCoequalizer_of_surjectiveEtale B S hS
    (quotientMap B S hS (relSource s) (relTarget s)) (relTarget s) (relSource s)
    (quotientMap_isPullback B S hS (relSource s) (relTarget s)) (isAlgebraicSpace_quot s)
    (quotientMap_surjective_unconditional B S hS (relSource s) (relTarget s))
    (quotientMap_etale_unconditional B S hS (relSource s) (relTarget s))
  have hk : yoneda.map (relTarget s) ≫ V₀.1.hom = yoneda.map (relSource s) ≫ V₀.1.hom := by
    have : Epi (relIso s).hom := IsIso.epi_of_iso _
    rw [← cancel_epi (relIso s).hom, ← Category.assoc, ← Category.assoc,
      relIso_hom_yoneda_map_relTarget, relIso_hom_yoneda_map_relSource]
    simp only [Functor.map_comp]
    exact congrArg (_ ≫ ·) (isPullback_pairObj ((comparisonFunctor B S hS Y).obj V₀)).w
  let k : (⟨yoneda.obj ((SmallEtale.toOver B S hS Y.1).obj V₀), hUsh⟩ :
      Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶ ⟨Y.1, Y.2.isSheaf⟩ := ⟨V₀.1.hom⟩
  refine ⟨(Cofork.IsColimit.desc hc k (Sheaf.hom_ext hk)).hom, ?_⟩
  have h := Cofork.IsColimit.π_desc' hc k (Sheaf.hom_ext hk)
  exact congrArg (fun f : _ ⟶ (⟨Y.1, Y.2.isSheaf⟩ :
    Sheaf (BigFppfOver.topology B S hS) (Type u)) => f.hom) h

/-- The map `V₀ / R ⟶ Y` induced by the chart `V₀ ⟶ Y`. -/
noncomputable def quotDesc : quot s ⟶ Y.1 := (exists_quot_desc s).choose

/-- The map `V₀ / R ⟶ Y` restricts to the chart `V₀ ⟶ Y`. -/
theorem quotientMap_quotDesc :
    quotientMap B S hS (relSource s) (relTarget s) ≫ quotDesc s = V₀.1.hom :=
  (exists_quot_desc s).choose_spec

/-- The map `V₀ / R ⟶ Y` is étale, by Stacks 03FS: its composite with the surjective étale
chart `V₀ ⟶ V₀ / R` of Stacks 02WW is the étale chart `V₀ ⟶ Y`. -/
theorem isEtale_quotDesc : IsEtale B S hS (quotDesc s) := by
  have := isEtaleEquivalenceRelation_rel s
  refine (isEtale_iff_exists_source_chart B S hS (isAlgebraicSpace_quot s) Y.2 _).2
    ⟨_, quotientMap B S hS (relSource s) (relTarget s),
      quotientMap_surjective_unconditional B S hS (relSource s) (relTarget s),
      quotientMap_etale_unconditional B S hS (relSource s) (relTarget s), ?_⟩
  rw [quotientMap_quotDesc]
  exact (isEtale_iff_presheaf_of_yoneda B S hS _).2 V₀.2

/-- The quotient `V₀ / R`, as an algebraic space étale over `Y`. -/
noncomputable def quotObj : SpacesEtale B S hS Y :=
  ⟨Over.mk (ObjectProperty.homMk (quotDesc s) :
    (⟨quot s, isAlgebraicSpace_quot s⟩ : AlgebraicSpaces B S hS) ⟶ Y), isEtale_quotDesc s⟩

/-- The quotient map `V₀ ⟶ V₀ / R`, as a morphism of the spaces-étale site of `Y`. -/
noncomputable def quotProj : (comparisonFunctor B S hS Y).obj V₀ ⟶ quotObj s :=
  ObjectProperty.homMk (Over.homMk
    (ObjectProperty.homMk (quotientMap B S hS (relSource s) (relTarget s)))
    (ObjectProperty.hom_ext _ (quotientMap_quotDesc s)))

/-- The relation object is the fibre product `V₀ ×_{V₀ / R} V₀` in the spaces-étale site of
`Y`, by Stacks 02WV. -/
theorem isPullback_quotProj :
    IsPullback (relι s ≫ pullback.fst _ _) (relι s ≫ pullback.snd _ _)
      (quotProj s) (quotProj s) := by
  have := isEtaleEquivalenceRelation_rel s
  let Φ := SpacesEtale.toSpaces B S hS Y ⋙ (algebraicSpaceProperty B S hS).ι
  have h := (quotientMap_isPullback B S hS (relSource s) (relTarget s)).of_iso
    (relIso s).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (fst' := Φ.map (relι s ≫ pullback.fst _ _)) (snd' := Φ.map (relι s ≫ pullback.snd _ _))
    (f' := Φ.map (quotProj s)) (g' := Φ.map (quotProj s))
    ((Category.comp_id _).trans (yoneda_map_relTarget s))
    ((Category.comp_id _).trans (yoneda_map_relSource s))
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
  refine IsPullback.of_map Φ (Φ.map_injective ?_) h
  rw [Functor.map_comp, Functor.map_comp]
  exact h.w

/-- The quotient map `V₀ ⟶ V₀ / R` alone covers `V₀ / R` in the spaces-étale site of `Y`. -/
theorem ofArrows_quotProj_mem :
    Sieve.ofArrows (fun _ : PUnit.{u + 2} => (comparisonFunctor B S hS Y).obj V₀)
      (fun _ => quotProj s) ∈ SpacesEtale.topology B S hS Y (quotObj s) := by
  have := isEtaleEquivalenceRelation_rel s
  refine Precoverage.generate_mem_toGrothendieck ⟨⟨PUnit.{u + 2}, _, fun _ => quotProj s⟩,
    rfl, fun x => ?_⟩
  obtain ⟨y, hy⟩ := (surjective_iff_surjective_pointsMap B S hS (quot s)
    (isAlgebraicSpace_quot s) _ _).1
    (quotientMap_surjective_unconditional B S hS (relSource s) (relTarget s)) x
  exact ⟨PUnit.unit, y, hy⟩

/-- The map of representable sheaves induced by the quotient map `V₀ ⟶ V₀ / R` is an
epimorphism: the quotient map covers `V₀ / R`. -/
instance epi_yoneda_map_quotProj :
    Epi ((SpacesEtale.topology B S hS Y).yoneda.map (quotProj s)) := by
  let J := SpacesEtale.topology B S hS Y
  have : Sheaf.IsLocallySurjective (J.yoneda.map (quotProj s)) := ⟨fun {U} x => by
    refine J.superset_covering ?_ (J.pullback_stable x (ofArrows_quotProj_mem s))
    rintro V g ⟨W, a, b, ⟨_⟩, hab⟩
    exact ⟨a, hab⟩⟩
  infer_instance

/-- Two effective epimorphisms with the same kernel pair have isomorphic targets. -/
private theorem nonempty_iso_of_isPullback {C : Type*} [Category C] [IsRegularEpiCategory C]
    {P X Z Z' : C} {a b : P ⟶ X} {f : X ⟶ Z} {f' : X ⟶ Z'} [Epi f] [Epi f']
    (h : IsPullback a b f f) (h' : IsPullback a b f' f') : Nonempty (Z ≅ Z') := by
  have := IsRegularEpiCategory.regularEpiOfEpi f
  have := IsRegularEpiCategory.regularEpiOfEpi f'
  exact ⟨(isColimitCoforkOfEffectiveEpi f _ h.isLimit).coconePointUniqueUpToIso
    (isColimitCoforkOfEffectiveEpi f' _ h'.isLimit)⟩

/-- **The sheaf is represented by the quotient**: if the section `s` of `G` over the scheme chart
`V₀` induces an epimorphism `h_{V₀} ⟶ G`, then `G` is isomorphic to the sheaf represented by
the algebraic space `V₀ / R` étale over `Y`. Both `h_{V₀} ⟶ G` and `h_{V₀} ⟶ h_{V₀ / R}` are
effective epimorphisms with the same kernel pair `h_R`, by `isPullback_relObj` and Stacks 02WV,
so they are coequalizers of the same pair. -/
theorem nonempty_iso_quotObj [Epi ((SpacesEtale.topology B S hS Y).yonedaEquiv.symm s)] :
    Nonempty (G ≅ (SpacesEtale.topology B S hS Y).yoneda.obj (quotObj s)) := by
  exact nonempty_iso_of_isPullback (isPullback_relObj s)
    ((isPullback_quotProj s).map (SpacesEtale.topology B S hS Y).yoneda)

end Chart

end SheafGivesSpace

/-- **Core of Stacks 0GF6.** Let `G` be a sheaf of sets on the spaces-étale site of `Y` which
receives an epimorphism from the sheaf represented by a scheme chart `V` of `Y` (the
set-theoretic condition of Stacks 0GF6). Then `G` is isomorphic to the sheaf represented by an
algebraic space étale over `Y`, namely the quotient `V / R` of Stacks 02WW by the étale
equivalence relation `R = h_V ×_G h_V`. -/
theorem exists_iso_yoneda_of_epi (G : Sheaf (SpacesEtale.topology B S hS Y) (Type (u + 1)))
    (V : SmallEtale B S hS Y.1)
    (e : (presheafToSheaf (SpacesEtale.topology B S hS Y) (Type (u + 1))).obj
      (yoneda.obj ((comparisonFunctor B S hS Y).obj V)) ⟶ G) [Epi e] :
    ∃ W : SpacesEtale B S hS Y,
      Nonempty (G ≅ (presheafToSheaf (SpacesEtale.topology B S hS Y) (Type (u + 1))).obj
        (yoneda.obj W)) := by
  let J := SpacesEtale.topology B S hS Y
  let s := J.yonedaEquiv
    ((sheafificationIso (J.yoneda.obj ((comparisonFunctor B S hS Y).obj V))).hom ≫ e)
  have : Epi (J.yonedaEquiv.symm s) := by
    simp only [s, Equiv.symm_apply_apply]
    infer_instance
  obtain ⟨i⟩ := SheafGivesSpace.nonempty_iso_quotObj s
  exact ⟨SheafGivesSpace.quotObj s,
    ⟨i ≪≫ sheafificationIso (J.yoneda.obj (SheafGivesSpace.quotObj s))⟩⟩

end AlgebraicGeometry.Space

end
