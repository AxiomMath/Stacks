module

public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import StacksFrontier.AlgebraicGeometry.Descent.MorphismPropertyTopology.FppfLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Descent.SeparatedQuasiFiniteSchemeDescent

/-!
# Gluing local representatives by immersions

Let `P` be a property of schemes over a base `B` which is stable under pulling back along
morphisms over `B` and which descends along the base changes of a fixed fppf covering family
`{q i : U i ⟶ B}`. If over each `U i` the property is represented by an immersion
`W i ⟶ U i` — a scheme over `U i` has the property, viewed over `B`, exactly when it factors
through `W i` — then the property is represented by an immersion `Z ⟶ B`.

This is the descent step shared by the representability theorems of the flatness chapter. The
local representatives carry a descent datum whose comparison isomorphisms are forced by
subterminality, the datum is effective because an immersion is separated and locally
quasi-finite (Stacks 02W8), the glued morphism is an immersion because being one is fppf local
on the base (Stacks 02YM), and it represents `P` because both `P` and the functor of points of
the glued scheme are sheaves for the covering, the latter by subcanonicality of the fpqc
topology. In the language of Stacks 02W5 this is the equivalence between sheaves which are
representable over every member of a covering and descent data of schemes, read off at
subterminal sheaves.

## Main results

* `Stacks.Flatness.exists_immersion_of_localRepresentatives`: the statement above, for objects
  of `Over B`.
* `Stacks.Flatness.exists_immersion_of_openCover`: the same along an open cover of `B`, for a
  property of morphisms into `B`, with local representatives given as immersions into `B`
  whose image lies in the member of the cover.

## References

* [Stacks Project, Tag 02W5](https://stacks.math.columbia.edu/tag/02W5)
* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
* [Stacks Project, Tag 02YM](https://stacks.math.columbia.edu/tag/02YM)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Flatness

/-- Morphisms over the base into an object whose structure morphism is a monomorphism form a
subsingleton. -/
theorem subsingleton_overHom_of_mono {S : Scheme.{u}} (T W : Over S) [Mono W.hom] :
    Subsingleton (T ⟶ W) :=
  ⟨fun a b ↦ Over.OverMorphism.ext ((cancel_mono W.hom).mp ((Over.w a).trans (Over.w b).symm))⟩

/-- The structure map of a local representative is a monomorphism when the representative's own
structure morphism is. -/
theorem mono_structureMap {S U' : Scheme.{u}} (q' : U' ⟶ S) (W' : Over U')
    [Mono W'.hom] : Mono (AlgebraicGeometry.structureMap q' W') :=
  (Over.forget S).mono_of_mono_map (inferInstanceAs (Mono W'.hom))

section LocalRepresentatives

variable {B : Scheme.{u}} (P : Over B → Prop) (hP : ∀ {T T' : Over B}, (T' ⟶ T) → P T → P T')

include hP in
/-- A scheme over the base with the property and mapping to a member of the family lifts, over
the base, to the local representative there. -/
theorem exists_lift_of_localRepresentative'
    {U : Scheme.{u}} (q : U ⟶ B) (W : Over U)
    (h : ∀ V : Over U, P ((Over.map q).obj V) ↔ Nonempty (V ⟶ W))
    {T : Over B} (a : T ⟶ Over.mk q) (hT : P T) :
    ∃ b : T ⟶ (Over.map q).obj W, b ≫ AlgebraicGeometry.structureMap q W = a := by
  let V := Over.mk a.left
  let e : (Over.map q).obj V ≅ T := Over.isoMk (Iso.refl _) (by simpa [V] using (Over.w a).symm)
  obtain ⟨b⟩ := (h V).mp (hP e.hom hT)
  refine ⟨Over.homMk b.left ?_, Over.OverMorphism.ext (Over.w b)⟩
  change b.left ≫ W.hom ≫ q = T.hom
  rw [← Category.assoc, Over.w b]
  exact Over.w a

variable {U V : Scheme.{u}} (q : U ⟶ B) (r : V ⟶ B) (W : Over U) (Z : Over V)

/-- The comparison morphism between two local representatives over the pairwise fibre product. -/
noncomputable def localRepresentativeTransition'
    (hW : P ((Over.map q).obj W))
    (hZ : ∀ T : Over V, P ((Over.map r).obj T) ↔ Nonempty (T ⟶ Z)) :
    (Over.map q).obj W ⨯ Over.mk r ⟶ Over.mk q ⨯ (Over.map r).obj Z :=
  prod.lift (prod.fst ≫ AlgebraicGeometry.structureMap q W)
    (Classical.choose (exists_lift_of_localRepresentative' P hP r Z hZ prod.snd
      (hP prod.fst hW)))

/-- The first component of the comparison morphism is the first projection followed by the
structure morphism of the local representative over `U`. -/
theorem localRepresentativeTransition'_fst
    (hW : P ((Over.map q).obj W))
    (hZ : ∀ T : Over V, P ((Over.map r).obj T) ↔ Nonempty (T ⟶ Z)) :
    localRepresentativeTransition' P hP q r W Z hW hZ ≫ prod.fst =
      prod.fst ≫ AlgebraicGeometry.structureMap q W := by
  simp [localRepresentativeTransition']

/-- The second component of the comparison morphism, followed by the structure morphism of the
local representative over `V`, is the second projection. -/
theorem localRepresentativeTransition'_snd
    (hW : P ((Over.map q).obj W))
    (hZ : ∀ T : Over V, P ((Over.map r).obj T) ↔ Nonempty (T ⟶ Z)) :
    localRepresentativeTransition' P hP q r W Z hW hZ ≫ prod.snd ≫
      AlgebraicGeometry.structureMap r Z = prod.snd := by
  simpa [localRepresentativeTransition'] using
    Classical.choose_spec (exists_lift_of_localRepresentative' P hP r Z hZ
      (prod.snd : (Over.map q).obj W ⨯ Over.mk r ⟶ Over.mk r) (hP prod.fst hW))

attribute [local simp] localRepresentativeTransition'_fst localRepresentativeTransition'_snd

attribute [local instance] mono_structureMap

/-- The comparison morphism of two local representatives is an isomorphism. -/
noncomputable def localRepresentativeTransitionIso' [Mono W.hom] [Mono Z.hom]
    (hW : ∀ T : Over U, P ((Over.map q).obj T) ↔ Nonempty (T ⟶ W))
    (hZ : ∀ T : Over V, P ((Over.map r).obj T) ↔ Nonempty (T ⟶ Z)) :
    (Over.map q).obj W ⨯ Over.mk r ≅ Over.mk q ⨯ (Over.map r).obj Z where
  hom := localRepresentativeTransition' P hP q r W Z ((hW W).mpr ⟨𝟙 W⟩) hZ
  inv := (prod.braiding _ _).hom ≫
    localRepresentativeTransition' P hP r q Z W ((hZ Z).mpr ⟨𝟙 Z⟩) hW ≫
      (prod.braiding _ _).hom
  hom_inv_id := by
    refine prod.hom_ext ?_ ?_
    · refine (cancel_mono (AlgebraicGeometry.structureMap q W)).mp ?_
      simp
    · simp
  inv_hom_id := by
    refine prod.hom_ext ?_ ?_
    · simp
    · refine (cancel_mono (AlgebraicGeometry.structureMap r Z)).mp ?_
      simp

end LocalRepresentatives

section Family

variable {B : Scheme.{u}} (P : Over B → Prop) (hP : ∀ {T T' : Over B}, (T' ⟶ T) → P T → P T')
  {I : Type u} {U : I → Scheme.{u}} (q : ∀ i, U i ⟶ B) (W : ∀ i, Over (U i))

attribute [local simp] localRepresentativeTransition'_fst localRepresentativeTransition'_snd

attribute [local instance] mono_structureMap

/-- The local representatives form a descent datum. -/
noncomputable def localRepresentativeDescentData' [∀ i, Mono (W i).hom]
    (h : ∀ i, ∀ T : Over (U i), P ((Over.map (q i)).obj T) ↔ Nonempty (T ⟶ W i)) :
    AlgebraicGeometry.DescentData q where
  obj := W
  gluing i j := Over.isoMk
    (localRepresentativeTransitionIso' P hP (q i) (q j) (W i) (W j) (h i) (h j)) (by
      refine prod.hom_ext ?_ ?_ <;>
        simp [localRepresentativeTransitionIso'])
  cocycle i j k := by
    change prod.map (localRepresentativeTransition' P hP (q i) (q j) (W i) (W j)
      ((h i (W i)).mpr ⟨𝟙 _⟩) (h j)) (𝟙 _) ≫
      prodMapLastTwo (localRepresentativeTransition' P hP (q j) (q k) (W j) (W k)
        ((h j (W j)).mpr ⟨𝟙 _⟩) (h k)) =
      prodMapFirstThird (localRepresentativeTransition' P hP (q i) (q k) (W i) (W k)
        ((h i (W i)).mpr ⟨𝟙 _⟩) (h k))
    refine prod.hom_ext (prod.hom_ext ?_ ?_) ?_
    · simp [prodMapLastTwo, prodMapFirstThird]
    · simp [prodMapLastTwo, prodMapFirstThird]
    · refine (cancel_mono (AlgebraicGeometry.structureMap (q k) (W k))).mp ?_
      simp [prodMapLastTwo, prodMapFirstThird]

include hP in
/-- **Local representatives by immersions glue** (Stacks 02W8 and 02YM). -/
theorem exists_isImmersion_of_localRepresentatives
    (hq : Presieve.ofArrows U q ∈ Scheme.fppfPrecoverage B) [∀ i, IsImmersion (W i).hom]
    (h : ∀ i, ∀ T : Over (U i), P ((Over.map (q i)).obj T) ↔ Nonempty (T ⟶ W i)) :
    ∃ Z : Over B, IsImmersion Z.hom ∧
      ∀ i, Nonempty ((Over.pullback (q i)).obj Z ≅ W i) := by
  let d := localRepresentativeDescentData' P hP q W h
  obtain ⟨Z, ⟨e⟩⟩ :=
    AlgebraicGeometry.DescentData.isFamilyEffective_of_forall_isSeparated_of_locallyQuasiFinite
      q hq d (fun i ↦ inferInstanceAs (IsSeparated (W i).hom))
      (fun i ↦ inferInstanceAs (LocallyQuasiFinite (W i).hom))
      (fun i ↦ inferInstanceAs (LocallyOfFiniteType (W i).hom))
  let ei (i : I) : (Over.pullback (q i)).obj Z ≅ W i :=
    (eqToIso ((AlgebraicGeometry.canonicalFamilyDescentFunctor q).obj Z i)).symm ≪≫
      (AlgebraicGeometry.DescentData.evaluation i).mapIso e
  refine ⟨Z, ?_, fun i ↦ ⟨ei i⟩⟩
  refine MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd
    (P := @IsImmersion) hq ?_
  rintro V' g' _ ⟨i⟩
  have : IsIso (ei i).hom.left := Functor.map_isIso (Over.forget (U i)) (ei i).hom
  have hw := Over.w (ei i).hom
  change (ei i).hom.left ≫ (W i).hom = pullback.snd Z.hom (q i) at hw
  rw [← hw]
  infer_instance

/-- A subterminal sheaf is inhabited over an object exactly when it is inhabited over every
member of a covering family. -/
theorem nonempty_iff_forall_of_subsingleton_sheaf {C : Type*} [Category C]
    {J : GrothendieckTopology C} (F : Cᵒᵖ ⥤ Type*) (hF : Presieve.IsSheaf J F)
    (hsub : ∀ T, Subsingleton (F.obj (op T))) {T : C} {I' : Type*} (U' : I' → C)
    (f' : ∀ i, U' i ⟶ T) (hf : Sieve.ofArrows U' f' ∈ J T) :
    Nonempty (F.obj (op T)) ↔ ∀ i, Nonempty (F.obj (op (U' i))) := by
  classical
  refine ⟨fun ⟨s⟩ i ↦ ⟨F.map (f' i).op s⟩, fun hs ↦ ?_⟩
  have hc : Presieve.Arrows.Compatible F f' fun i ↦ Classical.choice (hs i) :=
    fun i j V' a b _ ↦ @Subsingleton.elim _ (hsub V') _ _
  have hsheaf := (Presieve.isSheafFor_iff_generate (Presieve.ofArrows U' f')).mpr (hF _ hf)
  obtain ⟨s, _, _⟩ := (Presieve.isSheafFor_arrows_iff (π := f') (P := F)).mp hsheaf _ hc
  exact ⟨s⟩

/-- The projection from the base change of a scheme over the base along a member of the family. -/
noncomputable abbrev overBaseChangeProjection {S U' : Scheme.{u}} (q' : U' ⟶ S)
    (T : Over S) : (Over.map q').obj ((Over.pullback q').obj T) ⟶ T :=
  Over.homMk (pullback.fst T.hom q') pullback.condition

/-- Base changing a covering family of the base along a scheme over it covers that scheme. -/
theorem overBaseChangeProjection_covering {S : Scheme.{u}} {I' : Type u}
    {U' : I' → Scheme.{u}} (q' : ∀ i, U' i ⟶ S)
    (hq : Presieve.ofArrows U' q' ∈ Scheme.fpqcPrecoverage S) (T : Over S) :
    Sieve.ofArrows (fun i ↦ (Over.map (q' i)).obj ((Over.pullback (q' i)).obj T))
      (fun i ↦ overBaseChangeProjection (q' i) T) ∈ (Scheme.fpqcTopology.over S) T := by
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  exact Precoverage.generate_mem_toGrothendieck
    (({ I₀ := I', X := U', f := q', mem₀ := hq } :
      Scheme.fpqcPrecoverage.ZeroHypercover S).pullback₁ T.hom).mem₀

include hP in
/-- **A scheme restricting to the local representatives represents the property**, as soon as
the property descends along the base changes of the family. -/
theorem forall_iff_nonempty_of_localRepresentatives
    (hq : Presieve.ofArrows U q ∈ Scheme.fppfPrecoverage B)
    (hsheaf : ∀ T : Over B,
      (∀ i, P ((Over.map (q i)).obj ((Over.pullback (q i)).obj T))) → P T)
    (h : ∀ i, ∀ T : Over (U i), P ((Over.map (q i)).obj T) ↔ Nonempty (T ⟶ W i))
    (Z : Over B) [Mono Z.hom] (e : ∀ i, (Over.pullback (q i)).obj Z ≅ W i) (T : Over B) :
    P T ↔ Nonempty (T ⟶ Z) := by
  classical
  have hq' := Scheme.fppfPrecoverage_le_fpqcPrecoverage _ hq
  have hZ : Presieve.IsSheaf (Scheme.fpqcTopology.over B) (yoneda.obj Z) :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
  let Q (i : I) := (Over.map (q i)).obj ((Over.pullback (q i)).obj T)
  let a (i : I) : Q i ⟶ T := overBaseChangeProjection (q i) T
  have ha : Sieve.ofArrows Q a ∈ (Scheme.fpqcTopology.over B) T :=
    overBaseChangeProjection_covering q hq' T
  rw [show Nonempty (T ⟶ Z) ↔ ∀ i, Nonempty (Q i ⟶ Z) from
      nonempty_iff_forall_of_subsingleton_sheaf (yoneda.obj Z) hZ
        (fun T' ↦ subsingleton_overHom_of_mono T' Z) Q a ha]
  refine ⟨fun hT i ↦ ?_, fun hT ↦ hsheaf T fun i ↦ ?_⟩
  · have hQ : P (Q i) := hP (a i) hT
    obtain ⟨g⟩ := (h i ((Over.pullback (q i)).obj T)).mp hQ
    let adj := Over.mapPullbackAdj (q i)
    exact ⟨(adj.homEquiv _ _).symm (g ≫ (e i).inv)⟩
  · obtain ⟨g⟩ := hT i
    let adj := Over.mapPullbackAdj (q i)
    exact (h i ((Over.pullback (q i)).obj T)).mpr ⟨adj.homEquiv _ _ g ≫ (e i).hom⟩

include hP in
/-- **Representability by an immersion is local on the base** for a property which descends along
the base changes of an fppf covering family. -/
theorem exists_immersion_of_localRepresentatives
    (hq : Presieve.ofArrows U q ∈ Scheme.fppfPrecoverage B)
    (hsheaf : ∀ T : Over B,
      (∀ i, P ((Over.map (q i)).obj ((Over.pullback (q i)).obj T))) → P T)
    [∀ i, IsImmersion (W i).hom]
    (h : ∀ i, ∀ T : Over (U i), P ((Over.map (q i)).obj T) ↔ Nonempty (T ⟶ W i)) :
    ∃ Z : Over B, IsImmersion Z.hom ∧ ∀ T : Over B, P T ↔ Nonempty (T ⟶ Z) := by
  obtain ⟨Z, hZ, e⟩ := exists_isImmersion_of_localRepresentatives P hP q W hq h
  exact ⟨Z, hZ, forall_iff_nonempty_of_localRepresentatives P hP q W hq hsheaf h Z
    fun i ↦ Classical.choice (e i)⟩

end Family

section OpenCover

variable {S : Scheme.{u}}

/-- An immersion `i : Z ⟶ S` *represents* a property `P` of morphisms into `S` *over* an open
`W ⊆ S` if its image lies in `W` and a morphism with image in `W` has the property exactly when
it factors through `i`. -/
def RepresentsOn (P : ∀ T : Scheme.{u}, (T ⟶ S) → Prop) (W : S.Opens) {Z : Scheme.{u}}
    (i : Z ⟶ S) : Prop :=
  IsImmersion i ∧ Set.range i.base ⊆ W ∧
    ∀ (T : Scheme.{u}) (a : T ⟶ S), Set.range a.base ⊆ W → (P T a ↔ ∃ b : T ⟶ Z, b ≫ i = a)

variable (P : ∀ T : Scheme.{u}, (T ⟶ S) → Prop)
  (hP : ∀ {T T' : Scheme.{u}} (g : T' ⟶ T) (a : T ⟶ S), P T a → P T' (g ≫ a))
  (hsheaf : ∀ {T : Scheme.{u}} (a : T ⟶ S) {K : Type u} (O : K → T.Opens),
    (∀ t, ∃ k, t ∈ O k) → (∀ k, P _ ((O k).ι ≫ a)) → P T a)

/-- The range of a composite lies in any set containing the range of its last factor. -/
private theorem range_comp_base_subset {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) {A : Set Z}
    (h : Set.range g.base ⊆ A) : Set.range (f ≫ g).base ⊆ A := by
  rw [Scheme.Hom.comp_base, TopCat.coe_comp]
  exact (Set.range_comp_subset_range _ _).trans h

/-- The open `W.ι ⁻¹ᵁ V` of `W`, viewed in `S`, has image `V` when `V ≤ W`. -/
theorem range_preimage_ι_comp_ι {W V : S.Opens} (h : V ≤ W) :
    Set.range ((W.ι ⁻¹ᵁ V).ι ≫ W.ι).base = V := by
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
  ext s
  simp only [Set.mem_image, SetLike.mem_coe]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hs
    exact ⟨⟨s, h hs⟩, hs, rfl⟩

/-- Over morphisms `T ⟶ Y` are the factorisations of `T.hom ≫ m` through `Y.hom ≫ m`, for `m`
a monomorphism. -/
theorem nonempty_overHom_iff_exists_comp_mono {C : Type*} [Category C] {X X' : C} (m : X ⟶ X')
    [Mono m] (T Y : Over X) :
    Nonempty (T ⟶ Y) ↔ ∃ b : T.left ⟶ Y.left, b ≫ Y.hom ≫ m = T.hom ≫ m :=
  ⟨fun ⟨b⟩ ↦ ⟨b.left, by rw [← Category.assoc, Over.w b]⟩,
    fun ⟨b, hb⟩ ↦ ⟨Over.homMk b ((cancel_mono m).mp (by rw [Category.assoc, hb]))⟩⟩

include hP hsheaf in
/-- A property of morphisms into `S` which is local in the source holds for `T.hom ≫ W.ι` as
soon as it holds after base change along every member of an open cover of `W`. -/
theorem comp_ι_of_forall_pullback_opens (W : S.Opens) {J : Type u} (O : J → W.toScheme.Opens)
    (hcov : ∀ x : W.toScheme, ∃ j, x ∈ O j) (T : Over W.toScheme)
    (hT : ∀ j, P _ ((pullback.snd T.hom (O j).ι ≫ (O j).ι) ≫ W.ι)) : P _ (T.hom ≫ W.ι) := by
  refine hsheaf (T.hom ≫ W.ι) (fun j ↦ T.hom ⁻¹ᵁ O j)
    (fun t ↦ (hcov (T.hom t)).imp fun _ h ↦ h) fun j ↦ ?_
  have hT' := hT j
  rw [← pullback.condition] at hT'
  let l : (T.hom ⁻¹ᵁ O j).toScheme ⟶ pullback T.hom (O j).ι :=
    pullback.lift (T.hom ⁻¹ᵁ O j).ι (T.hom ∣_ O j) (morphismRestrict_ι T.hom (O j)).symm
  have := hP l _ hT'
  rwa [← Category.assoc, ← Category.assoc, pullback.lift_fst, Category.assoc] at this

include hP hsheaf in
/-- **Representability by an immersion over an open is local on that open.** If the opens `V j`
cover `W` and `P` is represented by an immersion over each of them, then it is represented by an
immersion over `W`. -/
theorem exists_representsOn_of_cover (W : S.Opens) {J : Type u} (V : J → S.Opens)
    (hV : ∀ j, V j ≤ W) (hcov : ∀ s ∈ W, ∃ j, s ∈ V j) (Z : J → Scheme.{u})
    (i : ∀ j, Z j ⟶ S) (hi : ∀ j, RepresentsOn P (V j) (i j)) :
    ∃ (Z₀ : Scheme.{u}) (i₀ : Z₀ ⟶ S), RepresentsOn P W i₀ := by
  classical
  let B := W.toScheme
  let O (j : J) : B.Opens := W.ι ⁻¹ᵁ V j
  let q (j : J) : (O j).toScheme ⟶ B := (O j).ι
  have hrange (j : J) : Set.range (q j ≫ W.ι).base = V j := range_preimage_ι_comp_ι (hV j)
  have hiV (j : J) : Set.range (i j).base ⊆ Set.range (q j ≫ W.ι).base :=
    (hi j).2.1.trans (hrange j).ge
  let w (j : J) : Z j ⟶ (O j).toScheme := IsOpenImmersion.lift (q j ≫ W.ι) (i j) (hiV j)
  have hw (j : J) : w j ≫ q j ≫ W.ι = i j := IsOpenImmersion.lift_fac _ _ _
  have hwimm (j : J) : IsImmersion (w j) := by
    have : IsImmersion (w j ≫ q j ≫ W.ι) := by
      rw [hw]
      exact (hi j).1
    exact IsImmersion.of_comp (w j) (q j ≫ W.ι)
  let Wj (j : J) : Over (O j).toScheme := Over.mk (w j)
  have : ∀ j, IsImmersion (Wj j).hom := hwimm
  let PB : Over B → Prop := fun T ↦ P _ (T.hom ≫ W.ι)
  have hPB : ∀ {T T' : Over B}, (T' ⟶ T) → PB T → PB T' := by
    intro T T' g hT
    change P _ (T'.hom ≫ W.ι)
    rw [← Over.w g, Category.assoc]
    exact hP g.left _ hT
  have hcovB : Presieve.ofArrows (fun j ↦ (O j).toScheme) q ∈ Scheme.fppfPrecoverage B := by
    refine (Scheme.ofArrows_mem_precoverage_iff _).mpr ⟨fun x ↦
      (hcov x.1 x.2).imp fun j hj ↦ ⟨⟨x, hj⟩, rfl⟩, fun j ↦ ⟨inferInstance, inferInstance⟩⟩
  have hsheafB : ∀ T : Over B,
      (∀ j, PB ((Over.map (q j)).obj ((Over.pullback (q j)).obj T))) → PB T :=
    fun T hT ↦ comp_ι_of_forall_pullback_opens P hP hsheaf W O (fun x ↦ hcov x.1 x.2) T hT
  have hloc : ∀ j, ∀ T : Over (O j).toScheme,
      PB ((Over.map (q j)).obj T) ↔ Nonempty (T ⟶ Wj j) := by
    intro j T
    change P _ ((T.hom ≫ q j) ≫ W.ι) ↔ _
    rw [Category.assoc]
    rw [(hi j).2.2 T.left _ (range_comp_base_subset _ _ (hrange j).le), ← hw]
    exact (nonempty_overHom_iff_exists_comp_mono (q j ≫ W.ι) T (Wj j)).symm
  obtain ⟨Z₀, hZ₀, hrep⟩ :=
    exists_immersion_of_localRepresentatives PB hPB q Wj hcovB hsheafB hloc
  refine ⟨Z₀.left, Z₀.hom ≫ W.ι, inferInstance, ?_, fun T a ha ↦ ?_⟩
  · exact range_comp_base_subset _ _ (Scheme.Opens.range_ι W).le
  · have ha' : Set.range a.base ⊆ Set.range W.ι.base := by rwa [Scheme.Opens.range_ι]
    let a' : T ⟶ B := IsOpenImmersion.lift W.ι a ha'
    have ha'fac : a' ≫ W.ι = a := IsOpenImmersion.lift_fac _ _ _
    rw [← ha'fac]
    exact (hrep (Over.mk a')).trans (nonempty_overHom_iff_exists_comp_mono W.ι (Over.mk a') Z₀)

/-- A representative over `W` satisfies the property itself. -/
theorem RepresentsOn.self {P : ∀ T : Scheme.{u}, (T ⟶ S) → Prop} {W : S.Opens} {Z : Scheme.{u}}
    {i : Z ⟶ S} (hi : RepresentsOn P W i) : P Z i :=
  (hi.2.2 Z i hi.2.1).mpr ⟨𝟙 Z, Category.id_comp _⟩

/-- A representative over `W` is a monomorphism. -/
theorem RepresentsOn.mono {P : ∀ T : Scheme.{u}, (T ⟶ S) → Prop} {W : S.Opens} {Z : Scheme.{u}}
    {i : Z ⟶ S} (hi : RepresentsOn P W i) : Mono i :=
  have := hi.1
  inferInstance

/-- **Restricting the range.** A representative over a smaller open `W'` is a representative
over `V ⊇ W'` as soon as every morphism with image in `V` having the property has image in
`W'`. -/
theorem RepresentsOn.of_le {P : ∀ T : Scheme.{u}, (T ⟶ S) → Prop} {W' V : S.Opens}
    {Z : Scheme.{u}} {i : Z ⟶ S} (hi : RepresentsOn P W' i) (hle : W' ≤ V)
    (h : ∀ (T : Scheme.{u}) (a : T ⟶ S), Set.range a.base ⊆ V → P T a →
      Set.range a.base ⊆ W') :
    RepresentsOn P V i := by
  refine ⟨hi.1, hi.2.1.trans hle, fun T a ha ↦ ⟨fun hP ↦ (hi.2.2 T a (h T a ha hP)).mp hP,
    fun ⟨b, hb⟩ ↦ (hi.2.2 T a ?_).mpr ⟨b, hb⟩⟩⟩
  rw [← hb]
  exact range_comp_base_subset _ _ hi.2.1

/-- A representative over `W` compares with a representative over `V ≤ W`: the second factors
through the first, and the preimage under the first of a subset of `V` is the image of its
preimage under the second. -/
theorem RepresentsOn.exists_factor {P : ∀ T : Scheme.{u}, (T ⟶ S) → Prop}
    (hP : ∀ {T T' : Scheme.{u}} (g : T' ⟶ T) (a : T ⟶ S), P T a → P T' (g ≫ a))
    {W V : S.Opens} {Z₀ Z : Scheme.{u}} {i₀ : Z₀ ⟶ S} {i : Z ⟶ S}
    (hi₀ : RepresentsOn P W i₀) (hi : RepresentsOn P V i) (hle : V ≤ W) :
    ∃ φ : Z ⟶ Z₀, φ ≫ i₀ = i ∧ ∀ A : Set S, A ⊆ V → i₀.base ⁻¹' A = φ.base '' (i.base ⁻¹' A) := by
  obtain ⟨φ, hφ⟩ := (hi₀.2.2 Z i (hi.2.1.trans hle)).mp hi.self
  refine ⟨φ, hφ, fun A hA ↦ ?_⟩
  ext z
  constructor
  · intro hz
    have hzV : i₀.base z ∈ V := hA hz
    let O : Z₀.Opens := i₀ ⁻¹ᵁ V
    have hrange : Set.range (O.ι ≫ i₀).base ⊆ V := by
      rintro _ ⟨w, rfl⟩
      exact w.2
    obtain ⟨c, hc⟩ := (hi.2.2 _ (O.ι ≫ i₀) hrange).mp (hP O.ι i₀ hi₀.self)
    have := hi₀.mono
    have hcφ : c ≫ φ = O.ι := by
      rw [← cancel_mono i₀, Category.assoc, hφ, hc]
    refine ⟨c.base ⟨z, hzV⟩, ?_, ?_⟩
    · change (c ≫ i).base ⟨z, hzV⟩ ∈ A
      rwa [hc]
    · change (c ≫ φ).base ⟨z, hzV⟩ = z
      rw [hcφ]
      rfl
  · rintro ⟨w, hw, rfl⟩
    change (φ ≫ i₀).base w ∈ A
    rwa [hφ]

/-- The preimage under `i` of every affine open contained in `W` is compact. -/
def QCOn (W : S.Opens) {Z : Scheme.{u}} (i : Z ⟶ S) : Prop :=
  ∀ U : S.Opens, U ≤ W → IsAffineOpen U → IsCompact (i.base ⁻¹' (U : Set S))

/-- **Quasi-compactness over an open is local on that open.** -/
theorem qcOn_of_cover {P : ∀ T : Scheme.{u}, (T ⟶ S) → Prop}
    (hP : ∀ {T T' : Scheme.{u}} (g : T' ⟶ T) (a : T ⟶ S), P T a → P T' (g ≫ a))
    (W : S.Opens) {Z₀ : Scheme.{u}} {i₀ : Z₀ ⟶ S} (hi₀ : RepresentsOn P W i₀)
    {J : Type u} (V : J → S.Opens) (hV : ∀ j, V j ≤ W) (hcov : ∀ s ∈ W, ∃ j, s ∈ V j)
    (Z : J → Scheme.{u}) (i : ∀ j, Z j ⟶ S) (hi : ∀ j, RepresentsOn P (V j) (i j))
    (hqc : ∀ j, QCOn (V j) (i j)) : QCOn W i₀ := by
  classical
  intro U hUW hU
  have hsmall : ∀ s : U, ∃ (A : S.Opens) (j : J), IsAffineOpen A ∧ s.1 ∈ A ∧ A ≤ U ∧ A ≤ V j := by
    intro s
    obtain ⟨j, hj⟩ := hcov s.1 (hUW s.2)
    obtain ⟨_, ⟨A, hA, rfl⟩, hsA, hAle⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open (show s.1 ∈ (U ⊓ V j : S.Opens) from
        ⟨s.2, hj⟩) (U ⊓ V j).isOpen
    exact ⟨A, j, hA, hsA, fun x hx ↦ (hAle hx).1, fun x hx ↦ (hAle hx).2⟩
  choose A j hA hsA hAU hAV using hsmall
  obtain ⟨t, ht⟩ := hU.isCompact.elim_finite_subcover (fun s : U ↦ (A s : Set S))
    (fun s ↦ (A s).isOpen) (fun x hx ↦ Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hsA ⟨x, hx⟩⟩)
  have hpre : i₀.base ⁻¹' (U : Set S) = ⋃ s ∈ t, i₀.base ⁻¹' (A s : Set S) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_iUnion]
    constructor
    · exact fun hz ↦ Set.mem_iUnion₂.mp (ht hz)
    · rintro ⟨s, -, hzs⟩
      exact hAU s hzs
  rw [hpre]
  refine t.isCompact_biUnion fun s _ ↦ ?_
  obtain ⟨φ, -, hφ⟩ := hi₀.exists_factor hP (hi (j s)) (hV (j s))
  rw [hφ _ (hAV s)]
  exact (hqc (j s) (A s) (hAV s) (hA s)).image φ.base.hom.continuous

end OpenCover

end Stacks.Flatness

end
