module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift
public import Mathlib.CategoryTheory.Limits.Types.Coproducts
public import Mathlib.CategoryTheory.Types.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Construction.ObjectsInCollection
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Presheaf
public import Mathlib.CategoryTheory.Sites.Over

/-!
# Hypercoverings of the final presheaf by objects in a covering collection

On a site with equalizers and fibre products, if every object has a covering by members of a
collection `B`, then the final presheaf has a hypercovering whose constituent objects all belong
to `B`.

## Main results

* `Stacks.CategoryTheory.Hypercovering.exists_hypercoveringOfTerminal_with_objects_in`:
  existence of such a hypercovering.
* `Stacks.CategoryTheory.Hypercovering.isHypercovering_yonedaFormal`: **the reverse transfer** --
  a hypercovering of the final presheaf becomes, under the Yoneda embedding into the slice over
  the final presheaf, a hypercovering for `localPretopology`.
* `Stacks.CategoryTheory.Hypercovering.isCoveringOver_yonedaFormal_map`: a covering morphism of
  semi-representable objects of the site becomes a covering morphism for `localPretopology`.
* `Stacks.CategoryTheory.Hypercovering.homLocallySurjective_of_locallySurjective`: a morphism of
  formal coproducts whose associated morphism of presheaves is locally surjective is locally
  surjective on morphisms out of the objects of the site -- the converse of
  `locallySurjective_of_homLocallySurjective`.

## Implementation notes

Hypercoverings of the final presheaf are `HypercoveringOfTerminal`, and semi-representable
objects are formal coproducts. The index universe is large enough to index both the objects of
the site and its morphisms.

The category of presheaves is equipped with the pretopology of families that are locally
surjective on sections. Applying the existence theorem for hypercoverings of an object to the
terminal presheaf gives a hypercovering by representables. The fully faithful Yoneda embedding
then lifts its simplicial object back to semi-representable objects of the original site. The
universal property of the matching cones allows the required local lifts to descend along this
embedding.

**The two directions.** `hypercoveringOfTerminal_lift` descends: a simplicial formal coproduct of
objects of the site, isomorphic after `yonedaFormal` to a hypercovering for `localPretopology`,
carries a hypercovering of the final presheaf. `isHypercovering_yonedaFormal` ascends. The
ascent is what makes results about hypercoverings of an *object* applicable to hypercoverings of
the final presheaf: the slice over the final presheaf is a slice over a terminal object in a
category with all limits, so [Stacks, Tag 01GJ] and the whole covering-permanence chain hold
there, whereas `FormalCoproduct C` has no terminal object unless `C` does.

Both directions rest on one bijection and nothing else: for a fully faithful `G`, precomposition
with `matchingComparison G L n t` is a bijection from `T ⟶ Mₙ(L)ₜ` onto `G T ⟶ Mₙ(L ⋙ G)ₜ`. It
is injective by `matchingComparison_injective` and surjective by `exists_matchingComparison_eq`;
neither uses preservation of limits by `G`, because a morphism into the matching object of the
image is a cone on `G` composed with the truncated diagram, whose legs are `G` of unique
morphisms by fullness and form a cone by faithfulness. In degree one the matching object is a
product of two copies of the degree-zero term -- there being exactly two face maps `⦋0⦌ ⟶ ⦋1⦌` --
and the two directions are `zeroMatchingLift` and `zeroMatching_hom_ext`.

## References

* [Stacks Project, Tag 0DAX](https://stacks.math.columbia.edu/tag/0DAX)
-/

@[expose] public section

universe w v u q d e

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local implicit_reducible] CategoryTheory.SimplicialObject.truncation

namespace Stacks.CategoryTheory.Hypercovering

attribute [local implicit_reducible] mapFormalCoproduct

variable {C : Type u} [Category.{v} C] [HasEqualizers C] [HasPullbacks C]

section LocalPretopology

/-- The sieve of arrows along which a section of a presheaf lifts to some member of a given
family of maps into it. -/
def localLifts
    {F : Cᵒᵖ ⥤ Type q} (R : Presieve F) (U : C) (s : F.obj (op U)) : Sieve U where
  arrows V f := ∃ (Y : Cᵒᵖ ⥤ Type q) (g : Y ⟶ F), R g ∧
    ∃ y : Y.obj (op V), g.app (op V) y = F.map f.op s
  downward_closed := by
    intro V W f hf h
    obtain ⟨Y, g, hg, y, hy⟩ := hf
    refine ⟨Y, g, hg, Y.map h.op y, ?_⟩
    rw [NatTrans.naturality_apply, hy]
    simpa only [op_comp] using (Functor.map_comp_apply F f.op h.op s).symm

/-- The pretopology on presheaves whose coverings are the families along which every section
lifts locally. -/
def localPretopology (J : Pretopology C) : Pretopology (Cᵒᵖ ⥤ Type q) where
  coverings F := {R | ∀ U s, localLifts R U s ∈ J.toGrothendieck U}
  has_isos := by
    intro X Y f hf
    have : IsIso f := hf
    intro U s
    have htop : (⊤ : Sieve U) ≤ localLifts (Presieve.singleton f) U s := by
      intro V g hg
      refine ⟨Y, f, Presieve.singleton_self f, (inv f).app (op V) (X.map g.op s), ?_⟩
      simp
    exact J.toGrothendieck.superset_covering htop (J.toGrothendieck.top_mem U)
  pullbacks := by
    intro X Y f R hR U s
    have hle : localLifts R U (f.app (op U) s) ≤ localLifts (Presieve.pullbackArrows f R) U s := by
      intro V g hg
      obtain ⟨Z, k, hk, z, hz⟩ := hg
      let P := pullback k f
      let a : PUnit.{q + 1} ⟶ Z.obj (op V) := TypeCat.ofHom (fun _ ↦ z)
      let b : PUnit.{q + 1} ⟶ Y.obj (op V) := TypeCat.ofHom (fun _ ↦ Y.map g.op s)
      let t : pullback (k.app (op V)) (f.app (op V)) :=
        (ConcreteCategory.hom (pullback.lift a b (by
          ext x
          exact hz.trans (NatTrans.naturality_apply f g.op s).symm))) PUnit.unit
      let y : P.obj (op V) := (pullbackObjIso k f (op V)).inv t
      have hy : (pullback.snd k f).app (op V) y = Y.map g.op s := by
        change (ConcreteCategory.hom ((pullbackObjIso k f (op V)).inv ≫
          (pullback.snd k f).app (op V))) t = _
        rw [pullbackObjIso_inv_comp_snd]
        change ConcreteCategory.hom
          (pullback.lift a b (by
              ext x
              exact hz.trans (NatTrans.naturality_apply f g.op s).symm) ≫
            pullback.snd (k.app (op V)) (f.app (op V)))
          PUnit.unit = _
        rw [pullback.lift_snd]
        rfl
      refine ⟨P, pullback.snd k f, Presieve.pullbackArrows.mk Z k hk, y, ?_⟩
      simp [hy]
    exact J.toGrothendieck.superset_covering hle (hR U (f.app (op U) s))
  transitive := by
    intro X R T hR hT U s
    apply J.toGrothendieck.transitive (hR U s)
    intro V f hf
    obtain ⟨Y, g, hg, y, hy⟩ := hf
    apply J.toGrothendieck.superset_covering ?_ (hT g hg V y)
    intro W k hk
    obtain ⟨Z, h, hh, z, hz⟩ := hk
    refine ⟨Z, h ≫ g, ⟨Y, h, g, hg, hh, rfl⟩, z, ?_⟩
    calc
      g.app (op W) (h.app (op W) z) = g.app (op W) (Y.map k.op y) := by rw [hz]
      _ = X.map k.op (g.app (op V) y) := NatTrans.naturality_apply g k.op y
      _ = X.map k.op (X.map f.op s) := by rw [hy]
      _ = X.map (k ≫ f).op s := by
        simpa only [op_comp] using (Functor.map_comp_apply X f.op k.op s).symm

omit [HasEqualizers C] in
/-- The coverings of `localPretopology` are upward closed: any family refining a family along
which every section lifts locally is again such a family. -/
theorem mem_localPretopology_coverings_of_le (J : Pretopology C) {F : Cᵒᵖ ⥤ Type q}
    {R R' : Presieve F} (hR : R ∈ (localPretopology J).coverings F) (hle : R ≤ R') :
    R' ∈ (localPretopology J).coverings F := by
  intro U s
  refine J.toGrothendieck.superset_covering ?_ (hR U s)
  intro V f hf
  obtain ⟨Y, g, hg, y, hy⟩ := hf
  exact ⟨Y, g, hle _ _ hg, y, hy⟩

/-- Composing a covering family of arrows with an equality of objects at the common target
leaves it covering. -/
theorem ofArrows_comp_eqToHom_mem {D : Type d} [Category.{e} D] [HasPullbacks D]
    (K : Pretopology D) {Z T : D} (h : Z = T) {σ : Type*} {Y : σ → D} (g : ∀ t, Y t ⟶ Z)
    (hg : Presieve.ofArrows Y g ∈ K Z) :
    Presieve.ofArrows Y (fun t ↦ g t ≫ eqToHom h) ∈ K T := by
  subst h
  simpa using hg

omit [HasEqualizers C] in
/-- **`localPretopology` is stable under composition.** Composing a family along which every
section of a presheaf lifts locally with such a family over each of its members gives again
such a family. -/
instance isStableUnderComposition_localPretopology (J : Pretopology C) :
    Precoverage.IsStableUnderComposition
      (localPretopology J : Pretopology (Cᵒᵖ ⥤ Type q)).toPrecoverage where
  comp_mem_coverings {_ι} {_S} {X} f hf {σ} {Y} g hg := by
    refine mem_localPretopology_coverings_of_le J
      ((localPretopology J).transitive (Presieve.ofArrows X f)
        (fun _ _ H ↦ Presieve.ofArrows (Y H.idx) fun t ↦ g H.idx t ≫ eqToHom H.obj_idx) hf
        (fun _ _ H ↦ ofArrows_comp_eqToHom_mem (localPretopology J) H.obj_idx _ (hg H.idx))) ?_
    rintro T u ⟨W, a, f', H, ⟨t⟩, rfl⟩
    exact Presieve.ofArrows.mk' ⟨H.idx, t⟩ rfl (by simp [Presieve.ofArrows.hom_idx H])

omit [HasEqualizers C] in
theorem localPretopology_adjoin (J : Pretopology C)
    {F Y : Cᵒᵖ ⥤ Type q} {R : Presieve F}
    (hR : R ∈ (localPretopology J).coverings F) (g : Y ⟶ F) :
    (fun {_} h ↦ R h ∨ Presieve.singleton g h) ∈ (localPretopology J).coverings F :=
  mem_localPretopology_coverings_of_le J hR fun _ _ h ↦ Or.inl h

omit [HasEqualizers C] in
theorem exists_presheaf_cover_by_representables (J : Pretopology C)
    (B : Set C) (hcover : ∀ U : C, ∃ (ι : Type (max w u v)) (V : ι → C)
      (f : ∀ i, V i ⟶ U), (∀ i, V i ∈ B) ∧ Presieve.ofArrows V f ∈ J U) :
    ∀ F : Cᵒᵖ ⥤ Type (max w u v), ∃ (κ : Type (max w u v))
      (P : κ → Cᵒᵖ ⥤ Type (max w u v))
      (g : ∀ i, P i ⟶ F), (∀ i, ∃ U ∈ B, P i = uliftYoneda.{max w u} (C := C).obj U) ∧
        Presieve.ofArrows P g ∈
          (localPretopology.{v, u, max w u v} J).coverings F := by
  classical
  intro F
  choose ι V f hB hJ using hcover
  let I := Σ U : C, Σ s : F.obj (op U), ι U
  let W : I → C := fun p ↦ V p.1 p.2.2
  let g : ∀ p : I, uliftYoneda.{max w u} (C := C).obj (W p) ⟶ F := fun p ↦
    (uliftYonedaEquiv (X := W p) (F := F)).symm (F.map (f p.1 p.2.2).op p.2.1)
  refine ⟨I, fun p ↦ uliftYoneda.{max w u} (C := C).obj (W p), g, ?_, ?_⟩
  · intro p
    exact ⟨W p, hB p.1 p.2.2, rfl⟩
  · show ∀ U s, localLifts
      (Presieve.ofArrows (fun p : I ↦ uliftYoneda.{max w u} (C := C).obj (W p)) g)
      U s ∈ J.toGrothendieck U
    intro U s
    let S := localLifts (Presieve.ofArrows
      (fun p : I ↦ uliftYoneda.{max w u} (C := C).obj (W p)) g) U s
    have hgen : ∀ i : ι U, localLifts
        (Presieve.ofArrows
          (fun p : I ↦ uliftYoneda.{max w u} (C := C).obj (W p)) g)
        U s (f U i) := by
      intro i
      let p : I := ⟨U, s, i⟩
      refine ⟨uliftYoneda.{max w u} (C := C).obj (W p), g p, Presieve.ofArrows.mk p,
        ULift.up (𝟙 (W p)), ?_⟩
      simp [g, W, p]
    have hle : Sieve.generate (Presieve.ofArrows (V U) (f U)) ≤ S := by
      rw [Sieve.generate_le_iff]
      exact Presieve.ofArrows_le_iff.mpr hgen
    have hcov : Sieve.generate (Presieve.ofArrows (V U) (f U)) ∈ J.toGrothendieck U :=
      (Pretopology.mem_toGrothendieck J U
        (Sieve.generate (Presieve.ofArrows (V U) (f U)))).mpr
        ⟨Presieve.ofArrows (V U) (f U), hJ U,
          Sieve.le_generate (Presieve.ofArrows (V U) (f U))⟩
    exact J.toGrothendieck.superset_covering hle hcov

omit [HasEqualizers C] in
theorem exists_hypercovering_of_terminal_presheaf_in_presheaf_category
    (J : Pretopology C) (B : Set C)
    (hcover : ∀ U : C, ∃ (ι : Type (max w u v)) (V : ι → C)
      (f : ∀ i, V i ⟶ U), (∀ i, V i ∈ B) ∧ Presieve.ofArrows V f ∈ J U) :
    ∃ K : SimplicialObject (FormalCoproduct.{max w u v}
        (Over (⊤_ (Cᵒᵖ ⥤ Type (max w u v))))),
      IsHypercovering (localPretopology.{v, u, max w u v} J) K ∧
        ∀ (n : ℕ) (i : (K.obj (op (SimplexCategory.mk n))).I),
          ((K.obj (op (SimplexCategory.mk n))).obj i).left ∈
            {P : Cᵒᵖ ⥤ Type (max w u v) | ∃ U ∈ B,
              P = uliftYoneda.{max w u} (C := C).obj U} := by
  let B' : Set (Cᵒᵖ ⥤ Type (max w u v)) :=
    {P | ∃ U ∈ B, P = uliftYoneda.{max w u} (C := C).obj U}
  have hcover' : ∀ F : Cᵒᵖ ⥤ Type (max w u v),
      ∃ (ι : Type (max w u v)) (V : ι → Cᵒᵖ ⥤ Type (max w u v))
        (f : ∀ i, V i ⟶ F), (∀ i, V i ∈ B') ∧
          Presieve.ofArrows V f ∈ (localPretopology.{v, u, max w u v} J) F := by
    intro F
    obtain ⟨ι, V, f, hV, hf⟩ := exists_presheaf_cover_by_representables J B hcover F
    exact ⟨ι, V, f, fun i ↦ hV i, hf⟩
  have hadjoin' : ∀ {ι : Type (max w u v)} (V : ι → Cᵒᵖ ⥤ Type (max w u v))
      {F : Cᵒᵖ ⥤ Type (max w u v)} (f : ∀ i, V i ⟶ F),
      (∀ i, V i ∈ B') → Presieve.ofArrows V f ∈
        (localPretopology.{v, u, max w u v} J) F →
      ∀ {F' : Cᵒᵖ ⥤ Type (max w u v)}, F' ∈ B' → ∀ g : F' ⟶ F,
        (fun {_} h ↦ Presieve.ofArrows V f h ∨ Presieve.singleton g h) ∈
          (localPretopology.{v, u, max w u v} J) F := by
    intro ι V F f hV hf F' hF' g
    exact localPretopology_adjoin J hf g
  obtain ⟨K, hK, hB'⟩ := exists_hypercovering_with_objects_in
    (localPretopology.{v, u, max w u v} J) B' hcover' hadjoin'
    (⊤_ (Cᵒᵖ ⥤ Type (max w u v)))
  exact ⟨K, hK, hB'⟩

end LocalPretopology

section Lift

abbrev representableObjectsIn (B : Set C) : Set (Cᵒᵖ ⥤ Type (max w u v)) :=
  {P | ∃ U ∈ B, P = uliftYoneda.{max w u} (C := C).obj U}

/-- Choose, for a formal coproduct of representable presheaves, a formal coproduct of objects of
the site representing it. -/
noncomputable abbrev liftFormalObject (B : Set C)
    (X : FormalCoproduct.{max w u v} (Cᵒᵖ ⥤ Type (max w u v)))
    (hX : ∀ i, X.obj i ∈ representableObjectsIn (C := C) B) :
    FormalCoproduct.{max w u v} C :=
  ⟨X.I, fun i ↦ Classical.choose (hX i)⟩

omit [HasEqualizers C] [HasPullbacks C] in
theorem liftFormalObject_mem (B : Set C)
    (X : FormalCoproduct.{max w u v} (Cᵒᵖ ⥤ Type (max w u v)))
    (hX : ∀ i, X.obj i ∈ representableObjectsIn (C := C) B) (i : X.I) :
    (liftFormalObject B X hX).obj i ∈ B :=
  (Classical.choose_spec (hX i)).1

omit [HasEqualizers C] [HasPullbacks C] in
theorem liftFormalObject_eq (B : Set C)
    (X : FormalCoproduct.{max w u v} (Cᵒᵖ ⥤ Type (max w u v)))
    (hX : ∀ i, X.obj i ∈ representableObjectsIn (C := C) B) (i : X.I) :
    X.obj i = uliftYoneda.{max w u} (C := C).obj ((liftFormalObject B X hX).obj i) :=
  (Classical.choose_spec (hX i)).2

noncomputable abbrev liftFormalHom (B : Set C)
    {X Y : FormalCoproduct.{max w u v} (Cᵒᵖ ⥤ Type (max w u v))}
    (hX : ∀ i, X.obj i ∈ representableObjectsIn (C := C) B)
    (hY : ∀ i, Y.obj i ∈ representableObjectsIn (C := C) B) (f : X ⟶ Y) :
    liftFormalObject B X hX ⟶ liftFormalObject B Y hY :=
  ⟨f.f, fun i ↦ ULift.down (uliftYonedaEquiv.{max w u}
    (eqToHom (liftFormalObject_eq B X hX i).symm ≫ f.φ i ≫
      eqToHom (liftFormalObject_eq B Y hY (f.f i))))⟩

omit [HasEqualizers C] [HasPullbacks C] in
theorem liftFormalHom_map (B : Set C)
    {X Y : FormalCoproduct.{max w u v} (Cᵒᵖ ⥤ Type (max w u v))}
    (hX : ∀ i, X.obj i ∈ representableObjectsIn (C := C) B)
    (hY : ∀ i, Y.obj i ∈ representableObjectsIn (C := C) B) (f : X ⟶ Y) (i : X.I) :
    uliftYoneda.map ((liftFormalHom B hX hY f).φ i) =
      eqToHom (liftFormalObject_eq B X hX i).symm ≫ f.φ i ≫
        eqToHom (liftFormalObject_eq B Y hY (f.f i)) := by
  apply uliftYonedaEquiv.injective
  rw [uliftYonedaEquiv_uliftYoneda_map]

omit [HasEqualizers C] [HasPullbacks C] in
private theorem yonedaConjugate_id {A : C} {F : Cᵒᵖ ⥤ Type (max w u v)}
    (e : F = uliftYoneda.{max w u} (C := C).obj A) :
    ULift.down (uliftYonedaEquiv.{max w u}
      (eqToHom e.symm ≫ 𝟙 F ≫ eqToHom e)) = 𝟙 A := by
  cases e
  simp [uliftYonedaEquiv]

omit [HasEqualizers C] [HasPullbacks C] in
private theorem yonedaConjugate_comp
    {A B D : C} {F G H : Cᵒᵖ ⥤ Type (max w u v)}
    (eF : F = uliftYoneda.{max w u} (C := C).obj A)
    (eG : G = uliftYoneda.{max w u} (C := C).obj B)
    (eH : H = uliftYoneda.{max w u} (C := C).obj D)
    (f : F ⟶ G) (g : G ⟶ H) :
    ULift.down (uliftYonedaEquiv.{max w u}
      (eqToHom eF.symm ≫ (f ≫ g) ≫ eqToHom eH)) =
      ULift.down (uliftYonedaEquiv.{max w u}
        (eqToHom eF.symm ≫ f ≫ eqToHom eG)) ≫
        ULift.down (uliftYonedaEquiv.{max w u}
          (eqToHom eG.symm ≫ g ≫ eqToHom eH)) := by
  cases eF
  cases eG
  cases eH
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  let a : A ⟶ B := ULift.down (uliftYonedaEquiv.{max w u} f)
  let b : B ⟶ D := ULift.down (uliftYonedaEquiv.{max w u} g)
  have hf : f = uliftYoneda.map a := by
    apply uliftYonedaEquiv.injective
    simp [a]
  have hg : g = uliftYoneda.map b := by
    apply uliftYonedaEquiv.injective
    simp [b]
  rw [hf, hg]
  rw [← uliftYoneda.map_comp]
  simp only [uliftYonedaEquiv_uliftYoneda_map, ULift.down_up]

omit [HasEqualizers C] [HasPullbacks C] in
theorem liftFormalHom_id (B : Set C)
    (X : FormalCoproduct.{max w u v} (Cᵒᵖ ⥤ Type (max w u v)))
    (hX : ∀ i, X.obj i ∈ representableObjectsIn (C := C) B) :
    liftFormalHom B hX hX (𝟙 X) = 𝟙 (liftFormalObject B X hX) := by
  refine FormalCoproduct.hom_ext ?_ ?_
  · rfl
  · intro i
    show (liftFormalHom B hX hX (𝟙 X)).φ i ≫ 𝟙 _ = 𝟙 _
    rw [Category.comp_id]
    apply uliftYoneda.map_injective
    rw [liftFormalHom_map]
    simp

omit [HasEqualizers C] [HasPullbacks C] in
theorem liftFormalHom_comp (B : Set C)
    {X Y Z : FormalCoproduct.{max w u v} (Cᵒᵖ ⥤ Type (max w u v))}
    (hX : ∀ i, X.obj i ∈ representableObjectsIn (C := C) B)
    (hY : ∀ i, Y.obj i ∈ representableObjectsIn (C := C) B)
    (hZ : ∀ i, Z.obj i ∈ representableObjectsIn (C := C) B)
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    liftFormalHom B hX hZ (f ≫ g) = liftFormalHom B hX hY f ≫ liftFormalHom B hY hZ g := by
  refine FormalCoproduct.hom_ext ?_ ?_
  · rfl
  · intro i
    show (liftFormalHom B hX hZ (f ≫ g)).φ i ≫ 𝟙 _ =
      (liftFormalHom B hX hY f).φ i ≫ (liftFormalHom B hY hZ g).φ (f.f i)
    rw [Category.comp_id]
    apply uliftYoneda.map_injective
    rw [Functor.map_comp, liftFormalHom_map, liftFormalHom_map, liftFormalHom_map]
    simp [Category.assoc]

/-- Lift a simplicial formal coproduct of representable presheaves to a simplicial formal
coproduct of objects of the site. -/
@[implicit_reducible]
noncomputable def liftSimplicialObject (B : Set C)
    (Q : SimplicialObject (FormalCoproduct.{max w u v}
      (Cᵒᵖ ⥤ Type (max w u v))))
    (hQ : ∀ (n : SimplexCategoryᵒᵖ) (i : (Q.obj n).I),
      (Q.obj n).obj i ∈ representableObjectsIn (C := C) B) :
    SimplicialObject (FormalCoproduct.{max w u v} C) := by
  refine {
    obj n := liftFormalObject B (Q.obj n) (hQ n)
    map f := liftFormalHom B (hQ _) (hQ _) (Q.map f)
    map_id n := ?_
    map_comp f g := ?_ }
  · rw [Q.map_id]
    exact liftFormalHom_id B (Q.obj n) (hQ n)
  · rw [Q.map_comp]
    exact liftFormalHom_comp B (hQ _) (hQ _) (hQ _) (Q.map f) (Q.map g)

end Lift

end Stacks.CategoryTheory.Hypercovering

end
