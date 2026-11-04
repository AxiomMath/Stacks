module

public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Basic

/-!
# Hypercoverings given by a simplicial object of the site

Let `C` be a site given by a pretopology `J`, and assume `C` has fibre products. An augmented
simplicial object `U ⟶ X` of `C` gives rise to a simplicial semi-representable object over `X`
with exactly one summand in every degree. This file constructs that object and characterizes when
it is a hypercovering: precisely when the augmentation `U₀ ⟶ X`, the canonical degree-one
morphism `U₁ ⟶ U₀ ×_X U₀`, and all the higher matching morphisms
`U_{n+1} ⟶ (cosk_n sk_n U)_{n+1}` are coverings of the site, the last two taken in the slice
category over `X`.

## Main definitions

* `associatedSimplicialObject`: the one-summand simplicial semi-representable object over `X`
  associated to an augmented simplicial object of the site.
* `oneSimplexToFiberProduct`: its canonical degree-one morphism to `U₀ ×_X U₀`.
* `matchingMap`: the canonical morphism from `U_{n+1}` to the degree-`n + 1` term of the `n`-th
  coskeleton, formed in the slice category over `X`.

## Main results

* `isHypercovering_associatedSimplicialObject_iff` is the characterization above: the associated
  simplicial semi-representable object is a hypercovering exactly when the augmentation, the
  degree-one morphism to the fibre product, and every higher matching morphism generate a
  covering presieve.

## Implementation notes

An augmentation is a natural transformation to the constant simplicial object; `Over.lift`
regards it as a simplicial object of `C / X`, and `FormalCoproduct.incl` regards each of its terms
as a one-summand formal coproduct. The coskeleton in the higher covering conditions is formed in
`C / X`, and the underlying object in `C` of its degree-`n + 1` term is the target displayed in
`matchingMap`; `inclCoskeletonIso` is the comparison with the coskeleton formed in
`SR(C, X) = FormalCoproduct (Over X)`, available because `FormalCoproduct.incl` preserves finite
limits.

Because every object involved has a one-element index type, each covering condition reduces to a
single arrow generating a covering presieve, and the bulk of the file is that reduction:
`isCoveringOver_unique_iff_singleton` and `isCoveringOver_comp_iso_iff` (both from
`Hypercovering.Basic`) for the formal-coproduct side, and the `ZeroMatching` section
for the identification of `(cosk_0 sk_0 U)_1` with
`U₀ ×_X U₀`, which is what turns the `n = 0` matching condition into the condition on
`oneSimplexToFiberProduct`.

## References

* [Stacks Project, Tag 0GM9](https://stacks.math.columbia.edu/tag/0GM9)
-/

@[expose] public section

universe w v u w' v'

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Simplicial
open CategoryTheory.SimplicialObject.Truncated

namespace Stacks.CategoryTheory.Hypercovering

private noncomputable def isLimitInclMapCone {C : Type u} [Category.{v} C] {J : Type w'}
    [Category.{v'} J] {F : J ⥤ C} {c : Cone F} (hc : IsLimit c) :
    IsLimit ((FormalCoproduct.incl.{w} C).mapCone c) := by
  let ci (s : Cone (F ⋙ FormalCoproduct.incl.{w} C)) (i : s.pt.I) : Cone F :=
    Cone.mk (s.pt.obj i)
      { app := fun j => (s.π.app j).φ i
        naturality := by
          intro j j' f
          have h := (FormalCoproduct.hom_ext_iff' _ _).mp (s.w f) i
          rcases h with ⟨_, h⟩
          simpa [FormalCoproduct.incl] using h.symm }
  refine ⟨fun s => ⟨fun _ => PUnit.unit, fun i => hc.lift (ci s i)⟩, ?_, ?_⟩
  · intro s j
    ext i
    · rfl
    · simp [FormalCoproduct.incl, ci]
  · intro s m hm
    ext i
    · rfl
    · have hm' : ∀ j, m.φ i ≫ c.π.app j = (ci s i).π.app j := by
        intro j
        have h := (FormalCoproduct.hom_ext_iff' _ _).mp (hm j) i
        rcases h with ⟨_, h⟩
        change (m.φ i ≫ c.π.app j) ≫ eqToHom (by rfl) = (ci s i).π.app j at h
        simpa [ci, Category.assoc] using h
      simpa [FormalCoproduct.incl] using hc.uniq (ci s i) (m.φ i) hm'

private instance preservesFiniteLimits_incl {C : Type u} [Category.{v} C]
    [HasFiniteLimits C] : PreservesFiniteLimits (FormalCoproduct.incl.{w} C) where
  preservesFiniteLimits _ _ _ := ⟨fun {_} => ⟨fun {_} hc => ⟨isLimitInclMapCone hc⟩⟩⟩

private theorem isCoveringOver_incl_map_iff {C : Type u} [Category.{v} C]
    [HasPullbacks C] (X : C) (J : Pretopology C) {A B : Over X} (f : A ⟶ B) :
    IsCoveringOver J ((FormalCoproduct.incl (Over X)).map f) ↔
      Presieve.singleton f.left ∈ J B.left := by
  constructor
  · intro h
    dsimp [IsCoveringOver, FormalCoproduct.incl] at h
    specialize h PUnit.unit
    let : Unique {i : PUnit // (PUnit.unit : PUnit) = PUnit.unit} :=
      ⟨⟨PUnit.unit, rfl⟩, fun i => by cases i; rfl⟩
    rw [Presieve.ofArrows_of_unique] at h
    simpa [Category.comp_id] using h
  · intro h j
    cases j
    dsimp [IsCoveringOver, FormalCoproduct.incl]
    let : Unique {i : PUnit // (PUnit.unit : PUnit) = PUnit.unit} :=
      ⟨⟨PUnit.unit, rfl⟩, fun i => by cases i; rfl⟩
    rw [Presieve.ofArrows_of_unique]
    change Presieve.singleton (f.left ≫ eqToHom (by rfl)) ∈ J B.left
    simpa using h

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {X : C}

private theorem mem_singleton_comp_iso {A B D : Over X} (J : Pretopology C)
    (f : A ⟶ B) (e : B ≅ D)
    (hf : Presieve.singleton f.left ∈ J B.left) :
    Presieve.singleton (f.left ≫ e.hom.left) ∈ J D.left := by
  have : IsIso e.hom.left := (Over.forget X).map_isIso _
  let Ti : ∀ ⦃Z : C⦄ (q : Z ⟶ D.left), Presieve.singleton e.hom.left q → Presieve Z :=
    fun {Z} _ hq => fun {_} r => by
      cases hq
      exact Presieve.singleton f.left r
  have hTi : ∀ ⦃Z⦄ (q : Z ⟶ D.left) (hq : Presieve.singleton e.hom.left q),
      Ti q hq ∈ J Z := by
    intro Z q hq
    cases hq
    exact hf
  have h := J.transitive (Presieve.singleton e.hom.left) Ti
    (J.has_isos e.hom.left) (by
      intro Z q hq
      exact hTi q hq)
  have heq : (Presieve.singleton e.hom.left).bind Ti =
      Presieve.singleton (f.left ≫ e.hom.left) := by
    funext Z q
    apply propext
    constructor
    · rintro ⟨Y, g, q', hq, hf', rfl⟩
      cases hq
      cases hf'
      exact Presieve.singleton.mk
    · rintro ⟨⟩
      exact Presieve.bind_comp (f := e.hom.left) (g := f.left)
        (Presieve.singleton_self e.hom.left)
        (by
          change Presieve.singleton f.left f.left
          exact Presieve.singleton_self f.left)
  rw [heq] at h
  exact h

private theorem mem_singleton_comp_iso_iff {A B D : Over X} (J : Pretopology C)
    (f : A ⟶ B) (e : B ≅ D) :
    Presieve.singleton f.left ∈ J B.left ↔
      Presieve.singleton (f.left ≫ e.hom.left) ∈ J D.left := by
  constructor
  · exact mem_singleton_comp_iso J f e
  · intro h
    have h' := mem_singleton_comp_iso J (f ≫ e.hom) e.symm h
    simpa [Category.assoc] using h'

variable (U : SimplicialObject C)
variable (a : U ⟶ (SimplicialObject.const C).obj X)

/-- **Stacks Project, Tag 0GM9.** The one-summand simplicial semi-representable object associated
to an augmented simplicial object of the site. -/
@[stacks 0GM9 "the associated simplicial object"]
def associatedSimplicialObject :
    SimplicialObject (FormalCoproduct.{w} (Over X)) :=
  Over.lift U a ⋙ FormalCoproduct.incl (Over X)

/-- The canonical map `U₁ ⟶ U₀ ×_X U₀`, whose two components are the two face maps. -/
noncomputable def oneSimplexToFiberProduct :
    U.obj (Opposite.op (SimplexCategory.mk 1)) ⟶
      pullback (a.app (Opposite.op (SimplexCategory.mk 0)))
        (a.app (Opposite.op (SimplexCategory.mk 0))) :=
  pullback.lift (U.δ 1) (U.δ 0) (by
    simp [SimplicialObject.δ, a.naturality])

/-- Pointwise right Kan extensions defining coskeleta exist for simplicial objects of `C / X`. -/
instance hasPointwiseRightKanExtension_over (n : ℕ)
    (F : SimplicialObject.Truncated (Over X) n) :
    (SimplexCategory.Truncated.inclusion n).op.HasPointwiseRightKanExtension F := by
  let _ : HasFiniteLimits (Over X) := hasFiniteLimits_of_hasTerminal_and_pullbacks
  let h :=
    hasPointwiseRightKanExtension_of_hasBinaryProducts_or_hasFiniteConnectedLimits
      (C := Over X)
  rcases n with _ | n
  · exact h.1 (by infer_instance) F
  · exact h.2 (fun _ _ _ _ ↦ by infer_instance) (n + 1) (by omega) F

private instance hasRightKanExtension_over (n : ℕ)
    (F : SimplicialObject.Truncated (Over X) n) :
    (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F :=
  (Functor.pointwiseRightKanExtensionIsPointwiseRightKanExtension
    (SimplexCategory.Truncated.inclusion n).op F).hasRightKanExtension

private instance hasRightKanExtension_formalCoproductOver (n : ℕ)
    (F : SimplicialObject.Truncated (FormalCoproduct.{w} (Over X)) n) :
    (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F :=
  (Functor.pointwiseRightKanExtensionIsPointwiseRightKanExtension
    (SimplexCategory.Truncated.inclusion n).op F).hasRightKanExtension

private instance preservesRightKanExtensions_incl (n : ℕ) :
    (FormalCoproduct.incl.{w} (Over X)).PreservesRightKanExtensions
      (SimplexCategory.Truncated.inclusion n).op := fun F' => by
  let : (FormalCoproduct.incl.{w} (Over X)).PreservesPointwiseRightKanExtension F'
      (SimplexCategory.Truncated.inclusion n).op := fun c =>
    ⟨fun E hE => ⟨IsLimit.ofIsoLimit (isLimitInclMapCone hE)
      (E.coneAtWhiskerRightIso _ F' _ c).symm⟩⟩
  infer_instance

private noncomputable def inclCoskeletonIso {C : Type u} [Category.{v} C]
    [HasPullbacks C] (X : C) (n : ℕ)
    (A : SimplicialObject (Over X)) :
    ((SimplicialObject.cosk n).obj A) ⋙ FormalCoproduct.incl.{w} (Over X) ≅
      (SimplicialObject.cosk n).obj (A ⋙ FormalCoproduct.incl.{w} (Over X)) := by
  let L := (SimplexCategory.Truncated.inclusion n).op
  let F := L ⋙ A
  let G := FormalCoproduct.incl.{w} (Over X)
  exact (G.ranCompIsoOfPreserves L).app F

private theorem incl_map_coskAdj_unit {C : Type u} [Category.{v} C] [HasPullbacks C]
    (X : C) (n : ℕ) (A : SimplicialObject (Over X)) (x : SimplexCategoryᵒᵖ) :
    (FormalCoproduct.incl.{w} (Over X)).map
        (((SimplicialObject.coskAdj n).unit.app A).app x) ≫
      (inclCoskeletonIso.{w} X n A).hom.app x =
    (((SimplicialObject.coskAdj n).unit.app
      (A ⋙ FormalCoproduct.incl.{w} (Over X))).app x) := by
  let L := (SimplexCategory.Truncated.inclusion n).op
  let F := L ⋙ A
  let G := FormalCoproduct.incl.{w} (Over X)
  let e := (G.ranCompIsoOfPreserves L).app F
  have hfac : L.whiskerLeft e.hom ≫ L.ranCounit.app (F ⋙ G) =
      (Functor.associator L (L.ran.obj F) G).inv ≫
        Functor.whiskerRight (L.ranCounit.app F) G := by
    change L.whiskerLeft ((G.ranCompIsoOfPreserves L).hom.app F) ≫
        L.ranCounit.app (F ⋙ G) =
      (Functor.associator L (L.ran.obj F) G).inv ≫
        Functor.whiskerRight (L.ranCounit.app F) G
    rw [Functor.ranCompIsoOfPreserves_hom_app]
    exact Functor.rightKanExtensionCompIsoOfPreserves_hom_fac G F L
  have htriO : L.whiskerLeft ((L.ranAdjunction (Over X)).unit.app A) ≫
      L.ranCounit.app F = 𝟙 (L ⋙ A) := by
    exact Functor.ranCounit_app_whiskerLeft_ranAdjunction_unit_app L A
  have htriFC : L.whiskerLeft
      ((L.ranAdjunction (FormalCoproduct (Over X))).unit.app (A ⋙ G)) ≫
        L.ranCounit.app (F ⋙ G) = 𝟙 (L ⋙ A ⋙ G) := by
    exact Functor.ranCounit_app_whiskerLeft_ranAdjunction_unit_app L (A ⋙ G)
  have hnat' : L.whiskerLeft
        (Functor.whiskerRight ((L.ranAdjunction (Over X)).unit.app A) G) ≫
      (Functor.associator L (L.ran.obj (L ⋙ A)) G).inv =
    (Functor.associator L A G).inv ≫
      Functor.whiskerRight
        (L.whiskerLeft ((L.ranAdjunction (Over X)).unit.app A)) G := by
    rw [Functor.whiskerRight_left]
    simp
  have hnat : L.whiskerLeft
        (Functor.whiskerRight ((L.ranAdjunction (Over X)).unit.app A) G) ≫
      (Functor.associator L (L.ran.obj F) G).inv =
    (Functor.associator L A G).inv ≫
      Functor.whiskerRight
        (L.whiskerLeft ((L.ranAdjunction (Over X)).unit.app A)) G := by
    simpa [F] using hnat'
  have hunit : Functor.whiskerRight ((L.ranAdjunction (Over X)).unit.app A) G ≫ e.hom =
      (L.ranAdjunction (FormalCoproduct (Over X))).unit.app (A ⋙ G) := by
    apply Functor.hom_ext_of_isRightKanExtension
      (L.ran.obj (F ⋙ G)) (L.ranCounit.app (F ⋙ G))
    rw [Functor.whiskerLeft_comp, Category.assoc, hfac]
    rw [← Category.assoc, hnat]
    rw [Category.assoc, ← Functor.whiskerRight_comp, htriO, htriFC]
    apply NatTrans.ext
    funext t
    simp
  have h := congrArg (fun η => η.app x) hunit
  exact h

/-- The canonical map from `U_{n+1}` to the degree-`n+1` term of
`cosk_n sk_n U`, formed in the slice category over the augmentation target. -/
noncomputable def matchingMap (n : ℕ) :
    U.obj (Opposite.op (SimplexCategory.mk (n + 1))) ⟶
      (((SimplicialObject.cosk n).obj (Over.lift U a)).obj
        (Opposite.op (SimplexCategory.mk (n + 1)))).left :=
  (((SimplicialObject.coskAdj n).unit.app (Over.lift U a)).app
    (Opposite.op (SimplexCategory.mk (n + 1)))).left

private theorem isCoveringOver_matching_iff (J : Pretopology C) (n : ℕ) :
    IsCoveringOver J
      (((SimplicialObject.coskAdj n).unit.app (associatedSimplicialObject U a)).app
        (Opposite.op (SimplexCategory.mk (n + 1)))) ↔
      Presieve.singleton (matchingMap U a n) ∈ J
        ((((SimplicialObject.cosk n).obj (Over.lift U a)).obj
          (Opposite.op (SimplexCategory.mk (n + 1)))).left) := by
  let x := Opposite.op (SimplexCategory.mk (n + 1))
  let A := Over.lift U a
  let G := FormalCoproduct.incl (Over X)
  let : Unique (G.obj (A.obj x)).I := by
    dsimp [G, FormalCoproduct.incl]
    infer_instance
  let : Unique (G.obj (((SimplicialObject.cosk n).obj A).obj x)).I := by
    dsimp [G, FormalCoproduct.incl]
    infer_instance
  let e := inclCoskeletonIso X n A
  let v := ((SimplicialObject.coskAdj n).unit.app A).app x
  have hunit : G.map v ≫ e.hom.app x =
      ((SimplicialObject.coskAdj n).unit.app (A ⋙ G)).app x := by
    exact incl_map_coskAdj_unit X n A x
  change IsCoveringOver J
      (((SimplicialObject.coskAdj n).unit.app (A ⋙ G)).app x) ↔
    Presieve.singleton v.left ∈ J (((SimplicialObject.cosk n).obj A).obj x).left
  rw [← hunit]
  exact (isCoveringOver_comp_iso_iff (J := J) (A := G.obj (A.obj x))
    (B := G.obj (((SimplicialObject.cosk n).obj A).obj x))
    (D := ((SimplicialObject.cosk n).obj (A ⋙ G)).obj x)
    (G.map v) (e.app x)).trans
    (isCoveringOver_incl_map_iff X J v)

private theorem isCoveringOver_degreeZero_iff (J : Pretopology C) :
    IsCoveringOver J
      (terminal.from ((associatedSimplicialObject U a).obj
        (Opposite.op (SimplexCategory.mk 0)))) ↔
      Presieve.singleton (a.app (Opposite.op (SimplexCategory.mk 0))) ∈ J X := by
  let x := Opposite.op (SimplexCategory.mk 0)
  let A := Over.lift U a
  let G := FormalCoproduct.incl (Over X)
  let T := G.obj (Over.mk (𝟙 X))
  let : Unique (G.obj (A.obj x)).I := by
    dsimp [G, FormalCoproduct.incl]
    infer_instance
  let : Unique T.I := by
    dsimp [T, G, FormalCoproduct.incl]
    infer_instance
  let q : A.obj x ⟶ Over.mk (𝟙 X) :=
    Over.homMk (a.app x) (by simp [A, Over.lift])
  let f : G.obj (A.obj x) ⟶ T :=
    G.map q
  let e : T ≅ (⊤_ FormalCoproduct (Over X)) :=
    (FormalCoproduct.isTerminalIncl _ (Over.mkIdTerminal)).uniqueUpToIso terminalIsTerminal
  have hterminal : terminal.from ((associatedSimplicialObject U a).obj x) = f ≫ e.hom := by
    apply terminal.hom_ext
  rw [hterminal]
  exact (isCoveringOver_comp_iso_iff (J := J) (A := G.obj (A.obj x))
    (B := T) (D := ⊤_ FormalCoproduct (Over X)) f e).trans <| by
    convert isCoveringOver_incl_map_iff X J q using 1
    rfl

section ZeroMatching

local instance simplexTruncatedZero_subsingleton :
    Subsingleton (SimplexCategory.Truncated 0) := by
  constructor
  intro a b
  obtain ⟨⟨m⟩, hm⟩ := a
  obtain ⟨⟨n⟩, hn⟩ := b
  have hm' : m = 0 := Nat.eq_zero_of_le_zero hm
  have hn' : n = 0 := Nat.eq_zero_of_le_zero hn
  subst m
  subst n
  rfl

local instance simplexTruncatedZero_hom_subsingleton
    (a b : SimplexCategory.Truncated 0) : Subsingleton (a ⟶ b) := by
  constructor
  intro f g
  apply SimplexCategory.Truncated.Hom.ext
  apply OrderHom.ext
  funext x
  have hb : b.1.len = 0 := Nat.eq_zero_of_le_zero b.2
  cases b with
  | mk Δ hΔ =>
    cases Δ with
    | mk n =>
      have hn : n = 0 := Nat.eq_zero_of_le_zero hΔ
      subst n
      apply Fin.ext
      omega

private abbrev zeroTruncCategory := (SimplexCategory.Truncated 0)ᵒᵖ
private abbrev zeroTruncObject : zeroTruncCategory :=
  Opposite.op (⟨SimplexCategory.mk 0, by decide⟩ : SimplexCategory.Truncated 0)
private abbrev zeroInclusion := (SimplexCategory.Truncated.inclusion 0).op

private def zeroFaceArrow (d : Fin 2) :
    StructuredArrow (Opposite.op (SimplexCategory.mk 1)) zeroInclusion :=
  StructuredArrow.mk (Quiver.Hom.op (SimplexCategory.δ d) :
    Opposite.op (SimplexCategory.mk 1) ⟶ zeroInclusion.obj zeroTruncObject)

private theorem zeroFaceArrow_eq (g :
    StructuredArrow (Opposite.op (SimplexCategory.mk 1)) zeroInclusion) :
    g = zeroFaceArrow (if g.hom.unop.toOrderHom 0 = 1 then 0 else 1) := by
  rcases g with ⟨left, ⟨⟨⟨m⟩, hm⟩⟩, hom⟩
  have hm0 : m = 0 := Nat.eq_zero_of_le_zero hm
  subst m
  let v := hom.unop.toOrderHom 0
  let d : Fin 2 := if v = 1 then 0 else 1
  have hr : (⟨left, Opposite.op (⟨SimplexCategory.mk 0, hm⟩ :
      SimplexCategory.Truncated 0), hom⟩ :
      StructuredArrow (Opposite.op (SimplexCategory.mk 1)) zeroInclusion).right =
      (zeroFaceArrow d).right := Subsingleton.elim _ _
  have hh : (⟨left, Opposite.op (⟨SimplexCategory.mk 0, hm⟩ :
      SimplexCategory.Truncated 0), hom⟩ :
      StructuredArrow (Opposite.op (SimplexCategory.mk 1)) zeroInclusion).hom ≫
      zeroInclusion.map (eqToHom hr) = (zeroFaceArrow d).hom := by
    cases hr
    apply Quiver.Hom.unop_inj
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext i
    fin_cases i
    have hs : v = 0 ∨ v = 1 := by
      have hs := Fin.eq_zero_or_eq_succ v
      simpa using hs
    rcases hs with hv0 | hv1
    · change v = (Fin.succAboveOrderEmb d).toOrderHom 0
      simp [d, hv0, Fin.succAboveOrderEmb_apply, OrderEmbedding.toOrderHom_coe]
    · change v = (Fin.succAboveOrderEmb d).toOrderHom 0
      simp [d, hv1, Fin.succAboveOrderEmb_apply, OrderEmbedding.toOrderHom_coe]
  exact StructuredArrow.obj_ext _ _ hr hh

private noncomputable def zeroPullbackFan :
    BinaryFan (Over.mk (a.app (Opposite.op (SimplexCategory.mk 0))))
      (Over.mk (a.app (Opposite.op (SimplexCategory.mk 0)))) :=
  (pullbackConeEquivBinaryFan).functor.obj
      (pullback.cone (a.app (Opposite.op (SimplexCategory.mk 0)))
        (a.app (Opposite.op (SimplexCategory.mk 0))))

private noncomputable def zeroPullbackPointIso :
    (zeroPullbackFan U a).pt ≅ Over.mk
      (pullback.fst (a.app (Opposite.op (SimplexCategory.mk 0)))
        (a.app (Opposite.op (SimplexCategory.mk 0))) ≫
        a.app (Opposite.op (SimplexCategory.mk 0))) :=
  Iso.refl _

private noncomputable def zeroMatchingCone :
    Cone (StructuredArrow.proj (Opposite.op (SimplexCategory.mk 1)) zeroInclusion ⋙
      (SimplicialObject.truncation 0).obj (Over.lift U a)) := by
  let pb := zeroPullbackFan U a
  refine {
    pt := pb.pt
    π := {
      app := fun g => by
        let d := g.hom.unop.toOrderHom 0
        rcases g with ⟨_, ⟨⟨⟨m⟩, hm⟩⟩, f⟩
        have hm' : m = 0 := Nat.eq_zero_of_le_zero hm
        subst m
        exact if d = 1 then pb.snd else pb.fst
      naturality := by
        intro g g' φ
        have hright : g.right = g'.right := Subsingleton.elim _ _
        have hφ : φ.right = eqToHom hright := Subsingleton.elim _ _
        have hg : g = g' := by
          apply StructuredArrow.obj_ext g g' hright
          rw [← hφ]
          exact StructuredArrow.w φ
        subst g'
        have hid : φ = 𝟙 g := StructuredArrow.hom_ext φ (𝟙 g) (Subsingleton.elim _ _)
        subst φ
        simp
    }
  }

private theorem zeroMatchingCone_face0 :
    (zeroMatchingCone U a).π.app (zeroFaceArrow 0) = (zeroPullbackFan U a).snd := by
  simp [zeroMatchingCone, zeroPullbackFan, zeroFaceArrow, SimplexCategory.δ]
  dsimp [StructuredArrow.hom, Comma.hom, SimplexCategory.Hom.toOrderHom,
    SimplexCategory.Hom.mk, Fin.succAboveOrderEmb]
  rfl

private theorem zeroMatchingCone_face1 :
    (zeroMatchingCone U a).π.app (zeroFaceArrow 1) = (zeroPullbackFan U a).fst := by
  simp [zeroMatchingCone, zeroPullbackFan, zeroFaceArrow, SimplexCategory.δ]
  dsimp [StructuredArrow.hom, Comma.hom, SimplexCategory.Hom.toOrderHom,
    SimplexCategory.Hom.mk, Fin.succAboveOrderEmb]
  rfl

private noncomputable def isLimitZeroMatchingCone :
    IsLimit (zeroMatchingCone U a) := by
  let pb := zeroPullbackFan U a
  have hpb : IsLimit pb := by
    exact (pullback.isLimit (a.app (Opposite.op (SimplexCategory.mk 0)))
      (a.app (Opposite.op (SimplexCategory.mk 0)))).pullbackConeEquivBinaryFanFunctor
  refine ⟨fun s => hpb.lift (BinaryFan.mk
    (s.π.app (zeroFaceArrow 1)) (s.π.app (zeroFaceArrow 0))), ?_, ?_⟩
  · intro s g
    let fan := BinaryFan.mk (s.π.app (zeroFaceArrow 1)) (s.π.app (zeroFaceArrow 0))
    have heq := zeroFaceArrow_eq g
    let v := g.hom.unop.toOrderHom 0
    by_cases hv : v = 1
    · have heq0 : g = zeroFaceArrow 0 := by
        rw [ite_eq_left hv] at heq
        exact heq
      rw [heq0]
      rw [zeroMatchingCone_face0]
      change hpb.lift fan ≫ pb.snd = s.π.app (zeroFaceArrow 0)
      exact hpb.fac fan ⟨WalkingPair.right⟩
    · have heq1 : g = zeroFaceArrow 1 := by
        rw [ite_eq_right hv] at heq
        exact heq
      rw [heq1]
      rw [zeroMatchingCone_face1]
      change hpb.lift fan ≫ pb.fst = s.π.app (zeroFaceArrow 1)
      exact hpb.fac fan ⟨WalkingPair.left⟩
  · intro s m hm
    let fan := BinaryFan.mk (s.π.app (zeroFaceArrow 1)) (s.π.app (zeroFaceArrow 0))
    have hm0 : m ≫ pb.fst = s.π.app (zeroFaceArrow 1) := by
        have h := hm (zeroFaceArrow 1)
        rw [zeroMatchingCone_face1] at h
        exact h
    have hm1 : m ≫ pb.snd = s.π.app (zeroFaceArrow 0) := by
        have h := hm (zeroFaceArrow 0)
        rw [zeroMatchingCone_face0] at h
        exact h
    have hf0 := hpb.fac fan ⟨WalkingPair.left⟩
    have hf1 := hpb.fac fan ⟨WalkingPair.right⟩
    exact BinaryFan.IsLimit.hom_ext hpb (hm0.trans hf0.symm) (hm1.trans hf1.symm)

private noncomputable def zeroMatchingExtension :
    RightExtension zeroInclusion ((SimplicialObject.truncation 0).obj (Over.lift U a)) :=
  RightExtension.mk _ ((SimplicialObject.coskAdj 0).counit.app
    ((SimplicialObject.truncation 0).obj (Over.lift U a)))

private noncomputable def zeroMatchingExtension_isPointwise :
    (zeroMatchingExtension U a).IsPointwiseRightKanExtensionAt
      (Opposite.op (SimplexCategory.mk 1)) := by
  let E : RightExtension zeroInclusion
      ((SimplicialObject.truncation 0).obj (Over.lift U a)) := zeroMatchingExtension U a
  let : E.left.IsRightKanExtension E.hom := by
    change
      (zeroInclusion.ran.obj
          ((SimplicialObject.truncation 0).obj (Over.lift U a))).IsRightKanExtension
        ((zeroInclusion.ranAdjunction (Over X)).counit.app
          ((SimplicialObject.truncation 0).obj (Over.lift U a)))
    rw [Functor.ranAdjunction_counit]
    infer_instance
  exact Functor.isPointwiseRightKanExtensionOfIsRightKanExtension E.left E.hom _

private noncomputable def zeroMatchingIso :
    (((SimplicialObject.cosk 0).obj (Over.lift U a)).obj
      (Opposite.op (SimplexCategory.mk 1))) ≅ (zeroPullbackFan U a).pt := by
  let hE := zeroMatchingExtension_isPointwise U a
  exact hE.conePointUniqueUpToIso (isLimitZeroMatchingCone U a)

private noncomputable def zeroMatchingIsoPullback :
    (((SimplicialObject.cosk 0).obj (Over.lift U a)).obj
      (Opposite.op (SimplexCategory.mk 1))) ≅ Over.mk
        (pullback.fst (a.app (Opposite.op (SimplexCategory.mk 0)))
          (a.app (Opposite.op (SimplexCategory.mk 0))) ≫
          a.app (Opposite.op (SimplexCategory.mk 0))) :=
  (zeroMatchingIso U a) ≪≫ (zeroPullbackPointIso U a)

private theorem zeroMatchingIso_hom_comp_face (d : Fin 2) :
    (zeroMatchingIso U a).hom ≫ (zeroMatchingCone U a).π.app (zeroFaceArrow d) =
      ((SimplicialObject.cosk 0).obj (Over.lift U a)).map
          (Quiver.Hom.op (SimplexCategory.δ d)) ≫
        ((SimplicialObject.coskAdj 0).counit.app
          ((SimplicialObject.truncation 0).obj (Over.lift U a))).app zeroTruncObject := by
  let hE := zeroMatchingExtension_isPointwise U a
  exact IsLimit.conePointUniqueUpToIso_hom_comp hE (isLimitZeroMatchingCone U a)
    (zeroFaceArrow d)

private theorem zero_unit_face (A : SimplicialObject (Over X)) (d : Fin 2) :
    (((SimplicialObject.coskAdj 0).unit.app A).app
        (Opposite.op (SimplexCategory.mk 1))) ≫
      (((SimplicialObject.cosk 0).obj A).map (SimplexCategory.δ d).op) ≫
      ((SimplicialObject.coskAdj 0).counit.app
        ((SimplicialObject.truncation 0).obj A)).app zeroTruncObject =
        A.map (SimplexCategory.δ d).op := by
  have hn := ((SimplicialObject.coskAdj 0).unit.app A).naturality
    (Quiver.Hom.op (SimplexCategory.δ d))
  have ht := (SimplicialObject.coskAdj (C := Over X) 0).left_triangle_components A
  have ht0 := congrArg (fun t : (SimplicialObject.truncation 0).obj A ⟶
      (SimplicialObject.truncation 0).obj A => t.app zeroTruncObject) ht
  dsimp only [NatTrans.comp_app, NatTrans.id_app] at ht0
  have h0 : ((SimplicialObject.coskAdj 0).unit.app A).app
      (Opposite.op (SimplexCategory.mk 0)) ≫
      ((SimplicialObject.coskAdj 0).counit.app
        ((SimplicialObject.truncation 0).obj A)).app zeroTruncObject =
      𝟙 (A.obj (Opposite.op (SimplexCategory.mk 0))) := by
    change _ = _ at ht0
    exact ht0
  have hnat : A.map (SimplexCategory.δ d).op ≫
      ((SimplicialObject.coskAdj 0).unit.app A).app (Opposite.op (SimplexCategory.mk 0)) =
      ((SimplicialObject.coskAdj 0).unit.app A).app (Opposite.op (SimplexCategory.mk 1)) ≫
        ((SimplicialObject.cosk 0).obj A).map (SimplexCategory.δ d).op := hn
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun f ↦ f ≫ ((SimplicialObject.coskAdj 0).counit.app
    ((SimplicialObject.truncation 0).obj A)).app zeroTruncObject) hnat.symm).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun f ↦ A.map (SimplexCategory.δ d).op ≫ f) h0).trans ?_
  exact Category.comp_id _

/-- The matching map followed by the identification with `U₀ ×_X U₀` and a projection `p` is the
corresponding face map, when `p` agrees with the matching cone leg of that face. -/
private theorem matchingMap_comp_iso_hom_comp_proj (d : Fin 2)
    (p : pullback (a.app (Opposite.op (SimplexCategory.mk 0)))
      (a.app (Opposite.op (SimplexCategory.mk 0))) ⟶ U.obj (Opposite.op (SimplexCategory.mk 0)))
    (hp : ((zeroPullbackPointIso U a).hom).left ≫ p =
      ((zeroMatchingCone U a).π.app (zeroFaceArrow d)).left) :
    matchingMap U a 0 ≫ ((zeroMatchingIsoPullback U a).hom).left ≫ p = U.δ d := by
  have h := zeroMatchingIso_hom_comp_face U a d
  have hpre := congrArg (fun f => matchingMap U a 0 ≫ (zeroMatchingIso U a).hom.left ≫ f) hp
  have hmid := congrArg (fun f => matchingMap U a 0 ≫ f.left) h
  have hu := congrArg (fun f => f.left) (zero_unit_face (Over.lift U a) d)
  simpa [zeroMatchingIsoPullback, matchingMap, SimplicialObject.δ, Over.comp_left,
    Category.assoc] using hpre.trans (hmid.trans hu)

private theorem zeroMatchingIso_hom_comp_fst :
    matchingMap U a 0 ≫ ((zeroMatchingIsoPullback U a).hom).left ≫ pullback.fst
        (a.app (Opposite.op (SimplexCategory.mk 0)))
        (a.app (Opposite.op (SimplexCategory.mk 0))) =
      U.δ 1 :=
  matchingMap_comp_iso_hom_comp_proj U a 1 _ (by
    simp [zeroMatchingCone_face1, zeroPullbackPointIso, zeroPullbackFan,
      pullbackConeEquivBinaryFan])

private theorem zeroMatchingIso_hom_comp_snd :
    matchingMap U a 0 ≫ ((zeroMatchingIsoPullback U a).hom).left ≫ pullback.snd
        (a.app (Opposite.op (SimplexCategory.mk 0)))
        (a.app (Opposite.op (SimplexCategory.mk 0))) =
      U.δ 0 :=
  matchingMap_comp_iso_hom_comp_proj U a 0 _ (by
    simp [zeroMatchingCone_face0, zeroPullbackPointIso, zeroPullbackFan,
      pullbackConeEquivBinaryFan])

private theorem matchingMap_zero_comp_iso_hom :
    (((SimplicialObject.coskAdj 0).unit.app (Over.lift U a)).app
      (Opposite.op (SimplexCategory.mk 1))).left ≫ ((zeroMatchingIsoPullback U a).hom).left =
      oneSimplexToFiberProduct U a := by
  change matchingMap U a 0 ≫ ((zeroMatchingIsoPullback U a).hom).left =
    oneSimplexToFiberProduct U a
  apply pullback.hom_ext
  · calc
      (matchingMap U a 0 ≫ ((zeroMatchingIsoPullback U a).hom).left) ≫ pullback.fst _ _ =
          U.δ 1 := by simpa only [Category.assoc] using zeroMatchingIso_hom_comp_fst U a
      _ = oneSimplexToFiberProduct U a ≫ pullback.fst _ _ := by
        simp only [oneSimplexToFiberProduct, pullback.lift_fst]
  · calc
      (matchingMap U a 0 ≫ ((zeroMatchingIsoPullback U a).hom).left) ≫ pullback.snd _ _ =
          U.δ 0 := by simpa only [Category.assoc] using zeroMatchingIso_hom_comp_snd U a
      _ = oneSimplexToFiberProduct U a ≫ pullback.snd _ _ := by
        simp only [oneSimplexToFiberProduct, pullback.lift_snd]

private theorem mem_singleton_matchingMap_zero_iff (J : Pretopology C) :
    Presieve.singleton (matchingMap U a 0) ∈ J
        ((((SimplicialObject.cosk 0).obj (Over.lift U a)).obj
          (Opposite.op (SimplexCategory.mk 1))).left) ↔
      Presieve.singleton (oneSimplexToFiberProduct U a) ∈ J
        (pullback (a.app (Opposite.op (SimplexCategory.mk 0)))
          (a.app (Opposite.op (SimplexCategory.mk 0)))) := by
  let A := Over.lift U a
  let v := ((SimplicialObject.coskAdj 0).unit.app A).app
    (Opposite.op (SimplexCategory.mk 1))
  let e := zeroMatchingIsoPullback U a
  have h := mem_singleton_comp_iso_iff J v e
  have hv : v.left = matchingMap U a 0 := rfl
  have hEq : v.left ≫ e.hom.left = oneSimplexToFiberProduct U a := by
    dsimp [v, A, e]
    exact matchingMap_zero_comp_iso_hom U a
  rw [hEq] at h
  exact h

end ZeroMatching

private theorem isCoveringOver_degreeOne_iff (J : Pretopology C) :
    IsCoveringOver J
      (((SimplicialObject.coskAdj 0).unit.app (associatedSimplicialObject U a)).app
        (Opposite.op (SimplexCategory.mk 1))) ↔
      Presieve.singleton (oneSimplexToFiberProduct U a) ∈
        J (pullback (a.app (Opposite.op (SimplexCategory.mk 0)))
          (a.app (Opposite.op (SimplexCategory.mk 0)))) := by
  exact (isCoveringOver_matching_iff U a J 0).trans (mem_singleton_matchingMap_zero_iff U a J)

/-- **Stacks Project, Tag 0GM9.** The simplicial semi-representable object over `X` associated to
an augmented simplicial object `U ⟶ X` is a hypercovering exactly when the augmentation in degree
zero, the degree-one morphism to `U₀ ×_X U₀`, and every higher matching morphism generate a
covering presieve of the site. -/
@[stacks 0GM9 "the covering characterization"]
theorem isHypercovering_associatedSimplicialObject_iff (J : Pretopology C) :
    IsHypercovering J (associatedSimplicialObject U a) ↔
      (Presieve.singleton (a.app (Opposite.op (SimplexCategory.mk 0))) ∈ J X) ∧
      (Presieve.singleton (oneSimplexToFiberProduct U a) ∈
        J (pullback (a.app (Opposite.op (SimplexCategory.mk 0)))
          (a.app (Opposite.op (SimplexCategory.mk 0))))) ∧
      ∀ n : ℕ, 1 ≤ n → Presieve.singleton (matchingMap U a n) ∈
        J ((((SimplicialObject.cosk n).obj (Over.lift U a)).obj
          (Opposite.op (SimplexCategory.mk (n + 1)))).left) := by
  have : HasFiniteLimits (Over X) := hasFiniteLimits_of_hasTerminal_and_pullbacks
  rw [IsHypercovering]
  constructor
  · intro h
    rcases h with ⟨h₀, hmatch⟩
    refine ⟨(isCoveringOver_degreeZero_iff U a J).mp h₀, ?_, ?_⟩
    · exact (isCoveringOver_degreeOne_iff U a J).mp (hmatch 0)
    · intro n hn
      exact (isCoveringOver_matching_iff U a J n).mp (hmatch n)
  · rintro ⟨h₀, h₁, hmatch⟩
    refine ⟨(isCoveringOver_degreeZero_iff U a J).mpr h₀, ?_⟩
    intro n
    cases n with
    | zero => exact (isCoveringOver_degreeOne_iff U a J).mpr h₁
    | succ n =>
      exact (isCoveringOver_matching_iff U a J (n + 1)).mpr (hmatch (n + 1) (by omega))

end Stacks.CategoryTheory.Hypercovering

end
